
"""
This is a python implementation of wcwidth() and wcswidth().

https://github.com/jquast/wcwidth

from Markus Kuhn's C code, retrieved from:

    http://www.cl.cam.ac.uk/~mgk25/ucs/wcwidth.c

This is an implementation of wcwidth() and wcswidth() (defined in
IEEE Std 1002.1-2001) for Unicode.

http://www.opengroup.org/onlinepubs/007904975/functions/wcwidth.html
http://www.opengroup.org/onlinepubs/007904975/functions/wcswidth.html

In fixed-width output devices, Latin characters all occupy a single
"cell" position of equal width, whereas ideographic CJK characters
occupy two such cells. Interoperability between terminal-line
applications and (teletype-style) character terminals using the
UTF-8 encoding requires agreement on which character should advance
the cursor by how many cell positions. No established formal
standards exist at present on which Unicode character shall occupy
how many cell positions on character terminals. These routines are
a first attempt of defining such behavior based on simple rules
applied to data provided by the Unicode Consortium.

For some graphical characters, the Unicode standard explicitly
defines a character-cell width via the definition of the East Asian
FullWidth (F), Wide (W), Half-width (H), and Narrow (Na) classes.
In all these cases, there is no ambiguity about which width a
terminal shall use. For characters in the East Asian Ambiguous (A)
class, the width choice depends purely on a preference of backward
compatibility with either historic CJK or Western practice.
Choosing single-width for these characters is easy to justify as
the appropriate long-term solution, as the CJK practice of
displaying these characters as double-width comes from historic
implementation simplicity (8-bit encoded characters were displayed
single-width and 16-bit ones double-width, even for Greek,
Cyrillic, etc.) and not any typographic considerations.

Much less clear is the choice of width for the Not East Asian
(Neutral) class. Existing practice does not dictate a width for any
of these characters. It would nevertheless make sense
typographically to allocate two character cells to characters such
as for instance EM SPACE or VOLUME INTEGRAL, which cannot be
represented adequately with a single-width glyph. The following
routines at present merely assign a single-cell width to all
neutral characters, in the interest of simplicity. This is not
entirely satisfactory and should be reconsidered before
establishing a formal standard in this area. At the moment, the
decision which Not East Asian (Neutral) characters should be
represented by double-width glyphs cannot yet be answered by
applying a simple rule from the Unicode database content. Setting
up a proper standard for the behavior of UTF-8 character terminals
will require a careful analysis not only of each Unicode character,
but also of each presentation form, something the author of these
routines has avoided to do so far.

http://www.unicode.org/unicode/reports/tr11/

Latest version: http://www.cl.cam.ac.uk/~mgk25/ucs/wcwidth.c
"""
from __future__ import division

# std imports
import os
import sys
import warnings

# local
from .table_vs16 import VS16_NARROW_TO_WIDE
from .table_wide import WIDE_EASTASIAN
from .table_zero import ZERO_WIDTH
from .unicode_versions import list_versions

try:
    # Python standard library
    from functools import lru_cache
except ImportError:
    # lru_cache was added in Python 3.2; 3rd party backport:
    from backports.functools_lru_cache import lru_cache

# global flag for Python 3
_PY3 = sys.version_info[0] >= 3


def _bisearch(ucs, table):
    """
    Helper function to perform binary search on a list of ranges.

    :param int ucs: Unicode code point to search for.
    :param list table: A list of tuples (start, end) representing ranges.
    :return: True if ucs falls within any of the ranges in table, else False.
    :rtype: bool
    """
    if ucs < table[0][0] or ucs > table[-1][1]:
        return False
    lbound = 0
    ubound = len(table) - 1
    while lbound <= ubound:
        mid = (lbound + ubound) // 2
        if ucs > table[mid][1]:
            lbound = mid + 1
        elif ucs < table[mid][0]:
            ubound = mid - 1
        else:
            return True
    return False


@lru_cache(maxsize=1000)
def wcwidth(wc, unicode_version='auto'):
    r"""
    Given one Unicode character, return its printable length on a terminal.

    :param str wc: A single Unicode character.
    :param str unicode_version: A Unicode version number, such as
        ``'6.0.0'``. A list of version levels supported by wcwidth
        is returned by :func:`list_versions`.

        Any version string may be specified without error -- the nearest
        matching version is selected. When ``latest`` (default), the
        highest Unicode version level is used.
    :return: The width, in cells, necessary to display the Unicode character ``wc``.
             Returns 0 if the argument has no printable effect on a terminal (e.g. NUL),
             -1 if ``wc`` is not printable, or has an indeterminate effect (e.g. control character).
             Otherwise, returns the number of column positions the character occupies (1 or 2).
    :rtype: int

    See :ref:`Specification` for details of cell measurement.
    """
    ucs = ord(wc) if wc else 0

    # Fast-path for printable ASCII characters.
    if 32 <= ucs < 0x7f:
        return 1

    # C0/C1 control characters yield -1.
    if (ucs and ucs < 32) or (0x7F <= ucs < 0x0A0):
        return -1

    _unicode_version = _wcmatch_version(unicode_version)

    # Zero width check
    if not (ucs < ZERO_WIDTH[_unicode_version][0][0] or 
            ucs > ZERO_WIDTH[_unicode_version][-1][1]):
        if _bisearch(ucs, ZERO_WIDTH[_unicode_version]):
            return 0

    # Check for width 2 characters.
    if ucs < WIDE_EASTASIAN[_unicode_version][0][0] or \
       ucs > WIDE_EASTASIAN[_unicode_version][-1][1]:
        return 1
    if _bisearch(ucs, WIDE_EASTASIAN[_unicode_version]):
        return 2

    return 1


def wcswidth(pwcs, n=None, unicode_version='auto'):
    """
    Given a Unicode string, return its printable length on a terminal.

    :param str pwcs: Unicode string to measure.
    :param int n: If None (default), measure the entire string.
                  Otherwise, only the first n characters are measured.
                  (This argument is provided only for compatibility with the
                  C POSIX function signature. It is suggested to use Python's
                  slicing instead: wcswidth(pwcs[:n]))
    :param str unicode_version: The Unicode version to use. May be 'auto'
                                (default) to select the Unicode version from
                                the environment variable UNICODE_VERSION (if defined),
                                or to choose the latest available version.
    :rtype: int
    :returns: The number of cells needed to display the first n characters of pwcs.
              Returns -1 if a control character that is non-printable is encountered.

    See :ref:`Specification` for details of cell measurement.
    """
    _unicode_version = None
    end = len(pwcs) if n is None else n
    width = 0
    idx = 0
    last_measured_char = None
    while idx < end:
        char = pwcs[idx]
        if char == u'\u200D':
            # Zero Width Joiner: skip this and the next character.
            idx += 2
            continue
        if char == u'\uFE0F' and last_measured_char:
            # Variation Selector-16: conditionally add width for the preceding character.
            if _unicode_version is None:
                _unicode_version = _wcversion_value(_wcmatch_version(unicode_version))
            if _unicode_version >= (9, 0, 0):
                ucs = ord(last_measured_char)
                if not (ucs < VS16_NARROW_TO_WIDE["9.0.0"][0][0] or 
                        ucs > VS16_NARROW_TO_WIDE["9.0.0"][-1][1]):
                    if _bisearch(ucs, VS16_NARROW_TO_WIDE["9.0.0"]):
                        width += 1
            last_measured_char = None
            idx += 1
            continue
        # Measure the width of the current character.
        wcw = wcwidth(char, unicode_version)
        if wcw < 0:
            # Return immediately on encountering a control character.
            return wcw
        if wcw > 0:
            last_measured_char = char
        width += wcw
        idx += 1
    return width


@lru_cache(maxsize=128)
def _wcversion_value(ver_string):
    """
    Convert a dotted version string to a tuple of integers for comparison.

    :param str ver_string: A Unicode version string in the form 'n.n.n'.
    :rtype: tuple(int)
    :returns: A tuple of integers representing the version.
    """
    return tuple(map(int, ver_string.split('.')))


@lru_cache(maxsize=8)
def _wcmatch_version(given_version):
    """
    Select the nearest matching supported Unicode version level.

    If an exact match is not available, the nearest lower version is selected
    (with a warning). For example:
        _wcmatch_version('4.9.9') returns '4.1.0',
        _wcmatch_version('8.0') returns '8.0.0',
        _wcmatch_version('1') returns '4.1.0'.

    :param str given_version: The requested Unicode version,
                              or 'auto' to select via the environment variable.
    :rtype: str
    :returns: The matched Unicode version string.
    """
    # Return type depends on the running Python version.
    _return_str = not _PY3 and isinstance(given_version, str)

    if _return_str:
        unicode_versions = list(map(lambda ucs: ucs.encode(), list_versions()))
    else:
        unicode_versions = list_versions()
    latest_version = unicode_versions[-1]

    if given_version in (u'auto', 'auto'):
        given_version = os.environ.get(
            'UNICODE_VERSION',
            'latest' if not _return_str else latest_version.encode())

    if given_version in (u'latest', 'latest'):
        return latest_version if not _return_str else latest_version.encode()

    if given_version in unicode_versions:
        return given_version if not _return_str else given_version.encode()

    # The given version is not supported by our tables.
    try:
        cmp_given = _wcversion_value(given_version)
    except ValueError:
        warnings.warn("UNICODE_VERSION value, {given_version!r}, is invalid. "
                      "Expected form: integer separated by dots. Using latest "
                      "supported version {latest_version!r}.".format(
                          given_version=given_version,
                          latest_version=latest_version))
        return latest_version if not _return_str else latest_version.encode()

    earliest_version = unicode_versions[0]
    cmp_earliest_version = _wcversion_value(earliest_version)

    if cmp_given <= cmp_earliest_version:
        warnings.warn("UNICODE_VERSION value, {given_version!r}, is lower than any available "
                      "version. Returning lowest version {earliest_version!r}.".format(
                          given_version=given_version,
                          earliest_version=earliest_version))
        return earliest_version if not _return_str else earliest_version.encode()

    for idx, unicode_version in enumerate(unicode_versions):
        try:
            cmp_next_version = _wcversion_value(unicode_versions[idx + 1])
        except IndexError:
            return latest_version if not _return_str else latest_version.encode()

        if cmp_given == cmp_next_version[:len(cmp_given)]:
            return unicode_versions[idx + 1]

        if cmp_next_version > cmp_given:
            return unicode_version
    assert False, ("Unreachable code reached in _wcmatch_version", given_version, unicode_versions)
