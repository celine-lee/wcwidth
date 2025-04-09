
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

# local imports
from .table_vs16 import VS16_NARROW_TO_WIDE
from .table_wide import WIDE_EASTASIAN
from .table_zero import ZERO_WIDTH
from .unicode_versions import list_versions

try:
    # std imports
    from functools import lru_cache
except ImportError:
    # lru_cache was added in Python 3.2; 3rd party fallback
    from backports.functools_lru_cache import lru_cache

# global flag for Python3
_PY3 = sys.version_info[0] >= 3


def _binary_search_in_ranges(value, ranges):
    """
    Helper function: perform binary search on a sorted list of ranges.
    
    Each range is a tuple (low, high). Returns True if value is within any
    range, False otherwise.
    """
    if value < ranges[0][0] or value > ranges[-1][1]:
        return False
    low = 0
    high = len(ranges) - 1
    while low <= high:
        mid = (low + high) // 2
        range_low, range_high = ranges[mid]
        if value > range_high:
            low = mid + 1
        elif value < range_low:
            high = mid - 1
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
        matching version is selected.  When ``latest`` (default), the
        highest Unicode version level is used.
    :return: The width, in cells, necessary to display the character of
        Unicode string character, ``wc``.  Returns 0 if the ``wc`` argument has
        no printable effect on a terminal (such as NUL '\0'), -1 if ``wc`` is
        not printable, or has an indeterminate effect on the terminal, such as
        a control character.  Otherwise, the number of column positions the
        character occupies on a graphic terminal (1 or 2) is returned.
    :rtype: int

    See :ref:`Specification` for details of cell measurement.
    """
    ucs = ord(wc) if wc else 0

    # Small optimization: early return for printable ASCII.
    if 32 <= ucs < 0x7f:
        return 1

    # C0/C1 control characters
    if (ucs and ucs < 32) or (0x07F <= ucs < 0x0A0):
        return -1

    _unicode_version = _wcmatch_version(unicode_version)

    # Check for zero-width characters.
    if not (ucs < ZERO_WIDTH[_unicode_version][0][0] or
            ucs > ZERO_WIDTH[_unicode_version][-1][1]):
        if _binary_search_in_ranges(ucs, ZERO_WIDTH[_unicode_version]):
            return 0

    # Check for wide characters (1 or 2 width).
    if ucs < WIDE_EASTASIAN[_unicode_version][0][0] or ucs > WIDE_EASTASIAN[_unicode_version][-1][1]:
        return 1
    if _binary_search_in_ranges(ucs, WIDE_EASTASIAN[_unicode_version]):
        return 2

    return 1


def wcswidth(pwcs, n=None, unicode_version='auto'):
    """
    Given a unicode string, return its printable length on a terminal.

    :param str pwcs: Measure width of given unicode string.
    :param int n: When ``n`` is None (default), return the length of the entire
        string, otherwise only the first ``n`` characters are measured. This
        argument exists only for compatibility with the C POSIX function
        signature. It is suggested instead to use python's string slicing
        capability, ``wcswidth(pwcs[:n])``
    :param str unicode_version: An explicit definition of the unicode version
        level to use for determination, may be ``auto`` (default), which uses
        the Environment Variable, ``UNICODE_VERSION`` if defined, or the latest
        available unicode version, otherwise.
    :rtype: int
    :returns: The width, in cells, needed to display the first ``n`` characters
        of the unicode string ``pwcs``.  Returns ``-1`` for C0 and C1 control
        characters!

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
            # Variation Selector-16: conditionally add width if applicable.
            if _unicode_version is None:
                _unicode_version = _wcversion_value(_wcmatch_version(unicode_version))
            # Only apply the rule for Unicode version 9.0.0 or later.
            if _unicode_version >= (9, 0, 0):
                ucs = ord(last_measured_char)
                # Use the VS16 conversion table.
                if not (ucs < VS16_NARROW_TO_WIDE["9.0.0"][0][0] or
                        ucs > VS16_NARROW_TO_WIDE["9.0.0"][-1][1]):
                    if _binary_search_in_ranges(ucs, VS16_NARROW_TO_WIDE["9.0.0"]):
                        width += 1
            last_measured_char = None
            idx += 1
            continue
        # Measure the current character.
        wcw = wcwidth(char, unicode_version)
        if wcw < 0:
            # Early return on control characters.
            return wcw
        if wcw > 0:
            last_measured_char = char
        width += wcw
        idx += 1
    return width


@lru_cache(maxsize=128)
def _wcversion_value(ver_string):
    """
    Integer-mapped value of a given dotted version string.

    :param str ver_string: Unicode version string, of form ``n.n.n``.
    :rtype: tuple(int)
    :returns: tuple of integers, e.g. (6, 0, 0)
    """
    return tuple(map(int, ver_string.split('.')))


@lru_cache(maxsize=8)
def _wcmatch_version(given_version):
    """
    Return the nearest matching supported Unicode version level.

    If an exact match is not determined, the nearest lower version level is
    returned after a warning is emitted.  For example, given supported levels
    ``4.1.0`` and ``5.0.0``, and a version string of ``4.9.9``, then ``4.1.0``
    is selected and returned:

    >>> _wcmatch_version('4.9.9')
    '4.1.0'
    >>> _wcmatch_version('8.0')
    '8.0.0'
    >>> _wcmatch_version('1')
    '4.1.0'

    :param str given_version: the desired Unicode version, may be ``auto``
        (default) to select the Unicode Version from the environment variable
        ``UNICODE_VERSION``. If this variable is not set, then the latest is used.
    :rtype: str
    :returns: the matched Unicode version string.
    """
    # Maintain type consistency for Python 2.
    _return_str = (not _PY3) and isinstance(given_version, str)

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

    try:
        cmp_given = _wcversion_value(given_version)
    except ValueError:
        warnings.warn("UNICODE_VERSION value, {given_version!r}, is invalid. "
                      "Value should be in form of `integer[.]+'. "
                      "Using latest supported unicode version {latest_version!r}."
                      .format(given_version=given_version, latest_version=latest_version))
        return latest_version if not _return_str else latest_version.encode()

    # If the given version is less than any available version, return the earliest.
    earliest_version = unicode_versions[0]
    cmp_earliest_version = _wcversion_value(earliest_version)
    if cmp_given <= cmp_earliest_version:
        warnings.warn("UNICODE_VERSION value, {given_version!r}, is lower than any "
                      "available unicode version. Returning lowest version {earliest_version!r}."
                      .format(given_version=given_version, earliest_version=earliest_version))
        return earliest_version if not _return_str else earliest_version.encode()

    # Find the highest version we support that does not exceed the given version.
    for idx, unicode_version in enumerate(unicode_versions):
        try:
            cmp_next_version = _wcversion_value(unicode_versions[idx + 1])
        except IndexError:
            return latest_version if not _return_str else latest_version.encode()

        if cmp_given == cmp_next_version[:len(cmp_given)]:
            return unicode_versions[idx + 1]
        if cmp_next_version > cmp_given:
            return unicode_version

    assert False, ("Unreachable code in _wcmatch_version", given_version, unicode_versions)
