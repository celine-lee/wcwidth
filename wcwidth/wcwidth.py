
"""
This is a python implementation of wcwidth() and wcswidth().

https://github.com/jquast/wcwidth

From Markus Kuhn's C code, retrieved from:

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
    # std imports
    from functools import lru_cache
except ImportError:
    # lru_cache was added in Python 3.2
    # 3rd party
    from backports.functools_lru_cache import lru_cache

# global cache indicator
_PY3 = sys.version_info[0] >= 3


def _in_range(ucs, ranges):
    """
    Check if a Unicode code point 'ucs' lies within any of the given range tuples.

    :param int ucs: Unicode code point.
    :param list ranges: List of tuples, where each tuple is (lo, hi) inclusive.
    :return: True if ucs is within any of the provided ranges, False otherwise.
    :rtype: bool
    """
    if not ranges:
        return False
    # Quick bounds check
    if ucs < ranges[0][0] or ucs > ranges[-1][1]:
        return False

    lbound = 0
    ubound = len(ranges) - 1
    while lbound <= ubound:
        mid = (lbound + ubound) // 2
        lo, hi = ranges[mid]
        if ucs > hi:
            lbound = mid + 1
        elif ucs < lo:
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
    :return: The width, in cells, needed to display the character of the
        Unicode string ``wc``. Returns 0 if the argument has no printable effect
        on a terminal (such as NUL '\0'), -1 if ``wc`` is not printable or
        has an indeterminate effect on the terminal (such as a control character).
        Otherwise, the number of column positions the character occupies on a
        graphic terminal (1 or 2) is returned.
    :rtype: int

    See :ref:`Specification` for details of cell measurement.
    """
    ucs = ord(wc) if wc else 0

    # Optimization: Printable ASCII
    if 32 <= ucs < 0x7f:
        return 1

    # C0/C1 control characters are -1 for POSIX compatibility
    if (ucs and ucs < 32) or (0x07F <= ucs < 0x0A0):
        return -1

    _version = _wcmatch_version(unicode_version)

    # Check for zero-width characters.
    if not (ucs < ZERO_WIDTH[_version][0][0] or ucs > ZERO_WIDTH[_version][-1][1]):
        if _in_range(ucs, ZERO_WIDTH[_version]):
            return 0

    # Check for double-width characters.
    if ucs < WIDE_EASTASIAN[_version][0][0] or ucs > WIDE_EASTASIAN[_version][-1][1]:
        return 1
    if _in_range(ucs, WIDE_EASTASIAN[_version]):
        return 2

    return 1


def wcswidth(pwcs, n=None, unicode_version='auto'):
    """
    Given a unicode string, return its printable length on a terminal.

    :param str pwcs: Unicode string whose width is to be measured.
    :param int n: When None (default), measure the entire string; otherwise,
        only the first n characters are measured. This argument exists only for
        compatibility with the C POSIX function signature. It is suggested instead
        to use python's string slicing capability, e.g. wcswidth(pwcs[:n]).
    :param str unicode_version: Explicit definition of the Unicode version
        level to use for determination. It may be ``auto`` (default), which uses
        the environment variable ``UNICODE_VERSION`` if defined, or the latest
        available Unicode version otherwise.
    :rtype: int
    :returns: The width, in cells, needed to display the first n characters of
        the string pwcs. Returns ``-1`` if a C0 or C1 control character is found.

    See :ref:`Specification` for details of cell measurement.
    """
    _version_numeric = None
    end = len(pwcs) if n is None else n
    width = 0
    idx = 0
    last_measured_char = None

    while idx < end:
        char = pwcs[idx]
        if char == u'\u200D':
            # Zero Width Joiner, skip this and the next character.
            idx += 2
            continue
        if char == u'\uFE0F' and last_measured_char:
            # Variation Selector-16 (VS16) may convert a character from narrow to wide.
            if _version_numeric is None:
                # Obtain numeric version tuple for comparison.
                _version_numeric = _wcversion_value(_wcmatch_version(unicode_version))
            if _version_numeric >= (9, 0, 0):
                ucs = ord(last_measured_char)
                if _in_range(ucs, VS16_NARROW_TO_WIDE["9.0.0"]):
                    width += 1
            last_measured_char = None
            idx += 1
            continue

        # Measure width for current character.
        wcw = wcwidth(char, unicode_version)
        if wcw < 0:
            # Return -1 immediately on control characters.
            return wcw
        if wcw > 0:
            last_measured_char = char
        width += wcw
        idx += 1
    return width


@lru_cache(maxsize=128)
def _wcversion_value(ver_string):
    """
    Convert a dotted Unicode version string into a numeric tuple.

    :param str ver_string: Unicode version string (e.g., "6.0.0").
    :rtype: tuple(int)
    :returns: A tuple of integers representing the version.
    """
    return tuple(map(int, ver_string.split('.')))


@lru_cache(maxsize=8)
def _wcmatch_version(given_version):
    """
    Return the nearest matching supported Unicode version level.

    If an exact match is not available, the nearest lower supported version is
    returned (with a warning). For example, with supported versions "4.1.0" and
    "5.0.0", a requested version "4.9.9" will yield "4.1.0".

    Examples:
      >>> _wcmatch_version('4.9.9')
      '4.1.0'
      >>> _wcmatch_version('8.0')
      '8.0.0'
      >>> _wcmatch_version('1')
      '4.1.0'

    :param str given_version: Requested version (or "auto"). "auto" selects the
        Unicode version from the environment variable UNICODE_VERSION if set,
        or "latest" otherwise.
    :rtype: str
    :returns: A supported Unicode version string.
    """
    # Decide whether to work with byte strings (Python 2) or unicode.
    _return_str = not _PY3 and isinstance(given_version, str)

    if _return_str:
        unicode_versions = list(map(lambda u: u.encode(), list_versions()))
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
        warnings.warn("UNICODE_VERSION value, {0!r}, is invalid. "
                      "Value should be in the form of 'integer[.]+'. The latest "
                      "supported unicode version {1!r} has been inferred."
                      .format(given_version, latest_version))
        return latest_version if not _return_str else latest_version.encode()

    earliest_version = unicode_versions[0]
    cmp_earliest = _wcversion_value(earliest_version)
    if cmp_given <= cmp_earliest:
        warnings.warn("UNICODE_VERSION value, {0!r}, is lower than any available "
                      "unicode version. Returning lowest version level {1!r}."
                      .format(given_version, earliest_version))
        return earliest_version if not _return_str else earliest_version.encode()

    for idx, uv in enumerate(unicode_versions):
        try:
            cmp_next = _wcversion_value(unicode_versions[idx + 1])
        except IndexError:
            return latest_version if not _return_str else latest_version.encode()
        if cmp_given == cmp_next[:len(cmp_given)]:
            return unicode_versions[idx + 1]
        if cmp_next > cmp_given:
            return uv
    assert False, ("Code path unreachable", given_version, unicode_versions)  # pragma: no cover
