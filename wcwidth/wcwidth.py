
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
In all these cases, there is no ambiguity about which width a terminal
shall use. For characters in the East Asian Ambiguous (A)
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
    from functools import lru_cache
except ImportError:
    from backports.functools_lru_cache import lru_cache

# global flag for Python3+
_PY3 = sys.version_info[0] >= 3


def _binary_search_intervals(ucs, intervals):
    """
    Helper function to perform a binary search over a list of interval tuples.
    
    :param int ucs: Unicode code point to search.
    :param list intervals: List of tuples (start, end) sorted in ascending order.
    :return: True if ucs is within any of the intervals, False otherwise.
    :rtype: bool
    """
    if not intervals:
        return False
    if ucs < intervals[0][0] or ucs > intervals[-1][1]:
        return False
    lbound = 0
    ubound = len(intervals) - 1
    while lbound <= ubound:
        mid = (lbound + ubound) // 2
        lo, hi = intervals[mid]
        if ucs < lo:
            ubound = mid - 1
        elif ucs > hi:
            lbound = mid + 1
        else:
            return True
    return False


def _is_printable_ascii(ucs):
    """
    Check if the given Unicode code point is in the printable ASCII range.
    
    :param int ucs: Unicode code point.
    :return: True if ucs is printable ASCII, False otherwise.
    :rtype: bool
    """
    return 32 <= ucs < 0x7f


def _is_control(ucs):
    """
    Check if the code point represents a C0/C1 control character.
    
    :param int ucs: Unicode code point.
    :return: True if it is a control character, False otherwise.
    :rtype: bool
    """
    return (ucs and ucs < 32) or (0x7F <= ucs < 0x0A0)


def _lookup_interval_width(ucs, table, unicode_version, width_value):
    """
    Generic lookup to test whether a code point falls into an interval table.

    :param int ucs: Unicode code point.
    :param dict table: Mapping from Unicode version to list of intervals.
    :param str unicode_version: The matched Unicode version string.
    :param int width_value: The width value to return if a match is found.
    :return: width_value if the code point is found; None otherwise.
    """
    intervals = table[unicode_version]
    if ucs < intervals[0][0] or ucs > intervals[-1][1]:
        return None
    if _binary_search_intervals(ucs, intervals):
        return width_value
    return None


def _apply_variation_selector(last_measured_char, unicode_version_tuple):
    """
    Apply the Variation Selector-16 rule for characters.

    :param str last_measured_char: The last character that was measured.
    :param tuple unicode_version_tuple: Tuple representation of the Unicode version.
    :return: True if an extra width should be applied, False otherwise.
    """
    # For Unicode version 9.0.0 or greater, check the VS16 table.
    if unicode_version_tuple >= (9, 0, 0):
        ucs = ord(last_measured_char)
        intervals = VS16_NARROW_TO_WIDE["9.0.0"]
        if not (ucs < intervals[0][0] or ucs > intervals[-1][1]):
            if _binary_search_intervals(ucs, intervals):
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
    :return: The width, in cells, necessary to display the Unicode character,
        ``wc``. Returns 0 if the argument has no printable effect on a terminal
        (such as NUL '\0'), -1 if ``wc`` is not printable (e.g. a control character),
        or the number of column positions (typically 1 or 2) otherwise.
    :rtype: int

    See :ref:`Specification` for details of cell measurement.
    """
    ucs = ord(wc) if wc else 0

    # Fast path for printable ASCII (approx. 40% performance improvement)
    if _is_printable_ascii(ucs):
        return 1

    # C0/C1 control characters are non-printable: return -1.
    if _is_control(ucs):
        return -1

    _unicode_version = _wcmatch_version(unicode_version)

    # Check zero-width intervals.
    zero_width = _lookup_interval_width(ucs, ZERO_WIDTH, _unicode_version, 0)
    if zero_width is not None:
        return zero_width

    # Check for wide (double-width) characters.
    wide_width = _lookup_interval_width(ucs, WIDE_EASTASIAN, _unicode_version, 2)
    if wide_width is not None:
        return wide_width

    return 1


def wcswidth(pwcs, n=None, unicode_version='auto'):
    """
    Given a Unicode string, return its printable length on a terminal.

    :param str pwcs: Unicode string to measure.
    :param int n: If ``n`` is None (default), measure the entire string, otherwise
                  only the first ``n`` characters are considered (for POSIX compatibility).
                  It is suggested to use Python's string slicing, e.g., wcswidth(pwcs[:n]).
    :param str unicode_version: Explicit Unicode version level to use, or ``auto``
                                (default) to select from the environment variable
                                ``UNICODE_VERSION`` or the latest available if unset.
    :rtype: int
    :returns: The width, in cells, needed to display the string. Returns -1 for
              non-printable characters (C0/C1 control characters).
    
    See :ref:`Specification` for details of cell measurement.
    """
    end = len(pwcs) if n is None else n
    width = 0
    idx = 0
    last_measured_char = None
    cached_unicode_version_tuple = None

    while idx < end:
        char = pwcs[idx]

        if char == u'\u200D':
            # Zero Width Joiner: skip this and the subsequent character.
            idx += 2
            continue

        if char == u'\uFE0F' and last_measured_char:
            # Handle Variation Selector-16: conditionally add width if last character
            # is converted from narrow to wide by VS16.
            if cached_unicode_version_tuple is None:
                _matched_version = _wcmatch_version(unicode_version)
                cached_unicode_version_tuple = _wcversion_value(_matched_version)
            if _apply_variation_selector(last_measured_char, cached_unicode_version_tuple):
                width += 1
            last_measured_char = None
            idx += 1
            continue

        wcw = wcwidth(char, unicode_version)
        if wcw < 0:
            # Early return for non-printable characters.
            return wcw
        if wcw > 0:
            last_measured_char = char
        width += wcw
        idx += 1

    return width


@lru_cache(maxsize=128)
def _wcversion_value(ver_string):
    """
    Convert a dotted Unicode version string to a tuple of integers.

    :param str ver_string: Unicode version string of the form ``n.n.n``.
    :rtype: tuple
    :returns: Tuple of integers representing the version.
    """
    return tuple(map(int, ver_string.split('.')))


@lru_cache(maxsize=8)
def _wcmatch_version(given_version):
    """
    Return the nearest matching supported Unicode version level.

    If an exact match is not determined, the nearest lower version is
    returned and a warning is emitted. For example:
    
    >>> _wcmatch_version('4.9.9')
    '4.1.0'
    >>> _wcmatch_version('8.0')
    '8.0.0'
    >>> _wcmatch_version('1')
    '4.1.0'

    :param str given_version: Version string (or "auto") to compare. "auto" selects
                              the version based on the ``UNICODE_VERSION`` environment
                              variable, or uses the latest supported if not set.
    :rtype: str
    :returns: The selected Unicode version string.
    """
    _return_str = (not _PY3) and isinstance(given_version, str)

    if _return_str:
        unicode_versions = list(map(lambda ucs: ucs.encode(), list_versions()))
    else:
        unicode_versions = list_versions()
    latest_version = unicode_versions[-1]

    if given_version in (u'auto', 'auto'):
        given_version = os.environ.get(
            'UNICODE_VERSION',
            latest_version if not _return_str else latest_version.encode())

    if given_version in (u'latest', 'latest'):
        return latest_version if not _return_str else latest_version.encode()

    if given_version in unicode_versions:
        return given_version if not _return_str else given_version.encode()

    try:
        cmp_given = _wcversion_value(given_version)
    except ValueError:
        warnings.warn("UNICODE_VERSION value {0!r} is invalid. "
                      "It should be in the form of 'integer[.]+'. "
                      "Inferring the latest supported version {1!r}.".format(
                          given_version, latest_version))
        return latest_version if not _return_str else latest_version.encode()

    earliest_version = unicode_versions[0]
    cmp_earliest_version = _wcversion_value(earliest_version)

    if cmp_given <= cmp_earliest_version:
        warnings.warn("UNICODE_VERSION value {0!r} is lower than any available "
                      "version. Returning the lowest supported version {1!r}.".format(
                          given_version, earliest_version))
        return earliest_version if not _return_str else earliest_version.encode()

    # Iterate through supported versions to find the nearest match.
    for idx, unicode_version in enumerate(unicode_versions):
        try:
            cmp_next_version = _wcversion_value(unicode_versions[idx + 1])
        except IndexError:
            return latest_version if not _return_str else latest_version.encode()

        if cmp_given == cmp_next_version[:len(cmp_given)]:
            return unicode_versions[idx + 1]
        if cmp_next_version > cmp_given:
            return unicode_version

    # Code path should be unreachable.
    assert False, ("Code path unreachable", given_version, unicode_versions)
