
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


# --- Reusable Helper Functions ---

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


def _in_intervals(ucs, intervals):
    """
    Check if the given code point is within the provided intervals.
    
    :param int ucs: Unicode code point
    :param list intervals: List of (start, end) tuples
    :return: True if ucs is in one of the intervals, False otherwise.
    :rtype: bool
    """
    if ucs < intervals[0][0] or ucs > intervals[-1][1]:
        return False
    return _binary_search_intervals(ucs, intervals)


@lru_cache(maxsize=128)
def _wcversion_value(ver_string):
    """
    Convert a dotted Unicode version string to a tuple of integers.

    :param str ver_string: Unicode version string of the form 'n.n.n'.
    :return: Tuple of integers representing the version.
    :rtype: tuple
    """
    return tuple(map(int, ver_string.split('.')))


@lru_cache(maxsize=8)
def _wcmatch_version(given_version):
    """
    Return the nearest matching supported Unicode version level.

    If an exact match is not determined, the nearest lower version is
    returned and a warning is emitted.

    :param str given_version: Version string (or "auto") to compare.
    :return: The selected Unicode version string.
    :rtype: str
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


def _apply_variation_selector(last_measured_char, base_version):
    """
    Determines if an extra cell width should be added due to Variation Selector-16 (U+FE0F)
    converting a narrow character into a wide form.

    :param str last_measured_char: The previous character measured (with a cell).
    :param tuple base_version: Unicode version tuple.
    :return: 1 if the last measured character should be rendered as wide in the context
             of VS16, otherwise 0.
    :rtype: int
    """
    if base_version >= (9, 0, 0):
        ucs = ord(last_measured_char)
        table = VS16_NARROW_TO_WIDE["9.0.0"]
        if ucs >= table[0][0] and ucs <= table[-1][1]:
            if _binary_search_intervals(ucs, table):
                return 1
    return 0


# --- Main Functions ---

@lru_cache(maxsize=1000)
def wcwidth(wc, unicode_version='auto'):
    r"""
    Given one Unicode character, return its printable length on a terminal.

    :param str wc: A single Unicode character.
    :param str unicode_version: A Unicode version number, e.g., '6.0.0'. 'auto' (default)
                                selects via the UNICODE_VERSION environment variable or the latest.
    :return: The width needed to display the Unicode character: 0 for zero-width, -1 for non-printable,
             or typically 1 or 2.
    :rtype: int
    """
    ucs = ord(wc) if wc else 0

    # Fast path for printable ASCII (approx. 40% performance improvement).
    if 32 <= ucs < 0x7f:
        return 1

    # C0/C1 control characters are non-printable: return -1.
    if (ucs and ucs < 32) or (0x7F <= ucs < 0x0A0):
        return -1

    _unicode_version = _wcmatch_version(unicode_version)

    # Check zero-width intervals.
    if not (ucs < ZERO_WIDTH[_unicode_version][0][0] or
            ucs > ZERO_WIDTH[_unicode_version][-1][1]):
        if _binary_search_intervals(ucs, ZERO_WIDTH[_unicode_version]):
            return 0

    # Check for wide (double-width) characters.
    if ucs < WIDE_EASTASIAN[_unicode_version][0][0] or \
       ucs > WIDE_EASTASIAN[_unicode_version][-1][1]:
        return 1
    if _binary_search_intervals(ucs, WIDE_EASTASIAN[_unicode_version]):
        return 2

    return 1


def wcswidth(pwcs, n=None, unicode_version='auto'):
    """
    Given a Unicode string, return its printable length on a terminal.

    :param str pwcs: Unicode string to measure.
    :param int n: If None (default), measure the entire string, otherwise only the first n characters.
    :param str unicode_version: Unicode version to use, or 'auto' to select based on environment or latest.
    :return: The width, in cells, needed to display the string; returns -1 for non-printable characters.
    :rtype: int
    """
    _unicode_version = None
    end = len(pwcs) if n is None else n
    width = 0
    idx = 0
    last_measured_char = None

    while idx < end:
        char = pwcs[idx]
        if char == u'\u200D':
            # Zero Width Joiner: skip this and the subsequent character.
            idx += 2
            continue

        if char == u'\uFE0F' and last_measured_char:
            # Variation Selector-16 handling.
            if _unicode_version is None:
                _unicode_version = _wcversion_value(_wcmatch_version(unicode_version))
            width += _apply_variation_selector(last_measured_char, _unicode_version)
            last_measured_char = None
            idx += 1
            continue

        # Measure the current character.
        wcw = wcwidth(char, unicode_version)
        if wcw < 0:
            # Early return for non-printable characters.
            return wcw
        if wcw > 0:
            last_measured_char = char
        width += wcw
        idx += 1

    return width
