#!/usr/bin/env python

from __future__ import print_function
from __future__ import unicode_literals
from itertools import groupby
from operator import itemgetter
import binascii
import re
import struct 
import argparse
import os

'''
##     ## ########   ######      ######## ######## ######## #### ########    ###     ######  
###   ### ##     ## ##    ##     ##       ##       ##        ##     ##      ## ##   ##    ## 
#### #### ##     ## ##           ##       ##       ##        ##     ##     ##   ##  ##       
## ### ## ########  ##   ####    ######   ######   ######    ##     ##    ##     ##  ######  
##     ## ##   ##   ##    ##     ##       ##       ##        ##     ##    #########       ## 
##     ## ##    ##  ##    ##     ##       ##       ##        ##     ##    ##     ## ##    ## 
##     ## ##     ##  ######      ######## ##       ##       ####    ##    ##     ##  ###### 
'''

'''
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
'''

print ("Auto XOR decryptor by MRG Effitas. Developed and tested on Python 3.3!") 
print ("")
print ("This tool can automagically find short XOR keys in a XOR encrypted binary file, and use ")
print ("that to decrypt the XOR encrypted binary. Most parameters are good on default ")
print ("but if it is not working for you, you might try to fine-tune those.")

parser = argparse.ArgumentParser()
parser.add_argument("--input", action="store", dest="input", required=False,
                    default="encrypted", help="input file name, default is encrypted")

parser.add_argument("--output", action="store", dest="output", required=False,
                    default="decrypted", help="output file name, default is decrypted")

parser.add_argument("--xorkeyhex", action="store", dest="xor_key_hex",
                    required=False, help="xor key in hex, e.g. 31323334")

parser.add_argument("--xorkeyascii", action="store", dest="xor_key_ascii",
                    required=False, help="xor key in ascii, e.g. ijkl")

parser.add_argument("--offset", action="store", dest="offset", required=False,
                    help="offset to rotate the xor key")

parser.add_argument("--keyminlen", action="store", dest="keyminlen", required=False,
                    default="2", help="minimum key length (measured in hex string), default 2")

parser.add_argument("--patternmaxsearch", action="store", dest="patternmaxsearch", required=False,
                    default="500", help="max length to search for pattern in the result, default 500")

parser.add_argument("--xorkeymaxsearch", action="store", dest="xorkeymaxsearch", required=False,
                    default="500", help="max distance to search for XOR key in the encrypted file, default 500")


parser.add_argument("--pattern", action="store", dest="pattern", required=False
                    , default=b"program", help="pattern which is found in valid"
                    "file. e.g. \"This program cannot be run in DOS mode\"."
                    " Default is \"program\" . ")

# Parse the arguments
args = parser.parse_args()
filename = args.input
output = args.output
if args.xor_key_hex:
    xor_key = args.xor_key_hex
if args.xor_key_ascii:
    xor_key_ascii = args.xor_key_ascii
if args.offset:
    offset = int(args.offset)

# the longest_common_substring and suffix_array methods are from http://stackoverflow.com/a/13693834/2716262
def longest_common_substring(text):
    """Get the longest common substrings and their positions.
    >>> longest_common_substring('banana')
    {'ana': [1, 3]}
    >>> text = "not so Agamemnon, who spoke fiercely to "
    >>> sorted(longest_common_substring(text).items())
    [(' s', [3, 21]), ('no', [0, 13]), ('o ', [5, 20, 38])]

    This function can be easy modified for any criteria, e.g. for searching ten
    longest non overlapping repeated substrings.
    """
    sa, rsa, lcp = suffix_array(text)
    maxlen = max(lcp)
    result = {}
    for i in range(1, len(text)):
        if lcp[i] == maxlen:
            j1, j2, h = sa[i - 1], sa[i], lcp[i]
            assert text[j1:j1 + h] == text[j2:j2 + h]
            substring = text[j1:j1 + h]
            if not substring in result:
                result[substring] = [j1]
            # result[substring].append(j2)
    # return dict((k, sorted(v)) for k, v in result.items())
    return substring

def suffix_array(text, _step=16):
    """Analyze all common strings in the text.

    Short substrings of the length _step a are first pre-sorted. The are the 
    results repeatedly merged so that the garanteed number of compared
    characters bytes is doubled in every iteration until all substrings are
    sorted exactly.

    Arguments:
        text:  The text to be analyzed.
        _step: Is only for optimization and testing. It is the optimal length
               of substrings used for initial pre-sorting. The bigger value is
               faster if there is enough memory. Memory requirements are
               approximately (estimate for 32 bit Python 3.3):
                   len(text) * (29 + (_size + 20 if _size > 2 else 0)) + 1MB

    Return value:      (tuple)
      (sa, rsa, lcp)
        sa:  Suffix array                  for i in range(1, size):
               assert text[sa[i-1]:] < text[sa[i]:]
        rsa: Reverse suffix array          for i in range(size):
               assert rsa[sa[i]] == i
        lcp: Longest common prefix         for i in range(1, size):
               assert text[sa[i-1]:sa[i-1]+lcp[i]] == text[sa[i]:sa[i]+lcp[i]]
               if sa[i-1] + lcp[i] < len(text):
                   assert text[sa[i-1] + lcp[i]] < text[sa[i] + lcp[i]]
    >>> suffix_array(text='banana')
    ([5, 3, 1, 0, 4, 2], [3, 2, 5, 1, 4, 0], [0, 1, 3, 0, 0, 2])

    Explanation: 'a' < 'ana' < 'anana' < 'banana' < 'na' < 'nana'
    The Longest Common String is 'ana': lcp[2] == 3 == len('ana')
    It is between  tx[sa[1]:] == 'ana' < 'anana' == tx[sa[2]:]
    """
    tx = text
    size = len(tx)
    step = min(max(_step, 1), len(tx))
    sa = list(range(len(tx)))
    sa.sort(key=lambda i: tx[i:i + step])
    grpstart = size * [False] + [True]  # a boolean map for iteration speedup.
    # It helps to skip yet resolved values. The last value True is a sentinel.
    rsa = size * [None]
    stgrp, igrp = '', 0
    for i, pos in enumerate(sa):
        st = tx[pos:pos + step]
        if st != stgrp:
            grpstart[igrp] = (igrp < i - 1)
            stgrp = st
            igrp = i
        rsa[pos] = igrp
        sa[i] = pos
    grpstart[igrp] = (igrp < size - 1 or size == 0)
    while grpstart.index(True) < size:
        # assert step <= size
        nextgr = grpstart.index(True)
        while nextgr < size:
            igrp = nextgr
            nextgr = grpstart.index(True, igrp + 1)
            glist = []
            for ig in range(igrp, nextgr):
                pos = sa[ig]
                if rsa[pos] != igrp:
                    break
                newgr = rsa[pos + step] if pos + step < size else -1
                glist.append((newgr, pos))
            glist.sort()
            for ig, g in groupby(glist, key=itemgetter(0)):
                g = [x[1] for x in g]
                sa[igrp:igrp + len(g)] = g
                grpstart[igrp] = (len(g) > 1)
                for pos in g:
                    rsa[pos] = igrp
                igrp += len(g)
        step *= 2
    del grpstart
    # create LCP array
    lcp = size * [None]
    h = 0
    for i in range(size):
        if rsa[i] > 0:
            j = sa[rsa[i] - 1]
            while i != size - h and j != size - h and tx[i + h] == tx[j + h]:
                h += 1
            lcp[rsa[i]] = h
            if h > 0:
                h -= 1
    if size > 0:
        lcp[0] = 0
    return sa, rsa, lcp

# XOR stream cipher
def cipher(infile, outfile, padfile):
    block_size = len(padfile)
    while 1:
        # read data in block of the XOR key size
        data = infile.read(block_size)
        if not data:
            break
        # Python 2.7 BUG: bytes and strings are a bit messed up here
        # when you are working with older Python versions.
        # Might be fixed in future versions
        encoded = [ a ^ b for a, b in zip(data, padfile) ]
        for item in encoded:
            # write the result to the output file
            outfile.write (struct.pack("B", item))

filename = args.input
# only guess the XOR key based on the first 500 (or whatever you defined) bytes
with open(filename, 'rb') as f:
    content = f.read(int(args.xorkeymaxsearch))
    #print (args.xorkeymaxsearch)
f.close()

try:
    xor_key
# if we don't have the final xor_key from the user 
except NameError:   
    try:
        xor_key_ascii
        # but the user defined the ascii xor key
        xor_key = binascii.hexlify(xor_key_ascii.encode('ascii'))
        # xor_key = ''.join(long_xor_key[i:i + 2] 
        #                for i in range(0, len(long_xor_key), 2))
        #print (xor_key)                
    except NameError: 
        # when the user have not provided any guess about the XOR key  
        long_xor_key = str(longest_common_substring(binascii.hexlify(content)))
        #print ("longxorkey: " +  long_xor_key)
        formatted_hex = ''.join(long_xor_key[i:i + 2] for i in range(0,
                        len(long_xor_key), 2))
        print ("XOR key: " + formatted_hex)
        r = re.compile("(.{" + args.keyminlen + r",}?)\1+")             
        xor_key_list = r.findall(formatted_hex)
        xor_key = xor_key_list[0] 
#print (xor_key)    
# binary XOR key to be used in decryption
xor_key_bin = binascii.unhexlify(xor_key)
print ("XOR key ascii: " + str(xor_key_bin))
print ("XOR key hex: " + str(binascii.hexlify(xor_key_bin)))
data = open (filename, 'rb+')
edit = data.read () 
data.close ()

try:
    offset
except NameError:
    # when the user have not provided any offset, try to guess it
    offset = len(xor_key_bin) - (edit.find (xor_key_bin) % len(xor_key_bin))
print ("Offset: " + str(offset))

def rotate(str1, n):
    rotated = str1[n:] + str1[:n]
    return rotated

# generate the final XOR key, rotate the xor_key with the offset
final_xor_key = binascii.unhexlify(rotate(xor_key, offset * 2))
print("Final XOR key: " + str(final_xor_key))
with open(output, 'wb') as d:
    with open(filename, 'rb') as f:
        # call the XOR decryptor with input file, output file and XOR key
        cipher (f, d, final_xor_key)
f.close()
d.close()

# Test whether decryption was successful, only check first 500 bytes.
filehandle = open (output, 'rb+')
data = filehandle.read (int(args.patternmaxsearch)) 
filehandle.close ()
pattern = args.pattern
rx = re.compile(pattern, re.IGNORECASE | re.MULTILINE | re.DOTALL)
result = rx.findall(data)
if not result:
    print ("Decrypt failed, or check your pattern. Output destination file has been deleted.")
    os.remove(output)
else:
    print ("Great success! input read from : " + str(filename) + 
           ", output written to : " + str(output))

