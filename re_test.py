import re

s="(^(([1-9]|22[0-3]|2[01][0-9]|1[013456789][0-9]|12[012345689]|[1-9][0-9])\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9]?[0-9])\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9]?[0-9]))/([0-9]|[1-2][0-9]|3[0-2])$)"

l=s.split("\.")
print l

