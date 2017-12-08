#!/bin/bash

for t in num;
do
  ./mh tests/$t.mh > tests/${t}-out.mh
  diff tests/${t}-out.mh tests/${t}-exp.mh
done
