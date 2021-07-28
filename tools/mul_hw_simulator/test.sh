#!/bin/sh

g++ mul_hw.cpp -o mul_hw -lgmpxx -lgmp

echo "ffffffff80000000 ffffffffffff8000" | ./mul_hw
echo "ffffffff80000000 ffffffffffff8000" | ./mul_hw
