#pragma once
#include "../upper113/prefixes.hpp"

bool mixedMode(const string &name) {
  if (name == "2222")
    return false;
  if (name == "mixed")
    return true;
  throw runtime_error("expected 2222 or mixed");
}
// An encoded start in 0..6 denotes separation two. Adding seven denotes
// separation three.
int markedStart(int encoded, int which) {
  if (encoded < 0 || encoded >= 14)
    throw runtime_error("invalid marked start");
  return (encoded % 7 + which * (2 + encoded / 7)) % 7;
}
Mask contactKey(MaskId left, MaskId right) {
  return (Mask(left) << 32) | right;
}
