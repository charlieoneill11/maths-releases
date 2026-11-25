#pragma once
#include "atlas.hpp"
struct CutSites {
  Mask cover{};
  array<Mask, 49> pointBit{};
};
using AxisCuts = array<array<CutSites, 7>, 3>;
vector<AxisCuts> ports;
struct Assignment {
  Mask bits;
  vector<Mask> selected;
};
struct MiddleChoice {
  Mask middle;
  uint16_t first, second, motion, intersectionSize;
  uint8_t centers[3], middleSize;
  uint32_t distanceCode;
};
static_assert(sizeof(MiddleChoice) == 24);
