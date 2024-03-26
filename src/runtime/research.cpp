#include "util/io.h"
#include <cstdlib> // For std::getenv
#include <assert.h>
#include <cstdint>

extern "C" {
uint8_t research_isReuseAcrossConstructorsEnabled(lean_object *) {
  const char *_var = std::getenv("RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED");
  if (!_var) {
     return true;
  } else {
    std::string var(_var);
    assert (var == "true" || var == "false");
    return var == "true";
  }
}
}
