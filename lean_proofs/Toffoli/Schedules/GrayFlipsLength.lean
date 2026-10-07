import Toffoli.Schedules.GrayScan
import Toffoli.Schedules.GrayWordsLength

namespace Toffoli

/-- There is one initial power evaluation and one after each sign change. -/
theorem gray_flips_length (n : ℕ) : (grayFlips n).length + 1 = 2 ^ n := by
  have h := congrArg List.length (gray_scan n)
  simpa [gray_words_length] using h

end Toffoli
