import Mathlib.Tactic

def is_even (n: Int): Prop := ∃ m : Int, n = (2 : Int) * m
def is_odd (n: Int) : Prop := ∃ m : Int, n = (2 : Int) * m + 1

theorem sum_of_two_odds_is_even (a : Int) (b : Int) :
    (is_odd a ∧ is_odd b → is_even (a+b)) := by
  intro h
  obtain ⟨ha, hb⟩ := h
  unfold is_odd at ha
  unfold is_odd at hb
  unfold is_even
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b', hb'⟩ := hb
  use a' + b' + 1
  calc
    a + b = (2*a' + 1) + (2*b' + 1) := by rw [ha', hb']
    _     = 2*a' + 2*b' + 2         := by ring
    _     = 2 * (a' + b' + 1)       := by ring

#check sum_of_two_odds_is_even 3 3
