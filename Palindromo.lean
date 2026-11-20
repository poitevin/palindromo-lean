import Palindromo.Versos

set_option autoImplicit false

namespace Palindromo

private def normalizeLetter (c : Char) : Char :=
  match c with
  | 'á' | 'Á' => 'a'
  | 'é' | 'É' => 'e'
  | 'í' | 'Í' => 'i'
  | 'ó' | 'Ó' => 'o'
  | 'ú' | 'Ú' | 'ü' | 'Ü' => 'u'
  | 'Ñ' => 'ñ'
  | letter =>
    if letter.isUpper then Char.ofNat (letter.toNat + ('a'.toNat - 'A'.toNat)) else letter

/-- Letters of the Spanish text, ignoring case, vowel accents, spaces and punctuation. -/
def normalize (verse : List Char) : List Char :=
  (verse.map normalizeLetter).filter fun c => c.isLower || c == 'ñ'

inductive Half where
  | first
  | second

private def vectorAt {α : Type} {n : Nat} (data : Vector α n) (i : Fin n) : α :=
  data.toArray[i.val]'(data.size_toArray.symm ▸ i.isLt)

private def line (half : Half) (group digit : Fin 10) : List Char :=
  let pair := vectorAt (vectorAt versePairs group) digit
  normalize (match half with | .first => pair.1 | .second => pair.2)

private def firstIndex (n : Nat) : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩

private def allFin {n : Nat} (p : Fin n → Bool) : Bool :=
  match n with
  | 0 => true
  | n + 1 => p (firstIndex n) && allFin (fun i : Fin n => p i.succ)

private theorem allFin_sound {n : Nat} {p : Fin n → Bool}
    (h : allFin p = true) (i : Fin n) : p i = true := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have both := Bool.and_eq_true_iff.mp h
    exact Fin.cases both.1 (fun j => ih both.2 j) i

-- These pointwise list proofs avoid functional extensionality.
private theorem ofFn_cons {n : Nat} {α : Type} (f : Fin (n + 1) → α) :
    List.ofFn f = f 0 :: List.ofFn (fun i => f i.succ) := by
  rw [List.ofFn, Fin.foldr_succ]
  rfl

private theorem ofFn_snoc {n : Nat} {α : Type} (f : Fin (n + 1) → α) :
    List.ofFn f = List.ofFn (fun i => f i.castSucc) ++ [f (Fin.last n)] := by
  induction n with
  | zero => simp only [ofFn_cons, List.ofFn_zero, List.nil_append]; rfl
  | succ n ih =>
    rw [ofFn_cons f, ofFn_cons (fun i => f i.castSucc), ih]
    rfl

private theorem ofFn_congr {n : Nat} {α : Type} {f g : Fin n → α}
    (h : ∀ i, f i = g i) : List.ofFn f = List.ofFn g := by
  induction n with
  | zero => rw [List.ofFn_zero, List.ofFn_zero]
  | succ n ih => rw [ofFn_cons f, ofFn_cons g, h 0, ih (fun i => h i.succ)]

private theorem map_ofFn {n : Nat} {α β : Type} (f : Fin n → α) (g : α → β) :
    (List.ofFn f).map g = List.ofFn (fun i => g (f i)) := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.map_nil]
  | succ n ih => rw [ofFn_cons f, List.map_cons, ofFn_cons (fun i => g (f i)), ih]

private theorem reverse_ofFn {n : Nat} {α : Type} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.reverse_nil]
  | succ n ih =>
    rw [ofFn_cons f, List.reverse_cons, ih, ofFn_snoc (fun i => f i.rev), Fin.rev_last]
    exact congrArg (· ++ [f 0]) (ofFn_congr fun i => congrArg f (Fin.rev_castSucc i).symm)

private theorem ofFn_injective {n : Nat} {α : Type} {f g : Fin n → α}
    (h : List.ofFn f = List.ofFn g) (i : Fin n) : f i = g i := by
  have h' := congrArg (fun (xs : List α) => xs[i.val]?) h
  simpa [List.getElem?_eq_getElem, i.isLt] using h'

def openings : Nat := 10 ^ 10
def pages : Nat := 2 * openings

private def decimalDigits (places number : Nat) : Fin places → Fin 10 :=
  match places with
  | 0 => Fin.elim0
  | n + 1 => Fin.cases ⟨number % 10, Nat.mod_lt _ (by decide)⟩ (decimalDigits n (number / 10))

private theorem decimalDigits_injective {n a b : Nat} (ha : a < 10 ^ n) (hb : b < 10 ^ n)
    (h : ∀ i, decimalDigits n a i = decimalDigits n b i) : a = b := by
  induction n generalizing a b with
  | zero => exact (Nat.lt_one_iff.mp ha).trans (Nat.lt_one_iff.mp hb).symm
  | succ n ih =>
    rw [Nat.pow_succ] at ha hb
    have ha' := (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2 ha
    have hb' := (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2 hb
    have h₀ := congrArg Fin.val (h 0)
    change a % 10 = b % 10 at h₀
    have h₁ := ih ha' hb' (fun i => h i.succ)
    calc
      a = a % 10 + 10 * (a / 10) := (Nat.mod_add_div a 10).symm
      _ = b % 10 + 10 * (b / 10) := by rw [h₀, h₁]
      _ = b := Nat.mod_add_div b 10

private def firstLines (i : Fin openings) : Fin 10 → List Char :=
  fun group => line .first group (decimalDigits 10 i.val group)

private def secondLines (i : Fin openings) : Fin 10 → List Char :=
  fun group => line .second group (decimalDigits 10 i.val group)

private def stanza (half : Half) (i : Fin openings) : List (List Char) :=
  match half with
  | .first => List.ofFn (firstLines i)
  | .second => List.ofFn fun group => secondLines i group.rev

private theorem reverse_lt_openings (i : Fin pages) (h : ¬ i.val < openings) :
    i.rev.val < openings := by
  change pages - (i.val + 1) < openings
  have h' := Nat.succ_le_succ (Nat.not_lt.mp h)
  calc
    pages - (i.val + 1) ≤ pages - (openings + 1) := Nat.sub_le_sub_left h' pages
    _ < openings := by decide

private theorem reverse_ge_openings (i : Fin pages) (h : i.val < openings) :
    openings ≤ i.rev.val :=
  Nat.le_sub_of_add_le (Nat.add_le_add_left h openings)

/-- The ten normalized lines on a page in reading order. Indices start at zero. -/
def stanzaAt (i : Fin pages) : List (List Char) :=
  if hi : i.val < openings then
    stanza .first ⟨i.val, hi⟩
  else
    stanza .second ⟨i.rev.val, reverse_lt_openings i hi⟩

/-- The full normalized reading, in increasing page order. -/
def bookLetters : List Char :=
  (List.ofFn fun i : Fin pages => (stanzaAt i).flatten).flatten

-- The reversed second stanza can run ahead by one letter at a verse boundary.
-- Each entry is the outstanding letter after the indicated number of groups.
private def carry (boundary : Fin 11) : List Char :=
  match boundary.val with
  | 2 | 3 => ['a']
  | 4 => ['s']
  | 5 | 7 => ['y']
  | _ => []

private theorem checkedVerseMirrors : allFin (fun g => allFin (fun d =>
    line .first g d ++ carry g.succ ==
      carry g.castSucc ++ (line .second g d).reverse)) = true := by decide +kernel

private theorem verse_mirror (group digit : Fin 10) :
    line .first group digit ++ carry group.succ =
      carry group.castSucc ++ (line .second group digit).reverse := by
  exact eq_of_beq (allFin_sound (allFin_sound checkedVerseMirrors group) digit)

private theorem stitch {n : Nat} {α : Type} (left right : Fin n → List α)
    (boundary : Fin (n + 1) → List α)
    (step : ∀ i, left i ++ boundary i.succ = boundary i.castSucc ++ right i) :
    (List.ofFn left).flatten ++ boundary (Fin.last n) =
      boundary 0 ++ (List.ofFn right).flatten := by
  induction n with
  | zero => simp [Fin.last]
  | succ n ih =>
    simp only [ofFn_cons, List.flatten_cons]
    rw [show Fin.last (n + 1) = (Fin.last n).succ from rfl]
    rw [List.append_assoc, ih (fun i => left i.succ) (fun i => right i.succ)
      (fun i => boundary i.succ) (fun i => step i.succ)]
    rw [← List.append_assoc, step 0, List.append_assoc]
    simp

private theorem opening_mirror (i : Fin openings) :
    (stanza .first i).flatten = (stanza .second i).flatten.reverse := by
  have h := stitch (firstLines i) (fun g => (secondLines i g).reverse) carry
    (fun g => verse_mirror g (decimalDigits 10 i.val g))
  change (List.ofFn (firstLines i)).flatten ++ [] =
    [] ++ (List.ofFn fun g => (secondLines i g).reverse).flatten at h
  rw [List.append_nil, List.nil_append] at h
  change (List.ofFn (firstLines i)).flatten =
    (List.ofFn fun g => secondLines i g.rev).flatten.reverse
  rw [List.reverse_flatten, map_ofFn, reverse_ofFn]
  exact h.trans (congrArg List.flatten (ofFn_congr fun g =>
    congrArg (fun j => (secondLines i j).reverse) (Fin.rev_rev g).symm))

/-- Every page is the letter reversal of the page at the opposite end of the book. -/
theorem mirror_pages (i : Fin pages) :
    (stanzaAt i).flatten = (stanzaAt i.rev).flatten.reverse := by
  unfold stanzaAt
  have hre : i.rev.rev = i := Fin.rev_rev i
  by_cases hi : i.val < openings
  · have hj := Nat.not_lt.mpr (reverse_ge_openings i hi)
    simpa only [dif_pos hi, dif_neg hj, hre] using opening_mirror ⟨i.val, hi⟩
  · have hj := reverse_lt_openings i hi
    have h := congrArg List.reverse (opening_mirror ⟨i.rev.val, hj⟩)
    simpa only [dif_pos hj, dif_neg hi, List.reverse_reverse] using h.symm

/-- Reading all twenty billion décimas in page order gives a palindrome. -/
theorem book_is_palindrome : bookLetters.reverse = bookLetters := by
  unfold bookLetters
  rw [List.reverse_flatten, map_ofFn, reverse_ofFn]
  exact congrArg List.flatten (ofFn_congr fun i => (mirror_pages i).symm)

private theorem checkedWithinHalves (half : Half) :
    allFin (fun g => allFin (fun a => allFin (fun b =>
      a == b || line half g a != line half g b))) = true := by
  cases half <;> decide +kernel

private theorem line_injective (half : Half) (group : Fin 10) :
    ∀ (a b : Fin 10), line half group a = line half group b → a = b := by
  intro a b h
  have distinct := allFin_sound (allFin_sound (allFin_sound (checkedWithinHalves half) group) a) b
  simpa [h] using distinct

private theorem checkedAcrossHalves :
    allFin (fun a => allFin (fun b =>
      line .first (firstIndex 9) a != line .second (Fin.last 9) b)) = true := by
  decide +kernel

private theorem halves_disjoint (a b : Fin 10) :
    line .first (firstIndex 9) a ≠ line .second (Fin.last 9) b := by
  simpa using allFin_sound (allFin_sound checkedAcrossHalves a) b

private theorem stanza_injective (half : Half) {i j : Fin openings}
    (h : stanza half i = stanza half j) : i = j := by
  apply Fin.ext
  apply decimalDigits_injective i.isLt j.isLt
  intro group
  cases half with
  | first => exact line_injective .first group _ _ (ofFn_injective h group)
  | second =>
    have same := ofFn_injective h group.rev
    change secondLines i group.rev.rev = secondLines j group.rev.rev at same
    rw [Fin.rev_rev] at same
    exact line_injective .second group _ _ same

private theorem stanza_halves_disjoint (i j : Fin openings) :
    stanza .first i ≠ stanza .second j := by
  intro h
  have firstLine := ofFn_injective h 0
  exact halves_disjoint _ _ firstLine

/-- Any two pages with identical normalized stanzas have the same index. -/
theorem stanzas_are_unique {i j : Fin pages} (h : stanzaAt i = stanzaAt j) : i = j := by
  unfold stanzaAt at h
  split at h <;> split at h
  · exact Fin.ext (congrArg (Fin.val (n := openings)) (stanza_injective .first h))
  · exact False.elim (stanza_halves_disjoint _ _ h)
  · exact False.elim (stanza_halves_disjoint _ _ h.symm)
  · have he : i.rev = j.rev :=
      Fin.ext (congrArg (Fin.val (n := openings)) (stanza_injective .second h))
    simpa using congrArg Fin.rev he

theorem number_of_stanzas : pages = 20_000_000_000 := rfl

theorem lines_per_stanza (i : Fin pages) : (stanzaAt i).length = 10 := by
  unfold stanzaAt
  split <;> simp only [stanza, List.length_ofFn]

/-- info: '_private.Palindromo.0.Palindromo.checkedVerseMirrors' does not depend on any axioms -/
#guard_msgs in #print axioms checkedVerseMirrors

/-- info: '_private.Palindromo.0.Palindromo.checkedWithinHalves' does not depend on any axioms -/
#guard_msgs in #print axioms checkedWithinHalves

/-- info: '_private.Palindromo.0.Palindromo.checkedAcrossHalves' does not depend on any axioms -/
#guard_msgs in #print axioms checkedAcrossHalves

/-- info: 'Palindromo.book_is_palindrome' depends on axioms: [propext] -/
#guard_msgs in #print axioms book_is_palindrome

/-- info: 'Palindromo.stanzas_are_unique' depends on axioms: [propext] -/
#guard_msgs in #print axioms stanzas_are_unique

end Palindromo
