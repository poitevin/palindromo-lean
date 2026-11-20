import Palindromo.Versos

set_option autoImplicit false

namespace Palindromo

private def normalizeLetter (c : Char) : Char :=
  match c.toLower with
  | 'á' | 'Á' => 'a'
  | 'é' | 'É' => 'e'
  | 'í' | 'Í' => 'i'
  | 'ó' | 'Ó' => 'o'
  | 'ú' | 'Ú' | 'ü' | 'Ü' => 'u'
  | 'Ñ' => 'ñ'
  | letter => letter

/-- Letters of the Spanish text, ignoring case, vowel accents, spaces and punctuation. -/
def normalize (verse : String) : List Char :=
  (verse.toList.map normalizeLetter).filter fun c => ('a' ≤ c && c ≤ 'z') || c == 'ñ'

inductive Half where
  | first
  | second

private def line (half : Half) (group digit : Fin 10) : List Char :=
  let pair := versePairs[group.val * 10 + digit.val]'(by omega)
  normalize (match half with | .first => pair.1 | .second => pair.2)

private def allFin {n : Nat} (p : Fin n → Bool) : Bool :=
  (List.finRange n).all p

private theorem allFin_sound {n : Nat} {p : Fin n → Bool}
    (h : allFin p = true) (i : Fin n) : p i = true :=
  List.all_eq_true.mp h i (List.mem_finRange i)

private theorem reverse_ofFn {n : Nat} {α : Type} (f : Fin n → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem (by simp)
  intro i hl hr
  simp [List.getElem_reverse, Fin.rev]
  congr 1
  apply Fin.ext
  simp
  omega

private theorem ofFn_injective {n : Nat} {α : Type} {f g : Fin n → α}
    (h : List.ofFn f = List.ofFn g) (i : Fin n) : f i = g i := by
  have h' := congrArg (fun (xs : List α) => xs[i.val]?) h
  simpa [List.getElem?_eq_getElem, i.isLt] using h'

def openings : Nat := 10 ^ 10
def pages : Nat := 2 * openings

private def decimalDigits (places number : Nat) : Fin places → Fin 10 :=
  match places with
  | 0 => Fin.elim0
  | n + 1 => Fin.cases ⟨number % 10, by omega⟩ (decimalDigits n (number / 10))

private theorem decimalDigits_injective {n a b : Nat} (ha : a < 10 ^ n) (hb : b < 10 ^ n)
    (h : decimalDigits n a = decimalDigits n b) : a = b := by
  induction n generalizing a b with
  | zero => simp at ha hb; omega
  | succ n ih =>
    rw [Nat.pow_succ] at ha hb
    have ha' := (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2 ha
    have hb' := (Nat.div_lt_iff_lt_mul (by decide : 0 < 10)).2 hb
    have h₀ := congrArg Fin.val (congrFun h 0)
    change a % 10 = b % 10 at h₀
    have h₁ : decimalDigits n (a / 10) = decimalDigits n (b / 10) :=
      funext fun i => congrFun h i.succ
    have := ih ha' hb' h₁
    omega

private def firstLines (i : Fin openings) : Fin 10 → List Char :=
  fun group => line .first group (decimalDigits 10 i.val group)

private def secondLines (i : Fin openings) : Fin 10 → List Char :=
  fun group => line .second group (decimalDigits 10 i.val group)

private def stanza (half : Half) (i : Fin openings) : List (List Char) :=
  match half with
  | .first => List.ofFn (firstLines i)
  | .second => List.ofFn fun group => secondLines i group.rev

/-- The ten normalized lines on a page in reading order. Indices start at zero. -/
def stanzaAt (i : Fin pages) : List (List Char) :=
  if hi : i.val < openings then
    stanza .first ⟨i.val, hi⟩
  else
    stanza .second ⟨i.rev.val, by simp [Fin.rev, pages] at *; omega⟩

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

set_option maxHeartbeats 5000000 in
private theorem verse_mirror (group digit : Fin 10) :
    line .first group digit ++ carry group.succ =
      carry group.castSucc ++ (line .second group digit).reverse := by
  have checked : allFin (fun g => allFin (fun d =>
      line .first g d ++ carry g.succ ==
        carry g.castSucc ++ (line .second g d).reverse)) = true := by decide
  exact eq_of_beq (allFin_sound (allFin_sound checked group) digit)

private theorem stitch {n : Nat} {α : Type} (left right : Fin n → List α)
    (boundary : Fin (n + 1) → List α)
    (step : ∀ i, left i ++ boundary i.succ = boundary i.castSucc ++ right i) :
    (List.ofFn left).flatten ++ boundary (Fin.last n) =
      boundary 0 ++ (List.ofFn right).flatten := by
  induction n with
  | zero => simp [Fin.last]
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons]
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
  simpa [stanza, List.reverse_flatten, reverse_ofFn, List.map_ofFn, Fin.rev_rev] using h

/-- Every page is the letter reversal of the page at the opposite end of the book. -/
theorem mirror_pages (i : Fin pages) :
    (stanzaAt i).flatten = (stanzaAt i.rev).flatten.reverse := by
  unfold stanzaAt
  have hre : i.rev.rev = i := Fin.rev_rev i
  by_cases hi : i.val < openings
  · have hj : ¬ i.rev.val < openings := by simp [Fin.rev, pages] at *; omega
    simpa only [dif_pos hi, dif_neg hj, hre] using opening_mirror ⟨i.val, hi⟩
  · have hj : i.rev.val < openings := by simp [Fin.rev, pages] at *; omega
    have h := congrArg List.reverse (opening_mirror ⟨i.rev.val, hj⟩)
    simpa only [dif_pos hj, dif_neg hi, List.reverse_reverse] using h.symm

/-- Reading all twenty billion décimas in page order gives a palindrome. -/
theorem book_is_palindrome : bookLetters.reverse = bookLetters := by
  unfold bookLetters
  rw [List.reverse_flatten, List.map_ofFn, reverse_ofFn]
  exact congrArg (fun f => (List.ofFn f).flatten) (funext fun i => (mirror_pages i).symm)

set_option maxHeartbeats 5000000 in
private theorem line_injective (half : Half) (group : Fin 10) :
    ∀ (a b : Fin 10), line half group a = line half group b → a = b := by
  have checked : ∀ half, allFin (fun g => allFin (fun a => allFin (fun b =>
      a == b || line half g a != line half g b))) = true := by
    intro side
    cases side <;> decide
  intro a b h
  have distinct := allFin_sound (allFin_sound (allFin_sound (checked half) group) a) b
  simpa [h] using distinct

private theorem halves_disjoint (a b : Fin 10) :
    line .first 0 a ≠ line .second 9 b := by
  have checked : allFin (fun a => allFin (fun b => line .first 0 a != line .second 9 b))
      = true := by decide
  simpa using allFin_sound (allFin_sound checked a) b

private theorem stanza_injective (half : Half) {i j : Fin openings}
    (h : stanza half i = stanza half j) : i = j := by
  apply Fin.ext
  apply decimalDigits_injective i.isLt j.isLt
  funext group
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
  split <;> simp [stanza]

#print axioms book_is_palindrome
#print axioms stanzas_are_unique

end Palindromo
