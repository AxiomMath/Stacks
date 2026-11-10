module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Localization away from an element as a sequential colimit

Let `A` be a commutative ring, `a ∈ A` and `M` an `A`-module. The localization
`M[1/a]` is the colimit of the sequence

`M --a--> M --a--> M --a--> ⋯`

the `n`-th structure map into the colimit being `m ↦ m/aⁿ`.

## Main definitions

* `Stacks.LocalCohomology.mulSeq`: the sequence of multiplication-by-`a` maps.
* `Stacks.LocalCohomology.locCocone`: the cocone on `M[1/a]` whose `n`-th leg is `m ↦ m/aⁿ`.
* `Stacks.LocalCohomology.isColimitLocCocone`: that cocone is a colimit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Multiplication by `a`, as an endomorphism of `M` in `ModuleCat A`. -/
def smulHom (a : A) (M : ModuleCat.{max u w} A) : M ⟶ M :=
  ModuleCat.ofHom (LinearMap.lsmul A M a)

/-- `Stacks.LocalCohomology.smulHom a M` sends `m` to `a • m`. -/
@[simp]
lemma smulHom_apply (a : A) (M : ModuleCat.{max u w} A) (m : M) :
    (smulHom a M).hom m = a • m := rfl

/-- The sequence `M --a--> M --a--> M --a--> ⋯` of multiplications by `a`. -/
@[reducible]
def mulSeq (a : A) (M : ModuleCat.{max u w} A) : ℕ ⥤ ModuleCat.{max u w} A where
  obj _ := M
  map {i j} φ := smulHom (a ^ (j - i)) M
  map_id i := by
    apply ModuleCat.hom_ext
    ext m
    change a ^ (i - i) • m = m
    rw [Nat.sub_self, pow_zero, one_smul]
  map_comp {i j k} φ ψ := by
    apply ModuleCat.hom_ext
    ext m
    change a ^ (k - i) • m = a ^ (k - j) • (a ^ (j - i) • m)
    rw [← mul_smul, ← pow_add, Nat.sub_add_sub_cancel (leOfHom ψ) (leOfHom φ)]

/-- The map `n ⟶ n + k` of the multiplication sequence is multiplication by `a ^ k`. -/
lemma mulSeq_map_le_add (a : A) (M : ModuleCat.{max u w} A) (n k : ℕ) :
    (mulSeq a M).map (homOfLE (Nat.le_add_right n k)) = smulHom (a ^ k) M := by
  change smulHom (a ^ (n + k - n)) M = _
  rw [Nat.add_sub_cancel_left]

/-- The map `n ⟶ n + 1` of the multiplication sequence is multiplication by `a`. -/
lemma mulSeq_map_succ (a : A) (M : ModuleCat.{max u w} A) (n : ℕ) :
    (mulSeq a M).map (homOfLE (Nat.le_add_right n 1)) = smulHom a M := by
  rw [mulSeq_map_le_add, pow_one]

/-- `a ^ n`, as an element of the submonoid of powers of `a`. -/
def powElt (a : A) (n : ℕ) : Submonoid.powers a := ⟨a ^ n, n, rfl⟩

/-- The underlying element of `Stacks.LocalCohomology.powElt a n` is `a ^ n`. -/
@[simp]
lemma powElt_coe (a : A) (n : ℕ) : ((powElt a n : Submonoid.powers a) : A) = a ^ n := rfl

/-- The localization `M[1/a]`, as an object of `ModuleCat A`. -/
@[reducible]
def locObj (a : A) (M : ModuleCat.{max u w} A) : ModuleCat.{max u w} A :=
  ModuleCat.of A (LocalizedModule (Submonoid.powers a) M)

/-- The `n`-th leg `m ↦ m/aⁿ` of the colimit presentation of `M[1/a]`. -/
def locLeg (a : A) (M : ModuleCat.{max u w} A) (n : ℕ) : M ⟶ locObj a M :=
  ModuleCat.ofHom
    ((LocalizedModule.divBy (powElt a n)).comp (LocalizedModule.mkLinearMap _ M))

/-- The `n`-th leg of the colimit presentation of `M[1/a]` sends `m` to `m / aⁿ`. -/
lemma locLeg_apply (a : A) (M : ModuleCat.{max u w} A) (n : ℕ) (m : M) :
    (locLeg a M n).hom m = LocalizedModule.mk m (powElt a n) := by
  change LocalizedModule.divBy (powElt a n) (LocalizedModule.mk m 1) = _
  rw [LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]

/-- The `(n + 1)`-th leg of the colimit presentation of `M[1/a]` sends `a • m` to the image of
`m` under the `n`-th leg. -/
lemma locLeg_succ_smul (a : A) (M : ModuleCat.{max u w} A) (n : ℕ) (m : M) :
    (locLeg a M (n + 1)).hom (a • m) = (locLeg a M n).hom m := by
  rw [locLeg_apply, locLeg_apply,
    ← LocalizedModule.mk_cancel_common_left (powElt a 1) (powElt a n) m, Submonoid.smul_def,
    powElt_coe, pow_one]
  congr 1
  ext
  simp [pow_succ']

/-- The cocone exhibiting `M[1/a]` as the colimit of the multiplication-by-`a` sequence. -/
def locCocone (a : A) (M : ModuleCat.{max u w} A) : Cocone (mulSeq a M) where
  pt := locObj a M
  ι := NatTrans.ofSequence (F := mulSeq a M) (G := (Functor.const ℕ).obj (locObj a M))
    (fun n ↦ locLeg a M n) (fun n ↦ by
      rw [mulSeq_map_succ]
      apply ModuleCat.hom_ext
      ext m
      exact locLeg_succ_smul a M n m)

/-- The `n`-th leg of `Stacks.LocalCohomology.locCocone a M` is
`Stacks.LocalCohomology.locLeg a M n`. -/
@[simp]
lemma locCocone_ι_app (a : A) (M : ModuleCat.{max u w} A) (n : ℕ) :
    (locCocone a M).ι.app n = locLeg a M n := rfl

section Desc

variable {a : A} {M : ModuleCat.{max u w} A} (t : Cocone (mulSeq a M))

/-- The legs of a cocone on the multiplication sequence absorb multiplication by powers
of `a`. -/
lemma cocone_ι_smul_pow (n k : ℕ) (m : M) :
    (t.ι.app (n + k)).hom (a ^ k • m) = (t.ι.app n).hom m := by
  have h := t.w (homOfLE (Nat.le_add_right n k))
  rw [mulSeq_map_le_add] at h
  exact congrArg (fun (g : M ⟶ t.pt) ↦ g.hom m) h

/-- Two representatives of the same element of `M[1/a]` are sent to the same element of the
tip of any cocone, whichever exponents are used to write their denominators. -/
lemma descFun_wd (p p' : M × Submonoid.powers a)
    (n n' : ℕ) (hn : (p.2 : A) = a ^ n) (hn' : (p'.2 : A) = a ^ n')
    (h : ∃ u : Submonoid.powers a, u • p'.2 • p.1 = u • p.2 • p'.1) :
    (t.ι.app n).hom p.1 = (t.ι.app n').hom p'.1 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨j, hj⟩ := u.2
  have hu' : (u : A) • ((p'.2 : A) • p.1) = (u : A) • ((p.2 : A) • p'.1) := by
    simpa only [Submonoid.smul_def] using hu
  rw [← hj, hn, hn'] at hu'
  have key : ∀ (n n' j : ℕ) (m : M),
      (t.ι.app (n + n' + j)).hom (a ^ j • (a ^ n' • m)) = (t.ι.app n).hom m := fun n n' j m ↦ by
    rw [← mul_smul, ← pow_add, add_comm j n', add_assoc]
    exact cocone_ι_smul_pow t n (n' + j) m
  calc (t.ι.app n).hom p.1
      = (t.ι.app (n + n' + j)).hom (a ^ j • (a ^ n' • p.1)) := (key n n' j p.1).symm
    _ = (t.ι.app (n + n' + j)).hom (a ^ j • (a ^ n • p'.1)) := by rw [hu']
    _ = (t.ι.app n').hom p'.1 := by rw [add_comm n n']; exact key n' n j p'.1

/-- The underlying function of the map descending a cocone through `M[1/a]`. -/
def descFun : LocalizedModule (Submonoid.powers a) M → t.pt :=
  fun x ↦ x.liftOn (fun p ↦ (t.ι.app p.2.2.choose).hom p.1)
    (fun p p' h ↦ descFun_wd t p p' _ _ p.2.2.choose_spec.symm p'.2.2.choose_spec.symm h)

/-- `Stacks.LocalCohomology.descFun t` sends `m / s` to the image of `m` under the `n`-th leg of
`t`, for any `n` with `s = aⁿ`. -/
lemma descFun_mk (m : M) (s : Submonoid.powers a) (n : ℕ) (hn : (s : A) = a ^ n) :
    descFun t (LocalizedModule.mk m s) = (t.ι.app n).hom m := by
  have h : descFun t (LocalizedModule.mk m s) = (t.ι.app (s.2.choose)).hom m :=
    LocalizedModule.liftOn_mk _ m s
  exact h.trans (descFun_wd t (m, s) (m, s) _ _ s.2.choose_spec.symm hn ⟨1, rfl⟩)

/-- `Stacks.LocalCohomology.descFun t` is additive. -/
lemma descFun_add (x y : LocalizedModule (Submonoid.powers a) M) :
    descFun t (x + y) = descFun t x + descFun t y := by
  refine x.induction_on₂ (fun m₁ m₂ s₁ s₂ ↦ ?_) y
  obtain ⟨n₁, hn₁⟩ := s₁.2
  obtain ⟨n₂, hn₂⟩ := s₂.2
  rw [LocalizedModule.mk_add_mk,
    descFun_mk t _ _ (n₁ + n₂) (by
      change ((s₁ * s₂ : Submonoid.powers a) : A) = a ^ (n₁ + n₂)
      rw [Submonoid.coe_mul, ← hn₁, ← hn₂, pow_add]),
    descFun_mk t m₁ s₁ n₁ hn₁.symm, descFun_mk t m₂ s₂ n₂ hn₂.symm, map_add]
  congr 1
  · rw [← cocone_ι_smul_pow t n₁ n₂ m₁]
    congr 1
    rw [Submonoid.smul_def, ← hn₂]
  · rw [show n₁ + n₂ = n₂ + n₁ by ring, ← cocone_ι_smul_pow t n₂ n₁ m₂]
    congr 1
    rw [Submonoid.smul_def, ← hn₁]

/-- `Stacks.LocalCohomology.descFun t` is `A`-linear. -/
lemma descFun_smul (c : A) (x : LocalizedModule (Submonoid.powers a) M) :
    descFun t (c • x) = c • descFun t x := by
  refine x.induction_on (fun m s ↦ ?_)
  obtain ⟨n, hn⟩ := s.2
  rw [LocalizedModule.smul'_mk, descFun_mk t _ _ n hn.symm, descFun_mk t m s n hn.symm, map_smul]

/-- The map descending a cocone through `M[1/a]`. -/
def descHom : locObj a M ⟶ t.pt :=
  ModuleCat.ofHom
    { toFun := descFun t
      map_add' := descFun_add t
      map_smul' := descFun_smul t }

/-- `Stacks.LocalCohomology.descHom t` sends `m / s` to the image of `m` under the `n`-th leg of
`t`, for any `n` with `s = aⁿ`. -/
lemma descHom_apply_mk (m : M) (s : Submonoid.powers a) (n : ℕ) (hn : (s : A) = a ^ n) :
    (descHom t).hom (LocalizedModule.mk m s) = (t.ι.app n).hom m :=
  descFun_mk t m s n hn

end Desc

/-- `M[1/a]`, with the legs `m ↦ m/aⁿ`, is the colimit of `M --a--> M --a--> ⋯`. -/
def isColimitLocCocone (a : A) (M : ModuleCat.{max u w} A) : IsColimit (locCocone a M) where
  desc t := descHom t
  fac t n := by
    apply ModuleCat.hom_ext
    ext m
    change (descHom t).hom ((locLeg a M n).hom m) = _
    rw [locLeg_apply, descHom_apply_mk t m (powElt a n) n rfl]
  uniq t g h := by
    apply ModuleCat.hom_ext
    ext x
    refine x.induction_on (fun m s ↦ ?_)
    obtain ⟨n, hn⟩ := s.2
    obtain rfl : s = powElt a n := Subtype.ext hn.symm
    have e : g.hom (LocalizedModule.mk m (powElt a n)) = (t.ι.app n).hom m := by
      rw [← h n]
      change _ = g.hom ((locLeg a M n).hom m)
      rw [locLeg_apply]
    exact e.trans (descHom_apply_mk t m (powElt a n) n rfl).symm

/-- The multiplication-by-`a` sequence on `M` has a colimit. -/
instance (a : A) (M : ModuleCat.{max u w} A) : HasColimit (mulSeq a M) :=
  ⟨⟨⟨locCocone a M, isColimitLocCocone a M⟩⟩⟩

end Stacks.LocalCohomology

end
