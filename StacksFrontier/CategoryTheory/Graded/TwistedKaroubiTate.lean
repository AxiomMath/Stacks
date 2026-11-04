module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiDegreeZero
public import StacksFrontier.CategoryTheory.Monoidal.InvertingObject

/-!
# Every twisted idempotent is an untwisted one up to Tate twists

Let `C` be a category graded over a ring `R` with a graded symmetric monoidal structure. In the
twisted Karoubi envelope the triples `T(n) = (𝟙, 𝟙, n)` are the twists: `T(n) ⊗ T(m) ≅ T(n + m)`
and `M ⊗ T(m) ≅ (X, p, n + m)` for `M = (X, p, n)`. For the functor `K : (X, p) ↦ (X, p, 0)` of
`CategoryTheory.GradedCategory.TwistedKaroubi.untwisted` and an object `L` with `K(L) ≅ T(-1)`:

* the symmetry of `T(1) ⊗ T(1)` is the identity;
* `K(L) ⊗ T(1) ≅ 𝟙`;
* every object `M` is isomorphic to `K(A) ⊗ T(1)^{⊗ n}` for some `A` and some `n : ℕ`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.tateTriple`: the twisted unit `(𝟙_ C, 𝟙, n)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.untwistedTensorTateIso`: `K(L) ⊗ T(1) ≅ 𝟙`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.braiding_tateTriple_one`: the symmetry of
  `T(1) ⊗ T(1)` is the identity.
* `CategoryTheory.GradedCategory.TwistedKaroubi.exists_iso_untwisted_tensor_tensorPow`: every
  object is isomorphic to some `K(A) ⊗ T(1)^{⊗ n}`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Idempotents

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

variable (R C) in
/-- The twisted unit `T(n) = (𝟙_ C, 𝟙, n)`. -/
abbrev tateTriple (n : ℤ) : TwistedKaroubi R C :=
  { ofObj (R := R) (𝟙_ C) with twist := n }

/-- `T(a)^{⊗ n} ≅ T(a n)`. -/
def tensorPowTateTripleIso (a : ℤ) :
    (n : ℕ) → tensorPow (tateTriple R C a) n ≅ tateTriple R C (a * n)
  | 0 => twistCongrIso (ofObj (R := R) (𝟙_ C)) (by simp)
  | n + 1 => whiskerRightIso (tensorPowTateTripleIso a n) (tateTriple R C a) ≪≫
      unitTwistTensorIso (a * n) a ≪≫ twistCongrIso (ofObj (R := R) (𝟙_ C)) (by push_cast; ring)

/-- The tensor power of an isomorphism. -/
def tensorPowIso {D : Type*} [Category D] [MonoidalCategory D] {X Y : D} (e : X ≅ Y) :
    (n : ℕ) → tensorPow X n ≅ tensorPow Y n
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowIso e n) e

/-- A monoidal functor commutes with tensor powers. -/
def tensorPowMapIso {D E : Type*} [Category D] [MonoidalCategory D] [Category E]
    [MonoidalCategory E] (F : D ⥤ E) [F.Monoidal] (X : D) :
    (n : ℕ) → F.obj (tensorPow X n) ≅ tensorPow (F.obj X) n
  | 0 => (Functor.Monoidal.εIso F).symm
  | n + 1 => (Functor.Monoidal.μIso F (tensorPow X n) X).symm ≪≫
      whiskerRightIso (tensorPowMapIso F X n) (F.obj X)

variable (L : Karoubi (DegreeZero R C)) (eL : (untwisted R C).obj L ≅ tateTriple R C (-1))

/-- `K(L) ⊗ T(1) ≅ 𝟙` when `K(L) ≅ T(-1)`. -/
def untwistedTensorTateIso : (untwisted R C).obj L ⊗ tateTriple R C 1 ≅ 𝟙_ (TwistedKaroubi R C) :=
  whiskerRightIso eL (tateTriple R C 1) ≪≫ unitTwistTensorIso (-1) 1 ≪≫
    twistCongrIso (ofObj (R := R) (𝟙_ C)) (by norm_num)

/-- The Karoubi object `(X, p)` of a triple `(X, p, m)`. -/
def untwistOf (M : TwistedKaroubi R C) : Karoubi (DegreeZero R C) :=
  ⟨M.X, DegreeZero.homMk M.p M.p_mem, DegreeZero.hom_ext M.idem⟩

include eL in
/-- **Every triple is an untwisted one up to Tate twists.** If `K(L) ≅ T(-1)`, then every
`M = (X, p, m)` is isomorphic to `K((X, p) ⊗ L^{⊗ b}) ⊗ T(1)^{⊗ a}` with `m = a - b`. -/
theorem exists_iso_untwisted_tensor_tensorPow (M : TwistedKaroubi R C) :
    ∃ (A : Karoubi (DegreeZero R C)) (n : ℕ),
      Nonempty (M ≅ (untwisted R C).obj A ⊗ tensorPow (tateTriple R C 1) n) := by
  refine ⟨untwistOf M ⊗ tensorPow L (-M.twist).toNat, M.twist.toNat, ⟨?_⟩⟩
  let e₁ : (untwisted R C).obj (untwistOf M ⊗ tensorPow L (-M.twist).toNat) ≅
      { M with twist := 0 } ⊗ tateTriple R C (-1 * ((-M.twist).toNat : ℕ)) :=
    (Functor.Monoidal.μIso (untwisted R C) _ _).symm ≪≫
      whiskerLeftIso _ (tensorPowMapIso (untwisted R C) L _ ≪≫ tensorPowIso eL _ ≪≫
        tensorPowTateTripleIso (-1) _)
  let e₂ : { M with twist := 0 } ⊗ tateTriple R C (-1 * ((-M.twist).toNat : ℕ)) ≅
      { M with twist := 0 + -1 * ((-M.twist).toNat : ℕ) } :=
    tensorUnitTwistIso { M with twist := 0 } _
  let e₃ := tensorUnitTwistIso { M with twist := 0 + -1 * ((-M.twist).toNat : ℕ) }
    (1 * (M.twist.toNat : ℕ))
  exact (twistCongrIso M (by lia)).symm ≪≫ e₃.symm ≪≫ whiskerRightIso (e₂.symm ≪≫ e₁.symm) _ ≪≫
    whiskerLeftIso _ (tensorPowTateTripleIso 1 _).symm

section Symmetric

variable [SymmetricCategory C] [IsGradedBraided R C]

/-- The symmetry of `T(1) ⊗ T(1)` is the identity. -/
theorem braiding_tateTriple_one :
    (β_ (tateTriple R C 1) (tateTriple R C 1)).hom = 𝟙 _ := by
  ext
  change (𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C)
  rw [id_tensorHom_id, id_comp, braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id]

end Symmetric

end CategoryTheory.GradedCategory.TwistedKaroubi
