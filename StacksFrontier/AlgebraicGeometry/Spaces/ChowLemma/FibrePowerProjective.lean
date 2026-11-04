module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.ChartCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.FibrePowerSite

/-!
# Finite fibre powers, closed subschemes and open subschemes of H-projective schemes

A finite product over a base `S` of schemes which are H-projective over `S` is again
H-projective over `S`. The product is `Stacks.Chow.overProd`, the product taken in the slice
`Over S`; the proof peels one factor off at a time, so that the inductive step is a base change
of an H-projective morphism followed by an H-projective morphism, and both of those steps are
available — [Stacks, Tag 01WF] and [Stacks, Tag 01WE], the latter being where the Segre
embedding of [Stacks, Tag 01WD] enters.

From that: a closed subscheme of such a product is H-projective over the base, and a compact
open subscheme of a closed subscheme of it is H-quasi-projective over the base. This is the
shape in which the source of the Chow cover of [Stacks, Tag 089J] appears.

## Main definitions

* `Stacks.Chow.overProdOneIso`: a product over the base with a single factor is that factor.
* `Stacks.Chow.overProdPeelIso`: a product over the base with at least one factor is the fibre
  product of its zeroth factor with the product of the remaining ones.

## Main results

* `AlgebraicGeometry.isProjectiveMorphism_overProd_hom`: **a finite product over a base of
  H-projective schemes is H-projective over that base.**
* `AlgebraicGeometry.isProjectiveMorphism_isClosedImmersion_comp`: a closed immersion followed
  by an H-projective morphism is H-projective.
* `AlgebraicGeometry.isHQuasiProjective_quasiCompact_comp`: a quasi-compact immersion followed
  by an H-projective morphism is H-quasi-projective.
* `AlgebraicGeometry.isHQuasiProjective_of_compactSpace_comp_toSpec`: over the spectrum of a
  ring, an immersion with compact source followed by an H-projective morphism is
  H-quasi-projective.

## What is and is not proved

No declaration here carries a Stacks attribute. The product statement is not a separate lemma in
the source: it is the iterate of [Stacks, Tag 01WE] and [Stacks, Tag 01WF], which are already
carried by `AlgebraicGeometry.IsProjectiveMorphism.comp` and
`AlgebraicGeometry.IsProjectiveMorphism.baseChange`. The three composition statements are the
defining existentials of [Stacks, Tag 01W8] and of [Stacks, Tag 01VW] with one more morphism
composed in front, and those tags sit on `AlgebraicGeometry.IsProjectiveMorphism` and
`AlgebraicGeometry.IsHQuasiProjective`.

**The induction starts at one factor, not at none.** A product over `Fin 0` is the base itself,
and `IsProjectiveMorphism (𝟙 S)` would need a closed immersion `S ⟶ ℙⁿ_S` over `S`, which this
library does not have — in particular it does not have `ℙ⁰_S ≅ S`. So the base case is a single
factor, identified with that factor by `Stacks.Chow.overProdOneIso`, and the recursion peels the
zeroth factor off a product of `n + 2` factors by `Stacks.Chow.overProdPeelIso`. Both
isomorphisms are built from the universal property of the product —
`Stacks.Chow.overProdLift` and `Stacks.Chow.overProd_hom_ext` — rather than from the existing
comparison isomorphisms `Stacks.Chow.overProdFinZeroIso` and `Stacks.Chow.overProdFinSuccIso`,
because what is needed of them is their compatibility with the structure morphisms to the base,
which the universal property supplies and those two do not record.

**This file sits in the Chow directory only because of one import.** Everything in it is a
statement about schemes and is independent of [Stacks, Tag 089J]; it is placed here because
`Stacks.Chow.overProdLift`, the universal property of the finite product over the base in the
form a morphism into it is given in, lives in
`StacksFrontier/AlgebraicGeometry/Spaces/ChowLemma/FibrePowerSite.lean`.

## References

* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
* [Stacks Project, Tag 01WE](https://stacks.math.columbia.edu/tag/01WE)
* [Stacks Project, Tag 01WF](https://stacks.math.columbia.edu/tag/01WF)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

variable {S : Scheme.{u}}

/-! ### A product with a single factor -/

/-- **A product over the base with a single factor is that factor.** The morphism out of the
factor is the one whose only component is the identity. -/
def overProdOneIso {Y : Fin 1 → Scheme.{u}} (g : ∀ i, Y i ⟶ S) : Y 0 ≅ (overProd g).left where
  hom := overProdLift g (g 0) (fun i ↦ Fin.cases (𝟙 (Y 0)) (fun k ↦ k.elim0) i)
    fun i ↦ Fin.cases (Category.id_comp (g 0)) (fun k ↦ k.elim0) i
  inv := overProdπ g 0
  hom_inv_id := by
    simp only [overProdLift_comp_π]
    exact Fin.cases_zero
  inv_hom_id := by
    refine overProd_hom_ext g _ _ ?_ ?_
    · rw [Category.assoc, overProdLift_comp_hom, overProdπ_comp, Category.id_comp]
    · intro i
      refine Fin.cases ?_ (fun k ↦ k.elim0) i
      rw [Category.assoc, overProdLift_comp_π]
      simp

/-- The identification of a one-factor product with its factor is compatible with the structure
morphisms to the base. -/
theorem overProdOneIso_hom_comp_hom {Y : Fin 1 → Scheme.{u}} (g : ∀ i, Y i ⟶ S) :
    (overProdOneIso g).hom ≫ (overProd g).hom = g 0 :=
  overProdLift_comp_hom _ _ _ _

/-! ### Peeling the zeroth factor -/

variable {n : ℕ} {Y : Fin (n + 1) → Scheme.{u}}

/-- The components of the morphism from the fibre product of the zeroth factor with the product
of the remaining ones into the whole product. -/
def overProdPeelComp (g : ∀ i, Y i ⟶ S) (i : Fin (n + 1)) :
    pullback (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ⟶ Y i :=
  Fin.cases (pullback.fst (g 0) (overProd fun i : Fin n ↦ g i.succ).hom)
    (fun k ↦ pullback.snd (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ≫
      overProdπ (fun i : Fin n ↦ g i.succ) k) i

/-- The zeroth component of `Stacks.Chow.overProdPeelComp` is the first projection. -/
theorem overProdPeelComp_zero (g : ∀ i, Y i ⟶ S) :
    overProdPeelComp g 0 = pullback.fst (g 0) (overProd fun i : Fin n ↦ g i.succ).hom :=
  Fin.cases_zero

/-- A later component of `Stacks.Chow.overProdPeelComp` is the second projection followed by the
corresponding projection of the smaller product. -/
theorem overProdPeelComp_succ (g : ∀ i, Y i ⟶ S) (k : Fin n) :
    overProdPeelComp g k.succ = pullback.snd (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ≫
      overProdπ (fun i : Fin n ↦ g i.succ) k :=
  Fin.cases_succ _

/-- Every component of `Stacks.Chow.overProdPeelComp` lies over the same morphism to the base. -/
theorem overProdPeelComp_comp (g : ∀ i, Y i ⟶ S) (i : Fin (n + 1)) :
    overProdPeelComp g i ≫ g i =
      pullback.fst (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ≫ g 0 := by
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · rw [overProdPeelComp_zero]
  · rw [overProdPeelComp_succ, Category.assoc, overProdπ_comp, pullback.condition]

/-- The morphism from the fibre product of the zeroth factor with the product of the remaining
ones into the whole product. -/
def overProdPeelHom (g : ∀ i, Y i ⟶ S) :
    pullback (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ⟶ (overProd g).left :=
  overProdLift g (pullback.fst (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ≫ g 0)
    (overProdPeelComp g) (overProdPeelComp_comp g)

/-- `Stacks.Chow.overProdPeelHom` is a morphism over the base. -/
theorem overProdPeelHom_comp_hom (g : ∀ i, Y i ⟶ S) :
    overProdPeelHom g ≫ (overProd g).hom =
      pullback.fst (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ≫ g 0 :=
  overProdLift_comp_hom _ _ _ _

/-- The components of `Stacks.Chow.overProdPeelHom`. -/
theorem overProdPeelHom_comp_π (g : ∀ i, Y i ⟶ S) (i : Fin (n + 1)) :
    overProdPeelHom g ≫ overProdπ g i = overProdPeelComp g i :=
  overProdLift_comp_π _ _ _ _ _

/-- The morphism from the whole product into the fibre product of the zeroth factor with the
product of the remaining ones. -/
def overProdPeelInv (g : ∀ i, Y i ⟶ S) :
    (overProd g).left ⟶ pullback (g 0) (overProd fun i : Fin n ↦ g i.succ).hom :=
  pullback.lift (overProdπ g 0)
    (overProdLift (fun i : Fin n ↦ g i.succ) (overProd g).hom
      (fun k ↦ overProdπ g k.succ) fun k ↦ overProdπ_comp g k.succ)
    (by rw [overProdπ_comp, overProdLift_comp_hom])

/-- The first component of `Stacks.Chow.overProdPeelInv`. -/
theorem overProdPeelInv_comp_fst (g : ∀ i, Y i ⟶ S) :
    overProdPeelInv g ≫ pullback.fst (g 0) (overProd fun i : Fin n ↦ g i.succ).hom =
      overProdπ g 0 :=
  pullback.lift_fst _ _ _

/-- The second component of `Stacks.Chow.overProdPeelInv`. -/
theorem overProdPeelInv_comp_snd (g : ∀ i, Y i ⟶ S) :
    overProdPeelInv g ≫ pullback.snd (g 0) (overProd fun i : Fin n ↦ g i.succ).hom =
      overProdLift (fun i : Fin n ↦ g i.succ) (overProd g).hom
        (fun k ↦ overProdπ g k.succ) fun k ↦ overProdπ_comp g k.succ :=
  pullback.lift_snd _ _ _

/-- **A finite product over the base with at least one factor is the fibre product of its
zeroth factor with the product of the remaining ones.** Both directions come from the universal
properties of the two limits, so the isomorphism carries its compatibility with the structure
morphisms to the base, which is `Stacks.Chow.overProdPeelIso_hom_comp_hom`. -/
def overProdPeelIso (g : ∀ i, Y i ⟶ S) :
    pullback (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ≅ (overProd g).left where
  hom := overProdPeelHom g
  inv := overProdPeelInv g
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, overProdPeelInv_comp_fst, overProdPeelHom_comp_π,
        overProdPeelComp_zero, Category.id_comp]
    · rw [Category.assoc, overProdPeelInv_comp_snd, Category.id_comp]
      refine overProd_hom_ext _ _ _ ?_ ?_
      · rw [Category.assoc, overProdLift_comp_hom, overProdPeelHom_comp_hom, pullback.condition]
      · intro k
        rw [Category.assoc, overProdLift_comp_π, overProdPeelHom_comp_π, overProdPeelComp_succ]
  inv_hom_id := by
    refine overProd_hom_ext _ _ _ ?_ ?_
    · rw [Category.id_comp, Category.assoc, overProdPeelHom_comp_hom, ← Category.assoc,
        overProdPeelInv_comp_fst, overProdπ_comp]
    · intro i
      rw [Category.id_comp, Category.assoc, overProdPeelHom_comp_π]
      refine Fin.cases ?_ (fun k ↦ ?_) i
      · rw [overProdPeelComp_zero, overProdPeelInv_comp_fst]
      · rw [overProdPeelComp_succ, ← Category.assoc, overProdPeelInv_comp_snd, overProdLift_comp_π]

/-- The identification of a product with the fibre product of its zeroth factor and the product
of the remaining ones is compatible with the structure morphisms to the base. -/
theorem overProdPeelIso_hom_comp_hom (g : ∀ i, Y i ⟶ S) :
    (overProdPeelIso g).hom ≫ (overProd g).hom =
      pullback.fst (g 0) (overProd fun i : Fin n ↦ g i.succ).hom ≫ g 0 :=
  overProdPeelHom_comp_hom g

end Stacks.Chow

namespace AlgebraicGeometry

/-- **A finite product over a base of H-projective schemes is H-projective over that base.**

The induction peels the zeroth factor: a product of `n + 2` factors is the fibre product of the
zeroth factor with the product of the other `n + 1`, by `Stacks.Chow.overProdPeelIso`, and under
that identification its structure morphism becomes the base change of the zeroth factor along
the structure morphism of the smaller product, followed by that structure morphism. The first of
those is H-projective by [Stacks, Tag 01WF] and the second by the inductive hypothesis, so the
composite is H-projective by [Stacks, Tag 01WE] — which is where the Segre embedding is used.

The base case is a single factor, not none; see the implementation notes of this file. -/
theorem isProjectiveMorphism_overProd_hom {S : Scheme.{u}} :
    ∀ (n : ℕ) {Y : Fin (n + 1) → Scheme.{u}} (g : ∀ i, Y i ⟶ S),
      (∀ i, IsProjectiveMorphism (g i)) → IsProjectiveMorphism (Stacks.Chow.overProd g).hom
  | 0, _, g, hg =>
      IsProjectiveMorphism.of_iso (Stacks.Chow.overProdOneIso g) (Iso.refl S)
        (by rw [Stacks.Chow.overProdOneIso_hom_comp_hom, Iso.refl_hom, Category.comp_id]) (hg 0)
  | m + 1, _, g, hg => by
      refine IsProjectiveMorphism.of_iso (Stacks.Chow.overProdPeelIso g) (Iso.refl S)
        (by rw [Stacks.Chow.overProdPeelIso_hom_comp_hom, Iso.refl_hom, Category.comp_id]) ?_
      rw [pullback.condition]
      exact ((hg 0).baseChange _).comp
        (isProjectiveMorphism_overProd_hom m (fun i : Fin (m + 1) ↦ g i.succ) fun i ↦ hg i.succ)

variable {X Z S : Scheme.{u}}

/-- **A closed immersion followed by an H-projective morphism is H-projective.** The closed
immersion into `ℙⁿ_S` over `S` witnessing H-projectivity of the second morphism is precomposed
with the given one.

In particular a closed subscheme of a scheme H-projective over `S` is H-projective over `S`. -/
theorem isProjectiveMorphism_isClosedImmersion_comp (i : X ⟶ Z) (q : Z ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion i] (hq : IsProjectiveMorphism q) :
    IsProjectiveMorphism (i ≫ q) := by
  obtain ⟨m, k, hk, hkq⟩ := hq
  have := hk
  exact ⟨m, i ≫ k, inferInstance, by rw [Category.assoc, hkq]⟩

/-- **A quasi-compact immersion followed by an H-projective morphism is H-quasi-projective.**
The closed immersion into `ℙⁿ_S` over `S` witnessing H-projectivity of the second morphism is
precomposed with the given immersion; the composite is an immersion, and is quasi-compact
because a closed immersion is. -/
theorem isHQuasiProjective_quasiCompact_comp (i : X ⟶ Z) (q : Z ⟶ S)
    [AlgebraicGeometry.IsImmersion i] [QuasiCompact i] (hq : IsProjectiveMorphism q) :
    IsHQuasiProjective (i ≫ q) := by
  obtain ⟨m, k, hk, hkq⟩ := hq
  have := hk
  exact ⟨m, i ≫ k, inferInstance, inferInstance, by rw [Category.assoc, hkq]⟩

/-- **Over the spectrum of a ring, an immersion with compact source followed by an H-projective
morphism is H-quasi-projective.** The immersion into `ℙⁿ_{Spec R}` is quasi-compact because its
source is a compact space and projective space over a ring is a quasi-separated space; that is
the only reason the base is written as a spectrum rather than as an arbitrary scheme.

In particular a compact open subscheme of a closed subscheme of a finite product over `Spec R`
of schemes H-projective over `Spec R` is H-quasi-projective over `Spec R`. -/
theorem isHQuasiProjective_of_compactSpace_comp_toSpec {R : CommRingCat.{u}} (i : X ⟶ Z)
    (q : Z ⟶ Spec R) [AlgebraicGeometry.IsImmersion i] [CompactSpace X]
    (hq : IsProjectiveMorphism q) : IsHQuasiProjective (i ≫ q) := by
  obtain ⟨m, k, hk, hkq⟩ := hq
  have := hk
  have hqs : QuasiSeparatedSpace (projectiveSpaceOver m (Spec R)) :=
    Stacks.ProjectiveCohomology.quasiSeparatedSpace_projectiveSpaceOverRing m R
  exact ⟨m, i ≫ k, inferInstance, quasiCompact_of_compactSpace _, by rw [Category.assoc, hkq]⟩

end AlgebraicGeometry

end
