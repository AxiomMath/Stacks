module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreQuotientDerivedPullbackAdjunction
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedQuasicoherentCohomology

/-!
# Cohomology functors on a Verdier quotient by a weak Serre part

Let `A` be an abelian category, `𝒜`, `𝒮` weak Serre subcategories of `A`, `D_𝒜(A)` the full
subcategory of `D(A)` of complexes with cohomology in `𝒜`, and `D_𝒜(A)/D_𝒮(A)` its Verdier
quotient (`DerivedCategoryB.serreQuotientW`).  Let `Φ : 𝒜 ⥤ B` be an exact functor to an
abelian category which kills the objects of `𝒜` lying in `𝒮`.  Then `Φ ∘ Hⁿ`, the composite of
the `n`-th cohomology `D_𝒜(A) ⥤ 𝒜` with `Φ`, is homological and kills `D_𝒮(A)`, so it factors
through the quotient, by the universal property of the Verdier quotient for homological functors
(**Stacks 05RJ**).

This is the formal content of **Stacks 07B7**: for an algebraic stack `𝒳`, `A = Mod(𝒪_𝒳)`,
`𝒜 = LQCoh^fbc(𝒪_𝒳)`, `𝒮 = Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` and `Φ = Q` the coherator of
**Stacks 0778**, exact and killing the parasitic modules by **Stacks 0779**.

## Main definitions

* `DerivedCategoryB.derivedCategoryBHomology`: `Hⁿ : D_𝒜(A) ⥤ 𝒜`.
* `DerivedCategoryB.serreQuotientCohomology`: the descended functor
  `Hⁿ : D_𝒜(A)/D_𝒮(A) ⥤ B` on `(serreQuotientW 𝒜 𝒮).Localization`, and
  `DerivedCategoryB.serreQuotientCohomologyFac`, its defining identity.
* `DerivedCategoryB.serreQuotientCohomologyOfTrW`: the same functor on the localization at the
  class attached to the triangulated subcategory `D_𝒮(A)`, which carries the triangulated
  structure of the Verdier quotient.

## Main results

* `DerivedCategoryB.isHomological_derivedCategoryBHomology_comp`: `Φ ∘ Hⁿ` is homological.
* `DerivedCategoryB.serreQuotientCohomology_uniq`: the descended functor is unique up to a unique
  isomorphism compatible with its defining identity.
* `DerivedCategoryB.isHomological_serreQuotientCohomologyOfTrW`: the descended functor is
  homological (the "cohomological functor" of **Stacks 07B7**).

## References

* [Stacks Project, Tag 05RJ](https://stacks.math.columbia.edu/tag/05RJ)
* [Stacks Project, Tag 07B7](https://stacks.math.columbia.edu/tag/07B7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ w₁ v₂ u₂

namespace DerivedCategoryB

open DerivedCategory ObjectProperty

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  (𝒜 𝒮 : ObjectProperty A)

/-- **`Hⁿ : D_𝒜(A) ⥤ 𝒜`**, the `n`-th cohomology object of a complex whose cohomology lies in
`𝒜`, as an object of `𝒜`. -/
def derivedCategoryBHomology (n : ℤ) :
    (derivedCategoryB 𝒜).FullSubcategory ⥤ 𝒜.FullSubcategory :=
  𝒜.lift ((derivedCategoryB 𝒜).ι ⋙ homologyFunctor A n) fun K => K.2 n

/-- `Hⁿ : D_𝒜(A) ⥤ 𝒜` followed by the inclusion is the `n`-th cohomology of `D(A)`. -/
def derivedCategoryBHomologyCompιIso (n : ℤ) :
    derivedCategoryBHomology 𝒜 n ⋙ 𝒜.ι ≅ (derivedCategoryB 𝒜).ι ⋙ homologyFunctor A n :=
  Iso.refl _

/-- `Hⁿ : D_𝒜(A) ⥤ 𝒜` preserves zero morphisms. -/
instance preservesZeroMorphisms_derivedCategoryBHomology (n : ℤ) :
    (derivedCategoryBHomology 𝒜 n).PreservesZeroMorphisms :=
  ⟨fun X Y => InducedCategory.hom_ext (Functor.map_zero (homologyFunctor A n) X.obj Y.obj)⟩

variable [𝒜.IsWeakSerreClass] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  (Φ : 𝒜.FullSubcategory ⥤ B) [Φ.PreservesZeroMorphisms] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ]

/-- **`Φ ∘ Hⁿ` is homological** for an exact `Φ`: a distinguished triangle of `D_𝒜(A)` is one
of `D(A)`, its cohomology sequence is exact in `A` and hence in `𝒜`, whose inclusion is exact and
faithful, and `Φ` preserves exactness. -/
instance isHomological_derivedCategoryBHomology_comp (n : ℤ) :
    (derivedCategoryBHomology 𝒜 n ⋙ Φ).IsHomological where
  exact T hT := by
    have : PreservesFiniteLimits 𝒜.ι := 𝒜.preservesFiniteLimits_ι_of_isWeakSerreClass
    have : PreservesFiniteColimits 𝒜.ι := 𝒜.preservesFiniteColimits_ι_of_isWeakSerreClass
    have h₁ : ((shortComplexOfDistTriangle T hT).map
        ((derivedCategoryB 𝒜).ι ⋙ homologyFunctor A n)).Exact :=
      ((derivedCategoryB 𝒜).ι ⋙ homologyFunctor A n).map_distinguished_exact T hT
    have h₂ : ((shortComplexOfDistTriangle T hT).map (derivedCategoryBHomology 𝒜 n)).Exact :=
      (ShortComplex.exact_map_iff_of_faithful
        ((shortComplexOfDistTriangle T hT).map (derivedCategoryBHomology 𝒜 n)) 𝒜.ι).1 h₁
    exact h₂.map Φ

variable (hΦ : ∀ M : 𝒜.FullSubcategory, 𝒮 M.obj → IsZero (Φ.obj M))

omit [Abelian B] [Φ.PreservesZeroMorphisms] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
include hΦ in
/-- `Φ ∘ Hⁿ` kills `D_𝒮(A)`, read inside `D_𝒜(A)`: every shift of an object of `D_𝒮(A)` has its
cohomology in `𝒮`. -/
theorem serreQuotientKernel_le_homologicalKernel [𝒮.IsWeakSerreClass] (n : ℤ) :
    serreQuotientKernel 𝒜 𝒮 ≤ (derivedCategoryBHomology 𝒜 n ⋙ Φ).homologicalKernel := by
  intro X hX k
  exact hΦ _ (((serreQuotientKernel 𝒜 𝒮).le_shift k X hX) n)

variable [𝒮.IsWeakSerreClass]

include hΦ in
/-- **`Φ ∘ Hⁿ` inverts the morphisms the Verdier quotient inverts.** -/
theorem isInvertedBy_derivedCategoryBHomology_comp (n : ℤ) :
    (serreQuotientW 𝒜 𝒮).IsInvertedBy (derivedCategoryBHomology 𝒜 n ⋙ Φ) := by
  rw [serreQuotientW_eq_trW]
  obtain ⟨H, fac, -, -⟩ := VerdierQuotientUniversalProperty.homological_universal_property
    (serreQuotientKernel 𝒜 𝒮) (derivedCategoryBHomology 𝒜 n ⋙ Φ)
    (serreQuotientKernel_le_homologicalKernel 𝒜 𝒮 Φ hΦ n)
  refine (MorphismProperty.IsInvertedBy.iff_of_iso _ fac).mp (fun X Y f hf => ?_)
  have : IsIso ((serreQuotientKernel 𝒜 𝒮).trW.Q.map f) := Localization.inverts _ _ f hf
  change IsIso (H.map ((serreQuotientKernel 𝒜 𝒮).trW.Q.map f))
  infer_instance

/-- **The cohomology functor `Hⁿ : D_𝒜(A)/D_𝒮(A) ⥤ B`** (the shape of **Stacks 07B7**): the
descent of `Φ ∘ Hⁿ` through the quotient functor. -/
def serreQuotientCohomology (n : ℤ) : (serreQuotientW 𝒜 𝒮).Localization ⥤ B :=
  Localization.lift (derivedCategoryBHomology 𝒜 n ⋙ Φ)
    (isInvertedBy_derivedCategoryBHomology_comp 𝒜 𝒮 Φ hΦ n) (serreQuotientW 𝒜 𝒮).Q

/-- **The defining identity of the cohomology functor**: composed with the quotient functor it is
`Φ ∘ Hⁿ`. -/
def serreQuotientCohomologyFac (n : ℤ) :
    (serreQuotientW 𝒜 𝒮).Q ⋙ serreQuotientCohomology 𝒜 𝒮 Φ hΦ n ≅
      derivedCategoryBHomology 𝒜 n ⋙ Φ :=
  Localization.fac _ _ _

/-- **The cohomology functor is unique** up to a unique isomorphism compatible with its defining
identity. -/
theorem serreQuotientCohomology_uniq (n : ℤ) (G : (serreQuotientW 𝒜 𝒮).Localization ⥤ B)
    (α : (serreQuotientW 𝒜 𝒮).Q ⋙ G ≅ derivedCategoryBHomology 𝒜 n ⋙ Φ) :
    ∃! e : G ≅ serreQuotientCohomology 𝒜 𝒮 Φ hΦ n,
      Functor.whiskerLeft (serreQuotientW 𝒜 𝒮).Q e.hom ≫
        (serreQuotientCohomologyFac 𝒜 𝒮 Φ hΦ n).hom = α.hom :=
  Localization.existsUnique_isoLift _ _ _ _ G α

/-- The cohomology functor on the localization of `D_𝒜(A)` at the class attached to the
triangulated subcategory `D_𝒮(A)`, the model of the Verdier quotient carrying its triangulated
structure. -/
def serreQuotientCohomologyOfTrW (n : ℤ) : (serreQuotientKernel 𝒜 𝒮).trW.Localization ⥤ B :=
  Localization.lift (derivedCategoryBHomology 𝒜 n ⋙ Φ)
    (serreQuotientW_eq_trW 𝒜 𝒮 ▸ isInvertedBy_derivedCategoryBHomology_comp 𝒜 𝒮 Φ hΦ n)
    (serreQuotientKernel 𝒜 𝒮).trW.Q

/-- The defining identity of `DerivedCategoryB.serreQuotientCohomologyOfTrW`. -/
def serreQuotientCohomologyOfTrWFac (n : ℤ) :
    (serreQuotientKernel 𝒜 𝒮).trW.Q ⋙ serreQuotientCohomologyOfTrW 𝒜 𝒮 Φ hΦ n ≅
      derivedCategoryBHomology 𝒜 n ⋙ Φ :=
  Localization.fac _ _ _

/-- **The cohomology functor is homological** (the "cohomological functor" of **Stacks 07B7**):
the functor produced by the universal property **Stacks 05RJ** is homological, and the
cohomology functor is isomorphic to it. -/
instance isHomological_serreQuotientCohomologyOfTrW (n : ℤ) :
    (serreQuotientCohomologyOfTrW 𝒜 𝒮 Φ hΦ n).IsHomological := by
  obtain ⟨H, fac, hH, huniq⟩ := VerdierQuotientUniversalProperty.homological_universal_property
    (serreQuotientKernel 𝒜 𝒮) (derivedCategoryBHomology 𝒜 n ⋙ Φ)
    (serreQuotientKernel_le_homologicalKernel 𝒜 𝒮 Φ hΦ n)
  obtain ⟨e, -, -⟩ := huniq _ (serreQuotientCohomologyOfTrWFac 𝒜 𝒮 Φ hΦ n)
  exact Functor.IsHomological.of_iso e.symm

end DerivedCategoryB
