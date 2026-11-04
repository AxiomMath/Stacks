module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Cohomology commutes with direct sums, and the subcategories it cuts out

Let `A` be an abelian category in which the direct sum functor
`colim : (Discrete J ⥤ A) ⥤ A` is exact — Grothendieck's axiom AB4 for the index type `J`,
which a Grothendieck abelian category satisfies for every `J` in its own universe. Then the
degree-`n` cohomology of a direct sum of cochain complexes is the direct sum of the cohomologies,
and the same holds for the cohomology functors of the derived category `D(A)`, direct sums there
being computed by termwise direct sums of complexes.

The consequence this file is built for: if an object property `B` on `A` is closed under
`J`-indexed direct sums, then the full subcategory `D_B(A) ⊆ D(A)` of complexes all of whose
cohomology objects satisfy `B` is closed under `J`-indexed direct sums, and therefore has them.
With `B` the quasi-coherent sheaves on a scheme this is the direct-sum half of
[Stacks, Tag 08DT], the hypothesis Brown representability needs in the proof of
[Stacks, Tag 0A9E].

## Main results

* `Stacks.Duality.isoCoproductHomologyCochainComplex` — `Hⁿ(⨁ⱼ Kⱼ) ≅ ⨁ⱼ Hⁿ(Kⱼ)` for cochain
  complexes.
* `Stacks.Duality.isoCoproductHomologyDerived` — the same for the cohomology functors of `D(A)`.
* `Stacks.Duality.derivedCategoryB_prop_coproduct` and
  `Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts` — `D_B(A)` is closed under
  `J`-indexed direct sums when `B` is.

## Implementation notes

The analytic content is that `colim : (Discrete J ⥤ A) ⥤ A` is exact, hence preserves homology,
so that `ShortComplex.mapHomologyIso` applies to it. Transporting that statement from a short
complex of `Discrete J`-diagrams to a `Discrete J`-diagram of short complexes is done through
`CategoryTheory.ShortComplex.functorEquivalence`, and the comparison of the two readings of the
degreewise cohomology is `ShortComplex.mapHomologyIso` for the evaluation functors, which are
exact as well.

Only an *isomorphism* is produced, not a `PreservesColimitsOfShape` instance: identifying the
cocone legs as well would be needed for that, and the consumers below ask for no more than the
isomorphism, every property of objects in sight being closed under isomorphism. The repository
already has the leg-compatible statement for a countable index type, in
`StacksFrontier/Algebra/Homology/DerivedCategory/Coproducts.lean`, and a version for an arbitrary
index type that is not exported; the index type needed for Brown representability is the morphism
universe of the derived category, which is not countable.

## References

* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 0A5L](https://stacks.math.columbia.edu/tag/0A5L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

attribute [local instance] Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

universe w' w v u

namespace Stacks.Duality

variable {A : Type u} [Category.{v} A] [Abelian A]

/-! ### Direct sums of short complexes -/

section

variable {J : Type w} [HasCoproductsOfShape J A] (K : Discrete J ⥤ ShortComplex A)

/-- The short complex of componentwise direct sums of a family of short complexes, written as the
image of the family under the direct-sum functor `colim : (Discrete J ⥤ A) ⥤ A`. -/
abbrev coprodShortComplex : ShortComplex A :=
  (colim (J := Discrete J) (C := A)).mapShortComplex.obj
    ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K)

/-- `coprodShortComplex K`, with the componentwise canonical injections, is a cocone over `K`. -/
def coprodShortComplexCofan : Cocone K where
  pt := coprodShortComplex K
  ι :=
    { app := fun j => ShortComplex.homMk (colimit.ι (K ⋙ ShortComplex.π₁) j)
        (colimit.ι (K ⋙ ShortComplex.π₂) j) (colimit.ι (K ⋙ ShortComplex.π₃) j)
        (ι_colimMap _ _) (ι_colimMap _ _)
      naturality := by
        rintro ⟨i⟩ ⟨j⟩ f
        obtain rfl : i = j := Discrete.eq_of_hom f
        obtain rfl : f = 𝟙 _ := by subsingleton
        ext <;> simp }

/-- **Direct sums of short complexes are computed componentwise.** -/
def coprodShortComplexIsColimit : IsColimit (coprodShortComplexCofan K) := by
  refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₁)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by
        intro j
        simp only [coprodShortComplexCofan, ShortComplex.homMk, Functor.const_obj_obj]
        exact Category.comp_id _))
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₂)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by
        intro j
        simp only [coprodShortComplexCofan, ShortComplex.homMk, Functor.const_obj_obj]
        exact Category.comp_id _))
  · exact (colimit.isColimit (K ⋙ ShortComplex.π₃)).ofIsoColimit
      (Cocone.ext (Iso.refl _) (by
        intro j
        simp only [coprodShortComplexCofan, ShortComplex.homMk, Functor.const_obj_obj]
        exact Category.comp_id _))

variable [(colim (J := Discrete J) (C := A)).PreservesHomology]

/-- The homology of a short complex of `Discrete J`-diagrams, evaluated at `j`, is the homology of
the short complex obtained by evaluating at `j`: the evaluation functors are exact. -/
def homologyEvalIso (j : Discrete J) :
    (((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K).homology).obj j ≅
      (K.obj j).homology :=
  (((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K).mapHomologyIso
      ((evaluation (Discrete J) A).obj j)).symm ≪≫
    (ShortComplex.homologyFunctor A).mapIso
      (((ShortComplex.FunctorEquivalence.counitIso (Discrete J) A).app K).app j)

/-- **Homology commutes with direct sums of short complexes.** The homology of the componentwise
direct sum of a family of short complexes is the direct sum of their homologies, because the
direct-sum functor is exact and therefore preserves homology. -/
def homologyCoprodShortComplexIso :
    (coprodShortComplex K).homology ≅ colimit (K ⋙ ShortComplex.homologyFunctor A) :=
  ((ShortComplex.functorEquivalence (Discrete J) A).inverse.obj K).mapHomologyIso
      (colim (J := Discrete J) (C := A)) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso (homologyEvalIso K))

end

/-! ### Direct sums of cochain complexes -/

section

variable (A)
variable {J : Type w} [HasCoproductsOfShape J A]

omit [Abelian A] in
/-- The degree-`n` short complex of a cochain complex commutes with direct sums: direct sums of
complexes are computed degreewise, and direct sums of short complexes componentwise. -/
theorem preservesColimitsOfShape_shortComplexFunctor [HasZeroMorphisms A] (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n) :=
  ⟨fun {D} => by
    have h := fun i => isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) i)
      (colimit.isColimit D)
    exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D)
      (ShortComplex.isColimitOfIsColimitπ _ (h _) (h _) (h _))⟩

variable [(colim (J := Discrete J) (C := A)).PreservesHomology]

/-- **Cohomology commutes with direct sums of cochain complexes** — Grothendieck's axiom AB4 in
the form `Hⁿ(⨁ⱼ Kⱼ) ≅ ⨁ⱼ Hⁿ(Kⱼ)`. -/
def isoCoproductHomologyCochainComplex (C : J → CochainComplex A ℤ) (n : ℤ) :
    (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).obj (∐ C) ≅
      ∐ fun j => (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n).obj (C j) :=
  letI _ := preservesColimitsOfShape_shortComplexFunctor A (J := J) n
  (ShortComplex.homologyFunctor A).mapIso
      ((isColimitOfPreserves (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n)
        (colimit.isColimit (Discrete.functor C))).coconePointUniqueUpToIso
          (coprodShortComplexIsColimit _)) ≪≫
    homologyCoprodShortComplexIso _ ≪≫ HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)

end

/-! ### Direct sums in the derived category -/

section

variable (A)
variable [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w'} A] {J : Type w}

/-- **Cohomology on the derived category commutes with direct sums.** Direct sums in `D(A)` are
computed by termwise direct sums of complexes, because the localization `Q : C(A) ⥤ D(A)`
preserves them, and cohomology of a termwise direct sum is the direct sum of the cohomologies. -/
def isoCoproductHomologyDerived (K : J → DerivedCategory A) (n : ℤ) :
    (DerivedCategory.homologyFunctor A n).obj (∐ K) ≅
      ∐ fun j => (DerivedCategory.homologyFunctor A n).obj (K j) :=
  letI _ := Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts A J
  let C : J → CochainComplex A ℤ := fun j => DerivedCategory.Q.objPreimage (K j)
  (DerivedCategory.homologyFunctor A n).mapIso
      ((HasColimit.isoOfNatIso (Discrete.natIso fun j =>
          DerivedCategory.Q.objObjPreimageIso (K j.as))).symm ≪≫
        (HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)).symm ≪≫
        (preservesColimitIso DerivedCategory.Q (Discrete.functor C)).symm) ≪≫
    (DerivedCategory.homologyFunctorFactors A n).app (∐ C) ≪≫
    isoCoproductHomologyCochainComplex A C n ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso fun j =>
      ((DerivedCategory.homologyFunctorFactors A n).app (C j.as)).symm ≪≫
        (DerivedCategory.homologyFunctor A n).mapIso
          (DerivedCategory.Q.objObjPreimageIso (K j.as)))

end

/-! ### The subcategory cut out by a property of the cohomology objects -/

section

variable (A)
variable [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w'} A] {J : Type w}
  (B : ObjectProperty A) (hB : WeakSerre.IsWeakSerre B)
  (hsum : ∀ M : J → A, (∀ j, B (M j)) → B (∐ M))

include hB hsum in
/-- **A direct sum of complexes with cohomology in `B` has cohomology in `B`**, as soon as `B` is
closed under direct sums. -/
theorem derivedCategoryB_prop_coproduct (K : J → DerivedCategory A)
    (hK : ∀ j, DerivedCategoryB.derivedCategoryB B (K j)) :
    DerivedCategoryB.derivedCategoryB B (∐ K) := fun n =>
  hB.isClosedUnderIsomorphisms.of_iso (isoCoproductHomologyDerived A K n).symm
    (hsum _ fun j => hK j n)

include hB hsum in
/-- **`D_B(A)` is closed under direct sums** when `B` is. This is the abstract form of the
direct-sum half of [Stacks, Tag 08DT]. -/
theorem derivedCategoryB_isClosedUnderCoproducts :
    (DerivedCategoryB.derivedCategoryB (A := A) B).IsClosedUnderColimitsOfShape (Discrete J) := by
  have : (DerivedCategoryB.derivedCategoryB (A := A) B).IsClosedUnderIsomorphisms :=
    DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms B hB
  refine IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  exact (DerivedCategoryB.derivedCategoryB B).prop_of_iso
    (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))).symm
    (derivedCategoryB_prop_coproduct A B hB hsum _ fun j => hF ⟨j⟩)

end

end Stacks.Duality

end
