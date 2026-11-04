module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.RestrictionGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects

/-!
# Restriction of a perfect object to a slice, at independent universes

Let `(C, O)` be a ringed site and `V` an object of `C`.  The restriction to the localized ringed
site `(C/V, O|_V)` of a perfect complex of `O`-modules (Stacks 08G5) is a perfect complex, and so
the restriction of a perfect object of `D(O)` is a perfect object of `D(O|_V)`.  The objects and
the morphisms of `C` and the sections of `O` live in three independent universes, so the
statements apply to the small étale site of an algebraic space.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfectComplex_restrictComplex_general`: the restriction of a
  perfect complex to a slice is perfect.
* `AlgebraicGeometry.RingedSite.isPerfect_derivedRestriction_general`: the restriction of a
  perfect object of `D(O)` to a slice is perfect.

## Implementation notes

The proof is the one of
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_restrictComplex_general`, with the
quasi-isomorphism of the strictly perfect local model transported along the equivalence of
Stacks 04IX between the slice of a slice and a slice, `Stacks.SheafOfModules.sliceEquiv`, which
is exact and so preserves quasi-isomorphisms.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d d'

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective
attribute [local instance] iterHasSheafify iterWEq iterHasSheafifyAll iterWEqAll
attribute [local instance] overMapLimits overMapColimits ovFunctorLimits ovFunctorColimits

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The restriction of a perfect complex to a slice is perfect**, at independent universes. -/
theorem isPerfectComplex_restrictComplex_general
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : X.IsPerfectComplex K) (V : X.C) :
    (X.over V).IsPerfectComplex (X.restrictComplex K V) := by
  intro Z
  obtain ⟨S₁, hS₁, hdata⟩ := hK Z.left
  refine ⟨Presieve.functorPullback (Over.forget V) S₁, ?_, ?_⟩
  · have hmem : (Sieve.overEquiv Z).symm (Sieve.generate S₁) ∈ (X.J.over V) Z := by
      rw [X.J.mem_over_iff]
      simpa using hS₁
    rw [show Sieve.generate (Presieve.functorPullback (Over.forget V) S₁) =
      (Sieve.overEquiv Z).symm (Sieve.generate S₁) from
        (Sieve.overEquiv_symm_generate S₁).symm]
    exact hmem
  · intro W f hf
    obtain ⟨P, hP, α, hα⟩ := hdata (Over.Hom.left f) hf
    let Fe := (Stacks.SheafOfModules.sliceEquiv
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W).functor
    let Fec := Fe.mapHomologicalComplex (ComplexShape.up ℤ)
    let e : Fec.obj (X.restrictComplex K W.left) ≅
        (X.over V).restrictComplex (X.restrictComplex K V) W :=
      Fec.mapIso
          ((Stacks.SheafOfModules.overFunctorMapComplexIso.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.hom).app K).symm ≪≫
        (Stacks.SheafOfModules.sliceEquivOverFunctorComplexIsoGeneral
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W).app
          (X.restrictComplex K V)
    have : PreservesFiniteLimits Fe := inferInstance
    have : PreservesFiniteColimits Fe := inferInstance
    have : Fe.PreservesHomology := Functor.preservesHomologyOfExact Fe
    have h1 : QuasiIso ((Fe.mapHomologicalComplex (ComplexShape.up ℤ)).map α) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology α Fe
    have h4 : IsIso e.hom := Iso.isIso_hom e
    have h3 : QuasiIso e.hom := quasiIso_of_isIso e.hom
    have h2 : QuasiIso ((Fe.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ e.hom) :=
      quasiIso_comp _ _
    exact ⟨Fec.obj P,
      Stacks.SheafOfModules.isStrictlyPerfect_sliceEquiv_general
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W hP,
      Fec.map α ≫ e.hom, h2⟩

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hRestrDer : ∀ U : X.C,
  HasDerivedCategory.{d'}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory ovHasDerived

/-- **The restriction of a perfect object of `D(O)` to a slice is perfect**, at independent
universes. -/
theorem isPerfect_derivedRestriction_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPerfect E) (V : X.C) :
    (X.over V).IsPerfect
      ((SheafOfModules.overFunctor.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj E) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  refine ⟨X.restrictComplex K V, isPerfectComplex_restrictComplex_general X K hK V, ⟨?_⟩⟩
  exact ((SheafOfModules.overFunctor.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.app K).symm ≪≫
    (SheafOfModules.overFunctor.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.mapIso eK

end AlgebraicGeometry.RingedSite
