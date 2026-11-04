module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.IteratedSliceFiniteFreeSummands
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence restricts to a slice of the site

Let `(C, O)` be a ringed site, let `E` be an object of `D(O)` and let `V` be an object of `C`.
If `E` is `m`-pseudo-coherent then so is its restriction `E|_V` on the localized ringed site
`(C/V, O|_V)`. This is the direction of Stacks 08FU, part (3) which
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally` does not cover: that result
assembles pseudo-coherence from local data, this one takes it apart.

## Main definitions

* `Stacks.SheafOfModules.sliceEquivOverFunctorComplexIso`: the degreewise form, on cochain
  complexes, of `Stacks.SheafOfModules.sliceEquivOverMapFunctorIso`.

## Main results

* `Stacks.SheafOfModules.isStrictlyPerfect_sliceEquiv`: transport to an iterated slice carries
  a strictly perfect complex to a strictly perfect complex.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_restrictComplex`: the restriction of
  an `m`-pseudo-coherent complex to a slice is `m`-pseudo-coherent there.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction`: **Stacks 08FU, part
  (3)**, in the direction which restricts pseudo-coherence to a slice.

## Implementation notes

Both the hypothesis and the conclusion are statements about every object of the respective site,
and the two quantifications are matched as follows. A strictly perfect approximation is a
property of the *source* of an arrow, so a covering of an object `Z` of `C/V` may be taken to be
a covering of `Z.left` in `C` pulled back along `Over.forget V`; `CategoryTheory.Sieve.overEquiv`
and `CategoryTheory.GrothendieckTopology.mem_over_iff` say that this is again covering, and
`CategoryTheory.Sieve.overEquiv_symm_generate` says that pulling back commutes with generating a
sieve from a presieve.

The approximation the hypothesis supplies over an arrow `W ⟶ Z` of `C/V` lives on the slice
`C/W.left`, whereas `m`-pseudo-coherence on `C/V` asks for one on the *iterated* slice
`(C/V)/W`. The passage is `Stacks.SheafOfModules.sliceEquiv`, the equivalence of the two
categories of sheaves of modules; it carries strict perfectness along by
`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex`, being exact and matching up the
two structure sheaves, and it carries the approximation itself along once the two readings of
the restriction of the ambient complex are identified. That identification is
`Stacks.SheafOfModules.sliceEquivOverMapFunctorIso` composed with
`SheafOfModules.overFunctorMap`, taken degreewise.

The sheafification data of the iterated slices is a hypothesis rather than a derivation, as in
`Stacks.SheafOfModules.exists_coveringSieve_isDirectSummandOfFiniteFree_overMap`: the results
which supply it, such as `Stacks.SheafOfModules.iteratedSliceHasSheafify`, are stated at an
unconstrained universe for the target category and cannot be registered as instances at the
universe of the sections.

## References

* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v d

namespace Stacks.SheafOfModules

section SliceForward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{0}) (U : C) (V : Over U)

/-- Transport of sheaves of modules to an iterated slice is additive: it is an equivalence, so
it preserves binary products. -/
instance sliceEquivFunctorAdditive : ((sliceEquiv R U V).functor).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The degreewise form of `Stacks.SheafOfModules.sliceEquivOverMapFunctorIso`.** Restricting
a complex of `O|_U`-modules along the structure arrow of `V` and transporting it to the iterated
slice over `V` is restricting it to that iterated slice. -/
def sliceEquivOverFunctorComplexIso :
    (SheafOfModules.overMap.{0} R V.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((sliceEquiv R U V).functor).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (SheafOfModules.overFunctor.{0} (R.over U) V).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (sliceEquivOverMapFunctorIso R U V) (ComplexShape.up ℤ)

variable [HasSheafify (J.over V.left) AddCommGrpCat.{0}]
  [(J.over V.left).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasSheafify ((J.over U).over V) AddCommGrpCat.{0}]
  [((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- **Transport to an iterated slice carries a strictly perfect complex to a strictly perfect
complex.** The transport is an equivalence, hence exact, and it matches up the two structure
sheaves by `Stacks.SheafOfModules.sliceEquivUnitIso`. -/
theorem isStrictlyPerfect_sliceEquiv
    {P : CochainComplex (SheafOfModules.{0} (R.over V.left)) ℤ}
    (hP : IsStrictlyPerfect (R.over V.left) P) :
    IsStrictlyPerfect ((R.over U).over V)
      ((((sliceEquiv R U V).functor).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have : PreservesFiniteColimits ((sliceEquiv R U V).functor) := inferInstance
  isStrictlyPerfect_mapHomologicalComplex _ (sliceEquivUnitIso R U V).symm hP

end SliceForward

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

section Restriction

variable (X : RingedSite.{u, v, 0})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ (U : X.C) (W : Over U), HasSheafify ((X.J.over U).over W) AddCommGrpCat.{0}]
variable [∀ (U : X.C) (W : Over U),
  ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

/-- Sheafification of abelian-group presheaves exists for the topology on a slice of the slice
site `X.over U`. -/
local instance restrOvHasSheafifyIter (U : X.C) (W : (X.over U).C) :
    HasSheafify ((X.over U).J.over W) AddCommGrpCat.{0} :=
  (inferInstance : ∀ (U : X.C) (W : Over U),
    HasSheafify ((X.J.over U).over W) AddCommGrpCat.{0}) U W

/-- On a slice of the slice site `X.over U`, the morphisms inverted by sheafification of
abelian-group presheaves are exactly the locally bijective ones. -/
local instance restrOvWEqIter (U : X.C) (W : (X.over U).C) :
    ((X.over U).J.over W).WEqualsLocallyBijective AddCommGrpCat.{0} :=
  (inferInstance : ∀ (U : X.C) (W : Over U),
    ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}) U W

/-- Restriction of sheaves of modules along a morphism `g : W ⟶ U` preserves finite limits. -/
local instance restrOverMapLimits {U W : X.C} (g : W ⟶ U) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction of sheaves of modules along a morphism `g : W ⟶ U` preserves finite colimits. -/
local instance restrOverMapColimits {U W : X.C} (g : W ⟶ U) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

/-- **The restriction of an `m`-pseudo-coherent complex to a slice is `m`-pseudo-coherent
there.** This is the complex-level half of Stacks 08FU, part (3), read in the direction which
takes pseudo-coherence apart. -/
theorem isPseudoCoherentComplexFrom_restrictComplex
    (K : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (hK : X.IsPseudoCoherentComplexFrom K m) (V : X.C) :
    (X.over V).IsPseudoCoherentComplexFrom (X.restrictComplex K V) m := by
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
    obtain ⟨P, hP, α, hiso, hepi⟩ := hdata (Over.Hom.left f) hf
    let Fe :=
      (Stacks.SheafOfModules.sliceEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W).functor
    let Fec := Fe.mapHomologicalComplex (ComplexShape.up ℤ)
    let e : Fec.obj (X.restrictComplex K W.left) ≅
        (X.over V).restrictComplex (X.restrictComplex K V) W :=
      Fec.mapIso
          ((Stacks.SheafOfModules.overFunctorMapComplexIso.{0}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.hom).app K).symm ≪≫
        (Stacks.SheafOfModules.sliceEquivOverFunctorComplexIso
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W).app (X.restrictComplex K V)
    have : PreservesFiniteLimits Fe := inferInstance
    have : PreservesFiniteColimits Fe := inferInstance
    refine ⟨Fec.obj P, Stacks.SheafOfModules.isStrictlyPerfect_sliceEquiv
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W hP, Fec.map α ≫ e.hom, fun j hj => ?_, ?_⟩
    · exact isIso_homologyMap_comp_iso _ e j
        (RingedSpace.isIso_homologyMap_map Fe α j (hiso j hj))
    · exact epi_homologyMap_comp_iso _ e m (RingedSpace.epi_homologyMap_map Fe α m hepi)

variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hRestrDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory ovHasDerived

attribute [local instance] preservesFiniteLimitsOverFunctor preservesFiniteColimitsOverFunctor

/-- **Stacks 08FU, part (3), in the direction which restricts pseudo-coherence to a slice.** If
an object `E` of `D(O)` is `m`-pseudo-coherent, then its restriction to the localized ringed
site over any object `V` of `C` is `m`-pseudo-coherent there. -/
@[stacks 08FU "part (3), restriction to a slice"]
theorem isPseudoCoherentFrom_derivedRestriction
    (E : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hE : X.IsPseudoCoherentFrom E m) (V : X.C) :
    (X.over V).IsPseudoCoherentFrom
      ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E) m := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  refine ⟨X.restrictComplex K V, isPseudoCoherentComplexFrom_restrictComplex X K m hK V, ⟨?_⟩⟩
  exact ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app K).symm ≪≫
    (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategory.mapIso eK

end Restriction

end AlgebraicGeometry.RingedSite

end
