module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.IteratedSliceFiniteFreeSummands
import StacksCore.Tactic.StacksAttribute

/-!
# Taking pseudo-coherence apart, at independent universes

This file is the universe-general form of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Restriction.lean`, together with the
two facts about strictly perfect complexes that the descent of Stacks 08HE needs in the same
generality. That file states them for a ringed site `X : RingedSite.{u, v, 0}` with modules in
`SheafOfModules.{0}`; this one states them for `X : RingedSite.{u, v, w}` with modules in
`SheafOfModules.{w}`, which is what the small Zariski and small étale ringed sites of a scheme
need — their structure sheaves have sections in `Type u`.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_restrictComplex_general`: the
  restriction of an `m`-pseudo-coherent complex to a slice is `m`-pseudo-coherent there.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction_general`: **Stacks 08FU,
  part (3)**, in the direction which restricts pseudo-coherence to a slice.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_isStrictlyPerfect_general` and
  `isPseudoCoherentFrom_Q_of_isStrictlyPerfect_general`: a strictly perfect complex is
  `n`-pseudo-coherent for every `n`.

## Implementation notes

**Why this file exists rather than a generalization in place.** The source files are owned by
another development; their statements are restated here with `0` replaced by `w` throughout and
no change to any proof. The restatement is possible because every input is already
universe-general: `Stacks.SheafOfModules.sliceEquiv`, `sliceEquivUnitIso` and
`sliceEquivOverMapFunctorIso` are stated at a free ring universe, and so is
`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex`, which is what carries strict
perfectness to the iterated slice; it is stated at `RingCat.{w}` with both categories at
anonymous universes.

`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_isStrictlyPerfect_general` and
`isStrictlyPerfect_over_general` repeat `private` lemmas of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`; that file is owned
elsewhere, so they cannot be made public there. They are already stated at a free `w`, so the
repetition is verbatim.

Unlike the source, the sheafification data of the *iterated* slices is derived rather than
hypothesised: the `local instance`s `AlgebraicGeometry.RingedSite.iterHasSheafify` and `iterWEq`
of `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean` transport it
along `CategoryTheory.Over.iteratedSliceEquiv`, and are re-enabled below. So the statements
below carry only the sheafification hypotheses on the site and on its first slices.

## References

* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d d'

namespace Stacks.SheafOfModules

/-! ### Transport of a strictly perfect complex to an iterated slice -/

section SliceForwardGeneral

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) (U : C) (V : Over U)

/-- Transport of sheaves of modules to an iterated slice is additive: it is an equivalence, so
it preserves binary products.

`Stacks.SheafOfModules.sliceEquivFunctorAdditive` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Restriction.lean` is the same
statement at `R : Sheaf J RingCat.{0}`; this one is at `R : Sheaf J RingCat.{w}`, so the two
are not the same declaration and importing that one would narrow the sections universe. -/
instance sliceEquivFunctorAdditiveGeneral : ((sliceEquiv R U V).functor).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The degreewise form of `Stacks.SheafOfModules.sliceEquivOverMapFunctorIso`.** Restricting
a complex of `O|_U`-modules along the structure arrow of `V` and transporting it to the iterated
slice over `V` is restricting it to that iterated slice. -/
def sliceEquivOverFunctorComplexIsoGeneral :
    (SheafOfModules.overMap.{w} R V.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((sliceEquiv R U V).functor).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (SheafOfModules.overFunctor.{w} (R.over U) V).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (sliceEquivOverMapFunctorIso R U V) (ComplexShape.up ℤ)

variable [HasSheafify (J.over V.left) AddCommGrpCat.{w}]
  [(J.over V.left).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify ((J.over U).over V) AddCommGrpCat.{w}]
  [((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Transport to an iterated slice carries a strictly perfect complex to a strictly perfect
complex.** The transport is an equivalence, hence exact, and it matches up the two structure
sheaves by `Stacks.SheafOfModules.sliceEquivUnitIso`. -/
theorem isStrictlyPerfect_sliceEquiv_general
    {P : CochainComplex (SheafOfModules.{w} (R.over V.left)) ℤ}
    (hP : IsStrictlyPerfect (R.over V.left) P) :
    IsStrictlyPerfect ((R.over U).over V)
      ((((sliceEquiv R U V).functor).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have : PreservesFiniteColimits ((sliceEquiv R U V).functor) := inferInstance
  isStrictlyPerfect_mapHomologicalComplex _ (sliceEquivUnitIso R U V).symm hP

end SliceForwardGeneral

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

/-! ### A strictly perfect complex is pseudo-coherent -/

section StrictlyPerfectGeneral

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Restriction to a slice of the site carries a strictly perfect complex to a strictly perfect
complex. This repeats a `private` lemma of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/Summands.lean`. -/
theorem isStrictlyPerfect_over_general (U : X.C)
    {P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) :
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)
      (X.restrictComplex P U) :=
  have : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U
  Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
    (Stacks.SheafOfModules.overFunctorUnitIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) hP

/-- **A strictly perfect complex is `n`-pseudo-coherent for every `n`**: the identity of its own
restriction is an approximation over the total covering. -/
theorem isPseudoCoherentComplexFrom_of_isStrictlyPerfect_general
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) (n : ℤ) :
    X.IsPseudoCoherentComplexFrom P n := by
  intro U
  refine ⟨⊤, by simp, fun V f hf => ?_⟩
  exact ⟨X.restrictComplex P V, isStrictlyPerfect_over_general X V hP, 𝟙 _,
    fun _ _ => by simp only [HomologicalComplex.homologyMap_id]; infer_instance,
    by simp only [HomologicalComplex.homologyMap_id]; infer_instance⟩

/-- The object of `D(O)` represented by a strictly perfect complex is `n`-pseudo-coherent for
every `n`. -/
theorem isPseudoCoherentFrom_Q_of_isStrictlyPerfect_general
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) (n : ℤ) :
    X.IsPseudoCoherentFrom (DerivedCategory.Q.obj P) n :=
  ⟨P, isPseudoCoherentComplexFrom_of_isStrictlyPerfect_general X P hP n, ⟨Iso.refl _⟩⟩

end StrictlyPerfectGeneral

/-! ### Restriction of pseudo-coherence to a slice -/

section RestrictionGeneral

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

-- The sheafification data of the slices and of the iterated slices, and the exactness of
-- restriction, at the spellings the localized ringed site uses. All of these are `local
-- instance`s of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/LocallyFiniteTorDimension.lean` and
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`, already at a
-- free sections universe `w`; the declarations are imported, so only the instance attribute has
-- to be re-enabled here.
attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective
attribute [local instance] iterHasSheafify iterWEq iterHasSheafifyAll iterWEqAll
attribute [local instance] overMapLimits overMapColimits ovFunctorLimits ovFunctorColimits

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The restriction of an `m`-pseudo-coherent complex to a slice is `m`-pseudo-coherent
there**, at independent universes. This is the complex-level half of Stacks 08FU, part (3), read
in the direction which takes pseudo-coherence apart. -/
theorem isPseudoCoherentComplexFrom_restrictComplex_general
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ)
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
          ((Stacks.SheafOfModules.overFunctorMapComplexIso.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.hom).app K).symm ≪≫
        (Stacks.SheafOfModules.sliceEquivOverFunctorComplexIsoGeneral
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W).app
          (X.restrictComplex K V)
    have : PreservesFiniteLimits Fe := inferInstance
    have : PreservesFiniteColimits Fe := inferInstance
    have : Fe.PreservesHomology := Functor.preservesHomologyOfExact Fe
    refine ⟨Fec.obj P,
      Stacks.SheafOfModules.isStrictlyPerfect_sliceEquiv_general
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W hP,
      Fec.map α ≫ e.hom, fun j hj => ?_, ?_⟩
    · exact isIso_homologyMap_comp_iso _ e j (isIso_homologyMap_map Fe α j (hiso j hj))
    · exact epi_homologyMap_comp_iso _ e m (epi_homologyMap_map Fe α m hepi)

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hRestrDer : ∀ U : X.C,
  HasDerivedCategory.{d'}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

-- The derived-category models of the slices, at both spellings; again the `local instance`s of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`.
attribute [local instance] locallyOverRingSheafHasDerivedCategory ovHasDerived

/-- Restriction to a slice carries an isomorphism `E ≅ Q K` to `E|_V ≅ Q (K|_V)`. -/
private def mapDerivedCategory_overFunctor_iso (V : X.C)
    {E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eK : DerivedCategory.Q.obj K ≅ E) :
    DerivedCategory.Q.obj (X.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E :=
  ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app K).symm ≪≫
    (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategory.mapIso eK

/-- **Stacks 08FU, part (3), in the direction which restricts pseudo-coherence to a slice**, at
independent universes. If an object `E` of `D(O)` is `m`-pseudo-coherent, then its restriction to
the localized ringed site over any object `V` of `C` is `m`-pseudo-coherent there. -/
theorem isPseudoCoherentFrom_derivedRestriction_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (m : ℤ) (hE : X.IsPseudoCoherentFrom E m) (V : X.C) :
    (X.over V).IsPseudoCoherentFrom
      ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E) m := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  refine ⟨X.restrictComplex K V,
    isPseudoCoherentComplexFrom_restrictComplex_general X K m hK V,
    ⟨mapDerivedCategory_overFunctor_iso X V eK⟩⟩

/-- **Stacks 08FU, part (3), all degrees at once, in the direction which restricts
pseudo-coherence to a slice**, at independent universes. If an object `E` of `D(O)` is
pseudo-coherent, then its restriction to the localized ringed site over any object `V` of `C` is
pseudo-coherent there.

This is not the fixed-degree statement read in each degree: the all-degrees clause of Stacks
08FT (3) asks for **one** complex which is `m`-pseudo-coherent for every `m`, and a family of
degreewise statements does not provide it.  What the proof restricts is the single complex that
pseudo-coherence of `E` already provides, and it stays `m`-pseudo-coherent for every `m` by
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_restrictComplex_general`, which is
itself stated at one complex and an arbitrary degree; so no quantifier swap is needed. -/
@[stacks 08FU "part (3), all degrees, restriction to a slice"]
theorem isPseudoCoherent_derivedRestriction_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPseudoCoherent E) (V : X.C) :
    (X.over V).IsPseudoCoherent
      ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  refine ⟨X.restrictComplex K V,
    fun m => isPseudoCoherentComplexFrom_restrictComplex_general X K m (hK m) V,
    ⟨mapDerivedCategory_overFunctor_iso X V eK⟩⟩

end RestrictionGeneral

end AlgebraicGeometry.RingedSite

end
