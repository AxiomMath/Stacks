module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SectionIdealCechPresheaf
public import StacksFrontier.RingTheory.Cech.GenPairRingIdeal

/-!
# The Čech identification of [Stacks, Tag 099D] on a ringed site, at the level of presheaves

Let `(𝒞, 𝒪)` be a ringed site and `f_1, …, f_r` global sections of `𝒪`. Two complexes of
presheaves of `𝒪`-modules are then available:

* `AlgebraicGeometry.RingedSite.presheafCechComplex`, the extended alternating Čech complex of
  `f_1, …, f_r` computed objectwise, `U ↦ Č(𝒪(U), f_1|_U, …, f_r|_U)`;
* `AlgebraicGeometry.RingedSite.sectionIdealCechComplex`, the complex `K^•_{U, I}` of
  [Stacks, Tag 099E], `U ↦ K(𝒪(U), I𝒪(U))`.

This file produces a **map of complexes of presheaves of modules** between them which is a
quasi-isomorphism at every object and compatible with the two augmentations onto the structure
presheaf. Both complexes and the map are pullbacks along one functor
`AlgebraicGeometry.RingedSite.genPairFunctor` of the corresponding objects on the category
`Stacks.GenPairSite.GenPair r` of rings carrying a chosen family of `r` elements, where they are
`Stacks.GenPairSite.cechComplexPre`, `Stacks.GenPairSite.kComplexNat` and
`Stacks.GenPairSite.cechToK`. Nothing of the Čech construction is redone: the assignment
`U ↦ (𝒪(U), f_1|_U, …, f_r|_U)` is a functor because the `f_i` are global sections, so their
restrictions compose on the nose.

The identification `Stacks.RingIdealSite.pullbackGenPair_kComplexNat` is what makes the target of
the pulled-back map the complex `AlgebraicGeometry.RingedSite.sectionIdealCechComplex`: the chosen
family is forgotten, and the complex depends on the objectwise ideal alone.

## Main definitions

* `AlgebraicGeometry.RingedSite.genPairFunctor`: the functor `𝒞ᵒᵖ ⥤ GenPair r` sending an object
  to its ring of sections carrying the restricted family.
* `AlgebraicGeometry.RingedSite.presheafCechComplex`: the objectwise extended alternating Čech
  complex, as a complex of presheaves of `𝒪`-modules, and
  `AlgebraicGeometry.RingedSite.presheafCechAugmentation` its augmentation.
* `AlgebraicGeometry.RingedSite.presheafCechToSectionIdeal`: **the comparison `Č^• ⟶ K^•`**,
  with its target the pullback of `Stacks.GenPairSite.kComplexNat`, which
  `Stacks.RingIdealSite.pullbackGenPair_kComplexNat` and
  `AlgebraicGeometry.RingedSite.genPairFunctor_comp_forgetElts` identify with
  `AlgebraicGeometry.RingedSite.sectionIdealCechComplex`.

## Main results

* `AlgebraicGeometry.RingedSite.genPairFunctor_comp_forgetElts`: forgetting the chosen family
  recovers `AlgebraicGeometry.RingedSite.ringIdealFunctor`, so the two pullbacks agree and the
  target of the comparison is the complex `K^•_{U, I}`.

## Implementation notes

Two properties of the comparison hold on generated pairs and are not restated here in the site's
own spelling: that it is a quasi-isomorphism at every object
(`Stacks.GenPairSite.quasiIso_evaluation_cechToK`) and that it carries the Čech augmentation to
the augmentation of `K` (`Stacks.GenPairSite.cechToKTerm_comp_kAugZero`). Both transport along
the pullback, but the transport is not `rfl`: the target of the comparison here is spelled through
`AlgebraicGeometry.RingedSite.ringIdealFunctor` and the source through
`AlgebraicGeometry.RingedSite.genPairFunctor`, and identifying them needs
`Stacks.RingIdealSite.pullbackGenPair_kComplexNat` rather than definitional unfolding, the colimit
defining `K` being behind a non-exposed `getColimitCocone`. The two properties are therefore read
at `(𝒪(U), f_1|_U, …, f_r|_U)` on generated pairs.

No `@[stacks]` attribute is attached. [Stacks, Tag 099D] is registered on
`Stacks.LocalCohomology.nonempty_functorialCechData`, and [Stacks, Tag 099E] asserts the
existence of a global map `K → 𝒪` in `D(𝒪)`, which a map of presheaf complexes is a step towards
and not a clause of.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.RingedSite

open Stacks.RingIdealSite Stacks.GenPairSite

variable {X : RingedSite.{u, v, w}} {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{w}))

/-- **The functor to the generated pairs attached to a finite family of global sections of
`𝒪`**: an object `U` goes to its ring of sections carrying the family `f_1|_U, …, f_r|_U`. A
morphism goes to the restriction map, which carries the family pointwise onto the family because
the `f_i` are global sections — so the restrictions compose on the nose and this really is a
functor. -/
def genPairFunctor : X.Cᵒᵖ ⥤ GenPair.{w} r where
  obj U :=
    { ring := X.O.obj.obj U
      commRing := inferInstance
      elts := fun i ↦ globalSectionVal (f i) U }
  map {_ _} g :=
    { toRingHom := (X.O.obj.map g).hom
      map_elts := fun i ↦ globalSectionVal_map (f i) g }
  map_id U := GenPair.Hom.ext' (congrArg CommRingCat.Hom.hom (X.O.obj.map_id U))
  map_comp {_ _ _} g h :=
    GenPair.Hom.ext' (congrArg CommRingCat.Hom.hom (X.O.obj.map_comp g h))

/-- The `i`-th chosen element over `U` is the restriction `f_i|_U` of the global section `f_i`. -/
@[simp]
theorem genPairFunctor_obj_elts (U : X.Cᵒᵖ) (i : Fin r) :
    ((genPairFunctor f).obj U).elts i = globalSectionVal (f i) U := rfl

/-- The ring homomorphism underlying the image of `g` is the restriction map of `𝒪` along `g`. -/
@[simp]
theorem genPairFunctor_map_toRingHom {U V : X.Cᵒᵖ} (g : U ⟶ V) :
    ((genPairFunctor f).map g).toRingHom = (X.O.obj.map g).hom := rfl

/-- **Forgetting the chosen family recovers the functor to the rings with an ideal**: the ideal
generated by the restricted family over `U` is the objectwise ideal
`AlgebraicGeometry.RingedSite.sectionSpan`. -/
theorem genPairFunctor_comp_forgetElts :
    genPairFunctor f ⋙ forgetElts.{w} r = ringIdealFunctor f := rfl

/-- **The pullback of presheaves of modules on the generated pairs along
`AlgebraicGeometry.RingedSite.genPairFunctor`.** -/
abbrev genPairPullback :
    GenPairModule.{w} r ⥤
      PresheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  PresheafOfModules.pushforward₀ (genPairFunctor f).rightOp (structureRings.{w} r)

/-- Restriction of presheaves of modules along `AlgebraicGeometry.RingedSite.genPairFunctor`
preserves zero morphisms, a morphism being carried to the morphism with the same components. -/
instance preservesZeroMorphisms_genPairPullback :
    (genPairPullback f).PreservesZeroMorphisms where
  map_zero _ _ := PresheafOfModules.hom_ext fun _ ↦ rfl

/-- **The extended alternating Čech complex of `f_1, …, f_r` computed objectwise**, as a complex
of presheaves of `𝒪`-modules: at `U` it is `Č(𝒪(U), f_1|_U, …, f_r|_U)`. -/
abbrev presheafCechComplex :
    CochainComplex (PresheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) ℕ :=
  ((genPairPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj (cechComplexPre.{w} r)

/-- **The augmentation of the objectwise Čech complex onto the structure presheaf.** -/
abbrev presheafCechAugmentation :
    (presheafCechComplex f).X 0 ⟶
      PresheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj :=
  (genPairPullback f).map (cechAugZeroPre.{w} r)

/-- **The comparison `Č^• ⟶ K^•_{U, I}` of complexes of presheaves of `𝒪`-modules**, the pullback
of `Stacks.GenPairSite.cechToK`. -/
def presheafCechToSectionIdeal :
    presheafCechComplex f ⟶
      ((genPairPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (Stacks.GenPairSite.kComplexNat.{w} r) :=
  ((genPairPullback f).mapHomologicalComplex (ComplexShape.up ℕ)).map (cechToK.{w} r)

end AlgebraicGeometry.RingedSite

end
