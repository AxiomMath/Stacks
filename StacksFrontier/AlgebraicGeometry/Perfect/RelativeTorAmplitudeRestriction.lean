module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkMateComp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkComposition
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to an open and shifting preserve the hypotheses on `K₀` and `L₀`

Stacks 0DHX is read at a pair `(K₀, L₀)` of objects of the derived category of the fixed stage,
with `K₀` pseudo-coherent and `L₀` of finite Tor dimension over the base. The induction of Stacks
08DR which reduces Stacks 0DI7 to that affine input moves the pair twice: it restricts both
objects to an open subscheme of the fixed stage, and — because the Mayer--Vietoris step is a five
lemma, which at degree `n` consumes degrees `n ± 1` — it shifts the second object by an arbitrary
integer. This file shows both hypotheses survive both moves.

Tor amplitude over the base is stalkwise, and the stalk maps of an open immersion are
isomorphisms; that is what makes restriction along an open immersion cheaper than a general base
change, which needs a cartesian square and Tor independence
(`AlgebraicGeometry.derivedPullback_hasTorAmplitudeOver`). Shifting a cochain complex by `n`
reindexes its terms, so an amplitude interval `[a, b]` becomes `[a - n, b - n]`: the predicate
records the interval, not merely its finiteness, so the shift statements carry that bookkeeping.

## Main results

* `AlgebraicGeometry.hasTorAmplitudeOver_derivedPullback_of_isOpenImmersion`: Tor amplitude over
  the base is inherited by the derived pullback along an open immersion, over the composed base
  morphism.
* `AlgebraicGeometry.hasTorAmplitudeOver_shift`: Tor amplitude in `[a, b]` over the base becomes
  Tor amplitude in `[a - n, b - n]` after shifting by `n`, for every integer `n`, positive or
  negative.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedRestrictModules`: pseudo-coherence,
  in the unbounded sense, is inherited by the derived restriction to an open subspace.
* `AlgebraicGeometry.RingedSpace.IsPseudoCoherent.shift` and
  `StacksDraft.PseudoCoherence.IsPseudoCoherent.shift`: pseudo-coherence in the unbounded sense
  is stable under shifting, on a ringed space and over a ring.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonicalLift_shift` and
  `StacksDraft.TorAmplitude.hasTorAmplitudeCanonicalLift_restrictScalars_extendScalars`: the two
  ring-level transfers the geometric statements rest on.
* `ModuleCat.extendRestrictScalarsSelfIso`: extending and then restricting scalars along a ring
  isomorphism is the identity functor.

## Implementation notes

`ModuleCat.extendRestrictScalarsSelfIso` and `ModuleCat.extendRestrictScalarsCompIso` belong
upstream next to `ModuleCat.restrictExtendScalarsSelfIso`, which is the opposite composite; they
are carried here because that file is outside the subtree this module was written in.

The transfer at a stalk is stated as a lemma about three abstract ring maps `σ`, `ρ`, `τ` with
`τ = ρ ∘ σ` rather than about the stalk maps themselves. The reason is that `(j ≫ f).base y` and
`f.base (j.base y)` are definitionally but not reducibly equal, so a goal which mentions both
spellings of the base ring is not type-correct at `instances` transparency and the `Additive`
instances of `CategoryTheory.Functor.mapHomologicalComplexCompIso` fail to synthesize. Taking
the rings abstractly pays that crossing once, in the application.

The proof of the restriction statement follows `derivedPullback_hasTorAmplitudeOver` step for
step: a K-flat representative is chosen, on which derived pullback is degreewise pullback
(`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`), and the relative stalk complex of the
degreewise pullback at `y` is identified with the one downstairs at `j(y)`. K-flatness is used
only for that first identification — the stalk step needs no flatness, because
`Stacks.ModuleSkyscraper.pullbackStalkIso` turns the stalk of the pullback into an extension of
scalars along `j.stalkMap y`, which an open immersion makes invertible.

The pseudo-coherence statements are the unbounded forms of the `m`-bounded ones:
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent` asks for *one* complex representative which is
`m`-pseudo-coherent for every `m`, so it is not the conjunction over `m` of
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom` and does not follow formally from it. They
are stated for `AlgebraicGeometry.RingedSpace.derivedRestrictModules`, the spelling of the
`m`-bounded statements; the identification of that functor with derived pullback along the open
immersion is a separate comparison.

## References

* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0C0V](https://stacks.math.columbia.edu/tag/0C0V)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude

universe d d' v u

/-! ### Extension and restriction of scalars along a ring isomorphism -/

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **Along a ring isomorphism, restriction of scalars undoes extension of scalars.** This is the
composite opposite to `ModuleCat.restrictExtendScalarsSelfIso`. -/
public def extendRestrictScalarsSelfIso (e : R ≃+* S) :
    extendScalars.{u, u, u} e.toRingHom ⋙ restrictScalars.{u} e.toRingHom ≅
      𝟭 (ModuleCat.{u} R) :=
  Functor.isoWhiskerRight (extendScalarsIsoRestrictScalarsSymm e)
      (restrictScalars.{u} e.toRingHom) ≪≫
    (restrictScalarsComp'.{u} e.toRingHom e.symm.toRingHom
      (e.symm.toRingHom.comp e.toRingHom) rfl).symm ≪≫
    restrictScalarsId'.{u} _ (by ext x; simp)

/-- Extending scalars along a ring isomorphism `e` and then restricting along `τ = e ∘ σ` is
restricting along `σ`. -/
public def extendRestrictScalarsCompIso {A B : Type u} [CommRing A] [CommRing B]
    (σ : R →+* A) (τ : R →+* B) (e : A ≃+* B) (hτ : τ = e.toRingHom.comp σ) :
    extendScalars.{u, u, u} e.toRingHom ⋙ restrictScalars.{u} τ ≅ restrictScalars.{u} σ :=
  Functor.isoWhiskerLeft (extendScalars.{u, u, u} e.toRingHom)
      (restrictScalarsComp'.{u} σ e.toRingHom τ hτ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extendRestrictScalarsSelfIso e) (restrictScalars.{u} σ) ≪≫
    Functor.leftUnitor _

end ModuleCat

/-- Shifting commutes with `Q`: an isomorphism `Q K ≅ E` gives `Q (K⟦n⟧) ≅ E⟦n⟧`. -/
private def shiftQIso {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K : CochainComplex C ℤ} {E : DerivedCategory C} (e : DerivedCategory.Q.obj K ≅ E) (n : ℤ) :
    DerivedCategory.Q.obj (K⟦n⟧) ≅ E⟦n⟧ :=
  (DerivedCategory.Q.commShiftIso n).app K ≪≫ (shiftFunctor (DerivedCategory C) n).mapIso e

section Standard

attribute [local instance] HasDerivedCategory.standard

/-! ### Tor amplitude of a single complex of modules -/

namespace StacksDraft.TorAmplitude

/-- Tor amplitude of the lift of an object of `D(R)` depends only on its isomorphism class. -/
public theorem hasTorAmplitudeCanonicalLift_of_iso {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L) (a b : ℤ)
    (hK : HasTorAmplitudeCanonicalLift.{u, u, u} K a b) :
    HasTorAmplitudeCanonicalLift.{u, u, u} L a b :=
  hasTorAmplitudeCanonical_of_iso ((moduleLift.{u, u, u} R).mapDerivedCategory.mapIso e) a b hK

/-- **Shifting an object of `D(R)` by `n` translates a Tor-amplitude interval by `-n`.** A flat
representative in `[a, b]` is carried to a flat representative in `[a - n, b - n]` by the shift,
which reindexes the terms of a complex. -/
public theorem hasTorAmplitudeCanonical_shift {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b n : ℤ)
    (hK : HasTorAmplitudeCanonical R K a b) :
    HasTorAmplitudeCanonical R (K⟦n⟧) (a - n) (b - n) := by
  obtain ⟨E, hflat, hGE, hLE, ⟨e⟩⟩ :=
    (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R K a b).1 hK
  have := hGE
  have := hLE
  refine (hasTorAmplitudeCanonical_iff_hasFlatRepresentative R (K⟦n⟧) (a - n) (b - n)).2
    ⟨E⟦n⟧, fun i => ?_, CochainComplex.isStrictlyGE_shift E a n (a - n) (by ring),
      CochainComplex.isStrictlyLE_shift E b n (b - n) (by ring),
      ⟨(shiftQIso e.symm n).symm⟩⟩
  exact hflat (i + n)

/-- **Shifting translates the Tor-amplitude interval of the lift of an object of `D(R)`.** -/
public theorem hasTorAmplitudeCanonicalLift_shift {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R)) (a b n : ℤ)
    (hK : HasTorAmplitudeCanonicalLift.{u, u, u} K a b) :
    HasTorAmplitudeCanonicalLift.{u, u, u} (K⟦n⟧) (a - n) (b - n) :=
  hasTorAmplitudeCanonical_of_iso
    (((moduleLift.{u, u, u} R).mapDerivedCategory.commShiftIso n).app K).symm (a - n) (b - n)
    (hasTorAmplitudeCanonical_shift _ a b n hK)

/-- **Tor amplitude over a ring is unchanged by extending scalars along an isomorphism.** If
`τ = ρ ∘ σ` with `ρ` the ring map of an isomorphism `e`, then extending scalars along `ρ` and
restricting along `τ` has the Tor amplitude over the source of `σ` of restriction along `σ`. -/
public theorem hasTorAmplitudeCanonicalLift_restrictScalars_extendScalars
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (σ : R →+* A) (ρ : A →+* B) (τ : R →+* B) (e : A ≃+* B)
    (he : e.toRingHom = ρ) (hτ : τ = ρ.comp σ)
    (Z : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (hZ : HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) a b) :
    HasTorAmplitudeCanonicalLift.{u, u, u} (DerivedCategory.Q.obj
      (((ModuleCat.restrictScalars τ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))) a b := by
  subst he
  exact hasTorAmplitudeCanonicalLift_of_iso (DerivedCategory.Q.mapIso
    ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendRestrictScalarsCompIso σ τ e hτ)
      (ComplexShape.up ℤ)).app Z).symm) a b hZ

end StacksDraft.TorAmplitude

/-! ### Pseudo-coherence over a ring under shifting -/

namespace StacksDraft.PseudoCoherence

/-- **Pseudo-coherence over a ring is stable under shifting in either direction.** A
bounded-above complex of finite free modules stays one after shifting: the shift reindexes the
terms and translates the upper bound. -/
@[sga "6 I 2.5" "a), special case"]
public theorem IsPseudoCoherent.shift {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{v} R)} (hK : IsPseudoCoherent K) (n : ℤ) :
    IsPseudoCoherent (K⟦n⟧) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  have := hb
  refine ⟨E⟦n⟧, ⟨⟨b - n, CochainComplex.isStrictlyLE_shift E b n (b - n) (by ring)⟩,
    fun i => ?_⟩, ⟨shiftQIso e n⟩⟩
  exact hE.finiteFree (i + n)

end StacksDraft.PseudoCoherence

/-! ### Restriction of Tor amplitude over the base along an open immersion -/

namespace AlgebraicGeometry

variable {X S V : Scheme.{u}} (f : X ⟶ S) (j : V ⟶ X)

variable [IsOpenImmersion j]

/-- The germ map of an open immersion at a point, as an isomorphism of rings. -/
public def stalkRingEquivOfIsOpenImmersion (y : V) :
    X.presheaf.stalk (j.base y) ≃+* V.presheaf.stalk y :=
  (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv

/-- At a point of an open subscheme, the relative stalk complex of the degreewise pullback of a
complex inherits the Tor amplitude of the relative stalk complex downstairs: the stalk of the
pullback is an extension of scalars along the germ map of the open immersion (Stacks 0098), which
is invertible, so restricting scalars to the base undoes it. -/
public theorem relativeStalkAmplitude_pullback_of_isOpenImmersion
    (K : CochainComplex X.Modules ℤ) (a b : ℤ) (y : V)
    (hamp : HasTorAmplitudeCanonicalLift.{u, u, u}
      (DerivedCategory.Q.obj (relativeStalkComplex f K (j.base y))) a b) :
    HasTorAmplitudeCanonicalLift.{u, u, u}
      (DerivedCategory.Q.obj (relativeStalkComplex (j ≫ f)
        (((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) y))
      a b := by
  have hring := hasTorAmplitudeCanonicalLift_restrictScalars_extendScalars
    (f.stalkMap (j.base y)).hom (j.stalkMap y).hom ((j ≫ f).stalkMap y).hom
    (stalkRingEquivOfIsOpenImmersion j y) rfl (Stacks.ModuleSkyscraper.stalkMap_hom_comp j f y)
    (((Stacks.ModuleSkyscraper.modulesStalkFunctor X (j.base y)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) a b hamp
  exact hasTorAmplitudeCanonicalLift_of_iso (DerivedCategory.Q.mapIso
    (((ModuleCat.restrictScalars ((j ≫ f).stalkMap y).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (pullbackRelativeStalkObjIso j y K).symm)) a b hring

/-- **Tor amplitude over the base is inherited by the derived pullback along an open
immersion.** If an object of `D(𝒪_X)` has Tor amplitude in `[a, b]` relative to `f : X ⟶ S`, its
derived pullback to an open subscheme `V` of `X` has Tor amplitude in `[a, b]` relative to the
composite `V ⟶ X ⟶ S`.

Unlike the Tor-independent base change of Stacks 0C0V, no cartesian square and no Tor
independence are needed: the germ maps of an open immersion are isomorphisms. -/
public theorem hasTorAmplitudeOver_derivedPullback_of_isOpenImmersion
    (E : DerivedCategory X.Modules) (a b : ℤ) (hE : HasTorAmplitudeOver f E a b) :
    HasTorAmplitudeOver (j ≫ f)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj E) a b := by
  obtain ⟨K₀, ⟨e₀⟩, hK₀⟩ := hE
  obtain ⟨K, q, hK, -, hq, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toSheafedSpace K₀
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
  let eK : DerivedCategory.Q.obj K ≅ E := asIso (DerivedCategory.Q.map q) ≪≫ e₀
  refine ⟨((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    ⟨(Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat j.toLRSHom.toShHom K hK).symm ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).mapIso eK⟩, fun y => ?_⟩
  exact relativeStalkAmplitude_pullback_of_isOpenImmersion f j K a b y
    (relativeStalkAmplitude_of_derivedIso f a b (e₀ ≪≫ eK.symm) hK₀ (j.base y))

/-! ### Tor amplitude over the base under shifting -/

/-- The relative stalk complex of a shifted complex is the shift of the relative stalk complex:
the stalk functor and restriction of scalars are applied degreewise, and shifting a cochain
complex reindexes its terms. -/
public def relativeStalkComplexShiftIso (K : CochainComplex X.Modules ℤ) (x : X) (n : ℤ) :
    relativeStalkComplex f (K⟦n⟧) x ≅ (relativeStalkComplex f K x)⟦n⟧ :=
  ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso
      ((((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
        (ComplexShape.up ℤ)).commShiftIso n).app K) ≪≫
    (((ModuleCat.restrictScalars (f.stalkMap x).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).commShiftIso n).app
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K)

/-- **Shifting translates the interval of Tor amplitude over the base.** An object of `D(𝒪_X)`
with Tor amplitude in `[a, b]` relative to `f` has Tor amplitude in `[a - n, b - n]` relative to
`f` after shifting by `n`, for every integer `n`, positive or negative. -/
public theorem hasTorAmplitudeOver_shift
    (E : DerivedCategory X.Modules) (a b n : ℤ) (hE : HasTorAmplitudeOver f E a b) :
    HasTorAmplitudeOver f (E⟦n⟧) (a - n) (b - n) := by
  obtain ⟨K, ⟨e⟩, hK⟩ := hE
  refine ⟨K⟦n⟧, ⟨shiftQIso e n⟩, fun x => ?_⟩
  exact hasTorAmplitudeCanonicalLift_of_iso
    (((DerivedCategory.Q.commShiftIso n).app (relativeStalkComplex f K x)).symm ≪≫
      DerivedCategory.Q.mapIso (relativeStalkComplexShiftIso f K x n).symm)
    (a - n) (b - n) (hasTorAmplitudeCanonicalLift_shift _ a b n (hK x))

end AlgebraicGeometry

end Standard

/-! ### Pseudo-coherence on a ringed space, unbounded -/

namespace AlgebraicGeometry.RingedSpace

open StrictlyPerfect

variable {X : RingedSpace.{u, u}}

/-- **The restriction of a pseudo-coherent complex to an open subspace is pseudo-coherent.** The
unbounded form of `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_restrictComplex`. -/
public theorem isPseudoCoherentComplex_restrictComplex
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (hK : IsPseudoCoherentComplex K)
    (W : Opens X.carrier) : IsPseudoCoherentComplex (restrictComplex K W) :=
  fun m => isPseudoCoherentComplexFrom_restrictComplex K m (hK m) W

/-- **Pseudo-coherence of a complex is stable under shifting in either direction.** The unbounded
form of `AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom.shift`. -/
@[sga "6 I 2.5" "a), special case"]
public theorem IsPseudoCoherentComplex.shift {K : CochainComplex (OXMod.{u, u} X) ℤ}
    (hK : IsPseudoCoherentComplex K) (n : ℤ) : IsPseudoCoherentComplex (K⟦n⟧) :=
  fun m => by simpa using (hK (m + n)).shift n

variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **The derived restriction of a pseudo-coherent object to an open subspace is
pseudo-coherent.** The unbounded form of
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules`: a pseudo-coherent
complex representing `E` restricts to a pseudo-coherent complex, and it represents the derived
restriction of `E`. -/
public theorem isPseudoCoherent_derivedRestrictModules
    [∀ V : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X)) (hE : IsPseudoCoherent E) (W : Opens X.carrier) :
    IsPseudoCoherent ((derivedRestrictModules X W).obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact ⟨restrictComplex K W, isPseudoCoherentComplex_restrictComplex K hK W,
    ⟨(derivedRestrictModulesObjQIso X W K).symm ≪≫ (derivedRestrictModules X W).mapIso e⟩⟩

/-- **Pseudo-coherence on a ringed space is stable under shifting in either direction.** -/
public theorem IsPseudoCoherent.shift {E : DerivedCategory (OXMod.{u, u} X)}
    (hE : IsPseudoCoherent E) (n : ℤ) : IsPseudoCoherent (E⟦n⟧) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact ⟨K⟦n⟧, hK.shift n, ⟨shiftQIso e n⟩⟩

end AlgebraicGeometry.RingedSpace

end
