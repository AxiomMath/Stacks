module

public import Mathlib.Algebra.Ring.Shrink
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ConstructibleAscendingChain
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleEssentiallyConstantColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Shrinking the coefficient ring of a constructible sheaf into the coefficient universe

The module development of this library is pinned to a Noetherian coefficient ring `Λ` living in
`Type (u + 1)`, the same universe as the modules: Stacks 09BH (3)
(`AlgebraicGeometry.isConstructibleModuleSheaf_of_mono`), Stacks 095P (3)
(`AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit`) and
Stacks 095N (`AlgebraicGeometry.isConstructibleModuleSheaf_iff_qcqsShriekPresentation`) are all
stated that way, because the shriek-presentation route passes through `ModuleCat.free Λ`, whose
source `Type u ⥤ ModuleCat.{u} Λ` ties the module universe to the ring universe.

Several rings a consumer actually wants do not live there. `ℤ` and every `ZMod m` live in
`Type 0`, while sheaves of modules over them are taken in `ModuleCat.{u + 1}`; this is the shape
Stacks 03UM's ℓ-adic sheaves have.

`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IntegerShriekPresentation` closes
that gap at `ℤ` alone, by transporting along `ULift.ringEquiv`. Nothing in the transport is
special to `ℤ`: the two universes of `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` are
independent, so for *any* ring `R` small in the coefficient universe the restriction of scalars
along `Shrink.ringEquiv` is an equivalence `ModuleCat.{s} R ≌ ModuleCat.{s} (Shrink.{s} R)`, and
`Shrink.{u + 1} R` is a Noetherian ring in `Type (u + 1)` whenever `R` is Noetherian. This file
performs the transport once and for all, and reads off the statements of the module development
that a consumer needs at a small coefficient ring.

`Shrink` is used in place of `ULift` because `ULift.{u + 1} R` lands in `Type (max (u + 1) r)`,
which is `Type (u + 1)` only for a ring universe `r` that is literally `0`, whereas
`Shrink.{u + 1} R` lands in `Type (u + 1)` for every `R` with `Small.{u + 1} R` — in particular
for every ring in `Type 0`, with no side condition for the consumer to discharge.

## Main definitions

* `ModuleCat.restrictScalarsShrinkEquivalence` — restriction of scalars along `Shrink.ringEquiv`,
  as an equivalence of module categories with the module universe free.
* `AlgebraicGeometry.SmallEtale.sheafShrinkEquivalence` — the induced equivalence of sheaf
  categories on the small étale site.

## Main results

* `AlgebraicGeometry.isConstructibleModuleSheaf_shrink` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_of_shrink` — constructibility is carried both
  ways along that equivalence.
* `AlgebraicGeometry.isConstructibleModuleSheaf_of_mono'` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_of_epi'` — **Stacks 09BH (3)** for a Noetherian
  coefficient ring small in the coefficient universe.
* `AlgebraicGeometry.isSerreClass_isConstructibleModuleSheaf_of_small` — the constructible
  sheaves of `R`-modules form a strong Serre subcategory, for such a ring.
* `AlgebraicGeometry.exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit'` —
  **Stacks 095P (3)** for such a ring.
* `AlgebraicGeometry.isNoetherianObject_of_isConstructibleModuleSheaf'` — **Stacks 09YV** for
  sheaves of modules, with both of its hypotheses discharged, for such a ring.

## Implementation notes

The instance hypotheses — existence of the inverse image along a base change of small étale
sites, and sheafification over the slices — are assumed at `R` only and *derived* at
`Shrink.{u + 1} R`, by
`CategoryTheory.Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence` and
`CategoryTheory.Sheaf.hasWeakSheafify_of_coefficientEquivalence`. Assuming them again at the
shrunk ring would be a hypothesis no consumer can discharge.

Transporting essential constancy of an ind-object is the only step that is not a restatement of
the transport of constructibility: the cocone is carried by the equivalence, which preserves the
colimit, and the retraction found upstairs is brought back as its preimage under the fully
faithful functor. Both clauses of `EssentiallyConstantInd.IsEssentiallyConstantWith` are
equations between morphisms, so faithfulness is all that is used.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 095P](https://stacks.math.columbia.edu/tag/095P)
* [Stacks Project, Tag 09YV](https://stacks.math.columbia.edu/tag/09YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r w v v₀

namespace ModuleCat

/-- Modules over `R` are the same thing as modules over `Shrink R`, by restriction of scalars
along `Shrink.ringEquiv`. The module universe is unconstrained by the universe the ring is
shrunk to, which is the point: it lets a statement about a ring in one universe be read at a
ring in another. -/
public abbrev restrictScalarsShrinkEquivalence.{ur, us, uw} (R : Type ur) [Ring R]
    [Small.{us} R] : ModuleCat.{uw} R ≌ ModuleCat.{uw} (Shrink.{us} R) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (Shrink.ringEquiv R)

end ModuleCat

namespace CategoryTheory.EssentiallyConstantInd

/-- Essential constancy of an ind-object is carried back along an equivalence. If the image
diagram is essentially constant with respect to the image cocone, witnessed by `r`, then the
original diagram is essentially constant with respect to the original cocone, witnessed by the
preimage of `r`.

Both clauses are equations between morphisms, so the faithfulness of the equivalence is all
that is used; the cocone components of the image cocone are the images of the originals. -/
public theorem IsEssentiallyConstantWith.of_equivalence {C : Type u} [Category.{r} C]
    {D : Type w} [Category.{v} D] (E : C ≌ D) {J : Type v₀} [Category J]
    (M : J ⥤ C) (t : Cocone M) (i : J)
    (s : (E.functor.mapCocone t).pt ⟶ (M ⋙ E.functor).obj i)
    (h : IsEssentiallyConstantWith (M ⋙ E.functor) (E.functor.mapCocone t) i s) :
    IsEssentiallyConstantWith M t i (E.functor.preimage s) where
  retraction := by
    refine E.functor.map_injective ?_
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_id]
    exact h.retraction
  cofinal j := by
    obtain ⟨k, σ, τ, hkτ⟩ := h.cofinal j
    refine ⟨k, σ, τ, E.functor.map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage]
    exact hkτ

end CategoryTheory.EssentiallyConstantInd

namespace AlgebraicGeometry

/-- A ring shrunk to a smaller universe is Noetherian if it was. -/
public instance isNoetherianRing_shrink (R : Type r) [CommRing R] [Small.{w} R]
    [IsNoetherianRing R] : IsNoetherianRing (Shrink.{w} R) :=
  isNoetherianRing_of_ringEquiv R (Shrink.ringEquiv R).symm

variable (B : BigEtaleSite.{u}) (R : Type r) [CommRing R] [Small.{u + 1} R]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} R)]

omit [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V) (ModuleCat.{u + 1} R)] in
/-- The inverse image along a base change of small étale sites exists for sheaves of
`Shrink R`-modules as soon as it exists for sheaves of `R`-modules: the two coefficient
categories are equivalent. -/
public theorem isRightAdjoint_sheafPushforwardContinuous_shrink (S T : B.Scheme) (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (Shrink.{u + 1} R))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint :=
  Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence _ _ _
    (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R)

omit [∀ (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint] in
/-- Presheaves of `Shrink R`-modules over a slice of the small étale site have a sheafification
as soon as presheaves of `R`-modules do. -/
public theorem hasWeakSheafify_over_shrink (T : B.Scheme) (V : SmallEtale B T.1 T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (Shrink.{u + 1} R)) :=
  Sheaf.hasWeakSheafify_of_coefficientEquivalence _
    (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R)

attribute [local instance 2000] isRightAdjoint_sheafPushforwardContinuous_shrink
  hasWeakSheafify_over_shrink

variable (X : B.Scheme)

/-- The equivalence between sheaves of `R`-modules and sheaves of `Shrink R`-modules on the small
étale site of `X`, induced by restriction of scalars along `Shrink.ringEquiv`. -/
public abbrev SmallEtale.sheafShrinkEquivalence :
    Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) ≌
      Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} (Shrink.{u + 1} R)) :=
  Sheaf.coefficientEquivalence (SmallEtale.topology B X.1 X.property)
    (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R)

/-- Constructibility is carried from a sheaf of `R`-modules to the associated sheaf of
`Shrink R`-modules. The same constructible stratification works; only the coefficient
translation has to be pushed past restriction to a stratum. -/
public theorem isConstructibleModuleSheaf_shrink [IsNoetherianRing R]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    IsConstructibleModuleSheaf B X (Shrink.{u + 1} R)
      ((SmallEtale.sheafShrinkEquivalence B R X).functor.obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence _
    (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R)
    (fun M => ModuleCat.isFG R M) (fun M hM => ?_) _ (hs i) _ ?_
  · have := (ModuleCat.isFG_iff M).1 hM
    exact (ModuleCat.isFG_iff _).2
      (ModuleCat.moduleFinite_restrictScalars_of_ringEquiv (Shrink.ringEquiv R) M)
  · exact (Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
      (SmallEtale.topology B X.1 X.property)
      (SmallEtale.topology B (s.piece i).1 (s.piece i).property)
      (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R)).app F

/-- Constructibility descends from the associated sheaf of `Shrink R`-modules back to the sheaf
of `R`-modules, by the same argument at the inverse equivalence. -/
public theorem isConstructibleModuleSheaf_of_shrink [IsNoetherianRing R]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B X (Shrink.{u + 1} R)
      ((SmallEtale.sheafShrinkEquivalence B R X).functor.obj F)) :
    IsConstructibleModuleSheaf B X R F := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i => ?_⟩
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_coefficientEquivalence _
    (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R).symm
    (fun M => ModuleCat.isFG (Shrink.{u + 1} R) M) (fun M hM => ?_) _ (hs i) _ ?_
  · have := (ModuleCat.isFG_iff M).1 hM
    exact (ModuleCat.isFG_iff _).2
      (ModuleCat.moduleFinite_restrictScalars_of_ringEquiv (Shrink.ringEquiv R).symm M)
  · refine (sheafCompose _
      (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R).inverse).mapIso
        ((Sheaf.sheafPullbackCoefficientIso (smallEtaleBaseChange B (s.inclusion i))
          (SmallEtale.topology B X.1 X.property)
          (SmallEtale.topology B (s.piece i).1 (s.piece i).property)
          (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R)).app F).symm ≪≫ ?_
    exact ((Sheaf.coefficientEquivalence _
      (ModuleCat.restrictScalarsShrinkEquivalence.{r, u + 1, u + 1} R)).unitIso.app _).symm

/-- **Stacks 09BH, part (3), subsheaves, for a coefficient ring in any universe.** A subsheaf of
a constructible sheaf of `R`-modules on the small étale site of a Noetherian scheme is
constructible.

`AlgebraicGeometry.isConstructibleModuleSheaf_of_mono` proves this for a ring in `Type (u + 1)`.
Here `R` need only be small in that universe: the statement is read at `Shrink.{u + 1} R`, a
Noetherian ring in `Type (u + 1)`, and transported back. The equivalence of sheaf categories
preserves monomorphisms, so the subsheaf upstairs is one. -/
@[stacks 09BH "part (3), subsheaf, for a Noetherian coefficient ring in any universe"]
public theorem isConstructibleModuleSheaf_of_mono' [IsNoetherian X.obj] [IsNoetherianRing R]
    {G F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)}
    (i : G ⟶ F) [Mono i] (hF : IsConstructibleModuleSheaf B X R F) :
    IsConstructibleModuleSheaf B X R G :=
  isConstructibleModuleSheaf_of_shrink B R X G
    (isConstructibleModuleSheaf_of_mono B X (Shrink.{u + 1} R)
      ((SmallEtale.sheafShrinkEquivalence B R X).functor.map i)
      (isConstructibleModuleSheaf_shrink B R X F hF))

/-- **Stacks 09BH, part (3), quotient sheaves, for a coefficient ring in any universe.** A
quotient of a constructible sheaf of `R`-modules on the small étale site of a Noetherian scheme
is constructible. This is `AlgebraicGeometry.isConstructibleModuleSheaf_of_epi` transported along
the same equivalence, which preserves epimorphisms. -/
@[stacks 09BH "part (3), quotient sheaf, for a Noetherian coefficient ring in any universe"]
public theorem isConstructibleModuleSheaf_of_epi' [IsNoetherian X.obj] [IsNoetherianRing R]
    {G Q : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)}
    (p : G ⟶ Q) [Epi p] (hG : IsConstructibleModuleSheaf B X R G) :
    IsConstructibleModuleSheaf B X R Q :=
  isConstructibleModuleSheaf_of_shrink B R X Q
    (isConstructibleModuleSheaf_of_epi B X (Shrink.{u + 1} R)
      ((SmallEtale.sheafShrinkEquivalence B R X).functor.map p)
      (isConstructibleModuleSheaf_shrink B R X G hG))

/-- **The constructible sheaves of `R`-modules form a strong Serre subcategory, for a coefficient
ring small in the coefficient universe.** This is
`AlgebraicGeometry.isSerreClass_isConstructibleModuleSheaf` read at a Noetherian ring `R` that
need only be small in `Type (u + 1)`.

Constructibility of a sheaf of `R`-modules is constructibility of the associated sheaf of
`Shrink R`-modules, by `AlgebraicGeometry.isConstructibleModuleSheaf_shrink` and
`AlgebraicGeometry.isConstructibleModuleSheaf_of_shrink`, so the class is the inverse image of the
class at `Shrink.{u + 1} R` along the equivalence of sheaf categories; an equivalence is exact,
and the inverse image of a Serre class along an exact functor is a Serre class. -/
public theorem isSerreClass_isConstructibleModuleSheaf_of_small [IsNoetherian X.obj]
    [IsNoetherianRing R]
    [HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)] :
    ObjectProperty.IsSerreClass
      (fun F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) =>
        IsConstructibleModuleSheaf B X R F) := by
  have hP : (fun F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R) =>
        IsConstructibleModuleSheaf B X R F) =
      ObjectProperty.inverseImage
        (fun F : Sheaf (SmallEtale.topology B X.1 X.property)
            (ModuleCat.{u + 1} (Shrink.{u + 1} R)) =>
          IsConstructibleModuleSheaf B X (Shrink.{u + 1} R) F)
        (SmallEtale.sheafShrinkEquivalence B R X).functor := by
    funext F
    exact propext ⟨isConstructibleModuleSheaf_shrink B R X F,
      isConstructibleModuleSheaf_of_shrink B R X F⟩
  have := isSerreClass_isConstructibleModuleSheaf B X (Shrink.{u + 1} R)
  rw [hP]
  infer_instance

/-- **Stacks 095P, part (3), for a coefficient ring in any universe.** A filtered colimit of
constructible sheaves of `R`-modules whose value is constructible is essentially constant as an
ind-object.

The cocone is carried to `Shrink.{u + 1} R`-modules by the equivalence of sheaf categories,
which preserves the colimit, and the witness found there is brought back by
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith.of_equivalence`. -/
@[stacks 095P "part (3), for a Noetherian coefficient ring in any universe"]
public theorem exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit'
    [IsNoetherianRing R] [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    {I : Type v} [Category.{v₀} I] [IsFiltered I] [EssentiallySmall.{u + 1} I]
    (F : I ⥤ Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (t : Cocone F) (ht : IsColimit t)
    (hF : ∀ i, IsConstructibleModuleSheaf B X R (F.obj i))
    (hcolim : IsConstructibleModuleSheaf B X R t.pt) :
    ∃ (i : I) (r : t.pt ⟶ F.obj i),
      EssentiallyConstantInd.IsEssentiallyConstantWith F t i r := by
  let E := SmallEtale.sheafShrinkEquivalence B R X
  let _ : PreservesColimit F E.functor :=
    E.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  obtain ⟨i, s, hs⟩ := exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit
    B X (Shrink.{u + 1} R) (F ⋙ E.functor) (E.functor.mapCocone t)
    (isColimitOfPreserves E.functor ht)
    (fun i => isConstructibleModuleSheaf_shrink B R X (F.obj i) (hF i))
    (isConstructibleModuleSheaf_shrink B R X t.pt hcolim)
  exact ⟨i, _, hs.of_equivalence (SmallEtale.sheafShrinkEquivalence B R X) F t i s⟩

/-- **Stacks 09YV for sheaves of modules, with nothing granted and the coefficient ring in any
universe.** On a Noetherian scheme, over a Noetherian ring, every ascending chain of subsheaves
of a constructible sheaf of `R`-modules stabilizes.

`AlgebraicGeometry.isNoetherianObject_of_isConstructibleModuleSheaf` carries Stacks 09BH and
Stacks 095P as the explicit hypotheses `hsub` and `hess`. Both are available above at a
coefficient ring in any universe, so they are supplied here and nothing is granted. The
quasi-compactness and quasi-separatedness that Stacks 095P asks of `X` follow from its being
Noetherian. -/
@[stacks 09YV "sheaves of modules over a Noetherian ring in any universe, with Stacks 09BH and \
Stacks 095P discharged", sga "4 IX 2.10"]
public theorem isNoetherianObject_of_isConstructibleModuleSheaf' [IsNoetherian X.obj]
    [IsNoetherianRing R]
    [HasSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    IsNoetherianObject F := by
  have hN := (AlgebraicGeometry.isNoetherian_iff X.obj).mp (inferInstance : IsNoetherian X.obj)
  let _ : CompactSpace X.1 := hN.2
  let _ : IsLocallyNoetherian X.1 := hN.1
  let _ : QuasiSeparatedSpace X.1 := IsLocallyNoetherian.quasiSeparatedSpace
  refine isNoetherianObject_of_isConstructibleModuleSheaf B X R (fun {_ _} i hi hH => ?_)
    (fun M c hc hM hc' =>
      exists_isEssentiallyConstantWith_of_isConstructibleModuleSheaf_colimit' B R X M c hc hM hc')
    F hF
  have := hi
  exact isConstructibleModuleSheaf_of_mono' B R X i hH

end AlgebraicGeometry

end
