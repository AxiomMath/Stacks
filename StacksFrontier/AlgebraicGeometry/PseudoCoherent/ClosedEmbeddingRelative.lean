module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ReductionClosedPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative pseudo-coherence along a homeomorphism onto a closed subset

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes locally of finite type and let
`i : X ⟶ Y` be a morphism over `S` which induces a homeomorphism of `X` with a closed subset of
`Y`. If `𝒪_X` is pseudo-coherent relative to `S` and `i_*𝒪_X` is pseudo-coherent relative to `S`,
then an object `E` of `D(𝒪_X)` is `m`-pseudo-coherent relative to `S` if and only if `Ri_*E` is,
for every integer `m`.

## Main results

* `AlgebraicGeometry.exists_isClosedImmersion_isPseudoCoherent_pushforward_restrict`: for a module
  which is pseudo-coherent relative to `S`, every compatible pair of affine opens carries a chart
  along which its restriction has a pseudo-coherent pushforward.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPushforward_unit_iff`: for a closed
  embedding on spaces, relative pseudo-coherence of `Ri_*𝒪_X` is that of `i_*𝒪_X`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_isClosedEmbedding`:
  `E` is `m`-pseudo-coherent relative to `S` if and only if `Ri_*E` is, provided `𝒪_X` and
  `i_*𝒪_X` are pseudo-coherent relative to `S`.

## Implementation notes

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.6 (09VG)](https://stacks.math.columbia.edu/tag/09VG)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Pushing a restricted module in degree zero forward along a chart -/

/-- **Restricting a module to an open, placing it in degree zero and pushing it forward along a
morphism with exact pushforward is the module obtained by doing all of that before passing to
derived categories.** -/
public def Scheme.Modules.pushforwardRestrictSingleIso {X P : Scheme.{u}} (W : X.Opens)
    (a : W.toScheme ⟶ P) [PreservesFiniteColimits (Scheme.Modules.pushforward a)]
    (M : X.Modules) :
    (Scheme.Modules.pushforward a).mapDerivedCategory.obj
        ((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M)) ≅
      (DerivedCategory.singleFunctor P.Modules 0).obj
        ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.restrictFunctor W.ι).obj M)) :=
  (Scheme.Modules.pushforward a).mapDerivedCategory.mapIso
      (((Scheme.Modules.restrictFunctor W.ι).mapDerivedCategorySingleFunctor 0).app M) ≪≫
    ((Scheme.Modules.pushforward a).mapDerivedCategorySingleFunctor 0).app _

/-! ### A chart for a relatively pseudo-coherent module -/

/-- **A module which is pseudo-coherent relative to `S` has, over every compatible pair of affine
opens, a chart along which its restriction becomes a pseudo-coherent module.** For
`f : X ⟶ S` locally of finite type, `M` a sheaf of `𝒪_X`-modules pseudo-coherent relative to `S`
and `U ⊆ f⁻¹V` a compatible pair of affine opens, there is a closed immersion
`a : U ⟶ 𝔸ᵏ_V` over `V` such that `a_*(M|_U)`, placed in degree zero, is a pseudo-coherent object
of `D(𝒪_{𝔸ᵏ_V})`. -/
public theorem exists_isClosedImmersion_isPseudoCoherent_pushforward_restrict {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (M : X.Modules)
    (hM : Scheme.Hom.IsModulePseudoCoherent f M)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ (k : ℕ) (a : (U.1 : Scheme.{u}) ⟶ AffineSpace (ULift.{u} (Fin k)) (V.1 : Scheme.{u})),
      IsClosedImmersion a ∧
      a ≫ (AffineSpace.over (ULift.{u} (Fin k)) (V.1 : Scheme.{u})).hom =
        f.resLE V.1 U.1 hUV ∧
      RingedSpace.IsPseudoCoherent
        (X := (AffineSpace (ULift.{u} (Fin k)) (V.1 : Scheme.{u})).toRingedSpace)
        ((DerivedCategory.singleFunctor
            (AffineSpace (ULift.{u} (Fin k)) (V.1 : Scheme.{u})).Modules 0).obj
          ((Scheme.Modules.pushforward a).obj
            ((Scheme.Modules.restrictFunctor U.1.ι).obj M))) := by
  obtain ⟨k, a, ha, hao⟩ := exists_isClosedImmersion_affineSpace_resLE f V U hUV
  refine ⟨k, a, ha, hao, RingedSpace.isPseudoCoherent_of_forall.{u} _ fun m => ?_⟩
  have h := Scheme.Hom.IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion f
    (Scheme.Hom.isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f
      (hM m) U V hUV) k a ha hao
  rw [Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff_of_exact] at h
  exact h.of_iso (Scheme.Modules.pushforwardRestrictSingleIso U.1 a M)

/-! ### The derived pushforward of the structure sheaf -/

/-- **For a morphism which is a closed embedding on spaces, `Ri_*𝒪_X` is `i_*𝒪_X` placed in degree
zero.** So relative `m`-pseudo-coherence of `Ri_*𝒪_X` is relative `m`-pseudo-coherence of the
sheaf of modules `i_*𝒪_X`. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_derivedPushforward_unit_iff
    {X Y S : Scheme.{u}} (g : Y ⟶ S) [LocallyOfFiniteType g] (i : X ⟶ Y)
    (hemb : Topology.IsClosedEmbedding i.base) (m : ℤ) :
    Scheme.Hom.IsPseudoCoherentFrom g
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            i.toLRSHom.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (SheafOfModules.unit X.ringCatSheaf))) m ↔
      Scheme.Hom.IsModulePseudoCoherentFrom g
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf)) m := by
  have hcol' : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePushforward i.toLRSHom.toShHom) :=
    Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward i.toLRSHom.toShHom hemb
  have hcol : PreservesFiniteColimits (Scheme.Modules.pushforward i) := hcol'
  have e := (Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
      i.toLRSHom.toShHom).app ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf)) ≪≫
    ((Scheme.Modules.pushforward i).mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit X.ringCatSheaf)
  exact ⟨fun h => Scheme.Hom.IsPseudoCoherentFrom.of_iso g h e,
    fun h => Scheme.Hom.IsPseudoCoherentFrom.of_iso g h e.symm⟩

/-! ### Stacks 09VG for an object whose structure sheaves are relatively pseudo-coherent -/

/-- Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes locally of finite type and let
`i : X ⟶ Y` be a morphism over `S` which induces a homeomorphism of `X` with a closed subset of
`Y`. Assume that `𝒪_X` is pseudo-coherent relative to `S` and that `i_*𝒪_X` is pseudo-coherent
relative to `S`. Then, for every object `E` of `D(𝒪_X)` and every integer `m`, `E` is
`m`-pseudo-coherent relative to `S` if and only if `Ri_*E` is. -/
@[sga "6 III 2.1" "closed embedding"]
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_isClosedEmbedding
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (i : X ⟶ Y) (hi : i ≫ g = f) (hemb : Topology.IsClosedEmbedding i.base)
    (hOX : Scheme.Hom.IsModulePseudoCoherent f (SheafOfModules.unit X.ringCatSheaf))
    (hOY : Scheme.Hom.IsModulePseudoCoherent g
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf)))
    (E : DerivedCategory X.Modules) (m : ℤ) :
    Scheme.Hom.IsPseudoCoherentFrom f E m ↔
      Scheme.Hom.IsPseudoCoherentFrom g
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i.toLRSHom.toShHom).obj E) m := by
  subst hi
  have : IsAffineHom i := isAffineHom_of_isInducing i hemb.isInducing hemb.isClosed_range
  have hcol : PreservesFiniteColimits (Scheme.Modules.pushforward i) :=
    Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward i.toLRSHom.toShHom hemb
  refine Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward_of_structureSheafCharts
    (i ≫ g) g i rfl hemb (fun U V hUV => ?_) (fun U V hUV => ?_) E m
  · obtain ⟨k, a, ha, hao, hpc⟩ := exists_isClosedImmersion_isPseudoCoherent_pushforward_restrict
      (i ≫ g) (SheafOfModules.unit X.ringCatSheaf) hOX ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ V
      ((Opens.map i.base).monotone hUV)
    exact ⟨k, a, ha, hao, hpc.of_iso <| (DerivedCategory.singleFunctor
        (AffineSpace (ULift.{u} (Fin k)) (V.1 : Scheme.{u})).Modules 0).mapIso
      ((Scheme.Modules.pushforward a).mapIso
        (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ U.1).ι))⟩
  · obtain ⟨n, b, hb, hbo, hpc⟩ := exists_isClosedImmersion_isPseudoCoherent_pushforward_restrict
      g ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf)) hOY U V hUV
    refine ⟨n, b, hb, hbo, hpc.of_iso <| (DerivedCategory.singleFunctor
        (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).Modules 0).mapIso ?_⟩
    exact (Scheme.Modules.pushforward b).mapIso
        ((Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso i U.1).app
            (SheafOfModules.unit X.ringCatSheaf) ≪≫
          (Scheme.Modules.pushforward (i ∣_ U.1)).mapIso
            (Scheme.Modules.restrictUnitIso (i ⁻¹ᵁ U.1).ι)) ≪≫
      (Scheme.Modules.pushforwardComp (i ∣_ U.1) b).app
        (SheafOfModules.unit (i ⁻¹ᵁ U.1).toScheme.ringCatSheaf)

end AlgebraicGeometry

end
