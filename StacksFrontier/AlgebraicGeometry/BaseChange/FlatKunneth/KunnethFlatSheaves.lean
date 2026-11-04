module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.GlobalCupProductAffine
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.KunnethChain
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatKunneth.TorVanishing
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ProjectionFormulaInterchanged
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeAffineBaseCoherence
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethSchemeTorIndependent
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethBaseChangeLeg
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0FU4]: the Künneth formula for two flat quasi-coherent modules

Let `S = Spec A` be affine, `a : X ⟶ S`, `b : Y ⟶ S` with `X`, `Y` quasi-compact with affine
diagonal, and `ℱ` on `X`, `𝒢` on `Y` quasi-coherent and flat over `S`.  [Stacks, Tag 0FU4]
asserts that the Künneth map of [Stacks, Tag 0G49]

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(X ×_S Y, p^*ℱ ⊗_{𝒪_{X ×_S Y}} q^*𝒢)`

is an isomorphism.  This file proves it, at the canonical map
`Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheavesSchemeCanonical`, with nothing carried.

## The proof

The map is, by definition, the global cup product `μ` on the base at `(Ra_*ℱ, Rb_*𝒢)` followed by
derived global sections of the relative Künneth map of [Stacks, Tag 0FLP] at `ℱ[0]`, `𝒢[0]` and
of the comparison `Lp^*ℱ ⊗^𝐋 Lq^*𝒢 ⟶ p^*ℱ ⊗ q^*𝒢`.  `μ` is invertible because `S` is affine.  The
relative Künneth map is the chain of the projection formula at `a`, of the base-change map
`La^*Rb_*𝒢 ⟶ Rp_*Lq^*𝒢` and of the projection formula at `p`.  When `X` and `Y` are not Tor
independent over `S` the base-change map is not invertible, and neither is the comparison; but
moving the factor `Lq^*𝒢 ⟶ q^*𝒢` of the comparison into the chain, past the projection formula at
`p`, turns the base-change map into `La^*Rb_*𝒢 ⟶ Rp_*(q^*𝒢)`, which is invertible because `𝒢` is
flat over `S` ([Stacks, Tag 0A1D]), and leaves `Lp^*ℱ ⊗^𝐋 q^*𝒢 ⟶ p^*ℱ ⊗ q^*𝒢`, which is invertible
because `p^*(-) ⊗ q^*𝒢` is exact ([Stacks, Tag 0GMU]).

The source proves the tag instead by computing both sides with Čech complexes of finite affine
coverings; that route needs the identification of the map of [Stacks, Tag 0G49] with the Čech cup
product, which the derived route above does not.  As a consequence only one of the two modules
needs to be flat; the registered statement keeps the source's two flatness hypotheses.

## Main results

* `AlgebraicGeometry.FlatKunneth.isIso_kunnethMapOfSheavesCanonical_of`: the Künneth map on a
  commuting square of ringed spaces is invertible granted its five inputs.
* `AlgebraicGeometry.FlatKunneth.isIso_kunnethMapOfSheavesSchemeCanonical_of_isFlatOver`: the
  statement for quasi-compact quasi-separated `a`, `b`, an affine base and one flat module.
* `AlgebraicGeometry.FlatKunneth.isIso_kunnethMapOfSheavesSchemeCanonical_of_affineDiagonal`:
  **[Stacks, Tag 0FU4]**, at the source's hypotheses.

## References

* [Stacks Project, Tag 0FU4](https://stacks.math.columbia.edu/tag/0FU4)
* [Stacks Project, Tag 0G49](https://stacks.math.columbia.edu/tag/0G49)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedKunneth (adjunctionTensorMapRight kunnethMap kunnethBaseChangeLeg)
open scoped CategoryTheory.Prod

universe u

namespace AlgebraicGeometry.FlatKunneth

attribute [local instance 100000] HasDerivedCategory.standard

section RingedSpaces

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (hq : q ≫ b = p ≫ a)

/-- **The relative form of [Stacks, Tag 0FU4]**, from its four inputs: the relative Künneth map
of [Stacks, Tag 0FLP] at `ℱ[0]` and `𝒢[0]`, followed by `R(p ≫ a)_*` of the derived-to-ordinary
comparison `Lp^*ℱ[0] ⊗^𝐋 Lq^*𝒢[0] ⟶ (p^*ℱ ⊗ q^*𝒢)[0]`, is invertible as soon as the projection
formula at `a` (`h1`), the base-change leg followed by the comparison `Lq^*𝒢[0] ⟶ (q^*𝒢)[0]`
(`h2`), the interchanged-order projection formula at `p` (`h3`), and the Tor-vanishing comparison
`Lp^*ℱ[0] ⊗^𝐋 (q^*𝒢)[0] ⟶ Tot((p^*ℱ)[0] ⊗ (q^*𝒢)[0])` (`h4`) are.  Neither the base-change leg
nor the comparison is assumed invertible on its own. -/
theorem isIso_kunnethMap_comp_externalTensorComparison
    (F : Modules X.sheaf) (G : Modules Y.sheaf)
    (h1 : IsIso (CategoryTheory.adjunctionTensorMap (derivedAdjunction a)
          (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
          (pullbackTensorComparison a) (singleD F) ((derivedPushforward b).obj (singleD G))))
    (h2 : IsIso (kunnethBaseChangeLeg a b p q hq (singleD G) ≫
      (derivedPushforward p).map (pullbackSingleComparison q G)))
    (h3 : IsIso (adjunctionTensorMapRight (derivedAdjunction p)
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
          (pullbackTensorComparison p) (singleD F) (singleD ((modulePullback q).obj G))))
    (h4 : IsIso (((derivedTensorProductFunctor W.sheaf).map (pullbackSingleComparison p F)).app
        (singleD ((modulePullback q).obj G)) ≫
      (canonicalDerivedTensorProduct W.sheaf).toTensor
        (singleC ((modulePullback p).obj F)) (singleC ((modulePullback q).obj G)))) :
    IsIso (kunnethMap a b p q (p ≫ a) rfl hq (singleD F) (singleD G) ≫
      (derivedPushforward (p ≫ a)).map (externalTensorComparison p q F G)) := by
  have hk := isIso_kunnethMap_comp_tensorMap a b p q hq (singleD F) (singleD G)
    (pullbackSingleComparison q G) h1 h2 h3
  rw [externalTensorComparison_eq]
  refine isIso_comp_map_bifunctor_comp (derivedPushforward (p ≫ a))
    (derivedTensorProductFunctor W.sheaf) _ _ _ _ _ hk h4 ?_
  exact @Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _)

/-- **The Künneth map for two module sheaves of [Stacks, Tag 0G49] is invertible**, at the
canonical global cup product and on a commuting square of ringed spaces, as soon as the global
cup product is invertible at `(Ra_*ℱ[0], Rb_*𝒢[0])` and the four inputs of
`isIso_kunnethMap_comp_externalTensorComparison` hold.  At the fibre product of two schemes all
five are proved: see `isIso_kunnethMapOfSheavesSchemeCanonical_of_isFlatOver`. -/
theorem isIso_kunnethMapOfSheavesCanonical_of
    (F : Modules X.sheaf) (G : Modules Y.sheaf)
    (hκ : IsIso ((globalCupProductCanonical S).app
      ((derivedPushforward a).obj (singleD F), (derivedPushforward b).obj (singleD G))))
    (h1 : IsIso (CategoryTheory.adjunctionTensorMap (derivedAdjunction a)
          (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
          (pullbackTensorComparison a) (singleD F) ((derivedPushforward b).obj (singleD G))))
    (h2 : IsIso (kunnethBaseChangeLeg a b p q hq (singleD G) ≫
      (derivedPushforward p).map (pullbackSingleComparison q G)))
    (h3 : IsIso (adjunctionTensorMapRight (derivedAdjunction p)
          (Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
          (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
          (pullbackTensorComparison p) (singleD F) (singleD ((modulePullback q).obj G))))
    (h4 : IsIso (((derivedTensorProductFunctor W.sheaf).map (pullbackSingleComparison p F)).app
        (singleD ((modulePullback q).obj G)) ≫
      (canonicalDerivedTensorProduct W.sheaf).toTensor
        (singleC ((modulePullback p).obj F)) (singleC ((modulePullback q).obj G)))) :
    IsIso (kunnethMapOfSheavesCanonical a b p q (p ≫ a) rfl hq F G) := by
  have hA : IsIso ((Functor.uncurry.obj (tensorBase S)).map
      ((lerayIso a).inv.app (singleD F) ×ₘ (lerayIso b).inv.app (singleD G))) :=
    ((Functor.uncurry.obj (tensorBase S)).mapIso
      (Iso.prod ((lerayIso a).app (singleD F)).symm
        ((lerayIso b).app (singleD G)).symm)).isIso_hom
  exact isIso_comp_natIso_map _ _ _ (lerayIso (p ≫ a)) _ _ _ (externalTensorComparison p q F G)
    hA hκ (isIso_kunnethMap_comp_externalTensorComparison a b p q hq F G h1 h2 h3 h4)

end RingedSpaces

section Schemes

/-- A quasi-coherent module placed in degree zero has quasi-coherent cohomology sheaves. -/
lemma isQCohAll_singleD {W : Scheme.{u}} (M : W.Modules) (hM : M.IsQuasicoherent) :
    IsQCohAll (singleD M) := by
  intro j
  have e := (DerivedCategory.homologyFunctorFactors W.Modules j).app
    ((HomologicalComplex.single W.Modules (ComplexShape.up ℤ) 0).obj M)
  by_cases h0 : j = 0
  · subst h0
    exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
      (e ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _).symm hM
  · have := isFinitePresentation_of_isZero
      ((HomologicalComplex.homologyFunctor W.Modules (ComplexShape.up ℤ) j).obj
        ((HomologicalComplex.single W.Modules (ComplexShape.up ℤ) 0).obj M))
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M j h0)
    exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso e.symm
      (isQuasicoherent_of_isFinitePresentation _)

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- **[Stacks, Tag 0FU4], in the generality its proof gives.**  Let `a : X ⟶ S` and `b : Y ⟶ S` be
quasi-compact and quasi-separated morphisms of schemes with `S` affine, `A = Γ(S, 𝒪_S)`, and let
`ℱ` on `X` and `𝒢` on `Y` be quasi-coherent with `𝒢` flat over `S`.  Then the Künneth map of
[Stacks, Tag 0G49]

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(X ×_S Y, p^*ℱ ⊗ q^*𝒢)`

is an isomorphism in `D(A)`.  Flatness of one of the two modules suffices; `X` and `Y` need not be
Tor independent over `S`.

The proof is the one of [Stacks, Tag 0FLQ], with the base-change step replaced: the global map is
the global cup product on the base, invertible over an affine base
(`isIso_globalCupProductCanonical_app`), followed by derived global sections of the relative map,
which is the chain of the projection formula of [Stacks, Tag 08EU] at `a`, of base change
`La^*Rb_*𝒢 ⟶ Rp_*(q^*𝒢)` for the `S`-flat `𝒢`
(`isIso_derivedBaseChangeComp_single_of_isQuasicoherent`, [Stacks, Tag 0A1D]), of the
interchanged projection formula at `p`, and of the Tor vanishing
`Lp^*ℱ ⊗^𝐋 q^*𝒢 ≅ p^*ℱ ⊗ q^*𝒢` (`isIso_derivedTensor_pullbackSingleComparison_toTensor_fibre`,
[Stacks, Tag 0GMU]). -/
theorem isIso_kunnethMapOfSheavesSchemeCanonical_of_isFlatOver [IsAffine S]
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hG : IsFlatOver b.toLRSHom.toShHom G) :
    IsIso (kunnethMapOfSheavesSchemeCanonical a b F G) := by
  have hF0 : IsQCohAll (singleD F) := isQCohAll_singleD F inferInstance
  have hG0 : IsQCohAll (singleD G) := isQCohAll_singleD G inferInstance
  have hqG : ((Scheme.Modules.pullback (pullback.snd a b)).obj G).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ G
  have hqG0 : IsQCohAll (singleD ((Scheme.Modules.pullback (pullback.snd a b)).obj G)) :=
    isQCohAll_singleD _ hqG
  -- the projection formula of Tag 08EU at `a`
  have h1 := isIso_adjunctionTensorMap_of_quasicoherent a (singleD F) hF0
    ((derivedPushforward b.toLRSHom.toShHom).obj (singleD G))
    (Stacks.Cohomology.DerivedKunneth.isQCohAll_derivedPushforward b hG0)
  -- the interchanged projection formula at `p`
  have h3 := isIso_adjunctionTensorMapRight_of_quasicoherent (pullback.fst a b) inferInstance
    inferInstance (singleD ((Scheme.Modules.pullback (pullback.snd a b)).obj G)) (singleD F)
    hqG0 hF0
  -- base change for the `S`-flat `𝒢`, with the ordinary pullback on the right
  have h2 : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg a.toLRSHom.toShHom
      b.toLRSHom.toShHom (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (toShHom_pullback_condition a b) (singleD G) ≫
      (derivedPushforward (pullback.fst a b).toLRSHom.toShHom).map
        (pullbackSingleComparison (pullback.snd a b).toLRSHom.toShHom G)) := by
    have hbc := isIso_derivedBaseChangeComp_single_of_isQuasicoherent b a (pullback.fst a b)
      (pullback.snd a b) (IsPullback.of_hasPullback a b).flip G hG
    exact isIso_comp_map_of_eq (derivedPushforward (pullback.fst a b).toLRSHom.toShHom) _ _
      (Stacks.Cohomology.DerivedKunneth.kunnethBaseChangeLeg_eq_derivedBaseChangeMap _ _ _ _ _ _)
      (pullbackSingleComparison_eq (pullback.snd a b).toLRSHom.toShHom G) hbc
      (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        (modulePullback (pullback.snd a b).toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app
          G)).isIso_hom
  -- Tor vanishing against `q^*𝒢`
  have : SheafOfModules.IsQuasicoherent
      (show SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) from G) :=
    inferInstanceAs G.IsQuasicoherent
  have h4 := isIso_derivedTensor_pullbackSingleComparison_toTensor_fibre a b G hG F
  -- the global cup product over the affine base
  have hκ := isIso_globalCupProductCanonical_app S _ _
    (Stacks.Cohomology.DerivedKunneth.isQCohAll_derivedPushforward a hF0)
    (Stacks.Cohomology.DerivedKunneth.isQCohAll_derivedPushforward b hG0)
  exact isIso_kunnethMapOfSheavesCanonical_of a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (toShHom_pullback_condition a b) F G hκ h1 h2 h3 h4


/-- **[Stacks, Tag 0FU4].**  Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes with `S`
affine, let `A = Γ(S, 𝒪_S)`, and let `p`, `q` be the projections of `X ×_S Y`.  If `ℱ` on `X` and
`𝒢` on `Y` are `S`-flat and quasi-coherent and `X` and `Y` are quasi-compact with affine
diagonal, then the Künneth map of [Stacks, Tag 0G49]

`RΓ(X, ℱ) ⊗^𝐋_A RΓ(Y, 𝒢) ⟶ RΓ(X ×_S Y, p^*ℱ ⊗_{𝒪_{X ×_S Y}} q^*𝒢)`

is an isomorphism in `D(A)`.  The map is
`Stacks.Cohomology.GlobalKunneth.kunnethMapOfSheavesSchemeCanonical`, built from the global cup
product of Cohomology, Section 0FKU with no parameter.

Nothing is carried.  Quasi-compactness and affineness of the diagonals give the
quasi-compactness and quasi-separatedness of `a` and `b`; affineness of `S`, flatness of `𝒢` and
quasi-coherence of `ℱ` and `𝒢` are consumed by
`isIso_kunnethMapOfSheavesSchemeCanonical_of_isFlatOver`, which this specializes.  Flatness of
`ℱ` is the tag's hypothesis but the proof does not need it: one flat factor suffices, by the
Tor vanishing of [Stacks, Tag 0GMU]. -/
@[stacks 0FU4]
theorem isIso_kunnethMapOfSheavesSchemeCanonical_of_affineDiagonal [IsAffine S] [CompactSpace X]
    [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (_hF : IsFlatOver a.toLRSHom.toShHom F) (hG : IsFlatOver b.toLRSHom.toShHom G) :
    IsIso (kunnethMapOfSheavesSchemeCanonical a b F G) := by
  have : QuasiSeparatedSpace X := (quasiSeparatedSpace_iff_quasiSeparated X).2 ⟨inferInstance⟩
  have : QuasiSeparatedSpace Y := (quasiSeparatedSpace_iff_quasiSeparated Y).2 ⟨inferInstance⟩
  exact isIso_kunnethMapOfSheavesSchemeCanonical_of_isFlatOver a b F G hG

end Schemes

end AlgebraicGeometry.FlatKunneth

end
