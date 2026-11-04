module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaPullbackComparisonCocycle
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafUnitIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaChartPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePullbackComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackKFlatComparison

/-!
# The derived comparison of décalages under pullback, at a presentation

Let `f : X ⟶ Y` be a morphism of ringed spaces, `I ⊆ 𝒪_Y` an invertible ideal sheaf whose
pullback `f^*I ⟶ 𝒪_X` is again an ideal, and `F^•` a complex of `I`-torsion-free modules whose
termwise pullback is `f^*I`-torsion-free. The comparison

`Lf^*[η_I F^•] ⟶ [f^*(η_I F^•)] ⟶ [η_{f^*I}(f^*F^•)]`

in `D(𝒪_X)` is the comparison of the left derived pullback with the degreewise pullback
(Stacks 06YJ) followed by the chain-level comparison of décalages. It is the part of the
comparison `Lf^*(Lη_I M) ⟶ Lη_{f^*I}(Lf^*M)` of Stacks 0F9X that is not an isomorphism for
formal reasons. This file proves that it is natural in the complex, that it is an isomorphism
for flat `f`, and that it satisfies a cocycle condition along a composite `p ≫ q`; the cocycle
condition is what lets the invertibility of the comparison be checked after restriction to the
members of open covers of the source and of the target.

## Main definitions

* `Stacks.IdealTorsion.Eta.derivedPullbackEtaCore`: the comparison
  `Lf^*[η_I F^•] ⟶ [η_{f^*I}(f^*F^•)]`.

## Main results

* `Stacks.IdealTorsion.Eta.derivedPullbackEtaCore_naturality`: naturality in the complex.
* `Stacks.IdealTorsion.Eta.isIso_derivedPullbackEtaCore_of_isFlat`: invertibility for flat `f`.
* `Stacks.IdealTorsion.Eta.derivedPullbackEtaCore_cocycle`: the cocycle condition
  `Lp^*(φ_q) ≫ φ_p = (Lq^* ⋙ Lp^* ≅ L(p ≫ q)^*) ≫ φ_{p ≫ q} ≫ (iso)`.
* `Stacks.IdealTorsion.Eta.isIso_derivedPullbackEtaCore_comp_iff_left` and
  `isIso_derivedPullbackEtaCore_comp_iff_right`: the two invertibility transfers it gives.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

/-- The quotient functor to the derived category of a ringed space, at the spelling
`structureSheafRing` of the structure sheaf in which the left derived pullback is written. -/
local notation "QR" W => DerivedCategory.Q (C := SheafOfModules (structureSheafRing W))

namespace Stacks.IdealTorsion.Eta

/-- The comparison of the left derived pullback with the degreewise pullback is invertible at
every complex when `f` is flat. -/
theorem isIso_derivedPullbackComplexComparison_app_of_isFlat {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (hf : AlgebraicGeometry.IsFlat f)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    IsIso ((Stacks.DerivedPullback.derivedPullbackComplexComparison f).app K) := by
  have := Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackComparison_app_of_isFlat
    f hf ((HomotopyCategory.quotient _ _).obj K)
  dsimp only [Stacks.DerivedPullback.derivedPullbackComplexComparison]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- Naturality of the comparison of the left derived pullback with the degreewise pullback, with
the derived pullback of a morphism of complexes written through `Q`. -/
private theorem derivedPullback_map_comparison_app {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ} (a : K ⟶ L) :
    (derivedPullback f).map ((QR Y).map a) ≫
        (Stacks.DerivedPullback.derivedPullbackComplexComparison f).app L =
      (Stacks.DerivedPullback.derivedPullbackComplexComparison f).app K ≫
        (QR X).map (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
  simpa only [Functor.comp_map] using
    (Stacks.DerivedPullback.derivedPullbackComplexComparison f).naturality a

section Core

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (pullbackIdealIncl f I ι)]

/-- **The comparison `Lf^*[η_I F^•] ⟶ [η_{f^*I}(f^*F^•)]`**: the comparison of the left derived
pullback with the degreewise pullback at `η_I F^•` (Stacks 06YJ), followed by the chain-level
comparison `Stacks.IdealTorsion.Eta.pullbackEtaMap` of décalages. No flatness is assumed. -/
def derivedPullbackEtaCore
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n)) :
    (derivedPullback f).obj ((QR Y).obj (etaObj Y I ι F hF)) ⟶
      (QR X).obj
        (etaObj X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F)
          hF') :=
  (Stacks.DerivedPullback.derivedPullbackComplexComparison f).app (etaObj Y I ι F hF) ≫
    (QR X).map (pullbackEtaMap f I ι F hF hF')

/-- The chain-level comparison of décalages is invertible once it is in every degree. -/
private theorem isIso_pullbackEtaMap_of_isIso_termMap
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (h : ∀ n : ℤ, IsIso (pullbackEtaTermMap f I ι F n)) :
    IsIso (pullbackEtaMap f I ι F hF hF') := by
  have : ∀ n : ℤ, IsIso ((pullbackEtaMap f I ι F hF hF').f n) := h
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **The comparison is natural in the complex.** -/
theorem derivedPullbackEtaCore_naturality
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Y ι (G.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hG' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f G).X n)) :
    (derivedPullback f).map ((QR Y).map (etaMap Y I ι a hF hG)) ≫
        derivedPullbackEtaCore f I ι G hG hG' =
      derivedPullbackEtaCore f I ι F hF hF' ≫
        (QR X).map (etaMap X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) hF' hG') := by
  rw [derivedPullbackEtaCore, derivedPullbackEtaCore,
    reassoc_of% derivedPullback_map_comparison_app f (etaMap Y I ι a hF hG), Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, pullbackEtaMap_naturality]

/-- **For a flat morphism the comparison is an isomorphism**: both of its constituents are. -/
theorem isIso_derivedPullbackEtaCore_of_isFlat (hf : AlgebraicGeometry.IsFlat f)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n)) :
    IsIso (derivedPullbackEtaCore f I ι F hF hF') := by
  have := isIso_derivedPullbackComplexComparison_app_of_isFlat f hf (etaObj Y I ι F hF)
  have := isIso_pullbackEtaMap f I ι F hF hF' hf
  rw [derivedPullbackEtaCore]
  infer_instance

/-- **The invertibility of the comparison does not depend on the presentation.** For a
quasi-isomorphism `a : F^• ⟶ G^•` between K-flat complexes of `I`-torsion-free modules whose
pullbacks are `f^*I`-torsion-free, the comparison at `F^•` is invertible exactly when the
comparison at `G^•` is: by naturality they differ by `Lf^*[η_I a]` and `[η_{f^*I}(f^*a)]`, which
are invertible by Stacks 0F8P. -/
theorem isIso_derivedPullbackEtaCore_iff_of_quasiIso
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (a : F ⟶ G)
    [QuasiIso a]
    (hFk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y F)
    (hGk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Y ι (G.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hG' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f G).X n)) :
    IsIso (derivedPullbackEtaCore f I ι F hF hF') ↔
      IsIso (derivedPullbackEtaCore f I ι G hG hG') := by
  have h := derivedPullbackEtaCore_naturality f I ι a hF hG hF' hG'
  have := quasiIso_etaMap Y I ι a hF hG inferInstance
  have : QuasiIso (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) :=
    quasiIso_pullbackComplex_map_of_kFlat f a hFk hGk
  have := quasiIso_etaMap X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
    (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) hF' hG' inferInstance
  exact ⟨fun _ => IsIso.of_isIso_fac_left h, fun _ => IsIso.of_isIso_fac_right h.symm⟩

/-- The invertibility of the comparison along a morphism depends only on the morphism, not on
how it is written: equal morphisms have comparisons that are invertible together. -/
theorem isIso_derivedPullbackEtaCore_congr {f' : X ⟶ Y} (e : f = f')
    [Mono (pullbackIdealIncl f' I ι)]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hF'' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f' I ι)
      ((pullbackComplex f' F).X n)) :
    IsIso (derivedPullbackEtaCore f I ι F hF hF') ↔
      IsIso (derivedPullbackEtaCore f' I ι F hF hF'') := by
  subst e
  rfl

/-- **The invertibility of the comparison depends only on the object of the derived category.**
Let `F^•` and `G^•` be K-flat complexes of `I`-torsion-free modules with `f^*I`-torsion-free
pullbacks, and suppose every flat module is `I`-torsion-free with `f^*I`-torsion-free pullback.
If `[F^•] ≅ [G^•]` in `D(𝒪_Y)`, the comparison at `F^•` is invertible exactly when the comparison
at `G^•` is. The isomorphism is a roof `F^• ⟵ P^• ⟶ G^•` of quasi-isomorphisms, and `P^•` may be
taken K-flat with flat terms (Stacks 06YF), so
`Stacks.IdealTorsion.Eta.isIso_derivedPullbackEtaCore_iff_of_quasiIso` applies to both legs. -/
theorem isIso_derivedPullbackEtaCore_iff_of_iso
    (htf : ∀ M : SheafOfModules.{u} (structureSheafRing Y),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) M →
        IsIdealTorsionFree Y ι M)
    (htf' : ∀ M : SheafOfModules.{u} (structureSheafRing Y),
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) M →
        IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackFunctor f).obj M))
    {F G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ}
    (hFk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y F)
    (hGk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Y ι (G.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hG' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f G).X n))
    (e : (QR Y).obj F ≅ (QR Y).obj G) :
    IsIso (derivedPullbackEtaCore f I ι F hF hF') ↔
      IsIso (derivedPullbackEtaCore f I ι G hG hG') := by
  obtain ⟨W, s, hs, g, hsg⟩ := DerivedCategory.right_fac e.hom
  obtain ⟨P, p, hPk, hPfl, hp, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y W
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hs
  have hg : IsIso ((QR Y).map g) := by
    have : (QR Y).map g = (QR Y).map s ≫ e.hom := by
      rw [hsg, IsIso.hom_inv_id_assoc]
    rw [this]
    infer_instance
  have hg' : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hg
  have hP : ∀ n : ℤ, IsIdealTorsionFree Y ι (P.X n) := fun n => htf _ (hPfl n)
  have hP' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f P).X n) := fun n => htf' _ (hPfl n)
  have hps : QuasiIso (p ≫ s) := inferInstance
  have hpg : QuasiIso (p ≫ g) := inferInstance
  rw [← isIso_derivedPullbackEtaCore_iff_of_quasiIso f I ι (p ≫ s) hPk hFk hP hF hP' hF',
    isIso_derivedPullbackEtaCore_iff_of_quasiIso f I ι (p ≫ g) hPk hGk hP hG hP' hG']

/-- **For the unit ideal the comparison is an isomorphism at every K-flat complex.** If the
inclusion `ι : I ⟶ 𝒪_Y` is invertible, the defining fibre products of `η_I F^•` have an invertible
leg, so every functor preserves them and the chain-level comparison is an isomorphism; and
`η_I F^• ≅ F^•`, so the comparison of `Lf^*` with the degreewise pullback is invertible at
`η_I F^•` as it is at the K-flat complex `F^•`. -/
theorem isIso_derivedPullbackEtaCore_of_isIso [IsIso ι]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hFk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y F)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n)) :
    IsIso (derivedPullbackEtaCore f I ι F hF hF') := by
  have hη : IsIso (pullbackEtaMap f I ι F hF hF') :=
    isIso_pullbackEtaMap_of_isIso_termMap f I ι F hF hF' fun n => by
      rw [isIso_pullbackEtaTermMap_iff]
      have := isIso_idealPowerIncl_of_isIso Y I ι n (F.X (n + 1))
      have h1 := pullbackComparison_comp_fst (pullbackFunctor f)
        (idealPowerMap Y I n (F.d n (n + 1))) (idealPowerIncl Y I ι n (F.X (n + 1)))
      rw [← IsIso.eq_comp_inv] at h1
      rw [h1]
      infer_instance
  have hc : IsIso ((Stacks.DerivedPullback.derivedPullbackComplexComparison f).app
      (etaObj Y I ι F hF)) := by
    have := Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat f F hFk
    exact IsIso.of_isIso_fac_right
      (derivedPullback_map_comparison_app f (etaObjIsoSelf Y I ι F hF).hom).symm
  rw [derivedPullbackEtaCore]
  infer_instance

/-- **A criterion for invertibility of the comparison.** If `η_I F^•` is K-flat and `f^*`
preserves, in every degree `n`, the fibre product defining the degree-`n` term of `η_I F^•`, then
the comparison is an isomorphism: the comparison of `Lf^*` with the degreewise pullback is
invertible at the K-flat complex `η_I F^•`, and the chain-level comparison is invertible in every
degree by `Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap_iff`. -/
theorem isIso_derivedPullbackEtaCore_of_kFlat_of_isIso_pullbackComparison
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))
    (hηk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y (etaObj Y I ι F hF))
    (hpc : ∀ n : ℤ, IsIso (pullbackComparison (pullbackFunctor f)
      (idealPowerMap Y I n (F.d n (n + 1))) (idealPowerIncl Y I ι n (F.X (n + 1))))) :
    IsIso (derivedPullbackEtaCore f I ι F hF hF') := by
  have := Stacks.DerivedPullback.isIso_derivedPullbackComplexComparison_app_of_kFlat f _ hηk
  have := isIso_pullbackEtaMap_of_isIso_termMap f I ι F hF hF' fun n =>
    (isIso_pullbackEtaTermMap_iff f I ι F n).2 (hpc n)
  rw [derivedPullbackEtaCore]
  infer_instance

/-- **The fibre products defining the décalage do not depend on the presentation of the
ideal.** For a compatible isomorphism `e : I ≅ J` of ideal sheaves (`e ≫ κ = ι`), a functor
preserves the fibre product defining the degree-`n` term of `η_I F^•` exactly when it preserves
the one defining the degree-`n` term of `η_J F^•`: the two cospans are isomorphic through the
transport `Stacks.IdealTorsion.Eta.IdealCongr.powerIso` of the ideal powers. -/
theorem isIso_pullbackComparison_idealCongr_iff {Z : RingedSpace.{u}} {D : Type*} [Category D]
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf) ⥤ D)
    (I J : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property I]
    [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property J]
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
    (κ : J ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) (e : I ≅ J)
    (he : e.hom ≫ κ = ι)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ)
    (n : ℤ)
    [HasPullback (G.map (idealPowerMap Z I n (F.d n (n + 1))))
      (G.map (idealPowerIncl Z I ι n (F.X (n + 1))))]
    [HasPullback (G.map (idealPowerMap Z J n (F.d n (n + 1))))
      (G.map (idealPowerIncl Z J κ n (F.X (n + 1))))] :
    IsIso (pullbackComparison G (idealPowerMap Z I n (F.d n (n + 1)))
        (idealPowerIncl Z I ι n (F.X (n + 1)))) ↔
      IsIso (pullbackComparison G (idealPowerMap Z J n (F.d n (n + 1)))
        (idealPowerIncl Z J κ n (F.X (n + 1)))) :=
  isIso_pullbackComparison_iff_of_isIso G _ _ _ _
    (IdealCongr.powerIso Z I J e n (F.X n)).hom
    (IdealCongr.powerIso Z I J e (n + 1) (F.X (n + 1))).hom
    (IdealCongr.powerIso Z I J e n (F.X (n + 1))).hom
    (IdealCongr.powerIso_natural Z I J e n (F.d n (n + 1)))
    (IdealCongr.powerIso_idealPowerIncl Z I J ι κ e he n (F.X (n + 1)))

end Core

/-! ### The cocycle condition -/

section Cocycle

variable {X Y Z : RingedSpace.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
  (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf).property I]
  [Mono (pullbackIdealIncl (p ≫ q) I ι)] [Mono (pullbackIdealIncl q I ι)]
  [Mono (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Z ι (F.X n))
  (hq : ∀ n : ℤ, IsIdealTorsionFree Y (pullbackIdealIncl q I ι) ((pullbackComplex q F).X n))
  (hk : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl (p ≫ q) I ι)
    ((pullbackComplex (p ≫ q) F).X n))
  (hpq : ∀ n : ℤ, IsIdealTorsionFree X
    (pullbackIdealIncl p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι))
    ((pullbackComplex p (pullbackComplex q F)).X n))

/-- **The cocycle condition for the derived comparison of décalages.** Along a composite
`p ≫ q`, the comparison for `q` pulled back along `p`, followed by the comparison for `p`, is the
composition isomorphism `Lq^* ⋙ Lp^* ≅ L(p ≫ q)^*` followed by the comparison for `p ≫ q` and by
the isomorphism `Stacks.IdealTorsion.Eta.pullbackCompEtaIso` of décalages. -/
theorem derivedPullbackEtaCore_cocycle :
    (derivedPullback p).map (derivedPullbackEtaCore q I ι F hF hq) ≫
        derivedPullbackEtaCore p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι)
          (pullbackComplex q F) hq hpq =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p q).hom.app
          ((QR Z).obj (etaObj Z I ι F hF)) ≫
        derivedPullbackEtaCore (p ≫ q) I ι F hF hk ≫
        (QR X).map (pullbackCompEtaIso p q (p ≫ q)
          (Stacks.DerivedPullback.Composition.modulePullbackComp p q) I ι F hk hpq).hom := by
  have hlaw :=
    AlgebraicGeometry.StandardModel.derivedPullbackComplexComparison_comp_compIsoCanonical
      p q (etaObj Z I ι F hF)
  have hlaw' : (derivedPullback p).map
        ((Stacks.DerivedPullback.derivedPullbackComplexComparison q).app (etaObj Z I ι F hF)) ≫
        (Stacks.DerivedPullback.derivedPullbackComplexComparison p).app
          (pullbackComplex q (etaObj Z I ι F hF)) =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical p q).hom.app
          ((QR Z).obj (etaObj Z I ι F hF)) ≫
        (Stacks.DerivedPullback.derivedPullbackComplexComparison (p ≫ q)).app
          (etaObj Z I ι F hF) ≫
        (QR X).map ((Functor.mapHomologicalComplexCompIso
          (Stacks.DerivedPullback.Composition.modulePullbackComp p q) (ComplexShape.up ℤ)).inv.app
            (etaObj Z I ι F hF)) := by
    rw [← Iso.app_hom, ← Iso.inv_comp_eq, Iso.app_inv]
    exact hlaw.symm
  have hnat := derivedPullback_map_comparison_app p (pullbackEtaMap q I ι F hF hq)
  have hco := pullbackEtaMap_cocycle p q (p ≫ q)
    (Stacks.DerivedPullback.Composition.modulePullbackComp p q) I ι F hF hq hk hpq
  unfold derivedPullbackEtaCore
  rw [Functor.map_comp, Category.assoc, reassoc_of% hnat,
    ← Functor.map_comp (QR X), reassoc_of% hlaw',
    ← Functor.map_comp (QR X), hco, Functor.map_comp, Category.assoc]

/-- If the comparison for `p` at `q^*F^•` is invertible — for instance if `p` is flat — then the
comparison for `p ≫ q` is invertible exactly when the comparison for `q`, pulled back along `p`,
is. -/
theorem isIso_derivedPullbackEtaCore_comp_iff_left
    (hp : IsIso (derivedPullbackEtaCore p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι)
      (pullbackComplex q F) hq hpq)) :
    IsIso ((derivedPullback p).map (derivedPullbackEtaCore q I ι F hF hq)) ↔
      IsIso (derivedPullbackEtaCore (p ≫ q) I ι F hF hk) := by
  have h := congrArg IsIso (derivedPullbackEtaCore_cocycle p q I ι F hF hq hk hpq)
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at h
  exact h.to_iff

/-- If the comparison for `q` at `F^•` is invertible — for instance if `q` is flat — then the
comparison for `p ≫ q` is invertible exactly when the comparison for `p` at `q^*F^•` is. -/
theorem isIso_derivedPullbackEtaCore_comp_iff_right
    (hq' : IsIso (derivedPullbackEtaCore q I ι F hF hq)) :
    IsIso (derivedPullbackEtaCore p ((pullbackFunctor q).obj I) (pullbackIdealIncl q I ι)
      (pullbackComplex q F) hq hpq) ↔
      IsIso (derivedPullbackEtaCore (p ≫ q) I ι F hF hk) := by
  have h := congrArg IsIso (derivedPullbackEtaCore_cocycle p q I ι F hF hq hk hpq)
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at h
  exact h.to_iff

end Cocycle

end Stacks.IdealTorsion.Eta

end
