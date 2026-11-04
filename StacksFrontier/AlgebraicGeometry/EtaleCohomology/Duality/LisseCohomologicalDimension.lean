module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LevelTorsionLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.OpenClosedDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FiniteEtaleExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FiniteEtaleAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperLocallyConstantDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleTraceDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckPerfect

/-!
# `Ext^q(F, ℤ/ℓⁿ) = 0` for `q > 2d` and `F` lisse on a proper variety of dimension `d`

Let `Y` be proper over a separably closed field, of dimension at most `d`, `ℓ` a prime and `F` a
locally constant sheaf of finite type of `ℤ/ℓ`-modules on `Y_étale`. Then
`Ext^q(F, ℤ/ℓ) = 0` for `q > 2d`, the vanishing on the dual side of Poincaré duality.

By Tag 0A3R there is a connected finite étale `π : T → Y` of degree `δ` prime to `ℓ` with `π^{-1}F`
a successive extension of copies of `ℤ/ℓ_T`. The unit of `π^{-1} ⊣ π_*` followed by the trace of
`π` is multiplication by `δ` (Tag 03SH, `AlgebraicGeometry.unit_comp_moduleTrace_eq_nsmul`), an
automorphism, so `F` is a direct summand of `π_* π^{-1} F`
(`Stacks.EtaleCohomology.exists_comp_eq_id_directImage_inverseImage`). Since `π_*` is left
adjoint to `π^{-1}`, `Ext^q(π_* π^{-1}F, ℤ/ℓ_Y) = Ext^q_T(π^{-1}F, ℤ/ℓ_T)`, which vanishes for
`q > 2d` by the long exact sequences of the filtration and `H^q(T, ℤ/ℓ) = 0` (Tag 095U).

The case of `ℤ/ℓᵐ` follows by dévissage along `0 → F[ℓ] → F → F/F[ℓ] → 0`, with
`Ext^q_{ℤ/ℓᵐ}(F[ℓ], ℤ/ℓᵐ) = Ext^q_{ℤ/ℓ}(F[ℓ], ℤ/ℓ)` (the `ℓ`-torsion of `ℤ/ℓᵐ` being `ℤ/ℓ`).
This is the vanishing `hv₂` of the dévissage
`Stacks.EtaleCohomology.LevelChange.isDualityPerfect_of_coextend`, in the proof of Poincaré duality
with `ℤ/ℓⁿ` coefficients for the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exists_comp_eq_id_directImage_inverseImage`: a sheaf of
  `ℤ/ℓ`-modules is a direct summand of `π_* π^{-1} F` for `π` finite étale of degree prime to `ℓ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe w v' u' u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- On a sheaf of `ℤ/n`-modules, `a • 𝟙` only depends on `a` modulo `n`. -/
theorem nsmul_id_sheaf_zmod_eq {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    {n : ℕ} (F : Sheaf J (ModuleCat.{w} (ZMod n))) {a b : ℕ} (hab : (a : ZMod n) = b) :
    a • 𝟙 F = b • 𝟙 F := by
  ext U x
  show a • (show F.obj.obj U from x) = b • (show F.obj.obj U from x)
  rw [← Nat.cast_smul_eq_nsmul (ZMod n), hab, Nat.cast_smul_eq_nsmul]

/-- **Retracts across equivalences and adjunctions.** Let `EY : C'_Y ≌ C_Y` and `ET : C'_T ≌ C_T`
be equivalences, `L ⊣ R` an adjunction between `C'_Y` and `C'_T`, and `L₀ ⊣ R₀` one between `C_Y`
and `C_T` with `R₀ ≅ EY ∘ R ∘ ET⁻¹`. If the unit of `L ⊣ R` at `EY⁻¹ G` has a retraction, then `G`
is a retract of `R₀ L₀ G`. -/
theorem exists_comp_eq_id_of_equivalence {CY' CT' CY CT : Type*} [Category CY'] [Category CT']
    [Category CY] [Category CT] (EY : CY' ≌ CY) (ET : CT' ≌ CT) {L : CY' ⥤ CT'} {R : CT' ⥤ CY'}
    (adjB : L ⊣ R) {L₀ : CY ⥤ CT} {R₀ : CT ⥤ CY} (adj₀ : L₀ ⊣ R₀)
    (isoR : (ET.inverse ⋙ R) ⋙ EY.functor ≅ R₀) (G : CY)
    (r : R.obj (L.obj (EY.inverse.obj G)) ⟶ EY.inverse.obj G)
    (hr : adjB.unit.app (EY.inverse.obj G) ≫ r = 𝟙 _) :
    ∃ (i : G ⟶ R₀.obj (L₀.obj G)) (r' : R₀.obj (L₀.obj G) ⟶ G), i ≫ r' = 𝟙 G := by
  let adjM := EY.symm.toAdjunction.comp (adjB.comp ET.toAdjunction)
  let isoL := (adjM.ofNatIsoRight isoR).leftAdjointUniq adj₀
  let isoH : EY.functor.obj (R.obj (L.obj (EY.inverse.obj G))) ≅ R₀.obj (L₀.obj G) :=
    EY.functor.mapIso (R.mapIso (ET.unitIso.app _)) ≪≫
      isoR.app (ET.functor.obj (L.obj (EY.inverse.obj G))) ≪≫ R₀.mapIso (isoL.app G)
  refine ⟨(EY.counitIso.app G).inv ≫ EY.functor.map (adjB.unit.app _) ≫ isoH.hom,
    isoH.inv ≫ EY.functor.map r ≫ (EY.counitIso.app G).hom, ?_⟩
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← EY.functor.map_comp_assoc, hr]
  simp

variable {p : ℕ} [Fact p.Prime]

/-- **A sheaf of `ℤ/p`-modules is a direct summand of `π_* π^{-1} F`** for `π` finite étale of
constant degree `δ` prime to `p`: the unit of `π^{-1} ⊣ π_*` followed by the trace is `δ`
(Tag 03SH), computed on the bounded small étale site of Stacks 021B and transported to Mathlib's
small étale site. -/
theorem exists_comp_eq_id_directImage_inverseImage {Y T : Scheme.{u}} (π : T ⟶ Y) [IsFinite π]
    [Etale π] (δ : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank π δ] (hδ : ¬ p ∣ δ)
    (G : EtaleModules.{u, 0} (ZMod p) Y) :
    ∃ (i : G ⟶ (etaleModuleDirectImage.{u, 0} (ZMod p) π).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod p) π).obj G))
      (r : (etaleModuleDirectImage.{u, 0} (ZMod p) π).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod p) π).obj G) ⟶ G), i ≫ r = 𝟙 G := by
  let A := ModuleCat.{u + 1} (ZMod p)
  let B := BigEtaleSite.containing Y
  have hY : B.Contains Y := BigEtaleSite.contains_containing Y
  have hT : B.Contains T := B.contains_of_finiteEtale π ⟨inferInstance, inferInstance⟩ hY
  let YB : B.Scheme := ⟨Y, hY⟩
  let TB : B.Scheme := ⟨T, hT⟩
  let fB : TB ⟶ YB := ObjectProperty.homMk π
  have : Etale (B.inclusion.map fB) := inferInstanceAs (Etale π)
  have : IsFinite (B.inclusion.map fB) := inferInstanceAs (IsFinite π)
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map fB) δ :=
    inferInstanceAs (Stacks.Morphisms.IsFiniteLocallyFreeOfRank π δ)
  let EY := SmallEtale.sheafEquiv B Y hY A
  let ET := SmallEtale.sheafEquiv B T hT A
  let adjB := smallEtalePostcomposePushforwardAdjunction B fB A
  let G' := EY.inverse.obj G
  let isoR : (ET.inverse ⋙ BigEtaleSite.smallPushforward B fB A) ⋙ EY.functor ≅
      etaleModuleDirectImage.{u, 0} (ZMod p) π :=
    Functor.isoWhiskerRight (SmallEtale.toEtaleSitePushforwardBaseChangeIso B fB A).symm
        EY.functor ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ EY.counitIso ≪≫
      Functor.rightUnitor _
  -- an inverse of `δ` modulo `p`
  have hδ' : (δ : ZMod p) ≠ 0 := fun h => hδ ((ZMod.natCast_eq_zero_iff δ p).1 h)
  let c : ℕ := ((δ : ZMod p)⁻¹).val
  have hc : ((c * δ : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hδ', Nat.cast_one]
  refine exists_comp_eq_id_of_equivalence EY ET adjB
    (etaleModuleInverseImageAdj.{u, 0} (ZMod p) π) isoR G
    (c • (moduleTrace B YB.1 YB.property (SmallEtale.ofEtaleHom B fB) (ZMod p)).app G') ?_
  rw [Preadditive.comp_nsmul, unit_comp_moduleTrace_eq_nsmul B fB (ZMod p) δ G', smul_smul,
    nsmul_id_sheaf_zmod_eq G' hc, one_smul]
  rfl

/-- `Ext^q(G, D)` is a retract of `Ext^q(H, D)` when `G` is a retract of `H`. -/
theorem subsingleton_ext_of_comp_eq_id {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    {G H : C} (i : G ⟶ H) (r : H ⟶ G) (hir : i ≫ r = 𝟙 G) (D : C) {q : ℕ}
    (h : Subsingleton (Ext.{w} H D q)) : Subsingleton (Ext.{w} G D q) := by
  refine ⟨fun a b => ?_⟩
  have hab : (Ext.mk₀ r).comp a (zero_add q) = (Ext.mk₀ r).comp b (zero_add q) :=
    Subsingleton.elim _ _
  have key : ∀ x : Ext.{w} G D q,
      x = (Ext.mk₀ i).comp ((Ext.mk₀ r).comp x (zero_add q)) (zero_add q) := fun x => by
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hir, Ext.mk₀_id_comp]
  rw [key a, key b, hab]

/-- The cokernel sequence of a monomorphism is short exact. -/
private theorem shortExact_cokernelSequence {C : Type*} [Category C] [Abelian C] {X Y : C}
    (f : X ⟶ Y) [Mono f] : (ShortComplex.cokernelSequence f).ShortExact :=
  .mk' (ShortComplex.cokernelSequence_exact f) ‹_› inferInstance

section Vanishing

variable {k : Type u} [Field k] [IsSepClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsProper f] (d : ℕ)

include f in
/-- **`Ext^q(G, ℤ/ℓ) = 0` for `q > 2d` on a proper scheme of dimension at most `d`**, for every
finite type locally constant sheaf `G` of `ℤ/ℓ`-modules on a connected `Y` proper over a
separably closed field: `G` is a direct summand of `π_* π^{-1} G` for a connected finite étale
`π : T → Y` of degree prime to `ℓ` over which `G` is a successive extension of copies of `ℤ/ℓ`
(Tag 0A3R), and `Ext^q(π_* π^{-1} G, ℤ/ℓ_Y) = Ext^q_T(π^{-1} G, ℤ/ℓ_T)` vanishes by
`H^q(T, ℤ/ℓ) = 0` (Tag 095U). -/
theorem subsingleton_ext_unitSheaf_right_of_isFiniteTypeLocallyConstant [ConnectedSpace Y]
    (hdim : topologicalKrullDim Y ≤ d) (G : EtaleModules.{u, 0} (ZMod p) Y)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod p) Y.smallEtaleTopology G)
    (q : ℕ) (hq : 2 * d < q) : Subsingleton (Ext G (unitSheaf (X := Y) p) q) := by
  obtain ⟨T, π, δ, _, _, -, _, hδ, Xs, hhead, hlast⟩ :=
    exists_connected_primeToEll_finiteEtale_relSeries_constantRankOneStep Fact.out G hG
  obtain ⟨i, r, hir⟩ := exists_comp_eq_id_directImage_inverseImage π δ hδ G
  refine subsingleton_ext_of_comp_eq_id i r hir _ ?_
  -- `Ext^q(π_* M, ℤ/ℓ_Y) = Ext^q_T(M, ℤ/ℓ_T)`
  suffices hT : Subsingleton (Ext ((etaleModuleInverseImage.{u, 0} (ZMod p) π).obj G)
      ((etaleModuleInverseImage.{u, 0} (ZMod p) π).obj (unitSheaf (X := Y) p)) q) from
    (extDirectImageLeftAddEquiv (ZMod p) π _ _ q).symm.toEquiv.subsingleton
  suffices hT' : Subsingleton (Ext ((etaleModuleInverseImage.{u, 0} (ZMod p) π).obj G)
      (unitSheaf (X := T) p) q) from
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
      (unitSheafInverseImageIso π).hom q).1.subsingleton
  -- the filtration by copies of `ℤ/ℓ_T`
  have hΛ : Subsingleton (Ext (unitSheaf (X := T) p) (unitSheaf (X := T) p) q) :=
    subsingleton_ext_unitSheaf_of_finiteEtale_proper f d hdim π _ q hq
  have key : ∀ j : Fin (Xs.length + 1),
      Subsingleton (Ext (Subobject.underlying.obj (Xs j)) (unitSheaf (X := T) p) q) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      exact subsingleton_ext_of_comp_eq_id (0 : _ ⟶ unitSheaf (X := T) p) 0
        (hhead.eq_of_src _ _) _ hΛ
    | succ j ih =>
      obtain ⟨hle, ⟨e⟩⟩ := Xs.step j
      exact Ext.subsingleton_ext_left_X₂_of_shortExact
        (shortExact_cokernelSequence (Subobject.ofLE _ _ hle)) _ ih
        (AdequateFunctor.subsingleton_ext_of_iso_left e.symm q inferInstance)
  exact AdequateFunctor.subsingleton_ext_of_iso_left (asIso Xs.last.arrow) q (key (Fin.last _))

include f in
/-- **`Ext^q(F, ℤ/pᵐ) = 0` for `q > 2d`** for every finite type locally constant sheaf `F` of
`ℤ/pᵐ`-modules on a connected `Y` proper over a separably closed field with `dim Y ≤ d`: by
dévissage along `0 → F[p] → F → F/F[p] → 0`, with
`Ext^q_{ℤ/pᵐ}(F[p], ℤ/pᵐ) = Ext^q_{ℤ/p}(F[p], ℤ/pᵐ[p]) = Ext^q_{ℤ/p}(F[p], ℤ/p)`
(`Stacks.EtaleCohomology.LevelChange.extMap_coextendScalars_bijective` and
`Stacks.EtaleCohomology.LevelChange.unitSheafCoextendIso`), which vanishes by
`subsingleton_ext_unitSheaf_right_of_isFiniteTypeLocallyConstant`. -/
theorem subsingleton_ext_unitSheaf_pow_right_of_isFiniteTypeLocallyConstant [ConnectedSpace Y]
    (hdim : topologicalKrullDim Y ≤ d) {m : ℕ} [NeZero m]
    (F : EtaleModules.{u, 0} (ZMod (p ^ m)) Y)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (p ^ m)) Y.smallEtaleTopology F)
    (q : ℕ) (hq : 2 * d < q) : Subsingleton (Ext F (unitSheaf (X := Y) (p ^ m)) q) := by
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (NeZero.ne m)
  have hdv := LevelChange.dvd_pow_self_of_neZero (p := p) (m := m)
  have hD : PowExact p m (unitSheaf (X := Y) (p ^ m)) := powExact_constantSheaf_zmod p m Y
  suffices key : ∀ k : ℕ, ∀ F : EtaleModules.{u, 0} (ZMod (p ^ m)) Y,
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (p ^ m)) Y.smallEtaleTopology F →
      (p ^ k) • 𝟙 F = 0 → Subsingleton (Ext F (unitSheaf (X := Y) (p ^ m)) q) from
    key m F hF (etaleModules_pow_nsmul_id F)
  intro k
  induction k with
  | zero =>
    intro F _ hk
    rw [pow_zero, one_nsmul] at hk
    refine ⟨fun a b => ?_⟩
    have h0 : ∀ x : Ext F (unitSheaf (X := Y) (p ^ m)) q, x = 0 := fun x => by
      rw [← Ext.mk₀_id_comp x, hk, Ext.mk₀_zero, Ext.zero_comp]
    rw [h0 a, h0 b]
  | succ k ih =>
    intro F hF hk
    have hS := shortExact_cokernelSequence (LevelChange.torsionCounit Y F)
    have h₃ := ih _ (LevelChange.isFiniteTypeLocallyConstant_cokernel_torsionCounit Y F hF)
        (LevelChange.pow_nsmul_id_cokernel_counit Y F hk)
    have h₁ : Subsingleton (Ext (ShortComplex.cokernelSequence
        (LevelChange.torsionCounit Y F)).X₁ (unitSheaf (X := Y) (p ^ m)) q) := by
      have : Subsingleton (Ext ((LevelChange.coextend Y hdv).obj F) (unitSheaf (X := Y) p) q) :=
        subsingleton_ext_unitSheaf_right_of_isFiniteTypeLocallyConstant f d hdim _
          (LevelChange.isFiniteTypeLocallyConstant_coextend Y F hF) q hq
      have : Subsingleton (Ext ((LevelChange.coextend Y hdv).obj F)
          ((LevelChange.coextend Y hdv).obj (unitSheaf (X := Y) (p ^ m))) q) :=
        (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso
          (LevelChange.unitSheafCoextendIso Y p m).hom q).2.subsingleton
      exact (LevelChange.extMap_coextendScalars_bijective Y hdv hm (pow_one p).symm _ _ hD
        q).surjective.subsingleton
    exact Ext.subsingleton_ext_left_X₂_of_shortExact hS _ h₁ h₃

end Vanishing

end Stacks.EtaleCohomology

end
