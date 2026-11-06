/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotOpenSubspaceHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorRepresentedProper
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# `Quot^P` of an open subspace is represented by an open subscheme

Let `j : X ⟶ Y` be an open immersion of algebraic spaces separated and of finite presentation
over `B`, `G` a quasi-coherent `𝒪_Y`-module, `F = j^*G` and `M` an invertible `𝒪_Y`-module. If
`Quot^{P, M}_{G/Y/B}` is represented by a scheme `Z` proper over `B`, then
`Quot^{P, j^*M}_{F/X/B}` is represented by an open subscheme `V ⊆ Z`: the locus of `Z` over which
the universal quotient is supported in `X` (the source's hint for Stacks 0DP3), through the open
immersion `Quot_{F/X/B} ⟶ Quot_{G/Y/B}` of Stacks 0DP3, which identifies `Quot^{P, j^*M}_{F/X/B}`
with the quotients of `Quot^{P, M}_{G/Y/B}` supported in `X`
(`AlgebraicGeometry.Space.QuotOpenSubspaceSituation.hasHilbertPolynomial_extendQuotient_iff`).

This is the step of the proof of Stacks 0DPD which exhibits `Quot^P_{F/X/B}` as an open subspace
of the proper `Quot^P_{𝒢/X'/B}`.

## Main results

* `Space.QuotOpenSubspaceSituation.exists_isOpenImmersion_represented_hilbertPolynomialQuot`
  (in the namespace `AlgebraicGeometry`): if `Quot^{P, M}_{G/Y/B}` is represented by a scheme `Z`
  proper over `B`, then `Quot^{P, j^*M}_{F/X/B}` is represented by an open subscheme of `Z`.

## References

* [Stacks Project, Tag 0DP3](https://stacks.math.columbia.edu/tag/0DP3)
* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotOpenSubspaceSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotOpenSubspaceSituation B S hS) (M : Modules.{u, u} B S hS D.Y.1 D.Y.2)
  [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.Y.1)
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O)).property M]
  (P : ℤ → ℤ)

/-- Membership in `Quot^{P, j^*M}_{F/X/B}`, unfolded. -/
theorem source_mem_hilbertPolynomialQuot_iff {T : BigFppfOver B S hS}
    (x : QuotFamilyOver D.sourceSituation T) :
    x ∈ (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.j).obj M)
        (hL := isInvertible_modulePullback B S hS D.j M) P).obj (op T) ↔
      @CoherentObject.HasHilbertPolynomial B S hS D.sourceSituation.toCoherentSituation
        ((modulePullback B S hS D.j).obj M) (isInvertible_modulePullback B S hS D.j M) P
        (D.sourceSituation.cohObject _ x.subobject x.mem) :=
  Iff.rfl

/-- Membership in `Quot^{P, M}_{G/Y/B}`, unfolded. -/
theorem target_mem_hilbertPolynomialQuot_iff {T : BigFppfOver B S hS}
    (y : QuotFamilyOver D.targetSituation T) :
    y ∈ (D.targetSituation.hilbertPolynomialQuot M P).obj (op T) ↔
      @CoherentObject.HasHilbertPolynomial B S hS D.targetSituation.toCoherentSituation M hM P
        (D.targetSituation.cohObject _ y.subobject y.mem) :=
  Iff.rfl

/-- A quotient of `F_T` lies in `Quot^{P, j^*M}` exactly when its direct image lies in
`Quot^{P, M}`. -/
theorem quotFamilyOverExtend_mem_iff {T : BigFppfOver B S hS}
    (x : QuotFamilyOver D.sourceSituation T) :
    D.quotFamilyOverExtend T x ∈ (D.targetSituation.hilbertPolynomialQuot M P).obj (op T) ↔
      x ∈ (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.j).obj M)
        (hL := isInvertible_modulePullback B S hS D.j M) P).obj (op T) := by
  rw [target_mem_hilbertPolynomialQuot_iff, source_mem_hilbertPolynomialQuot_iff]
  obtain ⟨b, K, hK⟩ := x
  dsimp only [quotFamilyOverExtend]
  exact D.hasHilbertPolynomial_extendQuotient_iff M P (CostructuredArrow.mk b) K hK

variable {M P}

/-- **`Quot^{P, j^*M}_{F/X/B}` is represented by an open subscheme of the scheme representing
`Quot^{P, M}_{G/Y/B}`.** If `Quot^{P, M}_{G/Y/B}` is represented by a scheme `Z` with a proper
morphism `q : h_Z ⟶ B`, then there are an open immersion `ι : V ⟶ Z` of schemes of the site and
an identification of `h_V` with `Quot^{P, j^*M}_{F/X/B}` under which the canonical morphism to
`B` is `h_ι ≫ q`. -/
theorem exists_isOpenImmersion_represented_hilbertPolynomialQuot
    (hG : D.targetSituation.IsRepresentedProper (D.targetSituation.hilbertPolynomialQuot M P)) :
    ∃ (Z V : BigFppfOver B S hS) (ι : V ⟶ Z) (q : yoneda.obj Z ⟶ D.base.obj)
      (e : yoneda.obj V ⋙ uliftFunctor.{u + 1, u} ≅
        (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.j).obj M)
          (hL := isInvertible_modulePullback B S hS D.j M) P).toFunctor),
      IsProper B S hS q ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι) ∧
        e.hom ≫ (D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.j).obj M)
            (hL := isInvertible_modulePullback B S hS D.j M) P).ι ≫
            D.sourceSituation.quotSitePresheafToBase =
          Functor.whiskerRight (yoneda.map ι ≫ q) uliftFunctor.{u + 1, u} := by
  obtain ⟨Z, e, q, he, hq⟩ := hG
  let QC := D.targetSituation.hilbertPolynomialQuot M P
  let QA := D.sourceSituation.hilbertPolynomialQuot ((modulePullback B S hS D.j).obj M)
    (hL := isInvertible_modulePullback B S hS D.j M) P
  -- the universal quotient over `Z`, and the locus where it is supported in `X`
  let yZ : QuotFamilyOver D.targetSituation Z := (e.hom.app (op Z) ⟨𝟙 Z⟩).1
  have he_app : ∀ {T : BigFppfOver B S hS} (g : T ⟶ Z),
      (e.hom.app (op T) ⟨g⟩).1 = yZ.baseChange g := by
    intro T g
    have h1 : e.hom.app (op T) ⟨g ≫ 𝟙 Z⟩ = QC.toFunctor.map g.op (e.hom.app (op Z) ⟨𝟙 Z⟩) :=
      types_congr_hom (e.hom.naturality g.op) ⟨𝟙 Z⟩
    rw [Category.comp_id] at h1
    exact congrArg Subtype.val h1
  let U := openSubspaceOfPoints B S hS (yoneda.obj Z) (D.supportLocus yZ)
  have hU : IsOpenSubspace B S hS U :=
    isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_yoneda B S hS Z) _
      (D.isOpen_supportLocus yZ)
  have hmemU : ∀ {T : BigFppfOver B S hS} (g : T ⟶ Z),
      g ∈ U.obj (op T) ↔ D.SupportedInOpen (yZ.baseChange g) := by
    intro T g
    rw [mem_openSubspaceOfPoints_iff, D.supportedInOpen_baseChange_iff]
    rfl
  -- `QA ≅ U`, objectwise through the direct image and `e`
  let w : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (x : QuotFamilyOver D.sourceSituation T.unop),
      x ∈ QA.obj T → QC.toFunctor.obj T := fun T x hx =>
    ⟨D.quotFamilyOverExtend T.unop x, (D.quotFamilyOverExtend_mem_iff M P x).2 hx⟩
  have hw : ∀ T x hx, e.hom.app T ⟨(e.inv.app T (w T x hx)).down⟩ = w T x hx :=
    fun T x hx => Iso.inv_hom_id_app_apply e T _
  let φ : ∀ T : (BigFppfOver B S hS)ᵒᵖ, QA.toFunctor.obj T → U.toFunctor.obj T := fun T x =>
    ⟨(e.inv.app T (w T x.1 x.2)).down, by
      rw [hmemU, ← he_app]
      erw [hw T x.1 x.2]
      exact (D.exists_quotFamilyOverExtend_eq_iff _).1 ⟨x.1, rfl⟩⟩
  have hφ_bij : ∀ T, Function.Bijective (φ T) := by
    intro T
    refine ⟨fun x x' hxx' => ?_, fun g => ?_⟩
    · exact Subtype.ext (D.quotFamilyOverExtend_injective T.unop (congrArg Subtype.val
        ((e.app T).toEquiv.symm.injective (ULift.ext (congrArg Subtype.val hxx')))))
    · obtain ⟨g, hg⟩ := g
      have hsupp : D.SupportedInOpen (e.hom.app T ⟨g⟩).1 := by
        rw [he_app]
        exact (hmemU g).1 hg
      obtain ⟨x, hx⟩ := (D.exists_quotFamilyOverExtend_eq_iff _).2 hsupp
      have hxA : x ∈ QA.obj T := (D.quotFamilyOverExtend_mem_iff M P x).1 (hx ▸ (e.hom.app T ⟨g⟩).2)
      refine ⟨⟨x, hxA⟩, Subtype.ext ?_⟩
      have h2 : w T x hxA = e.hom.app T ⟨g⟩ := Subtype.ext hx
      show (e.inv.app T (w T x hxA)).down = g
      rw [h2]
      exact congrArg ULift.down (Iso.hom_inv_id_app_apply e T _)
  let ψ : QA.toFunctor ≅ U.toFunctor ⋙ uliftFunctor.{u + 1, u} :=
    NatIso.ofComponents (fun T => (Equiv.ofBijective (φ T) (hφ_bij T) |>.trans
      Equiv.ulift.symm).toIso) (by
      intro T T' h
      ext x'
      obtain ⟨x, hxA⟩ := x'
      refine congrArg ULift.up (Subtype.ext ?_)
      have hnat : e.inv.app T' (QC.toFunctor.map h (w T x hxA)) =
          (yoneda.obj Z ⋙ uliftFunctor.{u + 1, u}).map h (e.inv.app T (w T x hxA)) :=
        types_congr_hom (e.inv.naturality h) _
      have hx : w T' (x.baseChange h.unop) (QA.map h hxA) = QC.toFunctor.map h (w T x hxA) :=
        Subtype.ext (D.quotFamilyOverExtend_baseChange h.unop x)
      show (e.inv.app T' (w T' (x.baseChange h.unop) (QA.map h hxA))).down =
        h.unop ≫ (e.inv.app T (w T x hxA)).down
      rw [hx, hnat]
      rfl)
  -- `U` is represented by an open subscheme `V ⟶ Z`
  have hrep := hU.2.rep
  let V := hrep.pullback (𝟙 (yoneda.obj Z))
  let ι : V ⟶ Z := hrep.snd (𝟙 (yoneda.obj Z))
  have hι : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι) :=
    hU.2.property_snd (𝟙 (yoneda.obj Z))
  have hpb := hrep.isPullback (𝟙 (yoneda.obj Z))
  have : IsIso (hrep.fst (𝟙 (yoneda.obj Z))) := hpb.isIso_fst_of_isIso
  let eV : yoneda.obj V ≅ U.toFunctor := asIso (hrep.fst (𝟙 (yoneda.obj Z)))
  have heV : eV.hom ≫ U.ι = yoneda.map ι := hpb.w.trans (Category.comp_id _)
  refine ⟨Z, V, ι, q, Functor.isoWhiskerRight eV uliftFunctor.{u + 1, u} ≪≫ ψ.symm, hq, hι, ?_⟩
  -- the morphism to `B`
  have hR : QA.ι ≫ D.sourceSituation.quotSitePresheafToBase =
      ψ.hom ≫ Functor.whiskerRight (U.ι ≫ q) uliftFunctor.{u + 1, u} := by
    ext T x
    refine congrArg ULift.up ?_
    have he' := congrArg ULift.down (types_congr_hom (NatTrans.congr_app he T) ⟨(φ T x).1⟩)
    show (D.sourceSituation.quotSitePresheafToBase.app T x.1).down = q.app T (φ T x).1
    refine Eq.trans ?_ he'
    show _ = (D.targetSituation.quotSitePresheafToBase.app T
      (QC.ι.app T (e.hom.app T ⟨(φ T x).1⟩))).down
    rw [hw T x.1 x.2]
    rfl
  rw [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, Category.assoc, hR,
    Iso.inv_hom_id_assoc, ← Functor.whiskerRight_comp, ← Category.assoc, heV]

end AlgebraicGeometry.Space.QuotOpenSubspaceSituation

end
