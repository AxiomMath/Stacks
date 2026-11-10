module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypeCoinduction
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafEffacementCriterion

/-!
# `ℱ` of a coinduced module is a direct image from a finite étale cover

Let `X` be a connected scheme, `Λ` a finite ring, `φ : V ⟶ X` a finite étale morphism with `V`
connected and `v` a geometric point of `V`, and let `H ⊆ π₁(X, φ(v))` be the image of
`π₁(V, v)`, an open subgroup. For a finite `Λ`-module `M` with a continuous action of `π₁(X, φ(v))`
this file constructs, naturally in `M`, an isomorphism
`ℱ_{Coind_H M} ≅ φ_* φ^* ℱ_M`
where `Coind_H M` is the module of functions `π₁(X, φ(v)) ⧸ H → M`
(`Stacks.GroupCohomology.finiteTypeContinuousModuleCoind`). Under it the unit
`ℱ_M ⟶ φ_* φ^* ℱ_M` of the adjunction `φ^* ⊣ φ_*` is `ℱ` of the embedding of `M` into
`Coind_H M` as the constant functions.

## Main definitions

* `AlgebraicGeometry.representationSheafCoindEval` — `φ^* ℱ_{Coind_H M} ⟶ φ^* ℱ_M`, the sheaf
  version of evaluation at the trivial coset (through Tag 0DV6,
  `AlgebraicGeometry.representationSheafPullbackIso`).
* `AlgebraicGeometry.representationSheafCoindComparison` — its adjoint
  `ℱ_{Coind_H M} ⟶ φ_* φ^* ℱ_M`.
* `AlgebraicGeometry.representationSheafCoindIso` — the comparison is an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_representationSheafCoindComparison_app`.
* `AlgebraicGeometry.representationSheafCoindUnit_comp_comparison` — the unit of `φ^* ⊣ φ_*` is
  `ℱ` of the constant functions followed by the comparison.

## Implementation notes

The comparison is an isomorphism by the Yoneda lemma in the category of representations. The
sheaf `φ_* φ^* ℱ_M` is finite type locally constant (Tags 093R and 095B), hence is `ℱ_N` for a
representation `N` (Tag 0DV5), and the comparison is `ℱ` of a map `g : Coind_H M ⟶ N` because `ℱ`
is fully faithful. Maps `Q ⟶ N` are, through `ℱ`, the adjunction and Tag 0DV6, the maps of
`π₁(V, v)`-modules `res Q ⟶ res M`; under this identification composition with `g` is Frobenius
reciprocity (`Stacks.GroupCohomology.bijective_finiteTypeContinuousModuleCoindEval_comp`), a
bijection. So `g` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

variable (B : BigEtaleSite.{u}) {X V : B.Scheme} (φ : V ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace V.1] (Λ : Type) [Ring Λ] [Finite Λ] (v : GeometricPoint V.1)
  (H : OpenSubgroup (EtaleFundamentalGroup X.1 (v.map φ.hom)))
  (hφ : ∀ g, etaleFundamentalGroupMap φ.hom v g ∈ H)

/-- **Evaluation at the trivial coset**, `res (Coind_H M) ⟶ res M`, as a natural transformation
of functors to the representations of `π₁(V, v)`, for `H` containing the image of `π₁(V, v)`. -/
def finiteTypeContinuousModuleCoindEvalNatTrans :
    finiteTypeContinuousModuleCoind Λ H ⋙
        finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap φ.hom v) ⟶
      finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap φ.hom v) where
  app M := finiteTypeContinuousModuleCoindEval Λ H (etaleFundamentalGroupMap φ.hom v) hφ M
  naturality _ _ a :=
    finiteTypeContinuousModuleCoindEval_naturality Λ H (etaleFundamentalGroupMap φ.hom v) hφ a

/-- **`φ^* ℱ_{Coind_H M} ⟶ φ^* ℱ_M`**: through Tag 0DV6 (`φ^* ℱ_ρ ≅ ℱ_{res ρ}`), the sheaf of the
evaluation at the trivial coset `res (Coind_H M) ⟶ res M`. -/
def representationSheafCoindEval :
    finiteTypeContinuousModuleCoind Λ H ⋙ representationSheaf B X (v.map φ.hom) Λ ⋙
        etaleModuleInverseImage.{u, 0} Λ φ.hom ⟶
      representationSheaf B X (v.map φ.hom) Λ ⋙ etaleModuleInverseImage.{u, 0} Λ φ.hom where
  app M := (representationSheafPullbackIso B φ Λ v).hom.app
      ((finiteTypeContinuousModuleCoind Λ H).obj M) ≫
    (representationSheaf B V v Λ).map
      (finiteTypeContinuousModuleCoindEval Λ H (etaleFundamentalGroupMap φ.hom v) hφ M) ≫
    (representationSheafPullbackIso B φ Λ v).inv.app M
  naturality M M' a := by
    have h1 := (representationSheafPullbackIso B φ Λ v).hom.naturality
      ((finiteTypeContinuousModuleCoind Λ H).map a)
    have h2 := (representationSheafPullbackIso B φ Λ v).inv.naturality a
    have h3 := congrArg (representationSheaf B V v Λ).map
      (finiteTypeContinuousModuleCoindEval_naturality Λ H (etaleFundamentalGroupMap φ.hom v) hφ a)
    rw [Functor.map_comp, Functor.map_comp] at h3
    dsimp only [Functor.comp_map, Functor.comp_obj] at h1 h2 ⊢
    rw [reassoc_of% h1, reassoc_of% h3, h2]
    simp only [Category.assoc]

/-- **The comparison `ℱ_{Coind_H M} ⟶ φ_* φ^* ℱ_M`**, adjoint under `φ^* ⊣ φ_*` to
`AlgebraicGeometry.representationSheafCoindEval`. -/
def representationSheafCoindComparison :
    finiteTypeContinuousModuleCoind Λ H ⋙ representationSheaf B X (v.map φ.hom) Λ ⟶
      representationSheaf B X (v.map φ.hom) Λ ⋙ etaleModuleInverseImage.{u, 0} Λ φ.hom ⋙
        etaleModuleDirectImage.{u, 0} Λ φ.hom where
  app M := (etaleModuleInverseImageAdj.{u, 0} Λ φ.hom).homEquiv _ _
    ((representationSheafCoindEval B φ Λ v H hφ).app M)
  naturality M M' a := by
    dsimp only [Functor.comp_map, Functor.comp_obj]
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
    exact congrArg _ ((representationSheafCoindEval B φ Λ v H hφ).naturality a)

/-- The component of `AlgebraicGeometry.representationSheafCoindComparison` at `M` is the adjoint
under `φ^* ⊣ φ_*` of the component of `AlgebraicGeometry.representationSheafCoindEval`. -/
lemma representationSheafCoindComparison_app
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (v.map φ.hom))) :
    (representationSheafCoindComparison B φ Λ v H hφ).app M =
      (etaleModuleInverseImageAdj.{u, 0} Λ φ.hom).homEquiv _ _
        ((representationSheafCoindEval B φ Λ v H hφ).app M) :=
  rfl

/-- Under the adjunction, `ℱ_a` followed by the comparison is `φ^* ℱ_a` followed by the
evaluation. -/
lemma homEquiv_symm_map_comp_representationSheafCoindComparison
    {Q M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (v.map φ.hom))}
    (a : Q ⟶ (finiteTypeContinuousModuleCoind Λ H).obj M) :
    ((etaleModuleInverseImageAdj.{u, 0} Λ φ.hom).homEquiv _ _).symm
        ((representationSheaf B X (v.map φ.hom) Λ).map a ≫
          (representationSheafCoindComparison B φ Λ v H hφ).app M) =
      (representationSheafPullbackIso B φ Λ v).hom.app Q ≫
        (representationSheaf B V v Λ).map
          ((finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap φ.hom v)).map a ≫
            finiteTypeContinuousModuleCoindEval Λ H (etaleFundamentalGroupMap φ.hom v) hφ M) ≫
        (representationSheafPullbackIso B φ Λ v).inv.app M := by
  rw [representationSheafCoindComparison_app, Adjunction.homEquiv_naturality_left_symm]
  refine (congrArg _ (((etaleModuleInverseImageAdj.{u, 0} Λ φ.hom).homEquiv _ _).symm_apply_apply
    _)).trans ?_
  dsimp only [representationSheafCoindEval]
  have hn := (representationSheafPullbackIso B φ Λ v).hom.naturality a
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn, Functor.map_comp_assoc]

/-- **The unit of `φ^* ⊣ φ_*` is `ℱ` of the constant functions followed by the comparison**:
`ℱ_M ⟶ ℱ_{Coind_H M} ⟶ φ_* φ^* ℱ_M` is the unit. -/
theorem representationSheafCoindUnit_comp_comparison
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (v.map φ.hom))) :
    (representationSheaf B X (v.map φ.hom) Λ).map (finiteTypeContinuousModuleCoindUnit Λ H M) ≫
        (representationSheafCoindComparison B φ Λ v H hφ).app M =
      (etaleModuleInverseImageAdj.{u, 0} Λ φ.hom).unit.app
        ((representationSheaf B X (v.map φ.hom) Λ).obj M) := by
  rw [← Adjunction.homEquiv_id, ← Equiv.symm_apply_eq,
    homEquiv_symm_map_comp_representationSheafCoindComparison,
    finiteTypeContinuousModuleCoindUnit_comp_eval, CategoryTheory.Functor.map_id]
  exact (congrArg ((representationSheafPullbackIso B φ Λ v).hom.app M ≫ ·)
    (Category.id_comp _)).trans ((representationSheafPullbackIso B φ Λ v).hom_inv_id_app M)

variable (hH : ∀ h ∈ H, ∃ g, etaleFundamentalGroupMap φ.hom v g = h)

include hH in
/-- **The comparison `ℱ_{Coind_H M} ⟶ φ_* φ^* ℱ_M` is an isomorphism** when `H` is the image of
`π₁(V, v)`, for `φ` finite étale. -/
theorem isIso_representationSheafCoindComparison_app [IsFinite φ.hom] [Etale φ.hom]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 (v.map φ.hom))) :
    IsIso ((representationSheafCoindComparison B φ Λ v H hφ).app M) := by
  let x := v.map φ.hom
  let F := representationSheaf B X x Λ
  let FV := representationSheaf B V v Λ
  let A := etaleModuleInverseImageAdj.{u, 0} Λ φ.hom
  let P := representationSheafPullbackIso B φ Λ v
  let E := finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X x Λ
  let β := representationSheafIsoFiniteTypeLocallyConstant B X x Λ
  let hFF := representationSheafFullyFaithful B X x Λ
  let hFFV := representationSheafFullyFaithful B V v Λ
  let FM := F.obj M
  have hFM : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology FM :=
    ObjectProperty.prop_of_iso
      (P := fun G : EtaleModules.{u, 0} Λ X.1 ↦
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology G)
      (β.app M).symm (E.inverse.obj M).property
  let T' : ObjectProperty.FullSubcategory (fun G : EtaleModules.{u, 0} Λ X.1 ↦
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.1.smallEtaleTopology G) :=
    ⟨(etaleModuleDirectImage.{u, 0} Λ φ.hom).obj ((etaleModuleInverseImage.{u, 0} Λ φ.hom).obj FM),
      isFiniteTypeLocallyConstant_directImage_inverseImage Λ φ.hom FM hFM⟩
  let N := E.functor.obj T'
  let θ : F.obj N ≅ T'.obj := β.app N ≪≫ (ObjectProperty.ι _).mapIso (E.unitIso.app T').symm
  let c := (representationSheafCoindComparison B φ Λ v H hφ).app M
  let g := hFF.preimage (c ≫ θ.inv)
  have hc : F.map g ≫ θ.hom = c := by
    rw [hFF.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let res := finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap φ.hom v)
  let ev := finiteTypeContinuousModuleCoindEval Λ H (etaleFundamentalGroupMap φ.hom v) hφ M
  suffices hgi : IsIso g by
    change IsIso c
    rw [← hc]
    infer_instance
  refine isIso_of_yoneda_map_bijective g fun Q ↦ ?_
  -- the identification of maps `Q ⟶ N` with maps `φ^* ℱ_Q ⟶ φ^* ℱ_M`
  let Ψ : (Q ⟶ N) → ((etaleModuleInverseImage.{u, 0} Λ φ.hom).obj (F.obj Q) ⟶
      (etaleModuleInverseImage.{u, 0} Λ φ.hom).obj FM) := fun b ↦
    (A.homEquiv _ _).symm (F.map b ≫ θ.hom)
  have hΨ : Function.Injective Ψ := by
    intro b b' hb
    have h1 : F.map b ≫ θ.hom = F.map b' ≫ θ.hom := (A.homEquiv _ _).symm.injective hb
    exact hFF.map_injective ((cancel_mono θ.hom).mp h1)
  -- Frobenius reciprocity, read on sheaves
  let frob : (Q ⟶ (finiteTypeContinuousModuleCoind Λ H).obj M) →
      ((etaleModuleInverseImage.{u, 0} Λ φ.hom).obj (F.obj Q) ⟶
        (etaleModuleInverseImage.{u, 0} Λ φ.hom).obj FM) := fun a ↦
    P.hom.app Q ≫ FV.map (res.map a ≫ ev) ≫ P.inv.app M
  have hfrob : Function.Bijective frob := by
    have h1 := bijective_finiteTypeContinuousModuleCoindEval_comp Λ H
      (etaleFundamentalGroupMap φ.hom v) hφ hH Q M
    have h2 : Function.Bijective (fun t : res.obj Q ⟶ res.obj M ↦ FV.map t) :=
      hFFV.map_bijective (res.obj Q) (res.obj M)
    have h3 : Function.Bijective (fun t : FV.obj (res.obj Q) ⟶ FV.obj (res.obj M) ↦
        P.hom.app Q ≫ t ≫ P.inv.app M) :=
      ((P.app Q).symm.homCongr (P.app M).symm).bijective
    exact h3.comp (h2.comp h1)
  have hcomp : ∀ a, Ψ (a ≫ g) = frob a := by
    intro a
    have h1 : F.map (a ≫ g) ≫ θ.hom = F.map a ≫ c := by
      rw [Functor.map_comp, Category.assoc, hc]
    exact (congrArg (A.homEquiv _ _).symm h1).trans
      (homEquiv_symm_map_comp_representationSheafCoindComparison B φ Λ v H hφ a)
  exact ⟨fun a a' h ↦ hfrob.1 ((hcomp a).symm.trans ((congrArg Ψ h).trans (hcomp a'))),
    fun b ↦ (hfrob.2 (Ψ b)).imp fun a ha ↦ hΨ ((hcomp a).trans ha)⟩

/-- **`ℱ_{Coind_H M} ≅ φ_* φ^* ℱ_M`, naturally in `M`.** For a finite étale morphism `φ : V ⟶ X`
of connected schemes, a geometric point `v` of `V` and `H` the image of `π₁(V, v)` in
`π₁(X, φ(v))`, the sheaf of the coinduced module `Coind_H M = (π₁(X, φ(v)) ⧸ H → M)` is the direct
image of the inverse image of `ℱ_M`. -/
def representationSheafCoindIso [IsFinite φ.hom] [Etale φ.hom] :
    finiteTypeContinuousModuleCoind Λ H ⋙ representationSheaf B X (v.map φ.hom) Λ ≅
      representationSheaf B X (v.map φ.hom) Λ ⋙ etaleModuleInverseImage.{u, 0} Λ φ.hom ⋙
        etaleModuleDirectImage.{u, 0} Λ φ.hom :=
  haveI : ∀ M, IsIso ((representationSheafCoindComparison B φ Λ v H hφ).app M) :=
    isIso_representationSheafCoindComparison_app B φ Λ v H hφ hH
  haveI := NatIso.isIso_of_isIso_app (representationSheafCoindComparison B φ Λ v H hφ)
  asIso (representationSheafCoindComparison B φ Λ v H hφ)

/-- The forward map of `AlgebraicGeometry.representationSheafCoindIso` is
`AlgebraicGeometry.representationSheafCoindComparison`. -/
lemma representationSheafCoindIso_hom [IsFinite φ.hom] [Etale φ.hom] :
    (representationSheafCoindIso B φ Λ v H hφ hH).hom =
      representationSheafCoindComparison B φ Λ v H hφ :=
  rfl

end AlgebraicGeometry

end
