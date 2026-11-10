module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafEffacementCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveCompactSupportBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleCofinality
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.ImageStabilizer
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TransitiveFiberConnected
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.GaloisCategoryAxioms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian
public import StacksFrontier.AlgebraicGeometry.Curves.FiniteEtaleCoverConstantField

/-!
# `ℱ_ρ` becomes constant on a finite étale cover

Let `X` be a connected scheme with a geometric point `x`, `Λ` a finite ring and `M` a finite
`Λ`-module with a continuous action of `π₁(X, x)`. Some open normal subgroup `H` of `π₁(X, x)`
acts trivially on `M`; the connected Galois cover `Y ⟶ X` with group `π₁(X, x)/H` (Tag 0BND)
has fundamental group mapping into `H` (its image is a stabilizer,
`AlgebraicGeometry.range_etaleFundamentalGroupMap_eq_stabilizer`), so the restriction of `M` to
`π₁(Y)` is trivial and `ℱ_M|_Y` is the constant sheaf `M_Y` (Remark 0DV6 and
`AlgebraicGeometry.representationSheafTrivialIsoConstant`).

## Main results

* `AlgebraicGeometry.exists_finiteEtaleOver_transitive_stabilizer_le` — the Galois cover attached
  to an open normal subgroup.
* `AlgebraicGeometry.exists_finiteEtale_inverseImage_representationSheaf_iso_constant` — the
  trivialization of `ℱ_M`, for sheaves of `Λ`-modules.
* `AlgebraicGeometry.exists_finiteEtale_inverseImage_underlyingAbelian_iso_constant` — the same for
  the underlying abelian sheaf, with a finite constant value.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup Stacks.GroupCohomology
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry

section Galois

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)

/-- **The Galois cover attached to an open normal subgroup.** For an open subgroup `H` of
`π₁(X, x)` there is a finite étale cover `W` of `X` with a point `w` of its geometric fibre whose
orbit is the whole fibre and whose stabilizer is contained in `H`: the cover with fibre
`π₁(X, x)/H` (Tag 0BND). -/
theorem exists_finiteEtaleOver_transitive_stabilizer_le
    (H : OpenSubgroup (EtaleFundamentalGroup X x)) :
    ∃ (W : FiniteEtaleOver X) (w : (finiteEtaleFiberFunctor x).obj W),
      (∀ z, ∃ σ : EtaleFundamentalGroup X x, σ • w = z) ∧
        ∀ σ : EtaleFundamentalGroup X x, σ • w = w → σ ∈ H := by
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  let G := EtaleFundamentalGroup X x
  let Q0 := quotientContAction H
  let Q : ContAction FintypeCat.{u} G := quotientContActionSwitch H
  let e := FintypeCat.uSwitchEquiv Q0.obj.V
  let q₀ : Q.obj.V := e.symm (⟦1⟧ : G ⧸ H.toSubgroup)
  let E := finiteEtaleEquivalenceOfIsGaloisCategory X x
  let W := E.inverse.obj Q
  let c := E.counitIso.app Q
  let ψ : (finiteEtaleFiberFunctor x).obj W → Q.obj.V := fun w ↦
    ConcreteCategory.hom c.hom.hom.hom w
  let ψ' : Q.obj.V → (finiteEtaleFiberFunctor x).obj W := fun q ↦
    ConcreteCategory.hom c.inv.hom.hom q
  have hψψ' : ∀ q, ψ (ψ' q) = q := fun q ↦
    ConcreteCategory.congr_hom (congrArg (fun φ : Q ⟶ Q ↦ φ.hom.hom) c.inv_hom_id) q
  have hψ'ψ : ∀ w, ψ' (ψ w) = w := fun w ↦
    ConcreteCategory.congr_hom
      (congrArg (fun φ : E.functor.obj W ⟶ E.functor.obj W ↦ φ.hom.hom) c.hom_inv_id) w
  have hψ : ∀ (σ : G) (w : (finiteEtaleFiberFunctor x).obj W), ψ (σ • w) = σ • ψ w := by
    intro σ w
    have h : ConcreteCategory.hom c.hom.hom.hom
        (ConcreteCategory.hom ((E.functor.obj W).obj.ρ σ).asHom w) =
          ConcreteCategory.hom (Q.obj.ρ σ).asHom (ConcreteCategory.hom c.hom.hom.hom w) :=
      ConcreteCategory.congr_hom (c.hom.hom.comm σ) w
    rwa [finiteEtaleEquivalenceOfIsGaloisCategory_rho_apply] at h
  have htransQ : MulAction.IsPretransitive G Q.obj.V := by
    have : MulAction.IsPretransitive G Q0.obj.V := by
      let : MulAction G (G ⧸ H.toSubgroup) := MulAction.quotient G H.toSubgroup
      exact MulAction.isPretransitive_quotient G H.toSubgroup
    exact pretransitive_uSwitch (A := Q0.obj)
  have hstabQ : ∀ σ : G, σ • q₀ = q₀ → σ ∈ H := by
    intro σ hσ
    have h0 : (FintypeCat.uSwitch.map (Q0.obj.ρ σ).asHom) q₀ = q₀ := hσ
    have h1 := congrArg e h0
    rw [← FintypeCat.uSwitchEquiv_naturality] at h1
    have hq : e q₀ = (⟦1⟧ : G ⧸ H.toSubgroup) := Equiv.apply_symm_apply _ _
    rw [hq] at h1
    let : MulAction G (G ⧸ H.toSubgroup) := MulAction.quotient G H.toSubgroup
    change σ • (⟦1⟧ : G ⧸ H.toSubgroup) = ⟦1⟧ at h1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one] at h1
    simpa using (QuotientGroup.eq.mp h1)
  refine ⟨W, ψ' q₀, fun z ↦ ?_, fun σ hσ ↦ hstabQ σ ?_⟩
  · obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G q₀ (ψ z)
    exact ⟨σ, by rw [← hψ'ψ (σ • ψ' q₀), hψ, hψψ', hσ, hψ'ψ]⟩
  · rw [← hψψ' q₀, ← hψ, hσ]

end Galois

section Transport

variable {X : Scheme.{u}} [ConnectedSpace X] (Λ : Type) [Ring Λ]

/-- Moving a module along an equality of base points keeps the stabilizer condition. -/
theorem rho_eqRec_eq_one_of_smul_eq {x x' : GeometricPoint X} (h : x = x') (W : FiniteEtaleOver X)
    (w : (finiteEtaleFiberFunctor x).obj W) (w' : (finiteEtaleFiberFunctor x').obj W)
    (hw : HEq w'.1 w.1)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X x))
    (hM : ∀ σ : EtaleFundamentalGroup X x, σ • w = w → M.obj.obj.obj.ρ σ = 1)
    (σ : EtaleFundamentalGroup X x') (hσ : σ • w' = w') :
    (h ▸ M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
      (EtaleFundamentalGroup X x')).obj.obj.obj.ρ σ = 1 := by
  subst h
  obtain rfl : w' = w := Subtype.ext (eq_of_heq hw)
  exact hM σ hσ

/-- **A module on which `φ` acts trivially restricts to the trivial module.** -/
def finiteTypeContinuousModuleTrivialIsoRes {G H : Type (u + 1)} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (φ : G →ₜ* H)
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ H)
    (hM : ∀ g : G, M.obj.obj.obj.ρ (φ g) = 1) :
    (finiteTypeContinuousModuleTrivial Λ G).obj ⟨M.obj.obj.obj.V, M.property⟩ ≅
      (finiteTypeContinuousModuleRes Λ φ).obj M :=
  let f : (finiteTypeContinuousModuleTrivial Λ G).obj ⟨M.obj.obj.obj.V, M.property⟩ ⟶
      (finiteTypeContinuousModuleRes Λ φ).obj M :=
    ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
      { hom := 𝟙 _
        comm := fun g ↦ by
          change 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ (M.obj.obj.obj.ρ (φ g)).asHom
          rw [hM g]
          rfl }))
  haveI : IsIso f := isIso_of_bijective Λ G f Function.bijective_id
  asIso f

end Transport

section Trivialization

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ]

/-- Moving a module along an equality of base points does not change its sheaf. -/
theorem representationSheaf_obj_eqRec {x x' : GeometricPoint X.1} (h : x = x')
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    (representationSheaf B X x' Λ).obj (h ▸ M) = (representationSheaf B X x Λ).obj M := by
  subst h
  rfl

/-- **`ℱ_M` becomes constant on a surjective finite étale cover.** For a finite `Λ`-module `M`
with continuous `π₁(X, x)`-action there is a surjective finite étale `π : Y ⟶ X` with
`π^* ℱ_M ≅ E_Y` constant, `E` finite: take the connected Galois cover attached to an open normal
subgroup acting trivially on `M`. -/
theorem exists_finiteEtale_inverseImage_representationSheaf_iso_constant
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X.1) (_ : IsFinite π) (_ : Etale π) (_ : Surjective π)
      (E : ModuleCat.{u + 1} Λ) (_ : Finite E),
      Nonempty ((Stacks.EtaleCohomology.etaleModuleInverseImage.{u, 0} Λ π).obj
          ((representationSheaf B X x Λ).obj M) ≅
        (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E) := by
  have := forall_finite_finiteEtaleFiberFunctor_obj x
  obtain ⟨Hs, -, hHo, hHρ⟩ := exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Λ _ M
  obtain ⟨W, w, htrans, hstab⟩ := exists_finiteEtaleOver_transitive_stabilizer_le x ⟨Hs, hHo⟩
  have : ConnectedSpace W.left := connectedSpace_left_of_exists_smul_eq htrans
  have hf : finiteEtale W.hom := W.prop
  have : IsFinite W.hom := hf.1
  have : Etale W.hom := hf.2
  let t : GeometricPoint W.left := ⟨x.residueField, w.1⟩
  have ht : x = t.map W.hom := by
    change x = ⟨x.residueField, w.1 ≫ W.hom⟩
    rw [w.2]
  have : ConnectedSpace ((𝟭 Scheme).obj W.left) := inferInstanceAs (ConnectedSpace W.left)
  have : ConnectedSpace ((Functor.fromPUnit X.obj).obj W.right) :=
    inferInstanceAs (ConnectedSpace X.1)
  let Yb : B.Scheme := ⟨W.left, contains_of_locallyOfFiniteType_of_quasiCompact B W.hom X.2⟩
  let g : Yb ⟶ X := ObjectProperty.homMk W.hom
  let M' := (ht ▸ M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
    (EtaleFundamentalGroup X.1 (t.map g.hom)))
  have hM' : ∀ τ : EtaleFundamentalGroup W.left t,
      M'.obj.obj.obj.ρ (etaleFundamentalGroupMap W.hom t τ) = 1 := by
    intro τ
    have hmem : etaleFundamentalGroupMap W.hom t τ ∈
        MulAction.stabilizer (EtaleFundamentalGroup X.1 (t.map W.hom))
          (finiteEtaleOverSourcePoint hf t) := by
      rw [← range_etaleFundamentalGroupMap_eq_stabilizer]
      exact ⟨τ, rfl⟩
    exact rho_eqRec_eq_one_of_smul_eq Λ ht W w (finiteEtaleOverSourcePoint hf t) HEq.rfl M
      (fun σ hσ ↦ hHρ σ (hstab σ hσ)) _ hmem
  let E₀ : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ) :=
    ⟨M'.obj.obj.obj.V, M'.property⟩
  have : Module.Finite Λ E₀.obj := E₀.property
  have : Finite E₀.obj := Module.finite_of_finite Λ
  refine ⟨W.left, W.hom, inferInstance, inferInstance,
    ⟨fun z ↦ surjective_of_finiteEtale W z⟩, (ModuleCat.uliftFunctor.{0, u + 1} Λ).obj E₀.obj,
    inferInstanceAs (Finite (ULift _)), ⟨?_⟩⟩
  exact eqToIso (congrArg _ (representationSheaf_obj_eqRec B X Λ ht M).symm) ≪≫
    (representationSheafPullbackIso B g Λ t).app M' ≪≫
    (representationSheaf B Yb t Λ).mapIso
      (finiteTypeContinuousModuleTrivialIsoRes Λ (etaleFundamentalGroupMap g.hom t) M'
        hM').symm ≪≫
    (representationSheafTrivialIsoConstant B Yb t Λ).app E₀

end Trivialization

end AlgebraicGeometry

end
