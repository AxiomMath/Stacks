module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantFibreSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisCoverDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.PointedGaloisCovering
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafIrreducibleSectionsRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ChangeOfRings

/-!
# No constant simple quotient survives restriction of scalars

Let `C` be an irreducible, geometrically unibranch scheme, `ρ : Λ₀ →+* Λ` a morphism of
commutative rings with `Λ` Noetherian, and `N` a finite type locally constant sheaf of
`Λ`-modules on `C_étale` without constant simple quotient
(`Stacks.EtaleCohomology.HasNoConstantSimpleQuotient`): every morphism from `N` to the constant
sheaf on a simple `Λ`-module vanishes. Then every `Λ₀`-linear morphism from the restriction of
scalars `res_ρ N` to a constant sheaf of `Λ₀`-modules vanishes
(`Stacks.EtaleCohomology.eq_zero_of_hasNoConstantSimpleQuotient_restrictScalars`).

## Main results

* `Stacks.EtaleCohomology.constantSheaf_map_eq_id_of_irreducibleSpace`: over an irreducible
  étale `C`-scheme, every endomorphism acts trivially on the sections of a constant sheaf.
* `Stacks.EtaleCohomology.eq_zero_of_hasNoConstantSimpleQuotient_restrictScalars`: every morphism
  from `res_ρ N` to a constant sheaf of `Λ₀`-modules vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- The constant sections `M ⟶ M̲(U)` over an étale `C`-scheme `U`, the unit of sheafification. -/
abbrev constantSheafUnitApp {Λ : Type} [Ring Λ] {C : Scheme.{u}} (M : ModuleCat.{u + 1} Λ)
    (U : C.Etale) :
    M ⟶ ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.obj (op U) :=
  (toSheafify C.smallEtaleTopology ((Functor.const (C.Etale)ᵒᵖ).obj M)).app (op U)

/-- The constant sections are compatible with the restriction maps of the constant sheaf. -/
theorem constantSheafUnitApp_comp_map {Λ : Type} [Ring Λ] {C : Scheme.{u}} (M : ModuleCat.{u + 1} Λ)
    {U V : C.Etale} (g : V ⟶ U) :
    constantSheafUnitApp M U ≫
      ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.map
      g.op = constantSheafUnitApp M V := by
  have h := (toSheafify C.smallEtaleTopology ((Functor.const (C.Etale)ᵒᵖ).obj M)).naturality g.op
  exact h.symm.trans (Category.id_comp _)

/-- **Over an irreducible étale `C`-scheme, every endomorphism acts trivially on the sections of
a constant sheaf.** -/
theorem constantSheaf_map_eq_id_of_irreducibleSpace {Λ : Type} [Ring Λ] {C : Scheme.{u}}
    (M : ModuleCat.{u + 1} Λ) {U : C.Etale} [IrreducibleSpace U.left] (g : U ⟶ U) :
    ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M).obj.map g.op = 𝟙 _ := by
  have hb := Scheme.bijective_toSheafify_const_app_of_irreducibleSpace Λ M U
  ext s
  obtain ⟨m, rfl⟩ := hb.2 s
  exact ConcreteCategory.congr_hom (constantSheafUnitApp_comp_map M g) m

/-- An additive map invariant under a family of `Λ`-linear endomorphisms `τ i` kills the
`Λ`-submodule spanned by the `τ i s - s`. -/
theorem map_eq_zero_of_mem_span_sub {Λ : Type} [CommRing Λ] {V : Type*} [AddCommGroup V]
    [Module Λ V] {E : Type*} [AddCommGroup E]
    (f : V →+ E) {ι : Type*} (τ : ι → V →ₗ[Λ] V) (hf : ∀ i s, f (τ i s) = f s) {y : V}
    (hy : y ∈ Submodule.span Λ {z | ∃ i s, z = τ i s - s}) : f y = 0 := by
  have key : ∀ a : Λ, f (a • y) = 0 := by
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, s, rfl⟩ := hz
      intro a
      rw [smul_sub, ← (τ i).map_smul, map_sub, hf, sub_self]
    | zero => intro a; rw [smul_zero, map_zero]
    | add z w _ _ hz hw => intro a; rw [smul_add, map_add, hz, hw, add_zero]
    | smul b z _ hz => intro a; rw [smul_smul]; exact hz _
  simpa using key 1

/-- **A sheaf without constant simple quotient has no nonzero map, after restriction of scalars,
to a constant sheaf.** Let `C` be irreducible and geometrically unibranch, `ρ : Λ₀ →+* Λ` a
morphism of commutative rings with `Λ` Noetherian and `N` a finite type locally constant sheaf of
`Λ`-modules on `C_étale` such that every morphism from `N` to the constant sheaf on a simple
`Λ`-module vanishes. Then every morphism of sheaves of `Λ₀`-modules from `res_ρ N` to the constant
sheaf `E₀` vanishes. -/
theorem eq_zero_of_hasNoConstantSimpleQuotient_restrictScalars {Λ₀ Λ : Type} [CommRing Λ₀]
    [CommRing Λ] [IsNoetherianRing Λ] (ρ : Λ₀ →+* Λ) {C : Scheme.{u}} [IrreducibleSpace C]
    (hC : IsGeometricallyUnibranch C) (N : EtaleModules.{u, 0} Λ C)
    (hN : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ C.smallEtaleTopology N)
    (hNQ : HasNoConstantSimpleQuotient Λ N) (E₀ : ModuleCat.{u + 1} Λ₀)
    (φ : (etaleModuleRestrictScalars ρ C).obj N ⟶
      (constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ₀)).obj E₀) : φ = 0 := by
  have hCne : Nonempty C := IrreducibleSpace.toNonempty
  have hCconn : ConnectedSpace C :=
    connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ C).isConnected
  let x : GeometricPoint C := GeometricPoint.ofPoint C (Classical.arbitrary C)
  obtain ⟨A, M, hM, ⟨e⟩⟩ := trivializedByPointedGaloisCovers hC x Λ N hN
  let G := A.etaleGaloisCovering hC
  let W : C.Etale := G.cover
  have : IrreducibleSpace W.left := G.irreducibleSpace
  let J := C.smallEtaleTopology
  let e₀ : (constantSheaf (J.over W) (ModuleCat.{u + 1} Λ₀)).obj
        ((ModuleCat.restrictScalars.{u + 1} ρ).obj M) ≅
      (J.overPullback (ModuleCat.{u + 1} Λ₀) W).obj ((etaleModuleRestrictScalars ρ C).obj N) :=
    ((constantCommuteCompose (J.over W) (ModuleCat.restrictScalars.{u + 1} ρ)).app M).symm ≪≫
      (sheafCompose (J.over W) (ModuleCat.restrictScalars.{u + 1} ρ)).mapIso e
  refine G.hom_ext e₀ ?_
  let f := φ.hom.app (op W)
  have hf : ∀ (τ : Aut A.obj) (s : N.obj.obj (op W)), f (N.obj.map (G.actHom τ).op s) = f s := by
    intro τ s
    have h := ConcreteCategory.congr_hom (φ.hom.naturality (G.actHom τ).op) s
    change f (N.obj.map (G.actHom τ).op s) =
      (((constantSheaf J (ModuleCat.{u + 1} Λ₀)).obj E₀).obj.map (G.actHom τ).op) (f s) at h
    rw [h, constantSheaf_map_eq_id_of_irreducibleSpace E₀ (G.actHom τ)]
    rfl
  let τ : Aut A.obj → N.obj.obj (op W) →ₗ[Λ] N.obj.obj (op W) :=
    fun g => (N.obj.map (G.actHom g).op).hom
  let K : Submodule Λ (N.obj.obj (op W)) := Submodule.span Λ {z | ∃ i s, z = τ i s - s}
  let fA : N.obj.obj (op W) →+
      ((constantSheaf J (ModuleCat.{u + 1} Λ₀)).obj E₀).obj.obj (op W) := f.hom.toAddMonoidHom
  have hfK : ∀ y ∈ K, f y = 0 := fun y hy =>
    map_eq_zero_of_mem_span_sub (V := N.obj.obj (op W)) fA τ hf hy
  change f = 0
  by_contra hne'
  have hKtop : K ≠ ⊤ := by
    intro hK
    refine hne' (ModuleCat.hom_ext (LinearMap.ext fun y => ?_))
    exact hfK y (hK ▸ Submodule.mem_top)
  have : Module.Finite Λ (N.obj.obj (op W)) := Module.Finite.equiv (e.sectionsEquiv hC)
  obtain ⟨P, hP, hKP⟩ := (eq_top_or_exists_le_coatom K).resolve_left hKtop
  let E : ModuleCat.{u + 1} Λ := ModuleCat.of Λ (N.obj.obj (op W) ⧸ P)
  have hE : IsSimpleModule Λ E := (isSimpleModule_iff_isCoatom).2 hP
  let q : N.obj.obj (op W) ⟶ E := ModuleCat.ofHom P.mkQ
  let f' : N.obj.obj (op W) ⟶
      ((constantSheaf J (ModuleCat.{u + 1} Λ)).obj E).obj.obj (op W) := q ≫ constantSheafUnitApp E W
  have hf' : ∀ g : Aut A.obj, N.obj.map (G.actHom g).op ≫ f' =
      f' ≫ ((constantSheaf J (ModuleCat.{u + 1} Λ)).obj E).obj.map (G.actHom g).op := by
    intro g
    rw [constantSheaf_map_eq_id_of_irreducibleSpace E (G.actHom g), Category.comp_id]
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    change constantSheafUnitApp E W (P.mkQ (τ g s)) = constantSheafUnitApp E W (P.mkQ s)
    congr 1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact hKP (Submodule.subset_span ⟨g, s, rfl⟩)
  obtain ⟨ψ, hψ⟩ := G.exists_hom_app_cover_eq e f' hf'
  have hψ0 := hNQ E hE ψ
  obtain ⟨y, -, hy⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.2 hP.1)
  have hb := Scheme.bijective_toSheafify_const_app_of_irreducibleSpace Λ E W
  have h1 : f' y = 0 := by
    have : f' = 0 := by rw [← hψ, hψ0]; rfl
    rw [this]; rfl
  have h2 : q y = 0 := hb.1 (h1.trans (map_zero _).symm)
  exact hy ((Submodule.Quotient.mk_eq_zero P).1 h2)

end Stacks.EtaleCohomology

end
