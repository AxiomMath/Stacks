module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveCoverConstantCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCoinduced
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTrivialization

/-!
# `H²(C, j_! ℱ_{N[π/H]}) = N`

Let `U` be a connected scheme with a geometric point `y`, `H` an open subgroup of `π₁(U, y)` and
`N` a finite module over a finite ring `Λ`. The induced module `N[π₁(U, y)/H]`, the functions
`π₁(U, y) ⧸ H → N` with `π₁(U, y)` translating the argument, has the sheaf
`ℱ_{N[π/H]} ≅ φ_*(N_V)` where `φ : V ⟶ U` is the connected finite étale cover with fundamental
group `H` (Tag 0BND). If `U` is an open with finite complement of a smooth proper curve `C` over an
algebraically closed field in which `#Λ` is invertible, then `H²(C, j_! ℱ_{N[π/H]}) ≅ N`.

This is the computation, on the modules `N[π/H]`, that the five-lemma argument for the
bijectivity of the map `H²_c(X_k̄, ℱ) → M_{π₁}` of Tag 03VK needs.

## Main results

* `AlgebraicGeometry.exists_finiteEtaleOver_transitive_stabilizer_eq` — the connected Galois cover
  attached to an open subgroup, with stabilizer exactly the subgroup.
* `AlgebraicGeometry.representationSheafCoindTrivialIso` — `ℱ_{N[π/H]} ≅ φ_*(N_V)`, naturally in
  `N`, for a cover whose fundamental group is `H`.
* `AlgebraicGeometry.nonempty_curveExtensionByZeroCoindTrace`,
  `AlgebraicGeometry.curveExtensionByZeroCoindTrace` — `H²(C, j_! ℱ_{N[π/H]}) ≃ₗ[Λ] N`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.FundamentalGroup Stacks.GroupCohomology
  Stacks.EtaleCohomology
open scoped FintypeCatDiscrete

universe u

namespace AlgebraicGeometry

attribute [local instance] compactSpace_etaleFundamentalGroup

section Galois

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)

/-- **The Galois cover attached to an open subgroup, with stabilizer exactly the subgroup.** For
an open subgroup `H` of `π₁(X, x)` there is a finite étale cover `W` of `X` with a point `w` of its
geometric fibre whose orbit is the whole fibre and whose stabilizer is `H`: the cover with fibre
`π₁(X, x)/H` (Tag 0BND). -/
theorem exists_finiteEtaleOver_transitive_stabilizer_eq
    (H : OpenSubgroup (EtaleFundamentalGroup X x)) :
    ∃ (W : FiniteEtaleOver X) (w : (finiteEtaleFiberFunctor x).obj W),
      (∀ z, ∃ σ : EtaleFundamentalGroup X x, σ • w = z) ∧
        ∀ σ : EtaleFundamentalGroup X x, σ • w = w ↔ σ ∈ H := by
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
  have hψ' : ∀ (σ : G) q, σ • ψ' q = ψ' (σ • q) := fun σ q ↦ by
    rw [← hψ'ψ (σ • ψ' q), hψ, hψψ']
  let : MulAction G (G ⧸ H.toSubgroup) := MulAction.quotient G H.toSubgroup
  have htransQ : MulAction.IsPretransitive G Q.obj.V := by
    have : MulAction.IsPretransitive G Q0.obj.V :=
      MulAction.isPretransitive_quotient G H.toSubgroup
    exact pretransitive_uSwitch (A := Q0.obj)
  have hq : e q₀ = (⟦1⟧ : G ⧸ H.toSubgroup) := Equiv.apply_symm_apply _ _
  have hstabQ : ∀ σ : G, σ • q₀ = q₀ ↔ σ ∈ H := by
    intro σ
    have key : σ • q₀ = q₀ ↔ σ • (⟦1⟧ : G ⧸ H.toSubgroup) = ⟦1⟧ := by
      show (FintypeCat.uSwitch.map (Q0.obj.ρ σ).asHom) q₀ = q₀ ↔ _
      rw [← e.apply_eq_iff_eq, ← FintypeCat.uSwitchEquiv_naturality, hq]
      rfl
    rw [key, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    simp
  refine ⟨W, ψ' q₀, fun z ↦ ?_, fun σ ↦ ?_⟩
  · obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq G q₀ (ψ z)
    exact ⟨σ, by rw [hψ', hσ, hψ'ψ]⟩
  · rw [← hstabQ σ]
    exact ⟨fun hσ ↦ by rw [← hψψ' q₀, ← hψ, hσ], fun hσ ↦ by rw [hψ', hσ]⟩

end Galois

section Trivial

variable (B : BigEtaleSite.{u}) {X V : B.Scheme} (φ : V ⟶ X) [ConnectedSpace X.1]
  [ConnectedSpace V.1] (Λ : Type) [Ring Λ] [Finite Λ] (v : GeometricPoint V.1)
  (H : OpenSubgroup (EtaleFundamentalGroup X.1 (v.map φ.hom)))
  (hφ : ∀ g, etaleFundamentalGroupMap φ.hom v g ∈ H)
  (hH : ∀ h ∈ H, ∃ g, etaleFundamentalGroupMap φ.hom v g = h)

/-- **`ℱ_{N[π/H]} ≅ φ_*(N_V)`, naturally in `N`.** For a finite étale morphism `φ : V ⟶ X` of
connected schemes, a geometric point `v` of `V` and `H` the image of `π₁(V, v)` in `π₁(X, φ(v))`,
the sheaf of the induced module `N[π/H] = Coind_H N` of a finite `Λ`-module `N` (with trivial
action) is the direct image of the constant sheaf `N_V`. -/
def representationSheafCoindTrivialIso [IsFinite φ.hom] [Etale φ.hom] :
    finiteTypeContinuousModuleTrivial Λ (EtaleFundamentalGroup X.1 (v.map φ.hom)) ⋙
        finiteTypeContinuousModuleCoind Λ H ⋙ representationSheaf B X (v.map φ.hom) Λ ≅
      ObjectProperty.ι _ ⋙ ModuleCat.uliftFunctor.{0, u + 1} Λ ⋙
        constantSheaf V.1.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        etaleModuleDirectImage.{u, 0} Λ φ.hom :=
  Functor.isoWhiskerLeft _ (representationSheafCoindIso B φ Λ v H hφ hH) ≪≫
    Functor.isoWhiskerRight (representationSheafTrivialIsoConstant B X (v.map φ.hom) Λ)
      (etaleModuleInverseImage.{u, 0} Λ φ.hom ⋙ etaleModuleDirectImage.{u, 0} Λ φ.hom) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _ ⋙ ModuleCat.uliftFunctor.{0, u + 1} Λ)
      (Functor.isoWhiskerRight (etaleModuleInverseImageConstantIso.{u, 0} Λ φ.hom)
        (etaleModuleDirectImage.{u, 0} Λ φ.hom))

end Trivial

section Curve

/- The cohomology groups here are those of
`Stacks.EtaleCohomology.curveExtensionByZeroConstantTrace`, built in the standard model of the
derived category. -/
attribute [local instance] HasDerivedCategory.standard etaleModulesEnoughInjectivesZero

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] (y : GeometricPoint U.1)
  (H : OpenSubgroup (EtaleFundamentalGroup U.1 y))
  {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (jC : U.1 ⟶ C) [IsOpenImmersion jC]

include q hn hζ in
/-- **`H²(C, j_! ℱ_{N[π/H]}) ≃ N`** for an open `j : U ⟶ C` of a smooth proper curve over an
algebraically closed field, a geometric point `y` of `U` (connected), an open subgroup `H` of
`π₁(U, y)` and a finite module `N` over a finite ring `Λ` of order invertible in the field:
`ℱ_{N[π/H]} = φ_*(N_V)` for the connected cover `φ : V ⟶ U` with group `H`, and
`H²(C, j_! φ_* N_V) = N` through the compactification of `V`. -/
theorem nonempty_curveExtensionByZeroCoindTrace
    (N : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    Nonempty (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((representationSheaf B U y Λ).obj ((finiteTypeContinuousModuleCoind Λ H).obj
            ((finiteTypeContinuousModuleTrivial Λ _).obj N)))) ≃ₗ[Λ] N.obj) := by
  obtain ⟨W, w, htrans, hstab⟩ := exists_finiteEtaleOver_transitive_stabilizer_eq y H
  have : ConnectedSpace W.left := connectedSpace_left_of_exists_smul_eq htrans
  have hf : finiteEtale W.hom := W.prop
  have : IsFinite W.hom := W.prop.1
  have : Etale W.hom := W.prop.2
  let Vb : B.Scheme := ⟨W.left, contains_of_locallyOfFiniteType_of_quasiCompact B W.hom U.2⟩
  let g : Vb ⟶ U := ObjectProperty.homMk W.hom
  have : ConnectedSpace Vb.1 := inferInstanceAs (ConnectedSpace W.left)
  have : IsFinite g.hom := inferInstanceAs (IsFinite W.hom)
  have : Etale g.hom := inferInstanceAs (Etale W.hom)
  let t : GeometricPoint Vb.1 := ⟨y.residueField, w.1⟩
  have hy : t.map g.hom = y := by
    show (⟨y.residueField, w.1 ≫ W.hom⟩ : GeometricPoint U.1) = y
    rw [w.2]
  have : Module.Finite Λ N.obj := N.property
  have : Finite N.obj := Module.finite_of_finite Λ
  have : Finite ((ModuleCat.uliftFunctor.{0, u + 1} Λ).obj ((ModuleCat.isFG Λ).ι.obj N)) :=
    inferInstanceAs (Finite (ULift N.obj))
  -- generalize the base point, so that it can be substituted by `t.map g`
  suffices key : ∀ (y' : GeometricPoint U.1) (_ : t.map g.hom = y')
      (H' : OpenSubgroup (EtaleFundamentalGroup U.1 y')) (w' : (finiteEtaleFiberFunctor y').obj W)
      (_ : HEq w'.1 w.1) (_ : ∀ σ : EtaleFundamentalGroup U.1 y', σ • w' = w' ↔ σ ∈ H'),
      Nonempty (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((representationSheaf B U y' Λ).obj ((finiteTypeContinuousModuleCoind Λ H').obj
            ((finiteTypeContinuousModuleTrivial Λ _).obj N)))) ≃ₗ[Λ] N.obj) from
    key y hy H w HEq.rfl hstab
  intro y' hy' H' w' hw' hstab'
  subst hy'
  obtain rfl : w' = finiteEtaleOverSourcePoint hf t := Subtype.ext (eq_of_heq hw')
  -- `H'` is the image of `π₁(V, t)`
  have hrange := range_etaleFundamentalGroupMap_eq_stabilizer (f := g.hom) hf t
  have hmem : ∀ σ, σ ∈ (etaleFundamentalGroupMap g.hom t).toMonoidHom.range ↔ σ ∈ H' := by
    intro σ
    rw [hrange, MulAction.mem_stabilizer_iff]
    exact hstab' σ
  have hφ : ∀ τ, etaleFundamentalGroupMap g.hom t τ ∈ H' := fun τ ↦ (hmem _).mp ⟨τ, rfl⟩
  have hH : ∀ h ∈ H', ∃ τ, etaleFundamentalGroupMap g.hom t τ = h := fun h hh ↦ (hmem h).mpr hh
  exact ⟨(((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).mapIso
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).mapIso
        ((representationSheafCoindTrivialIso B g Λ t H' hφ hH).app N))).toLinearEquiv.trans
    ((curveExtensionByZeroDirectImageConstantTrace q Λ hn hζ jC g.hom _).trans
      ULift.moduleEquiv)⟩

/-- **`H²(C, j_! ℱ_{N[π/H]}) ≃ₗ[Λ] N`**, a choice of the isomorphism of
`AlgebraicGeometry.nonempty_curveExtensionByZeroCoindTrace`. -/
def curveExtensionByZeroCoindTrace (N : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    ((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
          ((representationSheaf B U y Λ).obj ((finiteTypeContinuousModuleCoind Λ H).obj
            ((finiteTypeContinuousModuleTrivial Λ _).obj N)))) ≃ₗ[Λ] N.obj :=
  Classical.choice (nonempty_curveExtensionByZeroCoindTrace B U y H q Λ hn hζ jC N)

end Curve

end AlgebraicGeometry

end
