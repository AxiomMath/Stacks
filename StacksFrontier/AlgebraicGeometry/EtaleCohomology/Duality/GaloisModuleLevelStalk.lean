module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.GaloisModuleStalkTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryInertiaInvariantsLevels

/-!
# The Galois module of a pulled-back level of `ℱ_ρ` over a field

Let `X` be a connected scheme with a base geometric point `x̄`, `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)`
continuous, `ℱₙ` the `n`-th level of the ℓ-adic sheaf `ℱ_ρ` read on Mathlib's small étale site,
`φ : Y ⟶ X`, and `h : Spec K ⟶ Y` for a field `K`. The Galois module at a geometric point `t̄`
of `Spec K` (Stacks 04JQ) of the abelian sheaf `h⁻¹ (φ⁻¹ ℱₙ)` is `(ℤ/ℓⁿ⁺¹)^r`, through a path
`p` from `φ(h(t̄))` to `x̄`, and a Galois automorphism `σ`, extended to an automorphism `τ` of the
field of `t̄`, acts on it as `ρ mod ℓⁿ⁺¹` of the element of `π₁(X, x̄)` that `p` transports the
automorphism `Spec τ` of `φ(h(t̄))` to (Stacks 03Q1, 03QT, 0DV5).

## Main definitions

* `Stacks.EtaleCohomology.levelPullbackGaloisModule` — the Galois module.

## Main results

* `Stacks.EtaleCohomology.exists_levelPullbackGaloisModule_addEquiv` — the identification with
  `(ℤ/ℓⁿ⁺¹)^r` and the action.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] GeometricPoint.residueFieldAlgebra

/-! ### Transporting a commutation along an isomorphism of abelian groups -/

section Transport

variable {X Y : AddCommGrpCat.{u + 1}} (e : X ≅ Y) {f : X ⟶ X} {g : Y ⟶ Y}

/-- If `g ≫ e.inv = e.inv ≫ f`, then `e.hom` intertwines `f` and `g` on elements. -/
theorem iso_hom_apply_of_comp_inv (hfg : g ≫ e.inv = e.inv ≫ f) (y : X) :
    ConcreteCategory.hom e.hom (ConcreteCategory.hom f y) =
      ConcreteCategory.hom g (ConcreteCategory.hom e.hom y) := by
  have h1 := ConcreteCategory.congr_hom hfg (ConcreteCategory.hom e.hom y)
  simp only [ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at h1
  rw [← h1, Iso.inv_hom_id_apply]

/-- If `e.hom ≫ g = f ≫ e.hom`, then `e.inv` intertwines `g` and `f` on elements. -/
theorem iso_inv_apply_of_hom_comp (hfg : e.hom ≫ g = f ≫ e.hom) (z : Y) :
    ConcreteCategory.hom e.inv (ConcreteCategory.hom g z) =
      ConcreteCategory.hom f (ConcreteCategory.hom e.inv z) :=
  iso_hom_apply_of_comp_inv e.symm hfg.symm z

/-- Intertwining is preserved by composing additive equivalences. -/
theorem addEquiv_trans_apply_intertwine {A B C : Type*} [Add A] [Add B] [Add C] (e₁ : A ≃+ B)
    (e₂ : B ≃+ C) {fA : A → A} {fB : B → B} {fC : C → C} (h₁ : ∀ a, e₁ (fA a) = fB (e₁ a))
    (h₂ : ∀ b, e₂ (fB b) = fC (e₂ b)) (a : A) : (e₁.trans e₂) (fA a) = fC ((e₁.trans e₂) a) := by
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, h₁, h₂]

end Transport

/-- An automorphism of a geometric point `t̄` fixes `φ(h(t̄))`. -/
theorem comp_map_map_hom_eq {X Y Z : Scheme.{u}} (φ : Y ⟶ Z) (h : X ⟶ Y) (sbar : GeometricPoint X)
    {α : sbar.source ≅ sbar.source} (hαt : α.hom ≫ sbar.hom = sbar.hom) :
    α.hom ≫ ((sbar.map h).map φ).hom = ((sbar.map h).map φ).hom := by
  change α.hom ≫ (sbar.hom ≫ h) ≫ φ = (sbar.hom ≫ h) ≫ φ
  rw [← Category.assoc, ← Category.assoc, hαt]

/-- The Galois module in the coefficient category of continuous group cohomology and the module
of Tag 04JQ have the same underlying abelian group. -/
def etaleContinuousGModuleAddEquiv (B : BigEtaleSite.{u}) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K)))
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1}) :
    ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj F).obj.obj.V ≃+
      (etaleGaloisModule.{u, u + 1} B K hK sbar F).obj.obj.V :=
  continuousGModuleCounitAddEquiv _

/-- `etaleContinuousGModuleAddEquiv` is equivariant for the Galois actions. -/
theorem etaleContinuousGModuleAddEquiv_rho (B : BigEtaleSite.{u}) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K)))
    (F : Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1})
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (v : ((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj F).obj.obj.V) :
    etaleContinuousGModuleAddEquiv B K hK sbar F
        ((((etaleContinuousGModuleEquivalence.{u, u + 1} B K hK sbar).functor.obj F).obj.obj.ρ
          σ).asHom.hom v) =
      ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B K hK sbar F).obj.obj.ρ σ).asHom
        (etaleContinuousGModuleAddEquiv B K hK sbar F v) :=
  continuousGModuleCounitAddEquiv_rho _ σ v

section Level

variable (B : BigEtaleSite.{u}) (V : B.Scheme) [ConnectedSpace V.1] (x : GeometricPoint V.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian V.1]
  (ρ : EtaleFundamentalGroup V.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
  {Y : Scheme.{u}} (φ : Y ⟶ V.1) {K : Type u} [Field K] (h : Spec (.of K) ⟶ Y)
  (B'' : BigEtaleSite.{u}) (hK : B''.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K))) (n : ℕ)

/-- **The Galois module of `h⁻¹ φ⁻¹ ℱₙ` at `t̄`**, for the `n`-th level `ℱₙ` of `ℱ_ρ`. -/
abbrev levelPullbackGaloisModule :=
  (etaleContinuousGModuleEquivalence.{u, u + 1} B'' K hK sbar).functor.obj
    ((smallEtaleSheafRestriction B'' K hK).obj
      ((smallEtalePullbackAb h).obj
        ((etaleModuleForgetAb.{u, 0} (ZMod (ℓ ^ (n + 1))) Y).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1))) φ).obj
            (LAdicSheaf.etaleLevel B V ℓ (representationLAdicSheaf B V x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) ρ hρ) n)))))

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- **The Galois module of `h⁻¹ φ⁻¹ ℱₙ` is `(ℤ/ℓⁿ⁺¹)^r`, with the Galois action through `ρ`.** For
a path `p` from `φ(h(t̄))` to `x̄`, a Galois automorphism `σ` at `t̄` with an extension `τ` to the
field of `t̄` acts as `ρ mod ℓⁿ⁺¹` of the image under `p` of the automorphism `Spec τ` of
`φ(h(t̄))`. -/
theorem exists_levelPullbackGaloisModule_addEquiv
    (p : finiteEtaleFiberFunctor ((sbar.map h).map φ) ≅ finiteEtaleFiberFunctor x) :
    ∃ Θ : (levelPullbackGaloisModule B V x ρ hρ φ h B'' hK sbar n).obj.obj.V ≃+
        (Fin r → ZMod (ℓ ^ (n + 1))),
      ∀ (σ : GeometricPoint.absoluteGaloisGroup sbar)
        (τ : Gal(sbar.residueField / (Spec (.of K)).residueField (sbar.hom default)))
        (_ : ∀ a : GeometricPoint.separableClosure sbar,
          (σ a : sbar.residueField) = τ (a : sbar.residueField))
        (α : sbar.source ≅ sbar.source) (_ : α.hom = Spec.map (CommRingCat.ofHom τ.toRingHom))
        (hαt : α.hom ≫ sbar.hom = sbar.hom)
        (v : (levelPullbackGaloisModule B V x ρ hρ φ h B'' hK sbar n).obj.obj.V),
        Θ (((levelPullbackGaloisModule B V x ρ hρ φ h B'' hK sbar n).obj.obj.ρ σ).asHom.hom v) =
          levelRepresentation ρ (n + 1) (etaleFundamentalGroupMulEquiv p
            (GeometricPoint.sourceAutElement (S := V.1) ((sbar.map h).map φ) α
              (comp_map_map_hom_eq φ h sbar hαt))) (Θ v) := by
  let Λ := ZMod (ℓ ^ (n + 1))
  let Fρ := representationLAdicSheaf B V x
    (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) ρ hρ
  let L0 : Sheaf (SmallEtale.topology B V.1 V.2) (ModuleCat.{u + 1} Λ) := Fρ.level n
  let N0 := LAdicSheaf.etaleLevel B V ℓ Fρ n
  let G := (etaleModuleInverseImage.{u, 0} Λ φ).obj N0
  let NA := (etaleModuleForgetAb.{u, 0} Λ Y).obj G
  let Fk := (smallEtalePullbackAb h).obj NA
  let FB := (smallEtaleSheafRestriction B'' K hK).obj Fk
  let E := (abelianEtaleStalkEquivalence.{u, u + 1} B'' K hK sbar).functor.obj FB
  let w := (sbar.map h).map φ
  let I2 := (pointSmallEtaleSheafFiberIsoAb B'' (Spec (.of K)) hK sbar).app Fk
  let I3 := (smallEtaleStalkPullbackAbIso h sbar.hom).app NA
  let I4 := ((pointSmallEtale (sbar.map h).hom).sheafFiberCompIso
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app G
  let I5 := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
    ((etaleModuleStalkPullbackIso Λ φ (sbar.map h).hom).app N0)
  let I6 := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapIso
    ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B V Λ w).app L0)
  let I7 := representationLevelStalkIso B V x ρ hρ p (n + 1)
  let Θ₀ := etaleContinuousGModuleAddEquiv B'' K hK sbar FB
  let Θ₁ := etaleGaloisModuleAddEquivStalk.{u, u + 1} B'' K hK sbar FB
  let R7 := I7.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift
  let R6 := I6.addCommGroupIsoToAddEquiv.trans R7
  let R5 := I5.addCommGroupIsoToAddEquiv.trans R6
  let R4 := I4.addCommGroupIsoToAddEquiv.trans R5
  let R3 := I3.addCommGroupIsoToAddEquiv.trans R4
  let R2 := I2.symm.addCommGroupIsoToAddEquiv.trans R3
  let R1 := Θ₁.trans R2
  refine ⟨Θ₀.trans R1, ?_⟩
  intro σ τ hτ α hα hαt v
  let a : GeometricPoint.Hom sbar sbar := ⟨α.hom, hαt⟩
  let b : GeometricPoint.Hom w w := (a.map h).map φ
  have c0 : ∀ y, Θ₀ (((levelPullbackGaloisModule B V x ρ hρ φ h B'' hK sbar n).obj.obj.ρ
      σ).asHom.hom y) =
      ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B'' K hK sbar FB).obj.obj.ρ σ).asHom
        (Θ₀ y) :=
    etaleContinuousGModuleAddEquiv_rho B'' K hK sbar FB σ
  have c1 : ∀ y, Θ₁ (ConcreteCategory.hom ((etaleGaloisModule.{u, u + 1} B'' K hK sbar FB).obj.obj.ρ
      σ).asHom y) = ConcreteCategory.hom ((geometricPointStalkMap B'' (Spec (.of K)) hK a
        AddCommGrpCat.{u + 1}).app FB.obj) (Θ₁ y) :=
    etaleGaloisModuleAddEquivStalk_rho B'' K hK sbar FB σ τ hτ a hα
  have c2 : ∀ z, I2.symm.addCommGroupIsoToAddEquiv (ConcreteCategory.hom ((geometricPointStalkMap
      B'' (Spec (.of K)) hK a AddCommGrpCat.{u + 1}).app FB.obj) z) =
      ConcreteCategory.hom ((smallEtalePointHom (Spec (.of K)) a).sheafFiber.app Fk)
        (I2.symm.addCommGroupIsoToAddEquiv z) := iso_inv_apply_of_hom_comp I2
    (pointSmallEtaleSheafFiberIsoAb_hom_naturality B'' (Spec (.of K)) hK a Fk)
  have c3 : ∀ z, I3.addCommGroupIsoToAddEquiv (ConcreteCategory.hom
      ((smallEtalePointHom (Spec (.of K)) a).sheafFiber.app Fk) z) =
      ConcreteCategory.hom ((smallEtalePointHom Y (a.map h)).sheafFiber.app NA)
        (I3.addCommGroupIsoToAddEquiv z) := iso_hom_apply_of_comp_inv I3
    (smallEtalePointHom_sheafFiber_comp_smallEtaleStalkPullbackAbIso_inv h a NA)
  have c4 : ∀ z, I4.addCommGroupIsoToAddEquiv (ConcreteCategory.hom
      ((smallEtalePointHom Y (a.map h)).sheafFiber.app NA) z) =
      ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((smallEtalePointHom Y (a.map h)).sheafFiber.app G)) (I4.addCommGroupIsoToAddEquiv z) :=
    ConcreteCategory.congr_hom
        (sheafFiber_app_sheafFiberCompIso_forget₂ Λ (smallEtalePointHom Y (a.map h)) G)
  have h5 := congrArg (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
    (smallEtalePointHom_sheafFiber_comp_etaleModuleStalkPullbackIso_inv φ (a.map h) Λ N0)
  rw [Functor.map_comp, Functor.map_comp] at h5
  have c5 : ∀ z, I5.addCommGroupIsoToAddEquiv (ConcreteCategory.hom
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((smallEtalePointHom Y (a.map h)).sheafFiber.app G)) z) =
      ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((smallEtalePointHom V.1 b).sheafFiber.app N0)) (I5.addCommGroupIsoToAddEquiv z) :=
    iso_hom_apply_of_comp_inv I5 h5
  have h6₀ := congrArg (fun η => η.app L0)
    (sheafEquivCompSheafFiberIso_inv_naturality.{u, u + 1, 0} B V Λ b)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h6₀
  have c6 : ∀ z, I6.addCommGroupIsoToAddEquiv (ConcreteCategory.hom
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((smallEtalePointHom V.1 b).sheafFiber.app N0)) z) =
      ConcreteCategory.hom ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((geometricPointStalkMap B V.1 V.2 b (ModuleCat.{u + 1} Λ)).app L0.obj))
        (I6.addCommGroupIsoToAddEquiv z) := iso_hom_apply_of_comp_inv I6
    (g := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
      ((geometricPointStalkMap B V.1 V.2 b (ModuleCat.{u + 1} Λ)).app L0.obj))
    (f := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
      ((smallEtalePointHom V.1 b).sheafFiber.app
        ((SmallEtale.sheafEquiv B V.1 V.2 (ModuleCat.{u + 1} Λ)).functor.obj L0)))
    (by
      change _ ≫ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B V Λ w).inv.app L0) =
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          ((sheafEquivCompSheafFiberIso.{u, u + 1, 0} B V Λ w).inv.app L0) ≫ _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ h6₀.symm)
  have c7 : ∀ z, R7 (ConcreteCategory.hom
      ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        ((geometricPointStalkMap B V.1 V.2 b (ModuleCat.{u + 1} Λ)).app L0.obj)) z) =
      levelRepresentation ρ (n + 1) (etaleFundamentalGroupMulEquiv p
        (GeometricPoint.sourceAutElement (S := V.1) ((sbar.map h).map φ) α
          (comp_map_map_hom_eq φ h sbar hαt)))
        (R7 z) :=
    representationLevelStalkIso_geometricPointStalkMap B V x ρ hρ p b
      (GeometricPoint.sourceAutElement (S := V.1) w α (comp_map_map_hom_eq φ h sbar hαt))
      (GeometricPoint.sourceAutElement_hom_eq_finiteEtaleFiberMap w α _ b rfl) (n + 1)
  have d6 := addEquiv_trans_apply_intertwine I6.addCommGroupIsoToAddEquiv R7 c6 c7
  have d5 := addEquiv_trans_apply_intertwine I5.addCommGroupIsoToAddEquiv R6 c5 d6
  have d4 := addEquiv_trans_apply_intertwine I4.addCommGroupIsoToAddEquiv R5 c4 d5
  have d3 := addEquiv_trans_apply_intertwine I3.addCommGroupIsoToAddEquiv R4 c3 d4
  have d2 := addEquiv_trans_apply_intertwine I2.symm.addCommGroupIsoToAddEquiv R3 c2 d3
  have d1 := addEquiv_trans_apply_intertwine Θ₁ R2 c1 d2
  exact addEquiv_trans_apply_intertwine Θ₀ R1 c0 d1 v

end Level

end Stacks.EtaleCohomology

end
