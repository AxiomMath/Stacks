module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.FundamentalGroupTheorem
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.OpenSubgroups
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleConnectedObjects
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverSheets

/-!
# Finite étale covers with a prescribed geometric fibre

Let `X` be a connected scheme with a geometric point `x`. By Stacks 0BND (1) the fibre functor
`F_x` is an equivalence from finite étale covers of `X` to finite sets with a continuous action
of `π₁(X, x)`. This file records the two consequences used to build covers out of group theory:

* every finite set `S` with an action of `π₁(X, x)` with open stabilizers is, equivariantly, the
  geometric fibre of a finite étale cover (`exists_finiteEtaleOver_fiber_equiv`), with no
  restriction on the universe of `S`;
* every equivariant map between geometric fibres is induced by a morphism of covers
  (`exists_hom_of_equivariant`), uniquely (`finiteEtaleFiberFunctor_map_injective`).

In particular every open subgroup of `π₁(X, x)` is the stabilizer of a point of the fibre of a
finite étale cover (`exists_stabilizer_eq_of_isOpen`, Stacks 03VF (2)).
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped FintypeCatDiscrete

universe u w

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [ConnectedSpace X] (x : GeometricPoint X)

/-- The identification of a finite type `S` with a finite type in universe `u`. -/
def finiteShrinkEquiv (S : Type w) [Finite S] : S ≃ ULift.{u, 0} (Fin (Nat.card S)) :=
  (Finite.equivFin S).trans Equiv.ulift.{u, 0}.symm

/-- A finite set with an action of `π₁(X, x)`, transported to a finite type in universe `u`, as
an action of `π₁(X, x)` on an object of `FintypeCat`. -/
def finiteGSetAction (S : Type w) [MulAction (EtaleFundamentalGroup X x) S] [Finite S] :
    Action FintypeCat.{u} (EtaleFundamentalGroup X x) where
  V := FintypeCat.of (ULift.{u, 0} (Fin (Nat.card S)))
  ρ := { toFun := fun g => End.of <| FintypeCat.homMk fun t =>
            finiteShrinkEquiv.{u, w} S (g • (finiteShrinkEquiv.{u, w} S).symm t)
         map_one' := by
           apply End.ext
           apply FintypeCat.hom_ext
           intro t
           change finiteShrinkEquiv.{u, w} S ((1 : EtaleFundamentalGroup X x) •
             (finiteShrinkEquiv.{u, w} S).symm t) = t
           rw [one_smul, Equiv.apply_symm_apply]
         map_mul' := by
           intro g h
           apply End.ext
           apply FintypeCat.hom_ext
           intro t
           change finiteShrinkEquiv.{u, w} S ((g * h) • (finiteShrinkEquiv.{u, w} S).symm t) =
             finiteShrinkEquiv.{u, w} S (g • (finiteShrinkEquiv.{u, w} S).symm
               (finiteShrinkEquiv.{u, w} S (h • (finiteShrinkEquiv.{u, w} S).symm t)))
           rw [Equiv.symm_apply_apply, mul_smul] }

/-- Under the identification `finiteShrinkEquiv`, the action of `g` on `finiteGSetAction x S` is
the action of `g` on `S`. -/
theorem finiteGSetAction_ρ_apply (S : Type w) [MulAction (EtaleFundamentalGroup X x) S] [Finite S]
    (g : EtaleFundamentalGroup X x) (s : S) :
    ConcreteCategory.hom ((finiteGSetAction x S).ρ g).asHom (finiteShrinkEquiv.{u, w} S s) =
      finiteShrinkEquiv.{u, w} S (g • s) := by
  change finiteShrinkEquiv.{u, w} S
      (g • (finiteShrinkEquiv.{u, w} S).symm (finiteShrinkEquiv.{u, w} S s)) = _
  rw [Equiv.symm_apply_apply]

/-- If the stabilizers are open, `finiteGSetAction x S` is a continuous action. -/
def finiteGSetContAction (S : Type w) [MulAction (EtaleFundamentalGroup X x) S] [Finite S]
    (hS : ∀ s : S, IsOpen (MulAction.stabilizer (EtaleFundamentalGroup X x) s :
      Set (EtaleFundamentalGroup X x))) :
    ContAction FintypeCat.{u} (EtaleFundamentalGroup X x) := by
  refine ⟨finiteGSetAction x S, ?_⟩
  change (finiteGSetAction x S).IsContinuous
  rw [Action.isContinuous_def]
  have : DiscreteTopology ((forget₂ FintypeCat TopCat).obj (finiteGSetAction x S).V) :=
    inferInstanceAs (DiscreteTopology (finiteGSetAction x S).V)
  have : DiscreteTopology ((forget₂ (Action FintypeCat.{u} (EtaleFundamentalGroup X x)) TopCat).obj
      (finiteGSetAction x S)) :=
    inferInstanceAs (DiscreteTopology (finiteGSetAction x S).V)
  refine continuous_prod_of_discrete_right.2 fun t => ?_
  let : TopologicalSpace S := ⊥
  have : DiscreteTopology S := ⟨rfl⟩
  set s := (finiteShrinkEquiv.{u, w} S).symm t
  have hcont : Continuous fun g : EtaleFundamentalGroup X x => g • s := by
    refine continuous_discrete_rng.2 fun s' => ?_
    change IsOpen {g : EtaleFundamentalGroup X x | g • s = s'}
    by_cases h : ∃ g₀ : EtaleFundamentalGroup X x, g₀ • s = s'
    · obtain ⟨g₀, hg₀⟩ := h
      have : {g : EtaleFundamentalGroup X x | g • s = s'} =
          (fun g => g₀⁻¹ * g) ⁻¹' (MulAction.stabilizer (EtaleFundamentalGroup X x) s :
            Set (EtaleFundamentalGroup X x)) := by
        ext g
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe,
          MulAction.mem_stabilizer_iff, mul_smul]
        rw [inv_smul_eq_iff, hg₀]
      rw [this]
      exact (hS _).preimage (continuous_const.mul continuous_id)
    · rw [Set.eq_empty_of_forall_notMem fun g hg => h ⟨g, hg⟩]
      exact isOpen_empty
  have hc2 : @Continuous S ((forget₂ FintypeCat TopCat).obj (finiteGSetAction x S).V) _
      ((forget₂ FintypeCat TopCat).obj (finiteGSetAction x S).V).str
      fun s : S => finiteShrinkEquiv.{u, w} S s := continuous_of_discreteTopology
  refine (hc2.comp hcont).congr fun g => ?_
  change finiteShrinkEquiv.{u, w} S (g • s) =
    ConcreteCategory.hom ((finiteGSetAction x S).ρ g).asHom t
  rw [← finiteGSetAction_ρ_apply]
  exact congrArg _ ((finiteShrinkEquiv.{u, w} S).apply_symm_apply t)

/-- **A finite continuous `π₁(X, x)`-set is a geometric fibre**: for a finite set `S` with an
action of `π₁(X, x)` whose stabilizers are open there is a finite étale cover `Y` of `X` and an
equivariant bijection `F_x(Y) ≃ S`. -/
theorem exists_finiteEtaleOver_fiber_equiv (S : Type w) [MulAction (EtaleFundamentalGroup X x) S]
    [Finite S] (hS : ∀ s : S, IsOpen (MulAction.stabilizer (EtaleFundamentalGroup X x) s :
      Set (EtaleFundamentalGroup X x))) :
    ∃ (Y : FiniteEtaleOver X) (e : (finiteEtaleFiberFunctor x).obj Y ≃ S),
      ∀ (σ : EtaleFundamentalGroup X x) y, e (σ • y) = σ • e y := by
  let E := finiteEtaleEquivalenceOfIsGaloisCategory X x
  let M := finiteGSetContAction x S hS
  let e₀ := finiteShrinkEquiv.{u, w} S
  let Y := E.inverse.obj M
  let c : E.functor.obj Y ≅ M := E.counitIso.app M
  let f₀ : ToType (E.functor.obj Y).obj.V → ULift.{u, 0} (Fin (Nat.card S)) :=
    ConcreteCategory.hom c.hom.hom.hom
  let g₀ : ULift.{u, 0} (Fin (Nat.card S)) → ToType (E.functor.obj Y).obj.V :=
    ConcreteCategory.hom c.inv.hom.hom
  have hfg : ∀ t, f₀ (g₀ t) = t := fun t =>
    ConcreteCategory.congr_hom (congrArg (fun φ : M ⟶ M => φ.hom.hom) c.inv_hom_id) t
  have hgf : ∀ y, g₀ (f₀ y) = y := fun y =>
    ConcreteCategory.congr_hom
      (congrArg (fun φ : E.functor.obj Y ⟶ E.functor.obj Y => φ.hom.hom) c.hom_inv_id) y
  have hcomm : ∀ σ y, f₀ (ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ).asHom y) =
      ConcreteCategory.hom ((finiteGSetAction x S).ρ σ).asHom (f₀ y) := fun σ y =>
    ConcreteCategory.congr_hom (c.hom.hom.comm σ) y
  refine ⟨Y, ⟨fun y => e₀.symm (f₀ y), fun s => g₀ (e₀ s), fun y => ?_, fun s => ?_⟩,
    fun σ y => ?_⟩
  · change g₀ (e₀ (e₀.symm (f₀ y))) = y
    rw [Equiv.apply_symm_apply]
    exact hgf y
  · change e₀.symm (f₀ (g₀ (e₀ s))) = s
    rw [hfg, Equiv.symm_apply_apply]
  · change e₀.symm (f₀ ((σ.asIso.app Y).hom y)) = σ • e₀.symm (f₀ y)
    have hact := finiteEtaleEquivalenceOfIsGaloisCategory_action X x Y σ y
    change ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ).asHom y = (σ.asIso.app Y).hom y at hact
    rw [← hact]
    let y' : ToType (E.functor.obj Y).obj.V := y
    change e₀.symm (f₀ (ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ).asHom y')) =
      σ • e₀.symm (f₀ y')
    rw [hcomm]
    obtain ⟨s, hs⟩ := e₀.surjective (f₀ y')
    rw [← hs, Equiv.symm_apply_apply]
    change e₀.symm
        (ConcreteCategory.hom ((finiteGSetAction x S).ρ σ).asHom (finiteShrinkEquiv.{u, w} S s)) = _
    rw [finiteGSetAction_ρ_apply, Equiv.symm_apply_apply]

/-- **Equivariant maps of geometric fibres come from morphisms of covers.** -/
theorem exists_hom_of_equivariant {Y Y' : FiniteEtaleOver X}
    (f : (finiteEtaleFiberFunctor x).obj Y → (finiteEtaleFiberFunctor x).obj Y')
    (hf : ∀ (σ : EtaleFundamentalGroup X x) y, f (σ • y) = σ • f y) :
    ∃ g : Y ⟶ Y', ∀ y, (finiteEtaleFiberFunctor x).map g y = f y := by
  let E := finiteEtaleEquivalenceOfIsGaloisCategory X x
  let φ : E.functor.obj Y ⟶ E.functor.obj Y' :=
    ObjectProperty.homMk
      { hom := FintypeCat.homMk f
        comm := fun σ => by
          apply FintypeCat.hom_ext
          intro y
          have h1 := finiteEtaleEquivalenceOfIsGaloisCategory_action X x Y σ y
          have h2 := finiteEtaleEquivalenceOfIsGaloisCategory_action X x Y' σ (f y)
          change ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ).asHom y =
            (σ.asIso.app Y).hom y at h1
          change ConcreteCategory.hom ((E.functor.obj Y').obj.ρ σ).asHom (f y) =
            (σ.asIso.app Y').hom (f y) at h2
          change f (ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ).asHom y) =
            ConcreteCategory.hom ((E.functor.obj Y').obj.ρ σ).asHom (f y)
          rw [h1, h2]
          exact hf σ y }
  obtain ⟨g, hg⟩ := E.functor.map_surjective φ
  exact ⟨g, fun y => ConcreteCategory.congr_hom
    (congrArg (fun ψ : E.functor.obj Y ⟶ E.functor.obj Y' => ψ.hom.hom) hg) y⟩

/-- The geometric fibre functor is faithful. -/
theorem finiteEtaleFiberFunctor_map_injective {Y Y' : FiniteEtaleOver X} {g g' : Y ⟶ Y'}
    (h : ∀ y, (finiteEtaleFiberFunctor x).map g y = (finiteEtaleFiberFunctor x).map g' y) :
    g = g' := by
  apply (finiteEtaleEquivalenceOfIsGaloisCategory X x).functor.map_injective
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply FintypeCat.hom_ext
  exact h

/-- The stabilizers of the coset space of an open subgroup are open. -/
theorem isOpen_stabilizer_quotient (V : Subgroup (EtaleFundamentalGroup X x))
    (hV : IsOpen (V : Set (EtaleFundamentalGroup X x))) (s : EtaleFundamentalGroup X x ⧸ V) :
    IsOpen (MulAction.stabilizer (EtaleFundamentalGroup X x) s :
      Set (EtaleFundamentalGroup X x)) := by
  induction s using QuotientGroup.induction_on with | H g => ?_
  have : (MulAction.stabilizer (EtaleFundamentalGroup X x)
      (QuotientGroup.mk g : EtaleFundamentalGroup X x ⧸ V) : Set (EtaleFundamentalGroup X x)) =
      (fun h => g⁻¹ * h * g) ⁻¹' (V : Set (EtaleFundamentalGroup X x)) := by
    ext h
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_preimage]
    rw [show h • (QuotientGroup.mk g : EtaleFundamentalGroup X x ⧸ V) = QuotientGroup.mk (h * g)
      from rfl, QuotientGroup.eq, mul_inv_rev]
    constructor <;> intro h' <;> simpa [mul_assoc] using V.inv_mem h'
  rw [this]
  exact hV.preimage ((continuous_const.mul continuous_id).mul continuous_const)

/-- **Stacks 03VF (2): every open subgroup is a point stabilizer.** An open subgroup `V` of
`π₁(X, x)` is the stabilizer of a point of the geometric fibre of a finite étale cover. -/
theorem exists_stabilizer_eq_of_isOpen (V : Subgroup (EtaleFundamentalGroup X x))
    (hV : IsOpen (V : Set (EtaleFundamentalGroup X x))) :
    ∃ (Y : FiniteEtaleOver X) (y : (finiteEtaleFiberFunctor x).obj Y),
      MulAction.stabilizer (EtaleFundamentalGroup X x) y = V := by
  have : ∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y) := finite_finiteEtaleFiber x
  have : Finite (EtaleFundamentalGroup X x ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
  obtain ⟨Y, e, he⟩ := exists_finiteEtaleOver_fiber_equiv x (EtaleFundamentalGroup X x ⧸ V)
    (isOpen_stabilizer_quotient x V hV)
  refine ⟨Y, e.symm (QuotientGroup.mk 1), ?_⟩
  ext σ
  rw [MulAction.mem_stabilizer_iff, ← e.injective.eq_iff, he, Equiv.apply_symm_apply,
    show σ • (QuotientGroup.mk 1 : EtaleFundamentalGroup X x ⧸ V) = QuotientGroup.mk (σ * 1)
      from rfl, QuotientGroup.eq]
  constructor <;> intro h <;> simpa using V.inv_mem h

/-- **A cover with a nonempty fibre on which `π₁(X, x)` acts transitively is connected.** A
proper nonempty subobject would have a proper nonempty `π₁`-stable fibre. -/
theorem connectedSpace_left_of_isPretransitive (Y : FiniteEtaleOver X)
    (y₀ : (finiteEtaleFiberFunctor x).obj Y)
    (htrans : ∀ y : (finiteEtaleFiberFunctor x).obj Y,
      ∃ σ : EtaleFundamentalGroup X x, σ • y₀ = y) :
    ConnectedSpace Y.left := by
  have : ∀ Y, Finite ((finiteEtaleFiberFunctor x).obj Y) := finite_finiteEtaleFiber x
  let F := finiteEtaleFiberFintypeFunctor X x
  refine connectedSpace_left_of_isConnected Y ?_
  by_contra hc
  have hi : Limits.IsInitial Y → False := PreGaloisCategory.not_initial_of_inhabited F (X := Y) y₀
  obtain ⟨Z, v, hZ, hv, hniso⟩ :=
    PreGaloisCategory.has_non_trivial_subobject_of_not_isConnected_of_not_initial Y hc hi
  obtain ⟨z⟩ := (PreGaloisCategory.not_initial_iff_fiber_nonempty F Z).1 hZ
  have hlt := PreGaloisCategory.lt_card_fiber_of_mono_of_notIso F v hniso
  have hsurj : Function.Surjective ((finiteEtaleFiberFunctor x).map v) := by
    intro y
    obtain ⟨σ, hσ⟩ := htrans ((finiteEtaleFiberFunctor x).map v z)
    obtain ⟨τ, rfl⟩ := htrans y
    refine ⟨((τ * σ⁻¹).asIso.app Z).hom z, ?_⟩
    have h1 := NatTrans.naturality_apply ((τ * σ⁻¹).asIso.hom) v z
    change ((τ * σ⁻¹).asIso.app Y).hom ((finiteEtaleFiberFunctor x).map v z) =
      (finiteEtaleFiberFunctor x).map v (((τ * σ⁻¹).asIso.app Z).hom z) at h1
    rw [← h1]
    change (τ * σ⁻¹) • ((finiteEtaleFiberFunctor x).map v z) = τ • y₀
    rw [← hσ, smul_smul, inv_mul_cancel_right]
  have hle : Nat.card (F.obj Y) ≤ Nat.card (F.obj Z) :=
    Nat.card_le_card_of_surjective ((finiteEtaleFiberFunctor x).map v) hsurj
  exact absurd hlt (not_lt.2 hle)

end AlgebraicGeometry
