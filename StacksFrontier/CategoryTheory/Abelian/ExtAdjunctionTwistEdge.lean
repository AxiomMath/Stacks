module

public import StacksFrontier.Algebra.Homology.RightDerivedEdgeComparison
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionTwistComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor

/-!
# The edge morphism of a right adjoint, read on `Ext` out of the unit

Let `Φ ⊣ Ψ` be an adjunction of exact endofunctors of an abelian monoidal category `𝒜`, with `Φ`
lax monoidal and `Ψ` preserving injective objects, and let `G : 𝒜 ⥤ Ab` be corepresented by the
unit `𝟙`. Given `σ : Ψ ⋙ G ⟶ G` compatible with the corepresentations (on maps out of `𝟙` it is
`f ↦ ε ≫ (adjoint of f)`, where `ε : 𝟙 ⟶ Φ 𝟙` is the unit of the lax structure), the composite

`RⁿG ∘ Ψ ⟶ Rⁿ(Ψ ⋙ G) ⟶ RⁿG`

of the edge morphism of `(Ψ, G)` with the map induced by `σ` is, under
`Ext^n(𝟙, -) ≅ RⁿG`, the map `Stacks.ExtCup.adjunctionExtMap : Ext^n(𝟙, Ψ N) ⟶ Ext^n(𝟙, N)`,
`b ↦ ε_N ∘ Φ(b)` (`whiskerLeft_comp_edge_comp_rightDerived_comp_inv`).

The edge morphism is the inverse of the comparison of Stacks 03FD
(`Stacks.Cohomology.RightDerivedEdge.edge_eq_comparisonIso_inv`), which on `Ext` is
`c ↦ Ψ(c) ∘ η_𝟙` (`Stacks.Cohomology.ModuleComparison.comparisonIso_hom_eq_extMapComp`); the map
induced by `σ` is precomposition with `ε`
(`ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality`); and `adjunctionExtMap` undoes
`c ↦ Ψ(c) ∘ η_𝟙` up to precomposition with `ε` (`Stacks.ExtCup.adjunctionExtMap_extMapCompHom`).

This is the step, in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH),
which identifies the canonical geometric Frobenius on `Hⁱ_c(X_k̄, K) = Ext^i(Λ, (j_! K)|)` with
the twisted action `Stacks.ExtCup.twistAction`.
-/

@[expose] public noncomputable section

universe v u

namespace Stacks.ExtCup

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
  ModuleSheafCohomology Stacks.Cohomology.ModuleComparison Stacks.Cohomology.RightDerivedEdge

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [HasExt.{v} C]
  [HasInjectiveResolutions C] [EnoughInjectives C]
  (Φ Ψ : C ⥤ C) [Φ.LaxMonoidal] [Φ.Additive] [PreservesFiniteLimits Φ]
  [PreservesFiniteColimits Φ] (adj : Φ ⊣ Ψ) [Ψ.Additive] [PreservesFiniteLimits Ψ]
  [PreservesFiniteColimits Ψ] [Ψ.PreservesInjectiveObjects]

/-- The corepresentation of `Ψ ⋙ Hom(𝟙, -)` by `Φ 𝟙` given by the adjunction. -/
abbrev adjCorepresentation :
    preadditiveCoyoneda.obj (op (Φ.obj (𝟙_ C))) ≅ Ψ ⋙ preadditiveCoyoneda.obj (op (𝟙_ C)) :=
  (Stacks.Cohomology.ExtComparison.compPreadditiveCoyonedaIso adj (𝟙_ C)).symm

omit [HasExt.{v} C] [HasInjectiveResolutions C] [EnoughInjectives C] [Φ.LaxMonoidal]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] [Ψ.Additive] [PreservesFiniteLimits Ψ]
  [PreservesFiniteColimits Ψ] [Ψ.PreservesInjectiveObjects] in
/-- The unit read off the corepresentation `adjCorepresentation` is the unit of the adjunction. -/
lemma compUnit_adjCorepresentation :
    compUnit Ψ (𝟙_ C) (Φ.obj (𝟙_ C)) (adjCorepresentation Φ Ψ adj) = adj.unit.app (𝟙_ C) := by
  change adj.homEquiv _ _ (𝟙 _) = _
  simp [Adjunction.homEquiv_unit]

variable (G : C ⥤ Ab.{v}) [G.Additive] [PreservesFiniteLimits G]
  (α : G ≅ preadditiveCoyoneda.obj (op (𝟙_ C)))

/-- **The edge morphism of `(Ψ, G)` followed by the map induced by `σ`, read on `Ext^n(𝟙, -)`, is
`Stacks.ExtCup.adjunctionExtMap`.** Here `σ : Ψ ⋙ G ⟶ G` is compatible with the corepresentations:
under `G ≅ Hom(𝟙, -)` and `Ψ ⋙ G ≅ Hom(Φ 𝟙, -)` it is precomposition with the lax unit
`ε : 𝟙 ⟶ Φ 𝟙`. -/
theorem extFunctorObjIsoRightDerived_inv_edge_rightDerived (σ : Ψ ⋙ G ⟶ G)
    (hσ : σ ≫ α.hom = (compCorepresentation Ψ G (𝟙_ C) α (Φ.obj (𝟙_ C))
      (adjCorepresentation Φ Ψ adj)).hom ≫
        preadditiveCoyoneda.map (Functor.LaxMonoidal.ε Φ).op) (n : ℕ) (M : C)
    (b : Ext.{v} (𝟙_ C) (Ψ.obj M) n) :
    ((extFunctorObjIsoRightDerived G (𝟙_ C) α n).inv.app M).hom
        (((NatTrans.rightDerived σ n).app M).hom (((edge Ψ G n).app M).hom
          (((extFunctorObjIsoRightDerived G (𝟙_ C) α n).hom.app (Ψ.obj M)).hom b))) =
      adjunctionExtMap Φ Ψ adj M b := by
  let β := adjCorepresentation Φ Ψ adj
  have h : ∀ (I : C) [Injective I] (n : ℕ) (e : Ext.{v} (𝟙_ C) (Ψ.obj I) (n + 1)), e = 0 :=
    fun _ _ _ e => Ext.eq_zero_of_injective e
  have hc := comparisonIso_hom_eq_extMapComp Ψ G (𝟙_ C) α (Φ.obj (𝟙_ C)) β h n
  rw [compUnit_adjCorepresentation] at hc
  have hnat := extFunctorObjIsoRightDerived_naturality (Functor.LaxMonoidal.ε Φ) α
    (compCorepresentation Ψ G (𝟙_ C) α (Φ.obj (𝟙_ C)) β) σ hσ n
  let e₁ := extFunctorObjIsoRightDerived (Ψ ⋙ G) (Φ.obj (𝟙_ C))
    (compCorepresentation Ψ G (𝟙_ C) α (Φ.obj (𝟙_ C)) β) n
  set ι := extFunctorObjIsoRightDerived G (𝟙_ C) α n
  let κ := comparisonIso Ψ G (𝟙_ C) α (Φ.obj (𝟙_ C)) β h n
  have hih : ∀ {F F' : C ⥤ Ab.{v}} (i : F ≅ F') (X : C) (y : F.obj X),
      (i.inv.app X).hom ((i.hom.app X).hom y) = y := fun i X y =>
    congrArg (fun f => AddCommGrpCat.Hom.hom f y) (i.hom_inv_id_app X)
  have hhi : ∀ {F F' : C ⥤ Ab.{v}} (i : F ≅ F') (X : C) (y : F'.obj X),
      (i.hom.app X).hom ((i.inv.app X).hom y) = y := fun i X y =>
    congrArg (fun f => AddCommGrpCat.Hom.hom f y) (i.inv_hom_id_app X)
  -- the class `c` with `Ψ(c) ∘ η_𝟙 = b`
  let c : Ext.{v} (Φ.obj (𝟙_ C)) M n :=
    (e₁.inv.app M).hom ((κ.inv.app M).hom ((ι.hom.app (Ψ.obj M)).hom b))
  have hκ : ∀ x, (κ.hom.app M).hom x = (ι.hom.app (Ψ.obj M)).hom
      (extMapCompHom Ψ (adj.unit.app (𝟙_ C)) n M ((e₁.inv.app M).hom x)) := fun x =>
    congrArg (fun f => AddCommGrpCat.Hom.hom f x) (NatTrans.congr_app hc M)
  have hb : extMapCompHom Ψ (adj.unit.app (𝟙_ C)) n M c = b := by
    have h1 := hκ ((κ.inv.app M).hom ((ι.hom.app (Ψ.obj M)).hom b))
    rw [hhi κ] at h1
    exact ((hih ι _ b).symm.trans ((congrArg (ι.inv.app (Ψ.obj M)).hom h1).trans (hih ι _ _))).symm
  have hedge : (edge Ψ G n).app M = κ.inv.app M :=
    NatTrans.congr_app (edge_eq_comparisonIso_inv Ψ G (𝟙_ C) α (Φ.obj (𝟙_ C)) β h n) M
  have hσc : ((NatTrans.rightDerived σ n).app M).hom ((e₁.hom.app M).hom c) =
      (ι.hom.app M).hom ((Ext.mk₀ (Functor.LaxMonoidal.ε Φ)).comp c (zero_add n)) :=
    (congrArg (fun f => AddCommGrpCat.Hom.hom f c) (NatTrans.congr_app hnat M)).symm
  have h3 := hκ ((e₁.hom.app M).hom c)
  rw [hih e₁] at h3
  rw [← hb, adjunctionExtMap_extMapCompHom Φ Ψ adj M c, hedge, ← h3, hih κ, hσc]
  exact hih ι _ _

end Stacks.ExtCup

end
