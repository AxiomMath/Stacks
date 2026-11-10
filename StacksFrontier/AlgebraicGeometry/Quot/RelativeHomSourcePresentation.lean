module

public import StacksFrontier.CategoryTheory.Abelian.FilteredColimitRelationsDesc
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSourceColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward

/-!
# The relative Hom functor out of a module given by generators and relations

Let `F` be an `𝒪_X`-module, `E : I ⥤ Mod(𝒪_X)` a filtered diagram with a jointly epimorphic
cocone `π : E ⟶ F`, and for each `i` a family of morphisms `κ_{i, r} : P_r ⟶ E_i` generating the
kernel of `π_i`.  After pullback along any morphism `q : W ⟶ X`, a compatible family of
homomorphisms `q^*E_i ⟶ N` killing the `q^*κ_{i, r}` descends uniquely to `q^*F ⟶ N`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_modulePullback_desc_of_relations`: a compatible family of
  homomorphisms out of the pullbacks of the `E_i` killing the pullbacks of the relations descends
  uniquely to the pullback of `F`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

section ModuleLevel

attribute [local instance 5000] SheafOfModules.instAbelian

variable {I : Type u} [SmallCategory I] [IsFiltered I] (E : I ⥤ Modules.{u, u} B S hS X.1 X.2)
  {F : Modules.{u, u} B S hS X.1 X.2} (π : E ⟶ (Functor.const I).obj F)
  (hπ : ∀ {N : Modules.{u, u} B S hS X.1 X.2} (g : F ⟶ N), (∀ i, π.app i ≫ g = 0) → g = 0)
  {R : I → Type u} (P : ∀ i, R i → Modules.{u, u} B S hS X.1 X.2) (κ : ∀ i r, P i r ⟶ E.obj i)
  (hκπ : ∀ i r, κ i r ≫ π.app i = 0)
  (hκ : ∀ i {N : Modules.{u, u} B S hS X.1 X.2} (g : kernel (π.app i) ⟶ N),
    (∀ r, kernel.lift (π.app i) (κ i r) (hκπ i r) ≫ g = 0) → g = 0)

include hπ hκ in
/-- A compatible family of homomorphisms out of the pullbacks of the `E_i`, killing the pullbacks
of the relations, descends uniquely to the pullback of `F`. -/
theorem existsUnique_modulePullback_desc_of_relations {W : AlgebraicSpaces B S hS} (q : W ⟶ X)
    (N : Modules.{u, u} B S hS W.1 W.2)
    (ψ : ∀ i, (modulePullback B S hS q).obj (E.obj i) ⟶ N)
    (hcompat : ∀ {i j : I} (f : i ⟶ j), (modulePullback B S hS q).map (E.map f) ≫ ψ j = ψ i)
    (hkill : ∀ i r, (modulePullback B S hS q).map (κ i r) ≫ ψ i = 0) :
    ∃! φ : (modulePullback B S hS q).obj F ⟶ N,
      ∀ i, (modulePullback B S hS q).map (π.app i) ≫ φ = ψ i := by
  let := isGrothendieckAbelian_modules B S hS X.1 X.2
  have : IsConnected I := IsFiltered.isConnected I
  let adj := modulePullbackAdjunction B S hS q
  let ψ' : E ⟶ (Functor.const I).obj ((modulePushforward B S hS q).obj N) :=
    { app := fun i => adj.homEquiv _ _ (ψ i)
      naturality := fun i j f => by
        change E.map f ≫ adj.homEquiv _ _ (ψ j) = adj.homEquiv _ _ (ψ i) ≫ 𝟙 _
        rw [Category.comp_id, ← adj.homEquiv_naturality_left, hcompat] }
  have : (modulePullback B S hS q).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have hzero : ∀ {A : Modules.{u, u} B S hS X.1 X.2},
      adj.homEquiv A _ (0 : (modulePullback B S hS q).obj A ⟶ N) = 0 := by
    intro A
    have h := adj.homEquiv_naturality_left (0 : A ⟶ A) (0 : (modulePullback B S hS q).obj A ⟶ N)
    rwa [zero_comp, Functor.map_zero, zero_comp] at h
  have hψ' : ∀ i r, κ i r ≫ ψ'.app i = 0 := fun i r => by
    change κ i r ≫ adj.homEquiv _ _ (ψ i) = 0
    rw [← adj.homEquiv_naturality_left, hkill, hzero]
  obtain ⟨φ', hφ', huniq⟩ :=
    Abelian.existsUnique_desc_of_relations E π hπ P κ hκπ hκ ψ' hψ'
  refine ⟨(adj.homEquiv _ _).symm φ', fun i => ?_, fun φ hφ => ?_⟩
  · apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left]
    exact (congrArg (π.app i ≫ ·) ((adj.homEquiv _ _).apply_symm_apply φ')).trans (hφ' i)
  · apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    refine huniq _ fun i => ?_
    exact (adj.homEquiv_naturality_left (π.app i) φ).symm.trans
      (congrArg (adj.homEquiv _ _) (hφ i))

end ModuleLevel

end AlgebraicGeometry.Space

end
