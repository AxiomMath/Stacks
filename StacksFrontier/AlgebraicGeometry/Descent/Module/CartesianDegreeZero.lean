module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianTransport

/-!
# Morphisms of cartesian cosimplicial modules are determined in degree zero

Let `R` be a cosimplicial commutative ring, seen as a presheaf of commutative rings on
`SimplexCategoryᵒᵖ`, and let `M`, `N` be cartesian `R`-modules, so that every transition map
`M_n ⟶ M_m` induces an isomorphism `R_m ⊗_{R_n} M_n ≅ M_m`.  Then `M_n` is generated, as an
`R_n`-module, by the image of `M_0` under any vertex map `⦋0⦌ ⟶ ⦋n⦌`, and a morphism `M ⟶ N` is
the same as a map `g₀ : M_0 ⟶ N_0` which, after transport along the two vertices of `⦋1⦌`, gives
one and the same map `M_1 ⟶ N_1`.

## Main definitions

* `Stacks.PresheafOfModules.homOfDegreeZero`: the morphism `M ⟶ N` of cartesian modules
  determined by `g₀ : M_0 ⟶ N_0` and a map `g₁ : M_1 ⟶ N_1` compatible with `g₀` along both
  cofaces `⦋0⦌ ⟶ ⦋1⦌`.

## Main results

* `Stacks.PresheafOfModules.homOfDegreeZero_app_zero`: its degree-zero component is `g₀`.
* `Stacks.PresheafOfModules.hom_ext_of_cartesian`: a morphism out of a cartesian module is
  determined by its degree-zero component.
* `Stacks.PresheafOfModules.isIso_of_cartesian_of_isIso_app_zero`: a morphism of cartesian
  modules which is an isomorphism in degree zero is an isomorphism.

## Implementation notes

The degree-`n` component of `homOfDegreeZero` is read off from the vertex `0 : ⦋0⦌ ⟶ ⦋n⦌`.
Compatibility with an arbitrary vertex `i` is obtained through the edge `0 ⟶ i` of `⦋n⦌`, and
naturality for an arbitrary `β : ⦋n⦌ ⟶ ⦋m⦌` is checked on the generators of `M_n`; both steps
use only that semilinear maps out of `M_n` are determined on the image of `M_0`
(`Stacks.PresheafOfModules.hom_ext_of_isIso_restrictionBaseChange`).

## References

* [Stacks Project, Tag 039Y](https://stacks.math.columbia.edu/tag/039Y)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open scoped ChangeOfRings

universe r m

namespace Stacks.PresheafOfModules

section Generation

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- Two successive restriction maps are the restriction map of the composite. -/
theorem map_map_eq {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h)
    (x : M.obj X) : (M.map g (M.map f x) : M.obj Z) = M.map h x := by
  subst hfg
  exact (M.map_comp_apply f g x).symm

/-- **A map out of `M Y` is determined on the image of `M X`** when `M` is cartesian along
`f : X ⟶ Y`. -/
theorem hom_ext_of_isIso_restrictionBaseChange {X Y : Cᵒᵖ} (f : X ⟶ Y)
    [IsIso (restrictionBaseChange M f)] {P : ModuleCat.{max m r} (R.obj Y)}
    (φ₁ φ₂ : M.obj Y ⟶ P) (h : ∀ x : M.obj X, φ₁ (M.map f x) = φ₂ (M.map f x)) : φ₁ = φ₂ :=
  (cancel_epi (restrictionBaseChange M f)).mp <| ModuleCat.ExtendScalars.hom_ext fun x =>
    (congrArg φ₁ (restrictionBaseChange_one_tmul M f x)).trans
      ((h x).trans (congrArg φ₂ (restrictionBaseChange_one_tmul M f x)).symm)

end Generation

variable {R : SimplexCategoryᵒᵖᵒᵖ ⥤ CommRingCat.{r}}

/-- The vertex `0` of `⦋n⦌`. -/
abbrev vertexZero (n : SimplexCategory) : ⦋0⦌ ⟶ n := SimplexCategory.const _ n 0

/-- The edge `0 ⟶ i` of `⦋n⦌`. -/
abbrev edgeFromZero {n : ℕ} (i : Fin (n + 1)) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkOfLe 0 i (Fin.zero_le i)

/-- The coface `δ 1 : ⦋0⦌ ⟶ ⦋1⦌` followed by the edge `0 ⟶ i` is the vertex `0` of `⦋n⦌`. -/
theorem delta_one_comp_edgeFromZero {n : ℕ} (i : Fin (n + 1)) :
    SimplexCategory.δ 1 ≫ edgeFromZero i = vertexZero ⦋n⦌ :=
  SimplexCategory.Hom.ext_zero_left _ _ rfl

/-- The coface `δ 0 : ⦋0⦌ ⟶ ⦋1⦌` followed by the edge `0 ⟶ i` is the vertex `i` of `⦋n⦌`. -/
theorem delta_zero_comp_edgeFromZero {n : ℕ} (i : Fin (n + 1)) :
    SimplexCategory.δ 0 ≫ edgeFromZero i = SimplexCategory.const _ ⦋n⦌ i :=
  SimplexCategory.Hom.ext_zero_left _ _ rfl

/-- Two successive restriction maps along simplicial morphisms are the restriction map of the
composite. -/
private theorem map_map_op_op_eq (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y Z : SimplexCategory} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h)
    (x : M.obj (op (op X))) : M.map g.op.op (M.map f.op.op x) = M.map h.op.op x :=
  map_map_eq M _ _ _ (congrArg (fun g => g.op.op) hfg) x

variable {M N : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
  (hM : cartesianModules R M) (hN : cartesianModules R N)

include hM in
/-- `Stacks.PresheafOfModules.hom_ext_of_isIso_restrictionBaseChange` for a cartesian module. -/
theorem hom_ext_of_cartesian {X Y : SimplexCategoryᵒᵖᵒᵖ} (f : X ⟶ Y)
    {P : ModuleCat.{max m r} (R.obj Y)}
    (φ₁ φ₂ : M.obj Y ⟶ P) (h : ∀ x : M.obj X, φ₁ (M.map f x) = φ₂ (M.map f x)) : φ₁ = φ₂ :=
  have := hM f
  hom_ext_of_isIso_restrictionBaseChange M f φ₁ φ₂ h

/-- The degree-`n` component determined by a degree-zero map `g₀`, read off from the vertex `0`:
`R_n ⊗ M_0 ≅ M_n` and `R_n ⊗ N_0 ≅ N_n` conjugate the base change of `g₀`. -/
noncomputable def degreeComponent (g₀ : M.obj (op (op ⦋0⦌)) ⟶ N.obj (op (op ⦋0⦌)))
    (n : SimplexCategory) : M.obj (op (op n)) ⟶ N.obj (op (op n)) :=
  have := hM (vertexZero n).op.op
  inv (restrictionBaseChange M (vertexZero n).op.op) ≫
    (ModuleCat.extendScalars (R.map (vertexZero n).op.op).hom).map g₀ ≫
      restrictionBaseChange N (vertexZero n).op.op

/-- The degree-`n` component sends the image of `x : M_0` under the vertex `0` to the image of
`g₀ x` under the vertex `0`. -/
theorem degreeComponent_map_vertexZero (g₀ : M.obj (op (op ⦋0⦌)) ⟶ N.obj (op (op ⦋0⦌)))
    (n : SimplexCategory) (x : M.obj (op (op ⦋0⦌))) :
    degreeComponent hM g₀ n (M.map (vertexZero n).op.op x) =
      N.map (vertexZero n).op.op (g₀ x) := by
  have := hM (vertexZero n).op.op
  exact (congrArg (fun t => restrictionBaseChange N (vertexZero n).op.op
      ((ModuleCat.extendScalars (R.map (vertexZero n).op.op).hom).map g₀
        (inv (restrictionBaseChange M (vertexZero n).op.op) t)))
      (restrictionBaseChange_one_tmul M (vertexZero n).op.op x).symm).trans <|
    (congrArg (fun t => restrictionBaseChange N (vertexZero n).op.op
      ((ModuleCat.extendScalars (R.map (vertexZero n).op.op).hom).map g₀ t))
      (CategoryTheory.IsIso.hom_inv_id_apply (restrictionBaseChange M (vertexZero n).op.op)
        _)).trans <|
    (congrArg (restrictionBaseChange N (vertexZero n).op.op)
      (ModuleCat.ExtendScalars.map_tmul (R.map (vertexZero n).op.op).hom g₀ 1 x)).trans
      (restrictionBaseChange_one_tmul N _ _)

variable (g₀ : M.obj (op (op ⦋0⦌)) ⟶ N.obj (op (op ⦋0⦌)))
  (g₁ : M.obj (op (op ⦋1⦌)) ⟶ N.obj (op (op ⦋1⦌)))
  (h₁ : ∀ x, g₁ (M.map (SimplexCategory.δ (n := 0) 1).op.op x) =
    N.map (SimplexCategory.δ (n := 0) 1).op.op (g₀ x))
  (h₀ : ∀ x, g₁ (M.map (SimplexCategory.δ (n := 0) 0).op.op x) =
    N.map (SimplexCategory.δ (n := 0) 0).op.op (g₀ x))

include h₁ in
/-- The degree-`n` component is compatible with the edges `0 ⟶ i` of `⦋n⦌`. -/
theorem degreeComponent_map_edgeFromZero {n : ℕ} (i : Fin (n + 1)) (y : M.obj (op (op ⦋1⦌))) :
    degreeComponent hM g₀ ⦋n⦌ (M.map (edgeFromZero i).op.op y) =
      N.map (edgeFromZero i).op.op (g₁ y) := by
  have key := hom_ext_of_cartesian hM (SimplexCategory.δ (n := 0) 1).op.op
    (M.map (edgeFromZero i).op.op ≫
      (ModuleCat.restrictScalars (R.map (edgeFromZero i).op.op).hom).map
        (degreeComponent hM g₀ ⦋n⦌))
    (g₁ ≫ N.map (edgeFromZero i).op.op) fun x =>
      (congrArg (degreeComponent hM g₀ ⦋n⦌)
          (map_map_op_op_eq M (delta_one_comp_edgeFromZero i) x)).trans <|
        (degreeComponent_map_vertexZero hM g₀ ⦋n⦌ x).trans <|
          (map_map_op_op_eq N (delta_one_comp_edgeFromZero i) (g₀ x)).symm.trans
            (congrArg (N.map (edgeFromZero i).op.op) (h₁ x)).symm
  exact ConcreteCategory.congr_hom key y

include h₁ h₀ in
/-- The degree-`n` component is compatible with every vertex of `⦋n⦌`. -/
theorem degreeComponent_map_vertex {n : ℕ} (w : ⦋0⦌ ⟶ ⦋n⦌) (x : M.obj (op (op ⦋0⦌))) :
    degreeComponent hM g₀ ⦋n⦌ (M.map w.op.op x) = N.map w.op.op (g₀ x) := by
  have hw : SimplexCategory.δ 0 ≫ edgeFromZero (w.toOrderHom 0) = w :=
    (delta_zero_comp_edgeFromZero _).trans (SimplexCategory.eq_const_of_zero w).symm
  exact (congrArg (degreeComponent hM g₀ ⦋n⦌) (map_map_op_op_eq M hw x).symm).trans <|
    (degreeComponent_map_edgeFromZero hM g₀ g₁ h₁ (n := n) _ _).trans <|
      (congrArg (N.map (edgeFromZero (w.toOrderHom 0)).op.op) (h₀ x)).trans
        (map_map_op_op_eq N hw (g₀ x))

include h₁ h₀ in
/-- The degree components are natural. -/
theorem degreeComponent_naturality {n m : SimplexCategory} (β : n ⟶ m) :
    M.map β.op.op ≫ (ModuleCat.restrictScalars (R.map β.op.op).hom).map
        (degreeComponent hM g₀ m) =
      degreeComponent hM g₀ n ≫ N.map β.op.op := by
  obtain ⟨n⟩ := n
  obtain ⟨m⟩ := m
  refine hom_ext_of_cartesian hM (vertexZero ⦋n⦌).op.op _ _ fun x => ?_
  change degreeComponent hM g₀ ⦋m⦌ (M.map β.op.op (M.map (vertexZero ⦋n⦌).op.op x)) =
    N.map β.op.op (degreeComponent hM g₀ ⦋n⦌ (M.map (vertexZero ⦋n⦌).op.op x))
  rw [degreeComponent_map_vertexZero, ← PresheafOfModules.map_comp_apply,
    ← PresheafOfModules.map_comp_apply, ← op_comp, ← op_comp,
    degreeComponent_map_vertex hM g₀ g₁ h₁ h₀, op_comp, op_comp,
    PresheafOfModules.map_comp_apply]

/-- **The morphism of cartesian modules determined in degree zero.**  A map `g₀ : M_0 ⟶ N_0`
which, transported along the two cofaces `⦋0⦌ ⟶ ⦋1⦌`, gives one and the same map
`g₁ : M_1 ⟶ N_1`, extends to a morphism `M ⟶ N`. -/
noncomputable def homOfDegreeZero : M ⟶ N where
  app X := degreeComponent hM g₀ X.unop.unop
  naturality f := degreeComponent_naturality hM g₀ g₁ h₁ h₀ f.unop.unop

include h₁ h₀ in
/-- The component of `homOfDegreeZero` in degree `n` sends the image of `x : M_0` under a vertex
`w : ⦋0⦌ ⟶ ⦋n⦌` to the image of `g₀ x` under `w`. -/
theorem homOfDegreeZero_app_vertex {n : ℕ} (w : ⦋0⦌ ⟶ ⦋n⦌) (x : M.obj (op (op ⦋0⦌))) :
    (homOfDegreeZero hM g₀ g₁ h₁ h₀).app (op (op ⦋n⦌)) (M.map w.op.op x) =
      N.map w.op.op (g₀ x) :=
  degreeComponent_map_vertex hM g₀ g₁ h₁ h₀ w x

/-- The degree-zero component of `homOfDegreeZero` is `g₀`. -/
theorem homOfDegreeZero_app_zero :
    (homOfDegreeZero hM g₀ g₁ h₁ h₀).app (op (op ⦋0⦌)) = g₀ := by
  refine hom_ext_of_cartesian hM (𝟙 _) _ _ fun x => ?_
  have := homOfDegreeZero_app_vertex hM g₀ g₁ h₁ h₀ (𝟙 _) x
  rw [op_id, op_id] at this
  rw [this, PresheafOfModules.map_id, PresheafOfModules.map_id]
  rfl

/-- The degree-one component of `homOfDegreeZero` is `g₁`. -/
theorem homOfDegreeZero_app_one :
    (homOfDegreeZero hM g₀ g₁ h₁ h₀).app (op (op ⦋1⦌)) = g₁ :=
  hom_ext_of_cartesian hM (SimplexCategory.δ (n := 0) 1).op.op _ _ fun x =>
    (homOfDegreeZero_app_vertex hM g₀ g₁ h₁ h₀ (n := 1) (SimplexCategory.δ 1) x).trans
      (h₁ x).symm

include hM in
/-- **A morphism out of a cartesian module is determined by its degree-zero component.** -/
theorem hom_ext_of_cartesian_app_zero {φ ψ : M ⟶ N}
    (h : φ.app (op (op ⦋0⦌)) = ψ.app (op (op ⦋0⦌))) : φ = ψ := by
  refine PresheafOfModules.hom_ext fun X => ?_
  obtain ⟨⟨n⟩⟩ := X
  refine hom_ext_of_cartesian hM (vertexZero n).op.op _ _ fun x => ?_
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, h]

include hM hN in
/-- **A morphism of cartesian modules which is an isomorphism in degree zero is an
isomorphism.** -/
theorem isIso_of_cartesian_of_isIso_app_zero (φ : M ⟶ N) [IsIso (φ.app (op (op ⦋0⦌)))] :
    IsIso φ := by
  have hφ : ∀ X, IsIso (φ.app X) := by
    rintro ⟨⟨n⟩⟩
    have := hM (vertexZero n).op.op
    have := hN (vertexZero n).op.op
    have h := restrictionBaseChange_naturality φ (vertexZero n).op.op
    have : IsIso (restrictionBaseChange M (vertexZero n).op.op ≫ φ.app (op (op n))) := by
      rw [← h]
      infer_instance
    exact IsIso.of_isIso_comp_left (restrictionBaseChange M (vertexZero n).op.op) _
  exact (PresheafOfModules.isoMk (fun X => asIso (φ.app X))
    (fun _ _ f => φ.naturality f)).isIso_hom

end Stacks.PresheafOfModules

end
