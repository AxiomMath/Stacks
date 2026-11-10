module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerWedgeDuality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge

/-!
# The wedge pairing is the transpose of the multiplication

Let `E` be a sheaf of graded algebras on a site. Its multiplication `E_i ⊗ E_j ⟶ E_{i+j}`
corresponds, under the tensor--internal-Hom correspondence of Stacks 03EO
(`Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv`), to the wedge pairing
`E_i ⟶ SheafHom(E_j, E_{i+j})`, `x ↦ (y ↦ x y)`, of
`Stacks.SheafOfModules.WedgeDuality.wedgeHom`. Consequently, when the wedge pairing is an
isomorphism (for instance for the exterior algebra of a finite locally free module of rank
`i + j`, `Stacks.SheafOfModules.WedgeDuality.isIso_wedgeHom`), the multiplication is a perfect
pairing at the level of sheaves: every morphism `T ⊗ E_j ⟶ E_{i+j}` is the multiplication after
`g ⊗ 1` for exactly one `g : T ⟶ E_i`.

## Main results

* `Stacks.SheafOfModules.WedgeDuality.sheafTensorHomEquiv_mulSheaf`: the transpose of the
  multiplication is the wedge pairing.
* `Stacks.SheafOfModules.WedgeDuality.bijective_map_app_comp_mulSheaf`: the multiplication is a
  perfect pairing of sheaves when the wedge pairing is an isomorphism.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf Opposite

noncomputable section

universe u

namespace Stacks.SheafOfModules.WedgeDuality

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

variable (E : _root_.SheafOfModules.GradedAlgebra.{u, u} (toRingCat J Osharp)) (i j : ℤ)

/-- **The transpose of the multiplication `E_i ⊗ E_j ⟶ E_{i+j}` is the wedge pairing**
`E_i ⟶ SheafHom(E_j, E_{i+j})`: both send a section `x` over `U` and a section `y` over `V ⟶ U`
to `x|_V · y`. -/
theorem sheafTensorHomEquiv_mulSheaf :
    Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv Osharp (E.piece i) (E.piece j)
        (E.piece (i + j)) (E.mulSheaf i j) = wedgeHom E i j := by
  refine _root_.SheafOfModules.hom_ext ?_
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  refine (Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply Osharp (E.piece i)
    (E.piece j) (E.piece (i + j)) (E.mulSheaf i j) U.unop x V.unop.hom y).trans ?_
  rw [Stacks.SheafOfModules.InternalHom.sheafifyForgetAdjunction_homEquiv Osharp
    (E.piece (i + j)) (MonoidalCategoryStruct.tensorObj (E.piece i).val (E.piece j).val)
    (E.mulSheaf i j)]
  exact _root_.SheafOfModules.GradedAlgebra.mulSheaf_unit E i j (op V.unop.left) _ y

/-- **The multiplication is a perfect pairing of sheaves when the wedge pairing is an
isomorphism**: every morphism `T ⊗ E_j ⟶ E_{i+j}` is `μ ∘ (g ⊗ 1)` for exactly one
`g : T ⟶ E_i`, `μ` the multiplication. -/
theorem bijective_map_app_comp_mulSheaf [IsIso (wedgeHom E i j)]
    (T : _root_.SheafOfModules.{u} (toRingCat J Osharp)) :
    Function.Bijective (fun g : T ⟶ E.piece i =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map g).app (E.piece j) ≫
        E.mulSheaf i j) := by
  let w := asIso (wedgeHom E i j)
  let φ := fun T' => Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv Osharp T' (E.piece j)
    (E.piece (i + j))
  have h : (fun g : T ⟶ E.piece i =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map g).app (E.piece j) ≫
        E.mulSheaf i j) = (φ T).symm ∘ (fun g => g ≫ w.hom) := by
    funext g
    refine ((φ T).eq_symm_apply).2 ?_
    change _ = g ≫ wedgeHom E i j
    rw [← sheafTensorHomEquiv_mulSheaf]
    exact (Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction Osharp
      (E.piece j)).homEquiv_naturality_left g (E.mulSheaf i j)
  rw [h]
  exact (φ T).symm.bijective.comp
    ⟨fun g g' e => (cancel_mono w.hom).1 e, fun g => ⟨g ≫ w.inv, (Category.assoc _ _ _).trans
      ((congrArg (g ≫ ·) w.inv_hom_id).trans (Category.comp_id g))⟩⟩

end Stacks.SheafOfModules.WedgeDuality
