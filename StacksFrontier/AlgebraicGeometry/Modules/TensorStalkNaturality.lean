module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkGenerators
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge

/-!
# Naturality of the stalk of a tensor product in its left factor

Let `X` be a scheme and `G` a sheaf of `𝒪_X`-modules. Tensoring on the right by `G` turns a
morphism `f : A ⟶ B` of `𝒪_X`-modules into `f ⊗ 1 : A ⊗ G ⟶ B ⊗ G`, and the identification of
the stalk of a tensor product with the tensor product of the stalks carries the stalk map of
`f ⊗ 1` to `(-) ⊗ 1` applied to the stalk map of `f`. That naturality is proved here, together
with the three consequences it is used through: tensoring preserves surjectivity, vanishing and
injectivity of a stalk map.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tensorRightMap`: the morphism `f ⊗ 1 : A ⊗ G ⟶ B ⊗ G`.

## Main results

* `AlgebraicGeometry.tensorStalkEquiv_tensorRightMap`: the naturality square, stating that the
  comparison of the stalk of a tensor product with the tensor product of the stalks transforms
  the stalk map of `f ⊗ 1` into `LinearMap.rTensor` of the stalk map of `f`.
* `AlgebraicGeometry.surjective_stalkLinearMap_tensorRightMap`,
  `AlgebraicGeometry.stalkLinearMap_tensorRightMap_eq_zero` and
  `AlgebraicGeometry.injective_stalkLinearMap_tensorRightMap`: a stalk map that is surjective,
  zero, or bijective stays surjective, zero, or injective after tensoring on the right.

## Implementation notes

The comparison is pinned down only on the germs of pure tensors of local sections, so the
naturality square is proved by evaluating both sides on such germs and extending by linearity:
an element of the stalk of `A ⊗ G` is the image under the comparison's inverse of an element of
`A_x ⊗ G_x`, which is a sum of pure tensors of germs, and two germs can be represented on one
common neighbourhood by restricting to the intersection of two.

Every step that crosses the boundary between `TopCat.Sheaf CommRingCat X` and
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat` is written in term mode, since
the two spellings of a scheme's structure sheaf are not identified at the `implicit`
transparency level and a rewrite across that boundary does not fire.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Tensoring a morphism `f : A ⟶ B` of `𝒪_X`-modules on the right by `G`, as a morphism
`A ⊗_{𝒪_X} G ⟶ B ⊗_{𝒪_X} G`. -/
def Scheme.Modules.tensorRightMap {A B : X.Modules} (f : A ⟶ B) (G : X.Modules) :
    Scheme.Modules.tensorObj A G ⟶ Scheme.Modules.tensorObj B G :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(X).presheaf, (X).IsSheaf⟩).map f).app G

/-- Tensoring on the right by `G` sends the image of a pure tensor of local sections to the
image of the pure tensor of the image of the first factor. -/
theorem stalkLinearMap_tensorRightMap_tensorSheafGerm {A B : X.Modules} (f : A ⟶ B)
    (G : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (m : A.val.obj (op U)) (n : G.val.obj (op U)) :
    stalkLinearMap _ _ (Scheme.Modules.tensorRightMap f G) x
        (PresheafOfModules.tensorSheafGerm X.sheaf A G x U hx m n) =
      PresheafOfModules.tensorSheafGerm X.sheaf B G x U hx (f.val.app (op U) m) n :=
  (stalkLinearMap_germ (Scheme.Modules.tensorObj A G) (Scheme.Modules.tensorObj B G)
      (Scheme.Modules.tensorRightMap f G) U x hx _).trans
    (congrArg (ConcreteCategory.hom ((Scheme.Modules.tensorObj B G).presheaf.germ U x hx))
      ((PresheafOfModules.unit_naturality_apply
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
        (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj)
        (PresheafOfModules.tensorHom (O := X.presheaf) f.val (𝟙 G.val))
        (op U) (m ⊗ₜ n)).trans
        (congrArg ((PresheafOfModules.tensorSheafUnit B G).app (op U))
          (PresheafOfModules.tensorHom_tmul (O := X.presheaf) f.val (𝟙 G.val)
            (op U) m n))))

/-- **Naturality of Tag 01CB in the left factor.** The identification of the stalk of
`A ⊗_{𝒪_X} G` with `A_x ⊗_{𝒪_{X,x}} G_x` carries the stalk map of `f ⊗ 1` to the right tensor
product of the stalk map of `f` with `G_x`. -/
theorem tensorStalkEquiv_tensorRightMap {A B : X.Modules} (f : A ⟶ B) (G : X.Modules) (x : X)
    (z : (Scheme.Modules.tensorObj A G).presheaf.stalk x) :
    tensorStalkEquiv B G x (stalkLinearMap _ _ (Scheme.Modules.tensorRightMap f G) x z) =
      LinearMap.rTensor (G.presheaf.stalk x) (stalkLinearMap A B f x)
        (tensorStalkEquiv A G x z) := by
  obtain ⟨w, rfl⟩ : ∃ w, (tensorStalkEquiv A G x).symm w = z :=
    ⟨tensorStalkEquiv A G x z, (tensorStalkEquiv A G x).symm_apply_apply z⟩
  rw [LinearEquiv.apply_symm_apply]
  induction w using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | tmul p q =>
      obtain ⟨U, hxU, m, hm⟩ := A.presheaf.exists_germ_eq p
      obtain ⟨V, hxV, n, hn⟩ := G.presheaf.exists_germ_eq q
      have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
      let m' : A.val.obj (op (U ⊓ V)) :=
        A.val.map (homOfLE (inf_le_left (a := U) (b := V))).op m
      let n' : G.val.obj (op (U ⊓ V)) :=
        G.val.map (homOfLE (inf_le_right (a := U) (b := V))).op n
      have hpm : A.presheaf.germ (U ⊓ V) x hxW m' = p :=
        (A.presheaf.germ_res_apply _ x hxW m).trans hm
      have hqn : G.presheaf.germ (U ⊓ V) x hxW n' = q :=
        (G.presheaf.germ_res_apply _ x hxW n).trans hn
      have key : (tensorStalkEquiv A G x).symm (p ⊗ₜ q) =
          PresheafOfModules.tensorSheafGerm X.sheaf A G x (U ⊓ V) hxW m' n' :=
        (tensorStalkEquiv A G x).injective
          (by rw [LinearEquiv.apply_symm_apply, tensorStalkEquiv_germ, hpm, hqn])
      rw [key, stalkLinearMap_tensorRightMap_tensorSheafGerm, tensorStalkEquiv_germ,
        LinearMap.rTensor_tmul, ← hpm, ← hqn]
      exact congrArg (fun y => y ⊗ₜ[X.presheaf.stalk x] G.presheaf.germ (U ⊓ V) x hxW n')
        (stalkLinearMap_germ A B f (U ⊓ V) x hxW m').symm

/-- The stalk map of `f ⊗ 1` is the stalk map of `f` tensored with `G_x`, conjugated by the
comparison of the stalk of a tensor product with the tensor product of the stalks. -/
private theorem stalkLinearMap_tensorRightMap_eq_comp {A B : X.Modules} (f : A ⟶ B)
    (G : X.Modules) (x : X) :
    ⇑(stalkLinearMap _ _ (Scheme.Modules.tensorRightMap f G) x) =
      (tensorStalkEquiv B G x).symm ∘
        LinearMap.rTensor (G.presheaf.stalk x) (stalkLinearMap A B f x) ∘
          tensorStalkEquiv A G x :=
  funext fun z => (tensorStalkEquiv B G x).injective
    (by rw [tensorStalkEquiv_tensorRightMap, Function.comp_apply, Function.comp_apply,
      LinearEquiv.apply_symm_apply])

/-- A surjective stalk map stays surjective after tensoring on the right. -/
theorem surjective_stalkLinearMap_tensorRightMap {A B : X.Modules} (f : A ⟶ B) (G : X.Modules)
    (x : X) (hf : Function.Surjective (stalkLinearMap A B f x)) :
    Function.Surjective (stalkLinearMap _ _ (Scheme.Modules.tensorRightMap f G) x) := by
  rw [stalkLinearMap_tensorRightMap_eq_comp]
  exact (tensorStalkEquiv B G x).symm.surjective.comp
    ((LinearMap.rTensor_surjective _ hf).comp (tensorStalkEquiv A G x).surjective)

/-- A stalk map that vanishes stays zero after tensoring on the right. -/
theorem stalkLinearMap_tensorRightMap_eq_zero {A B : X.Modules} (f : A ⟶ B) (G : X.Modules)
    (x : X) (hf : stalkLinearMap A B f x = 0) :
    stalkLinearMap _ _ (Scheme.Modules.tensorRightMap f G) x = 0 := by
  refine LinearMap.ext fun z => ?_
  rw [stalkLinearMap_tensorRightMap_eq_comp, hf]
  simp

/-- A bijective stalk map stays injective after tensoring on the right. -/
theorem injective_stalkLinearMap_tensorRightMap {A B : X.Modules} (f : A ⟶ B) (G : X.Modules)
    (x : X) (hf : Function.Bijective (stalkLinearMap A B f x)) :
    Function.Injective (stalkLinearMap _ _ (Scheme.Modules.tensorRightMap f G) x) := by
  rw [stalkLinearMap_tensorRightMap_eq_comp]
  exact (tensorStalkEquiv B G x).symm.injective.comp
    ((LinearEquiv.rTensor (G.presheaf.stalk x)
      (LinearEquiv.ofBijective (stalkLinearMap A B f x) hf)).injective.comp
        (tensorStalkEquiv A G x).injective)

end AlgebraicGeometry

end
