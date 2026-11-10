module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksCore.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Right exactness of tensor products of modules on a ringed space

Tensoring an exact sequence of modules on a ringed space with a fixed module preserves
exactness at the middle and right terms.

## Main results

* `AlgebraicGeometry.SheafOfModules.tensorSheafMap_exact`: tensoring an exact pair whose
  second map is an epimorphism gives an exact pair.
* `AlgebraicGeometry.SheafOfModules.tensorSheafMap_epi`: tensoring an epimorphism gives an
  epimorphism.

## Implementation notes

The assertion that the resulting sequence ending in zero is exact is split into its two
standard categorical components: exactness of the induced short complex, and epimorphicity of
its second map. Since the tensor product of modules on a ringed space is a bifunctorial
construction rather than an endofunctor, the first component also supplies the proof that the
two induced maps compose to zero.

Both components are checked pointwise. The stalk criterion for exactness reduces them to
right exactness of the tensor product of modules over the local ring at a point, transported
along the canonical isomorphism between the stalk of a tensor product and the tensor product
of the stalks.

## References

* [Stacks Project, Tag 01CC](https://stacks.math.columbia.edu/tag/01CC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SheafOfModules

open Stacks.SheafOfModules.TensorStalkRingedSpace

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.sheafTensor
  PresheafOfModules.tensorObj TopCat.Presheaf.IsSheaf

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}

/-- Tensoring the zero morphism of modules on a ringed space with any morphism gives the
zero morphism. The ringed space is explicit, because it is not determined by the morphism
when the module is presented over a sheaf of rings obtained some other way. -/
lemma tensorSheafMap_zero_left (X : AlgebraicGeometry.RingedSpace.{u, u})
    {F F' G G' : _root_.SheafOfModules.{u} (structureSheafRing X)} (ψ : G ⟶ G') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
        (((0 : F ⟶ F'), ψ) : (_, _) ⟶ (_, _))) = 0 := by
  refine (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}) (0 : F ⟶ F') ψ).trans ?_
  rw [show (0 : F ⟶ F').val = 0 from rfl, PresheafOfModules.tensorHom_zero_left]
  exact CategoryTheory.Functor.map_zero _ _ _

/-- The second map of a stalk complex vanishes as soon as the second map of the complex it
comes from does. -/
private lemma stalkShortComplex_g_zero
    (S : ShortComplex (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (h : S.g = 0) (x : X.carrier) :
    (stalkShortComplex (structureSheafRing X) S x).g = 0 := by
  change (stalkAddCommGroupFunctor (structureSheafRing X) x).map S.g = 0
  rw [h, Functor.map_zero]

/-- A morphism of sheaves of modules is an epimorphism iff it is surjective on all stalks. -/
private lemma epi_iff_surjective_stalkMapL
    {F₂ F₃ : _root_.SheafOfModules.{u} (structureSheafRing X)} (g : F₂ ⟶ F₃) :
    Epi g ↔ ∀ x : X.carrier, Function.Surjective (stalkMapL X F₂.val F₃.val g.val x) := by
  let S := ShortComplex.mk g (0 : F₃ ⟶ F₃) Limits.comp_zero
  rw [← S.exact_iff_epi rfl, exact_iff_stalkShortComplex_exact (structureSheafRing X) S]
  refine forall_congr' fun x => ?_
  rw [(stalkShortComplex (structureSheafRing X) S x).exact_iff_epi
    (stalkShortComplex_g_zero S rfl x), AddCommGrpCat.epi_iff_surjective]
  rfl

/-- An epimorphism of sheaves of modules is surjective on stalks. -/
private lemma stalk_epi_surjective
    {F₂ F₃ : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (g : F₂ ⟶ F₃) [Epi g] (x : X.carrier) :
    Function.Surjective (stalkMapL X F₂.val F₃.val g.val x) :=
  (epi_iff_surjective_stalkMapL g).1 inferInstance x

/-- The canonical isomorphism between the stalk of a tensor product and the tensor product of
the stalks is natural in the first argument. -/
private lemma stalk_tensor_sheafMap
    {F F' G : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (f : F ⟶ F') (x : X.carrier)
    (z : grpStalk X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj (G))).val x) :
    LinearMap.rTensor (grpStalk X G.val x) (stalkMapL X F.val F'.val f.val x)
        ((tensorStalkIso X x F G) z) =
      (tensorStalkIso X x F' G)
        (stalkMapL X
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj (G))).val
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F')).obj (G))).val
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
              ((f, (𝟙 G)) : (_, _) ⟶ (_, _)))).val x z) := by
  let tensorStalkModule := stalkModule X
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj F).obj G).val x
  let idG : G ⟶ G := 𝟙 G
  have h := tensorStalkIso_natural X x F G F' G f idG
  have hid : stalkMapL X G.val G.val
      idG.val x = LinearMap.id := by
    ext z
    change Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap X G.val G.val idG.val x z = z
    simp [Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMap, idG]
    rfl
  have hz := LinearMap.congr_fun h z
  rwa [LinearMap.comp_apply, LinearMap.comp_apply, hid, ← LinearMap.rTensor_def] at hz

/-- Tensoring an epimorphism on the right by a module is surjective on stalks. -/
private lemma stalk_tensor_epi_surjective
    {F F' : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (f : F ⟶ F') [Epi f] (G : _root_.SheafOfModules.{u} (structureSheafRing X))
    (x : X.carrier) :
    Function.Surjective (stalkMapL X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F)).obj (G))).val
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (F')).obj (G))).val
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
          ((f, (𝟙 G)) : (_, _) ⟶ (_, _)))).val x) := by
  intro y
  obtain ⟨z, hz⟩ := LinearMap.rTensor_surjective (grpStalk X G.val x)
    (stalk_epi_surjective f x) (tensorStalkIso X x F' G y)
  refine ⟨(tensorStalkIso X x F G).symm z, (tensorStalkIso X x F' G).injective ?_⟩
  have hnat := stalk_tensor_sheafMap f x ((tensorStalkIso X x F G).symm z)
  rw [LinearEquiv.apply_symm_apply] at hnat
  exact hnat.symm.trans hz

private lemma tensor_stalk_exact
    (shortComplex : ShortComplex (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (factorSheaf : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hS : shortComplex.Exact) [Epi shortComplex.g] (point : X.carrier) :
    Function.Exact
      (stalkMapL X _ _ ((Functor.uncurry.obj (
          Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).map ((shortComplex.f, 𝟙 factorSheaf) :
          (shortComplex.X₁, factorSheaf) ⟶ (shortComplex.X₂, factorSheaf))).val point)
      (stalkMapL X _ _ ((Functor.uncurry.obj (
          Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).map ((shortComplex.g, 𝟙 factorSheaf) :
          (shortComplex.X₂, factorSheaf) ⟶ (shortComplex.X₃, factorSheaf))).val point) := by
  let firstTensorStalkModule := stalkModule X
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj
        shortComplex.X₁).obj factorSheaf).val point
  let secondTensorStalkModule := stalkModule X
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj
        shortComplex.X₂).obj factorSheaf).val point
  let thirdTensorStalkModule := stalkModule X
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj
        shortComplex.X₃).obj factorSheaf).val point
  let firstMap := stalkMapL X shortComplex.X₁.val shortComplex.X₂.val shortComplex.f.val point
  let secondMap := stalkMapL X shortComplex.X₂.val shortComplex.X₃.val shortComplex.g.val point
  let factor := grpStalk X factorSheaf.val point
  have exactStalks : Function.Exact firstMap secondMap :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      ((exact_iff_stalkShortComplex_exact _ shortComplex).mp hS point)
  refine (LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    _ _ (LinearMap.rTensor factor firstMap)
      (LinearMap.rTensor factor secondMap)
      (tensorStalkIso X point shortComplex.X₁ factorSheaf).toLinearMap
      (tensorStalkIso X point shortComplex.X₂ factorSheaf).toLinearMap
      (tensorStalkIso X point shortComplex.X₃ factorSheaf).toLinearMap
      ?_ ?_ (tensorStalkIso X point shortComplex.X₁ factorSheaf).surjective
      (tensorStalkIso X point shortComplex.X₂ factorSheaf).bijective
      (tensorStalkIso X point shortComplex.X₃ factorSheaf).injective).mpr
      (rTensor_exact factor exactStalks (stalk_epi_surjective shortComplex.g point))
  · exact LinearMap.ext (stalk_tensor_sheafMap shortComplex.f point)
  · exact LinearMap.ext (stalk_tensor_sheafMap shortComplex.g point)

/-- Tensoring an exact pair of `O_X`-modules whose second map is an epimorphism
on the right by an `O_X`-module gives an exact pair. -/
@[stacks 01CC "exactness at the middle term"]
theorem tensorSheafMap_exact
    (S : ShortComplex (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (G : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hS : S.Exact) [Epi S.g] :
    let tensorFunctor :
        (_root_.SheafOfModules.{u} (structureSheafRing X) ×
          _root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
          _root_.SheafOfModules.{u} (structureSheafRing X) :=
      Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)
    let firstMap := tensorFunctor.map ((S.f, 𝟙 G) : (S.X₁, G) ⟶ (S.X₂, G))
    let secondMap := tensorFunctor.map ((S.g, 𝟙 G) : (S.X₂, G) ⟶ (S.X₃, G))
    ∃ zeroComposite : firstMap ≫ secondMap = 0,
      (ShortComplex.mk firstMap secondMap zeroComposite).Exact := by
  intro tensorFunctor firstMap secondMap
  have hzero : firstMap ≫ secondMap = 0 := by
    rw [← tensorFunctor.map_comp]
    change tensorFunctor.map ((S.f ≫ S.g, 𝟙 G ≫ 𝟙 G) :
      (S.X₁, G) ⟶ (S.X₃, G)) = 0
    rw [S.zero, Category.id_comp]
    exact tensorSheafMap_zero_left X (𝟙 G)
  exact ⟨hzero, (exact_iff_stalkShortComplex_exact _ _).2 fun point =>
    (ShortComplex.ab_exact_iff_function_exact _).2 (tensor_stalk_exact S G hS point)⟩

/-- Tensoring an epimorphism of `O_X`-modules on the right by an
`O_X`-module gives an epimorphism. -/
@[stacks 01CC "exactness at the right term", instance]
theorem tensorSheafMap_epi
    {F₂ F₃ : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (G : _root_.SheafOfModules.{u} (structureSheafRing X)) (g : F₂ ⟶ F₃) [Epi g] :
    Epi (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u}))).map
        ((g, (𝟙 G)) : (_, _) ⟶ (_, _)))) := by
  exact (epi_iff_surjective_stalkMapL _).2 (stalk_tensor_epi_surjective g G)

end AlgebraicGeometry.SheafOfModules
