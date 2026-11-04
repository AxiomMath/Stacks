module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FunctorsHomomorphisms.Comparison

/-!
# Bijectivity in the functoriality of Galois categories

Let `H : C ⥤ C'` be a functor between Galois categories, compatible with fibre functors `F` and
`F'` through an isomorphism `t : H ⋙ F' ≅ F`, and let `h : Aut F' → Aut F` be the induced
continuous homomorphism. If `h` is bijective, then `H` is essentially surjective.

The automorphism groups are compact and Hausdorff, so a continuous bijection between them is a
homeomorphism, and restriction of actions along it is an equivalence
(`ContAction.resEquiv`). The functoriality square identifies `H` followed by the equivalence
`C' ≌ ContAction (Aut F')` with the equivalence `C ≌ ContAction (Aut F)` followed by restriction
along `h`, so `H` is an equivalence up to the two identifications.

## Main results

* `CategoryTheory.GaloisFunctorData.essSurj_of_bijective`: a bijective induced homomorphism makes
  the functor essentially surjective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

universe u v u' v' w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

/-- **A bijective induced homomorphism makes the functor essentially surjective.** Let
`H : C ⥤ C'` be a functor between Galois categories with fibre functors `F` and `F'`, and let
`d` be functoriality data for an isomorphism `t : H ⋙ F' ≅ F`. If the induced continuous
homomorphism `Aut F' → Aut F` is bijective, every object of `C'` is isomorphic to the image of an
object of `C`. -/
public theorem GaloisFunctorData.essSurj_of_bijective
    (F : C ⥤ FintypeCat.{w}) (F' : C' ⥤ FintypeCat.{w})
    [IsGaloisCategory (setValuedFiberFunctor F)]
    [IsGaloisCategory (setValuedFiberFunctor F')]
    (H : C ⥤ C') (t : H ⋙ F' ≅ F) (d : GaloisFunctorData F F' H t)
    (hbij : Function.Bijective d.hom) : H.EssSurj := by
  classical
  let : PreGaloisCategory C := preGalois_of_isGaloisCategory F
  let : PreGaloisCategory.FiberFunctor F := IsGaloisCategory.fiberFunctor F
  let : GaloisCategory C := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F)
  let : PreGaloisCategory C' := preGalois_of_isGaloisCategory F'
  let : PreGaloisCategory.FiberFunctor F' := IsGaloisCategory.fiberFunctor F'
  let : GaloisCategory C' := IsGaloisCategory.toGaloisCategory (setValuedFiberFunctor F')
  -- the induced homomorphism is a homeomorphism: compact source, Hausdorff target
  let f : Aut F' ≃ₜ* Aut F := ContinuousMulEquiv.mk'
    (d.hom.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective d.hom hbij)) (map_mul d.hom)
  have hf : (f : Aut F' →ₜ* Aut F) = d.hom := by
    ext σ
    rfl
  let A := PreGaloisCategory.functorToContAction F
  let B := PreGaloisCategory.functorToContAction F'
  let R := ContAction.resEquiv FintypeCat.{w} f
  refine ⟨fun X'' => ?_⟩
  obtain ⟨X', ⟨eX'⟩⟩ := Functor.EssSurj.mem_essImage A (R.inverse.obj (B.obj X''))
  -- `B (H X') ≅ res_h (A X') ≅ res_h (res_{h⁻¹} (B X'')) ≅ B X''`
  let i : B.obj (H.obj X') ≅ B.obj X'' :=
    (d.actionIso.app X').symm ≪≫ (ContAction.resCongr FintypeCat.{w} _ _ hf).symm.app _ ≪≫
      R.functor.mapIso eX' ≪≫ R.counitIso.app (B.obj X'')
  exact ⟨X', ⟨B.preimageIso i⟩⟩

end CategoryTheory

end
