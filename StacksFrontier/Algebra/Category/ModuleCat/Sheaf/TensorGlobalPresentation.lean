module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.CategoryTheory.Limits.ColimitComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedSymmetry

/-!
# A tensor product of two globally presented sheaves of modules is globally presented

`SheafOfModules.HasGlobalPresentation` is the global condition of Stacks 03DE(6): after raising
the universe of its sections, a sheaf of modules is a cokernel of a map between coproducts of
copies of the universe-lifted structure sheaf.  This file proves that the condition is inherited
by a tensor product.

The argument is the usual two-variable right-exactness computation.  Writing `1` for the
universe-lifted structure sheaf, `Ã = coker(Q → P)` and `B̃ = coker(Q' → P')` with `P` a
coproduct of copies of `1` and so on, the composite
`P ⊗ P' --𝟙⊗b'--> P ⊗ B̃ --b⊗𝟙--> Ã ⊗ B̃` is a cokernel of a map out of
`(P ⊗ Q') ⨿ (Q ⊗ P')`, and each of the four tensor products of coproducts of copies of `1` is
again one.  Both right-exactness steps are colimit preservation: in the second variable it is
`TensorColimits.tensorLeft_preservesColimits J` and in the first
`tensorRightRaised_preservesColimits`, and the commuting square needed to splice the two cokernels
is `Functor.map_comp` of the *bifunctor*, applied to `(a, 𝟙) ≫ (𝟙, b') = (𝟙, b') ≫ (a, 𝟙)` in
the product category.

## Main results

* `Stacks.SheafOfModules.TensorRaised.hasGlobalPresentation_of_tensorIso`: **a sheaf of modules
  whose universe lift is a tensor product of the universe lifts of two globally presented sheaves
  of modules is globally presented.**

## Implementation notes

The hypothesis is an isomorphism of the universe lift of the target with the tensor product of
the universe lifts, rather than the statement that the target *is* a tensor product.  That is
what the claim site needs: on a slice site at the module universe of the claim there is no
sheafification, so the tensor product cannot be formed there, while at the raised universe in
which a global presentation lives it can.

Every morphism in the proof is written as `Functor.map` of the bifunctor rather than of one of
the two one-variable functors, because the commuting square is an identity in the product
category; the colimit and cokernel facts are then read off the one-variable functors, to which
the bifunctor's `Functor.map` of a pair with an identity component is definitionally equal.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 05NB](https://stacks.math.columbia.edu/tag/05NB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.SheafOfModules.TensorRaised

open Stacks.CategoryTheory.ColimitComposition

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- The interchange law for a bifunctor: a pair of morphisms is the composite of its two
one-variable parts in either order. -/
theorem bifunctor_map_interchange {D₁ : Type*} [Category D₁] {D₂ : Type*} [Category D₂]
    {E : Type*} [Category E] (T : D₁ × D₂ ⥤ E) {X X' : D₁} {Y Y' : D₂} (f : X ⟶ X')
    (g : Y ⟶ Y') :
    T.map ((f, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫ T.map ((𝟙 X', g) : (X', Y) ⟶ (X', Y')) =
      T.map ((𝟙 X, g) : (X, Y) ⟶ (X, Y')) ≫ T.map ((f, 𝟙 Y') : (X, Y') ⟶ (X', Y')) := by
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  exact Prod.ext (by simp) (by simp)

/-- Tensoring two coproducts of copies of the universe-lifted structure sheaf gives a coproduct
of copies of it, indexed by the product of the two index types. -/
private noncomputable def isColimit_tensorCofan (R : Sheaf J CommRingCat.{w})
    {I K : Type (max u v w)}
    {F X : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)}
    {ιF : I → (liftedUnit.{u, v, w, max u v w} R ⟶ F)}
    {ιX : K → (liftedUnit.{u, v, w, max u v w} R ⟶ X)}
    (hF : IsColimit (Cofan.mk F ιF)) (hX : IsColimit (Cofan.mk X ιX)) :
    IsColimit (Cofan.mk (f := fun _ : K × I ↦ liftedUnit.{u, v, w, max u v w} R)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj F).obj X)
      (fun ⟨k, i⟩ ↦ (ιF i ≫ (rightUnitorRaisedIso.{u, v, w, max u v w} R F).inv) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj F).map
          (ιX k))) := by
  have hc1 : IsColimit (Cofan.mk
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj F).obj
          (liftedUnit.{u, v, w, max u v w} R))
      (fun i ↦ ιF i ≫ (rightUnitorRaisedIso.{u, v, w, max u v w} R F).inv)) :=
    IsColimit.ofIsoColimit hF
      (Cofan.ext (rightUnitorRaisedIso.{u, v, w, max u v w} R F).symm fun _ ↦ rfl)
  have hc2 : IsColimit (Cofan.mk
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj F).obj X)
      (fun k ↦ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj
          F).map (ιX k))) :=
    (Cofan.isColimitMapCoconeEquiv ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w,
        max u v w} R).obj F) _
      (Cofan.mk X ιX)).toFun
      (isColimitOfPreserves ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v
          w} R).obj F) hX)
  exact Cofan.IsColimit.prod
    (fun _ ↦ Cofan.mk _ (fun i ↦ ιF i ≫ (rightUnitorRaisedIso.{u, v, w, max u v w} R F).inv))
    (fun _ ↦ hc1) _ hc2

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A tensor product of two globally presented sheaves of modules is globally presented.**
The hypothesis is an isomorphism of the universe lift of `M` with the tensor product of the
universe lifts of `A` and `B`, at the raised universe in which a global presentation lives. -/
theorem hasGlobalPresentation_of_tensorIso (R : Sheaf J CommRingCat.{w})
    (A B M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (e : SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} M ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj
          (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} A)).obj
          (SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} B) :
        SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf R)))
    (hA : A.HasGlobalPresentation) (hB : B.HasGlobalPresentation) :
    M.HasGlobalPresentation := by
  classical
  obtain ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := hA
  obtain ⟨I', K', P', Q', ι', κ', hP', hQ', a', b', hab', hc'⟩ := hB
  let uA := SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} A
  let uB := SheafOfModules.uliftForPresentation.{u, v, w, w, max u v w} B
  -- the six structure maps, all written through the bifunctor
  let y : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P).obj
      Q' ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P).obj
      P' := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P
      |>.map a'
  let p₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P).obj
      P' ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P).obj
      uB := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P
      |>.map b'
  let q : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P).obj
      uB ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj uA).obj
      uB := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).map b).app
      uB
  let w₀ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj Q).obj
      uB ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P).obj
      uB := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).map a).app
      uB
  let ee : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj Q).obj
      P' ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj Q).obj
      uB := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj Q
      |>.map b'
  let v : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj Q).obj
      P' ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P).obj
      P' := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).map a).app
      P'
  have hyp₁ : y ≫ p₁ = 0 := by
    change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj
        P).map a' ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj P).map b'
            = 0
    rw [← Functor.map_comp, hab', Functor.map_zero]
  have hwq : w₀ ≫ q = 0 := by
    change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).flip.obj
        uB).map a ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).flip.obj
            uB).map b = 0
    rw [← Functor.map_comp, hab, Functor.map_zero]
  have hcp₁ : IsColimit (CokernelCofork.ofπ (f := y) p₁ hyp₁) :=
    isColimitCoforkMapOfIsColimit' ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w,
        max u v w} R).obj P) hab' hc'.some
  have hcq : IsColimit (CokernelCofork.ofπ (f := w₀) q hwq) :=
    isColimitCoforkMapOfIsColimit' ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w,
        max u v w} R).flip.obj uB) hab hc.some
  -- the epimorphism `ee`
  have hb'epi : Epi b' := by simpa using epi_of_isColimit_cofork hc'.some
  have hepi : Epi ee :=
    preserves_epi_of_preservesColimit ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v
        w, max u v w} R).obj Q) b'
  -- the commuting square, which is the interchange law of the bifunctor
  have hsq : v ≫ p₁ = ee ≫ w₀ := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max
      u v w} R).map a).naturality b' |>.symm
  -- the binary coproduct of the two relation objects
  let EE := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj
      P).obj Q') ⨿ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w}
      R).obj Q).obj P')
  let d : EE ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w} R).obj
      P).obj P' := coprod.desc y v
  have hjY : (coprod.inl : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v
      w} R).obj P).obj Q' ⟶ EE) ≫ d = y := coprod.inl_desc _ _
  have hjV : (coprod.inr : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v
      w} R).obj Q).obj P' ⟶ EE) ≫ d = v := coprod.inr_desc _ _
  have hd : d ≫ p₁ ≫ q = 0 := by
    refine coprod.hom_ext ?_ ?_
    · rw [comp_zero, ← Category.assoc, hjY, ← Category.assoc, hyp₁, zero_comp]
    · rw [comp_zero, ← Category.assoc, hjV, ← Category.assoc, hsq, Category.assoc, hwq, comp_zero]
  have hcoker : IsColimit (CokernelCofork.ofπ (f := d) (p₁ ≫ q) hd) :=
    isColimitCokernelComp hcp₁ hcq hsq hjY hjV hd
  -- transport the cokernel onto the universe lift of `M`
  have hd' : d ≫ (p₁ ≫ q) ≫ e.inv = 0 := by rw [← Category.assoc, hd, zero_comp]
  have hcoker' : IsColimit (CokernelCofork.ofπ (f := d) ((p₁ ≫ q) ≫ e.inv) hd') :=
    isColimitCokernelCompIso e.symm hcoker hd'
  -- the coproduct decompositions of the generators and of the relations
  have hPP' := isColimit_tensorCofan.{u, v, w} R hP.some hP'.some
  have hPQ' := isColimit_tensorCofan.{u, v, w} R hP.some hQ'.some
  have hQP' := isColimit_tensorCofan.{u, v, w} R hQ.some hP'.some
  have hEE := isColimitCofanSum hPQ' hQP'
    (coprodIsCoprod (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v w}
        R).obj P).obj Q') (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max u v w, max u v
        w} R).obj Q).obj P'))
  exact ⟨_, _, _, _, _, _, ⟨hPP'⟩, ⟨hEE⟩, d, (p₁ ≫ q) ≫ e.inv, hd', ⟨hcoker'⟩⟩

end Stacks.SheafOfModules.TensorRaised

end
