module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IntegralModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle

/-!
# Extension by zero commutes with an integral direct image

Let
```
V --j'--> V̄
|f        |f̄
v         v
U --j---> Ū
```
be a cartesian square of schemes with `j` an étale monomorphism (an open immersion) and `f̄`
integral, and let `Ū = j(U) ⊔ i(Z)` with `i` a closed immersion.  For a sheaf `M` of
`Λ`-modules on `V_étale` the canonical map `j_!(f_* M) ⟶ f̄_*(j'_! M)`, adjoint to
`f_* M ⟶ f_* j'^{-1} j'_! M ≅ j^{-1} f̄_* j'_! M`, is an isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.restrictionDirectImageIso`: the base change isomorphism
  `f_* j'^{-1} ≅ j^{-1} f̄_*`.
* `Stacks.EtaleCohomology.extensionByZeroDirectImageMap`: the canonical map
  `j_!(f_* M) ⟶ f̄_*(j'_! M)`.

## Main results

* `Stacks.EtaleCohomology.isIso_extensionByZeroDirectImageMap`: the canonical map
  `j_!(f_* M) ⟶ f̄_*(j'_! M)` is an isomorphism.
* `Stacks.EtaleCohomology.isPullback_fieldBaseChangeMap`: the base change to `k̄` of a morphism
  over `k` is a pullback of it.
* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isIntegralHom`: the
  base change map to `k̄` along an integral morphism over `k` is an isomorphism.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {U Ub V Vb : Scheme.{u}} (j : U ⟶ Ub) [Etale j] [Mono j]
  (j' : V ⟶ Vb) [Etale j'] [Mono j'] (f : V ⟶ U) (fb : Vb ⟶ Ub) [IsIntegralHom fb]
  (sq : IsPullback f j' j fb)

/-- The isomorphism `f_* j'^{-1} ≅ j^{-1} f̄_*`: the base change isomorphism, with inverse image
along the étale maps `j`, `j'` read as restriction. -/
def restrictionDirectImageIso :
    etaleModuleRestriction.{u, 0} Λ j' ⋙ etaleModuleDirectImage.{u, 0} Λ f ≅
      etaleModuleDirectImage.{u, 0} Λ fb ⋙ etaleModuleRestriction.{u, 0} Λ j :=
  haveI := isIso_etaleModuleBaseChange_of_isIntegralHom Λ fb f j j' sq
  Functor.isoWhiskerRight (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j').symm _ ≪≫
    (asIso (etaleModuleBaseChange Λ fb f j j' sq.w)).symm ≪≫
    Functor.isoWhiskerLeft _ (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j)

/-- The canonical map `j_!(f_* M) ⟶ f̄_*(j'_! M)`, adjoint under `j_! ⊣ j^{-1}` to the unit of
`j'_! ⊣ j'^{-1}` followed by `restrictionDirectImageIso`. -/
def extensionByZeroDirectImageMap (M : EtaleModules.{u, 0} Λ V) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).obj ((etaleModuleDirectImage.{u, 0} Λ f).obj M) ⟶
      (etaleModuleDirectImage.{u, 0} Λ fb).obj ((etaleModuleExtensionByZero.{u, 0} Λ j').obj M) :=
  ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).symm
    ((etaleModuleDirectImage.{u, 0} Λ f).map
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app M) ≫
      (restrictionDirectImageIso Λ j j' f fb sq).hom.app _)

/-- Let `i : Z ⟶ Ub` be a closed immersion onto the complement of `U`, with base change
`i' : Z' ⟶ Vb` a closed immersion onto the complement of `V`. Then the canonical map
`j_!(f_* M) ⟶ f̄_*(j'_! M)` is an isomorphism. -/
theorem isIso_extensionByZeroDirectImageMap {Z Z' : Scheme.{u}} (i : Z ⟶ Ub) [IsClosedImmersion i]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (i' : Z' ⟶ Vb) [IsClosedImmersion i']
    (hij' : Set.range j'.base = (Set.range i'.base)ᶜ) (fZ : Z' ⟶ Z) (sqZ : IsPullback fZ i' i fb)
    (M : EtaleModules.{u, 0} Λ V) :
    IsIso (extensionByZeroDirectImageMap Λ j j' f fb sq M) := by
  have hU : IsIso ((etaleModuleInverseImage.{u, 0} Λ j).map
      (extensionByZeroDirectImageMap Λ j j' f fb sq M)) := by
    have hR : IsIso ((etaleModuleRestriction.{u, 0} Λ j).map
        (extensionByZeroDirectImageMap Λ j j' f fb sq M)) := by
      have h := Adjunction.homEquiv_unit (etaleModuleExtensionByZeroAdj.{u, 0} Λ j) _ _
        (extensionByZeroDirectImageMap Λ j j' f fb sq M)
      have h' : ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _)
          (extensionByZeroDirectImageMap Λ j j' f fb sq M) =
          (etaleModuleDirectImage.{u, 0} Λ f).map
            ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app M) ≫
            (restrictionDirectImageIso Λ j j' f fb sq).hom.app _ :=
        Equiv.apply_symm_apply _ _
      have : IsIso ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app
          ((etaleModuleDirectImage.{u, 0} Λ f).obj M) ≫ (etaleModuleRestriction.{u, 0} Λ j).map
            (extensionByZeroDirectImageMap Λ j j' f fb sq M)) := by
        rw [← h, h']
        infer_instance
      exact IsIso.of_isIso_comp_left ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app
        ((etaleModuleDirectImage.{u, 0} Λ f).obj M)) _
    exact (NatIso.isIso_map_iff (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j) _).2 hR
  have hZ : IsIso ((etaleModuleInverseImage.{u, 0} Λ i).map
      (extensionByZeroDirectImageMap Λ j j' f fb sq M)) := by
    have := isIso_etaleModuleBaseChange_of_isIntegralHom Λ fb fZ i i' sqZ
    refine ⟨0, (isZero_etaleModuleInverseImage_extensionByZero Λ i j hij _).eq_of_src _ _, ?_⟩
    refine IsZero.eq_of_src ?_ _ _
    exact ((etaleModuleDirectImage.{u, 0} Λ fZ).map_isZero
      (isZero_etaleModuleInverseImage_extensionByZero Λ i' j' hij' M)).of_iso
        (asIso ((etaleModuleBaseChange Λ fb fZ i i' sqZ.w).app _))
  exact isIso_of_isIso_etaleModuleInverseImage Λ i j hij _

section FieldBaseChange

open Stacks.Frobenius

variable {k : Type u} [Field k] {Zk Yk : Over (Spec (.of k))} (i : Zk ⟶ Yk)
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- The base change `i_k̄ : Z_k̄ ⟶ Y_k̄` to `k̄` of a morphism `i : Z ⟶ Y` over `k` is a
pullback of `i`. -/
theorem isPullback_fieldBaseChangeMap :
    IsPullback (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Zk kbar)
      (fieldBaseChangeProj Yk kbar) i.left := by
  have hfst : fieldBaseChangeMap i kbar ≫ fieldBaseChangeProj Yk kbar =
      fieldBaseChangeProj Zk kbar ≫ i.left := pullback.lift_fst _ _ _
  have hsnd : fieldBaseChangeMap i kbar ≫ pullback.snd Yk.hom (specAlgebraMap k kbar) =
      pullback.snd Zk.hom (specAlgebraMap k kbar) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_right ?_ hfst (IsPullback.of_hasPullback Yk.hom (specAlgebraMap k kbar)).flip
  rw [hsnd, Over.w i]
  exact (IsPullback.of_hasPullback Zk.hom (specAlgebraMap k kbar)).flip

/-- For an integral morphism `i : Z ⟶ Y` over `k`, the base change map of étale `Λ`-modules
along the square of `i` and its base change `i_k̄` to `k̄` is an isomorphism. -/
theorem isIso_etaleModuleBaseChange_fieldBaseChangeMap_of_isIntegralHom [IsIntegralHom i.left] :
    IsIso (etaleModuleBaseChange Λ i.left (fieldBaseChangeMap i kbar) (fieldBaseChangeProj Yk kbar)
      (fieldBaseChangeProj Zk kbar) (fieldBaseChangeMap_comp_fst i kbar)) :=
  isIso_etaleModuleBaseChange_of_isIntegralHom Λ i.left (fieldBaseChangeMap i kbar)
    (fieldBaseChangeProj Yk kbar) (fieldBaseChangeProj Zk kbar)
    (isPullback_fieldBaseChangeMap i kbar)

end FieldBaseChange

end Stacks.EtaleCohomology

end
