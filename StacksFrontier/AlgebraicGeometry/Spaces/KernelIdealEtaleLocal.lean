module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# The kernel ideal of a morphism of algebraic spaces is étale-local on the target

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  The structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of Stacks 03G8 has a kernel, which
`AlgebraicGeometry.Space.kernelIdealSheaf` packages as a sheaf of ideals of `𝒪_Y`.  This file
shows that forming it commutes with étale localization of the target: on an étale scheme chart
`W` of `Y'` the kernel ideal of `f'` is the kernel ideal of `f` on the chart `g ∘ W` of `Y`.

Étale postcomposition with `g` leaves the underlying object of the big fppf site of `S`
unchanged, so `W` and `g ∘ W` have the same ring of regular functions and the two ideals are
ideals of that one ring: the statement is an equality of ideals, with no transport.

The proof is one application of the base-change compatibility of the structure maps,
`AlgebraicGeometry.Space.baseChangeStructureSharp_comp_baseChangeRingMap`.  That exhibits the
étale restriction of `f♯` along `g` as `(f')♯` followed by three comparisons of sheaves of
rings, each injective on sections: two are isomorphisms, and the third is
`AlgebraicGeometry.Space.baseChangeRingMap`, induced by the isomorphism of sheaves of sets of
Stacks 03LR, part (1).  A ring homomorphism followed by an injective one has the same kernel,
and that is the whole content.

## Main results

* `AlgebraicGeometry.Space.ker_structureSharp_baseChange_eq`: for a cartesian square with `g`
  étale, the kernel of `(f')♯` on an étale scheme chart `W` of `Y'` is the kernel of `f♯` on the
  chart `g ∘ W` of `Y`.
* `AlgebraicGeometry.Space.kernelIdealSheaf_baseChange_obj`: the same for the kernel ideal
  sheaf.
* `AlgebraicGeometry.Space.ker_structureSharp_fibreProduct_eq` and
  `AlgebraicGeometry.Space.kernelIdealSheaf_fibreProduct_obj` specialise both to the chosen
  fibre product `X ×_Y V` of Stacks 02X2, with `f'` the cartesian projection to `V`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparisons are injective on sections -/

/-- An isomorphism of sheaves of rings on the small étale site of an algebraic space is
injective on the sections over every étale scheme chart. -/
theorem injective_ringSheafIso_app (Z : AlgebraicSpaces B S hS)
    {A A' : Sheaf (SmallEtale.topology B S hS Z.1) RingCat.{u}} (e : A ≅ A')
    (T : (SmallEtale B S hS Z.1)ᵒᵖ) :
    Function.Injective (e.hom.hom.app T).hom := by
  have h1 : ∀ y, (e.inv.hom.app T).hom ((e.hom.hom.app T).hom y) = y := fun y ↦
    congrArg (fun m : A ⟶ A ↦ (m.hom.app T).hom y) e.hom_inv_id
  intro a b hab
  exact ((h1 a).symm.trans (congrArg (e.inv.hom.app T).hom hab)).trans (h1 b)

section Square

variable {X X' Y Y' : AlgebraicSpaces B S hS}
    (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The comparison of the two sheaves of rings transported around the base-change square is
injective on sections: on underlying sheaves of sets it is the isomorphism of Stacks 03LR,
part (1). -/
theorem injective_baseChangeRingMap_app (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (W : SmallEtale B S hS Y'.1) :
    Function.Injective (((baseChangeRingMap B S hS i f' f g sq hg).hom.app (op W)).hom) :=
  ((isIso_iff_bijective ((sectionsFunctor (SmallEtale.topology B S hS Y'.1) (op W)).map
    ((smallEtaleSetPushforwardBaseChangeIso B S hS i f' f g sq hg).hom.app
      (structureSetSheaf B S hS X)))).1 inferInstance).1

/-- **The kernel of the structure map commutes with étale localization of the target.**  For a
cartesian square with `g : Y' ⟶ Y` étale, the kernel of `(f')♯` on an étale scheme chart `W` of
`Y'` is the kernel of `f♯` on the chart `g ∘ W` of `Y`.

The two ideals are ideals of the same ring: étale postcomposition with `g` does not change the
underlying object of the big fppf site of `S`. -/
theorem ker_structureSharp_baseChange_eq (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (W : SmallEtale B S hS Y'.1) :
    RingHom.ker ((structureSharp B S hS f').hom.app (op W)).hom =
      RingHom.ker ((structureSharp B S hS f).hom.app
        (op ((smallEtalePostcomp B S hS g hg).obj W))).hom := by
  have hi : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i g f sq.flip hg
  have hkey : ∀ a, ((baseChangeRingMap B S hS i f' f g sq hg).hom.app (op W)).hom
        (((etaleBaseChangeRingCompIso B S hS i f' hi).hom.hom.app (op W)).hom
          (((etaleBaseChangeRingComparison B S hS i f' hi).inv.hom.app (op W)).hom
            (((structureSharp B S hS f').hom.app (op W)).hom a))) =
      ((structureSharp B S hS f).hom.app
        (op ((smallEtalePostcomp B S hS g hg).obj W))).hom a := fun a ↦
    congrArg (fun m : structureRingSheaf B S hS Y' ⟶ baseChangeRightRingSheaf B S hS f g hg ↦
        (m.hom.app (op W)).hom a)
      (baseChangeStructureSharp_comp_baseChangeRingMap B S hS i f' f g sq hg)
  have hinj1 : Function.Injective
      (((etaleBaseChangeRingComparison B S hS i f' hi).inv.hom.app (op W)).hom) :=
    injective_ringSheafIso_app B S hS Y'
      (etaleBaseChangeRingComparison B S hS i f' hi).symm (op W)
  have hinj2 : Function.Injective
      (((etaleBaseChangeRingCompIso B S hS i f' hi).hom.hom.app (op W)).hom) :=
    injective_ringSheafIso_app B S hS Y'
      (etaleBaseChangeRingCompIso B S hS i f' hi) (op W)
  have hinj3 := injective_baseChangeRingMap_app B S hS i f' f g sq hg W
  refine Ideal.ext fun a ↦ ⟨fun ha ↦ RingHom.mem_ker.2 ?_, fun ha ↦ RingHom.mem_ker.2 ?_⟩
  · refine Eq.trans (hkey a).symm ?_
    rw [RingHom.mem_ker.1 ha, map_zero, map_zero]
    exact map_zero _
  · refine (map_eq_zero_iff _ hinj1).1 ((map_eq_zero_iff _ hinj2).1
      ((map_eq_zero_iff _ hinj3).1 ?_))
    exact (hkey a).trans (RingHom.mem_ker.1 ha)

/-- **The kernel ideal sheaf commutes with étale localization of the target.**  The sections of
the kernel ideal sheaf of `f'` over an étale scheme chart `W` of `Y'` are the sections of the
kernel ideal sheaf of `f` over the chart `g ∘ W` of `Y`. -/
theorem kernelIdealSheaf_baseChange_obj (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (W : SmallEtale B S hS Y'.1) :
    (kernelIdealSheaf B S hS f').obj (op W) =
      (kernelIdealSheaf B S hS f).obj (op ((smallEtalePostcomp B S hS g hg).obj W)) :=
  ker_structureSharp_baseChange_eq B S hS i f' f g sq hg W

end Square

/-! ### The chosen fibre product -/

section FibreProduct

variable {X Y V : AlgebraicSpaces B S hS}

/-- **The kernel of the structure map of a base change along an étale morphism.**  For
`f : X ⟶ Y` and `g : V ⟶ Y` étale, the kernel of the structure map of the cartesian projection
`X ×_Y V ⟶ V` on an étale scheme chart `W` of `V` is the kernel of `f♯` on the chart `g ∘ W` of
`Y`. -/
theorem ker_structureSharp_fibreProduct_eq (f : X ⟶ Y) (g : V ⟶ Y)
    (hg : IsEtale B S hS g.hom) (W : SmallEtale B S hS V.1) :
    RingHom.ker ((structureSharp B S hS (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
          AlgebraicSpaces.fiberProduct B S hS f g ⟶ V)).hom.app (op W)).hom =
      RingHom.ker ((structureSharp B S hS f).hom.app
        (op ((smallEtalePostcomp B S hS g hg).obj W))).hom :=
  ker_structureSharp_baseChange_eq B S hS _ _ f g
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f g) hg W

/-- **The kernel ideal sheaf of a base change along an étale morphism.**  The sections of the
kernel ideal sheaf of `X ×_Y V ⟶ V` over an étale scheme chart `W` of `V` are the sections of
the kernel ideal sheaf of `f` over the chart `g ∘ W` of `Y`. -/
theorem kernelIdealSheaf_fibreProduct_obj (f : X ⟶ Y) (g : V ⟶ Y)
    (hg : IsEtale B S hS g.hom) (W : SmallEtale B S hS V.1) :
    (kernelIdealSheaf B S hS (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS f g ⟶ V)).obj (op W) =
      (kernelIdealSheaf B S hS f).obj (op ((smallEtalePostcomp B S hS g hg).obj W)) :=
  ker_structureSharp_fibreProduct_eq B S hS f g hg W

end FibreProduct

end AlgebraicGeometry.Space

end
