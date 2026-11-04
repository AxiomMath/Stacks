module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaAcyclic

/-!
# The differential graded Yoneda functor is fully faithful on homotopy categories

Let `C` be a differential graded category over a commutative ring `R`. The functor of
differential graded categories `X ↦ h_X` of `DGCategory.yonedaDGFunctor` induces, by Tag 09L8,
an ordinary functor

`K(h) = (yonedaDGFunctor C).onK : K(C) ⥤ K(Mod^dg(C))`,

and this file proves that it is full and faithful, as instances on the functor itself.

`DGCategory.RightModule.homYonedaObjKEquiv` already records a *bijection*
`Hom_{K(Mod^dg(C))}(h_x, h_y) ≃ Hom_{K(C)}(x, y)`, assembled out of the differential graded
Yoneda lemma on cohomology and Tag 09LC. What it does not say is that the bijection is the map
`f ↦ K(h) f`, and a bijection between two Hom groups is of no use to the full-subcategory
arguments that need the functor itself to be full and faithful — the image of `K(h)` being a
triangulated subcategory, for instance, needs a morphism between representables to *be* `h_f`
for an actual `f`. So the two statements are proved separately rather than one from the other,
and the proof here is the direct one: both directions are the degreewise Yoneda lemma
`DGCategory.yonedaPostcompEquiv`, which is evaluation at the identity, read on cocycles and on
homotopies.

## Main results

* `DGCategory.full_yonedaOnK`: `K(h)` is full. A degree-zero closed homogeneous morphism
  `h_x ⟶ h_y` is `h_a` for `a` its value at the identity, which is closed by
  `DGCategory.homD_eq_zero_iff`.
* `DGCategory.faithful_yonedaOnK`: `K(h)` is faithful. A homotopy between `h_f` and `h_g` has a
  value at the identity, which is a homotopy between `f` and `g` by
  `DGCategory.yonedaEval_dPrime`.

## References

* [Stacks Project, Tag 09L8](https://stacks.math.columbia.edu/tag/09L8)
* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

namespace DGCategory

universe v u r

open CategoryTheory

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

attribute [local implicit_reducible] DGCategory.K

/-- **The differential graded Yoneda functor is full on homotopy categories.** A morphism
`h_x ⟶ h_y` of `K(Mod^dg(C))` is represented by a closed degree-zero homogeneous morphism `φ`,
and `φ` is postcomposition with its own value `φ(1_x)`, which is closed because `φ` is. -/
instance full_yonedaOnK : ((yonedaDGFunctor C).onK).Full where
  map_surjective {x y} φ := by
    refine Quotient.inductionOn
      (motive := fun φ => ∃ f, (yonedaDGFunctor C).onK.map f = φ) φ fun φ => ?_
    refine ⟨Quotient.mk _ ⟨yonedaEval (yonedaRightModule C (y : C.Obj)) (x : C.Obj) 0 φ.1, ?_⟩,
      congrArg (Quotient.mk _) (Subtype.ext ?_)⟩
    · have h := (homD_eq_zero_iff (yonedaRightModule C (y : C.Obj)) (x : C.Obj) φ.1).1 φ.2
      rwa [yonedaRightModule_d] at h
    · change yonedaPostcomp C
          (yonedaEval (yonedaRightModule C (y : C.Obj)) (x : C.Obj) 0 φ.1) = φ.1
      exact (yonedaEval (yonedaRightModule C (y : C.Obj)) (x : C.Obj) 0).injective
        (yonedaEval_yonedaPostcomp _)

/-- A homotopy between the postcompositions `h_f` and `h_g` has a value at the identity, and
that value is a homotopy between `f` and `g`: evaluation at the identity commutes with the
coboundary `d'` by `DGCategory.yonedaEval_dPrime`, and carries `h_f` to `f` by
`DGCategory.yonedaEval_yonedaPostcomp`. -/
private theorem homotopic_of_dPrime_yonedaPostcomp {x y : C.Obj} {f g : C.Cocycle x y}
    (ψ : RightModule.HomogeneousMap (yonedaRightModule C x) (yonedaRightModule C y) (-1))
    (hψ : yonedaPostcomp C f.1 - yonedaPostcomp C g.1 =
      (rightModuleCategory.{v} C).d' (show (-1 : ℤ) + 1 = 0 by omega) ψ) :
    C.Homotopic f g := by
  refine ⟨yonedaEval (yonedaRightModule C y) x (-1) ψ, ?_⟩
  have h := congrArg (yonedaEval (yonedaRightModule C y) x 0) hψ
  rwa [map_sub, yonedaEval_yonedaPostcomp, yonedaEval_yonedaPostcomp,
    yonedaEval_dPrime _ _ (show (-1 : ℤ) + 1 = 0 by omega) ψ, yonedaRightModule_d] at h

/-- **The differential graded Yoneda functor is faithful on homotopy categories.** If `h_f` and
`h_g` are homotopic then the homotopy, which is a degree `-1` homogeneous morphism
`h_x ⟶ h_y`, has a value at the identity, and that value is a homotopy from `f` to `g`:
evaluation at the identity commutes with the coboundary by
`DGCategory.yonedaEval_dPrime`, and carries `h_f` to `f` by
`DGCategory.yonedaEval_yonedaPostcomp`. -/
instance faithful_yonedaOnK : ((yonedaDGFunctor C).onK).Faithful where
  map_injective {x y} f g hfg := by
    refine Quotient.inductionOn₂ (motive := fun f g =>
      (yonedaDGFunctor C).onK.map f = (yonedaDGFunctor C).onK.map g → f = g) f g
      (fun f g hfg => ?_) hfg
    obtain ⟨ψ, hψ⟩ := Quotient.exact hfg
    exact Quotient.sound (homotopic_of_dPrime_yonedaPostcomp ψ hψ)

end DGCategory

end
