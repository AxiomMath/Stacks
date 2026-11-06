module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperComplete
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.CartesianHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAdicThickeningsFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.EtaleChartLiftsFiniteOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SourceFiniteOrderMorphismImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified

/-!
# A cartesian tower of algebraic spaces over the adic fibres, finite at the bottom

Let `A` be a ring, `I ⊆ A` an ideal, `X` an algebraic space over `Spec A` and `X_n` its adic
fibres over `Spec (A / I ^ (n + 1))`. A *cartesian tower over the adic fibres* is a family of
algebraic spaces `Y_n` with morphisms `y_n : Y_n ⟶ X_n` and `t_n : Y_n ⟶ Y_{n + 1}` such that
every square

```
Y_n --t_n--→ Y_{n+1}
 |              |
y_n          y_{n+1}
 ↓              ↓
X_n ---------→ X_{n+1}
```

is cartesian. This is the input of Stacks 0A01. The first step of the source's proof is that,
since the base change of `y_n` to `X_0` is `y_0`, finiteness of `y_0` forces finiteness of every
`y_n`, by Stacks 09ZZ. This file carries out that step.

## Main definitions

* `AlgebraicGeometry.Space.adicFibreSuccHom`: the transition `X_n ⟶ X_{n + 1}` between adic
  fibres, as a morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isFirstOrderThickening_range_adicFibreSucc`: `X_n ⊂ X_{n + 1}` is a
  first-order thickening (Stacks 09ZX, base change of `Spec (A / I ^ (n + 1)) ⊂
  Spec (A / I ^ (n + 2))`).
* `AlgebraicGeometry.Space.isFinite_succ_of_isPullback`: one step of the induction, Stacks
  09ZZ (8) applied to the cartesian morphism of thickenings `(Y_n ⊂ Y_{n+1}) ⟶ (X_n ⊂ X_{n+1})`.
* `AlgebraicGeometry.Space.isFinite_of_isPullback_tower`: every `y_n` is finite once `y_0` is.

## Implementation notes

Stacks 09ZZ is stated for thickenings presented as subfunctors, while the tower is given by
morphisms. Both vertical inclusions are monomorphisms (base changes of the closed immersion of
schemes `Spec (A / I ^ (n + 1)) ⟶ Spec (A / I ^ (n + 2))`), hence isomorphisms onto their
ranges, and the square of ranges is again cartesian; finiteness is carried across those
isomorphisms by `AlgebraicGeometry.Space.isFinite_comp` and
`AlgebraicGeometry.Space.isFinite_of_isIso`.

## References

* [Stacks Project, Tag 0A01](https://stacks.math.columbia.edu/tag/0A01)
* [Stacks Project, Tag 09ZZ](https://stacks.math.columbia.edu/tag/09ZZ)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))

/-- The transition morphism `Spec (A / I ^ (n + 1)) ⟶ Spec (A / I ^ (n + 2))` of the adic
thickenings has monomorphic Yoneda image: it is a closed immersion of schemes, hence a
monomorphism of the big fppf category, and the Yoneda embedding preserves monomorphisms. -/
theorem mono_yoneda_map_adicThickeningSuccMap (n : ℕ) :
    Mono (yoneda.map (adicThickeningSuccMap A I B hA (contains_adicThickening A I B hA) n)) := by
  have hmono : Mono ((BigFppfOver.toScheme B (Spec (.of A)) hA).map
      (adicThickeningSuccMap A I B hA (contains_adicThickening A I B hA) n)) := by
    have h := (isFirstOrderThickening_adicThickeningSucc A I n).1
    exact inferInstanceAs (Mono (adicThickeningSucc A I n))
  have : Mono (adicThickeningSuccMap A I B hA (contains_adicThickening A I B hA) n) :=
    (BigFppfOver.toScheme B (Spec (.of A)) hA).mono_of_mono_map hmono
  infer_instance

/-- The range of the transition morphism of the represented adic thickenings is a first-order
thickening of the algebraic space represented by `Spec (A / I ^ (n + 2))`. -/
theorem isFirstOrderThickening_range_yoneda_adicThickeningSuccMap (n : ℕ) :
    IsNthOrderThickening B (Spec (.of A)) hA 1
      ((schemeSpaceFunctor B (Spec (.of A)) hA).obj
        (adicThickeningObject A I B hA (contains_adicThickening A I B hA) (n + 1)))
      (Subfunctor.range
        (yoneda.map (adicThickeningSuccMap A I B hA (contains_adicThickening A I B hA) n))) :=
  isNthOrderThickening_range_yoneda_map B (Spec (.of A)) hA 1 _
    ⟨(isFirstOrderThickening_adicThickeningSucc A I n).1,
      (isFirstOrderThickening_adicThickeningSucc A I n).2⟩

variable {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (baseObject A B hA))

/-- The transition `X_n ⟶ X_{n + 1}` between consecutive adic fibres, as a morphism of algebraic
spaces. -/
abbrev adicFibreSuccHom (n : ℕ) :
    adicFibreSpace A I B hA hX f n ⟶ adicFibreSpace A I B hA hX f (n + 1) :=
  ObjectProperty.homMk (adicFibreSucc A I B hA (contains_adicThickening A I B hA) f n)

/-- The cartesian square `X_n = X_{n + 1} ×_{S_{n + 1}} S_n`, read in the category of algebraic
spaces, with the represented thickening inclusion as its bottom edge. -/
theorem isPullback_adicFibreSuccHom (n : ℕ) :
    IsPullback (ObjectProperty.homMk (adicFibreSnd A I B hA f n) :
        adicFibreSpace A I B hA hX f n ⟶ (schemeSpaceFunctor B (Spec (.of A)) hA).obj
          (adicThickeningObject A I B hA (contains_adicThickening A I B hA) n))
      (adicFibreSuccHom A I B hA hX f n)
      ((schemeSpaceFunctor B (Spec (.of A)) hA).map
        (adicThickeningSuccMap A I B hA (contains_adicThickening A I B hA) n))
      (ObjectProperty.homMk (adicFibreSnd A I B hA f (n + 1))) := by
  refine IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι
      (fun F : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B (Spec (.of A)) hA F)) ?_
  exact (isPullback_adicFibreSucc A I B hA (contains_adicThickening A I B hA) f n).flip

/-- **`X_n ⊂ X_{n + 1}` is a first-order thickening**: the base change of the first-order
thickening `Spec (A / I ^ (n + 1)) ⊂ Spec (A / I ^ (n + 2))`, by Stacks 09ZX. -/
theorem isFiniteOrderThickening_range_adicFibreSucc (n : ℕ) :
    IsFiniteOrderThickening B (Spec (.of A)) hA (adicFibreSpace A I B hA hX f (n + 1))
      (Subfunctor.range (adicFibreSucc A I B hA (contains_adicThickening A I B hA) f n)) :=
  isFiniteOrderThickening_range_of_isPullback B (Spec (.of A)) hA
    (isPullback_adicFibreSuccHom A I B hA hX f n)
    ⟨1, isFirstOrderThickening_range_yoneda_adicThickeningSuccMap A I B hA n⟩

/-- The transition `X_n ⟶ X_{n + 1}` between adic fibres is a monomorphism, being a base change
of a monomorphism. -/
theorem mono_adicFibreSucc (n : ℕ) :
    Mono (adicFibreSucc A I B hA (contains_adicThickening A I B hA) f n) := by
  have := mono_yoneda_map_adicThickeningSuccMap A I B hA n
  exact (isPullback_adicFibreSucc A I B hA (contains_adicThickening A I B hA) f n).mono_fst_of_mono

/-- A monomorphism whose range is a finite order thickening of the target is a thickening. -/
private theorem isThickeningHom_of_isFiniteOrderThickening_range
    {X X' : AlgebraicSpaces B (Spec (.of A)) hA} (i : X ⟶ X') [Mono i.hom]
    (h : IsFiniteOrderThickening B (Spec (.of A)) hA X' (Subfunctor.range i.hom)) :
    IsThickeningHom B (Spec (.of A)) hA i :=
  (isThickeningHom_iff_of_mono i).2 h.choose_spec.1

/-- The transition `X_n ⟶ X_{n + 1}` is a thickening in the morphism sense. -/
theorem isThickeningHom_adicFibreSuccHom (n : ℕ) :
    IsThickeningHom B (Spec (.of A)) hA (adicFibreSuccHom A I B hA hX f n) :=
  have : Mono (adicFibreSuccHom A I B hA hX f n).hom := mono_adicFibreSucc A I B hA f n
  isThickeningHom_of_isFiniteOrderThickening_range A B hA _
    (isFiniteOrderThickening_range_adicFibreSucc A I B hA hX f n)

variable {A I B hA hX f}

/-- **One step of Stacks 09ZZ (8) along the tower.** In a cartesian square
`Y_n = Y_{n + 1} ×_{X_{n + 1}} X_n` over the transition between two consecutive adic fibres, if
`Y_n ⟶ X_n` is finite then so is `Y_{n + 1} ⟶ X_{n + 1}`. -/
theorem isFinite_succ_of_isPullback (n : ℕ) {Yn Yn' : AlgebraicSpaces B (Spec (.of A)) hA}
    (y : Yn ⟶ adicFibreSpace A I B hA hX f n) (y' : Yn' ⟶ adicFibreSpace A I B hA hX f (n + 1))
    (t : Yn ⟶ Yn') (hcart : IsPullback t y y' (adicFibreSuccHom A I B hA hX f n))
    (hy : IsFinite B (Spec (.of A)) hA y.hom) :
    IsFinite B (Spec (.of A)) hA y'.hom := by
  have hj := isThickeningHom_adicFibreSuccHom A I B hA hX f n
  have := hj.mono
  have : Mono t.hom :=
    (AlgebraicSpaces.isPullback_hom B (Spec (.of A)) hA hcart).flip.mono_snd_of_mono
  have hsrc : IsFiniteOrderThickening B (Spec (.of A)) hA Yn' (Subfunctor.range t.hom) :=
    isFiniteOrderThickening_range_of_isPullback B (Spec (.of A)) hA hcart.flip
      (isFiniteOrderThickening_range_adicFibreSucc A I B hA hX f n)
  have hi : IsThickeningHom B (Spec (.of A)) hA t :=
    isThickeningHom_of_isFiniteOrderThickening_range A B hA t hsrc
  let M : CartesianSourceFiniteOrderMorphismOfThickenings B (Spec (.of A)) hA :=
    { X' := Yn'
      Y' := adicFibreSpace A I B hA hX f (n + 1)
      X := Subfunctor.range t.hom
      Y := Subfunctor.range (adicFibreSucc A I B hA (contains_adicThickening A I B hA) f n)
      sourceFiniteOrder := hsrc
      targetThickening := hj.2
      morphism := Arrow.homMk (rangeMap hi hj y) y'.hom
        (rangeMap_comp_ι hi hj (congrArg (fun k => k.hom) hcart.w.symm))
      cartesian := by
        refine (AlgebraicSpaces.isPullback_hom B (Spec (.of A)) hA hcart.flip).of_iso
          hi.isoRange hj.isoRange (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
        · simp [rangeMap]
        · simp
        · rw [Iso.refl_hom, Category.comp_id]
          exact (IsThickeningHom.isoRange_hom_ι hj).symm
        · simp }
  have hf : IsFinite B (Spec (.of A)) hA M.f := by
    show IsFinite B (Spec (.of A)) hA (hi.isoRange.inv ≫ y.hom ≫ hj.isoRange.hom)
    exact isFinite_comp B _ hA (isFinite_of_isIso B _ hA _)
      (isFinite_comp B _ hA hy (isFinite_of_isIso B _ hA _))
  exact M.isFinite_iff.mp hf

/-- **Every level of a cartesian tower over the adic fibres is finite once the bottom level is.**
This is the first step of the proof of Stacks 0A01: the base change of `y_n` to `X_0` is `y_0`,
so Stacks 09ZZ makes every `y_n` finite. -/
theorem isFinite_of_isPullback_tower (Y : ℕ → AlgebraicSpaces B (Spec (.of A)) hA)
    (y : ∀ n, Y n ⟶ adicFibreSpace A I B hA hX f n) (t : ∀ n, Y n ⟶ Y (n + 1))
    (hcart : ∀ n, IsPullback (t n) (y n) (y (n + 1)) (adicFibreSuccHom A I B hA hX f n))
    (hfin : IsFinite B (Spec (.of A)) hA (y 0).hom) (n : ℕ) :
    IsFinite B (Spec (.of A)) hA (y n).hom := by
  induction n with
  | zero => exact hfin
  | succ n ih => exact isFinite_succ_of_isPullback n (y n) (y (n + 1)) (t n) (hcart n) ih

end AlgebraicGeometry.Space

end
