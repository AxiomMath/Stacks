module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.RegularSections

/-!
# The short exact sequence of a regular section

Let `L` be a sheaf of modules on a scheme `X`, let `s` be a global section of `L` and write
`f : 𝒪_X ⟶ L` for multiplication by `s`. Let `i : Z ⟶ X` be the closed subscheme of a
quasi-coherent ideal sheaf and write `g : L ⟶ i_* i^* L` for the unit of the
pullback–pushforward adjunction. This file proves

  `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0`

**short exact as soon as `f` is a monomorphism and `g` identifies `i_* i^* L` with the cokernel
of `f`** — which is the second half of [Stacks, Tag 0C6K] reduced to its first half. For the
zero scheme of `s` the monomorphy is regularity of `s` ([Stacks, Tag 01WY], which is literally
`Mono f`), and the cokernel identification is the first assertion of Tag 0C6K.

## Main results

* `CategoryTheory.ShortComplex.shortExact_of_cokernelIso`: in an abelian category, a
  monomorphism `f` followed by any map `g` that the cokernel projection factors as
  `cokernel.π f ≫ e.hom = g` for an isomorphism `e` is a short exact sequence, and `f ≫ g = 0`
  comes for free.
* `AlgebraicGeometry.Scheme.Modules.shortExact_of_mono_of_cokernelIso`: the same for
  `𝒪_X ⟶ L ⟶ i_* i^* L` over the closed subscheme of an arbitrary quasi-coherent ideal sheaf.
* `AlgebraicGeometry.Scheme.Modules.shortExact_of_isRegularSection_of_cokernelIso`: the same
  with monomorphy supplied by regularity of the section in the sense of
  `AlgebraicGeometry.IsRegularSection` ([Stacks, Tag 01WY]).

## Implementation notes

**What is generalized relative to Tag 0C6K.** The tag is about the zero scheme of a section of
an *invertible* sheaf. Neither invertibility nor the zero scheme is used by the argument here:
the ideal sheaf is arbitrary, and `L` is an arbitrary sheaf of modules. Specialising the ideal
sheaf to the zero scheme of `s` and adding invertibility gives back the statement of the tag.
`AlgebraicGeometry.IsRegularSection` is by definition `Mono (L.unitHomEquiv.symm s)`, so the
regularity hypothesis of the tag is exactly the monomorphy hypothesis here and nothing is
weakened by stating it that way.

**Why `f ≫ g = 0` is not an extra hypothesis.** `f ≫ g = (f ≫ cokernel.π f) ≫ e.hom` by the
factorisation hypothesis, and `f ≫ cokernel.π f = 0`. Stating the composite vanishing
separately would therefore have been a redundant — and, in the form "the section vanishes on its
own zero scheme", a non-trivial — extra assumption.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A monomorphism followed by a realisation of its cokernel is a short exact sequence.** If
`f` is a monomorphism and `e : cokernel f ≅ D` is an isomorphism through which the cokernel
projection factors as `g`, then `f ≫ g = 0` and `0 ⟶ A ⟶ B ⟶ D ⟶ 0` is short exact. -/
theorem shortExact_of_cokernelIso {A B D : C} (f : A ⟶ B) (hf : Mono f) {g : B ⟶ D}
    (e : cokernel f ≅ D) (he : cokernel.π f ≫ e.hom = g) :
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
  have := hf
  have hcomp : f ≫ g = 0 := by
    rw [← he, ← Category.assoc, cokernel.condition, zero_comp]
  refine ⟨hcomp, ?_⟩
  refine shortExact_of_iso (S₁ := ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e ?_ ?_) (shortExact_mk_cokernel_π f)
  · simp
  · simpa using he.symm

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Scheme.Modules

/-- **[Stacks, Tag 0C6K], second assertion, reduced to the first.** Let `s` be a global section
of a sheaf of modules `L` on a scheme `X` with `f : 𝒪_X ⟶ L` multiplication by `s` a
monomorphism, and let `i : Z ⟶ X` be the closed subscheme of a quasi-coherent ideal sheaf. If
the unit `g : L ⟶ i_* i^* L` of the pullback–pushforward adjunction realises `i_* i^* L` as the
cokernel of `f`, then `f ≫ g = 0` and

  `0 ⟶ 𝒪_X ⟶ L ⟶ i_* i^* L ⟶ 0`

is short exact.

Taking `I` to be the zero scheme of `s` and `L` invertible, this is the second statement of Tag
0C6K given its first. -/
theorem shortExact_of_mono_of_cokernelIso (X : Scheme.{u}) (L : X.Modules)
    (I : X.IdealSheafData) (s : L.sections) (hs : Mono (L.unitHomEquiv.symm s))
    (e : cokernel (L.unitHomEquiv.symm s) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj L))
    (he : cokernel.π (L.unitHomEquiv.symm s) ≫ e.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let f : O ⟶ L := L.unitHomEquiv.symm s
    let g : L ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj L) :=
      (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
  dsimp only
  exact ShortComplex.shortExact_of_cokernelIso _ hs e he

/-- **[Stacks, Tag 0C6K], second assertion, reduced to the first**, with the monomorphy
hypothesis spelled as regularity of the section in the sense of [Stacks, Tag 01WY]. This is the
same statement as `AlgebraicGeometry.Scheme.Modules.shortExact_of_mono_of_cokernelIso`:
`AlgebraicGeometry.IsRegularSection` is by definition the monomorphy of multiplication by the
section. -/
theorem shortExact_of_isRegularSection_of_cokernelIso (X : Scheme.{u}) (L : X.Modules)
    (I : X.IdealSheafData) (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    (e : cokernel (L.unitHomEquiv.symm s) ≅
      (Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj L))
    (he : cokernel.π (L.unitHomEquiv.symm s) ≫ e.hom =
      (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let f : O ⟶ L := L.unitHomEquiv.symm s
    let g : L ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj L) :=
      (Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι).unit.app L
    ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact :=
  shortExact_of_mono_of_cokernelIso X L I s hs e he

end AlgebraicGeometry.Scheme.Modules

end
