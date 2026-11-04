module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentPullbackCompSection

/-!
# The comparison of two pullback cotangent sheaves along a factorization, as a morphism

Let `f : X ⟶ S` be a morphism of schemes, `r : T ⟶ X` a second one and `s : T' ⟶ T` a third,
with `s ≫ r = rr`. This file defines the comparison morphism of `𝒪_{T'}`-modules

`s^*(r^*Ω_{X/S}) ⟶ rr^*Ω_{X/S}`

and shows that the comparison of global sections `Stacks.Smooth.pullbackCotangentCompSection` is
this morphism on global sections.

## Main definitions

* `Stacks.Smooth.pullbackCotangentCompHom`: **the comparison of the two pullback cotangent
  sheaves**, the composition comparison of inverse images of [Stacks Project, Tag 03LU] followed
  by the transport along the factorization.

## Main results

* `Stacks.Smooth.pullbackCotangentCompHom_eq`: the comparison, written out through its two
  factors.
* `Stacks.Smooth.pullbackCotangentCompSection_eq`: the comparison of global sections is the
  comparison of modules read on global sections, after pulling back along `s`.

## References

* [Stacks Project, Tag 01UQ](https://stacks.math.columbia.edu/tag/01UQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Smooth

open AlgebraicGeometry

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (r : T ⟶ X) (s : T' ⟶ T) (rr : T' ⟶ X)
  (hrr : s ≫ r = rr)

/-- **The comparison of two pullback cotangent sheaves along a factorization `s ≫ r = rr`**: the
composition comparison of inverse images of [Stacks Project, Tag 03LU], followed by the transport
of the inverse image along the factorization. -/
noncomputable def pullbackCotangentCompHom :
    (Scheme.Modules.pullback s).obj (pullbackCotangentSheaf f r) ⟶ pullbackCotangentSheaf f rr :=
  (Scheme.Modules.pullbackComp s r).hom.app (cotangentSheaf f) ≫
    (Scheme.Modules.pullbackCongr hrr).hom.app (cotangentSheaf f)

/-- The comparison, written out through its two factors. -/
theorem pullbackCotangentCompHom_eq :
    pullbackCotangentCompHom f r s rr hrr =
      (Scheme.Modules.pullbackComp s r).hom.app (cotangentSheaf f) ≫
        (Scheme.Modules.pullbackCongr hrr).hom.app (cotangentSheaf f) :=
  rfl

/-- **The comparison of global sections is the comparison of modules, on global sections**:
`Stacks.Smooth.pullbackCotangentCompSection` is `Stacks.Smooth.pullbackCotangentCompHom` at `⊤`
applied to the pullback along `s` of a global section. -/
theorem pullbackCotangentCompSection_eq (y : Γ(pullbackCotangentSheaf f r, (⊤ : T.Opens))) :
    pullbackCotangentCompSection f r s rr hrr y =
      (pullbackCotangentCompHom f r s rr hrr).val.app (op ⊤)
        (Scheme.Modules.pullbackSection s (pullbackCotangentSheaf f r) ⊤ ⊤ le_top y) :=
  rfl

end Stacks.Smooth

end
