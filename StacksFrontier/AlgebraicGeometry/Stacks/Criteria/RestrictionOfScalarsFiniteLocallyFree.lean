module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMorphismsFiniteLocallyFree

/-!
# Algebraicity of the restriction of scalars along a finite locally free morphism (Stacks 05YF)

Let `S` be a scheme contained in a big fppf site and let `x : X ⟶ Z` and `z : Z ⟶ Q` be morphisms
of algebraic spaces over `S` — the source writes the base `Q` as `B`, a name that here belongs to
the site. Stacks 05YF asserts that the restriction of scalars `Res_{Z/Q}(X)` of Stacks 05YA is an
algebraic space over `S` when `z` is finite locally free.

The proof is the source's: the square

```text
Mor_Q(Z, X) ⟶ Mor_Q(Z, Z)
     ↑              ↑ id_Z
Res_{Z/Q}(X) ⟶     Q
```

is cartesian in presheaves on the big fppf site of `S` by Stacks 05YE, the two relative morphism
functors in it are algebraic spaces by Stacks 05Y7 applied to the targets `X` and `Z`, and a fibre
product of algebraic spaces over an fppf sheaf with representable diagonal is an algebraic space
by Stacks 04T9.

Stacks 04T9 is used in the form that needs no algebraicity of the lower right corner of the
square it is applied to, only the sheaf condition and representability of the diagonal; both are
available for `Mor_Q(Z, Z)`, the first as Stacks 05Y3 and the second as a field of the
algebraicity supplied by Stacks 05Y7. Algebraicity of the two upper corners is used in full.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree`:
  **Stacks 05YF**, with the hypotheses the library's Stacks 05Y7 carries inherited.

## Implementation notes

Stacks 05Y7 is available here only in the conditional form
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree`, which names two
hypotheses: the case of a target representable by an object of the site, and the input
Stacks 05XR. Those are inherited here rather than discharged, and the conditionality is base's,
not a weakening of the statement of Stacks 05YF. Only the first is a missing result: Stacks 05XR
in this form holds outright by
`AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale`, and Stacks 05XQ by
`AlgebraicGeometry.Space.isFibreSectionsSurjective`; the form of Stacks 05YF with `h05XR_X` and
`h05XR_Z` discharged, so that only `hrepresentable` is carried beyond the source's `hz`, is
`Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_of_representable` in
`StacksFrontier/AlgebraicGeometry/Spaces/FibreSectionsAlgebraicEtale.lean`, which is downstream of
this file because the proof of Stacks 05XR for the fibre data needs the finiteness input from
Stacks 03ZU.

The two applications of Stacks 05Y7 share the hypothesis on a representable target, which depends
only on `z` and not on the target of the relative morphism functor; the input from Stacks 05XR
does depend on the target, so it appears twice, once for `X` and once for `Z`.

## References

* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05YE](https://stacks.math.columbia.edu/tag/05YE)
* [Stacks Project, Tag 05Y7](https://stacks.math.columbia.edu/tag/05Y7)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
* [Stacks Project, Tag 04T9](https://stacks.math.columbia.edu/tag/04T9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05YF.** Let `S` be a scheme contained in a big fppf site, and let `x : X ⟶ Z` and
`z : Z ⟶ Q` be morphisms of algebraic spaces over `S`. If `z` is finite locally free then the
restriction of scalars `Res_{Z/Q}(X)` of Stacks 05YA is an algebraic space over `S`.

The proof is the source's: the cartesian square of Stacks 05YE exhibits `Res_{Z/Q}(X)` as the
fibre product of `Mor_Q(Z, X)` and `Q` over `Mor_Q(Z, Z)`, the two relative morphism functors are
algebraic spaces by Stacks 05Y7, and Stacks 04T9 makes the fibre product one.

The three hypotheses besides `hz` are the two that the library's Stacks 05Y7 carries, taken at
the two targets `X` and `Z` of the two applications made here; see
`AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree`.

This is the general form, which takes that input as a hypothesis, and it carries no Stacks tag.
Stacks 05YF is registered on
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_source`,
which proves the same conclusion at the hypotheses of the source, with nothing carried. -/
theorem isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree
    {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q)
    (hz : IsFiniteLocallyFree B S hS z)
    (h05XR_X : ∀ (U : BigFppfOver B S hS) (c : yoneda.obj U ⟶ X.obj),
      IsFibreSectionsAlgebraicEtale B S hS
        (ObjectProperty.homMk c :
          (schemeSpace U : AlgebraicSpaces B S hS) ⟶ X) z)
    (h05XR_Z : ∀ (U : BigFppfOver B S hS) (c : yoneda.obj U ⟶ Z.obj),
      IsFibreSectionsAlgebraicEtale B S hS
        (ObjectProperty.homMk c :
          (schemeSpace U : AlgebraicSpaces B S hS) ⟶ Z) z)
    (hrepresentable : ∀ (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ Q.obj),
      IsAlgebraicSpace B S hS
        (relativeHom B S hS Z.obj (yoneda.obj U) Q.obj z.hom u Z.property
          (isAlgebraicSpace_yoneda B S hS U) Q.property)) :
    IsAlgebraicSpace B S hS (restrictionOfScalars B S hS x z).presheaf := by
  have hMorX : IsAlgebraicSpace B S hS
      (relativeHom B S hS Z.obj X.obj Q.obj z.hom (x.hom ≫ z.hom) Z.property X.property
        Q.property) :=
    isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree B S hS Z.obj X.obj Q.obj z.hom
      (x.hom ≫ z.hom) Z.property X.property Q.property hz h05XR_X hrepresentable
  have hMorZ : IsAlgebraicSpace B S hS
      (relativeHom B S hS Z.obj Z.obj Q.obj z.hom z.hom Z.property Z.property Q.property) :=
    isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree B S hS Z.obj Z.obj Q.obj z.hom z.hom
      Z.property Z.property Q.property hz h05XR_Z hrepresentable
  exact isAlgebraicSpace_of_isPullback hMorX Q.property
    (isSheaf_relativeHom B S hS Z.obj Z.obj Q.obj z.hom z.hom Z.property Z.property Q.property)
    hMorZ.diagonal_representable (isPullback_restrictionOfScalars_relativeHomData x z)

end AlgebraicGeometry.Space

end
