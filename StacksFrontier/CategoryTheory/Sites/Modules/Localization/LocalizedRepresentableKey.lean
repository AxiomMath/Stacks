module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableKey.CompositeAdjuncts
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableKey.ShriekCounitCrossing
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableKey.TransposedComparison

/-!
# The comparison of Stacks 04J7 transposed across the lower shriek

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`, `G = h_V^#` and `F = f^{-1}G`.
`AlgebraicGeometry.RingedSite.Hom.localizedRepresentableCompInverseImageIso` compares the
inverse images of the two composites

```
  ι_V ∘ f'_{04J0}  and  f'_{04IF} ∘ compareMid
```

of Stacks 04J7, and `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` promotes that
comparison to a 2-isomorphism once the comparison is known to be compatible with the two
structure maps. Since both structure maps have been computed in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/LocalizedRepresentableTwoIso.lean`, that
compatibility reduces to one equation with no structure map in it, between two morphisms of
`Sh(C/U)`.

This file carries that equation across the bijection of `j_{U!} ⊣ j_U^{-1}`, where the two
sides become morphisms of `Sh(C)` and every factor is described by a lemma of the library:
the factor of
Stacks 03CF's clause (b) by
`CategoryTheory.SliceTopos.shriek_overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit`,
and the two occurrences of Stacks 04J3's comparison — at `V` restricted along `f'`, and at `U` —
by
`AlgebraicGeometry.RingedSite.shriek_representableLocalizationInverseImageIso_hom_app_comp_counit`
at the two objects.

## Main results

* `CategoryTheory.Adjunction.homEquiv_symm_comp₂` and
  `CategoryTheory.Adjunction.homEquiv_symm_comp₃`: the adjunct of a composite of two or three
  morphisms is the left adjoint applied to each factor, followed by the counit.
* `CategoryTheory.Equivalence.trans_unitInv_app`: the inverse unit of a composite of two
  equivalences.
* `Hom.shriek_restrictedRepresentableLocalizationInverseImageIso_comp_counit`: the 04J0 side of the
  transposed equation, with Stacks 03CF's clause (b) already cancelled: Stacks 04J3's comparison at
  `V` restricted along `f'` and read through `j_{U!}` is Stacks 03CF's comparison
  `j_{U!}(f')^{-1} ≅ f^{-1}j_{V!}` followed by `f^{-1}` of Stacks 00Y1's identification and of the
  counit of the lower shriek of the localization at `h_V^#`.
* `AlgebraicGeometry.RingedSite.Hom.shriek_localizedCompareMidComp_comp_counit`: the 04IF side,
  with Stacks 04J3's comparison at `U` replaced by Stacks 00Y1's identification followed by the
  counit of the lower shriek of the localization at `h_U^#`.

## Implementation notes

Every step is an explicit term — `Eq.trans`, `congrArg`, naturality — and not a `rewrite` or a
`simp`. Two spellings of one functor occur throughout (`(f.over G).inverseImage` against
`Over.post f^{-1}`, and the inverse image of a morphism of ringed topoi against the sheaf
pullback of the underlying continuous functor), and they agree only at default transparency,
which is what a term-mode proof checks at and a rewrite's keyed matching does not.

For the same reason `Hom.shriek_localizedCompareMidComp_comp_counit` states the whole 04IF side
of the transposed equation rather than only its last two factors: a `congrArg` whose argument is
instantiated outside the goal can carry a different instance term for the sheaf pullback along
`u`, and then it no longer matches a subterm that prints identically to it, whereas the
statement as a whole is matched against the goal at default transparency.

## References

* [Stacks, Tag 04J7](https://stacks.math.columbia.edu/tag/04J7)
-/
