module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekGeometricStalkIso
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperBaseChangeStalk

/-!
# Base change for the direct image with proper support

Consider a cartesian square of a big étale site
```
X' --p--> X
|f'       |f
v         v
Y' --g--> Y
```
with `f` separated and locally of finite type. For every abelian sheaf `F` on the small étale site
of `X` the pullback map `g⁻¹f_*F ⟶ f'_*(p⁻¹F)` of Sites, Section 06UM carries `g⁻¹f_!F`
isomorphically onto `f'_!(p⁻¹F)`: this is Stacks 0F55.

The proof is the one of the source. The pullback map sends `g⁻¹f_!F` into `f'_!(p⁻¹F)`, because
supports pull back into inverse images and properness is stable under base change
(`AlgebraicGeometry.SmallEtale.properSupportBaseChange`). On the stalk at a geometric point `ȳ'` of
`Y'` the resulting map is identified, through the canonical isomorphisms of Stacks 0F76 for `f` at
`g ∘ ȳ'` and for `f'` at `ȳ'`, with the identification of compactly supported sections on the
common geometric fibre `X'_{ȳ'} = X_{g ∘ ȳ'}`
(`AlgebraicGeometry.SmallEtale.isIso_properSupportBaseChange_of_bijective`); so it is an
isomorphism on every stalk, hence an isomorphism (Stacks 03PU).

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportBaseChangeIso` — **Stacks 0F55**, the isomorphism
  `g⁻¹f_! ≅ f'_!p⁻¹` of functors on abelian sheaves on the small étale site of `X`.
* `AlgebraicGeometry.SmallEtale.properSupportBaseChangeIso_hom_app` — its component at `F` is
  the base-change map `AlgebraicGeometry.SmallEtale.properSupportBaseChange`, which is the
  restriction of the pullback map `g⁻¹f_*F ⟶ f'_*(p⁻¹F)` along `f_! ⊆ f_*` and `f'_! ⊆ f'_*`
  (`AlgebraicGeometry.SmallEtale.properSupportBaseChange_comp_arrow`).

## Implementation notes

The hypotheses on `f'` are read off the square: it is locally of finite type
(`AlgebraicGeometry.SmallEtale.locallyOfFiniteType_of_isPullback`) and separated, both being
stable under base change. The coefficients are abelian groups in `AddCommGrpCat.{max (u + 1) v}`
for the scheme universe `u`; at `v = 0` this is `AddCommGrpCat.{u + 1}`, the universe of Stacks
0F5J (`AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso`).

## References

* [Stacks Project, Tag 0F55](https://stacks.math.columbia.edu/tag/0F55)
* [Stacks Project, Tag 0F76](https://stacks.math.columbia.edu/tag/0F76)
* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y X' Y' : B.Scheme}
  (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : IsPullback p f' f g)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]

omit [LocallyOfFiniteType (B.inclusion.map f)] in
include sq in
/-- The base change of a separated morphism along a cartesian square is separated. -/
theorem isSeparated_of_isPullback : IsSeparated (B.inclusion.map f') :=
  MorphismProperty.of_isPullback (sq.map B.inclusion) inferInstance

/-- **Stacks 0F55.** For a cartesian square of a big étale site with horizontal morphisms
`p : X' ⟶ X`, `g : Y' ⟶ Y` and vertical morphisms `f : X ⟶ Y` separated and locally of finite
type and `f' : X' ⟶ Y'`, there is an isomorphism `g⁻¹f_!F ≅ f'_!(p⁻¹F)`, natural in the abelian
sheaf `F` on the small étale site of `X`. Its component at `F` is the base-change map
`AlgebraicGeometry.SmallEtale.properSupportBaseChange`, the restriction of the pullback map
`g⁻¹f_*F ⟶ f'_*(p⁻¹F)` (`AlgebraicGeometry.SmallEtale.properSupportBaseChange_comp_arrow`), so
the isomorphism is the identification `f'_!(p⁻¹F) = g⁻¹f_!F` of the source inside
`f'_*(p⁻¹F)`. The hypotheses on `f'` are read off the square. -/
@[stacks 0F55]
public def properSupportBaseChangeIso :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    properSupportFunctor B f ⋙ abPullback.{u, v} B g ≅
      abPullback.{u, v} B p ⋙ properSupportFunctor B f' :=
  letI := locallyOfFiniteType_of_isPullback B p f' f g sq
  haveI := isSeparated_of_isPullback B p f' f g sq
  NatIso.ofComponents
    (fun F => @asIso _ _ _ _ (properSupportBaseChange.{u, v} B p f' f g sq F)
      (isIso_properSupportBaseChange_of_bijective.{u, v} B p f' f g sq F fun t ht =>
        ⟨bijective_fShriekStalkToCompactSections B f F (t.map (B.inclusion.map g)) ht,
          bijective_fShriekStalkToCompactSections B f' ((abPullback.{u, v} B p).obj F) t ht⟩))
    fun φ => (properSupportBaseChangeNatTrans.{u, v} B p f' f g sq).naturality φ

/-- The component of the isomorphism of Stacks 0F55 at `F` is the base-change map
`AlgebraicGeometry.SmallEtale.properSupportBaseChange`. -/
@[simp]
public theorem properSupportBaseChangeIso_hom_app
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    letI := locallyOfFiniteType_of_isPullback B p f' f g sq
    (properSupportBaseChangeIso.{u, v} B p f' f g sq).hom.app F =
      properSupportBaseChange.{u, v} B p f' f g sq F :=
  rfl

end AlgebraicGeometry.SmallEtale

end
