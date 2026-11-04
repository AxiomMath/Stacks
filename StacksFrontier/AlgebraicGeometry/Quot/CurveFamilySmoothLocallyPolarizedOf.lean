module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesEtaleLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# A family of curves is smooth locally polarized, given the smoothness half of Stacks 0DQ0

`AlgebraicGeometry.CurveFamily.IsSmoothLocallyPolarized` is the shape in which Stacks 0E6F and
Stacks 0E88 consume the smoothness half of Stacks 0DQ0. For every point `t` of the base of a
family of curves `X ⟶ T` it asks for three things: a smooth `π : T' ⟶ T` of the site through
`t`, a scheme `Z` together with a cartesian square identifying `Z` with the base change
`X_{T'}`, and an invertible module on `Z` that is ample relative to `Z ⟶ T'`.

The source's proof of the smoothness half reads
`PolarizedCurves ×_{𝒞urves} T ⊂ Picardstack_{X/T}`
as the open substack of objects whose module is ample (Stacks 0D3D). That substack is smooth over
`T` because `Picardstack_{X/T}` is algebraic (Stacks 0D04, from Stacks 09DS) and smooth over `T`
(Stacks 0DPJ). Through every point of `T` the substack is non-empty, which is the surjectivity
half (`AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSquare_snd`). Restricted to a
smooth chart of that open substack, the universal invertible module is ample relative to the base
change of `X` in the sense of Stacks 0D31 (`AlgebraicGeometry.Space.IsRelativelyAmple`).

Of the four, only Stacks 0D3D is stated in the library
(`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`);
Stacks 0D04, 09DS and 0DPJ have none. Their combined output, at a single point of the base, is
therefore taken here as one explicit input, `hchart`. Its shape is a **guess**, chosen to be the
most direct form of what the source's argument yields:

* a smooth chart `π : T' ⟶ T` through the point;
* the base change of `X` along `π`, as a cartesian square of algebraic spaces;
* an invertible module on the base change that is ample relative to the projection, in the
  space-level sense of Stacks 0D31.

The work done here is the passage from the space-level conclusion to the scheme-level one that
`IsSmoothLocallyPolarized` asks for. A relatively ample module lives on a morphism that is
representable, so the base change is a scheme `Z`. Stacks 0D31, read at the identity of `T'`,
then says that the pullback of the module to `Z` is invertible and ample relative to `Z ⟶ T'`.

No tag is registered in this file.

## Main results

* `AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of`.

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **A family of curves is smooth locally polarized**, given the smoothness half of Stacks
0DQ0 at each point of its base. The input `hchart` provides, through every point `t` of the
base, three things:

* a smooth chart `π : T' ⟶ X.base`;
* the base change `X_{T'}` of `X` along `π`, as a cartesian square of algebraic spaces;
* an invertible module on `X_{T'}` that is ample relative to `X_{T'} ⟶ T'` in the sense of
  Stacks 0D31.

That is what the source's argument through Stacks 0D04, 0DPJ and 0D3D produces. The shape of
`hchart` is a guess, pending statements of Stacks 0D04, 09DS and 0DPJ.

Relative ampleness in the sense of Stacks 0D31 includes representability. Read along the
identity of `T'`, the base change is therefore a scheme `Z`, and the pullback of the module to
`Z` is invertible and ample relative to `Z ⟶ T'` (Stacks 01VH). -/
theorem isSmoothLocallyPolarized_of (X : CurveFamily B hZ)
    (hchart : ∀ t : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
      ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
        t ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
        ∃ (Xs : AlgebraicSpaces B integerBase hZ) (p : Xs ⟶ X.total) (q : Xs ⟶ schemeSpace T'),
          IsPullback p q X.toBase (schemeSpaceMap π) ∧
          ∃ L : Space.Modules.{u, u} B integerBase hZ Xs.1 Xs.2,
            Space.IsRelativelyAmple B integerBase hZ q L) :
    X.IsSmoothLocallyPolarized := by
  intro t
  obtain ⟨T', π, hsm, ht, Xs, p, q, hpb, L, hL⟩ := hchart t
  obtain ⟨Z, q₁, p₁, h₁⟩ := hL.1 (𝟙 (yoneda.obj T'))
  obtain ⟨hinv, hamp⟩ := hL.2 T' Z (𝟙 _) p₁ q₁ h₁
  -- the cartesian square `Z = X_{T'}`, read in the category of algebraic spaces
  have h₁' : IsPullback (ObjectProperty.homMk p₁ : schemeSpace Z ⟶ Xs) (schemeSpaceMap q₁) q
      (𝟙 (schemeSpace T')) := by
    refine IsPullback.of_map (ObjectProperty.ι _) ?_ ?_
    · apply ObjectProperty.hom_ext
      simp only [ObjectProperty.FullSubcategory.comp_hom, Category.comp_id]
      exact h₁.w.trans (Category.comp_id _)
    · exact h₁
  have hpaste := h₁'.paste_horiz hpb
  rw [Category.id_comp] at hpaste
  exact ⟨T', π, hsm, ht, Z, ObjectProperty.homMk p₁ ≫ p, q₁, hpaste,
    Space.baseChangeModule B integerBase hZ L Z p₁, hinv, hamp⟩

end AlgebraicGeometry.CurveFamily

end
