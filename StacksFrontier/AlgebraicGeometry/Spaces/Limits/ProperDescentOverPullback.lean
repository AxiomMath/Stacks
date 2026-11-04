module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.ProperMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase

/-!
# Stacks 08K1 for an inverse system indexed by a directed preorder, under the convention 07SD

The 0DLN reduction to a base of finite type over `ℤ` uses Stacks 08K1 in one form: an inverse
system `D` indexed by the opposite of a directed preorder, a morphism `f : X ⟶ Y` of spaces over
a stage `D i`, its base changes `((Over.pullback _).map f).left`, and the convention 07SD written
out as in `AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_chartLimitsInSite`. This file
derives that form from Stacks 08K1 for an `AlgebraicGeometry.Space.MorphismDescentSituation`
under the convention, `SiteContainsBaseChangeLimits` of the system of bases. The limit of the
system is an algebraic space by Stacks 07SF under the convention
(`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_chartLimitsInSite`), so the data form a
situation of Stacks 084W.

That form of Stacks 08K1 is a hypothesis here. The base proves Stacks 08K1 only for an
`AlgebraicGeometry.Space.MorphismDescentSystem`
(`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isProper_mapAt`), whose index is bounded
by the cofinality of the cutoff. The systems the reduction uses are indexed by `Finset A` for a
ring `A` below the cutoff, which need not meet that bound.

## Main results

* `AlgebraicGeometry.Space.isProper_overPullback_map_iff_isProper_pullbackLift`: the base change
  of `f` along `g`, read as a morphism of `Over`, is proper if and only if the base change in the
  form of `AlgebraicGeometry.Space.MorphismDescentSituation.mapAt` is.
* `AlgebraicGeometry.Space.exists_isProper_overPullback_map_of_chartLimitsInSite`: Stacks 08K1
  for an inverse system indexed by the opposite of a directed preorder, given Stacks 08K1 for a
  situation of Stacks 084W under the convention.
* `AlgebraicGeometry.Space.exists_isProper_overPullback_map_of_chartLimitsInSite_properInSite`:
  the same with that hypothesis discharged by
  `MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 084W](https://stacks.math.columbia.edu/tag/084W)
* [Stacks Project, Tag 08K1](https://stacks.math.columbia.edu/tag/08K1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Base change of a morphism over a base, in two forms, for properness.** Let `f : X ⟶ Y` be
a morphism of presheaves over `T` and `g : T' ⟶ T`. The base change
`((Over.pullback g).map f).left` from `X ×_T T'` to `Y ×_T T'` is proper if and only if the
morphism `T' ×_T X ⟶ T' ×_T Y` which is the identity on `T'` and `f` on the other factor is
proper. The two differ by the symmetry isomorphisms of the fibre products. -/
theorem isProper_overPullback_map_iff_isProper_pullbackLift
    {T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X Y : Over T} (f : X ⟶ Y) (g : T' ⟶ T) :
    IsProper B S hS ((Over.pullback g).map f).left ↔
      IsProper B S hS (pullback.lift (pullback.fst g X.hom) (pullback.snd g X.hom ≫ f.left)
        (by rw [pullback.condition, Category.assoc, Over.w f]) :
          pullback g X.hom ⟶ pullback g Y.hom) := by
  have h : ((Over.pullback g).map f).left = (pullbackSymmetry X.hom g).hom ≫
      pullback.lift (pullback.fst g X.hom) (pullback.snd g X.hom ≫ f.left)
        (by rw [pullback.condition, Category.assoc, Over.w f]) ≫
      (pullbackSymmetry Y.hom g).inv := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.lift_snd]
      simp only [pullbackSymmetry_hom_comp_snd_assoc]
      exact pullback.lift_fst _ _ _
    · rw [Category.assoc, Category.assoc, pullbackSymmetry_inv_comp_snd, pullback.lift_fst]
      simp only [pullbackSymmetry_hom_comp_fst]
      exact pullback.lift_snd _ _ _
  rw [h]
  exact (isProper_isIso_comp_iff B S hS _ _).trans (isProper_comp_isIso_iff B S hS _ _)

/-- **Stacks 08K1 for a system indexed by the opposite of a directed preorder, given Stacks 08K1
under the convention.** Let `D` be an inverse system of algebraic spaces over `S` indexed by
`Jᵒᵖ`, `J` a directed preorder, with affine transition morphisms, satisfying the chapter's
convention 07SD (written out as in
`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_of_chartLimitsInSite`). Let `f : X ⟶ Y` be
a morphism, locally of finite type, of quasi-compact and quasi-separated algebraic spaces over a
quasi-compact and quasi-separated stage `D i`. If the base change of `f` to the limit is proper,
then so is its base change to some stage `j` over `i`.

The hypothesis `h08K1` is Stacks 08K1 for a situation of Stacks 084W,
`AlgebraicGeometry.Space.MorphismDescentSituation`, under the convention
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits` of its system of bases. It is applied to
the situation with base `D`, distinguished stage `i` and morphism `f`; the limit of `D` is an
algebraic space by Stacks 07SF under the convention
(`AlgebraicGeometry.Space.isAlgebraicSpace_limit_of_chartLimitsInSite`). -/
theorem exists_isProper_overPullback_map_of_chartLimitsInSite (hZ : B.Contains (⊤_ Scheme.{u}))
    (h08K1 : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi))
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (D : Jᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hconv : ∀ (i : Jᵒᵖ) (Z : BigAffineFppf B S hS)
      (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
      (W : Over i ⥤ BigAffineFppf B S hS),
      (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
        (Over.post (X := i) D ⋙ Over.pullback g) ⋙
          Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
      ∀ c : Cone (((W ⋙ BigAffineFppf.inclusion B S hS) ⋙
          BigFppfOver.forget B S hS) ⋙ B.inclusion),
        IsLimit c → B.Contains c.pt)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAff : ∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (i : Jᵒᵖ) {X Y : Over (D.obj i)} (f : X ⟶ Y)
    (hBqc : IsQuasiCompactSpace B S hS (D.obj i))
    (hBqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hX : IsAlgebraicSpace B S hS X.left) (hY : IsAlgebraicSpace B S hS Y.left)
    (hXqc : IsQuasiCompactSpace B S hS X.left) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.left)
    (hYqc : IsQuasiCompactSpace B S hS Y.left) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.left)
    (proper : IsProper B S hS ((Over.pullback (limit.π D i)).map f).left)
    (ft : IsLocallyOfFiniteType B S hS f.left) :
    ∃ (j : Jᵒᵖ) (e : j ⟶ i), IsProper B S hS ((Over.pullback (D.map e)).map f).left := by
  have : Nonempty J := ⟨i.unop⟩
  let M : MorphismDescentSituation B S hS hZ J :=
    { base := D
      base_isAlgebraicSpace := fun j => hD (op j)
      transition_affine := hAff
      limit_isAlgebraicSpace :=
        isAlgebraicSpace_limit_of_chartLimitsInSite B S hS D hconv hD hAff i hBqc
      initial := i.unop
      source₀ := X.left
      target₀ := Y.left
      sourceToBase := X.hom
      targetToBase := Y.hom
      map₀ := f.left
      map₀_over := Over.w f
      source₀_isAlgebraicSpace := hX
      target₀_isAlgebraicSpace := hY
      base₀_quasiCompact := hBqc
      base₀_quasiSeparated := hBqs
      source₀_quasiCompact := hXqc
      source₀_quasiSeparated := hXqs
      target₀_quasiCompact := hYqc
      target₀_quasiSeparated := hYqs }
  obtain ⟨k, le, hk⟩ := h08K1 M (siteContainsBaseChangeLimits_of_chartLimitsInSite B S hS D hconv)
    ((isProper_overPullback_map_iff_isProper_pullbackLift B S hS f (limit.π D i)).1 proper) ft
  exact ⟨op k, (homOfLE le).op,
    (isProper_overPullback_map_iff_isProper_pullbackLift B S hS f (D.map (homOfLE le).op)).2 hk⟩

/-- **Stacks 08K1 for a system indexed by the opposite of a directed preorder, under the
convention 07SD**. This is
`AlgebraicGeometry.Space.exists_isProper_overPullback_map_of_chartLimitsInSite` with its
hypothesis `h08K1` discharged by Stacks 08K1 for a situation of Stacks 084W under the convention,
`MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem exists_isProper_overPullback_map_of_chartLimitsInSite_properInSite
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (D : Jᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hconv : ∀ (i : Jᵒᵖ) (Z : BigAffineFppf B S hS)
      (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ D.obj i)
      (W : Over i ⥤ BigAffineFppf B S hS),
      (W ⋙ (BigAffineFppf.inclusion B S hS ⋙ yoneda) ≅
        (Over.post (X := i) D ⋙ Over.pullback g) ⋙
          Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))) →
      ∀ c : Cone (((W ⋙ BigAffineFppf.inclusion B S hS) ⋙
          BigFppfOver.forget B S hS) ⋙ B.inclusion),
        IsLimit c → B.Contains c.pt)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAff : ∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (i : Jᵒᵖ) {X Y : Over (D.obj i)} (f : X ⟶ Y)
    (hBqc : IsQuasiCompactSpace B S hS (D.obj i))
    (hBqs : IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (hX : IsAlgebraicSpace B S hS X.left) (hY : IsAlgebraicSpace B S hS Y.left)
    (hXqc : IsQuasiCompactSpace B S hS X.left) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.left)
    (hYqc : IsQuasiCompactSpace B S hS Y.left) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.left)
    (proper : IsProper B S hS ((Over.pullback (limit.π D i)).map f).left)
    (ft : IsLocallyOfFiniteType B S hS f.left) :
    ∃ (j : Jᵒᵖ) (e : j ⟶ i), IsProper B S hS ((Over.pullback (D.map e)).map f).left :=
  exists_isProper_overPullback_map_of_chartLimitsInSite B S hS hZ
    (fun D hconv hf hf₀ => D.exists_isProper_mapAt_of_siteContainsBaseChangeLimits hconv hf hf₀)
    D hconv hD hAff i f hBqc hBqs hX hY hXqc hXqs hYqc hYqs proper ft

end AlgebraicGeometry.Space

end
