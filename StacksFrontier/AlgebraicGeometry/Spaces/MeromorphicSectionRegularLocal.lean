module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSections

/-!
# Regularity of a meromorphic section is local on the small étale site

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `s` be a
meromorphic section of a sheaf of `𝒪_F`-modules `L` (Stacks 0EN5).  Stacks 0ENB calls `s`
*regular* when multiplication by it, `r ↦ r • s|_V`, is injective on the meromorphic functions
over every étale scheme chart `V` of `F`.  That condition is **local**: it is enough to have it
on a covering family of each chart.

The reason is that `𝒦_F` is a sheaf: if two meromorphic functions over a chart are multiplied by
`s` to the same meromorphic section, they agree on each member of a covering family, hence agree.
Restriction of `r • s|_V` is `(r|_W) • s|_W`, because restriction in a presheaf of modules is
semilinear (`CategoryTheory.PresheafOfModules.map_smul`) and `s` is a *global* section, so its
value over `W` is the restriction of its value over `V`.

The consequence this is for is the one relevant to Stacks 0ENC, part (2): for a morphism
`f : X ⟶ Y` of algebraic spaces, the regularity of a meromorphic section on `X` need only be
checked on the charts of `X` that sit in a commuting square of étale charts over `f`, and indeed
only on the squares whose two charts are affine — those squares' source charts cover every chart
of `X`, by `AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`.

## Main results

* `AlgebraicGeometry.Space.meromorphicSectionSheaf_map_smul_eval`: restricting `x • s|_V` to a
  chart over `V` gives `x|_Z • s|_Z`.
* `AlgebraicGeometry.Space.isRegularMeromorphicSection_of_sieve` and
  `AlgebraicGeometry.Space.isRegularMeromorphicSection_of_cover`: **regularity is local** —
  a meromorphic section whose multiplication map is injective over a covering sieve, or over a
  covering family, of every chart is regular.
* `AlgebraicGeometry.Space.isRegularMeromorphicSection_of_chartDiagram`: **regularity over `X`
  need only be checked on affine chart diagrams over a morphism `f : X ⟶ Y`.**

## Implementation notes

Separatedness of the sheaf `𝒦_F` of meromorphic functions on the underlying sets of its sections
is `CategoryTheory.Presheaf.IsSheaf.isSeparated`, which needs the sheaf condition to be stable
under the forgetful functor of `CommRingCat`; that instance is available on this site and no
reformulation of the sheaf condition is needed.

A member of the covering sieve `CategoryTheory.Sieve.ofArrows` is a morphism factoring through
one of the given arrows, so the separatedness hypothesis is checked by restricting the equality
obtained at that arrow one step further.

*Why both the sieve form and the family form are kept.*  Neither subsumes the other.  The family
form asks for injectivity only over the members of the family and pays for the rest with that
factorization, so its hypothesis is the weaker of the two; and it cannot be obtained from the
sieve form by taking the family of all arrows of the sieve, because its index type is pinned to
`Type u` while the étale scheme charts live in `Type (u + 1)`.  That is a universe obstruction,
not a matter of convenience.

## References

* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Restriction of a multiple of a meromorphic section.**  Restricting `x • s|_V` to a chart
`Z` over `V` gives `x|_Z • s|_Z`: restriction in a presheaf of modules is semilinear, and `s`
being a *global* section its value over `Z` is the restriction of its value over `V`. -/
theorem meromorphicSectionSheaf_map_smul_eval
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    {Z V : SmallEtale B S hS F} (g : Z ⟶ V)
    (x : (Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS F hF).O).obj.obj (op V)) :
    (meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map g.op (x • s.eval (op V)) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS F hF).O).obj.map g.op x) • s.eval (op Z) := by
  rw [(meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map_smul g.op x (s.eval (op V)),
    PresheafOfModules.sections_property]
  rfl

/-- Regularity holds if each chart has a covering sieve whose members factor through a chart over
which multiplication by `s` is injective. -/
private theorem isRegularMeromorphicSection_of_factor
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    (h : ∀ V : SmallEtale B S hS F, ∃ T : Sieve V,
      T ∈ SmallEtale.topology B S hS F V ∧
      ∀ ⦃Z : SmallEtale B S hS F⦄ (g : Z ⟶ V), T g → ∃ (W : SmallEtale B S hS F) (p : Z ⟶ W)
        (a : W ⟶ V), g = p ≫ a ∧ Function.Injective fun r :
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS F hF).O).obj.obj (op W) ↦
        r • s.eval (op W)) :
    IsRegularMeromorphicSection.{u, u} B S hS F hF L s := by
  intro V r r' hr
  obtain ⟨T, hT, hinj⟩ := h V
  refine (Stacks.SheafOfModules.Tensor.ringSheaf
    (meromorphicRingedSite B S hS F hF).O).property.isSeparated V T hT r r' ?_
  intro Z g hg
  obtain ⟨W, p, a, rfl, hinj⟩ := hinj g hg
  have hi := hinj ((meromorphicSectionSheaf_map_smul_eval B S hS F hF L s a r).symm.trans
    ((congrArg ((meromorphicSectionSheaf.{u, u} B S hS F hF L).val.map a.op) hr).trans
      (meromorphicSectionSheaf_map_smul_eval B S hS F hF L s a r')))
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hi]

/-- **Regularity of a meromorphic section is local on the small étale site, for a covering
sieve.**  Let `s` be a meromorphic section of a sheaf of `𝒪_F`-modules `L`.  If every étale
scheme chart `V` of `F` carries a covering *sieve* over every member of which multiplication by
`s` is injective on meromorphic functions, then `s` is a regular meromorphic section in the sense
of Stacks 0ENB.

This is the shape a condition cut out by a local property takes: the charts over which a
meromorphic function is a fraction, or over which an invertible module is free, form a sieve and
not a family, and `AlgebraicGeometry.Space.imageSieve_toSheafify_localizationPresheaf_mem`
delivers the first of those as a sieve directly.

Two meromorphic functions over `V` multiplied by `s` to the same meromorphic section restrict,
over each member of the sieve, to meromorphic functions multiplied by `s` to the same section
(`AlgebraicGeometry.Space.meromorphicSectionSheaf_map_smul_eval`), so they agree there, and
`𝒦_F` being a sheaf they agree over `V`. -/
theorem isRegularMeromorphicSection_of_sieve
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    (h : ∀ V : SmallEtale B S hS F, ∃ T : Sieve V,
      T ∈ SmallEtale.topology B S hS F V ∧
      ∀ ⦃W : SmallEtale B S hS F⦄ (k : W ⟶ V), T k → Function.Injective fun r :
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS F hF).O).obj.obj (op W) ↦
        r • s.eval (op W)) :
    IsRegularMeromorphicSection.{u, u} B S hS F hF L s := by
  refine isRegularMeromorphicSection_of_factor B S hS F hF L s fun V ↦ ?_
  obtain ⟨T, hT, hinj⟩ := h V
  exact ⟨T, hT, fun Z g hg ↦ ⟨Z, 𝟙 _, g, (Category.id_comp g).symm, hinj g hg⟩⟩

/-- **Regularity of a meromorphic section is local on the small étale site.**  Let `s` be a
meromorphic section of a sheaf of `𝒪_F`-modules `L`.  If every étale scheme chart `V` of `F`
carries a covering family over whose members multiplication by `s` is injective on meromorphic
functions, then `s` is a regular meromorphic section in the sense of Stacks 0ENB.

Unlike `AlgebraicGeometry.Space.isRegularMeromorphicSection_of_sieve` this asks for injectivity
only over the members of the family, not over every chart mapping into one of them; the
difference is paid for by the factorization of a member of the generated sieve. -/
theorem isRegularMeromorphicSection_of_cover
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (L : Modules.{u, u} B S hS F hF) (s : MeromorphicSection.{u, u} B S hS F hF L)
    (h : ∀ V : SmallEtale B S hS F, ∃ (I : Type u) (W : I → SmallEtale B S hS F)
        (a : ∀ i, W i ⟶ V),
      Sieve.ofArrows W a ∈ SmallEtale.topology B S hS F V ∧
      ∀ i, Function.Injective fun r :
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS F hF).O).obj.obj (op (W i)) ↦
        r • s.eval (op (W i))) :
    IsRegularMeromorphicSection.{u, u} B S hS F hF L s := by
  refine isRegularMeromorphicSection_of_factor B S hS F hF L s fun V ↦ ?_
  obtain ⟨I, W, a, hcov, hinj⟩ := h V
  refine ⟨_, hcov, ?_⟩
  rintro Z g ⟨Z', p, q, ⟨i⟩, rfl⟩
  exact ⟨W i, p, a i, rfl, hinj i⟩

/-- **Regularity of a meromorphic section on `X` need only be checked on affine chart diagrams
over a morphism `f : X ⟶ Y`.**  Let `N` be a sheaf of `𝒪_X`-modules and `s` a meromorphic
section of it.  If multiplication by `s` is injective on the meromorphic functions over the chart
of `X` of every commuting square of étale scheme charts over `f` whose two charts are affine,
then `s` is a regular meromorphic section.

The source charts of those squares cover every étale chart of `X`
(`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`), and regularity is local
(`AlgebraicGeometry.Space.isRegularMeromorphicSection_of_cover`).

This is the reduction Stacks 0ENC, part (2) is proved through: the pullback of a meromorphic
section is computed on a chart diagram, by
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_chartDiagram`, and nowhere else. -/
theorem isRegularMeromorphicSection_of_chartDiagram
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (N : Modules.{u, u} B S hS X.1 X.2)
    (s : MeromorphicSection.{u, u} B S hS X.1 X.2 N)
    (h : ∀ d : ChartDiagram B S hS X.1 Y.1 f.hom,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
      Function.Injective fun r :
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS X.1 X.2).O).obj.obj (op d.U) ↦
        r • s.eval (op d.U)) :
    IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 N s := by
  refine isRegularMeromorphicSection_of_cover B S hS X.1 X.2 N s fun V ↦ ?_
  obtain ⟨I, W, a, d, hdU, hUaff, hVaff, hcov⟩ := exists_affine_chartDiagram_ofArrows B S hS f V
  refine ⟨I, W, a, hcov, fun i ↦ ?_⟩
  rw [← hdU i]
  exact h (d i) (by rw [hdU i]; exact hUaff i) (hVaff i)

end AlgebraicGeometry.Space

end
