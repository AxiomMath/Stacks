module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit
public import StacksFrontier.RingTheory.ColimitPresentation.FinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine schemes of finite presentation over a limit of affine schemes have a model

Let `S = lim Sᵢ` be a cofiltered limit of affine schemes with affine transition morphisms, and let
`X` be an affine scheme locally of finite presentation over `S`.  Then `X` is the base change of
an affine scheme locally of finite presentation over one of the stages `Sᵢ`.

This is the affine case of the essential-surjectivity half of Stacks Tag 0EY1, and equally the
affine case of Stacks Tag 01ZM part (1).  The source says of exactly this step: "In case each of
the schemes `S_i` is affine, and we consider only affine schemes of finite presentation over
`S_i`, resp. `S`, this lemma is equivalent to Algebra, Lemma 05N9."  That is how it is proved
here: Tag 05N9 part (1) is already in this library, so the geometric statement is obtained from
it by applying `Spec`.

## Main results

* `AlgebraicGeometry.exists_isPullback_of_isAffine_of_isLimit`: the statement for an index
  category at the universe of the schemes.
* `AlgebraicGeometry.exists_isPullback_of_isAffine_of_isLimit_of_initiallySmall`: the same with
  the index universes independent of the scheme universe.
* `AlgebraicGeometry.LimitDescent.exists_model_of_locallyOfFinitePresentation_of_isAffine`: the
  essential-surjectivity statement of Stacks Tag 0EY1 verbatim, restricted to the case of affine
  stages and an affine `X`.

## Implementation notes

The three ingredients are Mathlib's `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`, which
says that global sections take the limit cone to a colimit cocone of rings; Tag 05N9 part (1),
which descends a finitely presented algebra over a filtered colimit of rings to a stage, in the
form of a pushout square of rings; and `AlgebraicGeometry.isPullback_SpecMap_of_isPushout`, which
turns that square into a pullback square of affine schemes.  The limit itself is affine because
`AlgebraicGeometry.isAffineHom_π_app` makes the projection to any stage an affine morphism.

The general case of the essential surjectivity of Tag 0EY1 is not proved here, and the tag is
therefore not attached in this file.  It is proved in
`StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing`, as
`AlgebraicGeometry.LimitDescent.exists_isPullback_of_finitePresentation`: `X` is covered by
finitely many affine opens each mapping into an affine open of a stage, the affine case above is
applied to each by
`StacksDraft.AlgebraicGeometry.F3b.LimitDescent.Pieces`, and the pieces are then glued two at a
time.

### On the smallness of the index

Both results are stated for a general index category, the second at index universes independent
of the scheme universe, but the second pays for that with `CategoryTheory.LocallySmall.{u}` and
`CategoryTheory.InitiallySmall.{u}` on the index — the hypotheses under which
`StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit` frees Mathlib's limit
theory.  This is not an artefact of the route: already the affine case needs `Γ(lim Sᵢ)` to *be*
the colimit of the `Γ(Sᵢ)` in `CommRingCat.{u}`, and needs that colimit to be computed on
underlying sets, and both of those are statements about an index category at the scheme universe.
So the smallness that the fullness and faithfulness halves of Tag 0EY1 need is needed by the
essential-surjectivity half as well, and for a different reason: there it enters through the
reindexing of a diagram of base changes, here through the comparison of sections of the limit
with sections at the stages.

For the index of Tag 0EY1 — the opposite of a directed preorder `I` — the weakest hypothesis in
Mathlib's vocabulary that discharges both is `CategoryTheory.FinallySmall.{u} I`, that is, `I` has
a `u`-small cofinal set of objects: `CategoryTheory.LocallySmall.{u} Iᵒᵖ` is automatic, `Iᵒᵖ`
being thin, and `CategoryTheory.InitiallySmall.{u} Iᵒᵖ` is then an instance.  It is strictly
weaker than `Small.{u} I`, and is what the last result below assumes.

## References

* [Stacks Project, Tag 0EY1](https://stacks.math.columbia.edu/tag/0EY1)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 05N9](https://stacks.math.columbia.edu/tag/05N9)
-/

@[expose] public section

universe v uI u

open CategoryTheory CategoryTheory.Limits CategoryTheory.InitiallySmall

namespace AlgebraicGeometry

/-- An affine scheme locally of finite presentation over a cofiltered limit of affine schemes with
affine transition morphisms is the base change of an affine scheme locally of finite presentation
over one of the stages.

This is the affine case of Stacks Tag 01ZM part (1), and of the essential-surjectivity half of
Stacks Tag 0EY1. The index category is at the universe of the schemes; see
`AlgebraicGeometry.exists_isPullback_of_isAffine_of_isLimit_of_initiallySmall` for the version
with the index universes free. -/
public theorem exists_isPullback_of_isAffine_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] :
    ∃ (i : I) (Xᵢ : Scheme.{u}) (fᵢ : Xᵢ ⟶ D.obj i) (g : X ⟶ Xᵢ),
      IsAffine Xᵢ ∧ LocallyOfFinitePresentation fᵢ ∧ IsPullback g f fᵢ (c.π.app i) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffine c.pt :=
    have := isAffineHom_π_app D c hc i₀
    isAffine_of_isAffineHom (c.π.app i₀)
  obtain ⟨hcol⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  obtain ⟨j, A, φ, a, hφ, hpo⟩ :=
    (CommRingCat.exists_isPushout_and_exists_eq_comp_and_exists_comp_eq_of_isColimit hcol).1
      (Scheme.Γ.obj (.op X)) (Scheme.Γ.map f.op) (Scheme.Hom.finitePresentation_appTop f)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  refine ⟨j.unop, Spec A, Spec.map φ ≫ (D.obj j.unop).isoSpec.inv, X.isoSpec.hom ≫ Spec.map a,
    inferInstance, ?_, ?_⟩
  · have h₁ : LocallyOfFinitePresentation (Spec.map φ) :=
      (LocallyOfFinitePresentation.SpecMap_iff φ).2 hφ
    have h₂ : LocallyOfFinitePresentation (D.obj j.unop).isoSpec.inv := inferInstance
    exact MorphismProperty.comp_mem _ _ _ h₁ h₂
  · have : IsAffine (((Functor.const I).obj c.pt).obj j.unop) := ‹IsAffine c.pt›
    refine hpb.of_iso' X.isoSpec (Iso.refl _) c.pt.isoSpec (D.obj j.unop).isoSpec ?_ ?_ ?_ ?_
    · simp
    · exact Scheme.isoSpec_hom_naturality f
    · simp
    · exact Scheme.isoSpec_hom_naturality (c.π.app j.unop)

/-- `AlgebraicGeometry.exists_isPullback_of_isAffine_of_isLimit` with the index universes
independent of the scheme universe, at the cost of `CategoryTheory.LocallySmall.{u}` and
`CategoryTheory.InitiallySmall.{u}` on the index category. -/
@[ega "IV 8.8.3" "essential surjectivity"]
public theorem exists_isPullback_of_isAffine_of_isLimit_of_initiallySmall
    {I : Type uI} [Category.{v} I] [IsCofiltered I] [LocallySmall.{u} I] [InitiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, IsAffine (D.obj i)]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ c.pt) [LocallyOfFinitePresentation f] :
    ∃ (i : I) (Xᵢ : Scheme.{u}) (fᵢ : Xᵢ ⟶ D.obj i) (g : X ⟶ Xᵢ),
      IsAffine Xᵢ ∧ LocallyOfFinitePresentation fᵢ ∧ IsPullback g f fᵢ (c.π.app i) := by
  have h₁ : ∀ {a b : CofilteredInitialModel.{u} I} (g : a ⟶ b),
      IsAffineHom ((fromCofilteredInitialModel.{u} I ⋙ D).map g) := by
    intros; dsimp; infer_instance
  have h₂ : ∀ a, IsAffine ((fromCofilteredInitialModel.{u} I ⋙ D).obj a) := by
    intro a; dsimp; infer_instance
  obtain ⟨a, Xᵢ, fᵢ, g, h⟩ := exists_isPullback_of_isAffine_of_isLimit
    (fromCofilteredInitialModel.{u} I ⋙ D) _
    ((Functor.Initial.isLimitWhiskerEquiv (fromCofilteredInitialModel.{u} I) c).symm hc) f
  exact ⟨_, Xᵢ, fᵢ, g, h⟩

namespace LimitDescent

/-- **Essential surjectivity in Stacks Tag 0EY1**, in the case of affine stages and an affine `X`.

Let `S = lim Sᵢ` be a directed inverse limit of affine schemes with affine transition morphisms,
and let `X` be an affine scheme locally of finite presentation over `S`. Then `X` is isomorphic,
over `S`, to the base change of a quasi-compact, quasi-separated scheme locally of finite
presentation over one of the stages `Sᵢ`.

This is the Stacks statement verbatim apart from the two added hypotheses `IsAffine (D.obj i)`
and `IsAffine X.left`, and the index hypothesis `CategoryTheory.FinallySmall.{u} I`, which asks
that `I` have a `u`-small cofinal set of objects; see the module docstring. The quasi-compactness
and quasi-separatedness hypotheses on `X` are those of the source, and are carried unused, being implied by
affineness. -/
@[ega "IV 8.1.1" "special case",
  ega "IV 8.8.2" "special case",
  ega "IV 8.8.3" "special case",
  sga "3 VIB 10.0" "(ii), special case",
  sga "4 VII 5.2" "b, special case"]
public theorem exists_model_of_locallyOfFinitePresentation_of_isAffine
    {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] [FinallySmall.{u} I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (X : Over c.pt) [IsAffine X.left]
    (hXqc : CompactSpace X.left) (hXqs : QuasiSeparatedSpace X.left)
    (hX : LocallyOfFinitePresentation X.hom) :
    ∃ (i : I) (Xᵢ : Over (D.obj (.op i))),
      CompactSpace Xᵢ.left ∧ QuasiSeparatedSpace Xᵢ.left ∧
        LocallyOfFinitePresentation Xᵢ.hom ∧
        Nonempty (X ≅ (Over.pullback (c.π.app (.op i))).obj Xᵢ) := by
  -- The two quasi-compactness hypotheses follow from affineness; they are the source's.
  have := hXqc
  have := hXqs
  have : LocallyOfFinitePresentation X.hom := hX
  obtain ⟨i, Xᵢ, fᵢ, g, hXᵢ, hfᵢ, hpb⟩ :=
    exists_isPullback_of_isAffine_of_isLimit_of_initiallySmall D c hc X.hom
  have : IsAffine Xᵢ := hXᵢ
  refine ⟨i.unop, Over.mk fᵢ, inferInstanceAs (CompactSpace Xᵢ),
    inferInstanceAs (QuasiSeparatedSpace Xᵢ), hfᵢ, ⟨Over.isoMk hpb.isoPullback ?_⟩⟩
  simp

end LimitDescent

end AlgebraicGeometry
