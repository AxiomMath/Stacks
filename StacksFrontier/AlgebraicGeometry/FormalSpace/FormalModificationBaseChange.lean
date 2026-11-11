module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveBaseChange

/-!
# Formal modifications are stable under adic base change

Let `S` be a scheme contained in a big fppf site `B`, let `f : X ⟶ Y` be a formal modification
of locally Noetherian formal algebraic spaces over `S` (**Stacks 0GDK**) and let `g : Z ⟶ Y` be
an adic morphism (**Stacks 0AQ3**) with `Z` locally Noetherian. **Stacks 0GDN** says that the
base change `X ×_Y Z ⟶ Z` is again a formal modification. The library's statement of Stacks 0GDN
is `AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChangeAdic`, whose hypotheses
are those of the source; this module supplies the categorical lemmas it uses.

`AlgebraicGeometry.FormalSpace.IsFormalModification` is a structure with six fields, and the
proof of the earlier form `AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd`
kept below is field by field, as in the source:

* `isLocallyNoetherian_source`, that `X ×_Y Z` is locally Noetherian, is **Stacks 0AQ8**;
* `isLocallyNoetherian_target`, that `Z` is locally Noetherian, is the hypothesis `hZ`;
* `isProper` is **Stacks 0GBT**, `AlgebraicGeometry.FormalSpace.IsProper.of_isPullback`;
* `isRigEtale` is **Stacks 0GD1**,
  `AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isAdicMorphism`;
* `isRigSurjective` is **Stacks 0AQS**,
  `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback`;
* `isRigSurjective_diagonal` is **Stacks 0AQS** again, applied to the cartesian square which
  exhibits the relative diagonal of the base change as a base change of the relative diagonal
  of `f`. The source phrases this as "`Δ_{f'}` is the base change of `Δ_f` by the adic
  morphism `X' ×_{Y'} X' ⟶ X ×_Y X`".

## Main definitions

* `AlgebraicGeometry.FormalSpace.FibreProductIsLocallyNoetherian`: **Stacks 0AQ8** stated for
  every cartesian square at once, which is how it is carried below.

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_selfPullbackMap`: in any category with fibre
  products, the comparison `W ×_Z W ⟶ X ×_Y X` attached to a cartesian square with legs
  `p : W ⟶ Z`, `q : W ⟶ X` over `g : Z ⟶ Y`, `f : X ⟶ Y` is a base change of `g`.
* `AlgebraicGeometry.FormalSpace.isPullback_diagonal_selfPullbackMap`: in the same situation
  the relative diagonal of `p` is a base change of the relative diagonal of `f` along that
  comparison. This is the categorical content of the last step of Stacks 0GDN.
* `AlgebraicGeometry.FormalSpace.IsProper.isLocallyOfFiniteType`: a proper morphism of formal
  algebraic spaces over `S` is locally of finite type.
* `AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd`: an earlier form of
  Stacks 0GDN with extra hypotheses, kept for its downstream users; Stacks 0GDN itself is
  `AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism`.

## Implementation notes

The two categorical lemmas are proved for an arbitrary category with fibre products. The
second is obtained from the first by pasting: the composite of the square
`Δ_p / q / m / Δ_f` with the square `m / (fst ≫ p) / g / (fst ≫ f)` is the original square
`p / q / g / f`, because `Δ_p ≫ pullback.fst p p = 𝟙`, so
`CategoryTheory.Limits.IsPullback.of_right` turns the outer and right squares into the left
one. The first lemma is the only genuinely new cartesian square here; it says
`W ×_Z W ≅ (X ×_Y X) ×_Y Z`, with `m` the projection, and it is also what makes `m` locally of
finite type (Stacks 0AQ5) as soon as `g` is, which Stacks 0AQS needs of the morphism one bases
along. The existing lemma `CategoryTheory.Limits.isPullback_diagonal_of_isPullback` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionSquaringMap` does not apply: it
describes a *kernel pair* of a morphism into the source of `f` as a base change of `Δ_f`, and
instantiating it here would demand that `pullback.fst f g` be a monomorphism.

The earlier form `AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd` carries five
further hypotheses, each stated for all of its own data rather than for the `f` and `g` of the
conclusion:

* `h0AQ8` is **Stacks 0AQ8** quantified over every cartesian square
  (`AlgebraicGeometry.FormalSpace.FibreProductIsLocallyNoetherian`). The library proves it:
  every instance is
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_of_isPullback_of_isLocallyOfFiniteType`.
* `hcond`, `hiso` and `h31` are the three inputs that
  `AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isAdicMorphism` carries for
  Stacks 0GD1: the locality of the cohomology-annihilation condition `Rig.RigEtaleCondition`,
  the invariance of rig-étaleness under isomorphism of targets, and the implication
  (3) ⟹ (1) of Stacks 0ANG. The first of these is false:
  `Rig.not_propertyIsLocalNoetherian_rigEtaleCondition` in
  `StacksFrontier.RingTheory.Rig.RigEtaleConditionCounterexample` refutes it, so no caller can
  supply `hcond` and this form has no instance.
* `hcover` is the geometric half of Stacks 0GBD — the covering of a fibre product by fibre
  products of charts — quantified over all pairs of morphisms.

Stacks 0GD1 itself is proved without these inputs, as
`AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isLocallyNoetherian`, and that is what
the statement of Stacks 0GDN uses.

The earlier form makes three hypotheses on the data beyond those the source displays, and
takes its adic morphism `g` in the chart-wise form
`AlgebraicGeometry.FormalSpace.IsAdicOnEveryAffineEtaleDiagramNoetherian`. `hgft`, that `g` is
locally of finite type, is a hypothesis of Stacks 0AQS, which the source invokes twice;
adicness in the sense of Stacks 0AQ3 is a condition on chart maps and does not imply it.
`hdiag`, that the relative diagonal of `f` is locally of finite type, is needed for the same
reason: Definition 0AQQ presupposes its morphism locally of finite type, and the predicate
`AlgebraicGeometry.FormalSpace.IsRigSurjective` of this library does not build that in, so the
field `isRigSurjective_diagonal` of a formal modification does not carry it. `hZ`, that `Z` is
locally Noetherian, is displayed by the source; it is a hypothesis here because the predicate
of Stacks 0GDK records local Noetherianity of the source and target in its own fields.

Local finite typeness of `f` is not assumed: it follows from properness, which is the first
field of a formal modification, by
`AlgebraicGeometry.FormalSpace.IsProper.isLocallyOfFiniteType`.

## References

* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
* [Stacks Project, Tag 0AQ8](https://stacks.math.columbia.edu/tag/0AQ8)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0GBT](https://stacks.math.columbia.edu/tag/0GBT)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### The diagonal of a base change, categorically -/

section Categorical

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- Let `p : W ⟶ Z` and `q : W ⟶ X` be the legs of a cartesian square over `g : Z ⟶ Y` and
`f : X ⟶ Y`. The comparison morphism `W ×_Z W ⟶ X ×_Y X` with components `q` on each factor is
a base change of `g`: the square it forms with the two projections to `Z` and to `Y` is
cartesian, which is the statement that `W ×_Z W` is `(X ×_Y X) ×_Y Z`. -/
theorem isPullback_selfPullbackMap {W X Y Z : C} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y}
    {f : X ⟶ Y} (sq : IsPullback p q g f) :
    IsPullback (pullback.map p p f f q q g sq.w sq.w) (pullback.fst p p ≫ p)
      (pullback.fst f f ≫ f) g := by
  have hw : pullback.map p p f f q q g sq.w sq.w ≫ (pullback.fst f f ≫ f) =
      (pullback.fst p p ≫ p) ≫ g := by
    rw [← Category.assoc, pullback.lift_fst, Category.assoc, Category.assoc, sq.w]
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw (fun s =>
    pullback.lift (sq.lift s.snd (s.fst ≫ pullback.fst f f)
        (by rw [Category.assoc, ← s.condition]))
      (sq.lift s.snd (s.fst ≫ pullback.snd f f)
        (by rw [Category.assoc, ← pullback.condition, ← s.condition]))
      (by rw [sq.lift_fst, sq.lift_fst])) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_))
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, sq.lift_snd]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, sq.lift_snd]
  · rw [← Category.assoc, pullback.lift_fst, sq.lift_fst]
  · have h₁f := congrArg (fun t => t ≫ pullback.fst f f) h₁
    have h₁s := congrArg (fun t => t ≫ pullback.snd f f) h₁
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at h₁f h₁s
    refine pullback.hom_ext (sq.hom_ext ?_ ?_) (sq.hom_ext ?_ ?_)
    · rw [Category.assoc, pullback.lift_fst, IsPullback.lift_fst]; exact h₂
    · rw [Category.assoc, pullback.lift_fst, IsPullback.lift_snd]; exact h₁f
    · rw [Category.assoc, pullback.lift_snd, IsPullback.lift_fst, ← pullback.condition]
      exact h₂
    · rw [Category.assoc, pullback.lift_snd, IsPullback.lift_snd]; exact h₁s

/-- In the situation of `AlgebraicGeometry.FormalSpace.isPullback_selfPullbackMap`, the
relative diagonal `Δ_p : W ⟶ W ×_Z W` is a base change of the relative diagonal
`Δ_f : X ⟶ X ×_Y X` along the comparison morphism `W ×_Z W ⟶ X ×_Y X`.

The square `Δ_p / q / m / Δ_f` pasted with the square of
`AlgebraicGeometry.FormalSpace.isPullback_selfPullbackMap` is the original cartesian square,
since `Δ_p ≫ pullback.fst p p = 𝟙` and likewise for `f`. -/
theorem isPullback_diagonal_selfPullbackMap {W X Y Z : C} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y}
    {f : X ⟶ Y} (sq : IsPullback p q g f) :
    IsPullback (pullback.diagonal p) q (pullback.map p p f f q q g sq.w sq.w)
      (pullback.diagonal f) := by
  have hp : pullback.diagonal p ≫ pullback.map p p f f q q g sq.w sq.w =
      q ≫ pullback.diagonal f := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.diagonal_fst,
        Category.id_comp, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.diagonal_snd,
        Category.id_comp, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  refine IsPullback.of_right ?_ hp (isPullback_selfPullbackMap sq).flip
  have e₁ : pullback.diagonal p ≫ (pullback.fst p p ≫ p) = p := by
    rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
  have e₂ : pullback.diagonal f ≫ (pullback.fst f f ≫ f) = f := by
    rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
  rw [e₁, e₂]
  exact sq

end Categorical

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Properness and local finite typeness -/

/-- A proper morphism of formal algebraic spaces over `S` is locally of finite type:
properness of a morphism of algebraic spaces includes being of finite type, hence locally of
finite type, so the same representability witness serves. -/
theorem IsProper.isLocallyOfFiniteType {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (h : IsProper B S hS f) : IsLocallyOfFiniteType B S hS f := by
  obtain ⟨hrep, hprop⟩ := h
  exact ⟨hrep, fun U ξ => (hprop U ξ).2.1.1⟩

/-! ### Stacks 0AQ8 for every cartesian square -/

/-- Stacks 0AQ8 for every cartesian square at once: whenever `p : W ⟶ Z` and `q : W ⟶ X`
are the legs of a cartesian square over `g : Z ⟶ Y` and `f : X ⟶ Y`, with `Z` locally
Noetherian and `f` locally of finite type, the fibre product `W` is locally Noetherian.

`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_of_isPullback_of_isLocallyOfFiniteType`
proves each instance of this (Stacks 0AQ8); the earlier statements that take it as a hypothesis
keep this form so that the hypothesis is quantified over its own data. -/
abbrev FibreProductIsLocallyNoetherian : Prop :=
  ∀ {W X Y Z : FppfSheaf B S hS} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y},
    IsPullback p q g f → IsLocallyNoetherian B S hS Z →
      IsLocallyOfFiniteType B S hS f → IsLocallyNoetherian B S hS W

/-! ### An earlier form of Stacks 0GDN -/

/-- An earlier form of Stacks 0GDN with extra hypotheses. Let `f : X ⟶ Y` be a formal
modification of locally Noetherian formal algebraic spaces over `S`, let `g : Z ⟶ Y` be
locally of finite type and adic on every affine étale diagram, `Z` locally Noetherian, and let
the relative diagonal of `f` be locally of finite type. Given the hypotheses `hcond`, `hiso`,
`h31`, `hcover` and `h0AQ8` described in the module docstring, the base change `X ×_Y Z ⟶ Z`
of `f` along `g` is a formal modification.

The hypothesis `hcond` is refuted by `Rig.not_propertyIsLocalNoetherian_rigEtaleCondition`, so
this form has no instance. Stacks 0GDN, with the hypotheses of the source, is
`AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism`. -/
theorem isFormalModification_pullback_snd
    (hcond : TopologicalRing.PropertyIsLocalNoetherian.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        Rig.RigEtaleCondition φ))
    (hiso : PropertyIsInvariantUnderTargetIso.{u}
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
    (h31 : SourceCoverImpliesEveryAffineEtaleDiagram B S hS
      (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
      (fun {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
        [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] (φ : R₁ →+* R₂) ↦
        RingHom.IsRigEtaleArrow φ))
    (hcover : ∀ {X₀ Y₀ Z₀ : FppfSheaf B S hS} (f₀ : X₀ ⟶ Y₀) (g₀ : Z₀ ⟶ Y₀),
      HasBaseChangeCoverOverPullbackSnd B S hS f₀ g₀)
    (h0AQ8 : FibreProductIsLocallyNoetherian B S hS)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hg : IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS g)
    (hgft : IsLocallyOfFiniteType B S hS g)
    (hdiag : IsLocallyOfFiniteType B S hS (pullback.diagonal f))
    (hf : IsFormalModification B S hS f) :
    IsFormalModification B S hS (pullback.snd f g) := by
  have sq : IsPullback (pullback.snd f g) (pullback.fst f g) g f :=
    (IsPullback.of_hasPullback f g).flip
  have hfft : IsLocallyOfFiniteType B S hS f :=
    IsProper.isLocallyOfFiniteType B S hS hf.isProper
  have hmft : IsLocallyOfFiniteType B S hS
      (pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
        (pullback.fst f g) g sq.w sq.w) :=
    IsLocallyOfFiniteType.of_isPullback B S hS (isPullback_selfPullbackMap sq) hgft
  exact
    { isLocallyNoetherian_source := h0AQ8 sq hZ hfft
      isLocallyNoetherian_target := hZ
      isProper := IsProper.of_isPullback B S hS sq hf.isProper
      isRigEtale := isRigEtale_pullback_snd_of_isAdicMorphism B S hS hcond hiso h31 f g
        (hcover f g) hf.isLocallyNoetherian_source hf.isLocallyNoetherian_target hZ
        hf.isRigEtale hg
      isRigSurjective :=
        (IsRigSurjective.of_isPullback B S hS sq hfft hgft hf.isRigSurjective).2
      isRigSurjective_diagonal :=
        (IsRigSurjective.of_isPullback B S hS (isPullback_diagonal_selfPullbackMap sq) hdiag
          hmft hf.isRigSurjective_diagonal).2 }

end AlgebraicGeometry.FormalSpace

end
