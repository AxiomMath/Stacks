module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PrescribedCoverFiniteSubfamily
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteRepresentableOverAffineFormal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Surjective

/-!
# Refining a covering of the source against an affine étale diagram

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of fppf
sheaves on the big fppf site of `S`. Condition (3) of **Stacks 0ANG** hands us a covering
`{Uᵢ ⟶ X}` as in Definition **Stacks 0AIM** together with factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` through
affine formal algebraic spaces representable étale over `Y`; condition (1) hands us a
commutative square `U₀ ⟶ V₀` over `f` with `U₀`, `V₀` affine formal algebraic spaces and
`U₀ ⟶ X`, `V₀ ⟶ Y` representable étale. The proof of the implication (3) ⟹ (1) begins by
*refining the covering against the square*: it forms coverings of the fibre products

* `Vᵢ ×_Y V₀`, with members `Vᵢⱼ`, and
* `Vᵢⱼ ×_{Vᵢ} Uᵢ ×_X U₀`, with members `Uᵢⱼₖ`,

and assembles the family `{Uᵢⱼₖ ⟶ U₀}`, each of whose members also maps to `Uᵢ` and sits in a
square over `Uᵢ ⟶ Vᵢ` and in a square over `U₀ ⟶ V₀`. That family has to be a covering of `U₀`
as in Definition 0AIM, which is what makes the rest of the proof of Stacks 0ANG run.

This file carries out that construction and proves the resulting family jointly surjective.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affineEtaleRefinement_of_sourceCover`: the refinement,
  as a covering of `U₀` as in Definition 0AIM whose members carry both squares.
* `AlgebraicGeometry.FormalSpace.exists_finite_affineEtaleRefinement_of_sourceCover`: the same
  with the index type finite, by the finiteness step
  `FormalSpace.exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace`.

## The second fibre product is taken over `Vᵢ ×_Y V₀`, not over `Vᵢ`

The source writes the second fibre product as `Vᵢⱼ ×_{Vᵢ} Uᵢ ×_X U₀`, over `Vᵢ`. Over `Vᵢ`
there is no reason for the square

```
  Uᵢⱼₖ ⟶ Vᵢⱼ
    ↓       ↓
   U₀  ⟶  V₀
```

to commute: its two edges into `V₀` agree only after composition with `V₀ ⟶ Y`, and `V₀ ⟶ Y` is
not a monomorphism. The fibre product taken over `Vᵢ ×_Y V₀` instead — along the comparison map
`Uᵢ ×_X U₀ ⟶ Vᵢ ×_Y V₀` which the commutativity of the two given squares induces — makes both
squares commute by one application of its own cartesian square, and is the subobject of
`Vᵢⱼ ×_{Vᵢ} Uᵢ ×_X U₀` cut out by exactly that commutativity. Joint surjectivity survives the
passage to the subobject: the point of `Uᵢ ×_X U₀` assembled from a point of `U₀` and its lift
to `Uᵢ` is pushed to `Vᵢ ×_Y V₀` *before* a lift to `Vᵢⱼ` is chosen, so the lift is compatible
with it over `Vᵢ ×_Y V₀` and not merely over `Vᵢ`.

## What is assumed

Nothing. The three inputs this step needs are all available:

* both fibre products are formal algebraic spaces, with no hypothesis on the bases `X` and `Y`,
  by `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isEtale_of_isAffineFormal`
  and `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`
  — the legs are representable étale morphisms out of affine formal algebraic spaces, hence
  representable by objects of the site by **Stacks 0AIG**, so **Stacks 0AJ2** at an arbitrary
  base is not needed;
* joint surjectivity is checked on points, by
  `AlgebraicGeometry.FormalSpace.isLocallySurjective_sigmaDesc_of_jointly_surjective_points`
  and `AlgebraicGeometry.FormalSpace.exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc`,
  with compatible points assembled through a cartesian square by
  `AlgebraicGeometry.Space.exists_point_of_isPullbackULift`. So nothing here depends on
  `AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`, which this library does not
  prove;
* the finiteness step is
  `FormalSpace.exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace`,
  which cuts a covering handed in as an argument down to a finite reindexing of *itself*, so
  the members of the finite refinement keep their maps into the covering being refined.

## No tag

What is proved here is a step inside the proof of **Stacks 0ANG**, not one of its numbered
conditions nor any other statement the Stacks project registers, so no `@[stacks]` attribute is
attached. It is also not all of
`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'`: that predicate asks the
refinement to be delivered *presented*, each member carrying
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleLocalizationOfChartMap` and the covering carrying
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleFiniteCoverOfChartMap`. Those identifications are
the essential-surjectivity clause of **Stacks 0AN8** applied to the charts built here. The first
of them is supplied by
`FormalSpace.exists_finite_affineEtaleRefinement_completedEtaleLocalization_of_sourceCover`,
which adds it to the refinement built here when the members of the covering being refined are
countably indexed; the second this library does not carry. See the module documentation of
`StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty`.

## References

* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ2](https://stacks.math.columbia.edu/tag/0AJ2)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The refinement of a covering of the source against an affine étale diagram, as
constructed in the proof of Stacks 0ANG.** Let `f : X ⟶ Y` be a morphism of fppf sheaves on the
big fppf site of `S`, let `{Uᵢ ⟶ X}` be a covering as in Definition **Stacks 0AIM** with
factorizations `Uᵢ ⟶ Vᵢ ⟶ Y` through affine formal algebraic spaces representable étale over
`Y`, and let `U₀ ⟶ V₀` be a commutative square over `f` with `U₀`, `V₀` affine formal algebraic
spaces and `U₀ ⟶ X`, `V₀ ⟶ Y` representable étale. Then there is a covering `{Wₛ ⟶ U₀}` of `U₀`
as in Definition 0AIM, each member of which maps to a member `U (k s)` of the given covering by
a representable étale morphism and sits in a commutative square

```
  Wₛ ⟶ Zₛ        Wₛ ⟶ Zₛ
   ↓      ↓   and   ↓     ↓
 U (k s) ⟶ V (k s)  U₀ ⟶ V₀
```

with `Zₛ` an affine formal algebraic space representable étale over both `V (k s)` and `V₀`.

The members are the charts of the fibre products `Vᵢⱼ ×_{Vᵢ ×_Y V₀} (Uᵢ ×_X U₀)`, where
`{Vᵢⱼ ⟶ Vᵢ ×_Y V₀}` is a chart cover of the first fibre product of the proof of Stacks 0ANG and
the base change is along the comparison map `Uᵢ ×_X U₀ ⟶ Vᵢ ×_Y V₀` induced by the two given
squares. Taking the second fibre product over `Vᵢ ×_Y V₀` rather than over `Vᵢ` is what makes
the square over `U₀ ⟶ V₀` commute; see the module documentation.

NO TAG IS ATTACHED: this is a step inside the proof of Stacks 0ANG rather than a statement that
the Stacks project registers. It is also not
`AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'`, which asks the refinement to be
delivered presented by completed étale ring maps. -/
theorem exists_affineEtaleRefinement_of_sourceCover
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
    (t : ∀ i, U i ⟶ V i) (hUcover : IsAffineEtaleCover B S hS U u)
    (hVaffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (V i))
    (hVetale : ∀ i, IsRepresentableEtale B S hS (v i))
    (hVsquare : ∀ i, u i ≫ f = t i ≫ v i)
    {U₀ V₀ : FppfSheaf B S hS} (a : U₀ ⟶ X) (b : V₀ ⟶ Y) (τ : U₀ ⟶ V₀)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀)
    (hV₀ : IsAffineFormalAlgebraicSpace B S hS V₀)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hsquare : a ≫ f = τ ≫ b) :
    ∃ (σ : Type (u + 1)) (k : σ → I) (W Z : σ → FppfSheaf B S hS)
      (p : ∀ s, W s ⟶ U₀) (q : ∀ s, W s ⟶ U (k s)) (m : ∀ s, W s ⟶ Z s)
      (r : ∀ s, Z s ⟶ V (k s)) (c : ∀ s, Z s ⟶ V₀),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) ∧
        (∀ s, IsRepresentableEtale B S hS (q s)) ∧
        (∀ s, IsRepresentableEtale B S hS (r s)) ∧
        (∀ s, IsRepresentableEtale B S hS (c s)) ∧
        (∀ s, q s ≫ t (k s) = m s ≫ r s) ∧ (∀ s, p s ≫ τ = m s ≫ c s) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hUaffine, hUetale, hUsurjective⟩ := hUcover
  -- the first fibre product of the proof of Stacks 0ANG, and a chart cover of it
  have hVfib : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (v i) b) := fun i ↦
    isFormalAlgebraicSpace_pullback_of_isEtale_of_isAffineFormal B S hS (v i) b
      (hVaffine i) (hVetale i).1 (hVetale i).2 hV₀
  choose J Zc e hZaffine hZetale hZsurjective using fun i ↦ (hVfib i).2
  -- the fibre product `Uᵢ ×_X U₀`
  have hUfib : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (u i) a) := fun i ↦
    isFormalAlgebraicSpace_pullback_of_isEtale_of_isAffineFormal B S hS (u i) a
      (hUaffine i) (hUetale i).1 (hUetale i).2 hU₀
  -- the comparison map `Uᵢ ×_X U₀ ⟶ Vᵢ ×_Y V₀` induced by the two given squares
  have hcompat : ∀ i, (pullback.fst (u i) a ≫ t i) ≫ v i
      = (pullback.snd (u i) a ≫ τ) ≫ b := by
    intro i
    rw [Category.assoc, Category.assoc, ← hVsquare i, ← hsquare, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  let g : ∀ i, pullback (u i) a ⟶ pullback (v i) b := fun i ↦
    pullback.lift (pullback.fst (u i) a ≫ t i) (pullback.snd (u i) a ≫ τ) (hcompat i)
  have hgfst : ∀ i, g i ≫ pullback.fst (v i) b = pullback.fst (u i) a ≫ t i := fun i ↦
    pullback.lift_fst _ _ _
  have hgsnd : ∀ i, g i ≫ pullback.snd (v i) b = pullback.snd (u i) a ≫ τ := fun i ↦
    pullback.lift_snd _ _ _
  -- the second fibre product of the proof of Stacks 0ANG, over `Vᵢ ×_Y V₀`
  have hDfib : ∀ i (j : J i), IsFormalAlgebraicSpace B S hS (pullback (e i j) (g i)) :=
    fun i j ↦ isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS (e i j) (g i)
      (hVfib i) (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS (hZaffine i j))
      (hUfib i)
  choose K Wc w hWaffine hWetale hWsurjective using fun i (j : J i) ↦ (hDfib i j).2
  -- the base changes of the two given diagrams along the comparison map
  have hetfst : ∀ {P Q R : FppfSheaf B S hS} (x : P ⟶ R) {y : Q ⟶ R},
      IsRepresentableEtale B S hS y → IsRepresentableEtale B S hS (pullback.fst x y) :=
    fun x _ hy ↦ isRepresentableEtale_of_isPullback B S hS (IsPullback.of_hasPullback x _).flip hy
  have hetsndU : ∀ i, IsRepresentableEtale B S hS (pullback.snd (u i) a) := fun i ↦
    isRepresentableEtale_pullback_snd B S hS (u i) a (hUetale i)
  have hetsndV : ∀ i, IsRepresentableEtale B S hS (pullback.snd (v i) b) := fun i ↦
    isRepresentableEtale_pullback_snd B S hS (v i) b (hVetale i)
  have hetsndD : ∀ i (j : J i), IsRepresentableEtale B S hS (pullback.snd (e i j) (g i)) :=
    fun i j ↦ isRepresentableEtale_pullback_snd B S hS (e i j) (g i) (hZetale i j)
  -- the cartesian squares, on the level of the underlying presheaves
  have hsq : ∀ {P Q R : FppfSheaf B S hS} (x : P ⟶ R) (y : Q ⟶ R),
      IsPullback (pullback.fst x y).hom (pullback.snd x y).hom x.hom y.hom := fun x y ↦
    (IsPullback.of_hasPullback x y).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  -- each member is representable étale over `U₀`
  have hWet : ∀ i (j : J i) l, IsRepresentableEtale B S hS
      (w i j l ≫ pullback.snd (e i j) (g i) ≫ pullback.snd (u i) a) := fun i j l ↦
    IsRepresentableEtale.comp B S hS (hWetale i j l)
      (IsRepresentableEtale.comp B S hS (hetsndD i j) (hetsndU i))
  -- the cartesian square of the second fibre product, post-composed with an arbitrary map
  have hkey : ∀ i (j : J i) {T : FppfSheaf B S hS} (h : pullback (v i) b ⟶ T),
      pullback.snd (e i j) (g i) ≫ g i ≫ h
        = pullback.fst (e i j) (g i) ≫ e i j ≫ h := by
    intro i j T h
    simp only [← Category.assoc, pullback.condition]
  refine ⟨Σ i, Σ j : J i, K i j, fun s ↦ s.1, fun s ↦ Wc s.1 s.2.1 s.2.2,
    fun s ↦ Zc s.1 s.2.1,
    fun s ↦ w s.1 s.2.1 s.2.2 ≫ pullback.snd (e s.1 s.2.1) (g s.1) ≫
      pullback.snd (u s.1) a,
    fun s ↦ w s.1 s.2.1 s.2.2 ≫ pullback.snd (e s.1 s.2.1) (g s.1) ≫
      pullback.fst (u s.1) a,
    fun s ↦ w s.1 s.2.1 s.2.2 ≫ pullback.fst (e s.1 s.2.1) (g s.1),
    fun s ↦ e s.1 s.2.1 ≫ pullback.fst (v s.1) b,
    fun s ↦ e s.1 s.2.1 ≫ pullback.snd (v s.1) b,
    ⟨fun s ↦ hWaffine s.1 s.2.1 s.2.2, fun s ↦ ?_, ?_⟩,
    fun s ↦ hZaffine s.1 s.2.1,
    fun s ↦ IsRepresentableEtale.comp B S hS (hWetale s.1 s.2.1 s.2.2)
      (IsRepresentableEtale.comp B S hS (hetsndD s.1 s.2.1) (hetfst _ ha)),
    fun s ↦ IsRepresentableEtale.comp B S hS (hZetale s.1 s.2.1) (hetfst _ hb),
    fun s ↦ IsRepresentableEtale.comp B S hS (hZetale s.1 s.2.1) (hetsndV s.1),
    fun s ↦ ?_, fun s ↦ ?_⟩
  · exact hWet s.1 s.2.1 s.2.2
  · -- joint surjectivity, checked on points
    refine isLocallySurjective_sigmaDesc_of_jointly_surjective_points B S hS _
      (fun s ↦ hWaffine s.1 s.2.1 s.2.2)
      (fun s ↦ hWet s.1 s.2.1 s.2.2) ?_
    intro x₀
    -- a point of `U₀` lifts to a member of the given covering of `X`
    obtain ⟨i, y, hy⟩ := exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS u
      hUsurjective (Space.pointsMapULift.{u + 1} B S hS U₀.obj a.hom x₀)
    -- the two compatible points assemble to a point of `Uᵢ ×_X U₀`
    obtain ⟨d, -, hdsnd⟩ := Space.exists_point_of_isPullbackULift B S hS (hsq (u i) a) y x₀ hy
    -- its image in `Vᵢ ×_Y V₀` lifts to a chart `Vᵢⱼ`
    obtain ⟨j, z, hz⟩ := exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS
      (e i) (hZsurjective i)
      (Space.pointsMapULift.{u + 1} B S hS (pullback (u i) a).obj (g i).hom d)
    -- so the two points assemble to a point of the second fibre product
    obtain ⟨n, -, hnsnd⟩ := Space.exists_point_of_isPullbackULift B S hS (hsq (e i j) (g i)) z d hz
    -- and that point lifts to a chart `Uᵢⱼₖ`
    obtain ⟨l, pt, hpt⟩ := exists_pointsMapULift_eq_of_isLocallySurjective_sigmaDesc B S hS
      (w i j) (hWsurjective i j) n
    refine ⟨⟨i, j, l⟩, pt, ?_⟩
    have hdecomp : (w i j l ≫ pullback.snd (e i j) (g i) ≫ pullback.snd (u i) a).hom
        = (w i j l).hom ≫ (pullback.snd (e i j) (g i)).hom ≫ (pullback.snd (u i) a).hom := rfl
    rw [hdecomp, Space.pointsMapULift_comp, Space.pointsMapULift_comp, Function.comp_apply,
      Function.comp_apply, hpt, hnsnd, hdsnd]
  · -- the square over `Uᵢ ⟶ Vᵢ`
    simp only [Category.assoc]
    rw [← hgfst s.1, hkey s.1 s.2.1]
  · -- the square over `U₀ ⟶ V₀`
    simp only [Category.assoc]
    rw [← hgsnd s.1, hkey s.1 s.2.1]

/-- **The refinement of a covering of the source against an affine étale diagram, with finitely
many members.** This is
`AlgebraicGeometry.FormalSpace.exists_affineEtaleRefinement_of_sourceCover` followed by the
finiteness step of the proof of **Stacks 0ANG**: `U₀` is an affine formal algebraic space, so
`FormalSpace.exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace`
cuts the refinement down to a finite jointly surjective *subfamily*, whose members therefore
keep their maps to the members of the covering being refined and both of their commutative
squares.

This is the whole of `AlgebraicGeometry.FormalSpace.HasEtaleRefinementOfSourceCover'` except the
presentation of the refinement by completed étale ring maps — the two clauses
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleLocalizationOfChartMap` and
`AlgebraicGeometry.FormalSpace.IsCompletedEtaleFiniteCoverOfChartMap`, which are the
essential-surjectivity clause of **Stacks 0AN8** for the charts built here and which this
library does not carry.

NO TAG IS ATTACHED, for the reason given on
`AlgebraicGeometry.FormalSpace.exists_affineEtaleRefinement_of_sourceCover`. -/
theorem exists_finite_affineEtaleRefinement_of_sourceCover
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
    (t : ∀ i, U i ⟶ V i) (hUcover : IsAffineEtaleCover B S hS U u)
    (hVaffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (V i))
    (hVetale : ∀ i, IsRepresentableEtale B S hS (v i))
    (hVsquare : ∀ i, u i ≫ f = t i ≫ v i)
    {U₀ V₀ : FppfSheaf B S hS} (a : U₀ ⟶ X) (b : V₀ ⟶ Y) (τ : U₀ ⟶ V₀)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀)
    (hV₀ : IsAffineFormalAlgebraicSpace B S hS V₀)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hsquare : a ≫ f = τ ≫ b) :
    ∃ (σ : Type (u + 1)) (_ : Finite σ) (k : σ → I) (W Z : σ → FppfSheaf B S hS)
      (p : ∀ s, W s ⟶ U₀) (q : ∀ s, W s ⟶ U (k s)) (m : ∀ s, W s ⟶ Z s)
      (r : ∀ s, Z s ⟶ V (k s)) (c : ∀ s, Z s ⟶ V₀),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) ∧
        (∀ s, IsRepresentableEtale B S hS (q s)) ∧
        (∀ s, IsRepresentableEtale B S hS (r s)) ∧
        (∀ s, IsRepresentableEtale B S hS (c s)) ∧
        (∀ s, q s ≫ t (k s) = m s ≫ r s) ∧ (∀ s, p s ≫ τ = m s ≫ c s) := by
  obtain ⟨σ, k, W, Z, p, q, m, r, c, hWcover, hZaffine, hq, hr, hc, hsq₁, hsq₂⟩ :=
    exists_affineEtaleRefinement_of_sourceCover B S hS f U V u v t hUcover hVaffine hVetale
      hVsquare a b τ hU₀ hV₀ ha hb hsquare
  obtain ⟨K, hKfinite, κ, hsubcover⟩ :=
    exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace B S hS hU₀ W p
      hWcover
  exact ⟨K, hKfinite, fun s ↦ k (κ s), fun s ↦ W (κ s), fun s ↦ Z (κ s), fun s ↦ p (κ s),
    fun s ↦ q (κ s), fun s ↦ m (κ s), fun s ↦ r (κ s), fun s ↦ c (κ s), hsubcover,
    fun s ↦ hZaffine (κ s), fun s ↦ hq (κ s), fun s ↦ hr (κ s), fun s ↦ hc (κ s),
    fun s ↦ hsq₁ (κ s), fun s ↦ hsq₂ (κ s)⟩

end AlgebraicGeometry.FormalSpace

end
