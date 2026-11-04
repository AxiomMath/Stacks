module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroups
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GradedStructure

/-!
# Chow groups of motives are representable

Over a base field the functor `CH^i(-)` on the category `M_k` of Chow motives is represented by
the `(-i)`-twist `𝟙(-i)` of the unit motive:

  `CH^i(M) = Hom_{M_k}(𝟙(-i), M)`,

functorially in `M`.

This file builds the category of Chow motives on top of the Chow groups of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroups` (Stacks 0FGL) and the
identification `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)` of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePoint` (Stacks 0FG0 (3)), and
proves that identification restricts to a natural `ℚ`-linear isomorphism between `CH^i(M)` and
the morphisms `𝟙(-i) → M`.

## Main definitions

* `Stacks.WeilCohomology.CorrespondenceObj`: a scheme locally of finite type over the base,
  together with the dimension that fixes the degree of a correspondence on it; the objects on
  which correspondences live.
* `Stacks.WeilCohomology.MotiveCorr` and `Stacks.WeilCohomology.TotalCorr`: the degree-`r`
  correspondences between two such objects, and the total module `⨁ᵣ Corrʳ(P, Q)`.
* `Stacks.WeilCohomology.fromPointCorr`: the identification
  `CH^j(X) ⊗ ℚ = Corr^j(Spec k, X)` of Stacks 0FG0 (3), with its target read as a space of
  correspondences between objects.
* `Stacks.WeilCohomology.MotiveCalculus`: the correspondence calculus needed to speak about the
  *category* of motives — composition of correspondences in all degrees, the action of a
  correspondence of arbitrary degree on rational Chow groups, and the compatibility of that
  action with the identification of Stacks 0FG0 (3) — carried as data on top of
  `Stacks.WeilCohomology.CorrespondenceCalculus`.
* `Stacks.WeilCohomology.MotiveCalculus.homSubmodule`: the morphisms
  `q ∘ Corr^{n-m}(X, Y) ∘ p` of Stacks 0FGA between two Chow motives.
* `Stacks.WeilCohomology.MotiveCalculus.Obj`: the category `M_k` of Chow motives.
* `Stacks.WeilCohomology.MotiveCalculus.unitTwist`: the motive `𝟙(-i)`, the unit motive
  `(Spec k, [Δ], 0)` with its Tate twist shifted to `-i`.
* `Stacks.WeilCohomology.MotiveCalculus.chowGroupMap`: the map `CH^i(M) → CH^i(N)` induced by a
  morphism of motives, the restriction of the action of the underlying correspondence.
* `Stacks.WeilCohomology.MotiveCalculus.chowFunctor` and
  `Stacks.WeilCohomology.MotiveCalculus.homFunctor`: the functors `M ↦ CH^i(M)` and
  `M ↦ Hom(𝟙(-i), M)` from `M_k` to `ℚ`-vector spaces.

## Main results

* `Stacks.WeilCohomology.MotiveCalculus.mem_homSubmodule_iff`: a total correspondence is a
  morphism of motives exactly when it is a sandwich `p ∘ a ∘ q` of a homogeneous correspondence
  of degree `n - m` between the two projectors, which is the description of Stacks 0FGA.
* `Stacks.WeilCohomology.MotiveCalculus.chowGroupEquivHom`: **Stacks 0FGM**, the `ℚ`-linear
  isomorphism `CH^i(M) ≃ Hom_{M_k}(𝟙(-i), M)`.
* `Stacks.WeilCohomology.MotiveCalculus.chowGroupEquivHom_naturality`: **Stacks 0FGM**, that
  isomorphism is natural in `M`: it carries the map on Chow groups induced by a morphism
  `f : M → N` to postcomposition with `f`.
* `Stacks.WeilCohomology.MotiveCalculus.chowFunctorIso`: **Stacks 0FGM**, the two statements
  packaged as an isomorphism of functors `CH^i(-) ≅ Hom(𝟙(-i), -)` on `M_k`.

## Implementation notes

**Where the Tate twist sits.** A Chow motive is a triple `(X, p, m)` and `CH^i(X, p, m)` is
`p(CH^{i+m}(X) ⊗ ℚ)`. The unit motive is `(Spec k, [Δ], 0)` and its `(-i)`-twist is
`(Spec k, [Δ], -i)`, so the morphisms `𝟙(-i) → (X, p, m)` are the correspondences of degree
`m - (-i) = i + m` from `Spec k` to `X` that are fixed by `p`. Under the identification
`CH^{i+m}(X) ⊗ ℚ = Corr^{i+m}(Spec k, X)` of Stacks 0FG0 (3) these are exactly the rational Chow
classes fixed by `p`, which is `CH^i(M)`; that is the whole proof, and it is the proof of the
source.

**What is carried, and why.** `Stacks.WeilCohomology.CorrespondenceCalculus` already carries, as
data, composition of degree-zero self-correspondences and their pushforward action on rational
Chow groups: composition of correspondences needs the intersection product of Stacks 0FC1, the
Gysin pullback of Stacks 0FFB and the projection formula of Stacks 0FFC, none of which is
formalized in this repository. Speaking about the *category* of motives needs three further
pieces of that same uncarried input, and `Stacks.WeilCohomology.MotiveCalculus` carries exactly
those three:

* composition in *all* degrees, with its `ℚ`-bilinearity, associativity and diagonal unit
  laws — the `Stacks.WeilCohomology.GradedCompositionData` of Stacks 0FG2, i.e. Stacks 0FG0 (1)
  together with the unit laws of Stacks 0FFD, plus the agreement of that composition with the
  degree-zero composition already carried;
* the action `c ↦ c_*` of a correspondence of arbitrary degree on rational Chow groups, raising
  codimension by the degree, agreeing in degree zero with the action already carried; and
* the compatibility of that action with the identification of Stacks 0FG0 (3): pushing a Chow
  class forward by `c` is composing with `c` the correspondence from the base point that the
  class corresponds to. This is the second half of Stacks 0FG0 (3).

Nothing else is assumed: no hypothesis about the Chow groups of motives, about idempotent
splittings, or about the behaviour of the unit, and in particular the induced map on Chow
groups is *not* defined by transport along the isomorphism being constructed — it is the
restriction of the carried action of the correspondence, which is what makes naturality a
statement with content.

**Degrees as parameters rather than casts.** `i + n` and `(i + m) + (n - m)` are the same
integer written two ways but not the same type, and the Chow groups and correspondence spaces
here are indexed by integers. The carried action therefore takes its target index as a
*parameter* together with a proof that it has the required value, which removes every type cast
from the development; and the laws of composition are stated, following
`Stacks.WeilCohomology.GradedCompositionData`, after `DirectSum.lof` in the total correspondence
module, where indices are arguments rather than type indices.

**Why every object argument is explicit.** `Stacks.WeilCohomology.MotiveCorr` is indexed by
objects, and recovering an object from the type of a correspondence would mean solving
`?P.sX = sX` for `?P`; the elaborator cannot, and unfolding the correspondence spaces instead
diverges. Every definition below therefore takes its objects as explicit arguments, and
`Stacks.WeilCohomology.MotiveCalculus.compTotal`,
`Stacks.WeilCohomology.lofCorr` and `Stacks.WeilCohomology.componentCorr` wrap the direct-sum
operations with the objects supplied.

**Smoothness and projectivity.** As in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Transpose` and in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ChowGroups`, neither hypothesis enters any
definition or proof below and so neither is imposed: a Chow motive in the sense of the source is
one whose underlying scheme is smooth and projective over a base field.

## References

* [Stacks Project, Tag 0FGM](https://stacks.math.columbia.edu/tag/0FGM)
* [Stacks Project, Tag 0FGL](https://stacks.math.columbia.edu/tag/0FGL)
* [Stacks Project, Tag 0FGA](https://stacks.math.columbia.edu/tag/0FGA)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### The objects on which correspondences live -/

/-- An object carrying correspondences: a scheme locally of finite type over the base of a Chow
situation, together with the integer that fixes the degree of a correspondence having it as
target. As in `Stacks.WeilCohomology.Correspondence` the dimension is a parameter rather than a
quantity derived from the scheme, so no equidimensionality hypothesis is needed. -/
structure CorrespondenceObj (C : ChowSituation.{u}) where
  /-- The underlying scheme. -/
  X : Scheme.{u}
  /-- Its structure morphism to the base of the situation. -/
  sX : X ⟶ C.S
  /-- The structure morphism is locally of finite type, so `X` has Chow groups. -/
  [locallyOfFiniteType : LocallyOfFiniteType sX]
  /-- The dimension of `X`. -/
  dimension : ℤ

attribute [instance] CorrespondenceObj.locallyOfFiniteType

/-- The space `Corrʳ(P, Q)` of rational correspondences of degree `r` between two objects. -/
abbrev MotiveCorr (C : ChowSituation.{u}) (P Q : CorrespondenceObj C) (r : ℤ) : Type u :=
  Correspondence C P.sX Q.sX Q.dimension r

/-- The total module `⨁ᵣ Corrʳ(P, Q)` of correspondences of all degrees. -/
abbrev TotalCorr (C : ChowSituation.{u}) (P Q : CorrespondenceObj C) : Type u :=
  DirectSum ℤ fun k ↦ MotiveCorr C P Q k

/-- The inclusion of the degree-`r` correspondences into the total module. -/
abbrev lofCorr (C : ChowSituation.{u}) (P Q : CorrespondenceObj C) (r : ℤ)
    (a : MotiveCorr C P Q r) : TotalCorr C P Q :=
  DirectSum.lof ℚ ℤ (fun k ↦ MotiveCorr C P Q k) r a

/-- The degree-`r` homogeneous component of a total correspondence. -/
abbrev componentCorr (C : ChowSituation.{u}) (P Q : CorrespondenceObj C) (r : ℤ)
    (f : TotalCorr C P Q) : MotiveCorr C P Q r :=
  DirectSum.component ℚ ℤ (fun k ↦ MotiveCorr C P Q k) r f

/-- The inclusion of the degree-`r` correspondences into the total module is injective. -/
theorem lofCorr_injective {C : ChowSituation.{u}} (P Q : CorrespondenceObj C) (r : ℤ) :
    Function.Injective (lofCorr C P Q r) := by
  intro a b hab
  refine DirectSum.of_injective (β := fun k ↦ MotiveCorr C P Q k) r ?_
  rw [← DirectSum.lof_eq_of ℚ, ← DirectSum.lof_eq_of ℚ]
  exact hab

/-- The degree-`r` component of the inclusion of a degree-`r` correspondence is that
correspondence. -/
@[simp]
theorem componentCorr_lofCorr {C : ChowSituation.{u}} (P Q : CorrespondenceObj C) (r : ℤ)
    (a : MotiveCorr C P Q r) : componentCorr C P Q r (lofCorr C P Q r a) = a :=
  DirectSum.component.lof_self ℚ r a

/-- The base point `Spec k` of the situation, as an object carrying correspondences: the base
itself, with its identity as structure morphism and dimension `0`. -/
abbrev basePointObj (C : ChowSituation.{u}) : CorrespondenceObj C :=
  ⟨C.S, 𝟙 C.S, 0⟩

/-- **Stacks Project, Tag 0FG0 (3).** The identification
`CH^j(X) ⊗ ℚ = Corr^j(Spec k, X)` of
`Stacks.WeilCohomology.correspondenceFromPointEquiv`, with its target read as the space of
degree-`j` correspondences from the base point to `Q`. -/
abbrev fromPointCorr (C : ChowSituation.{u}) (Q : CorrespondenceObj C) (j : ℤ) :
    RationalChowGroupCodim C Q.sX Q.dimension j ≃ₗ[ℚ] MotiveCorr C (basePointObj C) Q j :=
  correspondenceFromPointEquiv C Q.sX Q.dimension j

/-- The degree-`r` homogeneous part of the total module of correspondences. -/
def corrGrade (C : ChowSituation.{u}) (P Q : CorrespondenceObj C) (r : ℤ) :
    Submodule ℚ (TotalCorr C P Q) :=
  LinearMap.range (DirectSum.lof ℚ ℤ (fun k ↦ MotiveCorr C P Q k) r)

/-- A total correspondence lies in the degree-`r` homogeneous part exactly when it is the inclusion
of a degree-`r` correspondence. -/
theorem mem_corrGrade_iff {C : ChowSituation.{u}} {P Q : CorrespondenceObj C} {r : ℤ}
    {f : TotalCorr C P Q} :
    f ∈ corrGrade C P Q r ↔ ∃ a : MotiveCorr C P Q r, lofCorr C P Q r a = f :=
  Iff.rfl

/-- The inclusion of a degree-`r` correspondence lies in the degree-`r` homogeneous part. -/
theorem lofCorr_mem_corrGrade {C : ChowSituation.{u}} (P Q : CorrespondenceObj C) (r : ℤ)
    (a : MotiveCorr C P Q r) : lofCorr C P Q r a ∈ corrGrade C P Q r :=
  ⟨a, rfl⟩

/-- A homogeneous correspondence lies in the homogeneous part of any degree equal to its own. -/
theorem lofCorr_mem_corrGrade' {C : ChowSituation.{u}} (P Q : CorrespondenceObj C) {r r' : ℤ}
    (h : r = r') (a : MotiveCorr C P Q r) : lofCorr C P Q r a ∈ corrGrade C P Q r' := by
  subst h
  exact ⟨a, rfl⟩

/-- A homogeneous total correspondence is recovered from its homogeneous component. The degree
is passed as a second parameter with a proof that it agrees, so that the lemma applies to any
integer expression equal to the degree of homogeneity. -/
theorem lofCorr_componentCorr_eq_self {C : ChowSituation.{u}} {P Q : CorrespondenceObj C}
    {r r' : ℤ} (h : r' = r) {f : TotalCorr C P Q} (hf : f ∈ corrGrade C P Q r) :
    lofCorr C P Q r' (componentCorr C P Q r' f) = f := by
  subst h
  obtain ⟨a, rfl⟩ := hf
  rw [componentCorr_lofCorr]

/-! ### The correspondence calculus of the category of motives -/

/-- The correspondence calculus needed to speak about the category of Chow motives, carried as
data on top of `Stacks.WeilCohomology.CorrespondenceCalculus`.

Every field is intersection-theoretic input that this repository does not have; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.Representability`. -/
structure MotiveCalculus (C : ChowSituation.{u}) extends CorrespondenceCalculus C where
  /-- Composition of correspondences in all degrees: `ℚ`-bilinear, degree-additive, associative
  and with the diagonal classes as two-sided units. This is the carried datum of Stacks 0FG2,
  standing in for Stacks 0FG0 (1) and the unit laws of Stacks 0FFD. -/
  graded : GradedCompositionData fun P Q r ↦ MotiveCorr C P Q r
  /-- The composition of degree-zero self-correspondences already carried by
  `Stacks.WeilCohomology.CorrespondenceCalculus` is the degree-zero case of the composition of
  all degrees. -/
  of_comp_eq : ∀ (P : CorrespondenceObj C) (c c' : MotiveCorr C P P 0),
    lofCorr C P P 0 (comp P.sX P.dimension c' c) =
      lofCorr C P P (0 + 0) (graded.comp (X := P) (Y := P) (Z := P) c c')
  /-- The action `c ↦ c_*` of a correspondence of degree `r` on rational Chow groups, raising
  codimension by `r`. The target codimension is a parameter together with a proof that it is
  `j + r`, so that the field applies at any integer expression of that value. -/
  act : ∀ (P Q : CorrespondenceObj C) (j j' r : ℤ), j' = j + r → MotiveCorr C P Q r →
    RationalChowGroupCodim C P.sX P.dimension j →ₗ[ℚ]
      RationalChowGroupCodim C Q.sX Q.dimension j'
  /-- In degree zero the action is the pushforward action already carried by
  `Stacks.WeilCohomology.CorrespondenceCalculus`. -/
  act_zero : ∀ (P : CorrespondenceObj C) (j : ℤ) (c : MotiveCorr C P P 0),
    act P P j j 0 (add_zero j).symm c = pushforward P.sX P.dimension (P.dimension - j) c
  /-- **The second half of Stacks 0FG0 (3).** Under the identification
  `CH^j(X) ⊗ ℚ = Corr^j(Spec k, X)`, pushing a rational Chow class forward by a correspondence
  `c` is composing with `c` the correspondence from the base point that the class corresponds
  to. -/
  of_fromPoint_act : ∀ (P Q : CorrespondenceObj C) (j j' r : ℤ) (hj : j' = j + r)
      (c : MotiveCorr C P Q r) (α : RationalChowGroupCodim C P.sX P.dimension j),
    lofCorr C (basePointObj C) Q j' (fromPointCorr C Q j' (act P Q j j' r hj c α)) =
      lofCorr C (basePointObj C) Q (j + r)
        (graded.comp (X := basePointObj C) (Y := P) (Z := Q) (fromPointCorr C P j α) c)

namespace MotiveCalculus

variable {C : ChowSituation.{u}} (D : MotiveCalculus C)

/-! ### Composition of total correspondences -/

/-- Composition of total correspondences, with the three objects supplied explicitly. -/
abbrev compTotal (P Q R : CorrespondenceObj C) (f : TotalCorr C P Q) (g : TotalCorr C Q R) :
    TotalCorr C P R :=
  D.graded.compLinear P Q R f g

/-- The composite of homogeneous correspondences of degrees `r` and `s` is homogeneous of degree
`r + s`, given by their composition. -/
theorem compTotal_lofCorr (P Q R : CorrespondenceObj C) (r s : ℤ) (a : MotiveCorr C P Q r)
    (b : MotiveCorr C Q R s) :
    D.compTotal P Q R (lofCorr C P Q r a) (lofCorr C Q R s b) =
      lofCorr C P R (r + s) (D.graded.comp (X := P) (Y := Q) (Z := R) a b) :=
  D.graded.compLinear_of_of a b

/-- Composition of total correspondences is associative. -/
theorem compTotal_assoc (P Q R S : CorrespondenceObj C) (f : TotalCorr C P Q)
    (g : TotalCorr C Q R) (h : TotalCorr C R S) :
    D.compTotal P R S (D.compTotal P Q R f g) h = D.compTotal P Q S f (D.compTotal Q R S g h) :=
  D.graded.compLinear_assoc f g h

/-- The diagonal class is a left unit for composition of total correspondences. -/
theorem diagonal_compTotal (P Q : CorrespondenceObj C) (f : TotalCorr C P Q) :
    D.compTotal P P Q (lofCorr C P P 0 (D.graded.diagonal P)) f = f :=
  D.graded.diagonal_compLinear f

/-- Composing the zero correspondence with any correspondence gives zero. -/
theorem compTotal_zero_left (P Q R : CorrespondenceObj C) (g : TotalCorr C Q R) :
    D.compTotal P Q R 0 g = 0 :=
  DFunLike.congr_fun (map_zero (D.graded.compLinear P Q R)) g

/-- Composing any correspondence with the zero correspondence gives zero. -/
theorem compTotal_zero_right (P Q R : CorrespondenceObj C) (f : TotalCorr C P Q) :
    D.compTotal P Q R f 0 = 0 :=
  map_zero (D.graded.compLinear P Q R f)

/-- Composition of total correspondences is additive in the first argument. -/
theorem compTotal_add_left (P Q R : CorrespondenceObj C) (f f' : TotalCorr C P Q)
    (g : TotalCorr C Q R) :
    D.compTotal P Q R (f + f') g = D.compTotal P Q R f g + D.compTotal P Q R f' g :=
  DFunLike.congr_fun ((D.graded.compLinear P Q R).map_add f f') g

/-- Composition of total correspondences is additive in the second argument. -/
theorem compTotal_add_right (P Q R : CorrespondenceObj C) (f : TotalCorr C P Q)
    (g g' : TotalCorr C Q R) :
    D.compTotal P Q R f (g + g') = D.compTotal P Q R f g + D.compTotal P Q R f g' :=
  (D.graded.compLinear P Q R f).map_add g g'

/-- Composition of total correspondences is `ℚ`-homogeneous in the first argument. -/
theorem compTotal_smul_left (P Q R : CorrespondenceObj C) (w : ℚ) (f : TotalCorr C P Q)
    (g : TotalCorr C Q R) :
    D.compTotal P Q R (w • f) g = w • D.compTotal P Q R f g :=
  DFunLike.congr_fun ((D.graded.compLinear P Q R).map_smul w f) g

/-- Composition of total correspondences is `ℚ`-homogeneous in the second argument. -/
theorem compTotal_smul_right (P Q R : CorrespondenceObj C) (w : ℚ) (f : TotalCorr C P Q)
    (g : TotalCorr C Q R) :
    D.compTotal P Q R f (w • g) = w • D.compTotal P Q R f g :=
  (D.graded.compLinear P Q R f).map_smul w g

/-! ### The projector of a motive, and the diagonal -/

/-- The object carrying the correspondences of a Chow motive: its scheme, structure morphism and
dimension. -/
abbrev motiveObj {A : CorrespondenceCalculus C} (M : ChowMotive C A) : CorrespondenceObj C :=
  ⟨M.X, M.sX, M.dimension⟩

/-- The projector of a Chow motive as a total correspondence, homogeneous of degree zero. -/
abbrev projectorTotal (M : ChowMotive C D.toCorrespondenceCalculus) :
    TotalCorr C (motiveObj M) (motiveObj M) :=
  lofCorr C (motiveObj M) (motiveObj M) 0 M.projector

/-- The projector of a Chow motive is idempotent for composition in all degrees. -/
theorem compTotal_projectorTotal_self (M : ChowMotive C D.toCorrespondenceCalculus) :
    D.compTotal (motiveObj M) (motiveObj M) (motiveObj M) (D.projectorTotal M)
        (D.projectorTotal M) = D.projectorTotal M := by
  rw [projectorTotal, D.compTotal_lofCorr, ← D.of_comp_eq (motiveObj M) M.projector M.projector]
  exact congrArg _ M.projector_idempotent

/-- The diagonal class of an object is idempotent for the degree-zero composition carried by the
underlying correspondence calculus. -/
theorem comp_diagonal_self (P : CorrespondenceObj C) :
    D.toCorrespondenceCalculus.comp P.sX P.dimension (D.graded.diagonal P)
        (D.graded.diagonal P) = D.graded.diagonal P := by
  refine lofCorr_injective P P 0 ?_
  rw [D.of_comp_eq P (D.graded.diagonal P) (D.graded.diagonal P)]
  exact D.graded.of_diagonal_comp (D.graded.diagonal P)

/-! ### The category of Chow motives -/

/-- The morphisms `(X, p, m) → (Y, q, n)` of Chow motives of Stacks 0FGA: the correspondences of
degree `n - m` from `X` to `Y` that are fixed by `p` on the left and by `q` on the right. By
`Stacks.WeilCohomology.MotiveCalculus.mem_homSubmodule_iff` these are exactly the sandwiches
`q ∘ a ∘ p`, which is the description of the source. -/
def homSubmodule (M N : ChowMotive C D.toCorrespondenceCalculus) :
    Submodule ℚ (TotalCorr C (motiveObj M) (motiveObj N)) where
  carrier :=
    {f | f ∈ corrGrade C (motiveObj M) (motiveObj N) (N.twist - M.twist) ∧
      D.compTotal (motiveObj M) (motiveObj M) (motiveObj N) (D.projectorTotal M) f = f ∧
      D.compTotal (motiveObj M) (motiveObj N) (motiveObj N) f (D.projectorTotal N) = f}
  zero_mem' :=
    ⟨Submodule.zero_mem _, D.compTotal_zero_right _ _ _ _, D.compTotal_zero_left _ _ _ _⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨Submodule.add_mem _ hf.1 hg.1,
      by rw [D.compTotal_add_right, hf.2.1, hg.2.1],
      by rw [D.compTotal_add_left, hf.2.2, hg.2.2]⟩
  smul_mem' := by
    intro w f hf
    exact ⟨Submodule.smul_mem _ w hf.1,
      by rw [D.compTotal_smul_right, hf.2.1],
      by rw [D.compTotal_smul_left, hf.2.2]⟩

/-- A total correspondence is a morphism of motives `(X, p, m) → (Y, q, n)` exactly when it is
homogeneous of degree `n - m`, fixed by `p` on the left and fixed by `q` on the right. -/
theorem mem_homSubmodule {M N : ChowMotive C D.toCorrespondenceCalculus}
    {f : TotalCorr C (motiveObj M) (motiveObj N)} :
    f ∈ D.homSubmodule M N ↔
      (f ∈ corrGrade C (motiveObj M) (motiveObj N) (N.twist - M.twist) ∧
        D.compTotal (motiveObj M) (motiveObj M) (motiveObj N) (D.projectorTotal M) f = f ∧
        D.compTotal (motiveObj M) (motiveObj N) (motiveObj N) f (D.projectorTotal N) = f) :=
  Iff.rfl

/-- A total correspondence is a morphism of motives `(X, p, m) → (Y, q, n)` exactly when it is a
sandwich `p ∘ a ∘ q` of a correspondence `a` homogeneous of degree `n - m`: the fixed set of the
idempotent sandwich operator is its image. -/
@[stacks 0FGA "the morphisms of the category of motives are the sandwiched correspondences"]
theorem mem_homSubmodule_iff {M N : ChowMotive C D.toCorrespondenceCalculus}
    {f : TotalCorr C (motiveObj M) (motiveObj N)} :
    f ∈ D.homSubmodule M N ↔
      ∃ a ∈ corrGrade C (motiveObj M) (motiveObj N) (N.twist - M.twist),
        D.compTotal (motiveObj M) (motiveObj N) (motiveObj N)
          (D.compTotal (motiveObj M) (motiveObj M) (motiveObj N) (D.projectorTotal M) a)
          (D.projectorTotal N) = f := by
  refine ⟨fun hf ↦ ⟨f, hf.1, by rw [hf.2.1, hf.2.2]⟩, ?_⟩
  rintro ⟨a, ha, rfl⟩
  obtain ⟨b, rfl⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · rw [projectorTotal, projectorTotal, D.compTotal_lofCorr, D.compTotal_lofCorr]
    exact lofCorr_mem_corrGrade' _ _ (by omega) _
  · rw [← D.compTotal_assoc, ← D.compTotal_assoc, D.compTotal_projectorTotal_self]
  · rw [D.compTotal_assoc, D.compTotal_projectorTotal_self]

/-- An object of the category `M_k` of Chow motives. -/
structure Obj (D : MotiveCalculus C) where
  /-- The underlying Chow motive. -/
  as : ChowMotive C D.toCorrespondenceCalculus

/-- The category of Chow motives: Chow motives as objects, the sandwiched correspondences of
degree `n - m` as morphisms, the projector as the identity and composition of correspondences as
composition. -/
@[stacks 0FGA "the category of Chow motives"]
instance category : Category.{u} D.Obj where
  Hom M N := ↥(D.homSubmodule M.as N.as)
  id M := ⟨D.projectorTotal M.as, by
    refine ⟨?_, D.compTotal_projectorTotal_self M.as, D.compTotal_projectorTotal_self M.as⟩
    rw [show M.as.twist - M.as.twist = 0 from sub_self _, projectorTotal]
    exact lofCorr_mem_corrGrade (motiveObj M.as) (motiveObj M.as) 0 M.as.projector⟩
  comp {M N P} f g := ⟨D.compTotal (motiveObj M.as) (motiveObj N.as) (motiveObj P.as) f.1 g.1, by
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := f.2.1
      obtain ⟨b, hb⟩ := g.2.1
      rw [← ha, ← hb, D.compTotal_lofCorr]
      exact lofCorr_mem_corrGrade' (motiveObj M.as) (motiveObj P.as)
        (show N.as.twist - M.as.twist + (P.as.twist - N.as.twist) =
          P.as.twist - M.as.twist by omega)
        (D.graded.comp (X := motiveObj M.as) (Y := motiveObj N.as) (Z := motiveObj P.as) a b)
    · rw [← D.compTotal_assoc, f.2.2.1]
    · rw [D.compTotal_assoc, g.2.2.2]⟩
  id_comp f := Subtype.ext f.2.2.1
  comp_id f := Subtype.ext f.2.2.2
  assoc f g h := Subtype.ext (D.compTotal_assoc _ _ _ _ f.1 g.1 h.1)

/-- The correspondence underlying a composite of morphisms of motives is the composite of the
underlying correspondences. -/
theorem hom_comp_val {M N P : D.Obj} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).1 = D.compTotal (motiveObj M.as) (motiveObj N.as) (motiveObj P.as) f.1 g.1 :=
  rfl

/-- The correspondence underlying the identity of a motive is its projector. -/
theorem hom_id_val (M : D.Obj) : (𝟙 M : M ⟶ M).1 = D.projectorTotal M.as :=
  rfl

/-- Chow motives form a preadditive category. -/
instance preadditive : Preadditive D.Obj where
  homGroup M N := inferInstanceAs (AddCommGroup ↥(D.homSubmodule M.as N.as))
  add_comp _ _ _ f f' g := Subtype.ext (D.compTotal_add_left _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (D.compTotal_add_right _ _ _ f.1 g.1 g'.1)

/-- Chow motives form an `ℚ`-linear category. -/
instance linear : Linear ℚ D.Obj where
  homModule M N := inferInstanceAs (Module ℚ ↥(D.homSubmodule M.as N.as))
  smul_comp _ _ _ w f g := Subtype.ext (D.compTotal_smul_left _ _ _ w f.1 g.1)
  comp_smul _ _ _ f w g := Subtype.ext (D.compTotal_smul_right _ _ _ w f.1 g.1)

/-! ### The unit motive and its Tate twists -/

/-- The unit motive `(Spec k, [Δ], 0)` of `M_k` with its Tate twist shifted to `-i`: the motive
`𝟙(-i)` representing `CH^i(-)`. -/
abbrev unitTwistMotive (i : ℤ) : ChowMotive C D.toCorrespondenceCalculus where
  X := C.S
  sX := 𝟙 C.S
  dimension := 0
  projector := D.graded.diagonal (basePointObj C)
  projector_idempotent := D.comp_diagonal_self (basePointObj C)
  twist := -i

/-- The motive `𝟙(-i)`, as an object of `M_k`. -/
abbrev unitTwist (i : ℤ) : D.Obj := ⟨D.unitTwistMotive i⟩

/-! ### The identification of Stacks 0FG0 (3), in the total correspondence module -/

/-- The rational Chow class `α` of codimension `i + m` on the underlying scheme of a motive
`M = (X, p, m)`, viewed through Stacks 0FG0 (3) as a total correspondence from the base point,
homogeneous of degree `i + m`. -/
abbrev fromPointTotal (M : ChowMotive C D.toCorrespondenceCalculus) (i : ℤ)
    (α : RationalChowGroupCodim C M.sX M.dimension (i + M.twist)) :
    TotalCorr C (basePointObj C) (motiveObj M) :=
  lofCorr C (basePointObj C) (motiveObj M) (i + M.twist)
    (fromPointCorr C (motiveObj M) (i + M.twist) α)

/-- `Stacks.WeilCohomology.MotiveCalculus.fromPointTotal` as a `ℚ`-linear map. -/
abbrev fromPointTotalLinear (M : ChowMotive C D.toCorrespondenceCalculus) (i : ℤ) :
    RationalChowGroupCodim C M.sX M.dimension (i + M.twist) →ₗ[ℚ]
      TotalCorr C (basePointObj C) (motiveObj M) :=
  (DirectSum.lof ℚ ℤ (fun k ↦ MotiveCorr C (basePointObj C) (motiveObj M) k)
      (i + M.twist)).comp
    (fromPointCorr C (motiveObj M) (i + M.twist)).toLinearMap

/-- `Stacks.WeilCohomology.MotiveCalculus.fromPointTotal` is injective. -/
theorem fromPointTotal_injective (M : ChowMotive C D.toCorrespondenceCalculus) (i : ℤ) :
    Function.Injective (D.fromPointTotal M i) := fun _ _ hαβ ↦
  (fromPointCorr C (motiveObj M) (i + M.twist)).injective
    (lofCorr_injective (basePointObj C) (motiveObj M) (i + M.twist) hαβ)

/-- The degree-`(i + m)` component of the total correspondence attached to a rational Chow class
`α` is the correspondence from the base point corresponding to `α`. -/
theorem componentCorr_fromPointTotal (M : ChowMotive C D.toCorrespondenceCalculus) (i : ℤ)
    (α : RationalChowGroupCodim C M.sX M.dimension (i + M.twist)) :
    componentCorr C (basePointObj C) (motiveObj M) (i + M.twist) (D.fromPointTotal M i α) =
      fromPointCorr C (motiveObj M) (i + M.twist) α :=
  componentCorr_lofCorr (basePointObj C) (motiveObj M) (i + M.twist)
    (fromPointCorr C (motiveObj M) (i + M.twist) α)

/-- A total correspondence from the base point, homogeneous of degree `i + m`, is the total
correspondence attached to the rational Chow class corresponding to its homogeneous component. -/
theorem fromPointTotal_component (M : ChowMotive C D.toCorrespondenceCalculus) (i : ℤ)
    (f : TotalCorr C (basePointObj C) (motiveObj M))
    (hf : f ∈ corrGrade C (basePointObj C) (motiveObj M) (i + M.twist)) :
    D.fromPointTotal M i ((fromPointCorr C (motiveObj M) (i + M.twist)).symm
        (componentCorr C (basePointObj C) (motiveObj M) (i + M.twist) f)) = f := by
  rw [fromPointTotal, LinearEquiv.apply_symm_apply]
  exact lofCorr_componentCorr_eq_self rfl hf

/-- Composing the correspondence attached to a rational Chow class with the projector of the
motive is the projector acting on the class: the degree-zero case of the second half of Stacks
0FG0 (3), which is the case the Chow group of a motive is built from. -/
theorem compTotal_fromPointTotal_projectorTotal
    (M : ChowMotive C D.toCorrespondenceCalculus) (i : ℤ)
    (α : RationalChowGroupCodim C M.sX M.dimension (i + M.twist)) :
    D.compTotal (basePointObj C) (motiveObj M) (motiveObj M) (D.fromPointTotal M i α)
        (D.projectorTotal M) = D.fromPointTotal M i (M.projectorAction i α) := by
  have h := D.of_fromPoint_act (motiveObj M) (motiveObj M) (i + M.twist) (i + M.twist) 0
    (add_zero (i + M.twist)).symm M.projector α
  rw [D.act_zero (motiveObj M) (i + M.twist) M.projector] at h
  rw [fromPointTotal, projectorTotal, D.compTotal_lofCorr, ← h]
  rfl

/-- Composing the correspondence attached to a rational Chow class with a homogeneous
correspondence is the action of that correspondence on the class: the second half of Stacks
0FG0 (3). -/
theorem compTotal_fromPointTotal_lofCorr (M N : ChowMotive C D.toCorrespondenceCalculus)
    (i r j' : ℤ) (hj : j' = i + M.twist + r)
    (c : MotiveCorr C (motiveObj M) (motiveObj N) r)
    (α : RationalChowGroupCodim C M.sX M.dimension (i + M.twist)) :
    D.compTotal (basePointObj C) (motiveObj M) (motiveObj N) (D.fromPointTotal M i α)
        (lofCorr C (motiveObj M) (motiveObj N) r c) =
      lofCorr C (basePointObj C) (motiveObj N) j'
        (fromPointCorr C (motiveObj N) j'
          (D.act (motiveObj M) (motiveObj N) (i + M.twist) j' r hj c α)) := by
  rw [fromPointTotal, D.compTotal_lofCorr]
  exact (D.of_fromPoint_act (motiveObj M) (motiveObj N) (i + M.twist) j' r hj c α).symm

/-! ### The induced map on Chow groups -/

/-- The underlying homogeneous correspondence of degree `n - m` of a morphism of motives. -/
abbrev homCorr {M N : D.Obj} (f : M ⟶ N) :
    MotiveCorr C (motiveObj M.as) (motiveObj N.as) (N.as.twist - M.as.twist) :=
  componentCorr C (motiveObj M.as) (motiveObj N.as) (N.as.twist - M.as.twist) f.1

/-- A morphism of motives is the inclusion of its underlying homogeneous correspondence. -/
theorem lofCorr_homCorr {M N : D.Obj} (f : M ⟶ N) :
    lofCorr C (motiveObj M.as) (motiveObj N.as) (N.as.twist - M.as.twist) (D.homCorr f) = f.1 :=
  lofCorr_componentCorr_eq_self rfl f.2.1

/-- The action on rational Chow classes of codimension `i + m` of the correspondence underlying
a morphism of motives `f : M → N`, landing in codimension `i + n`. -/
abbrev chowAct {M N : D.Obj} (i : ℤ) (f : M ⟶ N) :
    RationalChowGroupCodim C M.as.sX M.as.dimension (i + M.as.twist) →ₗ[ℚ]
      RationalChowGroupCodim C N.as.sX N.as.dimension (i + N.as.twist) :=
  D.act (motiveObj M.as) (motiveObj N.as) (i + M.as.twist) (i + N.as.twist)
    (N.as.twist - M.as.twist) (by omega) (D.homCorr f)

/-- Composing the correspondence attached to a rational Chow class `α` on `M` with a morphism of
motives `f : M → N` gives the correspondence attached to the action of `f` on `α`. -/
theorem compTotal_fromPointTotal_hom {M N : D.Obj} (i : ℤ) (f : M ⟶ N)
    (α : RationalChowGroupCodim C M.as.sX M.as.dimension (i + M.as.twist)) :
    D.compTotal (basePointObj C) (motiveObj M.as) (motiveObj N.as) (D.fromPointTotal M.as i α)
        f.1 = D.fromPointTotal N.as i (D.chowAct i f α) := by
  rw [← D.lofCorr_homCorr f, D.compTotal_fromPointTotal_lofCorr M.as N.as i
    (N.as.twist - M.as.twist) (i + N.as.twist) (by omega) (D.homCorr f) α]

/-- The action of the correspondence underlying a morphism of motives `f : M → N` lands in
`CH^i(N)`, and does so on *every* rational Chow class of codimension `i + m`, not only on those
of `CH^i(M)`: the target projector already fixes `f`. In particular a morphism of motives
carries `CH^i(M)` into `CH^i(N)`. -/
theorem chowAct_mem_chowGroup {M N : D.Obj} (i : ℤ) (f : M ⟶ N)
    (α : RationalChowGroupCodim C M.as.sX M.as.dimension (i + M.as.twist)) :
    D.chowAct i f α ∈ N.as.chowGroup i := by
  rw [ChowMotive.mem_chowGroup_iff]
  refine D.fromPointTotal_injective N.as i ?_
  rw [← D.compTotal_fromPointTotal_projectorTotal, ← D.compTotal_fromPointTotal_hom,
    D.compTotal_assoc, f.2.2.2]

/-- The map `CH^i(M) → CH^i(N)` induced by a morphism of motives `f : M → N`: the restriction to
the two Chow groups of the action of the correspondence underlying `f`. This is the action of
`CH^i(-)` on morphisms, and `Stacks.WeilCohomology.MotiveCalculus.chowGroupEquivHom_naturality`
is the assertion of Stacks 0FGM about it. -/
def chowGroupMap (i : ℤ) {M N : D.Obj} (f : M ⟶ N) :
    ↥(M.as.chowGroup i) →ₗ[ℚ] ↥(N.as.chowGroup i) :=
  (D.chowAct i f).restrict fun α _ ↦ D.chowAct_mem_chowGroup i f α

/-- The map on Chow groups induced by a morphism of motives is the action of its underlying
correspondence on rational Chow classes. -/
theorem chowGroupMap_val (i : ℤ) {M N : D.Obj} (f : M ⟶ N) (α : ↥(M.as.chowGroup i)) :
    (D.chowGroupMap i f α).1 = D.chowAct i f α.1 :=
  rfl

/-! ### Representability -/

/-- The degree `n - (-i)` of morphisms `𝟙(-i) → (X, p, n)` is `i + n`. -/
theorem unitTwist_twist_sub (M : D.Obj) (i : ℤ) :
    M.as.twist - (D.unitTwistMotive i).twist = i + M.as.twist := by
  show M.as.twist - -i = i + M.as.twist
  omega

/-- The functor `CH^i(-)` on the category of Chow motives is represented by the `(-i)`-twist of
the unit motive: the identification
`CH^{i+m}(X) ⊗ ℚ = Corr^{i+m}(Spec k, X)` of Stacks 0FG0 (3) restricts to an isomorphism of
`ℚ`-vector spaces

  `CH^i(M) ≃ Hom_{M_k}(𝟙(-i), M)`.

Naturality in `M` is `Stacks.WeilCohomology.MotiveCalculus.chowGroupEquivHom_naturality`, and
the two together are packaged as
`Stacks.WeilCohomology.MotiveCalculus.chowFunctorIso`. -/
@[stacks 0FGM "CH^i(M) = Hom(1(-i), M)"]
def chowGroupEquivHom (M : D.Obj) (i : ℤ) : ↥(M.as.chowGroup i) ≃ₗ[ℚ] (D.unitTwist i ⟶ M) where
  toFun α := ⟨D.fromPointTotal M.as i α.1, by
    refine ⟨?_, ?_, ?_⟩
    · rw [D.unitTwist_twist_sub M i]
      exact lofCorr_mem_corrGrade (basePointObj C) (motiveObj M.as) (i + M.as.twist)
        (fromPointCorr C (motiveObj M.as) (i + M.as.twist) α.1)
    · exact D.diagonal_compTotal (basePointObj C) (motiveObj M.as) _
    · rw [D.compTotal_fromPointTotal_projectorTotal]
      exact congrArg _ ((ChowMotive.mem_chowGroup_iff M.as i α.1).1 α.2)⟩
  map_add' α β := Subtype.ext ((D.fromPointTotalLinear M.as i).map_add α.1 β.1)
  map_smul' w α := Subtype.ext ((D.fromPointTotalLinear M.as i).map_smul w α.1)
  invFun f := ⟨(fromPointCorr C (motiveObj M.as) (i + M.as.twist)).symm
      (componentCorr C (basePointObj C) (motiveObj M.as) (i + M.as.twist) f.1), by
    have hgrade : f.1 ∈ corrGrade C (basePointObj C) (motiveObj M.as) (i + M.as.twist) := by
      rw [← D.unitTwist_twist_sub M i]; exact f.2.1
    have hfix := D.fromPointTotal_component M.as i f.1 hgrade
    rw [ChowMotive.mem_chowGroup_iff]
    refine D.fromPointTotal_injective M.as i ?_
    rw [← D.compTotal_fromPointTotal_projectorTotal, hfix, f.2.2.2, ← hfix]⟩
  left_inv α := by
    refine Subtype.ext ?_
    change (fromPointCorr C (motiveObj M.as) (i + M.as.twist)).symm
        (componentCorr C (basePointObj C) (motiveObj M.as) (i + M.as.twist)
          (D.fromPointTotal M.as i α.1)) = α.1
    rw [D.componentCorr_fromPointTotal M.as i α.1, LinearEquiv.symm_apply_apply]
  right_inv f :=
    Subtype.ext (D.fromPointTotal_component M.as i f.1 (by
      rw [← D.unitTwist_twist_sub M i]; exact f.2.1))

/-- The morphism `𝟙(-i) → M` attached to a class `α ∈ CH^i(M)` is the total correspondence from
the base point corresponding to `α`. -/
theorem chowGroupEquivHom_apply_val (M : D.Obj) (i : ℤ) (α : ↥(M.as.chowGroup i)) :
    (D.chowGroupEquivHom M i α).1 = D.fromPointTotal M.as i α.1 :=
  rfl

/-- The isomorphism `CH^i(M) ≃ Hom(𝟙(-i), M)` is natural in `M`: it carries the map on Chow
groups induced by a morphism of motives `f : M → N` — the restriction of the action of the
correspondence underlying `f` — to postcomposition with `f`. -/
@[stacks 0FGM "the identification is functorial in the motive"]
theorem chowGroupEquivHom_naturality {M N : D.Obj} (i : ℤ) (f : M ⟶ N)
    (α : ↥(M.as.chowGroup i)) :
    D.chowGroupEquivHom N i (D.chowGroupMap i f α) = D.chowGroupEquivHom M i α ≫ f :=
  Subtype.ext (D.compTotal_fromPointTotal_hom i f α.1).symm

/-- The identity of a motive acts as the identity on its Chow group. -/
theorem chowGroupMap_id (M : D.Obj) (i : ℤ) : D.chowGroupMap i (𝟙 M) = LinearMap.id := by
  refine LinearMap.ext fun α ↦ (D.chowGroupEquivHom M i).injective ?_
  rw [D.chowGroupEquivHom_naturality i (𝟙 M) α, Category.comp_id]
  rfl

/-- The map on Chow groups induced by a composite of morphisms of motives is the composite of
the induced maps. -/
theorem chowGroupMap_comp {M N P : D.Obj} (i : ℤ) (f : M ⟶ N) (g : N ⟶ P) :
    D.chowGroupMap i (f ≫ g) = (D.chowGroupMap i g).comp (D.chowGroupMap i f) := by
  refine LinearMap.ext fun α ↦ (D.chowGroupEquivHom P i).injective ?_
  rw [D.chowGroupEquivHom_naturality i (f ≫ g) α,
    show (D.chowGroupMap i g).comp (D.chowGroupMap i f) α =
      D.chowGroupMap i g (D.chowGroupMap i f α) from rfl,
    D.chowGroupEquivHom_naturality i g (D.chowGroupMap i f α),
    D.chowGroupEquivHom_naturality i f α, Category.assoc]

/-- The functor `CH^i(-)` from the category of Chow motives to `ℚ`-vector spaces. Its action on
morphisms is `Stacks.WeilCohomology.MotiveCalculus.chowGroupMap`, the restriction of the action
of the underlying correspondence; the functor laws follow from naturality of
`Stacks.WeilCohomology.MotiveCalculus.chowGroupEquivHom`. -/
def chowFunctor (i : ℤ) : D.Obj ⥤ ModuleCat.{u} ℚ where
  obj M := ModuleCat.of ℚ ↥(M.as.chowGroup i)
  map f := ModuleCat.ofHom (D.chowGroupMap i f)
  map_id M := by rw [D.chowGroupMap_id M i]; rfl
  map_comp f g := by rw [D.chowGroupMap_comp i f g]; rfl

/-- The functor `Hom(𝟙(-i), -)` on the category of Chow motives, with values in `ℚ`-vector
spaces: the functor that `Stacks.WeilCohomology.MotiveCalculus.chowFunctor` is isomorphic to. -/
def homFunctor (i : ℤ) : D.Obj ⥤ ModuleCat.{u} ℚ where
  obj M := ModuleCat.of ℚ (D.unitTwist i ⟶ M)
  map f := ModuleCat.ofHom
    { toFun := fun g ↦ g ≫ f
      map_add' := fun _ _ ↦ Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun _ _ ↦ Linear.smul_comp _ _ _ _ _ _ }
  map_id _ := ModuleCat.hom_ext (LinearMap.ext fun g ↦ Category.comp_id g)
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun h ↦ (Category.assoc h f g).symm)

/-- The functor `CH^i(-)` on the category of Chow motives is representable by `𝟙(-i)`: an
isomorphism of functors `CH^i(-) ≅ Hom_{M_k}(𝟙(-i), -)` with values in `ℚ`-vector spaces. -/
@[stacks 0FGM "CH^i(-) is representable by 1(-i), as functors"]
def chowFunctorIso (i : ℤ) : D.chowFunctor i ≅ D.homFunctor i :=
  NatIso.ofComponents (fun M ↦ (D.chowGroupEquivHom M i).toModuleIso) fun {_ _} f ↦
    ModuleCat.hom_ext (LinearMap.ext fun α ↦ D.chowGroupEquivHom_naturality i f α)

end MotiveCalculus

end Stacks.WeilCohomology

end
