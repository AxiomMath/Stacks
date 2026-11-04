module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceUndeformedTargetSurjective
public import StacksFrontier.Deformation.LiftsOfObjects.Action.PairTorsor

/-!
# The simply transitive action of local derivations on lifts into an undeformed target

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, let `b : W ⟶ V`
be a morphism of algebraic spaces, let `a : Z ⟶ W` be a morphism and let `β : X ⟶ V` be a
structure morphism.  A *lift of `a` over `V`* is a morphism `c : X ⟶ W` with

* `i ≫ c = a`, its restriction to the thickening, and
* `c ≫ b = β`, so that it is a morphism over `V`.

This file equips the set of such lifts with the simply transitive action of the group of
`𝒪_Z`-linear maps `a^*Ω_{W/V} ⟶ 𝒞_{Z/X}`: the translate `θ +ᵥ c` is the unique lift whose
difference from `c` is `θ`.  This is the action of [Stacks Project, Tag 061C] and the notation
`θ · c` of [Stacks Project, Tag 0CK6], **for an undeformed target**, and it is unconditional —
no part of [Stacks Project, Tag 05ZM] and no identification of the small étale topoi of a
thickening are used.

## Main definitions

* `AlgebraicGeometry.Space.IsUndeformedLift` is the condition of being such a lift.
* `AlgebraicGeometry.Space.UndeformedLifts` is the set of lifts.
* `AlgebraicGeometry.Space.UndeformedLiftDerivations` is the acting group
  `Hom_{𝒪_Z}(a^*Ω_{W/V}, 𝒞_{Z/X})`.
* `AlgebraicGeometry.Space.undeformedLiftsDiff` is the difference of two lifts, the `θ` of
  Equation [Stacks Project, Tag 0619].
* `AlgebraicGeometry.Space.undeformedLiftsDiffEquiv` is the bijection from the lifts onto the
  acting group given by the difference from a fixed lift.
* `AlgebraicGeometry.Space.undeformedLiftsAddAction` is the action itself, so that `θ +ᵥ c` is
  the source's `θ · c`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_undeformedLiftsDiff_eq`: **exactly one lift has a
  prescribed difference from a given lift**, which is [Stacks Project, Tag 04D0] in the form
  the torsor statement consumes.
* `AlgebraicGeometry.Space.undeformedLiftsDiff_vadd`: **the characterising equation of
  [Stacks Project, Tag 0CK6]** — the difference of the pair `(c, θ +ᵥ c)` is `θ`.
* `AlgebraicGeometry.Space.eq_vadd_of_undeformedLiftsDiff_eq`: that equation characterises
  `θ +ᵥ c`.
* `AlgebraicGeometry.Space.undeformedLiftsVAdd_bijective`: **simple transitivity** — over an
  ambient space carrying a lift, translation `θ ↦ θ +ᵥ c` is a bijection from the acting group
  onto the lifts.

## Implementation notes

**Why the undeformed case, and why it is the case that is true.**  [Stacks Project, Tag 061A]
cuts the lifts of a morphism along a thickening of the source out of the morphisms into a
thickened target `Y ⊆ Y'` by three conditions: (1) lying over the base, (2) restricting to the
given morphism on the thickening, and (3) inducing a prescribed map
`a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of conormal modules.  Only with (3) imposed are the lifts a torsor;
two lifts satisfying (1) and (2) alone can induce different maps of conormal modules, and the
set of such lifts is then a union of torsors rather than one.  The sheaf of lifts this
development carries — `AlgebraicGeometry.Space.liftSubfunctor` and
`AlgebraicGeometry.Space.liftsSubfunctor` — imposes (1) and (2) only, for the reason their
files record: without functoriality of the conormal module in the étale source, condition (3)
does not even cut out a subrule of the presheaf of morphisms.

**For an undeformed target condition (3) carries no information at all**, which is what Remark
[Stacks Project, Tag 061D] observes and what
`AlgebraicGeometry.Space.isZero_conormalModule_top` proves here: for `Y = Y'` the conormal
module `𝒞_{Y/Y'}` vanishes, so every map out of its inverse image is zero and (3) holds for
every `a'`.  So in that case the lifts cut out by (1) and (2) *are* the lifts of the source's
problem, and they *are* a torsor.  That is why this file is scoped to a target which is not
thickened: the statements below are false for a general target thickening and true, with no
further hypothesis, for an undeformed one.

**Everything geometric is already proved.**  The content is
`AlgebraicGeometry.Space.existsUnique_undeformedLiftDiff_eq` — [Stacks Project, Tag 04D0] for
an undeformed target — together with the additivity
`AlgebraicGeometry.Space.undeformedLiftDiff_add_undeformedLiftDiff` and the vanishing
`AlgebraicGeometry.Space.undeformedLiftDiff_self` of Equation [Stacks Project, Tag 0619].  What
this file adds is the repackaging into an action: the difference bijection, and then
`Deformation.addActionOfPairEquiv` and its companions, already in the library for the same
statement about lifts of objects of a deformation category.

**Why the lifts are taken relative to a morphism `a` and a structure morphism `β`, not relative
to a chosen lift.**  `AlgebraicGeometry.Space.existsUnique_undeformedLiftDiff_eq` is stated for
the lifts of the restriction `i ≫ c` of a *given* `c`, so its two conditions name `c`.  Read
that way the set of lifts and the acting group both change with the choice of `c`, and the
difference of two lifts would be typed in a group depending on one of them.  Taking the
restriction `a` and the structure morphism `β` as the data instead makes the set of lifts and
the acting group symmetric in the lifts, which is what a torsor statement needs; the existence
clause is transported to this form by
`AlgebraicGeometry.Space.exists_undeformedLiftDiff_eq_of_restriction_eq`, a substitution.

**What is not done here: the action on the sheaf of lifts.**  The statements below are for one
ambient space `X` at a time.  Making them an action of a sheaf of groups on the sheaf of lifts
over the small étale site of `X` additionally needs the restriction maps of the acting group —
that is, the comparison `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso` of
[Stacks Project, Tag 04CO] to be functorial in the étale source, which the "What is not proved"
section of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` records
as open — and the compatibility of
`AlgebraicGeometry.Space.undeformedLiftDiff` with étale restriction, which no statement in this
development carries.  Accordingly no restriction-compatibility clause is proved below; what
`Deformation.map_vadd_of_natural_difference` would need is exactly that compatibility.

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W V : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1)
  (a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W) (b : W ⟶ V)

/-! ### The existence clause, read at an arbitrary restriction -/

/-- **The existence half of [Stacks Project, Tag 04D0] for an undeformed target, read at an
arbitrary restriction.**  `AlgebraicGeometry.Space.exists_undeformedLiftDiff_eq` states it for
the lifts of the restriction `i ≫ c` of the given lift `c`; here the restriction is a morphism
`a` presented together with the equation `i ≫ c = a`, which is the form in which the two lifts
of a pair enter symmetrically.  The two statements are the same after substituting `a`. -/
theorem exists_undeformedLiftDiff_eq_of_restriction_eq (c : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = a)
    (θ : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z) :
    ∃ (c' : X ⟶ W) (h' : subspaceInclusion B S hS X Z ≫ c' = a) (hb : c ≫ b = c' ≫ b),
      undeformedLiftDiff B S hS Z hZ a b c c' h h' hb = θ := by
  subst h
  exact exists_undeformedLiftDiff_eq B S hS Z hZ b c θ

/-! ### The lifts and the group acting on them -/

variable (β : X ⟶ V)

/-- **A lift of `a : Z ⟶ W` over `V`**: a morphism `c : X ⟶ W` out of the ambient space of the
thickening whose restriction to the thickening is `a` and which lies over `V`, that is whose
composite with `b` is the given structure morphism `β`.  These are the conditions (1) and (2) of
[Stacks Project, Tag 061A]; the conormal condition (3) is vacuous here because the target is not
thickened, by `AlgebraicGeometry.Space.eq_zero_of_isZero_conormalModule_top`. -/
def IsUndeformedLift (c : X ⟶ W) : Prop :=
  subspaceInclusion B S hS X Z ≫ c = a ∧ c ≫ b = β

/-- The set of lifts of `a : Z ⟶ W` over `V` along the thickening `Z ⊂ X`. -/
abbrev UndeformedLifts := {c : X ⟶ W // IsUndeformedLift B S hS Z a b β c}

/-- **The group acting on the lifts**: the `𝒪_Z`-linear maps `a^*Ω_{W/V} ⟶ 𝒞_{Z/X}`.  These are
the global sections over `Z` of the sheaf
`AlgebraicGeometry.Space.liftActionSheaf` of [Stacks Project, Tag 061D]. -/
abbrev UndeformedLiftDerivations :=
  (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶ conormalModule B S hS X Z

/-- **The difference of two lifts**, the `𝒪_Z`-linear map `a^*Ω_{W/V} ⟶ 𝒞_{Z/X}` of
[Stacks Project, Tag 0618] with Equation [Stacks Project, Tag 0619].  Both lifts restrict to `a`
and both lie over `V`, which is exactly the data
`AlgebraicGeometry.Space.undeformedLiftDiff` consumes. -/
def undeformedLiftsDiff (c c' : UndeformedLifts B S hS Z a b β) :
    UndeformedLiftDerivations B S hS Z a b :=
  undeformedLiftDiff B S hS Z hZ a b c.1 c'.1 c.2.1 c'.2.1 (c.2.2.trans c'.2.2.symm)

/-- **A lift does not differ from itself.** -/
theorem undeformedLiftsDiff_self (c : UndeformedLifts B S hS Z a b β) :
    undeformedLiftsDiff B S hS Z hZ a b β c c = 0 :=
  undeformedLiftDiff_self B S hS Z hZ a b c.1 c.2.1

/-- **The differences along a chain of three lifts add up**, the cocycle identity. -/
theorem undeformedLiftsDiff_add_undeformedLiftsDiff
    (c₁ c₂ c₃ : UndeformedLifts B S hS Z a b β) :
    undeformedLiftsDiff B S hS Z hZ a b β c₁ c₂ +
        undeformedLiftsDiff B S hS Z hZ a b β c₂ c₃ =
      undeformedLiftsDiff B S hS Z hZ a b β c₁ c₃ :=
  undeformedLiftDiff_add_undeformedLiftDiff B S hS Z hZ a b _ _ _ _ _ _ _ _ _

/-- **The difference from a fixed lift is injective**, the uniqueness half of
[Stacks Project, Tag 04D0] for an undeformed target. -/
theorem undeformedLiftsDiff_injective (c : UndeformedLifts B S hS Z a b β) :
    Function.Injective (undeformedLiftsDiff B S hS Z hZ a b β c) := by
  intro c₁ c₂ heq
  exact Subtype.ext (undeformedLiftDiff_injective B S hS Z hZ a b _ _ _ _ _ _ _ _
    (c₁.2.2.trans c₂.2.2.symm) heq)

/-- **Every `𝒪_Z`-linear map is the difference from a given lift of some lift**, the existence
half of [Stacks Project, Tag 04D0] for an undeformed target. -/
theorem exists_undeformedLiftsDiff_eq (c : UndeformedLifts B S hS Z a b β)
    (θ : UndeformedLiftDerivations B S hS Z a b) :
    ∃ c' : UndeformedLifts B S hS Z a b β,
      undeformedLiftsDiff B S hS Z hZ a b β c c' = θ := by
  obtain ⟨c', h', hb, hθ⟩ :=
    exists_undeformedLiftDiff_eq_of_restriction_eq B S hS Z hZ a b c.1 c.2.1 θ
  exact ⟨⟨c', h', hb.symm.trans c.2.2⟩, hθ⟩

/-- **The difference from a fixed lift is a bijection onto the acting group**, which is
[Stacks Project, Tag 04D0] for an undeformed target read as simple transitivity. -/
theorem undeformedLiftsDiff_bijective (c : UndeformedLifts B S hS Z a b β) :
    Function.Bijective (undeformedLiftsDiff B S hS Z hZ a b β c) :=
  ⟨undeformedLiftsDiff_injective B S hS Z hZ a b β c,
    fun θ => exists_undeformedLiftsDiff_eq B S hS Z hZ a b β c θ⟩

/-- **[Stacks Project, Tag 04D0] for an undeformed target, in the form the torsor statement of
[Stacks Project, Tag 061C] consumes.**  For every `𝒪_Z`-linear map
`θ : a^*Ω_{W/V} ⟶ 𝒞_{Z/X}` there is exactly one lift whose difference from a given lift is
`θ`. -/
theorem existsUnique_undeformedLiftsDiff_eq (c : UndeformedLifts B S hS Z a b β)
    (θ : UndeformedLiftDerivations B S hS Z a b) :
    ∃! c' : UndeformedLifts B S hS Z a b β,
      undeformedLiftsDiff B S hS Z hZ a b β c c' = θ := by
  obtain ⟨c', hθ⟩ := exists_undeformedLiftsDiff_eq B S hS Z hZ a b β c θ
  exact ⟨c', hθ, fun c'' hc'' =>
    undeformedLiftsDiff_injective B S hS Z hZ a b β c (hc''.trans hθ.symm)⟩

/-- The bijection from the lifts onto the acting group given by the difference from a fixed
lift. -/
def undeformedLiftsDiffEquiv (c : UndeformedLifts B S hS Z a b β) :
    UndeformedLifts B S hS Z a b β ≃ UndeformedLiftDerivations B S hS Z a b :=
  Equiv.ofBijective _ (undeformedLiftsDiff_bijective B S hS Z hZ a b β c)

/-- The difference of two lifts, in the form which reconstructs an action: the bijection
replacing the second member of a pair of lifts by the difference of the two. -/
def undeformedLiftsPairEquiv :
    (UndeformedLifts B S hS Z a b β × UndeformedLifts B S hS Z a b β) ≃
      (UndeformedLifts B S hS Z a b β × UndeformedLiftDerivations B S hS Z a b) where
  toFun p := (p.1, undeformedLiftsDiff B S hS Z hZ a b β p.1 p.2)
  invFun p := (p.1, (undeformedLiftsDiffEquiv B S hS Z hZ a b β p.1).symm p.2)
  left_inv p := congrArg (Prod.mk p.1)
    ((undeformedLiftsDiffEquiv B S hS Z hZ a b β p.1).symm_apply_apply p.2)
  right_inv p := congrArg (Prod.mk p.1)
    ((undeformedLiftsDiffEquiv B S hS Z hZ a b β p.1).apply_symm_apply p.2)

/-! ### The action -/

/-- **The action of local derivations on the lifts into an undeformed target.**  The
`𝒪_Z`-linear maps `θ : a^*Ω_{W/V} ⟶ 𝒞_{Z/X}` act additively on the lifts of `a` over `V`: the
translate `θ +ᵥ c` is the source's `θ · c`, the unique lift whose difference from `c` is `θ`.

This is the action of [Stacks Project, Tag 061C] and the notation of
[Stacks Project, Tag 0CK6], for a target which is not thickened. -/
@[instance_reducible]
def undeformedLiftsAddAction :
    AddAction (UndeformedLiftDerivations B S hS Z a b) (UndeformedLifts B S hS Z a b β) :=
  Deformation.addActionOfPairEquiv (undeformedLiftsPairEquiv B S hS Z hZ a b β)
    (fun _ _ => rfl) (undeformedLiftsDiff_self B S hS Z hZ a b β)
    (undeformedLiftsDiff_add_undeformedLiftsDiff B S hS Z hZ a b β)

/-- **The characterising equation of [Stacks Project, Tag 0CK6].**  The difference of the pair
`(c, θ +ᵥ c)` is `θ`.  Through Equation [Stacks Project, Tag 0619] this says what the source's
notation means: the comorphisms of `c` and of `θ · c` differ by the derivation that equation
attaches to `θ`. -/
theorem undeformedLiftsDiff_vadd (c : UndeformedLifts B S hS Z a b β)
    (θ : UndeformedLiftDerivations B S hS Z a b) :
    letI := undeformedLiftsAddAction B S hS Z hZ a b β
    undeformedLiftsDiff B S hS Z hZ a b β c (θ +ᵥ c) = θ :=
  Deformation.pairEquiv_inverse_difference (undeformedLiftsPairEquiv B S hS Z hZ a b β)
    (fun _ _ => rfl) c θ

/-- **Simple transitivity, [Stacks Project, Tag 061C], for an undeformed target.**  Over an
ambient space carrying a lift `c`, translation `θ ↦ θ +ᵥ c` is a bijection from the acting group
onto the lifts; equivalently the action is free and transitive there. -/
theorem undeformedLiftsVAdd_bijective (c : UndeformedLifts B S hS Z a b β) :
    letI := undeformedLiftsAddAction B S hS Z hZ a b β
    Function.Bijective
      (fun θ : UndeformedLiftDerivations B S hS Z a b => θ +ᵥ c) :=
  Deformation.addActionOfPairEquiv_pointwiseBijective
    (undeformedLiftsPairEquiv B S hS Z hZ a b β) (fun _ _ => rfl) c

/-- **The characterising equation of [Stacks Project, Tag 0CK6] characterises the action.**  A
lift whose difference from `c` is `θ` is `θ +ᵥ c`. -/
theorem eq_vadd_of_undeformedLiftsDiff_eq (c c' : UndeformedLifts B S hS Z a b β)
    (θ : UndeformedLiftDerivations B S hS Z a b)
    (hd : undeformedLiftsDiff B S hS Z hZ a b β c c' = θ) :
    letI := undeformedLiftsAddAction B S hS Z hZ a b β
    c' = θ +ᵥ c :=
  let := undeformedLiftsAddAction B S hS Z hZ a b β
  Deformation.injective_difference_of_vadd (undeformedLiftsDiff B S hS Z hZ a b β)
    (undeformedLiftsDiff_vadd B S hS Z hZ a b β)
    (undeformedLiftsVAdd_bijective B S hS Z hZ a b β) c
    (hd.trans (undeformedLiftsDiff_vadd B S hS Z hZ a b β c θ).symm)

end AlgebraicGeometry.Space

end
