module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeComparisonComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCompositeSections

/-!
# The comparison of the two iterated derived pushforwards, read on derived sections over an open

For a commutative square of ringed spaces
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
`Stacks.Cohomology.DerivedBaseChange.Mate.derivedPushforwardComparisonSquare` compares the two
routes from `X'` to `S`, `Rf_*(Rg'_* M) ⟶ Rg_*(Rf'_* M)`. Composing that comparison with derived
sections over an open `V ⊆ S` makes both of its ends computable by [Stacks, Tag 0D5W]: derived
sections over `V` of an iterated derived pushforward are derived sections over the iterated
inverse image, and the two iterated inverse images of `V` are **the same open of `X'`**, because
`g' ≫ f = f' ≫ g`.

This file proves that the comparison, so read, is exactly the transport along that equality: the
square contributes nothing to derived sections beyond the identification of the two names of one
open.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.lerayComparison_comp_whiskerRight_eqToHom`: the Leray
  comparison carries the transport between the derived pushforwards along two equal morphisms to
  the transport between the derived sections over their inverse images.
* `Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_comp_leray`: **the
  comparison of the two iterated derived pushforwards, on derived sections over `V`, is the
  transport along `g' ≫ f = f' ≫ g`.** Stated through the composition isomorphism of
  [Stacks, Tag 079W] on either side, which is the shape
  `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_comp` produces.
* `Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_comp_lerayComposite`:
  the same with each side's Leray comparison split into the relative comparison for the upper
  morphism followed by the comparison for the lower one, which is the form in which a consumer
  meets derived sections over the two intermediate opens `f⁻¹V` and `g⁻¹V`.
* `Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_app_comp_leray`: the
  first of those read at an object of the unbounded derived category.

## Implementation notes

*The transport cannot be removed.* `Rg'_* ⋙ Rf_*` is compared with `R(g' ≫ f)_*` and
`Rf'_* ⋙ Rg_*` with `R(f' ≫ g)_*`; the two composites `g' ≫ f` and `f' ≫ g` are equal but not
syntactically so, and the same `CategoryTheory.eqToHom` that
`derivedPushforwardComparisonSquare_natTrans_eq_compIso` carries on the pushforward side appears
here on the sections side. It is identified by substituting the equation, which is why
`lerayComparison_comp_whiskerRight_eqToHom` is stated at an arbitrary equality of morphisms
rather than at `sq`: after a substitution nothing about the transport has to be decided.

*Nothing is assumed of the square beyond its commutativity*, and nothing of `V`: both
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_comp` and
`derivedPushforwardComparisonSquare_natTrans_eq_compIso` are unconditional.

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.DerivedPullback.Composition

namespace Stacks.Cohomology.DerivedBaseChange

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section Canonical

variable {X' X S' S : RingedSpace.{u, u}}

/-- **A cancelling pair in the middle of a four-fold composite.** If `y ≫ z = 𝟙`, then
`(x ≫ y) ≫ z ≫ t` is `x ≫ t`. Stated at variables of an abstract category — which the functor
category the whiskered comparisons live in is — because that is where the reassociation is free.

It is not decoration. Performing the same reassociation on the concrete spelling, by `rw` with
either the whiskered composition isomorphism as an explicit argument to
`CategoryTheory.Category.assoc` or `reassoc_of%` at the cancellation, is a deterministic
`isDefEq` timeout: both sides mention iterated derived functors of ringed spaces, and the
unifier has to decide them. `BaseChangeComparisonComposition.lean` keeps a `private` sibling of
this shape for the same measurement, and the two cannot be shared — that one is `private`, and
nothing lower in the import order holds either. -/
private theorem comp_comp_cancel {C : Type*} [Category* C] {A B D E : C} (x : A ⟶ B)
    {y : B ⟶ D} {z : D ⟶ B} (h : y ≫ z = 𝟙 B) (t : B ⟶ E) : (x ≫ y) ≫ z ≫ t = x ≫ t := by
  rw [Category.assoc, ← Category.assoc y z t, h, Category.id_comp]

/-- **A two-factor head of a composite replaced by another, at variables.** From `x ≫ y = u ≫ v`
one gets `x ≫ y ≫ t = u ≫ v ≫ t`. Stated at variables of an abstract category for the reason
recorded at `comp_comp_cancel`. -/
private theorem comp_seg_eq {C : Type*} [Category* C] {A A' B D E : C} {x : A ⟶ B} {y : B ⟶ D}
    {u : A ⟶ A'} {v : A' ⟶ D} (h : x ≫ y = u ≫ v) (t : D ⟶ E) :
    x ≫ y ≫ t = u ≫ v ≫ t := by
  rw [← Category.assoc, h, Category.assoc]

/-- **The Leray comparison carries a transport between derived pushforwards to a transport between
derived sections.** For two equal morphisms `a = b : X' ⟶ S` of ringed spaces and an open
`V ⊆ S`, the Leray comparison of [Stacks, Tag 0D5W] at `a`, followed by derived sections over `V`
of the transport `Ra_* ⟶ Rb_*`, is the transport `RΓ(a⁻¹V, -) ⟶ RΓ(b⁻¹V, -)` followed by the
Leray comparison at `b`.

Both transports are `CategoryTheory.eqToHom` of the equality applied to a functor, so the
statement is proved by substituting the equation, after which both are identities. -/
theorem lerayComparison_comp_whiskerRight_eqToHom {a b : X' ⟶ S} (hab : a = b)
    (V : Opens S.carrier) :
    lerayComparison a V ≫
        Functor.whiskerRight
          (eqToHom (congrArg (fun k : X' ⟶ S => derivedPushforward k) hab))
          (derivedSectionsOverOpen S V) =
      eqToHom (congrArg (fun k : X' ⟶ S => derivedPreimageSections k V) hab) ≫
        lerayComparison b V := by
  subst hab
  simp

/-- **The transport between the derived sections over the inverse images of two equal morphisms,
read at an object.** For two equal morphisms `a = b : X' ⟶ S` of ringed spaces, an open `V ⊆ S`
and an object `M` of `D(𝒪_{X'})`, the transport `RΓ(a⁻¹V, -) ⟶ RΓ(b⁻¹V, -)` evaluated at `M` is
the transport `RΓ(a⁻¹V, M) ⟶ RΓ(b⁻¹V, M)`. Substituting the equation makes both identities. -/
theorem eqToHom_derivedPreimageSections_app {a b : X' ⟶ S} (hab : a = b) (V : Opens S.carrier)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) :
    (eqToHom (congrArg (fun k : X' ⟶ S => derivedPreimageSections k V) hab)).app M =
      eqToHom (congrArg (fun k : X' ⟶ S => (derivedPreimageSections k V).obj M) hab) := by
  subst hab
  simp

/-- **An equation of natural transformations with a leading transport, read at an object.** From
`α = eqToHom h ≫ β` one gets `α.app M = eqToHom _ ≫ β.app M`, the transport evaluated at `M`. -/
private theorem app_eq_eqToHom_comp_app {C D : Type*} [Category* C] [Category* D]
    {F F' G : C ⥤ D} {α : F ⟶ G} {β : F' ⟶ G} {h : F = F'} (H : α = eqToHom h ≫ β) (M : C) :
    α.app M = eqToHom (congrArg (fun K : C ⥤ D => K.obj M) h) ≫ β.app M := by
  subst h
  simp [H]

variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
  (V : Opens S.carrier)

/-- **The comparison of the two iterated derived pushforwards, on derived sections over an open,
is the transport along the square.** For a commutative square of ringed spaces
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
and an open `V ⊆ S`, the Leray comparison of [Stacks, Tag 0D5W] for `g' ≫ f`, read through the
composition isomorphism of [Stacks, Tag 079W], followed by derived sections over `V` of the
comparison `Rg'_* ⋙ Rf_* ⟶ Rf'_* ⋙ Rg_*`, is the transport
`RΓ((g' ≫ f)⁻¹V, -) ⟶ RΓ((f' ≫ g)⁻¹V, -)` followed by the same route down the other side.

So on derived sections the comparison of the two iterated derived pushforwards says nothing
beyond `(g' ≫ f)⁻¹V = (f' ≫ g)⁻¹V`. There is no hypothesis on the square beyond `sq`, none on
`V` and none on the object.

The proof is `derivedPushforwardComparisonSquare_natTrans_eq_compIso` — the comparison is the two
composition isomorphisms of [Stacks, Tag 079W] with the transport between them — followed by the
cancellation of the first of those against the composition isomorphism the left-hand side already
carries, and by `lerayComparison_comp_whiskerRight_eqToHom` on what is left. -/
theorem derivedPushforwardComparisonSquare_comp_leray :
    (lerayComparison (g' ≫ f) V ≫
          Functor.whiskerRight (derivedPushforwardCompIso g' f).inv
            (derivedSectionsOverOpen S V)) ≫
        Functor.whiskerRight
          (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
              (derivedAdjunction g) (derivedAdjunction g')
              (derivedPullbackCompIsoLeft g' f' f g sq)
              (derivedPullbackCompIsoCanonical g' f))
          (derivedSectionsOverOpen S V) =
      eqToHom (congrArg (fun k : X' ⟶ S => derivedPreimageSections k V) sq) ≫
        lerayComparison (f' ≫ g) V ≫
          Functor.whiskerRight (derivedPushforwardCompIso f' g).inv
            (derivedSectionsOverOpen S V) := by
  have hcancel :
      Functor.whiskerRight (derivedPushforwardCompIso g' f).inv
            (derivedSectionsOverOpen S V) ≫
          Functor.whiskerRight (derivedPushforwardCompIso g' f).hom
            (derivedSectionsOverOpen S V) =
        𝟙 _ :=
    (Functor.isoWhiskerRight (derivedPushforwardCompIso g' f)
      (derivedSectionsOverOpen S V)).inv_hom_id
  rw [derivedPushforwardComparisonSquare_natTrans_eq_compIso g' f' f g sq,
    Functor.whiskerRight_comp, Functor.whiskerRight_comp]
  exact (comp_comp_cancel _ hcancel _).trans
    (comp_seg_eq (lerayComparison_comp_whiskerRight_eqToHom sq V) _)

/-- **The same identity with each side's Leray comparison split at the intermediate open.** The
left-hand route is the relative Leray comparison of
`Stacks.Cohomology.DerivedSectionsLeray.lerayCompositeComparison` for `g'` over `f⁻¹V`, followed
by `Rg'_*` of the Leray comparison for `f` at `V`; the right-hand route is the same with
`(f', g)` in place of `(g', f)`, so with `g⁻¹V` as the intermediate open. The comparison of the
two iterated derived pushforwards carries the first to the second, up to the transport along
`(g' ≫ f)⁻¹V = (f' ≫ g)⁻¹V`.

This is the form a consumer meets: it is the shape in which derived sections over the two
intermediate opens `f⁻¹V` and `g⁻¹V` occur, which is where the two halves of conclusion (c) of
[Stacks, Tag 0EX3] are computed. It is
`derivedPushforwardComparisonSquare_comp_leray` with
`Stacks.Cohomology.DerivedSectionsLeray.lerayComparison_comp` substituted on either side. -/
theorem derivedPushforwardComparisonSquare_comp_lerayComposite :
    (lerayCompositeComparison g' f V ≫
          Functor.whiskerLeft (derivedPushforward g') (lerayComparison f V)) ≫
        Functor.whiskerRight
          (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
              (derivedAdjunction g) (derivedAdjunction g')
              (derivedPullbackCompIsoLeft g' f' f g sq)
              (derivedPullbackCompIsoCanonical g' f))
          (derivedSectionsOverOpen S V) =
      eqToHom (congrArg (fun k : X' ⟶ S => derivedPreimageSections k V) sq) ≫
        lerayCompositeComparison f' g V ≫
          Functor.whiskerLeft (derivedPushforward f') (lerayComparison g V) := by
  rw [← lerayComparison_comp g' f V, ← lerayComparison_comp f' g V]
  exact derivedPushforwardComparisonSquare_comp_leray g' f' f g sq V

/-- **The comparison on derived sections over an open, read at an object.**
`derivedPushforwardComparisonSquare_comp_leray` at an object `M` of the unbounded derived
category of `X'`, with the transport pushed onto the object.

The two sides are morphisms `RΓ((g' ≫ f)⁻¹V, M) ⟶ RΓ(V, Rf'_*(Rg_*M))` in the derived category of
modules over the functions on `V`; nothing is assumed of the square beyond `sq`, of `V` or of
`M`. -/
theorem derivedPushforwardComparisonSquare_app_comp_leray
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) :
    ((lerayComparison (g' ≫ f) V).app M ≫
          (derivedSectionsOverOpen S V).map ((derivedPushforwardCompIso g' f).inv.app M)) ≫
        (derivedSectionsOverOpen S V).map
          ((Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
            (derivedAdjunction g) (derivedAdjunction g')
            (derivedPullbackCompIsoLeft g' f' f g sq)
            (derivedPullbackCompIsoCanonical g' f)).app M) =
      eqToHom (congrArg (fun k : X' ⟶ S => (derivedPreimageSections k V).obj M) sq) ≫
        (lerayComparison (f' ≫ g) V).app M ≫
          (derivedSectionsOverOpen S V).map ((derivedPushforwardCompIso f' g).inv.app M) :=
  app_eq_eqToHom_comp_app (derivedPushforwardComparisonSquare_comp_leray g' f' f g sq V) M

/-- **The split form of the comparison on derived sections over an open, read at an object.**
`derivedPushforwardComparisonSquare_comp_lerayComposite` at an object `M` of the unbounded derived
category of `X'`, with the transport pushed onto the object: the relative Leray comparison for
`g'` over `f⁻¹V` at `M`, then the Leray comparison for `f` at `V` at `Rg'_* M`, then derived
sections over `V` of the comparison of the two iterated derived pushforwards, is the transport
`RΓ((g' ≫ f)⁻¹V, M) ⟶ RΓ((f' ≫ g)⁻¹V, M)`, the relative Leray comparison for `f'` over `g⁻¹V`,
and the Leray comparison for `g` at `V` at `Rf'_* M`.

Nothing is assumed of the square beyond `sq`, of `V` or of `M`. -/
theorem derivedPushforwardComparisonSquare_app_comp_lerayComposite
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))) :
    ((lerayCompositeComparison g' f V).app M ≫
          (lerayComparison f V).app ((derivedPushforward g').obj M)) ≫
        (derivedSectionsOverOpen S V).map
          ((Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
            (derivedAdjunction g) (derivedAdjunction g')
            (derivedPullbackCompIsoLeft g' f' f g sq)
            (derivedPullbackCompIsoCanonical g' f)).app M) =
      eqToHom (congrArg (fun k : X' ⟶ S => (derivedPreimageSections k V).obj M) sq) ≫
        (lerayCompositeComparison f' g V).app M ≫
          (lerayComparison g V).app ((derivedPushforward f').obj M) :=
  app_eq_eqToHom_comp_app (derivedPushforwardComparisonSquare_comp_lerayComposite g' f' f g sq V)
    M

end Canonical

end

end Stacks.Cohomology.DerivedBaseChange

end
