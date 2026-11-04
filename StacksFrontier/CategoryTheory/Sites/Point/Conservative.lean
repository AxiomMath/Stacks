module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Point.Map
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points is a local condition

Stacks 06UL: let `C` be a site and `{U_i}_{i ∈ I}` a family of objects such that

1. `∐ h_{U_i}^# → *` is a surjective map of sheaves, and
2. each localization `C/U_i` has enough points.

Then `C` has enough points.

Mathlib has the *converse* direction — if `(C, J)` has enough points then so does each
`(Over X, J.over X)` — in `Mathlib/CategoryTheory/Sites/Point/Over.lean`. This file
supplies the direction Stacks 06UL states.

## Rendering of hypothesis (1)

Hypothesis (1) is taken as `J.CoversTop Ui`, i.e. `Sieve.ofObjects Ui W ∈ J W` for every
object `W`. Unwound (`coversTop_iff_exists_covering` below) this says: every object `W` of
`C` admits a covering by objects each of which maps to some `U_i`. That is exactly what
surjectivity of `∐ h_{U_i}^# → *` says — the unique section of `*` over `W` lifts locally
into `∐ h_{U_i}^#` — and it is the form in which the Stacks proof consumes hypothesis (1)
("By assumption (1) there exists a covering `{W_a → W}` and morphisms `W_a → U_{i(a)}`").
Mathlib has no lemma identifying `CoversTop` with local surjectivity onto the terminal
sheaf, so that identification is not proved here.

## Proof

For each `i`, `Over.forget (U i)` is cocontinuous and continuous for `J.over (U i)` and
`J`, so Mathlib's `Point.map` pushes a point of `C/U_i` forward to a point of `C`, and
`Point.sheafFiberMapIso` identifies the pushed-forward stalk functor with
`J.overPullback _ (U i) ⋙` the original stalk functor. Hence if the pushed-forward stalks
of a map of sheaves `f` are all isomorphisms, conservativity on each `C/U_i` makes
`(J.overPullback _ (U i)).map f` an isomorphism for every `i`, and
`Sheaf.isIso_of_coversTop` — which is where hypothesis (1) is used — makes `f` an
isomorphism.

The smallness side condition `Small.{w} I` is forced by Mathlib's `HasEnoughPoints`, whose
conservative family is required to be `w`-small.
-/

@[expose] public section

namespace CategoryTheory

open GrothendieckTopology Limits

universe w v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  {I : Type*} (Ui : I → C) (P : ∀ i, ObjectProperty (Point.{w} (J.over (Ui i))))

omit [LocallySmall.{w} C] in
/-- Hypothesis (1) of Stacks 06UL, unwound: `J.CoversTop Ui` says that every object `W` of
`C` has a covering sieve all of whose members have source admitting a morphism to some
`U_i`. -/
theorem GrothendieckTopology.coversTop_iff_exists_covering :
    J.CoversTop Ui ↔ ∀ W : C, ∃ S ∈ J W,
      ∀ ⦃V : C⦄ (g : V ⟶ W), S.arrows g → ∃ i, Nonempty (V ⟶ Ui i) := by
  constructor
  · exact fun h W ↦ ⟨_, h W, fun _ _ hg ↦ hg⟩
  · intro h W
    obtain ⟨S, hS, hS'⟩ := h W
    exact J.superset_covering (fun _ g hg ↦ hS' g hg) hS

/-- The family of points of `C` obtained by pushing forward, along `Over.forget (U i)`,
the points of `C/U_i` belonging to `P i`. -/
def GrothendieckTopology.pointsOfLocalizations : ObjectProperty (Point.{w} J) :=
  .ofObj (fun (ψ : Σ i : I, (P i).FullSubcategory) ↦ ψ.2.obj.map (Over.forget (Ui ψ.1)) J)

/-- The pushforward along `Over.forget (U i)` of a point of `C/U_i` lying in `P i` belongs to
`pointsOfLocalizations`. -/
lemma GrothendieckTopology.mem_pointsOfLocalizations (i : I) (Ψ : (P i).FullSubcategory) :
    GrothendieckTopology.pointsOfLocalizations Ui P (Ψ.obj.map (Over.forget (Ui i)) J) :=
  ObjectProperty.ofObj_apply
    (fun (ψ : Σ i : I, (P i).FullSubcategory) ↦ ψ.2.obj.map (Over.forget (Ui ψ.1)) J) ⟨i, Ψ⟩

/-- `pointsOfLocalizations` is `w`-small as soon as the index type `I` and each family `P i`
are: it is indexed by the sigma type of the `P i`. -/
instance [Small.{w} I] [∀ i, ObjectProperty.Small.{w} (P i)] :
    ObjectProperty.Small.{w} (GrothendieckTopology.pointsOfLocalizations Ui P) := by
  unfold pointsOfLocalizations
  infer_instance

/-- **Stacks 06UL**, the conservativity step. If the `U_i` cover the final object and each
`P i` is a conservative family of points of `C/U_i`, then the pushed-forward family
`pointsOfLocalizations` is a conservative family of points of `C`. -/
@[stacks 06UL, sga "4 IV 6.7.4" "second assertion", sga "4 IV 6.7.3" "converse direction"]
theorem ObjectProperty.IsConservativeFamilyOfPoints.of_coversTop
    (hU : J.CoversTop Ui) (hP : ∀ i, (P i).IsConservativeFamilyOfPoints) :
    (GrothendieckTopology.pointsOfLocalizations Ui P).IsConservativeFamilyOfPoints := by
  refine ⟨⟨fun {F G} f hf ↦ Sheaf.isIso_of_coversTop hU (fun i ↦ ?_)⟩⟩
  have : ∀ Ψ : (P i).FullSubcategory,
      IsIso ((Ψ.obj.sheafFiber (A := Type w)).map ((J.overPullback (Type w) (Ui i)).map f)) := by
    intro Ψ
    have h := hf ⟨Ψ.obj.map (Over.forget (Ui i)) J,
      GrothendieckTopology.mem_pointsOfLocalizations Ui P i Ψ⟩
    rwa [NatIso.isIso_map_iff
      (Ψ.obj.sheafFiberMapIso (Over.forget (Ui i)) J (A := Type w))] at h
  exact ((hP i).jointlyReflectIsomorphisms_type).isIso
    ((J.overPullback (Type w) (Ui i)).map f)

/-- **Stacks 06UL.** Let `C` be a site and `{U_i}_{i ∈ I}` a family of objects such that
the `U_i` cover the final object (hypothesis (1), see the module docstring) and each
localization `C/U_i` has enough points (hypothesis (2)). Then `C` has enough points. -/
@[stacks 06UL, sga "4 IV 6.7.3" "converse", sga "4 IV 6.7.4" "second assertion"]
theorem GrothendieckTopology.hasEnoughPoints_of_coversTop [Small.{w} I]
    (hU : J.CoversTop Ui) [∀ i, HasEnoughPoints.{w} (J.over (Ui i))] :
    HasEnoughPoints.{w} J := by
  choose P hPsmall hP using fun i ↦
    HasEnoughPoints.exists_objectProperty (J.over (Ui i))
  have : ∀ i, ObjectProperty.Small.{w} (P i) := hPsmall
  exact ⟨GrothendieckTopology.pointsOfLocalizations Ui P, inferInstance,
    ObjectProperty.IsConservativeFamilyOfPoints.of_coversTop Ui P hU hP⟩

end CategoryTheory
