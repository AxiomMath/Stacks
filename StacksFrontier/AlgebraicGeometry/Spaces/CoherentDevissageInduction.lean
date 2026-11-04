module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverAlgClosedFieldConstant
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The induction principle for coherent modules on a Noetherian algebraic space

Stacks 07US: a property of coherent modules on a Noetherian algebraic space `X` which is closed
under extensions and holds for every direct image `i_*I` of a quasi-coherent sheaf of ideals on a
reduced closed subspace `i : Z → X` with `|Z|` irreducible holds for every coherent module.

As stated in the source the lemma fails when `|X|` is empty: the property that never holds then
satisfies both hypotheses, the second one vacuously, and fails for the zero module.  The
statement below adds the alternative "`X` has a point, or the property holds for zero modules",
which is automatic when `X` has a point.

## Main results

* `AlgebraicGeometry.Space.isReducedIrreducible_reducedClosedSubspace`: the reduced closed
  subspace on an irreducible closed set of points is reduced with irreducible space of points.
* `AlgebraicGeometry.Space.property_of_isZero_of_nonempty`: on an algebraic space with a point,
  the two hypotheses of Stacks 07US give the property for every zero module.
* `AlgebraicGeometry.Space.property_of_ideal_pushforward_and_extensions`: Stacks 07US.
* `AlgebraicGeometry.Space.exists_isNoetherian_not_forall_property`: the statement of Stacks 07US
  without the alternative is false, at the Noetherian algebraic space with no points.

## References

* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reduced closed subspaces with irreducible space of points -/

/-- The reduced closed subspace on an irreducible closed set of points is reduced with
irreducible space of points. -/
theorem isReducedIrreducible_reducedClosedSubspace (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) (closed : IsClosed T) (irreducible : IsIrreducible T) :
    IsReducedIrreducible B S hS (reducedClosedSubspace B S hS X.1 X.2 T closed) := by
  have hWc := isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 T closed
  have hrange := range_pointsMap_ι_reducedClosedSubspace B S hS X.1 X.2 T closed
  refine ⟨hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X.1 X.2 T closed, ?_⟩
  have hpre := preirreducibleSpace_points_of_isPreirreducible_range_pointsMap B S hS X.2 _
    (isImmersion_of_isClosedImmersion B S hS hWc.2) (by rw [hrange]; exact irreducible.2)
  obtain ⟨x, hx⟩ := irreducible.1
  rw [← hrange] at hx
  obtain ⟨y, -⟩ := hx
  exact { toPreirreducibleSpace := hpre, toNonempty := ⟨y⟩ }

/-- An algebraic space with a point has a reduced closed subspace with irreducible space of
points. -/
theorem exists_isReducedIrreducible (X : AlgebraicSpaces B S hS) (x : points B S hS X.1) :
    ∃ (Z : Subfunctor X.1) (_ : IsClosedSubspace B S hS Z), IsReducedIrreducible B S hS Z :=
  ⟨_, isClosedSubspace_reducedClosedSubspace B S hS X.1 X.2 (closure {x}) isClosed_closure,
    isReducedIrreducible_reducedClosedSubspace B S hS X (closure {x}) isClosed_closure
      isIrreducible_singleton.closure⟩

/-- A subfunctor of an algebraic space with no points is not reduced with irreducible space of
points. -/
theorem not_isReducedIrreducible_of_isEmpty (X : AlgebraicSpaces B S hS)
    (empty : IsEmpty (points B S hS X.1)) (Z : Subfunctor X.1) :
    ¬ IsReducedIrreducible B S hS Z := by
  rintro ⟨-, hirr⟩
  obtain ⟨z⟩ := hirr.toNonempty
  exact empty.false (pointsMap B S hS Z.toFunctor Z.ι z)

/-! ### The property on zero modules -/

/-- On an algebraic space `X` with a point, a property of modules which is closed under
extensions of coherent modules and holds for every direct image `i_*I` of a quasi-coherent sheaf
of ideals on a reduced closed subspace `i : Z → X` with `|Z|` irreducible holds for every zero
module. -/
theorem property_of_isZero_of_nonempty (X : AlgebraicSpaces B S hS) (x : points B S hS X.1)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (extensions : ClosedUnderCoherentExtensions B S hS X P)
    (idealPushforward : ∀ (Z : Subfunctor X.1) (closed : IsClosedSubspace B S hS Z),
      IsReducedIrreducible B S hS Z →
      ∀ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS closed),
        P ((modulePushforward B S hS (closedSubfunctorι B S hS closed)).obj
          I.1.toSheafOfModules))
    (M : Modules.{u, u} B S hS X.1 X.2) (zero : IsZero M) : P M := by
  obtain ⟨Z, closed, hred⟩ := exists_isReducedIrreducible B S hS X x
  let I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS closed) :=
    ⟨⊥, SheafOfModules.IsQuasicoherentOnSite.of_isZero
      (SheafOfModules.Submodule.isZero_toSheafOfModules_bot _)⟩
  have hN := isZero_modulePushforward_of_eq_bot B S hS X closed I rfl
  have hNcoh := IsCoherent.of_isZero B S hS X.1 X.2 hN
  exact extensions (ShortComplex.mk (0 : _ ⟶ M) (0 : M ⟶ _) comp_zero)
    (.mk' (ShortComplex.exact_of_isZero_X₂ _ zero) (hN.mono _) (hN.epi _)) hNcoh
    (IsCoherent.of_isZero B S hS X.1 X.2 zero) hNcoh (idealPushforward Z closed hred I)
    (idealPushforward Z closed hred I)

/-! ### Stacks 07US -/

/-- Let `X` be a Noetherian algebraic space over `S` and let `P` be a property of `𝒪_X`-modules
such that

1. for a short exact sequence `0 → F₁ → F → F₂ → 0` of coherent modules, if `F₁` and `F₂` have
   `P` then so does `F`;
2. for every reduced closed subspace `i : Z → X` with `|Z|` irreducible and every quasi-coherent
   sheaf of ideals `I ⊆ 𝒪_Z`, `P` holds for `i_*I`.

Suppose moreover that `X` has a point or that `P` holds for every zero module.  Then `P` holds
for every coherent module on `X`.

Without the alternative the statement fails when `|X|` is empty
(`AlgebraicGeometry.Space.exists_isNoetherian_not_forall_property`). -/
@[stacks 07US]
theorem property_of_ideal_pushforward_and_extensions (X : AlgebraicSpaces B S hS)
    (noetherian : IsNoetherian B S hS B.contains_terminal X.1)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (nonempty_or_zero : Nonempty (points B S hS X.1) ∨
      ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (extensions : ClosedUnderCoherentExtensions B S hS X P)
    (idealPushforward : ∀ (Z : Subfunctor X.1) (closed : IsClosedSubspace B S hS Z),
      IsReducedIrreducible B S hS Z →
      ∀ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS closed),
        P ((modulePushforward B S hS (closedSubfunctorι B S hS closed)).obj
          I.1.toSheafOfModules))
    (M : Modules.{u, u} B S hS X.1 X.2) (coherent : IsCoherent B S hS X.1 X.2 M) : P M :=
  property_of_forall_hasIdealDevissage B S hS X
    (fun N hN => hasIdealDevissage_of_isCoherent B S hS B.contains_terminal X noetherian N hN) P
    (nonempty_or_zero.elim (fun h ↦ property_of_isZero_of_nonempty B S hS X h.some P extensions
      idealPushforward) id) extensions idealPushforward M coherent

/-! ### The source's statement fails on the empty algebraic space -/

/-- An algebraic space has a coherent module (a zero module). -/
private theorem exists_isCoherent (X : AlgebraicSpaces B S hS) :
    ∃ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N := by
  obtain ⟨N, hN⟩ := HasZeroObject.zero (C := Modules.{u, u} B S hS X.1 X.2)
  exact ⟨N, IsCoherent.of_isZero B S hS X.1 X.2 hN⟩

/-- On an algebraic space with no points, the property that never holds satisfies hypotheses
(1) and (2) of Stacks 07US, the latter vacuously, and fails for a coherent module. -/
theorem not_forall_property_of_isEmpty (X : AlgebraicSpaces B S hS)
    (empty : IsEmpty (points B S hS X.1)) :
    ClosedUnderCoherentExtensions B S hS X (fun _ => False) ∧
      (∀ (Z : Subfunctor X.1) (closed : IsClosedSubspace B S hS Z),
        IsReducedIrreducible B S hS Z →
        ∀ _ : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS closed), False) ∧
      ¬ ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M → False := by
  refine ⟨fun _ _ _ _ _ h _ => h, fun Z _ hred _ =>
    not_isReducedIrreducible_of_isEmpty B S hS X empty Z hred, fun h => ?_⟩
  obtain ⟨N, hN⟩ := exists_isCoherent B S hS X
  exact h N hN

/-- The object of the big fppf site over `S` whose underlying scheme is empty. -/
abbrev emptyOver : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (B.contains_of_isEmpty (Z := (∅ : Scheme.{u})) inferInstance)
    (Scheme.emptyTo S)

/-- There is a Noetherian algebraic space over `S` with no points. -/
theorem exists_isNoetherian_isEmpty_points :
    ∃ X : AlgebraicSpaces B S hS,
      IsNoetherian B S hS B.contains_terminal X.1 ∧ IsEmpty (points B S hS X.1) := by
  let E := emptyOver B S hS
  have hE : IsEmpty ((BigFppfOver.toScheme B S hS).obj E) :=
    inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
  refine ⟨⟨yoneda.obj E, isAlgebraicSpace_yoneda B S hS E⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact isQuasiCompactSpace_yoneda B S hS E inferInstance
  · exact isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj E)
      B.contains_terminal ⟨E, inferInstance, ⟨Functor.RepresentableBy.yoneda E⟩⟩
  · exact ⟨E, 𝟙 _, presheaf_surjective_id B S hS E, presheaf_etale_id B S hS E,
      inferInstanceAs (IsLocallyNoetherian (∅ : Scheme.{u}))⟩
  · exact (pointsEquivScheme B S hS E).isEmpty

/-- There are a Noetherian algebraic space `X` over `S` and a property `P` of `𝒪_X`-modules
satisfying hypotheses (1) and (2) of Stacks 07US which fails for a coherent module. -/
theorem exists_isNoetherian_not_forall_property :
    ∃ (X : AlgebraicSpaces B S hS) (P : Modules.{u, u} B S hS X.1 X.2 → Prop),
      IsNoetherian B S hS B.contains_terminal X.1 ∧
      ClosedUnderCoherentExtensions B S hS X P ∧
      (∀ (Z : Subfunctor X.1) (closed : IsClosedSubspace B S hS Z),
        IsReducedIrreducible B S hS Z →
        ∀ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS closed),
          P ((modulePushforward B S hS (closedSubfunctorι B S hS closed)).obj
            I.1.toSheafOfModules)) ∧
      ∃ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M ∧ ¬ P M := by
  obtain ⟨X, noetherian, empty⟩ := exists_isNoetherian_isEmpty_points B S hS
  obtain ⟨extensions, idealPushforward, -⟩ := not_forall_property_of_isEmpty B S hS X empty
  obtain ⟨N, hN⟩ := exists_isCoherent B S hS X
  exact ⟨X, fun _ => False, noetherian, extensions, idealPushforward, N, hN, not_false⟩

end AlgebraicGeometry.Space

end
