module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Recompletion

/-!
# Recompletion of an affine formal algebraic space: the countably indexed, adic\* and
Noetherian clauses

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an *affine* formal algebraic
space over `S`, let `i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed.
For the completion `X_{/T}` of `X` along `T`:

3. if `|X_red| \ T` is quasi-compact and `X` is countably indexed, so is `X_{/T}`;
4. if `|X_red| \ T` is quasi-compact and `X` is adic\*, so is `X_{/T}`;
5. if `X` is Noetherian, so is `X_{/T}`.

Quasi-compactness of `|X_red| \ T` is stated as compactness of `Tᶜ` for the point topology
`AlgebraicGeometry.Space.pointTopologyULift` of a reduction.

## Main definitions

* `AlgebraicGeometry.FormalSpace.CompletionOfCountablyIndexedIsCountableSpf`: the completion of a
  countably indexed space along a closed subset with quasi-compact complement has a countable
  weak presentation.
* `AlgebraicGeometry.FormalSpace.CompletionOfAdicStarIsCompletionAlongFGIdeal`: the completion of
  an adic\* space along a closed subset with quasi-compact complement is the completion of an
  affine scheme along a finitely generated ideal.
* `AlgebraicGeometry.FormalSpace.CompletionOfNoetherianIsCompletionAlongNoetherianIdeal`: the
  completion of a Noetherian space along a closed subset is the completion of a Noetherian affine
  scheme along an ideal.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_completionAlong`: clause (3), given
  `CompletionOfCountablyIndexedIsCountableSpf`.
* `AlgebraicGeometry.FormalSpace.isAdicStar_completionAlong`: clause (4), given
  `CompletionOfAdicStarIsCompletionAlongFGIdeal` and the set-theoretic condition on `X_{/T}`.
* `AlgebraicGeometry.FormalSpace.isNoetherian_completionAlong`: clause (5), given
  `CompletionOfNoetherianIsCompletionAlongNoetherianIdeal` and the set-theoretic condition on
  `X_{/T}`.

## References

* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0GVQ](https://stacks.math.columbia.edu/tag/0GVQ)
* [Stacks Project, Tag 0GVV](https://stacks.math.columbia.edu/tag/0GVV)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport along an isomorphism -/

/-- Being an affine formal algebraic space transports along an isomorphism of fppf sheaves
once the set-theoretic condition is known on the source. -/
private theorem isAffineFormalAlgebraicSpace_of_iso_hset {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y) :
    IsAffineFormalAlgebraicSpace B S hS X := by
  obtain ⟨-, I, pre, hne, hdir, D, hD, ⟨k⟩⟩ := hY
  exact ⟨hset, I, pre, hne, hdir, D, hD, ⟨e ≪≫ k⟩⟩

/-- Being a McQuillan affine formal algebraic space transports along an isomorphism of fppf
sheaves once the set-theoretic condition is known on the source. -/
private theorem hasSomeSurjectivePresentation_of_iso_hset {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (hY : HasSomeSurjectivePresentation B S hS Y) :
    HasSomeSurjectivePresentation B S hS X := by
  obtain ⟨haff, I, pre, hne, hdir, D, hD, ⟨k⟩, hsurj⟩ := hY
  exact ⟨isAffineFormalAlgebraicSpace_of_iso_hset B S hS e hset haff, I, pre, hne, hdir, D, hD,
    ⟨e ≪≫ k⟩, hsurj⟩

/-- A ring presenting an fppf sheaf presents any sheaf isomorphic to it. -/
private theorem isPresentingRing_of_iso_hset {X Y : FppfSheaf B S hS} (e : X ≅ Y) (A : Type u)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hY : IsPresentingRing B S hS A Y) : IsPresentingRing B S hS A X := by
  obtain ⟨hwa, ⟨pres⟩⟩ := hY
  exact ⟨hwa, ⟨{ pres with colimitIso := e ≪≫ pres.colimitIso }⟩⟩

/-- A surjectively presented sheaf with a presenting ring satisfying a property `Q` transports
along an isomorphism of fppf sheaves once the set-theoretic condition is known on the source. -/
private theorem presentingRing_prop_of_iso_hset {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (hset : SatisfiesSetTheoreticCondition B S hS X)
    (Q : (A : Type u) → [CommRing A] → [TopologicalSpace A] → [IsTopologicalRing A] →
      [IsLinearTopology A A] → Prop)
    (hY : HasSomeSurjectivePresentation B S hS Y ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A Y ∧ Q A) :
    HasSomeSurjectivePresentation B S hS X ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A X ∧ Q A := by
  obtain ⟨hpres, A, i1, i2, i3, i4, hpr, hrest⟩ := hY
  exact ⟨hasSomeSurjectivePresentation_of_iso_hset B S hS e hset hpres, A, i1, i2, i3, i4,
    isPresentingRing_of_iso_hset B S hS e A hpr, hrest⟩

/-! ### Clause (3): the completion of a countably indexed space is countably indexed -/

/-- For every countably indexed affine formal algebraic space `Y` over `S` with reduction
`j : Y_red ⟶ Y` and every closed `V ⊆ |Y_red|` with compact complement, the completion of `Y`
along `V` is the formal spectrum of a weakly admissible topological ring with a countable
fundamental system of neighbourhoods of `0`. -/
abbrev CompletionOfCountablyIndexedIsCountableSpf : Prop :=
  ∀ (Y Yred : FppfSheaf B S hS) (j : Yred ⟶ Y), IsReduction B S hS Y Yred j →
    IsCountablyIndexed B S hS Y →
    ∀ V : Set (Space.pointsULift.{u + 1} B S hS Yred.obj),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Yred.obj) V →
      @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Yred.obj) Vᶜ →
      HasCountableWeakPresentation B S hS (completionAlong j V)

/-- Let `S` be a scheme, let `X` be an affine formal algebraic space over `S`, let
`i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed with `|X_red| \ T`
quasi-compact. If `X` is countably indexed then so is the completion `X_{/T}` of `X` along `T`.

It takes as hypothesis `hspf : CompletionOfCountablyIndexedIsCountableSpf`. -/
@[stacks 0GVV "clause (3): if `|X_red| \\ T` is quasi-compact and `X` is countably indexed \
then so is `X_{/T}`, countably indexed being `IsCountablyIndexed` (Stacks 0AIJ, \
StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexed.lean). Carried hypotheses: `hX` is \
the tag's own countable-indexing hypothesis on `X`, `hi` supplies the reduction as data \
rather than choosing one from Stacks 0AIN (the convention of the library's Stacks 0GVT \
and 0GB8), `hT` is the tag's own closedness of `T` in `|X_red|`, `hqc` is the tag's own \
quasi-compactness of `|X_red| \\ T`, stated as compactness of `Tᶜ` for the point topology \
`Space.pointTopologyULift` since this library has no quasi-compactness predicate for formal \
algebraic spaces, and `hspf` is the source's own step producing the weakly admissible ring \
`lim A/J_{m,n}` with a countable fundamental system of neighbourhoods of zero — condition (2) \
of Stacks 0AN1 — quantified over its own space, reduction and subset. The \
step from `hspf` to the conclusion is Stacks 0AN1, (2) ⇒ (1) \
(`isCountablyIndexedAffine_of_hasCountableWeakPresentation`)."]
theorem isCountablyIndexed_completionAlong {X Xred : FppfSheaf B S hS}
    (hX : IsCountablyIndexed B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) Tᶜ)
    (hspf : CompletionOfCountablyIndexedIsCountableSpf B S hS) :
    IsCountablyIndexed B S hS (completionAlong i T) :=
  (isCountablyIndexedAffine_of_hasCountableWeakPresentation B S hS (completionAlong i T)
    (hspf X Xred i hi hX T hT hqc)).2

/-! ### Clause (4): the completion of an adic\* space is adic\* -/

/-- For every adic\* affine formal algebraic space `Y` over `S` with reduction
`j : Y_red ⟶ Y` and every closed `V ⊆ |Y_red|` with compact complement, the completion of `Y`
along `V` is isomorphic to the completion of an affine scheme `Spec A` of the site along a
finitely generated ideal `J` of `A`. -/
abbrev CompletionOfAdicStarIsCompletionAlongFGIdeal : Prop :=
  ∀ (Y Yred : FppfSheaf B S hS) (j : Yred ⟶ Y), IsReduction B S hS Y Yred j →
    IsAdicStar B S hS Y →
    ∀ V : Set (Space.pointsULift.{u + 1} B S hS Yred.obj),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Yred.obj) V →
      @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Yred.obj) Vᶜ →
      ∃ (A : Type u) (_ : CommRing A) (str : Spec (.of A) ⟶ S)
        (hA : B.Contains (Spec (.of A))) (J : Ideal A), J.FG ∧
        Nonempty (completionAlong j V ≅ completionAlongIdeal B S hS str hA J)

/-- Let `S` be a scheme, let `X` be an affine formal algebraic space over `S`, let
`i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed with `|X_red| \ T`
quasi-compact. If `X` is adic\* then so is the completion `X_{/T}` of `X` along `T`.

It takes as hypotheses `hideal : CompletionOfAdicStarIsCompletionAlongFGIdeal` and the
set-theoretic condition `hset` on `X_{/T}`. -/
@[stacks 0GVV "clause (4): if `|X_red| \\ T` is quasi-compact and `X` is adic* then so is \
`X_{/T}`, adic* being `IsAdicStar` (Stacks 0AID (4), \
StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/Types.lean). Carried hypotheses: `hX` is the \
tag's own adic* hypothesis on `X`, `hi` supplies the reduction as data rather than choosing \
one from Stacks 0AIN (the convention of the library's Stacks 0GVT and 0GB8), `hT` is the \
tag's own closedness of `T` in `|X_red|`, `hqc` is the tag's own quasi-compactness of \
`|X_red| \\ T`, stated as compactness of `Tᶜ` for the point topology \
`Space.pointTopologyULift` since this library has no quasi-compactness predicate for formal \
algebraic spaces, `hideal` is the source's own step identifying `X_{/T}` with the completion \
of an affine scheme along the finitely generated ideal `J = (f_1,...,f_r) + I`, quantified \
over its own space, reduction and subset, and `hset` is the set-theoretic \
condition of Stacks 0AIS on the completion, carried where Stacks 0GVM \
(`isAffineFormalAlgebraicSpace_colimit`) carries it and needed to transport the conclusion \
back along the isomorphism. The step from `hideal` to the conclusion is Stacks \
0GXX (3) (`isAdicStar_completionAlongIdeal`)."]
theorem isAdicStar_completionAlong {X Xred : FppfSheaf B S hS}
    (hX : IsAdicStar B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) Tᶜ)
    (hideal : CompletionOfAdicStarIsCompletionAlongFGIdeal B S hS)
    (hset : SatisfiesSetTheoreticCondition B S hS (completionAlong i T)) :
    IsAdicStar B S hS (completionAlong i T) := by
  obtain ⟨A, _, str, hA, J, hJ, ⟨e⟩⟩ := hideal X Xred i hi hX T hT hqc
  exact presentingRing_prop_of_iso_hset B S hS e hset
    (fun A _ _ _ _ => TopologicalRing.IsAdic A ∧ ∃ I : Ideal A,
      TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
    (isAdicStar_completionAlongIdeal B S hS str hA J hJ)

/-! ### Clause (5): the completion of a Noetherian space is Noetherian -/

/-- For every Noetherian affine formal algebraic space `Y` over `S` with reduction
`j : Y_red ⟶ Y` and every closed `V ⊆ |Y_red|`, the completion of `Y` along `V` is isomorphic to
the completion of a Noetherian affine scheme `Spec A` of the site along an ideal `J` of `A`. -/
abbrev CompletionOfNoetherianIsCompletionAlongNoetherianIdeal : Prop :=
  ∀ (Y Yred : FppfSheaf B S hS) (j : Yred ⟶ Y), IsReduction B S hS Y Yred j →
    IsNoetherian B S hS Y →
    ∀ V : Set (Space.pointsULift.{u + 1} B S hS Yred.obj),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Yred.obj) V →
      ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (str : Spec (.of A) ⟶ S)
        (hA : B.Contains (Spec (.of A))) (J : Ideal A),
        Nonempty (completionAlong j V ≅ completionAlongIdeal B S hS str hA J)

/-- Let `S` be a scheme, let `X` be an affine formal algebraic space over `S`, let
`i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be closed. If `X` is Noetherian
then so is the completion `X_{/T}` of `X` along `T`. No quasi-compactness of `|X_red| \ T` is
assumed.

It takes as hypotheses `hideal : CompletionOfNoetherianIsCompletionAlongNoetherianIdeal` and the
set-theoretic condition `hset` on `X_{/T}`. -/
@[stacks 0GVV "clause (5): if `X` is Noetherian then so is `X_{/T}`, Noetherian being \
`IsNoetherian` (Stacks 0AID (5), \
StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/Types.lean). Carried hypotheses: `hX` is the \
tag's own Noetherian hypothesis on `X`, `hi` supplies the reduction as data rather than \
choosing one from Stacks 0AIN (the convention of the library's Stacks 0GVT and 0GB8), `hT` \
is the tag's own closedness of `T` in `|X_red|`, `hideal` is the source's own step identifying \
`X_{/T}` with the completion of a Noetherian affine scheme along an ideal, quantified over its \
own space, reduction and subset, and `hset` is the set-theoretic condition \
of Stacks 0AIS on the completion, carried where Stacks 0GVM \
(`isAffineFormalAlgebraicSpace_colimit`) carries it and needed to transport the conclusion \
back along the isomorphism. There is deliberately NO quasi-compactness hypothesis: the source \
notes it is automatic here. The step from `hideal` to the conclusion is Stacks \
0GXX (4) (`isNoetherian_completionAlongIdeal`)."]
theorem isNoetherian_completionAlong {X Xred : FppfSheaf B S hS}
    (hX : IsNoetherian B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T)
    (hideal : CompletionOfNoetherianIsCompletionAlongNoetherianIdeal B S hS)
    (hset : SatisfiesSetTheoreticCondition B S hS (completionAlong i T)) :
    IsNoetherian B S hS (completionAlong i T) := by
  obtain ⟨A, _, _, str, hA, J, ⟨e⟩⟩ := hideal X Xred i hi hX T hT
  exact presentingRing_prop_of_iso_hset B S hS e hset
    (fun A _ _ _ _ => IsNoetherianRing A ∧ TopologicalRing.IsAdic A)
    (isNoetherian_completionAlongIdeal B S hS str hA J)

end AlgebraicGeometry.FormalSpace

end
