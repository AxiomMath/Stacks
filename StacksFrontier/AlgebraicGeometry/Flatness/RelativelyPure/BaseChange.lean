module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Universal purity and base change

Universal purity along a fibre is equivalent to purity along the corresponding fibre after
every pointed base change. Consequently, universal purity relative to a base is equivalent to
purity relative to every base change.

## Main results

* `AlgebraicGeometry.relativeAssassin_eq_of_moduleIso`: the relative assassin is invariant
  under an isomorphism of modules.
* `AlgebraicGeometry.isUniversallyPureAlong_iff_forall_baseChange_isPureAlong` is the
  pointed-fibre characterization.
* `AlgebraicGeometry.isUniversallyPureRelative_iff_forall_baseChange_isPureRelative` is the
  relative characterization.

## Implementation notes

A base change is expressed by an arbitrary cartesian square. Its module is specified up to
isomorphism with the canonical pullback rather than by equality; this includes the identity base
change and is invariant under choices of pullback objects. The pre-pure situations carry the
finite type and quasi-coherence hypotheses inherited by base change.

Invariance of the relative assassin under an isomorphism of modules is obtained from
`AlgebraicGeometry.associatedPoints_subset_of_mono` applied to the two halves of the
isomorphism on each fibre.

## References

* [Stacks Project, Tag 05J6](https://stacks.math.columbia.edu/tag/05J6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The associated points of a module are invariant under an isomorphism: both halves of the
isomorphism are monomorphisms. -/
public theorem associatedPoints_eq_of_moduleIso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) :
    Stacks.Divisors.associatedPoints F = Stacks.Divisors.associatedPoints G :=
  Set.Subset.antisymm (associatedPoints_subset_of_mono e.hom)
    (associatedPoints_subset_of_mono e.inv)

/-- The relative assassin of a module along a morphism is invariant under an isomorphism of
modules. -/
public theorem relativeAssassin_eq_of_moduleIso {X S : Scheme.{u}} (f : X ⟶ S)
    {F G : X.Modules} (e : F ≅ G) :
    Stacks.Divisors.relativeAssassin f F = Stacks.Divisors.relativeAssassin f G := by
  ext x
  simp only [Stacks.Divisors.mem_relativeAssassin]
  refine exists_congr fun s => exists_congr fun xs => and_congr_left fun _ => ?_
  rw [associatedPoints_eq_of_moduleIso ((Scheme.Modules.pullback (f.fiberι s)).mapIso e)]

/-- **Stacks Project, Tag 05J6.** Universal purity along the chosen fibre can be tested by
purity after every pointed base change. -/
@[stacks 05J6 "the pointed-fibre equivalence"]
public theorem isUniversallyPureAlong_iff_forall_baseChange_isPureAlong
    (P : PrePureSituation.{u}) :
    IsUniversallyPureAlong P ↔
      ∀ (Q : PrePureSituation.{u}) (g : Q.S ⟶ P.S)
        (_hg : g.base Q.s = P.s) (toX : Q.X ⟶ P.X)
        (_hpb : IsPullback toX Q.f P.f g)
        (_hF : Q.F ≅ (Scheme.Modules.pullback toX).obj P.F),
          IsPureAlong Q := by
  constructor
  · intro hP Q g hg toX hpb hF E hEtale hElem hEimp
    let D' : ImpurityDiagram P :=
      { T := E.T, g := E.g ≫ g, t' := E.t', t := E.t
        specializes := E.specializes
        mapsToChosenPoint := by
          rw [← E.mapsToChosenPoint] at hg
          simpa using hg
        X_T := E.X_T, toX := E.toX ≫ toX, toT := E.toT
        isPullback := E.isPullback.paste_horiz hpb
        xi := E.xi, xi_liesOver := E.xi_liesOver }
    exact hP D' ⟨(relativeAssassin_eq_of_moduleIso E.toT
      (((Scheme.Modules.pullbackComp E.toX toX).app P.F).symm ≪≫
        ((Scheme.Modules.pullback E.toX).mapIso hF).symm)).symm.subset hEimp.1, hEimp.2⟩
  · intro hAll D hD
    let Q : PrePureSituation.{u} :=
      { S := D.T, X := D.X_T, f := D.toT
        locallyOfFiniteType := MorphismProperty.of_isPullback D.isPullback inferInstance
        quasiCompact := MorphismProperty.of_isPullback D.isPullback inferInstance
        F := D.pulledBack P
        isFiniteType := SheafOfModules.pullback_isFiniteType
          D.toX.toLRSHom.toShHom P.F
        isQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent
          D.X_T.toRingedSpace P.X.toRingedSpace D.toX.toLRSHom.toShHom
          P.F P.isQuasicoherent, s := D.t }
    let E : ImpurityDiagram Q :=
      { T := D.T, g := 𝟙 D.T, t' := D.t', t := D.t
        specializes := D.specializes, mapsToChosenPoint := rfl
        X_T := D.X_T, toX := 𝟙 D.X_T, toT := D.toT
        isPullback := IsPullback.id_horiz D.toT
        xi := D.xi, xi_liesOver := D.xi_liesOver }
    exact hAll Q D.g D.mapsToChosenPoint D.toX D.isPullback (Iso.refl _) E inferInstance
      (EtaleNeighborhood.isElementary_self D.T D.t)
      ⟨(relativeAssassin_eq_of_moduleIso D.toT
        ((Scheme.Modules.pullbackId D.X_T).app Q.F)).symm.subset hD.1, hD.2⟩

/-- **Stacks Project, Tag 05J6, in particular.** Universal purity over the base can be tested
by purity relative to every base change. -/
@[stacks 05J6 "the relative equivalence"]
public theorem isUniversallyPureRelative_iff_forall_baseChange_isPureRelative
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    IsUniversallyPureRelative f F ↔
      ∀ {X' S' : Scheme.{u}} (f' : X' ⟶ S')
        [LocallyOfFiniteType f'] [QuasiCompact f']
        (F' : X'.Modules) [F'.IsFiniteType] [F'.IsQuasicoherent]
        (g : S' ⟶ S) (toX : X' ⟶ X)
        (_hpb : IsPullback toX f' f g)
        (_hF : F' ≅ (Scheme.Modules.pullback toX).obj F),
          IsPureRelative f' F' := by
  unfold IsUniversallyPureRelative IsPureRelative
  exact ⟨fun h X' S' f' _ _ F' _ _ g toX hpb hF s' =>
    (isUniversallyPureAlong_iff_forall_baseChange_isPureAlong
      { S := S, X := X, f := f, F := F, s := g.base s' }).mp (h (g.base s'))
      { S := S', X := X', f := f', F := F', s := s' } g rfl toX hpb hF,
    fun h s => (isUniversallyPureAlong_iff_forall_baseChange_isPureAlong
      { S := S, X := X, f := f, F := F, s := s }).mpr
      fun Q g _ toX hpb hF => h Q.f Q.F g toX hpb hF Q.s⟩

end AlgebraicGeometry
