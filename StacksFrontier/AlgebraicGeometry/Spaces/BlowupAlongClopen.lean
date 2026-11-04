module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupUniversalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents

/-!
# Blowing up an algebraic space in an open and closed subspace

Let `X` be an algebraic space over a scheme `S` and let `C ⊆ X` be a closed subspace whose set
of points is open in `|X|`.  Then the blowup of `X` in `C` is the inclusion of the open
complement `X ∖ C`.  That inclusion lies in the category `𝒞` of Stacks 085U, because the
inverse image of `C` in `X ∖ C` has no points.  It is a final object of `𝒞` for the following
reason.  If the inverse image `D` of `C` along `Y ⟶ X` is an effective Cartier divisor, then its
complement is dense in `|Y|` (Stacks 083S).  The points of `D` form an open set, and an open set
disjoint from a dense set is empty.  So `Y ⟶ X` lands in `X ∖ C`.

## Main results

* `AlgebraicGeometry.Space.isEmpty_points_of_isEffectiveCartierDivisor_of_isOpen`: an effective
  Cartier divisor whose set of points is open has no points.
* `AlgebraicGeometry.Space.isBlowupAlong_openComplement_ι_of_isOpen`: the inclusion of the
  complement of a closed subspace with open point set is the blowup in that subspace.

## References

* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An effective Cartier divisor whose set of points is open has no points.**  Its open
complement is scheme-theoretically dense (Stacks 083S), hence dense on points.  An open set
of points disjoint from a dense set is empty. -/
theorem isEmpty_points_of_isEffectiveCartierDivisor_of_isOpen (X : AlgebraicSpaces B S hS)
    (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)
    (hopen : IsOpen (subspacePointSet B S hS X.1 D.1)) :
    IsEmpty (points B S hS D.1.toFunctor) := by
  have hdense : Dense (subspacePointSet B S hS X.1 (openComplement B S hS D.1)) :=
    dense_subspacePointSet_of_isSchemeTheoreticallyDense B S hS _
      (isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor B S hS X D hD)
  have hcompl : subspacePointSet B S hS X.1 (openComplement B S hS D.1) =
      (subspacePointSet B S hS X.1 D.1)ᶜ :=
    range_pointsMap_ι_openComplement B S hS D.1
  rw [hcompl] at hdense
  refine ⟨fun x => ?_⟩
  obtain ⟨y, hy₁, hy₂⟩ := hdense.inter_open_nonempty _ hopen ⟨_, x, rfl⟩
  exact hy₂ hy₁

/-- **The blowup in a closed subspace with open point set is the inclusion of its complement.**
Let `C ⊆ X` be a closed subspace of an algebraic space whose set of points is open.  Then the
inclusion `X ∖ C ⟶ X` of the open complement is the blowup of `X` in `C`: it is a final object
of the category `𝒞` of Stacks 085U. -/
theorem isBlowupAlong_openComplement_ι_of_isOpen (X : AlgebraicSpaces B S hS)
    (C : ClosedSubspaces B S hS X.1) (hopen : IsOpen (subspacePointSet B S hS X.1 C.1)) :
    IsBlowupAlong B S hS C
      (ObjectProperty.homMk (openComplement B S hS C.1).ι :
        (⟨(openComplement B S hS C.1).toFunctor,
          (isOpenSubspace_openComplement B S hS X.2 C.1 C.2).1⟩ : AlgebraicSpaces B S hS) ⟶
            X) := by
  set O := openComplement B S hS C.1 with hOdef
  have hO : IsOpenSubspace B S hS O := isOpenSubspace_openComplement B S hS X.2 C.1 C.2
  have hOpts : subspacePointSet B S hS X.1 O = (subspacePointSet B S hS X.1 C.1)ᶜ :=
    range_pointsMap_ι_openComplement B S hS C.1
  have hdisj : Disjoint (subspacePointSet B S hS X.1 C.1) (subspacePointSet B S hS X.1 O) := by
    rw [hOpts]
    exact disjoint_compl_right
  refine isBlowupAlong_of_existsUnique_lift ?_ ?_
  · exact isEffectiveCartierDivisor_of_isEmpty_points B S hS _ _
      (isEmpty_points_preimage_of_disjoint B S hS C.1 O hdisj O.ι (𝟙 _) (Category.id_comp _))
  · intro Y y hy
    -- The inverse image of `C` in `Y` has an open set of points, hence no points.
    have hopen' : IsOpen (subspacePointSet B S hS Y.1 (C.1.preimage y.hom)) := by
      rw [subspacePointSet_preimage B S hS]
      exact hopen.preimage (continuous_pointsMap B S hS y.hom)
    have hempty := isEmpty_points_of_isEffectiveCartierDivisor_of_isOpen Y
      ⟨C.1.preimage y.hom, isClosedSubspace_preimage B S hS y.hom C.1 X.2 Y.2 C.2⟩ hy hopen'
    -- So the inverse image of `O` in `Y` is everything.
    have hP : IsOpenSubspace B S hS (O.preimage y.hom) :=
      isOpenSubspace_preimage B S hS y.hom O X.2 Y.2 hO
    have hsurj : Function.Surjective
        (pointsMap B S hS (O.preimage y.hom).toFunctor (O.preimage y.hom).ι) := by
      intro x
      have hx : x ∈ subspacePointSet B S hS Y.1 (O.preimage y.hom) := by
        rw [subspacePointSet_preimage B S hS, Set.mem_preimage, hOpts]
        intro hxC
        have hxC' : x ∈ subspacePointSet B S hS Y.1 (C.1.preimage y.hom) := by
          rw [subspacePointSet_preimage B S hS]
          exact hxC
        obtain ⟨z, -⟩ := hxC'
        exact hempty.false z
      obtain ⟨z, hz⟩ := hx
      exact ⟨z, hz⟩
    have : IsIso (O.preimage y.hom).ι :=
      isIso_of_isOpenImmersion_of_surjective_pointsMap B S hS _ hP.2 hsurj
    set l : Y.1 ⟶ O.toFunctor := inv (O.preimage y.hom).ι ≫ O.fromPreimage y.hom with hl
    have hlι : l ≫ O.ι = y.hom := by
      rw [hl, Category.assoc, Subfunctor.fromPreimage_ι, IsIso.inv_hom_id_assoc]
    have : Mono O.ι := inferInstance
    refine ⟨ObjectProperty.homMk l, ObjectProperty.hom_ext _ hlι, fun m hm => ?_⟩
    refine ObjectProperty.hom_ext _ ((cancel_mono O.ι).1 ?_)
    show m.hom ≫ O.ι = l ≫ O.ι
    rw [hlι]
    exact congrArg (fun φ : Y ⟶ X => φ.hom) hm

end AlgebraicGeometry.Space

end
