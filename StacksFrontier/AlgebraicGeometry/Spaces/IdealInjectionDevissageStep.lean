module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageHigherRank
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIrreducibleIdealInjection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPointsInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissageFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFiniteProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentIntersectionPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealCoproductGenericIso
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealMeet
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeTheoreticSupport

/-!
# A generic trivialization of positive rank, and a Noetherian induction on supports

## Main results

* `AlgebraicGeometry.Space.subsingleton_pi_fin_zero_val_obj`: the sections of a product of
  modules over `Fin 0` are trivial.
* `AlgebraicGeometry.Space.exists_generic_trivialization_pos`: a coherent module with full
  support on a nonempty reduced Noetherian algebraic space has a generic trivialization of
  positive rank.
* `AlgebraicGeometry.Space.forall_property_idealPushforward_of_step`: on a Noetherian algebraic
  space `X`, a property of `𝒪_X`-modules holding on zero modules and closed under extensions of
  coherent modules holds for every direct image `i_*I` of a quasi-coherent sheaf of ideals on a
  reduced closed subspace `i : Z ⟶ X` with `|Z|` irreducible, as soon as it holds for such a
  direct image whenever it holds for every coherent module of strictly smaller support.

## References

* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 07UR](https://stacks.math.columbia.edu/tag/07UR)
* [Stacks Project, Tag 07US](https://stacks.math.columbia.edu/tag/07US)
* [Stacks Project, Tag 07UT](https://stacks.math.columbia.edu/tag/07UT)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A generic trivialization of positive rank -/

/-- **The sections of a product over the empty index type are trivial.** -/
theorem subsingleton_pi_fin_zero_val_obj {Y : AlgebraicSpaces B S hS}
    (M : Modules.{u, u} B S hS Y.1 Y.2) (U : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Subsingleton ((∏ᶜ fun _ : Fin 0 => M).val.obj U) :=
  (bijective_pi_π_val_app_fin B S hS (fun _ : Fin 0 => M) U).1.subsingleton

/-- **A coherent module with full support on a nonempty reduced Noetherian algebraic space has a
generic trivialization of positive rank.** There are a quasi-coherent sheaf of ideals `J` with
nonempty unit locus, an `r > 0` and a map from the `r`-fold product of `J` to `G` which is
bijective on sections over every object of the small étale site on which `J` is the unit
ideal. -/
theorem exists_generic_trivialization_pos (hZtop : B.Contains (⊤_ Scheme.{u}))
    (Y : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZtop Y.1)
    (hred : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsReduced V))
    (hne : Nonempty (points B S hS Y.1))
    (G : Modules.{u, u} B S hS Y.1 Y.2) (hG : IsCoherent B S hS Y.1 Y.2 G)
    (hsupp : moduleSupportSet B S hS Y G = Set.univ) :
    ∃ J : (SheafOfModules.unit (structureRingSheaf B S hS Y)).Submodule,
      J.toSheafOfModules.IsQuasicoherentOnSite ∧ (idealUnitLocus B S hS Y J).Nonempty ∧
      ∃ (r : ℕ) (ψ : (∏ᶜ fun _ : Fin r =>
          (J.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2)) ⟶ G),
        0 < r ∧ ∀ W : SmallEtale B S hS Y.1, J.obj (op W) = ⊤ →
          Function.Bijective (ψ.val.app (op W)).hom := by
  obtain ⟨J, hJq, hJne, r, ψ, hψ⟩ := exists_generic_trivialization B S hS hZtop Y hN hred hne G hG
  refine ⟨J, hJq, hJne, r, ψ, Nat.pos_of_ne_zero fun hr => ?_, hψ⟩
  subst hr
  have hsub : moduleSupportSet B S hS Y G ⊆ idealZeroLocus B S hS Y J := by
    refine supportOfSheaf_subset_idealZeroLocus_of_forall_subsingleton B S hS Y G J
      fun V hV W g => ?_
    have hW : J.obj (op W) = ⊤ := SheafOfModules.Submodule.unit_obj_eq_top_of_map J g.op hV
    exact @Function.Surjective.subsingleton _ _ _ (subsingleton_pi_fin_zero_val_obj B S hS
      (J.toSheafOfModules : Modules.{u, u} B S hS Y.1 Y.2) (op W)) (hψ W hW).2
  obtain ⟨x, hx⟩ := hJne
  exact (hsub (hsupp ▸ Set.mem_univ x)) hx

/-! ### The Noetherian induction -/

/-- **A Noetherian induction on supports.**  Let `P` be a property of
`𝒪_X`-modules on a Noetherian algebraic space, holding on zero modules and closed under
extensions of coherent modules.  Suppose that `P` holds for the direct image `i_*I` of a
quasi-coherent sheaf of ideals on a reduced closed subspace with irreducible space of points as
soon as it holds for every coherent module whose support is strictly smaller than that of
`i_*I`.  Then `P` holds for every such direct image. -/
theorem forall_property_idealPushforward_of_step (hZtop : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hZtop X.1)
    (P : Modules.{u, u} B S hS X.1 X.2 → Prop)
    (hzero : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsZero M → P M)
    (hext : ClosedUnderCoherentExtensions B S hS X P)
    (hstep : ∀ (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z),
      IsReducedIrreducible B S hS Z →
      ∀ I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ),
      (∀ N : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 N →
        moduleSupportSet B S hS X N ⊂ moduleSupportSet B S hS X
          ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) →
        P N) →
      P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules))
    (Z : Subfunctor X.1) (hZ : IsClosedSubspace B S hS Z) (hint : IsReducedIrreducible B S hS Z)
    (I : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ)) :
    P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ)).obj I.1.toSheafOfModules) := by
  have _ : TopologicalSpace.NoetherianSpace (points B S hS X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X.1 X.2 hX.1 hX.2.2
  have key : ∀ T : TopologicalSpace.Closeds (points B S hS X.1),
      ∀ (Z' : Subfunctor X.1) (hZ' : IsClosedSubspace B S hS Z'),
      IsReducedIrreducible B S hS Z' →
      ∀ I' : QuasicoherentIdeals B S hS (closedSubfunctorSpace B S hS hZ'),
      moduleSupportSet B S hS X ((modulePushforward B S hS
          (closedSubfunctorι B S hS hZ')).obj I'.1.toSheafOfModules) ⊆
        (T : Set (points B S hS X.1)) →
      P ((modulePushforward B S hS (closedSubfunctorι B S hS hZ')).obj
        I'.1.toSheafOfModules) := by
    intro T
    induction T using WellFoundedLT.induction with
    | _ T IH =>
      intro Z' hZ' hint' I' hsub
      refine hstep Z' hZ' hint' I' fun N hN hNlt => ?_
      exact property_of_moduleSupportSet_subset B S hS X
        (hasIdealDevissage_of_isCoherent B S hS hZtop X hX) P hzero hext
        (moduleSupportSet B S hS X N)
        (IH ⟨moduleSupportSet B S hS X N, isClosed_moduleSupportSet B S hS X N hN⟩
          (SetLike.coe_ssubset_coe.mp (hNlt.trans_le hsub)))
        N hN Set.Subset.rfl
  exact key ⊤ Z hZ hint I (Set.subset_univ _)

end AlgebraicGeometry.Space

end
