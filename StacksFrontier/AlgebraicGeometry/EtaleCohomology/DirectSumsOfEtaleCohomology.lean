module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleColimits
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CoproductsFromFiltered
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale cohomology commutes with direct sums

Let `X` be a quasi-compact and quasi-separated scheme. For every degree `p` the functor
`H^p_étale(X, -)` on abelian sheaves of the small étale site preserves arbitrary coproducts, and
in particular a direct sum of sheaves whose cohomology vanishes in degree `p` again has
vanishing cohomology in degree `p`.

A coproduct is not a filtered colimit, so this does not follow from Stacks 03Q5 alone: it is the
filtered colimit of its finite sub-coproducts, and the finite ones are supplied by additivity of
a right derived functor.

## Main results

* `Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_Γ_smallEtale` — Stacks 03Q5 read
  as preservation of filtered colimits rather than as invertibility of the canonical map.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale` — étale
  cohomology preserves arbitrary coproducts of abelian sheaves.
* `Stacks.EtaleCohomology.isZero_rightDerived_Γ_sigma_smallEtale` — **a direct sum of sheaves
  with vanishing degree-`p` cohomology has vanishing degree-`p` cohomology.**
* `Stacks.EtaleCohomology.subsingleton_sheafH_sigma_smallEtale` — the same for Mathlib's
  `CategoryTheory.Sheaf.H`.
* `Stacks.EtaleCohomology.isZero_rightDerived_Γ_sigma_smallEtale_small` and
  `Stacks.EtaleCohomology.subsingleton_sheafH_sigma_smallEtale_small` — the two of them for a
  family indexed by a type of the scheme universe, such as the closed points of `X`.

## Implementation notes

The three inputs are `Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale` for
the filtered colimits, `CategoryTheory.Functor.additive_rightDerived` for the finite coproducts,
and `Stacks.CoproductsFromFiltered.preservesColimitsOfShape_discrete` to combine them.

Coefficients are `AddCommGrpCat.{max (u + 1) v}` and the index type of the direct sum lives in
`Type (max (u + 1) v)`, so that the filtered poset of its finite subsets is an index category of
the size Stacks 03Q5 is stated for. Existence of the colimits involved is not reachable by
instance search on this site; it is opened from the scoped namespace
`AlgebraicGeometry.Scheme.SmallEtaleColimits`.

## References

* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry.Scheme.SmallEtaleColimits

universe v u

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]

/-- **Étale cohomology of a quasi-compact quasi-separated scheme preserves filtered colimits.**
This is Stacks 03Q5 read through `CategoryTheory.Limits.preservesColimit_of_isIso_post`. -/
@[sga "4 VII 3.3", sga "4 XIV 1.11" "partial"]
theorem preservesColimitsOfShape_rightDerived_Γ_smallEtale (p : ℕ)
    (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p) :=
  ⟨fun {F} =>
    have : IsIso (colimit.post F
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p)) :=
      isIso_colimit_post_rightDerived_Γ_smallEtale.{v} X p F
    preservesColimit_of_isIso_post (F := F)
      (G := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p)⟩

/-- **Étale cohomology of a quasi-compact quasi-separated scheme preserves direct sums.** A
coproduct is the filtered colimit of its finite sub-coproducts; the filtered colimits are Stacks
03Q5 and the finite ones are additivity of a right derived functor. -/
theorem preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale (p : ℕ)
    (α : Type (max (u + 1) v)) :
    PreservesColimitsOfShape (Discrete α)
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p) :=
  have : HasCoproducts.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    fun _ => hasColimitsOfShape_sheaf_smallEtaleTopology.{u, v} X _
  have : PreservesColimitsOfShape (Finset (Discrete α))
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p) :=
    preservesColimitsOfShape_rightDerived_Γ_smallEtale.{v} X p _
  CoproductsFromFiltered.preservesColimitsOfShape_discrete _

/-- **The degree-`p` étale cohomology of a direct sum vanishes as soon as that of every summand
does.** -/
theorem isZero_rightDerived_Γ_sigma_smallEtale (p : ℕ) {α : Type (max (u + 1) v)}
    (F : α → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ a, IsZero
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj (F a))) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj (∐ F)) := by
  set G := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p with hG
  have : PreservesColimitsOfShape (Discrete α) G :=
    preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale.{v} X p α
  have hc : IsColimit (G.mapCocone (Cofan.mk (∐ F) (Sigma.ι F))) :=
    isColimitOfPreserves G (coproductIsCoproduct F)
  refine (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun j => ?_)
  have h0 : G.map (Sigma.ι F j.as) = 0 := (hF j.as).eq_zero_of_src _
  simp [h0]

/-- **The degree-`p` étale cohomology of a direct sum vanishes as soon as that of every summand
does**, stated for Mathlib's `CategoryTheory.Sheaf.H`. -/
theorem subsingleton_sheafH_sigma_smallEtale
    [HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (p : ℕ) {α : Type (max (u + 1) v)}
    (F : α → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ a, Subsingleton (Sheaf.H.{max (u + 1) v, max (u + 1) v} (F a) p)) :
    Subsingleton (Sheaf.H.{max (u + 1) v, max (u + 1) v} (∐ F) p) :=
  (Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v}
      X.smallEtaleTopology _ p).2
    (isZero_rightDerived_Γ_sigma_smallEtale.{v} X p F fun a =>
      (Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v}
        X.smallEtaleTopology _ p).1 (hF a))

/-- `Stacks.EtaleCohomology.isZero_rightDerived_Γ_sigma_smallEtale` for a family indexed by a
type of the scheme universe, such as the closed points of `X`. -/
theorem isZero_rightDerived_Γ_sigma_smallEtale_small (p : ℕ) {α : Type u}
    (F : α → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ a, IsZero
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj (F a))) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj (∐ F)) :=
  have h := isZero_rightDerived_Γ_sigma_smallEtale.{v} X p
    (fun a : ULift.{max (u + 1) v} α => F a.down) fun a => hF a.down
  h.of_iso (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).rightDerived p).mapIso
    (Sigma.whiskerEquiv (f := F) (g := fun a : ULift.{max (u + 1) v} α => F a.down)
      Equiv.ulift.symm fun _ => Iso.refl _))

/-- `Stacks.EtaleCohomology.subsingleton_sheafH_sigma_smallEtale` for a family indexed by a type
of the scheme universe, such as the closed points of `X`. -/
theorem subsingleton_sheafH_sigma_smallEtale_small
    [HasExt.{max (u + 1) v} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (p : ℕ) {α : Type u} (F : α → Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : ∀ a, Subsingleton (Sheaf.H.{max (u + 1) v, max (u + 1) v} (F a) p)) :
    Subsingleton (Sheaf.H.{max (u + 1) v, max (u + 1) v} (∐ F) p) :=
  (Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v}
      X.smallEtaleTopology _ p).2
    (isZero_rightDerived_Γ_sigma_smallEtale_small.{v} X p F fun a =>
      (Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{v}
        X.smallEtaleTopology _ p).1 (hF a))

end Stacks.EtaleCohomology

end
