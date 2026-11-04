module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobeniusNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.ConstantSheafOverField
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering

/-!
# `RΓ_c` of an empty scheme

Every sheaf of modules on the small étale site of an empty scheme is zero, so a bounded below
complex `K` of such sheaves lies in degrees `≥ a` for every `a`, and so does `RΓ_c(X_k̄, K)`. An
object of the derived category with no homology is zero, hence `RΓ_c(X_k̄, K)` is zero, perfect,
and `det(1 - π_X^* T | RΓ_c(X_k̄, K)) = 1`. This is the base case of the dévissage of
[Stacks, Tag 03UZ] along a closed filtration, whose last member is empty.

## Main results

* `Stacks.EtaleCohomology.isZero_smallEtaleModuleSheaf_of_isEmpty`.
* `Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomology_of_isEmpty`.
* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_of_isEmpty`.
* `Stacks.EtaleCohomology.perfectDerivedCharSeries_canonicalCompactSupportFrobenius_of_isEmpty`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ZeroObject

universe u r

/-- An object of `D⁺(C)` lying in degrees `≥ a` for every `a` is zero. -/
theorem DerivedCategory.Plus.isZero_ι_obj_of_forall_isGE {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory.Plus C) (h : ∀ a : ℤ, K.IsGE a) :
    IsZero (DerivedCategory.Plus.ι.obj K) := by
  have hK : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor C i).obj
      (DerivedCategory.Plus.ι.obj K)) := fun i => by
    have := h (i + 1)
    exact DerivedCategory.Plus.isZero_homology_of_isGE K (i + 1) i (by omega)
  have hiso : IsIso (0 : DerivedCategory.Plus.ι.obj K ⟶ 0) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    exact ⟨⟨0, (hK n).eq_of_src _ _,
      (Functor.map_isZero _ (isZero_zero _)).eq_of_src _ _⟩⟩
  exact (isZero_zero _).of_iso (asIso (0 : DerivedCategory.Plus.ι.obj K ⟶ 0))

namespace Stacks.EtaleCohomology

/-- **A sheaf of modules on the small étale site of an empty scheme is zero.** -/
theorem isZero_smallEtaleModuleSheaf_of_isEmpty (Λ : Type r) [Ring Λ] {X : Scheme.{u}} [IsEmpty X]
    (F : EtaleModules.{u, r} Λ X) : IsZero F :=
  Sheaf.isZero_of_forall_isZero_sections F fun V =>
    have : IsEmpty V.left := ⟨fun x => IsEmpty.false (show X from V.hom.base x)⟩
    (F.isTerminalOfBotCover V (Scheme.Etale.bot_mem_smallEtaleTopology_of_isEmpty V)).isZero

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [Fintype k] in
/-- **`RΓ_c` of an empty scheme is zero.** -/
theorem isZero_compactSupportFrobeniusCohomology_of_isEmpty [IsEmpty X]
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    IsZero (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)) := by
  refine DerivedCategory.Plus.isZero_ι_obj_of_forall_isGE _ fun a => ?_
  have : K.obj.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ a).mpr fun i _ =>
    isZero_smallEtaleModuleSheaf_of_isEmpty Λ _
  exact isGE_compactSupportFrobeniusFunctor_obj Λ f j kbar K a

omit [Fintype k] in
/-- `RΓ_c` of an empty scheme is perfect. -/
theorem isPerfect_compactSupportFrobeniusCohomology_of_isEmpty [IsEmpty X]
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)) := by
  have hQ : IsZero (DerivedCategory.Q.obj (zeroCochainComplex.{r, max (u + 1) r} Λ)) :=
    Functor.map_isZero _ (zeroCochainComplex_isZero.{r, max (u + 1) r} Λ)
  refine StacksDraft.Perfect.isPerfect_of_iso
    ((isZero_compactSupportFrobeniusCohomology_of_isEmpty Λ f j kbar K).iso hQ) ?_
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hP⟩ := zeroCochainComplex_finiteProjective.{r, max (u + 1) r} Λ
  exact ⟨_, a, b, ha, hb, fun i => (hP i).2, fun i => (hP i).1, ⟨Iso.refl _⟩⟩

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`det(1 - π^* T | RΓ_c) = 1` on an empty scheme.** -/
theorem perfectDerivedCharSeries_canonicalCompactSupportFrobenius_of_isEmpty {Λ : Type r}
    [CommRing Λ] [IsEmpty X] (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X))
    (hp : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K))) :
    CategoryTheory.FilteredDerived.perfectDerivedCharSeries Λ _ hp (DerivedCategory.Plus.ι.map
      (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K)) = 1 :=
  CategoryTheory.FilteredDerived.perfectDerivedCharSeries_eq_one_of_isZero Λ hp
    (isZero_compactSupportFrobeniusCohomology_of_isEmpty Λ f j kbar K) _

end Stacks.EtaleCohomology
