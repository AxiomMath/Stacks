module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.RingTheory.Support
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute

/-!
# Modules supported in a subset of the spectrum

For a subset `T` of the prime spectrum of a commutative ring `A`, the degree-zero sections with
support in `T` of an `A`-module `M` form the submodule `sectionsWithSupportIn A T M`, the union of
the `I`-power-torsion submodules over the closed subsets `V(I) ⊆ T`. This file identifies that
submodule elementwise — an element belongs to it exactly when the zero locus of its annihilator is
contained in `T` — and deduces that it is all of `M` exactly when `M` is supported in `T`. The
modules supported in `T` are then shown to form a Serre subcategory of `A`-modules which is closed
under arbitrary direct sums.

## Main definitions

* `Stacks.LocalCohomology.supportModuleProperty` — the property of an `A`-module that its support
  is contained in `T`.
* `Stacks.LocalCohomology.ModulesSupportedIn` — the corresponding full subcategory of modules.
* `Stacks.LocalCohomology.sectionsWithSupportInCompIso` — sections with support in `T'` followed by
  sections with support in `T` are sections with support in `T ∩ T'`.

## Main results

* `Stacks.LocalCohomology.mem_sectionsWithSupportIn_iff` — an element is a section with support in
  `T` exactly when the zero locus of its annihilator is contained in `T`.
* `Stacks.LocalCohomology.sectionsWithSupportIn_eq_top_iff` — sections with support in `T` fill a
  module exactly when its support is contained in `T`.
* `Stacks.LocalCohomology.supportModuleProperty_isSerreClass` — modules supported in `T` form a
  Serre subcategory.
* `Stacks.LocalCohomology.supportModuleProperty_isClosedUnderCoproducts` — that subcategory is
  closed under arbitrary direct sums.

## References

* [Stacks Project, Tag 0EEZ](https://stacks.math.columbia.edu/tag/0EEZ)
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

namespace Stacks.LocalCohomology

/-- Power torsion is antitone in the ideal: an element killed by a power of `J` is killed by the
same power of any `I ≤ J`. -/
private lemma primaryComponent_mono (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    {I J : Ideal A} (hIJ : I ≤ J) :
    J.primaryComponent M ≤ I.primaryComponent M := by
  intro x hx
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M J x).mp hx
  exact (Ideal.primaryComponent_mem M I x).mpr
    ⟨n, Submodule.torsionBySet_le_torsionBySet_of_subset (Ideal.pow_right_mono hIJ n) hn⟩

/-- The property that an `A`-module has support contained in `T`. -/
def supportModuleProperty (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) : ObjectProperty (ModuleCat.{v} A) :=
  fun M ↦ Module.support A M ⊆ T

/-- The full subcategory of `A`-modules whose support is contained in `T`. -/
abbrev ModulesSupportedIn (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :=
  (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A)).FullSubcategory

/-- An element is a section with support in `T` exactly when the zero locus of its annihilator
is contained in `T`. -/
@[simp]
theorem mem_sectionsWithSupportIn_iff (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : Type v) [AddCommGroup M] [Module A M] (m : M) :
    m ∈ sectionsWithSupportIn A T M ↔
      PrimeSpectrum.zeroLocus (Ideal.torsionOf A M m : Set A) ⊆ T := by
  constructor
  · intro hm p hp
    have hdir : Directed (fun X Y : Submodule A M => X ≤ Y)
        (fun I : {I : Ideal A // PrimeSpectrum.zeroLocus (I : Set A) ⊆ T} =>
          I.val.primaryComponent M) := by
      intro I J
      exact ⟨⟨I.val * J.val, (PrimeSpectrum.zeroLocus_mul _ _).subset.trans
        (Set.union_subset I.property J.property)⟩, primaryComponent_mono A M Ideal.mul_le_left,
        primaryComponent_mono A M Ideal.mul_le_right⟩
    have : Nonempty {I : Ideal A // PrimeSpectrum.zeroLocus (I : Set A) ⊆ T} :=
      ⟨⟨⊤, by simp⟩⟩
    rw [sectionsWithSupportIn, iSup_subtype', Submodule.mem_iSup_of_directed _ hdir] at hm
    obtain ⟨I, hmI⟩ := hm
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I.val m).mp hmI
    refine I.property fun a ha => Ideal.IsPrime.mem_of_pow_mem inferInstance n ?_
    have hn' := (Submodule.mem_torsionBySet_iff _ _).mp hn
      ⟨a ^ n, Ideal.pow_mem_pow ha n⟩
    exact (PrimeSpectrum.mem_zeroLocus p _ |>.mp hp)
      (Ideal.mem_torsionOf_iff m (a ^ n) |>.mpr hn')
  · intro h
    rw [sectionsWithSupportIn]
    apply Submodule.mem_iSup_of_mem (Ideal.torsionOf A M m)
    apply Submodule.mem_iSup_of_mem h
    exact (Ideal.primaryComponent_mem M _ m).mpr ⟨1, by
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      exact Ideal.mem_torsionOf_iff m (a : A) |>.mp (by simpa using a.property)⟩

/-- Degree-zero sections with support in `T` fill `M` if and only if the support of `M` is
contained in `T`. -/
@[stacks 0EEZ "equivalence", ega "IV 5.9.12" "affine module case"]
theorem sectionsWithSupportIn_eq_top_iff (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : Type v) [AddCommGroup M] [Module A M] :
    sectionsWithSupportIn A T M = ⊤ ↔ Module.support A M ⊆ T := by
  refine ⟨fun h p hp => ?_, fun h => top_unique fun m _ =>
    (mem_sectionsWithSupportIn_iff A T M m).mpr fun p hp =>
      h (Module.mem_support_iff_exists_annihilator.mpr
        ⟨m, by rwa [Ideal.annihilator_span_singleton_eq_torsionOf]⟩)⟩
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hp
  exact (mem_sectionsWithSupportIn_iff A T M m).mp (h ▸ Submodule.mem_top) fun a ha =>
    hm (by simpa [Ideal.annihilator_span_singleton_eq_torsionOf] using ha)

/-- Modules whose support is contained in `T` form a Serre subcategory of `A`-modules. -/
@[stacks 0EEZ "Serre subcategory", ega "IV 5.9.12" "(i) C_Z is Serre, affine"]
instance supportModuleProperty_isSerreClass (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A)).IsSerreClass where
  exists_zero := ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _, by
    rw [supportModuleProperty, Module.support_eq_empty_iff.mpr inferInstance]
    exact Set.empty_subset _⟩
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    rw [supportModuleProperty] at h₁ h₃ ⊢
    rw [Module.support_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
      hS.injective_f hS.surjective_g]
    exact Set.union_subset h₁ h₃
  prop_of_mono {X Y} f _ hY := (Module.support_subset_of_injective f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)).trans hY
  prop_of_epi {X Y} f _ hX := (Module.support_subset_of_surjective f.hom
    ((ModuleCat.epi_iff_surjective f).mp inferInstance)).trans hX

/-- The inclusion of the modules supported in `T` preserves finite limits. -/
instance supportModuleProperty_ι_preservesFiniteLimits (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    PreservesFiniteLimits (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A)).ι :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of the modules supported in `T` preserves finite colimits. -/
instance supportModuleProperty_ι_preservesFiniteColimits (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    PreservesFiniteColimits (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A)).ι :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

/-- If a module is a colimit of a discrete diagram of modules whose supports are contained in `T`,
then its support is contained in `T`. -/
private lemma support_subset_of_discrete_colimit {J : Type w} (A : Type u) [CommRing A]
    (F : Discrete J ⥤ ModuleCat.{v} A) {X : ModuleCat.{v} A}
    (ι : F ⟶ (Functor.const (Discrete J)).obj X) (hc : IsColimit (Cocone.mk _ ι))
    (T : Set (PrimeSpectrum A))
    (hF : ∀ j, Module.support A (F.obj j) ⊆ T) :
    Module.support A X ⊆ T := by
  intro p hp
  let S : Submodule A X :=
    Submodule.span A (⋃ j : Discrete J, Set.range
      (fun y : (F.obj j) => show X from (ι.app j).hom y))
  have hS : S = ⊤ := top_unique fun y _ => by
    have hq : ModuleCat.ofHom S.mkQ = 0 := hc.hom_ext fun j => by
      ext y
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.subset_span (Set.mem_iUnion.2 ⟨j, ⟨y, rfl⟩⟩))
    have : S.mkQ y = 0 := congrArg (fun f => f.hom y) hq
    simpa using this
  obtain ⟨x, hxS, hx⟩ := (Module.mem_support_iff_of_span_eq_top hS).mp hp
  obtain ⟨j, y, rfl⟩ := Set.mem_iUnion.mp hxS
  exact hF j (Module.mem_support_iff_exists_annihilator.mpr ⟨y, fun a ha =>
    hx ((Submodule.mem_annihilator_span_singleton _ _).mpr (by
      simpa using congrArg (fun z => show X from (ι.app j).hom z)
        ((Submodule.mem_annihilator_span_singleton _ _).mp ha)))⟩)

/-- Modules whose support is contained in `T` are closed under arbitrary direct sums. -/
@[stacks 0EEZ "closed under direct sums"]
instance supportModuleProperty_isClosedUnderCoproducts (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (J : Type w) :
    (supportModuleProperty A T : ObjectProperty (ModuleCat.{v} A)).IsClosedUnderColimitsOfShape
      (Discrete J) where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    exact support_subset_of_discrete_colimit A h.diag h.ι h.isColimit T h.prop_diag_obj

/-! ### Iterated sections with support -/

section Iterated

/-- A section with support in `T'` has support in `T` exactly when, as an element of the
ambient module, it has support in `T ∩ T'`. -/
public lemma mem_sectionsWithSupportIn_comp_iff (A : Type u) [CommRing A]
    (T T' : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A)
    (x : sectionsWithSupportIn A T' M) :
    x ∈ sectionsWithSupportIn A T (sectionsWithSupportIn A T' M) ↔
      x.val ∈ sectionsWithSupportIn A (T ∩ T') M := by
  rw [mem_sectionsWithSupportIn_iff, mem_sectionsWithSupportIn_iff, torsionOf_submodule_eq]
  exact ⟨fun h p hp => ⟨h hp, (mem_sectionsWithSupportIn_iff A T' M x.val).mp x.property hp⟩,
    fun h p hp => (h hp).1⟩

/-- Sections with support in `T` of sections with support in `T'` push forward onto sections
with support in `T ∩ T'`. -/
public lemma sectionsWithSupportIn_map_eq (A : Type u) [CommRing A]
    (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) :
    (sectionsWithSupportIn A T (sectionsWithSupportIn A T' M)).map
        (sectionsWithSupportIn A T' M).subtype =
      sectionsWithSupportIn A (T ∩ T') M := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_sectionsWithSupportIn_comp_iff A T T' M y).mp hy
  · intro hx
    exact ⟨⟨x, (mem_sectionsWithSupportIn_iff A T' M x).2 fun p hp =>
      ((mem_sectionsWithSupportIn_iff A (T ∩ T') M x).1 hx hp).2⟩,
      (mem_sectionsWithSupportIn_comp_iff A T T' M _).2 hx, rfl⟩

/-- Iterated sections with support are sections with support in the intersection. -/
public noncomputable def sectionsWithSupportInCompEquiv
    (A : Type u) [CommRing A] (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A) :
    sectionsWithSupportIn A T (sectionsWithSupportIn A T' M) ≃ₗ[A]
      sectionsWithSupportIn A (T ∩ T') M :=
  ((sectionsWithSupportIn A T' M).equivSubtypeMap
      (sectionsWithSupportIn A T (sectionsWithSupportIn A T' M))).trans
    (LinearEquiv.ofEq _ _ (sectionsWithSupportIn_map_eq A T T' M))

/-- The iterated-sections equivalence is the identity on underlying elements. -/
public lemma sectionsWithSupportInCompEquiv_apply
    (A : Type u) [CommRing A] (T T' : Set (PrimeSpectrum A))
    (M : ModuleCat.{max u v} A)
    (x : sectionsWithSupportIn A T (sectionsWithSupportIn A T' M)) :
    (sectionsWithSupportInCompEquiv A T T' M x).val = x.val.val := by
  change ((((sectionsWithSupportIn A T' M).equivSubtypeMap
      (sectionsWithSupportIn A T (sectionsWithSupportIn A T' M))).trans
    (LinearEquiv.ofEq _ _ (sectionsWithSupportIn_map_eq A T T' M))) x : M) = x.val.val
  rw [LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, Submodule.equivSubtypeMap_apply]
  rfl

attribute [local irreducible] sectionsWithSupportIn

/-- Sections with support in `T'` followed by sections with support in `T` is sections with
support in `T ∩ T'`, naturally in the module. -/
public noncomputable def sectionsWithSupportInCompIso
    (A : Type u) [CommRing A] (T T' : Set (PrimeSpectrum A)) :
    sectionsWithSupportInFunctor.{u, v} A T' ⋙ sectionsWithSupportInFunctor.{u, v} A T ≅
      sectionsWithSupportInFunctor.{u, v} A (T ∩ T') :=
  NatIso.ofComponents (fun M => (sectionsWithSupportInCompEquiv A T T' M).toModuleIso)
    (fun {M N} f => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change ((sectionsWithSupportInCompEquiv A T T' N)
          (((sectionsWithSupportInFunctor A T).map
            ((sectionsWithSupportInFunctor A T').map f)).hom x)).val =
        f.hom ((sectionsWithSupportInCompEquiv A T T' M x).val)
      simp only [sectionsWithSupportInCompEquiv_apply, sectionsWithSupportInFunctor_map_val])

end Iterated

end Stacks.LocalCohomology
