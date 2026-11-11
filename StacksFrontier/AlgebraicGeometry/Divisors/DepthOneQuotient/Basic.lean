module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.SupportedSections.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LargestSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.RingTheory.Depth.AssociatedPrime
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Specialization.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# The depth-one quotient of a coherent module

On a Noetherian scheme, a coherent module has a canonical quotient which agrees with it away
from a specialization-closed set and has depth at least one at every point of that set.

## Main definitions

* `AlgebraicGeometry.IsDepthOneQuotient` records the three local properties of the quotient map.
* `AlgebraicGeometry.depthOneQuotient` is the canonical target sheaf.
* `AlgebraicGeometry.toDepthOneQuotient` is its quotient map.

## Main results

* `AlgebraicGeometry.exists_depthOneQuotient` constructs the quotient together with its
  universal property.
* `AlgebraicGeometry.depthOneQuotient_spec` gives the quotient properties.
* `AlgebraicGeometry.depthOneQuotient_lift` factors maps to coherent sheaves of depth at least
  one along the chosen set uniquely through the quotient.
* `AlgebraicGeometry.depthOneQuotient_unique` gives uniqueness up to a unique isomorphism
  compatible with the quotient maps.

## Implementation notes

Surjectivity is categorical epimorphy in the category of sheaves of modules. Agreement away from
the chosen set is tested on the induced abelian-group stalk maps. The depth of a stalk is taken
along the maximal ideal of its local ring. The uniqueness statement compares any two quotient
maps by a unique isomorphism over their common source, rather than identifying their target
sheaves literally. The existence claim also records the universal property driving the
construction: the quotient removes the subsheaf of sections supported on the chosen set. So the
lift property does not require the map to the target to be surjective, or even an isomorphism
away from the chosen set.

## References

* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.CoherentSubquotients


private lemma mono_of_mono_underlyingPresheaf {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) (hf : Mono ((Scheme.Modules.toPresheaf X).map f)) : Mono f := by
  refine ⟨?_⟩
  intro Z g h hcomp
  apply Functor.map_injective (Scheme.Modules.toPresheaf X)
  let : Mono ((Scheme.Modules.toPresheaf X).map f) := hf
  apply (cancel_mono ((Scheme.Modules.toPresheaf X).map f)).1
  simpa only [Functor.map_comp] using
    congrArg (fun k => (Scheme.Modules.toPresheaf X).map k) hcomp

/-- The inclusion of the submodule of sections supported on `T` is a monomorphism. -/
private lemma mono_supportedSectionsSubmodule_ι {X : Scheme.{u}} (T : Set X) (F : X.Modules) :
    Mono (Scheme.Modules.supportedSectionsSubmodule T F).ι := by
  refine mono_of_mono_underlyingPresheaf _ ((NatTrans.mono_iff_mono_app _).2 fun U => ?_)
  rw [AddCommGrpCat.mono_iff_injective]
  exact fun s t h => Subtype.ext h

private noncomputable def supportedSectionsObject {X : Scheme.{u}} (T : Set X)
    (F : X.Modules) : Subobject F :=
  let N := Scheme.Modules.supportedSectionsSubmodule T F
  @Subobject.mk (X.Modules) (inferInstance) F (N.toSheafOfModules) N.ι
    (mono_supportedSectionsSubmodule_ι T F)

private noncomputable def maximalQCSupportedSubobject {X : Scheme.{u}}
    [IsNoetherian X] (T : Set X) (F : X.Modules) [F.IsCoherent] :
    {W : Subobject ((supportedSectionsObject T F : Subobject F) : X.Modules) //
      (W : X.Modules).IsQuasicoherent} :=
  let S := supportedSectionsObject T F
  letI : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  Classical.choose (existsUnique_quasicoherentSubobject X F S)

private noncomputable abbrev torsionModule {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F : X.Modules) [F.IsCoherent] : X.Modules :=
  (maximalQCSupportedSubobject T F).1

private noncomputable def torsionModuleι {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F : X.Modules) [F.IsCoherent] : torsionModule T F ⟶ F :=
  (maximalQCSupportedSubobject T F).1.arrow ≫ (supportedSectionsObject T F).arrow

private instance torsionModuleι_mono {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F : X.Modules) [F.IsCoherent] : Mono (torsionModuleι T F) := by
  dsimp [torsionModuleι]
  infer_instance

private instance torsionModule_isCoherent {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F : X.Modules) [F.IsCoherent] : (torsionModule T F).IsCoherent := by
  let : (torsionModule T F).IsQuasicoherent := (maximalQCSupportedSubobject T F).2
  exact isCoherent_of_mono
    (X := X) (F := F) (G := torsionModule T F) (torsionModuleι T F)

private noncomputable def depthOneQuotientCandidate {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F : X.Modules) [F.IsCoherent] : X.Modules :=
  cokernel (torsionModuleι T F)

private noncomputable def depthOneQuotientCandidateMap {X : Scheme.{u}}
    [IsNoetherian X] (T : Set X) (F : X.Modules) [F.IsCoherent] :
    F ⟶ depthOneQuotientCandidate T F :=
  cokernel.π (torsionModuleι T F)

private instance depthOneQuotientCandidate_isCoherent {X : Scheme.{u}}
    [IsNoetherian X] (T : Set X) (F : X.Modules) [F.IsCoherent] :
    (depthOneQuotientCandidate T F).IsCoherent := by
  exact SheafOfModules.cokernel_isCoherent (torsionModuleι T F)

private lemma coimage_isCoherent {X : Scheme.{u}} [IsNoetherian X]
    {F H : X.Modules} [F.IsCoherent] [H.IsCoherent] (f : F ⟶ H) :
    (Abelian.coimage f).IsCoherent := by
  let : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  let : F.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).2
  let : H.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent H).1
  let : H.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent H).2
  let : (kernel f).IsCoherent := SheafOfModules.kernel_isCoherent f
  have hcok : (cokernel (kernel.ι f)).IsCoherent :=
    SheafOfModules.cokernel_isCoherent (kernel.ι f)
  exact hcok

private lemma depthOneQuotientCandidateMap_epi {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F : X.Modules) [F.IsCoherent] :
    Epi (depthOneQuotientCandidateMap T F) := by
  let f := torsionModuleι T F
  change Epi (cokernel.π f)
  exact Cofork.IsColimit.epi
    (s := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f))
    (cokernelIsCokernel f)

private lemma maximalIdeal_not_mem_associatedPrimes_of_one_le_depth
    {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdepth : 1 ≤ Module.depth R (IsLocalRing.maximalIdeal R) M) :
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R M := by
  intro hass
  have hz :=
    (Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes (S := R) (N := M)).2 hass
  have hbad : (1 : ℕ∞) ≤ 0 := hz ▸ hdepth
  simp at hbad

private lemma exists_associatedPoint_of_nonempty_support
    {X : Scheme.{u}} [IsNoetherian X] (H : X.Modules) [H.IsCoherent]
    (hsupp : (SheafOfModules.supp H).Nonempty) :
    ∃ x : X, x ∈ SheafOfModules.supp H ∧ x ∈ Stacks.Divisors.associatedPoints H := by
  classical
  let : H.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent H).1
  let : H.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent H).2
  let G : SheafOfModules X.ringCatSheaf := H
  let S : Set X := SheafOfModules.supp G
  have hclosed : IsClosed S := SheafOfModules.isClosed_supp G
  obtain ⟨C, hCirr, hCeq⟩ :=
    (inferInstance : TopologicalSpace.NoetherianSpace X).exists_finset_irreducible
      (⟨S, hclosed⟩ : TopologicalSpace.Closeds X)
  have hCne : C.Nonempty := by
    by_contra h
    have hz : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨x, hx⟩ := hsupp
    have hx' : x ∈ (⟨S, hclosed⟩ : TopologicalSpace.Closeds X) := hx
    have hSempty : S = ∅ := by
      have h := congrArg (fun Z : TopologicalSpace.Closeds X => (Z : Set X)) hCeq
      simpa [hz] using h
    change x ∈ S at hx
    rw [hSempty] at hx
    exact hx
  obtain ⟨D, hD, hDmax⟩ := C.exists_maximal hCne
  let hDirr : IsIrreducible (D : Set X) := hCirr ⟨D, hD⟩
  let x := hDirr.genericPoint
  have hDclosed : IsClosed (D : Set X) := D.2
  have hDgen : IsGenericPoint x (D : Set X) :=
    hDirr.isGenericPoint_genericPoint hDclosed
  have hxS : x ∈ S := by
    have hDC' : D ≤ C.sup id := Finset.le_sup (f := id) hD
    have hS_eq : S = (C.sup id : TopologicalSpace.Closeds X) :=
      congrArg (fun Z : TopologicalSpace.Closeds X => (Z : Set X)) hCeq
    have hDC : (D : Set X) ⊆ S := by rw [hS_eq]; exact hDC'
    exact hDC hDgen.mem
  refine ⟨x, hxS, ?_⟩
  apply mem_associatedPoints_of_mem_supp_of_specialization X H x hxS
  intro y hy hspec
  have hYclosed : IsClosed (closure ({y} : Set X)) := isClosed_closure
  have hYsubset : closure ({y} : Set X) ⊆ S :=
    closure_minimal (Set.singleton_subset_iff.mpr hy) hclosed
  have hDsubsetY : (D : Set X) ⊆ closure ({y} : Set X) := by
    rw [← hDgen.def]
    have hxY : x ∈ closure ({y} : Set X) :=
      specializes_iff_mem_closure.mp hspec
    exact closure_minimal (Set.singleton_subset_iff.mpr hxY) isClosed_closure
  have hYirr : IsIrreducible (closure ({y} : Set X)) :=
    (isIrreducible_iff_closure).mpr (isIrreducible_singleton (x := y))
  let C' : Finset (Set X) := Finset.image
    (fun z : TopologicalSpace.Closeds X => (z : Set X)) C
  have hmemC (z : X) :
      z ∈ C.sup (fun E : TopologicalSpace.Closeds X => (E : Set X)) ↔
        ∃ E ∈ C, z ∈ (E : Set X) := by
    rw [Finset.sup_eq_iSup]
    change z ∈ (⋃ E : TopologicalSpace.Closeds X, ⋃ (_ : E ∈ C), (E : Set X)) ↔ _
    simp only [Set.mem_iUnion, exists_prop]
  have hS_eq_set : S = C.sup (fun E : TopologicalSpace.Closeds X => (E : Set X)) := by
    have h := congrArg (fun Z : TopologicalSpace.Closeds X => (Z : Set X)) hCeq
    rw [TopologicalSpace.Closeds.coe_finset_sup] at h
    exact h
  have hYcover : closure ({y} : Set X) ⊆ ⋃₀ (C' : Set (Set X)) := by
    intro z hz
    have hzS : z ∈ S := hYsubset hz
    rw [hS_eq_set] at hzS
    rcases (hmemC z).mp hzS with ⟨E, hE, hzE⟩
    exact Set.mem_sUnion.mpr ⟨(E : Set X), Finset.mem_image.mpr ⟨E, hE, rfl⟩, hzE⟩
  obtain ⟨E, hE, hEsub⟩ := (isIrreducible_iff_sUnion_isClosed.mp hYirr) C'
    (by
      intro E hE
      obtain ⟨E₀, hE₀, rfl⟩ := Finset.mem_image.mp hE
      exact E₀.2)
    hYcover
  rcases Finset.mem_image.mp hE with ⟨E', hE', rfl⟩
  have hDE : D ≤ E' := by
    intro z hz
    exact hEsub (hDsubsetY hz)
  have hEqDE : D = E' := le_antisymm hDE (hDmax hE' hDE)
  have hYsubsetD : closure ({y} : Set X) ⊆ (D : Set X) := by
    rw [hEqDE]
    exact hEsub
  have hygen : IsGenericPoint y (D : Set X) := by
    change closure ({y} : Set X) = (D : Set X)
    exact Set.Subset.antisymm hYsubsetD hDsubsetY
  exact hDgen.eq hygen |>.symm

private lemma module_isZero_iff_all_stalks_isZero (X : Scheme.{u}) (M : X.Modules) :
    IsZero M ↔ ∀ x : X, IsZero (((Scheme.Modules.toPresheaf X).obj M).stalk x) := by
  let P := (Scheme.Modules.toPresheaf X).obj M
  let H : TopCat.Sheaf Ab (↑X.toPresheafedSpace) := ⟨P, M.isSheaf⟩
  let forgetH := TopCat.Sheaf.forget (Ab.{u}) (↑X.toPresheafedSpace)
  calc
    IsZero M ↔ ∀ x : X, IsZero (((Scheme.Modules.toPresheaf X).obj M).stalk x) := by
      constructor
      · intro h x
        exact Functor.map_isZero (TopCat.Presheaf.stalkFunctor (Ab.{u}) x)
          (Functor.map_isZero (Scheme.Modules.toPresheaf X) h)
      · intro h
        have hH : IsZero H :=
          (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero H).mpr (by
            intro x
            exact h x)
        have hP : IsZero P := Functor.map_isZero forgetH hH
        apply (IsZero.iff_id_eq_zero M).2
        apply (Functor.map_injective (Scheme.Modules.toPresheaf X))
        have hmap0 : (Scheme.Modules.toPresheaf X).map (0 : M ⟶ M) = 0 := by
          ext U s
          rfl
        have hmapid : (Scheme.Modules.toPresheaf X).map (𝟙 M) = 𝟙 P := by
          ext U s
          rfl
        rw [hmapid, hmap0]
        exact (IsZero.iff_id_eq_zero P).mp hP

private lemma supportedSections_stalk_isZero {X : Scheme.{u}} (T : Set X)
    (F : X.Modules) (x : X) (hxT : x ∉ T) :
    IsZero (((Scheme.Modules.toPresheaf X).obj
      (Scheme.Modules.supportedSectionsSubmodule T F).toSheafOfModules).stalk x) := by
  let N := Scheme.Modules.supportedSectionsSubmodule T F
  let P := (Scheme.Modules.toPresheaf X).obj N.toSheafOfModules
  let j : N.toSheafOfModules ⟶ F := N.ι
  let jf := (Scheme.Modules.toPresheaf X).map j
  have hι : Function.Injective ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map jf) :=
    TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
      (f := jf) (by
        intro U s t h
        exact Subtype.ext h) x
  have hzero (a : P.stalk x) : a = 0 := by
    obtain ⟨U, hxU, s, rfl⟩ := P.exists_germ_eq a
    apply hι
    have hs := (Scheme.Modules.mem_supportedSectionsSubmodule_iff T F U s.1).mp
      s.2 x hxU hxT
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change TopCat.Presheaf.germ F.val.presheaf U x hxU s.1 = _
    rw [hs]
    exact (((TopCat.Presheaf.stalkFunctor Ab.{u} x).map jf).hom.map_zero).symm
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩

/-- A monomorphism of sheaves of modules induces monomorphisms on stalks. -/
private lemma mono_stalk_map_of_mono {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G) [Mono f]
    (y : X) : Mono ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).map f) :=
  (AddCommGrpCat.mono_iff_injective _).mpr
    (TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective (f := f.mapPresheaf)
      (fun U => (AddCommGrpCat.mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app _).mp
          (Functor.map_mono (Scheme.Modules.toPresheaf X) f) (Opposite.op U))) y)

/-- A point at which the stalk is a subsingleton is not in the support. -/
private lemma not_mem_supp_of_subsingleton_stalk {X : Scheme.{u}} (M : X.Modules) (y : X)
    (h : Subsingleton
      ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).obj M)) :
    y ∉ SheafOfModules.supp M :=
  fun hy => not_nontrivial_iff_subsingleton.mpr h
    ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).mp hy)

/-- If a monomorphism induces the zero map on the stalk at `y`, then `y` is not in the support
of its source. -/
private lemma not_mem_supp_of_mono_of_stalk_map_eq_zero {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Mono f] (y : X)
    (h : (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y).map f = 0) :
    y ∉ SheafOfModules.supp F := by
  refine not_mem_supp_of_subsingleton_stalk F y ⟨fun a b => ?_⟩
  have := mono_stalk_map_of_mono f y
  apply (AddCommGrpCat.mono_iff_injective _).mp this
  rw [h]
  rfl

private lemma support_subset_of_mono {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Mono f] : SheafOfModules.supp F ⊆ SheafOfModules.supp G := by
  intro x hx
  have hx' := (SheafOfModules.mem_supp_iff_nontrivial_stalk
    (show SheafOfModules X.ringCatSheaf from F) x).mp hx
  exact (SheafOfModules.mem_supp_iff_nontrivial_stalk
    (show SheafOfModules X.ringCatSheaf from G) x).mpr
    (@Function.Injective.nontrivial _ _ hx' _
      ((AddCommGrpCat.mono_iff_injective _).mp (mono_stalk_map_of_mono f x)))

private lemma modules_isLocallySurjective_of_epi {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f.val) := by
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
  intro x
  let S := SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hepi : Epi (show (M : SheafOfModules.{u} X.ringCatSheaf) ⟶ N from f) := ‹Epi f›
  have : Epi (S.map f) := @Functor.map_epi _ _ _ _ S _ _ _ f hepi
  exact (ModuleCat.epi_iff_surjective (S.map f)).mp this

private lemma support_subset_of_epi {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) [Epi f] : SheafOfModules.supp G ⊆ SheafOfModules.supp F := by
  intro x hx
  have hx' := (SheafOfModules.mem_supp_iff_nontrivial_stalk
    (show SheafOfModules X.ringCatSheaf from G) x).mp hx
  let h := (TopCat.Presheaf.stalkFunctor Ab.{u} x).map
    ((Scheme.Modules.toPresheaf X).map f)
  have hsurj : Function.Surjective h.hom :=
    (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp
      (modules_isLocallySurjective_of_epi f) x
  obtain ⟨b, hb⟩ := (nontrivial_iff_exists_ne (0 : _)).mp hx'
  obtain ⟨a, ha⟩ := hsurj b
  have ha0 : a ≠ 0 := by
    intro hz
    apply hb
    rw [← ha, hz]
    exact h.hom.map_zero
  apply (SheafOfModules.mem_supp_iff_nontrivial_stalk
    (show SheafOfModules X.ringCatSheaf from F) x).mpr
  exact (nontrivial_iff_exists_ne (0 : _)).mpr ⟨a, ha0⟩

private lemma supportedSectionsSubmodule_support_subset {X : Scheme.{u}}
    [IsNoetherian X] (T : Set X) (F : X.Modules) [F.IsCoherent] :
    SheafOfModules.supp ((Scheme.Modules.supportedSectionsSubmodule T F).toSheafOfModules) ⊆ T := by
  intro x hx
  by_contra hxT
  exact not_mem_supp_of_subsingleton_stalk _ x
    (AddCommGrpCat.isZero_iff_subsingleton.mp (supportedSections_stalk_isZero T F x hxT)) hx

private lemma torsionModule_support_subset {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F : X.Modules) [F.IsCoherent] :
    SheafOfModules.supp (torsionModule T F) ⊆ T := by
  let N := Scheme.Modules.supportedSectionsSubmodule T F
  have := mono_supportedSectionsSubmodule_ι T F
  let e : (supportedSectionsObject T F : X.Modules) ≅ N.toSheafOfModules :=
    Subobject.underlyingIso N.ι
  have : Mono ((maximalQCSupportedSubobject T F).1.arrow) := by infer_instance
  have : Mono e.hom := ⟨fun {Z} a b h => by
    calc
      a = a ≫ (𝟙 _) := by rw [Category.comp_id]
      _ = a ≫ (e.hom ≫ e.inv) := by rw [e.hom_inv_id]
      _ = b ≫ (e.hom ≫ e.inv) := congrArg (fun k => k ≫ e.inv) h
      _ = b ≫ (𝟙 _) := by rw [e.hom_inv_id]
      _ = b := by rw [Category.comp_id]⟩
  have : Mono ((maximalQCSupportedSubobject T F).1.arrow ≫ e.hom) := by
    refine ⟨fun {Z} a b h => ?_⟩
    have h' : (a ≫ (maximalQCSupportedSubobject T F).1.arrow) ≫ e.hom =
        (b ≫ (maximalQCSupportedSubobject T F).1.arrow) ≫ e.hom := by
      calc
        _ = a ≫ ((maximalQCSupportedSubobject T F).1.arrow ≫ e.hom) := Category.assoc ..
        _ = b ≫ ((maximalQCSupportedSubobject T F).1.arrow ≫ e.hom) := h
        _ = _ := (Category.assoc ..).symm
    exact (cancel_mono ((maximalQCSupportedSubobject T F).1.arrow)).1
      ((cancel_mono e.hom).1 h')
  calc
    SheafOfModules.supp (torsionModule T F) ⊆ SheafOfModules.supp N.toSheafOfModules := by
      exact support_subset_of_mono ((maximalQCSupportedSubobject T F).1.arrow ≫ e.hom)
    _ ⊆ T := by
      exact supportedSectionsSubmodule_support_subset T F

private lemma support_nonempty_of_not_isZero {X : Scheme.{u}}
    (M : X.Modules) (hM : ¬ IsZero M) :
    (SheafOfModules.supp M).Nonempty := by
  by_contra h
  have hempty : SheafOfModules.supp M = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  apply hM
  apply (module_isZero_iff_all_stalks_isZero X M).2
  intro x
  let G : SheafOfModules X.ringCatSheaf := M
  have hx : x ∉ SheafOfModules.supp G := by
    rw [hempty]
    simp
  have hnot : ¬ Nontrivial ((TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf) x) := by
    rw [← SheafOfModules.mem_supp_iff_nontrivial_stalk G x]
    exact hx
  have hsub : Subsingleton (((Scheme.Modules.toPresheaf X).obj M).stalk x) := by
    apply not_nontrivial_iff_subsingleton.mp
    change ¬ Nontrivial ((TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf) x) at hnot
    exact hnot
  apply (IsZero.iff_id_eq_zero _).2
  ext a
  exact hsub.elim _ _

private lemma isZero_of_mono_supported_and_no_associatedPoints
    {X : Scheme.{u}} [IsNoetherian X] (T : Set X)
    (K H : X.Modules) [K.IsCoherent] (f : K ⟶ H) [Mono f]
    (hKsupport : SheafOfModules.supp K ⊆ T)
    (hHass : ∀ x : X, x ∈ T → x ∉ Stacks.Divisors.associatedPoints H)
    (hKnonempty : (SheafOfModules.supp K).Nonempty) : IsZero K := by
  obtain ⟨x, hxK, hxAss⟩ := exists_associatedPoint_of_nonempty_support K hKnonempty
  have hxT : x ∈ T := hKsupport hxK
  have hxH : x ∈ Stacks.Divisors.associatedPoints H :=
    associatedPoints_subset_of_mono f hxAss
  exact (hHass x hxT hxH).elim

private lemma finite_stalk_of_isFiniteType {X : Scheme.{u}}
    (F : X.Modules) [F.IsFiniteType] (x : X) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  SheafOfModules.finite_stalk X.sheaf F x

private lemma associatedPoints_disjoint_of_depth_one
    {X : Scheme.{u}} [IsNoetherian X] (T : Set X) (H : X.Modules)
    (hdepth : ∀ x : X, x ∈ T →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) H.val x
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x))
    (hfinite : ∀ x : X, x ∈ T →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) H.val x
      Module.Finite (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x)) :
    ∀ x : X, x ∈ T → x ∉ Stacks.Divisors.associatedPoints H := by
  intro x hxT hxass
  rw [Stacks.Divisors.mem_associatedPoints_iff] at hxass
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) H.val x
  let : Module.Finite (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) := hfinite x hxT
  exact maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth (hdepth x hxT) hxass

private lemma hom_eq_zero_of_supported_source_and_no_associatedPoints
    {X : Scheme.{u}} [IsNoetherian X] (T : Set X)
    (K H : X.Modules) [K.IsCoherent] [H.IsCoherent] (f : K ⟶ H)
    (hKsupport : SheafOfModules.supp K ⊆ T)
    (hHass : ∀ x : X, x ∈ T → x ∉ Stacks.Divisors.associatedPoints H) : f = 0 := by
  let C := Abelian.coimage f
  let : C.IsCoherent := coimage_isCoherent f
  have hCsupport : SheafOfModules.supp C ⊆ T :=
    (support_subset_of_epi (Abelian.coimage.π f)).trans hKsupport
  have : Mono (Abelian.factorThruCoimage f) := inferInstance
  have hCzero : IsZero C := by
    by_contra hC
    exact hC (isZero_of_mono_supported_and_no_associatedPoints T C H
      (Abelian.factorThruCoimage f) hCsupport hHass
      (support_nonempty_of_not_isZero C hC))
  have hzero : Abelian.factorThruCoimage f = 0 := by
    exact IsZero.eq_of_src hCzero _ _
  rw [← Abelian.coimage.fac f, hzero, comp_zero]

private lemma exists_restriction_eq_zero_of_finitely_many_germs_eq_zero
    {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ U)
    {ι : Type*} (A : Finset ι) (s : ι → Γ(F, U))
    (hs : ∀ i ∈ A, F.presheaf.germ U x hx (s i) = 0) :
    ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ i ∈ A, F.presheaf.map (homOfLE hVU).op (s i) = 0 := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨U, le_rfl, hx, by simp⟩
  | @insert i A hi ih =>
    obtain ⟨V, hVU, hxV, hV⟩ := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
    obtain ⟨W, hxW, hWU, _, hW⟩ := F.presheaf.germ_eq x hx hx (s i) 0
      (by simpa using hs i (Finset.mem_insert_self i A))
    refine ⟨V ⊓ W, inf_le_left.trans hVU, ⟨hxV, hxW⟩, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have h := congrArg (F.presheaf.map (homOfLE (show V ⊓ W ≤ W from inf_le_right)).op) hW
      simp only [← F.presheaf.map_comp_apply, map_zero] at h
      convert h using 1
    · have h := congrArg (F.presheaf.map (homOfLE (show V ⊓ W ≤ V from inf_le_left)).op)
        (hV j hj)
      simp only [← F.presheaf.map_comp_apply, map_zero] at h
      convert h using 1

/-- `PresheafOfModules.germ_smul` restated at the spelling an `X.Modules` presents, so that it
can be rewritten with. -/
private lemma germ_smul_modules {X : Scheme.{u}} (F : X.Modules) (x : X) (U : X.Opens)
    (hx : x ∈ U) (r : Γ(X, U)) (s : Γ(F, U)) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    F.presheaf.germ U x hx (r • s) =
      X.presheaf.germ U x hx r • F.presheaf.germ U x hx s :=
  F.val.germ_smul x U hx r s

private lemma associatedPoint_mem_support_supportedClosure {X : Scheme.{u}}
    [IsNoetherian X] (F : X.Modules) (x : X)
    (hx : Stacks.Divisors.IsAssociatedPoint F x) :
    x ∈ SheafOfModules.supp
      (Scheme.Modules.supportedSectionsSubmodule (closure ({x} : Set X)) F).toSheafOfModules := by
  classical
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  obtain ⟨_, m, hm⟩ := hx
  have hmne : m ≠ 0 := by
    intro h
    have ht : IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊤ := by
      rw [← hm, h]
      simp
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ht
  obtain ⟨U, hxU, hU, s, hsm⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens F.presheaf x m
  let p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨A, hA⟩ := (Ideal.FG.of_isNoetherianRing p)
  have hkill : ∀ r ∈ A, F.presheaf.germ U x hxU (r • s) = 0 := by
    intro r hr
    let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
    let : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
      hU.isLocalization_stalk ⟨x, hxU⟩
    have hrp : r ∈ p := hA ▸ Ideal.subset_span hr
    have hrm : X.presheaf.germ U x hxU r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x) p r).mpr hrp
    have hzero : X.presheaf.germ U x hxU r • m = 0 :=
      Submodule.mem_colon_span_singleton.mp (hm.symm ▸ hrm)
    rw [germ_smul_modules F x U hxU r s, hsm]
    exact hzero
  obtain ⟨V, hVU, hxV, hV⟩ :=
    exists_restriction_eq_zero_of_finitely_many_germs_eq_zero F U x hxU A
      (fun r => r • s) hkill
  let sV : Γ(F, V) := F.presheaf.map (homOfLE hVU).op s
  have hsV : ∀ (y : X) (hy : y ∈ V), y ∉ closure ({x} : Set X) →
      F.presheaf.germ V y hy sV = 0 := by
    intro y hy hycl
    let q := (hU.primeIdealOf ⟨y, hVU hy⟩).asIdeal
    let : Module (X.presheaf.stalk y) (F.presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    let : Algebra Γ(X, U) (X.presheaf.stalk y) :=
      (X.presheaf.germ U y (hVU hy)).hom.toAlgebra
    let : IsLocalization.AtPrime (X.presheaf.stalk y) q :=
      hU.isLocalization_stalk ⟨y, hVU hy⟩
    by_contra hn
    have hpq : p ≤ q := by
      rw [← hA, Ideal.span_le]
      intro r hr
      by_contra hrq
      have hu : IsUnit (X.presheaf.germ U y (hVU hy) r) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y) q r).mpr hrq
      have hz := congrArg (F.presheaf.germ V y hy) (hV r hr)
      have hz' : X.presheaf.germ U y (hVU hy) r • F.presheaf.germ V y hy sV = 0 := by
        dsimp [sV]
        rw [TopCat.Presheaf.germ_res_apply]
        rw [TopCat.Presheaf.germ_res_apply,
          germ_smul_modules F y U (hVU hy) r s, map_zero] at hz
        exact hz
      exact hn (hu.smul_eq_zero.mp hz')
    have hxy : x ⤳ y := by
      have hspec := (PrimeSpectrum.le_iff_specializes
        (hU.primeIdealOf ⟨x, hxU⟩) (hU.primeIdealOf ⟨y, hVU hy⟩)).mp hpq
      simpa only [hU.fromSpec_primeIdealOf] using hspec.map hU.fromSpec.continuous
    exact hycl (specializes_iff_mem_closure.mp hxy)
  let N := Scheme.Modules.supportedSectionsSubmodule (closure ({x} : Set X)) F
  let n : N.toSheafOfModules.val.obj (Opposite.op V) := ⟨sV, hsV⟩
  have hneq : TopCat.Presheaf.germ N.toSheafOfModules.val.presheaf V x hxV n ≠ 0 := by
    intro hn
    have he := TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
      ((Scheme.Modules.toPresheaf X).map N.ι) n
    have hn' : TopCat.Presheaf.germ
        ((Scheme.Modules.toPresheaf X).obj N.toSheafOfModules) V x hxV n = 0 := hn
    have h0 : (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
        ((Scheme.Modules.toPresheaf X).map N.ι)))
        (TopCat.Presheaf.germ ((Scheme.Modules.toPresheaf X).obj N.toSheafOfModules)
          V x hxV n) = 0 := by
      rw [hn']
      exact map_zero _
    have h1 : F.presheaf.germ V x hxV sV = 0 := he.symm.trans h0
    have hmzero : m = 0 := by
      have h2 : F.presheaf.germ U x hxU s = 0 := by
        rw [show (sV : Γ(F, V)) = F.presheaf.map (homOfLE hVU).op s from rfl,
          TopCat.Presheaf.germ_res_apply] at h1
        exact h1
      rw [hsm] at h2
      exact h2
    exact hmne hmzero
  apply (SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mpr
  exact (nontrivial_iff_exists_ne (0 : _)).mpr ⟨_, hneq⟩

/-- A functor that preserves the cokernel of `f` and kills `f` sends the cokernel projection of
`f` to an isomorphism. Stated for opaque categories, so that the proof does not have to see
through the category structure of `X.Modules`. -/
private lemma isIso_map_cokernelπ_of_map_eq_zero {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroMorphisms C] [Limits.HasZeroMorphisms D]
    {A B : C} (f : A ⟶ B) [HasCokernel f]
    (G : C ⥤ D) (hG : Functor.PreservesZeroMorphisms G)
    (hpc : PreservesColimit (parallelPair f 0) G) (hf : G.map f = 0) :
    IsIso (G.map (cokernel.π f)) := by
  have := hG
  have := hpc
  have : IsIso (cokernel.π (G.map f)) := coequalizer.π_of_eq hf
  have : IsIso (G.map (cokernel.π f) ≫ (PreservesCokernel.iso G f).hom) := by
    rw [PreservesCokernel.π_iso_hom]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso G f).hom

private lemma depthOneQuotientCandidateMap_stalk_isIso {X : Scheme.{u}}
    [IsNoetherian X] (T : Set X) (F : X.Modules) [F.IsCoherent]
    (x : X) (hx : x ∉ T) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      (depthOneQuotientCandidateMap T F).mapPresheaf) := by
  let S := SheafOfModules.stalkFunctor X.ringCatSheaf x ⋙
    forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk
      (C := RingCat.{u}) X.ringCatSheaf.obj x)) Ab.{u}
  have hz : IsZero (S.obj (torsionModule T F)) := by
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    apply not_nontrivial_iff_subsingleton.mp
    intro hn
    exact hx (torsionModule_support_subset T F
      ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mpr hn))
  have hf : S.map (torsionModuleι T F) = 0 := hz.eq_of_src _ _
  have h2 : IsIso (cokernel.π (S.map (torsionModuleι T F))) := coequalizer.π_of_eq hf
  have he := PreservesCokernel.π_iso_hom S (torsionModuleι T F)
  have key : IsIso (S.map (cokernel.π (torsionModuleι T F))) := by
    have hcomp : S.map (cokernel.π (torsionModuleι T F)) =
        cokernel.π (S.map (torsionModuleι T F)) ≫
          (PreservesCokernel.iso S (torsionModuleι T F)).inv := by
      rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl
    rw [hcomp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2
      (PreservesCokernel.iso S (torsionModuleι T F)).isIso_inv
  exact key

private lemma coherent_pullback {X : Scheme.{u}} {F G H : X.Modules}
    [F.IsCoherent] [G.IsCoherent] [H.IsCoherent] (f : F ⟶ H) (g : G ⟶ H) :
    (pullback f g).IsCoherent := by
  let P : ObjectProperty X.Modules := fun M => M.IsCoherent
  let : P.IsWeakSerreClass :=
    SheafOfModules.coherentModules_isWeakSerreClass
  have hp : P (F ⊞ G) := P.prop_biprod ‹F.IsCoherent› ‹G.IsCoherent›
  exact P.prop_of_iso
    ((kernelIsKernel (biprod.desc f (-g))).conePointUniqueUpToIso
      (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g))
    (P.prop_kernel (biprod.desc f (-g)) hp ‹H.IsCoherent›)

private lemma factors_through_torsionModule {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F P : X.Modules) [F.IsCoherent] [P.IsQuasicoherent]
    (f : P ⟶ F) (hP : SheafOfModules.supp P ⊆ T) :
    ∃ l : P ⟶ torsionModule T F, l ≫ torsionModuleι T F = f := by
  let N := Scheme.Modules.supportedSectionsSubmodule T F
  let g : P ⟶ N.toSheafOfModules :=
    { val :=
      { app := fun U => ModuleCat.ofHom ((f.val.app U).hom.codRestrict
          (N.toSubmodule.obj U) (by
            intro s x hxU hxT
            have hx : x ∉ SheafOfModules.supp P := fun h => hxT (hP h)
            have hsub : Subsingleton (P.presheaf.stalk x) :=
              not_nontrivial_iff_subsingleton.mp
                (mt (SheafOfModules.mem_supp_iff_nontrivial_stalk P x).mpr hx)
            have hs : P.presheaf.germ U.unop x hxU s = 0 := hsub.elim _ _
            have hh := TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hxU
              f.mapPresheaf s
            refine hh.symm.trans ?_
            rw [hs]
            exact map_zero _))
        naturality := by
          intro U V i
          ext s
          apply Subtype.ext
          exact ConcreteCategory.congr_hom (f.val.naturality i) s } }
  have hg : g ≫ N.ι = f := by ext U s; rfl
  have := mono_supportedSectionsSubmodule_ι T F
  let e : (supportedSectionsObject T F : X.Modules) ≅ N.toSheafOfModules :=
    Subobject.underlyingIso N.ι
  let : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  have hmax := (Classical.choose_spec
    (existsUnique_quasicoherentSubobject X F (supportedSectionsObject T F))).1 P
  obtain ⟨l, hl⟩ := hmax.surjective (g ≫ e.inv)
  change l ≫ (maximalQCSupportedSubobject T F).1.arrow = g ≫ e.inv at hl
  refine ⟨l, ?_⟩
  dsimp [torsionModuleι]
  have h3 : (l ≫ (maximalQCSupportedSubobject T F).1.arrow) ≫
      (supportedSectionsObject T F).arrow = f := by
    rw [hl]
    change (g ≫ (Subobject.underlyingIso N.ι).inv) ≫ (Subobject.mk N.ι).arrow = f
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun m => g ≫ m) (Subobject.underlyingIso_arrow N.ι)).trans hg)
  exact (Category.assoc _ _ _).symm.trans h3

private lemma depthOneQuotientCandidate_not_associated {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (x : X) (hxT : x ∈ T) :
    ¬ Stacks.Divisors.IsAssociatedPoint (depthOneQuotientCandidate T F) x := by
  intro hx
  let Q := depthOneQuotientCandidate T F
  let : Q.IsCoherent := depthOneQuotientCandidate_isCoherent T F
  let q := depthOneQuotientCandidateMap T F
  let : Epi q := depthOneQuotientCandidateMap_epi T F
  let : Q.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent Q).1
  let Z : Set X := closure {x}
  have hZT : Z ⊆ T := by
    intro y hy
    exact hT (specializes_iff_mem_closure.mpr hy) hxT
  let N := Scheme.Modules.supportedSectionsSubmodule Z Q
  have : N.toSheafOfModules.IsQuasicoherent :=
    supportedSectionsSubmodule_isQuasicoherent
      Z isClosed_closure (by intro U hU hc; exact TopologicalSpace.NoetherianSpace.isCompact _) Q
  have hmono : Mono (C := X.Modules) N.ι := mono_supportedSectionsSubmodule_ι Z Q
  have : N.toSheafOfModules.IsCoherent :=
    isCoherent_of_mono N.ι
  let P := pullback q N.ι
  have : P.IsCoherent := coherent_pullback q N.ι
  have : P.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent P).1
  let f : P ⟶ F := pullback.fst q N.ι
  let g : P ⟶ N.toSheafOfModules := pullback.snd q N.ι
  have hP : SheafOfModules.supp P ⊆ T := by
    intro y hy
    by_contra hyT
    let S := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} y
    have : IsIso (S.map q) := depthOneQuotientCandidateMap_stalk_isIso T F y hyT
    have hmf : Mono f := pullback.fst_of_mono (f := q) (g := N.ι)
    have hn : IsZero (S.obj N.toSheafOfModules) :=
      supportedSections_stalk_isZero Z Q y (fun h => hyT (hZT h))
    have hg : S.map g = 0 := hn.eq_of_tgt _ _
    have hf : S.map f = 0 := by
      apply (cancel_mono (S.map q)).mp
      have h := congrArg S.map (pullback.condition (f := q) (g := N.ι))
      simp only [S.map_comp] at h
      have h2 : S.map (pullback.snd q N.ι ≫ N.ι) = 0 :=
        (S.map_comp (pullback.snd q N.ι) N.ι).trans
          ((congrArg (fun m => m ≫ S.map N.ι) hg).trans zero_comp)
      exact h.trans (h2.trans zero_comp.symm)
    exact not_mem_supp_of_mono_of_stalk_map_eq_zero f y hf hy
  obtain ⟨l, hl⟩ := factors_through_torsionModule T F P f hP
  have hf : f ≫ q = 0 := by
    rw [← hl, Category.assoc]
    change l ≫ (torsionModuleι T F ≫ cokernel.π (torsionModuleι T F)) = 0
    rw [cokernel.condition, comp_zero]
  let N' : X.Modules := N.toSheafOfModules
  let g' : P ⟶ N' := g
  let ι' : N' ⟶ Q := N.ι
  have hmono'' : Mono ι' := hmono
  have hgz : g' = 0 := by
    apply (cancel_mono ι').mp
    exact ((pullback.condition (f := q) (g := N.ι)).symm.trans hf).trans zero_comp.symm
  have : Epi g' := Abelian.epi_pullback_of_epi_f q N.ι
  have hN : IsZero N' := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (cancel_epi g').mp
    exact ((congrArg (fun m => m ≫ (𝟙 N')) hgz).trans zero_comp).trans (comp_zero (f := g')).symm
  have hn := (module_isZero_iff_all_stalks_isZero X N.toSheafOfModules).mp hN x
  exact not_mem_supp_of_subsingleton_stalk _ x (AddCommGrpCat.isZero_iff_subsingleton.mp hn)
    (associatedPoint_mem_support_supportedClosure Q x hx)

private lemma depthOneQuotientCandidate_lift {X : Scheme.{u}} [IsNoetherian X]
    (T : Set X) (F H : X.Modules) [F.IsCoherent] [H.IsCoherent] (g : F ⟶ H)
    (hdepth : ∀ x : X, x ∈ T →
      letI : Module (X.presheaf.stalk x) (H.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) H.val x
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (H.presheaf.stalk x)) :
    ∃! l : depthOneQuotientCandidate T F ⟶ H,
      depthOneQuotientCandidateMap T F ≫ l = g := by
  let : H.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent H).2
  have hzero : torsionModuleι T F ≫ g = 0 :=
    hom_eq_zero_of_supported_source_and_no_associatedPoints T (torsionModule T F) H
      (torsionModuleι T F ≫ g) (torsionModule_support_subset T F)
      (associatedPoints_disjoint_of_depth_one T H hdepth
        (fun x _ => finite_stalk_of_isFiniteType H x))
  refine ⟨cokernel.desc _ g hzero, cokernel.π_desc _ _ _, ?_⟩
  intro l hl
  have : Epi (depthOneQuotientCandidateMap T F) :=
    depthOneQuotientCandidateMap_epi T F
  apply (cancel_epi (depthOneQuotientCandidateMap T F)).mp
  exact hl.trans (cokernel.π_desc _ _ _).symm

/-- The conditions of [Stacks, Tag 0DX3] on a map `f : F ⟶ G` of `𝒪_X`-modules: `G` is coherent,
`f` is surjective (an epimorphism of sheaves of modules, equivalently surjective on every stalk),
the stalk map `F_x ⟶ G_x` is an isomorphism for `x ∉ T`, and
`depth_{𝒪_{X,x}}(G_x) ≥ 1` (depth along the maximal ideal of the local ring) for `x ∈ T`. -/
public def IsDepthOneQuotient {X : Scheme.{u}} (T : Set X)
    {F G : X.Modules} (f : F ⟶ G) : Prop :=
  G.IsCoherent ∧ Epi f ∧
    (∀ x : X, x ∉ T → IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      f.mapPresheaf)) ∧
    (∀ x : X, x ∈ T →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x))

private lemma mono_of_depthOneQuotient_source {X : Scheme.{u}} [IsNoetherian X]
    {T : Set X} {F Q G : X.Modules} (q : F ⟶ Q)
    (hq : IsDepthOneQuotient T q) [G.IsCoherent] (l : Q ⟶ G)
    (hl : ∀ x : X, x ∉ T →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map l.mapPresheaf)) :
    Mono l := by
  let : Q.IsCoherent := hq.1
  let : Q.IsQuasicoherent :=
    (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent X Q hq.1).1
  let : Q.IsFiniteType :=
    (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent X Q hq.1).2
  let : G.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
  let : G.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).2
  let : (kernel l).IsCoherent := SheafOfModules.kernel_isCoherent l
  apply Abelian.mono_of_kernel_ι_eq_zero
  apply hom_eq_zero_of_supported_source_and_no_associatedPoints T (kernel l) Q
  · intro x hx
    by_contra hxT
    let S := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
    have : IsIso (S.map l) := hl x hxT
    have hz : S.map (kernel.ι l) = 0 := by
      apply (cancel_mono (S.map l)).mp
      rw [← S.map_comp, kernel.condition, S.map_zero, zero_comp]
    exact not_mem_supp_of_mono_of_stalk_map_eq_zero (kernel.ι l) x hz hx
  · exact associatedPoints_disjoint_of_depth_one T Q hq.2.2.2
      (fun x _ => finite_stalk_of_isFiniteType Q x)

/-- Existence of a depth-one quotient along a specialization-closed set, with
the universal property of quotienting by sections supported on that set. -/
public theorem exists_depthOneQuotient (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] :
    ∃ (G : X.Modules) (f : F ⟶ G), IsDepthOneQuotient T f ∧
      ∀ (H : X.Modules) (_ : H.IsCoherent) (g : F ⟶ H),
        (∀ x : X, x ∈ T →
          letI : Module (X.presheaf.stalk x)
              (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) :=
            PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
              (R := X.presheaf) H.val x
          (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
            (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x)) →
        ∃! l : G ⟶ H, f ≫ l = g := by
  refine ⟨depthOneQuotientCandidate T F, depthOneQuotientCandidateMap T F,
    ⟨inferInstance, depthOneQuotientCandidateMap_epi T F,
      depthOneQuotientCandidateMap_stalk_isIso T F, ?_⟩, ?_⟩
  · intro x hx
    let Q := depthOneQuotientCandidate T F
    let : Q.IsCoherent := depthOneQuotientCandidate_isCoherent T F
    let : Q.IsFiniteType :=
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent Q).2
    let : Module (X.presheaf.stalk x) (Q.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) Q.val x
    have := finite_stalk_of_isFiniteType Q x
    by_contra hn
    have hz : Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (Q.presheaf.stalk x) = 0 :=
      Order.lt_one_iff.mp (not_le.mp hn)
    have ha := Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes.mp hz
    obtain ⟨hp, m, hm⟩ := isAssociatedPrime_iff.mp ha
    apply depthOneQuotientCandidate_not_associated T hT F x hx
    exact ⟨hp, m, Submodule.colon_span.trans hm.symm⟩
  · intro H hH g hdepth
    let := hH
    exact depthOneQuotientCandidate_lift T F H g hdepth

/-- The canonical depth-one quotient of a coherent module along `T`. -/
public noncomputable def depthOneQuotient (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] : X.Modules :=
  Classical.choose (exists_depthOneQuotient X T hT F)

/-- The canonical map onto the depth-one quotient. -/
public noncomputable def toDepthOneQuotient (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] : F ⟶ depthOneQuotient X T hT F :=
  Classical.choose (Classical.choose_spec (exists_depthOneQuotient X T hT F))

/-- The canonical quotient is coherent, surjective, unchanged away from `T`,
and of depth at least one along `T`. -/
@[stacks 0DX3 "depth_one_quotient"]
public theorem depthOneQuotient_spec (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] :
    IsDepthOneQuotient T (toDepthOneQuotient X T hT F) := by
  exact (Classical.choose_spec
    (Classical.choose_spec (exists_depthOneQuotient X T hT F))).1

/-- Every map to a coherent sheaf of depth at least one along `T` factors
uniquely through the depth-one quotient. No epimorphy or isomorphism condition
on the map to the target is needed. -/
public theorem depthOneQuotient_lift (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent]
    (G : X.Modules) [G.IsCoherent] (g : F ⟶ G)
    (hG : ∀ x : X, x ∈ T →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) :
    ∃! l : depthOneQuotient X T hT F ⟶ G,
      toDepthOneQuotient X T hT F ≫ l = g := by
  exact (Classical.choose_spec
    (Classical.choose_spec (exists_depthOneQuotient X T hT F))).2 G inferInstance g hG

/-- Every other quotient satisfying the defining properties is uniquely
isomorphic to the canonical one over its source. The form with the conditions of
[Stacks, Tag 0DX3] spelled out is `AlgebraicGeometry.depthOneQuotient_unique_of_epi_of_depth`. -/
public theorem depthOneQuotient_unique (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent]
    (G : X.Modules) (g : F ⟶ G) (hg : IsDepthOneQuotient T g) :
    ∃! e : depthOneQuotient X T hT F ≅ G,
      toDepthOneQuotient X T hT F ≫ e.hom = g := by
  let : G.IsCoherent := hg.1
  let : Epi g := hg.2.1
  let q := toDepthOneQuotient X T hT F
  have hq := depthOneQuotient_spec X T hT F
  let : Epi q := hq.2.1
  obtain ⟨l, hl, hluniq⟩ := depthOneQuotient_lift X T hT F G g hg.2.2.2
  have : Epi l := epi_of_epi_fac hl
  have : Mono l := mono_of_depthOneQuotient_source q hq l (by
    intro x hx
    let S := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
    have : IsIso (S.map q) := hq.2.2.1 x hx
    have : IsIso (S.map g) := hg.2.2.1 x hx
    have he : S.map q ≫ S.map l = S.map g := by
      rw [← S.map_comp]
      exact congrArg S.map hl
    have he' : S.map l = inv (S.map q) ≫ S.map g := by
      rw [← he, IsIso.inv_hom_id_assoc]
    change IsIso (S.map l)
    rw [he']
    infer_instance)
  have : IsIso l := isIso_of_mono_of_epi l
  refine ⟨asIso l, hl, ?_⟩
  intro e he
  apply Iso.ext
  exact hluniq e.hom he

/-- **Stacks Project, Tag 0DX3**, uniqueness. Let `X` be a Noetherian scheme, `T ⊆ X` stable under
specialization and `F` a coherent `𝒪_X`-module. If `g : F ⟶ G` is a surjection onto a coherent
module `G` such that the stalk map `F_x ⟶ G_x` is an isomorphism for `x ∉ T` and
`depth_{𝒪_{X,x}}(G_x) ≥ 1` for `x ∈ T`, then `G` is identified with the canonical depth-one
quotient `depthOneQuotient X T hT F` by a unique isomorphism over `F`. -/
@[stacks 0DX3 "depth_one_quotient"]
public theorem depthOneQuotient_unique_of_epi_of_depth (X : Scheme.{u}) [IsNoetherian X]
    (T : Set X) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent]
    (G : X.Modules) [G.IsCoherent] (g : F ⟶ G) [Epi g]
    (hstalk : ∀ x : X, x ∉ T → IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      g.mapPresheaf))
    (hdepth : ∀ x : X, x ∈ T →
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) G.val x
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x)) :
    ∃! e : depthOneQuotient X T hT F ≅ G,
      toDepthOneQuotient X T hT F ≫ e.hom = g :=
  depthOneQuotient_unique X T hT F G g ⟨inferInstance, inferInstance, hstalk, hdepth⟩

end AlgebraicGeometry

end
