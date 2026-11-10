module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sober
public import StacksCore.Topology.NowhereDense.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Coherent
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.CardinalGeneration.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Embedded
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Serre
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.NowhereDense
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.SupportedSections.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSections
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGenerated
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGeneratedSmall
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LargestSubsheaf
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.Topology.Sheaves.Modules.Support
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule

/-!
# Removing the nowhere dense part of a coherent sheaf

On a locally Noetherian scheme, the coherent subsheaves of a coherent sheaf `F` whose
supports are nowhere dense in the support of `F` have a greatest member `K`. The quotient
`F / K` has the same support as `F`, has no embedded associated points, and agrees with `F`
on a dense open subset. This is [Stacks, Tag 02OL].

## Main definitions

* `Stacks.AlgebraicGeometry.CoherentSubquotients.IsNowhereDenseCoherentSubobject`: the
  property of a subobject of `F` picked out by the maximality assertion — it is coherent and
  its support is nowhere dense in the support of `F`.

## Main results

* `Stacks.AlgebraicGeometry.CoherentSubquotients.exists_greatest_isNowhereDenseCoherentSubobject`:
  the greatest such subsheaf exists.
* `Stacks.AlgebraicGeometry.CoherentSubquotients.supp_cokernel_eq`: the quotient by it has the
  same support as `F`.
* `Stacks.AlgebraicGeometry.CoherentSubquotients.cokernel_hasNoEmbeddedAssociatedPoints`: the
  quotient has no embedded associated points.
* `Stacks.AlgebraicGeometry.CoherentSubquotients.exists_denseOpen_cokernel_iso`: the quotient
  map is an isomorphism on sections over every open contained in some dense open.

## Implementation notes

Subsheaves are subobjects in the category of sheaves of modules, and the quotient is the
cokernel of the subobject inclusion; nowhere denseness is taken in the subspace topology on
the support of `F`. The last assertion is stated as an isomorphism on sections over every
open below the selected dense open, which is what pins down the identification of the two
restrictions.

`AlgebraicGeometry.Scheme.Modules` is a definition unfolding to `SheafOfModules` over the
structure sheaf, and its categorical instances are copies of the ones on `SheafOfModules`.
Instance search cannot see through that copy, so goals that print identically can be
unsolvable in one spelling and immediate in the other. Three devices appear throughout:
functors into `ModuleCat` are ascribed with `X.Modules` as their domain, so that `Functor.map`
and the composition it is applied to agree; morphisms whose type is handed over from
`SheafOfModules` (the inclusion of a submodule sheaf, say) are re-bound at `X.Modules` with an
explicit type; and the monomorphism and epimorphism predicates are transported between the two
readings by `mono_sheafOfModules` and `epi_sheafOfModules`, which do it by hand from the
cancellation property.

## References

* [Stacks Project, Tag 02OL](https://stacks.math.columbia.edu/tag/02OL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.CoherentSubquotients


/-- A monomorphism of modules on a scheme, read in the category of sheaves of modules over
the structure sheaf. `AlgebraicGeometry.Scheme.Modules` is a definition whose category
instance is a copy of the one on `SheafOfModules`, so the two readings of `Mono f` are not
interchangeable by instance search. -/
private theorem mono_sheafOfModules {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    @Mono (SheafOfModules.{u} X.ringCatSheaf) (inferInstance) M N f :=
  ⟨fun g h hcomp => (‹Mono f›).right_cancellation g h hcomp⟩

/-- The forgetful functor to sheaves of abelian groups preserves monomorphisms, being left
exact. -/
private theorem mono_toSheaf_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := by
  have hm : @Mono (SheafOfModules.{u} X.ringCatSheaf) (inferInstance) M N f :=
    mono_sheafOfModules f
  have hlim : PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf) := inferInstance
  exact CategoryTheory.preserves_mono_of_preservesLimit (SheafOfModules.toSheaf X.ringCatSheaf) f

/-- Zero morphisms between modules on a scheme, named so that instance search finds it in one
step. `AlgebraicGeometry.Scheme.Modules` reaches `HasZeroMorphisms` only through its abelian
structure, and that search does not terminate within the project's `maxSynthPendingDepth`
inside a long proof. -/
private instance hasZeroMorphisms_modules (X : Scheme.{u}) : HasZeroMorphisms X.Modules :=
  inferInstance

/-- The kernel inclusion of a morphism of modules on a scheme is a monomorphism. Named so
that instance search finds it as a local hypothesis: inside a long proof the search for this
goal does not terminate within the project's `maxSynthPendingDepth`. -/
private theorem mono_kernel_ι {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    Mono (kernel.ι f) :=
  inferInstance

/-- An epimorphism of modules on a scheme, read in the category of sheaves of modules over
the structure sheaf; see `mono_sheafOfModules`. -/
private alias epi_sheafOfModules := AlgebraicGeometry.Scheme.Modules.epi_sheafOfModules

/-- Taking stalks preserves epimorphisms, being a colimit-preserving functor. The
colimit-preservation is passed explicitly because it is not a global instance. -/
private theorem epi_stalkFunctor_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Epi f]
    (x : X)
    (hT : PreservesColimits
      (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x)) :
    Epi ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f) := by
  have he : @Epi (SheafOfModules.{u} X.ringCatSheaf) (inferInstance) M N f := epi_sheafOfModules f
  exact CategoryTheory.preserves_epi_of_preservesColimit
    (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x) f

/-- Taking stalks of the underlying sheaf of abelian groups preserves monomorphisms. The
monomorphism is passed explicitly: `TopCat.Sheaf` and `Sheaf (Opens.grothendieckTopology _)`
are the same category with different instance paths, so instance search does not see it. -/
private theorem mono_stalk_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) [Mono f] (x : X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map f).hom) :=
  (TopCat.Presheaf.mono_iff_stalk_mono ((SheafOfModules.toSheaf X.ringCatSheaf).map f)).mp
    (mono_toSheaf_map f) x

/-- A monomorphism of modules on a scheme is injective on stalks. -/
private theorem injective_stalkFunctor_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [Mono f] (x : X) :
    Function.Injective ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f) :=
  (AddCommGrpCat.mono_iff_injective _).mp (mono_stalk_map f x)

/-- Taking stalks as a module over the stalk of the structure sheaf preserves
monomorphisms. -/
theorem mono_stalkFunctor_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [Mono f] (x : X) :
    Mono ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).map f) :=
  (ModuleCat.mono_iff_injective _).mpr (injective_stalkFunctor_map f x)

private alias support_eq_nontrivial_stalks :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.supp_eq_setOf_nontrivial_stalk

private lemma nontrivial_stalk_of_mem_support {X : Scheme.{u}} (M : X.Modules)
    {x : X} (hx : x ∈ (⟨M.val, M.isSheaf⟩ :
      RingedSpace.ModuleSheaf X.toRingedSpace).supp) :
    Nontrivial ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj M) := by
  rwa [support_eq_nontrivial_stalks] at hx

private alias support_subobject_subset :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.supp_subobject_subset_supp

private theorem moduleSheaf_toSheaf_preservesColimits {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    PreservesColimits (SheafOfModules.toSheaf.{u,u,u,u} O) := by
  let F := PresheafOfModules.sheafification (𝟙 O.obj)
  let adj : F ⊣ _ := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  have hF : PreservesColimits F := adj.leftAdjoint_preservesColimits
  have hP : PreservesColimits (PresheafOfModules.toPresheaf O.obj) := inferInstance
  have hS : PreservesColimits
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).leftAdjoint_preservesColimits
  have hFT : PreservesColimits (F ⋙ SheafOfModules.toSheaf O) :=
    preservesColimits_of_natIso (PresheafOfModules.sheafificationCompToSheaf (𝟙 O.obj)).symm
  refine ⟨?_⟩
  intro J _
  refine ⟨?_⟩
  intro D
  refine ⟨?_⟩
  intro c hc
  let G := SheafOfModules.forget O ⋙ PresheafOfModules.restrictScalars (𝟙 O.obj)
  have e : (D ⋙ G) ⋙ F ≅ D :=
    NatIso.ofComponents (fun j => (asIso adj.counit).app (D.obj j))
      (fun f => (asIso adj.counit).hom.naturality (D.map f))
  have h1 : PreservesColimit (D ⋙ G) F := hF.preservesColimitsOfShape.preservesColimit
  have h2 : PreservesColimit (D ⋙ G) (F ⋙ SheafOfModules.toSheaf O) :=
    hFT.preservesColimitsOfShape.preservesColimit
  have hpc : PreservesColimit ((D ⋙ G) ⋙ F) (SheafOfModules.toSheaf O) :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (D ⋙ G)))
      (isColimitOfPreserves (F ⋙ SheafOfModules.toSheaf O) (colimit.isColimit (D ⋙ G)))
  have hD := preservesColimit_of_iso_diagram (SheafOfModules.toSheaf O) e
  exact ⟨isColimitOfPreserves (SheafOfModules.toSheaf O) hc⟩

private theorem moduleSheaf_stalk_preservesColimits {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) :
    PreservesColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor O x) := by
  let G := forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk
    (C := RingCat.{u}) (X := X) O.obj x)) AddCommGrpCat.{u}
  have h : PreservesColimits
      (AlgebraicGeometry.SheafOfModules.stalkFunctor O x ⋙ G) := by
    change PreservesColimits ((SheafOfModules.toSheaf O ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} X) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    have hM : PreservesColimits (SheafOfModules.toSheaf.{u,u,u,u} O) :=
      moduleSheaf_toSheaf_preservesColimits O
    have hS : PreservesColimitsOfSize.{u,u}
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by infer_instance
    have hs' : PreservesColimitsOfSize.{u,u,u,u,u+1,u+1}
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := hS
    change PreservesColimits (SheafOfModules.toSheaf O ⋙
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))
    exact @comp_preservesColimits.{u,u,u,u,u,u+1,u+1,u+1}
      _ _ _ _ _ _ (SheafOfModules.toSheaf O)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) hM hs'
  have hr : ReflectsColimits G := ⟨fun {J} _ => inferInstance⟩
  exact preservesColimits_of_reflects_of_preserves
    (AlgebraicGeometry.SheafOfModules.stalkFunctor O x) G

private alias moduleCat_zero_colimit := Stacks.AlgebraicGeometry.EmbeddedPoints.isZero_colimit

private alias stalk_sSup_isZero :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.isZero_stalkFunctor_obj_sSup

private lemma stalk_cokernel_π_isIso_of_isZero
    {C : Type (u + 1)} [CategoryTheory.Category.{u, u + 1} C] [Preadditive C]
    [CategoryTheory.Limits.HasZeroObject C]
    {D : Type (u + 1)} [CategoryTheory.Category.{u, u + 1} D] [Preadditive D]
    [CategoryTheory.Limits.HasZeroObject D]
    (T : C ⥤ D) [T.PreservesZeroMorphisms] [PreservesColimits T]
    {A B : C} (f : A ⟶ B) [HasCokernel f] (hA : IsZero (T.obj A)) :
    IsIso (T.map (cokernel.π f)) := by
  have hf : T.map f = 0 := hA.eq_of_src _ _
  have hcomp : IsIso (T.map (cokernel.π f) ≫ (PreservesCokernel.iso T f).hom) := by
    rw [PreservesCokernel.π_iso_hom (G := T) (f := f)]
    exact cokernel.π_of_zero hf
  exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso T f).hom

private alias subsingleton_of_isZero_module :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.subsingleton_of_isZero

private lemma stalk_cokernel_π_isZero_of_isZero_target
    {C : Type (u + 1)} [CategoryTheory.Category.{u, u + 1} C] [Preadditive C]
    {D : Type (u + 1)} [CategoryTheory.Category.{u, u + 1} D] [Preadditive D]
    (T : C ⥤ D) [T.PreservesZeroMorphisms] [PreservesColimits T]
    {A B : C} (f : A ⟶ B) [HasCokernel f]
    (hB : IsZero (T.obj B)) : IsZero (T.obj (cokernel f)) := by
  have hπ : IsIso (cokernel.π (T.map f)) := cokernel.π_of_zero (hB.eq_of_tgt _ _)
  exact (hB.of_iso (asIso (cokernel.π (T.map f))).symm).of_iso (PreservesCokernel.iso T f)

private alias support_cokernel_subset :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.supp_cokernel_subset_supp

private alias mem_support_cokernel_of_mem_support_of_not_mem_support :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.mem_supp_cokernel_of_mem_supp_of_notMem_supp

/-- **[Stacks, Tag 02OL].** A subobject of `F` is a *nowhere dense coherent subobject* when it
is coherent and its support is nowhere dense in the support of `F`. These are the subsheaves
over which the maximality assertion of the tag quantifies. -/
public def IsNowhereDenseCoherentSubobject {X : Scheme.{u}} (F : X.Modules)
    (K : Subobject F) : Prop :=
  (K : X.Modules).IsCoherent ∧
    IsNowhereDense
      {x : ↥((⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) |
        (x : X) ∈
      (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
            RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp}

private lemma support_closed_of_coherent_module {X : Scheme.{u}}
    [IsLocallyNoetherian X] (M : X.Modules) [M.IsCoherent] :
    IsClosed ((⟨M.val, M.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) := by
  have hMqcft : M.IsQuasicoherent ∧ M.IsFiniteType :=
    ((Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae X M).out 1 2).mp
      (inferInstance : M.IsCoherent)
  let M' : SheafOfModules
      ((sheafCompose (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.toRingedSpace.sheaf) := M
  have : M'.IsFiniteType := hMqcft.2
  have h := SheafOfModules.isClosed_supp M'
  rw [← SheafOfModules.supp_eq_moduleSheaf_supp (F := M')] at h
  simpa [M', AlgebraicGeometry.SheafOfModules.moduleSheafOfModules] using h

/-- A stalk map of a monomorphism that vanishes at `y` shows `y` is outside the support of its
source. -/
private lemma notMem_support_of_stalk_map_eq_zero {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) [Mono f] {y : X}
    (h : (AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y).map f = 0) :
    y ∉ (⟨M.val, M.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp := fun hy =>
  not_nontrivial_iff_subsingleton.mpr
    ⟨fun a b => injective_stalkFunctor_map f y (by rw [h]; simp)⟩
    (nontrivial_stalk_of_mem_support M hy)

private lemma affine_section_mem_supportedSections_closure
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (s : Γ(F, U)) (hs : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon
      (Submodule.span Γ(X, U) {s}) = (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    s ∈ (AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule
      (closure ({x} : Set X)) F).toSubmodule.obj (op U) := by
  rw [AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_iff]
  intro z hz hznot
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let q := (hU.primeIdealOf ⟨z, hz⟩).asIdeal
  have hpq : ¬ p ≤ q := by
    intro hpq
    apply hznot
    apply specializes_iff_mem_closure.mp
    have hle : hU.primeIdealOf ⟨x, hx⟩ ≤ hU.primeIdealOf ⟨z, hz⟩ :=
      hpq
    have hspec := (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mpr
      ((PrimeSpectrum.le_iff_specializes _ _).mp hle)
    simpa only [hU.fromSpec_primeIdealOf] using hspec
  obtain ⟨r, hrp, hrq⟩ := Set.not_subset.mp hpq
  have hrkill : r • s = 0 := by
    have hr : r ∈ (⊥ : Submodule Γ(X, U) Γ(F, U)).colon
        (Submodule.span Γ(X, U) {s}) := by
      rw [hs]
      exact hrp
    simpa only [Submodule.mem_colon_span_singleton, Submodule.mem_bot] using hr
  let : Algebra Γ(X, U) (X.presheaf.stalk z) :=
    (X.presheaf.germ U z hz).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk z) q :=
    hU.isLocalization_stalk ⟨z, hz⟩
  have hu : IsUnit ((algebraMap (Γ(X, U)) (X.presheaf.stalk z)) r) :=
    IsLocalization.map_units (X.presheaf.stalk z) (⟨r, hrq⟩ : q.primeCompl)
  have hz0 : (X.presheaf.germ U z hz).hom r •
      TopCat.Presheaf.germ F.val.presheaf U z hz s = 0 :=
    ((PresheafOfModules.germ_smul F.val z U hz r s).symm.trans
        (congrArg (fun t => TopCat.Presheaf.germ F.val.presheaf U z hz t) hrkill)).trans
      (map_zero (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf U z hz)))
  have halg : (X.presheaf.germ U z hz).hom r =
      (algebraMap (Γ(X, U)) (X.presheaf.stalk z)) r := rfl
  rw [halg] at hz0
  exact hu.smul_eq_zero.mp hz0

private def affineSupportHomeomorph {X : Type*} [TopologicalSpace X]
    (U S : Set X) :
    {u : ↥U // (u : X) ∈ S} ≃ₜ {x : ↥S // (x : X) ∈ U} where
  toEquiv := {
    toFun := fun u => ⟨⟨u.1.1, u.2⟩, u.1.2⟩
    invFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    change Continuous (fun z : {u : ↥U // (u : X) ∈ S} => (z.1.1 : X))
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    change Continuous (fun z : {x : ↥S // (x : X) ∈ U} => (z.1.1 : X))
    exact continuous_subtype_val.comp continuous_subtype_val

/-- A generic point of an irreducible component of a Noetherian space is carried by an open
embedding outside every closed nowhere dense subset of the target: the component contains a
nonempty open subset, whose image would then lie in the empty interior. -/
alias genericPoint_not_mem_nowhereDense :=
    Stacks.AlgebraicGeometry.EmbeddedPoints.notMem_of_isGenericPoint_of_isNowhereDense

/-- On a locally Noetherian scheme, the generic point of an irreducible component avoids every
closed nowhere dense subset. The space itself need not be Noetherian, so the previous lemma is
applied on an affine open neighbourhood of the point, where it is: the component meets that
open in an irreducible component of it, of which the point is still generic. -/
theorem genericPoint_notMem_of_nowhereDense (X : Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] {Z T : Set X} {x : X}
    (hZ : Z ∈ irreducibleComponents X) (hx : IsGenericPoint x Z)
    (hT : IsClosed T) (hT' : IsNowhereDense T) : x ∉ T := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by trivial)
  have _ : IsNoetherianRing Γ(X, U) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hNoeth : NoetherianSpace ↥(U : Set X) :=
    AlgebraicGeometry.noetherianSpace_of_isAffineOpen U hU
  have hxU' : x ∈ (U : Set X) := hxU
  have hZU : Subtype.val ⁻¹' Z ∈ irreducibleComponents ↥(U : Set X) :=
    preimage_mem_irreducibleComponents hZ U.isOpen.isOpenEmbedding_subtypeVal
      ⟨x, hx.mem, ⟨⟨x, hxU'⟩, rfl⟩⟩
  have hgen : IsGenericPoint (⟨x, hxU'⟩ : ↥(U : Set X)) (Subtype.val ⁻¹' Z) := by
    change closure {(⟨x, hxU'⟩ : ↥(U : Set X))} = Subtype.val ⁻¹' Z
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Set.image_singleton, hx.def]
  exact genericPoint_not_mem_nowhereDense Subtype.val
    U.isOpen.isOpenEmbedding_subtypeVal hT hT' hZU hgen

private lemma exists_largest_quasicoherent_subobject {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] (G : Subobject F) :
    ∃ L : Subobject F, L ≤ G ∧ (L : X.Modules).IsQuasicoherent ∧
      ∀ P : Subobject F, P ≤ G → (P : X.Modules).IsQuasicoherent → P ≤ L := by
  obtain ⟨H, hH, _⟩ := AlgebraicGeometry.existsUnique_quasicoherentSubobject X F G
  let L : Subobject F := (Subobject.map G.arrow).obj H.1
  have hL : L = Subobject.mk (H.1.arrow ≫ G.arrow) := by
    dsimp [L]
    rw [← Subobject.map_mk, Subobject.mk_arrow]
  have hLqc : (L : X.Modules).IsQuasicoherent := by
    rw [hL]
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (H.1.arrow ≫ G.arrow)).symm H.2
  have hLG : L ≤ G := by
    rw [hL]
    apply Subobject.le_of_comm
      ((Subobject.underlyingIso (H.1.arrow ≫ G.arrow)).hom ≫ H.1.arrow)
    simp [Category.assoc]
  refine ⟨L, hLG, hLqc, ?_⟩
  intro P hPG hPqc
  let f₀ := Subobject.ofLE P G hPG
  obtain ⟨f, hf⟩ := (hH (P : X.Modules)).2 f₀
  change f ≫ H.1.arrow = f₀ at hf
  have hcomp : f ≫ H.1.arrow ≫ G.arrow = P.arrow := by
    rw [← Category.assoc, hf]
    exact Subobject.ofLE_arrow hPG
  rw [hL]
  apply Subobject.le_of_comm (f ≫ (Subobject.underlyingIso (H.1.arrow ≫ G.arrow)).inv)
  rw [Category.assoc, Subobject.underlyingIso_arrow, hcomp]

private lemma stalk_sSup_isZero_of_isGenericPoint {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) {V : Type*} [TopologicalSpace V] [NoetherianSpace V]
    {e : V → ↥((⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp)}
    (he : Topology.IsOpenEmbedding e) {Z : Set V} (hZ : Z ∈ irreducibleComponents V)
    {y : V} (hy : IsGenericPoint y Z) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf (e y : X)).obj
      ((sSup {L | IsNowhereDenseCoherentSubobject F L} : Subobject F) : X.Modules)) := by
  refine stalk_sSup_isZero F _ (e y : X) fun L hL => ?_
  have : (L : X.Modules).IsCoherent := hL.1
  refine ModuleCat.isZero_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp fun hnon => ?_)
  apply genericPoint_not_mem_nowhereDense e he
    ((support_closed_of_coherent_module (L : X.Modules)).preimage continuous_subtype_val)
    hL.2 hZ hy
  change (e y : X) ∈ (⟨(L : X.Modules).val, (L : X.Modules).isSheaf⟩ :
    RingedSpace.ModuleSheaf X.toRingedSpace).supp
  rwa [support_eq_nontrivial_stalks]

private lemma isNowhereDense_supp_of_le_sSup {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (K : Subobject F) [(K : X.Modules).IsCoherent]
    (hKG : K ≤ sSup {L | IsNowhereDenseCoherentSubobject F L}) :
    IsNowhereDense
      {x : ↥((⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) |
        (x : X) ∈ (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
          RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp} := by
  let SF : Set X := (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let SK : Set X := (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
    RingedSpace.ModuleSheaf X.toRingedSpace).supp
  have hRelClosed : IsClosed {x : ↥SF | (x : X) ∈ SK} :=
    (support_closed_of_coherent_module (K : X.Modules)).preimage continuous_subtype_val
  apply hRelClosed.isNowhereDense_iff.mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_interior.mp hx
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := (x : X)) (by simp)
  let V : Set U := {z | z.1 ∈ SF}
  have hVclosed : IsClosed V := by
    change IsClosed (Subtype.val ⁻¹' SF)
    exact (support_closed_of_coherent_module F).preimage continuous_subtype_val
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  have : QuasiSober V := hVclosed.isClosedEmbedding_subtypeVal.quasiSober
  let z : V := ⟨⟨(x : X), hxU⟩, (x : ↥SF).property⟩
  let Z : Set V := irreducibleComponent z
  have hZ : Z ∈ irreducibleComponents V := irreducibleComponent_mem_irreducibleComponents z
  let y : V := hZ.1.genericPoint
  have hy : IsGenericPoint y Z := hZ.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents Z hZ)
  let e₀ : V ≃ₜ {q : ↥SF // (q : X) ∈ U} := affineSupportHomeomorph (U : Set X) SF
  let e : V → ↥SF := fun q => (e₀ q).1
  have he : Topology.IsOpenEmbedding e := by
    have hUrel : IsOpen {q : ↥SF | (q : X) ∈ U} := U.2.preimage continuous_subtype_val
    change Topology.IsOpenEmbedding ((Subtype.val : {q : ↥SF // (q : X) ∈ U} → ↥SF) ∘ e₀)
    exact hUrel.isOpenEmbedding_subtypeVal.comp e₀.isOpenEmbedding
  have hyW : y ∈ e ⁻¹' W := by
    apply hy.mem_open_set_iff (hWopen.preimage he.continuous) |>.2
    refine ⟨z, mem_irreducibleComponent, ?_⟩
    change e z ∈ W
    rw [show e z = x from Subtype.ext rfl]
    exact hxW
  have hGzero := stalk_sSup_isZero_of_isGenericPoint F he hZ hy
  let T : X.Modules ⥤ ModuleCat.{u} _ :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf (e y : X)
  have hTG : T.map (sSup {L | IsNowhereDenseCoherentSubobject F L} : Subobject F).arrow = 0 :=
    hGzero.eq_of_src _ _
  have hmapzero : T.map K.arrow = 0 := by
    rw [← Subobject.ofLE_arrow hKG, Functor.map_comp, hTG, comp_zero]
  exact notMem_support_of_stalk_map_eq_zero K.arrow hmapzero (hWsub hyW)

/-- For a nowhere dense coherent subobject `K` of `F`, the points of the support of `F` outside
the support of `K` are dense in the support of `F`. -/
private lemma dense_support_diff_of_isNowhereDenseCoherentSubobject {X : Scheme.{u}}
    [IsLocallyNoetherian X] {F : X.Modules} (K : Subobject F)
    (hK : IsNowhereDenseCoherentSubobject F K) :
    Dense {x : ↥((⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) |
      (x : X) ∉ (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp} := by
  have : (K : X.Modules).IsCoherent := hK.1
  exact (isClosed_isNowhereDense_iff_compl.mp ⟨(support_closed_of_coherent_module
    (K : X.Modules)).preimage continuous_subtype_val, hK.2⟩).2

/-- **[Stacks, Tag 02OL].** Among the coherent subsheaves of a coherent sheaf `F` on a locally
Noetherian scheme whose support is nowhere dense in the support of `F` there is a greatest
one. -/
@[stacks 02OL "greatest subsheaf"]
public theorem exists_greatest_isNowhereDenseCoherentSubobject
    {X : Scheme.{u}} [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] :
    ∃ K : Subobject F,
      IsNowhereDenseCoherentSubobject F K ∧
        ∀ L : Subobject F, IsNowhereDenseCoherentSubobject F L → L ≤ K := by
  classical
  let S : Set (Subobject F) := {L | IsNowhereDenseCoherentSubobject F L}
  have : F.IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ F inferInstance
  obtain ⟨K, hKG, hKqc, hKmax⟩ := exists_largest_quasicoherent_subobject F (sSup S)
  have hKcoh : (K : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono K.arrow
  refine ⟨K, ⟨hKcoh, isNowhereDense_supp_of_le_sSup F K hKG⟩, fun L hL => ?_⟩
  exact hKmax L (Subobject.le_sSup S L hL) (@_root_.isQuasicoherent_of_isCoherent _ _ _ _ hL.1)

/-- **[Stacks, Tag 02OL], part (1).** The quotient of `F` by a coherent subsheaf with nowhere
dense support has the same support as `F`. -/
@[stacks 02OL "part (1): support of the quotient"]
public theorem supp_cokernel_eq {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (K : Subobject F)
    (hK : IsNowhereDenseCoherentSubobject F K) :
    (⟨(cokernel K.arrow).val, (cokernel K.arrow).isSheaf⟩ :
      RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp =
      (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp := by
  classical
  let Q : X.Modules := cokernel K.arrow
  let SF : Set X :=
    (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let SK : Set X := (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
    RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let SQ := (⟨Q.val, Q.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  have : (K : X.Modules).IsCoherent := hK.1
  have : (K : X.Modules).IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ _ hK.1
  have : F.IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ F inferInstance
  have : Q.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel K.arrow
  have : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi (cokernel.π K.arrow)
  have hQclosed : IsClosed SQ := support_closed_of_coherent_module Q
  have hSdense : Dense {x : ↥SF | (x : X) ∉ SK} :=
    dense_support_diff_of_isNowhereDenseCoherentSubobject K hK
  have himage : Subtype.val '' {x : ↥SF | (x : X) ∉ SK} ⊆ SQ := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_support_cokernel_of_mem_support_of_not_mem_support F K y.2 hy
  exact (support_cokernel_subset F K).antisymm fun x hx => closure_minimal himage hQclosed
    ((Subtype.dense_iff (s := SF) (t := {x : ↥SF | (x : X) ∉ SK})).mp hSdense hx)

private alias stalk_map_injective := injective_stalkFunctor_map

private alias stalk_isZero_of_not_mem_support :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.isZero_stalkFunctor_obj_of_notMem_supp

private alias isRetrocompact_of_locallyNoetherian :=
  Stacks.AlgebraicGeometry.EmbeddedPoints.isRetrocompact_of_isLocallyNoetherian

private lemma supportedSections_stalk_isZero {X : Scheme.{u}} (Z : Set X)
    (F : X.Modules) {x : X} (hx : x ∉ Z) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj
      (AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule Z F).toSheafOfModules) := by
  let H := AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule Z F
  let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x
  have hmono : Mono H.ι := AlgebraicGeometry.Scheme.Modules.mono_submodule_ι H
  have hinj := @stalk_map_injective X H.toSheafOfModules F H.ι hmono x
  have hz (a : T.obj H.toSheafOfModules) : a = 0 := by
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq H.toSheafOfModules.val.presheaf a
    apply hinj
    refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hxU
      ((SheafOfModules.toSheaf X.ringCatSheaf).map H.ι).hom s).trans ?_
    change TopCat.Presheaf.germ F.val.presheaf U x hxU s.1 = _
    rw [(AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_iff Z F U s.1).mp
      s.2 x hxU hx]
    exact ((T.map H.ι).hom.map_zero).symm
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

private alias isNowhereDense_closure_singleton_of_not_generic :=
    Stacks.AlgebraicGeometry.EmbeddedPoints.isNowhereDense_closure_singleton

private alias isNowhereDense_closure_of_not_generic :=
    Stacks.AlgebraicGeometry.EmbeddedPoints.isNowhereDense_setOf_mem_closure_singleton

private lemma not_mem_support_of_comp_cokernel_π_eq_zero {X : Scheme.{u}} {F : X.Modules}
    (K L : Subobject F) {H₀ : X.Modules} (hι : H₀ ⟶ cokernel K.arrow)
    (hL : L.arrow ≫ cokernel.π K.arrow ≫ cokernel.π hι = 0) {y : X}
    (hK : y ∉ (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
      RingedSpace.ModuleSheaf X.toRingedSpace).supp)
    (hH : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y).obj H₀)) :
    y ∉ (⟨(L : X.Modules).val, (L : X.Modules).isSheaf⟩ :
      RingedSpace.ModuleSheaf X.toRingedSpace).supp := by
  intro hy
  let T : X.Modules ⥤ ModuleCat.{u} _ :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y
  have : PreservesColimits T := moduleSheaf_stalk_preservesColimits _ _
  have : T.PreservesZeroMorphisms := inferInstance
  have : IsIso (T.map (cokernel.π K.arrow)) :=
    stalk_cokernel_π_isIso_of_isZero T K.arrow (stalk_isZero_of_not_mem_support _ hK)
  have : IsIso (T.map (cokernel.π hι)) := stalk_cokernel_π_isIso_of_isZero T hι hH
  have : IsIso (T.map (cokernel.π K.arrow ≫ cokernel.π hι)) := by
    rw [T.map_comp]
    infer_instance
  have hz : T.map L.arrow = 0 := by
    apply (cancel_mono (T.map (cokernel.π K.arrow ≫ cokernel.π hι))).mp
    rw [← Functor.map_comp, hL, Functor.map_zero, zero_comp]
  exact notMem_support_of_stalk_map_eq_zero L.arrow hz hy

private lemma eq_zero_of_kernel_comp_cokernel_π_le {X : Scheme.{u}} {F : X.Modules}
    (K L : Subobject F) {H₀ : X.Modules} (hι : H₀ ⟶ cokernel K.arrow)
    (g : kernel (cokernel.π K.arrow ≫ cokernel.π hι) ⟶ (L : X.Modules))
    (hg : g ≫ L.arrow = kernel.ι (cokernel.π K.arrow ≫ cokernel.π hι)) (hLK : L ≤ K) :
    hι = 0 := by
  have hLπ : L.arrow ≫ cokernel.π K.arrow = 0 := by
    rw [← Subobject.ofLE_arrow hLK, Category.assoc, cokernel.condition, comp_zero]
  have hkπ : kernel.ι (cokernel.π K.arrow ≫ cokernel.π hι) ≫ cokernel.π K.arrow = 0 := by
    rw [← hg, Category.assoc, hLπ, comp_zero]
  have haf : pullback.fst (cokernel.π K.arrow) hι ≫ cokernel.π K.arrow ≫ cokernel.π hι = 0 := by
    rw [← Category.assoc, pullback.condition, Category.assoc, cokernel.condition, comp_zero]
  have haπ : pullback.fst (cokernel.π K.arrow) hι ≫ cokernel.π K.arrow = 0 := by
    rw [← kernel.lift_ι (cokernel.π K.arrow ≫ cokernel.π hι) _ haf, Category.assoc, hkπ,
      comp_zero]
  apply (cancel_epi (pullback.snd (cokernel.π K.arrow) hι)).mp
  rw [comp_zero]
  exact pullback.condition.symm.trans haπ

private lemma supportedSections_ι_eq_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (K : Subobject F)
    (hK : IsNowhereDenseCoherentSubobject F K)
    (hmax : ∀ L : Subobject F, IsNowhereDenseCoherentSubobject F L → L ≤ K)
    {Z : Set X} (hZ : IsClosed Z)
    (hZnd : IsNowhereDense {y : ↥((⟨F.val, F.isSheaf⟩ :
      RingedSpace.ModuleSheaf X.toRingedSpace).supp) | (y : X) ∈ Z}) :
    (AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule Z (cokernel K.arrow)).ι =
      @Zero.zero _ ((hasZeroMorphisms_modules X).zero _ _) := by
  classical
  let Q := cokernel K.arrow
  have : (K : X.Modules).IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ _ hK.1
  have : F.IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ F inferInstance
  have : Q.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel K.arrow
  let H := AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule Z Q
  let H₀ : X.Modules := H.toSheafOfModules
  have : H₀.IsQuasicoherent :=
    AlgebraicGeometry.supportedSectionsSubmodule_isQuasicoherent
      Z hZ (isRetrocompact_of_locallyNoetherian _) Q
  let hι : H₀ ⟶ Q := H.ι
  have hιmono : Mono hι := AlgebraicGeometry.Scheme.Modules.mono_submodule_ι H
  let C₁ : X.Modules := cokernel hι
  have : C₁.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel hι
  let πι : Q ⟶ C₁ := cokernel.π hι
  let f : F ⟶ C₁ := cokernel.π K.arrow ≫ πι
  have hfmono : Mono (kernel.ι f) := mono_kernel_ι f
  have : (kernel f).IsQuasicoherent := Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel f
  let L : Subobject F := Subobject.mk (kernel.ι f)
  have : (L : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Subobject.underlyingIso (kernel.ι f)).symm inferInstance
  have hLcoh : (L : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono L.arrow
  have hLcond : L.arrow ≫ f = 0 := by
    dsimp [L]
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    simp
  have hLnd : IsNowhereDense {y : ↥((⟨F.val, F.isSheaf⟩ :
      RingedSpace.ModuleSheaf X.toRingedSpace).supp) | (y : X) ∈
      (⟨(L : X.Modules).val, (L : X.Modules).isSheaf⟩ :
        RingedSpace.ModuleSheaf X.toRingedSpace).supp} := by
    apply (hK.2.union hZnd).mono
    intro y hy
    by_contra hn
    exact not_mem_support_of_comp_cokernel_π_eq_zero K L hι hLcond (fun h ↦ hn (Or.inl h))
      (supportedSections_stalk_isZero Z Q fun h ↦ hn (Or.inr h)) hy
  exact eq_zero_of_kernel_comp_cokernel_π_le K L hι
    (Subobject.underlyingIso (kernel.ι f)).inv (Subobject.underlyingIso_arrow _)
    (hmax L ⟨hLcoh, hLnd⟩)

private lemma supportedSections_closure_ι_ne_zero {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Q : X.Modules) [Q.IsQuasicoherent] {x : X} (hx : Stacks.Divisors.IsAssociatedPoint Q x) :
    (AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule (closure ({x} : Set X)) Q).ι ≠
      @Zero.zero _ ((hasZeroMorphisms_modules X).zero _ _) := by
  intro hHz
  let H := AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule (closure ({x} : Set X)) Q
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) (by simp)
  obtain ⟨hp, s, hs⟩ :=
    (AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
      Q U hU hxU).mpr hx
  have hsH : s ∈ H.toSubmodule.obj (op U) :=
    affine_section_mem_supportedSections_closure Q U hU hxU s hs
  have hs0 : s = 0 := congrArg (fun g : @Quiver.Hom X.Modules _ H.toSheafOfModules Q ↦
    g.val.app (op U) (⟨s, hsH⟩ : H.toSheafOfModules.val.obj (op U))) hHz
  rw [hs0, Submodule.span_zero_singleton, Submodule.colon_bot] at hs
  exact hp.ne_top hs.symm

/-- **[Stacks, Tag 02OL], part (2).** The quotient of `F` by a coherent subsheaf with nowhere
dense support has no embedded associated points. -/
@[stacks 02OL "part (2): no embedded associated points"]
public theorem cokernel_hasNoEmbeddedAssociatedPoints
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (K : Subobject F)
    (hK : IsNowhereDenseCoherentSubobject F K)
    (hmax : ∀ L : Subobject F, IsNowhereDenseCoherentSubobject F L → L ≤ K) :
    AlgebraicGeometry.HasNoEmbeddedAssociatedPoints (cokernel K.arrow) := by
  let Q := cokernel K.arrow
  have : (K : X.Modules).IsCoherent := hK.1
  have : (K : X.Modules).IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ _ hK.1
  have : F.IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ F inferInstance
  have : Q.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel K.arrow
  have : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi (cokernel.π K.arrow)
  intro x hx
  have hxng := (AlgebraicGeometry.isEmbeddedAssociatedPoint_iff_not_genericPoint X Q x).mp hx
  let SF := (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  have hQS : SheafOfModules.supp Q = SF := by
    rw [← SheafOfModules.supp_eq_moduleSheaf_supp (F := Q)]
    exact supp_cokernel_eq F K hK
  have hxSF : x ∈ SF := by
    rw [← hQS]
    exact AlgebraicGeometry.associatedPoints_subset_support Q hxng.1
  have hng : ¬ ∃ Z ∈ irreducibleComponents (↥SF),
      IsGenericPoint x (Subtype.val '' Z) := by
    rw [← hQS]
    exact hxng.2
  exact supportedSections_closure_ι_ne_zero Q hx.1
    (supportedSections_ι_eq_zero F K hK hmax isClosed_closure
      (isNowhereDense_closure_of_not_generic SF (support_closed_of_coherent_module F) hxSF hng))

/-- If a subset `A` of `S` has dense complement relative to `S`, then its complement is dense
in the whole space. -/
private theorem dense_compl_of_dense_compl_subtype {Y : Type*} [TopologicalSpace Y] {S A : Set Y}
    (hAS : A ⊆ S) (hd : Dense {x : S | (x : Y) ∉ A}) : Dense Aᶜ := by
  rw [dense_iff_inter_open]
  intro W hW hWne
  by_cases hWS : (W ∩ S).Nonempty
  · obtain ⟨x, hxW, hxS⟩ := hWS
    obtain ⟨y, hyW, hyA⟩ := hd.inter_open_nonempty (Subtype.val ⁻¹' W)
      (hW.preimage continuous_subtype_val) ⟨⟨x, hxS⟩, hxW⟩
    exact ⟨y.1, hyW, hyA⟩
  · obtain ⟨x, hxW⟩ := hWne
    exact ⟨x, hxW, fun hxA => hWS ⟨x, hxW, hAS hxA⟩⟩

/-- **[Stacks, Tag 02OL], part (3).** There is a dense open subset, meeting the support of `F`
densely, over every open subset of which the quotient map is an isomorphism on sections. -/
@[stacks 02OL "part (3): agreement on a dense open"]
public theorem exists_denseOpen_cokernel_iso
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (K : Subobject F)
    (hK : IsNowhereDenseCoherentSubobject F K) :
    ∃ U : X.Opens,
      Dense (U : Set X) ∧
      Dense {x : ↥((⟨F.val, F.isSheaf⟩ :
            RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp) | (x : X) ∈ U} ∧
          ∀ V : X.Opens, V ≤ U →
            IsIso ((cokernel.π K.arrow).val.app (op V)) := by
  classical
  let SF := (⟨F.val, F.isSheaf⟩ : RingedSpace.ModuleSheaf X.toRingedSpace).supp
  let SK := (⟨(K : X.Modules).val, (K : X.Modules).isSheaf⟩ :
    RingedSpace.ModuleSheaf X.toRingedSpace).supp
  have htop : ((X.toRingedSpace.toPresheafedSpace : TopCat).str :
      TopologicalSpace (↑↑X.toRingedSpace.toPresheafedSpace)) =
        AlgebraicGeometry.SheafedSpace.instTopologicalSpaceCarrierCarrier X.toRingedSpace := rfl
  have hKsub : SK ⊆ SF := support_subobject_subset F K
  have : (K : X.Modules).IsCoherent := hK.1
  have hSKclosed : @IsClosed X _ SK := htop.symm ▸ support_closed_of_coherent_module (K : X.Modules)
  have hRelDense : Dense {x : ↥SF | (x : X) ∉ SK} :=
    dense_support_diff_of_isNowhereDenseCoherentSubobject K hK
  let U : X.Opens := ⟨SKᶜ, hSKclosed.isOpen_compl⟩
  have hUdense : Dense (U : Set X) := dense_compl_of_dense_compl_subtype hKsub hRelDense
  refine ⟨U, hUdense, ?_, ?_⟩
  · simpa [U, SF, SK] using hRelDense
  · intro V hVU
    let T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf
    let f := (SheafOfModules.toSheaf X.ringCatSheaf).map (cokernel.π K.arrow)
    have hst : ∀ x : V, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x.1).map f.hom) := by
      intro x
      have : PreservesColimits (T x.1) := moduleSheaf_stalk_preservesColimits
        X.ringCatSheaf x.1
      have : (T x.1).PreservesZeroMorphisms := inferInstance
      have : IsIso ((T x.1).map (cokernel.π K.arrow)) :=
        stalk_cokernel_π_isIso_of_isZero (T x.1) K.arrow
          (stalk_isZero_of_not_mem_support (K : X.Modules) (hVU x.2))
      exact Functor.map_isIso (forget₂ (ModuleCat _) AddCommGrpCat)
        ((T x.1).map (cokernel.π K.arrow))
    have hadd : IsIso (f.hom.app (op V)) :=
      TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso f V
    have : IsIso ((forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V)))
      AddCommGrpCat).map ((cokernel.π K.arrow).val.app (op V))) := hadd
    exact isIso_of_reflects_iso ((cokernel.π K.arrow).val.app (op V))
      (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op V))) AddCommGrpCat)

end Stacks.AlgebraicGeometry.CoherentSubquotients

end
