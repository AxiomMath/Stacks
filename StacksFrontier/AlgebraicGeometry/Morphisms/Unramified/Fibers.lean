module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibres of unramified morphisms

A scheme unramified over a field is a disjoint union of spectra of finite separable field
extensions. Consequently, every fibre of an unramified morphism has this form over the residue
field of its base point.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.unramified_iff_iso_coproduct_spectra_finite_separable` characterizes schemes
  unramified over a field.
* `AlgebraicGeometry.Unramified.exists_iso_fiber_coproduct_spectra_finite_separable` describes the
  fibres of an unramified morphism.

## Implementation notes

In both results the isomorphism with the coproduct is required to respect the given morphism to
the spectrum of the base field. A finite separable extension is expressed by `Module.Finite`
together with `Algebra.IsSeparable`.

Over a field the source is discrete, because an unramified morphism is locally quasi-finite and
the spectrum of a field is a point; it is reduced because a formally unramified algebra of finite
type over a field is. Its one-point opens are therefore affine with a field of sections, which
exhibits the source as the coproduct of their spectra. The statement about fibres follows by base
change along the inclusion of the residue field of the base point.

## References

* [Stacks Project, Tag 02G7](https://stacks.math.columbia.edu/tag/02G7)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

private theorem isReduced_of_formallyUnramified_over_field
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [FormallyUnramified f] [LocallyOfFiniteType f] : IsReduced X := by
  wlog hX : ∃ A : CommRingCat.{u}, X = Spec A generalizing X
  · rw [IsReduced.iff_of_openCover X X.affineCover]
    intro i
    have hF : FormallyUnramified (X.affineCover.f i ≫ f) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _
        (inferInstanceAs (FormallyUnramified (X.affineCover.f i))) inferInstance
    have hL : LocallyOfFiniteType (X.affineCover.f i ≫ f) :=
      MorphismProperty.comp_mem @LocallyOfFiniteType _ _
        (inferInstanceAs (LocallyOfFiniteType (X.affineCover.f i))) inferInstance
    exact this (f := X.affineCover.f i ≫ f) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  have : Algebra.FormallyUnramified k A :=
    (HasRingHomProperty.Spec_iff (P := @FormallyUnramified) (φ := φ)).mp inferInstance
  have : Algebra.FiniteType k A :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp inferInstance
  have : Algebra.EssFiniteType k A := inferInstance
  have : _root_.IsReduced A := Algebra.FormallyUnramified.isReduced_of_field k A
  infer_instance

private theorem unramified_coproduct_spectra_finite_separable
    (k : Type u) [Field k] (I : Type u) (K : I → Type u)
    [hK : ∀ i, Field (K i)] [hAlg : ∀ i, Algebra k (K i)]
    [hFin : ∀ i, Module.Finite k (K i)]
    [hSep : ∀ i, Algebra.IsSeparable k (K i)] :
    Unramified
      (Sigma.desc fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) := by
  let (i : I) : Field (K i) := hK i
  let (i : I) : Algebra k (K i) := hAlg i
  let (i : I) : Module.Finite k (K i) := hFin i
  let (i : I) : Algebra.IsSeparable k (K i) := hSep i
  let : IsZariskiLocalAtSource
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FiniteType)
  let : IsZariskiLocalAtSource
      (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FormallyUnramified)
  let g (i : I) : Scheme.{u} := Spec (.of (K i))
  let 𝒰 : (∐ g).OpenCover := {
    I₀ := I
    X := g
    f := Sigma.ι g
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
      obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk g).surjective x
      refine ⟨i, ?_⟩
      change x ∈ Set.range (Sigma.ι g i)
      exact ⟨y, by simpa only [sigmaMk_mk] using hy⟩ }
  apply (unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mpr
  constructor
  · rw [IsZariskiLocalAtSource.iff_of_openCover
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u})) 𝒰]
    intro i
    change LocallyOfFiniteType (Sigma.ι g i ≫ Sigma.desc _)
    rw [Sigma.ι_comp_desc, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap).mpr inferInstance
  · rw [IsZariskiLocalAtSource.iff_of_openCover
      (P := (@FormallyUnramified : MorphismProperty Scheme.{u})) 𝒰]
    intro i
    change FormallyUnramified (Sigma.ι g i ≫ Sigma.desc _)
    rw [Sigma.ι_comp_desc, HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact (RingHom.formallyUnramified_algebraMap).mpr
      (Algebra.FormallyUnramified.of_isSeparable k (K i))

private theorem isField_sections_singleton
    {X : Scheme.{u}} [IsReduced X] [DiscreteTopology X] (x : X) :
    IsField Γ(X, (⟨{x}, isOpen_discrete _⟩ : X.Opens)) := by
  let U : X.Opens := ⟨{x}, isOpen_discrete _⟩
  have hU : IsAffineOpen U := IsAffineOpen.of_subsingleton (Set.subsingleton_singleton)
  have hr : Set.range hU.fromSpec = ({x} : Set X) := by
    simp [U, hU.range_fromSpec]
  obtain ⟨y, -⟩ : x ∈ Set.range hU.fromSpec := by simp [hr]
  have : Nontrivial Γ(X, U) := PrimeSpectrum.nontrivial y
  have : _root_.IsReduced Γ(X, U) :=
    (affine_isReduced_iff _).mp (isReduced_of_isOpenImmersion hU.fromSpec)
  have h (a : Spec Γ(X, U)) : hU.fromSpec a = x := by
    have : hU.fromSpec a ∈ Set.range hU.fromSpec := ⟨a, rfl⟩
    simpa [hr] using this
  have : Subsingleton (Spec Γ(X, U)) :=
    ⟨fun a b ↦ hU.fromSpec.isOpenEmbedding.injective ((h a).trans (h b).symm)⟩
  have hs : Subsingleton (PrimeSpectrum Γ(X, U)) := by
    change Subsingleton (Spec Γ(X, U))
    infer_instance
  exact PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp hs

private theorem finite_separable_sections_over_field
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Unramified f] (U : X.Opens) (hU : IsAffineOpen U)
    (hField : IsField Γ(X, U)) :
    letI : Algebra k Γ(X, U) :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom).toAlgebra
    Module.Finite k Γ(X, U) ∧ Algebra.IsSeparable k Γ(X, U) := by
  have : FormallyUnramified f := formallyUnramified_of_unramified f
  let : Field Γ(X, U) := hField.toField
  let φ := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom
  let : Algebra k Γ(X, U) := φ.toAlgebra
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (.of k)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2
  have hft : φ.FiniteType := by
    simpa only [φ, CommRingCat.hom_comp] using
      RingHom.FiniteType.comp
        (f.finiteType_appLE (isAffineOpen_top _) hU le_top)
        (RingHom.FiniteType.of_surjective _ hsurj)
  have hfu : φ.FormallyUnramified := by
    simpa only [φ, CommRingCat.hom_comp] using
      RingHom.FormallyUnramified.comp
        (RingHom.FormallyUnramified.of_surjective hsurj)
        (f.formallyUnramified_appLE (isAffineOpen_top _) hU le_top)
  have : Algebra.FiniteType k Γ(X, U) :=
    (RingHom.finiteType_algebraMap).mp (show (algebraMap k Γ(X, U)).FiniteType from hft)
  have : Algebra.EssFiniteType k Γ(X, U) := inferInstance
  have : Algebra.FormallyUnramified k Γ(X, U) :=
    (RingHom.formallyUnramified_algebraMap).mp
      (show (algebraMap k Γ(X, U)).FormallyUnramified from hfu)
  exact ⟨Algebra.FormallyUnramified.finite_of_free k Γ(X, U),
    Algebra.FormallyUnramified.isSeparable k Γ(X, U)⟩

private theorem fromSpec_comp_to_field
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(X, U) :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom).toAlgebra
    hU.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, U))) := by
  let : Algebra k Γ(X, U) :=
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom).toAlgebra
  change hU.fromSpec ≫ f =
    Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top)
  simpa only [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp] using
    (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top).symm

/-- **Stacks Project, Tag 02G7, part (1).** A morphism to the spectrum of a field is unramified
if and only if its source is, over that spectrum, a coproduct of spectra of finite separable
field extensions. -/
@[stacks 02G7 "part (1)", ega "IV 17.15.11" "b) <=> c)", sga "3 XI 1.3" "(a)<=>(e) over field"]
public theorem unramified_iff_iso_coproduct_spectra_finite_separable
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Unramified f ↔
      ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
        (_ : ∀ i, Algebra k (K i)) (_ : ∀ i, Module.Finite k (K i))
        (_ : ∀ i, Algebra.IsSeparable k (K i))
        (e : X ≅ ∐ fun i ↦ Spec (.of (K i))),
        e.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap k (K i)))) = f := by
  constructor
  · intro hf
    let : Unramified f := hf
    let : LocallyQuasiFinite f := inferInstance
    let s : Spec (.of k) := IsLocalRing.closedPoint k
    have : Subsingleton (Spec (.of k)) := by
      change Subsingleton (PrimeSpectrum k)
      infer_instance
    have hs : f ⁻¹' {s} = (Set.univ : Set X) := by
      ext x
      simp [Subsingleton.elim (f x) s]
    have : DiscreteTopology X := by
      rw [← isDiscrete_univ_iff]
      simpa only [hs] using f.isDiscrete_preimage_singleton s
    have : FormallyUnramified f := formallyUnramified_of_unramified f
    have : IsReduced X := isReduced_of_formallyUnramified_over_field k f
    let U (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩
    let K (x : X) : Type u := Γ(X, U x)
    have hU (x : X) : IsAffineOpen (U x) :=
      IsAffineOpen.of_subsingleton Set.subsingleton_singleton
    let hK (x : X) : Field (K x) := (isField_sections_singleton x).toField
    let hAlg (x : X) : Algebra k (K x) :=
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ (U x) le_top).hom).toAlgebra
    have hFS (x : X) := finite_separable_sections_over_field k f (U x) (hU x)
      (isField_sections_singleton x)
    have hFin (x : X) : Module.Finite k (K x) := (hFS x).1
    have hSep (x : X) : Algebra.IsSeparable k (K x) := (hFS x).2
    let g (x : X) : Spec (.of (K x)) ⟶ X := (hU x).fromSpec
    have (x : X) : IsOpenImmersion (g x) := inferInstance
    have hRange (x : X) : (g x).opensRange = U x := (hU x).opensRange_fromSpec
    have hcov : ⨆ x, (g x).opensRange = ⊤ := by
      simp_rw [hRange]
      ext y
      simp [U]
    have hdisj : Pairwise (fun i j ↦ Disjoint (g i).opensRange (g j).opensRange) := by
      intro i j hij
      rw [hRange i, hRange j]
      simp [U, disjoint_iff, hij]
    have hcolimit : Nonempty (IsColimit (Cofan.mk X g)) :=
      nonempty_isColimit_cofanMk_of g hcov hdisj
    let : IsIso (Sigma.desc g) :=
      (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X g)).mp hcolimit
    let e : X ≅ ∐ fun x ↦ Spec (.of (K x)) := (asIso (Sigma.desc g)).symm
    refine ⟨X, K, hK, hAlg, hFin, hSep, e, ?_⟩
    rw [← cancel_epi e.inv]
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    change Sigma.desc (fun i ↦ Spec.map
      (CommRingCat.ofHom (algebraMap k (K i)))) = Sigma.desc g ≫ f
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    exact (fromSpec_comp_to_field k f (U i) (hU i)).symm
  · rintro ⟨I, K, hK, hAlg, hFin, hSep, e, he⟩
    let (i : I) : Field (K i) := hK i
    let (i : I) : Algebra k (K i) := hAlg i
    let (i : I) : Module.Finite k (K i) := hFin i
    let (i : I) : Algebra.IsSeparable k (K i) := hSep i
    have hg := unramified_coproduct_spectra_finite_separable k I K
    rw [← he]
    have he' : Unramified e.hom :=
      (unramified_iff_locallyOfFiniteType_and_formallyUnramified _).mpr
        ⟨inferInstance, inferInstance⟩
    exact MorphismProperty.comp_mem @Unramified _ _ he' hg

/-- **Stacks Project, Tag 02G7, part (2).** Every fibre of an unramified morphism is, over the
residue field of the base point, a coproduct of spectra of finite separable field extensions. -/
@[stacks 02G7 "part (2)", sga "3 XI 1.3" "(a) => (e)"]
public theorem Unramified.exists_iso_fiber_coproduct_spectra_finite_separable
    {X S : Scheme.{u}} (f : X ⟶ S) [Unramified f] (s : S) :
    ∃ (I : Type u) (K : I → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, Algebra (S.residueField s) (K i))
      (_ : ∀ i, Module.Finite (S.residueField s) (K i))
      (_ : ∀ i, Algebra.IsSeparable (S.residueField s) (K i))
      (e : f.fiber s ≅ ∐ fun i ↦ Spec (.of (K i))),
      e.hom ≫ Sigma.desc (fun i ↦
        Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (K i)))) =
        f.fiberToSpecResidueField s := by
  have hfiber : Unramified (f.fiberToSpecResidueField s) := by
    change Unramified (pullback.snd f (S.fromSpecResidueField s))
    exact unramified_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) inferInstance
  exact (unramified_iff_iso_coproduct_spectra_finite_separable
    (S.residueField s) (f.fiberToSpecResidueField s)).mp hfiber

end AlgebraicGeometry
