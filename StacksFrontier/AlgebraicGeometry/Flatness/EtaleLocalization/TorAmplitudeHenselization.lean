module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.FlatHenselization
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.CompositionCanonical
public import StacksFrontier.Homology.TorAmplitude.ExtendScalars
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.GlobalDimension
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel

/-!
# Tor amplitude and henselization

Let `(R, 𝔪, κ)` be a local ring, let `κ ⊆ K` be an extension of its residue field, let `Rh` be a
henselization of `R` and let `Rsh` be a henselization of `R` with residue field `K` — a strict
henselization when `K` is a separable closure of `κ`. A complex of `Rsh`-modules has tor
amplitude in `[a, b]` over `R` if and only if it has it over `Rh`, if and only if it has it over
`Rsh`. When the complex is the derived base change of a complex of `Rh`-modules, two further
conditions on that complex are equivalent, and when that complex is itself a derived base change
from `R`, so is the condition on the original complex.

Each equivalence is reduced to the corresponding statement for flatness of a single module,
`flat_tfae_henselization`: a complex bounded above admits a bounded-above resolution by
projectives, over such a resolution tor amplitude in `[a, b]` is the conjunction of `IsGE a` with
flatness of the `a`-th opcycles, and both of those are detected by restriction of scalars along a
henselization map.

## Main results

* `torAmplitude_tfae_henselization`: the three equivalent tor-amplitude conditions for a complex
  over the extended-residue-field henselization.
* `torAmplitude_tfae_baseChange_henselization`: the five equivalent conditions when that complex
  is a base change.
* `torAmplitude_tfae_iteratedBaseChange_henselization`: the six equivalent conditions when the
  complex is an iterated base change.

## Implementation notes

Objects of the derived categories are represented by cochain complexes of modules, and the
derived tensor products of the source by extension of scalars, which computes them because the
henselization maps are flat. Tor amplitude is
`StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift`, whose universe-lifted formulation lets
the three rings live in independent universes; the complexes inhabit a single module universe
large enough for all three, and `canonicalLift_ambient_independent_any` shows the predicate does
not depend on the auxiliary lifting universe. The `include K` retains the
extended-residue-field henselization hypothesis in all three statements.

## References

* [Stacks Project, Tag 0DK0](https://stacks.math.columbia.edu/tag/0DK0)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u uh ush v w x z m n

attribute [local instance] HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  HomologicalComplex StacksDraft.TorAmplitude CochainComplex

/-- Tor amplitude in `[a, b]` depends only on the quasi-isomorphism class of a complex, because
the comparison is computed against a projective resolution, which is K-flat. -/
private lemma torAmplitude_iff_of_quasiIso {R : Type u} [CommRing R]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) [QuasiIso f] (a b : ℤ) :
    FaithfullyFlat.HasTorAmplitude P a b ↔ FaithfullyFlat.HasTorAmplitude Q a b := by
  have he (M : ModuleCat.{u} R) (i : ℤ) :
      IsZero (FaithfullyFlat.derivedTensorHomology P M i) ↔
        IsZero (FaithfullyFlat.derivedTensorHomology Q M i) := by
    have hproj : ∀ n : ℤ, Projective ((FaithfullyFlat.projResComplex M).X n) := by
      intro n
      show Projective (((ProjectiveResolution.of M).complex.extend
        ComplexShape.embeddingDownNat).X n)
      infer_instance
    have hLE : (FaithfullyFlat.projResComplex M).IsStrictlyLE 0 := by
      show CochainComplex.IsStrictlyLE
        ((ProjectiveResolution.of M).complex.extend ComplexShape.embeddingDownNat) 0
      infer_instance
    have := quasiIso_tensorRight_map
      (kFlat_of_isStrictlyLE_projective (FaithfullyFlat.projResComplex M) 0 hproj) f
    exact (asIso (homologyMap ((tensorRight (FaithfullyFlat.projResComplex M)).map f) i)).isZero_iff
  exact ⟨fun h M i hi => (he M i).mp (h M i hi),
    fun h M i hi => (he M i).mpr (h M i hi)⟩

/-- For a complex bounded above by `b` with flat terms, tor amplitude in `[a, b]` agrees with the
termwise vanishing condition. -/
private lemma torAmplitude_iff_termwise {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) [P.IsStrictlyLE b]
    (hflat : ∀ i, Module.Flat R (P.X i)) (a : ℤ) :
    FaithfullyFlat.HasTorAmplitude P a b ↔ Termwise.HasTorAmplitudeIn P a b := by
  have := hflat
  have hbound : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨b, (CochainComplex.isStrictlyLE_iff P b).mp inferInstance⟩
  exact (hasTorAmplitude_iff_hasTorAmplitude0DJF (canonicalTensorComparison R)
    (canonicalTensorIsLeftDerived R) P (CochainComplex.KFlat.kFlat_of_flat P b)
    hbound hflat a b).symm.trans
      (hasTorAmplitude_iff_termwise_of_flat (canonicalTensorComparison R)
        (canonicalTensorIsLeftDerived R) P hbound hflat a b)

/-- A complex with tor amplitude in `[a, b]` has vanishing homology outside `[a, b]`, as is seen by
tensoring with the base ring. -/
private lemma torAmplitude_isZero_homology {R : Type u} [CommRing R]
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (h : FaithfullyFlat.HasTorAmplitude P a b) (i : ℤ) (hi : i < a ∨ b < i) :
    IsZero (P.homology i) :=
  (derivedTensorHomologyUnitIso R P i).isZero_iff.mp (h (ModuleCat.of R R) i hi)

/-- For a complex of flat modules bounded above by `b`, tor amplitude in `[a, b]` says exactly that
the complex is supported in degrees `≥ a` and that its `a`-th opcycles are flat. -/
private lemma torAmplitude_iff_isGE_flat_opcycles {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [P.IsStrictlyLE b]
    (hflat : ∀ i, Module.Flat R (P.X i)) :
    FaithfullyFlat.HasTorAmplitude P a b ↔ P.IsGE a ∧ Module.Flat R (P.opcycles a) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [CochainComplex.isGE_iff]
      intro i hi
      rw [exactAt_iff_isZero_homology]
      exact torAmplitude_isZero_homology h i (Or.inl hi)
    · have := Termwise.cokernel_flat_of_termwise_torAmplitude P a b hflat
        ((torAmplitude_iff_termwise P b hflat a).mp h)
      let e : P.opcycles a ≅ (cokernel (P.d (a - 1) a) : ModuleCat.{u} R) :=
        IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel (a - 1) a (by simp))
          (colimit.isColimit _)
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
  · rintro ⟨hGE, hop⟩
    have : (P.truncGE a).IsStrictlyLE b := truncGE_isStrictlyLE P a b inferInstance
    apply (torAmplitude_iff_of_quasiIso (P.πTruncGE a) a b).mpr
    apply (torAmplitude_iff_termwise (P.truncGE a) b (flat_truncGE P a) a).mpr
    intro M i hi
    have hz : IsZero ((P.truncGE a).X i) := by
      rcases hi with hi | hi
      · exact CochainComplex.isZero_of_isStrictlyGE _ a i hi
      · exact CochainComplex.isZero_of_isStrictlyLE _ b i hi
    exact ShortComplex.isZero_homology_of_isZero_X₂ _ ((tensorRight M).map_isZero hz)

/-- Restriction of scalars does not change which homology objects of a complex vanish. -/
private lemma isZero_homology_restrictScalars_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (P : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ) :
    IsZero (((CochainComplex.restrictScalars f).obj P).homology i) ↔
      IsZero (P.homology i) :=
  ((P.sc i).mapHomologyIso (ModuleCat.restrictScalars f)).isZero_iff.trans
    (FaithfullyFlat.isZero_restrictScalars_iff f (P.homology i))

/-- Restriction of scalars preserves and reflects being supported in degrees `≥ a`. -/
private lemma isGE_restrictScalars_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (P : CochainComplex (ModuleCat.{u} B) ℤ) (a : ℤ) :
    ((CochainComplex.restrictScalars f).obj P).IsGE a ↔ P.IsGE a := by
  simp only [CochainComplex.isGE_iff, exactAt_iff_isZero_homology,
    isZero_homology_restrictScalars_iff]

/-- Restriction of scalars preserves and reflects being supported in degrees `≤ b`. -/
private lemma isLE_restrictScalars_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (P : CochainComplex (ModuleCat.{u} B) ℤ) (b : ℤ) :
    ((CochainComplex.restrictScalars f).obj P).IsLE b ↔ P.IsLE b := by
  simp only [CochainComplex.isLE_iff, exactAt_iff_isZero_homology,
    isZero_homology_restrictScalars_iff]

/-- A module over `B` is zero exactly when its restriction of scalars to `A` is, with the two rings
in independent universes. -/
private lemma isZero_restrictScalars_iff_any
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    (f : A →+* B) (N : ModuleCat.{max u uh m} B) :
    IsZero ((ModuleCat.restrictScalars.{max u uh m} f).obj N) ↔ IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

/-- A complex with tor amplitude in `[a, b]` is supported in degrees `≤ b`. -/
private lemma torAmplitude_isLE {R : Type u} [CommRing R]
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (h : FaithfullyFlat.HasTorAmplitude P a b) : P.IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact torAmplitude_isZero_homology h i (Or.inr hi)

/-- A complex supported in degrees `≤ b` is quasi-isomorphic to a complex of flat modules that is
strictly supported in degrees `≤ b`, namely a bounded-above projective resolution. -/
private lemma exists_flat_isStrictlyLE_quasiIso {R : Type u} [CommRing R] [Small.{m} R]
    (P : CochainComplex (ModuleCat.{m} R) ℤ) (b : ℤ) [P.IsLE b] :
    ∃ (E : CochainComplex (ModuleCat.{m} R) ℤ) (g : E ⟶ P),
      QuasiIso g ∧ E.IsStrictlyLE b ∧ ∀ i, Module.Flat R (E.X i) := by
  obtain ⟨PR, -⟩ := ProjectiveResolutionLemma.statement3 b (P.truncLE b) inferInstance
  have : QuasiIso PR.α := PR.quasiIso
  exact ⟨PR.complex, PR.α ≫ P.ιTruncLE b, inferInstance, PR.boundedAbove,
    fun i => by have := PR.projective i; infer_instance⟩

/-- Flatness of a module is invariant under isomorphism. -/
private lemma flat_iff_of_iso {R : Type u} [CommRing R] {M N : ModuleCat.{v} R} (e : M ≅ N) :
    Module.Flat R M ↔ Module.Flat R N :=
  ⟨fun h => h.of_linearEquiv e.symm.toLinearEquiv, fun h => h.of_linearEquiv e.toLinearEquiv⟩

/-- For a complex supported in degrees `≤ b`, tor amplitude in `[a, b]` is detected by restriction
of scalars along a ring map along which flatness descends. The comparison is made on a
bounded-above projective resolution, where tor amplitude is the criterion of
`torAmplitude_iff_isGE_flat_opcycles`. -/
private lemma torAmplitude_restrictScalars_iff_of_isLE {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B)
    (hflat : ∀ N : ModuleCat.{u} B,
      Module.Flat A ((ModuleCat.restrictScalars f).obj N) ↔ Module.Flat B N)
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ) [P.IsLE b] :
    FaithfullyFlat.HasTorAmplitude ((CochainComplex.restrictScalars f).obj P) a b ↔
      FaithfullyFlat.HasTorAmplitude P a b := by
  obtain ⟨E, g, hg, hE, hEflat⟩ := exists_flat_isStrictlyLE_quasiIso P b
  have : QuasiIso ((CochainComplex.restrictScalars f).map g) := by
    show QuasiIso (((ModuleCat.restrictScalars f).mapHomologicalComplex _).map _)
    infer_instance
  rw [← torAmplitude_iff_of_quasiIso g a b,
    ← torAmplitude_iff_of_quasiIso ((CochainComplex.restrictScalars f).map g) a b]
  have hERflat : ∀ i, Module.Flat A (((CochainComplex.restrictScalars f).obj E).X i) :=
    fun i => (hflat (E.X i)).mpr (hEflat i)
  have : ((CochainComplex.restrictScalars f).obj E).IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff
      (K := E) (ModuleCat.restrictScalars f) b).mpr inferInstance
  rw [torAmplitude_iff_isGE_flat_opcycles _ a b hEflat,
    torAmplitude_iff_isGE_flat_opcycles _ a b hERflat, isGE_restrictScalars_iff]
  exact and_congr_right fun _ => (flat_iff_of_iso
    ((E.sc a).mapOpcyclesIso (ModuleCat.restrictScalars f))).trans (hflat (E.opcycles a))

/-- The same comparison without the boundedness hypothesis, which is itself detected by restriction
of scalars. -/
private lemma torAmplitude_restrictScalars_iff {A B : Type u}
    [CommRing A] [CommRing B] (f : A →+* B)
    (hflat : ∀ N : ModuleCat.{u} B,
      Module.Flat A ((ModuleCat.restrictScalars f).obj N) ↔ Module.Flat B N)
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ) :
    FaithfullyFlat.HasTorAmplitude ((CochainComplex.restrictScalars f).obj P) a b ↔
      FaithfullyFlat.HasTorAmplitude P a b := by
  constructor
  · intro h
    have : P.IsLE b := (isLE_restrictScalars_iff f P b).mp (torAmplitude_isLE h)
    exact (torAmplitude_restrictScalars_iff_of_isLE f hflat P a b).mp h
  · intro h
    have := torAmplitude_isLE h
    exact (torAmplitude_restrictScalars_iff_of_isLE f hflat P a b).mpr h

/-- The canonical tor-amplitude predicate is invariant under isomorphism in the derived
category. -/
private lemma hasTorAmplitudeCanonical_iff_of_iso {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u} R)} (e : K ≅ L) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R K a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R L a b := by
  rw [StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative,
    StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative]
  exact ⟨hasFlatRepresentative_of_iso e, hasFlatRepresentative_of_iso e.symm⟩

/-- The canonical tor-amplitude predicate in the derived category is invariant under
quasi-isomorphism of representatives. -/
private lemma hasTorAmplitudeCanonical_iff_of_quasiIso {R : Type u} [CommRing R]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) [QuasiIso f] (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R (DerivedCategory.Q.obj Q) a b :=
  hasTorAmplitudeCanonical_iff_of_iso (asIso (DerivedCategory.Q.map f)) a b

/-- For a complex of flat modules bounded above, the canonical tor-amplitude predicate on its image
in the derived category is the complex-level one. -/
private lemma hasTorAmplitudeCanonical_iff_hasTorAmplitude_of_boundedProjective
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyLE b] (hflat : ∀ i, Module.Flat R (P.X i)) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R (DerivedCategory.Q.obj P) a b ↔
      FaithfullyFlat.HasTorAmplitude P a b := by
  have hbound : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨b, (CochainComplex.isStrictlyLE_iff P b).mp inferInstance⟩
  exact (hasTorAmplitudeIn_canonical_iff R (DerivedCategory.Q.obj P) a b).symm.trans
    ((hasTorAmplitudeIn_iff_hasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R)
      (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R)
      (DerivedCategory.Q.obj P) a b).trans
      (hasTorAmplitude_iff_hasTorAmplitude0DJF (canonicalTensorComparison R)
        (canonicalTensorIsLeftDerived R) P (CochainComplex.KFlat.kFlat_of_flat P b)
        hbound hflat a b))

/-- A complex whose image in the derived category has canonical tor amplitude in `[a, b]` is
supported in degrees `≤ b`. -/
private lemma hasTorAmplitudeCanonical_isLE {R : Type u} [CommRing R]
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (h : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R (DerivedCategory.Q.obj P) a b) :
    P.IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  have h' := (StacksDraft.TorAmplitude.hasTorAmplitudeIn_iff_hasTorAmplitude
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R)
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
    (DerivedCategory.Q.obj P) a b).mp
      ((StacksDraft.TorAmplitude.hasTorAmplitudeIn_canonical_iff R
        (DerivedCategory.Q.obj P) a b).mpr h)
  exact StacksDraft.TorAmplitude.isZero_homology_of_hasTorAmplitude
    (StacksDraft.TorAmplitude.canonicalTensorComparison R)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) P a b h' i (Or.inr hi)

/-- For a complex supported in degrees `≤ b`, the canonical tor-amplitude predicate on its image in
the derived category is the complex-level one, as is seen on a bounded-above flat model. -/
private lemma hasTorAmplitudeCanonical_iff_hasTorAmplitude_of_isLE {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [P.IsLE b] :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R (DerivedCategory.Q.obj P) a b ↔
      FaithfullyFlat.HasTorAmplitude P a b := by
  obtain ⟨E, g, hg, hE, hEflat⟩ := exists_flat_isStrictlyLE_quasiIso P b
  rw [← hasTorAmplitudeCanonical_iff_of_quasiIso g a b, ← torAmplitude_iff_of_quasiIso g a b]
  exact hasTorAmplitudeCanonical_iff_hasTorAmplitude_of_boundedProjective E a b hEflat

/-- For an arbitrary complex, the canonical tor-amplitude predicate on its image in the derived
category is the complex-level one: both sides force the complex to be supported in degrees
`≤ b`. -/
private lemma hasTorAmplitudeCanonical_iff_hasTorAmplitude {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical R (DerivedCategory.Q.obj P) a b ↔
      FaithfullyFlat.HasTorAmplitude P a b := by
  constructor
  · intro h
    have := hasTorAmplitudeCanonical_isLE h
    exact (hasTorAmplitudeCanonical_iff_hasTorAmplitude_of_isLE P a b).mp h
  · intro h
    have := torAmplitude_isLE h
    exact (hasTorAmplitudeCanonical_iff_hasTorAmplitude_of_isLE P a b).mpr h

/-- The universe-lifted canonical tor-amplitude predicate is the existence of a flat representative
of the universe-lifted object. -/
private lemma canonicalLift_iff_hasFlatRepresentative
    {R : Type u} [CommRing R] {K : DerivedCategory (ModuleCat.{v} R)}
    (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, v, w} K a b ↔
      StacksDraft.TorAmplitude.HasFlatRepresentative
        ((StacksDraft.TorAmplitude.moduleLift.{u, v, w} R).mapDerivedCategory.obj K) a b := by
  unfold StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
  exact StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
    (ULift.{max v w} R) _ a b

/-- Canonical tor amplitude is detected by restriction of scalars along a ring map along which
flatness descends. -/
private lemma canonical_restrictScalars_iff {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B)
    (hflat : ∀ N : ModuleCat.{u} B,
      Module.Flat A ((ModuleCat.restrictScalars f).obj N) ↔ Module.Flat B N)
    (P : CochainComplex (ModuleCat.{u} B) ℤ) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical A
        (DerivedCategory.Q.obj ((CochainComplex.restrictScalars f).obj P)) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical B (DerivedCategory.Q.obj P) a b :=
  (hasTorAmplitudeCanonical_iff_hasTorAmplitude _ a b).trans
    ((torAmplitude_restrictScalars_iff f hflat P a b).trans
      (hasTorAmplitudeCanonical_iff_hasTorAmplitude _ a b).symm)

/-- Universe lifting of modules commutes with restriction of scalars, degreewise on complexes. -/
private noncomputable def moduleLift_restrictScalars_iso
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    (f : A →+* B)
    (P : CochainComplex (ModuleCat.{max u (max uh x)} B) ℤ) :
    (((StacksDraft.TorAmplitude.moduleLift.{u, max u (max uh x),
      max u (max uh x)} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≅
    (((ModuleCat.restrictScalars
      f.ulift.{max u (max uh x), max u (max uh x)}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((StacksDraft.TorAmplitude.moduleLift.{uh, max u (max uh x),
        max u (max uh x)} B).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun _ _ _ => rfl

/-- The universe-lifted tor-amplitude predicate for a complex is the canonical predicate for the
universe-lifted complex over the universe-lifted ring. -/
private lemma canonicalLift_iff_canonical_moduleLift
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{m} A) ℤ) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, n}
        (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical (ULift.{max m n} A)
        (DerivedCategory.Q.obj
          (((StacksDraft.TorAmplitude.moduleLift.{u, m, n} A).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) a b := by
  rw [canonicalLift_iff_hasFlatRepresentative.{u, m, n}]
  let L := (((StacksDraft.TorAmplitude.moduleLift.{u, m, n} A).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P)
  let e := (StacksDraft.TorAmplitude.moduleLift.{u, m, n} A).mapDerivedCategoryFactors.app P
  have he : StacksDraft.TorAmplitude.HasFlatRepresentative.{max u (max m n), 0}
      ((StacksDraft.TorAmplitude.moduleLift.{u, m, n} A).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P)) a b ↔
      StacksDraft.TorAmplitude.HasFlatRepresentative (DerivedCategory.Q.obj L) a b :=
    ⟨hasFlatRepresentative_of_iso e, hasFlatRepresentative_of_iso e.symm⟩
  exact he.trans
    (StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
      (ULift.{max m n} A) (DerivedCategory.Q.obj L) a b).symm

/-- Universe lifting does not change which homology objects of a complex vanish. -/
private lemma moduleLift_isZero_homology_iff
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{m} A) ℤ) (i : ℤ) :
    IsZero ((((StacksDraft.TorAmplitude.moduleLift.{u, m, n} A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology i) ↔ IsZero (P.homology i) := by
  let F := StacksDraft.TorAmplitude.moduleLift.{u, m, n} A
  exact ((P.sc i).mapHomologyIso F).isZero_iff.trans
    ⟨IsZero.of_full_of_faithful_of_isZero F _, F.map_isZero⟩

/-- A module is flat exactly when its universe lift is flat over the universe-lifted ring. -/
private lemma moduleLift_flat_iff
    {A : Type u} [CommRing A] (N : ModuleCat.{m} A) :
    Module.Flat (ULift.{max m n} A)
        ((StacksDraft.TorAmplitude.moduleLift.{u, m, n} A).obj N) ↔
      Module.Flat A N := by
  show Module.Flat (ULift.{max m n} A) (ULift.{max u n} N) ↔ Module.Flat A N
  rw [Module.Flat.ulift_left_iff, Module.Flat.ulift_right_iff]

/-- Universe lifting preserves and reflects being supported in degrees `≥ a`. -/
private lemma moduleLift_isGE_iff
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{m} A) ℤ) (a : ℤ) :
    let LP : CochainComplex (ModuleCat.{max u m n} (ULift.{max m n} A)) ℤ :=
      ((StacksDraft.TorAmplitude.moduleLift.{u, m, n} A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P
    LP.IsGE a ↔ P.IsGE a := by
  simp only [CochainComplex.isGE_iff, exactAt_iff_isZero_homology,
    moduleLift_isZero_homology_iff]

/-- The universe-lifted tor-amplitude predicate read off a bounded-above complex of flat modules
isomorphic to the given one in the derived category. -/
private lemma moduleLift_iff_flatResolutionCriterion
    {A : Type u} [CommRing A]
    (P E : CochainComplex (ModuleCat.{m} A) ℤ) (a b : ℤ)
    (hEstrict : E.IsStrictlyLE b)
    (hEflat : ∀ i, Module.Flat A (E.X i))
    (hiso : Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj E)) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, n}
        (DerivedCategory.Q.obj P) a b ↔
      E.IsGE a ∧ Module.Flat A (E.opcycles a) := by
  let F := StacksDraft.TorAmplitude.moduleLift.{u, m, n} A
  let LP : CochainComplex (ModuleCat.{max u m n} (ULift.{max m n} A)) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let LE : CochainComplex (ModuleCat.{max u m n} (ULift.{max m n} A)) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  have hflatLE : ∀ i, Module.Flat (ULift.{max m n} A) (LE.X i) := fun i =>
    (moduleLift_flat_iff.{u, m, n} (E.X i)).mpr (hEflat i)
  have hLEstrict : LE.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := E) F b).mpr hEstrict
  have hiso' : Nonempty (DerivedCategory.Q.obj LP ≅ DerivedCategory.Q.obj LE) := by
    obtain ⟨e⟩ := hiso
    exact ⟨(F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
      F.mapDerivedCategoryFactors.app E⟩
  have hcan : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      (ULift.{max m n} A) (DerivedCategory.Q.obj LP) a b ↔
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      (ULift.{max m n} A) (DerivedCategory.Q.obj LE) a b := by
    obtain ⟨e⟩ := hiso'
    exact hasTorAmplitudeCanonical_iff_of_iso e a b
  have hLEcan : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
      (ULift.{max m n} A) (DerivedCategory.Q.obj LE) a b ↔
      FaithfullyFlat.HasTorAmplitude LE a b :=
    hasTorAmplitudeCanonical_iff_hasTorAmplitude LE a b
  have hcriterion : FaithfullyFlat.HasTorAmplitude LE a b ↔
      LE.IsGE a ∧ Module.Flat (ULift.{max m n} A) (LE.opcycles a) := by
    let : LE.IsStrictlyLE b := hLEstrict
    exact torAmplitude_iff_isGE_flat_opcycles LE a b hflatLE
  have hopflat : Module.Flat (ULift.{max m n} A) (LE.opcycles a) ↔
      Module.Flat A (E.opcycles a) :=
    (flat_iff_of_iso ((E.sc a).mapOpcyclesIso F)).trans
      (moduleLift_flat_iff.{u, m, n} (E.opcycles a))
  have hGE := moduleLift_isGE_iff.{u, m} E a
  change LE.IsGE a ↔ E.IsGE a at hGE
  rw [canonicalLift_iff_canonical_moduleLift.{u, m, n} P a b,
    hcan, hLEcan, hcriterion, hGE, hopflat]

/-- For a complex with a bounded-above flat model, the universe-lifted tor-amplitude predicate does
not depend on the auxiliary lifting universe. -/
private lemma canonicalLift_ambient_independent
    {A : Type u} [CommRing A]
    (P E : CochainComplex (ModuleCat.{m} A) ℤ) (a b : ℤ)
    (hEstrict : E.IsStrictlyLE b)
    (hEflat : ∀ i, Module.Flat A (E.X i))
    (hiso : Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj E)) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, n}
        (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, x}
        (DerivedCategory.Q.obj P) a b :=
  (moduleLift_iff_flatResolutionCriterion.{u, m, n} P E a b hEstrict hEflat hiso).trans
    (moduleLift_iff_flatResolutionCriterion.{u, m, x} P E a b hEstrict hEflat hiso).symm

/-- A complex whose universe-lifted tor amplitude lies in `[a, b]` is supported in degrees
`≤ b`. -/
private lemma canonicalLift_isLE
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{m} A) ℤ) (a b : ℤ)
    (h : StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, n}
      (DerivedCategory.Q.obj P) a b) : P.IsLE b := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  obtain ⟨E, -, -, hLE, ⟨e⟩⟩ := (canonicalLift_iff_hasFlatRepresentative.{u, m, n} a b).mp h
  have hzeroE : IsZero (E.homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ (CochainComplex.isZero_of_isStrictlyLE E b i hi)
  let F := StacksDraft.TorAmplitude.moduleLift.{u, m, n} A
  let LP : CochainComplex (ModuleCat.{max u m n} (ULift.{max m n} A)) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hqiso : DerivedCategory.Q.obj LP ≅ DerivedCategory.Q.obj E :=
    (F.mapDerivedCategoryFactors.app P).symm ≪≫ e
  let H := DerivedCategory.homologyFunctor
    (ModuleCat.{max u m n} (ULift.{max m n} A)) i
  let fac := DerivedCategory.homologyFunctorFactors
    (ModuleCat.{max u m n} (ULift.{max m n} A)) i
  have hiso : LP.homology i ≅ E.homology i :=
    (fac.app LP).symm ≪≫ H.mapIso hqiso ≪≫ fac.app E
  exact (moduleLift_isZero_homology_iff.{u, m, n} P i).mp (hzeroE.of_iso hiso)

/-- For any complex over a ring small in the module universe, the universe-lifted tor-amplitude
predicate does not depend on the auxiliary lifting universe: a bounded-above projective
resolution provides the flat model required by `canonicalLift_ambient_independent`. -/
private lemma canonicalLift_ambient_independent_any
    {A : Type u} [CommRing A] [Small.{m} A]
    (P : CochainComplex (ModuleCat.{m} A) ℤ) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, n}
        (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, x}
        (DerivedCategory.Q.obj P) a b := by
  constructor
  · intro h
    have := canonicalLift_isLE.{u, m, n} P a b h
    obtain ⟨E, g, hg, hE, hEflat⟩ := exists_flat_isStrictlyLE_quasiIso P b
    exact (canonicalLift_ambient_independent.{u, x, m, n} P E a b hE hEflat
      ⟨(asIso (DerivedCategory.Q.map g)).symm⟩).mp h
  · intro h
    have := canonicalLift_isLE.{u, m, x} P a b h
    obtain ⟨E, g, hg, hE, hEflat⟩ := exists_flat_isStrictlyLE_quasiIso P b
    exact (canonicalLift_ambient_independent.{u, x, m, n} P E a b hE hEflat
      ⟨(asIso (DerivedCategory.Q.map g)).symm⟩).mpr h

/-- An equivalence of universe-lifted tor-amplitude predicates for one auxiliary lifting universe
gives the equivalence for any auxiliary lifting universes. -/
private lemma canonicalLift_iff_of_ambient
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B] [Small.{m} A] [Small.{m} B]
    {P : CochainComplex (ModuleCat.{m} A) ℤ} {Q : CochainComplex (ModuleCat.{m} B) ℤ} {a b : ℤ}
    (h : StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, m}
        (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{uh, m, m}
        (DerivedCategory.Q.obj Q) a b) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, m, n} (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{uh, m, x}
        (DerivedCategory.Q.obj Q) a b :=
  (canonicalLift_ambient_independent_any P a b).trans
    (h.trans (canonicalLift_ambient_independent_any Q a b).symm)

/-- `B` seen as an `A`-module through the structure map. This is the left tensor factor through
which extension of scalars is defined. -/
private noncomputable abbrev extendScalarsBaseModule
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat.{uh} A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)

/-- The identification of `extendScalarsBaseModule` with `B` as an `A`-module. -/
private noncomputable def extendScalarsBaseModuleEquiv
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B] [Algebra A B] :
    (extendScalarsBaseModule.{u, uh} (A := A) (B := B) : Type uh) ≃ₗ[A] B := by
  exact
    { Equiv.refl B with
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => by
        rw [ModuleCat.restrictScalars.smul_def]
        simp only [RingHom.id_apply, Algebra.smul_def]
        rfl }

/-- Extension of scalars of a module is its base change `B ⊗[A] N`, as a `B`-module, with the two
rings and the module in independent universes. -/
private noncomputable def extendScalarsCarrierEquivLarge
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B] [Algebra A B]
    (N : ModuleCat.{max m u uh} A) :
    ((ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)).obj N :
      Type (max m u uh)) ≃ₗ[B] TensorProduct A B (N : Type (max m u uh)) := by
  letI : Module B (extendScalarsBaseModule.{u, uh} (A := A) (B := B) : Type uh) :=
    inferInstanceAs (Module B B)
  letI : IsScalarTower A B
      (extendScalarsBaseModule.{u, uh} (A := A) (B := B) : Type uh) :=
    .of_algebraMap_smul fun _ _ => rfl
  letI : Module A ((ModuleCat.extendScalars.{u, uh, max m u uh}
      (algebraMap A B)).obj N : Type (max m u uh)) :=
    Module.compHom _ (algebraMap A B)
  let e := extendScalarsBaseModuleEquiv.{u, uh} (A := A) (B := B)
  letI : Module B (TensorProduct A
      (extendScalarsBaseModule.{u, uh} (A := A) (B := B) : Type uh)
      (N : Type (max m u uh))) := TensorProduct.leftModule
  let E : TensorProduct A
      (extendScalarsBaseModule.{u, uh} (A := A) (B := B) : Type uh)
      (N : Type (max m u uh)) ≃ₗ[A]
      TensorProduct A B (N : Type (max m u uh)) :=
    TensorProduct.congr e (LinearEquiv.refl A (N : Type (max m u uh)))
  refine
    { toFun := fun z => E z
      invFun := fun z => E.symm z
      left_inv := E.left_inv
      right_inv := E.right_inv
      map_add' := E.map_add'
      map_smul' := ?_ }
  have key (b : B) (z : TensorProduct A
      (extendScalarsBaseModule.{u, uh} (A := A) (B := B) : Type uh)
      (N : Type (max m u uh))) : E (b • z) = b • E z := by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul x n =>
        rw [TensorProduct.smul_tmul' b x n]
        change (e (b • x)) ⊗ₜ[A] n = b • ((e x) ⊗ₜ[A] n)
        rw [TensorProduct.smul_tmul' b (e x) n]
        congr 1
    | add x y hx hy =>
        rw [smul_add, map_add, hx, hy, ← smul_add, ← map_add]
  exact key

/-- Extension of scalars along a flat algebra map preserves finite limits, hence is exact, with the
two rings and the modules in independent universes. -/
private lemma extendScalarsLarge_preservesFiniteLimits
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)) := by
  let F : ModuleCat.{max m u uh} A ⥤ ModuleCat.{max m u uh} B :=
    ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)
  have hflatBase : Module.Flat A
      (extendScalarsBaseModule.{u, uh} (A := A) (B := B) : Type uh) :=
    Module.Flat.of_linearEquiv (extendScalarsBaseModuleEquiv.{u, uh} (A := A) (B := B))
  have hadd : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max m u uh, u, uh}
      (algebraMap A B)).left_adjoint_additive
  have hshort : ∀ S : ShortComplex (ModuleCat.{max m u uh} A),
      S.Exact → (S.map F).Exact := by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact @Module.Flat.lTensor_exact A
      (extendScalarsBaseModule.{u, uh} (A := A) (B := B) : Type uh) _ _ _ hflatBase
      _ _ _ _ _ _ _ _ _ _ _ hS
  exact (((Functor.exact_tfae F).out 2 4 rfl rfl).mp hshort).1

/-- Extension of scalars along a flat algebra map preserves homology, with the two rings and the
modules in independent universes. -/
private lemma extendScalarsLarge_preservesHomology
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] :
    (ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)).PreservesHomology := by
  let F : ModuleCat.{max m u uh} A ⥤ ModuleCat.{max m u uh} B :=
    ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)
  have : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max m u uh, u, uh}
      (algebraMap A B)).left_adjoint_additive
  have : PreservesFiniteLimits F :=
    extendScalarsLarge_preservesFiniteLimits.{u, uh, m} (A := A) (B := B)
  have : PreservesColimitsOfSize.{max m u uh, max m u uh} F :=
    (ModuleCat.extendRestrictScalarsAdj.{max m u uh, u, uh}
      (algebraMap A B)).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits F
  exact Functor.preservesHomologyOfExact F

/-- Extension of scalars along a faithfully flat algebra map reflects isomorphisms. -/
private lemma extendScalarsLarge_reflectsIsomorphisms
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] :
    (ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)).ReflectsIsomorphisms := by
  let F : ModuleCat.{max m u uh} A ⥤ ModuleCat.{max m u uh} B :=
    ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)
  refine ⟨fun {X Y} g hg => ?_⟩
  rw [ConcreteCategory.isIso_iff_bijective] at hg ⊢
  let eX := extendScalarsCarrierEquivLarge.{u, uh, m} (A := A) (B := B) X
  let eY := extendScalarsCarrierEquivLarge.{u, uh, m} (A := A) (B := B) Y
  have hmap : (eY : _ → _) ∘ (F.map g).hom =
      (LinearMap.lTensor B g.hom) ∘ (eX : _ → _) := by
    funext z
    show eY ((F.map g).hom z) = LinearMap.lTensor B g.hom (eX z)
    induction z using TensorProduct.induction_on with
    | zero =>
        have h1 : eY ((F.map g).hom 0) = 0 :=
          (congrArg (eY : _ → _) (map_zero (F.map g).hom)).trans (map_zero eY)
        have h2 : LinearMap.lTensor B g.hom (eX 0) = 0 :=
          (congrArg (LinearMap.lTensor B g.hom : _ → _) (map_zero eX)).trans
            (map_zero (LinearMap.lTensor B g.hom))
        exact h1.trans h2.symm
    | tmul s x => rfl
    | add x y hx hy =>
        have h1 : eY ((F.map g).hom (x + y)) =
            eY ((F.map g).hom x) + eY ((F.map g).hom y) :=
          (congrArg (eY : _ → _) (map_add (F.map g).hom x y)).trans (map_add eY _ _)
        have h2 : LinearMap.lTensor B g.hom (eX (x + y)) =
            LinearMap.lTensor B g.hom (eX x) + LinearMap.lTensor B g.hom (eX y) :=
          (congrArg (LinearMap.lTensor B g.hom : _ → _) (map_add eX x y)).trans
            (map_add (LinearMap.lTensor B g.hom) _ _)
        exact h1.trans (by rw [hx, hy]; exact h2.symm)
  have hbij : Function.Bijective (F.map g).hom ↔
      Function.Bijective (LinearMap.lTensor B g.hom) := by
    calc
      _ ↔ Function.Bijective ((eY : _ → _) ∘ (F.map g).hom) :=
        (EquivLike.comp_bijective (F.map g).hom eY).symm
      _ ↔ Function.Bijective ((LinearMap.lTensor B g.hom) ∘ (eX : _ → _)) := by
        rw [hmap]
      _ ↔ _ := EquivLike.bijective_comp eX (LinearMap.lTensor B g.hom)
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B g.hom).mp
    (hbij.mp hg)

/-- A module is zero exactly when its base change along a faithfully flat algebra map is zero. -/
private lemma isZero_extendScalarsLarge_iff
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    (N : ModuleCat.{max m u uh} A) :
    IsZero ((ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)).obj N) ↔
      IsZero N := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  have he : Subsingleton ((ModuleCat.extendScalars.{u, uh, max m u uh}
      (algebraMap A B)).obj N : Type (max m u uh)) ↔
      Subsingleton (TensorProduct A B (N : Type (max m u uh))) :=
    (extendScalarsCarrierEquivLarge.{u, uh, m} (A := A) (B := B) N).toEquiv.subsingleton_congr
  exact he.trans <| Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right A B
    (N := (N : Type (max m u uh)))

/-- Base change along a faithfully flat algebra map does not change which homology objects of a
complex vanish. -/
private lemma isZero_homology_extendScalarsLarge_iff
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    (P : CochainComplex (ModuleCat.{max m u uh} A) ℤ) (i : ℤ) :
    IsZero (((CochainComplex.extendScalarsLarge.{m, u, uh} (algebraMap A B)).obj P).homology i) ↔
      IsZero (P.homology i) := by
  let F : ModuleCat.{max m u uh} A ⥤ ModuleCat.{max m u uh} B :=
    ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)
  have : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max m u uh, u, uh}
      (algebraMap A B)).left_adjoint_additive
  have : F.PreservesHomology := extendScalarsLarge_preservesHomology.{u, uh, m} (A := A) (B := B)
  exact ((P.sc i).mapHomologyIso F).isZero_iff.trans
    (isZero_extendScalarsLarge_iff.{u, uh, m} (P.homology i))

/-- Base change along a faithfully flat algebra map preserves and reflects being supported in
degrees `≥ a`. -/
private lemma isGE_extendScalarsLarge_iff
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    (P : CochainComplex (ModuleCat.{max m u uh} A) ℤ) (a : ℤ) :
    ((CochainComplex.extendScalarsLarge.{m, u, uh} (algebraMap A B)).obj P).IsGE a ↔
      P.IsGE a := by
  simp only [CochainComplex.isGE_iff, exactAt_iff_isZero_homology,
    isZero_homology_extendScalarsLarge_iff.{u, uh, m}]

/-- Base change along a faithfully flat algebra map preserves and reflects being supported in
degrees `≤ b`. -/
private lemma isLE_extendScalarsLarge_iff
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    (P : CochainComplex (ModuleCat.{max m u uh} A) ℤ) (b : ℤ) :
    ((CochainComplex.extendScalarsLarge.{m, u, uh} (algebraMap A B)).obj P).IsLE b ↔
      P.IsLE b := by
  simp only [CochainComplex.isLE_iff, exactAt_iff_isZero_homology,
    isZero_homology_extendScalarsLarge_iff.{u, uh, m}]

/-- For a complex supported in degrees `≤ b`, tor amplitude in `[a, b]` is unchanged by base
change along a faithfully flat algebra map: both sides are read off a bounded-above projective
resolution and its base change. -/
private lemma canonicalLift_extendScalarsLarge_iff_of_isLE
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    [Small.{max m u uh} A]
    (P : CochainComplex (ModuleCat.{max m u uh} A) ℤ) (a b : ℤ) [P.IsLE b] :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, max m u uh, max m u uh}
        (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{uh, max m u uh, max m u uh}
        (DerivedCategory.Q.obj
          ((CochainComplex.extendScalarsLarge.{m, u, uh} (algebraMap A B)).obj P)) a b := by
  let PB := (CochainComplex.extendScalarsLarge.{m, u, uh} (algebraMap A B)).obj P
  let F : ModuleCat.{max m u uh} A ⥤ ModuleCat.{max m u uh} B :=
    ModuleCat.extendScalars.{u, uh, max m u uh} (algebraMap A B)
  have : F.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max m u uh, u, uh}
      (algebraMap A B)).left_adjoint_additive
  have : F.ReflectsIsomorphisms :=
    extendScalarsLarge_reflectsIsomorphisms.{u, uh, m} (A := A) (B := B)
  have : F.PreservesHomology := extendScalarsLarge_preservesHomology.{u, uh, m} (A := A) (B := B)
  obtain ⟨E, g, hg, hEstrict, hEflat⟩ := exists_flat_isStrictlyLE_quasiIso P b
  let EB : CochainComplex (ModuleCat.{max m u uh} B) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj E
  have hEBstrict : EB.IsStrictlyLE b := inferInstance
  have hbase (N : ModuleCat.{max m u uh} A) : Module.Flat B (F.obj N) ↔ Module.Flat A N := by
    let e := extendScalarsCarrierEquivLarge.{u, uh, m} (A := A) (B := B) N
    exact ⟨fun h => ((Module.Flat.iff_flat_tensorProduct A N B).mp (h.of_linearEquiv e.symm)),
      fun h => ((Module.Flat.iff_flat_tensorProduct A N B).mpr h).of_linearEquiv e⟩
  have hEBflat : ∀ i, Module.Flat B (EB.X i) := fun i => (hbase (E.X i)).mpr (hEflat i)
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology g F).mpr inferInstance
  have hcyc : Module.Flat B (EB.opcycles a) ↔ Module.Flat A (E.opcycles a) :=
    (flat_iff_of_iso ((E.sc a).mapOpcyclesIso F)).trans (hbase _)
  exact (moduleLift_iff_flatResolutionCriterion.{u, max m u uh, max m u uh} P E a b
      hEstrict hEflat ⟨(asIso (DerivedCategory.Q.map g)).symm⟩).trans
    (((isGE_extendScalarsLarge_iff.{u, uh, m} (A := A) (B := B) (P := E) a).and hcyc).symm.trans
      (moduleLift_iff_flatResolutionCriterion.{uh, max m u uh, max m u uh} PB EB a b
        hEBstrict hEBflat ⟨(asIso (DerivedCategory.Q.map
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g))).symm⟩).symm)

/-- Tor amplitude in `[a, b]` is unchanged by base change along a faithfully flat algebra map: both
sides are read off a bounded-above projective resolution and its base change. -/
private lemma canonicalLift_extendScalarsLarge_iff
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B]
    [Small.{max m u uh} A] [Small.{max m u uh} B]
    (P : CochainComplex (ModuleCat.{max m u uh} A) ℤ) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u, max m u uh, max m u uh}
        (DerivedCategory.Q.obj P) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{uh, max m u uh, max m u uh}
        (DerivedCategory.Q.obj
          ((CochainComplex.extendScalarsLarge.{m, u, uh} (algebraMap A B)).obj P)) a b := by
  constructor
  · intro hP
    have := canonicalLift_isLE.{u, max m u uh, max m u uh} P a b hP
    exact (canonicalLift_extendScalarsLarge_iff_of_isLE.{u, uh, m} P a b).mp hP
  · intro hPB
    have := (isLE_extendScalarsLarge_iff.{u, uh, m} (A := A) (B := B) (P := P) b).mp
      (canonicalLift_isLE.{uh, max m u uh, max m u uh} _ a b hPB)
    exact (canonicalLift_extendScalarsLarge_iff_of_isLE.{u, uh, m} P a b).mpr hPB

/-- **Tor amplitude is detected by restriction of scalars along a ring map along which flatness
descends.** Let `f : A → B` be a ring map such that a `B`-module is flat over `A` exactly when it
is flat over `B`. Then a complex of `B`-modules has Tor amplitude in `[a, b]` over `A` exactly
when it has Tor amplitude in `[a, b]` over `B`. -/
alias hasTorAmplitudeCanonical_restrictScalars_iff_of_flat_iff := canonical_restrictScalars_iff

variable {R : Type u} {Rh : Type uh} {Rsh : Type ush} [CommRing R] [IsLocalRing R]
  [CommRing Rh] [IsLocalRing Rh] [CommRing Rsh] [IsLocalRing Rsh]
  [Algebra R Rh] [Algebra Rh Rsh] [Algebra R Rsh] [IsScalarTower R Rh Rsh]
  [IsHenselization R (ResidueField R) Rh]
  {K : Type v} [Field K] [Algebra (ResidueField R) K]
  [IsHenselization R K Rsh]

include K R Rsh

/-- The map from the henselization of `R` to a henselization of `R` with a larger residue field is
faithfully flat: it is flat by `Module.Flat.of_isHenselization` and local because both maximal
ideals are extended from the maximal ideal of `R`. -/
private lemma henselizationTower_faithfullyFlat : Module.FaithfullyFlat Rh Rsh := by
  let : Module.Flat R Rsh := IsHenselization.flat (L := K)
  let : Module.Flat Rh Rsh :=
    Module.Flat.of_isHenselization (R := R) (Rh := Rh) (ResidueField R) Rsh
  let : IsLocalHom (algebraMap Rh Rsh) := by
    apply ((local_hom_TFAE (algebraMap Rh Rsh)).out 3 1).mp
    rw [← IsHenselization.map_maximalIdeal (R := R) (L := ResidueField R) (Rh := Rh),
      Ideal.map_map, ← IsScalarTower.algebraMap_eq R Rh Rsh,
      IsHenselization.map_maximalIdeal (R := R) (L := K) (Rh := Rsh)]
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The flatness comparison of `flat_tfae_baseChange_henselization`, transported to the
universe-lifted rings. -/
private lemma flat_tfae_moduleLift_baseChange (N : Type (max u uh ush w))
    [AddCommGroup N]
    [Module (ULift.{max u uh ush w, uh} Rh) N] :
    let fR : ULift.{max u uh ush w, u} R →+*
        ULift.{max u uh ush w, uh} Rh := (algebraMap R Rh).ulift
    letI : Module (ULift.{max u uh ush w, u} R) N :=
      Module.compHom N fR
    List.TFAE
      [Module.Flat (ULift.{max u uh ush w, u} R) N,
       Module.Flat (ULift.{max u uh ush w, uh} Rh) N] := by
  let fR : ULift.{max u uh ush w, u} R →+*
      ULift.{max u uh ush w, uh} Rh := (algebraMap R Rh).ulift
  let : Module Rh N := Module.compHom N
    (ULift.ringEquiv.{uh, max u uh ush w} (R := Rh)).symm.toRingHom
  let : Module R N := Module.compHom N (algebraMap R Rh)
  let : Module (ULift.{max u uh ush w, u} R) N := Module.compHom N fR
  have hRlift : Module.Flat (ULift.{max u uh ush w, u} R) N ↔ Module.Flat R N :=
    Module.Flat.ulift_left_iff
  have hRhlift : Module.Flat (ULift.{max u uh ush w, uh} Rh) N ↔ Module.Flat Rh N :=
    Module.Flat.ulift_left_iff
  have hcard := flat_tfae_baseChange_henselization.{u, uh, ush, v,
    max u uh ush w} (R := R) (Rh := Rh) (Rsh := Rsh) (K := K) (Mh := N)
  have h12 : Module.Flat (ULift.{max u uh ush w, u} R) N ↔
      Module.Flat (ULift.{max u uh ush w, uh} Rh) N :=
    hRlift.trans ((hcard.out 4 5).trans hRhlift.symm)
  tfae_have 1 → 2 := h12.mp
  tfae_have 2 → 1 := h12.mpr
  tfae_finish

/-- The flatness comparison of `flat_tfae_henselization`, transported to the universe-lifted
rings. -/
private lemma flat_tfae_moduleLift (N : Type (max u uh ush w))
    [AddCommGroup N] [Module (ULift.{max u uh ush w, ush} Rsh) N] :
    let fR : ULift.{max u uh ush w, u} R →+*
        ULift.{max u uh ush w, ush} Rsh := (algebraMap R Rsh).ulift
    let fRh : ULift.{max u uh ush w, uh} Rh →+*
        ULift.{max u uh ush w, ush} Rsh := (algebraMap Rh Rsh).ulift
    letI : Module Rsh N := Module.compHom N
      (ULift.ringEquiv.{ush, max u uh ush w} (R := Rsh)).symm.toRingHom
    letI : Module R N := Module.compHom N
      ((ULift.ringEquiv.{ush, max u uh ush w} (R := Rsh)).symm.toRingHom.comp
        (algebraMap R Rsh))
    letI : Module Rh N := Module.compHom N
      ((ULift.ringEquiv.{ush, max u uh ush w} (R := Rsh)).symm.toRingHom.comp
        (algebraMap Rh Rsh))
    letI : Module (ULift.{max u uh ush w, u} R) N := Module.compHom N fR
    letI : Module (ULift.{max u uh ush w, uh} Rh) N := Module.compHom N fRh
    List.TFAE
      [Module.Flat (ULift.{max u uh ush w, u} R) N,
       Module.Flat (ULift.{max u uh ush w, uh} Rh) N,
       Module.Flat (ULift.{max u uh ush w, ush} Rsh) N] := by
  let fR : ULift.{max u uh ush w, u} R →+*
      ULift.{max u uh ush w, ush} Rsh := (algebraMap R Rsh).ulift
  let fRh : ULift.{max u uh ush w, uh} Rh →+*
      ULift.{max u uh ush w, ush} Rsh := (algebraMap Rh Rsh).ulift
  let : Module Rsh N := Module.compHom N
    (ULift.ringEquiv.{ush, max u uh ush w} (R := Rsh)).symm.toRingHom
  let : Module R N := Module.compHom N
    ((ULift.ringEquiv.{ush, max u uh ush w} (R := Rsh)).symm.toRingHom.comp
      (algebraMap R Rsh))
  let : Module Rh N := Module.compHom N
    ((ULift.ringEquiv.{ush, max u uh ush w} (R := Rsh)).symm.toRingHom.comp
      (algebraMap Rh Rsh))
  let : Module (ULift.{max u uh ush w, u} R) N := Module.compHom N fR
  let : Module (ULift.{max u uh ush w, uh} Rh) N := Module.compHom N fRh
  have hRlift : Module.Flat (ULift.{max u uh ush w, u} R) N ↔ Module.Flat R N :=
    Module.Flat.ulift_left_iff
  have hRhlift : Module.Flat (ULift.{max u uh ush w, uh} Rh) N ↔ Module.Flat Rh N :=
    Module.Flat.ulift_left_iff
  have hRshlift : Module.Flat (ULift.{max u uh ush w, ush} Rsh) N ↔
      Module.Flat Rsh N := by
    let : Module (ULift.{max u uh ush w, ush} Rsh) N :=
      Module.compHom N (RingHom.id _)
    show Module.Flat (ULift.{max u uh ush w, ush} Rsh) N ↔ Module.Flat Rsh N
    exact Module.Flat.ulift_left_iff
  have hcard := flat_tfae_henselization.{u, uh, ush, v,
    max u uh ush w}
    (R := R) (Rh := Rh) (Rsh := Rsh) (K := K) (Msh := N)
  have h12 : Module.Flat (ULift.{max u uh ush w, u} R) N ↔
      Module.Flat (ULift.{max u uh ush w, uh} Rh) N :=
    hRlift.trans ((hcard.out 1 2).trans hRhlift.symm)
  have h23 : Module.Flat (ULift.{max u uh ush w, uh} Rh) N ↔
      Module.Flat (ULift.{max u uh ush w, ush} Rsh) N :=
    hRhlift.trans ((hcard.out 2 3).trans hRshlift.symm)
  have h13 : Module.Flat (ULift.{max u uh ush w, u} R) N ↔
      Module.Flat (ULift.{max u uh ush w, ush} Rsh) N :=
    hRlift.trans ((hcard.out 1 3).trans hRshlift.symm)
  tfae_have 1 → 2 := h12.mp
  tfae_have 2 → 1 := h12.mpr
  tfae_have 2 → 3 := h23.mp
  tfae_have 3 → 2 := h23.mpr
  tfae_have 1 → 3 := h13.mp
  tfae_have 3 → 1 := h13.mpr
  tfae_finish

omit K [Field K] in
omit R Rsh [CommRing R] [IsLocalRing R] [CommRing Rsh] [IsLocalRing Rsh]
  [Algebra R Rsh] in
/-- Tor amplitude of a complex of `B`-modules is the same measured over `A`, whenever flatness over
the lift of `A` of a lifted `B`-module is flatness over the lift of `B`. -/
private lemma canonicalLift_restrictScalars_iff
    {A : Type u} {B : Type uh} [CommRing A] [CommRing B]
    (f : A →+* B)
    (hflat : ∀ N : ModuleCat.{max u uh z} (ULift.{max u uh z, uh} B),
      Module.Flat (ULift.{max u uh z, u} A)
        ((ModuleCat.restrictScalars
          f.ulift.{max u uh z, max u uh z}).obj N) ↔
      Module.Flat (ULift.{max u uh z, uh} B) N)
    (P : CochainComplex (ModuleCat.{max u uh z} B) ℤ) (a b : ℤ) :
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{u,
        max u uh z, max u uh z}
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift.{uh,
        max u uh z, max u uh z} (DerivedCategory.Q.obj P) a b := by
  have hleft := canonicalLift_iff_canonical_moduleLift.{u, max u uh z}
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a b
  have hright := canonicalLift_iff_canonical_moduleLift.{uh, max u uh z} P a b
  let LP := (((StacksDraft.TorAmplitude.moduleLift.{uh, max u uh z,
    max u uh z} B).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  let e := moduleLift_restrictScalars_iso.{u, uh, z} f P
  have he : StacksDraft.TorAmplitude.HasTorAmplitudeCanonical (ULift.{max u uh z} A)
      (DerivedCategory.Q.obj
        (((StacksDraft.TorAmplitude.moduleLift.{u, max u uh z,
          max u uh z} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
        a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical (ULift.{max u uh z} A)
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars
            f.ulift.{max u uh z, max u uh z}).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj LP)) a b :=
    hasTorAmplitudeCanonical_iff_of_iso (DerivedCategory.Q.mapIso e) a b
  exact hleft.trans (he.trans
    ((canonical_restrictScalars_iff f.ulift hflat LP a b).trans hright.symm))

/-- **Stacks Project, Tag 0DK0, conditions (1)--(3).** The tor amplitude of a
complex over a henselization with extended residue field is the same whether
it is measured over the original local ring, the henselization with unchanged
residue field, or the extended-residue-field henselization. -/
@[stacks 0DK0 "conditions (1)--(3)"]
public theorem torAmplitude_tfae_henselization
    (Msh : CochainComplex (ModuleCat.{max u uh ush w} Rsh) ℤ) (a b : ℤ) :
    List.TFAE
      [StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap R Rsh)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Msh)) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap Rh Rsh)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Msh)) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
         (DerivedCategory.Q.obj Msh) a b] := by
  have hflatR (N : ModuleCat.{max u uh ush w}
      (ULift.{max u uh ush w, ush} Rsh)) :
      Module.Flat (ULift.{max u uh ush w, u} R)
          ((ModuleCat.restrictScalars
            ((algebraMap R Rsh).ulift.{max u uh ush w, max u uh ush w})).obj N) ↔
        Module.Flat (ULift.{max u uh ush w, ush} Rsh) N :=
    (flat_tfae_moduleLift.{u, uh, ush, v, w}
      (R := R) (Rh := Rh) (Rsh := Rsh) (K := K) (N := N)).out 1 3
  have hflatRh (N : ModuleCat.{max u uh ush w}
      (ULift.{max u uh ush w, ush} Rsh)) :
      Module.Flat (ULift.{max u uh ush w, uh} Rh)
          ((ModuleCat.restrictScalars
            ((algebraMap Rh Rsh).ulift.{max u uh ush w, max u uh ush w})).obj N) ↔
        Module.Flat (ULift.{max u uh ush w, ush} Rsh) N :=
    (flat_tfae_moduleLift.{u, uh, ush, v, w}
      (R := R) (Rh := Rh) (Rsh := Rsh) (K := K) (N := N)).out 2 3
  have h13 := canonicalLift_iff_of_ambient
    (canonicalLift_restrictScalars_iff.{u, ush, max uh w} (A := R) (B := Rsh)
      (f := (algebraMap R Rsh : R →+* Rsh)) hflatR Msh a b)
  have h23 := canonicalLift_iff_of_ambient
    (canonicalLift_restrictScalars_iff.{uh, ush, max u w} (A := Rh) (B := Rsh)
      (f := (algebraMap Rh Rsh : Rh →+* Rsh)) hflatRh Msh a b)
  tfae_have 1 → 3 := h13.mp
  tfae_have 3 → 1 := h13.mpr
  tfae_have 2 → 3 := h23.mp
  tfae_have 3 → 2 := h23.mpr
  tfae_finish

/-- **Stacks Project, Tag 0DK0, conditions (1)--(5).** If the complex over the
extended-residue-field henselization is obtained from a complex over `Rh` by
base change, the preceding three conditions are also equivalent to tor
amplitude of the original complex over `R` and over `Rh`. -/
@[stacks 0DK0 "conditions (1)--(5)"]
public theorem torAmplitude_tfae_baseChange_henselization
    (Mh : CochainComplex (ModuleCat.{max u uh ush w} Rh) ℤ) (a b : ℤ) :
    let Msh := (CochainComplex.extendScalarsLarge.{max u w, uh, ush}
      (algebraMap Rh Rsh)).obj Mh
    List.TFAE
      [StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap R Rsh)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Msh)) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap Rh Rsh)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Msh)) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
         (DerivedCategory.Q.obj Msh) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap R Rh)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Mh)) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
         (DerivedCategory.Q.obj Mh) a b] := by
  dsimp only
  let Msh := (CochainComplex.extendScalarsLarge.{max u w, uh, ush}
    (algebraMap Rh Rsh)).obj Mh
  let : Module.Flat R Rh := IsHenselization.flat (L := ResidueField R)
  let : Module.FaithfullyFlat R Rh :=
    IsHenselization.faithfullyFlat (L := ResidueField R)
  let : Module.Flat R Rsh := IsHenselization.flat (L := K)
  let : Module.FaithfullyFlat R Rsh := IsHenselization.faithfullyFlat (L := K)
  let : Module.Flat Rh Rsh :=
    Module.Flat.of_isHenselization (R := R) (Rh := Rh) (ResidueField R) Rsh
  let : Module.FaithfullyFlat Rh Rsh :=
    henselizationTower_faithfullyFlat (R := R) (Rh := Rh) (Rsh := Rsh) (K := K)
  have h123 := torAmplitude_tfae_henselization.{u, uh, ush, v, w,
      max u uh ush w, max u uh ush w, max u uh ush w}
    (R := R) (Rh := Rh) (Rsh := Rsh) (K := K) Msh a b
  have hflatRh (N : ModuleCat.{max u uh ush w}
      (ULift.{max u uh ush w, uh} Rh)) :
      Module.Flat (ULift.{max u uh ush w, u} R)
          ((ModuleCat.restrictScalars
            (algebraMap R Rh).ulift.{max u uh ush w, max u uh ush w}).obj N) ↔
        Module.Flat (ULift.{max u uh ush w, uh} Rh) N :=
    (flat_tfae_moduleLift_baseChange.{u, uh, ush, v, w}
      (R := R) (Rh := Rh) (Rsh := Rsh) (K := K) (N := N)).out 1 2
  have h45 := canonicalLift_restrictScalars_iff.{u, uh, max ush w} (A := R) (B := Rh)
    (f := (algebraMap R Rh : R →+* Rh)) hflatRh Mh a b
  have h35 := canonicalLift_extendScalarsLarge_iff.{uh, ush, max u w}
    (A := Rh) (B := Rsh) Mh a b
  have h12 := canonicalLift_iff_of_ambient (h123.out 1 2)
  have h23 := canonicalLift_iff_of_ambient (h123.out 2 3)
  have h34 := canonicalLift_iff_of_ambient (h35.symm.trans h45.symm)
  have h45' := canonicalLift_iff_of_ambient h45
  tfae_have 1 → 2 := h12.mp
  tfae_have 2 → 1 := h12.mpr
  tfae_have 2 → 3 := h23.mp
  tfae_have 3 → 2 := h23.mpr
  tfae_have 3 → 4 := h34.mp
  tfae_have 4 → 3 := h34.mpr
  tfae_have 4 → 5 := h45'.mp
  tfae_have 5 → 4 := h45'.mpr
  tfae_finish

/-- **Stacks Project, Tag 0DK0, conditions (1)--(6).** If the complex over `Rh`
is itself obtained by base change from `R`, all five conditions after base
change are equivalent to tor amplitude of the original complex over `R`. -/
@[stacks 0DK0 "conditions (1)--(6)"]
public theorem torAmplitude_tfae_iteratedBaseChange_henselization
    (M : CochainComplex (ModuleCat.{max u uh ush w} R) ℤ) (a b : ℤ) :
    let Mh := (CochainComplex.extendScalarsLarge.{max ush w, u, uh}
      (algebraMap R Rh)).obj M
    let Msh := (CochainComplex.extendScalarsLarge.{max u w, uh, ush}
      (algebraMap Rh Rsh)).obj Mh
    List.TFAE
      [StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap R Rsh)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Msh)) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap Rh Rsh)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Msh)) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
         (DerivedCategory.Q.obj Msh) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
        (DerivedCategory.Q.obj
          (((ModuleCat.restrictScalars (algebraMap R Rh)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Mh)) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
         (DerivedCategory.Q.obj Mh) a b,
       StacksDraft.TorAmplitude.HasTorAmplitudeCanonicalLift
         (DerivedCategory.Q.obj M) a b] := by
  dsimp only
  let Mh := (CochainComplex.extendScalarsLarge.{max ush w, u, uh}
    (algebraMap R Rh)).obj M
  let : Module.Flat R Rh := IsHenselization.flat (L := ResidueField R)
  let : Module.FaithfullyFlat R Rh :=
    IsHenselization.faithfullyFlat (L := ResidueField R)
  let : Module.Flat R Rsh := IsHenselization.flat (L := K)
  let : Module.FaithfullyFlat R Rsh := IsHenselization.faithfullyFlat (L := K)
  let : Module.Flat Rh Rsh :=
    Module.Flat.of_isHenselization (R := R) (Rh := Rh) (ResidueField R) Rsh
  let : Module.FaithfullyFlat Rh Rsh :=
    henselizationTower_faithfullyFlat (R := R) (Rh := Rh) (Rsh := Rsh) (K := K)
  have h15 := torAmplitude_tfae_baseChange_henselization.{u, uh, ush, v, w,
      max u uh ush w, max u uh ush w, max u uh ush w,
      max u uh ush w, max u uh ush w}
    (R := R) (Rh := Rh) (Rsh := Rsh) (K := K) Mh a b
  have h56 := canonicalLift_extendScalarsLarge_iff.{u, uh, max ush w}
    (A := R) (B := Rh) M a b
  have h12 := canonicalLift_iff_of_ambient (h15.out 1 2)
  have h23 := canonicalLift_iff_of_ambient (h15.out 2 3)
  have h34 := canonicalLift_iff_of_ambient (h15.out 3 4)
  have h45 := canonicalLift_iff_of_ambient (h15.out 4 5)
  have h56' := canonicalLift_iff_of_ambient h56.symm
  tfae_have 1 → 2 := h12.mp
  tfae_have 2 → 1 := h12.mpr
  tfae_have 2 → 3 := h23.mp
  tfae_have 3 → 2 := h23.mpr
  tfae_have 3 → 4 := h34.mp
  tfae_have 4 → 3 := h34.mpr
  tfae_have 4 → 5 := h45.mp
  tfae_have 5 → 4 := h45.mpr
  tfae_have 5 → 6 := h56'.mp
  tfae_have 6 → 5 := h56'.mpr
  tfae_finish

end

