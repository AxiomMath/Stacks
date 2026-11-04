module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Functorial
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.WeaklyNormalScheme
public import StacksFrontier.AlgebraicGeometry.SeminormalizationGluing.Basic
public import StacksFrontier.RingTheory.Seminormalization.SeminormalizationInitial

/-!
# The seminormalization of a scheme inside its normalization

Let `X` be a scheme every quasi-compact open of which has finitely many irreducible
components, so that the normalization `ν : Xᵛ ⟶ X` is defined. The seminormalization of `X`
in `ν` and the seminormalization of `X` then agree: both are initial among universal
homeomorphisms onto `X` inducing isomorphisms on residue fields.

The reason is that the source of the canonical morphism from the generic-point residue
fields is a coproduct of spectra of fields, so that morphism lifts — necessarily uniquely —
through every universal homeomorphism onto `X`, and the universal property of the relative
normalization turns such a lift into a morphism out of `Xᵛ`.

## Main results

* `AlgebraicGeometry.existsUnique_iso_seminormalization_seminormalizationFactorization`:
  the unique isomorphism over `X` between the seminormalization of `X` in its normalization
  and the seminormalization of `X`.

## Implementation notes

The equality of the two seminormalizations is recorded as the existence of a unique
isomorphism compatible with the two morphisms to `X`; this is the form in which it is
independent of the choices of initial objects made by
`AlgebraicGeometry.seminormalizationFactorization` and
`AlgebraicGeometry.Scheme.seminormalization`.

`AlgebraicGeometry.Scheme.seminormalization` presupposes an initial object of
`AlgebraicGeometry.SeminormalizationCategory X`, which is Stacks Tag 0EUS.  That construction
is unconditional here: `AlgebraicGeometry.hasInitial_seminormalizationCategory` is a global
instance producing it for an arbitrary scheme by affine gluing, so the statement below carries
no hypothesis on `X` beyond the finiteness of the irreducible components of its quasi-compact
opens, which Tag 0H3Q itself assumes in order to have a normalization at all.

The lift of the generic-point residue fields is built pointwise: a universal homeomorphism
is a homeomorphism on points, so each generic point has a preimage, and the hypothesis that
the residue field maps are isomorphisms turns the residue field at that preimage back into
the residue field downstairs.

## References

* [Stacks Project, Tag 0H3Q](https://stacks.math.columbia.edu/tag/0H3Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Two morphisms from the spectrum of a residue field of `X` to a universal homeomorphism
over `X` agree as soon as they agree after composing with the structure morphism. -/
private theorem specResidueField_hom_ext {T : Scheme.{u}} (q : T ⟶ X)
    (hq : UniversalHomeomorphism q) (x : X)
    (f g : Spec (.of (X.residueField x)) ⟶ T)
    (hf : f ≫ q = X.fromSpecResidueField x) (hg : g ≫ q = X.fromSpecResidueField x) :
    f = g := by
  have hinj := (tfae_universallyInjective q).out 1 2 |>.mp
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective q).mp hq).2.1
  apply hinj (X.residueField x)
  show f ≫ q = g ≫ q
  rw [hf, hg]

/-- The generic-point residue fields lift in at most one way through a universal
homeomorphism onto `X`. -/
private theorem genericPointResidueSpectrum_hom_ext {T : Scheme.{u}} (q : T ⟶ X)
    (hq : UniversalHomeomorphism q)
    (f g : X.genericPointResidueSpectrum ⟶ T)
    (hf : f ≫ q = X.fromGenericPointResidueFields)
    (hg : g ≫ q = X.fromGenericPointResidueFields) : f = g := by
  let D := fun η : genericPoints X => Spec (.of (X.residueField η.1))
  let f' : (∐ D) ⟶ T := f
  let g' : (∐ D) ⟶ T := g
  let v : (∐ D) ⟶ X := X.fromGenericPointResidueFields
  have hf' : f' ≫ q = v := by
    simpa [f', v, D, Scheme.genericPointResidueSpectrum] using hf
  have hg' : g' ≫ q = v := by
    simpa [g', v, D, Scheme.genericPointResidueSpectrum] using hg
  show f' = g'
  apply Sigma.hom_ext
  intro η
  have key : ∀ h : (∐ D) ⟶ T, h ≫ q = v → (Sigma.ι D η ≫ h) ≫ q = X.fromSpecResidueField η.1 :=
    fun h hh => by
      rw [Category.assoc, hh]
      exact X.genericPointResidueSpectrum_ι_fromGenericPointResidueFields η
  exact specResidueField_hom_ext q hq η.1 _ _ (key f' hf') (key g' hg')

/-- The lift of the spectrum of the residue field at `x` through a universal homeomorphism onto
`X` inducing isomorphisms on residue fields. -/
private def specResidueFieldLift {T : Scheme.{u}} (q : T ⟶ X)
    (hq : UniversalHomeomorphism q) (hres : ∀ z : T, IsIso (q.residueFieldMap z)) (x : X) :
    Spec (.of (X.residueField x)) ⟶ T :=
  let htop : IsHomeomorph q.base :=
    hq.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  let z : T := Classical.choose (htop.surjective x)
  have hz : q z = x := Classical.choose_spec (htop.surjective x)
  have : IsIso (q.residueFieldMap z) := hres z
  Spec.map ((asIso (q.residueFieldMap z)).inv ≫ (X.residueFieldCongr hz).hom) ≫
    T.fromSpecResidueField z

private theorem specResidueFieldLift_comp {T : Scheme.{u}} (q : T ⟶ X)
    (hq : UniversalHomeomorphism q) (hres : ∀ z : T, IsIso (q.residueFieldMap z)) (x : X) :
    specResidueFieldLift q hq hres x ≫ q = X.fromSpecResidueField x := by
  rw [specResidueFieldLift, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp]
  simp

/-- The lift of the generic-point residue fields through a universal homeomorphism onto `X`
inducing isomorphisms on residue fields. -/
private def genericPointResidueSpectrumLift {T : Scheme.{u}} (q : T ⟶ X)
    (hq : UniversalHomeomorphism q) (hres : ∀ z : T, IsIso (q.residueFieldMap z)) :
    X.genericPointResidueSpectrum ⟶ T :=
  Sigma.desc fun η : genericPoints X => specResidueFieldLift q hq hres η.1

private theorem genericPointResidueSpectrumLift_comp {T : Scheme.{u}} (q : T ⟶ X)
    (hq : UniversalHomeomorphism q) (hres : ∀ z : T, IsIso (q.residueFieldMap z)) :
    genericPointResidueSpectrumLift q hq hres ≫ q = X.fromGenericPointResidueFields := by
  let D := fun η : genericPoints X => Spec (.of (X.residueField η.1))
  let l : (∐ D) ⟶ T := genericPointResidueSpectrumLift q hq hres
  let v : (∐ D) ⟶ X := X.fromGenericPointResidueFields
  show l ≫ q = v
  apply Sigma.hom_ext
  intro η
  rw [← Category.assoc, show Sigma.ι D η ≫ l = specResidueFieldLift q hq hres η.1 by
    simp [l, genericPointResidueSpectrumLift, D]]
  exact (specResidueFieldLift_comp q hq hres η.1).trans
    (X.genericPointResidueSpectrum_ι_fromGenericPointResidueFields η).symm

/-- Two morphisms out of the normalization of `X` into a universal homeomorphism over `X`
agree as soon as they are compatible with the normalization morphism. -/
private theorem normalization_hom_ext_of_universalHomeomorphism
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {T : Scheme.{u}} (q : T ⟶ X) (hq : UniversalHomeomorphism q)
    {a b : Scheme.normalizationScheme X hX ⟶ T}
    (ha : a ≫ q = Scheme.normalization X hX) (hb : b ≫ q = Scheme.normalization X hX) :
    a = b := by
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  let f := X.fromGenericPointResidueFields
  have : IsIntegralHom q :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective q).mp hq |>.1
  have key : ∀ c : Scheme.normalizationScheme X hX ⟶ T, c ≫ q = Scheme.normalization X hX →
      (f.toNormalization ≫ c) ≫ q = f := fun c hc => by
    rw [Category.assoc, hc]
    exact Scheme.Hom.toNormalization_fromNormalization (f := f)
  have hpre : f.toNormalization ≫ a = f.toNormalization ≫ b :=
    genericPointResidueSpectrum_hom_ext q hq _ _ (key a ha) (key b hb)
  exact Scheme.Hom.normalization.hom_ext (f := f) a b q hpre ha hb

/-- **Stacks Project, Tag 0H3Q.** If every quasi-compact open of `X` has finitely many
irreducible components, the seminormalization of `X` in its normalization is canonically
isomorphic over `X` to the seminormalization of `X`. -/
@[stacks 0H3Q "the seminormalization of `X` in its normalization agrees with the
seminormalization of `X`; the only hypothesis is the tag's own assumption `hX` that every
quasi-compact open of `X` has finitely many irreducible components, which is what makes the
normalization of `X` exist"]
theorem existsUnique_iso_seminormalization_seminormalizationFactorization (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    letI := Scheme.quasiCompactFromGenericPointResidueFields X hX
    letI := Scheme.quasiSeparatedFromGenericPointResidueFields X
    letI := Scheme.normalization_isDominant X hX
    ∃! e : (seminormalizationFactorization (Scheme.normalization X hX)).middle ≅
        X.seminormalization,
      e.hom ≫ X.seminormalizationHom =
        (seminormalizationFactorization (Scheme.normalization X hX)).toBase := by
  let := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let := Scheme.quasiSeparatedFromGenericPointResidueFields X
  let := Scheme.normalization_isDominant X hX
  let f := X.fromGenericPointResidueFields
  let S := X.seminormalization
  let q := X.seminormalizationHom
  have hqhomeo : UniversalHomeomorphism q :=
    (initial (SeminormalizationCategory X)).property.1
  have hqres : ∀ z : S, IsIso (q.residueFieldMap z) :=
    (initial (SeminormalizationCategory X)).property.2
  have : IsIntegralHom q :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective q).mp hqhomeo |>.1
  let lift := genericPointResidueSpectrumLift q hqhomeo hqres
  have hlift : lift ≫ q = f := genericPointResidueSpectrumLift_comp q hqhomeo hqres
  let nToS : Scheme.normalizationScheme X hX ⟶ S := f.normalizationDesc lift q hlift.symm
  have hnToS : nToS ≫ q = Scheme.normalization X hX :=
    f.normalizationDesc_comp lift q hlift.symm
  let F := seminormalizationFactorization (Scheme.normalization X hX)
  let hF := seminormalizationFactorizationIsInitial (Scheme.normalization X hX)
  let B : SubintegralFactorization (Scheme.normalization X hX) :=
    ⟨S, nToS, q, hnToS, hqhomeo, hqres⟩
  let m := hF.to B
  let C : SeminormalizationCategory X :=
    ⟨Over.mk F.toBase, F.universalHomeomorphism, F.residueFieldIsomorphisms⟩
  let n := initial.to C
  let k : S ⟶ F.middle := n.hom.left
  have hkbase : k ≫ F.toBase = q := by simpa [C, k] using n.hom.w
  have hsource : F.toMiddle ≫ m.hom ≫ k = F.toMiddle := by
    calc
      F.toMiddle ≫ m.hom ≫ k = (F.toMiddle ≫ m.hom) ≫ k := by rw [Category.assoc]
      _ = nToS ≫ k := by simpa [B] using congrArg (fun t => t ≫ k) m.toMiddle_hom
      _ = F.toMiddle :=
        normalization_hom_ext_of_universalHomeomorphism hX F.toBase F.universalHomeomorphism
          (a := nToS ≫ k) (b := F.toMiddle) (by rw [Category.assoc, hkbase, hnToS]) F.fac
  have hbase : (m.hom ≫ k) ≫ F.toBase = F.toBase := by
    calc
      (m.hom ≫ k) ≫ F.toBase = m.hom ≫ q := by rw [Category.assoc, hkbase]
      _ = F.toBase := by simpa [B] using m.hom_toBase
  let mm : F ⟶ F := ⟨m.hom ≫ k, hsource, hbase⟩
  let idF : F ⟶ F := ⟨𝟙 F.middle, by simp, by simp⟩
  have hmInv : m.hom ≫ k = 𝟙 F.middle := by
    simpa [mm, idF] using congrArg (fun t : F ⟶ F => t.hom) (hF.hom_ext mm idF)
  have hkmBase : (k ≫ m.hom) ≫ q = q := by
    calc
      (k ≫ m.hom) ≫ q = k ≫ F.toBase := by
        rw [Category.assoc]
        simpa [B] using congrArg (fun t => k ≫ t) m.hom_toBase
      _ = q := hkbase
  let abs := initial (SeminormalizationCategory X)
  let kk : abs ⟶ abs := ObjectProperty.homMk (Over.homMk (k ≫ m.hom) hkmBase)
  have hkInv : k ≫ m.hom = 𝟙 S := by
    simpa [kk, abs, S, q] using
      congrArg (fun t : abs ⟶ abs => t.hom.left) (initial.hom_ext kk (𝟙 abs))
  refine ⟨⟨m.hom, k, hmInv, hkInv⟩, ?_, ?_⟩
  · show m.hom ≫ q = F.toBase
    simpa [B] using m.hom_toBase
  · intro e' he'
    have hsource' : F.toMiddle ≫ e'.hom = nToS :=
      normalization_hom_ext_of_universalHomeomorphism hX q hqhomeo
        (a := F.toMiddle ≫ e'.hom) (b := nToS) (by rw [Category.assoc, he', F.fac]) hnToS
    let mm' : F ⟶ B := ⟨e'.hom, by simpa [B] using hsource', by simpa [B] using he'⟩
    apply Iso.ext
    simpa [mm'] using congrArg (fun t : F ⟶ B => t.hom) (hF.hom_ext mm' m)

end AlgebraicGeometry

end
