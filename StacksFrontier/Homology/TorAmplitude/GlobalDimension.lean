module

public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import StacksFrontier.Algebra.Homology.ProjectiveDimension
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.RingTheory.GlobalDimension.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor dimension over a ring of bounded global dimension

Let `R` be a commutative ring of global dimension at most `d`. Then every `R`-module has Tor
dimension at most `d`, a complex whose cohomology is concentrated in `[a, b]` has Tor amplitude
in `[a - d, b]`, and a complex has finite Tor dimension exactly when it lies in the bounded
derived category.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitude_single_of_globalDimension_le`: a module placed in
  degree `0` has Tor amplitude in `[-d, 0]`, i.e. Tor dimension at most `d`.
* `StacksDraft.TorAmplitude.hasTorAmplitude_widen`: monotonicity of Tor amplitude in the
  interval.
* `StacksDraft.TorAmplitude.bounded_of_hasTorAmplitude`: a complex of finite Tor dimension lies
  in the bounded derived category.
* `StacksDraft.TorAmplitude.hasTorAmplitude_of_isZero_homology`: a complex whose cohomology is
  concentrated in `[a, b]` has Tor amplitude in `[a - d, b]`.
* `StacksDraft.TorAmplitude.torAmplitude_and_finiteTorDimension_of_globalDimension_le`:
  the three statements of Stacks 066P.

## Implementation notes

Tor amplitude is `StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude`, which computes `K ⊗_R^L
  M` as `K ⊗ P` for the
chosen projective resolution `P` of `M`; global dimension is `ringGlobalDimension`. Membership
in the bounded derived category is the bounded-object property of the canonical `t`-structure on
`D(R)` applied to the image of the complex under the localisation functor.

Because `StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude` evaluates `K ⊗ P` at the *chosen*
  projective resolution `P`
of `M`, the amplitude bound of part (2) is obtained by moving both tensor factors, never by
computing a derived tensor product: the first factor `K` is replaced by a bounded above complex
of projectives and then by its canonical truncation, and the second factor by a projective
resolution of `M` of length `d`, which exists because global dimension at most `d` bounds the
projective dimension of `M`. Each replacement is a quasi-isomorphism between K-flat complexes, so
it is inverted after tensoring (`quasiIso_tensorRight_map`, `quasiIso_tensorLeft_map`), and the
resulting complex is a tensor product of a complex concentrated in `[a, b]` with one concentrated
in `[-d, 0]`, hence vanishes degreewise outside `[a - d, b]`.

## References

* [Stacks Project, Tag 066P](https://stacks.math.columbia.edu/tag/066P)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace StacksDraft.TorAmplitude

universe u v

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-- Tensoring on the left with a fixed complex preserves homotopy equivalences. -/
public noncomputable def tensorLeftHomotopyEquiv
    {R : Type u} [CommRing R] (L : CochainComplex (ModuleCat.{u} R) ℤ)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (h : HomotopyEquiv P Q) :
    HomotopyEquiv ((tensorLeft L).obj P) ((tensorLeft L).obj Q) where
  hom := (tensorLeft L).map h.hom
  inv := (tensorLeft L).map h.inv
  homotopyHomInvId := by
    rw [← (tensorLeft L).map_comp, ← (tensorLeft L).map_id]
    exact HomologicalComplex.mapBifunctorMapHomotopy₂
      (K₁ := L) (L₁ := L) (K₂ := P) (L₂ := P) (f₁ := 𝟙 L) h.homotopyHomInvId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)
  homotopyInvHomId := by
    rw [← (tensorLeft L).map_comp, ← (tensorLeft L).map_id]
    exact HomologicalComplex.mapBifunctorMapHomotopy₂
      (K₁ := L) (L₁ := L) (K₂ := Q) (L₂ := Q) (f₁ := 𝟙 L) h.homotopyInvHomId
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)

/-- Over a ring of global dimension at most `d`, every module has projective dimension at
most `d`. -/
public theorem hasProjectiveDimensionLE_of_globalDimension_le (R : Type u) [CommRing R] (d : ℕ)
    (hR : ringGlobalDimension R ≤ d) (M : ModuleCat.{u} R) :
    HasProjectiveDimensionLE M d := by
  rw [← projectiveDimension_le_iff]
  exact (le_iSup (fun N : ModuleCat.{u} R ↦ projectiveDimension N) M).trans hR

/-- The left derived functors of an additive functor vanish on an object of projective
dimension at most `d` in degrees above `d`. -/
@[ega "0 17.2.2" "(ii), special case"]
public theorem isZero_leftDerived_of_hasProjectiveDimensionLE
    {C : Type v} [Category.{u} C] [Abelian C] [HasProjectiveResolutions C]
    (F : Functor C C) [F.Additive] (X : C) (d n : ℕ)
    (hX : HasProjectiveDimensionLE X d) (hdn : d < n) :
    IsZero ((F.leftDerived n).obj X) := by
  obtain ⟨P, hP⟩ :=
    ((CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution X d).out 1 2).mp hX
  exact (ShortComplex.isZero_homology_of_isZero_X₂ _ (F.map_isZero (hP n hdn))).of_iso
    ((P.toProjectiveResolution P.property).isoLeftDerivedObj F n)

/-- **Stacks 066P (1).** Over a ring of global dimension at most `d`, every module placed in
cohomological degree `0` has Tor amplitude in `[-d, 0]`; that is, every module has Tor
dimension at most `d`. -/
public theorem hasTorAmplitude_single_of_globalDimension_le (R : Type u) [CommRing R] (d : ℕ)
    (hR : ringGlobalDimension R ≤ d) (N : ModuleCat.{u} R) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) (-(d : ℤ)) 0 := by
  intro M i hi
  rcases hi with hi | hi
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
    exact (isZero_leftDerived_of_hasProjectiveDimensionLE (tensorLeft N) M d n
      (hasProjectiveDimensionLE_of_globalDimension_le R d hR M) (by omega)).of_iso
      (FaithfullyFlat.derivedTensorHomologySingle₀Iso N M n)
  · rw [FaithfullyFlat.derivedTensorHomology, ← HomologicalComplex.exactAt_iff_isZero_homology]
    apply ShortComplex.exact_of_isZero_X₂
    show IsZero (((tensorLeft
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).obj
        (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)).X i)
    have hz : IsZero
        ((((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)).X i) := by
      apply (tensorLeft N).map_isZero
      show IsZero (HomologicalComplex.extend.X (ProjectiveResolution.of M).complex
        (ComplexShape.embeddingDownNat.r i))
      rw [show ComplexShape.embeddingDownNat.r i = none by
        apply ComplexShape.Embedding.r_eq_none
        intro n hn
        rw [show ComplexShape.embeddingDownNat.f n = -(n : ℤ) from rfl] at hn
        omega]
      exact isZero_zero _
    exact hz.of_iso ((HomologicalComplex.eval _ _ i).mapIso
      (StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso N
        (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)))

/-- Derived tensoring with the unit module `R` recovers the cohomology of the complex. -/
public noncomputable def derivedTensorHomologyUnitIso (R : Type u) [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology K (ModuleCat.of R R) i ≅
      K.homology i := by
  let P := ProjectiveResolution.of (ModuleCat.of R R)
  let Q := ProjectiveResolution.self (ModuleCat.of R R)
  let e := ProjectiveResolution.homotopyEquiv P Q
  let ee := FaithfullyFlat.homotopyEquivExtendDownNat e
  let te := tensorLeftHomotopyEquiv K ee
  let eu : Q.complex.extend ComplexShape.embeddingDownNat ≅
      HomologicalComplex.tensorUnit (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat (ModuleCat.of R R) 0 0 rfl
  exact (te.toHomologyIso i).trans
    (((HomologicalComplex.homologyFunctor _ _ i).mapIso ((tensorLeft K).mapIso eu)).trans
      ((HomologicalComplex.homologyFunctor _ _ i).mapIso
        (HomologicalComplex.rightUnitor K)))

/-- Tor amplitude is monotone in the interval: an amplitude bound in `[a, b]` also holds in any
larger interval `[a', b']`. -/
public theorem hasTorAmplitude_widen {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b a' b' : ℤ}
    (ha : a' ≤ a) (hb : b ≤ b')
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a' b' :=
  fun M i hi => h M i (hi.imp (·.trans_le ha) hb.trans_lt)

/-- A complex of finite Tor dimension has bounded cohomology, hence lies in the bounded
derived category. This is the forward implication of Stacks 066P (3). -/
@[sga "6 III 3.2" "special case"]
public theorem bounded_of_hasTorAmplitude {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) {a b : ℤ}
    (h : StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b) :
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).bounded
      (DerivedCategory.Q.obj K) := by
  have hz (i : ℤ) (hi : i < a ∨ b < i) : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} R) i).obj (DerivedCategory.Q.obj K)) :=
    ((h (ModuleCat.of R R) i hi).of_iso (derivedTensorHomologyUnitIso R K i).symm).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K)
  exact ⟨⟨a, (DerivedCategory.isGE_iff _ _).2 fun i hi => hz i (.inl hi)⟩,
    ⟨b, (DerivedCategory.isLE_iff _ _).2 fun i hi => hz i (.inr hi)⟩⟩

/-! ### Tor amplitude from bounded cohomology -/

/-- The extension by zero of a projective resolution is strictly bounded above by `0` and
consists of projective objects. -/
private theorem isStrictlyLE_and_projective_extend {R : Type u} [CommRing R] {M : ModuleCat.{u} R}
    (G : ProjectiveResolution M) :
    CochainComplex.IsStrictlyLE (G.complex.extend ComplexShape.embeddingDownNat) 0 ∧
      ∀ i, Projective ((G.complex.extend ComplexShape.embeddingDownNat).X i) :=
  ⟨inferInstance, fun _ => inferInstance⟩

/-- A module of projective dimension at most `d` admits a projective resolution which, read as a
cochain complex in nonpositive degrees, is concentrated in `[-d, 0]`, and which is homotopy
equivalent to the chosen projective resolution used by
  `StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomology`. -/
public theorem exists_projResComplex_isStrictlyGE (R : Type u) [CommRing R] (d : ℕ)
    (hR : ringGlobalDimension R ≤ d) (M : ModuleCat.{u} R) :
    ∃ Q : CochainComplex (ModuleCat.{u} R) ℤ,
      Q.IsStrictlyGE (-(d : ℤ)) ∧ Q.IsStrictlyLE 0 ∧ (∀ i : ℤ, Projective (Q.X i)) ∧
        Nonempty (HomotopyEquiv Q (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M)) := by
  obtain ⟨F, hF⟩ :=
    ((CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution M d).out 1 2).mp
      (hasProjectiveDimensionLE_of_globalDimension_le R d hR M)
  let G : ProjectiveResolution M := F.toProjectiveResolution F.property
  refine ⟨(ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} R)).obj G.complex,
    ?_, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    by_cases h : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = i
    · obtain ⟨n, hn⟩ := h
      have hnd : d < n := by
        have hn' : -(n : ℤ) = i := hn
        omega
      exact (hF n hnd).of_iso
        (G.complex.extendXIso ComplexShape.embeddingDownNat hn)
    · exact G.complex.isZero_extend_X ComplexShape.embeddingDownNat i
        (fun n hn => h ⟨n, hn⟩)
  · exact (isStrictlyLE_and_projective_extend G).1
  · exact (isStrictlyLE_and_projective_extend G).2
  · exact ⟨FaithfullyFlat.homotopyEquivExtendDownNat
      (ProjectiveResolution.homotopyEquiv G (ProjectiveResolution.of M))⟩

/-- The degree-`n` term of a tensor product of two strictly bounded complexes vanishes as soon as
no pair of degrees from the two windows adds up to `n`: the term is a coproduct over the
antidiagonal, and each summand has a zero factor. -/
public theorem isZero_tensorObj_X {R : Type u} [CommRing R]
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (a b c e : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] [L.IsStrictlyGE c] [L.IsStrictlyLE e]
    (n : ℤ) (hn : n < a + c ∨ b + e < n) : IsZero ((K ⊗ L).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  have hsum : i + j = n := hij
  have hz : IsZero (((curriedTensor (ModuleCat.{u} R)).obj (K.X i)).obj (L.X j)) := by
    rcases hn with hn | hn
    · by_cases hi : i < a
      · exact (tensorRight (L.X j)).map_isZero
          (CochainComplex.isZero_of_isStrictlyGE K a i hi)
      · exact ((curriedTensor (ModuleCat.{u} R)).obj (K.X i)).map_isZero
          (CochainComplex.isZero_of_isStrictlyGE L c j (by omega))
    · by_cases hi : b < i
      · exact (tensorRight (L.X j)).map_isZero
          (CochainComplex.isZero_of_isStrictlyLE K b i hi)
      · exact ((curriedTensor (ModuleCat.{u} R)).obj (K.X i)).map_isZero
          (CochainComplex.isZero_of_isStrictlyLE L e j (by omega))
  exact hz.eq_of_src _ _

/-- The homology isomorphism attached to a quasi-isomorphism. -/
private noncomputable def homologyIsoOfQuasiIso {R : Type u} [CommRing R]
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) [hf : QuasiIso f] (i : ℤ) :
    X.homology i ≅ Y.homology i :=
  have : IsIso (HomologicalComplex.homologyMap f i) :=
    (quasiIsoAt_iff_isIso_homologyMap f i).mp (hf.quasiIsoAt i)
  asIso (HomologicalComplex.homologyMap f i)


/-- A quasi-isomorphism preserves vanishing of homology. -/
private theorem isZero_homology_iff_of_quasiIso {R : Type u} [CommRing R]
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) [hf : QuasiIso f] (i : ℤ) :
    IsZero (X.homology i) ↔ IsZero (Y.homology i) :=
  have : IsIso (HomologicalComplex.homologyMap f i) :=
    (quasiIsoAt_iff_isIso_homologyMap f i).mp (hf.quasiIsoAt i)
  (asIso (HomologicalComplex.homologyMap f i)).isZero_iff

/-- **Stacks 066P (2).** Over a ring of global dimension at most `d`, a complex whose cohomology
is concentrated in `[a, b]` has Tor amplitude in `[a - d, b]`. -/
public theorem hasTorAmplitude_of_isZero_homology (R : Type u) [CommRing R] (d : ℕ)
    (hR : ringGlobalDimension R ≤ d) (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hK : ∀ i : ℤ, (i < a ∨ b < i) → IsZero (K.homology i)) :
    StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K (a - d) b := by
  intro M i hi
  obtain ⟨Q, hQGE, hQLE, hQproj, ⟨eQ⟩⟩ := exists_projResComplex_isStrictlyGE R d hR M
  have := hQGE
  have := hQLE
  -- The chosen projective resolution of `M`, and the length-`d` one, are both K-flat.
  obtain ⟨hPMLE, hPMproj⟩ := isStrictlyLE_and_projective_extend (ProjectiveResolution.of M)
  have : (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M).IsStrictlyLE 0 := hPMLE
  have hPMKF : (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M).KFlat :=
    kFlat_of_isStrictlyLE_projective (StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M) 0
      hPMproj
  have hQKF : Q.KFlat := kFlat_of_isStrictlyLE_projective Q 0 hQproj
  -- Replace `K` by a bounded above complex of projectives.
  have hKLE : K.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hK j (Or.inr hj)
  have hι : QuasiIso (K.ιTruncLE b) := (CochainComplex.quasiIso_ιTruncLE_iff K b).2 hKLE
  obtain ⟨PR, -⟩ := ProjectiveResolutionLemma.statement3 b (K.truncLE b) inferInstance
  set P := PR.complex
  have hPLE : P.IsStrictlyLE b := PR.boundedAbove
  have := hPLE
  have hφ : QuasiIso (PR.α ≫ K.ιTruncLE b) := quasiIso_comp (hφ := PR.quasiIso) (hφ' := hι) _ _
  have hPKF : P.KFlat := kFlat_of_isStrictlyLE_projective P b PR.projective
  -- `P` has no cohomology below `a`, so its canonical truncation at `a` is quasi-isomorphic.
  have hPGE : P.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have := hφ
    exact (isZero_homology_iff_of_quasiIso (PR.α ≫ K.ιTruncLE b) j).2 (hK j (Or.inl hj))
  have := hPGE
  have hτ : QuasiIso (P.πTruncGE a) := (CochainComplex.quasiIso_πTruncGE_iff P a).2 hPGE
  have hτLE : (P.truncGE a).IsStrictlyLE b := truncGE_isStrictlyLE P a b hPLE
  have := hτLE
  -- The tensor product of the two truncations vanishes degreewise outside `[a - d, b]`;
  -- transport this back along the three quasi-isomorphisms.
  have h1 : IsZero ((P ⊗ Q).homology i) := by
    have := hτ
    have := quasiIso_tensorRight_map hQKF (P.πTruncGE a)
    exact (isZero_homology_iff_of_quasiIso ((tensorRight Q).map (P.πTruncGE a)) i).2
      (ShortComplex.isZero_homology_of_isZero_X₂ _
        (isZero_tensorObj_X (P.truncGE a) Q a b (-(d : ℤ)) 0 i (by omega)))
  have h2 : IsZero ((P ⊗ StacksDraft.TorAmplitude.FaithfullyFlat.projResComplex M).homology i) := by
    have := quasiIso_tensorLeft_map P hPKF eQ.hom
    exact (isZero_homology_iff_of_quasiIso ((tensorLeft P).map eQ.hom) i).1 h1
  have := quasiIso_tensorRight_map hPMKF (PR.α ≫ K.ιTruncLE b)
  exact (isZero_homology_iff_of_quasiIso
    ((tensorRight (FaithfullyFlat.projResComplex M)).map (PR.α ≫ K.ιTruncLE b)) i).1 h2

/-! ### Stacks 066P -/

/-- **Stacks 066P.** Let `R` be a ring of global dimension at most `d`. Then

1. every `R`-module placed in degree `0` has Tor amplitude in `[-d, 0]`, i.e. Tor dimension at
   most `d`;
2. a complex whose cohomology is concentrated in `[a, b]` has Tor amplitude in `[a - d, b]`;
3. a complex has finite Tor dimension if and only if it lies in the bounded derived
   category. -/
@[stacks 066P, sga "6 I 5.9" "special case", sga "6 III 3.2" "special case"]
public theorem torAmplitude_and_finiteTorDimension_of_globalDimension_le
    (R : Type u) [CommRing R] (d : ℕ) (hR : ringGlobalDimension R ≤ d) :
    (∀ M : ModuleCat.{u} R,
      StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) (-(d : ℤ)) 0) ∧
    (∀ (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (K.homology i)) →
        StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K (a - d) b) ∧
    (∀ K : CochainComplex (ModuleCat.{u} R) ℤ,
      (∃ a b : ℤ, StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude K a b) ↔
        (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).bounded
          (DerivedCategory.Q.obj K)) := by
  refine ⟨hasTorAmplitude_single_of_globalDimension_le R d hR,
    hasTorAmplitude_of_isZero_homology R d hR,
    fun K => ⟨fun ⟨_, _, h⟩ => bounded_of_hasTorAmplitude K h, ?_⟩⟩
  rintro ⟨⟨c, hc⟩, ⟨e, he⟩⟩
  refine ⟨c - d, e, hasTorAmplitude_of_isZero_homology R d hR K c e (fun i hi => ?_)⟩
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (DerivedCategory.Q.obj K)) := by
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ c).1 hc i hi
    · exact (DerivedCategory.isLE_iff _ e).1 he i hi
  exact hz.of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K).symm

end

end StacksDraft.TorAmplitude
