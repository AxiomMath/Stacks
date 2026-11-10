module

public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.Star
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.RingTheory.Nagata.Universes
public import StacksFrontier.RingTheory.Nagata.Examples
public import StacksFrontier.RingTheory.Nagata.MonogenicN1
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import Mathlib.RingTheory.KrullDimension.PID

/-!
# The affine line with infinitely many origins

Over a field `k`, glue countably many copies of the affine line `Spec k[t]` along the punctured
line `Spec k[t, t⁻¹]`. The result is an integral scheme, regular of dimension one and Nagata,
which is not quasi-compact: each origin has a neighbourhood containing no other origin. It is the
base of the counterexample to Tags 0BRQ and 0BRS as stated in the source.

## Main definitions

* `AlgebraicGeometry.ReducedFibreCurveCounterexample.base`: the line with infinitely many origins.
* `AlgebraicGeometry.ReducedFibreCurveCounterexample.baseι`: its charts, one copy of the affine
  line for every natural number.

## Main results

* `AlgebraicGeometry.ReducedFibreCurveCounterexample.isIntegral_base`: the line with infinitely
  many origins is integral.
* `AlgebraicGeometry.ReducedFibreCurveCounterexample.isRegular_base`: it is regular.
* `AlgebraicGeometry.ReducedFibreCurveCounterexample.isNagataScheme_base`: it is Nagata.
* `AlgebraicGeometry.ReducedFibreCurveCounterexample.topologicalKrullDim_base`: it has dimension
  one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.ReducedFibreCurveCounterexample

variable (k : Type u) [Field k]

/-- The affine line `Spec k[t]`. -/
abbrev line : Scheme.{u} := Spec (.of k[X])

/-- The punctured affine line `Spec k[t, t⁻¹]`. -/
abbrev puncturedLine : Scheme.{u} := Spec (.of (Localization.Away (X : k[X])))

/-- The inclusion of the punctured line into the line. -/
def puncturedLineι : puncturedLine k ⟶ line k :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (X : k[X]))))

/-- The inclusion of the punctured line into the line is an open immersion. -/
instance : IsOpenImmersion (puncturedLineι k) := by
  dsimp [puncturedLineι]; infer_instance

/-- **The line with infinitely many origins**: copies of the affine line, one for each natural
number, glued along the punctured line. -/
def base : Scheme.{u} := StarGlue.glued (fun _ : ℕ ↦ line k) (fun _ ↦ puncturedLineι k)

/-- The `n`-th chart of the line with infinitely many origins. -/
def baseι (n : ℕ) : line k ⟶ base k := StarGlue.ι (fun _ : ℕ ↦ line k) (fun _ ↦ puncturedLineι k) n

/-- Each chart of the line with infinitely many origins is an open immersion. -/
instance (n : ℕ) : IsOpenImmersion (baseι k n) :=
  StarGlue.isOpenImmersion_ι (fun _ : ℕ ↦ line k) (fun _ ↦ puncturedLineι k) n

/-- Every point of the line with infinitely many origins lies in the image of some chart. -/
theorem baseι_jointly_surjective (x : base k) : ∃ (n : ℕ) (y : line k), baseι k n y = x :=
  StarGlue.ι_jointly_surjective _ _ x

/-- Any two charts of the line with infinitely many origins agree on the punctured line. -/
@[reassoc]
theorem puncturedLineι_baseι (m n : ℕ) :
    puncturedLineι k ≫ baseι k m = puncturedLineι k ≫ baseι k n :=
  StarGlue.glue_condition _ _ m n

/-- The `n`-th chart of the line with infinitely many origins, as an affine open. -/
abbrev baseChart (n : ℕ) : (base k).Opens := (baseι k n) ''ᵁ ⊤

/-- Each chart of the line with infinitely many origins is an affine open subscheme. -/
theorem isAffineOpen_baseChart (n : ℕ) : IsAffineOpen (baseChart k n) :=
  (isAffineOpen_top (line k)).image_of_isOpenImmersion (baseι k n)

/-- The image under `baseι k n` of a point of the affine line lies in `baseChart k n`. -/
theorem mem_baseChart (n : ℕ) (y : line k) : baseι k n y ∈ baseChart k n :=
  ⟨y, trivial, rfl⟩

/-- The sections of the line with infinitely many origins over a chart are the polynomials. -/
def baseChartIso (n : ℕ) : Γ(base k, baseChart k n) ≅ CommRingCat.of k[X] :=
  (baseι k n).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

/-- The ring of sections over each chart is regular. -/
theorem isRegularRing_baseChart (n : ℕ) : IsRegularRing Γ(base k, baseChart k n) :=
  IsRegularRing.of_ringEquiv (baseChartIso k n).symm.commRingCatIsoToRingEquiv

/-- The ring of sections over each chart is Nagata. -/
theorem isNagataRing_baseChart (n : ℕ) : IsNagataRing Γ(base k, baseChart k n) :=
  MonogenicN1.isNagataRing_of_ringEquiv (baseChartIso k n).symm.commRingCatIsoToRingEquiv
    (IsNagataRing.of_finiteType (A := k) IsNagataRing.of_field)

/-- A ring property holding on the ring of sections over every chart holds on an affine open
neighbourhood of every point of the line with infinitely many origins. -/
private theorem exists_affineOpen_of_baseChart (P : CommRingCat.{u} → Prop)
    (h : ∀ n, P Γ(base k, baseChart k n)) (x : base k) :
    ∃ U : (base k).affineOpens, x ∈ U.val ∧ P Γ(base k, U.val) := by
  obtain ⟨n, y, rfl⟩ := baseι_jointly_surjective k x
  exact ⟨⟨baseChart k n, isAffineOpen_baseChart k n⟩, mem_baseChart k n y, h n⟩

/-- **The line with infinitely many origins is regular.** -/
theorem isRegular_base : IsRegular (base k) :=
  exists_affineOpen_of_baseChart k (fun R ↦ IsRegularRing R) (isRegularRing_baseChart k)

/-- **The line with infinitely many origins is Nagata.** -/
theorem isNagataScheme_base : IsNagataScheme (base k) :=
  exists_affineOpen_of_baseChart k (fun R ↦ IsNagataRing R) (isNagataRing_baseChart k)

/-- The image of the punctured line in the affine line is the basic open set `D(t)`. -/
theorem opensRange_puncturedLineι :
    (puncturedLineι k).opensRange = PrimeSpectrum.basicOpen (X : k[X]) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of k[X]) X

/-- The generic point of the affine line. -/
def lineGenericPoint : line k := ⟨⊥, Ideal.isPrime_bot⟩

/-- Every point of the affine line is a specialization of its generic point. -/
theorem lineGenericPoint_specializes (y : line k) : lineGenericPoint k ⤳ y :=
  (PrimeSpectrum.le_iff_specializes _ _).mp bot_le

/-- The generic point of the affine line lies in the image of the punctured line. -/
theorem lineGenericPoint_mem_range :
    lineGenericPoint k ∈ Set.range (puncturedLineι k) := by
  have hmem : lineGenericPoint k ∈ (puncturedLineι k).opensRange := by
    rw [opensRange_puncturedLineι]
    change X ∉ (⊥ : Ideal k[X])
    simp
  exact hmem

/-- Every point of the line with infinitely many origins is a specialization of the image of the
generic point of the zeroth chart. -/
theorem specializes_base (x : base k) : baseι k 0 (lineGenericPoint k) ⤳ x := by
  obtain ⟨n, y, rfl⟩ := baseι_jointly_surjective k x
  obtain ⟨w, hw⟩ := lineGenericPoint_mem_range k
  have h : baseι k 0 (lineGenericPoint k) = baseι k n (lineGenericPoint k) := by
    rw [← hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, puncturedLineι_baseι k 0 n]
  rw [h]
  exact (lineGenericPoint_specializes k y).map (baseι k n).continuous

/-- The line with infinitely many origins is irreducible. -/
instance : IrreducibleSpace (base k) := by
  rw [irreducibleSpace_def]
  have : closure {baseι k 0 (lineGenericPoint k)} = (⊤ : Set (base k)) := by
    refine Set.eq_univ_of_forall fun x ↦ ?_
    exact specializes_iff_mem_closure.mp (specializes_base k x)
  rw [← this]
  exact isIrreducible_singleton.closure

/-- The line with infinitely many origins is reduced. -/
instance : IsReduced (base k) := by
  have h : ∀ a : WidePushoutShape ℕ, IsReduced
      ((StarGlue.diagram (fun _ : ℕ ↦ line k) (fun _ ↦ puncturedLineι k)).obj a) := by
    intro a
    cases a
    · exact inferInstanceAs (IsReduced (puncturedLine k))
    · exact inferInstanceAs (IsReduced (line k))
  exact @IsReduced.of_openCover _
    (StarGlue.openCover (fun _ : ℕ ↦ line k) (fun _ ↦ puncturedLineι k)) h

/-- **The line with infinitely many origins is integral.** -/
instance isIntegral_base : IsIntegral (base k) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- The affine line has dimension one. -/
theorem topologicalKrullDim_line : topologicalKrullDim (line k) = 1 := by
  change topologicalKrullDim (PrimeSpectrum k[X]) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField k)

/-- **The line with infinitely many origins has dimension one.** -/
theorem topologicalKrullDim_base : topologicalKrullDim (base k) = 1 := by
  apply le_antisymm
  · rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun x ↦ ?_
    obtain ⟨n, y, rfl⟩ := baseι_jointly_surjective k x
    have h1 : TopologicalSpace.localKrullDim (base k) (baseι k n y) ≤
        topologicalKrullDim (Set.range (baseι k n)) := by
      unfold TopologicalSpace.localKrullDim
      exact iInf_le_of_le (Set.range (baseι k n))
        (iInf_le_of_le (baseι k n).isOpenEmbedding.isOpen_range
          (iInf_le (fun _ ↦ topologicalKrullDim (Set.range (baseι k n))) ⟨y, rfl⟩))
    refine h1.trans (le_of_eq ?_)
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (baseι k n).isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph,
      topologicalKrullDim_line]
  · rw [← topologicalKrullDim_line k]
    exact (baseι k 0).isOpenEmbedding.isInducing.topologicalKrullDim_le

end AlgebraicGeometry.ReducedFibreCurveCounterexample
