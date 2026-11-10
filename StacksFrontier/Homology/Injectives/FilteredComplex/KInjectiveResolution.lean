module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Factorizations.CM5b
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Defs
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# K-injective resolutions of filtered complexes

Every filtered complex in a Grothendieck abelian category admits a filtered
quasi-isomorphism to a filtered complex whose terms, filtration steps, and
filtration quotients are injective, and whose corresponding complexes are
K-injective.

The construction starts from a functorial K-injective resolution
`Stacks.Injectives.functorialKInjectiveResolution`, applied to the underlying
complex and to every filtration step at once. Functoriality alone does not make
the resolutions of the steps into *subcomplexes* of the resolution of the whole,
so each step is corrected by a contractible complex of injectives: a step is
represented by the graph of a map into an acyclic envelope, and the single
ambient complex is enlarged by the product of all these envelopes. Since the
envelopes are contractible, enlarging by them changes neither K-injectivity nor
the quasi-isomorphism class, while the graphs give honest termwise monomorphisms
that are compatible with the transition maps of the filtration. The quotients
are then handled by the degreewise split short exact sequences they sit in.

## Main definitions

* `Stacks.Injectives.filtrationQuotientMap` is the map induced on the quotient by
  a filtration step.
* `Stacks.Injectives.filtrationSubquotientMap` is the map induced between two
  filtration steps modulo the smaller one.

## Main results

* `Stacks.Injectives.exists_filtered_quasiIso_isKInjective` constructs the
  required filtered K-injective resolution.

## Implementation notes

A filtered complex is represented as a `ℤᵒᵖ`-filtered object in cochain
complexes. Thus `F^p K` is `K.filtration.obj (op p)`, while the quotients in
the statement are categorical cokernels. The two auxiliary maps below record
the canonical induced maps on those cokernels. The four groups of clauses in
the conclusion respectively state termwise injectivity, K-injectivity, and
the four families of quasi-isomorphisms.

The Grothendieck universe is independent of the object and morphism universes,
as in the functorial K-injective resolution theorem used in the construction.

## References

* [Stacks Project, Tag 0BKI](https://stacks.math.columbia.edu/tag/0BKI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ZeroObject

universe w' v u

namespace Stacks.Injectives

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The canonical map `K/F^pK ⟶ J/F^pJ` induced by a morphism of filtered
complexes. -/
noncomputable def filtrationQuotientMap
    {K J : CochainComplex.Filtered A} (f : K ⟶ J) (p : ℤ) :
    cokernel (K.filtration.ι.app (op p)) ⟶
      cokernel (J.filtration.ι.app (op p)) :=
  cokernel.map _ _ (f.natTrans.app (op p)) f.hom (f.comm (op p)).symm

/-- The quotient map of a filtered complex is natural: composing with the
projection onto `K/F^pK` agrees with the map on the underlying complexes. -/
@[reassoc]
lemma cokernel_π_filtrationQuotientMap
    {K J : CochainComplex.Filtered A} (f : K ⟶ J) (p : ℤ) :
    cokernel.π (K.filtration.ι.app (op p)) ≫ filtrationQuotientMap f p =
      f.hom ≫ cokernel.π (J.filtration.ι.app (op p)) := by
  simp [filtrationQuotientMap]

/-- The canonical map `F^pK/F^{p'}K ⟶ F^pJ/F^{p'}J`, for `p ≤ p'`,
induced by a morphism of filtered complexes. -/
noncomputable def filtrationSubquotientMap
    {K J : CochainComplex.Filtered A} (f : K ⟶ J) {p p' : ℤ} (h : p ≤ p') :
    cokernel (K.filtration.diagram.map (opHomOfLE h)) ⟶
      cokernel (J.filtration.diagram.map (opHomOfLE h)) :=
  cokernel.map _ _ (f.natTrans.app (op p')) (f.natTrans.app (op p))
    (f.natTrans.naturality (opHomOfLE h))

/-- The subquotient map of a filtered complex is natural: composing with the
projection onto `F^pK/F^{p'}K` agrees with the map on the `p`-th steps. -/
@[reassoc]
lemma cokernel_π_filtrationSubquotientMap
    {K J : CochainComplex.Filtered A} (f : K ⟶ J) {p p' : ℤ} (h : p ≤ p') :
    cokernel.π (K.filtration.diagram.map (opHomOfLE h)) ≫
        filtrationSubquotientMap f h =
      f.natTrans.app (op p) ≫
        cokernel.π (J.filtration.diagram.map (opHomOfLE h)) := by
  apply cokernel.π_desc

/-- Extend a map from a subcomplex to an injective complex when it agrees up to
homotopy with a map defined on the ambient complex. -/
private lemma extendHomotopicMap {K L I : CochainComplex A ℤ}
    [∀ n, Injective (I.X n)] {α : K ⟶ L} [∀ n, Mono (α.f n)]
    {β₀ : L ⟶ I} {γ : K ⟶ I} (h : Homotopy (α ≫ β₀) γ) :
    ∃ β : L ⟶ I, α ≫ β = γ := by
  refine ⟨β₀ - Homotopy.nullHomotopicMap (fun i j =>
    Injective.factorThru (h.hom i j) (α.f i)), ?_⟩
  rw [Preadditive.comp_sub, Homotopy.comp_nullHomotopicMap,
    funext₂ fun i j => Injective.comp_factorThru (h.hom i j) (α.f i),
    ← h.sub_eq_nullHomotopicMap, sub_sub_cancel]

/-- A contractible complex is K-injective, since every map into it is
null-homotopic. -/
private lemma isKInjective_of_contractible (I : CochainComplex A ℤ)
    (h : Homotopy (𝟙 I) 0) : I.IsKInjective := by
  refine ⟨fun {K} f _ => ⟨?_⟩⟩
  simpa using (h.compLeft f).trans (Homotopy.ofEq (by simp))

/-- Any complex embeds termwise into a contractible complex of injectives.
This is the acyclic envelope used for each filtration step. -/
private lemma exists_contractible_injective_envelope [HasZeroObject A] [EnoughInjectives A]
    (K : CochainComplex A ℤ) :
    ∃ (E : CochainComplex A ℤ) (t : K ⟶ E),
      (∀ n, Mono (t.f n)) ∧ (∀ n, Injective (E.X n)) ∧
      Nonempty (Homotopy (𝟙 E) 0) ∧ E.IsKInjective := by
  let B := CochainComplex.mappingCone (𝟙 (CochainComplex.cm5b.I K))
  let t : K ⟶ B := CochainComplex.cm5b.i (0 : K ⟶ (0 : CochainComplex A ℤ)) ≫
    (biprod.fst : B ⊞ (0 : CochainComplex A ℤ) ⟶ B)
  have ht : ∀ n, Mono (t.f n) := by
    intro n
    have hm : Mono
        ((CochainComplex.cm5b.i (0 : K ⟶ (0 : CochainComplex A ℤ))).f n ≫
          (biprod.fst : B ⊞ (0 : CochainComplex A ℤ) ⟶ B).f n) := by
      have hmono : Mono
          (((CochainComplex.cm5b.i (0 : K ⟶ (0 : CochainComplex A ℤ))).f n ≫
            (biprod.fst : B ⊞ (0 : CochainComplex A ℤ) ⟶ B).f n) ≫
            (CochainComplex.mappingCone.snd
              (𝟙 (CochainComplex.cm5b.I K))).v n n (add_zero n)) := by
        rw [Category.assoc, CochainComplex.cm5b.i_f_comp]
        exact Injective.ι_mono _
      exact @mono_of_mono_fac A _ _ _ _ _ _ _ hmono rfl
    simpa only [t, HomologicalComplex.comp_f] using hm
  have h : Homotopy (𝟙 B) 0 := CochainComplex.mappingCone.homotopyToZeroOfId _
  exact ⟨B, t, ht, (fun _ => inferInstance), ⟨h⟩,
    isKInjective_of_contractible B h⟩

/-- Products of contractible complexes are contractible. This is the product
argument for the acyclic correction factors. -/
private lemma product_contractible {T : Type} (E : T → CochainComplex A ℤ)
    [∀ n : ℤ, HasProduct fun t => (E t).X n] [HasProduct E]
    (hE : ∀ t, Nonempty (Homotopy (𝟙 (E t)) 0)) :
    Nonempty (Homotopy (𝟙 (∏ᶜ E : CochainComplex A ℤ)) 0) := by
  apply Stacks.Injectives.KInjectiveProduct.product_homotopyZero_of_componentwise E (𝟙 _)
  intro t
  simpa using (hE t).some.compLeft (Pi.π E t)

/-- Termwise injectivity survives products of complexes. -/
private lemma product_terms_injective {T : Type} (E : T → CochainComplex A ℤ)
    [∀ n : ℤ, HasProduct fun t => (E t).X n] [HasProduct E]
    (hE : ∀ t n, Injective ((E t).X n)) :
    ∀ n, Injective ((∏ᶜ E : CochainComplex A ℤ).X n) := by
  intro n
  let (t : T) : Injective ((E t).X n) := hE t n
  exact Injective.of_iso (Stacks.Injectives.KInjectiveProduct.productComplex_degreewise E
    n).some.symm inferInstance

/-- Adding a contractible summand does not change a complex up to homotopy. -/
private noncomputable def biprodHomotopyEquivOfContractible
    (I E : CochainComplex A ℤ) (hE : Homotopy (𝟙 E) 0) :
    HomotopyEquiv (I ⊞ E) I where
  hom := biprod.fst
  inv := biprod.inl
  homotopyHomInvId := by
    have h : Homotopy
        ((biprod.snd : I ⊞ E ⟶ E) ≫ (biprod.inr : E ⟶ I ⊞ E)) 0 := by
      simpa using (hE.compLeft (biprod.snd : I ⊞ E ⟶ E)).compRight
        (biprod.inr : E ⟶ I ⊞ E)
    have h' := Homotopy.add
      (Homotopy.refl ((biprod.fst : I ⊞ E ⟶ I) ≫
        (biprod.inl : I ⟶ I ⊞ E))) h
    rw [add_zero, biprod.total] at h'
    exact h'.symm
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- Enlarging a K-injective complex by a contractible summand keeps it
K-injective. -/
private lemma biprod_isKInjective_of_contractible (I E : CochainComplex A ℤ)
    [I.IsKInjective] (hE : Homotopy (𝟙 E) 0) :
    (I ⊞ E).IsKInjective :=
  (biprodHomotopyEquivOfContractible I E hE).symm.isKInjective

/-- A graph map is degreewise monic when its second coordinate is. -/
private lemma mono_f_biprod_lift_of_second
    {P I E : CochainComplex A ℤ} (a : P ⟶ I) (t : P ⟶ E)
    (ht : ∀ n, Mono (t.f n)) :
    ∀ n, Mono ((biprod.lift a t).f n) := by
  intro n
  let : Mono (t.f n) := ht n
  apply mono_of_mono_fac (h := t.f n)
  rw [← HomologicalComplex.comp_f, biprod.lift_snd]

/-- A map into a complex plus a contractible summand is a quasi-isomorphism
as soon as its first coordinate is. -/
private lemma quasiIso_biprod_lift_of_contractible
    {K I E : CochainComplex A ℤ} (i : K ⟶ I) (s : K ⟶ E)
    [QuasiIso i] (hE : Homotopy (𝟙 E) 0) :
    QuasiIso (biprod.lift i s) := by
  let : QuasiIso (biprod.fst : I ⊞ E ⟶ I) :=
    (biprodHomotopyEquivOfContractible I E hE).quasiIso_hom
  have : QuasiIso ((biprod.lift i s) ≫ (biprod.fst : I ⊞ E ⟶ I)) := by
    simpa using (inferInstance : QuasiIso i)
  exact quasiIso_of_comp_right
    (biprod.lift i s) (biprod.fst : I ⊞ E ⟶ I)

/-- The correction map into a contractible envelope agrees with the chosen
resolution of a filtration step on the original subcomplex. -/
private lemma exists_step_correction [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ)
    (E : CochainComplex A ℤ)
    (t : R.functor.obj (K.filtration.obj (op p)) ⟶ E)
    [∀ n, Injective (E.X n)] (hE : Homotopy (𝟙 E) 0) :
    ∃ s : R.functor.obj K.X ⟶ E,
      (K.filtration.ι.app (op p) ≫ R.inclusion.app K.X) ≫ s =
        R.inclusion.app (K.filtration.obj (op p)) ≫ t := by
  let α := K.filtration.ι.app (op p) ≫ R.inclusion.app K.X
  let γ := R.inclusion.app (K.filtration.obj (op p)) ≫ t
  have hm : ∀ n, Mono (α.f n) := by
    intro n
    dsimp [α]
    let : Mono ((R.inclusion.app K.X).f n) := R.mono_f K.X n
    exact mono_comp _ _
  let (n : ℤ) : Mono (α.f n) := hm n
  have h : Homotopy (α ≫ (0 : R.functor.obj K.X ⟶ E)) γ := by
    simpa only [Category.comp_id, comp_zero] using (hE.compLeft γ).symm
  exact extendHomotopicMap h

/-- One filtration step can be represented by a monic graph inside a
K-injective resolution enlarged by an acyclic correction factor. -/
private lemma exists_one_step_graph [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    ∃ (E : CochainComplex A ℤ)
      (t : R.functor.obj (K.filtration.obj (op p)) ⟶ E)
      (s : R.functor.obj K.X ⟶ E),
      (∀ n, Mono (t.f n)) ∧ (∀ n, Injective (E.X n)) ∧
      Nonempty (Homotopy (𝟙 E) 0) ∧
      (K.filtration.ι.app (op p) ≫ R.inclusion.app K.X) ≫ s =
        R.inclusion.app (K.filtration.obj (op p)) ≫ t ∧
      K.filtration.ι.app (op p) ≫
          biprod.lift (R.inclusion.app K.X) (R.inclusion.app K.X ≫ s) =
        R.inclusion.app (K.filtration.obj (op p)) ≫
          biprod.lift (R.functor.map (K.filtration.ι.app (op p))) t ∧
      QuasiIso (biprod.lift (R.inclusion.app K.X)
        (R.inclusion.app K.X ≫ s)) ∧
      (∀ n, Mono ((biprod.lift
        (R.functor.map (K.filtration.ι.app (op p))) t).f n)) := by
  obtain ⟨E, t, ht, hEinj, ⟨hcontr⟩, _⟩ :=
    exists_contractible_injective_envelope
      (R.functor.obj (K.filtration.obj (op p)))
  let (n : ℤ) : Injective (E.X n) := hEinj n
  obtain ⟨s, hs⟩ := exists_step_correction K R p E t hcontr
  refine ⟨E, t, s, ht, hEinj, ⟨hcontr⟩, hs, ?_, ?_,
    mono_f_biprod_lift_of_second _ _ ht⟩
  · have hn := R.inclusion.naturality (K.filtration.ι.app (op p))
    apply biprod.hom_ext
    · simpa [Functor.const] using hn
    · simpa [Category.assoc] using hs
  · let : QuasiIso (R.inclusion.app K.X) := R.quasiIso K.X
    exact quasiIso_biprod_lift_of_contractible _ _ hcontr

/-- The data extracted from `exists_one_step_graph`: the acyclic envelope of the
`p`-th filtration step together with the two maps into it and the properties
needed to assemble the resolved filtration. -/
private structure StepData [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) where
  /-- The contractible envelope of the resolution of the `p`-th step. -/
  E : CochainComplex A ℤ
  /-- The termwise monic map from the resolution of the `p`-th step. -/
  t : R.functor.obj (K.filtration.obj (op p)) ⟶ E
  /-- The correction map from the resolution of the whole complex. -/
  s : R.functor.obj K.X ⟶ E
  mono_t : ∀ n, Mono (t.f n)
  injective_E : ∀ n, Injective (E.X n)
  contractible_E : Nonempty (Homotopy (𝟙 E) 0)
  correction : (K.filtration.ι.app (op p) ≫ R.inclusion.app K.X) ≫ s =
    R.inclusion.app (K.filtration.obj (op p)) ≫ t
  comm : K.filtration.ι.app (op p) ≫
      biprod.lift (R.inclusion.app K.X) (R.inclusion.app K.X ≫ s) =
    R.inclusion.app (K.filtration.obj (op p)) ≫
      biprod.lift (R.functor.map (K.filtration.ι.app (op p))) t
  quasiIso_graph : QuasiIso
    (biprod.lift (R.inclusion.app K.X) (R.inclusion.app K.X ≫ s))
  mono_graph : ∀ n, Mono ((biprod.lift
    (R.functor.map (K.filtration.ι.app (op p))) t).f n)

/-- A choice of step data for every index `p`. -/
private noncomputable def stepData [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    StepData K R p := Classical.choice (by
  obtain ⟨E, t, s, ht, hE, hc, hcorrection, hcomm, hq, hm⟩ :=
    exists_one_step_graph K R p
  exact ⟨⟨E, t, s, ht, hE, hc, hcorrection, hcomm, hq, hm⟩⟩)

/-- The product of all the acyclic envelopes, one for each filtration index. -/
private noncomputable abbrev correctionProduct [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) : CochainComplex A ℤ :=
  ∏ᶜ fun p : ℤ => (stepData K R p).E

/-- The complex underlying the filtered resolution: the K-injective resolution of
`K.X` enlarged by the product of all acyclic envelopes. -/
private noncomputable abbrev ambient [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) : CochainComplex A ℤ :=
  R.functor.obj K.X ⊞ correctionProduct K R

/-- The comparison map from `K.X` into the ambient complex. -/
private noncomputable def ambientMap [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    K.X ⟶ ambient K R :=
  biprod.lift (R.inclusion.app K.X)
    (R.inclusion.app K.X ≫ Pi.lift (fun p => (stepData K R p).s))

/-- The product of the acyclic envelopes is contractible. -/
private lemma correctionProduct_contractible [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    Nonempty (Homotopy (𝟙 (correctionProduct K R)) 0) :=
  product_contractible (fun p : ℤ => (stepData K R p).E)
    (fun p => (stepData K R p).contractible_E)

/-- The product of the acyclic envelopes has injective terms. -/
private lemma correctionProduct_terms_injective [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    ∀ n, Injective ((correctionProduct K R).X n) :=
  product_terms_injective (fun p : ℤ => (stepData K R p).E)
    (fun p n => (stepData K R p).injective_E n)

/-- The ambient complex is K-injective. -/
private lemma ambient_isKInjective [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    (ambient K R).IsKInjective := by
  let : (R.functor.obj K.X).IsKInjective := R.isKInjective K.X
  exact biprod_isKInjective_of_contractible _ _
    (correctionProduct_contractible K R).some

/-- The comparison map into the ambient complex is a quasi-isomorphism. -/
private lemma ambientMap_quasiIso [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    QuasiIso (ambientMap K R) := by
  let : QuasiIso (R.inclusion.app K.X) := R.quasiIso K.X
  exact quasiIso_biprod_lift_of_contractible _ _
    (correctionProduct_contractible K R).some

/-- A biproduct of complexes with injective terms has injective terms. -/
private lemma biprod_terms_injective (I E : CochainComplex A ℤ)
    (hI : ∀ n, Injective (I.X n)) (hE : ∀ n, Injective (E.X n)) :
    ∀ n, Injective ((I ⊞ E).X n) := by
  intro n
  let : Injective (I.X n) := hI n
  let : Injective (E.X n) := hE n
  exact Injective.of_iso (HomologicalComplex.biprodXIso I E n).symm inferInstance

/-- The ambient complex has injective terms. -/
private lemma ambient_terms_injective [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    ∀ n, Injective ((ambient K R).X n) :=
  biprod_terms_injective _ _ (R.injective K.X) (correctionProduct_terms_injective K R)

/-- The product of the acyclic envelopes at indices strictly above `p`. -/
private noncomputable abbrev correctionTail [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    CochainComplex A ℤ :=
  ∏ᶜ fun q : {q : ℤ // p < q} => (stepData K R q.1).E

/-- The second coordinate of the `p`-th graph: into the envelope at index `q` it
is the composite through the transition map when `q ≤ p`, and the projection
from the tail otherwise. -/
private noncomputable def stepCorrectionMap [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    R.functor.obj (K.filtration.obj (op p)) ⊞ correctionTail K R p ⟶
      correctionProduct K R := by
  classical
  exact Pi.lift (fun q : ℤ =>
    if h : q ≤ p then
      (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p))) ≫
        R.functor.map (K.filtration.diagram.map (opHomOfLE h)) ≫
          (stepData K R q).t
    else
      (biprod.snd : _ ⟶ correctionTail K R p) ≫
        Pi.π (fun r : {r : ℤ // p < r} => (stepData K R r.1).E)
          ⟨q, lt_of_not_ge h⟩)

/-- The `p`-th step of the resolved filtration, as a map into the ambient
complex. -/
private noncomputable def stepGraph [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    R.functor.obj (K.filtration.obj (op p)) ⊞ correctionTail K R p ⟶
      ambient K R :=
  biprod.lift
    ((biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p))) ≫
      R.functor.map (K.filtration.ι.app (op p)))
    (stepCorrectionMap K R p)

/-- The `p`-th component of the `p`-th correction map is the chosen map `t`. -/
private lemma stepCorrectionMap_π_self [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    stepCorrectionMap K R p ≫
        Pi.π (fun q : ℤ => (stepData K R q).E) p =
      (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p))) ≫
        (stepData K R p).t := by
  classical
  unfold stepCorrectionMap correctionTail correctionProduct
  rw [Pi.lift_comp_π]
  simp only [dite_eq_left le_rfl]
  have h : (opHomOfLE (le_refl p) : op p ⟶ op p) = 𝟙 _ := Subsingleton.elim _ _
  simp [h]

/-- The `q`-th component of the `p`-th correction map for `q ≤ p`. -/
private lemma stepCorrectionMap_π_le [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p q : ℤ} (h : q ≤ p) :
    stepCorrectionMap K R p ≫
        Pi.π (fun r : ℤ => (stepData K R r).E) q =
      (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p))) ≫
        R.functor.map (K.filtration.diagram.map (opHomOfLE h)) ≫
          (stepData K R q).t := by
  classical
  unfold stepCorrectionMap correctionTail correctionProduct
  rw [Pi.lift_comp_π]
  simp only [dite_eq_left h]

/-- The `q`-th component of the `p`-th correction map for `p < q`. -/
private lemma stepCorrectionMap_π_gt [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p q : ℤ} (h : p < q) :
    stepCorrectionMap K R p ≫
        Pi.π (fun r : ℤ => (stepData K R r).E) q =
      (biprod.snd : _ ⟶ correctionTail K R p) ≫
        Pi.π (fun r : {r : ℤ // p < r} => (stepData K R r.1).E) ⟨q, h⟩ := by
  classical
  unfold stepCorrectionMap correctionTail correctionProduct
  rw [Pi.lift_comp_π]
  simp [not_le.mpr h]

/-- Evaluating the tail product in a fixed degree is again a product. -/
private noncomputable def correctionTailEvalIsLimit [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p n : ℤ) :
    IsLimit (Fan.mk ((correctionTail K R p).X n)
      (fun q : {q : ℤ // p < q} =>
        (Pi.π (fun r : {r : ℤ // p < r} => (stepData K R r.1).E) q).f n)) := by
  unfold correctionTail
  exact Stacks.Injectives.KInjectiveProduct.productEvalIsLimit
    (fun r : {r : ℤ // p < r} => (stepData K R r.1).E) n

/-- The `p`-th correction map is degreewise monic. -/
private lemma stepCorrectionMap_mono_f [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    ∀ n, Mono ((stepCorrectionMap K R p).f n) := by
  intro n
  let S := R.functor.obj (K.filtration.obj (op p))
  let : Mono (((stepData K R p).t).f n) := (stepData K R p).mono_t n
  have hself : (stepCorrectionMap K R p).f n ≫
      (Pi.π (fun q : ℤ => (stepData K R q).E) p).f n =
      (biprod.fst : S ⊞ correctionTail K R p ⟶ S).f n ≫
        ((stepData K R p).t).f n := by
    rw [← HomologicalComplex.comp_f]
    exact congrArg (fun f => f.f n) (stepCorrectionMap_π_self K R p)
  have htail (q : {q : ℤ // p < q}) :
      (stepCorrectionMap K R p).f n ≫
        (Pi.π (fun r : ℤ => (stepData K R r).E) q.1).f n =
        (biprod.snd : S ⊞ correctionTail K R p ⟶ correctionTail K R p).f n ≫
          (Pi.π (fun r : {r : ℤ // p < r} => (stepData K R r.1).E) q).f n := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    exact congrArg (fun f => f.f n) (stepCorrectionMap_π_gt K R q.2)
  constructor
  intro X f g hfg
  apply HomologicalComplex.biprodX_ext_to
  · have h := hfg =≫ (Pi.π (fun q : ℤ => (stepData K R q).E) p).f n
    simp only [Category.assoc, hself] at h
    exact (cancel_mono ((stepData K R p).t.f n)).1
      (by simpa only [Category.assoc] using h)
  · apply (correctionTailEvalIsLimit K R p n).hom_ext
    rintro ⟨q⟩
    have h := hfg =≫ (Pi.π (fun r : ℤ => (stepData K R r).E) q.1).f n
    simp only [Category.assoc, htail q] at h
    change (f ≫ (biprod.snd : S ⊞ correctionTail K R p ⟶
        correctionTail K R p).f n) ≫
        (Pi.π (fun r : {r : ℤ // p < r} => (stepData K R r.1).E) q).f n =
      (g ≫ (biprod.snd : S ⊞ correctionTail K R p ⟶
        correctionTail K R p).f n) ≫
        (Pi.π (fun r : {r : ℤ // p < r} => (stepData K R r.1).E) q).f n
    simpa only [Category.assoc] using h

/-- The `p`-th step of the resolved filtration is degreewise monic. -/
private lemma stepGraph_mono_f [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    ∀ n, Mono ((stepGraph K R p).f n) :=
  mono_f_biprod_lift_of_second _ _ (stepCorrectionMap_mono_f K R p)

/-- The tail product of acyclic envelopes is contractible. -/
private lemma correctionTail_contractible [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    Nonempty (Homotopy (𝟙 (correctionTail K R p)) 0) :=
  product_contractible
    (fun q : {q : ℤ // p < q} => (stepData K R q.1).E)
    (fun q => (stepData K R q.1).contractible_E)

/-- The tail product of acyclic envelopes has injective terms. -/
private lemma correctionTail_terms_injective [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    ∀ n, Injective ((correctionTail K R p).X n) :=
  product_terms_injective
    (fun q : {q : ℤ // p < q} => (stepData K R q.1).E)
    (fun q n => (stepData K R q.1).injective_E n)

/-- The source of the `p`-th step of the resolved filtration is K-injective. -/
private lemma stepGraph_source_isKInjective [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    (R.functor.obj (K.filtration.obj (op p)) ⊞
      correctionTail K R p).IsKInjective := by
  let : (R.functor.obj (K.filtration.obj (op p))).IsKInjective :=
    R.isKInjective _
  exact biprod_isKInjective_of_contractible _ _
    (correctionTail_contractible K R p).some

/-- The source of the `p`-th step of the resolved filtration has injective
terms. -/
private lemma stepGraph_source_terms_injective [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    ∀ n, Injective
      ((R.functor.obj (K.filtration.obj (op p)) ⊞
        correctionTail K R p).X n) :=
  biprod_terms_injective _ _ (R.injective _) (correctionTail_terms_injective K R p)

/-- The transition map of the resolved filtration from index `p'` down to
`p ≤ p'`. -/
private noncomputable def stepGraphTransition [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p p' : ℤ} (h : p ≤ p') :
    R.functor.obj (K.filtration.obj (op p')) ⊞ correctionTail K R p' ⟶
      R.functor.obj (K.filtration.obj (op p)) ⊞ correctionTail K R p :=
  biprod.lift
    ((biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p'))) ≫
      R.functor.map (K.filtration.diagram.map (opHomOfLE h)))
    (Pi.lift (fun q : {q : ℤ // p < q} =>
      stepGraph K R p' ≫
        (biprod.snd : ambient K R ⟶ correctionProduct K R) ≫
          Pi.π (fun r : ℤ => (stepData K R r).E) q.1))

/-- The first coordinate of the `p`-th step of the resolved filtration. -/
private lemma stepGraph_fst [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    stepGraph K R p ≫
        (biprod.fst : ambient K R ⟶ R.functor.obj K.X) =
      (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p))) ≫
        R.functor.map (K.filtration.ι.app (op p)) :=
  biprod.lift_fst _ _

/-- The second coordinate of the `p`-th step of the resolved filtration. -/
private lemma stepGraph_snd [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    stepGraph K R p ≫
        (biprod.snd : ambient K R ⟶ correctionProduct K R) =
      stepCorrectionMap K R p :=
  biprod.lift_snd _ _

/-- The first coordinate of a transition map of the resolved filtration. -/
private lemma stepGraphTransition_fst [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p p' : ℤ} (h : p ≤ p') :
    stepGraphTransition K R h ≫
        (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p))) =
      (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p'))) ≫
        R.functor.map (K.filtration.diagram.map (opHomOfLE h)) :=
  biprod.lift_fst _ _

/-- The tail components of a transition map of the resolved filtration. -/
private lemma stepGraphTransition_tail_π [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p p' : ℤ} (h : p ≤ p') (q : {q : ℤ // p < q}) :
    stepGraphTransition K R h ≫
        (biprod.snd : _ ⟶ correctionTail K R p) ≫
          Pi.π (fun r : {r : ℤ // p < r} => (stepData K R r.1).E) q =
      stepGraph K R p' ≫
        (biprod.snd : ambient K R ⟶ correctionProduct K R) ≫
          Pi.π (fun r : ℤ => (stepData K R r).E) q.1 := by
  rw [← Category.assoc]
  unfold stepGraphTransition
  rw [biprod.lift_snd, Pi.lift_comp_π]

/-- The transition maps are compatible with the inclusions into the ambient
complex, so the steps really do form a filtration. -/
private lemma stepGraphTransition_comp_stepGraph [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p p' : ℤ} (h : p ≤ p') :
    stepGraphTransition K R h ≫ stepGraph K R p = stepGraph K R p' := by
  apply biprod.hom_ext
  · rw [Category.assoc, stepGraph_fst, ← Category.assoc,
      stepGraphTransition_fst, Category.assoc, ← R.functor.map_comp,
      K.filtration.diagram_map_comp_ι_app]
    exact (stepGraph_fst K R p').symm
  · apply Pi.hom_ext
    intro q
    by_cases hq : q ≤ p
    · have hq' : q ≤ p' := hq.trans h
      rw [Category.assoc (stepGraphTransition K R h) (stepGraph K R p)
        (biprod.snd : ambient K R ⟶ correctionProduct K R),
        stepGraph_snd,
        Category.assoc (stepGraphTransition K R h) (stepCorrectionMap K R p)
        (Pi.π (fun r : ℤ => (stepData K R r).E) q),
        stepCorrectionMap_π_le K R hq,
        stepGraph_snd, stepCorrectionMap_π_le K R hq',
        ← Category.assoc (stepGraphTransition K R h)
        (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p)))
        (R.functor.map (K.filtration.diagram.map (opHomOfLE hq)) ≫
          (stepData K R q).t),
        stepGraphTransition_fst]
      have hh : (opHomOfLE h : op p' ⟶ op p) ≫
          (opHomOfLE hq : op p ⟶ op q) = opHomOfLE hq' :=
        Subsingleton.elim _ _
      have hm : R.functor.map (K.filtration.diagram.map (opHomOfLE h)) ≫
          R.functor.map (K.filtration.diagram.map (opHomOfLE hq)) =
        R.functor.map (K.filtration.diagram.map (opHomOfLE hq')) := by
        rw [← R.functor.map_comp, ← K.filtration.diagram.map_comp, hh]
      simpa only [Category.assoc] using
        congrArg (fun f =>
          (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p'))) ≫
            f ≫ (stepData K R q).t) hm
    · have hlt : p < q := lt_of_not_ge hq
      rw [Category.assoc (stepGraphTransition K R h) (stepGraph K R p)
        (biprod.snd : ambient K R ⟶ correctionProduct K R),
        stepGraph_snd,
        Category.assoc (stepGraphTransition K R h) (stepCorrectionMap K R p)
        (Pi.π (fun r : ℤ => (stepData K R r).E) q),
        stepCorrectionMap_π_gt K R hlt]
      simpa only [Category.assoc] using
        stepGraphTransition_tail_π K R h ⟨q, hlt⟩

/-- The `p`-th step of the resolved filtration is a monomorphism. -/
private lemma stepGraph_mono [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    Mono (stepGraph K R p) :=
  HomologicalComplex.mono_of_mono_f _ (stepGraph_mono_f K R p)

/-- The filtration on the ambient complex assembled from the step graphs. -/
private noncomputable def resolvedFiltration [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    Filtration (ambient K R) ℤᵒᵖ where
  toMonoOver :=
    { obj i := ⟨Over.mk (stepGraph K R i.unop), stepGraph_mono K R i.unop⟩
      map f := MonoOver.homMk
        (stepGraphTransition K R (leOfHom f.unop))
        (stepGraphTransition_comp_stepGraph K R (leOfHom f.unop))
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }

/-- The filtered complex resolving `K`. -/
private noncomputable def resolved [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    CochainComplex.Filtered A :=
  ⟨ambient K R, resolvedFiltration K R⟩

/-- The `p`-th step of the resolving filtered complex is the `p`-th step
graph. -/
private lemma resolved_filtration_ι [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    (resolved K R).filtration.ι.app (op p) = stepGraph K R p := by
  rfl

/-- The transition maps of the resolving filtered complex are the step
transitions. -/
private lemma resolved_filtration_step [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p p' : ℤ} (h : p ≤ p') :
    (resolved K R).filtration.diagram.map (opHomOfLE h) =
      stepGraphTransition K R h := by
  rfl

/-- The defining property of the correction map, in associated form. -/
private lemma stepData_correction [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (q : ℤ) :
    K.filtration.ι.app (op q) ≫ R.inclusion.app K.X ≫
        (stepData K R q).s =
      R.inclusion.app (K.filtration.obj (op q)) ≫
        (stepData K R q).t := by
  simpa only [Category.assoc] using (stepData K R q).correction

/-- The correction map at index `q` restricted to a larger filtration step
`F^p K` with `q ≤ p`. -/
private lemma stepData_correction_le [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p q : ℤ} (h : q ≤ p) :
    K.filtration.ι.app (op p) ≫ R.inclusion.app K.X ≫
        (stepData K R q).s =
      R.inclusion.app (K.filtration.obj (op p)) ≫
        R.functor.map (K.filtration.diagram.map (opHomOfLE h)) ≫
          (stepData K R q).t := by
  rw [← K.filtration.diagram_map_comp_ι_app (opHomOfLE h)]
  simp only [Category.assoc, stepData_correction K R q]
  have hn := R.inclusion.naturality (K.filtration.diagram.map (opHomOfLE h))
  simpa only [Functor.id_map, Functor.const_obj_obj, Category.assoc] using
    congrArg (fun f => f ≫ (stepData K R q).t) hn

/-- The comparison map from the `p`-th filtration step of `K` to the `p`-th step
of the resolved filtration. -/
private noncomputable def stepComparison [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    K.filtration.obj (op p) ⟶
      R.functor.obj (K.filtration.obj (op p)) ⊞ correctionTail K R p :=
  biprod.lift (R.inclusion.app (K.filtration.obj (op p)))
    (Pi.lift (fun q : {q : ℤ // p < q} =>
      K.filtration.ι.app (op p) ≫ ambientMap K R ≫
        (biprod.snd : ambient K R ⟶ correctionProduct K R) ≫
          Pi.π (fun r : ℤ => (stepData K R r).E) q.1))

/-- The `q`-th correction component of the ambient comparison map. -/
private lemma ambientMap_correction_π [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (q : ℤ) :
    ambientMap K R ≫
        (biprod.snd : ambient K R ⟶ correctionProduct K R) ≫
          Pi.π (fun r : ℤ => (stepData K R r).E) q =
      R.inclusion.app K.X ≫ (stepData K R q).s := by
  rw [← Category.assoc (ambientMap K R)
    (biprod.snd : ambient K R ⟶ correctionProduct K R)
    (Pi.π (fun r : ℤ => (stepData K R r).E) q)]
  unfold ambientMap
  rw [biprod.lift_snd, Category.assoc, Pi.lift_comp_π]

/-- The first coordinate of the step comparison map. -/
private lemma stepComparison_fst [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    stepComparison K R p ≫
        (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p))) =
      R.inclusion.app (K.filtration.obj (op p)) :=
  biprod.lift_fst _ _

/-- The tail components of the step comparison map. -/
private lemma stepComparison_tail_π [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A)
    {p q : ℤ} (h : p < q) :
    stepComparison K R p ≫
        (biprod.snd : _ ⟶ correctionTail K R p) ≫
          Pi.π (fun r : {r : ℤ // p < r} => (stepData K R r.1).E)
            ⟨q, h⟩ =
      K.filtration.ι.app (op p) ≫ ambientMap K R ≫
        (biprod.snd : ambient K R ⟶ correctionProduct K R) ≫
          Pi.π (fun r : ℤ => (stepData K R r).E) q := by
  rw [← Category.assoc]
  unfold stepComparison
  rw [biprod.lift_snd, Pi.lift_comp_π]

/-- The step comparison maps are compatible with the inclusions of the
filtration steps, so they assemble into a morphism of filtered complexes. -/
private lemma stepComparison_comp_stepGraph [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    stepComparison K R p ≫ stepGraph K R p =
      K.filtration.ι.app (op p) ≫ ambientMap K R := by
  apply biprod.hom_ext
  · rw [Category.assoc, stepGraph_fst, ← Category.assoc]
    have hn := R.inclusion.naturality (K.filtration.ι.app (op p))
    simpa only [stepComparison, ambientMap, biprod.lift_fst, Category.assoc,
      Functor.id_map, Functor.const_obj_obj] using hn.symm
  · apply Pi.hom_ext
    intro q
    rw [Category.assoc (stepComparison K R p) (stepGraph K R p)
      (biprod.snd : ambient K R ⟶ correctionProduct K R), stepGraph_snd]
    by_cases hq : q ≤ p
    · rw [Category.assoc (stepComparison K R p) (stepCorrectionMap K R p)
        (Pi.π (fun r : ℤ => (stepData K R r).E) q),
        stepCorrectionMap_π_le K R hq]
      have hr : (K.filtration.ι.app (op p) ≫ ambientMap K R) ≫
          (biprod.snd : ambient K R ⟶ correctionProduct K R) ≫
            Pi.π (fun r : ℤ => (stepData K R r).E) q =
        K.filtration.ι.app (op p) ≫ R.inclusion.app K.X ≫
          (stepData K R q).s := by
        simpa only [Category.assoc] using congrArg
          (fun f => K.filtration.ι.app (op p) ≫ f)
          (ambientMap_correction_π K R q)
      rw [Category.assoc (K.filtration.ι.app (op p) ≫ ambientMap K R)
        (biprod.snd : ambient K R ⟶ correctionProduct K R)
        (Pi.π (fun r : ℤ => (stepData K R r).E) q),
        hr, stepData_correction_le K R hq, ← Category.assoc (stepComparison K R p)
        (biprod.fst : _ ⟶ R.functor.obj (K.filtration.obj (op p)))
        (R.functor.map (K.filtration.diagram.map (opHomOfLE hq)) ≫
          (stepData K R q).t), stepComparison_fst]
    · have hlt : p < q := lt_of_not_ge hq
      rw [Category.assoc (stepComparison K R p) (stepCorrectionMap K R p)
        (Pi.π (fun r : ℤ => (stepData K R r).E) q),
        stepCorrectionMap_π_gt K R hlt]
      simpa only [Category.assoc] using stepComparison_tail_π K R hlt

/-- The filtered quasi-isomorphism from `K` to its filtered K-injective
resolution. -/
private noncomputable def resolvedMap [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    K ⟶ resolved K R :=
  FilteredObject.homMk (ambientMap K R)
    (fun i => stepComparison K R i.unop)
    (fun i => stepComparison_comp_stepGraph K R i.unop)

/-- The underlying map of the filtered resolution is the ambient comparison
map. -/
private lemma resolvedMap_hom [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) :
    (resolvedMap K R).hom = ambientMap K R := rfl

/-- The `p`-th component of the filtered resolution is the `p`-th step
comparison map. -/
private lemma resolvedMap_step [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    (resolvedMap K R).natTrans.app (op p) = stepComparison K R p := rfl

/-- Each step comparison map is a quasi-isomorphism. -/
private lemma stepComparison_quasiIso [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A)
    (R : FunctorialKInjectiveResolution A) (p : ℤ) :
    QuasiIso (stepComparison K R p) := by
  let : QuasiIso (R.inclusion.app (K.filtration.obj (op p))) := R.quasiIso _
  exact quasiIso_biprod_lift_of_contractible _ _
    (correctionTail_contractible K R p).some

/-- The short complex `X ⟶ Y ⟶ cokernel f` attached to a map of complexes. -/
private noncomputable abbrev cokernelShortComplex
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk f (cokernel.π f) (cokernel.condition f)

/-- A monomorphism of complexes sits in a short exact sequence with its
cokernel. -/
private lemma cokernelShortComplex_shortExact
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [Mono f] :
    (cokernelShortComplex f).ShortExact where
  exact := ShortComplex.exact_cokernel f
  mono_f := inferInstance
  epi_g := inferInstance

/-- If the source of a monomorphism of complexes has injective terms, then the
short exact sequence with its cokernel splits in every degree. -/
private noncomputable def cokernelDegreewiseSplitting
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [Mono f]
    (hX : ∀ n, Injective (X.X n)) :
    ∀ n, ((cokernelShortComplex f).map
      (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).Splitting := by
  intro n
  letI : Injective
      (((cokernelShortComplex f).map
        (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).X₁) := hX n
  exact ((cokernelShortComplex_shortExact f).map_of_exact
    (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).splittingOfInjective

/-- The cokernel of a monomorphism between complexes with injective terms again
has injective terms. -/
private lemma injective_cokernel_of_degreewise_mono
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [Mono f]
    (hX : ∀ n, Injective (X.X n)) (hY : ∀ n, Injective (Y.X n)) :
    ∀ n, Injective ((cokernel f).X n) := by
  intro n
  let : Injective
      (((cokernelShortComplex f).map
        (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).X₂) := hY n
  let σ := cokernelDegreewiseSplitting f hX n
  exact Retract.injective ⟨σ.s, (cokernel.π f).f n, σ.s_g⟩

/-- The cokernel of a monomorphism of K-injective complexes whose source has
injective terms is again K-injective, by the two-out-of-three property along the
degreewise split distinguished triangle. -/
private lemma isKInjective_cokernel_of_degreewise_mono
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) [Mono f]
    (hX : ∀ n, Injective (X.X n))
    (hKX : X.IsKInjective) (hKY : Y.IsKInjective) :
    (cokernel f).IsKInjective :=
  (CochainComplex.isKInjective_two_out_of_three_of_distTriang _ _ _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished
      (cokernelShortComplex f) (cokernelDegreewiseSplitting f hX))).2.2 hKX hKY

/-- A map of monomorphisms whose two components are quasi-isomorphisms induces a
quasi-isomorphism on cokernels. -/
private lemma quasiIso_cokernel_map
    {X Y X' Y' : CochainComplex A ℤ}
    (f : X ⟶ Y) (g : X' ⟶ Y') [Mono f] [Mono g]
    (a : X ⟶ X') (b : Y ⟶ Y') (w : f ≫ b = a ≫ g)
    [QuasiIso a] [QuasiIso b] :
    QuasiIso (cokernel.map f g a b w) := by
  let φ : cokernelShortComplex f ⟶ cokernelShortComplex g :=
    { τ₁ := a
      τ₂ := b
      τ₃ := cokernel.map f g a b w
      comm₁₂ := w.symm
      comm₂₃ := by simp }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (cokernelShortComplex_shortExact f) (cokernelShortComplex_shortExact g)
    inferInstance inferInstance

/-- **Stacks 0BKI.** A filtered complex in a Grothendieck abelian category has a
filtered resolution which is termwise injective and K-injective before and after
taking any filtration step or filtration quotient, and the comparison maps on all
of these complexes are quasi-isomorphisms. -/
@[stacks 0BKI]
theorem exists_filtered_quasiIso_isKInjective [IsGrothendieckAbelian.{w'} A]
    (K : CochainComplex.Filtered A) :
    ∃ (J : CochainComplex.Filtered A) (j : K ⟶ J),
      (∀ n : ℤ, Injective (J.X.X n)) ∧
      (∀ p n : ℤ, Injective ((J.filtration.obj (op p)).X n)) ∧
      (∀ p n : ℤ, Injective ((cokernel (J.filtration.ι.app (op p))).X n)) ∧
      (∀ (p p' : ℤ) (h : p ≤ p') n,
        Injective ((cokernel (J.filtration.diagram.map (opHomOfLE h))).X n)) ∧
      J.X.IsKInjective ∧
      (∀ p : ℤ, (J.filtration.obj (op p)).IsKInjective) ∧
      (∀ p : ℤ, (cokernel (J.filtration.ι.app (op p))).IsKInjective) ∧
      (∀ (p p' : ℤ) (h : p ≤ p'),
        (cokernel (J.filtration.diagram.map (opHomOfLE h))).IsKInjective) ∧
      QuasiIso j.hom ∧
      (∀ p : ℤ, QuasiIso (j.natTrans.app (op p))) ∧
      (∀ p : ℤ, QuasiIso (filtrationQuotientMap j p)) ∧
      ∀ (p p' : ℤ) (h : p ≤ p'), QuasiIso (filtrationSubquotientMap j h) := by
  let R := functorialKInjectiveResolution A
  let J := resolved K R
  let j := resolvedMap K R
  refine ⟨J, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ambient_terms_injective K R
  · exact stepGraph_source_terms_injective K R
  · intro p n
    exact injective_cokernel_of_degreewise_mono
      (J.filtration.ι.app (op p))
      (stepGraph_source_terms_injective K R p)
      (ambient_terms_injective K R) n
  · intro p p' h n
    exact injective_cokernel_of_degreewise_mono
      (J.filtration.diagram.map (opHomOfLE h))
      (stepGraph_source_terms_injective K R p')
      (stepGraph_source_terms_injective K R p) n
  · exact ambient_isKInjective K R
  · exact stepGraph_source_isKInjective K R
  · intro p
    exact isKInjective_cokernel_of_degreewise_mono
      (J.filtration.ι.app (op p))
      (stepGraph_source_terms_injective K R p)
      (stepGraph_source_isKInjective K R p) (ambient_isKInjective K R)
  · intro p p' h
    exact isKInjective_cokernel_of_degreewise_mono
      (J.filtration.diagram.map (opHomOfLE h))
      (stepGraph_source_terms_injective K R p')
      (stepGraph_source_isKInjective K R p')
      (stepGraph_source_isKInjective K R p)
  · exact ambientMap_quasiIso K R
  · exact stepComparison_quasiIso K R
  · intro p
    let : QuasiIso (j.natTrans.app (op p)) := stepComparison_quasiIso K R p
    let : QuasiIso j.hom := ambientMap_quasiIso K R
    exact quasiIso_cokernel_map
      (K.filtration.ι.app (op p)) (J.filtration.ι.app (op p))
      (j.natTrans.app (op p)) j.hom (j.comm (op p)).symm
  · intro p p' h
    let : QuasiIso (j.natTrans.app (op p')) := stepComparison_quasiIso K R p'
    let : QuasiIso (j.natTrans.app (op p)) := stepComparison_quasiIso K R p
    exact quasiIso_cokernel_map
      (K.filtration.diagram.map (opHomOfLE h))
      (J.filtration.diagram.map (opHomOfLE h))
      (j.natTrans.app (op p')) (j.natTrans.app (op p))
      (j.natTrans.naturality (opHomOfLE h))

end Stacks.Injectives
