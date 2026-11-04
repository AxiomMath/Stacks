module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Regular.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Sum
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.Topology.Dimension.Codimension
public import StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# The effective Cartier part of a closed subscheme

Let `X` be a Noetherian scheme and `Z ⊆ X` a closed subscheme contained, set-theoretically, in
the union of a family of integral effective Cartier divisors `Dᵢ` together with a closed subset
all of whose components have codimension at least two.  Then a suitable finite nonnegative
combination `D = ∑ aᵢ Dᵢ` is an effective Cartier divisor contained in `Z` and agreeing with `Z`
away from codimension two.

## Main results

* `AlgebraicGeometry.exists_effectiveCartierDivisor_agree_off_codimension_two`: a finite
  nonnegative combination of the `Dᵢ` is an effective Cartier divisor contained in `Z` and
  agreeing with `Z` away from codimension two.
* `AlgebraicGeometry.exists_le_pow_comap_eq_of_supportSet_subset`: the case of a single integral
  effective Cartier divisor, over a locally Noetherian scheme.

## References

* [Stacks Project, Tag 0AGB](https://stacks.math.columbia.edu/tag/0AGB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors TopologicalSpace

universe u v

namespace AlgebraicGeometry

private alias stalk_le_maximalIdeal_iff_mem_support :=
    Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support

private lemma stalk_ne_top_of_mem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (x : X) (hx : x ∈ I.support) :
    IdealSheafData.stalk I x ≠ ⊤ := by
  intro h
  have hle : (⊤ : Ideal (X.presheaf.stalk x)) ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    simpa [h] using (stalk_le_maximalIdeal_iff_mem_support I x).2 hx
  exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
    (top_le_iff.mp hle)

/-- The stalk of an ideal sheaf is the unit ideal away from its support. -/
private lemma stalk_eq_top_of_notMem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (x : X) (hx : x ∉ I.support) :
    IdealSheafData.stalk I x = ⊤ := by
  by_contra htop
  exact hx ((stalk_le_maximalIdeal_iff_mem_support I x).mp (IsLocalRing.le_maximalIdeal htop))

/-- The image of a point of the closed subscheme of `I` lies in the support of `I`. -/
private lemma subschemeι_mem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (ξ : I.subscheme) : I.subschemeι ξ ∈ I.support := by
  change I.subschemeι ξ ∈ (I.support : Set X)
  rw [← I.range_subschemeι]
  exact ⟨ξ, rfl⟩

/-- Every point of a scheme has an affine open neighborhood. -/
private lemma exists_affineOpen_mem {X : Scheme.{u}} (x : X) : ∃ U : X.affineOpens, x ∈ U.1 := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU⟩

private lemma ideal_chart_prime_minimal {X : Scheme.{u}} (I : X.IdealSheafData)
    (ξ : I.subscheme)
    (hξ : ∃ C : irreducibleComponents I.subscheme,
      IsGenericPoint ξ (C : Set I.subscheme))
    (U : X.affineOpens) (hxU : I.subschemeι ξ ∈ U.1) :
    (I.ideal U).IsMinimalPrime
      (U.2.primeIdealOf ⟨I.subschemeι ξ, hxU⟩).asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  let x : X := I.subschemeι ξ
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hpfrom : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hxSupport : x ∈ I.supportSet := subschemeι_mem_support I ξ
  have hIp : I.ideal U ≤ p.asIdeal := by
    intro f hf
    have hnot : x ∉ X.basicOpen f :=
      (Scheme.mem_zeroLocus_iff X (I.ideal U : Set Γ(X, U.1)) x).mp
        (I.supportSet_subset_zeroLocus U hxSupport) f hf
    by_contra hfp
    have hxbasic : x ∈ X.basicOpen f := by
      rw [← hpfrom]
      change p ∈ (hU.fromSpec ⁻¹ᵁ X.basicOpen f)
      rw [hU.fromSpec_preimage_basicOpen f]
      exact (PrimeSpectrum.mem_basicOpen f p).2 hfp
    exact hnot hxbasic
  refine ⟨⟨p.isPrime, hIp⟩, ?_⟩
  intro q hq hqp
  let qpt : Spec Γ(X, U) := ⟨q, hq.1⟩
  let yX : X := hU.fromSpec qpt
  have hyU : yX ∈ U.1 := by
    change hU.fromSpec qpt ∈ U.1
    have hyRange : hU.fromSpec qpt ∈ Set.range hU.fromSpec := ⟨qpt, rfl⟩
    rw [hU.range_fromSpec] at hyRange
    exact hyRange
  have hyzero : yX ∈ X.zeroLocus (U := U.1) (I.ideal U) := by
    apply (Scheme.mem_zeroLocus_iff X (I.ideal U : Set Γ(X, U.1)) yX).2
    intro f hf hbasic
    have hqbasic : qpt ∈ PrimeSpectrum.basicOpen f := by
      rw [← hU.fromSpec_preimage_basicOpen f]
      exact hbasic
    exact (PrimeSpectrum.mem_basicOpen f qpt).mp hqbasic (hq.2 hf)
  have hySupport : yX ∈ I.supportSet := (I.mem_supportSet_iff_of_mem hyU).2 hyzero
  have hyRange : yX ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hySupport
  obtain ⟨η, hη⟩ := hyRange
  have hqpSpec : qpt ⤳ p :=
    (PrimeSpectrum.le_iff_specializes qpt p).mp
      ((PrimeSpectrum.asIdeal_le_asIdeal qpt p).mpr hqp)
  have hqpX : yX ⤳ x := by
    simpa [yX, x, hpfrom] using hqpSpec.map hU.fromSpec.continuous
  obtain ⟨C, hgen⟩ := hξ
  have hsource : ξ ∈ closure ({η} : Set I.subscheme) := by
    have hclX : I.subschemeι ξ ∈ closure ({I.subschemeι η} : Set X) := by
      simpa [x, yX, hη] using (specializes_iff_mem_closure.mp hqpX)
    rw [I.subschemeι.isClosedEmbedding.isInducing.closure_eq_preimage_closure_image]
    change I.subschemeι ξ ∈ closure (I.subschemeι '' ({η} : Set I.subscheme))
    simpa [Set.image_singleton] using hclX
  have hsub : (C : Set I.subscheme) ⊆ closure ({η} : Set I.subscheme) := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hsource) isClosed_closure
  have hclsub : closure ({η} : Set I.subscheme) ⊆ (C : Set I.subscheme) :=
    C.2.2 isIrreducible_singleton.closure hsub
  have hηgen : IsGenericPoint η (C : Set I.subscheme) :=
    Set.Subset.antisymm hclsub hsub
  have hξη : ξ = η := hgen.eq hηgen
  have hpoint : yX = x := by
    calc
      yX = I.subschemeι η := hη.symm
      _ = I.subschemeι ξ := congrArg I.subschemeι hξη.symm
      _ = x := rfl
  have hpoint' : hU.fromSpec qpt = hU.fromSpec p := by simpa [yX, hpfrom] using hpoint
  have hqpEq : qpt = p := hU.fromSpec.isOpenEmbedding.injective hpoint'
  change p.asIdeal ≤ q
  rw [← congrArg PrimeSpectrum.asIdeal hqpEq]

private lemma stalk_ne_bot_of_generic_component {X : Scheme.{u}}
    (I : X.IdealSheafData) (ξ : I.subscheme)
    (hξ : ∃ C : irreducibleComponents I.subscheme,
      IsGenericPoint ξ (C : Set I.subscheme))
    (x : X) (hxy : x = I.subschemeι ξ)
    (hdom : IsDomain (X.presheaf.stalk x))
    (hdvr : IsDiscreteValuationRing (X.presheaf.stalk x)) :
    IdealSheafData.stalk I (I.subschemeι ξ) ≠ ⊥ := by
  cases hxy
  classical
  let x : X := I.subschemeι ξ
  let _ : IsDomain (X.presheaf.stalk x) := hdom
  let _ : IsDiscreteValuationRing (X.presheaf.stalk x) := hdvr
  obtain ⟨⟨U, hU⟩, hxU⟩ := exists_affineOpen_mem x
  let U' : X.affineOpens := ⟨U, hU⟩
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hpmin := ideal_chart_prime_minimal I ξ hξ U' hxU
  let _ : Algebra (Γ(X, U)) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hmap : (I.ideal U').map (algebraMap (Γ(X, U)) (X.presheaf.stalk x)) =
      IdealSheafData.stalk I x := by
    rw [IdealSheafData.stalk_eq_map_germ I x U' hxU]
    rfl
  intro hbot
  have hu : (Ideal.map (algebraMap (Γ(X, U)) (X.presheaf.stalk x)) p.asIdeal).under
      (Γ(X, U)) = p.asIdeal :=
    Ideal.under_map_of_isLocalizationAtPrime (q := p.asIdeal) (p := p.asIdeal) le_rfl
  have hpmap : Ideal.map (algebraMap (Γ(X, U)) (X.presheaf.stalk x)) p.asIdeal ∈
      ((I.ideal U').map (algebraMap (Γ(X, U)) (X.presheaf.stalk x))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map p.asIdeal.primeCompl (X.presheaf.stalk x) (I.ideal U')]
    change (Ideal.map (algebraMap (Γ(X, U)) (X.presheaf.stalk x)) p.asIdeal).under
      (Γ(X, U)) ∈ (I.ideal U').minimalPrimes
    rw [hu]
    exact hpmin
  have hpmapBot : Ideal.map (algebraMap (Γ(X, U)) (X.presheaf.stalk x)) p.asIdeal = ⊥ := by
    rw [hmap, hbot] at hpmap
    have hmem : (⊥ : Ideal (X.presheaf.stalk x)).IsMinimalPrime
        (Ideal.map (algebraMap (Γ(X, U)) (X.presheaf.stalk x)) p.asIdeal) := by
      simpa only [Ideal.minimalPrimes, Set.mem_ofPred_eq] using hpmap
    have hle := hmem.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    exact le_antisymm hle bot_le
  have hmax : Ideal.map (algebraMap (Γ(X, U)) (X.presheaf.stalk x)) p.asIdeal =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal _ _
  rw [hmax] at hpmapBot
  exact IsDiscreteValuationRing.not_isField (X.presheaf.stalk x)
    (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hpmapBot)

private lemma exists_affine_chart_generator {X : Scheme.{u}}
    (I : X.IdealSheafData)
    (hI : IsEffectiveCartierDivisor I)
    (x : X) (hx : x ∈ I.support) :
    ∃ (U : X.affineOpens), x ∈ U.1 ∧ ∃ f : Γ(X, U),
      IsRegular f ∧ I.ideal U = Ideal.span {f} := by
  rcases (isEffectiveCartierDivisor_iff_affineLocal I).mp hI x hx with
    ⟨U, hU, hxU, f, hf, e, he⟩
  let U' : X.affineOpens := ⟨U, hU⟩
  refine ⟨U', hxU, f, hf, ?_⟩
  exact ideal_eq_quotient_of_chart I U hU (Ideal.span {f}) e he

private lemma exists_affine_below_finset {X : Scheme.{u}} {ι : Type v}
    (s : Finset ι) (U : ι → X.affineOpens) (x : X)
    (hx : ∀ i ∈ s, x ∈ (U i).1) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ ∀ i ∈ s, W ≤ U i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ :=
        (X.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      refine ⟨⟨W, hW⟩, hxW, ?_⟩
      intro i hi
      simp at hi
  | @insert i s his ih =>
      obtain ⟨W, hxW, hW⟩ := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
      obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hsub⟩ :=
        (X.isBasis_affineOpens).exists_subset_of_mem_open
          (show x ∈ (W.1 : Set X) ∩ (U i).1 from
            ⟨hxW, hx i (Finset.mem_insert_self i s)⟩)
          (W.1.2.inter (U i).1.2)
      let W' : X.affineOpens := ⟨V, hV⟩
      refine ⟨W', hxV, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact fun y hy => (hsub hy).2
      · exact le_trans (show W' ≤ W from fun y hy => (hsub hy).1) (hW j hj)

private lemma isRegular_map_of_flat {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) (a : A) (ha : IsRegular a) :
    IsRegular (f a) := by
  let _ : Algebra A B := f.toAlgebra
  have hflat : Module.Flat A B := hf
  have hmul : IsSMulRegular B (algebraMap A B a) :=
    ha.left.isSMulRegular.of_flat
  change IsRegular (algebraMap A B a)
  exact ⟨fun x y hxy => hmul hxy, fun x y hxy => hmul (by simpa [mul_comm] using hxy)⟩

private lemma restriction_flat {X : Scheme.{u}} {U W : X.affineOpens}
    (hWU : W ≤ U) :
    ((X.presheaf.map (homOfLE (X := X.Opens) hWU).op).hom).Flat := by
  let f := (𝟙 X : X ⟶ X).resLE U.1 W.1 hWU
  have _ : IsOpenImmersion f := by
    simpa [f, Scheme.Hom.resLE_id] using
      (inferInstance : IsOpenImmersion (X.homOfLE hWU))
  have _ : IsAffine (W.1.toScheme) := W.2
  have _ : IsAffine (U.1.toScheme) := U.2
  have hf : f.appTop.hom.Flat := f.flat_appTop
  have hf' : ((𝟙 X : X ⟶ X).appLE U.1 W.1 hWU).hom.Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso (𝟙 X : X ⟶ X) U.1 W.1 hWU)).mp hf
  have heq : CommRingCat.Hom.hom
      (𝟙 Γ(X, U) ≫ X.presheaf.map (homOfLE (X := X.Opens) hWU).op) =
      (X.presheaf.map (homOfLE (X := X.Opens) hWU).op).hom :=
    congrArg CommRingCat.Hom.hom (Category.id_comp _)
  change RingHom.Flat (CommRingCat.Hom.hom
    (𝟙 Γ(X, U) ≫ X.presheaf.map (homOfLE (X := X.Opens) hWU).op)) at hf'
  rw [heq] at hf'
  exact hf'

private lemma restrict_generator_of_effective_cartier
    {X : Scheme.{u}} (I : X.IdealSheafData) {U W : X.affineOpens}
    (hWU : W ≤ U) (f : Γ(X, U)) (hf : IsRegular f)
    (hspan : I.ideal U = Ideal.span {f}) :
    ∃ fW : Γ(X, W), IsRegular fW ∧ I.ideal W = Ideal.span {fW} := by
  let φ := (X.presheaf.map (homOfLE (X := X.Opens) hWU).op).hom
  let fW : Γ(X, W) := φ f
  have hfW : IsRegular fW := isRegular_map_of_flat φ (restriction_flat hWU) f hf
  refine ⟨fW, hfW, ?_⟩
  rw [← I.map_ideal hWU, hspan, Ideal.map_span]
  simp [fW]
  rfl

private lemma exists_common_affine_principal_neighborhood
    {X : Scheme.{u}} {ι : Type v} (D : ι → X.IdealSheafData)
    (hD : ∀ i, IsEffectiveCartierDivisor (D i))
    (s : Finset ι) (x : X) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧
      (∀ i ∈ s, x ∈ (D i).support →
        ∃ f : Γ(X, W), IsRegular f ∧ (D i).ideal W = Ideal.span {f}) ∧
      (∀ i ∈ s, x ∉ (D i).support →
        (W.1 : Set X) ⊆ Set.compl ((D i).support : Set X)) := by
  classical
  let localData : ∀ i, ∃ U : X.affineOpens, x ∈ U.1 ∧
      (x ∈ (D i).support →
        ∃ f : Γ(X, U), IsRegular f ∧ (D i).ideal U = Ideal.span {f}) ∧
      (x ∉ (D i).support →
        (U.1 : Set X) ⊆ Set.compl ((D i).support : Set X)) := by
    intro i
    by_cases hx : x ∈ (D i).support
    · obtain ⟨U, hxU, f, hf, hspan⟩ := exists_affine_chart_generator (D i) (hD i) x hx
      exact ⟨U, hxU, fun _ => ⟨f, hf, hspan⟩, fun hn => (hn hx).elim⟩
    · obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hsub⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open
          (show x ∈ Set.compl ((D i).support : Set X) from hx)
          (D i).isClosed_supportSet.isOpen_compl
      exact ⟨⟨U, hU⟩, hxU, fun hx' => (hx hx').elim, fun _ => hsub⟩
  let V : ι → X.affineOpens := fun i => Classical.choose (localData i)
  have hxV : ∀ i ∈ s, x ∈ (V i).1 := fun i _ => (Classical.choose_spec (localData i)).1
  obtain ⟨W, hxW, hW⟩ := exists_affine_below_finset s V x hxV
  refine ⟨W, hxW, ?_, ?_⟩
  · intro i hi hxi
    obtain ⟨f, hf, hspan⟩ := (Classical.choose_spec (localData i)).2.1 hxi
    exact restrict_generator_of_effective_cartier (D i) (hW i hi) f hf hspan
  · intro i hi hxi z hz
    exact (Classical.choose_spec (localData i)).2.2 hxi (hW i hi hz)

private lemma ideal_top_of_support_disjoint
    {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.affineOpens)
    (hW : (I.support : Set X) ∩ W.1 = ∅) : I.ideal W = ⊤ := by
  change I.supportSet ∩ W.1 = ∅ at hW
  have hzero : X.zeroLocus (U := W.1) (I.ideal W) ∩ W.1 = ∅ := by
    rw [← I.supportSet_inter W, hW]
  have hspec : PrimeSpectrum.zeroLocus (I.ideal W : Set Γ(X, W)) = ∅ := by
    have himage := W.2.fromSpec_image_zeroLocus (I.ideal W)
    rw [hzero] at himage
    exact Set.image_eq_empty.mp himage
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp hspec

/-- The generic point of an irreducible component generates that component. -/
private lemma isGenericPoint_genericPoint_component {Y : Type u} [TopologicalSpace Y]
    [QuasiSober Y] (C : irreducibleComponents Y) :
    IsGenericPoint C.2.1.genericPoint (C : Set Y) := by
  simpa only [(isClosed_of_mem_irreducibleComponents C.1 C.2).closure_eq] using
    C.2.1.isGenericPoint_genericPoint_closure

/-- The generic point of an irreducible space generates an irreducible component. -/
private lemma exists_component_isGenericPoint_genericPoint (Y : Type u) [TopologicalSpace Y]
    [IrreducibleSpace Y] [QuasiSober Y] :
    ∃ C : irreducibleComponents Y, IsGenericPoint (_root_.genericPoint Y) (C : Set Y) := by
  refine ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; simp⟩, ?_⟩
  simpa using genericPoint_spec Y

private lemma codimension_genericPoint_eq_one {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [IsIntegral I.subscheme]
    (hI : IsEffectiveCartierDivisor I) :
    codimension (IrreducibleCloseds.closureSingleton
      (I.subschemeι (_root_.genericPoint I.subscheme))) = 1 := by
  let ξ : I.subscheme := _root_.genericPoint I.subscheme
  have hlocal := ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor
    I hI ξ (exists_component_isGenericPoint_genericPoint I.subscheme)
  let y : X := I.subschemeι ξ
  have hdim : (Order.coheight y : WithBot ℕ∞) = (1 : WithBot ℕ∞) := by
    rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
    exact hlocal
  have hdim' : Order.coheight y = (1 : ℕ∞) := by exact_mod_cast hdim
  calc
    codimension (IrreducibleCloseds.closureSingleton y) =
        Order.coheight (IrreducibleCloseds.closureSingleton y) :=
      codimension_eq_coheight _
    _ = Order.coheight y := by
      let e := irreducibleSetEquivPoints (α := X)
      have hy : IsGenericPoint y (IrreducibleCloseds.closureSingleton y : Set X) := rfl
      have heq : e (IrreducibleCloseds.closureSingleton y) = y := by
        change (IrreducibleCloseds.closureSingleton y).isIrreducible.genericPoint = y
        exact ((IrreducibleCloseds.closureSingleton y).isIrreducible
          |>.isGenericPoint_genericPoint (IrreducibleCloseds.closureSingleton y).isClosed).eq hy
      calc
        Order.coheight (IrreducibleCloseds.closureSingleton y) =
            Order.coheight (e (IrreducibleCloseds.closureSingleton y)) :=
          (Order.coheight_orderIso e (IrreducibleCloseds.closureSingleton y)).symm
        _ = Order.coheight y := congrArg Order.coheight heq
    _ = 1 := hdim'

private lemma codimension_antitone_of_le {X : Type u} [TopologicalSpace X]
    {A B : IrreducibleCloseds X} (h : A ≤ B) : codimension B ≤ codimension A := by
  rw [codimension_eq_coheight, codimension_eq_coheight]
  exact Order.coheight_le_iff.mpr fun p hp => Order.length_le_coheight (le_trans h hp)

private lemma exists_divisor_of_codimension_one_point
    {X : Scheme.{u}} {Z : X.IdealSheafData} {Z' : Closeds X}
    {ι : Type v} (D : ι → X.IdealSheafData)
    (hZ' : ∀ x : X, x ∈ (Z' : Set X) →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hcover : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ i, ((D i).support : Set X))
    (x : X) (hx : x ∈ (Z.support : Set X))
    (hcodim : codimension (IrreducibleCloseds.closureSingleton x) = 1) :
    ∃ i, x ∈ ((D i).support : Set X) := by
  rcases hcover hx with hx' | hxD
  · have h := hZ' x hx'
    norm_num [hcodim] at h
  · exact Set.mem_iUnion.mp hxD

private lemma genericPoint_support_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] :
    closure ({I.subschemeι (_root_.genericPoint I.subscheme)} : Set X) =
      (I.support : Set X) := by
  rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
    genericPoint_closure, Set.image_univ, I.range_subschemeι]

private lemma ideal_prime_of_integral_subscheme_on_affine
    {X : Scheme.{u}} (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (U : X.affineOpens) (x : X) (hxI : x ∈ I.support) (hxU : x ∈ U.1) :
    (I.ideal U).IsPrime := by
  obtain ⟨ξ, hξ⟩ : x ∈ Set.range I.subschemeι := by rwa [I.range_subschemeι]
  let V : I.subscheme.Opens := I.subschemeι ⁻¹ᵁ U.1
  have hξV : ξ ∈ V := by
    change I.subschemeι ξ ∈ U.1
    simpa [hξ] using hxU
  let _ : Nonempty V.toScheme := ⟨⟨ξ, hξV⟩⟩
  let _ : IsIntegral V.toScheme := inferInstance
  let e := I.subschemeObjIso U
  have hΓ : IsDomain Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) := inferInstance
  have _ : IsDomain (Γ(X, U) ⧸ I.ideal U) :=
    e.commRingCatIsoToRingEquiv.isDomain_iff.mp hΓ
  exact (Ideal.Quotient.isDomain_iff_prime (I.ideal U)).mp inferInstance

private lemma ideal_eq_primeIdealOf_generic
    {X : Scheme.{u}} (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (U : X.affineOpens) (ξ : I.subscheme)
    (hξ : ξ = _root_.genericPoint I.subscheme) (hξU : I.subschemeι ξ ∈ U.1) :
    I.ideal U = (U.2.primeIdealOf ⟨I.subschemeι ξ, hξU⟩).asIdeal := by
  subst ξ
  have hpmin := ideal_chart_prime_minimal I (_root_.genericPoint I.subscheme)
    (exists_component_isGenericPoint_genericPoint I.subscheme) U hξU
  have hprime := ideal_prime_of_integral_subscheme_on_affine I U
    (I.subschemeι (_root_.genericPoint I.subscheme))
    (subschemeι_mem_support I _) hξU
  exact le_antisymm hpmin.le (hpmin.2 ⟨hprime, le_rfl⟩ hpmin.le)

/-- A point of the support of an integral `I` specializes to the generic point of `I.subscheme`. -/
private lemma closureSingleton_le_genericPoint {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] (x : X) (hx : x ∈ I.support) :
    IrreducibleCloseds.closureSingleton x ≤
      IrreducibleCloseds.closureSingleton (I.subschemeι (_root_.genericPoint I.subscheme)) := by
  change closure ({x} : Set X) ⊆ closure _
  rw [genericPoint_support_eq]
  exact closure_minimal (Set.singleton_subset_iff.mpr hx) I.isClosed_supportSet

private lemma codimension_ge_one_of_mem_integral_effective_support
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [IsIntegral I.subscheme]
    (hI : IsEffectiveCartierDivisor I)
    (x : X) (hx : x ∈ (I.support : Set X)) :
    1 ≤ codimension (IrreducibleCloseds.closureSingleton x) :=
  (codimension_genericPoint_eq_one I hI).symm.le.trans
    (codimension_antitone_of_le (closureSingleton_le_genericPoint I x hx))

private lemma codimension_ge_one_of_mem_covered_support
    {X : Scheme.{u}} [IsLocallyNoetherian X] {Z : X.IdealSheafData}
    {Z' : Closeds X} {ι : Type v} (D : ι → X.IdealSheafData)
    (hD : ∀ i, IsIntegral (D i).subscheme ∧
      IsEffectiveCartierDivisor (D i))
    (hZ' : ∀ x : X, x ∈ (Z' : Set X) →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hcover : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ i, ((D i).support : Set X))
    (x : X) (hx : x ∈ (Z.support : Set X)) :
    1 ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  rcases hcover hx with hx' | hxD
  · exact le_trans (by norm_num) (hZ' x hx')
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxD
    let _ : IsIntegral (D i).subscheme := (hD i).1
    exact codimension_ge_one_of_mem_integral_effective_support (D i) (hD i).2 x hxi

/-- An extended natural number that is at least `1` and different from `1` is at least `2`. -/
lemma codimension_ge_two_of_ge_one_ne_one (n : ℕ∞)
    (h₁ : 1 ≤ n) (hne : n ≠ 1) : 2 ≤ n := by
  cases n with
  | top => simp
  | coe k =>
    have hk : 1 ≤ k := by simpa using h₁
    have hkne : k ≠ 1 := by simpa using hne
    exact_mod_cast (show 2 ≤ k by omega)

private lemma codimension_ge_two_of_mem_support_outside_open
    {X : Scheme.{u}} [IsLocallyNoetherian X] {Z : X.IdealSheafData}
    {Z' : Closeds X} {ι : Type v} (D : ι → X.IdealSheafData)
    (hD : ∀ i, IsIntegral (D i).subscheme ∧
      IsEffectiveCartierDivisor (D i))
    (hZ' : ∀ x : X, x ∈ (Z' : Set X) →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hcover : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ i, ((D i).support : Set X))
    (U : X.Opens)
    (hU : ∀ x : X, x ∈ (Z.support : Set X) →
      codimension (IrreducibleCloseds.closureSingleton x) = 1 → x ∈ U)
    (x : X) (hx : x ∈ (Z.support : Set X)) (hxU : x ∉ U) :
    (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  exact codimension_ge_two_of_ge_one_ne_one _
    (codimension_ge_one_of_mem_covered_support D hD hZ' hcover x hx) fun hcod => hxU (hU x hx hcod)

private lemma irreducibleCloseds_eq_of_le_and_codim_one
    {X : Type u} [TopologicalSpace X] {A B : IrreducibleCloseds X}
    (hAB : A ≤ B) (hA : codimension A = 1) (hB : codimension B = 1) : A = B := by
  by_contra hne
  have hlt : A < B := lt_of_le_of_ne hAB hne
  have h := Order.coheight_add_one_le hlt
  rw [← codimension_eq_coheight A, ← codimension_eq_coheight B, hA, hB] at h
  norm_num at h

private lemma mem_span_pow_of_mul_mem_span_pow
    {A : Type*} [CommRing A] (f s x : A) (hf : IsRegular f)
    (hP : (Ideal.span {f} : Ideal A).IsPrime) (hs : s ∉ Ideal.span {f}) :
    ∀ n : ℕ, s * x ∈ Ideal.span {f} ^ n → x ∈ Ideal.span {f} ^ n := by
  intro n
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      intro h
      have hpow : s * x ∈ Ideal.span {f ^ (n + 1)} := by
        simpa only [Ideal.span_singleton_pow] using h
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hpow
      have hsxP : s * x ∈ Ideal.span {f} :=
        Ideal.mem_span_singleton.mpr ⟨y * f ^ n, by rw [hy]; ring⟩
      have hxP : x ∈ Ideal.span {f} :=
        (hP.mem_or_mem hsxP).resolve_left hs
      obtain ⟨x', hx'⟩ := Ideal.mem_span_singleton.mp hxP
      have hcancelMul : f * (s * x') = f * (y * f ^ n) := by
        calc
          f * (s * x') = s * (f * x') := by ring
          _ = s * x := by rw [hx']
          _ = f * (y * f ^ n) := by rw [hy]; ring
      have hcancel : s * x' = y * f ^ n := hf.1 hcancelMul
      have hsx'n : s * x' ∈ Ideal.span {f} ^ n := by
        rw [Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton.mpr ⟨y, by rw [hcancel]; ring⟩
      have hxn : x' ∈ Ideal.span {f} ^ n := ih x' hsx'n
      rw [Ideal.span_singleton_pow] at hxn
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hxn
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.mpr ⟨z, by rw [hx', hz]; ring⟩

private lemma mem_span_pow_of_mem_atPrime
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (f x : A) (hf : IsRegular f) (hP : (Ideal.span {f} : Ideal A).IsPrime)
    (n : ℕ) [IsLocalization.AtPrime S (Ideal.span {f})]
    (hx : algebraMap A S x ∈ (Ideal.span {f} ^ n).map (algebraMap A S)) :
    x ∈ Ideal.span {f} ^ n := by
  obtain ⟨s, hs, hsx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Ideal.span {f} : Ideal A).primeCompl S (Ideal.span {f} ^ n) x).mp hx
  exact mem_span_pow_of_mul_mem_span_pow f s x hf hP
    (Ideal.mem_primeCompl_iff.mp hs) n hsx

private lemma mem_finset_product_of_mem_each_prime_power
    {A ι : Type*} [CommRing A] (s : Finset ι) (f : ι → A) (n : ι → ℕ)
    (x : A)
    (hreg : ∀ i ∈ s, IsRegular (f i))
    (hprime : ∀ i ∈ s, (Ideal.span {f i} : Ideal A).IsPrime)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ^ n i ∉ Ideal.span {f j})
    (hmem : ∀ i ∈ s, x ∈ Ideal.span {f i} ^ n i) :
    x ∈ ∏ i ∈ s, Ideal.span {f i} ^ n i := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | @insert i s hi ih =>
      have hxpow : x ∈ Ideal.span {f i ^ n i} := by
        simpa only [Ideal.span_singleton_pow] using hmem i (Finset.mem_insert_self i s)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hxpow
      have hymem : ∀ j ∈ s, y ∈ Ideal.span {f j} ^ n j := by
        intro j hj
        have hij : i ≠ j := by
          rintro rfl
          exact hi hj
        apply mem_span_pow_of_mul_mem_span_pow (f j) (f i ^ n i) y
          (hreg j (Finset.mem_insert_of_mem hj))
          (hprime j (Finset.mem_insert_of_mem hj))
          (hcross i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) hij)
          (n j)
        simpa [hy, mul_comm] using hmem j (Finset.mem_insert_of_mem hj)
      rw [Finset.prod_insert hi, hy]
      exact Ideal.mul_mem_mul
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (f i)) (n i))
        (ih y (fun j hj => hreg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hprime j (Finset.mem_insert_of_mem hj))
          (fun j hj k hk hjk => hcross j (Finset.mem_insert_of_mem hj)
            k (Finset.mem_insert_of_mem hk) hjk) hymem)

private lemma ideal_le_finset_product_of_atPrime_powers
    {A ι : Type*} [CommRing A] (s : Finset ι) (f : ι → A) (n : ι → ℕ)
    (I : Ideal A)
    (hreg : ∀ i ∈ s, IsRegular (f i))
    (hprime : ∀ i ∈ s, (Ideal.span {f i} : Ideal A).IsPrime)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ^ n i ∉ Ideal.span {f j})
    (hlocal : ∀ i ∈ s, ∀ x ∈ I, ∃ t : A, t ∉ Ideal.span {f i} ∧
      t * x ∈ Ideal.span {f i} ^ n i) :
    I ≤ ∏ i ∈ s, Ideal.span {f i} ^ n i := by
  intro x hx
  exact mem_finset_product_of_mem_each_prime_power s f n x hreg hprime hcross
    (fun i hi => by
      let _ : (Ideal.span {f i} : Ideal A).IsPrime := hprime i hi
      obtain ⟨t, ht, htx⟩ := hlocal i hi x hx
      exact mem_span_pow_of_mul_mem_span_pow (f i) t x (hreg i hi) (hprime i hi)
        ((Ideal.mem_primeCompl_iff.mp ht)) (n i) htx)

private lemma ideal_finset_product
    {X : Scheme.{u}} {ι : Type v} (D : ι → X.IdealSheafData)
    (n : ι → ℕ) (s : Finset ι) (U : X.affineOpens) :
    (∏ i ∈ s, (D i) ^ n i).ideal U = ∏ i ∈ s, ((D i).ideal U) ^ n i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.prod_insert his, Finset.prod_insert his]
      simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
        Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      rw [ih]

/-- On an affine chart through the generic point of an integral `I`, the ideal of `I` becomes the
maximal ideal of the stalk at the generic point. -/
private lemma map_germ_ideal_genericPoint {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] (U : X.affineOpens)
    (hξU : I.subschemeι (_root_.genericPoint I.subscheme) ∈ U.1) :
    (I.ideal U).map (X.presheaf.germ U.1 _ hξU).hom =
      IsLocalRing.maximalIdeal
        (X.presheaf.stalk (I.subschemeι (_root_.genericPoint I.subscheme))) := by
  let x := I.subschemeι (_root_.genericPoint I.subscheme)
  let p := U.2.primeIdealOf ⟨x, hξU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hξU⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    U.2.isLocalization_stalk ⟨x, hξU⟩
  rw [ideal_eq_primeIdealOf_generic I U _ rfl hξU]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal _ _

/-- A point of the support of an integral `I` lying in an open set forces the generic point of
`I.subscheme` into that open set. -/
private lemma genericPoint_mem_of_mem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] (W : X.Opens) (x : X) (hx : x ∈ I.support) (hxW : x ∈ W) :
    I.subschemeι (_root_.genericPoint I.subscheme) ∈ W := by
  rw [← SetLike.mem_coe, ← genericPoint_support_eq] at hx
  obtain ⟨y, hyW, hy⟩ := mem_closure_iff.mp hx (W : Set X) W.isOpen hxW
  exact Set.mem_singleton_iff.mp hy ▸ hyW

private lemma ideal_le_span_pow_of_generic_order
    {X : Scheme.{u}} (Z D : X.IdealSheafData) [IsIntegral D.subscheme]
    (U : X.affineOpens) (ξ : D.subscheme)
    (hξ : ξ = _root_.genericPoint D.subscheme)
    (hξU : D.subschemeι ξ ∈ U.1) (n : ℕ)
    (horder : IdealSheafData.stalk Z (D.subschemeι ξ) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (D.subschemeι ξ)) ^ n)
    (f : Γ(X, U)) (hf : IsRegular f) (hspan : D.ideal U = Ideal.span {f}) :
    Z.ideal U ≤ Ideal.span {f} ^ n := by
  let p := U.2.primeIdealOf ⟨D.subschemeι ξ, hξU⟩
  have hpEq := ideal_eq_primeIdealOf_generic D U ξ hξ hξU
  have hprimeD := ideal_prime_of_integral_subscheme_on_affine D U
    (D.subschemeι ξ) (subschemeι_mem_support D ξ) hξU
  have hprime : (Ideal.span {f} : Ideal Γ(X, U)).IsPrime := by rwa [← hspan]
  have hpFeq : Ideal.span {f} = p.asIdeal := hspan.symm.trans hpEq
  let _ : p.asIdeal.IsPrime := p.isPrime
  let _ : Algebra (Γ(X, U)) (X.presheaf.stalk (D.subschemeι ξ)) :=
    X.presheaf.algebra_section_stalk ⟨D.subschemeι ξ, hξU⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk (D.subschemeι ξ)) p.asIdeal :=
    U.2.isLocalization_stalk ⟨D.subschemeι ξ, hξU⟩
  let _ : (Ideal.span {f} : Ideal Γ(X, U)).IsPrime := hprime
  have hcomp : (Ideal.span {f} : Ideal Γ(X, U)).primeCompl = p.asIdeal.primeCompl := by
    ext x
    change x ∉ (Ideal.span {f} : Ideal Γ(X, U)) ↔ x ∉ p.asIdeal
    rw [hpFeq]
  have hAtPrime : IsLocalization.AtPrime (X.presheaf.stalk (D.subschemeι ξ))
      (Ideal.span {f} : Ideal Γ(X, U)) := by
    change IsLocalization ((Ideal.span {f} : Ideal Γ(X, U)).primeCompl)
      (X.presheaf.stalk (D.subschemeι ξ))
    exact hcomp ▸ (show IsLocalization p.asIdeal.primeCompl
      (X.presheaf.stalk (D.subschemeι ξ)) from inferInstance)
  let _ := hAtPrime
  have hDmap : (D.ideal U).map
      (algebraMap (Γ(X, U)) (X.presheaf.stalk (D.subschemeι ξ))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (D.subschemeι ξ)) := by
    subst hξ
    exact map_germ_ideal_genericPoint D U hξU
  have hZmap : (Z.ideal U).map
      (algebraMap (Γ(X, U)) (X.presheaf.stalk (D.subschemeι ξ))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (D.subschemeι ξ)) ^ n := by
    calc
      (Z.ideal U).map
          (algebraMap (Γ(X, U)) (X.presheaf.stalk (D.subschemeι ξ))) =
          (Z.ideal U).map (X.presheaf.germ U.1 (D.subschemeι ξ) hξU).hom := rfl
      _ = IdealSheafData.stalk Z (D.subschemeι ξ) :=
        (IdealSheafData.stalk_eq_map_germ Z (D.subschemeι ξ) U hξU).symm
      _ = _ := horder
  have hspanmap : (Ideal.span {f} : Ideal Γ(X, U)).map
      (algebraMap (Γ(X, U)) (X.presheaf.stalk (D.subschemeι ξ))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (D.subschemeι ξ)) := by
    rw [← hspan, hDmap]
  intro g hg
  have hgmax : algebraMap (Γ(X, U)) (X.presheaf.stalk (D.subschemeι ξ)) g ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk (D.subschemeι ξ)) ^ n := by
    rw [← hZmap]
    exact Ideal.mem_map_of_mem _ hg
  have hgmap : algebraMap (Γ(X, U)) (X.presheaf.stalk (D.subschemeι ξ)) g ∈
      (Ideal.span {f} ^ n).map
        (algebraMap (Γ(X, U)) (X.presheaf.stalk (D.subschemeι ξ))) := by
    rw [Ideal.map_pow, hspanmap]
    exact hgmax
  exact mem_span_pow_of_mem_atPrime f g hf hprime n hgmap

private lemma exists_eq_maximalIdeal_pow_of_ne_bot
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (I : Ideal R) (hI : I ≠ ⊥) : ∃ n : ℕ, I = IsLocalRing.maximalIdeal R ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hπ
  exact ⟨n, by rw [hn, ← Ideal.span_singleton_pow, hπ.maximalIdeal_eq]⟩

private lemma exists_stalk_eq_maximalIdeal_pow_at_component
    {X : Scheme.{u}} (Z : X.IdealSheafData)
    (C : irreducibleComponents Z.subscheme) (x : X)
    (hxy : x = Z.subschemeι C.2.1.genericPoint)
    (hdom : IsDomain (X.presheaf.stalk x))
    (hdvr : IsDiscreteValuationRing (X.presheaf.stalk x)) :
    ∃ n : ℕ, n ≠ 0 ∧ IdealSheafData.stalk Z
      (Z.subschemeι C.2.1.genericPoint) =
        IsLocalRing.maximalIdeal
          (X.presheaf.stalk (Z.subschemeι C.2.1.genericPoint)) ^ n := by
  cases hxy
  have hξ : ∃ C' : irreducibleComponents Z.subscheme,
      IsGenericPoint C.2.1.genericPoint (C' : Set Z.subscheme) :=
    ⟨C, isGenericPoint_genericPoint_component C⟩
  let _ : IsDomain (X.presheaf.stalk (Z.subschemeι C.2.1.genericPoint)) := hdom
  let _ : IsDiscreteValuationRing (X.presheaf.stalk (Z.subschemeι C.2.1.genericPoint)) := hdvr
  have hneBot := stalk_ne_bot_of_generic_component Z C.2.1.genericPoint hξ
    (Z.subschemeι C.2.1.genericPoint) rfl hdom hdvr
  have hneTop := stalk_ne_top_of_mem_support Z
    (Z.subschemeι C.2.1.genericPoint) (subschemeι_mem_support Z _)
  obtain ⟨n, hn⟩ := exists_eq_maximalIdeal_pow_of_ne_bot
    (IdealSheafData.stalk Z
      (Z.subschemeι C.2.1.genericPoint)) hneBot
  exact ⟨n, fun hn0 => hneTop (by simpa [hn0] using hn), hn⟩

private lemma divisor_genericPoint_eq_of_support_eq_closure
    {X : Scheme.{u}} (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (x : X) (h : (I.support : Set X) = closure ({x} : Set X)) :
    I.subschemeι (_root_.genericPoint I.subscheme) = x := by
  have hgenI : IsGenericPoint (I.subschemeι (_root_.genericPoint I.subscheme))
      (closure ({x} : Set X)) := by
    rw [← h, ← genericPoint_support_eq I]
    rfl
  exact hgenI.eq (rfl : IsGenericPoint x (closure ({x} : Set X)))

private lemma support_eq_closure_of_codimension_one
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    [IsIntegral I.subscheme]
    (hI : IsEffectiveCartierDivisor I)
    (x : X) (hx : x ∈ I.support)
    (hcod : codimension (IrreducibleCloseds.closureSingleton x) = 1) :
    (I.support : Set X) = closure ({x} : Set X) := by
  have heq := irreducibleCloseds_eq_of_le_and_codim_one (closureSingleton_le_genericPoint I x hx)
    hcod (codimension_genericPoint_eq_one I hI)
  rw [← genericPoint_support_eq]
  exact congrArg (fun A : IrreducibleCloseds X => (A : Set X)) heq.symm

private lemma codimension_one_point_eq_divisor_support
    {X : Scheme.{u}} [IsLocallyNoetherian X] {Z : X.IdealSheafData} {Z' : Closeds X}
    {ι : Type v} (D : ι → X.IdealSheafData)
    (hD : ∀ i, IsIntegral (D i).subscheme ∧
      IsEffectiveCartierDivisor (D i))
    (hZ' : ∀ x : X, x ∈ (Z' : Set X) →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hcover : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ i, ((D i).support : Set X))
    (x : X) (hx : x ∈ (Z.support : Set X))
    (hcodim : codimension (IrreducibleCloseds.closureSingleton x) = 1) :
    ∃ i, ((D i).support : Set X) = closure ({x} : Set X) := by
  obtain ⟨i, hxi⟩ := exists_divisor_of_codimension_one_point D hZ' hcover x hx hcodim
  let _ : IsIntegral (D i).subscheme := (hD i).1
  exact ⟨i, support_eq_closure_of_codimension_one (D i) (hD i).2 x hxi hcodim⟩

private lemma exists_divisor_for_codimension_one_component
    {X : Scheme.{u}} [IsNoetherian X] (Z : X.IdealSheafData)
    {Z' : Closeds X} {ι : Type v} (D : ι → X.IdealSheafData)
    (hD : ∀ i, IsIntegral (D i).subscheme ∧
      IsEffectiveCartierDivisor (D i))
    (hZ' : ∀ x : X, x ∈ (Z' : Set X) →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hcover : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ i, ((D i).support : Set X))
    (C : irreducibleComponents Z.subscheme)
    (hC : codimension (IrreducibleCloseds.closureSingleton
      (Z.subschemeι C.2.1.genericPoint)) = 1) :
    ∃ i, ((D i).support : Set X) = closure
      ({Z.subschemeι C.2.1.genericPoint} : Set X) := by
  exact codimension_one_point_eq_divisor_support D hD hZ' hcover _
    (subschemeι_mem_support Z _) hC

private lemma point_eq_of_closure_singletons {X : Type u} [TopologicalSpace X] [T0Space X]
    {x y : X} (h : closure ({x} : Set X) = closure ({y} : Set X)) : x = y := by
  have hx : IsGenericPoint x (closure ({x} : Set X)) := rfl
  have hy : IsGenericPoint y (closure ({y} : Set X)) := rfl
  rw [h] at hx
  exact hx.eq hy

private lemma irreducibleComponent_eq_of_genericPoint_eq
    {Y : Type u} [TopologicalSpace Y] [QuasiSober Y]
    {C C' : irreducibleComponents Y}
    (h : C.2.1.genericPoint = C'.2.1.genericPoint) : C = C' := by
  exact Subtype.ext (by
    rw [← (isGenericPoint_genericPoint_component C).def,
      ← (isGenericPoint_genericPoint_component C').def, h])

private lemma exists_finset_cover_codimension_one_components
    {X : Scheme.{u}} [IsNoetherian X] (Z : X.IdealSheafData)
    {Z' : Closeds X} {ι : Type v} (D : ι → X.IdealSheafData)
    (hD : ∀ i, IsIntegral (D i).subscheme ∧
      IsEffectiveCartierDivisor (D i))
    (hZ' : ∀ x : X, x ∈ (Z' : Set X) →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hcover : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ i, ((D i).support : Set X)) :
    ∃ s : Finset ι,
      (∀ C : irreducibleComponents Z.subscheme,
        codimension (IrreducibleCloseds.closureSingleton
          (Z.subschemeι C.2.1.genericPoint)) = 1 →
        ∃ i ∈ s, ((D i).support : Set X) =
          closure ({Z.subschemeι C.2.1.genericPoint} : Set X)) ∧
      (∀ i ∈ s, ∃ C : irreducibleComponents Z.subscheme,
        codimension (IrreducibleCloseds.closureSingleton
          (Z.subschemeι C.2.1.genericPoint)) = 1 ∧
        ((D i).support : Set X) =
          closure ({Z.subschemeι C.2.1.genericPoint} : Set X)) ∧
      (∀ i ∈ s, ∀ j ∈ s,
        ((D i).support : Set X) = ((D j).support : Set X) → i = j) := by
  classical
  let Y := Z.subscheme
  let iZ : Y ⟶ X := Z.subschemeι
  have hiEmbedding : Topology.IsEmbedding iZ.base := IsPreimmersion.isEmbedding iZ
  let _ : NoetherianSpace Y := hiEmbedding.isInducing.noetherianSpace
  let K := irreducibleComponents Y
  let _ : Finite K := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let _ : Fintype K := Fintype.ofFinite K
  let good : Type u := {C : K // codimension (IrreducibleCloseds.closureSingleton
      (Z.subschemeι C.2.1.genericPoint)) = 1}
  let pick : good → ι := fun C => Classical.choose
    (exists_divisor_for_codimension_one_component Z D hD hZ' hcover C.1 C.2)
  refine ⟨Finset.univ.image pick, ?_, ?_, ?_⟩
  · intro C hC
    let C' : K := C
    let c : good := ⟨C', hC⟩
    refine ⟨pick c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa [pick, c, C'] using Classical.choose_spec
      (exists_divisor_for_codimension_one_component Z D hD hZ' hcover C' c.2)
  · intro i hi
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hi
    refine ⟨c.1, c.2, ?_⟩
    simpa [pick] using Classical.choose_spec
      (exists_divisor_for_codimension_one_component Z D hD hZ' hcover c.1 c.2)
  · intro i hi j hj hij
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hj
    have hpi : ((D (pick c)).support : Set X) =
        closure ({Z.subschemeι c.1.2.1.genericPoint} : Set X) := Classical.choose_spec
      (exists_divisor_for_codimension_one_component Z D hD hZ' hcover c.1 c.2)
    have hpj : ((D (pick c')).support : Set X) =
        closure ({Z.subschemeι c'.1.2.1.genericPoint} : Set X) := Classical.choose_spec
      (exists_divisor_for_codimension_one_component Z D hD hZ' hcover c'.1 c'.2)
    have hcl : closure ({Z.subschemeι c.1.2.1.genericPoint} : Set X) =
        closure ({Z.subschemeι c'.1.2.1.genericPoint} : Set X) := by
      calc
        _ = ((D (pick c)).support : Set X) := hpi.symm
        _ = ((D (pick c')).support : Set X) := hij
        _ = _ := hpj
    have hpoint := point_eq_of_closure_singletons hcl
    have hgeneric : c.1.2.1.genericPoint = c'.1.2.1.genericPoint :=
      Z.subschemeι.isClosedEmbedding.injective hpoint
    have hC := irreducibleComponent_eq_of_genericPoint_eq hgeneric
    exact congrArg pick (Subtype.ext hC)

private lemma finite_product_effective
    {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (D : ι → X.IdealSheafData)
    (n : ι → ℕ)
    (hD : ∀ i ∈ s, IsEffectiveCartierDivisor (D i)) :
    IsEffectiveCartierDivisor
      (∏ i ∈ s, (D i) ^ n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isEffectiveCartierDivisor_top
  | @insert i s his ih =>
      rw [Finset.prod_insert his]
      apply isEffectiveCartierDivisor_mul
      · induction n i with
        | zero => simpa using isEffectiveCartierDivisor_top
        | succ k hk =>
            rw [pow_succ]
            exact isEffectiveCartierDivisor_mul ((D i) ^ k) (D i) hk
              (hD i (Finset.mem_insert_self i s))
      · exact ih (fun j hj => hD j (Finset.mem_insert_of_mem hj))

private lemma exists_away_eq_of_equal_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] [IsLocalization p.primeCompl S]
    (I J : Ideal R) (hIJ : I ≤ J)
    (hmap : I.map (algebraMap R S) = J.map (algebraMap R S))
    (hJ : J.FG) :
    ∃ f : R, f ∉ p ∧
      I.map (algebraMap R (Localization.Away f)) =
        J.map (algebraMap R (Localization.Away f)) := by
  classical
  obtain ⟨n, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hJ
  have hgen : ∀ k : Fin n, g k ∈ J := by
    intro k
    rw [← hg]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hlocal : ∀ k : Fin n, ∃ d : R, d ∉ p ∧ d * g k ∈ I := by
    intro k
    have hmem : algebraMap R S (g k) ∈ I.map (algebraMap R S) := by
      rw [hmap]
      exact Ideal.mem_map_of_mem (algebraMap R S) (hgen k)
    obtain ⟨d, hd, hdi⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S I (g k)).mp hmem
    exact ⟨d, Ideal.mem_primeCompl_iff.mp hd, hdi⟩
  choose d hd hdi using hlocal
  let f : R := ∏ k : Fin n, d k
  have hf : f ∉ p := by
    intro hfp
    rw [Ideal.IsPrime.prod_mem_iff] at hfp
    obtain ⟨k, -, hdk⟩ := hfp
    exact hd k hdk
  have hmul : ∀ k : Fin n, f * g k ∈ I := by
    intro k
    have hprod : f = d k * ∏ j ∈ Finset.univ.erase k, d j := by
      simp [f, Finset.mul_prod_erase]
    rw [hprod]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (I.mul_mem_left (∏ j ∈ Finset.univ.erase k, d j) (hdi k))
  have hgenMap : ∀ k : Fin n,
      algebraMap R (Localization.Away f) (g k) ∈
        I.map (algebraMap R (Localization.Away f)) := by
    intro k
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers f) (Localization.Away f) I (g k)).2
    exact ⟨f, ⟨1, by simp⟩, by simpa using hmul k⟩
  have hJmap : J.map (algebraMap R (Localization.Away f)) ≤
      I.map (algebraMap R (Localization.Away f)) := by
    rw [← hg, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro z ⟨k, hk⟩
    obtain ⟨i, rfl⟩ := hk.1
    rw [← hk.2]
    exact hgenMap i
  exact ⟨f, hf, le_antisymm (Ideal.map_mono hIJ) hJmap⟩

private lemma exists_affine_neighborhood_ideal_eq_of_stalk_eq
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I J : X.IdealSheafData) (x : X)
    (hle : I ≤ J)
    (hIJ : IdealSheafData.stalk I x =
      IdealSheafData.stalk J x) :
    ∃ W : X.affineOpens, x ∈ W.1 ∧ I.ideal W = J.ideal W := by
  obtain ⟨U', hxU⟩ := exists_affineOpen_mem x
  let p : PrimeSpectrum Γ(X, U') := U'.2.primeIdealOf ⟨x, hxU⟩
  let _ : Algebra (Γ(X, U')) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal := by
    simpa [p] using U'.2.isLocalization_stalk ⟨x, hxU⟩
  have hmap : (I.ideal U').map (algebraMap (Γ(X, U')) (X.presheaf.stalk x)) =
      (J.ideal U').map (algebraMap (Γ(X, U')) (X.presheaf.stalk x)) := by
    rw [IdealSheafData.stalk_eq_map_germ I x U' hxU,
      IdealSheafData.stalk_eq_map_germ J x U' hxU] at hIJ
    exact hIJ
  have _ : IsNoetherianRing (Γ(X, U')) := IsLocallyNoetherian.component_noetherian U'
  have hJ : (J.ideal U').FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨f, hf, haway⟩ := exists_away_eq_of_equal_localization
    p.asIdeal (I.ideal U') (J.ideal U') (hle U') hmap hJ
  let W : X.affineOpens := X.affineBasicOpen (U := U') f
  have hWU : W ≤ U' := X.basicOpen_le f
  let ρ : Γ(X, U') →+* Γ(X, W) :=
    (X.presheaf.map (homOfLE (X := X.Opens) hWU).op).hom
  let _ : Algebra (Γ(X, U')) Γ(X, W) := ρ.toAlgebra
  have _ : IsLocalization.Away f Γ(X, W) := U'.2.isLocalization_of_eq_basicOpen f
    (homOfLE hWU) rfl
  let e := IsLocalization.algEquiv (.powers f) (Localization.Away f) Γ(X, W)
  have heq : (I.ideal U').map ρ = (J.ideal U').map ρ := by
    have h := congrArg (fun K : Ideal (Localization.Away f) => K.map e.toRingHom) haway
    have hcomp : e.toRingHom.comp (algebraMap (Γ(X, U')) (Localization.Away f)) = ρ := by
      ext r
      exact e.commutes r
    simpa only [Ideal.map_map, hcomp] using h
  refine ⟨W, ?_, ?_⟩
  · change x ∈ X.basicOpen f
    have hp : p ∈ PrimeSpectrum.basicOpen f :=
      (PrimeSpectrum.mem_basicOpen f p).2 hf
    have hx' : U'.2.fromSpec p ∈ X.basicOpen f := by
      change p ∈ (U'.2.fromSpec ⁻¹ᵁ X.basicOpen f)
      rw [U'.2.fromSpec_preimage_basicOpen f]
      exact hp
    simpa [p, U'.2.fromSpec_primeIdealOf ⟨x, hxU⟩] using hx'
  · rwa [← I.map_ideal hWU, ← J.map_ideal hWU]

private lemma ideal_eq_of_stalk_eq_on_affine {X : Scheme.{u}}
    (I J : X.IdealSheafData) (W : X.affineOpens)
    (h : ∀ x ∈ W.1, IdealSheafData.stalk I x =
      IdealSheafData.stalk J x) : I.ideal W = J.ideal W := by
  apply le_antisymm
  all_goals
    intro f hf
    apply W.2.mem_ideal_iff.mpr
    intro x hx
    have heq := h x hx
    rw [IdealSheafData.stalk_eq_map_germ I x W hx, IdealSheafData.stalk_eq_map_germ J x W hx] at heq
    first | rw [← heq] | rw [heq]
    exact Ideal.mem_map_of_mem _ hf

private lemma comap_eq_of_stalk_eq_on_open {X : Scheme.{u}}
    (I J : X.IdealSheafData) (U : X.Opens)
    (h : ∀ x ∈ U, IdealSheafData.stalk I x =
      IdealSheafData.stalk J x) : I.comap U.ι = J.comap U.ι := by
  ext W : 2
  rw [I.ideal_comap_of_isOpenImmersion, J.ideal_comap_of_isOpenImmersion]
  congr 1
  exact ideal_eq_of_stalk_eq_on_affine _ _ _ fun x hx =>
    h x (by simpa using U.ι.image_le_opensRange W.1 hx)

private lemma exists_open_comap_eq_of_stalk_eq_on_set {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I J : X.IdealSheafData) (hle : I ≤ J) (S : Set X)
    (hS : ∀ x ∈ S, IdealSheafData.stalk I x =
      IdealSheafData.stalk J x) :
    ∃ U : X.Opens, S ⊆ U ∧ I.comap U.ι = J.comap U.ι := by
  let V : {W : X.affineOpens // I.ideal W = J.ideal W} → X.Opens := fun W => W.1.1
  let U : X.Opens := ⨆ W, V W
  refine ⟨U, ?_, comap_eq_of_stalk_eq_on_open I J U ?_⟩
  · intro x hx
    obtain ⟨W, hxW, hW⟩ := exists_affine_neighborhood_ideal_eq_of_stalk_eq I J x hle (hS x hx)
    exact (le_iSup V ⟨W, hW⟩) hxW
  · intro x hx
    obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp hx
    rw [IdealSheafData.stalk_eq_map_germ I x W.1 hxW,
      IdealSheafData.stalk_eq_map_germ J x W.1 hxW, W.2]

private lemma exists_component_genericPoint_eq_of_codimension_one
    {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hlow : ∀ x ∈ Z.support, 1 ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (x : X) (hx : x ∈ Z.support)
    (hcod : codimension (IrreducibleCloseds.closureSingleton x) = 1) :
    ∃ C : irreducibleComponents Z.subscheme, Z.subschemeι C.2.1.genericPoint = x := by
  obtain ⟨z, rfl⟩ : x ∈ Set.range Z.subschemeι := by rwa [Z.range_subschemeι]
  let C : irreducibleComponents Z.subscheme :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  have hgen : closure ({C.2.1.genericPoint} : Set Z.subscheme) = C.1 :=
    C.2.1.isGenericPoint_genericPoint_closure.trans
      (isClosed_of_mem_irreducibleComponents C.1 C.2).closure_eq
  have hz : Z.subschemeι z ∈ closure ({Z.subschemeι C.2.1.genericPoint} : Set X) := by
    rw [← Set.image_singleton, Z.subschemeι.isClosedEmbedding.closure_image_eq, hgen]
    exact ⟨z, mem_irreducibleComponent, rfl⟩
  have hle : IrreducibleCloseds.closureSingleton (Z.subschemeι z) ≤
      IrreducibleCloseds.closureSingleton (Z.subschemeι C.2.1.genericPoint) :=
    closure_minimal (Set.singleton_subset_iff.mpr hz) isClosed_closure
  have hc : codimension (IrreducibleCloseds.closureSingleton
      (Z.subschemeι C.2.1.genericPoint)) = 1 := by
    exact le_antisymm ((codimension_antitone_of_le hle).trans_eq hcod)
      (hlow _ (subschemeι_mem_support Z _))
  exact ⟨C, point_eq_of_closure_singletons (congrArg (fun A : IrreducibleCloseds X => (A : Set X))
    (irreducibleCloseds_eq_of_le_and_codim_one hle hcod hc).symm)⟩

private lemma stalk_genericPoint_eq_maximalIdeal {X : Scheme.{u}}
    (I : X.IdealSheafData) [IsIntegral I.subscheme] :
    IdealSheafData.stalk I (I.subschemeι (_root_.genericPoint I.subscheme)) =
      IsLocalRing.maximalIdeal
        (X.presheaf.stalk (I.subschemeι (_root_.genericPoint I.subscheme))) := by
  obtain ⟨W, hxW⟩ := exists_affineOpen_mem (I.subschemeι (_root_.genericPoint I.subscheme))
  rw [IdealSheafData.stalk_eq_map_germ I _ W hxW]
  exact map_germ_ideal_genericPoint I W hxW

/-- **The ideal induced at a point by a finite product of powers of ideal sheaves** is the
corresponding product of the induced ideals. -/
public lemma stalk_finset_product {X : Scheme.{u}} {ι : Type v}
    (D : ι → X.IdealSheafData) (n : ι → ℕ) (s : Finset ι) (x : X) :
    IdealSheafData.stalk (∏ i ∈ s, (D i) ^ n i) x =
      ∏ i ∈ s, IdealSheafData.stalk (D i) x ^ n i := by
  obtain ⟨W, hxU⟩ := exists_affineOpen_mem x
  rw [IdealSheafData.stalk_eq_map_germ _ x W hxU, ideal_finset_product]
  change (Ideal.mapHom (X.presheaf.germ W.1 x hxU).hom) _ = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_pow, Ideal.mapHom_apply, IdealSheafData.stalk_eq_map_germ (D i) x W hxU]

/-- The Cartier part of a closed subscheme supported, up to codimension two,
on integral effective Cartier divisors. -/
@[stacks 0AGB "cartier_part"]
theorem exists_effectiveCartierDivisor_agree_off_codimension_two
    (X : Scheme.{u}) [IsNoetherian X] (Z : X.IdealSheafData)
    {ι : Type v} (D : ι → X.IdealSheafData) (Z' : Closeds X)
    (hD : ∀ i, IsIntegral (D i).subscheme ∧
      IsEffectiveCartierDivisor (D i))
    (hZ' : ∀ x : X, x ∈ (Z' : Set X) →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (hcover : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ i, ((D i).support : Set X)) :
    ∃ a : ι →₀ ℕ,
      let E : X.IdealSheafData := a.prod fun i n => (D i) ^ n
      IsEffectiveCartierDivisor E ∧
        Z ≤ E ∧
        ∃ U : X.Opens,
          E.comap U.ι = Z.comap U.ι ∧
          ∀ x : X, x ∈ (Z.support : Set X) → x ∉ (U : Set X) →
            (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) :=
  by
    classical
    obtain ⟨s, hsComponents, hsChosen, hsUnique⟩ :=
      exists_finset_cover_codimension_one_components Z D hD hZ' hcover
    let _ : ∀ i, IsIntegral (D i).subscheme := fun i => (hD i).1
    have hpt : ∀ i (hi : i ∈ s),
        (D i).subschemeι (_root_.genericPoint (D i).subscheme) =
          Z.subschemeι (Classical.choose (hsChosen i hi)).2.1.genericPoint := fun i hi =>
      divisor_genericPoint_eq_of_support_eq_closure (D i) _
        (Classical.choose_spec (hsChosen i hi)).2
    have horders : ∀ i (hi : i ∈ s), ∃ n : ℕ, n ≠ 0 ∧
        IdealSheafData.stalk Z
          (Z.subschemeι (Classical.choose (hsChosen i hi)).2.1.genericPoint) =
          IsLocalRing.maximalIdeal
            (X.presheaf.stalk
              (Z.subschemeι (Classical.choose (hsChosen i hi)).2.1.genericPoint)) ^ n := by
      intro i hi
      obtain ⟨hdom, hdvr⟩ := isDiscreteValuationRing_stalk_genericPoint (D i) (hD i).2
      exact exists_stalk_eq_maximalIdeal_pow_at_component Z (Classical.choose (hsChosen i hi))
        _ (hpt i hi) hdom hdvr
    let n : ι → ℕ := fun i => if hi : i ∈ s then Classical.choose (horders i hi) else 0
    have hn_support : ∀ i, n i ≠ 0 → i ∈ s := by
      intro i hni
      by_contra hi
      simp [n, hi] at hni
    let a : ι →₀ ℕ := Finsupp.onFinset s n hn_support
    let E : X.IdealSheafData := a.prod fun i k => (D i) ^ k
    have hEprod : E = ∏ i ∈ s, (D i) ^ n i := by
      dsimp [E, a]
      rw [Finsupp.prod_of_support_subset (Finsupp.onFinset s n hn_support)
        (s := s) (by simp [Finsupp.support_onFinset])]
      · rfl
      · intro i hi
        simp
    have hEff : IsEffectiveCartierDivisor E := by
      rw [hEprod]
      exact finite_product_effective s D n (fun i hi => (hD i).2)
    refine ⟨a, ?_⟩
    change IsEffectiveCartierDivisor E ∧
      Z ≤ E ∧ ∃ U : X.Opens,
        E.comap U.ι = Z.comap U.ι ∧
        ∀ x : X, x ∈ (Z.support : Set X) → x ∉ (U : Set X) →
          (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)
    have hZE : Z ≤ E := by
      apply IdealSheafData.le_of_stalk_le
      intro x
      obtain ⟨W, hxW, hgens, havoid⟩ :=
        exists_common_affine_principal_neighborhood D (fun i => (hD i).2) s x
      let t := s.filter fun i => x ∈ (D i).support
      have htSub : t ⊆ s := Finset.filter_subset _ _
      let f : ι → Γ(X, W) := fun i =>
        if hi : i ∈ t then
          Classical.choose (hgens i (htSub hi) (Finset.mem_filter.mp hi).2)
        else 1
      have hspan : ∀ i, i ∈ t → (D i).ideal W = Ideal.span {f i} := by
        intro i hi
        have h := Classical.choose_spec
          (hgens i (htSub hi) (Finset.mem_filter.mp hi).2)
        simpa [f, hi] using h.2
      have hreg : ∀ i, i ∈ t → IsRegular (f i) := by
        intro i hi
        have h := Classical.choose_spec
          (hgens i (htSub hi) (Finset.mem_filter.mp hi).2)
        simpa [f, hi] using h.1
      have htop : ∀ i, i ∈ s → i ∉ t → (D i).ideal W = ⊤ := by
        intro i hi hit
        have hxi : x ∉ (D i).support := fun hx => hit (Finset.mem_filter.mpr ⟨hi, hx⟩)
        exact ideal_top_of_support_disjoint (D i) W
          (Set.eq_empty_iff_forall_notMem.mpr fun y hy => havoid i hi hxi hy.2 hy.1)
      have hEchart : E.ideal W = ∏ i ∈ t, Ideal.span {f i} ^ n i := by
        rw [hEprod, ideal_finset_product D n s W]
        calc
          (∏ i ∈ s, ((D i).ideal W) ^ n i) =
              ∏ i ∈ t, ((D i).ideal W) ^ n i := by
            symm
            apply Finset.prod_subset htSub
            intro i hi hit
            rw [htop i hi hit]
            simp
          _ = ∏ i ∈ t, Ideal.span {f i} ^ n i := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [hspan i hi]
      have horder : ∀ i, (hi : i ∈ t) →
          IdealSheafData.stalk Z
            ((D i).subschemeι (_root_.genericPoint (D i).subscheme)) =
          IsLocalRing.maximalIdeal
            (X.presheaf.stalk ((D i).subschemeι
              (_root_.genericPoint (D i).subscheme))) ^ n i := by
        intro i hi
        rw [hpt i (htSub hi)]
        simpa [n, htSub hi] using (Classical.choose_spec (horders i (htSub hi))).2
      have hxiGeneric : ∀ i, (hi : i ∈ t) →
          (D i).subschemeι (_root_.genericPoint (D i).subscheme) ∈ W.1 := fun i hi =>
        genericPoint_mem_of_mem_support (D i) W.1 x (Finset.mem_filter.mp hi).2 hxW
      have hZpow : ∀ i, (hi : i ∈ t) →
          Z.ideal W ≤ Ideal.span {f i} ^ n i := fun i hi =>
        ideal_le_span_pow_of_generic_order Z (D i) W
          (_root_.genericPoint (D i).subscheme) rfl (hxiGeneric i hi) (n i)
          (horder i hi) (f i) (hreg i hi) (hspan i hi)
      have hprime : ∀ i, (hi : i ∈ t) →
          (Ideal.span {f i} : Ideal Γ(X, W)).IsPrime := by
        intro i hi
        rw [← hspan i hi]
        exact ideal_prime_of_integral_subscheme_on_affine (D i) W _
          (subschemeι_mem_support (D i) _) (hxiGeneric i hi)
      have hcross : ∀ i, (hi : i ∈ t) → ∀ j, (hj : j ∈ t) → i ≠ j →
          f i ^ n i ∉ Ideal.span {f j} := by
        intro i hi j hj hij hpow
        have hxjW := hxiGeneric j hj
        have hfi : f i ∈ (D j).ideal W := by
          rw [hspan j hj]
          exact (hprime j hj).mem_of_pow_mem (n i) hpow
        have hfiMax := Ideal.mem_map_of_mem (X.presheaf.germ W.1 _ hxjW).hom hfi
        rw [map_germ_ideal_genericPoint (D j) W hxjW] at hfiMax
        have hbasic : (D j).subschemeι (_root_.genericPoint (D j).subscheme) ∉
            X.basicOpen (f i) := fun hb =>
          (IsLocalRing.mem_maximalIdeal _).mp hfiMax ((Scheme.mem_basicOpen X (f i) _ hxjW).mp hb)
        have hzero : (D j).subschemeι (_root_.genericPoint (D j).subscheme) ∈
            X.zeroLocus (U := W.1) ((D i).ideal W) := by
          rw [hspan i hi, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
          exact hbasic
        have hsupport := support_eq_closure_of_codimension_one (D i) (hD i).2 _
          ((D i).mem_supportSet_iff_of_mem hxjW |>.2 hzero)
          (codimension_genericPoint_eq_one (D j) (hD j).2)
        exact hij (hsUnique i (htSub hi) j (htSub hj)
          (hsupport.trans (genericPoint_support_eq (D j))))
      have hZchart : Z.ideal W ≤ E.ideal W := by
        rw [hEchart]
        apply ideal_le_finset_product_of_atPrime_powers t f n (Z.ideal W) hreg hprime hcross
        intro i hi g hg
        refine ⟨1, ?_, ?_⟩
        · simpa using (hprime i hi).one_notMem
        · simpa using hZpow i hi hg
      rw [IdealSheafData.stalk_eq_map_germ Z x W hxW,
        IdealSheafData.stalk_eq_map_germ E x W hxW]
      exact Ideal.map_mono hZchart
    refine ⟨hEff, hZE, ?_⟩
    have hstalk : ∀ x ∈ (Z.support : Set X),
        codimension (IrreducibleCloseds.closureSingleton x) = 1 →
        IdealSheafData.stalk Z x = IdealSheafData.stalk E x := by
      intro x hx hcod
      obtain ⟨C, hCx⟩ := exists_component_genericPoint_eq_of_codimension_one Z
        (codimension_ge_one_of_mem_covered_support D hD hZ' hcover) x hx hcod
      have hCcod : codimension (IrreducibleCloseds.closureSingleton
          (Z.subschemeι C.2.1.genericPoint)) = 1 := by rwa [hCx]
      obtain ⟨i, hi, hisupport⟩ := hsComponents C hCcod
      rw [hCx] at hisupport
      have hix : (D i).subschemeι (_root_.genericPoint (D i).subscheme) = x :=
        divisor_genericPoint_eq_of_support_eq_closure (D i) x hisupport
      have hchosen : Z.subschemeι (Classical.choose (hsChosen i hi)).2.1.genericPoint = x :=
        point_eq_of_closure_singletons
          ((Classical.choose_spec (hsChosen i hi)).2.symm.trans hisupport)
      have hZorder : IdealSheafData.stalk Z x =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n i := by
        rw [← hchosen]
        simpa only [n, dite_eq_left hi] using (Classical.choose_spec (horders i hi)).2
      have hDi : IdealSheafData.stalk (D i) x =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
        rw [← hix]
        exact stalk_genericPoint_eq_maximalIdeal (D i)
      have hothers : ∀ j ∈ s, j ≠ i → IdealSheafData.stalk (D j) x = ⊤ := by
        intro j hj hji
        apply stalk_eq_top_of_notMem_support
        intro hxj
        have hjSupport := support_eq_closure_of_codimension_one (D j) (hD j).2 x hxj hcod
        exact hji (hsUnique j hj i hi (hjSupport.trans hisupport.symm))
      rw [hZorder, hEprod, stalk_finset_product]
      symm
      calc
        (∏ j ∈ s, IdealSheafData.stalk (D j) x ^ n j) =
            IdealSheafData.stalk (D i) x ^ n i := by
          apply Finset.prod_eq_single i
          · intro j hj hji
            rw [hothers j hj hji]
            simp
          · exact fun h => (h hi).elim
        _ = _ := by rw [hDi]
    obtain ⟨U, hU, hEq⟩ := exists_open_comap_eq_of_stalk_eq_on_set Z E hZE
      {x | x ∈ (Z.support : Set X) ∧
        codimension (IrreducibleCloseds.closureSingleton x) = 1}
      (fun x hx => hstalk x hx.1 hx.2)
    refine ⟨U, hEq.symm, ?_⟩
    exact codimension_ge_two_of_mem_support_outside_open D hD hZ' hcover U
      (fun x hx hcod => hU ⟨hx, hcod⟩)

/-- **An effective Cartier divisor whose support lies in that of an integral effective Cartier
divisor `D` is contained in a power of `D`, and agrees with that power on an open set containing
every codimension-one point of its support.** -/
theorem exists_le_pow_comap_eq_of_supportSet_subset {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z D : X.IdealSheafData) [IsIntegral D.subscheme]
    (hD : IsEffectiveCartierDivisor D)
    (hsub : (Z.support : Set X) ⊆ (D.support : Set X)) :
    ∃ n : ℕ, IsEffectiveCartierDivisor (D ^ n) ∧ Z ≤ D ^ n ∧
      ∃ U : X.Opens, Z.comap U.ι = (D ^ n).comap U.ι ∧
        ∀ x : X, x ∈ (Z.support : Set X) →
          codimension (IrreducibleCloseds.closureSingleton x) = 1 → x ∈ U := by
  classical
  have hstalkpow : ∀ (I : X.IdealSheafData) (m : ℕ) (x : X),
      IdealSheafData.stalk (I ^ m) x = IdealSheafData.stalk I x ^ m := fun I m x => by
    simpa using stalk_finset_product (fun _ : Unit => I) (fun _ => m) {()} x
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      IdealSheafData.stalk Z (D.subschemeι (_root_.genericPoint D.subscheme)) =
        IsLocalRing.maximalIdeal
          (X.presheaf.stalk (D.subschemeι (_root_.genericPoint D.subscheme))) ^ n := by
    by_cases hξZ : D.subschemeι (_root_.genericPoint D.subscheme) ∈ Z.support
    · obtain ⟨hdom, hdvr⟩ := isDiscreteValuationRing_stalk_genericPoint D hD
      obtain ⟨C, hC⟩ := exists_component_genericPoint_eq_of_codimension_one Z
        (fun x hx => codimension_ge_one_of_mem_integral_effective_support D hD x (hsub hx))
        _ hξZ (codimension_genericPoint_eq_one D hD)
      obtain ⟨m, -, hm⟩ := exists_stalk_eq_maximalIdeal_pow_at_component Z C _ hC.symm hdom hdvr
      rw [hC] at hm
      exact ⟨m, hm⟩
    · exact ⟨0, by
        rw [pow_zero, Ideal.one_eq_top]
        exact stalk_eq_top_of_notMem_support Z _ hξZ⟩
  have hDn : IsEffectiveCartierDivisor (D ^ n) := by
    simpa using finite_product_effective {()} (fun _ : Unit => D) (fun _ => n) fun _ _ => hD
  have hle : Z ≤ D ^ n := by
    apply IdealSheafData.le_of_stalk_le
    intro x
    by_cases hxD : x ∈ (D.support : Set X)
    · obtain ⟨W, hW, hxW, f, hf, hspan⟩ :=
        exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD x
      have hξW := genericPoint_mem_of_mem_support D W x hxD hxW
      have hchart : Z.ideal ⟨W, hW⟩ ≤ Ideal.span {f} ^ n :=
        ideal_le_span_pow_of_generic_order Z D ⟨W, hW⟩ (_root_.genericPoint D.subscheme) rfl
          hξW n hn f hf hspan
      have hpow : (D ^ n).ideal ⟨W, hW⟩ = Ideal.span {f} ^ n := by
        rw [show (D ^ n).ideal ⟨W, hW⟩ = D.ideal ⟨W, hW⟩ ^ n from rfl, hspan]
      rw [IdealSheafData.stalk_eq_map_germ Z x ⟨W, hW⟩ hxW,
        IdealSheafData.stalk_eq_map_germ (D ^ n) x ⟨W, hW⟩ hxW, hpow]
      exact Ideal.map_mono hchart
    · have hDx : IdealSheafData.stalk D x = ⊤ :=
        stalk_eq_top_of_notMem_support D x hxD
      rw [hstalkpow, hDx, Ideal.top_pow]
      exact le_top
  have hstalk : ∀ x ∈ {x : X | x ∈ (Z.support : Set X) ∧
      codimension (IrreducibleCloseds.closureSingleton x) = 1},
      IdealSheafData.stalk Z x = IdealSheafData.stalk (D ^ n) x := by
    intro x hx
    have hxD : x ∈ D.support := hsub hx.1
    have hxξ : x = D.subschemeι (_root_.genericPoint D.subscheme) :=
      point_eq_of_closure_singletons
        ((support_eq_closure_of_codimension_one D hD x hxD hx.2).symm.trans
          (genericPoint_support_eq D).symm)
    rw [hxξ, hstalkpow, stalk_genericPoint_eq_maximalIdeal D, hn]
  obtain ⟨U, hU, hUeq⟩ := exists_open_comap_eq_of_stalk_eq_on_set Z (D ^ n) hle _ hstalk
  exact ⟨n, hDn, hle, U, hUeq, fun x hx hcod => hU ⟨hx, hcod⟩⟩

end AlgebraicGeometry

end
