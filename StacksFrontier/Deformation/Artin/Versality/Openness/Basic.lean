module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct

/-!
# Openness of versality: definitions and the Artin-axioms functor

The functor of `k[s, t]`-algebras and the category of Tag 07XR, smoothness on predeformation
categories (Tag 07XS), openness of versality and its relative form (Tag 07XQ), and the
geometric criterion for the Artin-axioms functor to take its unique value.
-/

@[expose] public section

namespace Deformation.Artin

/-! ### A functor of algebras used in the Artin axioms example -/

section
open CategoryTheory

universe u v

/-- The condition defining the nonempty values of the functor in Tag 07XR.

The displayed equation says that `s`, `t`, and the finitely many `f i` generate
the unit ideal. -/
public abbrev IsAdmissible (k : Type u) [CommRing k]
    (A : Type v) [CommRing A] [Algebra (MvPolynomial (Fin 2) k) A] : Prop :=
  ∃ (n : ℕ) (f : Fin n → A) (a b : A) (g : Fin n → A),
    algebraMap (MvPolynomial (Fin 2) k) A (MvPolynomial.X 0) * a +
        algebraMap (MvPolynomial (Fin 2) k) A (MvPolynomial.X 1) * b +
        ∑ i, f i * g i = 1 ∧
      ∀ i, f i * algebraMap (MvPolynomial (Fin 2) k) A (MvPolynomial.X 0) = 0

/-- The functor which assigns a singleton to an admissible `k[s,t]`-algebra
and the empty set to every other algebra. -/
@[stacks 07XR "functor", implicit_reducible]
public def artinAxiomsFunctor (k : Type u) [Field k] :
    CommAlgCat.{v, u} (MvPolynomial (Fin 2) k) ⥤ Type v where
  obj A := ULift.{v, 0} (PLift (IsAdmissible k A))
  map {α β} φ := ↾ (fun x ↦ ⟨⟨by
    rcases x.down.down with ⟨n, f, a, b, g, hgen, hann⟩
    refine ⟨n, fun i ↦ φ (f i), φ a, φ b, fun i ↦ φ (g i), ?_, ?_⟩
    · simpa using congrArg φ hgen
    · intro i; simpa using congrArg φ (hann i)⟩⟩)
  map_id A := by ext x; exact Subsingleton.elim _ _
  map_comp φ ψ := by ext x; exact Subsingleton.elim _ _

end

/-! ### The category associated to the Artin-axioms functor -/

section
open AlgebraicGeometry CategoryTheory

universe u

/-- A scheme over `Spec k[s,t]` has an affine open cover whose coordinate rings
all satisfy the nonemptiness condition for the Artin-axioms functor. -/
public abbrev IsArtinAxiomsObject (k : Type u) [Field k]
    (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k))))
    (X : BigFppfOver B (Spec (.of (MvPolynomial (Fin 2) k))) hS) : Prop :=
  ∃ 𝒰 : Scheme.AffineOpenCover.{u, u} ((BigFppfOver.toScheme B _ hS).obj X),
    ∀ i : 𝒰.I₀,
      letI : Algebra (MvPolynomial (Fin 2) k) Γ(Spec (𝒰.X i), ⊤) :=
        ((AlgebraicGeometry.toSpecΓ (.of (MvPolynomial (Fin 2) k))) ≫
          (𝒰.f i ≫ B.inclusion.map X.hom).appTop).hom.toAlgebra
      IsAdmissible k Γ(Spec (𝒰.X i), ⊤)

/-- The full subcategory of schemes over `Spec k[s,t]` admitting an affine open
cover on which the functor of Tag 07XR has its unique value. -/
@[stacks 07XR "category"]
public abbrev artinAxiomsCategory (k : Type u) [Field k]
    (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of (MvPolynomial (Fin 2) k)))) :=
  ObjectProperty.FullSubcategory (IsArtinAxiomsObject k B hS)

end

/-! ### Smoothness on predeformation categories -/

noncomputable section
open AlgebraicGeometry CategoryTheory

universe u v₁ v₂ w₁ w₂

/-- Smoothness of the induced map on predeformation categories at every
finite-type field-valued point of the source. -/
@[stacks 07XS]
public abbrev IsSmoothOnPredeformationCategories
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v₁} [Category.{w₁} X]
    {Y : Type v₂} [Category.{w₂} Y]
    (pX : X ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS)
    (F : X ⥤ Y) (hF : F ⋙ pY = pX) : Prop :=
  let qX := pX ⋙ Over.post B.inclusion
  let qY := pY ⋙ Over.post B.inclusion
  let hF' : F ⋙ qY = qX := by
    dsimp [qX, qY]
    simpa only [Functor.assoc] using
      congrArg (fun p => p ⋙ Over.post B.inclusion) hF
  ∀ {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S)
    (x₀ : X)
    (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)),
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
    QuasiCompact
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) →
    IsOpenImmersion iΛ →
    Deformation.IsSmooth
      (mapPredeformationCategory iΛ qX qY F hF' x₀ hx₀).toBasedFunctor

end

/-! ### Openness of versality -/

noncomputable section
open AlgebraicGeometry CategoryTheory

universe u vX vY wX wY

/-- Versality of objects at finite-type points persists on an open neighbourhood. -/
@[stacks 07XQ "part (1)"]
public abbrev IsOpenVersality {S : Scheme.{u}} {X : Type vX} [Category.{wX} X]
    (q : X ⥤ Over S) (_hq : q.IsFiberedInGroupoids) : Prop :=
  ∀ (U : Over S), LocallyOfFiniteType U.hom →
    ∀ (x : X) (hx : q.obj x = U) (u₀ : U.left),
      IsFiniteTypePoint u₀ →
      IsVersalAt U q u₀ x hx →
      ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
        ∀ (u : U.left), u ∈ V.1 →
          IsFiniteTypePoint u →
          IsVersalAt U q u x hx

/-- A morphism has openness of versality if its 2-fibre product with every
scheme over a target object has openness of versality. -/
@[stacks 07XQ "part (2)"]
public noncomputable abbrev IsOpenVersalityMorphism {S : Scheme.{u}}
    {X : Type vX} [Category.{wX} X] {Y : Type vY} [Category.{wY} Y]
    (pX : X ⥤ Over S) (pY : Y ⥤ Over S) (F : X ⥤ Y)
    (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    (hF : F ⋙ pY = pX) : Prop :=
  ∀ (U : Over S), LocallyOfFiniteType U.hom →
    ∀ (y : Y) (hy : pY.obj y = U),
      let rX := pX ⋙ Over.forget S
      let rY := pY ⋙ Over.forget S
      let hrX := Functor.IsFiberedInGroupoids.comp pX (Over.forget S) hpX
        (Functor.IsFiberedInGroupoids.over_forget S)
      let hrY := Functor.IsFiberedInGroupoids.comp pY (Over.forget S) hpY
        (Functor.IsFiberedInGroupoids.over_forget S)
      letI : rY.IsFibered := hrY.isFibered
      let c := rY.chosenPullbacks
      let y' : rY.Fiber U.left :=
        ⟨y, congrArg (fun V : Over S => V.left) hy⟩
      let G := c.sliceFunctor y'
      let hG : G ⋙ rY = Over.forget U.left := c.sliceFunctor_comp y'
      let hF' : F ⋙ rY = rX := by
        dsimp [rX, rY]
        simpa only [Functor.assoc] using
          congrArg (fun p => p ⋙ Over.forget S) hF
      IsOpenVersality
        (TwoFibreProductOver.fst (Over.forget U.left) rX rY G F)
        (TwoFibreProductOver.fst_isFiberedInGroupoids U.left rX rY F G
          hrX hrY hF' hG)

end

/-! ### A geometric criterion for the Artin-axioms functor -/

section
open CategoryTheory

universe u v

private lemma exists_pow_mul_eq_zero_of_localization_eq_zero
    {R : Type v} [CommRing R] (f s : R)
    (h : ∀ x : PrimeSpectrum R, x ∈ PrimeSpectrum.basicOpen f →
      algebraMap R (Localization.AtPrime x.asIdeal) s = 0) :
    ∃ n : ℕ, f ^ n * s = 0 := by
  let J : Ideal R := (Submodule.span R ({s} : Set R)).annihilator
  have hzero : PrimeSpectrum.zeroLocus (J : Set R) ⊆
      PrimeSpectrum.zeroLocus ({f} : Set R) := by
    intro x hx
    rw [PrimeSpectrum.mem_zeroLocus] at hx ⊢
    by_contra hfx
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff x.asIdeal.primeCompl
        (Localization.AtPrime x.asIdeal) s).mp (h x (by simpa using hfx))
    have hmem : (m : R) ∈ J := by
      rw [show J = (Submodule.span R ({s} : Set R)).annihilator from rfl,
        Submodule.mem_annihilator_span_singleton]
      simpa [smul_eq_mul, mul_comm] using hm
    exact m.2 (hx hmem)
  have hrad : f ∈ J.radical := by
    apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff J (Ideal.span ({f} : Set R))).mp
      (by simpa only [PrimeSpectrum.zeroLocus_span] using hzero)
    exact Ideal.subset_span (by simp)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
  exact ⟨n, by simpa [smul_eq_mul] using
    (Submodule.mem_annihilator_span_singleton s (f ^ n)).mp hn⟩

/-- The functor of Tag 07XR has its unique value on `A` if and only if
`V(s,t) ⊆ Spec(A)` has a quasi-compact open neighbourhood on which `s`
vanishes. -/
@[stacks 07XR "geometric_criterion"]
public theorem nonempty_artinAxiomsFunctor_iff_exists_isCompact_open
    (k : Type u) [Field k]
    (A : CommAlgCat.{v, u} (MvPolynomial (Fin 2) k)) :
    Nonempty ((artinAxiomsFunctor k).obj A) ↔
      ∃ W : Set (PrimeSpectrum A),
        IsOpen W ∧ IsCompact W ∧
          PrimeSpectrum.zeroLocus
              ({algebraMap (MvPolynomial (Fin 2) k) A (MvPolynomial.X 0),
                algebraMap (MvPolynomial (Fin 2) k) A (MvPolynomial.X 1)} : Set A) ⊆ W ∧
          ∀ x ∈ W,
            algebraMap A (Localization.AtPrime x.asIdeal)
                (algebraMap (MvPolynomial (Fin 2) k) A (MvPolynomial.X 0)) = 0 := by
  classical
  let s : A := algebraMap (MvPolynomial (Fin 2) k) A (MvPolynomial.X 0)
  let t : A := algebraMap (MvPolynomial (Fin 2) k) A (MvPolynomial.X 1)
  constructor
  · rintro ⟨⟨⟨n, f, a, b, g, hgen, hann⟩⟩⟩
    let W : Set (PrimeSpectrum A) := ⋃ i, (PrimeSpectrum.basicOpen (f i) : Set _)
    refine ⟨W, ?_, ?_, ?_, ?_⟩
    · exact isOpen_iUnion fun i => PrimeSpectrum.isOpen_basicOpen
    · exact isCompact_iUnion fun i => PrimeSpectrum.isCompact_basicOpen _
    · intro x hx
      by_contra hxW
      have hst : s ∈ x.asIdeal ∧ t ∈ x.asIdeal := by
        have hV : ({s, t} : Set A) ⊆ x.asIdeal := by
          simpa [s, t] using (PrimeSpectrum.mem_zeroLocus x _).mp hx
        exact ⟨hV (by simp), hV (by simp)⟩
      have hfi : ∀ i, f i ∈ x.asIdeal := by
        intro i; by_contra hnot
        exact hxW (Set.mem_iUnion.mpr ⟨i, (PrimeSpectrum.mem_basicOpen _ _).mpr hnot⟩)
      have hsum : (s * a + t * b + ∑ i, f i * g i) ∈ x.asIdeal :=
        x.asIdeal.add_mem (x.asIdeal.add_mem (x.asIdeal.mul_mem_right a hst.1)
          (x.asIdeal.mul_mem_right b hst.2))
          (Submodule.sum_mem x.asIdeal fun i _ => x.asIdeal.mul_mem_right (g i) (hfi i))
      have hgen' : s * a + t * b + ∑ i, f i * g i = 1 := by simpa [s, t] using hgen
      exact x.2.ne_top ((Ideal.eq_top_iff_one x.asIdeal).mpr (hgen' ▸ hsum))
    · intro x hx
      rcases Set.mem_iUnion.mp (show x ∈ W from hx) with ⟨i, hi⟩
      have hloc : algebraMap A (Localization.AtPrime x.asIdeal) s = 0 := by
        apply (IsLocalization.map_eq_zero_iff x.asIdeal.primeCompl
          (Localization.AtPrime x.asIdeal) s).mpr
        refine ⟨⟨f i, ?_⟩, ?_⟩
        · simpa using (PrimeSpectrum.mem_basicOpen _ _).mp hi
        · simpa [s, mul_comm] using hann i
      simpa [s] using hloc
  · rintro ⟨W, hWopen, hWcompact, hV, hvanish⟩
    let B : Type v := {f : A // (PrimeSpectrum.basicOpen f : Set _) ⊆ W}
    have hcoverW : W ⊆ ⋃ f : B, (PrimeSpectrum.basicOpen f.1 : Set _) := by
      intro x hx
      obtain ⟨U, ⟨f, rfl⟩, hxf, hUW⟩ :=
        PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hWopen
      exact Set.mem_iUnion.mpr ⟨⟨f, hUW⟩, hxf⟩
    obtain ⟨T, hT⟩ := hWcompact.elim_finite_subcover
      (fun f : B => (PrimeSpectrum.basicOpen f.1 : Set _))
      (fun f => PrimeSpectrum.isOpen_basicOpen) hcoverW
    let ι := Fin T.card
    let pick : ι → B := fun i => (T.equivFin.symm i).1
    let f : ι → A := fun i => (pick i).1
    have hT' : W ⊆ ⋃ i : ι, (PrimeSpectrum.basicOpen (f i) : Set _) := by
      intro x hx
      rcases Set.mem_iUnion₂.mp (hT hx) with ⟨j, hj, hjx⟩
      exact Set.mem_iUnion.mpr ⟨T.equivFin ⟨j, hj⟩, by simpa [f, pick] using hjx⟩
    have hfin : ∀ i : ι, ∃ n : ℕ, f i ^ n * s = 0 := fun i =>
      exists_pow_mul_eq_zero_of_localization_eq_zero (f i) s
        (fun x hx => hvanish x ((pick i).2 hx))
    choose e he using hfin
    let g : ι → A := fun i => f i ^ e i
    have hVcover : ∀ x : PrimeSpectrum A,
        x ∈ PrimeSpectrum.zeroLocus ({s, t} : Set A) →
          ∃ i : ι, x ∈ PrimeSpectrum.basicOpen (g i) := by
      intro x hx
      rcases Set.mem_iUnion.mp (hT' (hV hx)) with ⟨i, hi⟩
      exact ⟨i, (PrimeSpectrum.le_basicOpen_pow (f i) (e i)) hi⟩
    let q : Fin 2 ⊕ ι → A := Sum.elim (fun j => if j.val = 0 then s else t) g
    have htopOpen : (⨆ z : Fin 2 ⊕ ι, PrimeSpectrum.basicOpen (q z)) = ⊤ := by
      apply le_antisymm le_top
      intro x _
      rw [TopologicalSpace.Opens.mem_iSup]
      by_cases hs : s ∉ x.asIdeal
      · exact ⟨Sum.inl 0, by simpa [q] using hs⟩
      by_cases ht : t ∉ x.asIdeal
      · exact ⟨Sum.inl 1, by simpa [q] using ht⟩
      have hxV : x ∈ PrimeSpectrum.zeroLocus ({s, t} : Set A) := by
        rw [PrimeSpectrum.mem_zeroLocus]
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · simpa using hs
        · simpa using ht
      obtain ⟨i, hi⟩ := hVcover x hxV
      exact ⟨Sum.inr i, by simpa [q] using hi⟩
    have hone : (1 : A) ∈ Ideal.span (Set.range q) := by
      rw [(PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := q)).mp htopOpen]
      exact Submodule.mem_top
    have hsubset : Set.range q ⊆ insert s (insert t (Set.range g)) := by
      rintro x ⟨z, rfl⟩
      cases z with
      | inl j => fin_cases j <;> simp [q]
      | inr i => simp [q]
    have hspan' : (1 : A) ∈ Ideal.span (insert s (insert t (Set.range g))) :=
      (Ideal.span_le.2 (fun x hx => Ideal.subset_span (hsubset hx))) hone
    rcases Ideal.mem_span_insert.mp hspan' with ⟨a, z, hz, heq⟩
    rcases Ideal.mem_span_insert.mp hz with ⟨b, z', hz', heq'⟩
    rcases (Ideal.mem_span_range_iff_exists_fun).mp hz' with ⟨c, hc⟩
    let E := Fintype.equivFin ι
    let gFin : Fin (Fintype.card ι) → A := g ∘ E.symm
    let cFin : Fin (Fintype.card ι) → A := c ∘ E.symm
    have hsumFin : (∑ i, gFin i * cFin i) = z' := by
      change (∑ i : Fin (Fintype.card ι), g (E.symm i) * c (E.symm i)) = z'
      rw [E.symm.sum_comp (fun i => g i * c i)]
      simpa only [mul_comm] using hc
    refine ⟨⟨⟨Fintype.card ι, gFin, a, b, cFin, ?_, fun i => he (E.symm i)⟩⟩⟩
    change s * a + t * b + ∑ i, gFin i * cFin i = 1
    calc
      s * a + t * b + ∑ i, gFin i * cFin i = a * s + (b * t + z') := by
        rw [mul_comm s a, mul_comm t b, hsumFin]; ring
      _ = a * s + z := by rw [← heq']
      _ = 1 := heq.symm

end

end Deformation.Artin
