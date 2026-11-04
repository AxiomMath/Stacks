module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniUniversalDivisorGenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniParameterFunctionField
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Criteria
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension
public import StacksFrontier.RingTheory.Spectrum.Prime.CodimensionHeight
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniJacobianDivisor

/-!
# A prime hypersurface through finitely many closed points

Let `R` be a domain of finite type over a field `k` with `dim R ≥ 2`, and let `s` be a finite set
of maximal ideals of `R`. Then some nonzero prime ideal of `R` is contained in every member of
`s`: through finitely many closed points of an affine variety of dimension at least two passes an
irreducible proper closed subset.

Over an algebraically closed field this is an application of the Bertini irreducibility theorem
[Stacks, Tag 0G4F] (`Stacks.Bertini.FamilyDivisors.Hypotheses.forGeneral_geometricallyIrreducible`)
to the linear system on `Spec R`, with `L = 𝒪`, spanned by generators of `I = ⋂_{m ∈ s} m` and by
`e, a e, b e`, where `e ∈ I` is nonzero, `a` and `b` lie in a maximal ideal `m₀ ∌ e`, and `b`
avoids the minimal primes of `(a)`. A minimal prime `𝔯 ⊆ m₀` of `(a, b)` has height two and does
not contain `e`, so `V(𝔯)` is a component of `H_{a e} ∩ H_{b e}` of codimension two not contained
in `H_e`; the common zero locus of the system is the finite set `s` of closed points, of
codimension `dim R ≥ 2`. A general member `g ∈ I` of the system, at a rational point of the
parameter space, cuts out an irreducible `V(g)`, and `√(g)` is the required prime. The general
case follows by an integral extension to a domain of finite type over an algebraic closure.

## Main results

* `Stacks.Bertini.FamilyDivisors.isIrreducible_divisorSet_of_geometricallyIrreducible`: for a
  coordinate tuple over the base field, geometric irreducibility of `H_v` over `k` makes the
  divisor `|H_v| ⊆ X` irreducible.
* `Stacks.Bertini.FamilyDivisors.exists_parameterPoint_mem`: over an infinite field a nonempty open
  of the parameter space `𝔸^r_k` contains a nonzero rational point.
* `Stacks.Bertini.exists_isPrime_ne_bot_le_of_isMaximal_of_isAlgClosed`: the statement over an
  algebraically closed field.
* `Stacks.Bertini.exists_isPrime_ne_bot_le_of_isMaximal`: the statement over any field.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Bertini

namespace FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-- The section `∑ᵢ cᵢ ψ(vᵢ)` of a coordinate tuple over the base field is the section of the
vector `∑ᵢ cᵢ vᵢ`. -/
theorem constCoeffSection_eq_sectionOf (c : Fin (Module.finrank D.k D.V) → D.k) :
    D.constCoeffSection c = D.sectionOf (∑ i, c i • D.basis i) := by
  rw [constCoeffSection, sectionOf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (D.sectionOf_smul (c i) (D.basis i)).symm

/-- For a coordinate tuple over the base field itself, `H_v ⊆ X_k` is the inverse image of the
divisor of `v = ∑ᵢ cᵢ vᵢ` on `X` along `X_k → X`. -/
theorem specializedDivisor_self_eq_comap (c : Fin (Module.finrank D.k D.V) → D.k) :
    D.specializedDivisor D.k c =
      (D.divisor (∑ i, c i • D.basis i)).comap (D.baseChangeToX D.k) := by
  rw [specializedDivisor,
    show D.specializedSection D.k c = pullbackGlobalSections (D.baseChangeToX D.k) D.L
      (D.constCoeffSection c) from D.specializedSection_eq_pullbackGlobalSections D.k c,
    divisor, constCoeffSection_eq_sectionOf]
  exact Divisors.zeroScheme_pullback _ _ _

/-- **A geometrically irreducible member over the base field has irreducible support.** If the
divisor `H_v` of the coordinate tuple `c` over `k` itself is geometrically irreducible over `k`,
then `|H_v| ⊆ X` is irreducible, for `v = ∑ᵢ cᵢ vᵢ`. -/
theorem isIrreducible_divisorSet_of_geometricallyIrreducible
    (c : Fin (Module.finrank D.k D.V) → D.k)
    (h : GeometricallyIrreducible
      ((D.specializedDivisor D.k c).subschemeι ≫ D.baseChangeToSpec D.k)) :
    IsIrreducible (D.divisorSet (∑ i, c i • D.basis i)) := by
  have : IrreducibleSpace (D.specializedDivisor D.k c).subscheme :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      ((D.specializedDivisor D.k c).subschemeι ≫ D.baseChangeToSpec D.k)
  have hirr : IsIrreducible (D.specializedDivisor D.k c).supportSet := by
    have := (IrreducibleSpace.isIrreducible_univ _).image _
      (D.specializedDivisor D.k c).subschemeι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.IdealSheafData.range_subschemeι] at this
  have hsupp : (D.specializedDivisor D.k c).supportSet =
      D.baseChangeToX D.k ⁻¹' D.divisorSet (∑ i, c i • D.basis i) := by
    rw [specializedDivisor_self_eq_comap]
    ext x
    simp [divisorSet]
    rfl
  have := D.isIso_baseChangeToX D.k Function.bijective_id
  rw [hsupp] at hirr
  have := hirr.image _ (D.baseChangeToX D.k).continuous.continuousOn
  rwa [Set.image_preimage_eq _ (D.baseChangeToX D.k).surjective] at this

/-- The `k`-point of `𝔸^r_k` with coordinate tuple `c` evaluates a polynomial function at `c`. -/
theorem parameterPoint_appTop_parameterBaseΓEquiv (c : Fin (Module.finrank D.k D.V) → D.k)
    (F : MvPolynomial D.basisIndex D.k) :
    (D.parameterPoint c).appTop (D.parameterBaseΓEquiv F) =
      (Scheme.ΓSpecIso (.of D.k)).inv (MvPolynomial.eval (fun i => c i.down) F) := by
  have := congrArg (fun φ : MvPolynomial D.basisIndex D.k →+* Γ(Spec (.of D.k), ⊤) => φ F)
    (MvPolynomial.ringHom_ext
      (f := (D.parameterPoint c).appTop.hom.comp D.parameterBaseΓEquiv.toRingHom)
      (g := (Scheme.ΓSpecIso (.of D.k)).inv.hom.comp (MvPolynomial.eval fun i => c i.down))
      (fun r => ?_) (fun i => ?_))
  · exact this
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, MvPolynomial.eval_C]
    rw [D.parameterBaseΓEquiv_C, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      D.parameterPoint_comp_base D.k c, D.appTop_SpecMap_algebraMap D.k r]
    rfl
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, MvPolynomial.eval_X]
    rw [D.parameterBaseΓEquiv_X, D.parameterPoint_appTop_coord D.k c i]

/-- **A nonempty open of `𝔸^r_k` has a nonzero rational point** when `k` is infinite and
`r > 0`. -/
theorem exists_parameterPoint_mem [Infinite D.k] (hr : 0 < Module.finrank D.k D.V)
    (U : D.parameterBase.Opens) (hU : (U : Set D.parameterBase).Nonempty) :
    ∃ c : Fin (Module.finrank D.k D.V) → D.k, c ≠ 0 ∧
      ∀ p : Spec (.of D.k), D.parameterPoint c p ∈ U := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨f, hfU, hxf⟩ :=
    (isAffineOpen_top D.parameterBase).exists_basicOpen_le (V := U) ⟨x, hx⟩ trivial
  set F := D.parameterBaseΓEquiv.symm f
  have hfF : f = D.parameterBaseΓEquiv F := by simp [F]
  have hF : F ≠ 0 := by
    rintro hF0
    rw [hfF, hF0, map_zero, Scheme.basicOpen_zero] at hxf
    exact hxf
  let i₀ : D.basisIndex := ⟨⟨0, hr⟩⟩
  have hG : F * MvPolynomial.X i₀ ≠ 0 := mul_ne_zero hF (MvPolynomial.X_ne_zero _)
  obtain ⟨a, ha⟩ : ∃ a : D.basisIndex → D.k, MvPolynomial.eval a (F * MvPolynomial.X i₀) ≠ 0 := by
    by_contra! h
    exact hG (MvPolynomial.funext fun a => by simp only [h a, map_zero])
  rw [map_mul, MvPolynomial.eval_X] at ha
  refine ⟨fun i => a ⟨i⟩, fun h0 => ?_, fun p => hfU ?_⟩
  · exact ha (by rw [show a i₀ = 0 from congrFun h0 ⟨0, hr⟩, mul_zero])
  · show p ∈ D.parameterPoint (fun i => a ⟨i⟩) ⁻¹ᵁ D.parameterBase.basicOpen f
    rw [Scheme.preimage_basicOpen_top, hfF, parameterPoint_appTop_parameterBaseΓEquiv,
      Scheme.basicOpen_of_isUnit]
    · trivial
    · exact ((isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul ha)).map
        (Scheme.ΓSpecIso (.of D.k)).inv.hom)

end FamilyDivisors

namespace AffineFamily

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]

/-- The structure morphism `Spec R ⟶ Spec k` of a `k`-algebra `R`. -/
abbrev structureMap : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

/-- The global sections of `𝒪_{Spec R}`, as a `k`-vector space. -/
abbrev sections : ModuleCat.{u} k :=
  globalSections k (structureMap k R)
    (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf)

/-- The identification of `R` with the global sections of `𝒪_{Spec R}`. -/
def toSections : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv

/-- A scalar of `k` acts on the global sections of `𝒪_{Spec R}` through `k → R`. -/
theorem smul_sections (c : k) (x : sections k R) :
    (show Γ(Spec (CommRingCat.of R), ⊤) from c • x) =
      toSections R (algebraMap k R c) * (show Γ(Spec (CommRingCat.of R), ⊤) from x) := by
  show (show Γ(Spec (CommRingCat.of R), ⊤) from baseRingHom k (structureMap k R) c) *
    (show Γ(Spec (CommRingCat.of R), ⊤) from x) = _
  congr 1
  show ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (structureMap k R).appTop) c =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv (algebraMap k R c)
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The identification `Γ(Spec R, ⊤) ≅ R` is semilinear over `k → R`. -/
theorem toSections_symm_smul (c : k) (x : sections k R) :
    (toSections R).symm (c • x) = algebraMap k R c * (toSections R).symm x := by
  show (toSections R).symm (show Γ(Spec (CommRingCat.of R), ⊤) from c • x) = _
  rw [smul_sections, map_mul, RingEquiv.symm_apply_apply]

/-- `𝒪_{Spec R}` is an invertible module over itself, in the spelling of
`Stacks.Bertini.FamilyDivisors`. -/
instance isInvertible_unit_spec :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible
      (Spec (CommRingCat.of R)).sheaf.obj (Spec (CommRingCat.of R)).ringCatSheaf.property
      (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) :=
  _root_.AlgebraicGeometry.SheafOfModules.isInvertible_unit _ _

variable {k R}

/-- The family of divisors on `Spec R` cut out by a finite-dimensional space `V` of functions on
`Spec R`, with `L = 𝒪_{Spec R}`. -/
abbrev family (V : Submodule k (sections k R)) [FiniteDimensional k V] :
    FamilyDivisors.{u, u} where
  k := k
  V := V
  X := Spec (CommRingCat.of R)
  toBase := structureMap k R
  L := SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf
  ψ := V.subtype
  basis := Module.finBasis k V

/-- The preimage of a point under the bijection `R → Γ(Spec R, ⊤)`. -/
theorem preimage_ΓSpecIso_inv_singleton (a : Γ(Spec (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ⁻¹' {a} =
      {(Scheme.ΓSpecIso (CommRingCat.of R)).hom a} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) y).symm
  · rintro rfl
    exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) _

/-- **The divisor of a vector of the system is a zero locus.** The support of `H_w` on
`Spec R` is `V(f)` for `f ∈ R` the function `ψ(w)`. -/
theorem divisorSet_family (V : Submodule k (sections k R)) [FiniteDimensional k V] (w : V) :
    (family V).divisorSet w =
      PrimeSpectrum.zeroLocus {(toSections R).symm (w : sections k R)} := by
  ext x
  show x ∈ (zeroScheme _ _ _).supportSet ↔ _
  rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem
      (U := ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩) trivial,
    zeroScheme_ideal_of_trivialization _ _ _ _ (LinearEquiv.refl _ _) _ rfl,
    Scheme.zeroLocus_span, Spec_zeroLocus]
  rw [preimage_ΓSpecIso_inv_singleton]
  congr! 3

/-- A prime lies in the divisor of `w` exactly when it contains the function `ψ(w)`. -/
theorem mem_divisorSet_family (V : Submodule k (sections k R)) [FiniteDimensional k V] (w : V)
    (y : PrimeSpectrum R) :
    y ∈ (family V).divisorSet w ↔ (toSections R).symm (w : sections k R) ∈ y.asIdeal := by
  rw [divisorSet_family]
  exact (PrimeSpectrum.mem_zeroLocus _ _).trans Set.singleton_subset_iff

/-- An irreducible divisor `|H_w|` is the irreducible zero locus of the principal ideal of the
function `ψ(w)`. -/
theorem isIrreducible_zeroLocus_of_divisorSet (V : Submodule k (sections k R))
    [FiniteDimensional k V] (w : V) (h : IsIrreducible ((family V).divisorSet w)) :
    IsIrreducible (PrimeSpectrum.zeroLocus
      (Ideal.span {(toSections R).symm (w : sections k R)} : Set R)) := by
  rw [divisorSet_family] at h
  rw [PrimeSpectrum.zeroLocus_span]
  exact h

/-- The function of the zero section is zero. -/
theorem toSections_symm_zero : (toSections R).symm (0 : sections k R) = 0 :=
  map_zero (toSections R).symm

/-- The images in `Γ(Spec R, ⊤)` of a set of elements of `R`, as a set of vectors of the
`k`-vector space of global sections. -/
abbrev sectionsImage (S : Set R) : Set (sections k R) := toSections R '' S

/-- A combination of the images of elements of an ideal `I` corresponds to an element of `I`. -/
theorem toSections_symm_mem {S : Set R} {I : Ideal R} (hS : S ⊆ I) {w : sections k R}
    (hw : w ∈ Submodule.span k (sectionsImage (k := k) S)) : (toSections R).symm w ∈ I := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using hS hy
  | zero =>
    convert I.zero_mem using 1
    exact map_zero (toSections R).symm
  | add x y _ _ hx hy =>
    convert I.add_mem hx hy using 1
    exact map_add (toSections R).symm x y
  | smul c x _ hx =>
    rw [toSections_symm_smul]
    exact I.mul_mem_left _ hx

/-- The prime of functions vanishing on an irreducible closed subset of `Spec R` is a point of
it. -/
theorem genericPoint_mem_irreducibleCloseds
    (W : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) :
    (⟨PrimeSpectrum.vanishingIdeal (W : Set (PrimeSpectrum R)),
      PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp W.isIrreducible⟩ :
        PrimeSpectrum R) ∈ (W : Set (PrimeSpectrum R)) := by
  have h : (W : Set (PrimeSpectrum R)) =
      PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (W : Set (PrimeSpectrum R))) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, W.isClosed.closure_eq]
  rw [Set.ext_iff] at h
  exact (h _).mpr fun _ hx => hx

end AffineFamily

open AffineFamily in
/-- **Through finitely many closed points passes a prime hypersurface, over an algebraically closed
field.** Let `R` be a domain of finite type over an algebraically closed field `k` with
`dim R ≥ 2`, and let `s` be a finite set of maximal ideals of `R`. Then some nonzero prime ideal
of `R` is contained in every member of `s`.

The prime is `√(g)` for a general member `g` of a linear system of functions in `⋂_{m ∈ s} m`,
whose zero locus is irreducible by the Bertini irreducibility theorem [Stacks, Tag 0G4F]. -/
theorem exists_isPrime_ne_bot_le_of_isMaximal_of_isAlgClosed {k R : Type u} [Field k]
    [IsAlgClosed k] [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (hdim : 2 ≤ ringKrullDim R) (s : Finset (Ideal R)) (hs : ∀ m ∈ s, m.IsMaximal) :
    ∃ P : Ideal R, P.IsPrime ∧ P ≠ ⊥ ∧ ∀ m ∈ s, P ≤ m := by
  classical
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hmax : ∀ m : Ideal R, m.IsMaximal → 2 ≤ m.height := by
    intro m hm
    have := (Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim
      k R).1 m
    rw [this] at hdim
    have h2 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (m.height : WithBot ℕ∞) := hdim
    exact WithBot.coe_le_coe.mp h2
  have hne_bot : ∀ m : Ideal R, m.IsMaximal → m ≠ ⊥ := by
    rintro m hm rfl
    have := hmax ⊥ hm
    rw [Ideal.height_bot] at this
    exact absurd this (by decide)
  -- the ideal of the finite set of closed points, and a nonzero element of it
  set I : Ideal R := s.inf id with hIdef
  obtain ⟨e, heI, he0⟩ : ∃ e ∈ I, e ≠ 0 := by
    have hprod : (∏ m ∈ s, m) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
      exact fun m hm => by rw [Ideal.zero_eq_bot]; exact hne_bot m (hs m hm)
    obtain ⟨e, he, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hprod
    exact ⟨e, Ideal.prod_le_inf he, he0⟩
  -- a closed point outside `V(e)`
  obtain ⟨m₀, hm₀, hem₀⟩ : ∃ m₀ : Ideal R, m₀.IsMaximal ∧ e ∉ m₀ := by
    have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := k)
    by_contra! h
    have hjac : e ∈ (⊥ : Ideal R).jacobson :=
      Submodule.mem_sInf.mpr fun J hJ => h J hJ.2
    rw [IsJacobsonRing.out' (⊥ : Ideal R) Ideal.isPrime_bot.isRadical] at hjac
    exact he0 hjac
  obtain ⟨a, ham₀, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne_bot m₀ hm₀)
  -- `b ∈ m₀` outside every minimal prime of `(a)`
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a})
  obtain ⟨b, hbm₀, hb⟩ : ∃ b ∈ m₀, ∀ p ∈ (Ideal.span {a}).minimalPrimes, b ∉ p := by
    by_contra! h
    have hsub : (m₀ : Set R) ⊆ ⋃ p ∈ (↑hfin.toFinset : Set (Ideal R)), (p : Set R) := by
      intro x hx
      obtain ⟨p, hp, hxp⟩ := h x hx
      exact Set.mem_biUnion (by simpa using hp) hxp
    obtain ⟨p, hp, hm₀p⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥
      (fun p hp _ _ => ((Set.Finite.mem_toFinset hfin).mp hp).isPrime)).mp hsub
    have hp' := (Set.Finite.mem_toFinset hfin).mp hp
    have hpm₀ : p = m₀ := (hm₀.eq_of_le hp'.isPrime.ne_top hm₀p).symm
    have : (Ideal.span {a}).IsPrincipal := ⟨⟨a, rfl⟩⟩
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp'
    rw [hpm₀] at h1
    exact absurd ((hmax m₀ hm₀).trans h1) (by norm_num)
  -- a minimal prime `𝔯` of `(a, b)` inside `m₀`
  obtain ⟨r, hr, hrm₀⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a, b})
    (J := m₀) (Ideal.span_le.mpr (Set.insert_subset ham₀ (Set.singleton_subset_iff.mpr hbm₀)))
  have hrprime : r.IsPrime := hr.isPrime
  have har : a ∈ r := hr.1.2 (Ideal.subset_span (by simp))
  have hbr : b ∈ r := hr.1.2 (Ideal.subset_span (by simp))
  have her : e ∉ r := fun h => hem₀ (hrm₀ h)
  have hr2 : r.height = 2 := by
    refine le_antisymm ?_ ?_
    · have := Ideal.height_le_card_of_mem_minimalPrimes_span_finset (s := {a, b})
        (p := r) (by simpa using hr)
      exact this.trans (by exact_mod_cast Finset.card_le_two)
    · obtain ⟨p, hp, hpr⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {a}) (J := r)
        (Ideal.span_le.mpr (by simpa using har))
      have := hp.isPrime
      have hap : a ∈ p := hp.1.2 (Ideal.subset_span rfl)
      have hp1 : 1 ≤ p.height := by
        rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
        rintro rfl
        exact ha0 hap
      have hlt : p.height < r.height :=
        Ideal.height_strict_mono_of_isPrime (lt_of_le_of_ne hpr (fun h => hb p hp (h ▸ hbr)))
      have := Order.add_one_le_of_lt (hp1.trans_lt hlt)
      exact this
  -- the linear system: generators of `I`, together with `e`, `a e` and `b e`
  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian I : I.FG)
  let S : Set R := ↑G ∪ {e, a * e, b * e}
  have hSI : S ⊆ I := by
    rintro x (hx | rfl | rfl | rfl)
    · rw [← hG]
      exact Ideal.subset_span hx
    · exact heI
    · exact I.mul_mem_left a heI
    · exact I.mul_mem_left b heI
  have hSfin : S.Finite := G.finite_toSet.union (by simp)
  let V : Submodule k (sections k R) := Submodule.span k (sectionsImage (k := k) S)
  have : FiniteDimensional k V := FiniteDimensional.span_of_finite k (hSfin.image _)
  let D := family V
  let vec : ∀ x ∈ S, D.V := fun x hx => ⟨toSections R x, Submodule.subset_span ⟨x, hx, rfl⟩⟩
  have hvec : ∀ x (hx : x ∈ S) (y : PrimeSpectrum R),
      y ∈ D.divisorSet (vec x hx) ↔ x ∈ y.asIdeal := by
    intro x hx y
    refine (mem_divisorSet_family V (vec x hx) y).trans ?_
    show (toSections R).symm (toSections R x) ∈ y.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply]
  have heS : e ∈ S := Or.inr (Set.mem_insert _ _)
  have haeS : a * e ∈ S := Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hbeS : b * e ∈ S := Or.inr (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  let Z : TopologicalSpace.IrreducibleCloseds D.X :=
    PrimeSpectrum.irreducibleClosedsOfPrime ⟨r, hrprime⟩
  have hrZ : (⟨r, hrprime⟩ : PrimeSpectrum R) ∈ (Z : Set D.X) := fun _ h => h
  -- hypothesis (3)
  have hZcomp : Maximal (fun W : TopologicalSpace.IrreducibleCloseds D.X =>
      (W : Set D.X) ⊆ D.divisorSet (vec (a * e) haeS) ∩ D.divisorSet (vec (b * e) hbeS)) Z := by
    refine ⟨fun x hx => ?_, fun W hW hZW => ?_⟩
    · have hrx : (r : Set R) ⊆ x.asIdeal := hx
      exact ⟨(hvec _ haeS x).mpr (x.asIdeal.mul_mem_right e (hrx har)),
        (hvec _ hbeS x).mpr (x.asIdeal.mul_mem_right e (hrx hbr))⟩
    · let W' : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) := W
      have hqprime : (PrimeSpectrum.vanishingIdeal (W' : Set (PrimeSpectrum R))).IsPrime :=
        PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp W'.isIrreducible
      have hgen := genericPoint_mem_irreducibleCloseds W'
      have hrW : (⟨r, hrprime⟩ : PrimeSpectrum R) ∈ (W' : Set (PrimeSpectrum R)) := hZW hrZ
      have hqr : PrimeSpectrum.vanishingIdeal (W' : Set (PrimeSpectrum R)) ≤ r :=
        fun f hf => (PrimeSpectrum.mem_vanishingIdeal _ _).mp hf _ hrW
      have hae := (hvec _ haeS _).mp (hW hgen).1
      have hbe := (hvec _ hbeS _).mp (hW hgen).2
      have key : ∀ x, x * e ∈ PrimeSpectrum.vanishingIdeal (W' : Set (PrimeSpectrum R)) →
          x ∈ PrimeSpectrum.vanishingIdeal (W' : Set (PrimeSpectrum R)) := fun x hx =>
        (hqprime.mem_or_mem hx).resolve_right fun h => her (hqr h)
      have hrq : r ≤ PrimeSpectrum.vanishingIdeal (W' : Set (PrimeSpectrum R)) :=
        hr.2 ⟨hqprime, Ideal.span_le.mpr (Set.insert_subset (key a hae)
          (Set.singleton_subset_iff.mpr (key b hbe)))⟩ hqr
      intro x hx
      show (r : Set R) ⊆ (x : PrimeSpectrum R).asIdeal
      intro f hf
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp (hrq hf) x hx
  have hZnot : ¬ (Z : Set D.X) ⊆ D.divisorSet (vec e heS) :=
    fun h => her ((hvec _ heS _).mp (h hrZ))
  have hZcodim : codimension Z = 2 :=
    (PrimeSpectrum.codimension_irreducibleClosedsOfPrime _).trans hr2
  -- hypothesis (4)
  have hcommon : ∀ Y : TopologicalSpace.IrreducibleCloseds D.X,
      (Y : Set D.X) ⊆ D.commonZeroSet → 2 ≤ codimension Y := by
    intro Y hY
    let Y' : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) := Y
    rw [show codimension Y = codimension Y' from rfl,
      PrimeSpectrum.codimension_eq_height_vanishingIdeal]
    have hq : (PrimeSpectrum.vanishingIdeal (Y' : Set (PrimeSpectrum R))).IsPrime :=
      PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp Y'.isIrreducible
    have hgen := genericPoint_mem_irreducibleCloseds Y'
    have hGq : I ≤ PrimeSpectrum.vanishingIdeal (Y' : Set (PrimeSpectrum R)) := by
      rw [← hG, Ideal.span_le]
      intro g hg
      exact (hvec g (Or.inl hg) _).mp
        ((D.commonZeroSet_subset_divisorSet (vec g (Or.inl hg))) (hY hgen))
    obtain ⟨m, hm, hmq⟩ := hq.inf_le'.mp hGq
    rw [← (hs m hm).eq_of_le hq.ne_top hmq]
    exact hmax m (hs m hm)
  let hyp : D.Hypotheses :=
    { locallyOfFiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
      quasiCompact := inferInstance
      geometricallyIrreducible :=
        (Algebra.isGeometricallyIrreducible_iff_irreducibleSpace_primeSpectrum k R).mpr
          inferInstance
      v₁ := vec e heS
      v₂ := vec (a * e) haeS
      v₃ := vec (b * e) hbeS
      Z := Z
      Z_component := hZcomp
      Z_not_subset := hZnot
      Z_codimension := hZcodim
      commonZeroSet_codimension := hcommon }
  -- Bertini: a general member of the linear system is irreducible
  obtain ⟨U, hUne, hU⟩ := hyp.forGeneral_geometricallyIrreducible
  have hrpos : 0 < Module.finrank k V := by
    refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨vec e heS, fun h => he0 ?_⟩
    have := congrArg (fun w : D.V => (toSections R).symm (w : sections k R)) h
    simpa [vec, toSections_symm_zero] using this
  obtain ⟨c, hc0, hcU⟩ := D.exists_parameterPoint_mem hrpos U hUne
  have hirr := D.isIrreducible_divisorSet_of_geometricallyIrreducible c (hU k c hcU c rfl)
  set w : D.V := ∑ i, c i • D.basis i with hw
  have hprime := (PrimeSpectrum.isIrreducible_zeroLocus_iff _).mp
    (isIrreducible_zeroLocus_of_divisorSet V w hirr)
  have hgI : (toSections R).symm (w : sections k R) ∈ I := toSections_symm_mem hSI w.2
  have hw0 : w ≠ 0 := by
    intro h
    apply hc0
    funext i
    exact Fintype.linearIndependent_iff.mp D.basis.linearIndependent c h i
  have hg0 : (toSections R).symm (w : sections k R) ≠ 0 := by
    intro h
    apply hw0
    apply Subtype.ext
    exact (toSections R).symm.injective (h.trans (toSections_symm_zero (k := k)).symm)
  refine ⟨_, hprime, fun h => hg0 ?_, fun m hm => ?_⟩
  · have := Ideal.le_radical
      (Ideal.mem_span_singleton_self ((toSections R).symm (w : sections k R)))
    rw [h] at this
    exact this
  · exact (hs m hm).isPrime.radical_le_iff.mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr (Finset.inf_le (f := id) hm hgI))

/-- A domain of finite type over a field `k` embeds, by an integral ring map, in a domain of
finite type over an algebraic closure of `k`: a quotient of `k̄ ⊗[k] R` by a prime lying over
`0`. -/
theorem exists_integral_extension_algebraicClosure (k R : Type u) [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] :
    ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : Algebra (AlgebraicClosure k) R'')
      (_ : Algebra.FiniteType (AlgebraicClosure k) R'') (_ : Algebra R R''),
      Algebra.IsIntegral R R'' ∧ Function.Injective (algebraMap R R'') := by
  let K := AlgebraicClosure k
  let T := TensorProduct k K R
  let : Algebra R T := Algebra.TensorProduct.rightAlgebra
  have hinj : Function.Injective (algebraMap R T) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k K).injective
  have : Algebra.IsIntegral R T := by
    refine ⟨fun x => ?_⟩
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul a r =>
      have h1 : IsIntegral k (a ⊗ₜ[k] (1 : R) : T) :=
        (Algebra.IsIntegral.isIntegral (R := k) a).map
          (Algebra.TensorProduct.includeLeft : K →ₐ[k] T)
      have h2 : (a ⊗ₜ[k] r : T) = (a ⊗ₜ[k] (1 : R)) * algebraMap R T r := by
        rw [Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul]
      rw [h2]
      exact (h1.tower_top).mul isIntegral_algebraMap
    | add x y hx hy => exact hx.add hy
  obtain ⟨Q, -, hQ, hQR⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal R)
    (⊥ : Ideal T) (by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj])
  refine ⟨T ⧸ Q, inferInstance, Ideal.Quotient.isDomain Q, inferInstance,
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K Q)
      (Ideal.Quotient.mkₐ_surjective K Q), inferInstance, inferInstance, ?_⟩
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have hx' : Ideal.Quotient.mk Q (algebraMap R T x) = 0 := hx
  have : x ∈ Q.comap (algebraMap R T) := Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hx')
  rw [hQR] at this
  exact this

/-- **Through finitely many closed points of an affine variety of dimension at least two passes
an irreducible proper closed subset.** Let `R` be a domain of finite type over a field `k` with
`dim R ≥ 2`, and let `s` be a finite set of maximal ideals of `R`. Then there is a nonzero prime
ideal of `R` contained in every member of `s`.

Over an algebraically closed field this is
`Stacks.Bertini.exists_isPrime_ne_bot_le_of_isMaximal_of_isAlgClosed`. In general, `R` embeds
integrally in a domain `R''` of finite type over an algebraic closure of `k`, of the same
dimension; the maximal ideals of `s` lift to `R''`, and the contraction of a nonzero prime of
`R''` below them is the required prime of `R`. -/
public theorem exists_isPrime_ne_bot_le_of_isMaximal {k R : Type u} [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] (hdim : 2 ≤ ringKrullDim R)
    (s : Finset (Ideal R)) (hs : ∀ m ∈ s, m.IsMaximal) :
    ∃ P : Ideal R, P.IsPrime ∧ P ≠ ⊥ ∧ ∀ m ∈ s, P ≤ m := by
  classical
  obtain ⟨R'', _, _, _, _, _, hint, hinj⟩ := exists_integral_extension_algebraicClosure k R
  have : FaithfulSMul R R'' := (faithfulSMul_iff_algebraMap_injective R R'').mpr hinj
  have hdim'' : 2 ≤ ringKrullDim R'' := by
    rw [← Algebra.IsIntegral.ringKrullDim_eq R R'']
    exact hdim
  have hker : RingHom.ker (algebraMap R R'') = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have hlift : ∀ m ∈ s, ∃ Q : Ideal R'', Q.IsMaximal ∧ Q.comap (algebraMap R R'') = m := by
    intro m hm
    have := hs m hm
    exact Ideal.exists_ideal_over_maximal_of_isIntegral m (by rw [hker]; exact bot_le)
  let lift : s → Ideal R'' := fun m => Classical.choose (hlift m.1 m.2)
  have hlift_spec : ∀ m : s, (lift m).IsMaximal ∧ (lift m).comap (algebraMap R R'') = m :=
    fun m => Classical.choose_spec (hlift m.1 m.2)
  obtain ⟨P'', hP''prime, hP''ne, hP''le⟩ :=
    exists_isPrime_ne_bot_le_of_isMaximal_of_isAlgClosed (k := AlgebraicClosure k) hdim''
      (s.attach.image lift) (by
        intro Q hQ
        obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hQ
        exact (hlift_spec m).1)
  refine ⟨P''.comap (algebraMap R R''), Ideal.comap_isPrime _ _, fun h => hP''ne
    (Ideal.eq_bot_of_comap_eq_bot h), fun m hm => ?_⟩
  exact (Ideal.comap_mono (hP''le _ (Finset.mem_image_of_mem lift
    (Finset.mem_attach s ⟨m, hm⟩)))).trans_eq (hlift_spec ⟨m, hm⟩).2

end Stacks.Bertini

end
