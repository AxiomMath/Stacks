module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SplitConicFibreComponents
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwists
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ProjHyperplane
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
public import StacksFrontier.AlgebraicGeometry.ProjQuotientChartIdeal.Basic
public import StacksFrontier.AlgebraicGeometry.HomogeneousAwayMapCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Quotient
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MatrixSubstitution

/-!
# The two lines of the special fibre of the split conic are exceptional curves

Let `R` be a discrete valuation ring with uniformizer `π` and residue field `k`, and let
`X = V(T₁T₂ - πT₀²) ⊆ ℙ²_R`. The special fibre of `X` is `C₁ + C₂`, with `C₁ = V(π, T₁)` and
`C₂ = V(π, T₂)` two copies of `ℙ¹_k` meeting transversally in the point `(1 : 0 : 0)`. Since `X_k`
is principal, `𝒪_X(C₁)|_{C₁} ≅ 𝒪_X(-C₂)|_{C₁} = 𝒪(-1)`, so `C₁` is an exceptional curve of the
first kind, and likewise `C₂`.

## Main results

* `Stacks.Models.GenusZero.comap_ker_secondLine_firstLine`: `C₂ ∩ C₁`, pulled back to `ℙ¹_k`
  along `C₁`, is the zero scheme of `S₀`, the reduced point `(0 : 1)`.
* `Stacks.Models.GenusZero.isExceptionalCurveOfFirstKind_firstLine` and
  `Stacks.Models.GenusZero.isExceptionalCurveOfFirstKind_secondLine`: the two lines are exceptional
  curves of the first kind on `X`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.Divisors (IsEffectiveCartierDivisor picardClass)

/-! ### The two lines are effective Cartier divisors with opposite classes -/

section Classes

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
  (hπ : Irreducible π)

/-- The line `C₁` is an effective Cartier divisor on `X`: it is an irreducible component of the
special fibre of the regular model `X`. -/
theorem isEffectiveCartierDivisor_ker_firstLine :
    IsEffectiveCartierDivisor (firstLine (mem_maximalIdeal_of_irreducible hπ)).ker := by
  obtain ⟨hAc, hBc, hA, hB, hcov, hAB, -⟩ := specialFibre_lines hπ
  let S := conicSituation (FractionRing R) hπ
  let Z1 : irreducibleComponents S.specialFiber :=
    ⟨_, mem_irreducibleComponents_of_union hAc hBc hA hB hcov hAB⟩
  have : IsClosedImmersion (firstLineFibre (mem_maximalIdeal_of_irreducible hπ) ≫
      pullback.fst (conicToSpec π) (residueSpecMap R)) := by
    rw [pullback.lift_fst]
    infer_instance
  have := S.isEffectiveCartierDivisor_specialFiberComponent Z1
  rwa [specialFiberComponentIdeal_eq_ker (FractionRing R) hπ _ Z1 rfl, pullback.lift_fst] at this

/-- The line `C₂` is an effective Cartier divisor on `X`. -/
theorem isEffectiveCartierDivisor_ker_secondLine :
    IsEffectiveCartierDivisor (secondLine (mem_maximalIdeal_of_irreducible hπ)).ker := by
  obtain ⟨hAc, hBc, hA, hB, hcov, -, hBA⟩ := specialFibre_lines hπ
  let S := conicSituation (FractionRing R) hπ
  let Z2 : irreducibleComponents S.specialFiber :=
    ⟨_, mem_irreducibleComponents_of_union hBc hAc hB hA ((Set.union_comm _ _).trans hcov) hBA⟩
  have : IsClosedImmersion (secondLineFibre (mem_maximalIdeal_of_irreducible hπ) ≫
      pullback.fst (conicToSpec π) (residueSpecMap R)) := by
    rw [pullback.lift_fst]
    infer_instance
  have := S.isEffectiveCartierDivisor_specialFiberComponent Z2
  rwa [specialFiberComponentIdeal_eq_ker (FractionRing R) hπ _ Z2 rfl, pullback.lift_fst] at this

/-- **`𝒪_X(C₁) ⊗ 𝒪_X(C₂)` is trivial**: `C₁ + C₂ = X_k` is cut out by the uniformizer. -/
theorem picardClass_ker_firstLine_add_secondLine :
    haveI := isEffectiveCartierDivisor_ker_firstLine hπ
    haveI := isEffectiveCartierDivisor_ker_secondLine hπ
    picardClass (firstLine (mem_maximalIdeal_of_irreducible hπ)).ker +
      picardClass (secondLine (mem_maximalIdeal_of_irreducible hπ)).ker = 0 := by
  have := isEffectiveCartierDivisor_ker_firstLine hπ
  have := isEffectiveCartierDivisor_ker_secondLine hπ
  rw [← Stacks.Divisors.picardClass_mul]
  refine Eq.trans ?_ (picardClass_specialFiberIdeal (conicSituation (FractionRing R) hπ))
  exact @Stacks.Divisors.picardClass_congr _ _ _
    (specialFiberIdeal_eq_mul (FractionRing R) hπ).symm _
    (Stacks.Models.isEffectiveCartierDivisor_specialFiberIdeal
      (conicSituation (FractionRing R) hπ).toRegularModelSituation)

end Classes


/-! ### Chart functions and `Proj.map` -/

section Charts

open AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

/-- `Proj.map f` carries the chart function `b / s ^ n` on `D₊(s)` to the chart function
`f b / f s ^ n` on `D₊(f s)`. -/
theorem appLE_map_chartFraction {s : A} {i : ℕ} (hs : s ∈ 𝒜 i) (n : ℕ) (b : 𝒜 (n • i))
    (hle : Proj.basicOpen ℬ (f s) ≤ Proj.map f hf ⁻¹ᵁ Proj.basicOpen 𝒜 s) :
    ((Proj.map f hf).appLE (Proj.basicOpen 𝒜 s) (Proj.basicOpen ℬ (f s)) hle).hom
        (chartFraction 𝒜 hs n b) =
      chartFraction ℬ (f.map_mem hs) n ⟨f b, f.map_mem b.2⟩ := by
  have h := congrArg (fun φ => φ.hom (Away.mk 𝒜 hs n (b : A) b.2))
    (Proj.awayToSection_comp_appLE f hf hs)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk] at h
  exact h

/-- A chart function `b / s ^ n` with `f b = 0` vanishes on `Proj ℬ`: it lies in the ideal of the
closed immersion `Proj.map f` over `D₊(s)`. -/
theorem chartFraction_mem_ker_map [IsClosedImmersion (Proj.map f hf)] {s : A} {i : ℕ}
    (hs : s ∈ 𝒜 i) (hi : 0 < i) (n : ℕ)
    (b : 𝒜 (n • i)) (hb : f b = 0) :
    chartFraction 𝒜 hs n b ∈ (Proj.map f hf).ker.ideal
      ⟨Proj.basicOpen 𝒜 s, Proj.isAffineOpen_basicOpen 𝒜 s hs hi⟩ := by
  refine (congrArg (fun I => chartFraction 𝒜 hs n b ∈ I)
    (AlgebraicGeometry.Scheme.Hom.ker_apply (Proj.map f hf)
      ⟨Proj.basicOpen 𝒜 s, Proj.isAffineOpen_basicOpen 𝒜 s hs hi⟩)).mpr ?_
  refine (Stacks.ProjQuotientChartIdeal.awayToSection_mem_ker_app_projMap_iff f hf hs hi _).mpr ?_
  refine (Stacks.AlgebraicGeometry.HomogeneousAwayMap.awayMk_mem_ker_awayMap_iff f hs n _ _).mpr
    ⟨0, ?_⟩
  rwa [pow_zero, one_mul, RingHom.mem_ker]

end Charts


/-! ### The points of `ℙ¹_k` cut out by the coordinates -/

section LinePoint

open AlgebraicGeometry.ProjectiveSpectrum.Proj

/-- `k[S₀, S₁]` is generated in degree one. -/
theorem adjoin_lineGrading (k : Type u) [Field k] :
    Algebra.adjoin (lineGrading k 0) (lineGrading k 1 : Set (MvPolynomial (Fin (1 + 1)) k)) = ⊤ :=
  MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (1 + 1)) k

/-- The twisting sheaves of `ℙ¹_k` are invertible. -/
instance isInvertible_twistingSheafModule_lineGrading (k : Type u) [Field k] (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj (lineGrading k)).sheaf.obj
      (AlgebraicGeometry.Proj (lineGrading k)).ringCatSheaf.property
      (twistingSheafModule (lineGrading k) (n : ℤ)) :=
  algebraicGeometry_isInvertible_twistingSheaf _ (adjoin_lineGrading k) _

/-- **The point `V(Sⱼ)` of `ℙ¹_k`**: the zero scheme of the section `Sⱼ` of `𝒪(1)`. -/
abbrev linePoint (k : Type u) [Field k] (j : Fin (1 + 1)) :
    (AlgebraicGeometry.Proj (lineGrading k)).IdealSheafData :=
  Stacks.Divisors.zeroScheme (AlgebraicGeometry.Proj (lineGrading k))
    (twistingSheafModule (lineGrading k) ((1 : ℕ) : ℤ))
    (degreeSection (lineGrading k) 1 ⟨X j, X_mem k j⟩)

/-- On the chart `D₊(g)`, the point `V(Sⱼ)` is cut out by `Sⱼ / g`. -/
theorem linePoint_ideal_basicOpen (k : Type u) [Field k] (j : Fin (1 + 1))
    {g : MvPolynomial (Fin (1 + 1)) k} (hg : g ∈ lineGrading k 1) :
    (linePoint k j).ideal ⟨Proj.basicOpen _ g, Proj.isAffineOpen_basicOpen _ g hg one_pos⟩ =
      Ideal.span {chartFraction (lineGrading k) hg 1 ⟨X j, by simpa using X_mem k j⟩} :=
  zeroScheme_degreeSection_ideal_basicOpen (lineGrading k) hg one_pos 1 ⟨X j, _⟩

/-- The point `V(Sⱼ)` is an effective Cartier divisor on `ℙ¹_k`. -/
instance isEffectiveCartierDivisor_linePoint (k : Type u) [Field k] (j : Fin (1 + 1)) :
    IsEffectiveCartierDivisor (linePoint k j) :=
  Stacks.Chow.GenuineChern.isEffectiveCartierDivisor_zeroScheme_degreeSection (lineGrading k)
    (adjoin_lineGrading k) ⟨X j, X_mem k j⟩
    (isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero (X_ne_zero j)))

end LinePoint

/-! ### The line `C₂` cuts `C₁` in a reduced point -/

section Meet

open AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {R : Type u} [CommRing R] [IsLocalRing R] {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R)

local notation "κ" => IsLocalRing.ResidueField R

/-- On a chart `D₊(φ s)`, the reduced point `V(Sⱼ)` contains the pullback along `Proj.map φ` of
the kernel of `Proj.map ψ`, if some coordinate `Tᵢ` goes to `Sⱼ` under `φ` and to `0` under `ψ`. -/
private theorem linePoint_ideal_le_comap_ker_map {φ ψ : conicGrading π →+*ᵍ lineGrading κ}
    (hφ : HomogeneousIdeal.irrelevant (lineGrading κ) ≤
      (HomogeneousIdeal.irrelevant (conicGrading π)).map φ)
    (hψ : HomogeneousIdeal.irrelevant (lineGrading κ) ≤
      (HomogeneousIdeal.irrelevant (conicGrading π)).map ψ) (hψs : Function.Surjective ψ)
    {s : MvPolynomial (Fin 3) R ⧸ conicIdeal π} (hs : s ∈ conicGrading π 1)
    {g : MvPolynomial (Fin (1 + 1)) κ} (hg : g ∈ lineGrading κ 1) (hsg : φ s = g)
    (j : Fin (1 + 1)) (c : Fin 3) (hφc : φ (conicCoord π c) = X j) (hψc : ψ (conicCoord π c) = 0) :
    (linePoint κ j).ideal ⟨Proj.basicOpen _ g, Proj.isAffineOpen_basicOpen _ g hg one_pos⟩ ≤
      ((Proj.map ψ hψ).ker.comap (Proj.map φ hφ)).ideal
        ⟨Proj.basicOpen _ g, Proj.isAffineOpen_basicOpen _ g hg one_pos⟩ := by
  have := Proj.isClosedImmersion_map_of_surjective' ψ hψs
  subst hsg
  rw [linePoint_ideal_basicOpen κ j hg, Ideal.span_le, Set.singleton_subset_iff]
  have hE := Stacks.IdealSheaf.ideal_comap_appLE (Proj.map ψ hψ).ker (Proj.map φ hφ)
    ⟨Proj.basicOpen _ s, Proj.isAffineOpen_basicOpen _ s hs one_pos⟩
    ⟨Proj.basicOpen _ _, Proj.isAffineOpen_basicOpen _ _ hg one_pos⟩ le_rfl
  refine (congrArg (fun I => _ ∈ I) hE).mpr ?_
  have h2 : (conicCoord π c : MvPolynomial (Fin 3) R ⧸ conicIdeal π) ∈ conicGrading π (1 • 1) := by
    simpa using conicCoord_mem π c
  have hmem := chartFraction_mem_ker_map ψ hψ hs one_pos 1 ⟨_, h2⟩ (by simpa using hψc)
  have himg := Ideal.mem_map_of_mem ((Proj.map φ hφ).appLE (Proj.basicOpen _ s)
    (Proj.basicOpen _ _) le_rfl).hom hmem
  have hval := appLE_map_chartFraction φ hφ hs 1 ⟨_, h2⟩ le_rfl
  have heq : chartFraction (lineGrading κ) hg 1 ⟨X j, by simpa using X_mem κ j⟩ =
      chartFraction (lineGrading κ) hg 1 ⟨φ (conicCoord π c), φ.map_mem h2⟩ := by
    congr 2
    exact hφc.symm
  rwa [heq.trans hval.symm]

/-- On a chart `D₊(f₁ s)` of `C₁`, the reduced point `V(S₀)` contains `C₂ ∩ C₁`. -/
theorem linePoint_ideal_le_comap_secondLine_firstLine {s : MvPolynomial (Fin 3) R ⧸ conicIdeal π}
    (hs : s ∈ conicGrading π 1) {g : MvPolynomial (Fin (1 + 1)) κ} (hg : g ∈ lineGrading κ 1)
    (hsg : lineHom π _ (firstLine_rel hπ) firstLine_lin s = g) :
    (linePoint κ 0).ideal ⟨Proj.basicOpen _ g, Proj.isAffineOpen_basicOpen _ g hg one_pos⟩ ≤
      ((secondLine hπ).ker.comap (firstLine hπ)).ideal
        ⟨Proj.basicOpen _ g, Proj.isAffineOpen_basicOpen _ g hg one_pos⟩ :=
  linePoint_ideal_le_comap_ker_map _ _ (surjective_lineHom π _ _ _ 0 1 rfl rfl) hs hg hsg 0 2
    (by simp) (by simp)

/-- On a chart `D₊(f₂ s)` of `C₂`, the reduced point `V(S₁)` contains `C₁ ∩ C₂`. -/
theorem linePoint_ideal_le_comap_firstLine_secondLine {s : MvPolynomial (Fin 3) R ⧸ conicIdeal π}
    (hs : s ∈ conicGrading π 1) {g : MvPolynomial (Fin (1 + 1)) κ} (hg : g ∈ lineGrading κ 1)
    (hsg : lineHom π _ (secondLine_rel hπ) secondLine_lin s = g) :
    (linePoint κ 1).ideal ⟨Proj.basicOpen _ g, Proj.isAffineOpen_basicOpen _ g hg one_pos⟩ ≤
      ((firstLine hπ).ker.comap (secondLine hπ)).ideal
        ⟨Proj.basicOpen _ g, Proj.isAffineOpen_basicOpen _ g hg one_pos⟩ :=
  linePoint_ideal_le_comap_ker_map _ _ (surjective_lineHom π _ _ _ 2 0 rfl rfl) hs hg hsg 1 1
    (by simp) (by simp)

end Meet


/-! ### The point `V(Sⱼ)` as a closed subscheme -/

section PointQuotient

open AlgebraicGeometry.ProjectiveSpectrum.Proj

variable (k : Type u) [Field k] (j : Fin (1 + 1))

/-- The homogeneous ideal `(Sⱼ)` of `k[S₀, S₁]`. -/
def pointIdeal : HomogeneousIdeal (lineGrading k) where
  toSubmodule := Ideal.span {X j}
  is_homogeneous' := Ideal.homogeneous_span _ _ <| by
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨1, hx ▸ X_mem k j⟩

/-- The graded quotient map `k[S₀, S₁] ⟶ k[S₀, S₁]/(Sⱼ)`. -/
abbrev pointQuotient := Stacks.HomogeneousIdeal.quotientMk (pointIdeal k j)

/-- The quotient map `k[S₀, S₁] ⟶ k[S₀, S₁]/(Sⱼ)` induces a morphism of `Proj`s. -/
theorem irrelevant_le_pointQuotient :
    HomogeneousIdeal.irrelevant (Stacks.HomogeneousIdeal.quotientGrading (pointIdeal k j)) ≤
      (HomogeneousIdeal.irrelevant (lineGrading k)).map (pointQuotient k j) :=
  Proj.irrelevant_le_map_of_surjective _ (Stacks.HomogeneousIdeal.surjective_quotientMk _)

/-- **The point `V(Sⱼ)` is the closed subscheme `Proj k[S₀, S₁]/(Sⱼ)` of `ℙ¹_k`.** -/
theorem linePoint_eq_ker :
    linePoint k j = (Proj.map (pointQuotient k j) (irrelevant_le_pointQuotient k j)).ker :=
  Stacks.Chow.GenuineChern.zeroScheme_degreeSection_eq_ker_projMap (lineGrading k) _
    (adjoin_lineGrading k) (pointQuotient k j) (irrelevant_le_pointQuotient k j)
    (Stacks.HomogeneousIdeal.surjective_quotientMk _) ⟨X j, X_mem k j⟩
    (Ideal.mk_ker (I := (pointIdeal k j).toIdeal))

end PointQuotient

section MapComp

variable {A B B' C σ τ τ' υ : Type u} [CommRing A] [CommRing B] [CommRing B'] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike τ' B'] [AddSubgroupClass τ' B'] [SetLike υ C] [AddSubgroupClass υ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {ℬ' : ℕ → τ'} {𝒞 : ℕ → υ} [GradedRing 𝒜] [GradedRing ℬ]
  [GradedRing ℬ'] [GradedRing 𝒞]

/-- Two composites of morphisms `Proj.map` agree when the composites of the graded ring maps do. -/
theorem map_comp_map_eq (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (f' : 𝒜 →+*ᵍ ℬ') (g' : ℬ' →+*ᵍ 𝒞)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hf' : HomogeneousIdeal.irrelevant ℬ' ≤ (HomogeneousIdeal.irrelevant 𝒜).map f')
    (hg' : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ').map g')
    (h : g.comp f = g'.comp f') :
    Proj.map g hg ≫ Proj.map f hf = Proj.map g' hg' ≫ Proj.map f' hf' := by
  have key : ∀ (φ φ' : 𝒜 →+*ᵍ 𝒞) (hφ : HomogeneousIdeal.irrelevant 𝒞 ≤
      (HomogeneousIdeal.irrelevant 𝒜).map φ) (hφ' : HomogeneousIdeal.irrelevant 𝒞 ≤
      (HomogeneousIdeal.irrelevant 𝒜).map φ'), φ = φ' → Proj.map φ hφ = Proj.map φ' hφ' := by
    rintro _ _ _ _ rfl
    rfl
  rw [← Proj.map_comp, ← Proj.map_comp]
  exact key _ _ _ _ h

end MapComp


/-! ### `C₂ ∩ C₁` is the reduced point `V(S₀)` of `C₁` -/

section MeetEq

open AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {R : Type u} [CommRing R] [IsLocalRing R] {π : R} (hπ : π ∈ IsLocalRing.maximalIdeal R)

local notation "κ" => IsLocalRing.ResidueField R

/-- If `V(Sⱼ)` receives `Proj.map φ` through `Proj.map ψ` and a graded endomorphism `σ` of
`k[S₀, S₁]`, then the pullback along `Proj.map φ` of the kernel of `Proj.map ψ` lies in `V(Sⱼ)`. -/
private theorem comap_ker_map_le_linePoint {φ ψ : conicGrading π →+*ᵍ lineGrading κ}
    (hφ : HomogeneousIdeal.irrelevant (lineGrading κ) ≤
      (HomogeneousIdeal.irrelevant (conicGrading π)).map φ)
    (hψ : HomogeneousIdeal.irrelevant (lineGrading κ) ≤
      (HomogeneousIdeal.irrelevant (conicGrading π)).map ψ) (hφs : Function.Surjective φ)
    (j : Fin (1 + 1)) (σ : lineGrading κ →+*ᵍ lineGrading κ)
    (hcomp : (pointQuotient κ j).comp φ = ((pointQuotient κ j).comp σ).comp ψ) :
    (Proj.map ψ hψ).ker.comap (Proj.map φ hφ) ≤ linePoint κ j := by
  have hsurj : Function.Surjective ((pointQuotient κ j).comp σ) := by
    intro y
    obtain ⟨x, hx⟩ := (Stacks.HomogeneousIdeal.surjective_quotientMk (pointIdeal κ j)).comp hφs y
    refine ⟨ψ x, ?_⟩
    rwa [← GradedRingHom.comp_apply, ← hcomp, GradedRingHom.comp_apply]
  have hsq := map_comp_map_eq φ (pointQuotient κ j) ψ ((pointQuotient κ j).comp σ) hφ
    (irrelevant_le_pointQuotient κ j) hψ (Proj.irrelevant_le_map_of_surjective _ hsurj) hcomp
  rw [linePoint_eq_ker, ← Scheme.IdealSheafData.le_map_iff_comap_le,
    Scheme.IdealSheafData.map_ker, hsq]
  exact Scheme.Hom.le_ker_comp _ _

/-- The point `V(S₀)` of `C₁` contains `C₂ ∩ C₁`. -/
theorem linePoint_le_comap_secondLine_firstLine :
    linePoint κ 0 ≤ (secondLine hπ).ker.comap (firstLine hπ) := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun i : Fin (1 + 1) =>
    ⟨Proj.basicOpen _ (X i), Proj.isAffineOpen_basicOpen _ _ (X_mem κ i) one_pos⟩)
    (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top κ 1) fun i => ?_
  fin_cases i
  · exact linePoint_ideal_le_comap_secondLine_firstLine hπ (conicCoord_mem π 2) (X_mem κ 0)
      (by simp)
  · exact linePoint_ideal_le_comap_secondLine_firstLine hπ (conicCoord_mem π 0) (X_mem κ 1)
      (by simp)

/-- `C₂ ∩ C₁` contains the point `V(S₀)` of `C₁`: the composite of `V(S₀) ⟶ C₁ ⟶ X` factors
through `C₂`. -/
theorem comap_secondLine_firstLine_le :
    (secondLine hπ).ker.comap (firstLine hπ) ≤ linePoint κ 0 := by
  let σ0 := matrixSubstGradedHom κ 1 !![0, 0; 1, 0]
  refine comap_ker_map_le_linePoint _ _ (surjective_lineHom π _ _ _ 2 0 rfl rfl) 0 σ0 ?_
  apply GradedRingHom.coe_ringHom_injective
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
  · simp [σ0, matrixSubstGradedHom_C]
  · have h0 : Ideal.Quotient.mk (pointIdeal κ 0).toIdeal (X 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    fin_cases i <;> simp [σ0, matrixSubstGradedHom_X, Fin.sum_univ_two, h0]

/-- **`C₂ ∩ C₁`, read on `C₁ = ℙ¹_k`, is the reduced point `V(S₀)`**: the two lines meet
transversally. -/
theorem comap_ker_secondLine_firstLine :
    (secondLine hπ).ker.comap (firstLine hπ) = linePoint κ 0 :=
  le_antisymm (comap_secondLine_firstLine_le hπ) (linePoint_le_comap_secondLine_firstLine hπ)

/-- The point `V(S₁)` of `C₂` contains `C₁ ∩ C₂`. -/
theorem linePoint_le_comap_firstLine_secondLine :
    linePoint κ 1 ≤ (firstLine hπ).ker.comap (secondLine hπ) := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun i : Fin (1 + 1) =>
    ⟨Proj.basicOpen _ (X i), Proj.isAffineOpen_basicOpen _ _ (X_mem κ i) one_pos⟩)
    (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top κ 1) fun i => ?_
  fin_cases i
  · exact linePoint_ideal_le_comap_firstLine_secondLine hπ (conicCoord_mem π 0) (X_mem κ 0)
      (by simp)
  · exact linePoint_ideal_le_comap_firstLine_secondLine hπ (conicCoord_mem π 1) (X_mem κ 1)
      (by simp)

/-- `C₁ ∩ C₂` contains the point `V(S₁)` of `C₂`. -/
theorem comap_firstLine_secondLine_le :
    (firstLine hπ).ker.comap (secondLine hπ) ≤ linePoint κ 1 := by
  let σ1 := matrixSubstGradedHom κ 1 !![0, 1; 0, 0]
  refine comap_ker_map_le_linePoint _ _ (surjective_lineHom π _ _ _ 0 1 rfl rfl) 1 σ1 ?_
  apply GradedRingHom.coe_ringHom_injective
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_))
  · simp [σ1, matrixSubstGradedHom_C]
  · have h1 : Ideal.Quotient.mk (pointIdeal κ 1).toIdeal (X 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    fin_cases i <;> simp [σ1, matrixSubstGradedHom_X, Fin.sum_univ_two, h1]

/-- **`C₁ ∩ C₂`, read on `C₂ = ℙ¹_k`, is the reduced point `V(S₁)`.** -/
theorem comap_ker_firstLine_secondLine :
    (firstLine hπ).ker.comap (secondLine hπ) = linePoint κ 1 :=
  le_antisymm (comap_firstLine_secondLine_le hπ) (linePoint_le_comap_firstLine_secondLine hπ)

end MeetEq


/-! ### The two lines are exceptional curves of the first kind -/

section Exceptional

open Stacks.Picard (schemePullbackClass schemePullbackClassHom)

/-- **The class of `𝒪(D)` pulls back to the class of `𝒪(f⁻¹D)`** along every morphism along
which the pullback of the effective Cartier divisor `D` is defined. -/
theorem schemePullbackClass_picardClass_of_isPullbackDefined {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] [Stacks.Divisors.IsPullbackDefined f D] :
    haveI : IsEffectiveCartierDivisor (D.comap f) := ‹Stacks.Divisors.IsPullbackDefined f D›
    schemePullbackClass f (picardClass D) = picardClass (D.comap f) := by
  refine (Stacks.Picard.pullbackClass_classOf f.toLRSHom.toShHom
    (Stacks.Divisors.invertibleSheaf' D)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)).trans ?_
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard (D.comap f))).2
      ⟨Stacks.Divisors.invertibleSheafPullbackIso f D⟩

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
  (hπ : Irreducible π)

local notation "κ" => IsLocalRing.ResidueField R

/-- The point `V(Sⱼ)` of `ℙ¹_k` has the class of `𝒪(1)`. -/
theorem picardClass_linePoint (j : Fin (1 + 1)) :
    picardClass (linePoint κ j) = twistingSheafPicardClass κ 1 :=
  AlgebraicGeometry.picardClass_zeroScheme _ (isInvertible_twistingSheaf_projectiveLineProj κ 1) _

/-- If `D + D'` is principal and `f : ℙ¹_k ⟶ X` pulls `D'` back to the point `V(Sⱼ)`, then `𝒪(D)`
pulls back to `𝒪(-1)` along `f`. -/
private theorem schemePullbackClass_picardClass_eq_neg_one {X : Scheme.{u}}
    (f : AlgebraicGeometry.Proj (lineGrading κ) ⟶ X) (D D' : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D']
    (hsum : picardClass D + picardClass D' = 0) (j : Fin (1 + 1))
    (hf : D'.comap f = linePoint κ j) :
    schemePullbackClass f (picardClass D) = twistingSheafPicardClass κ (-1) := by
  have : Stacks.Divisors.IsPullbackDefined f D' := by
    change IsEffectiveCartierDivisor (D'.comap f)
    rw [hf]
    infer_instance
  have h2 := (schemePullbackClass_picardClass_of_isPullbackDefined f D').trans
    ((Stacks.Divisors.picardClass_congr hf).trans (picardClass_linePoint j))
  rw [eq_neg_of_add_eq_zero_left hsum,
    show schemePullbackClass f (-picardClass D') = -schemePullbackClass f (picardClass D') from
      map_neg (schemePullbackClassHom f) _,
    h2, twistingSheafPicardClass_eq_zsmul κ (-1), neg_one_zsmul]

/-- The identification of `ℙ¹_k` with the line `C₁ ⊆ X`. -/
abbrev firstLineIso : projectiveLineProj κ ≅
    (firstLine (mem_maximalIdeal_of_irreducible hπ)).ker.subscheme :=
  asIso (firstLine (mem_maximalIdeal_of_irreducible hπ)).toImage

/-- The identification of `ℙ¹_k` with the line `C₂ ⊆ X`. -/
abbrev secondLineIso : projectiveLineProj κ ≅
    (secondLine (mem_maximalIdeal_of_irreducible hπ)).ker.subscheme :=
  asIso (secondLine (mem_maximalIdeal_of_irreducible hπ)).toImage

/-- **The line `C₁ = V(π, T₁)` is an exceptional curve of the first kind on `X`**: it is a copy of
`ℙ¹_k`, an effective Cartier divisor, and `𝒪_X(C₁)|_{C₁} = 𝒪_X(-C₂)|_{C₁} = 𝒪(-1)`, since
`C₁ + C₂ = X_k` is principal and `C₂` meets `C₁` transversally in one rational point. -/
theorem isExceptionalCurveOfFirstKind_firstLine :
    (firstLine (mem_maximalIdeal_of_irreducible hπ)).ker.IsExceptionalCurveOfFirstKind κ
      (firstLineIso hπ) := by
  have := isEffectiveCartierDivisor_ker_firstLine hπ
  have := isEffectiveCartierDivisor_ker_secondLine hπ
  rw [Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_iff_pullbackPicardClass]
  show schemePullbackClass (firstLineIso hπ).hom
    (schemePullbackClass (firstLine _).ker.subschemeι (picardClass _)) = _
  rw [Stacks.Picard.schemePullbackClass_comp, asIso_hom, Scheme.Hom.toImage_imageι]
  exact schemePullbackClass_picardClass_eq_neg_one _ _ (secondLine _).ker
    (picardClass_ker_firstLine_add_secondLine hπ) 0 (comap_ker_secondLine_firstLine _)

/-- **The line `C₂ = V(π, T₂)` is an exceptional curve of the first kind on `X`**: it is a copy of
`ℙ¹_k`, an effective Cartier divisor, and `𝒪_X(C₂)|_{C₂} = 𝒪_X(-C₁)|_{C₂} = 𝒪(-1)`. -/
theorem isExceptionalCurveOfFirstKind_secondLine :
    (secondLine (mem_maximalIdeal_of_irreducible hπ)).ker.IsExceptionalCurveOfFirstKind κ
      (secondLineIso hπ) := by
  have := isEffectiveCartierDivisor_ker_secondLine hπ
  have := isEffectiveCartierDivisor_ker_firstLine hπ
  rw [Scheme.IdealSheafData.isExceptionalCurveOfFirstKind_iff_pullbackPicardClass]
  show schemePullbackClass (secondLineIso hπ).hom
    (schemePullbackClass (secondLine _).ker.subschemeι (picardClass _)) = _
  rw [Stacks.Picard.schemePullbackClass_comp, asIso_hom, Scheme.Hom.toImage_imageι]
  refine schemePullbackClass_picardClass_eq_neg_one _ (secondLine _).ker (firstLine _).ker ?_ 1
    (comap_ker_firstLine_secondLine _)
  rw [add_comm]
  exact picardClass_ker_firstLine_add_secondLine hπ

end Exceptional

end Stacks.Models.GenusZero

end
