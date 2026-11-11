module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ClosedImmersionSections
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodFiltration
public import StacksFrontier.AlgebraicGeometry.Surfaces.FormalNeighborhoodGradedPiece
public import StacksFrontier.AlgebraicGeometry.Surfaces.NegativeCurveFormalNeighborhoodAlgebra
public import StacksFrontier.AlgebraicGeometry.Surfaces.ThickeningKernelFiltration

/-!
# The formal neighbourhood of a curve with negative normal bundle

Let `D` be an effective Cartier divisor on a scheme `X`, cut out by the ideal sheaf `I`, with
subscheme `C = V(I)`, infinitesimal thickenings `Cₙ₊₁ = V(Iⁿ⁺¹)`
(`AlgebraicGeometry.Scheme.IdealSheafData.thickening D n`) and ring of compatible functions
`A = lim Γ(Cₙ, 𝒪)` (`AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing D`), filtered by
the projection kernels `Fₙ₊₁ = ker (A ⟶ Γ(Cₙ₊₁, 𝒪))`. Write `L = 𝒪_X(-D)|_C = I/I²` for the
conormal sheaf, so that `𝒪_X(-D ^ n)|_C = Iⁿ/Iⁿ⁺¹` is its `n`-th power.

This is the situation of a curve `C` whose normal bundle is negative, i.e. whose conormal bundle
`L` is positive: Artin's contraction of `C` starts from the ring `A`. This file proves, for an
arbitrary such `D`, the structure theory of `A` from three properties of `C` and `L`:

* `Γ(C, 𝒪_C)` is a field (for `C` proper over `k` with `H⁰(C, 𝒪_C) = k`);
* `H¹(C, Lⁿ) = 0` for `n ≥ 1` (for `L` of degree `> 2g - 2` on a curve of genus `g`);
* the section ring `⨁ₙ H⁰(C, Lⁿ)` is generated in degrees `≤ c` and finite in those degrees.

The conclusions are:

* the transition maps `Γ(Cₙ₊₁, 𝒪) ⟶ Γ(Cₙ, 𝒪)` and the projections `A ⟶ Γ(Cₙ, 𝒪)` are surjective
  (`AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestriction_of_isZero`);
* `A / F₁ ≅ Γ(C, 𝒪_C)` (`AlgebraicGeometry.Scheme.IdealSheafData.residueRingEquiv`), and the graded
  piece `Fₙ₊₁ / Fₙ₊₂` is `H⁰(C, Lⁿ⁺¹)`, semilinearly over `A / F₁`
  (`AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceEquiv`, `gradedSymbol_mul`);
* `A` is a complete Noetherian local ring with maximal ideal `F₁`, and `F_{c n} ⊆ 𝔪ⁿ ⊆ Fₙ`, so the
  `𝔪`-adic topology of `A` is the topology of the thickenings
  (`AlgebraicGeometry.Scheme.IdealSheafData.isNoetherianCompleteLocalRing_of_negativeCurve`,
  `maximalIdeal_eq_formalNeighborhoodFiltration_one`, `formalNeighborhoodFiltration_mul_le_pow`).

## The generation hypothesis

The pairing on the graded pieces is the one of
`AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_mul`: the product of a
section `a` of `L^{i+1}` and a section `b` of `L^{j+1}` is the section whose symbol is the product
`u v` of any lifts `u`, `v` of `a`, `b` to the thickening `C_{i+j+2}`
(`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsProducts`). It is the restricted product
`Stacks.Divisors.restrictedIdealMulSections a b` of the two sections, by
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections`.

## References

* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K) — the case of an
  exceptional curve of the first kind, whose proof this generalizes.
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-! ### The filtration is complete -/

/-- The projection-kernel filtration of the ring of compatible functions is a complete
filtration, for every ideal sheaf. -/
public theorem isCompleteFiltration_formalNeighborhoodFiltration :
    Stacks.IsCompleteFiltration (formalNeighborhoodFiltration D) where
  zero := formalNeighborhoodFiltration_zero D
  succ_le := formalNeighborhoodFiltration_succ_le D
  mul_le := formalNeighborhoodFiltration_mul_le D
  iInf_eq_bot := iInf_formalNeighborhoodFiltration D
  exists_sum := exists_sum_formalNeighborhoodFiltration D

/-! ### Surjectivity of the transition maps -/

/-- **The transition maps of the tower of thickenings are surjective when `H¹(C, Lⁿ) = 0` for
`n ≥ 1`.** The vanishing on `C` is moved to `X` along the closed immersion, and
`AlgebraicGeometry.Scheme.IdealSheafData.surjective_thickeningRestriction` ([Stacks, Tag 0C4T])
applies. -/
public theorem surjective_thickeningRestriction_of_isZero [IsEffectiveCartierDivisor D]
    (hH1 : ∀ n : ℕ, IsZero (((Stacks.Cohomology.sectionsFunctor D.subscheme ⊤).rightDerived 1).obj
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))))))
    (m : ℕ) : Function.Surjective (thickeningRestriction D m) :=
  surjective_thickeningRestriction D m
    (Stacks.Cohomology.ClosedImmersion.isZero_rightDerived_one_sectionsFunctor_pushforward
      D.subschemeι _ (hH1 m))

/-! ### The residue ring -/

/-- The residue map `A ⟶ Γ(C, 𝒪_C)`: projection to the first thickening `V(D ^ 1)`, read on
`V(D)`. -/
public def formalNeighborhoodResidueMap : formalNeighborhoodRing D →+* Γ(D.subscheme, ⊤) :=
  (inclusion (le_of_eq (pow_one D))).appTop.hom.comp (formalNeighborhoodProjection D 0)

/-- Restricting the `(n + 1)`-st component of a compatible function to `C` gives its residue. -/
public theorem inclusion_appTop_formalNeighborhoodProjection (n : ℕ)
    (a : formalNeighborhoodRing D) :
    (inclusion (pow_succ_le_self D n)).appTop.hom (formalNeighborhoodProjection D n a) =
      formalNeighborhoodResidueMap D a := by
  rw [formalNeighborhoodResidueMap, RingHom.comp_apply,
    ← thickeningRestrictionLE_formalNeighborhoodProjection D (Nat.zero_le n) a]
  exact (inclusion_appTop_inclusion_appTop _ _ _).symm

/-- The residue map is surjective when the projection to the first thickening is. -/
public theorem surjective_formalNeighborhoodResidueMap
    (hsurj : Function.Surjective (formalNeighborhoodProjection D 0)) :
    Function.Surjective (formalNeighborhoodResidueMap D) := by
  intro w
  obtain ⟨a, ha⟩ := hsurj ((inclusion (pow_one D).ge).appTop.hom w)
  exact ⟨a, by rw [formalNeighborhoodResidueMap, RingHom.comp_apply, ha,
    inclusion_appTop_inclusion_appTop_of_eq_symm (pow_one D) w]⟩

/-- The kernel of the residue map is the first step of the filtration. -/
public theorem ker_formalNeighborhoodResidueMap :
    RingHom.ker (formalNeighborhoodResidueMap D) = formalNeighborhoodFiltration D 1 := by
  ext a
  change formalNeighborhoodResidueMap D a = 0 ↔ formalNeighborhoodProjection D 0 a = 0
  rw [formalNeighborhoodResidueMap, RingHom.comp_apply]
  constructor
  · intro h
    rw [← inclusion_appTop_inclusion_appTop_of_eq (pow_one D)
      (formalNeighborhoodProjection D 0 a), h, map_zero]
  · intro h
    rw [h, map_zero]

/-- **The residue ring of the formal neighbourhood is the ring of functions on `C`**:
`A / F₁ ≅ Γ(C, 𝒪_C)`, when the projection to the first thickening is surjective. -/
public def residueRingEquiv (hsurj : Function.Surjective (formalNeighborhoodProjection D 0)) :
    formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1 ≃+* Γ(D.subscheme, ⊤) :=
  (Ideal.quotEquivOfEq (ker_formalNeighborhoodResidueMap D).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_formalNeighborhoodResidueMap D hsurj))

/-- If `Γ(C, 𝒪_C)` is a field and the projection to the first thickening is surjective, the
residue ring `A / F₁` is a field. -/
public theorem isField_quotient_formalNeighborhoodFiltration_one_of_isField
    (hsurj : Function.Surjective (formalNeighborhoodProjection D 0))
    (hfield : IsField Γ(D.subscheme, ⊤)) :
    IsField (formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1) :=
  MulEquiv.isField hfield (residueRingEquiv D hsurj).toMulEquiv

/-! ### The graded pieces are the sections of the powers of the conormal sheaf -/

section Graded

variable [IsEffectiveCartierDivisor D]

/-- The global sections `H⁰(C, Lⁿ⁺¹)` of the `(n + 1)`-st power `𝒪_X(-D ^ (n + 1))|_C` of the
conormal sheaf. -/
public abbrev conormalPowSections (n : ℕ) : Type u :=
  Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
    (⊤ : D.subscheme.Opens))

/-- The symbol of an element of `Fₙ₊₁`: the global section of `Lⁿ⁺¹ = 𝒪_X(-D ^ (n + 1))|_C`
whose image under `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHom` is its
`(n + 1)`-st component. -/
public def gradedSymbol (n : ℕ) :
    (formalNeighborhoodFiltration D (n + 1)).toAddSubgroup →+
      Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
        (⊤ : D.subscheme.Opens)) :=
  (AddMonoidHom.ofInjective (gradedSectionsHom_injective D n)).symm.toAddMonoidHom.comp
    (((formalNeighborhoodProjection D (n + 1)).toAddMonoidHom.comp
      (formalNeighborhoodFiltration D (n + 1)).toAddSubgroup.subtype).codRestrict _
      fun a => (gradedSectionsHom_eq_iff D n _).1
        (thickeningRestriction_projection_eq_zero D n a.2))

/-- The image of the symbol of `a` under `gradedSectionsHom` is the `(n + 1)`-st component of
`a`. -/
public theorem gradedSectionsHom_gradedSymbol (n : ℕ)
    (a : (formalNeighborhoodFiltration D (n + 1)).toAddSubgroup) :
    gradedSectionsHom D n (gradedSymbol D n a) = formalNeighborhoodProjection D (n + 1) a := by
  have := (AddMonoidHom.ofInjective (gradedSectionsHom_injective D n)).apply_symm_apply
    ⟨formalNeighborhoodProjection D (n + 1) a, (gradedSectionsHom_eq_iff D n _).1
      (thickeningRestriction_projection_eq_zero D n a.2)⟩
  exact congrArg Subtype.val this

/-- The symbol of `a` is characterized by its image under `gradedSectionsHom`. -/
public theorem gradedSymbol_eq_iff (n : ℕ)
    (a : (formalNeighborhoodFiltration D (n + 1)).toAddSubgroup)
    (x : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens))) :
    gradedSymbol D n a = x ↔ gradedSectionsHom D n x = formalNeighborhoodProjection D (n + 1) a :=
  ⟨fun h => h ▸ gradedSectionsHom_gradedSymbol D n a, fun h =>
    gradedSectionsHom_injective D n (by rw [gradedSectionsHom_gradedSymbol, h])⟩

/-- An element of `Fₙ₊₁` has symbol zero exactly when it lies in `Fₙ₊₂`. -/
public theorem gradedSymbol_eq_zero_iff (n : ℕ)
    (a : (formalNeighborhoodFiltration D (n + 1)).toAddSubgroup) :
    gradedSymbol D n a = 0 ↔
      (a : formalNeighborhoodRing D) ∈ formalNeighborhoodFiltration D (n + 2) := by
  rw [gradedSymbol_eq_iff, map_zero, eq_comm]
  exact Iff.rfl

/-- **Every section of `Lⁿ⁺¹` is a symbol**, when the transition maps are surjective. -/
public theorem surjective_gradedSymbol
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m)) (n : ℕ) :
    Function.Surjective (gradedSymbol D n) := by
  intro x
  obtain ⟨a, ha, hax⟩ := exists_projection_eq_of_thickeningRestriction_eq_zero D n hsurj
    ((gradedSectionsHom_eq_iff D n _).2 ⟨x, rfl⟩)
  exact ⟨⟨a, ha⟩, (gradedSymbol_eq_iff D n _ x).2 hax.symm⟩

/-- **The symbol is semilinear over the residue map**: the symbol of `b a` is the residue of `b`
times the symbol of `a`. -/
public theorem gradedSymbol_mul (n : ℕ) (b : formalNeighborhoodRing D)
    (a : (formalNeighborhoodFiltration D (n + 1)).toAddSubgroup) :
    gradedSymbol D n ⟨b * a, Ideal.mul_mem_left _ b a.2⟩ =
      formalNeighborhoodResidueMap D b • gradedSymbol D n a := by
  rw [gradedSymbol_eq_iff, ← inclusion_appTop_formalNeighborhoodProjection D (n + 1) b,
    gradedSectionsHom_smul, gradedSectionsHom_gradedSymbol]
  exact (map_mul _ _ _).symm

/-- **The graded piece `Fₙ₊₁ / Fₙ₊₂` is `H⁰(C, Lⁿ⁺¹)`.** The symbol identifies the quotient of
`Fₙ₊₁` by the elements of `Fₙ₊₂` with the global sections of `𝒪_X(-D ^ (n + 1))|_C`, when the
transition maps are surjective; it is semilinear over `A / F₁ ≅ Γ(C, 𝒪_C)` by
`AlgebraicGeometry.Scheme.IdealSheafData.gradedSymbol_mul`. -/
public def gradedPieceEquiv (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m))
    (n : ℕ) :
    (formalNeighborhoodFiltration D (n + 1)).toAddSubgroup ⧸ (gradedSymbol D n).ker ≃+
      Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
        (⊤ : D.subscheme.Opens)) :=
  QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_gradedSymbol D hsurj n)

/-- The kernel divided out in `AlgebraicGeometry.Scheme.IdealSheafData.gradedPieceEquiv` is
`Fₙ₊₂`. -/
public theorem mem_ker_gradedSymbol_iff (n : ℕ)
    (a : (formalNeighborhoodFiltration D (n + 1)).toAddSubgroup) :
    a ∈ (gradedSymbol D n).ker ↔
      (a : formalNeighborhoodRing D) ∈ formalNeighborhoodFiltration D (n + 2) :=
  (AddMonoidHom.mem_ker).trans (gradedSymbol_eq_zero_iff D n a)

/-! ### Generation of the section ring -/

/-- The *products* in `H⁰(C, Lⁿ⁺¹)` of a section of `L^{i+1}` with a section of `L^{j+1}`, where
`i + j + 1 = n`: a member is a section `y` for which there are sections `a`, `b` such that the
symbol of `y` is the product `u v` of **every** pair of lifts `u` of `a` and `v` of `b` to the
thickening `C_{n+1}`. By `AlgebraicGeometry.Scheme.IdealSheafData.exists_gradedSectionsHom_eq_mul`
every pair `(a, b)` has such a product; it is `Stacks.Divisors.restrictedIdealMulSections a b`,
by `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections`. -/
public def gradedSectionsProducts {n i j : ℕ} (h : i + j + 1 = n) :
    Set Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens)) :=
  {y | ∃ (a : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (i + 1))),
          (⊤ : D.subscheme.Opens)))
        (b : Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (j + 1))),
          (⊤ : D.subscheme.Opens))),
      ∀ u v : Γ(thickening D (n + 1), ⊤),
        thickeningRestrictionLE D (show i + 1 ≤ n + 1 by omega) u = gradedSectionsHom D i a →
        thickeningRestrictionLE D (show j + 1 ≤ n + 1 by omega) v = gradedSectionsHom D j b →
        gradedSectionsHom D n y = u * v}

/-- The products in `H⁰(C, Lⁿ⁺¹)` of a section of `L^{i+1}`, `i < c`, with a section of a
complementary power. -/
public def gradedSectionsProductsBelow (c n : ℕ) :
    Set Γ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1))),
      (⊤ : D.subscheme.Opens)) :=
  {y | ∃ (i j : ℕ) (h : i + j + 1 = n), i < c ∧ y ∈ gradedSectionsProducts D h}

/-- A symbol of a product of two lifts is the projection of the product of two elements of the
filtration. -/
private theorem exists_mul_of_mem_gradedSectionsProducts
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m)) {n i j : ℕ}
    (h : i + j + 1 = n) {y} (hy : y ∈ gradedSectionsProducts D h) :
    ∃ a ∈ formalNeighborhoodFiltration D (i + 1), ∃ b ∈ formalNeighborhoodFiltration D (j + 1),
      gradedSectionsHom D n y = formalNeighborhoodProjection D (n + 1) (a * b) := by
  obtain ⟨x, z, hxz⟩ := hy
  obtain ⟨a, ha, hax⟩ := exists_projection_eq_of_thickeningRestriction_eq_zero D i hsurj
    ((gradedSectionsHom_eq_iff D i _).2 ⟨x, rfl⟩)
  obtain ⟨b, hb, hbz⟩ := exists_projection_eq_of_thickeningRestriction_eq_zero D j hsurj
    ((gradedSectionsHom_eq_iff D j _).2 ⟨z, rfl⟩)
  refine ⟨a, ha, b, hb, ?_⟩
  rw [map_mul]
  exact hxz _ _ (by rw [thickeningRestrictionLE_formalNeighborhoodProjection, hax])
    (by rw [thickeningRestrictionLE_formalNeighborhoodProjection, hbz])

/-- **Bounded-degree generation of the section ring gives bounded-degree generation of the
filtration.** If the transition maps are surjective, `H⁰(C, Lᵐ⁺¹)` is finitely generated over
`Γ(C, 𝒪_C)` for `m < c`, and every section of `Lⁿ⁺¹`, `n ≥ c`, is a sum of products of a section
of some `L^{i+1}`, `i < c`, with a section of the complementary power, then finitely many
elements `gₖ ∈ F₁` satisfy `Fₙ ⊆ (g) · F_{n-c} + Fₙ₊₁` for every `n ≥ 1`. -/
public theorem exists_le_mul_sup_of_gradedSectionsProducts
    (hsurj : ∀ m, Function.Surjective (thickeningRestriction D m)) (c : ℕ)
    (hfin : ∀ m < c, ∃ t : Finset Γ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ (m + 1))), (⊤ : D.subscheme.Opens)),
      Submodule.span Γ(D.subscheme, ⊤) (t : Set (conormalPowSections D m)) = ⊤)
    (hgen : ∀ n, c ≤ n → ∀ x : Γ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ (n + 1))), (⊤ : D.subscheme.Opens)),
      x ∈ AddSubgroup.closure (gradedSectionsProductsBelow D c n)) :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → formalNeighborhoodRing D),
      (∀ k, g k ∈ formalNeighborhoodFiltration D 1) ∧
      ∀ n, 1 ≤ n → formalNeighborhoodFiltration D n ≤
        Ideal.span (Set.range g) * formalNeighborhoodFiltration D (n - c) ⊔
          formalNeighborhoodFiltration D (n + 1) := by
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  choose t ht using hfin
  -- Lifts of the chosen generators of the graded pieces of degree `≤ c`.
  have hlift : ∀ (m : ℕ) (x : Γ((Scheme.Modules.pullback D.subschemeι).obj
      (negativeTwist (D ^ (m + 1))), (⊤ : D.subscheme.Opens))),
      ∃ a ∈ formalNeighborhoodFiltration D (m + 1),
        formalNeighborhoodProjection D (m + 1) a = gradedSectionsHom D m x := fun m x =>
    exists_projection_eq_of_thickeningRestriction_eq_zero D m hsurj
      ((gradedSectionsHom_eq_iff D m _).2 ⟨x, rfl⟩)
  choose lift hliftF hliftP using hlift
  let ι : Type u := Σ m : Fin c, {x // x ∈ t m.1 m.2}
  let g : ι → formalNeighborhoodRing D := fun k => lift k.1.1 k.2.1
  have : Fintype ι := inferInstance
  set J := Ideal.span (Set.range g)
  have hgF : ∀ k, g k ∈ formalNeighborhoodFiltration D 1 := fun k =>
    hF.antitone (by omega) (hliftF _ _)
  refine ⟨ι, this, g, hgF, ?_⟩
  have hres := surjective_formalNeighborhoodResidueMap D
    (surjective_formalNeighborhoodProjection D hsurj 0)
  -- Degrees `≤ c`: `F_{m+1} ⊆ J + F_{m+2}`.
  have hlow : ∀ m (hm : m < c), formalNeighborhoodFiltration D (m + 1) ≤
      J ⊔ formalNeighborhoodFiltration D (m + 2) := by
    intro m hm z hz
    have hx : gradedSymbol D m ⟨z, hz⟩ ∈ Submodule.span Γ(D.subscheme, ⊤) (t m hm : Set _) := by
      rw [ht m hm]; exact Submodule.mem_top
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hx
    choose α hα using fun s => hres (f s)
    obtain ⟨w, hwdef⟩ : ∃ w : formalNeighborhoodRing D,
        w = ∑ s ∈ (t m hm).attach, α s * g ⟨⟨m, hm⟩, s⟩ := ⟨_, rfl⟩
    have hw : w ∈ J := hwdef ▸ Submodule.sum_mem _ fun s _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, rfl⟩)
    have hproj : formalNeighborhoodProjection D (m + 1) w =
        formalNeighborhoodProjection D (m + 1) z := by
      have h1 : formalNeighborhoodProjection D (m + 1) z =
          gradedSectionsHom D m (∑ s ∈ t m hm, f s • s) := by
        rw [hf, gradedSectionsHom_gradedSymbol]
      rw [h1, hwdef, ← Finset.sum_attach (t m hm) (fun s => f s • s), map_sum, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_mul, ← hα s, ← inclusion_appTop_formalNeighborhoodProjection D (m + 1),
        gradedSectionsHom_smul]
      exact congrArg (formalNeighborhoodProjection D (m + 1) (α s) * ·) (hliftP _ _)
    refine Submodule.mem_sup.2 ⟨w, hw, z - w, ?_, by ring⟩
    change z - w ∈ RingHom.ker (formalNeighborhoodProjection D (m + 1))
    rw [RingHom.mem_ker, map_sub, hproj, sub_self]
  -- Hence every `Fₘ`, `m ≥ 1`, lies in `J + F_{c+1}`.
  have hlow' : ∀ d m, m + d = c + 1 → 1 ≤ m → formalNeighborhoodFiltration D m ≤
      J ⊔ formalNeighborhoodFiltration D (c + 1) := by
    intro d
    induction d with
    | zero => intro m hm _; rw [show m = c + 1 by omega]; exact le_sup_right
    | succ d ih =>
      intro m hm hm1
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      refine (hlow m' (by omega)).trans (sup_le le_sup_left ?_)
      exact ih (m' + 2) (by omega) (by omega)
  have hlowF : ∀ m, 1 ≤ m → formalNeighborhoodFiltration D m ≤
      J ⊔ formalNeighborhoodFiltration D (c + 1) := by
    intro m hm
    rcases le_or_gt m (c + 1) with h | h
    · exact hlow' (c + 1 - m) m (by omega) hm
    · exact (hF.antitone h.le).trans le_sup_right
  intro n hn
  rcases le_or_gt n c with hnc | hnc
  · -- Low degrees.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.sub_eq_zero_of_le hnc, formalNeighborhoodFiltration_zero, Ideal.mul_top]
    exact hlow m (by omega)
  · -- High degrees, from the generation of the section ring.
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    let S : AddSubgroup Γ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ (n' + 1))), (⊤ : D.subscheme.Opens)) :=
      { carrier := {x | ∃ w ∈ J * formalNeighborhoodFiltration D (n' + 1 - c),
          formalNeighborhoodProjection D (n' + 1) w = gradedSectionsHom D n' x}
        add_mem' := by
          rintro x y ⟨w, hw, hwx⟩ ⟨w', hw', hwy⟩
          exact ⟨w + w', add_mem hw hw', by rw [map_add, map_add, hwx, hwy]⟩
        zero_mem' := ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩
        neg_mem' := by
          rintro x ⟨w, hw, hwx⟩
          exact ⟨-w, neg_mem hw, by rw [map_neg, map_neg, hwx]⟩ }
    have hcl : AddSubgroup.closure (gradedSectionsProductsBelow D c n') ≤ S := by
      rw [AddSubgroup.closure_le]
      rintro y ⟨i, j, h, hi, hy⟩
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_gradedSectionsProducts D hsurj h hy
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 (hlowF (i + 1) (by omega) ha)
      refine ⟨p * b, Ideal.mul_mem_mul hp (hF.antitone (by omega) hb), ?_⟩
      have hqb : q * b ∈ formalNeighborhoodFiltration D (n' + 2) :=
        hF.antitone (by omega) (hF.mul_le _ _ (Ideal.mul_mem_mul hq hb))
      have hqb' : formalNeighborhoodProjection D (n' + 1) (q * b) = 0 := hqb
      rw [hab, add_mul, map_add, hqb', add_zero]
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hcl (hgen n' (by omega) (gradedSymbol D n' ⟨z, hz⟩))
    rw [gradedSectionsHom_gradedSymbol] at hwz
    refine Submodule.mem_sup.2 ⟨w, hw, z - w, ?_, by ring⟩
    change z - w ∈ RingHom.ker (formalNeighborhoodProjection D (n' + 1))
    rw [RingHom.mem_ker, map_sub]
    exact sub_eq_zero.2 hwz.symm

end Graded

/-! ### The structure of the ring of compatible functions -/

section Structure

variable [IsEffectiveCartierDivisor D]

/-- The three hypotheses on a curve with positive conormal bundle `L`, in the form the
structure theory of the formal neighbourhood uses: `Γ(C, 𝒪_C)` is a field, `H¹(C, Lⁿ) = 0` for
`n ≥ 1`, and the section ring `⨁ₙ H⁰(C, Lⁿ)` is generated in degrees `≤ c`, `c ≥ 1`, by finitely
generated pieces. -/
public structure IsPositiveConormal (c : ℕ) : Prop where
  /-- `H⁰(C, 𝒪_C)` is a field. -/
  isField : IsField Γ(D.subscheme, ⊤)
  /-- `H¹(C, Lⁿ) = 0` for `n ≥ 1`. -/
  isZero_H1 : ∀ n : ℕ,
    IsZero (((Stacks.Cohomology.sectionsFunctor D.subscheme ⊤).rightDerived 1).obj
      ((Scheme.Modules.pullback D.subschemeι).obj (negativeTwist (D ^ (n + 1)))))
  /-- The generation degree is positive. -/
  one_le : 1 ≤ c
  /-- `H⁰(C, Lᵐ⁺¹)` is finitely generated over `H⁰(C, 𝒪_C)` for `m < c`. -/
  fg : ∀ m < c, ∃ t : Finset Γ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ (m + 1))), (⊤ : D.subscheme.Opens)),
      Submodule.span Γ(D.subscheme, ⊤) (t : Set (conormalPowSections D m)) = ⊤
  /-- The section ring is generated in degrees `≤ c`. -/
  generate : ∀ n, c ≤ n → ∀ x : Γ((Scheme.Modules.pullback D.subschemeι).obj
        (negativeTwist (D ^ (n + 1))), (⊤ : D.subscheme.Opens)),
      x ∈ AddSubgroup.closure (gradedSectionsProductsBelow D c n)

variable {D} {c : ℕ} (hD : IsPositiveConormal D c)
include hD

/-- Under `AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal`, the transition maps of
the tower of thickenings are surjective. -/
public theorem IsPositiveConormal.surjective_thickeningRestriction (m : ℕ) :
    Function.Surjective (thickeningRestriction D m) :=
  surjective_thickeningRestriction_of_isZero D hD.isZero_H1 m

/-- Under `AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal`, the projections of the
ring of compatible functions to the thickenings are surjective. -/
public theorem IsPositiveConormal.surjective_formalNeighborhoodProjection (n : ℕ) :
    Function.Surjective (formalNeighborhoodProjection D n) :=
  _root_.AlgebraicGeometry.Scheme.IdealSheafData.surjective_formalNeighborhoodProjection D
    hD.surjective_thickeningRestriction n

/-- Under `AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal`, the residue ring `A / F₁`
is a field. -/
public theorem IsPositiveConormal.isField_quotient :
    IsField (formalNeighborhoodRing D ⧸ formalNeighborhoodFiltration D 1) :=
  isField_quotient_formalNeighborhoodFiltration_one_of_isField D
    (hD.surjective_formalNeighborhoodProjection 0) hD.isField

/-- Under `AlgebraicGeometry.Scheme.IdealSheafData.IsPositiveConormal`, finitely many elements of
`F₁` generate the filtration in degrees `≤ c`. -/
public theorem IsPositiveConormal.exists_le_mul_sup :
    ∃ (ι : Type u) (_ : Fintype ι) (g : ι → formalNeighborhoodRing D),
      (∀ k, g k ∈ formalNeighborhoodFiltration D 1) ∧
      ∀ n, 1 ≤ n → formalNeighborhoodFiltration D n ≤
        Ideal.span (Set.range g) * formalNeighborhoodFiltration D (n - c) ⊔
          formalNeighborhoodFiltration D (n + 1) :=
  exists_le_mul_sup_of_gradedSectionsProducts D hD.surjective_thickeningRestriction c hD.fg
    hD.generate

omit hD in
/-- **The ring of compatible functions on the thickenings of a curve with positive conormal
bundle is a complete Noetherian local ring.** -/
public theorem IsPositiveConormal.isNoetherianCompleteLocalRing {D : X.IdealSheafData}
    [IsEffectiveCartierDivisor D] {c : ℕ} (hD : IsPositiveConormal D c) :
    IsNoetherianCompleteLocalRing (formalNeighborhoodRing D) := by
  obtain ⟨ι, _, g, hg, hstep⟩ := hD.exists_le_mul_sup
  exact (isCompleteFiltration_formalNeighborhoodFiltration D)
    |>.isNoetherianCompleteLocalRing_of_le_mul_sup g c hD.one_le hg hstep
      hD.isField_quotient

/-- The local ring structure of the ring of compatible functions. -/
public theorem IsPositiveConormal.isLocalRing : IsLocalRing (formalNeighborhoodRing D) :=
  hD.isNoetherianCompleteLocalRing.isLocal

/-- **The maximal ideal is the first step of the filtration**: the compatible functions
vanishing on `C`. -/
public theorem IsPositiveConormal.maximalIdeal_eq :
    letI := hD.isLocalRing
    IsLocalRing.maximalIdeal (formalNeighborhoodRing D) = formalNeighborhoodFiltration D 1 := by
  let _ := hD.isLocalRing
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.Quotient.maximal_of_isField _ hD.isField_quotient)).symm

/-- **The `𝔪`-adic topology of `A` is the topology of the thickenings**: `𝔪ⁿ ⊆ Fₙ`, i.e. a
power of the maximal ideal vanishes on the corresponding thickening. -/
public theorem IsPositiveConormal.maximalIdeal_pow_le (n : ℕ) :
    letI := hD.isLocalRing
    IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ n ≤ formalNeighborhoodFiltration D n := by
  let _ := hD.isLocalRing
  exact (isCompleteFiltration_formalNeighborhoodFiltration D).pow_le _
    hD.maximalIdeal_eq.le n

/-- **The `𝔪`-adic topology of `A` is the topology of the thickenings**: `F_{c n} ⊆ 𝔪ⁿ`, i.e. a
compatible function vanishing on `C_{c n}` lies in the `n`-th power of the maximal ideal. -/
public theorem IsPositiveConormal.le_maximalIdeal_pow (n : ℕ) :
    letI := hD.isLocalRing
    formalNeighborhoodFiltration D (c * n) ≤
      IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ n := by
  let _ := hD.isLocalRing
  obtain ⟨ι, _, g, hg, hstep⟩ := hD.exists_le_mul_sup
  have hF := isCompleteFiltration_formalNeighborhoodFiltration D
  rw [hD.maximalIdeal_eq, hF.eq_one_of_le_mul_sup g c hg hstep]
  exact hF.le_pow_of_le_mul_sup g c hD.one_le hstep n

/-- The kernel of the projection to the `(n + 1)`-st thickening lies between `𝔪^{⌈(n+1)/c⌉}` and
`𝔪ⁿ⁺¹`; in particular the kernels are open for the `𝔪`-adic topology. -/
public theorem IsPositiveConormal.maximalIdeal_pow_le_ker (n : ℕ) :
    letI := hD.isLocalRing
    IsLocalRing.maximalIdeal (formalNeighborhoodRing D) ^ (n + 1) ≤
      RingHom.ker (formalNeighborhoodProjection D n) :=
  hD.maximalIdeal_pow_le (n + 1)

end Structure

end AlgebraicGeometry.Scheme.IdealSheafData

end
