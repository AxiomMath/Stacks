module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Classes
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.TwoGeneratorChartGlue
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections

/-!
# Functions and cohomology on the two-generator almost blowup square

Let `f₁, f₂` be elements of a commutative ring `A`. The two-generator almost blowup square of
[Stacks, Tag 0EVH] has base `X = Spec A` and modification
`b : X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁)) ⟶ X`. This file proves the first two assertions of
[Stacks, Tag 0EVJ] for it:

* the higher cohomology of `𝒪_{X'}` vanishes;
* `Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` is surjective.

The third, that the kernel of that map is an ideal of square zero, is
`Stacks.AlmostBlowUp.modificationToBase_ker_sq_eq_bot` in
`StacksFrontier/AlgebraicGeometry/Topologies/WeakNormalization/TwoGeneratorKernel.lean`. Together the
three carry Tag 0EVJ.

## Main definitions

* `Stacks.AlmostBlowUp.chartEval`: the value of a global function on the modification on the chart
  `D₊(Tᵢ)`, as a degree-zero fraction.

## Main results

* `Stacks.AlmostBlowUp.eq_of_chartEval_eq`: a global function is determined by its two chart
  values.
* `Stacks.AlmostBlowUp.awayMap_chartEval`: the two chart values agree on the overlap.
* `Stacks.AlmostBlowUp.exists_restrict_add_restrict_eq`: every function on the overlap of the two
  charts is a sum of one restricted from each.
* `Stacks.AlmostBlowUp.isZero_hgroup_unit_of_two_affine_cover`: **Mayer--Vietoris vanishing** for
  a scheme covered by two affine opens with affine intersection whose Čech `H¹` vanishes.
* `Stacks.AlmostBlowUp.surjective_Γ_modificationToBase` and
  `Stacks.AlmostBlowUp.isZero_hgroup_structureSheaf`: **the two assertions of Tag 0EVJ** proved
  here.

## Implementation notes

**The route is the two-chart Čech computation, not base change from `Z[f₁,f₂]`.** The source
proves the universal case over the polynomial ring `Z[f₁,f₂]`, where `X'` is an effective Cartier
divisor in `P¹_X` cut out by `f₂T₀ - f₁T₁`, and then transports the conclusion to an arbitrary
base by cohomology and base change ([Stacks, Tags 0E7F, 0E7G, 0E7I]). That detour exists because
the resolution `0 → 𝒪(-1) → 𝒪 → 𝒪_{X'} → 0` on `P¹_X` is exact on the left only when
`f₂T₀ - f₁T₁` is a nonzerodivisor, which fails for a general `A` — for `f₁ = f₂ = 0` the map
`𝒪(-1) → 𝒪` is zero.

Over an arbitrary base both assertions are instead immediate from the two standard charts, and
that is what is done here. On `D₊(T₀)` the coordinate is `T₁/T₀` and on `D₊(T₁)` it is `T₀/T₁`,
and the overlap `D₊(T₀T₁)` is generated additively by the two charts because a binary form of
degree `2n` is divisible monomialwise by `T₁ⁿ` or by `T₀ⁿ`. The kernel computation is the glueing
lemma `Stacks.AlmostBlowUp.exists_const_of_relationForm_mem`. Nothing here needs cohomology and
base change, properness, finite presentation, or the universal case; the inputs are Serre
vanishing on an affine open ([Stacks, Tag 01XB]), the Mayer--Vietoris sequence ([Stacks, Tag
01EB]) and polynomial algebra.

**The chart value, not the restriction.** `Stacks.AlmostBlowUp.chartEval` reads a global function
through `AlgebraicGeometry.Proj.awayι`, the chart inclusion as a morphism out of a spectrum,
rather than through the restriction map to `D₊(Tᵢ)`. That is the spelling for which
`Stacks.AlmostBlowUp.awayι_comp_modificationToBase` and
`AlgebraicGeometry.Proj.SpecMap_awayMap_awayι` apply with no transport, and it is what makes the
comparison with the chart structure map `Stacks.AlmostBlowUp.chartAwayMap` a one-line
consequence of `AlgebraicGeometry.Scheme.ΓSpecIso_naturality`.

**Mayer--Vietoris is run on an abstract scheme.** The elaborated terms of `Proj` of the
modification grading are large enough that the diagram chase does not fit in the default
heartbeat budget when written out at that scheme; it is therefore stated and proved for an
arbitrary `X`, `U`, `V` as `isZero_hgroup_unit_of_two_affine_cover` and applied once.

## References

* [Stacks Project, Tag 0EVJ](https://stacks.math.columbia.edu/tag/0EVJ)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousLocalization
open TopologicalSpace Opposite
open Stacks.Cohomology Stacks.Cohomology.AmbientMayerVietoris

namespace Stacks.AlmostBlowUp

universe u

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- The value of a global function on the modification on the chart `D₊(Tᵢ)`, read as a
degree-zero fraction. -/
def chartEval (i : Fin 2) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    Γ(AlgebraicGeometry.Proj (modificationGrading A f₁ f₂), ⊤) →
      Away (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ i) :=
  letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
  fun σ => (Scheme.ΓSpecIso (CommRingCat.of (Away (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ i)))).hom.hom ((awayChartι A f₁ f₂ i).appTop.hom σ)

/-- **The chart value of a function pulled back from the base is the chart structure map.** -/
theorem chartEval_modificationToBase (i : Fin 2) (a : A) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    chartEval A f₁ f₂ i ((Scheme.Γ.map (modificationToBase A f₁ f₂).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
      = chartAwayMap A f₁ f₂ i a := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hmor : (Scheme.ΓSpecIso (CommRingCat.of A)).inv
        ≫ (modificationToBase A f₁ f₂).appTop ≫ (awayChartι A f₁ f₂ i).appTop
        ≫ (Scheme.ΓSpecIso (CommRingCat.of (Away (modificationGrading A f₁ f₂)
            (modificationCoord A f₁ f₂ i)))).hom
      = CommRingCat.ofHom (chartAwayMap A f₁ f₂ i) := by
    rw [← Category.assoc ((modificationToBase A f₁ f₂).appTop), ← Scheme.Hom.comp_appTop,
      awayι_comp_modificationToBase, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := ConcreteCategory.congr_hom hmor a
  rw [Scheme.Γ_map_op]
  simp only at h
  exact h

/-- **A global function on the modification is determined by its two chart values.** -/
theorem eq_of_chartEval_eq :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∀ σ τ : Γ(AlgebraicGeometry.Proj (modificationGrading A f₁ f₂), ⊤),
      (∀ i : Fin 2, chartEval A f₁ f₂ i σ = chartEval A f₁ f₂ i τ) → σ = τ := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  intro σ τ h
  refine (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).sheaf.eq_of_locally_eq'
    (fun i : Fin 2 => (Proj.basicOpen (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ i)).ι ''ᵁ ⊤)
    ⊤ (fun _ => homOfLE le_top) ?_ σ τ fun i => ?_
  · simp only [Scheme.Opens.ι_image_top]
    exact le_of_eq (iSup_basicOpen_modificationCoord_eq_top A f₁ f₂).symm
  have hfac : (awayChartι A f₁ f₂ i).appTop
      = (Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ i)).ι.appTop
        ≫ (Proj.basicOpenIsoSpec (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ i)
            (modificationCoord_mem A f₁ f₂ i) Nat.one_pos).inv.appTop := by
    rw [← Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_inv_ι]
  have hinj : Function.Injective (ConcreteCategory.hom
      (Proj.basicOpenIsoSpec (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ i)
        (modificationCoord_mem A f₁ f₂ i) Nat.one_pos).inv.appTop) := by
    intro x y hxy
    have h2 := congrArg (ConcreteCategory.hom
      (Proj.basicOpenIsoSpec (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ i)
        (modificationCoord_mem A f₁ f₂ i) Nat.one_pos).hom.appTop) hxy
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      Iso.hom_inv_id] at h2
    simpa using h2
  have hi : ConcreteCategory.hom ((awayChartι A f₁ f₂ i).appTop) σ
      = ConcreteCategory.hom ((awayChartι A f₁ f₂ i).appTop) τ := by
    have hh := h i
    simp only [chartEval] at hh
    exact (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (Away (modificationGrading A f₁ f₂)
        (modificationCoord A f₁ f₂ i)))).hom).1 hh
  rw [hfac, CommRingCat.comp_apply, CommRingCat.comp_apply] at hi
  have hres := hinj hi
  rw [Scheme.Opens.ι_appTop] at hres
  exact hres

/-- Reading a global function on an affine chart of a scheme is compatible with a factorization
of that chart through another. -/
theorem ΓSpecIso_hom_appTop_of_comp {X : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (u : Spec (CommRingCat.of R) ⟶ X) (v : Spec (CommRingCat.of S) ⟶ X)
    (hv : Spec.map (CommRingCat.ofHom φ) ≫ u = v) (σ : Γ(X, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (v.appTop.hom σ)
      = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (u.appTop.hom σ)) := by
  have hmor : v.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom
      = u.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ := by
    rw [← hv, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  have h := ConcreteCategory.congr_hom hmor σ
  simp only at h
  exact h

/-- **The two chart values of a global function agree on the overlap.** -/
theorem awayMap_chartEval :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∀ σ : Γ(AlgebraicGeometry.Proj (modificationGrading A f₁ f₂), ⊤),
      awayMap (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 1) rfl
          (chartEval A f₁ f₂ 0 σ)
        = awayMap (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 0)
            (mul_comm (modificationCoord A f₁ f₂ 0) (modificationCoord A f₁ f₂ 1))
            (chartEval A f₁ f₂ 1 σ) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  intro σ
  have h0 := ΓSpecIso_hom_appTop_of_comp
    (awayMap (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 1) rfl)
    (awayChartι A f₁ f₂ 0)
    (Proj.awayι (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)
      (SetLike.mul_mem_graded (modificationCoord_mem A f₁ f₂ 0)
        (modificationCoord_mem A f₁ f₂ 1)) (by omega))
    (Proj.SpecMap_awayMap_awayι (modificationGrading A f₁ f₂)
      (modificationCoord_mem A f₁ f₂ 0) Nat.one_pos
      (modificationCoord_mem A f₁ f₂ 1) rfl) σ
  have h1 := ΓSpecIso_hom_appTop_of_comp
    (awayMap (modificationGrading A f₁ f₂) (modificationCoord_mem A f₁ f₂ 0)
      (mul_comm (modificationCoord A f₁ f₂ 0) (modificationCoord A f₁ f₂ 1)))
    (awayChartι A f₁ f₂ 1)
    (Proj.awayι (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)
      (SetLike.mul_mem_graded (modificationCoord_mem A f₁ f₂ 0)
        (modificationCoord_mem A f₁ f₂ 1)) (by omega))
    (Proj.SpecMap_awayMap_awayι (modificationGrading A f₁ f₂)
      (modificationCoord_mem A f₁ f₂ 1) Nat.one_pos
      (modificationCoord_mem A f₁ f₂ 0)
      (mul_comm (modificationCoord A f₁ f₂ 0) (modificationCoord A f₁ f₂ 1))) σ
  exact h0.symm.trans h1

/-- **Stacks Project, Tag 0EVJ.** For the two-generator almost blowup square the ring map
`Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` is surjective.

A global function on `X'` has a value on each of the two standard charts; the two agree on the
overlap, so `Stacks.AlmostBlowUp.exists_chartAwayMap_eq` produces an element of `A` with those
two values, and a global function is determined by its chart values. -/
@[stacks 0EVJ "surjectivity"]
theorem surjective_Γ_modificationToBase :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    Function.Surjective (Scheme.Γ.map (modificationToBase A f₁ f₂).op).hom := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  intro σ
  obtain ⟨a, h0, h1⟩ := exists_chartAwayMap_eq (chartEval A f₁ f₂ 0 σ) (chartEval A f₁ f₂ 1 σ)
    (awayMap_chartEval A f₁ f₂ σ)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a, ?_⟩
  refine eq_of_chartEval_eq A f₁ f₂ _ σ fun i => ?_
  rw [chartEval_modificationToBase]
  fin_cases i
  · exact h0.symm
  · exact h1.symm

/-! ### The two charts generate the functions on their overlap -/

/-- **Every function on the overlap of the two standard charts is a sum of one restricted from
each chart.**  This is the vanishing of the Čech `H¹` of the two-chart cover. -/
theorem exists_restrict_add_restrict_eq :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∀ {W : (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Opens}
      (_ : Proj.basicOpen (modificationGrading A f₁ f₂)
        (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1) = W)
      (h₀ : W ≤ Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 0))
      (h₁ : W ≤ Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 1))
      (s : Γ(AlgebraicGeometry.Proj (modificationGrading A f₁ f₂), W)),
      ∃ (s₀ : Γ(AlgebraicGeometry.Proj (modificationGrading A f₁ f₂),
          Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 0)))
        (s₁ : Γ(AlgebraicGeometry.Proj (modificationGrading A f₁ f₂),
          Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 1))),
        ((AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).presheaf.map
            (homOfLE h₀).op).hom s₀
          + ((AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).presheaf.map
            (homOfLE h₁).op).hom s₁ = s := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  intro W hW h₀ h₁ s
  subst hW
  obtain ⟨w, hw⟩ := (ConcreteCategory.bijective_of_isIso
    (Proj.basicOpenIsoAway (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)
      (SetLike.mul_mem_graded (modificationCoord_mem A f₁ f₂ 0)
        (modificationCoord_mem A f₁ f₂ 1)) (by omega)).hom).2 s
  have hw' : (Proj.awayToSection (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)).hom w = s := hw
  obtain ⟨z₀, z₁, hz⟩ := exists_awayMap_add_awayMap_eq w
  refine ⟨(Proj.awayToSection (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ 0)).hom z₀,
    (Proj.awayToSection (modificationGrading A f₁ f₂)
      (modificationCoord A f₁ f₂ 1)).hom z₁, ?_⟩
  have key : ∀ {f g : _} (hg : g ∈ (modificationGrading A f₁ f₂) 1)
      (hx : modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1 = f * g)
      (h : Proj.basicOpen (modificationGrading A f₁ f₂)
          (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)
        ≤ Proj.basicOpen (modificationGrading A f₁ f₂) f)
      (z : Away (modificationGrading A f₁ f₂) f),
      ((AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).presheaf.map (homOfLE h).op).hom
        ((Proj.awayToSection (modificationGrading A f₁ f₂) f).hom z)
      = (Proj.awayToSection (modificationGrading A f₁ f₂)
          (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)).hom
        (awayMap (modificationGrading A f₁ f₂) hg hx z) := by
    intro f g hg hx h z
    have hh := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection
      (modificationGrading A f₁ f₂) hg hx) z
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hh
    exact hh.symm
  rw [key (modificationCoord_mem A f₁ f₂ 1) rfl h₀,
    key (modificationCoord_mem A f₁ f₂ 0) (mul_comm _ _) h₁, ← map_add, hz, hw']

/-! ### Higher cohomology of the structure sheaf -/

/-- **Mayer--Vietoris vanishing for a cover by two affine opens with affine intersection.** If a
scheme `X` is the union of two affine opens `U` and `V` whose intersection is affine, and if every
function on `U ⊓ V` is a sum of one restricted from `U` and one restricted from `V`, then the
higher cohomology of `𝒪_X` vanishes.

The glueing hypothesis is the vanishing of the Čech `H¹` of the cover `{U, V}`; everything else is
Serre vanishing on the three affines. In degree at least two the class on `U ⊓ V` produced by
Mayer--Vietoris already vanishes, so the hypothesis is used only in degree one. -/
theorem isZero_hgroup_unit_of_two_affine_cover (X : Scheme.{u}) (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    (hcover : U ⊔ V = ⊤)
    (hglue : ∀ s : Γ(X, U ⊓ V), ∃ (s₀ : Γ(X, U)) (s₁ : Γ(X, V)),
      (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom s₀
        - (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom s₁ = s)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p (SheafOfModules.unit X.ringCatSheaf)) := by
  have hbr : ∀ {W W' : X.Opens} (h : W ≤ W') (z : Γ(X, W')),
      ((secRestrict X.ringCatSheaf h).app (SheafOfModules.unit X.ringCatSheaf)).hom z
        = (X.presheaf.map (homOfLE h).op).hom z := fun _ _ => rfl
  have hvan : ∀ {W : X.Opens}, IsAffineOpen W → ∀ (n : ℕ)
      (x : Hgroup X.ringCatSheaf W (n + 1) (SheafOfModules.unit X.ringCatSheaf)), x = 0 :=
    fun {W} hW n x => @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X _ W hW (n + 1) n.succ_pos)) _ _
  have hzero : ∀ x : (Hgroup X.ringCatSheaf ⊤ p (SheafOfModules.unit X.ringCatSheaf) : Type u),
      x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    have hxU := hvan hU q (Hrestrict X.ringCatSheaf (le_top (a := U)) (q + 1)
      (SheafOfModules.unit X.ringCatSheaf) x)
    have hxV := hvan hV q (Hrestrict X.ringCatSheaf (le_top (a := V)) (q + 1)
      (SheafOfModules.unit X.ringCatSheaf) x)
    obtain ⟨θ, hθ⟩ := exists_ambientDelta_eq X.ringCatSheaf U V
      (SheafOfModules.unit X.ringCatSheaf) ⊤ le_top le_top hcover q x hxU hxV
    rcases q with _ | q'
    · obtain ⟨s₀, s₁, hs⟩ := hglue ((HzeroIso X.ringCatSheaf (U ⊓ V)).hom.app
        (SheafOfModules.unit X.ringCatSheaf) θ)
      obtain ⟨a, ha⟩ :=
        (bijective_Hzero X.ringCatSheaf U (SheafOfModules.unit X.ringCatSheaf)).2 s₀
      obtain ⟨b, hb⟩ :=
        (bijective_Hzero X.ringCatSheaf V (SheafOfModules.unit X.ringCatSheaf)).2 s₁
      have key : θ = Hrestrict X.ringCatSheaf inf_le_left 0
            (SheafOfModules.unit X.ringCatSheaf) a
          - Hrestrict X.ringCatSheaf inf_le_right 0
            (SheafOfModules.unit X.ringCatSheaf) b := by
        refine (bijective_Hzero X.ringCatSheaf (U ⊓ V)
          (SheafOfModules.unit X.ringCatSheaf)).1 ?_
        rw [map_sub, Hzero_Hrestrict, Hzero_Hrestrict, ha, hb, hbr, hbr]
        exact hs.symm
      rw [← hθ, key, ambientDelta_restrict_sub]
    · rw [← hθ, hvan hUV q' θ, map_zero]
  have : Subsingleton (Hgroup X.ringCatSheaf ⊤ p (SheafOfModules.unit X.ringCatSheaf)) :=
    ⟨fun a b => by rw [hzero a, hzero b]⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The two standard charts cover the modification, read as a supremum of two opens. -/
theorem sup_basicOpen_modificationCoord_eq_top :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 0)
        ⊔ Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 1) = ⊤ := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  refine le_antisymm le_top ?_
  rw [← iSup_basicOpen_modificationCoord_eq_top A f₁ f₂]
  exact iSup_le fun i => by fin_cases i <;> [exact le_sup_left; exact le_sup_right]

/-- **Stacks Project, Tag 0EVJ.** `Hᵖ(X', 𝒪_{X'}) = 0` for `p > 0`.

The modification of the two-generator almost blowup square is covered by the two standard affine
opens `D₊(T₀)` and `D₊(T₁)`, whose intersection `D₊(T₀T₁)` is affine too. Mayer--Vietoris
therefore reduces positive-degree cohomology over the whole space to positive-degree cohomology
over those three affines, which vanishes by Serre, plus — in degree one — the surjectivity of
`Stacks.AlmostBlowUp.exists_restrict_add_restrict_eq`. -/
@[stacks 0EVJ "higher cohomology vanishing"]
theorem isZero_hgroup_structureSheaf (p : ℕ) (hp : 0 < p) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsZero (Hgroup (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf ⊤ p
      (SheafOfModules.unit
        (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hmul : Proj.basicOpen (modificationGrading A f₁ f₂)
        (modificationCoord A f₁ f₂ 0 * modificationCoord A f₁ f₂ 1)
      = Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 0)
        ⊓ Proj.basicOpen (modificationGrading A f₁ f₂) (modificationCoord A f₁ f₂ 1) :=
    Proj.basicOpen_mul _ _ _
  refine isZero_hgroup_unit_of_two_affine_cover
    (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)) _ _
    (Proj.isAffineOpen_basicOpen _ _ (modificationCoord_mem A f₁ f₂ 0) Nat.one_pos)
    (Proj.isAffineOpen_basicOpen _ _ (modificationCoord_mem A f₁ f₂ 1) Nat.one_pos)
    (hmul ▸ Proj.isAffineOpen_basicOpen _ _
      (SetLike.mul_mem_graded (modificationCoord_mem A f₁ f₂ 0)
        (modificationCoord_mem A f₁ f₂ 1)) (by omega))
    (sup_basicOpen_modificationCoord_eq_top A f₁ f₂)
    (fun s => by
      obtain ⟨s₀, s₁, hs⟩ :=
        exists_restrict_add_restrict_eq A f₁ f₂ hmul inf_le_left inf_le_right s
      exact ⟨s₀, -s₁, by rw [map_neg, sub_neg_eq_add]; exact hs⟩) p hp

end Stacks.AlmostBlowUp

end
