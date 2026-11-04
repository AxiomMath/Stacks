module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.ProjCharts
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous coordinates on `Proj k[T₀, …, Tₙ]`

Let `k` be a field and `Q = Proj k[T₀, …, Tₙ]`, graded by total degree. For a scheme `T` over `k`
and global functions `c₀, …, cₙ` on `T` generating the unit ideal, evaluation at `c` is a ring map
`k[T₀, …, Tₙ] →+* Γ(T, 𝒪_T)` sending the irrelevant ideal to the unit ideal, hence a morphism
`[c₀ : … : cₙ] : T ⟶ Q`. These morphisms are natural in `T`, invariant under scaling `c` by a
unit, and every morphism `T ⟶ Q` over `k` landing in a standard chart `D₊(Tⱼ)` is of this form.
These are the properties of these morphisms that the representability of a complete linear
system uses.

## Main definitions

* `Stacks.LinearSystemScheme.coordGrading`: the grading of `k[T₀, …, Tₙ]` by total degree.
* `Stacks.LinearSystemScheme.chartElem`: the coordinate function `Tᵢ / Tⱼ` on `D₊(Tⱼ)`.
* `Stacks.LinearSystemScheme.structRingHom`: the ring map `k →+* Γ(T, 𝒪_T)` of a `k`-scheme.
* `Stacks.LinearSystemScheme.coordMor`: the morphism `[c₀ : … : cₙ] : T ⟶ Q`.

## Main results

* `Stacks.LinearSystemScheme.away_mk_eq_eval₂`: a degree-zero fraction `p / Tⱼᵐ` is the
  polynomial `p` evaluated at the coordinate functions `Tᵢ / Tⱼ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.LinearSystemScheme

variable (k : Type u) [Field k] (n : ℕ)

/-- The grading of `k[T₀, …, Tₙ]` by total degree. -/
abbrev coordGrading : ℕ → Submodule k (MvPolynomial (Fin (n + 1)) k) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

variable {k n}

/-- The variable `Tᵢ` is homogeneous of degree `1`. -/
theorem X_mem_coordGrading (i : Fin (n + 1)) : MvPolynomial.X i ∈ coordGrading k n 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k i)

/-- The variable `Tᵢ` is homogeneous of degree `1 • 1`. -/
theorem X_mem_coordGrading' (i : Fin (n + 1)) :
    MvPolynomial.X i ∈ coordGrading k n (1 • 1) := by
  simpa using X_mem_coordGrading (k := k) i

variable (k n)

/-- **The coordinate function `Tᵢ / Tⱼ`** on the standard chart `D₊(Tⱼ)`. -/
def chartElem (j i : Fin (n + 1)) : Away (coordGrading k n) (MvPolynomial.X j) :=
  Away.mk (coordGrading k n) (X_mem_coordGrading j) 1 (MvPolynomial.X i) (X_mem_coordGrading' i)

/-- The ring map `k →+* A_{(Tⱼ)}`. -/
def awayScalars (j : Fin (n + 1)) : k →+* Away (coordGrading k n) (MvPolynomial.X j) :=
  (fromZeroRingHom (coordGrading k n) _).comp (algebraMap k (coordGrading k n 0))

variable {k n}

/-- **A degree-zero fraction is a polynomial in the chart coordinates.** For `p` homogeneous of
degree `m`, `p / Tⱼᵐ = p(T₀ / Tⱼ, …, Tₙ / Tⱼ)` in `A_{(Tⱼ)}`. -/
theorem away_mk_eq_eval₂ (j : Fin (n + 1)) (m : ℕ) (p : MvPolynomial (Fin (n + 1)) k)
    (hp : p ∈ coordGrading k n (m • 1)) :
    Away.mk (coordGrading k n) (X_mem_coordGrading j) m p hp =
      MvPolynomial.eval₂ (awayScalars k n j) (chartElem k n j) p := by
  apply val_injective
  have hhom : p.IsHomogeneous m := by
    simpa using (MvPolynomial.mem_homogeneousSubmodule _ _).mp hp
  let R := MvPolynomial (Fin (n + 1)) k
  let L := Localization.Away (MvPolynomial.X j : R)
  have hunit : IsUnit (algebraMap R L (MvPolynomial.X j)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let v : L := ↑hunit.unit⁻¹
  have hv : algebraMap R L (MvPolynomial.X j) * v = 1 := hunit.unit.mul_inv
  have hsc : ∀ c : k, (awayScalars k n j c).val = algebraMap k L c := by
    intro c
    show (Localization.mk ((algebraMap k (coordGrading k n 0) c : R)) 1 : L) = _
    rw [Localization.mk_one_eq_algebraMap]
    rfl
  have hch : ∀ i, (chartElem k n j i).val = v * algebraMap R L (MvPolynomial.X i) := by
    intro i
    show (Localization.mk (MvPolynomial.X i : R)
      ⟨(MvPolynomial.X j : R) ^ 1, ⟨1, rfl⟩⟩ : L) = _
    rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul, mul_comm v, mul_assoc]
    simp only [pow_one]
    rw [mul_comm v, hv, mul_one]
  have hval : (MvPolynomial.eval₂ (awayScalars k n j) (chartElem k n j) p).val =
      MvPolynomial.eval₂ (algebraMap k L) (fun i => v * algebraMap R L (MvPolynomial.X i)) p := by
    rw [← HomogeneousLocalization.algebraMap_apply, MvPolynomial.eval₂_comp_left]
    have h1 : (algebraMap (Away (coordGrading k n) (MvPolynomial.X j)) L).comp
        (awayScalars k n j) = algebraMap k L := RingHom.ext hsc
    have h2 : (algebraMap (Away (coordGrading k n) (MvPolynomial.X j)) L) ∘ chartElem k n j =
        fun i => v * algebraMap R L (MvPolynomial.X i) := funext hch
    rw [h1, h2]
  rw [hval, hhom.eval₂_const_mul]
  show (Localization.mk p ⟨(MvPolynomial.X j : R) ^ m, ⟨m, rfl⟩⟩ : L) = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  have he : MvPolynomial.eval₂ (algebraMap k L) (fun i => algebraMap R L (MvPolynomial.X i)) p =
      algebraMap R L p := by
    rw [show algebraMap k L = (algebraMap R L).comp MvPolynomial.C from
      IsScalarTower.algebraMap_eq k R L]
    exact (MvPolynomial.eval₂_comp_left (algebraMap R L) MvPolynomial.C MvPolynomial.X p).symm.trans
      (by rw [MvPolynomial.eval₂_eta])
  rw [he]
  show algebraMap R L p = v ^ m * algebraMap R L p * algebraMap R L (MvPolynomial.X j ^ m)
  rw [map_pow, mul_comm (v ^ m), mul_assoc, ← mul_pow, mul_comm v, hv, one_pow, mul_one]

/-! ### The morphism `[c₀ : … : cₙ]` -/

section CoordMor

variable (k n) {T T' : Scheme.{u}} (h : T ⟶ Spec (.of k))

/-- `Proj k[T₀, …, Tₙ]` as a scheme over `Spec k`. -/
abbrev projToSpec : Proj (coordGrading k n) ⟶ Spec (.of k) :=
  toSpecZero (coordGrading k n) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k (coordGrading k n 0)))

/-- The ring map `k →+* Γ(T, 𝒪_T)` of a scheme `T` over `Spec k`. -/
def structRingHom : k →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop).hom

variable {k n}

/-- Evaluation at `c`, as a ring map `k[T₀, …, Tₙ] →+* Γ(T, 𝒪_T)`. -/
def evalHom (c : Fin (n + 1) → Γ(T, ⊤)) : MvPolynomial (Fin (n + 1)) k →+* Γ(T, ⊤) :=
  MvPolynomial.eval₂Hom (structRingHom k h) c

/-- Evaluation at `c` sends the irrelevant ideal to the unit ideal when the `cᵢ` generate it. -/
theorem map_irrelevant_evalHom (c : Fin (n + 1) → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    (HomogeneousIdeal.irrelevant (coordGrading k n)).toIdeal.map (evalHom h c) = ⊤ := by
  rw [eq_top_iff, ← hc, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  have hX : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k) ∈
      (HomogeneousIdeal.irrelevant (coordGrading k n)).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (X_mem_coordGrading i)
  simpa [evalHom] using Ideal.mem_map_of_mem (evalHom h c) hX

/-- **The morphism `[c₀ : … : cₙ] : T ⟶ Proj k[T₀, …, Tₙ]`** of global functions generating the
unit ideal. -/
def coordMor (c : Fin (n + 1) → Γ(T, ⊤)) (hc : Ideal.span (Set.range c) = ⊤) :
    T ⟶ Proj (coordGrading k n) :=
  fromOfGlobalSections (coordGrading k n) (evalHom h c) (map_irrelevant_evalHom h c hc)

/-- `[c₀ : … : cₙ]` is a morphism over `Spec k`. -/
theorem coordMor_comp_projToSpec (c : Fin (n + 1) → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    coordMor h c hc ≫ projToSpec k n = h := by
  rw [coordMor, projToSpec, fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have : ((evalHom h c).comp (algebraMap (coordGrading k n 0) (MvPolynomial (Fin (n + 1)) k))).comp
      (algebraMap k (coordGrading k n 0)) = structRingHom k h := by
    ext a
    simp [evalHom]
  rw [this, structRingHom, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The preimage of `D₊(Tⱼ)` under `[c₀ : … : cₙ]` is `T_{cⱼ}`. -/
theorem coordMor_preimage_basicOpen (c : Fin (n + 1) → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (j : Fin (n + 1)) :
    coordMor h c hc ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = T.basicOpen (c j) := by
  rw [coordMor, fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos (X_mem_coordGrading j)]
  simp [evalHom]

/-- The preimage of `D₊(Tⱼ)` under `[c₀ : … : cₙ]` is everything when `cⱼ = 1`. -/
private theorem coordMor_preimage_basicOpen_eq_top (c : Fin (n + 1) → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (j : Fin (n + 1)) (hcj : c j = 1) :
    coordMor h c hc ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤ := by
  rw [coordMor_preimage_basicOpen, hcj, Scheme.basicOpen_one]

/-- If `c₀, …, cₙ` generate the unit ideal of `Γ(T, 𝒪_T)`, then so do their pullbacks
`g^♯(c₀), …, g^♯(cₙ)` along `g : T' ⟶ T`. -/
theorem span_range_comp_eq_top (g : T' ⟶ T) (c : Fin (n + 1) → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    Ideal.span (Set.range (fun i => g.appTop (c i))) = ⊤ := by
  have := congrArg (Ideal.map g.appTop.hom) hc
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

/-- The structure ring map of `g ≫ h` is that of `h` followed by
`g^♯ : Γ(T, 𝒪_T) → Γ(T', 𝒪_T')`. -/
theorem structRingHom_comp (g : T' ⟶ T) :
    structRingHom k (g ≫ h) = g.appTop.hom.comp (structRingHom k h) := by
  ext a
  simp only [structRingHom, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

/-- The morphism `T ⟶ Proj k[T₀, …, Tₙ]` of a ring map on global sections depends only on the
ring map. -/
theorem fromOfGlobalSections_congr' {f f' : MvPolynomial (Fin (n + 1)) k →+* Γ(T, ⊤)}
    (e : f = f') (hf) (hf') :
    fromOfGlobalSections (coordGrading k n) f hf =
      fromOfGlobalSections (coordGrading k n) f' hf' := by
  subst e
  rfl

/-- **`[c₀ : … : cₙ]` is natural in `T`**: precomposing with `g : T' ⟶ T` pulls the coordinates
back. -/
theorem comp_coordMor (g : T' ⟶ T) (c : Fin (n + 1) → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) :
    g ≫ coordMor h c hc =
      coordMor (g ≫ h) (fun i => g.appTop (c i)) (span_range_comp_eq_top g c hc) := by
  rw [coordMor, Proj.comp_fromOfGlobalSections _ g _ _
    (Proj.map_irrelevant_comp_appTop_eq_top _ g _ (map_irrelevant_evalHom h c hc)), coordMor]
  refine fromOfGlobalSections_congr' ?_ _ _
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · simp [evalHom, structRingHom_comp]
  · simp [evalHom]

/-- **`[c₀ : … : cₙ]` is unchanged when the coordinates are scaled by a unit.** -/
theorem coordMor_unit_mul (c : Fin (n + 1) → Γ(T, ⊤)) (hc : Ideal.span (Set.range c) = ⊤)
    (u : Γ(T, ⊤)ˣ) (hc' : Ideal.span (Set.range (fun i => (u : Γ(T, ⊤)) * c i)) = ⊤) :
    coordMor h (fun i => (u : Γ(T, ⊤)) * c i) hc' = coordMor h c hc := by
  refine (Proj.fromOfGlobalSections_congr_unit (coordGrading k n) _ _ u ?_ _ _).symm
  intro m a ha
  exact ((MvPolynomial.mem_homogeneousSubmodule _ _).mp ha).eval₂Hom_const_mul _ _ _

/-- **The chart coordinates `g^♯(Tᵢ / Tⱼ)`** of a morphism `g : T ⟶ Proj k[T₀, …, Tₙ]` landing in
`D₊(Tⱼ)`. -/
def chartCoords (g : T ⟶ Proj (coordGrading k n)) (j : Fin (n + 1))
    (hg : g ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) (i : Fin (n + 1)) :
    Γ(T, ⊤) :=
  (awayToSection (coordGrading k n) (MvPolynomial.X j) ≫
    g.appLE (basicOpen (coordGrading k n) (MvPolynomial.X j)) ⊤ hg.ge).hom (chartElem k n j i)

/-- The coordinate function `Tⱼ / Tⱼ` on `D₊(Tⱼ)` is `1`. -/
theorem chartElem_self (j : Fin (n + 1)) : chartElem k n j j = 1 := by
  apply val_injective
  simp [chartElem]

/-- The `j`-th chart coordinate of a morphism landing in `D₊(Tⱼ)` is `1`. -/
theorem chartCoords_self (g : T ⟶ Proj (coordGrading k n)) (j : Fin (n + 1))
    (hg : g ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) :
    chartCoords g j hg j = 1 := by
  rw [chartCoords, chartElem_self, map_one]

/-- The chart coordinates of a morphism landing in `D₊(Tⱼ)` generate the unit ideal. -/
theorem span_range_chartCoords (g : T ⟶ Proj (coordGrading k n)) (j : Fin (n + 1))
    (hg : g ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) :
    Ideal.span (Set.range (chartCoords g j hg)) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩)
    (by rw [chartCoords_self]; exact isUnit_one)

/-- The chart coordinates of `g' ≫ g` are the pullbacks along `g'` of those of `g`. -/
theorem chartCoords_comp (g' : T' ⟶ T) (g : T ⟶ Proj (coordGrading k n)) (j : Fin (n + 1))
    (hg : g ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤)
    (hg' : (g' ≫ g) ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) (i : Fin (n + 1)) :
    chartCoords (g' ≫ g) j hg' i = g'.appTop (chartCoords g j hg i) := by
  have e : g.appLE (basicOpen (coordGrading k n) (MvPolynomial.X j)) ⊤ hg.ge ≫ g'.appTop =
      (g' ≫ g).appLE (basicOpen (coordGrading k n) (MvPolynomial.X j)) ⊤ hg'.ge := by
    refine (congrArg
      (fun m => g.appLE (basicOpen (coordGrading k n) (MvPolynomial.X j)) ⊤ hg.ge ≫ m)
      (Stacks.AlgebraicGeometry.ProjTwistChain.appLE_top_top g' le_top).symm).trans ?_
    exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  simp only [chartCoords, ← e, CommRingCat.hom_comp, RingHom.comp_apply]

/-- The ring map `A_{(Tⱼ)} →+* Γ(T, 𝒪_T)` of chart coordinates `c` with `cⱼ = 1`. -/
def chartAwayHom (c : Fin (n + 1) → Γ(T, ⊤)) (j : Fin (n + 1)) (hcj : c j = 1) :
    Away (coordGrading k n) (MvPolynomial.X j) →+* Γ(T, ⊤) :=
  (Localization.awayLift (evalHom h c) (MvPolynomial.X j)
    (by simp [evalHom, hcj])).comp (algebraMap _ (Localization.Away _))

/-- `chartAwayHom` sends the degree-zero fraction `p / Tⱼᵐ` to `p(c₀, …, cₙ)`. -/
theorem chartAwayHom_mk (c : Fin (n + 1) → Γ(T, ⊤)) (j : Fin (n + 1)) (hcj : c j = 1) (m : ℕ)
    (p : MvPolynomial (Fin (n + 1)) k) (hp : p ∈ coordGrading k n (m • 1)) :
    chartAwayHom h c j hcj (Away.mk (coordGrading k n) (X_mem_coordGrading j) m p hp) =
      evalHom h c p := by
  rw [chartAwayHom, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  exact (Localization.awayLift_mk (evalHom h c) (MvPolynomial.X j) p 1
    (by simp [evalHom, hcj]) m).trans (by rw [one_pow, mul_one])

/-- **The chart coordinates of `[c₀ : … : cₙ]` in the chart `D₊(Tⱼ)`, when `cⱼ = 1`, are `c`.**
More precisely its chart ring map is `chartAwayHom`. -/
theorem awayToSection_comp_appLE_coordMor (c : Fin (n + 1) → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (j : Fin (n + 1)) (hcj : c j = 1)
    (hg : coordMor h c hc ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) :
    awayToSection (coordGrading k n) (MvPolynomial.X j) ≫
        (coordMor h c hc).appLE (basicOpen (coordGrading k n) (MvPolynomial.X j)) ⊤ hg.ge =
      CommRingCat.ofHom (chartAwayHom h c j hcj) := by
  have hV : T.basicOpen (evalHom h c (MvPolynomial.X j)) = ⊤ := by
    simp [evalHom, hcj]
  have h1 := awayToSection_comp_appLE_fromOfGlobalSections (evalHom h c)
    (map_irrelevant_evalHom h c hc) one_pos (X_mem_coordGrading (k := k) j)
  have h2 : (coordMor h c hc).appLE (basicOpen (coordGrading k n) (MvPolynomial.X j)) ⊤ hg.ge =
      (coordMor h c hc).appLE (basicOpen (coordGrading k n) (MvPolynomial.X j))
        (T.basicOpen (evalHom h c (MvPolynomial.X j)))
        (fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos (X_mem_coordGrading j)).ge ≫
        T.presheaf.map (homOfLE hV.ge).op :=
    (Scheme.Hom.appLE_map _ _ _).symm
  have he : evalHom h c (MvPolynomial.X j) = 1 := by simp [evalHom, hcj]
  rw [h2, ← Category.assoc]
  refine (congrArg (fun m => m ≫ T.presheaf.map (homOfLE hV.ge).op) h1).trans ?_
  ext x
  obtain ⟨m, p, hp, rfl⟩ := Away.mk_surjective (coordGrading k n) (X_mem_coordGrading j) x
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [chartAwayHom_mk,
    Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one _ _ _ m p hp
      (v := 1) (by rw [mul_one]; exact (congrArg _ he).trans (map_one _)), one_pow, mul_one,
    Stacks.ProjGlobalSectionsAppTop.resTop, ← CommRingCat.comp_apply, ← Functor.map_comp,
    show ((homOfLE (le_top (a := T.basicOpen (evalHom h c (MvPolynomial.X j))))).op ≫
      (homOfLE hV.ge).op : Opposite.op (⊤ : T.Opens) ⟶ Opposite.op ⊤) = 𝟙 _ from
    Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
  rfl

/-- **On constants the chart ring map of a morphism over `Spec k` is the structure map.** -/
theorem chartRingHom_awayScalars {W : Scheme.{u}} (hW : W ⟶ Spec (.of k))
    (g : W ⟶ Proj (coordGrading k n)) (hgk : g ≫ projToSpec k n = hW) (j : Fin (n + 1))
    (hg : g ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) (a : k) :
    (awayToSection (coordGrading k n) (MvPolynomial.X j) ≫
        g.appLE (basicOpen (coordGrading k n) (MvPolynomial.X j)) ⊤ hg.ge).hom
        (awayScalars k n j a) = structRingHom k hW a := by
  have e := awayToSection_comp_appLE_fromZeroRingHom one_pos (X_mem_coordGrading (k := k) j) g hg
  have e' := congrArg (fun m => m.hom (algebraMap k (coordGrading k n 0) a)) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e'
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, awayScalars]
  rw [e', structRingHom, ← hgk, projToSpec, ← Category.assoc, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  refine congrArg (g ≫ toSpecZero (coordGrading k n)).appTop.hom ?_
  exact congrArg (fun m => m.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (coordGrading k n 0))))

/-- **Recognition of `[c₀ : … : cₙ]`.** A morphism `g : W ⟶ Proj k[T₀, …, Tₙ]` over `Spec k`
landing in `D₊(Tⱼ)` is `[c₀ : … : cₙ]` for its chart coordinates `cᵢ = g^♯(Tᵢ / Tⱼ)`. -/
theorem eq_coordMor_chartCoords {W : Scheme.{u}} (hW : W ⟶ Spec (.of k))
    (g : W ⟶ Proj (coordGrading k n)) (hgk : g ≫ projToSpec k n = hW) (j : Fin (n + 1))
    (hg : g ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) :
    g = coordMor hW (chartCoords g j hg) (span_range_chartCoords g j hg) := by
  have hcj := chartCoords_self g j hg
  have hg' := coordMor_preimage_basicOpen_eq_top hW _ (span_range_chartCoords g j hg) j hcj
  refine eq_of_awayToSection_comp_appLE_eq one_pos (X_mem_coordGrading j) hg hg' ?_
  rw [awayToSection_comp_appLE_coordMor hW _ _ j hcj hg']
  ext x
  obtain ⟨m, p, hp, rfl⟩ := Away.mk_surjective (coordGrading k n) (X_mem_coordGrading j) x
  rw [CommRingCat.hom_ofHom, chartAwayHom_mk, away_mk_eq_eval₂, MvPolynomial.hom_eval₂]
  simp only [evalHom, MvPolynomial.coe_eval₂Hom]
  congr 1
  ext a
  exact chartRingHom_awayScalars hW g hgk j hg a

/-- The chart coordinates of equal morphisms are equal. -/
theorem chartCoords_congr {g g' : T ⟶ Proj (coordGrading k n)} (e : g = g') (j : Fin (n + 1))
    (hg : g ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤)
    (hg' : g' ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) :
    chartCoords g j hg = chartCoords g' j hg' := by
  subst e
  rfl

/-- **The chart coordinates of `[c₀ : … : cₙ]` with `cⱼ = 1` are the `cᵢ`.** -/
theorem chartCoords_coordMor (c : Fin (n + 1) → Γ(T, ⊤)) (hc : Ideal.span (Set.range c) = ⊤)
    (j : Fin (n + 1)) (hcj : c j = 1)
    (hg : coordMor h c hc ⁻¹ᵁ basicOpen (coordGrading k n) (MvPolynomial.X j) = ⊤) :
    chartCoords (coordMor h c hc) j hg = c := by
  funext i
  rw [chartCoords, awayToSection_comp_appLE_coordMor h c hc j hcj hg, CommRingCat.hom_ofHom,
    chartElem, chartAwayHom_mk]
  simp [evalHom]

/-- **Proportionality.** If `[c₀ : … : cₙ] = [c'₀ : … : c'ₙ]`, `c'ₗ = 1` and `cₗ` is a unit, then
`c' = cₗ⁻¹ · c`. -/
theorem eq_inv_mul_of_coordMor_eq (c c' : Fin (n + 1) → Γ(T, ⊤))
    (hc : Ideal.span (Set.range c) = ⊤) (hc' : Ideal.span (Set.range c') = ⊤)
    (e : coordMor h c hc = coordMor h c' hc') (l : Fin (n + 1)) (hc'l : c' l = 1)
    (u : Γ(T, ⊤)ˣ) (hu : (u : Γ(T, ⊤)) = c l) :
    c' = fun i => (↑u⁻¹ : Γ(T, ⊤)) * c i := by
  have hc'' : Ideal.span (Set.range (fun i => (↑u⁻¹ : Γ(T, ⊤)) * c i)) = ⊤ := by
    rw [eq_top_iff, ← hc, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : c i = (u : Γ(T, ⊤)) * ((↑u⁻¹ : Γ(T, ⊤)) * c i) := by
      rw [← mul_assoc, Units.mul_inv, one_mul]
    rw [SetLike.mem_coe, this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have e2 : coordMor h (fun i => (↑u⁻¹ : Γ(T, ⊤)) * c i) hc'' = coordMor h c' hc' :=
    (coordMor_unit_mul h c hc u⁻¹ hc'').trans e
  have h1l : (fun i => (↑u⁻¹ : Γ(T, ⊤)) * c i) l = 1 := by
    simp only [← hu, Units.inv_mul]
  have hg' := coordMor_preimage_basicOpen_eq_top h c' hc' l hc'l
  have hg'' := coordMor_preimage_basicOpen_eq_top h _ hc'' l h1l
  rw [← chartCoords_coordMor h c' hc' l hc'l hg',
    ← chartCoords_coordMor h _ hc'' l h1l hg'']
  exact chartCoords_congr e2.symm l hg' hg''

end CoordMor

end Stacks.LinearSystemScheme

end
