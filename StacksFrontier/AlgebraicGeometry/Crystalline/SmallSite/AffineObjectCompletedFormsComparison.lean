module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamFormsDataCompletion
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectFormsDPNaturality
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalConnection

/-!
# The completed divided power forms of a divided power algebra over an affine object

Let `(p, (S, I, γ), X)` be a global crystalline situation with `S` affine, let `B = (U, T, δ)` be
an object of `CRIS(X/S)` with `T` affine, and let `(E, J, h)` be a divided power algebra over
`Γ(S, 𝒪_S)` in which `p` is nilpotent, with a divided power morphism
`θ₀ : (E, J, h) → (Γ(T, 𝒪_T), δ)` of `Γ(S, 𝒪_S)`-algebras (the algebra structure on `Γ(T, 𝒪_T)`
is `...crysTopAlgebra`, the one [Stacks, Tag 07J0] is stated under at `V = ⊤`).  This file
compares the ring with forms `Crystalline.FormsData.ofDividedPowers p Γ(S, 𝒪_S) h` — the
completion `Ê` with the completed divided power forms `Ω̂^*_E` — with the crystalline forms
`Ω^*_{X/S}` at `B`:

* `...formsRingHom : Ê →+* Γ(T, 𝒪_T)` is the inverse of `AdicCompletion.of`, bijective because
  `p` is nilpotent (`Crystalline.pAdicOfRingEquiv`), followed by `θ₀`;
* `...formsHom a : Ω̂^a_E → ⋀^a Ω_{X/S}(B)` is the inverse of `AdicCompletion.of`, the
  functoriality `Crystalline.mapDifferentialFormsOfDPMorphism` along `θ₀`, and the `a`-th exterior
  power of the inverse `...affineFormsOneInv` of [Stacks, Tag 07J0]; `...formsOneHom` is its
  degree-one case read through `exteriorPower.oneEquiv`.

## Main results

* `...formsOneHom_diff`, `...formsHom_wedge`, `...formsHom_deRham` — `formsHom` carries the
  universal differential, the wedge product and the de Rham differential of `Ω̂^*_E` to `d_{X/S}`,
  `Crystalline.leftWedge` and the crystalline de Rham differential
  `(crysDeRhamComplex S).differential` of [Stacks, Tag 07J4]; `...formsHom_ιMulti_d` computes it
  on the wedges `d e₁ ∧ ⋯ ∧ d e_a`.
* `...formsRingHom_bijective`, `...formsHom_bijective`, `...formsOneHom_bijective` — all three
  maps are bijective when `θ₀` is bijective (for the ring map), resp. has an inverse which is a
  divided power morphism too (for the forms).
* `...formsHom_naturality_succ`, `...formsOneHom_naturality` — naturality: for a second datum
  `(B', E', h', θ₀')`, a morphism `k : B ⟶ B'` and a morphism `g` of rings with forms with
  `formsRingHom θ₀ ∘ g = crysRingMap k ∘ formsRingHom θ₀'`, the comparison of forms after
  `g.psi` is the transition map along `k` after the comparison, in every positive degree and in
  degree one for `Ω_{X/S}` itself.  In degree zero (`...formsHom_naturality_zero`,
  `...formsHom_naturality`) the same holds under the extra hypothesis that `g.psi 0` fixes the
  unit zero-form; the axioms of `Crystalline.FormsData.Hom` do not imply it.

Everything is first proved for an arbitrary divided power morphism `θ : E → C` and an arbitrary
linear map `g : Ω¹_{C,δ} → M` (`Crystalline.completedFormsHom` and its lemmas), and then
specialised.  The specialisation is where the two spellings of the ring `Γ(T, 𝒪_T)` meet (see
the implementation notes of `AffineObjectDifferentialForms.lean`); working with the generic maps
keeps every elaboration problem on one spelling.

## What is not proved

Nothing here is a tag of the Stacks project, and no tag attribute is placed.  The comparison is
not assembled into a morphism of complexes or of rings with forms, and the degree-zero
naturality needs its stated hypothesis on the unit zero-form.

## References

* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite DividedPowers

universe u

namespace Crystalline

section Nilpotent

variable (p : ℕ) {E : Type*} [CommRing E] (hE : ∃ k, (p : E) ^ k = 0)

/-- If `p` is nilpotent in `E`, some power of the ideal `(p)` vanishes. -/
theorem pAdicIdeal_pow_eq_bot : pAdicIdeal (A := E) p ^ hE.choose = ⊥ := by
  rw [pAdicIdeal, Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
  exact hE.choose_spec

/-- A module is adically complete along an ideal some power of which vanishes. -/
theorem isAdicComplete_module_of_pow_eq_bot {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {k : ℕ} (hk : I ^ k = ⊥) : IsAdicComplete I M := by
  have hzero : ∀ {x y : M}, x ≡ y [SMOD (I ^ k • ⊤ : Submodule R M)] → x = y := by
    intro x y h
    rwa [hk, Submodule.bot_smul, SModEq.bot] at h
  have hh : IsHausdorff I M := ⟨fun x hx => hzero (hx k)⟩
  have hp : IsPrecomplete I M := by
    refine ⟨fun f hf => ⟨f k, fun n => ?_⟩⟩
    rcases le_or_gt n k with hn | hn
    · exact hf hn
    · rw [hzero (hf hn.le)]
  exact ⟨⟩

/-- **With `p` nilpotent, a module is its own `p`-adic completion**, through
`AdicCompletion.of`. -/
def pAdicOfEquiv (M : Type*) [AddCommGroup M] [Module E M] :
    M ≃ₗ[E] AdicCompletion (pAdicIdeal (A := E) p) M :=
  haveI := isAdicComplete_module_of_pow_eq_bot (M := M) _ (pAdicIdeal_pow_eq_bot p hE)
  AdicCompletion.ofLinearEquiv _ M

/-- The identification `pAdicOfEquiv` is `AdicCompletion.of`. -/
@[simp] theorem pAdicOfEquiv_apply (M : Type*) [AddCommGroup M] [Module E M] (m : M) :
    pAdicOfEquiv p hE M m = AdicCompletion.of _ M m := rfl

/-- **With `p` nilpotent, a ring is its own `p`-adic completion, as a ring.** -/
def pAdicOfRingEquiv : E ≃+* AdicCompletion (pAdicIdeal (A := E) p) E :=
  RingEquiv.ofBijective (algebraMap E (AdicCompletion (pAdicIdeal (A := E) p) E)) (by
    have h : ⇑(algebraMap E (AdicCompletion (pAdicIdeal (A := E) p) E)) =
        pAdicOfEquiv p hE E := funext fun e ↦ by
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rfl
    rw [h]
    exact (pAdicOfEquiv p hE E).bijective)

/-- The ring identification `pAdicOfRingEquiv` is `AdicCompletion.of`. -/
@[simp] theorem pAdicOfRingEquiv_apply (e : E) :
    pAdicOfRingEquiv p hE e = AdicCompletion.of _ E e := by
  rw [pAdicOfRingEquiv, RingEquiv.ofBijective_apply, AdicCompletion.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- The inverse of the identification of a module with its completion is semilinear over the
inverse of the identification of the ring with its completion. -/
theorem pAdicOfEquiv_symm_smul (M : Type*) [AddCommGroup M] [Module E M]
    (x : AdicCompletion (pAdicIdeal (A := E) p) E)
    (y : AdicCompletion (pAdicIdeal (A := E) p) M) :
    (pAdicOfEquiv p hE M).symm (x • y) =
      (pAdicOfRingEquiv p hE).symm x • (pAdicOfEquiv p hE M).symm y := by
  obtain ⟨e, rfl⟩ := (pAdicOfRingEquiv p hE).surjective x
  obtain ⟨m, rfl⟩ := (pAdicOfEquiv p hE M).surjective y
  rw [RingEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, pAdicOfRingEquiv,
    RingEquiv.ofBijective_apply, algebraMap_smul, ← map_smul, LinearEquiv.symm_apply_apply]

/-- `AdicCompletion.of` carries a scalar to the scalar `pAdicOfRingEquiv`. -/
theorem pAdicOf_smul (M : Type*) [AddCommGroup M] [Module E M] (e : E) (m : M) :
    AdicCompletion.of (pAdicIdeal (A := E) p) M (e • m) =
      pAdicOfRingEquiv p hE e • AdicCompletion.of (pAdicIdeal (A := E) p) M m := by
  rw [pAdicOfRingEquiv, RingEquiv.ofBijective_apply, algebraMap_smul, map_smul]

end Nilpotent

/-! ### Exterior powers of a map out of the divided power differentials -/

section ExteriorPowerMap

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] {K : Ideal C}
  (hK : DividedPowers K) {N M : Type*} [AddCommGroup N] [Module C N] [AddCommGroup M] [Module C M]

/-- **The exterior powers of a linear map respect left exterior multiplication.** -/
theorem exteriorPower_map_leftWedge (f : N →ₗ[C] M) (a : ℕ) (x : N) (z : ⋀[C]^a N) :
    exteriorPower.map (a + 1) f (leftWedge a x z) =
      leftWedge a (f x) (exteriorPower.map a f z) := by
  apply Subtype.ext
  rw [exteriorPower.coe_map, leftWedge_coe, leftWedge_coe, exteriorPower.coe_map, map_mul,
    ExteriorAlgebra.map_apply_ι]

/-- **In degree one the exterior power of a linear map is the map**, through
`exteriorPower.oneEquiv`. -/
theorem oneEquiv_exteriorPower_map (f : N →ₗ[C] M) (z : ⋀[C]^1 N) :
    exteriorPower.oneEquiv C M (exteriorPower.map 1 f z) = f (exteriorPower.oneEquiv C N z) := by
  obtain ⟨x, rfl⟩ := (exteriorPower.oneEquiv C N).symm.surjective z
  rw [exteriorPower.oneEquiv_symm_apply, exteriorPower.map_apply_ιMulti,
    exteriorPower.oneEquiv_ιMulti, exteriorPower.oneEquiv_ιMulti]
  rfl

/-- The exterior powers of a bijective linear map are bijective. -/
theorem exteriorPower_map_bijective (f : N →ₗ[C] M) (hf : Function.Bijective f) (a : ℕ) :
    Function.Bijective (exteriorPower.map a f) :=
  (exteriorPowerCongr a (LinearEquiv.ofBijective f hf)).bijective

/-- **A criterion for the exterior powers of a map out of the divided power differentials to
intertwine the divided power de Rham differential with a given differential `D`**: it suffices
that `D` obeys the Leibniz rule against the images of the universal differentials and the rule
`D (c₀ · d c₁ ∧ ⋯ ∧ d c_a) = d c₀ ∧ ⋯ ∧ d c_a` on the images of the standard generators. -/
theorem exteriorPower_map_dividedPowerDeRham
    (f : dividedPowerDifferentials (A := A) hK →ₗ[C] M) (a : ℕ)
    (D : ⋀[C]^a M →+ ⋀[C]^(a + 1) M)
    (hsmul : ∀ (c : C) (ω : ⋀[C]^a M),
      D (c • ω) = c • D ω + leftWedge a (f (dividedPowerDifferential (A := A) hK c)) ω)
    (hgen : ∀ c : Fin (a + 1) → C,
      D (c 0 • exteriorPower.ιMulti C a fun j ↦
          f (dividedPowerDifferential (A := A) hK (c j.succ))) =
        exteriorPower.ιMulti C (a + 1) fun j ↦ f (dividedPowerDifferential (A := A) hK (c j)))
    (z : dividedPowerDifferentialForms (A := A) hK a) :
    exteriorPower.map (a + 1) f (dividedPowerDeRham hK a z) = D (exteriorPower.map a f z) := by
  have hz : z ∈ Submodule.span C (Set.range fun c : Fin (a + 1) → C ↦
      c 0 • exteriorPower.ιMulti C a fun j ↦ dividedPowerDifferential (A := A) hK (c j.succ)) := by
    rw [span_range_smul_ιMulti_eq_top (R := C) (dividedPowerDifferential (A := A) hK)
      (dividedPowerDifferentials_span hK) a]
    trivial
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      rw [dividedPowerDeRham_generator, exteriorPower.map_apply_ιMulti, LinearMap.map_smul,
        exteriorPower.map_apply_ιMulti]
      exact (hgen c).symm
  | zero => rw [dividedPowerDeRham_zero, map_zero, map_zero, map_zero]
  | add y y' _ _ hy hy' => rw [dividedPowerDeRham_add, map_add, hy, hy', map_add, map_add]
  | smul c y _ hy =>
      rw [dividedPowerDeRham_smul, map_add, LinearMap.map_smul, hy,
        exteriorPower_map_leftWedge, LinearMap.map_smul, hsmul]

end ExteriorPowerMap

/-! ### The generators of the completed forms -/

section Generators

variable (p : ℕ) (A : Type u) [CommRing A] {E : Type u} [CommRing E] [Algebra A E]
  {J : Ideal E} (h : DividedPowers J)

/-- The universal differential of the completed forms on the image of an element is the image of
the one-form `d e`, written as a wedge of length one. -/
theorem ofDividedPowers_diff_of (e : E) :
    (FormsData.ofDividedPowers p A h).diff (AdicCompletion.of _ E e) =
      AdicCompletion.of _ _ (exteriorPower.ιMulti E 1 fun _ ↦
        dividedPowerDifferential (A := A) h e) := by
  change completedFormsDifferential p A h (AdicCompletion.of _ E e) = _
  rw [completedFormsDifferential_of, dividedPowerOneForm_apply, exteriorPower.oneEquiv_symm_apply]

/-- **A wedge `d e₀ ∧ d e₁ ∧ ⋯ ∧ d e_a` of universal differentials in the completed forms is the
wedge product of `d e₁ ∧ ⋯ ∧ d e_a` with `d e₀`.** -/
theorem ofDividedPowers_wedge_of_ιMulti (a : ℕ) (e : Fin (a + 1) → E) :
    (FormsData.ofDividedPowers p A h).wedge a
        (AdicCompletion.of _ _ (exteriorPower.ιMulti E a fun j ↦
          dividedPowerDifferential (A := A) h (e j.succ)))
        ((FormsData.ofDividedPowers p A h).diff (AdicCompletion.of _ E (e 0))) =
      AdicCompletion.of _ _ (exteriorPower.ιMulti E (a + 1) fun j ↦
        dividedPowerDifferential (A := A) h (e j)) := by
  rw [ofDividedPowers_diff_of]
  change completedDividedPowerWedge p A h a (AdicCompletion.of _ _ _) (AdicCompletion.of _ _ _) = _
  rw [completedDividedPowerWedge_of_of, dividedPowerWedge_apply, exteriorPower.oneEquiv_ιMulti,
    leftWedge_ιMulti]
  exact congrArg (fun v ↦ AdicCompletion.of _ _ (exteriorPower.ιMulti E (a + 1) v))
    (Fin.cons_self_tail fun j ↦ dividedPowerDifferential (A := A) h (e j))

/-- **The empty wedge is the unit zero-form**, in the completed forms. -/
theorem of_ιMulti_zero_eq_completedUnitZeroForm
    (v : Fin 0 → dividedPowerDifferentials (A := A) h) :
    AdicCompletion.of (pAdicIdeal (A := E) p) _ (exteriorPower.ιMulti E 0 v) =
      completedUnitZeroForm p A h := by
  refine congrArg (AdicCompletion.of (pAdicIdeal (A := E) p) _) (Subtype.ext ?_)
  rw [coe_unitZeroForm, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]

end Generators

/-! ### The comparison of the completed forms along a divided power morphism -/

section CompletedForms

variable (p : ℕ) {A : Type u} [CommRing A] {E : Type u} [CommRing E] [Algebra A E]
  {J : Ideal E} {h : DividedPowers J} (hE : ∃ k, (p : E) ^ k = 0)
  {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C} {hK : DividedPowers K}
  (θ : E →ₐ[A] C) (hθ : IsDPMorphism h hK θ.toRingHom)
  {M : Type*} [AddCommGroup M] [Module C M] (g : dividedPowerDifferentials (A := A) hK →ₗ[C] M)

/-- **The ring map `Ê → C`** of a divided power morphism `θ : E → C` out of a ring in which `p`
is nilpotent: the inverse of `AdicCompletion.of`, bijective because `p` is nilpotent, followed
by `θ`. -/
def completedFormsRingHom : AdicCompletion (pAdicIdeal (A := E) p) E →+* C :=
  θ.toRingHom.comp (pAdicOfRingEquiv p hE).symm.toRingHom

/-- `completedFormsRingHom` extends `θ`. -/
@[simp] theorem completedFormsRingHom_of (e : E) :
    completedFormsRingHom p hE θ (AdicCompletion.of _ E e) = θ e := by
  change θ ((pAdicOfRingEquiv p hE).symm (AdicCompletion.of _ E e)) = θ e
  rw [← pAdicOfRingEquiv_apply p hE e, RingEquiv.symm_apply_apply]

/-- `completedFormsRingHom` is bijective when `θ` is. -/
theorem completedFormsRingHom_bijective (hθb : Function.Bijective θ) :
    Function.Bijective (completedFormsRingHom p hE θ) :=
  hθb.comp (pAdicOfRingEquiv p hE).symm.bijective

/-- **The comparison of forms `Ω̂^a_E → ⋀^a_C M`** along a divided power morphism `θ : E → C`
and a linear map `g : Ω¹_{C/A} → M`: the inverse of `AdicCompletion.of` (`p` is nilpotent in
`E`), the functoriality `Crystalline.mapDifferentialFormsOfDPMorphism` of divided power forms
along `θ`, and the `a`-th exterior power of `g`.  It is semilinear over
`completedFormsRingHom`. -/
def completedFormsHom (a : ℕ) :
    (FormsData.ofDividedPowers p A h).Om a →ₛₗ[completedFormsRingHom p hE θ] ⋀[C]^a M where
  toFun ω := exteriorPower.map a g
    (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := h) hK θ hθ a
      ((pAdicOfEquiv p hE _).symm ω))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    rw [pAdicOfEquiv_symm_smul, map_smulₛₗ, LinearMap.map_smul]
    rfl

/-- `completedFormsHom` on the image of an uncompleted form. -/
theorem completedFormsHom_of (a : ℕ) (w : dividedPowerDifferentialForms (A := A) h a) :
    completedFormsHom p hE θ hθ g a (AdicCompletion.of _ _ w) =
      exteriorPower.map a g
        (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := h) hK θ hθ a w) := by
  change exteriorPower.map a g
    (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := h) hK θ hθ a
      ((pAdicOfEquiv p hE _).symm (pAdicOfEquiv p hE _ w))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- **`completedFormsHom` on a wedge of universal differentials**: `d e₁ ∧ ⋯ ∧ d e_a` goes to
`g (d θ(e₁)) ∧ ⋯ ∧ g (d θ(e_a))`. -/
theorem completedFormsHom_ιMulti_d (a : ℕ) (e : Fin a → E) :
    completedFormsHom p hE θ hθ g a (AdicCompletion.of _ _ (exteriorPower.ιMulti E a fun j ↦
        dividedPowerDifferential (A := A) h (e j))) =
      exteriorPower.ιMulti C a fun j ↦ g (dividedPowerDifferential (A := A) hK (θ (e j))) := by
  rw [completedFormsHom_of, mapDifferentialFormsOfDPMorphism_ιMulti_d,
    exteriorPower.map_apply_ιMulti]
  rfl

/-- **`completedFormsHom` in degree one on the universal differential.** -/
theorem completedFormsHom_diff (x : (FormsData.ofDividedPowers p A h).ring) :
    completedFormsHom p hE θ hθ g 1 ((FormsData.ofDividedPowers p A h).diff x) =
      exteriorPower.ιMulti C 1 fun _ ↦
        g (dividedPowerDifferential (A := A) hK (completedFormsRingHom p hE θ x)) := by
  obtain ⟨e, rfl⟩ := (pAdicOfRingEquiv p hE).surjective x
  rw [pAdicOfRingEquiv_apply, completedFormsRingHom_of, ofDividedPowers_diff_of,
    completedFormsHom_ιMulti_d]

/-- **`completedFormsHom` carries the universal differential to `g ∘ d`**, read through
`exteriorPower.oneEquiv`. -/
theorem oneEquiv_completedFormsHom_diff (x : (FormsData.ofDividedPowers p A h).ring) :
    exteriorPower.oneEquiv C M
        (completedFormsHom p hE θ hθ g 1 ((FormsData.ofDividedPowers p A h).diff x)) =
      g (dividedPowerDifferential (A := A) hK (completedFormsRingHom p hE θ x)) := by
  rw [completedFormsHom_diff, exteriorPower.oneEquiv_ιMulti]

/-- **`completedFormsHom` respects the wedge product.** -/
theorem completedFormsHom_wedge (a : ℕ) (ω : (FormsData.ofDividedPowers p A h).Om a)
    (η : (FormsData.ofDividedPowers p A h).Om 1) :
    completedFormsHom p hE θ hθ g (a + 1) ((FormsData.ofDividedPowers p A h).wedge a ω η) =
      leftWedge a (exteriorPower.oneEquiv C M (completedFormsHom p hE θ hθ g 1 η))
        (completedFormsHom p hE θ hθ g a ω) := by
  obtain ⟨w, rfl⟩ := (pAdicOfEquiv p hE _).surjective ω
  obtain ⟨v, rfl⟩ := (pAdicOfEquiv p hE _).surjective η
  rw [pAdicOfEquiv_apply, pAdicOfEquiv_apply]
  change completedFormsHom p hE θ hθ g (a + 1)
    (completedDividedPowerWedge p A h a (AdicCompletion.of _ _ w) (AdicCompletion.of _ _ v)) = _
  rw [completedDividedPowerWedge_of_of, completedFormsHom_of, completedFormsHom_of,
    completedFormsHom_of, mapDifferentialFormsOfDPMorphism_wedge, dividedPowerWedge_apply,
    exteriorPower_map_leftWedge, oneEquiv_exteriorPower_map,
    mapDifferentialFormsOfDPMorphism_oneEquiv]

/-- **`completedFormsHom` intertwines the de Rham differential of the completed forms with any
differential `D` on `⋀^*_C M` obeying the Leibniz rule and the generator rule.** -/
theorem completedFormsHom_deRham (a : ℕ) (D : ⋀[C]^a M →+ ⋀[C]^(a + 1) M)
    (hsmul : ∀ (c : C) (ω : ⋀[C]^a M),
      D (c • ω) = c • D ω + leftWedge a (g (dividedPowerDifferential (A := A) hK c)) ω)
    (hgen : ∀ c : Fin (a + 1) → C,
      D (c 0 • exteriorPower.ιMulti C a fun j ↦
          g (dividedPowerDifferential (A := A) hK (c j.succ))) =
        exteriorPower.ιMulti C (a + 1) fun j ↦ g (dividedPowerDifferential (A := A) hK (c j)))
    (ω : (FormsData.ofDividedPowers p A h).Om a) :
    completedFormsHom p hE θ hθ g (a + 1) ((FormsData.ofDividedPowers p A h).deRham a ω) =
      D (completedFormsHom p hE θ hθ g a ω) := by
  obtain ⟨w, rfl⟩ := (pAdicOfEquiv p hE _).surjective ω
  rw [pAdicOfEquiv_apply]
  change completedFormsHom p hE θ hθ g (a + 1)
    (completedDividedPowerDeRham p A h a (AdicCompletion.of _ _ w)) = _
  rw [completedDividedPowerDeRham_of, completedFormsHom_of, completedFormsHom_of,
    mapDifferentialFormsOfDPMorphism_deRham]
  exact exteriorPower_map_dividedPowerDeRham hK g a D hsmul hgen _

/-- **`completedFormsHom` is bijective when `g` is and `θ` is an isomorphism of divided power
algebras**, that is, has an inverse which is a divided power morphism too. -/
theorem completedFormsHom_bijective (hg : Function.Bijective g) (θ₁ : C →ₐ[A] E)
    (hθ₁ : IsDPMorphism hK h θ₁.toRingHom) (h₁ : θ₁.comp θ = AlgHom.id A E)
    (h₂ : θ.comp θ₁ = AlgHom.id A C) (a : ℕ) :
    Function.Bijective (completedFormsHom p hE θ hθ g a) := by
  have hc₁ : IsDPMorphism h h (θ₁.comp θ).toRingHom := by
    rw [h₁]
    exact (DPMorphism.id h).isDPMorphism
  have hc₂ : IsDPMorphism hK hK (θ.comp θ₁).toRingHom := by
    rw [h₂]
    exact (DPMorphism.id hK).isDPMorphism
  have keyE : ∀ (f : E →ₐ[A] E) (hf : IsDPMorphism h h f.toRingHom), f = AlgHom.id A E →
      ∀ x, mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := h) h f hf a x = x := by
    rintro f hf rfl x
    exact mapDifferentialFormsOfDPMorphism_id (A := A) (J := J) (delta := h) a hf x
  have keyC : ∀ (f : C →ₐ[A] C) (hf : IsDPMorphism hK hK f.toRingHom), f = AlgHom.id A C →
      ∀ x, mapDifferentialFormsOfDPMorphism (A := A) (J := K) (delta := hK) hK f hf a x = x := by
    rintro f hf rfl x
    exact mapDifferentialFormsOfDPMorphism_id (A := A) (J := K) (delta := hK) a hf x
  have hmap : Function.Bijective
      (mapDifferentialFormsOfDPMorphism (A := A) (J := J) (delta := h) hK θ hθ a) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨mapDifferentialFormsOfDPMorphism (A := A) (J := K) (delta := hK) h θ₁ hθ₁ a,
        fun x ↦ ?_, fun y ↦ ?_⟩
    · rw [← mapDifferentialFormsOfDPMorphism_comp (A := A) (J := J) (delta := h) hK h θ θ₁ hθ hθ₁
        hc₁]
      exact keyE _ hc₁ h₁ x
    · rw [← mapDifferentialFormsOfDPMorphism_comp (A := A) (J := K) (delta := hK) h hK θ₁ θ hθ₁ hθ
        hc₂]
      exact keyC _ hc₂ h₂ y
  exact (exteriorPower_map_bijective g hg a).comp (hmap.comp (pAdicOfEquiv p hE _).symm.bijective)

include hE in
/-- **Two additive maps out of the completed forms agree as soon as they are semilinear over the
same ring map and agree on the wedges `d e₁ ∧ ⋯ ∧ d e_a` of universal differentials.** -/
theorem completedForms_addMonoidHom_ext {a : ℕ} {T N : Type*} [Semiring T] [AddCommGroup N]
    [Module T N] (σ : AdicCompletion (pAdicIdeal (A := E) p) E →+* T)
    (F G : (FormsData.ofDividedPowers p A h).Om a →+ N)
    (hF : ∀ c x, F (c • x) = σ c • F x) (hG : ∀ c x, G (c • x) = σ c • G x)
    (hgen : ∀ e : Fin a → E,
      F (AdicCompletion.of _ _ (exteriorPower.ιMulti E a fun j ↦
        dividedPowerDifferential (A := A) h (e j))) =
      G (AdicCompletion.of _ _ (exteriorPower.ιMulti E a fun j ↦
        dividedPowerDifferential (A := A) h (e j)))) :
    F = G := by
  refine AddMonoidHom.ext fun ω ↦ ?_
  obtain ⟨w, rfl⟩ := (pAdicOfEquiv p hE _).surjective ω
  rw [pAdicOfEquiv_apply]
  have hw : w ∈ Submodule.span E (Set.range fun c : Fin (a + 1) → E ↦
      c 0 • exteriorPower.ιMulti E a fun j ↦ dividedPowerDifferential (A := A) h (c j.succ)) := by
    rw [span_range_smul_ιMulti_eq_top (R := E) (dividedPowerDifferential (A := A) h)
      (dividedPowerDifferentials_span h) a]
    trivial
  induction hw using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨c, rfl⟩ := hy
      rw [pAdicOf_smul p hE, hF, hG, hgen]
  | zero => rw [map_zero, map_zero, map_zero]
  | add y y' _ _ hy hy' => rw [map_add, map_add, map_add, hy, hy']
  | smul c y _ hy => rw [pAdicOf_smul p hE, hF, hG, hy]

variable {E' : Type u} [CommRing E'] [Algebra A E'] {J' : Ideal E'} {h' : DividedPowers J'}

/-- **A morphism of rings with forms followed by `completedFormsHom`, on a wedge of universal
differentials of positive degree.**  The wedge is an iterated wedge product of universal
differentials, which a morphism of rings with forms preserves. -/
theorem completedFormsHom_psi_ιMulti_d
    (g' : FormsData.Hom (FormsData.ofDividedPowers p A h') (FormsData.ofDividedPowers p A h))
    (a : ℕ) (e : Fin (a + 1) → E') :
    completedFormsHom p hE θ hθ g (a + 1) (g'.psi (a + 1)
        (AdicCompletion.of _ _ (exteriorPower.ιMulti E' (a + 1) fun j ↦
          dividedPowerDifferential (A := A) h' (e j)))) =
      exteriorPower.ιMulti C (a + 1) fun j ↦ g (dividedPowerDifferential (A := A) hK
        (completedFormsRingHom p hE θ (g'.toRingHom (AdicCompletion.of _ E' (e j))))) := by
  induction a with
  | zero =>
      have h0 : (fun j : Fin 1 ↦ dividedPowerDifferential (A := A) h' (e j)) =
          fun _ ↦ dividedPowerDifferential (A := A) h' (e 0) :=
        funext fun j ↦ by rw [Fin.fin_one_eq_zero j]
      have h0' : (fun j : Fin 1 ↦ g (dividedPowerDifferential (A := A) hK
          (completedFormsRingHom p hE θ (g'.toRingHom (AdicCompletion.of _ E' (e j)))))) =
          fun _ ↦ g (dividedPowerDifferential (A := A) hK
            (completedFormsRingHom p hE θ (g'.toRingHom (AdicCompletion.of _ E' (e 0))))) :=
        funext fun j ↦ by rw [Fin.fin_one_eq_zero j]
      rw [h0, h0', ← ofDividedPowers_diff_of, g'.psi_diff, completedFormsHom_diff]
  | succ a ih =>
      rw [← ofDividedPowers_wedge_of_ιMulti p A h' (a + 1) e, g'.psi_wedge, g'.psi_diff,
        completedFormsHom_wedge, oneEquiv_completedFormsHom_diff, ih fun j ↦ e j.succ,
        leftWedge_ιMulti]
      exact congrArg (exteriorPower.ιMulti C (a + 1 + 1)) (Fin.cons_self_tail fun j ↦
        g (dividedPowerDifferential (A := A) hK
          (completedFormsRingHom p hE θ (g'.toRingHom (AdicCompletion.of _ E' (e j))))))

end CompletedForms

namespace GlobalCrystallineSituation

/-! ### The inverse of [Stacks, Tag 07J0] at an affine object -/

section AffineForms

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme] (B : Thickening S)
  [IsAffine B.thickening.target.scheme]

/-- **The divided power differentials `Ω¹_{Γ(T,𝒪_T)/Γ(S,𝒪_S),δ}`** of the sections of the ambient
scheme of an object, with the algebra structure `crysTopAlgebra` supplied positionally. -/
abbrev crysTopDifferentials : Type u :=
  @dividedPowerDifferentials (Γ(S.S.scheme, ⊤) : Type u)
    (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _ (crysDividedPowers S B)

/-- **The inverse of [Stacks, Tag 07J0] in degree one at `V = ⊤`**: the divided power
differentials of `Γ(T, 𝒪_T)` over `Γ(S, 𝒪_S)` to the sections of `Ω_{X/S}`. -/
def affineFormsOneInv :
    crysTopDifferentials B →ₗ[Γ(B.thickening.target.scheme, ⊤)]
      ↥((crysDifferentials S).obj (op B)) :=
  (affineCrysDifferentialsIso S B (V := ⊤) le_rfl (isAffineOpen_top _)).inv.hom

/-- The degree-one inverse carries the universal divided power differential to `d_{X/S}`. -/
theorem affineFormsOneInv_d (b : Γ(B.thickening.target.scheme, ⊤)) :
    affineFormsOneInv B (@dividedPowerDifferential (Γ(S.S.scheme, ⊤) : Type u)
        (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
        (crysDividedPowers S B) b) = crysD S B b := by
  rw [← dpd_eq (affineBaseAppLE S B (V := ⊤) le_rfl) (crysDividedPowers S B) b]
  exact affineCrysDifferentialsIso_inv_dpd S B le_rfl (isAffineOpen_top _) b

/-- The degree-one inverse is bijective, being the inverse of an isomorphism. -/
theorem affineFormsOneInv_bijective : Function.Bijective (affineFormsOneInv B) :=
  (affineCrysDifferentialsIso S B (V := ⊤) le_rfl (isAffineOpen_top _)).toLinearEquiv.symm.bijective

end AffineForms

/-! ### The completed forms of a divided power algebra over an affine object -/

section Forms

attribute [local instance] crysTopAlgebra

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme] {B : Thickening S}
  [IsAffine B.thickening.target.scheme] {E : Type u} [CommRing E]
  [Algebra (Γ(S.S.scheme, ⊤) : Type u) E] {J : Ideal E} {h : DividedPowers J}
  (hE : ∃ k, (S.p : E) ^ k = 0)
  (θ₀ : E →ₐ[(Γ(S.S.scheme, ⊤) : Type u)] (Γ(B.thickening.target.scheme, ⊤) : Type u))
  (hθ₀ : IsDPMorphism h (crysDividedPowers S B) θ₀.toRingHom)

/-- **The ring map `Ê → Γ(T, 𝒪_T)`** of a divided power algebra `E` over `Γ(S, 𝒪_S)` in which `p`
is nilpotent, along `θ₀ : E → Γ(T, 𝒪_T)`: `Crystalline.completedFormsRingHom`, the inverse of
`AdicCompletion.of` followed by `θ₀`. -/
def formsRingHom : AdicCompletion (pAdicIdeal (A := E) S.p) E →+* crysFormRing S B :=
  completedFormsRingHom S.p hE θ₀

omit [IsAffine S.S.scheme] [IsAffine B.thickening.target.scheme] in
/-- `formsRingHom` extends `θ₀`. -/
@[simp] theorem formsRingHom_of (e : E) :
    formsRingHom hE θ₀ (AdicCompletion.of _ E e) = θ₀ e :=
  completedFormsRingHom_of S.p hE θ₀ e

/-- **The comparison of forms `Ω̂^a_E → Ω^a_{X/S}(B)`**: `Crystalline.completedFormsHom` at the
inverse `affineFormsOneInv` of [Stacks, Tag 07J0]; semilinear over `formsRingHom`. -/
def formsHom (a : ℕ) :
    (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).Om a →ₛₗ[formsRingHom hE θ₀]
      ⋀[crysFormRing S B]^a ↥((crysDifferentials S).obj (op B)) :=
  completedFormsHom S.p hE θ₀ hθ₀ (affineFormsOneInv B) a

/-- **The comparison of one-forms `Ω̂^1_E → Ω_{X/S}(B)`**, `formsHom` in degree one read through
`exteriorPower.oneEquiv`. -/
def formsOneHom :
    (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).Om 1 →ₛₗ[formsRingHom hE θ₀]
      ↥((crysDifferentials S).obj (op B)) :=
  (exteriorPower.oneEquiv (crysFormRing S B)
    ↥((crysDifferentials S).obj (op B))).toLinearMap.comp (formsHom hE θ₀ hθ₀ 1)

/-- `formsOneHom` is `formsHom` in degree one, read through `exteriorPower.oneEquiv`. -/
theorem formsOneHom_apply
    (η : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).Om 1) :
    formsOneHom hE θ₀ hθ₀ η =
      exteriorPower.oneEquiv (crysFormRing S B) _ (formsHom hE θ₀ hθ₀ 1 η) := rfl

/-- `formsHom` is semilinear over `formsRingHom`. -/
theorem formsHom_smul (a : ℕ) (c : AdicCompletion (pAdicIdeal (A := E) S.p) E)
    (x : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).Om a) :
    formsHom hE θ₀ hθ₀ a (c • x) = formsRingHom hE θ₀ c • formsHom hE θ₀ hθ₀ a x :=
  map_smulₛₗ _ c x

/-- `formsOneHom` is semilinear over `formsRingHom`. -/
theorem formsOneHom_smul (c : AdicCompletion (pAdicIdeal (A := E) S.p) E)
    (x : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).Om 1) :
    formsOneHom hE θ₀ hθ₀ (c • x) = formsRingHom hE θ₀ c • formsOneHom hE θ₀ hθ₀ x :=
  map_smulₛₗ _ c x

/-- **`formsHom` on a wedge of universal differentials**: `d e₁ ∧ ⋯ ∧ d e_a` goes to
`d θ₀(e₁) ∧ ⋯ ∧ d θ₀(e_a)`. -/
theorem formsHom_ιMulti_d (a : ℕ) (e : Fin a → E) :
    formsHom hE θ₀ hθ₀ a (AdicCompletion.of _ _ (exteriorPower.ιMulti E a fun j ↦
        dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h (e j))) =
      exteriorPower.ιMulti (crysFormRing S B) a fun j ↦ crysD S B (θ₀ (e j)) := by
  refine (completedFormsHom_ιMulti_d S.p hE θ₀ hθ₀ (affineFormsOneInv B) a e).trans ?_
  rw [show (fun j ↦ affineFormsOneInv B (@dividedPowerDifferential (Γ(S.S.scheme, ⊤) : Type u)
      (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
      (crysDividedPowers S B) (θ₀ (e j)))) = fun j ↦ crysD S B (θ₀ (e j)) from
    funext fun j ↦ affineFormsOneInv_d B (θ₀ (e j))]
  rfl

/-- **`formsOneHom` carries the universal differential to `d_{X/S}`**:
`formsOneHom (d x) = d (formsRingHom x)`. -/
theorem formsOneHom_diff
    (x : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).ring) :
    formsOneHom hE θ₀ hθ₀ ((FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).diff x) =
      crysD S B (formsRingHom hE θ₀ x) :=
  (oneEquiv_completedFormsHom_diff S.p hE θ₀ hθ₀ (affineFormsOneInv B) x).trans
    (affineFormsOneInv_d B _)

/-- **`formsHom` respects the wedge product**: `formsHom (η ∧ ω) = formsOneHom η ∧ formsHom ω`,
in the variance of `Crystalline.leftWedge`. -/
theorem formsHom_wedge (a : ℕ)
    (ω : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).Om a)
    (η : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).Om 1) :
    formsHom hE θ₀ hθ₀ (a + 1)
        ((FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).wedge a ω η) =
      leftWedge a (formsOneHom hE θ₀ hθ₀ η) (formsHom hE θ₀ hθ₀ a ω) :=
  completedFormsHom_wedge S.p hE θ₀ hθ₀ (affineFormsOneInv B) a ω η

/-- **`formsHom` is a map of de Rham complexes**: it carries the de Rham differential of the
completed forms to the crystalline de Rham differential of [Stacks, Tag 07J4]. -/
theorem formsHom_deRham (a : ℕ)
    (ω : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).Om a) :
    formsHom hE θ₀ hθ₀ (a + 1)
        ((FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h).deRham a ω) =
      (crysDeRhamComplex S).differential a B (formsHom hE θ₀ hθ₀ a ω) :=
  completedFormsHom_deRham S.p hE θ₀ hθ₀ (affineFormsOneInv B) a
    ((crysDeRhamComplex S).differential a B)
    (fun c ω ↦ by
      rw [affineFormsOneInv_d]
      exact (crysDeRhamComplex S).differential_smul S a B c ω)
    (fun c ↦ by
      simp only [affineFormsOneInv_d]
      exact (crysDeRhamComplex S).differential_generator a B c) ω

omit [IsAffine S.S.scheme] [IsAffine B.thickening.target.scheme] in
/-- `formsRingHom` is bijective when `θ₀` is. -/
theorem formsRingHom_bijective (hθb : Function.Bijective θ₀) :
    Function.Bijective (formsRingHom hE θ₀) :=
  completedFormsRingHom_bijective S.p hE θ₀ hθb

/-- **`formsHom` is bijective when `θ₀` is an isomorphism of divided power algebras**, that is,
has an inverse `θ₁` which is a divided power morphism too. -/
theorem formsHom_bijective
    (θ₁ : (Γ(B.thickening.target.scheme, ⊤) : Type u) →ₐ[(Γ(S.S.scheme, ⊤) : Type u)] E)
    (hθ₁ : IsDPMorphism (crysDividedPowers S B) h θ₁.toRingHom)
    (h₁ : θ₁.comp θ₀ = AlgHom.id _ E) (h₂ : θ₀.comp θ₁ = AlgHom.id _ _) (a : ℕ) :
    Function.Bijective (formsHom hE θ₀ hθ₀ a) :=
  completedFormsHom_bijective S.p hE θ₀ hθ₀ (affineFormsOneInv B) (affineFormsOneInv_bijective B)
    θ₁ hθ₁ h₁ h₂ a

/-- **`formsOneHom` is bijective when `θ₀` is an isomorphism of divided power algebras.** -/
theorem formsOneHom_bijective
    (θ₁ : (Γ(B.thickening.target.scheme, ⊤) : Type u) →ₐ[(Γ(S.S.scheme, ⊤) : Type u)] E)
    (hθ₁ : IsDPMorphism (crysDividedPowers S B) h θ₁.toRingHom)
    (h₁ : θ₁.comp θ₀ = AlgHom.id _ E) (h₂ : θ₀.comp θ₁ = AlgHom.id _ _) :
    Function.Bijective (formsOneHom hE θ₀ hθ₀) :=
  (exteriorPower.oneEquiv (crysFormRing S B) ↥((crysDifferentials S).obj (op B))).bijective.comp
    (formsHom_bijective hE θ₀ hθ₀ θ₁ hθ₁ h₁ h₂ 1)

end Forms

/-! ### Naturality in the object -/

section Naturality

attribute [local instance] crysTopAlgebra

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme] {B B' : Thickening S}
  [IsAffine B.thickening.target.scheme] [IsAffine B'.thickening.target.scheme]
  {E : Type u} [CommRing E] [Algebra (Γ(S.S.scheme, ⊤) : Type u) E] {J : Ideal E}
  {h : DividedPowers J} (hE : ∃ k, (S.p : E) ^ k = 0)
  (θ₀ : E →ₐ[(Γ(S.S.scheme, ⊤) : Type u)] (Γ(B.thickening.target.scheme, ⊤) : Type u))
  (hθ₀ : IsDPMorphism h (crysDividedPowers S B) θ₀.toRingHom)
  {E' : Type u} [CommRing E'] [Algebra (Γ(S.S.scheme, ⊤) : Type u) E'] {J' : Ideal E'}
  {h' : DividedPowers J'} (hE' : ∃ k, (S.p : E') ^ k = 0)
  (θ₀' : E' →ₐ[(Γ(S.S.scheme, ⊤) : Type u)] (Γ(B'.thickening.target.scheme, ⊤) : Type u))
  (hθ₀' : IsDPMorphism h' (crysDividedPowers S B') θ₀'.toRingHom)
  (k : B ⟶ B')
  (g : FormsData.Hom (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h')
    (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h))
  (hg : ∀ x, formsRingHom hE θ₀ (g.toRingHom x) = crysRingMap S k (formsRingHom hE' θ₀' x))

/-- **The transition map of `Ω_{X/S}` along a morphism of `CRIS(X/S)`, as an additive map**
between the sections at the spelling of the presheaf of modules; it is semilinear by
`crysDifferentialsAddMap_smul`. -/
def crysDifferentialsAddMap {A A' : Thickening S} (k : A ⟶ A') :
    ↥((crysDifferentials S).obj (op A')) →+ ↥((crysDifferentials S).obj (op A)) :=
  ((crysDifferentials S).map k.op).hom.toAddMonoidHom

omit [IsAffine S.S.scheme] in
/-- `crysDifferentialsAddMap` is the transition map of `Ω_{X/S}`. -/
theorem crysDifferentialsAddMap_apply {A A' : Thickening S} (k : A ⟶ A')
    (x : ↥((crysDifferentials S).obj (op A'))) :
    crysDifferentialsAddMap k x = (crysDifferentials S).map k.op x := rfl

omit [IsAffine S.S.scheme] in
/-- `crysDifferentialsAddMap` is semilinear over the map on sections. -/
theorem crysDifferentialsAddMap_smul {A A' : Thickening S} (k : A ⟶ A') (c : crysFormRing S A')
    (x : ↥((crysDifferentials S).obj (op A'))) :
    crysDifferentialsAddMap k (c • x) = crysRingMap S k c • crysDifferentialsAddMap k x :=
  PresheafOfModules.map_smul (crysDifferentials S) k.op c x

include hg in
/-- **`formsHom ∘ g.psi` and the transition map after `formsHom` agree as soon as they agree on
the wedges of universal differentials**: both are semilinear over the same ring map. -/
theorem formsHom_naturality_of_ιMulti (a : ℕ)
    (hgen : ∀ e : Fin a → E',
      formsHom hE θ₀ hθ₀ a (g.psi a (AdicCompletion.of _ _
        (exteriorPower.ιMulti E' a fun j ↦
          dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e j)))) =
        crysFormMap S k (formsHom hE' θ₀' hθ₀' a (AdicCompletion.of _ _
          (exteriorPower.ιMulti E' a fun j ↦
            dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e j)))))
    (ω : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om a) :
    formsHom hE θ₀ hθ₀ a (g.psi a ω) = crysFormMap S k (formsHom hE' θ₀' hθ₀' a ω) := by
  have hF : ∀ (c : AdicCompletion (pAdicIdeal (A := E') S.p) E')
      (x : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om a),
      formsHom hE θ₀ hθ₀ a (g.psi a (c • x)) =
        formsRingHom hE θ₀ (g.toRingHom c) • formsHom hE θ₀ hθ₀ a (g.psi a x) :=
    fun c x ↦ by rw [map_smulₛₗ, formsHom_smul]
  have hG : ∀ (c : AdicCompletion (pAdicIdeal (A := E') S.p) E')
      (x : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om a),
      crysFormMap S k (formsHom hE' θ₀' hθ₀' a (c • x)) =
        formsRingHom hE θ₀ (g.toRingHom c) • crysFormMap S k (formsHom hE' θ₀' hθ₀' a x) :=
    fun c x ↦ by rw [formsHom_smul, crysFormMap_smul, hg]
  have key := completedForms_addMonoidHom_ext S.p hE' ((formsRingHom hE θ₀).comp g.toRingHom)
    ((formsHom hE θ₀ hθ₀ a).toAddMonoidHom.comp (g.psi a).toAddMonoidHom)
    ((crysFormMap S k).comp (formsHom hE' θ₀' hθ₀' a).toAddMonoidHom) hF hG hgen
  exact DFunLike.congr_fun key ω


include hg in
/-- **`formsHom` is natural in positive degree**: for a morphism `k : B ⟶ B'` of `CRIS(X/S)` and
a morphism `g` of rings with forms compatible with the ring maps, `formsHom ∘ g.psi` is the
transition map of `Ω^{a+1}_{X/S}` along `k` after `formsHom`.  Both sides are semilinear over
the same ring map, and they agree on the wedges of universal differentials, which a morphism of
rings with forms preserves. -/
theorem formsHom_naturality_succ (a : ℕ)
    (ω : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om (a + 1)) :
    formsHom hE θ₀ hθ₀ (a + 1) (g.psi (a + 1) ω) =
      crysFormMap S k (formsHom hE' θ₀' hθ₀' (a + 1) ω) := by
  have hgen : ∀ e : Fin (a + 1) → E',
      formsHom hE θ₀ hθ₀ (a + 1) (g.psi (a + 1) (AdicCompletion.of _ _
        (exteriorPower.ιMulti E' (a + 1) fun j ↦
          dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e j)))) =
        crysFormMap S k (formsHom hE' θ₀' hθ₀' (a + 1) (AdicCompletion.of _ _
          (exteriorPower.ιMulti E' (a + 1) fun j ↦
            dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e j)))) := by
    intro e
    rw [formsHom_ιMulti_d]
    refine (completedFormsHom_psi_ιMulti_d S.p hE θ₀ hθ₀ (affineFormsOneInv B) g a e).trans
      (Eq.trans ?_ (crysFormMap_ιMulti S k (fun j ↦ θ₀' (e j))).symm)
    have hj : ∀ j, affineFormsOneInv B (@dividedPowerDifferential (Γ(S.S.scheme, ⊤) : Type u)
        (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
        (crysDividedPowers S B)
        (completedFormsRingHom S.p hE θ₀ (g.toRingHom (AdicCompletion.of _ E' (e j))))) =
        crysD S B (crysRingMap S k (θ₀' (e j))) := fun j ↦ by
      rw [affineFormsOneInv_d]
      have := hg (AdicCompletion.of _ E' (e j))
      rw [formsRingHom_of] at this
      exact congrArg (crysD S B) this
    rw [show (fun j ↦ affineFormsOneInv B (@dividedPowerDifferential (Γ(S.S.scheme, ⊤) : Type u)
        (Γ(B.thickening.target.scheme, ⊤) : Type u) _ _ (crysTopAlgebra S B) _
        (crysDividedPowers S B)
        (completedFormsRingHom S.p hE θ₀ (g.toRingHom (AdicCompletion.of _ E' (e j)))))) =
        fun j ↦ crysD S B (crysRingMap S k (θ₀' (e j))) from funext hj]
    rfl
  exact formsHom_naturality_of_ιMulti hE θ₀ hθ₀ hE' θ₀' hθ₀' k g hg (a + 1) hgen ω

include hg in
/-- **`formsHom` is natural in degree zero**, provided `g` carries the unit zero-form to the unit
zero-form.  (The axioms of a morphism of rings with forms do not force this: they constrain the
comparison of forms only through the universal differential, the wedge product and the de Rham
differential, none of which reaches `Ω^0` beyond multiplication by a closed constant.  It holds
for `Crystalline.FormsData.Hom.ofCompletion`, by
`Crystalline.completedMapDifferentialForms_completedUnitZeroForm`.) -/
theorem formsHom_naturality_zero
    (hg₀ : g.psi 0 (completedUnitZeroForm S.p (Γ(S.S.scheme, ⊤) : Type u) h') =
      completedUnitZeroForm S.p (Γ(S.S.scheme, ⊤) : Type u) h)
    (ω : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om 0) :
    formsHom hE θ₀ hθ₀ 0 (g.psi 0 ω) = crysFormMap S k (formsHom hE' θ₀' hθ₀' 0 ω) := by
  refine formsHom_naturality_of_ιMulti hE θ₀ hθ₀ hE' θ₀' hθ₀' k g hg 0 (fun e ↦ ?_) ω
  rw [of_ιMulti_zero_eq_completedUnitZeroForm, hg₀,
    ← of_ιMulti_zero_eq_completedUnitZeroForm S.p _ h fun j ↦
      dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h (Fin.elim0 j : E),
    ← of_ιMulti_zero_eq_completedUnitZeroForm S.p _ h' fun j ↦
      dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e j)]
  refine (formsHom_ιMulti_d hE θ₀ hθ₀ 0 fun j ↦ Fin.elim0 j).trans ?_
  refine Eq.trans ?_ (congrArg (crysFormMap S k) (formsHom_ιMulti_d hE' θ₀' hθ₀' 0 e)).symm
  refine Eq.trans ?_ (crysFormMap_ιMulti S k (fun j ↦ θ₀' (e j))).symm
  exact congrArg _ (funext fun j ↦ Fin.elim0 j)

include hg in
/-- **`formsHom` is natural in every degree**, provided `g` carries the unit zero-form to the
unit zero-form (which is needed only in degree zero; see `formsHom_naturality_zero`). -/
theorem formsHom_naturality
    (hg₀ : g.psi 0 (completedUnitZeroForm S.p (Γ(S.S.scheme, ⊤) : Type u) h') =
      completedUnitZeroForm S.p (Γ(S.S.scheme, ⊤) : Type u) h) (a : ℕ)
    (ω : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om a) :
    formsHom hE θ₀ hθ₀ a (g.psi a ω) = crysFormMap S k (formsHom hE' θ₀' hθ₀' a ω) := by
  cases a with
  | zero => exact formsHom_naturality_zero hE θ₀ hθ₀ hE' θ₀' hθ₀' k g hg hg₀ ω
  | succ a => exact formsHom_naturality_succ hE θ₀ hθ₀ hE' θ₀' hθ₀' k g hg a ω

include hg in
/-- **`formsOneHom` is natural**: for a morphism `k : B ⟶ B'` of `CRIS(X/S)` and a morphism `g`
of rings with forms compatible with the ring maps, `formsOneHom ∘ g.psi` is the transition map
of `Ω_{X/S}` along `k` after `formsOneHom`. -/
theorem formsOneHom_naturality
    (η : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om 1) :
    formsOneHom hE θ₀ hθ₀ (g.psi 1 η) =
      crysDifferentialsAddMap k (formsOneHom hE' θ₀' hθ₀' η) := by
  have hgen : ∀ e : Fin 1 → E',
      formsOneHom hE θ₀ hθ₀ (g.psi 1 (AdicCompletion.of _ _
        (exteriorPower.ιMulti E' 1 fun j ↦
          dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e j)))) =
        crysDifferentialsAddMap k (formsOneHom hE' θ₀' hθ₀' (AdicCompletion.of _ _
          (exteriorPower.ιMulti E' 1 fun j ↦
            dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e j)))) := by
    intro e
    have he : (fun j : Fin 1 ↦
          dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e j)) =
        fun _ ↦ dividedPowerDifferential (A := (Γ(S.S.scheme, ⊤) : Type u)) h' (e 0) :=
      funext fun j ↦ by rw [Fin.fin_one_eq_zero j]
    rw [he, ← ofDividedPowers_diff_of, g.psi_diff, formsOneHom_diff, formsOneHom_diff, hg,
      crysDifferentialsAddMap_apply, crysD_map]
    rfl
  have hF : ∀ (c : AdicCompletion (pAdicIdeal (A := E') S.p) E')
      (x : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om 1),
      formsOneHom hE θ₀ hθ₀ (g.psi 1 (c • x)) =
        formsRingHom hE θ₀ (g.toRingHom c) • formsOneHom hE θ₀ hθ₀ (g.psi 1 x) :=
    fun c x ↦ by rw [map_smulₛₗ, formsOneHom_smul]
  have hG : ∀ (c : AdicCompletion (pAdicIdeal (A := E') S.p) E')
      (x : (FormsData.ofDividedPowers S.p (Γ(S.S.scheme, ⊤) : Type u) h').Om 1),
      crysDifferentialsAddMap k (formsOneHom hE' θ₀' hθ₀' (c • x)) =
        formsRingHom hE θ₀ (g.toRingHom c) •
          crysDifferentialsAddMap k (formsOneHom hE' θ₀' hθ₀' x) :=
    fun c x ↦ by rw [formsOneHom_smul, crysDifferentialsAddMap_smul, hg]
  have key := completedForms_addMonoidHom_ext S.p hE' ((formsRingHom hE θ₀).comp g.toRingHom)
    ((formsOneHom hE θ₀ hθ₀).toAddMonoidHom.comp (g.psi 1).toAddMonoidHom)
    ((crysDifferentialsAddMap k).comp (formsOneHom hE' θ₀' hθ₀').toAddMonoidHom) hF hG hgen
  exact DFunLike.congr_fun key η

end Naturality

end GlobalCrystallineSituation

end Crystalline

end
