module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.Deformation.Artin.Versality.FormalObjectApproximation
public import StacksFrontier.Deformation.Artin.Versality.GRingCounterexample
public import StacksFrontier.Deformation.Artin.Versality.GRingCounterexampleEffective
public import StacksFrontier.Deformation.Artin.Versality.GRingCounterexampleVersal
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity
public import StacksFrontier.RingTheory.AdicCompletion.KerTruncation
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase

/-!
# The local ring must be a G-ring for Artin approximation of versal formal objects

Let `Λ` be a Noetherian ring, let `𝔪 ⊂ Λ` be a maximal ideal, let `R = Λ_𝔪^∧`, and let
`Λ → C → R` be a factorization with `C` of finite type over `Λ`. Set `S = Spec(Λ)`,
`U = S ∖ {𝔪}` and `S' = U ⨿ Spec(C)`, and let `F` be the functor on the big fppf site of `S`
which is a one-point set on a scheme whose structure morphism factors through `S' → S` and
empty otherwise. **Stacks 07XI** builds the category `𝒳 = 𝒮_F` fibred in sets from `F`,
asserts that `𝒳 → (Sch/S)_{fppf}` is limit preserving on objects and that there is an
effective versal formal object `ξ` over `R`, and then argues *conditionally*: **if** the
conclusion of **Stacks 07XH** holds for all of these `𝒳`, one gets for each `C` a finite type
`Λ`-algebra `A` with a maximal ideal `𝔪_A` over `𝔪` such that `κ(𝔪) = κ(𝔪_A)`, such that
`Λ → A` satisfies condition (4) of **Stacks 02HT** at `𝔪_A` — hence is smooth there — and
such that `C` maps to `A` over `Λ`. Since a solution of a system of equations in `R` is a
`Λ`-algebra map `C → R`, that says a system with a solution in `R` has a solution in the
henselization of `Λ_𝔪`; that is the approximation property for `Λ_𝔪^h`, which forces `Λ_𝔪^h`,
and hence `Λ_𝔪`, to be a G-ring. So the Example's point is that the G-ring property is
*necessary*: it assumes no G-ring property anywhere, and the conclusion of 07XH enters only
as the hypothesis of its final implication.

This file proves the Example: `Deformation.Artin.GRingCounterexample.exists_algHom_henselian`
states the functor's defining property, the three assertions about `𝒳` and `ξ`, and the
Example's implication with the conclusion of 07XH — in the form of the datum
`Deformation.Artin.AlgebraizesFiniteTypeFactorizations` the Example reads off it — as the
antecedent of its last conjunct, and with no G-ring hypothesis.

It also proves the opposite implication: applying Stacks 07XH to this `𝒳` and this `ξ` under the
hypothesis that `𝒪_{S, 𝔪}` is a G-ring derives the datum for this `C`, and hence the same
conclusion (`Deformation.Artin.GRingCounterexample.exists_algHom_henselian_of_isGRing` and its
two corollaries).

## Main results

* `Deformation.Artin.GRingCounterexample.exists_algHom_henselian`: **Stacks 07XI**, the
  Example whole, with the conclusion of 07XH assumed in the antecedent of its last conjunct
  and no G-ring hypothesis.
* `Deformation.Artin.GRingCounterexample.exists_algHom_henselian_of_isGRing`: the converse
  implication, a consequence of Stacks 07XH -- if `𝒪_{S, 𝔪}` is a G-ring, the datum for this
  `𝒳` and this `ξ` is derived rather than assumed.
* `Deformation.Artin.GRingCounterexample.exists_solution_of_isGRing`: its conclusion in the
  source's closing form, for a system of polynomial equations.
* `Deformation.Artin.GRingCounterexample.exists_solution_henselization_of_isGRing`: the same
  with the target a henselization of `Λ_𝔪`, which is the source's own wording.
* `Deformation.Artin.GRingCounterexample.isVersal_formalObject_stalk`: the Example's versal
  formal object, read over the local ring of `S` at `𝔪`.

## Implementation notes

Stacks 07XH assumes, as its item (3), that `𝒪_{S, s}` is a G-ring, and that is the hypothesis
the Example is about: "In this example we show that the local ring `𝒪_{S, s}` has to be a
G-ring in order for the result of Lemma 07XH to be true." The Example therefore does not
assume it; it assumes the *conclusion* of 07XH for its `𝒳` and derives the approximation
property of `Λ_𝔪^h`, which is what forces the G-ring property. Accordingly
`Deformation.Artin.GRingCounterexample.exists_algHom_henselian` has no `IsGRing` hypothesis, and
no `Deformation.Artin.AlgebraizesFiniteTypeFactorizations` hypothesis either: the latter is the
antecedent of its last conjunct.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
* [Stacks Project, Tag 04SU](https://stacks.math.columbia.edu/tag/04SU)
-/


@[expose] public noncomputable section

open IsLocalRing

namespace Deformation.Artin.GRingCounterexample

universe u

/-! ### Algebras whose infinitesimal neighbourhoods are those of the base -/

section Algebra

variable {Λ : Type u} [CommRing Λ] {m : Ideal Λ} [m.IsMaximal]
variable {A : Type u} [CommRing A] [Algebra Λ A]

/-- The truncation map `Λ → A ⧸ 𝔭 ^ n`. -/
private abbrev truncMap (p : Ideal A) (n : ℕ) : Λ →+* A ⧸ p ^ n :=
  (Ideal.Quotient.mk (p ^ n)).comp (algebraMap Λ A)

variable {p : Ideal A} [p.IsPrime]

omit [p.IsPrime] in
private theorem truncMap_eq_zero_iff (n : ℕ) (a : Λ) :
    truncMap (Λ := Λ) p n a = 0 ↔ algebraMap Λ A a ∈ p ^ n :=
  Ideal.Quotient.eq_zero_iff_mem

omit [m.IsMaximal] [p.IsPrime] in
/-- `𝔪` is the contraction of `𝔭` as soon as the first truncation map has kernel `𝔪`. -/
private theorem comap_eq_of_ker_truncMap
    (hk : RingHom.ker (truncMap (Λ := Λ) p 1) = m ^ 1) :
    m = p.comap (algebraMap Λ A) := by
  ext a
  rw [Ideal.mem_comap, ← pow_one p, ← truncMap_eq_zero_iff 1 a, ← RingHom.mem_ker, hk, pow_one]

omit [p.IsPrime] in
/-- If `Λ → A ⧸ 𝔭` is surjective with kernel `𝔪`, then `𝔭` is maximal. -/
private theorem isMaximal_of_truncMap
    (hs : Function.Surjective (truncMap (Λ := Λ) p 1))
    (hk : RingHom.ker (truncMap (Λ := Λ) p 1) = m ^ 1) :
    p.IsMaximal := by
  have e : (Λ ⧸ RingHom.ker (truncMap (Λ := Λ) p 1)) ≃+* (A ⧸ p ^ 1) :=
    RingHom.quotientKerEquivOfSurjective hs
  rw [hk, pow_one, pow_one] at e
  exact Ideal.Quotient.maximal_of_isField p (e.symm.toMulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp inferInstance))

/-- If `Λ → A ⧸ 𝔭` is surjective with kernel `𝔪`, the residue field map `κ(𝔪) → κ(𝔭)` is
bijective. -/
private theorem bijective_residueFieldMap_of_truncMap
    (hs : Function.Surjective (truncMap (Λ := Λ) p 1))
    (hk : RingHom.ker (truncMap (Λ := Λ) p 1) = m ^ 1) :
    Function.Bijective (Ideal.ResidueField.map m p (algebraMap Λ A)
      (comap_eq_of_ker_truncMap hk)) := by
  have := isMaximal_of_truncMap hs hk
  refine ⟨(Ideal.ResidueField.map m p (algebraMap Λ A) (comap_eq_of_ker_truncMap hk)).injective,
    fun y => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective p y
  obtain ⟨c, hc⟩ := hs (Ideal.Quotient.mk (p ^ 1) a)
  refine ⟨algebraMap Λ m.ResidueField c, ?_⟩
  rw [Ideal.ResidueField.map_algebraMap]
  have hmem : a - algebraMap Λ A c ∈ p := by
    have h := Ideal.Quotient.eq.mp hc.symm
    rwa [pow_one] at h
  have hz : algebraMap A p.ResidueField (a - algebraMap Λ A c) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr hmem
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

omit [m.IsMaximal] in
/-- **Condition (4) of Stacks 02HT, for an algebra whose infinitesimal neighbourhoods at `𝔭`
are those of `Λ` at `𝔪`.** If `Λ → A ⧸ 𝔭 ^ n` is surjective with kernel `𝔪 ^ n` for every `n`,
then `Λ → A` is smooth at `𝔭`. -/
private theorem isSmoothAt_of_truncMap [IsNoetherianRing Λ] [Algebra.FiniteType Λ A]
    (hs : ∀ n, Function.Surjective (truncMap (Λ := Λ) p n))
    (hk : ∀ n, RingHom.ker (truncMap (Λ := Λ) p n) = m ^ n) :
    Algebra.IsSmoothAt Λ p := by
  refine ((Algebra.isSmoothAt_tfae (R := Λ) (S := A) p).out 4 1).mp ?_
  intro B' B _ _ _ _ _ _ _ _ f hf _ g hq _
  obtain ⟨N₁, hN₁⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B')
  obtain ⟨N₂, hN₂⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN₁ hN₂
  set N := max N₁ N₂ with hNdef
  have hmB' : maximalIdeal B' ^ N = ⊥ := pow_eq_zero_of_le (le_max_left N₁ N₂) hN₁
  have hmB : maximalIdeal B ^ N = ⊥ := pow_eq_zero_of_le (le_max_right N₁ N₂) hN₂
  have hlocal : IsLocalHom (f : B' →+* B) := hf.isLocalHom (f : B' →+* B)
  have hmΛB' : ∀ c : Λ, c ∈ m → algebraMap Λ B' c ∈ maximalIdeal B' := by
    intro c hc
    have hcp : algebraMap Λ A c ∈ p := (comap_eq_of_ker_truncMap (hk 1)).le hc
    have h1 : algebraMap Λ B c ∈ maximalIdeal B := by
      have hmem : g (algebraMap Λ A c) ∈ maximalIdeal B := by
        rw [← hq] at hcp
        exact hcp
      rwa [AlgHom.commutes] at hmem
    rw [← IsLocalRing.maximalIdeal_comap (f : B' →+* B), Ideal.mem_comap, RingHom.coe_coe]
    rwa [AlgHom.commutes]
  have hkill : ∀ c : Λ, c ∈ m ^ N → algebraMap Λ B' c = 0 := by
    intro c hc
    have : algebraMap Λ B' c ∈ maximalIdeal B' ^ N := by
      have hle : (m ^ N).map (algebraMap Λ B') ≤ maximalIdeal B' ^ N := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hmΛB') N
      exact hle (Ideal.mem_map_of_mem _ hc)
    rwa [hmB', Ideal.mem_bot] at this
  set e : (Λ ⧸ m ^ N) ≃+* (A ⧸ p ^ N) := (hk N) ▸ RingHom.quotientKerEquivOfSurjective (hs N)
    with hedef
  have he : ∀ c : Λ, e (Ideal.Quotient.mk (m ^ N) c) = Ideal.Quotient.mk (p ^ N)
      (algebraMap Λ A c) := by
    intro c
    have : ∀ (I : Ideal Λ) (h : RingHom.ker (truncMap (Λ := Λ) p N) = I)
        (c : Λ), (h ▸ RingHom.quotientKerEquivOfSurjective (hs N) :
          (Λ ⧸ I) ≃+* (A ⧸ p ^ N)) (Ideal.Quotient.mk I c) =
        Ideal.Quotient.mk (p ^ N) (algebraMap Λ A c) := by
      intro I h
      subst h
      intro c
      rfl
    exact this _ (hk N) c
  set u : (Λ ⧸ m ^ N) →+* B' := Ideal.Quotient.lift (m ^ N) (algebraMap Λ B') hkill with hudef
  have hu : ∀ c : Λ, u (Ideal.Quotient.mk (m ^ N) c) = algebraMap Λ B' c := fun c => rfl
  set g' : A →ₐ[Λ] B' :=
    { toRingHom := (u.comp e.symm.toRingHom).comp (Ideal.Quotient.mk (p ^ N))
      commutes' := fun c => by
        change u (e.symm (Ideal.Quotient.mk (p ^ N) (algebraMap Λ A c))) = _
        rw [← he c, e.symm_apply_apply, hu] } with hg'def
  have hg'zero : ∀ a : A, a ∈ p ^ N → g' a = 0 := by
    intro a ha
    change u (e.symm (Ideal.Quotient.mk (p ^ N) a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero, map_zero]
  have hgzero : ∀ a : A, a ∈ p ^ N → g a = 0 := by
    intro a ha
    have hle : (p ^ N).map (g : A →+* B) ≤ maximalIdeal B ^ N := by
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr ?_) N
      rw [hq]
    have := hle (Ideal.mem_map_of_mem _ ha)
    rwa [hmB, Ideal.mem_bot] at this
  refine ⟨g', AlgHom.ext fun a => ?_⟩
  obtain ⟨c, hc⟩ := hs N (Ideal.Quotient.mk (p ^ N) a)
  have hmem : a - algebraMap Λ A c ∈ p ^ N := Ideal.Quotient.eq.mp hc.symm
  have h1 := hgzero _ hmem
  have h2 := hg'zero _ hmem
  rw [map_sub, sub_eq_zero, AlgHom.commutes] at h1 h2
  rw [AlgHom.comp_apply, h2, h1, AlgHom.commutes]

end Algebra

/-! ### The truncations of `R = Λ_𝔪^∧` are those of `Λ` at `𝔪` -/

section Completion

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : Ideal Λ) [m.IsMaximal]

/-- The composite `Λ → R ⧸ 𝔪_R ^ n` for `R = Λ_𝔪^∧`. -/
private abbrev baseTruncMap (n : ℕ) :
    Λ →+* completion m ⧸ maximalIdeal (completion m) ^ n :=
  (Ideal.Quotient.mk (maximalIdeal (completion m) ^ n)).comp (algebraMap Λ (completion m))

/-- `Λ → R ⧸ 𝔪_R ^ n` is the composite of the quotient map `Λ → Λ ⧸ 𝔪 ^ n` with the two
isomorphisms `Λ ⧸ 𝔪 ^ n ≅ Λ_𝔪 ⧸ 𝔪_{Λ_𝔪} ^ n ≅ R ⧸ 𝔪_R ^ n`. -/
private theorem baseTruncMap_apply (n : ℕ) (a : Λ) :
    baseTruncMap m n a =
      (completionQuotientEquiv (Localization.AtPrime m) n).symm
        (IsLocalization.AtPrime.equivQuotMaximalIdealPow m (Localization.AtPrime m) n
          (Ideal.Quotient.mk (m ^ n) a)) := by
  rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk, eq_comm,
    RingEquiv.symm_apply_eq]
  change completionQuotientEquiv (Localization.AtPrime m) n
      (Ideal.Quotient.mk _ (algebraMap Λ (completion m) a)) = _
  rw [show algebraMap Λ (completion m) a =
      algebraMap (Localization.AtPrime m) (completion m) (algebraMap Λ (Localization.AtPrime m) a)
      from IsScalarTower.algebraMap_apply _ _ _ a]
  exact completionQuotientEquiv_mk (Localization.AtPrime m) n _

/-- **`Λ → R ⧸ 𝔪_R ^ n` is surjective**: the `n`-th infinitesimal neighbourhood of the closed
point of `Spec(R)` is the `n`-th infinitesimal neighbourhood of `𝔪` in `Spec(Λ)`. -/
private theorem surjective_baseTruncMap (n : ℕ) : Function.Surjective (baseTruncMap m n) := by
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((IsLocalization.AtPrime.equivQuotMaximalIdealPow m (Localization.AtPrime m) n).symm
      (completionQuotientEquiv (Localization.AtPrime m) n y))
  refine ⟨a, ?_⟩
  rw [baseTruncMap_apply, ha, AlgEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]

/-- **The kernel of `Λ → R ⧸ 𝔪_R ^ n` is `𝔪 ^ n`.** -/
private theorem ker_baseTruncMap (n : ℕ) : RingHom.ker (baseTruncMap m n) = m ^ n := by
  ext a
  rw [RingHom.mem_ker, baseTruncMap_apply, map_eq_zero_iff _ (RingEquiv.injective _),
    map_eq_zero_iff _ (AlgEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

/-- The contraction of the maximal ideal of `R = Λ_𝔪^∧` to `Λ` is `𝔪`. -/
private theorem comap_maximalIdeal_completion :
    (maximalIdeal (completion m)).comap (algebraMap Λ (completion m)) = m := by
  exact (comap_eq_of_ker_truncMap (ker_baseTruncMap m 1)).symm

/-- **The truncation conditions from a map to `R = Λ_𝔪^∧`.** A `Λ`-algebra map `Θ : A → R`
under which the preimage of `𝔪_R ^ n` is `𝔭 ^ n` makes `Λ → A ⧸ 𝔭 ^ n` surjective with kernel
`𝔪 ^ n`. -/
private theorem truncMap_spec_of_ringHom {A : Type u} [CommRing A] [Algebra Λ A]
    (p : Ideal A) [p.IsPrime] (Θ : A →+* completion m)
    (hΛ : ∀ a : Λ, Θ (algebraMap Λ A a) = algebraMap Λ (completion m) a)
    (n : ℕ) (hpre : ∀ a : A, Θ a ∈ maximalIdeal (completion m) ^ n ↔ a ∈ p ^ n) :
    Function.Surjective (truncMap (Λ := Λ) p n) ∧
      RingHom.ker (truncMap (Λ := Λ) p n) = m ^ n := by
  constructor
  · intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := surjective_baseTruncMap m n (Ideal.Quotient.mk _ (Θ a))
    refine ⟨c, Ideal.Quotient.eq.mpr ?_⟩
    rw [← hpre, map_sub, hΛ]
    exact Ideal.Quotient.eq.mp hc
  · ext a
    rw [RingHom.mem_ker, truncMap_eq_zero_iff, ← hpre, hΛ, ← ker_baseTruncMap m n]
    exact Ideal.Quotient.eq_zero_iff_mem.symm

end Completion

/-! ### The completed local ring at the approximating point -/

section Approximation

open AlgebraicGeometry CategoryTheory

universe v w

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type v} [Category.{w} F] {p : F ⥤ AlgebraicGeometry.BigFppfOver B S hS}

/-- Reassociating a threefold composite. -/
private theorem assoc₃ {C : Type*} [Category C] {W X Y Z T : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ T) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  rw [Category.assoc, Category.assoc]

/-- Two commuting squares compose. -/
private theorem comp_square {C : Type*} [Category C] {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (u : X₁ ⟶ Y₁) (v : X₂ ⟶ Y₂) (ww : X₃ ⟶ Y₃)
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (h₁ : a ≫ v = u ≫ f) (h₂ : b ≫ ww = v ≫ g) :
    (a ≫ b) ≫ ww = u ≫ f ≫ g := by
  rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

/-- The base map of a composition of morphisms of formal objects is the composition of their
base maps. -/
private alias formalBaseMap_comp := Deformation.Artin.formalBaseMap_comp

/-- The base map of the identity is the identity. -/
private alias formalBaseMap_id := Deformation.Artin.formalBaseMap_id

/-- An isomorphism of formal objects induces an isomorphism of the spectra of their bases. -/
private def formalBaseMapIso {X Y : Deformation.Artin.FormalObject B S hS p} (e : X ≅ Y) :
    Spec (.of X.base.R) ≅ Spec (.of Y.base.R) where
  hom := e.hom.baseMap
  inv := e.inv.baseMap
  hom_inv_id := by rw [← formalBaseMap_comp, e.hom_inv_id, formalBaseMap_id]
  inv_hom_id := by rw [← formalBaseMap_comp, e.inv_hom_id, formalBaseMap_id]

/-- **An isomorphism of formal objects identifies their complete local base rings**, by a ring
isomorphism whose spectrum is the induced map of bases. -/
private theorem exists_formalBaseRingEquiv
    {X Y : Deformation.Artin.FormalObject B S hS p} (e : X ≅ Y) :
    ∃ w : Y.base.R ≃+* X.base.R,
      Spec.map (CommRingCat.ofHom w.toRingHom) = e.hom.baseMap := by
  let : CommRing X.base.R := X.base.commRing
  let : CommRing Y.base.R := Y.base.commRing
  exact ⟨(Spec.fullyFaithful.preimageIso (formalBaseMapIso e)).unop.commRingCatIsoToRingEquiv,
    Spec.fullyFaithful.map_preimage (formalBaseMapIso e).hom⟩

/-- A morphism of the big fppf category over `S`, read as a morphism of schemes, commutes
with the structure morphisms to `S`. -/
private theorem left_hom_comp_hom {T T' : AlgebraicGeometry.BigFppfOver B S hS}
    (α : T ⟶ T') (U : Over S) (hU : (Over.post B.inclusion).obj T' = U) :
    (α.left.hom ≫ eqToHom (congrArg Over.left hU)) ≫ U.hom =
      ((Over.post B.inclusion).obj T).hom := by
  subst hU
  refine Eq.trans ?_ (Over.w ((Over.post B.inclusion).map α))
  exact congrArg (fun t => t ≫ ((Over.post B.inclusion).obj T').hom)
    (Category.comp_id α.left.hom)

/-- Transport of the structure morphism of an object of the big fppf category over `S` along
an equality with an object of `Over S`. -/
private theorem comp_eqToHom_hom {T : AlgebraicGeometry.BigFppfOver B S hS} (U : Over S)
    (hU : (Over.post B.inclusion).obj T = U) :
    eqToHom (congrArg Over.left hU).symm ≫ ((Over.post B.inclusion).obj T).hom = U.hom := by
  subst hU
  simp

/-- **The complete local ring at the approximating point presents the base of the formal
object**, compatibly with the structure morphisms to `S`. -/
private theorem exists_completedLocalRing_equiv
    (hp : p.IsFiberedInGroupoids) (U : Over S) (x : F)
    (hx : (p ⋙ Over.post B.inclusion).obj x = U) (u₀ : U.left) [IsLocallyNoetherian U.left]
    (ξ : Deformation.Artin.FormalObject B S hS p)
    (xR : Deformation.Artin.CompleteLocalObjects B S hS p)
    (e : ξ ≅ (Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    (r : xR.obj.1 ⟶ x)
    (eR : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+*
      (Deformation.Artin.chosenBase B S hS p xR.obj).R)
    (hrbase : ((eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫
          p.map r).left.hom ≫ eqToHom (congrArg Over.left hx)) =
        Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (U.left.presheaf.stalk u₀)
              (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
          U.left.fromSpecStalk u₀) :
    ∃ Ψ : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* ξ.base.R,
      ξ.base.toS = (Spec.map (CommRingCat.ofHom Ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀) ≫ U.hom := by
  have hbase : (Deformation.Artin.chosenBase B S hS p xR.obj).toS =
      Spec.map (CommRingCat.ofHom eR.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀ ≫ U.hom := by
    have key := left_hom_comp_hom
      (eqToHom (Deformation.Artin.chosenBase_eq B S hS p xR.obj).symm ≫ p.map r) U hx
    rw [hrbase] at key
    have hpost : ((Over.post B.inclusion).obj (Deformation.Artin.baseOver B S hS
        (Deformation.Artin.chosenBase B S hS p xR.obj)
        (Deformation.Artin.chosenContains B S hS p xR.obj))).hom =
      (Deformation.Artin.chosenBase B S hS p xR.obj).toS := rfl
    rw [hpost] at key
    exact key.symm.trans (assoc₃ _ _ _ _)
  obtain ⟨e', -, hbase', -⟩ := Deformation.Artin.exists_approximationBase_presentation
    B S hS p hp U x hx u₀ xR ((Deformation.Artin.approximationFunctor B S hS p hp).obj xR)
    rfl r eR hrbase hbase
  obtain ⟨w, hw⟩ := exists_formalBaseRingEquiv e
  refine ⟨e'.trans w, ?_⟩
  have hsplit : Spec.map (CommRingCat.ofHom (e'.trans w).toRingHom) =
      Spec.map (CommRingCat.ofHom w.toRingHom) ≫
        Spec.map (CommRingCat.ofHom e'.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg
      (fun f : CommRingCat.of (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀) ⟶
        CommRingCat.of ξ.base.R => Spec.map f)
      (CommRingCat.hom_ext (RingHom.ext fun t => rfl))
  rw [hsplit, ← (Deformation.Artin.FormalObject.Hom.baseMap_spec e.hom).1, hw, hbase']
  simp only [Category.assoc]

end Approximation

/-! ### Preimages of the powers of the maximal ideal -/

section Preimage

/-- A ring isomorphism of local rings carries the maximal ideal onto the maximal ideal. -/
private theorem ringEquiv_map_maximalIdeal {A C : Type*} [CommRing A] [CommRing C]
    [IsLocalRing A] [IsLocalRing C] (e : A ≃+* C) :
    (maximalIdeal A).map (e : A →+* C) = maximalIdeal C := by
  have : IsLocalHom (e : A →+* C) := ⟨fun x h => by simpa using h.map (e.symm : C →+* A)⟩
  have hmax : (maximalIdeal C).comap (e : A →+* C) = maximalIdeal A :=
    IsLocalRing.maximalIdeal_comap _
  have hsurj : Function.Surjective (e : A →+* C) := fun y => ⟨e.symm y, by simp⟩
  rw [← hmax]
  exact Ideal.map_comap_of_surjective (e : A →+* C) hsurj (maximalIdeal C)

/-- A ring isomorphism of local rings carries the powers of the maximal ideal to each
other. -/
private theorem ringEquiv_mem_maximalIdeal_pow {A C : Type*} [CommRing A] [CommRing C]
    [IsLocalRing A] [IsLocalRing C] (e : A ≃+* C) (n : ℕ) {a : A}
    (ha : a ∈ maximalIdeal A ^ n) : e a ∈ maximalIdeal C ^ n := by
  have hpow : ((maximalIdeal A) ^ n).map (e : A →+* C) = maximalIdeal C ^ n := by
    rw [Ideal.map_pow, ringEquiv_map_maximalIdeal e]
  rw [← hpow]
  exact Ideal.mem_map_of_mem _ ha

/-- A ring isomorphism of local rings identifies the powers of the maximal ideals. -/
private theorem ringEquiv_mem_maximalIdeal_pow_iff {A C : Type*} [CommRing A] [CommRing C]
    [IsLocalRing A] [IsLocalRing C] (e : A ≃+* C) (n : ℕ) (a : A) :
    e a ∈ maximalIdeal C ^ n ↔ a ∈ maximalIdeal A ^ n :=
  ⟨fun h => by simpa using ringEquiv_mem_maximalIdeal_pow e.symm n h,
    fun h => ringEquiv_mem_maximalIdeal_pow e n h⟩

/-- The preimage of the `n`-th power of the maximal ideal of the completion of a Noetherian
local ring is the `n`-th power of the maximal ideal. -/
private theorem mem_maximalIdeal_pow_adicCompletion_iff {L : Type*} [CommRing L]
    [IsLocalRing L] [IsNoetherianRing L] (n : ℕ) (x : L) :
    algebraMap L (AdicCompletion (maximalIdeal L) L) x ∈
        maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔ x ∈ maximalIdeal L ^ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem (I := _ ^ n),
    ← map_eq_zero_iff _ (completionQuotientEquiv L n).injective, completionQuotientEquiv_mk]

end Preimage

/-! ### The affine chart at the approximating point -/

section Chart

open AlgebraicGeometry CategoryTheory Opposite

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {m : Ideal Λ} [m.IsMaximal]

/-- **The affine chart at the approximating point.** Let `U` be of finite type over
`S = Spec(Λ)`, let `u₀ ∈ U` be a point whose completed local ring is identified with
`R = Λ_𝔪^∧` compatibly with the structure morphisms to `S`, and let `W ⊆ U` be an affine open
neighbourhood of `u₀`. Then `A = Γ(U, W)` is of finite type over `Λ`, the prime `𝔭` of `u₀`
is maximal, and `Λ → A ⧸ 𝔭 ^ n` is surjective with kernel `𝔪 ^ n` for every `n`: the
infinitesimal neighbourhoods of `u₀` in `U` are the infinitesimal neighbourhoods of `𝔪` in
`Spec(Λ)`. -/
private theorem exists_chart_truncations
    (U : Over (Spec (CommRingCat.of Λ))) [IsLocallyNoetherian U.left]
    [LocallyOfFiniteType U.hom] (u₀ : U.left)
    (Ψ : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* completion m)
    (hΨ : Spec.map (CommRingCat.ofHom (algebraMap Λ (completion m))) =
      (Spec.map (CommRingCat.ofHom Ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀) ≫ U.hom)
    {W : U.left.Opens} (hW : IsAffineOpen W) (hu₀ : u₀ ∈ W) :
    ∃ _ : Algebra Λ Γ(U.left, W),
      Algebra.FiniteType Λ Γ(U.left, W) ∧
      Spec.map (CommRingCat.ofHom (algebraMap Λ Γ(U.left, W))) = hW.fromSpec ≫ U.hom ∧
      (hW.primeIdealOf ⟨u₀, hu₀⟩).asIdeal.IsMaximal ∧
      (∀ n, Function.Surjective
        (truncMap (Λ := Λ) (hW.primeIdealOf ⟨u₀, hu₀⟩).asIdeal n)) ∧
      ∀ n, RingHom.ker
        (truncMap (Λ := Λ) (hW.primeIdealOf ⟨u₀, hu₀⟩).asIdeal n) = m ^ n := by
  classical
  let algA : Algebra Λ Γ(U.left, W) :=
    (Spec.preimage (hW.fromSpec ≫ U.hom)).hom.toAlgebra
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap Λ Γ(U.left, W))) =
      hW.fromSpec ≫ U.hom := Spec.map_preimage _
  have hftspec : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ Γ(U.left, W)))) := by
    rw [hspec]
    infer_instance
  have hft : Algebra.FiniteType Λ Γ(U.left, W) :=
    AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp hftspec
  let algStalk : Algebra Γ(U.left, W) (U.left.presheaf.stalk u₀) :=
    TopCat.Presheaf.algebra_section_stalk U.left.presheaf ⟨u₀, hu₀⟩
  set p := (hW.primeIdealOf ⟨u₀, hu₀⟩).asIdeal with hpdef
  have hpprime : p.IsPrime := by
    rw [hpdef]
    infer_instance
  have hloc : IsLocalization.AtPrime (U.left.presheaf.stalk u₀) p :=
    hW.isLocalization_stalk ⟨u₀, hu₀⟩
  set Θ : Γ(U.left, W) →+* completion m :=
    (Ψ.toRingHom.comp
      (algebraMap (U.left.presheaf.stalk u₀)
        (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))).comp
      (algebraMap Γ(U.left, W) (U.left.presheaf.stalk u₀)) with hΘdef
  have hfs : U.left.fromSpecStalk u₀ =
      Spec.map (U.left.presheaf.germ W u₀ hu₀) ≫ hW.fromSpec := by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hu₀]
    rfl
  have hΛspec : Spec.map (CommRingCat.ofHom (algebraMap Λ (completion m))) =
      Spec.map (CommRingCat.ofHom (Θ.comp (algebraMap Λ Γ(U.left, W)))) := by
    rw [hΨ, hfs]
    simp only [Category.assoc]
    rw [← hspec]
    simp only [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => rfl))
  have hΛ : ∀ a : Λ, Θ (algebraMap Λ Γ(U.left, W) a) = algebraMap Λ (completion m) a := by
    have hmap := Spec.map_inj.mp hΛspec
    intro a
    exact (congrArg (fun g : CommRingCat.of Λ ⟶ CommRingCat.of (completion m) => g.hom a)
      hmap).symm
  have hpreL : ∀ (n : ℕ) (a : Γ(U.left, W)),
      Θ a ∈ maximalIdeal (completion m) ^ n ↔
        algebraMap Γ(U.left, W) (U.left.presheaf.stalk u₀) a ∈
          maximalIdeal (U.left.presheaf.stalk u₀) ^ n := by
    intro n a
    rw [hΘdef]
    change Ψ (algebraMap (U.left.presheaf.stalk u₀)
      (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)
      (algebraMap Γ(U.left, W) (U.left.presheaf.stalk u₀) a)) ∈ _ ↔ _
    rw [ringEquiv_mem_maximalIdeal_pow_iff Ψ n, mem_maximalIdeal_pow_adicCompletion_iff]
  have hp1 : ∀ a : Γ(U.left, W), Θ a ∈ maximalIdeal (completion m) ^ 1 ↔ a ∈ p ^ 1 := by
    intro a
    rw [hpreL 1 a, pow_one, pow_one,
      ← IsLocalization.AtPrime.under_maximalIdeal (U.left.presheaf.stalk u₀) p,
      Ideal.under_def]
    exact Ideal.mem_comap.symm
  have hpmax : p.IsMaximal := by
    have h := truncMap_spec_of_ringHom (m := m) p Θ hΛ 1 hp1
    exact isMaximal_of_truncMap h.1 h.2
  have hpre : ∀ (n : ℕ) (a : Γ(U.left, W)),
      Θ a ∈ maximalIdeal (completion m) ^ n ↔ a ∈ p ^ n := by
    intro n a
    rw [hpreL n a,
      ← IsLocalization.AtPrime.under_maximalIdeal_pow p (U.left.presheaf.stalk u₀) n,
      Ideal.under_def]
    exact Ideal.mem_comap.symm
  exact ⟨algA, hft, hspec, hpmax,
    fun n => (truncMap_spec_of_ringHom (m := m) p Θ hΛ n (hpre n)).1,
    fun n => (truncMap_spec_of_ringHom (m := m) p Θ hΛ n (hpre n)).2⟩

end Chart

/-! ### The deformation base read on the stalk of `S` at `𝔪` -/

section StalkBase

open AlgebraicGeometry CategoryTheory

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : Ideal Λ) [m.IsMaximal]

/-- The local ring of `S = Spec(Λ)` at the point `𝔪`. -/
public abbrev stalkPoint : Type u := (Spec (CommRingCat.of Λ)).presheaf.stalk (point m)

/-- **The local ring of `S = Spec(Λ)` at `𝔪` is `Λ_𝔪`.** -/
public def stalkEquiv : stalkPoint m ≃+* Localization.AtPrime m :=
  (Spec.stalkIso (CommRingCat.of Λ) (point m)).commRingCatIsoToRingEquiv

/-- `R = Λ_𝔪^∧` as an algebra over the local ring of `S` at `𝔪`. -/
public instance algebraStalkCompletion : Algebra (stalkPoint m) (completion m) :=
  ((algebraMap (Localization.AtPrime m) (completion m)).comp
    (stalkEquiv m).toRingHom).toAlgebra

omit [IsNoetherianRing Λ] in
/-- The structure map `𝒪_{S, 𝔪} → R = Λ_𝔪^∧` is the structure map of `Λ_𝔪` read through the
identification of the stalk with `Λ_𝔪`. -/
public theorem algebraMap_stalkPoint (x : stalkPoint m) :
    algebraMap (stalkPoint m) (completion m) x =
      algebraMap (Localization.AtPrime m) (completion m) (stalkEquiv m x) := rfl

omit [IsNoetherianRing Λ] in
/-- The canonical morphism `Spec(𝒪_{S, 𝔪}) ⟶ S` is the chart `Spec(Λ_𝔪) ⟶ S` read through
the identification of the stalk with `Λ_𝔪`. -/
public theorem fromSpecStalk_point :
    (Spec (CommRingCat.of Λ)).fromSpecStalk (point m) =
      Spec.map (Spec.stalkIso (CommRingCat.of Λ) (point m)).inv ≫ localChart m := by
  have h1 : (Spec (CommRingCat.of Λ)).fromSpecStalk (point m) =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv ≫
        (Spec (CommRingCat.of Λ)).presheaf.germ ⊤ (point m) trivial) :=
    Spec.fromSpecStalk_eq _ _
  rw [← Spec.algebraMap_stalkIso_inv, Spec.map_comp] at h1
  exact h1

variable (C : Type u) [CommRing C] (φ : Λ →+* C)
  (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (ψ : C →+* completion m) (hψ : ψ.comp φ = algebraMap Λ (completion m))
  (hR : B.Contains (Spec (CommRingCat.of (completion m))))

/-- The `𝒪_{S, 𝔪}`-algebra structure on the base ring of the Example's formal object. -/
public instance algebra_formalObject_base_stalk :
    Algebra (stalkPoint m) (formalObject m C φ B hS ψ hψ hR).base.R :=
  inferInstanceAs (Algebra (stalkPoint m) (completion m))

/-- The structure morphism of `R = Λ_𝔪^∧` factors through `Spec(𝒪_{S, 𝔪}) ⟶ S`. -/
public theorem base_toS_eq_stalk :
    Spec.map (CommRingCat.ofHom (algebraMap (stalkPoint m)
        (formalObject m C φ B hS ψ hψ hR).base.R)) ≫
        (Spec (CommRingCat.of Λ)).fromSpecStalk (point m) =
      (formalObject m C φ B hS ψ hψ hR).base.toS := by
  have hcomp : (Spec.stalkIso (CommRingCat.of Λ) (point m)).inv ≫
      CommRingCat.ofHom (algebraMap (stalkPoint m) (completion m)) =
      CommRingCat.ofHom (algebraMap (Localization.AtPrime m) (completion m)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    have hid := congrArg
      (fun f : CommRingCat.of (Localization.AtPrime (point m).asIdeal) ⟶
          CommRingCat.of (Localization.AtPrime (point m).asIdeal) => f.hom x)
      (Spec.stalkIso (CommRingCat.of Λ) (point m)).inv_hom_id
    change algebraMap (stalkPoint m) (completion m)
      ((Spec.stalkIso (CommRingCat.of Λ) (point m)).inv.hom x) = _
    rw [algebraMap_stalkPoint]
    exact congrArg (algebraMap (Localization.AtPrime m) (completion m)) hid
  change Spec.map (CommRingCat.ofHom (algebraMap (stalkPoint m) (completion m))) ≫
      (Spec (CommRingCat.of Λ)).fromSpecStalk (point m) =
    (formalObject m C φ B hS ψ hψ hR).base.toS
  rw [fromSpecStalk_point, ← Category.assoc, ← Spec.map_comp]
  exact (congrArg (fun f : CommRingCat.of (Localization.AtPrime m) ⟶
      CommRingCat.of (completion m) => Spec.map f ≫ localChart m) hcomp).trans
    (base_toS_eq m C φ B hS ψ hψ hR)

/-- The identification of the stalk with `Λ_𝔪` is a local homomorphism. -/
public instance isLocalHom_stalkEquiv :
    IsLocalHom (stalkEquiv m : stalkPoint m →+* Localization.AtPrime m) :=
  ⟨fun x hx => by
    simpa using hx.map ((stalkEquiv m).symm : Localization.AtPrime m →+* stalkPoint m)⟩

/-- The structure map `𝒪_{S, 𝔪} → R = Λ_𝔪^∧` is a local homomorphism. -/
public instance isLocalHom_algebraMap_stalk :
    IsLocalHom (algebraMap (stalkPoint m) (completion m)) :=
  ⟨fun x hx => by
    have h1 : IsUnit (stalkEquiv m x) :=
      (isLocalHom_algebraMap_completion m).map_nonunit _ hx
    simpa using h1.map ((stalkEquiv m).symm : Localization.AtPrime m →+* stalkPoint m)⟩

/-- The structure morphism `Algebra.ofId` of `R = Λ_𝔪^∧` over `𝒪_{S, 𝔪}` is a local
homomorphism. -/
public instance isLocalHom_ofId_stalk :
    IsLocalHom (Algebra.ofId (stalkPoint m) (completion m)) :=
  ⟨fun a ha => (isLocalHom_algebraMap_stalk m).map_nonunit a ha⟩

/-- **The residue field of `𝒪_{S, 𝔪}` is that of `R = Λ_𝔪^∧`.** -/
public theorem bijective_residueField_map_stalk :
    Function.Bijective (IsLocalRing.ResidueField.map
      (algebraMap (stalkPoint m) (completion m))) := by
  have hη : Function.Bijective (IsLocalRing.ResidueField.map
      (stalkEquiv m : stalkPoint m →+* Localization.AtPrime m)) := by
    refine ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := (stalkEquiv m).surjective b
    exact ⟨IsLocalRing.residue _ a, IsLocalRing.ResidueField.map_residue _ _⟩
  have hcomp : Function.Bijective (IsLocalRing.ResidueField.map
      ((algebraMap (Localization.AtPrime m) (completion m)).comp
        (stalkEquiv m : stalkPoint m →+* Localization.AtPrime m))) := by
    rw [IsLocalRing.ResidueField.map_comp]
    exact (AdicCompletion.residueField_map_bijective (Localization.AtPrime m)).comp hη
  exact hcomp

/-- **The residue field of `R = Λ_𝔪^∧` as the residue field of `𝒪_{S, 𝔪}`.** -/
public def residueFieldEquivCompletionStalk :
    ResidueField (stalkPoint m) ≃ₐ[stalkPoint m] ResidueField (completion m) :=
  AlgEquiv.ofBijective
    (IsLocalRing.ResidueField.mapAlgHom (Algebra.ofId (stalkPoint m) (completion m)))
    (bijective_residueField_map_stalk m)

/-- **`R = Λ_𝔪^∧` has the same adic truncations as `𝒪_{S, 𝔪}`.** -/
public theorem hasBaseTruncations_stalk :
    Deformation.HasBaseTruncations
      ((formalObject m C φ B hS ψ hψ hR).completeLocalBase (stalkPoint m)) := by
  intro n
  change Function.Bijective (IsScalarTower.toAlgHom (stalkPoint m)
    (stalkPoint m ⧸ maximalIdeal (stalkPoint m) ^ n)
    (completion m ⧸ Ideal.map (algebraMap (stalkPoint m) (completion m))
      (maximalIdeal (stalkPoint m) ^ n)))
  have hLoc : Function.Bijective (IsScalarTower.toAlgHom (Localization.AtPrime m)
      (Localization.AtPrime m ⧸ maximalIdeal (Localization.AtPrime m) ^ n)
      (completion m ⧸ Ideal.map (algebraMap (Localization.AtPrime m) (completion m))
        (maximalIdeal (Localization.AtPrime m) ^ n))) :=
    hasBaseTruncations_completeBase m n
  have hJ : Ideal.map (algebraMap (stalkPoint m) (completion m))
        (maximalIdeal (stalkPoint m) ^ n) =
      Ideal.map (algebraMap (Localization.AtPrime m) (completion m))
        (maximalIdeal (Localization.AtPrime m) ^ n) := by
    have hmapcomp : (algebraMap (stalkPoint m) (completion m)) =
        (algebraMap (Localization.AtPrime m) (completion m)).comp
          (stalkEquiv m : stalkPoint m →+* Localization.AtPrime m) := rfl
    rw [hmapcomp, ← Ideal.map_map, Ideal.map_pow, ringEquiv_map_maximalIdeal (stalkEquiv m)]
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine Ideal.Quotient.eq.mpr ?_
    have hdiff : algebraMap (stalkPoint m) (completion m) (a - b) ∈
        Ideal.map (algebraMap (stalkPoint m) (completion m))
          (maximalIdeal (stalkPoint m) ^ n) := by
      rw [map_sub]
      exact Ideal.Quotient.eq.mp hxy
    rw [hJ, algebraMap_stalkPoint, map_sub] at hdiff
    have hLocmem : stalkEquiv m a - stalkEquiv m b ∈
        maximalIdeal (Localization.AtPrime m) ^ n :=
      Ideal.Quotient.eq.mp (hLoc.1 (a₁ := Ideal.Quotient.mk _ (stalkEquiv m a))
        (a₂ := Ideal.Quotient.mk _ (stalkEquiv m b)) (Ideal.Quotient.eq.mpr hdiff))
    exact (ringEquiv_mem_maximalIdeal_pow_iff (stalkEquiv m) n (a - b)).mp
      (by rwa [map_sub])
  · intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨w, hw⟩ := hLoc.2 (Ideal.Quotient.mk _ z)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨Ideal.Quotient.mk _ ((stalkEquiv m).symm c), Ideal.Quotient.eq.mpr ?_⟩
    have hmem : algebraMap (Localization.AtPrime m) (completion m) c - z ∈
        Ideal.map (algebraMap (Localization.AtPrime m) (completion m))
          (maximalIdeal (Localization.AtPrime m) ^ n) := Ideal.Quotient.eq.mp hw
    rw [← hJ] at hmem
    rwa [algebraMap_stalkPoint, RingEquiv.apply_symm_apply]

/-- **The formal object `ξ` over `R = Λ_𝔪^∧` is versal relative to the local ring of `S` at
`𝔪`.** -/
public theorem isVersal_formalObject_stalk :
    @Deformation.Artin.FormalObject.IsVersal B (Spec (CommRingCat.of Λ)) hS _ _
      (stack m C φ B hS).val.p ((stack m C φ B hS).isFiberedInGroupoids)
      (formalObject m C φ B hS ψ hψ hR) (stalkPoint m) _
      (algebra_formalObject_base_stalk m C φ B hS ψ hψ hR)
      ((Spec (CommRingCat.of Λ)).fromSpecStalk (point m))
      (base_toS_eq_stalk m C φ B hS ψ hψ hR) := by
  intro P
  exact Deformation.isSmooth_of_subsingleton_restrictedCoyoneda
    (Deformation.nonempty_subsingleton_hom_of_hasBaseTruncations
      (residueFieldEquivCompletionStalk m)
      ((formalObject m C φ B hS ψ hψ hR).completeLocalBase (stalkPoint m))
      (hasBaseTruncations_stalk m C φ B hS ψ hψ hR))
    (Deformation.Artin.exists_vertical_predeformationHom
      (fun s t h => stack_map_injective m C φ B hS s t h)
      (fun e => exists_verticalHom m C φ B hS e))
    (fun s t h => Deformation.Artin.predeformationCategory_hom_ext
      (fun s' t' h' => stack_map_injective m C φ B hS s' t' h') s t h) _

end StalkBase

/-! ### The Example -/

section TheExample

open AlgebraicGeometry CategoryTheory

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (m : Ideal Λ) [m.IsMaximal]
  (C : Type u) [CommRing C] (φ : Λ →+* C)
  (B : AlgebraicGeometry.BigFppfSite.{u}) (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (ψ : C →+* completion m) (hψ : ψ.comp φ = algebraMap Λ (completion m))
  (hR : B.Contains (Spec (CommRingCat.of (completion m))))

/-- The closed point of `Spec(R)` lies over `𝔪`. -/
private theorem base_toS_closedPoint :
    (formalObject m C φ B hS ψ hψ hR).base.toS
        (IsLocalRing.closedPoint (formalObject m C φ B hS ψ hψ hR).base.R) = point m :=
  PrimeSpectrum.ext (comap_maximalIdeal_completion m)

omit [IsNoetherianRing Λ] in
/-- **An object of `𝒳 = 𝒮_F` over `U` is a factorization of `U → S` through `g : S' ⟶ S`.** -/
private theorem exists_factorization_of_object
    (U : Over (Spec (CommRingCat.of Λ))) (z : (stack m C φ B hS).val.obj)
    (hz : ((stack m C φ B hS).val.p ⋙ Over.post B.inclusion).obj z = U) :
    ∃ g : U.left ⟶ auxScheme m C, g ≫ auxMap m C φ = U.hom := by
  have hfac : Factors m C φ B hS ((stack m C φ B hS).val.p.obj z) :=
    (Discrete.as (show Discrete ((functor m C φ B hS).obj (Opposite.op z.base)) from
      z.fiber)).down.down
  obtain ⟨h, hh⟩ := hfac
  refine ⟨eqToHom (congrArg Over.left hz).symm ≫ h, ?_⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => eqToHom (congrArg Over.left hz).symm ≫ t) hh).trans
      (comp_eqToHom_hom U hz))

/-- Let `Λ` be a Noetherian ring, let `𝔪 ⊂ Λ` be a maximal
ideal, let `R = Λ_𝔪^∧`, and let `Λ → C → R` be a factorization with `C` of finite type over
`Λ`. Set `S = Spec(Λ)`, `U = S ∖ {𝔪}` and `S' = U ⨿ Spec(C)`, and let `F`, `𝒳 = 𝒮_F` and `ξ`
be the functor on the big fppf site of `S`, the category fibred in sets it defines, and the
formal object over `R` that the Example builds from that factorization. Then

* `F` is the functor the Example displays: its value at `T` is a subsingleton, and it is
  nonempty exactly when the structure morphism of `T` factors through `S'`,
* `𝒳 → (Sch/S)_{fppf}` is limit preserving on objects,
* `ξ` is effective,
* `ξ` is versal, relative to `𝒪_{S, 𝔪}`, and
* **if** the conclusion of Stacks 07XH holds for all of these `𝒳` -- that is, if every
  factorization `Λ → C' → R` with `C'` of finite type over `Λ` carries the three-item datum
  `Deformation.Artin.AlgebraizesFiniteTypeFactorizations` that the Example reads off that
  conclusion, namely a finite type `Λ`-algebra `A` with a maximal ideal `𝔪_A` over `𝔪` such
  that `κ(𝔪) = κ(𝔪_A)`, such that `Λ → A` satisfies condition (4) of Stacks 02HT at `𝔪_A`
  -- hence is smooth there -- and such that `C'` maps to `A` over `Λ` -- then `C` maps to
  every henselian local `Λ`-algebra `H` whose maximal ideal contracts to `𝔪` by a
  `Λ`-algebra map, and every finite system of polynomial equations over `Λ` with a solution
  in `R` has a solution in a henselization of `Λ_𝔪`.

**No G-ring hypothesis is made, and the conclusion of Stacks 07XH is assumed rather than
used:** it enters only as the antecedent of the last clause. -/
@[stacks 07XI "the Example whole, in the Example's own logical direction: the functor `F` on \
the big fppf site of `S = Spec(Λ)` \
(`Deformation.Artin.GRingCounterexample.functor`, whose displayed defining property -- a \
one-point set on a `T` whose structure morphism factors through `S' = (S ∖ {𝔪}) ⨿ Spec(C)`, \
empty otherwise -- is the first conjunct below), the category `𝒳 = 𝒮_F` fibred in sets it \
defines (`Deformation.Artin.GRingCounterexample.stack`), the formal object `ξ` over \
`R = Λ_𝔪^∧` (`Deformation.Artin.GRingCounterexample.formalObject`), the source's three \
assertions about them -- limit preservation on objects, effectivity and versality of `ξ` -- \
and the Example's conditional conclusion: IF the conclusion of Stacks 07XH holds for all \
these `𝒳`, i.e. if every finite type factorization `Λ → C' → R` carries the three-item datum \
the Example reads off it (`Deformation.Artin.AlgebraizesFiniteTypeFactorizations`: a finite \
type `Λ`-algebra `A`, a maximal ideal `𝔪_A` over `𝔪` with `κ(𝔪) = κ(𝔪_A)` and condition (4) \
of Stacks 02HT, and a `Λ`-algebra map `C' → A`), THEN `C` maps over `Λ` to every henselian \
local `Λ`-algebra whose maximal ideal contracts to `𝔪` and every polynomial system over `Λ` \
with a solution in `R` has a solution in a henselization of `Λ_𝔪` -- the approximation \
property for `Λ_𝔪^h`, which is the source's closing sentence. The G-ring property is NOT \
hypothesised anywhere here: in the Example it is the *conclusion* drawn from that \
approximation property (\\\"In this example we show that the local ring `O_{S, s}` has to be a \
G-ring in order for the result of Lemma 07XH to be true\\\"), and the conclusion of 07XH is \
assumed, in the antecedent, rather than derived from a G-ring assumption. NOT covered: the \
source's final step, from the approximation property of `Λ_𝔪^h` to `Λ_𝔪^h` and then `Λ_𝔪` \
being G-rings, which the Stacks Project itself defers (\\\"insert future reference here\\\"), \
so there is no statement to formalize against."]
public theorem exists_algHom_henselian (hφ : RingHom.FiniteType φ) :
    (∀ T : (AlgebraicGeometry.BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ,
        Subsingleton ((functor m C φ B hS).obj T) ∧
          (Nonempty ((functor m C φ B hS).obj T) ↔ Factors m C φ B hS T.unop)) ∧
      AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B
        (Spec (CommRingCat.of Λ)) hS (stack m C φ B hS)
        (Deformation.Artin.Approximation.baseFiberedCategory B (Spec (CommRingCat.of Λ)) hS)
        (Deformation.Artin.Approximation.structureMorphism B (Spec (CommRingCat.of Λ)) hS
          (stack m C φ B hS)) ∧
      Deformation.Artin.FormalObject.IsEffective B (Spec (CommRingCat.of Λ)) hS
        (stack m C φ B hS).val.p ((stack m C φ B hS).isFiberedInGroupoids)
        (formalObject m C φ B hS ψ hψ hR) ∧
      (@Deformation.Artin.FormalObject.IsVersal B (Spec (CommRingCat.of Λ)) hS _ _
        (stack m C φ B hS).val.p ((stack m C φ B hS).isFiberedInGroupoids)
        (formalObject m C φ B hS ψ hψ hR) (stalkPoint m) _
        (algebra_formalObject_base_stalk m C φ B hS ψ hψ hR)
        ((Spec (CommRingCat.of Λ)).fromSpecStalk (point m))
        (base_toS_eq_stalk m C φ B hS ψ hψ hR)) ∧
      (Deformation.Artin.AlgebraizesFiniteTypeFactorizations Λ m (completion m) →
        (∀ (H : Type u) [CommRing H] [HenselianLocalRing H] [Algebra Λ H],
            m = (maximalIdeal H).comap (algebraMap Λ H) →
            ∃ χ : C →+* H, χ.comp φ = algebraMap Λ H) ∧
          ∀ (H : Type u) [CommRing H] [IsLocalRing H] [Algebra Λ H]
              [Algebra (Localization.AtPrime m) H]
              [IsScalarTower Λ (Localization.AtPrime m) H]
              [IsHenselization (Localization.AtPrime m)
                (ResidueField (Localization.AtPrime m)) H]
              (n k : ℕ) (f : Fin k → MvPolynomial (Fin n) Λ) (a : Fin n → completion m),
            (∀ j, MvPolynomial.aeval a (f j) = 0) →
              ∃ b : Fin n → H, ∀ j, MvPolynomial.aeval b (f j) = 0) :=
  ⟨fun _ => ⟨inferInstance, ⟨fun z => z.some.down.down,
      fun h => ⟨ULift.up (PLift.up h)⟩⟩⟩,
    isLimitPreservingOnObjects_stack m C φ B hS hφ,
    isEffective_formalObject m C φ B hS ψ hψ hR,
    isVersal_formalObject_stalk m C φ B hS ψ hψ hR,
    fun hyp =>
      ⟨fun _ _ _ _ hH =>
        Deformation.Artin.exists_ringHom_of_algebraizesFiniteTypeFactorizations hyp φ hφ ψ hψ hH,
      fun H _ _ _ _ _ _ _ _ f a ha =>
        Deformation.Artin.exists_solution_henselization_of_algebraizesFiniteTypeFactorizations
          Λ m hyp H f a ha⟩⟩

/-- **The converse implication, which is a consequence of Stacks 07XH rather than a part of
Stacks 07XI.** Let `Λ` be a Noetherian ring, let `𝔪 ⊂ Λ` be a maximal ideal, let
`R = Λ_𝔪^∧`, and let `Λ → C → R` be a factorization with `C` of finite type over `Λ`. Set
`S = Spec(Λ)` and let `F`, `𝒳 = 𝒮_F` and `ξ` be the functor on the big fppf site of `S`, the
category fibred in sets it defines, and the formal object over `R` that the Example builds
from that factorization. Assume the local ring `𝒪_{S, 𝔪}` is a G-ring. Then

* `F` is the functor the Example displays: its value at `T` is a subsingleton, and it is
  nonempty exactly when the structure morphism of `T` factors through
  `S' = (S ∖ {𝔪}) ⨿ Spec(C)`,
* `𝒳 → (Sch/S)_{fppf}` is limit preserving on objects,
* `ξ` is effective,
* `ξ` is versal, relative to `𝒪_{S, 𝔪}`,

and consequently `C` maps to every henselian local `Λ`-algebra `H` whose maximal ideal
contracts to `𝔪` by a `Λ`-algebra map -- for `C = Λ[y_1, …, y_n]/(f_1, …, f_k)` and `C → R`
a solution of `f_1 = … = f_k = 0` in `R`, a solution of that system in `H`. -/
public theorem exists_algHom_henselian_of_isGRing (hφ : RingHom.FiniteType φ)
    (hG : IsGRing (stalkPoint m))
    (H : Type u) [CommRing H] [HenselianLocalRing H] [Algebra Λ H]
    (hH : m = (maximalIdeal H).comap (algebraMap Λ H)) :
    (∀ T : (AlgebraicGeometry.BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ,
        Subsingleton ((functor m C φ B hS).obj T) ∧
          (Nonempty ((functor m C φ B hS).obj T) ↔ Factors m C φ B hS T.unop)) ∧
      AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects.{u, u, u, u, u + 1} B
        (Spec (CommRingCat.of Λ)) hS (stack m C φ B hS)
        (Deformation.Artin.Approximation.baseFiberedCategory B (Spec (CommRingCat.of Λ)) hS)
        (Deformation.Artin.Approximation.structureMorphism B (Spec (CommRingCat.of Λ)) hS
          (stack m C φ B hS)) ∧
      Deformation.Artin.FormalObject.IsEffective B (Spec (CommRingCat.of Λ)) hS
        (stack m C φ B hS).val.p ((stack m C φ B hS).isFiberedInGroupoids)
        (formalObject m C φ B hS ψ hψ hR) ∧
      (@Deformation.Artin.FormalObject.IsVersal B (Spec (CommRingCat.of Λ)) hS _ _
        (stack m C φ B hS).val.p ((stack m C φ B hS).isFiberedInGroupoids)
        (formalObject m C φ B hS ψ hψ hR) (stalkPoint m) _
        (algebra_formalObject_base_stalk m C φ B hS ψ hψ hR)
        ((Spec (CommRingCat.of Λ)).fromSpecStalk (point m))
        (base_toS_eq_stalk m C φ B hS ψ hψ hR)) ∧
      ∃ χ : C →+* H, χ.comp φ = algebraMap Λ H := by
  classical
  have hlimit := isLimitPreservingOnObjects_stack m C φ B hS hφ
  have heff := isEffective_formalObject m C φ B hS ψ hψ hR
  have hvers := isVersal_formalObject_stalk m C φ B hS ψ hψ hR
  refine ⟨fun T => ⟨inferInstance, ⟨fun z => z.some.down.down,
    fun h => ⟨ULift.up (PLift.up h)⟩⟩⟩, hlimit, heff, hvers, ?_⟩
  obtain ⟨U, u₀, V, -, x, hx, hfin, hqc, hu₀ft, -, -, xR, e, r, eR, -, hrbase⟩ :=
    @Deformation.Artin.exists_finiteType_versal_approximation B (Spec (CommRingCat.of Λ)) hS _
      (stack m C φ B hS) (formalObject m C φ B hS ψ hψ hR) heff (point m)
      (base_toS_closedPoint m C φ B hS ψ hψ hR) hG hlimit
      (algebra_formalObject_base_stalk m C φ B hS ψ hψ hR)
      ((Spec (CommRingCat.of Λ)).fromSpecStalk (point m)) rfl
      (base_toS_eq_stalk m C φ B hS ψ hψ hR) hvers
  have : LocallyOfFiniteType U.hom := hfin
  have : QuasiCompact U.hom := hqc
  have : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_completedLocalRing_equiv
    ((stack m C φ B hS).isFiberedInGroupoids) U x.1 hx u₀
    (formalObject m C φ B hS ψ hψ hR) xR e r eR hrbase
  let Ψ : AlgebraicGeometry.Scheme.completedLocalRing U.left u₀ ≃+* completion m := Ψ₀
  have hΨ' : Spec.map (CommRingCat.ofHom (algebraMap Λ (completion m))) =
      (Spec.map (CommRingCat.ofHom Ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀) ≫ U.hom := hΨ₀
  have hΨloc : IsLocalHom (Ψ.toRingHom) :=
    ⟨fun y hy => by simpa using hy.map Ψ.symm.toRingHom⟩
  have hstalkloc : IsLocalHom (algebraMap (U.left.presheaf.stalk u₀)
      (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) :=
    AdicCompletion.algebraMap_isLocalHom_of_fg
      (maximalIdeal (U.left.presheaf.stalk u₀)).fg_of_isNoetherianRing
  have hu₀pt : U.hom u₀ = point m := by
    have h := congrArg
      (fun t : Spec (CommRingCat.of (completion m)) ⟶ Spec (CommRingCat.of Λ) =>
        t (IsLocalRing.closedPoint (completion m))) hΨ'
    have hleft : Spec.map (CommRingCat.ofHom (algebraMap Λ (completion m)))
        (IsLocalRing.closedPoint (completion m)) = point m :=
      PrimeSpectrum.ext (comap_maximalIdeal_completion m)
    have hp1 : Spec.map (CommRingCat.ofHom Ψ.toRingHom)
        (IsLocalRing.closedPoint (completion m)) =
        IsLocalRing.closedPoint
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀) :=
      IsLocalRing.comap_closedPoint _
    have hp2 : Spec.map (CommRingCat.ofHom
          (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)))
          (IsLocalRing.closedPoint
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀)) =
        IsLocalRing.closedPoint (U.left.presheaf.stalk u₀) :=
      IsLocalRing.comap_closedPoint _
    have e1 := Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom Ψ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀) U.hom (IsLocalRing.closedPoint (completion m))
    have e2 := Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom Ψ.toRingHom))
      (Spec.map (CommRingCat.ofHom
          (algebraMap (U.left.presheaf.stalk u₀)
            (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))) ≫
        U.left.fromSpecStalk u₀) (IsLocalRing.closedPoint (completion m))
    have e3 := Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom
        (algebraMap (U.left.presheaf.stalk u₀)
          (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))))
      (U.left.fromSpecStalk u₀)
      (IsLocalRing.closedPoint (AlgebraicGeometry.Scheme.completedLocalRing U.left u₀))
    rw [hleft, e1, e2, hp1, e3, hp2, Scheme.fromSpecStalk_closedPoint] at h
    exact h.symm
  obtain ⟨g, hg⟩ := exists_factorization_of_object m C φ B hS U x.1 hx
  have hrange : g u₀ ∈ Set.range (auxInr m C) := by
    have hcompl := AlgebraicGeometry.isCompl_range_inl_inr
      (openComplement m).toScheme (Spec (CommRingCat.of C))
    have hall := Set.eq_univ_iff_forall.mp (codisjoint_iff.mp hcompl.codisjoint) (g u₀)
    rcases hall with hl | hr
    · exfalso
      obtain ⟨w, hw⟩ := hl
      have hval : U.hom u₀ = w.1 := by
        have h1 : (g ≫ auxMap m C φ) u₀ = U.hom u₀ := by rw [hg]
        have h2 : (g ≫ auxMap m C φ) u₀ = auxMap m C φ (g u₀) :=
          Scheme.Hom.comp_apply _ _ _
        have h3 : auxMap m C φ (auxInl m C w) = (openComplement m).ι w :=
          (Scheme.Hom.comp_apply _ _ _).symm.trans
            (congrArg (fun t : (openComplement m).toScheme ⟶ Spec (CommRingCat.of Λ) => t w)
              (auxInl_auxMap m C φ))
        rw [← h1, h2, ← hw]
        exact h3
      exact w.2 (by rw [← hval, hu₀pt]; rfl)
    · exact hr
  have : IsOpenImmersion (auxInr m C) :=
    inferInstanceAs (IsOpenImmersion (Limits.coprod.inr :
      Spec (CommRingCat.of C) ⟶ (openComplement m).toScheme ⨿ Spec (CommRingCat.of C)))
  obtain ⟨-, ⟨W, hW, rfl⟩, hu₀W, hWsub⟩ :=
    U.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show u₀ ∈ (g ⁻¹ᵁ (auxInr m C).opensRange : U.left.Opens).1 from hrange)
      (g ⁻¹ᵁ (auxInr m C).opensRange).2
  obtain ⟨algA, hft, hspecA, hpmax, hsurj, hker⟩ :=
    exists_chart_truncations U u₀ Ψ hΨ' hW hu₀W
  let := algA
  have := hpmax
  have hmA : m = (hW.primeIdealOf ⟨u₀, hu₀W⟩).asIdeal.comap (algebraMap Λ Γ(U.left, W)) :=
    comap_eq_of_ker_truncMap (hker 1)
  have hresf : Function.Bijective (Ideal.ResidueField.map m
      (hW.primeIdealOf ⟨u₀, hu₀W⟩).asIdeal (algebraMap Λ Γ(U.left, W)) hmA) :=
    bijective_residueFieldMap_of_truncMap (hsurj 1) (hker 1)
  have hsm : Algebra.IsSmoothAt Λ (hW.primeIdealOf ⟨u₀, hu₀W⟩).asIdeal :=
    isSmoothAt_of_truncMap hsurj hker
  have hrangeW : Set.range (hW.fromSpec ≫ g) ⊆ Set.range (auxInr m C) := by
    rintro z ⟨y, rfl⟩
    have hmemW : hW.fromSpec y ∈ (W : Set U.left) := hW.range_fromSpec ▸ Set.mem_range_self y
    exact hWsub hmemW
  obtain ⟨κ, hκfac⟩ : ∃ κ : Spec Γ(U.left, W) ⟶ Spec (CommRingCat.of C),
      κ ≫ auxInr m C = hW.fromSpec ≫ g :=
    ⟨AlgebraicGeometry.IsOpenImmersion.lift (auxInr m C) (hW.fromSpec ≫ g) hrangeW,
      AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨ρC, hρCspec⟩ : ∃ ρ : CommRingCat.of C ⟶ Γ(U.left, W), Spec.map ρ = κ :=
    ⟨Spec.preimage κ, Spec.map_preimage κ⟩
  have hρC : ρC.hom.comp φ = algebraMap Λ Γ(U.left, W) := by
    have hspecκ : Spec.map (CommRingCat.ofHom φ ≫ ρC) =
        Spec.map (CommRingCat.ofHom (algebraMap Λ Γ(U.left, W))) := by
      calc Spec.map (CommRingCat.ofHom φ ≫ ρC)
          = Spec.map ρC ≫ Spec.map (CommRingCat.ofHom φ) := Spec.map_comp _ _
        _ = Spec.map ρC ≫ auxInr m C ≫ auxMap m C φ := by rw [auxInr_auxMap]
        _ = (Spec.map ρC ≫ auxInr m C) ≫ auxMap m C φ := (Category.assoc _ _ _).symm
        _ = (hW.fromSpec ≫ g) ≫ auxMap m C φ := by rw [hρCspec, hκfac]
        _ = hW.fromSpec ≫ g ≫ auxMap m C φ := Category.assoc _ _ _
        _ = hW.fromSpec ≫ U.hom := by rw [hg]
        _ = Spec.map (CommRingCat.ofHom (algebraMap Λ Γ(U.left, W))) := hspecA.symm
    exact congrArg CommRingCat.Hom.hom (Spec.map_inj.mp hspecκ)
  obtain ⟨F⟩ := Deformation.Artin.exists_algHom_of_isSmoothAt hft
    (hW.primeIdealOf ⟨u₀, hu₀W⟩).asIdeal hmA hresf hsm hH
  refine ⟨(F : Γ(U.left, W) →+* H).comp ρC.hom, ?_⟩
  rw [RingHom.comp_assoc, hρC]
  exact F.comp_algebraMap

include B hS hR in
/-- **The converse implication in the Example's closing form.** If the local ring `𝒪_{S, 𝔪}`
is a G-ring, then every finite system of polynomial equations over `Λ` with a solution in
`R = Λ_𝔪^∧` has a solution in every henselian local `Λ`-algebra whose maximal ideal contracts
to `𝔪` -- in particular in the henselization of `Λ_𝔪`, whose existence in the universe of `Λ`
is `Deformation.Artin.exists_henselization_over_maximalIdeal`. -/
public theorem exists_solution_of_isGRing (hG : IsGRing (stalkPoint m))
    (H : Type u) [CommRing H] [HenselianLocalRing H] [Algebra Λ H]
    (hH : m = (maximalIdeal H).comap (algebraMap Λ H))
    {n k : ℕ} (f : Fin k → MvPolynomial (Fin n) Λ) (a : Fin n → completion m)
    (ha : ∀ j, MvPolynomial.aeval a (f j) = 0) :
    ∃ b : Fin n → H, ∀ j, MvPolynomial.aeval b (f j) = 0 := by
  classical
  set I : Ideal (MvPolynomial (Fin n) Λ) := Ideal.span (Set.range f) with hI
  have hmem : ∀ j, f j ∈ I := fun j => by
    rw [hI]
    exact Ideal.subset_span ⟨j, rfl⟩
  have hker : ∀ z ∈ I,
      ((MvPolynomial.aeval a : MvPolynomial (Fin n) Λ →ₐ[Λ] completion m) :
        MvPolynomial (Fin n) Λ →+* completion m) z = 0 := by
    have hle : I ≤ RingHom.ker
        ((MvPolynomial.aeval a : MvPolynomial (Fin n) Λ →ₐ[Λ] completion m) :
          MvPolynomial (Fin n) Λ →+* completion m) := by
      rw [hI, Ideal.span_le]
      rintro w ⟨j, rfl⟩
      simpa [SetLike.mem_coe, RingHom.mem_ker] using ha j
    exact fun z hz => hle hz
  have hCft : RingHom.FiniteType
      ((Ideal.Quotient.mk I).comp (MvPolynomial.C : Λ →+* MvPolynomial (Fin n) Λ)) := by
    refine RingHom.FiniteType.comp_surjective ?_ Ideal.Quotient.mk_surjective
    rw [← MvPolynomial.algebraMap_eq]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hψq : (Ideal.Quotient.lift I
        ((MvPolynomial.aeval a : MvPolynomial (Fin n) Λ →ₐ[Λ] completion m) :
          MvPolynomial (Fin n) Λ →+* completion m) hker).comp
        ((Ideal.Quotient.mk I).comp (MvPolynomial.C : Λ →+* MvPolynomial (Fin n) Λ)) =
      algebraMap Λ (completion m) := by
    refine RingHom.ext fun c => ?_
    change Ideal.Quotient.lift I _ hker (Ideal.Quotient.mk I (MvPolynomial.C c)) = _
    rw [Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_C a c
  obtain ⟨-, -, -, -, χ, hχ⟩ := exists_algHom_henselian_of_isGRing m
    (MvPolynomial (Fin n) Λ ⧸ I)
    ((Ideal.Quotient.mk I).comp (MvPolynomial.C : Λ →+* MvPolynomial (Fin n) Λ)) B hS
    (Ideal.Quotient.lift I
      ((MvPolynomial.aeval a : MvPolynomial (Fin n) Λ →ₐ[Λ] completion m) :
        MvPolynomial (Fin n) Λ →+* completion m) hker) hψq hR hCft hG H hH
  set Θ : MvPolynomial (Fin n) Λ →ₐ[Λ] H :=
    { toRingHom := χ.comp (Ideal.Quotient.mk I)
      commutes' := fun c => congrArg (fun g : Λ →+* H => g c) hχ } with hΘ
  refine ⟨fun i => Θ (MvPolynomial.X i), fun j => ?_⟩
  have hu : Θ = MvPolynomial.aeval (⇑Θ ∘ MvPolynomial.X) := MvPolynomial.aeval_unique Θ
  have hz : Θ (f j) = 0 := by
    change χ (Ideal.Quotient.mk I (f j)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hmem j), map_zero]
  rw [show (fun i => Θ (MvPolynomial.X i)) = (⇑Θ ∘ MvPolynomial.X) from rfl, ← hu]
  exact hz

include B hS hR in
/-- **The approximation property of `Λ_𝔪^h`.** If the local ring `𝒪_{S, 𝔪}` is a G-ring, every
finite system of polynomial equations over `Λ` with a solution in `R = Λ_𝔪^∧` has a solution in
a henselization `H` of `Λ_𝔪`. A henselization of `Λ_𝔪` in the universe of `Λ` exists, by
`Deformation.Artin.exists_henselization_over_maximalIdeal`. -/
public theorem exists_solution_henselization_of_isGRing (hG : IsGRing (stalkPoint m))
    (H : Type u) [CommRing H] [IsLocalRing H] [Algebra Λ H]
    [Algebra (Localization.AtPrime m) H] [IsScalarTower Λ (Localization.AtPrime m) H]
    [IsHenselization (Localization.AtPrime m) (ResidueField (Localization.AtPrime m)) H]
    {n k : ℕ} (f : Fin k → MvPolynomial (Fin n) Λ) (a : Fin n → completion m)
    (ha : ∀ j, MvPolynomial.aeval a (f j) = 0) :
    ∃ b : Fin n → H, ∀ j, MvPolynomial.aeval b (f j) = 0 := by
  have : HenselianLocalRing H :=
    IsHenselization.henselian (R := Localization.AtPrime m)
      (L := ResidueField (Localization.AtPrime m)) (Rh := H)
  have : IsLocalHom (algebraMap (Localization.AtPrime m) H) :=
    IsHenselization.isLocalHom (L := ResidueField (Localization.AtPrime m))
  have hH : m = (maximalIdeal H).comap (algebraMap Λ H) := by
    rw [IsScalarTower.algebraMap_eq Λ (Localization.AtPrime m) H, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime m) m).symm
  exact exists_solution_of_isGRing m B hS hR hG H hH f a ha

end TheExample

end Deformation.Artin.GRingCounterexample

end
