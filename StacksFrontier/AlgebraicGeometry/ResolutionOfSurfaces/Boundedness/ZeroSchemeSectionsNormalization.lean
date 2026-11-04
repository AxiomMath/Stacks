module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ZeroSchemeSectionsBound
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrum
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ZeroSchemeSections

/-!
# The sections of the divisor cut out by `c` inside the normalization of `A ⧸ cA`

Let `(A, 𝔪)` be a two-dimensional Noetherian normal local domain, `c ∈ 𝔪` nonzero with
`R = A ⧸ cA` reduced, and `f : X ⟶ Spec A` a modification with `X` normal. Let `Z ⊂ X` be cut
out by `c`. The `A`-linear map `H⁰(Z, 𝒪_Z) ⟶ Q(R)` to the total ring of fractions sends a
section `s` to `r / d`, where `d ∈ A` lies in no minimal prime `𝔭` of `cA` and `d s ≡ r` at the
point `y_𝔭` of `X` over each `𝔭`. It takes values in the integral closure `R̄` of `R` and induces
an injection of `H⁰(Z, 𝒪_Z) / A` into `R̄ / R`. Hence the length of the cokernel of
`A ⟶ H⁰(Z, 𝒪_Z)` is bounded independently of the modification.

## Main definitions

* `AlgebraicGeometry.ZeroScheme.psi`: the map `H⁰(Z, 𝒪_Z) ⟶ Q(A ⧸ cA)`, `s ↦ r / d`.

## Main results

* `AlgebraicGeometry.ZeroScheme.eq_base_of_psi_eq`: a section sent by `psi` into `A ⧸ cA` comes
  from `A`.
* `AlgebraicGeometry.ZeroScheme.isIntegral_psi`: the values of `psi` are integral over `A ⧸ cA`.
* `AlgebraicGeometry.length_quotient_baseToZeroSchemeSections_le_of_isReduced`: the cokernel of
  `A ⟶ H⁰(Z, 𝒪_Z)` has length at most that of `R̄ / R`.
* `AlgebraicGeometry.exists_uniform_bound_length_quotient_baseToZeroSchemeSections`: the length
  of the cokernel of `A ⟶ H⁰(Z, 𝒪_Z)` is bounded uniformly in the normal modification `X`.

## References

* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing Order
open Stacks.LocalCohomology (puncturedSpectrum)

universe u

namespace AlgebraicGeometry.ZeroScheme

section Algebra

variable {A : Type u} [CommRing A]

/-- In a ring whose quotient by `I` is reduced, an element of a minimal prime `𝔭` of `I` is
multiplied into `I` by an element outside `𝔭`. -/
theorem exists_mul_mem_of_mem_minimalPrimes_of_isReduced {I P : Ideal A}
    (hred : _root_.IsReduced (A ⧸ I)) (hP : P ∈ I.minimalPrimes) {x : A} (hx : x ∈ P) :
    ∃ s ∉ P, s * x ∈ I := by
  have : P.IsPrime := hP.1.1
  have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (Localization.AtPrime P) P I hP
  have hxmap : algebraMap A (Localization.AtPrime P) x ∈ (I.map (algebraMap A _)).radical := by
    rw [hrad]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨n, hn⟩ := hxmap
  rw [← map_pow, IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl] at hn
  obtain ⟨s, hs, hsx⟩ := hn
  refine ⟨s, hs, ?_⟩
  have hnil : IsNilpotent (Ideal.Quotient.mk I (s * x)) := by
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, mul_pow]
    have : s ^ (n + 1) * x ^ (n + 1) = (s ^ n * x) * (s * x ^ n) := by ring
    rw [this]
    exact I.mul_mem_left _ (by simpa [mul_comm] using hsx)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact hnil.eq_zero

/-- In a two-dimensional local ring the maximal ideal has height two. -/
private theorem height_maximalIdeal_eq_two [IsLocalRing A] (hdim : ringKrullDim A = 2) :
    (maximalIdeal A).height = 2 := by
  have hh := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [hdim] at hh
  exact WithBot.coe_injective (hh.trans rfl)

/-- In a two-dimensional Noetherian local ring, the maximal ideal is not a minimal prime of a
principal ideal. -/
private theorem maximalIdeal_notMem_minimalPrimes_span [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (c : A) : maximalIdeal A ∉ (Ideal.span {c}).minimalPrimes := by
  intro hm
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hm
  rw [height_maximalIdeal_eq_two hdim] at h1
  exact absurd h1 (by decide)

variable [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]

omit [IsNoetherianRing A] in
/-- In a two-dimensional local domain, a prime containing a nonzero `c` other than the maximal
ideal is a minimal prime of `cA`. -/
theorem mem_minimalPrimes_span_of_ne_maximalIdeal (hdim : ringKrullDim A = 2) {c : A}
    (hc : c ≠ 0) {Q : Ideal A} [hQ : Q.IsPrime] (hcQ : c ∈ Q) (hQm : Q ≠ maximalIdeal A) :
    Q ∈ (Ideal.span {c}).minimalPrimes := by
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem Q).mpr hcQ)
  have : P.IsPrime := hP.1.1
  rcases eq_or_lt_of_le hPQ with h | h
  · exact h ▸ hP
  exfalso
  have hP0 : P ≠ ⊥ := fun h0 =>
    hc (by simpa [h0] using hP.1.2 (Ideal.mem_span_singleton_self c))
  have h1 : 1 ≤ P.height :=
    Order.one_le_iff_ne_zero.mpr fun h0 => hP0 (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime h
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime
    (lt_of_le_of_ne (le_maximalIdeal hQ.ne_top) hQm)
  rw [height_maximalIdeal_eq_two hdim] at h3
  have h4 : P.height + 1 + 1 ≤ 2 := (add_le_add_left h2 1).trans h3
  have h5 : (1 : ℕ∞) + 1 + 1 ≤ 2 := (add_le_add_left (add_le_add_left h1 1) 1).trans h4
  exact absurd h5 (by decide)

omit [IsLocalRing A] [IsNoetherianRing A] [IsDomain A] in
/-- Among finitely many minimal primes of an ideal, each one is avoided by an element of all
the others. -/
theorem exists_notMem_forall_mem_of_minimalPrimes {I : Ideal A} (S : Finset (Ideal A))
    (hS : ∀ P ∈ S, P ∈ I.minimalPrimes) {P : Ideal A} (hP : P ∈ S) :
    ∃ e ∉ P, ∀ P' ∈ S, P' ≠ P → e ∈ P' := by
  classical
  have hPp : P.IsPrime := (hS P hP).1.1
  by_contra! H
  rcases (S.erase P).eq_empty_or_nonempty with he | hne
  · obtain ⟨P', hP', hne', h1⟩ := H 1 (fun h => hPp.ne_top ((Ideal.eq_top_iff_one _).mpr h))
    exact (Finset.notMem_empty P') (he ▸ Finset.mem_erase.mpr ⟨hne', hP'⟩) |>.elim
  have hle : (S.erase P).inf id ≤ P := fun e he => by
    by_contra heP
    obtain ⟨P', hP', hne', h1⟩ := H e heP
    exact h1 (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hne', hP'⟩) he)
  obtain ⟨P', hP', hle'⟩ := (hPp.inf_le' (s := S.erase P) (f := id)).mp hle
  obtain ⟨hne', hP'S⟩ := Finset.mem_erase.mp hP'
  exact hne' (le_antisymm hle' ((hS P hP).2 (hS P' hP'S).1 hle'))

end Algebra

section Stalks

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- An element of the base lies in the maximal ideal of `𝒪_{X, y}` exactly when it lies in the
prime of `A` under `y`. -/
theorem baseRingToStalk_mem_maximalIdeal_iff (y : X) (a : A) :
    baseRingToStalk f y a ∈ maximalIdeal (X.presheaf.stalk y) ↔ a ∈ (f y).asIdeal := by
  have : (f y).asIdeal.IsPrime := (f y).isPrime
  let : Algebra A ((Spec (.of A)).presheaf.stalk (f y)) :=
    StructureSheaf.stalkAlgebra A (f y)
  have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk (f y)) (f y).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (f y)
  show (f.stalkMap y).hom (StructureSheaf.toStalk A (f y) a) ∈ _ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (.of A)).presheaf.stalk (f y))
      (f y).asIdeal a, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact not_congr (isUnit_map_iff (f.stalkMap y).hom _)

/-- If `f` is an isomorphism on the stalk at `y`, every element of `𝒪_{X, y}` is a fraction of
elements of `A`. -/
theorem exists_mul_baseRingToStalk_eq (y : X) [IsIso (f.stalkMap y)]
    (g : X.presheaf.stalk y) :
    ∃ a b : A, b ∉ (f y).asIdeal ∧ g * baseRingToStalk f y b = baseRingToStalk f y a := by
  have : (f y).asIdeal.IsPrime := (f y).isPrime
  let : Algebra A ((Spec (.of A)).presheaf.stalk (f y)) :=
    StructureSheaf.stalkAlgebra A (f y)
  have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk (f y)) (f y).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (f y)
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hz⟩ := IsLocalization.surj (f y).asIdeal.primeCompl
    ((inv (f.stalkMap y)).hom g)
  refine ⟨a, b, hb, ?_⟩
  have h := congrArg (f.stalkMap y).hom hz
  rwa [map_mul, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply] at h

/-- A point over a minimal prime of `cA` in a two-dimensional local ring is not the closed
point. -/
private theorem ne_closedPoint_of_mem_minimalPrimes [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) {c : A} {y : X}
    (hy : (f y).asIdeal ∈ (Ideal.span {c}).minimalPrimes) : f y ≠ closedPoint A := fun h =>
  maximalIdeal_notMem_minimalPrimes_span hdim c
    (by rwa [show (f y).asIdeal = _ by rw [h]] at hy)

variable [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
  [IsIntegral X] (hf : IsModification f)

include hdim hf

omit [IsIntegral X] in
/-- The restriction of the modification over the punctured spectrum is an isomorphism. -/
lemma isIso_restrict_punctured : IsIso (f ∣_ (puncturedSpectrum (.of A))) :=
  isIso_morphismRestrict_of_isModification (.of A) hdim.le f hf _ (fun h => h rfl)

omit [IsIntegral X] in
/-- Every point of the punctured spectrum is the image of a point of `X`. -/
theorem exists_apply_eq (P : PrimeSpectrum A) (hP : P ≠ closedPoint A) : ∃ y : X, f y = P := by
  have := isIso_restrict_punctured f hdim hf
  obtain ⟨⟨y, hy⟩, h⟩ := (f ∣_ (puncturedSpectrum (.of A))).homeomorph.surjective
    (⟨P, hP⟩ : (puncturedSpectrum (.of A)))
  exact ⟨y, (morphismRestrict_base_coe f (puncturedSpectrum (.of A)) ⟨y, hy⟩).symm.trans
    (congrArg Subtype.val h)⟩

omit [IsIntegral X] in
/-- Points of `X` off the closed fibre are determined by their images. -/
theorem eq_of_apply_eq {y y' : X} (hy : f y ≠ closedPoint A) (h : f y = f y') : y = y' := by
  have := isIso_restrict_punctured f hdim hf
  have hinj := (f ∣_ (puncturedSpectrum (.of A))).homeomorph.injective
  have hy' : f y' ≠ closedPoint A := h ▸ hy
  have hyV : y ∈ f ⁻¹ᵁ (puncturedSpectrum (.of A)) := hy
  have hyV' : y' ∈ f ⁻¹ᵁ (puncturedSpectrum (.of A)) := hy'
  have := @hinj ⟨y, hyV⟩ ⟨y', hyV'⟩ (Subtype.ext
    ((morphismRestrict_base_coe f _ ⟨y, hyV⟩).trans
      (h.trans (morphismRestrict_base_coe f _ ⟨y', hyV'⟩).symm)))
  exact congrArg Subtype.val this

omit [IsIntegral X] in
/-- Off the closed fibre the modification is an isomorphism on stalks. -/
theorem isIso_stalkMap_of_ne_closedPoint {y : X} (hy : f y ≠ closedPoint A) :
    IsIso (f.stalkMap y) :=
  isIso_stalkMap_of_isIso_morphismRestrict f (isIso_restrict_punctured f hdim hf) (x := y) hy

omit [IsIntegral X] in
/-- At a point over a minimal prime of `cA`, with `A ⧸ cA` reduced, the maximal ideal of the local
ring is generated by `c`. -/
theorem exists_eq_mul_of_mem_maximalIdeal {c : A} (hred : _root_.IsReduced (A ⧸ Ideal.span {c}))
    {y : X} (hy : (f y).asIdeal ∈ (Ideal.span {c}).minimalPrimes)
    {g : X.presheaf.stalk y} (hg : g ∈ maximalIdeal (X.presheaf.stalk y)) :
    ∃ g', g = baseRingToStalk f y c * g' := by
  have := isIso_stalkMap_of_ne_closedPoint f hdim hf
    (ne_closedPoint_of_mem_minimalPrimes f hdim hy)
  obtain ⟨a, b, hb, hab⟩ := exists_mul_baseRingToStalk_eq f y g
  have ha : a ∈ (f y).asIdeal := by
    rw [← baseRingToStalk_mem_maximalIdeal_iff, ← hab]
    exact Ideal.mul_mem_right _ _ hg
  obtain ⟨s, hs, hsa⟩ := exists_mul_mem_of_mem_minimalPrimes_of_isReduced hred hy ha
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hsa
  have hsa' : s * a = k * c := hk.symm
  have hu : IsUnit (baseRingToStalk f y (s * b)) := by
    by_contra hnu
    have hmem : baseRingToStalk f y (s * b) ∈ maximalIdeal (X.presheaf.stalk y) := hnu
    rw [baseRingToStalk_mem_maximalIdeal_iff] at hmem
    exact (Ideal.IsPrime.mem_or_mem (f y).isPrime hmem).elim hs hb
  have key : g * baseRingToStalk f y (s * b) =
      baseRingToStalk f y c * baseRingToStalk f y k := by
    rw [map_mul, ← mul_assoc, mul_comm g, mul_assoc, hab, ← map_mul, ← map_mul, hsa', mul_comm]
  refine ⟨baseRingToStalk f y k * ↑hu.unit⁻¹, ?_⟩
  rw [← mul_assoc, ← key, mul_assoc, hu.mul_val_inv, mul_one]

end Stalks

section Sections

attribute [local instance] Scheme.commRingRingCatSheafObj

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (c : A)

/-- The global sections of `𝒪_Z` as an `A`-module. -/
abbrev Glob : Type u := globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f c)

/-- The germ at `y` of the chosen local lift of a global section of `𝒪_Z`. -/
def liftGerm (s : Sec f c ⊤) (y : X) : X.presheaf.stalk y :=
  X.presheaf.germ _ y (mem_liftOpen f c s y) (lift f c s y)

/-- The function `a` lifts the section `a` of `𝒪_Z`. -/
lemma proj_baseRes_eq (a : A) (W : X.Opens) :
    proj f c W (baseRes f a W) = resZ f c le_top (baseToZeroSchemeSections X f c a) :=
  proj_map f c le_top _

/-- If `t` lifts `s`, then `a t` lifts `a s`. -/
lemma proj_baseRes_mul_eq {W : X.Opens} {t : Γ(X, W)} {s : Glob f c}
    (ht : proj f c W t = resZ f c le_top s) (a : A) :
    proj f c W (baseRes f a W * t) = resZ f c le_top (a • s) := by
  have h1 : proj f c W (baseRes f a W * t) =
      (show X.ringCatSheaf.obj.obj (op W) from baseRes f a W) • proj f c W t :=
    ((toZeroSchemeStructureSheaf X f c).val.app (op W)).hom.map_smul _ t
  rw [h1, ht]
  exact (PresheafOfModules.map_smul (zeroSchemeStructureSheaf X f c).val
    (homOfLE (le_top : W ≤ ⊤)).op _ s).symm

/-- A section whose local lift at `y` is divisible by `c` there vanishes near `y`. -/
lemma exists_resZ_eq_zero (s : Sec f c ⊤) {y : X} (g : X.presheaf.stalk y)
    (hg : liftGerm f c s y = baseRingToStalk f y c * g) :
    ∃ W : X.Opens, y ∈ W ∧ resZ f c (le_top : W ≤ ⊤) s = 0 := by
  obtain ⟨W1, hyW1, v, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf g
  rw [← germ_baseRes f c W1 y hyW1, ← map_mul] at hg
  obtain ⟨W2, hyW2, iU, iV, he⟩ := TopCat.Presheaf.germ_eq X.presheaf y _ hyW1 _ _ hg
  refine ⟨W2, hyW2, ?_⟩
  have h3 := congrArg (proj f c W2) he
  rwa [show iU = homOfLE iU.le from rfl, proj_map, proj_lift, resZ_resZ, map_mul,
    show iV = homOfLE iV.le from rfl, baseRes, map_map, ← baseRes, proj_baseRes_mul] at h3

end Sections

section Residues

attribute [local instance] Scheme.commRingRingCatSheafObj

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]
  {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of A)) (c : A)

/-- A point of `X` over a minimal prime of `cA`. -/
abbrev OverMin (y : X) : Prop := (f y).asIdeal ∈ (Ideal.span {c}).minimalPrimes

variable {f c}
omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- At a point over a minimal prime of `cA`, `c` vanishes. -/
lemma baseRingToStalk_mem_of_overMin {y : X} (hy : OverMin f c y) :
    baseRingToStalk f y c ∈ maximalIdeal (X.presheaf.stalk y) :=
  (baseRingToStalk_mem_maximalIdeal_iff f y c).mpr (hy.1.2 (Ideal.mem_span_singleton_self c))

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- The kernel of `A ⟶ κ(y)` is the prime under `y`. -/
lemma residueAlgebraMap_eq_zero_iff (y : X) (a : A) :
    residueAlgebraMap f y a = 0 ↔ a ∈ (f y).asIdeal := by
  rw [residueAlgebraMap_eq_residue_baseRingToStalk, ← baseRingToStalk_mem_maximalIdeal_iff]
  exact IsLocalRing.residue_eq_zero_iff _

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- The residue at a point over a minimal prime of `cA` is additive. -/
lemma residue_add {y : X} (hy : OverMin f c y) (s s' : Sec f c ⊤) :
    residue f c (s + s') y = residue f c s y + residue f c s' y := by
  set W := liftOpen f c s y ⊓ liftOpen f c s' y
  have hyW : y ∈ W := ⟨mem_liftOpen f c s y, mem_liftOpen f c s' y⟩
  let t : Γ(X, W) := X.presheaf.map (homOfLE inf_le_left).op (lift f c s y) +
    X.presheaf.map (homOfLE inf_le_right).op (lift f c s' y)
  have ht : proj f c W t = resZ f c le_top (s + s') := by
    have h1 : proj f c W t = proj f c W (X.presheaf.map (homOfLE inf_le_left).op (lift f c s y)) +
        proj f c W (X.presheaf.map (homOfLE inf_le_right).op (lift f c s' y)) :=
      map_add ((toZeroSchemeStructureSheaf X f c).val.app (op W)).hom _ _
    rw [h1, proj_map, proj_map, proj_lift, proj_lift, resZ_resZ, resZ_resZ]
    exact (map_add ((zeroSchemeStructureSheaf X f c).val.map (homOfLE le_top).op).hom s s').symm
  rw [residue_eq (baseRingToStalk_mem_of_overMin hy) hyW t ht, map_add, map_add,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  rfl

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- The residue at a point over a minimal prime of `cA` is `A`-linear. -/
lemma residue_smul {y : X} (hy : OverMin f c y) (a : A) (s : Glob f c) :
    residue f c (a • s) y = residueAlgebraMap f y a * residue f c s y := by
  rw [residue_eq (baseRingToStalk_mem_of_overMin hy) (mem_liftOpen f c s y) _
    (proj_baseRes_mul_eq f c (proj_lift f c s y) a), map_mul, germ_baseRes, map_mul]
  rfl

omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- The residue of the section `a` is the image of `a`. -/
lemma residue_base {y : X} (hy : OverMin f c y) (a : A) :
    residue f c (baseToZeroSchemeSections X f c a) y = residueAlgebraMap f y a := by
  rw [residue_eq (baseRingToStalk_mem_of_overMin hy) (Set.mem_univ y) _
    (proj_baseRes_eq f c a ⊤), germ_baseRes]
  rfl

variable (hdim : ringKrullDim A = 2) (hf : IsModification f)
include hdim hf

/-- **Injectivity.** A section of `𝒪_Z` with zero residue at every point over a minimal prime of
`cA` is zero. -/
theorem eq_zero_of_forall_residue_eq_zero [IsNormal X] (hc : c ≠ 0)
    (hred : _root_.IsReduced (A ⧸ Ideal.span {c})) (s : Glob f c)
    (hs : ∀ y : X, OverMin f c y → residue f c s y = 0) : s = 0 := by
  refine eq_zero_of_forall_coheight_eq_one f c hdim hf hc s fun y hy1 hfy => ?_
  have := (f y).isPrime
  by_cases hcy : c ∈ (f y).asIdeal
  · have hmin : OverMin f c y := by
      have : (f y).asIdeal ≠ maximalIdeal A := fun h => hfy (PrimeSpectrum.ext h)
      exact mem_minimalPrimes_span_of_ne_maximalIdeal hdim hc hcy this
    have h0 := hs y hmin
    have hm : liftGerm f c s y ∈ maximalIdeal (X.presheaf.stalk y) :=
      (IsLocalRing.residue_eq_zero_iff _).mp h0
    obtain ⟨g, hg⟩ := exists_eq_mul_of_mem_maximalIdeal f hdim hf hred hmin hm
    exact exists_resZ_eq_zero f c s g hg
  · have hu : IsUnit (baseRingToStalk f y c) := by
      by_contra hnu
      exact hcy ((baseRingToStalk_mem_maximalIdeal_iff f y c).mp hnu)
    refine exists_resZ_eq_zero f c s (↑hu.unit⁻¹ * liftGerm f c s y) ?_
    rw [← mul_assoc, hu.mul_val_inv, one_mul]

omit hdim in
omit [IsLocalRing A] [IsNoetherianRing A] [IsIntegral X] in
/-- **Integrality.** The residue of a section of `𝒪_Z` at a point over a minimal prime of `cA`
is integral over `A`. -/
theorem isIntegralElem_residue (s : Glob f c) {y : X} (hy : OverMin f c y) :
    (residueAlgebraMap f y).hom.IsIntegralElem (residue f c s y) := by
  have : IsProper f := hf.isProper
  refine isIntegralElem_residue_of_forall_specializes f y _ fun x hyx => ?_
  refine ⟨liftGerm f c s x, ?_⟩
  show X.residue y (X.presheaf.stalkSpecializes hyx
    (X.presheaf.germ _ x (mem_liftOpen f c s x) (lift f c s x))) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (residue_eq (baseRingToStalk_mem_of_overMin hy) _ _ (proj_lift f c s x)).symm

omit hdim hf in
omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- The residue at a point over a minimal prime of `cA` commutes with subtraction. -/
lemma residue_sub {y : X} (hy : OverMin f c y) (s s' : Sec f c ⊤) :
    residue f c (s - s') y = residue f c s y - residue f c s' y := by
  rw [eq_sub_iff_add_eq, ← residue_add hy, sub_add_cancel]

end Residues

section Psi

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]
  {X : Scheme.{u}} [IsIntegral X] {f : X ⟶ Spec (.of A)} {c : A}

/-- A pair `(d, r)` presenting a section of `𝒪_Z` as the fraction `r / d` of `A ⧸ cA`: `d` lies in
no minimal prime of `cA`, and `d s` and `r` have the same residue at every point over one. -/
def IsGood (s : Glob f c) (d r : A) : Prop :=
  (∀ P ∈ (Ideal.span {c}).minimalPrimes, d ∉ P) ∧
    ∀ y : X, OverMin f c y → residueAlgebraMap f y d * residue f c s y = residueAlgebraMap f y r

omit [IsLocalRing A] [IsNormalDomain A] in
omit [IsNoetherianRing A] in
/-- An element in every minimal prime of `cA` lies in `cA` when `A ⧸ cA` is reduced. -/
theorem mem_span_of_forall_mem_minimalPrimes (hred : _root_.IsReduced (A ⧸ Ideal.span {c}))
    {x : A} (hx : ∀ P ∈ (Ideal.span {c}).minimalPrimes, x ∈ P) : x ∈ Ideal.span {c} := by
  have hrad : x ∈ (Ideal.span {c}).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Ideal.mem_sInf.mpr hx
  obtain ⟨n, hn⟩ := hrad
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact IsNilpotent.eq_zero ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩

omit [IsLocalRing A] [IsNormalDomain A] in
omit [IsNoetherianRing A] in
/-- An element in no minimal prime of `cA` is a nonzerodivisor of `A ⧸ cA` when the latter is
reduced. -/
theorem mk_mem_nonZeroDivisors (hred : _root_.IsReduced (A ⧸ Ideal.span {c})) {d : A}
    (hd : ∀ P ∈ (Ideal.span {c}).minimalPrimes, d ∉ P) :
    Ideal.Quotient.mk (Ideal.span {c}) d ∈ nonZeroDivisors (A ⧸ Ideal.span {c}) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine mem_span_of_forall_mem_minimalPrimes hred fun P hP => ?_
  have := hP.1.1
  exact ((this.mem_or_mem (hP.1.2 hx)).resolve_right (hd P hP))

/-- The fraction `r / d` in the total ring of fractions of `A ⧸ cA`. -/
def frac (hred : _root_.IsReduced (A ⧸ Ideal.span {c})) (d r : A)
    (hd : ∀ P ∈ (Ideal.span {c}).minimalPrimes, d ∉ P) : FractionRing (A ⧸ Ideal.span {c}) :=
  IsLocalization.mk' _ (Ideal.Quotient.mk _ r) ⟨_, mk_mem_nonZeroDivisors hred hd⟩

variable (hdim : ringKrullDim A = 2) (hf : IsModification f)
include hdim hf

omit hf in
omit [IsNormalDomain A] [IsIntegral X] in
/-- A point over a minimal prime of `cA` is not over the closed point. -/
lemma ne_closedPoint_of_overMin {y : X} (hy : OverMin f c y) : f y ≠ closedPoint A :=
  ne_closedPoint_of_mem_minimalPrimes f hdim hy

omit [IsIntegral X] in
/-- Over every minimal prime of `cA` there is a point of `X`. -/
theorem exists_overMin {P : Ideal A} (hP : P ∈ (Ideal.span {c}).minimalPrimes) :
    ∃ y : X, OverMin f c y ∧ (f y).asIdeal = P := by
  have := hP.1.1
  have hPm : P ≠ maximalIdeal A := fun h => maximalIdeal_notMem_minimalPrimes_span hdim c (h ▸ hP)
  obtain ⟨y, hy⟩ := exists_apply_eq f hdim hf ⟨P, this⟩
    (fun h => hPm (congrArg PrimeSpectrum.asIdeal h))
  refine ⟨y, ?_, by rw [hy]⟩
  show (f y).asIdeal ∈ _
  rwa [hy]

omit [IsIntegral X] in
/-- Two presentations of the same section give fractions that agree modulo `cA`. -/
theorem sub_mem_span_of_isGood {s : Glob f c} {d r d' r' : A} (hg : IsGood s d r)
    (hg' : IsGood s d' r') (hred : _root_.IsReduced (A ⧸ Ideal.span {c})) :
    d' * r - d * r' ∈ Ideal.span {c} := by
  refine mem_span_of_forall_mem_minimalPrimes hred fun P hP => ?_
  obtain ⟨y, hy, rfl⟩ := exists_overMin hdim hf hP
  rw [← residueAlgebraMap_eq_zero_iff, map_sub, map_mul, map_mul, ← hg.2 y hy, ← hg'.2 y hy]
  ring

omit [IsIntegral X] in
/-- The fraction attached to a presentation does not depend on the presentation. -/
theorem frac_eq_of_isGood {s : Glob f c} {d r d' r' : A} (hg : IsGood s d r)
    (hg' : IsGood s d' r') (hred : _root_.IsReduced (A ⧸ Ideal.span {c})) :
    frac hred d r hg.1 = frac hred d' r' hg'.1 := by
  rw [frac, frac, IsLocalization.mk'_eq_iff_eq]
  congr 1
  have h := sub_mem_span_of_isGood hdim hf hg hg' hred
  rwa [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, sub_eq_zero] at h

/-- **Every section of `𝒪_Z` is a fraction.** -/
theorem exists_isGood (s : Glob f c) : ∃ d r : A, IsGood s d r := by
  classical
  have hfin := (Ideal.span {c}).finite_minimalPrimes_of_isNoetherianRing
  set S := hfin.toFinset
  have hS : ∀ P ∈ S, P ∈ (Ideal.span {c}).minimalPrimes := fun P hP => hfin.mem_toFinset.mp hP
  have hpt : ∀ P ∈ S, ∃ y : X, OverMin f c y ∧ (f y).asIdeal = P ∧ ∃ a b : A,
      b ∉ P ∧ residueAlgebraMap f y b * residue f c s y = residueAlgebraMap f y a := by
    intro P hP
    obtain ⟨y, hy, hyP⟩ := exists_overMin hdim hf (hS P hP)
    have hne : f y ≠ closedPoint A := ne_closedPoint_of_overMin hdim hy
    have := isIso_stalkMap_of_ne_closedPoint f hdim hf hne
    obtain ⟨a, b, hb, hab⟩ := exists_mul_baseRingToStalk_eq f y (liftGerm f c s y)
    refine ⟨y, hy, hyP, a, b, hyP ▸ hb, ?_⟩
    rw [residueAlgebraMap_eq_residue_baseRingToStalk, residueAlgebraMap_eq_residue_baseRingToStalk,
      ← hab, map_mul, mul_comm]
    rfl
  choose! yP hyP hyPP aP bP hbP habP using hpt
  have he : ∀ P ∈ S, ∃ e ∉ P, ∀ P' ∈ S, P' ≠ P → e ∈ P' := fun P hP =>
    exists_notMem_forall_mem_of_minimalPrimes S hS hP
  choose! e heP heP' using he
  refine ⟨∑ P ∈ S, e P * bP P, ∑ P ∈ S, e P * aP P, ?_, ?_⟩
  · intro Q hQ hdQ
    have hQS : Q ∈ S := hfin.mem_toFinset.mpr hQ
    have := hQ.1.1
    rw [← Finset.add_sum_erase S _ hQS] at hdQ
    have hrest : ∑ P ∈ S.erase Q, e P * bP P ∈ Q := Ideal.sum_mem _ fun P hP =>
      Ideal.mul_mem_right _ _ (heP' P (Finset.mem_of_mem_erase hP) Q hQS
        (Finset.ne_of_mem_erase hP).symm)
    have h1 : e Q * bP Q ∈ Q := by simpa using Q.sub_mem hdQ hrest
    rcases this.mem_or_mem h1 with h | h
    · exact heP Q hQS h
    · exact hbP Q hQS h
  · intro y hy
    have hQS : (f y).asIdeal ∈ S := hfin.mem_toFinset.mpr hy
    have hyy : yP (f y).asIdeal = y :=
      eq_of_apply_eq f hdim hf (ne_closedPoint_of_overMin hdim (hyP _ hQS))
        (PrimeSpectrum.ext (hyPP _ hQS))
    rw [← sub_eq_zero, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun P hP => ?_
    rw [map_mul, map_mul, mul_assoc, ← mul_sub]
    by_cases hPQ : P = (f y).asIdeal
    · have h := habP _ hQS
      rw [hyy] at h
      rw [hPQ, h, sub_self, mul_zero]
    · have hmem : e P ∈ (f y).asIdeal := heP' P hP _ hQS fun h => hPQ h.symm
      rw [(residueAlgebraMap_eq_zero_iff y (e P)).mpr hmem, zero_mul]

omit hdim hf in
omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- Presentations add. -/
theorem isGood_add {s s' : Glob f c} {d r d' r' : A} (hg : IsGood s d r) (hg' : IsGood s' d' r') :
    IsGood (s + s') (d * d') (d' * r + d * r') := by
  refine ⟨fun P hP h => ?_, fun y hy => ?_⟩
  · have := hP.1.1
    rcases this.mem_or_mem h with h | h
    · exact hg.1 P hP h
    · exact hg'.1 P hP h
  · rw [show residue f c (s + s') y = residue f c s y + residue f c s' y from
      residue_add hy s s', map_mul, map_add, map_mul, map_mul, ← hg.2 y hy, ← hg'.2 y hy]
    ring

omit hdim hf in
omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- Presentations are `A`-linear. -/
theorem isGood_smul {s : Glob f c} {d r : A} (hg : IsGood s d r) (a : A) :
    IsGood (a • s) d (a * r) :=
  ⟨hg.1, fun y hy => by rw [residue_smul hy, map_mul, ← hg.2 y hy]; ring⟩

omit hdim hf in
omit [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] [IsIntegral X] in
/-- The section `a` is presented by `(1, a)`. -/
theorem isGood_base (a : A) : IsGood (baseToZeroSchemeSections X f c a) 1 a :=
  ⟨fun P hP h => hP.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h),
    fun y hy => by rw [map_one, one_mul, residue_base hy]⟩

variable (hred : _root_.IsReduced (A ⧸ Ideal.span {c}))

/-- **The map `H⁰(Z, 𝒪_Z) ⟶ Q(A ⧸ cA)`**, `s ↦ r / d` for any presentation `(d, r)` of `s`. -/
def psi : Glob f c →ₗ[A] FractionRing (A ⧸ Ideal.span {c}) where
  toFun s := frac hred (exists_isGood hdim hf s).choose (exists_isGood hdim hf s).choose_spec.choose
    (exists_isGood hdim hf s).choose_spec.choose_spec.1
  map_add' s s' := by
    have hg := (exists_isGood hdim hf s).choose_spec.choose_spec
    have hg' := (exists_isGood hdim hf s').choose_spec.choose_spec
    rw [frac_eq_of_isGood hdim hf (exists_isGood hdim hf (s + s')).choose_spec.choose_spec
      (isGood_add hg hg') hred, frac, frac, frac, ← IsLocalization.mk'_add,
      IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [Submonoid.coe_mul, map_mul, map_add]
    ring
  map_smul' a s := by
    have hg := (exists_isGood hdim hf s).choose_spec.choose_spec
    rw [frac_eq_of_isGood hdim hf (exists_isGood hdim hf (a • s)).choose_spec.choose_spec
      (isGood_smul hg a) hred, frac, frac, RingHom.id_apply, Algebra.smul_def,
      IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span {c}), IsLocalization.mul_mk'_eq_mk'_of_mul,
      Ideal.Quotient.algebraMap_eq, map_mul]

/-- `psi s` is `r / d` for any presentation `(d, r)` of `s`. -/
theorem psi_eq {s : Glob f c} {d r : A} (hg : IsGood s d r) :
    psi hdim hf hred s = frac hred d r hg.1 :=
  frac_eq_of_isGood hdim hf (exists_isGood hdim hf s).choose_spec.choose_spec hg hred

/-- `psi` sends the section `a` to the image of `a`. -/
theorem psi_base (a : A) :
    psi hdim hf hred (baseToZeroSchemeSections X f c a) =
      algebraMap (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c}))
        (Ideal.Quotient.mk (Ideal.span {c}) a) := by
  rw [psi_eq hdim hf hred (isGood_base a), frac, IsLocalization.mk'_eq_iff_eq_mul]
  simp

/-- **Injectivity modulo `A`.** A section sent by `psi` into `A ⧸ cA` comes from `A`. -/
theorem eq_base_of_psi_eq [IsNormal X] (hc : c ≠ 0) {s : Glob f c} {a : A}
    (h : psi hdim hf hred s =
      algebraMap (A ⧸ Ideal.span {c}) (FractionRing (A ⧸ Ideal.span {c}))
        (Ideal.Quotient.mk (Ideal.span {c}) a)) :
    s = baseToZeroSchemeSections X f c a := by
  obtain ⟨d, r, hg⟩ := exists_isGood hdim hf s
  rw [psi_eq hdim hf hred hg, frac, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul] at h
  have h' := IsFractionRing.injective (A ⧸ Ideal.span {c}) _ h
  rw [← map_mul, Ideal.Quotient.eq] at h'
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_residue_eq_zero hdim hf hc hred _ fun y hy => ?_
  have hmem : r - a * d ∈ (f y).asIdeal := hy.1.2 h'
  rw [← residueAlgebraMap_eq_zero_iff, map_sub, map_mul, ← hg.2 y hy, sub_eq_zero] at hmem
  have hd0 : residueAlgebraMap f y d ≠ 0 := fun h0 =>
    hg.1 _ hy ((residueAlgebraMap_eq_zero_iff y d).mp h0)
  rw [show residue f c (s - baseToZeroSchemeSections X f c a) y =
      residue f c s y - residue f c (baseToZeroSchemeSections X f c a) y from residue_sub hy _ _,
    residue_base hy, sub_eq_zero]
  refine mul_left_cancel₀ hd0 ?_
  rw [hmem, mul_comm]

/-- **The values of `psi` are integral over `A ⧸ cA`.** -/
theorem isIntegral_psi (s : Glob f c) :
    _root_.IsIntegral (A ⧸ Ideal.span {c}) (psi hdim hf hred s) := by
  classical
  set Q := FractionRing (A ⧸ Ideal.span {c})
  obtain ⟨d, r, hg⟩ := exists_isGood hdim hf s
  rw [psi_eq hdim hf hred hg]
  have hfin := (Ideal.span {c}).finite_minimalPrimes_of_isNoetherianRing
  set S := hfin.toFinset
  have hint : ∀ P ∈ S, ∃ p : Polynomial A, p.Monic ∧ ∀ y : X, OverMin f c y →
      (f y).asIdeal = P → p.eval₂ (residueAlgebraMap f y).hom (residue f c s y) = 0 := by
    intro P hP
    obtain ⟨y, hy, hyP⟩ := exists_overMin hdim hf (hfin.mem_toFinset.mp hP)
    obtain ⟨p, hpm, hp⟩ := isIntegralElem_residue hf s hy
    refine ⟨p, hpm, fun y' hy' hy'P => ?_⟩
    have : y' = y := eq_of_apply_eq f hdim hf (ne_closedPoint_of_overMin hdim hy')
      (PrimeSpectrum.ext (hy'P.trans hyP.symm))
    rwa [this]
  choose! pP hpPm hpP using hint
  let p := ∏ P ∈ S, pP P
  have hpm : p.Monic := Polynomial.monic_prod_of_monic _ _ hpPm
  have hp : ∀ y : X, OverMin f c y →
      p.eval₂ (residueAlgebraMap f y).hom (residue f c s y) = 0 := by
    intro y hy
    rw [Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.mpr hy) (hpP _ (hfin.mem_toFinset.mpr hy) y hy rfl)
  set z := (Polynomial.scaleRoots p d).eval r
  have hz : z ∈ Ideal.span {c} := by
    refine mem_span_of_forall_mem_minimalPrimes hred fun P hP => ?_
    obtain ⟨y, hy, rfl⟩ := exists_overMin hdim hf hP
    rw [← residueAlgebraMap_eq_zero_iff]
    show (residueAlgebraMap f y).hom z = 0
    rw [← Polynomial.eval₂_at_apply, ← hg.2 y hy, Polynomial.scaleRoots_eval₂_mul, hp y hy,
      mul_zero]
  let φ : A →+* Q := algebraMap A Q
  have hφ : φ = (algebraMap (A ⧸ Ideal.span {c}) Q).comp (Ideal.Quotient.mk _) :=
    IsScalarTower.algebraMap_eq _ _ _
  have hφz : φ z = 0 := by
    rw [hφ, RingHom.comp_apply, (Ideal.Quotient.eq_zero_iff_mem).mpr hz, map_zero]
  set q := frac hred d r hg.1
  have hq : φ d * q = φ r := by
    rw [hφ, RingHom.comp_apply, RingHom.comp_apply]
    exact IsLocalization.mk'_spec' Q (Ideal.Quotient.mk (Ideal.span {c}) r)
      (⟨_, mk_mem_nonZeroDivisors hred hg.1⟩ : nonZeroDivisors (A ⧸ Ideal.span {c}))
  have hu : IsUnit (φ d) := by
    rw [hφ, RingHom.comp_apply]
    exact IsLocalization.map_units Q (⟨_, mk_mem_nonZeroDivisors hred hg.1⟩ :
      nonZeroDivisors (A ⧸ Ideal.span {c}))
  have h0 : p.eval₂ φ q = 0 := by
    have h1 := Polynomial.scaleRoots_eval₂_mul (p := p) φ q d
    rw [hq, Polynomial.eval₂_at_apply, hφz] at h1
    exact (hu.pow _).mul_right_eq_zero.mp h1.symm
  exact IsIntegral.tower_top (A := A ⧸ Ideal.span {c}) (⟨p, hpm, h0⟩ : _root_.IsIntegral A q)

end Psi

end AlgebraicGeometry.ZeroScheme

namespace AlgebraicGeometry

open ZeroScheme

/-- **The bound for an element with reduced principal quotient.** Let `A` be a two-dimensional
Noetherian normal local domain, `c ∈ A` nonzero with `A ⧸ cA` reduced, and `f : X ⟶ Spec A` a
modification with `X` normal. The cokernel of `A ⟶ H⁰(Z, 𝒪_Z)`, for `Z` cut out by `c`, has
length at most that of the cokernel of `A ⧸ cA` in its normalization. -/
theorem length_quotient_baseToZeroSchemeSections_le_of_isReduced {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) {c : A}
    (hc : c ≠ 0) (hred : _root_.IsReduced (A ⧸ Ideal.span {c})) (X : Scheme.{u}) [IsNormal X]
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) :
    Module.length A (globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f c) ⧸
        LinearMap.range (baseToZeroSchemeSections X f c)) ≤
      Module.length (A ⧸ Ideal.span {c}) (normalizationCokernel (A ⧸ Ideal.span {c})) := by
  have : IsIntegral X := hf.source_isIntegral
  set R := A ⧸ Ideal.span {c}
  set K := FractionRing R
  let Φ₀ : Glob f c →ₗ[A] integralClosure R K :=
    { toFun := fun s => ⟨psi hdim hf hred s, isIntegral_psi hdim hf hred s⟩
      map_add' := fun s s' => Subtype.ext (map_add (psi hdim hf hred) s s')
      map_smul' := fun a s => Subtype.ext (map_smul (psi hdim hf hred) a s) }
  let Φ : Glob f c →ₗ[A] normalizationCokernel R :=
    ((LinearMap.range (Algebra.linearMap R (integralClosure R K))).mkQ.restrictScalars A).comp Φ₀
  have h1 : LinearMap.range (baseToZeroSchemeSections X f c) ≤ LinearMap.ker Φ := by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨Ideal.Quotient.mk _ a, Subtype.ext (psi_base hdim hf hred a).symm⟩
  have h2 : LinearMap.ker Φ ≤ LinearMap.range (baseToZeroSchemeSections X f c) := by
    intro s hs
    rw [LinearMap.mem_ker] at hs
    change Submodule.Quotient.mk _ = 0 at hs
    rw [Submodule.Quotient.mk_eq_zero] at hs
    obtain ⟨x, hx⟩ := hs
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, (eq_base_of_psi_eq hdim hf hred hc (congrArg Subtype.val hx).symm).symm⟩
  let Ψ := (LinearMap.range (baseToZeroSchemeSections X f c)).liftQ Φ h1
  refine (Module.length_le_of_injective Ψ
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ h1 h2))).trans (le_of_eq ?_)
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

/-- Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two and let `a ∈ A` be nonzero.
There is an integer `N` such that for every modification `f : X ⟶ Spec A` with `X` normal the
`A`-module

  `M_{X,a} = Coker(A ⟶ H⁰(Z, 𝒪_Z))`,

for `Z ⊂ X` the closed subscheme cut out by `a`, has length at most `N`. -/
@[stacks 0AXJ]
theorem exists_uniform_bound_length_quotient_baseToZeroSchemeSections {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNormalDomain A] [IsNagataRing A] (hdim : ringKrullDim A = 2) {a : A}
    (ha : a ≠ 0) :
    ∃ N : ℕ, ∀ (X : Scheme.{u}) [IsNormal X] (f : X ⟶ Spec (.of A)), IsModification f →
      Module.length A (globalSectionsAsBaseModule X f (zeroSchemeStructureSheaf X f a) ⧸
        LinearMap.range (baseToZeroSchemeSections X f a)) ≤ N :=
  exists_bound_length_quotient_baseToZeroSchemeSections hdim ha
    fun _ hc _ hred _ hN X _ f hf =>
      (length_quotient_baseToZeroSchemeSections_le_of_isReduced hdim hc hred X f hf).trans hN

end AlgebraicGeometry
