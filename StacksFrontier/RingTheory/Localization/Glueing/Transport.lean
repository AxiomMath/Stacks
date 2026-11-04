module

public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory

/-!
# Transporting a glueing datum along a comparison of generic parts

A system of module glueing data for a ring map `R → S` and a finite family `f = (f₁, …, f_t)` in
`R` can be moved along a map of its generic part provided that map becomes bijective after
inverting each `f i`.  The local pieces and the overlap isomorphisms are unchanged — in
particular the cocycle condition is inherited verbatim — and the comparison of the generic part
with the local pieces is composed with the inverse of the localized map.

## Main results

* `FormalGlueing.exists_pow_smul_mem_range` — a map which is surjective after inverting `a`
  has every element of its target in the image up to a power of `a`.
* `FormalGlueing.transportDatum` — the transported system of glueing data.
* `FormalGlueing.transportAlpha_mk` — the value of its comparison on the image of the
  original generic part.

## References

* [Stacks Project, Tag 05EL](https://stacks.math.columbia.edu/tag/05EL)
* [Stacks Project, Tag 0EAE](https://stacks.math.columbia.edu/tag/0EAE)
-/

@[expose] public noncomputable section

namespace FormalGlueing

universe u v w

open CategoryTheory Cech TensorProduct

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-! ### Elements become visible after inverting an element -/

/-- If a map of `S`-modules becomes surjective after inverting `a`, then every element of its
target is carried into its image by a power of `a`. -/
theorem exists_pow_smul_mem_range {M N : Type*} [AddCommGroup M] [Module S M]
    [AddCommGroup N] [Module S N] (a : S) (g : M →ₗ[S] N)
    (hg : Function.Surjective (LocalizedModule.map (Submonoid.powers a) g)) (t : N) :
    ∃ (k : ℕ) (y : M), a ^ k • t = g y := by
  obtain ⟨z, hz⟩ := hg (LocalizedModule.mk t 1)
  induction z using LocalizedModule.induction_on with
  | _ y s =>
    rw [LocalizedModule.map_mk] at hz
    obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.1 hz
    obtain ⟨k₁, hk₁⟩ := c.2
    obtain ⟨k₂, hk₂⟩ := s.2
    have hk₁' : a ^ k₁ = (c : S) := hk₁
    have hk₂' : a ^ k₂ = (s : S) := hk₂
    refine ⟨k₁ + k₂, (c : S) • y, ?_⟩
    rw [map_smul, pow_add, hk₁', hk₂', mul_smul]
    simpa only [Submonoid.smul_def, one_smul] using hc.symm

/-- Compatibility of the scalar action with multiplication, in both factors. -/
theorem smul_mul_smul_of_smul_mul {R₀ P : Type*} [CommRing R₀] [CommRing P] [Module R₀ P]
    (hP : ∀ (c : R₀) (p p' : P), (c • p) * p' = c • (p * p')) (c d : R₀) (p p' : P) :
    (c • p) * (d • p') = (c * d) • (p * p') := by
  rw [hP, mul_comm p, hP, smul_smul, mul_comm p']

/-- A linear map out of a localization which is multiplicative on the localizing generating set
is multiplicative everywhere. -/
theorem map_mul_of_isLocalizedModule {R₀ : Type*} [CommRing R₀] {M P Q : Type*}
    [CommRing M] [CommRing P] [CommRing Q] [Module R₀ M] [Module R₀ P] [Module R₀ Q]
    (TT : Submonoid R₀) (ι : M →ₗ[R₀] P) [IsLocalizedModule TT ι]
    (hP : ∀ (c : R₀) (p p' : P), (c • p) * p' = c • (p * p'))
    (hQ : ∀ (c : R₀) (q q' : Q), (c • q) * q' = c • (q * q'))
    (hTQ : ∀ c ∈ TT, Function.Injective fun q : Q ↦ c • q)
    (e : P →ₗ[R₀] Q) (hι : ∀ a b : M, ι (a * b) = ι a * ι b)
    (hmul : ∀ a b : M, e (ι (a * b)) = e (ι a) * e (ι b)) (p p' : P) :
    e (p * p') = e p * e p' := by
  obtain ⟨⟨a, c⟩, hc⟩ := IsLocalizedModule.surj TT ι p
  obtain ⟨⟨b, d⟩, hd⟩ := IsLocalizedModule.surj TT ι p'
  have hc : (c : R₀) • p = ι a := hc
  have hd : (d : R₀) • p' = ι b := hd
  have h1 : ((c : R₀) * d) • (p * p') = ι (a * b) := by
    rw [← smul_mul_smul_of_smul_mul hP, hc, hd, ← hι]
  have h2 : ((c : R₀) * d) • (e p * e p') = e (ι a) * e (ι b) := by
    rw [← smul_mul_smul_of_smul_mul hQ, ← map_smul, ← map_smul, hc, hd]
  refine hTQ ((c : R₀) * d) (mul_mem c.2 d.2) ?_
  show ((c : R₀) * d) • e (p * p') = ((c : R₀) * d) • (e p * e p')
  rw [← map_smul, h1, hmul, h2]

/-! ### The scalar action on a left tensor factor -/

variable {S}

/-- Mapping the right factor of a tensor product commutes with the action of `S` on the left
factor. -/
theorem map_id_smul {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (g : X →ₗ[R] Y) (a : S) (z : TensorProduct R S X) :
    TensorProduct.map LinearMap.id g (a • z) = a • TensorProduct.map LinearMap.id g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s xx => simp [TensorProduct.smul_tmul']
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]

/-- The action of an element coming from `R` on a tensor product is the map induced by its
action on the right factor. -/
theorem algebraMap_smul_eq_map {X : Type*} [AddCommGroup X] [Module R X] (b : R)
    (z : TensorProduct R S X) :
    (algebraMap R S b) • z =
      TensorProduct.map LinearMap.id (b • (LinearMap.id : X →ₗ[R] X)) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s xx =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul]
    simp only [LinearMap.id_coe, id_eq, LinearMap.smul_apply]
    rw [smul_eq_mul, ← Algebra.smul_def, TensorProduct.smul_tmul]
  | add p q hp hq => simp only [smul_add, map_add, hp, hq]

variable (S)

/-- An element of the localizing submonoid acts injectively on a tensor product whose right
factor is a localization at that submonoid. -/
theorem injective_algebraMap_smul (TT : Submonoid R) {X Y : Type*} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (g : X →ₗ[R] Y) [IsLocalizedModule TT g]
    (c : R) (hc : c ∈ TT) :
    Function.Injective fun z : TensorProduct R S Y ↦ (algebraMap R S c) • z := by
  have hunit : IsUnit (algebraMap R (Module.End R Y) c) :=
    IsLocalizedModule.map_units g ⟨c, hc⟩
  rw [Module.End.isUnit_iff] at hunit
  have he : (algebraMap R (Module.End R Y) c) = c • (LinearMap.id : Y →ₗ[R] Y) := by
    ext z; simp [Algebra.algebraMap_eq_smul_one]
  rw [he] at hunit
  have heq : (fun z : TensorProduct R S Y ↦ (algebraMap R S c) • z) =
      ⇑(TensorProduct.congr (LinearEquiv.refl R S) (LinearEquiv.ofBijective _ hunit)) := by
    funext y
    rw [algebraMap_smul_eq_map]
    rfl
  rw [heq]
  exact LinearEquiv.injective _

/-- A power of `f i` acts injectively on a tensor product whose right factor has `f i`
inverted. -/
theorem injective_algebraMap_pow_smul {X : Type*} [AddCommGroup X] [Module R X]
    (i : Fin r) (k : ℕ) :
    Function.Injective
      fun z : TensorProduct R S (cechMod f X {i}) ↦ (algebraMap R S (f i)) ^ k • z := by
  have hmem : f i ^ k ∈ cechSub f ({i} : Finset (Fin r)) := by
    simpa only [cechSub, Finset.prod_singleton] using
      (Submonoid.powers (f i)).pow_mem (Submonoid.mem_powers (f i)) k
  simpa only [map_pow] using injective_algebraMap_smul S (cechSub f ({i} : Finset (Fin r)))
    (LocalizedModule.mkLinearMap (cechSub f ({i} : Finset (Fin r))) X) (f i ^ k) hmem

/-! ### The transported datum -/

variable (Y : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
  (G : ModuleCat.{max u v w} S) (ψ : Y.generic ⟶ G)

/-- The localization of `ψ` at `f i`, as a map over `S`. -/
abbrev transportMap (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) Y.generic →ₗ[S]
      LocalizedModule.Away (algebraMap R S (f i)) G :=
  (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) ψ.hom).restrictScalars S

/-- The comparison of the generic part with the local pieces, transported along `ψ`. -/
def transportAlpha
    (hψ : ∀ i, Function.Bijective (transportMap S f Y G ψ i))
    (i : Fin r) :
    LocalizedModule.Away (algebraMap R S (f i)) G ≃ₗ[S]
      TensorProduct R S (restrictFromAway f i (Y.localPiece i)) :=
  LinearEquiv.trans (LinearEquiv.ofBijective _ (hψ i)).symm (Y.alpha i)

variable (hψ : ∀ i, Function.Bijective (transportMap S f Y G ψ i))

/-- The transported comparison, unfolded. -/
theorem transportAlpha_apply (i : Fin r)
    (z : LocalizedModule.Away (algebraMap R S (f i)) G) :
    transportAlpha S f Y G ψ hψ i z =
      Y.alpha i ((LinearEquiv.ofBijective _ (hψ i)).symm z) := rfl

/-- The transported comparison, on the image of the original generic part. -/
theorem transportAlpha_mk (i : Fin r) (y : Y.generic) :
    transportAlpha S f Y G ψ hψ i
        (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) G (ψ.hom y)) =
      Y.alpha i (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R S (f i))) Y.generic y) := by
  rw [transportAlpha_apply]
  congr 1
  exact (LinearEquiv.ofBijective _ (hψ i)).symm_apply_eq.2 (LocalizedModule.map_mk _ _ _ _).symm

/-- Transport of a system of glueing data along a map of generic parts which becomes bijective
after inverting each `f i`.  Local pieces, overlap isomorphisms and the cocycle condition are
unchanged. -/
def transportDatum : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) where
  generic := G
  localPiece := Y.localPiece
  alpha := transportAlpha S f Y G ψ hψ
  alphaIJ := Y.alphaIJ
  alpha_compatibility i j t := by
    obtain ⟨k, y, hy⟩ :=
      exists_pow_smul_mem_range S (algebraMap R S (f i)) ψ.hom (hψ i).2 t
    have hmk : ∀ i' : Fin r,
        transportAlpha S f Y G ψ hψ i'
            (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i'))) G
              ((algebraMap R S (f i)) ^ k • t)) =
          Y.alpha i' (LocalizedModule.mkLinearMap
            (Submonoid.powers (algebraMap R S (f i'))) Y.generic y) := fun i' => by
      rw [hy]
      exact transportAlpha_mk S f Y G ψ hψ i' y
    refine injective_algebraMap_pow_smul S f i k ?_
    change (algebraMap R S (f i)) ^ k • _ = (algebraMap R S (f i)) ^ k • _
    rw [← map_id_smul, ← map_id_smul, ← map_smul, ← map_smul, hmk i,
      ← map_id_smul, ← map_smul, ← map_smul, hmk j]
    exact Y.alpha_compatibility i j y
  cocycle := Y.cocycle

/-- The generic part of the transported datum. -/
theorem transportDatum_generic : (transportDatum S f Y G ψ hψ).generic = G := rfl

/-- The local pieces of the transported datum. -/
theorem transportDatum_localPiece :
    (transportDatum S f Y G ψ hψ).localPiece = Y.localPiece := rfl

/-- The comparison of the transported datum. -/
theorem transportDatum_alpha (i : Fin r) :
    (transportDatum S f Y G ψ hψ).alpha i = transportAlpha S f Y G ψ hψ i := rfl

/-- The overlap isomorphisms of the transported datum. -/
theorem transportDatum_alphaIJ : (transportDatum S f Y G ψ hψ).alphaIJ = Y.alphaIJ := rfl

end FormalGlueing

end
