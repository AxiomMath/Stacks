module

public import StacksFrontier.RingTheory.Rig.Algebraization.AlgebraizationTowerComparison
public import StacksFrontier.RingTheory.Rig.Algebraization.GRing
public import StacksFrontier.RingTheory.Rig.Algebraization.HenselianApproximation
public import StacksFrontier.RingTheory.Rig.Algebraization.NormalBundleData
public import StacksFrontier.RingTheory.Rig.Algebraization.NormalBundleSections
public import StacksFrontier.RingTheory.Rig.Algebraization.QuasiIdempotentApproximation
public import StacksFrontier.RingTheory.Rig.Algebraization.QuasiIdempotentKernel
public import StacksFrontier.RingTheory.Rig.Algebraization.RigEtaleAlgebraization

/-!
# Algebraization of rig-smooth algebras over a principal ideal (Elkik)

Let `A` be a Noetherian ring and `a ∈ A`. If `B` is an object of the category of Stacks 0AL4 over
`(A, (a))` which is rig-smooth over `(A, (a))`, then `B` is the `(a)`-adic completion of a finite
type `A`-algebra. This is [Elkik, III Théorème 7], the third case of Stacks Remark 0GAX.

## The proof

1. A presentation `B = A⟨x⟩ / J` and the data of `Rig.NormalBundle.Data` (`nonempty_data`): a
   quasi-idempotent `E`, `E² = aᶜ E`, which off `V(a)` projects onto the normal directions.
2. The completed normal bundle `Ĉ = B⟨T⟩/((aᶜ − E) T)` is rig-étale over `(A[X], (a))` through the
   tubular map `X ↦ x + aᶜ⁺¹ T` (`Rig.NormalBundle.Data.isRigEtale`). So Stacks 0AKA gives
   `Ĉ ≅ D^∧` with `D` of finite type.
3. `B` is the zero section `Ĉ / (T)` of `Ĉ`. The fibre coordinates `T` and the matrix `E` on `Ĉ`
   are approximated by elements of the henselization `Dʰ`: the matrix by an exact quasi-idempotent
   (`exists_quasiIdempotent_approx`, by henselian approximation on the normal bundle of the
   quasi-idempotent variety), and the coordinates by an exact solution `t` of `(aᶜ − E₀) t = 0`
   (`Rig.exists_mulVec_eq_zero_of_mulVec_mem`). Then
   `Rig.NormalBundle.Data.nonempty_algEquiv_quotient` gives `B ≅ Ĉ / (t) = (Dʰ / (t))^∧`.
4. Stacks 0GAS turns the completion of a quotient of a henselization into the completion of a
   finite type `A`-algebra.

## Main results

* `Rig.exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_principal`: a rig-smooth object
  over `(A, (a))` is the `(a)`-adic completion of a finite type `A`-algebra.

## References

* [R. Elkik, *Solutions d'équations à coefficients dans un anneau hensélien*, III Théorème 7]
* [Stacks Project, Tag 0GAX](https://stacks.math.columbia.edu/tag/0GAX)
-/

@[expose] public noncomputable section

universe u v

namespace Rig

section Quotient

variable {A : Type*} [CommRing A] {X Y : Type*} [CommRing X] [CommRing Y] [Algebra A X]
  [Algebra A Y]

/-- The map `X ⧸ J → Y ⧸ f(J)` induced by an `A`-algebra map `f`. -/
def quotientMapOfAlgHom (f : X →ₐ[A] Y) (J : Ideal X) : X ⧸ J →ₐ[A] Y ⧸ J.map (f : X →+* Y) :=
  Ideal.quotientMapₐ _ f Ideal.le_comap_map

/-- If `f` is bijective modulo `𝔞`, every element of `f(J)` is congruent modulo `𝔞` to the image of
an element of `J`. -/
private theorem IsBijectiveMod.exists_mem_sub_mem_map {𝔞 : Ideal A} {f : X →ₐ[A] Y}
    (hf : IsBijectiveMod 𝔞 f) {J : Ideal X} {z : Y} (hz : z ∈ J.map (f : X →+* Y)) :
    ∃ x ∈ J, z - f x ∈ 𝔞.map (algebraMap A Y) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    exact ⟨j, hj, by simp⟩
  | zero => exact ⟨0, J.zero_mem, by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨x₁, hx₁, h₁⟩ := hz
    obtain ⟨x₂, hx₂, h₂⟩ := hz'
    refine ⟨x₁ + x₂, J.add_mem hx₁ hx₂, ?_⟩
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ h₁ h₂
  | smul c z _ hz =>
    obtain ⟨x₁, hx₁, h₁⟩ := hz
    obtain ⟨xc, hxc⟩ := hf.1 c
    refine ⟨xc * x₁, J.mul_mem_left _ hx₁, ?_⟩
    have : c • z - f (xc * x₁) = c * (z - f x₁) + (c - f xc) * f x₁ := by
      rw [smul_eq_mul, map_mul]
      ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_right _ _ hxc)

/-- If `f` is bijective modulo `𝔞`, so is the induced map `X ⧸ J → Y ⧸ f(J)`. -/
theorem IsBijectiveMod.quotient {𝔞 : Ideal A} {f : X →ₐ[A] Y} (hf : IsBijectiveMod 𝔞 f)
    (J : Ideal X) : IsBijectiveMod 𝔞 (quotientMapOfAlgHom f J) := by
  have hmapX :
      𝔞.map (algebraMap A (X ⧸ J)) = (𝔞.map (algebraMap A X)).map (Ideal.Quotient.mk J) := by
    rw [Ideal.map_map]
    rfl
  have hmapY : 𝔞.map (algebraMap A (Y ⧸ J.map (f : X →+* Y))) =
      (𝔞.map (algebraMap A Y)).map (Ideal.Quotient.mk (J.map (f : X →+* Y))) := by
    rw [Ideal.map_map]
    rfl
  refine ⟨fun y ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hf.1 y
    refine ⟨Ideal.Quotient.mk J x, ?_⟩
    rw [hmapY]
    have : Ideal.Quotient.mk (J.map (f : X →+* Y)) y - quotientMapOfAlgHom f J
        (Ideal.Quotient.mk J x) = Ideal.Quotient.mk (J.map (f : X →+* Y)) (y - f x) := by
      rw [map_sub]
      rfl
    rw [this]
    exact Ideal.mem_map_of_mem _ hx
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hmapY] at hx
    change Ideal.Quotient.mk (J.map (f : X →+* Y)) (f x) ∈ _ at hx
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Ideal.Quotient.eq] at hyx
    obtain ⟨x', hx', h'⟩ := hf.exists_mem_sub_mem_map hyx
    have hfx : f (x + x') ∈ 𝔞.map (algebraMap A Y) := by
      have : f (x + x') = y - (y - f x - f x') := by
        rw [map_add]
        ring
      rw [this]
      exact Ideal.sub_mem _ hy h'
    have hx0 := hf.2 _ hfx
    rw [hmapX]
    have : Ideal.Quotient.mk J x = Ideal.Quotient.mk J (x + x') := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hx', add_zero]
    rw [this]
    exact Ideal.mem_map_of_mem _ hx0

/-- **Two out of three for bijectivity modulo `𝔞`.** If `f` and `g ∘ f` are bijective modulo `𝔞`,
so is `g`. -/
theorem IsBijectiveMod.of_comp_left {Z : Type*} [CommRing Z] [Algebra A Z] {𝔞 : Ideal A}
    {f : X →ₐ[A] Y} {g : Y →ₐ[A] Z} (hf : IsBijectiveMod 𝔞 f) (hgf : IsBijectiveMod 𝔞 (g.comp f)) :
    IsBijectiveMod 𝔞 g := by
  refine ⟨fun z ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hgf.1 z
    exact ⟨f x, hx⟩
  · obtain ⟨x, hx⟩ := hf.1 y
    have hgx : g (f x) ∈ 𝔞.map (algebraMap A Z) := by
      have h := Ideal.sub_mem _ hy (map_mem_map_algebraMap g hx)
      rwa [map_sub, sub_sub_cancel] at h
    have hx0 := hgf.2 x hgx
    have h := Ideal.add_mem _ hx (map_mem_map_algebraMap f hx0)
    rwa [sub_add_cancel] at h

end Quotient

section MatrixLemmas

variable {R : Type*} [CommRing R] {n : ℕ}

/-- If `E² = u E` then `(u − E)² = u (u − E)`. -/
theorem smul_one_sub_mul_self {u : R} {E : Matrix (Fin n) (Fin n) R} (hE : E * E = u • E) :
    (u • 1 - E) * (u • 1 - E) = u • (u • 1 - E) := by
  simp only [sub_mul, mul_sub, hE, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub]
  abel

/-- A matrix-vector product is small if it is close to one that vanishes. -/
theorem mulVec_mem_of_sub_mem (Q : Ideal R) (M M' : Matrix (Fin n) (Fin n) R) (v v' : Fin n → R)
    (hM : ∀ i j, M i j - M' i j ∈ Q) (hv : ∀ j, v j - v' j ∈ Q) (h0 : M'.mulVec v' = 0)
    (i : Fin n) : M.mulVec v i ∈ Q := by
  have : M.mulVec v i = ((M - M').mulVec v) i + (M'.mulVec (v - v')) i + M'.mulVec v' i := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  rw [this, h0, Pi.zero_apply, add_zero, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
  refine Q.add_mem (Q.sum_mem fun j _ ↦ ?_) (Q.sum_mem fun j _ ↦ ?_)
  · rw [Matrix.sub_apply]
    exact Q.mul_mem_right _ (hM i j)
  · rw [Pi.sub_apply]
    exact Q.mul_mem_left _ (hv j)

/-- If `(u − E) t = 0`, then its image under a ring map `ψ` satisfies `ψ(u) ψ(t) = ψ(E) ψ(t)`. -/
private theorem smul_map_eq_mulVec_map_of_mulVec_eq_zero {S : Type*} [CommRing S] (ψ : R →+* S)
    {u : R} {E : Matrix (Fin n) (Fin n) R} {t : Fin n → R} (ht : (u • 1 - E).mulVec t = 0) :
    ψ u • (fun i ↦ ψ (t i)) = (E.map ψ).mulVec fun i ↦ ψ (t i) := by
  have h0 : ((u • 1 - E).map ψ).mulVec (fun i ↦ ψ (t i)) = 0 := by
    funext i
    refine (RingHom.map_mulVec ψ _ t i).symm.trans ?_
    rw [ht]
    simp
  have h2 : (u • 1 - E).map ψ = ψ u • 1 - E.map ψ := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
      map_mul, Matrix.one_apply]
    split_ifs <;> simp
  rwa [h2, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0

end MatrixLemmas

/-- The image of `(a)ᵏ` in an `A`-algebra `X` is `(a)ᵏ` in `X`. -/
theorem map_span_singleton_pow {A X : Type*} [CommRing A] [CommRing X] [Algebra A X] (a : A)
    (k : ℕ) : ((Ideal.span {a}) ^ k).map (algebraMap A X) = Ideal.span {algebraMap A X a} ^ k := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]

section Henselization

variable {A : Type u} [CommRing A] (I : Ideal A) (D : Type u) [CommRing D] [Algebra A D]
  [IsNoetherianRing D]

/-- The henselization of `(D, ID)` as an `A`-algebra. -/
abbrev henselizationAlgebra : Algebra A (henselization D (I.map (algebraMap A D))) :=
  ((algebraMap D (henselization D (I.map (algebraMap A D)))).comp (algebraMap A D)).toAlgebra

attribute [local instance] henselizationAlgebra

/-- The scalar tower `A → D → Dʰ` for the henselization of `(D, ID)`. -/
instance : IsScalarTower A D (henselization D (I.map (algebraMap A D))) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The canonical map `Dʰ → D^∧`, as an `A`-algebra map. -/
def henselizationToCompletionA :
    henselization D (I.map (algebraMap A D)) →ₐ[A]
      AdicCompletion (I.map (algebraMap A D)) D :=
  (henselizationToAdicCompletion D (I.map (algebraMap A D))).1.restrictScalars A

/-- **The henselization and the completion agree modulo every power of `I`.** -/
theorem isBijectiveMod_henselizationToCompletionA (m : ℕ) :
    IsBijectiveMod (I ^ m) (henselizationToCompletionA I D) := by
  set 𝔡 := I.map (algebraMap A D)
  have hι : IsBijectiveMod (I ^ m)
      (IsScalarTower.toAlgHom A D (henselization D 𝔡)) := by
    have hb := (flat_and_bijective_quotientMap_pow_of_ind_etale D 𝔡 (henselization D 𝔡)
      (ind_henselization D 𝔡) (bijective_quotientMap_henselization D 𝔡)).2 m
    have hmapD : (I ^ m).map (algebraMap A D) = 𝔡 ^ m := by rw [Ideal.map_pow]
    have hmapH : (I ^ m).map (algebraMap A (henselization D 𝔡)) =
        (𝔡 ^ m).map (algebraMap D (henselization D 𝔡)) := by
      rw [← hmapD, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    refine ⟨fun y ↦ ?_, fun x hx ↦ ?_⟩
    · obtain ⟨x, hx⟩ := hb.2 (Ideal.Quotient.mk _ y)
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨x, ?_⟩
      rw [hmapH, ← Ideal.Quotient.eq]
      exact hx.symm
    · rw [hmapH] at hx
      rw [hmapD]
      have h0 : Ideal.quotientMap ((𝔡 ^ m).map (algebraMap D (henselization D 𝔡)))
          (algebraMap D (henselization D 𝔡)) Ideal.le_comap_map (Ideal.Quotient.mk _ x) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hx
      rw [← map_zero (Ideal.quotientMap ((𝔡 ^ m).map (algebraMap D (henselization D 𝔡)))
        (algebraMap D (henselization D 𝔡)) Ideal.le_comap_map)] at h0
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hb.1 h0)
  have hψ : IsBijectiveMod (I ^ m)
      ((henselizationToCompletionA I D).comp (IsScalarTower.toAlgHom A D (henselization D 𝔡))) := by
    have heq : (henselizationToCompletionA I D).comp
        (IsScalarTower.toAlgHom A D (henselization D 𝔡)) =
        toAdicCompletionAlgHom (A := A) 𝔡 :=
      AlgHom.ext fun x ↦ RingHom.congr_fun (henselizationToAdicCompletion D 𝔡).2 x
    rw [heq]
    exact isBijectiveMod_toAdicCompletionAlgHom (A := A) (C := D) I
      (Ideal.fg_of_isNoetherianRing _) m
  exact IsBijectiveMod.of_comp_left hι hψ

end Henselization

attribute [local instance] henselizationAlgebra

/-- The scalar `D.sc j` is the image of `aʲ`. -/
theorem NormalBundle.Data.sc_eq_algebraMap {A : Type u} [CommRing A] [IsNoetherianRing A] {a : A}
    {B : AdicFiniteTypeAlgebra.{u, v} A (Ideal.span {a})}
    {Pres : CompletedPolynomialPresentation (Ideal.span {a}) B} (D : NormalBundle.Data B Pres)
    (j : ℕ) : D.sc j = algebraMap A D.obj.carrier (a ^ j) := by
  rw [NormalBundle.Data.sc, NormalBundle.Data.π_apply]
  rfl

/-- The image of the matrix `E` under a ring map `φ` satisfies `E² = φ(aᶜ) E`. -/
theorem NormalBundle.Data.map_Eb_mul_map_Eb {A : Type u} [CommRing A] [IsNoetherianRing A]
    {a : A} {B : AdicFiniteTypeAlgebra.{u, v} A (Ideal.span {a})}
    {Pres : CompletedPolynomialPresentation (Ideal.span {a}) B} (D : NormalBundle.Data B Pres)
    {R : Type*} [CommRing R] (φ : D.obj.carrier →+* R) :
    (Matrix.of fun i j ↦ φ (D.Eb i j)) * (Matrix.of fun i j ↦ φ (D.Eb i j)) =
      φ (D.sc D.c) • Matrix.of fun i j ↦ φ (D.Eb i j) := by
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, ← map_mul,
    ← D.Eb_mul_Eb, map_sum]
  exact Finset.sum_congr rfl fun m _ ↦ (map_mul φ _ _).symm

open NormalBundle in
/-- **Elkik's theorem, [Elkik, III Théorème 7].** Let `A` be a Noetherian ring and `a ∈ A`. Let
`B` be an object of the category of Stacks 0AL4 over `(A, (a))` which is rig-smooth over
`(A, (a))`. Then there is a finite type `A`-algebra `C` and an isomorphism `B ≅ C^∧` of
`A`-algebras with the `(a)`-adic completion of `C`. -/
public theorem exists_finiteType_adicCompletion_algEquiv_of_isRigSmooth_principal
    {A : Type u} [CommRing A] [IsNoetherianRing A] {a : A}
    (B : AdicFiniteTypeAlgebra.{u, v} A (Ideal.span {a})) (hB : IsRigSmooth B) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion ((Ideal.span {a}).map (algebraMap A C)) C) := by
  obtain ⟨Pres⟩ := nonempty_completedPolynomialPresentation
    (Ideal.fg_of_isNoetherianRing (Ideal.span {a})) B
  obtain ⟨Dt⟩ := nonempty_data B Pres hB
  -- the normal bundle is the completion of a finite type `A[X]`-algebra `D` (Stacks 0AKA)
  obtain ⟨D, _, _, hDft, ⟨eC₀⟩⟩ :=
    exists_finiteType_algEquiv_adicCompletion_of_isRigEtale Dt.obj Dt.isRigEtale
  let : Algebra A D :=
    ((algebraMap (Base (A := A) Pres.variableCount) D).comp MvPolynomial.C).toAlgebra
  have : IsScalarTower A (Base (A := A) Pres.variableCount) D :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsNoetherianRing D :=
    Algebra.FiniteType.isNoetherianRing (Base (A := A) Pres.variableCount) D
  have : Algebra.FiniteType A D := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType A (Base (A := A) Pres.variableCount)) hDft
  have h𝔡 : (baseIdeal a Pres.variableCount).map
      (algebraMap (Base (A := A) Pres.variableCount) D) =
      (Ideal.span {a}).map (algebraMap A D) := by
    rw [Ideal.map_map]
    rfl
  let eC : Dt.obj.carrier ≃ₐ[A] AdicCompletion ((Ideal.span {a}).map (algebraMap A D)) D :=
    (eC₀.restrictScalars A).trans (AdicCompletion.congrAlgEquiv AlgEquiv.refl
      (by rw [h𝔡, show ((AlgEquiv.refl : D ≃ₐ[A] D) : D →+* D) = RingHom.id D from rfl,
        Ideal.map_id]))
  let K := (Ideal.span {a}).map (algebraMap A D)
  obtain ⟨n₁, hn₁⟩ := Dt.nonempty_algEquiv_quotient
  obtain ⟨n₀, c', hQI⟩ := exists_quasiIdempotent_approx a Pres.variableCount Dt.c D
  have : IsNoetherianRing (henselization D K) := isNoetherianRing_henselization D K
  obtain ⟨k₀, hk₀⟩ := exists_mulVec_eq_zero_of_mulVec_mem
    (algebraMap A (henselization D K) a) Dt.c
  set n := n₀ + c' + k₀ + n₁ + Dt.c + 1 with hn
  let Ê : Matrix (Fin Pres.variableCount) (Fin Pres.variableCount) (AdicCompletion K D) :=
    Matrix.of fun i j ↦ (eC : Dt.obj.carrier →+* AdicCompletion K D) (Dt.Eb i j)
  have hÊ : Ê * Ê = algebraMap A (AdicCompletion K D) (a ^ Dt.c) • Ê := by
    have h := Dt.map_Eb_mul_map_Eb (eC : Dt.obj.carrier →+* AdicCompletion K D)
    rwa [show (eC : Dt.obj.carrier →+* AdicCompletion K D) (Dt.sc Dt.c) =
        algebraMap A (AdicCompletion K D) (a ^ Dt.c) by
      rw [Dt.sc_eq_algebraMap]
      exact eC.commutes (a ^ Dt.c)] at h
  obtain ⟨E₀, hE₀q, hE₀c⟩ := hQI n (by omega) Ê hÊ
  let h : henselization D K →ₐ[A] AdicCompletion K D := henselizationToCompletionA _ D
  have hbij : ∀ m, IsBijectiveMod ((Ideal.span {a}) ^ m) h := fun m ↦
    isBijectiveMod_henselizationToCompletionA _ D m
  have hKmap : ∀ m, ((Ideal.span {a}) ^ m).map (algebraMap A (AdicCompletion K D)) =
      (K.map (algebraMap D (AdicCompletion K D))) ^ m := fun m ↦ by
    rw [Ideal.map_pow, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have htilde : ∀ i, ∃ y : henselization D K,
      eC (Dt.Tb i) - h y ∈ ((Ideal.span {a}) ^ n).map (algebraMap A (AdicCompletion K D)) :=
    fun i ↦ (hbij n).1 (eC (Dt.Tb i))
  choose t' ht' using htilde
  have hrelÊ : (algebraMap A (AdicCompletion K D) (a ^ Dt.c) • 1 - Ê).mulVec
      (fun i ↦ eC (Dt.Tb i)) = 0 := by
    have h1 := congrArg (fun v ↦ (fun i ↦ (eC : Dt.obj.carrier →+* AdicCompletion K D) (v i)))
      Dt.smul_Tb_eq_mulVec
    simp only [Pi.smul_apply, smul_eq_mul, map_mul] at h1
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
    funext i
    have h2 := congrFun h1 i
    rw [Pi.smul_apply, smul_eq_mul]
    refine (eC.commutes (a ^ Dt.c) ▸ h2).trans ?_
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Ê, Matrix.of_apply]
    rfl
  let P : Matrix (Fin Pres.variableCount) (Fin Pres.variableCount) (henselization D K) :=
    algebraMap A (henselization D K) (a ^ Dt.c) • 1 - E₀
  have hP : P * P = algebraMap A (henselization D K) a ^ Dt.c • P := by
    rw [← map_pow]
    exact smul_one_sub_mul_self hE₀q
  have hmem : ∀ i, P.mulVec t' i ∈ Ideal.span {algebraMap A (henselization D K) a} ^ (n - c') := by
    intro i
    have hQ : h (P.mulVec t' i) ∈
        ((Ideal.span {a}) ^ (n - c')).map (algebraMap A (AdicCompletion K D)) := by
      have hmv : h (P.mulVec t' i) = (P.map h).mulVec (fun j ↦ h (t' j)) i :=
        RingHom.map_mulVec (h : henselization D K →+* AdicCompletion K D) P t' i
      rw [hmv]
      refine mulVec_mem_of_sub_mem _ _ _ _ _ (fun i j ↦ ?_) (fun j ↦ ?_) hrelÊ i
      · have : (P.map h) i j - (algebraMap A (AdicCompletion K D) (a ^ Dt.c) • 1 - Ê) i j =
            -((henselizationToAdicCompletion D K).1 (E₀ i j) - Ê i j) := by
          simp only [P, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub,
            smul_eq_mul, map_mul, AlgHom.commutes]
          have h1 : h ((1 : Matrix (Fin Pres.variableCount) (Fin Pres.variableCount)
              (henselization D K)) i j) = (1 : Matrix (Fin Pres.variableCount)
                (Fin Pres.variableCount) (AdicCompletion K D)) i j := by
            rw [Matrix.one_apply, Matrix.one_apply]
            split_ifs <;> simp
          rw [h1]
          show _ - h (E₀ i j) - _ = -(h (E₀ i j) - _)
          ring
        rw [this, neg_mem_iff, hKmap]
        exact hE₀c i j
      · rw [← neg_sub, neg_mem_iff]
        exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (ht' j)
    have hH := (hbij (n - c')).2 _ hQ
    rwa [map_span_singleton_pow] at hH
  obtain ⟨t, ht0, htt'⟩ := hk₀ (n - c') (by omega) P hP t' hmem
  let ψC : henselization D K →ₐ[A] Dt.obj.carrier := (eC.symm : _ →ₐ[A] Dt.obj.carrier).comp h
  have hψC : ∀ x, ψC x = eC.symm (h x) := fun _ ↦ rfl
  have hcong : ∀ k, n₁ ≤ k → ∀ (x : henselization D K) (y : Dt.obj.carrier),
      h x - eC y ∈ ((Ideal.span {a}) ^ k).map (algebraMap A (AdicCompletion K D)) →
      ψC x - y ∈ Ideal.span {algebraMap A Dt.obj.carrier a} ^ n₁ := fun k hk x y hxy ↦ by
    refine Ideal.pow_le_pow_right hk ?_
    have : ψC x - y = eC.symm (h x - eC y) := by simp [hψC]
    rw [this, ← map_span_singleton_pow]
    exact map_mem_map_algebraMap (eC.symm : _ →ₐ[A] Dt.obj.carrier) hxy
  have hcongT : ∀ i, ψC (t i) - Dt.Tb i ∈ Ideal.span {algebraMap A Dt.obj.carrier a} ^ n₁ := by
    intro i
    refine hcong (n - c' - Dt.c) (by omega) _ _ ?_
    have : h (t i) - eC (Dt.Tb i) = h (t i - t' i) - (eC (Dt.Tb i) - h (t' i)) := by
      rw [map_sub]
      ring
    rw [this]
    refine Ideal.sub_mem _ ?_ ?_
    · have h1 := htt' i
      rw [← map_span_singleton_pow] at h1
      exact map_mem_map_algebraMap h h1
    · exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (ht' i)
  have hcongE : ∀ i j, ψC (E₀ i j) - Dt.Eb i j ∈
      Ideal.span {algebraMap A Dt.obj.carrier a} ^ n₁ := by
    intro i j
    refine hcong (n - c') (by omega) _ _ ?_
    rw [hKmap]
    exact hE₀c i j
  have hrelC : algebraMap A Dt.obj.carrier (a ^ Dt.c) • (fun i ↦ ψC (t i)) =
      (E₀.map ψC).mulVec (fun i ↦ ψC (t i)) := by
    simpa using smul_map_eq_mulVec_map_of_mulVec_eq_zero
      (ψC : henselization D K →+* Dt.obj.carrier) (u := algebraMap A (henselization D K) (a ^ Dt.c))
      (E := E₀) ht0
  obtain ⟨eB⟩ := hn₁ _ _ hcongT hcongE hrelC
  let J : Ideal (henselization D K) := Ideal.span (Set.range t)
  have hJ : J.map (h : henselization D K →+* AdicCompletion K D) =
      (Ideal.span (Set.range fun i ↦ ψC (t i))).map
        (eC : Dt.obj.carrier →+* AdicCompletion K D) := by
    rw [Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp_apply, hψC]
    exact (AlgEquiv.apply_symm_apply eC (h (t i))).symm
  let e2 := Ideal.quotientEquivAlg (Ideal.span (Set.range fun i ↦ ψC (t i)))
    (J.map (h : henselization D K →+* AdicCompletion K D)) eC hJ
  obtain ⟨e3⟩ := nonempty_algEquiv_adicCompletion (Ideal.span {a}) (quotientMapOfAlgHom h J)
    (quotient_isAdicFiniteType (adicCompletionObj (Ideal.span {a}) (B := D))
      (J.map (h : henselization D K →+* AdicCompletion K D))).1
    fun m ↦ (hbij m).quotient J
  obtain ⟨C', _, _, hC'ft, ⟨e4⟩⟩ :=
    exists_finiteType_adicCompletion_algEquiv_henselization_quotient A D (Ideal.span {a}) J
  let eTot : B.carrier ≃ₐ[A] AdicCompletion ((Ideal.span {a}).map (algebraMap A C')) C' :=
    Pres.quotientEquiv.symm.trans (eB.trans (e2.trans (e3.trans e4.symm)))
  let E : C' ≃ₐ[A] ULift.{max u v} C' := ULift.algEquiv.symm
  exact ⟨ULift.{max u v} C', inferInstance, inferInstance, Algebra.FiniteType.equiv hC'ft E,
    ⟨eTot.trans (adicCompletionCongr (Ideal.span {a}) E)⟩⟩

end Rig
