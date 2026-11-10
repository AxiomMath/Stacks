module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Cardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.ConcreteExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.FrameDescentEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.Glue
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.SquareZeroKernel

/-!
# Infinitesimal lifts through a formally étale chart glue along a faithfully flat cover

This file assembles the chart gluing. Let `A' → A` be a surjection of commutative rings with
square-zero kernel, let `X` be a functor on a class `P` of `A'`-algebras containing every algebra
of cardinality at most `κ`, and let `Φ` be a formally étale chart `R` of `X` with `Ω[R⁄A']`
projective. Let `B'` be a faithfully flat `A'`-algebra with reduction `B = A ⊗[A'] B'`, let `x`
be a point of `X` over `A`, let `ū : R → B` be a frame of `x|_B` and `u' : R → B'` a lift of `ū`.
If `X` satisfies the sheaf condition for `A' → B'` and is separated for `A → B`, then `x` lifts to
a point of `X` over `A'`.

## Main definitions

* `Stacks.ChartGlue.Assembly.cover`: the concrete Čech cover, as a
  `Stacks.ChartGlue.CechCover`.
* `Stacks.ChartGlue.Assembly.kerLin`: the `A`-linear map of reduced square-zero kernels induced
  by a commuting square of algebra maps.

## Main results

* `Stacks.ChartGlue.Assembly.exists_lift`: under the sheaf and separation hypotheses, the point
  `x` over `A` is the image of a point over `A'`.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct Cardinal

universe v u

namespace Stacks.ChartGlue

namespace Assembly

variable {A' : Type u} [CommRing A'] {P : ObjectProperty (CommAlgCat.{u} A')}
  {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
  (hP : ∀ (T : Type u) [CommRing T] [Algebra A' T], #T ≤ κ → P (CommAlgCat.of A' T))

/-- An algebra of cardinality at most `κ`, as an object of `P`. -/
abbrev ob (T : Type u) [CommRing T] [Algebra A' T] (hT : #T ≤ κ) : P.FullSubcategory :=
  ⟨CommAlgCat.of A' T, hP T hT⟩

/-- An algebra map between objects of `P`, as a morphism. -/
abbrev hm {T T' : Type u} [CommRing T] [Algebra A' T] [CommRing T'] [Algebra A' T']
    {hT : #T ≤ κ} {hT' : #T' ≤ κ} (f : T →ₐ[A'] T') : ob hP T hT ⟶ ob hP T' hT' :=
  ObjectProperty.homMk (CommAlgCat.ofHom f)

/-- The algebra map underlying `hm f` is `f`. -/
lemma ah_hm {T T' : Type u} [CommRing T] [Algebra A' T] [CommRing T'] [Algebra A' T']
    {hT : #T ≤ κ} {hT' : #T' ≤ κ} (f : T →ₐ[A'] T') :
    ah (hm hP (hT := hT) (hT' := hT') f) = f := rfl

/-- The composite `hm f ≫ hm g` is `hm (g.comp f)`. -/
lemma hm_comp {T T' T'' : Type u} [CommRing T] [Algebra A' T] [CommRing T'] [Algebra A' T']
    [CommRing T''] [Algebra A' T''] {hT : #T ≤ κ} {hT' : #T' ≤ κ} {hT'' : #T'' ≤ κ}
    (f : T →ₐ[A'] T') (g : T' →ₐ[A'] T'') :
    hm hP (hT := hT) (hT' := hT') f ≫ hm hP (hT' := hT'') g =
      hm hP (hT := hT) (hT' := hT'') (g.comp f) := rfl

/-- Equal algebra maps give equal morphisms `hm f = hm g`. -/
lemma hm_congr {T T' : Type u} [CommRing T] [Algebra A' T] [CommRing T'] [Algebra A' T']
    {hT : #T ≤ κ} {hT' : #T' ≤ κ} {f g : T →ₐ[A'] T'} (h : f = g) :
    hm hP (hT := hT) (hT' := hT') f = hm hP (hT := hT) (hT' := hT') g := by
  rw [h]

section Cover

variable (A : Type u) [CommRing A] [Algebra A' A] (hA : Function.Surjective (algebraMap A' A))
  (hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
  (B' : Type u) [CommRing B'] [Algebra A' B'] (hA' : #A' ≤ κ) (hB' : #B' ≤ κ)

open Concrete

include hA hA' in
/-- The quotient `A` of `A'` has cardinality at most `κ`. -/
lemma mk_A : #A ≤ κ := (mk_le_of_surjective hA).trans hA'

include hκ hA hA' hB' in
/-- The reduction `B = A ⊗[A'] B'` has cardinality at most `κ`. -/
lemma mk_Bb : #(Bb A' A B') ≤ κ := mk_tensorProduct_le hκ (mk_A A hA hA') hB'

include hκ hB' in
/-- The double product `B' ⊗[A'] B'` has cardinality at most `κ`. -/
lemma mk_B₂ : #(B' ⊗[A'] B') ≤ κ := mk_tensorProduct_le hκ hB' hB'

include hκ hB' in
/-- The triple product `B' ⊗[A'] (B' ⊗[A'] B')` has cardinality at most `κ`. -/
lemma mk_B₃ : #(B' ⊗[A'] (B' ⊗[A'] B')) ≤ κ := mk_tensorProduct_le hκ hB' (mk_B₂ hκ B' hB')

include hκ hA hA' hB' in
/-- The double product `B ⊗[A] B` of the reduction has cardinality at most `κ`. -/
lemma mk_Bb₂ : #(Bb A' A B' ⊗[A] Bb A' A B') ≤ κ :=
  mk_tensorProduct_le hκ (mk_Bb hκ A hA B' hA' hB') (mk_Bb hκ A hA B' hA' hB')

include hκ hA hA' hB' in
/-- The triple product `B ⊗[A] (B ⊗[A] B)` of the reduction has cardinality at most `κ`. -/
lemma mk_Bb₃ : #(Bb A' A B' ⊗[A] (Bb A' A B' ⊗[A] Bb A' A B')) ≤ κ :=
  mk_tensorProduct_le hκ (mk_Bb hκ A hA B' hA' hB') (mk_Bb₂ hκ A hA B' hA' hB')

/-- **The concrete Čech cover** of the thickening `A' → A` by `B'`. -/
abbrev cover : CechCover P where
  O := ob hP A' hA'
  O' := ob hP A (mk_A A hA hA')
  B₁ := ob hP B' hB'
  B₁' := ob hP (Bb A' A B') (mk_Bb hκ A hA B' hA' hB')
  B₂ := ob hP (B' ⊗[A'] B') (mk_B₂ hκ B' hB')
  B₂' := ob hP _ (mk_Bb₂ hκ A hA B' hA' hB')
  B₃ := ob hP (B' ⊗[A'] (B' ⊗[A'] B')) (mk_B₃ hκ B' hB')
  B₃' := ob hP _ (mk_Bb₃ hκ A hA B' hA' hB')
  πO := hm hP (Algebra.ofId A' A)
  π₁ := hm hP (π₁ A' A B')
  π₂ := hm hP (π₂ A' A B')
  π₃ := hm hP (π₃ A' A B')
  ι := hm hP (Algebra.ofId A' B')
  ι' := hm hP ((Algebra.ofId A (Bb A' A B')).restrictScalars A')
  p₁ := hm hP (p₁ A' B')
  p₂ := hm hP (p₂ A' B')
  p₁' := hm hP (i₁ A' A B')
  p₂' := hm hP (i₂ A' A B')
  q₁₂ := hm hP (q₁₂ A' B')
  q₂₃ := hm hP (q₂₃ A' B')
  q₁₃ := hm hP (q₁₃ A' B')
  q₁₂' := hm hP (FrameDescent.e₁₂ₐ A (Bb A' A B'))
  q₂₃' := hm hP (FrameDescent.e₂₃ₐ A (Bb A' A B'))
  q₁₃' := hm hP (FrameDescent.e₁₃ₐ A (Bb A' A B'))
  ι_π := hm_congr hP (f := (π₁ A' A B').comp (Algebra.ofId A' B'))
    (g := ((Algebra.ofId A (Bb A' A B')).restrictScalars A').comp (Algebra.ofId A' A))
    (AlgHom.ext fun a ↦ by simp [IsScalarTower.algebraMap_apply A' A (Bb A' A B')])
  p₁_π := hm_congr hP (p₁_π A' A B')
  p₂_π := hm_congr hP (p₂_π A' A B')
  q₁₂_π := hm_congr hP (q₁₂_π A' A B')
  q₂₃_π := hm_congr hP (q₂₃_π A' A B')
  q₁₃_π := hm_congr hP (q₁₃_π A' A B')
  ι_p := hm_congr hP (f := (p₁ A' B').comp (Algebra.ofId A' B'))
    (g := (p₂ A' B').comp (Algebra.ofId A' B')) (AlgHom.ext fun a ↦ by simp)
  ι_p' := hm_congr hP (f := (i₁ A' A B').comp ((Algebra.ofId A (Bb A' A B')).restrictScalars A'))
    (g := (i₂ A' A B').comp ((Algebra.ofId A (Bb A' A B')).restrictScalars A'))
    (AlgHom.ext fun a ↦ by
      simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul'])
  p₁_q₁₂ := hm_congr hP (p₁_q₁₂ A' B')
  p₂_q₁₂ := hm_congr hP (p₂_q₁₂ A' B')
  p₂_q₂₃ := hm_congr hP (p₂_q₂₃ A' B')
  p₁_q₁₂' := hm_congr hP (FrameDescent.e₁₂_q₁ (A' := A') (A := A) (B := Bb A' A B'))
  p₂_q₁₂' := hm_congr hP (FrameDescent.e₁₂_q₂ (A' := A') (A := A) (B := Bb A' A B'))
  p₂_q₂₃' := hm_congr hP (FrameDescent.e₂₃_q₂ (A' := A') (A := A) (B := Bb A' A B'))
  π₁_surj := bc_surjective A' A hA B'
  π₂_surj := π₂_surjective A' A hA B'
  π₃_surj := π₃_surjective A' A hA B'
  π₁_sq := ker_bc_sq A' A hA hI B'
  π₂_sq := ker_π₂_sq A' A hA hI B'
  π₃_sq := ker_π₃_sq A' A hA hI B'
  hJ₂ := hP _ (mk_trivExt_le hκ (mk_B₂ hκ B' hB') ((mk_subtype_le _).trans (mk_B₂ hκ B' hB')))
  hJ₃ := hP _ (mk_trivExt_le hκ (mk_B₃ hκ B' hB') ((mk_subtype_le _).trans (mk_B₃ hκ B' hB')))

end Cover

/-- An `A`-algebra map, restricted to `A'`, still commutes with the algebra maps from `A`. -/
private lemma restrictScalars_commutes {A : Type u} [CommRing A] [Algebra A' A] {C D : Type u}
    [CommRing C] [CommRing D] [Algebra A C] [Algebra A D] [Algebra A' C] [Algebra A' D]
    [IsScalarTower A' A C] [IsScalarTower A' A D] (f : C →ₐ[A] D) (a : A) :
    (f.restrictScalars A') (algebraMap A C a) = algebraMap A D a :=
  f.commutes a

section KerLin

variable {A : Type u} [CommRing A] {C D C' D' : Type u} [CommRing C] [CommRing D] [CommRing C']
  [CommRing D'] [Algebra A' C] [Algebra A' D] [Algebra A' C'] [Algebra A' D'] [Algebra A D]
  [Algebra A D'] (π : C →ₐ[A'] D) (π' : C' →ₐ[A'] D') (hπ : Function.Surjective π)
  {N N' : Type u} [AddCommGroup N] [AddCommGroup N'] [Module D N] [Module D' N'] [Module A N]
  [Module A N'] [IsScalarTower A D N] [IsScalarTower A D' N']
  (t : RingHom.ker π →ₛₗ[(π : C →+* D)] N) (ht : Function.Bijective t)
  (t' : RingHom.ker π' →ₛₗ[(π' : C' →+* D')] N')
  (q : C →ₐ[A'] C') (e : D →ₐ[A'] D') (hqe : π'.comp q = e.comp π)
  (he : ∀ a : A, e (algebraMap A D a) = algebraMap A D' a)

/-- The kernel element `q j`. -/
def kerElt (j : RingHom.ker π) : RingHom.ker π' :=
  ⟨q j, by
    rw [RingHom.mem_ker, ← AlgHom.comp_apply, hqe, AlgHom.comp_apply,
      show π (j : C) = 0 from j.2, map_zero]⟩

/-- The underlying element of `kerElt j` is `q j`. -/
@[simp] lemma coe_kerElt (j : RingHom.ker π) : (kerElt π π' q e hqe j : C') = q j := rfl

/-- The map of reduced kernel modules induced by a commuting square. -/
def kerFun (n : N) : N' := t' (kerElt π π' q e hqe ((Equiv.ofBijective t ht).symm n))

/-- On `t j`, the map `kerFun` is `t'` applied to the kernel element `q j`. -/
lemma kerFun_t (j : RingHom.ker π) :
    kerFun π π' t ht t' q e hqe (t j) = t' (kerElt π π' q e hqe j) := by
  rw [kerFun, show (Equiv.ofBijective t ht).symm (t j) = j from
    (Equiv.ofBijective t ht).symm_apply_apply j]

include hπ in
/-- The map `kerFun` is semilinear along `e : D → D'`. -/
lemma kerFun_smul (d : D) (n : N) :
    kerFun π π' t ht t' q e hqe (d • n) = e d • kerFun π π' t ht t' q e hqe n := by
  obtain ⟨j, rfl⟩ := ht.2 n
  obtain ⟨c, rfl⟩ := hπ d
  rw [show π c • t j = t (c • j) from (t.map_smulₛₗ c j).symm, kerFun_t, kerFun_t,
    ← AlgHom.comp_apply e π, ← hqe, AlgHom.comp_apply]
  change _ = ((π' : C' →+* D') (q c)) • _
  rw [← t'.map_smulₛₗ]
  congr 1
  apply Subtype.ext
  simp [smul_eq_mul, map_mul]

include hπ he in
/-- **The `A`-linear map of reduced kernels** induced by a commuting square. -/
def kerLin : N →ₗ[A] N' where
  toFun := kerFun π π' t ht t' q e hqe
  map_add' n n' := by
    obtain ⟨j, rfl⟩ := ht.2 n
    obtain ⟨j', rfl⟩ := ht.2 n'
    rw [← map_add, kerFun_t, kerFun_t, kerFun_t, ← map_add]
    congr 1
    exact Subtype.ext (map_add q _ _)
  map_smul' a n := by
    rw [← algebraMap_smul D a n, kerFun_smul π π' hπ t ht t' q e hqe, he, algebraMap_smul,
      RingHom.id_apply]

/-- The underlying function of `kerLin` is `kerFun`. -/
lemma kerLin_apply (n : N) : kerLin π π' hπ t ht t' q e hqe he n = kerFun π π' t ht t' q e hqe n :=
  rfl

/-- On `t j`, the map `kerLin` is `t'` applied to the kernel element `q j`. -/
private lemma kerLin_t (j : RingHom.ker π) :
    kerLin π π' hπ t ht t' q e hqe he (t j) = t' (kerElt π π' q e hqe j) :=
  kerFun_t π π' t ht t' q e hqe j

/-- The map `kerLin` is semilinear along `e : D → D'`. -/
lemma kerLin_smul (d : D) (n : N) :
    kerLin π π' hπ t ht t' q e hqe he (d • n) = e d • kerLin π π' hπ t ht t' q e hqe he n :=
  kerFun_smul π π' hπ t ht t' q e hqe d n

end KerLin

section Main

open Concrete FrameDescent

variable {X : P.FullSubcategory ⥤ Type v} {R : Type u} [CommRing R] [Algebra A' R]
  (Φ : FormallyEtaleChart P X R)
  (A : Type u) [CommRing A] [Algebra A' A] [hAf : Fact (Function.Surjective (algebraMap A' A))]
  [hIf : Fact (RingHom.ker (algebraMap A' A) ^ 2 = ⊥)]
  (B' : Type u) [CommRing B'] [Algebra A' B'] (hA' : #A' ≤ κ) (hB' : #B' ≤ κ)

/-- The kernel `J₁ ⊆ B'`, as a module over the reduction `B`. -/
def J₁b : Type u := RingHom.ker (π₁ A' A B')
/-- The kernel `J₂ ⊆ B' ⊗ B'`, as a module over `B ⊗ B`. -/
def J₂b : Type u := RingHom.ker (π₂ A' A B')
/-- The kernel `J₃ ⊆ B' ⊗ (B' ⊗ B')`, as a module over `B ⊗ (B ⊗ B)`. -/
def J₃b : Type u := RingHom.ker (π₃ A' A B')

/-- The additive group structure of the kernel `J₁b`. -/
instance : AddCommGroup (J₁b (A' := A') A B') :=
  inferInstanceAs (AddCommGroup (RingHom.ker (π₁ A' A B')))
/-- The additive group structure of the kernel `J₂b`. -/
instance : AddCommGroup (J₂b (A' := A') A B') :=
  inferInstanceAs (AddCommGroup (RingHom.ker (π₂ A' A B')))
/-- The additive group structure of the kernel `J₃b`. -/
instance : AddCommGroup (J₃b (A' := A') A B') :=
  inferInstanceAs (AddCommGroup (RingHom.ker (π₃ A' A B')))

/-- The square-zero kernel `J₁b` as a module over the reduction `B`. -/
instance : Module (Bb A' A B') (J₁b (A' := A') A B') :=
  sqZeroModule (π₁ A' A B') (bc_surjective A' A hAf.out B') (ker_bc_sq A' A hAf.out hIf.out B')
/-- The square-zero kernel `J₂b` as a module over `B ⊗[A] B`. -/
instance : Module (Bb A' A B' ⊗[A] Bb A' A B') (J₂b (A' := A') A B') :=
  sqZeroModule (π₂ A' A B') (π₂_surjective A' A hAf.out B') (ker_π₂_sq A' A hAf.out hIf.out B')
/-- The square-zero kernel `J₃b` as a module over `B ⊗[A] (B ⊗[A] B)`. -/
instance : Module (Bb A' A B' ⊗[A] (Bb A' A B' ⊗[A] Bb A' A B')) (J₃b (A' := A') A B') :=
  sqZeroModule (π₃ A' A B') (π₃_surjective A' A hAf.out B') (ker_π₃_sq A' A hAf.out hIf.out B')

/-- The `A`-module structure on `J₁b` by restriction of scalars along `A → B`. -/
instance : Module A (J₁b (A' := A') A B') := Module.compHom _ (algebraMap A (Bb A' A B'))
/-- The `A`-module structure on `J₂b` by restriction of scalars along `A → B ⊗[A] B`. -/
instance : Module A (J₂b (A' := A') A B') :=
  Module.compHom _ (algebraMap A (Bb A' A B' ⊗[A] Bb A' A B'))
/-- The `A`-module structure on `J₃b` by restriction of scalars along `A → B ⊗[A] (B ⊗[A] B)`. -/
instance : Module A (J₃b (A' := A') A B') :=
  Module.compHom _ (algebraMap A (Bb A' A B' ⊗[A] (Bb A' A B' ⊗[A] Bb A' A B')))

/-- The scalar actions of `A` and `B` on `J₁b` form a tower. -/
instance : IsScalarTower A (Bb A' A B') (J₁b (A' := A') A B') :=
  ⟨fun a c j ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
/-- The scalar actions of `A` and `B ⊗[A] B` on `J₂b` form a tower. -/
instance : IsScalarTower A (Bb A' A B' ⊗[A] Bb A' A B') (J₂b (A' := A') A B') :=
  ⟨fun a c j ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩
/-- The scalar actions of `A` and `B ⊗[A] (B ⊗[A] B)` on `J₃b` form a tower. -/
instance : IsScalarTower A (Bb A' A B' ⊗[A] (Bb A' A B' ⊗[A] Bb A' A B')) (J₃b (A' := A') A B') :=
  ⟨fun a c j ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

/-- The identity `J₁ → J₁b`, semilinear along `B' → B`. -/
def t₁ : RingHom.ker (π₁ A' A B') →ₛₗ[((π₁ A' A B' : B' →ₐ[A'] Bb A' A B') : B' →+* Bb A' A B')]
    J₁b (A' := A') A B' where
  toFun j := j
  map_add' _ _ := rfl
  map_smul' c j := (sqZero_smul_eq (π₁ A' A B') (bc_surjective A' A hAf.out B')
    (ker_bc_sq A' A hAf.out hIf.out B') c j).symm

/-- The identity `J₂ → J₂b`, semilinear along `B' ⊗ B' → B ⊗ B`. -/
def t₂ : RingHom.ker (π₂ A' A B') →ₛₗ[((π₂ A' A B' :
      B' ⊗[A'] B' →ₐ[A'] Bb A' A B' ⊗[A] Bb A' A B') :
      B' ⊗[A'] B' →+* Bb A' A B' ⊗[A] Bb A' A B')]
    J₂b (A' := A') A B' where
  toFun j := j
  map_add' _ _ := rfl
  map_smul' c j := (sqZero_smul_eq (π₂ A' A B') (π₂_surjective A' A hAf.out B')
    (ker_π₂_sq A' A hAf.out hIf.out B') c j).symm

/-- The identity `J₃ → J₃b`, semilinear along the reduction. -/
def t₃ : RingHom.ker (π₃ A' A B') →ₛₗ[((π₃ A' A B' : B' ⊗[A'] (B' ⊗[A'] B') →ₐ[A']
      Bb A' A B' ⊗[A] (Bb A' A B' ⊗[A] Bb A' A B')) :
      B' ⊗[A'] (B' ⊗[A'] B') →+* Bb A' A B' ⊗[A] (Bb A' A B' ⊗[A] Bb A' A B'))]
    J₃b (A' := A') A B' where
  toFun j := j
  map_add' _ _ := rfl
  map_smul' c j := (sqZero_smul_eq (π₃ A' A B') (π₃_surjective A' A hAf.out B')
    (ker_π₃_sq A' A hAf.out hIf.out B') c j).symm

/-- The map `t₁` is bijective. -/
lemma t₁_bij : Function.Bijective (t₁ (A' := A') A B') := Function.bijective_id
/-- The map `t₂` is bijective. -/
lemma t₂_bij : Function.Bijective (t₂ (A' := A') A B') := Function.bijective_id
/-- The map `t₃` is bijective. -/
lemma t₃_bij : Function.Bijective (t₃ (A' := A') A B') := Function.bijective_id

/-- The underlying element of `B' ⊗ B'` of an element of `J₂b`. -/
def v₂ (j : J₂b (A' := A') A B') : B' ⊗[A'] B' := (show RingHom.ker (π₂ A' A B') from j).1
/-- The underlying element of `B' ⊗ (B' ⊗ B')` of an element of `J₃b`. -/
def v₃ (j : J₃b (A' := A') A B') : B' ⊗[A'] (B' ⊗[A'] B') :=
  (show RingHom.ker (π₃ A' A B') from j).1

omit hAf hIf in
/-- The map `v₂` is additive. -/
lemma v₂_add (j j' : J₂b (A' := A') A B') :
    v₂ (A' := A') A B' (j + j') = v₂ (A' := A') A B' j + v₂ (A' := A') A B' j' := rfl
omit hAf hIf in
/-- The map `v₃` is additive. -/
lemma v₃_add (j j' : J₃b (A' := A') A B') :
    v₃ (A' := A') A B' (j + j') = v₃ (A' := A') A B' j + v₃ (A' := A') A B' j' := rfl
omit hAf hIf in
/-- The map `v₂` commutes with subtraction. -/
lemma v₂_sub (j j' : J₂b (A' := A') A B') :
    v₂ (A' := A') A B' (j - j') = v₂ (A' := A') A B' j - v₂ (A' := A') A B' j' := rfl
omit hAf hIf in
/-- The map `v₃` is injective. -/
lemma v₃_injective : Function.Injective (v₃ (A' := A') A B') := fun _ _ h ↦ Subtype.ext h



/-- An element of `J₁b`, read in the kernel `J₁ ⊆ B'`. -/
def raw₁ (x : J₁b (A' := A') A B') : RingHom.ker (π₁ A' A B') := x

/-- For `c : B'`, `c • raw₁ x = raw₁ (π₁ c • x)`. -/
lemma raw₁_smul (c : B') (x : J₁b (A' := A') A B') :
    c • raw₁ A B' x = raw₁ A B' (π₁ A' A B' c • x) :=
  (t₁ (A' := A') A B').map_smulₛₗ c x

omit hAf hIf in
/-- The map `raw₁` is additive. -/
lemma raw₁_add (x y : J₁b (A' := A') A B') : raw₁ A B' (x + y) = raw₁ A B' x + raw₁ A B' y := rfl

/-- The map of reduced kernels `J₂b → J₃b` induced by `q` sends `t₂ j` to an element with
underlying element `q j`. -/
lemma v₃_kerLin (q : B' ⊗[A'] B' →ₐ[A'] B' ⊗[A'] (B' ⊗[A'] B'))
    (e : Bb A' A B' ⊗[A] Bb A' A B' →ₐ[A'] Bb A' A B' ⊗[A] (Bb A' A B' ⊗[A] Bb A' A B'))
    (hqe : (π₃ A' A B').comp q = e.comp (π₂ A' A B'))
    (he : ∀ a : A, e (algebraMap A _ a) = algebraMap A _ a) (j : RingHom.ker (π₂ A' A B')) :
    v₃ (A' := A') A B' (kerLin (π₂ A' A B') (π₃ A' A B') (π₂_surjective A' A hAf.out B')
      (t₂ (A' := A') A B') (t₂_bij A B') (t₃ (A' := A') A B') q e hqe he
      (t₂ (A' := A') A B' j)) = q j := by
  rw [kerLin_t]; rfl

/-- The map of reduced kernels `J₁b → J₂b` induced by `q` sends `t₁ j` to an element with
underlying element `q j`. -/
lemma v₂_kerLin (q : B' →ₐ[A'] B' ⊗[A'] B') (e : Bb A' A B' →ₐ[A'] Bb A' A B' ⊗[A] Bb A' A B')
    (hqe : (π₂ A' A B').comp q = e.comp (π₁ A' A B'))
    (he : ∀ a : A, e (algebraMap A _ a) = algebraMap A _ a) (j : RingHom.ker (π₁ A' A B')) :
    v₂ (A' := A') A B' (kerLin (π₁ A' A B') (π₂ A' A B') (bc_surjective A' A hAf.out B')
      (t₁ (A' := A') A B') (t₁_bij A B') (t₂ (A' := A') A B') q e hqe he
      (t₁ (A' := A') A B' j)) = q j := by
  rw [kerLin_t]; rfl

variable [Algebra R (Bb A' A B')] [IsScalarTower A' R (Bb A' A B')] [Module.FaithfullyFlat A' B']
  [Module.Projective R Ω[R⁄A']] (hR : #R ≤ κ)

/-- The concrete cover. -/
abbrev Kc := cover hκ hP A hAf.out hIf.out B' hA' hB'

omit hIf [IsScalarTower A' R (Bb A' A B')] [Module.FaithfullyFlat A' B']
  [Module.Projective R Ω[R⁄A']] in
include hκ hA' hB' hR in
/-- The frame module `FrameModule R B` has cardinality at most `κ`. -/
lemma mk_frameModule : #(FrameModule (A' := A') R (Bb A' A B')) ≤ κ :=
  mk_tensorProduct_le hκ (mk_Bb hκ A hAf.out B' hA' hB') (mk_kaehler_le hκ hR)

omit hIf [IsScalarTower A' R (Bb A' A B')] [Module.FaithfullyFlat A' B']
  [Module.Projective R Ω[R⁄A']] in
include hκ hA' hB' hR in
/-- The module `E₁ R A B` has cardinality at most `κ`. -/
lemma mk_E₁ : #(E₁ (A' := A') R A (Bb A' A B')) ≤ κ :=
  mk_tensorProduct_le hκ (mk_frameModule hκ A B' hA' hB' hR) (mk_Bb hκ A hAf.out B' hA' hB')

omit hIf [IsScalarTower A' R (Bb A' A B')] [Module.FaithfullyFlat A' B']
  [Module.Projective R Ω[R⁄A']] in
include hκ hA' hB' hR in
/-- The module `E₂ R A B` has cardinality at most `κ`. -/
lemma mk_E₂ : #(E₂ (A' := A') R A (Bb A' A B')) ≤ κ :=
  mk_tensorProduct_le hκ (mk_Bb hκ A hAf.out B' hA' hB') (mk_frameModule hκ A B' hA' hB' hR)

omit hIf [IsScalarTower A' R (Bb A' A B')] [Module.FaithfullyFlat A' B']
  [Module.Projective R Ω[R⁄A']] in
include hκ hA' hB' hR in
/-- The module `F₃ R A B` has cardinality at most `κ`. -/
lemma mk_F₃ : #(F₃ (A' := A') R (A := A) (B := Bb A' A B')) ≤ κ :=
  mk_tensorProduct_le hκ (mk_Bb hκ A hAf.out B' hA' hB') (mk_E₂ hκ A B' hA' hB' hR)


attribute [local irreducible] Concrete.π₂ Concrete.π₃ in
include hκ hA' hB' hR in
/-- Let `x` be a point of `X` over `A` whose restriction to the reduction `B` has frame
`frame R B`, and let `u' : R → B'` lift that frame. If `X` satisfies the sheaf condition for
`A' → B'` and is separated for `A → B`, then `x` is the image of a point of `X` over `A'`. -/
theorem exists_lift (x : X.obj (Kc hκ hP A B' hA' hB').O')
    (hū : Φ.pt (Kc hκ hP A B' hA' hB').B₁' (frame R (Bb A' A B')) =
      X.map (Kc hκ hP A B' hA' hB').ι' x)
    (u' : R →ₐ[A'] B') (hu' : (π₁ A' A B').comp u' = frame R (Bb A' A B'))
    (hglue : ∀ z : X.obj (Kc hκ hP A B' hA' hB').B₁,
      X.map (Kc hκ hP A B' hA' hB').p₁ z = X.map (Kc hκ hP A B' hA' hB').p₂ z →
        ∃ z₀, X.map (Kc hκ hP A B' hA' hB').ι z₀ = z)
    (hsep : ∀ y₁ y₂ : X.obj (Kc hκ hP A B' hA' hB').O',
      X.map (Kc hκ hP A B' hA' hB').ι' y₁ = X.map (Kc hκ hP A B' hA' hB').ι' y₂ → y₁ = y₂) :
    ∃ z : X.obj (Kc hκ hP A B' hA' hB').O, X.map (Kc hκ hP A B' hA' hB').πO z = x := by
  have hC₂ : P (CommAlgCat.of A' ((Bb A' A B') ⊗[A] (Bb A' A B'))) :=
    hP _ (mk_Bb₂ hκ A hAf.out B' hA' hB')
  have hpt : Φ.pt (C₂ A (Bb A' A B') hC₂) (w₁ R A (Bb A' A B') hC₂) =
      Φ.pt (C₂ A (Bb A' A B') hC₂) (w₂ R A (Bb A' A B') hC₂) :=
    CechCover.pt_p₁'_eq_pt_p₂' Φ (Kc hκ hP A B' hA' hB') x _ hū
  have hE₁ := hP _ (mk_trivExt_le hκ (mk_Bb₂ hκ A hAf.out B' hA' hB') (mk_E₁ hκ A B' hA' hB' hR))
  have hE₂ := hP _ (mk_trivExt_le hκ (mk_Bb₂ hκ A hAf.out B' hA' hB') (mk_E₂ hκ A B' hA' hB' hR))
  have hC₃ : P (CommAlgCat.of A' ((Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B')))) :=
    hP _ (mk_Bb₃ hκ A hAf.out B' hA' hB')
  have hF₃ := hP _ (mk_trivExt_le hκ (mk_Bb₃ hκ A hAf.out B' hA' hB') (mk_F₃ hκ A B' hA' hB' hR))
  obtain ⟨Dm⟩ := exists_descended R Φ hC₂ hpt hE₁ hE₂ hC₃ hF₃
  have hM : Module.Projective A Dm.M := Dm.projective
  -- the defect, read along the second reduced frame, and the map `φ_D : M → J₂` it comes from
  have hw₂ : (π₂ A' A B').comp ((p₂ A' B').comp u') =
      ((Descended.incl₂ (A := A) (B := Bb A' A B')).restrictScalars A').comp
        (frame R (Bb A' A B')) := by
    rw [← AlgHom.comp_assoc, p₂_π, AlgHom.comp_assoc, hu']
  let D := CechCover.defect (Φ := Φ) (K := Kc hκ hP A B' hA' hB') hū u' hu'
  let Db := (D.map (π₂ A' A B') (t₂ (A' := A') A B')).cast hw₂
  let φD := Dm.phiOf (Descended.incl₂ (A := A) (B := Bb A' A B')) Db
  have hDb : Dm.psi (Descended.incl₂ (A := A) (B := Bb A' A B')) φD = Db := Dm.psi_phiOf _ _
  -- the `A`-algebra maps out of `B` into the double and triple products
  let i1 : (Bb A' A B') →ₐ[A] (Bb A' A B') ⊗[A] (Bb A' A B') := Algebra.TensorProduct.includeLeft
  let i2 : (Bb A' A B') →ₐ[A] (Bb A' A B') ⊗[A] (Bb A' A B') := Algebra.TensorProduct.includeRight
  let E12 : (Bb A' A B') ⊗[A] (Bb A' A B') →ₐ[A]
      (Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B')) :=
    Algebra.TensorProduct.map (AlgHom.id A (Bb A' A B')) Algebra.TensorProduct.includeLeft
  let E23 : (Bb A' A B') ⊗[A] (Bb A' A B') →ₐ[A]
      (Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B')) :=
    Algebra.TensorProduct.includeRight
  let E13 : (Bb A' A B') ⊗[A] (Bb A' A B') →ₐ[A]
      (Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B')) :=
    Algebra.TensorProduct.map (AlgHom.id A (Bb A' A B')) Algebra.TensorProduct.includeRight
  -- the `A`-linear maps of reduced kernels
  let k1 := kerLin (π₁ A' A B') (π₂ A' A B') (bc_surjective A' A hAf.out B') (t₁ (A' := A') A B')
    (t₁_bij A B') (t₂ (A' := A') A B') (p₁ A' B') (i1.restrictScalars A') (p₁_π A' A B')
    (restrictScalars_commutes i1)
  let k2 := kerLin (π₁ A' A B') (π₂ A' A B') (bc_surjective A' A hAf.out B') (t₁ (A' := A') A B')
    (t₁_bij A B') (t₂ (A' := A') A B') (p₂ A' B') (i2.restrictScalars A') (p₂_π A' A B')
    (restrictScalars_commutes i2)
  let k12 := kerLin (π₂ A' A B') (π₃ A' A B') (π₂_surjective A' A hAf.out B') (t₂ (A' := A') A B')
    (t₂_bij A B') (t₃ (A' := A') A B') (q₁₂ A' B') (E12.restrictScalars A') (q₁₂_π A' A B')
    (restrictScalars_commutes E12)
  let k23 := kerLin (π₂ A' A B') (π₃ A' A B') (π₂_surjective A' A hAf.out B') (t₂ (A' := A') A B')
    (t₂_bij A B') (t₃ (A' := A') A B') (q₂₃ A' B') (E23.restrictScalars A') (q₂₃_π A' A B')
    (restrictScalars_commutes E23)
  let k13 := kerLin (π₂ A' A B') (π₃ A' A B') (π₂_surjective A' A hAf.out B') (t₂ (A' := A') A B')
    (t₂_bij A B') (t₃ (A' := A') A B') (q₁₃ A' B') (E13.restrictScalars A') (q₁₃_π A' A B')
    (restrictScalars_commutes E13)
  -- the cocycle identity of `φ_D`
  let a3 : (Bb A' A B') →ₐ[A] (Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B')) := E23.comp i1
  let b3 : (Bb A' A B') →ₐ[A] (Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B')) := E23.comp i2
  have hE12i2 : E12.comp i2 = a3 := by ext b; simp [a3, E12, E23, i1, i2]
  have hE13i2 : E13.comp i2 = b3 := by ext b; simp [b3, E13, E23, i2]
  have hab : Φ.pt (Kc hκ hP A B' hA' hB').B₃'
      ((a3.restrictScalars A').comp (frame R (Bb A' A B'))) =
      Φ.pt (Kc hκ hP A B' hA' hB').B₃' ((b3.restrictScalars A').comp (frame R (Bb A' A B'))) := by
    have h := congrArg (X.map (hm hP (hT := mk_Bb₂ hκ A hAf.out B' hA' hB')
      (hT' := mk_Bb₃ hκ A hAf.out B' hA' hB') (E23.restrictScalars A'))) hpt
    rw [← Φ.pt_comp, ← Φ.pt_comp] at h
    exact h
  have hJ3C : P (CommAlgCat.of A'
      (TrivExt ((Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B'))) (J₃b (A' := A') A B'))) :=
    hP _ (mk_trivExt_le hκ (mk_Bb₃ hκ A hAf.out B' hA' hB')
      ((mk_subtype_le _).trans (mk_B₃ hκ B' hB')))
  have hpsiD : ∀ r, Dm.psi i2 φD r = t₂ (A' := A') A B' (D r) := fun r ↦ by
    rw [hDb]; rfl
  have e₁ : (π₃ A' A B').comp ((q₂₃ A' B').comp ((p₁ A' B').comp u')) =
      (a3.restrictScalars A').comp (frame R (Bb A' A B')) := AlgHom.ext fun r ↦ by
    have h1 := AlgHom.congr_fun (q₂₃_π A' A B') (p₁ A' B' (u' r))
    have h2 := AlgHom.congr_fun (p₁_π A' A B') (u' r)
    have h3 := AlgHom.congr_fun hu' r
    simp only [AlgHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3]; rfl
  have e₂ : (π₃ A' A B').comp ((q₂₃ A' B').comp (CechCover.lift₂ (Φ := Φ)
      (K := Kc hκ hP A B' hA' hB') hū u' hu')) =
      (b3.restrictScalars A').comp (frame R (Bb A' A B')) :=
    AlgHom.ext fun r ↦ by
      have h1 := AlgHom.congr_fun (q₂₃_π A' A B') (CechCover.lift₂ (Φ := Φ)
        (K := Kc hκ hP A B' hA' hB') hū u' hu' r)
      have h2 := AlgHom.congr_fun (CechCover.π₂_lift₂ (Φ := Φ) (K := Kc hκ hP A B' hA' hB')
        hū u' hu') r
      simp only [AlgHom.comp_apply] at h1 h2 ⊢
      rw [h1]
      change (e₂₃ₐ A (Bb A' A B')) (ah (Kc hκ hP A B' hA' hB').π₂ _) = _
      rw [h2]; rfl
  have hNf : letI := Module.compHom (J₃b (A' := A') A B') (Algebra.TensorProduct.lift a3 b3
        (fun _ _ ↦ Commute.all _ _) : (Bb A' A B') ⊗[A] (Bb A' A B') →ₐ[A]
          (Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B'))).toRingHom
      P (CommAlgCat.of A' (TrivExt ((Bb A' A B') ⊗[A] (Bb A' A B')) (J₃b (A' := A') A B'))) := by
    let := Module.compHom (J₃b (A' := A') A B') (Algebra.TensorProduct.lift a3 b3
        (fun _ _ ↦ Commute.all _ _) : (Bb A' A B') ⊗[A] (Bb A' A B') →ₐ[A]
          (Bb A' A B') ⊗[A] ((Bb A' A B') ⊗[A] (Bb A' A B'))).toRingHom
    exact hP _ (mk_trivExt_le hκ (mk_Bb₂ hκ A hAf.out B' hA' hB')
      ((mk_subtype_le _).trans (mk_B₃ hκ B' hB')))
  have hT : ∀ (h : Φ.pt (Kc hκ hP A B' hA' hB').B₃ ((q₂₃ A' B').comp ((p₁ A' B').comp u')) =
      Φ.pt (Kc hκ hP A B' hA' hB').B₃ ((q₂₃ A' B').comp (CechCover.lift₂ (Φ := Φ)
        (K := Kc hκ hP A B' hA' hB') hū u' hu')))
      (δ : DerAlong ((q₂₃ A' B').comp ((p₁ A' B').comp u')) (RingHom.ker (π₃ A' A B')))
      (_ : ∀ r, t₃ (A' := A') A B' (δ r) = Dm.psi a3 (k12.comp φD) r) (r : R),
      t₃ (A' := A') A B' (Φ.transportFun (Kc hκ hP A B' hA' hB').hJ₃ h δ r) =
        Dm.psi b3 (k12.comp φD) r := by
    intro h δ hδ r
    exact Dm.transportFun_map_psi_pair h (Kc hκ hP A B' hA' hB').π₃ (t₃ (A' := A') A B') a3 b3
      e₁ e₂ hJ3C hNf hab (k12.comp φD) δ hδ r
  have hcoc : k13.comp φD = k23.comp φD + k12.comp φD := by
    refine Dm.psi_injective b3 fun r ↦ v₃_injective A B' ?_
    have hTr := hT (CechCover.pt_q₂₃_v₁_eq (Φ := Φ) (K := Kc hκ hP A B' hA' hB') hū u' hu')
      ((D.map (ah (Kc hκ hP A B' hA' hB').q₁₂)
        (CechCover.kerQ₁₂ (K := Kc hκ hP A B' hA' hB'))).cast
          (CechCover.q₁₂_v₂ (K := Kc hκ hP A B' hA' hB') u'))
      (fun r ↦ by
        rw [← Dm.psi_comp_eq _ E12 a3 hE12i2 φD k12 (kerLin_smul _ _ _ _ _ _ _ _ _ _), hpsiD]
        simp only [k12]
        rw [kerLin_t]; rfl) r
    have hdc := CechCover.defect_cocycle (Φ := Φ) (K := Kc hκ hP A B' hA' hB') hū u' hu' r
    rw [Dm.psi_add, v₃_add,
      ← Dm.psi_comp_eq _ E13 b3 hE13i2 φD k13 (kerLin_smul _ _ _ _ _ _ _ _ _ _),
      ← Dm.psi_comp_eq _ E23 b3 rfl φD k23 (kerLin_smul _ _ _ _ _ _ _ _ _ _), hpsiD, ← hTr]
    simp only [k13, k23]
    rw [v₃_kerLin, v₃_kerLin]
    exact hdc
  -- every value of `φ_D` is a coboundary, so `φ_D` lifts through `d = k2 - k1`
  let d := k2 - k1
  have hrange : ∀ m, φD m ∈ LinearMap.range d := by
    intro m
    have hc := congrArg (fun φ : Dm.M →ₗ[A] J₃b (A' := A') A B' ↦ v₃ (A' := A') A B' (φ m)) hcoc
    simp only [LinearMap.comp_apply, LinearMap.add_apply, v₃_add] at hc
    obtain ⟨c, hc0⟩ : ∃ c : RingHom.ker (π₂ A' A B'), t₂ (A' := A') A B' c = φD m :=
      (t₂_bij A B').2 _
    rw [← hc0] at hc
    simp only [k13, k23, k12] at hc
    rw [v₃_kerLin, v₃_kerLin, v₃_kerLin] at hc
    obtain ⟨s₀, hs₀, hs⟩ := exists_ker_of_cocycle A' A hAf.out B' c c.2 (by rw [hc]; abel)
    refine ⟨t₁ (A' := A') A B' ⟨s₀, hs₀⟩, ?_⟩
    rw [← hc0]
    apply Subtype.ext
    change v₂ (A' := A') A B' (k2 _ - k1 _) = _
    rw [v₂_sub]
    simp only [k1, k2]
    rw [v₂_kerLin, v₂_kerLin]
    exact hs
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property (LinearMap.rangeRestrict d)
    (LinearMap.codRestrict (LinearMap.range d) φD hrange) (LinearMap.surjective_rangeRestrict d)
  have hdψ : d.comp ψ = φD := by
    ext m
    have := congrArg Subtype.val (LinearMap.congr_fun hψ m)
    simpa using this
  -- the correcting derivation `θ` along `u'`
  let θb := Dm.psi (AlgHom.id A (Bb A' A B')) ψ
  let θ : DerAlong u' (Kc hκ hP A B' hA' hB').J₁ :=
    ⟨fun r ↦ raw₁ A B' (θb r), fun r s ↦ by rw [θb.map_add, raw₁_add],
      fun a ↦ by rw [θb.map_algebraMap]; rfl, fun r s ↦ by
        have hu1 : ∀ r, π₁ A' A B' (u' r) = frame R (Bb A' A B') r :=
          fun r ↦ AlgHom.congr_fun hu' r
        change raw₁ A B' (θb (r * s)) = u' r • raw₁ A B' (θb s) + u' s • raw₁ A B' (θb r)
        rw [raw₁_smul, raw₁_smul, hu1, hu1, ← raw₁_add, θb.leibniz]
        rfl⟩
  -- the twisted coboundary of `θ` is the defect
  have hJ2C : P (CommAlgCat.of A' (TrivExt (Bb A' A B' ⊗[A] Bb A' A B') (J₂b (A' := A') A B'))) :=
    hP _ (mk_trivExt_le hκ (mk_Bb₂ hκ A hAf.out B' hA' hB')
      ((mk_subtype_le _).trans (mk_B₂ hκ B' hB')))
  have hNf2 : letI := Module.compHom (J₂b (A' := A') A B') (Algebra.TensorProduct.lift i1 i2
        (fun _ _ ↦ Commute.all _ _) : Bb A' A B' ⊗[A] Bb A' A B' →ₐ[A]
          Bb A' A B' ⊗[A] Bb A' A B').toRingHom
      P (CommAlgCat.of A' (TrivExt (Bb A' A B' ⊗[A] Bb A' A B') (J₂b (A' := A') A B'))) := by
    let := Module.compHom (J₂b (A' := A') A B') (Algebra.TensorProduct.lift i1 i2
        (fun _ _ ↦ Commute.all _ _) : Bb A' A B' ⊗[A] Bb A' A B' →ₐ[A]
          Bb A' A B' ⊗[A] Bb A' A B').toRingHom
    exact hP _ (mk_trivExt_le hκ (mk_Bb₂ hκ A hAf.out B' hA' hB')
      ((mk_subtype_le _).trans (mk_B₂ hκ B' hB')))
  have e₁' : (π₂ A' A B').comp ((p₁ A' B').comp u') =
      (i1.restrictScalars A').comp (frame R (Bb A' A B')) := by
    rw [← AlgHom.comp_assoc, p₁_π, AlgHom.comp_assoc, hu']
  have e₂' : (π₂ A' A B').comp (CechCover.lift₂ (Φ := Φ) (K := Kc hκ hP A B' hA' hB') hū u' hu') =
      (i2.restrictScalars A').comp (frame R (Bb A' A B')) :=
    CechCover.π₂_lift₂ (Φ := Φ) (K := Kc hκ hP A B' hA' hB') hū u' hu'
  have hT2 : ∀ r, t₂ (A' := A') A B' (Φ.transportFun (Kc hκ hP A B' hA' hB').hJ₂
      (CechCover.pt_v₁_eq_pt_lift₂ (Φ := Φ) (K := Kc hκ hP A B' hA' hB') hū u' hu')
      (θ.map (ah (Kc hκ hP A B' hA' hB').p₁) (CechCover.kerP₁ (K := Kc hκ hP A B' hA' hB'))) r) =
        Dm.psi i2 (k1.comp ψ) r := fun r ↦
    Dm.transportFun_map_psi_pair
      (CechCover.pt_v₁_eq_pt_lift₂ (Φ := Φ) (K := Kc hκ hP A B' hA' hB') hū u' hu')
      (Kc hκ hP A B' hA' hB').π₂ (t₂ (A' := A') A B') i1 i2 e₁' e₂' hJ2C hNf2 hpt (k1.comp ψ)
      _ (fun r ↦ by
        rw [← Dm.psi_comp_eq _ i1 i1 (AlgHom.comp_id _) ψ k1 (kerLin_smul _ _ _ _ _ _ _ _ _ _)]
        simp only [k1]
        rw [show θb r = t₁ (A' := A') A B' (raw₁ A B' (θb r)) from rfl, kerLin_t]
        rfl) r
  have hθ2 : ∀ r, t₂ (A' := A') A B' ((θ.map (ah (Kc hκ hP A B' hA' hB').p₂)
      (CechCover.kerP₂ (K := Kc hκ hP A B' hA' hB'))) r) = Dm.psi i2 (k2.comp ψ) r := fun r ↦ by
    rw [← Dm.psi_comp_eq _ i2 i2 (AlgHom.comp_id _) ψ k2 (kerLin_smul _ _ _ _ _ _ _ _ _ _)]
    simp only [k2]
    rw [show θb r = t₁ (A' := A') A B' (raw₁ A B' (θb r)) from rfl, kerLin_t]
    rfl
  have hD : ∀ r, t₂ (A' := A') A B' (D r) =
      Dm.psi i2 (k2.comp ψ) r - Dm.psi i2 (k1.comp ψ) r := fun r ↦ by
    rw [← hpsiD, ← Dm.psi_sub, ← LinearMap.sub_comp, ← hdψ]
  refine CechCover.exists_lift_of_coboundary (Φ := Φ) (K := Kc hκ hP A B' hA' hB') hū u' hu'
    hglue hsep θ fun r ↦ ?_
  have h1 := congrArg (v₂ (A' := A') A B') (hθ2 r)
  have h2 := congrArg (v₂ (A' := A') A B') (hT2 r)
  have h3 := congrArg (v₂ (A' := A') A B') (hD r)
  rw [v₂_sub] at h3
  exact (congrArg₂ (· - ·) h1 h2).trans h3.symm

end Main

end Assembly

end Stacks.ChartGlue

end
