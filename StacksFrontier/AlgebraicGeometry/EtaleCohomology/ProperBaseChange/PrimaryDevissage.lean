module

public import Mathlib.Data.Nat.Factorization.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AlgClosedCase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian

/-!
# Dévissage of an annihilated object into prime-annihilated pieces

Let `F` be an exact functor between abelian categories and `X` an object of its source. If `F` is
bijective on `Ext` from `X` into every object killed by a prime, in every degree, then it is
bijective on `Ext` from `X` into every object killed by a positive integer. The same holds for the
restriction map on étale cohomology along a morphism of schemes.

## Main definitions

* `Stacks.EtaleCohomology.kernelQuotientShortComplex`: the short exact sequence
  `0 → ker φ → A → A/ker φ → 0` of an endomorphism `φ` of an object of an abelian category.

## Main results

* `Stacks.EtaleCohomology.isBijectiveOnExt_of_nsmul_id_eq_zero_of_pow`: if an exact functor is
  bijective on `Ext` into every object killed by `a`, then it is bijective on `Ext` into every
  object killed by a power of `a`.
* `Stacks.EtaleCohomology.isBijectiveOnExt_of_nsmul_id_eq_zero`: if an exact functor is
  bijective on `Ext` into every object killed by a prime, then it is bijective on `Ext` into
  every object killed by a positive integer.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_bijective_of_nsmul_id_eq_zero`: the
  same statement for the restriction map on étale cohomology along an arbitrary morphism of
  schemes.

## Implementation notes

No decomposition into primary parts is used: writing `n = a * b` with `a` the `ℓ`-part and `b`
the prime-to-`ℓ` part, the sequence `0 → A[a] → A → A/A[a] → 0` has its sub killed by `a` and its
quotient killed by `b`, so an induction on `n` along short exact sequences
(`Stacks.EtaleCohomology.isBijectiveOnExt_of_shortExact`) suffices.

Being killed by an integer is the global condition `n • 𝟙 F = 0`, not the local torsion condition
`Stacks.Torsion.torsionSheafProperty`.

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.EtaleCohomology

universe w u v v₁ v₂ u₁ u₂

section Annihilated

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]

/-- The short exact sequence `0 → ker φ → A → A/ker φ → 0` attached to an endomorphism `φ` of an
object of an abelian category. -/
def kernelQuotientShortComplex {A : C} (φ : A ⟶ A) : ShortComplex C :=
  ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (by simp)

/-- The sequence `0 → ker φ → A → A/ker φ → 0` is short exact. -/
lemma kernelQuotientShortComplex_shortExact {A : C} (φ : A ⟶ A) :
    (kernelQuotientShortComplex φ).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := inferInstanceAs (Mono (kernel.ι φ))
  epi_g := inferInstanceAs (Epi (cokernel.π (kernel.ι φ)))

/-- The kernel of multiplication by `a` on `A` is killed by `a`. -/
lemma nsmul_id_kernel_eq_zero (A : C) (a : ℕ) :
    a • 𝟙 (kernel (a • 𝟙 A)) = 0 := by
  rw [← cancel_mono (kernel.ι (a • 𝟙 A)), zero_comp, Preadditive.nsmul_comp,
    Category.id_comp, ← Category.comp_id (kernel.ι (a • 𝟙 A)),
    ← Preadditive.comp_nsmul]
  exact kernel.condition _

/-- If `a * b` kills `A` then `b` kills the quotient of `A` by the kernel of multiplication by
`a`. -/
lemma nsmul_id_cokernel_eq_zero (A : C) (a b : ℕ) (hA : (a * b) • 𝟙 A = 0) :
    b • 𝟙 (cokernel (kernel.ι (a • 𝟙 A))) = 0 := by
  have hfac : (b • 𝟙 A) ≫ (a • 𝟙 A) = 0 := by
    rw [Preadditive.nsmul_comp, Category.id_comp, smul_smul, Nat.mul_comm, hA]
  have hzero : (b • 𝟙 A) ≫ cokernel.π (kernel.ι (a • 𝟙 A)) = 0 := by
    rw [← kernel.lift_ι (a • 𝟙 A) (b • 𝟙 A) hfac, Category.assoc, cokernel.condition,
      comp_zero]
  rw [← cancel_epi (cokernel.π (kernel.ι (a • 𝟙 A))), comp_zero, Preadditive.comp_nsmul,
    Category.comp_id, ← Category.id_comp (cokernel.π (kernel.ι (a • 𝟙 A))),
    ← Preadditive.nsmul_comp]
  exact hzero

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- `Ext` from `X` into an object whose identity vanishes is a subsingleton. -/
lemma subsingleton_ext_of_id_eq_zero [HasExt.{w} C] (X : C) {A : C} (h : 𝟙 A = 0) (n : ℕ) :
    Subsingleton (Ext.{w} X A n) := by
  have hx (z : Ext.{w} X A n) : z = 0 := by
    have hz := Ext.comp_mk₀_id (X := X) (Y := A) (n := n) z
    rwa [h, Ext.mk₀_zero, Ext.comp_zero, eq_comm] at hz
  exact ⟨fun x y => (hx x).trans (hx y).symm⟩

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- An additive functor carries an object whose identity vanishes to one whose identity
vanishes. -/
lemma id_map_eq_zero_of_id_eq_zero {A : C} (h : 𝟙 A = 0) : 𝟙 (F.obj A) = 0 := by
  rw [← F.map_id A, h, F.map_zero]

attribute [local instance] HasDerivedCategory.standard

/-- An exact functor is bijective on `Ext` into an object whose identity vanishes, in every
degree. -/
lemma isBijectiveOnExt_of_id_eq_zero (X : C) {A : C} (h : 𝟙 A = 0) (n : ℕ) :
    IsBijectiveOnExt F X A n := by
  have hC := HasExt.standard C
  have hD := HasExt.standard D
  have h₁ := subsingleton_ext_of_id_eq_zero X h n
  have h₂ := subsingleton_ext_of_id_eq_zero (F.obj X) (id_map_eq_zero_of_id_eq_zero F h) n
  exact (mapExt_bijective_iff_mapDerivedCategory F X A n).mp ⟨fun x y _ => h₁.elim x y,
    fun y => ⟨0, h₂.elim _ _⟩⟩

/-- If `F` is bijective on `Ext` from `X` into every object killed by `a` and into every object
killed by `b`, then it is bijective on `Ext` from `X` into every object killed by `a * b`. -/
private theorem isBijectiveOnExt_of_mul_nsmul_id_eq_zero (X : C) {a b : ℕ}
    (ha : ∀ A : C, a • 𝟙 A = 0 → ∀ n, IsBijectiveOnExt F X A n)
    (hb : ∀ A : C, b • 𝟙 A = 0 → ∀ n, IsBijectiveOnExt F X A n)
    {A : C} (hA : (a * b) • 𝟙 A = 0) (n : ℕ) : IsBijectiveOnExt F X A n :=
  isBijectiveOnExt_of_shortExact F X (kernelQuotientShortComplex_shortExact (a • 𝟙 A))
    (ha _ (nsmul_id_kernel_eq_zero A a)) (hb _ (nsmul_id_cokernel_eq_zero A a b hA)) n

/-- If an exact functor `F` is bijective on `Ext` from `X` into every object killed by `a`, in
every degree, then it is bijective on `Ext` from `X` into every object killed by a power of
`a`. -/
theorem isBijectiveOnExt_of_nsmul_id_eq_zero_of_pow (X : C) (a : ℕ)
    (h : ∀ A : C, a • 𝟙 A = 0 → ∀ n, IsBijectiveOnExt F X A n) :
    ∀ (k : ℕ) (A : C), a ^ k • 𝟙 A = 0 → ∀ n, IsBijectiveOnExt F X A n := by
  intro k
  induction k with
  | zero => exact fun A hA n ↦ isBijectiveOnExt_of_id_eq_zero F X (by simpa using hA) n
  | succ k ih =>
    intro A hA n
    exact isBijectiveOnExt_of_mul_nsmul_id_eq_zero F X h ih (by rwa [← pow_succ']) n

/-- If an exact functor `F` is bijective on `Ext` from `X` into every object killed by a prime,
in every degree, then it is bijective on `Ext` from `X` into every object killed by a positive
integer. -/
theorem isBijectiveOnExt_of_nsmul_id_eq_zero (X : C)
    (h : ∀ p : ℕ, p.Prime → ∀ A : C, p • 𝟙 A = 0 → ∀ n, IsBijectiveOnExt F X A n) :
    ∀ (m : ℕ), m ≠ 0 → ∀ A : C, m • 𝟙 A = 0 → ∀ n, IsBijectiveOnExt F X A n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm A hA n
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm) with hm1 | hm1
    · exact isBijectiveOnExt_of_id_eq_zero F X (by simpa [← hm1] using hA) n
    · have hp : m.minFac.Prime := Nat.minFac_prime (by omega)
      obtain ⟨b, hb⟩ := Nat.ordProj_dvd m m.minFac
      have hbne : b ≠ 0 := right_ne_zero_of_mul (hb ▸ hm)
      have hblt : b < m := hb ▸ lt_mul_left (Nat.pos_of_ne_zero hbne)
        (Nat.one_lt_pow (hp.factorization_pos_of_dvd hm (Nat.minFac_dvd m)).ne' hp.one_lt)
      exact isBijectiveOnExt_of_mul_nsmul_id_eq_zero F X
        (isBijectiveOnExt_of_nsmul_id_eq_zero_of_pow F X m.minFac (h _ hp)
          (m.factorization m.minFac)) (ih b hblt hbne) (by rwa [← hb]) n

end Annihilated

section Geometric

attribute [local instance] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- Let `f : X ⟶ Y` be a morphism of schemes. If restriction along `f` is bijective on étale
cohomology, in every degree, for every abelian étale sheaf on `Y` killed by a prime, then it is
bijective in every degree for every abelian étale sheaf killed by a positive integer. -/
theorem etaleCohomologyRestrictionMap_bijective_of_nsmul_id_eq_zero
    (h : ∀ p : ℕ, p.Prime →
      ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}, p • 𝟙 G = 0 →
        ∀ q, Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f G q))
    (m : ℕ) (hm : m ≠ 0)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (hF : m • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} f F q) :=
  (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w} f F q).mpr
    (isBijectiveOnExt_of_nsmul_id_eq_zero (etaleAbelianInverseImage.{u, v} f) _
      (fun p hp G hG r =>
        (etaleCohomologyRestrictionMap_bijective_iff_isBijectiveOnExt.{u, v, w} f G r).mp
          (h p hp G hG r))
      m hm F hF q)

end Geometric

end Stacks.EtaleCohomology

end
