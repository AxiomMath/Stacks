module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.Combinatorics.Quiver.ReflQuiver

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Inverse systems of `f`-torsion and of quotients by powers of `f`

Let `R` be a sheaf of rings on a site and let `f : End (𝟭 (SheafOfModules R))` be an
endomorphism of the identity functor; for the sheaf of rings of a ringed space `(X, 𝒪_X)` and a
global section `f ∈ Γ(X, 𝒪_X)` this is multiplication by `f`, which is `𝒪_X`-linear and commutes
with every module homomorphism. For an inverse system `… → ℱ₃ → ℱ₂ → ℱ₁` of modules the
following conditions are compared:

1. multiplication by `f` on `ℱ_{n+1}` factors as `ℱ_{n+1} → ℱ_n → ℱ_{n+1}` through the
   transition map, and `0 → ℱ_n → ℱ_{n+1} → ℱ₁ → 0` is short exact;
2. multiplication by `f^n` on `ℱ_{n+1}` factors as `ℱ_{n+1} → ℱ₁ → ℱ_{n+1}`, and
   `0 → ℱ₁ → ℱ_{n+1} → ℱ_n → 0` is short exact;
3. there is an `f`-divisible module `G` with `ℱ_n ≅ G[f^n]` compatibly with the transition maps,
   the transition maps of `G[f^•]` being multiplication by `f`;
4. there is an `f`-torsion free module `M` with `ℱ_n ≅ M/f^nM` compatibly with the transition
   maps, the transition maps of `M/f^•M` being the canonical surjections.

Then `(1) ⇔ (2) ⇔ (3)` and `(4) ⇒ (3)`.

## Main definitions

* `IsTorsionFree`, `IsDivisible`: multiplication by `f` is a monomorphism, an epimorphism.
* `torsionSub`, `powQuotient`: the kernel `M[f^n]` and the cokernel `M/f^nM` of `f^n`.
* `Condition1`, `Condition2`, `Condition3`, `Condition4`: the four conditions above.

## Main results

* `stacks0H39_one_iff_two`: `(1) ⇔ (2)`.
* `stacks0H39_two_iff_three`: `(2) ⇔ (3)`.
* `stacks0H39_four_imp_three`: `(4) ⇒ (3)`.

## Implementation notes

The inverse system is `0`-indexed: `obj : ℕ → SheafOfModules R` with `obj k = ℱ_{k+1}` and
transition maps `map k : obj (k + 1) ⟶ obj k`, so a condition stated for all `n ≥ 1` becomes a
condition for all `k : ℕ` with `n = k + 1`. The cokernel `coker(f^n)` is used for `M/f^nM`; it
agrees with the cokernel of the inclusion of the image `f^nM`.
-/

open CategoryTheory Limits

/- The "third isomorphism" short exact sequence for a composable pair of monomorphisms
`b : Y ⟶ X`, `a : X ⟶ Z` in an abelian category: `0 → coker b → coker (b ≫ a) → coker a → 0`.
The left map is induced by `a`, the right map is the canonical surjection. -/
namespace CokSES

open CategoryTheory.Abelian.Pseudoelement

variable {D : Type*} [Category D] [Abelian D]

/-- The map `coker b → coker (b ≫ a)` induced by `a`. -/
noncomputable def jmap {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) :
    cokernel b ⟶ cokernel (b ≫ a) := cokernel.map b (b ≫ a) (𝟙 Y) a (by simp)

/-- The canonical surjection `coker (b ≫ a) → coker a`. -/
noncomputable def canmap {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) :
    cokernel (b ≫ a) ⟶ cokernel a :=
  cokernel.desc _ (cokernel.π a) (by rw [Category.assoc, cokernel.condition, comp_zero])

/-- `π_b ≫ jmap b a = a ≫ π_{b ≫ a}`. -/
theorem jmap_pi {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) :
    cokernel.π b ≫ jmap b a = a ≫ cokernel.π (b ≫ a) := by simp [jmap, cokernel.map]

/-- `π_{b ≫ a} ≫ canmap b a = π_a`. -/
theorem canmap_pi {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) :
    cokernel.π (b ≫ a) ≫ canmap b a = cokernel.π a := by simp [canmap]

/-- The composite `coker b → coker (b ≫ a) → coker a` is zero. -/
theorem jmap_canmap {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) : jmap b a ≫ canmap b a = 0 := by
  apply (cancel_epi (cokernel.π b)).1
  rw [← Category.assoc, jmap_pi, Category.assoc, canmap_pi, comp_zero, cokernel.condition]

/-- `canmap b a` is an epimorphism. -/
theorem epi_canmap {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) : Epi (canmap b a) :=
  epi_of_epi_fac (canmap_pi b a)

/-- If `a` is a monomorphism then so is `jmap b a`. -/
theorem mono_jmap {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) [Mono a] : Mono (jmap b a) := by
  apply mono_of_zero_of_map_zero
  intro x hx
  obtain ⟨m, rfl⟩ := pseudo_surjective_of_epi (cokernel.π b) x
  rw [← Abelian.Pseudoelement.comp_apply, jmap_pi, Abelian.Pseudoelement.comp_apply] at hx
  obtain ⟨y, hy⟩ := pseudo_exact_of_exact (ShortComplex.exact_cokernel (b ≫ a)) (pseudoApply a m) hx
  rw [Abelian.Pseudoelement.comp_apply] at hy
  have hbym : pseudoApply b y = m := pseudo_injective_of_mono a hy
  rw [← hbym, ← Abelian.Pseudoelement.comp_apply, cokernel.condition]; exact zero_apply _ _

/-- `canmap` is the cokernel of `jmap`. -/
noncomputable def canIsCokernel {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) :
    IsColimit (CokernelCofork.ofπ (canmap b a) (jmap_canmap b a)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {W} t ht => cokernel.desc a (cokernel.π (b ≫ a) ≫ t) (by
        rw [← Category.assoc, ← jmap_pi, Category.assoc, ht, comp_zero]))
    (fun {W} t ht => by
        apply (cancel_epi (cokernel.π (b ≫ a))).1; rw [← Category.assoc, canmap_pi]; simp)
    (fun {W} t ht m hm => by
        have := epi_canmap b a
        apply (cancel_epi (canmap b a)).1; rw [hm]; symm
        apply (cancel_epi (cokernel.π (b ≫ a))).1; rw [← Category.assoc, canmap_pi]; simp)

/-- The third-isomorphism short exact sequence for composable monos. -/
theorem compMono_shortExact {Y X Z : D} (b : Y ⟶ X) (a : X ⟶ Z) [Mono a] [Mono (b ≫ a)] :
    (ShortComplex.mk (jmap b a) (canmap b a) (jmap_canmap b a)).ShortExact := by
  have := mono_jmap b a; have := epi_canmap b a
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (canIsCokernel b a))
    (mono_jmap b a) (epi_canmap b a)

end CokSES

/- The dual "third isomorphism" short exact sequence for a composable pair of epimorphisms
`a : W ⟶ X`, `b : X ⟶ Y` in an abelian category: `0 → ker a → ker (a ≫ b) → ker b → 0`.
The left map is the canonical inclusion, the right map is induced by `a`. -/
namespace KerSES

open CategoryTheory.Abelian.Pseudoelement

variable {D : Type*} [Category D] [Abelian D]

/-- The canonical inclusion `ker a → ker (a ≫ b)`. -/
noncomputable def kincl {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) :
    kernel a ⟶ kernel (a ≫ b) :=
  kernel.lift (a ≫ b) (kernel.ι a) (by rw [← Category.assoc, kernel.condition, zero_comp])

/-- The map `ker (a ≫ b) → ker b` induced by `a`. -/
noncomputable def kjmap {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) :
    kernel (a ≫ b) ⟶ kernel b :=
  kernel.lift b (kernel.ι (a ≫ b) ≫ a) (by rw [Category.assoc, kernel.condition])

/-- `kincl a b ≫ ι_{a ≫ b} = ι_a`. -/
theorem ι_kincl {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) :
    kincl a b ≫ kernel.ι (a ≫ b) = kernel.ι a := by simp [kincl]

/-- `kjmap a b ≫ ι_b = ι_{a ≫ b} ≫ a`. -/
theorem ι_kjmap {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) :
    kjmap a b ≫ kernel.ι b = kernel.ι (a ≫ b) ≫ a := by simp [kjmap]

/-- The composite `ker a → ker (a ≫ b) → ker b` is zero. -/
theorem kincl_kjmap {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) : kincl a b ≫ kjmap a b = 0 := by
  apply (cancel_mono (kernel.ι b)).1
  rw [Category.assoc, ι_kjmap, ← Category.assoc, ι_kincl, kernel.condition, zero_comp]

/-- `kincl a b` is a monomorphism. -/
theorem mono_kincl {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) : Mono (kincl a b) :=
  mono_of_mono_fac (ι_kincl a b)

/-- If `a` is an epimorphism then so is `kjmap a b`. -/
theorem epi_kjmap {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) [Epi a] : Epi (kjmap a b) := by
  apply epi_of_pseudo_surjective
  intro y
  obtain ⟨x, hx⟩ := pseudo_surjective_of_epi a (pseudoApply (kernel.ι b) y)
  have hab : pseudoApply (a ≫ b) x = 0 := by
    rw [Abelian.Pseudoelement.comp_apply, hx, ← Abelian.Pseudoelement.comp_apply,
      kernel.condition, Abelian.Pseudoelement.zero_apply]
  obtain ⟨x', hx'⟩ := pseudo_exact_of_exact (ShortComplex.exact_kernel (a ≫ b)) x hab
  refine ⟨x', ?_⟩
  apply pseudo_injective_of_mono (kernel.ι b)
  rw [← Abelian.Pseudoelement.comp_apply, ι_kjmap, Abelian.Pseudoelement.comp_apply, hx', hx]

/-- `kincl` is the kernel of `kjmap`. -/
noncomputable def kinclIsKernel {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) :
    IsLimit (KernelFork.ofι (kincl a b) (kincl_kjmap a b)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {T} t ht => kernel.lift a (t ≫ kernel.ι (a ≫ b)) (by
        rw [Category.assoc, ← ι_kjmap, ← Category.assoc, ht, zero_comp]))
    (fun {T} t ht => by
        apply (cancel_mono (kernel.ι (a ≫ b))).1
        rw [Category.assoc, ι_kincl]; simp)
    (fun {T} t ht m hm => by
        have := mono_kincl a b
        apply (cancel_mono (kincl a b)).1; rw [hm]; symm
        apply (cancel_mono (kernel.ι (a ≫ b))).1
        rw [Category.assoc, ι_kincl]; simp)

/-- The third-isomorphism short exact sequence for composable epis. -/
theorem compEpi_shortExact {W X Y : D} (a : W ⟶ X) (b : X ⟶ Y) [Epi a] [Epi (a ≫ b)] :
    (ShortComplex.mk (kincl a b) (kjmap a b) (kincl_kjmap a b)).ShortExact := by
  have := mono_kincl a b; have := epi_kjmap a b
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kinclIsKernel a b))
    (mono_kincl a b) (epi_kjmap a b)

end KerSES

namespace Stacks.Cohomology.InverseSystems.TorsionFreeDivisible

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A module `M` is `f`-torsion free if multiplication by `f` is a monomorphism. -/
def IsTorsionFree (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R) :
    Prop :=
  Mono (f.asHom.app M)

/-- A module `M` is `f`-divisible if multiplication by `f` is an epimorphism. -/
def IsDivisible (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R) : Prop
    :=
  Epi (f.asHom.app M)

/-- The submodule `M[f^n] = ker(f^n : M → M)`. -/
noncomputable def torsionSub (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u
    v} R) (n : ℕ) :
    SheafOfModules.{max u v} R :=
  kernel ((f ^ n).asHom.app M)

/-- The quotient `M / f^n M`, realised as `coker(f^n : M → M)`. -/
noncomputable def powQuotient (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u
    v} R) (n : ℕ) :
    SheafOfModules.{max u v} R :=
  cokernel ((f ^ n).asHom.app M)

/-- The composite transition map `obj k ⟶ obj 0`, i.e. the informal iterated transition
`ℱ_{k+1} → ℱ₁`. -/
def proj (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    ∀ k, obj k ⟶ obj 0
  | 0 => 𝟙 _
  | (k + 1) => map k ≫ proj obj map k

/-- Multiplication by `f` and by `f^n` compose to multiplication by `f^{n+1}`. -/
theorem mulF_pow_succ (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R)
    (n : ℕ) :
    f.asHom.app M ≫ (f ^ n).asHom.app M = (f ^ (n + 1)).asHom.app M := by
  rw [pow_succ, End.mul_asHom, NatTrans.comp_app]

/-- Naturality of multiplication by `f`: it commutes with every module homomorphism. -/
theorem mulF_naturality (f : End (𝟭 (SheafOfModules.{max u v} R)))
    {A B : SheafOfModules.{max u v} R} (g : A ⟶ B) :
    f.asHom.app A ≫ g = g ≫ f.asHom.app B := by
  simpa using (f.asHom.naturality g).symm

/-- Multiplication by `f` sends `G[f^{n+1}]` into `G[f^n]`; this is the transition map
`G[f^{n+1}] ⟶ G[f^n]` of the torsion submodules. -/
noncomputable def kernelToKernelMulF (f : End (𝟭 (SheafOfModules.{max u v} R))) (G :
    SheafOfModules.{max u v} R)
    (n : ℕ) : torsionSub f G (n + 1) ⟶ torsionSub f G n :=
  kernel.lift _ (kernel.ι _ ≫ f.asHom.app G) (by
    have h : kernel.ι ((f ^ (n + 1)).asHom.app G) ≫ (f ^ (n + 1)).asHom.app G = 0 :=
      kernel.condition _
    rw [Category.assoc, mulF_pow_succ]
    exact h)

/-- The canonical surjection `M / f^{n+1} M → M / f^n M`. -/
noncomputable def quotientToQuotient (f : End (𝟭 (SheafOfModules.{max u v} R))) (M :
    SheafOfModules.{max u v} R)
    (n : ℕ) : powQuotient f M (n + 1) ⟶ powQuotient f M n :=
  cokernel.desc _ (cokernel.π _) (by
    have h : (f ^ n).asHom.app M ≫ cokernel.π ((f ^ n).asHom.app M) = 0 := cokernel.condition _
    rw [← mulF_pow_succ, Category.assoc, h, comp_zero])

/-- Condition (1): for every `n ≥ 1` (here `n = k+1`), multiplication by `f` on `ℱ_{n+1}`
(`= obj (k+1)`) factors through the transition map `π_n` (`= map k`) via a map
`ι : ℱ_n → ℱ_{n+1}` (`ι : obj k ⟶ obj (k+1)`) satisfying `map k ≫ ι = f`, and the resulting
data form a short exact sequence `0 → ℱ_n → ℱ_{n+1} → ℱ₁ → 0`, i.e.
`0 → obj k → obj (k+1) → obj 0 → 0`, where the last map is the iterated transition. -/
def Condition1 (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) : Prop :=
  ∀ k : ℕ, ∃ (ι : obj k ⟶ obj (k + 1)) (w : ι ≫ proj obj map (k + 1) = 0),
    (map k ≫ ι = f.asHom.app (obj (k + 1))) ∧
      (ShortComplex.mk ι (proj obj map (k + 1)) w).ShortExact

/-- Condition (2): for every `n ≥ 1` (here `n = k+1`), multiplication by `f^n` on `ℱ_{n+1}`
(`= obj (k+1)`) factors through the iterated transition `ℱ_{n+1} → ℱ₁` (`proj (k+1)`) via a
map `j : ℱ₁ → ℱ_{n+1}` (`j : obj 0 ⟶ obj (k+1)`) satisfying `proj (k+1) ≫ j = f^{k+1}`,
and the resulting data form a short exact sequence `0 → ℱ₁ → ℱ_{n+1} → ℱ_n → 0`, i.e.
`0 → obj 0 → obj (k+1) → obj k → 0`, with the last map the transition `map k`. -/
def Condition2 (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) : Prop :=
  ∀ k : ℕ, ∃ (j : obj 0 ⟶ obj (k + 1)) (w : j ≫ map k = 0),
    (proj obj map (k + 1) ≫ j = (f ^ (k + 1)).asHom.app (obj (k + 1))) ∧
      (ShortComplex.mk j (map k) w).ShortExact

/-- Condition (3): there is an `f`-divisible module `G` and isomorphisms `obj n ≅ G[f^{n+1}]`
(recall `obj n = ℱ_{n+1}`) under which the transition map `map n` corresponds to the map
`G[f^{n+2}] → G[f^{n+1}]` induced by multiplication by `f`. -/
def Condition3 (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) : Prop :=
  ∃ (G : SheafOfModules.{max u v} R) (_ : IsDivisible f G)
    (e : ∀ n, obj n ≅ torsionSub f G (n + 1)),
    ∀ n : ℕ, (e (n + 1)).hom ≫ kernelToKernelMulF f G (n + 1) = map n ≫ (e n).hom

/-- Condition (4): there is an `f`-torsion-free module `M` and isomorphisms
`obj n ≅ M / f^{n+1} M` (recall `obj n = ℱ_{n+1}`), compatible with the transition maps,
where the transition map on the quotient side is the canonical surjection
`M/f^{n+2}M → M/f^{n+1}M`. -/
def Condition4 (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) : Prop :=
  ∃ (M : SheafOfModules.{max u v} R) (_ : IsTorsionFree f M)
    (e : ∀ n, obj n ≅ powQuotient f M (n + 1)),
    ∀ n : ℕ, (e (n + 1)).hom ≫ quotientToQuotient f M (n + 1) = map n ≫ (e n).hom

/-- The iterated composite `ι₀ ≫ ι₁ ≫ … ≫ ι_{k-1} : obj 0 ⟶ obj k` of maps
`ι n : obj n ⟶ obj (n + 1)`. -/
def upComp (obj : ℕ → SheafOfModules.{max u v} R)
    (ι : ∀ n, obj n ⟶ obj (n + 1)) : ∀ k, obj 0 ⟶ obj k
  | 0 => 𝟙 _
  | (k + 1) => upComp obj ι k ≫ ι k

/-- If `map n ≫ ι n = f` for all `n`, the iterated transition `proj (k + 1)` followed by the
iterated composite `upComp (k + 1)` of the `ι n` is `f^{k+1}`. -/
theorem proj_upComp (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n)
    (ι : ∀ n, obj n ⟶ obj (n + 1)) (hf : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1))) :
    ∀ k, proj obj map (k + 1) ≫ upComp obj ι (k + 1) = (f ^ (k + 1)).asHom.app (obj (k + 1)) := by
  intro k
  induction k with
  | zero =>
    simp only [proj, upComp, Category.comp_id, Category.id_comp]
    rw [hf 0]
    simp [pow_one]
  | succ k ih =>
    simp only [proj, upComp]
    calc (map (k + 1) ≫ proj obj map (k + 1)) ≫ upComp obj ι (k + 1) ≫ ι (k + 1)
        = map (k + 1) ≫ (proj obj map (k + 1) ≫ upComp obj ι (k + 1)) ≫ ι (k + 1) := by
            simp only [Category.assoc]
      _ = map (k + 1) ≫ (f ^ (k + 1)).asHom.app (obj (k + 1)) ≫ ι (k + 1) := by rw [ih]
      _ = map (k + 1) ≫ ι (k + 1) ≫ (f ^ (k + 1)).asHom.app (obj (k + 2)) := by
            rw [mulF_naturality]
      _ = (map (k + 1) ≫ ι (k + 1)) ≫ (f ^ (k + 1)).asHom.app (obj (k + 2)) := by
            rw [Category.assoc]
      _ = f.asHom.app (obj (k + 2)) ≫ (f ^ (k + 1)).asHom.app (obj (k + 2)) := by rw [hf (k + 1)]
      _ = (f ^ (k + 2)).asHom.app (obj (k + 2)) := mulF_pow_succ f (obj (k + 2)) (k + 1)

/-! ## The implications between the four conditions -/

/-- The iterated transition `proj 1` is the first transition map. -/
private theorem proj_one {obj : ℕ → SheafOfModules.{max u v} R}
    {map : ∀ n, obj (n + 1) ⟶ obj n} : proj obj map 1 = map 0 := by simp [proj]

/-- If `p ≫ i` is multiplication by `f` and `i` is a monomorphism, so is `i ≫ p`. -/
private theorem comp_eq_mulF_of_mono (f : End (𝟭 (SheafOfModules.{max u v} R)))
    {A B : SheafOfModules.{max u v} R} (p : B ⟶ A) (i : A ⟶ B) (hi : Mono i)
    (h : p ≫ i = f.asHom.app B) : i ≫ p = f.asHom.app A := by
  have := hi
  apply (cancel_mono i).1
  rw [Category.assoc, h, ← mulF_naturality]

open CategoryTheory.Abelian.Pseudoelement in
/-- `(1) ⇒ (2)`: if the maps `ι n` witness condition (1), then the iterated composite
`upComp obj ι (k + 1) : obj 0 ⟶ obj (k + 1)` witnesses condition (2). -/
theorem stacks0H39_one_imp_two
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    Condition1 f obj map → Condition2 f obj map := by
  intro h1
  choose ι w hf S using h1
  have hmono : ∀ m, Mono (ι m) := fun m => (S m).mono_f
  have hιmap : ∀ m, ι m ≫ map m = f.asHom.app (obj m) := fun m =>
    comp_eq_mulF_of_mono f (map m) (ι m) (hmono m) (hf m)
  have hf0 : f.asHom.app (obj 0) = 0 := by
    rw [← hιmap 0]
    simpa [proj] using w 0
  have hepiAll : ∀ m, Epi (map m) := by
    intro m
    induction m with
    | zero =>
        simpa [proj_one] using (S 0).epi_g
    | succ m ih =>
        have := ih; have := hmono m; have := hmono (m + 1)
        apply Preadditive.epi_of_cokernel_zero
        set π : obj (m + 1) ⟶ cokernel (map (m + 1)) := cokernel.π (map (m + 1)) with hπ
        have hstar : map m ≫ ι m = ι (m + 1) ≫ map (m + 1) := by rw [hf m, hιmap (m + 1)]
        have hιπ : ι m ≫ π = 0 := by
          apply (cancel_epi (map m)).1
          rw [← Category.assoc, hstar, Category.assoc, hπ, cokernel.condition, comp_zero,
            comp_zero]
        obtain ⟨ψ, hψ⟩ := CokernelCofork.IsColimit.desc' (S m).gIsCokernel π hιπ
        have hψ' : proj obj map (m + 1) ≫ ψ = π := hψ
        have hepiP2 : Epi (proj obj map (m + 2)) := (S (m + 1)).epi_g
        have hψ0 : ψ = 0 := by
          have hpc : proj obj map (m + 2) = map (m + 1) ≫ proj obj map (m + 1) := rfl
          apply (cancel_epi (proj obj map (m + 2))).1
          rw [comp_zero, hpc, Category.assoc, hψ', hπ, cokernel.condition]
        rw [← hψ', hψ0, comp_zero]
  intro k
  have hepiP : Epi (proj obj map (k + 1)) := (S k).epi_g
  have hepimap : Epi (map k) := hepiAll k
  have hmonoUp : ∀ m, Mono (upComp obj ι m) := by
    intro m
    induction m with
    | zero => change Mono (𝟙 _); infer_instance
    | succ m ih =>
        have := ih; have := hmono m
        change Mono (upComp obj ι m ≫ ι m); infer_instance
  have hmonoJ : Mono (upComp obj ι (k + 1)) := hmonoUp (k + 1)
  have hex : ∀ m (c : Abelian.Pseudoelement (obj m)),
      pseudoApply (f.asHom.app (obj m)) c = 0 → ∃ a, pseudoApply (upComp obj ι m) a = c := by
    intro m
    induction m with
    | zero =>
        intro c _
        obtain ⟨a, ha⟩ := pseudo_surjective_of_epi (𝟙 (obj 0)) c
        exact ⟨a, by rw [upComp]; exact ha⟩
    | succ m ih =>
        intro c hc
        have := hmono m
        have hmc : pseudoApply (map m) c = 0 := by
          apply pseudo_injective_of_mono (ι m)
          rw [← Abelian.Pseudoelement.comp_apply, hf m, hc]; simp
        have hpc : pseudoApply (proj obj map (m + 1)) c = 0 := by
          have : proj obj map (m + 1) = map m ≫ proj obj map m := rfl
          rw [this, Abelian.Pseudoelement.comp_apply, hmc]; simp
        obtain ⟨d, hd⟩ := pseudo_exact_of_exact (S m).exact c hpc
        have hfd : pseudoApply (f.asHom.app (obj m)) d = 0 := by
          rw [← hιmap m, Abelian.Pseudoelement.comp_apply, hd, hmc]
        obtain ⟨a, ha⟩ := ih d hfd
        refine ⟨a, ?_⟩
        rw [upComp, Abelian.Pseudoelement.comp_apply, ha, hd]
  refine ⟨upComp obj ι (k + 1), ?_, ?_, ?_⟩
  · rw [upComp, Category.assoc, hιmap k, ← mulF_naturality, hf0, zero_comp]
  · exact proj_upComp f obj map ι hf k
  · apply ShortComplex.ShortExact.mk'
    · apply exact_of_pseudo_exact
      intro b hb
      have hpb : pseudoApply (proj obj map (k + 1)) b = 0 := by
        have : proj obj map (k + 1) = map k ≫ proj obj map k := rfl
        rw [this, Abelian.Pseudoelement.comp_apply, hb]; simp
      obtain ⟨c, hc⟩ := pseudo_exact_of_exact (S k).exact b hpb
      have hfc : pseudoApply (f.asHom.app (obj k)) c = 0 := by
        rw [← hιmap k, Abelian.Pseudoelement.comp_apply, hc, hb]
      obtain ⟨a, ha⟩ := hex k c hfc
      refine ⟨a, ?_⟩
      change pseudoApply (upComp obj ι (k + 1)) a = b
      rw [upComp, Abelian.Pseudoelement.comp_apply, ha, hc]
    · exact hmonoJ
    · exact hepimap

open CategoryTheory.Abelian.Pseudoelement in
/-- `(2) ⇒ (1)`: multiplication by `f` on `obj (k + 1)` kills the image of the map
`obj 0 ⟶ obj (k + 1)` of condition (2), so it factors through `map k`, and the factorization
witnesses condition (1). -/
theorem stacks0H39_two_imp_one
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    Condition2 f obj map → Condition1 f obj map := by
  classical
  intro h2
  choose j w hf T using h2
  have hmonoj : ∀ m, Mono (j m) := fun m => (T m).mono_f
  have hepimap : ∀ m, Epi (map m) := fun m => (T m).epi_g
  have hf0base : map 0 ≫ j 0 = f.asHom.app (obj 1) := by
    simpa [proj_one] using hf 0
  have hf0 : f.asHom.app (obj 0) = 0 := by
    have hnat : f.asHom.app (obj 0) ≫ j 0 = j 0 ≫ f.asHom.app (obj 1) := mulF_naturality f (j 0)
    have := hmonoj 0
    apply (cancel_mono (j 0)).1
    rw [zero_comp, hnat, ← hf0base, ← Category.assoc, w 0, zero_comp]
  have hjf : ∀ m, j m ≫ f.asHom.app (obj (m + 1)) = 0 := by
    intro m
    rw [← mulF_naturality, hf0, zero_comp]
  have hιdesc : ∀ m, ∃ (ι : obj m ⟶ obj (m + 1)), map m ≫ ι = f.asHom.app (obj (m + 1)) := by
    intro m
    obtain ⟨ι, hι⟩ := CokernelCofork.IsColimit.desc' (T m).gIsCokernel
      (f.asHom.app (obj (m + 1))) (hjf m)
    exact ⟨ι, hι⟩
  choose ι hfι using hιdesc
  have hιproj : ∀ m, ι m ≫ proj obj map (m + 1) = 0 := by
    intro m
    have := hepimap m
    apply (cancel_epi (map m)).1
    rw [comp_zero, ← Category.assoc, hfι m]
    rw [mulF_naturality, hf0, comp_zero]
  have hepiAll : ∀ m, Epi (proj obj map (m + 1)) := by
    intro m
    induction m with
    | zero =>
        rw [proj_one]; exact hepimap 0
    | succ m ih =>
        have := ih; have := hepimap (m + 1)
        have hp : proj obj map (m + 2) = map (m + 1) ≫ proj obj map (m + 1) := rfl
        rw [hp]; exact epi_comp _ _
  have hιmap : ∀ m, ι m ≫ map m = f.asHom.app (obj m) := by
    intro m
    have := hepimap m
    apply (cancel_epi (map m)).1
    rw [← Category.assoc, hfι m, mulF_naturality]
  have hι0 : ι 0 = j 0 := by
    have := hepimap 0
    apply (cancel_epi (map 0)).1
    rw [hfι 0, hf0base]
  have hjι : ∀ m, j (m + 1) = j m ≫ ι (m + 1) := by
    intro m
    have := hepiAll (m + 1)
    apply (cancel_epi (proj obj map (m + 2))).1
    rw [hf (m + 1)]
    have hpc : proj obj map (m + 2) = map (m + 1) ≫ proj obj map (m + 1) := rfl
    rw [hpc, ← Category.assoc, Category.assoc (map (m + 1)), hf m, Category.assoc,
      mulF_naturality (f ^ (m + 1)) (ι (m + 1)), ← Category.assoc, hfι (m + 1),
      mulF_pow_succ]
  have hker : ∀ m (c : Abelian.Pseudoelement (obj (m + 1))),
      pseudoApply (f.asHom.app (obj (m + 1))) c = 0 → ∃ a, pseudoApply (j m) a = c := by
    intro m
    induction m with
    | zero =>
        intro c hc
        have := hmonoj 0
        have hmc : pseudoApply (map 0) c = 0 := by
          apply pseudo_injective_of_mono (j 0)
          rw [← Abelian.Pseudoelement.comp_apply, hf0base, hc]; simp
        obtain ⟨a, ha⟩ := pseudo_exact_of_exact (T 0).exact c hmc
        exact ⟨a, ha⟩
    | succ m ih =>
        intro c hc
        have := hmonoj (m + 1)
        have hfmc : pseudoApply (f.asHom.app (obj (m + 1))) (pseudoApply (map (m + 1)) c) = 0 := by
          rw [← Abelian.Pseudoelement.comp_apply, ← mulF_naturality f (map (m + 1)),
            Abelian.Pseudoelement.comp_apply, hc]; simp
        obtain ⟨b, hb⟩ := ih (pseudoApply (map (m + 1)) c) hfmc
        have hjb : pseudoApply (j (m + 1)) b = 0 := by
          rw [hjι m, Abelian.Pseudoelement.comp_apply, hb,
            ← Abelian.Pseudoelement.comp_apply, hfι (m + 1), hc]
        have hb0 : b = 0 := by
          have := hmonoj (m + 1)
          apply pseudo_injective_of_mono (j (m + 1))
          rw [hjb]; simp
        have hmc : pseudoApply (map (m + 1)) c = 0 := by rw [← hb, hb0]; simp
        obtain ⟨a, ha⟩ := pseudo_exact_of_exact (T (m + 1)).exact c hmc
        exact ⟨a, ha⟩
  have hExact : ∀ m (x : Abelian.Pseudoelement (obj (m + 1))),
      pseudoApply (proj obj map (m + 1)) x = 0 → ∃ a, pseudoApply (ι m) a = x := by
    intro m
    induction m with
    | zero =>
        intro x hx
        rw [proj_one] at hx
        obtain ⟨a, ha⟩ := pseudo_exact_of_exact (T 0).exact x hx
        refine ⟨a, ?_⟩; rw [hι0]; exact ha
    | succ m ih =>
        intro x hx
        have := hepimap m; have := hepimap (m + 1)
        have hpm : pseudoApply (proj obj map (m + 1)) (pseudoApply (map (m + 1)) x) = 0 := by
          have hpc : proj obj map (m + 2) = map (m + 1) ≫ proj obj map (m + 1) := rfl
          rw [← Abelian.Pseudoelement.comp_apply, ← hpc, hx]
        obtain ⟨a', ha'⟩ := ih (pseudoApply (map (m + 1)) x) hpm
        obtain ⟨a, ham⟩ := pseudo_surjective_of_epi (map m) a'
        have heq : pseudoApply (map (m + 1)) (pseudoApply (ι (m + 1)) a)
            = pseudoApply (map (m + 1)) x := by
          rw [← Abelian.Pseudoelement.comp_apply, hιmap (m + 1),
            ← hfι m, Abelian.Pseudoelement.comp_apply, ham, ha']
        obtain ⟨z, hz0, hzuniv⟩ := sub_of_eq_image (map (m + 1)) x (pseudoApply (ι (m + 1)) a)
            heq.symm
        set π : obj (m + 2) ⟶ cokernel (ι (m + 1)) := cokernel.π (ι (m + 1)) with hπ
        have hπa : pseudoApply π (pseudoApply (ι (m + 1)) a) = 0 := by
          rw [← Abelian.Pseudoelement.comp_apply, hπ, cokernel.condition]; simp
        have hπzx : pseudoApply π z = pseudoApply π x := hzuniv _ π hπa
        obtain ⟨s, hs⟩ := pseudo_exact_of_exact (T (m + 1)).exact z hz0
        have hs' : pseudoApply (j (m + 1)) s = z := hs
        have hπz : pseudoApply π z = 0 := by
          rw [← hs', hjι m, Abelian.Pseudoelement.comp_apply,
            ← Abelian.Pseudoelement.comp_apply, hπ, cokernel.condition]; simp
        have hπx : pseudoApply π x = 0 := by rw [← hπzx, hπz]
        obtain ⟨a2, ha2⟩ := pseudo_exact_of_exact (ShortComplex.exact_cokernel (ι (m + 1))) x hπx
        exact ⟨a2, ha2⟩
  have hmonoι : ∀ m, Mono (ι m) := by
    intro m
    have := hepimap m
    apply mono_of_zero_of_map_zero
    intro a ha
    obtain ⟨y, hy⟩ := pseudo_surjective_of_epi (map m) a
    have hfy : pseudoApply (f.asHom.app (obj (m + 1))) y = 0 := by
      rw [← hfι m, Abelian.Pseudoelement.comp_apply, hy, ha]
    obtain ⟨t, ht⟩ := hker m y hfy
    rw [← hy, ← ht, ← Abelian.Pseudoelement.comp_apply, w m]; simp
  intro k
  have hepiP : Epi (proj obj map (k + 1)) := hepiAll k
  have := hmonoι k
  refine ⟨ι k, hιproj k, hfι k, ?_⟩
  apply ShortComplex.ShortExact.mk'
  · apply exact_of_pseudo_exact
    intro b hb
    exact hExact k b hb
  · exact hmonoι k
  · exact hepiP


/-! ### Sequential-colimit machinery for `(2) ⇒ (3)`

The hard direction `(2) ⇒ (3)` builds the `f`-divisible module `G := colim_k obj k`
along the "up" maps `ι` supplied by Condition1 (obtained from Condition2 via
`stacks0H39_two_imp_one`). This nested namespace packages that construction and isolates
the remaining obligations as named sub-lemmas. -/
namespace DivColim

variable {obj : ℕ → SheafOfModules.{max u v} R}

/-- The sequence functor `ℕ ⥤ SheafOfModules R` built from the up-maps `ι`. -/
noncomputable def seqF (ι : ∀ n, obj n ⟶ obj (n + 1)) : ℕ ⥤ SheafOfModules.{max u v} R :=
  Functor.ofSequence ι

/-- The colimit object `G = colim_k obj k`. -/
noncomputable def Gobj (ι : ∀ n, obj n ⟶ obj (n + 1)) : SheafOfModules.{max u v} R :=
  colimit (seqF ι)

/-- Colimit cocone legs `c_k : obj k ⟶ G`. -/
noncomputable def cleg (ι : ∀ n, obj n ⟶ obj (n + 1)) (k : ℕ) : obj k ⟶ Gobj ι :=
  (colimit.ι (seqF ι) k : (seqF ι).obj k ⟶ _)

/-- Cocone relation: `ι k ≫ c_{k+1} = c_k`. -/
theorem cleg_succ (ι : ∀ n, obj n ⟶ obj (n + 1)) (k : ℕ) :
    ι k ≫ cleg ι (k + 1) = cleg ι k := by
  have hw := colimit.w (seqF ι) (homOfLE (Nat.le_succ k))
  have hm : (seqF ι).map (homOfLE (Nat.le_succ k)) = ι k :=
    Functor.ofSequence_map_homOfLE_succ ι k
  rw [hm] at hw; exact hw

variable (f : End (𝟭 (SheafOfModules.{max u v} R)))
  (map : ∀ n, obj (n + 1) ⟶ obj n) (ι : ∀ n, obj n ⟶ obj (n + 1))

/-- Joint epimorphy of the colimit legs. -/
theorem cleg_hom_ext {T : SheafOfModules.{max u v} R} {p q : Gobj ι ⟶ T}
    (h : ∀ k, cleg ι k ≫ p = cleg ι k ≫ q) : p = q :=
  colimit.hom_ext h

/-- The colimit legs `c_k` are monomorphisms when every `ι k` is: a sequential colimit of
monomorphisms in the Grothendieck abelian category `SheafOfModules R` has monic legs. -/
theorem cleg_mono (ι : ∀ n, obj n ⟶ obj (n + 1)) (hmonoι : ∀ n, Mono (ι n)) (n : ℕ) :
    Mono (cleg ι n) := by
  have : AB5OfSize.{0,0} (AddCommGrpCat.{max u v}) :=
    AB5OfSize_of_univLE.{0,0,max u v, max u v} (AddCommGrpCat.{max u v})
  have hmaps : ∀ (i j : ℕ) (φ : i ⟶ j), Mono ((seqF ι).map φ) := by
    have : ∀ n, Mono (ι n) := hmonoι
    have key : ∀ (i j : ℕ) (hij : i ≤ j), Mono (Functor.OfSequence.map ι i j hij) := by
      intro i j hij
      induction j with
      | zero =>
        obtain rfl : i = 0 := Nat.le_zero.mp hij
        rw [Functor.OfSequence.map_id]; infer_instance
      | succ j ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h | h
        · have hij' : i ≤ j := Nat.lt_succ_iff.mp h
          rw [Functor.OfSequence.map_comp ι i j (j + 1) hij' (Nat.le_succ j),
              Functor.OfSequence.map_le_succ]
          have := ih hij'
          exact mono_comp _ _
        · subst h
          rw [Functor.OfSequence.map_id]; infer_instance
    intro i j φ
    exact key i j (leOfHom φ)
  have : HasExactColimitsOfShape (Under n) (PresheafOfModules.{max u v} R.obj) :=
    HasExactColimitsOfShape.domain_of_functor (Under n) (PresheafOfModules.toPresheaf R.obj)
  have : HasExactColimitsOfShape (Under n) (SheafOfModules.{max u v} R) :=
    Adjunction.hasExactColimitsOfShape
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) (Under n)
  exact IsColimit.mono_ι_app_of_isFiltered (colimit.isColimit (seqF ι)) n

/-- `map k ≫ c_k = c_{k+1} ≫ f.asHom.app G`. -/
theorem formulaA (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1))) (k : ℕ) :
    map k ≫ cleg ι k = cleg ι (k + 1) ≫ f.asHom.app (Gobj ι) := by
  have hnat : f.asHom.app (obj (k + 1)) ≫ cleg ι (k + 1) = cleg ι (k + 1) ≫ f.asHom.app (Gobj ι) :=
    mulF_naturality f (cleg ι (k + 1))
  rw [← hnat, ← hfι k, Category.assoc, cleg_succ ι k]

/-- The colimit `G` is `f`-divisible: `f.asHom.app G` is an epimorphism. -/
theorem epi_fappG (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hepi : ∀ n, Epi (map n)) : Epi (f.asHom.app (Gobj ι)) := by
  rw [Preadditive.epi_iff_cancel_zero]
  intro T p hp
  apply cleg_hom_ext (ι := ι)
  intro k
  have := hepi k
  rw [comp_zero]
  apply (cancel_epi (map k)).1
  rw [comp_zero, ← Category.assoc, formulaA f map ι hfι k, Category.assoc, hp, comp_zero]

/-- `f^{n+1}` acts as zero on `obj n = ℱ_{n+1}`, since `f` shifts the tower down one step and
`f` is zero on `obj 0 = ℱ₁`. -/
theorem vanishing (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n))
    (hf0 : f.asHom.app (obj 0) = 0) (n : ℕ) :
    (f ^ (n + 1)).asHom.app (obj n) = 0 := by
  have descent : ∀ (k s : ℕ),
      (f ^ (s + 1)).asHom.app (obj (k + 1)) = map k ≫ (f ^ s).asHom.app (obj k) ≫ ι k := by
    intro k s
    induction s with
    | zero =>
      rw [pow_one, ← hfι k, pow_zero]
      simp
    | succ s ih =>
      rw [← mulF_pow_succ f (obj (k + 1)) (s + 1), ih, ← hfι k]
      rw [Category.assoc, ← Category.assoc (ι k), hιmap k]
      rw [← mulF_pow_succ f (obj k) s]
      simp only [Category.assoc]
  induction n with
  | zero => rw [pow_one, hf0]
  | succ n ih =>
    rw [descent n (n + 1), ih, zero_comp, comp_zero]

/-- The leg `c_n` is killed by `f^{n+1}` on `G`. -/
theorem fpow_cleg_eq_zero (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hf0 : f.asHom.app (obj 0) = 0) (n : ℕ) :
    cleg ι n ≫ (f ^ (n + 1)).asHom.app (Gobj ι) = 0 := by
  have hnat : cleg ι n ≫ (f ^ (n + 1)).asHom.app (Gobj ι)
      = (f ^ (n + 1)).asHom.app (obj n) ≫ cleg ι n :=
    (mulF_naturality (f ^ (n + 1)) (cleg ι n)).symm
  rw [hnat, vanishing f map ι hfι hιmap hf0 n, zero_comp]

/-- The induced comparison `obj n ⟶ G[f^{n+1}] = ker((f^{n+1}).asHom.app G)`. -/
noncomputable def kerLift (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hf0 : f.asHom.app (obj 0) = 0) (n : ℕ) :
    obj n ⟶ torsionSub f (Gobj ι) (n + 1) :=
  kernel.lift _ (cleg ι n) (fpow_cleg_eq_zero f map ι hfι hιmap hf0 n)

/-- `kerLift n ≫ kernel.ι = c_n`. -/
theorem kerLift_ι (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hf0 : f.asHom.app (obj 0) = 0) (n : ℕ) :
    kerLift f map ι hfι hιmap hf0 n ≫ kernel.ι _ = cleg ι n := by
  simp [kerLift, torsionSub]

/-! ### Helpers for `kerLift_isIso` (the analytic kernel of `(2) ⇒ (3)`)

The proof that `kerLift n` is an isomorphism is via pseudoelements.
Mono is `mono_of_mono_fac` from `kerLift_ι` + `cleg_mono`.
Epi/surjectivity uses: (i) every pseudoelement of `G = colim obj` comes from some stage
(`cleg_pseudo_surjective`); (ii) `cleg` mono pushes the kernel condition to that stage;
(iii) `stabilization` says a stage element killed by `f^{n+1}` is in the image of the
iterated up-map `iterUp`; (iv) `iterUp_cleg` transports back to `cleg n`. -/

/-- Naturality of multiplication by `g^k`. -/
theorem powF_nat (g : End (𝟭 (SheafOfModules.{max u v} R))) (k : ℕ)
    {A B : SheafOfModules.{max u v} R} (φ : A ⟶ B) :
    (g ^ k).asHom.app A ≫ φ = φ ≫ (g ^ k).asHom.app B :=
  mulF_naturality (g ^ k) φ

/-- The iterated "up" composite `obj n ⟶ obj (n + r)`. -/
noncomputable def iterUp (ι : ∀ n, obj n ⟶ obj (n + 1)) (n : ℕ) :
    ∀ r, obj n ⟶ obj (n + r)
  | 0 => 𝟙 _
  | (r + 1) => iterUp ι n r ≫ ι (n + r)

/-- The cocone relation iterated: `iterUp ι n r ≫ c_{n+r} = c_n`. -/
theorem iterUp_cleg (ι : ∀ n, obj n ⟶ obj (n + 1)) (n : ℕ) :
    ∀ r, iterUp ι n r ≫ cleg ι (n + r) = cleg ι n := by
  intro r
  induction r with
  | zero => simp [iterUp]
  | succ r ih =>
    change iterUp ι n r ≫ ι (n + r) ≫ cleg ι ((n + r) + 1) = cleg ι n
    rw [cleg_succ ι (n + r), ih]

/-- `iterUp ι n r` is a mono (composite of the monos `ι`). -/
theorem iterUp_mono (ι : ∀ n, obj n ⟶ obj (n + 1)) (hmonoι : ∀ n, Mono (ι n)) (n : ℕ) :
    ∀ r, Mono (iterUp ι n r) := by
  intro r
  induction r with
  | zero => rw [show iterUp ι n 0 = 𝟙 _ from rfl]; infer_instance
  | succ r ih =>
    have := ih
    have := hmonoι (n + r)
    rw [show iterUp ι n (r + 1) = iterUp ι n r ≫ ι (n + r) from rfl]
    exact mono_comp _ _

/-- `iterUp ι n r` is killed by `(f^{n+1}).asHom.app (obj (n+r))`. -/
theorem iterUp_fpow_eq_zero (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hf0 : f.asHom.app (obj 0) = 0) (n r : ℕ) :
    iterUp ι n r ≫ (f ^ (n + 1)).asHom.app (obj (n + r)) = 0 := by
  rw [← powF_nat f (n + 1) (iterUp ι n r), vanishing f map ι hfι hιmap hf0 n, zero_comp]

/-- For `k ≥ 1` and `q + 1 ≥ k`, if `(f^k).asHom.app (obj (q + 1))` kills the pseudoelement `x` then
`proj (q + 1) x = 0`. -/
theorem lemmaP (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hmonoι : ∀ n, Mono (ι n)) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (q : ℕ), k ≤ q + 1 →
      ∀ (x : Abelian.Pseudoelement (obj (q + 1))),
        Abelian.Pseudoelement.pseudoApply ((f ^ k).asHom.app (obj (q + 1))) x = 0 →
        Abelian.Pseudoelement.pseudoApply (proj obj map (q + 1)) x = 0 := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro q _ x hx
    rw [pow_one, ← hfι q, Abelian.Pseudoelement.comp_apply] at hx
    have := hmonoι q
    have hmap0 : Abelian.Pseudoelement.pseudoApply (map q) x = 0 := by
      apply Abelian.Pseudoelement.pseudo_injective_of_mono (ι q)
      rw [hx, Abelian.Pseudoelement.apply_zero]
    change Abelian.Pseudoelement.pseudoApply (map q ≫ proj obj map q) x = 0
    rw [Abelian.Pseudoelement.comp_apply, hmap0, Abelian.Pseudoelement.apply_zero]
  | succ k hk ih =>
    intro q hq x hx
    obtain ⟨Q, rfl⟩ : ∃ Q, q = Q + 1 :=
      ⟨q - 1, by omega⟩
    set u := Abelian.Pseudoelement.pseudoApply (map (Q + 1)) x with hu
    rw [← mulF_pow_succ f (obj (Q + 1 + 1)) k, Abelian.Pseudoelement.comp_apply] at hx
    rw [← hfι (Q + 1), Abelian.Pseudoelement.comp_apply] at hx
    have := hmonoι (Q + 1)
    have hfk0 : Abelian.Pseudoelement.pseudoApply ((f ^ k).asHom.app (obj (Q + 1))) u = 0 := by
      apply Abelian.Pseudoelement.pseudo_injective_of_mono (ι (Q + 1))
      rw [Abelian.Pseudoelement.apply_zero,
        ← Abelian.Pseudoelement.comp_apply, powF_nat f k (ι (Q + 1)),
        Abelian.Pseudoelement.comp_apply, hx]
    have hQ : k ≤ Q + 1 := by omega
    have hproju : Abelian.Pseudoelement.pseudoApply (proj obj map (Q + 1)) u = 0 :=
      ih Q hQ u hfk0
    change Abelian.Pseudoelement.pseudoApply (map (Q + 1) ≫ proj obj map (Q + 1)) x = 0
    rw [Abelian.Pseudoelement.comp_apply, ← hu, hproju]

/-- For every `N` and `r`, a pseudoelement `x : obj (N + r)` killed by `f^{N+1}` lies in the
image of the iterated up-map `iterUp ι N r : obj N ⟶ obj (N + r)`. -/
theorem stabilization (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (w : ∀ n, ι n ≫ proj obj map (n + 1) = 0)
    (hSES : ∀ n, (ShortComplex.mk (ι n) (proj obj map (n + 1)) (w n)).ShortExact) :
    ∀ (N r : ℕ) (x : Abelian.Pseudoelement (obj (N + r))),
      Abelian.Pseudoelement.pseudoApply ((f ^ (N + 1)).asHom.app (obj (N + r))) x = 0 →
      ∃ y, Abelian.Pseudoelement.pseudoApply (iterUp ι N r) y = x := by
  have hmonoι : ∀ n, Mono (ι n) := fun n => (hSES n).mono_f
  intro N r
  induction r with
  | zero =>
    intro x hx
    refine ⟨x, ?_⟩
    change Abelian.Pseudoelement.pseudoApply (𝟙 (obj (N + 0))) x = x
    induction x using Quotient.inductionOn with
    | _ a =>
      rw [Abelian.Pseudoelement.pseudoApply_mk']
      apply Quotient.sound
      exact ⟨a.left, 𝟙 _, 𝟙 _, inferInstance, inferInstance, by simp⟩
  | succ r ih =>
    intro x hx
    have hproj : Abelian.Pseudoelement.pseudoApply (proj obj map (N + r + 1)) x = 0 :=
      lemmaP f map ι hfι hmonoι (N + 1) (by omega) (N + r) (by omega) x hx
    obtain ⟨x₀, hx₀⟩ := Abelian.Pseudoelement.pseudo_exact_of_exact (hSES (N + r)).exact x hproj
    have := hmonoι (N + r)
    have hx₀kill :
        Abelian.Pseudoelement.pseudoApply ((f ^ (N + 1)).asHom.app (obj (N + r))) x₀ = 0 := by
      apply Abelian.Pseudoelement.pseudo_injective_of_mono (ι (N + r))
      rw [Abelian.Pseudoelement.apply_zero,
        ← Abelian.Pseudoelement.comp_apply, powF_nat f (N + 1) (ι (N + r)),
        Abelian.Pseudoelement.comp_apply, hx₀]
      exact hx
    obtain ⟨y, hy⟩ := ih x₀ hx₀kill
    refine ⟨y, ?_⟩
    change Abelian.Pseudoelement.pseudoApply (iterUp ι N r ≫ ι (N + r)) y = x
    rw [Abelian.Pseudoelement.comp_apply, hy, hx₀]

/-- `iterUp ι n r` is a kernel of `(f^{n+1}).asHom.app (obj (n+r))`: the canonical lift
`obj n ⟶ ker((f^{n+1}).asHom.app (obj (n+r)))` is an isomorphism `e` with
`e.hom ≫ kernel.ι = iterUp ι n r`. -/
noncomputable def iterUpKerIso (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hf0 : f.asHom.app (obj 0) = 0)
    (w : ∀ n, ι n ≫ proj obj map (n + 1) = 0)
    (hSES : ∀ n, (ShortComplex.mk (ι n) (proj obj map (n + 1)) (w n)).ShortExact)
    (n r : ℕ) :
    obj n ≅ torsionSub f (obj (n + r)) (n + 1) := by
  haveI hmonoι : ∀ n, Mono (ι n) := fun n => (hSES n).mono_f
  let u : obj n ⟶ torsionSub f (obj (n + r)) (n + 1) :=
    kernel.lift _ (iterUp ι n r) (iterUp_fpow_eq_zero f map ι hfι hιmap hf0 n r)
  have hu : u ≫ kernel.ι _ = iterUp ι n r := by simp [u, torsionSub]
  haveI : Mono u := by
    have := iterUp_mono ι hmonoι n r
    exact mono_of_mono_fac hu
  haveI : Epi u := by
    apply Abelian.Pseudoelement.epi_of_pseudo_surjective
    intro z
    set x : Abelian.Pseudoelement (obj (n + r)) :=
      Abelian.Pseudoelement.pseudoApply (kernel.ι ((f ^ (n + 1)).asHom.app (obj (n + r)))) z with hx
    have hxker : Abelian.Pseudoelement.pseudoApply
        ((f ^ (n + 1)).asHom.app (obj (n + r))) x = 0 := by
      rw [hx, ← Abelian.Pseudoelement.comp_apply]
      show Abelian.Pseudoelement.pseudoApply
        (kernel.ι ((f ^ (n + 1)).asHom.app (obj (n + r))) ≫
          (f ^ (n + 1)).asHom.app (obj (n + r))) z = 0
      rw [kernel.condition, Abelian.Pseudoelement.zero_apply]
    obtain ⟨y, hy⟩ := stabilization f map ι hfι w hSES n r x hxker
    refine ⟨y, ?_⟩
    apply Abelian.Pseudoelement.pseudo_injective_of_mono
      (kernel.ι ((f ^ (n + 1)).asHom.app (obj (n + r))))
    rw [← Abelian.Pseudoelement.comp_apply, hu, hy, ← hx]
  haveI : IsIso u := isIso_of_mono_of_epi u
  exact asIso u

/-- The defining factorization of `iterUpKerIso`: `e.hom ≫ kernel.ι = iterUp ι n r`. -/
theorem iterUpKerIso_hom_ι (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hf0 : f.asHom.app (obj 0) = 0)
    (w : ∀ n, ι n ≫ proj obj map (n + 1) = 0)
    (hSES : ∀ n, (ShortComplex.mk (ι n) (proj obj map (n + 1)) (w n)).ShortExact)
    (n r : ℕ) :
    (iterUpKerIso f map ι hfι hιmap hf0 w hSES n r).hom
      ≫ kernel.ι ((f ^ (n + 1)).asHom.app (obj (n + r))) = iterUp ι n r := by
  simp [iterUpKerIso, torsionSub]

/-- Composing two transition maps of an `ℕ`-indexed functor. -/
theorem seq_map_trans_comp {A : Type*} [Category A] (F : ℕ ⥤ A) {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    F.map (homOfLE hab) ≫ F.map (homOfLE hbc) = F.map (homOfLE (le_trans hab hbc)) := by
  rw [← Functor.map_comp]; rfl

/-- All transition maps `F.map (a ⟶ b)` with `n ≤ a ≤ b` are isos, provided every
successor transition past `n` is an iso. -/
theorem seq_trans_iso {A : Type*} [Category A] (F : ℕ ⥤ A) (n : ℕ)
    (h : ∀ k, n ≤ k → IsIso (F.map (homOfLE (Nat.le_succ k))))
    (a b : ℕ) (hna : n ≤ a) (hab : a ≤ b) : IsIso (F.map (homOfLE hab)) := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    simpa using (inferInstance : IsIso (F.map (𝟙 (0 : ℕ))))
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · have hab' : a ≤ b := by omega
      have : F.map (homOfLE hab) = F.map (homOfLE hab') ≫ F.map (homOfLE (Nat.le_succ b)) := by
        rw [← Functor.map_comp]; rfl
      rw [this]; have := ih hab'; have := h b (by omega); infer_instance
    · obtain rfl : a = b + 1 := by omega
      simpa using (inferInstance : IsIso (F.map (𝟙 (b + 1 : ℕ))))

/-- **Eventually-iso sequential colimit.** If all successor transitions of `F : ℕ ⥤ A` past
`n` are isos, then the colimit leg `colimit.ι F n` is an isomorphism. -/
theorem isIso_colimit_ι_of_eventually_iso {A : Type*} [Category A] (F : ℕ ⥤ A) [HasColimit F]
    (n : ℕ) (h : ∀ k, n ≤ k → IsIso (F.map (homOfLE (Nat.le_succ k)))) :
    IsIso (colimit.ι F n) := by
  have htr : ∀ (m : ℕ) (hnm : n ≤ m), IsIso (F.map (homOfLE hnm)) := fun m hnm =>
    seq_trans_iso F n h n m (le_refl n) hnm
  let ℓ : ∀ k, F.obj k ⟶ F.obj n := fun k =>
    F.map (homOfLE (le_max_right n k)) ≫ inv (F.map (homOfLE (le_max_left n k)))
  have hℓeq : ∀ (k m : ℕ) (hnm : n ≤ m) (hkm : k ≤ m),
      ℓ k = F.map (homOfLE hkm) ≫ inv (F.map (homOfLE hnm)) := by
    intro k m hnm hkm
    have := htr m hnm
    have := htr (max n k) (le_max_left n k)
    have key : inv (F.map (homOfLE (le_max_left n k))) ≫ F.map (homOfLE hnm)
        = F.map (homOfLE (show max n k ≤ m by omega)) := by
      rw [IsIso.inv_comp_eq, seq_map_trans_comp]
    rw [show ℓ k = F.map (homOfLE (le_max_right n k)) ≫ inv (F.map (homOfLE (le_max_left n k)))
        from rfl, IsIso.eq_comp_inv, Category.assoc, key, seq_map_trans_comp]
  have hℓι : ∀ k, ℓ k ≫ colimit.ι F n = colimit.ι F k := by
    intro k
    rw [hℓeq k (max n k) (le_max_left n k) (le_max_right n k)]
    have := htr (max n k) (le_max_left n k)
    rw [Category.assoc, ← colimit.w F (homOfLE (le_max_left n k)), IsIso.inv_hom_id_assoc]
    exact colimit.w F (homOfLE (le_max_right n k))
  let coc : Cocone F :=
    { pt := F.obj n
      ι := { app := ℓ
             naturality := by
               intro i j φ
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
               have hij : i ≤ j := leOfHom φ
               rw [hℓeq j (max n j) (le_max_left n j) (le_max_right n j),
                   hℓeq i (max n j) (le_max_left n j) (by omega), ← Category.assoc]
               congr 1
               change F.map φ ≫ F.map (homOfLE (le_max_right n j)) = _
               rw [show φ = homOfLE hij from rfl, seq_map_trans_comp] } }
  refine ⟨colimit.desc F coc, ?_, ?_⟩
  · rw [colimit.ι_desc]
    change ℓ n = 𝟙 (F.obj n)
    rw [hℓeq n n (le_refl n) (le_refl n)]
    have := htr n (le_refl n)
    rw [IsIso.hom_inv_id]
  · apply colimit.hom_ext; intro k
    rw [← Category.assoc, colimit.ι_desc, Category.comp_id]
    exact hℓι k

/-- The natural transformation on `seqF ι` given by (multiplication by) `g`, used to express
`G[f^{n+1}]` as `colim` of a kernel diagram. -/
noncomputable def kerNat (ι : ∀ n, obj n ⟶ obj (n + 1))
    (g : End (𝟭 (SheafOfModules.{max u v} R))) : seqF ι ⟶ seqF ι where
  app k := g.asHom.app ((seqF ι).obj k)
  naturality i j φ := by simpa using g.asHom.naturality ((seqF ι).map φ)

/-- Given `g : End (𝟭 _)` and a family of isos `u r : obj n ≅ ker (g.asHom.app (obj (n+r)))`
compatible with the iterated up-maps `iterUp`, the canonical lift `L : obj n ⟶ ker (g.asHom.app G)`
is an isomorphism. -/
theorem colimKerLift_isIso (ι : ∀ n, obj n ⟶ obj (n + 1)) (n : ℕ)
    (g : End (𝟭 (SheafOfModules.{max u v} R)))
    (powFg : ∀ {A B : SheafOfModules.{max u v} R} (φ : A ⟶ B),
      g.asHom.app A ≫ φ = φ ≫ g.asHom.app B)
    [PreservesFiniteLimits (colim (J := ℕ) (C := SheafOfModules.{max u v} R))]
    (iterUpf : ∀ r, obj n ⟶ obj (n + r))
    (hiterUp0 : iterUpf 0 = 𝟙 (obj n))
    (hiterUpS : ∀ r, iterUpf (r + 1) = iterUpf r ≫ ι (n + r))
    (u : ∀ r, obj n ≅ kernel (g.asHom.app (obj (n + r))))
    (hu : ∀ r, (u r).hom ≫ kernel.ι (g.asHom.app (obj (n + r))) = iterUpf r)
    (L : obj n ⟶ kernel (g.asHom.app (Gobj ι)))
    (hLι : L ≫ kernel.ι (g.asHom.app (Gobj ι)) = cleg ι n) :
    IsIso L := by
  set kerN := kerNat ι g with hkerN
  have hcolmap : (colim (J := ℕ)).map kerN = g.asHom.app (Gobj ι) := by
    apply colimit.hom_ext; intro k
    rw [colimit.ι_map]; exact powFg (colimit.ι (seqF ι) k)
  let Φ : colimit (kernel kerN) ≅ kernel (g.asHom.app (Gobj ι)) :=
    (PreservesKernel.iso (colim (J := ℕ) (C := SheafOfModules.{max u v} R)) kerN)
      ≪≫ kernelIsoOfEq hcolmap
  have hΦι : Φ.hom ≫ kernel.ι (g.asHom.app (Gobj ι)) = (colim (J := ℕ)).map (kernel.ι kerN) := by
    rw [show Φ.hom = (PreservesKernel.iso (colim (J := ℕ)) kerN).hom ≫ (kernelIsoOfEq hcolmap).hom
          from rfl,
        Category.assoc, kernelIsoOfEq_hom_comp_ι hcolmap, PreservesKernel.iso_hom,
        kernelComparison_comp_ι]
  have : ∀ k, PreservesLimit (parallelPair kerN 0)
      ((evaluation ℕ (SheafOfModules.{max u v} R)).obj k) := fun _ => inferInstance
  let eKer : ∀ k, (kernel kerN).obj k ≅ kernel (g.asHom.app (obj k)) := fun k =>
    PreservesKernel.iso ((evaluation ℕ (SheafOfModules.{max u v} R)).obj k) kerN
  have heKer : ∀ k, (eKer k).hom ≫ kernel.ι (g.asHom.app (obj k)) = (kernel.ι kerN).app k := by
    intro k
    rw [show (eKer k).hom = kernelComparison kerN ((evaluation ℕ (SheafOfModules.{max u v} R)).obj
        k)
        from PreservesKernel.iso_hom _ _]
    exact kernelComparison_comp_ι kerN ((evaluation ℕ (SheafOfModules.{max u v} R)).obj k)
  have hseqmap : ∀ m, (seqF ι).map (homOfLE (Nat.le_succ m)) = ι m := fun m =>
    Functor.ofSequence_map_homOfLE_succ ι m
  have htrans : ∀ r, IsIso ((kernel kerN).map (homOfLE (Nat.le_succ (n + r)))) := by
    intro r
    let kerMap : kernel (g.asHom.app (obj (n + r))) ⟶ kernel (g.asHom.app (obj (n + r + 1))) :=
      kernel.map (g.asHom.app (obj (n + r))) (g.asHom.app (obj (n + r + 1))) (ι (n + r)) (ι (n + r))
        (powFg (ι (n + r)))
    have hkerMapι : kerMap ≫ kernel.ι (g.asHom.app (obj (n + r + 1)))
        = kernel.ι (g.asHom.app (obj (n + r))) ≫ ι (n + r) := kernel.lift_ι _ _ _
    have : IsIso kerMap := by
      have hukerMap : (u r).hom ≫ kerMap = (u (r + 1)).hom := by
        apply (cancel_mono (kernel.ι (g.asHom.app (obj (n + r + 1))))).1
        have rhs : (u (r + 1)).hom ≫ kernel.ι (g.asHom.app (obj (n + r + 1))) = iterUpf (r + 1) :=
          hu (r + 1)
        rw [rhs, Category.assoc, hkerMapι, hiterUpS r, ← hu r]
        exact (Category.assoc _ _ _).symm
      have hkm : kerMap = (u r).inv ≫ (u (r + 1)).hom := by
        rw [← hukerMap, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      rw [hkm]; infer_instance
    have hnat : (kernel kerN).map (homOfLE (Nat.le_succ (n + r))) ≫ (kernel.ι kerN).app (n + r + 1)
        = (kernel.ι kerN).app (n + r) ≫ ι (n + r) := by
      have := (kernel.ι kerN).naturality (homOfLE (Nat.le_succ (n + r)))
      rw [hseqmap] at this; exact this
    have : Mono ((kernel.ι kerN).app (n + r + 1)) := by rw [← heKer (n + r + 1)]; infer_instance
    have hconj : (kernel kerN).map (homOfLE (Nat.le_succ (n + r))) ≫ (eKer (n + r + 1)).hom
        = (eKer (n + r)).hom ≫ kerMap := by
      apply (cancel_mono (kernel.ι (g.asHom.app (obj (n + r + 1))))).1
      rw [Category.assoc, heKer (n + r + 1), hnat, Category.assoc, hkerMapι, ← Category.assoc,
        heKer (n + r)]
    have : IsIso ((kernel kerN).map (homOfLE (Nat.le_succ (n + r))) ≫ (eKer (n + r + 1)).hom) := by
      rw [hconj]; infer_instance
    exact IsIso.of_isIso_comp_right _ (eKer (n + r + 1)).hom
  have hleg : IsIso (colimit.ι (kernel kerN) n) := by
    apply isIso_colimit_ι_of_eventually_iso (kernel kerN) n
    intro k hk
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact htrans r
  let Ψ : obj n ≅ colimit (kernel kerN) :=
    u 0 ≪≫ (eKer n).symm ≪≫ asIso (colimit.ι (kernel kerN) n)
  let Θ : obj n ≅ kernel (g.asHom.app (Gobj ι)) := Ψ ≪≫ Φ
  have hΘ : Θ.hom ≫ kernel.ι (g.asHom.app (Gobj ι)) = cleg ι n := by
    change (Ψ.hom ≫ Φ.hom) ≫ kernel.ι (g.asHom.app (Gobj ι)) = cleg ι n
    rw [Category.assoc, hΦι]
    change ((u 0).hom ≫ (eKer n).inv ≫ colimit.ι (kernel kerN) n)
        ≫ (colim (J := ℕ)).map (kernel.ι kerN) = cleg ι n
    rw [Category.assoc, Category.assoc, colimit.ι_map]
    change (u 0).hom ≫ (eKer n).inv ≫ (kernel.ι kerN).app n ≫ colimit.ι (seqF ι) n = cleg ι n
    rw [← heKer n]
    change (u 0).hom ≫ (eKer n).inv ≫ ((eKer n).hom ≫ kernel.ι (g.asHom.app (obj n)))
        ≫ colimit.ι (seqF ι) n = cleg ι n
    rw [Category.assoc, ← Category.assoc (eKer n).inv, Iso.inv_hom_id, Category.id_comp]
    have h0 : (u 0).hom ≫ kernel.ι (g.asHom.app (obj n)) = 𝟙 (obj n) := by
      have := hu 0; rw [hiterUp0] at this; exact this
    rw [← Category.assoc, h0, Category.id_comp]
    rfl
  have hLΘ : L = Θ.hom := by
    apply (cancel_mono (kernel.ι (g.asHom.app (Gobj ι)))).1
    rw [hLι, hΘ]
  rw [hLΘ]; infer_instance

/-- The comparison `obj n ⟶ G[f^{n+1}]` is an isomorphism. -/
theorem kerLift_isIso (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hmono : ∀ n, Mono (cleg ι n))
    (hf0 : f.asHom.app (obj 0) = 0)
    (w : ∀ n, ι n ≫ proj obj map (n + 1) = 0)
    (hSES : ∀ n, (ShortComplex.mk (ι n) (proj obj map (n + 1)) (w n)).ShortExact)
    (n : ℕ) :
    IsIso (kerLift f map ι hfι hιmap hf0 n) := by
  have : AB5OfSize.{0,0} (AddCommGrpCat.{max u v}) :=
    AB5OfSize_of_univLE.{0,0,max u v, max u v} (AddCommGrpCat.{max u v})
  have : HasExactColimitsOfShape ℕ (PresheafOfModules.{max u v} R.obj) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (PresheafOfModules.toPresheaf R.obj)
  have : HasExactColimitsOfShape ℕ (SheafOfModules.{max u v} R) :=
    Adjunction.hasExactColimitsOfShape
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)) ℕ
  have : PreservesFiniteLimits (colim (J := ℕ) (C := SheafOfModules.{max u v} R)) :=
    inferInstance
  exact (fun _ : Mono (cleg ι n) =>
    colimKerLift_isIso ι n (f ^ (n + 1)) (fun φ => powF_nat f (n + 1) φ)
      (iterUp ι n) rfl (fun r => rfl)
      (fun r => iterUpKerIso f map ι hfι hιmap hf0 w hSES n r)
      (fun r => iterUpKerIso_hom_ι f map ι hfι hιmap hf0 w hSES n r)
      (kerLift f map ι hfι hιmap hf0 n)
      (kerLift_ι f map ι hfι hιmap hf0 n)) (hmono n)

/-- The kernel isomorphisms `e n : obj n ≅ G[f^{n+1}]`. -/
noncomputable def kerIso (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hmono : ∀ n, Mono (cleg ι n))
    (hf0 : f.asHom.app (obj 0) = 0)
    (w : ∀ n, ι n ≫ proj obj map (n + 1) = 0)
    (hSES : ∀ n, (ShortComplex.mk (ι n) (proj obj map (n + 1)) (w n)).ShortExact)
    (n : ℕ) :
    obj n ≅ torsionSub f (Gobj ι) (n + 1) :=
  haveI := kerLift_isIso f map ι hfι hιmap hmono hf0 w hSES n
  asIso (kerLift f map ι hfι hιmap hf0 n)

/-- Under the isomorphisms `e`, the transition map `map n` corresponds to `kernelToKernelMulF`,
multiplication by `f` on the kernels. -/
theorem kerIso_compat (hfι : ∀ n, map n ≫ ι n = f.asHom.app (obj (n + 1)))
    (hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n)) (hmono : ∀ n, Mono (cleg ι n))
    (hf0 : f.asHom.app (obj 0) = 0)
    (w : ∀ n, ι n ≫ proj obj map (n + 1) = 0)
    (hSES : ∀ n, (ShortComplex.mk (ι n) (proj obj map (n + 1)) (w n)).ShortExact)
    (n : ℕ) :
    (kerIso f map ι hfι hιmap hmono hf0 w hSES (n + 1)).hom ≫ kernelToKernelMulF f (Gobj ι) (n
        + 1)
      = map n ≫ (kerIso f map ι hfι hιmap hmono hf0 w hSES n).hom := by
  apply (cancel_mono (kernel.ι ((f ^ (n + 1)).asHom.app (Gobj ι)))).1
  change kerLift f map ι hfι hιmap hf0 (n + 1) ≫ kernelToKernelMulF f (Gobj ι) (n + 1)
      ≫ kernel.ι ((f ^ (n + 1)).asHom.app (Gobj ι))
    = (map n ≫ kerLift f map ι hfι hιmap hf0 n) ≫ kernel.ι ((f ^ (n + 1)).asHom.app (Gobj ι))
  have hk : kernelToKernelMulF f (Gobj ι) (n + 1) ≫ kernel.ι ((f ^ (n + 1)).asHom.app (Gobj ι))
      = kernel.ι ((f ^ (n + 1 + 1)).asHom.app (Gobj ι)) ≫ f.asHom.app (Gobj ι) := by
    simp [kernelToKernelMulF, torsionSub]
  rw [hk, ← Category.assoc,
    kerLift_ι f map ι hfι hιmap hf0 (n + 1), Category.assoc,
    kerLift_ι f map ι hfι hιmap hf0 n, formulaA f map ι hfι n]

end DivColim


/-- `(2) ⇒ (3)`: with `ι m : obj m ⟶ obj (m + 1)` the maps of condition (1), the sequential
colimit `G` of `obj 0 →[ι 0] obj 1 →[ι 1] ⋯` is `f`-divisible, and its colimit legs identify
`obj n` with `G[f^{n+1}]` compatibly with the transition maps. -/
theorem stacks0H39_two_imp_three
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    Condition2 f obj map → Condition3 f obj map := by
  classical
  intro h2
  have hepimap : ∀ n, Epi (map n) := fun n => (h2 n).choose_spec.choose_spec.2.epi_g
  have h1 : Condition1 f obj map := stacks0H39_two_imp_one f obj map h2
  choose ι w hfι hSES using h1
  have hmonoι : ∀ n, Mono (ι n) := fun n => (hSES n).mono_f
  have hιmap : ∀ n, ι n ≫ map n = f.asHom.app (obj n) := fun n =>
    comp_eq_mulF_of_mono f (map n) (ι n) (hmonoι n) (hfι n)
  have hf0 : f.asHom.app (obj 0) = 0 := by
    rw [← hιmap 0]
    simpa [proj] using w 0
  have hmonoc : ∀ n, Mono (DivColim.cleg ι n) := fun n => DivColim.cleg_mono ι hmonoι n
  refine ⟨DivColim.Gobj ι, ?_, ?_, ?_⟩
  · exact DivColim.epi_fappG f map ι hfι hepimap
  · exact fun n => DivColim.kerIso f map ι hfι hιmap hmonoc hf0 w hSES n
  · exact fun n => DivColim.kerIso_compat f map ι hfι hιmap hmonoc hf0 w hSES n

/-- Naturality of multiplication by `f^n`: it commutes with every module homomorphism. -/
theorem powF_naturality (f : End (𝟭 (SheafOfModules.{max u v} R))) (n : ℕ)
    {A B : SheafOfModules.{max u v} R} (g : A ⟶ B) :
    (f ^ n).asHom.app A ≫ g = g ≫ (f ^ n).asHom.app B :=
  mulF_naturality (f ^ n) g

/-- If `M` is `f`-torsion free then multiplication by `f^n` is a monomorphism. -/
theorem torsionFree_pow_mono (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (M : SheafOfModules.{max u v} R) [Mono (f.asHom.app M)] (n : ℕ) :
    Mono ((f ^ n).asHom.app M) := by
  induction n with
  | zero => have h : (f ^ 0).asHom.app M = 𝟙 M := by rw [pow_zero]; rfl
            rw [h]; exact CategoryTheory.instMonoId M
  | succ n ih => rw [← mulF_pow_succ]; exact mono_comp _ _

/-- `f^{k+2} = f^1 ≫ f^{k+1}` as endomorphisms of `M`. -/
theorem powapp_eq (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R) (k :
    ℕ) :
    (f ^ (k + 2)).asHom.app M = (f ^ 1).asHom.app M ≫ (f ^ (k + 1)).asHom.app M := by
  rw [pow_one, mulF_pow_succ]

/-- Identifies `M/f^{k+2}M = coker (f^{k+2})` with `coker (f ≫ f^{k+1})`. -/
noncomputable def indexIso (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v}
    R)
    (k : ℕ) :
    powQuotient f M (k + 2) ≅ cokernel ((f ^ 1).asHom.app M ≫ (f ^ (k + 1)).asHom.app M) :=
  eqToIso (by change cokernel ((f ^ (k + 2)).asHom.app M) = _; rw [powapp_eq])

/-- Cokernel projections of equal morphisms agree up to the induced `eqToHom`. -/
theorem cokπ_eqToHom {X Y : SheafOfModules.{max u v} R} (g g' : X ⟶ Y) (h : g = g')
    (hc : cokernel g = cokernel g') : cokernel.π g ≫ eqToHom hc = cokernel.π g' := by subst h; simp

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the cokernel index iso exceeds the default synthInstance budget
/-- `indexIso` is compatible with the cokernel projections. -/
theorem indexIso_hom_pi (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R)
    (k : ℕ) : cokernel.π ((f ^ (k + 2)).asHom.app M) ≫ (indexIso f M k).hom
      = cokernel.π ((f ^ 1).asHom.app M ≫ (f ^ (k + 1)).asHom.app M) := by
  rw [indexIso, eqToIso.hom]; exact cokπ_eqToHom _ _ (powapp_eq f M k) _

/-- The inverse of `indexIso` is compatible with the cokernel projections. -/
theorem indexIso_inv_pi (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R)
    (k : ℕ) : cokernel.π ((f ^ 1).asHom.app M ≫ (f ^ (k + 1)).asHom.app M) ≫ (indexIso f M k).inv
      = cokernel.π ((f ^ (k + 2)).asHom.app M) := by
  rw [← indexIso_hom_pi, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `π_{f^{n+1}} ≫ quotientToQuotient f M n = π_{f^n}`. -/
theorem qToQ_pi (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R) (n : ℕ)
    :
    cokernel.π ((f ^ (n + 1)).asHom.app M) ≫ quotientToQuotient f M n =
      cokernel.π ((f ^ n).asHom.app M) := by
  rw [quotientToQuotient]; exact cokernel.π_desc _ _ _

/-- The iterated canonical surjection `M/f^{n+1}M → M/fM`. -/
noncomputable def projQuot (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v}
    R) :
    ∀ n, powQuotient f M (n + 1) ⟶ powQuotient f M 1
  | 0 => 𝟙 _
  | (n + 1) => quotientToQuotient f M (n + 1) ≫ projQuot f M n

/-- `π_{f^{n+1}} ≫ projQuot f M n = π_{f}`. -/
theorem projQuot_pi (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R) :
    ∀ n, cokernel.π ((f ^ (n + 1)).asHom.app M) ≫ projQuot f M n = cokernel.π ((f ^ 1).asHom.app M)
  | 0 => Category.comp_id _
  | (n + 1) => by rw [projQuot, ← Category.assoc, qToQ_pi, projQuot_pi f M n]

/-- Under `indexIso`, the canonical surjection `canmap` of `CokSES` is `quotientToQuotient`. -/
theorem indexIso_canmap (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R)
    (k : ℕ) : (indexIso f M k).hom ≫ CokSES.canmap ((f ^ 1).asHom.app M) ((f ^ (k + 1)).asHom.app M)
      = quotientToQuotient f M (k + 1) := by
  apply (cancel_epi (cokernel.π ((f ^ (k + 2)).asHom.app M))).1
  rw [← Category.assoc, indexIso_hom_pi, CokSES.canmap_pi]
  change _ = cokernel.π ((f ^ (k + 2)).asHom.app M) ≫ quotientToQuotient f M (k + 1)
  rw [quotientToQuotient, cokernel.π_desc]

/-- Transport of the iterated transition `proj` to the quotient side. -/
theorem proj_transport (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R)
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n)
    (e : ∀ n, obj n ≅ powQuotient f M (n + 1))
    (hcompat : ∀ n, (e (n + 1)).hom ≫ quotientToQuotient f M (n + 1) = map n ≫ (e n).hom) :
    ∀ n, (e n).hom ≫ projQuot f M n = proj obj map n ≫ (e 0).hom
  | 0 => by rw [projQuot, proj, Category.comp_id, Category.id_comp]
  | (n + 1) => by
      rw [projQuot, proj, ← Category.assoc, hcompat n, Category.assoc,
        proj_transport f M obj map e hcompat n, ← Category.assoc]

/-- On the quotient side, `proj` composed with the multiplication-by-`f^{k+1}` map `jmap`
is multiplication by `f^{k+1}` on `M/f^{k+2}M`. -/
theorem phiIdentity (f : End (𝟭 (SheafOfModules.{max u v} R))) (M : SheafOfModules.{max u v} R)
    [Mono (f.asHom.app M)] (k : ℕ) :
    projQuot f M (k + 1) ≫ CokSES.jmap ((f ^ 1).asHom.app M) ((f ^ (k + 1)).asHom.app M) ≫
        (indexIso f M k).inv
      = (f ^ (k + 1)).asHom.app (powQuotient f M (k + 2)) := by
  apply (cancel_epi (cokernel.π ((f ^ (k + 2)).asHom.app M))).1
  rw [← Category.assoc, ← Category.assoc]
  rw [show cokernel.π ((f ^ (k + 2)).asHom.app M) ≫ projQuot f M (k + 1)
        = cokernel.π ((f ^ 1).asHom.app M) from projQuot_pi f M (k + 1)]
  rw [CokSES.jmap_pi, Category.assoc, indexIso_inv_pi]
  exact powF_naturality f (k + 1) (cokernel.π ((f ^ (k + 2)).asHom.app M))

/-- Condition (2) transports along an isomorphism with a short exact sequence `S`: `e₀`, `e ≫ idx`
and `eₖ` identify the tower with `S`, `P` is the iterated transition on the model side, and
`P ≫ S.f ≫ idx.inv` is multiplication by `f^{k+1}`. -/
private theorem condition2_of_iso_shortExact
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) (k : ℕ)
    {Y : SheafOfModules.{max u v} R} (S : ShortComplex (SheafOfModules.{max u v} R))
    (hS : S.ShortExact) (e₀ : obj 0 ≅ S.X₁) (e : obj (k + 1) ≅ Y) (idx : Y ≅ S.X₂)
    (eₖ : obj k ≅ S.X₃) (P : Y ⟶ S.X₁) (hmapk : e.hom ≫ idx.hom ≫ S.g = map k ≫ eₖ.hom)
    (hP : e.hom ≫ P = proj obj map (k + 1) ≫ e₀.hom)
    (hphi : P ≫ S.f ≫ idx.inv = (f ^ (k + 1)).asHom.app Y) :
    ∃ (j : obj 0 ⟶ obj (k + 1)) (w : j ≫ map k = 0),
      (proj obj map (k + 1) ≫ j = (f ^ (k + 1)).asHom.app (obj (k + 1))) ∧
        (ShortComplex.mk j (map k) w).ShortExact := by
  set j : obj 0 ⟶ obj (k + 1) := e₀.hom ≫ S.f ≫ idx.inv ≫ e.inv with hj
  have hinv : e.inv ≫ map k = idx.hom ≫ S.g ≫ eₖ.inv := by
    rw [Iso.inv_comp_eq, reassoc_of% hmapk, Iso.hom_inv_id, Category.comp_id]
  have hw : j ≫ map k = 0 := by simp [hj, hinv]
  refine ⟨j, hw, ?_, ?_⟩
  · calc proj obj map (k + 1) ≫ j
        = (proj obj map (k + 1) ≫ e₀.hom) ≫ S.f ≫ idx.inv ≫ e.inv := by
          simp only [hj, Category.assoc]
      _ = e.hom ≫ P ≫ S.f ≫ idx.inv ≫ e.inv := by rw [← hP, Category.assoc]
      _ = e.hom ≫ (f ^ (k + 1)).asHom.app Y ≫ e.inv := by rw [reassoc_of% hphi]
      _ = (f ^ (k + 1)).asHom.app (obj (k + 1)) := by
          rw [← Category.assoc, ← mulF_naturality (f ^ (k + 1)) e.hom, Category.assoc,
            Iso.hom_inv_id, Category.comp_id]
  · exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk e₀ (e ≪≫ idx) eₖ (by simp [hj]) (by simpa using hmapk)).symm hS

/-- `(4) ⇒ (2)`: for an `f`-torsion free `M` with `obj n ≅ M/f^{n+1}M`, the sequence
`0 → M/fM → M/f^{k+2}M → M/f^{k+1}M → 0`, whose first map is induced by multiplication by
`f^{k+1}`, is short exact and transports across the isomorphisms to condition (2). -/
theorem stacks0H39_four_imp_two
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    Condition4 f obj map → Condition2 f obj map := by
  rintro ⟨M, htf, e, hcompat⟩ k
  have : Mono (f.asHom.app M) := htf
  have hma : Mono ((f ^ (k + 1)).asHom.app M) := torsionFree_pow_mono f M (k + 1)
  have hmba : Mono ((f ^ 1).asHom.app M ≫ (f ^ (k + 1)).asHom.app M) := by
    rw [← powapp_eq]; exact torsionFree_pow_mono f M (k + 2)
  exact condition2_of_iso_shortExact f obj map k _
    (CokSES.compMono_shortExact ((f ^ 1).asHom.app M) ((f ^ (k + 1)).asHom.app M)) (e 0) (e (k + 1))
    (indexIso f M k) (e k) (projQuot f M (k + 1)) (by rw [indexIso_canmap]; exact hcompat k)
    (proj_transport f M obj map e hcompat (k + 1)) (phiIdentity f M k)

/-! ## Kernel-side machinery for `(3) ⇒ (2)` (dual of the quotient-side helpers above)

Mirror of `indexIso`/`projQuot`/`proj_transport`/`phiIdentity`, but for the kernel
(torsion-submodule) tower of an `f`-divisible module `G`, using the dual SES namespace
`KerSES`. -/

/-- The `ι` characterization of `kernelToKernelMulF` (it is mult-by-`f` on the kernels). -/
theorem kerToKer_ι (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u v} R)
    (n : ℕ) : kernelToKernelMulF f G n ≫ kernel.ι ((f ^ n).asHom.app G)
      = kernel.ι ((f ^ (n + 1)).asHom.app G) ≫ f.asHom.app G := by
  simp [kernelToKernelMulF, torsionSub]

/-- If `G` is `f`-divisible then multiplication by `f^n` is an epimorphism. -/
theorem divisible_pow_epi (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (G : SheafOfModules.{max u v} R) [Epi (f.asHom.app G)] (n : ℕ) : Epi ((f ^ n).asHom.app G) := by
  induction n with
  | zero => have h : (f ^ 0).asHom.app G = 𝟙 G := by rw [pow_zero]; rfl
            rw [h]; exact CategoryTheory.instEpiId G
  | succ n ih => rw [← mulF_pow_succ]; exact epi_comp _ _

/-- Kernel inclusions of equal morphisms agree up to the induced `eqToHom`. -/
theorem kerι_eqToHom {X Y : SheafOfModules.{max u v} R} (g g' : X ⟶ Y) (h : g = g')
    (hc : kernel g = kernel g') : eqToHom hc ≫ kernel.ι g' = kernel.ι g := by subst h; simp

/-- Identifies `G[f^{k+2}] = ker (f^{k+2})` with `ker (f ≫ f^{k+1})`. -/
noncomputable def indexIsoK (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u
    v} R)
    (k : ℕ) : torsionSub f G (k + 2) ≅ kernel ((f ^ 1).asHom.app G ≫ (f ^ (k + 1)).asHom.app G) :=
  eqToIso (by change kernel ((f ^ (k + 2)).asHom.app G) = _; rw [powapp_eq])

/-- The inverse of `indexIsoK` is compatible with the kernel inclusions. -/
theorem indexIsoK_inv_ι (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u v} R)
    (k : ℕ) : (indexIsoK f G k).inv ≫ kernel.ι ((f ^ (k + 2)).asHom.app G)
      = kernel.ι ((f ^ 1).asHom.app G ≫ (f ^ (k + 1)).asHom.app G) := by
  rw [indexIsoK, eqToIso.inv]; exact kerι_eqToHom _ _ (powapp_eq f G k) _

/-- `indexIsoK` is compatible with the kernel inclusions. -/
theorem indexIsoK_hom_ι (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u v} R)
    (k : ℕ) : (indexIsoK f G k).hom ≫ kernel.ι ((f ^ 1).asHom.app G ≫ (f ^ (k + 1)).asHom.app G)
      = kernel.ι ((f ^ (k + 2)).asHom.app G) := by
  rw [← indexIsoK_inv_ι, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The `kjmap` of `KerSES` matches `kernelToKernelMulF` after the index isomorphism. -/
theorem indexIsoK_kjmap (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u v} R)
    (k : ℕ) : (indexIsoK f G k).hom ≫ KerSES.kjmap ((f ^ 1).asHom.app G) ((f ^ (k + 1)).asHom.app G)
      = kernelToKernelMulF f G (k + 1) := by
  apply (cancel_mono (kernel.ι ((f ^ (k + 1)).asHom.app G))).1
  rw [Category.assoc, KerSES.ι_kjmap, ← Category.assoc, indexIsoK_hom_ι, kerToKer_ι f G (k + 1)]
  change kernel.ι ((f ^ (k + 2)).asHom.app G) ≫ (f ^ 1).asHom.app G = _
  rw [pow_one]

/-- The iterated `kernelToKernelMulF`: `G[f^{n+1}] → G[f]`. -/
noncomputable def projKer (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u v}
    R) :
    ∀ n, torsionSub f G (n + 1) ⟶ torsionSub f G 1
  | 0 => 𝟙 _
  | (n + 1) => kernelToKernelMulF f G (n + 1) ≫ projKer f G n

/-- `projKer f G n ≫ ι_{f} = ι_{f^{n+1}} ≫ f^n`. -/
theorem projKer_ι (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u v} R) :
    ∀ n, projKer f G n ≫ kernel.ι ((f ^ 1).asHom.app G)
      = kernel.ι ((f ^ (n + 1)).asHom.app G) ≫ (f ^ n).asHom.app G
  | 0 => by
      rw [projKer]
      change 𝟙 _ ≫ kernel.ι ((f ^ 1).asHom.app G) =
        kernel.ι ((f ^ 1).asHom.app G) ≫ (f ^ 0).asHom.app G
      rw [Category.id_comp, pow_zero]; change _ = _ ≫ (𝟙 G); rw [Category.comp_id]
  | (n + 1) => by
      rw [projKer, Category.assoc, projKer_ι f G n, ← Category.assoc, kerToKer_ι f G (n + 1),
        Category.assoc, mulF_pow_succ]

/-- Transport of the iterated transition `proj` to the kernel side. -/
theorem proj_transport_ker (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u v}
    R)
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n)
    (e : ∀ n, obj n ≅ torsionSub f G (n + 1))
    (hcompat : ∀ n, (e (n + 1)).hom ≫ kernelToKernelMulF f G (n + 1) = map n ≫ (e n).hom) :
    ∀ n, (e n).hom ≫ projKer f G n = proj obj map n ≫ (e 0).hom
  | 0 => by rw [projKer, proj, Category.comp_id, Category.id_comp]
  | (n + 1) => by
      rw [projKer, proj, ← Category.assoc, hcompat n, Category.assoc,
        proj_transport_ker f G obj map e hcompat n, ← Category.assoc]

/-- On the kernel side, `projKer` composed with the inclusion `kincl` is multiplication by
`f^{k+1}` on `G[f^{k+2}]`. -/
theorem phiIdentityK (f : End (𝟭 (SheafOfModules.{max u v} R))) (G : SheafOfModules.{max u v} R)
    (k : ℕ) :
    projKer f G (k + 1) ≫ KerSES.kincl ((f ^ 1).asHom.app G) ((f ^ (k + 1)).asHom.app G)
        ≫ (indexIsoK f G k).inv
      = (f ^ (k + 1)).asHom.app (torsionSub f G (k + 2)) := by
  apply (cancel_mono (kernel.ι ((f ^ (k + 2)).asHom.app G))).1
  rw [Category.assoc, Category.assoc, indexIsoK_inv_ι, KerSES.ι_kincl, projKer_ι f G (k + 1)]
  exact (powF_naturality f (k + 1) (kernel.ι ((f ^ (k + 2)).asHom.app G))).symm

/-- `(3) ⇒ (2)`: for an `f`-divisible `G` with `obj n ≅ G[f^{n+1}]`, the short exact sequence
`0 → G[f] →[kincl] G[f^{k+2}] →[mult by f] G[f^{k+1}] → 0` transports across the isomorphisms
to condition (2). -/
theorem stacks0H39_three_imp_two
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    Condition3 f obj map → Condition2 f obj map := by
  rintro ⟨G, hdiv, e, hcompat⟩ k
  have : Epi (f.asHom.app G) := hdiv
  have hea : Epi ((f ^ 1).asHom.app G) := by rw [pow_one]; exact hdiv
  have heba : Epi ((f ^ 1).asHom.app G ≫ (f ^ (k + 1)).asHom.app G) := by
    rw [← powapp_eq]; exact divisible_pow_epi f G (k + 2)
  exact condition2_of_iso_shortExact f obj map k _
    (KerSES.compEpi_shortExact ((f ^ 1).asHom.app G) ((f ^ (k + 1)).asHom.app G)) (e 0) (e (k + 1))
    (indexIsoK f G k) (e k) (projKer f G (k + 1)) (by rw [indexIsoK_kjmap]; exact hcompat k)
    (proj_transport_ker f G obj map e hcompat (k + 1)) (phiIdentityK f G k)

/-- Conditions (1) and (2) on an inverse system are equivalent. -/
@[stacks 0H39 "(1)⇔(2)"]
theorem stacks0H39_one_iff_two
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    Condition1 f obj map ↔ Condition2 f obj map :=
  ⟨stacks0H39_one_imp_two f obj map, stacks0H39_two_imp_one f obj map⟩

/-- Conditions (2) and (3) on an inverse system are equivalent. -/
@[stacks 0H39 "(2)⇔(3)"]
theorem stacks0H39_two_iff_three
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    Condition2 f obj map ↔ Condition3 f obj map :=
  ⟨stacks0H39_two_imp_three f obj map, stacks0H39_three_imp_two f obj map⟩

/-- Condition (4) on an inverse system implies condition (3). -/
@[stacks 0H39 "(4)⇒(3)"]
theorem stacks0H39_four_imp_three
    (f : End (𝟭 (SheafOfModules.{max u v} R)))
    (obj : ℕ → SheafOfModules.{max u v} R) (map : ∀ n, obj (n + 1) ⟶ obj n) :
    Condition4 f obj map → Condition3 f obj map := fun h =>
  stacks0H39_two_imp_three f obj map (stacks0H39_four_imp_two f obj map h)

end Stacks.Cohomology.InverseSystems.TorsionFreeDivisible
