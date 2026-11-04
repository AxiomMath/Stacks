module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.LocalRing.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products of rings

Let `f : A → B` and `g : C → B` be maps of `R`-algebras.  Their fibre product `A ×_B C` is the
subalgebra of `A × C` cut out by `f a = g c`; it is Mathlib's `AlgHom.pullback`, and for plain
ring maps `RingHom.pullback`.  This file collects the ring-theoretic properties of such a fibre
product that do not involve modules over it.

## Main definitions

* `RingFibreProduct.Situation` is Stacks Tag 08KH: the data of a map `B → A` together with a
  surjection `A' → A` with a specified kernel `I`.  Its `fibreProduct` is the fourth corner
  `B ×_A A'` of the resulting cartesian square, and `pullbackConeIsLimit` records that the
  square really is cartesian.

## Main results

* `Algebra.FiniteType.pullback` is Stacks Tag 00IT: over a Noetherian ring, the fibre product of
  finite type algebras `A` and `C` along a surjection `A → B` and a finite map `C → B` is again
  of finite type.  Its module-theoretic crux is `AlgHom.moduleFinite_prod_pullback`.
* `RingFibreProduct.finiteType_of_pullback_pi` is Stacks Tag 08NI: the same conclusion for a
  cartesian square assembled from a finite product of surjections.
* `RingFibreProduct.pullback_snd_isIntegral_of_surjective` is Stacks Tag 0E1S: the projection
  `B ×_A A' → A'` is integral as soon as `B → A` is integral and `A' → A` is surjective.

## Implementation notes

Finite type of `A ×_B C` is deduced from the Artin-Tate lemma (`fg_of_fg_of_fg`, Stacks Tag
00IS) applied to the tower `R → A ×_B C → A × C`, so the work is in showing that `A × C` is a
finite module over the fibre product.  The source of Tag 00IT also assumes that `B` is of finite
type over `R`; that follows from the hypotheses on `C` and `g`, so it is omitted.

The situation of Tag 08KH is phrased with an explicitly named kernel because the sections on
Milnor patching quantify over that ideal; the cartesian square itself is Mathlib's concrete
pullback cone in `CommRingCat`, which is why the categorical statements are restricted to a
single universe.

## References

* [Stacks Project, Tag 00IT](https://stacks.math.columbia.edu/tag/00IT)
* [Stacks Project, Tag 08KH](https://stacks.math.columbia.edu/tag/08KH)
* [Stacks Project, Tag 08NI](https://stacks.math.columbia.edu/tag/08NI)
* [Stacks Project, Tag 0E1S](https://stacks.math.columbia.edu/tag/0E1S)
-/

@[expose] public section

/-! ### The fibre product situation -/

section

open CategoryTheory CategoryTheory.Limits

namespace RingFibreProduct
universe u uA uA' uB

variable {A : Type uA} {A' : Type uA'} {B : Type uB} [CommRing A] [CommRing A'] [CommRing B]

@[expose] public section

/-- The setup for a ring fibre product `B ×_A A'` in which `A' → A` is surjective and
has the specified ideal `I` as its kernel. -/
@[stacks 08KH]
public structure Situation (toBase : B →+* A) (surjection : A' →+* A)
    (I : Ideal A') : Prop where
  surjective_surjection : Function.Surjective surjection
  ker_surjection : RingHom.ker surjection = I

namespace Situation

/-- The ring `B' = B ×_A A'` associated to a ring fibre product situation. -/
public abbrev fibreProduct {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (_s : Situation toBase surjection I) : Type (max uB uA') :=
  RingHom.pullback toBase surjection

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]

/-- The canonical cone whose point is `B ×_A A'` and whose legs are the two projections. -/
@[stacks 08KH]
public abbrev pullbackCone {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (_s : Situation toBase surjection I) :
    PullbackCone (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection) :=
  CommRingCat.pullbackCone (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection)

/-- The canonical square defining `B ×_A A'` is cartesian. -/
@[stacks 08KH]
public def pullbackConeIsLimit {toBase : B →+* A} {surjection : A' →+* A}
    {I : Ideal A'} (s : Situation toBase surjection I) :
    IsLimit s.pullbackCone :=
  CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection)

end Situation

end

end RingFibreProduct

end

/-! ### Finite type -/

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/- INFORMAL PROOF (Stacks Tag 00IT, the module-finiteness step).
Write `D = A ×_B C = {(a,c) : f a = g c}`. There is a commutative diagram with
exact rows
  `0 ← B ← A ← I ← 0`   (`I = ker f`)
  `0 ← C ← D ← I ← 0`
where the left squares are the projections. The claim is that `A × C` is a
finite `D`-module, because it is the (internal) direct sum of the two finite
`D`-modules `A × {0}` and `{0} × C`, viewed as `D`-modules via the inclusion
`D ↪ A × C` and the componentwise action `(a',c') • (x,y) = (a'x, c'y)`.

* `{0} × C` is generated over `D` by `(0,1)` together with `(1,1) = 1_{A×C}`:
  the projection `π_C : D → C`, `(a,c) ↦ c`, is SURJECTIVE — given `c : C`,
  `g c ∈ B` lifts (since `f` is surjective) to some `a : A` with `f a = g c`, so
  `(a, c) ∈ D` and `π_C (a,c) = c`. Hence every `(0, c)` equals
  `(a, c) • (0,1) = (0, c)` where `(a,c) ∈ D`, so `{0} × C = D • (0,1)`, a cyclic
  (hence finite) `D`-module.

* `A × {0}` is generated over `D` by the finite set `{(1,0)} ∪ {(xᵢ, 0)}` where
  the `xᵢ ∈ A` are chosen as follows. Choose `y₁, …, yₙ ∈ B` generating `B` as a
  `C`-module (possible by `hBC : (g).Finite`). Choose `xᵢ ∈ A` with `f xᵢ = yᵢ`
  (possible by surjectivity of `f`). Then `1, x₁, …, xₙ` generate `A` as a
  `D`-module: given `a : A`, write `f a = Σᵢ (g cᵢ) yᵢ` with `cᵢ ∈ C`; pick
  `aᵢ : A` with `f aᵢ = g cᵢ` so `(aᵢ, cᵢ) ∈ D`, and set
  `a' = a - Σᵢ aᵢ xᵢ ∈ A`. Then `f a' = f a - Σᵢ (g cᵢ) yᵢ = 0`, i.e.
  `a' ∈ I = ker f`, and `(a', 0) ∈ D` (since `f a' = 0 = g 0`). Therefore
  `(a, 0) = (a', 0) • (1, 0) + Σᵢ (aᵢ, cᵢ) • (xᵢ, 0)` is a `D`-combination of
  `(1,0), (x₁,0), …, (xₙ,0)`. So `A × {0}` is a finite `D`-module.

* `A × C = (A × {0}) + ({0} × C)` as `D`-submodules, so it is finite over `D`
  (sum of two finite submodules; or directly: the finite generating set
  `{(1,0), (x₁,0), …, (xₙ,0), (0,1)}` together with `1_D` generates `A × C`).
-/

/-- **Crux of Stacks Tag 00IT (the "finite module" step).** The product `A × C` is finite as
a module over the pullback `f.pullback g`, provided that `f` is surjective and that `B` is
finite as a `C`-module via `g`. -/
theorem AlgHom.moduleFinite_prod_pullback (f : A →ₐ[R] B) (g : C →ₐ[R] B)
    (hf : Function.Surjective f) (hBC : g.Finite) :
    Module.Finite (f.pullback g) (A × C) := by
  let := (g : C →+* B).toAlgebra
  have hMod : Module.Finite C B := hBC
  obtain ⟨s, hs⟩ := hMod.fg_top
  set D := f.pullback g with hD
  have hact : ∀ (d : D) (x : A × C), d • x = (d : A × C) * x := fun d x => rfl
  choose lx hlx using fun y : B => hf y
  set T : Set (A × C) :=
    insert ((1 : A), (0 : C)) ((fun y => (lx y, (0 : C))) '' (s : Set B)) ∪ {((0 : A), (1 : C))}
  -- the `(a, 0)` component lies in the span of `T`.
  have hzeroA : ∀ a : A, ((a, 0) : A × C) ∈ Submodule.span D T := by
    intro a
    have hfa : f a ∈ Submodule.span C (s : Set B) := by rw [hs]; trivial
    rw [Submodule.mem_span_finset] at hfa
    obtain ⟨coeff, _, hcoeff⟩ := hfa
    set a' : A := a - ∑ y ∈ s, lx (g (coeff y)) * lx y with ha'
    have hfa' : f a' = 0 := by
      rw [ha']
      simp only [map_sub, map_sum, map_mul, hlx]
      rw [← hcoeff]
      exact sub_eq_zero.mpr (Finset.sum_congr rfl fun _ _ => rfl)
    have hmemA' : ((a', 0) : A × C) ∈ D := by simp [hD, AlgHom.mem_equalizer, hfa']
    have hmemY : ∀ y : B, ((lx (g (coeff y)), coeff y) : A × C) ∈ D := fun y => hlx _
    have hsum :
        (∑ y ∈ s, (⟨(lx (g (coeff y)), coeff y), hmemY y⟩ : D) • ((lx y, 0) : A × C))
          = ((∑ y ∈ s, lx (g (coeff y)) * lx y, (0 : C)) : A × C) := by
      rw [Finset.sum_congr rfl fun y _ => by rw [hact]]
      refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]
    have heq : ((a, 0) : A × C)
        = (⟨(a', 0), hmemA'⟩ : D) • ((1, 0) : A × C)
          + ∑ y ∈ s, (⟨(lx (g (coeff y)), coeff y), hmemY y⟩ : D) • ((lx y, 0) : A × C) := by
      rw [hact, hsum]
      refine Prod.ext ?_ ?_
      · simp [ha']
      · simp
    rw [heq]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      (Submodule.sum_mem _ fun y hy => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    · exact Or.inl (Set.mem_insert _ _)
    · exact Or.inl (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩)
  -- the `(0, c)` component lies in the span of `T`.
  have hzeroC : ∀ c : C, ((0, c) : A × C) ∈ Submodule.span D T := by
    intro c
    obtain ⟨d, hd⟩ := AlgHom.surjective_pullbackSnd_of_surjective f g hf c
    have hsmul0 : d • ((0, 1) : A × C) = ((0, c) : A × C) := by
      rw [hact, ← hd]; simp [Prod.ext_iff]
    rw [← hsmul0]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))
  -- conclude: the span of the finite set `T` is everything.
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨T, ?_, ?_⟩
  · exact ((s.finite_toSet.image _).insert _).union (Set.finite_singleton _)
  · rw [eq_top_iff]
    rintro ⟨a, c⟩ -
    have : ((a, c) : A × C) = ((a, 0) : A × C) + ((0, c) : A × C) := by
      rw [Prod.ext_iff]; constructor <;> simp
    rw [this]
    exact Submodule.add_mem _ (hzeroA a) (hzeroC c)

/-- **Stacks Tag 00IT.** Let `R` be a Noetherian ring and let `f : A →ₐ[R] B`
and `g : C →ₐ[R] B` be `R`-algebra maps. If `A` and `C` are of finite type over
`R`, `f` is surjective, and `g` is a finite morphism (that is, `B` is finitely
generated as a `C`-module), then the fibre product `A ×_B C` is of finite type
over `R`. -/
@[stacks 00IT]
theorem Algebra.FiniteType.pullback [IsNoetherianRing R] [Algebra.FiniteType R A]
    [Algebra.FiniteType R C] (f : A →ₐ[R] B) (g : C →ₐ[R] B) (hf : Function.Surjective f)
    (hBC : g.Finite) : Algebra.FiniteType R (f.pullback g) := by
  -- Artin–Tate (Stacks Tag 00IS = `fg_of_fg_of_fg`) on the tower `R → f.pullback g → A × C`.
  set D := f.pullback g
  have hMod : Module.Finite (D : Type _) (A × C) :=
    AlgHom.moduleFinite_prod_pullback f g hf hBC
  have hAC : (⊤ : Subalgebra R (A × C)).FG := Algebra.FiniteType.out
  have hinj : Function.Injective (algebraMap (D : Type _) (A × C)) := by
    rw [Subalgebra.algebraMap_eq]; exact Subtype.coe_injective
  exact ⟨fg_of_fg_of_fg R (D : Type _) (A × C) hAC (Module.finite_def.mp hMod) hinj⟩

section

section
namespace RingFibreProduct
private theorem finiteType_pi
    {R : Type*} [CommRing R] {I : Type*} [Finite I]
    (A : I → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (hA : ∀ i, Algebra.FiniteType R (A i)) :
    Algebra.FiniteType R (∀ i, A i) := by
  let := Fintype.ofFinite I
  revert A
  refine Fintype.induction_empty_option
    (fun α β _ e h A _ _ hA ↦
      Algebra.FiniteType.equiv (h _ (fun i ↦ hA (e i)))
        (AlgEquiv.piCongrLeft R A e)) ?_ ?_ I
  · intro A _ _ _
    exact Algebra.FiniteType.of_surjective (Algebra.ofId R _)
      (fun x ↦ ⟨0, Subsingleton.elim _ _⟩)
  · intro α _ h A _ _ hA
    let e : (∀ i, A i) ≃ₐ[R] A none × (∀ i, A (some i)) :=
      AlgEquiv.ofRingEquiv (f := RingEquiv.piOptionEquivProd) (by intro r; rfl)
    let : Algebra.FiniteType R (A none) := hA none
    let : Algebra.FiniteType R (∀ i, A (some i)) := h _ (fun i ↦ hA (some i))
    exact Algebra.FiniteType.equiv inferInstance e.symm

/-- Stacks Tag 08NI: in a cartesian square formed from finite products of surjective maps of
finite type algebras over a Noetherian ring, the lower right corner is of finite type. -/
@[stacks 08NI]
public theorem finiteType_of_pullback_pi
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {I : Type*} [Finite I]
    {A B : I → Type*}
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)]
    {Q : Type*} [CommRing Q] [Algebra R Q]
    {P : Type*} [CommRing P] [Algebra R P]
    (φ : ∀ i, A i →ₐ[R] B i) (ψ : ∀ i, Q →ₐ[R] B i)
    (toA : P →ₐ[R] ∀ i, A i) (toQ : P →ₐ[R] Q)
    (e : P ≃ₐ[R]
      AlgHom.pullback
        (AlgHom.pi (fun i ↦ (φ i).comp (Pi.evalAlgHom R A i)))
        (AlgHom.pi ψ))
    (_he : ∀ p, (e p : (∀ i, A i) × Q) = (toA p, toQ p))
    (hφ : ∀ i, Function.Surjective (φ i))
    (hψ : ∀ i, Function.Surjective (ψ i))
    (hA : ∀ i, Algebra.FiniteType R (A i))
    (_hB : ∀ i, Algebra.FiniteType R (B i))
    (hQ : Algebra.FiniteType R Q) :
    Algebra.FiniteType R P := by
  let f : (∀ i, A i) →ₐ[R] (∀ i, B i) :=
    AlgHom.pi (fun i ↦ (φ i).comp (Pi.evalAlgHom R A i))
  let g : Q →ₐ[R] (∀ i, B i) := AlgHom.pi ψ
  have hf : Function.Surjective f := by
    intro b
    choose a ha using fun i ↦ hφ i (b i)
    exact ⟨a, funext ha⟩
  have : Algebra.FiniteType R (∀ i, A i) := finiteType_pi A hA
  have hg : (g : Q →+* (∀ i, B i)).Finite := by
    let : Algebra Q (∀ i, B i) := (g : Q →+* (∀ i, B i)).toAlgebra
    let (i : I) : Algebra Q (B i) := (ψ i : Q →+* B i).toAlgebra
    have (i : I) : Module.Finite Q (B i) := RingHom.Finite.of_surjective _ (hψ i)
    exact Module.Finite.pi
  exact Algebra.FiniteType.equiv (Algebra.FiniteType.pullback f g hf hg) e.symm

end RingFibreProduct
end

end

/-! ### Integrality of the projections -/

section

section
open CategoryTheory CategoryTheory.Limits Polynomial

namespace RingFibreProduct
universe u

variable {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]

/-- The second projection `B ×_A A' → A'` is integral when `B → A` is integral and
`A' → A` is surjective. -/
@[stacks 0E1S]
public theorem pullback_snd_isIntegral_of_surjective (toBase : B →+* A) (surjection : A' →+* A)
    (hSurjective : Function.Surjective surjection) (hIntegral : toBase.IsIntegral) :
    (CommRingCat.pullbackCone (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom surjection)).snd.hom.IsIntegral := by
  let cone := CommRingCat.pullbackCone (CommRingCat.ofHom toBase)
    (CommRingCat.ofHom surjection)
  let fst : cone.pt →+* B := cone.fst.hom
  let snd : cone.pt →+* A' := cone.snd.hom
  have hfst : Function.Surjective fst :=
    RingHom.surjective_pullbackFst_of_surjective toBase surjection hSurjective
  show snd.IsIntegral
  rcases subsingleton_or_nontrivial B with hB | hB
  · have hzero : (0 : A) = 1 := by
      rw [← map_zero toBase, ← map_one toBase, Subsingleton.elim (0 : B) 1]
    have : Subsingleton A := subsingleton_of_zero_eq_one hzero
    intro a'
    let y : cone.pt := ⟨(0, a'), Subsingleton.elim _ _⟩
    refine ⟨X - C y, monic_X_sub_C y, ?_⟩
    rw [eval₂_sub, eval₂_X, eval₂_C]
    show a' - a' = 0
    exact sub_self a'
  have : Nontrivial cone.pt := hfst.nontrivial
  intro x
  obtain ⟨p, hp, hpx⟩ := hIntegral (surjection x)
  obtain ⟨q, hqmap, hqdeg, hq⟩ :=
    lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective hfst (p * X)) (hp.mul monic_X)
  let e : A' := eval₂ snd x q
  have he : surjection e = 0 := by
    rw [show surjection e = eval₂ (surjection.comp snd) (surjection x) q by
      simp [e, hom_eval₂],
      show surjection.comp snd = toBase.comp fst from RingHom.ext fun y ↦ y.property.symm,
      ← eval₂_map, hqmap]
    simp [hpx]
  let k : cone.pt := ⟨(0, e), by simpa [e] using he.symm⟩
  refine ⟨q - C k, ?_, ?_⟩
  · apply hq.add_of_left
    rw [degree_neg]
    refine degree_C_lt.trans_le ?_
    rw [degree_eq_natDegree hq.ne_zero, hqdeg, natDegree_mul_X hp.ne_zero]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le p.natDegree)
  · rw [eval₂_sub, eval₂_C]
    show e - e = 0
    exact sub_self e

end RingFibreProduct
end

end
