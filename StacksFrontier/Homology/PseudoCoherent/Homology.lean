module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import StacksFrontier.Algebra.Homology.PseudoCoherent
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

-- Needed so the `HomologicalComplex.sc`/`sc'` normalisations below close by `rfl`.
set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Throughout, `R` is a (unital) ring, and complexes of `R`-modules are
cochain complexes
`K^• = (... → K^{i-1} → K^i → K^{i+1} → ...)`
indexed by `i ∈ ℤ`, with differentials `d^i_K : K^i → K^{i+1}` satisfying
`d^{i+1}_K ∘ d^i_K = 0`. We write `H^i(K^•) = ker(d^i_K) / im(d^{i-1}_K)` for the
`i`-th cohomology module. We work in the derived category `D(R)` of the category of
`R`-modules; morphisms in `D(R)` are morphisms in the derived category (i.e. obtained
from chain maps by formally inverting quasi-isomorphisms). For a morphism `α` of
`D(R)`, `H^i(α) : H^i(E^•) → H^i(K^•)` denotes the induced map on the `i`-th
cohomology.

## Main Definition

Definition 1 (`m`-pseudo-coherent complex). Let `m ∈ ℤ`. An object `K^•` of `D(R)`
is `m`-pseudo-coherent if there exists a complex `E^•` of finite free `R`-modules
together with a morphism `α : E^• → K^•` in `D(R)` such that:
- `E^•` is bounded, i.e. `E^i = 0` for all but finitely many `i ∈ ℤ`;
- each `E^i` is a finite free `R`-module, i.e. isomorphic to `R^{⊕ r_i}` for some
  integer `r_i ≥ 0`;
- `H^i(α) : H^i(E^•) → H^i(K^•)` is an isomorphism for all `i > m`; and
- `H^m(α) : H^m(E^•) → H^m(K^•)` is surjective.

This is Definition 15.66.1(1) of the Stacks project (tag 064Q).

Definition 2 (finite type `R`-module). An `R`-module `M` is of finite type
(equivalently, finitely generated) if there exists a surjection
`R^{⊕ t} ↠ M`. In Mathlib this is `Module.Finite R M`.

Definition 3 (finitely presented `R`-module). An `R`-module `M` is finitely presented
if there exist integers `s, t ≥ 0` and an exact sequence
`R^{⊕ s} → R^{⊕ t} → M → 0`. In Mathlib this is `Module.FinitePresentation R M`.

## Main Statements

Let `R` be a ring, let `K^•` be a complex of `R`-modules (viewed as an object of
`D(R)`), and let `m ∈ ℤ`.

Statement 1. If `K^•` is `m`-pseudo-coherent and `H^i(K^•) = 0` for all `i > m`,
then `H^m(K^•)` is a finite type (i.e. finitely generated) `R`-module.

Statement 2. If `K^•` is `m`-pseudo-coherent and `H^i(K^•) = 0` for all `i > m + 1`,
then `H^{m+1}(K^•)` is a finitely presented `R`-module.

This is Lemma 15.66.3 (Stacks project tag 064S).
-/

/-
# Notes and Context

- The definition of `m`-pseudo-coherent used here is Definition 15.66.1(1) (tag 064Q),
  which uses a *bounded* complex `E^•` of finite free `R`-modules (i.e. `E^i = 0` for
  all but finitely many `i`). The "bounded above" phrasing in the Stacks project belongs
  to the separate, unqualified notion of a *pseudo-coherent* object (Definition
  15.66.1(2)), which is not used in Lemma 15.66.3.
- The two statements are independent claims about the same setup.
- Modelling choices:
  * `K^•` is taken to be an object `K` of the derived category
    `DerivedCategory (ModuleCat R)`.
  * The cohomology `H^i(K^•)` is `(DerivedCategory.homologyFunctor (ModuleCat R) i).obj K`,
    an object of `ModuleCat R`, regarded as an `R`-module via its coercion.
  * `H^i(K^•) = 0` is expressed as `IsZero (...)`.
  * `E^•` is a `CochainComplex (ModuleCat R) ℤ`; "finite free" for `E^i` is
    `Module.Free R (E.X i) ∧ Module.Finite R (E.X i)`; boundedness is "`E.X i` is the
    zero object outside a finite window".
  * `α : E^• → K^•` is a morphism `(DerivedCategory.Q).obj E ⟶ K` in `D(R)`, where
    `DerivedCategory.Q` is the localization functor sending a cochain complex to `D(R)`.
  * `H^i(α)` is `(DerivedCategory.homologyFunctor (ModuleCat R) i).map α`; "isomorphism"
    is `IsIso`, "surjective" is `Epi` (in `ModuleCat R`, `Epi` is equivalent to
    surjectivity).
-/

open CategoryTheory Limits
open StacksDraft.PseudoCoherence

universe u v

/-! ## Main definition

`m`-pseudo-coherence (Definition 15.66.1(1), Stacks tag 064Q) is
`StacksDraft.PseudoCoherence.IsPseudoCoherentFrom`, and the boundedness/finite-freeness of the
approximating complex is packaged there as `IsBoundedFiniteFree`, whose fields
`IsBoundedFiniteFree.upperBound` and `IsBoundedFiniteFree.finiteFree` supply the degree above
which the complex vanishes and its degreewise finite freeness. The comparison
`H^i(Q(E)) ≅ H^i(E)` between the derived-category homology of `Q(E)` and the cochain homology
of `E` is `StacksDraft.PseudoCoherence.bridgeIso`.
-/

/-!
## Auxiliary lemmas about bounded cochain complexes of finite free modules

The structural heart of Stacks 064S is purely about a *bounded cochain complex
`E` of finite free `R`-modules* and its honest cohomology `H^i(E)`.  Once these
are established, the derived-category statements follow by transporting along the
natural isomorphism `DerivedCategory.homologyFunctorFactors`, which identifies
`H^i((DerivedCategory.Q).obj E)` with `H^i(E)`, together with the
iso/epi maps `H^i(α)` and the cohomology vanishing of `K`.
-/

/- **Auxiliary Lemma A (finite type).**
If `E` is a bounded cochain complex of finite free `R`-modules with `H^i(E) = 0`
for all `i > m`, then `H^m(E)` is of finite type.

The argument is the "split off the top term" induction of Stacks 064S, run on the
cycle modules rather than by truncating the complex.  Descending from a degree `b`
above which `E` vanishes, exactness at `i` identifies `range d^i` with
`ker d^{i+1}`, so the projectivity of `ker d^{i+1}` splits `d^i` and hands down
finiteness *and* projectivity of `ker d^i`; above `b` the cycles are trivial, which
starts the induction.  Projectivity, not freeness, is the invariant that survives
each splitting, so the induction is stated for projective modules even though the
hypothesis received is finite freeness.  `H^m(E)` is then a quotient of the finite
module `ker d^m`. -/
/-- The "split off the top summand" step.  Given an `R`-linear map `f : A → B`
out of a finite projective module `A` whose image `range f` is projective, the
kernel `ker f` is finite and projective.  (The surjection `A ↠ range f` splits
because `range f` is projective, exhibiting `ker f` as a direct summand of `A`.) -/
@[sga "6 I 1.3" "more general"]
private theorem finite_projective_ker {R A B : Type*} [Ring R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [Module.Finite R A] [Module.Projective R A] (f : A →ₗ[R] B)
    (hrangeProj : Module.Projective R (LinearMap.range f)) :
    Module.Finite R (LinearMap.ker f) ∧ Module.Projective R (LinearMap.ker f) := by
  set g : A →ₗ[R] (LinearMap.range f) := f.rangeRestrict
  have hgsurj : Function.Surjective g := f.surjective_rangeRestrict
  have hgker : LinearMap.ker g = LinearMap.ker f := LinearMap.ker_rangeRestrict f
  have : Module.FinitePresentation R (LinearMap.range f) :=
    Module.finitePresentation_of_projective R (LinearMap.range f)
  refine ⟨?_, ?_⟩
  · have hfg : (LinearMap.ker g).FG := Module.FinitePresentation.fg_ker g hgsurj
    rw [hgker] at hfg
    exact Module.Finite.iff_fg.mpr hfg
  · obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hgsurj
    have hmem : ∀ x : A, x - s (g x) ∈ LinearMap.ker g := by
      intro x
      simp only [LinearMap.mem_ker, map_sub]
      have : g (s (g x)) = g x := by simpa using LinearMap.congr_fun hs (g x)
      rw [this, sub_self]
    let r : A →ₗ[R] LinearMap.ker g :=
      (LinearMap.id - s ∘ₗ g).codRestrict (LinearMap.ker g) hmem
    have hsplit : r ∘ₗ (LinearMap.ker g).subtype = LinearMap.id := by
      ext x
      simp only [r, LinearMap.codRestrict, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.sub_apply, LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk]
      have hx : g x = 0 := x.property
      simp [hx]
    have hp : Module.Projective R (LinearMap.ker g) :=
      Module.Projective.of_split (LinearMap.ker g).subtype r hsplit
    rwa [hgker] at hp

/-- Core module-theoretic induction.  For a ℤ-indexed family of finitely generated
projective modules `M i` with maps `f i : M i →ₗ[R] M (i + 1)`, where `M i` is trivial for
`i > b` and the family is exact (`range (f i) = ker (f (i + 1))`) for `i ≥ m`, the cycle
module `ker (f m)` is finite **and** projective. -/
private theorem finite_projective_ker_of_exact {R : Type*} [Ring R] (M : ℤ → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (f : ∀ i, M i →ₗ[R] M (i + 1))
    (hfin : ∀ i, Module.Finite R (M i)) (hproj : ∀ i, Module.Projective R (M i)) (m b : ℤ)
    (hb : ∀ i, b < i → Subsingleton (M i))
    (hex : ∀ i, m ≤ i → LinearMap.range (f i) = LinearMap.ker (f (i + 1))) :
    Module.Finite R (LinearMap.ker (f m)) ∧ Module.Projective R (LinearMap.ker (f m)) := by
  have hzero : ∀ i, b < i →
      Module.Finite R (LinearMap.ker (f i)) ∧ Module.Projective R (LinearMap.ker (f i)) := by
    intro i hbi
    have := hb i hbi
    have : Subsingleton (LinearMap.ker (f i)) := inferInstance
    exact ⟨Module.Finite.of_finite, inferInstance⟩
  have key : ∀ n : ℕ, ∀ i : ℤ, m ≤ i → (b + 1 - i).toNat ≤ n →
      Module.Finite R (LinearMap.ker (f i)) ∧ Module.Projective R (LinearMap.ker (f i)) := by
    intro n
    induction n with
    | zero => exact fun i _ hn => hzero i (by omega)
    | succ n ih =>
      intro i hi hn
      by_cases hbi : b < i
      · exact hzero i hbi
      · have hi1 : m ≤ i + 1 := by omega
        have hn1 : (b + 1 - (i + 1)).toNat ≤ n := by omega
        obtain ⟨-, hrangeProj⟩ := ih (i + 1) hi1 hn1
        rw [← hex i hi] at hrangeProj
        have := hfin i
        have := hproj i
        exact finite_projective_ker (f i) hrangeProj
  exact key (b + 1 - m).toNat m le_rfl le_rfl

namespace CochainComplex

/-- Bridge: vanishing of `H^{i+1}(E)` (as a `ModuleCat` zero object) gives the honest
exactness `range d^i = ker d^{i+1}` at the level of underlying `R`-linear maps. -/
private theorem range_d_eq_ker_d_of_isZero_homology {R : Type*} [Ring R]
    (E : CochainComplex (ModuleCat R) ℤ) (i : ℤ)
    (h : IsZero ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ)
      (i + 1)).obj E)) :
    LinearMap.range (E.d i (i + 1)).hom = LinearMap.ker (E.d (i + 1) (i + 1 + 1)).hom := by
  have hExactAt : E.ExactAt (i + 1) := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr h
  have hprev : (ComplexShape.up ℤ).prev (i+1) = i := by simp
  have hnext : (ComplexShape.up ℤ).next (i+1) = i+1+1 := by simp
  rw [HomologicalComplex.exactAt_iff' E i (i+1) (i+1+1) hprev hnext,
    ShortComplex.moduleCat_exact_iff_range_eq_ker] at hExactAt
  have hf : (E.sc' i (i+1) (i+1+1)).f = E.d i (i+1) := by simp [HomologicalComplex.sc']
  have hg : (E.sc' i (i+1) (i+1+1)).g = E.d (i+1) (i+1+1) := by simp [HomologicalComplex.sc']
  rwa [hf, hg] at hExactAt

/-- The kernel of the right map of `E.sc m` is the module of degree-`m` cycles `ker d^m`. -/
private theorem ker_sc_g_eq_ker_d {R : Type*} [Ring R] (E : CochainComplex (ModuleCat R) ℤ)
    (m : ℤ) : LinearMap.ker (E.sc m).g.hom = LinearMap.ker (E.d m (m + 1)).hom := by
  change LinearMap.ker (E.d m ((ComplexShape.up ℤ).next m)).hom = _
  rw [show (ComplexShape.up ℤ).next m = m + 1 from by simp]

/-- Bridge: finiteness of the degree-`m` cycles `ker d^m` gives finiteness of `H^m(E)`,
since the latter is a quotient of the former. -/
private theorem finite_homology_of_finite_cycles {R : Type*} [Ring R]
    (E : CochainComplex (ModuleCat R) ℤ) (m : ℤ)
    (hker : Module.Finite R (LinearMap.ker (E.d m (m + 1)).hom)) :
    Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) m).obj E) := by
  have hcyc : Module.Finite R (LinearMap.ker ((E.sc m).g).hom) := by
    rwa [ker_sc_g_eq_ker_d]
  have hH : Module.Finite R ((E.sc m).moduleCatLeftHomologyData.H) := by
    unfold ShortComplex.moduleCatLeftHomologyData; dsimp only; infer_instance
  have hiso : (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) m).obj E
      ≅ (E.sc m).moduleCatLeftHomologyData.H :=
    ShortComplex.moduleCatHomologyIso (E.sc m)
  exact Module.Finite.equiv (hiso.symm.toLinearEquiv)

/-- For a cochain complex `E` of finite free `R`-modules vanishing above degree `b`, whose
cohomology vanishes above degree `m`, the degree-`m` cycle module `ker d^m` is finite and
projective. -/
private theorem finite_projective_cycles_of_finiteFree {R : Type*} [Ring R]
    (E : CochainComplex (ModuleCat R) ℤ) (m b : ℤ) [E.IsStrictlyLE b]
    (hfree : ∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i))
    (hvanish : ∀ i : ℤ, m < i →
      IsZero ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj E)) :
    Module.Finite R (LinearMap.ker (E.d m (m + 1)).hom) ∧
      Module.Projective R (LinearMap.ker (E.d m (m + 1)).hom) := by
  -- Package the complex as a ℤ-indexed family of finite free modules.
  let M : ℤ → Type _ := fun i => ↥(E.X i)
  let f : ∀ i, M i →ₗ[R] M (i + 1) := fun i => (E.d i (i + 1)).hom
  exact finite_projective_ker_of_exact M f (fun i => (hfree i).right)
    (fun i => have := (hfree i).left; inferInstance) m b
    (fun i hi => ModuleCat.subsingleton_of_isZero (E.isZero_of_isStrictlyLE b i hi))
    (fun i hi => range_d_eq_ker_d_of_isZero_homology E i (hvanish (i + 1) (by omega)))

/-- If `E` is a cochain complex of finite free `R`-modules vanishing above degree `b`, with
`H^i(E) = 0` for all `i > m`, then `H^m(E)` is a finite `R`-module. -/
@[sga "6 I 2.1.1" "special case"]
theorem finite_homology_of_finiteFree {R : Type*} [Ring R]
    (E : CochainComplex (ModuleCat R) ℤ) (m b : ℤ) [E.IsStrictlyLE b]
    (hfree : ∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i))
    (hvanish : ∀ i : ℤ, m < i →
      IsZero ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj E)) :
    Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) m).obj E) :=
  finite_homology_of_finite_cycles E m
    (finite_projective_cycles_of_finiteFree E m b hfree hvanish).left

/- **Auxiliary Lemma B (finitely presented).**
If `E` is a bounded cochain complex of finite free `R`-modules with `H^i(E) = 0`
for all `i > m + 1`, then `H^{m+1}(E)` is finitely presented.

Lemma A's induction already gives that `ker d^{m+1}` is finite and projective,
hence finitely presented.  `H^{m+1}(E)` is its quotient by the image of `d^m`,
which is finitely generated because `E^m` is; a quotient of a finitely presented
module by a finitely generated submodule is finitely presented. -/
/-- Finite-presentation bridge: if the degree-`m+1` cycles `ker d^{m+1}` are finitely
presented (which holds when they are finite and projective) and `E^m` is finite, then
`H^{m+1}(E)` is finitely presented, being the quotient of the finitely-presented cycle
module by the finitely-generated image of `d^m`. -/
private theorem finitePresentation_homology_succ_of_finitePresentation_cycles {R : Type*} [Ring R]
    (E : CochainComplex (ModuleCat R) ℤ) (m : ℤ)
    [Module.Finite R (E.X m)]
    (hker : Module.FinitePresentation R (LinearMap.ker (E.d (m + 1) (m + 1 + 1)).hom)) :
    Module.FinitePresentation R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (m + 1)).obj E) := by
  -- The cycle module `ker (E.sc (m+1)).g.hom` is finitely presented.
  have hkerS : Module.FinitePresentation R (LinearMap.ker ((E.sc (m+1)).g).hom) := by
    rwa [ker_sc_g_eq_ker_d]
  -- `E^m` finite ⟹ the cycle-image `range (moduleCatToCycles)` is finitely generated.
  have hX1 : Module.Finite R (E.sc (m+1)).X₁ := by
    have h : (E.sc (m+1)).X₁ = E.X m := by simp [HomologicalComplex.sc]
    rw [h]; infer_instance
  have hrangeFG : (LinearMap.range (E.sc (m+1)).moduleCatToCycles).FG :=
    Module.Finite.iff_fg.mp inferInstance
  -- `H = ker / range` is finitely presented (quotient of f.p. by f.g.).
  have hHfp : Module.FinitePresentation R
      (↥(LinearMap.ker ((E.sc (m+1)).g).hom) ⧸
        LinearMap.range (E.sc (m+1)).moduleCatToCycles) :=
    Module.finitePresentation_of_surjective
      (LinearMap.range (E.sc (m+1)).moduleCatToCycles).mkQ
      (LinearMap.range (E.sc (m+1)).moduleCatToCycles).mkQ_surjective
      (by rwa [Submodule.ker_mkQ])
  -- Transport along `moduleCatLeftHomologyData_H` and the homology iso.
  have hHeq : (E.sc (m+1)).moduleCatLeftHomologyData.H =
      ModuleCat.of R (↥((E.sc (m+1)).g.hom).ker ⧸ (E.sc (m+1)).moduleCatToCycles.range) :=
    ShortComplex.moduleCatLeftHomologyData_H (E.sc (m+1))
  have : Module.FinitePresentation R ((E.sc (m+1)).moduleCatLeftHomologyData.H) := by
    rwa [hHeq]
  have hiso : (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (m+1)).obj E
      ≅ (E.sc (m+1)).moduleCatLeftHomologyData.H :=
    ShortComplex.moduleCatHomologyIso (E.sc (m+1))
  exact Module.FinitePresentation.of_equiv hiso.symm.toLinearEquiv

/-- If `E` is a cochain complex of finite free `R`-modules vanishing above degree `b`, with
`H^i(E) = 0` for all `i > m + 1`, then `H^{m+1}(E)` is a finitely presented `R`-module. -/
@[sga "6 I 2.1.1" "special case"]
theorem finitePresentation_homology_succ_of_finiteFree {R : Type*} [Ring R]
    (E : CochainComplex (ModuleCat R) ℤ) (m b : ℤ) [E.IsStrictlyLE b]
    (hfree : ∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i))
    (hvanish : ∀ i : ℤ, m + 1 < i →
      IsZero ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj E)) :
    Module.FinitePresentation R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (m + 1)).obj E) := by
  -- The degree-`m+1` cycle module is finite and projective, hence finitely presented.
  obtain ⟨_, _⟩ := finite_projective_cycles_of_finiteFree E (m + 1) b hfree hvanish
  have : Module.Finite R (E.X m) := (hfree m).right
  -- And `H^{m+1}(E)` is finitely presented, being a quotient of it by `im d^m`.
  exact finitePresentation_homology_succ_of_finitePresentation_cycles E m
    (Module.finitePresentation_of_projective R (LinearMap.ker (E.d (m + 1) (m + 1 + 1)).hom))

end CochainComplex


/-!
## Transport from `H^*(E)` to `H^*(K)`

The natural isomorphism `DerivedCategory.homologyFunctorFactors (ModuleCat R) i`
identifies the derived-category homology of `Q.obj E` with the cochain homology
of `E`; `StacksDraft.PseudoCoherence.bridgeIso` is the per-object iso it supplies.
-/

-- Main Statement(s)

namespace PseudoCoherence

/-- If `H^i(α)` is an isomorphism for `α : Q(E) ⟶ K` and `H^i(K) = 0`, then `H^i(E) = 0`. -/
private theorem isZero_homology_of_isIso_map {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (E : CochainComplex (ModuleCat.{v} R) ℤ)
    {K : DerivedCategory (ModuleCat.{v} R)} (α : (DerivedCategory.Q).obj E ⟶ K) (i : ℤ)
    (hα : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map α))
    (hK : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K)) :
    IsZero ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj E) :=
  (hK.of_iso (asIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map α))).of_iso
    (bridgeIso E i).symm

/-- Statement 1 (Stacks 064S). If `K^•` is `m`-pseudo-coherent and `H^i(K^•) = 0`
for all `i > m`, then `H^m(K^•)` is a finite type `R`-module. -/
@[stacks 064S "(1)"]
theorem finite_homology_of_isPseudoCoherentFrom {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (K : DerivedCategory (ModuleCat.{v} R))
    (m : ℤ) (hK : IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K)) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat R) m).obj K) := by
  -- Unfold the witness `(E, α)` of `m`-pseudo-coherence, and name a degree `b` above which
  -- the bounded finite free complex `E` vanishes.
  obtain ⟨E, hE, α, hiso, hepi⟩ := hK
  obtain ⟨b, _⟩ := hE.upperBound
  -- STEP 1: `H^i(E) = 0` for `i > m`.
  -- For `i > m`: `H^i(α) : H^i(Q.obj E) → H^i(K)` is iso, and `H^i(K) = 0`,
  -- so `H^i(Q.obj E) = 0`; transport along `bridgeIso` to get `H^i(E) = 0`.
  have hEvanish : ∀ i : ℤ, m < i →
      IsZero ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj E) :=
    fun i hi => isZero_homology_of_isIso_map E α i (hiso i hi) (hvanish i hi)
  -- STEP 2: by Lemma A, `H^m(E)` is finite type.
  have hEfin : Module.Finite R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) m).obj E) :=
    E.finite_homology_of_finiteFree m b (fun i => (hE.finiteFree i).symm) hEvanish
  -- STEP 3: transport to `H^m(Q.obj E)` via `bridgeIso` (iso), then push along
  -- the epi `H^m(α)` to `H^m(K)`.
  have hQEfin : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) m).obj ((DerivedCategory.Q).obj E)) :=
    Module.Finite.equiv (bridgeIso E m).symm.toLinearEquiv
  -- `H^m(α)` is epi, hence surjective on underlying modules.
  have hsurj : Function.Surjective
      ⇑(ConcreteCategory.hom ((DerivedCategory.homologyFunctor (ModuleCat R) m).map α)) := by
    rwa [← ModuleCat.epi_iff_surjective]
  exact Module.Finite.of_surjective
    (ModuleCat.Hom.hom ((DerivedCategory.homologyFunctor (ModuleCat R) m).map α)) hsurj

/-- Statement 2 (Stacks 064S). If `K^•` is `m`-pseudo-coherent and `H^i(K^•) = 0`
for all `i > m + 1`, then `H^{m+1}(K^•)` is a finitely presented `R`-module. -/
@[stacks 064S "(2)"]
theorem finitePresentation_homology_succ_of_isPseudoCoherentFrom {R : Type u} [Ring R]
    [HasDerivedCategory (ModuleCat.{v} R)] (K : DerivedCategory (ModuleCat.{v} R))
    (m : ℤ) (hK : IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K)) :
    Module.FinitePresentation R
      ((DerivedCategory.homologyFunctor (ModuleCat R) (m + 1)).obj K) := by
  obtain ⟨E, hE, α, hiso, -⟩ := hK
  obtain ⟨b, _⟩ := hE.upperBound
  -- STEP 1: `H^i(E) = 0` for `i > m + 1` (same transport as in statement 1,
  -- using that `m + 1 < i ⟹ m < i`, so `H^i(α)` is iso).
  have hEvanish : ∀ i : ℤ, m + 1 < i →
      IsZero ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) i).obj E) :=
    fun i hi => isZero_homology_of_isIso_map E α i (hiso i (by omega)) (hvanish i hi)
  -- STEP 2: by Lemma B, `H^{m+1}(E)` is finitely presented.
  have hEfp : Module.FinitePresentation R
      ((HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (m + 1)).obj E) :=
    E.finitePresentation_homology_succ_of_finiteFree m b
      (fun i => (hE.finiteFree i).symm) hEvanish
  -- STEP 3: transport to `H^{m+1}(Q.obj E)` via `bridgeIso`, then push along the
  -- iso `H^{m+1}(α)` to `H^{m+1}(K)`.
  -- Since `m + 1 > m`, `H^{m+1}(α)` is an isomorphism (not merely epi), so
  -- `H^{m+1}(K) ≅ H^{m+1}(Q.obj E) ≅ H^{m+1}(E)`, and finite presentation is
  -- preserved by `R`-linear isomorphism.
  have hQEfp : Module.FinitePresentation R
      ((DerivedCategory.homologyFunctor (ModuleCat R) (m + 1)).obj
        ((DerivedCategory.Q).obj E)) :=
    Module.FinitePresentation.of_equiv (bridgeIso E (m + 1)).symm.toLinearEquiv
  have hiso1 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) (m + 1)).map α) :=
    hiso (m + 1) (by omega)
  exact Module.FinitePresentation.of_equiv
    (asIso ((DerivedCategory.homologyFunctor (ModuleCat R) (m + 1)).map α)).toLinearEquiv

end PseudoCoherence
