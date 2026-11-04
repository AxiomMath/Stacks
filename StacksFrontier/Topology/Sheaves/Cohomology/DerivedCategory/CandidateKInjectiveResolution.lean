module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
import StacksCore.Tactic.StacksAttribute

/-!
# The candidate K-injective resolution of a complex of modules

Let `O` be a sheaf of rings on a topological space `X` and let `F` be an unbounded complex of
sheaves of `O`-modules. Stacks 20.38 builds a candidate K-injective resolution of `F` as
follows: resolve each canonical truncation `τ_{≥ -n} F` by a bounded-below complex of
injectives `I_n`, arranged so that the transition maps `I_{n+1} ⟶ I_n` are degreewise split
epimorphisms and the resulting ladder commutes; the inverse limit `I = lim_n I_n` is then
K-injective, and the compatible maps `F ⟶ τ_{≥ -n} F ⟶ I_n` determine a canonical map
`F ⟶ I`.

The structure `Stacks.KInjective.CandidateKInjectiveResolution` records this situation and the
canonical map, and the situation can always be arranged. No quasi-isomorphism claim is made
about the canonical map: in the source that requires extra cohomological hypotheses.

## Main definitions

* `Stacks.KInjective.CandidateKInjectiveResolution`: the inverse system of bounded-below
  injective complexes resolving the canonical truncations of `F`, its K-injective limit, and
  the canonical map from `F` into that limit.

## Main results

* `Stacks.KInjective.nonempty_candidateKInjectiveResolution`: every complex of sheaves of
  modules on a topological space admits such a candidate K-injective resolution.

## Implementation notes

The assertion that the displayed map is *canonical* is recorded by its universal
characterisation: `canonicalMap_comp_π` says its composite with each limit projection is the
map through the corresponding canonical truncation, and `canonicalMap_unique` says it is the
only map with that property. So the structure does not merely assert the existence of some
map into the limit.

The inverse system is indexed by `ℕᵒᵖ` through `Functor.ofOpSequence`, which is the shape in
which `isKInjective_limit_of_inverseSystem` and
`CochainComplex.exists_sequence_quasiIso_truncGE` are stated.

## References

* [Stacks Project, Tag 071A](https://stacks.math.columbia.edu/tag/071A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.KInjective

/-- The data surrounding the displayed map of Stacks 071A: an inverse system of bounded-below
complexes of injectives resolving the canonical truncations of `F`, together with its
K-injective limit and the canonical map from `F` to that limit. -/
structure CandidateKInjectiveResolution
    {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : CochainComplex (SheafOfModules.{u} O) ℤ) where
  /-- The bounded below injective complexes in the inverse system. -/
  I : ℕ → CochainComplex (SheafOfModules.{u} O) ℤ
  /-- The quasi-isomorphisms from the canonical truncations of `F`. -/
  f : ∀ n : ℕ, F.truncGE (-(n : ℤ)) ⟶ I n
  /-- The transition maps of the inverse system. -/
  g : ∀ n : ℕ, I (n + 1) ⟶ I n
  quasiIso_f : ∀ n : ℕ, QuasiIso (f n)
  strictlyGE_I : ∀ n : ℕ, (I n).IsStrictlyGE (-(n : ℤ))
  injective_I : ∀ (n : ℕ) (i : ℤ), Injective ((I n).X i)
  splitEpi_g : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((g n).f i)
  ladder : ∀ n : ℕ, F.πTruncGE (-((n + 1 : ℕ) : ℤ)) ≫ f (n + 1) ≫ g n =
    F.πTruncGE (-(n : ℤ)) ≫ f n
  kInjective_limit : (limit (Functor.ofOpSequence g)).IsKInjective
  /-- The displayed map `F ⟶ I` of Tag 071A. -/
  canonicalMap : F ⟶ limit (Functor.ofOpSequence g)
  canonicalMap_comp_π : ∀ n : ℕ,
    canonicalMap ≫ limit.π (Functor.ofOpSequence g) ⟨n⟩ =
      F.πTruncGE (-(n : ℤ)) ≫ f n
  canonicalMap_unique : ∀ (γ : F ⟶ limit (Functor.ofOpSequence g)),
    (∀ n : ℕ, γ ≫ limit.π (Functor.ofOpSequence g) ⟨n⟩ =
      F.πTruncGE (-(n : ℤ)) ≫ f n) → γ = canonicalMap

/-- Every complex of sheaves of modules on a topological space admits a candidate K-injective
resolution. -/
@[stacks 071A]
theorem nonempty_candidateKInjectiveResolution
    {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : CochainComplex (SheafOfModules.{u} O) ℤ) :
    Nonempty (CandidateKInjectiveResolution O F) := by
  let P : ObjectProperty (SheafOfModules.{u} O) := isInjective (SheafOfModules.{u} O)
  let : HasBinaryBiproducts (SheafOfModules.{u} O) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have hprod : ∀ A B : SheafOfModules.{u} O, P A → P B → P (A ⊞ B) := by
    intro A B hA hB
    let : Injective A := hA
    let : Injective B := hB
    infer_instance
  have hP (A : SheafOfModules.{u} O) : ∃ B, ∃ (_ : P B), ∃ i : A ⟶ B, Mono i :=
    let ⟨p⟩ := EnoughInjectives.presentation A
    ⟨p.J, p.injective, p.f, p.mono⟩
  obtain ⟨I, f, g, hf, hmono, hGE, hI, hsplit, hcomm⟩ :=
    CochainComplex.exists_sequence_quasiIso_truncGE P hprod hP F
  have hsplit' : ∀ (n : ℕ) (i : ℤ), IsSplitEpi ((g n).f i) := by
    intro n i
    obtain ⟨C, _, e, he⟩ := hsplit n i
    have hg : (g n).f i = e.hom ≫ biprod.fst := by
      apply (cancel_epi e.inv).1
      simp [he]
    rw [hg]
    infer_instance
  let c : Cone (Functor.ofOpSequence g) := Cone.mk F (NatTrans.ofOpSequence
    (fun n => F.πTruncGE (-(n : ℤ)) ≫ f n) (by
      intro n
      simp only [Functor.const_obj_map]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact (hcomm n).symm))
  let q : F ⟶ limit (Functor.ofOpSequence g) := limit.lift _ c
  have hq : ∀ n : ℕ, q ≫ limit.π (Functor.ofOpSequence g) ⟨n⟩ =
      F.πTruncGE (-(n : ℤ)) ≫ f n := by
    intro n; simp [q, c]; rfl
  have hK : (limit (Functor.ofOpSequence g)).IsKInjective :=
    isKInjective_limit_of_inverseSystem (Functor.ofOpSequence g) (fun n => by
      let : (I n).IsStrictlyGE (-(n : ℤ)) := hGE n
      let : ∀ i : ℤ, Injective ((I n).X i) := hI n
      exact CochainComplex.isKInjective_of_injective (I n) (-(n : ℤ)))
      (by intro n i; rw [Functor.ofOpSequence_map_homOfLE_succ]; exact hsplit' n i)
  exact ⟨{
    I := I, f := f, g := g, quasiIso_f := hf,
    strictlyGE_I := hGE, injective_I := hI, splitEpi_g := hsplit',
    ladder := hcomm, kInjective_limit := hK, canonicalMap := q,
    canonicalMap_comp_π := hq,
    canonicalMap_unique := fun γ hγ => limit.hom_ext fun ⟨n⟩ => (hγ n).trans (hq n).symm }⟩

end Stacks.KInjective
