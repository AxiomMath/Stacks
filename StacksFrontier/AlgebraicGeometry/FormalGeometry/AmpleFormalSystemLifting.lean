module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.AmplePowers.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison

/-!
# Lifting the embedding sections through the thickenings

In the proof of Grothendieck's algebraization theorem ([Stacks, Tag 089A]) the vanishing of
`H¹(X₁, 𝓕ₙ ⊗ ℒ₁^{⊗d})` makes the transition maps on global sections of the `ℒₙ^{⊗d}` surjective,
and the sections `s_{0,1}, …, s_{N,1}` that embed `X₁` are lifted inductively to sections
`s_{0,n}, …, s_{N,n}` of `ℒₙ^{⊗d}`. This file carries out that lifting, and packages its output
in the form the rest of the proof consumes.

Two things have to be produced: the sections, and the fact that at every level they still
*generate*. The first is a recursion on `ℕ` using the surjectivity of the transition maps. The
second is free, and for a reason that has nothing to do with cohomology: the nonvanishing locus
of a pulled-back section is the preimage of the nonvanishing locus
([Stacks, Tag 0H78], an *equality* of loci, not merely an inclusion), and the transition maps
`Xₙ ⟶ X_{n+1}` of the tower are surjective on points. So a family generating at one level
generates at the next, and generation propagates up the tower from `s_{•,1}`.

## Main results

* `Stacks.AmpleFormalSystemLifting.generatesStalks_congr` — generation transports along an
  isomorphism of modules carrying one family of sections to the other.
* `Stacks.AmpleFormalSystemLifting.generatesStalks_of_surjective_base` — generation lifts along
  a morphism which is surjective on points.
* `Stacks.AmpleFormalSystemLifting.exists_sectionTower` — the inductive lifting itself: from
  surjective transition maps on global sections and a family at the bottom, a compatible family
  at every level.
* `Stacks.AmpleFormalSystemLifting.exists_generatingTupleTower` — the two together, in the shape
  `Stacks.AmpleFormalSystemSections.isPullback_adicLift_tupleHom` consumes: a tower of generating
  tuples compatible under pullback, restricting to the given one at the bottom.

## Implementation notes

The sections are carried as `Stacks.ProjectiveSpaceModuli.GeneratingTuple`s, which bundle the
module, its invertibility and the generation of the family. That is the form in which the
identification of [Stacks, Tag 01NE] is stated, and the compatibility of the sections under the
transition maps is then exactly `Stacks.ProjectiveSpaceModuli.Isomorphic` between the pullback of
the tuple at level `n + 1` and the tuple at level `n` — which is literally the tuple-level
reading of `φₙ : iₙ^* ℒ_{n+1} ≅ ℒₙ` carrying lifted sections to the sections below.

Nothing in this file knows where the surjectivity of the transition maps on global sections comes
from; it is a hypothesis. In the proof of [Stacks, Tag 089A] it comes from the vanishing of
`H¹(X₁, 𝓕ₙ ⊗ ℒ₁^{⊗d})` through the long exact sequence of
`0 ⟶ 𝓕ₙ ⊗ ℒ₁^{⊗d} ⟶ ℒ_{n+1}^{⊗d} ⟶ ℒₙ^{⊗d} ⟶ 0`.

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli
open Stacks.AmpleImmersionReduction

universe u v

namespace Stacks.AmpleFormalSystemLifting

/-! ### Generation transports along an isomorphism -/

/-- **Generation transports along an isomorphism of modules** carrying one family of global
sections to the other: the two families have the same nonvanishing loci,
`Stacks.Ample.nonvanishingLocus_congr`. -/
public lemma generatesStalks_congr {X : Scheme.{u}} {M N : X.Modules}
    [IsInvertibleModule X M] [IsInvertibleModule X N] (e : M ≅ N) {ι : Type v}
    (s : ι → Γ(M, ⊤)) (hs : GeneratesStalks s) :
    GeneratesStalks fun k => Scheme.Modules.Hom.app e.hom ⊤ (s k) := by
  refine (generatesStalks_iff_forall_exists_mem _).2 fun x => ?_
  obtain ⟨k, hk⟩ := (generatesStalks_iff_forall_exists_mem s).1 hs x
  refine ⟨k, ?_⟩
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, nonvanishingLocus_congr e (s k)]
  exact hk

/-! ### Generation lifts along a morphism surjective on points -/

/-- The two spellings of the pullback of a global section agree. -/
public lemma pullbackGlobalSections_eq_pullbackGlobalSection {X Y : Scheme.{u}} (h : Y ⟶ X)
    (M : X.Modules) (t : Γ(M, ⊤)) :
    pullbackGlobalSections h M t = Stacks.NonvanishingPullback.pullbackGlobalSection h M t := by
  change ((Scheme.Modules.pullback h).obj M).presheaf.map
      (eqToHom (show h ⁻¹ᵁ (⊤ : X.Opens) = ⊤ from rfl)).op
      (Stacks.NonvanishingPullback.pullbackGlobalSection h M t) = _
  exact Functor.map_id_apply _ _ _

/-- **Generation lifts along a morphism surjective on points.** If the pullbacks of a family of
global sections generate upstairs and the morphism is surjective, the family generates
downstairs: by [Stacks, Tag 0H78] the nonvanishing locus of a pulled-back section is exactly the
preimage of the nonvanishing locus, so a point downstairs is covered as soon as one of its
preimages is. -/
public lemma generatesStalks_of_surjective_base {X Y : Scheme.{u}} (h : Y ⟶ X)
    (hsurj : Function.Surjective h.base) (M : X.Modules) [IsInvertibleModule X M] {ι : Type v}
    (s : ι → Γ(M, ⊤))
    (hs : GeneratesStalks fun k => pullbackGlobalSections h M (s k)) :
    GeneratesStalks s := by
  let : IsInvertibleModule Y ((Scheme.Modules.pullback h).obj M) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback h M
  refine (generatesStalks_iff_forall_exists_mem s).2 fun x => ?_
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨k, hk⟩ := (generatesStalks_iff_forall_exists_mem _).1 hs y
  refine ⟨k, ?_⟩
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen] at hk ⊢
  have hk' : y ∈ nonvanishingLocus ((Scheme.Modules.pullback h).obj M)
      (Stacks.NonvanishingPullback.pullbackGlobalSection h M (s k)) := by
    rw [← pullbackGlobalSections_eq_pullbackGlobalSection h M (s k)]
    exact hk
  exact (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff h M (s k) y).1 hk'

/-- Applying an isomorphism of modules to a global section and then its inverse is the
identity. -/
public lemma app_inv_app_hom {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (x : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app e.inv ⊤ (Scheme.Modules.Hom.app e.hom ⊤ x) = x := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply,
    show Scheme.Modules.Hom.app e.hom ⊤ ≫ Scheme.Modules.Hom.app e.inv ⊤ =
      Scheme.Modules.Hom.app (e.hom ≫ e.inv) ⊤ from rfl, e.hom_inv_id]
  simp

/-! ### The inductive lifting -/

variable {Xn : ℕ → Scheme.{u}} (i : ∀ n, Xn n ⟶ Xn (n + 1)) (M : ∀ n, (Xn n).Modules)
  (θ : ∀ n, (Scheme.Modules.pullback (i n)).obj (M (n + 1)) ≅ M n)

/-- The transition map on global sections of the tower: pull back along `iₙ` and read the result
through `θₙ`. -/
public def transitionSections (n : ℕ) (σ : Γ(M (n + 1), ⊤)) : Γ(M n, ⊤) :=
  Scheme.Modules.Hom.app (θ n).hom ⊤ (pullbackGlobalSections (i n) (M (n + 1)) σ)

/-- **The inductive lifting of a family of global sections through the tower.** If every
transition map on global sections is surjective then a family at the bottom extends to a
compatible family at every level. -/
public lemma exists_sectionTower
    (hres : ∀ n, Function.Surjective (transitionSections i M θ n))
    {ι : Type v} (s₀ : ι → Γ(M 0, ⊤)) :
    ∃ s : ∀ n, ι → Γ(M n, ⊤), s 0 = s₀ ∧
      ∀ (n : ℕ) (k : ι), transitionSections i M θ n (s (n + 1) k) = s n k := by
  choose g hg using fun n => hres n
  refine ⟨fun n => Nat.rec (motive := fun m => ι → Γ(M m, ⊤)) s₀
    (fun m sm k => g m (sm k)) n, rfl, fun n k => hg n _⟩

/-! ### The tower of generating tuples -/

/-- **The lifted sections generate at every level, and form a compatible tower of generating
tuples.**

Let `Xₙ` be a tower whose transition maps are surjective on points, let `ℒₙ` be invertible
modules on the `Xₙ` with isomorphisms `θₙ : iₙ^* ℒ_{n+1} ≅ ℒₙ`, assume the induced transition
maps on global sections are surjective, and let `s₀` be a generating family of `N + 1` global
sections of `ℒ₀`. Then there is a tower of generating tuples `tₙ` on the `Xₙ`, compatible under
pullback, whose bottom member is `(ℒ₀, s₀)`.

This is the source's "The vanishing of `H¹(X, 𝓕ₙ ⊗ ℒ₁^{⊗d})` implies we can inductively lift
`s_{0,1}, …, s_{N,1}` to sections `s_{0,n}, …, s_{N,n}`", together with the fact — free from
[Stacks, Tag 0H78] and surjectivity — that the lifts still generate. -/
public lemma exists_generatingTupleTower (hsurj : ∀ n, Function.Surjective (i n).base)
    (hM : ∀ n, IsInvertibleModule (Xn n) (M n))
    (hres : ∀ n, Function.Surjective (transitionSections i M θ n))
    (N : ℕ) (s₀ : Fin (N + 1) → Γ(M 0, ⊤)) (hs₀ : GeneratesStalks s₀) :
    ∃ t : ∀ n, GeneratingTuple (Xn n) N,
      (∀ n, Isomorphic (pullbackTuple (i n) (t (n + 1))) (t n)) ∧
        Isomorphic (t 0) ⟨M 0, hM 0, s₀, hs₀⟩ := by
  obtain ⟨s, hs0, hstep⟩ := exists_sectionTower i M θ hres s₀
  have hgen : ∀ n, GeneratesStalks (s n) := by
    intro n
    induction n with
    | zero => rw [hs0]; exact hs₀
    | succ n ih =>
      let := hM n
      let := hM (n + 1)
      let : IsInvertibleModule (Xn n) ((Scheme.Modules.pullback (i n)).obj (M (n + 1))) :=
        Stacks.InvertiblePullback.isInvertibleModule_pullback (i n) (M (n + 1))
      refine generatesStalks_of_surjective_base (i n) (hsurj n) (M (n + 1)) (s (n + 1)) ?_
      have h := generatesStalks_congr (θ n).symm (s n) ih
      have heq : (fun k => Scheme.Modules.Hom.app (θ n).symm.hom ⊤ (s n k)) =
          fun k => pullbackGlobalSections (i n) (M (n + 1)) (s (n + 1) k) := by
        funext k
        rw [← hstep n k]
        exact app_inv_app_hom (θ n) _
      rwa [heq] at h
  refine ⟨fun n => ⟨M n, hM n, s n, hgen n⟩, fun n => ⟨θ n, hstep n⟩,
    Iso.refl _, fun k => ?_⟩
  let := hM 0
  simp [hs0]

end Stacks.AmpleFormalSystemLifting

end
