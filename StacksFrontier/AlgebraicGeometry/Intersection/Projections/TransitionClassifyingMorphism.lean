module

public import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsPointValue
public import StacksFrontier.AlgebraicGeometry.Constructions.GeneratingSectionsRestrict
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionClassifyingSections

/-!
# The classifying morphism to the parameter space of Tag 0B1S

`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionSections` is the linear system

`ψ : (End V)ᵛ → Γ(𝒪(1,1), ⊤)`

on the source `X × Y × 𝔸(c, u, u', w, h)` of the bilinear parametrisation, whose value at a
`k`-point is `φ ↦ φ(G)` for `G` the endomorphism
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd` that point's data produces. This file
feeds it to clause (5) of [Stacks, Tag 0FCY] and gets the classifying morphism

`Φ : U ⟶ 𝐏 = 𝐏((End V)ᵛ)`

whose value at a point is the parameter point of `G`.

**The morphism is defined on an open, not on the source.** Clause (5) of Tag 0FCY asks the values
of the system to generate everywhere, and these do not: `G` vanishes identically at `c = 0`,
`w = 0`, and there `every` `ψ(φ)` vanishes. The locus the morphism exists on is exactly

`U = ⨆_φ (source)_{ψ(φ)}`,

the locus where `G ≠ 0`, and the restriction of the system to it is the `k`-linear map
`Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackSectionsₗ` composed with `ψ`. Every
statement downstream of `Φ` is therefore phrased on `U`; the loss is nothing, `U` being a nonempty
open of the irreducible source and hence irreducible with the same generic point.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifyingOpen`: the open `U`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifyingModule`: `𝒪(1,1)|_U`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifyingSystem`: the restriction of `ψ`
  to `U`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifying`: the morphism `Φ`.

## Main results

* `…ProjectiveSpaceOfModule.iSup_nonvanishingOpen_transitionClassifyingSystem_eq_top`: the
  restricted system generates on `U` — the hypothesis clause (5) of Tag 0FCY consumes.
* `…ProjectiveSpaceOfModule.mem_transitionClassifyingOpen_of_transitionEnd_ne_zero`: a `k`-point
  of the source at which the parametrisation is nonzero lies in `U`.
* `…ProjectiveSpaceOfModule.transitionClassifying_base_eq`: **the value of `Φ` at a `k`-point of
  the source is the parameter point of `G`**, read as in
  `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`:
  the point of `𝐏` cut out by a functional `f₃` on `(End V)ᵛ` which is evaluation at `G`.
* `…ProjectiveSpaceOfModule.irreducibleSpace_transitionClassifyingOpen`: `U` is irreducible when
  `X` and `Y` are and `U` is nonempty.

## Implementation notes

**Why the parameter point is named by a functional on `(End V)ᵛ` rather than by `G` itself.** The
value of a morphism into `𝐏(W)` that the library computes is
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections_base_eq`,
which produces `AlgebraicGeometry.ProjectiveSpaceOfModule.linearFunctionalPoint` of a nonzero
functional on `W`. Here `W = (End V)ᵛ`, so the functional is an element of `(End V)ᵛᵛ`, and the
statement carries it together with the hypothesis that it is evaluation at `G` — exactly the
spelling
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`
already uses for a parameter point of the correspondence, so the two meet with no bridge. No
identification of `(End V)ᵛᵛ` with `End V` is needed or made.

**The structure morphism of `U`.** `U.toScheme` is given the structure morphism
`U.ι ≫ transitionSourceToSpec` as an instance, which is what makes the compatibility hypothesis of
`Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackSectionsₗ` hold by `rfl`. Choosing
the structure map so that the identity it is used through is definitional is the same move that
dissolves the `h₁` of the source's projections, the `closedSubschemeOfToSpec` rewrite and
the `baseRingHom`/`scalarTop` mismatch.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule
  morphismOfGeneratingSections morphismOfGeneratingSections_base_eq)
open Stacks.AlgebraicGeometry.GeneratingSectionsRestrict (pullbackSectionsₗ
  pullbackSectionsₗ_apply nonvanishingOpen_pullbackGlobalSections
  iSup_nonvanishingOpen_pullbackGlobalSections_eq_top)
open Stacks.NonvanishingOpen (nonvanishingOpen)

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

attribute [local instance] isInvertible_tautologicalModule globalSectionsModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)
  (b : Module.Basis (Fin (Module.finrank k V)) k V)

/-! ### The open on which the classifying morphism is defined -/

/-- **The locus on which the classifying morphism of Tag 0B1S is defined**: the union of the
nonvanishing opens of the linear system. By
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingOpen_transitionSections_point_iff` it
is the locus where the parametrisation `G` is nonzero, which is not all of the source — `G`
vanishes at `c = 0, w = 0`. -/
public def transitionClassifyingOpen : (transitionSource k V X Y hXc hYc).Opens :=
  ⨆ φ : Module.Dual k (V →ₗ[k] V), nonvanishingOpen (transitionSource k V X Y hXc hYc)
    (transitionPairTaut k V X Y hXc hYc) (transitionSections k V X Y hXc hYc b φ)

/-- A point of the source lies in the locus exactly when some value of the linear system is
nonvanishing there. -/
public theorem mem_transitionClassifyingOpen_iff (t : transitionSource k V X Y hXc hYc) :
    t ∈ transitionClassifyingOpen k V X Y hXc hYc b ↔
      ∃ φ : Module.Dual k (V →ₗ[k] V), t ∈ nonvanishingOpen (transitionSource k V X Y hXc hYc)
        (transitionPairTaut k V X Y hXc hYc) (transitionSections k V X Y hXc hYc b φ) :=
  Opens.mem_iSup

/-- **The locus is a scheme over the ground field**, through the inclusion followed by the
structure morphism of the source. This is the choice that makes the compatibility hypothesis of
`Stacks.AlgebraicGeometry.GeneratingSectionsRestrict.pullbackSectionsₗ` hold by `rfl`. -/
public instance over_transitionClassifyingOpen :
    (transitionClassifyingOpen k V X Y hXc hYc b).toScheme.Over (Spec (CommRingCat.of k)) :=
  ⟨(transitionClassifyingOpen k V X Y hXc hYc b).ι ≫ transitionSourceToSpec k V X Y hXc hYc⟩

/-- `↘ Spec k` on the locus is the composite it was given. -/
public theorem transitionClassifyingOpen_over_eq :
    (transitionClassifyingOpen k V X Y hXc hYc b).toScheme ↘ Spec (CommRingCat.of k) =
      (transitionClassifyingOpen k V X Y hXc hYc b).ι ≫
        transitionSourceToSpec k V X Y hXc hYc := rfl

/-- **The restriction `𝒪(1,1)|_U` of the invertible module to the locus.** -/
public abbrev transitionClassifyingModule :
    (transitionClassifyingOpen k V X Y hXc hYc b).toScheme.Modules :=
  (Scheme.Modules.pullback (transitionClassifyingOpen k V X Y hXc hYc b).ι).obj
    (transitionPairTaut k V X Y hXc hYc)

/-- **The restriction of the linear system to the locus**, as a `k`-linear map: the system
composed with the `k`-linear pullback of global sections along the inclusion. -/
public def transitionClassifyingSystem :
    Module.Dual k (V →ₗ[k] V) →ₗ[k] Γ(transitionClassifyingModule k V X Y hXc hYc b, ⊤) :=
  (pullbackSectionsₗ k (transitionClassifyingOpen k V X Y hXc hYc b).ι
    (transitionPairTaut k V X Y hXc hYc) rfl).comp (transitionSections k V X Y hXc hYc b)

/-- The restricted system is the pullback of the system, value by value. -/
public theorem transitionClassifyingSystem_apply (φ : Module.Dual k (V →ₗ[k] V)) :
    transitionClassifyingSystem k V X Y hXc hYc b φ =
      pullbackGlobalSections (transitionClassifyingOpen k V X Y hXc hYc b).ι
        (transitionPairTaut k V X Y hXc hYc) (transitionSections k V X Y hXc hYc b φ) := rfl

/-- **The nonvanishing open of a value of the restricted system** is the part of the
corresponding nonvanishing open of the system that lies in the locus. This is [Stacks, Tag
0H78]. -/
public theorem nonvanishingOpen_transitionClassifyingSystem (φ : Module.Dual k (V →ₗ[k] V)) :
    nonvanishingOpen (transitionClassifyingOpen k V X Y hXc hYc b).toScheme
        (transitionClassifyingModule k V X Y hXc hYc b)
        (transitionClassifyingSystem k V X Y hXc hYc b φ) =
      (transitionClassifyingOpen k V X Y hXc hYc b).ι ⁻¹ᵁ
        nonvanishingOpen (transitionSource k V X Y hXc hYc)
          (transitionPairTaut k V X Y hXc hYc) (transitionSections k V X Y hXc hYc b φ) :=
  nonvanishingOpen_pullbackGlobalSections (transitionClassifyingOpen k V X Y hXc hYc b).ι
    (transitionPairTaut k V X Y hXc hYc) (transitionSections k V X Y hXc hYc b φ)

/-- **The restricted system generates on the locus** — the hypothesis that clause (5) of
[Stacks, Tag 0FCY] consumes. The locus is by definition the union of the nonvanishing opens of
the system, and each nonvanishing open of the restricted system is the part of the corresponding
one lying in the locus. -/
public theorem iSup_nonvanishingOpen_transitionClassifyingSystem_eq_top :
    (⨆ φ : Module.Dual k (V →ₗ[k] V),
      nonvanishingOpen (transitionClassifyingOpen k V X Y hXc hYc b).toScheme
        (transitionClassifyingModule k V X Y hXc hYc b)
        (transitionClassifyingSystem k V X Y hXc hYc b φ)) = ⊤ :=
  iSup_nonvanishingOpen_pullbackGlobalSections_eq_top (transitionPairTaut k V X Y hXc hYc)
    (fun φ : Module.Dual k (V →ₗ[k] V) => transitionSections k V X Y hXc hYc b φ) le_rfl

/-! ### The classifying morphism -/

/-- **The classifying morphism `Φ : U ⟶ 𝐏` of Tag 0B1S**: the morphism of clause (5) of
[Stacks, Tag 0FCY] attached to the restriction to `U` of the linear system of the bilinear
parametrisation. Its value at a `k`-point of the source is the parameter point of the
endomorphism the parametrisation produces there,
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionClassifying_base_eq`. -/
public def transitionClassifying :
    (transitionClassifyingOpen k V X Y hXc hYc b).toScheme ⟶
      projectiveSpaceOfModule k (ParameterModule k V) :=
  morphismOfGeneratingSections k (Module.Dual k (V →ₗ[k] V))
    (transitionClassifyingModule k V X Y hXc hYc b)
    (transitionClassifyingSystem k V X Y hXc hYc b)
    (iSup_nonvanishingOpen_transitionClassifyingSystem_eq_top k V X Y hXc hYc b)

/-! ### Where a `k`-point of the source goes -/

section Point

variable {k V X Y} {hXc hYc} {b}

/-- **A `k`-point of the source at which the parametrisation is nonzero lies in the locus.** A
nonzero endomorphism is not killed by every functional, and by the closed form of the
nonvanishing criterion the value of the system at such a functional is nonvanishing there. -/
public theorem mem_transitionClassifyingOpen_of_transitionEnd_ne_zero
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (hpt : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (a : Spec (CommRingCat.of k))
    (f : Module.Dual k V) (hf : f ≠ 0)
    (e₁ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
      linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (e₂ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
      linearFunctionalPoint k V f' hf')
    (hG : transitionEnd k V f f' c u u' w h ≠ 0) :
    (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a ∈
      transitionClassifyingOpen k V X Y hXc hYc b := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k (V →ₗ[k] V),
      φ (transitionEnd k V f f' c u u' w h) ≠ 0 :=
    not_forall.mp fun hall =>
      hG ((Module.forall_dual_apply_eq_zero_iff k (transitionEnd k V f f' c u u' w h)).mp hall)
  refine (mem_transitionClassifyingOpen_iff k V X Y hXc hYc b _).mpr ⟨φ, ?_⟩
  exact (mem_nonvanishingOpen_transitionSections_point_iff k V X Y hXc hYc b pt hpt c u u' w h a
    f hf e₁ f' hf' e₂ φ).mpr hφ

/-- **The value of the classifying morphism at a `k`-point of the source is the parameter point
of `G`.** The point of `𝐏 = 𝐏((End V)ᵛ)` is named by a nonzero functional `f₃` on `(End V)ᵛ`
which is evaluation at `G = transitionEnd f f' c u u' w h`, which is the spelling
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint` uses
for a parameter point of the correspondence.

Only one direction of the nonvanishing criterion is used — that a functional killing `G` has a
vanishing section — because
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections_base_eq`
asks only that much. -/
public theorem transitionClassifying_base_eq
    (pt : Spec (CommRingCat.of k) ⟶ prodOfClosed k V X Y hXc hYc)
    (hpt : pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfToSpec k V X hXc = 𝟙 _)
    (c : k) (u u' w : V) (h : V →ₗ[k] V) (a : Spec (CommRingCat.of k))
    (f : Module.Dual k V) (hf : f ≠ 0)
    (e₁ : (pt ≫ pullback.fst (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V X hXc).base a =
      linearFunctionalPoint k V f hf)
    (f' : Module.Dual k V) (hf' : f' ≠ 0)
    (e₂ : (pt ≫ pullback.snd (closedSubschemeOfToSpec k V X hXc)
      (closedSubschemeOfToSpec k V Y hYc) ≫ closedSubschemeOfι k V Y hYc).base a =
      linearFunctionalPoint k V f' hf')
    (x : (transitionClassifyingOpen k V X Y hXc hYc b).toScheme)
    (hx : (transitionClassifyingOpen k V X Y hXc hYc b).ι.base x =
      (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a)
    (f₃ : Module.Dual k (ParameterModule k V)) (hf₃ : f₃ ≠ 0)
    (hf₃G : ∀ φ : ParameterModule k V, f₃ φ = φ (transitionEnd k V f f' c u u' w h)) :
    (transitionClassifying k V X Y hXc hYc b).base x =
      linearFunctionalPoint k (ParameterModule k V) f₃ hf₃ := by
  refine morphismOfGeneratingSections_base_eq k (Module.Dual k (V →ₗ[k] V))
    (transitionClassifyingModule k V X Y hXc hYc b)
    (transitionClassifyingSystem k V X Y hXc hYc b)
    (iSup_nonvanishingOpen_transitionClassifyingSystem_eq_top k V X Y hXc hYc b) x hf₃
    fun φ hφ hmem => ?_
  rw [nonvanishingOpen_transitionClassifyingSystem k V X Y hXc hYc b φ] at hmem
  have hmem' : (transitionSourcePoint k V X Y hXc hYc b pt c u u' w h).base a ∈
      nonvanishingOpen (transitionSource k V X Y hXc hYc)
        (transitionPairTaut k V X Y hXc hYc) (transitionSections k V X Y hXc hYc b φ) := by
    rw [← hx]
    exact hmem
  refine ((mem_nonvanishingOpen_transitionSections_point_iff k V X Y hXc hYc b pt hpt c u u' w h a
    f hf e₁ f' hf' e₂ φ).mp hmem') ?_
  rw [← hf₃G φ]
  exact hφ

end Point

/-! ### Irreducibility of the locus -/

/-- **The locus is irreducible** when `X` and `Y` are and it is nonempty: a nonempty open
subspace of an irreducible space is irreducible. So the generic point of the source lies in the
locus and nothing is lost by phrasing the construction there. -/
public theorem irreducibleSpace_transitionClassifyingOpen [IsAlgClosed k]
    (hXirr : IsIrreducible X) (hYirr : IsIrreducible Y)
    [Nonempty (transitionClassifyingOpen k V X Y hXc hYc b).toScheme] :
    IrreducibleSpace (transitionClassifyingOpen k V X Y hXc hYc b).toScheme :=
  have : IrreducibleSpace (transitionSource k V X Y hXc hYc) :=
    irreducibleSpace_transitionSource k V X Y hXc hYc hXirr hYirr
  (transitionClassifyingOpen k V X Y hXc hYc b).ι.isOpenEmbedding.irreducibleSpace

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
