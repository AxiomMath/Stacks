module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.GorensteinGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.IntersectionPairing
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentCartier
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeDivisibility

/-!
# The components of the special fibre are proper curves over the residue field

Let `X` be a regular model of a smooth curve over a discrete valuation ring `R` with residue
field `k`, and let `C ⊆ X_k` be an irreducible component of the special fibre, taken with its
reduced induced structure as a closed subscheme of `X` as in
`Stacks.Models.RegularModelSituation.specialFiberComponentIdeal`. This file constructs the
canonical structure morphism `C ⟶ Spec(k)` and proves the two properties of it that the
intersection theory of a regular proper model consumes: it is proper when the model is, and the
space of `C` has topological Krull dimension at most one. In other words each component of the
special fibre is a proper curve over `k`.

Both properties were previously carried as hypotheses by every construction in Section 55.9 —
see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Curves/Models/IntersectionPairing.lean` — so the two results here
are what lets a caller apply those constructions to the components of the special fibre instead
of to an abstract closed subscheme with properness and dimension assumed.

## Main definitions

* `Stacks.Models.RegularModelSituation.specialFiberComponentι` — the closed immersion of a
  component of the special fibre into the special fibre `X_k`.
* `Stacks.Models.RegularModelSituation.specialFiberComponentToSpec` — the canonical structure
  morphism `C ⟶ Spec(k)` of a component of the special fibre, namely the previous closed
  immersion followed by the structure morphism of `X_k`.
* `Stacks.Models.RegularProperModelSituation.specialFiberComponentDegree` — the degree
  `deg(ℒ|_C)` of an invertible module restricted to a component of the special fibre, i.e.
  `Stacks.Models.componentDegree` with its properness and dimension hypotheses discharged.
* `Stacks.Models.RegularProperModelSituation.specialFiberDegreePairing` — the degree pairing of
  [Stacks, Tag 0C64] over the components of the special fibre, i.e.
  `Stacks.Models.degreePairing` with its three hypotheses on the family discharged.

## Main results

* `Stacks.Models.RegularModelSituation.topologicalKrullDim_specialFiberComponent` — a component
  of the special fibre has topological Krull dimension at most one.
* `Stacks.Models.RegularProperModelSituation.isProper_specialFiberComponentToSpec` — for a
  regular *proper* model the structure morphism of a component is proper.
* `Stacks.Models.RegularProperModelSituation`'s
  `isField_and_finite_globalSections_specialFiberComponent` — consequently `κ_C = Γ(C, 𝒪_C)` is
  a field, finite over `k`.

## The argument

*The structure morphism.* A component is contained in the special fibre, so its reduced ideal
sheaf contains the ideal sheaf `ℐ_{X_k}` cut out by `X_k`: that is
`specialFiberIdeal_le_specialFiberComponentIdeal`, proved through the Galois connection between
`support` and `vanishingIdeal`. Hence `Scheme.IdealSheafData.inclusion` gives a closed immersion
of the component into `ℐ_{X_k}.subscheme`, which is identified with the pullback `X_k` by
`Scheme.Hom.toImage` — an isomorphism because `X_k ⟶ X` is a closed immersion. Composing with
the second projection `X_k ⟶ Spec(k)` gives the structure morphism, and
`specialFiberComponentToSpec_comp` records that it is the canonical one: it agrees over
`Spec(R)` with the composite of the closed immersion of the component into `X` and the model
morphism.

*Properness.* The structure morphism of `X_k` is a base change of the model morphism, so it is
proper when the model is, and a closed immersion is proper; properness is stable under
composition.

*Dimension.* The special fibre, being the pullback along `Spec(k) ⟶ Spec(R)`, is homeomorphic to
the scheme-theoretic fibre of the model over the closed point of `Spec(R)`: both have the same
image in `X`, by `AlgebraicGeometry.Scheme.Pullback.range_fst` and
`AlgebraicGeometry.Scheme.Hom.fiberHomeo`, because `Spec(k)` is a one-point space. That fibre
is one-dimensional by part (1) of Tag 0C60,
`Stacks.Models.RegularModelSituation.relativeDimension_model`, and the component embeds in it.

## Implementation notes

**No Stacks tag is attached.** The statement that the components of the special fibre are proper
curves over `k` is used freely in Section 55.9 but is not the content of a tag: the four clauses
of [Stacks, Tag 0C5Z] concern only the divisorial structure of `X_k` and its components, and
Situation [Stacks, Tag 0C61] introduces `C₁, …, Cₙ` as the irreducible components of `X_k`
without asserting anything about them. Rather than attach a tag whose statement these results do
not prove, they carry none.

**The dimension bound on a component is an inequality, not an equality.** A component has
dimension exactly one: the fibre is *equidimensional* of dimension one by Tag 0C60, which is the
other clause of `Stacks.Models.RegularModelSituation.relativeDimension_model`, and every
irreducible component of an equidimensional space has the dimension of the space. Deducing it
would mean transporting the component `Z` of the pullback `X_k` along the homeomorphism used
below onto an irreducible component of that fibre; only `≤ 1` is proved here, since `≤ 1` is what
`AlgebraicGeometry.invertibleCurveDegree` and `Stacks.Models.componentDegree` consume, and the
closed immersion of the component into `X_k` gives it directly.

**Nonemptiness.** `topologicalKrullDim_specialFiber` takes `Nonempty X_k` as a hypothesis rather
than deriving it: the model morphism of a regular model need not be surjective without further
hypotheses, and the application below supplies the point from the component itself, an
irreducible component being nonempty.

## References

* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C60](https://stacks.math.columbia.edu/tag/0C60)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- The ideal sheaf cutting out the special fibre is contained in the reduced ideal sheaf of one
of its irreducible components: the component is contained in the special fibre, and the
containment of closed subsets is the containment of ideal sheaves the other way round. -/
public theorem specialFiberIdeal_le_specialFiberComponentIdeal
    (Z : irreducibleComponents S.specialFiber) :
    S.specialFiberIdeal ≤ S.specialFiberComponentIdeal Z := by
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 ?_
  intro x hx
  rw [← SetLike.mem_coe, S.coe_closure_image_specialFiberComponent Z] at hx
  rw [← SetLike.mem_coe, S.coe_support_specialFiberIdeal]
  exact Set.image_subset_range _ _ hx

/-- The closed immersion of an irreducible component of the special fibre, with its reduced
induced structure, into the special fibre `X_k`. -/
public def specialFiberComponentι (Z : irreducibleComponents S.specialFiber) :
    (S.specialFiberComponentIdeal Z).subscheme ⟶ S.specialFiber :=
  Scheme.IdealSheafData.inclusion (S.specialFiberIdeal_le_specialFiberComponentIdeal Z) ≫
    (asIso S.specialFiberι.toImage).inv

/-- The inclusion `specialFiberComponentι Z` of a component into the special fibre is a closed
immersion. -/
public instance isClosedImmersion_specialFiberComponentι
    (Z : irreducibleComponents S.specialFiber) :
    IsClosedImmersion (S.specialFiberComponentι Z) := by
  change IsClosedImmersion
    (Scheme.IdealSheafData.inclusion (S.specialFiberIdeal_le_specialFiberComponentIdeal Z) ≫
      (asIso S.specialFiberι.toImage).inv)
  infer_instance

/-- The closed immersion of a component into the special fibre, followed by the closed immersion
of the special fibre into the model, is the closed immersion of the component into the model. -/
public theorem specialFiberComponentι_specialFiberι
    (Z : irreducibleComponents S.specialFiber) :
    S.specialFiberComponentι Z ≫ S.specialFiberι =
      (S.specialFiberComponentIdeal Z).subschemeι := by
  have he : (asIso S.specialFiberι.toImage).hom ≫ S.specialFiberIdeal.subschemeι =
      S.specialFiberι := S.specialFiberι.toImage_imageι
  have hinv : (asIso S.specialFiberι.toImage).inv ≫ S.specialFiberι =
      S.specialFiberIdeal.subschemeι := (Iso.inv_comp_eq _).2 he.symm
  change (Scheme.IdealSheafData.inclusion (S.specialFiberIdeal_le_specialFiberComponentIdeal Z) ≫
      (asIso S.specialFiberι.toImage).inv) ≫ S.specialFiberι = _
  rw [Category.assoc, hinv, Scheme.IdealSheafData.inclusion_subschemeι]

/-- **The structure morphism of an irreducible component of the special fibre over the residue
field.** A component of `X_k`, with its reduced induced structure as a closed subscheme of the
model, is a scheme over `k` through its closed immersion into `X_k`. -/
public def specialFiberComponentToSpec (Z : irreducibleComponents S.specialFiber) :
    (S.specialFiberComponentIdeal Z).subscheme ⟶ Spec (.of S.k) :=
  S.specialFiberComponentι Z ≫ S.specialFiberToSpec

/-- The structure morphism of a component over `k` is the canonical one: composed with
`Spec(k) ⟶ Spec(R)` it is the closed immersion of the component into the model followed by the
model morphism. -/
public theorem specialFiberComponentToSpec_comp (Z : irreducibleComponents S.specialFiber) :
    S.specialFiberComponentToSpec Z ≫ Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) =
      (S.specialFiberComponentIdeal Z).subschemeι ≫ S.X_to_R := by
  change (S.specialFiberComponentι Z ≫ S.specialFiberToSpec) ≫
    Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) = _
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    S.specialFiberComponentι_specialFiberι Z]

/-- **The special fibre of a regular model is one-dimensional.** It is homeomorphic to the
scheme-theoretic fibre of the model over the closed point of `Spec(R)`, because both have the
same image in `X` and `Spec(k)` is a one-point space, and that fibre is one-dimensional by part
(1) of Tag 0C60. -/
public theorem topologicalKrullDim_specialFiber (hne : Nonempty S.specialFiber) :
    topologicalKrullDim S.specialFiber = (1 : WithBot ℕ∞) := by
  obtain ⟨pt⟩ : Nonempty (Spec (.of S.k)) := inferInstance
  set q : Spec (.of S.R) := (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))).base pt
  have hrangeg : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))).base = {q} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨pt, rfl⟩, ?_⟩
    rintro x ⟨z, rfl⟩
    exact congrArg _ (Subsingleton.elim z pt)
  have hfst := Scheme.Pullback.range_fst S.X_to_R
    (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))
  rw [hrangeg] at hfst
  have hrange : Set.range S.specialFiberι.base = S.X_to_R.base ⁻¹' {q} := hfst
  have hhomeo : S.specialFiber ≃ₜ S.X_to_R.fiber q :=
    (S.specialFiberι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)).trans (S.X_to_R.fiberHomeo q).symm
  obtain ⟨-, hdim⟩ := S.relativeDimension_model q (hne.map hhomeo)
  rw [IsHomeomorph.topologicalKrullDim_eq _ hhomeo.isHomeomorph]
  exact hdim

/-- **An irreducible component of the special fibre of a regular model has dimension at most
one.** It is a closed subscheme of the special fibre, which is one-dimensional. -/
public theorem topologicalKrullDim_specialFiberComponent
    (Z : irreducibleComponents S.specialFiber) :
    topologicalKrullDim (S.specialFiberComponentIdeal Z).subscheme ≤ (1 : WithBot ℕ∞) := by
  obtain ⟨w, -⟩ := Z.2.1.nonempty
  have hle : topologicalKrullDim (S.specialFiberComponentIdeal Z).subscheme ≤
      topologicalKrullDim S.specialFiber :=
    (S.specialFiberComponentι Z).isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  rw [S.topologicalKrullDim_specialFiber ⟨w⟩] at hle
  exact hle

end RegularModelSituation

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The structure morphism of an irreducible component of the special fibre of a regular proper
model is proper.** The structure morphism of the special fibre is a base change of the proper
model morphism, the component is a closed subscheme of the special fibre, and properness is
stable under composition. -/
public instance isProper_specialFiberComponentToSpec
    (Z : irreducibleComponents S.specialFiber) :
    IsProper (S.specialFiberComponentToSpec Z) := by
  change IsProper (S.specialFiberComponentι Z ≫ S.specialFiberToSpec)
  infer_instance

/-- **Each irreducible component of the special fibre of a regular proper model is a proper curve
over the residue field.** Collected statement of the two properties proved above: the structure
morphism over `k` is proper and the space of the component is at most one-dimensional. -/
public theorem isProper_and_topologicalKrullDim_le_specialFiberComponent
    (Z : irreducibleComponents S.specialFiber) :
    IsProper (S.specialFiberComponentToSpec Z) ∧
      topologicalKrullDim (S.specialFiberComponentIdeal Z).subscheme ≤ (1 : WithBot ℕ∞) :=
  ⟨S.isProper_specialFiberComponentToSpec Z,
    S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z⟩

/-- The degree `deg(ℒ|_C)` of an invertible `𝒪_X`-module restricted to an irreducible component
of the special fibre of a regular proper model.

This is `Stacks.Models.componentDegree` applied to the component, with all three of the
structure morphism, its properness and the dimension bound supplied rather than assumed. -/
public def specialFiberComponentDegree (Z : irreducibleComponents S.specialFiber)
    (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) : ℤ :=
  componentDegree S.k (S.specialFiberComponentIdeal Z) (S.specialFiberComponentToSpec Z)
    (S.isProper_specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z) L hL

/-- The degree pairing `⟨a, ℒ⟩ = ∑ᵢ aᵢ · deg(ℒ|_{Cᵢ})` of [Stacks, Tag 0C64] over a finite set
of irreducible components of the special fibre of a regular proper model.

This is `Stacks.Models.degreePairing` applied to the canonical family of components, with the
structure morphisms, their properness and the dimension bounds supplied rather than assumed. -/
public def specialFiberDegreePairing (s : Finset (irreducibleComponents S.specialFiber))
    (a : irreducibleComponents S.specialFiber → ℤ) (L : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L) : ℤ :=
  degreePairing S s (fun Z => S.specialFiberComponentIdeal Z)
    (fun Z => S.specialFiberComponentToSpec Z)
    (fun Z => S.isProper_specialFiberComponentToSpec Z)
    (fun Z => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z) a L hL

/-- **The global functions on an irreducible component of the special fibre form a field, finite
over the residue field.** This is Tag 0C6P applied to the component: it is reduced and connected,
being integral, and proper over `k` by the above. -/
public theorem isField_and_finite_globalSections_specialFiberComponent
    (Z : irreducibleComponents S.specialFiber) :
    letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫
        (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
    IsField Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) ∧
      Module.Finite S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
  AlgebraicGeometry.isField_and_finite_globalSections S.k (S.specialFiberComponentToSpec Z)

end RegularProperModelSituation

end Stacks.Models

end
