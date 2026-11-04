module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Restriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree
public import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence on an affine scheme: from modules to sheaves

Let `R` be a commutative ring and `M^•` a complex of `R`-modules. This file proves the direction
of Stacks 08E7 which goes from modules to sheaves: if `M^•` is `m`-pseudo-coherent as a complex
of `R`-modules (Stacks 064Q (1)), then the associated object `\widetilde{M^•}` of
`D(𝒪_{Spec R})` is `m`-pseudo-coherent (Stacks 08CB (3)).

## Main results

* `Stacks.AffineTilde.isPseudoCoherentComplexFrom_tildeComplex`: `\widetilde{M^•}` is an
  `m`-pseudo-coherent *complex* of `𝒪_{Spec R}`-modules.
* `Stacks.AffineTilde.isPseudoCoherentFrom_tildeComplex`: hence its image in the derived category
  is `m`-pseudo-coherent. This is the "if" half of the first clause of Stacks 08E7.
* `Stacks.AffineTilde.isPseudoCoherent_tildeComplex`: the same for pseudo-coherence in all
  degrees, the "if" half of the second clause of Stacks 08E7.
* `Stacks.AffineTilde.isPseudoCoherentComplexFrom_tildeComplex_of_isPseudoCoherentFrom`: the
  converse direction's first step — the local strictly perfect approximations may be taken on
  `\widetilde{M^•}` itself rather than on some other representative. This is Stacks 08CC (2)
  specialized to `Spec R`, and it is where the proof of the hard direction of Stacks 08E7 starts.

## Implementation notes

The source says of this direction only that it "is immediate from the definitions". It is not
quite immediate in the formalization, and the reason is a genuine mismatch of shape rather than
bookkeeping: the witness of `m`-pseudo-coherence at the level of modules (Stacks 064Q (1),
`StacksDraft.PseudoCoherence.IsPseudoCoherentFrom`) is a morphism `α : Q(E^•) ⟶ Q(M^•)` of the
*derived* category, while the witness at the level of sheaves (Stacks 08CB (1),
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom`) is a morphism of *complexes*. So
exactness of `M ↦ M^~` alone does not transport the witness; one has to descend `α` to a
morphism of complexes first.

That is done entirely at the level of modules, with `DerivedCategory.left_fac`: `α` is
`Q(γ) ≫ Q(s)⁻¹` for morphisms of complexes `γ : E^• ⟶ G^•` and `s : M^• ⟶ G^•` with `s` a
quasi-isomorphism, and `γ` inherits the cohomological properties of `α`
(`CategoryTheory.isIso_homologyMap_of_left_fac` and its `Epi` companion). Applying
`M ↦ M^~` degreewise then keeps those properties, because the functor is exact
(`Stacks.AffineTilde.tildeFunctor_preservesHomology`), and the pair
`(\widetilde{γ}, \widetilde{s})` is exactly the left fraction that the common core of
Stacks 08CC, `AlgebraicGeometry.RingedSpace.exists_local_strictlyPerfect_approximation`,
consumes. No derived-category-level functoriality of `M ↦ M^~` is needed at the level of sheaves.

The strictly perfect complex is `\widetilde{E^•}`, strictly perfect by
`Stacks.AffineTilde.isStrictlyPerfect_tildeComplex`, which is where
`Stacks.AffineTilde.finiteFreeIsoTilde` is used.

The `Stacks.StrictlyPerfect.OXMod` and `AlgebraicGeometry.Scheme.Modules` spellings of the
category of `𝒪_{Spec R}`-modules are definitionally equal, and no instance has to be carried
across as a term here: `CategoryTheory.HasDerivedCategory.standard`, made a local instance, is
found independently for each spelling.

## References

* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.AffineTilde

variable {R : CommRingCat.{u}}

/-- The complex of `𝒪_{Spec R}`-modules associated termwise to a complex of `R`-modules. -/
abbrev tildeComplex (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (Spec R).Modules ℤ :=
  ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M

/-- A bounded complex of finite free `R`-modules vanishes outside a finite set of degrees. -/
theorem finite_support_of_isBoundedFiniteFree {E : CochainComplex (ModuleCat.{u} R) ℤ}
    (hE : StacksDraft.PseudoCoherence.IsBoundedFiniteFree E) :
    {i : ℤ | ¬ IsZero (E.X i)}.Finite := by
  obtain ⟨⟨a, b, hab⟩, _⟩ :=
    (StacksDraft.PseudoCoherence.isBoundedFiniteFree_iff_exists_window E).1 hE
  refine (Set.finite_Icc a b).subset fun i hi => ?_
  simp only [Set.mem_ofPred_eq] at hi
  exact ⟨by by_contra h; exact hi (hab i (Or.inl (by omega))),
    by by_contra h; exact hi (hab i (Or.inr (by omega)))⟩

/-- **Stacks 08E7, the direction from modules to sheaves, at the level of complexes.** If a
complex `M^•` of `R`-modules is `m`-pseudo-coherent, then the associated complex
`\widetilde{M^•}` of `𝒪_{Spec R}`-modules is `m`-pseudo-coherent.

The derived morphism witnessing `m`-pseudo-coherence of `M^•` is written as a left fraction
`Q(γ) ≫ Q(s)⁻¹` with `γ` and `s` morphisms of complexes of `R`-modules, both of which are then
carried to morphisms of complexes of sheaves by the exact functor `M ↦ M^~`; the pair is the
input of the common core of Stacks 08CC. -/
theorem isPseudoCoherentComplexFrom_tildeComplex (M : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom
      (X := (Spec R).toRingedSpace) (tildeComplex M) m := by
  have := tildeFunctor_preservesHomology R
  have := AlgebraicGeometry.tilde.preservesFiniteLimits R
  have := preservesFiniteColimits_tildeFunctor R
  obtain ⟨E, hE, α, hα, hα₀⟩ := h
  obtain ⟨G, γ, s, hs, hfac⟩ := DerivedCategory.left_fac α
  have hSP : StrictlyPerfect.IsStrictlyPerfect (X := (Spec R).toRingedSpace) (tildeComplex E) :=
    isStrictlyPerfect_tildeComplex E (finite_support_of_isBoundedFiniteFree hE)
      fun i => ⟨(hE.finiteFree i).1, (hE.finiteFree i).2⟩
  intro x
  exact AlgebraicGeometry.RingedSpace.exists_local_strictlyPerfect_approximation (U := ⊤)
    (AlgebraicGeometry.RingedSpace.isStrictlyPerfect_restrictComplex hSP ⊤) m
    (AlgebraicGeometry.RingedSpace.restrictComplexMap
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map γ) ⊤)
    (fun j hj => AlgebraicGeometry.RingedSpace.isIso_homologyMap_restrictComplexMap _ ⊤ j
      (CategoryTheory.isIso_homologyMap_mapHomologicalComplex (tilde.functor R) γ j
        (CategoryTheory.isIso_homologyMap_of_left_fac α γ s hs hfac j (hα j hj))))
    (AlgebraicGeometry.RingedSpace.epi_homologyMap_restrictComplexMap _ ⊤ m
      (CategoryTheory.epi_homologyMap_mapHomologicalComplex (tilde.functor R) γ m
        (CategoryTheory.epi_homologyMap_of_left_fac α γ s hs hfac m hα₀)))
    (AlgebraicGeometry.RingedSpace.restrictComplexMap
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map s) ⊤)
    (fun j => AlgebraicGeometry.RingedSpace.isIso_homologyMap_restrictComplexMap _ ⊤ j
      (CategoryTheory.isIso_homologyMap_mapHomologicalComplex (tilde.functor R) s j
        (CategoryTheory.isIso_homologyMap_of_isIso_Q_map s hs j)))
    x (Opens.mem_top x)

/-- **Stacks 08E7, the direction from modules to sheaves.** If a complex `M^•` of `R`-modules is
`m`-pseudo-coherent (Stacks 064Q (1)), then the object of `D(𝒪_{Spec R})` it determines is
`m`-pseudo-coherent (Stacks 08CB (3)). -/
@[stacks 08E7 "m-pseudo-coherent, the direction from modules to sheaves"]
theorem isPseudoCoherentFrom_tildeComplex (M : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj M) m) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom
      (X := (Spec R).toRingedSpace) (DerivedCategory.Q.obj (tildeComplex M)) m :=
  AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom.isPseudoCoherentFrom_Q
    (X := (Spec R).toRingedSpace) (isPseudoCoherentComplexFrom_tildeComplex M m h)

/-- **Stacks 08E7, the direction from modules to sheaves, all degrees at once.** If a complex
`M^•` of `R`-modules is pseudo-coherent (Stacks 064Q (2)), then the object of `D(𝒪_{Spec R})` it
determines is pseudo-coherent (Stacks 08CB (3)).

Both notions of pseudo-coherence are `m`-pseudo-coherence for every `m` — at the level of modules
by Stacks 064U
(`StacksDraft.PseudoCoherence.pseudoCoherent_iff_all`), at the level of sheaves by definition —
so this follows from `Stacks.AffineTilde.isPseudoCoherentComplexFrom_tildeComplex` degree by
degree, with the single representative `\widetilde{M^•}` serving for all degrees. -/
@[stacks 08E7 "pseudo-coherent, the direction from modules to sheaves"]
theorem isPseudoCoherent_tildeComplex (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent
      (X := (Spec R).toRingedSpace) (DerivedCategory.Q.obj (tildeComplex M)) :=
  ⟨tildeComplex M, fun m => isPseudoCoherentComplexFrom_tildeComplex M m
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all (DerivedCategory.Q.obj M)).1 h m),
    ⟨Iso.refl _⟩⟩

/-- **Stacks 08CC (2) on an affine scheme**, which is where the proof of the converse direction
of Stacks 08E7 begins: if `\widetilde{M^•}` is `m`-pseudo-coherent as an object of
`D(𝒪_{Spec R})`, then the local strictly perfect approximations may be taken on the complex
`\widetilde{M^•}` itself, rather than on the other representative that the definition of
`m`-pseudo-coherence for a derived object supplies. -/
theorem isPseudoCoherentComplexFrom_tildeComplex_of_isPseudoCoherentFrom
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (h : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom
      (X := (Spec R).toRingedSpace) (DerivedCategory.Q.obj (tildeComplex M)) m) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom
      (X := (Spec R).toRingedSpace) (tildeComplex M) m :=
  AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_iso _ m h _ (Iso.refl _)

end Stacks.AffineTilde

end
