module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated

/-!
# The third term of the localization triangle is unique up to one natural isomorphism

A `Stacks.LocalCohomology.LocalizationTriangleData` for a finitely generated ideal `I` of `R`
packages a functor `complement : ModuleCat R ⥤ D(R)` together with a distinguished triangle

`RΓ_{V(I)}(M) ⟶ M⟦0⟧ ⟶ complement(M) ⟶ RΓ_{V(I)}(M)⟦1⟧`

whose first map is the counit of the local-cohomology adjunction of Stacks 0A6Q, and a
degree-zero identification of `H⁰(complement(M))` with sections on `U = Spec R \ V(I)`. Several
constructions of such a datum exist in this library, and every downstream result is stated
relative to a fixed one; nothing so far compares two of them. This file supplies the comparison.

The point is that the *first* map of the triangle is not part of the data: it is the adjunction
counit, the same for every datum. Two data therefore give two distinguished triangles with the
same first map, and completing the identity of the first two objects to a morphism of triangles
gives an isomorphism of the third ones. What that argument leaves open is naturality in the
module, since the filler of a triangle morphism is not unique in general. Here it *is* unique,
and the reason is a vanishing statement that this file proves first:

`Hom(W, complement(M)) = 0` for every `W` with `I`-power-torsion cohomology,

i.e. `complement(M)` lies in the right orthogonal of the torsion subcategory. Indeed a morphism
`W ⟶ complement(M)` has zero composite with the boundary map, because composing further with the
shifted counit is injective on morphisms out of a torsion object; so it factors through `M⟦0⟧`,
and every morphism `W ⟶ M⟦0⟧` factors in turn through the counit, whose composite with the
restriction vanishes. Both factorizations are instances of
`Stacks.LocalCohomology.bijective_comp_localCohomologyCounit`, the universal property of
Stacks 0A6Q.

The vanishing turns the restriction into a universal arrow: for every `I`-local `Z`, composing
with `restriction` is a *bijection* `Hom(complement(M), Z) ≅ Hom(M⟦0⟧, Z)`. That is the
derived-category counterpart of "sections on `U`", and it pins the comparison between two data
down to a single map, hence makes it natural, invertible, and compatible with the boundary.

## Main definitions

* `Stacks.LocalCohomology.complementComparison` — the comparison
  `D.complement.obj M ⟶ D'.complement.obj M` between two data: the unique map whose composite
  with the restriction of `D` is the restriction of `D'`.
* `Stacks.LocalCohomology.complementIso` — **the uniqueness statement**, a natural isomorphism
  `D.complement ≅ D'.complement` of functors `ModuleCat R ⥤ D(R)`.

## Main results

* `Stacks.LocalCohomology.rightOrthogonal_complement` — the third term of the localization
  triangle admits no nonzero morphism from an object with `I`-power-torsion cohomology.
* `Stacks.LocalCohomology.bijective_comp_restriction` — **the universal property**: for an
  `I`-local `Z`, composing with the restriction identifies `Hom(complement(M), Z)` with
  `Hom(M⟦0⟧, Z)`.
* `Stacks.LocalCohomology.restriction_comp_complementComparison` and
  `Stacks.LocalCohomology.complementComparison_comp_boundary` — the two clauses that characterize
  the comparison: it carries the restriction of one datum to the restriction of the other, and
  the boundary of the other to the boundary of the one. Together they say that the comparison is
  an isomorphism of localization triangles which is the identity on the first two objects.

## Implementation notes

The comparison is produced from a bijection rather than from
`CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism`, which only asserts
that a filler exists; the bijection is what makes the filler unique and the construction
`def`-level. The boundary clause is nevertheless proved *through* the triangle axiom: the filler
it supplies satisfies the boundary identity, and uniqueness identifies it with the comparison.

No `@[stacks]` attribute is placed here. Stacks 0DWR states the localization sequence for one
model of derived sections on `U`; this file says that the model is irrelevant, which the tag does
not assert.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

attribute [local instance] derivedPowerTorsionProperty_isClosedUnderIsomorphisms
attribute [local instance] derivedPowerTorsionProperty_isTriangulated

variable {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)

/-! ### Local cohomology of a module stays torsion after a shift -/

/-- Every shift of the local cohomology of a module has `I`-power-torsion cohomology: the
torsion objects form a triangulated, hence shift-stable, subcategory. -/
theorem derivedPowerTorsionProperty_shift_localCohomologyOnModules
    (M : ModuleCat.{max u v} R) (n : ℤ) :
    Dualizing.derivedPowerTorsionProperty R I hI
      (((localCohomologyOnModules R I hI).obj M)⟦n⟧) :=
  (Dualizing.derivedPowerTorsionProperty R I hI).le_shift n _
    (derivedPowerTorsionProperty_localCohomologyOnModules I hI M)

/-- **The universal property of the counit, one shift up.** For `W` with `I`-power-torsion
cohomology, composing with the shifted counit is injective on morphisms into the shifted local
cohomology, because `W⟦-1⟧` is torsion as well. -/
theorem eq_zero_of_comp_shift_localCohomologyCounit
    (M : ModuleCat.{max u v} R) (W : DerivedCategory (ModuleCat.{max u v} R))
    (hW : Dualizing.derivedPowerTorsionProperty R I hI W)
    (k : W ⟶ ((localCohomologyOnModules R I hI).obj M)⟦(1 : ℤ)⟧)
    (hk : k ≫ ((localCohomologyCounit.{v} I hI).app M)⟦(1 : ℤ)⟧' = 0) : k = 0 := by
  have hW' : Dualizing.derivedPowerTorsionProperty R I hI (W⟦(-1 : ℤ)⟧) :=
    (Dualizing.derivedPowerTorsionProperty R I hI).le_shift (-1 : ℤ) _ hW
  set C := DerivedCategory (ModuleCat.{max u v} R)
  set e := shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)
  have hzero : ((shiftFunctor C (-1 : ℤ)).map k ≫
      e.hom.app ((localCohomologyOnModules R I hI).obj M)) ≫
        (localCohomologyCounit.{v} I hI).app M = 0 := by
    rw [Category.assoc, show e.hom.app ((localCohomologyOnModules R I hI).obj M) ≫
        (localCohomologyCounit.{v} I hI).app M =
      (shiftFunctor C (1 : ℤ) ⋙ shiftFunctor C (-1 : ℤ)).map
          ((localCohomologyCounit.{v} I hI).app M) ≫
        e.hom.app ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) from
      (e.hom.naturality ((localCohomologyCounit.{v} I hI).app M)).symm, ← Category.assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp, hk, Functor.map_zero, zero_comp]
  have h1 : (shiftFunctor C (-1 : ℤ)).map k ≫
      e.hom.app ((localCohomologyOnModules R I hI).obj M) = 0 :=
    (bijective_comp_localCohomologyCounit_app I hI M _ hW').injective
      (hzero.trans zero_comp.symm)
  have h2 : (shiftFunctor C (-1 : ℤ)).map k = 0 := by
    rw [← cancel_mono (e.hom.app ((localCohomologyOnModules R I hI).obj M)), h1, zero_comp]
  exact (shiftFunctor C (-1 : ℤ)).map_injective (by simpa using h2)

/-! ### The third term is `I`-local -/

variable {I hI}

/-- **The third term of the localization triangle is `I`-local**: there is no nonzero morphism to
it from an object with `I`-power-torsion cohomology.

A morphism `g : W ⟶ complement(M)` composed with the boundary map is killed by the shifted
counit, hence zero; so `g` factors through `M⟦0⟧`, and that factorization itself factors through
the counit, whose composite with the restriction vanishes. -/
theorem rightOrthogonal_complement (D : LocalizationTriangleData.{u, max u v} R I hI)
    (M : ModuleCat.{max u v} R) :
    (Dualizing.derivedPowerTorsionProperty R I hI).rightOrthogonal (D.complement.obj M) := by
  intro W g hW
  have hdist := D.distinguished M
  have h31 : D.boundary.app M ≫ ((localCohomologyCounit.{v} I hI).app M)⟦(1 : ℤ)⟧' = 0 :=
    comp_distTriang_mor_zero₃₁ _ hdist
  have h12 : (localCohomologyCounit.{v} I hI).app M ≫ D.restriction.app M = 0 :=
    comp_distTriang_mor_zero₁₂ _ hdist
  have hb : g ≫ D.boundary.app M = 0 := by
    refine eq_zero_of_comp_shift_localCohomologyCounit I hI M W hW _ ?_
    rw [Category.assoc, h31, comp_zero]
  obtain ⟨h, hh⟩ : ∃ t : W ⟶ (DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M,
      g = t ≫ D.restriction.app M :=
    Triangle.coyoneda_exact₃ (D.triangle M) hdist g hb
  obtain ⟨h', hh'⟩ := (bijective_comp_localCohomologyCounit_app I hI M W hW).surjective h
  have hh'' : h' ≫ (localCohomologyCounit.{v} I hI).app M = h := hh'
  rw [hh, ← hh'', Category.assoc, h12, comp_zero]

/-- **The universal property of the third term of the localization triangle.** For an `I`-local
object `Z` of `D(R)` — one admitting no nonzero morphism from a torsion object — composing with
the restriction is a bijection from the morphisms out of `complement(M)` onto the morphisms out
of `M⟦0⟧`.

Surjectivity is the vanishing of `Hom(RΓ_{V(I)}(M), Z)`, injectivity the vanishing of
`Hom(RΓ_{V(I)}(M)⟦1⟧, Z)`. This is the sense in which `complement(M)` is "sections away from
`V(I)`" as an object of `D(R)` and not merely in degree zero. -/
theorem bijective_comp_restriction (D : LocalizationTriangleData.{u, max u v} R I hI)
    (M : ModuleCat.{max u v} R) (Z : DerivedCategory (ModuleCat.{max u v} R))
    (hZ : (Dualizing.derivedPowerTorsionProperty R I hI).rightOrthogonal Z) :
    Function.Bijective (fun θ : D.complement.obj M ⟶ Z => D.restriction.app M ≫ θ) := by
  refine ⟨fun θ θ' hθ ↦ ?_, fun f ↦ ?_⟩
  · have h0 : D.restriction.app M ≫ (θ - θ') = 0 :=
      (Preadditive.comp_sub _ _ _).trans (sub_eq_zero.2 hθ)
    obtain ⟨t, ht⟩ : ∃ t : ((localCohomologyOnModules R I hI).obj M)⟦(1 : ℤ)⟧ ⟶ Z,
        θ - θ' = D.boundary.app M ≫ t :=
      Triangle.yoneda_exact₃ (D.triangle M) (D.distinguished M) (θ - θ') h0
    rw [hZ t (derivedPowerTorsionProperty_shift_localCohomologyOnModules I hI M 1),
      comp_zero] at ht
    exact sub_eq_zero.1 ht
  · obtain ⟨θ, hθ⟩ : ∃ t : D.complement.obj M ⟶ Z, f = D.restriction.app M ≫ t :=
      Triangle.yoneda_exact₂ (D.triangle M) (D.distinguished M) f
        (hZ _ (derivedPowerTorsionProperty_localCohomologyOnModules I hI M))
    exact ⟨θ, hθ.symm⟩

/-- **Extensionality for morphisms out of the third term.** Two morphisms from
`D.complement.obj M` to an `I`-local object agree as soon as their composites with the
restriction agree. This is the injectivity half of
`Stacks.LocalCohomology.bijective_comp_restriction`, in the form the comparisons below use. -/
theorem hom_ext_of_restriction_comp (D : LocalizationTriangleData.{u, max u v} R I hI)
    (M : ModuleCat.{max u v} R) {Z : DerivedCategory (ModuleCat.{max u v} R)}
    (hZ : (Dualizing.derivedPowerTorsionProperty R I hI).rightOrthogonal Z)
    {θ θ' : D.complement.obj M ⟶ Z}
    (h : D.restriction.app M ≫ θ = D.restriction.app M ≫ θ') : θ = θ' :=
  (bijective_comp_restriction D M Z hZ).injective h

/-! ### The comparison between two data -/

/-- **The comparison between the third terms of two localization triangles for the same ideal**:
the unique morphism whose composite with the restriction of `D` is the restriction of `D'`. It
exists and is unique because `D'.complement.obj M` is `I`-local. -/
def complementComparison (D D' : LocalizationTriangleData.{u, max u v} R I hI)
    (M : ModuleCat.{max u v} R) : D.complement.obj M ⟶ D'.complement.obj M :=
  (Equiv.ofBijective _
    (bijective_comp_restriction D M _ (rightOrthogonal_complement D' M))).symm
      (D'.restriction.app M)

/-- **The characterizing clause of the comparison.** Its composite with the restriction of `D` is
the restriction of `D'`. -/
@[simp] theorem restriction_comp_complementComparison
    (D D' : LocalizationTriangleData.{u, max u v} R I hI) (M : ModuleCat.{max u v} R) :
    D.restriction.app M ≫ complementComparison D D' M = D'.restriction.app M :=
  (Equiv.ofBijective _
    (bijective_comp_restriction D M _ (rightOrthogonal_complement D' M))).apply_symm_apply _

/-- **Uniqueness.** Any morphism carrying the restriction of `D` to the restriction of `D'` is
the comparison. -/
theorem eq_complementComparison (D D' : LocalizationTriangleData.{u, max u v} R I hI)
    (M : ModuleCat.{max u v} R) (θ : D.complement.obj M ⟶ D'.complement.obj M)
    (hθ : D.restriction.app M ≫ θ = D'.restriction.app M) :
    θ = complementComparison D D' M :=
  (bijective_comp_restriction D M _ (rightOrthogonal_complement D' M)).injective
    (by rw [hθ, restriction_comp_complementComparison])

/-- **The second characterizing clause of the comparison.** It carries the boundary map of `D'`
back to the boundary map of `D`, so that together with
`Stacks.LocalCohomology.restriction_comp_complementComparison` it is a morphism of localization
triangles which is the identity on local cohomology and on the module.

The filler supplied by the triangle axiom satisfies this identity, and uniqueness identifies that
filler with the comparison. -/
theorem complementComparison_comp_boundary
    (D D' : LocalizationTriangleData.{u, max u v} R I hI) (M : ModuleCat.{max u v} R) :
    complementComparison D D' M ≫ D'.boundary.app M = D.boundary.app M := by
  obtain ⟨c, hc₁, hc₂⟩ : ∃ c : D.complement.obj M ⟶ D'.complement.obj M,
      D.restriction.app M ≫ c = D'.restriction.app M ∧
        c ≫ D'.boundary.app M =
          D.boundary.app M ≫ (𝟙 ((localCohomologyOnModules R I hI).obj M))⟦(1 : ℤ)⟧' := by
    obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism (D.triangle M)
      (D'.triangle M) (D.distinguished M) (D'.distinguished M) (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ⟨c, hc₁.trans (Category.id_comp _), hc₂.symm⟩
  rw [← eq_complementComparison D D' M c hc₁]
  simpa using hc₂

/-- **The localization triangle datum is unique up to a canonical natural isomorphism.** For a
finitely generated ideal `I` of `R`, any two `Stacks.LocalCohomology.LocalizationTriangleData`
have naturally isomorphic third terms, by the comparison of
`Stacks.LocalCohomology.complementComparison`.

This is what makes a statement proved for one model of derived sections on
`U = Spec R \ V(I)` a statement about every model: a result quantified over an abstract datum
follows from the same result for a single concrete one. Naturality is a consequence of
uniqueness, which in turn comes from the `I`-locality of the third term. -/
def complementIso (D D' : LocalizationTriangleData.{u, max u v} R I hI) :
    D.complement ≅ D'.complement :=
  NatIso.ofComponents
    (fun M =>
      { hom := complementComparison D D' M
        inv := complementComparison D' D M
        hom_inv_id := hom_ext_of_restriction_comp D M (rightOrthogonal_complement D M)
          (by rw [← Category.assoc, restriction_comp_complementComparison,
            restriction_comp_complementComparison, Category.comp_id])
        inv_hom_id := hom_ext_of_restriction_comp D' M (rightOrthogonal_complement D' M)
          (by rw [← Category.assoc, restriction_comp_complementComparison,
            restriction_comp_complementComparison, Category.comp_id]) })
    (fun {M N} g => by
      refine hom_ext_of_restriction_comp D M (rightOrthogonal_complement D' N) ?_
      rw [← Category.assoc, ← D.restriction.naturality g, Category.assoc,
        restriction_comp_complementComparison, ← Category.assoc,
        restriction_comp_complementComparison, D'.restriction.naturality g])

/-- The components of the uniqueness isomorphism are the comparison maps. -/
@[simp] theorem complementIso_hom_app (D D' : LocalizationTriangleData.{u, max u v} R I hI)
    (M : ModuleCat.{max u v} R) :
    (complementIso D D').hom.app M = complementComparison D D' M := rfl

/-- The components of the inverse of the uniqueness isomorphism are the comparison maps in the
other direction. -/
@[simp] theorem complementIso_inv_app (D D' : LocalizationTriangleData.{u, max u v} R I hI)
    (M : ModuleCat.{max u v} R) :
    (complementIso D D').inv.app M = complementComparison D' D M := rfl

/-- The uniqueness isomorphism carries one restriction to the other. -/
theorem restriction_comp_complementIso_hom_app
    (D D' : LocalizationTriangleData.{u, max u v} R I hI) (M : ModuleCat.{max u v} R) :
    D.restriction.app M ≫ (complementIso D D').hom.app M = D'.restriction.app M :=
  restriction_comp_complementComparison D D' M

/-- The uniqueness isomorphism carries one boundary map to the other. -/
theorem complementIso_hom_app_comp_boundary
    (D D' : LocalizationTriangleData.{u, max u v} R I hI) (M : ModuleCat.{max u v} R) :
    (complementIso D D').hom.app M ≫ D'.boundary.app M = D.boundary.app M :=
  complementComparison_comp_boundary D D' M

end Stacks.LocalCohomology

end
