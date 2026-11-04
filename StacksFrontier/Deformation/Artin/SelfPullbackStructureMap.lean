module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.Theory
public import StacksFrontier.Deformation.Artin.SquareZeroDifferenceBaseChange

/-!
# The structure morphism of a self-fibre product is pinned by its two sections

Let `q : A' ⟶ A` be a surjection with square-zero kernel. The geometric difference of
Stacks 07Y9 (2)(b) glues two lifts over the self-fibre product `A' ×_A A'`, and
`Deformation.Artin.IsGeometricDifference` quantifies *existentially* over a structure morphism
`Spec (A' ×_A A') ⟶ S` for it, constraining that morphism only through its composites with the
two sections `Spec A' ⟶ Spec (A' ×_A A')`. For the predicate to be single-valued those
composites have to determine the morphism, and that is what this file proves — under the one
extra hypothesis that the common composite maps into an affine open of `S`.

Both halves of the argument are needed. The sections are square-zero thickenings, so each of
them is surjective on spectra (`Deformation.Artin.surjective_specMap_pullbackFst`): the image
of a morphism out of `Spec (A' ×_A A')` is therefore the image of its restriction along a
section, and lands in the same affine open. And over an affine target a morphism out of
`Spec (A' ×_A A')` is a ring map *into* `A' ×_A A'`, which is determined by its two components
because `A' ×_A A'` is a subring of `A' × A'`
(`Deformation.Artin.pullback_ext`).

## Main results

* `Deformation.Artin.eq_of_comp_specMap_pullback_sections` — two morphisms
  `Spec (A' ×_A A') ⟶ S` which agree after both sections, and whose common restriction maps
  into an affine open of `S`, are equal.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

section StructureMap

universe u

variable {A A' : Type u} [CommRing A] [CommRing A'] (q : A' →+* A)

/-- **Over an affine target, a morphism out of a self-fibre product is determined by its two
sections.** A morphism into an affine scheme is its map on global sections, and a ring map into
`A' ×_A A'` is determined by its two components. -/
public theorem eq_of_comp_specMap_pullback_sections_of_isAffine {V : Scheme.{u}} [IsAffine V]
    {w₁ w₂ : Spec (CommRingCat.of (q.pullback q)) ⟶ V}
    (hfst : Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ≫ w₁ =
      Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ≫ w₂)
    (hsnd : Spec.map (CommRingCat.ofHom (q.pullbackSnd q)) ≫ w₁ =
      Spec.map (CommRingCat.ofHom (q.pullbackSnd q)) ≫ w₂) :
    w₁ = w₂ := by
  have happ : Scheme.Hom.appTop w₁ = Scheme.Hom.appTop w₂ := by
    have key : ∀ g : q.pullback q →+* A',
        Spec.map (CommRingCat.ofHom g) ≫ w₁ = Spec.map (CommRingCat.ofHom g) ≫ w₂ →
        (Scheme.Hom.appTop w₁ ≫ (Scheme.ΓSpecIso (CommRingCat.of (q.pullback q))).hom) ≫
          CommRingCat.ofHom g =
        (Scheme.Hom.appTop w₂ ≫ (Scheme.ΓSpecIso (CommRingCat.of (q.pullback q))).hom) ≫
          CommRingCat.ofHom g := by
      intro g h
      have e := congrArg Scheme.Hom.appTop h
      rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e
      rw [Category.assoc, Category.assoc,
        ← Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g),
        ← Category.assoc, ← Category.assoc, e]
    have hθ : Scheme.Hom.appTop w₁ ≫
          (Scheme.ΓSpecIso (CommRingCat.of (q.pullback q))).hom =
        Scheme.Hom.appTop w₂ ≫
          (Scheme.ΓSpecIso (CommRingCat.of (q.pullback q))).hom := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      refine pullback_ext q q ?_ ?_
      · exact ConcreteCategory.congr_hom (key _ hfst) r
      · exact ConcreteCategory.congr_hom (key _ hsnd) r
    have hcancel := congrArg
      (fun k => k ≫ (Scheme.ΓSpecIso (CommRingCat.of (q.pullback q))).inv) hθ
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hcancel
  have : IsIso V.toSpecΓ := by
    rw [← Scheme.isoSpec_hom]
    infer_instance
  refine (cancel_mono V.toSpecΓ).1 ?_
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, happ]

/-- **The structure morphism of a self-fibre product to `S` is pinned by its two sections.**
Two morphisms `Spec (A' ×_A A') ⟶ S` which agree after both sections `Spec A' ⟶ Spec (A' ×_A A')`
and whose common restriction along the first maps into an affine open of `S` are equal.

The first section is surjective on spectra, because its kernel is square zero
(`Deformation.Artin.surjective_specMap_pullbackFst`), so both morphisms have the same image as
that restriction and factor through the affine open; over an affine target
`Deformation.Artin.eq_of_comp_specMap_pullback_sections_of_isAffine` applies.

This is what makes `Deformation.Artin.IsGeometricDifference` single-valued in the charted
setting of Stacks 07YA, where the hypothesis `haff` is
`Deformation.Artin.AffineObject.mapsIntoAffineOpen`. -/
public theorem eq_of_comp_specMap_pullback_sections {S : Scheme.{u}}
    (hq : Function.Surjective q) (hsq : RingHom.ker q ^ 2 = ⊥)
    {u₁ u₂ : Spec (CommRingCat.of (q.pullback q)) ⟶ S}
    (hfst : Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ≫ u₁ =
      Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ≫ u₂)
    (hsnd : Spec.map (CommRingCat.ofHom (q.pullbackSnd q)) ≫ u₁ =
      Spec.map (CommRingCat.ofHom (q.pullbackSnd q)) ≫ u₂)
    (haff : MapsIntoAffineOpen S
      (Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ≫ u₁)) :
    u₁ = u₂ := by
  obtain ⟨U, hUaff, hU⟩ := haff
  have : IsAffine (U : Scheme.{u}) := hUaff
  have hsurjSpec := surjective_specMap_pullbackFst q hq hsq
  have hrange : ∀ u : Spec (CommRingCat.of (q.pullback q)) ⟶ S,
      Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ≫ u =
        Spec.map (CommRingCat.ofHom (q.pullbackFst q)) ≫ u₁ → Set.range ⇑u ⊆ Set.range ⇑U.ι := by
    intro u hu
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := hsurjSpec z
    rw [← Scheme.Hom.comp_apply, hu, Scheme.Hom.comp_apply]
    exact hU y
  have hrange₁ := hrange u₁ rfl
  have hrange₂ := hrange u₂ hfst.symm
  have hw₁ := IsOpenImmersion.lift_fac U.ι u₁ hrange₁
  have hw₂ := IsOpenImmersion.lift_fac U.ι u₂ hrange₂
  have hlift : ∀ g : q.pullback q →+* A',
      Spec.map (CommRingCat.ofHom g) ≫ u₁ = Spec.map (CommRingCat.ofHom g) ≫ u₂ →
      Spec.map (CommRingCat.ofHom g) ≫ IsOpenImmersion.lift U.ι u₁ hrange₁ =
        Spec.map (CommRingCat.ofHom g) ≫ IsOpenImmersion.lift U.ι u₂ hrange₂ := by
    intro g h
    refine (cancel_mono U.ι).1 ?_
    rw [Category.assoc, hw₁, Category.assoc, hw₂]
    exact h
  rw [← hw₁, ← hw₂,
    eq_of_comp_specMap_pullback_sections_of_isAffine q (hlift _ hfst) (hlift _ hsnd)]

end StructureMap

end Deformation.Artin

end
