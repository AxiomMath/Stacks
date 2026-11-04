module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization
public import StacksFrontier.RingTheory.Branches.Completion

/-!
# Elementary étale neighbourhoods of a point with henselian local ring

Let `S` be a scheme and `s ∈ S` a point whose local ring `𝒪_{S, s}` is henselian. Every elementary
étale neighbourhood `(U, u) → (S, s)` then admits a retraction on local rings: a local
homomorphism `𝒪_{U, u} → 𝒪_{S, s}` left inverse to the stalk map. This is the universal property
of the henselization (Stacks 05KS, 04HY), for the henselian ring `𝒪_{S, s}`, which is its own
henselization. When moreover `S` is the spectrum of its local ring at `s`, the retraction gives a
section `S → Spec 𝒪_{U, u}` of the composite `Spec 𝒪_{U, u} → U → S`, through the closed point.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.exists_stalk_retraction_of_henselian`: the retraction on
  local rings.
* `AlgebraicGeometry.EtaleNeighborhood.exists_section_of_henselian`: the section of
  `Spec 𝒪_{U, u} → S` through the closed point.

## References

* [Stacks Project, Tag 05KS](https://stacks.math.columbia.edu/tag/05KS)
* [Stacks Project, Tag 04HY](https://stacks.math.columbia.edu/tag/04HY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If the local ring of `S` at `s` is henselian, every elementary étale neighbourhood
`(U, u) → (S, s)` admits a local homomorphism `𝒪_{U, u} → 𝒪_{S, s}` retracting the stalk map:
on spectra, composing it with `Spec 𝒪_{U, u} → U → S` gives the canonical `Spec 𝒪_{S, s} → S`. -/
theorem EtaleNeighborhood.exists_stalk_retraction_of_henselian {S : Scheme.{u}} {s : S}
    [HenselianLocalRing (S.presheaf.stalk s)] (N : EtaleNeighborhood S s) (hN : N.IsElementary) :
    ∃ g : N.scheme.presheaf.stalk N.point ⟶ S.presheaf.stalk s, IsLocalHom g.hom ∧
      Spec.map g ≫ N.scheme.fromSpecStalk N.point ≫ N.toBase = S.fromSpecStalk s := by
  obtain ⟨X, x, f, _, rfl⟩ := N
  let := isHenselization_self (S.presheaf.stalk (f x))
  obtain ⟨ι, -, hover, -, -⟩ := isColimit_globalSections S (f x) (S.presheaf.stalk (f x))
  obtain ⟨g, hg, hcomp, -⟩ := hover (Opposite.op ⟨⟨X, x, f, rfl⟩, hN⟩)
  let g' : X.presheaf.stalk x ⟶ S.presheaf.stalk (f x) := CommRingCat.ofHom g
  refine ⟨g', hg, ?_⟩
  dsimp only
  have h1 : f.stalkMap x ≫ g' = 𝟙 _ := by
    ext a
    have := RingHom.congr_fun hcomp a
    simp only [AlgebraicGeometry.stalkMap, RingHom.comp_apply] at this
    simp only [RingHom.algebraMap_toAlgebra, RingHom.id_apply, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id] at this
    exact this
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, h1, Spec.map_id,
    Category.id_comp]

/-- If the local ring of `S` at `s` is henselian and `S` is the spectrum of that local ring, every
elementary étale neighbourhood `(U, u) → (S, s)` admits a section `S → Spec 𝒪_{U, u}` of the
composite `Spec 𝒪_{U, u} → U → S`, sending `s` to the closed point. -/
theorem EtaleNeighborhood.exists_section_of_henselian {S : Scheme.{u}} {s : S}
    [HenselianLocalRing (S.presheaf.stalk s)] [IsIso (S.fromSpecStalk s)]
    (N : EtaleNeighborhood S s) (hN : N.IsElementary) :
    ∃ ρ : S ⟶ Spec (N.scheme.presheaf.stalk N.point),
      ρ ≫ N.scheme.fromSpecStalk N.point ≫ N.toBase = 𝟙 S ∧
        ρ s = IsLocalRing.closedPoint (N.scheme.presheaf.stalk N.point) := by
  obtain ⟨g, hg, hcomp⟩ := N.exists_stalk_retraction_of_henselian hN
  refine ⟨inv (S.fromSpecStalk s) ≫ Spec.map g, ?_, ?_⟩
  · rw [Category.assoc, hcomp, IsIso.inv_hom_id]
  · have hs : inv (S.fromSpecStalk s) s = IsLocalRing.closedPoint (S.presheaf.stalk s) := by
      have h : inv (S.fromSpecStalk s) s = inv (S.fromSpecStalk s)
          (S.fromSpecStalk s (IsLocalRing.closedPoint (S.presheaf.stalk s))) := by
        rw [Scheme.fromSpecStalk_closedPoint]
      rw [h]
      exact Scheme.hom_inv_apply (asIso (S.fromSpecStalk s)) _
    rw [Scheme.Hom.comp_apply, hs, Spec_closedPoint]

end AlgebraicGeometry
