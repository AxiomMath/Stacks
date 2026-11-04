module

public import StacksFrontier.AlgebraicGeometry.FibreSeparation.Basic

/-!
# Separating a closed subset from a fibre

A closed subset of a base change `X ×_S T` of a quasi-compact morphism `f : X ⟶ S`, disjoint from
the fibre over a point `t ∈ T`, is locally contained in a closed subset already defined over an
affine base locally of finite presentation over `S`, which remains disjoint from the corresponding
fibre.

## Main results

* `AlgebraicGeometry.exists_affine_locallyFinitePresentation_separation_isClosed` produces the
  affine neighbourhood of `t`, the affine approximation of the base which is locally of finite
  presentation over `S`, and the separating closed subset.

## Implementation notes

The closed-subscheme form of the statement is applied to the vanishing ideal sheaf of the given
closed subset, whose support is that subset again; the support of the resulting ideal sheaf is the
separating closed subset. The inclusion between preimages is the inequality of the two ideal
sheaves read through the Galois connection between supports and vanishing ideals, using that
taking supports is antitone and commutes with pullback along a morphism.

## References

* [Stacks Project, Tag 0H29](https://stacks.math.columbia.edu/tag/0H29)
* [Stacks Project, Tag 05BD](https://stacks.math.columbia.edu/tag/05BD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Let `f : X ⟶ S` be a quasi-compact morphism of schemes, `g : T ⟶ S` a morphism, `t ∈ T` a
point and `E ⊆ X ×_S T` a closed subset whose image in `T` misses `t`. Then there are an affine
open neighbourhood `V` of `t`, a commutative square `V ⟶ T' ⟶ S`, `V ⟶ T ⟶ S` with `T'` affine and
`T' ⟶ S` locally of finite presentation, and a closed subset `E' ⊆ X ×_S T'` whose image in `T'`
misses the image of `t`, such that the preimage of `E` in `X ×_S V` lies in the preimage of `E'`.

This is the case of schemes, for closed subsets, of the separation lemma for algebraic stacks. -/
@[stacks 0H29 "the case of schemes, for closed subsets"]
theorem exists_affine_locallyFinitePresentation_separation_isClosed
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] (g : T ⟶ S)
    (t : T) (E : Set ↥(pullback f g)) (hE : IsClosed E)
    (ht : t ∉ Set.image (pullback.snd f g) E) :
    ∃ (V : T.affineOpens) (htV : t ∈ V.1)
      (T' : Scheme.{u}) (_ : IsAffine T') (b : T' ⟶ S)
      (_ : LocallyOfFinitePresentation b) (a : V.1.toScheme ⟶ T')
      (_ : V.1.ι ≫ g = a ≫ b)
      (E' : Set ↥(pullback f b)) (_ : IsClosed E')
      (p : pullback f (V.1.ι ≫ g) ⟶ pullback f g)
      (q : pullback f (V.1.ι ≫ g) ⟶ pullback f b),
      (p ≫ pullback.fst f g = pullback.fst f (V.1.ι ≫ g)) ∧
      (p ≫ pullback.snd f g = pullback.snd f (V.1.ι ≫ g) ≫ V.1.ι) ∧
      (q ≫ pullback.fst f b = pullback.fst f (V.1.ι ≫ g)) ∧
      (q ≫ pullback.snd f b = pullback.snd f (V.1.ι ≫ g) ≫ a) ∧
      (a ⟨t, htV⟩ ∉ Set.image (pullback.snd f b) E') ∧
      (p ⁻¹' E ⊆ q ⁻¹' E') := by
  classical
  set I : (pullback f g).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨E, hE⟩ with hI
  have hIsupp : I.support.carrier = E := by
    have h : (I.support : Set ↥(pullback f g)) = E := by simp [hI]
    exact h
  obtain ⟨V, htV, T', hT', b, hb, a, hab, I', p, q, h1, h2, h3, h4, h5, h6⟩ :=
    exists_affine_locallyFinitePresentation_separation f g t I (by rw [hIsupp]; exact ht)
  refine ⟨V, htV, T', hT', b, hb, a, hab, (I'.support : Set ↥(pullback f b)),
    I'.support.isClosed, p, q, h1, h2, h3, h4, h5, ?_⟩
  have hmono := Scheme.IdealSheafData.support_antitone h6
  rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap] at hmono
  intro x hx
  exact hmono (hIsupp.ge hx)

end AlgebraicGeometry

end
