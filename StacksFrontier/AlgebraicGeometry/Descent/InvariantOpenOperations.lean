module

public import StacksFrontier.AlgebraicGeometry.Descent.CanonicalDatumRealizations

/-!
# Intersections and inverse images of invariant opens of a descent datum

Let `f i : X i ⟶ S` be a family of morphisms of schemes with common target. The families of open
subschemes of the components of a descent datum which are invariant under its gluing isomorphisms
are stable under intersection, and a morphism of descent data pulls an invariant family back to an
invariant family.

Combined with the fact that the images of a morphism of descent data with open-immersion
components are invariant, this produces the opens entering the glueing construction of Stacks
0AP4: if two schemes over `S` map to a descent datum by open immersions of their canonical descent
data, then the part of the first lying in the second is the inverse image of a unique open
subscheme of the first scheme over `S`.

## Main results

* `AlgebraicGeometry.DescentData.IsInvariantOpens.inf`: the intersection of two invariant
  families of opens is invariant.
* `AlgebraicGeometry.DescentData.IsInvariantOpens.comap`: the inverse image of an invariant
  family along a morphism of descent data is invariant.
* `AlgebraicGeometry.DescentData.canonicalFunctor_existsUnique_preimage_eq_inf_opensRange` and
  its specialization `..._of_flat` to a surjective quasi-compact flat morphism: the overlap of
  two open-immersion morphisms of canonical descent data into a common descent datum descends to
  a unique open subscheme of the base of the first.

## Implementation notes

Invariance is a condition on the literal fibre products of schemes, but the compatibility carried
by a morphism of descent data is a square of products in `Over S`. The square is therefore first
composed with the projections in `Over S`, where the two product identities
`CategoryTheory.Limits.prod.map_fst` and `CategoryTheory.Limits.prod.map_snd` apply, and only then
transported to underlying schemes; passing from a morphism of `Over S` to its underlying morphism
of schemes commutes with composition definitionally, so the transport is a single `congrArg`.

## References

* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.DescentData

open CategoryTheory CategoryTheory.Limits

section Operations

variable {ι : Type v} {S : Scheme.{u}} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ S}

/-- **The intersection of two invariant families of opens is invariant.** -/
lemma IsInvariantOpens.inf {D : DescentData f} {W W' : ∀ i, (D.obj i).left.Opens}
    (hW : D.IsInvariantOpens W) (hW' : D.IsInvariantOpens W') :
    D.IsInvariantOpens fun i ↦ W i ⊓ W' i := fun i j ↦ by
  rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, hW i j, hW' i j]

/-- **The inverse image of an invariant family of opens along a morphism of descent data is
invariant.** -/
lemma IsInvariantOpens.comap {D E : DescentData f} (φ : E ⟶ D)
    {W : ∀ i, (D.obj i).left.Opens} (hW : D.IsInvariantOpens W) :
    E.IsInvariantOpens fun i ↦ (φ.hom i).left ⁻¹ᵁ W i := by
  refine (isInvariantOpens_iff_gluing E fun i ↦ (φ.hom i).left ⁻¹ᵁ W i).mpr fun i j ↦ ?_
  have hD := (isInvariantOpens_iff_gluing D W).mp hW i j
  have key : (E.gluing i j).hom.left ≫
        (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (E.obj j) ⟶ _) ≫
          (Over.map (f j)).map (φ.hom j) =
      prod.map ((Over.map (f i)).map (φ.hom i)) (𝟙 (Over.mk (f j))) ≫
        (D.gluing i j).hom.left ≫ prod.snd := by
    rw [show (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (E.obj j) ⟶ _) ≫
        (Over.map (f j)).map (φ.hom j) =
        prod.map (𝟙 (Over.mk (f i))) ((Over.map (f j)).map (φ.hom j)) ≫ prod.snd from by simp,
      ← Category.assoc, ← φ.comm i j, Category.assoc]
  have keyL : (E.gluing i j).hom.left.left ≫
        (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (E.obj j) ⟶ _).left ≫
          (φ.hom j).left =
      (prod.map ((Over.map (f i)).map (φ.hom i)) (𝟙 (Over.mk (f j)))).left ≫
        (D.gluing i j).hom.left.left ≫
        (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left :=
    congrArg Over.Hom.left key
  have key2 : prod.map ((Over.map (f i)).map (φ.hom i)) (𝟙 (Over.mk (f j))) ≫
        (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _) =
      (prod.fst : (Over.map (f i)).obj (E.obj i) ⨯ Over.mk (f j) ⟶ _) ≫
        (Over.map (f i)).map (φ.hom i) := by simp
  have key2L : (prod.map ((Over.map (f i)).map (φ.hom i)) (𝟙 (Over.mk (f j)))).left ≫
        (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left =
      (prod.fst : (Over.map (f i)).obj (E.obj i) ⨯ Over.mk (f j) ⟶ _).left ≫
        (φ.hom i).left :=
    congrArg Over.Hom.left key2
  simp only [← Scheme.Hom.comp_preimage] at hD ⊢
  rw [keyL, Scheme.Hom.comp_preimage, hD, ← Scheme.Hom.comp_preimage, key2L]

end Operations

section Overlap

variable {S X : Scheme.{u}} (f : X ⟶ S) {D : DescentData (fun _ : Unit ↦ f)} {U U' : Over S}

/-- The preimage under `φ` of the overlap of the images of `φ` and `φ'` is an invariant open. -/
private theorem isInvariantOpens_comap_opensRange_inf {E E' : DescentData (fun _ : Unit ↦ f)}
    (φ : E ⟶ D) (φ' : E' ⟶ D) [IsOpenImmersion (φ.hom ()).left]
    [IsOpenImmersion (φ'.hom ()).left] :
    E.IsInvariantOpens fun i ↦
      (φ.hom i).left ⁻¹ᵁ ((φ.hom i).left.opensRange ⊓ (φ'.hom i).left.opensRange) := by
  have hφ : ∀ i : Unit, IsOpenImmersion (φ.hom i).left := fun _ ↦ ‹_›
  have hφ' : ∀ i : Unit, IsOpenImmersion (φ'.hom i).left := fun _ ↦ ‹_›
  exact ((isInvariantOpens_opensRange φ).inf (isInvariantOpens_opensRange φ')).comap φ

/-- **The overlap of two open-immersion morphisms into a descent datum descends.** If the
canonical descent data of `U` and of `U'` map to a descent datum `D` relative to a one-member
fpqc covering by morphisms with open-immersion components, then the part of `U ×_S X` landing in
the image of `U' ×_S X` is the inverse image of a unique open subscheme of `U`.

This is the step of Stacks 0AP4 which produces the opens `U_{ij} ⊆ U_i` from the opens
`W_i ∩ W_j`. -/
theorem canonicalFunctor_existsUnique_preimage_eq_inf_opensRange
    (hf : Presieve.ofArrows (fun _ : Unit ↦ X) (fun _ ↦ f) ∈ Scheme.fpqcPrecoverage S)
    (φ : (canonicalFunctor f).obj U ⟶ D) (φ' : (canonicalFunctor f).obj U' ⟶ D)
    [IsOpenImmersion (φ.hom ()).left] [IsOpenImmersion (φ'.hom ()).left] :
    ∃! V : U.left.Opens, pullback.fst U.hom f ⁻¹ᵁ V =
      (φ.hom ()).left ⁻¹ᵁ ((φ.hom ()).left.opensRange ⊓ (φ'.hom ()).left.opensRange) := by
  exact canonicalFunctor_existsUnique_preimage_eq_of_isInvariantOpens f U hf _
    (isInvariantOpens_comap_opensRange_inf f φ φ')

/-- **The overlap of two open-immersion morphisms into a descent datum relative to a surjective
quasi-compact flat morphism descends.** -/
theorem canonicalFunctor_existsUnique_preimage_eq_inf_opensRange_of_flat
    [Surjective f] [QuasiCompact f] [Flat f]
    (φ : (canonicalFunctor f).obj U ⟶ D) (φ' : (canonicalFunctor f).obj U' ⟶ D)
    [IsOpenImmersion (φ.hom ()).left] [IsOpenImmersion (φ'.hom ()).left] :
    ∃! V : U.left.Opens, pullback.fst U.hom f ⁻¹ᵁ V =
      (φ.hom ()).left ⁻¹ᵁ ((φ.hom ()).left.opensRange ⊓ (φ'.hom ()).left.opensRange) := by
  exact canonicalFunctor_existsUnique_preimage_eq_of_isInvariantOpens_of_flat f U _
    (isInvariantOpens_comap_opensRange_inf f φ φ')

end Overlap

end AlgebraicGeometry.DescentData

end

end
