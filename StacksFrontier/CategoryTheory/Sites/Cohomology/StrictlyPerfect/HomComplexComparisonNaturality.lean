module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison

/-!
# Naturality of the comparison between the naive and the derived internal Hom

For complexes `E` and `F` of sheaves of modules on a ringed site,
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` is the canonical morphism

`Q(SheafHom(E, F)) ⟶ RSheafHom(QE, QF)`

from the image in the derived category of the naive internal Hom complex to the derived internal
Hom. This file proves that it is natural in both variables.

No hypothesis on `E` or `F` is needed. The comparison is a composite of three morphisms — the map
of internal Hom complexes induced by the augmentation into a K-injective resolution of the
target, the inverse of the model comparison for that K-injective target, and the inverse of the
map induced by the augmentation — and each of the three is natural; the content of the proof is
pasting the three squares, two of which have an inverse on one side.

## Main results

* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality`: **the comparison is
  natural in both variables**, contravariantly in the source and covariantly in the target.

## Implementation notes

**Why a separate file, and why the derived-category universe is left free.** The same statement
was already proved, twice, in the course of the affine duality development
(`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffinePseudoCoherentDerivedHom` and
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom`), but in both places it is
`private`, and in both places the derived-category universe is pinned — to `u + 1` in the first,
and to the derived category of modules over `Spec R` in the second, whose statement also mentions
a `private` abbreviation. The statement is about the comparison itself and has nothing to do with
affine schemes, so it belongs beside the definition, with the universe `d` of the derived category
left free as `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` leaves it.

**The two rearrangements.** Turning a naturality square for the `hom` components of two
isomorphisms into one for their `inv` components, and pasting a three-factor square whose last
factor is an inverse, are stated here as private lemmas rather than inlined, because each is used
once but reads as a transposition rather than as a step of the argument. They are pure category
theory, independent of everything else in this file.

## References

* [Stacks Project, Tag 08I5](https://stacks.math.columbia.edu/tag/08I5)
* [Stacks Project, Tag 0A8N](https://stacks.math.columbia.edu/tag/0A8N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

/-- Pasting the naturality squares of a comparison which is a three-factor composite whose last
factor is the inverse of an isomorphism. -/
private lemma paste_inv_square {C : Type*} [Category C] {S S' P P' T T' U U' : C}
    (h : S ⟶ S') (c : S ⟶ P) (c' : S' ⟶ P') (cc : P ⟶ T) (cc' : P' ⟶ T')
    (m : U ⟶ T) (m' : U' ⟶ T') [IsIso m] [IsIso m']
    (hm : P ⟶ P') (uI : T ⟶ T') (u : U ⟶ U')
    (h1 : h ≫ c' = c ≫ hm) (h2 : hm ≫ cc' = cc ≫ uI) (h3 : m ≫ uI = u ≫ m') :
    h ≫ (c' ≫ cc' ≫ inv m') = (c ≫ cc ≫ inv m) ≫ u := by
  have key : uI ≫ inv m' = inv m ≫ u := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, h3, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, key]

variable (X : RingedSite.{u, u, u})
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X)

/-- **The comparison `Q(SheafHom(E, F)) ⟶ RSheafHom(QE, QF)` is natural in both variables**:
contravariantly in the source, through a morphism `e : E' ⟶ E`, and covariantly in the target,
through a morphism `g : F ⟶ F'`. No hypothesis on any of the four complexes is needed.

The three factors of
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` are natural separately. For the first
this is functoriality of `AlgebraicGeometry.RingedSite.homMap` together with naturality of the
augmentation into the K-injective resolution; for the second it is the
`homComparison_natural` field of
`AlgebraicGeometry.RingedSite.DerivedInternalHom`, transposed to the inverses; for the third it is
naturality of the derived internal Hom in each variable, again transposed. -/
theorem strictlyPerfectHomComparison_naturality
    (E E' F F' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (e : E' ⟶ E) (g : F ⟶ F') :
    DerivedCategory.Q.map (homMap X e g) ≫ strictlyPerfectHomComparison X D E' F' =
      strictlyPerfectHomComparison X D E F ≫
        ((D.hom.map (DerivedCategory.Q.map e).op).app (DerivedCategory.Q.obj F) ≫
          (D.hom.obj (op (DerivedCategory.Q.obj E'))).map (DerivedCategory.Q.map g)) := by
  have hnat : g ≫ (kInjectiveAugmentation X).app F' =
      (kInjectiveAugmentation X).app F ≫ (kInjectiveResolution X).map g :=
    (kInjectiveAugmentation X).naturality g
  have h1' : homMap X e g ≫ homMap X (𝟙 E') ((kInjectiveAugmentation X).app F') =
      homMap X (𝟙 E) ((kInjectiveAugmentation X).app F) ≫
        homMap X e ((kInjectiveResolution X).map g) := by
    rw [homMap_comp, homMap_comp, Category.id_comp, Category.comp_id, hnat]
  have h1 : DerivedCategory.Q.map (homMap X e g) ≫
        DerivedCategory.Q.map (homMap X (𝟙 E') ((kInjectiveAugmentation X).app F')) =
      DerivedCategory.Q.map (homMap X (𝟙 E) ((kInjectiveAugmentation X).app F)) ≫
        DerivedCategory.Q.map (homMap X e ((kInjectiveResolution X).map g)) := by
    rw [← Functor.map_comp, h1', Functor.map_comp]
  -- The `hom` naturality square of the two comparisons, transposed across their inverses.
  have h2 := (CommSq.vert_inv
    (g := D.homComparison E ((kInjectiveResolution X).obj F))
    (h := D.homComparison E' ((kInjectiveResolution X).obj F'))
    ⟨(Category.assoc _ _ _).trans
      (D.homComparison_natural e ((kInjectiveResolution X).map g))⟩).w
  have hntr := (D.hom.map (DerivedCategory.Q.map e).op).naturality
    (DerivedCategory.Q.map ((kInjectiveAugmentation X).app F))
  have h3 : (D.hom.obj (op (DerivedCategory.Q.obj E))).map
        (DerivedCategory.Q.map ((kInjectiveAugmentation X).app F)) ≫
      ((D.hom.map (DerivedCategory.Q.map e).op).app
          (DerivedCategory.Q.obj ((kInjectiveResolution X).obj F)) ≫
        (D.hom.obj (op (DerivedCategory.Q.obj E'))).map
          (DerivedCategory.Q.map ((kInjectiveResolution X).map g))) =
      ((D.hom.map (DerivedCategory.Q.map e).op).app (DerivedCategory.Q.obj F) ≫
        (D.hom.obj (op (DerivedCategory.Q.obj E'))).map (DerivedCategory.Q.map g)) ≫
        (D.hom.obj (op (DerivedCategory.Q.obj E'))).map
          (DerivedCategory.Q.map ((kInjectiveAugmentation X).app F')) := by
    rw [← Category.assoc, hntr, Category.assoc, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← hnat]
    rfl
  exact paste_inv_square _ _ _ _ _ _ _ _ _ _ h1 h2 h3

/-- **At a K-injective target the comparison is the inverse of the model comparison.** For
`I` K-injective the derived internal Hom is computed by the internal Hom complex, by the
`homComparison` field of `AlgebraicGeometry.RingedSite.DerivedInternalHom`, and the canonical
comparison of
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` — which is built by passing through a
K-injective resolution — is that inverse on the nose, not merely up to an isomorphism.

So every statement about the comparison specialises at a K-injective target to a statement about
the model comparison, and conversely the `homComparison_natural` field is the K-injective case of
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_naturality`.

The proof is the naturality of the model comparison in the second variable along the augmentation
`I ⟶ I'` into the chosen K-injective resolution, whose first variable is the identity, so that one
factor of the square collapses. -/
theorem strictlyPerfectHomComparison_eq_homComparison_inv
    (E I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    strictlyPerfectHomComparison X D E I = (D.homComparison E I).inv := by
  have hKI : ((Functor.id
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)).obj
        I).IsKInjective := inferInstanceAs I.IsKInjective
  have hnat := D.homComparison_natural (𝟙 E) ((kInjectiveAugmentation X).app I)
  simp only [Functor.id_obj] at hnat
  refine (cancel_epi (D.homComparison E I).hom).mp ?_
  rw [Iso.hom_inv_id, strictlyPerfectHomComparison, ← Category.assoc, ← hnat]
  simp

end AlgebraicGeometry.RingedSite

end
