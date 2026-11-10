module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.Schemes

/-!
# Deformations of an open subscheme

A deformation of a scheme `X` over the residue field `k` does not change the underlying
topological space: its special-fibre immersion is a closed immersion, because the residue map
of an object of `𝒞_Λ` is surjective, and it is surjective on points, because the spectrum of
an Artinian local ring is a single point. So an open `U ⊆ X` names an open of the total space
of every deformation of `X`, and that open, with the restricted structure morphism, is a
deformation of `U`: its special fibre is `U` because the defining square is pasted from the
restriction square of an open immersion. The construction is functorial, and the functor
commutes with the projections to `𝒞_Λ` because it does not change the base of a deformation.

## Main definitions

* `Deformation.Examples.restrictedOpen`: the open of the total space of a deformation
  corresponding to an open of the scheme being deformed.
* `Deformation.Examples.restrictDeformation`: the restriction of a deformation of `X` to a
  deformation of an open subscheme `U ⊆ X`.
* `Deformation.Examples.restrictDeformationHom`: the restriction of a morphism of deformations.
* `Deformation.Examples.openRestrictionFunctor`: the resulting functor of deformation
  categories over `𝒞_Λ`.

## Main results

* `Deformation.Examples.deformationSpecialMap_isHomeomorph`: the special-fibre immersion of a
  deformation is a homeomorphism of underlying topological spaces.
* `Deformation.Examples.specialMap_preimage_restrictedOpen`: the defining property of the
  corresponding open, namely that its preimage in the special fibre is the given open.
* `Deformation.Examples.map_preimage_restrictedOpen`: a morphism of deformations carries the
  corresponding opens to one another.
* `Deformation.Examples.specialMap_resLE_isPullback`: the special fibre of the restricted
  deformation is the given open subscheme.
* `Deformation.Examples.restrictDeformationHom_map_comp_ι`: the open immersions of the
  restricted deformations into the original ones are natural in the deformation.

## Implementation notes

The corresponding open is the image of the given open under the special-fibre immersion, which
is open because that immersion is a homeomorphism of underlying spaces. The homeomorphism is
recorded as a proposition rather than as a `Homeomorph`, so the restriction functor is built
from the immersion itself and involves no inverse map and no choices.

The restricted deformation keeps the base of the original one, which is why the structure
functor of the restricted deformation category is matched on the nose and the based functor's
compatibility is `rfl`. For the same reason the structure morphism of the restriction is an
honest equation `(restrictDeformation U P).toBase = (restrictedOpen P U).ι ≫ P.toBase` between
morphisms with the same target, rather than a heterogeneous one.

## References

* [Stacks Project, Tag 01IO](https://stacks.math.columbia.edu/tag/01IO)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0DYW](https://stacks.math.columbia.edu/tag/0DYW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### A deformation does not change the underlying topological space -/

/-- The residue map of an object of `𝒞_Λ` is surjective: it is the reduction modulo the
maximal ideal followed by the chosen identification of the residue field with `k`. -/
theorem residueMap_surjective (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Function.Surjective (Deformation.Artin.residueMap A) :=
  A.residueEquiv.toEquiv.surjective.comp IsLocalRing.residue_surjective

/-- The closed point of the spectrum of an object of `𝒞_Λ` is a closed immersion. -/
theorem residueSpecMap_isClosedImmersion (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    IsClosedImmersion (residueSpecMap A) :=
  IsClosedImmersion.spec_of_surjective _ (residueMap_surjective A)

/-- The closed point of the spectrum of an object of `𝒞_Λ` is surjective on points: the
spectrum of an Artinian local ring has a single point. -/
theorem residueSpecMap_surjective (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Function.Surjective (residueSpecMap A) := by
  let : Subsingleton (baseSpec A) := by
    change Subsingleton (PrimeSpectrum A)
    infer_instance
  exact Function.surjective_to_subsingleton _

variable {X : Over (Spec (.of k))}

/-- The special-fibre immersion of a deformation is a closed immersion, being the base change
of the closed point of the spectrum of the base. -/
theorem deformationSpecialMap_isClosedImmersion
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) : IsClosedImmersion P.specialMap :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
    P.specialCartesian.flip (residueSpecMap_isClosedImmersion P.base)

/-- The special-fibre immersion of a deformation is surjective on points, being the base change
of the closed point of the spectrum of the base. -/
theorem deformationSpecialMap_surjective
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Function.Surjective P.specialMap :=
  (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
    P.specialCartesian.flip ⟨residueSpecMap_surjective P.base⟩).surj

/-- A deformation has the same underlying topological space as the scheme it deforms: the
special-fibre immersion is a surjective closed embedding, hence a homeomorphism. -/
theorem deformationSpecialMap_isHomeomorph
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) : IsHomeomorph P.specialMap :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(@Scheme.Hom.isClosedEmbedding _ _ P.specialMap
        (deformationSpecialMap_isClosedImmersion P)).isEmbedding,
      deformationSpecialMap_surjective P⟩

/-! ### The open of a deformation corresponding to an open of the special fibre -/

/-- The open of the total space of a deformation corresponding to an open of the scheme being
deformed: its image under the special-fibre immersion, which is open because that immersion is
a homeomorphism of underlying spaces. -/
@[sga "7 VI 4.1(d)" "partial"]
def restrictedOpen (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) (U : X.left.Opens) :
    P.scheme.Opens :=
  ⟨P.specialMap '' U, (deformationSpecialMap_isHomeomorph P).isOpenMap _ U.isOpen⟩

/-- A point of a deformation lies in the corresponding open exactly when it is the image of a
point of the given open. -/
@[simp]
theorem mem_restrictedOpen {P : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    {U : X.left.Opens} {y : P.scheme} :
    y ∈ restrictedOpen P U ↔ ∃ x ∈ U, P.specialMap x = y := Iff.rfl

/-- The corresponding open of a deformation cuts out the given open on the special fibre. -/
theorem specialMap_preimage_restrictedOpen
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) (U : X.left.Opens) :
    P.specialMap ⁻¹ᵁ restrictedOpen P U = U :=
  TopologicalSpace.Opens.ext
    (Set.preimage_image_eq _ (deformationSpecialMap_isHomeomorph P).bijective.injective)

/-- The given open is contained in the preimage of the corresponding open, which is the
inequality that restricts the special-fibre immersion to the two opens. -/
theorem le_specialMap_preimage_restrictedOpen
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) (U : X.left.Opens) :
    U ≤ P.specialMap ⁻¹ᵁ restrictedOpen P U :=
  (specialMap_preimage_restrictedOpen P U).ge

/-- A morphism of deformations carries the corresponding opens to one another: the two
identifications of the underlying space with that of the scheme being deformed agree. -/
theorem map_preimage_restrictedOpen {U : X.left.Opens}
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    f.map ⁻¹ᵁ restrictedOpen P U = restrictedOpen Q U := by
  have hcompat : ∀ x : X.left, f.map (Q.specialMap x) = P.specialMap x := fun x => by
    simpa using congrArg (fun g : X.left ⟶ P.scheme => g x) f.special_compat
  ext y
  change (∃ x ∈ U, P.specialMap x = f.map y) ↔ ∃ x ∈ U, Q.specialMap x = y
  constructor
  · rintro ⟨x, hxU, hx⟩
    obtain ⟨x', hx'⟩ := deformationSpecialMap_surjective Q y
    have hinj : x' = x := (deformationSpecialMap_isHomeomorph P).bijective.injective
      (by rw [← hcompat x', hx', hx])
    exact ⟨x, hxU, by rw [← hinj, hx']⟩
  · rintro ⟨x, hxU, hx⟩
    exact ⟨x, hxU, by rw [← hcompat x, hx]⟩

/-- The corresponding open of the source is contained in the preimage of the corresponding open
of the target, which is the inequality that restricts a morphism to the two opens. -/
theorem le_map_preimage_restrictedOpen {U : X.left.Opens}
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    restrictedOpen Q U ≤ f.map ⁻¹ᵁ restrictedOpen P U :=
  (map_preimage_restrictedOpen f).ge

/-- The special fibre of the corresponding open is the given open: the restriction of the
special-fibre immersion to the two opens is cartesian over it. -/
theorem specialMap_resLE_isPullback
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) (U : X.left.Opens) :
    IsPullback (P.specialMap.resLE (restrictedOpen P U) U
        (le_specialMap_preimage_restrictedOpen P U))
      U.ι (restrictedOpen P U).ι P.specialMap := by
  apply IsOpenImmersion.isPullback
  · exact (Scheme.Hom.resLE_comp_ι P.specialMap
      (le_specialMap_preimage_restrictedOpen P U)).symm
  · rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
      specialMap_preimage_restrictedOpen]

/-! ### The restriction functor -/

/-- The restriction of a deformation of `X` to a deformation of an open subscheme `U ⊆ X`: the
total space is the corresponding open, and the special fibre is `U`. -/
@[sga "7 VI 4.1(d)"]
def restrictDeformation (U : X.left.Opens)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom)) where
  base := P.base
  scheme := (restrictedOpen P U).toScheme
  toBase := (restrictedOpen P U).ι ≫ P.toBase
  flat := by
    let : Flat P.toBase := P.flat
    infer_instance
  specialMap :=
    P.specialMap.resLE (restrictedOpen P U) U (le_specialMap_preimage_restrictedOpen P U)
  specialCartesian := (specialMap_resLE_isPullback P U).paste_vert P.specialCartesian

/-- The restriction of a deformation keeps the object of `𝒞_Λ` it lives over. -/
theorem restrictDeformation_base (U : X.left.Opens)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    (restrictDeformation U P).base = P.base := rfl

/-- The structure morphism of the restriction is the structure morphism of the original
deformation restricted to the corresponding open. -/
theorem restrictDeformation_toBase (U : X.left.Opens)
    (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    (restrictDeformation U P).toBase = (restrictedOpen P U).ι ≫ P.toBase := rfl

/-- The restriction of a morphism of deformations of `X` to the corresponding opens. -/
@[sga "7 VI 4.1(d)" "partial"]
def restrictDeformationHom (U : X.left.Opens)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    restrictDeformation U P ⟶ restrictDeformation U Q where
  base := f.base
  map :=
    f.map.resLE (restrictedOpen P U) (restrictedOpen Q U) (le_map_preimage_restrictedOpen f)
  cartesian := by
    have hpull : IsPullback
        (f.map.resLE (restrictedOpen P U) (restrictedOpen Q U)
          (le_map_preimage_restrictedOpen f))
        (restrictedOpen Q U).ι (restrictedOpen P U).ι f.map := by
      apply IsOpenImmersion.isPullback
      · exact (Scheme.Hom.resLE_comp_ι f.map (le_map_preimage_restrictedOpen f)).symm
      · rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
          map_preimage_restrictedOpen (U := U) f]
    exact hpull.paste_vert f.cartesian
  special_compat := by
    change Q.specialMap.resLE (restrictedOpen Q U) U
          (le_specialMap_preimage_restrictedOpen Q U) ≫
        f.map.resLE (restrictedOpen P U) (restrictedOpen Q U)
          (le_map_preimage_restrictedOpen f) =
      P.specialMap.resLE (restrictedOpen P U) U
        (le_specialMap_preimage_restrictedOpen P U)
    apply (cancel_mono (restrictedOpen P U).ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, f.special_compat,
      Scheme.Hom.resLE_comp_ι]

/-- The restricted deformations sit inside the original ones as open subschemes, naturally in
the deformation. -/
theorem restrictDeformationHom_map_comp_ι (U : X.left.Opens)
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) X} (f : P ⟶ Q) :
    (restrictDeformationHom U f).map ≫ (restrictedOpen P U).ι =
      (restrictedOpen Q U).ι ≫ f.map :=
  Scheme.Hom.resLE_comp_ι f.map (le_map_preimage_restrictedOpen f)

/-- **Stacks 0DYW.** Let `X` be a scheme over `k` and `U ⊆ X` an open subscheme. Restricting a
deformation of `X` to the open corresponding to `U` is a functor from the deformation category
of `X` to that of `U`, over the category `𝒞_Λ` of Artinian local `Λ`-algebras. -/
@[stacks 0DYW, sga "7 VI 4.1(d)"]
def openRestrictionFunctor (X : Over (Spec (.of k))) (U : X.left.Opens) :
    BasedFunctor
      (BasedCategory.ofFunctor (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X))
      (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk (U.ι ≫ X.hom)))) := by
  refine
    { obj := restrictDeformation U
      map := fun f => restrictDeformationHom U f
      map_id := ?_
      map_comp := ?_
      w := rfl }
  · intro P
    apply SchemeDeformationCategory.Hom.ext
    · rfl
    · change Scheme.Hom.resLE (𝟙 P.scheme) (restrictedOpen P U) (restrictedOpen P U) _ =
        𝟙 (restrictedOpen P U).toScheme
      exact (Scheme.Hom.resLE_id _).trans (Scheme.homOfLE_rfl P.scheme (restrictedOpen P U))
  · intro P Q R f g
    apply SchemeDeformationCategory.Hom.ext
    · rfl
    · change Scheme.Hom.resLE (g.map ≫ f.map) (restrictedOpen P U) (restrictedOpen R U) _ =
        Scheme.Hom.resLE g.map (restrictedOpen Q U) (restrictedOpen R U) _ ≫
          Scheme.Hom.resLE f.map (restrictedOpen P U) (restrictedOpen Q U) _
      exact (Scheme.Hom.resLE_comp_resLE (f := g.map)
        (e := le_map_preimage_restrictedOpen g) (g := f.map)
        (e' := le_map_preimage_restrictedOpen f)).symm

end Deformation.Examples

end
