module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# The sheafified universe lift of a morphism of fppf sheaves

Let `S` be a scheme contained in a big fppf site `B` and let `f : X' ⟶ X` be a morphism of
presheaves on the big fppf site of `S` with values in `Type u`. Its sheafified universe lift
`AlgebraicGeometry.Space.sheafifiedULiftMap` is a morphism of fppf sheaves of `Type (u + 1)`,
the shape in which a morphism of algebraic spaces enters the formal-space constructions. When
`X'` and `X` are fppf sheaves, the sheafification is an isomorphism on both sides, so the
sheafified universe lift carries the same information as `f` itself: it is étale, respectively
representable by algebraic spaces, exactly when `f` is.

## Main results

* `AlgebraicGeometry.Space.sheafifiedULiftIso`: the sheafified universe lift of a sheaf of
  `Type u` is isomorphic to its universe lift.
* `AlgebraicGeometry.Space.isEtaleULift_sheafifiedULiftMap_iff` and
  `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_sheafifiedULiftMap_iff`: the
  sheafified universe lift of a morphism of fppf sheaves of `Type u` is étale, respectively
  representable by algebraic spaces, exactly when the morphism is.
* `AlgebraicGeometry.Space.exists_hasPropertyULift_sheafifiedULiftMap`: a property of
  morphisms of algebraic spaces invariant under isomorphism passes from the universe lift of
  a morphism of fppf sheaves of `Type u` to its sheafified universe lift.
* `AlgebraicGeometry.Space.isEtaleULift_isIso_comp_iff` and
  `AlgebraicGeometry.Space.isEtaleULift_comp_isIso_iff`: étaleness in a larger value universe
  is unchanged by composing with an isomorphism on either side.

## Implementation notes

The universe lift of a sheaf of `Type u` is again a sheaf, universe lifting being an
equivalence on the compatible families of a presieve, so the unit of the sheafification of the
universe lift is an isomorphism and is natural in the presheaf. Conjugating by it reduces both
statements to the corresponding bridge lemma for the universe lift of a morphism,
`AlgebraicGeometry.Space.isEtaleULift_whiskerRight_iff` and
`AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_whiskerRight_iff`.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 0APZ](https://stacks.math.columbia.edu/tag/0APZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Isomorphism invariance of étaleness in a larger value universe -/

/-- Precomposing a morphism of presheaves of `Type (max w u)` with an isomorphism does not
change whether it is étale. -/
theorem isEtaleULift_isIso_comp_iff
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (e : F ⟶ G) [IsIso e] (f : G ⟶ H) :
    IsEtaleULift.{w} B S hS (e ≫ f) ↔ IsEtaleULift.{w} B S hS f := by
  let P := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
  constructor
  · intro hf U φ hφ
    have h := hf U (φ ≫ inv e) ((P.cancel_right_of_respectsIso φ (inv e)).mpr hφ)
    rwa [Category.assoc, IsIso.inv_hom_id_assoc] at h
  · intro hf U φ hφ
    have h := hf U (φ ≫ e) ((P.cancel_right_of_respectsIso φ e).mpr hφ)
    rwa [Category.assoc] at h

/-- Postcomposing a morphism of presheaves of `Type (max w u)` with an isomorphism does not
change whether it is étale. -/
theorem isEtaleULift_comp_isIso_iff
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} (f : F ⟶ G) (e : G ⟶ H) [IsIso e] :
    IsEtaleULift.{w} B S hS (f ≫ e) ↔ IsEtaleULift.{w} B S hS f := by
  let P := (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
  constructor
  · intro hf U φ hφ
    have h := hf U φ hφ
    rw [← Category.assoc] at h
    exact (P.cancel_right_of_respectsIso (φ ≫ f) e).mp h
  · intro hf U φ hφ
    have h := (P.cancel_right_of_respectsIso (φ ≫ f) e).mpr (hf U φ hφ)
    rwa [Category.assoc] at h

/-! ### Isomorphism invariance of representability by algebraic spaces -/

/-- Representability by algebraic spaces of a morphism of presheaves of `Type (max w u)`
transports along isomorphisms of its source and target. -/
theorem isRepresentableByAlgebraicSpacesULift_of_iso
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {a : F ⟶ G} {a' : F' ⟶ G'}
    (eF : F ≅ F') (eG : G ≅ G') (hcomm : a ≫ eG.hom = eF.hom ≫ a')
    (ha : IsRepresentableByAlgebraicSpacesULift.{w} B S hS a) :
    IsRepresentableByAlgebraicSpacesULift.{w} B S hS a' := by
  refine isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS eF.inv a' a eG.inv ?_ ha
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hcomm]
  simp

/-! ### The sheafification of the universe lift of a sheaf -/

/-- The universe lift of an fppf sheaf of `Type u` is already an fppf sheaf of
`Type (u + 1)`, so it is isomorphic to its own fppf sheafification. -/
def sheafifiedULiftIso (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) :
    X ⋙ uliftFunctor.{u + 1} ≅ (sheafifiedULift B S hS X).obj :=
  (BigFppfOver.topology B S hS).isoSheafify
    ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2
      (Presieve.isSheaf_comp_uliftFunctor (BigFppfOver.topology B S hS)
        ((CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).1 hX)))

/-- The sheafified universe lift of a morphism of fppf sheaves of `Type u` is, up to the
isomorphisms identifying the sheafifications with the universe lifts, the universe lift of
the morphism. -/
theorem whiskerRight_comp_sheafifiedULiftIso_hom
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (f : X' ⟶ X) :
    Functor.whiskerRight f uliftFunctor.{u + 1} ≫ (sheafifiedULiftIso B S hS X hX).hom =
      (sheafifiedULiftIso B S hS X' hX').hom ≫ (sheafifiedULiftMap B S hS f).hom :=
  (BigFppfOver.topology B S hS).toSheafify_naturality _

/-- The sheafified universe lift of a morphism of fppf sheaves of `Type u` is the universe
lift of the morphism conjugated by the isomorphisms identifying the sheafifications with the
universe lifts. -/
theorem sheafifiedULiftMap_hom_eq {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (f : X' ⟶ X) :
    (sheafifiedULiftMap B S hS f).hom =
      (sheafifiedULiftIso B S hS X' hX').inv ≫
        Functor.whiskerRight f uliftFunctor.{u + 1} ≫
          (sheafifiedULiftIso B S hS X hX).hom := by
  rw [whiskerRight_comp_sheafifiedULiftIso_hom B S hS hX' hX f, Iso.inv_hom_id_assoc]

/-! ### Transfer along the sheafified universe lift -/

/-- The sheafified universe lift of a morphism of fppf sheaves of `Type u` is étale in the
value universe `u + 1` exactly when the morphism is étale. -/
theorem isEtaleULift_sheafifiedULiftMap_iff
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (f : X' ⟶ X) :
    IsEtaleULift.{u + 1} B S hS (sheafifiedULiftMap B S hS f).hom ↔ IsEtale B S hS f := by
  rw [sheafifiedULiftMap_hom_eq B S hS hX' hX f, isEtaleULift_isIso_comp_iff,
    isEtaleULift_comp_isIso_iff, isEtaleULift_whiskerRight_iff]

/-- The sheafified universe lift of a morphism of fppf sheaves of `Type u` is representable by
algebraic spaces in the value universe `u + 1` exactly when the morphism is representable by
algebraic spaces. -/
theorem isRepresentableByAlgebraicSpacesULift_sheafifiedULiftMap_iff
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (f : X' ⟶ X) :
    IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (sheafifiedULiftMap B S hS f).hom ↔
      IsRepresentableByAlgebraicSpaces B S hS f := by
  refine ⟨fun ha => ?_, fun ha => isRepresentableByAlgebraicSpacesULift_of_iso B S hS
    (sheafifiedULiftIso B S hS X' hX') (sheafifiedULiftIso B S hS X hX)
    (whiskerRight_comp_sheafifiedULiftIso_hom B S hS hX' hX f)
    ((isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f).mpr ha)⟩
  refine (isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f).mp ?_
  refine isRepresentableByAlgebraicSpacesULift_of_iso B S hS
    (sheafifiedULiftIso B S hS X' hX').symm (sheafifiedULiftIso B S hS X hX).symm ?_ ha
  rw [Iso.symm_hom, Iso.symm_hom, sheafifiedULiftMap_hom_eq B S hS hX' hX f]
  simp

/-- A property of morphisms of algebraic spaces over `S` invariant under isomorphism holds for
the sheafified universe lift of a morphism of fppf sheaves of `Type u` in the bootstrap sense
of Stacks 03XZ as soon as it holds for the universe lift of that morphism. -/
theorem exists_hasPropertyULift_sheafifiedULiftMap
    {P : MorphismProperty (AlgebraicSpacesULift.{u + 1} B S hS)} [P.RespectsIso]
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X) (f : X' ⟶ X)
    (hrep : IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Functor.whiskerRight f uliftFunctor.{u + 1}))
    (h : HasPropertyULift.{u + 1} B S hS P
      (Functor.whiskerRight f uliftFunctor.{u + 1}) hrep) :
    ∃ hrep' : IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (sheafifiedULiftMap B S hS f).hom,
      HasPropertyULift.{u + 1} B S hS P (sheafifiedULiftMap B S hS f).hom hrep' := by
  have hsq : IsPullback (sheafifiedULiftIso B S hS X' hX').inv
      (sheafifiedULiftMap B S hS f).hom (Functor.whiskerRight f uliftFunctor.{u + 1})
      (sheafifiedULiftIso B S hS X hX).inv := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [sheafifiedULiftMap_hom_eq B S hS hX' hX f]
    simp
  exact ⟨_, hasPropertyULift_of_isPullback B S hS hsq hrep h⟩

end AlgebraicGeometry.Space

end
