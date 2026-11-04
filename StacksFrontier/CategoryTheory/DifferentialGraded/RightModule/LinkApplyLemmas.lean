module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaHomCohomology
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaImageQuotient
public import StacksFrontier.CategoryTheory.Triangulated.LocalReflectorHom

/-!
# Computing the links of the chain of Tag 09LK on an element

The chain of [Stacks, Tag 09LK] identifies the degree-`n` cohomology of `ev_K (L h_X)` with a
morphism group of a derived category by composing four bijections, and each of them is defined
as an `Equiv.trans` of auxiliary bijections. A composite of `Equiv.trans`es is opaque: nothing
can be *computed* with it, and the compatibility that the assembly of the chain has to verify —
that on the coprojection of a comparison cocone the composite is the left fraction
`Q(s)⟦n⟧⁻¹ ∘ Q(f)` — is a statement about a value of the composite at a specific element.

This file supplies, for each link, the equation that makes the composite computable. The four
links split into two kinds.

## The links that compute

Links 1 and 2 are built from `CategoryTheory.Iso.homCongr`, from `Equiv.ofBijective` applied to
`CategoryTheory.Functor.map`, and from `Submodule.Quotient.equiv` and `Quotient.congr`. All of
those have a forward map that is a closed formula, so both directions of links 1 and 2 are
closed formulas:

* `CategoryTheory.ObjectProperty.homEquivReflectorShift_apply` is link 2, and
  `CategoryTheory.ObjectProperty.homEquivReflectorShift_apply_inv` writes its value as the left
  fraction `Q(η)⟦n⟧⁻¹ ∘ Q(f)`, which is the shape the compatibility is stated in;
* `DGCategory.RightModule.homShiftEquivGradedCohomology_mk` is link 1 on the homotopy class of a
  degree-zero cocycle, whose value is the cohomology class of the cocycle's evaluation at the
  identity, and
  `DGCategory.RightModule.homShiftEquivEvaluationGradedCohomology_mk` is the same read through
  evaluation at an object, which is the spelling the chain uses.

`DGCategory.RightModule.gradedCohomologyIso`, the fourth bijection of link 1's file, is not
treated here: it is pinned down already, by
`DGCategory.RightModule.homologyπ_gradedCohomologyIso_hom` in its own file, which computes it on
the homology projection — the only element shape its source has.

The *forward* direction of links 3 and 4 is a closed formula too, and the two of them share one
engine: both go through `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift`, computed
once in
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_apply`, and link 4 goes through
`CategoryTheory.homShiftEquivOfIsLocalization` as well, computed once in
`CategoryTheory.homShiftEquivOfIsLocalization_apply`. The per-link lemmas
`DGCategory.RightModule.homEquivDerivedYonedaVerdier'_apply` and
`DGCategory.RightModule.homEquivDerivedYonedaOnK'_apply` only peel the definitions off those
two, so a composite of all four rewrites by `simp` with no lemma proved twice.

## The direction that does not compute, and what replaces it

The *inverse* of links 3 and 4 does not compute, and no apply-lemma for it exists. Both are
built on `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift`, whose first factor is
`CategoryTheory.Functor.FullyFaithful.homEquiv` for the Verdier embedding `J`; the inverse of
that is `CategoryTheory.Functor.FullyFaithful.preimage`, which on
`CategoryTheory.ObjectProperty.fullyFaithfulVerdierEmbedding` comes from the fullness of `J` and
is a choice of preimage with no formula. Link 4 inverts
`CategoryTheory.homShiftEquivOfIsLocalization` as well, whose first factor is the same
construction for the comparison equivalence of two localizations
(`CategoryTheory.Localization.uniq`), itself obtained from a universal property; so there the
obstruction occurs twice.

What a non-computing bijection still supports is being *pinned down* by an equation, and that is
what is given instead: the inverse is characterised by applying the forward direction, which does
compute. The characterisation is legitimate because the forward direction is injective
(`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_injective`,
`CategoryTheory.homShiftEquivOfIsLocalization_injective`), so at most one morphism satisfies the
equation, and it is enough to discharge a compatibility stated at a value of the inverse: the
goal `e.symm c = g` becomes the goal `<closed formula at g> = c`, in which nothing opaque is
left.

## Main results

* `CategoryTheory.homShiftEquivOfIsLocalization_apply`,
  `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_apply`: the two shared engines,
  computed. Links 3 and 4 are these.
* `CategoryTheory.homShiftEquivOfIsLocalization_symm_eq_iff`,
  `CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_symm_eq_iff`: the inverses of the
  two engines, characterised.
* `CategoryTheory.ObjectProperty.homEquivReflectorShift_apply` and
  `CategoryTheory.ObjectProperty.homEquivReflectorShift_symm_eq_iff`: link 2, both directions.
* `DGCategory.RightModule.homShiftEquivGradedCohomology_mk` and
  `DGCategory.RightModule.homShiftEquivGradedCohomology_symm_eq_iff`: link 1, both directions.
* `DGCategory.RightModule.homYonedaObjKEquiv_mk` and
  `DGCategory.RightModule.homotopyClassEquiv_symm_mk`: the other bijection of link 1's file,
  full faithfulness of the differential graded Yoneda functor on homotopy categories, computed.
* `DGCategory.RightModule.homEquivDerivedYonedaVerdier'_apply` and
  `DGCategory.RightModule.homEquivDerivedYonedaVerdier'_symm_eq_iff`: link 3.
* `DGCategory.RightModule.homEquivDerivedYonedaOnK'_apply` and
  `DGCategory.RightModule.homEquivDerivedYonedaOnK'_symm_eq_iff`: link 4.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂ v u v' u' r

namespace CategoryTheory

open Category Limits Pretriangulated

/-- The inverse of a bijection takes `g` to `f` exactly when the bijection takes `f` to `g`. -/
private theorem equiv_symm_eq_iff_apply_eq {α β : Sort*} (e : α ≃ β) (g : β) (f : α) :
    e.symm g = f ↔ e f = g :=
  e.symm_apply_eq.trans eq_comm

/-! ### The first engine: a Hom group between shifted images of a localization -/

section ShiftHomUniq

variable {S : Type u} [Category.{v} S] [HasShift S ℤ]
  {D₁ : Type u₁} [Category.{v₁} D₁] [HasShift D₁ ℤ]
  {D₂ : Type u₂} [Category.{v₂} D₂] [HasShift D₂ ℤ]
  (W : MorphismProperty S)
  (q₁ : S ⥤ D₁) [q₁.IsLocalization W] [q₁.CommShift ℤ]
  (q₂ : S ⥤ D₂) [q₂.IsLocalization W] [q₂.CommShift ℤ]

/-- **The comparison equivalence of two localizations commutes with the shift.** This is the
instance `CategoryTheory.Functor.commShiftOfLocalization` that
`CategoryTheory.homShiftEquivOfIsLocalization` introduces inside its own body; it is named here
so that the isomorphism occurring in the value of that bijection can be named too. -/
@[instance_reducible] noncomputable def commShiftUniqFunctor :
    (Localization.uniq q₁ q₂ W).functor.CommShift ℤ :=
  Functor.commShiftOfLocalization q₁ W ℤ q₂ (Localization.uniq q₁ q₂ W).functor

/-- **The isomorphism moving the shift out of the comparison equivalence.** For `E` the
comparison equivalence of the two localizations this is `E ((q₁ y)⟦n⟧) ≅ (q₂ y)⟦n⟧`: the
commutation of `E` with the shift, followed by the shift of the characteristic isomorphism
`q₁ ⋙ E ≅ q₂`. It is the target isomorphism of the `CategoryTheory.Iso.homCongr` inside
`CategoryTheory.homShiftEquivOfIsLocalization`. -/
noncomputable def uniqFunctorShiftIso (y : S) (n : ℤ) :
    (Localization.uniq q₁ q₂ W).functor.obj ((q₁.obj y)⟦n⟧) ≅ (q₂.obj y)⟦n⟧ :=
  letI := commShiftUniqFunctor W q₁ q₂
  ((Localization.uniq q₁ q₂ W).functor.commShiftIso n).app (q₁.obj y) ≪≫
    (shiftFunctor D₂ n).mapIso ((Localization.compUniqFunctor q₁ q₂ W).app y)

/-- **The first engine of link 4, computed.** The bijection
`CategoryTheory.homShiftEquivOfIsLocalization` takes `f` to the image of `f` under the comparison
equivalence `E` of the two localizations, conjugated by the characteristic isomorphism
`q₁ ⋙ E ≅ q₂` on the source and by `CategoryTheory.uniqFunctorShiftIso` on the target.

Every step occurring here computes: the forward map of
`CategoryTheory.Functor.FullyFaithful.homEquiv` is `E.map` and the forward map of
`CategoryTheory.Iso.homCongr` is conjugation, so this is a definitional equality. -/
@[simp] theorem homShiftEquivOfIsLocalization_apply (x y : S) (n : ℤ)
    (f : q₁.obj x ⟶ (q₁.obj y)⟦n⟧) :
    homShiftEquivOfIsLocalization W q₁ q₂ x y n f =
      ((Localization.compUniqFunctor q₁ q₂ W).app x).inv ≫
        (Localization.uniq q₁ q₂ W).functor.map f ≫ (uniqFunctorShiftIso W q₁ q₂ y n).hom :=
  rfl

/-- **The inverse of the first engine, characterised.** The inverse of
`CategoryTheory.homShiftEquivOfIsLocalization` does not compute — it applies
`CategoryTheory.Functor.FullyFaithful.preimage` for the comparison equivalence of the two
localizations, which is a choice of preimage supplied by fullness and carries no formula — but it
is pinned down by the forward direction, which does compute: `f` is its value at `g` exactly when
the closed formula of `CategoryTheory.homShiftEquivOfIsLocalization_apply` at `f` is `g`. -/
theorem homShiftEquivOfIsLocalization_symm_eq_iff (x y : S) (n : ℤ)
    (g : q₂.obj x ⟶ (q₂.obj y)⟦n⟧) (f : q₁.obj x ⟶ (q₁.obj y)⟦n⟧) :
    (homShiftEquivOfIsLocalization W q₁ q₂ x y n).symm g = f ↔
      ((Localization.compUniqFunctor q₁ q₂ W).app x).inv ≫
          (Localization.uniq q₁ q₂ W).functor.map f ≫
            (uniqFunctorShiftIso W q₁ q₂ y n).hom = g := by
  rw [equiv_symm_eq_iff_apply_eq, homShiftEquivOfIsLocalization_apply]

/-- The first engine is injective, which is what makes
`CategoryTheory.homShiftEquivOfIsLocalization_symm_eq_iff` a characterisation: at most one `f`
satisfies that equation. -/
theorem homShiftEquivOfIsLocalization_injective (x y : S) (n : ℤ) :
    Function.Injective (homShiftEquivOfIsLocalization W q₁ q₂ x y n) :=
  (homShiftEquivOfIsLocalization W q₁ q₂ x y n).injective

end ShiftHomUniq

namespace ObjectProperty

/-! ### The second engine: the Hom groups of a Verdier quotient embedding -/

section Verdier

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (A N : ObjectProperty C) [A.IsClosedUnderIsomorphisms] [A.IsTriangulated]
  [N.IsClosedUnderIsomorphisms] [N.IsTriangulated]
  {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
  (L : A.FullSubcategory ⥤ D) [L.IsLocalization (N.inverseImage A.ι).trW] [L.CommShift ℤ]
  [L.IsTriangulated]

/-- **The Verdier embedding commutes with the shift.** This is the instance
`CategoryTheory.Functor.commShiftOfLocalization` that
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift` introduces inside its own body,
named so that the isomorphism occurring in the value of that bijection can be named too. -/
@[instance_reducible] noncomputable def verdierEmbeddingCommShift :
    (A.verdierEmbedding N L).CommShift ℤ :=
  Functor.commShiftOfLocalization L (N.inverseImage A.ι).trW ℤ (A.ι ⋙ N.trW.Q)
    (A.verdierEmbedding N L)

/-- **The isomorphism moving the shift out of the Verdier embedding.** For `J` the embedding
`A/(A ⊓ N) ⥤ C/N` this is `J ((L y)⟦n⟧) ≅ (Q y)⟦n⟧`: the commutation of `J` with the shift,
followed by the shift of the characteristic isomorphism `L ⋙ J ≅ A.ι ⋙ Q`. It is the target
isomorphism of the `CategoryTheory.Iso.homCongr` inside
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift`. -/
noncomputable def verdierEmbeddingShiftIso (y : A.FullSubcategory) (n : ℤ) :
    (A.verdierEmbedding N L).obj ((L.obj y)⟦n⟧) ≅ (N.trW.Q.obj y.1)⟦n⟧ :=
  letI := A.verdierEmbeddingCommShift N L
  ((A.verdierEmbedding N L).commShiftIso n).app (L.obj y) ≪≫
    (shiftFunctor N.trW.Localization n).mapIso ((verdierEmbeddingCompIso A N L).app y)

omit [A.IsClosedUnderIsomorphisms] [HasZeroObject D] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [L.IsTriangulated] in
/-- **The second engine, computed.** The bijection
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift` takes `f` to the image of `f` under
the Verdier embedding `J`, conjugated by the characteristic isomorphism `L ⋙ J ≅ A.ι ⋙ Q` on the
source and by `CategoryTheory.ObjectProperty.verdierEmbeddingShiftIso` on the target.

The forward map of `CategoryTheory.Functor.FullyFaithful.homEquiv` is `J.map` and the forward map
of `CategoryTheory.Iso.homCongr` is conjugation, so this is a definitional equality. Links 3 and
4 both reduce to it. -/
@[simp] theorem homEquivVerdierEmbeddingShift_apply [A.IsVerdierLeftLocalizing N]
    (x y : A.FullSubcategory) (n : ℤ) (f : L.obj x ⟶ (L.obj y)⟦n⟧) :
    homEquivVerdierEmbeddingShift A N L x y n f =
      ((verdierEmbeddingCompIso A N L).app x).inv ≫ (A.verdierEmbedding N L).map f ≫
        (A.verdierEmbeddingShiftIso N L y n).hom :=
  rfl

omit [A.IsClosedUnderIsomorphisms] [HasZeroObject D] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [L.IsTriangulated] in
/-- **The inverse of the second engine, characterised.** The inverse of
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift` does not compute: its first factor
is `CategoryTheory.Functor.FullyFaithful.preimage` for
`CategoryTheory.ObjectProperty.fullyFaithfulVerdierEmbedding`, a choice of preimage supplied by
the fullness of the embedding and carrying no formula. It is pinned down by the forward
direction, which does compute. -/
theorem homEquivVerdierEmbeddingShift_symm_eq_iff [A.IsVerdierLeftLocalizing N]
    (x y : A.FullSubcategory) (n : ℤ) (g : N.trW.Q.obj x.1 ⟶ (N.trW.Q.obj y.1)⟦n⟧)
    (f : L.obj x ⟶ (L.obj y)⟦n⟧) :
    (homEquivVerdierEmbeddingShift A N L x y n).symm g = f ↔
      ((verdierEmbeddingCompIso A N L).app x).inv ≫ (A.verdierEmbedding N L).map f ≫
        (A.verdierEmbeddingShiftIso N L y n).hom = g := by
  rw [equiv_symm_eq_iff_apply_eq, homEquivVerdierEmbeddingShift_apply]

omit [A.IsClosedUnderIsomorphisms] [HasZeroObject D] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [L.IsTriangulated] in
/-- The second engine is injective, which is what makes
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_symm_eq_iff` a characterisation: at
most one `f` satisfies that equation. -/
theorem homEquivVerdierEmbeddingShift_injective [A.IsVerdierLeftLocalizing N]
    (x y : A.FullSubcategory) (n : ℤ) :
    Function.Injective (homEquivVerdierEmbeddingShift A N L x y n) :=
  (homEquivVerdierEmbeddingShift A N L x y n).injective

end Verdier

/-! ### Link 2: morphisms into a shift of a reflected object -/

section Reflector

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)
  {D : Type u'} [Category.{v'} D] (Q : C ⥤ D)
  [Q.IsLocalization P.localizingClosure.{w}.trW] [HasShift D ℤ] [IsTriangulated C] [Q.CommShift ℤ]
  {L : C ⥤ C} {η : 𝟭 C ⟶ L}

omit [HasShift D ℤ] [IsTriangulated C] [Q.CommShift ℤ] in
/-- **The image of the unit under the quotient is an isomorphism.** This is
`CategoryTheory.ObjectProperty.localizingClosureUnitIso` read as a statement about `Q (η X)`
itself; it is what makes the `CategoryTheory.inv` in
`CategoryTheory.ObjectProperty.homEquivReflectorShift_apply_inv` meaningful. -/
theorem isIso_map_localizingClosure_unit_app
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (X : C) : IsIso (Q.map (η.app X)) :=
  ⟨(P.localizingClosureUnitIso Q hη X).inv,
    (P.localizingClosureUnitIso Q hη X).hom_inv_id,
    (P.localizingClosureUnitIso Q hη X).inv_hom_id⟩

/-- **Link 2, computed.** On a morphism `f : A ⟶ (L X)⟦n⟧` the bijection
`CategoryTheory.ObjectProperty.homEquivReflectorShift` is `Q f`, followed by the commutation of
`Q` with the shift and by the inverse of the shift of the unit isomorphism `Q X ≅ Q (L X)`.

Every factor computes. The first is `Equiv.ofBijective` applied to `Q.map`, whose forward map is
`Q.map` by `CategoryTheory.ObjectProperty.homEquivMapOfRightOrthogonalShift_apply`; the second is
a `CategoryTheory.Iso.homCongr` at the identity on the source; and the third is the inverse of a
`CategoryTheory.Iso.homCongr`, again at the identity on the source, so it is postcomposition with
an inverse. -/
@[simp] theorem homEquivReflectorShift_apply
    (hL : ∀ X, P.localizingClosure.{w}.rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (A X : C) (n : ℤ) (f : A ⟶ (L.obj X)⟦n⟧) :
    P.homEquivReflectorShift Q hL hη A X n f =
      Q.map f ≫ ((Q.commShiftIso n).app (L.obj X)).hom ≫
        (shiftFunctor D n).map (P.localizingClosureUnitIso Q hη X).inv := by
  simp [homEquivReflectorShift, homEquivShiftLocalizingClosureUnit]

/-- **Link 2 as a left fraction.** The same value as
`CategoryTheory.ObjectProperty.homEquivReflectorShift_apply`, written with `CategoryTheory.inv`
of the shifted image of the unit: `Q(η)⟦n⟧⁻¹ ∘ Q(f)`, with the commutation of `Q` with the shift
in between. This is the shape in which the compatibility of the chain of [Stacks, Tag 09LK] with
a comparison cocone is stated. -/
theorem homEquivReflectorShift_apply_inv
    (hL : ∀ X, P.localizingClosure.{w}.rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (A X : C) (n : ℤ) (f : A ⟶ (L.obj X)⟦n⟧)
    [IsIso ((shiftFunctor D n).map (Q.map (η.app X)))] :
    P.homEquivReflectorShift Q hL hη A X n f =
      Q.map f ≫ ((Q.commShiftIso n).app (L.obj X)).hom ≫
        CategoryTheory.inv ((shiftFunctor D n).map (Q.map (η.app X))) := by
  have h : (shiftFunctor D n).map (P.localizingClosureUnitIso Q hη X).inv =
      CategoryTheory.inv ((shiftFunctor D n).map (Q.map (η.app X))) :=
    IsIso.eq_inv_of_hom_inv_id (by
      rw [← P.localizingClosureUnitIso_hom Q hη X, ← Functor.map_comp, Iso.hom_inv_id,
        Functor.map_id]
      rfl)
  rw [homEquivReflectorShift_apply, h]

/-- **Link 2 with the unit cleared.** The value of
`CategoryTheory.ObjectProperty.homEquivReflectorShift` postcomposed with the shifted image of the
unit is `Q f` followed by the commutation of `Q` with the shift. This is the left-fraction
characterisation with no `CategoryTheory.inv` in it, so it needs no `IsIso` instance. -/
theorem homEquivReflectorShift_apply_comp
    (hL : ∀ X, P.localizingClosure.{w}.rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (A X : C) (n : ℤ) (f : A ⟶ (L.obj X)⟦n⟧) :
    P.homEquivReflectorShift Q hL hη A X n f ≫ (shiftFunctor D n).map (Q.map (η.app X)) =
      Q.map f ≫ ((Q.commShiftIso n).app (L.obj X)).hom := by
  rw [homEquivReflectorShift_apply, ← P.localizingClosureUnitIso_hom Q hη X, assoc, assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  simp

/-- **The inverse of link 2, computed.** Unlike links 3 and 4 the bijection of link 2 has a
computing forward map at every factor, so this characterisation of its inverse is a genuine
equation and not a substitute for a missing one. -/
theorem homEquivReflectorShift_symm_eq_iff
    (hL : ∀ X, P.localizingClosure.{w}.rightOrthogonal (L.obj X))
    (hη : ∀ (X Z : C) (f : Z ⟶ X) (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
      Triangle.mk f (η.app X) g ∈ distTriang C → P.localizingClosure.{w} Z)
    (A X : C) (n : ℤ) (g : Q.obj A ⟶ (Q.obj X)⟦n⟧) (f : A ⟶ (L.obj X)⟦n⟧) :
    (P.homEquivReflectorShift Q hL hη A X n).symm g = f ↔
      Q.map f ≫ ((Q.commShiftIso n).app (L.obj X)).hom ≫
        (shiftFunctor D n).map (P.localizingClosureUnitIso Q hη X).inv = g := by
  rw [equiv_symm_eq_iff_apply_eq, homEquivReflectorShift_apply]

end Reflector

end ObjectProperty

end CategoryTheory

namespace DGCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace RightModule

/-! ### Link 1: the Yoneda lemma on cohomology -/

section Link1

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

attribute [local implicit_reducible] DGCategory.K

/-- Evaluation at the identity, restricted to the cocycles, is evaluation at the identity. -/
@[simp] theorem yonedaCocyclesEquiv_val (M : RightModule.{v} C) (X : C.Obj) (p : ℤ)
    (f : (rightModuleCategory.{v} C).cocyclesSubmodule (yonedaRightModule C X) M p) :
    (yonedaCocyclesEquiv M X p f : M.obj X p) = yonedaEval M X p f.1 := rfl

/-- The comparison of the cocycles of `(M⟦n⟧) X` with those of `M X` does not change the
underlying element: the two are submodules of the same module. -/
@[simp] theorem gradedCocyclesShiftEquiv_val (M : RightModule.{v} C) (n : ℤ) (X : C.Obj) (i : ℤ)
    (a : gradedCocycles (shift M n) X i) :
    (gradedCocyclesShiftEquiv M n X i a : M.obj X (i + n)) = (a : (shift M n).obj X i) := rfl

/-- The comparison of the cocycles of `(M⟦n⟧) X` with those of `M X`, with the target degree an
argument, as in `DGCategory.RightModule.gradedCohomologyShiftEquiv`. At `i = 0` the degree on the
right can then be `n` and not `0 + n`. -/
def gradedCocyclesShiftEquiv' (M : RightModule.{v} C) (n : ℤ) (X : C.Obj) {i j : ℤ}
    (h : i + n = j) : gradedCocycles (shift M n) X i ≃ₗ[R] gradedCocycles M X j := by
  subst h
  exact gradedCocyclesShiftEquiv M n X i

/-- At the identity degree equation the comparison with the target degree an argument is the
comparison of `DGCategory.RightModule.gradedCocyclesShiftEquiv`. -/
@[simp] theorem gradedCocyclesShiftEquiv'_rfl (M : RightModule.{v} C) (n : ℤ) (X : C.Obj)
    (i : ℤ) (a : gradedCocycles (shift M n) X i) :
    gradedCocyclesShiftEquiv' M n X (rfl : i + n = i + n) a = gradedCocyclesShiftEquiv M n X i a :=
  rfl

/-- **The cohomology of a shift, computed.** `DGCategory.RightModule.gradedCohomologyShiftEquiv`
takes the class of a cocycle to the class of the same cocycle, read in the shifted degree. -/
@[simp] theorem gradedCohomologyShiftEquiv_mk (M : RightModule.{v} C) (n : ℤ) (X : C.Obj)
    {i j : ℤ} (h : i + n = j) (a : gradedCocycles (shift M n) X i) :
    gradedCohomologyShiftEquiv M n X h (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (gradedCocyclesShiftEquiv' M n X h a) := by
  subst h
  rfl

/-- **The Yoneda lemma on cohomology, computed.**
`DGCategory.RightModule.yonedaHomCohomologyEquiv` takes the class of a cocycle of the Hom complex
`Hom^•(h_X, M)` to the class of its evaluation at the identity. -/
@[simp] theorem yonedaHomCohomologyEquiv_mk (M : RightModule.{v} C) (X : C.Obj) (p : ℤ)
    (f : (rightModuleCategory.{v} C).cocyclesSubmodule (yonedaRightModule C X) M p) :
    yonedaHomCohomologyEquiv M X p (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (yonedaCocyclesEquiv M X p f) :=
  rfl

/-- **The Yoneda lemma in the homotopy category, computed.**
`DGCategory.RightModule.homKEquivGradedCohomology` takes the homotopy class of a degree-zero
cocycle `f : h_X ⟶ M` to the cohomology class of its evaluation at the identity. -/
@[simp] theorem homKEquivGradedCohomology_mk (M : (rightModuleCategory.{v} C).K) (X : C.Obj)
    (f : (rightModuleCategory.{v} C).cocyclesSubmodule (yonedaRightModule C X) M 0) :
    homKEquivGradedCohomology M X (Quotient.mk _ f) =
      Submodule.Quotient.mk (yonedaCocyclesEquiv M X 0 f) :=
  rfl

/-- **Link 1, computed.** The bijection
`DGCategory.RightModule.homShiftEquivGradedCohomology` takes the homotopy class of a degree-zero
cocycle `f : h_X ⟶ M⟦n⟧` to the degree-`n` cohomology class of its evaluation at the identity,
read in `M X`.

Every factor computes: `DGCategory.homotopyClassEquiv` is a `Quotient.congr` at the identity,
`DGCategory.RightModule.yonedaHomCohomologyEquiv` is a `Submodule.Quotient.equiv`, and
`DGCategory.RightModule.gradedCohomologyShiftEquiv` is one too after its degree equation is
substituted. -/
@[simp] theorem homShiftEquivGradedCohomology_mk (M : (rightModuleCategory.{v} C).K) (X : C.Obj)
    (n : ℤ)
    (f : (rightModuleCategory.{v} C).cocyclesSubmodule (yonedaRightModule C X) (shift M n) 0) :
    homShiftEquivGradedCohomology M X n (Quotient.mk _ f) =
      Submodule.Quotient.mk (gradedCocyclesShiftEquiv' M n X (zero_add n)
        (yonedaCocyclesEquiv (shift M n) X 0 f)) :=
  gradedCohomologyShiftEquiv_mk M n X (zero_add n) _

/-- **Link 1 in the form the chain uses, computed.** The same value as
`DGCategory.RightModule.homShiftEquivGradedCohomology_mk`, read through
`DGCategory.RightModule.gradedCohomology_evaluation` — the explicit cohomology of `ev_K M` over
the endomorphism complex is the explicit cohomology of `M` at `K`, so the two bijections have the
same value. -/
@[simp] theorem homShiftEquivEvaluationGradedCohomology_mk (M : (rightModuleCategory.{v} C).K)
    (K : C.Obj) (e : (endDGCategory C K).Obj) (n : ℤ)
    (f : (rightModuleCategory.{v} C).cocyclesSubmodule (yonedaRightModule C K) (shift M n) 0) :
    homShiftEquivEvaluationGradedCohomology M K e n (Quotient.mk _ f) =
      Submodule.Quotient.mk (gradedCocyclesShiftEquiv' M n K (zero_add n)
        (yonedaCocyclesEquiv (shift M n) K 0 f)) :=
  homShiftEquivGradedCohomology_mk M K n f

/-- **The inverse of link 1, computed.** The inverse of
`DGCategory.RightModule.homShiftEquivGradedCohomology` is characterised by the forward direction,
which is a closed formula; as with link 2 and unlike links 3 and 4, this is a genuine equation
and not a substitute for a missing one. On a morphism presented as the homotopy class of a
cocycle the right-hand side is computed by
`DGCategory.RightModule.homShiftEquivGradedCohomology_mk`. -/
theorem homShiftEquivGradedCohomology_symm_eq_iff (M : (rightModuleCategory.{v} C).K)
    (X : C.Obj) (n : ℤ) (c : gradedCohomology M X n) (g : yonedaObjK X ⟶ M⟦n⟧) :
    (homShiftEquivGradedCohomology M X n).symm c = g ↔
      homShiftEquivGradedCohomology M X n g = c := by
  exact equiv_symm_eq_iff_apply_eq _ _ _

/-- Link 1 is injective, which is what makes
`DGCategory.RightModule.homShiftEquivGradedCohomology_symm_eq_iff` a characterisation. -/
theorem homShiftEquivGradedCohomology_injective (M : (rightModuleCategory.{v} C).K) (X : C.Obj)
    (n : ℤ) : Function.Injective (homShiftEquivGradedCohomology M X n) :=
  (homShiftEquivGradedCohomology M X n).injective

/-- **The inverse of Tag 09LC's bijection, computed.** `DGCategory.homotopyClassEquiv` is a
`Quotient.congr` at the identity, so its inverse takes the cohomology class of a degree-zero
cocycle back to the homotopy class of the same cocycle. This is the companion of
`DGCategory.homotopyClassEquiv_mk`, and it is what makes the `.symm` in
`DGCategory.RightModule.homYonedaObjKEquiv` compute. -/
@[simp] theorem homotopyClassEquiv_symm_mk (A : DGCategory.{v, u} R) (x y : A.Obj)
    (f : A.cocyclesSubmodule x y 0) :
    (A.homotopyClassEquiv x y).symm (Submodule.Quotient.mk f) = Quotient.mk _ f := rfl

/-- **The Yoneda functor on homotopy categories, computed.** The bijection
`DGCategory.RightModule.homYonedaObjKEquiv`, which is full faithfulness of the differential
graded Yoneda functor on homotopy categories, takes the homotopy class of a degree-zero cocycle
`h_x ⟶ h_y` to the homotopy class of its evaluation at the identity, read as a cocycle of the
Hom complex `C(x, y)`.

Both factors compute: `DGCategory.RightModule.homKEquivGradedCohomology` by
`DGCategory.RightModule.homKEquivGradedCohomology_mk` and the inverse of
`DGCategory.homotopyClassEquiv` by
`DGCategory.RightModule.homotopyClassEquiv_symm_mk`. -/
@[simp] theorem homYonedaObjKEquiv_mk (x y : C.K)
    (f : (rightModuleCategory.{v} C).cocyclesSubmodule (yonedaRightModule C (x : C.Obj))
      (yonedaObjK (y : C.Obj)) 0) :
    homYonedaObjKEquiv x y (Quotient.mk _ f) =
      Quotient.mk _ (yonedaCocyclesEquiv (yonedaObjK (y : C.Obj)) (x : C.Obj) 0 f) :=
  rfl

end Link1

/-! ### Link 3: the Verdier quotient of the triangulated envelope -/

section Link3

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R) [Nonempty C.Obj]
  {ι : Type*} (G : ι → C.Obj)

/-- **The third link over arbitrary objects of `A`, computed.** This is the second engine,
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_apply`, at the triangulated envelope
of the representables; the definition is peeled off and nothing is reproved. -/
@[simp] theorem homEquivYonedaEnvelopeVerdier_apply
    (x y : (yonedaEnvelope C).FullSubcategory) (n : ℤ)
    (f : (yonedaEnvelopeQ C G).obj x ⟶ ((yonedaEnvelopeQ C G).obj y)⟦n⟧) :
    homEquivYonedaEnvelopeVerdier C G x y n f =
      ((verdierEmbeddingCompIso (yonedaEnvelope C) (yonedaLocalizing C G)
            (yonedaEnvelopeQ C G)).app x).inv ≫
        ((yonedaEnvelope C).verdierEmbedding (yonedaLocalizing C G)
            (yonedaEnvelopeQ C G)).map f ≫
          ((yonedaEnvelope C).verdierEmbeddingShiftIso (yonedaLocalizing C G)
            (yonedaEnvelopeQ C G) y n).hom :=
  rfl

/-- **Link 3, computed.** The bijection
`DGCategory.RightModule.homEquivDerivedYonedaVerdier'` is the second engine at the representables:
the image under the Verdier embedding, conjugated by the characteristic isomorphism on the source
and by `CategoryTheory.ObjectProperty.verdierEmbeddingShiftIso` on the target. -/
@[simp] theorem homEquivDerivedYonedaVerdier'_apply (x y : C.Obj) (n : ℤ)
    (f : (yonedaEnvelopeQ C G).obj (yonedaEnvelopeObj C x) ⟶
      ((yonedaEnvelopeQ C G).obj (yonedaEnvelopeObj C y))⟦n⟧) :
    homEquivDerivedYonedaVerdier' C G x y n f =
      ((verdierEmbeddingCompIso (yonedaEnvelope C) (yonedaLocalizing C G)
            (yonedaEnvelopeQ C G)).app (yonedaEnvelopeObj C x)).inv ≫
        ((yonedaEnvelope C).verdierEmbedding (yonedaLocalizing C G)
            (yonedaEnvelopeQ C G)).map f ≫
          ((yonedaEnvelope C).verdierEmbeddingShiftIso (yonedaLocalizing C G)
            (yonedaEnvelopeQ C G) (yonedaEnvelopeObj C y) n).hom :=
  rfl

/-- **The inverse of link 3, characterised.** The inverse of
`DGCategory.RightModule.homEquivDerivedYonedaVerdier'` does not compute: it applies
`CategoryTheory.Functor.FullyFaithful.preimage` for the Verdier embedding, which is a choice of
preimage supplied by fullness and carries no formula. What is available instead is this
characterisation by the forward direction, which does compute. -/
theorem homEquivDerivedYonedaVerdier'_symm_eq_iff (x y : C.Obj) (n : ℤ)
    (g : (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q.obj (yonedaObjK x) ⟶
      ((ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q.obj (yonedaObjK y))⟦n⟧)
    (f : (yonedaEnvelopeQ C G).obj (yonedaEnvelopeObj C x) ⟶
      ((yonedaEnvelopeQ C G).obj (yonedaEnvelopeObj C y))⟦n⟧) :
    (homEquivDerivedYonedaVerdier' C G x y n).symm g = f ↔
      homEquivDerivedYonedaVerdier' C G x y n f = g := by
  exact equiv_symm_eq_iff_apply_eq _ _ _

/-- Link 3 is injective, which is what makes
`DGCategory.RightModule.homEquivDerivedYonedaVerdier'_symm_eq_iff` a characterisation. -/
theorem homEquivDerivedYonedaVerdier'_injective (x y : C.Obj) (n : ℤ) :
    Function.Injective (homEquivDerivedYonedaVerdier' C G x y n) :=
  (homEquivDerivedYonedaVerdier' C G x y n).injective

end Link3

/-! ### Link 4: the source side of the chain -/

section Link4

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R) {ι : Type*} (G : ι → C.Obj)

attribute [local implicit_reducible] DGCategory.K

variable [Preadditive C.K] [HasZeroObject C.K] [HasShift C.K ℤ]
  [∀ n : ℤ, (shiftFunctor C.K n).Additive] [Pretriangulated C.K]
  [((yonedaDGFunctor C).onK).CommShift ℤ] [((yonedaDGFunctor C).onK).IsTriangulated]

attribute [local instance] isLocalization_yonedaLift_comp

/-- **The third link over the essential image, computed.** This is the second engine,
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_apply`, at the essential image of
the differential graded Yoneda functor. -/
@[simp] theorem homEquivYonedaImageVerdier_apply (x y : (yonedaImage C).FullSubcategory) (n : ℤ)
    (f : (yonedaImageQ C G).obj x ⟶ ((yonedaImageQ C G).obj y)⟦n⟧) :
    homEquivYonedaImageVerdier C G x y n f =
      ((verdierEmbeddingCompIso (yonedaImage C) (yonedaLocalizing C G)
            (yonedaImageQ C G)).app x).inv ≫
        ((yonedaImage C).verdierEmbedding (yonedaLocalizing C G) (yonedaImageQ C G)).map f ≫
          ((yonedaImage C).verdierEmbeddingShiftIso (yonedaLocalizing C G)
            (yonedaImageQ C G) y n).hom :=
  rfl

/-- **Link 4, computed.** The bijection
`DGCategory.RightModule.homEquivDerivedYonedaOnK'` is the first engine
(`CategoryTheory.homShiftEquivOfIsLocalization`, comparing `q` with the localization
`Φ' ⋙ (A₀ ⥤ A₀/(A₀ ⊓ N))`) followed by the second engine over the essential image. Both are
computed once and for all above, so `simp` rewrites this to a closed formula in the images under
the comparison equivalence and the Verdier embedding. -/
@[simp] theorem homEquivDerivedYonedaOnK'_apply {DA : Type u'} [Category.{v'} DA]
    [HasShift DA ℤ] (q : C.K ⥤ DA) [q.IsLocalization (yonedaInverseImage C G).trW]
    [q.CommShift ℤ] (x y : C.K) (n : ℤ) (f : q.obj x ⟶ (q.obj y)⟦n⟧) :
    homEquivDerivedYonedaOnK' C G q x y n f =
      homEquivYonedaImageVerdier C G ((yonedaLift C).obj x) ((yonedaLift C).obj y) n
        (homShiftEquivOfIsLocalization (yonedaInverseImage C G).trW q
          (yonedaLift C ⋙ yonedaImageQ C G) x y n f) :=
  rfl

/-- **The inverse of link 4, characterised.** The inverse of
`DGCategory.RightModule.homEquivDerivedYonedaOnK'` does not compute, and the obstruction occurs
twice: `CategoryTheory.Functor.FullyFaithful.preimage` for the comparison equivalence of two
localizations (`CategoryTheory.Localization.uniq`, obtained from a universal property) and the
same for the Verdier embedding (obtained from fullness). Neither carries a formula.

This characterisation by the forward direction is what replaces an apply-lemma, and it discharges
a compatibility stated at a value of the inverse: the goal `e.symm c = g` becomes
`<closed formula at g> = c`, and the closed formula is produced by `simp` from
`DGCategory.RightModule.homEquivDerivedYonedaOnK'_apply`,
`CategoryTheory.homShiftEquivOfIsLocalization_apply` and
`CategoryTheory.ObjectProperty.homEquivVerdierEmbeddingShift_apply`. -/
theorem homEquivDerivedYonedaOnK'_symm_eq_iff {DA : Type u'} [Category.{v'} DA]
    [HasShift DA ℤ] (q : C.K ⥤ DA) [q.IsLocalization (yonedaInverseImage C G).trW]
    [q.CommShift ℤ] (x y : C.K) (n : ℤ)
    (g : (ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q.obj
        (yonedaObjK (x : C.Obj)) ⟶
      ((ofObj fun i ↦ yonedaObjK (G i)).localizingClosure.{v}.trW.Q.obj
        (yonedaObjK (y : C.Obj)))⟦n⟧)
    (f : q.obj x ⟶ (q.obj y)⟦n⟧) :
    (homEquivDerivedYonedaOnK' C G q x y n).symm g = f ↔
      homEquivDerivedYonedaOnK' C G q x y n f = g := by
  exact equiv_symm_eq_iff_apply_eq _ _ _

/-- Link 4 is injective, which is what makes
`DGCategory.RightModule.homEquivDerivedYonedaOnK'_symm_eq_iff` a characterisation: at most one
`f` satisfies that equation, so an inverse pinned down by it is pinned down uniquely. -/
theorem homEquivDerivedYonedaOnK'_injective {DA : Type u'} [Category.{v'} DA] [HasShift DA ℤ]
    (q : C.K ⥤ DA) [q.IsLocalization (yonedaInverseImage C G).trW] [q.CommShift ℤ]
    (x y : C.K) (n : ℤ) :
    Function.Injective (homEquivDerivedYonedaOnK' C G q x y n) :=
  (homEquivDerivedYonedaOnK' C G q x y n).injective

end Link4

end RightModule

end DGCategory

end
