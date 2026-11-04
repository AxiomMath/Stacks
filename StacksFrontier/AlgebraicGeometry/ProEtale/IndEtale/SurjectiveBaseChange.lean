module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleSite
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.QuotientLift

/-!
# Base change of ind-étale algebras along a surjective ring map

Stacks 097P constructs, for a ring `A` and an ideal `I ⊆ A`, a right adjoint of extension of
scalars `IndEtaleAlgebra A ⥤ IndEtaleAlgebra (A ⧸ I)`
(`AlgebraicGeometry.ProEtale.indEtaleBaseChange_hasFullyFaithfulRightAdjoint`).  This file
defines extension of scalars along an arbitrary ring map, restricted to ind-étale algebras,
observes that for a quotient projection it is the functor of Stacks 097P on the nose, and shows
that it has a right adjoint whenever the ring map is surjective, for instance for the ring map on
global sections of a closed immersion of affine schemes (Stacks 09BK).

## Main definitions

* `AlgebraicGeometry.ProEtale.indEtaleExtendScalars` — extension of scalars along a ring map
  `φ : R ⟶ S`, as a functor `IndEtaleAlgebra R ⥤ IndEtaleAlgebra S`.
* `AlgebraicGeometry.ProEtale.indEtaleRestrictScalarsOfIso` — restriction of scalars along an
  *isomorphism* of rings, as a functor in the other direction.  Restriction along a general ring
  map does not preserve ind-étaleness.
* `AlgebraicGeometry.ProEtale.indEtaleExtendScalarsComp` and
  `AlgebraicGeometry.ProEtale.indEtaleExtendScalarsId` — the functoriality isomorphisms.
* `AlgebraicGeometry.ProEtale.indEtaleExtendScalarsIsoAdj` — along an isomorphism of rings,
  extension of scalars is left adjoint to restriction of scalars.
* `AlgebraicGeometry.ProEtale.indEtaleExtendScalarsAppTopObjIso` — extension of scalars along
  `Γ(X, ⊤) ⟶ Γ(Z, ⊤)` agrees objectwise with the base-change functor `u` of Stacks 09BK.

## Main results

* `AlgebraicGeometry.ProEtale.indEtaleExtendScalars_quotient` — for the projection `A ⟶ A ⧸ I`
  this functor *is* `AlgebraicGeometry.ProEtale.indEtaleQuotientBaseChange`, by `rfl`.
* `AlgebraicGeometry.ProEtale.isLeftAdjoint_indEtaleExtendScalars_iso` — extension of scalars
  along an isomorphism of rings has a right adjoint.
* `AlgebraicGeometry.ProEtale.isLeftAdjoint_indEtaleExtendScalars_of_surjective` — extension of
  scalars of ind-étale algebras along a surjective ring map has a right adjoint.
* `AlgebraicGeometry.ProEtale.isLeftAdjoint_indEtaleExtendScalars_appTop_of_isClosedImmersion` —
  the same for the ring map on global sections of a closed immersion with affine target.

## Implementation notes

* `indEtaleExtendScalars φ` is `CategoryTheory.Under.pushout φ` cut down to the ind-étale
  objects, the cut being legitimate by `CategoryTheory.MorphismProperty.ind_underObj_pushout`.
  That is the same formula as `indEtaleQuotientBaseChange`, which is why
  `indEtaleExtendScalars_quotient` is `rfl` and no transport lemma is needed on that side.
* The functoriality isomorphisms are obtained from `CategoryTheory.Under.pushoutComp` and
  `CategoryTheory.Under.pushoutId` by `CategoryTheory.Functor.fullyFaithfulCancelRight` along the
  inclusion of the full subcategory: `indEtaleExtendScalars φ ⋙ ι` and `ι ⋙ Under.pushout φ`
  are the same functor definitionally, so the whiskered isomorphism transfers with no coercion.
* The adjunction along an isomorphism is `CategoryTheory.Under.mapPushoutAdj` restricted to the
  two full subcategories by `CategoryTheory.Adjunction.restrictFullyFaithful`, both comparison
  isomorphisms being `CategoryTheory.Iso.refl` for the same definitional reason.
* Surjectivity enters only through `RingHom.quotientKerEquivOfSurjective`: a surjection factors
  as its own kernel projection followed by an isomorphism, and the two halves are handled by
  Stacks 097P and by `indEtaleExtendScalarsIsoAdj` respectively.
* `indEtaleExtendScalarsAppTopObjIso` is the pushout isomorphism
  `AlgebraicGeometry.ProEtale.proetaleBaseChangeAppTopPushoutIso` transported into the ind-étale
  full subcategory; the pushout square itself is
  `AlgebraicGeometry.ProEtale.isPushout_appTop_pullback_proEt`.
* The lemmas `indEtaleBaseChange_adjunction` and
  `indEtaleBaseChange_hasFullyFaithfulRightAdjoint`
  (`StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.QuotientLift`) are about the quotient functor
  `indEtaleQuotientBaseChange`, not about the general `indEtaleExtendScalars` of this file.

## References

* [Stacks Project, Tag 097P](https://stacks.math.columbia.edu/tag/097P)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- Extension of scalars along a ring map `φ : R ⟶ S`, restricted to ind-étale algebras.  On
objects it sends an ind-étale `R`-algebra `R ⟶ C` to `S ⟶ S ⊗_R C`; the result is ind-étale
because ind-étale ring maps are stable under cobase change. -/
public noncomputable def indEtaleExtendScalars {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    IndEtaleAlgebra ↥R ⥤ IndEtaleAlgebra ↥S :=
  (ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of ↥S))).lift ((ObjectProperty.ι _) ⋙ Under.pushout φ)
    (fun V ↦ MorphismProperty.ind_underObj_pushout φ V.property)

/-- For the projection `A ⟶ A ⧸ I`, extension of scalars of ind-étale algebras is the functor of
Stacks 097P. -/
public theorem indEtaleExtendScalars_quotient (A : Type u) [CommRing A] (I : Ideal A) :
    indEtaleExtendScalars (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
      indEtaleQuotientBaseChange A I :=
  rfl

/-- Extension of scalars along a composite is the composite of the extensions of scalars. -/
public noncomputable def indEtaleExtendScalarsComp {R S T : CommRingCat.{u}} (φ : R ⟶ S)
    (ψ : S ⟶ T) : indEtaleExtendScalars (φ ≫ ψ) ≅
      indEtaleExtendScalars φ ⋙ indEtaleExtendScalars ψ :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _) (Under.pushoutComp φ ψ))

/-- Extension of scalars along the identity is the identity. -/
public noncomputable def indEtaleExtendScalarsId (R : CommRingCat.{u}) :
    indEtaleExtendScalars (𝟙 R) ≅ 𝟭 (IndEtaleAlgebra ↥R) :=
  Functor.fullyFaithfulCancelRight (ObjectProperty.ι _)
    (Functor.isoWhiskerLeft (ObjectProperty.ι _) Under.pushoutId)

/-- Restriction of scalars along an isomorphism of rings, restricted to ind-étale algebras.  An
ind-étale `S`-algebra becomes an ind-étale `R`-algebra because ind-étaleness of a ring map is
unchanged by composing with an isomorphism on the left. -/
public noncomputable def indEtaleRestrictScalarsOfIso {R S : CommRingCat.{u}} (e : R ≅ S) :
    IndEtaleAlgebra ↥S ⥤ IndEtaleAlgebra ↥R :=
  (ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
    (X := CommRingCat.of ↥R))).lift ((ObjectProperty.ι _) ⋙ Under.map e.hom)
    (fun V ↦ by
      have hV : MorphismProperty.ind.{u} (CommRingCat.etale.{u}) V.obj.hom :=
        (MorphismProperty.ind_iff_ind_underMk _).mpr V.property
      have hiso : MorphismProperty.isomorphisms CommRingCat.{u} e.hom := inferInstance
      exact (MorphismProperty.ind_iff_ind_underMk _).mp
        (MorphismProperty.RespectsLeft.precomp _ hiso _ hV))

/-- Along an isomorphism of rings, extension of scalars of ind-étale algebras is left adjoint to
restriction of scalars.  This is `CategoryTheory.Under.mapPushoutAdj` restricted to the ind-étale
full subcategories. -/
public noncomputable def indEtaleExtendScalarsIsoAdj {R S : CommRingCat.{u}} (e : R ≅ S) :
    indEtaleExtendScalars e.hom ⊣ indEtaleRestrictScalarsOfIso e :=
  Adjunction.restrictFullyFaithful (Under.mapPushoutAdj e.hom)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Iso.refl _) (Iso.refl _)

/-- Extension of scalars of ind-étale algebras along an isomorphism of rings has a right
adjoint. -/
public theorem isLeftAdjoint_indEtaleExtendScalars_iso {R S : CommRingCat.{u}} (e : R ≅ S) :
    (indEtaleExtendScalars e.hom).IsLeftAdjoint :=
  ⟨_, ⟨indEtaleExtendScalarsIsoAdj e⟩⟩

/-- A surjective ring map is its own kernel projection followed by an isomorphism. -/
private theorem ofHom_quotient_comp_quotientKerEquiv {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Surjective φ.hom) :
    CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ.hom)) ≫
        (RingHom.quotientKerEquivOfSurjective hφ).toCommRingCatIso.hom = φ := by
  ext x
  exact RingHom.quotientKerEquivOfSurjective_apply_mk hφ x

/-- **The existence half of Stacks 097P, for a surjection.** Extension of scalars of ind-étale
algebras along a surjective ring map has a right adjoint.

The surjection `φ` factors as the projection onto `R ⧸ ker φ` followed by an isomorphism.
Extension of scalars along the projection has a right adjoint by Stacks 097P, extension of
scalars along the isomorphism has one by `indEtaleExtendScalarsIsoAdj`, and extension of
scalars along the composite is the composite of the two. -/
public theorem isLeftAdjoint_indEtaleExtendScalars_of_surjective {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (hφ : Function.Surjective φ.hom) :
    (indEtaleExtendScalars φ).IsLeftAdjoint := by
  set I : Ideal ↥R := RingHom.ker φ.hom
  set e : CommRingCat.of (↥R ⧸ I) ≅ S :=
    (RingHom.quotientKerEquivOfSurjective hφ).toCommRingCatIso
  have hquot : (indEtaleExtendScalars
      (CommRingCat.ofHom (Ideal.Quotient.mk I))).IsLeftAdjoint := by
    rw [indEtaleExtendScalars_quotient]
    exact ⟨_, indEtaleBaseChange_hasFullyFaithfulRightAdjoint ↥R I⟩
  have hiso : (indEtaleExtendScalars e.hom).IsLeftAdjoint :=
    isLeftAdjoint_indEtaleExtendScalars_iso e
  have hcomp : (indEtaleExtendScalars (CommRingCat.ofHom (Ideal.Quotient.mk I)) ⋙
      indEtaleExtendScalars e.hom).IsLeftAdjoint := inferInstance
  have hfac : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ e.hom = φ :=
    ofHom_quotient_comp_quotientKerEquiv φ hφ
  have hnat : indEtaleExtendScalars φ ≅
      indEtaleExtendScalars (CommRingCat.ofHom (Ideal.Quotient.mk I)) ⋙
        indEtaleExtendScalars e.hom :=
    eqToIso (congrArg (fun ψ ↦ indEtaleExtendScalars ψ) hfac.symm) ≪≫
      indEtaleExtendScalarsComp _ _
  exact ((Adjunction.ofIsLeftAdjoint _).ofNatIsoLeft hnat.symm).isLeftAdjoint

/-- Extension of scalars of ind-étale algebras along the ring map on global sections of a closed
immersion with affine target has a right adjoint, the map on global sections being
surjective. -/
public theorem isLeftAdjoint_indEtaleExtendScalars_appTop_of_isClosedImmersion
    {Z X : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i] :
    (indEtaleExtendScalars i.appTop).IsLeftAdjoint :=
  isLeftAdjoint_indEtaleExtendScalars_of_surjective _
    (i.app_surjective ⊤ (isAffineOpen_top X))

/-! ## Comparison with pro-étale base change on the affine ind-étale sites -/

section Comparison

variable {Z X : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X)

/-- Extension of scalars along `Γ(X, ⊤) ⟶ Γ(Z, ⊤)` agrees with the base-change functor `u` of
Stacks 09BK objectwise, under the identification of an affine ind-étale object with its
coordinate ring extension: the coordinate ring of `V ×_X Z` is the pushout of that of `V` along
`Γ(X, ⊤) ⟶ Γ(Z, ⊤)`, as objects under `Γ(Z, ⊤)`. -/
public noncomputable def indEtaleExtendScalarsAppTopObjIso (V : AppProetale X) :
    (indEtaleExtendScalars i.appTop).obj (appToIndEtaleAlgebra X V) ≅
      appToIndEtaleAlgebra Z ((appBaseChange i).obj V) :=
  ObjectProperty.isoMk _ (proetaleBaseChangeAppTopPushoutIso i V.obj V.property.1)

end Comparison

end AlgebraicGeometry.ProEtale

end
