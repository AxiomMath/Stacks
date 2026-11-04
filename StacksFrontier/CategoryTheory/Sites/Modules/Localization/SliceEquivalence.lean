module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.ToposLocalization
public import StacksFrontier.CategoryTheory.Sites.ToposLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The localization of a ringed topos at a sheaf is the slice topos

Let `X` be a ringed topos presented by a site `(C, J)` and let `F` be a sheaf of sets on `C`.
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/ToposLocalization.lean` builds the
localization of `X` at `F` on the site of elements of `F` and the morphism of ringed topoi
`j : X_F ⟶ X` it carries. This file identifies that localization with the slice topos
`Sh(C)/F` of Stacks 04GZ and reads the two set-valued functors of `j` across the
identification:

* the inverse image `j⁻¹`, which becomes "product with `F`, viewed over `F`";
* the lower shriek `j_!`, which becomes `Over.forget F`.

All three statements are extracted from the single package
`CategoryTheory.Presheaf.IsSheaf.sheafEquivalenceCostructuredArrowYoneda`, the sheaf-level form
of Stacks 0791, rather than reproved: that package supplies the equivalence, pins down its
inverse on underlying presheaves, and says that its functor followed by `Over.forget` is left
adjoint to restriction along the projection from the site of elements — which is exactly `j⁻¹`.

## Main definitions

* `AlgebraicGeometry.RingedTopos.localizationEquivalence`: the equivalence between the topos of
  the localization of `X` at `F` and the slice topos `Sh(C)/F`.
* `AlgebraicGeometry.RingedTopos.localizationInverseImageIso`: the inverse image of the
  localization morphism, read through that equivalence, is `toOver F`.
* `AlgebraicGeometry.RingedTopos.localizationEquivalence_fibers`: the inverse of the
  equivalence is the canonical fibre construction `(G, φ) ↦ ((U, s) ↦ {t ∈ G(U) | φ(t) = s})`,
  not merely some equivalence of the two topoi.
* `AlgebraicGeometry.RingedTopos.localizationShriekAdjunction`: the lower shriek of the
  localization morphism on sheaves of sets is `Over.forget F`.

## Main results

* `CategoryTheory.Iso.ext_of_left_comp_forgetAdjToOver_counit`: an isomorphism of a functor with
  `toOver F` is determined by its components followed by the projection `A ⊗ F ⟶ A`.
* `AlgebraicGeometry.RingedTopos.forget_localizationInverseImageIso_hom_app` and
  `AlgebraicGeometry.RingedTopos.localizationInverseImageIso_eq`: the comparison
  `localizationInverseImageIso` is the isomorphism whose components, after the projection
  `G × F ⟶ G`, are the counit of the lower shriek adjunction, and it is the only one.
* `AlgebraicGeometry.RingedTopos.fibreTranspose_shriek_counit`: the fibre transpose of the lower
  shriek counit is the unit of the equivalence. This is the functor-level form of Stacks 0791's
  bridge between the fibre description of the equivalence and the counit of `j_!`, and it is what
  lets a comparison built from fibres be compared with one built from the counit.

## Implementation notes

`localizationEquivalence` is the equivalence that Stacks 0791 constructs,
`CategoryTheory.Stacks.Topos.Localized.sheafEquivalence`, whose inverse is, on the nose, the fibre
functor `(φ : G ⟶ F) ↦ ((U, s) ↦ {t ∈ G(U) | φ(t) = s})`; the two characterisations below are
therefore immediate. Using the construction rather than an equivalence chosen from the
existential statement of Stacks 0791 is what lets constructions built on the localization, such
as the tautological section, be computed.

`localizationInverseImageIso` is a uniqueness-of-right-adjoints argument and nothing more.
Stacks 0791 exhibits `j⁻¹ ⋙ E.functor` as a right adjoint of `Over.forget F`
(`CategoryTheory.Stacks.Topos.Localized.forgetAdjunction`, whose hom-bijection is the one of
`Stacks.Topos.Localized.homEquivFiber`: a section of `j⁻¹G` over the fibre of `φ : H ⟶ F` is a
morphism `H ⟶ G`), and `forgetAdjToOver F` exhibits `toOver F` as a right adjoint of
`Over.forget F`; `Adjunction.rightAdjointUniq` identifies the two. The Cartesian structure on
`Sh(C, J)` in `toOver F` is Mathlib's sectionwise one, `CartesianMonoidalCategory.fullSubcategory`.

The site of elements, the localized ringed topos and the localization morphism are not
rebuilt here; this file adds only the comparison with the slice topos. Universes follow
`ToposLocalization.lean`: site morphisms and sections of `O` are taken in one universe `v`, which
is what Stacks 0791 needs in order to return a sheaf equivalence, and site objects in a universe
of their own.

## References

* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 04GZ](https://stacks.math.columbia.edu/tag/04GZ)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.OverPresheafAux

universe v₁ u₁ v u

namespace CategoryTheory

/-- **An isomorphism with `toOver F` is determined by its components through the projection.**
A morphism into `(toOver F).obj A` is a pair of a morphism to `A` and a morphism to `F`, of which
the second is its structure morphism and so is already determined; hence two isomorphisms of a
functor with `toOver F` whose components agree after the projection `A ⊗ F ⟶ A` agree.

The projection is spelled as the counit of `CategoryTheory.forgetAdjToOver`, which is the form in
which it appears in the descriptions of the comparison isomorphisms built from that adjunction. -/
theorem Iso.ext_of_left_comp_forgetAdjToOver_counit {C : Type u₁} [Category.{v₁} C]
    [CartesianMonoidalCategory C] {F : C} {P : C ⥤ Over F} {γ γ' : P ≅ toOver F}
    (h : ∀ A : C, (Over.forget F).map (γ.hom.app A) ≫ (forgetAdjToOver F).counit.app A =
      (Over.forget F).map (γ'.hom.app A) ≫ (forgetAdjToOver F).counit.app A) :
    γ = γ' :=
  Iso.ext (NatTrans.ext (funext fun A ↦ Over.OverMorphism.ext
    (CartesianMonoidalCategory.hom_ext _ _ (h A)
      ((Over.w (γ.hom.app A)).trans (Over.w (γ'.hom.app A)).symm))))

/-- For an equivalence `E`, the inverse image of `E.functor` applied to a morphism `u` and
followed by the counit is the inverse unit followed by `u`. -/
theorem Equivalence.inverse_map_functor_map_comp_counit {A : Type*} [Category A] {B : Type*}
    [Category B] (E : B ≌ A) {Z : B} {T : A} (u : Z ⟶ E.inverse.obj T) :
    E.inverse.map (E.functor.map u ≫ E.counit.app T) = E.unitInv.app Z ≫ u := by
  simp

end CategoryTheory

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{v, u, v}) [EssentiallySmall.{v} X.C] (F : X.Topos)

/-- The **canonical equivalence between the localization of `X` at `F` and the slice topos**
`Sh(C)/F`: the equivalence supplied by Stacks 0791, whose inverse is the fibre construction
recorded in `localizationEquivalence_fibers`. -/
@[stacks 04IE "equivalence with the slice topos"]
noncomputable def localizationEquivalence : (localizedRingedTopos X F).Topos ≌ Over F :=
  CategoryTheory.Stacks.Topos.Localized.sheafEquivalence F.obj X.J F.property

/-- The equivalence with the slice topos is the canonical fibre construction: on underlying
presheaves its inverse sends an object `φ : G ⟶ F` of `Sh(C)/F` to the presheaf
`(U, s) ↦ {t ∈ G(U) | φ(t) = s}` on the site of elements of `F`. -/
@[stacks 04IE "canonical identification with the slice topos"]
noncomputable def localizationEquivalence_fibers :
    (localizationEquivalence X F).inverse ⋙
      sheafToPresheaf (elementTopology X F) (Type v) ≅
      Over.post (X := F) (sheafToPresheaf X.J (Type v)) ⋙
        (overEquivPresheafCostructuredArrow F.obj).functor :=
  Iso.refl _

/-- **The lower shriek of the localization on sheaves of sets is `Over.forget F`**: read
through the equivalence with the slice topos, the left adjoint of the inverse image of the
localization morphism is the forgetful functor from `Sh(C)/F`.

This is the adjunction of Stacks 0791 for the same equivalence as
`localizationEquivalence_fibers`, which is what pins the comparisons built from it down. -/
@[stacks 04IE "part (3): lower shriek on sets", sga "4 III 5.5" "Clause 3"]
noncomputable def localizationShriekAdjunction :
    (localizationEquivalence X F).functor ⋙ Over.forget F ⊣
      (localizationMorphism X F).toToposHom.inverseImage :=
  F.property.sheafEquivalenceCostructuredArrowYoneda.shriek

/-- `localizationShriekAdjunction` in existence form. -/
theorem localization_shriek :
    Nonempty ((localizationEquivalence X F).functor ⋙ Over.forget F ⊣
      (localizationMorphism X F).toToposHom.inverseImage) :=
  ⟨CategoryTheory.Stacks.Topos.Localized.shriekAdjunction F.obj X.J F.property⟩

/-- **The inverse image of the localization is product with `F`**: read through the
equivalence with the slice topos, the inverse image of the localization morphism is
`toOver F`, which sends a sheaf `G` to the product `G × F` viewed as an object over `F`. -/
@[stacks 04IE "part (1): inverse image", sga "4 IV 5.2"]
noncomputable def localizationInverseImageIso :
    (localizationMorphism X F).toToposHom.inverseImage ⋙
      (localizationEquivalence X F).functor ≅ toOver F :=
  Adjunction.rightAdjointUniq
    (CategoryTheory.Stacks.Topos.Localized.forgetAdjunction F.obj X.J F.property)
    (forgetAdjToOver F)

/-- **The comparison of the inverse image with `toOver F` is the one the lower shriek
prescribes**: the component of `localizationInverseImageIso` at a sheaf `G`, followed by the
projection `G × F ⟶ G`, is the counit of the lower shriek adjunction at `G`.

This is what `localizationInverseImageIso` means, and it is a statement only because the
equivalence and the adjunction come from one package: for an unrelated adjunction the two sides
are morphisms that nothing relates. With `localizationInverseImageIso_eq` it pins the comparison
down completely. -/
@[stacks 04IE "part (1): the comparison is the one the lower shriek prescribes"]
theorem forget_localizationInverseImageIso_hom_app (G : X.Topos) :
    (Over.forget F).map ((localizationInverseImageIso X F).hom.app G) ≫
        (forgetAdjToOver F).counit.app G =
      (localizationShriekAdjunction X F).counit.app G := by
  refine Eq.trans (Adjunction.rightAdjointUniq_hom_app_counit
    (Stacks.Topos.Localized.forgetAdjunction F.obj X.J F.property) (forgetAdjToOver F) G) ?_
  show (Stacks.Topos.Localized.forgetAdjunction F.obj X.J F.property).counit.app G =
      (Over.forget F).map ((localizationEquivalence X F).functor.map
          ((localizationEquivalence X F).unit.app
            ((localizationMorphism X F).toToposHom.inverseImage.obj G))) ≫
        (Over.forget F).map ((localizationEquivalence X F).counit.app
            ((localizationEquivalence X F).functor.obj
              ((localizationMorphism X F).toToposHom.inverseImage.obj G))) ≫
          (Stacks.Topos.Localized.forgetAdjunction F.obj X.J F.property).counit.app G
  exact (congrArg (fun z => (Over.forget F).map z ≫
        (Stacks.Topos.Localized.forgetAdjunction F.obj X.J F.property).counit.app G)
      ((localizationEquivalence X F).functor_unit_comp
        ((localizationMorphism X F).toToposHom.inverseImage.obj G))).symm.trans
    (Functor.map_comp_assoc (Over.forget F) _ _ _)

/-- **The comparison of the inverse image with `toOver F` is unique**: an isomorphism of
`j⁻¹ ⋙ E.functor` with `toOver F` whose components are, after the projection `G × F ⟶ G`, the
counit of the lower shriek adjunction is `localizationInverseImageIso`.

A morphism into `toOver F` over `F` is determined by its composite with that projection, its
composite with the other one being its structure morphism — which is
`CategoryTheory.Iso.ext_of_left_comp_forgetAdjToOver_counit`. Together with
`forget_localizationInverseImageIso_hom_app` this is what makes the comparison of a relocalization
with base change computable: it is enough to exhibit one isomorphism with the right counits. -/
@[stacks 04IE "part (1): the comparison is unique"]
theorem localizationInverseImageIso_eq
    (Ψ : (localizationMorphism X F).toToposHom.inverseImage ⋙
      (localizationEquivalence X F).functor ≅ toOver F)
    (h : ∀ G : X.Topos, (Over.forget F).map (Ψ.hom.app G) ≫ (forgetAdjToOver F).counit.app G =
      (localizationShriekAdjunction X F).counit.app G) :
    Ψ = localizationInverseImageIso X F :=
  Iso.ext_of_left_comp_forgetAdjToOver_counit fun G ↦
    (h G).trans (forget_localizationInverseImageIso_hom_app X F G).symm

/-! ### Transposing a morphism out of a slice object onto its fibre sheaf -/

/-- **The fibre transpose of a morphism out of a slice object.** For an object `T` of `Sh(C)/F`
and a morphism `β : T.left ⟶ G` of sheaves of sets on `C`, this is `β` read as a morphism
`j_! (E⁻¹T) ⟶ G` — which is what precomposing with the counit of the equivalence does — and then
transposed across the lower shriek adjunction, giving a morphism from `E⁻¹T` to `j⁻¹G`.

Since `E⁻¹T` is the fibre sheaf of `T`, this is the only computable description of `β`: the
underlying sheaf `T.left` of an object in the image of `E` has none, while
`CategoryTheory.Presheaf.IsSheaf.app_fibers_inv_comp_homEquiv_shriek` evaluates the transpose on
fibre sections as `β` itself. -/
noncomputable def fibreTranspose (T : Over F) (G : X.Topos) (β : T.left ⟶ G) :
    (localizationEquivalence X F).inverse.obj T ⟶
      (X.localizationMorphism F).toToposHom.inverseImage.obj G :=
  (X.localizationShriekAdjunction F).homEquiv ((localizationEquivalence X F).inverse.obj T) G
    ((Over.forget F).map ((localizationEquivalence X F).counit.app T) ≫ β)

/-- **The fibre transpose, on sections.** Read on the fibre presheaf of `T` by the fibre
description of the equivalence, the transpose of `β` sends a section `t` of `T.left` over `U`
lying in the fibre of `T` over `s ∈ F(U)` to `β(t)`.

This is Stacks 0791's `app_fibers_inv_comp_homEquiv_shriek` for `fibreTranspose`, and it is the
only way to evaluate a morphism out of `T.left` when `T` is in the image of the equivalence. -/
theorem app_fibreTranspose (T : Over F) (G : X.Topos) (β : T.left ⟶ G)
    (Z : CostructuredArrow yoneda F.obj) (p : OverArrows T.hom.hom Z.hom) :
    ((localizationEquivalence_fibers X F).inv.app T ≫
        (fibreTranspose X F T G β).hom).app (op Z) p =
      β.hom.app (op Z.left) p.val :=
  F.property.app_fibers_inv_comp_homEquiv_shriek T G β Z p

/-- **The lower shriek counit recovers a section from its fibre coordinate.** A section `w` of
`j⁻¹G` over an element `(U, s)` of `F` is, by the unit of the equivalence and the fibre
description of its inverse, a section of `j_!j⁻¹G` over `U` lying in the fibre over `s`; the
counit of `j_! ⊣ j⁻¹` sends that section back to `w`.

This is `app_fibers_inv_comp_unitInv` read in the other direction, which is legitimate because
the fibre identification and the unit are isomorphisms. It is how a fibre coordinate produced by
the equivalence at one sheaf is compared with a section of `G`. -/
theorem counit_app_val_app_fibers_hom_unit (G : X.Topos) (Y : CostructuredArrow yoneda F.obj)
    (w : ((X.localizationMorphism F).toToposHom.inverseImage.obj G).obj.obj (op Y)) :
    ((X.localizationShriekAdjunction F).counit.app G).hom.app (op Y.left)
        (((localizationEquivalence_fibers X F).hom.app
              ((localizationEquivalence X F).functor.obj
                ((X.localizationMorphism F).toToposHom.inverseImage.obj G))).app (op Y)
            (((localizationEquivalence X F).unit.app
              ((X.localizationMorphism F).toToposHom.inverseImage.obj G)).hom.app (op Y) w)).val =
      w := by
  have e1 : ∀ v, ((localizationEquivalence_fibers X F).inv.app
          ((localizationEquivalence X F).functor.obj
            ((X.localizationMorphism F).toToposHom.inverseImage.obj G))).app (op Y)
        (((localizationEquivalence_fibers X F).hom.app
          ((localizationEquivalence X F).functor.obj
            ((X.localizationMorphism F).toToposHom.inverseImage.obj G))).app (op Y) v) = v :=
    fun v => Iso.hom_inv_id_apply (((localizationEquivalence_fibers X F).app
      ((localizationEquivalence X F).functor.obj
        ((X.localizationMorphism F).toToposHom.inverseImage.obj G))).app (op Y)) v
  have e2 : ∀ v, ((localizationEquivalence X F).unitInv.app
          ((X.localizationMorphism F).toToposHom.inverseImage.obj G)).hom.app (op Y)
        (((localizationEquivalence X F).unit.app
          ((X.localizationMorphism F).toToposHom.inverseImage.obj G)).hom.app (op Y) v) = v :=
    fun v => Iso.hom_inv_id_apply
      ((sheafToPresheaf (elementTopology X F) (Type v) ⋙
        (CategoryTheory.evaluation (elementSite X F)ᵒᵖ (Type v)).obj (op Y)).mapIso
          ((localizationEquivalence X F).unitIso.app
            ((X.localizationMorphism F).toToposHom.inverseImage.obj G))) v
  refine (F.property.app_fibers_inv_comp_unitInv G Y _).symm.trans ?_
  show ((localizationEquivalence X F).unitInv.app
        ((X.localizationMorphism F).toToposHom.inverseImage.obj G)).hom.app (op Y)
      (((localizationEquivalence_fibers X F).inv.app
            ((localizationEquivalence X F).functor.obj
              ((X.localizationMorphism F).toToposHom.inverseImage.obj G))).app (op Y)
        ((((localizationEquivalence_fibers X F).hom.app
              ((localizationEquivalence X F).functor.obj
                ((X.localizationMorphism F).toToposHom.inverseImage.obj G))).app (op Y))
          (((localizationEquivalence X F).unit.app
            ((X.localizationMorphism F).toToposHom.inverseImage.obj G)).hom.app (op Y) w))) = w
  exact (congrArg (fun v => ((localizationEquivalence X F).unitInv.app
      ((X.localizationMorphism F).toToposHom.inverseImage.obj G)).hom.app (op Y) v)
    (e1 _)).trans (e2 w)

/-- **A morphism out of a slice object is determined by its fibre transpose.** Transposition is a
bijection composed with precomposition by an isomorphism. -/
theorem fibreTranspose_injective (T : Over F) (G : X.Topos) {β β' : T.left ⟶ G}
    (h : fibreTranspose X F T G β = fibreTranspose X F T G β') : β = β' :=
  (cancel_epi ((Over.forget F).map ((localizationEquivalence X F).counitIso.app T).hom)).1
    (((X.localizationShriekAdjunction F).homEquiv _ G).injective h)

/-- **The fibre transpose is natural in the slice object.** Precomposing `β` with a morphism
`w : T ⟶ T'` of `Sh(C)/F` transposes to precomposition with the fibre sheaf of `w`. -/
theorem fibreTranspose_forget_map_comp {T T' : Over F} (G : X.Topos) (w : T ⟶ T')
    (β : T'.left ⟶ G) :
    fibreTranspose X F T G ((Over.forget F).map w ≫ β) =
      (localizationEquivalence X F).inverse.map w ≫ fibreTranspose X F T' G β :=
  (congrArg ((X.localizationShriekAdjunction F).homEquiv _ G)
    (show (Over.forget F).map ((localizationEquivalence X F).counit.app T) ≫
          (Over.forget F).map w ≫ β =
        (Over.forget F).map ((localizationEquivalence X F).functor.map
              ((localizationEquivalence X F).inverse.map w)) ≫
          ((Over.forget F).map ((localizationEquivalence X F).counit.app T') ≫ β) from by
      rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
      exact congrArg (fun z => (Over.forget F).map z ≫ β)
        ((localizationEquivalence X F).counit_naturality w).symm)).trans
    (Adjunction.homEquiv_naturality_left _ _ _)

/-- **The fibre transpose of the lower shriek counit is the unit of the equivalence.** Both
morphisms `E⁻¹(E(j⁻¹G)) ⟶ j⁻¹G` agree on fibre sections, by
`CategoryTheory.Presheaf.IsSheaf.app_fibers_inv_comp_homEquiv_shriek` and by
`CategoryTheory.Presheaf.IsSheaf.app_fibers_inv_comp_unitInv`; the fibre identification is an
isomorphism, so they are equal.

This is the functor-level form of Stacks 0791's bridge between the fibre description of the
equivalence and the counit of `j_!`, and it is what lets a comparison built from fibres be
compared with the counit. -/
@[stacks 04IE "part (1): the fibre transpose of the lower shriek counit"]
theorem fibreTranspose_shriek_counit (G : X.Topos) :
    fibreTranspose X F ((localizationEquivalence X F).functor.obj
          ((X.localizationMorphism F).toToposHom.inverseImage.obj G)) G
        ((X.localizationShriekAdjunction F).counit.app G) =
      (localizationEquivalence X F).unitInv.app
        ((X.localizationMorphism F).toToposHom.inverseImage.obj G) := by
  refine Sheaf.homEquiv.injective ?_
  refine (cancel_epi (((localizationEquivalence_fibers X F).app
    ((localizationEquivalence X F).functor.obj
      ((X.localizationMorphism F).toToposHom.inverseImage.obj G))).inv)).1 ?_
  ext Z p
  obtain ⟨Z⟩ := Z
  exact (F.property.app_fibers_inv_comp_homEquiv_shriek _ G
      ((X.localizationShriekAdjunction F).counit.app G) Z p).trans
    (F.property.app_fibers_inv_comp_unitInv G Z p).symm

end AlgebraicGeometry.RingedTopos

end
