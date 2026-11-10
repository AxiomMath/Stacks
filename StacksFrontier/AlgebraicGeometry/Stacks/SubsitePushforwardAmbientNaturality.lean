module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardAmbientUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardFormulaNaturality

/-!
# The pushforward identity of Stacks 07AT at its canonical map

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over a base with `𝒴` fibred in groupoids, let
`𝒳' ⊆ 𝒳` and `𝒴' ⊆ 𝒴` be full subcategories with `f` carrying `𝒳'` into `𝒴'`, and let
`f' : 𝒳' ⥤ 𝒴'` be the restriction. Writing `g`, `g'` for the two inclusions, the second
assertion of **Stacks 07AT** is that the canonical map `g^{-1}f_* ⟶ f'_*(g')^{-1}` of
Sites, Section 06UM is an isomorphism.

That canonical map is the base-change transformation of the square of `f`, `f'`, `g` and `g'`,
which commutes on the nose. This file constructs it and proves it bijective at every object of
`𝒴'`, under the local-factorization conditions of **Stacks 07AK** that
`StacksFrontier/AlgebraicGeometry/Stacks/SubsitePushforwardAmbientUnconditional.lean` discharges
for the lisse-étale and flat-fppf sites of an algebraic stack.

## Main definitions

* `CategoryTheory.SubsitePushforward.subsiteRanSquare`: the 2-square of the two inclusions, the
  1-morphism and its restriction.
* `CategoryTheory.SubsitePushforward.subsiteRanBaseChange`: the canonical map
  `g^{-1}f_* ⟶ f'_*(g')^{-1}` on presheaves of sets.
* `CategoryTheory.SubsitePushforward.subsiteSheafBaseChange`: the same on sheaves of sets.
* `CategoryTheory.SubsitePushforward.primedObjOfHom`: the object of the primed 2-fibre product
  attached to an arrow `f x' ⟶ y` out of the subsite.

## Main results

* `CategoryTheory.SubsitePushforward.subsiteRanBaseChange_counit`: the canonical map is
  characterized by the counits of the two right Kan extensions.
* `CategoryTheory.SubsitePushforward.primedPushforwardAmbientEquiv_counit`: the objectwise
  bijection of **Stacks 07AT** has that same characterization.
* `CategoryTheory.SubsitePushforward.ran_ext_of_primed`: a section of `f_*ℱ` over an object of
  `𝒴'` is determined by its restrictions along the arrows out of `𝒳'`.
* `CategoryTheory.SubsitePushforward.bijective_subsiteRanBaseChange_app_app`: the canonical map
  is bijective at each object of `𝒴'`.
* `CategoryTheory.SubsitePushforward.isIso_subsiteSheafBaseChange`: it is therefore an
  isomorphism of functors on sheaves of sets.
* `CategoryTheory.SubsitePushforward.ranObjEquiv_naturality_right`: the comparison of the two
  right Kan extensions is natural in the object of `𝒴'`.

## Implementation notes

Proving the *canonical* map invertible, rather than exhibiting the objectwise bijection as a
natural transformation, is what makes naturality in the object of `𝒴'` free: the canonical map
is a natural transformation of functors to begin with. The objectwise bijection enters only
through `primedPushforwardAmbientEquiv_counit`, as the source of a preimage.

The two counit characterizations are read off at the object of the 2-fibre product that an arrow
`f x' ⟶ y` determines, which is `CategoryTheory.Presheaf.pushforwardIndexInverseObj` of the
corresponding costructured arrow; its comparison arrow is that arrow back again.

The four continuity and cocontinuity facts that the sheaf-level statement needs are explicit
arguments rather than instances: at the sites of an algebraic stack they are theorems whose
subjects are the composites `f' ⋙ g` and `g' ⋙ f`, which instance search does not see through.

The coefficient universe is a parameter, instantiated at `Type (u + 1)` for an algebraic stack
in `StacksFrontier/AlgebraicGeometry/Stacks/SubsiteSheafPushforwardBaseChange.lean`.

## References

* [Stacks Project, Tag 06UM](https://stacks.math.columbia.edu/tag/06UM)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 07AU](https://stacks.math.columbia.edu/tag/07AU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SubsitePushforward

attribute [local implicit_reducible] Functor.Fiber ambientProjection primedProjection

universe u₁ u₂ u₃ v₁ v₂ v₃ w

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

section Index

variable (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
  (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))
  (ℋ : (P.FullSubcategory)ᵒᵖ ⥤ Type w)
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
    (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w, (P.ι ⋙ f).op.HasPointwiseRightKanExtension G]

/-- The comparison of the two right Kan extensions is natural in the object of the subsite
of `𝒴`. -/
theorem ranObjEquiv_naturality_right {y₁ y₂ : Q.FullSubcategory} (b : y₁ ⟶ y₂)
    (s : ((subsiteFunctor f P hPQ).op.ran.obj ℋ).obj (op y₂)) :
    ranObjEquiv f P hPQ y₁ ℋ (((subsiteFunctor f P hPQ).op.ran.obj ℋ).map b.op s) =
      ((P.ι ⋙ f).op.ran.obj ℋ).map (Q.ι.map b).op (ranObjEquiv f P hPQ y₂ ℋ s) := by
  refine ranObjObj_ext (P.ι ⋙ f) ℋ fun x a => ?_
  rw [ranObjEquiv_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp, ranObjEquiv_apply]
  rfl

end Index

/-! ### The canonical base-change transformation -/

section BaseChange

variable (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
  (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))

/-- The square of the two inclusions, the 1-morphism and its restriction, as a 2-square of the
opposite categories. It commutes on the nose, so its 2-morphism is the identity. -/
def subsiteRanSquare :
    TwoSquare (subsiteFunctor f P hPQ).op P.ι.op Q.ι.op f.op :=
  TwoSquare.mk _ _ _ _ (𝟙 _)

/-- Each component of the 2-morphism of `subsiteRanSquare` is the identity. -/
@[simp]
theorem subsiteRanSquare_natTrans_app (x : (P.FullSubcategory)ᵒᵖ) :
    (subsiteRanSquare f P hPQ).app x = 𝟙 _ :=
  rfl

variable [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
    (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
  [∀ G : 𝒳ᵒᵖ ⥤ Type w, f.op.HasPointwiseRightKanExtension G]

/-- **The canonical map `g^{-1}f_* ⟶ f'_*(g')^{-1}` on presheaves of sets.** For a 1-morphism
`f : 𝒳 ⥤ 𝒴` carrying a full subcategory `𝒳'` of `𝒳` into a full subcategory `𝒴'` of `𝒴`, this
is the base-change transformation of the commuting square of `f`, its restriction `f'` and the
two inclusions: restriction along the inclusion of `𝒴'` of the pushforward along `f` maps to the
pushforward along `f'` of the restriction along the inclusion of `𝒳'`.

This is the canonical map of Sites, Section 06UM, whose invertibility is the second assertion of
**Stacks 07AT**. -/
abbrev subsiteRanBaseChange :
    f.op.ran ⋙ (Functor.whiskeringLeft (Q.FullSubcategory)ᵒᵖ 𝒴ᵒᵖ (Type w)).obj Q.ι.op ⟶
      (Functor.whiskeringLeft (P.FullSubcategory)ᵒᵖ 𝒳ᵒᵖ (Type w)).obj P.ι.op ⋙
        (subsiteFunctor f P hPQ).op.ran :=
  (subsiteRanSquare f P hPQ).ranBaseChange

/-- **The canonical map is characterized by the counits.** The restriction, along an arrow
`f' x' ⟶ y` of the subsite of `𝒴`, of the image of a section of `f_*ℱ` over `y`, read through
the counit of the pushforward along `f'`, is the restriction of that section along the same arrow
read in `𝒴`, through the counit of the pushforward along `f`. -/
theorem subsiteRanBaseChange_counit (ℱ : 𝒳ᵒᵖ ⥤ Type w) (y : Q.FullSubcategory)
    (t : (f.op.ran.obj ℱ).obj (op y.obj)) (x : P.FullSubcategory)
    (a : (subsiteFunctor f P hPQ).obj x ⟶ y) :
    ((subsiteFunctor f P hPQ).op.ranCounit.app (P.ι.op ⋙ ℱ)).app (op x)
        (((subsiteFunctor f P hPQ).op.ran.obj (P.ι.op ⋙ ℱ)).map a.op
          (((subsiteRanBaseChange f P hPQ).app ℱ).app (op y) t)) =
      (f.op.ranCounit.app ℱ).app (op x.obj)
        ((f.op.ran.obj ℱ).map (Q.ι.map a).op t) := by
  have key : ((subsiteFunctor f P hPQ).op.ran.obj (P.ι.op ⋙ ℱ)).map a.op
        (((subsiteRanBaseChange f P hPQ).app ℱ).app (op y) t) =
      ((subsiteRanBaseChange f P hPQ).app ℱ).app (op ((subsiteFunctor f P hPQ).obj x))
        ((f.op.ran.obj ℱ).map (Q.ι.map a).op t) :=
    (congrArg (fun g : (f.op.ran.obj ℱ).obj (op y.obj) ⟶
        ((subsiteFunctor f P hPQ).op.ran.obj (P.ι.op ⋙ ℱ)).obj
          (op ((subsiteFunctor f P hPQ).obj x)) => g t)
      (((subsiteRanBaseChange f P hPQ).app ℱ).naturality a.op)).symm
  have hfac : ((subsiteFunctor f P hPQ).op.ranCounit.app (P.ι.op ⋙ ℱ)).app (op x)
        (((subsiteRanBaseChange f P hPQ).app ℱ).app (op ((subsiteFunctor f P hPQ).obj x))
          ((f.op.ran.obj ℱ).map (Q.ι.map a).op t)) =
      (f.op.ranCounit.app ℱ).app (op x.obj)
        ((f.op.ran.obj ℱ).map (Q.ι.map a).op t) := by
    have h := congrArg (fun g : (f.op.ran.obj ℱ).obj
        (op ((subsiteFunctor f P hPQ).obj x).obj) ⟶ ℱ.obj (op x.obj) => g
          ((f.op.ran.obj ℱ).map (Q.ι.map a).op t))
      (Stacks.SheafOfModules.ranBaseChange_fac (subsiteRanSquare f P hPQ) ℱ (op x))
    refine h.trans (congrArg (fun u => (f.op.ranCounit.app ℱ).app (op x.obj) u) ?_)
    rw [subsiteRanSquare_natTrans_app]
    exact Functor.map_id_apply (f.op.ran.obj ℱ) _ _
  rw [key, hfac]

end BaseChange

/-! ### The identity at one object of the subsite -/

section Ambient

variable (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳)
  (c : p𝒴.ChoiceOfPullbacks) {Q : ObjectProperty 𝒴}
  (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj)) (h𝒴 : p𝒴.IsFiberedInGroupoids)
  (hf : f ⋙ p𝒴 = p𝒳) (y : Q.FullSubcategory) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
  (J : GrothendieckTopology (ambientTwoFibreProduct p𝒳 p𝒴 f c y))
  (hℱ : Presieve.IsSheaf J ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ))
  (hfac : Stacks.Sites.HasLocalFactorizations J (primedProperty p𝒳 p𝒴 f P c y).ι)
  (hconn : Stacks.Sites.HasLocallyConnectedFactorizations J
    (primedProperty p𝒳 p𝒴 f P c y).ι)

/-- The extension of a compatible family from the primed 2-fibre product to the whole 2-fibre
product restricts back to the family it came from. -/
theorem primedSectionsAmbientEquiv_val
    (σ : Presheaf.globalSections ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ (P.ι.op ⋙ ℱ)))
    (T : primedTwoFibreProduct p𝒳 p𝒴 f P c y) :
    ((Presheaf.globalSectionsEquivSections ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ))
        (primedSectionsAmbientEquiv p𝒳 p𝒴 f P c y ℱ J hℱ hfac hconn σ)).1
          (op ((primedProperty p𝒳 p𝒴 f P c y).ι.obj T)) =
      ((Presheaf.globalSectionsEquivSections
        ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ (P.ι.op ⋙ ℱ))) σ).1 (op T) := by
  have h := (Stacks.Sites.sectionsEquivOfHasLocallyConnectedFactorizations J hℱ hfac
      hconn).apply_symm_apply
    ((Presheaf.globalSectionsEquivSections
      ((primedProjection p𝒳 p𝒴 f P c y).op ⋙ (P.ι.op ⋙ ℱ))) σ)
  have h' := congrArg (fun t : (((primedProperty p𝒳 p𝒴 f P c y).ι.op ⋙
    ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ))).sections => Subtype.val t (op T)) h
  simp only [primedSectionsAmbientEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact h'

include h𝒴 hf hℱ hfac hconn in
/-- **An element of `f_*ℱ` at an object of the subsite of `𝒴` is determined by its restrictions
along the arrows out of the subsite of `𝒳`.** Under the local-factorization conditions of
Stacks 07AK, two sections of the pushforward over `y` which have the same restriction, read
through the counit of the right Kan extension, along every arrow `f x' ⟶ y` with `x'` in the
subsite, are equal. -/
theorem ran_ext_of_primed
    [∀ G : 𝒳ᵒᵖ ⥤ Type w, f.op.HasPointwiseRightKanExtension G]
    {t t' : (f.op.ran.obj ℱ).obj (op y.obj)}
    (h : ∀ (x : P.FullSubcategory) (a : f.obj x.obj ⟶ y.obj),
      (f.op.ranCounit.app ℱ).app (op x.obj) ((f.op.ran.obj ℱ).map a.op t) =
        (f.op.ranCounit.app ℱ).app (op x.obj) ((f.op.ran.obj ℱ).map a.op t')) :
    t = t' := by
  apply (Presheaf.pushforwardSectionsEquiv p𝒳 p𝒴 f h𝒴 hf c ⟨y.obj, rfl⟩ ℱ).injective
  apply (Presheaf.globalSectionsEquivSections
    ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ)).injective
  apply (Stacks.Sites.sectionsEquivOfHasLocallyConnectedFactorizations J hℱ hfac hconn).injective
  refine Functor.sections_ext_iff.mpr fun T => ?_
  have et := Presheaf.pushforwardSectionsEquiv_apply p𝒳 p𝒴 f h𝒴 hf c ⟨y.obj, rfl⟩ ℱ t
    ((primedProperty p𝒳 p𝒴 f P c y).ι.obj T.unop)
  have et' := Presheaf.pushforwardSectionsEquiv_apply p𝒳 p𝒴 f h𝒴 hf c ⟨y.obj, rfl⟩ ℱ t'
    ((primedProperty p𝒳 p𝒴 f P c y).ι.obj T.unop)
  exact et.trans ((h ⟨T.unop.obj.y, T.unop.property⟩ _).trans et'.symm)

include h𝒴 hf in
/-- The object of the primed 2-fibre product attached to an arrow `f x' ⟶ y` out of the
subsite: its slice component is the image of the arrow in the base, and its `𝒳`-component is
`x'`. -/
def primedObjOfHom (x : P.FullSubcategory) (a : f.obj x.obj ⟶ y.obj) :
    primedTwoFibreProduct p𝒳 p𝒴 f P c y :=
  ⟨Presheaf.pushforwardIndexInverseObj p𝒳 p𝒴 f (c.sliceDatum y.obj) h𝒴 hf
    (CostructuredArrow.mk a), x.property⟩

include h𝒴 hf in
/-- The comparison arrow of `CategoryTheory.SubsitePushforward.primedObjOfHom` is the arrow it
was built from. -/
theorem primedObjOfHom_comparison (x : P.FullSubcategory) (a : f.obj x.obj ⟶ y.obj) :
    ((primedProperty p𝒳 p𝒴 f P c y).ι.obj (primedObjOfHom p𝒳 p𝒴 f P c h𝒴 hf y x a)).iso.inv ≫
        c.map ((primedProperty p𝒳 p𝒴 f P c y).ι.obj
          (primedObjOfHom p𝒳 p𝒴 f P c h𝒴 hf y x a)).x.hom ⟨y.obj, rfl⟩ = a :=
  Presheaf.pushforwardIndexInverseObj_iso_inv_comp_cone p𝒳 p𝒴 f (c.sliceDatum y.obj) h𝒴 hf
    (CostructuredArrow.mk a)

include hℱ hfac hconn in
/-- **The identity of Stacks 07AT at one object of the subsite is characterized by the
counits.** The restriction of the section of `f_*ℱ` over `y` corresponding to a section `s` of
`f'_*(g')^{-1}ℱ`, along an arrow `f x' ⟶ y` out of the subsite and read through the counit of the
pushforward along `f`, is the restriction of `s` along the same arrow read in the subsite of `𝒴`,
through the counit of the pushforward along `f'`. -/
theorem primedPushforwardAmbientEquiv_counit
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
      (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w, (P.ι ⋙ f).op.HasPointwiseRightKanExtension G]
    [∀ G : 𝒳ᵒᵖ ⥤ Type w, f.op.HasPointwiseRightKanExtension G]
    (s : ((subsiteFunctor f P hPQ).op.ran.obj (P.ι.op ⋙ ℱ)).obj (op y))
    (x : P.FullSubcategory) (a : f.obj x.obj ⟶ y.obj) :
    (f.op.ranCounit.app ℱ).app (op x.obj)
        ((f.op.ran.obj ℱ).map a.op
          (primedPushforwardAmbientEquiv p𝒳 p𝒴 f P c hPQ h𝒴 hf y ℱ J hℱ hfac hconn s)) =
      ((subsiteFunctor f P hPQ).op.ranCounit.app (P.ι.op ⋙ ℱ)).app (op x)
        (((subsiteFunctor f P hPQ).op.ran.obj (P.ι.op ⋙ ℱ)).map
          (ObjectProperty.homMk (P := Q) a).op s) := by
  have hcmp := primedObjOfHom_comparison p𝒳 p𝒴 f P c h𝒴 hf y x a
  have hcmp' : (primedObjOfHom p𝒳 p𝒴 f P c h𝒴 hf y x a).obj.iso.inv ≫
      c.map (primedObjOfHom p𝒳 p𝒴 f P c h𝒴 hf y x a).obj.x.hom ⟨y.obj, rfl⟩ = a := hcmp
  have e1 := Presheaf.pushforwardSectionsEquiv_apply p𝒳 p𝒴 f h𝒴 hf c ⟨y.obj, rfl⟩ ℱ
    (primedPushforwardAmbientEquiv p𝒳 p𝒴 f P c hPQ h𝒴 hf y ℱ J hℱ hfac hconn s)
    ((primedProperty p𝒳 p𝒴 f P c y).ι.obj (primedObjOfHom p𝒳 p𝒴 f P c h𝒴 hf y x a))
  rw [hcmp] at e1
  have e3 := subsitePushforwardSectionsEquiv_apply p𝒳 p𝒴 f P hPQ h𝒴 hf c y (P.ι.op ⋙ ℱ) s
    (primedObjOfHom p𝒳 p𝒴 f P c h𝒴 hf y x a)
  have hC : Presheaf.pushforwardSectionsEquiv p𝒳 p𝒴 f h𝒴 hf c ⟨y.obj, rfl⟩ ℱ
        (primedPushforwardAmbientEquiv p𝒳 p𝒴 f P c hPQ h𝒴 hf y ℱ J hℱ hfac hconn s) =
      primedSectionsAmbientEquiv p𝒳 p𝒴 f P c y ℱ J hℱ hfac hconn
        (subsitePushforwardSectionsEquiv p𝒳 p𝒴 f P hPQ h𝒴 hf c y (P.ι.op ⋙ ℱ) s) := by
    simp only [primedPushforwardAmbientEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  have e2 := primedSectionsAmbientEquiv_val p𝒳 p𝒴 f P c y ℱ J hℱ hfac hconn
    (subsitePushforwardSectionsEquiv p𝒳 p𝒴 f P hPQ h𝒴 hf c y (P.ι.op ⋙ ℱ) s)
    (primedObjOfHom p𝒳 p𝒴 f P c h𝒴 hf y x a)
  refine e1.symm.trans (((hC ▸ e2).trans e3).trans ?_)
  exact congrArg (fun b : f.obj x.obj ⟶ y.obj =>
    ((subsiteFunctor f P hPQ).op.ranCounit.app (P.ι.op ⋙ ℱ)).app (op x)
      (((subsiteFunctor f P hPQ).op.ran.obj (P.ι.op ⋙ ℱ)).map
        (ObjectProperty.homMk (P := Q) b).op s)) hcmp'

include h𝒴 hf hℱ hfac hconn in
/-- **Stacks 07AT, second assertion, at one object of the subsite of `𝒴`.** The canonical map
`g^{-1}f_*ℱ ⟶ f'_*(g')^{-1}ℱ` is bijective at `y`: it is injective because a section of `f_*ℱ`
over `y` is determined by its restrictions out of the subsite, and surjective because the
objectwise identification of Stacks 07AT provides a preimage. -/
theorem bijective_subsiteRanBaseChange_app_app
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
      (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
    [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w, (P.ι ⋙ f).op.HasPointwiseRightKanExtension G]
    [∀ G : 𝒳ᵒᵖ ⥤ Type w, f.op.HasPointwiseRightKanExtension G] :
    Function.Bijective (((subsiteRanBaseChange f P hPQ).app ℱ).app (op y)) := by
  refine ⟨fun {t t'} hbc => ?_, fun s => ?_⟩
  · refine ran_ext_of_primed p𝒳 p𝒴 f P c h𝒴 hf y ℱ J hℱ hfac hconn fun x a => ?_
    exact (subsiteRanBaseChange_counit f P hPQ ℱ y t x
      (ObjectProperty.homMk (P := Q) a)).symm.trans <| (congrArg (fun u =>
      ((subsiteFunctor f P hPQ).op.ranCounit.app (P.ι.op ⋙ ℱ)).app (op x)
        (((subsiteFunctor f P hPQ).op.ran.obj (P.ι.op ⋙ ℱ)).map
          (ObjectProperty.homMk (P := Q) a).op u)) hbc).trans
      (subsiteRanBaseChange_counit f P hPQ ℱ y t' x (ObjectProperty.homMk (P := Q) a))
  · refine ⟨primedPushforwardAmbientEquiv p𝒳 p𝒴 f P c hPQ h𝒴 hf y ℱ J hℱ hfac hconn s,
      ranObjObj_ext (subsiteFunctor f P hPQ) (P.ι.op ⋙ ℱ) fun x a => ?_⟩
    exact (subsiteRanBaseChange_counit f P hPQ ℱ y _ x a).trans
      (primedPushforwardAmbientEquiv_counit p𝒳 p𝒴 f P c hPQ h𝒴 hf y ℱ J hℱ hfac hconn s x
        (Q.ι.map a))

end Ambient

/-! ### The identity as an isomorphism of functors on sheaves -/

section Sheaves

variable (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
  (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))
  (J𝒳 : GrothendieckTopology 𝒳) (J𝒴 : GrothendieckTopology 𝒴)
  (J𝒳' : GrothendieckTopology P.FullSubcategory) (J𝒴' : GrothendieckTopology Q.FullSubcategory)
  (hfcc : f.IsCocontinuous J𝒳 J𝒴)
  (hf'cc : (subsiteFunctor f P hPQ).IsCocontinuous J𝒳' J𝒴')
  (hX : P.ι.IsContinuous J𝒳' J𝒳) (hY : Q.ι.IsContinuous J𝒴' J𝒴)
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
    (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
  [∀ G : 𝒳ᵒᵖ ⥤ Type w, f.op.HasPointwiseRightKanExtension G]

/-- **The canonical map `g^{-1}f_* ⟶ f'_*(g')^{-1}` on sheaves of sets**, the one of
`CategoryTheory.SubsitePushforward.subsiteRanBaseChange` read on sheaves: the direct images
along `f` and `f'` are the right Kan extensions of the underlying presheaves, and the inverse
images along the two inclusions are restriction, so the two composites have the two presheaves
of that transformation as their underlying presheaves. -/
def subsiteSheafBaseChange :
    letI := hfcc
    letI := hf'cc
    letI := hX
    letI := hY
    f.sheafPushforwardCocontinuous (Type w) J𝒳 J𝒴 ⋙
        Q.ι.sheafPushforwardContinuous (Type w) J𝒴' J𝒴 ⟶
      P.ι.sheafPushforwardContinuous (Type w) J𝒳' J𝒳 ⋙
        (subsiteFunctor f P hPQ).sheafPushforwardCocontinuous (Type w) J𝒳' J𝒴' :=
  letI := hfcc
  letI := hf'cc
  letI := hX
  letI := hY
  { app := fun G => ObjectProperty.homMk ((subsiteRanBaseChange f P hPQ).app G.obj)
    naturality := fun _ _ φ => by
      apply ObjectProperty.hom_ext
      exact (subsiteRanBaseChange f P hPQ).naturality φ.hom }

/-- **Stacks 07AT, second assertion.** If the canonical map of presheaves is bijective at every
object of the subsite of `𝒴` and every sheaf, then `g^{-1}f_* ⟶ f'_*(g')^{-1}` is an
isomorphism of functors on sheaves of sets, that is, `f'_*(g')^{-1} = g^{-1}f_*`. -/
theorem isIso_subsiteSheafBaseChange
    (H : ∀ (G : Sheaf J𝒳 (Type w)) (y : Q.FullSubcategory),
      Function.Bijective (((subsiteRanBaseChange f P hPQ).app G.obj).app (op y))) :
    letI := hfcc
    letI := hf'cc
    letI := hX
    letI := hY
    IsIso (subsiteSheafBaseChange f P hPQ J𝒳 J𝒴 J𝒳' J𝒴' hfcc hf'cc hX hY) := by
  let := hfcc
  let := hf'cc
  let := hX
  let := hY
  refine (NatTrans.isIso_iff_isIso_app _).2 fun G => ?_
  have h : IsIso ((subsiteRanBaseChange f P hPQ).app G.obj) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun z => (isIso_iff_bijective _).mpr (H G z.unop)
  have : IsIso ((sheafToPresheaf J𝒴' (Type w)).map
      ((subsiteSheafBaseChange f P hPQ J𝒳 J𝒴 J𝒳' J𝒴' hfcc hf'cc hX hY).app G)) := h
  exact isIso_of_reflects_iso _ (sheafToPresheaf J𝒴' (Type w))

end Sheaves

/-! ### The second identity, `g'_!(f')^{-1} = f^{-1}g_!` -/

section Shriek

variable (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
  (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))
  (J𝒳 : GrothendieckTopology 𝒳) (J𝒴 : GrothendieckTopology 𝒴)
  (J𝒳' : GrothendieckTopology P.FullSubcategory) (J𝒴' : GrothendieckTopology Q.FullSubcategory)
  (hfc : f.IsContinuous J𝒳 J𝒴) (hfcc : f.IsCocontinuous J𝒳 J𝒴)
  (hf'c : (subsiteFunctor f P hPQ).IsContinuous J𝒳' J𝒴')
  (hf'cc : (subsiteFunctor f P hPQ).IsCocontinuous J𝒳' J𝒴')
  (hX : P.ι.IsContinuous J𝒳' J𝒳) (hY : Q.ι.IsContinuous J𝒴' J𝒴)
  [∀ G : (P.FullSubcategory)ᵒᵖ ⥤ Type w,
    (subsiteFunctor f P hPQ).op.HasPointwiseRightKanExtension G]
  [∀ G : 𝒳ᵒᵖ ⥤ Type w, f.op.HasPointwiseRightKanExtension G]
  (Lg : Sheaf J𝒴' (Type w) ⥤ Sheaf J𝒴 (Type w))
  (Lg' : Sheaf J𝒳' (Type w) ⥤ Sheaf J𝒳 (Type w))

/-- **Stacks 07AT, the identity `g'_!(f')^{-1} = f^{-1}g_!`.** It follows formally from
`f'_*(g')^{-1} = g^{-1}f_*`: the two sides of that identity are the right adjoints of the two
sides of this one, by the adjointness of `f^{-1}` and `f_*`, of `g_!` and `g^{-1}`, and of their
primed versions, so conjugating the isomorphism along those four adjunctions gives this one. -/
def subsiteShriekBaseChangeIso
    (adjY : letI := hY; Lg ⊣ Q.ι.sheafPushforwardContinuous (Type w) J𝒴' J𝒴)
    (adjX : letI := hX; Lg' ⊣ P.ι.sheafPushforwardContinuous (Type w) J𝒳' J𝒳)
    (hiso : IsIso (subsiteSheafBaseChange f P hPQ J𝒳 J𝒴 J𝒳' J𝒴' hfcc hf'cc hX hY)) :
    letI := hfc
    letI := hfcc
    letI := hf'c
    letI := hf'cc
    (subsiteFunctor f P hPQ).sheafPushforwardContinuous (Type w) J𝒳' J𝒴' ⋙ Lg' ≅
      Lg ⋙ f.sheafPushforwardContinuous (Type w) J𝒳 J𝒴 :=
  letI := hfc
  letI := hfcc
  letI := hf'c
  letI := hf'cc
  letI := hX
  letI := hY
  haveI := hiso
  (conjugateIsoEquiv (adjY.comp (f.sheafAdjunctionCocontinuous (Type w) J𝒳 J𝒴))
      (((subsiteFunctor f P hPQ).sheafAdjunctionCocontinuous (Type w) J𝒳' J𝒴').comp adjX)).symm
    (asIso (subsiteSheafBaseChange f P hPQ J𝒳 J𝒴 J𝒳' J𝒴' hfcc hf'cc hX hY))

end Shriek


end CategoryTheory.SubsitePushforward

end
