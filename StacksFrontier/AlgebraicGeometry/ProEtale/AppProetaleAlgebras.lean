module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Characterization
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.AppProetaleSite
public import StacksFrontier.AlgebraicGeometry.Smooth.LiftTorsor

/-!
# The affine ind-étale pro-étale site is the opposite of the ind-étale algebras

For an **affine** scheme `S`, Stacks 098X singles out inside the small pro-étale site of `S` the
full subcategory `S_app` of objects which are affine and whose coordinate ring extension
`Γ(S, ⊤) → Γ(V, ⊤)` is ind-étale; this is
`AlgebraicGeometry.ProEtale.AppProetale`.  Taking global sections identifies `S_app` with the
opposite of the category `AlgebraicGeometry.ProEtale.IndEtaleAlgebra Γ(S, ⊤)` of ind-étale
`Γ(S, ⊤)`-algebras, which is the category on which Stacks 097P is proved.

## Main definitions

* `AlgebraicGeometry.ProEtale.appGamma` — global sections as a functor
  `(AppProetale S)ᵒᵖ ⥤ IndEtaleAlgebra Γ(S, ⊤)`.
* `AlgebraicGeometry.ProEtale.appGammaPreimage` and
  `AlgebraicGeometry.ProEtale.appGammaFullyFaithful` — its inverse on morphisms, and the
  resulting full faithfulness.
* `AlgebraicGeometry.ProEtale.appOfIndEtaleAlgebraHom` and
  `AlgebraicGeometry.ProEtale.appOfIndEtaleAlgebra` — the affine ind-étale object of the small
  pro-étale site attached to an ind-étale `Γ(S, ⊤)`-algebra, and its structure morphism.
* `AlgebraicGeometry.ProEtale.appGammaObjIso` — its global sections are the algebra one started
  from, so `appGamma` is essentially surjective.
* `AlgebraicGeometry.ProEtale.appGammaEquivalence` — the resulting equivalence
  `(AppProetale S)ᵒᵖ ≌ IndEtaleAlgebra Γ(S, ⊤)`.
* `AlgebraicGeometry.ProEtale.appBaseChangeAlg` — the opposite of the base-change functor `u` of
  Stacks 09BK, read through that equivalence as a functor between ind-étale algebras.

## Main results

* `AlgebraicGeometry.ProEtale.indEtale_iff_ind_etale_underMk` — the universe-pinned algebra
  form `StacksDraft.IndEtale` of ind-étaleness agrees with the
  `CategoryTheory.ObjectProperty.ind` form used by
  `AlgebraicGeometry.ProEtale.IndEtaleAlgebra` and
  `AlgebraicGeometry.ProEtale.IsAffineIndEtaleAlgebra`.
* `AlgebraicGeometry.ProEtale.weaklyEtale_specMap_of_ind_etale` — `Spec` of an ind-étale ring
  map is weakly étale.
* `AlgebraicGeometry.ProEtale.isRightAdjoint_appBaseChange_of_comparison` and its
  `appBaseChangeAlg` form — the functor `u` of Stacks 09BK has a left adjoint as soon as a
  functor of ind-étale algebras comparing with `u`ᵒᵖ has a right adjoint.
* `AlgebraicGeometry.ProEtale.isRightAdjoint_proetaleInverseImage_of_isRightAdjoint_appBaseChange`
  — Stacks 09BL (3) from `HasAppCover` (Stacks 097Z) together with a left adjoint of `u` and its
  continuity.

## Implementation notes

* Morphisms into an affine scheme are read off global sections by
  `Stacks.Smooth.homEquivOfIsAffine`, which assumes only that the *target* is affine.
* Full faithfulness of `appGamma` needs `S` affine even though both objects of `S_app` are
  affine: the commuting triangle over `S` is recovered from its image on global sections by
  `AlgebraicGeometry.ext_of_isAffine`, whose hypothesis is affineness of the target, here `S`.
* The structure morphism of the object attached to an algebra `Γ(S, ⊤) → B` is written as
  `Stacks.Smooth.homEquivOfIsAffine.symm` of `Γ(S, ⊤) → B ≅ Γ(Spec B, ⊤)`, so that its map on
  global sections is that composite *on the nose* and no naturality lemma for
  `AlgebraicGeometry.Scheme.isoSpec` is needed.
* Ind-étaleness of a ring map is spelled by `CategoryTheory.ObjectProperty.ind` applied to
  `CommRingCat.etale.underObj`, which is the spelling of `IndEtaleAlgebra` and of
  `IsAffineIndEtaleAlgebra`; `indEtale_iff_ind_etale_underMk` converts it into the universe-pinned
  algebra form `StacksDraft.IndEtale`.
* `appGammaEquivalence` is `CategoryTheory.Functor.asEquivalence`, so its inverse is
  `CategoryTheory.Functor.inv` and is choice-based; `isRightAdjoint_appBaseChange_of_comparison`
  is stated for an arbitrary comparison functor, so it involves no computation with that inverse.

## References

* [Stacks Project, Tag 097N](https://stacks.math.columbia.edu/tag/097N)
* [Stacks Project, Tag 097P](https://stacks.math.columbia.edu/tag/097P)
* [Stacks Project, Tag 097Z](https://stacks.math.columbia.edu/tag/097Z)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
* [Stacks Project, Tag 09BL](https://stacks.math.columbia.edu/tag/09BL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

universe u w

/-! ## Global sections of an affine ind-étale object -/

variable (S : Scheme.{u})

/-- Global sections as a functor from the opposite of the affine ind-étale site of `S` to the
ind-étale `Γ(S, ⊤)`-algebras.  On objects it is
`AlgebraicGeometry.ProEtale.appToIndEtaleAlgebra`, and on morphisms it is
`AlgebraicGeometry.Scheme.Hom.appTop`. -/
public def appGamma : (AppProetale S)ᵒᵖ ⥤ IndEtaleAlgebra ↥Γ(S, ⊤) where
  obj V := appToIndEtaleAlgebra S V.unop
  map {V _} f := ObjectProperty.homMk (Under.homMk f.unop.hom.left.appTop
    ((Scheme.Hom.comp_appTop f.unop.hom.left (unop V).obj.hom).symm.trans
      (congrArg Scheme.Hom.appTop f.unop.hom.w)))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The morphism of `AppProetale S` attached to a map of ind-étale `Γ(S, ⊤)`-algebras.

Its underlying morphism of schemes is `Stacks.Smooth.homEquivOfIsAffine.symm` of the ring map,
and the commuting triangle over `S` is recovered from the one over `Γ(S, ⊤)` because `S` is
affine. -/
public def appGammaPreimage [IsAffine S] {V V' : (AppProetale S)ᵒᵖ}
    (φ : (appGamma S).obj V ⟶ (appGamma S).obj V') : V ⟶ V' := by
  have hV : IsAffine (unop V).obj.left := (unop V).property.1
  have hVi : IsAffine ((𝟭 Scheme.{u}).obj (unop V).obj.left) := (unop V).property.1
  have hS : IsAffine ((Functor.fromPUnit S).obj (unop V).obj.right) := ‹IsAffine S›
  have hS' : IsAffine ((Functor.fromPUnit S).obj (unop V').obj.right) := ‹IsAffine S›
  refine Quiver.Hom.op (ObjectProperty.homMk
    (MorphismProperty.Over.homMk (Stacks.Smooth.homEquivOfIsAffine.symm φ.hom.right) ?_))
  refine ext_of_isAffine ((Scheme.Hom.comp_appTop _ _).trans ?_)
  exact (congrArg (fun g ↦ Scheme.Hom.appTop (unop V).obj.hom ≫ g)
    (Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply φ.hom.right)).trans (Under.w φ.hom)

/-- Global sections is fully faithful on the affine ind-étale site of an affine scheme: a map of
ind-étale `Γ(S, ⊤)`-algebras comes from a unique morphism of the site, namely
`AlgebraicGeometry.ProEtale.appGammaPreimage` of it. -/
public def appGammaFullyFaithful [IsAffine S] : (appGamma S).FullyFaithful where
  preimage φ := appGammaPreimage S φ
  map_preimage {V V'} φ := by
    have hV : IsAffine (unop V).obj.left := (unop V).property.1
    have hVi : IsAffine ((𝟭 Scheme.{u}).obj (unop V).obj.left) := (unop V).property.1
    refine ObjectProperty.hom_ext _ (Under.UnderMorphism.ext ?_)
    exact Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply φ.hom.right
  preimage_map {V V'} f := by
    have hV : IsAffine (unop V).obj.left := (unop V).property.1
    refine Quiver.Hom.unop_inj (ObjectProperty.hom_ext _
      (MorphismProperty.Comma.Hom.ext' (CommaMorphism.ext ?_ ?_)))
    · exact Stacks.Smooth.homEquivOfIsAffine.symm_apply_apply f.unop.hom.left
    · exact Subsingleton.elim _ _

/-- Global sections is faithful on the affine ind-étale site of an affine scheme. -/
public instance appGamma_faithful [IsAffine S] : (appGamma S).Faithful :=
  (appGammaFullyFaithful S).faithful

/-- Global sections is full on the affine ind-étale site of an affine scheme. -/
public instance appGamma_full [IsAffine S] : (appGamma S).Full := (appGammaFullyFaithful S).full

/-! ## The affine ind-étale object attached to an ind-étale algebra -/

/-- The universe-pinned algebra form of ind-étaleness, `StacksDraft.IndEtale`, agrees with the
`CategoryTheory.ObjectProperty.ind` form in which `AlgebraicGeometry.ProEtale.IndEtaleAlgebra`
and `AlgebraicGeometry.ProEtale.IsAffineIndEtaleAlgebra` are stated. -/
public theorem indEtale_iff_ind_etale_underMk {R : CommRingCat.{u}} {B : Type u} [CommRing B]
    [Algebra ↥R B] :
    StacksDraft.IndEtale ↥R B ↔
      ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj (X := R))
        (Under.mk (CommRingCat.ofHom (algebraMap ↥R B))) := by
  rw [StacksDraft.indEtale_iff, CommAlgCat.ind_etale_iff_ind_algebraMap,
    MorphismProperty.ind_iff_ind_underMk]

/-- **Stacks Project, Tag 097N** in geometric form: `Spec` of an ind-étale ring map is weakly
étale.  Ind-étaleness is in the `CategoryTheory.ObjectProperty.ind` spelling used by
`AlgebraicGeometry.ProEtale.IndEtaleAlgebra`. -/
public theorem weaklyEtale_specMap_of_ind_etale {R B : CommRingCat.{u}} (f : R ⟶ B)
    (h : ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj (X := R)) (Under.mk f)) :
    WeaklyEtale (Spec.map f) := by
  rw [weaklyEtale_specMap_iff]
  algebraize [f.hom]
  exact Algebra.weaklyEtale_of_ind_etale (indEtale_iff_ind_etale_underMk.mpr h)

/-- The structure morphism over `S` of the affine ind-étale object attached to an ind-étale
`Γ(S, ⊤)`-algebra `B`: the morphism of schemes `Spec B ⟶ S` whose map on global sections is the
structure map of `B` followed by `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
public def appOfIndEtaleAlgebraHom [IsAffine S] (B : IndEtaleAlgebra ↥Γ(S, ⊤)) :
    Spec B.obj.right ⟶ S :=
  Stacks.Smooth.homEquivOfIsAffine.symm (B.obj.hom ≫ (Scheme.ΓSpecIso B.obj.right).inv)

/-- The structure morphism attached to an ind-étale algebra induces, on global sections, the
structure map of the algebra followed by `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
@[simp]
public theorem appTop_appOfIndEtaleAlgebraHom [IsAffine S] (B : IndEtaleAlgebra ↥Γ(S, ⊤)) :
    (appOfIndEtaleAlgebraHom S B).appTop
      = B.obj.hom ≫ (Scheme.ΓSpecIso B.obj.right).inv :=
  Stacks.Smooth.homEquivOfIsAffine.apply_symm_apply _

/-- An ind-étale `Γ(S, ⊤)`-algebra is isomorphic, as an object under `Γ(S, ⊤)`, to the global
sections of the affine scheme of the algebra with the structure morphism
`AlgebraicGeometry.ProEtale.appOfIndEtaleAlgebraHom`. -/
public def indEtaleAlgebraUnderIso [IsAffine S] (B : IndEtaleAlgebra ↥Γ(S, ⊤)) :
    B.obj ≅ Under.mk (appOfIndEtaleAlgebraHom S B).appTop :=
  Under.isoMk (Scheme.ΓSpecIso B.obj.right).symm
    (appTop_appOfIndEtaleAlgebraHom S B).symm

/-- The structure morphism attached to an ind-étale algebra is weakly étale, so the affine
scheme of the algebra is an object of the small pro-étale site of `S`. -/
public instance weaklyEtale_appOfIndEtaleAlgebraHom [IsAffine S]
    (B : IndEtaleAlgebra ↥Γ(S, ⊤)) : WeaklyEtale (appOfIndEtaleAlgebraHom S B) := by
  have h : WeaklyEtale (Spec.map (appOfIndEtaleAlgebraHom S B).appTop) := by
    rw [appTop_appOfIndEtaleAlgebraHom, Spec.map_comp]
    have hB : WeaklyEtale (Spec.map B.obj.hom) := weaklyEtale_specMap_of_ind_etale _ B.property
    infer_instance
  exact (MorphismProperty.arrow_mk_iso_iff (P := @WeaklyEtale)
    (arrowIsoSpecΓOfIsAffine (appOfIndEtaleAlgebraHom S B))).mpr h

/-- The affine ind-étale object of the small pro-étale site of `S` attached to an ind-étale
`Γ(S, ⊤)`-algebra `B`: the affine scheme `Spec B` with the structure morphism
`AlgebraicGeometry.ProEtale.appOfIndEtaleAlgebraHom`. -/
public def appOfIndEtaleAlgebra [IsAffine S] (B : IndEtaleAlgebra ↥Γ(S, ⊤)) :
    AppProetale S where
  obj := Scheme.ProEt.mk (appOfIndEtaleAlgebraHom S B)
  property := ⟨inferInstanceAs (IsAffine (Spec B.obj.right)),
    (ObjectProperty.ind.{u} ((CommRingCat.etale.{u}).underObj
      (X := Γ(S, ⊤)))).prop_of_iso (indEtaleAlgebraUnderIso S B) B.property⟩

/-- The global sections of the affine ind-étale object attached to an ind-étale algebra are that
algebra: `AlgebraicGeometry.ProEtale.appGamma` is essentially surjective. -/
public def appGammaObjIso [IsAffine S] (B : IndEtaleAlgebra ↥Γ(S, ⊤)) :
    (appGamma S).obj (op (appOfIndEtaleAlgebra S B)) ≅ B :=
  ObjectProperty.isoMk _ (indEtaleAlgebraUnderIso S B).symm

/-- Global sections is essentially surjective on the affine ind-étale site of an affine scheme:
every ind-étale `Γ(S, ⊤)`-algebra is the global sections of
`AlgebraicGeometry.ProEtale.appOfIndEtaleAlgebra` of it. -/
public instance appGamma_essSurj [IsAffine S] : (appGamma S).EssSurj where
  mem_essImage B := ⟨op (appOfIndEtaleAlgebra S B), ⟨appGammaObjIso S B⟩⟩

/-- Global sections is an equivalence on the affine ind-étale site of an affine scheme. -/
public instance appGamma_isEquivalence [IsAffine S] : (appGamma S).IsEquivalence := {}

/-- Global sections is an equivalence from the opposite of the affine ind-étale site of an
affine scheme `S` to the ind-étale `Γ(S, ⊤)`-algebras. -/
public def appGammaEquivalence [IsAffine S] :
    (AppProetale S)ᵒᵖ ≌ IndEtaleAlgebra ↥Γ(S, ⊤) :=
  (appGamma S).asEquivalence

/-! ## Base change on the affine ind-étale sites, read on ind-étale algebras -/

section BaseChange

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (i : Z ⟶ X)

/-- The *opposite* of pro-étale base change on the affine ind-étale sites — the opposite of the
functor `u` of Stacks 09BK — read through `AlgebraicGeometry.ProEtale.appGammaEquivalence` as a
functor between the categories of ind-étale algebras.  Up to the two equivalences it is
extension of scalars along `Γ(X, ⊤) ⟶ Γ(Z, ⊤)`; being the avatar of `u`ᵒᵖ rather than of `u`,
it has a *right* adjoint exactly when `u` has a *left* adjoint. -/
public def appBaseChangeAlg :
    IndEtaleAlgebra ↥Γ(X, ⊤) ⥤ IndEtaleAlgebra ↥Γ(Z, ⊤) :=
  (appGammaEquivalence X).inverse ⋙ (appBaseChange i).op ⋙ (appGammaEquivalence Z).functor

/-- `AlgebraicGeometry.ProEtale.appBaseChangeAlg` compares with opposite base change along the
two global-sections equivalences. -/
public def appBaseChangeAlgIso :
    (appGammaEquivalence X).functor ⋙ appBaseChangeAlg i ≅
      (appBaseChange i).op ⋙ (appGammaEquivalence Z).functor :=
  (appGammaEquivalence X).funInvIdAssoc
    ((appBaseChange i).op ⋙ (appGammaEquivalence Z).functor)

/-- The base-change functor `u` of Stacks 09BK on the affine ind-étale sites of two affine
schemes has a left adjoint as soon as some functor `F` of ind-étale algebras has a right adjoint
and compares with `u`ᵒᵖ along the two global-sections equivalences.

Only existence of a left adjoint is concluded; Stacks 09BK's `v` is moreover fully faithful,
cocontinuous and covering-preserving, none of which is asserted here. -/
public theorem isRightAdjoint_appBaseChange_of_comparison
    (F : IndEtaleAlgebra ↥Γ(X, ⊤) ⥤ IndEtaleAlgebra ↥Γ(Z, ⊤)) [F.IsLeftAdjoint]
    (e : (appGammaEquivalence X).functor ⋙ F ≅
      (appBaseChange i).op ⋙ (appGammaEquivalence Z).functor) :
    (appBaseChange i).IsRightAdjoint := by
  have ecomp : ((appGammaEquivalence X).functor ⋙ F) ⋙ (appGammaEquivalence Z).inverse ≅
      (appBaseChange i).op :=
    Functor.isoWhiskerRight e (appGammaEquivalence Z).inverse ≪≫
      Functor.isoWhiskerLeft (appBaseChange i).op (appGammaEquivalence Z).unitIso.symm ≪≫
      (appBaseChange i).op.rightUnitor
  have hop : ((appBaseChange i).op).IsLeftAdjoint :=
    ((((appGammaEquivalence X).toAdjunction.comp (Adjunction.ofIsLeftAdjoint F)).comp
      (appGammaEquivalence Z).symm.toAdjunction).ofNatIsoLeft ecomp).isLeftAdjoint
  exact (Adjunction.unop (Adjunction.ofIsLeftAdjoint ((appBaseChange i).op))).isRightAdjoint

/-- The base-change functor `u` of Stacks 09BK has a left adjoint as soon as its
ind-étale-algebra avatar `AlgebraicGeometry.ProEtale.appBaseChangeAlg` has a right adjoint. -/
public theorem isRightAdjoint_appBaseChange_of_alg [(appBaseChangeAlg i).IsLeftAdjoint] :
    (appBaseChange i).IsRightAdjoint :=
  isRightAdjoint_appBaseChange_of_comparison i _ (appBaseChangeAlgIso i)

/-- **Stacks 09BL (3)** for the small pro-étale sites, with the left adjoint `v` of Stacks 09BK
replaced by the bare assertion that the base-change functor `u` has one: given `HasAppCover` for
`X` and for `Z` (Stacks 097Z) and continuity of the left adjoint of `u`, pullback of sheaves along
pro-étale base change is a right adjoint. -/
public theorem isRightAdjoint_proetaleInverseImage_of_isRightAdjoint_appBaseChange
    [(appBaseChange i).IsRightAdjoint] (hX : HasAppCover X) (hZ : HasAppCover Z)
    (hW : ((appBaseChange i).leftAdjoint).IsContinuous
      ((AppProetale.inclusion Z).inducedTopology (Scheme.ProEt.topology Z))
      ((AppProetale.inclusion X).inducedTopology (Scheme.ProEt.topology X))) :
    (Functor.sheafPullbackConstruction.sheafPullback (Scheme.proetaleBaseChange i)
      (Type (max (u + 1) w)) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z)).IsRightAdjoint :=
  isRightAdjoint_proetaleInverseImage_of_hasAppCover i hX hZ _ hW
    (Adjunction.ofIsRightAdjoint (appBaseChange i))

end BaseChange

end AlgebraicGeometry.ProEtale

end
