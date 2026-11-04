module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverSchemeRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Equalizer
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange

/-!
# Functors on the test schemes supported on a locally closed subscheme

This file collects the infrastructure for the following argument: a functor on the test schemes
over a scheme `Z` which is *supported* on a subscheme `Z₀ ⊆ Z` (every test scheme at which it
has a point factors through `Z₀`) and whose restriction to the test schemes over `Z₀` is
representable, is itself representable.

## Main definitions

* `AlgebraicGeometry.Space.overSchemeTest`: the objects of `(Sch/Z)` as test schemes over the
  algebraic space of `Z`.
* `AlgebraicGeometry.Space.spacePointsOverBaseChangeIso`: the functor of points over `W` of the
  base change of `p : H ⟶ Y` along `j : W ⟶ Y` is the restriction along `j` of the functor of
  points of `p`.

## Main results

* `CategoryTheory.Over.supportedReprIso`: a presheaf on `C/U` supported on the objects factoring
  through a monomorphism `j : Z ⟶ U`, whose restriction along `Over.map j` is represented by
  `q : H ⟶ Z`, is represented by `q ≫ j`.
* `CategoryTheory.Functor.relativelyRepresentable.exists_iso_yoneda`: a presheaf with a
  relatively representable morphism to a representable presheaf is representable.
* `AlgebraicGeometry.Space.exists_mono_comp_eq_iff_factors` (and its presheaf form
  `AlgebraicGeometry.Space.exists_mono_yoneda_comp_eq_iff`): the locus of a scheme `U` where two
  morphisms to an algebraic space agree is a subscheme of `U`.
* `AlgebraicGeometry.Space.IsAffineAlgebraicSpaceOver.baseChange` and
  `AlgebraicGeometry.Space.IsAffineFinitePresentationAlgebraicSpaceOver.baseChange`: being an
  algebraic space affine (and of finite presentation) over the base is stable under base change.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_factors_iff`: the intersection of two open
  subspaces.
* `AlgebraicGeometry.Space.exists_iso_yoneda_overSchemeTest`: a functor on the test schemes over
  a scheme `Z`, supported on an open subspace `W` of `Z` and an algebraic space affine over `W`
  there, is representable on `(Sch/Z)`; `exists_iso_yoneda_overSchemeTest_of_mono` is the same
  for a monomorphism of schemes `Z₀ ⟶ Z` in place of the open subspace.

## Implementation notes

The support lemma is proved for an arbitrary category `C`: for an object `g` of `C/U` with a
section of the presheaf, the factorization `t` of `g` through `j` is unique since `j` is a
monomorphism, so the section can be transported to the object `t` of `C/Z`, where the
representability is available.  Uniqueness of `t` is what makes the construction independent of
the factorization chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Over

universe v₁ u₁ w

variable {C : Type u₁} [Category.{v₁} C] {U Z H : C} (j : Z ⟶ U) (q : H ⟶ Z)
  (P : (Over U)ᵒᵖ ⥤ Type (max v₁ w))
  (e : (Over.map j).op ⋙ P ≅ yoneda.obj (Over.mk q) ⋙ uliftFunctor.{w})

/-- An object of `C/U` together with a factorization `t` of its structure morphism through
`j : Z ⟶ U` is isomorphic to the image under `Over.map j` of the object `t` of `C/Z`. -/
def mapObjMkIso {g : Over U} (t : g.left ⟶ Z) (ht : t ≫ j = g.hom) :
    (Over.map j).obj (Over.mk t) ≅ g :=
  Over.isoMk (Iso.refl _) (by simp [ht])

/-- The morphism to `q` in `C/Z` attached to a section `a` of `P` over `g` and a factorization
`t` of `g` through `j`: transport `a` to the object `t` of `C/Z` and apply `e`. -/
def supportedLift (g : Over U) (t : g.left ⟶ Z) (ht : t ≫ j = g.hom) (a : P.obj (op g)) :
    Over.mk t ⟶ Over.mk q :=
  (e.hom.app (op (Over.mk t)) (P.map (mapObjMkIso j t ht).hom.op a)).down

/-- The morphism `supportedLift` lies over `Z`. -/
theorem supportedLift_w (g : Over U) (t : g.left ⟶ Z) (ht : t ≫ j = g.hom) (a : P.obj (op g)) :
    (supportedLift j q P e g t ht a).left ≫ q = t :=
  Over.w (supportedLift j q P e g t ht a)

/-- The point of `yoneda (q ≫ j)` attached to a section `a` of `P` over `g` and a factorization
`t` of `g` through `j`: the composite of `supportedLift` with `j`. -/
def supportedPoint (g : Over U) (t : g.left ⟶ Z) (ht : t ≫ j = g.hom) (a : P.obj (op g)) :
    ULift.{w} (g ⟶ Over.mk (q ≫ j)) :=
  ULift.up (Over.homMk (supportedLift j q P e g t ht a).left (by
    change _ ≫ q ≫ j = g.hom
    rw [← Category.assoc, supportedLift_w, ht]))

variable [Mono j]

/-- The point `supportedPoint` does not depend on the factorization, which is unique since `j`
is a monomorphism. -/
theorem supportedPoint_congr (g : Over U) (t t' : g.left ⟶ Z) (ht : t ≫ j = g.hom)
    (ht' : t' ≫ j = g.hom) (a : P.obj (op g)) :
    supportedPoint j q P e g t ht a = supportedPoint j q P e g t' ht' a := by
  obtain rfl : t = t' := (cancel_mono j).1 (ht.trans ht'.symm)
  rfl

/-- The point `supportedPoint` is natural in the object of `C/U`. -/
theorem supportedPoint_naturality {X₁ X₂ : Over U} (h : X₂ ⟶ X₁) (t₁ : X₁.left ⟶ Z)
    (ht₁ : t₁ ≫ j = X₁.hom) (t₂ : X₂.left ⟶ Z) (ht₂ : t₂ ≫ j = X₂.hom) (a : P.obj (op X₁)) :
    (supportedPoint j q P e X₂ t₂ ht₂ (P.map h.op a)).down =
      h ≫ (supportedPoint j q P e X₁ t₁ ht₁ a).down := by
  have hk : h.left ≫ t₁ = t₂ := (cancel_mono j).1 (by simp [ht₁, ht₂, Over.w h])
  let k : Over.mk t₂ ⟶ Over.mk t₁ := Over.homMk h.left hk
  have hm : (mapObjMkIso j t₂ ht₂).hom ≫ h = (Over.map j).map k ≫ (mapObjMkIso j t₁ ht₁).hom := by
    ext
    simp [k, mapObjMkIso]
  have h1 : P.map (mapObjMkIso j t₂ ht₂).hom.op (P.map h.op a) =
      P.map ((Over.map j).map k).op (P.map (mapObjMkIso j t₁ ht₁).hom.op a) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hm]
  have h2 : supportedLift j q P e X₂ t₂ ht₂ (P.map h.op a) =
      k ≫ supportedLift j q P e X₁ t₁ ht₁ a :=
    (congrArg (fun x => (e.hom.app (op (Over.mk t₂)) x).down) h1).trans
      (congrArg ULift.down
        (NatTrans.naturality_apply e.hom k.op (P.map (mapObjMkIso j t₁ ht₁).hom.op a)))
  exact Over.OverMorphism.ext (congrArg (fun m => m.left) h2)

variable (hP : ∀ g : Over U, Nonempty (P.obj (op g)) → ∃ t : g.left ⟶ Z, t ≫ j = g.hom)

/-- The comparison morphism from a presheaf supported on the objects factoring through `j` to
the presheaf represented by `q ≫ j`. -/
def supportedPointsHom : P ⟶ yoneda.obj (Over.mk (q ≫ j)) ⋙ uliftFunctor.{w} where
  app g := ↾fun a => supportedPoint j q P e g.unop (hP g.unop ⟨a⟩).choose
    (hP g.unop ⟨a⟩).choose_spec a
  naturality g₁ g₂ h := by
    ext a
    exact ULift.ext _ _ (supportedPoint_naturality j q P e h.unop _ _ _ _ a)

/-- The comparison morphism `supportedPointsHom` is bijective at every object. -/
theorem bijective_supportedPointsHom_app (g : (Over U)ᵒᵖ) :
    Function.Bijective ((supportedPointsHom j q P e hP).app g) := by
  refine ⟨fun a a' haa => ?_, fun s => ?_⟩
  · have h1 : (supportedLift j q P e g.unop _ (hP g.unop ⟨a⟩).choose_spec a).left =
        (supportedLift j q P e g.unop _ (hP g.unop ⟨a⟩).choose_spec a').left :=
      congrArg (fun s => s.down.left) haa
    exact (P.mapIso (mapObjMkIso j _ (hP g.unop ⟨a⟩).choose_spec).op).toEquiv.injective
      ((e.app (op (Over.mk (hP g.unop ⟨a⟩).choose))).toEquiv.injective
        (ULift.ext _ _ (Over.OverMorphism.ext h1)))
  · let t₀ : g.unop.left ⟶ Z := s.down.left ≫ q
    have ht₀ : t₀ ≫ j = g.unop.hom := by
      simpa [t₀] using Over.w s.down
    let ε := mapObjMkIso j t₀ ht₀
    let b := e.inv.app (op (Over.mk t₀))
      (ULift.up (Over.homMk s.down.left rfl : Over.mk t₀ ⟶ Over.mk q))
    refine ⟨P.map ε.inv.op b, ?_⟩
    show supportedPoint j q P e g.unop _ _ (P.map ε.inv.op b) = s
    rw [supportedPoint_congr j q P e g.unop _ t₀ _ ht₀]
    have hb : P.map ε.hom.op (P.map ε.inv.op b) = b := (P.mapIso ε.op).inv_hom_id_apply b
    have hl : supportedLift j q P e g.unop t₀ ht₀ (P.map ε.inv.op b) =
        (Over.homMk s.down.left rfl : Over.mk t₀ ⟶ Over.mk q) :=
      (congrArg (fun x => (e.hom.app (op (Over.mk t₀)) x).down) hb).trans
        (congrArg ULift.down (Iso.inv_hom_id_app_apply e _ _))
    exact ULift.ext _ _ (Over.OverMorphism.ext (congrArg (fun m => m.left) hl))

/-- **A presheaf supported on a monomorphism and representable there is representable.**
Let `j : Z ⟶ U` be a monomorphism and `P` a presheaf on `C/U` such that every object of `C/U`
at which `P` has a section factors through `j`.  If the restriction of `P` along `Over.map j`
is represented by `q : H ⟶ Z`, then `P` is represented by `q ≫ j`. -/
def supportedReprIso : P ≅ yoneda.obj (Over.mk (q ≫ j)) ⋙ uliftFunctor.{w} :=
  haveI : ∀ g, IsIso ((supportedPointsHom j q P e hP).app g) := fun g =>
    (isIso_iff_bijective _).2 (bijective_supportedPointsHom_app j q P e hP g)
  haveI : IsIso (supportedPointsHom j q P e hP) := NatIso.isIso_of_isIso_app _
  asIso (supportedPointsHom j q P e hP)

end CategoryTheory.Over

namespace CategoryTheory.Functor.relativelyRepresentable

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {F : Cᵒᵖ ⥤ Type v₁} {Z : C}

/-- A presheaf with a relatively representable morphism to a representable presheaf is
representable: by its base change along the identity. -/
theorem exists_iso_yoneda {f : F ⟶ yoneda.obj Z} (hf : yoneda.relativelyRepresentable f) :
    ∃ (Z₀ : C) (i : Z₀ ⟶ Z) (e : yoneda.obj Z₀ ≅ F), e.hom ≫ f = yoneda.map i := by
  have sq := hf.isPullback (𝟙 (yoneda.obj Z))
  have : IsIso (hf.fst (𝟙 (yoneda.obj Z))) := sq.isIso_fst_of_isIso
  exact ⟨_, hf.snd (𝟙 _), asIso (hf.fst (𝟙 _)), by simpa using hf.w (𝟙 (yoneda.obj Z))⟩

/-- If a monomorphism `f : F ⟶ yoneda.obj Z` is identified with `yoneda.map i` by an isomorphism
`yoneda.obj Z₀ ≅ F`, then `i` is a monomorphism. -/
theorem mono_of_iso_comp_eq_yoneda_map {Z₀ : C} (i : Z₀ ⟶ Z) (e : yoneda.obj Z₀ ≅ F)
    (f : F ⟶ yoneda.obj Z) (hf : Mono f) (he : e.hom ≫ f = yoneda.map i) : Mono i := by
  have : Mono (yoneda.map i) := by
    rw [← he]
    infer_instance
  exact yoneda.mono_of_mono_map this

end CategoryTheory.Functor.relativelyRepresentable

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The equalizer of two morphisms from a scheme -/

/-- A morphism of representables `t` with `t ≫ yoneda.map j = yoneda.map v` comes from a morphism
`V ⟶ Z` factoring `v` through `j`. -/
private theorem exists_comp_eq_of_comp_yoneda_map {C : Type*} [Category C] {V Z U : C}
    (j : Z ⟶ U) (v : V ⟶ U) (t : yoneda.obj V ⟶ yoneda.obj Z)
    (h : t ≫ yoneda.map j = yoneda.map v) : ∃ t' : V ⟶ Z, t' ≫ j = v :=
  ⟨yoneda.preimage t, yoneda.map_injective (by rw [yoneda.map_comp, yoneda.map_preimage, h])⟩

/-- **The locus where two morphisms from a scheme agree is a subscheme**, at the level of
presheaves: for an algebraic space `Y` and two morphisms `g g' : yoneda.obj U ⟶ Y` there is a
monomorphism of schemes `j : Z ⟶ U` such that `v : V ⟶ U` equalizes `g` and `g'` exactly when
it factors through `j`.  The scheme `Z` represents the equalizer of `g` and `g'`, which is a base
change of the diagonal of `Y`, hence relatively representable over `yoneda.obj U`. -/
theorem exists_mono_yoneda_comp_eq_iff {U : BigFppfOver B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (g g' : yoneda.obj U ⟶ Y) :
    ∃ (Z : BigFppfOver B S hS) (j : Z ⟶ U), Mono j ∧
      ∀ ⦃V : BigFppfOver B S hS⦄ (v : V ⟶ U),
        (yoneda.map v ≫ g = yoneda.map v ≫ g' ↔ ∃ t : V ⟶ Z, t ≫ j = v) := by
  obtain ⟨Z, j, e, he⟩ := Functor.relativelyRepresentable.exists_iso_yoneda
    (relative_locallyOfFiniteType_equalizer_ι B S hS hY g g').rep
  refine ⟨Z, j, Functor.relativelyRepresentable.mono_of_iso_comp_eq_yoneda_map j e _
    inferInstance he, fun V v => ⟨fun h => ?_, ?_⟩⟩
  · refine exists_comp_eq_of_comp_yoneda_map j v (equalizer.lift _ h ≫ e.inv) ?_
    rw [Category.assoc, ← he]
    simp
  · rintro ⟨t, rfl⟩
    rw [yoneda.map_comp, ← he]
    simp only [Category.assoc]
    rw [equalizer.condition]

/-- **The locus where two morphisms from a scheme to an algebraic space agree is a subscheme.**
For two morphisms `g g' : U ⟶ Y` from a scheme to an algebraic space there is a monomorphism of
schemes `j : Z ⟶ U` such that a morphism `v : V ⟶ U` equalizes `g` and `g'` exactly when it
factors through `j`.  The scheme `Z` represents the equalizer of `g` and `g'`. -/
theorem exists_mono_comp_eq_iff_factors {U : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS}
    (g g' : (schemeSpaceFunctor B S hS).obj U ⟶ Y) :
    ∃ (Z : BigFppfOver B S hS) (j : Z ⟶ U), Mono j ∧
      ∀ ⦃V : BigFppfOver B S hS⦄ (v : V ⟶ U),
        ((schemeSpaceFunctor B S hS).map v ≫ g = (schemeSpaceFunctor B S hS).map v ≫ g' ↔
          ∃ t : V ⟶ Z, t ≫ j = v) := by
  obtain ⟨Z, j, hj, H⟩ := exists_mono_yoneda_comp_eq_iff (U := U) Y.property g.hom g'.hom
  refine ⟨Z, j, hj, fun V v => ?_⟩
  rw [← H v]
  exact ⟨fun h => congrArg (fun k => k.hom) h, fun h => ObjectProperty.hom_ext _ h⟩

/-! ### Base change of the functor of points over the base -/

/-- The section of `Y` that the test scheme `(CostructuredArrow.map j).obj T` is, is the image
under `j` of the section of `W` that `T` is. -/
theorem testPoint_map {Y W : AlgebraicSpaces B S hS} (j : W ⟶ Y) (T : SchemesOver W) :
    testPoint ((CostructuredArrow.map j).obj T) = j.hom.app _ (testPoint T) :=
  yonedaEquiv_comp T.hom.hom j.hom

section BaseChange

variable {Y W H : AlgebraicSpaces B S hS} (p : H ⟶ Y) (j : W ⟶ Y)

/-- The projection to `W` of the fibre product `H ×_Y W`, as a morphism of algebraic spaces. -/
abbrev fiberProductSndToRight :
    AlgebraicSpaces.fiberProduct B S hS p j ⟶ W :=
  ObjectProperty.homMk (pullback.snd p.hom j.hom)

/-- The comparison from the functor of points over `W` of the base change `H ×_Y W ⟶ W` to the
restriction along `j` of the functor of points of `p`: the first projection. -/
def spacePointsOverBaseChangeHom :
    spacePointsOver (fiberProductSndToRight p j) ⟶
      (CostructuredArrow.map j).op ⋙ spacePointsOver p where
  app T := ↾fun x => ⟨(pullback.fst p.hom j.hom).app _ x.1, by
    calc p.hom.app _ ((pullback.fst p.hom j.hom).app _ x.1)
        = (pullback.fst p.hom j.hom ≫ p.hom).app _ x.1 := rfl
      _ = (pullback.snd p.hom j.hom ≫ j.hom).app _ x.1 := by rw [pullback.condition]
      _ = j.hom.app _ ((pullback.snd p.hom j.hom).app _ x.1) := rfl
      _ = j.hom.app _ (testPoint T.unop) := congrArg (j.hom.app _) x.2
      _ = testPoint ((CostructuredArrow.map j).obj T.unop) := (testPoint_map j T.unop).symm⟩
  naturality T T' f := by
    refine ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_
    exact NatTrans.naturality_apply (pullback.fst p.hom j.hom) f.unop.left.op x.1

/-- The comparison `spacePointsOverBaseChangeHom` is bijective at every test scheme: an element
of the fibre product of presheaves is determined by its two projections, and every compatible
pair comes from one. -/
theorem bijective_spacePointsOverBaseChangeHom_app (T : (SchemesOver W)ᵒᵖ) :
    Function.Bijective ((spacePointsOverBaseChangeHom p j).app T) := by
  have sq := (IsPullback.of_hasPullback p.hom j.hom).map
    ((evaluation _ (Type u)).obj (op T.unop.left))
  obtain ⟨-, hinj, hsurj⟩ := (Types.isPullback_iff _ _ _ _).1 sq
  constructor
  · intro x y hxy
    exact Subtype.ext (hinj x.1 y.1 ⟨congrArg Subtype.val hxy, x.2.trans y.2.symm⟩)
  · intro y
    obtain ⟨z, hz₁, hz₂⟩ := hsurj y.1 (testPoint T.unop) (y.2.trans (testPoint_map j T.unop))
    exact ⟨⟨z, hz₂⟩, Subtype.ext hz₁⟩

/-- **The functor of points of a base change.**  The functor of points over `W` of the base
change `H ×_Y W ⟶ W` of `p : H ⟶ Y` along `j : W ⟶ Y` is the restriction along `j` of the
functor of points over `Y` of `p`. -/
def spacePointsOverBaseChangeIso :
    spacePointsOver (fiberProductSndToRight p j) ≅
      (CostructuredArrow.map j).op ⋙ spacePointsOver p :=
  haveI : ∀ T, IsIso ((spacePointsOverBaseChangeHom p j).app T) := fun T =>
    (isIso_iff_bijective _).2 (bijective_spacePointsOverBaseChangeHom_app p j T)
  haveI : IsIso (spacePointsOverBaseChangeHom p j) := NatIso.isIso_of_isIso_app _
  asIso (spacePointsOverBaseChangeHom p j)

end BaseChange

variable {Y W : AlgebraicSpaces B S hS} {R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}

/-- **Being an algebraic space affine over the base is stable under base change.**  If `R` is an
algebraic space affine over `Y` and `j : W ⟶ Y` is a morphism of algebraic spaces, then the
restriction of `R` to the test schemes over `W` is an algebraic space affine over `W`,
represented by the base change. -/
theorem IsAffineAlgebraicSpaceOver.baseChange (j : W ⟶ Y) (h : IsAffineAlgebraicSpaceOver Y R) :
    IsAffineAlgebraicSpaceOver W ((CostructuredArrow.map j).op ⋙ R) := by
  obtain ⟨H, p, hp, ⟨c⟩⟩ := h
  exact ⟨_, fiberProductSndToRight p j,
    IsAffineHom.of_isPullback (IsPullback.of_hasPullback p.hom j.hom) hp,
    ⟨Functor.isoWhiskerRight (spacePointsOverBaseChangeIso p j) uliftFunctor.{u + 1, u} ≪≫
      Functor.isoWhiskerLeft (CostructuredArrow.map j).op c⟩⟩

/-- **Being an algebraic space affine and of finite presentation over the base is stable under
base change.**  If `R` is an algebraic space affine and of finite presentation over `Y` and
`j : W ⟶ Y` is a morphism of algebraic spaces, then the restriction of `R` to the test schemes
over `W` is an algebraic space affine and of finite presentation over `W`. -/
theorem IsAffineFinitePresentationAlgebraicSpaceOver.baseChange (j : W ⟶ Y)
    (h : IsAffineFinitePresentationAlgebraicSpaceOver Y R) :
    IsAffineFinitePresentationAlgebraicSpaceOver W ((CostructuredArrow.map j).op ⋙ R) := by
  obtain ⟨H, p, hp, hfp, ⟨c⟩⟩ := h
  exact ⟨_, fiberProductSndToRight p j,
    IsAffineHom.of_isPullback (IsPullback.of_hasPullback p.hom j.hom) hp,
    IsFinitePresentation.of_isPullback B S hS
      (AlgebraicSpaces.fiberProduct B S hS p j).property H.property W.property Y.property
      (IsPullback.of_hasPullback p.hom j.hom) hfp,
    ⟨Functor.isoWhiskerRight (spacePointsOverBaseChangeIso p j) uliftFunctor.{u + 1, u} ≪≫
      Functor.isoWhiskerLeft (CostructuredArrow.map j).op c⟩⟩

/-! ### Intersection of two open subspaces -/

/-- **The intersection of two open subspaces.**  For open immersions `j₁ : W₁ ⟶ Y` and
`j₂ : W₂ ⟶ Y` of algebraic spaces there is an open immersion `j : W ⟶ Y` factoring through both,
such that a morphism to `Y` factors through `j` exactly when it factors through `j₁` and
through `j₂`.  It is the fibre product `W₁ ×_Y W₂`. -/
theorem exists_isOpenImmersion_factors_iff {W₁ W₂ : AlgebraicSpaces B S hS} (j₁ : W₁ ⟶ Y)
    (j₂ : W₂ ⟶ Y) (h₁ : IsOpenImmersion B S hS j₁.hom) (h₂ : IsOpenImmersion B S hS j₂.hom) :
    ∃ (W : AlgebraicSpaces B S hS) (j : W ⟶ Y), IsOpenImmersion B S hS j.hom ∧
      (∃ k₁ : W ⟶ W₁, k₁ ≫ j₁ = j) ∧ (∃ k₂ : W ⟶ W₂, k₂ ≫ j₂ = j) ∧
      ∀ ⦃X : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y),
        ((∃ t : X ⟶ W, t ≫ j = f) ↔
          (∃ t₁ : X ⟶ W₁, t₁ ≫ j₁ = f) ∧ ∃ t₂ : X ⟶ W₂, t₂ ≫ j₂ = f) := by
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS j₁ j₂
  refine ⟨AlgebraicSpaces.fiberProduct B S hS j₁ j₂,
    (ObjectProperty.homMk (pullback.fst j₁.hom j₂.hom) :
      AlgebraicSpaces.fiberProduct B S hS j₁ j₂ ⟶ W₁) ≫ j₁,
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isPullback B S hS sq.flip h₂) h₁,
    ⟨_, rfl⟩, ⟨_, sq.w.symm⟩, fun X f => ⟨?_, ?_⟩⟩
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t ≫ _, Category.assoc _ _ _⟩,
      ⟨t ≫ _, (Category.assoc _ _ _).trans (congrArg (t ≫ ·) sq.w.symm)⟩⟩
  · rintro ⟨⟨t₁, rfl⟩, ⟨t₂, ht₂⟩⟩
    exact ⟨sq.lift t₁ t₂ ht₂.symm,
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ j₁) (sq.lift_fst _ _ _))⟩

/-! ### Representability on the test schemes over a scheme -/

/-- The objects of `(Sch/Z)` as test schemes over the algebraic space of the scheme `Z`. -/
def overSchemeTest (Z : BigFppfOver B S hS) :
    Over Z ⥤ SchemesOver ((schemeSpaceFunctor B S hS).obj Z) where
  obj g := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.hom)
  map {g₁ g₂} h := CostructuredArrow.homMk h.left (by
    simp only [CostructuredArrow.mk_hom_eq_self, ← Functor.map_comp, Over.w h])
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Restricting the test schemes over `Z` along a morphism of schemes `i : Z₀ ⟶ Z` commutes with
reading the objects of `(Sch/Z₀)` as test schemes. -/
def overSchemeTestMapIso {Z₀ Z : BigFppfOver B S hS} (i : Z₀ ⟶ Z) :
    overSchemeTest Z₀ ⋙ CostructuredArrow.map ((schemeSpaceFunctor B S hS).map i) ≅
      Over.map i ⋙ overSchemeTest Z :=
  NatIso.ofComponents
    (fun g => CostructuredArrow.isoMk (Iso.refl _) (by simp [overSchemeTest]))
    (fun f => by ext; simp [overSchemeTest])

/-- The functor of points over a scheme `Z₀` of an algebraic space `H₀` over `Z₀` which is
represented by `P : Y₁ ⟶ Z₀`, read on `(Sch/Z₀)`, is the presheaf represented by `P`. -/
def overSchemeTestPointsIso {Z₀ Y₁ : BigFppfOver B S hS} {H₀ : AlgebraicSpaces B S hS}
    (p : H₀ ⟶ (schemeSpaceFunctor B S hS).obj Z₀) (e : H₀.obj ≅ yoneda.obj Y₁) (P : Y₁ ⟶ Z₀)
    (he : e.inv ≫ p.hom = yoneda.map P) :
    (overSchemeTest Z₀).op ⋙ spacePointsOver p ≅ yoneda.obj (Over.mk P) :=
  NatIso.ofComponents
    (fun g => Equiv.toIso
      { toFun := fun x => Over.homMk (e.hom.app (op g.unop.left) x.1) (by
          change (yoneda.map P).app (op g.unop.left) (e.hom.app (op g.unop.left) x.1) = g.unop.hom
          rw [← he]
          refine Eq.trans ?_ (x.2.trans (yonedaEquiv_yoneda_map g.unop.hom))
          exact congrArg (p.hom.app (op g.unop.left)) (Iso.hom_inv_id_app_apply e _ x.1))
        invFun := fun s => ⟨e.inv.app (op g.unop.left) s.left, by
          change (e.inv ≫ p.hom).app (op g.unop.left) s.left = yonedaEquiv (yoneda.map g.unop.hom)
          rw [he, yonedaEquiv_yoneda_map]
          exact Over.w s⟩
        left_inv := fun x => Subtype.ext (Iso.hom_inv_id_app_apply e _ x.1)
        right_inv := fun s =>
          Over.OverMorphism.ext (Iso.inv_hom_id_app_apply e (op g.unop.left) _) })
    (fun f => by
      ext x
      apply Over.OverMorphism.ext
      dsimp
      exact NatTrans.naturality_apply e.hom f.unop.left.op x.1)

/-- **Representability on `(Sch/Z)` from a subscheme.**  Let `i : Z₀ ⟶ Z` be a monomorphism of
schemes and `R` a functor on the test schemes over `Z` such that every test scheme at which `R`
has a point factors through `i`.  If the restriction of `R` to the test schemes over `Z₀` is an
algebraic space affine over `Z₀`, then `R`, read on `(Sch/Z)`, is representable. -/
theorem exists_iso_yoneda_overSchemeTest_of_mono {Z₀ Z : BigFppfOver B S hS} (i : Z₀ ⟶ Z)
    [Mono i] (R : (SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1))
    (hR : ∀ T : SchemesOver ((schemeSpaceFunctor B S hS).obj Z), Nonempty (R.obj (op T)) →
      ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ (schemeSpaceFunctor B S hS).obj Z₀,
        t ≫ (schemeSpaceFunctor B S hS).map i = T.hom)
    (hA : IsAffineAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj Z₀)
      ((CostructuredArrow.map ((schemeSpaceFunctor B S hS).map i)).op ⋙ R)) :
    ∃ (H : BigFppfOver B S hS) (q : H ⟶ Z),
      Nonempty ((overSchemeTest Z).op ⋙ R ≅ yoneda.obj (Over.mk q) ⋙ uliftFunctor.{u + 1}) := by
  obtain ⟨H₀, p, hp, ⟨c⟩⟩ := hA
  obtain ⟨Y₁, e, P, he, -⟩ :=
    exists_representing_over_of_isAffineHom B S hS (T := Z₀) H₀.property p.hom hp
  refine ⟨Y₁, P ≫ i, ⟨Over.supportedReprIso i P ((overSchemeTest Z).op ⋙ R)
    (Functor.isoWhiskerRight (NatIso.op (overSchemeTestMapIso i)) R ≪≫
      Functor.isoWhiskerLeft (overSchemeTest Z₀).op c.symm ≪≫
      Functor.isoWhiskerRight (overSchemeTestPointsIso p e P he) uliftFunctor.{u + 1, u})
    (fun g hg => ?_)⟩⟩
  obtain ⟨t, ht⟩ := hR _ hg
  exact exists_comp_eq_of_comp_yoneda_map i g.hom t.hom (congrArg (fun k => k.hom) ht)

/-- Precomposing with the restriction along `φ` and then along `j` is restricting along the
composite, when `φ ≫ j` is the image of a morphism of schemes. -/
def costructuredArrowMapCompIso {Z₀ : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
    (φ : (schemeSpaceFunctor B S hS).obj Z₀ ⟶ W) (j : W ⟶ X)
    (k : (schemeSpaceFunctor B S hS).obj Z₀ ⟶ X) (hk : φ ≫ j = k) :
    CostructuredArrow.map (S := schemeSpaceFunctor B S hS) k ≅
      CostructuredArrow.map φ ⋙ CostructuredArrow.map j :=
  NatIso.ofComponents
    (fun T => CostructuredArrow.isoMk (Iso.refl _) (by simp [← hk]))
    (fun f => by ext; simp)

/-- **Representability on `(Sch/Z)` from an open subspace.**  Let `Z` be a scheme, `j : W ⟶ Z`
an open immersion of algebraic spaces and `R` a functor on the test schemes over `Z` such that
every test scheme at which `R` has a point factors through `W`.  If the restriction of `R` to
the test schemes over `W` is an algebraic space affine over `W`, then `R`, read on `(Sch/Z)`, is
representable: by a scheme `H` with a morphism `q : H ⟶ Z`.

The open subspace `W` of the scheme `Z` is a scheme `Z₀` (an open immersion is representable),
the algebraic space affine over `W` representing the restriction of `R` is a scheme (an
algebraic space affine over a scheme is a scheme), and the support condition carries the
representability from `(Sch/Z₀)` to `(Sch/Z)`. -/
theorem exists_iso_yoneda_overSchemeTest {Z : BigFppfOver B S hS} {W : AlgebraicSpaces B S hS}
    (j : W ⟶ (schemeSpaceFunctor B S hS).obj Z) (hj : IsOpenImmersion B S hS j.hom)
    (R : (SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1))
    (hR : ∀ T : SchemesOver ((schemeSpaceFunctor B S hS).obj Z), Nonempty (R.obj (op T)) →
      ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ W, t ≫ j = T.hom)
    (hA : IsAffineAlgebraicSpaceOver W ((CostructuredArrow.map j).op ⋙ R)) :
    ∃ (H : BigFppfOver B S hS) (q : H ⟶ Z),
      Nonempty ((overSchemeTest Z).op ⋙ R ≅ yoneda.obj (Over.mk q) ⋙ uliftFunctor.{u + 1}) := by
  obtain ⟨Z₀, i, e, he⟩ := Functor.relativelyRepresentable.exists_iso_yoneda (Z := Z) hj.rep
  have : Mono i := Functor.relativelyRepresentable.mono_of_iso_comp_eq_yoneda_map i e _
    (mono_of_isOpenImmersion B S hS j.hom hj) he
  let φ : (schemeSpaceFunctor B S hS).obj Z₀ ≅ W := ObjectProperty.isoMk _ e
  have hφ : φ.hom ≫ j = (schemeSpaceFunctor B S hS).map i := ObjectProperty.hom_ext _ he
  refine exists_iso_yoneda_overSchemeTest_of_mono i R (fun T hT => ?_)
    ((hA.baseChange φ.hom).of_iso (Functor.isoWhiskerRight
      (NatIso.op (costructuredArrowMapCompIso φ.hom j _ hφ)) R))
  obtain ⟨t, ht⟩ := hR T hT
  exact ⟨t ≫ φ.inv, by rw [Category.assoc, ← hφ, Iso.inv_hom_id_assoc, ht]⟩

/-- **Representability on `(Sch/Z)` from an open subspace**, for a functor which is an algebraic
space affine and of finite presentation over the open subspace: the special case of
`AlgebraicGeometry.Space.exists_iso_yoneda_overSchemeTest` in which the restriction is moreover
of finite presentation. -/
theorem exists_iso_yoneda_overSchemeTest_of_isAffineFinitePresentation
    {Z : BigFppfOver B S hS} {W : AlgebraicSpaces B S hS}
    (j : W ⟶ (schemeSpaceFunctor B S hS).obj Z) (hj : IsOpenImmersion B S hS j.hom)
    (R : (SchemesOver ((schemeSpaceFunctor B S hS).obj Z))ᵒᵖ ⥤ Type (u + 1))
    (hR : ∀ T : SchemesOver ((schemeSpaceFunctor B S hS).obj Z), Nonempty (R.obj (op T)) →
      ∃ t : (schemeSpaceFunctor B S hS).obj T.left ⟶ W, t ≫ j = T.hom)
    (hA : IsAffineFinitePresentationAlgebraicSpaceOver W ((CostructuredArrow.map j).op ⋙ R)) :
    ∃ (H : BigFppfOver B S hS) (q : H ⟶ Z),
      Nonempty ((overSchemeTest Z).op ⋙ R ≅ yoneda.obj (Over.mk q) ⋙ uliftFunctor.{u + 1}) :=
  exists_iso_yoneda_overSchemeTest j hj R hR hA.isAffineAlgebraicSpaceOver

end AlgebraicGeometry.Space

end
