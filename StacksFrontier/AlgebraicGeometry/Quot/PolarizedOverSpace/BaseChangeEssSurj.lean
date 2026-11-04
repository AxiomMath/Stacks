module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.GluePolarization
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeFullDescent
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.InverseImageComparison
public import StacksFrontier.CategoryTheory.Bicategory.CoGrothendieckInverseImageLift

/-!
# Essential surjectivity of the base-change functor `F^R` of Stacks 0E94

Let `G` be a functor over the site from the points of `T` to
`AlgebraicGeometry.PolarizedOverSpace.RepresentedPolarized`, and let `ξ = (X ⟶ T, L)` be the
polarized family glued from it (`AlgebraicGeometry.PolarizedOverSpace.gluePolarized`: `X` from
Stacks 0E93, `L` by Stacks 04W8). Then `F^R(ξ) ≅ G`.

At a point `a` of `T`, the family `Z_a` of `G` maps to the chosen base change `U ×_T X` of `X`
(both are fibre products), and `σ_a : M_a ≅ s_a^* L`
(`AlgebraicGeometry.PolarizedOverSpace.glueSigma`) identifies the module of `G` with the inverse
image of `L`. Written in the Grothendieck construction, `σ` is a natural isomorphism of `G` with
the functor `a ↦ (Z_a, s_a^* L)` (its naturality is the naturality of `σ`), and the maps
`Z_a ⟶ U ×_T X` form a natural transformation of the triples `(Z_a, (X, L), s_a)` to the triples
`(U ×_T X, (X, L), q_a)` of `F^R(ξ)`, whose inverse images are isomorphisms. Their composite is the
isomorphism `G ≅ F^R(ξ)`.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.isIso_of_isIso_hom_hom`: a morphism of
  `RepresentedPolarized` with invertible underlying morphism is invertible.
* `AlgebraicGeometry.PolarizedOverSpace.glueFibreLift`, `isIso_glueFibreLift`: the isomorphism of
  the family of `G` at a point with the base change of the glued space there.
* `AlgebraicGeometry.PolarizedOverSpace.glueArrowNatTrans`: these isomorphisms, naturally in the
  point, as morphisms of arrows.
* `AlgebraicGeometry.PolarizedOverSpace.modulesPseudofunctor_square_of_heq`: a naturality square
  of modules read in the pseudofunctor of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pseudofunctor.CoGrothendieck

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso

-- The morphisms of the Grothendieck construction carry the quiver of `CategoryStruct`.
attribute [-instance] CategoryTheory.catToReflQuiver

variable {B : BigFppfSite.{u}}

section IsoCriterion

/-- A morphism of a wide subcategory whose underlying morphism is invertible, with inverse in the
subcategory, is invertible. -/
theorem _root_.CategoryTheory.WideSubcategory.isIso_of_isIso_hom {C : Type*} [Category C]
    {P : MorphismProperty C} [P.IsMultiplicative] {X Y : WideSubcategory P} (f : X ⟶ Y)
    [IsIso f.hom] (h : P (inv f.hom)) : IsIso f :=
  ⟨⟨⟨inv f.hom, h⟩, WideSubcategory.hom_ext _ (IsIso.hom_inv_id f.hom),
    WideSubcategory.hom_ext _ (IsIso.inv_hom_id f.hom)⟩⟩

/-- **An isomorphism of the Grothendieck construction between polarized families is a morphism of
`RepresentedPolarized`**: its square of schemes has invertible horizontal sides and its
comparison of modules is invertible. -/
theorem cartesianIso_of_isIso {X Y : RepresentedPolarizedObj B} (f : X ⟶ Y) [IsIso f.hom] :
    cartesianIso B f := by
  have : IsIso f.hom.base :=
    Functor.map_isIso (Pseudofunctor.CoGrothendieck.forget (arrowModules B)) f.hom
  have : IsIso f.hom.base.left := Functor.map_isIso Arrow.leftFunc f.hom.base
  have : IsIso f.hom.base.right := Functor.map_isIso Arrow.rightFunc f.hom.base
  have : IsIso (sch B f.hom.base.left) := Functor.map_isIso _ _
  have : IsIso (sch B f.hom.base.right) := Functor.map_isIso _ _
  refine ⟨IsPullback.of_horiz_isIso ⟨?_⟩, isIso_fiber_of_isIso f.hom⟩
  rw [← Functor.map_comp, ← Functor.map_comp, Arrow.w]

/-- A morphism of `RepresentedPolarized` whose underlying morphism of the Grothendieck
construction is invertible is invertible. -/
theorem isIso_of_isIso_hom_hom {X Y : RepresentedPolarized B} (f : X ⟶ Y) (hf : IsIso f.hom.hom) :
    IsIso f := by
  have : IsIso ((ObjectProperty.ι (IsRepresentedPolarized B)).map f.hom) := hf
  have : IsIso f.hom := isIso_of_fully_faithful (ObjectProperty.ι _) _
  have : IsIso (inv f.hom).hom := Functor.map_isIso (ObjectProperty.ι _) (inv f.hom)
  exact WideSubcategory.isIso_of_isIso_hom f (cartesianIso_of_isIso (inv f.hom))

/-- An equation `α ≪≫ F.mapIso i ≪≫ γ⁻¹ = δ` of isomorphisms, read on morphisms:
`α ≫ F.map i = δ ≫ γ`. -/
theorem _root_.CategoryTheory.Iso.hom_comp_map_hom_eq_of_trans_mapIso_trans_symm_eq {C D : Type*}
    [Category C] [Category D] (F : C ⥤ D) {A A' : C} {W Z : D} (α : W ≅ F.obj A) (i : A ≅ A')
    (γ : Z ≅ F.obj A') (δ : W ≅ Z) (h : α ≪≫ F.mapIso i ≪≫ γ.symm = δ) :
    α.hom ≫ F.map i.hom = δ.hom ≫ γ.hom := by
  subst h
  simp

end IsoCriterion

variable {T : AlgebraicSpaces B integerBase (hZ B)}
  (G : Points T ⥤ᵇ BasedCategory.ofFunctor (representedPolarizedProjection B))

section Arrows

/-- The squares of `G` over the morphisms of points lie over them. -/
theorem glue_base_right_comp {a' a : (Points T).obj} (u : a' ⟶ a) :
    (G.map u).hom.hom.base.right ≫ eqToHom (SpacesOverSpace.fam_right (glueFamilies G) a) =
      eqToHom (SpacesOverSpace.fam_right (glueFamilies G) a') ≫ u.base := by
  have h1 : (Points T).p.IsHomLift u.base u := IsHomLift.map (p := (Points T).p) u
  have h2 : (representedPolarizedProjection B).IsHomLift u.base (G.map u) :=
    BasedFunctor.preserves_isHomLift G u.base u
  have h := IsHomLift.fac' (representedPolarizedProjection B) u.base (G.map u)
  change (G.map u).hom.hom.base.right = _ at h
  have key : ∀ {X X' Y Y' : Site B} (f : X ⟶ Y) (e₁ : X' = X) (e₂ : Y = Y') (e₃ : Y' = Y)
      (e₄ : X' = X), (eqToHom e₁ ≫ f ≫ eqToHom e₂) ≫ eqToHom e₃ = eqToHom e₄ ≫ f := by
    intro X X' Y Y' f e₁ e₂ e₃ e₄
    subst e₁ e₂
    simp
  exact (congrArg (· ≫ eqToHom _) h).trans (key _ _ _ _ _)

/-- **The family of `G` at a point maps to the base change of the glued space there**, both
being fibre products of `X ⟶ T` with the point. -/
def glueFibreLift (a : (Points T).obj) :
    (G.obj a).obj.obj.base.left ⟶ fibreScheme (gluePolarized G) a :=
  (relativelyRepresentable_familyMap (gluePolarized G)).lift
    (SpacesOverSpace.famToGlue (glueFamilies G) a)
    ((G.obj a).obj.obj.base.hom ≫ eqToHom (SpacesOverSpace.fam_right (glueFamilies G) a))
    ((SpacesOverSpace.famToGlue_comp_glueToBase (glueFamilies G) a).trans
      (congrArg (· ≫ (SpacesOverSpace.pointMap a).hom) (Functor.map_comp yoneda _ _).symm))

/-- Composing `glueFibreLift` with the first projection of the fibre gives `famToGlue`. -/
theorem glueFibreLift_fst (a : (Points T).obj) :
    yoneda.map (glueFibreLift G a) ≫ fibreFst (gluePolarized G) a =
      SpacesOverSpace.famToGlue (glueFamilies G) a :=
  (relativelyRepresentable_familyMap (gluePolarized G)).lift_fst _ _ _

/-- Composing `glueFibreLift` with the projection of the fibre to the point gives the structure
map of the family of `G` at that point. -/
theorem glueFibreLift_proj (a : (Points T).obj) :
    glueFibreLift G a ≫ fibreProj (gluePolarized G) a =
      (G.obj a).obj.obj.base.hom ≫ eqToHom (SpacesOverSpace.fam_right (glueFamilies G) a) :=
  (relativelyRepresentable_familyMap (gluePolarized G)).lift_snd _ _ _

/-- The map of the family of `G` to the base change is an isomorphism: both are fibre products. -/
instance isIso_glueFibreLift (a : (Points T).obj) : IsIso (glueFibreLift G a) := by
  have sq : IsPullback (SpacesOverSpace.famToGlue (glueFamilies G) a)
      (yoneda.map ((G.obj a).obj.obj.base.hom ≫
        eqToHom (SpacesOverSpace.fam_right (glueFamilies G) a)))
      (familyMap (gluePolarized G)).hom (SpacesOverSpace.pointMap a).hom := by
    rw [Functor.map_comp]
    exact (SpacesOverSpace.isPullback_famToGlue (glueFamilies G) a).flip
  have e : yoneda.map (glueFibreLift G a) =
      (IsPullback.isoIsPullback _ _ sq (isPullback_fibre (gluePolarized G) a)).hom :=
    (isPullback_fibre (gluePolarized G) a).hom_ext
      ((glueFibreLift_fst G a).trans (IsPullback.isoIsPullback_hom_fst _ _ _ _).symm)
      (((Functor.map_comp yoneda _ _).symm.trans
          (congrArg yoneda.map (glueFibreLift_proj G a))).trans
        (IsPullback.isoIsPullback_hom_snd _ _ _ _).symm)
  haveI : IsIso (yoneda.map (glueFibreLift G a)) := by rw [e]; exact Iso.isIso_hom _
  exact isIso_of_fully_faithful yoneda _

/-- The functor `G`, read in the Grothendieck construction of the modules on the arrows. -/
abbrev glueInclusion : (Points T).obj ⥤ Pseudofunctor.CoGrothendieck (arrowModules B) :=
  G.toFunctor ⋙ wideSubcategoryInclusion _ ⋙ ObjectProperty.ι _

/-- The arrows of the families of `G`. -/
abbrev glueArrowFunctor : (Points T).obj ⥤ Arrow (Site B) :=
  glueInclusion G ⋙ Pseudofunctor.CoGrothendieck.forget (arrowModules B)

/-- The morphism of arrows from the family of `G` at a point to the base change of `X`. -/
def glueArrowHom (a : (Points T).obj) :
    @Quiver.Hom (Arrow (Site B)) CategoryStruct.toQuiver ((glueArrowFunctor G).obj a)
      (fibreArrow (gluePolarized G) a) :=
  Arrow.homMk (glueFibreLift G a) (eqToHom (SpacesOverSpace.fam_right (glueFamilies G) a))
    (glueFibreLift_proj G a)

/-- The morphisms of arrows to the base changes, naturally in the point. -/
def glueArrowNatTrans : glueArrowFunctor G ⟶ fibreArrowFunctor (gluePolarized G) where
  app := glueArrowHom G
  naturality a' a u := by
    have hw := Arrow.w (G.map u).hom.hom.base
    refine Arrow.hom_ext _ _ (fibre_hom_ext (gluePolarized G) ?_ ?_) (glue_base_right_comp G u)
    · change yoneda.map ((G.map u).hom.hom.base.left ≫ glueFibreLift G a) ≫ _ =
        yoneda.map (glueFibreLift G a' ≫ fibreMap (gluePolarized G) u) ≫ _
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, glueFibreLift_fst,
        fibreMap_fst, glueFibreLift_fst]
      exact SpacesOverSpace.famMap_comp_famToGlue (glueFamilies G) u
    · change ((G.map u).hom.hom.base.left ≫ glueFibreLift G a) ≫ _ =
        (glueFibreLift G a' ≫ fibreMap (gluePolarized G) u) ≫ _
      rw [Category.assoc, Category.assoc, glueFibreLift_proj, fibreMap_proj,
        ← Category.assoc (glueFibreLift G a'), glueFibreLift_proj, ← Category.assoc, hw,
        Category.assoc, Category.assoc, glue_base_right_comp G u]
      exact (Category.assoc _ _ _).symm

end Arrows

section Comparison

/-- The triples `(Z_a ⟶ U, (X, L), s_a)` of the families of `G` over the glued polarized
family. -/
abbrev glueComma : (Points T).obj ⥤
    Comma (arrowSpace B) (forget (Space.modulesPseudofunctor B integerBase (hZ B))) :=
  liftConstComma (glueInclusion G) ((familyPair B T).obj (gluePolarized G)) (chartMap G)
    (chartHom_comp_chartMap G)

/-- The comparison of iterated inverse images only depends on its data up to equality: equal
spellings of the spaces, morphisms and module give the same comparison. -/
theorem _root_.AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison_hom_heq
    {S : Scheme.{u}} {hS : B.Contains S} {X Y Z X' Y' Z' : AlgebraicSpaces B S hS}
    (hX : X = X') (hY : Y = Y') (hZZ : Z = Z') {q : Z ⟶ Y} {f : Y ⟶ X} {k : Z ⟶ X}
    {q' : Z' ⟶ Y'} {f' : Y' ⟶ X'} {k' : Z' ⟶ X'} (hq : HEq q q') (hf : HEq f f') (hk : HEq k k')
    (hqk : q ≫ f = k) (hqk' : q' ≫ f' = k') {N : Space.Modules.{u, u} B S hS X.1 X.2}
    {N' : Space.Modules.{u, u} B S hS X'.1 X'.2} (hN : HEq N N') :
    HEq (Space.QuasiCoherentDescent.pullbackComparison B S hS q f k hqk N).hom
      (Space.QuasiCoherentDescent.pullbackComparison B S hS q' f' k' hqk' N').hom := by
  subst hX hY hZZ
  cases hq
  cases hf
  cases hk
  cases hN
  rfl

/-- **Transfer of a naturality square from the module language to the pseudofunctor of
modules**, with every datum given twice (the two spellings linked by equalities): the square
`κ ≫ q^*σ_Y = σ_Z ≫ c` with `c` the comparison of iterated inverse images (Stacks 03LU) is the
square with the inverse image and the comparison of the pseudofunctor. -/
theorem modulesPseudofunctor_square_of_heq
    {X Y Z X' Y' Z' : AlgebraicSpaces B integerBase (hZ B)} (hX : X = X') (hY : Y = Y')
    (hZZ : Z = Z') (q : Z ⟶ Y) (f : Y ⟶ X) (k : Z ⟶ X) (hk : q ≫ f = k)
    (hF : f.op.toLoc ≫ q.op.toLoc = k.op.toLoc) (q' : Z' ⟶ Y') (f' : Y' ⟶ X') (k' : Z' ⟶ X')
    (hk' : q' ≫ f' = k') (hq : HEq q q') (hf : HEq f f') (hkk : HEq k k')
    (L : Space.Modules.{u, u} B integerBase (hZ B) X.1 X.2)
    (L' : Space.Modules.{u, u} B integerBase (hZ B) X'.1 X'.2)
    (hL : HEq L L') (MY : Space.Modules.{u, u} B integerBase (hZ B) Y.1 Y.2)
    (MY' : Space.Modules.{u, u} B integerBase (hZ B) Y'.1 Y'.2) (hMY : HEq MY MY')
    (MZ : Space.Modules.{u, u} B integerBase (hZ B) Z.1 Z.2)
    (MZ' : Space.Modules.{u, u} B integerBase (hZ B) Z'.1 Z'.2)
    (hMZ : HEq MZ MZ') (σY : MY ⟶ (Space.modulePullback B integerBase (hZ B) f).obj L)
    (σY' : MY' ⟶ (Space.modulePullback B integerBase (hZ B) f').obj L') (hσY : HEq σY σY')
    (σZ : MZ ⟶ (Space.modulePullback B integerBase (hZ B) k).obj L)
    (σZ' : MZ' ⟶ (Space.modulePullback B integerBase (hZ B) k').obj L') (hσZ : HEq σZ σZ')
    (κ : MZ ⟶ (Space.modulePullback B integerBase (hZ B) q).obj MY)
    (κ' : MZ' ⟶ (Space.modulePullback B integerBase (hZ B) q').obj MY') (hκ : HEq κ κ')
    (h : κ' ≫ (Space.modulePullback B integerBase (hZ B) q').map σY' =
      σZ' ≫
        (Space.QuasiCoherentDescent.pullbackComparison B integerBase (hZ B) q' f' k' hk' L').hom) :
    κ ≫ ((Space.modulesPseudofunctor B integerBase (hZ B)).map q.op.toLoc).toFunctor.map σY =
      σZ ≫ ((Space.modulesPseudofunctor B integerBase (hZ B)).mapComp' f.op.toLoc q.op.toLoc
        k.op.toLoc hF).hom.toNatTrans.app L := by
  subst hX hY hZZ
  cases hq
  cases hf
  cases hkk
  cases hL
  cases hMY
  cases hMZ
  cases hσY
  cases hσZ
  cases hκ
  exact (congrArg (κ ≫ ·) (modulesPseudofunctor_map_map q σY)).trans (h.trans
    (congrArg (σZ ≫ ·) (Space.modulesPseudofunctor_mapComp'_hom_app q f k hk hF L).symm))

end Comparison

end AlgebraicGeometry.PolarizedOverSpace

end
