module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.HomDescent
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesOverSpaceEssSurj
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.RepresentedPolarizedFunctor

/-!
# The functor `F^R` of Stacks 0E94 is faithful

Two isomorphisms `(f, φ), (g, ψ) : (X, L) ⟶ (X', L')` of polarized families of algebraic spaces
over `T` with the same image under `F^R` agree. Every point `s : W ⟶ X` of `X` factors through the
base change of `X` along the point `s ≫ (X ⟶ T)` of `T`, so `f = g`; and the inverse images of `φ`
and `ψ` along the base change `Z₀ ⟶ X` of an étale atlas `U₀ ⟶ T` agree, `Z₀ ⟶ X` is an étale
covering (Stacks 041F), and morphisms of modules are determined by their inverse images along an
étale covering, so `φ = ψ`.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.atlasPoint`: the point of `T` given by a scheme atlas.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.isEtaleCovering_fibreFst_atlasPoint`: the base change of
  the atlas is an étale covering.
* `AlgebraicGeometry.PolarizedOverSpace.baseChangeRepresentedFunctor_faithful`: `F^R` is faithful.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pseudofunctor.CoGrothendieck

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

variable {B : BigFppfSite.{u}} (T : AlgebraicSpaces B integerBase (hZ B))

/-- The scheme of a scheme atlas of `T`. -/
def atlasScheme : Site B := T.property.exists_atlas.choose

/-- A scheme atlas of `T`. -/
def atlasMap : yoneda.obj (atlasScheme T) ⟶ T.obj := T.property.exists_atlas.choose_spec.choose

/-- The point of `T` given by the atlas. -/
def atlasPoint : (Points T).obj :=
  SpacesOverSpace.pt (atlasScheme T) (yonedaEquiv (atlasMap T))

/-- The morphism of the atlas point of `T` is the atlas map `atlasMap T`. -/
theorem pointMap_atlasPoint : (SpacesOverSpace.pointMap (atlasPoint T)).hom = atlasMap T :=
  SpacesOverSpace.pointMap_pt_yonedaEquiv _

/-- The atlas is an étale covering of `T` (Stacks 041E). -/
theorem isEtaleCovering_atlasPoint :
    Space.IsEtaleCovering B integerBase (hZ B) (fun _ : PUnit.{1} => yoneda.obj (atlasScheme T))
      (fun _ => (SpacesOverSpace.pointMap (atlasPoint T)).hom) := by
  rw [pointMap_atlasPoint]
  exact Space.isEtaleCovering_atlas B integerBase (hZ B) T.property
    T.property.exists_atlas.choose_spec.choose_spec.1
    T.property.exists_atlas.choose_spec.choose_spec.2

variable {T}

/-- **The base change of the atlas along `X ⟶ T` is an étale covering of `X`** (Stacks 041F). -/
theorem isEtaleCovering_fibreFst_atlasPoint (ξ : PolarizedSpacesOver B T) :
    Space.IsEtaleCovering B integerBase (hZ B)
      (fun _ : Unit => yoneda.obj (fibreScheme ξ (atlasPoint T)))
      (fun _ => fibreFst ξ (atlasPoint T)) := by
  have h₁ := Space.isEtaleCovering_pullback B integerBase (hZ B) (familyMap ξ).hom
    ((familyPair B T).obj ξ).base.property _ _ (isEtaleCovering_atlasPoint T)
  have h₂ := Space.isEtaleCovering_comp B integerBase (hZ B) (fun _ : PUnit.{1} => Unit) _ _ _
    (fun _ _ => (isPullback_fibre ξ (atlasPoint T)).isoPullback.hom) h₁
    (fun _ => Space.isEtaleCovering_of_isIso B integerBase (hZ B) _
      (h₁.source_isAlgebraicSpace PUnit.unit))
  have h₃ := Space.IsEtaleCovering.reindex B integerBase (hZ B) h₂
    (σ := fun _ : Unit => (⟨PUnit.unit, ()⟩ : Σ _ : PUnit.{1}, Unit))
    (fun x => ⟨(), by obtain ⟨⟨⟩, ⟨⟩⟩ := x; rfl⟩)
  have e : (fun _ : Unit => (isPullback_fibre ξ (atlasPoint T)).isoPullback.hom ≫
      pullback.fst (familyMap ξ).hom (SpacesOverSpace.pointMap (atlasPoint T)).hom) =
      fun _ => fibreFst ξ (atlasPoint T) :=
    funext fun _ => IsPullback.isoPullback_hom_fst _
  exact (congrArg (Space.IsEtaleCovering B integerBase (hZ B)
    (fun _ : Unit => yoneda.obj (fibreScheme ξ (atlasPoint T)))) e).mp h₃

/-- Morphisms of modules on the total space are determined by their inverse images on the base
change of the atlas. -/
theorem modulePullback_fibreFst_atlasPoint_injective (ξ : PolarizedSpacesOver B T)
    {M N : Space.Modules B integerBase (hZ B) ((familyPair B T).obj ξ).base.obj
      ((familyPair B T).obj ξ).base.property} (φ ψ : M ⟶ N)
    (h : (Space.modulePullback B integerBase (hZ B)
        (ObjectProperty.homMk (fibreFst ξ (atlasPoint T)) :
          schemeSpace (fibreScheme ξ (atlasPoint T)) ⟶ ((familyPair B T).obj ξ).base)).map φ =
      (Space.modulePullback B integerBase (hZ B)
        (ObjectProperty.homMk (fibreFst ξ (atlasPoint T)) :
          schemeSpace (fibreScheme ξ (atlasPoint T)) ⟶ ((familyPair B T).obj ξ).base)).map ψ) :
    φ = ψ :=
  Space.QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B integerBase (hZ B)
    (fun _ : Unit => schemeSpace (fibreScheme ξ (atlasPoint T)))
    (fun _ => ObjectProperty.homMk (fibreFst ξ (atlasPoint T)))
    (isEtaleCovering_fibreFst_atlasPoint ξ) φ ψ (fun _ => h)

/-- The components of `F^R` on a morphism. -/
theorem baseChangeRepresentedFunctor_map_app_hom_hom {ξ ξ' : PolarizedSpacesOver B T}
    (e : ξ ⟶ ξ') (a : (Points T).obj) :
    (((baseChangeRepresentedFunctor B T).map e).app a).hom.hom =
      fibreInverseImage.map ((fibreCommaNatTrans e).app a) :=
  rfl

section Faithful

-- Elaboration compares the inverse images of the pseudofunctor with the functors themselves
-- without unfolding the latter.
attribute [local irreducible] Space.modulePullback Space.modulePullbackCompIso

/-- The functor `familyPair B T` is faithful. -/
instance familyPair_faithful : (familyPair B T).Faithful :=
  inferInstanceAs (Core.inclusion _ ⋙ ObjectProperty.ι _ ⋙
    forgetComp (Space.modulesPseudofunctor B integerBase (hZ B)) (familyFunctor B T)).Faithful

variable {ξ ξ' : PolarizedSpacesOver B T}

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The inverse image of the pseudofunctor of modules along a morphism is the inverse image of
Stacks 03LU, as functors. -/
theorem modulesPseudofunctor_map_toFunctor {X Y : AlgebraicSpaces B integerBase (hZ B)}
    (f : X ⟶ Y) :
    ((Space.modulesPseudofunctor B integerBase (hZ B)).map f.op.toLoc).toFunctor =
      Space.modulePullback B integerBase (hZ B) f :=
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Morphism form of `modulesPseudofunctor_map_toFunctor`. -/
theorem modulesPseudofunctor_map_map {X Y : AlgebraicSpaces B integerBase (hZ B)} (f : X ⟶ Y)
    {M N : Space.Modules B integerBase (hZ B) Y.1 Y.2} (x : M ⟶ N) :
    ((Space.modulesPseudofunctor B integerBase (hZ B)).map f.op.toLoc).toFunctor.map x =
      (Space.modulePullback B integerBase (hZ B) f).map x :=
  (Functor.congr_hom (modulesPseudofunctor_map_toFunctor f) x).trans
    (_root_.CategoryTheory.eqToHom_self_comp_comp_eqToHom_self _ _ _)

/-- The section of the base change of `X` along the point of `T` under a point of `X`. -/
def fibreSection {W : Site B} (s : yoneda.obj W ⟶ ((familyPair B T).obj ξ).base.obj) :
    W ⟶ fibreScheme ξ (SpacesOverSpace.pt W (yonedaEquiv (s ≫ (familyMap ξ).hom))) :=
  (relativelyRepresentable_familyMap ξ).lift s (𝟙 W) (by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, SpacesOverSpace.pointMap_pt_yonedaEquiv])

/-- The section `fibreSection s` followed by the projection `fibreFst` is `s`. -/
theorem fibreSection_fst {W : Site B} (s : yoneda.obj W ⟶ ((familyPair B T).obj ξ).base.obj) :
    yoneda.map (fibreSection s) ≫ fibreFst ξ _ = s :=
  (relativelyRepresentable_familyMap ξ).lift_fst _ _ _

/-- Isomorphisms of polarized families with the same base changes have the same underlying
morphism of algebraic spaces. -/
theorem familyPair_map_base_eq_of_fibreHomMap {e₁ e₂ : ξ ⟶ ξ'}
    (h : ∀ a, fibreHomMap e₁ a = fibreHomMap e₂ a) :
    ((familyPair B T).map e₁).base = ((familyPair B T).map e₂).base := by
  apply ObjectProperty.hom_ext
  apply hom_ext_yoneda
  intro W s
  rw [← fibreSection_fst s, Category.assoc, Category.assoc, ← fibreHomMap_fst, ← fibreHomMap_fst,
    h]

variable {e₁ e₂ : ξ ⟶ ξ'}
  (h : (baseChangeRepresentedFunctor B T).map e₁ = (baseChangeRepresentedFunctor B T).map e₂)
include h

/-- Morphisms with the same image under `F^R` have the same inverse images on the base change
along every point of `T`. -/
theorem fibreInverseImage_map_eq_of_map_eq (a : (Points T).obj) :
    fibreInverseImage.map ((fibreCommaNatTrans e₁).app a) =
      fibreInverseImage.map ((fibreCommaNatTrans e₂).app a) :=
  (baseChangeRepresentedFunctor_map_app_hom_hom e₁ a).symm.trans
    ((congrArg (fun η => (η.app a).hom.hom) h).trans
      (baseChangeRepresentedFunctor_map_app_hom_hom e₂ a))

/-- Morphisms with the same image under `F^R` induce the same morphisms of base changes along
every point of `T`. -/
theorem fibreHomMap_eq_of_map_eq (a : (Points T).obj) : fibreHomMap e₁ a = fibreHomMap e₂ a :=
  congrArg (fun m => m.base.left) (fibreInverseImage_map_eq_of_map_eq h a)

/-- Morphisms with the same image under `F^R` have the same components of `fibreCommaNatTrans`
at the atlas point of `T`. -/
theorem fibreCommaNatTrans_app_atlasPoint_eq_of_map_eq :
    (fibreCommaNatTrans e₁).app (atlasPoint T) = (fibreCommaNatTrans e₂).app (atlasPoint T) :=
  inverseImage_map_injective (arrowSpace B) ((fibreCommaNatTrans e₁).app (atlasPoint T))
    ((fibreCommaNatTrans e₂).app (atlasPoint T))
    (congrArg (fun m => m.base) (fibreInverseImage_map_eq_of_map_eq h (atlasPoint T)))
    (familyPair_map_base_eq_of_fibreHomMap (fibreHomMap_eq_of_map_eq h))
    (fun φ ψ hφψ => modulePullback_fibreFst_atlasPoint_injective ξ φ ψ
      ((modulesPseudofunctor_map_map _ φ).symm.trans
        (hφψ.trans (modulesPseudofunctor_map_map _ ψ))))
    (fibreInverseImage_map_eq_of_map_eq h _)

omit h in
/-- **`F^R` is faithful.** -/
instance baseChangeRepresentedFunctor_faithful :
    (baseChangeRepresentedFunctor B T).Faithful where
  map_injective h :=
    (familyPair B T).map_injective
      (congrArg CommaMorphism.right (fibreCommaNatTrans_app_atlasPoint_eq_of_map_eq h))

end Faithful

end AlgebraicGeometry.PolarizedOverSpace

end
