module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Sheafify
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The relative morphism functor is relatively limit preserving

Let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over a scheme `S` of a big fppf
site, with `z` of finite presentation and `x` locally of finite presentation. The projection
`Mor_Q(Z, X) ⟶ Q` of the relative morphism functor of Stacks 05Y2 is then relatively limit
preserving in the sense of Stacks 049J, and hence locally of finite presentation by Stacks 04AK.
This is the half "locally of finite presentation over the base" of Stacks 0D1C, and the second
clause of Stacks 0DPN; it is proved here without the algebraicity of `Mor_Q(Z, X)`.

## Main definitions

* `AlgebraicGeometry.Space.homFromBaseChange`: for `π : Y ⟶ h_A` and `g : Y ⟶ Q`, the presheaf on
  the objects over `A` sending `V` to the morphisms `Y ×_A V ⟶ X` over `Q`.
* `AlgebraicGeometry.Space.homFromBaseChangePrecomp`: precomposition with a morphism over `A`.

## Main results

* `AlgebraicGeometry.limitPreserving_overPullback_comp`: limit preservation is carried along
  base change between affine objects.
* `AlgebraicGeometry.Space.limitPreserving_homFromBaseChange_yoneda`: the case `Y = h_U` with `U`
  affine, which is the relative limit preservation of `x` read on the base changes of `U`.
* `AlgebraicGeometry.Space.limitPreserving_homFromBaseChange`: the case of `Y ⟶ h_A` of finite
  presentation over an affine `A`, through an affine étale atlas of `Y` and an affine étale atlas
  of its self-intersection.
* `AlgebraicGeometry.Space.relativelyLimitPreserving_relativeHomProjection`: the projection
  `Mor_Q(Z, X) ⟶ Q` is relatively limit preserving.
* `Space.isLocallyOfFinitePresentation_relativeHomProjection_of_isFinitePresentation`:
  the projection is locally of finite presentation.

## Implementation notes

The source deduces local finite presentation of `Mor_Q(Z, X) ⟶ Q` from the open immersion into
the Hilbert functor of `Z ×_Q X` (Stacks 0D1B) and the algebraicity of that Hilbert functor
(Stacks 0D01, through Stacks 09TU). Here it is instead read off the functor of points: over a
cofiltered limit `T = lim T_i` of affine schemes, a morphism `Z_T ⟶ X` over `Q` is restricted to
an affine étale atlas `U` of a stage `Z_{T_i}`, where it is a point of `X` over the affine scheme
`U ×_{T_i} T`; the relative limit preservation of `x` (Stacks 04AK, (1) ⟹ (2)) descends it to a
stage, and the kernel pair of the atlas, which is quasi-compact because `z` is quasi-separated,
is handled the same way through an affine étale atlas of it. Formally this is the presentation
of `Hom(Z_V, X)` as the equalizer of `Hom(U_V, X) ⇉ Hom(R_V, X)`, and
`AlgebraicGeometry.limitPreserving_of_isEqualizer` concludes. Stacks 04AK in the direction
(2) ⟹ (1) needs no algebraicity of the source, so local finite presentation follows.

The values of `AlgebraicGeometry.Space.homFromBaseChange` are morphisms of presheaves, one
universe above the sections of an algebraic space; limit preservation is insensitive to that, and
the comparison with section fibres goes through `CategoryTheory.uliftFunctor`.

## References

* [Stacks Project, Tag 0DPN](https://stacks.math.columbia.edu/tag/0DPN)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w' z z'

namespace AlgebraicGeometry

/-! ### Base change of a limit cone of objects over an affine object -/

section OverPullback

variable {C : Type z} [Category.{z'} C] [HasPullbacks C]
  (T : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan T]

/-- Base changing a cofiltered cone of objects over `A` along `u : U ⟶ A` gives a limit cone of
underlying schemes when the original cone is one. -/
def isLimitMapConeOverPullback {I : Type w} [Category.{w'} I] [IsCofiltered I]
    {A U : C} (u : U ⟶ A) (D : I ⥤ Over A) (c : Cone D)
    (hc : IsLimit ((Over.forget A ⋙ T).mapCone c)) :
    IsLimit ((Over.forget U ⋙ T).mapCone ((Over.pullback u).mapCone c)) := by
  letI : IsConnected I := IsCofiltered.isConnected I
  let α : D ⋙ Over.pullback u ⋙ Over.forget U ⋙ T ⟶ D ⋙ Over.forget A ⋙ T :=
    { app := fun j => T.map (pullback.fst (D.obj j).hom u)
      naturality := by
        intro j k g
        simp only [Functor.comp_obj, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
          ← T.map_comp, pullback.lift_fst] }
  let f : (Cone.postcompose α).obj ((Over.forget U ⋙ T).mapCone ((Over.pullback u).mapCone c)) ⟶
      (Over.forget A ⋙ T).mapCone c :=
    { hom := T.map (pullback.fst c.pt.hom u)
      w := by
        intro j
        simp only [Functor.comp_obj, Cone.postcompose_obj_pt, Functor.mapCone_pt,
          Over.forget_obj, Over.pullback_obj_left, Cone.postcompose_obj_π, NatTrans.comp_app,
          Functor.mapCone_π_app, Functor.comp_map, Over.forget_map, Over.pullback_map_left,
          α, ← T.map_comp, pullback.lift_fst] }
  refine isLimitOfIsPullbackOfIsConnected α _ _ f (fun j => ?_) hc
  exact (isPullback_pullback_map u (c.π.app j)).map T

/-- **Limit preservation along base change of affine objects.** If `F` is limit preserving on the
objects over an affine object `U`, and `u : U ⟶ A` is a morphism to an affine object, then the
presheaf `V ↦ F(V ×_A U)` on the objects over `A` is limit preserving. -/
theorem limitPreserving_overPullback_comp {A U : C} (u : U ⟶ A)
    (hA : IsAffine (T.obj A)) (hU : IsAffine (T.obj U)) (F : (Over U)ᵒᵖ ⥤ Type v)
    (hF : LimitPreserving.{u, v, w, w'} (Over.forget U ⋙ T) F) :
    LimitPreserving.{u, v, w, w'} (Over.forget A ⋙ T) ((Over.pullback u).op ⋙ F) := by
  intro I _ _ D c hc hD hC
  have : IsAffine (T.obj A) := hA
  have : IsAffine (T.obj U) := hU
  have hD' : ∀ i, IsAffine ((Over.forget U ⋙ T).obj ((D ⋙ Over.pullback u).obj i)) := fun i => by
    have : IsAffine (T.obj (D.obj i).left) := hD i
    exact isAffine_obj_pullback T (D.obj i).hom u
  have hC' : IsAffine ((Over.forget U ⋙ T).obj ((Over.pullback u).mapCone c).pt) := by
    have : IsAffine (T.obj c.pt.left) := hC
    exact isAffine_obj_pullback T c.pt.hom u
  exact hF I (D ⋙ Over.pullback u) ((Over.pullback u).mapCone c)
    (isLimitMapConeOverPullback T u D c hc) hD' hC'

end OverPullback

/-! ### Reduction to an affine base -/

section AffineBase

variable {C : Type z} [Category.{z'} C] (T : C ⥤ Scheme.{u})

/-- **Limit preservation over an object reduces to limit preservation over affine objects.** A
presheaf `F` on the objects over `T₀` is limit preserving as soon as, for every affine `A` with a
morphism `α : A ⟶ T₀`, its restriction along `Over.map α` is: a cofiltered system of affines over
`T₀` lies, from any of its stages `i₀` on, over the affine object `D(i₀)`. -/
theorem limitPreserving_of_overMap {T₀ : C} (F : (Over T₀)ᵒᵖ ⥤ Type v)
    (h : ∀ (A : C) (α : A ⟶ T₀), IsAffine (T.obj A) →
      LimitPreserving.{u, v, w, w'} (Over.forget A ⋙ T) ((Over.map α).op ⋙ F)) :
    LimitPreserving.{u, v, w, w'} (Over.forget T₀ ⋙ T) F := by
  intro I _ _ D c hc hD hC
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  let A := (D.obj i₀).left
  let α : A ⟶ T₀ := (D.obj i₀).hom
  let D' : Over i₀ ⥤ Over A := Over.post D ⋙ Over.iteratedSliceForward (D.obj i₀)
  let c' : Cone D' := (Over.iteratedSliceForward (D.obj i₀)).mapCone (c.overPost i₀)
  have hc' : IsLimit ((Over.forget A ⋙ T).mapCone c') :=
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i₀) _).symm hc).ofIsoLimit
      (Cone.ext (Iso.refl _) (fun j => (Category.id_comp _).symm))
  have hD' : ∀ j, IsAffine ((Over.forget A ⋙ T).obj (D'.obj j)) := fun j => hD j.left
  have hC' : IsAffine ((Over.forget A ⋙ T).obj c'.pt) := hC
  obtain ⟨hcol⟩ := h A α (hD i₀) (Over i₀) D' c' hc' hD' hC'
  let isoj (j : Over i₀) : (Over.map α).obj (D'.obj j) ≅ D.obj j.left :=
    Over.isoMk (Iso.refl _) (
      (Category.id_comp _).trans (Over.w (D.map j.hom)).symm)
  let isoc : (Over.map α).obj c'.pt ≅ c.pt :=
    Over.isoMk (Iso.refl _) (
      (Category.id_comp _).trans (Over.w (c.π.app i₀)).symm)
  have hπ (j : Over i₀) : (Over.map α).map (c'.π.app j) ≫ (isoj j).hom =
      isoc.hom ≫ c.π.app j.left := by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hmap {j j' : Over i₀} (g : j' ⟶ j) : (Over.map α).map (D'.map g) ≫ (isoj j).hom =
      (isoj j').hom ≫ D.map g.left := by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  have hcomp : ∀ {W₁ W₂ W₃ : Over T₀} (a : W₁ ⟶ W₂) (b : W₂ ⟶ W₃) (z : F.obj (op W₃)),
      F.map a.op (F.map b.op z) = F.map (a ≫ b).op z := fun a b z => by
    rw [op_comp, Functor.map_comp_apply]
  refine isColimit_mapCocone_of_exists_of_eventually_eq F D c ?_ ?_
  · intro x₀
    obtain ⟨j, y', hy'⟩ := Types.jointly_surjective_of_isColimit hcol (F.map isoc.hom.op x₀)
    refine ⟨j.unop.left, F.map (isoj j.unop).inv.op y', ?_⟩
    have hy'' : F.map ((Over.map α).map (c'.π.app j.unop)).op y' = F.map isoc.hom.op x₀ := hy'
    have hinv : c.π.app j.unop.left ≫ (isoj j.unop).inv =
        isoc.inv ≫ (Over.map α).map (c'.π.app j.unop) := by
      rw [Iso.comp_inv_eq, Category.assoc, hπ, Iso.inv_hom_id_assoc]
    rw [hcomp, hinv, ← hcomp, hy'', hcomp, Iso.inv_hom_id]
    exact F.map_id_apply _ x₀
  · intro i x₁ x₂ hx
    let jk : Over i₀ := Over.mk (IsCofiltered.minToRight i i₀)
    let fk := IsCofiltered.minToLeft i i₀
    let z₁ := F.map (isoj jk).hom.op (F.map (D.map fk).op x₁)
    let z₂ := F.map (isoj jk).hom.op (F.map (D.map fk).op x₂)
    have hw : c.π.app jk.left ≫ D.map fk = c.π.app i := c.w fk
    have hpt : ∀ x : F.obj (op (D.obj i)), F.map ((Over.map α).map (c'.π.app jk)).op
        (F.map (isoj jk).hom.op (F.map (D.map fk).op x)) =
        F.map isoc.hom.op (F.map (c.π.app i).op x) := by
      intro x
      rw [hcomp, hcomp, hπ, Category.assoc, hw, ← hcomp]
    have hz : F.map ((Over.map α).map (c'.π.app jk)).op z₁ =
        F.map ((Over.map α).map (c'.π.app jk)).op z₂ := by
      simp only [z₁, z₂]
      rw [hpt, hpt, hx]
    obtain ⟨j', g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol z₁ z₂).mp hz
    have key : ∀ x : F.obj (op (D.obj i)), F.map ((Over.map α).map (D'.map g.unop)).op
        (F.map (isoj jk).hom.op (F.map (D.map fk).op x)) =
        F.map (isoj j'.unop).hom.op (F.map (D.map (g.unop.left ≫ fk)).op x) := by
      intro x
      rw [hcomp, hcomp, show (Over.map α).map (D'.map g.unop) ≫ (isoj jk).hom =
        (isoj j'.unop).hom ≫ D.map g.unop.left from hmap g.unop, Category.assoc,
        ← Functor.map_comp, ← hcomp]
    have hg' : F.map ((Over.map α).map (D'.map g.unop)).op z₁ =
        F.map ((Over.map α).map (D'.map g.unop)).op z₂ := hg
    simp only [z₁, z₂] at hg'
    rw [key, key] at hg'
    refine ⟨j'.unop.left, g.unop.left ≫ fk, ?_⟩
    have := congrArg (F.map (isoj j'.unop).inv.op) hg'
    rw [hcomp, hcomp, Iso.inv_hom_id, Category.id_comp, hcomp, hcomp, Iso.inv_hom_id,
      Category.id_comp] at this
    exact this

end AffineBase

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0 (it explores `GradedObject` instances first); supply the functor-category instance. -/
local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

local instance (priority := high) {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : Y ≅ Z) :
    Epi e.hom :=
  IsIso.epi_of_iso _

local instance (priority := high) {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : Y ≅ Z) :
    Epi e.inv :=
  IsIso.epi_of_iso _

/-! ### Morphisms out of base changes -/

section HomFromBaseChange

variable {X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X ⟶ Q) {A : BigFppfOver B S hS}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The comparison of the base changes of `π : Y ⟶ h_A` along a morphism of objects over `A`. -/
def baseChangeRestrictionMap (π : Y ⟶ yoneda.obj A) {V V' : Over A} (f : V' ⟶ V) :
    pullback (yoneda.map V'.hom) π ⟶ pullback (yoneda.map V.hom) π :=
  pullback.map _ _ _ _ (yoneda.map f.left) (𝟙 Y) (𝟙 _)
    (by rw [Category.comp_id, ← Functor.map_comp, Over.w f]) (by simp)

/-- The comparison of base changes along `f : V' ⟶ V` commutes with the projections to `h_V'` and
`h_V`. -/
@[reassoc (attr := simp)]
theorem baseChangeRestrictionMap_fst (π : Y ⟶ yoneda.obj A) {V V' : Over A} (f : V' ⟶ V) :
    baseChangeRestrictionMap π f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ yoneda.map f.left := by
  simp [baseChangeRestrictionMap]

/-- The comparison of base changes commutes with the projections to `Y`. -/
@[reassoc (attr := simp)]
theorem baseChangeRestrictionMap_snd (π : Y ⟶ yoneda.obj A) {V V' : Over A} (f : V' ⟶ V) :
    baseChangeRestrictionMap π f ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [baseChangeRestrictionMap]

/-- The comparison of base changes along the identity of `V` is the identity. -/
theorem baseChangeRestrictionMap_id (π : Y ⟶ yoneda.obj A) (V : Over A) :
    baseChangeRestrictionMap π (𝟙 V) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- The comparison of base changes along a composite is the composite of the comparisons. -/
theorem baseChangeRestrictionMap_comp (π : Y ⟶ yoneda.obj A) {V V' V'' : Over A} (f : V'' ⟶ V')
    (f' : V' ⟶ V) :
    baseChangeRestrictionMap π (f ≫ f') =
      baseChangeRestrictionMap π f ≫ baseChangeRestrictionMap π f' := by
  apply pullback.hom_ext <;> simp

/-- The morphisms `b : Y ×_A V ⟶ X` with `b ≫ x` the composite `Y ×_A V ⟶ Y ⟶ Q`. -/
abbrev HomFromBaseChangeAt (π : Y ⟶ yoneda.obj A) (g : Y ⟶ Q) (V : Over A) : Type (u + 1) :=
  {b : pullback (yoneda.map V.hom) π ⟶ X // b ≫ x = pullback.snd (yoneda.map V.hom) π ≫ g}

/-- **Morphisms out of the base changes of `Y` over `Q`.** For `π : Y ⟶ h_A` and `g : Y ⟶ Q`, the
presheaf on the objects over `A` whose value at `V` is the set of morphisms `b : Y ×_A V ⟶ X` with
`b ≫ x` the composite `Y ×_A V ⟶ Y ⟶ Q`, restriction being precomposition with the comparison
of base changes. -/
def homFromBaseChange (π : Y ⟶ yoneda.obj A) (g : Y ⟶ Q) : (Over A)ᵒᵖ ⥤ Type (u + 1) where
  obj V := HomFromBaseChangeAt x π g V.unop
  map {V V'} f := TypeCat.ofHom (fun (b : HomFromBaseChangeAt x π g V.unop) =>
    (⟨baseChangeRestrictionMap π f.unop ≫ b.1, by
      rw [Category.assoc, b.2, baseChangeRestrictionMap_snd_assoc]⟩ :
        HomFromBaseChangeAt x π g V'.unop))
  map_id V := by
    ext b : 3
    exact Subtype.ext ((congrArg (· ≫ b.1) (baseChangeRestrictionMap_id π V.unop)).trans
      (Category.id_comp _))
  map_comp {V V' V''} f f' := by
    ext b : 3
    exact Subtype.ext ((congrArg (· ≫ b.1) (baseChangeRestrictionMap_comp π f'.unop f.unop)).trans
      (Category.assoc _ _ _))

/-- Restriction in `homFromBaseChange` is precomposition with the comparison of base changes. -/
@[simp]
theorem homFromBaseChange_map_coe (π : Y ⟶ yoneda.obj A) (g : Y ⟶ Q) {V V' : (Over A)ᵒᵖ}
    (f : V ⟶ V') (b : (homFromBaseChange x π g).obj V) :
    ((homFromBaseChange x π g).map f b).1 = baseChangeRestrictionMap π f.unop ≫ b.1 :=
  rfl

/-- The map of base changes induced by a morphism `φ : Y' ⟶ Y` over `A`. -/
def baseChangePrecompMap {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : Y' ⟶ Y)
    (π : Y ⟶ yoneda.obj A) (π' : Y' ⟶ yoneda.obj A) (hπ : φ ≫ π = π') (V : Over A) :
    pullback (yoneda.map V.hom) π' ⟶ pullback (yoneda.map V.hom) π :=
  pullback.map _ _ _ _ (𝟙 _) φ (𝟙 _) (by simp) (by rw [Category.comp_id, hπ])

/-- The map of base changes induced by `φ` commutes with the projections to `h_V`. -/
@[reassoc (attr := simp)]
theorem baseChangePrecompMap_fst {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : Y' ⟶ Y)
    (π : Y ⟶ yoneda.obj A) (π' : Y' ⟶ yoneda.obj A) (hπ : φ ≫ π = π') (V : Over A) :
    baseChangePrecompMap φ π π' hπ V ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [baseChangePrecompMap]

/-- The map of base changes induced by `φ` lies over `φ`. -/
@[reassoc (attr := simp)]
theorem baseChangePrecompMap_snd {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : Y' ⟶ Y)
    (π : Y ⟶ yoneda.obj A) (π' : Y' ⟶ yoneda.obj A) (hπ : φ ≫ π = π') (V : Over A) :
    baseChangePrecompMap φ π π' hπ V ≫ pullback.snd _ _ = pullback.snd _ _ ≫ φ := by
  simp [baseChangePrecompMap]

/-- **Precomposition with a morphism over `A`.** A morphism `φ : Y' ⟶ Y` over `A` sends a morphism
`Y ×_A V ⟶ X` over `Q` to its composite with `Y' ×_A V ⟶ Y ×_A V`. -/
def homFromBaseChangePrecomp {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : Y' ⟶ Y)
    (π : Y ⟶ yoneda.obj A) (π' : Y' ⟶ yoneda.obj A) (hπ : φ ≫ π = π') (g : Y ⟶ Q)
    (g' : Y' ⟶ Q) (hg : φ ≫ g = g') :
    homFromBaseChange x π g ⟶ homFromBaseChange x π' g' where
  app V := TypeCat.ofHom (fun (b : HomFromBaseChangeAt x π g V.unop) =>
    (⟨baseChangePrecompMap φ π π' hπ V.unop ≫ b.1, by
      rw [Category.assoc, b.2, baseChangePrecompMap_snd_assoc, hg]⟩ :
        HomFromBaseChangeAt x π' g' V.unop))
  naturality V V' f := by
    ext b : 3
    refine Subtype.ext ?_
    change baseChangePrecompMap φ π π' hπ V'.unop ≫ baseChangeRestrictionMap π f.unop ≫ b.1 =
      baseChangeRestrictionMap π' f.unop ≫ baseChangePrecompMap φ π π' hπ V.unop ≫ b.1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp

/-- `homFromBaseChangePrecomp` acts by precomposition with the map of base changes induced by
`φ`. -/
@[simp]
theorem homFromBaseChangePrecomp_app_coe {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : Y' ⟶ Y)
    (π : Y ⟶ yoneda.obj A) (π' : Y' ⟶ yoneda.obj A) (hπ : φ ≫ π = π') (g : Y ⟶ Q)
    (g' : Y' ⟶ Q) (hg : φ ≫ g = g') (V : (Over A)ᵒᵖ) (b : (homFromBaseChange x π g).obj V) :
    ((homFromBaseChangePrecomp x φ π π' hπ g g' hg).app V b).1 =
      baseChangePrecompMap φ π π' hπ V.unop ≫ b.1 :=
  rfl

end HomFromBaseChange

/-! ### The representable case -/

section Representable

variable {X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X ⟶ Q) {A : BigFppfOver B S hS}

/-- The base change of the Yoneda image of `u : U ⟶ A` along `V ⟶ A` is represented by
`V ×_A U`, compatibly with the comparison maps. -/
theorem preservesPullbackIso_hom_baseChangeRestrictionMap {U : BigFppfOver B S hS} (u : U ⟶ A)
    {V V' : Over A} (f : V' ⟶ V) :
    (PreservesPullback.iso yoneda V'.hom u).hom ≫ baseChangeRestrictionMap (yoneda.map u) f =
      yoneda.map ((Over.pullback u).map f).left ≫ (PreservesPullback.iso yoneda V.hom u).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, baseChangeRestrictionMap_fst, PreservesPullback.iso_hom_fst_assoc,
      PreservesPullback.iso_hom_fst, ← Functor.map_comp, Over.pullback_map_left, pullback.lift_fst]
  · simp only [Category.assoc, baseChangeRestrictionMap_snd, PreservesPullback.iso_hom_snd,
      ← Functor.map_comp, Over.pullback_map_left, pullback.lift_snd]

/-- **Morphisms out of base changes of a representable presheaf are points of a section fibre.**
For `u : U ⟶ A` and `g : h_U ⟶ Q`, a morphism `h_U ×_A V ⟶ X` over `Q` is a point of `X` over
`V ×_A U` lifting the restriction of `g`, i.e. a section of the presheaf of lifts of `g` through
`x` on the base change `V ×_A U` of `V`. -/
def homFromBaseChangeYonedaIso {U : BigFppfOver B S hS} (u : U ⟶ A) (g : yoneda.obj U ⟶ Q) :
    homFromBaseChange x (yoneda.map u) g ≅
      (Over.pullback u).op ⋙ sectionFiber B S hS x U (yonedaEquiv g) ⋙
        uliftFunctor.{u + 1} :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun (b : HomFromBaseChangeAt x (yoneda.map u) g V.unop) =>
        (ULift.up ⟨yonedaEquiv ((PreservesPullback.iso yoneda V.unop.hom u).hom ≫ b.1), by
          change x.app _ (yonedaEquiv _) = Q.map (pullback.snd V.unop.hom u).op (yonedaEquiv g)
          rw [← yonedaEquiv_comp, Category.assoc, b.2, ← Category.assoc,
            PreservesPullback.iso_hom_snd, yonedaEquiv_naturality]⟩ :
          ULift.{u + 1} ((sectionFiber B S hS x U (yonedaEquiv g)).obj
            (op ((Over.pullback u).obj V.unop))))
      invFun := fun (ξ : ULift.{u + 1} ((sectionFiber B S hS x U (yonedaEquiv g)).obj
            (op ((Over.pullback u).obj V.unop)))) =>
        (⟨(PreservesPullback.iso yoneda V.unop.hom u).inv ≫ yonedaEquiv.symm ξ.down.1, by
          have h : x.app (op (pullback V.unop.hom u)) ξ.down.1 =
              Q.map (pullback.snd V.unop.hom u).op (yonedaEquiv g) := ξ.down.2
          rw [← cancel_epi (PreservesPullback.iso yoneda V.unop.hom u).hom]
          simp only [Category.assoc, Iso.hom_inv_id_assoc, PreservesPullback.iso_hom_snd_assoc]
          apply yonedaEquiv.injective
          rw [yonedaEquiv_comp, Equiv.apply_symm_apply, h, yonedaEquiv_naturality]⟩ :
          HomFromBaseChangeAt x (yoneda.map u) g V.unop)
      left_inv := fun b => Subtype.ext (by
        change (PreservesPullback.iso yoneda V.unop.hom u).inv ≫ yonedaEquiv.symm (yonedaEquiv
          ((PreservesPullback.iso yoneda V.unop.hom u).hom ≫ b.1)) = b.1
        rw [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc])
      right_inv := fun ξ => by
        apply ULift.ext
        apply Subtype.ext
        change yonedaEquiv ((PreservesPullback.iso yoneda V.unop.hom u).hom ≫
          (PreservesPullback.iso yoneda V.unop.hom u).inv ≫ yonedaEquiv.symm ξ.down.1) = ξ.down.1
        rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply] }) (by
    intro V V' f
    ext b : 3
    apply ULift.ext
    apply Subtype.ext
    change yonedaEquiv ((PreservesPullback.iso yoneda V'.unop.hom u).hom ≫
        baseChangeRestrictionMap (yoneda.map u) f.unop ≫ b.1) =
      X.map ((Over.pullback u).map f.unop).left.op
        (yonedaEquiv ((PreservesPullback.iso yoneda V.unop.hom u).hom ≫ b.1))
    rw [← Category.assoc, preservesPullbackIso_hom_baseChangeRestrictionMap, Category.assoc,
      yonedaEquiv_naturality])

/-- **The representable case.** For `u : U ⟶ A` between affine objects and `x` locally of finite
presentation between algebraic spaces, the presheaf of morphisms `h_U ×_A V ⟶ X` over `Q` is limit
preserving: it is the relative limit preservation of `x` (Stacks 04AK, (1) ⟹ (2)) read on the base
changes `V ×_A U`. -/
theorem limitPreserving_homFromBaseChange_yoneda (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) (hx : IsLocallyOfFinitePresentation B S hS x)
    {U : BigFppfOver B S hS} (u : U ⟶ A)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (g : yoneda.obj U ⟶ Q) :
    LimitPreserving.{u, u + 1, u, u} (Over.forget A ⋙ BigFppfOver.toScheme B S hS)
      (homFromBaseChange x (yoneda.map u) g) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have h1 := relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hX hQ hx U
    (yonedaEquiv g)
  have h2 := limitPreserving_overPullback_comp (BigFppfOver.toScheme B S hS) u hA hU _ h1
  have h3 : LimitPreserving.{u, u + 1, u, u} (Over.forget A ⋙ BigFppfOver.toScheme B S hS)
      (((Over.pullback u).op ⋙ sectionFiber B S hS x U (yonedaEquiv g)) ⋙
        uliftFunctor.{u + 1}) := by
    intro I _ _ D c hc hD hC
    obtain ⟨h⟩ := h2 I D c hc hD hC
    exact ⟨isColimitOfPreserves uliftFunctor.{u + 1} h⟩
  exact limitPreserving_of_natIso (homFromBaseChangeYonedaIso x u g).symm h3

end Representable

/-! ### Base changes of a morphism of finite presentation -/

section FinitePresentation

variable {X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : X ⟶ Q) {A : BigFppfOver B S hS}

/-- **Morphisms out of the base changes of a morphism of finite presentation.** Let `A` be an
affine object, `π : Y ⟶ h_A` a morphism of finite presentation from an algebraic space, and
`x : X ⟶ Q` a morphism locally of finite presentation of algebraic spaces. Then the presheaf of
morphisms `Y ×_A V ⟶ X` over `Q`, on the objects `V` over `A`, is limit preserving.

`Y` is quasi-compact, so it has an affine étale atlas `q : h_U ⟶ Y`; `Y` is quasi-separated over
`A`, so the kernel pair `h_U ×_Y h_U` is quasi-compact and has an affine étale atlas
`r : h_R ⟶ h_U ×_Y h_U`. A morphism `Y ×_A V ⟶ X` is a morphism `h_U ×_A V ⟶ X` whose two
restrictions to `h_R ×_A V` agree: injectivity is cancellation of the surjective étale atlas
`h_U ×_A V ⟶ Y ×_A V`, and existence is descent along it (Stacks 0262), the descent condition on
the kernel pair of that atlas being checked after the surjective étale cover by `h_R ×_A V`. The
equalizer of two limit-preserving presheaves is limit preserving, and the two presheaves of the
charts are, by `AlgebraicGeometry.Space.limitPreserving_homFromBaseChange_yoneda`. -/
theorem limitPreserving_homFromBaseChange (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q) (hx : IsLocallyOfFinitePresentation B S hS x)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (π : Y ⟶ yoneda.obj A) (hπ : IsFinitePresentation B S hS π) (g : Y ⟶ Q) :
    LimitPreserving.{u, u + 1, u, u} (Over.forget A ⋙ BigFppfOver.toScheme B S hS)
      (homFromBaseChange x π g) := by
  classical
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  let Psurj := MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let Pet := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : Psurj.presheaf.IsStableUnderBaseChange :=
    Psurj.relative_isStableUnderBaseChange (F := yoneda)
  have : Pet.presheaf.IsStableUnderBaseChange :=
    Pet.relative_isStableUnderBaseChange (F := yoneda)
  have hAalg := isAlgebraicSpace_yoneda B S hS A
  have hYqc : IsQuasiCompactSpace B S hS Y :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS π hAalg
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS A hA) hπ
  obtain ⟨U, q, hU, hqs, hqe'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hY).mp hYqc
  have hqe : Pet.presheaf q := presheaf_etale_of_isEtale B S hS hqe'
  let u : U ⟶ A := yoneda.preimage (q ≫ π)
  have hu : yoneda.map u = q ≫ π := yoneda.map_preimage _
  have hUalg := isAlgebraicSpace_yoneda B S hS U
  have hKalg : IsAlgebraicSpace B S hS (pullback q q) :=
    isAlgebraicSpace_pullback B S hS q q hUalg hUalg hY
  have hKqc : IsQuasiCompactSpace B S hS (pullback q q) := by
    have hZalg : IsAlgebraicSpace B S hS (pullback (q ≫ π) (q ≫ π)) :=
      isAlgebraicSpace_pullback B S hS _ _ hUalg hUalg hAalg
    have hZqc : IsQuasiCompactSpace B S hS (pullback (q ≫ π) (q ≫ π)) := by
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj A) := hA
      have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
      have hUU : IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback u u)) :=
        isAffine_obj_pullback _ u u
      exact IsQuasiCompactSpace.of_iso B S hS
        (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hUU)
        (PreservesPullback.iso yoneda u u ≪≫ pullback.congrHom hu hu)
    have h := hπ.2.2 _ hZalg hZqc
      (pullback.map (q ≫ π) (q ≫ π) π π q q (𝟙 _) (Category.comp_id _) (Category.comp_id _))
    exact IsQuasiCompactSpace.of_iso B S hS h
      (pullbackSymmetry _ _ ≪≫ pullbackDiagonalMapIdIso q q π)
  obtain ⟨R, r, hR, hrs, hre'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hKalg).mp hKqc
  have hre : Pet.presheaf r := presheaf_etale_of_isEtale B S hS hre'
  let s' : R ⟶ U := yoneda.preimage (r ≫ pullback.fst q q)
  let t' : R ⟶ U := yoneda.preimage (r ≫ pullback.snd q q)
  have hs' : yoneda.map s' = r ≫ pullback.fst q q := yoneda.map_preimage _
  have ht' : yoneda.map t' = r ≫ pullback.snd q q := yoneda.map_preimage _
  have hst : yoneda.map s' ≫ q = yoneda.map t' ≫ q := by
    rw [hs', ht', Category.assoc, Category.assoc, pullback.condition]
  let ρ : R ⟶ A := s' ≫ u
  have hsρ : yoneda.map s' ≫ yoneda.map u = yoneda.map ρ := (yoneda.map_comp _ _).symm
  have htρ : yoneda.map t' ≫ yoneda.map u = yoneda.map ρ := by
    rw [← hsρ, hu, ← Category.assoc, ← Category.assoc, hst]
  let a := homFromBaseChangePrecomp x q π (yoneda.map u) hu.symm g (q ≫ g) rfl
  let b₁ := homFromBaseChangePrecomp x (yoneda.map s') (yoneda.map u) (yoneda.map ρ) hsρ
    (q ≫ g) (yoneda.map s' ≫ q ≫ g) rfl
  let b₂ := homFromBaseChangePrecomp x (yoneda.map t') (yoneda.map u) (yoneda.map ρ) htρ
    (q ≫ g) (yoneda.map s' ≫ q ≫ g) (by rw [← Category.assoc, ← hst, Category.assoc])
  let pm (V : Over A) := baseChangePrecompMap q π (yoneda.map u) hu.symm V
  let e (V : Over A) := PreservesPullback.iso yoneda V.hom u
  have hpm (V : Over A) : IsPullback (pm V) (pullback.snd _ _) (pullback.snd _ _) q := by
    refine IsPullback.of_right (h₁₂ := pullback.fst (yoneda.map V.hom) π) (h₂₂ := π)
      (v₁₃ := yoneda.map V.hom) ?_ (by simp [pm]) (IsPullback.of_hasPullback _ _)
    rw [baseChangePrecompMap_fst]
    exact hu ▸ IsPullback.of_hasPullback (yoneda.map V.hom) (yoneda.map u)
  have hpS (V : Over A) : Psurj.presheaf ((e V).hom ≫ pm V) :=
    MorphismProperty.RespectsIso.precomp _ _ _ (MorphismProperty.of_isPullback (hpm V).flip hqs)
  have hpE (V : Over A) : Pet.presheaf ((e V).hom ≫ pm V) :=
    MorphismProperty.RespectsIso.precomp _ _ _ (MorphismProperty.of_isPullback (hpm V).flip hqe)
  have hFsh (V : Over A) : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (pullback (yoneda.map V.hom) π) :=
    Presheaf.isSheaf_pullback _ _ _ (isAlgebraicSpace_yoneda B S hS _).isSheaf hY.isSheaf
      hAalg.isSheaf
  refine limitPreserving_of_isEqualizer _ a b₁ b₂ ?_ ?_ ?_
    (limitPreserving_homFromBaseChange_yoneda x hX hQ hx u hA hU (q ≫ g))
    (limitPreserving_homFromBaseChange_yoneda x hX hQ hx ρ hA hR (yoneda.map s' ≫ q ≫ g))
  · intro V b₁' b₂' hb
    apply Subtype.ext
    apply hom_ext_of_etale_atlas B S hS (hFsh V.unop) hX.isSheaf _ (hpS V.unop) (hpE V.unop)
    have h := congrArg Subtype.val hb
    change pm V.unop ≫ b₁'.1 = pm V.unop ≫ b₂'.1 at h
    rw [Category.assoc, Category.assoc, h]
  · intro V b
    apply Subtype.ext
    change baseChangePrecompMap (yoneda.map s') (yoneda.map u) (yoneda.map ρ) hsρ V.unop ≫
        pm V.unop ≫ b.1 =
      baseChangePrecompMap (yoneda.map t') (yoneda.map u) (yoneda.map ρ) htρ V.unop ≫
        pm V.unop ≫ b.1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp [pm]
    · simp only [Category.assoc, baseChangePrecompMap_snd, baseChangePrecompMap_snd_assoc, pm]
      rw [hst]
  · intro V ξ hξ
    let V₀ := V.unop
    let p := (e V₀).hom ≫ pm V₀
    obtain ⟨R₀, s, t, hR₀⟩ := exists_kernelPair_of_etale_atlas B S hS p (hpE V₀)
    have hk : yoneda.map s ≫ ((e V₀).hom ≫ ξ.1) = yoneda.map t ≫ ((e V₀).hom ≫ ξ.1) := by
      let sn : pullback V₀.hom u ⟶ U := pullback.snd V₀.hom u
      let fs : pullback V₀.hom u ⟶ V₀.left := pullback.fst V₀.hom u
      have hsn : (e V₀).hom ≫ pullback.snd (yoneda.map V₀.hom) (yoneda.map u) = yoneda.map sn :=
        PreservesPullback.iso_hom_snd _ _ _
      have hfs : (e V₀).hom ≫ pullback.fst (yoneda.map V₀.hom) (yoneda.map u) = yoneda.map fs :=
        PreservesPullback.iso_hom_fst _ _ _
      have hpq : yoneda.map sn ≫ q = p ≫ pullback.snd (yoneda.map V₀.hom) π := by
        simp only [p, pm, Category.assoc, baseChangePrecompMap_snd, ← hsn]
      have hpf : yoneda.map fs = p ≫ pullback.fst (yoneda.map V₀.hom) π := by
        simp only [p, pm, Category.assoc, baseChangePrecompMap_fst, ← hfs]
      let m : yoneda.obj R₀ ⟶ pullback q q := pullback.lift (yoneda.map (s ≫ sn))
        (yoneda.map (t ≫ sn)) (by
          simp only [Functor.map_comp, Category.assoc, hpq]
          rw [← Category.assoc, hR₀.w, Category.assoc])
      let E := hre.rep.pullback m
      let eE : E ⟶ R₀ := hre.rep.snd m
      let fE : yoneda.obj E ⟶ yoneda.obj R := hre.rep.fst m
      have hEpb : IsPullback fE (yoneda.map eE) r m := hre.rep.isPullback m
      have hEs : Psurj.presheaf (yoneda.map eE) := MorphismProperty.of_isPullback hEpb hrs
      have hEe : Pet.presheaf (yoneda.map eE) := MorphismProperty.of_isPullback hEpb hre
      let fR : E ⟶ R := yoneda.preimage fE
      have hfR : yoneda.map fR = fE := yoneda.map_preimage _
      have hfEs : fE ≫ yoneda.map s' = yoneda.map (eE ≫ s ≫ sn) := by
        rw [hs', ← Category.assoc, hEpb.w, Category.assoc, pullback.lift_fst, ← Functor.map_comp]
      have hfEt : fE ≫ yoneda.map t' = yoneda.map (eE ≫ t ≫ sn) := by
        rw [ht', ← Category.assoc, hEpb.w, Category.assoc, pullback.lift_snd, ← Functor.map_comp]
      have hsfs : s ≫ fs = t ≫ fs := by
        apply yoneda.map_injective
        simp only [Functor.map_comp, hpf]
        rw [← Category.assoc, hR₀.w, Category.assoc]
      have hψ : (eE ≫ s ≫ fs) ≫ V₀.hom = fR ≫ ρ := by
        apply yoneda.map_injective
        have hc : fs ≫ V₀.hom = sn ≫ u := pullback.condition
        calc yoneda.map ((eE ≫ s ≫ fs) ≫ V₀.hom) = yoneda.map (eE ≫ s ≫ sn) ≫ yoneda.map u := by
              rw [← Functor.map_comp]; simp only [Category.assoc, hc]
          _ = fE ≫ yoneda.map s' ≫ yoneda.map u := by rw [← hfEs, Category.assoc]
          _ = yoneda.map (fR ≫ ρ) := by rw [← hfR]; simp only [ρ, Functor.map_comp]
      let ψ : E ⟶ pullback V₀.hom ρ := pullback.lift (eE ≫ s ≫ fs) fR hψ
      let eR := PreservesPullback.iso yoneda V₀.hom ρ
      let pS := baseChangePrecompMap (yoneda.map s') (yoneda.map u) (yoneda.map ρ) hsρ V₀
      let pT := baseChangePrecompMap (yoneda.map t') (yoneda.map u) (yoneda.map ρ) htρ V₀
      have hEq : pS ≫ ξ.1 = pT ≫ ξ.1 := congrArg Subtype.val hξ
      have hSq : ∀ (σ : R ⟶ U) (τ : R₀ ⟶ pullback V₀.hom u) (hσ : yoneda.map σ ≫ yoneda.map u =
          yoneda.map ρ), fE ≫ yoneda.map σ = yoneda.map (eE ≫ τ ≫ sn) → τ ≫ fs = s ≫ fs →
          yoneda.map ψ ≫ eR.hom ≫ baseChangePrecompMap (yoneda.map σ) (yoneda.map u)
            (yoneda.map ρ) hσ V₀ = yoneda.map eE ≫ yoneda.map τ ≫ (e V₀).hom :=
        fun σ τ hσ h₁ h₂ => by
        apply pullback.hom_ext
        · simp only [Category.assoc, baseChangePrecompMap_fst, eR, PreservesPullback.iso_hom_fst,
            hfs, ← Functor.map_comp, ψ, pullback.lift_fst, h₂]
        · simp only [Category.assoc, baseChangePrecompMap_snd, eR,
            PreservesPullback.iso_hom_snd_assoc, hsn, ← Functor.map_comp]
          rw [pullback.lift_snd_assoc, Functor.map_comp, hfR, h₁]
      apply hom_ext_of_etale_atlas B S hS (isAlgebraicSpace_yoneda B S hS R₀).isSheaf
        hX.isSheaf (yoneda.map eE) hEs hEe
      have h : (yoneda.map ψ ≫ eR.hom ≫ pS) ≫ ξ.1 = (yoneda.map ψ ≫ eR.hom ≫ pT) ≫ ξ.1 := by
        simp only [Category.assoc, hEq]
      rw [hSq _ s hsρ hfEs rfl, hSq _ t htρ hfEt hsfs.symm] at h
      simpa only [Category.assoc] using h
    obtain ⟨d, hd, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS (hFsh V₀) p hR₀
      (hpS V₀) (hpE V₀) hX.isSheaf ((e V₀).hom ≫ ξ.1) hk
    refine ⟨⟨d, ?_⟩, ?_⟩
    · apply hom_ext_of_etale_atlas B S hS (hFsh V₀) hQ.isSheaf p (hpS V₀) (hpE V₀)
      rw [← Category.assoc, hd, Category.assoc, ξ.2]
      simp only [p, pm, V₀, Category.assoc, baseChangePrecompMap_snd_assoc]
    · apply Subtype.ext
      change pm V₀ ≫ d = ξ.1
      rw [← cancel_epi (e V₀).hom, ← Category.assoc]
      exact hd

end FinitePresentation

/-! ### Restricting a section fibre along a morphism of the base -/

/-- **The presheaf of lifts of `y` restricted to the objects over `A` is the presheaf of lifts of
the restriction of `y` to `A`.** -/
def sectionFiberOverMapIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G)
    {A T₀ : BigFppfOver B S hS} (α : A ⟶ T₀) (y : G.obj (op T₀)) :
    (Over.map α).op ⋙ sectionFiber B S hS p T₀ y ≅ sectionFiber B S hS p A (G.map α.op y) :=
  NatIso.ofComponents (fun W => Equiv.toIso (Equiv.subtypeEquivRight (fun f => by
      change _ = G.map (W.unop.hom ≫ α).op y ↔ _ = G.map W.unop.hom.op (G.map α.op y)
      rw [op_comp, Functor.map_comp_apply]
      exact Iff.rfl))) (by
    intro W W' f
    ext w : 3
    rfl)

/-! ### The relative morphism functor -/

section RelativeHom

variable {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)
  (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
  (hQ : IsAlgebraicSpace B S hS Q)

/-- The pair of Stacks 05Y1 over `V` determined by a morphism `h_V ×_A (h_A ×_Q Z) ⟶ X` over `Q`,
for a point `a : h_A ⟶ Q` and `V` over `A`: its base is `h_V ⟶ h_A ⟶ Q`, and its second component
is read through `h_V ×_A (h_A ×_Q Z) ≅ h_V ×_Q Z`. -/
def relativeHomOfHomFromBaseChange {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ Q) (V : Over A)
    (b : HomFromBaseChangeAt x (pullback.fst a z) (pullback.snd a z ≫ z) V) :
    (relativeHom B S hS Z X Q z x hZ hX hQ).obj (op V.left) :=
  (relativeHomSections B S hS Z X Q z x hZ hX hQ V.left).symm
    { base := yoneda.map V.hom ≫ a
      morphism := (pullbackRightPullbackFstIso a z (yoneda.map V.hom)).inv ≫ b.1
      commutes := by
        rw [Category.assoc, b.2]
        simp }

/-- The section `relativeHomOfHomFromBaseChange` of `Mor_Q(Z, X)` over `V` projects to the
restriction of the point `a` of `Q` to `V`. -/
theorem relativeHomProjection_app_relativeHomOfHomFromBaseChange {A : BigFppfOver B S hS}
    (a : yoneda.obj A ⟶ Q) (V : Over A)
    (b : HomFromBaseChangeAt x (pullback.fst a z) (pullback.snd a z ≫ z) V) :
    (relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (op V.left)
        (relativeHomOfHomFromBaseChange z x hZ hX hQ a V b) =
      Q.map V.hom.op (yonedaEquiv a) := by
  rw [show (relativeHomProjection B S hS Z X Q z x hZ hX hQ).app (op V.left)
      (relativeHomOfHomFromBaseChange z x hZ hX hQ a V b) = yonedaEquiv
        ((relativeHomSections B S hS Z X Q z x hZ hX hQ V.left)
          (relativeHomOfHomFromBaseChange z x hZ hX hQ a V b)).base from
      (relativeHomData B S hS Z X Q z x hZ hX hQ).projection_sections _ _]
  simp only [relativeHomOfHomFromBaseChange, Equiv.apply_symm_apply]
  exact (yonedaEquiv_naturality a V.hom).symm

/-- The inverse of `pullbackRightPullbackFstIso` intertwines the comparison of base changes along
`f : V' ⟶ V` with the map `h_V' ×_Q Z ⟶ h_V ×_Q Z` induced by `f`. -/
theorem pullbackRightPullbackFstIso_inv_baseChangeRestrictionMap {A : BigFppfOver B S hS}
    (a : yoneda.obj A ⟶ Q) {V V' : Over A} (f : V' ⟶ V)
    (hbase : yoneda.map V'.hom ≫ a = yoneda.map f.left ≫ yoneda.map V.hom ≫ a) :
    (pullbackRightPullbackFstIso a z (yoneda.map V'.hom)).inv ≫
        baseChangeRestrictionMap (pullback.fst a z) f =
      (pullback.congrHom hbase rfl).hom ≫
        pullback.map (yoneda.map f.left ≫ yoneda.map V.hom ≫ a) z (yoneda.map V.hom ≫ a) z
          (yoneda.map f.left) (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫
        (pullbackRightPullbackFstIso a z (yoneda.map V.hom)).inv := by
  apply pullback.hom_ext
  · simp
  · apply pullback.hom_ext
    · simp only [Category.assoc, baseChangeRestrictionMap_snd,
        pullbackRightPullbackFstIso_inv_snd_fst]
      simp [← Functor.map_comp, Over.w f]
    · simp

/-- **The presheaf of lifts of a point of `Q` to `Mor_Q(Z, X)` is a presheaf of morphisms out of
base changes.** For a point `a : h_A ⟶ Q`, a section of `Mor_Q(Z, X)` over `V ⟶ A` lying over
the restriction of `a` is a morphism `h_V ×_A (h_A ×_Q Z) ⟶ X` over `Q`. -/
def homFromBaseChangeToSectionFiber {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ Q) :
    homFromBaseChange x (pullback.fst a z) (pullback.snd a z ≫ z) ⟶
      sectionFiber B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) A (yonedaEquiv a) ⋙
        uliftFunctor.{u + 1} where
  app V := TypeCat.ofHom (fun (b : HomFromBaseChangeAt x (pullback.fst a z)
      (pullback.snd a z ≫ z) V.unop) =>
    (ULift.up ⟨relativeHomOfHomFromBaseChange z x hZ hX hQ a V.unop b,
      relativeHomProjection_app_relativeHomOfHomFromBaseChange z x hZ hX hQ a V.unop b⟩ :
        ULift.{u + 1} ((sectionFiber B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) A
          (yonedaEquiv a)).obj V)))
  naturality V V' f := by
    ext b : 3
    apply ULift.ext
    apply Subtype.ext
    change relativeHomOfHomFromBaseChange z x hZ hX hQ a V'.unop
        ((homFromBaseChange x (pullback.fst a z) (pullback.snd a z ≫ z)).map f b) =
      (relativeHom B S hS Z X Q z x hZ hX hQ).map f.unop.left.op
        (relativeHomOfHomFromBaseChange z x hZ hX hQ a V.unop b)
    apply (relativeHomSections B S hS Z X Q z x hZ hX hQ V'.unop.left).injective
    rw [relativeHomSections_map]
    simp only [relativeHomOfHomFromBaseChange, Equiv.apply_symm_apply]
    have hbase : yoneda.map V'.unop.hom ≫ a =
        yoneda.map f.unop.left ≫ yoneda.map V.unop.hom ≫ a := by
      rw [← Category.assoc, ← Functor.map_comp, Over.w f.unop]
    refine RelativeMorphism.ext_of_base_eq hbase ?_
    simp only [RelativeMorphism.restrict_morphism, homFromBaseChange_map_coe]
    exact (reassoc_of% (pullbackRightPullbackFstIso_inv_baseChangeRestrictionMap z a f.unop
      hbase)) b.1

/-- The comparison `homFromBaseChangeToSectionFiber` is an isomorphism of presheaves. -/
theorem isIso_homFromBaseChangeToSectionFiber {A : BigFppfOver B S hS} (a : yoneda.obj A ⟶ Q) :
    IsIso (homFromBaseChangeToSectionFiber z x hZ hX hQ a) := by
  have : ∀ V, IsIso ((homFromBaseChangeToSectionFiber z x hZ hX hQ a).app V) := fun V => by
    rw [isIso_iff_bijective]
    refine ⟨fun b₁ b₂ h => ?_, ?_⟩
    · have h0 := congrArg ULift.down h
      have h1 : relativeHomOfHomFromBaseChange z x hZ hX hQ a V.unop b₁ =
          relativeHomOfHomFromBaseChange z x hZ hX hQ a V.unop b₂ :=
        congrArg Subtype.val h0
      have h2 := (relativeHomSections B S hS Z X Q z x hZ hX hQ V.unop.left).symm.injective h1
      have h3 := eq_of_heq (RelativeMorphism.mk.inj h2).2
      rw [cancel_epi] at h3
      exact Subtype.ext h3
    · rintro ⟨w⟩
      let P := relativeHomSections B S hS Z X Q z x hZ hX hQ V.unop.left w.1
      have hbase : P.base = yoneda.map V.unop.hom ≫ a := by
        apply yonedaEquiv.injective
        rw [← yonedaEquiv_naturality, ← w.2]
        exact ((relativeHomData B S hS Z X Q z x hZ hX hQ).projection_sections _ _).symm
      refine ⟨⟨(pullbackRightPullbackFstIso a z (yoneda.map V.unop.hom)).hom ≫
        (pullback.congrHom hbase rfl).inv ≫ P.morphism, ?_⟩, ?_⟩
      · rw [Category.assoc, Category.assoc, P.commutes]
        simp [pullback.congrHom_inv]
      · apply ULift.ext
        apply Subtype.ext
        change relativeHomOfHomFromBaseChange z x hZ hX hQ a V.unop _ = w.1
        rw [relativeHomOfHomFromBaseChange, Equiv.symm_apply_eq]
        refine RelativeMorphism.ext_of_base_eq hbase.symm ?_
        change (pullbackRightPullbackFstIso a z (yoneda.map V.unop.hom)).inv ≫
            (pullbackRightPullbackFstIso a z (yoneda.map V.unop.hom)).hom ≫
            (pullback.congrHom hbase rfl).inv ≫ P.morphism =
          (pullback.congrHom hbase.symm rfl).hom ≫ P.morphism
        rw [Iso.inv_hom_id_assoc]
        congr 1
        apply pullback.hom_ext <;> simp [pullback.congrHom_inv]
  exact NatIso.isIso_of_isIso_app _

/-- **The presheaf of lifts to `Mor_Q(Z, X)` over an affine object is limit preserving**, for `z`
of finite presentation and `x` locally of finite presentation. -/
theorem limitPreserving_sectionFiber_relativeHomProjection
    (hz : IsFinitePresentation B S hS z) (hx : IsLocallyOfFinitePresentation B S hS x)
    {A : BigFppfOver B S hS} (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (a : yoneda.obj A ⟶ Q) :
    LimitPreserving.{u, u, u, u} (Over.forget A ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) A
        (yonedaEquiv a)) := by
  have hAalg := isAlgebraicSpace_yoneda B S hS A
  have hY := isAlgebraicSpace_pullback B S hS a z hAalg hZ hQ
  have hπ : IsFinitePresentation B S hS (pullback.fst a z) :=
    IsFinitePresentation.of_isPullback B S hS hY hZ hAalg hQ
      (IsPullback.of_hasPullback a z).flip hz
  have h := limitPreserving_homFromBaseChange x hX hQ hx hA hY (pullback.fst a z) hπ
    (pullback.snd a z ≫ z)
  have := isIso_homFromBaseChangeToSectionFiber z x hZ hX hQ a
  have h' := limitPreserving_of_natIso (asIso (homFromBaseChangeToSectionFiber z x hZ hX hQ a)) h
  intro I _ _ D c hc hD hC
  obtain ⟨hcol⟩ := h' I D c hc hD hC
  exact ⟨isColimitOfReflects uliftFunctor.{u + 1} hcol⟩

/-- **The projection `Mor_Q(Z, X) ⟶ Q` is relatively limit preserving**, for `z : Z ⟶ Q` of finite
presentation and `x : X ⟶ Q` locally of finite presentation (Stacks 049J). Over a point `y` of `Q`
over `T₀`, a cofiltered system of affines over `T₀` lies over one of its stages `A`, over which the
presheaf of lifts of `y` is the presheaf of morphisms `h_V ×_A (h_A ×_Q Z) ⟶ X` over `Q`. -/
theorem relativelyLimitPreserving_relativeHomProjection
    (hz : IsFinitePresentation B S hS z) (hx : IsLocallyOfFinitePresentation B S hS x) :
    RelativelyLimitPreserving.{u, u, u, u} B S hS
      (relativeHomProjection B S hS Z X Q z x hZ hX hQ) := by
  intro T₀ y
  refine limitPreserving_of_overMap (BigFppfOver.toScheme B S hS) _ (fun A α hA => ?_)
  refine limitPreserving_of_natIso
    (sectionFiberOverMapIso (relativeHomProjection B S hS Z X Q z x hZ hX hQ) α y).symm ?_
  obtain ⟨a, ha⟩ := yonedaEquiv.surjective (Q.map α.op y)
  rw [← ha]
  exact limitPreserving_sectionFiber_relativeHomProjection z x hZ hX hQ hz hx hA a

/-- **`Mor_Q(Z, X) ⟶ Q` is locally of finite presentation**, for `z : Z ⟶ Q` of finite
presentation and `x : X ⟶ Q` locally of finite presentation. This is the half "locally of finite
presentation over `B`" of Stacks 0D1C, read off the functor of points through Stacks 04AK, which
needs no algebraicity of `Mor_Q(Z, X)`. -/
theorem isLocallyOfFinitePresentation_relativeHomProjection_of_isFinitePresentation
    (hz : IsFinitePresentation B S hS z) (hx : IsLocallyOfFinitePresentation B S hS x) :
    IsLocallyOfFinitePresentation B S hS (relativeHomProjection B S hS Z X Q z x hZ hX hQ) :=
  AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving B S hS
    (relativelyLimitPreserving_relativeHomProjection z x hZ hX hQ hz hx)

end RelativeHom

end Space

end AlgebraicGeometry

end
