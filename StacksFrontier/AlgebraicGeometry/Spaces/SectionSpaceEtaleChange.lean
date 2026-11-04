module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RelocalizedSectionsFibre
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibreRestrict

/-!
# Spaces of sections along an étale change of the target

Let `U` be a scheme contained in a big fppf site, let `Z` be an object of the big fppf site of
`U` whose structure morphism is finite, and let `p : W' ⟶ W` be a morphism of presheaves over
`h_Z`. This file identifies the fibre of the induced morphism of spaces of sections
`AlgebraicGeometry.Space.sectionSpaceMap p : Γ(W'/Z) ⟶ Γ(W/Z)` over a scheme-valued point
`σ : h_T ⟶ Γ(W/Z)`: it is the lower-shriek extension, along the structure morphism `a : T ⟶ U`,
of the space of sections over the big fppf site of `T` of the base change
`W'_σ = W' ×_{W, σ} Z_T ⟶ Z_T`, where `Z_T = Z ×_U T`.

## Main definitions

* `AlgebraicGeometry.Space.sectionSubfunctorMap`: the morphism of the subfunctors of
  `T ↦ W(Z × T)` attached to `p`, which `sectionSpaceMap p` becomes under
  `AlgebraicGeometry.Space.sectionSpaceIsoSubfunctor`.
* `AlgebraicGeometry.Space.SectionFibre.cover`: the base change `Z_T` of `Z`, an object of the
  big fppf site of `T`.
* `AlgebraicGeometry.Space.SectionFibre.point`: the morphism `h_{Z_T} ⟶ W|_T` given by `σ`.
* `AlgebraicGeometry.Space.SectionFibre.total`: the presheaf `W'_σ` on the big fppf site of `T`,
  with its structure morphism `AlgebraicGeometry.Space.SectionFibre.proj` to `h_{Z_T}`.

## Main results

* `AlgebraicGeometry.Space.SectionFibre.isPullback_total`: `W'_σ` is the fibre product of the
  restriction of `p` to the site of `T` and of `σ`.
* `AlgebraicGeometry.Space.SectionFibre.fibreIso`: the fibre of `sectionSubfunctorMap p` over the
  point named by `σ`, in the form `CategoryTheory.OverShriek.fibreOfSection`, is the subfunctor
  of sections of `W'_σ ⟶ Z_T`.

## Implementation notes

The base change `Z_T` is `CategoryTheory.Over.pullback a` applied to `Z`, and the identification
of `(Z_T × Y) ↦ T` with `Z × (Y ↦ U)` for an object `Y` of the site of `T` is the comparison
morphism `AlgebraicGeometry.Space.SectionFibre.prodComparison`, an isomorphism because the
underlying square of schemes is the composite of two cartesian squares. Everything is stated in
terms of the subfunctor `AlgebraicGeometry.Space.sectionSubfunctor` of `T ↦ W(Z × T)`, which is
how `AlgebraicGeometry.Space.sectionSpace` is identified with an elementwise description.

## References

* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YD](https://stacks.math.columbia.edu/tag/05YD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OverShriek

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}

/-! ### The morphism of subfunctors attached to a morphism over `h_Z` -/

section SubfunctorMap

variable {Z : BigFppfOver B U hU} {W W' : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
  {w : W ⟶ yoneda.obj Z} {w' : W' ⟶ yoneda.obj Z} (p : W' ⟶ W) (hp : p ≫ w = w')

/-- The morphism of the subfunctors of `T ↦ W'(Z × T)` and `T ↦ W(Z × T)` given by `p`. -/
noncomputable def sectionSubfunctorMap :
    (sectionSubfunctor Z W' w').toFunctor ⟶ (sectionSubfunctor Z W w).toFunctor where
  app T := ↾fun s => ⟨p.app _ s.1, by
    refine Eq.trans ?_ s.2
    exact congrArg (fun k : W' ⟶ yoneda.obj Z => k.app _ s.1) hp⟩
  naturality T T' f := by
    ext s
    apply Subtype.ext
    exact NatTrans.naturality_apply p (prod.map (𝟙 Z) f.unop).op s.1

/-- Under `AlgebraicGeometry.Space.sectionSpaceIsoSubfunctor`, `sectionSpaceMap p` is
`sectionSubfunctorMap p`. -/
theorem sectionSpaceMap_comp_sectionSpaceIsoSubfunctor_hom :
    sectionSpaceMap hp ≫ (sectionSpaceIsoSubfunctor Z W w).hom =
      (sectionSpaceIsoSubfunctor Z W' w').hom ≫ sectionSubfunctorMap p hp := by
  ext T s
  apply Subtype.ext
  show (sectionsOverEquiv T.unop (sectionSpaceEquiv B U hU Z T.unop W w
      ((sectionSpaceMap hp).app T s))).1 =
    p.app _ (sectionsOverEquiv T.unop (sectionSpaceEquiv B U hU Z T.unop W' w' s)).1
  rw [sectionSpaceEquiv_sectionSpaceMap]
  show yonedaEquiv ((prodYonedaIso T.unop).hom ≫ (sectionSpaceEquiv B U hU Z T.unop W' w' s).1 ≫
      p) = p.app _ (yonedaEquiv ((prodYonedaIso T.unop).hom ≫
        (sectionSpaceEquiv B U hU Z T.unop W' w' s).1))
  rw [← Category.assoc, yonedaEquiv_comp]

end SubfunctorMap

/-! ### Surjectivity of a space of sections -/

/-- **The space of sections of a surjective étale `w : W ⟶ h_Z` over a finite `Z ⟶ U` is surjective
over `U`.** By Stacks 05XQ it has a point over a surjective étale `T ⟶ U`. -/
theorem isSurjective_sectionSpace {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    {w : W ⟶ yoneda.obj Z} (hW : IsAlgebraicSpace B U hU W) (hwS : Space.IsSurjective B U hU w)
    (hw : Space.IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    Space.IsSurjective B U hU (terminal.from (Space.sectionSpace B U hU Z W w)) := by
  obtain ⟨T, hTS, -, ⟨σ⟩⟩ := Space.exists_surjective_etale_sectionsOver B U hU Z W w hW hwS hw
  let φ : yoneda.obj T ⟶ Space.sectionSpace B U hU Z W w :=
    yonedaEquiv.symm ((Space.sectionSpaceEquiv B U hU Z T W w).symm σ)
  have hyoneda : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hU)))) :=
    (Over.mkIdTerminal (X := B.obj hU)).isTerminalObj yoneda _
  have hT : Space.IsSurjective B U hU (φ ≫ terminal.from _) := by
    rw [show φ ≫ terminal.from _ = yoneda.map (Space.toBase T) ≫
        (hyoneda.uniqueUpToIso terminalIsTerminal).hom from terminal.hom_ext _ _]
    refine Space.isSurjective_comp B U hU (Space.isSurjective_of_presheafSurjective B U hU _ ?_)
      (Space.isSurjective_of_isIso B U hU _)
    refine (Space.presheaf_yoneda_map_iff B U hU
      (inferInstance : MorphismProperty.IsStableUnderBaseChange
        (@_root_.AlgebraicGeometry.Surjective.{u})) _).2 ?_
    rw [Space.toScheme_map_toBase]
    exact hTS
  intro x
  obtain ⟨y, hy⟩ := hT x
  exact ⟨Space.pointsMap B U hU _ φ y, by rw [← hy, Space.pointsMap_comp_apply]⟩

/-! ### The fibre over a scheme-valued point -/

namespace SectionFibre

variable {Z : BigFppfOver B U hU} {W W' : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
  {w : W ⟶ yoneda.obj Z} {w' : W' ⟶ yoneda.obj Z} (p : W' ⟶ W) (hp : p ≫ w = w')
  {A : Scheme.{u}} {hA : B.Contains A} (a : B.obj hA ⟶ B.obj hU)

variable (Z) in
/-- The base change `Z_T = Z ×_U T` of `Z` along `a : T ⟶ U`, an object of the big fppf site of
`T`. -/
noncomputable abbrev cover : BigFppfOver B A hA := (Over.pullback a).obj Z

variable (Z) in
/-- The projection `Z_T ⟶ Z`, read over `U`. -/
noncomputable abbrev coverProj : (Over.map a).obj (cover Z a) ⟶ Z :=
  (Over.mapPullbackAdj a).counit.app Z

variable (Z) in
/-- For a morphism `z : Y ⟶ Z_T` of the site of `T`, the morphism `Y ⟶ Z × T` it determines, read
over `U`. -/
noncomputable def coverPair {Y : BigFppfOver B A hA} (z : Y ⟶ cover Z a) :
    (Over.map a).obj Y ⟶ Z ⨯ Over.mk a :=
  prod.lift ((Over.map a).map z ≫ coverProj Z a) (overMapTautHom a Y)

/-- `coverPair` is natural: precomposing `z` with `f : Y' ⟶ Y` precomposes the induced morphism
with the image of `f` over `U`. -/
theorem coverPair_comp {Y Y' : BigFppfOver B A hA} (f : Y' ⟶ Y) (z : Y ⟶ cover Z a) :
    coverPair Z a (f ≫ z) = (Over.map a).map f ≫ coverPair Z a z := by
  refine prod.hom_ext ?_ ?_
  · simp [coverPair, Functor.map_comp]
  · simp only [coverPair, prod.lift_snd, Category.assoc]
    exact (overMap_map_comp_overMapTautHom a f).symm

variable (σ : (sectionSubfunctor Z W w).toFunctor.obj (op (Over.mk a)))

/-- The morphism `h_{Z_T} ⟶ W|_T` named by a section `σ` of `W_T ⟶ Z_T`: a morphism `Y ⟶ Z_T`
of the site of `T` is sent to the restriction of `σ` along the induced morphism `Y ⟶ Z × T`. -/
noncomputable def point :
    yoneda.obj (cover Z a) ⟶ (relocalizeRestrict a).obj W where
  app Y := ↾fun z => W.map (coverPair Z a z).op σ.1
  naturality Y Y' f := by
    ext z
    change W.map (coverPair Z a (f.unop ≫ z)).op σ.1 =
      W.map ((Over.map a).map f.unop).op (W.map (coverPair Z a z).op σ.1)
    rw [coverPair_comp, op_comp]
    exact FunctorToTypes.map_comp_apply W _ _ σ.1

/-- **The presheaf `W'_σ = W' ×_{W, σ} Z_T`** on the big fppf site of `T`: a section over `Y` is a
section of `W'` over `Y` together with a morphism `Y ⟶ Z_T`, whose images in `W` agree. -/
noncomputable def total : (BigFppfOver B A hA)ᵒᵖ ⥤ Type u where
  obj Y := {x : W'.obj (op ((Over.map a).obj Y.unop)) × (Y.unop ⟶ cover Z a) //
    p.app _ x.1 = (point a σ).app Y x.2}
  map {Y Y'} f := ↾fun x => ⟨(W'.map ((Over.map a).map f.unop).op x.1.1, f.unop ≫ x.1.2), by
    change p.app _ (W'.map _ x.1.1) = (point a σ).app Y' ((yoneda.obj (cover Z a)).map f x.1.2)
    rw [NatTrans.naturality_apply, x.2, NatTrans.naturality_apply]
    rfl⟩
  map_id Y := by
    ext x
    · change W'.map ((Over.map a).map (𝟙 _)).op x.1.1 = x.1.1
      rw [(Over.map a).map_id, op_id]
      exact FunctorToTypes.map_id_apply W' x.1.1
    · simp
  map_comp {Y Y' Y''} f g := by
    ext x
    · change W'.map ((Over.map a).map (g.unop ≫ f.unop)).op x.1.1 =
        W'.map ((Over.map a).map g.unop).op (W'.map ((Over.map a).map f.unop).op x.1.1)
      rw [(Over.map a).map_comp, op_comp]
      exact FunctorToTypes.map_comp_apply W' _ _ x.1.1
    · simp

/-- The structure morphism `W'_σ ⟶ h_{Z_T}`. -/
noncomputable def proj : total p a σ ⟶ yoneda.obj (cover Z a) where
  app _ := ↾fun x => x.1.2
  naturality _ _ _ := rfl

/-- The projection `W'_σ ⟶ W'|_T`. -/
noncomputable def toRestrict : total p a σ ⟶ (relocalizeRestrict a).obj W' where
  app _ := ↾fun x => x.1.1
  naturality _ _ _ := rfl

/-- **`W'_σ` is the fibre product of `p|_T` and of the point named by `σ`.** -/
theorem isPullback_total :
    IsPullback (toRestrict p a σ) (proj p a σ) ((relocalizeRestrict a).map p) (point a σ) := by
  refine IsPullback.of_forall_isPullback_app fun Y => ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    exact x.2
  · rintro x x' ⟨h₁, h₂⟩
    exact Subtype.ext (Prod.ext h₁ h₂)
  · intro s z h
    exact ⟨⟨(s, z), h⟩, rfl, rfl⟩

/-! ### The comparison of products -/

variable (Z) in
/-- The comparison `(Z_T × Y) ⟶ Z × Y` of a product in the site of `T` with a product in the site
of `U`, for an object `Y` of the site of `T`. -/
noncomputable def prodComparison (Y : BigFppfOver B A hA) :
    (Over.map a).obj (cover Z a ⨯ Y) ⟶ Z ⨯ (Over.map a).obj Y :=
  prod.lift ((Over.map a).map prod.fst ≫ coverProj Z a) ((Over.map a).map prod.snd)

/-- The first component of `prodComparison` is the first projection followed by `Z_T ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem prodComparison_fst (Y : BigFppfOver B A hA) :
    prodComparison Z a Y ≫ prod.fst = (Over.map a).map prod.fst ≫ coverProj Z a :=
  prod.lift_fst _ _

/-- The second component of `prodComparison` is the second projection, read over `U`. -/
@[reassoc (attr := simp)]
theorem prodComparison_snd (Y : BigFppfOver B A hA) :
    prodComparison Z a Y ≫ prod.snd = (Over.map a).map prod.snd :=
  prod.lift_snd _ _

/-- `prodComparison` is natural in the object `Y` of the site of `T`. -/
theorem prodComparison_naturality {Y Y' : BigFppfOver B A hA} (f : Y' ⟶ Y) :
    (Over.map a).map (prod.map (𝟙 _) f) ≫ prodComparison Z a Y =
      prodComparison Z a Y' ≫ prod.map (𝟙 Z) ((Over.map a).map f) := by
  refine prod.hom_ext ?_ ?_
  · simp only [Category.assoc, prodComparison_fst, prod.map_fst, Category.comp_id,
      ← Functor.map_comp_assoc, prod.map_fst]
  · simp only [Category.assoc, prodComparison_snd, prod.map_snd, prodComparison_snd_assoc,
      ← Functor.map_comp]

/-- The comparison of products followed by the base change of the tautological morphism is the
morphism `Z_T × Y ⟶ Z × T` determined by the first projection. -/
theorem prodComparison_comp_prodMap_overMapTautHom (Y : BigFppfOver B A hA) :
    prodComparison Z a Y ≫ prod.map (𝟙 Z) (overMapTautHom a Y) =
      coverPair Z a (prod.fst : cover Z a ⨯ Y ⟶ cover Z a) := by
  refine prod.hom_ext ?_ ?_
  · simp [coverPair]
  · simp only [Category.assoc, prod.map_snd, prodComparison_snd_assoc, coverPair, prod.lift_snd]
    exact overMap_map_comp_overMapTautHom a _

/-- The square of schemes underlying `Z_T × Y` over `Z` and `Y ⟶ T ⟶ U` is cartesian. -/
theorem isPullback_prodComparison (Y : BigFppfOver B A hA) :
    IsPullback (((Over.map a).map prod.fst ≫ coverProj Z a).left)
      ((Over.map a).map (prod.snd : cover Z a ⨯ Y ⟶ Y)).left Z.hom (Y.hom ≫ a) := by
  have h₀ := (IsPullback.of_isLimit_binaryFan_of_isTerminal (prodIsProd (cover Z a) Y)
      Over.mkIdTerminal).map (Over.forget _)
  have e₁ : (Over.forget _).map (Over.mkIdTerminal.from ((pair (cover Z a) Y).obj
      ⟨WalkingPair.left⟩)) = (cover Z a).hom := by
    simp
  have e₂ : (Over.forget _).map (Over.mkIdTerminal.from ((pair (cover Z a) Y).obj
      ⟨WalkingPair.right⟩)) = Y.hom := by
    simp
  rw [e₁, e₂] at h₀
  have h₁ : IsPullback (prod.fst : cover Z a ⨯ Y ⟶ _).left (prod.snd : cover Z a ⨯ Y ⟶ Y).left
      (cover Z a).hom Y.hom := by
    simpa using h₀
  have he : ((Over.map a).map (prod.fst : cover Z a ⨯ Y ⟶ _) ≫ coverProj Z a).left =
      (prod.fst : cover Z a ⨯ Y ⟶ _).left ≫ pullback.fst Z.hom a := by
    simp [coverProj]
  rw [he]
  exact h₁.paste_horiz (IsPullback.of_hasPullback _ _)

/-- The comparison `(Z_T × Y) ⟶ Z × Y` of products is an isomorphism. -/
instance isIso_prodComparison (Y : BigFppfOver B A hA) : IsIso (prodComparison Z a Y) := by
  let hL := Stack.overBinaryFanIsLimit Z.hom ((Over.map a).obj Y)
    ((Over.map a).obj (cover Z a ⨯ Y)) ((Over.map a).map prod.snd)
    ((Over.map a).map prod.fst ≫ coverProj Z a) (isPullback_prodComparison a Y)
  let e := hL.conePointUniqueUpToIso (prodIsProd ((Over.map a).obj Y) Z)
  have he : prodComparison Z a Y = e.hom ≫ (prod.braiding _ _).hom := by
    refine prod.hom_ext ?_ ?_
    · simp only [prodComparison_fst, Category.assoc, prod.braiding_hom, prod.lift_fst]
      exact (hL.conePointUniqueUpToIso_hom_comp (prodIsProd _ _) ⟨WalkingPair.right⟩).symm
    · simp only [prodComparison_snd, Category.assoc, prod.braiding_hom, prod.lift_snd]
      exact (hL.conePointUniqueUpToIso_hom_comp (prodIsProd _ _) ⟨WalkingPair.left⟩).symm
  rw [he]
  infer_instance

/-! ### The fibre -/

section Elements

variable (s₀ : W.obj (op (Z ⨯ Over.mk a))) {Y : BigFppfOver B A hA}

/-- If the image under `p` of a section `x` of `W'` over `Z × Y` is the restriction of `s₀`, then
the image under `p` of the restriction of `x` along `prodComparison` is the restriction of `s₀`
along `coverPair Z a prod.fst`. -/
theorem map_prodComparison_mem (x : W'.obj (op (Z ⨯ (Over.map a).obj Y)))
    (hx : p.app _ x = W.map (prod.map (𝟙 Z) (overMapTautHom a Y)).op s₀) :
    p.app _ (W'.map (prodComparison Z a Y).op x) = W.map (coverPair Z a prod.fst).op s₀ := by
  rw [NatTrans.naturality_apply, hx, ← prodComparison_comp_prodMap_overMapTautHom, op_comp,
    FunctorToTypes.map_comp_apply]

/-- If the image under `p` of a section `x` of `W'` over `Z_T × Y` is the restriction of `s₀`
along `coverPair Z a prod.fst`, then the image under `p` of the restriction of `x` along the
inverse of `prodComparison` is the restriction of `s₀` to `Z × Y`. -/
theorem map_inv_prodComparison_mem (x : W'.obj (op ((Over.map a).obj (cover Z a ⨯ Y))))
    (hx : p.app _ x = W.map (coverPair Z a prod.fst).op s₀) :
    p.app _ (W'.map (inv (prodComparison Z a Y)).op x) =
      W.map (prod.map (𝟙 Z) (overMapTautHom a Y)).op s₀ := by
  rw [NatTrans.naturality_apply, hx, ← prodComparison_comp_prodMap_overMapTautHom, op_comp,
    FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp,
    IsIso.inv_hom_id, op_id, FunctorToTypes.map_id_apply]

include hp in
/-- If `s₀` lies over the first projection and the image under `p` of a section `x` of `W'` over
`Z_T × Y` is the restriction of `s₀` along `coverPair Z a prod.fst`, then the restriction of `x`
along the inverse of `prodComparison` lies over the first projection `Z × Y ⟶ Z`. -/
theorem map_inv_prodComparison_over (hs₀ : w.app _ s₀ = prod.fst)
    (x : W'.obj (op ((Over.map a).obj (cover Z a ⨯ Y))))
    (hx : p.app _ x = W.map (coverPair Z a prod.fst).op s₀) :
    w'.app _ (W'.map (inv (prodComparison Z a Y)).op x) = prod.fst := by
  rw [← hp]
  show w.app _ (p.app _ _) = _
  rw [map_inv_prodComparison_mem p a s₀ x hx, NatTrans.naturality_apply, hs₀]
  show prod.map (𝟙 Z) _ ≫ prod.fst = prod.fst
  simp

/-- Restricting a section of `W'` along `prodComparison` and then along its inverse gives back the
section. -/
theorem map_inv_map_prodComparison (x : W'.obj (op (Z ⨯ (Over.map a).obj Y))) :
    W'.map (inv (prodComparison Z a Y)).op (W'.map (prodComparison Z a Y).op x) = x := by
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
    FunctorToTypes.map_id_apply]

/-- Restricting a section of `W'` along the inverse of `prodComparison` and then along
`prodComparison` gives back the section. -/
theorem map_map_inv_prodComparison (x : W'.obj (op ((Over.map a).obj (cover Z a ⨯ Y)))) :
    W'.map (prodComparison Z a Y).op (W'.map (inv (prodComparison Z a Y)).op x) = x := by
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, IsIso.hom_inv_id, op_id,
    FunctorToTypes.map_id_apply]

/-- Restriction of sections of `W'` along `prodComparison` is natural in the object `Y` of the
site of `T`. -/
theorem map_prodComparison_naturality {Y' : BigFppfOver B A hA} (f : Y' ⟶ Y)
    (x : W'.obj (op (Z ⨯ (Over.map a).obj Y))) :
    W'.map (prodComparison Z a Y').op (W'.map (prod.map (𝟙 Z) ((Over.map a).map f)).op x) =
      W'.map ((Over.map a).map (prod.map (𝟙 _) f)).op (W'.map (prodComparison Z a Y).op x) := by
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
    prodComparison_naturality]

end Elements

/-- **The fibre of `sectionSubfunctorMap p` over the point named by `σ` is the subfunctor of
sections of `W'_σ ⟶ Z_T`**, on the big fppf site of `T`. -/
noncomputable def fibreIso :
    fibreOfSection a (sectionSubfunctorMap p hp) (yonedaEquiv.symm σ) ≅
      (sectionSubfunctor (cover Z a) (total p a σ) (proj p a σ)).toFunctor :=
  NatIso.ofComponents (fun Y => Equiv.toIso
    { toFun := fun x => ⟨⟨(W'.map (prodComparison Z a Y.unop).op x.1.1, prod.fst),
        map_prodComparison_mem p a σ.1 x.1.1 (congrArg Subtype.val x.2)⟩, rfl⟩
      invFun := fun x => ⟨⟨W'.map (inv (prodComparison Z a Y.unop)).op x.1.1.1,
        map_inv_prodComparison_over p hp a σ.1 σ.2 x.1.1.1 (x.2 ▸ x.1.2)⟩,
        Subtype.ext (map_inv_prodComparison_mem p a σ.1 x.1.1.1 (x.2 ▸ x.1.2))⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (map_inv_map_prodComparison a x.1.1))
      right_inv := fun x => Subtype.ext (Subtype.ext (Prod.ext
        (map_map_inv_prodComparison a x.1.1.1) x.2.symm)) }) (by
    intro Y Y' f
    ext x
    refine Subtype.ext (Subtype.ext (Prod.ext (map_prodComparison_naturality a f.unop x.1.1) ?_))
    exact (by simp : (prod.fst : cover Z a ⨯ Y'.unop ⟶ _) =
      prod.map (𝟙 (cover Z a)) f.unop ≫ prod.fst))

end SectionFibre

/-! ### The structural morphism of a lower-shriek extension -/

section Relocalize

variable {A : Scheme.{u}} {hA : B.Contains A} (a : B.obj hA ⟶ B.obj hU)
  {F : (BigFppfOver B A hA)ᵒᵖ ⥤ Type u}

/-- `toYonedaId` is the map to the terminal presheaf followed by the identification of the latter
with the representable presheaf of the identity. -/
private theorem toYonedaId_eq_terminal_from_comp :
    toYonedaId B A hA F = terminal.from F ≫ (((Over.mkIdTerminal (X := B.obj hA)).isTerminalObj
      yoneda _).uniqueUpToIso terminalIsTerminal).inv :=
  ((Over.mkIdTerminal (X := B.obj hA)).isTerminalObj yoneda _).hom_ext _ _

/-- **Étaleness over a smaller base is étaleness of the lower-shriek extension over its image.**
If an algebraic space over `T` is étale over `T`, its lower-shriek extension along `a : T ⟶ U` is
étale over the representable presheaf of `a`. -/
theorem isEtale_relocalizeToYoneda_of_isEtale (hF : IsAlgebraicSpace B A hA F)
    (h : IsEtale B A hA (terminal.from F)) :
    IsEtale B U hU (OverShriek.relocalizeToYoneda a F) := by
  have htoId : IsEtale B A hA (toYonedaId B A hA F) := by
    rw [toYonedaId_eq_terminal_from_comp]
    exact isEtale_comp B A hA h (isEtale_of_isIso B A hA _)
  refine (isEtale_iff_holdsOnEveryEtaleChart B U hU
    (isAlgebraicSpace_viewOver B A U hA hU a F hF) (isAlgebraicSpace_yoneda B U hU _) _).2 ?_
  refine (holdsOnEveryEtaleChart_relocalizeToYoneda_iff B A U hA hU a
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) F).2 ?_
  exact (isEtale_iff_holdsOnEveryEtaleChart B A hA hF (isAlgebraicSpace_yoneda B A hA _) _).1
    htoId

/-- **Surjectivity over a smaller base is surjectivity of the lower-shriek extension over its
image.** -/
theorem isSurjective_relocalizeToYoneda_of_isSurjective
    (h : IsSurjective B A hA (terminal.from F)) :
    IsSurjective B U hU (OverShriek.relocalizeToYoneda a F) := by
  have htoId : IsSurjective B A hA (toYonedaId B A hA F) := by
    rw [toYonedaId_eq_terminal_from_comp]
    exact isSurjective_comp B A hA h (isSurjective_of_isIso B A hA _)
  have := isIso_relocalizeToYoneda_yonedaId B A U hA hU a
  have h₄ := isSurjective_comp B U hU (isSurjective_relocalize B A hA U hU a _ htoId)
    (isSurjective_of_isIso B U hU
      (OverShriek.relocalizeToYoneda a (yoneda.obj (Over.mk (𝟙 (B.obj hA))))))
  rwa [relocalizeToYoneda_eq_map_toYonedaId B A U hA hU a F] at h₄

end Relocalize

/-! ### The fibres of the morphism of spaces of sections -/

section Fibres

variable {Z : BigFppfOver B U hU} {W W' : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
  {w : W ⟶ yoneda.obj Z} {w' : W' ⟶ yoneda.obj Z} (p : W' ⟶ W) (hp : p ≫ w = w')

/-- **The fibre of `sectionSubfunctorMap p` over a scheme-valued point.** Let `Z ⟶ U` be finite,
let `W'` and `W` be algebraic spaces and let `p : W' ⟶ W` be étale and surjective after every
base change to a scheme. Then the fibre of `sectionSubfunctorMap p` over a scheme-valued point is
an algebraic space, étale and surjective over the point.

The fibre is the lower-shriek extension of the space of sections of `W'_σ ⟶ Z_T` over `T`
(`AlgebraicGeometry.Space.SectionFibre.fibreIso` and
`CategoryTheory.OverShriek.isPullback_relocalizeFibreOfSectionMap`), and that space of sections is
an algebraic space étale over `T` by Stacks 05XR and surjective over `T` by Stacks 05XQ: `W'_σ`
is the base change of the restriction of `p` to the site of `T`. -/
theorem sectionSubfunctorMap_fibre
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    (hW : IsAlgebraicSpace B U hU W) (hW' : IsAlgebraicSpace B U hU W')
    (hpE : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B U hU)).presheaf p)
    (hpS : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B U hU)).presheaf p)
    (T : BigFppfOver B U hU) (ξ : yoneda.obj T ⟶ (sectionSubfunctor Z W w).toFunctor) :
    IsAlgebraicSpace B U hU (pullback ξ (sectionSubfunctorMap p hp)) ∧
      IsEtale B U hU (pullback.fst ξ (sectionSubfunctorMap p hp)) ∧
      IsSurjective B U hU (pullback.fst ξ (sectionSubfunctorMap p hp)) := by
  let a : B.obj T.left.2 ⟶ B.obj hU := T.hom
  obtain ⟨σ, rfl⟩ : ∃ σ : (sectionSubfunctor Z W w).toFunctor.obj (op (Over.mk a)),
      yonedaEquiv.symm σ = ξ := ⟨yonedaEquiv ξ, Equiv.symm_apply_apply _ _⟩
  let F := fibreOfSection a (sectionSubfunctorMap p hp) (yonedaEquiv.symm σ)
  have hpb := isPullback_relocalizeFibreOfSectionMap a (sectionSubfunctorMap p hp)
    (yonedaEquiv.symm σ)
  let e := hpb.flip.isoPullback
  have he := hpb.flip.isoPullback_hom_fst
  have _ : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u})
      (BigFppfOver.toScheme B T.left.1 T.left.2)).RespectsIso :=
    have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.Etale.{u}) :=
      MorphismProperty.RespectsIso.mk _ (fun e f hf => by
        let _ : _root_.AlgebraicGeometry.Etale f := hf
        infer_instance) (fun e f hf => by
        let _ : _root_.AlgebraicGeometry.Etale f := hf
        infer_instance)
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B T.left.1 T.left.2)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  -- the base change of `p` over the site of `T`
  have hrW : IsAlgebraicSpace B T.left.1 T.left.2 ((relocalizeRestrict a).obj W) :=
    isAlgebraicSpace_relocalizeRestrict B T.left.1 U T.left.2 hU a W hW
  have hrW' : IsAlgebraicSpace B T.left.1 T.left.2 ((relocalizeRestrict a).obj W') :=
    isAlgebraicSpace_relocalizeRestrict B T.left.1 U T.left.2 hU a W' hW'
  have htot := SectionFibre.isPullback_total p a σ
  have hTot : IsAlgebraicSpace B T.left.1 T.left.2 (SectionFibre.total p a σ) :=
    AlgebraicGeometry.isAlgebraicSpace_of_iso B T.left.1 T.left.2 htot.isoPullback
      (isAlgebraicSpace_pullback B T.left.1 T.left.2 _ _ hrW'
        (isAlgebraicSpace_yoneda B T.left.1 T.left.2 _) hrW)
  have hProjE : IsEtale B T.left.1 T.left.2 (SectionFibre.proj p a σ) :=
    isEtale_of_presheaf_etale B T.left.1 T.left.2 (presheaf_of_isPullback B T.left.1 T.left.2
      htot (OverShriek.relative_relocalizeRestrict_map a
        (inverseImage_restrictReindexSnd B T.left.1 U T.left.2 hU a
          (@_root_.AlgebraicGeometry.Etale.{u})) hpE))
  have hProjS : IsSurjective B T.left.1 T.left.2 (SectionFibre.proj p a σ) :=
    isSurjective_of_presheafSurjective B T.left.1 T.left.2 _ (presheaf_of_isPullback B T.left.1
      T.left.2 htot (OverShriek.relative_relocalizeRestrict_map a
        (inverseImage_restrictReindexSnd B T.left.1 U T.left.2 hU a
          (@_root_.AlgebraicGeometry.Surjective.{u})) hpS))
  have hcover : _root_.AlgebraicGeometry.IsFinite
      (B.inclusion.map (SectionFibre.cover Z a).hom) :=
    MorphismProperty.of_isPullback ((IsPullback.of_hasPullback Z.hom a).map B.inclusion) hZfin
  -- Stacks 05XR and Stacks 05XQ over `T`
  have h05XR := isAlgebraicSpace_sectionSpace_and_isEtale hTot hProjE hcover
  have h05XQ := isSurjective_sectionSpace hTot hProjS hProjE hcover
  let eF : F ≅ sectionSpace B T.left.1 T.left.2 (SectionFibre.cover Z a)
      (SectionFibre.total p a σ) (SectionFibre.proj p a σ) :=
    SectionFibre.fibreIso p hp a σ ≪≫ (sectionSpaceIsoSubfunctor _ _ _).symm
  have hF : IsAlgebraicSpace B T.left.1 T.left.2 F :=
    AlgebraicGeometry.isAlgebraicSpace_of_iso B T.left.1 T.left.2 eF h05XR.1
  have hterm : terminal.from F = eF.hom ≫ terminal.from _ := terminal.hom_ext _ _
  have hFE : IsEtale B T.left.1 T.left.2 (terminal.from F) := by
    rw [hterm]
    exact isEtale_comp B T.left.1 T.left.2 (isEtale_of_isIso B T.left.1 T.left.2 _) h05XR.2
  have hFS : IsSurjective B T.left.1 T.left.2 (terminal.from F) := by
    rw [hterm]
    exact isSurjective_comp B T.left.1 T.left.2 (isSurjective_of_isIso B T.left.1 T.left.2 _)
      h05XQ
  have hfst : pullback.fst (yonedaEquiv.symm σ) (sectionSubfunctorMap p hp) =
      e.inv ≫ OverShriek.relocalizeToYoneda a F := by
    rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨AlgebraicGeometry.isAlgebraicSpace_of_iso B U hU e.symm
    (isAlgebraicSpace_viewOver B T.left.1 U T.left.2 hU a F hF), ?_, ?_⟩
  · rw [hfst]
    exact isEtale_comp B U hU (isEtale_of_isIso B U hU _)
      (isEtale_relocalizeToYoneda_of_isEtale a hF hFE)
  · rw [hfst]
    exact isSurjective_comp B U hU (isSurjective_of_isIso B U hU _)
      (isSurjective_relocalizeToYoneda_of_isSurjective a hFS)

end Fibres

end AlgebraicGeometry.Space

end
