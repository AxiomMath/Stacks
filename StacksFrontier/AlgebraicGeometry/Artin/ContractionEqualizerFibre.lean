module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionWitnessComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseSubspaces

/-!
# The functor of the equalizer situation of Stacks 0GHD

In the situation of Stacks 0GH8 let `V` be a locally Noetherian scheme over `S` and let
`(Z₁, u'₁, x̂₁)`, `(Z₂, u'₂, x̂₂)` be two elements of `F(V)` with chosen compatibility witnesses
(the data `d` of `AlgebraicGeometry.Artin.ContractionEqualizer`). Assertion (4) of Stacks 0GHD
(`AlgebraicGeometry.Artin.ContractionEqualizer.situation`) makes `E'`, `(E' ⟶ V)⁻¹ Z` and
`E'_{/Z} ⟶ E_W` a situation as in Stacks 0GH8 over the base `V`.

This file identifies the functor `F_{(4)}` of that situation (Stacks 0GHA over `V`) on a scheme
`A` over `V` with the fibre `F ×_{Δ, F × F} V` evaluated at `A`, that is, with the set of
elements of `F(A)` which are the restriction of both given triples. Concretely, an element
`(Z_A, u_A, x̂_A)` of `F_{(4)}(A)` exists exactly when the two triples restrict to the same
element of `F(A)`, and then it is unique:

* the closed set `Z_A` is forced to be `φ⁻¹ Z`, `φ : A ⟶ V` the structure morphism, because
  `u_A` lands in `E' ×_V (V ∖ Z)` and `x̂_A` in `E_W ⊆ V_{/Z}`;
* `u_A` and `x̂_A` are then factorizations of `A ∖ φ⁻¹ Z ⟶ V ∖ Z` through `E' ×_V (V ∖ Z)` and
  of `A_{/φ⁻¹ Z} ⟶ V_{/Z}` through `E_W`, which are unique by assertion (2) and because `E_W` is
  an equalizer, and which exist exactly when the triples agree on `A` by assertion (5).

## Main definitions

* `AlgebraicGeometry.Artin.ContractionEqualizer.diagonalFibre`: the fibre `F ×_{Δ, F × F} V` on
  the locally Noetherian schemes over `V`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.contractionFunctorSituationIso`: the functor of
  the situation of assertion (4) is isomorphic to `F ×_{Δ, F × F} V`.

## Main results

* `AlgebraicGeometry.Artin.ContractionEqualizer.factorsOffCenter_and_factorsEW_of_triple`: an
  element of `F_{(4)}(A)` gives the two factorizations of assertion (5)(b).
* `AlgebraicGeometry.Artin.ContractionEqualizer.subsingleton_triple_situation`: `F_{(4)}(A)` has
  at most one element.
* `AlgebraicGeometry.Artin.ContractionEqualizer.nonempty_triple_situation_of_mapTriple_eq`: an
  element of `F_{(4)}(A)` exists when the two triples agree on `A`; its compatibility witness is
  the base change to `V` of `A ×_V V'₁ ⟶ A` with its morphism to `E'`
  (`AlgebraicGeometry.Artin.ContractionSituation.CompatibilityWitness.exists_hom`, Stacks 0GDU).

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of presheaves `e : P ≅ Q` identifies the subfunctor of `P` cut out by the
inverse image of a set `W'` of points of `Q` with the subfunctor of `Q` cut out by `W'`. -/
def openSubspaceOfPointsIsoOfIso {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : P ≅ Q)
    (W : Set (points B S hS P)) (W' : Set (points B S hS Q))
    (hW : W = pointsMap B S hS P e.hom ⁻¹' W') :
    (openSubspaceOfPoints B S hS P W).toFunctor ≅ (openSubspaceOfPoints B S hS Q W').toFunctor where
  hom := openSubspaceOfPointsRestrict B S hS e.hom W W' hW.subset
  inv := openSubspaceOfPointsRestrict B S hS e.inv W' W (by
    intro x hx
    have h := congrFun (congrArg (pointsMap B S hS Q) e.inv_hom_id) x
    rw [pointsMap_comp, pointsMap_id] at h
    change pointsMap B S hS Q e.inv x ∈ W
    rw [hW]
    change pointsMap B S hS P e.hom (pointsMap B S hS Q e.inv x) ∈ W'
    rw [show pointsMap B S hS P e.hom (pointsMap B S hS Q e.inv x) = x from h]
    exact hx)
  hom_inv_id := by
    ext U x
    exact Subtype.ext (congrFun (congrArg (fun k => k.app U) e.hom_inv_id) x.1)
  inv_hom_id := by
    ext U x
    exact Subtype.ext (congrFun (congrArg (fun k => k.app U) e.inv_hom_id) x.1)

/-- An isomorphism of presheaves `e : P ≅ Q` identifies the completion of `P` along the inverse
image of a set `T'` of points of `Q` with the completion of `Q` along `T'`. -/
def completionSheafIsoOfIso {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : P ≅ Q)
    (T : Set (points B S hS P)) (T' : Set (points B S hS Q))
    (hT : T = pointsMap B S hS P e.hom ⁻¹' T') :
    completionSheaf B S hS P T ≅ completionSheaf B S hS Q T' :=
  have hinv : T' ⊆ pointsMap B S hS Q e.inv ⁻¹' T := by
    intro x hx
    have h := congrFun (congrArg (pointsMap B S hS Q) e.inv_hom_id) x
    rw [pointsMap_comp, pointsMap_id] at h
    change pointsMap B S hS Q e.inv x ∈ T
    rw [hT]
    change pointsMap B S hS P e.hom (pointsMap B S hS Q e.inv x) ∈ T'
    rw [show pointsMap B S hS P e.hom (pointsMap B S hS Q e.inv x) = x from h]
    exact hx
  { hom := completionSheafRestrict B S hS e.hom T T' hT.subset
    inv := completionSheafRestrict B S hS e.inv T' T hinv
    hom_inv_id := by
      rw [completionSheafRestrict_comp_eq B S hS e.hom e.inv (𝟙 P) e.hom_inv_id T T' T _ _
        (subset_preimage_pointsMap_id B S hS subset_rfl), completionSheafRestrict_id]
    inv_hom_id := by
      rw [completionSheafRestrict_comp_eq B S hS e.inv e.hom (𝟙 Q) e.inv_hom_id T' T T' _ _
        (subset_preimage_pointsMap_id B S hS subset_rfl), completionSheafRestrict_id] }

/-- A morphism whose composite with `f` lands in the subfunctor cut out by `W` lands in the
subfunctor cut out by the inverse image of `W` under `f`. -/
theorem range_le_openSubspaceOfPoints_preimage {P F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (m : P ⟶ F) (f : F ⟶ G) (W : Set (points B S hS G))
    (h : Subfunctor.range (m ≫ f) ≤ openSubspaceOfPoints B S hS G W) :
    Subfunctor.range m ≤ openSubspaceOfPoints B S hS F (pointsMap B S hS F f ⁻¹' W) := by
  rintro U _ ⟨s, rfl⟩ _ ⟨w, rfl⟩
  have hw := h U ⟨s, rfl⟩ ⟨w, rfl⟩
  rw [show (m ≫ f).app U s = f.app U (m.app U s) from rfl, ← yonedaEquiv_symm_naturality_right,
    pointsMap_comp] at hw
  exact hw

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- Morphisms into the sheaf over `V` attached to a sheaf `X` over the representable sheaf of
`g : V ⟶ S` are the morphisms over `V` into `X` from the attached sheaves. -/
def smallerBaseSheafOfHomEquiv (G : FppfSheaf B V hV) (X : FppfSheaf B S hS)
    (p : X ⟶ smallerBaseTarget B V S hV hS g) :
    (G ⟶ smallerBaseSheafOf B V S hV hS g X p) ≃
      {f : (smallerBaseSheafFunctor B V S hV hS g).obj G ⟶ X //
        f ≫ p = smallerBaseStr B V S hV hS g G} where
  toFun h := ⟨(smallerBaseSheafFunctor B V S hV hS g).map h ≫
      (smallerBaseSheafOfIso B V S hV hS g X p).hom, by
    rw [Category.assoc, smallerBaseSheafOfIso_hom_comp, smallerBaseSheafFunctor_map_comp_str]⟩
  invFun f := smallerBaseLift B V S hV hS g (f.1 ≫ (smallerBaseSheafOfIso B V S hV hS g X p).inv)
    (by
      have e : (smallerBaseSheafOfIso B V S hV hS g X p).inv ≫
          smallerBaseStr B V S hV hS g (smallerBaseSheafOf B V S hV hS g X p) = p := by
        rw [Iso.inv_comp_eq, smallerBaseSheafOfIso_hom_comp]
      rw [Category.assoc, e, f.2])
  left_inv h := (smallerBaseSheafFunctor B V S hV hS g).map_injective (by
    rw [smallerBaseSheafFunctor_map_smallerBaseLift, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])
  right_inv f := Subtype.ext (by
    simp only [smallerBaseSheafFunctor_map_smallerBaseLift, Category.assoc, Iso.inv_hom_id,
      Category.comp_id])

end FormalSpace

namespace Artin.ContractionEqualizer

open ContractionSituation FormalSpace

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V) (hVN : IsLocallyNoetherian V.left.obj)

/-- The structure morphism `φ : A ⟶ V` of an object `A` of the big fppf site of `V`, as a morphism
of the big fppf site of `S`. -/
abbrev toV (A : BigFppfOver B V.left.obj V.left.property) : (Over.map V.hom).obj A ⟶ V :=
  Space.smallerBaseStructureHom B V.left.obj S V.left.property hS V.hom A

/-- The identification of the points of `A` over `V` with the points of `A` over `S`. -/
def pointsOver (A : BigFppfOver B V.left.obj V.left.property) :
    Space.points B V.left.obj V.left.property (yoneda.obj A) ≃ₜ
      Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A)) :=
  (Space.pointsHomeomorphOfIso B V.left.obj V.left.property
    (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A)).trans
    (Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
      (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A))

/-- The subfunctor of `A` over `V` cut out by the inverse image of the complement of `Zs ⊆ |A|`
is attached to the subfunctor `A ∖ Zs` of `A` over `S`, with its morphism to `V`. -/
def openOverIso (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A)))) :
    (Space.openSubspaceOfPoints B V.left.obj V.left.property (yoneda.obj A)
        (pointsOver A ⁻¹' Zs)ᶜ).toFunctor ≅
      (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.obj
        (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
          Zsᶜ).ι ≫ yoneda.map (toV A))) :=
  Space.openSubspaceOfPointsIsoOfIso B V.left.obj V.left.property
      (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A)
      (pointsOver A ⁻¹' Zs)ᶜ _ rfl ≪≫
    Space.smallerBaseInverseOpenIso B V.left.obj S V.left.property hS V.hom
      (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) Zsᶜ

/-- `openOverIso A Zs`, followed by the image of the inclusion `A ∖ Zs ⟶ A` under the inverse of
the comparison of presheaves over `V` with presheaves over `S` with a morphism to `V`, is the
inclusion of the open subfunctor of `A` over `V`, followed by the identification of `A` with the
image of `A` over `S`. -/
theorem openOverIso_hom_comp (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A)))) :
    (openOverIso A Zs).hom ≫
        (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map
          (Over.homMk (Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
            Zsᶜ).ι : Over.mk ((Space.openSubspaceOfPoints B S hS
              (yoneda.obj ((Over.map V.hom).obj A)) Zsᶜ).ι ≫ yoneda.map (toV A)) ⟶
                Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) =
      (Space.openSubspaceOfPoints B V.left.obj V.left.property (yoneda.obj A)
          (pointsOver A ⁻¹' Zs)ᶜ).ι ≫
        (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A).hom := rfl

/-- The second components of the triples of the situation of assertion (4) over `A`, with first
component the inverse image of `Zs ⊆ |A|`, are the morphisms `A ∖ Zs ⟶ E' ∖ (E' ⟶ V)⁻¹ Z` over
`V`. -/
def uEquiv (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A)))) :
    ((Space.openSubspaceOfPoints B V.left.obj V.left.property (yoneda.obj A)
        (pointsOver A ⁻¹' Zs)ᶜ).toFunctor ⟶ (d.situation hVN).U'.toFunctor) ≃
      ((Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
          Zsᶜ).ι ≫ yoneda.map (toV A)) :
            Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
        Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase)) :=
  ((openOverIso A Zs).homCongr
    (Space.smallerBaseInverseOpenIso B V.left.obj S V.left.property hS V.hom d.E'OverV
      d.centerEqzᶜ)).trans
    (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS
      V.hom).fullyFaithfulInverse.homEquiv.symm

/-- The inverse of `uEquiv A Zs` sends a morphism `k` over `V` to its image under the inverse of
the comparison of presheaves, conjugated by `openOverIso A Zs` and the identification of the open
subspaces of `E'`. -/
theorem uEquiv_symm_apply (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A))))
    (k : (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
          Zsᶜ).ι ≫ yoneda.map (toV A)) :
            Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
        Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase)) :
    (d.uEquiv hVN A Zs).symm k = (openOverIso A Zs).hom ≫
      (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map k ≫
        (Space.smallerBaseInverseOpenIso B V.left.obj S V.left.property hS V.hom d.E'OverV
          d.centerEqzᶜ).inv := rfl

/-- The third components of the triples of the situation of assertion (4) over `A`, with first
component the inverse image of `Zs ⊆ |A|`, are the morphisms `A_{/Zs} ⟶ E_W` over `V`. -/
def xhatEquiv (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A)))) :
    (Space.completionSheaf B V.left.obj V.left.property (yoneda.obj A) (pointsOver A ⁻¹' Zs) ⟶
        (d.situation hVN).W) ≃
      {l : Space.completionSheaf B S hS (yoneda.obj ((Over.map V.hom).obj A)) Zs ⟶ d.EW //
        (l ≫ d.EWToTarget).hom =
          Space.completionSheafToSmallerBase B V.left.obj S V.left.property hS V.hom
            (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) Zs
            (isAlgebraicSpace_yoneda B S hS _)} :=
  let e := smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom
    (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
    (isAlgebraicSpace_yoneda B S hS _) Zs
  have he := smallerBaseCompletionIso_hom_comp B V.left.obj S V.left.property hS V.hom
    (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
    (isAlgebraicSpace_yoneda B S hS _) Zs
  ((Space.completionSheafIsoOfIso B V.left.obj V.left.property
      (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A)
      (pointsOver A ⁻¹' Zs) _ rfl).homCongr (Iso.refl _)).trans <|
    (smallerBaseSheafOfHomEquiv B V.left.obj S V.left.property hS V.hom _ d.EW
      d.EWToTarget).trans
    { toFun := fun f => ⟨e.inv ≫ f.1, by
        have h1 : ((e.inv ≫ f.1) ≫ d.EWToTarget).hom =
            e.inv.hom ≫ (smallerBaseStr B V.left.obj S V.left.property hS V.hom _).hom :=
          congrArg (fun k => k.hom) ((Category.assoc _ _ _).trans (congrArg (e.inv ≫ ·) f.2))
        refine h1.trans ((congrArg (e.inv.hom ≫ ·) he.symm).trans ?_)
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
          (congrArg (fun k => k.hom) e.inv_hom_id)).trans (Category.id_comp _))⟩
      invFun := fun l => ⟨e.hom ≫ l.1, by
        apply ObjectProperty.hom_ext
        have h2 : ((e.hom ≫ l.1) ≫ d.EWToTarget).hom = e.hom.hom ≫ (l.1 ≫ d.EWToTarget).hom := by
          rw [Category.assoc]
          rfl
        exact h2.trans ((congrArg (e.hom.hom ≫ ·) l.2).trans he)⟩
      left_inv := fun f => Subtype.ext (Iso.hom_inv_id_assoc e f.1)
      right_inv := fun l => Subtype.ext (Iso.inv_hom_id_assoc e l.1) }

/-- `E_W ⟶ V` is the composite `E_W ⟶ V_{/Z} ⟶ V`. -/
theorem EWToTarget_eq : d.EWToTarget = equalizer.ι d.xhat₁ d.xhat₂ ≫ toAmbient d.Z :=
  ObjectProperty.hom_ext _ d.EWToTarget_hom

omit d in
/-- The morphism `A_{/T} ⟶ V` from a completion of `A`, for `A` an object over `V`, is the
morphism into `A` followed by `A ⟶ V`. -/
theorem completionSheafToSmallerBase_yonedaOver (A : BigFppfOver B V.left.obj V.left.property)
    (T : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A)))) :
    Space.completionSheafToSmallerBase B V.left.obj S V.left.property hS V.hom
        (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) T
        (isAlgebraicSpace_yoneda B S hS _) =
      Space.completionSheafToAmbient B S hS (yoneda.obj ((Over.map V.hom).obj A))
          (isSheaf_comp_uliftFunctor B S hS (isAlgebraicSpace_yoneda B S hS _)) T ≫
        Functor.whiskerRight (yoneda.map (toV A)) uliftFunctor.{u + 1} := by
  rw [Space.completionSheafToAmbient_eq B S hS (isAlgebraicSpace_yoneda B S hS _).isSheaf]
  rfl

/-- A morphism `l` into `E_W` factors `A_{/φ⁻¹ Z} ⟶ V_{/Z}` exactly when it lies over `V` as
`A_{/φ⁻¹ Z} ⟶ V`. -/
private theorem comp_ι_eq_restrict_iff (A : BigFppfOver B V.left.obj V.left.property)
    (l : Space.completionSheaf B S hS (yoneda.obj ((Over.map V.hom).obj A)) (d.preZ (toV A)) ⟶
      d.EW) :
    l ≫ equalizer.ι d.xhat₁ d.xhat₂ =
      Space.completionSheafRestrict B S hS (yoneda.map (toV A)) (d.preZ (toV A)) d.Z
        Set.Subset.rfl ↔
    (l ≫ d.EWToTarget).hom =
      Space.completionSheafToSmallerBase B V.left.obj S V.left.property hS V.hom
        (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) (d.preZ (toV A))
        (isAlgebraicSpace_yoneda B S hS _) := by
  have hAsp := isAlgebraicSpace_yoneda B S hS ((Over.map V.hom).obj A)
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have key := (Space.completionSheafRestrict_comp_completionSheafToAmbient B S hS
    (yoneda.map (toV A)) _ d.Z Set.Subset.rfl (isSheaf_comp_uliftFunctor B S hS hAsp)
    (isSheaf_comp_uliftFunctor B S hS hVsp)).trans
      (completionSheafToSmallerBase_yonedaOver A _).symm
  rw [← cancel_mono (toAmbient d.Z), Category.assoc, ← EWToTarget_eq]
  exact ⟨fun hl => by rw [hl]; exact key, fun hl => ObjectProperty.hom_ext _ (hl.trans key.symm)⟩

/-- **The components of an element of `F_{(4)}(A)`.** For an object `A` over `V` with structure
morphism `φ : A ⟶ V`, a second and a third component `u`, `x̂` of a triple of the situation of
assertion (4) over `A` with first component the inverse image of `Zs ⊆ |A|` force `Zs = φ⁻¹ Z`,
and give the two factorizations of assertion (5)(b): `u` lands in `E' ∖ (E' ⟶ V)⁻¹ Z` over `V`,
which forces `φ⁻¹ Z ⊆ Zs` and factors `A ∖ φ⁻¹ Z ⟶ V ∖ Z` through `E' ×_V (V ∖ Z)`, and `x̂` is
a morphism `A_{/Zs} ⟶ E_W ⊆ V_{/Z}` over `V`, which forces `Zs ⊆ φ⁻¹ Z`
(`AlgebraicGeometry.Space.subset_preimage_of_completionSheaf_hom`) and factors
`A_{/φ⁻¹ Z} ⟶ V_{/Z}` through `E_W`. -/
theorem preZ_eq_and_factors (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A))))
    (u : (Space.openSubspaceOfPoints B V.left.obj V.left.property (yoneda.obj A)
        (pointsOver A ⁻¹' Zs)ᶜ).toFunctor ⟶ (d.situation hVN).U'.toFunctor)
    (xhat : Space.completionSheaf B V.left.obj V.left.property (yoneda.obj A)
        (pointsOver A ⁻¹' Zs) ⟶ (d.situation hVN).W) :
    Zs = d.preZ (toV A) ∧ d.FactorsOffCenter (toV A) ∧ d.FactorsEW (toV A) := by
  let k := d.uEquiv hVN A Zs u
  have hk : k.left ≫ (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase =
      (Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A)) Zsᶜ).ι ≫
        yoneda.map (toV A) := Over.w k
  obtain ⟨l, hl⟩ := d.xhatEquiv hVN A Zs xhat
  have hAs := isAlgebraicSpace_yoneda B S hS ((Over.map V.hom).obj A)
  have hVs := isAlgebraicSpace_yoneda B S hS V
  have hl' : (l ≫ equalizer.ι d.xhat₁ d.xhat₂).hom ≫
      Space.completionSheafToAmbient B S hS (yoneda.obj V) (isSheaf_comp_uliftFunctor B S hS hVs)
        d.Z =
      Space.completionSheafToAmbient B S hS (yoneda.obj ((Over.map V.hom).obj A))
          (isSheaf_comp_uliftFunctor B S hS hAs) Zs ≫
        Functor.whiskerRight (yoneda.map (toV A)) uliftFunctor.{u + 1} := by
    have h0 : (l ≫ equalizer.ι d.xhat₁ d.xhat₂).hom ≫
        Space.completionSheafToAmbient B S hS (yoneda.obj V)
          (isSheaf_comp_uliftFunctor B S hS hVs) d.Z = (l ≫ d.EWToTarget).hom := by
      rw [EWToTarget_eq]
      rfl
    exact h0.trans (hl.trans (completionSheafToSmallerBase_yonedaOver A Zs))
  have h2 : Zs ⊆ d.preZ (toV A) :=
    Space.subset_preimage_of_completionSheaf_hom B S hS
      (isSheaf_comp_uliftFunctor B S hS hAs) hVs.isSheaf (isSheaf_comp_uliftFunctor B S hS hVs)
      (yoneda.map (toV A)) _ hl'
  have h1 : d.preZ (toV A) ⊆ Zs := by
    intro x hx
    by_contra hxs
    obtain ⟨y, rfl⟩ : x ∈ Set.range (Space.pointsMap B S hS _
        (Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A)) Zsᶜ).ι) := by
      rw [Space.range_pointsMap_ι_openSubspaceOfPoints]
      exact hxs
    have hmem : Space.pointsMap B S hS _ (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι
        (Space.pointsMap B S hS _ k.left y) ∈ d.centerEqzᶜ :=
      (Space.range_pointsMap_ι_openSubspaceOfPoints B S hS d.centerEqzᶜ).subset ⟨_, rfl⟩
    have h := congrFun (congrArg (Space.pointsMap B S hS _) hk) y
    simp only [Space.pointsMap_comp, Function.comp_apply] at h
    exact hmem ((congrArg (· ∈ d.Z) h).mpr hx)
  have hZ : Zs = d.preZ (toV A) := h2.antisymm h1
  subst hZ
  refine ⟨rfl, ⟨Limits.pullback.lift (k.left ≫ (Space.openSubspaceOfPoints B S hS d.eqz
    d.centerEqzᶜ).ι) (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (toV A))
      (d.preZ (toV A))ᶜ d.Zᶜ Set.Subset.rfl) ?_, Limits.pullback.lift_snd _ _ _⟩, ⟨l, ?_⟩⟩
  · rw [Category.assoc, hk]
    rfl
  · exact (d.comp_ι_eq_restrict_iff A l).2 hl

/-- A set of points of `A` over `V` is the inverse image of a set of points of `A` over `S`. -/
theorem exists_eq_preimage_pointsOver (A : BigFppfOver B V.left.obj V.left.property)
    (Z : Set (Space.points B V.left.obj V.left.property (yoneda.obj A))) :
    ∃ Zs, Z = pointsOver (hS := hS) (V := V) A ⁻¹' Zs :=
  ⟨(pointsOver A).symm ⁻¹' Z, by ext x; simp⟩

/-- **An element of `F_{(4)}(A)` gives the two factorizations of assertion (5)(b).** -/
theorem factorsOffCenter_and_factorsEW_of_triple (A : BigFppfOver B V.left.obj V.left.property)
    (τ : Triple (d.situation hVN) A) : d.FactorsOffCenter (toV A) ∧ d.FactorsEW (toV A) := by
  obtain ⟨Z, -, u, xhat, -, -⟩ := τ
  obtain ⟨Zs, rfl⟩ := exists_eq_preimage_pointsOver A Z
  exact (d.preZ_eq_and_factors hVN A Zs u xhat).2

/-- **An element of `F_{(4)}(A)` makes the two triples agree on `A`**, by assertion (5). -/
theorem mapTriple_eq_of_triple (A : BigFppfOver B V.left.obj V.left.property)
    (τ : Triple (d.situation hVN) A) : mapTriple c (toV A) d.t₁ = mapTriple c (toV A) d.t₂ :=
  (d.mapTriple_eq_iff_factorsOffCenter_and_factorsEW (toV A)).2
    (d.factorsOffCenter_and_factorsEW_of_triple hVN A τ)

/-- The morphisms `A ∖ φ⁻¹ Z ⟶ E' ∖ (E' ⟶ V)⁻¹ Z` over `V` are unique: composed with
`E' ∖ (E' ⟶ V)⁻¹ Z ⟶ E'` they factor `A ∖ φ⁻¹ Z ⟶ V ∖ Z` through `E' ×_V (V ∖ Z)`, whose
morphism to `V ∖ Z` is a monomorphism by assertion (2). -/
theorem eq_of_hom_offCenter (A : BigFppfOver B V.left.obj V.left.property)
    (k k' : (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
          (d.preZ (toV A))ᶜ).ι ≫ yoneda.map (toV A)) :
            Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
        Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase)) :
    k = k' := by
  have hc : ∀ k : (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
          (d.preZ (toV A))ᶜ).ι ≫ yoneda.map (toV A)) :
            Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
        Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase),
      (k.left ≫ (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι) ≫ d.toBase =
        Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (toV A)) (d.preZ (toV A))ᶜ d.Zᶜ
          Set.Subset.rfl ≫ d.offCenter.ι := by
    intro k
    exact (Category.assoc _ _ _).trans (Over.w k)
  have := d.mono_pullbackSnd_offCenter
  have heq : Limits.pullback.lift _ _ (hc k) = Limits.pullback.lift _ _ (hc k') :=
    (cancel_mono (Limits.pullback.snd d.toBase d.offCenter.ι)).1 (by
      rw [Limits.pullback.lift_snd, Limits.pullback.lift_snd])
  apply Over.OverMorphism.ext
  rw [← cancel_mono (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι,
    ← Limits.pullback.lift_fst _ _ (hc k), heq, Limits.pullback.lift_fst]

/-- The morphisms `A_{/Zs} ⟶ E_W` over `V` are unique: `E_W ⟶ V_{/Z}` and `V_{/Z} ⟶ V` are
monomorphisms. -/
theorem eq_of_hom_EW (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A))))
    (l l' : {l : Space.completionSheaf B S hS (yoneda.obj ((Over.map V.hom).obj A)) Zs ⟶ d.EW //
        (l ≫ d.EWToTarget).hom =
          Space.completionSheafToSmallerBase B V.left.obj S V.left.property hS V.hom
            (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) Zs
            (isAlgebraicSpace_yoneda B S hS _)}) : l = l' := by
  have : Mono d.EWToTarget := by
    rw [EWToTarget_eq]
    infer_instance
  exact Subtype.ext ((cancel_mono d.EWToTarget).1 (ObjectProperty.hom_ext _ (l.2.trans l'.2.symm)))

/-- **`F_{(4)}(A)` has at most one element.** -/
theorem subsingleton_triple_situation (A : BigFppfOver B V.left.obj V.left.property) :
    Subsingleton (Triple (d.situation hVN) A) := by
  refine ⟨fun ⟨Z, hZc, u, xhat, ha, hw⟩ ⟨Z', hZc', u', xhat', ha', hw'⟩ => ?_⟩
  obtain ⟨Zs, rfl⟩ := exists_eq_preimage_pointsOver A Z
  obtain ⟨Zs', rfl⟩ := exists_eq_preimage_pointsOver A Z'
  obtain ⟨rfl, -, -⟩ := d.preZ_eq_and_factors hVN A Zs u xhat
  obtain ⟨rfl, -, -⟩ := d.preZ_eq_and_factors hVN A Zs' u' xhat'
  obtain rfl : u = u' := (d.uEquiv hVN A _).injective (d.eq_of_hom_offCenter A _ _)
  obtain rfl : xhat = xhat' := (d.xhatEquiv hVN A _).injective (d.eq_of_hom_EW A _ _ _)
  rfl

/-- The composite of the second component `(uEquiv A Zs).symm k` with `U' ⟶ X'`. -/
theorem uEquiv_symm_apply_comp_ι (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A))))
    (k : (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
          Zsᶜ).ι ≫ yoneda.map (toV A)) :
            Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
        Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase)) :
    (d.uEquiv hVN A Zs).symm k ≫ (d.situation hVN).U'.ι =
      (openOverIso A Zs).hom ≫
        (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map
          (k ≫ (Over.homMk (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι rfl :
            (Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase) :
              Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
                d.E'OverV)) := by
  have hβ : (Space.smallerBaseInverseOpenIso B V.left.obj S V.left.property hS V.hom d.E'OverV
      d.centerEqzᶜ).inv ≫ (d.situation hVN).U'.ι =
      (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map
        (Over.homMk (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι rfl :
          (Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase) :
            Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶ d.E'OverV) :=
    (Iso.inv_comp_eq _).2 (Space.smallerBaseInverseOpenIso_hom_comp B V.left.obj S
      V.left.property hS V.hom d.E'OverV d.centerEqzᶜ).symm
  exact (congrArg (· ≫ (d.situation hVN).U'.ι) (d.uEquiv_symm_apply hVN A Zs k)).trans
    ((Category.assoc _ _ _).trans (congrArg ((openOverIso A Zs).hom ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hβ).trans
        (CategoryTheory.Functor.map_comp _ _ _).symm))))

omit d in
/-- An isomorphism over `A ∖ Zs`, over `S`, gives an isomorphism over the inverse image of
`A ∖ Zs`, over `V`. -/
theorem isPullback_openOverIso (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A))))
    {Wo : Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (fj : (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
          Zsᶜ).ι ≫ yoneda.map (toV A)) :
            Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶ Wo)
    (fp : Wo ⟶ Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
    (hsq : IsPullback (𝟙 _) fj.left
      (Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A)) Zsᶜ).ι fp.left) :
    IsPullback (𝟙 _) ((openOverIso A Zs).hom ≫
        (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map fj)
      (Space.openSubspaceOfPoints B V.left.obj V.left.property (yoneda.obj A)
        (pointsOver A ⁻¹' Zs)ᶜ).ι
      ((smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map fp ≫
        (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A).inv) := by
  let fι : (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
      Zsᶜ).ι ≫ yoneda.map (toV A)) :
        Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
      Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A :=
    Over.homMk (Space.openSubspaceOfPoints B S hS _ Zsᶜ).ι rfl
  have hOver : IsPullback (𝟙 _) fj fι fp :=
    IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (by
      rw [Over.comp_left, Over.comp_left, Over.id_left, ← hsq.w]
      rfl)) (by rw [CategoryTheory.Functor.map_id]; exact hsq)
  have hα : (openOverIso A Zs).hom ≫
      (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map fι =
      (Space.openSubspaceOfPoints B V.left.obj V.left.property (yoneda.obj A)
        (pointsOver A ⁻¹' Zs)ᶜ).ι ≫
        (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A).hom :=
    openOverIso_hom_comp A Zs
  refine (hOver.map (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS
    V.hom).inverse).of_iso (openOverIso A Zs).symm (openOverIso A Zs).symm (Iso.refl _)
    (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A).symm
    (by simp) (by simp) ?_ (by simp)
  rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, hα, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **The completion square of the restricted witness, over `S`.** For a morphism `φ : A ⟶ V`, a
morphism `x : A ×_V V'₁ ⟶ E'` over `V` lifting the second projection, and a factorization `l` of
`A_{/φ⁻¹ Z} ⟶ V_{/Z}` through `E_W`, the completion of `A ×_V V'₁` along the inverse image of
`φ⁻¹ Z` is the fibre product of `A_{/φ⁻¹ Z}` and `E'_{/Z}` over `E_W`: paste the cartesian square
of the witness `A ×_V V'₁` (restricted to `φ⁻¹ Z ⊆ φ⁻¹ Z₁`) with assertion (3). -/
theorem isPullback_completionSheafRestrict_toEqz {A : BigFppfOver B S hS} (φ : A ⟶ V)
    (x : (d.w₁.pullback φ d.t₁).V' ⟶ d.eqz)
    (hx1 : x ≫ d.toBase = Limits.pullback.fst (yoneda.map φ) d.w₁.p ≫ yoneda.map φ)
    (hx2 : x ≫ d.toFst = Limits.pullback.snd (yoneda.map φ) d.w₁.p)
    (l : Space.completionSheaf B S hS (yoneda.obj A) (d.preZ φ) ⟶ d.EW)
    (hl : l ≫ equalizer.ι d.xhat₁ d.xhat₂ =
      Space.completionSheafRestrict B S hS (yoneda.map φ) (d.preZ φ) d.Z Set.Subset.rfl)
    (hxs : Space.pointsMap B S hS _ (d.w₁.pullback φ d.t₁).p ⁻¹' d.preZ φ ⊆
      Space.pointsMap B S hS _ x ⁻¹' d.centerEqz) :
    IsPullback (Space.completionSheafRestrict B S hS (d.w₁.pullback φ d.t₁).p
        (Space.pointsMap B S hS _ (d.w₁.pullback φ d.t₁).p ⁻¹' d.preZ φ) (d.preZ φ) subset_rfl)
      (Space.completionSheafRestrict B S hS x _ d.centerEqz hxs) l d.completedToEW := by
  have hZ0 : d.preZ φ ⊆ (mapTriple c φ d.t₁).Z := d.preZ_subset_preZ₁ φ
  have hsq0 := (d.w₁.pullback φ d.t₁).isPullback_restrict hZ0
  have E1 : Space.completionSheafRestrict B S hS x _ d.centerEqz hxs ≫ d.completedToSituation =
      Space.completionSheafRestrict B S hS (𝟙 (d.w₁.pullback φ d.t₁).V')
      (Space.pointsMap B S hS (d.w₁.pullback φ d.t₁).V' (d.w₁.pullback φ d.t₁).p ⁻¹' d.preZ φ)
      (Space.pointsMap B S hS (d.w₁.pullback φ d.t₁).V' (d.w₁.pullback φ d.t₁).p ⁻¹'
        (mapTriple c φ d.t₁).Z)
      (Space.subset_preimage_pointsMap_id B S hS (Set.preimage_mono hZ0)) ≫
        (d.w₁.pullback φ d.t₁).xhat' := by
    have := Space.mono_completionSheafInclusion B S hS c.X' c.T'
    rw [← cancel_mono (Space.completionSheafInclusion B S hS c.X' c.T'), Category.assoc,
      completedToSituation, Space.completionSheafRestrict_comp_inclusion, ← Category.assoc,
      Space.completionSheafRestrict_comp_inclusion, Category.assoc,
      ← Space.sheafifiedULiftMap_comp, Category.assoc,
      (d.w₁.pullback φ d.t₁).completionSheafRestrict_comp_xhat'_comp_inclusion, Category.id_comp]
    exact congrArg (fun k => _ ≫ Space.sheafifiedULiftMap B S hS k)
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ d.w₁.x') hx2))
  have E2 : l ≫ equalizer.ι d.xhat₁ d.xhat₂ ≫ d.xhat₁ =
      Space.completionSheafRestrict B S hS (𝟙 _) (d.preZ φ) (mapTriple c φ d.t₁).Z
        (Space.subset_preimage_pointsMap_id B S hS hZ0) ≫ (mapTriple c φ d.t₁).xhat := by
    have key := d.completionSheafRestrict_comp_xhat₁ φ (d.preZ φ) subset_rfl (d.preZ_subset_preZ₁ φ)
    rw [Space.completionSheafRestrict_id, Category.id_comp] at key
    rw [← Category.assoc, hl, ← key]
    exact (Space.completionSheafRestrict_id_comp_assoc B S hS (yoneda.map φ) _ _ _ _ _ _).symm
  have hcomp : Space.pointsMap B S hS _ (d.w₁.pullback φ d.t₁).p ⁻¹' d.preZ φ ⊆
      Space.pointsMap B S hS _ ((d.w₁.pullback φ d.t₁).p ≫ yoneda.map φ) ⁻¹' d.Z := by
    intro y hy
    rw [Set.mem_preimage, Space.pointsMap_comp]
    exact hy
  have p0 : Space.completionSheafRestrict B S hS (d.w₁.pullback φ d.t₁).p
      (Space.pointsMap B S hS _ (d.w₁.pullback φ d.t₁).p ⁻¹' d.preZ φ)
      (d.preZ φ) subset_rfl ≫ l =
      Space.completionSheafRestrict B S hS x _ d.centerEqz hxs ≫ d.completedToEW := by
    rw [← cancel_mono (equalizer.ι d.xhat₁ d.xhat₂), Category.assoc, hl, Category.assoc,
      completedToEW_comp_ι, completedToBase,
      Space.completionSheafRestrict_comp_eq B S hS (d.w₁.pullback φ d.t₁).p (yoneda.map φ)
        ((d.w₁.pullback φ d.t₁).p ≫ yoneda.map φ) rfl
        _ _ _ _ _ hcomp,
      Space.completionSheafRestrict_comp_eq B S hS x d.toBase
        ((d.w₁.pullback φ d.t₁).p ≫ yoneda.map φ) hx1
        _ _ _ _ _ hcomp]
  exact IsPullback.of_bot (by rw [E1, E2]; exact hsq0) p0
    (d.isPullback_completedToSituation_completedToEW.2.flip)

/-- **The completion square over `V`.** Moving an S-side cartesian square of completions to the big
fppf site of `V` by Stacks 04SG: if the completion of `Wo` along `T` is the fibre product of
`A_{/Zs}` and `E'_{/Z}` over `E_W`, then the completion of the attached `Wo_V` is the fibre
product of `A_{/Zs}` (over `V`) and `X'_{/T'}` of the situation of assertion (4) over its `W`. -/
theorem isPullback_completion_situation (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A))))
    {Wo : Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (hWsp : IsAlgebraicSpace B S hS Wo.left)
    (fp : Wo ⟶ Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
    (fx : Wo ⟶ d.E'OverV) (T : Set (Space.points B S hS Wo.left))
    (hT : T ⊆ Space.pointsMap B S hS _ fp.left ⁻¹' Zs)
    (hxs : T ⊆ Space.pointsMap B S hS _ fx.left ⁻¹' d.centerEqz)
    (l : Space.completionSheaf B S hS (yoneda.obj ((Over.map V.hom).obj A)) Zs ⟶ d.EW)
    (hSQ : IsPullback (Space.completionSheafRestrict B S hS fp.left T Zs hT)
      (Space.completionSheafRestrict B S hS fx.left T d.centerEqz hxs) l d.completedToEW)
    (xhat : Space.completionSheaf B V.left.obj V.left.property (yoneda.obj A)
      (pointsOver A ⁻¹' Zs) ⟶
        smallerBaseSheafOf B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget)
    (γ : Space.completionSheaf B V.left.obj V.left.property
        (Space.smallerBaseInverse B V.left.obj S V.left.property hS V.hom d.E'OverV)
        (Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom d.E'OverV
          d.centerEqz) ⟶
      smallerBaseSheafOf B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget)
    (hγ : (smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom).map γ =
      (smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom d.E'OverV
          d.isAlgebraicSpace_eqz d.centerEqz).hom ≫ d.completedToEW ≫
        (smallerBaseSheafOfIso B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget).inv)
    (hΨx : (smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom).map
        ((Space.completionSheafIsoOfIso B V.left.obj V.left.property
          (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A)
          (pointsOver A ⁻¹' Zs) (Space.smallerBaseInverseSet B V.left.obj S V.left.property hS
            V.hom (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) Zs)
            rfl).inv ≫ xhat) =
      (smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom
          (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
          (isAlgebraicSpace_yoneda B S hS _) Zs).hom ≫ l ≫
        (smallerBaseSheafOfIso B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget).inv)
    (hset : Space.pointsMap B V.left.obj V.left.property _
        ((smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map fp ≫
          (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A).inv) ⁻¹'
          (pointsOver A ⁻¹' Zs) =
      Space.pointsMap B V.left.obj V.left.property _ (Iso.refl _).hom ⁻¹'
        Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom Wo T)
    (hsub : Space.pointsMap B V.left.obj V.left.property _
        ((smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map fp ≫
          (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A).inv) ⁻¹'
          (pointsOver A ⁻¹' Zs) ⊆
      Space.pointsMap B V.left.obj V.left.property _
        ((smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map
          fx) ⁻¹'
          Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom d.E'OverV
            d.centerEqz) :
    IsPullback (Space.completionSheafRestrict B V.left.obj V.left.property
        ((smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map fp ≫
          (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A).inv)
        _ (pointsOver A ⁻¹' Zs) subset_rfl)
      (Space.completionSheafRestrict B V.left.obj V.left.property
        ((smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse.map fx)
        _ (Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom d.E'OverV
          d.centerEqz) hsub) xhat γ := by
  let Φi := (smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom).inverse
  let Ψ := smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom
  let Yo := Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A
  let eA := Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A
  have hAsp := isAlgebraicSpace_yoneda B S hS ((Over.map V.hom).obj A)
  let cA := Space.completionSheafIsoOfIso B V.left.obj V.left.property eA (pointsOver A ⁻¹' Zs)
    (Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom Yo Zs) rfl
  let eY := smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom Yo hAsp Zs
  let sO := smallerBaseSheafOfIso B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget
  let cSet := Space.completionSheafIsoOfIso B V.left.obj V.left.property (Iso.refl (Φi.obj Wo))
    _ _ hset
  let eW := smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom Wo hWsp T
  let cE := smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom d.E'OverV
    d.isAlgebraicSpace_eqz d.centerEqz
  have N1 := Space.smallerBaseSheafFunctor_map_completionSheafRestrict_comp B V.left.obj S
    V.left.property hS V.hom fp hWsp hAsp T Zs hT
  have N2 := Space.smallerBaseSheafFunctor_map_completionSheafRestrict_comp B V.left.obj S
    V.left.property hS V.hom fx hWsp d.isAlgebraicSpace_eqz T d.centerEqz hxs
  have hsubK : Space.pointsMap B V.left.obj V.left.property _ (Φi.map fp ≫ eA.inv) ⁻¹'
      (pointsOver A ⁻¹' Zs) ⊆ Space.pointsMap B V.left.obj V.left.property _ (Φi.map fp) ⁻¹'
        Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom Yo Zs := by
    intro y hy
    have hy' : y ∈ Space.pointsMap B V.left.obj V.left.property _ (Iso.refl _).hom ⁻¹'
        Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom Wo T := hset ▸ hy
    rw [Iso.refl_hom, Space.pointsMap_id, Set.preimage_id] at hy'
    change
      Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom Yo _ ∈ Zs
    rw [Space.pointsSmallerBaseInverseHomeomorph_naturality]
    exact hT hy'
  have K1 : cSet.hom ≫ Space.completionSheafRestrict B V.left.obj V.left.property (Φi.map fp)
      _ _ (Space.smallerBaseInverseSet_subset B V.left.obj S V.left.property hS V.hom fp hT) =
      Space.completionSheafRestrict B V.left.obj V.left.property (Φi.map fp ≫ eA.inv)
        _ (pointsOver A ⁻¹' Zs) subset_rfl ≫ cA.hom := by
    change Space.completionSheafRestrict B V.left.obj V.left.property (Iso.refl _).hom _ _ _ ≫ _ =
      _ ≫ Space.completionSheafRestrict B V.left.obj V.left.property eA.hom _ _ _
    rw [Space.completionSheafRestrict_comp_eq B V.left.obj V.left.property (Iso.refl _).hom
      (Φi.map fp) (Φi.map fp) (Category.id_comp _) _ _ _ _ _ hsubK,
      Space.completionSheafRestrict_comp_eq B V.left.obj V.left.property (Φi.map fp ≫ eA.inv)
      eA.hom (Φi.map fp) (by simp) _ _ _ _ _ hsubK]
  have K2 : cSet.hom ≫ Space.completionSheafRestrict B V.left.obj V.left.property (Φi.map fx)
      _ _ (Space.smallerBaseInverseSet_subset B V.left.obj S V.left.property hS V.hom fx hxs) =
      Space.completionSheafRestrict B V.left.obj V.left.property (Φi.map fx)
        _ (Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom d.E'OverV
          d.centerEqz) hsub := by
    change Space.completionSheafRestrict B V.left.obj V.left.property (Iso.refl _).hom _ _ _ ≫ _ =
      _
    rw [Space.completionSheafRestrict_comp_eq B V.left.obj V.left.property (Iso.refl _).hom
      (Φi.map fx) (Φi.map fx) (Category.id_comp _) _ _ _ _ _ hsub]
  have c1 : Space.completionSheafRestrict B S hS fp.left T Zs hT ≫ (Ψ.mapIso cA ≪≫ eY).symm.hom =
      (Ψ.mapIso cSet ≪≫ eW).symm.hom ≫ Ψ.map (Space.completionSheafRestrict B V.left.obj
        V.left.property (Φi.map fp ≫ eA.inv) _ (pointsOver A ⁻¹' Zs) subset_rfl) := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rw [← N1, ← Category.assoc, ← CategoryTheory.Functor.map_comp, K1,
      CategoryTheory.Functor.map_comp, Category.assoc]
  have c2 : Space.completionSheafRestrict B S hS fx.left T d.centerEqz hxs ≫ cE.symm.hom =
      (Ψ.mapIso cSet ≪≫ eW).symm.hom ≫ Ψ.map (Space.completionSheafRestrict B V.left.obj
        V.left.property (Φi.map fx) _ (Space.smallerBaseInverseSet B V.left.obj S
          V.left.property hS V.hom d.E'OverV d.centerEqz) hsub) := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rw [← N2, ← Category.assoc, ← CategoryTheory.Functor.map_comp, K2]
  have c3 : l ≫ sO.symm.hom = (Ψ.mapIso cA ≪≫ eY).symm.hom ≫ Ψ.map xhat := by
    rw [Iso.symm_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Category.assoc,
      ← CategoryTheory.Functor.map_comp, hΨx, Iso.inv_hom_id_assoc]
  have c4 : d.completedToEW ≫ sO.symm.hom = cE.symm.hom ≫ Ψ.map γ := by
    rw [hγ, Iso.symm_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  have hΨsq := hSQ.of_iso (Ψ.mapIso cSet ≪≫ eW).symm (Ψ.mapIso cA ≪≫ eY).symm cE.symm sO.symm
    c1 c2 c3 c4
  exact IsPullback.of_map Ψ (Ψ.map_injective (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    exact hΨsq.w)) hΨsq


/-- The condition defining the third components, for a factorization of `A_{/φ⁻¹ Z} ⟶ V_{/Z}`
through `E_W`. -/
theorem EWToTarget_cond (A : BigFppfOver B V.left.obj V.left.property)
    (l : Space.completionSheaf B S hS (yoneda.obj ((Over.map V.hom).obj A)) (d.preZ (toV A)) ⟶
      d.EW)
    (hl : l ≫ equalizer.ι d.xhat₁ d.xhat₂ =
      Space.completionSheafRestrict B S hS (yoneda.map (toV A)) (d.preZ (toV A)) d.Z
        Set.Subset.rfl) :
    (l ≫ d.EWToTarget).hom =
      Space.completionSheafToSmallerBase B V.left.obj S V.left.property hS V.hom
        (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) (d.preZ (toV A))
        (isAlgebraicSpace_yoneda B S hS _) := by
  exact (d.comp_ι_eq_restrict_iff A l).1 hl

/-- The third component attached to `l`, moved to `S`, is `l`. -/
theorem smallerBaseSheafFunctor_map_xhatEquiv_symm (A : BigFppfOver B V.left.obj V.left.property)
    (Zs : Set (Space.points B S hS (yoneda.obj ((Over.map V.hom).obj A))))
    (l : Space.completionSheaf B S hS (yoneda.obj ((Over.map V.hom).obj A)) Zs ⟶ d.EW)
    (hl' : (l ≫ d.EWToTarget).hom =
      Space.completionSheafToSmallerBase B V.left.obj S V.left.property hS V.hom
        (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) Zs
        (isAlgebraicSpace_yoneda B S hS _)) :
    (smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom).map
        ((Space.completionSheafIsoOfIso B V.left.obj V.left.property
          (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A)
          (pointsOver A ⁻¹' Zs) (Space.smallerBaseInverseSet B V.left.obj S V.left.property hS
            V.hom (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) Zs)
            rfl).inv ≫ (d.xhatEquiv hVN A Zs).symm ⟨l, hl'⟩) =
      (smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom
          (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
          (isAlgebraicSpace_yoneda B S hS _) Zs).hom ≫ l ≫
        (smallerBaseSheafOfIso B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget).inv := by
  let Ψ := smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom
  let cA := Space.completionSheafIsoOfIso B V.left.obj V.left.property
    (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A)
    (pointsOver A ⁻¹' Zs) (Space.smallerBaseInverseSet B V.left.obj S V.left.property hS
      V.hom (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A) Zs) rfl
  let eY := smallerBaseCompletionIso B V.left.obj S V.left.property hS V.hom
    (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
    (isAlgebraicSpace_yoneda B S hS _) Zs
  let sO := smallerBaseSheafOfIso B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget
  let xhat := (d.xhatEquiv hVN A Zs).symm ⟨l, hl'⟩
  have hxl : eY.inv ≫ Ψ.map (cA.inv ≫ xhat ≫ (Iso.refl _).hom) ≫ sO.hom = l :=
    congrArg Subtype.val ((d.xhatEquiv hVN A Zs).apply_symm_apply ⟨l, hl'⟩)
  simp only [Iso.refl_hom, Category.comp_id] at hxl
  change Ψ.map (cA.inv ≫ xhat) = eY.hom ≫ l ≫ sO.inv
  rw [← hxl]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact ((Category.comp_id _).symm.trans (congrArg (Ψ.map (cA.inv ≫ xhat) ≫ ·)
    sO.hom_inv_id.symm)).trans (Category.assoc _ _ _).symm

/-- The third component attached to a factorization of `A_{/φ⁻¹ Z} ⟶ V_{/Z}` through `E_W` is
adic. -/
theorem isRepresentable_xhatEquiv_symm (A : BigFppfOver B V.left.obj V.left.property)
    (l : Space.completionSheaf B S hS (yoneda.obj ((Over.map V.hom).obj A)) (d.preZ (toV A)) ⟶
      d.EW)
    (hl : l ≫ equalizer.ι d.xhat₁ d.xhat₂ =
      Space.completionSheafRestrict B S hS (yoneda.map (toV A)) (d.preZ (toV A)) d.Z
        Set.Subset.rfl) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B V.left.obj V.left.property
      ((d.xhatEquiv hVN A (d.preZ (toV A))).symm ⟨l, d.EWToTarget_cond A l hl⟩).hom := by
  have hAsp := isAlgebraicSpace_yoneda B S hS ((Over.map V.hom).obj A)
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  have hΨx := d.smallerBaseSheafFunctor_map_xhatEquiv_symm hVN A _ l (d.EWToTarget_cond A l hl)
  have hladic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS l.hom := by
    refine FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_mono B S hS l
      (equalizer.ι d.xhat₁ d.xhat₂) ?_
    have e : l.hom ≫ (equalizer.ι d.xhat₁ d.xhat₂).hom =
        (Space.completionSheafMap B S hS (yoneda.map (toV A)) d.Z).hom :=
      (congrArg (fun k => k.hom) hl).trans (congrArg (fun k => k.hom)
        (Space.completionSheafRestrict_self B S hS (yoneda.map (toV A)) d.Z _))
    rw [e]
    exact Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS hAsp hVsp _ _
  have h1 := Space.isRepresentableByAlgebraicSpacesULift_of_iso B S hS
    ((sheafToPresheaf _ _).mapIso (smallerBaseCompletionIso B V.left.obj S V.left.property hS
      V.hom (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
      (isAlgebraicSpace_yoneda B S hS _) (d.preZ (toV A))).symm)
    ((sheafToPresheaf _ _).mapIso (smallerBaseSheafOfIso B V.left.obj S V.left.property hS
      V.hom d.EW d.EWToTarget).symm) (by
        have e := (Iso.inv_hom_id_assoc (smallerBaseCompletionIso B V.left.obj S V.left.property hS
          V.hom (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A)
          (isAlgebraicSpace_yoneda B S hS _) (d.preZ (toV A))) (l ≫ (smallerBaseSheafOfIso B
            V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget).inv)).symm.trans
          (congrArg (_ ≫ ·) hΨx.symm)
        exact congrArg (fun k => k.hom) e) hladic
  have h2 := (isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B V.left.obj S
    V.left.property hS V.hom _).1 h1
  exact Space.isRepresentableByAlgebraicSpacesULift_of_iso B V.left.obj V.left.property
    ((sheafToPresheaf _ _).mapIso (Space.completionSheafIsoOfIso B V.left.obj V.left.property
      (Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A)
      (pointsOver A ⁻¹' d.preZ (toV A)) (Space.smallerBaseInverseSet B V.left.obj S
        V.left.property hS V.hom (Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS
          V.hom A) (d.preZ (toV A))) rfl).symm) (Iso.refl _) (by simp) h2

/-- The witness `A ×_V V'₁ ⟶ A` of the restricted triple, as a morphism over `V`. -/
def pOver (A : BigFppfOver B V.left.obj V.left.property) :
    (Over.mk ((d.w₁.pullback (toV A) d.t₁).p ≫ yoneda.map (toV A)) :
      Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
      Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A :=
  Over.homMk (d.w₁.pullback (toV A) d.t₁).p rfl

/-- The identification of `A ∖ φ⁻¹ Z` with an open subspace of `A ×_V V'₁`, as a morphism over
`V`. -/
def jOver (A : BigFppfOver B V.left.obj V.left.property)
    (hU : d.preZ₁ (toV A) ⊆ d.preZ (toV A)) :
    (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
        (d.preZ (toV A))ᶜ).ι ≫ yoneda.map (toV A)) :
      Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
      Over.mk ((d.w₁.pullback (toV A) d.t₁).p ≫ yoneda.map (toV A)) :=
  Over.homMk ((Space.openSubspaceOfPointsIsoOfIso B S hS (Iso.refl _) (d.preZ (toV A))ᶜ
      (d.preZ₁ (toV A))ᶜ (by
        rw [Iso.refl_hom, Space.pointsMap_id, Set.preimage_id,
          (d.preZ_subset_preZ₁ (toV A)).antisymm hU])).hom ≫ (d.w₁.pullback (toV A) d.t₁).j)
    (by
      have hw := (d.w₁.pullback (toV A) d.t₁).isPullback_j.w
      rw [Category.id_comp] at hw
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ yoneda.map (toV A)) hw.symm))).trans rfl))

/-- The identification `A ∖ φ⁻¹ Z ⟶ A ×_V V'₁` followed by the witness `A ×_V V'₁ ⟶ A` is the
inclusion `A ∖ φ⁻¹ Z ⟶ A`. -/
theorem jOver_left_comp (A : BigFppfOver B V.left.obj V.left.property)
    (hU : d.preZ₁ (toV A) ⊆ d.preZ (toV A)) :
    (d.jOver A hU).left ≫ (d.w₁.pullback (toV A) d.t₁).p =
      (Space.openSubspaceOfPoints B S hS _ (d.preZ (toV A))ᶜ).ι := by
  have hw := (d.w₁.pullback (toV A) d.t₁).isPullback_j.w
  rw [Category.id_comp] at hw
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hw.symm).trans rfl)

/-- The square with the identity of `A ∖ φ⁻¹ Z`, the identification `A ∖ φ⁻¹ Z ⟶ A ×_V V'₁`, the
inclusion `A ∖ φ⁻¹ Z ⟶ A` and the witness `A ×_V V'₁ ⟶ A` is a pullback; it is the pullback
square of the witness restricted to `A ×_V V'₁`, up to identifying its open part with
`A ∖ φ⁻¹ Z`. -/
theorem isPullback_jOver (A : BigFppfOver B V.left.obj V.left.property)
    (hU : d.preZ₁ (toV A) ⊆ d.preZ (toV A)) :
    IsPullback (𝟙 _) (d.jOver A hU).left
      (Space.openSubspaceOfPoints B S hS _ (d.preZ (toV A))ᶜ).ι (d.pOver A).left := by
  let rI := Space.openSubspaceOfPointsIsoOfIso B S hS
    (Iso.refl (yoneda.obj ((Over.map V.hom).obj A)))
    (d.preZ (toV A))ᶜ (d.preZ₁ (toV A))ᶜ (by
      rw [Iso.refl_hom, Space.pointsMap_id, Set.preimage_id,
        (d.preZ_subset_preZ₁ (toV A)).antisymm hU])
  exact (d.w₁.pullback (toV A) d.t₁).isPullback_j.of_iso rI.symm rI.symm (Iso.refl _) (Iso.refl _)
    (by rw [Category.id_comp, Category.comp_id])
    (by
      change (d.w₁.pullback (toV A) d.t₁).j ≫ 𝟙 _ = rI.inv ≫ rI.hom ≫ (d.w₁.pullback (toV A) d.t₁).j
      exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc rI _).symm)
    rfl (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl)

/-- The morphism `E' ∖ (E' ⟶ V)⁻¹ Z`-valued second component, from `x : A ×_V V'₁ ⟶ E'`. -/
theorem exists_offCenter_hom (A : BigFppfOver B V.left.obj V.left.property)
    (hU : d.preZ₁ (toV A) ⊆ d.preZ (toV A)) (x : (d.w₁.pullback (toV A) d.t₁).V' ⟶ d.eqz)
    (hx1 : x ≫ d.toBase = Limits.pullback.fst (yoneda.map (toV A)) d.w₁.p ≫ yoneda.map (toV A)) :
    ∃ k₀ : (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
        (d.preZ (toV A))ᶜ).ι ≫ yoneda.map (toV A)) :
          Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
        Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase),
      k₀ ≫ (Over.homMk (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι rfl :
        (Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase) :
          Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶ d.E'OverV) =
        d.jOver A hU ≫ (Over.homMk x hx1 : Over.mk ((d.w₁.pullback (toV A) d.t₁).p ≫
          yoneda.map (toV A)) ⟶ d.E'OverV) := by
  let m := (d.jOver A hU).left ≫ x
  have hm : m ≫ d.toBase =
      (Space.openSubspaceOfPoints B S hS _ (d.preZ (toV A))ᶜ).ι ≫ yoneda.map (toV A) :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx1).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ yoneda.map (toV A))
        (d.jOver_left_comp A hU))))
  have hrange : Subfunctor.range m ≤ Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ := by
    refine Space.range_le_openSubspaceOfPoints_preimage B S hS m d.toBase d.Zᶜ ?_
    rw [hm]
    rintro U _ ⟨s, rfl⟩
    exact ((Space.openSubspaceOfPointsRestrict B S hS (yoneda.map (toV A)) (d.preZ (toV A))ᶜ d.Zᶜ
      Set.Subset.rfl).app U s).2
  exact ⟨Over.homMk (Subfunctor.lift m hrange) (by
    change Subfunctor.lift m hrange ≫ _ ≫ d.toBase = _
    rw [← Category.assoc, Subfunctor.lift_ι]
    exact hm), Over.OverMorphism.ext (Subfunctor.lift_ι m hrange)⟩

/-- **The compatibility witness of the constructed triple.** The base change to `V` of the
witness `A ×_V V'₁ ⟶ A`, with the morphism `A ×_V V'₁ ⟶ E'`, witnesses the compatibility of the
second and third components built from `x` and `l`. -/
theorem nonempty_compatibilityWitness_situation (A : BigFppfOver B V.left.obj V.left.property)
    (hU : d.preZ₁ (toV A) ⊆ d.preZ (toV A)) (x : (d.w₁.pullback (toV A) d.t₁).V' ⟶ d.eqz)
    (hx1 : x ≫ d.toBase = Limits.pullback.fst (yoneda.map (toV A)) d.w₁.p ≫ yoneda.map (toV A))
    (hx2 : x ≫ d.toFst = Limits.pullback.snd (yoneda.map (toV A)) d.w₁.p)
    (l : Space.completionSheaf B S hS (yoneda.obj ((Over.map V.hom).obj A)) (d.preZ (toV A)) ⟶
      d.EW)
    (hl : l ≫ equalizer.ι d.xhat₁ d.xhat₂ =
      Space.completionSheafRestrict B S hS (yoneda.map (toV A)) (d.preZ (toV A)) d.Z
        Set.Subset.rfl)
    (k₀ : (Over.mk ((Space.openSubspaceOfPoints B S hS (yoneda.obj ((Over.map V.hom).obj A))
        (d.preZ (toV A))ᶜ).ι ≫ yoneda.map (toV A)) :
          Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶
        Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase))
    (hk : k₀ ≫ (Over.homMk (Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι rfl :
        (Over.mk ((Space.openSubspaceOfPoints B S hS d.eqz d.centerEqzᶜ).ι ≫ d.toBase) :
          Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) ⟶ d.E'OverV) =
        d.jOver A hU ≫ (Over.homMk x hx1 : Over.mk ((d.w₁.pullback (toV A) d.t₁).p ≫
          yoneda.map (toV A)) ⟶ d.E'OverV)) :
    Nonempty (CompatibilityWitness (d.situation hVN) A (pointsOver A ⁻¹' d.preZ (toV A))
      ((d.uEquiv hVN A (d.preZ (toV A))).symm k₀)
      ((d.xhatEquiv hVN A (d.preZ (toV A))).symm ⟨l, d.EWToTarget_cond A l hl⟩)) := by
  let Φ := smallerBasePresheafEquivalence B V.left.obj S V.left.property hS V.hom
  let φ := toV (hS := hS) A
  let ω := d.w₁.pullback φ d.t₁
  have hAsp := isAlgebraicSpace_yoneda B S hS ((Over.map V.hom).obj A)
  let xhat := (d.xhatEquiv hVN A (d.preZ φ)).symm ⟨l, d.EWToTarget_cond A l hl⟩
  have hxz : ∀ z, Space.pointsMap B S hS _ d.toBase (Space.pointsMap B S hS _ x z) =
      Space.pointsMap B S hS _ (yoneda.map φ) (Space.pointsMap B S hS _ ω.p z) := fun z =>
    (congrFun (Space.pointsMap_comp B S hS _ x d.toBase) z).symm.trans
      ((congrArg (fun k => Space.pointsMap B S hS _ k z) hx1).trans
        (congrFun (Space.pointsMap_comp B S hS _ ω.p (yoneda.map φ)) z))
  let Wo : Over (yoneda.obj (Over.mk V.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    Over.mk (ω.p ≫ yoneda.map φ)
  let Yo := Space.smallerBaseYonedaOver B V.left.obj S V.left.property hS V.hom A
  let eA := Space.smallerBaseInverseYonedaIso B V.left.obj S V.left.property hS V.hom A
  have hWsp : IsAlgebraicSpace B S hS Wo.left := ω.isAlgebraicSpace_V'
  let fp : Wo ⟶ Yo := d.pOver A
  let fx : Wo ⟶ d.E'OverV := Over.homMk x hx1
  let fj := d.jOver A hU
  let V'' := Φ.inverse.obj Wo
  let p'' : V'' ⟶ yoneda.obj A := Φ.inverse.map fp ≫ eA.inv
  let j'' := (openOverIso A (d.preZ φ)).hom ≫ Φ.inverse.map fj
  let x'' : V'' ⟶ (d.situation hVN).X' := Φ.inverse.map fx
  let ρW := Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom Wo
  let ρY := Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom Yo
  let ρE := Space.pointsSmallerBaseInverseHomeomorph B V.left.obj S V.left.property hS V.hom
    d.E'OverV
  have hpts2 : ∀ y, ρY (Space.pointsMap B V.left.obj V.left.property V'' (Φ.inverse.map fp) y) =
      Space.pointsMap B S hS _ ω.p (ρW y) := fun y =>
    Space.pointsSmallerBaseInverseHomeomorph_naturality B V.left.obj S V.left.property hS V.hom fp y
  have hxpts : ∀ y, ρE (Space.pointsMap B V.left.obj V.left.property V'' x'' y) =
      Space.pointsMap B S hS _ x (ρW y) := fun y =>
    Space.pointsSmallerBaseInverseHomeomorph_naturality B V.left.obj S V.left.property hS V.hom fx y
  have hpts : ∀ y, pointsOver A (Space.pointsMap B V.left.obj V.left.property V'' p'' y) =
      Space.pointsMap B S hS _ ω.p (ρW y) := by
    intro y
    have e : p'' ≫ eA.hom = Φ.inverse.map fp := by simp [p'']
    have h1 :
        Space.pointsMap _ _ _ _ eA.hom (Space.pointsMap B V.left.obj V.left.property V'' p'' y) =
        Space.pointsMap B V.left.obj V.left.property V'' (Φ.inverse.map fp) y :=
      (congrFun (Space.pointsMap_comp B V.left.obj V.left.property _ p'' eA.hom) y).symm.trans
        (congrArg (fun k => Space.pointsMap B V.left.obj V.left.property V'' k y) e)
    change ρY (Space.pointsMap _ _ _ _ eA.hom _) = _
    rw [h1, hpts2]
  have hxs : Space.pointsMap B S hS _ ω.p ⁻¹' d.preZ φ ⊆
      Space.pointsMap B S hS _ x ⁻¹' d.centerEqz := fun y hy =>
    (congrArg (· ∈ d.Z) (hxz y)).mpr hy
  have hsub :
      Space.pointsMap B V.left.obj V.left.property V'' p'' ⁻¹' (pointsOver A ⁻¹' d.preZ φ) ⊆
      Space.pointsMap B V.left.obj V.left.property V'' x'' ⁻¹' (d.situation hVN).T' := by
    intro y hy
    have hy' : Space.pointsMap B S hS _ ω.p (ρW y) ∈ d.preZ φ := by
      rw [← hpts]
      exact hy
    change ρE (Space.pointsMap B V.left.obj V.left.property V'' x'' y) ∈ d.centerEqz
    rw [hxpts]
    exact hxs hy'
  have hsetV :
      Space.pointsMap B V.left.obj V.left.property V'' p'' ⁻¹' (pointsOver A ⁻¹' d.preZ φ) =
      Space.pointsMap B V.left.obj V.left.property V'' (Iso.refl V'').hom ⁻¹'
        Space.smallerBaseInverseSet B V.left.obj S V.left.property hS V.hom Wo
          (Space.pointsMap B S hS _ ω.p ⁻¹' d.preZ φ) := by
    ext y
    rw [Iso.refl_hom, Space.pointsMap_id, Set.preimage_id]
    change pointsOver A (Space.pointsMap B V.left.obj V.left.property V'' p'' y) ∈ d.preZ φ ↔
      Space.pointsMap B S hS _ ω.p (ρW y) ∈ d.preZ φ
    rw [hpts]
  have hp'' : Space.IsProper B V.left.obj V.left.property p'' :=
    (Space.isProper_comp_isIso_iff B V.left.obj V.left.property _ eA.inv).2
      (Space.isProper_smallerBaseInverse_map B V.left.obj S V.left.property hS V.hom fp hWsp hAsp
        ω.isProper_p)
  have hjpb := isPullback_openOverIso A (d.preZ φ) fj fp (d.isPullback_jOver A hU)
  have e1 : j'' ≫ x'' = (openOverIso A (d.preZ φ)).hom ≫ Φ.inverse.map (fj ≫ fx) :=
    (Category.assoc _ _ _).trans (congrArg ((openOverIso A (d.preZ φ)).hom ≫ ·)
      (Φ.inverse.map_comp fj fx).symm)
  have hrx : j'' ≫ x'' = (d.uEquiv hVN A (d.preZ φ)).symm k₀ ≫ (d.situation hVN).U'.ι :=
    e1.trans ((congrArg (fun k => (openOverIso A (d.preZ φ)).hom ≫ Φ.inverse.map k) hk.symm).trans
      (d.uEquiv_symm_apply_comp_ι hVN A (d.preZ φ) k₀).symm)
  have hSQ := d.isPullback_completionSheafRestrict_toEqz φ x hx1 hx2 l hl hxs
  have hΨx := d.smallerBaseSheafFunctor_map_xhatEquiv_symm hVN A _ l (d.EWToTarget_cond A l hl)
  have hpbx := d.isPullback_completion_situation A (d.preZ φ) hWsp fp fx
    (Space.pointsMap B S hS _ ω.p ⁻¹' d.preZ φ) subset_rfl hxs l hSQ xhat (d.situation hVN).g
    (d.smallerBaseSheafFunctor_map_situation_g hVN) hΨx hsetV hsub
  exact ⟨{ V' := V''
           isAlgebraicSpace_V' := isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B
             V.left.obj S V.left.property hS V.hom Wo hWsp
           p := p''
           isProper_p := hp''
           j := j''
           isPullback_j := hjpb
           xhat' := Space.completionSheafRestrict B V.left.obj V.left.property x'' _ _ hsub
           isPullback_xhat' := hpbx
           x' := x''
           restrict_x' := hrx
           completion_x' := (Space.completionSheafRestrict_comp_inclusion B V.left.obj
             V.left.property x'' _ _ hsub).symm }⟩

/-- **An element of `F_{(4)}(A)` exists when the two triples agree on `A`.** Let `A` be a locally
Noetherian scheme over `V`, with structure morphism `φ : A ⟶ V`, along which the two triples
restrict to the same element of `F(A)`. Then the situation of assertion (4) has a triple over `A`:
its first component is `φ⁻¹ Z`, its second component is the restriction to `A ∖ φ⁻¹ Z` of the
morphism `A ×_V V'₁ ⟶ E'` of `exists_toE'_of_mapTriple_eq`, its third component is the
factorization of `A_{/φ⁻¹ Z} ⟶ V_{/Z}` through `E_W` given by assertion (5), and the
compatibility is witnessed by `A ×_V V'₁ ⟶ A` (`nonempty_compatibilityWitness_situation`). -/
theorem nonempty_triple_situation_of_mapTriple_eq (A : BigFppfOver B V.left.obj V.left.property)
    (hA : IsLocallyNoetherian ((BigFppfOver.toScheme B V.left.obj V.left.property).obj A))
    (h : mapTriple c (toV A) d.t₁ = mapTriple c (toV A) d.t₂) :
    Nonempty (Triple (d.situation hVN) A) := by
  have hAS : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj ((Over.map V.hom).obj A)) :=
    hA
  obtain ⟨hoff, ⟨l, hl⟩⟩ := (d.mapTriple_eq_iff_factorsOffCenter_and_factorsEW (toV A)).1 h
  have hU := d.preZ₁_subset_preZ (toV A) (d.union_subset_preZ_of_factorsOffCenter (toV A) hoff)
  obtain ⟨x, hx1, hx2⟩ := d.exists_toE'_of_mapTriple_eq hAS (toV A) h
  obtain ⟨k₀, hk⟩ := d.exists_offCenter_hom A hU x hx1
  exact ⟨{ Z := pointsOver A ⁻¹' d.preZ (toV A)
           isClosed_Z := (d.isClosed_Z.preimage (Space.continuous_pointsMap B S hS _)).preimage
             (pointsOver A).continuous
           u := (d.uEquiv hVN A _).symm k₀
           xhat := (d.xhatEquiv hVN A _).symm ⟨l, d.EWToTarget_cond A l hl⟩
           adic_xhat := d.isRepresentable_xhatEquiv_symm hVN A l hl
           compatible := d.nonempty_compatibilityWitness_situation hVN A hU x hx1 hx2 l hl k₀ hk }⟩

/-- The value of the fibre `F ×_{Δ, F × F} V` at an object `A` over `V`, with structure morphism
`φ : A ⟶ V`: the elements `y ∈ F(A)` with `(y, y) = (φ^* t₁, φ^* t₂)` in `(F × F)(A)`, that is,
the elements of `F(A)` which are the restriction of both triples. -/
def diagonalFibreObj (A : BigFppfOver B V.left.obj V.left.property) : Type (u + 1) :=
  {y : Triple c ((Over.map V.hom).obj A) //
    y = mapTriple c (toV A) d.t₁ ∧ y = mapTriple c (toV A) d.t₂}

/-- The fibre `F ×_{Δ, F × F} V` has at most one element over each `A`: an element is the
restriction of the first triple. -/
theorem subsingleton_diagonalFibreObj (A : BigFppfOver B V.left.obj V.left.property) :
    Subsingleton (d.diagonalFibreObj A) :=
  ⟨fun a b => Subtype.ext (a.2.1.trans b.2.1.symm)⟩

/-- The restriction maps of the fibre `F ×_{Δ, F × F} V`. -/
def diagonalFibreMap {A₂ A₁ : BigFppfOver B V.left.obj V.left.property} (ψ : A₂ ⟶ A₁)
    (y : d.diagonalFibreObj A₁) : d.diagonalFibreObj A₂ :=
  have hc : (Over.map V.hom).map ψ ≫ toV A₁ = toV A₂ := Over.OverMorphism.ext (Over.w ψ)
  ⟨mapTriple c ((Over.map V.hom).map ψ) y.1,
    by rw [y.2.1, ← mapTriple_comp, hc], by rw [y.2.2, ← mapTriple_comp, hc]⟩

/-- **The fibre `F ×_{Δ, F × F} V`** of Stacks 0GHD, on the category of locally Noetherian schemes
over `V`. Here `F` is Artin's functor of Stacks 0GHA
(`AlgebraicGeometry.Artin.contractionFunctor c`), a locally Noetherian scheme `A` over `V` is
viewed over `S` through `V ⟶ S`, the diagonal is `Δ : F ⟶ F × F` and `V ⟶ F × F` is the pair
`(t₁, t₂) = ((Z₁, u'₁, x̂₁), (Z₂, u'₂, x̂₂))`. Since the structure morphism `A ⟶ V` of an object
over `V` is fixed, the value at `A` is the set of `y ∈ F(A)` with `y = φ^* t₁` and `y = φ^* t₂`. -/
def diagonalFibre : (LocallyNoetherianOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type (u + 1) where
  obj A := d.diagonalFibreObj A.unop.obj
  map ψ := ↾(d.diagonalFibreMap ψ.unop.hom)
  map_id A := by
    ext y
    exact @Subsingleton.elim _ (d.subsingleton_diagonalFibreObj _) _ _
  map_comp _ _ := by
    ext y
    exact @Subsingleton.elim _ (d.subsingleton_diagonalFibreObj _) _ _

/-- **The functor of the equalizer situation is the fibre `F ×_{Δ, F × F} V`.** For the data of
Stacks 0GHD over a locally Noetherian scheme `V`, the functor `F_{(4)}` of Stacks 0GHA for the
situation of assertion (4) (`AlgebraicGeometry.Artin.ContractionEqualizer.situation`), on the
locally Noetherian schemes over `V`, is isomorphic to `F ×_{Δ, F × F} V`: an element of
`F_{(4)}(A)` exists exactly when the two triples restrict to the same element of `F(A)`
(`mapTriple_eq_of_triple`, `nonempty_triple_situation_of_mapTriple_eq`, both through assertion
(5)), and it is then unique (`subsingleton_triple_situation`). -/
def contractionFunctorSituationIso :
    contractionFunctor (d.situation hVN) ≅ d.diagonalFibre :=
  NatIso.ofComponents (fun A => Equiv.toIso
    { toFun := fun τ => ⟨mapTriple c (toV A.unop.obj) d.t₁, rfl,
        d.mapTriple_eq_of_triple hVN A.unop.obj τ⟩
      invFun := fun y => (d.nonempty_triple_situation_of_mapTriple_eq hVN A.unop.obj
        A.unop.property (y.2.1.symm.trans y.2.2)).some
      left_inv := fun τ => @Subsingleton.elim _ (d.subsingleton_triple_situation hVN _) _ _
      right_inv := fun y => @Subsingleton.elim _ (d.subsingleton_diagonalFibreObj _) _ _ })
    (fun _ => by
      ext τ
      exact @Subsingleton.elim _ (d.subsingleton_diagonalFibreObj _) _ _)

end Artin.ContractionEqualizer

end AlgebraicGeometry

end
