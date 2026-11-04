module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTarget
public import
  StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreEtaleRefinement

/-!
# The relative weak assassin is insensitive to an étale morphism of the target

Let `g : X ⟶ Y'` be a morphism of algebraic spaces over `S`, let `ψ : Y' ⟶ Y` be étale and let
`𝓕` be an `𝒪_X`-module. Then the two relative weak assassins agree:

`WeakAss_{X/Y'}(𝓕) = WeakAss_{X/Y}(𝓕)`.

## Main results

* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_of_comp_of_isEtale`: a point of
  `WeakAss_{X/Y}(𝓕)` lies in `WeakAss_{X/Y'}(𝓕)`.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale` and
  `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_comp_eq_of_isEtale`: the equality of
  the two relative weak assassins, as a biconditional and as a set equality.

## References

* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Y' : AlgebraicSpaces B S hS}

/-- For `ψ : Y' ⟶ Y` étale and a field-valued point `p` of `Y`, the projection of the fibre of
`ψ` over `p` to the spectrum of the field is étale. -/
theorem isEtale_pullback_snd_fieldMorphism (ψ : Y' ⟶ Y) (hψ : IsEtale B S hS ψ.hom)
    (p : FieldValuedPoint B S hS Y.1) :
    IsEtale B S hS (pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p)) :=
  isEtale_of_isPullback B S hS (fibreAtFieldValuedPointProjection B S hS ψ p)
    (fibreAtFieldValuedPointStructure B S hS ψ p) ψ
    (ObjectProperty.homMk (fieldMorphism B S hS Y.1 p) :
      fieldValuedPointSpace B S hS p ⟶ Y)
    (IsPullback.of_map_of_faithful (ObjectProperty.ι fun G ↦ IsAlgebraicSpace B S hS G)
      (IsPullback.of_hasPullback ψ.hom (fieldMorphism B S hS Y.1 p))) hψ

/-- Let `g : X ⟶ Y'`, let `ψ : Y' ⟶ Y`, let `p` be a field-valued point of `Y` and let `P` be a
field-valued point of `Y'` presented by an étale morphism `ξ : Spec L ⟶ N = Y' ×_Y Spec k`
compatible with the two projections, where `κ` is the induced morphism of field spectra. If `θ`
is a point of `X ×_Y Spec k` above `x`, weakly associated to the restriction of `𝓕` and whose
image in `|N|` is the image of a point `ρ` of `Spec L`, then `x` is the image of a point of
`X ×_{Y'} Spec L` weakly associated to the restriction of `𝓕`. -/
private theorem isWeaklyAssociatedOnFibre_of_isEtale_fieldSpaceMap
    (g : X ⟶ Y') (ψ : Y' ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    {x : points B S hS X.1} (p : FieldValuedPoint B S hS Y.1)
    (P : FieldValuedPoint B S hS Y'.1) (κ : P.siteObject ⟶ p.siteObject)
    (ξ : fieldValuedPointSpace B S hS P ⟶ fibreAtFieldValuedPoint B S hS ψ p)
    (hξproj : ξ.hom ≫ (fibreAtFieldValuedPointProjection B S hS ψ p).hom =
      fieldMorphism B S hS Y'.1 P)
    (hξsnd : ξ.hom ≫ pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p) = yoneda.map κ)
    (hξet : IsEtale B S hS ξ.hom)
    {θ : points B S hS (fibreAtFieldValuedPoint B S hS (g ≫ ψ) p).1}
    (hθ : pointsMap B S hS (fibreAtFieldValuedPoint B S hS (g ≫ ψ) p).1
      (fibreAtFieldValuedPointProjection B S hS (g ≫ ψ) p).hom θ = x)
    (ρ : points B S hS (yoneda.obj P.siteObject))
    (hρ : pointsMap B S hS (yoneda.obj P.siteObject) ξ.hom ρ =
      pointsMap B S hS (fibreAtFieldValuedPoint B S hS (g ≫ ψ) p).1
        (fibreAtFieldValuedPointMap B S hS g ψ p).hom θ)
    (hwa : IsWeaklyAssociatedPoint B S hS (fibreAtFieldValuedPoint B S hS (g ≫ ψ) p)
      ((modulePullback B S hS (fibreAtFieldValuedPointProjection B S hS (g ≫ ψ) p)).obj F) θ) :
    IsWeaklyAssociatedOnFibre B S hS g F P x := by
  have hξprojfst : ξ.hom ≫ pullback.fst ψ.hom (fieldMorphism B S hS Y.1 p) =
      fieldMorphism B S hS Y'.1 P := hξproj
  have hκp : yoneda.map κ ≫ fieldMorphism B S hS Y.1 p =
      fieldMorphism B S hS Y'.1 P ≫ ψ.hom := by
    rw [← hξsnd, ← hξprojfst, Category.assoc, Category.assoc, pullback.condition]
  have hlift : pullback.fst g.hom (fieldMorphism B S hS Y'.1 P) ≫ (g ≫ ψ).hom =
      (pullback.snd g.hom (fieldMorphism B S hS Y'.1 P) ≫ yoneda.map κ) ≫
        fieldMorphism B S hS Y.1 p := by
    rw [Category.assoc, hκp, show (g ≫ ψ).hom = g.hom ≫ ψ.hom from rfl, ← Category.assoc,
      pullback.condition, Category.assoc]
  obtain ⟨lam, hlamfst, hlamsnd⟩ :
      ∃ lam : fibreAtFieldValuedPoint B S hS g P ⟶ fibreAtFieldValuedPoint B S hS (g ≫ ψ) p,
        lam.hom ≫ pullback.fst (g ≫ ψ).hom (fieldMorphism B S hS Y.1 p) =
            pullback.fst g.hom (fieldMorphism B S hS Y'.1 P) ∧
          lam.hom ≫ pullback.snd (g ≫ ψ).hom (fieldMorphism B S hS Y.1 p) =
            pullback.snd g.hom (fieldMorphism B S hS Y'.1 P) ≫ yoneda.map κ :=
    ⟨ObjectProperty.homMk (pullback.lift _ _ hlift), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have hlamprojhom : lam.hom ≫ (fibreAtFieldValuedPointProjection B S hS (g ≫ ψ) p).hom =
      (fibreAtFieldValuedPointProjection B S hS g P).hom := hlamfst
  have hlamproj : lam ≫ fibreAtFieldValuedPointProjection B S hS (g ≫ ψ) p =
      fibreAtFieldValuedPointProjection B S hS g P :=
    (ObjectProperty.fullyFaithfulι _).map_injective hlamprojhom
  have sq : IsPullback lam.hom (pullback.snd g.hom (fieldMorphism B S hS Y'.1 P))
      (fibreAtFieldValuedPointMap B S hS g ψ p).hom ξ.hom := by
    refine IsPullback.of_right ?_ ?_ (isPullback_fibreAtFieldValuedPointMap_hom B S hS g ψ p)
    · rw [hlamprojhom, hξproj]
      exact IsPullback.of_hasPullback g.hom (fieldMorphism B S hS Y'.1 P)
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, show (fibreAtFieldValuedPointMap B S hS g ψ p).hom ≫
              pullback.fst ψ.hom (fieldMorphism B S hS Y.1 p) =
            pullback.fst (g ≫ ψ).hom (fieldMorphism B S hS Y.1 p) ≫ g.hom from
              pullback.lift_fst _ _ _,
          ← Category.assoc, hlamfst, pullback.condition, Category.assoc, hξprojfst]
      · rw [Category.assoc, show (fibreAtFieldValuedPointMap B S hS g ψ p).hom ≫
              pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p) =
            pullback.snd (g ≫ ψ).hom (fieldMorphism B S hS Y.1 p) from
              pullback.lift_snd _ _ _,
          hlamsnd, Category.assoc, hξsnd]
  have sq' : IsPullback lam (fibreAtFieldValuedPointStructure B S hS g P)
      (fibreAtFieldValuedPointMap B S hS g ψ p) ξ :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι fun G ↦ IsAlgebraicSpace B S hS G) sq
  have hlamet : IsEtale B S hS lam.hom :=
    isEtale_of_isPullback B S hS (fibreAtFieldValuedPointStructure B S hS g P) lam ξ
      (fibreAtFieldValuedPointMap B S hS g ψ p) sq'.flip hξet
  obtain ⟨ζ, hζ, -⟩ := exists_point_of_isPullback B S hS sq' θ ρ hρ.symm
  refine ⟨ζ, ?_, ?_⟩
  · have h := congrArg
      (fun k ↦ pointsMap B S hS (fibreAtFieldValuedPoint B S hS g P).1 k ζ) hlamprojhom
    simp only [pointsMap_comp, Function.comp_apply] at h
    rw [← h, hζ, hθ]
  · exact (isWeaklyAssociatedPoint_congr B S hS
      ((modulePullbackCompIso B S hS lam
            (fibreAtFieldValuedPointProjection B S hS (g ≫ ψ) p)).app F ≪≫
        eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj F) hlamproj)) ζ).1
      ((isWeaklyAssociatedPoint_modulePullback_iff B S hS lam hlamet _ ζ).2 (hζ ▸ hwa))

/-- Let `g : X ⟶ Y'` be a morphism of algebraic spaces over `S`, let `ψ : Y' ⟶ Y` be étale and
let `𝓕` be an `𝒪_X`-module. A point of `WeakAss_{X/Y}(𝓕)` lies in `WeakAss_{X/Y'}(𝓕)`. -/
theorem isRelativeWeaklyAssociatedPoint_of_comp_of_isEtale (g : X ⟶ Y') (ψ : Y' ⟶ Y)
    (hψ : IsEtale B S hS ψ.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    {x : points B S hS X.1}
    (hx : IsRelativeWeaklyAssociatedPoint B S hS (g ≫ ψ) F x) :
    IsRelativeWeaklyAssociatedPoint B S hS g F x := by
  obtain ⟨p, -, θ, hθ, hwa⟩ := hx
  obtain ⟨n, hn, hnet⟩ := exists_fieldValuedPoint_fibre_isEtale_siteHom B S hS ψ hψ p
    (pointsMap B S hS (fibreAtFieldValuedPoint B S hS (g ≫ ψ) p).1
      (fibreAtFieldValuedPointMap B S hS g ψ p).hom θ)
  have hξsnd : fieldMorphism B S hS (fibreAtFieldValuedPoint B S hS ψ p).1 n ≫
        pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p) =
      yoneda.map (FieldValuedPoint.map B S hS (fibreAtFieldValuedPoint B S hS ψ p).1
        (pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p)) n).siteHom :=
    (fieldMorphism_map B S hS (fibreAtFieldValuedPoint B S hS ψ p).1
        (pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p)) n).symm.trans
      (fieldMorphism_yoneda B S hS (FieldValuedPoint.map B S hS
        (fibreAtFieldValuedPoint B S hS ψ p).1
        (pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p)) n))
  have hξproj : fieldMorphism B S hS (fibreAtFieldValuedPoint B S hS ψ p).1 n ≫
        (fibreAtFieldValuedPointProjection B S hS ψ p).hom =
      fieldMorphism B S hS Y'.1 (FieldValuedPoint.map B S hS
        (fibreAtFieldValuedPoint B S hS ψ p).1
        (fibreAtFieldValuedPointProjection B S hS ψ p).hom n) :=
    (fieldMorphism_map B S hS (fibreAtFieldValuedPoint B S hS ψ p).1
      (fibreAtFieldValuedPointProjection B S hS ψ p).hom n).symm
  have hξet : IsEtale B S hS
      (fieldMorphism B S hS (fibreAtFieldValuedPoint B S hS ψ p).1 n) :=
    isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS n.siteObject)
      (fibreAtFieldValuedPoint B S hS ψ p).2 (isAlgebraicSpace_yoneda B S hS p.siteObject)
      (fieldMorphism B S hS (fibreAtFieldValuedPoint B S hS ψ p).1 n)
      (yoneda.map (FieldValuedPoint.map B S hS (fibreAtFieldValuedPoint B S hS ψ p).1
        (pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p)) n).siteHom)
      (pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p)) hnet
      (isEtale_pullback_snd_fieldMorphism B S hS ψ hψ p) hξsnd
  have hPclass : (FieldValuedPoint.map B S hS (fibreAtFieldValuedPoint B S hS ψ p).1
        (fibreAtFieldValuedPointProjection B S hS ψ p).hom n).class B S hS Y'.1 =
      pointsMap B S hS X.1 g.hom x := by
    rw [← pointsMap_class, hn, pointsMap_fibreAtFieldValuedPointMap B S hS g ψ p θ, hθ]
  refine isRelativeWeaklyAssociatedPoint_of_isWeaklyAssociatedOnFibre B S hS g F hPclass
    (isWeaklyAssociatedOnFibre_of_isEtale_fieldSpaceMap B S hS g ψ F p _
      (FieldValuedPoint.map B S hS (fibreAtFieldValuedPoint B S hS ψ p).1
        (pullback.snd ψ.hom (fieldMorphism B S hS Y.1 p)) n).siteHom
      (ObjectProperty.homMk (fieldMorphism B S hS (fibreAtFieldValuedPoint B S hS ψ p).1 n))
      hξproj hξsnd hξet hθ
      ((n.tautologicalPoint B S hS (fibreAtFieldValuedPoint B S hS ψ p).1).class B S hS
        (yoneda.obj n.siteObject))
      ((pointsMap_fieldMorphism_tautologicalPoint B S hS
        (fibreAtFieldValuedPoint B S hS ψ p).1 n).trans hn) hwa)

/-- For `g : X ⟶ Y'` and `ψ : Y' ⟶ Y` étale, a point of `X` lies in `WeakAss_{X/Y}(𝓕)` if and
only if it lies in `WeakAss_{X/Y'}(𝓕)`. -/
theorem isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale (g : X ⟶ Y') (ψ : Y' ⟶ Y)
    (hψ : IsEtale B S hS ψ.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (x : points B S hS X.1) :
    IsRelativeWeaklyAssociatedPoint B S hS (g ≫ ψ) F x ↔
      IsRelativeWeaklyAssociatedPoint B S hS g F x :=
  ⟨isRelativeWeaklyAssociatedPoint_of_comp_of_isEtale B S hS g ψ hψ F,
    isRelativeWeaklyAssociatedPoint_comp_of_isEtale B S hS g ψ hψ F⟩

/-- For `g : X ⟶ Y'` and `ψ : Y' ⟶ Y` étale, `WeakAss_{X/Y}(𝓕) = WeakAss_{X/Y'}(𝓕)`. -/
theorem relativeWeaklyAssociatedPoints_comp_eq_of_isEtale (g : X ⟶ Y') (ψ : Y' ⟶ Y)
    (hψ : IsEtale B S hS ψ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    relativeWeaklyAssociatedPoints B S hS (g ≫ ψ) F =
      relativeWeaklyAssociatedPoints B S hS g F :=
  Set.ext fun x ↦ isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale B S hS g ψ hψ F x

end AlgebraicGeometry.Space

end
