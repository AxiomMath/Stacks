module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# The open image of an étale morphism of the site, and factorization through it

Let `ψ : Y' ⟶ Y` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is étale.  Its image is open, so it is an open subscheme of `Y`, again an object of the
site.  This file constructs that object `etaleOpenImage ψ`, the open immersion
`etaleOpenImageι ψ : etaleOpenImage ψ ⟶ Y`, the factorization `etaleOpenImageLift ψ` of `ψ`
through it, which is étale and surjective, and the factorization through `etaleOpenImage ψ` of a
morphism of the site whose image lies in the image of `ψ`.

## Main definitions

* `AlgebraicGeometry.Space.etaleOpenImage`: the open image of `ψ`, as an object of the site.
* `AlgebraicGeometry.Space.etaleOpenImageι`: its inclusion into `Y`.
* `AlgebraicGeometry.Space.etaleOpenImageLift`: the factorization of `ψ` through the image.
* `AlgebraicGeometry.Space.etaleOpenImageFactor`: the factorization of a morphism whose image lies
  in the image of `ψ`.

## Main results

* `AlgebraicGeometry.Space.etaleOpenImageLift_comp_ι`, `etale_etaleImageLift`,
  `surjective_etaleImageLift`, `etaleOpenImageFactor_comp_ι`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y Y' : BigFppfOver B S hS} (ψ : Y' ⟶ Y) [Etale ((BigFppfOver.toScheme B S hS).map ψ)]

/-- The open image of an étale morphism of the site, as an open subset of the target. -/
def etaleOpenImageOpens : ((BigFppfOver.toScheme B S hS).obj Y).Opens :=
  ⟨Set.range ((BigFppfOver.toScheme B S hS).map ψ),
    ((BigFppfOver.toScheme B S hS).map ψ).isOpenMap.isOpen_range⟩

/-- The inclusion of the open image of `ψ` into the target is an open immersion. -/
instance isOpenImmersion_etaleImageOpens_ι :
    _root_.AlgebraicGeometry.IsOpenImmersion (etaleOpenImageOpens B S hS ψ).ι :=
  inferInstance

/-- The open image of `ψ`, as a scheme, lies in the big fppf site `B`. -/
theorem contains_etaleImage :
    B.Contains (etaleOpenImageOpens B S hS ψ : Scheme.{u}) :=
  Scheme.size_lt_of_isOpenImmersion (etaleOpenImageOpens B S hS ψ).ι Y.left.property

/-- The open image of an étale morphism of the site, as an object of the site. -/
def etaleOpenImage : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_etaleImage B S hS ψ)
    ((etaleOpenImageOpens B S hS ψ).ι ≫ B.inclusion.map Y.hom)

/-- The inclusion of the open image. -/
def etaleOpenImageι : etaleOpenImage B S hS ψ ⟶ Y :=
  Over.homMk (ObjectProperty.homMk (etaleOpenImageOpens B S hS ψ).ι) (by
    apply ObjectProperty.hom_ext
    rfl)

/-- The underlying morphism of schemes of `etaleOpenImageι ψ` is the inclusion of the open
subscheme `etaleOpenImageOpens ψ`. -/
theorem toScheme_map_etaleImageι :
    (BigFppfOver.toScheme B S hS).map (etaleOpenImageι B S hS ψ) =
      (etaleOpenImageOpens B S hS ψ).ι :=
  rfl

/-- The underlying morphism of schemes of `etaleOpenImageι ψ` is an open immersion. -/
instance : _root_.AlgebraicGeometry.IsOpenImmersion
    ((BigFppfOver.toScheme B S hS).map (etaleOpenImageι B S hS ψ)) :=
  isOpenImmersion_etaleImageOpens_ι B S hS ψ

/-- The factorization through the image of a morphism of the site whose underlying image lies
in the image of `ψ`. -/
def etaleOpenImageFactor {V : BigFppfOver B S hS} (a : V ⟶ Y)
    (ha : Set.range ((BigFppfOver.toScheme B S hS).map a) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map ψ)) :
    V ⟶ etaleOpenImage B S hS ψ :=
  BigFppfOver.homMk B S hS (contains_etaleImage B S hS ψ) _
    (_root_.AlgebraicGeometry.IsOpenImmersion.lift
      (H := isOpenImmersion_etaleImageOpens_ι B S hS ψ) (etaleOpenImageOpens B S hS ψ).ι
      ((BigFppfOver.toScheme B S hS).map a) (by rwa [Scheme.Opens.range_ι])) (by
      rw [← Category.assoc, _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac
        (H := isOpenImmersion_etaleImageOpens_ι B S hS ψ)]
      exact congrArg (fun k ↦ k.hom) (Over.w a))

/-- The factorization `etaleOpenImageFactor ψ a ha` composed with the inclusion of the open image
is `a`. -/
theorem etaleOpenImageFactor_comp_ι {V : BigFppfOver B S hS} (a : V ⟶ Y)
    (ha : Set.range ((BigFppfOver.toScheme B S hS).map a) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map ψ)) :
    etaleOpenImageFactor B S hS ψ a ha ≫ etaleOpenImageι B S hS ψ = a :=
  (BigFppfOver.toScheme B S hS).map_injective (((BigFppfOver.toScheme B S hS).map_comp _ _).trans
    (_root_.AlgebraicGeometry.IsOpenImmersion.lift_fac
      (H := isOpenImmersion_etaleImageOpens_ι B S hS ψ) _ _ _))

/-- The factorization of `ψ` through its image. -/
def etaleOpenImageLift : Y' ⟶ etaleOpenImage B S hS ψ :=
  etaleOpenImageFactor B S hS ψ ψ subset_rfl

/-- The factorization `etaleOpenImageLift ψ` composed with the inclusion of the open image is `ψ`.
-/
theorem etaleOpenImageLift_comp_ι :
    etaleOpenImageLift B S hS ψ ≫ etaleOpenImageι B S hS ψ = ψ :=
  etaleOpenImageFactor_comp_ι B S hS ψ ψ subset_rfl

/-- Composing the underlying morphism of `etaleOpenImageLift ψ` with the inclusion gives `ψ`. -/
private theorem map_etaleOpenImageLift_comp_map_ι :
    (BigFppfOver.toScheme B S hS).map (etaleOpenImageLift B S hS ψ) ≫
      (BigFppfOver.toScheme B S hS).map (etaleOpenImageι B S hS ψ) =
        (BigFppfOver.toScheme B S hS).map ψ := by
  rw [← Functor.map_comp, etaleOpenImageLift_comp_ι]

/-- The underlying morphism of schemes of `etaleOpenImageLift ψ` is étale. -/
theorem etale_etaleImageLift :
    Etale ((BigFppfOver.toScheme B S hS).map (etaleOpenImageLift B S hS ψ)) := by
  have : Etale ((BigFppfOver.toScheme B S hS).map (etaleOpenImageLift B S hS ψ) ≫
      (BigFppfOver.toScheme B S hS).map (etaleOpenImageι B S hS ψ)) := by
    rw [map_etaleOpenImageLift_comp_map_ι]
    infer_instance
  exact Etale.of_comp _ ((BigFppfOver.toScheme B S hS).map (etaleOpenImageι B S hS ψ))

/-- The underlying morphism of schemes of `etaleOpenImageLift ψ` is surjective. -/
theorem surjective_etaleImageLift :
    Surjective ((BigFppfOver.toScheme B S hS).map (etaleOpenImageLift B S hS ψ)) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨y', hy'⟩ : (etaleOpenImageOpens B S hS ψ).ι y ∈
      Set.range ((BigFppfOver.toScheme B S hS).map ψ) :=
    (Scheme.Opens.range_ι (etaleOpenImageOpens B S hS ψ)).subset (Set.mem_range_self y)
  refine ⟨y', (etaleOpenImageOpens B S hS ψ).ι.isOpenEmbedding.injective ?_⟩
  exact congr($(map_etaleOpenImageLift_comp_map_ι B S hS ψ) y').trans hy'

end AlgebraicGeometry.Space

end
