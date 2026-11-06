module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.UnionPreimageCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverGlue

/-!
# Glueing a morphism along a family of open immersions of the site

A family of open immersions of the big fppf category over `S` generating a covering sieve gives
a Zariski covering of the representable presheaf of its target by image subfunctors, so a
morphism into a sheaf glues along such a family. Applied to the `d` opens `gᵢ⁻¹(W)` of
`AlgebraicGeometry.Space.unionPreimageObj`, this glues a morphism out of that object.

## Main definitions

* `AlgebraicGeometry.Space.yonedaRangeFamily`: the family of image subfunctors of a family of
  morphisms of the site, and `AlgebraicGeometry.Space.yonedaRangeFamilyIso` the identification of
  each member with the representable presheaf it is the image of.
* `AlgebraicGeometry.Space.uliftPreimageObj` and
  `AlgebraicGeometry.Space.uliftUnionPreimageIncl`: the `d` opens `gᵢ⁻¹(W)` and their open
  immersions into `X'`, reindexed by `ULift (Fin d)` so that the index type lies in the working
  universe.

## Main results

* `AlgebraicGeometry.Space.isZariskiCover_yonedaRangeFamily`: a family of open immersions of the
  site generating a covering sieve gives a Zariski covering of the representable presheaf of its
  target.
* `AlgebraicGeometry.Space.glueYonedaHom_of_ofArrows_mem_topology`: a family of morphisms
  `yoneda.obj (U i) ⟶ Q` into a sheaf which agree on every common refinement glues to a unique
  morphism `yoneda.obj Z ⟶ Q`.
* `AlgebraicGeometry.Space.ofArrows_uliftUnionPreimageIncl_mem_topology`: the reindexed `d`
  opens still generate a covering sieve of `X'`.
* `AlgebraicGeometry.Space.glueHom_unionPreimageObj`: morphisms `gᵢ⁻¹(W) ⟶ X` into an algebraic
  space which agree on every common refinement glue to a unique morphism out of
  `AlgebraicGeometry.Space.unionPreimageObj`.

## References

* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Family

variable {I : Type u} {U : I → BigFppfOver B S hS} {Z : BigFppfOver B S hS}

/-- The family of image subfunctors of the representable presheaves of a family of morphisms of
the big fppf category over `S`. -/
abbrev yonedaRangeFamily (j : ∀ i, U i ⟶ Z) :
    I → Subfunctor (yoneda.obj Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun i ↦ Subfunctor.range (yoneda.map (j i))

/-- A family of open immersions of the site generating a covering sieve gives a Zariski covering
of the representable presheaf of its target by the image subfunctors of the family. -/
theorem isZariskiCover_yonedaRangeFamily (j : ∀ i, U i ⟶ Z)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcov : Sieve.ofArrows U j ∈ BigFppfOver.topology B S hS Z) :
    IsZariskiCover B S hS I (yonedaRangeFamily B S hS j) := by
  refine ⟨fun i ↦ isOpenSubspace_range_of_isOpenImmersion (U i) (yoneda.map (j i))
      (isOpenImmersion_yoneda_map B S hS (j i) (hj i)), ⟨fun {T} x ↦ ?_⟩⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable x hcov)
  rintro T' g hg
  obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  refine ⟨(Sigma.ι (fun i ↦ (yonedaRangeFamily B S hS j i).toFunctor) i).app (op T')
    ⟨g ≫ x, ⟨(a : T' ⟶ U i), ha.symm⟩⟩, ?_⟩
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (Sigma.ι_desc (fun i ↦ (yonedaRangeFamily B S hS j i).ι) i) (op T')) _

/-- The comparison isomorphism between the representable presheaf of `U i` and the image
subfunctor of `yoneda.map (j i)`, for a family of open immersions of the site. -/
def yonedaRangeFamilyIso (j : ∀ i, U i ⟶ Z)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i))) (i : I) :
    (yoneda.obj (U i) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ≅
      (yonedaRangeFamily B S hS j i).toFunctor :=
  rangeIsoOfIsOpenImmersion (U i) (yoneda.map (j i))
    (isOpenImmersion_yoneda_map B S hS (j i) (hj i))

/-- The comparison isomorphism `AlgebraicGeometry.Space.yonedaRangeFamilyIso`, followed by the
inclusion of the image subfunctor, is `yoneda.map (j i)`. -/
theorem yonedaRangeFamilyIso_hom_comp_ι (j : ∀ i, U i ⟶ Z)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i))) (i : I) :
    (yonedaRangeFamilyIso B S hS j hj i).hom ≫ (yonedaRangeFamily B S hS j i).ι =
      yoneda.map (j i) :=
  Subfunctor.toRange_ι (yoneda.map (j i))

/-- A section of the image subfunctor of `yoneda.map (j i)` is the arrow it comes from, composed
with `j i`. -/
theorem val_eq_yonedaRangeFamilyIso_inv_app (j : ∀ i, U i ⟶ Z)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i))) (i : I) (T : (BigFppfOver B S hS)ᵒᵖ)
    (x : (yonedaRangeFamily B S hS j i).toFunctor.obj T) :
    x.val = (yonedaRangeFamilyIso B S hS j hj i).inv.app T x ≫ j i := by
  have hx : (yonedaRangeFamilyIso B S hS j hj i).hom.app T
      ((yonedaRangeFamilyIso B S hS j hj i).inv.app T x) = x := by
    rw [← NatTrans.comp_app_apply, (yonedaRangeFamilyIso B S hS j hj i).inv_hom_id]
    rfl
  have h1 := Subfunctor.toRange_app_val (yoneda.map (j i))
    ((yonedaRangeFamilyIso B S hS j hj i).inv.app T x)
  rw [show Subfunctor.toRange (yoneda.map (j i)) =
    (yonedaRangeFamilyIso B S hS j hj i).hom from rfl, hx] at h1
  exact h1

/-- Let `j i : U i ⟶ Z` be a family of morphisms of the big fppf category over `S` which are open
immersions of schemes and generate a covering sieve, and let `Q` be a sheaf. A family of
morphisms `φ i : yoneda.obj (U i) ⟶ Q` which agree on every common refinement — whenever
`a : T ⟶ U i` and `a' : T ⟶ U i'` have `a ≫ j i = a' ≫ j i'` — glues to a unique morphism
`yoneda.obj Z ⟶ Q` restricting to each of them. -/
theorem glueYonedaHom_of_ofArrows_mem_topology (j : ∀ i, U i ⟶ Z)
    (hj : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i)))
    (hcov : Sieve.ofArrows U j ∈ BigFppfOver.topology B S hS Z)
    {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q)
    (φ : ∀ i, (yoneda.obj (U i) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ Q)
    (hφ : ∀ (T : BigFppfOver B S hS) (i i' : I) (a : T ⟶ U i) (a' : T ⟶ U i'),
      a ≫ j i = a' ≫ j i' → yoneda.map a ≫ φ i = yoneda.map a' ≫ φ i') :
    ∃! ψ : (yoneda.obj Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ Q,
      ∀ i, yoneda.map (j i) ≫ ψ = φ i := by
  have hcompat : ∀ (T : (BigFppfOver B S hS)ᵒᵖ) (i i' : I)
      (x : (yonedaRangeFamily B S hS j i).toFunctor.obj T)
      (y : (yonedaRangeFamily B S hS j i').toFunctor.obj T),
      (yonedaRangeFamily B S hS j i).ι.app T x = (yonedaRangeFamily B S hS j i').ι.app T y →
        ((yonedaRangeFamilyIso B S hS j hj i).inv ≫ φ i).app T x =
          ((yonedaRangeFamilyIso B S hS j hj i').inv ≫ φ i').app T y := by
    intro T i i' x y hxy
    obtain ⟨T⟩ := T
    have hxy' : (yonedaRangeFamilyIso B S hS j hj i).inv.app (op T) x ≫ j i =
        (yonedaRangeFamilyIso B S hS j hj i').inv.app (op T) y ≫ j i' := by
      rw [← val_eq_yonedaRangeFamilyIso_inv_app B S hS j hj i (op T) x,
        ← val_eq_yonedaRangeFamilyIso_inv_app B S hS j hj i' (op T) y]
      exact hxy
    have happ := congrArg
      (fun t : (yoneda.obj T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ Q ↦ t.app (op T) (𝟙 T))
      (hφ T i i' ((yonedaRangeFamilyIso B S hS j hj i).inv.app (op T) x)
        ((yonedaRangeFamilyIso B S hS j hj i').inv.app (op T) y) hxy')
    simpa [NatTrans.comp_app_apply] using happ
  obtain ⟨ψ, hψ, huniq⟩ := glueHom_of_isZariskiCover B S hS (yonedaRangeFamily B S hS j)
    (isZariskiCover_yonedaRangeFamily B S hS j hj hcov) hQ
    (fun i ↦ (yonedaRangeFamilyIso B S hS j hj i).inv ≫ φ i) hcompat
  refine ⟨ψ, fun i ↦ ?_, fun ψ' hψ' ↦ huniq ψ' fun i ↦ ?_⟩
  · rw [← yonedaRangeFamilyIso_hom_comp_ι B S hS j hj i, Category.assoc, hψ i,
      Iso.hom_inv_id_assoc]
  · refine ((yonedaRangeFamilyIso B S hS j hj i).cancel_iso_hom_left _ _).1 ?_
    rw [Iso.hom_inv_id_assoc, ← Category.assoc,
      yonedaRangeFamilyIso_hom_comp_ι B S hS j hj i, hψ' i]

end Family

section UnionPreimage

variable (Z : BigFppfOver B S hS) {Y : Scheme.{u}} {n : ℕ}
    (g : Fin n → (Z.left.obj ⟶ Y)) (W : Y.Opens)

/-- The `d` opens `gᵢ⁻¹(W)` of `AlgebraicGeometry.Space.unionPreimageObj`, reindexed by
`ULift (Fin d)`. -/
def uliftPreimageObj (i : ULift.{u} (Fin n)) : BigFppfOver B S hS :=
  preimageObj B S hS Z g W i.down

/-- The `d` open immersions `gᵢ⁻¹(W) ⟶ X'`, reindexed by `ULift (Fin d)`. -/
def uliftUnionPreimageIncl (i : ULift.{u} (Fin n)) :
    uliftPreimageObj B S hS Z g W i ⟶ unionPreimageObj B S hS Z g W :=
  unionPreimageIncl B S hS Z g W i.down

/-- The `d` opens `gᵢ⁻¹(W)`, reindexed by `ULift (Fin d)`, generate a covering sieve of
`AlgebraicGeometry.Space.unionPreimageObj` in the big fppf category over `S`. -/
theorem ofArrows_uliftUnionPreimageIncl_mem_topology :
    Sieve.ofArrows (uliftPreimageObj B S hS Z g W) (uliftUnionPreimageIncl B S hS Z g W) ∈
      BigFppfOver.topology B S hS (unionPreimageObj B S hS Z g W) := by
  refine BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion B S hS _
    (fun i ↦ isOpenImmersion_unionPreimageIncl B S hS Z g W i.down) fun x ↦ ?_
  obtain ⟨i, hi⟩ := (mem_unionPreimageOpens B S hS Z g W x.1).1 x.2
  refine ⟨⟨i⟩, ⟨⟨x.1, hi⟩, ?_⟩⟩
  rw [show (BigFppfOver.toScheme B S hS).map (uliftUnionPreimageIncl B S hS Z g W ⟨i⟩) =
    Z.left.obj.homOfLE (preimage_le_unionPreimageOpens B S hS Z g W i) from rfl]
  exact Subtype.ext (congrArg Subtype.val
    (Scheme.homOfLE_apply' (preimage_le_unionPreimageOpens B S hS Z g W i) x.1 hi))

/-- A family of morphisms from the `d` opens `gᵢ⁻¹(W)` into an algebraic space `X` which agree on
every common refinement glues to a unique morphism `X' ⟶ X` out of
`AlgebraicGeometry.Space.unionPreimageObj` restricting to each of them. -/
theorem glueHom_unionPreimageObj {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (φ : ∀ i : ULift.{u} (Fin n),
      (yoneda.obj (uliftPreimageObj B S hS Z g W i) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X)
    (hφ : ∀ (T : BigFppfOver B S hS) (i i' : ULift.{u} (Fin n))
      (a : T ⟶ uliftPreimageObj B S hS Z g W i)
      (a' : T ⟶ uliftPreimageObj B S hS Z g W i'),
      a ≫ uliftUnionPreimageIncl B S hS Z g W i =
          a' ≫ uliftUnionPreimageIncl B S hS Z g W i' →
        yoneda.map a ≫ φ i = yoneda.map a' ≫ φ i') :
    ∃! ψ : (yoneda.obj (unionPreimageObj B S hS Z g W) :
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⟶ X,
      ∀ i, yoneda.map (uliftUnionPreimageIncl B S hS Z g W i) ≫ ψ = φ i :=
  glueYonedaHom_of_ofArrows_mem_topology B S hS (uliftUnionPreimageIncl B S hS Z g W)
    (fun i ↦ isOpenImmersion_unionPreimageIncl B S hS Z g W i.down)
    (ofArrows_uliftUnionPreimageIncl_mem_topology B S hS Z g W) hX.isSheaf φ hφ

end UnionPreimage

end AlgebraicGeometry.Space

end
