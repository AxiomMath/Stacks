module

public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsLimits

/-!
# Comparing two Zariski sheaves which preserve affine limits

Let `S` be a scheme and let `𝒞` be a full subcategory of `Sch/S` which contains, up to
isomorphism, the affine schemes of finite presentation over the affine opens of `S`. A
transformation `θ : A ⟶ B` between two functors on `Sch/S` which are Zariski sheaves and take
directed inverse limits of affine schemes over `S` to filtered colimits is an isomorphism as soon
as it is bijective at every object of `𝒞`.

This is the pointwise form of the uniqueness clause of Stacks 0EUW. The uniqueness clause itself,
`AlgebraicGeometry.ExtendingFunctors.exists_unique_extension`, produces an *abstract* isomorphism
between two functors with isomorphic restrictions; what is proved here is that a *given*
transformation is an isomorphism, which is what is needed whenever the isomorphism has to be
compatible with further structure — for instance with a projection to a third functor.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.injective_app_of_bijective_isAffineOverAffineOpen`: a
  transformation of Zariski sheaves which is injective at the affine objects lying over affine
  opens of `S` is injective everywhere.
* `AlgebraicGeometry.ExtendingFunctors.bijective_app_of_bijective_isAffineOverAffineOpen`: the
  same for bijectivity.
* `AlgebraicGeometry.ExtendingFunctors.bijective_app_of_bijective_subcategory`: a transformation
  of functors preserving affine limits which is bijective at the objects of `𝒞` is bijective at
  every affine object lying over an affine open of `S`.
* `AlgebraicGeometry.ExtendingFunctors.isIso_of_bijective_subcategory`: the two steps combined.

## Implementation notes

Injectivity is proved first and separately, because the surjectivity step needs injectivity at the
*pairwise intersections* of the members of a covering, and those are not affine. Once injectivity
is known at every object, the sections produced over the members of a covering agree on the
overlaps and glue.

The passage from the objects of `𝒞` to the affine objects lying over affine opens of `S` is the
presentation `AlgebraicGeometry.ExtendingFunctors.exists_lfpPresentation` of such an object as a
directed inverse limit of objects of `𝒞`: limit preservation turns both sides into filtered
colimits over the same index category, and a natural transformation whose components are
isomorphisms induces an isomorphism of the colimits.

## References

* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}}

section Comparison

variable {A B : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))}

/-- **A transformation of Zariski sheaves is injective as soon as it is injective at the affine
objects lying over affine opens of `S`.** Two sections with the same image agree on the members of
a covering of their object by such objects, hence agree. -/
theorem injective_app_of_bijective_isAffineOverAffineOpen (haA : IsZariskiSheaf A) (θ : A ⟶ B)
    (hθ : ∀ V : Over S, IsAffineOverAffineOpen V → Function.Injective (θ.app (op V)))
    (X : Over S) : Function.Injective (θ.app (op X)) := by
  intro t t' h
  obtain ⟨ι, V, hcov, hVaff⟩ := exists_isAffineOverAffineOpen_cover X
  refine zariskiSheaf_ext haA V hcov t t' fun i => ?_
  refine hθ _ (hVaff i) ?_
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]

/-- **A transformation of Zariski sheaves is bijective as soon as it is bijective at the affine
objects lying over affine opens of `S`.** Injectivity is
`AlgebraicGeometry.ExtendingFunctors.injective_app_of_bijective_isAffineOverAffineOpen`; for
surjectivity, a section is lifted over each member of a covering of its object by such objects, the
lifts agree on the overlaps because injectivity is already known at *every* object, and the sheaf
property of the source glues them. -/
theorem bijective_app_of_bijective_isAffineOverAffineOpen (haA : IsZariskiSheaf A)
    (haB : IsZariskiSheaf B) (θ : A ⟶ B)
    (hθ : ∀ V : Over S, IsAffineOverAffineOpen V → Function.Bijective (θ.app (op V)))
    (X : Over S) : Function.Bijective (θ.app (op X)) := by
  have hinj : ∀ Y : Over S, Function.Injective (θ.app (op Y)) :=
    injective_app_of_bijective_isAffineOverAffineOpen haA θ (fun V hV => (hθ V hV).1)
  refine ⟨hinj X, fun b => ?_⟩
  obtain ⟨ι, V, hcov, hVaff⟩ := exists_isAffineOverAffineOpen_cover X
  choose s hs using fun i => (hθ _ (hVaff i)).2 (B.map (overOpenι X (V i)).op b)
  have hres : ∀ (i : ι) (W : X.left.Opens) (h : W ≤ V i),
      B.map (overOpenLE X h).op (B.map (overOpenι X (V i)).op b)
        = B.map (overOpenι X W).op b := by
    intro i W h
    rw [← Functor.map_comp_apply, ← op_comp, overOpenLE_comp_overOpenι]
  have hcompat : ∀ i j, A.map (overOpenLE X (inf_le_left : V i ⊓ V j ≤ V i)).op (s i)
      = A.map (overOpenLE X (inf_le_right : V i ⊓ V j ≤ V j)).op (s j) := by
    intro i j
    refine hinj (overOpen X (V i ⊓ V j)) ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hs i, hs j, hres i _ inf_le_left,
      hres j _ inf_le_right]
  obtain ⟨t, ht, -⟩ := haA X ι V hcov s hcompat
  refine ⟨t, ?_⟩
  refine zariskiSheaf_ext haB V hcov (θ.app (op X) t) b fun i => ?_
  rw [← NatTrans.naturality_apply, ht i, hs i]

variable {P : ObjectProperty (Over S)}

/-- **A transformation of functors preserving affine limits which is bijective at the objects of
`𝒞` is bijective at every affine object lying over an affine open of `S`.** Such an object is a
directed inverse limit of objects of `𝒞`, which both functors turn into filtered colimits; the
transformation is an isomorphism of the two diagrams, hence of the two colimits, and the induced
map of colimits is the transformation itself. -/
theorem bijective_app_of_bijective_subcategory (hP2 : HasFinitePresentationAffines P)
    (hbA : PreservesAffineLimits A) (hbB : PreservesAffineLimits B) (θ : A ⟶ B)
    (hθ : ∀ Z : Over S, P Z → Function.Bijective (θ.app (op Z)))
    (X : Over S) (hX : IsAffineOverAffineOpen X) : Function.Bijective (θ.app (op X)) := by
  obtain ⟨Λ, _, _, _, D, c, hc, ci, haff⟩ := exists_lfpPresentation hP2 X hX
  have hcX : IsLimit (c.extend ci.inv) :=
    hc.ofIsoLimit (Cone.ext ci fun j => (Iso.hom_inv_id_assoc ci (c.π.app j)).symm)
  obtain ⟨hcolA⟩ := hbA Λ (D ⋙ (lfpPart P).ι) haff (c.extend ci.inv) hcX
  obtain ⟨hcolB⟩ := hbB Λ (D ⋙ (lfpPart P).ι) haff (c.extend ci.inv) hcX
  have hiso : ∀ l, IsIso ((Functor.whiskerLeft (D ⋙ (lfpPart P).ι).op θ).app l) := by
    intro l
    rw [CategoryTheory.isIso_iff_bijective]
    exact hθ _ (D.obj l.unop).property.1
  have : IsIso (Functor.whiskerLeft (D ⋙ (lfpPart P).ι).op θ) := NatIso.isIso_of_isIso_app _
  have key : (IsColimit.coconePointsIsoOfNatIso hcolA hcolB
      (asIso (Functor.whiskerLeft (D ⋙ (lfpPart P).ι).op θ))).hom = θ.app (op X) := by
    refine hcolA.hom_ext fun l => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact (θ.naturality ((c.extend ci.inv).op.ι.app l)).symm
  have : IsIso (θ.app (op X)) := key ▸ inferInstance
  exact (CategoryTheory.isIso_iff_bijective _).1 this

/-- **A transformation between two Zariski sheaves preserving affine limits which is bijective at
every object of `𝒞` is an isomorphism.**

This is the pointwise form of the uniqueness clause of Stacks 0EUW: the isomorphism is the given
transformation rather than one produced out of nothing, so it is compatible with whatever further
structure the transformation is compatible with. -/
theorem isIso_of_bijective_subcategory (hP2 : HasFinitePresentationAffines P)
    (haA : IsZariskiSheaf A) (haB : IsZariskiSheaf B)
    (hbA : PreservesAffineLimits A) (hbB : PreservesAffineLimits B) (θ : A ⟶ B)
    (hθ : ∀ Z : Over S, P Z → Function.Bijective (θ.app (op Z))) : IsIso θ := by
  have : ∀ Z : (Over S)ᵒᵖ, IsIso (θ.app Z) := by
    intro Z
    rw [CategoryTheory.isIso_iff_bijective]
    exact bijective_app_of_bijective_isAffineOverAffineOpen haA haB θ
      (fun V hV => bijective_app_of_bijective_subcategory hP2 hbA hbB θ hθ V hV) Z.unop
  exact NatIso.isIso_of_isIso_app θ

end Comparison

end AlgebraicGeometry.ExtendingFunctors

end
