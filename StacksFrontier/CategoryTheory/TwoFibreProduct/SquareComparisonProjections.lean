module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CategoricalPullbackSquareDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Functoriality

/-!
# Every functor into an explicit 2-fibre product is the comparison of a square

A functor `F : C' ⥤ p ⊡ b` into the explicit 2-fibre product of Stacks 003R *is* a 2-commutative
square over the cospan `(p, b)`: its two projections are the upper and left legs, and the
structural isomorphism of `F x` is the filler read at `x`. This file records that
identification: `F` is the comparison functor
`CategoryTheory.Limits.CategoricalPullback.squareComparison` of that square.

## Main definitions

* `CategoryTheory.Limits.CategoricalPullback.projFiller`: the filler of the square read off `F`.
* `CategoryTheory.Limits.CategoricalPullback.projFillerOfEq`: the same filler, for legs given
  up to equality.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.squareComparison_proj`: `F` is the comparison
  functor of that square.
* `CategoryTheory.Limits.CategoricalPullback.squareComparison_projOfEq`: the same, for legs given
  up to equality.
* `CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_projOfEq`: a square
  whose data agrees with that of an equivalence into `p ⊡ b` is 2-cartesian.
* `CategoryTheory.Limits.CategoricalPullback.map_comp_π₁` and
  `CategoryTheory.Limits.CategoricalPullback.map_comp_π₂`: the action of a change of cospan on
  the two projections.

## References

* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C' : Type u₁} {C : Type u₂} {D' : Type u₃} {D : Type u₄}
  [Category.{v₁} C'] [Category.{v₂} C] [Category.{v₃} D'] [Category.{v₄} D]
  (p : C ⥤ D) (b : D' ⥤ D)

/-- **The filler of the square read off a functor into the explicit 2-fibre product.** It is the
canonical filler of `p ⊡ b` -- the structural isomorphism of each object -- whiskered into `F`. -/
def projFiller (F : C' ⥤ p ⊡ b) : (F ⋙ π₁ p b) ⋙ p ≅ (F ⋙ π₂ p b) ⋙ b :=
  Functor.isoWhiskerLeft F (catCommSq p b).iso

/-- The filler `projFiller` at an object `x` is the structural isomorphism of `F x`. -/
@[simp] lemma projFiller_hom_app (F : C' ⥤ p ⊡ b) (x : C') :
    (projFiller p b F).hom.app x = (F.obj x).iso.hom := rfl

/-- **A functor into an explicit 2-fibre product is the comparison functor of its own square.**
Both sides send `x` to the triple consisting of the two projections of `F x` and the structural
isomorphism of `F x`. -/
lemma squareComparison_proj (F : C' ⥤ p ⊡ b) :
    squareComparison (F ⋙ π₁ p b) (F ⋙ π₂ p b) p b (projFiller p b F) = F := rfl

variable (a : C' ⥤ C) (u : C' ⥤ D')

/-- **The filler of a square whose legs are named separately.** Given a functor `F` into
`p ⊡ b` whose projections are known to be `a` and `u`, this transports
`CategoryTheory.Limits.CategoricalPullback.projFiller` into a filler for the square
`(a, u, p, b)`. -/
def projFillerOfEq (F : C' ⥤ p ⊡ b) (ha : F ⋙ π₁ p b = a) (hu : F ⋙ π₂ p b = u) :
    a ⋙ p ≅ u ⋙ b :=
  eqToIso (congrArg (· ⋙ p) ha.symm) ≪≫ projFiller p b F ≪≫
    eqToIso (congrArg (· ⋙ b) hu)

/-- **The filler of a square named by the projections of a functor, read at an object**: the
structural isomorphism of the functor's value, between the two transports the renaming of the
legs contributes. -/
lemma projFillerOfEq_hom_app (F : C' ⥤ p ⊡ b) (ha : F ⋙ π₁ p b = a) (hu : F ⋙ π₂ p b = u)
    (x : C') :
    (projFillerOfEq p b a u F ha hu).hom.app x =
      eqToHom ((Functor.congr_obj (congrArg (· ⋙ p) ha.symm) x).trans
            ((Functor.comp_obj (F ⋙ π₁ p b) p x).trans
              (congrArg p.obj ((Functor.comp_obj F (π₁ p b) x).trans
                (π₁_obj p b (F.obj x)))))) ≫
          (F.obj x).iso.hom ≫
        eqToHom ((((congrArg b.obj ((π₂_obj p b (F.obj x)).symm.trans
                (Functor.comp_obj F (π₂ p b) x).symm)).trans
              (Functor.comp_obj (F ⋙ π₂ p b) b x).symm)).trans
          (Functor.congr_obj (congrArg (· ⋙ b) hu) x)) := by
  simp only [projFillerOfEq, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    CategoryTheory.eqToHom_app, projFiller_hom_app]
  rfl

/-- **A functor into an explicit 2-fibre product is the comparison functor of the square its
projections name.** This is
`CategoryTheory.Limits.CategoricalPullback.squareComparison_proj` with the two legs transported
along given equalities. -/
lemma squareComparison_projOfEq (F : C' ⥤ p ⊡ b) (ha : F ⋙ π₁ p b = a)
    (hu : F ⋙ π₂ p b = u) :
    squareComparison a u p b (projFillerOfEq p b a u F ha hu) = F := by
  subst ha hu
  convert squareComparison_proj p b F using 2
  ext x
  simp [projFillerOfEq]
  rfl

/-- **A square named by the projections of an equivalence into `p ⊡ b` is 2-cartesian.** -/
lemma isEquivalence_squareComparison_projOfEq (F : C' ⥤ p ⊡ b) [F.IsEquivalence]
    (ha : F ⋙ π₁ p b = a) (hu : F ⋙ π₂ p b = u) :
    (squareComparison a u p b (projFillerOfEq p b a u F ha hu)).IsEquivalence := by
  rw [squareComparison_projOfEq p b a u F ha hu]
  infer_instance

section Functoriality

variable {𝒜 ℬ 𝒞 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒞]
  (H : C ⥤ D) (I : D' ⥤ D) (L : C ⥤ 𝒜) (K : D' ⥤ ℬ) (M : D ⥤ 𝒞) (F : 𝒜 ⥤ 𝒞) (G : ℬ ⥤ 𝒞)
  (α : K ⋙ G ≅ I ⋙ M) (β : H ⋙ M ≅ L ⋙ F)

/-- **A change of cospan acts on the first projection by its first component.** -/
lemma map_comp_π₁ :
    map H I L K M F G α β ⋙ π₁ F G = π₁ H I ⋙ L := rfl

/-- **A change of cospan acts on the second projection by its second component.** -/
lemma map_comp_π₂ :
    map H I L K M F G α β ⋙ π₂ F G = π₂ H I ⋙ K := rfl

end Functoriality

end CategoryTheory.Limits.CategoricalPullback

end
