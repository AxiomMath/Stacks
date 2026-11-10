module

public import Mathlib.CategoryTheory.Limits.Constructions.Filtered

/-!
# Arbitrary coproducts as colimits of their finite subcoproducts

In a category with finite coproducts, a coproduct indexed by an arbitrary type is the filtered
colimit, over the finite subsets of the index set, of the subcoproducts they span. Mathlib's
`CategoryTheory.Limits.CoproductsFromFiniteFiltered.liftToFinsetColimitCocone` constructs the
resulting colimit cocone assuming that *every* diagram indexed by `Finset (Discrete J)` has a
colimit. This file gives the same cocone assuming only that the single diagram
`CoproductsFromFiniteFiltered.liftToFinsetObj F` has one, which is what is available when the
coproduct is produced by a functor that need not land in a cocomplete category.

## Main definitions

* `CategoryTheory.Limits.finiteSubsetCoproductCocone`: the colimit cocone on a discrete diagram
  whose cocone point is the colimit of the finite subcoproducts.

## Implementation notes

`(CoproductsFromFiniteFiltered.liftToFinsetObj F).obj S` and
`∐ fun x : S => F.obj x.val` agree only after unfolding the construction of colimits, which the
elaborator will not do while rewriting. The two helper lemmas `ιmap_liftToFinsetObj` and
`ι_colimit_ι_liftToFinsetObj` state the identities that are needed as equations between
morphisms, which is what lets the proofs below proceed by `congrArg` and `calc` rather than by
relaxing the transparency settings.

## References

* [Stacks Project, Tag 0GNK](https://stacks.math.columbia.edu/tag/0GNK)
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Limits.CoproductsFromFiniteFiltered

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] {J : Type w}

/-- The transition map of `liftToFinsetObj F` sends the summand at `y` to the summand at `y`. -/
public lemma ιmap_liftToFinsetObj (F : Discrete J ⥤ C)
    {S T : Finset (Discrete J)} (h : S ⟶ T) (y : S) :
    Sigma.ι (fun x : S => F.obj x.val) y ≫ (liftToFinsetObj F).map h =
      Sigma.ι (fun x : T => F.obj x.val) ⟨y.val, h.down.down y.2⟩ :=
  Eq.trans
    (congrArg
      (fun z : (liftToFinsetObj F).obj S ⟶ (liftToFinsetObj F).obj T =>
        Sigma.ι (fun x : S => F.obj x.val) y ≫ z)
      (liftToFinsetObj_map F h))
    (Sigma.ι_comp_desc _ _)

/-- The leg of the colimit of `liftToFinsetObj F` at the summand indexed by `j` does not depend
on which finite subset containing `j` it is computed in. -/
public lemma ι_colimit_ι_liftToFinsetObj (F : Discrete J ⥤ C)
    [HasColimit (liftToFinsetObj F)] {t : Finset (Discrete J)} {j : Discrete J} (hj : j ∈ t) :
    Sigma.ι (fun x : ({j} : Finset (Discrete J)) => F.obj x.val)
        ⟨j, Finset.mem_singleton_self j⟩ ≫ colimit.ι (liftToFinsetObj F) {j} =
      Sigma.ι (fun x : t => F.obj x.val) ⟨j, hj⟩ ≫ colimit.ι (liftToFinsetObj F) t := by
  have h' : ({j} : Finset (Discrete J)) ⟶ t := homOfLE (Finset.singleton_subset_iff.2 hj)
  exact ((congrArg _ (colimit.w (liftToFinsetObj F) h').symm).trans
      (Category.assoc _ _ _).symm).trans
    (congrArg (· ≫ colimit.ι (liftToFinsetObj F) t)
      (ιmap_liftToFinsetObj F h' ⟨j, Finset.mem_singleton_self j⟩))

/-- A cocone on a discrete diagram `F` induces a cocone on the diagram of finite
subcoproducts of `F`. -/
public noncomputable def finiteSubcoproductsDescCocone (F : Discrete J ⥤ C) (s : Cocone F) :
    Cocone (liftToFinsetObj F) where
  pt := s.pt
  ι :=
    { app := fun S => Sigma.desc fun x : S => s.ι.app x.val
      naturality := by
        intro S T h
        apply Sigma.hom_ext
        intro y
        calc Sigma.ι (fun x : S => F.obj x.val) y ≫
              ((liftToFinsetObj F).map h ≫ Sigma.desc fun x : T => s.ι.app x.val)
            = (Sigma.ι (fun x : S => F.obj x.val) y ≫ (liftToFinsetObj F).map h) ≫
                (Sigma.desc fun x : T => s.ι.app x.val) := (Category.assoc _ _ _).symm
          _ = Sigma.ι (fun x : T => F.obj x.val) ⟨y.val, h.down.down y.2⟩ ≫
                (Sigma.desc fun x : T => s.ι.app x.val) :=
              congrArg (fun z => z ≫ (Sigma.desc fun x : T => s.ι.app x.val))
                (ιmap_liftToFinsetObj F h y)
          _ = s.ι.app y.val :=
              Sigma.ι_comp_desc (f := fun x : T => F.obj x.val)
                (fun x : T => s.ι.app x.val) ⟨y.val, h.down.down y.2⟩
          _ = Sigma.ι (fun x : S => F.obj x.val) y ≫
                (Sigma.desc fun x : S => s.ι.app x.val) :=
              (Sigma.ι_comp_desc (f := fun x : S => F.obj x.val)
                (fun x : S => s.ι.app x.val) y).symm
          _ = Sigma.ι (fun x : S => F.obj x.val) y ≫
                ((Sigma.desc fun x : S => s.ι.app x.val) ≫
                  ((Functor.const (Finset (Discrete J))).obj s.pt).map h) := by simp }

/-- Descending along `finiteSubcoproductsDescCocone` recovers the leg of the original cocone. -/
public lemma ι_colimit_desc_finiteSubcoproductsDescCocone (F : Discrete J ⥤ C)
    [HasColimit (liftToFinsetObj F)] (s : Cocone F)
    {t : Finset (Discrete J)} {j : Discrete J} (hj : j ∈ t) :
    Sigma.ι (fun x : t => F.obj x.val) ⟨j, hj⟩ ≫
        (colimit.ι (liftToFinsetObj F) t ≫
          colimit.desc (liftToFinsetObj F) (finiteSubcoproductsDescCocone F s)) = s.ι.app j :=
  Eq.trans
    (congrArg
      (fun z : (liftToFinsetObj F).obj t ⟶ s.pt =>
        Sigma.ι (fun x : t => F.obj x.val) ⟨j, hj⟩ ≫ z)
      (colimit.ι_desc (finiteSubcoproductsDescCocone F s) t))
    (Sigma.ι_comp_desc (f := fun x : t => F.obj x.val) (fun x : t => s.ι.app x.val) ⟨j, hj⟩)

/-- The cocone on a discrete diagram whose point is the colimit of the finite subcoproducts. -/
public noncomputable def finiteSubsetCoconeOfColimit (F : Discrete J ⥤ C)
    [HasColimit (liftToFinsetObj F)] : Cocone F where
  pt := colimit (liftToFinsetObj F)
  ι := Discrete.natTrans fun j =>
    Sigma.ι (fun x : ({j} : Finset (Discrete J)) => F.obj x.val)
        ⟨j, Finset.mem_singleton_self j⟩ ≫ colimit.ι (liftToFinsetObj F) {j}

/-- `finiteSubsetCoconeOfColimit` is a colimit cocone. -/
public noncomputable def isColimitFiniteSubsetCoconeOfColimit (F : Discrete J ⥤ C)
    [HasColimit (liftToFinsetObj F)] : IsColimit (finiteSubsetCoconeOfColimit F) where
  desc := fun s => colimit.desc (liftToFinsetObj F) (finiteSubcoproductsDescCocone F s)
  fac := by
    intro s j
    exact Eq.trans (Category.assoc _ _ _)
      (ι_colimit_desc_finiteSubcoproductsDescCocone F s (Finset.mem_singleton_self j))
  uniq := by
    intro s m hm
    refine colimit.hom_ext (F := liftToFinsetObj F) (f := m)
      (f' := colimit.desc (liftToFinsetObj F) (finiteSubcoproductsDescCocone F s)) ?_
    intro t
    refine Sigma.hom_ext (f := fun x : t => F.obj x.val)
      (colimit.ι (liftToFinsetObj F) t ≫ m)
      (colimit.ι (liftToFinsetObj F) t ≫
        colimit.desc (liftToFinsetObj F) (finiteSubcoproductsDescCocone F s)) ?_
    rintro ⟨j, hj⟩
    have e1 : Sigma.ι (fun x : t => F.obj x.val) ⟨j, hj⟩ ≫
          (colimit.ι (liftToFinsetObj F) t ≫ m) =
        (Sigma.ι (fun x : t => F.obj x.val) ⟨j, hj⟩ ≫
          colimit.ι (liftToFinsetObj F) t) ≫ m := (Category.assoc _ _ _).symm
    have e2 : (Sigma.ι (fun x : t => F.obj x.val) ⟨j, hj⟩ ≫
          colimit.ι (liftToFinsetObj F) t) ≫ m =
        (Sigma.ι (fun x : ({j} : Finset (Discrete J)) => F.obj x.val)
          ⟨j, Finset.mem_singleton_self j⟩ ≫ colimit.ι (liftToFinsetObj F) {j}) ≫ m :=
      congrArg (fun z => z ≫ m) (ι_colimit_ι_liftToFinsetObj F hj).symm
    have e3 : (Sigma.ι (fun x : ({j} : Finset (Discrete J)) => F.obj x.val)
          ⟨j, Finset.mem_singleton_self j⟩ ≫ colimit.ι (liftToFinsetObj F) {j}) ≫ m =
        s.ι.app j := hm j
    exact ((e1.trans e2).trans e3).trans
      (ι_colimit_desc_finiteSubcoproductsDescCocone F s hj).symm

/-- The coproduct of a family indexed by an arbitrary type, realized as the colimit over the
finite subsets of the index set of the coproducts they span. -/
public noncomputable def finiteSubsetCoproductCocone (F : Discrete J ⥤ C)
    [HasColimit (liftToFinsetObj F)] : ColimitCocone F :=
  ⟨finiteSubsetCoconeOfColimit F, isColimitFiniteSubsetCoconeOfColimit F⟩

end CategoryTheory.Limits
