module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The direct sum of a family of abelian groups is its coproduct

The external direct sum `⨁ i, A i` of a family of abelian groups, together with the inclusions of
the summands, is a coproduct of the family in the category of abelian groups, and the resulting
identification `⨁ i, A i ≅ ∐ A` is natural in the family.

## Main definitions

* `AddCommGrpCat.directSumCofan` — the cofan of a family of abelian groups given by the
  inclusions into the direct sum.
* `AddCommGrpCat.directSumCofanIsColimit` — that cofan is a coproduct.
* `AddCommGrpCat.directSumCoproductIso` — the direct sum, identified with the coproduct.

## Main results

* `AddCommGrpCat.inj_directSumCoproductIso_hom` — the identification carries the inclusion of a
  summand to the inclusion of a factor of the coproduct.
* `AddCommGrpCat.directSumCoproductIso_natural` — the identification is natural in the family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped DirectSum

universe w t

namespace AddCommGrpCat

variable {ι : Type w} (A A' : ι → AddCommGrpCat.{max w t})

/-- The cofan of a family of abelian groups given by the inclusions into their direct sum. -/
public def directSumCofan : Cofan A := by
  classical
  exact Cofan.mk (AddCommGrpCat.of (⨁ i : ι, (A i : Type _)))
    (fun i => AddCommGrpCat.ofHom (DirectSum.of (fun i => (A i : Type _)) i))

/-- The direct sum of a family of abelian groups is their coproduct: a map out of it is uniquely
determined by its restrictions to the summands. -/
@[sga "4 I 2.3.2" "special case"]
public def directSumCofanIsColimit : IsColimit (directSumCofan A) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun c => AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun i => (c.inj i).hom)) ?_ ?_
  · intro c i
    ext x
    exact DirectSum.toAddMonoid_of (fun i => (c.inj i).hom) i x
  · intro c m hm
    ext x
    have h : m.hom =
        (DirectSum.toAddMonoid (fun i => (c.inj i).hom) :
          (⨁ i : ι, (A i : Type _)) →+ c.pt) := by
      refine DirectSum.addHom_ext fun i y => ?_
      have hi := DFunLike.congr_fun (congrArg AddCommGrpCat.Hom.hom (hm i)) y
      change m.hom ((DirectSum.of (fun i => (A i : Type _)) i) y) = (c.inj i).hom y at hi
      rw [DirectSum.toAddMonoid_of]
      exact hi
    exact DFunLike.congr_fun h x

/-- The direct sum of a family of abelian groups, identified with its coproduct. -/
public def directSumCoproductIso :
    AddCommGrpCat.of (⨁ i : ι, (A i : Type _)) ≅ ∐ A :=
  IsColimit.coconePointUniqueUpToIso (directSumCofanIsColimit A) (coproductIsCoproduct A)

/-- The identification of a direct sum with the coproduct carries the inclusion of a summand to
the inclusion of a factor of the coproduct. -/
public theorem inj_directSumCoproductIso_hom (i : ι) :
    (directSumCofan A).inj i ≫ (directSumCoproductIso A).hom = Sigma.ι A i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (directSumCofanIsColimit A) (coproductIsCoproduct A) ⟨i⟩

/-- The identification of a direct sum with the coproduct is natural in the family: the direct sum
of a family of homomorphisms becomes the coproduct of those homomorphisms. -/
public theorem directSumCoproductIso_natural (g : ∀ i, A i ⟶ A' i) :
    AddCommGrpCat.ofHom (DirectSum.map fun i => (g i).hom) ≫ (directSumCoproductIso A').hom =
      (directSumCoproductIso A).hom ≫ Limits.Sigma.map g := by
  classical
  refine (directSumCofanIsColimit A).hom_ext fun j => ?_
  obtain ⟨i⟩ := j
  have hmap : (directSumCofan A).inj i ≫
      AddCommGrpCat.ofHom (DirectSum.map fun j => (g j).hom) =
      g i ≫ (directSumCofan A').inj i := by
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_)
    exact DirectSum.map_of (fun j => (g j).hom) i x
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (directSumCoproductIso A').hom) hmap).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => g i ≫ z) (inj_directSumCoproductIso_hom A' i)).trans
          ((Sigma.ι_map (fun i => g i) i).symm.trans
            ((congrArg (fun z => z ≫ Limits.Sigma.map g)
                (inj_directSumCoproductIso_hom A i)).symm.trans
              (Category.assoc _ _ _))))))

end AddCommGrpCat

end
