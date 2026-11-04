module

public import Mathlib.Algebra.Category.Grp.LargeColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Recognising a filtered colimit of abelian groups elementwise

A cocone over a filtered diagram of abelian groups is colimiting as soon as two element-level
conditions hold: its components are **jointly surjective**, and two elements of one stage with the
same image in the vertex **already agree at a later stage**. No size hypothesis is needed, and the
diagram is not required to have a colimit.

## Main results

* `AddCommGrpCat.isColimit_of_jointlySurjective_of_separated`: the criterion.

## Implementation notes

The route is the one of `Stacks.QuasiCompactColimit.isColimitOfJointlySurjective`, which is this
statement for `CommRingCat`: `CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'` gives the
cocone of underlying sets, and the descended map is given additivity by hand, using that any two
elements of the vertex come from one stage. It is deliberately *not* reflection along the
forgetful functor. `CategoryTheory.Limits.reflectsColimit_of_reflectsIsomorphisms` — the engine of
`Stacks.Cohomology.AbelianSpectral.isColimit_of_bijective_desc` — needs the diagram to have a
colimit, and that statement is therefore pinned to an index category and coefficients in the
*same* universe. The index categories this is wanted for are slice categories `(Over i)ᵒᵖ` of the
index of an inverse system of sites, whose universe is that of the system's index and not that of
the coefficients, so the reflection route is unavailable exactly where it is needed.

`AddCommGrpCat.isColimit_of_isDirectedColimitOfTypes` is the same fact for an index category that
is a *directed preorder*, with the two conditions packaged as `IsDirectedColimitOfTypes`. It is
not a substitute: a slice category is a category and not a preorder. The statement below has it as
a special case, and re-proving it from this one is a follow-up that belongs to the file that owns
it.

## References

* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace AddCommGrpCat

variable {K : Type u} [Category.{v} K] [IsFiltered K] {F : K ⥤ AddCommGrpCat.{w}} (c : Cocone F)
  (hsurj : ∀ x : c.pt, ∃ (k : K) (y : F.obj k), c.ι.app k y = x)
  (hsep : ∀ (k : K) (x y : F.obj k), c.ι.app k x = c.ι.app k y →
    ∃ (l : K) (f : k ⟶ l), F.map f x = F.map f y)

include hsurj hsep in
/-- **Recognising a filtered colimit of abelian groups elementwise.** A cocone over a filtered
diagram of abelian groups is colimiting as soon as its components are jointly surjective (`hsurj`)
and two elements of one stage with the same image in the vertex agree at a later stage (`hsep`).

Neither condition mentions a colimit of the diagram, and the index category and the coefficients
are in unrelated universes; see the module documentation for why that matters and for the two
library statements this one is the common generalisation of. -/
def isColimit_of_jointlySurjective_of_separated : IsColimit c := by
  classical
  let ht : IsColimit ((forget AddCommGrpCat.{w}).mapCocone c) :=
    Types.FilteredColimit.isColimitOf' _ _
      (fun x => by obtain ⟨k, y, hy⟩ := hsurj x; exact ⟨k, y, hy.symm⟩)
      fun k x y h => hsep k x y h
  let d (s : Cocone F) : c.pt → s.pt := ht.desc ((forget AddCommGrpCat.{w}).mapCocone s)
  have hd (s : Cocone F) (k : K) (x : F.obj k) : d s (c.ι.app k x) = s.ι.app k x :=
    ConcreteCategory.congr_hom (ht.fac ((forget AddCommGrpCat.{w}).mapCocone s) k) x
  let dm (s : Cocone F) : c.pt →+ s.pt :=
    { toFun := d s
      map_zero' := by
        obtain ⟨k⟩ := IsFiltered.nonempty (C := K)
        simpa only [map_zero] using hd s k 0
      map_add' := fun x y => by
        obtain ⟨k, a, rfl⟩ := hsurj x
        obtain ⟨l, b, rfl⟩ := hsurj y
        have ha : c.ι.app (IsFiltered.max k l) (F.map (IsFiltered.leftToMax k l) a) =
            c.ι.app k a := by
          rw [← ConcreteCategory.comp_apply, c.w (IsFiltered.leftToMax k l)]
        have hb : c.ι.app (IsFiltered.max k l) (F.map (IsFiltered.rightToMax k l) b) =
            c.ι.app l b := by
          rw [← ConcreteCategory.comp_apply, c.w (IsFiltered.rightToMax k l)]
        rw [← ha, ← hb, ← map_add, hd, hd, hd, map_add] }
  refine { desc := fun s => AddCommGrpCat.ofHom (dm s), fac := ?_, uniq := ?_ }
  · intro s k
    ext x
    exact hd s k x
  · intro s m hm
    ext x
    obtain ⟨k, a, rfl⟩ := hsurj x
    exact (ConcreteCategory.congr_hom (hm k) a).trans (hd s k a).symm

end AddCommGrpCat

end
