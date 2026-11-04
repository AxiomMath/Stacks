module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.SetTheory.Cardinal.Order

/-!
# The size of an object of an abelian category

The size `|M|` of an object `M` of an abelian category is the cardinality of the set of
subobjects of `M`. For a short exact sequence `0 → M' → M → M'' → 0` in a Grothendieck abelian
category, `|M'| ≤ |M|` and `|M''| ≤ |M|`.

## Main definitions

* `Stacks.Injectives.Size.size`: the cardinality of `Subobject M`.

## Main results

* `Stacks.Injectives.Size.exists_pullback_of_epi`: for an epimorphism `g`, the image along `g`
  of the pullback along `g` of a subobject `b` is `b`.
* `Stacks.Injectives.Size.size_X₁_le_size_X₂`: `|M'| ≤ |M|`.
* `Stacks.Injectives.Size.size_X₃_le_size_X₂`: `|M''| ≤ |M|`.

## References

* [Stacks Project, Tag 079C](https://stacks.math.columbia.edu/tag/079C)
* [Stacks Project, Tag 079D](https://stacks.math.columbia.edu/tag/079D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Injectives.Size

/-- The *size* of an object `M` of an abelian category: the cardinality of the set of
subobjects of `M`. -/
@[stacks 079C]
noncomputable def size {C : Type*} [Category C] [Abelian C] (M : C) : Cardinal :=
  Cardinal.mk (Subobject M)

/-- For a short exact sequence `0 → M' → M → M'' → 0` in a Grothendieck abelian
category, the size of `M'` is at most the size of `M`: there is an injection from the
subobjects of `M'` into the subobjects of `M`, hence `|M'| ≤ |M|`. -/
@[stacks 079D]
theorem size_X₁_le_size_X₂ {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    size S.X₁ ≤ size S.X₂ := by
  have : Mono S.f := hS.mono_f
  exact Cardinal.mk_le_of_injective (Subobject.map_obj_injective S.f)

/-- For an epimorphism `g`, the pullback of subobjects is recovered by `exists`:
`exists g (pullback g b) = b`. -/
theorem exists_pullback_of_epi {C : Type*} [Category C] [Abelian C]
    {X Y : C} (g : X ⟶ Y) [Epi g] (b : Subobject Y) :
    (Subobject.exists g).obj ((Subobject.pullback g).obj b) = b := by
  refine le_antisymm ((Subobject.existsPullbackAdj g).gc.l_u_le b) ?_
  set x := (Subobject.pullback g).obj b
  have hpb := Subobject.isPullback g b
  have : Epi (Subobject.pullbackπ g b) := Abelian.epi_fst_of_isLimit b.arrow g hpb.isLimit
  have hm := Subobject.imageFactorisation_F_m g x
  set F := (Subobject.imageFactorisation g x).F
  have : Mono F.m := F.m_mono
  have h₀ : kernel.ι (Subobject.pullbackπ g b) ≫ F.e = 0 := by
    rw [← cancel_mono F.m, zero_comp, Category.assoc, F.fac, ← hpb.w, kernel.condition_assoc,
      zero_comp]
  set q := Abelian.epiDesc (Subobject.pullbackπ g b) F.e h₀
  have hqe : Subobject.pullbackπ g b ≫ q = F.e := Abelian.comp_epiDesc _ _ _
  refine Subobject.le_of_comm q ((cancel_epi (Subobject.pullbackπ g b)).mp ?_)
  rw [← hm]
  exact ((reassoc_of% hqe) F.m).trans (F.fac.trans hpb.w.symm)

example {C : Type*} [Category C] [Abelian C] {A B X : C} (e : A ⟶ B) [Epi e] (m : B ⟶ X) [Mono m] :
    Subobject.mk (Limits.image.ι (e ≫ m)) = Subobject.mk m := by
  have : StrongEpi e := strongEpi_of_epi e
  refine (Subobject.mk_eq_mk_of_comm _ _ (Limits.image.isoStrongEpiMono e m rfl).symm ?_)
  rw [Iso.symm_hom]
  simp

/-- For a short exact sequence `0 → M' → M → M'' → 0`, the size of `M''` is at most the
size of `M`: there is an injection from the subobjects of `M''` into the subobjects of
`M`, hence `|M''| ≤ |M|`. -/
@[stacks 079D]
theorem size_X₃_le_size_X₂ {C : Type*} [Category C] [Abelian C] [IsGrothendieckAbelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    size S.X₃ ≤ size S.X₂ := by
  have : Epi S.g := hS.epi_g
  exact Cardinal.mk_le_of_injective (f := (Subobject.pullback S.g).obj) fun b₁ b₂ h => by
    rw [← exists_pullback_of_epi S.g b₁, h, exists_pullback_of_epi]

end Stacks.Injectives.Size
