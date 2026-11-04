module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero commutes with the direct image along a finite morphism

Stacks Tag 0GJ1: for a cartesian square
```
U --j'--> X
|g        |f
V --j---> Y
```
with `f` finite and `j` an open immersion, `f_* ∘ j'_! ≅ j_! ∘ g_*` as functors from abelian
sheaves on `U_étale` to abelian sheaves on `Y_étale`. This file proves it on Mathlib's small étale
sites, at the coefficients `AddCommGrpCat.{u + 1}`, with no hypothesis beyond the source's.

## Main results

* `Stacks.EtaleCohomology.isIso_counit_of_isZero_inverseImage`: a sheaf whose inverse image to
  the closed complement of an open `V` vanishes is the extension by zero of its restriction to
  `V`.
* `Stacks.EtaleCohomology.directImageExtensionByZeroIso`: **Tag 0GJ1**, and
  `Stacks.EtaleCohomology.directImageExtensionByZeroIsoOfClosed`, the same through a chosen
  closed complement.

## Implementation notes

The proof is through the characterization of extension by zero. Write `H = f_* j'_! F`. By the
base change of Tag 0959 along the closed complement `i : Z ⟶ Y` of `V`
(`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback`), `i^{-1} H`
is a direct image of the inverse image of `j'_! F` to `Z ×_Y X`, which misses `U` and so
vanishes; hence the counit `j_! j^{-1} H ⟶ H` is invertible (Tag 095L). By the same base change
along `j`, `j^{-1} H ≅ g_* (j')^{-1} j'_! F ≅ g_* F`. Every step is a natural isomorphism, so the
result is an isomorphism of functors. The closed complement is any closed immersion whose image
is the complement of that of `j`; the reduced one always exists.

## References

* [Stacks Project, Tag 0GJ1](https://stacks.math.columbia.edu/tag/0GJ1)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 095L](https://stacks.math.columbia.edu/tag/095L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **A sheaf vanishing on the closed complement of an open is extended by zero from the open.**
For an open immersion `j : V ⟶ Y` and a closed immersion `i : Z ⟶ Y` with complementary images,
the counit `j_! j^{-1} H ⟶ H` is an isomorphism as soon as `i^{-1} H = 0`, by the exact sequence
`0 → j_! j^{-1} H → H → i_* i^{-1} H → 0` of Tag 095L. -/
theorem isIso_counit_of_isZero_inverseImage {Z V Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (j : V ⟶ Y) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : IsZero ((etaleAbelianInverseImage.{u, 0} i).obj H)) :
    IsIso ((extensionByZeroAdj.{u, 0} j).counit.app H) := by
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} i j hij H
  have := hS.mono_f
  have : Epi ((extensionByZeroAdj.{u, 0} j).counit.app H) :=
    hS.exact.epi_f (((etaleAbelianDirectImage.{u, 0} i).map_isZero hH).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

variable {U V X Y : Scheme.{u}} (j' : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion j'] [IsFinite f] (sq : IsPullback j' g f j)
  {Z : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
  (hij : Set.range j.base = (Set.range i.base)ᶜ)

omit [IsOpenImmersion j] [IsClosedImmersion i] in
include sq hij in
/-- The direct image of an extension by zero from `U` has zero inverse image to the closed
complement of `V`. -/
theorem isZero_inverseImage_directImage_extensionByZero
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsZero ((etaleAbelianInverseImage.{u, 0} i).obj
      ((etaleAbelianDirectImage.{u, 0} f).obj ((extensionByZero.{u, 0} j').obj F))) := by
  have P := IsPullback.of_hasPullback f i
  have := isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback f i _ _ P
  refine IsZero.of_iso ?_ ((asIso (etaleAbelianBaseChange.{u, 0} f i _ _ P.w)).app _)
  refine (etaleAbelianDirectImage.{u, 0} _).map_isZero
    (isZero_etaleAbelianInverseImage_extensionByZero_of_disjoint.{u, 0} _ j' ?_ F)
  rw [Set.disjoint_left]
  rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
  have h₁ : f.base ((pullback.fst f i).base z) ∈ Set.range i.base :=
    ⟨(pullback.snd f i).base z, by rw [← Scheme.Hom.comp_apply, ← pullback.condition,
      Scheme.Hom.comp_apply]⟩
  have h₂ : f.base ((pullback.fst f i).base z) ∈ Set.range j.base :=
    ⟨g.base x, by rw [← hx, ← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]⟩
  rw [hij] at h₂
  exact h₂ h₁

include sq hij in
/-- Tag 0GJ1 through a chosen closed complement: for a cartesian square `j' ≫ f = g ≫ j` with
`f` finite and `j` an open immersion, and a closed immersion `i` whose image is the complement of
that of `j`, `f_* ∘ j'_! ≅ j_! ∘ g_*`. -/
def directImageExtensionByZeroIsoOfClosed :
    extensionByZero.{u, 0} j' ⋙ etaleAbelianDirectImage.{u, 0} f ≅
      etaleAbelianDirectImage.{u, 0} g ⋙ extensionByZero.{u, 0} j := by
  have hc : ∀ F, IsIso ((extensionByZeroAdj.{u, 0} j).counit.app
      ((etaleAbelianDirectImage.{u, 0} f).obj ((extensionByZero.{u, 0} j').obj F))) := fun F ↦
    isIso_counit_of_isZero_inverseImage i j hij _
      (isZero_inverseImage_directImage_extensionByZero j' g f j sq i hij F)
  have hc' : IsIso (Functor.whiskerLeft (extensionByZero.{u, 0} j' ⋙
      etaleAbelianDirectImage.{u, 0} f) (extensionByZeroAdj.{u, 0} j).counit) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hc
  have := isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback f j j' g sq
  -- `j^{-1} f_* j'_! ≅ g_* (j')^{-1} j'_! ≅ g_*`
  let e : extensionByZero.{u, 0} j' ⋙ etaleAbelianDirectImage.{u, 0} f ⋙
      etaleRestriction.{u, 0} j ≅ etaleAbelianDirectImage.{u, 0} g :=
    Functor.isoWhiskerLeft (extensionByZero.{u, 0} j' ⋙ etaleAbelianDirectImage.{u, 0} f)
        (etaleAbelianInverseImageRestrictionIso.{u, 0} j).symm ≪≫
      Functor.isoWhiskerLeft (extensionByZero.{u, 0} j')
        (asIso (etaleAbelianBaseChange.{u, 0} f j j' g sq.w)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (extensionByZero.{u, 0} j')
          (etaleAbelianInverseImageRestrictionIso.{u, 0} j') ≪≫
        (asIso (extensionByZeroAdj.{u, 0} j').unit).symm)
        (etaleAbelianDirectImage.{u, 0} g) ≪≫ Functor.leftUnitor _
  exact (asIso (Functor.whiskerLeft (extensionByZero.{u, 0} j' ⋙
      etaleAbelianDirectImage.{u, 0} f) (extensionByZeroAdj.{u, 0} j).counit)).symm ≪≫
    Functor.isoWhiskerRight e (extensionByZero.{u, 0} j)

omit [IsClosedImmersion i] in
include sq in
/-- **Stacks Project, Tag 0GJ1.** For a cartesian square `j' ≫ f = g ≫ j` of schemes with `f`
finite and `j` an open immersion, `f_* ∘ j'_! ≅ j_! ∘ g_*` as functors from abelian sheaves on
`U_étale` to abelian sheaves on `Y_étale`. -/
@[stacks 0GJ1 "at the coefficients AddCommGrpCat.{u+1}, on Mathlib's small etale sites"]
def directImageExtensionByZeroIso :
    extensionByZero.{u, 0} j' ⋙ etaleAbelianDirectImage.{u, 0} f ≅
      etaleAbelianDirectImage.{u, 0} g ⋙ extensionByZero.{u, 0} j :=
  directImageExtensionByZeroIsoOfClosed j' g f j sq
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩).subschemeι
    (by rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]; simp)

end Stacks.EtaleCohomology

end
