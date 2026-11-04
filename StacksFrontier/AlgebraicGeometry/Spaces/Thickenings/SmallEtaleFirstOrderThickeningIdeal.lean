module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.Deformation.ToposThickening.RelativeBaseIdeal

/-!
# The ideal of a first order thickening of algebraic spaces, on the small étale site

Let `i : Z ⟶ Z'` be a morphism of algebraic spaces identifying `Z` with its range, a first order
thickening of `Z'`. The morphism of small étale ringed topoi of `i` is a first order thickening
of ringed topoi (`AlgebraicGeometry.Space.smallEtaleRingedToposHomFirstOrderThickening`). This
file identifies its square-zero ideal with the defining ideal sheaf of the range: a local section
of `𝒪_{Z'}` is killed by the structure map of `i` exactly when it lies in the defining ideal. In
particular the ideal is quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.fSharp_eq_zero_iff_mem_definingIdealAt`: the kernel of the structure
  map of a thickening is the defining ideal of its range.
* `AlgebraicGeometry.Space.smallEtaleThickeningIdealIso`: the square-zero ideal is the defining
  ideal sheaf of the range.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleThickeningIdeal`: it is
  quasi-coherent.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The kernel of the structure map of a thickening of algebraic spaces is the defining ideal
of its range.** -/
theorem fSharp_eq_zero_iff_mem_definingIdealAt {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z')
    (hi : IsThickeningHom B S hS i) (U : (SmallEtale B S hS Z'.1)ᵒᵖ)
    (x : (smallEtaleRingedTopos B S hS Z').O.obj.obj U) :
    (smallEtaleRingedToposHom B S hS i).fSharp.hom.app U x = 0 ↔
      x ∈ definingIdealAt B S hS Z' ⟨Subfunctor.range i.hom, hi.2.1⟩ U := by
  have key : (smallEtaleRingedToposHom B S hS (IsThickening.inclusion B S hS hi.2)).fSharp.hom.app
      U x = 0 ↔ x ∈ definingIdealAt B S hS Z' ⟨Subfunctor.range i.hom, hi.2.1⟩ U :=
    Iff.of_eq (congrArg (fun f ↦ (f.hom.app U).hom x = 0)
      (map_structureSharpCommRing B S hS (IsThickening.inclusion B S hS hi.2)))
  refine ⟨fun hx => key.1 ?_, fun hx => ?_⟩
  · have hψφ : (ObjectProperty.homMk (@inv _ _ _ _ (Subfunctor.toRange i.hom) hi.1) :
          IsThickening.space B S hS hi.2 ⟶ Z) ≫
        (ObjectProperty.homMk (Subfunctor.toRange i.hom) : Z ⟶ IsThickening.space B S hS hi.2) =
          𝟙 _ := by
      ext1
      exact @IsIso.inv_hom_id _ _ _ _ _ hi.1
    exact fSharp_app_eq_zero_of_comp B S hS _ (IsThickening.inclusion B S hS hi.2)
      (exists_retraction_fSharp B S hS _ _ hψφ) i (homMk_toRange_comp_inclusion B S hS i hi) U x hx
  · have h0 := key.2 hx
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f ↦ f.hom)
      (fSharp_comp_compRingIso B S hS
        (ObjectProperty.homMk (Subfunctor.toRange i.hom) : Z ⟶ IsThickening.space B S hS hi.2)
        (IsThickening.inclusion B S hS hi.2) (𝟙 _))) U) x
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, CommRingCat.hom_comp,
      RingHom.comp_apply, h0, map_zero, Category.comp_id] at h
    rw [← homMk_toRange_comp_inclusion B S hS i hi]
    exact h.symm

variable {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z') (hiso : IsIso (Subfunctor.toRange i.hom))
  (hfo : IsFirstOrderThickening B S hS Z' (Subfunctor.range i.hom))

/-- **The square-zero ideal of a first order thickening of algebraic spaces is the defining ideal
sheaf of its range.** Both are submodules of `𝒪_{Z'}` whose sections are those killed by the
structure map of `i`. -/
noncomputable def smallEtaleThickeningIdealIso :
    (smallEtaleRingedToposHomFirstOrderThickening B S hS i hiso hfo).idealOfThickening.I ≅
      (definingIdealSheaf B S hS Z' ⟨Subfunctor.range i.hom, hfo.1.1⟩).toSheafOfModules :=
  Deformation.ToposThickening.sectionwiseIsoOfRangeEq
    (smallEtaleRingedToposHomFirstOrderThickening B S hS i hiso hfo).idealOfThickening.incl
    (definingIdealSheaf B S hS Z' ⟨Subfunctor.range i.hom, hfo.1.1⟩).ι
    (smallEtaleRingedToposHomFirstOrderThickening B S hS i hiso hfo).idealOfThickening.injective
    (fun _ => Subtype.val_injective)
    (fun U x =>
      ((smallEtaleRingedToposHomFirstOrderThickening B S hS i hiso hfo).idealOfThickening.kernel
        U x).symm.trans ((fSharp_eq_zero_iff_mem_definingIdealAt B S hS i ⟨hiso, hfo.1⟩ U x).trans
      ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.2⟩))

/-- **The square-zero ideal of a first order thickening of algebraic spaces is quasi-coherent**
on the small étale site, being the defining ideal sheaf of the range (Stacks 03MB). -/
theorem isQuasicoherentOnSite_smallEtaleThickeningIdeal :
    (smallEtaleRingedToposHomFirstOrderThickening B S hS i hiso hfo).idealOfThickening.I
      |>.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (smallEtaleThickeningIdealIso B S hS i hiso hfo).symm
    (isQuasicoherentOnSite_definingIdealSheaf B S hS Z' _)

end AlgebraicGeometry.Space

end
