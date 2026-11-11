module

public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatDimensionFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericRankCoproduct

/-!
# Stacks 05UE: the flat-dimension functor is the coproduct of the generic-rank functors

Let `f : X ⟶ S` be a smooth morphism of affine schemes with geometrically irreducible fibres of
dimension `d` and let `F` be a quasi-coherent `𝒪_X`-module of finite presentation. Stacks 05UE
asserts `F_d = ∐_{p = 0, …, c} H_p` for some `c ≥ 0`.

`FreeAtGenericPointsSituation.flatDimensionFunctor_iso_coproduct_freeAtGenericPointsFunctor`
proves this with `F_d` sheafified. This file removes the sheafification: `F_d` is an fpqc
sheaf by Stacks 05MV, hence a Zariski sheaf, so it is isomorphic to its own sheafification.

## Main results

* `FreeAtGenericPointsSituation.exists_isSheaf_flatDimensionFunctor_and_iso_coproduct`:
  **Stacks 05UE**.

## References

* [Stacks Project, Tag 05UE](https://stacks.math.columbia.edu/tag/05UE)
* [Stacks Project, Tag 05MV](https://stacks.math.columbia.edu/tag/05MV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace FreeAtGenericPointsSituation

attribute [local instance] sheafHasColimits

variable (D : FreeAtGenericPointsSituation.{u})

/-- **Stacks Project, Tag 05UE.** Let `f : X ⟶ S` be a smooth morphism of affine schemes with
geometrically irreducible fibres of dimension `d` and let `F` be a quasi-coherent `𝒪_X`-module
of finite presentation. Then there is a `c ≥ 0` with
```
F_d = ∐_{p = 0, …, c} H_p
```
where `F_d` is the functor of flatness in dimensions `≥ d` of Stacks 05MT and (05MU) and `H_p`
is the functor of Stacks 05MP, as functors on schemes over `S`.

The functor `F_d` itself (lifted to `Type (u + 1)`) is a Zariski sheaf, by the fpqc sheaf
property of Stacks 05MV, and as a sheaf it is isomorphic to the coproduct, in Zariski sheaves
over `S`, of the `H_p` for `p ≤ c`. The coproduct is the one of sheaves: the pointwise disjoint
union of the subterminal presheaves `H_p` is not a sheaf (it has `c + 1` elements over `∅`, and
misses the sections over a disconnected `T` with different generic ranks on its pieces), and
its sheafification is the coproduct of sheaves. -/
@[stacks 05UE]
theorem exists_isSheaf_flatDimensionFunctor_and_iso_coproduct [IsAffine D.X] [IsAffine D.S]
    [D.F.IsFinitePresentation] {d : ℕ} (hd : RelativeDimension D.f d) :
    ∃ (c : ℕ) (h : Presheaf.IsSheaf (Scheme.zariskiTopology.over D.S)
        ((D.toFlatDimensionSituation d).flatDimensionFunctor ⋙ uliftFunctor.{u + 1})),
      Nonempty ((⟨_, h⟩ : Sheaf (Scheme.zariskiTopology.over D.S) (Type (u + 1))) ≅
        ∐ fun p : Fin (c + 1) ↦
          (presheafToSheaf (Scheme.zariskiTopology.over D.S) (Type (u + 1))).obj
            (D.freeAtGenericPointsFunctor p.val ⋙ uliftFunctor.{u + 1})) := by
  have hfpqc := (D.toFlatDimensionSituation d).flatDimensionFunctor_isSheaf_fpqc
  have hzar : Presheaf.IsSheaf (Scheme.zariskiTopology.over D.S)
      (D.toFlatDimensionSituation d).flatDimensionFunctor :=
    hfpqc.of_le (fun _ _ hR ↦ Scheme.zariskiTopology_le_fpqcTopology _ hR)
  have h : Presheaf.IsSheaf (Scheme.zariskiTopology.over D.S)
      ((D.toFlatDimensionSituation d).flatDimensionFunctor ⋙ uliftFunctor.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).2
      (Presieve.isSheaf_comp_uliftFunctor _ ((isSheaf_iff_isSheaf_of_type _ _).1 hzar))
  obtain ⟨c, ⟨e⟩⟩ := D.flatDimensionFunctor_iso_coproduct_freeAtGenericPointsFunctor hd
  exact ⟨c, h, ⟨sheafificationIso ⟨_, h⟩ ≪≫ e⟩⟩

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
