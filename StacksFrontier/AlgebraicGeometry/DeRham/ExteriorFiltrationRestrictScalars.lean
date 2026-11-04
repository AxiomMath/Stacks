module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsImageSubobject
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsImage
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerFiltration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The filtration of an exterior power, read over a smaller ring sheaf

Let `ρ : 𝒜 ⟶ 𝒪` be a morphism of sheaves of commutative rings on a space `X` and let
`iF : F ⟶ H` be a morphism of sheaves of `𝒪`-modules. The filtration

`F^k = Im (⋀^k F ⊗_𝒪 ⋀^{n-k} H ⟶ ⋀ⁿ H)`

of `SheafOfModules.exteriorImageFiltration` is built from morphisms out of tensor products over
`𝒪`. Section 50.12 of the Stacks project describes the filtration of the relative de Rham complex
of a morphism of schemes over a base `S` by the forms pulled back from the target, and there the
wedge maps are taken over the *base* ring sheaf `(f ∘ g)^{-1}𝒪_S`, not over `𝒪_X`; the two
descriptions have to be matched before the graded pieces of one can be computed from the other.

**This file matches them.** The lax comparison

`(⋀^k F)|_𝒜 ⊗_𝒜 (⋀^{n-k} H)|_𝒜 ⟶ (⋀^k F ⊗_𝒪 ⋀^{n-k} H)|_𝒜`

is an epimorphism (`Stacks.SheafOfModules.TensorRestrictScalars.epi_laxComparison`), so the
`𝒜`-linear wedge map and the restriction of scalars of the `𝒪`-linear one have the same image.
Transporting a subobject along restriction of scalars
(`Stacks.SheafOfModules.ChangeOfRings.imageSubobject_map_restrictScalars`) therefore carries each
step of the filtration of `⋀ⁿ H` to the image of a wedge map formed over `𝒜`: the two realizations
of the `k`-th step agree on the nose, with no comparison of their sources.

## Main results

* `SheafOfModules.imageSubobject_restrictScalars_prodWedgeHomOfEq`: **the `𝒜`-linear wedge map and
  the restriction of scalars of the `𝒪`-linear one have the same image.**
* `SheafOfModules.mapSubobjects_exteriorImageFiltration`: **the bridge** — the `k`-th step of the
  filtration of `⋀ⁿ H`, transported along restriction of scalars along `ρ`, is the image of the
  wedge map `(⋀^k F)|_𝒜 ⊗_𝒜 (⋀^{n-k} H)|_𝒜 ⟶ (⋀ⁿ H)|_𝒜` formed over `𝒜`.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.TensorRestrictScalars
open PresheafOfModules (ringedSpaceOfSheaf)

universe u

namespace SheafOfModules

variable {X : TopCat.{u}} {Abase Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  (ρ : Abase ⟶ Osharp)
  {F H : SheafOfModules.{u} (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) H)
  (iF : F ⟶ H)

/-! Sheaves of modules over the ring sheaves underlying `𝒪` and `𝒜` form abelian categories,
which is what gives the image subobjects the filtration is built from.  The instance is pinned
rather than restated: finding it at these binders exceeds the default instance-synthesis budget,
and `Stacks.SheafOfModules.abelianOfSmallSite` is that instance, over an arbitrary sheaf of
rings on a small site, with the budget already spent. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite

/-! The modules `F` and `H` are indexed by `CategoryTheory.Sheaf.toRingCat`, while restriction of
scalars along `ρ` and the tensor products over `𝒜` are indexed by
`Stacks.SheafOfModules.Tensor.ringSheaf`. The two are the same bundled sheaf of rings, but
`ringSheaf` is an opaque `def`, so the subobject lattice of `⋀ⁿ H` is not recognised as the one
of the abelian structure just pinned. Making `ringSheaf` reducible for instances identifies the
two spellings. -/
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

/-- **The `𝒜`-linear wedge map and the restriction of scalars of the `𝒪`-linear one have the same
image.** The sources differ — one is a tensor product over `𝒜`, the other the restriction of a
tensor product over `𝒪` — but the lax comparison between them is an epimorphism, and precomposing
with an epimorphism does not change an image. -/
theorem imageSubobject_restrictScalars_prodWedgeHomOfEq (k q n : ℕ) (h : k + q = n) :
    imageSubobject (laxComparison Abase Osharp ρ (AF.exteriorPower k) (A.exteriorPower q) ≫
        (restrictScalarsSheaf Abase Osharp ρ).map
          (prodWedgeHomOfEq AF A A iF (𝟙 H) k q n h)) =
      imageSubobject ((restrictScalarsSheaf Abase Osharp ρ).map
        (prodWedgeHomOfEq AF A A iF (𝟙 H) k q n h)) :=
  imageSubobject_laxComparison_comp_map Abase Osharp ρ (AF.exteriorPower k) (A.exteriorPower q) _

/-- **The two realizations of the `k`-th step of the filtration of `⋀ⁿ H` agree.** The step
`SheafOfModules.exteriorImageFiltration`, a subobject of `⋀ⁿ H` cut out by the image of a wedge
map formed over `𝒪`, is carried by restriction of scalars along `ρ` to the image of the wedge map
formed over `𝒜`, out of `(⋀^k F)|_𝒜 ⊗_𝒜 (⋀^{n-k} H)|_𝒜`.

This is the comparison [Stacks, Section 0FMK] needs between the filtration of the single sheaf
`Ω^n_{X/S}` and the step in degree `n` of the filtration of the complex `Ω^•_{X/S}`, whose wedge
maps are formed over `(f ∘ g)^{-1}𝒪_S`. -/
theorem mapSubobjects_exteriorImageFiltration (n k : ℕ) (hk : k ≤ n) :
    (mapSubobjects (restrictScalarsSheaf Abase Osharp ρ) (A.exteriorPower n)).obj
        (exteriorImageFiltration AF A iF n k) =
      imageSubobject (laxComparison Abase Osharp ρ (AF.exteriorPower k)
            (A.exteriorPower (n - k)) ≫
          (restrictScalarsSheaf Abase Osharp ρ).map
            (prodWedgeHomOfEq AF A A iF (𝟙 H) k (n - k) n (Nat.add_sub_cancel' hk))) := by
  rw [exteriorImageFiltration_of_le AF A iF n k hk,
    imageSubobject_restrictScalars_prodWedgeHomOfEq ρ AF A iF k (n - k) n
      (Nat.add_sub_cancel' hk)]
  exact (Stacks.SheafOfModules.ChangeOfRings.imageSubobject_map_restrictScalars
    (sheafRingMap Abase Osharp ρ)
    (prodWedgeHomOfEq AF A A iF (𝟙 H) k (n - k) n (Nat.add_sub_cancel' hk))).symm

end SheafOfModules

end
