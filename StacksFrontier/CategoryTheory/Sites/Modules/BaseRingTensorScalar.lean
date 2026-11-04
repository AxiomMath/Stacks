module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRightScalar
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear
public import StacksFrontier.CategoryTheory.Sites.Modules.BaseRingTensorInverseLimit

/-!
# `𝒪_X ⊗_R -` carries multiplication by a scalar to multiplication by its image

For a base ring `R` of a sheaf of commutative rings `O`, given by `φ : R →+* Γ(C, O)`, the functor
`M ↦ 𝒪_X ⊗_R M` (`Stacks.Cohomology.SiteModules.baseRingTensorFunctor`) carries multiplication by
`c ∈ R` on `M` to multiplication by the global section `φ(c)` on `𝒪_X ⊗_R M`. This is read off the
mapping property of `𝒪_X ⊗_R -` (Stacks 01BH for a base ring): its right adjoint, global sections
read as `R`-modules through `φ`, carries multiplication by `φ(c)` to multiplication by `c`
(`CategoryTheory.Adjunction.map_endOfId`). In the proof of [Stacks Project, Tag 0D1K] this
identifies the action of `k` on `Ext¹(NL_{X/k}, 𝒪_X ⊗_k k)` through `k ⊗ -` with its action
through the structure morphism `X ⟶ Spec k`.

## Main definitions

* `Stacks.Cohomology.SiteModules.smulEndId`: multiplication by `c` on `R`-modules, as an
  endomorphism of the identity functor.

## Main results

* `Stacks.Cohomology.SiteModules.baseRingTensorFunctor_map_smul_id`

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u v r w w' t

namespace Stacks.Cohomology.SiteModules

/-- **Multiplication by `c` on `R`-modules**, as an endomorphism of the identity functor of
`ModuleCat R`. -/
def smulEndId {R : Type t} [CommRing R] (c : R) : End (𝟭 (ModuleCat.{w'} R)) where
  app M := c • 𝟙 M
  naturality M N g := by
    simp only [Functor.id_obj, Functor.id_map, Linear.comp_smul, Linear.smul_comp,
      Category.comp_id, Category.id_comp]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  {O : Sheaf J CommRingCat.{r}}
  [HasWeakSheafify J AddCommGrpCat.{max u r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u r w}]
  {R : Type t} [CommRing R] (φ : R →+* GlobalFunctionRing O)

/-- The rings of sections of `O` read as a sheaf of rings are commutative. -/
local instance isMulCommutative_ringSheafOfSite_obj (X : Cᵒᵖ) :
    IsMulCommutative ((ringSheafOfSite O).obj.obj X) :=
  ⟨⟨fun a b => mul_comm (G := O.obj.obj X) a b⟩⟩

/-- **`𝒪_X ⊗_R -` carries multiplication by `c ∈ R` to multiplication by `φ(c)`.** -/
theorem baseRingTensorFunctor_map_smul_id (c : R) (M : ModuleCat.{max u r w} R) :
    (baseRingTensorFunctor.{u, v, r, w} φ).map (c • 𝟙 M) =
      globalSmul (ringSheafOfSite O) (φ c) ((baseRingTensorFunctor.{u, v, r, w} φ).obj M) :=
  (baseRingTensorAdjunction.{u, v, r, w} φ).map_endOfId (a := smulEndId c)
    (b := Stacks.SheafOfModules.globalSectionToEnd (ringSheafOfSite O) ⟨(φ c).1, (φ c).2⟩)
    (fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl))) M

end Stacks.Cohomology.SiteModules

end
