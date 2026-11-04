module

public import StacksFrontier.Topology.Sheaves.Modules.StalkCokernel

/-!
# A map between two cokernels of sheaves of modules, read elementwise on stalks

Let `𝒪` be a sheaf of rings on a topological space `X`, let `f : A ⟶ B` and `γ : L ⟶ M` be
morphisms of sheaves of `𝒪`-modules and let `ψ : B ⟶ M` be a morphism with
`f ≫ ψ ≫ cokernel.π γ = 0`, so that `ψ` descends to a morphism of cokernels

`coker f ⟶ coker γ`.

`AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_iff_forall_bijective_liftQ` already presents
the *source* of such a descended map at a stalk as the quotient `B_x ⧸ range (f_x)`, but leaves
its target as the stalk of the sheaf cokernel `coker γ`.  This file presents that target as the
quotient `M_x ⧸ range (γ_x)` as well, so that the whole criterion becomes a statement about one
map of explicit quotient modules over the stalk ring — the shape in which a surjectivity proof
and an injectivity proof carried out at the ring level can be fed in.

The identification of the target is
`AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso`, the stalk of a cokernel being the
cokernel of the stalks, followed by Mathlib's `ModuleCat.cokernelIsoRangeQuotient`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.stalkObjCokernelRangeQuotientIso`: **the stalk of a cokernel
  of sheaves of modules is the quotient of the stalk by the range of the stalk map.**

## Main results

* `AlgebraicGeometry.SheafOfModules.stalkMap_π_comp_stalkObjCokernelRangeQuotientIso_hom` and
  `stalkObjCokernelRangeQuotientIso_hom_stalkMap_π`: the identification carries the stalk of the
  cokernel projection to the quotient projection, as morphisms and elementwise.
* `AlgebraicGeometry.SheafOfModules.range_stalkMap_le_ker_mkQ_comp_stalkMap`: the side condition
  of the `Submodule.liftQ` below.
* `AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_comp_π_iff_forall_bijective_liftQ`: **a
  map of cokernels of sheaves of modules is an isomorphism exactly when the induced map
  `B_x ⧸ range (f_x) ⟶ M_x ⧸ range (γ_x)` is bijective at every point.**

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG), isomorphy is stalkwise.
* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH), the stalk functor is
  exact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

variable {A B L M : _root_.SheafOfModules.{u} 𝒪}

/-- **The stalk of a cokernel of sheaves of modules is the quotient of the stalk of the target by
the range of the stalk map.**  It is
`AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso`, the stalk of a cokernel being the
cokernel of the stalks, followed by `ModuleCat.cokernelIsoRangeQuotient`. -/
def stalkObjCokernelRangeQuotientIso (γ : L ⟶ M) :
    stalkObj 𝒪 x (cokernel γ) ≅
      ModuleCat.of _ (ToType (stalkObj 𝒪 x M) ⧸ LinearMap.range (stalkMap 𝒪 x γ).hom) :=
  (stalkObjCokernelIso 𝒪 x γ).trans (ModuleCat.cokernelIsoRangeQuotient (stalkMap 𝒪 x γ))

/-- The identification of `AlgebraicGeometry.SheafOfModules.stalkObjCokernelRangeQuotientIso`
carries the stalk of the cokernel projection of `γ` to the projection onto the quotient by the
range of the stalk map of `γ`. -/
@[reassoc]
theorem stalkMap_π_comp_stalkObjCokernelRangeQuotientIso_hom (γ : L ⟶ M) :
    stalkMap 𝒪 x (cokernel.π γ) ≫ (stalkObjCokernelRangeQuotientIso 𝒪 x γ).hom =
      ModuleCat.ofHom (LinearMap.range (stalkMap 𝒪 x γ).hom).mkQ := by
  rw [stalkObjCokernelRangeQuotientIso, Iso.trans_hom, ← Category.assoc,
    stalkMap_π_comp_stalkObjCokernelIso_hom,
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]

/-- `AlgebraicGeometry.SheafOfModules.stalkMap_π_comp_stalkObjCokernelRangeQuotientIso_hom`
read elementwise. -/
theorem stalkObjCokernelRangeQuotientIso_hom_stalkMap_π (γ : L ⟶ M)
    (m : ToType (stalkObj 𝒪 x M)) :
    (stalkObjCokernelRangeQuotientIso 𝒪 x γ).hom.hom ((stalkMap 𝒪 x (cokernel.π γ)).hom m) =
      (LinearMap.range (stalkMap 𝒪 x γ).hom).mkQ m :=
  congrArg (fun φ => ModuleCat.Hom.hom φ m)
    (stalkMap_π_comp_stalkObjCokernelRangeQuotientIso_hom 𝒪 x γ)

/-- Projecting the stalk of `ψ` to the quotient by the range of `γ_x` is the stalk of
`ψ ≫ cokernel.π γ` followed by the identification of the stalk of `coker γ` with that quotient. -/
private theorem mkQ_stalkMap_eq_iso_hom_stalkMap_comp_π (γ : L ⟶ M) (ψ : B ⟶ M)
    (y : ToType (stalkObj 𝒪 x B)) :
    (LinearMap.range (stalkMap 𝒪 x γ).hom).mkQ ((stalkMap 𝒪 x ψ).hom y) =
      (stalkObjCokernelRangeQuotientIso 𝒪 x γ).hom.hom
        ((stalkMap 𝒪 x (ψ ≫ cokernel.π γ)).hom y) := by
  rw [show stalkMap 𝒪 x (ψ ≫ cokernel.π γ) =
      stalkMap 𝒪 x ψ ≫ stalkMap 𝒪 x (cokernel.π γ) from (stalkFunctor 𝒪 x).map_comp _ _]
  exact (stalkObjCokernelRangeQuotientIso_hom_stalkMap_π 𝒪 x γ _).symm

/-- The side condition of the `Submodule.liftQ` of
`AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_comp_π_iff_forall_bijective_liftQ`: if
`f ≫ ψ ≫ cokernel.π γ` vanishes then at every stalk the range of `f` is carried by `ψ` into the
range of `γ`. -/
theorem range_stalkMap_le_ker_mkQ_comp_stalkMap {f : A ⟶ B} {γ : L ⟶ M} {ψ : B ⟶ M}
    (h : f ≫ ψ ≫ cokernel.π γ = 0) :
    LinearMap.range (stalkMap 𝒪 x f).hom ≤
      LinearMap.ker ((LinearMap.range (stalkMap 𝒪 x γ).hom).mkQ.comp
        (stalkMap 𝒪 x ψ).hom) := by
  intro y hy
  have h₁ : (stalkMap 𝒪 x (ψ ≫ cokernel.π γ)).hom y = 0 :=
    range_stalkMap_le_ker_stalkMap 𝒪 x h hy
  rw [LinearMap.mem_ker, LinearMap.comp_apply, mkQ_stalkMap_eq_iso_hom_stalkMap_comp_π, h₁,
    map_zero]

/-- **A map between two cokernels of sheaves of modules is an isomorphism exactly when the
induced map of quotients is bijective at every point.**  For `f : A ⟶ B`, `γ : L ⟶ M` and
`ψ : B ⟶ M` with `f ≫ ψ ≫ cokernel.π γ = 0`, the descended morphism
`coker f ⟶ coker γ` is an isomorphism if and only if, for every point `x` of `X`, the map

`B_x ⧸ range (γ_x ∘ -) ⟶ M_x ⧸ range (γ_x)`

induced by the stalk of `ψ` is bijective.

This is
`AlgebraicGeometry.SheafOfModules.isIso_cokernelDesc_iff_forall_bijective_liftQ` with the stalk
of the target cokernel read as a quotient module through
`AlgebraicGeometry.SheafOfModules.stalkObjCokernelRangeQuotientIso`; the two sides of the
criterion differ by that isomorphism, which does not affect bijectivity. -/
theorem isIso_cokernelDesc_comp_π_iff_forall_bijective_liftQ (f : A ⟶ B) (γ : L ⟶ M) (ψ : B ⟶ M)
    (h : f ≫ ψ ≫ cokernel.π γ = 0) :
    IsIso (cokernel.desc f (ψ ≫ cokernel.π γ) h) ↔ ∀ x : X,
      Function.Bijective ((LinearMap.range (stalkMap 𝒪 x f).hom).liftQ
        ((LinearMap.range (stalkMap 𝒪 x γ).hom).mkQ.comp (stalkMap 𝒪 x ψ).hom)
        (range_stalkMap_le_ker_mkQ_comp_stalkMap 𝒪 x h)) := by
  rw [isIso_cokernelDesc_iff_forall_bijective_liftQ]
  refine forall_congr' fun x => ?_
  have he : Function.Bijective (stalkObjCokernelRangeQuotientIso 𝒪 x γ).hom.hom :=
    ConcreteCategory.bijective_of_isIso (stalkObjCokernelRangeQuotientIso 𝒪 x γ).hom
  have key : ⇑((LinearMap.range (stalkMap 𝒪 x f).hom).liftQ
        ((LinearMap.range (stalkMap 𝒪 x γ).hom).mkQ.comp (stalkMap 𝒪 x ψ).hom)
        (range_stalkMap_le_ker_mkQ_comp_stalkMap 𝒪 x h)) =
      (stalkObjCokernelRangeQuotientIso 𝒪 x γ).hom.hom ∘
        ⇑((LinearMap.range (stalkMap 𝒪 x f).hom).liftQ
          (stalkMap 𝒪 x (ψ ≫ cokernel.π γ)).hom
          (range_stalkMap_le_ker_stalkMap 𝒪 x h)) := by
    refine funext fun q => ?_
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (stalkMap 𝒪 x f).hom) q
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply, Function.comp_apply,
      LinearMap.comp_apply]
    exact mkQ_stalkMap_eq_iso_hom_stalkMap_comp_π 𝒪 x γ ψ _
  rw [key]
  exact (he.of_comp_iff' _).symm

end AlgebraicGeometry.SheafOfModules

end

end
