module

public import StacksFrontier.Algebra.Homology.MapBifunctorHomotopyEquiv
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.Cohomology.GodementBoundedBelowResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# The flasque reduction of the cup-product diagram, and the agreement of its two targets

Let `(S, 𝒪_S)` be a ringed space, put `A = Γ(S, 𝒪_S)`, and let `𝒦^•` and `ℳ^•` be bounded below
complexes of `𝒪_S`-modules. This file proves the first paragraph of the proof of
[Stacks, Tag 0FKV]: there are quasi-isomorphisms `a : 𝒦^• ⟶ 𝒦_1^•` and `b : ℳ^• ⟶ ℳ_1^•` as in
[Stacks, Tag 0FKT] onto bounded below complexes of *flasque* modules for which
`Tot(𝒦^• ⊗_{𝒪_S} ℳ^•) ⟶ Tot(𝒦_1^• ⊗_{𝒪_S} ℳ_1^•)` is a quasi-isomorphism, so that the two diagrams
of [Stacks, Tag 0FKV] -- the one for `(𝒦^•, ℳ^•)` and the one for `(𝒦_1^•, ℳ_1^•)` -- have the same
target `RΓ(S, Tot(𝒦^• ⊗_{𝒪_S} ℳ^•))` in `D(A)`.

## Main results

* `quasiIso_mapBifunctorMap_sheafTensor_of_forall_stalk_homotopyEquiv`: on a ringed space, if
  the stalk maps of `a` and `b` at every point are homotopy equivalences then
  `Tot(𝒦^• ⊗_{𝒪_S} ℳ^•) ⟶ Tot(𝒦_1^• ⊗_{𝒪_S} ℳ_1^•)` is a quasi-isomorphism; this is the
  consequence of [Stacks, Tag 064I] for sheaves of modules.
* `Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_quasiIso_tensor`: the previous
  statement applied to the resolution of [Stacks, Tag 0FKT] -- for bounded below `𝒦^•`, `ℳ^•`
  there *exist* bounded below complexes of flasque modules and quasi-isomorphisms onto them for
  which the induced map of total tensor complexes is a quasi-isomorphism.
* `Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_isIso_baseSections_map`: the same,
  with the conclusion read in `D(A)`: `RΓ(S, -)` of that map is an isomorphism, so the two
  diagrams of Tag 0FKV's proof have the same target.  `RΓ(S, -)` is spelled
  `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen S ⊤`, which is by definition
  `Stacks.Cohomology.GlobalKunneth.baseSections S`, the derived global sections the cup product
  of Cohomology, Section 0FKU is stated at.

## Implementation notes

Every statement about stalks is written in the `stalkComplex` spelling that
`stalkTensorComplexIso` declares, through the abbreviation `stalkComplexMap` for the stalk of a
morphism.  The `.obj`/`.map` spelling of the same thing is definitionally equal but *not*
interchangeable: `HomologicalComplex.mapBifunctorMap` carries `HasMapBifunctor` instance
arguments, and synthesis at the two spellings returns two different instance terms, so an
instance keyed on one is not found for the other even though the two morphisms are defeq.
`Stacks.SheafOfModules.KFlatStalkCriterion` makes the same observation about the two spellings
of the ring sheaf of a ringed space, which is also why the `local instance_reducible` block is
needed to synthesize `Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf`'s instances for
`S : AlgebraicGeometry.RingedSpace`.

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 0FKT](https://stacks.math.columbia.edu/tag/0FKT)
* [Stacks Project, Tag 064I](https://stacks.math.columbia.edu/tag/064I)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory

universe u

noncomputable section

namespace Stacks.Cohomology.FlasqueReduction

open AlgebraicGeometry AlgebraicGeometry.SheafOfModules
open Stacks.SheafOfModules.KFlatStalkCriterion

variable {X : TopCat.{u}}
  (R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology X) CommRingCat.{u})
  (x : X)

/-- The stalk functor at `x` on `𝒪_X`-modules is additive. -/
local instance :
    (stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).Additive :=
  stalkFunctor_additive (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x

/-- For the Grothendieck topology of open covers of `X`, the weak equivalences of presheaves of
abelian groups are the locally bijective morphisms. -/
local instance :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance

/-- The stalk at `x` of a morphism of cochain complexes of `𝒪_X`-modules, with its type
written in the `AlgebraicGeometry.SheafOfModules.stalkComplex` spelling that
`Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso` is stated in. -/
def stalkComplexMap {K K' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ}
    (a : K ⟶ K') : stalkComplex R x K ⟶ stalkComplex R x K' :=
  ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapHomologicalComplex
    (ComplexShape.up ℤ)).map a

/-- **The stalk-of-a-total-tensor-complex comparison is natural in both complexes.**  For
`a : K ⟶ K'` and `b : L ⟶ L'`, the stalk at `x` of the induced map
`Tot(K ⊗_{𝒪_X} L) ⟶ Tot(K' ⊗_{𝒪_X} L')` is, through
`Stacks.SheafOfModules.KFlatStalkCriterion.stalkTensorComplexIso`, the map induced on total
tensor complexes of stalks by the two stalk maps. -/
theorem stalkTensorComplexIso_hom_naturality
    {K K' L L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)) ≫
        (stalkTensorComplexIso R x K' L').hom =
      (stalkTensorComplexIso R x K L).hom ≫
        HomologicalComplex.mapBifunctorMap (stalkComplexMap R x a) (stalkComplexMap R x b)
          (MonoidalCategory.curriedTensor (ModuleCat.{u}
            (TopCat.Presheaf.stalk (C := RingCat.{u})
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj x)))
          (ComplexShape.up ℤ) := by
  let := fun n : ℤ => stalkFunctor_preservesAntidiagonalCoproducts
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R) x n
  apply CategoryTheory.Functor.mapBifunctorTotalIso_hom_naturality
  all_goals exact fun f N => stalkTensorIso_naturality_left (ringedSpaceOfSheaf R) x f N

/-- **The consequence of [Stacks, Tag 064I] on a ringed space.**  If `a : K ⟶ K'` and
`b : L ⟶ L'` are morphisms of cochain complexes of `𝒪_X`-modules whose stalk maps at every point
of `X` are homotopy equivalences, then the induced map `Tot(K ⊗_{𝒪_X} L) ⟶ Tot(K' ⊗_{𝒪_X} L')`
is a quasi-isomorphism.

No boundedness and no flatness is required: the hypothesis is on the stalks of `a` and `b` only. -/
theorem quasiIso_mapBifunctorMap_sheafTensor_of_forall_stalk_homotopyEquiv
    {K K' L L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R)) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (ha : ∀ y : X, ∃ e : HomotopyEquiv (stalkComplex R y K) (stalkComplex R y K'),
      e.hom = stalkComplexMap R y a)
    (hb : ∀ y : X, ∃ e : HomotopyEquiv (stalkComplex R y L) (stalkComplex R y L'),
      e.hom = stalkComplexMap R y b) :
    QuasiIso (HomologicalComplex.mapBifunctorMap a b
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R) (ComplexShape.up ℤ)) := by
  refine quasiIso_of_forall_stalk_quasiIso _ _ fun y => ?_
  obtain ⟨ea, hea⟩ := ha y
  obtain ⟨eb, heb⟩ := hb y
  have hψ : QuasiIso (HomologicalComplex.mapBifunctorMap ea.hom eb.hom
      (MonoidalCategory.curriedTensor (ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj y)))
      (ComplexShape.up ℤ)) :=
    (HomologicalComplex.mapBifunctorHomotopyEquiv
      (MonoidalCategory.curriedTensor (ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := RingCat.{u})
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj y)))
      (ComplexShape.up ℤ) ea eb).quasiIso_hom
  rw [hea, heb] at hψ
  refine (quasiIso_iff_comp_right _ (stalkTensorComplexIso R y K' L').hom).1 ?_
  erw [stalkTensorComplexIso_hom_naturality]
  exact quasiIso_comp _ _ (hφ' := hψ)
    (hφ := @quasiIso_of_isIso _ _ _ _ _ _ _ _ (stalkTensorComplexIso R y K L).isIso_hom _ _)

section Reduction

attribute [local instance 10000] HasDerivedCategory.standard

/-- A functor out of the derived category carries the class of a quasi-isomorphism to an
isomorphism. -/
private theorem isIso_map_Q_map_of_quasiIso {C : Type*} {D : Type*} [Category* C] [Category* D]
    [Abelian C] [HasDerivedCategory C] (G : DerivedCategory C ⥤ D)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (h : QuasiIso φ) :
    IsIso (G.map (DerivedCategory.Q.map φ)) := by
  have : IsIso (DerivedCategory.Q.map φ) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact h
  infer_instance

variable (S : AlgebraicGeometry.RingedSpace.{u, u})

/-- **The flasque reduction of the first paragraph of the proof of [Stacks, Tag 0FKV].**  Let
`K` and `M` be bounded below complexes of `𝒪_S`-modules.  Then there are bounded below complexes
`K₁`, `M₁` of *flasque* `𝒪_S`-modules and quasi-isomorphisms `a : K ⟶ K₁`, `b : M ⟶ M₁` --
these four conclusions are [Stacks, Tag 0FKT] -- for which the induced map

`Tot(K ⊗_{𝒪_S} M) ⟶ Tot(K₁ ⊗_{𝒪_S} M₁)`

is a quasi-isomorphism. -/
theorem exists_flasqueResolution_quasiIso_tensor
    (K M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hM : ∃ n : ℤ, M.IsStrictlyGE n) :
    ∃ (K₁ M₁ : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ)
      (a : K ⟶ K₁) (b : M ⟶ M₁),
      QuasiIso a ∧ QuasiIso b ∧
        (∃ n : ℤ, K₁.IsStrictlyGE n) ∧ (∃ n : ℤ, M₁.IsStrictlyGE n) ∧
        (∀ i : ℤ, TopCat.Sheaf.IsFlasque
          ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)).obj (K₁.X i))) ∧
        (∀ i : ℤ, TopCat.Sheaf.IsFlasque
          ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)).obj (M₁.X i))) ∧
        QuasiIso (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf)
          (ComplexShape.up ℤ)) := by
  obtain ⟨K₁, a, haqi, hKge, hKfl, hKst⟩ :=
    GodementResolution.exists_quasiIso_boundedBelow_isFlasque_isHomotopyEquiv_stalk_godement
      S K hK
  obtain ⟨M₁, b, hbqi, hMge, hMfl, hMst⟩ :=
    GodementResolution.exists_quasiIso_boundedBelow_isFlasque_isHomotopyEquiv_stalk_godement
      S M hM
  refine ⟨K₁, M₁, a, b, haqi, hbqi, hKge, hMge, hKfl, hMfl, ?_⟩
  exact quasiIso_mapBifunctorMap_sheafTensor_of_forall_stalk_homotopyEquiv S.sheaf a b
    hKst hMst

/-- **The two targets of the two diagrams in the proof of [Stacks, Tag 0FKV] are the same in
`D(A)`**, `A = Γ(S, 𝒪_S)`.  `exists_flasqueResolution_quasiIso_tensor` with its last conclusion
read after `RΓ(S, -) : D(𝒪_S) ⥤ D(A)`: the class in `D(𝒪_S)` of the induced map
`Tot(K ⊗_{𝒪_S} M) ⟶ Tot(K₁ ⊗_{𝒪_S} M₁)` is invertible, hence so is its image under derived
global sections.  In the source's words: "Thus the targets
`RΓ(X, Tot(𝒦^• ⊗ ℳ^•)) = RΓ(X, Tot(𝒦_1^• ⊗ ℳ_1^•))` of the two diagrams are the same in `D(A)`." -/
theorem exists_flasqueResolution_isIso_baseSections_map
    (K M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hM : ∃ n : ℤ, M.IsStrictlyGE n) :
    ∃ (K₁ M₁ : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)) ℤ)
      (a : K ⟶ K₁) (b : M ⟶ M₁),
      QuasiIso a ∧ QuasiIso b ∧
        (∃ n : ℤ, K₁.IsStrictlyGE n) ∧ (∃ n : ℤ, M₁.IsStrictlyGE n) ∧
        (∀ i : ℤ, TopCat.Sheaf.IsFlasque
          ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)).obj (K₁.X i))) ∧
        (∀ i : ℤ, TopCat.Sheaf.IsFlasque
          ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} S.sheaf)).obj (M₁.X i))) ∧
        IsIso ((Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen S ⊤).map
          (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf)
            (ComplexShape.up ℤ)))) := by
  obtain ⟨K₁, M₁, a, b, haqi, hbqi, hKge, hMge, hKfl, hMfl, hqi⟩ :=
    exists_flasqueResolution_quasiIso_tensor S K M hK hM
  exact ⟨K₁, M₁, a, b, haqi, hbqi, hKge, hMge, hKfl, hMfl,
    isIso_map_Q_map_of_quasiIso _ _ hqi⟩

end Reduction

end Stacks.Cohomology.FlasqueReduction

end

end
