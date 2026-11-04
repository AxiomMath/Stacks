module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# Higher direct images and the flat base change property on algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact (**Stacks 050U**) and quasi-separated (**Stacks 04YW**)
1-morphism of algebraic stacks over a scheme `S`, and let `ℱ` be a sheaf of `𝒪_𝒳`-modules on
`𝒳_étale` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat base change property
(**Stacks 0762**). **Stacks 0765** says that every higher direct image `Rⁱf_*ℱ`, computed in the
étale topology, has the flat base change property.

This file records that statement at general degree, together with the reduction available in
degree zero. **No part of Stacks 0765 is claimed here** and no tag is recorded: nothing here proves
of any `Rⁱf_*ℱ` that it has the flat base change property. **Stacks 0765** itself is
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_moduleSheafHigherDirectImage`, with the
flat base change property read on sheaves.

In degree zero the higher direct image is the direct image of **Stacks 06WE**, so the assertion
for `R⁰f_*ℱ` is equivalent to the assertion for `f_*ℱ`. That equivalence holds for every
1-morphism and every module, with none of the hypotheses of the source. It is a *reduction* and
not an assertion about `R⁰f_*ℱ`: the flat base change property of `f_*ℱ` is not proved here.

At general degree the statement is recorded with the step the source's proof turns on carried as
the hypothesis `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyDirectImages`. That hypothesis
contains the conclusion in positive degree, so the general-degree statement proves nothing.

## Main definitions

* `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyDirectImages`: for a 1-morphism of algebraic
  stacks, the assertion that the direct image of **Stacks 06WE** and the higher direct images in
  positive degree of a module satisfying the hypotheses of **Stacks 0765** all have the flat base
  change property. In positive degree this is the conclusion of the source itself.

## Main results

* `AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE_naturality`: **Stacks 06WC** is
  natural in the module at a module universe above that of the schemes.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_of_iso`: the flat base change property
  at such a module universe transports along an isomorphism of presheaves of modules.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_moduleSheafHigherDirectImage_zero_iff`:
  in degree zero, the flat base change property of the higher direct image is equivalent to that
  of the direct image, with the universe of the schemes independent of the universes of the two
  fibred categories.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_higherDirectImage_zero_iff`: the same
  equivalence for a 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_higherDirectImage`: the statement of
  **Stacks 0765** at general degree, granted
  `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyDirectImages`.

## Implementation notes

### The universes at which the statement can be formed

The higher direct image of **Stacks 06WE** is computed by limits indexed by the two fibred
categories, so for `𝒳` with objects in `Type v` and morphisms in `Type w` and `𝒴` with objects in
`Type v'` and morphisms in `Type w'` over schemes in `Type u`, it produces sheaves of modules
with sections in `max u v w v' w'`. The underlying category of an algebraic stack lies in
`Type (u + 1)` with morphisms in `Type u`, as the big fppf category over `S` itself does, so for a
1-morphism of algebraic stacks that universe is `u + 1` while the schemes stay in `u`.

`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` asks for a module with sections in `u`, and
the two therefore do not meet. The flat base change property used here is instead
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`, whose module universe is free over the
universe of the schemes subject only to `UnivLE`; it is built on the comparison map
`AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE`. The naturality of that
comparison map in the module, which the transport along an isomorphism of modules and hence the
degree-zero reduction need, is proved here at the free module universe.

The degree-zero reduction is therefore available for every 1-morphism of categories fibred in
groupoids with the universe of the schemes independent of the four category universes, and the
statement for a 1-morphism of algebraic stacks is its instance at
`v = v' = u + 1` and `w = w' = u`.

### Why the general-degree statement proves nothing

The positive-degree clause of `AlgebraicGeometry.Stack.HasFlatBaseChangePropertyDirectImages` is
the conclusion of **Stacks 0765** in those degrees, so the general-degree statement below is an
implication from the source's conclusion to itself and establishes none of it.

## References

* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WL](https://stacks.math.columbia.edu/tag/06WL)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073N](https://stacks.math.columbia.edu/tag/073N)
* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 075P](https://stacks.math.columbia.edu/tag/075P)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0765](https://stacks.math.columbia.edu/tag/0765)
* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
* [Stacks Project, Tag 07AP](https://stacks.math.columbia.edu/tag/07AP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w v' w' m t

namespace AlgebraicGeometry.Stack

section Naturality

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) {x y : 𝒳} (φ : x ⟶ y)

/-- **Stacks 06WC.** The comparison map `c_φ` of
`AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE` is natural in the module. -/
theorem restrictModulePullbackComparisonUnivLE_naturality [UnivLE.{u, m}]
    {F F' : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj} (α : F ⟶ F') :
    (PresheafOfModules.pullback.{m}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).map
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ y).map α) ≫
          restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F' =
      restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F ≫
        (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x).map α := by
  have hleft := (PresheafOfModules.pullbackPushforwardAdjunction.{m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv_naturality_left_symm
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ y).map α)
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F')
  have hright := (PresheafOfModules.pullbackPushforwardAdjunction.{m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv_naturality_right_symm
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F)
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x).map α)
  rw [restrictModulePushforwardComparison_naturality B E h S hS p hp τ hτ φ α] at hleft
  exact hleft.symm.trans hright

/-- The flat base change property of **Stacks 0762**, at a module universe above that of the
schemes, transports along an isomorphism of presheaves of modules. -/
theorem hasFlatBaseChangePropertyUnivLE_of_iso [UnivLE.{u, m}]
    {F F' : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj} (e : F ≅ F')
    (hF : HasFlatBaseChangePropertyUnivLE B E h S hS p hp τ hτ F) :
    HasFlatBaseChangePropertyUnivLE B E h S hS p hp τ hτ F' := by
  intro a b ψ hflat
  have : IsIso (restrictModulePullbackComparisonUnivLE B E h S hS p hp ψ τ hτ F) := hF ψ hflat
  refine (isIso_comp_left_iff ((PresheafOfModules.pullback.{m}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ))
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ b).map e.hom)) _).1 ?_
  rw [restrictModulePullbackComparisonUnivLE_naturality]
  exact IsIso.comp_isIso' this
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ a).map_isIso e.hom)

end Naturality

section DegreeZero

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  [HasWeakSheafify (associatedTopology B S hS p τ) AddCommGrpCat.{max u v w v' w'}]
  [(associatedTopology B S hS p τ).WEqualsLocallyBijective AddCommGrpCat.{max u v w v' w'}]
  [HasWeakSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{max u v w v' w'}]
  [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{max u v w v' w'}]

/-- In degree zero the higher direct image of a sheaf of modules is the direct image of
**Stacks 06WE**, so it has the flat base change property of **Stacks 0762** exactly when the
direct image does.

The universe of the schemes is independent of the universes of the two fibred categories here: the
flat base change property is the one of
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`, whose module universe is free, and
`max u v w v' w'` is the module universe the higher direct image is constructed at. -/
theorem hasFlatBaseChangePropertyUnivLE_moduleSheafHigherDirectImage_zero_iff
    (M : SheafOfModules.{max u v w v' w'} (ringStructureSheafCore B S hS p hp τ hτ)) :
    HasFlatBaseChangePropertyUnivLE B E h S hS q hq τ hτ
        (((moduleSheafHigherDirectImage B S hS p q hp hq f hf τ hτ 0).obj M).val) ↔
      HasFlatBaseChangePropertyUnivLE B E h S hS q hq τ hτ
        (((moduleSheafPushforward.{u, v, w, u, v', w'}
          B S hS p q hp hq f hf τ hτ).obj M).val) := by
  have e :
      (((moduleSheafHigherDirectImage B S hS p q hp hq f hf τ hτ 0).obj M).val) ≅
        (((moduleSheafPushforward.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ).obj M).val) :=
    (SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ)).mapIso
      ((moduleSheafHigherDirectImageZeroIso B S hS p q hp hq f hf τ hτ).app M)
  exact ⟨fun hF => hasFlatBaseChangePropertyUnivLE_of_iso B E h S hS q hq τ hτ e hF,
    fun hF => hasFlatBaseChangePropertyUnivLE_of_iso B E h S hS q hq τ hτ e.symm hF⟩

end DegreeZero

section AlgebraicStack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
  [HasWeakSheafify (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)).WEqualsLocallyBijective
    AddCommGrpCat.{u + 1}]
  [HasWeakSheafify (associatedTopology B S hS 𝒴.val.val.p (etaleTopology B))
    AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS 𝒴.val.val.p (etaleTopology B)).WEqualsLocallyBijective
    AddCommGrpCat.{u + 1}]

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` and a sheaf of `𝒪_𝒳`-modules `ℱ` on
`𝒳_étale`, the zeroth higher direct image `R⁰f_*ℱ` has the flat base change property of
**Stacks 0762** exactly when the direct image `f_*ℱ` of **Stacks 06WE** does.

It assumes nothing: neither quasi-compactness nor quasi-separatedness of `f`, nor local
quasi-coherence of `ℱ`, nor the flat base change property of `ℱ` enters, because `R⁰f_*` is `f_*`
and the two assertions are the same assertion. The flat base change property is read at the
module universe `u + 1` of the higher direct image, by
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`.

This is a reduction of the degree-zero case of **Stacks 0765** to the underived direct image and
not an assertion about `R⁰f_*ℱ`, so no tag is recorded. -/
theorem hasFlatBaseChangePropertyUnivLE_higherDirectImage_zero_iff
    (ℱ : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))) :
    HasFlatBaseChangePropertyUnivLE B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)
        (((moduleSheafHigherDirectImage B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (etaleTopology B)
          (etaleTopology_le_topology B) 0).obj ℱ).val) ↔
      HasFlatBaseChangePropertyUnivLE B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)
        (((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (etaleTopology B)
          (etaleTopology_le_topology B)).obj ℱ).val) :=
  hasFlatBaseChangePropertyUnivLE_moduleSheafHigherDirectImage_zero_iff
    B E h S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (etaleTopology B) (etaleTopology_le_topology B) ℱ

/-- **The flat base change property of the direct images along a 1-morphism of algebraic
stacks.** For `f : 𝒳 ⟶ 𝒴` this is the assertion that whenever `f` is quasi-compact
(**Stacks 050U**) and quasi-separated (**Stacks 04YW**) and a sheaf of `𝒪_𝒳`-modules `G` on
`𝒳_étale` is locally quasi-coherent (**Stacks 06WJ**) and has the flat base change property
(**Stacks 0762**), the direct image `f_*G` of **Stacks 06WE** and every higher direct image
`R^{i+1}f_*G` have the flat base change property.

In positive degree this is the conclusion of **Stacks 0765** itself, so nothing is established by
assuming it. The degree-zero clause is stated for the *underived* direct image, which
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertyUnivLE_higherDirectImage_zero_iff` relates to
`R⁰f_*`. -/
abbrev HasFlatBaseChangePropertyDirectImages : Prop :=
  ∀ (G : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B))),
    IsQuasiCompactMorphism B S hS f → AlgebraicStacks.IsQuasiSeparated B S hS f →
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids G.val →
    HasFlatBaseChangePropertyUnivLE B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) G.val →
    HasFlatBaseChangePropertyUnivLE B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
        (etaleTopology B) (etaleTopology_le_topology B)
        (((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (etaleTopology B)
          (etaleTopology_le_topology B)).obj G).val) ∧
      ∀ i : ℕ, HasFlatBaseChangePropertyUnivLE B E h S hS 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
        (((moduleSheafHigherDirectImage B S hS 𝒳.val.val.p 𝒴.val.val.p
          𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
          (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (etaleTopology B)
          (etaleTopology_le_topology B) (i + 1)).obj G).val)

/-- **The statement of Stacks 0765 at general degree.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and
quasi-separated 1-morphism of algebraic stacks over `S` and let `ℱ` be a sheaf of `𝒪_𝒳`-modules
on `𝒳_étale` which is locally quasi-coherent (**Stacks 06WJ**) and has the flat base change
property (**Stacks 0762**). The conclusion recorded here is that of the source: each higher direct
image `Rⁱf_*ℱ`, computed in the étale topology, has the flat base change property.

**No part of Stacks 0765 is claimed and no tag is recorded.** The hypothesis `hbc` is
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyDirectImages`, whose positive-degree clause is
the conclusion in those degrees, so this is an implication from the source's conclusion to itself.
-/
theorem hasFlatBaseChangePropertyUnivLE_higherDirectImage
    (hqc : IsQuasiCompactMorphism B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (ℱ : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)))
    (hlqc : IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ℱ.val)
    (hfbc : HasFlatBaseChangePropertyUnivLE B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) ℱ.val)
    (hbc : HasFlatBaseChangePropertyDirectImages B E h S hS f) (i : ℕ) :
    HasFlatBaseChangePropertyUnivLE B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)
      (((moduleSheafHigherDirectImage B S hS 𝒳.val.val.p 𝒴.val.val.p
        𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (etaleTopology B)
        (etaleTopology_le_topology B) i).obj ℱ).val) := by
  obtain ⟨hzero, hsucc⟩ := hbc ℱ hqc hqs hlqc hfbc
  intro a b ψ hflat
  cases i with
  | zero =>
    exact (hasFlatBaseChangePropertyUnivLE_higherDirectImage_zero_iff
      B E h S hS f ℱ).2 hzero ψ hflat
  | succ j => exact hsucc j ψ hflat

end AlgebraicStack

end AlgebraicGeometry.Stack

end
