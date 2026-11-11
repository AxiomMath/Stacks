module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCubeUnboundedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoUnboundedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnboundedCompositionIsoIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded base change isomorphisms of `Rf_!` are compatible with composition

[Stacks, Tag 0F7L], second part, on the unbounded derived categories `D(X_étale, Λ)` for a
torsion ring `Λ`: the isomorphisms `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹`
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso`) are compatible with the
isomorphisms `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J]
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`). The case of `D⁺_tors(X_étale, Λ)`
for an arbitrary ring is `Stacks.EtaleCohomology.derivedLowerShriekBaseChange_compIso`.

The proof is the source's: through an auxiliary compactification `X ⟶ X̄` of `X` over the
compactification `Ȳ` of `Y` the isomorphism of [Stacks, Tag 0F7J] is
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso`
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_hom_app_eq`), which commutes with
base change (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompOverIso_baseChange`), and the
base change maps do not depend on the compactifications
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeCube_eq` and
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange_compactificationIso`).

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange_compIso`.

## References

* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- The chase of `derivedLowerShriekUnboundedBaseChange_compIso`, over plain objects. -/
private theorem unboundedCompIso_baseChange_chain {C C' D : Type*} [Category* C] [Category* C']
    [Category* D] (Dh : C ⥤ C') (Rg' : D ⥤ C')
    {A₀ A₁ A₂ A₃ : C} {B₁ B₂ B₃ : C'} {E₀ E₁ E₂ E₄ : D}
    (Φ : A₀ ⟶ A₃) (ci1 : A₀ ⟶ A₁) (co : A₁ ⟶ A₂) (rci2 : A₂ ⟶ A₃)
    (bcg2 : Dh.obj A₃ ⟶ Rg'.obj E₀) (bcfjf : E₀ ⟶ E₁) (bcg1 : Dh.obj A₂ ⟶ Rg'.obj E₂)
    (dci2 : E₂ ⟶ E₀) (bc'f : E₂ ⟶ E₄) (ci5 : E₄ ⟶ E₁) (bcfg' : Dh.obj A₁ ⟶ B₁)
    (co' : B₁ ⟶ Rg'.obj E₄) (bcfgcO : Dh.obj A₁ ⟶ B₂) (ci6 : B₂ ⟶ B₁) (bcfgj : Dh.obj A₀ ⟶ B₃)
    (ci7 : B₃ ⟶ B₂) (ci8 : B₃ ⟶ B₁) (Φ' : B₃ ⟶ Rg'.obj E₁)
    (hΦ : Φ = ci1 ≫ co ≫ rci2)
    (hb : Dh.map rci2 ≫ bcg2 = bcg1 ≫ Rg'.map dci2)
    (hc : dci2 ≫ bcfjf = bc'f ≫ ci5)
    (he : Dh.map co ≫ bcg1 ≫ Rg'.map bc'f = bcfg' ≫ co')
    (hg : bcfg' = bcfgcO ≫ ci6) (hf : Dh.map ci1 ≫ bcfgcO = bcfgj ≫ ci7)
    (hh : ci7 ≫ ci6 = ci8) (hΦ' : Φ' = ci8 ≫ co' ≫ Rg'.map ci5) :
    Dh.map Φ ≫ bcg2 ≫ Rg'.map bcfjf = bcfgj ≫ Φ' := by
  rw [hΦ, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, reassoc_of% hb,
    ← Functor.map_comp, hc, Functor.map_comp, reassoc_of% he, hg, Category.assoc,
    reassoc_of% hf, hΦ', reassoc_of% hh]

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)
  {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z}
  {hY : Y' ⟶ Y} {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Z'] [QuasiSeparatedSpace Z']
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

open CompactificationOf in
/-- **Stacks Project, Tag 0F7L, the compatibility with Tag 0F7J, on `D(X_étale, Λ)`.** For
cartesian squares of quasi-compact and quasi-separated schemes
```
X' --hX--> X
|f'        |f
Y' --hY--> Y
|g'        |g
Z' --h-->  Z
```
with `f` and `g` separated of finite type and a torsion ring `Λ`, the base change isomorphisms
`h⁻¹ ∘ R(g ∘ f)_! ≅ R(g' ∘ f')_! ∘ hX⁻¹`, `h⁻¹ ∘ Rg_! ≅ Rg'_! ∘ hY⁻¹` and
`hY⁻¹ ∘ Rf_! ≅ Rf'_! ∘ hX⁻¹` of `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso`
(whose components are `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange`) are
compatible with the isomorphisms `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` and `R(g' ∘ f')_! ≅ Rg'_! ∘ Rf'_!` of
[Stacks, Tag 0F7J] (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`) on the unbounded
derived category `D(X_étale, Λ)`, for arbitrary compactifications `jf`, `jg`, `j` of `f`, `g`,
`g ∘ f`, the primed functors being computed through their base changes. The case of
`D⁺_tors(X_étale, Λ)` for an arbitrary ring is
`Stacks.EtaleCohomology.derivedLowerShriekBaseChange_compIso`. -/
@[stacks 0F7L "compatibility with the isomorphisms of 0F7J, on unbounded D(X_étale, Λ), Λ torsion"]
theorem derivedLowerShriekUnboundedBaseChange_compIso (sqg : IsPullback hY g' g h)
    (sqf : IsPullback hX f' f hY) (jf : CompactificationOf (Over.mk f))
    (jg : CompactificationOf (Over.mk g)) (j : CompactificationOf (Over.mk (f ≫ g)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    haveI : IsSeparated f' := MorphismProperty.of_isPullback sqf inferInstance
    haveI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sqf inferInstance
    haveI : IsSeparated g' := MorphismProperty.of_isPullback sqg inferInstance
    haveI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback sqg inferInstance
    (etaleModuleDerivedInverseImage.{u, 0} Λ h).map
        ((derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jg j).hom.app K) ≫
      (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sqg jg).app
        ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K) ≫
      (derivedLowerShriekUnbounded.{u, 0} g' (jg.baseChange sqg) Λ).map
        ((derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sqf jf).app K) =
    (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ (sqf.paste_vert sqg) j).app K ≫
      (derivedLowerShriekUnboundedCompIso Λ hΛ f' g' (jf.baseChange sqf) (jg.baseChange sqg)
        (j.baseChange (sqf.paste_vert sqg))).hom.app
          ((etaleModuleDerivedInverseImage.{u, 0} Λ hX).obj K) := by
  have : IsSeparated f' := MorphismProperty.of_isPullback sqf inferInstance
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sqf inferInstance
  have : IsSeparated g' := MorphismProperty.of_isPullback sqg inferInstance
  have : LocallyOfFiniteType g' := MorphismProperty.of_isPullback sqg inferInstance
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  have : QuasiCompact f' := quasiCompact_of_compactSpace f'
  have : QuasiCompact (f' ≫ g') := quasiCompact_of_compactSpace _
  have : QuasiCompact (f ≫ jg.immersion) := quasiCompact_of_compactSpace _
  have : UniversallyClosed jg.toBase := IsProper.toUniversallyClosed
  have : QuasiCompact jg.toBase := instQuasiCompactOfUniversallyClosed jg.toBase
  have : CompactSpace jg.space := QuasiCompact.compactSpace_of_compactSpace jg.toBase
  have : UniversallyClosed (jg.baseChange sqg).toBase := IsProper.toUniversallyClosed
  have : QuasiCompact (jg.baseChange sqg).toBase :=
    instQuasiCompactOfUniversallyClosed (jg.baseChange sqg).toBase
  have : CompactSpace (jg.baseChange sqg).space :=
    QuasiCompact.compactSpace_of_compactSpace (jg.baseChange sqg).toBase
  let jX := (nonempty_compactificationOf_comp_immersion f g jg).some
  let jXs := compImmersionBaseChange sqg sqf jg jX
  let K' := (etaleModuleDerivedInverseImage.{u, 0} Λ hX).obj K
  have hΦ := derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g jf jg j jX K
  have hΦ' := derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f' g' (jf.baseChange sqf)
    (jg.baseChange sqg) (j.baseChange (sqf.paste_vert sqg)) jXs K'
  have hb := (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sqg jg).naturality
    ((derivedLowerShriekUnboundedCompactificationIsoUniv f (restrictBase jg jX) jf Λ hΛ).hom.app K)
  simp only [Functor.comp_map] at hb
  have hc := NatTrans.congr_app (derivedLowerShriekUnboundedBaseChange_compactificationIso Λ sqf hΛ
    (restrictBase jg jX) jf) K
  have hd := NatTrans.congr_app (derivedLowerShriekUnboundedBaseChangeCube_eq Λ sqf hΛ
    (restrictBase jg jX) (restrictBase (jg.baseChange sqg) jXs)
    (restrictBaseBaseChangeι sqg sqf jg jX) (isPullback_restrictBase_baseChange sqg sqf jg jX)
    (restrictBase_baseChange_toBase_comm sqg sqf jg jX)) K
  have hci := NatTrans.congr_app (congrArg Iso.hom
    (derivedLowerShriekUnboundedCompactificationIsoUniv_trans f' Λ hΛ
      ((restrictBase jg jX).baseChange sqf) (restrictBase (jg.baseChange sqg) jXs)
      (jf.baseChange sqf))) K'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom] at hc hd hci
  have hc' : (etaleModuleDerivedInverseImage.{u, 0} Λ hY).map
        ((derivedLowerShriekUnboundedCompactificationIsoUniv f (restrictBase jg jX) jf Λ
          hΛ).hom.app K) ≫
      (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sqf jf).app K =
      (derivedLowerShriekUnboundedBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) jXs) (restrictBaseBaseChangeι sqg sqf jg jX)
          (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).app K ≫
        (derivedLowerShriekUnboundedCompactificationIsoUniv f'
          (restrictBase (jg.baseChange sqg) jXs) (jf.baseChange sqf) Λ hΛ).hom.app K' := by
    rw [hc, hd, ← hci, Category.assoc]
  have he := derivedLowerShriekUnboundedCompOverIso_baseChange Λ hΛ sqg sqf jg jX K
  have hg := NatTrans.congr_app (derivedLowerShriekUnboundedBaseChangeCube_eq Λ
    (sqf.paste_vert sqg) hΛ (compOver jg jX) (compOver (jg.baseChange sqg) jXs)
    (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_compOver_baseChange sqg sqf jg jX)
    (compOver_baseChange_toBase_comm sqg sqf jg jX)) K
  have hf := NatTrans.congr_app (derivedLowerShriekUnboundedBaseChange_compactificationIso Λ
    (sqf.paste_vert sqg) hΛ j (compOver jg jX)) K
  have hh := NatTrans.congr_app (congrArg Iso.hom
    (derivedLowerShriekUnboundedCompactificationIsoUniv_trans (f' ≫ g') Λ hΛ
      (j.baseChange (sqf.paste_vert sqg)) ((compOver jg jX).baseChange (sqf.paste_vert sqg))
      (compOver (jg.baseChange sqg) jXs))) K'
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_hom] at hg hf hh
  exact unboundedCompIso_baseChange_chain (etaleModuleDerivedInverseImage.{u, 0} Λ h)
    (derivedLowerShriekUnbounded.{u, 0} g' (jg.baseChange sqg) Λ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ hΦ hb hc' he hg hf hh hΦ'

end Stacks.EtaleCohomology

end
