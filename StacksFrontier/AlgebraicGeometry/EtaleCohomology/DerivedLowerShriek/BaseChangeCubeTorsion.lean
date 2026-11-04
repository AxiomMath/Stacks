module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCubeComposition
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InverseImageTorsion

/-!
# The base change map of `Rf_!` does not depend on the compactification

On `D⁺_tors`, the base change map `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of a cube of compactifications is
the base change map through the base change of the compactification followed by the canonical
comparison of the two compactifications; and the base change maps of two compactifications
correspond under the canonical comparisons.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekHomIso_id`: the comparison along the identity of a
  compactification is the identity.
* `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeCube_app_eq`: the base change map of a cube
  is the base change map through the base change of the compactification followed by the
  canonical comparison.
* `Stacks.EtaleCohomology.derivedLowerShriekBaseChange_compactificationIso`: the base change maps
  of two compactifications correspond under the canonical comparisons.

## References

* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ]

/-- The comparison of `Rf_!` along the identity of a compactification is the identity. -/
lemma derivedLowerShriekHomIso_id {X Y : Scheme.{u}} {f : X ⟶ Y}
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekHomIso Λ (𝟙 j) = Iso.refl _ := by
  have h := congrArg Iso.hom (derivedLowerShriekHomIso_comp Λ (𝟙 j) (𝟙 j))
  rw [Category.comp_id, Iso.trans_hom] at h
  refine Iso.ext (NatTrans.ext (funext fun K ↦ ?_))
  have h' := NatTrans.congr_app h K
  simp only [NatTrans.comp_app] at h'
  rw [Iso.refl_hom, NatTrans.id_app,
    ← cancel_mono ((derivedLowerShriekHomIso Λ (𝟙 j)).hom.app K), Category.id_comp]
  exact h'.symm

/-- The canonical comparison of `Rf_!` for a compactification with itself is the identity. -/
lemma derivedLowerShriekCompactificationIso_self {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekCompactificationIso f j j Λ = Iso.refl _ := by
  rw [derivedLowerShriekCompactificationIso_of_hom f Λ (𝟙 j), derivedLowerShriekHomIso_id]

/-- The canonical comparisons of `Rf_!` for two compactifications are inverse to each other. -/
lemma derivedLowerShriekCompactificationIso_symm {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (j k : CompactificationOf (Over.mk f)) :
    (derivedLowerShriekCompactificationIso f j k Λ).symm =
      derivedLowerShriekCompactificationIso f k j Λ := by
  have h := derivedLowerShriekCompactificationIso_trans f Λ j k j
  rw [derivedLowerShriekCompactificationIso_self] at h
  exact Iso.ext (Iso.inv_ext (congrArg Iso.hom h))

section Cube

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) [CompactSpace Y'] [QuasiSeparatedSpace Y'] [IsSeparated f']
  [LocallyOfFiniteType f'] [QuasiCompact f']

/-- On `D⁺_tors`, the base change map of a cube of compactifications is the base change map through
the base change of the compactification, followed by the canonical comparison of the two
compactifications of `f'`. -/
theorem derivedLowerShriekBaseChangeCube_app_eq (j : CompactificationOf (Over.mk f))
    (j' : CompactificationOf (Over.mk f')) (φ : j'.space ⟶ j.space)
    (hc : IsPullback g' j'.immersion j.immersion φ) (w : j'.toBase ≫ g = φ ≫ j.toBase)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hK : isTorsionPlus.{u, 0} Λ X K) :
    (derivedLowerShriekBaseChangeCube Λ j j' φ hc w).app K =
      (derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K ≫
        (derivedLowerShriekCompactificationIso f' (j.baseChange sq) j' Λ).hom.app
          ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K,
            isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ g' K hK⟩ := by
  let κ := CompactificationOf.toBaseChange sq j j' φ hc.w.symm w
  have N := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_naturality Λ (𝟙 j) κ φ
    (pullback.fst j.toBase g) hc (j.isPullback_baseChange sq)
    ((CompactificationOf.toBaseChange_map_fst sq j j' φ hc.w.symm w).trans
      (Category.comp_id _).symm) w pullback.condition.symm) K
  have h1 : (derivedLowerShriekHom Λ (𝟙 j)).app K = 𝟙 _ := by
    simpa using congrArg (fun e ↦ e.hom.app (⟨K, hK⟩ : (isTorsionPlus.{u, 0} Λ X).FullSubcategory))
      (derivedLowerShriekHomIso_id Λ j)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, h1,
    CategoryTheory.Functor.map_id] at N
  refine ((Category.id_comp _).symm.trans N).trans ?_
  rw [derivedLowerShriekCompactificationIso_of_hom f' Λ κ]
  rfl

omit [CompactSpace Y'] [QuasiSeparatedSpace Y'] [IsSeparated f'] [LocallyOfFiniteType f']
  [QuasiCompact f'] in
/-- The base change maps of two compactifications of `f` commute with the maps `Rf_!` induced by a
morphism `ψ` of compactifications and by its base change. -/
lemma derivedLowerShriekBaseChange_hom_app {j₁ j₂ : CompactificationOf (Over.mk f)}
    (ψ : j₁ ⟶ j₂) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map ((derivedLowerShriekHom Λ ψ).app K) ≫
        (derivedLowerShriekBaseChange.{u, 0} Λ sq j₁).app K =
      (derivedLowerShriekBaseChange.{u, 0} Λ sq j₂).app K ≫
        (derivedLowerShriekHom Λ (CompactificationOf.baseChangeHom sq ψ)).app
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K) := by
  have N := NatTrans.congr_app (derivedLowerShriekBaseChangeCube_naturality Λ ψ
    (CompactificationOf.baseChangeHom sq ψ) (pullback.fst j₁.toBase g) (pullback.fst j₂.toBase g)
    (j₁.isPullback_baseChange sq) (j₂.isPullback_baseChange sq)
    (CompactificationOf.baseChangeHom_map_fst sq ψ) pullback.condition.symm
    pullback.condition.symm) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at N
  exact N

/-- The base change maps of `Rf_!` do not depend on the compactification: for two compactifications
`j₁` and `j₂` of `f`, the base change maps correspond under the canonical comparisons for `f` and
for `f'`. -/
theorem derivedLowerShriekBaseChange_compactificationIso [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j₁ j₂ : CompactificationOf (Over.mk f))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hK : isTorsionPlus.{u, 0} Λ X K) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
        ((derivedLowerShriekCompactificationIso f j₁ j₂ Λ).hom.app ⟨K, hK⟩) ≫
      (derivedLowerShriekBaseChange.{u, 0} Λ sq j₂).app K =
    (derivedLowerShriekBaseChange.{u, 0} Λ sq j₁).app K ≫
      (derivedLowerShriekCompactificationIso f' (j₁.baseChange sq) (j₂.baseChange sq) Λ).hom.app
        ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K,
          isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ g' K hK⟩ := by
  let l := IsCofiltered.min j₁ j₂
  let ψ₁ : l ⟶ j₁ := IsCofiltered.minToLeft j₁ j₂
  let ψ₂ : l ⟶ j₂ := IsCofiltered.minToRight j₁ j₂
  have e1 := derivedLowerShriekBaseChange_hom_app Λ sq ψ₁ K
  have e2 := derivedLowerShriekBaseChange_hom_app Λ sq ψ₂ K
  have c1 := derivedLowerShriekCompactificationIso_of_hom f Λ ψ₁
  have c2 := derivedLowerShriekCompactificationIso_of_hom f Λ ψ₂
  have c1' :=
    derivedLowerShriekCompactificationIso_of_hom f' Λ (CompactificationOf.baseChangeHom sq ψ₁)
  have c2' :=
    derivedLowerShriekCompactificationIso_of_hom f' Λ (CompactificationOf.baseChangeHom sq ψ₂)
  rw [← derivedLowerShriekCompactificationIso_trans f Λ j₁ l j₂,
    ← derivedLowerShriekCompactificationIso_symm Λ f j₂ l,
    ← derivedLowerShriekCompactificationIso_trans f' Λ (j₁.baseChange sq) (l.baseChange sq)
      (j₂.baseChange sq),
    ← derivedLowerShriekCompactificationIso_symm Λ f' (j₂.baseChange sq) (l.baseChange sq),
    c1, c2, c1', c2']
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    derivedLowerShriekHomIso_hom_app]
  have h2 : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
        ((derivedLowerShriekHomIso Λ ψ₂).inv.app ⟨K, hK⟩) ≫
        (derivedLowerShriekBaseChange.{u, 0} Λ sq j₂).app K =
      (derivedLowerShriekBaseChange.{u, 0} Λ sq l).app K ≫
        (derivedLowerShriekHomIso Λ (CompactificationOf.baseChangeHom sq ψ₂)).inv.app
          ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K,
            isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ g' K hK⟩ := by
    rw [← cancel_epi ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
      ((derivedLowerShriekHomIso Λ ψ₂).hom.app ⟨K, hK⟩)), ← Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      derivedLowerShriekHomIso_hom_app, ← Category.assoc, e2, Category.assoc]
    have hi := Iso.hom_inv_id_app
      (derivedLowerShriekHomIso Λ (CompactificationOf.baseChangeHom sq ψ₂))
      ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K,
        isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ g' K hK⟩
    rw [derivedLowerShriekHomIso_hom_app] at hi
    rw [hi]
    exact (Category.comp_id _).symm
  rw [h2, ← Category.assoc, e1, Category.assoc]

end Cube

end Stacks.EtaleCohomology
