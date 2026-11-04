module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CartesianRestrictModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LocallyQuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatDescent

/-!
# Cartesian over the flat arrows between affine objects gives `LQCoh^fbc`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `F` a presheaf of
`𝒪_𝒳`-modules which is a sheaf for the étale topology. Suppose `F` is cartesian over every arrow
`x₁ ⟶ x₂` lying over a **flat** morphism of affine schemes: `𝒪(x₁) ⊗_{𝒪(x₂)} F(x₂) ⟶ F(x₁)` is
bijective. This file proves that `F` lies in `LQCoh^fbc(𝒪_𝒳)`, at module universe `u`, with the
flat base change property of **Stacks 0762** read with the pullback of sheaves.

* Local quasi-coherence (**Stacks 06WJ**): étale morphisms are flat, so the restriction of `F` to
  the affine subcategory satisfies condition (1) of **Stacks 0H0F**, which makes every
  restriction `x^*F|_{U_ét}` quasi-coherent
  (`AlgebraicGeometry.Stack.isCartesianOnAffines_restrictModuleToSmallEtale`,
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines`).
* The flat base change property: the comparison-map theorem of
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CartesianRestrictModulePullbackComparison`
  (`AlgebraicGeometry.Stack.isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_cartesian`)
  uses the cartesian property only along the arrows `(etaleIndex x).map a ≫ φ'` of `𝒳` which
  compute the comparison of Stacks 06W2 over an affine étale object; when `φ` lies over a flat
  morphism these arrows lie over flat morphisms too — the composite of an étale morphism and a
  base change of the morphism below `φ`
  (`AlgebraicGeometry.Stack.exists_restrictionPushforwardComparison_app_eq_of_flat`,
  `AlgebraicGeometry.Stack.flat_etaleIndex_map_comp`). The three statements of that file
  consuming the cartesian property are restated here over the cartesian property along flat
  arrows; the lemmas they rest on are reused unchanged.

## Main results

* `isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_flatCartesian`:
  the comparison map of Stacks 06WC along a flat arrow is locally bijective.
* `isLocallyQuasicoherent_of_bijective_restrictionBaseChange_of_flat`:
  local quasi-coherence.
* `isLocallyQuasicoherentWithSheafFlatBaseChange_of_bijective_restrictionBaseChange_of_flat`:
  membership in `LQCoh^fbc(𝒪_𝒳)`.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y : 𝒳} (φ : x ⟶ y)
  (F : PresheafOfModules.{max u m} (ringStructureSheafCore B S hS p hp τ hτ).obj)

/-- **The arrow computing the comparison of Stacks 06W2 lies over a flat morphism** when `φ`
does: it lies, up to the counits of the localization equivalences of Stacks 06W0, over the
projection `U ×_V T ⟶ T`, a base change of the morphism below `φ`. This is
`AlgebraicGeometry.Stack.exists_restrictionPushforwardComparison_app_eq` together with that
flatness. -/
theorem exists_restrictionPushforwardComparison_app_eq_of_flat
    (hφ : Flat (B.inclusion.map (p.map φ).left))
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :
    ∃ φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T,
      (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf).app (op T) =
          F.presheaf.map φ'.op ∧
        (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op ∧
        Flat (B.inclusion.map (p.map φ').left) := by
  obtain ⟨φ', hfac, hproj⟩ := exists_restrictionComparisonLift B E h S hS p hp φ T
  refine ⟨φ', restrictionPushforwardComparison_app B E h S hS p hp φ F.presheaf T φ' hfac hproj,
    restrictionPushforwardComparison_app B E h S hS p hp φ _ T φ' hfac hproj, ?_⟩
  let : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
    isEquivalence_overPost B S hS p hp x
  let : (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
    isEquivalence_overPost B S hS p hp y
  have key : ∀ {X Y Z W : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ W) (c : X ⟶ Z) (d : Z ⟶ W)
      [IsIso b] [IsIso c], a ≫ b = c ≫ d → Flat d → Flat a := by
    intro X Y Z W a b c d _ _ hsq hd
    have ha : a = c ≫ d ≫ inv b := by
      rw [← Category.assoc, ← hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [ha]
    infer_instance
  have hpb := (IsPullback.of_hasPullback T.obj.hom
    (smallEtaleBaseMorphism B E h S hS p φ)).map E.inclusion
  have hfst : Flat (E.inclusion.map (pullback.fst T.obj.hom
      (smallEtaleBaseMorphism B E h S hS p φ))) :=
    MorphismProperty.of_isPullback (P := @Flat) hpb.flip hφ
  have hiso : ∀ (z : 𝒳) [(Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).IsEquivalence]
      (A : Over ((p ⋙ Over.forget (B.obj hS)).obj z)),
      IsIso (B.inclusion.map ((Over.post (X := z) (p ⋙ Over.forget (B.obj hS))
        ).asEquivalence.counit.app A).left) := fun z _ A => by
    show IsIso ((Over.forget _ ⋙ B.inclusion).map _)
    infer_instance
  exact @key _ _ _ _ _ _ _ _ (hiso y _) (hiso x _) hproj hfst

/-- An arrow of `𝒳` out of the image of an étale arrow followed by a flat one lies over a flat
morphism of schemes. -/
theorem flat_etaleIndex_map_comp
    {T T' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : T ⟶ T') {z : 𝒳} (ψ : (etaleIndex B E h S hS p hp x).obj T' ⟶ z)
    (hψ : Flat (B.inclusion.map (p.map ψ).left)) :
    Flat (B.inclusion.map (p.map ((etaleIndex B E h S hS p hp x).map a ≫ ψ)).left) := by
  have : Etale (B.inclusion.map (p.map ((etaleIndex B E h S hS p hp x).map a)).left) :=
    etale_etaleIndex_map B E h S hS p hp x a
  rw [Functor.map_comp, Over.comp_left, Functor.map_comp]
  infer_instance

/-- The cartesian property along flat arrows gives bijectivity along the arrow
`(etaleIndex x).map a ≫ φ'` between the images of affine étale objects. -/
private theorem bijective_restrictionBaseChange_etaleIndex_map_comp
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
      _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
        _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
          Flat (B.inclusion.map (p.map e).left) →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
            (R := (structureSheaf B S hS p hp τ hτ).obj)
            (commRestrictModule B S hS p hp τ hτ F) e.op))
    {T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)}
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj y).left.1 (contains_base B E h S hS p y)).obj T))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (hW : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj x).left.1 (contains_base B E h S hS p x)).obj W))
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hφ' : Flat (B.inclusion.map (p.map φ').left)) :
    Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
      (R := (structureSheaf B S hS p hp τ hτ).obj)
      (commRestrictModule B S hS p hp τ hτ F)
      ((etaleIndex B E h S hS p hp x).map a ≫ φ').op) :=
  hcart _ (isAffine_etaleIndex_obj B E h S hS p hp x W hW)
    (isAffine_etaleIndex_obj B E h S hS p hp y T hT)
    (flat_etaleIndex_map_comp B E h S hS p hp a φ' hφ')

section FlatCartesian

/-- **The affine case, surjectivity, over the cartesian property along flat arrows.** Over an
affine object `W` mapping to the base change of an affine object, every section of `F|_{U_ét}` is
a value of the comparison map along a flat arrow `φ`. -/
theorem exists_restrictModulePullbackComparisonUnivLE_app_eq_of_flatCartesian
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
      _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
        _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
          Flat (B.inclusion.map (p.map e).left) →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
            (R := (structureSheaf B S hS p hp τ hτ).obj)
            (commRestrictModule B S hS p hp τ hτ F) e.op))
    (hφ : Flat (B.inclusion.map (p.map φ).left))
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj y).left.1 (contains_base B E h S hS p y)).obj T))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (hW : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj x).left.1 (contains_base B E h S hS p x)).obj W))
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (s : (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).obj (op W)) :
    ∃ t, (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app (op W) t = s := by
  obtain ⟨φ', hF, hR, hφ'⟩ := exists_restrictionPushforwardComparison_app_eq_of_flat
    B E h S hS p hp τ hτ φ F hφ T
  obtain ⟨ζ, hζ⟩ := (bijective_restrictionBaseChange_etaleIndex_map_comp B E h S hS p hp τ hτ φ F
    hcart hT hW a φ' hφ').2 s
  exact ⟨pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a φ' hR ζ,
    (restrictModulePullbackComparisonUnivLE_app_pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a
      φ' hF hR ζ).trans hζ⟩

/-- **The affine case, injectivity, over the cartesian property along flat arrows.** Over an
affine object `W` mapping to the base change of an affine object `T`, a section in the span at
`(T, a)` killed by the comparison map along a flat arrow `φ` is zero. -/
theorem eq_zero_of_mem_pullbackUnitSpan_of_flatCartesian
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
      _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
        _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
          Flat (B.inclusion.map (p.map e).left) →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
            (R := (structureSheaf B S hS p hp τ hτ).obj)
            (commRestrictModule B S hS p hp τ hτ F) e.op))
    (hφ : Flat (B.inclusion.map (p.map φ).left))
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj y).left.1 (contains_base B E h S hS p y)).obj T))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (hW : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj x).left.1 (contains_base B E h S hS p x)).obj W))
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    {q : ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W)}
    (hq : q ∈ pullbackUnitSpan B E h S hS p hp τ hτ φ F T a)
    (h0 : (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app (op W) q = 0) :
    q = 0 := by
  obtain ⟨φ', hF, hR, hφ'⟩ := exists_restrictionPushforwardComparison_app_eq_of_flat
    B E h S hS p hp τ hτ φ F hφ T
  obtain ⟨ζ, rfl⟩ := exists_pullbackUnitTensorMap_eq_of_mem_pullbackUnitSpan B E h S hS p hp τ hτ
    φ F T a φ' hR hq
  rw [restrictModulePullbackComparisonUnivLE_app_pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a
    φ' hF hR ζ] at h0
  rw [(bijective_restrictionBaseChange_etaleIndex_map_comp B E h S hS p hp τ hτ φ F hcart hT hW a
    φ' hφ').1 (h0.trans (map_zero _).symm)]
  exact map_zero _

/-- **Local injectivity of the comparison map of Stacks 06WC** along a flat arrow `φ`, for a
module cartesian over the flat arrows between affine objects. -/
theorem isLocallyInjective_restrictModulePullbackComparisonUnivLE_of_flatCartesian
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
      _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
        _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
          Flat (B.inclusion.map (p.map e).left) →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
            (R := (structureSheaf B S hS p hp τ hτ).obj)
            (commRestrictModule B S hS p hp τ hτ F) e.op))
    (hφ : Flat (B.inclusion.map (p.map φ).left)) :
    Presheaf.IsLocallyInjective
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F)) := by
  constructor
  intro W' x₁ x₂ hx
  let P := (PresheafOfModules.pullback.{max u m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
      (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)
  let c := restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F
  let y₁ : P.obj W' := x₁
  let y₂ : P.obj W' := x₂
  have hx' : c.app W' y₁ = c.app W' y₂ := hx
  have hq0 : c.app W' (y₁ - y₂) = 0 := by
    rw [(c.app W').hom.map_sub, hx', sub_self]
  refine GrothendieckTopology.transitive _
    (pullbackUnitSpanSieve_mem B E h S hS p hp τ hτ φ F (W := W'.unop) (y₁ - y₂)) _ ?_
  rintro W'' g ⟨T, hT, a, hmem⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (SmallEtale.mem_topology_sieve₀_affineImageCover E _ _ W'')
  rintro Z k ⟨_, j, _, ⟨i⟩, rfl⟩
  have key : P.map ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op y₁ =
      P.map ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op y₂ := by
    have hm : P.map ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op (y₁ - y₂) ∈
        pullbackUnitSpan B E h S hS p hp τ hτ φ F T
          ((SmallEtale.affineImageCover E _ _ W'').f i ≫ a) := by
      rw [op_comp, PresheafOfModules.map_comp_apply]
      exact map_mem_pullbackUnitSpan B E h S hS p hp τ hτ φ F T a _ hmem
    have hc : c.app (op ((SmallEtale.affineImageCover E _ _ W'').X i))
        (P.map ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op (y₁ - y₂)) = 0 := by
      rw [PresheafOfModules.naturality_apply, hq0, map_zero]
      rfl
    have h0 := eq_zero_of_mem_pullbackUnitSpan_of_flatCartesian B E h S hS p hp τ hτ φ F hcart
      hφ T hT (SmallEtale.isAffine_affineImageCover_X E _ _ W'' i) _ hm hc
    rw [(P.map ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op).hom.map_sub] at h0
    exact sub_eq_zero.1 h0
  show P.map ((j ≫ (SmallEtale.affineImageCover E _ _ W'').f i) ≫ g).op y₁ =
    P.map ((j ≫ (SmallEtale.affineImageCover E _ _ W'').f i) ≫ g).op y₂
  rw [Category.assoc, op_comp, PresheafOfModules.map_comp_apply,
    PresheafOfModules.map_comp_apply, key]

/-- **Local surjectivity of the comparison map of Stacks 06WC** along a flat arrow `φ`, for a
module cartesian over the flat arrows between affine objects. -/
theorem isLocallySurjective_restrictModulePullbackComparisonUnivLE_of_flatCartesian
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
      _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
        _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
          Flat (B.inclusion.map (p.map e).left) →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
            (R := (structureSheaf B S hS p hp τ hτ).obj)
            (commRestrictModule B S hS p hp τ hτ F) e.op))
    (hφ : Flat (B.inclusion.map (p.map φ).left)) :
    Presheaf.IsLocallySurjective
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      ((PresheafOfModules.toPresheaf _).map
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F)) := by
  constructor
  intro W' s
  let P := (PresheafOfModules.pullback.{max u m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
      (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)
  let Q := restrictModuleToSmallEtale B E h S hS p hp x τ hτ F
  refine GrothendieckTopology.transitive _
    (pullbackUnitSpanSieve_mem B E h S hS p hp τ hτ φ F (0 : P.obj (op W'))) _ ?_
  rintro W'' g ⟨T, hT, a, -⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (SmallEtale.mem_topology_sieve₀_affineImageCover E _ _ W'')
  rintro Z k ⟨_, j, _, ⟨i⟩, rfl⟩
  let s' : Q.obj (op W') := s
  obtain ⟨t, ht⟩ := exists_restrictModulePullbackComparisonUnivLE_app_eq_of_flatCartesian
    B E h S hS p hp τ hτ φ F hcart hφ T hT (SmallEtale.isAffine_affineImageCover_X E _ _ W'' i)
    ((SmallEtale.affineImageCover E _ _ W'').f i ≫ a)
    (Q.map ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op s')
  refine ⟨P.map j.op t, ?_⟩
  show (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app (op Z)
    (P.map j.op t) = Q.map ((j ≫ (SmallEtale.affineImageCover E _ _ W'').f i) ≫ g).op s'
  rw [PresheafOfModules.naturality_apply, ht, Category.assoc]
  exact (PresheafOfModules.map_comp_apply Q
    ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op j.op s').symm

/-- **The comparison map of Stacks 06WC of a module cartesian over the flat arrows between affine
objects is locally bijective** along every arrow `φ` of `𝒳` lying over a flat morphism: it
becomes an isomorphism after sheafification for the small étale topology. -/
theorem isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_flatCartesian
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
      _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
        _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
          Flat (B.inclusion.map (p.map e).left) →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
            (R := (structureSheaf B S hS p hp τ hτ).obj)
            (commRestrictModule B S hS p hp τ hτ F) e.op))
    (hφ : Flat (B.inclusion.map (p.map φ).left)) :
    IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE B E h S hS p hp τ hτ φ F :=
  ⟨isLocallyInjective_restrictModulePullbackComparisonUnivLE_of_flatCartesian
      B E h S hS p hp τ hτ φ F hcart hφ,
    isLocallySurjective_restrictModulePullbackComparisonUnivLE_of_flatCartesian
      B E h S hS p hp τ hτ φ F hcart hφ⟩

end FlatCartesian


section Assembly

variable {B E h S hS p hp} in
/-- **Cartesian over the flat arrows between affine objects gives local quasi-coherence.** An
étale sheaf of modules on `𝒳` whose base-change comparisons `𝒪(x₁) ⊗_{𝒪(x₂)} F(x₂) ⟶ F(x₁)` are
bijective along the arrows lying over flat morphisms of affine schemes is locally quasi-coherent
(Stacks 06WJ): étale morphisms are flat, so its restriction to the affine subcategory satisfies
condition (1) of Stacks 0H0F, and condition (1) makes every restriction `x^*F|_{U_ét}`
quasi-coherent. -/
theorem isLocallyQuasicoherent_of_bijective_restrictionBaseChange_of_flat
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
      _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
        _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
          Flat (B.inclusion.map (p.map e).left) →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
            (R := (structureSheaf B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)).obj)
            (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F)
            e.op)) :
    IsLocallyQuasicoherent B E h S hS p hp F := by
  let G : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) :=
    ⟨F, hF⟩
  have hEt : IsEtaleCartesian B S hS p
      ((PresheafOfModules.pushforward₀ (AffineCategory.inclusion B S hS p) _).obj G.val) := by
    intro y y' f hf
    have hf' : Etale (B.inclusion.map (p.map f.hom).left) := hf
    exact (ConcreteCategory.isIso_iff_bijective
      (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
        (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
        (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F)
        f.hom.op)).2 (hcart f.hom y.property y'.property inferInstance)
  exact ⟨hF, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF,
    SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines E _ _ _
      (isCartesianOnAffines_restrictModuleToSmallEtale B E h S hS p hp G _ (Iso.refl _) hEt x)⟩⟩

variable {B E h S hS p hp} in
/-- **Cartesian over the flat arrows between affine objects gives `LQCoh^fbc(𝒪_𝒳)`**, at module
universe `u`, with the flat base change property of Stacks 0762 read with the pullback of
sheaves: local quasi-coherence is
`isLocallyQuasicoherent_of_bijective_restrictionBaseChange_of_flat`, and along every flat arrow
the comparison of Stacks 06WC is locally bijective by
`isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_flatCartesian`. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_of_bijective_restrictionBaseChange_of_flat
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
      _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
        _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
          Flat (B.inclusion.map (p.map e).left) →
          Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u}
            (R := (structureSheaf B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)).obj)
            (commRestrictModule B S hS p hp (etaleTopology B) (etaleTopology_le_topology B) F)
            e.op)) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp F :=
  ⟨isLocallyQuasicoherent_of_bijective_restrictionBaseChange_of_flat F hF hcart,
    fun φ hφ =>
      isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_flatCartesian.{u, v, w, u}
      B E h S hS p hp (etaleTopology B) (etaleTopology_le_topology B) φ F hcart hφ⟩

end Assembly

end AlgebraicGeometry.Stack
