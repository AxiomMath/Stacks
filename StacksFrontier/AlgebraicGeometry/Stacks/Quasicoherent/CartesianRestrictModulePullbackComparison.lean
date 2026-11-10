module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineImageCover
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestrictionComposition

/-!
# The comparison map of Stacks 06WC of a module cartesian over the affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `φ : x ⟶ y` an arrow of `𝒳` lying
over `f : U ⟶ V`, and `F` a presheaf of `𝒪_𝒳`-modules. The comparison map of Stacks 06WC is
`c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}`, where `f_{small}^*` is the pullback of presheaves of
modules (`AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE`). This file proves that
**`c_φ` is locally bijective for the small étale topology of `U` — an isomorphism after
sheafification — whenever `F` is cartesian over the arrows between objects lying over affine
schemes**, that is, `𝒪(x₁) ⊗_{𝒪(x₂)} F(x₂) ⟶ F(x₁)` is bijective for every arrow `x₁ ⟶ x₂` of `𝒳`
over a morphism of affine schemes. No flatness of `f` is needed, and the module universe is free.
A quasi-coherent module on `(𝒳_{fppf}, 𝒪_𝒳)` is cartesian in this sense
(`AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`),
which is how
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSheafFlatBaseChange` obtains
clause (b) of the forward direction of Stacks 06WK.

## The argument

Mathlib's pullback of presheaves of modules is an abstract left adjoint; its sections are not
described. Two facts about it suffice:

* it is **generated** by the restrictions `a^*(η(n))` of the unit sections `η(n)`, `n ∈ F|_V(T)`,
  `a : W ⟶ f^{-1}T` (`PresheafOfModules.generatedSubmodule_unit_eq_top`);
* the comparison map sends `a^*(η(n))` to the restriction of `n` along the arrow
  `(etaleIndex x).map a ≫ φ'` of `𝒳` that computes the comparison of Stacks 06W2
  (`AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE_app_pullbackUnitRestriction`).

For `T` affine, the `𝒪_U(W)`-span of the `a^*(η(n))` is the image of an additive map
`𝒪_𝒳(x_W) ⊗_{𝒪_𝒳(y_T)} F(y_T) ⟶ (f^*F|_V)(W)` (`AlgebraicGeometry.Stack.pullbackUnitTensorMap`)
whose composite with `c_φ` is the base-change comparison of `F` along that arrow of `𝒳`. If `W` is
affine too, the hypothesis makes the latter bijective; so over affine `W` the comparison map is
surjective onto `F|_U(W)` and injective on that span. It remains to see that every section of the
pullback lies in such a span locally on `U_ét`: the generators do, after refining `T` by an affine
étale covering and pulling the covering back along `f^{-1}` (which preserves coverings), and two
spans at `(T₁, a₁)` and `(T₂, a₂)` lie locally in one at an affine refinement of `T₁ × T₂`,
`f^{-1}` preserving products. Affine objects cover `U_ét`
(`AlgebraicGeometry.SmallEtale.mem_topology_sieve₀_affineImageCover`), which gives local
surjectivity and local injectivity.

## Main results

* `AlgebraicGeometry.Stack.isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_cartesian`:
  the comparison map of Stacks 06WC of a module cartesian over the affine objects is locally
  bijective, along every arrow of `𝒳`.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
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

/-- The comparison map of Stacks 06WC sends a unit section `η(n)` to the comparison of Stacks 06W2
applied to `n`: it is the adjoint transpose of the latter. -/
theorem restrictModulePullbackComparisonUnivLE_app_unit_apply
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    (n : (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).obj (op T)) :
    (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app
        (op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T))
        (((PresheafOfModules.pullbackPushforwardAdjunction.{max u m}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).unit.app
            (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).app (op T) n) =
      (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F).app (op T) n := by
  have key := restrictModulePullbackComparisonUnivLE_adjunct B E h S hS p hp φ τ hτ F
  rw [Adjunction.homEquiv_unit] at key
  rw [← key]
  rfl

/-- The arrow of `𝒳` computing the comparison of Stacks 06W2 at an object `T` of the small étale
site of the scheme below `y`, for every presheaf on `𝒳` at once. -/
theorem exists_restrictionPushforwardComparison_app_eq
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :
    ∃ φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T,
      (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf).app (op T) =
          F.presheaf.map φ'.op ∧
        (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op := by
  obtain ⟨φ', hfac, hproj⟩ := exists_restrictionComparisonLift B E h S hS p hp φ T
  exact ⟨φ', restrictionPushforwardComparison_app B E h S hS p hp φ F.presheaf T φ' hfac hproj,
    restrictionPushforwardComparison_app B E h S hS p hp φ _ T φ' hfac hproj⟩

/-- **The map of rings below a composite of the comparison and a restriction.** For `a : W ⟶ b(T)`
in the small étale site of the scheme below `x`, the ring map
`𝒪_V(T) ⟶ 𝒪_U(b T) ⟶ 𝒪_U(W)` read through the identifications of Stacks 06W9 is the restriction
of the structure sheaf of `𝒳` along the arrow `(etaleIndex x).map a ≫ φ'` computing the
comparison. -/
theorem localStructurePresheafIso_inv_comp_smallEtaleStructureComparison
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hR : (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op) :
    (localStructurePresheafIso B E h S hS p hp y τ hτ).inv.app (op T) ≫
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app (op T) ≫
          (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.map
            a.op =
      (ringStructureSheafCore B S hS p hp τ hτ).obj.map
          ((etaleIndex B E h S hS p hp x).map a ≫ φ').op ≫
        (localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W) := by
  have hnat := (localStructurePresheafIso B E h S hS p hp x τ hτ).inv.naturality a.op
  simp only [smallEtaleStructureComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, hR]
  exact (congrArg (fun k => (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op ≫ k)
    hnat.symm).trans (by rw [op_comp, Functor.map_comp, Category.assoc]; rfl)

/-- **The restriction of a unit section of the pullback.** For `a : W ⟶ b(T)` in the small étale
site of the scheme below `x` and `n` a section over `T` of the restriction at `y`, the section
`a^*(η(n))` over `W` of the Stacks 06WC pullback of that restriction. -/
noncomputable def pullbackUnitRestriction
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (n : (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).obj (op T)) :
    ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W) :=
  ((PresheafOfModules.pullback.{max u m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
      (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map a.op
    (((PresheafOfModules.pullbackPushforwardAdjunction.{max u m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).unit.app
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).app (op T) n)

/-- The restrictions of unit sections are semilinear over the ring map
`𝒪_V(T) ⟶ 𝒪_U(f^{-1}T) ⟶ 𝒪_U(W)`. -/
theorem pullbackUnitRestriction_smul
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (t : (SmallEtale.structureSheaf E (p.obj y).left.1 (contains_base B E h S hS p y)).obj.obj
      (op T))
    (n : (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).obj (op T)) :
    pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a (t • n) =
      ((smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app (op T) ≫
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.map
          a.op).hom t • pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n := by
  unfold pullbackUnitRestriction
  rw [(((PresheafOfModules.pullbackPushforwardAdjunction.{max u m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).unit.app
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).app (op T)).hom.map_smul]
  exact PresheafOfModules.map_smul _ _ _ _

/-- The comparison map sends `a^*(η(n))` to the restriction of `n` along the arrow
`(etaleIndex x).map a ≫ φ'` of `𝒳`. -/
theorem restrictModulePullbackComparisonUnivLE_app_pullbackUnitRestriction
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hF : (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf).app (op T) =
          F.presheaf.map φ'.op)
    (n : (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).obj (op T)) :
    (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app (op W)
        (pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n) =
      F.map ((etaleIndex B E h S hS p hp x).map a ≫ φ').op n := by
  refine (PresheafOfModules.naturality_apply
    (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F) a.op _).trans ?_
  rw [restrictModulePullbackComparisonUnivLE_app_unit_apply,
    restrictModulePushforwardComparison_app, hF, op_comp, PresheafOfModules.map_comp]
  rfl

/-- The ring identity behind `pullbackUnitRestriction_smul`, read on elements. -/
theorem smallEtaleStructureComparison_comp_map_localStructurePresheafIso_inv_apply
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hR : (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op)
    (t : (ringStructureSheafCore B S hS p hp τ hτ).obj.obj
      (op ((etaleIndex B E h S hS p hp y).obj T))) :
    ((smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app (op T) ≫
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.map
          a.op).hom ((localStructurePresheafIso B E h S hS p hp y τ hτ).inv.app (op T) t) =
      ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom
        (((ringStructureSheafCore B S hS p hp τ hτ).obj.map
          ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom t) := by
  have hA := localStructurePresheafIso_inv_comp_smallEtaleStructureComparison B E h S hS p hp τ hτ
    φ T a φ' hR
  have := congrArg (fun k => k.hom t) hA
  simpa only [RingCat.hom_comp, RingHom.comp_apply] using this

/-- A presheaf of modules over the structure sheaf of `𝒳`, read over its commutative spelling
`AlgebraicGeometry.Stack.structureSheaf`, so that its sections are modules over commutative
rings for instance search. -/
abbrev commRestrictModule :
    PresheafOfModules.{max u m}
      ((structureSheaf B S hS p hp τ hτ).obj ⋙ forget₂ CommRingCat RingCat) := F

/-- A scalar of the structure sheaf of `𝒳` acts on the restriction of Stacks 06WJ through the
identification of Stacks 06W9. -/
private theorem localStructurePresheafIso_inv_smul_aux (z : 𝒳)
    {W : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z)}
    (r : (structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp z).obj W)))
    (n : (commRestrictModule B S hS p hp τ hτ F).obj
      (op ((etaleIndex B E h S hS p hp z).obj W))) :
    @Eq ((restrictModuleToSmallEtale B E h S hS p hp z τ hτ F).obj (op W))
      (((localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app (op W)).hom r •
        @id ((restrictModuleToSmallEtale B E h S hS p hp z τ hτ F).obj (op W)) n) (r • n) := by
  change (((localStructurePresheafIso B E h S hS p hp z τ hτ).hom.app (op W)).hom
      (((localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app (op W)).hom r)) •
    @id (F.obj (op ((etaleIndex B E h S hS p hp z).obj W))) n = _
  have key : ((localStructurePresheafIso B E h S hS p hp z τ hτ).hom.app (op W)).hom
      (((localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app (op W)).hom r) = r :=
    congrArg (fun k => k.hom r)
      (Iso.inv_hom_id_app (localStructurePresheafIso B E h S hS p hp z τ hτ) (op W))
  rw [key]
  rfl

/-- The restrictions of unit sections are additive. -/
theorem pullbackUnitRestriction_add
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (n n' : (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).obj (op T)) :
    pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a (n + n') =
      pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n +
        pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n' := by
  unfold pullbackUnitRestriction
  rw [map_add]
  exact map_add _ _ _

/-- `pullbackUnitRestriction_smul` with the scalar taken in the structure sheaf of `𝒳`. -/
theorem pullbackUnitRestriction_smul_comm
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hR : (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op)
    (t : (structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp y).obj T)))
    (n : (commRestrictModule B S hS p hp τ hτ F).obj
      (op ((etaleIndex B E h S hS p hp y).obj T))) :
    pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a (t • n) =
      ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom
          (((structureSheaf B S hS p hp τ hτ).obj.map
            ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom t) •
        pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n := by
  have ht : (t • n : (commRestrictModule B S hS p hp τ hτ F).obj
      (op ((etaleIndex B E h S hS p hp y).obj T))) =
      (((localStructurePresheafIso B E h S hS p hp y τ hτ).inv.app (op T)).hom t •
        @id ((restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).obj (op T)) n) :=
    (localStructurePresheafIso_inv_smul_aux B E h S hS p hp τ hτ F y t n).symm
  rw [ht]
  exact (pullbackUnitRestriction_smul B E h S hS p hp τ hτ φ F T a _ _).trans
    (congrArg (fun c => c • pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n)
      (smallEtaleStructureComparison_comp_map_localStructurePresheafIso_inv_apply
        B E h S hS p hp τ hτ φ T a φ' hR t))

/-- **The base change of the restriction of unit sections.** The additive map
`𝒪_𝒳(x_W) ⊗_{𝒪_𝒳(y_T)} F(y_T) ⟶ (a_{small}^* F|_{V_ét})(W)` sending `r ⊗ n` to `r · a^*(η(n))`,
where `x_W ⟶ y_T` is the arrow `(etaleIndex x).map a ≫ φ'` computing the comparison and `r` acts
through the identification of Stacks 06W9. -/
noncomputable def pullbackUnitTensorMap
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hR : (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op) :
    letI : Module ((structureSheaf B S hS p hp τ hτ).obj.obj
        (op ((etaleIndex B E h S hS p hp y).obj T)))
        ((structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp x).obj W))) :=
      Module.compHom _ ((structureSheaf B S hS p hp τ hτ).obj.map
        ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom
    TensorProduct ((structureSheaf B S hS p hp τ hτ).obj.obj
        (op ((etaleIndex B E h S hS p hp y).obj T)))
        ((structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp x).obj W)))
        ((commRestrictModule B S hS p hp τ hτ F).obj (op ((etaleIndex B E h S hS p hp y).obj T)))
        →+
      ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W) :=
  letI : Module ((structureSheaf B S hS p hp τ hτ).obj.obj
      (op ((etaleIndex B E h S hS p hp y).obj T)))
      ((structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp x).obj W))) :=
    Module.compHom _ ((structureSheaf B S hS p hp τ hτ).obj.map
      ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun r => AddMonoidHom.mk'
        (fun n => ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom r •
          pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n)
        (fun n n' =>
          (congrArg (fun z => ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app
            (op W)).hom r • z)
            (pullbackUnitRestriction_add B E h S hS p hp τ hτ φ F T a n n')).trans
            (smul_add _ _ _)))
      (fun r r' => AddMonoidHom.ext fun n =>
        (congrArg (fun c => c • pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n)
          (map_add ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom
            r r')).trans
          (add_smul _ _ _)))
    (fun t r n => by
      change ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom
          (((structureSheaf B S hS p hp τ hτ).obj.map
            ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom t * r) •
          pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n =
        ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom r •
          pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a (t • n)
      rw [pullbackUnitRestriction_smul_comm B E h S hS p hp τ hτ φ F T a φ' hR,
        mul_comm (((structureSheaf B S hS p hp τ hτ).obj.map
            ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom t) r]
      refine (congrArg (fun c => c • pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n)
        (map_mul ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom r
          (((structureSheaf B S hS p hp τ hτ).obj.map
            ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom t))).trans ?_
      exact mul_smul _ _ _)

/-- `AlgebraicGeometry.Stack.pullbackUnitTensorMap` on a pure tensor. -/
theorem pullbackUnitTensorMap_tmul
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hR : (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op)
    (r : (structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp x).obj W)))
    (n : (commRestrictModule B S hS p hp τ hτ F).obj
      (op ((etaleIndex B E h S hS p hp y).obj T))) :
    letI : Module ((structureSheaf B S hS p hp τ hτ).obj.obj
        (op ((etaleIndex B E h S hS p hp y).obj T)))
        ((structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp x).obj W))) :=
      Module.compHom _ ((structureSheaf B S hS p hp τ hτ).obj.map
        ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom
    pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a φ' hR (r ⊗ₜ n) =
      ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom r •
        pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n :=
  rfl

/-- A scalar of the structure sheaf of `𝒳` acts on the restriction of Stacks 06WJ through the
identification of Stacks 06W9. -/
theorem localStructurePresheafIso_inv_smul (z : 𝒳)
    {W : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z)}
    (r : (structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp z).obj W)))
    (n : (commRestrictModule B S hS p hp τ hτ F).obj
      (op ((etaleIndex B E h S hS p hp z).obj W))) :
    @Eq ((restrictModuleToSmallEtale B E h S hS p hp z τ hτ F).obj (op W))
      (((localStructurePresheafIso B E h S hS p hp z τ hτ).inv.app (op W)).hom r •
        @id ((restrictModuleToSmallEtale B E h S hS p hp z τ hτ F).obj (op W)) n) (r • n) :=
  localStructurePresheafIso_inv_smul_aux B E h S hS p hp τ hτ F z r n

/-- **The comparison map after the tensor map is the base-change comparison of `F`** along the
arrow `(etaleIndex x).map a ≫ φ'` of `𝒳`. -/
theorem restrictModulePullbackComparisonUnivLE_app_pullbackUnitTensorMap
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hF : (restrictionPushforwardComparison B E h S hS p hp φ F.presheaf).app (op T) =
          F.presheaf.map φ'.op)
    (hR : (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op)
    (ζ : (ModuleCat.extendScalars ((structureSheaf B S hS p hp τ hτ).obj.map
        ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom).obj
        ((commRestrictModule B S hS p hp τ hτ F).obj
          (op ((etaleIndex B E h S hS p hp y).obj T)))) :
    (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app (op W)
        (pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a φ' hR ζ) =
      Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
        (R := (structureSheaf B S hS p hp τ hτ).obj) (commRestrictModule B S hS p hp τ hτ F)
        ((etaleIndex B E h S hS p hp x).map a ≫ φ').op ζ := by
  let : Module ((structureSheaf B S hS p hp τ hτ).obj.obj
      (op ((etaleIndex B E h S hS p hp y).obj T)))
      ((structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp x).obj W))) :=
    Module.compHom _ ((structureSheaf B S hS p hp τ hτ).obj.map
      ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom
  induction ζ using TensorProduct.inductionOn with
  | tmul r n =>
    refine (congrArg _ (pullbackUnitTensorMap_tmul B E h S hS p hp τ hτ φ F T a φ' hR r n)).trans ?_
    refine (((restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app
      (op W)).hom.map_smul _ _).trans ?_
    refine Eq.trans ?_ (Stacks.PresheafOfModules.restrictionBaseChange_tmul.{v, w, u, m}
      (R := (structureSheaf B S hS p hp τ hτ).obj) (commRestrictModule B S hS p hp τ hτ F)
      ((etaleIndex B E h S hS p hp x).map a ≫ φ').op r n).symm
    rw [restrictModulePullbackComparisonUnivLE_app_pullbackUnitRestriction
      B E h S hS p hp τ hτ φ F T a φ' hF n]
    exact localStructurePresheafIso_inv_smul B E h S hS p hp τ hτ F x r _
  | add z z' hz hz' =>
    refine (congrArg _ (map_add _ z z')).trans ?_
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hz hz').trans (map_add _ z z').symm)

/-- The `𝒪_U(W)`-submodule of the sections over `W` of the pullback spanned by the restrictions
`a^*(η(n))` of unit sections over `T`. -/
noncomputable def pullbackUnitSpan
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) :
    Submodule ((SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj.obj (op W))
      (((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W)) :=
  Submodule.span _ (Set.range (pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a))

/-- Restriction along `h : W' ⟶ W` carries the span at `(T, a)` into the span at `(T, h ≫ a)`. -/
theorem map_mem_pullbackUnitSpan
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W W' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (k : W' ⟶ W)
    {q : ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W)}
    (hq : q ∈ pullbackUnitSpan B E h S hS p hp τ hτ φ F T a) :
    ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map k.op q ∈
      pullbackUnitSpan B E h S hS p hp τ hτ φ F T (k ≫ a) := by
  induction hq using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, rfl⟩ := hz
    refine Submodule.subset_span ⟨n, ?_⟩
    exact PresheafOfModules.map_comp_apply _ a.op k.op _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z z' _ _ hz hz' => rw [map_add]; exact Submodule.add_mem _ hz hz'
  | smul r z _ hz =>
    rw [PresheafOfModules.map_smul]
    exact Submodule.smul_mem _ _ hz

/-- Changing the index along `j : T' ⟶ T`: the span at `(T, k ≫ b(j))` lies in the span at
`(T', k)`. -/
theorem pullbackUnitSpan_comp_le
    {T T' : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)} (j : T' ⟶ T)
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (k : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T') :
    pullbackUnitSpan B E h S hS p hp τ hτ φ F T
        (k ≫ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).map j) ≤
      pullbackUnitSpan B E h S hS p hp τ hτ φ F T' k := by
  refine Submodule.span_le.2 ?_
  rintro z ⟨n, rfl⟩
  refine Submodule.subset_span ⟨(restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).map j.op n,
    ?_⟩
  have h1 : ((PresheafOfModules.pullbackPushforwardAdjunction.{max u m}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).unit.app
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).app (op T')
        ((restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).map j.op n) =
      ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).map j).op
        (((PresheafOfModules.pullbackPushforwardAdjunction.{max u m}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).unit.app
            (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).app (op T) n) :=
    PresheafOfModules.naturality_apply
      ((PresheafOfModules.pullbackPushforwardAdjunction.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).unit.app
          (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)) j.op n
  unfold pullbackUnitRestriction
  rw [h1]
  exact (PresheafOfModules.map_comp_apply _
    ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).map j).op k.op _).symm

/-- The range of `AlgebraicGeometry.Stack.pullbackUnitTensorMap` is stable under the scalars of
`𝒪_U(W)`. -/
theorem exists_pullbackUnitTensorMap_eq_smul
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hR : (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op)
    (s : (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.obj
      (op W))
    (ζ : (ModuleCat.extendScalars ((structureSheaf B S hS p hp τ hτ).obj.map
        ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom).obj
        ((commRestrictModule B S hS p hp τ hτ F).obj
          (op ((etaleIndex B E h S hS p hp y).obj T)))) :
    ∃ ζ', pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a φ' hR ζ' =
      s • pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a φ' hR ζ := by
  let : Module ((structureSheaf B S hS p hp τ hτ).obj.obj
      (op ((etaleIndex B E h S hS p hp y).obj T)))
      ((structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp x).obj W))) :=
    Module.compHom _ ((structureSheaf B S hS p hp τ hτ).obj.map
      ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom
  induction ζ using TensorProduct.inductionOn with
  | tmul r n =>
    refine ⟨(@id ((structureSheaf B S hS p hp τ hτ).obj.obj
        (op ((etaleIndex B E h S hS p hp x).obj W)))
        (((localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app (op W)).hom s) *
        @id ((structureSheaf B S hS p hp τ hτ).obj.obj
          (op ((etaleIndex B E h S hS p hp x).obj W))) r) ⊗ₜ n, ?_⟩
    refine (pullbackUnitTensorMap_tmul B E h S hS p hp τ hτ φ F T a φ' hR _ n).trans ?_
    refine Eq.trans ?_ (congrArg (s • ·)
      (pullbackUnitTensorMap_tmul B E h S hS p hp τ hτ φ F T a φ' hR r n).symm)
    have key : ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom
        (((localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app (op W)).hom s) = s :=
      congrArg (fun k => k.hom s)
        (Iso.hom_inv_id_app (localStructurePresheafIso B E h S hS p hp x τ hτ) (op W))
    refine (congrArg (fun c => c • pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n)
      ((map_mul ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom _
        (@id ((structureSheaf B S hS p hp τ hτ).obj.obj
          (op ((etaleIndex B E h S hS p hp x).obj W))) r)).trans
        (congrArg (· * _) key))).trans ?_
    exact mul_smul _ _ _
  | add z z' hz hz' =>
    obtain ⟨ζ₁, h₁⟩ := hz
    obtain ⟨ζ₂, h₂⟩ := hz'
    exact ⟨ζ₁ + ζ₂, (map_add _ _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans
      ((smul_add _ _ _).symm.trans (congrArg (s • ·) (map_add _ z z').symm)))⟩

/-- **Every element of the span at `(T, a)` is a value of the tensor map.** -/
theorem exists_pullbackUnitTensorMap_eq_of_mem_pullbackUnitSpan
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (φ' : (etaleIndex B E h S hS p hp x).obj
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) ⟶
        (etaleIndex B E h S hS p hp y).obj T)
    (hR : (restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op T) =
          (ringStructureSheafCore B S hS p hp τ hτ).obj.map φ'.op)
    {q : ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W)}
    (hq : q ∈ pullbackUnitSpan B E h S hS p hp τ hτ φ F T a) :
    ∃ ζ, pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a φ' hR ζ = q := by
  let : Module ((structureSheaf B S hS p hp τ hτ).obj.obj
      (op ((etaleIndex B E h S hS p hp y).obj T)))
      ((structureSheaf B S hS p hp τ hτ).obj.obj (op ((etaleIndex B E h S hS p hp x).obj W))) :=
    Module.compHom _ ((structureSheaf B S hS p hp τ hτ).obj.map
      ((etaleIndex B E h S hS p hp x).map a ≫ φ').op).hom
  induction hq using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨n, rfl⟩ := hz
    refine ⟨(1 : (structureSheaf B S hS p hp τ hτ).obj.obj
      (op ((etaleIndex B E h S hS p hp x).obj W))) ⊗ₜ n, ?_⟩
    refine (pullbackUnitTensorMap_tmul B E h S hS p hp τ hτ φ F T a φ' hR _ n).trans ?_
    refine (congrArg (fun c => c • pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n)
      (map_one ((localStructurePresheafIso B E h S hS p hp x τ hτ).inv.app (op W)).hom)).trans ?_
    exact one_smul _ _
  | zero => exact ⟨0, map_zero _⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨ζ₁, h₁⟩ := hz
    obtain ⟨ζ₂, h₂⟩ := hz'
    exact ⟨ζ₁ + ζ₂, (map_add _ _ _).trans (congrArg₂ (· + ·) h₁ h₂)⟩
  | smul r z _ hz =>
    obtain ⟨ζ, rfl⟩ := hz
    exact exists_pullbackUnitTensorMap_eq_smul B E h S hS p hp τ hτ φ F T a φ' hR r ζ

/-- **Locally, an arrow into a base change factors through the base change of an affine object.**
For `a : W ⟶ b(T)`, the arrows `h : W' ⟶ W` for which `h ≫ a = k ≫ b(j)` with `j : T' ⟶ T` and
`T'` affine form a covering sieve of the small étale site of the scheme below `x`. -/
theorem exists_sieve_mem_forall_comp_eq_baseChange_map_affine
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T) :
    ∃ R : Sieve W, R ∈ SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x) W ∧
      ∀ ⦃W' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)⦄ (k : W' ⟶ W), R k →
        ∃ (T' : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
          (_ : _root_.AlgebraicGeometry.IsAffine
            ((SmallEtale.toScheme E (p.obj y).left.1 (contains_base B E h S hS p y)).obj T'))
          (k' : W' ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T')
          (j : T' ⟶ T),
          k ≫ a = k' ≫ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).map j := by
  have hcont := smallEtaleBaseChange_isContinuous E (smallEtaleBaseMorphism B E h S hS p φ)
  have hcp : CoverPreserving
      (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y))
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)) :=
    CoverPreserving.of_isContinuous _ _ _
  refine ⟨(Sieve.functorPushforward (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
    (SmallEtale.affineImageCover E (p.obj y).left.1 (contains_base B E h S hS p y)
      T).sieve₀).pullback a,
    GrothendieckTopology.pullback_stable _ a (hcp.cover_preserve
      (SmallEtale.mem_topology_sieve₀_affineImageCover E _ _ T)), ?_⟩
  intro W' k hk
  obtain ⟨Z, j, k', hj, hfac⟩ := hk
  obtain ⟨_, j₁, _, ⟨i⟩, rfl⟩ := hj
  refine ⟨_, SmallEtale.isAffine_affineImageCover_X E _ _ T i,
    k' ≫ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).map j₁,
    (SmallEtale.affineImageCover E _ _ T).f i, ?_⟩
  rw [hfac, Functor.map_comp, Category.assoc]

/-- The sieve of the arrows `g : W' ⟶ W` along which a section `q` of the pullback restricts into
the span at some `(T, a)` with `T` affine. -/
noncomputable def pullbackUnitSpanSieve
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (q : ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W)) : Sieve W where
  arrows W' g := ∃ (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    (_ : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj y).left.1 (contains_base B E h S hS p y)).obj T))
    (a : W' ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T),
    ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map g.op q ∈
      pullbackUnitSpan B E h S hS p hp τ hτ φ F T a
  downward_closed := by
    rintro W' W'' g ⟨T, hT, a, hq⟩ k
    refine ⟨T, hT, k ≫ a, ?_⟩
    rw [op_comp, PresheafOfModules.map_comp_apply]
    exact map_mem_pullbackUnitSpan B E h S hS p hp τ hτ φ F T a k hq

/-- **A restriction of a unit section lies locally in the span at an affine index**: refine the
index by an affine covering and pull it back along the base change. -/
theorem pullbackUnitSpanSieve_pullbackUnitRestriction_mem
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (n : (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).obj (op T)) :
    pullbackUnitSpanSieve B E h S hS p hp τ hτ φ F
        (pullbackUnitRestriction B E h S hS p hp τ hτ φ F T a n) ∈
      SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x) W := by
  obtain ⟨R, hR, hfac⟩ :=
    exists_sieve_mem_forall_comp_eq_baseChange_map_affine B E h S hS p φ T a
  refine GrothendieckTopology.superset_covering _ ?_ hR
  intro W' k hk
  obtain ⟨T', hT', k', j, hkj⟩ := hfac k hk
  refine ⟨T', hT', k', pullbackUnitSpan_comp_le B E h S hS p hp τ hτ φ F j k' ?_⟩
  rw [← hkj]
  exact map_mem_pullbackUnitSpan B E h S hS p hp τ hτ φ F T a k (Submodule.subset_span ⟨n, rfl⟩)

/-- Restriction of sections of the pullback is additive. -/
theorem pullbackObj_map_add
    {W W' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)} (k : W' ⟶ W)
    (z z' : ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W)) :
    ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map k.op (z + z') =
      ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map k.op z +
      ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map k.op z' :=
  map_add _ _ _

/-- **Sums of sections lying locally in affine spans lie locally in affine spans**: two indices
are refined by an affine covering of their product. -/
theorem pullbackUnitSpanSieve_add_mem
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (q₁ q₂ : ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W))
    (h₁ : pullbackUnitSpanSieve B E h S hS p hp τ hτ φ F q₁ ∈
      SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x) W)
    (h₂ : pullbackUnitSpanSieve B E h S hS p hp τ hτ φ F q₂ ∈
      SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x) W) :
    pullbackUnitSpanSieve B E h S hS p hp τ hτ φ F (q₁ + q₂) ∈
      SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x) W := by
  refine GrothendieckTopology.transitive _ (GrothendieckTopology.intersection_covering _ h₁ h₂)
    _ ?_
  rintro W' g ⟨⟨T₁, hT₁, a₁, m₁⟩, ⟨T₂, hT₂, a₂, m₂⟩⟩
  let bc := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)
  let a₁₂ : W' ⟶ bc.obj (T₁ ⨯ T₂) := prod.lift a₁ a₂ ≫ inv (prodComparison bc T₁ T₂)
  obtain ⟨R, hR, hfac⟩ :=
    exists_sieve_mem_forall_comp_eq_baseChange_map_affine B E h S hS p φ (T₁ ⨯ T₂) a₁₂
  refine GrothendieckTopology.superset_covering _ ?_ hR
  intro W'' k hk
  obtain ⟨T', hT', k', j, hkj⟩ := hfac k hk
  refine ⟨T', hT', k', ?_⟩
  rw [pullbackObj_map_add]
  have key : ∀ (Tm : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
      (pr : T₁ ⨯ T₂ ⟶ Tm) (am : W' ⟶ bc.obj Tm), a₁₂ ≫ bc.map pr = am →
      ∀ qm, ((PresheafOfModules.pullback.{max u m}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
          (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map g.op qm ∈
          pullbackUnitSpan B E h S hS p hp τ hτ φ F Tm am →
        ((PresheafOfModules.pullback.{max u m}
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
          (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).map (k ≫ g).op qm ∈
          pullbackUnitSpan B E h S hS p hp τ hτ φ F T' k' := by
    intro Tm pr am ham qm hqm
    rw [op_comp, PresheafOfModules.map_comp_apply]
    refine pullbackUnitSpan_comp_le B E h S hS p hp τ hτ φ F (j ≫ pr) k' ?_
    have : k ≫ am = k' ≫ bc.map (j ≫ pr) := by
      rw [← ham, ← Category.assoc, hkj, Category.assoc, ← Functor.map_comp]
    rw [← this]
    exact map_mem_pullbackUnitSpan B E h S hS p hp τ hτ φ F Tm am k hqm
  refine Submodule.add_mem _ (key T₁ prod.fst a₁ ?_ _ m₁) (key T₂ prod.snd a₂ ?_ _ m₂)
  · simp only [a₁₂, Category.assoc, inv_prodComparison_map_fst]
    exact prod.lift_fst _ _
  · simp only [a₁₂, Category.assoc, inv_prodComparison_map_snd]
    exact prod.lift_snd _ _

/-- Multiplying a section by a scalar preserves lying in a span. -/
theorem pullbackUnitSpanSieve_le_smul
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (r : (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj.obj
      (op W))
    (q : ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W)) :
    pullbackUnitSpanSieve B E h S hS p hp τ hτ φ F q ≤
      pullbackUnitSpanSieve B E h S hS p hp τ hτ φ F (r • q) := by
  rintro W' g ⟨T, hT, a, hq⟩
  refine ⟨T, hT, a, ?_⟩
  rw [PresheafOfModules.map_smul]
  exact Submodule.smul_mem _ _ hq

/-- **Every section of the pullback lies, locally, in the span at an affine index.** -/
theorem pullbackUnitSpanSieve_mem
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (q : ((PresheafOfModules.pullback.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
        (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)).obj (op W)) :
    pullbackUnitSpanSieve B E h S hS p hp τ hτ φ F q ∈
      SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x) W := by
  have htop := PresheafOfModules.generatedSubmodule_unit_eq_top.{max u m}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
    (P := restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)
  have hq : q ∈ (PresheafOfModules.generatedSubmodule
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
      ((PresheafOfModules.pullbackPushforwardAdjunction.{max u m}
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).unit.app
          (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F))).obj (op W) := by
    rw [htop]
    trivial
  rw [PresheafOfModules.generatedSubmodule_obj] at hq
  induction hq using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨X, hX, s, rfl⟩ := hz
    exact pullbackUnitSpanSieve_pullbackUnitRestriction_mem B E h S hS p hp τ hτ φ F X.unop
      hX.unop s
  | zero =>
    let bc := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)
    let hterm : IsTerminal (bc.obj (⊤_ (SmallEtale E (p.obj y).left.1
        (contains_base B E h S hS p y)))) :=
      terminalIsTerminal.isTerminalObj bc _
    have h0 := pullbackUnitSpanSieve_pullbackUnitRestriction_mem B E h S hS p hp τ hτ φ F
      (⊤_ (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))) (hterm.from W) 0
    have hz : pullbackUnitRestriction B E h S hS p hp τ hτ φ F
        (⊤_ (SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))) (hterm.from W)
        0 = 0 := by
      unfold pullbackUnitRestriction
      rw [map_zero]
      exact map_zero _
    rwa [hz] at h0
  | add z z' _ _ hz hz' =>
    exact pullbackUnitSpanSieve_add_mem B E h S hS p hp τ hτ φ F z z' hz hz'
  | smul r z _ hz =>
    exact GrothendieckTopology.superset_covering _
      (pullbackUnitSpanSieve_le_smul B E h S hS p hp τ hτ φ F r z) hz

section Cartesian

variable (hcart : ∀ ⦃x₁ x₂ : 𝒳⦄ (e : x₁ ⟶ x₂),
  _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁)) →
    _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₂)) →
      Function.Bijective (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, m}
        (R := (structureSheaf B S hS p hp τ hτ).obj) (commRestrictModule B S hS p hp τ hτ F) e.op))

include hcart

/-- **The affine case, surjectivity.** Over an affine object `W` mapping to the base change of an
affine object, every section of `F|_{U_ét}` is a value of the comparison map. -/
theorem exists_restrictModulePullbackComparisonUnivLE_app_eq_of_cartesian
    (T : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    (hT : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj y).left.1 (contains_base B E h S hS p y)).obj T))
    {W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)}
    (hW : _root_.AlgebraicGeometry.IsAffine
      ((SmallEtale.toScheme E (p.obj x).left.1 (contains_base B E h S hS p x)).obj W))
    (a : W ⟶ (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj T)
    (s : (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).obj (op W)) :
    ∃ t, (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app (op W) t = s := by
  obtain ⟨φ', hF, hR⟩ := exists_restrictionPushforwardComparison_app_eq B E h S hS p hp τ hτ φ F T
  obtain ⟨ζ, hζ⟩ := (hcart ((etaleIndex B E h S hS p hp x).map a ≫ φ')
    (isAffine_etaleIndex_obj B E h S hS p hp x W hW)
    (isAffine_etaleIndex_obj B E h S hS p hp y T hT)).2 s
  exact ⟨pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a φ' hR ζ,
    (restrictModulePullbackComparisonUnivLE_app_pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a
      φ' hF hR ζ).trans hζ⟩

/-- **The affine case, injectivity.** Over an affine object `W` mapping to the base change of an
affine object `T`, a section in the span at `(T, a)` killed by the comparison map is zero. -/
theorem eq_zero_of_mem_pullbackUnitSpan_of_cartesian
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
  obtain ⟨φ', hF, hR⟩ := exists_restrictionPushforwardComparison_app_eq B E h S hS p hp τ hτ φ F T
  obtain ⟨ζ, rfl⟩ := exists_pullbackUnitTensorMap_eq_of_mem_pullbackUnitSpan B E h S hS p hp τ hτ
    φ F T a φ' hR hq
  have hb := (hcart ((etaleIndex B E h S hS p hp x).map a ≫ φ')
    (isAffine_etaleIndex_obj B E h S hS p hp x W hW)
    (isAffine_etaleIndex_obj B E h S hS p hp y T hT)).1
  rw [restrictModulePullbackComparisonUnivLE_app_pullbackUnitTensorMap B E h S hS p hp τ hτ φ F T a
    φ' hF hR ζ] at h0
  have hζ : ζ = 0 := hb (h0.trans (map_zero _).symm)
  rw [hζ]
  exact map_zero _

/-- **The comparison map of Stacks 06WC of a module cartesian over the affine objects is locally
bijective**, along every arrow `φ` of `𝒳`: it becomes an isomorphism after sheafification for
the small étale topology. No flatness of the morphism below `φ` is needed. -/
theorem isLocallyBijectiveRestrictModulePullbackComparisonUnivLE_of_cartesian :
    IsLocallyBijectiveRestrictModulePullbackComparisonUnivLE B E h S hS p hp τ hτ φ F := by
  constructor
  · constructor
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
      have h0 := eq_zero_of_mem_pullbackUnitSpan_of_cartesian B E h S hS p hp τ hτ φ F hcart T hT
        (SmallEtale.isAffine_affineImageCover_X E _ _ W'' i) _ hm hc
      rw [(P.map ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op).hom.map_sub] at h0
      exact sub_eq_zero.1 h0
    change P.map ((j ≫ (SmallEtale.affineImageCover E _ _ W'').f i) ≫ g).op y₁ =
      P.map ((j ≫ (SmallEtale.affineImageCover E _ _ W'').f i) ≫ g).op y₂
    rw [Category.assoc, op_comp, PresheafOfModules.map_comp_apply,
      PresheafOfModules.map_comp_apply, key]
  · constructor
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
    obtain ⟨t, ht⟩ := exists_restrictModulePullbackComparisonUnivLE_app_eq_of_cartesian
      B E h S hS p hp τ hτ φ F hcart T hT (SmallEtale.isAffine_affineImageCover_X E _ _ W'' i)
      ((SmallEtale.affineImageCover E _ _ W'').f i ≫ a)
      (Q.map ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op s')
    refine ⟨P.map j.op t, ?_⟩
    change (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ τ hτ F).app (op Z)
      (P.map j.op t) = Q.map ((j ≫ (SmallEtale.affineImageCover E _ _ W'').f i) ≫ g).op s'
    rw [PresheafOfModules.naturality_apply, ht, Category.assoc]
    exact (PresheafOfModules.map_comp_apply Q
      ((SmallEtale.affineImageCover E _ _ W'').f i ≫ g).op j.op s').symm

end Cartesian

end AlgebraicGeometry.Stack
