module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSemiorthogonalDecompositionSucc
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfDerivedModuleLowerShriekSuccSheafFlatBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactnessGeneral
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice

/-!
# Stacks 0H15 over a smooth chart: the reduction to the stack of an affine scheme

Let `𝒳` be an algebraic stack and `H ∈ D_QCoh(𝒪_{𝒳_{flat,fppf}})` (module universe `u + 1`).
**Stacks 0H15** asserts that for every morphism `x ⟶ x'` of `𝒳_{affine}` the map
`RΓ(x', Lg_!H) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, Lg_!H)` is a quasi-isomorphism. This file carries out the
third and fourth paragraphs of the source's proof: given the étale locality of the second
paragraph (`AlgebraicGeometry.Stack.FlatFppf.hasAffineDerivedSectionsBaseChange_of_covering`), it
reduces the statement for `𝒳` to the case `𝒳 = (Sch/X)_fppf` with `X` affine, the last paragraph
of the proof (taken as the hypothesis `haff`).

## The argument

* **Stacks 075C at a chart.** For an object `x₀` of `𝒳` over a scheme `U`, the canonical
  localization functor `Ψ = Over.post p : 𝒳/x₀ ⥤ (Sch/U)` of Stacks 06W0 is an equivalence of
  sites, with inverse the functor `Φ` of chosen cartesian lifts of `x₀`
  (`AlgebraicGeometry.Stack.FlatFppf.chartSliceEquivalence`); with the identification of structure
  sheaves of Stacks 06TW it gives an equivalence of sheaves of modules
  (`AlgebraicGeometry.Stack.FlatFppf.chartModuleEquivalence`), and the inverse image
  `x₀^{-1}` along `x₀ : (Sch/U) ⟶ 𝒳` is restriction to the slice followed by it
  (`AlgebraicGeometry.Stack.FlatFppf.modulePullbackChartIso`).
* **Derived sections over the chart.** Restriction to a slice has an exact left adjoint, extension
  by zero (Stacks 03DJ), so `x₀^{-1}` preserves K-injective complexes
  (`AlgebraicGeometry.Stack.FlatFppf.isKInjective_chartPullback_mapHomologicalComplex`), and the
  sections of `x₀^{-1}I` over `Ψ(w)` are those of `I` over `w`, compatibly with restriction
  (`AlgebraicGeometry.Stack.FlatFppf.chartSectionsIso`). Hence the map of Stacks 0H15 for `K` along
  an arrow `a` of `𝒳/x₀` is invertible exactly when the one for `x₀^{-1}K` along `Ψ(a)` is
  (`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedSectionsBaseChange_iff_chart`).
* **Stacks 07AV.** For a flat object `x₀`, `x₀^{-1} Lg_! H = L(g')_!(f')^{-1}H`, and `(f')^{-1}`
  preserves `D_QCoh` of the flat-fppf sites
  (`derivedCategoryB_flatQuasicoherentModulesSucc_derivedModuleSubsiteInverseImage`);
  so for `x₀` flat over an affine scheme, the affine case gives the map of Stacks 0H15 along every
  arrow of `𝒳_{affine}` mapping to `x₀`
  (`isIso_derivedSectionsBaseChange_derivedModuleLowerShriekSucc_of_hom_flatAffine`).
* **The covering.** By Stacks 06XH an étale covering of an affine `x'` lifts to a smooth surjective
  chart `(Sch/X) ⟶ 𝒳`; refining by the affine opens of `X`, `x'` has a covering sieve of
  `𝒳_{affine, étale}` whose members map to flat objects over affine schemes
  (`AlgebraicGeometry.Stack.FlatFppf.exists_flatAffine_sieve_mem`).

## Main results

All names are in the namespace `AlgebraicGeometry.Stack.FlatFppf`.

* `isIso_derivedSectionsBaseChange_iff_chart`.
* `exists_flatAffine_sieve_mem`.
* `hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc_of_affine`:
  **Stacks 0H15 for `𝒳` from the case of an affine scheme.**

## References

* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 075C](https://stacks.math.columbia.edu/tag/075C)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 07AV](https://stacks.math.columbia.edu/tag/07AV)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (x₀ : 𝒳.val.val.obj)

/-- The chosen lift of `x₀` along `a : V ⟶ U` (the 2-Yoneda lemma, Stacks 004B). -/
abbrev chartLift (a : Over (𝒳.val.val.p.obj x₀)) :
    Functor.TwoYoneda.Lift 𝒳.val.val.p (𝒳.val.val.p.obj x₀) (Functor.Fiber.mk (a := x₀) rfl) a :=
  Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _
    (Functor.Fiber.mk (a := x₀) rfl) a

/-- The functor `(Sch/U) ⥤ 𝒳` of the 1-morphism `x₀ : (Sch/U) ⟶ 𝒳`. -/
abbrev chartLiftFunctor : Over (𝒳.val.val.p.obj x₀) ⥤ 𝒳.val.val.obj :=
  Functor.TwoYoneda.liftFunctor 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _
    (Functor.Fiber.mk (a := x₀) rfl)

/-- The chart slice functor `Φ : (Sch/U) ⥤ 𝒳/x₀`, `U` the scheme under `x₀`. -/
def chartSliceFunctor : Over (𝒳.val.val.p.obj x₀) ⥤ Over x₀ where
  obj a := Over.mk (chartLift B S hS 𝒳 x₀ a).φ
  map {a a'} g := Over.homMk ((chartLiftFunctor B S hS 𝒳 x₀).map g)
    (@Functor.IsStronglyCartesian.fac _ _ _ _ 𝒳.val.val.p _ _ _ _ a'.hom
      (chartLift B S hS 𝒳 x₀ a').φ (chartLift B S hS 𝒳 x₀ a').isStronglyCartesian _ _ _ _
      (Over.w g).symm (chartLift B S hS 𝒳 x₀ a).φ
      (chartLift B S hS 𝒳 x₀ a).isStronglyCartesian.toIsHomLift)
  map_id a := Over.OverMorphism.ext ((chartLiftFunctor B S hS 𝒳 x₀).map_id a)
  map_comp g g' := Over.OverMorphism.ext ((chartLiftFunctor B S hS 𝒳 x₀).map_comp g g')

/-- `Φ ⋙ Ψ ≅ 𝟭`, `Ψ = Over.post p` the canonical localization functor of Stacks 06W0. -/
def chartSliceCounitIso :
    chartSliceFunctor B S hS 𝒳 x₀ ⋙ Over.post 𝒳.val.val.p ≅ 𝟭 (Over (𝒳.val.val.p.obj x₀)) :=
  NatIso.ofComponents
    (fun a => Over.isoMk (eqToIso (Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _ (Functor.Fiber.mk (a := x₀) rfl)) a)) (by
      haveI := (chartLift B S hS 𝒳 x₀ a).isStronglyCartesian.toIsHomLift
      exact (IsHomLift.commSq 𝒳.val.val.p a.hom (chartLift B S hS 𝒳 x₀ a).φ).w.symm.trans
        (Category.comp_id _)))
    (fun {a a'} g => by
      have hw := Functor.TwoYoneda.liftFunctor_w 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids _ (Functor.Fiber.mk (a := x₀) rfl)
      apply Over.OverMorphism.ext
      have h := Functor.congr_hom hw g
      simp only [Functor.comp_map] at h
      change 𝒳.val.val.p.map ((chartLiftFunctor B S hS 𝒳 x₀).map g) ≫
          eqToHom (Functor.congr_obj hw a') = eqToHom (Functor.congr_obj hw a) ≫ g.left
      rw [h]
      simp)

/-- The chosen lift over `p(z ⟶ x₀)` is strongly cartesian. -/
theorem isStronglyCartesian_chartSliceFunctor_obj_post (z : Over x₀) :
    𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map z.hom)
      ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj z)).hom :=
  (chartLift B S hS 𝒳 x₀ ((Over.post 𝒳.val.val.p).obj z)).isStronglyCartesian

/-- `𝟭 ≅ Ψ ⋙ Φ`: an object `z ⟶ x₀` of `𝒳/x₀` is the chosen lift of `x₀` along the arrow
below it, up to the unique isomorphism over the identity. -/
def chartSliceUnitIso :
    𝟭 (Over x₀) ≅ Over.post 𝒳.val.val.p ⋙ chartSliceFunctor B S hS 𝒳 x₀ :=
  NatIso.ofComponents
    (fun z =>
      haveI : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map z.hom) z.hom :=
        𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
      haveI := isStronglyCartesian_chartSliceFunctor_obj_post B S hS 𝒳 x₀ z
      Over.isoMk (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p (𝒳.val.val.p.map z.hom)
        ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj z)).hom z.hom)
        (Functor.IsCartesian.fac 𝒳.val.val.p (𝒳.val.val.p.map z.hom)
          ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj z)).hom z.hom))
    (fun {z y} a => by
      haveI : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map z.hom) z.hom :=
        𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
      haveI : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map y.hom) y.hom :=
        𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
      haveI := isStronglyCartesian_chartSliceFunctor_obj_post B S hS 𝒳 x₀ z
      haveI := isStronglyCartesian_chartSliceFunctor_obj_post B S hS 𝒳 x₀ y
      apply Over.OverMorphism.ext
      change a.left ≫ (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p
          (𝒳.val.val.p.map y.hom)
          ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj y)).hom y.hom).hom =
        (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p (𝒳.val.val.p.map z.hom)
          ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj z)).hom z.hom).hom ≫
          ((chartSliceFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a)).left
      haveI : 𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map a.left)
          ((chartSliceFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a)).left := by
        change 𝒳.val.val.p.IsHomLift ((Over.post 𝒳.val.val.p).map a).left
          ((chartLiftFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a))
        haveI : (Over.forget (𝒳.val.val.p.obj x₀)).IsHomLift ((Over.post 𝒳.val.val.p).map a).left
            ((Over.post 𝒳.val.val.p).map a) :=
          inferInstanceAs ((Over.forget (𝒳.val.val.p.obj x₀)).IsHomLift
            ((Over.forget (𝒳.val.val.p.obj x₀)).map ((Over.post 𝒳.val.val.p).map a)) _)
        exact Functor.isHomLift_map_of_comp_eq (Functor.TwoYoneda.liftFunctor_w 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids _ (Functor.Fiber.mk (a := x₀) rfl)) _ _
      haveI : 𝒳.val.val.p.IsHomLift (𝒳.val.val.p.map a.left)
          ((Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p (𝒳.val.val.p.map z.hom)
            ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj z)).hom
              z.hom).hom ≫
            ((chartSliceFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a)).left) := by
        have h := IsHomLift.comp 𝒳.val.val.p (𝟙 _) (𝒳.val.val.p.map a.left)
          (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p (𝒳.val.val.p.map z.hom)
            ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj z)).hom
              z.hom).hom
          ((chartSliceFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a)).left
        rwa [Category.id_comp] at h
      refine Functor.IsStronglyCartesian.ext 𝒳.val.val.p (𝒳.val.val.p.map y.hom)
        ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj y)).hom
        (𝒳.val.val.p.map a.left) ?_
      have h₁ := Over.w ((chartSliceFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a))
      have h₂ := Functor.IsCartesian.fac 𝒳.val.val.p (𝒳.val.val.p.map y.hom)
          ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj y)).hom y.hom
      have h₃ := Functor.IsCartesian.fac 𝒳.val.val.p (𝒳.val.val.p.map z.hom)
          ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj z)).hom z.hom
      simp only [Functor.IsCartesian.domainUniqueUpToIso_hom, Category.assoc, h₁, h₂, h₃]
      exact (Over.w a).symm ▸ rfl)


/-- **Stacks 06W0 at a chart**: `𝒳/x₀ ≌ (Sch/U)`, with functor the canonical localization functor
`Ψ = Over.post p` and inverse the chart slice functor `Φ` of chosen lifts. -/
def chartSliceEquivalence : Over x₀ ≌ Over (𝒳.val.val.p.obj x₀) :=
  CategoryTheory.Equivalence.mk (Over.post 𝒳.val.val.p) (chartSliceFunctor B S hS 𝒳 x₀)
    (chartSliceUnitIso B S hS 𝒳 x₀) (chartSliceCounitIso B S hS 𝒳 x₀)

/-- The topology of `𝒳/x₀` is the one it inherits along `𝒳/x₀ ⥤ 𝒳 ⥤ (Sch/S)`. -/
theorem fppfTopology_over_eq :
    (associatedTopology B S hS 𝒳.val.val.p B.topology).over x₀ =
      (Over.forget x₀ ⋙ 𝒳.val.val.p).inheritedTopology (B.topology.over (B.obj hS)) :=
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  (Functor.inheritedTopology_overForget_comp 𝒳.val.val.p _ x₀).symm

/-- A functor over the base between two categories fibred in groupoids is continuous and
cocontinuous for the inherited topologies (Stacks 06NW). -/
private theorem isContinuous_and_isCocontinuous_inheritedTopology_of_comp_eq
    {𝒞 C₁ C₂ : Type*} [Category 𝒞] [HasPullbacks 𝒞] [Category C₁] [Category C₂]
    (J : GrothendieckTopology 𝒞) {p₁ : C₁ ⥤ 𝒞} {p₂ : C₂ ⥤ 𝒞} (h₁ : p₁.IsFiberedInGroupoids)
    (h₂ : p₂.IsFiberedInGroupoids) {F : C₁ ⥤ C₂} (hF : F ⋙ p₂ = p₁) :
    F.IsContinuous (p₁.inheritedTopology J) (p₂.inheritedTopology J) ∧
      F.IsCocontinuous (p₁.inheritedTopology J) (p₂.inheritedTopology J) :=
  have := h₁.isFibered
  have := h₂.isFibered
  (h₂.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology J

/-- `Ψ = Over.post p : 𝒳/x₀ ⥤ (Sch/U)` is continuous and cocontinuous (Stacks 06NW). -/
theorem isContinuous_and_isCocontinuous_overPost :
    (Over.post 𝒳.val.val.p (X := x₀)).IsContinuous
        ((associatedTopology B S hS 𝒳.val.val.p B.topology).over x₀)
        (associatedTopology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p
          B.topology) ∧
      (Over.post 𝒳.val.val.p (X := x₀)).IsCocontinuous
        ((associatedTopology B S hS 𝒳.val.val.p B.topology).over x₀)
        (associatedTopology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p
          B.topology) := by
  rw [fppfTopology_over_eq]
  exact isContinuous_and_isCocontinuous_inheritedTopology_of_comp_eq _
    (Functor.IsFiberedInGroupoids.comp _ _ (Functor.IsFiberedInGroupoids.over_forget x₀)
      𝒳.val.isFiberedInGroupoids)
    (Functor.IsFiberedInGroupoids.over_forget (𝒳.val.val.p.obj x₀))
    (Over.post_forget_eq_forget_comp 𝒳.val.val.p x₀)

/-- `Φ : (Sch/U) ⥤ 𝒳/x₀` is continuous and cocontinuous (Stacks 06NW). -/
theorem isContinuous_and_isCocontinuous_chartSliceFunctor :
    (chartSliceFunctor B S hS 𝒳 x₀).IsContinuous
        (associatedTopology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p
          B.topology)
        ((associatedTopology B S hS 𝒳.val.val.p B.topology).over x₀) ∧
      (chartSliceFunctor B S hS 𝒳 x₀).IsCocontinuous
        (associatedTopology B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p
          B.topology)
        ((associatedTopology B S hS 𝒳.val.val.p B.topology).over x₀) := by
  rw [fppfTopology_over_eq]
  exact isContinuous_and_isCocontinuous_inheritedTopology_of_comp_eq _
    (Functor.IsFiberedInGroupoids.over_forget (𝒳.val.val.p.obj x₀))
    (Functor.IsFiberedInGroupoids.comp _ _ (Functor.IsFiberedInGroupoids.over_forget x₀)
      𝒳.val.isFiberedInGroupoids)
    (Functor.TwoYoneda.liftFunctor_w 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _
      (Functor.Fiber.mk (a := x₀) rfl))


/-- The identification of Stacks 06TW along the chart: the structure sheaf of `(Sch/U)` is the
restriction of that of `𝒳` along `x₀ : (Sch/U) ⟶ 𝒳`. -/
theorem chartRingEq :
    (ambientRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj =
      (objectStackMap B S hS 𝒳 x₀).hom.hom.toFunctor.op ⋙
        (ambientRingStructureSheaf B S hS 𝒳).obj :=
  ringStructureSheafCore_obj_eq B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p
    𝒳.val.val.p (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids (objectStackMap B S hS 𝒳 x₀).hom.hom.toFunctor
    (objectStackMap B S hS 𝒳 x₀).hom.hom.w B.topology le_rfl

/-- `chartRingEq`, with the chart written through the chosen lifts. -/
theorem chartRingEq' :
    (ambientRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj =
      (chartLiftFunctor B S hS 𝒳 x₀).op ⋙ (ambientRingStructureSheaf B S hS 𝒳).obj :=
  chartRingEq B S hS 𝒳 x₀

/-- The ring transport along `𝒳/x₀ ≌ (Sch/U)` from the restricted structure sheaf of `𝒳` to the
structure sheaf of `(Sch/U)`: the identification of Stacks 06TW. -/
def chartRingTransport :
    Stacks.UniverseLift.RingTransport (chartSliceEquivalence B S hS 𝒳 x₀)
      ((ambientRingStructureSheaf B S hS 𝒳).over x₀).obj
      (ambientRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj where
  iso Y := ((eqToIso (chartRingEq' B S hS 𝒳 x₀)).app Y).ringCatIsoToRingEquiv
  naturality {Y Y'} f x := by
    have h := congrArg (fun φ => (RingCat.Hom.hom φ) x)
      ((eqToHom (chartRingEq' B S hS 𝒳 x₀)).naturality f)
    exact h

attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections

/-- **Sheaves of modules on `𝒳/x₀` and on `(Sch/U)`**, with sections in `Type (u + 1)`: the
equivalence induced by `𝒳/x₀ ≌ (Sch/U)` and Stacks 06TW. -/
def chartModuleEquivalence :
    SheafOfModules.{u + 1} ((ambientRingStructureSheaf B S hS 𝒳).over x₀) ≌
      SheafOfModules.{u + 1}
        (ambientRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))) :=
  @Stacks.UniverseLift.RingTransport.sheafEquivalence.{u + 1} _ _ _ _ _ _ _ _ _
    (chartRingTransport B S hS 𝒳 x₀) (isContinuous_and_isCocontinuous_overPost B S hS 𝒳 x₀).1
    (isContinuous_and_isCocontinuous_chartSliceFunctor B S hS 𝒳 x₀).1

/-- **The inverse image along the chart is restriction to the slice followed by the chart
equivalence**: `x₀^{-1} ≅ (j_{x₀})^{-1} ⋙ (𝒳/x₀ ≌ (Sch/U))`, on the nose on sections. -/
def modulePullbackChartIso :
    AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
        (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p 𝒳.val.val.p
        (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids (objectStackMap B S hS 𝒳 x₀).hom.hom.toFunctor
        (objectStackMap B S hS 𝒳 x₀).hom.hom.w B.topology le_rfl ≅
      SheafOfModules.overFunctor (ambientRingStructureSheaf B S hS 𝒳) x₀ ⋙
        (chartModuleEquivalence B S hS 𝒳 x₀).functor :=
  NatIso.ofComponents (fun M => (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun Y => ModuleCat.restrictScalarsComp'App
        ((chartRingTransport B S hS 𝒳 x₀).iso Y).toRingHom (RingHom.id _)
        ((eqToHom (chartRingEq B S hS 𝒳 x₀)).app Y).hom rfl
        (M.val.obj (op ((objectStackMap B S hS 𝒳 x₀).hom.hom.toFunctor.obj Y.unop))))
      (fun _ _ _ => by ext; rfl)))
    (fun _ => by ext; rfl)


/-- Sheafification on `𝒳/x₀` of abelian presheaves with sections in `Type (u + 1)`. -/
local instance hasSheafify_over_chart :
    HasSheafify ((associatedTopology B S hS 𝒳.val.val.p B.topology).over x₀)
      AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- On `𝒳/x₀`, sheafification of abelian presheaves with sections in `Type (u + 1)` inverts exactly
the locally bijective morphisms. -/
local instance wEqualsLocallyBijective_over_chart :
    ((associatedTopology B S hS 𝒳.val.val.p B.topology).over x₀).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

/-- **Restriction to `𝒳/x₀` preserves K-injective complexes** (Stacks 03F3, Stacks 070G): its left
adjoint, extension by zero, is exact (Stacks 03DJ). -/
theorem isKInjective_overFunctor_mapHomologicalComplex
    (I : CochainComplex (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((SheafOfModules.overFunctor.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)
        x₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have hex := SheafOfModules.extensionByZero_exact.{0} (ambientRingStructureSheaf B S hS 𝒳) x₀
  rw [exactFunctor_iff] at hex
  have := hex.1
  have := hex.2
  have adj := SheafOfModules.extensionByZeroAdjunction.{0} (ambientRingStructureSheaf B S hS 𝒳) x₀
  have := adj.left_adjoint_additive
  have : (SheafOfModules.overFunctor.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) x₀).Additive :=
    adj.right_adjoint_additive
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ adj I

/-- The pullback of a K-injective complex along the chart is K-injective after the identification
`modulePullbackChartIso`: restriction to `𝒳/x₀` and the equivalence `𝒳/x₀ ≌ (Sch/U)` both
preserve K-injectivity. -/
theorem isKInjective_chartModuleEquivalence_overFunctor
    (I : CochainComplex (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((chartModuleEquivalence B S hS 𝒳 x₀).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((SheafOfModules.overFunctor.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)
          x₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) := by
  have := isKInjective_overFunctor_mapHomologicalComplex B S hS 𝒳 x₀ I
  have : (chartModuleEquivalence B S hS 𝒳 x₀).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  exact Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence _ _


/-- The comparison `w ≅ Φ(Ψ w)` of `𝒳/x₀` lies over the identity of the scheme below `w`. -/
theorem p_map_chartSliceUnitIso_hom_left (w : Over x₀) :
    𝒳.val.val.p.map ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left =
      eqToHom (Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids _ (Functor.Fiber.mk (a := x₀) rfl))
          ((Over.post 𝒳.val.val.p).obj w)).symm := by
  have : 𝒳.val.val.p.IsStronglyCartesian (𝒳.val.val.p.map w.hom) w.hom :=
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _
  have := isStronglyCartesian_chartSliceFunctor_obj_post B S hS 𝒳 x₀ w
  have := Functor.IsCartesian.domainUniqueUpToIso_hom_isHomLift 𝒳.val.val.p
    (𝒳.val.val.p.map w.hom)
    ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj w)).hom w.hom
  have h := IsHomLift.fac' 𝒳.val.val.p (𝟙 (𝒳.val.val.p.obj w.left))
    (Functor.IsCartesian.domainUniqueUpToIso 𝒳.val.val.p (𝒳.val.val.p.map w.hom)
      ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj w)).hom w.hom).hom
  refine h.trans ?_
  simp only [Category.id_comp, eqToHom_trans]
  rfl

/-- Restriction of sections of a presheaf of rings along an identification, after an
identification of rings, is an identification. -/
private theorem map_eqToHom_op_apply {C : Type*} [Category C] (F : Cᵒᵖ ⥤ RingCat.{u})
    {A A' : C} (f : A ⟶ A') (e : A = A') (hf : f = eqToHom e)
    (h : F.obj (op A) = F.obj (op A')) (r : F.obj (op A)) :
    (F.map f.op).hom ((eqToHom h).hom r) = r := by
  subst hf
  subst e
  simp

/-- **Stacks 06TW at the comparison `w ≅ Φ(Ψ w)`**: the identification of rings of sections along
the chart, followed by restriction along the comparison, is the identity of `𝒪(w)`. -/
theorem chartRingTransport_iso_map_unit_apply (w : Over x₀)
    (r : (ambientRingStructureSheaf B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj.obj
        (op ((Over.post 𝒳.val.val.p).obj w))) :
    ((ambientRingStructureSheaf B S hS 𝒳).obj.map
        ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left.op).hom
      ((chartRingTransport B S hS 𝒳 x₀).iso (op ((Over.post 𝒳.val.val.p).obj w)) r) = r :=
  (congrArg (fun φ => ((ambientRingStructureSheaf B S hS 𝒳).obj.map
        ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left.op).hom (φ.hom r))
      (eqToHom_app (chartRingEq' B S hS 𝒳 x₀) (op ((Over.post 𝒳.val.val.p).obj w)))).trans
    (map_eqToHom_op_apply (BigFppfOver.structureSheaf B S hS).obj
      (𝒳.val.val.p.map ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left) _
      (p_map_chartSliceUnitIso_hom_left B S hS 𝒳 x₀ w)
      (Functor.congr_obj (chartRingEq' B S hS 𝒳 x₀) (op ((Over.post 𝒳.val.val.p).obj w))) r)


/-- The comparison `Φ(Ψ w) ⟶ w` and its inverse compose to the identity of `Φ(Ψ w)`, on the
objects of `𝒳`. -/
theorem chartSliceUnitIso_inv_hom_left (w : Over x₀) :
    ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left ≫
      ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left = 𝟙 _ :=
  congrArg CommaMorphism.left ((chartSliceUnitIso B S hS 𝒳 x₀).inv_hom_id_app w)

/-- The comparison `w ⟶ Φ(Ψ w)` and its inverse compose to the identity of `w`, on the objects
of `𝒳`. -/
theorem chartSliceUnitIso_hom_inv_left (w : Over x₀) :
    ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left ≫
      ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left = 𝟙 _ :=
  congrArg CommaMorphism.left ((chartSliceUnitIso B S hS 𝒳 x₀).hom_inv_id_app w)

/-- The identification of rings of sections along the chart is restriction along the inverse
comparison `Φ(Ψ w) ⟶ w`. -/
theorem chartRingTransport_iso_apply_eq (w : Over x₀)
    (r : (ambientRingStructureSheaf B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj.obj
        (op ((Over.post 𝒳.val.val.p).obj w))) :
    (chartRingTransport B S hS 𝒳 x₀).iso (op ((Over.post 𝒳.val.val.p).obj w)) r =
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map
        ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op).hom r := by
  have h1 := chartRingTransport_iso_map_unit_apply B S hS 𝒳 x₀ w r
  have h2 : ∀ t, ((ambientRingStructureSheaf B S hS 𝒳).obj.map
        ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op).hom
      (((ambientRingStructureSheaf B S hS 𝒳).obj.map
        ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left.op).hom t) = t := fun t => by
    rw [← RingCat.comp_apply, ← Functor.map_comp, ← op_comp, chartSliceUnitIso_inv_hom_left,
      op_id, CategoryTheory.Functor.map_id, RingCat.id_apply]
  exact (h2 _).symm.trans (congrArg _ h1)


/-- Restricting along an arrow and then along a left inverse of it is the identity, with the
universes of the rings and of the modules independent (`AlgebraicGeometry.Space` has the case of
equal universes). -/
theorem presheafOfModules_map_map_of_comp_eq_id {C : Type*} [Category C]
    {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{w} R₀) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) (x : M.obj X) : (M.map g).hom ((M.map f).hom x) = x := by
  rw [← PresheafOfModules.map_comp_apply, h, PresheafOfModules.map_id_apply]

/-- Two composites of restriction maps agree when the composites of the arrows do, with the
universes of the rings and of the modules independent (`AlgebraicGeometry.Space` has the case of
equal universes). -/
theorem presheafOfModules_map_map_eq {C : Type*} [Category C]
    {R₀ : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{w} R₀) {X Y Y' Z : Cᵒᵖ} (f₁ : X ⟶ Y)
    (g₁ : Y ⟶ Z) (f₂ : X ⟶ Y') (g₂ : Y' ⟶ Z) (h : f₁ ≫ g₁ = f₂ ≫ g₂) (x : M.obj X) :
    (M.map g₁).hom ((M.map f₁).hom x) = (M.map g₂).hom ((M.map f₂).hom x) := by
  rw [← PresheafOfModules.map_comp_apply, h, PresheafOfModules.map_comp_apply]

/-- The inverse image `x₀^{-1}` of sheaves of modules along the chart `x₀ : (Sch/U) ⟶ 𝒳`, at
module universe `u + 1` (the functor underlying `derivedModulePullback`). -/
abbrev chartPullback :
    SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) ⥤
      SheafOfModules.{u + 1}
        (ambientRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))) :=
  AlgebraicGeometry.Stack.modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p 𝒳.val.val.p
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids (objectStackMap B S hS 𝒳 x₀).hom.hom.toFunctor
    (objectStackMap B S hS 𝒳 x₀).hom.hom.w B.topology le_rfl

/-- **Sections over the chart.** For a sheaf `M` of `𝒪_𝒳`-modules and an object `w ⟶ x₀` of
`𝒳/x₀`, the sections of the inverse image `x₀^{-1} M` over `Ψ(w)` are the sections of `M` over
`w`, as modules over `𝒪(Ψ w) = 𝒪(w)`: restriction along the comparison `w ≅ Φ(Ψ w)`. -/
def chartSectionsIso (M : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
    (w : Over x₀) :
    ((chartPullback B S hS 𝒳 x₀).obj M).val.obj (op ((Over.post 𝒳.val.val.p).obj w)) ≅
      M.val.obj (op w.left) :=
  let Rw := (ambientRingStructureSheaf B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj.obj
      (op ((Over.post 𝒳.val.val.p).obj w))
  letI instN : Module Rw (M.val.obj (op w.left)) := ModuleCat.isModule _
  have e₁ : ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left.op ≫
      ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op = 𝟙 _ := by
    rw [← op_comp, chartSliceUnitIso_inv_hom_left]
    rfl
  have e₂ : ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op ≫
      ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left.op = 𝟙 _ := by
    rw [← op_comp, chartSliceUnitIso_hom_inv_left]
    rfl
  let f : ((chartPullback B S hS 𝒳 x₀).obj M).val.obj (op ((Over.post 𝒳.val.val.p).obj w)) →ₗ[Rw]
      M.val.obj (op w.left) :=
    { toFun := fun x => (M.val.map ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left.op).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x =>
        (M.val.map_smul ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left.op
          ((chartRingTransport B S hS 𝒳 x₀).iso (op ((Over.post 𝒳.val.val.p).obj w)) r) x).trans
          (congrArg (· • _) (chartRingTransport_iso_map_unit_apply B S hS 𝒳 x₀ w r)) }
  let g : M.val.obj (op w.left) →ₗ[Rw]
      ((chartPullback B S hS 𝒳 x₀).obj M).val.obj (op ((Over.post 𝒳.val.val.p).obj w)) :=
    { toFun := fun y => (M.val.map ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op).hom y
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r y => by
        change (M.val.map ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op).hom (r • y) =
          (fun (t : (ambientRingStructureSheaf B S hS 𝒳).obj.obj
                (op ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj w)).left))
              (z : M.val.obj (op ((chartSliceFunctor B S hS 𝒳 x₀).obj
                ((Over.post 𝒳.val.val.p).obj w)).left)) => t • z)
            ((chartRingTransport B S hS 𝒳 x₀).iso (op ((Over.post 𝒳.val.val.p).obj w)) r)
            ((M.val.map ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op).hom y)
        exact (M.val.map_smul ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op r y).trans
          (congrArg (fun t => (fun (t' : (ambientRingStructureSheaf B S hS 𝒳).obj.obj
                (op ((chartSliceFunctor B S hS 𝒳 x₀).obj ((Over.post 𝒳.val.val.p).obj w)).left))
              (z : M.val.obj (op ((chartSliceFunctor B S hS 𝒳 x₀).obj
                ((Over.post 𝒳.val.val.p).obj w)).left)) => t' • z) t
              ((M.val.map ((chartSliceUnitIso B S hS 𝒳 x₀).inv.app w).left.op).hom y))
            (chartRingTransport_iso_apply_eq B S hS 𝒳 x₀ w r).symm) }
  { hom := ModuleCat.homEquiv.symm f
    inv := ModuleCat.homEquiv.symm g
    hom_inv_id := ModuleCat.hom_ext (LinearMap.ext fun x =>
      presheafOfModules_map_map_of_comp_eq_id M.val _ _ e₁ x)
    inv_hom_id := ModuleCat.hom_ext (LinearMap.ext fun y =>
      presheafOfModules_map_map_of_comp_eq_id M.val _ _ e₂ y) }

/-- `chartSectionsIso` is natural in the sheaf of modules. -/
theorem chartSectionsIso_hom_naturality
    {M M' : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)} (φ : M ⟶ M')
    (w : Over x₀) :
    ((chartPullback B S hS 𝒳 x₀).map φ).val.app (op ((Over.post 𝒳.val.val.p).obj w)) ≫
        (chartSectionsIso B S hS 𝒳 x₀ M' w).hom =
      (chartSectionsIso B S hS 𝒳 x₀ M w).hom ≫ φ.val.app (op w.left) :=
  let : Module ((ambientRingStructureSheaf B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj.obj
        (op ((Over.post 𝒳.val.val.p).obj w))) (M'.val.obj (op w.left)) := ModuleCat.isModule _
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    (PresheafOfModules.naturality_apply φ.val
      ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app w).left.op x).symm)

/-- The comparison `w ≅ Φ(Ψ w)` commutes with the arrows of `𝒳/x₀`. -/
theorem chartSliceUnitIso_hom_left_naturality {z y : Over x₀} (a : z ⟶ y) :
    a.left ≫ ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app y).left =
      ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app z).left ≫
        ((chartSliceFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a)).left :=
  congrArg CommaMorphism.left ((chartSliceUnitIso B S hS 𝒳 x₀).hom.naturality a)

/-- `chartSectionsIso` commutes with the restriction maps along an arrow of `𝒳/x₀`. -/
theorem chartSectionsIso_hom_restrict (M : SheafOfModules.{u + 1}
    (ambientRingStructureSheaf B S hS 𝒳)) {z y : Over x₀} (a : z ⟶ y) (x) :
    (chartSectionsIso B S hS 𝒳 x₀ M z).hom.hom
        ((((chartPullback B S hS 𝒳 x₀).obj M).val.map ((Over.post 𝒳.val.val.p).map a).op).hom x) =
      (M.val.map a.left.op).hom ((chartSectionsIso B S hS 𝒳 x₀ M y).hom.hom x) := by
  show (M.val.map ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app z).left.op).hom
      ((M.val.map ((chartSliceFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a)).left.op).hom
        x) =
    (M.val.map a.left.op).hom
      ((M.val.map ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app y).left.op).hom x)
  exact presheafOfModules_map_map_eq M.val
    ((chartSliceFunctor B S hS 𝒳 x₀).map ((Over.post 𝒳.val.val.p).map a)).left.op
    ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app z).left.op
    ((chartSliceUnitIso B S hS 𝒳 x₀).hom.app y).left.op a.left.op
    (by rw [← op_comp, ← op_comp, chartSliceUnitIso_hom_left_naturality]) x

/-- The inverse image along the chart is additive. -/
instance additive_chartPullback : (chartPullback B S hS 𝒳 x₀).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

/-- **Sections over the chart, on complexes**: `Γ(Ψ w, x₀^{-1} I) ≅ Γ(w, I)` as complexes of
`𝒪(w)`-modules. -/
def chartSectionsComplexIso
    (I : CochainComplex (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)
    (w : Over x₀) :
    ((SheafOfModules.evaluation (ambientRingStructureSheaf B S hS
        (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)))
          (op ((Over.post 𝒳.val.val.p).obj w))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((chartPullback B S hS 𝒳 x₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((SheafOfModules.evaluation (ambientRingStructureSheaf B S hS 𝒳)
        (op w.left)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  HomologicalComplex.Hom.isoOfComponents (fun n => chartSectionsIso B S hS 𝒳 x₀ (I.X n) w)
    (fun i j _ => (chartSectionsIso_hom_naturality B S hS 𝒳 x₀ (I.d i j) w).symm)

/-- **The inverse image along the chart preserves K-injective complexes**: it is restriction to
`𝒳/x₀` (whose left adjoint, extension by zero, is exact) followed by the equivalence
`𝒳/x₀ ≌ (Sch/U)`. -/
theorem isKInjective_chartPullback_mapHomologicalComplex
    (I : CochainComplex (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((chartPullback B S hS 𝒳 x₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have := isKInjective_chartModuleEquivalence_overFunctor B S hS 𝒳 x₀ I
  exact CochainComplex.isKInjective_of_iso
    (HomologicalComplex.Hom.isoOfComponents
      (C₁ := ((chartModuleEquivalence B S hS 𝒳 x₀).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((SheafOfModules.overFunctor.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)
          x₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
      (fun n => ((modulePullbackChartIso B S hS 𝒳 x₀).app (I.X n)).symm)
      (fun i j _ => ((modulePullbackChartIso B S hS 𝒳 x₀).inv.naturality (I.d i j)).symm))

/-- `chartSectionsIso` commutes with the restriction maps along an arrow of `𝒳/x₀`, as
morphisms of modules. -/
theorem sectionsRestrict_app_chartSectionsIso_hom
    (M : SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) {z y : Over x₀}
    (a : z ⟶ y) :
    (chartSectionsIso B S hS 𝒳 x₀ M y).hom ≫
        (Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict
          (ambientRingStructureSheaf B S hS 𝒳) a.left).app M =
      (Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict
          (ambientRingStructureSheaf B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)))
          ((Over.post 𝒳.val.val.p).map a)).app ((chartPullback B S hS 𝒳 x₀).obj M) ≫
        (ModuleCat.restrictScalars ((ambientRingStructureSheaf B S hS
          (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj.map
            ((Over.post 𝒳.val.val.p).map a).op).hom).map (chartSectionsIso B S hS 𝒳 x₀ M z).hom :=
  let : Module ((ambientRingStructureSheaf B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))).obj.obj
        (op ((Over.post 𝒳.val.val.p).obj y)))
      ((SheafOfModules.evaluation (ambientRingStructureSheaf B S hS 𝒳) (op z.left) ⋙
        ModuleCat.restrictScalars ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.left.op).hom).obj
          M) := ModuleCat.isModule _
  ModuleCat.hom_ext (LinearMap.ext fun x =>
    (chartSectionsIso_hom_restrict B S hS 𝒳 x₀ M a x).symm)

/-- Conjugating a commutative square by isomorphisms of its source and target. -/
theorem comp_map_inv_eq_inv_comp_of_hom_comp_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A A' : D} {B B' : C} (e₁ : A' ≅ A) (e₂ : B' ≅ B) (f : A ⟶ F.obj B)
    (f' : A' ⟶ F.obj B') (h : e₁.hom ≫ f = f' ≫ F.map e₂.hom) :
    f ≫ F.map e₂.inv = e₁.inv ≫ f' := by
  rw [Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, ← F.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

section FlatPullbackQuasicoherent

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat preservesCoveringPullbacks_inclusion_topology
  essentiallySmall_obj_largeSections essentiallySmall_flatFppf_largeSections
  hasSheafify_topology_largeSections wEqualsLocallyBijective_topology_largeSections

/-- **The inverse image along a flat 1-morphism preserves quasi-coherence on the flat-fppf
sites** (Stacks 03DM for clause (6) of Stacks 03DL): `(f')^{-1}` is restriction along the
continuous and cocontinuous functor `f'`, read through the identification of structure sheaves
Stacks 06TW. -/
theorem isQuasicoherentOnSite_moduleSubsiteInverseImage {𝒳' 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳' ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f)
    (M : SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴))
    (hM : M.IsQuasicoherentOnSite) :
    ((moduleSubsiteInverseImage B S hS f hf).obj M).IsQuasicoherentOnSite := by
  have := isContinuous_subsiteFunctor_topology B S hS f hf
  have := isCocontinuous_subsiteFunctor_topology B S hS f hf
  have : ∀ X, (Over.post (X := X) (primedSiteFunctor B S hS f hf)).IsContinuous
      ((topology B S hS 𝒳').over X) ((topology B S hS 𝒴).over
        ((primedSiteFunctor B S hS f hf).obj X)) := fun X =>
    Functor.isContinuous_overPost _ _ _ X
  refine Stacks.SheafOfModules.isQuasicoherentOnSite_pushforward (primedSiteFunctor B S hS f hf)
    (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm) ?_ M hM
  intro X Y g
  let G' := Over.post (X := X) (primedSiteFunctor B S hS f hf) ⋙ Over.map g
  have _ : G'.IsCocontinuous ((topology B S hS 𝒳').over X) ((topology B S hS 𝒴).over Y) :=
    isCocontinuous_comp _ _ ((topology B S hS 𝒳').over X)
      ((topology B S hS 𝒴).over ((primedSiteFunctor B S hS f hf).obj X))
  have _ : HasSheafify ((topology B S hS 𝒳').over X) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : ((topology B S hS 𝒳').over X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify ((topology B S hS 𝒴).over Y) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : ((topology B S hS 𝒴).over Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits G' _

end FlatPullbackQuasicoherent

section ChartCovering

/-- **Lifting a Zariski covering of the scheme under an object.** For an object `W` of `𝒳` and an
open cover `O` of the scheme under `W`, the cartesian lifts of `W` along the members of `O` form a
covering family of `W` for the Zariski topology `𝒳` inherits. -/
theorem exists_lift_openCover_mem_zariski (W : 𝒳.val.val.obj)
    (O : (B.inclusion.obj (𝒳.val.val.p.obj W).left).OpenCover.{u + 1}) :
    ∃ (y : O.I₀ → 𝒳.val.val.obj) (φ : ∀ i, y i ⟶ W),
      (∀ i, ∃ e : B.inclusion.obj (𝒳.val.val.p.obj (y i)).left ≅ O.X i,
        e.hom ≫ O.f i = B.inclusion.map (𝒳.val.val.p.map (φ i)).left) ∧
      Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .zariski W := by
  classical
  let p := 𝒳.val.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  let V : PreZeroHypercover.{u + 1} (p.obj W).left :=
    { I₀ := O.I₀
      X := fun i => ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) (p.obj W).left.2⟩
      f := fun i => ObjectProperty.homMk (O.f i) }
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .zariski (p.obj W) := by
    have hZ : IsZariskiCovering (⟨(p.obj W).left, V⟩ : Covering B.Schemes) := by
      show (V.map B.inclusion).presieve₀ ∈ Scheme.zariskiPrecoverage _
      simpa [V, PreZeroHypercover.map] using O.mem₀
    obtain ⟨⟨T', E'⟩, hE', hCE⟩ := B.zariskiCovering_has_representative ⟨(p.obj W).left, V⟩ hZ
    obtain ⟨hbase, hfamily⟩ := hCE
    change (p.obj W).left = T' at hbase
    cases hbase
    have hgen : Sieve.generate V.presieve₀ ∈ B.zariskiTopology (p.obj W).left := by
      rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
        (show PreZeroHypercover.CombinatoriallyEquivalent V E' by simpa using hfamily)]
      exact Precoverage.generate_mem_toGrothendieck ⟨E', rfl, hE'⟩
    let Vover : PreZeroHypercover.{u + 1} (p.obj W) := ⟨V.I₀, Vobj, vmap⟩
    have hgenOver :
        Sieve.generate Vover.presieve₀ ∈ B.zariskiTopology.over (B.obj hS) (p.obj W) := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
        ← Sieve.arrows_generate_map_eq_functorPushforward]
      simpa [Vover, Vobj, vmap, PreZeroHypercover.presieve₀, PreZeroHypercover.map] using hgen
    exact hgenOver
  choose y φ hφ using fun j => hp.exists_lift (vmap j) W rfl
  have hdom : ∀ j, p.obj (y j) = Vobj j := fun j => by
    have := hφ j
    exact IsHomLift.domain_eq p (vmap j) (φ j)
  have hcart : ∀ j, p.IsStronglyCartesian (p.map (φ j)) (φ j) :=
    fun j => hp.isStronglyCartesian (φ j)
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    have := hφ j
    simpa using IsHomLift.fac p (vmap j) (φ j)
  have hfib : p.IsFibered := hp.isFibered
  refine ⟨y, φ, fun j => ⟨B.inclusion.mapIso (eqToIso (congrArg Comma.left (hdom j))), ?_⟩, ?_⟩
  · have := hφ j
    rw [IsHomLift.fac' p (vmap j) (φ j)]
    simp [vmap, V]
  · refine (Functor.isInheritedTopology_inheritedTopology p
      (BigFppfOver.baseOverTopology B S hS .zariski) y φ hcart).2 ?_
    refine (BigFppfOver.baseOverTopology B S hS .zariski).superset_covering ?_ hBcover
    intro Z g hg
    rw [Sieve.mem_ofArrows_iff] at hg
    obtain ⟨j, a, rfl⟩ := hg
    exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed
      (hvmapmem j) a

/-- **An object mapping into an affine open of a flat object maps to a flat object over an affine
scheme.** If `d : w ⟶ x₁` is an arrow to a flat object whose underlying morphism of schemes factors
through an affine open `U_i ⊆ X` of the scheme `X` under `x₁`, then `w` has an arrow to the
restriction of `x₁` to `U_i`, a flat object over the affine scheme `U_i`. -/
theorem exists_flatAffine_of_factor (x₁ : FlatFppf B S hS 𝒳) {w : 𝒳.val.val.obj}
    (d : w ⟶ x₁.obj) (Ui : Scheme.{u}) [IsAffine Ui]
    (fi : Ui ⟶ B.inclusion.obj (𝒳.val.val.p.obj x₁.obj).left) [AlgebraicGeometry.IsOpenImmersion fi]
    (gi : B.inclusion.obj (𝒳.val.val.p.obj w).left ⟶ Ui)
    (hgi : gi ≫ fi = B.inclusion.map (𝒳.val.val.p.map d).left) :
    ∃ x₀ : FlatFppf B S hS 𝒳,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₀.obj)) ∧
        Nonempty (w ⟶ x₀.obj) := by
  let p := 𝒳.val.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  let UiB : B.Schemes := ⟨Ui, Scheme.size_lt_of_isOpenImmersion fi (p.obj x₁.obj).left.2⟩
  let fiB : UiB ⟶ (p.obj x₁.obj).left := ObjectProperty.homMk fi
  let Xobj : BigFppfOver B S hS := Over.mk (fiB ≫ (p.obj x₁.obj).hom)
  let xmap : Xobj ⟶ p.obj x₁.obj := Over.homMk fiB
  obtain ⟨x₁i, ψ, hψ⟩ := hp.exists_lift xmap x₁.obj rfl
  have hdom : p.obj x₁i = Xobj := IsHomLift.domain_eq p xmap ψ
  have hψmap : p.map ψ = eqToHom hdom ≫ xmap := by
    rw [IsHomLift.fac' p xmap ψ]
    simp
  have hflat : Flat (B.inclusion.map (p.map ψ).left) := by
    rw [hψmap, Over.comp_left, Functor.map_comp]
    have : Flat (B.inclusion.map xmap.left) := inferInstanceAs (Flat fi)
    have key : ∀ {A A' : Scheme.{u}} (e : A = A') {Z : Scheme.{u}} (f : A' ⟶ Z) [Flat f],
        Flat (eqToHom e ≫ f) := by
      intro A A' e Z f _
      subst e
      simpa
    simp only [Over.eqToHom_left, eqToHom_map]
    exact key _ _
  let x₀ : FlatFppf B S hS 𝒳 :=
    ⟨x₁i, flatObject_of_flat B S hS 𝒳 ψ hflat x₁.property⟩
  have haff : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₀.obj)) := by
    show IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₁i))
    rw [hdom]
    exact inferInstanceAs (IsAffine Ui)
  have hw : ObjectProperty.homMk (X := (p.obj w).left) (Y := UiB) gi ≫ fiB ≫ (p.obj x₁.obj).hom =
      (p.obj w).hom := by
    have h₂ : (ObjectProperty.homMk (X := (p.obj w).left) (Y := UiB) gi ≫ fiB :
        (p.obj w).left ⟶ (p.obj x₁.obj).left) = (p.map d).left := B.inclusion.map_injective hgi
    rw [← Category.assoc, h₂, Over.w (p.map d)]
  let g : p.obj w ⟶ Xobj := Over.homMk (ObjectProperty.homMk (X := (p.obj w).left) (Y := UiB) gi) hw
  have hf' : p.map d = g ≫ xmap := Over.OverMorphism.ext (B.inclusion.map_injective hgi).symm
  have := hψ
  have := hp.isStronglyCartesian_homLift xmap ψ
  exact ⟨x₀, haff, ⟨Functor.IsStronglyCartesian.map p xmap ψ hf' d⟩⟩

/-- **Zariski locally, an object over a flat object maps to a flat object over an affine scheme.**
If `z` has an arrow `c` to a flat object `x₁`, then the arrows `z' ⟶ z` from objects over affine
schemes with an arrow to a flat object over an affine scheme generate a covering sieve of `z` for
the Zariski topology: pull an affine open cover of the scheme under `x₁` back along `c` and refine
it by affine opens. -/
theorem generate_affine_flatAffine_mem_zariski (z : 𝒳.val.val.obj) (x₁ : FlatFppf B S hS 𝒳)
    (c : z ⟶ x₁.obj) :
    Sieve.generate (fun (z' : 𝒳.val.val.obj) (_ : z' ⟶ z) =>
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z')) ∧
        ∃ x₀ : FlatFppf B S hS 𝒳,
          IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₀.obj)) ∧
            Nonempty (z' ⟶ x₀.obj)) ∈
      BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .zariski z := by
  classical
  let p := 𝒳.val.val.p
  let X := B.inclusion.obj (p.obj x₁.obj).left
  let m : B.inclusion.obj (p.obj z).left ⟶ X := B.inclusion.map (p.map c).left
  let 𝒰 := X.affineOpenCover.openCover
  let 𝒰' : (B.inclusion.obj (p.obj z).left).OpenCover := 𝒰.pullback₁ m
  let O : (B.inclusion.obj (p.obj z).left).OpenCover.{u + 1} :=
    { I₀ := ULift.{u + 1} (Σ i : 𝒰'.I₀, (𝒰'.X i).affineOpenCover.I₀)
      X := fun k => Spec ((𝒰'.X k.down.1).affineOpenCover.X k.down.2)
      f := fun k => (𝒰'.X k.down.1).affineOpenCover.f k.down.2 ≫ 𝒰'.f k.down.1
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, fun k ↦ ?_⟩
        · obtain ⟨y, hy⟩ := 𝒰'.covers x
          obtain ⟨y', hy'⟩ := (𝒰'.X (𝒰'.idx x)).affineOpenCover.covers y
          refine ⟨⟨⟨𝒰'.idx x, (𝒰'.X (𝒰'.idx x)).affineOpenCover.idx y⟩⟩, y', ?_⟩
          simp [hy', hy]
        · have := (𝒰'.X k.down.1).affineOpenCover.map_prop k.down.2
          have := 𝒰'.map_prop k.down.1
          infer_instance }
  obtain ⟨y, φ, hφ, hcov⟩ := exists_lift_openCover_mem_zariski B S hS 𝒳 z O
  refine (BigFppfOver.associatedTopology B S hS p .zariski).superset_covering ?_ hcov
  intro Z g hg
  obtain ⟨W, a, b, ⟨k⟩, rfl⟩ := hg
  have hk : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj (y k))) ∧
      ∃ x₀ : FlatFppf B S hS 𝒳,
        IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₀.obj)) ∧
          Nonempty (y k ⟶ x₀.obj) := ⟨?_, ?_⟩
  · exact (Sieve.generate _).downward_closed (Sieve.le_generate _ _ (φ k) hk) a
  · obtain ⟨e, -⟩ := hφ k
    have : IsAffine (O.X k) := inferInstanceAs (IsAffine (Spec _))
    exact IsAffine.of_isIso e.hom
  · obtain ⟨e, he⟩ := hφ k
    let i := k.down.1
    have : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec _))
    have := 𝒰.map_prop i
    refine exists_flatAffine_of_factor B S hS 𝒳 x₁ (φ k ≫ c) (𝒰.X i) (𝒰.f i)
      (e.hom ≫ (𝒰'.X i).affineOpenCover.f k.down.2 ≫ pullback.snd m (𝒰.f i)) ?_
    have he' : (e.hom ≫ (𝒰'.X i).affineOpenCover.f k.down.2) ≫ pullback.fst m (𝒰.f i) =
        B.inclusion.map (𝒳.val.val.p.map (φ k)).left := (Category.assoc _ _ _).trans he
    have hpc : (𝒳.val.val.p.map (φ k)).left ≫ (𝒳.val.val.p.map c).left =
        (𝒳.val.val.p.map (φ k ≫ c)).left := by
      rw [CategoryTheory.Functor.map_comp]
      rfl
    exact ((congrArg (e.hom ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm).trans
      ((congrArg ((e.hom ≫ (𝒰'.X i).affineOpenCover.f k.down.2) ≫ ·)
        (pullback.condition (f := m) (g := 𝒰.f i)).symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ m) he').trans
            ((B.inclusion.map_comp _ _).symm.trans (congrArg (fun t => B.inclusion.map t) hpc)))))

/-- **The covering of the third paragraph of the proof of Stacks 0H15.** Every object `x'` of
`𝒳_{affine}` has a covering sieve for the associated affine étale topology all of whose members
map to a flat object of `𝒳` over an affine scheme: by Stacks 06XH an étale covering of `x'` lifts
to a smooth surjective chart `(Sch/X) ⟶ 𝒳`, and the affine opens of `X` refine it. -/
theorem exists_flatAffine_sieve_mem (x' : AffineCategory B S hS 𝒳.val.val.p) :
    ∃ T : Sieve x', T ∈ associatedAffineTopology B S hS 𝒳.val.val.p
        (BigAffineFppf.siteKindTopology B S hS .etale) x' ∧
      ∀ ⦃y : AffineCategory B S hS 𝒳.val.val.p⦄ (g : y ⟶ x'), T g →
        ∃ x₀ : FlatFppf B S hS 𝒳,
          IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₀.obj)) ∧
            Nonempty (y.obj ⟶ x₀.obj) := by
  let p := 𝒳.val.val.p
  have hp : p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  let L : 𝒳.val.val.obj → Prop := fun z => ∃ x₀ : FlatFppf B S hS 𝒳,
    IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj x₀.obj)) ∧ Nonempty (z ⟶ x₀.obj)
  let T : Sieve x' :=
    { arrows := fun y _ => L y.obj
      downward_closed := fun {_ _} _ hy h => by
        obtain ⟨x₀, ha, ⟨d⟩⟩ := hy
        exact ⟨x₀, ha, ⟨h.hom ≫ d⟩⟩ }
  refine ⟨T, ?_, fun y g hg => hg⟩
  have := AffineCategory.isDenseSubsite_inclusion_siteKind B S hS p hp .etale
  rw [← (AffineCategory.inclusion B S hS p).functorPushforward_mem_iff
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .etale))
    (BigFppfOver.associatedTopology B S hS p .etale)]
  obtain ⟨x₁, hsm, hsurj⟩ := exists_smooth_surjective_objectMorphism B S hS 𝒳
  have hx₁ := flatObject_of_smoothObject B S hS 𝒳 hsm
  obtain ⟨t, α, hα⟩ := Stack.exists_etaleLocalLift B S hS (objectStackMap B S hS 𝒳 x₁) hsurj hsm
    x'.obj
  have hle : BigFppfOver.associatedTopology B S hS p .zariski ≤
      BigFppfOver.associatedTopology B S hS p .etale := by
    apply Precoverage.toGrothendieck_mono
    intro X R hR
    exact ⟨hR.1, BigFppfOver.baseOverTopology_zariski_le_etale B S hS _ hR.2⟩
  refine (BigFppfOver.associatedTopology B S hS p .etale).transitive hα _ ?_
  intro Z k hk
  obtain ⟨Z', h, g, hg, rfl⟩ := hk
  cases hg
  have hZ := generate_affine_flatAffine_mem_zariski B S hS 𝒳 Z ⟨x₁, hx₁⟩
    (h ≫ (chartLift B S hS 𝒳 x₁ t).φ)
  refine (BigFppfOver.associatedTopology B S hS p .etale).superset_covering ?_ (hle _ hZ)
  rw [Sieve.generate_le_iff]
  rintro z' q ⟨haff, hLz'⟩
  exact ⟨⟨z', haff⟩, ObjectProperty.homMk (q ≫ h ≫ α), 𝟙 z', hLz', (Category.id_comp _).symm⟩

end ChartCovering

section Transfer

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
attribute [local instance] isGrothendieckAbelian_ambientModulesSucc
attribute [-instance] Stacks.ModulesOnACategory.QuasiCoherentEquivalence.rsPreservesFiniteLimits
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.rsPreservesFiniteColimits
attribute [local instance] restrictScalarsSucc_preservesFiniteLimits
  restrictScalarsSucc_preservesFiniteColimits
attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology
  Stacks.hasSheafCompose_forget₂_commRingCat preservesCoveringPullbacks_inclusion_topology
  essentiallySmall_obj_largeSections essentiallySmall_flatFppf_largeSections
  hasSheafify_topology_largeSections wEqualsLocallyBijective_topology_largeSections

/-- **The base change map of Stacks 0H15 along an arrow over the chart, at a K-injective
complex.** For a K-injective complex `I` on `𝒳_fppf` and an arrow `a : z ⟶ y` of `𝒳/x₀`, the map
of Stacks 0H15 for `I` along `a` is invertible exactly when the map of Stacks 0H15 for
`x₀^{-1} I` along `Ψ(a)` in `(Sch/U)_fppf` is: the inverse image preserves K-injectivity, and its
sections over `Ψ(w)` are the sections of `I` over `w`, compatibly with restriction. -/
theorem isIso_derivedSectionsBaseChange_quotient_iff_chart
    (I : CochainComplex (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)
    [I.IsKInjective] {z y : Over x₀} (a : z ⟶ y) :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 a.left (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ↔
      IsIso (derivedSectionsBaseChange B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))
        ((Over.post 𝒳.val.val.p).map a) (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((chartPullback B S hS 𝒳 x₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) := by
  have := isKInjective_chartPullback_mapHomologicalComplex B S hS 𝒳 x₀ I
  rw [isIso_derivedSectionsBaseChange_quotient_iff B S hS 𝒳 I a.left,
    isIso_derivedSectionsBaseChange_quotient_iff B S hS
      (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)) _ ((Over.post 𝒳.val.val.p).map a)]
  refine Functor.IsUniversalArrow.iff_of_iso
    (DerivedCategory.Q.mapIso (chartSectionsComplexIso B S hS 𝒳 x₀ I y)).symm
    (DerivedCategory.Q.mapIso (chartSectionsComplexIso B S hS 𝒳 x₀ I z)).symm ?_
  refine Functor.map_comp_app_comp_map_map_eq DerivedCategory.Q DerivedCategory.Q
    ((ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.left.op).hom).mapHomologicalComplex
        (ComplexShape.up ℤ))
    (ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.left.op).hom).mapDerivedCategory
    (ModuleCat.restrictScalars.{u + 1}
      ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.left.op).hom).mapDerivedCategoryFactors.inv
    (chartSectionsComplexIso B S hS 𝒳 x₀ I z).inv (chartSectionsComplexIso B S hS 𝒳 x₀ I y).inv
    _ _ ?_
  exact comp_map_inv_eq_inv_comp_of_hom_comp_eq _ _ _ _ _
    (HomologicalComplex.hom_ext _ _ fun n =>
      sectionsRestrict_app_chartSectionsIso_hom B S hS 𝒳 x₀ (I.X n) a)

/-- **The base change map of Stacks 0H15 along an arrow over the chart.** For `K` in `D(𝒪_𝒳)` and
an arrow `a : z ⟶ y` of `𝒳/x₀`, the map of Stacks 0H15 for `K` along `a` is invertible exactly when
the map of Stacks 0H15 for the inverse image `x₀^{-1} K` along `Ψ(a)` in `(Sch/U)_fppf` is: the
restriction of `K` to `(Sch/X)_fppf = 𝒳/f` computes the same derived sections (Stacks 075C). -/
theorem isIso_derivedSectionsBaseChange_iff_chart
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    {z y : Over x₀} (a : z ⟶ y) :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 a.left K) ↔
      IsIso (derivedSectionsBaseChange B S hS (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))
        ((Over.post 𝒳.val.val.p).map a)
        ((derivedModulePullback B S hS (objectStackMap B S hS 𝒳 x₀)).obj K)) := by
  obtain ⟨I, hI, ⟨e⟩⟩ : ∃ I : CochainComplex
      (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ, I.IsKInjective ∧
        Nonempty (K ≅ DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
    obtain ⟨I, f, hI, hf⟩ := Stacks.Cohomology.Localization.enoughKInjectives
      (DerivedCategory.Qh.objPreimage K).as
    have hiso : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f)) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)
    exact ⟨I, hI, ⟨(DerivedCategory.Qh.objObjPreimageIso K).symm ≪≫
      @asIso _ _ _ _
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map f))
        hiso⟩⟩
  have := hI
  have := preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p 𝒳.val.val.p
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids (objectStackMap B S hS 𝒳 x₀).hom.hom.toFunctor
    (objectStackMap B S hS 𝒳 x₀).hom.hom.w B.topology le_rfl
  have := preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.val.p 𝒳.val.val.p
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀)).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids (objectStackMap B S hS 𝒳 x₀).hom.hom.toFunctor
    (objectStackMap B S hS 𝒳 x₀).hom.hom.w B.topology le_rfl
  refine (isIso_derivedSectionsBaseChange_iff_of_iso B S hS 𝒳 e a.left).trans
    ((isIso_derivedSectionsBaseChange_quotient_iff_chart B S hS 𝒳 x₀ I a).trans
      (isIso_derivedSectionsBaseChange_iff_of_iso B S hS
        (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀))
        ((derivedModulePullback B S hS (objectStackMap B S hS 𝒳 x₀)).mapIso e ≪≫
          ((chartPullback B S hS 𝒳 x₀).mapDerivedCategoryFactorsh.app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) _).symm)

/-- **The inverse image along a flat 1-morphism preserves `D_QCoh` of the flat-fppf sites**: it
is exact, so it commutes with cohomology, and it preserves quasi-coherence. -/
theorem derivedCategoryB_flatQuasicoherentModulesSucc_derivedModuleSubsiteInverseImage
    {𝒳' 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳' ⟶ 𝒴)
    (hf : AlgebraicStacks.IsFlat B S hS f)
    (H : DerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒴)))
    (hH : DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒴) H) :
    DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒳')
      ((derivedModuleSubsiteInverseImage B S hS f hf).obj H) := by
  have := isContinuous_subsiteFunctor_topology B S hS f hf
  have := isCocontinuous_subsiteFunctor_topology B S hS f hf
  have : PreservesFiniteLimits (moduleSubsiteInverseImage B S hS f hf) :=
    (_root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
      (primedSiteFunctor B S hS f hf)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)).1
  have : PreservesFiniteColimits (moduleSubsiteInverseImage B S hS f hf) :=
    (_root_.SheafOfModules.exactFunctor_pushforward_of_isCocontinuous.{u + 1, u, u + 1, u, u, u + 1}
      (primedSiteFunctor B S hS f hf)
      (eqToHom (subsiteRingStructureSheaf_inverseImageRing B S hS f hf).symm)).2
  intro n
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((moduleSubsiteInverseImage B S hS f hf).mapDerivedCategoryHomologyIso n).app H).symm
    (isQuasicoherentOnSite_moduleSubsiteInverseImage B S hS f hf _ (hH n))

/-- **Stacks 0H15 along an arrow over a flat affine chart, from the case of an affine scheme.**
Let `H ∈ D_QCoh(𝒪_{𝒳_{flat,fppf}})`, `x₀` a flat object of `𝒳` over an affine scheme, and
`b : z ⟶ y` an arrow of `𝒳_{affine}` with an arrow `y ⟶ x₀`. If the conclusion of Stacks 0H15
holds for every `(Sch/X)_fppf` with `X` affine (`haff`, the last paragraph of the source's proof),
then the map `RΓ(y, Lg_!H) ⊗^L 𝒪(z) ⟶ RΓ(z, Lg_!H)` is a quasi-isomorphism: `b` is the image of an
arrow of `(Aff/U)` under `(Sch/U)_fppf = 𝒳/x₀ → 𝒳` (Stacks 075C), derived sections over `𝒳/x₀`
are those over `𝒳`, and the restriction of `Lg_!H` to `(Sch/U)_fppf` is `L(g')_!(f')^*H`
(Stacks 07AV). -/
theorem isIso_derivedSectionsBaseChange_derivedModuleLowerShriekSucc_of_hom_flatAffine
    (haff : ∀ (X : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj X) →
      ∀ (H : DerivedCategory (SheafOfModules.{u + 1}
          (subsiteRingStructureSheaf B S hS (schemeStack.{u, w} B S hS X)))),
        DerivedCategoryB.derivedCategoryB
          (flatQuasicoherentModulesSucc B S hS (schemeStack.{u, w} B S hS X)) H →
        HasAffineDerivedSectionsBaseChange B S hS (schemeStack.{u, w} B S hS X)
          ((derivedModuleLowerShriekSucc B S hS (schemeStack.{u, w} B S hS X)).obj H))
    (H : DerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)))
    (hH : DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒳) H)
    {z y : 𝒳.val.val.obj} (b : z ⟶ y)
    (hz : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj z)))
    (hy : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)))
    (x₀ : FlatFppf B S hS 𝒳)
    (hx₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x₀.obj)))
    (g : y ⟶ x₀.obj) :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 b
      ((derivedModuleLowerShriekSucc B S hS 𝒳).obj H)) := by
  let a : (Over.mk (b ≫ g) : Over x₀.obj) ⟶ Over.mk g := Over.homMk b
  refine (isIso_derivedSectionsBaseChange_iff_chart B S hS 𝒳 x₀.obj _ a).2 ?_
  refine (isIso_derivedSectionsBaseChange_iff_of_iso B S hS
    (schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x₀.obj))
    ((moduleDerivedLowerShriekBaseChangeIso B S hS (objectStackMap B S hS 𝒳 x₀.obj)
      x₀.property).app H) _).2 ?_
  exact haff _ hx₀ _
    (derivedCategoryB_flatQuasicoherentModulesSucc_derivedModuleSubsiteInverseImage B S hS
      (objectStackMap B S hS 𝒳 x₀.obj) x₀.property H hH) _ hz hy

/-- **Stacks 0H15, reduced to the stack of an affine scheme** (the third and fourth paragraphs of
the source's proof). Let `𝒳` be an algebraic stack and `H ∈ D_QCoh(𝒪_{𝒳_{flat,fppf}})`, at module
universe `u + 1`. If the conclusion of Stacks 0H15 holds for `(Sch/X)_fppf` for every affine
scheme `X` (`haff`, the last paragraph of the source's proof), then it holds for `𝒳`: for every
morphism `x ⟶ x'` of `𝒳_{affine}` the map `RΓ(x', Lg_!H) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, Lg_!H)` is a
quasi-isomorphism.

The property is étale local on `x'` (the second paragraph,
`AlgebraicGeometry.Stack.FlatFppf.hasAffineDerivedSectionsBaseChange_of_covering`, applicable
since `Lg_!H ∈ D_{LQCoh^fbc}` by Stacks 07B9 (2)(c)); étale locally `x'` lifts to a smooth chart
and then into an affine open of it (Stacks 06XH,
`AlgebraicGeometry.Stack.FlatFppf.exists_flatAffine_sieve_mem`); and over such a flat affine
chart Stacks 07AV identifies the restriction of `Lg_!H` with `L(g')_!(f')^*H`
(`isIso_derivedSectionsBaseChange_derivedModuleLowerShriekSucc_of_hom_flatAffine`). -/
theorem hasAffineDerivedSectionsBaseChange_derivedModuleLowerShriekSucc_of_affine
    (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (haff : ∀ (X : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj X) →
      ∀ (H : DerivedCategory (SheafOfModules.{u + 1}
          (subsiteRingStructureSheaf B S hS (schemeStack.{u, w} B S hS X)))),
        DerivedCategoryB.derivedCategoryB
          (flatQuasicoherentModulesSucc B S hS (schemeStack.{u, w} B S hS X)) H →
        HasAffineDerivedSectionsBaseChange B S hS (schemeStack.{u, w} B S hS X)
          ((derivedModuleLowerShriekSucc B S hS (schemeStack.{u, w} B S hS X)).obj H))
    (H : DerivedCategory (SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)))
    (hH : DerivedCategoryB.derivedCategoryB (flatQuasicoherentModulesSucc B S hS 𝒳) H) :
    HasAffineDerivedSectionsBaseChange B S hS 𝒳 ((derivedModuleLowerShriekSucc B S hS 𝒳).obj H) :=
  hasAffineDerivedSectionsBaseChange_of_covering B S hS 𝒳 E h _
    (derivedCategoryB_derivedModuleLowerShriekSucc B E h S hS 𝒳 H hH) .etale fun x' => by
      obtain ⟨T, hT, hT'⟩ := exists_flatAffine_sieve_mem B S hS 𝒳 x'
      refine ⟨T, hT, fun y g hg z b => ?_⟩
      obtain ⟨x₀, hx₀, ⟨d⟩⟩ := hT' g hg
      exact isIso_derivedSectionsBaseChange_derivedModuleLowerShriekSucc_of_hom_flatAffine B S hS 𝒳
        haff H hH b.hom z.property y.property x₀ hx₀ d

end Transfer

end AlgebraicGeometry.Stack.FlatFppf

end
