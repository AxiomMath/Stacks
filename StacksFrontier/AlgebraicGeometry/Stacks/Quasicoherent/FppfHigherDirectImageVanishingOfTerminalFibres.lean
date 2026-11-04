module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModuleDirectImageInitialChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExactOfLocallyExactSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineCoveringFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineRepresentableStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange

/-!
# Higher direct images vanish along 1-morphisms with acyclic affine fibres

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and `F` a module on the fppf site of `𝒳`,
at module universe `u + 1`. If the fibre of `f` over the chart `Sch/V ⟶ 𝒴` of every object over an
affine scheme has a terminal object, and the cohomology of `F` at every object of `𝒳` over an
affine scheme vanishes in degree `n`, then `Rⁿf_* F = 0`: computing `Rⁿf_*` with an injective
resolution `I•` of `F`, the sections at such a chart of `f_* I•` are the sections of `I•` at the
first projection of the terminal object
(`AlgebraicGeometry.Stack.moduleSheafPushforwardEvaluationIsoOfTerminal`), whose cohomology is the
vanishing cohomology of `F` there; and a complex of sheaves of modules which is exact on the
sections over a covering family is exact (`SheafOfModules.exact_of_locally_exists_preimage`).

This is the vanishing half of the affine case of Stacks 0770 / 0771: for stacks representable by
affine schemes the fibres are again representable by affine schemes, hence have terminal objects
(`AlgebraicGeometry.Stack.AlgebraicStacks.exists_isTerminal_of_isAffineRepresentable`).

## Main results

* `AlgebraicGeometry.Stack.isZero_rightDerived_moduleSheafPushforward_of_isTerminal_fibre`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isZero_fppfHigherDirectImage_of_isAffineRepresentable`.

## References

* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Stack

universe u w

section Generic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hfc : f ⋙ p𝒴 = p𝒳)
  [HasSheafify (associatedTopology B S hS p𝒳 B.topology) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS p𝒳 B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify (associatedTopology B S hS p𝒴 B.topology) AddCommGrpCat.{u + 1}]
  [(associatedTopology B S hS p𝒴 B.topology).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

attribute [local irreducible] moduleSheafPushforward

/-- **Higher direct images vanish when the fibres over a covering family of charts have acyclic
terminal objects**, for a 1-morphism of categories fibred in groupoids. Let `P` be a property of
the objects of `𝒴` such that every object is covered by objects with `P`; suppose that for every
`y` with `P` the 2-fibre product of `f` with the chart `Sch/V ⟶ 𝒴` of `y` has a terminal object
`t` whose first projection satisfies `Q`, and that the `n`-th right derived functor of the
sections at every object with `Q` vanishes on `F`. Then `Rⁿf_* F = 0`. -/
theorem isZero_rightDerived_moduleSheafPushforward_of_isTerminal_fibre
    (F : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl)) (n : ℕ)
    (P : 𝒴 → Prop) (Q : 𝒳 → Prop)
    (hcov : ∀ T : 𝒴, ∃ U ∈ associatedTopology B S hS p𝒴 B.topology T,
      ∀ ⦃V : 𝒴⦄ (a : V ⟶ T), U a → ∃ (W : 𝒴) (b : V ⟶ W) (c : W ⟶ T), b ≫ c = a ∧ P W)
    (hfib : ∀ y : 𝒴, P y →
      ∃ t : TwoFibreProductOver p𝒳 (Over.forget (p𝒴.obj y)) p𝒴 f
        (Functor.TwoYoneda.liftFunctor p𝒴 h𝒴 (p𝒴.obj y) (Functor.Fiber.mk (a := y) rfl)),
        Nonempty (IsTerminal t) ∧ Q t.x)
    (hvan : ∀ x : 𝒳, Q x →
      letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p𝒳 h𝒳 B.topology le_rfl
      IsZero (((SheafOfModules.evaluation
        (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl) (op x)).rightDerived n).obj F)) :
    letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p𝒳 h𝒳 B.topology le_rfl
    IsZero (((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
      B.topology le_rfl).rightDerived n).obj F) := by
  let := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS p𝒳 h𝒳 B.topology le_rfl
  let fF := moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc
    B.topology le_rfl
  let R := injectiveResolution F
  refine IsZero.of_iso ?_ (R.isoRightDerivedObj fF n)
  change IsZero (((fF.mapHomologicalComplex _).obj R.cocomplex).homology n)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff]
  set C := ((fF.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex).sc n
  apply SheafOfModules.exact_of_locally_exists_preimage
  intro T x hx
  obtain ⟨U, hU, hP⟩ := hcov T
  refine ⟨U, hU, fun V₀ a₀ ha₀ => ?_⟩
  obtain ⟨V, b, a, rfl, hV⟩ := hP a₀ ha₀
  suffices hW : ∃ y, C.f.val.app (op V) y = C.X₂.val.map a.op x by
    obtain ⟨y, hy⟩ := hW
    refine ⟨C.X₁.val.map b.op y, ?_⟩
    refine (ConcreteCategory.congr_hom (C.f.val.naturality b.op) y).trans ?_
    rw [ConcreteCategory.comp_apply, hy]
    exact (C.X₂.val.map_comp_apply a.op b.op x).symm
  obtain ⟨t, ⟨ht⟩, hQ⟩ := hfib V hV
  let E := fun k : ℕ => moduleSheafPushforwardEvaluationIsoOfTerminal B S hS p𝒳
    (Over.forget (p𝒴.obj V)) p𝒴 f
    (Functor.TwoYoneda.liftFunctor p𝒴 h𝒴 (p𝒴.obj V) (Functor.Fiber.mk (a := V) rfl)) h𝒳
    (Functor.IsFiberedInGroupoids.over_forget _) h𝒴 hfc
    (Functor.TwoYoneda.liftFunctor_w p𝒴 h𝒴 (p𝒴.obj V) (Functor.Fiber.mk (a := V) rfl))
    Over.mkIdTerminal ht (liftFunctorTerminalIso B S hS p𝒴 h𝒴 V) (R.cocomplex.X k)
  have nat : ∀ {k l : ℕ} (d : R.cocomplex.X k ⟶ R.cocomplex.X l)
      (z : ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
        (fF.obj (R.cocomplex.X k))).obj (op V)),
      (E l).hom (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        (fF.map d)).app (op V) z) =
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map d).app (op t.x)
        ((E k).hom z) := fun {k l} d z =>
    ConcreteCategory.congr_hom
      (moduleSheafPushforwardEvaluationIsoOfTerminal_naturality B S hS p𝒳
        (Over.forget (p𝒴.obj V)) p𝒴 f
        (Functor.TwoYoneda.liftFunctor p𝒴 h𝒴 (p𝒴.obj V) (Functor.Fiber.mk (a := V) rfl)) h𝒳
        (Functor.IsFiberedInGroupoids.over_forget _) h𝒴 hfc
        (Functor.TwoYoneda.liftFunctor_w p𝒴 h𝒴 (p𝒴.obj V) (Functor.Fiber.mk (a := V) rfl))
        Over.mkIdTerminal ht (liftFunctorTerminalIso B S hS p𝒴 h𝒴 V) d) z
  have hex : (((Functor.mapHomologicalComplex (SheafOfModules.evaluation
      (ringStructureSheafCore B S hS p𝒳 h𝒳 B.topology le_rfl) (op t.x))
      (ComplexShape.up ℕ)).obj R.cocomplex).sc n).Exact := by
    rw [← HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff_isZero_homology]
    exact IsZero.of_iso (hvan t.x hQ) (R.isoRightDerivedObj _ n).symm
  rw [ShortComplex.moduleCat_exact_iff] at hex
  let x' := C.X₂.val.map a.op x
  have hx' : C.g.val.app (op V) x' = 0 := by
    refine (ConcreteCategory.congr_hom (C.g.val.naturality a.op) x).trans ?_
    rw [ConcreteCategory.comp_apply, hx]
    exact map_zero _
  obtain ⟨u', hu'⟩ := hex ((E n).hom x') (by
    have h := nat (R.cocomplex.d n ((ComplexShape.up ℕ).next n)) x'
    refine h.symm.trans ?_
    refine (congrArg (fun w => (E ((ComplexShape.up ℕ).next n)).hom w) hx').trans ?_
    exact map_zero _)
  refine ⟨(E _).inv u', ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (E n).hom).1
  have h := nat (R.cocomplex.d ((ComplexShape.up ℕ).prev n) n) ((E _).inv u')
  refine h.trans ?_
  have key := Iso.inv_hom_id_apply (E ((ComplexShape.up ℕ).prev n)) u'
  refine (congrArg (fun w => ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (R.cocomplex.d ((ComplexShape.up ℕ).prev n) n)).app (op t.x) w) key).trans ?_
  exact hu'

end Generic

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasSheafify_fppfAssociatedTopology
  wEqualsLocallyBijective_fppfAssociatedTopology

/-- **Higher direct images between stacks representable by affine schemes vanish on modules
acyclic over affine objects.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks both
representable by affine schemes, and `F` a module on `𝒳` whose `n`-th cohomology at every object
over an affine scheme vanishes. Then `Rⁿf_* F = 0`. -/
theorem isZero_fppfHigherDirectImage_of_isAffineRepresentable
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (h𝒳 : IsAffineRepresentable B S hS 𝒳)
    (h𝒴 : IsAffineRepresentable B S hS 𝒴) (F : fppfModules B S hS 𝒳) (n : ℕ)
    (hvan : ∀ x : 𝒳.val.val.obj, IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) →
      letI := enoughInjectives_moduleSheaves.{u, u + 1, u, u + 1} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl
      IsZero (((SheafOfModules.evaluation (ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids B.topology le_rfl) (op x)).rightDerived n).obj F)) :
    IsZero ((fppfHigherDirectImage B S hS f n).obj F) := by
  refine isZero_rightDerived_moduleSheafPushforward_of_isTerminal_fibre B S hS 𝒳.val.val.p
    𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom) F n
    (fun y => IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y)))
    (fun x => IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))) ?_ ?_ hvan
  · intro T
    obtain ⟨I, y, a, hcov, haff, -⟩ := exists_isAffine_covering_of_object B S hS 𝒴.val T
    refine ⟨_, hcov, fun V b hb => ?_⟩
    obtain ⟨W, b', c, ⟨i⟩, rfl⟩ := hb
    exact ⟨y i, b', a i, rfl, haff i⟩
  · intro y hy
    obtain ⟨t, ht, htaff⟩ := exists_isTerminal_of_isAffineRepresentable B S hS
      (𝒳 := twoFibreProductAlgebraicStack B S hS f (objectStackMap B S hS 𝒴 y))
      (isAffineRepresentable_twoFibreProductAlgebraicStack B S hS f _ h𝒳 h𝒴
        (isAffineRepresentable_schemeStack B S hS _ hy))
    refine ⟨t, ht, ?_⟩
    rw [t.hx]
    exact htaff

end AlgebraicGeometry.Stack.AlgebraicStacks
