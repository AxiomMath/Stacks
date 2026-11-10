module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.LocalCharts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition

/-!
# Duality charts are carried along an equivalence of ringed sites

Let `eqv : C_Y ≌ C_X` be an equivalence of the underlying sites of two ringed sites `X` and `Y`,
continuous in both directions, with an invertible structure map `φ : O_Y ⟶ eqv_* O_X`. The
pushforward along `φ` is an equivalence `Mod(O_X) ≌ Mod(O_Y)`, it preserves and reflects finite
presentation (Stacks 03DM for 03DL (7)), and it carries the derived internal Hom of `X` to that of
`Y` (`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIsoOfIso`). A duality chart on `X` is
therefore carried to a duality chart on `Y`.

## Main definitions

* `AlgebraicGeometry.RingedSite.siteEquivModulesEquiv`: the equivalence of categories of modules.
* `AlgebraicGeometry.RingedSite.DualityChart.transport`: the transported chart.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.SheafOfModules.ModelFinitePresentation

universe w u₁ v₁ u₂ v₂

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous

/-- The pushforward of the structure sheaf along an invertible structure map is the structure
sheaf. -/
def pushforwardUnitIsoOfIso {Y' : Type u₁} [Category.{v₁} Y'] {X' : Type u₂} [Category.{v₂} X']
    {JY : GrothendieckTopology Y'} {JX : GrothendieckTopology X'} (F : Y' ⥤ X')
    [F.IsContinuous JY JX] {R : Sheaf JX RingCat.{w}} {S : Sheaf JY RingCat.{w}}
    (ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} JY JX).obj R) [IsIso ψ] :
    (SheafOfModules.pushforward.{w} ψ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S :=
  haveI : IsIso ψ.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map ψ))
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.pushforwardUnitIso (G := F) ψ.hom)

/-- `Stacks.SheafOfModules.ModelFinitePresentation.isFinitePresentation_pushforward` with the unit
comparison supplied and the invertibility of the structure map an explicit argument. -/
theorem isFinitePresentation_pushforward_of_isIso {C : Type u₁} [Category.{v₁} C]
    {C' : Type u₂} [Category.{v₂} C'] {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
    {R : Sheaf J RingCat.{w}}
    [hsheafify : ∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
    [hlocBij : ∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [hsheafify' : ∀ X : C', HasSheafify (J'.over X) AddCommGrpCat.{w}]
    [hlocBij' : ∀ X : C', (J'.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (e : C' ≌ C) [e.functor.IsContinuous J' J] [hdense : e.functor.IsDenseSubsite J' J]
    [hpull : HasPullbacks C] [hpull' : HasPullbacks C'] {S : Sheaf J' RingCat.{w}}
    (φ : S ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} J' J).obj R) (hφ : IsIso φ)
    (M : SheafOfModules.{w} R) (hM : M.IsFinitePresentation) :
    ((SheafOfModules.pushforward φ).obj M).IsFinitePresentation :=
  isFinitePresentation_pushforward e φ (pushforwardUnitIsoOfIso _ _) M

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ X : C', HasSheafify (J'.over X) AddCommGrpCat.{w}]
  [∀ X : C', (J'.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.functor.IsDenseSubsite J' J] [e.inverse.IsDenseSubsite J J'] [HasPullbacks C]
  [HasPullbacks C'] {R : Sheaf J RingCat.{w}} {S : Sheaf J' RingCat.{w}}
  (φ : S ⟶ (e.functor.sheafPushforwardContinuous RingCat.{w} J' J).obj R) [IsIso φ]
  (ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{w} J J').obj S) [IsIso ψ]
  (H₁ : Functor.whiskerRight (NatTrans.op e.counit) R.obj = ψ.hom ≫ e.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ e.functor.op.whiskerLeft ψ.hom ≫ Functor.whiskerRight (NatTrans.op e.unit) S.obj =
    𝟙 S.obj)

include ψ H₁ H₂ in
/-- **Finite presentation is invariant under the equivalence of sheaves of modules of an
equivalence of sites with invertible structure maps** (Stacks 03DM for the clause 03DL (7)). The
two sites may live in different universes. -/
theorem isFinitePresentation_pushforward_iff_of_equivalence (M : SheafOfModules.{w} R) :
    ((SheafOfModules.pushforward.{w} φ).obj M).IsFinitePresentation ↔
      M.IsFinitePresentation := by
  refine ⟨fun h => ?_, isFinitePresentation_pushforward_of_isIso e φ ‹_› M⟩
  have : e.symm.functor.IsContinuous J J' := ‹e.inverse.IsContinuous J J'›
  have : e.symm.functor.IsDenseSubsite J J' := ‹e.inverse.IsDenseSubsite J J'›
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    ((SheafOfModules.pushforwardPushforwardEquivalence e φ ψ H₁ H₂).unitIso.app M).symm
    (isFinitePresentation_pushforward_of_isIso e.symm ψ ‹_›
      ((SheafOfModules.pushforward.{w} φ).obj M) h)

end Stacks.SheafOfModules.ModelFinitePresentation

namespace AlgebraicGeometry.RingedSite

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (eqv : Y.C ≌ X.C) [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [hφ : IsIso φ]

/-- The equivalence `Mod(O_X) ≌ Mod(O_Y)` of an equivalence of ringed sites with invertible
structure map: the pushforward along `φ`, with inverse the pushforward along the inverse
structure map. -/
def siteEquivModulesEquiv :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  SheafOfModules.pushforwardPushforwardEquivalence eqv φ
    (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ)

omit [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The functor of `siteEquivModulesEquiv eqv φ` is the pushforward along `φ`. -/
theorem siteEquivModulesEquiv_functor :
    (siteEquivModulesEquiv eqv φ).functor = SheafOfModules.pushforward.{u} φ := rfl

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous

/-- The inverse structure map of an equivalence of ringed sites with invertible structure map is
invertible. -/
instance isIso_psiOfIso : IsIso (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ) := by
  have : IsIso (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ).hom := by
    change IsIso ((Functor.isoWhiskerRight (NatIso.op eqv.counitIso)
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).hom ≫
      Functor.whiskerLeft eqv.inverse.op (inv φ.hom))
    infer_instance
  have : IsIso ((sheafToPresheaf X.J RingCat.{u}).map
      (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)) := this
  exact isIso_of_fully_faithful (sheafToPresheaf X.J RingCat.{u}) _

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **Finite presentation is invariant under an equivalence of ringed sites** (Stacks 03DM for
the clause 03DL (7)). -/
theorem isFinitePresentation_pushforward_iff
    [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
    [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{u}]
    [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [eqv.functor.IsDenseSubsite Y.J X.J] [eqv.inverse.IsDenseSubsite X.J Y.J]
    [HasPullbacks X.C] [HasPullbacks Y.C]
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((SheafOfModules.pushforward.{u} φ).obj M).IsFinitePresentation ↔ M.IsFinitePresentation :=
  Stacks.SheafOfModules.ModelFinitePresentation.isFinitePresentation_pushforward_iff_of_equivalence
    eqv φ (Stacks.SheafOfModules.InternalHom.psiOfIso eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_counit eqv φ)
    (Stacks.SheafOfModules.InternalHom.psiOfIso_unit eqv φ) M

/-! ### The derived equivalence -/

/-- **The derived equivalence `D(O_X) ≌ D(O_Y)`** of an equivalence of ringed sites with
invertible structure map, whose functor is the derived pushforward along `φ`. -/
def siteEquivDerivedEquivalence : StdDerived X ≌ StdDerived Y :=
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
  letI : (siteEquivModulesEquiv eqv φ).functor.Additive :=
    inferInstanceAs (SheafOfModules.pushforward.{u} φ).Additive
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory (siteEquivModulesEquiv eqv φ)

/-- The cohomology sheaves of the derived pushforward are the pushforwards of the cohomology
sheaves. -/
def siteEquivDerivedHomologyIso (n : ℤ) (L : StdDerived X) :
    (stdHomology Y n).obj ((siteEquivDerivedEquivalence eqv φ).functor.obj L) ≅
      (SheafOfModules.pushforward.{u} φ).obj ((stdHomology X n).obj L) :=
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
  letI : (siteEquivModulesEquiv eqv φ).functor.Additive :=
    inferInstanceAs (SheafOfModules.pushforward.{u} φ).Additive
  ((siteEquivModulesEquiv eqv φ).functor.mapDerivedCategoryHomologyIso n).app L

/-- The derived pushforward carries the derived internal Hom of `X` to that of `Y`
(`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIsoOfIso`, at the standard models). -/
def stdSiteEquivDerivedSheafHomIso (K L : StdDerived X) :
    (siteEquivDerivedEquivalence eqv φ).functor.obj (((stdSheafHom X).obj (op K)).obj L) ≅
      ((stdSheafHom Y).obj (op ((siteEquivDerivedEquivalence eqv φ).functor.obj K))).obj
        ((siteEquivDerivedEquivalence eqv φ).functor.obj L) :=
  haveI := pushforward_preservesFiniteLimitsOfIso eqv φ
  haveI := pushforward_preservesFiniteColimitsOfIso eqv φ
  siteEquivDerivedSheafHomIsoOfIso eqv φ (hφ := hφ) K L

/-! ### Transport of a duality chart -/

variable {eqv φ}

/-- The chart functor `Φ` followed by the pushforward along `φ`. -/
def ChartFunctor.transport (c : ChartFunctor X) : ChartFunctor Y where
  T := c.T
  isAffine := c.isAffine
  isNoetherian := c.isNoetherian
  Φ := c.Φ ⋙ SheafOfModules.pushforward.{u} φ
  additive := letI := c.additive; inferInstance
  preservesFiniteLimits :=
    letI := c.preservesFiniteLimits
    letI := pushforward_preservesFiniteLimitsOfIso eqv φ
    comp_preservesFiniteLimits _ _
  preservesFiniteColimits :=
    letI := c.preservesFiniteColimits
    letI := pushforward_preservesFiniteColimitsOfIso eqv φ
    comp_preservesFiniteColimits _ _

variable (eqv φ) in
/-- The derived functor of the transported chart is the derived functor of the chart followed by
the derived pushforward. -/
def ChartFunctor.transportDerivedIso (c : ChartFunctor X) :
    (c.transport (eqv := eqv) (φ := φ)).derived ≅
      c.derived ⋙ (siteEquivDerivedEquivalence eqv φ).functor :=
  letI := c.additive
  letI := c.preservesFiniteLimits
  letI := c.preservesFiniteColimits
  letI := pushforward_preservesFiniteLimitsOfIso eqv φ
  letI := pushforward_preservesFiniteColimitsOfIso eqv φ
  letI : HasDerivedCategory c.T.Modules := HasDerivedCategory.standard _
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
  (Stacks.DerivedFunctor.mapDerivedCategoryCompIso c.Φ (SheafOfModules.pushforward.{u} φ)).symm

variable [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{u}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [eqv.functor.IsDenseSubsite Y.J X.J] [eqv.inverse.IsDenseSubsite X.J Y.J]
  [HasPullbacks X.C] [HasPullbacks Y.C]

/-- **A duality chart is carried along an equivalence of ringed sites** with invertible
structure map: the chart functor is followed by the pushforward along `φ`, and the complex is
carried by the derived pushforward. -/
def DualityChart.transport {K : StdDerived X} {P : ChartClass.{u}} (c : DualityChart X K P) :
    DualityChart Y ((siteEquivDerivedEquivalence eqv φ).functor.obj K) P where
  toChartFunctor := c.toChartFunctor.transport (eqv := eqv) (φ := φ)
  ω := c.ω
  isDualizing := c.isDualizing
  isCoherent_iff M hM :=
    (c.isCoherent_iff M hM).trans (isFinitePresentation_pushforward_iff eqv φ _).symm
  isZero_of_isZero M hM h :=
    c.isZero_of_isZero M hM <| (Functor.map_isZero (siteEquivModulesEquiv eqv φ).inverse h).of_iso
      ((siteEquivModulesEquiv eqv φ).unitIso.app (c.Φ.obj M))
  exists_iso L hL := by
    let E := siteEquivDerivedEquivalence eqv φ
    have hL₀ : ∀ n : ℤ, ((stdHomology X n).obj (E.inverse.obj L)).IsFinitePresentation := by
      intro n
      rw [← isFinitePresentation_pushforward_iff eqv φ]
      exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
        ((stdHomology Y n).mapIso (E.counitIso.app L).symm ≪≫
          siteEquivDerivedHomologyIso eqv φ n _) (hL n)
    obtain ⟨L', hL', ⟨e'⟩⟩ := c.exists_iso _ hL₀
    exact ⟨L', hL', ⟨(c.toChartFunctor.transportDerivedIso eqv φ).app L' ≪≫
      E.functor.mapIso e' ≪≫ E.counitIso.app L⟩⟩
  map_bijective A B hA hB := by
    let E := siteEquivDerivedEquivalence eqv φ
    let e := c.toChartFunctor.transportDerivedIso eqv φ
    have hfun :
        (fun f : A ⟶ B => (c.toChartFunctor.transport (eqv := eqv) (φ := φ)).derived.map f) =
          ((Iso.homCongr (e.app A).symm (e.app B).symm) ∘ fun g => E.functor.map g) ∘
            fun f => c.derived.map f :=
      funext fun f => (NatIso.naturality_1 e.symm f).symm
    change Function.Bijective
      (fun f : A ⟶ B => (c.toChartFunctor.transport (eqv := eqv) (φ := φ)).derived.map f)
    rw [hfun]
    exact ((Iso.homCongr (e.app A).symm (e.app B).symm).bijective.comp
      (E.fullyFaithfulFunctor.map_bijective _ _)).comp (c.map_bijective A B hA hB)
  isoDualizing := by
    obtain ⟨i⟩ := c.isoDualizing
    exact ⟨(c.toChartFunctor.transportDerivedIso eqv φ).app c.ω ≪≫
      (siteEquivDerivedEquivalence eqv φ).functor.mapIso i⟩
  dualIso Z hZ hPZ := by
    let E := siteEquivDerivedEquivalence eqv φ
    let e := c.toChartFunctor.transportDerivedIso eqv φ
    obtain ⟨d⟩ := c.dualIso Z hZ hPZ
    exact ⟨((stdSheafHom Y).mapIso (e.app Z).symm.op).app (E.functor.obj K) ≪≫
      (stdSiteEquivDerivedSheafHomIso eqv φ _ _).symm ≪≫ E.functor.mapIso d ≪≫ (e.app _).symm⟩

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **An object modelled by a chart is carried to an object modelled by the transported chart.** -/
theorem DualityChart.models_transport {K : StdDerived X} {P : ChartClass.{u}}
    (c : DualityChart X K P) {M' : StdDerived X} (h : c.Models M') {M : StdDerived Y}
    (e : (siteEquivDerivedEquivalence eqv φ).functor.obj M' ≅ M) :
    (c.transport (eqv := eqv) (φ := φ)).Models M := by
  obtain ⟨L', h₁, h₂, h₃, ⟨d⟩⟩ := h
  exact ⟨L', h₁, h₂, h₃, ⟨(c.toChartFunctor.transportDerivedIso eqv φ).app L' ≪≫
    (siteEquivDerivedEquivalence eqv φ).functor.mapIso d ≪≫ e⟩⟩

end AlgebraicGeometry.RingedSite

end
