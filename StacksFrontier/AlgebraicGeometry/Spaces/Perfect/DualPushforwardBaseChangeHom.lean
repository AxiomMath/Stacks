module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackDualHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDualHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProjectionFormulaUnitHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.CategoryTheory.Preadditive.HomAddCommGrpFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChange

/-!
# Morphisms out of the base change of `(Rf_*(P^∨ ⊗^L 𝒢^•))^∨`

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces with `f` quasi-compact and quasi-separated, `P` a
perfect object of `D(𝒪_X)` and `𝒢^•` a bounded above complex of quasi-coherent `𝒪_X`-modules flat
over `Y`, and put `K = Rf_*(P^∨ ⊗^L 𝒢^•)`. If `K` is perfect then for `N ∈ D_QCoh(𝒪_{Y'})`

`Hom(Lg^*K^∨, N) ≅ Hom(L(g')^*P, (g')^*𝒢^• ⊗^L L(f')^*N)`,

naturally in `N`. This is the base-changed form of the identification of Stacks 08JN in the proof
of Stacks 08JR, and it is the step of the proof of Stacks 0DKL in which the perfect stages of the
tower defining the complex `L` of Stacks 08JR (B) are compared after base change.

The isomorphism is the composite of
* `Lg^*(K^∨) ≅ (Lg^*K)^∨` (`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDualIso`);
* `Hom((Lg^*K)^∨, N) ≅ Hom(𝒪_{Y'}, Lg^*K ⊗^L N)` (Stacks 08JJ, with `(Lg^*K)^∨∨ ≅ Lg^*K`);
* `Lg^*K ≅ Rf'_*(L(g')^*P^∨ ⊗^L (g')^*𝒢^•)`, Stacks 0A1K;
* `Hom(𝒪_{Y'}, Rf'_*W ⊗^L N) ≅ Hom(𝒪_{X'}, W ⊗^L L(f')^*N)`, the projection formula
  (Stacks 08IN) for the quasi-compact quasi-separated `f'`;
* the associativity of `⊗^L`, `L(g')^*(P^∨) ≅ (L(g')^*P)^∨` and Stacks 08JJ on `X'`.

## Main definitions

* `AlgebraicGeometry.Space.derivedPullbackPushforwardDualTensorIso`: Stacks 0A1K for `P^∨`.
* `AlgebraicGeometry.Space.dualPushforwardBaseChangeHomAddEquiv`: the isomorphism above.

## Main results

* `AlgebraicGeometry.Space.dualPushforwardBaseChangeHomNatIso_naturality`: the naturality in `N`,
  read componentwise off the natural isomorphism
  `AlgebraicGeometry.Space.dualPushforwardBaseChangeHomNatIso` whose components the group
  isomorphism above is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Precomposition with an isomorphism, as an isomorphism of groups of morphisms. -/
def homAddEquivOfIsoSource {C : Type*} [Category C] [Preadditive C] {A A' : C} (e : A ≅ A')
    (N : C) : (A ⟶ N) ≃+ (A' ⟶ N) where
  toFun h := e.inv ≫ h
  invFun h := e.hom ≫ h
  left_inv h := by simp
  right_inv h := by simp
  map_add' h h' := Preadditive.comp_add _ _ _ _ _ _

/-- Postcomposition with an isomorphism, as an isomorphism of groups of morphisms. -/
def homAddEquivOfIsoTarget {C : Type*} [Category C] [Preadditive C] (A : C) {N N' : C}
    (e : N ≅ N') : (A ⟶ N) ≃+ (A ⟶ N') where
  toFun h := h ≫ e.hom
  invFun h := h ≫ e.inv
  left_inv h := by simp
  right_inv h := by simp
  map_add' h h' := Preadditive.add_comp _ _ _ _ _ _

/-- **Stacks 0A1K for the dual of a perfect object**, as an isomorphism:
`Lg^*Rf_*(P^∨ ⊗^L 𝒢^•) ≅ Rf'_*(L(g')^*P^∨ ⊗^L (g')^*𝒢^•)`. -/
def derivedPullbackPushforwardDualTensorIso (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) P)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n)) :
    (smallEtaleDerivedModulePullback B S hS g).obj
        ((smallEtaleDerivedModulePushforward B S hS f).obj
          (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
            (DerivedCategory.Q.obj G))) ≅
      (smallEtaleDerivedModulePushforward B S hS f').obj
        (((smallEtaleDerivedTensor B S hS X').obj ((smallEtaleDerivedModulePullback B S hS g').obj
          (smallEtaleDerivedDual B S hS X P))).obj
            (DerivedCategory.Q.obj
              (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))) :=
  @asIso _ _ _ _ _ (isIso_smallEtaleDerivedBaseChangeComp_derivedTensor sq hfqc hfqs
    (smallEtaleDerivedDual B S hS X P)
    (qcohDerived_of_isPerfect_derivedCategoryB X _ (isPerfect_smallEtaleDerivedDual B S hS X P hP))
    G hGb hq hfl)

/-- `D_QCoh(𝒪_Z)` as a property of objects of the derived category in the spelling
`SheafOfModules (ringedToposStructureRingSheaf Z)` of derived pullback. -/
abbrev qcohDerivedSheafOfModules (Z : AlgebraicSpaces B S hS) :
    ObjectProperty
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :=
  fun N => QcohDerived B S hS Z N

/-- `Hom(E, -) ≅ Hom(𝒪, E^∨ ⊗^L -)` for a perfect `E`, as an isomorphism of functors to abelian
groups (`AlgebraicGeometry.Space.smallEtaleHomAddEquivUnitTensorDual`). -/
def smallEtaleHomUnitTensorDualNatIso (Z : AlgebraicSpaces B S hS)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)))
    (hA : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Z.1 Z.2) A) :
    homAddCommGrpFunctor A ≅
      (smallEtaleDerivedTensor B S hS Z).obj (smallEtaleDerivedDual B S hS Z A) ⋙
        homAddCommGrpFunctor (structureDerived Z) :=
  NatIso.ofComponents
    (fun M => (smallEtaleHomAddEquivUnitTensorDual B S hS Z A hA M).toAddCommGrpIso)
    (fun {M M'} q => by
      ext h
      exact smallEtaleHomAddEquivUnitTensorDual_naturality B S hS Z A hA q h)

/-- The associator of `⊗^L` in its third variable, as an isomorphism of functors. -/
def smallEtaleDerivedTensorAssociatorNatIso (Z : AlgebraicSpaces B S hS)
    (A A' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedTensor B S hS Z).obj (((smallEtaleDerivedTensor B S hS Z).obj A).obj A') ≅
      (smallEtaleDerivedTensor B S hS Z).obj A' ⋙ (smallEtaleDerivedTensor B S hS Z).obj A :=
  NatIso.ofComponents (fun M => smallEtaleDerivedTensorAssociator Z A A' M)
    (fun h => (smallEtaleDerivedTensorProduct B S hS Z).associatorGeneral_naturality_right A A' h)

/-- **The base change of `Hom((Rf_*(P^∨ ⊗^L 𝒢^•))^∨, -)`, as an isomorphism of functors on
`D_QCoh(𝒪_{Y'})`.** For `f` quasi-compact and quasi-separated, `P` perfect, `𝒢^•` a bounded above
complex of quasi-coherent modules flat over `Y` with `K = Rf_*(P^∨ ⊗^L 𝒢^•)` perfect,
`Hom(Lg^*K^∨, N) ≅ Hom(L(g')^*P, (g')^*𝒢^• ⊗^L L(f')^*N)`, naturally in `N ∈ D_QCoh(𝒪_{Y'})`. -/
def dualPushforwardBaseChangeHomNatIso (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) P)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
          (DerivedCategory.Q.obj G)))) :
    (qcohDerivedSheafOfModules Y').ι ⋙ homAddCommGrpFunctor
        ((smallEtaleDerivedModulePullback B S hS g).obj (smallEtaleDerivedDual B S hS Y
          ((smallEtaleDerivedModulePushforward B S hS f).obj
            (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
              (DerivedCategory.Q.obj G))))) ≅
      (qcohDerivedSheafOfModules Y').ι ⋙ smallEtaleDerivedModulePullback B S hS f' ⋙
        (smallEtaleDerivedTensor B S hS X').obj (DerivedCategory.Q.obj
          (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G)) ⋙
        homAddCommGrpFunctor ((smallEtaleDerivedModulePullback B S hS g').obj P) :=
  let K := (smallEtaleDerivedModulePushforward B S hS f).obj
    (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
      (DerivedCategory.Q.obj G))
  let G' := ((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G
  let A := (smallEtaleDerivedModulePullback B S hS g').obj (smallEtaleDerivedDual B S hS X P)
  let W := ((smallEtaleDerivedTensor B S hS X').obj A).obj (DerivedCategory.Q.obj G')
  have hgK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y'.1 Y'.2)
      ((smallEtaleDerivedModulePullback B S hS g).obj K) :=
    isPerfect_smallEtaleDerivedModulePullback g K hK
  have hgP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X'.1 X'.2)
      ((smallEtaleDerivedModulePullback B S hS g').obj P) :=
    isPerfect_smallEtaleDerivedModulePullback g' P hP
  have hf'qc : IsQuasiCompact B S hS f'.hom :=
    (isQuasiCompact_isStableUnderBaseChange B S hS).of_isPullback sq hfqc
  have hf'qs : IsQuasiSeparated B S hS f'.hom :=
    (isQuasiSeparated_isStableUnderBaseChange B S hS).of_isPullback sq hfqs
  have hW : QcohDerived B S hS X' W :=
    qcohDerived_smallEtaleDerivedTensor X' _ _
      (qcohDerived_of_isPerfect_derivedCategoryB X' _
        (isPerfect_smallEtaleDerivedModulePullback g' _
          (isPerfect_smallEtaleDerivedDual B S hS X P hP)))
      (qcohDerived_Q_obj_of_isQuasicoherentOnSite G' fun n =>
        isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' (G.X n) (hq n))
  haveI : ∀ N, IsIso ((Functor.whiskerLeft (qcohDerivedSheafOfModules Y').ι
      (unitHomProjectionFormula B S hS f' W)).app N) := fun N =>
    isIso_unitHomProjectionFormula_app B S hS f' hf'qc hf'qs W hW N.1 N.2
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerLeft (qcohDerivedSheafOfModules Y').ι
      (unitHomProjectionFormula B S hS f' W))
  Functor.isoWhiskerLeft _ (homAddCommGrpFunctorIsoOfIso
      (smallEtaleDerivedPullbackDualIso g K hK).symm) ≪≫
    Functor.isoWhiskerLeft _ (smallEtaleHomUnitTensorDualNatIso Y' _
      (isPerfect_smallEtaleDerivedDual B S hS Y' _ hgK)) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight ((smallEtaleDerivedTensor B S hS Y').mapIso
      (smallEtaleDerivedBidualIso B S hS Y' _ hgK)) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight ((smallEtaleDerivedTensor B S hS Y').mapIso
      (derivedPullbackPushforwardDualTensorIso sq hfqc hfqs P hP G hGb hq hfl)) _) ≪≫
    Functor.isoWhiskerLeft ((qcohDerivedSheafOfModules Y').ι ⋙
        (smallEtaleDerivedTensor B S hS Y').obj
          ((smallEtaleDerivedModulePushforward B S hS f').obj W))
      (preadditiveCoyonedaIsoHomAddCommGrpFunctor (structureDerived Y')).symm ≪≫
    asIso (Functor.whiskerLeft (qcohDerivedSheafOfModules Y').ι
      (unitHomProjectionFormula B S hS f' W)) ≪≫
    Functor.isoWhiskerLeft ((qcohDerivedSheafOfModules Y').ι ⋙
        smallEtaleDerivedModulePullback B S hS f' ⋙ (smallEtaleDerivedTensor B S hS X').obj W)
      (preadditiveCoyonedaIsoHomAddCommGrpFunctor (structureDerived X')) ≪≫
    Functor.isoWhiskerLeft
      ((qcohDerivedSheafOfModules Y').ι ⋙ smallEtaleDerivedModulePullback B S hS f')
      (Functor.isoWhiskerRight (smallEtaleDerivedTensorAssociatorNatIso X' A
          (DerivedCategory.Q.obj G')) (homAddCommGrpFunctor (structureDerived X')) ≪≫
        Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft ((qcohDerivedSheafOfModules Y').ι ⋙
        smallEtaleDerivedModulePullback B S hS f' ⋙
        (smallEtaleDerivedTensor B S hS X').obj (DerivedCategory.Q.obj G'))
      (Functor.isoWhiskerRight ((smallEtaleDerivedTensor B S hS X').mapIso
        (smallEtaleDerivedPullbackDualIso g' P hP)) _ ≪≫
        (smallEtaleHomUnitTensorDualNatIso X' _ hgP).symm)

/-- **The base change of `Hom((Rf_*(P^∨ ⊗^L 𝒢^•))^∨, -)`** at one `N ∈ D_QCoh(𝒪_{Y'})`. -/
def dualPushforwardBaseChangeHomAddEquiv (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) P)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
          (DerivedCategory.Q.obj G))))
    (N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')))
    (hN : QcohDerived B S hS Y' N) :
    ((smallEtaleDerivedModulePullback B S hS g).obj (smallEtaleDerivedDual B S hS Y
        ((smallEtaleDerivedModulePushforward B S hS f).obj
          (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
            (DerivedCategory.Q.obj G)))) ⟶ N) ≃+
      ((smallEtaleDerivedModulePullback B S hS g').obj P ⟶
        ((smallEtaleDerivedTensor B S hS X').obj (DerivedCategory.Q.obj
          (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))).obj
            ((smallEtaleDerivedModulePullback B S hS f').obj N)) :=
  ((dualPushforwardBaseChangeHomNatIso sq hfqc hfqs P hP G hGb hq hfl hK).app
    ⟨N, hN⟩).addCommGroupIsoToAddEquiv



/-- **Naturality of the base change of `Hom((Rf_*(P^∨ ⊗^L 𝒢^•))^∨, -)`**, componentwise. -/
theorem dualPushforwardBaseChangeHomNatIso_naturality (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) P)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
          (DerivedCategory.Q.obj G))))
    {N N' : (qcohDerivedSheafOfModules Y').FullSubcategory} (q : N ⟶ N')
    (h : (smallEtaleDerivedModulePullback B S hS g).obj (smallEtaleDerivedDual B S hS Y
        ((smallEtaleDerivedModulePushforward B S hS f).obj
          (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
            (DerivedCategory.Q.obj G)))) ⟶ N.obj) :
    ((dualPushforwardBaseChangeHomNatIso sq hfqc hfqs P hP G hGb hq hfl hK).hom.app N').hom
        (h ≫ q.hom) =
      ((dualPushforwardBaseChangeHomNatIso sq hfqc hfqs P hP G hGb hq hfl hK).hom.app N).hom h ≫
        ((smallEtaleDerivedTensor B S hS X').obj (DerivedCategory.Q.obj
          (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))).map
            ((smallEtaleDerivedModulePullback B S hS f').map q.hom) := by
  have h1 := (dualPushforwardBaseChangeHomNatIso sq hfqc hfqs P hP G hGb hq hfl hK).hom.naturality q
  have h2 := congrArg (fun φ => AddCommGrpCat.Hom.hom φ h) h1
  exact h2

end AlgebraicGeometry.Space

end
