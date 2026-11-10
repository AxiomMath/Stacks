module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoefficientLFunction
public import StacksFrontier.CategoryTheory.Sites.IdempotentCoefficientSplitting

/-!
# The L-function over the factors of an idempotent splitting of the coefficients

Let `Λ` be a commutative ring, `e` an idempotent and `Λ₁ = Λ ⧸ (1 - e)`. For a sheaf `F` of
`Λ`-modules on the small étale site of Tag 021B, the sheaf `e F = Λ₁ ⊗_Λ F` of
`IsIdempotentElem.sheafBaseChange` is a sheaf of `Λ₁`-modules. If `F` is constructible flat, so is
`e F`, and the L-function of `e F` (Tag 03UV) is the image of the L-function of `F` under
`Λ⟦T⟧ → Λ₁⟦T⟧`: the stalks of `e F` are the base changes of the stalks of `F`, compatibly with the
geometric Frobenius, and characteristic series commute with base change. This is the L-function
half of the reduction of Tag 03UZ to local coefficient rings.

## Main results

* `Stacks.EtaleCohomology.isConstructibleFlatModuleSheaf_sheafBaseChange`: `e F` is
  constructible flat.
* `Stacks.EtaleCohomology.map_constructibleFlatLFunction_sheafBaseChange`:
  `L(X, e F)` is the image of `L(X, F)`.

## References

* [Stacks Project, Tag 03UV](https://stacks.math.columbia.edu/tag/03UV)
* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Frobenius
open scoped TensorProduct

universe u w r

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {Λ : Type r} [CommRing Λ] {e : Λ}
  (he : IsIdempotentElem e)

/-! ### Constructibility -/

section Constructible

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{max w r} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{max w r} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))]

/-- **`e F` is constructible flat** when `F` is: the same stratifications work, since base change
commutes with restriction to the strata and preserves local constancy with finite projective
values. -/
public theorem isConstructibleFlatModuleSheaf_sheafBaseChange
    {F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max w r} Λ)}
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    IsConstructibleFlatModuleSheaf B X (Λ ⧸ Ideal.span {1 - e})
      ((he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property)).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i => Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
    ((he.sheafPullbackBaseChangeIso.{w} _ _ (smallEtaleBaseChange B (s.inclusion i))).app F)
    (he.isFiniteProjectiveLocallyConstant_sheafBaseChange.{w} _ (hs i))⟩

end Constructible

/-! ### Stalks and the L-function -/

section Stalks

variable [HasColimitsOfSize.{u, u} (ModuleCat.{max w r} Λ)]
  [HasLimitsOfSize.{u, u} (ModuleCat.{max w r} Λ)]
  [HasColimitsOfSize.{u, u} (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))]
  [HasLimitsOfSize.{u, u} (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))]

/-- Base change commutes with the identification of the two small étale sites. -/
public def sheafEquivSheafBaseChangeIso :
    (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max w r} Λ)).functor ⋙
        he.sheafBaseChange.{w} X.obj.smallEtaleTopology ≅
      he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property) ⋙
        (SmallEtale.sheafEquiv B X.obj X.property
          (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))).functor :=
  Equivalence.functorCompIsoOfInverseComp _ _ (Iso.refl _)

/-- **The stalks of `e F` are the base changes of the stalks of `F`.** -/
public def frobeniusStalkModuleSheafBaseChangeIso
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max w r} Λ)) (x : X.obj) :
    frobeniusStalkModule B X (Λ ⧸ Ideal.span {1 - e})
        ((he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property)).obj F) x ≅
      (Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e})).obj
        (frobeniusStalkModule B X Λ F x) :=
  haveI := (he.restrictScalarsBaseChangeAdj.{w}).rightAdjoint_preservesLimits
  haveI := (Stacks.ModuleCat.baseChangeRestrictScalarsAdj.{w} Λ
    (Λ ⧸ Ideal.span {1 - e})).leftAdjoint_preservesColimits
  (Scheme.pointSmallEtale (geometricPointAt X.obj x).hom).sheafFiber.mapIso
      ((sheafEquivSheafBaseChangeIso B X he).app F).symm ≪≫
    ((Scheme.pointSmallEtale (geometricPointAt X.obj x).hom).sheafFiberCompIso
      (Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e}))).app
        ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max w r} Λ)).functor.obj F)

/-- **The identification of the stalks commutes with the geometric Frobenius.** -/
public theorem frobeniusStalk_sheafBaseChange
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max w r} Λ)) (x : X.obj)
    [Finite (X.obj.residueField x)] :
    frobeniusStalk (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) X.obj x
        ((SmallEtale.sheafEquiv B X.obj X.property
          (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))).functor.obj
          ((he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property)).obj F)) ≫
        (frobeniusStalkModuleSheafBaseChangeIso B X he F x).hom =
      (frobeniusStalkModuleSheafBaseChangeIso B X he F x).hom ≫
        (Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e})).map
          (frobeniusStalk (ModuleCat.{max w r} Λ) X.obj x
            ((SmallEtale.sheafEquiv B X.obj X.property
              (ModuleCat.{max w r} Λ)).functor.obj F)) := by
  have := (he.restrictScalarsBaseChangeAdj.{w}).rightAdjoint_preservesLimits
  have := (Stacks.ModuleCat.baseChangeRestrictScalarsAdj.{w} Λ
    (Λ ⧸ Ideal.span {1 - e})).leftAdjoint_preservesColimits
  let F' := (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max w r} Λ)).functor.obj F
  let p := Scheme.pointSmallEtale (geometricPointAt X.obj x).hom
  let G := Stacks.ModuleCat.baseChangeFunctor.{max w r} Λ (Λ ⧸ Ideal.span {1 - e})
  have h1 := frobeniusStalk_naturality (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))
    X.obj x ((sheafEquivSheafBaseChangeIso B X he).inv.app F)
  have h2 : frobeniusStalk (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) X.obj x
        ((he.sheafBaseChange.{w} X.obj.smallEtaleTopology).obj F') ≫
        (p.sheafFiberCompIso G).hom.app F' =
      (p.sheafFiberCompIso G).hom.app F' ≫
        G.map (frobeniusStalk (ModuleCat.{max w r} Λ) X.obj x F') := by
    simp only [GrothendieckTopology.Point.sheafFiberCompIso_hom_app]
    exact GrothendieckTopology.Point.Hom.presheafFiber_app_comp_presheafFiberCompIso_hom
      (J := X.obj.smallEtaleTopology) G _ _
  change _ ≫ (p.sheafFiber.map ((sheafEquivSheafBaseChangeIso B X he).inv.app F) ≫
      (p.sheafFiberCompIso G).hom.app F') =
    (p.sheafFiber.map ((sheafEquivSheafBaseChangeIso B X he).inv.app F) ≫
      (p.sheafFiberCompIso G).hom.app F') ≫ _
  let m := p.sheafFiber.map ((sheafEquivSheafBaseChangeIso B X he).inv.app F)
  let c := (p.sheafFiberCompIso G).hom.app F'
  calc _ = (_ ≫ m) ≫ c := (Category.assoc _ _ _).symm
    _ = (m ≫ _) ≫ c := congrArg (· ≫ c) h1.symm
    _ = m ≫ (_ ≫ c) := Category.assoc _ _ _
    _ = m ≫ (c ≫ _) := congrArg (m ≫ ·) h2
    _ = _ := (Category.assoc _ _ _).symm

variable {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- **The local factors of `e F` are the images of those of `F`.** -/
public theorem map_finiteProjectiveLocalCharSeries_sheafBaseChange
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max w r} Λ))
    (hfin : ∀ s : GeometricPoint X.obj, Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (hproj : ∀ s : GeometricPoint X.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (hfin' : ∀ s : GeometricPoint X.obj, Module.Finite (Λ ⧸ Ideal.span {1 - e})
      ((etaleModuleStalkFunctor B X (Λ ⧸ Ideal.span {1 - e}) s).obj
        ((he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property)).obj F)))
    (hproj' : ∀ s : GeometricPoint X.obj, Module.Projective (Λ ⧸ Ideal.span {1 - e})
      ((etaleModuleStalkFunctor B X (Λ ⧸ Ideal.span {1 - e}) s).obj
        ((he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property)).obj F)))
    (x : closedPoints X.obj) :
    PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))
        (finiteProjectiveLocalCharSeries B X Λ F f hfin hproj x) =
      finiteProjectiveLocalCharSeries B X (Λ ⧸ Ideal.span {1 - e})
        ((he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property)).obj F)
        f hfin' hproj' x := by
  have := finite_residueField f x.1 x.2
  have := finite_sheafFiber_sheafEquiv B X Λ (geometricPointAt X.obj x.1) F (hfin _)
  have := projective_sheafFiber_sheafEquiv B X Λ F (geometricPointAt X.obj x.1) (hproj _)
  have := finite_sheafFiber_sheafEquiv B X (Λ ⧸ Ideal.span {1 - e}) (geometricPointAt X.obj x.1)
    _ (hfin' _)
  have := projective_sheafFiber_sheafEquiv B X (Λ ⧸ Ideal.span {1 - e}) _
    (geometricPointAt X.obj x.1) (hproj' _)
  let ψ := (frobeniusStalkModuleSheafBaseChangeIso B X he F x.1).toLinearEquiv
  have hconj : ψ.conj (closedPointFrobenius B X (Λ ⧸ Ideal.span {1 - e})
      ((he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property)).obj F) f x) =
      (closedPointFrobenius B X Λ F f x).baseChange (Λ ⧸ Ideal.span {1 - e}) := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply]
    have := congrArg (fun g => g.hom (ψ.symm y)) (frobeniusStalk_sheafBaseChange B X he F x.1)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    refine this.trans ?_
    rw [show (frobeniusStalkModuleSheafBaseChangeIso B X he F x.1).hom (ψ.symm y) = y from
      ψ.apply_symm_apply y]
    rfl
  rw [finiteProjectiveLocalCharSeries, finiteProjectiveLocalCharSeries,
    ← ProjectiveDeterminant.charSeries_baseChange, ← hconj, ProjectiveDeterminant.charSeries_conj]

variable [QuasiCompact f]

variable
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{max w r} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{max w r} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e})) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max w r} (Λ ⧸ Ideal.span {1 - e}))]

/-- **`L(X, e F)` is the image of `L(X, F)` under `Λ⟦T⟧ → (Λ ⧸ (1 - e))⟦T⟧`** (Tag 03UV), for a
constructible flat `F`. -/
public theorem map_constructibleFlatLFunction_sheafBaseChange
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max w r} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))
        (constructibleFlatLFunction B X Λ F f hF) =
      constructibleFlatLFunction B X (Λ ⧸ Ideal.span {1 - e})
        ((he.sheafBaseChange.{w} (SmallEtale.topology B X.obj X.property)).obj F) f
        (isConstructibleFlatModuleSheaf_sheafBaseChange B X he hF) := by
  ext j
  let t := (finite_setOf_closedPoints_residueDegree_le f j).toFinset
  have ht : ∀ x : closedPoints X.obj, residueDegree f x.1 ≤ j → x ∈ t := fun x hx => by simpa [t]
  rw [PowerSeries.coeff_map, coeff_constructibleFlatLFunction_eq B X Λ F f hF ht,
    coeff_constructibleFlatLFunction_eq B X _ _ f _ ht,
    ← PowerSeries.coeff_map (algebraMap Λ (Λ ⧸ Ideal.span {1 - e})), map_prod]
  congr 2
  refine funext fun x => ?_
  have hfin' := finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X _ _
    (isConstructibleFlatModuleSheaf_sheafBaseChange B X he hF)
  have hproj' := projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X _ _
    (isConstructibleFlatModuleSheaf_sheafBaseChange B X he hF)
  have h₁ := finiteProjectiveLocalCharSeries_mul_localFactor B X Λ F f
    (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)
    (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF) x
  have h₂ := finiteProjectiveLocalCharSeries_mul_localFactor B X (Λ ⧸ Ideal.span {1 - e}) _ f
    hfin' hproj' x
  have h₃ := congrArg (PowerSeries.map (algebraMap Λ (Λ ⧸ Ideal.span {1 - e}))) h₁
  rw [map_mul, map_one, map_finiteProjectiveLocalCharSeries_sheafBaseChange B X he f F _ _
    hfin' hproj' x] at h₃
  exact left_inv_eq_right_inv (by rwa [mul_comm]) h₂

end Stalks

end Stacks.EtaleCohomology

end
