module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatIsFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkAcyclicityCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DerivedStalkPerfection
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.BifunctorLocalization
public import StacksFrontier.Homology.TwoTermComplex.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# K-flatness of a bounded above complex with flat étale stalks

Let `B` be a big étale site, `X` an object of it and `Λ` a commutative ring. Stacks 06YQ says
that a bounded above complex of flat modules is K-flat. This file proves that statement for the
tensor product of sheaves of `Λ`-modules on the small étale site of `X`, with flatness taken in
the form of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FlatEtaleStalks`:
every étale stalk of every term is a flat `Λ`-module. Nothing is asked of `X`.

The engine is the bifunctor-generic `CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE`, whose
base case asks that tensoring with a single term be exact on complexes. That is where flatness
enters, and it is checked on stalks: the étale module stalk functors are jointly faithful and
exact, so they detect exactness of a short complex of sheaves, and the stalk of a tensor product
is the tensor product of the stalks
(`AlgebraicGeometry.SmallEtale.modStalkTensorIso`), which is exact because the stalk of the fixed
factor is a flat `Λ`-module.

With K-flatness in both variables the total tensor complex becomes insensitive to the choice of
representative: a quasi-isomorphism in either variable induces a quasi-isomorphism of total
complexes.

## Main results

* `Stacks.EtaleCohomology.exact_of_forall_etaleModuleStalk_exact` and
  `Stacks.EtaleCohomology.acyclic_of_forall_etaleModuleStalk_acyclic` — exactness and acyclicity
  of complexes of sheaves of `Λ`-modules are detected by the étale stalks.
* `Stacks.EtaleCohomology.acyclic_rowComplex_of_flat_etaleModuleStalk` — **tensoring with a sheaf
  whose étale stalks are flat carries acyclic complexes to acyclic complexes**, and its mirror
  `Stacks.EtaleCohomology.acyclic_rowComplex_flip_of_flat_etaleModuleStalk`.
* `Stacks.EtaleCohomology.kFlat_of_flat_etaleModuleStalk` and
  `Stacks.EtaleCohomology.kFlatLeft_of_flat_etaleModuleStalk` — **Stacks 06YQ for the small étale
  tensor product**: a bounded above complex whose terms have flat étale stalks is K-flat on
  either side.
* `Stacks.EtaleCohomology.quasiIso_mapBifunctorMap` — **the total tensor complex is insensitive
  to quasi-isomorphisms in either variable** when the opposite variable is K-flat.

## Implementation notes

The two hypotheses of `CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE` beyond the base case
are discharged from the structure of the sheaf category rather than assumed: tensoring preserves
sequential colimits because the category is monoidal closed, which is Day's reflection theorem
applied to sheafification, and sequential colimits are exact there because they are exact in
`Λ`-modules and sheafification is a left adjoint preserving finite limits.

`HomologicalComplex.mapBifunctorMap_eq_map₂_comp` factors a two-variable
map of total complexes as the first variable followed by the second;
`Stacks.EtaleCohomology.mapBifunctorMap_snd_comp_mapBifunctorMap_fst` is the other order, which
is the one that pairs K-flatness of the right target with left K-flatness of the left source.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.SmallEtale.moduleSheafMonoidal
  AlgebraicGeometry.SmallEtale.modStalkMonoidal
  SheafOfModules.hasSheafify_commRingCat
  SheafOfModules.wEqualsLocallyBijective_commRingCat
  GrothendieckTopology.hasSheafify_addCommGrpCat
  SheafOfModules.wEqualsLocallyBijective_addCommGrpCat

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type (max (u + 1) w)) [CommRing Λ]
  [(curriedTensor
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive]

/-! ### Joint faithfulness of the étale module stalks -/

omit [(curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive] in
/-- The geometric-point stalk functors with coefficients in `Λ`-modules are jointly faithful:
the abelian-sheaf statement `AlgebraicGeometry.jointlyFaithful_etaleStalkSheafFiber` composed
with the faithful `sheafCompose` along `forget₂`. -/
@[sga "4 VIII 3.7" "special case"]
public theorem jointlyFaithful_etaleModuleStalkFunctor :
    JointlyFaithful (fun s : GeometricPoint X.obj =>
      etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s) := by
  refine ⟨fun {F G} {φ ψ} h => ?_⟩
  apply (sheafCompose (SmallEtale.topology B X.obj X.property)
    (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w})).map_injective
  refine (jointlyFaithful_etaleStalkSheafFiber.{u, w} B X.obj X.property).map_injective
    fun s => ?_
  have e := (geometricPointSitePoint B X.obj X.property s).sheafFiberCompIso
    (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w})
  have n1 := e.hom.naturality φ
  have n2 := e.hom.naturality ψ
  simp only [Functor.comp_map] at n1 n2
  rw [← cancel_mono (e.hom.app G), n1, n2]
  exact congrArg (fun m => e.hom.app F ≫
    (forget₂ (ModuleCat.{max (u + 1) w} Λ) AddCommGrpCat.{max (u + 1) w}).map m) (h s)

/-- Limits of the size of the site exist in the coefficient category. -/
local instance hasLimitsOfSize_moduleCat :
    HasLimitsOfSize.{u, u} (ModuleCat.{max (u + 1) w} Λ) :=
  ⟨fun _ => ModuleCat.hasLimitsOfShape⟩

/-- Filtered colimits of the size of the site are exact in the coefficient category. -/
local instance ab5OfSize_moduleCat : AB5OfSize.{u, u} (ModuleCat.{max (u + 1) w} Λ) :=
  AlgebraicGeometry.aB5OfSize_moduleCat_of_univLE.{u, max (u + 1) w, max (u + 1) w} Λ

/-! ### Exactness and acyclicity through the étale module stalks -/

omit [(curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive] in
/-- A sheaf of `Λ`-modules whose étale stalk at every geometric point vanishes vanishes. -/
public theorem isZero_of_forall_isZero_etaleModuleStalk
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    (h : ∀ s : GeometricPoint X.obj,
      IsZero ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj F)) :
    IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  refine (jointlyFaithful_etaleModuleStalkFunctor B X Λ).map_injective fun s => ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (h s).eq_of_src _ _

omit [(curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive] in
/-- A short complex of sheaves of `Λ`-modules whose étale stalk complexes are all exact is
exact. -/
public theorem exact_of_forall_etaleModuleStalk_exact
    (T : ShortComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
    (h : ∀ s : GeometricPoint X.obj,
      (T.map (etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s)).Exact) :
    T.Exact := by
  rw [T.exact_iff_isZero_homology]
  refine isZero_of_forall_isZero_etaleModuleStalk B X Λ _ fun s => ?_
  exact IsZero.of_iso ((T.map _).exact_iff_isZero_homology.1 (h s))
    (T.mapHomologyIso (etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s)).symm

omit [(curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive] in
/-- Taking étale stalks carries an acyclic complex of sheaves of `Λ`-modules to an acyclic
complex of `Λ`-modules. -/
public theorem acyclic_map_etaleModuleStalk (s : GeometricPoint X.obj)
    {K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (hK : K.Acyclic) :
    (((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic :=
  fun i => (HomologicalComplex.exactAt_iff _ i).2
    (((HomologicalComplex.exactAt_iff K i).1 (hK i)).map
      (etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s))

omit [(curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive] in
/-- A complex of sheaves of `Λ`-modules whose étale stalk complexes are all acyclic is
acyclic. -/
public theorem acyclic_of_forall_etaleModuleStalk_acyclic
    (K : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ)
    (h : ∀ s : GeometricPoint X.obj,
      (((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).Acyclic) :
    K.Acyclic := fun i =>
  (HomologicalComplex.exactAt_iff K i).2
    (exact_of_forall_etaleModuleStalk_exact B X Λ _ fun s =>
      (HomologicalComplex.exactAt_iff _ i).1 (h s i))

/-! ### Tensoring on the right is additive -/

/-- Tensoring on the right with a fixed sheaf is additive: it is the value at that sheaf of the
additive functor `curriedTensor`. -/
local instance additive_tensorRight
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) :
    (MonoidalCategory.tensorRight M).Additive where
  map_add {F F'} f g := by
    change ((curriedTensor _).map (f + g)).app M = _
    rw [(curriedTensor
      (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))).map_add]
    rfl

/-! ### Deliverable 1 -/

/-- The étale module stalk functor is monoidal: it is the fibre of a point of the site, for
which `AlgebraicGeometry.SmallEtale.modStalkMonoidal` supplies the structure. -/
local instance monoidal_etaleModuleStalkFunctor (s : GeometricPoint X.obj) :
    (etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).Monoidal :=
  AlgebraicGeometry.SmallEtale.modStalkMonoidal.{u, w} B Λ X s

/-- **The stalk functor is monoidal in the first variable.** Tensoring with a fixed sheaf `M`
and then taking the stalk at `s` is tensoring the stalk with the stalk of `M`, naturally in the
first variable; the components are
`AlgebraicGeometry.SmallEtale.modStalkTensorIso` and the squares commute by
`CategoryTheory.Functor.LaxMonoidal.μ_natural_left`. -/
public def stalkTensorRightIso (s : GeometricPoint X.obj)
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) :
    etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s ⋙
        MonoidalCategory.tensorRight
          ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj M) ≅
      MonoidalCategory.tensorRight M ⋙
        etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s :=
  NatIso.ofComponents
    (fun F => AlgebraicGeometry.SmallEtale.modStalkTensorIso.{u, w} B Λ X s F M)
    (fun f => Functor.LaxMonoidal.μ_natural_left _ f M)

/-- If `H` is intertwined with a homology preserving `H'` by a homology preserving `Φ`, then `H`
carries an acyclic complex to one whose `Φ`-image short complexes are exact. -/
private theorem exact_map_comp_of_natIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {Φ : C ⥤ D} [Φ.PreservesZeroMorphisms] [Φ.PreservesHomology]
    (G : CochainComplex C ℤ) (hG : G.Acyclic) (i : ℤ) (H : C ⥤ C) (H' : D ⥤ D)
    [H.PreservesZeroMorphisms] [H'.PreservesZeroMorphisms] [H'.PreservesHomology]
    (e : Φ ⋙ H' ≅ H ⋙ Φ) : ((G.sc i).map (H ⋙ Φ)).Exact :=
  ShortComplex.exact_of_iso ((G.sc i).mapNatIso e) <| by
    rw [ShortComplex.map_comp]
    exact (((HomologicalComplex.exactAt_iff G i).1 (hG i)).map Φ).map H'

omit [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive] in
/-- **Tensoring with a stalkwise-flat sheaf is exact on complexes.** -/
public theorem acyclic_rowComplex_of_flat_etaleModuleStalk
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    (hM : ∀ s : GeometricPoint X.obj,
        Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj M))
    (G : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ)
    (hG : G.Acyclic) :
    (CochainComplex.KFlatBifunctor.rowComplex
        (curriedTensor
          (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
        G M).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff]
  refine exact_of_forall_etaleModuleStalk_exact B X Λ _ fun s => ?_
  have : Module.Flat Λ
      ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj M) := hM s
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight
      ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj M)) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  exact exact_map_comp_of_natIso G hG i _ _ (stalkTensorRightIso B X Λ s M)

/-! ### Stacks 06YQ for the small étale tensor product -/

section KFlat

variable
  [∀ (P G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ)]
  [∀ K : HomologicalComplex₂ (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ)) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]

open scoped MonoidalClosed.FunctorCategory in
/-- **The sheaf category is monoidal closed**, by Day's reflection theorem applied to the
sheafification adjunction: the presheaf category is symmetric monoidal closed and
sheafification is monoidal. -/
local instance monoidalClosed_moduleSheaf :
    MonoidalClosed (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

/-- Sequential colimits are exact in the sheaf category: they are so in `Λ`-modules, and
sheafification is a left adjoint which preserves finite limits. -/
local instance hasExactColimitsOfShape_nat_moduleSheaf :
    HasExactColimitsOfShape ℕ (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)) :=
  haveI : HasExactColimitsOfShape ℕ (ModuleCat.{max (u + 1) w} Λ) :=
    TwoTermComplex.hasExactColimitsOfShape_nat_moduleCat.{max (u + 1) w} (R := Λ)
  inferInstance

omit [∀ (P G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ)]
  [∀ K : HomologicalComplex₂ (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  [(curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive]
  [∀ F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ),
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).obj F).Additive] in
/-- A sequential colimit of acyclic complexes of sheaves is acyclic. -/
public theorem acyclic_of_isColimit_nat
    (E : ℕ ⥤ CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)) ℤ) (c : Limits.Cocone E) (hc : Limits.IsColimit c)
    (hE : ∀ i, (E.obj i).Acyclic) : c.pt.Acyclic := fun n =>
  (CochainComplex.KFlat.acyclic_colimit E hE n).of_iso
    ((Limits.colimit.isColimit E).coconePointUniqueUpToIso hc)

omit [∀ (P G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ)] in
/-- **Stacks 06YQ for the étale sheaf tensor product.** A bounded-above complex of sheaves of
`Λ`-modules all of whose terms have flat étale stalks is K-flat. -/
public theorem kFlat_of_flat_etaleModuleStalk
    (G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)) ℤ) (b : ℤ) [G.IsStrictlyLE b]
    (hG : ∀ (i : ℤ) (s : GeometricPoint X.obj),
        Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w}
          B X Λ s).obj (G.X i))) :
    CochainComplex.KFlatBifunctor.KFlat
      (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) G :=
  CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ G b
    (fun Y => (ihom.adjunction Y).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape)
    (acyclic_of_isColimit_nat B X Λ)
    (fun q => CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ (G.X q) q
      (fun G' hG' =>
        acyclic_rowComplex_of_flat_etaleModuleStalk B X Λ (G.X q) (fun s => hG q s) G' hG'))

/-- The left-tensor companion of `stalkTensorRightIso`, by
`CategoryTheory.Functor.LaxMonoidal.μ_natural_right`. -/
public def stalkTensorLeftIso (s : GeometricPoint X.obj)
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) :
    etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s ⋙
        MonoidalCategory.tensorLeft
          ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj M) ≅
      MonoidalCategory.tensorLeft M ⋙
        etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s :=
  NatIso.ofComponents
    (fun F => AlgebraicGeometry.SmallEtale.modStalkTensorIso.{u, w} B Λ X s M F)
    (fun f => Functor.LaxMonoidal.μ_natural_right _ M f)

omit [∀ (P G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ)]
  [∀ K : HomologicalComplex₂ (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  [(curriedTensor
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))).Additive] in
/-- The left-tensor form of Deliverable 1: tensoring an acyclic complex on the left with a
stalkwise-flat sheaf is acyclic. -/
public theorem acyclic_rowComplex_flip_of_flat_etaleModuleStalk
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    (hM : ∀ s : GeometricPoint X.obj,
        Module.Flat Λ ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj M))
    (G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)) ℤ) (hG : G.Acyclic) :
    (CochainComplex.KFlatBifunctor.rowComplex
        (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ))).flip G M).Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff]
  refine exact_of_forall_etaleModuleStalk_exact B X Λ _ fun s => ?_
  have : Module.Flat Λ
      ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj M) := hM s
  exact exact_map_comp_of_natIso G hG i _ _ (stalkTensorLeftIso B X Λ s M)

/-- The sheaf category is braided, the coefficient category being so. -/
local instance braided_moduleSheaf : BraidedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) :=
  Sheaf.braidedCategory _ _

/-- Transposing the tensor bifunctor keeps it additive in the first variable: that is
additivity of `curriedTensor` in its second variable. -/
local instance additive_curriedTensor_flip :
    ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).flip).Additive where
  map_add {_ _} _ _ :=
    NatTrans.ext (funext fun F => ((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ))).obj F).map_add)

omit [∀ (P G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ)] in
/-- **Stacks 06YQ on the left.** The same hypotheses give left K-flatness, read through
`CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip`. -/
public theorem kFlatLeft_of_flat_etaleModuleStalk
    [∀ (P G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)) ℤ),
      HomologicalComplex.HasMapBifunctor P G
        (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ))).flip (ComplexShape.up ℤ)]
    (G : CochainComplex (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)) ℤ) (b : ℤ) [G.IsStrictlyLE b]
    (hG : ∀ (i : ℤ) (s : GeometricPoint X.obj),
        Module.Flat Λ
          ((etaleModuleStalkFunctor.{u, max (u + 1) w, max (u + 1) w} B X Λ s).obj (G.X i))) :
    CochainComplex.KFlatBifunctor.KFlatLeft
      (curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ))) G :=
  (CochainComplex.KFlatBifunctor.kFlatLeft_iff_kFlat_flip _ G).2
    (CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ G b
      (fun Y => by
        have : Limits.PreservesColimitsOfShape ℕ (MonoidalCategory.tensorLeft Y) :=
          (ihom.adjunction Y).leftAdjoint_preservesColimits.preservesColimitsOfShape
        exact Limits.preservesColimitsOfShape_of_natIso
          (BraidedCategory.tensorLeftIsoTensorRight Y))
      (acyclic_of_isColimit_nat B X Λ)
      (fun q => CochainComplex.KFlatBifunctor.kFlat_single_of_exact _ (G.X q) q
        (fun G' hG' =>
          acyclic_rowComplex_flip_of_flat_etaleModuleStalk B X Λ (G.X q) (fun s => hG q s) G' hG')))

end KFlat

/-! ### Insensitivity of the total complex to the representatives -/

section QuasiIso

variable
  [∀ (P G : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor P G
      (curriedTensor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
      (ComplexShape.up ℤ)]

/-- The mirror of `HomologicalComplex.mapBifunctorMap_eq_map₂_comp`:
the two one-variable maps compose to the two-variable one in the other order as well. -/
public theorem mapBifunctorMap_snd_comp_mapBifunctorMap_fst
    {P P' G G' : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (f : P' ⟶ P) (g : G' ⟶ G) :
    HomologicalComplex.mapBifunctorMap (𝟙 P') g
          (curriedTensor
            (Sheaf (SmallEtale.topology B X.obj X.property)
              (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap f (𝟙 G)
          (curriedTensor
            (Sheaf (SmallEtale.topology B X.obj X.property)
              (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap f g
        (curriedTensor
          (Sheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{max (u + 1) w} Λ))) (ComplexShape.up ℤ) := by
  have hn := (((curriedTensor (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) w} Λ))).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map f).naturality g
  exact hn.trans
    (HomologicalComplex.mapBifunctorMap_eq_map₂_comp _ _ f g)

/-- **The quasi-isomorphism comparison of two total complexes.** -/
public theorem quasiIso_mapBifunctorMap
    {P P' G G' : CochainComplex
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (f : P' ⟶ P) (g : G' ⟶ G) (hf : QuasiIso f) (hg : QuasiIso g)
    (hG : CochainComplex.KFlatBifunctor.KFlat
      (curriedTensor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))) G)
    (hP' : CochainComplex.KFlatBifunctor.KFlatLeft
      (curriedTensor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))) P') :
    QuasiIso (HomologicalComplex.mapBifunctorMap f g
      (curriedTensor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
      (ComplexShape.up ℤ)) := by
  have h1 : QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 P') g
      (curriedTensor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
      (ComplexShape.up ℤ)) :=
    CochainComplex.KFlatBifunctor.quasiIso_of_kFlatLeft _ P' hP' g hg
  have h2 : QuasiIso (HomologicalComplex.mapBifunctorMap f (𝟙 G)
      (curriedTensor
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)))
      (ComplexShape.up ℤ)) :=
    CochainComplex.KFlatBifunctor.quasiIso_of_kFlat _ G hG f hf
  rw [← mapBifunctorMap_snd_comp_mapBifunctorMap_fst B X Λ f g]
  infer_instance

end QuasiIso

end Stacks.EtaleCohomology

end
