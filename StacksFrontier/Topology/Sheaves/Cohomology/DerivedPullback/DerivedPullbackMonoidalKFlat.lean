module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorKFlat
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatMonoidalFunctorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackKFlatMonoidal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitCoherence

/-!
# The tensorator of derived pullback on K-flat complexes

For a morphism of ringed spaces `f : X ⟶ Y` and K-flat complexes `K`, `L` of `𝒪_Y`-modules, the
tensorator `Lf^*(QK ⊗ᴸ QL) ≅ Lf^*QK ⊗ᴸ Lf^*QL` of the monoidal structure
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal` is computed by the
degreewise comparison of [Stacks, Tag 01CD]: at the standard model it is the comparison
`Stacks.Cohomology.DerivedPullbackTensor.modelComparison` through which the isomorphism of
[Stacks, Tag 079U] is constructed.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open CochainComplex.KFlatBifunctor RingedSpaceModuleAdjunction
open scoped CategoryTheory.Prod

universe w₁ w₂ u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory
  abelianStructureSheafRing

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

section Model

variable [HasDerivedCategory.{w₁} (SheafOfModules.{u} (structureSheafRing X))]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheafRing Y))]

attribute [local instance] hasDerivedCategoryModulesX hasDerivedCategoryModulesY

/-! ### The tensorator on K-flat complexes -/

attribute [local instance] CochainComplex.KFlatMonoidal.homotopyMonoidal in
/-- **The tensorator of `Lf^*` on K-flat complexes** ([Stacks, Tag 079U]): for K-flat complexes
`K`, `L` of `𝒪_Y`-modules, the oplax tensorator `Lf^*(QK ⊗ᴸ QL) ⟶ Lf^*QK ⊗ᴸ Lf^*QL` of
`derivedPullbackCanonicalMonoidal`, followed by the comparisons `Lf^*QK ≅ Q(f^*K)` and the
K-flat comparison of the derived tensor product on `X`, is the K-flat comparison on `Y` followed
by `Lf^*Q(K ⊗ L) ≅ Q(f^*(K ⊗ L))` and the comparison of total tensor complexes of
[Stacks, Tag 01CD]. -/
theorem derivedPullbackCanonicalMonoidal_δ_comp
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) K)
    (hL : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) L) :
    @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          (CochainComplex.KFlatMonoidal.derivedFunctorQComparison
            (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
            (derivedPullbackKFlatIso f) hK)).app _ ≫
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).map
          (CochainComplex.KFlatMonoidal.derivedFunctorQComparison
            (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
            (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
            (derivedPullbackKFlatIso f) hL) ≫
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).comparison
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlat_pullbackComplex f K hK) (kFlat_pullbackComplex f L hL)).hom =
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).comparison
          K L hK hL).hom ≫
      CochainComplex.KFlatMonoidal.derivedFunctorQComparison
          (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
          (derivedPullbackKFlatIso f)
          (CochainComplex.KFlatMonoidal.kFlat_tensor _ hK hL) ≫
      DerivedCategory.Q.map (Functor.OplaxMonoidal.δ (pullbackComplex f) K L) :=
  CochainComplex.KFlatMonoidal.reseatFunctorMonoidal_δ_comp_derivedFunctorQComparison
    (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackKFlatIso f) _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf)
    (fun K L hK hL =>
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).comparison K L hK hL)
    (fun K L hK hL =>
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).comparison K L hK hL)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso_inv_app_app Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso_hom_app_app X.sheaf)
    hK hL

/-- **The unit of `Lf^*` on the unit complex**: the lax unit `𝒪_X[0] ⟶ Lf^*(𝒪_Y[0])` of
`derivedPullbackCanonicalMonoidal`, followed by the comparison `Lf^*Q(𝒪_Y[0]) ≅ Q(f^*𝒪_Y[0])`, is
the image under `Q` of the unit of `f^*` on complexes. -/
theorem derivedPullbackCanonicalMonoidal_ε_comp :
    @Functor.LaxMonoidal.ε _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toLaxMonoidal ≫
      CochainComplex.KFlatMonoidal.derivedFunctorQComparison
        (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackKFlatIso f) (CochainComplex.KFlatMonoidal.kFlat_tensorUnit _) =
    DerivedCategory.Q.map (Functor.LaxMonoidal.ε (pullbackComplex f)) :=
  CochainComplex.KFlatMonoidal.reseatFunctorMonoidal_ε_comp_derivedFunctorQComparison
    (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.sheaf)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (derivedPullbackKFlatIso f) _ _
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso Y.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)

end Model

/-! ### The standard model -/

section Standard

/-- Two families of morphisms `F.obj X ⟶ G.obj X`, both natural, which agree at `Y` agree at every
object isomorphic to `Y`. -/
private lemma eq_of_iso_of_natural {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (a b : ∀ X, F.obj X ⟶ G.obj X)
    (ha : ∀ {X Y : C} (u : X ⟶ Y), F.map u ≫ a Y = a X ≫ G.map u)
    (hb : ∀ {X Y : C} (u : X ⟶ Y), F.map u ≫ b Y = b X ≫ G.map u) {X Y : C} (e : X ≅ Y)
    (h : a X = b X) : a Y = b Y := by
  rw [← cancel_epi (F.map e.hom), ha, hb, h]

/-- If `x ≫ a ≫ b ≫ c = y ≫ p ≫ d` and `d ≫ m = 𝟙`, then `x ≫ (a ≫ b) ≫ c ≫ m = y ≫ p`, with `c`
and `m` given up to equality. -/
private lemma comp_eq_of_comp_eq {C : Type*} [Category C] {S T₁ T₂ T₃ T₄ T₅ V : C}
    {x : S ⟶ T₁} {a : T₁ ⟶ T₂} {b : T₂ ⟶ T₃} {c c' : T₃ ⟶ T₄} {y : S ⟶ V} {p : V ⟶ T₅}
    {d : T₅ ⟶ T₄} {m m' : T₄ ⟶ T₅}
    (h : x ≫ a ≫ b ≫ c = y ≫ p ≫ d) (hc : c' = c) (hm : m' = m) (hdm : d ≫ m = 𝟙 T₅) :
    x ≫ (a ≫ b) ≫ c' ≫ m' = y ≫ p := by
  subst hc hm
  rw [Category.assoc, reassoc_of% h, hdm, Category.comp_id]

attribute [local instance] HasDerivedCategory.standard

/-- The left comparison of [Stacks, Tag 079U] on a pair of K-flat complexes. -/
private lemma leftComparison_app_eq_aux
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) K)
    (hL : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) L) :
    (leftComparison f).app (K, L) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).comparison
            K L hK hL).hom ≫
        CochainComplex.KFlatMonoidal.derivedFunctorQComparison
          (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
          (derivedPullbackKFlatIso f) (CochainComplex.KFlatMonoidal.kFlat_tensor _ hK hL) :=
  congrArg (fun x => (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map x ≫
      (derivedPullbackNatTrans f).app _)
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.sheaf).toTensor_eq_comparison
      K L hK hL)

/-- The right comparison of [Stacks, Tag 079U] at a pair of complexes, unfolded. -/
private lemma rightComparison_app_eq_aux₁
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (rightComparison f).app (K, L) =
      (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
          ((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) ≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).toTensor
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L) ≫
        DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app (K, L)) := rfl

/-- The right comparison of [Stacks, Tag 079U] on a pair of K-flat complexes. -/
private lemma rightComparison_app_eq_aux
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) K)
    (hL : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) L) :
    (rightComparison f).app (K, L) =
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          (CochainComplex.KFlatMonoidal.derivedFunctorQComparison
          (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
          (derivedPullbackKFlatIso f) hK)).app _ ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj _).map
          (CochainComplex.KFlatMonoidal.derivedFunctorQComparison
          (StacksDraft.KFlat.modulePullback f) (kFlat_pullbackComplex f)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
          (derivedPullbackKFlatIso f) hL)) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf).comparison
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlat_pullbackComplex f K hK) (kFlat_pullbackComplex f L hL)).hom ≫
        DerivedCategory.Q.map (Functor.LaxMonoidal.μ (pullbackComplex f) K L) :=
  (rightComparison_app_eq_aux₁ f K L).trans
    (congrArg₂ (fun x y => _ ≫ x ≫ DerivedCategory.Q.map y)
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          X.sheaf).toTensor_eq_comparison
        _ _ (kFlat_pullbackComplex f K hK) (kFlat_pullbackComplex f L hL))
      (pullbackTensorComplexNatIso_inv_app_eq f (isComparisonTensorator_sheafTensor f) K L))

/-- **At the standard model, the tensorator of `Lf^*` on a pair of K-flat complexes is the
comparison `modelComparison`** through which the isomorphism of [Stacks, Tag 079U] is
constructed. -/
theorem derivedPullbackCanonicalMonoidal_δ_eq_modelComparison
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) K)
    (hL : KFlat (curriedTensor (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) L) :
    @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
      (modelComparison f K L hK hL).hom := by
  have : IsIso ((rightComparison f).app (K, L)) := isIso_rightComparison_app f K L hK hL
  exact (IsIso.eq_comp_inv _).2 ((congrArg (_ ≫ ·) (rightComparison_app_eq_aux f K L hK hL)).trans
    ((comp_eq_of_comp_eq (derivedPullbackCanonicalMonoidal_δ_comp f K L hK hL) rfl rfl
      ((DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
        (Functor.Monoidal.δ_μ _ _ _)).trans (DerivedCategory.Q.map_id _)))).trans
      (leftComparison_app_eq_aux f K L hK hL).symm))

/-- **[Stacks, Tag 079U]: at the standard model, the tensorator of the monoidal structure
`derivedPullbackCanonicalMonoidal` of `Lf^*` is the comparison
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`**, at every pair of objects. -/
theorem derivedPullbackCanonicalMonoidal_δ_eq_derivedPullbackTensorIso
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K L =
      (derivedPullbackTensorIso f).hom.app (K, L) := by
  have res : ∀ M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y),
      ∃ (P : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
        (_ : KFlat (curriedTensor (RingedSpace.KFlatDerivedPullback.Modules Y)) P),
        Nonempty (DerivedCategory.Q.obj P ≅ M) := by
    intro M
    obtain ⟨P, π, hP, hπ⟩ :=
      Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso Y.sheaf
        (DerivedCategory.Q.objPreimage M)
    have : IsIso (DerivedCategory.Q.map π) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ π).2 hπ
    exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩
  obtain ⟨P, hP, ⟨eK⟩⟩ := res K
  obtain ⟨P', hP', ⟨eL⟩⟩ := res L
  refine eq_of_iso_of_natural (F := Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf) ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (G := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).prod
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ⋙
      Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf))
    (fun M => @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal M.1 M.2)
    (fun M => (derivedPullbackTensorIso f).hom.app M)
    (fun u => (@Functor.OplaxMonoidal.δ_natural _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal _ _ _ _ u.1 u.2).symm)
    (fun u => (derivedPullbackTensorIso f).hom.naturality u) (X := (DerivedCategory.Q.obj P,
      DerivedCategory.Q.obj P')) (Y := (K, L)) (eK.prod eL) ?_
  exact (derivedPullbackCanonicalMonoidal_δ_eq_modelComparison f P P' hP hP').trans
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison_app_q_of_kFlat
      f P P' hP hP').symm

end Standard

end Stacks.Cohomology.DerivedPullbackTensor

end
