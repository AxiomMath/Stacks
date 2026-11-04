module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapCanonical
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.Devissage
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SitePointStalkColimits
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsNoLeftAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.EilenbergWatts.DevissageNatTrans

/-!
# Geometric stalks of associated modules on affine representable spaces

Let `U` be an object of the big fppf site over `S` whose underlying scheme is affine, with ring
of global functions `A`, and let `x̄` be a geometric point of the algebraic space `yoneda.obj U`.
For an `A`-module `M` with associated module `M^~`, the geometric stalk is
`(M^~)_{x̄} ≅ 𝒪_{x̄} ⊗_A M`, naturally in `M`, along a flat ring map `A ⟶ 𝒪_{x̄}`; and these ring
maps are compatible with the stalk maps of morphisms of affine representables.

## Main definitions

* `Stacks.ExtendScalarsComparison.natTrans`: for a functor `G` from `A`-modules to `O`-modules
  and an element `g ∈ G(A)` on which `A` acts through `δ : A ⟶ O`, the natural map
  `O ⊗_A M ⟶ G(M)`.
* `AlgebraicGeometry.Space.representedAffineGlobalStalkRingHom`: the ring map `A ⟶ 𝒪_{x̄}` through
  which `A` acts on the stalk of `A^~`.
* `AlgebraicGeometry.Space.representedAffineStalkIso`: `𝒪_{x̄} ⊗_A M ≅ (M^~)_{x̄}`.
* `AlgebraicGeometry.Space.representedStalkGerm`: the germ map `Γ(U, 𝒪) ⟶ 𝒪_{x̄}` read over the
  identity chart.

## Main results

* `Stacks.ExtendScalarsComparison.isIso_natTrans`: the natural map is an isomorphism when `G`
  preserves colimits and `g` generates `G(A)`.
* `AlgebraicGeometry.Space.flat_representedAffineStalkRingHom`: `𝒪_{x̄}` is flat over `A`.
* `AlgebraicGeometry.Space.stalkStructureMap_representedAffineStalkRingHom`: for `g : P ⟶ U` of
  affine objects the stalk map of `g` at `x̄'` restricted to `Γ(U, 𝒪)` is
  `Γ(U, 𝒪) ⟶ Γ(P, 𝒪) ⟶ 𝒪_{x̄'}`.
* `AlgebraicGeometry.Space.stalkStructureMap_comp_representedStalkGerm`: the same for germs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings TensorProduct

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace Stacks

/-! ### The stalk of a sheaf of modules commutes with colimits of the size of the rings -/

section StalkColimits

variable {C : Type*} [Category.{u} C] [LocallySmall.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The stalk of a sheaf of modules at a point of a site commutes with colimits indexed by
categories of the size of the rings. -/
theorem preservesColimitsOfSize_sheafModuleFiber (R : Sheaf J RingCat.{u}) (Φ : J.Point.{u}) :
    PreservesColimitsOfSize.{u, u} (sheafModuleFiber Φ R) := by
  have h0 : PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} R) :=
    preservesColimitsOfSize_shrink _
  have hcomp : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.toSheaf.{u} R ⋙ Φ.sheafFiber (A := AddCommGrpCat.{u})) := inferInstance
  have hforget : PreservesColimitsOfSize.{u, u} (sheafModuleFiber Φ R ⋙
      forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj))
        AddCommGrpCat.{u}) :=
    preservesColimits_of_natIso (sheafModuleFiberCompForget₂ Φ R).symm
  have hreflects : ReflectsColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj))
        AddCommGrpCat.{u}) := reflectsColimits_of_reflectsIsomorphisms
  exact preservesColimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u} ((Φ.presheafFiber (A := RingCat.{u})).obj R.obj))
      AddCommGrpCat.{u})

/-- The stalk functor over the stalk of a sheaf of commutative rings commutes with colimits
indexed by categories of the size of the rings. -/
theorem preservesColimitsOfSize_sheafModuleFiberOfCommRing (Φ : J.Point.{u})
    (O : Sheaf J CommRingCat.{u}) [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] :
    PreservesColimitsOfSize.{u, u} (sheafModuleFiberOfCommRing Φ O) := by
  have := preservesColimitsOfSize_sheafModuleFiber (commRingSheafToRingSheaf O) Φ
  show PreservesColimitsOfSize.{u, u}
    (sheafModuleFiber Φ (commRingSheafToRingSheaf O) ⋙
      ModuleCat.restrictScalars.{u} (commRingSheafFiberIso Φ O).inv.hom)
  infer_instance

end StalkColimits

end Stacks

namespace Stacks.ExtendScalarsComparison

/-! ### Natural maps out of extension of scalars -/

variable {A O : Type u} [CommRing A] [CommRing O] (δ : A →+* O)
  (G : ModuleCat.{u} A ⥤ ModuleCat.{u} O) [G.Additive] (g : G.obj (ModuleCat.of A A))
  (hg : ∀ a : A, (G.map (a • 𝟙 (ModuleCat.of A A))).hom g = δ a • g)

/-- The map `M ⟶ G(M)`, `m ↦ G(a ↦ a • m)(g)`, linear over `δ`. -/
def linearMap (M : ModuleCat.{u} A) : M →ₗ[A] (ModuleCat.restrictScalars δ).obj (G.obj M) where
  toFun m := (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))).hom g
  map_add' m m' := by
    change (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M (m + m')))).hom g =
      (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))).hom g +
        (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m'))).hom g
    rw [LinearMap.toSpanSingleton_add, ModuleCat.ofHom_add, CategoryTheory.Functor.map_add,
      ModuleCat.hom_add, LinearMap.add_apply]
  map_smul' a m := by
    have h : ModuleCat.ofHom (LinearMap.toSpanSingleton A M (a • m)) =
        (a • 𝟙 (ModuleCat.of A A)) ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton A M m) := by
      refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
      change t • a • m = (a • t) • m
      rw [smul_smul, smul_eq_mul, mul_comm]
    change (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M (a • m)))).hom g =
      δ a • (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))).hom g
    rw [h, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hg,
      map_smul]

include hg in
/-- The map `M ⟶ G(M)` is natural in `M`. -/
theorem linearMap_naturality {M N : ModuleCat.{u} A} (h : M ⟶ N) (m : M) :
    linearMap δ G g hg N (h.hom m) = (G.map h).hom (linearMap δ G g hg M m) := by
  have hc : ModuleCat.ofHom (LinearMap.toSpanSingleton A N (h.hom m)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton A M m) ≫ h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    show t • h.hom m = h.hom (t • m)
    rw [map_smul]
  show (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A N (h.hom m)))).hom g =
    (G.map h).hom ((G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A M m))).hom g)
  rw [hc, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The map `O ⊗_A M ⟶ G(M)`, `t ⊗ m ↦ t • G(a ↦ a • m)(g)`. -/
def app (M : ModuleCat.{u} A) : (ModuleCat.extendScalars.{u, u, u} δ).obj M ⟶ G.obj M :=
  ((ModuleCat.extendRestrictScalarsAdj δ).homEquiv _ _).symm
    (ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars δ).obj (G.obj M))
      (linearMap δ G g hg M))

/-- The map `O ⊗_A M ⟶ G(M)` sends `1 ⊗ m` to `G(a ↦ a • m)(g)`. -/
theorem app_one_tmul (M : ModuleCat.{u} A) (m : M) :
    (app δ G g hg M).hom ((1 : O) ⊗ₜ[A, δ] m) = linearMap δ G g hg M m :=
  (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (app δ G g hg M) m).symm.trans
    (congrArg (fun φ => φ.hom m) (Equiv.apply_symm_apply
      ((ModuleCat.extendRestrictScalarsAdj δ).homEquiv M (G.obj M))
      (ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars δ).obj (G.obj M))
        (linearMap δ G g hg M))))

/-- The natural map `O ⊗_A M ⟶ G(M)`, `t ⊗ m ↦ t • G(a ↦ a • m)(g)`. -/
def natTrans : ModuleCat.extendScalars.{u, u, u} δ ⟶ G where
  app M := app δ G g hg M
  naturality M N h := by
    refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
    exact (congrArg (app δ G g hg N).hom (ModuleCat.ExtendScalars.map_tmul δ h 1 m)).trans
      ((app_one_tmul δ G g hg N _).trans ((linearMap_naturality δ G g hg h m).trans
        (congrArg (G.map h).hom (app_one_tmul δ G g hg M m).symm)))

include hg in
/-- The value of the linear map at `a ∈ A` is `δ a • g`. -/
theorem linearMap_self (a : A) : linearMap δ G g hg (ModuleCat.of A A) a = δ a • g := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton A (ModuleCat.of A A) a) =
      a • 𝟙 (ModuleCat.of A A) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    show t • a = a • t
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  show (G.map (ModuleCat.ofHom (LinearMap.toSpanSingleton A (ModuleCat.of A A) a))).hom g = _
  rw [h, hg]

include hg in
/-- The natural map is invertible at `A` as soon as `g` is a generator of `G(A)`, in the sense that
some isomorphism `G(A) ≅ O` sends it to `1`. -/
theorem isIso_app_self (e : G.obj (ModuleCat.of A A) ≅ ModuleCat.of O O) (he : e.hom.hom g = 1) :
    IsIso (app δ G g hg (ModuleCat.of A A)) := by
  let E := (ModuleCat.extendScalars.{u, u, u} δ).obj (ModuleCat.of A A)
  let f : E ⟶ ModuleCat.of O O := app δ G g hg (ModuleCat.of A A) ≫ e.hom
  let one : E := (1 : O) ⊗ₜ[A, δ] (1 : A)
  let k : ModuleCat.of O O ⟶ E :=
    @ModuleCat.ofHom O _ O E _ _ E.isAddCommGroup E.isModule
      (@LinearMap.toSpanSingleton O E _ E.isAddCommGroup.toAddCommMonoid E.isModule one)
  have hc : ∀ a : A, f.hom ((1 : O) ⊗ₜ[A, δ] a) = δ a := by
    intro a
    show e.hom.hom ((app δ G g hg (ModuleCat.of A A)).hom ((1 : O) ⊗ₜ[A, δ] a)) = δ a
    rw [app_one_tmul, linearMap_self δ G g hg a, map_smul, he]
    show δ a * 1 = δ a
    rw [mul_one]
  have h1 : f ≫ k = 𝟙 E := by
    refine ModuleCat.ExtendScalars.hom_ext fun a => ?_
    show k.hom (f.hom ((1 : O) ⊗ₜ[A, δ] a)) = (1 : O) ⊗ₜ[A, δ] a
    rw [hc]
    refine (ModuleCat.ExtendScalars.smul_tmul (f := δ) (M := ModuleCat.of A A) (δ a) 1 1).trans ?_
    let R' := (ModuleCat.restrictScalars δ).obj (ModuleCat.of O O)
    let o : R' := (1 : O)
    have h3 : ((δ a * 1 : O) : R') = a • o := rfl
    exact (congrArg (fun t : R' => t ⊗ₜ[A] (1 : A)) h3).trans
      ((TensorProduct.smul_tmul a o (1 : A)).trans
        (congrArg (fun t : A => o ⊗ₜ[A] t) (mul_one a)))
  have h2 : k ≫ f = 𝟙 (ModuleCat.of O O) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
    show f.hom (@HSMul.hSMul O E E (@instHSMul O E (@SMulZeroClass.toSMul O E _
      (@SMulWithZero.toSMulZeroClass O E _ _ (@MulActionWithZero.toSMulWithZero O E _ _
        (@Module.toMulActionWithZero O E _ _ E.isModule))))) t one) = t
    rw [map_smul, hc, map_one]
    exact mul_one t
  have hf : IsIso f := ⟨k, h1, h2⟩
  exact IsIso.of_isIso_comp_right (app δ G g hg (ModuleCat.of A A)) e.hom

include hg in
/-- The natural map `O ⊗_A M ⟶ G(M)` is an isomorphism for a colimit-preserving `G` and a
generator `g` of `G(A)`. -/
theorem isIso_natTrans [PreservesColimitsOfSize.{u, u} G]
    (e : G.obj (ModuleCat.of A A) ≅ ModuleCat.of O O) (he : e.hom.hom g = 1) :
    IsIso (natTrans δ G g hg) := by
  have : PreservesColimitsOfSize.{u, u} (ModuleCat.extendScalars.{u, u, u} δ) :=
    (ModuleCat.extendRestrictScalarsAdj δ).leftAdjoint_preservesColimits
  have := isIso_app_self δ G g hg e he
  have h : ∀ M, IsIso ((natTrans δ G g hg).app M) := fun M =>
    @Stacks.EilenbergWatts.isIso_app_of_isIso_app_unit A _ _ _ _ _ _ _ (natTrans δ G g hg) this M
  exact NatIso.isIso_of_isIso_app _

/-- Extension of scalars carries multiplication by `a` to multiplication by its image. -/
theorem extendScalars_map_smul_id {R T : Type u} [CommRing R] [CommRing T] (ψ : R →+* T)
    (M : ModuleCat.{u} R) (a : R) :
    (ModuleCat.extendScalars.{u, u, u} ψ).map (a • 𝟙 M) = ψ a • 𝟙 _ := by
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  exact (ModuleCat.ExtendScalars.map_tmul ψ (a • 𝟙 M) 1 m).trans
    (((ModuleCat.extendRestrictScalarsAdj ψ).unit.app M).hom.map_smul a m)

/-- Scalar multiples of the identity correspond along an isomorphism. -/
theorem smul_id_transport {T : Type u} [CommRing T] {Z W : ModuleCat.{u} T} (χ : Z ≅ W) {r s : T}
    (h : r • 𝟙 Z = s • 𝟙 Z) : r • 𝟙 W = s • 𝟙 W := by
  have h' := congrArg (fun f => χ.inv ≫ f ≫ χ.hom) h
  simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Iso.inv_hom_id] using h'

end Stacks.ExtendScalarsComparison

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The germ of global functions at a geometric point -/

section Germ

variable (U : BigFppfOver B S hS)

/-- The lift of a geometric point of `yoneda.obj U` into the identity chart: the geometric point
itself. -/
def selfChartFiberPoint (x : GeometricPoint B S hS (yoneda.obj U)) :
    GeometricFiber B S hS (yoneda.obj U) x (selfChart B S hS U) :=
  ⟨x.val.value, rfl⟩

/-- The germ map `Γ(U, 𝒪) ⟶ 𝒪_{yoneda.obj U, x̄}` sending a global function on the scheme
underlying `U` to its germ at `x̄`, read over the identity chart. -/
def representedStalkGerm (x : GeometricPoint B S hS (yoneda.obj U)) :
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⟶
      geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x :=
  (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U)).toPresheafFiber
    (selfChart B S hS U) (selfChartFiberPoint B S hS U x)
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O.obj

end Germ

/-- The germ maps form a commutative square with the stalk map: for `g : P ⟶ U` and a
geometric point `x̄'` of `yoneda.obj P`, the germ at `x̄'` of the pullback of a global function
on `U` is the image under the stalk map of `g` of its germ at `g(x̄')`. -/
theorem stalkStructureMap_comp_representedStalkGerm {P U : BigFppfOver B S hS} (g : P ⟶ U)
    (x : GeometricPoint B S hS (yoneda.obj P)) :
    representedStalkGerm B S hS U (geometricPointMap (representedSpaceMap B S hS g).hom x) ≫
        stalkStructureMap B S hS (representedSpaceMap B S hS g) x =
      Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map g) ≫
        representedStalkGerm B S hS P x := by
  ext s
  exact stalkStructureMap_toPresheafFiber B S hS (representedSpaceMap B S hS g) x
    ⟨selfChart B S hS P, selfChart B S hS U, g,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩
    (selfChartFiberPoint B S hS P x)
    (selfChartFiberPoint B S hS U (geometricPointMap (representedSpaceMap B S hS g).hom x)) rfl s

/-! ### The geometric stalk of an associated module -/

section Stalk

variable (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (x : GeometricPoint B S hS (yoneda.obj U))

/-- The geometric stalk at `x̄` of the associated module: `M ↦ (M^~)_{x̄}`, from `A`-modules to
modules over `𝒪_{yoneda.obj U, x̄}`. -/
abbrev representedAffineStalk :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⥤
      ModuleCat.{u} (geometricStalkRing B S hS
        (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x) :=
  representedAffineAssociated B S hS U ⋙
    Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- The geometric stalk of the associated module is additive. -/
instance additive_representedAffineStalk : (representedAffineStalk B S hS U x).Additive where
  map_add {M N f g} := by
    have := additive_representedAffineAssociated B S hS U
    have := Stacks.instAdditiveSheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O
    exact (congrArg (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).map
        ((representedAffineAssociated B S hS U).map_add (f := f) (g := g))).trans
      (Functor.map_add _)

/-- The stalk of `A^~` is free of rank one: `A^~ ≅ 𝒪` and the stalk of `𝒪` is `𝒪_{x̄}`. -/
def representedAffineStalkUnitIso :
    (representedAffineStalk B S hS U x).obj (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≅
      ModuleCat.of (geometricStalkRing B S hS
          (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x)
        (geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x) :=
  (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).mapIso
      (representedAffineAssociatedObjUnitIso B S hS U) ≪≫
    Stacks.unitModuleStalkIso
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O

/-- An endomorphism of a commutative ring, as a module over itself, is multiplication by its
value at `1`. -/
private theorem endo_eq_smul_id {R : Type u} [CommRing R]
    (f : ModuleCat.of R R ⟶ ModuleCat.of R R) : f = f.hom 1 • 𝟙 _ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  show f.hom t = f.hom 1 * t
  have h := f.hom.map_smul t 1
  rw [smul_eq_mul, mul_one] at h
  rw [h, smul_eq_mul, mul_comm]

/-- The scalar by which `a ∈ A` acts on the stalk of `A^~`, read through
`representedAffineStalkUnitIso`. -/
def representedAffineStalkScalarFun (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x :=
  (representedAffineStalkUnitIso B S hS U x).hom.hom
    (((representedAffineStalk B S hS U x).map
        (a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))).hom
      ((representedAffineStalkUnitIso B S hS U x).inv.hom 1))

/-- Multiplication by `a` on `A`, after taking the stalk of the associated module, is
multiplication by `representedAffineStalkScalarFun a`. -/
theorem representedAffineStalk_map_smul_id_unit (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineStalk B S hS U x).map
        (a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) =
      representedAffineStalkScalarFun B S hS U x a • 𝟙 _ := by
  set e := representedAffineStalkUnitIso B S hS U x
  set f := (representedAffineStalk B S hS U x).map
    (a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
  have h := endo_eq_smul_id (e.inv ≫ f ≫ e.hom)
  have h1 : (e.inv ≫ f ≫ e.hom).hom 1 = representedAffineStalkScalarFun B S hS U x a := rfl
  rw [h1] at h
  calc f = e.hom ≫ (e.inv ≫ f ≫ e.hom) ≫ e.inv := by simp
    _ = _ := by rw [h, Linear.smul_comp, Linear.comp_smul, Category.id_comp, e.hom_inv_id]

/-- Two scalars acting in the same way on the stalk of `A^~` are equal. -/
theorem representedAffineStalkScalar_unique
    {c d : geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x}
    (h : c • 𝟙 ((representedAffineStalk B S hS U x).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) = d • 𝟙 _) : c = d := by
  simpa using congrArg (fun f => f.hom 1) (Stacks.ExtendScalarsComparison.smul_id_transport
    (representedAffineStalkUnitIso B S hS U x) h)

/-- The ring map `A ⟶ 𝒪_{yoneda.obj U, x̄}` through which `A` acts on the geometric stalk at `x̄`
of the associated module of `A`. -/
def representedAffineGlobalStalkRingHom :
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) →+*
      geometricStalkRing B S hS (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) x where
  toFun := representedAffineStalkScalarFun B S hS U x
  map_one' := by
    refine representedAffineStalkScalar_unique B S hS U x ?_
    rw [← representedAffineStalk_map_smul_id_unit, one_smul, one_smul,
      CategoryTheory.Functor.map_id]
  map_mul' a b := by
    refine representedAffineStalkScalar_unique B S hS U x ?_
    have hc : a • b • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) =
        (b • 𝟙 _) ≫ (a • 𝟙 _) := by
      rw [Linear.comp_smul, Category.comp_id]
    rw [← representedAffineStalk_map_smul_id_unit, mul_smul, hc, CategoryTheory.Functor.map_comp,
      representedAffineStalk_map_smul_id_unit, representedAffineStalk_map_smul_id_unit,
      Linear.comp_smul, Category.comp_id, mul_smul]
  map_zero' := by
    refine representedAffineStalkScalar_unique B S hS U x ?_
    rw [← representedAffineStalk_map_smul_id_unit, zero_smul, zero_smul,
      CategoryTheory.Functor.map_zero]
  map_add' a b := by
    refine representedAffineStalkScalar_unique B S hS U x ?_
    rw [← representedAffineStalk_map_smul_id_unit, add_smul, add_smul,
      CategoryTheory.Functor.map_add,
      representedAffineStalk_map_smul_id_unit, representedAffineStalk_map_smul_id_unit]

/-- Multiplication by `a` on `A`, after taking the stalk of the associated module, is
multiplication by `representedAffineGlobalStalkRingHom a`. -/
theorem representedAffineStalk_map_smul_id_unit' (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineStalk B S hS U x).map
        (a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) =
      representedAffineGlobalStalkRingHom B S hS U x a • 𝟙 _ :=
  representedAffineStalk_map_smul_id_unit B S hS U x a

/-- `a ∈ A` acts on the generator of the stalk of `A^~` through
`representedAffineGlobalStalkRingHom`. -/
theorem representedAffineStalk_map_smul_id_generator
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((representedAffineStalk B S hS U x).map
        (a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))).hom
        ((representedAffineStalkUnitIso B S hS U x).inv.hom 1) =
      representedAffineGlobalStalkRingHom B S hS U x a •
        (representedAffineStalkUnitIso B S hS U x).inv.hom 1 := by
  rw [representedAffineStalk_map_smul_id_unit']
  rfl

/-- The geometric stalk of the associated module preserves colimits. -/
instance preservesColimitsOfSize_representedAffineStalk :
    PreservesColimitsOfSize.{u, u} (representedAffineStalk B S hS U x) := by
  have h1 : PreservesColimitsOfSize.{u, u} (representedAffineAssociated B S hS U) :=
    (representedAffineAssociatedAdjunction B S hS U).leftAdjoint_preservesColimits
  have h2 := Stacks.preservesColimitsOfSize_sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ h1 h2

/-- The geometric stalk of an associated module: for an `A`-module `M` and a geometric point
`x̄` of `yoneda.obj U`, `(M^~)_{x̄} ≅ 𝒪_{x̄} ⊗_A M`, naturally in `M`, where `A ⟶ 𝒪_{x̄}` is
`representedAffineGlobalStalkRingHom`. -/
def representedAffineStalkIso :
    ModuleCat.extendScalars.{u, u, u} (representedAffineGlobalStalkRingHom B S hS U x) ≅
      representedAffineStalk B S hS U x :=
  have := Stacks.ExtendScalarsComparison.isIso_natTrans
    (representedAffineGlobalStalkRingHom B S hS U x)
    (representedAffineStalk B S hS U x) ((representedAffineStalkUnitIso B S hS U x).inv.hom 1)
    (representedAffineStalk_map_smul_id_generator B S hS U x)
    (representedAffineStalkUnitIso B S hS U x)
    (by rw [← ModuleCat.comp_apply, Iso.inv_hom_id]; rfl)
  asIso (Stacks.ExtendScalarsComparison.natTrans (representedAffineGlobalStalkRingHom B S hS U x)
    (representedAffineStalk B S hS U x) ((representedAffineStalkUnitIso B S hS U x).inv.hom 1)
    (representedAffineStalk_map_smul_id_generator B S hS U x))

/-- The geometric stalk ring is flat over the ring of global functions. -/
theorem flat_representedAffineStalkRingHom :
    (representedAffineGlobalStalkRingHom B S hS U x).Flat := by
  refine Stacks.ChangeOfRings.flat_of_preservesMonomorphisms_extendScalars _ ?_
  have h1 : PreservesFiniteLimits (representedAffineAssociated B S hS U) := inferInstance
  have h2 : PreservesFiniteLimits (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O) :=
    Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O
  have h3 : PreservesFiniteLimits (representedAffineStalk B S hS U x) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h1 h2
  have : (representedAffineStalk B S hS U x).PreservesMonomorphisms := inferInstance
  exact Functor.preservesMonomorphisms.of_iso (representedAffineStalkIso B S hS U x).symm

/-- A natural isomorphism of functors carries an equation of scalar endomorphisms. -/
private theorem map_eq_smul_of_iso {C : Type*} [Category* C] {T : Type u} [CommRing T]
    {F₁ F₂ : C ⥤ ModuleCat.{u} T} (e : F₁ ≅ F₂) {X : C} (f : X ⟶ X) (r : T)
    (h : F₂.map f = r • 𝟙 _) : F₁.map f = r • 𝟙 _ := by
  have hn := e.hom.naturality f
  rw [h, Linear.comp_smul, Category.comp_id] at hn
  rw [← Iso.cancel_iso_hom_right _ _ (e.app X), Iso.app_hom, hn, Linear.smul_comp,
    Category.id_comp]

/-- The stalk of the associated module turns multiplication by `a` on any `A`-module into
multiplication by its image in the stalk ring. -/
theorem representedAffineStalk_map_smul_id
    (M : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineStalk B S hS U x).map (a • 𝟙 M) =
      representedAffineGlobalStalkRingHom B S hS U x a • 𝟙 _ := by
  refine map_eq_smul_of_iso (representedAffineStalkIso B S hS U x).symm _ _ ?_
  exact Stacks.ExtendScalarsComparison.extendScalars_map_smul_id _ _ _

end Stalk

section Square

variable {P U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
  (g : P ⟶ U) (x : GeometricPoint B S hS (yoneda.obj P))

/-- `M ↦ (g^*(M^~))_{x̄'}`, from `A`-modules to modules over `𝒪_{yoneda.obj P, x̄'}`. -/
abbrev representedAffinePullbackStalk :
    ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⥤
      ModuleCat.{u} (geometricStalkRing B S hS
        (X := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩) x) :=
  representedAffineAssociated B S hS U ⋙
    Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom ⋙
    Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj P) x (isAlgebraicSpace_yoneda B S hS P))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩).O

/-- Through Stacks 05V5, `(g^*(M^~))_{x̄'}` is `𝒪_{x̄'} ⊗ (M^~)_{g(x̄')}`. -/
def representedAffinePullbackStalkIso :
    representedAffinePullbackStalk B S hS g x ≅
      representedAffineStalk B S hS U (geometricPointMap (representedSpaceMap B S hS g).hom x) ⋙
        ModuleCat.extendScalars.{u, u, u}
          (smallEtaleStalkPullbackRingMap B S hS (representedSpaceMap B S hS g) x) :=
  Functor.isoWhiskerLeft (representedAffineAssociated B S hS U)
    (pullbackStalkFunctorIso (representedSpaceMap B S hS g) x)

/-- Through the affine base change of the associated module, `(g^*(M^~))_{x̄'}` is
`((A' ⊗_A M)^~)_{x̄'}`. -/
def representedAffinePullbackStalkIso' :
    representedAffinePullbackStalk B S hS g x ≅
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom ⋙
        representedAffineStalk B S hS P x :=
  Functor.isoWhiskerRight (representedAffineAssociatedPullbackIso B S hS g)
      (Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS (yoneda.obj P) x (isAlgebraicSpace_yoneda B S hS P))
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩).O)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj P)] in
/-- Multiplication by `a ∈ A` on `A`, after taking `(g^*(-^~))_{x̄'}`, is multiplication by the
image of `a` under `A ⟶ 𝒪_{g(x̄')} ⟶ 𝒪_{x̄'}`. -/
theorem representedAffinePullbackStalk_map_smul_id₁
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffinePullbackStalk B S hS g x).map
        (a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) =
      (stalkStructureMap B S hS (representedSpaceMap B S hS g) x).hom
          (representedAffineGlobalStalkRingHom B S hS U
            (geometricPointMap (representedSpaceMap B S hS g).hom x) a) • 𝟙 _ := by
  rw [stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap_derived]
  refine map_eq_smul_of_iso (representedAffinePullbackStalkIso B S hS g x) _ _ ?_
  rw [Functor.comp_map, representedAffineStalk_map_smul_id]
  exact Stacks.ExtendScalarsComparison.extendScalars_map_smul_id
    (smallEtaleStalkPullbackRingMap B S hS (representedSpaceMap B S hS g) x) _ _

/-- Multiplication by `a ∈ A` on `A`, after taking `(g^*(-^~))_{x̄'}`, is multiplication by the
image of `a` under `A ⟶ A' ⟶ 𝒪_{x̄'}`. -/
theorem representedAffinePullbackStalk_map_smul_id₂
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffinePullbackStalk B S hS g x).map
        (a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) =
      representedAffineGlobalStalkRingHom B S hS P x
          ((representedAffineCommRingCatHom B S hS g).hom a) • 𝟙 _ := by
  refine map_eq_smul_of_iso (representedAffinePullbackStalkIso' B S hS g x) _ _ ?_
  rw [Functor.comp_map, Stacks.ExtendScalarsComparison.extendScalars_map_smul_id,
    representedAffineStalk_map_smul_id]
  rfl

/-- The stalk ring maps of affine representables form a commutative square with the ring map
of global functions: for `g : P ⟶ U` of affine objects and a geometric point `x̄'` of
`yoneda.obj P`, the stalk map of `g` at `x̄'` restricted along `A ⟶ 𝒪_{g(x̄')}` is
`A ⟶ A' ⟶ 𝒪_{x̄'}`. -/
theorem stalkStructureMap_representedAffineStalkRingHom
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (stalkStructureMap B S hS (representedSpaceMap B S hS g) x).hom
        (representedAffineGlobalStalkRingHom B S hS U
          (geometricPointMap (representedSpaceMap B S hS g).hom x) a) =
      representedAffineGlobalStalkRingHom B S hS P x
        ((representedAffineCommRingCatHom B S hS g).hom a) := by
  have h := (representedAffinePullbackStalk_map_smul_id₁ B S hS g x a).symm.trans
    (representedAffinePullbackStalk_map_smul_id₂ B S hS g x a)
  have χ : (representedAffinePullbackStalk B S hS g x).obj
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≅
      (representedAffineStalk B S hS P x).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj P, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj P, ⊤)) :=
    (representedAffinePullbackStalkIso' B S hS g x).app _ ≪≫
      (representedAffineStalk B S hS P x).mapIso
        (ModuleCat.ExtendScalars.objSelfIso (representedAffineCommRingCatHom B S hS g).hom)
  exact representedAffineStalkScalar_unique B S hS P x
    (Stacks.ExtendScalarsComparison.smul_id_transport χ h)

end Square

end AlgebraicGeometry.Space

end
