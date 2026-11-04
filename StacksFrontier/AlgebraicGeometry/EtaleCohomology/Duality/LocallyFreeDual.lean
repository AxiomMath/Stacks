module

public import StacksFrontier.CategoryTheory.Sites.Point.ExactPairingOfFibers
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDescFiber
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.GeometricFibres
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass

/-!
# The dual of an étale-locally free sheaf of modules

Let `Λ` be a commutative ring, `Y` a scheme and `N` a sheaf of `Λ`-modules on the small étale site
of `Y` which is étale-locally constant with value a finite free `Λ`-module. Its dual
`N^∨ = Hom(N, Λ)` is the internal hom `Stacks.ConstantSheaf.moduleSheafHom` into the unit, whose
sections over `U` are the morphisms `N|_U ⟶ Λ|_U` on the slice site, and the evaluation
`N^∨ ⊗ N ⟶ Λ`, `(α, n) ↦ α(n)`, is an exact pairing: `N` is dualizable in the monoidal category of
étale sheaves of `Λ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open Functor.LaxMonoidal

universe u

namespace Stacks.EtaleCohomology

variable {Λ : Type} [CommRing Λ] {Y : Scheme.{u}}

/-- On the small étale site of a scheme, the class of morphisms of presheaves of `Λ`-modules that
become isomorphisms after sheafification is monoidal. -/
local instance (S : Scheme.{u}) : (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

attribute [local instance] Sheaf.monoidalCategory

/-- **The dual `Hom(N, Λ)` of an étale sheaf of `Λ`-modules**: the internal hom into the unit,
whose sections over `U` are the morphisms `N|_U ⟶ Λ|_U` on the slice site. -/
abbrev etaleModuleDual (N : EtaleModules.{u, 0} Λ Y) : EtaleModules.{u, 0} Λ Y :=
  Stacks.ConstantSheaf.moduleSheafHom Y.smallEtaleTopology Λ N (𝟙_ (EtaleModules.{u, 0} Λ Y))

/-- The evaluation of a section of the dual on a section of `N`, over the same object. -/
def etaleModuleDualPairing (N : EtaleModules.{u, 0} Λ Y) (U : Y.Etaleᵒᵖ) :
    (etaleModuleDual N).obj.obj U →ₗ[Λ] N.obj.obj U →ₗ[Λ]
      (𝟙_ (EtaleModules.{u, 0} Λ Y)).obj.obj U where
  toFun α := (α.hom.app (op (Over.mk (𝟙 U.unop)))).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pairing evaluates `α` at the identity of `U` on the slice site and applies it to `n`. -/
theorem etaleModuleDualPairing_apply (N : EtaleModules.{u, 0} Λ Y) (U : Y.Etaleᵒᵖ)
    (α : (etaleModuleDual N).obj.obj U) (n : N.obj.obj U) :
    etaleModuleDualPairing N U α n = (α.hom.app (op (Over.mk (𝟙 U.unop)))).hom n :=
  rfl

/-- A section `φ` of the dual over `V` commutes with restriction along a morphism of the slice. -/
private theorem unit_map_dual_app_apply (N : EtaleModules.{u, 0} Λ Y) {V : Y.Etale}
    (φ : (etaleModuleDual N).obj.obj (op V)) {A B : Over V} (h : B ⟶ A)
    (x : N.obj.obj (op A.left)) :
    ((𝟙_ (EtaleModules.{u, 0} Λ Y)).obj.map h.left.op).hom ((φ.hom.app (op A)).hom x) =
      (φ.hom.app (op B)).hom ((N.obj.map h.left.op).hom x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality h.op) x |>.symm

/-- The pairing commutes with restriction along `f : U ⟶ V`. -/
theorem etaleModuleDualPairing_map (N : EtaleModules.{u, 0} Λ Y) {U V : Y.Etaleᵒᵖ} (f : U ⟶ V)
    (α : (etaleModuleDual N).obj.obj U) (n : N.obj.obj U) :
    (𝟙_ (EtaleModules.{u, 0} Λ Y)).obj.map f (etaleModuleDualPairing N U α n) =
      etaleModuleDualPairing N V ((etaleModuleDual N).obj.map f α) (N.obj.map f n) := by
  have key : ((etaleModuleDual N).obj.map f α).hom.app (op (Over.mk (𝟙 V.unop))) =
      α.hom.app (op (Over.mk f.unop)) := by
    rw [Stacks.ConstantSheaf.moduleSheafHom_obj_map_apply]
    exact CategoryTheory.presheafHom_map_app (𝟙 V.unop) f.unop f.unop
      (Category.id_comp _) α.hom
  rw [etaleModuleDualPairing_apply, etaleModuleDualPairing_apply, key]
  exact unit_map_dual_app_apply N α (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop)) n

/-- **The evaluation `N^∨ ⊗ N ⟶ Λ`**, `(α, n) ↦ α(n)`. -/
def etaleModuleDualEvaluation (N : EtaleModules.{u, 0} Λ Y) :
    etaleModuleDual N ⊗ N ⟶ 𝟙_ (EtaleModules.{u, 0} Λ Y) :=
  Sheaf.tensorDesc.{u + 1, u, u + 1, 0} (etaleModuleDualPairing N)
    (fun f a b => etaleModuleDualPairing_map N f a b)

/-! ### The evaluation on fibres -/

attribute [local instance] moduleCat_hasLimitsOfSize etaleModules_AB5OfSize
  etaleModules_preservesFilteredColimits_forget
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

open Stacks.SheafDuality

/-- **The fibre pairing of the evaluation on germs** is the germ of the evaluation. -/
theorem fiberPairing_etaleModuleDualEvaluation_germ (N : EtaleModules.{u, 0} Λ Y)
    (Φ : Y.smallEtaleTopology.Point.{u + 1}) {U : Y.Etale} (x : Φ.fiber.obj U)
    (α : (etaleModuleDual N).obj.obj (op U)) (n : N.obj.obj (op U)) :
    fiberPairing (etaleModuleDualEvaluation N) Φ (germ Φ x (etaleModuleDual N) α)
        (germ Φ x N n) =
      unitEquiv (moduleFiber Λ Φ)
        (germ Φ x (𝟙_ (EtaleModules.{u, 0} Λ Y)) (etaleModuleDualPairing N (op U) α n)) :=
  congrArg (unitEquiv (moduleFiber Λ Φ))
    (Sheaf.sheafFiber_tensorDesc_tmul Φ (etaleModuleDualPairing N)
      (fun f a b => etaleModuleDualPairing_map N f a b) U x α n)

/-- The germ of the unit section attached to `r`. -/
theorem germ_unit (Φ : Y.smallEtaleTopology.Point.{u + 1}) {U : Y.Etale} (x : Φ.fiber.obj U)
    (r : 𝟙_ (ModuleCat.{u + 1} Λ)) :
    germ Φ x (𝟙_ (EtaleModules.{u, 0} Λ Y))
        (((toSheafify Y.smallEtaleTopology (𝟙_ (Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ))).app (op U) ≫
          (Functor.OplaxMonoidal.η (presheafToSheaf Y.smallEtaleTopology
            (ModuleCat.{u + 1} Λ))).hom.app (op U)).hom r) =
      (ε (moduleFiber Λ Φ)).hom r := by
  let L := presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let e := Φ.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} Λ)
  have hε : ε (moduleFiber Λ Φ) = ε (Φ.presheafFiber (A := ModuleCat.{u + 1} Λ)) ≫
      e.inv.app _ ≫ (moduleFiber Λ Φ).map (Functor.OplaxMonoidal.η L) :=
    Localization.Monoidal.functorMonoidalOfComp_ε L Y.smallEtaleTopology.W (moduleFiber Λ Φ)
      Φ.presheafFiber
  have h : ε (moduleFiber Λ Φ) =
      ((toSheafify Y.smallEtaleTopology (𝟙_ (Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ))).app (op U) ≫
        (Functor.OplaxMonoidal.η L).hom.app (op U)) ≫
        Φ.toPresheafFiber U x (𝟙_ (EtaleModules.{u, 0} Λ Y)).obj := by
    rw [hε, Φ.toPresheafFiber_ε U x]
    show Φ.toPresheafFiber U x _ ≫ Φ.presheafFiber.map (toSheafify Y.smallEtaleTopology _) ≫
      Φ.presheafFiber.map (Functor.OplaxMonoidal.η L).hom = _
    rw [← Φ.presheafFiber.map_comp, Φ.toPresheafFiber_naturality, Category.assoc]
    rfl
  exact (ConcreteCategory.congr_hom h r).symm

/-! ### Surjectivity of the fibre pairing -/

/-- Sheafification on the slices of the small étale site, at the coefficient universe `u + 1`. -/
local instance hasWeakSheafify_smallEtale_over (V : Y.Etale) :
    HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ) :=
  haveI := Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1}
    (Y.smallEtaleTopology.over V) Λ
  inferInstance

/-- On the slices of the small étale site, a morphism of presheaves of `Λ`-modules becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
local instance wEqualsLocallyBijective_smallEtaleOver_moduleCat (V : Y.Etale) :
    (Y.smallEtaleTopology.over V).WEqualsLocallyBijective (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, 0} _ Λ

/-- The restriction to the slice at `V` of the unit sheaf receives the constant sheaf on the unit
module. -/
def unitOverComparison (V : Y.Etale) :
    (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj
        (𝟙_ (ModuleCat.{u + 1} Λ)) ⟶
      (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).obj
        (𝟙_ (EtaleModules.{u, 0} Λ Y)) :=
  ((Stacks.ConstantSheaf.overPullbackConstantSheafIso Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) V).hom.app (𝟙_ (ModuleCat.{u + 1} Λ))) ≫
    (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).map
      (Functor.OplaxMonoidal.η (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))

/-- A linear form on the constant value of a trivialization of `N` over `V`, as a section of the
dual over `V`. -/
def dualSectionOfConst (N : EtaleModules.{u, 0} Λ Y) {V : Y.Etale} {E : ModuleCat.{u + 1} Λ}
    (e : (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
      (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).obj N)
    (l : E →ₗ[Λ] Λ) : (etaleModuleDual N).obj.obj (op V) :=
  e.inv ≫ (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).map
    (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ l)) ≫ unitOverComparison V

/-- The section `dualSectionOfConst N e l` pairs with the constant section `constSection e m` to
the section of the unit sheaf over `V` attached to `l m`. -/
theorem etaleModuleDualPairing_dualSectionOfConst (N : EtaleModules.{u, 0} Λ Y) {V : Y.Etale}
    {E : ModuleCat.{u + 1} Λ}
    (e : (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
      (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).obj N)
    (l : E →ₗ[Λ] Λ) (m : E) :
    etaleModuleDualPairing N (op V) (dualSectionOfConst N e l) (constSection e m) =
      ((toSheafify Y.smallEtaleTopology (𝟙_ (Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ))).app (op V) ≫
          (Functor.OplaxMonoidal.η (presheafToSheaf Y.smallEtaleTopology
            (ModuleCat.{u + 1} Λ))).hom.app (op V)).hom (ULift.up (l m)) := by
  let K := Y.smallEtaleTopology.over V
  let A := ModuleCat.{u + 1} Λ
  let t := ((toSheafify K ((Functor.const _).obj E)).app (op (Over.mk (𝟙 V)))).hom m
  have he : (e.inv.hom.app (op (Over.mk (𝟙 V)))).hom ((e.hom.hom.app (op (Over.mk (𝟙 V)))).hom t) =
      t := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op (Over.mk (𝟙 V))))
        e.hom_inv_id) t
  have hc := ConcreteCategory.congr_hom (Stacks.ConstantSheaf.toSheafify_const_naturality_app K A
    (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ l)) (op (Over.mk (𝟙 V)))) m
  have hk := ConcreteCategory.congr_hom
    (Stacks.ConstantSheaf.toSheafify_overPullbackConstantSheafIso Y.smallEtaleTopology A V
      (𝟙_ A)) (ULift.up (l m))
  show ((unitOverComparison V).hom.app (op (Over.mk (𝟙 V)))).hom
      ((((constantSheaf K A).map
        (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ l))).hom.app
          (op (Over.mk (𝟙 V)))).hom
        ((e.inv.hom.app (op (Over.mk (𝟙 V)))).hom ((e.hom.hom.app (op (Over.mk (𝟙 V)))).hom t))) = _
  refine (congrArg (fun z => ((unitOverComparison V).hom.app (op (Over.mk (𝟙 V)))).hom
    ((((constantSheaf K A).map (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ l))).hom.app
      (op (Over.mk (𝟙 V)))).hom z)) he).trans ?_
  refine (congrArg ((unitOverComparison V).hom.app (op (Over.mk (𝟙 V)))).hom hc.symm).trans ?_
  exact congrArg ((Functor.OplaxMonoidal.η (presheafToSheaf Y.smallEtaleTopology A)).hom.app
    (op V)).hom hk

/-- **The fibre pairing of the evaluation is onto** `Hom(N_Φ, Λ)` at a point lifting to an object
over which `N` is constant. -/
theorem surjective_fiberPairing_etaleModuleDualEvaluation (N : EtaleModules.{u, 0} Λ Y)
    (Φ : Y.smallEtaleTopology.Point.{u + 1}) {V : Y.Etale} (y : Φ.fiber.obj V)
    {E : ModuleCat.{u + 1} Λ}
    (e : (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
      (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).obj N) :
    Function.Surjective (fiberPairing (etaleModuleDualEvaluation N) Φ) := by
  intro ψ
  refine ⟨germ Φ y (etaleModuleDual N)
    (dualSectionOfConst N e (ψ ∘ₗ (germ Φ y N ∘ₗ constSection e))), ?_⟩
  refine LinearMap.ext fun g => ?_
  obtain ⟨m, rfl⟩ := exists_germ_constSection_eq e Φ y g
  show fiberPairing (etaleModuleDualEvaluation N) Φ (germ Φ y (etaleModuleDual N) _)
    (germ Φ y N (constSection e m)) = _
  rw [fiberPairing_etaleModuleDualEvaluation_germ, etaleModuleDualPairing_dualSectionOfConst,
    germ_unit, unitEquiv_ε]
  rfl

/-! ### Injectivity of the fibre pairing -/

/-- A section of the dual over `V` vanishing, after restriction along `k`, on the constant
sections of a generating family of a trivialization of `N` over `V`, vanishes, after restriction
along `k`, on every constant section. -/
private theorem etaleModuleDualPairing_constSection_map_eq_zero (N : EtaleModules.{u, 0} Λ Y)
    {V : Y.Etale} {E : ModuleCat.{u + 1} Λ}
    (e : (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
      (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).obj N)
    {n : ℕ} (gen : Fin n → E) (hgen : Submodule.span Λ (Set.range gen) = ⊤)
    {W : Y.Etale} (k : W ⟶ V) (φ : (etaleModuleDual N).obj.obj (op V))
    (h0 : ∀ j, ((𝟙_ (EtaleModules.{u, 0} Λ Y)).obj.map k.op).hom
      (etaleModuleDualPairing N (op V) φ (constSection e (gen j))) = 0) (m : E) :
    ((𝟙_ (EtaleModules.{u, 0} Λ Y)).obj.map k.op).hom
      (etaleModuleDualPairing N (op V) φ (constSection e m)) = 0 := by
  have hm : m ∈ Submodule.span Λ (Set.range gen) := hgen ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h0 j
  | zero => simp
  | add x y _ _ hx hy => simp only [_root_.map_add, hx, hy, add_zero]
  | smul c x _ hx => simp only [_root_.map_smul, hx, smul_zero]

/-- A section of the dual over `V` vanishing on the constant sections of a finite generating family
of a trivialization of `N` over `V`, after restriction along `k : W ⟶ V`, vanishes after
restriction along `k`. -/
theorem etaleModuleDual_map_eq_zero (N : EtaleModules.{u, 0} Λ Y) {V : Y.Etale}
    {E : ModuleCat.{u + 1} Λ}
    (e : (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
      (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).obj N)
    {n : ℕ} (gen : Fin n → E) (hgen : Submodule.span Λ (Set.range gen) = ⊤)
    {W : Y.Etale} (k : W ⟶ V) (φ : (etaleModuleDual N).obj.obj (op V))
    (h0 : ∀ j, ((𝟙_ (EtaleModules.{u, 0} Λ Y)).obj.map k.op).hom
      (etaleModuleDualPairing N (op V) φ (constSection e (gen j))) = 0) :
    (etaleModuleDual N).obj.map k.op φ = 0 := by
  have hall := etaleModuleDualPairing_constSection_map_eq_zero N e gen hgen k φ h0
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun T => ModuleCat.hom_ext (LinearMap.ext fun c => ?_))
  obtain ⟨⟨T, _, g⟩⟩ := T
  show (φ.hom.app (op (Over.mk (g ≫ k)))).hom c = 0
  refine (eq_of_germ_eq (isConservativeFamilyOfPoints_residueGeometricPoints.{u, 0} Y)
    (H := 𝟙_ (EtaleModules.{u, 0} Λ Y)) fun Ψ z => ?_).trans rfl
  let I := 𝟙_ (EtaleModules.{u, 0} Λ Y)
  obtain ⟨m, hm⟩ := exists_germ_constSection_eq e Ψ.obj (Ψ.obj.fiber.map (g ≫ k) z)
    (germ Ψ.obj z N c)
  have h1 : germ Ψ.obj z N ((N.obj.map (g ≫ k).op).hom (constSection e m)) =
      germ Ψ.obj z N c := (germ_map Ψ.obj (g ≫ k) z N _).trans hm
  obtain ⟨T₂, h, z₂, hz₂, hh⟩ := (Ψ.obj.toPresheafFiber_eq_iff' T z _ _).1 h1
  have n1 := unit_map_dual_app_apply N φ
    (Over.homMk h rfl : Over.mk (h ≫ g ≫ k) ⟶ Over.mk (g ≫ k)) c
  have n2 := unit_map_dual_app_apply N φ
    (Over.homMk (h ≫ g ≫ k) (Category.comp_id _) : Over.mk (h ≫ g ≫ k) ⟶ Over.mk (𝟙 V))
    (constSection e m)
  have hmap : (N.obj.map (h ≫ g ≫ k).op).hom (constSection e m) =
      (N.obj.map h.op).hom ((N.obj.map (g ≫ k).op).hom (constSection e m)) := by
    rw [op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hI : (I.obj.map (h ≫ g ≫ k).op).hom
      (etaleModuleDualPairing N (op V) φ (constSection e m)) = 0 := by
    rw [show (h ≫ g ≫ k).op = k.op ≫ (h ≫ g).op by simp, Functor.map_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, hall m, map_zero]
  subst hz₂
  calc germ Ψ.obj _ I ((φ.hom.app (op (Over.mk (g ≫ k)))).hom c)
      = germ Ψ.obj z₂ I ((I.obj.map h.op).hom ((φ.hom.app (op (Over.mk (g ≫ k)))).hom c)) :=
        (germ_map Ψ.obj h z₂ I _).symm
    _ = germ Ψ.obj z₂ I ((φ.hom.app (op (Over.mk (h ≫ g ≫ k)))).hom ((N.obj.map h.op).hom c)) :=
        congrArg _ n1
    _ = germ Ψ.obj z₂ I ((φ.hom.app (op (Over.mk (h ≫ g ≫ k)))).hom
          ((N.obj.map (h ≫ g ≫ k).op).hom (constSection e m))) := by
        rw [hmap]
        exact congrArg _ (congrArg _ hh.symm)
    _ = germ Ψ.obj z₂ I ((I.obj.map (h ≫ g ≫ k).op).hom
          (etaleModuleDualPairing N (op V) φ (constSection e m))) :=
        congrArg _ n2.symm
    _ = germ Ψ.obj _ I 0 := by rw [hI, map_zero, map_zero]

/-- **The fibre pairing of the evaluation is injective** for `N` locally constant of finite
type. -/
theorem injective_fiberPairing_etaleModuleDualEvaluation (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.smallEtaleTopology N)
    (Φ : Y.smallEtaleTopology.Point.{u + 1}) :
    Function.Injective (fiberPairing (etaleModuleDualEvaluation N) Φ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  let I₁ := 𝟙_ (EtaleModules.{u, 0} Λ Y)
  obtain ⟨U, x, φ, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := (etaleModuleDual N).obj) a
  obtain ⟨I, V, f, hcov, htriv⟩ := hN U
  obtain ⟨Y₀, g, ⟨Z, p, q, ⟨i⟩, rfl⟩, y₀, hy₀⟩ := Φ.jointly_surjective _ hcov x
  obtain ⟨E, hE, ⟨e⟩⟩ := htriv i
  have : Module.Finite Λ E := hE
  obtain ⟨n, gen, hgen⟩ := Module.Finite.exists_fin (R := Λ) (M := E)
  have hy : Φ.fiber.map (f i) (Φ.fiber.map p y₀) = x := by simpa using hy₀
  subst hy
  let φ' := ((etaleModuleDual N).obj.map (f i).op).hom φ
  have hφ' : germ Φ (Φ.fiber.map p y₀) (etaleModuleDual N) φ' =
      germ Φ (Φ.fiber.map (f i) (Φ.fiber.map p y₀)) (etaleModuleDual N) φ :=
    germ_map Φ (f i) _ _ φ
  let σ : Fin n → I₁.obj.obj (op (V i)) :=
    fun j => etaleModuleDualPairing N (op (V i)) φ' (constSection e (gen j))
  have hσ : ∀ j, (Φ.toPresheafFiber (V i) (Φ.fiber.map p y₀)
      I₁.obj).hom (σ j) = 0 := by
    intro j
    have h := LinearMap.congr_fun ha (germ Φ (Φ.fiber.map p y₀) N (constSection e (gen j)))
    change fiberPairing (etaleModuleDualEvaluation N) Φ
      (germ Φ (Φ.fiber.map (f i) (Φ.fiber.map p y₀)) (etaleModuleDual N) φ)
      (germ Φ (Φ.fiber.map p y₀) N (constSection e (gen j))) = 0 at h
    rw [← hφ', fiberPairing_etaleModuleDualEvaluation_germ] at h
    exact (unitEquiv (moduleFiber Λ Φ)).map_eq_zero_iff.1 h
  obtain ⟨W₂, k, w₂, hw₂, h0⟩ := exists_map_eq_zero_of_germ_eq_zero Φ _ σ hσ
  refine hφ'.symm.trans ?_
  calc germ Φ (Φ.fiber.map p y₀) (etaleModuleDual N) φ'
      = germ Φ (Φ.fiber.map k w₂) (etaleModuleDual N) φ' :=
        congrArg (fun t => germ Φ t (etaleModuleDual N) φ') hw₂.symm
    _ = germ Φ w₂ (etaleModuleDual N) (((etaleModuleDual N).obj.map k.op).hom φ') :=
        (germ_map Φ k w₂ _ φ').symm
    _ = 0 := by rw [etaleModuleDual_map_eq_zero N e gen hgen k φ' h0, map_zero]

/-! ### The exact pairing -/

/-- Every point of the small étale site lifts to an object over which an étale-locally free sheaf
of finite rank is constant with value a finite free module. -/
theorem exists_trivialization_of_isLocallyConstantWith (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N)
    (Φ : Y.smallEtaleTopology.Point.{u + 1}) :
    ∃ (V : Y.Etale) (_ : Φ.fiber.obj V) (E : ModuleCat.{u + 1} Λ),
      (Module.Free Λ E ∧ Module.Finite Λ E) ∧
      Nonempty ((constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
        (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) V).obj N) := by
  obtain ⟨⟨X, x⟩⟩ : Nonempty Φ.fiber.Elements := IsCofiltered.nonempty
  obtain ⟨I, V, f, hcov, htriv⟩ := hN X
  obtain ⟨Y₀, g, ⟨Z, p, q, ⟨i⟩, rfl⟩, y₀, -⟩ := Φ.jointly_surjective _ hcov x
  obtain ⟨E, hE, he⟩ := htriv i
  exact ⟨V i, Φ.fiber.map p y₀, E, hE, he⟩

/-- An étale-locally free sheaf of finite rank is locally constant of finite type. -/
theorem isFiniteTypeLocallyConstant_of_isLocallyConstantWith (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Y.smallEtaleTopology N := fun U => by
  obtain ⟨I, V, f, hcov, htriv⟩ := hN U
  exact ⟨I, V, f, hcov, fun i => by
    obtain ⟨E, hE, he⟩ := htriv i
    exact ⟨E, hE.2, he⟩⟩

/-- **The fibre pairing of the evaluation is perfect** for an étale-locally free sheaf of finite
rank, and its fibres are finite free. -/
theorem bijective_fiberPairing_etaleModuleDualEvaluation (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N)
    (Φ : Y.smallEtaleTopology.Point.{u + 1}) :
    Function.Bijective (fiberPairing (etaleModuleDualEvaluation N) Φ) ∧
      Module.Free Λ ((moduleFiber Λ Φ).obj N) ∧ Module.Finite Λ ((moduleFiber Λ Φ).obj N) := by
  obtain ⟨V, y, E, ⟨hfree, hfin⟩, ⟨e⟩⟩ := exists_trivialization_of_isLocallyConstantWith N hN Φ
  let l := (Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver Φ y N E e).toLinearEquiv
  exact ⟨⟨injective_fiberPairing_etaleModuleDualEvaluation N
      (isFiniteTypeLocallyConstant_of_isLocallyConstantWith N hN) Φ,
    surjective_fiberPairing_etaleModuleDualEvaluation N Φ y e⟩,
    Module.Free.of_equiv l.symm, Module.Finite.equiv l.symm⟩

/-- **An étale-locally free sheaf of finite rank is dualizable**: the evaluation
`N^∨ ⊗ N ⟶ Λ` is the evaluation of an exact pairing between `N` and its dual `Hom(N, Λ)`. The
coevaluation `Λ ⟶ N ⊗ N^∨` is glued from the canonical elements of the fibres
(`Stacks.SheafDuality.exactPairing`), the fibre pairings being perfect. -/
@[instance_reducible]
def etaleModuleDualExactPairing (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    ExactPairing N (etaleModuleDual N) :=
  Stacks.SheafDuality.exactPairing (isConservativeFamilyOfPoints_residueGeometricPoints.{u, 0} Y)
    (etaleModuleDualEvaluation N) (isFiniteTypeLocallyConstant_of_isLocallyConstantWith N hN)
    fun Φ => by
      obtain ⟨hb, hfree, hfin⟩ := bijective_fiberPairing_etaleModuleDualEvaluation N hN Φ.obj
      exact existsUnique_isCanonical (etaleModuleDualEvaluation N) Φ.obj hb

/-- The evaluation of `etaleModuleDualExactPairing` is `(α, n) ↦ α(n)`. -/
theorem etaleModuleDualExactPairing_evaluation (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    letI := etaleModuleDualExactPairing N hN
    ε_ N (etaleModuleDual N) = etaleModuleDualEvaluation N :=
  rfl

end Stacks.EtaleCohomology
