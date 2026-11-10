module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PresheafFiberOverMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.HigherDirectImageSliceActionComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.HigherDirectImageClassMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupStalk

/-!
# The class map `𝓗om(μ_N, G) ⟶ R^q g_*(g⁻¹ G)` on stalks, read on `G`

Let `g : X ⟶ U` be a morphism of schemes, `s` a global section of `R^q g_*(g⁻¹ μ_N)` and
`c_G : 𝓗om(μ_N, G) ⟶ R^q g_*(g⁻¹ G)`, `α ↦ α_* s`, the class map
(`Stacks.EtaleCohomology.higherDirectImageClassMap`), for sheaves `G` of `ℤ/N`-modules on
`U_étale`. Fix a point `Φ` of `U_étale` and a neighbourhood `V` of it carrying a primitive
`N`-th root of unity `ζ`. On every refinement `W` of `V` evaluation at `ζ` identifies the
sections of `𝓗om(μ_N, G)` over `W` with those of `G`
(`Stacks.Kummer.bijective_twistNegOneModuleEvalRoot`), so the class map becomes a map
`G(W) ⟶ R^q g_*(g⁻¹ G)(W)`, compatible with restriction, and on stalks a map
`Stacks.EtaleCohomology.Purity.classMapGermMap : G_Φ ⟶ (R^q g_*(g⁻¹ G))_Φ`
(through `Stacks.EtaleCohomology.Purity.presheafFiberOverMap`). The stalk of `c_G` is this map
after the identification of the stalk of the twist with `G_Φ`
(`Stacks.EtaleCohomology.Purity.presheafFiber_map_classMap_eq`), so it is bijective exactly when
`Stacks.EtaleCohomology.Purity.classMapGermMap` is
(`Stacks.EtaleCohomology.Purity.bijective_presheafFiber_map_classMap_iff`).

This reading makes the class map natural in `G`
(`Stacks.EtaleCohomology.Purity.classMapGermMap_naturality`) and local in `G`: a local isomorphism
`G|_{V'} ≅ G'|_{V'}` around the point carries one map of stalks to the other
(`Stacks.EtaleCohomology.Purity.bijective_classMapGermMap_iff_of_slice_iso`).

## Main definitions

* `Stacks.EtaleCohomology.Purity.rootEvalHom`, `Stacks.EtaleCohomology.Purity.rootEvalEquiv`.
* `Stacks.EtaleCohomology.Purity.classMapGermMap`.

## Main results

* `Stacks.EtaleCohomology.Purity.bijective_presheafFiber_map_classMap_iff`.
* `Stacks.EtaleCohomology.Purity.classMapGermMap_naturality`.
* `Stacks.EtaleCohomology.Purity.bijective_classMapGermMap_iff_of_slice_iso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
  GrothendieckTopology

universe u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

attribute [local instance] AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_addCommGrpCat

variable {X U : Scheme.{u}} (g : X ⟶ U) (q : ℕ) (N : ℕ) [NeZero N]
  (s : ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
    ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N)
      (rootsOfUnityModule.{u, 0} U N)))).obj.obj (op ((opensToEtale U).obj ⊤))))
  (Φ : Point.{u} U.smallEtaleTopology) {V : U.Etale} (v : Φ.fiber.obj V) {K : Type u} [Field K]
  (κ : K →+* Γ(V.left, ⊤)) {ζ : K} (hζ : IsPrimitiveRoot ζ N)

/-- The class map of `s` with coefficients `G`. -/
abbrev classMap (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))) :
    smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G) ⟶
      ((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G)) :=
  higherDirectImageClassMap g q (isTerminal_opensToEtale_top U) s

/-- The primitive root `ζ` as a section of `μ_N` over `V`. -/
abbrev rootSectionOver : ToType ((rootsOfUnityModule.{u, 0} U N).obj.obj (op V)) :=
  sliceRootSection.{u, 0} V κ hζ (Over.mk (𝟙 V)) 1

variable (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N)))

/-- The class map on sections over `W`, with the twist read as an abelian sheaf. -/
theorem classMap_hom_app_apply {W : U.Etale}
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    (classMap g q N s G).hom.app (op W) α =
      higherDirectImageInverseImageSectionMap g q W (moduleSheafHomForgetSliceHom W α)
        ((((smallEtalePushforwardAb g).rightDerived q).obj ((smallEtalePullbackAb g).obj
          (smallEtaleModuleSheafForgetAb (ZMod N) (rootsOfUnityModule.{u, 0} U N)))).obj.map
            ((isTerminal_opensToEtale_top U).from W).op s) := rfl

/-- **Evaluation at `ζ`** of a section of `𝓗om(μ_N, G)` over a refinement `W` of `V`. -/
def rootEvalHom {W : U.Etale} (a : W ⟶ V) :
    ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W)) →+ ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W)) :=
  ((twistNegOneModulePairing.{u, 0} U N G W).flip
    ((rootsOfUnityModule.{u, 0} U N).obj.map a.op (rootSectionOver N κ hζ))).toAddMonoidHom

/-- Evaluation at `ζ` is the pairing with the restriction of `ζ` to `W`. -/
theorem rootEvalHom_apply {W : U.Etale} (a : W ⟶ V)
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    rootEvalHom N κ hζ G a α = twistNegOneModulePairing.{u, 0} U N G W α
      ((rootsOfUnityModule.{u, 0} U N).obj.map a.op (rootSectionOver N κ hζ)) := rfl

/-- Evaluation at `ζ` commutes with restriction. -/
theorem rootEvalHom_naturality {W W' : U.Etale} (a : W ⟶ V) (b : W' ⟶ W)
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    rootEvalHom N κ hζ G (b ≫ a)
        ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.map b.op α) =
      (smallEtaleModuleSheafForgetAb (ZMod N) G).obj.map b.op (rootEvalHom N κ hζ G a α) := by
  change twistNegOneModulePairing.{u, 0} U N G W' ((twistNegOneModule.{u, 0} U N G).obj.map b.op α)
      ((rootsOfUnityModule.{u, 0} U N).obj.map (b ≫ a).op (rootSectionOver N κ hζ)) =
    G.obj.map b.op (twistNegOneModulePairing.{u, 0} U N G W α
      ((rootsOfUnityModule.{u, 0} U N).obj.map a.op (rootSectionOver N κ hζ)))
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  exact twistNegOneModulePairing_naturality.{u, 0} U N G b α _

/-- Evaluation at `ζ` is bijective on every refinement of `V`. -/
theorem bijective_rootEvalHom {W : U.Etale} (a : W ⟶ V) :
    Function.Bijective (rootEvalHom N κ hζ G a) := by
  change Function.Bijective (fun α => twistNegOneModulePairing.{u, 0} U N G W α
    ((rootsOfUnitySheaf.{u, 0} U N).obj.map a.op (rootSectionOver N κ hζ)))
  rw [rootsOfUnitySheaf_map_sliceRootSection N a κ hζ 1]
  exact bijective_twistNegOneModuleEvalRoot.{u, 0} W _ hζ G

/-- Evaluation at `ζ`, as an additive equivalence. -/
def rootEvalEquiv {W : U.Etale} (a : W ⟶ V) :
    ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W)) ≃+ ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W)) :=
  AddEquiv.ofBijective (rootEvalHom N κ hζ G a) (bijective_rootEvalHom N κ hζ G a)

/-- The additive equivalence `rootEvalEquiv` is evaluation at `ζ`. -/
theorem rootEvalEquiv_apply {W : U.Etale} (a : W ⟶ V)
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    rootEvalEquiv N κ hζ G a α = rootEvalHom N κ hζ G a α := rfl

/-- Transport of a compatibility of `f` and `h` with evaluation at `ζ` to the inverses. -/
private theorem rootEvalEquiv_symm_eq_of_rootEvalHom
    {G₁ G₂ : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))} {W W' : U.Etale}
    (a : W ⟶ V) (a' : W' ⟶ V)
    (f : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G₁)).obj.obj
      (op W)) → ToType ((smallEtaleModuleSheafForgetAb (ZMod N)
        (twistNegOneModule.{u, 0} U N G₂)).obj.obj (op W')))
    (h : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G₁).obj.obj (op W)) →
      ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G₂).obj.obj (op W')))
    (hf : ∀ α, rootEvalEquiv N κ hζ G₂ a' (f α) = h (rootEvalEquiv N κ hζ G₁ a α))
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G₁).obj.obj (op W))) :
    (rootEvalEquiv N κ hζ G₂ a').symm (h z) = f ((rootEvalEquiv N κ hζ G₁ a).symm z) := by
  rw [AddEquiv.symm_apply_eq, hf, AddEquiv.apply_symm_apply]

/-- The inverse of evaluation at `ζ` commutes with restriction. -/
theorem rootEvalEquiv_symm_naturality {W W' : U.Etale} (a : W ⟶ V) (b : W' ⟶ W)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    (rootEvalEquiv N κ hζ G (b ≫ a)).symm
        ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.map b.op z) =
      (smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.map b.op
        ((rootEvalEquiv N κ hζ G a).symm z) := by
  exact rootEvalEquiv_symm_eq_of_rootEvalHom N κ hζ a (b ≫ a) _ _
    (rootEvalHom_naturality N κ hζ G a b) z

/-- The class map, read through evaluation at `ζ` on a refinement `W` of `V`. -/
def classMapLocalHom {W : U.Etale} (a : W ⟶ V) :
    ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W)) →+
      ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj.obj
          (op W)) :=
  ((classMap g q N s G).hom.app (op W)).hom.comp
    (rootEvalEquiv N κ hζ G a).symm.toAddMonoidHom

/-- `classMapLocalHom` sends `z` to the class map applied to the local morphism `μ_N ⟶ G`
taking `ζ` to `z`. -/
theorem classMapLocalHom_apply {W : U.Etale} (a : W ⟶ V)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    classMapLocalHom g q N s κ hζ G a z =
      (classMap g q N s G).hom.app (op W) ((rootEvalEquiv N κ hζ G a).symm z) := rfl

/-- The class map read through evaluation at `ζ` commutes with restriction. -/
theorem classMapLocalHom_naturality {W W' : U.Etale} (a : W ⟶ V) (b : W' ⟶ W)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    classMapLocalHom g q N s κ hζ G (b ≫ a)
        ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.map b.op z) =
      (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj.map b.op
          (classMapLocalHom g q N s κ hζ G a z) := by
  rw [classMapLocalHom_apply, classMapLocalHom_apply, rootEvalEquiv_symm_naturality]
  exact NatTrans.naturality_apply (classMap g q N s G).hom b.op _

/-- **The class map on stalks, read on `G`**: the map `G_Φ ⟶ (R^q g_*(g⁻¹ G))_Φ` sending the germ
of `z` to the germ of `α_* s`, for `α` the local morphism `μ_N ⟶ G` with `α(ζ) = z`. -/
def classMapGermMap :
    ToType (Φ.presheafFiber.obj (smallEtaleModuleSheafForgetAb (ZMod N) G).obj) →+
      ToType (Φ.presheafFiber.obj (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj) :=
  presheafFiberOverMap Φ v (P := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj)
    (Q := (((smallEtalePushforwardAb g).rightDerived q).obj
      ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj)
    (fun a => classMapLocalHom g q N s κ hζ G a)
    (fun a b z => classMapLocalHom_naturality g q N s κ hζ G a b z)

/-- `classMapGermMap` sends the germ of `z` at `w` to the germ of `classMapLocalHom z`. -/
theorem classMapGermMap_germ {W : U.Etale} (w : Φ.fiber.obj W) (a : W ⟶ V)
    (ha : Φ.fiber.map a w = v)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    classMapGermMap g q N s Φ v κ hζ G
        (Φ.toPresheafFiber W w (smallEtaleModuleSheafForgetAb (ZMod N) G).obj z) =
      Φ.toPresheafFiber W w (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj
          (classMapLocalHom g q N s κ hζ G a z) :=
  presheafFiberOverMap_germ Φ v (P := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj)
    (Q := (((smallEtalePushforwardAb g).rightDerived q).obj
      ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj) _ _ w a ha z

/-- Evaluation at `ζ` on stalks: the stalk of the twist is the stalk of `G`. -/
def rootEvalGermMap :
    ToType (Φ.presheafFiber.obj
        (smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj) →+
      ToType (Φ.presheafFiber.obj (smallEtaleModuleSheafForgetAb (ZMod N) G).obj) :=
  presheafFiberOverMap Φ v
    (P := (smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj)
    (Q := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj) (fun a => rootEvalHom N κ hζ G a)
    (fun a b z => rootEvalHom_naturality N κ hζ G a b z)

/-- `rootEvalGermMap` sends the germ of `α` at `w` to the germ of its evaluation at `ζ`. -/
theorem rootEvalGermMap_germ {W : U.Etale} (w : Φ.fiber.obj W) (a : W ⟶ V)
    (ha : Φ.fiber.map a w = v)
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    rootEvalGermMap N Φ v κ hζ G (Φ.toPresheafFiber W w
        (smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj α) =
      Φ.toPresheafFiber W w (smallEtaleModuleSheafForgetAb (ZMod N) G).obj
        (rootEvalHom N κ hζ G a α) :=
  presheafFiberOverMap_germ Φ v
    (P := (smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj)
    (Q := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj) _ _ w a ha α

/-- Evaluation at `ζ` on stalks is bijective. -/
theorem bijective_rootEvalGermMap : Function.Bijective (rootEvalGermMap N Φ v κ hζ G) :=
  bijective_presheafFiberOverMap Φ v
    (P := (smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj)
    (Q := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj) _ _
    (fun a => bijective_rootEvalHom N κ hζ G a)

/-- **The stalk of the class map is `classMapGermMap` after evaluation at `ζ`.** -/
theorem presheafFiber_map_classMap_eq
    (p : ToType (Φ.presheafFiber.obj
      (smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj)) :
    Φ.presheafFiber.map (classMap g q N s G).hom p =
      classMapGermMap g q N s Φ v κ hζ G (rootEvalGermMap N Φ v κ hζ G p) := by
  obtain ⟨W, w, a, α, ha, rfl⟩ := exists_germ_over Φ v
    (P := (smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj) p
  rw [Point.toPresheafFiber_naturality_apply, rootEvalGermMap_germ N Φ v κ hζ G w a ha,
    classMapGermMap_germ g q N s Φ v κ hζ G w a ha, classMapLocalHom_apply]
  change _ = Φ.toPresheafFiber W w (((smallEtalePushforwardAb g).rightDerived q).obj
      ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj
    ((classMap g q N s G).hom.app (op W)
    ((rootEvalEquiv N κ hζ G a).symm (rootEvalEquiv N κ hζ G a α)))
  rw [AddEquiv.symm_apply_apply]

/-- **The stalk of the class map is bijective exactly when `classMapGermMap` is.** -/
theorem bijective_presheafFiber_map_classMap_iff :
    Function.Bijective (Φ.presheafFiber.map (classMap g q N s G).hom) ↔
      Function.Bijective (classMapGermMap g q N s Φ v κ hζ G) := by
  have e : (Φ.presheafFiber.map (classMap g q N s G).hom : _ → _) =
      classMapGermMap g q N s Φ v κ hζ G ∘ rootEvalGermMap N Φ v κ hζ G :=
    funext (presheafFiber_map_classMap_eq g q N s Φ v κ hζ G)
  rw [e]
  exact Function.Bijective.of_comp_iff _ (bijective_rootEvalGermMap N Φ v κ hζ G)

/-! ### Naturality in the coefficients -/

section Naturality

variable {G} {G' : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))} (t : G ⟶ G')

/-- Evaluation at `ζ` commutes with postcomposition. -/
theorem rootEvalHom_twistNegOneModuleMap {W : U.Etale} (a : W ⟶ V)
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    rootEvalHom N κ hζ G' a (((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map
          (twistNegOneModuleMap.{u, 0} U N t)).hom.app (op W) α) =
      ((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map t).hom.app (op W)
          (rootEvalHom N κ hζ G a α) := by
  change ((U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).map (𝟙 _) ≫ α ≫
      (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).map t).hom.app
        (op (Over.mk (𝟙 W))) _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The inverse of evaluation at `ζ` commutes with postcomposition. -/
theorem rootEvalEquiv_symm_twistNegOneModuleMap {W : U.Etale} (a : W ⟶ V)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    (rootEvalEquiv N κ hζ G' a).symm (((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map t).hom.app (op W) z) =
      ((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map
          (twistNegOneModuleMap.{u, 0} U N t)).hom.app (op W)
        ((rootEvalEquiv N κ hζ G a).symm z) := by
  exact rootEvalEquiv_symm_eq_of_rootEvalHom N κ hζ a a _ _
    (rootEvalHom_twistNegOneModuleMap N κ hζ t a) z

/-- The class map read through evaluation at `ζ` is natural in the coefficients. -/
theorem classMapLocalHom_map {W : U.Etale} (a : W ⟶ V)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    classMapLocalHom g q N s κ hζ G' a (((sheafCompose U.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map t).hom.app (op W) z) =
      (((smallEtalePushforwardAb g).rightDerived q).map
        ((smallEtalePullbackAb g).map ((sheafCompose U.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map t))).hom.app (op W)
        (classMapLocalHom g q N s κ hζ G a z) := by
  rw [classMapLocalHom_apply, classMapLocalHom_apply, rootEvalEquiv_symm_twistNegOneModuleMap]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun φ => φ.hom)
    (moduleSheafHomMap_comp_higherDirectImageClassMap g q (isTerminal_opensToEtale_top U) s t))
      (op W)) ((rootEvalEquiv N κ hζ G a).symm z)

/-- **`classMapGermMap` is natural in the coefficients.** -/
theorem classMapGermMap_naturality
    (p : ToType (Φ.presheafFiber.obj (smallEtaleModuleSheafForgetAb (ZMod N) G).obj)) :
    classMapGermMap g q N s Φ v κ hζ G'
        (Φ.presheafFiber.map ((sheafCompose U.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map t).hom p) =
      Φ.presheafFiber.map (((smallEtalePushforwardAb g).rightDerived q).map
        ((smallEtalePullbackAb g).map ((sheafCompose U.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map t))).hom
        (classMapGermMap g q N s Φ v κ hζ G p) := by
  obtain ⟨W, w, a, z, ha, rfl⟩ := exists_germ_over Φ v
    (P := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj) p
  rw [Point.toPresheafFiber_naturality_apply, classMapGermMap_germ g q N s Φ v κ hζ G w a ha,
    Point.toPresheafFiber_naturality_apply, classMapGermMap_germ g q N s Φ v κ hζ G' w a ha,
    classMapLocalHom_map]

end Naturality

/-! ### Locality in the coefficients -/

omit [NeZero N] in
/-- Forgetting the linear structure of local morphisms respects composition. -/
theorem moduleSheafHomForgetSliceHom_comp {F₁ F₂ F₃ : Sheaf U.smallEtaleTopology
    (ModuleCat.{u + 1} (ZMod N))} (W : U.Etale)
    (α : (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj F₁ ⟶
      (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj F₂)
    (β : (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj F₂ ⟶
      (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj F₃) :
    moduleSheafHomForgetSliceHom W (α ≫ β) =
      moduleSheafHomForgetSliceHom W α ≫ moduleSheafHomForgetSliceHom W β :=
  (sheafCompose (U.smallEtaleTopology.over W)
    (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map_comp α β

omit [NeZero N] in
/-- Forgetting the linear structure of local morphisms respects identities. -/
theorem moduleSheafHomForgetSliceHom_id (F₁ : Sheaf U.smallEtaleTopology
    (ModuleCat.{u + 1} (ZMod N))) (W : U.Etale) :
    moduleSheafHomForgetSliceHom W
        (𝟙 ((U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj F₁)) = 𝟙 _ :=
  (sheafCompose (U.smallEtaleTopology.over W)
    (forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1})).map_id _

omit [NeZero N] in
/-- The action of a local isomorphism on sections is invertible. -/
theorem higherDirectImageInverseImageSectionMap_forget_hom_inv
    {F₁ F₂ : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))} {W : U.Etale}
    (e : (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj F₁ ≅
      (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj F₂) :
    higherDirectImageInverseImageSectionMap g q W (moduleSheafHomForgetSliceHom W e.hom) ≫
      higherDirectImageInverseImageSectionMap g q W (moduleSheafHomForgetSliceHom W e.inv) =
        𝟙 _ := by
  rw [← higherDirectImageInverseImageSectionMap_comp, ← moduleSheafHomForgetSliceHom_comp,
    e.hom_inv_id, moduleSheafHomForgetSliceHom_id, higherDirectImageInverseImageSectionMap_id]

section Locality

variable {G} {G' : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ZMod N))} {V₁ : U.Etale}
  (v₁ : Φ.fiber.obj V₁)
  (ρ : (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) V₁).obj G ≅
    (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) V₁).obj G')

/-- The restriction of the local isomorphism `ρ` to a refinement `W` of `V₁`. -/
abbrev sliceIsoRestrict {W : U.Etale} (b : W ⟶ V₁) :
    (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj G ≅
      (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj G' :=
  (U.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} (ZMod N)) b).mapIso ρ

/-- The local isomorphism `ρ`, as a section of the internal hom over `V₁`. -/
def sliceIsoSection :
    ToType ((Stacks.ConstantSheaf.moduleSheafHom U.smallEtaleTopology (ZMod N) G G').obj.obj
      (op V₁)) :=
  ρ.hom

/-- The component over a refinement `W` of `V₁` of the local isomorphism `ρ`. -/
def sliceIsoComponent {W : U.Etale} (b : W ⟶ V₁) :
    ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W)) →+
      ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G').obj.obj (op W)) :=
  ((sliceIsoRestrict N ρ b).hom.hom.app (op (Over.mk (𝟙 W)))).hom.toAddMonoidHom

omit [NeZero N] in
/-- `sliceIsoComponent` is the component of the restriction of `ρ` to `W` at `W` itself. -/
theorem sliceIsoComponent_apply {W : U.Etale} (b : W ⟶ V₁)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    sliceIsoComponent N ρ b z = (sliceIsoRestrict N ρ b).hom.hom.app (op (Over.mk (𝟙 W))) z := rfl

omit [NeZero N] in
/-- The components of `ρ` commute with restriction. -/
theorem sliceIsoComponent_naturality {W W' : U.Etale} (b : W ⟶ V₁) (c : W' ⟶ W)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    sliceIsoComponent N ρ (c ≫ b) ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.map c.op z) =
      (smallEtaleModuleSheafForgetAb (ZMod N) G').obj.map c.op (sliceIsoComponent N ρ b z) :=
  ConcreteCategory.congr_hom
    (ρ.hom.hom.naturality (Over.homMk c : Over.mk (c ≫ b) ⟶ Over.mk b).op) z

omit [NeZero N] in
/-- The components of `ρ` are bijective. -/
theorem bijective_sliceIsoComponent {W : U.Etale} (b : W ⟶ V₁) :
    Function.Bijective (sliceIsoComponent N ρ b) := by
  have : IsIso (sliceIsoRestrict N ρ b).hom.hom :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map (sliceIsoRestrict N ρ b).hom))
  exact (ConcreteCategory.isIso_iff_bijective
    ((sliceIsoRestrict N ρ b).hom.hom.app (op (Over.mk (𝟙 W))))).1 inferInstance

/-- The local isomorphism `ρ` on stalks. -/
def sliceIsoGermMap :
    ToType (Φ.presheafFiber.obj (smallEtaleModuleSheafForgetAb (ZMod N) G).obj) →+
      ToType (Φ.presheafFiber.obj (smallEtaleModuleSheafForgetAb (ZMod N) G').obj) :=
  presheafFiberOverMap Φ v₁ (P := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj)
    (Q := (smallEtaleModuleSheafForgetAb (ZMod N) G').obj) (fun b => sliceIsoComponent N ρ b)
    (fun b c z => sliceIsoComponent_naturality N ρ b c z)

/-- The action of `ρ` on the sections of `R^q g_*(g⁻¹ G)` over a refinement `W` of `V₁`. -/
def sliceIsoTargetComponent {W : U.Etale} (b : W ⟶ V₁) :
    ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj.obj
          (op W)) →+
      ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G'))).obj.obj
          (op W)) :=
  (higherDirectImageInverseImageSectionMap g q W
    (moduleSheafHomForgetSliceHom W (sliceIsoRestrict N ρ b).hom)).hom

omit [NeZero N] in
/-- The action of `ρ` on the sections of `R^q g_*(g⁻¹ -)` commutes with restriction. -/
theorem sliceIsoTargetComponent_naturality {W W' : U.Etale} (b : W ⟶ V₁) (c : W' ⟶ W)
    (x : ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj.obj
          (op W))) :
    sliceIsoTargetComponent g q N ρ (c ≫ b)
        ((((smallEtalePushforwardAb g).rightDerived q).obj
          ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj.map
            c.op x) =
      (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G'))).obj.map c.op
          (sliceIsoTargetComponent g q N ρ b x) := by
  have hr := ConcreteCategory.congr_hom (higherDirectImageInverseImageSectionMap_restrict g q c
    (moduleSheafHomForgetSliceHom W (sliceIsoRestrict N ρ b).hom)) x
  simp only [ConcreteCategory.comp_apply] at hr
  have e : (sliceIsoRestrict N ρ (c ≫ b)).hom =
      (U.smallEtaleTopology.overMapPullback (ModuleCat.{u + 1} (ZMod N)) c).map
        (sliceIsoRestrict N ρ b).hom :=
    (ConcreteCategory.congr_hom
      ((Stacks.ConstantSheaf.moduleSheafHom U.smallEtaleTopology (ZMod N) G G').obj.map_comp
        b.op c.op) (sliceIsoSection N ρ)).trans (ConcreteCategory.comp_apply _ _ _)
  rw [sliceIsoTargetComponent, sliceIsoTargetComponent, e]
  exact hr

omit [NeZero N] in
/-- The action of `ρ` on the sections of `R^q g_*(g⁻¹ -)` is bijective. -/
theorem bijective_sliceIsoTargetComponent {W : U.Etale} (b : W ⟶ V₁) :
    Function.Bijective (sliceIsoTargetComponent g q N ρ b) :=
  (ConcreteCategory.isIso_iff_bijective (higherDirectImageInverseImageSectionMap g q W
      (moduleSheafHomForgetSliceHom W (sliceIsoRestrict N ρ b).hom))).1
    ⟨_, higherDirectImageInverseImageSectionMap_forget_hom_inv g q N (sliceIsoRestrict N ρ b),
      higherDirectImageInverseImageSectionMap_forget_hom_inv g q N (sliceIsoRestrict N ρ b).symm⟩

/-- The action of the local isomorphism `ρ` on the stalks of `R^q g_*(g⁻¹ -)`. -/
def sliceIsoTargetGermMap :
    ToType (Φ.presheafFiber.obj (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj) →+
      ToType (Φ.presheafFiber.obj (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G'))).obj) :=
  presheafFiberOverMap Φ v₁ (P := (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj)
    (Q := (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G'))).obj)
    (fun b => sliceIsoTargetComponent g q N ρ b)
    (fun b c x => sliceIsoTargetComponent_naturality g q N ρ b c x)

omit [NeZero N] in
/-- `sliceIsoGermMap` sends the germ of `z` at `w` to the germ of its image under `ρ`. -/
theorem sliceIsoGermMap_germ {W : U.Etale} (w : Φ.fiber.obj W) (b : W ⟶ V₁)
    (hb : Φ.fiber.map b w = v₁)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    sliceIsoGermMap N Φ v₁ ρ
        (Φ.toPresheafFiber W w (smallEtaleModuleSheafForgetAb (ZMod N) G).obj z) =
      Φ.toPresheafFiber W w (smallEtaleModuleSheafForgetAb (ZMod N) G').obj
        (sliceIsoComponent N ρ b z) :=
  presheafFiberOverMap_germ Φ v₁ (P := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj)
    (Q := (smallEtaleModuleSheafForgetAb (ZMod N) G').obj) _ _ w b hb z

omit [NeZero N] in
/-- `sliceIsoTargetGermMap` sends the germ of `x` at `w` to the germ of its image under `ρ`. -/
theorem sliceIsoTargetGermMap_germ {W : U.Etale} (w : Φ.fiber.obj W) (b : W ⟶ V₁)
    (hb : Φ.fiber.map b w = v₁)
    (x : ToType ((((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj.obj
          (op W))) :
    sliceIsoTargetGermMap g q N Φ v₁ ρ
        (Φ.toPresheafFiber W w (((smallEtalePushforwardAb g).rightDerived q).obj
          ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj x) =
      Φ.toPresheafFiber W w (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G'))).obj
        (sliceIsoTargetComponent g q N ρ b x) :=
  presheafFiberOverMap_germ Φ v₁ (P := (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj)
    (Q := (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G'))).obj)
    _ _ w b hb x

/-- Postcomposition of a local morphism `μ_N ⟶ G` over a refinement of `V₁` with `ρ`. -/
def twistSlicePostcomp {W : U.Etale} (b : W ⟶ V₁)
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G')).obj.obj
      (op W)) :=
  (show (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj
      (rootsOfUnityModule.{u, 0} U N) ⟶
    (U.smallEtaleTopology.overPullback (ModuleCat.{u + 1} (ZMod N)) W).obj G from α) ≫
    (sliceIsoRestrict N ρ b).hom

/-- Evaluation at `ζ` of a local morphism followed by the local isomorphism `ρ`. -/
theorem rootEvalHom_twistSlicePostcomp {W : U.Etale} (a : W ⟶ V) (b : W ⟶ V₁)
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    rootEvalHom N κ hζ G' a (twistSlicePostcomp N ρ b α) =
      sliceIsoComponent N ρ b (rootEvalHom N κ hζ G a α) := rfl

/-- Forgetting the linear structure of a local morphism postcomposed with `ρ`. -/
theorem moduleSheafHomForgetSliceHom_twistSlicePostcomp {W : U.Etale} (b : W ⟶ V₁)
    (α : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) (twistNegOneModule.{u, 0} U N G)).obj.obj
      (op W))) :
    moduleSheafHomForgetSliceHom W (twistSlicePostcomp N ρ b α) =
      moduleSheafHomForgetSliceHom W α ≫
        moduleSheafHomForgetSliceHom W (sliceIsoRestrict N ρ b).hom :=
  moduleSheafHomForgetSliceHom_comp N W _ _

/-- **The class map commutes with a local isomorphism of the coefficients**, on the sections over
a common refinement of `V` and `V₁`. -/
theorem classMapLocalHom_sliceIsoComponent {W : U.Etale} (a : W ⟶ V) (b : W ⟶ V₁)
    (z : ToType ((smallEtaleModuleSheafForgetAb (ZMod N) G).obj.obj (op W))) :
    classMapLocalHom g q N s κ hζ G' a (sliceIsoComponent N ρ b z) =
      sliceIsoTargetComponent g q N ρ b (classMapLocalHom g q N s κ hζ G a z) := by
  rw [classMapLocalHom_apply, classMapLocalHom_apply]
  have key : (rootEvalEquiv N κ hζ G' a).symm (sliceIsoComponent N ρ b z) =
      twistSlicePostcomp N ρ b ((rootEvalEquiv N κ hζ G a).symm z) := by
    exact rootEvalEquiv_symm_eq_of_rootEvalHom N κ hζ a a _ _
      (rootEvalHom_twistSlicePostcomp N κ hζ ρ a b) z
  rw [key, classMap_hom_app_apply, classMap_hom_app_apply,
    moduleSheafHomForgetSliceHom_twistSlicePostcomp, higherDirectImageInverseImageSectionMap_comp,
    ConcreteCategory.comp_apply]
  rfl

/-- **A local isomorphism of the coefficients carries one class map on stalks to the other.** -/
theorem classMapGermMap_sliceIsoGermMap
    (p : ToType (Φ.presheafFiber.obj (smallEtaleModuleSheafForgetAb (ZMod N) G).obj)) :
    classMapGermMap g q N s Φ v κ hζ G' (sliceIsoGermMap N Φ v₁ ρ p) =
      sliceIsoTargetGermMap g q N Φ v₁ ρ (classMapGermMap g q N s Φ v κ hζ G p) := by
  obtain ⟨V₂, v₂, a₂, b₂, ha₂, hb₂⟩ := exists_fiber_cone_of_point Φ v v₁
  obtain ⟨W, w, c, z, hc, rfl⟩ := exists_germ_over Φ v₂
    (P := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj) p
  have ha : Φ.fiber.map (c ≫ a₂) w = v := by
    rw [Functor.map_comp_apply, hc, ha₂]
  have hb : Φ.fiber.map (c ≫ b₂) w = v₁ := by
    rw [Functor.map_comp_apply, hc, hb₂]
  rw [sliceIsoGermMap_germ N Φ v₁ ρ w (c ≫ b₂) hb,
    classMapGermMap_germ g q N s Φ v κ hζ G' w (c ≫ a₂) ha,
    classMapGermMap_germ g q N s Φ v κ hζ G w (c ≫ a₂) ha,
    sliceIsoTargetGermMap_germ g q N Φ v₁ ρ w (c ≫ b₂) hb, classMapLocalHom_sliceIsoComponent]

omit [NeZero N] in
/-- The local isomorphism `ρ` is bijective on stalks. -/
theorem bijective_sliceIsoGermMap : Function.Bijective (sliceIsoGermMap N Φ v₁ ρ) :=
  bijective_presheafFiberOverMap Φ v₁ (P := (smallEtaleModuleSheafForgetAb (ZMod N) G).obj)
    (Q := (smallEtaleModuleSheafForgetAb (ZMod N) G').obj) _ _
    (fun b => bijective_sliceIsoComponent N ρ b)

omit [NeZero N] in
/-- The action of `ρ` on the stalks of `R^q g_*(g⁻¹ -)` is bijective. -/
theorem bijective_sliceIsoTargetGermMap : Function.Bijective (sliceIsoTargetGermMap g q N Φ v₁ ρ) :=
  bijective_presheafFiberOverMap Φ v₁ (P := (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G))).obj)
    (Q := (((smallEtalePushforwardAb g).rightDerived q).obj
        ((smallEtalePullbackAb g).obj (smallEtaleModuleSheafForgetAb (ZMod N) G'))).obj) _ _
    (fun b => bijective_sliceIsoTargetComponent g q N ρ b)

include v₁ ρ in
/-- **The class map on stalks is local in the coefficients**: a local isomorphism `G ≅ G'` around
the point makes one bijective exactly when the other is. -/
theorem bijective_classMapGermMap_iff_of_slice_iso :
    Function.Bijective (classMapGermMap g q N s Φ v κ hζ G) ↔
      Function.Bijective (classMapGermMap g q N s Φ v κ hζ G') := by
  have e : (sliceIsoTargetGermMap g q N Φ v₁ ρ : _ → _) ∘ classMapGermMap g q N s Φ v κ hζ G =
      classMapGermMap g q N s Φ v κ hζ G' ∘ sliceIsoGermMap N Φ v₁ ρ :=
    funext fun p => (classMapGermMap_sliceIsoGermMap g q N s Φ v κ hζ v₁ ρ p).symm
  rw [← Function.Bijective.of_comp_iff' (bijective_sliceIsoTargetGermMap g q N Φ v₁ ρ), e]
  exact Function.Bijective.of_comp_iff _ (bijective_sliceIsoGermMap N Φ v₁ ρ)

end Locality

end Stacks.EtaleCohomology.Purity

end
