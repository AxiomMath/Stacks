module

public import StacksFrontier.CategoryTheory.Abelian.ExtUnitAction
public import StacksFrontier.CategoryTheory.Sites.Point.FreeSheafFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicLevelPoincarePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FreeModuleSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.DiagonalEdgeMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback

/-!
# The edge map of a global class, acting on all sheaves

Let `p : Y ⟶ B` be a morphism of schemes, `N ≥ 1`, `Λ = ℤ/N`, and `c ∈ Ext²(Λ_Y, Λ_Y)` a global
class on `Y`. For a sheaf `G` of `Λ`-modules on `B_étale` write

`T(G) = H⁰(Rp_*(p⁻¹G[2])) = R²p_*(p⁻¹G)`

for the underlying abelian sheaf, computed in the derived category of abelian sheaves. This file
builds a morphism `ν_G : G ⟶ T(G)`, natural in `G`
(`Stacks.EtaleCohomology.TopTrace.trace`):

* for `A` whose inverse image has flat fibres, `c` acts on `p⁻¹A` by tensoring
  (`Stacks.ExtUnitAction.action`), and the adjoint of `c · p⁻¹A : p⁻¹A[0] ⟶ p⁻¹A[2]` along
  `p⁻¹ ⊣ Rp_*` gives `Θ_A : A ⟶ T(A)` (`Stacks.EtaleCohomology.TopTrace.edge`), natural in `A`
  (`Stacks.EtaleCohomology.TopTrace.edge_naturality`) because the action is;
* free sheaves `Λ[P]` have free fibres, so every `G` is a quotient `Λ[G] ↠ G` of such an `A`
  whose kernel is again a quotient of one, and `Θ` descends to `ν_G`.

This is the global construction of the top-degree trace of a relative curve in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): for the diagonal class on `X̄ ×_S X̄` it is
the map `X ⟶ R²f_!(f⁻¹X)` inverse to the trace. No local choice is made, so no compatibility
between local choices has to be checked.

The derived categories are those of the standard model `HasDerivedCategory.standard`.

## Main definitions

* `Stacks.EtaleCohomology.TopTrace.FlatFibres`: all fibres at geometric points are flat.
* `Stacks.EtaleCohomology.TopTrace.topSheaf`: `G ↦ H⁰(Rp_*(p⁻¹G[2]))`.
* `Stacks.EtaleCohomology.TopTrace.edge`: `Θ_A` for `A` with `p⁻¹A` of flat fibres.
* `Stacks.EtaleCohomology.TopTrace.trace`: `ν : U ⟶ T`, the natural transformation.

## Main results

* `Stacks.EtaleCohomology.TopTrace.flatFibres_free`: free sheaves have flat fibres.
* `Stacks.EtaleCohomology.TopTrace.edge_naturality`.
* `Stacks.EtaleCohomology.TopTrace.trace_app_eq_edge`: `ν = Θ` on flat sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.TopTrace

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  isMonoidal_W_etaleModules isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {N : ℕ}

/-- A sheaf of `ℤ/N`-modules **has flat fibres** when its fibre at every geometric point with
separably closed residue field is a flat `ℤ/N`-module. -/
def FlatFibres {S : Scheme.{u}} (G : EtaleModules.{u, 0} (ZMod N) S) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S),
    Module.Flat (ZMod N)
      ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod N))).obj G)

/-- **Free sheaves have flat fibres**: the fibre of `Λ[P]` is the free module on the fibre of
`P` (`CategoryTheory.GrothendieckTopology.Point.freeSheafFiberIso`). -/
theorem flatFibres_free {S : Scheme.{u}} (P : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    FlatFibres ((etaleModuleFree (ZMod N) S).obj P) := by
  intro Ω _ _ s
  have : Module.Flat (ZMod N) ((ModuleCat.freeSplit.{u + 1, 0} (ZMod N)).obj
      ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber (A := Type (u + 1))).obj P)) :=
    Module.Flat.of_free
  have h2 : Module.Flat (ZMod N) ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
      (A := Type (u + 1)) ⋙ ModuleCat.freeSplit.{u + 1, 0} (ZMod N)).obj P) := this
  exact Module.Flat.of_linearEquiv
    (((((Scheme.pointSmallEtale s).ulift.{u + 1}).freeSheafFiberIso (ZMod N)).app P)).toLinearEquiv

/-- Flat fibres pass to inverse images. -/
theorem FlatFibres.inverseImage {S T : Scheme.{u}} (g : T ⟶ S)
    {G : EtaleModules.{u, 0} (ZMod N) S} (hG : FlatFibres G) :
    FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj G) :=
  fun Ω _ _ s => flat_sheafFiber_inverseImage g G hG Ω s

/-- Tensoring with a sheaf with flat fibres is exact. -/
theorem FlatFibres.exact {S : Scheme.{u}} {G : EtaleModules.{u, 0} (ZMod N) S}
    (hG : FlatFibres G) :
    (MonoidalCategory.tensorRight G).Additive ∧
      PreservesFiniteLimits (MonoidalCategory.tensorRight G) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight G) :=
  tensorRight_exact_of_flat G hG

variable {B Y : Scheme.{u}} (p : Y ⟶ B)

/-- **`T(G) = H⁰(Rp_*(p⁻¹G[2]))`**, the underlying abelian sheaf of `R²p_*(p⁻¹G)`, computed in the
unbounded derived category of abelian sheaves. -/
def topSheaf :
    EtaleModules.{u, 0} (ZMod N) B ⥤ Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  etaleModuleInverseImage.{u, 0} (ZMod N) p ⋙ etaleModuleUnderlyingAbelian Y (ZMod N) ⋙
    DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ ((2 : ℕ) : ℤ) ⋙
    etaleAbelianDerivedDirectImage.{u, 0} p ⋙ DerivedCategory.homologyFunctor _ 0

/-- `T = H⁰(Rp_*(p⁻¹(-)[2]))` preserves zero morphisms, `Rp_*` being a right adjoint. -/
instance topSheaf_preservesZeroMorphisms : (topSheaf p (N := N)).PreservesZeroMorphisms := by
  have : (etaleAbelianDerivedDirectImage.{u, 0} p).PreservesZeroMorphisms :=
    haveI := (etaleAbelianDerivedAdjunction.{u, 0} p).isRightAdjoint
    Functor.preservesZeroMorphisms_of_isRightAdjoint _
  unfold topSheaf
  infer_instance

/-- `p⁻¹(U A)[0] ≅ U(p⁻¹A)[0]` in the derived category of abelian sheaves on `Y`, as a natural
isomorphism. -/
def inverseImageSingleNatIso :
    etaleModuleUnderlyingAbelian B (ZMod N) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        etaleAbelianDerivedInverseImage.{u, 0} p ≅
      etaleModuleInverseImage.{u, 0} (ZMod N) p ⋙ etaleModuleUnderlyingAbelian Y (ZMod N) ⋙
        DerivedCategory.singleFunctor _ 0 :=
  Functor.isoWhiskerLeft _
      ((etaleAbelianInverseImage.{u, 0} p).mapDerivedCategorySingleFunctor 0) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleUnderlyingAbelianInverseImageIso (ZMod N) p) _ ≪≫
    Functor.associator _ _ _

/-- `p⁻¹(U A)[0] ≅ U(p⁻¹A)[0]` in the derived category of abelian sheaves on `Y`. -/
def inverseImageSingleIso (A : EtaleModules.{u, 0} (ZMod N) B) :
    (etaleAbelianDerivedInverseImage.{u, 0} p).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((etaleModuleUnderlyingAbelian B (ZMod N)).obj A)) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A)) :=
  (inverseImageSingleNatIso p).app A

/-- Naturality in `A` of `Stacks.EtaleCohomology.TopTrace.inverseImageSingleIso`. -/
theorem inverseImageSingleIso_hom_naturality {A A' : EtaleModules.{u, 0} (ZMod N) B}
    (φ : A ⟶ A') :
    (etaleAbelianDerivedInverseImage.{u, 0} p).map ((DerivedCategory.singleFunctor _ 0).map
        ((etaleModuleUnderlyingAbelian B (ZMod N)).map φ)) ≫ (inverseImageSingleIso p A').hom =
      (inverseImageSingleIso p A).hom ≫ (DerivedCategory.singleFunctor _ 0).map
        ((etaleModuleUnderlyingAbelian Y (ZMod N)).map
          ((etaleModuleInverseImage.{u, 0} (ZMod N) p).map φ)) :=
  (inverseImageSingleNatIso p).hom.naturality φ

variable (c : Ext.{u + 1} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) (𝟙_ _) 2)

/-- **The action of `c` on a sheaf with flat fibres**, read as a morphism `U F[0] ⟶ U F[2]` of the
derived category of abelian sheaves. -/
def classHom (F : EtaleModules.{u, 0} (ZMod N) Y) (hF : FlatFibres F) :
    (DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj F) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj F))⟦((2 : ℕ) : ℤ)⟧ :=
  letI := etaleModules_enoughInjectives.{u, 0} (ZMod N) Y
  haveI := hF.exact.1
  haveI := hF.exact.2.1
  haveI := hF.exact.2.2
  ((Stacks.ExtUnitAction.action c F).mapExactFunctor (etaleModuleUnderlyingAbelian Y (ZMod N))).hom

/-- **The action of `c` is natural** on sheaves with flat fibres, because
`Stacks.ExtUnitAction.action` is (`Stacks.ExtUnitAction.mk₀_comp_action`). -/
theorem classHom_naturality {F F' : EtaleModules.{u, 0} (ZMod N) Y} (hF : FlatFibres F)
    (hF' : FlatFibres F') (φ : F ⟶ F') :
    (DerivedCategory.singleFunctor _ 0).map ((etaleModuleUnderlyingAbelian Y (ZMod N)).map φ) ≫
        classHom c F' hF' =
      classHom c F hF ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((etaleModuleUnderlyingAbelian Y (ZMod N)).map φ))⟦((2 : ℕ) : ℤ)⟧' := by
  let := etaleModules_enoughInjectives.{u, 0} (ZMod N) Y
  obtain ⟨_, _, _⟩ := hF.exact
  obtain ⟨_, _, _⟩ := hF'.exact
  have h := congrArg (fun e => e.mapExactFunctor (etaleModuleUnderlyingAbelian Y (ZMod N)))
    (Stacks.ExtUnitAction.mk₀_comp_action c φ)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀] at h
  have h' := congrArg Ext.hom h
  simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at h'
  exact h'

/-- **The edge map of `c` at `A`, in the derived category**: the adjoint along `p⁻¹ ⊣ Rp_*` of the
action `p⁻¹(U A)[0] ≅ U(p⁻¹A)[0] ⟶ U(p⁻¹A)[2]` of `c`. -/
def edgeHom (A : EtaleModules.{u, 0} (ZMod N) B)
    (hA : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A)) :
    (DerivedCategory.singleFunctor _ 0).obj ((etaleModuleUnderlyingAbelian B (ZMod N)).obj A) ⟶
      (etaleAbelianDerivedDirectImage.{u, 0} p).obj (((DerivedCategory.singleFunctor _ 0).obj
        ((etaleModuleUnderlyingAbelian Y (ZMod N)).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A)))⟦((2 : ℕ) : ℤ)⟧) :=
  (etaleAbelianDerivedAdjunction.{u, 0} p).homEquiv _ _
    ((inverseImageSingleIso p A).hom ≫ classHom c _ hA)

/-- Naturality of `Stacks.EtaleCohomology.TopTrace.edgeHom` on sheaves whose inverse images have
flat fibres. -/
theorem edgeHom_naturality {A A' : EtaleModules.{u, 0} (ZMod N) B}
    (hA : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A))
    (hA' : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A')) (φ : A ⟶ A') :
    (DerivedCategory.singleFunctor _ 0).map ((etaleModuleUnderlyingAbelian B (ZMod N)).map φ) ≫
        edgeHom p c A' hA' =
      edgeHom p c A hA ≫ (etaleAbelianDerivedDirectImage.{u, 0} p).map
        (((DerivedCategory.singleFunctor _ 0).map ((etaleModuleUnderlyingAbelian Y (ZMod N)).map
          ((etaleModuleInverseImage.{u, 0} (ZMod N) p).map φ)))⟦((2 : ℕ) : ℤ)⟧') := by
  rw [edgeHom, edgeHom, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_right]
  congr 1
  rw [← Category.assoc, inverseImageSingleIso_hom_naturality, Category.assoc,
    classHom_naturality c hA hA' ((etaleModuleInverseImage.{u, 0} (ZMod N) p).map φ),
    Category.assoc]

/-- `X ≅ H⁰(X[0])`, with the target spelled as `H⁰` of the single complex. -/
def singleHomologyZeroIso {S : Scheme.{u}} (X : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    X ≅ (DerivedCategory.homologyFunctor _ 0).obj ((DerivedCategory.singleFunctor _ 0).obj X) :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app X).symm

/-- Naturality in `X` of `Stacks.EtaleCohomology.TopTrace.singleHomologyZeroIso`. -/
theorem singleHomologyZeroIso_hom_naturality {S : Scheme.{u}}
    {X X' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : X ⟶ X') :
    φ ≫ (singleHomologyZeroIso X').hom =
      (singleHomologyZeroIso X).hom ≫
        (DerivedCategory.homologyFunctor _ 0).map ((DerivedCategory.singleFunctor _ 0).map φ) :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).inv.naturality φ

/-- **The edge map `Θ_A : A ⟶ T(A)` of `c`** for `A` whose inverse image has flat fibres: `H⁰` of
`Stacks.EtaleCohomology.TopTrace.edgeHom`. -/
def edge (A : EtaleModules.{u, 0} (ZMod N) B)
    (hA : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A)) :
    (etaleModuleUnderlyingAbelian B (ZMod N)).obj A ⟶ (topSheaf p).obj A :=
  (singleHomologyZeroIso _).hom ≫ (DerivedCategory.homologyFunctor _ 0).map (edgeHom p c A hA)

/-- **`Θ` is natural** on sheaves whose inverse images have flat fibres. -/
theorem edge_naturality {A A' : EtaleModules.{u, 0} (ZMod N) B}
    (hA : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A))
    (hA' : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A')) (φ : A ⟶ A') :
    edge p c A hA ≫ (topSheaf p).map φ =
      (etaleModuleUnderlyingAbelian B (ZMod N)).map φ ≫ edge p c A' hA' := by
  have h := congrArg (DerivedCategory.homologyFunctor _ 0).map (edgeHom_naturality p c hA hA' φ)
  simp only [Functor.map_comp] at h
  have h2 := singleHomologyZeroIso_hom_naturality ((etaleModuleUnderlyingAbelian B (ZMod N)).map φ)
  exact (Category.assoc _ _ _).trans ((congrArg (fun k => _ ≫ k) h.symm).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ _) h2.symm).trans
      (Category.assoc _ _ _))))

/-! ### Descent to all sheaves -/

/-- The free sheaf `Λ[G]` on the underlying sheaf of sets of `G`. -/
abbrev freeCover (G : EtaleModules.{u, 0} (ZMod N) B) : EtaleModules.{u, 0} (ZMod N) B :=
  (etaleModuleFree (ZMod N) B).obj
    ((sheafCompose B.smallEtaleTopology (forget (ModuleCat.{u + 1} (ZMod N)))).obj G)

/-- The counit `Λ[G] ↠ G`. -/
abbrev freeCoverπ (G : EtaleModules.{u, 0} (ZMod N) B) : freeCover G ⟶ G :=
  (etaleModuleFreeAdj (ZMod N) B).counit.app G

/-- `Λ[φ] : Λ[G] ⟶ Λ[G']`. -/
abbrev freeCoverMap {G G' : EtaleModules.{u, 0} (ZMod N) B} (φ : G ⟶ G') :
    freeCover G ⟶ freeCover G' :=
  (etaleModuleFree (ZMod N) B).map
    ((sheafCompose B.smallEtaleTopology (forget (ModuleCat.{u + 1} (ZMod N)))).map φ)

/-- Naturality of the counit `Λ[G] ↠ G`: `Λ[φ] ≫ π_{G'} = π_G ≫ φ`. -/
theorem freeCoverMap_comp_freeCoverπ {G G' : EtaleModules.{u, 0} (ZMod N) B} (φ : G ⟶ G') :
    freeCoverMap φ ≫ freeCoverπ G' = freeCoverπ G ≫ φ :=
  (etaleModuleFreeAdj (ZMod N) B).counit.naturality φ

/-- The counit `Λ[G] ↠ G` is an epimorphism. -/
theorem epi_freeCoverπ (G : EtaleModules.{u, 0} (ZMod N) B) : Epi (freeCoverπ G) :=
  (etaleModuleFreeAdj (ZMod N) B).counit_epi_of_R_faithful G

/-- The inverse image of the free cover `Λ[G]` has flat fibres. -/
theorem flatFibres_inverseImage_freeCover (G : EtaleModules.{u, 0} (ZMod N) B) :
    FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj (freeCover G)) :=
  (flatFibres_free _).inverseImage p

/-- The underlying map of abelian sheaves of the counit `Λ[G] ↠ G` is an epimorphism. -/
theorem epi_map_freeCoverπ (G : EtaleModules.{u, 0} (ZMod N) B) :
    Epi ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G)) := by
  have := epi_freeCoverπ G
  infer_instance

/-- The comparison `U Λ[K] ⟶ ker(U Λ[G] ⟶ U G)` for `K = ker(Λ[G] ⟶ G)` is an epimorphism. -/
theorem epi_kernelLift_map_freeCover (G : EtaleModules.{u, 0} (ZMod N) B) :
    Epi (kernel.lift ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G))
      ((etaleModuleUnderlyingAbelian B (ZMod N)).map
        (freeCoverπ (kernel (freeCoverπ G)) ≫ kernel.ι (freeCoverπ G)))
      (by rw [← Functor.map_comp, Category.assoc, kernel.condition, Limits.comp_zero,
        Functor.map_zero])) := by
  have := epi_freeCoverπ (kernel (freeCoverπ G))
  rw [show ∀ h, kernel.lift ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G))
      ((etaleModuleUnderlyingAbelian B (ZMod N)).map
        (freeCoverπ (kernel (freeCoverπ G)) ≫ kernel.ι (freeCoverπ G))) h =
      (etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ (kernel (freeCoverπ G))) ≫
        kernelComparison (freeCoverπ G) (etaleModuleUnderlyingAbelian B (ZMod N)) from fun h => by
    rw [← cancel_mono (kernel.ι _), kernel.lift_ι, Category.assoc, kernelComparison_comp_ι,
      Functor.map_comp]]
  infer_instance

/-- `Θ` on the free cover `Λ[G]`, followed by `T(Λ[G] ↠ G)`, vanishes on the kernel of
`U Λ[G] ⟶ U G`; this is what lets it descend to `U G`. -/
theorem kernel_ι_comp_edge_freeCover (G : EtaleModules.{u, 0} (ZMod N) B) :
    kernel.ι ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G)) ≫
        edge p c (freeCover G) (flatFibres_inverseImage_freeCover p G) ≫
          (topSheaf p).map (freeCoverπ G) = 0 := by
  have := epi_kernelLift_map_freeCover G
  rw [← cancel_epi (kernel.lift ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G))
      ((etaleModuleUnderlyingAbelian B (ZMod N)).map
        (freeCoverπ (kernel (freeCoverπ G)) ≫ kernel.ι (freeCoverπ G))) _),
    kernel.lift_ι_assoc, Limits.comp_zero, ← Category.assoc,
    ← edge_naturality p c (flatFibres_inverseImage_freeCover p _)
      (flatFibres_inverseImage_freeCover p G), Category.assoc, ← Functor.map_comp,
    Category.assoc, kernel.condition, Limits.comp_zero, Functor.map_zero, Limits.comp_zero]

/-- **The top-degree trace map `ν_G : U G ⟶ T(G)`** of the class `c`: `Θ` on the free cover
`Λ[G] ↠ G`, descended along it. -/
def traceApp (G : EtaleModules.{u, 0} (ZMod N) B) :
    (etaleModuleUnderlyingAbelian B (ZMod N)).obj G ⟶ (topSheaf p).obj G :=
  haveI := epi_map_freeCoverπ G
  Abelian.epiDesc ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G))
    (edge p c (freeCover G) (flatFibres_inverseImage_freeCover p G) ≫
      (topSheaf p).map (freeCoverπ G)) (kernel_ι_comp_edge_freeCover p c G)

/-- **`ν_G` restricts to `Θ` along the free cover**:
`U(Λ[G] ↠ G) ≫ ν_G = Θ_{Λ[G]} ≫ T(Λ[G] ↠ G)`. -/
theorem map_freeCoverπ_comp_traceApp (G : EtaleModules.{u, 0} (ZMod N) B) :
    (etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G) ≫ traceApp p c G =
      edge p c (freeCover G) (flatFibres_inverseImage_freeCover p G) ≫
        (topSheaf p).map (freeCoverπ G) := by
  have := epi_map_freeCoverπ G
  exact Abelian.comp_epiDesc _ _ _

/-- **`ν` is natural** in the sheaf. -/
theorem traceApp_naturality {G G' : EtaleModules.{u, 0} (ZMod N) B} (φ : G ⟶ G') :
    (etaleModuleUnderlyingAbelian B (ZMod N)).map φ ≫ traceApp p c G' =
      traceApp p c G ≫ (topSheaf p).map φ := by
  have := epi_map_freeCoverπ G
  rw [← cancel_epi ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ G)),
    ← Category.assoc, ← Functor.map_comp, ← freeCoverMap_comp_freeCoverπ, Functor.map_comp,
    Category.assoc, map_freeCoverπ_comp_traceApp, ← Category.assoc,
    ← edge_naturality p c (flatFibres_inverseImage_freeCover p G)
      (flatFibres_inverseImage_freeCover p G'), Category.assoc, ← Functor.map_comp,
    freeCoverMap_comp_freeCoverπ, Functor.map_comp, ← Category.assoc,
    ← map_freeCoverπ_comp_traceApp, Category.assoc]

/-- **The top-degree trace `ν : U ⟶ T`** of the class `c`, natural in the sheaf. -/
def trace : etaleModuleUnderlyingAbelian B (ZMod N) ⟶ topSheaf p where
  app := traceApp p c
  naturality _ _ φ := traceApp_naturality p c φ

/-- The component of `Stacks.EtaleCohomology.TopTrace.trace` at `G` is
`Stacks.EtaleCohomology.TopTrace.traceApp`. -/
theorem trace_app (G : EtaleModules.{u, 0} (ZMod N) B) : (trace p c).app G = traceApp p c G :=
  rfl

/-- **`ν = Θ` on sheaves whose inverse images have flat fibres.** -/
theorem trace_app_eq_edge (A : EtaleModules.{u, 0} (ZMod N) B)
    (hA : FlatFibres ((etaleModuleInverseImage.{u, 0} (ZMod N) p).obj A)) :
    (trace p c).app A = edge p c A hA := by
  have := epi_map_freeCoverπ A
  rw [trace_app, ← cancel_epi ((etaleModuleUnderlyingAbelian B (ZMod N)).map (freeCoverπ A)),
    map_freeCoverπ_comp_traceApp, edge_naturality]

end Stacks.EtaleCohomology.TopTrace
