module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex

/-!
# The de Rham differential on Čech complexes over an affine base

Let `f : X ⟶ Spec A` be a scheme over an affine base and `U` a family of opens of `X`. The Čech
complexes of an `𝒪_X`-module `F` with respect to `U` are complexes of `A`-modules
(`Stacks.Cech.cechModuleComplex`, `Stacks.Cech.alternatingCechModuleComplex`). A morphism of the
underlying presheaves of abelian groups which is `A`-linear on sections acts on both, termwise,
by a morphism of complexes of `A`-modules. The de Rham differential `Ω^p_{X/A} ⟶ Ω^{p+1}_{X/A}` is
such a morphism: it is `f^{-1}𝒪_{Spec A}`-linear, and `A` acts on sections through
`f^{-1}𝒪_{Spec A}`.

## Main definitions

* `Stacks.Cech.cechModulePush` and `Stacks.Cech.alternatingCechModulePush`: the morphisms of
  Čech complexes induced by an `A`-linear morphism of presheaves.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamComplex_d_app_smul`: the de Rham differential of a scheme
  over `Spec A` is `A`-linear on sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I : Type u}
  (U : I → X.Opens) {F G : X.Modules} (ψ : F.presheaf ⟶ G.presheaf)
  (hψ : ∀ (W : X.Opens) (a : A) (x : Γ(F, W)),
    ψ.app (op W) ((baseRingHom f W).hom a • x) = (baseRingHom f W).hom a • ψ.app (op W) x)

include hψ in
/-- A morphism of presheaves which is `A`-linear on sections acts `A`-linearly on Čech
cochains. -/
def cochainPushₗ (p : ℕ) :
    letI := cochainModule f U F p
    letI := cochainModule f U G p
    CechCochains.Cochain U F.presheaf p →ₗ[A] CechCochains.Cochain U G.presheaf p :=
  letI := cochainModule f U F p
  letI := cochainModule f U G p
  { toFun := Stacks.Cohomology.CechOne.push U ψ p
    map_add' := map_add _
    map_smul' := fun a s => funext fun i => hψ _ a (s i) }

include hψ in
/-- The same on alternating cochains. -/
def alternatingCochainPushₗ (p : ℕ) :
    letI := cochainModule f U F p
    letI := cochainModule f U G p
    alternatingSubmodule f U F p →ₗ[A] alternatingSubmodule f U G p :=
  letI := cochainModule f U F p
  letI := cochainModule f U G p
  (cochainPushₗ f U ψ hψ p).restrict fun _ hs => cochainMap_isAlternating U ψ p hs

include ψ hψ in
/-- **The morphism of Čech complexes of `A`-modules induced by an `A`-linear morphism of the
underlying presheaves.** -/
def cechModulePush : cechModuleComplex f U F ⟶ cechModuleComplex f U G where
  f p :=
    letI := cochainModule f U F p
    letI := cochainModule f U G p
    ModuleCat.ofHom (cochainPushₗ f U ψ hψ p)
  comm' := by
    rintro p q (rfl : p + 1 = q)
    rw [cechModuleComplex_d, cechModuleComplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    change CechCochains.cechD U G.presheaf p (Stacks.Cohomology.CechOne.push U ψ p s) =
      Stacks.Cohomology.CechOne.push U ψ (p + 1) (CechCochains.cechD U F.presheaf p s)
    exact (Stacks.Cohomology.CechOne.push_cechD U ψ p s).symm

include ψ hψ in
/-- **The morphism of alternating Čech complexes of `A`-modules induced by an `A`-linear morphism
of the underlying presheaves.** -/
def alternatingCechModulePush :
    alternatingCechModuleComplex f U F ⟶ alternatingCechModuleComplex f U G where
  f p := ModuleCat.ofHom (alternatingCochainPushₗ f U ψ hψ p)
  comm' := by
    rintro p q (rfl : p + 1 = q)
    rw [alternatingCechModuleComplex_d, alternatingCechModuleComplex_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun s => Subtype.ext ?_)
    change CechCochains.cechD U G.presheaf p (Stacks.Cohomology.CechOne.push U ψ p s.1) =
      Stacks.Cohomology.CechOne.push U ψ (p + 1) (CechCochains.cechD U F.presheaf p s.1)
    exact (Stacks.Cohomology.CechOne.push_cechD U ψ p s.1).symm

/-- The push commutes with the inclusion of the alternating complex. -/
theorem alternatingCechModulePush_inclusion :
    alternatingCechModulePush f U ψ hψ ≫ alternatingCechModuleComplex_inclusion f U G =
      alternatingCechModuleComplex_inclusion f U F ≫ cechModulePush f U ψ hψ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  rfl

end Stacks.Cech

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (h : X ⟶ Spec (.of A))

/-- **The structural ring map of a scheme over `Spec A` factors through `h^{-1}𝒪_{Spec A}`**: on
every open `W`, the image of `a ∈ A` in `Γ(X, W)` is the image, under the structure map
`h^{-1}𝒪_{Spec A} ⟶ 𝒪_X`, of a section of `h^{-1}𝒪_{Spec A}` over `W`. This is the triangle
identity of `h^{-1} ⊣ h_*` at the structure map. -/
theorem exists_inverseImageStructureMap_app_eq_baseRingHom (W : X.Opens) (a : A) :
    ∃ c : ((TopCat.Sheaf.pullback CommRingCat h.base).obj (Spec (.of A)).sheaf).obj.obj (op W),
      ((inverseImageStructureMap h).hom.app (op W)).hom c =
        (Stacks.Cech.baseRingHom h W).hom a := by
  let baseAdjunction := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat h.base
  let baseUnit := baseAdjunction.unit.app (Spec (.of A)).sheaf
  let structureMap : (Spec (.of A)).sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat h.base).obj X.sheaf := ⟨h.c⟩
  have htriangle : baseUnit ≫ (TopCat.Sheaf.pushforward CommRingCat h.base).map
      (inverseImageStructureMap h) = structureMap := by
    change baseAdjunction.homEquiv (Spec (.of A)).sheaf X.sheaf (inverseImageStructureMap h) =
      structureMap
    exact (baseAdjunction.homEquiv (Spec (.of A)).sheaf X.sheaf).apply_symm_apply structureMap
  let a₀ : Γ(Spec (.of A), ⊤) := (_root_.AlgebraicGeometry.toSpecΓ (CommRingCat.of A)).hom a
  refine ⟨((TopCat.Sheaf.pullback CommRingCat h.base).obj (Spec (.of A)).sheaf).obj.map
    (homOfLE le_top).op ((baseUnit.hom.app (op ⊤)).hom a₀), ?_⟩
  have hnat := ConcreteCategory.congr_hom
    ((inverseImageStructureMap h).hom.naturality (homOfLE (le_top : W ≤ ⊤)).op)
    ((baseUnit.hom.app (op ⊤)).hom a₀)
  have htop := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op (⊤ : Opens (Spec (.of A))))) htriangle) a₀
  change _ = (X.presheaf.map (homOfLE le_top).op).hom ((h.appTop).hom a₀)
  exact hnat.trans (congrArg (X.presheaf.map (homOfLE le_top).op).hom htop)

/-- The de Rham differential `Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}`, as a morphism of the underlying
presheaves of abelian groups. -/
def deRhamPresheafD (p : ℕ) :
    (relativeDifferentialForms h (p : ℤ)).presheaf ⟶
      (relativeDifferentialForms h ((p + 1 : ℕ) : ℤ)).presheaf :=
  ((SheafOfModules.toSheaf _).map (h.deRhamComplex.d p (p + 1))).hom

/-- **The de Rham differential of a scheme over `Spec A` is `A`-linear on sections**, for the
action of `A` through the structural map. -/
theorem deRhamPresheafD_app_smul (p : ℕ) (W : X.Opens) (a : A)
    (x : Γ(relativeDifferentialForms h (p : ℤ), W)) :
    (deRhamPresheafD h p).app (op W) ((Stacks.Cech.baseRingHom h W).hom a • x) =
      (Stacks.Cech.baseRingHom h W).hom a • (deRhamPresheafD h p).app (op W) x := by
  obtain ⟨c, hc⟩ := exists_inverseImageStructureMap_app_eq_baseRingHom h W a
  rw [← hc]
  exact ((h.deRhamComplex.d p (p + 1)).val.app (op W)).hom.map_smul c x

end AlgebraicGeometry.Scheme.Hom
