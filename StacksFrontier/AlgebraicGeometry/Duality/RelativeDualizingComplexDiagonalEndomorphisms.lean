module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexDiagonalGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexSquareOpens
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Endomorphisms of the diagonal object, and the generator of a relative dualizing complex

Let `f : X ⟶ S` be a morphism of schemes and `D` an open `W ⊆ X ×_S X` through which the
relative diagonal factors as a closed immersion `Δ : X ⟶ W`. The ring `Γ(X, 𝒪_X)` acts on
`D(𝒪_W)` through `pr₁^♯ : Γ(X, 𝒪_X) ⟶ Γ(W, 𝒪_W)`. This file proves:

* every endomorphism of `Δ_*𝒪_X` in `D(𝒪_W)` is multiplication by a unique element of
  `Γ(X, 𝒪_X)`: an `𝒪_W`-linear endomorphism of `Δ_*𝒪_X` is `Δ_*𝒪_X`-linear because `𝒪_W ⟶ Δ_*𝒪_X`
  is locally surjective, and `Δ^♯ ∘ pr₁^♯ = id`;
* the map `ζ ↦ a(ζ)` defined by the diagonal is `Γ(X, 𝒪_X)`-linear;
* if `a(η)` is an isomorphism, as for a relative dualizing complex `(L, η)`, then
  `Hom(Δ_*𝒪_X, L pr₁^*L|_W)` is free of rank one over `Γ(X, 𝒪_X)` on `η`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.exists_eq_smul_id_diagonalObject`
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.smul_id_diagonalObject_injective`
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.diagonalAction_smul`
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.existsUnique_eq_smul_of_isIso_diagonalAction`

## References

* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Lemma 48.28.5 (Tag 0E2W)](https://stacks.math.columbia.edu/tag/0E2W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect
  AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- The closed immersion `Δ : X ⟶ W` is a section of `pr₁|_W : W ⟶ X`. -/
@[reassoc (attr := simp)]
alias diag_proj := diag_proj_eq_id

/-- The structure map `𝒪_W ⟶ Δ_*𝒪_X` of the closed immersion `Δ` is locally surjective. -/
instance isLocallySurjective_structureMap :
    Sheaf.IsLocallySurjective
      (Stacks.RelativeSpec.AlgebraSheaf.structureMap D.diagonalAlgebra) := by
  have := D.isClosedImmersion
  change TopCat.Presheaf.IsLocallySurjective _
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    (isBasis_affineOpens D.W).exists_subset_of_mem_open hx U.isOpen
  obtain ⟨s, hs⟩ := D.diag.app_surjective V hV (TopCat.Presheaf.restrictOpen t V hVU)
  exact ⟨V, hVU, ⟨s, hs⟩, hxV⟩

/-! ### Scalars -/

/-- Multiplication by the image in `Γ(W, 𝒪_W)` of `a ∈ Γ(X, 𝒪_X)`, as an endomorphism of the
`𝒪_W`-module `Δ_*𝒪_X`. -/
abbrev diagonalScalar (a : Γ(X, ⊤)) :
    Stacks.RelativeSpec.AlgebraSheaf.moduleOfAlgebra D.diagonalAlgebra ⟶
      Stacks.RelativeSpec.AlgebraSheaf.moduleOfAlgebra D.diagonalAlgebra :=
  (Stacks.SheafOfModules.terminalSectionToEnd D.W.ringCatSheaf ⊤ isTerminalTop
    (D.proj.appTop a)).asHom.app _

/-- **A scalar of `Γ(X, 𝒪_X)` acting on `Δ_*𝒪_X` in `D(𝒪_W)` is the image of its action on the
module.** -/
theorem smul_id_diagonalObject (a : Γ(X, ⊤)) :
    letI := D.proj.linearStructureSheafModules
    (a • 𝟙 D.diagonalObject : D.diagonalObject ⟶ D.diagonalObject) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor
        (SheafOfModules.{u} D.W.ringCatSheaf) 0).map (D.diagonalScalar a)) := by
  let := D.proj.linearStructureSheafModules
  have h1 : 𝟙 D.diagonalObject = (DerivedCategory.singleFunctor
      (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) 0).map
        (𝟙 D.diagonalAlgebra.moduleOfAlgebra) :=
    (CategoryTheory.Functor.map_id (DerivedCategory.singleFunctor
      (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) 0)
        D.diagonalAlgebra.moduleOfAlgebra).symm
  rw [h1, ← Functor.map_smul]
  exact congrArg _ (Category.comp_id _)

/-- **Scalars commute with the derived multiplication of `Δ_*𝒪_X`**, acting on the first
factor. -/
theorem derivedTensor_map_smul_app_comp_derivedMul (a : Γ(X, ⊤)) :
    letI := D.proj.linearStructureSheafModules
    ((Stacks.SheafOfModules.derivedTensor D.W.sheaf).map (a • 𝟙 D.diagonalObject)).app
        D.diagonalObject ≫ D.diagonalAlgebra.derivedMul =
      D.diagonalAlgebra.derivedMul ≫ (a • 𝟙 D.diagonalObject) := by
  let := D.proj.linearStructureSheafModules
  rw [D.smul_id_diagonalObject a]
  exact Stacks.RelativeSpec.AlgebraSheaf.derivedTensor_map_single_app_comp_derivedMul
    (D.diagonalScalar a)
    (Stacks.RelativeSpec.AlgebraSheaf.sheafTensor_map_globalSectionToEnd_comp_mul _ _)

/-- **The section of the derived multiplication of `Δ_*𝒪_X` commutes with scalars**, acting on
the first factor. -/
theorem derivedMulSection_comp_derivedTensor_map_smul_app (a : Γ(X, ⊤)) :
    letI := D.proj.linearStructureSheafModules
    D.diagonalAlgebra.derivedMulSection ≫
        ((Stacks.SheafOfModules.derivedTensor D.W.sheaf).map (a • 𝟙 D.diagonalObject)).app
          D.diagonalObject =
      (a • 𝟙 D.diagonalObject) ≫ D.diagonalAlgebra.derivedMulSection := by
  let := D.proj.linearStructureSheafModules
  rw [D.smul_id_diagonalObject a]
  exact Stacks.RelativeSpec.AlgebraSheaf.derivedMulSection_comp_derivedTensor_map_single_app
    (D.diagonalScalar a)
    (Stacks.RelativeSpec.AlgebraSheaf.sheafTensor_map_globalSectionToEnd_comp_mul _ _)

/-- A scalar multiple is the composite with the scalar acting on the source. -/
theorem smul_eq_smul_id_comp {P Q : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules
      D.W.sheaf)} (a : Γ(X, ⊤)) (f : P ⟶ Q) :
    letI := D.proj.linearStructureSheafModules
    a • f = (a • 𝟙 P) ≫ f := by
  let := D.proj.linearStructureSheafModules
  rw [Linear.smul_comp, Category.id_comp]

/-- `Stacks.SheafOfModules.derivedSheafHomTensorEquiv` is natural in the source: precomposing with
an endomorphism of `Δ_*𝒪_X` is tensoring that endomorphism with `Δ_*𝒪_X`. -/
theorem derivedSheafHomTensorEquiv_comp_diagonalObject
    {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)} (w : D.diagonalObject ⟶ D.diagonalObject)
    (ψ : D.diagonalObject ⟶
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj
        (D.derivedPullbackProj K)) :
    Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
      D.diagonalObject (D.derivedPullbackProj K) (w ≫ ψ) =
      ((Stacks.SheafOfModules.derivedTensor D.W.sheaf).map w).app D.diagonalObject ≫
        Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
          D.diagonalObject (D.derivedPullbackProj K) ψ :=
  let := Stacks.SheafOfModules.derivedMonoidalStructure D.W.sheaf
  Stacks.SheafOfModules.derivedSheafHomTensorEquiv_comp_left D.W.sheaf _ _ _ ψ

/-- The transposes of the maps that `a • ζ` and `ζ` define differ by the scalar `a`. -/
theorem derivedSheafHomTensorEquiv_diagonalAction_smul
    {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)} (a : Γ(X, ⊤))
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    letI := D.proj.linearStructureSheafModules
    Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
      D.diagonalObject (D.derivedPullbackProj K) (D.diagonalAction K (a • ζ)) =
      ((Stacks.SheafOfModules.derivedTensor D.W.sheaf).map (a • 𝟙 D.diagonalObject)).app
        D.diagonalObject ≫
          Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
      D.diagonalObject (D.derivedPullbackProj K) (D.diagonalAction K ζ) :=
  (D.derivedSheafHomTensorEquiv_diagonalAction_apply _).trans
    ((congrArg (D.diagonalAlgebra.derivedMul ≫ ·) (D.smul_eq_smul_id_comp _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ ζ) (D.derivedTensor_map_smul_app_comp_derivedMul _).symm).trans
          ((Category.assoc _ _ _).trans
            (congrArg (_ ≫ ·) (D.derivedSheafHomTensorEquiv_diagonalAction_apply _).symm)))))

/-- **The diagonal action is `Γ(X, 𝒪_X)`-linear**: the map defined by `a • ζ` is the map defined
by `ζ` precomposed with the scalar `a` of `Δ_*𝒪_X`. -/
theorem diagonalAction_smul {K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)} (a : Γ(X, ⊤))
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    letI := D.proj.linearStructureSheafModules
    D.diagonalAction K (a • ζ) = (a • 𝟙 D.diagonalObject) ≫ D.diagonalAction K ζ :=
  (Stacks.SheafOfModules.derivedSheafHomTensorEquiv D.W.sheaf D.diagonalObject
      D.diagonalObject (D.derivedPullbackProj K)).injective
    ((D.derivedSheafHomTensorEquiv_diagonalAction_smul _ _).trans
      (D.derivedSheafHomTensorEquiv_comp_diagonalObject _ _).symm)

/-- The section of the derived multiplication commutes with scalars, in reassociated form. -/
theorem derivedMulSection_comp_derivedTensor_map_smul_app_comp
    {Z : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf)} (a : Γ(X, ⊤))
    (g : ((Stacks.SheafOfModules.derivedTensor D.W.sheaf).obj D.diagonalObject).obj
      D.diagonalObject ⟶ Z) :
    letI := D.proj.linearStructureSheafModules
    D.diagonalAlgebra.derivedMulSection ≫
      (((Stacks.SheafOfModules.derivedTensor D.W.sheaf).map (a • 𝟙 D.diagonalObject)).app
        D.diagonalObject ≫ g) =
      (a • 𝟙 D.diagonalObject) ≫ (D.diagonalAlgebra.derivedMulSection ≫ g) := by
  rw [← Category.assoc, D.derivedMulSection_comp_derivedTensor_map_smul_app, Category.assoc]

/-- `Δ^♯ ∘ pr₁^♯` is the identity on global sections, `Δ` being a section of `pr₁|_W`. -/
theorem diag_appTop_proj_appTop_apply (a : Γ(X, ⊤)) : D.diag.appTop (D.proj.appTop a) = a := by
  have h : D.proj.appTop ≫ D.diag.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, D.diag_proj, Scheme.Hom.id_appTop]
  simpa using congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(X, ⊤) => φ a) h

/-- `Δ^♯ ∘ pr₁^♯` is the identity on global sections, with `Δ^♯` written as `D.diag.app ⊤`. -/
theorem diag_app_top_proj_appTop_apply (a : Γ(X, ⊤)) : D.diag.app ⊤ (D.proj.appTop a) = a :=
  D.diag_appTop_proj_appTop_apply a

/-! ### Endomorphisms of `Δ_*𝒪_X` -/

/-- **Every `𝒪_W`-linear endomorphism of `Δ_*𝒪_X` is multiplication by a global function on
`X`**, namely by its value on the section `1`. Since `𝒪_W ⟶ Δ_*𝒪_X` is locally surjective, an
`𝒪_W`-linear endomorphism is `Δ_*𝒪_X`-linear, hence multiplication by the image of `1`. -/
theorem eq_diagonalScalar
    (c : D.diagonalAlgebra.moduleOfAlgebra ⟶ D.diagonalAlgebra.moduleOfAlgebra) :
    c = D.diagonalScalar (c.val.app (op ⊤) (1 : D.diagonalAlgebra.right.obj.obj (op ⊤))) := by
  have : (SheafOfModules.restrictScalars
      (Stacks.RelativeSpec.AlgebraSheaf.structureMap D.diagonalAlgebra)).Full :=
    Stacks.SheafOfModules.ChangeOfRings.full_restrictScalars _
  let c₁ := (SheafOfModules.restrictScalars
    (Stacks.RelativeSpec.AlgebraSheaf.structureMap D.diagonalAlgebra)).preimage c
  have hc : (SheafOfModules.restrictScalars
      (Stacks.RelativeSpec.AlgebraSheaf.structureMap D.diagonalAlgebra)).map c₁ = c :=
    Functor.map_preimage _ _
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let i : U.unop ⟶ ⊤ := homOfLE le_top
  let a := c.val.app (op ⊤) (1 : D.diagonalAlgebra.ringSheaf.obj.obj (op ⊤))
  have hlin : ∀ r : D.diagonalAlgebra.ringSheaf.obj.obj U, c₁.val.app U r =
      r * (@id (D.diagonalAlgebra.ringSheaf.obj.obj U)
        (c₁.val.app U (1 : D.diagonalAlgebra.ringSheaf.obj.obj U))) := fun r => by
    calc c₁.val.app U r = c₁.val.app U (r • (1 : D.diagonalAlgebra.ringSheaf.obj.obj U)) :=
          congrArg (c₁.val.app U) (mul_one r).symm
      _ = r • c₁.val.app U (1 : D.diagonalAlgebra.ringSheaf.obj.obj U) :=
          (c₁.val.app U).hom.map_smul r _
      _ = _ := rfl
  have h1 : ∀ r : D.diagonalAlgebra.ringSheaf.obj.obj U, c.val.app U r = c₁.val.app U r :=
    fun r => by rw [← hc]; rfl
  have h5 : c.val.app U (1 : D.diagonalAlgebra.ringSheaf.obj.obj U) =
      X.presheaf.map ((Opens.map D.diag.base).map i).op a := by
    have hn := PresheafOfModules.naturality_apply c.val i.op
      (1 : D.diagonalAlgebra.ringSheaf.obj.obj (op ⊤))
    have h1U : (D.diagonalAlgebra.moduleOfAlgebra.val.map i.op)
        (1 : D.diagonalAlgebra.ringSheaf.obj.obj (op ⊤)) =
          (1 : D.diagonalAlgebra.ringSheaf.obj.obj U) :=
      map_one (D.diagonalAlgebra.right.obj.map i.op).hom
    rwa [h1U] at hn
  have h6 : D.diag.app U.unop (D.W.presheaf.map i.op (D.proj.appTop a)) =
      X.presheaf.map ((Opens.map D.diag.base).map i).op a := by
    have hn := congrArg (fun φ : D.W.presheaf.obj (op ⊤) ⟶
        X.presheaf.obj (op (D.diag ⁻¹ᵁ U.unop)) => φ (D.proj.appTop a))
        (D.diag.naturality i.op)
    simp only [ConcreteCategory.comp_apply] at hn
    exact hn.trans (congrArg (ConcreteCategory.hom (X.presheaf.map ((Opens.map D.diag.base).map
      i).op)) (D.diag_app_top_proj_appTop_apply _))
  have key : c.val.app U x = (@id (D.diagonalAlgebra.ringSheaf.obj.obj U) x) *
      @id (D.diagonalAlgebra.ringSheaf.obj.obj U)
        (X.presheaf.map ((Opens.map D.diag.base).map i).op a) := by
    rw [h1 x, hlin x, ← h1 1, h5]
    rfl
  have hcomm : ∀ r s : D.diagonalAlgebra.ringSheaf.obj.obj U, r * s = s * r := fun r s => by
    let : CommRing (D.diagonalAlgebra.ringSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (D.diagonalAlgebra.right.obj.obj U))
    exact mul_comm r s
  exact key.trans ((hcomm _ _).trans (congrArg (fun y : D.diagonalAlgebra.ringSheaf.obj.obj U =>
    y * @id (D.diagonalAlgebra.ringSheaf.obj.obj U) x) h6.symm))

/-- On the section `1` over `W`, multiplication by `a` gives `a`. -/
theorem diagonalScalar_app_top_one (a : Γ(X, ⊤)) :
    (D.diagonalScalar a).val.app (op ⊤) (1 : D.diagonalAlgebra.right.obj.obj (op ⊤)) = a := by
  change D.diag.app ⊤ (D.W.presheaf.map (𝟙 (op (⊤ : D.W.Opens))) (D.proj.appTop a)) * 1 = a
  rw [CategoryTheory.Functor.map_id, mul_one]
  exact D.diag_appTop_proj_appTop_apply a

/-- **Every endomorphism of `Δ_*𝒪_X` in `D(𝒪_W)` is a scalar of `Γ(X, 𝒪_X)`.** -/
theorem exists_eq_smul_id_diagonalObject (c : D.diagonalObject ⟶ D.diagonalObject) :
    letI := D.proj.linearStructureSheafModules
    ∃ a : Γ(X, ⊤), c = a • 𝟙 D.diagonalObject := by
  let := D.proj.linearStructureSheafModules
  let c₀ := (DerivedCategory.singleFunctor
    (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) 0).preimage c
  have hc : (DerivedCategory.singleFunctor
      (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) 0).map c₀ = c :=
    Functor.map_preimage _ _
  obtain ⟨a, ha⟩ : ∃ a : Γ(X, ⊤), c₀ = D.diagonalScalar a := ⟨_, D.eq_diagonalScalar c₀⟩
  refine ⟨a, ?_⟩
  rw [D.smul_id_diagonalObject, ← hc]
  exact congrArg (fun t => DerivedCategory.Q.map ((CochainComplex.singleFunctor
    (SheafOfModules.{u} D.W.ringCatSheaf) 0).map t)) ha

/-- **Scalars act faithfully on `Δ_*𝒪_X`.** -/
theorem smul_id_diagonalObject_injective :
    letI := D.proj.linearStructureSheafModules
    Function.Injective (fun a : Γ(X, ⊤) => (a • 𝟙 D.diagonalObject :
      D.diagonalObject ⟶ D.diagonalObject)) := by
  let := D.proj.linearStructureSheafModules
  intro a b h
  have h' : D.diagonalScalar a = D.diagonalScalar b := by
    apply (DerivedCategory.singleFunctor
      (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf) 0).map_injective
    exact (D.smul_id_diagonalObject a).symm.trans (h.trans (D.smul_id_diagonalObject b))
  rw [← D.diagonalScalar_app_top_one a, ← D.diagonalScalar_app_top_one b, h']

/-! ### The diagonal map generates -/

/-- **Free of rank one.** If `η` makes `(L, η)` satisfy the dualizing condition, every map
`Δ_*𝒪_X ⟶ L pr₁^*L|_W` is `a • η` for a unique `a ∈ Γ(X, 𝒪_X)`. -/
theorem existsUnique_eq_smul_of_isIso_diagonalAction
    {L : DerivedCategory (OXMod.{u, u} X.toRingedSpace)}
    {η : D.diagonalObject ⟶ D.derivedPullbackProj L} (hη : IsIso (D.diagonalAction L η))
    (ζ : D.diagonalObject ⟶ D.derivedPullbackProj L) :
    letI := D.proj.linearStructureSheafModules
    ∃! a : Γ(X, ⊤), ζ = a • η := by
  obtain ⟨a, ha⟩ := D.exists_eq_smul_id_diagonalObject
    (D.diagonalAction L ζ ≫ inv (D.diagonalAction L η))
  have hz := (IsIso.comp_inv_eq _).mp ha
  refine ⟨a, D.diagonalAction_injective L (hz.trans (D.diagonalAction_smul a η).symm),
    fun b hb => ?_⟩
  have hb' := (congrArg (D.diagonalAction L) hb).trans (D.diagonalAction_smul b η)
  exact D.smul_id_diagonalObject_injective ((cancel_mono (D.diagonalAction L η)).mp
    (hb'.symm.trans hz))

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
