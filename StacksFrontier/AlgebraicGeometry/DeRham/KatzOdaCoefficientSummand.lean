module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaPulledBackWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquareAtCut
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeComponentGeneratedEpi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings

/-!
# The summands of the step of Section 50.12, for a general coefficient module

For `f : X ⟶ Y` over `S` and an `𝒪_Y`-module `M`, this file builds the morphism
`f^{-1}M ⊗_{(f∘g)^{-1}𝒪_S} Ω^q_{X/S} ⟶ (f^{-1}M[-c] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y})^n`, `n = c + q`,
`x ⊗ ω ↦ θ(x) ⊗ q(ω)` (`Stacks.DeRhamSmooth.coefficientSummandToTarget`), which at
`M = Ω^c_{Y/S}` is `Stacks.DeRhamSmooth.stepSummandToGradedTarget`. It is natural in `M`
(`Stacks.DeRhamSmooth.coefficientSummandToTarget_naturality`), an epimorphism
(`Stacks.DeRhamSmooth.epi_coefficientSummandToTarget`), and compatible with the shift from the cut
`c` to the cut `c + p` (`Stacks.DeRhamSmooth.coefficientSummandToTarget_comp_shiftHom_f`). These
are the inputs of the step-square compatibility of the Katz–Oda description of `d_1` in
[Stacks, Tag 0FMN]. No `@[stacks]` attribute is attached here.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceCotangent (baseStructureMap)

universe u

attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-! ### The comparison of the two inverse images of a module -/

/-- **The transpose of the comparison of the two inverse images of an `𝒪_Y`-module `M`**: the unit
of the pullback along `(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)` at `M`, read over `g^{-1}𝒪_S` and carried along
the square `Stacks.DeRhamDirectImage.inverseImageBaseProjection_comp_toInverseImageBase`. At
`M = Ω^k_{Y/S}` it is `Stacks.DeRhamSmooth.pulledBackFormsToTargetLeg`. -/
def coefficientPulledBackLeg (M : Modules Y.toRingedSpace) :
    (pushforward (toInverseImageBase g)).obj M ⟶
      (pushforward (relativeBase f g)).obj
        ((coefficientRestriction f g).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)) :=
  (pushforward (toInverseImageBase g)).map
      ((_root_.pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app M) ≫
    (pushforwardComp (inverseImageBaseProjection f) (toInverseImageBase g)).inv.app _ ≫
    eqToHom (congrArg (fun m : inverseImageBase f ⟶ inverseImageBase g =>
      (pushforward m).obj ((_root_.pullback (inverseImageBaseProjection f)).obj M))
      (inverseImageBaseProjection_comp_toInverseImageBase f g)) ≫
    (pushforwardComp (coefficientRingChange f g) (relativeBase f g)).hom.app _

/-- **The comparison `f^{-1}M ⟶ (f^{-1}M)|_{(f∘g)^{-1}𝒪_S}` of the two inverse images of an
`𝒪_Y`-module `M`**: from the one along `(X, (f∘g)^{-1}𝒪_S) ⟶ (Y, g^{-1}𝒪_S)` to the one along
`(X, f^{-1}𝒪_Y) ⟶ (Y, 𝒪_Y)`, read over `(f∘g)^{-1}𝒪_S`. At `M = Ω^k_{Y/S}` it is
`Stacks.DeRhamSmooth.pulledBackFormsToTarget`. -/
def coefficientPulledBackComparison (M : Modules Y.toRingedSpace) :
    (_root_.pullback (relativeBase f g)).obj ((pushforward (toInverseImageBase g)).obj M) ⟶
      (coefficientRestriction f g).obj ((_root_.pullback (inverseImageBaseProjection f)).obj M) :=
  ((_root_.pullbackPushforwardAdjunction (relativeBase f g)).homEquiv _ _).symm
    (coefficientPulledBackLeg f g M)

/-- At `Ω^k_{Y/S}` the comparison is `Stacks.DeRhamSmooth.pulledBackFormsToTarget`. -/
theorem coefficientPulledBackComparison_relativeDifferentialForms (k : ℕ) :
    coefficientPulledBackComparison f g
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) =
      pulledBackFormsToTarget f g k :=
  rfl

/-- The transpose of the comparison is the pullback unit on sections. -/
theorem coefficientPulledBackLeg_val_app_heq (M : Modules Y.toRingedSpace)
    (V : (Opens Y.carrier)ᵒᵖ) (s : ((pushforward (toInverseImageBase g)).obj M).val.obj V) :
    (coefficientPulledBackLeg f g M).val.app V s ≍
      ((_root_.pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app M).val.app
        V s :=
  eqToHom_val_app_heq (Z := inverseImageBase g)
    (congrArg (fun m : inverseImageBase f ⟶ inverseImageBase g =>
      (pushforward m).obj ((_root_.pullback (inverseImageBaseProjection f)).obj M))
      (inverseImageBaseProjection_comp_toInverseImageBase f g)) V _

/-- The transpose of the comparison is the pullback unit on sections. -/
theorem coefficientPulledBackLeg_val_app (M : Modules Y.toRingedSpace)
    (V : (Opens Y.carrier)ᵒᵖ) (s : ((_root_.pushforward (toInverseImageBase g)).obj M).val.obj V) :
    (coefficientPulledBackLeg f g M).val.app V s =
      ((_root_.pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app M).val.app
        V s :=
  eq_of_heq (coefficientPulledBackLeg_val_app_heq f g M V s)

/-- **The comparison of the two inverse images is natural in the module.** -/
theorem coefficientPulledBackComparison_naturality {M M' : Modules Y.toRingedSpace}
    (φ : M ⟶ M') :
    coefficientPulledBackComparison f g M ≫
        (coefficientRestriction f g).map ((_root_.pullback (inverseImageBaseProjection f)).map φ) =
      (_root_.pullback (relativeBase f g)).map ((_root_.pushforward (toInverseImageBase g)).map φ) ≫
        coefficientPulledBackComparison f g M' := by
  apply ((_root_.pullbackPushforwardAdjunction (relativeBase f g)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    coefficientPulledBackComparison, coefficientPulledBackComparison, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  ext V s
  refine Eq.trans
    (congrArg (fun t => ((_root_.pullback (inverseImageBaseProjection f)).map φ).val.app
      (op ((Opens.map (inverseImageBaseProjection f).hom.base).obj V.unop)) t)
      (coefficientPulledBackLeg_val_app f g M V s)) ?_
  exact (pullback_map_unit_apply (inverseImageBaseProjection f) φ V.unop s).trans
    (coefficientPulledBackLeg_val_app f g M' V (φ.val.app V s)).symm

/-- The comparison carries the pullback-unit section of `s` to the pullback-unit section of `s`. -/
theorem coefficientPulledBackComparison_unit_apply (M : Modules Y.toRingedSpace)
    (V : Opens Y.carrier)
    (s : ((_root_.pushforward (toInverseImageBase g)).obj M).val.obj (op V)) :
    (coefficientPulledBackComparison f g M).val.app
        (op ((Opens.map (relativeBase f g).hom.base).obj V))
      (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((_root_.pushforward (toInverseImageBase g)).obj M)).val.app (op V) s) =
      ((_root_.pullbackPushforwardAdjunction (inverseImageBaseProjection f)).unit.app M).val.app
        (op V) s := by
  have h : (_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
        ((_root_.pushforward (toInverseImageBase g)).obj M) ≫
      (_root_.pushforward (relativeBase f g)).map (coefficientPulledBackComparison f g M) =
      coefficientPulledBackLeg f g M :=
    ((_root_.pullbackPushforwardAdjunction (relativeBase f g)).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  exact (congrArg (fun φ => φ.val.app (op V) s) h).trans
    (coefficientPulledBackLeg_val_app f g M (op V) s)

/-! ### The summands of the step, for a general coefficient module -/

/-- The degree-`n` term of `f^{-1}M[-c] ⊗ Ω^•_{X/Y}` is `f^{-1}M ⊗ Ω^{n-c}_{X/Y}`, by
definition. -/
theorem coefficientTargetComplex_X (c : ℕ) (M : Modules Y.toRingedSpace) (n : ℤ) :
    ((coefficientTargetComplex f g c).obj M).X n =
      (coefficientRestriction f g).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)).obj
          ((deRhamCochainComplex f).X (n + -(c : ℤ)))) :=
  rfl

/-- **The degree-`n` term of `f^{-1}M[-c] ⊗ Ω^•_{X/Y}` is `f^{-1}M ⊗ Ω^q_{X/Y}`** for
`n = c + q`; at `M = Ω^c_{Y/S}` it is `Stacks.DeRhamSmooth.gradedTargetXIso`. -/
def coefficientTargetXIso (c : ℕ) (M : Modules Y.toRingedSpace) (q : ℕ) (n : ℤ)
    (h : n + -(c : ℤ) = (q : ℤ)) :
    ((coefficientTargetComplex f g c).obj M).X n ≅
      (coefficientRestriction f g).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)).obj
          ((_root_.pushforward (toInverseImageBase f)).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((q : ℕ) : ℤ)))) :=
  eqToIso (coefficientTargetComplex_X f g c M n) ≪≫
    (coefficientRestriction f g).mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)).mapIso
        ((deRhamCochainComplex f).XIsoOfEq h ≪≫ deRhamCochainXIso f q))

/-- At `Ω^c_{Y/S}` it is `Stacks.DeRhamSmooth.gradedTargetXIso`. -/
theorem coefficientTargetXIso_relativeDifferentialForms (c q n : ℕ) (h : c + q = n) :
    coefficientTargetXIso f g c (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (c : ℤ))
        q (n : ℤ) (by subst h; push_cast; ring) = gradedTargetXIso f g c q n h :=
  rfl

/-- **`x ⊗ ω ↦ θ(x) ⊗ q(ω)` into the degree-`n` term of `f^{-1}M[-c] ⊗ Ω^•_{X/Y}`**, `n = c + q`:
`θ ⊗ 1`, the triangle of restrictions of scalars, the lax comparison along
`(f∘g)^{-1}𝒪_S ⟶ f^{-1}𝒪_Y`, `1 ⊗ q` and the inverse of
`Stacks.DeRhamSmooth.coefficientTargetXIso`, the body of
`Stacks.DeRhamSmooth.stepSummandToGradedTarget` with `Ω^c_{Y/S}` replaced by `M`. At
`M = Ω^c_{Y/S}` and `q = j + 1` it is `Stacks.DeRhamSmooth.stepSummandToGradedTarget`. -/
def coefficientSummandToTarget (c : ℕ) (M : Modules Y.toRingedSpace) (q : ℕ) (n : ℤ)
    (h : n + -(c : ℤ) = (q : ℤ)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
          ((_root_.pullback (relativeBase f g)).obj
            ((_root_.pushforward (toInverseImageBase g)).obj M))).obj
        ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ))) ⟶
      ((coefficientTargetComplex f g c).obj M).X n :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        (coefficientPulledBackComparison f g M)).app _ ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
        ((coefficientRestriction f g).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M))).map
      ((coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ))) ≫
    Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
      (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)
      ((_root_.pullback (inverseImageBaseProjection f)).obj M)
      ((_root_.pushforward (toInverseImageBase f)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ))) ≫
    (coefficientRestriction f g).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
        ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map
          (formsToRelativeCochain f g q)) ≫
    (coefficientTargetXIso f g c M q n h).inv

/-- At `Ω^k_{Y/S}` and `q = j + 1` it is `Stacks.DeRhamSmooth.stepSummandToGradedTarget`. -/
theorem coefficientSummandToTarget_succ (k j : ℕ) :
    coefficientSummandToTarget f g k
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ)) (j + 1)
        ((k + 1 + j : ℕ) : ℤ) (by push_cast; ring) =
      stepSummandToGradedTarget f g k j :=
  rfl

/-- Five naturality squares, pasted. -/
theorem comp5_naturality_paste {C : Type*} [Category C]
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅)
    (b₁ : B₀ ⟶ B₁) (b₂ : B₁ ⟶ B₂) (b₃ : B₂ ⟶ B₃) (b₄ : B₃ ⟶ B₄) (b₅ : B₄ ⟶ B₅)
    (v₀ : A₀ ⟶ B₀) (v₁ : A₁ ⟶ B₁) (v₂ : A₂ ⟶ B₂) (v₃ : A₃ ⟶ B₃) (v₄ : A₄ ⟶ B₄) (v₅ : A₅ ⟶ B₅)
    (h₁ : a₁ ≫ v₁ = v₀ ≫ b₁) (h₂ : a₂ ≫ v₂ = v₁ ≫ b₂) (h₃ : a₃ ≫ v₃ = v₂ ≫ b₃)
    (h₄ : a₄ ≫ v₄ = v₃ ≫ b₄) (h₅ : a₅ ≫ v₅ = v₄ ≫ b₅) :
    (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) ≫ v₅ = v₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅ := by
  simp only [Category.assoc, h₅, reassoc_of% h₄, reassoc_of% h₃, reassoc_of% h₂, reassoc_of% h₁]

/-- A functor preserves the naturality square of a natural transformation. -/
private theorem map_comp_naturality_app {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H : E ⥤ C} (η : G ⟶ H) {a b : E} (u : a ⟶ b) :
    F.map (G.map u) ≫ F.map (η.app b) = F.map (η.app a) ≫ F.map (H.map u) := by
  rw [← F.map_comp, η.naturality, F.map_comp]

/-- The inverse of `Stacks.DeRhamSmooth.coefficientTargetXIso`, with its identity transport
dropped. -/
theorem coefficientTargetXIso_inv_eq (c : ℕ) (M : Modules Y.toRingedSpace) (q : ℕ) (n : ℤ)
    (h : n + -(c : ℤ) = (q : ℤ)) :
    (coefficientTargetXIso f g c M q n h).inv =
      (coefficientRestriction f g).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map
          (((deRhamCochainComplex f).XIsoOfEq h ≪≫ deRhamCochainXIso f q).inv)) :=
  Category.comp_id _

/-- The inverse of `Stacks.DeRhamSmooth.coefficientTargetXIso` is natural in the module. -/
theorem coefficientTargetXIso_inv_naturality (c : ℕ) {M M' : Modules Y.toRingedSpace}
    (φ : M ⟶ M') (q : ℕ) (n : ℤ) (h : n + -(c : ℤ) = (q : ℤ)) :
    (coefficientTargetXIso f g c M q n h).inv ≫ ((coefficientTargetComplex f g c).map φ).f n =
      (coefficientRestriction f g).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).map
            ((_root_.pullback (inverseImageBaseProjection f)).map φ)).app
            ((_root_.pushforward (toInverseImageBase f)).obj
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((q : ℕ) : ℤ)))) ≫
        (coefficientTargetXIso f g c M' q n h).inv := by
  rw [coefficientTargetXIso_inv_eq, coefficientTargetXIso_inv_eq]
  exact map_comp_naturality_app (coefficientRestriction f g)
    ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).map
      ((_root_.pullback (inverseImageBaseProjection f)).map φ)) _

/-- The change of coefficients `Stacks.DeRhamDirectImage.coefficientRestriction` on morphisms is
the restriction of scalars of sheaves of commutative rings along the structure map, by
definition; isolated so that it is checked once. -/
theorem coefficientRestriction_map_eq_restrictScalarsSheaf_map
    {M M' : Modules (inverseImageBase f)} (a : M ⟶ M') :
    (coefficientRestriction f g).map a =
      (Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (inverseImageBase f).sheaf
        (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)).map a :=
  rfl

/-- **The lax comparison into `(- ⊗_{f^{-1}𝒪_Y} N)|` is natural in the first variable**, in the
spelling of `Stacks.DeRhamDirectImage.coefficientRestriction`. -/
theorem laxComparison_coefficientRestriction_naturality_left {M M' : Modules (inverseImageBase f)}
    (a : M ⟶ M') (N : Modules (inverseImageBase f)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        ((coefficientRestriction f g).map a)).app ((coefficientRestriction f g).obj N) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) M' N =
    Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) M N ≫
      (coefficientRestriction f g).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).map a).app N) := by
  have h := Stacks.SheafOfModules.TensorRestrictScalars.laxComparison_naturality
    ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
    (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) a
    (𝟙 N)
  simp only [Functor.uncurry_obj_map] at h
  have h' : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        ((Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
          (inverseImageBase f).sheaf
          (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)).map a)).app
          ((Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
            (inverseImageBase f).sheaf
            (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)).obj N) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) M' N =
    Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) M N ≫
      (Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
          (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).map a).app N) := by
    refine Eq.trans ?_ (h.trans ?_)
    · exact congrArg (· ≫ Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) M' N)
        (Stacks.CategoryTheory.comp_map_map_id_eq _ _ _).symm
    · exact congrArg (fun t => Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom) M N ≫
        (Stacks.SheafOfModules.TensorRestrictScalars.restrictScalarsSheaf
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
          (inverseImageBase f).sheaf
          (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)).map t)
        (Stacks.CategoryTheory.comp_map_id_eq _ _)
  refine Eq.mpr ?_ h'
  kernel_rfl

/-- **The summands into the target complex are natural in the module.** -/
theorem coefficientSummandToTarget_naturality (c : ℕ) {M M' : Modules Y.toRingedSpace}
    (φ : M ⟶ M') (q : ℕ) (n : ℤ) (h : n + -(c : ℤ) = (q : ℤ)) :
    coefficientSummandToTarget f g c M q n h ≫ ((coefficientTargetComplex f g c).map φ).f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
          ((_root_.pullback (relativeBase f g)).map
            ((_root_.pushforward (toInverseImageBase g)).map φ))).app _ ≫
        coefficientSummandToTarget f g c M' q n h := by
  have h₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        (coefficientPulledBackComparison f g M)).app
          ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ))) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        ((coefficientRestriction f g).map
          ((_root_.pullback (inverseImageBaseProjection f)).map φ))).app
          ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ))) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
          ((_root_.pullback (relativeBase f g)).map
            ((_root_.pushforward (toInverseImageBase g)).map φ))).app
          ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ))) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        (coefficientPulledBackComparison f g M')).app
          ((_root_.pushforward (toInverseImageBase (f ≫ g))).obj
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ))) :=
    (NatTrans.comp_app _ _ _).symm.trans ((congrArg (fun t => NatTrans.app t _)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map_comp
          _ _).symm.trans
        ((congrArg (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
          (coefficientPulledBackComparison_naturality f g φ)).trans
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map_comp
              _ _)))).trans
      (NatTrans.comp_app _ _ _))
  have h₂ := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
        ((coefficientRestriction f g).map
          ((_root_.pullback (inverseImageBaseProjection f)).map φ))).naturality
      ((coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ)))
  have h₃ := (laxComparison_coefficientRestriction_naturality_left f g
    ((_root_.pullback (inverseImageBaseProjection f)).map φ)
    ((_root_.pushforward (toInverseImageBase f)).obj
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ)))).symm
  exact comp5_naturality_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
    (map_comp_naturality_app (coefficientRestriction f g)
      ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).map
        ((_root_.pullback (inverseImageBaseProjection f)).map φ)) (formsToRelativeCochain f g q))
    (coefficientTargetXIso_inv_naturality f g c φ q n h)

/-! ### The summands are an epimorphism -/

/-- **`f^{-1}M` over `f^{-1}𝒪_Y` is locally generated by the image of the comparison** of the two
inverse images: the pullback-unit sections generate it locally
(`Stacks.PullbackUnitGenerators.mem_localUnitSpan`), and they are in the image
(`Stacks.DeRhamSmooth.coefficientPulledBackComparison_unit_apply`). -/
theorem mem_localSpan_comparisonSections_coefficientPulledBackComparison
    (M : Modules Y.toRingedSpace) (V : (Opens X.carrier)ᵒᵖ)
    (x : ((_root_.pullback (inverseImageBaseProjection f)).obj M).val.obj V) :
    x ∈ (Stacks.SheafOfModules.localSpan ((_root_.pullback (inverseImageBaseProjection f)).obj M)
      (AlgebraicGeometry.SheafOfModules.comparisonSections (X := inverseImageBase f)
        (A := (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (φ := baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)
        (M := (_root_.pullback (inverseImageBaseProjection f)).obj M)
        (coefficientPulledBackComparison f g M))).obj V := by
  have hT : ∀ (W : (Opens X.carrier)ᵒᵖ)
      (y : ((_root_.pullback (inverseImageBaseProjection f)).obj M).val.obj W),
      y ∈ Stacks.PullbackUnitGenerators.unitSections (inverseImageBaseProjection f) M W →
      y ∈ AlgebraicGeometry.SheafOfModules.comparisonSections (X := inverseImageBase f)
          (A := (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
          (φ := baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)
          (M := (_root_.pullback (inverseImageBaseProjection f)).obj M)
          (coefficientPulledBackComparison f g M) W := by
    intro W y hy
    obtain ⟨V₁, k, s, rfl⟩ := hy
    refine ⟨((_root_.pullback (relativeBase f g)).obj
      ((_root_.pushforward (toInverseImageBase g)).obj M)).val.map k
        (((_root_.pullbackPushforwardAdjunction (relativeBase f g)).unit.app
          ((_root_.pushforward (toInverseImageBase g)).obj M)).val.app V₁ s), ?_⟩
    refine Eq.trans (PresheafOfModules.naturality_apply
      (coefficientPulledBackComparison f g M).val k _) ?_
    exact congrArg (fun t => ((_root_.pullback (inverseImageBaseProjection f)).obj M).val.map k t)
      (coefficientPulledBackComparison_unit_apply f g M V₁.unop s)
  exact AlgebraicGeometry.SheafOfModules.mem_localSpan_map
    (𝟙 ((_root_.pullback (inverseImageBaseProjection f)).obj M)) hT
    (Stacks.PullbackUnitGenerators.mem_localUnitSpan (inverseImageBaseProjection f) M V x)

/-- `q : Ω^m_{X/S} ⟶ Ω^m_{X/Y}` is an epimorphism: it is the `m`-th exterior power of the
epimorphism `Ω_{X/S} ⟶ Ω_{X/Y}` (Tag 01CJ). -/
theorem epi_deRhamFormsToRelativeHom_app (m : ℕ) :
    Epi ((AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom f g).app (m : ℤ)) :=
  @SheafOfModules.ExtPresentation.epi_extDesc_app _ _ _ _ _ _ _ _
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentials (f ≫ g)))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentials f))
    (AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials f g)
    (AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_epi f g) m

/-- A composite of five morphisms whose first two factors are, up to a square, an isomorphism
followed by a morphism making an epimorphism with the third, and whose last two are
epimorphisms, is an epimorphism. -/
theorem epi_comp5_of_square {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ B₁ : C}
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅)
    (b₁ : A₀ ⟶ B₁) (b₂ : B₁ ⟶ A₂) (e : a₁ ≫ a₂ = b₁ ≫ b₂) (h₁ : IsIso b₁)
    (h₂ : Epi (b₂ ≫ a₃)) (h₄ : Epi a₄) (h₅ : Epi a₅) :
    Epi (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) := by
  have e' : a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ = b₁ ≫ (b₂ ≫ a₃) ≫ a₄ ≫ a₅ := by
    rw [reassoc_of% e]
    simp only [Category.assoc]
  rw [e']
  infer_instance

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens in
/-- **The summands of the step, for a general coefficient module, are epimorphisms**:
`f^{-1}M ⊗_{(f∘g)^{-1}𝒪_S} Ω^q_{X/S} ⟶ (f^{-1}M ⊗_{f^{-1}𝒪_Y} Ω^q_{X/Y})|`. The comparison of the
two inverse images has image generating `f^{-1}M` over `f^{-1}𝒪_Y` locally
(`Stacks.DeRhamSmooth.mem_localSpan_comparisonSections_coefficientPulledBackComparison`), so it
crosses the lax comparison as an epimorphism
(`AlgebraicGeometry.SheafOfModules.epi_tensorFunctor_map_comp_laxComparison`), and `q` is an
epimorphism (`Stacks.DeRhamSmooth.epi_deRhamFormsToRelativeHom_app`). -/
theorem epi_coefficientSummandToTarget (c : ℕ) (M : Modules Y.toRingedSpace) (q : ℕ) (n : ℤ)
    (h : n + -(c : ℤ) = (q : ℤ)) : Epi (coefficientSummandToTarget f g c M q n h) := by
  have e₁ := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
    (coefficientPulledBackComparison f g M)).naturality
      ((coefficientRestrictionToInverseImageBaseIso f g).inv.app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ)))
  have hL : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).map
      (coefficientPulledBackComparison f g M)).app
        ((coefficientRestriction f g).obj ((_root_.pushforward (toInverseImageBase f)).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ)))) ≫
      Stacks.SheafOfModules.TensorRestrictScalars.laxComparison
        ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)
        (inverseImageBase f).sheaf (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom)
        ((_root_.pullback (inverseImageBaseProjection f)).obj M)
        ((_root_.pushforward (toInverseImageBase f)).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ)))) := by
    refine Eq.mpr ?_ (AlgebraicGeometry.SheafOfModules.epi_tensorFunctor_map_comp_laxComparison
      (X := inverseImageBase f)
      (A := ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf))
      (φ := (baseStructureMap f.toLRSHom.toShHom g.toLRSHom.toShHom))
      (Q := (_root_.pullback (relativeBase f g)).obj
        ((_root_.pushforward (toInverseImageBase g)).obj M))
      (M := (_root_.pullback (inverseImageBaseProjection f)).obj M)
      (coefficientPulledBackComparison f g M) ((_root_.pushforward (toInverseImageBase f)).obj
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ)))
      (mem_localSpan_comparisonSections_coefficientPulledBackComparison f g M))
    kernel_rfl
  have hq : Epi (formsToRelativeCochain f g q) := by
    have := epi_deRhamFormsToRelativeHom_app f g q
    exact Functor.map_epi (_root_.pushforward (toInverseImageBase f)) _
  have h₄ : Epi ((coefficientRestriction f g).map
      (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
        ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map
          (formsToRelativeCochain f g q))) := by
    have h0 := @Stacks.SheafOfModules.TensorEncodings.epi_tensorSheafBifunctor_map _ _
      (Opens.grothendieckTopology X.carrier) _ _ _ (inverseImageBase f).sheaf _ _ _ _
      (𝟙 ((_root_.pullback (inverseImageBaseProjection f)).obj M)) (formsToRelativeCochain f g q)
      (@IsIso.epi_of_iso _ _ _ _ _ (IsIso.id _)) hq
    have : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
        ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map
          (formsToRelativeCochain f g q)) := @epi_of_epi _ _ _ _ _ _ _ h0
    exact Functor.map_epi (coefficientRestriction f g) _
  exact epi_comp5_of_square _ _ _ _ _ _ _ e₁.symm
    (Iso.isIso_hom (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).base).obj S.sheaf)).obj
        ((_root_.pullback (relativeBase f g)).obj
          ((_root_.pushforward (toInverseImageBase g)).obj M))).mapIso
      ((coefficientRestrictionToInverseImageBaseIso f g).app
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms (f ≫ g) ((q : ℕ) : ℤ))).symm))
    hL h₄
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _))

/-! ### The summands and the shift from the cut `c` to the cut `c + p` -/

/-- **The degreewise comparison of the target complex at the cut `k` and at the cut `k + p` agree
through `Stacks.DeRhamSmooth.coefficientTargetComplexShiftHom`**: both read the degree `n` term of
`f^{-1}M[-k] ⊗ Ω^•_{X/Y}` as `f^{-1}M ⊗ Ω^q_{X/Y}`. -/
theorem coefficientTargetXIso_inv_comp_shiftHom_f (k p : ℕ) (M : Modules Y.toRingedSpace)
    (q : ℕ) (n : ℤ) (h : n + -(k : ℤ) = (q : ℤ)) :
    (coefficientTargetXIso f g k M q n h).inv ≫
        (coefficientTargetComplexShiftHom f g k p M).f n =
      (coefficientTargetXIso f g (k + p) M q (n + (p : ℤ)) (by push_cast; omega)).inv := by
  rw [coefficientTargetXIso_inv_eq, coefficientTargetXIso_inv_eq]
  simp only [coefficientTargetComplexShiftHom, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, CochainComplex.shiftFunctorAdd'_hom_app_f',
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  have L1 : ∀ {a b : ℤ} (e : a = b),
      (HomologicalComplex.XIsoOfEq (V := Modules (inverseImageBase f))
        ((coefficientTargetTensor f).obj M) e).hom =
        ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map
          ((deRhamCochainComplex f).XIsoOfEq e).hom := by
    intro a b e
    subst e
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    exact (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map_id
            ((deRhamCochainComplex f).X a)).symm
  refine Eq.trans (congrArg (fun t => _ ≫ (coefficientRestriction f g).map t ≫ 𝟙 _)
    (L1 (show n + -(k : ℤ) = n + (p : ℤ) + -((k + p : ℕ) : ℤ) by push_cast; ring))) ?_
  refine Eq.trans (congrArg (fun t => _ ≫ t) (Category.comp_id _)) ?_
  refine Eq.trans ((coefficientRestriction f g).map_comp _ _).symm ?_
  refine congrArg (coefficientRestriction f g).map ?_
  refine Eq.trans (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map_comp _ _).symm ?_
  refine congrArg ((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
          ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map ?_
  simp only [Iso.trans_inv, Category.assoc]
  rw [HomologicalComplex.XIsoOfEq_inv_comp_XIsoOfEq_hom]
  rfl

/-- A composite of five morphisms followed by `s`, with the last factor and `s` combined. -/
theorem comp5_assoc_eq {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : C}
    (a₁ : A₀ ⟶ A₁) (a₂ : A₁ ⟶ A₂) (a₃ : A₂ ⟶ A₃) (a₄ : A₃ ⟶ A₄) (a₅ : A₄ ⟶ A₅) (s : A₅ ⟶ A₆)
    (a₅' : A₄ ⟶ A₆) (h : a₅ ≫ s = a₅') :
    (a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) ≫ s = a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅' := by
  simp only [Category.assoc, h]

/-- **The summands into the target complex at the cuts `k` and `k + p` agree through the shift.**
-/
theorem coefficientSummandToTarget_comp_shiftHom_f (k p : ℕ) (M : Modules Y.toRingedSpace)
    (q : ℕ) (n : ℤ) (h : n + -(k : ℤ) = (q : ℤ)) :
    coefficientSummandToTarget f g k M q n h ≫ (coefficientTargetComplexShiftHom f g k p M).f n =
      coefficientSummandToTarget f g (k + p) M q (n + (p : ℤ)) (by push_cast; omega) :=
  comp5_assoc_eq _ _ _ _ _ _ _ (coefficientTargetXIso_inv_comp_shiftHom_f f g k p M q n h)

/-- **`f^{-1}M[-c] ⊗ Ω^•_{X/Y}` is concentrated in degrees `≥ c`**, the de Rham complex being
concentrated in nonnegative degrees. -/
theorem isZero_coefficientTargetComplex_X (c : ℕ) (M : Modules Y.toRingedSpace) (n : ℤ)
    (hn : n < (c : ℤ)) : IsZero (((coefficientTargetComplex f g c).obj M).X n) :=
  (coefficientRestriction f g).map_isZero
    (((Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageBase f).sheaf).obj
        ((_root_.pullback (inverseImageBaseProjection f)).obj M)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE (deRhamCochainComplex f) 0 (n + -(c : ℤ))
        (by omega)))

end Stacks.DeRhamSmooth
