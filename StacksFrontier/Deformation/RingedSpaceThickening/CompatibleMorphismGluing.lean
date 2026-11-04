module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSections
public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismPresentation

/-!
# Gluing a compatible morphism of thickenings from a factorization

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces, let
`𝒪_{X'}` be a square-zero extension of `f⁻¹𝒪_S`-algebras of `𝒪_X` by `ℱ` and `𝒪_{Y'}` one of
`(g ∘ f)⁻¹𝒪_S`-algebras of `𝒪_Y` by `𝒢`, and let `c : ℱ ⟶ g_*𝒢` be a `g`-map. Present `𝒪_X` by
the sheaf of sets underlying `𝒪_{X'}` and `𝒪_Y` by the one underlying `𝒪_{Y'}` (Stacks 0GQ0).

The fibre product `N = g^*𝖭𝖫(α_X) ×_{𝖭𝖫_{Y/S}} 𝖭𝖫(α_Y)`, taken termwise along the canonical map
`g^*𝖭𝖫(α_X) ⟶ g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}` and the comparison `𝖭𝖫(α_Y) ⟶ 𝖭𝖫_{Y/S}`, carries the
difference `Δ` of the two conormal homomorphisms, `c ∘ g^*(𝒥_X/𝒥_X² ⟶ ℱ)` and
`𝒥_Y/𝒥_Y² ⟶ 𝒢`. This file constructs `N`, its differential `d_N` and the homomorphism `Δ`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.LiftGluing.N₀`, `N₁`, `dN`: the two terms of `N` and
  its differential.
* `AlgebraicGeometry.RingedSpaceThickening.LiftGluing.Δ`: the difference homomorphism
  `N₀ ⟶ 𝒢`.

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal conormalClass tensorDifferential)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf freeAlgebraSheafDesc
  freeAlgebraSheafVariable freeAlgebraSheafCoefficientMap)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening.LiftGluing

variable {X S Y : RingedSpace.{u, u}} {f : X ⟶ S} (g : Y ⟶ X)
  {F : SheafOfModules.{u} (structureSheafRing X)} {G : SheafOfModules.{u} (structureSheafRing Y)}
  (P : SquareZeroAlgebraExtension f F) (Q : SquareZeroAlgebraExtension (g ≫ f) G)
  (c : F ⟶ (modulePushforward g).obj G)

/-! ### The terms -/

/-- The conormal sequence of the presentation of `𝒪_X` by `𝒪_{X'}`. -/
abbrev seqX :=
  Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    P.generators P.generatorsMap

/-- The conormal sequence of the presentation of `𝒪_Y` by `𝒪_{Y'}`. -/
abbrev seqβ :=
  Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap

/-- The conormal sequence of the canonical presentation of `𝒪_Y`. -/
abbrev seqY (f : X ⟶ S) (g : Y ⟶ X) :=
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
      (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology Y.carrier)
        (inverseImageBaseRing (g ≫ f)) Y.sheaf (structureRingMap (g ≫ f))
        (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)).hom :=
    Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _
  Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)

/-- The canonical presentation of `𝒪_Y` is locally surjective. -/
instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y.carrier)
    (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology Y.carrier)
      (inverseImageBaseRing (g ≫ f)) Y.sheaf (structureRingMap (g ≫ f))
      (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

/-- The canonical presentation of `𝒪_X` is locally surjective. -/
instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (Stacks.SheafOfModules.presentation (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) X.sheaf (structureRingMap f)
      (X.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)).hom :=
  Stacks.SheafOfModules.presentation_id_isLocallySurjective _ _ _ _

/-- `𝒥_X/𝒥_X²`, as a sheaf of modules over the structure sheaf. -/
def cX : SheafOfModules.{u} (structureSheafRing X) := (seqX P).X₁

/-- `𝛺_X`, as a sheaf of modules over the structure sheaf. -/
def bX : SheafOfModules.{u} (structureSheafRing X) := (seqX P).X₂

/-- `𝒥_Y/𝒥_Y²` of the canonical presentation, as a sheaf of modules over the structure sheaf. -/
def cY (f : X ⟶ S) (g : Y ⟶ X) : SheafOfModules.{u} (structureSheafRing Y) := (seqY f g).X₁

/-- `𝛺_Y` of the canonical presentation, as a sheaf of modules over the structure sheaf. -/
def bY (f : X ⟶ S) (g : Y ⟶ X) : SheafOfModules.{u} (structureSheafRing Y) := (seqY f g).X₂

/-- `𝒥_β/𝒥_β²`, as a sheaf of modules over the structure sheaf. -/
def cβ : SheafOfModules.{u} (structureSheafRing Y) := (seqβ g Q).X₁

/-- `𝛺_β`, as a sheaf of modules over the structure sheaf. -/
def bβ : SheafOfModules.{u} (structureSheafRing Y) := (seqβ g Q).X₂

/-- The generators of `𝒪_X` by `𝒪_{X'}`, sent along `g`: `s ↦ g^♯(s mod ℱ)`. -/
abbrev εX : P.generators ⟶ (Opens.map g.hom.base).op ⋙ (Y.sheaf.obj ⋙ forget CommRingCat) :=
  P.generatorsMap ≫ Functor.whiskerRight (structureComorphism g).hom (forget CommRingCat.{u})

/-- `εX` followed by the identity of `𝒪_Y`, restricted along `g`, is `s ↦ g^♯(s mod ℱ)`. -/
theorem εX_comp : εX g P ≫ Functor.whiskerLeft (Opens.map g.hom.base).op
    (𝟙 (Y.sheaf.obj ⋙ forget CommRingCat)) =
      P.generatorsMap ≫ Functor.whiskerRight (structureComorphism g).hom
        (forget CommRingCat.{u}) :=
  Category.comp_id _

/-- The map `𝒥_X/𝒥_X² ⟶ g_*(𝒥_Y/𝒥_Y²)` of conormal sheaves, from the presentation of `𝒪_X` by
`𝒪_{X'}` along `g` to the canonical presentation of `𝒪_Y`. -/
def ψpush₀ : (seqX P).X₁ ⟶ (SheafOfModules.pushforward.{u}
    (Stacks.Sites.Conormal.pushforwardRingHom g.hom.base (structureComorphism g))).obj
      (seqY f g).X₁ :=
  Stacks.SheafOfModules.presentationConormalPushMap g.hom.base
    (structureRingMap_comp_structureComorphism g f) (εX_comp g P)

/-- The map `𝛺_X ⟶ g_*𝛺_Y` of degree `0` terms. -/
def ψpush₁ : (seqX P).X₂ ⟶ (SheafOfModules.pushforward.{u}
    (Stacks.Sites.Conormal.pushforwardRingHom g.hom.base (structureComorphism g))).obj
      (seqY f g).X₂ :=
  Stacks.SheafOfModules.presentationTensorPushMap g.hom.base
    (structureRingMap_comp_structureComorphism g f) (εX_comp g P)

/-- The transposed map `g^*(𝒥_X/𝒥_X²) ⟶ 𝒥_Y/𝒥_Y²`. -/
def ψ₀ : (modulePullback g).obj (cX P) ⟶
    (cY f g) :=
  ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm (ψpush₀ g P)

/-- The transposed map `g^*𝛺_X ⟶ 𝛺_Y`. -/
def ψ₁ : (modulePullback g).obj (bX P) ⟶
    (bY f g) :=
  ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm (ψpush₁ g P)

/-- The comparison `𝒥_β/𝒥_β² ⟶ 𝒥_Y/𝒥_Y²` of the presentation of `𝒪_Y` by `𝒪_{Y'}`. -/
def ιβ₀ : (cβ g Q) ⟶
    (cY f g) :=
  Stacks.SheafOfModules.presentationConormalMap.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.generators
    (Y.sheaf.obj ⋙ forget CommRingCat) Q.generatorsMap Y.sheaf (structureRingMap (g ≫ f))
    Q.generatorsMap (𝟙 _) (Category.comp_id _)

/-- The comparison `𝛺_β ⟶ 𝛺_Y`. -/
def ιβ₁ : (bβ g Q) ⟶
    (bY f g) :=
  Stacks.SheafOfModules.presentationTensorMap.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.generators
    (Y.sheaf.obj ⋙ forget CommRingCat) Q.generatorsMap Y.sheaf (structureRingMap (g ≫ f))
    Q.generatorsMap (𝟙 _) (Category.comp_id _)

/-! ### Sections of a pullback along the unit -/

section Unit

/-- The unit `M ⟶ g_*g^*M`, on sections over `U`. -/
abbrev unitSec (M : SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier) :
    M.val.obj (op U) → ((modulePullback g).obj M).val.obj (op ((Opens.map g.hom.base).obj U)) :=
  fun m ↦ ((modulePullbackPushforwardAdjunction g).unit.app M).val.app (op U) m

/-- The transpose of `φ : M ⟶ g_*N`, at the image of a section under the unit, is `φ`. -/
theorem homEquiv_symm_unitSec {M : SheafOfModules.{u} (structureSheafRing X)}
    {N : SheafOfModules.{u} (structureSheafRing Y)} (φ : M ⟶ (modulePushforward g).obj N)
    (U : Opens X.carrier) (m : M.val.obj (op U)) :
    (((modulePullbackPushforwardAdjunction g).homEquiv M N).symm φ).val.app _
        (unitSec g M U m) = φ.val.app (op U) m := by
  conv_rhs => rw [← ((modulePullbackPushforwardAdjunction g).homEquiv M N).apply_symm_apply φ]
  rw [Adjunction.homEquiv_unit]
  rfl

/-- The unit is natural. -/
theorem map_unitSec {M M' : SheafOfModules.{u} (structureSheafRing X)} (φ : M ⟶ M')
    (U : Opens X.carrier) (m : M.val.obj (op U)) :
    ((modulePullback g).map φ).val.app _ (unitSec g M U m) = unitSec g M' U (φ.val.app (op U) m) :=
  (congrArg (fun t : M ⟶ (modulePushforward g).obj ((modulePullback g).obj M') ↦
    t.val.app (op U) m) ((modulePullbackPushforwardAdjunction g).unit.naturality φ)).symm

/-- The unit on sections is additive. -/
theorem unitSec_add (M : SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier)
    (m m' : M.val.obj (op U)) : unitSec g M U (m + m') = unitSec g M U m + unitSec g M U m' :=
  map_add _ _ _

/-- The unit on sections preserves subtraction. -/
theorem unitSec_sub (M : SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier)
    (m m' : M.val.obj (op U)) : unitSec g M U (m - m') = unitSec g M U m - unitSec g M U m' :=
  map_sub _ _ _

/-- The unit on sections is semilinear along `g^♯ : 𝒪_X(U) ⟶ 𝒪_Y(g⁻¹U)`. -/
theorem unitSec_smul (M : SheafOfModules.{u} (structureSheafRing X)) (U : Opens X.carrier)
    (r : (structureSheafRing X).obj.obj (op U)) (m : M.val.obj (op U)) :
    unitSec g M U (r • m) =
      (show (structureSheafRing Y).obj.obj (op ((Opens.map g.hom.base).obj U)) from
        (g.hom.c.app (op U)).hom r) • unitSec g M U m :=
  ((((modulePullbackPushforwardAdjunction g).unit.app M).val.app (op U)).hom.map_smul r m)

end Unit

/-! ### The comparison ring maps -/

section Rings

/-- The polynomial algebra presenting `𝒪_X` by `𝒪_{X'}`. -/
abbrev FX := freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
  P.generators

/-- The polynomial algebra presenting `𝒪_Y` by `𝒪_{Y'}`. -/
abbrev Fβ := freeAlgebraSheaf (Opens.grothendieckTopology Y.carrier)
  (inverseImageBaseRing (g ≫ f)) Q.generators

variable (f) in
/-- The canonical polynomial algebra presenting `𝒪_Y`. -/
abbrev FY := freeAlgebraSheaf (Opens.grothendieckTopology Y.carrier)
  (inverseImageBaseRing (g ≫ f)) (Y.sheaf.obj ⋙ forget CommRingCat)

/-- The ring map `f⁻¹𝒪_S[𝒪_{X'}] ⟶ g_*(g ∘ f)⁻¹𝒪_S[𝒪_Y]`: `[s] ↦ [g^♯ s̄]`. -/
abbrev ΦX : FX P ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj (FY f g) :=
  Stacks.SheafOfModules.freeAlgebraPushMap g.hom.base (inverseImageBaseRing f) P.generators
    (inverseImageBaseRing (g ≫ f)) (Y.sheaf.obj ⋙ forget CommRingCat) (baseRingPushMap g f)
    (εX g P)

/-- The ring map `(g ∘ f)⁻¹𝒪_S[𝒪_{Y'}] ⟶ (g ∘ f)⁻¹𝒪_S[𝒪_Y]`: `[e] ↦ [ē]`. -/
abbrev Φβ : Fβ g Q ⟶ FY f g :=
  Stacks.SheafOfModules.freeAlgebraMap (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) Q.generators (Y.sheaf.obj ⋙ forget CommRingCat)
    Q.generatorsMap

end Rings

/-! ### The maps on local conormal classes and differentials -/

section Evaluation

variable (f) in
/-- The canonical presentation of `𝒪_Y`. -/
abbrev presY := Stacks.SheafOfModules.presentation (Opens.grothendieckTopology Y.carrier)
  (inverseImageBaseRing (g ≫ f)) Y.sheaf (structureRingMap (g ≫ f))
  (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)

/-- `ΦX` lies over `g^♯`. -/
theorem ΦX_comp_presY : ΦX g P ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).map
    (presY f g) = P.presentation ≫ structureComorphism g :=
  Stacks.SheafOfModules.freeAlgebraPushMap_comp_presentation g.hom.base
    (structureRingMap_comp_structureComorphism g f) (εX_comp g P)

/-- `Φβ` lies over `𝒪_Y`. -/
theorem Φβ_comp_presY : Φβ g Q ≫ presY f g = Q.presentation :=
  Stacks.SheafOfModules.freeAlgebraMap_comp_presentation _ _ _ _ _ Y.sheaf
    (structureRingMap (g ≫ f)) _ _ (Category.comp_id _)

/-- The image under the unit of the local conormal class of a relation of `α_X`. -/
def unitClassX (U : Opens X.carrier) (x : kernelIdeal P.presentation.hom (op U)) :
    ((modulePullback g).obj (cX P)).val.obj (op ((Opens.map g.hom.base).obj U)) :=
  unitSec g (cX P) U
    (conormalClass.{u, u, u, u} (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
      (FX P) X.sheaf (freeAlgebraSheafCoefficientMap _ _ _) P.presentation (op U) x)

/-- The local conormal class, for the canonical presentation of `𝒪_Y`, of the image under `ΦX`
of a relation of `α_X`. -/
def pushClassY (U : Opens X.carrier) (x : kernelIdeal P.presentation.hom (op U)) :
    (cY f g).val.obj
      (op ((Opens.map g.hom.base).obj U)) :=
  conormalClass.{u, u, u, u} (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) (FY f g) Y.sheaf (freeAlgebraSheafCoefficientMap _ _ _)
    (presY f g) (op ((Opens.map g.hom.base).obj U))
    ⟨((ΦX g P).hom.app (op U)).hom x.1, Stacks.Sites.Conormal.kernelIdeal_le_comap_sectionsMapPush
      g.hom.base X.sheaf Y.sheaf (structureComorphism g) P.presentation (presY f g) (ΦX g P)
      (ΦX_comp_presY g P) (op U) x.2⟩

/-- `ψ₀` on the image under the unit of a local conormal class. -/
theorem ψ₀_unitClassX (U : Opens X.carrier) (x : kernelIdeal P.presentation.hom (op U)) :
    (ψ₀ g P).val.app _ (unitClassX g P U x) = pushClassY g P U x :=
  (homEquiv_symm_unitSec g (ψpush₀ g P) U _).trans
    (Stacks.Sites.Conormal.conormalSheafMapPush_conormalClass g.hom.base X.sheaf Y.sheaf
      (structureComorphism g) P.presentation (presY f g) (ΦX g P) (ΦX_comp_presY g P)
      (inverseImageBaseRing f) (inverseImageBaseRing (g ≫ f))
      (freeAlgebraSheafCoefficientMap _ _ _) (freeAlgebraSheafCoefficientMap _ _ _) (op U) x)

/-- The image under the unit of the local differential `1 ⊗ d z` of the presentation of `𝒪_X`. -/
def unitDiffX (U : Opens X.carrier) (z : (FX P).obj.obj (op U)) :
    ((modulePullback g).obj (bX P)).val.obj (op ((Opens.map g.hom.base).obj U)) :=
  unitSec g (bX P) U
    (tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (FX P) X.sheaf (freeAlgebraSheafCoefficientMap _ _ _)
      P.presentation (op U) z)

/-- A local conormal class of the canonical presentation of `𝒪_Y`. -/
def classY (V : (Opens Y.carrier)ᵒᵖ) (z : kernelIdeal (presY f g).hom V) :
    (cY f g).val.obj V :=
  conormalClass.{u, u, u, u} (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) (FY f g) Y.sheaf (freeAlgebraSheafCoefficientMap _ _ _)
    (presY f g) V z

/-- A local differential `1 ⊗ d z` of the canonical presentation of `𝒪_Y`. -/
def diffY (V : (Opens Y.carrier)ᵒᵖ) (z : (FY f g).obj.obj V) :
    (bY f g).val.obj V :=
  tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) (FY f g) Y.sheaf (freeAlgebraSheafCoefficientMap _ _ _)
    (presY f g) V z

/-- A local conormal class of the presentation of `𝒪_Y` by `𝒪_{Y'}`. -/
def classβ (V : (Opens Y.carrier)ᵒᵖ) (z : kernelIdeal Q.presentation.hom V) :
    (cβ g Q).val.obj V :=
  conormalClass.{u, u, u, u} (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) (Fβ g Q) Y.sheaf (freeAlgebraSheafCoefficientMap _ _ _)
    Q.presentation V z

/-- A local differential `1 ⊗ d z` of the presentation of `𝒪_Y` by `𝒪_{Y'}`. -/
def diffβ (V : (Opens Y.carrier)ᵒᵖ) (z : (Fβ g Q).obj.obj V) :
    (bβ g Q).val.obj V :=
  tensorDifferential.{u, u, u, u} (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing (g ≫ f)) (Fβ g Q) Y.sheaf (freeAlgebraSheafCoefficientMap _ _ _)
    Q.presentation V z

/-- `ψ₁` on the image under the unit of a local differential. -/
theorem ψ₁_unitDiffX (U : Opens X.carrier) (z : (FX P).obj.obj (op U)) :
    (ψ₁ g P).val.app _ (unitDiffX g P U z) =
      diffY g (op ((Opens.map g.hom.base).obj U)) (((ΦX g P).hom.app (op U)).hom z) := by
  have h1 := homEquiv_symm_unitSec g (ψpush₁ g P) U (tensorDifferential.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) (FX P) X.sheaf
    (freeAlgebraSheafCoefficientMap _ _ _) P.presentation (op U) z)
  have h2 := Stacks.Sites.Conormal.tensorSheafMapPush_tensorDifferential g.hom.base X.sheaf Y.sheaf
      (structureComorphism g) P.presentation (presY f g) (ΦX g P) (ΦX_comp_presY g P)
      (inverseImageBaseRing f) (inverseImageBaseRing (g ≫ f))
      (freeAlgebraSheafCoefficientMap _ _ _) (freeAlgebraSheafCoefficientMap _ _ _)
      (baseRingPushMap g f) (Stacks.SheafOfModules.freeAlgebraPushMap_coefficient g.hom.base
        (structureRingMap_comp_structureComorphism g f)) (op U) z
  unfold diffY ψ₁ unitDiffX
  exact h1.trans h2

/-- `ιβ₀` on a local conormal class. -/
theorem ιβ₀_classβ (V : (Opens Y.carrier)ᵒᵖ) (y : kernelIdeal Q.presentation.hom V) :
    (ιβ₀ g Q).val.app V (classβ g Q V y) =
      classY g V ⟨((Φβ g Q).hom.app V).hom y.1, Stacks.Sites.Conormal.kernelIdeal_le_comap
        Q.presentation.hom (presY f g).hom (Φβ g Q).hom
        (Stacks.Sites.Conormal.hom_of_comp_eq (Φβ_comp_presY g Q)) V y.2⟩ := by
  have h := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf (Fβ g Q) (FY f g)
    (freeAlgebraSheafCoefficientMap _ _ _) (freeAlgebraSheafCoefficientMap _ _ _)
    Q.presentation (presY f g) (Φβ g Q) (Φβ_comp_presY g Q) V y
  unfold classY classβ ιβ₀
  exact h

/-- `ιβ₁` on a local differential. -/
theorem ιβ₁_diffβ (V : (Opens Y.carrier)ᵒᵖ) (z : (Fβ g Q).obj.obj V) :
    (ιβ₁ g Q).val.app V (diffβ g Q V z) = diffY g V (((Φβ g Q).hom.app V).hom z) := by
  have h := Stacks.Sites.Conormal.tensorSheafMapOfFac_tensorDifferential.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf (Fβ g Q)
    (FY f g) (freeAlgebraSheafCoefficientMap _ _ _) (freeAlgebraSheafCoefficientMap _ _ _)
    Q.presentation (presY f g) (Φβ g Q) (Φβ_comp_presY g Q)
    (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap _ _ _ _ _) V z
  unfold diffβ diffY ιβ₁
  exact h

end Evaluation

/-- The degree `-1` term of `N`. -/
abbrev N₀ := pullback (ψ₀ g P) (ιβ₀ g Q)

/-- The degree `0` term of `N`. -/
abbrev N₁ := pullback (ψ₁ g P) (ιβ₁ g Q)

/-! ### The differential of `N` -/

section Differential

/-- The differential `𝒥_X/𝒥_X² ⟶ 𝛺_X`. -/
def dX : (cX P) ⟶
    (bX P) :=
  (seqX P).f

/-- The differential `𝒥_Y/𝒥_Y² ⟶ 𝛺_Y`. -/
def dY : (cY f g) ⟶
    (bY f g) :=
  (seqY f g).f

/-- The differential `𝒥_β/𝒥_β² ⟶ 𝛺_β`. -/
def dβ : (cβ g Q) ⟶
    (bβ g Q) :=
  (seqβ g Q).f

/-- `ψpush₀` and `ψpush₁` commute with the differentials `𝒥_X/𝒥_X² ⟶ 𝛺_X` and
`g_*(𝒥_Y/𝒥_Y²) ⟶ g_*𝛺_Y`. -/
theorem ψpush_comm : dX P ≫ ψpush₁ g P = ψpush₀ g P ≫
    (SheafOfModules.pushforward.{u} (Stacks.Sites.Conormal.pushforwardRingHom g.hom.base
      (structureComorphism g))).map (seqY f g).f := by
  have h := Stacks.Sites.Conormal.conormalSequence_f_naturality_push g.hom.base X.sheaf Y.sheaf
    (structureComorphism g) P.presentation (presY f g) (ΦX g P) (ΦX_comp_presY g P)
    (inverseImageBaseRing f) (inverseImageBaseRing (g ≫ f))
    (freeAlgebraSheafCoefficientMap _ _ _) (freeAlgebraSheafCoefficientMap _ _ _)
    (baseRingPushMap g f) (Stacks.SheafOfModules.freeAlgebraPushMap_coefficient g.hom.base
      (structureRingMap_comp_structureComorphism g f))
  unfold dX ψpush₁ ψpush₀
  exact h

/-- `ψ₀` and `ψ₁` commute with the differentials `g^*dX` and `dY`. -/
theorem ψ_comm : (modulePullback g).map (dX P) ≫ ψ₁ g P = ψ₀ g P ≫ dY g := by
  apply ((modulePullbackPushforwardAdjunction g).homEquiv _ _).injective
  refine ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_left _ _).trans ?_
  refine Eq.trans ?_ ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_right _ _).symm
  refine (congrArg (dX P ≫ ·) (((modulePullbackPushforwardAdjunction g).homEquiv _
    _).apply_symm_apply _)).trans ?_
  refine (ψpush_comm g P).trans ?_
  exact congrArg (· ≫ _) (((modulePullbackPushforwardAdjunction g).homEquiv _
    _).apply_symm_apply _).symm

/-- `ιβ₀` and `ιβ₁` commute with the differentials `dβ` and `dY`. -/
theorem ιβ_comm : dβ g Q ≫ ιβ₁ g Q = ιβ₀ g Q ≫ dY g := by
  have h := Stacks.Sites.Conormal.conormalSequence_f_naturality.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf (Fβ g Q)
    (FY f g) (freeAlgebraSheafCoefficientMap _ _ _) (freeAlgebraSheafCoefficientMap _ _ _)
    Q.presentation (presY f g) (Φβ g Q) (Φβ_comp_presY g Q)
    (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap _ _ _ _ _)
  unfold dβ ιβ₁ ιβ₀ dY
  exact h

/-- The differential `N₀ ⟶ N₁` of `N`. -/
def dN : N₀ g P Q ⟶ N₁ g P Q :=
  pullback.lift (pullback.fst _ _ ≫ (modulePullback g).map (dX P)) (pullback.snd _ _ ≫ dβ g Q)
    (by rw [Category.assoc, ψ_comm, ← Category.assoc, pullback.condition, Category.assoc,
      ← ιβ_comm, Category.assoc])

end Differential

/-! ### The difference homomorphism -/

section Difference

/-- The homomorphism `𝒥_X/𝒥_X² ⟶ ℱ` of `𝒪_{X'}` (Stacks 0GQ0). -/
def δX : (cX P) ⟶ F :=
  P.conormalToIdeal

/-- The homomorphism `𝒥_β/𝒥_β² ⟶ 𝒢` of `𝒪_{Y'}` (Stacks 0GQ0). -/
def δβ : (cβ g Q) ⟶ G :=
  Q.conormalToIdeal

/-- The adjoint transpose `g^*ℱ ⟶ 𝒢` of the `g`-map `c`. -/
def cAdj : (modulePullback g).obj F ⟶ G :=
  ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm c

/-- **The difference homomorphism** `N₀ ⟶ 𝒢`: on a pair `(a, b)` it is
`c(δ_X a) - δ_β b`. -/
def Δ : N₀ g P Q ⟶ G :=
  pullback.fst _ _ ≫ (modulePullback g).map (δX P) ≫ cAdj g c - pullback.snd _ _ ≫ δβ g Q

end Difference

end AlgebraicGeometry.RingedSpaceThickening.LiftGluing

end
