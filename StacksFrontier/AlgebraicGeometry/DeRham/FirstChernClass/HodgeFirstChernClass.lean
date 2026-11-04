module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DifferentialMap
public import StacksFrontier.AlgebraicGeometry.Picard.FirstCohomologyNaturality

/-!
# The first Chern class in Hodge cohomology

For a morphism of schemes `p : X ⟶ S` the logarithmic differential `d log u = u⁻¹ · d u` is a
morphism of sheaves of abelian groups `𝒪_X^* ⟶ Ω_{X/S}`, and composing the induced map on first
cohomology with the identification `Pic(X) = H¹(X, 𝒪_X^*)` of Stacks Tag 09NU gives the **Hodge
first Chern class**

`c₁^{Hodge} : Pic(X) ⟶ H¹(X, Ω_{X/S})`.

A commutative square of schemes with horizontal arrows `f : X' ⟶ X` and `g : S' ⟶ S` induces
`Ω_{X/S} ⟶ f_*Ω_{X'/S'}`, hence a pullback `H¹(X, Ω_{X/S}) ⟶ H¹(X', Ω_{X'/S'})` through the
first Leray edge map, and the Hodge first Chern class commutes with pullback.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.logarithmicDifferential`: `d log u = u⁻¹ · d u`, on invertible
  local sections of the structure sheaf.
* `AlgebraicGeometry.Scheme.Hom.logarithmicDifferentialSheafHom`: **logarithmic differentiation
  as a morphism of sheaves of abelian groups** `𝒪_X^* ⟶ Ω_{X/S}`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPushforwardMap`: the canonical morphism
  `Ω_{X/S} ⟶ f_*Ω_{X'/S'}` of a commutative square, the transpose of the canonical morphism
  `f^*Ω_{X/S} ⟶ Ω_{X'/S'}` of Stacks Tag 01UV.
* `AlgebraicGeometry.Scheme.Hom.hodgeCohomologyOne`: the Hodge cohomology group
  `H¹(X, Ω_{X/S})`.
* `AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass`: **the Hodge first Chern class**
  `c₁^{Hodge} : Pic(X) ⟶ H¹(X, Ω_{X/S})`.
* `AlgebraicGeometry.Scheme.Hom.hodgeCohomologyOnePullback`: pullback on `H¹(X, Ω_{X/S})` along a
  commutative square: the map induced by `Ω_{X/S} ⟶ f_*Ω_{X'/S'}` followed by the first Leray
  edge map.

## Main results

* `AlgebraicGeometry.Scheme.Hom.logarithmicDifferential_mul`:
  `d log (u v) = d log u + d log v`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPushforwardMap_logarithmicDifferential`:
  **logarithmic differentiation commutes with pullback**, on local sections.
* `AlgebraicGeometry.Scheme.Hom.logarithmicDifferentialSheafHom_naturality`: the same square, as
  an identity of morphisms of sheaves of abelian groups.
* `AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass_schemePullbackClassHom`: **the Hodge first
  Chern class commutes with pullback.**

## Implementation notes

Logarithmic differentiation is only additive, not `𝒪_X`-linear, so the first Chern class is
formed in sheaves of abelian groups; `Ω_{X/S}` enters through
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsAbelian`, its underlying sheaf of abelian
groups.

## References

* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.Generators (unitsSheaf)
open Stacks.Cohomology.LerayLowDegree (abelianCohomology abelianEdgeMap abelianPushforward)
open Stacks.GlueSquishUnits (unitsPushforwardMap unitsPushforwardMap_app)

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-! ### The logarithmic differential -/

section LogarithmicDifferential

variable {X S : Scheme.{u}} (p : X ⟶ S)

/-- **The logarithmic differential `d log u = u⁻¹ · d u`** of an invertible local section `u` of
the structure sheaf, as a local section of `Ω_{X/S}`. -/
def logarithmicDifferential (U : (X.Opens)ᵒᵖ) (u : (X.sheaf.obj.obj U)ˣ) :
    (relativeDifferentials p).val.obj U :=
  (u⁻¹).val • (universalRelativeDerivation p).d u.val

/-- **Logarithmic differentiation turns multiplication into addition**:
`d log (u v) = d log u + d log v`. -/
theorem logarithmicDifferential_mul (U : (X.Opens)ᵒᵖ) (u v : (X.sheaf.obj.obj U)ˣ) :
    logarithmicDifferential p U (u * v) =
      logarithmicDifferential p U u + logarithmicDifferential p U v := by
  have h : ∀ a b : (X.sheaf.obj.obj U)ˣ, ((a * b)⁻¹).val * a.val = (b⁻¹).val := fun a b =>
    congrArg Units.val (by simp [mul_comm] : (a * b)⁻¹ * a = b⁻¹)
  have h₂ := h v u
  rw [mul_comm v u] at h₂
  rw [logarithmicDifferential, logarithmicDifferential, logarithmicDifferential, Units.val_mul,
    (universalRelativeDerivation p).d_mul, smul_add, smul_smul, smul_smul, h, h₂, add_comm]

/-- `d log 1 = 0`. -/
theorem logarithmicDifferential_one (U : (X.Opens)ᵒᵖ) :
    logarithmicDifferential p U 1 = 0 := by
  rw [logarithmicDifferential, Units.val_one, (universalRelativeDerivation p).d_one U, smul_zero]

/-- **Logarithmic differentiation commutes with restriction.** -/
theorem logarithmicDifferential_map {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V)
    (u : (X.sheaf.obj.obj U)ˣ) :
    (relativeDifferentials p).val.map i (logarithmicDifferential p U u) =
      logarithmicDifferential p V (Units.map (X.sheaf.obj.map i).hom.toMonoidHom u) := by
  refine ((relativeDifferentials p).val.map_smul i (u⁻¹).val
    ((universalRelativeDerivation p).d u.val)).trans ?_
  exact congrArg (fun z => _ • z) ((universalRelativeDerivation p).d_map i u.val).symm

/-- `Ω_{X/S}`, read as a sheaf of abelian groups. -/
abbrev relativeDifferentialsAbelian :
    TopCat.Sheaf AddCommGrpCat.{u} X.toRingedSpace.toPresheafedSpace :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj (relativeDifferentials p)

/-- Logarithmic differentiation on the underlying presheaves: the additive map `u ↦ d log u` on
the units of each ring of local sections. -/
def logarithmicDifferentialPresheafHom :
    (unitsSheaf X.toRingedSpace).obj ⟶ (relativeDifferentialsAbelian p).obj where
  app U := AddCommGrpCat.ofHom
    { toFun := fun g => logarithmicDifferential p U (Additive.toMul g)
      map_zero' := logarithmicDifferential_one p U
      map_add' := fun g h => logarithmicDifferential_mul p U _ _ }
  naturality U V i := by
    ext g
    exact (logarithmicDifferential_map p i (Additive.toMul g)).symm

/-- **Logarithmic differentiation as a morphism of sheaves of abelian groups**
`𝒪_X^* ⟶ Ω_{X/S}`, the sheaf of units being written additively. -/
@[stacks 0FLE "d log into the sheaf of relative differentials"]
def logarithmicDifferentialSheafHom :
    unitsSheaf X.toRingedSpace ⟶ relativeDifferentialsAbelian p :=
  ObjectProperty.homMk (logarithmicDifferentialPresheafHom p)

/-- The sheaf morphism of logarithmic differentiation is `u ↦ u⁻¹ · d u` on local sections. -/
theorem logarithmicDifferentialSheafHom_app (U : (X.Opens)ᵒᵖ) (u : (X.sheaf.obj.obj U)ˣ) :
    (logarithmicDifferentialSheafHom p).hom.app U (Additive.ofMul u) =
      logarithmicDifferential p U u := rfl

end LogarithmicDifferential

/-! ### Pullback of relative differentials and of logarithmic differentials -/

section Pullback

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
  (hcomm : f ≫ p = p' ≫ g)

/-- The canonical morphism `Ω_{X/S} ⟶ f_*Ω_{X'/S'}` of a commutative square of schemes: the
transpose across the pullback-pushforward adjunction of the canonical morphism
`f^*Ω_{X/S} ⟶ Ω_{X'/S'}` of Stacks Tag 01UV. -/
def relativeDifferentialsPushforwardMap :
    relativeDifferentials p ⟶ (Scheme.Modules.pushforward f).obj (relativeDifferentials p') :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (relativeDifferentialsMap f p p' g hcomm)

/-- The canonical morphism `Ω_{X/S} ⟶ f_*Ω_{X'/S'}` carries the universal differential of a
local section of `𝒪_X` to the universal differential of its pullback along `f`. -/
theorem relativeDifferentialsPushforwardMap_d (U : X.Opens) (x : Γ(X, U)) :
    ((relativeDifferentialsPushforwardMap f p p' g hcomm).val.app (op U)).hom
        ((universalRelativeDerivation p).d x) =
      (universalRelativeDerivation p').d ((f.app U).hom x) :=
  relativeDifferentialsMap_app_d g hcomm U x

/-- **Logarithmic differentiation commutes with pullback**: the canonical morphism
`Ω_{X/S} ⟶ f_*Ω_{X'/S'}` carries `d log u` to `d log` of the pullback of `u`. -/
theorem relativeDifferentialsPushforwardMap_logarithmicDifferential (U : X.Opens)
    (u : (X.sheaf.obj.obj (op U))ˣ) :
    ((relativeDifferentialsPushforwardMap f p p' g hcomm).val.app (op U)).hom
        (logarithmicDifferential p (op U) u) =
      logarithmicDifferential p' (op (f ⁻¹ᵁ U)) (Units.map (f.app U).hom.toMonoidHom u) := by
  refine Eq.trans
    (((relativeDifferentialsPushforwardMap f p p' g hcomm).val.app (op U)).hom.map_smul
      (u⁻¹).val ((universalRelativeDerivation p).d u.val)) ?_
  exact congrArg (fun z => (u⁻¹ : (X.ringCatSheaf.obj.obj (op U))ˣ).val • z)
    (relativeDifferentialsPushforwardMap_d f p p' g hcomm U u.val)

/-- The canonical morphism `Ω_{X/S} ⟶ f_*Ω_{X'/S'}`, read in sheaves of abelian groups. -/
abbrev relativeDifferentialsPushforwardSheafHom :
    relativeDifferentialsAbelian p ⟶
      (abelianPushforward.{u, u} f.base).obj (relativeDifferentialsAbelian p') :=
  (SheafOfModules.toSheaf X.ringCatSheaf).map
    (relativeDifferentialsPushforwardMap f p p' g hcomm)

/-- **The square of sheaves of abelian groups expressing that `d log` commutes with pullback**:
pullback of units followed by `d log` on `X'` is `d log` on `X` followed by the canonical
morphism `Ω_{X/S} ⟶ f_*Ω_{X'/S'}`. -/
theorem logarithmicDifferentialSheafHom_naturality :
    unitsPushforwardMap f ≫
        (abelianPushforward.{u, u} f.base).map (logarithmicDifferentialSheafHom p') =
      logarithmicDifferentialSheafHom p ≫
        relativeDifferentialsPushforwardSheafHom f p p' g hcomm := by
  apply Sheaf.hom_ext
  ext U s
  obtain ⟨V⟩ := U
  obtain ⟨u, rfl⟩ : ∃ u : (X.sheaf.obj.obj (op V))ˣ, Additive.ofMul u = s := ⟨s, rfl⟩
  show (logarithmicDifferentialSheafHom p').hom.app (op (f ⁻¹ᵁ V))
      ((unitsPushforwardMap f).hom.app (op V) (Additive.ofMul u)) =
    ((relativeDifferentialsPushforwardMap f p p' g hcomm).val.app (op V)).hom
      ((logarithmicDifferentialSheafHom p).hom.app (op V) (Additive.ofMul u))
  rw [unitsPushforwardMap_app f V u]
  exact (relativeDifferentialsPushforwardMap_logarithmicDifferential f p p' g hcomm V u).symm

end Pullback

/-! ### The Hodge first Chern class -/

section HodgeFirstChernClass

/-- **The Hodge cohomology group `H¹(X, Ω_{X/S})`** of a morphism of schemes. -/
abbrev hodgeCohomologyOne {X S : Scheme.{u}} (p : X ⟶ S) : AddCommGrpCat.{u} :=
  (abelianCohomology.{u, u} _ ⊤ 1).obj (relativeDifferentialsAbelian p)

/-- **The first Chern class in Hodge cohomology** `c₁^{Hodge} : Pic(X) ⟶ H¹(X, Ω_{X/S})`: the
identification `Pic(X) = H¹(X, 𝒪_X^*)` of Stacks Tag 09NU followed by the map on first cohomology
induced by logarithmic differentiation. -/
@[stacks 0FLE "the Hodge first Chern class"]
def hodgeFirstChernClass {X S : Scheme.{u}} (p : X ⟶ S) :
    Stacks.Picard.ofScheme X →+ hodgeCohomologyOne p :=
  ((abelianCohomology.{u, u} _ ⊤ 1).map (logarithmicDifferentialSheafHom p)).hom.comp
    (Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X).symm.toAddMonoidHom

variable {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S)
  (hcomm : f ≫ p = p' ≫ g)

/-- **Pullback on Hodge cohomology** `H¹(X, Ω_{X/S}) ⟶ H¹(X', Ω_{X'/S'})` along a commutative
square of schemes: the map induced by the canonical morphism `Ω_{X/S} ⟶ f_*Ω_{X'/S'}`, followed
by the first Leray edge map. -/
def hodgeCohomologyOnePullback : hodgeCohomologyOne p ⟶ hodgeCohomologyOne p' :=
  (abelianCohomology.{u, u} _ ⊤ 1).map
      (relativeDifferentialsPushforwardSheafHom f p p' g hcomm) ≫
    (abelianEdgeMap.{u, u} f.base 1).app (relativeDifferentialsAbelian p')

/-- Pullback on first cohomology of the sheaf of units, followed by the map induced by `d log`
on `X'`, is `d log` on `X` followed by pullback on Hodge cohomology. -/
theorem hodgeCohomologyOnePullback_comp :
    (abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) ≫
        (abelianEdgeMap.{u, u} f.base 1).app (unitsSheaf X'.toRingedSpace) ≫
          (abelianCohomology.{u, u} _ ⊤ 1).map (logarithmicDifferentialSheafHom p') =
      (abelianCohomology.{u, u} _ ⊤ 1).map (logarithmicDifferentialSheafHom p) ≫
        hodgeCohomologyOnePullback f p p' g hcomm := by
  have hn := (abelianEdgeMap.{u, u} f.base 1).naturality (logarithmicDifferentialSheafHom p')
  have hsq := logarithmicDifferentialSheafHom_naturality f p p' g hcomm
  have hmap : (abelianCohomology.{u, u} _ ⊤ 1).map (unitsPushforwardMap f) ≫
        (abelianCohomology.{u, u} _ ⊤ 1).map
          ((abelianPushforward.{u, u} f.base).map (logarithmicDifferentialSheafHom p')) =
      (abelianCohomology.{u, u} _ ⊤ 1).map (logarithmicDifferentialSheafHom p) ≫
        (abelianCohomology.{u, u} _ ⊤ 1).map
          (relativeDifferentialsPushforwardSheafHom f p p' g hcomm) :=
    Eq.trans ((abelianCohomology.{u, u} _ ⊤ 1).map_comp _ _).symm
      (Eq.trans (congrArg (abelianCohomology.{u, u} _ ⊤ 1).map hsq)
        ((abelianCohomology.{u, u} _ ⊤ 1).map_comp _ _))
  refine Eq.trans (congrArg (fun m => (abelianCohomology.{u, u} _ ⊤ 1).map
    (unitsPushforwardMap f) ≫ m) hn.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun m => m ≫ (abelianEdgeMap.{u, u} f.base 1).app
    (relativeDifferentialsAbelian p')) hmap) ?_
  exact Category.assoc _ _ _

/-- **The Hodge first Chern class commutes with pullback**: for a commutative square of schemes
with horizontal arrows `f : X' ⟶ X` and `g : S' ⟶ S`, the square formed by `c₁^{Hodge}`, by
pullback of Picard classes and by pullback on `H¹(-, Ω)` commutes. -/
@[stacks 0FMD "the Hodge square"]
theorem hodgeFirstChernClass_schemePullbackClassHom (c : Stacks.Picard.ofScheme X) :
    hodgeFirstChernClass p' (Stacks.Picard.schemePullbackClassHom f c) =
      (hodgeCohomologyOnePullback f p p' g hcomm).hom (hodgeFirstChernClass p c) := by
  obtain ⟨x, rfl⟩ : ∃ x, Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X x = c :=
    ⟨_, (Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X).apply_symm_apply c⟩
  have hnat := Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_naturality f x
  have happ := ConcreteCategory.congr_hom
    (hodgeCohomologyOnePullback_comp f p p' g hcomm) x
  simp only [ConcreteCategory.comp_apply] at happ
  rw [← hnat]
  simp only [hodgeFirstChernClass, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply]
  exact happ

end HodgeFirstChernClass

end AlgebraicGeometry.Scheme.Hom

end
