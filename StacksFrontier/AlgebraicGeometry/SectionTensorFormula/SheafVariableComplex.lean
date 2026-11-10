module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormulaLeft
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.AffineOpen
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Naturality of the section formula in the sheaf variable, and the complex-level formula

`Stacks.SectionTensorFormula.tensorSectionEquiv` is the section formula for a tensor product over
an **affine** open: for `F G : X.Modules` quasi-coherent and `V` an affine open it is a
`Γ(X, V)`-linear equivalence `Γ(F, V) ⊗_{Γ(X, V)} Γ(G, V) ≅ Γ(F ⊗ G, V)`. It was known to be
natural in the *open*, by `Stacks.SectionTensorFormula.map_tensorSection`, and natural in its
*second sheaf variable*, by `Stacks.SectionTensorFormula.toTensorSection_comp_whiskerLeft_val`.
Naturality in its **first** sheaf variable was missing, and that is the direction a *complex*
needs: the differential of a complex `E` acts on the left-hand factor, so the components of the
section formula are a chain map against `E.d i j ▷ M` only once the first-variable square is
available. This file proves that square and assembles the complex-level statement from it.

## Main definitions

* `Stacks.SectionTensorFormula.tensorComplex`: the complex of `𝒪_X`-modules with objects
  `E.X i ⊗ M` and differentials `E.d i j ▷ M` — the degreewise tensor product of a complex with a
  fixed module. It did not exist, because `d ≫ d = 0` for it needs `0 ▷ M = 0`, which the
  localized monoidal structure on sheaves of modules carries no additivity for; see
  `zero_whiskerRight`.
* `Stacks.SectionTensorFormula.tensorSectionsComplex`: its sections over an open, as a complex in
  `ModuleCat Γ(X, V)`: objects `Γ(E.X i ⊗ M, V)`, differentials `Γ(E.d i j ▷ M, V)`.
* `Stacks.SectionTensorFormula.sectionsTensorComplex`: the complex in `ModuleCat Γ(X, V)` with
  objects `Γ(E.X i, V) ⊗_{Γ(X, V)} Γ(M, V)` and differentials `Γ(E.d i j, V) ⊗ 𝟙`, i.e. the
  degreewise tensor product of the complex of sections of `E` with the module of sections of `M`.
  Pure algebra.

## Main results

* `Stacks.SectionTensorFormula.toTensorSection_comp_tensorHom_val`: **naturality of the
  comparison on sections** in both sheaf variables at once, from the first-variable naturality
  `Stacks.SectionTensorFormula.toTensorSection_comp_whiskerRight_val` of
  `StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormulaLeft.lean`
  (itself resting on `Stacks.SectionTensorFormula.tensorSheafIsoTensorObj_hom_whiskerRight`
  there) and the second-variable one.
* `Stacks.SectionTensorFormula.tensorSection_whiskerLeft`: the same on an element, over a scheme,
  in the second variable; the first-variable form
  `(f ▷ G).app U (m ⊗ₛ n) = (f.app U m) ⊗ₛ n` is
  `Stacks.SectionTensorFormula.tensorSection_whiskerRight` of
  `StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormulaLeft.lean`.
* `Stacks.SectionTensorFormula.zero_whiskerRight`: **tensoring a zero morphism of sheaves of
  modules with a fixed sheaf gives zero**, for the localized monoidal structure, on any ringed
  site. Deduced from the first-variable naturality together with
  `presheaf_zero_whiskerRight` and `sheafify_map_zero`. This is what makes `tensorComplex` a
  complex.
* `Stacks.SectionTensorFormula.tensorSectionEquiv_whiskerRight` and
  `Stacks.SectionTensorFormula.tensorSectionEquiv_whiskerLeft`: **naturality of the affine section
  formula in the sheaf variable**, and `tensorSectionIso_hom_comp_whiskerRight` the same as a
  commuting square in `ModuleCat Γ(X, V)`.
* `Stacks.SectionTensorFormula.sectionsTensorComplexIso`: **the complex-level section formula.**
  Over an affine open `V`, `sectionsTensorComplex E M V ≅ tensorSectionsComplex E M V`, the
  components being `tensorSectionIso`. This is the statement
  `Γ(V, Eⁱ ⊗ M) ≅ Γ(V, Eⁱ) ⊗_{Γ(X, V)} Γ(V, M)` *as a complex*.

## Implementation notes

**Where additivity of `- ⊗ M` comes from.** The differentials of `tensorComplex` compose to
`(E.d i j ≫ E.d j k) ▷ M = 0 ▷ M`, and `0 ▷ M = 0` is not available: the monoidal structure of
`Stacks.SheafInternalHom.monoidalCategory` is a localization of the sectionwise one and carries no
`MonoidalPreadditive` instance in this repository. The first-variable naturality proved here
transports the question across `tensorSheafIsoTensorObj` to the sheafified sectionwise tensor
product, where it splits into two facts that *are* reachable: `0 ▷ R = 0` for presheaves of
modules, which is `ModuleCat`'s own `MonoidalPreadditive.zero_whiskerRight` read sectionwise, and
`sheafify.map 0 = 0`, which the hom-equivalence of the sheafification adjunction gives since
sheafification is not known here to be an additive functor. So no affineness and no
quasi-coherence are used for the complexes; they enter only in the isomorphism, where
`tensorSectionEquiv` lives.

**Why the element-level lemmas are stated twice.** At the scheme level `F.val ⊗ G.val` does not
elaborate: the monoidal structure on presheaves of modules is declared over
`PresheafOfModules (structureSheaf 𝒪 h𝒪).obj`, and `X.Modules` presents its underlying presheaves
over `X.ringCatSheaf.obj`, a spelling instance search does not see through. So
`toTensorSection_whiskerRight_apply` is stated in the general ringed-site section, where the type
ascription needed by `congrArg` is writable, and the scheme-level `tensorSection_whiskerRight` is
an `exact` of it — the two types being definitionally equal, which `exact` checks and `rw` would
not. This is the technique of
`StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormula.lean`.

For the same reason, `(tensorComplex E M).d i j` is **not** `rw`-visible as
`E.d i j ▷ M`, so `tensorSectionsComplex` proves its own `shape` and `d_comp_d'` from
`zero_whiskerRight_modules` rather than quoting `tensorComplex`'s.

**The linear map on sections is Mathlib-adjacent, not new.**
`AlgebraicGeometry.Scheme.Modules.sectionsLinearMap` (in
`StacksFrontier/AlgebraicGeometry/PullbackSections/Affine.lean`) is the existing `Γ(X, U)`-linear
packaging of `Scheme.Modules.Hom.app`; nothing of the kind is defined here.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)

## What is not done

No `@[stacks]` attribute is attached: this is infrastructure for the formal-functions arguments
and asserts no statement of the source.

Only `zero_whiskerRight` is proved, not the full `MonoidalPreadditive` structure on sheaves of
modules: `add_whiskerRight` would additionally need sheafification to be additive, not merely to
preserve zero, and nothing here needs it.

The isomorphism of complexes is over a **fixed** affine open. It is not glued over a cover, and
nothing here says the induced maps on homology of the two complexes agree with any derived tensor
product; that comparison is a separate statement.

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules (sheafifyValIso)
open scoped TensorProduct

universe w v u

namespace Stacks.SectionTensorFormula

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

section Left

variable {F F' : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
  (G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- `toTensorSection_comp_whiskerRight_val` read on an element of the sectionwise tensor
product. -/
theorem toTensorSection_whiskerRight_apply (f : F ⟶ F') (U : Cᵒᵖ)
    (t : (F.val ⊗ G.val).obj U) :
    ConcreteCategory.hom ((f ▷ G).val.app U) ((toTensorSection 𝒪 h𝒪 F G).app U t) =
      (toTensorSection 𝒪 h𝒪 F' G).app U (ConcreteCategory.hom ((f.val ▷ G.val).app U) t) :=
  congrArg
    (fun φ : (F.val ⊗ G.val ⟶ (F' ⊗ G).val) ↦ ConcreteCategory.hom (φ.app U) t)
    (toTensorSection_comp_whiskerRight_val 𝒪 h𝒪 G f)

end Left

/-! ### Naturality in both sheaf variables -/

section Both

variable {F F' G G' : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}

/-- **Naturality of the section comparison in both sheaf variables at once**, obtained from the
first-variable square of `toTensorSection_comp_whiskerRight_val` and the second-variable square
of `toTensorSection_comp_whiskerLeft_val` by `MonoidalCategory.tensorHom_def`. -/
theorem toTensorSection_comp_tensorHom_val (f : F ⟶ F') (g : G ⟶ G') :
    toTensorSection 𝒪 h𝒪 F G ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ toTensorSection 𝒪 h𝒪 F' G' :=
  calc toTensorSection 𝒪 h𝒪 F G ≫ (f ⊗ₘ g).val
      = toTensorSection 𝒪 h𝒪 F G ≫ ((f ▷ G) ≫ (F' ◁ g)).val :=
        whisker_eq _ (congrArg SheafOfModules.Hom.val (MonoidalCategory.tensorHom_def f g))
    _ = (toTensorSection 𝒪 h𝒪 F G ≫ (f ▷ G).val) ≫ (F' ◁ g).val := (Category.assoc _ _ _).symm
    _ = ((f.val ▷ G.val) ≫ toTensorSection 𝒪 h𝒪 F' G) ≫ (F' ◁ g).val :=
        eq_whisker (toTensorSection_comp_whiskerRight_val 𝒪 h𝒪 G f) _
    _ = (f.val ▷ G.val) ≫ toTensorSection 𝒪 h𝒪 F' G ≫ (F' ◁ g).val := Category.assoc _ _ _
    _ = (f.val ▷ G.val) ≫ (F'.val ◁ g.val) ≫ toTensorSection 𝒪 h𝒪 F' G' :=
        whisker_eq _ (toTensorSection_comp_whiskerLeft_val 𝒪 h𝒪 F' g)
    _ = ((f.val ▷ G.val) ≫ (F'.val ◁ g.val)) ≫ toTensorSection 𝒪 h𝒪 F' G' :=
        (Category.assoc _ _ _).symm
    _ = (f.val ⊗ₘ g.val) ≫ toTensorSection 𝒪 h𝒪 F' G' :=
        eq_whisker (MonoidalCategory.tensorHom_def f.val g.val).symm _

/-- `toTensorSection_comp_whiskerLeft_val` read on an element of the sectionwise tensor
product. -/
theorem toTensorSection_whiskerLeft_apply (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
    (g : G ⟶ G') (U : Cᵒᵖ) (t : (F.val ⊗ G.val).obj U) :
    ConcreteCategory.hom ((F ◁ g).val.app U) ((toTensorSection 𝒪 h𝒪 F G).app U t) =
      (toTensorSection 𝒪 h𝒪 F G').app U (ConcreteCategory.hom ((F.val ◁ g.val).app U) t) :=
  congrArg
    (fun φ : (F.val ⊗ G.val ⟶ (F ⊗ G').val) ↦ ConcreteCategory.hom (φ.app U) t)
    (toTensorSection_comp_whiskerLeft_val 𝒪 h𝒪 F g)

end Both

/-! ### Tensoring a vanishing morphism -/

section Zero

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The sectionwise tensor product of a zero morphism of presheaves of modules with an identity
is zero.** Sectionwise this is `ModuleCat`'s own `MonoidalPreadditive.zero_whiskerRight`, and the
`show` fixes the one spelling at which `ModuleCat` has a monoidal structure at all: the ring of
sections is `𝒪.obj X`, a *commutative* ring, and not the `RingCat` the presheaf of modules is
indexed over. -/
theorem presheaf_zero_whiskerRight
    {P Q R : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj} :
    (0 : P ⟶ Q) ▷ R = 0 := by
  refine PresheafOfModules.Hom.ext (funext fun X ↦ ?_)
  change MonoidalCategory.whiskerRight (C := ModuleCat (𝒪.obj X)) 0 (R.obj X) = 0
  exact MonoidalPreadditive.zero_whiskerRight

/-- **Sheafification sends a zero morphism to a zero morphism.** Both sides have the same image
under the hom-equivalence of the sheafification adjunction: on the left by naturality of the
unit, on the right because the right adjoint of a zero morphism is zero. Sheafification is not
known to this repository to be an additive functor, so this is proved and not inferred. -/
theorem sheafify_map_zero {P Q : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj} :
    (sheafify 𝒪 h𝒪).map (0 : P ⟶ Q) = 0 := by
  refine ((sheafifyAdjunction 𝒪 h𝒪).homEquiv P ((sheafify 𝒪 h𝒪).obj Q)).injective ?_
  have hL : (sheafifyAdjunction 𝒪 h𝒪).homEquiv P ((sheafify 𝒪 h𝒪).obj Q)
      ((sheafify 𝒪 h𝒪).map (0 : P ⟶ Q)) = 0 :=
    (Adjunction.homEquiv_unit _ _ _ _).trans
      (((sheafifyAdjunction 𝒪 h𝒪).unit.naturality (0 : P ⟶ Q)).symm.trans zero_comp)
  have hR : (sheafifyAdjunction 𝒪 h𝒪).homEquiv P ((sheafify 𝒪 h𝒪).obj Q) 0 = 0 :=
    (Adjunction.homEquiv_unit _ _ _ _).trans comp_zero
  exact hL.trans hR.symm

/-- **A zero morphism of sheaves of modules stays zero after tensoring with a fixed sheaf.** This
is `0 ▷ G = 0` for the localized monoidal structure of
`Stacks.SheafInternalHom.monoidalCategory`, which carries no additivity of its own: the
first-variable naturality of `tensorSheafIsoTensorObj` transports the question to the sheafified
sectionwise tensor product, where `presheaf_zero_whiskerRight` and `sheafify_map_zero` answer it.
No affineness and no quasi-coherence. -/
theorem zero_whiskerRight {F F' G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} :
    (0 : F ⟶ F') ▷ G = 0 :=
  have h0 : (sheafify 𝒪 h𝒪).map ((0 : F ⟶ F').val ▷ G.val) = 0 :=
    (congrArg (sheafify 𝒪 h𝒪).map (presheaf_zero_whiskerRight 𝒪 h𝒪)).trans
      (sheafify_map_zero 𝒪 h𝒪)
  have key : (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom ≫ (0 : F ⟶ F') ▷ G =
      (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom ≫ (0 : F ⊗ G ⟶ F' ⊗ G) :=
    (tensorSheafIsoTensorObj_hom_whiskerRight 𝒪 h𝒪 G (0 : F ⟶ F')).trans
      ((eq_whisker h0 (tensorSheafIsoTensorObj 𝒪 h𝒪 F' G).hom).trans
        (zero_comp.trans comp_zero.symm))
  (cancel_epi (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom).1 key

end Zero

/-! ### The scheme level -/

section Scheme

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

variable {X : Scheme.{u}}

/-- **Naturality of the product of sections in the second sheaf variable.** -/
theorem tensorSection_whiskerLeft (F : X.Modules) {G G' : X.Modules} (g : G ⟶ G')
    {U : X.Opens} (m : Γ(F, U)) (n : Γ(G, U)) :
    (F ◁ g).app U (tensorSection F G m n) = tensorSection F G' m (g.app U n) :=
  toTensorSection_whiskerLeft_apply X.presheaf (schemeSheafCondition X) F g (op U)
    (m ⊗ₜ[Γ(X, U)] n)

/-- `zero_whiskerRight` in Mathlib's `AlgebraicGeometry.Scheme.Modules` spelling. -/
theorem zero_whiskerRight_modules {F F' G : X.Modules} : (0 : F ⟶ F') ▷ G = 0 :=
  zero_whiskerRight X.presheaf (schemeSheafCondition X)

/-- A morphism of `𝒪_X`-modules that vanishes induces the zero map on sections. -/
theorem sectionsLinearMap_eq_zero {F F' : X.Modules} {f : F ⟶ F'} (hf : f = 0) (U : X.Opens) :
    Scheme.Modules.sectionsLinearMap f U = 0 :=
  hf ▸ LinearMap.ext fun _ ↦ rfl

end Scheme

/-! ### The affine open: naturality of the section isomorphism -/

section AffineOpen

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

open Scheme.Modules (sectionsLinearMap)

variable {X : Scheme.{u}}

/-- **Naturality of `tensorSectionEquiv` in the sheaf variable.** -/
theorem tensorSectionEquiv_whiskerRight {F F' : X.Modules} (f : F ⟶ F') (M : X.Modules)
    [F.IsQuasicoherent] [F'.IsQuasicoherent] [M.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (t : TensorProduct Γ(X, V) Γ(F, V) Γ(M, V)) :
    sectionsLinearMap (f ▷ M) V (tensorSectionEquiv F M hV t) =
      tensorSectionEquiv F' M hV (LinearMap.rTensor Γ(M, V) (sectionsLinearMap f V) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m n => exact tensorSection_whiskerRight f m n
  | _ => simp_all

/-- The square of `tensorSectionEquiv_whiskerRight` as a commuting square in
`ModuleCat Γ(X, V)`, through `tensorSectionIso`. -/
theorem tensorSectionIso_hom_comp_whiskerRight {F F' : X.Modules} (f : F ⟶ F') (M : X.Modules)
    [F.IsQuasicoherent] [F'.IsQuasicoherent] [M.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) :
    (tensorSectionIso F M hV).hom ≫ ModuleCat.ofHom (sectionsLinearMap (f ▷ M) V) =
      ModuleCat.ofHom (LinearMap.rTensor Γ(M, V) (sectionsLinearMap f V)) ≫
        (tensorSectionIso F' M hV).hom :=
  ModuleCat.hom_ext (LinearMap.ext (tensorSectionEquiv_whiskerRight f M hV))

/-- **Naturality of `tensorSectionEquiv` in its second sheaf variable.** -/
theorem tensorSectionEquiv_whiskerLeft (F : X.Modules) {G G' : X.Modules} (g : G ⟶ G')
    [F.IsQuasicoherent] [G.IsQuasicoherent] [G'.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) (t : TensorProduct Γ(X, V) Γ(F, V) Γ(G, V)) :
    sectionsLinearMap (F ◁ g) V (tensorSectionEquiv F G hV t) =
      tensorSectionEquiv F G' hV (LinearMap.lTensor Γ(F, V) (sectionsLinearMap g V) t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m n => exact tensorSection_whiskerLeft F g m n
  | _ => simp_all

end AffineOpen

/-! ### The complex level -/

section Complex

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

open Scheme.Modules (sectionsLinearMap)

variable {X : Scheme.{u}} {κ : Type*} {c : ComplexShape κ}

/-- **The degreewise tensor product of the complex of sections with the sections of `M`.** Its
objects are `Γ(E.X i, V) ⊗_{Γ(X, V)} Γ(M, V)` and its differentials are `Γ(E.d i j, V) ⊗ 𝟙`. -/
def sectionsTensorComplex (E : HomologicalComplex X.Modules c) (M : X.Modules) (V : X.Opens) :
    HomologicalComplex (ModuleCat Γ(X, V)) c where
  X i := ModuleCat.of Γ(X, V) (TensorProduct Γ(X, V) Γ(E.X i, V) Γ(M, V))
  d i j := ModuleCat.ofHom (LinearMap.rTensor Γ(M, V) (sectionsLinearMap (E.d i j) V))
  shape i j h := by
    rw [sectionsLinearMap_eq_zero (E.shape i j h) V, LinearMap.rTensor_zero,
      ModuleCat.ofHom_zero]
  d_comp_d' i j k _ _ := by
    have h0 : (sectionsLinearMap (E.d j k) V).comp (sectionsLinearMap (E.d i j) V) = 0 :=
      sectionsLinearMap_eq_zero (E.d_comp_d i j k) V
    rw [← ModuleCat.ofHom_comp, ← LinearMap.rTensor_comp, h0, LinearMap.rTensor_zero,
      ModuleCat.ofHom_zero]

/-- The objects of `sectionsTensorComplex E M V` are `Γ(E.X i, V) ⊗_{Γ(X, V)} Γ(M, V)`. -/
@[simp]
lemma sectionsTensorComplex_X (E : HomologicalComplex X.Modules c) (M : X.Modules) (V : X.Opens)
    (i : κ) :
    (sectionsTensorComplex E M V).X i =
      ModuleCat.of Γ(X, V) (TensorProduct Γ(X, V) Γ(E.X i, V) Γ(M, V)) := rfl

/-- The differentials of `sectionsTensorComplex E M V` are `Γ(E.d i j, V) ⊗ 𝟙`. -/
@[simp]
lemma sectionsTensorComplex_d (E : HomologicalComplex X.Modules c) (M : X.Modules) (V : X.Opens)
    (i j : κ) :
    (sectionsTensorComplex E M V).d i j =
      ModuleCat.ofHom (LinearMap.rTensor Γ(M, V) (sectionsLinearMap (E.d i j) V)) := rfl

/-- **The degreewise tensor product of a complex of `𝒪_X`-modules with a fixed module.** Its
objects are `E.X i ⊗ M` and its differentials are `E.d i j ▷ M`, the differential of `E` tensored
with the identity of `M`. That the differentials still compose to zero is `zero_whiskerRight`. -/
def tensorComplex (E : HomologicalComplex X.Modules c) (M : X.Modules) :
    HomologicalComplex X.Modules c where
  X i := E.X i ⊗ M
  d i j := E.d i j ▷ M
  shape i j h := (congrArg (fun g ↦ g ▷ M) (E.shape i j h)).trans zero_whiskerRight_modules
  d_comp_d' i j k _ _ :=
    ((MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
        (congrArg (fun g ↦ g ▷ M) (E.d_comp_d i j k))).trans zero_whiskerRight_modules

/-- The objects of `tensorComplex E M` are `E.X i ⊗ M`. -/
@[simp]
lemma tensorComplex_X (E : HomologicalComplex X.Modules c) (M : X.Modules) (i : κ) :
    (tensorComplex E M).X i = E.X i ⊗ M := rfl

/-- The differentials of `tensorComplex E M` are `E.d i j ▷ M`. -/
@[simp]
lemma tensorComplex_d (E : HomologicalComplex X.Modules c) (M : X.Modules) (i j : κ) :
    (tensorComplex E M).d i j = E.d i j ▷ M := rfl

/-- **The complex of sections over an open of the degreewise tensor product of `E` with `M`.**
Its objects are `Γ(E.X i ⊗ M, V)` and its differentials are `Γ(E.d i j ▷ M, V)`. It is the
sections of `tensorComplex`, and needs neither affineness nor quasi-coherence. -/
def tensorSectionsComplex (E : HomologicalComplex X.Modules c) (M : X.Modules) (V : X.Opens) :
    HomologicalComplex (ModuleCat Γ(X, V)) c where
  X i := ModuleCat.of Γ(X, V) Γ(E.X i ⊗ M, V)
  d i j := ModuleCat.ofHom (sectionsLinearMap (E.d i j ▷ M) V)
  shape i j h := by
    have h0 : sectionsLinearMap (E.d i j ▷ M) V = 0 :=
      sectionsLinearMap_eq_zero
        ((congrArg (fun g ↦ g ▷ M) (E.shape i j h)).trans zero_whiskerRight_modules) V
    rw [h0, ModuleCat.ofHom_zero]
  d_comp_d' i j k _ _ := by
    have h0 : (sectionsLinearMap (E.d j k ▷ M) V).comp (sectionsLinearMap (E.d i j ▷ M) V) = 0 :=
      sectionsLinearMap_eq_zero
        (((MonoidalCategory.comp_whiskerRight _ _ _).symm.trans
          (congrArg (fun g ↦ g ▷ M) (E.d_comp_d i j k))).trans zero_whiskerRight_modules) V
    rw [← ModuleCat.ofHom_comp, h0, ModuleCat.ofHom_zero]

/-- The objects of `tensorSectionsComplex E M V` are `Γ(E.X i ⊗ M, V)`. -/
@[simp]
lemma tensorSectionsComplex_X (E : HomologicalComplex X.Modules c) (M : X.Modules)
    (V : X.Opens) (i : κ) :
    (tensorSectionsComplex E M V).X i = ModuleCat.of Γ(X, V) Γ(E.X i ⊗ M, V) := rfl

/-- The differentials of `tensorSectionsComplex E M V` are `Γ(E.d i j ▷ M, V)`. -/
@[simp]
lemma tensorSectionsComplex_d (E : HomologicalComplex X.Modules c) (M : X.Modules)
    (V : X.Opens) (i j : κ) :
    (tensorSectionsComplex E M V).d i j =
      ModuleCat.ofHom (sectionsLinearMap (E.d i j ▷ M) V) := rfl

/-- **The section formula for a degreewise tensor product, as an isomorphism of complexes.**
Over an affine open `V`, the complex of sections of the degreewise tensor product of a complex
`E` of quasi-coherent `𝒪_X`-modules with a fixed quasi-coherent `M` is the degreewise tensor
product of the complex of sections of `E` with `Γ(M, V)` — compatibly with the differentials, the
components being `tensorSectionEquiv`. -/
def sectionsTensorComplexIso (E : HomologicalComplex X.Modules c) (M : X.Modules)
    (hE : ∀ i, (E.X i).IsQuasicoherent) [M.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) :
    sectionsTensorComplex E M V ≅ tensorSectionsComplex E M V :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ haveI := hE i; tensorSectionIso (E.X i) M hV)
    (fun i j _ ↦ by
      have := hE i
      have := hE j
      exact tensorSectionIso_hom_comp_whiskerRight (E.d i j) M hV)

end Complex

end Stacks.SectionTensorFormula

end
