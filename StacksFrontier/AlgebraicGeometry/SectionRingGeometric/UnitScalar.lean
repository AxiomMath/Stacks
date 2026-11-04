module

public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections

/-!
# The endomorphisms of the monoidal unit are the global functions

Let `X` be a scheme. An endomorphism of the monoidal unit of `X.Modules` is the same thing as a
global function on `X`, and composing with such an endomorphism is multiplication by that
function on global sections. This file proves both statements.

They are what makes the degree-zero part of the section ring `Γ_*(X, L)` of
[Stacks, Tag 01CV] the ring `Γ(X, 𝒪_X)` *acting in the expected way*: the degree-zero piece
`𝟙_ ⟶ L ^⊗ 0` is `𝟙_ ⟶ 𝟙_`, and the product of a degree-zero element with a degree-`n` element
is — after the commutation that the grading forces — a plain composition, so the second
statement below computes it on sections.

## Main definitions

* `Stacks.SectionRingGeometric.unitModule`: Mathlib's free rank-one sheaf of modules, read as an
  `𝒪_X`-module.
* `Stacks.SectionRingGeometric.unitComparison`: the comparison isomorphism between the monoidal
  unit and `unitModule`.
* `Stacks.SectionRingGeometric.unitOne`: the section `1` of that free rank-one sheaf.
* `Stacks.SectionRingGeometric.unitScalar`: the global function attached to an endomorphism of the
  monoidal unit, and `unitScalarEquiv` the resulting bijection.

## Main results

* `Stacks.SectionRingGeometric.globalSection_unitComp`: **composing with an endomorphism of the
  monoidal unit multiplies the global section by its scalar.**
* `Stacks.SectionRingGeometric.unitScalar_id` and
  `Stacks.SectionRingGeometric.unitScalar_comp`: the scalar of the identity is `1` and the scalar
  of a composite is the product.

## Implementation notes

Everything is computed through Mathlib's `AlgebraicGeometry.SheafOfModules.unitHomEquiv`, which
reads a morphism out of the free rank-one sheaf as the family of its values at the section `1`;
the only input is that the value of a morphism of sheaves of modules at `c • 1` is `c` times its
value at `1`, which is `AlgebraicGeometry.Scheme.Modules.Hom.app_smul`.

The sections of the free rank-one sheaf over `⊤` *are* the global functions, but as an object of
`AddCommGrp` rather than of `CommRingCat`, so the two types are definitionally equal without being
syntactically so; `unitOne` and `unitScalar` are where that identification is made, each once, and
everything else is stated in one spelling or the other throughout. The monoidal unit is not the
free rank-one sheaf but its sheafification, so each statement is conjugated by `unitComparison`.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification

universe u

namespace Stacks.SectionRingGeometric

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory

variable (X : Scheme.{u})

/-- **Mathlib's free sheaf of modules of rank one**, read as an `𝒪_X`-module. -/
abbrev unitModule : X.Modules := _root_.SheafOfModules.unit X.ringCatSheaf

/-- **The comparison isomorphism between the monoidal unit and the free rank-one sheaf.** The
monoidal unit is the sheafification of the latter, and this is the counit of the sheafification
adjunction there, which is an isomorphism because sheaves of modules are reflective in presheaves
of modules. -/
def unitComparison : 𝟙_ X.Modules ≅ unitModule X :=
  _root_.AlgebraicGeometry.SheafOfModules.unitIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)

/-- **The section `1` of the free rank-one sheaf of modules.** Its sections over `⊤` are the
global functions on `X`, and this is the unit of that ring read as such a section. -/
def unitOne : Γ(unitModule X, ⊤) := (1 : Γ(X, ⊤))

/-- **A global function, read as a section of the free rank-one sheaf of modules.** -/
def unitSec (c : Γ(X, ⊤)) : Γ(unitModule X, ⊤) := c

/-- **Scaling the section `1` is the inclusion of global functions.** The module structure on the
sections of the free rank-one sheaf is the multiplication of the ring of functions, so this is
`mul_one`. -/
theorem smul_unitOne (c : Γ(X, ⊤)) : c • unitOne X = unitSec X c :=
  mul_one c

/-- **The global function attached to an endomorphism of the monoidal unit**: its value at the
section `1`, read through the comparison with the free rank-one sheaf. -/
def unitScalar (b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) : Γ(X, ⊤) :=
  ((unitComparison X).inv ≫ b ≫ (unitComparison X).hom).app ⊤ (unitOne X)

/-- `unitScalar` read as a section of the free rank-one sheaf is the value at `1` itself. -/
theorem unitSec_unitScalar (b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    unitSec X (unitScalar X b)
      = ((unitComparison X).inv ≫ b ≫ (unitComparison X).hom).app ⊤ (unitOne X) :=
  rfl

/-- **The endomorphisms of the monoidal unit are exactly the global functions.** Conjugating by
the comparison isomorphism turns them into the endomorphisms of the free rank-one sheaf, and those
are its global sections by `AlgebraicGeometry.SheafOfModules.unitHomEquiv`. -/
def unitScalarEquiv : (𝟙_ X.Modules ⟶ 𝟙_ X.Modules) ≃ Γ(X, ⊤) :=
  ((unitComparison X).homCongr (unitComparison X)).trans
    ((unitModule X).unitHomEquiv.trans (sectionsEquivObj isTerminalTop (unitModule X).val))

/-- `unitScalarEquiv` sends an endomorphism of the monoidal unit to its scalar `unitScalar`. -/
@[simp] theorem unitScalarEquiv_apply (b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    unitScalarEquiv X b = unitScalar X b :=
  rfl

/-- **The global section of a morphism out of the monoidal unit is its value at `1`**, after the
comparison with the free rank-one sheaf. This unfolds
`Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv`. -/
theorem schemeGlobalSectionsAddEquiv_apply (F : X.Modules) (f : 𝟙_ X.Modules ⟶ F) :
    schemeGlobalSectionsAddEquiv X F f = ((unitComparison X).inv ≫ f).app ⊤ (unitOne X) :=
  rfl

/-- Precomposing `inv ≫ g` with an endomorphism `b` of the monoidal unit multiplies its value at
`1` by the scalar of `b`. -/
private theorem inv_comp_app_unitOne {G : X.Modules} (b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (g : 𝟙_ X.Modules ⟶ G) :
    ((unitComparison X).inv ≫ b ≫ g).app ⊤ (unitOne X)
      = unitScalar X b • ((unitComparison X).inv ≫ g).app ⊤ (unitOne X) := by
  rw [show (unitComparison X).inv ≫ b ≫ g = ((unitComparison X).inv ≫ b ≫ (unitComparison X).hom)
      ≫ ((unitComparison X).inv ≫ g) by simp, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply, ← unitSec_unitScalar, ← smul_unitOne,
    Scheme.Modules.Hom.app_smul]

/-- **Composing with an endomorphism of the monoidal unit multiplies the global section by its
scalar.** After conjugation the composite `b ≫ t` is a composite of two morphisms out of the free
rank-one sheaf; the first carries `1` to the scalar of `b`, which is that scalar times `1`, and the
second is linear. -/
theorem globalSection_unitComp {F : X.Modules} (b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules)
    (t : 𝟙_ X.Modules ⟶ F) :
    schemeGlobalSectionsAddEquiv X F (b ≫ t)
      = unitScalar X b • schemeGlobalSectionsAddEquiv X F t := by
  rw [schemeGlobalSectionsAddEquiv_apply, schemeGlobalSectionsAddEquiv_apply,
    inv_comp_app_unitOne]

/-- **The scalar of a sum is the sum of the scalars.** -/
theorem unitScalar_add (b c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    unitScalar X (b + c) = unitScalar X b + unitScalar X c := by
  have hsplit : (unitComparison X).inv ≫ (b + c) ≫ (unitComparison X).hom
      = ((unitComparison X).inv ≫ b ≫ (unitComparison X).hom)
        + ((unitComparison X).inv ≫ c ≫ (unitComparison X).hom) := by
    rw [Preadditive.add_comp, Preadditive.comp_add]
  have h : unitSec X (unitScalar X (b + c))
      = unitSec X (unitScalar X b) + unitSec X (unitScalar X c) := by
    rw [unitSec_unitScalar, unitSec_unitScalar, unitSec_unitScalar, hsplit,
      Scheme.Modules.Hom.add_app]
    rfl
  exact h

/-- **The endomorphisms of the monoidal unit are the global functions, additively.** -/
def unitScalarAddEquiv : (𝟙_ X.Modules ⟶ 𝟙_ X.Modules) ≃+ Γ(X, ⊤) where
  toEquiv := unitScalarEquiv X
  map_add' := unitScalar_add X

/-- `unitScalarAddEquiv` sends an endomorphism of the monoidal unit to its scalar `unitScalar`. -/
@[simp] theorem unitScalarAddEquiv_apply (b : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    unitScalarAddEquiv X b = unitScalar X b :=
  rfl

/-- **The scalar of the identity is `1`.** -/
@[simp] theorem unitScalar_id : unitScalar X (𝟙 (𝟙_ X.Modules)) = 1 := by
  have h : (unitComparison X).inv ≫ 𝟙 (𝟙_ X.Modules) ≫ (unitComparison X).hom
      = 𝟙 (unitModule X) := by
    simp
  rw [unitScalar, h]
  rfl

/-- **The scalar of a composite is the product of the scalars.** -/
theorem unitScalar_comp (b c : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    unitScalar X (b ≫ c) = unitScalar X b * unitScalar X c := by
  have hmul : unitSec X (unitScalar X b * unitScalar X c)
      = unitScalar X b • unitSec X (unitScalar X c) :=
    rfl
  have h : unitSec X (unitScalar X (b ≫ c))
      = unitSec X (unitScalar X b * unitScalar X c) := by
    rw [unitSec_unitScalar, Category.assoc, inv_comp_app_unitOne, hmul, unitSec_unitScalar]
  exact h

end Stacks.SectionRingGeometric

end
