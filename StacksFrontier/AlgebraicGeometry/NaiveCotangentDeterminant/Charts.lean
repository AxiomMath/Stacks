module

public import StacksFrontier.AlgebraicGeometry.ChartModuleSystem.Index
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.RingTheory.NaiveCotangent.DeterminantBaseChange

/-!
# The rings of the affine charts of a morphism of schemes

Let `f : Y ⟶ X` be a morphism of schemes. A chart of `f`
(`AlgebraicGeometry.Scheme.AffineChartIndex.ofHom f`) is a pair of affine opens `U ⊆ X` and
`V ⊆ Y` with `f(V) ⊆ U`; it carries the ring map `Γ(X, U) → Γ(Y, V)`. For two nested pairs
`U' ⊆ U`, `V' ⊆ V` the restriction maps form a commutative square of rings. This file records
the algebra structures of these squares and the facts about them that the gluing of
`det(NL_{Γ(V)/Γ(U)})` along the charts uses:

* the ring map of a chart of a syntomic (locally quasi-finite) morphism is syntomic
  (quasi-finite);
* the squares of nested charts satisfy the scalar tower conditions;
* the square of a refinement of charts is good for the naive cotangent complex
  (`NaiveCotangent.IsGoodSquare`), both restriction maps being localizations (Stacks 00S7 and
  07BS).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.chartAlgebra`: the algebra `Γ(Y, V)` over `Γ(X, U)` of a pair
  `f(V) ⊆ U`.
* `AlgebraicGeometry.Scheme.Hom.restrictAlgebra`: the restriction `Γ(X, U) → Γ(X, U')` as an
  algebra.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isGoodSquare_of_isBasicOpenOf`: the square of rings of a
  refinement of charts is good.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- The restriction `Γ(X, U) → Γ(X, U')` along `U' ≤ U`, as an algebra structure. -/
abbrev restrictAlgebra (X : Scheme.{u}) {U U' : X.Opens} (h : U' ≤ U) :
    Algebra Γ(X, U) Γ(X, U') :=
  (X.presheaf.map (homOfLE h).op).hom.toAlgebra

/-- Restricting along `U'' ≤ U' ≤ U` is restricting along `U'' ≤ U`. -/
theorem isScalarTower_restrictAlgebra (X : Scheme.{u}) {U U' U'' : X.Opens} (h : U' ≤ U)
    (h' : U'' ≤ U') :
    letI := X.restrictAlgebra h
    letI := X.restrictAlgebra h'
    letI := X.restrictAlgebra (h'.trans h)
    IsScalarTower Γ(X, U) Γ(X, U') Γ(X, U'') := by
  let := X.restrictAlgebra h
  let := X.restrictAlgebra h'
  let := X.restrictAlgebra (h'.trans h)
  refine .of_algebraMap_eq fun x => ?_
  simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting along `U ≤ U` is bijective. -/
theorem bijective_restrict_self (X : Scheme.{u}) (U : X.Opens) (h : U ≤ U) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  have : homOfLE h = 𝟙 U := rfl
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

end Scheme

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The algebra `Γ(Y, V)` over `Γ(X, U)` attached to opens with `f(V) ⊆ U`. -/
abbrev chartAlgebra {U : X.Opens} {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) : Algebra Γ(X, U) Γ(Y, V) :=
  (f.appLE U V e).hom.toAlgebra

/-- The ring map of a chart of a syntomic morphism is syntomic. -/
theorem syntomic_chartAlgebra (hf : Syntomic f) (U : X.affineOpens) (V : Y.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI := f.chartAlgebra e
    Algebra.Syntomic Γ(X, U.1) Γ(Y, V.1) :=
  HasRingHomProperty.appLE (P := @Syntomic) f hf U V e

/-- The ring map of a chart of a locally quasi-finite morphism is quasi-finite. -/
theorem quasiFinite_chartAlgebra (hf : LocallyQuasiFinite f) (U : X.affineOpens)
    (V : Y.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI := f.chartAlgebra e
    Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
  HasRingHomProperty.appLE (P := @LocallyQuasiFinite) f hf U V e

/-! ### The square of rings of two nested charts -/

section Square

variable {U U' : X.Opens} {V V' : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U')
  (hU : U' ≤ U) (hV : V' ≤ V)

/-- In the square of two nested charts, `Γ(X, U) → Γ(X, U') → Γ(Y, V')` is the diagonal. -/
theorem isScalarTower_chartAlgebra_restrict :
    letI := f.chartAlgebra e'
    letI := X.restrictAlgebra hU
    letI := f.chartAlgebra (hV.trans e)
    IsScalarTower Γ(X, U) Γ(X, U') Γ(Y, V') := by
  let := f.chartAlgebra e'
  let := X.restrictAlgebra hU
  let := f.chartAlgebra (hV.trans e)
  refine .of_algebraMap_eq fun x => ?_
  simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- In the square of two nested charts, `Γ(X, U) → Γ(Y, V) → Γ(Y, V')` is the diagonal. -/
theorem isScalarTower_restrict_chartAlgebra :
    letI := f.chartAlgebra e
    letI := Y.restrictAlgebra hV
    letI := f.chartAlgebra (hV.trans e)
    IsScalarTower Γ(X, U) Γ(Y, V) Γ(Y, V') := by
  let := f.chartAlgebra e
  let := Y.restrictAlgebra hV
  let := f.chartAlgebra (hV.trans e)
  refine .of_algebraMap_eq fun x => ?_
  simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end Square

/-- **The square of rings of a refinement of charts is good for the naive cotangent complex**:
if `U'` is a basic open of `U` and `V'` a basic open of `V`, the comparison
`NL_{Γ(V)/Γ(U)} ⊗ Γ(V') ⟶ NL_{Γ(V')/Γ(U')}` is a quasi-isomorphism, both restrictions being
localizations (Stacks 00S7 and 07BS). -/
theorem isGoodSquare_of_isBasicOpenOf {U U' : X.affineOpens} {V V' : Y.affineOpens}
    (e : V.1 ≤ f ⁻¹ᵁ U.1) (e' : V'.1 ≤ f ⁻¹ᵁ U'.1) (hU : X.IsBasicOpenOf U.1 U'.1)
    (hV : Y.IsBasicOpenOf V.1 V'.1) :
    letI := f.chartAlgebra e
    letI := f.chartAlgebra e'
    letI := X.restrictAlgebra hU.le
    letI := Y.restrictAlgebra hV.le
    letI := f.chartAlgebra (hV.le.trans e)
    haveI := f.isScalarTower_chartAlgebra_restrict e e' hU.le hV.le
    haveI := f.isScalarTower_restrict_chartAlgebra e hV.le
    NaiveCotangent.IsGoodSquare Γ(X, U.1) Γ(Y, V.1) Γ(X, U'.1) Γ(Y, V'.1) := by
  let := f.chartAlgebra e
  let := f.chartAlgebra e'
  let := X.restrictAlgebra hU.le
  let := Y.restrictAlgebra hV.le
  let := f.chartAlgebra (hV.le.trans e)
  have := f.isScalarTower_chartAlgebra_restrict e e' hU.le hV.le
  have := f.isScalarTower_restrict_chartAlgebra e hV.le
  obtain ⟨a, ha⟩ := hU
  obtain ⟨g, hg⟩ := hV
  have : IsLocalization.Away a Γ(X, U'.1) :=
    U.2.isLocalization_of_eq_basicOpen a (homOfLE _) ha
  have : IsLocalization.Away g Γ(Y, V'.1) :=
    V.2.isLocalization_of_eq_basicOpen g (homOfLE _) hg
  intro k
  exact NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization_of_isLocalization
    (Submonoid.powers g) (Submonoid.powers a) k


/-! ### The square of rings of charts over a commutative square of schemes -/

section BaseChangeSquare

variable {X' Y' : Scheme.{u}} {f' : Y' ⟶ X'} {a : X' ⟶ X} {b : Y' ⟶ Y}
  {U : X.Opens} {V : Y.Opens} {U' : X'.Opens} {V' : Y'.Opens}

/-- The ring map `Γ(X, U) → Γ(Y', V')` of a chart `(U', V')` of `f'` lying over a chart `(U, V)`
of `f` along `a`, through `Γ(X', U')`. -/
abbrev squareAlgebra (f' : Y' ⟶ X') (a : X' ⟶ X) (hU : U' ≤ a ⁻¹ᵁ U) (e' : V' ≤ f' ⁻¹ᵁ U') :
    Algebra Γ(X, U) Γ(Y', V') :=
  (a.appLE U U' hU ≫ f'.appLE U' V' e').hom.toAlgebra

/-- In the square of rings of charts over a commutative square, `Γ(X, U) → Γ(X', U') → Γ(Y', V')`
is the diagonal. -/
theorem isScalarTower_squareAlgebra_left (hU : U' ≤ a ⁻¹ᵁ U) (e' : V' ≤ f' ⁻¹ᵁ U') :
    letI := a.chartAlgebra hU
    letI := f'.chartAlgebra e'
    letI := squareAlgebra f' a hU e'
    IsScalarTower Γ(X, U) Γ(X', U') Γ(Y', V') := by
  let := a.chartAlgebra hU
  let := f'.chartAlgebra e'
  let := squareAlgebra f' a hU e'
  exact .of_algebraMap_eq fun _ => rfl

/-- In the square of rings of charts over a commutative square `b ≫ f = f' ≫ a`,
`Γ(X, U) → Γ(Y, V) → Γ(Y', V')` is the diagonal. -/
theorem isScalarTower_squareAlgebra_right (w : b ≫ f = f' ≫ a) (e : V ≤ f ⁻¹ᵁ U)
    (hU : U' ≤ a ⁻¹ᵁ U) (hV : V' ≤ b ⁻¹ᵁ V) (e' : V' ≤ f' ⁻¹ᵁ U') :
    letI := f.chartAlgebra e
    letI := b.chartAlgebra hV
    letI := squareAlgebra f' a hU e'
    IsScalarTower Γ(X, U) Γ(Y, V) Γ(Y', V') := by
  let := f.chartAlgebra e
  let := b.chartAlgebra hV
  let := squareAlgebra f' a hU e'
  refine .of_algebraMap_eq fun x => ?_
  simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]
  have key : ∀ (g h : Y' ⟶ X) (_ : g = h) (e₁ : V' ≤ g ⁻¹ᵁ U) (e₂ : V' ≤ h ⁻¹ᵁ U),
      g.appLE U V' e₁ = h.appLE U V' e₂ := by
    rintro g _ rfl _ _
    rfl
  rw [key _ _ w]

/-- **The square of rings of a chart `(U', V')` of `f'` over a chart `(U, V)` of `f` is good**
for the naive cotangent complex, along a commutative square `b ≫ f = f' ≫ a`: the comparison
`NL_{Γ(V)/Γ(U)} ⊗ Γ(V') ⟶ NL_{Γ(V')/Γ(U')}` is a quasi-isomorphism. -/
def IsGoodChartSquare (w : b ≫ f = f' ≫ a) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f' ⁻¹ᵁ U')
    (hU : U' ≤ a ⁻¹ᵁ U) (hV : V' ≤ b ⁻¹ᵁ V) : Prop :=
  letI := f.chartAlgebra e
  letI := f'.chartAlgebra e'
  letI := a.chartAlgebra hU
  letI := b.chartAlgebra hV
  letI := squareAlgebra f' a hU e'
  haveI := isScalarTower_squareAlgebra_left hU e'
  haveI := f.isScalarTower_squareAlgebra_right w e hU hV e'
  NaiveCotangent.IsGoodSquare Γ(X, U) Γ(Y, V) Γ(X', U') Γ(Y', V')

end BaseChangeSquare

end Scheme.Hom

end AlgebraicGeometry

end
