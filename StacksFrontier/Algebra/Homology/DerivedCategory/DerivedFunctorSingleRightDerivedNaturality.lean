module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived

/-! # The bridge `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` is natural in the functor `w`

Let `A` and `B` be abelian categories with unbounded derived categories, `A` with enough
injectives, let `w₁, w₂ : A ⥤ B` be additive and let `Rw₁, Rw₂ : D(A) ⥤ D(B)`, with units `α₁`
and `α₂`, be right derived functors of `w₁` and `w₂` on the unbounded derived category. A
natural transformation `τ : w₁ ⟶ w₂` induces a morphism on each side of the bridge
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`:

* on the derived side, the morphism `Rw₁ ⟶ Rw₂` produced by the universal property of right
  derivation from `τ` read on homotopy categories, and then `Hⁿ(-(X[0]))`; and
* on the classical side, Mathlib's `CategoryTheory.NatTrans.rightDerived τ n`.

The two agree under the bridge. That is
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality`.

This is one of the three coherences a comparison of an excision statement proved in the
unbounded derived category with one proved from Mathlib's `CategoryTheory.Functor.rightDerived`
needs — the one for the degreewise comparison itself, as opposed to the two for pre- and
post-composition with an exact functor. The implementation notes of
`Stacks.Cohomology.SupportedComplexes.LocalCohomologySheafExcision` record all three as missing;
this file supplies this one.

## Main definitions

* `Stacks.DerivedFunctor.mapHomotopyCategoryCompQhNatTrans`: the natural transformation
  `w₁(-) ∘ Qh ⟶ w₂(-) ∘ Qh` induced by `τ` on complexes, which is the datum the universal
  property of right derivation consumes.
* `Stacks.DerivedFunctor.derivedNatTrans`: the induced morphism `Rw₁ ⟶ Rw₂` of right derived
  functors on the unbounded derived category.
* `Stacks.DerivedFunctor.singleCompDerivedCompHomologyNatTrans`: that morphism read on
  `Hⁿ(-(X[0]))`, the derived side of the square.

## Main results

* `Stacks.DerivedFunctor.rightDerivedNatTrans_unit_iso`: **the morphism of right derived functors
  produced by the universal property is unchanged when the units are transported along
  isomorphisms of the underived functors.** This is the glue that makes the main result
  applicable to a right derived functor whose unit is presented at a functor isomorphic to, but
  not spelled as, `w(-) ∘ Qh` — which is the shape a composite `Rw ⋙ G.mapDerivedCategory`
  comes in, and the only shape the bridge is defined for.
* `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_hom_app`: the components
  of the bridge, written out as the four-factor composite they are.
* `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality_app`,
  `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived_naturality`: **the bridge
  is natural in the functor variable**, componentwise and as an equality of natural
  transformations.

## Implementation notes

The proof is four commuting squares pasted side by side, one for each factor of the bridge:

* naturality of the induced `Rw₁ ⟶ Rw₂` along the augmentation
  `X[0] ⟶ Qh(resH X)` of `Stacks.DerivedFunctor.singleIsoResCompQh`;
* the defining equation of `CategoryTheory.Functor.rightDerivedNatTrans`, read at the extended
  chosen injective resolution, where both units are invertible — this is the one step that uses
  the universal property, and it is the reason the statement is about the *induced* morphism and
  not about an arbitrary one;
* naturality of `CategoryTheory.DerivedCategory.homologyFunctorFactorsh`; and
* `Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_naturality`, the corresponding statement
  for Mathlib's `ℕ`-indexed right derived functors.

The second and the fourth are squares whose horizontal edges are the *inverses* of the
isomorphisms that the hypotheses provide, hence
`Stacks.DerivedIndexing.comm_of_comm_inv`, which this file uses rather than keeping its own
copy.

`singleCompDerivedCompHomologyIsoRightDerived` is a six-fold `Iso.trans` two of whose factors
are `CategoryTheory.Iso.refl` reassociations, so its components carry two identity morphisms.
`singleCompDerivedCompHomologyIsoRightDerived_hom_app` removes them: the identity-laden form is
`rfl`, which elaborates at default transparency and so sees through the two spellings of the
reassociated composites, and the identities are then cancelled with `congrArg` at an explicit
lambda rather than by a rewrite, which would have to re-typecheck the goal at a transparency at
which those spellings are not interchangeable.

## References

* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- Four commuting squares pasted side by side, in the shape in which the four-factor comparison
`singleCompDerivedCompHomologyIsoRightDerived_hom_app` produces it. Stated at an arbitrary
category with the objects implicit and the morphisms explicit. -/
private lemma paste_squares₄ {E : Type*} [Category* E]
    {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : E}
    (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁) (v₂ : X₂ ⟶ Y₂) (v₃ : X₃ ⟶ Y₃) (v₄ : X₄ ⟶ Y₄)
    (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃) (a₄ : X₃ ⟶ X₄)
    (b₁ : Y₀ ⟶ Y₁) (b₂ : Y₁ ⟶ Y₂) (b₃ : Y₂ ⟶ Y₃) (b₄ : Y₃ ⟶ Y₄)
    (h₁ : v₀ ≫ b₁ = a₁ ≫ v₁) (h₂ : v₁ ≫ b₂ = a₂ ≫ v₂) (h₃ : v₂ ≫ b₃ = a₃ ≫ v₃)
    (h₄ : v₃ ≫ b₄ = a₄ ≫ v₄) :
    v₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ v₄ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]

/-! ### Transporting the units of a right derived functor along isomorphisms -/

section Transport

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W] (RF₁ RF₂ : D ⥤ E)
  {F₁ F₂ G₁ G₂ : C ⥤ E}

/-- **The morphism of right derived functors produced by the universal property does not change
when the units are transported along isomorphisms of the underived functors.** If `β₁ = e₁ ≫ α₁`
and `β₂ = e₂ ≫ α₂` for isomorphisms `e₁ : G₁ ≅ F₁`, `e₂ : G₂ ≅ F₂`, then the morphism induced by
`σ = e₁ ≫ τ ≫ e₂⁻¹` from the units `β₁, β₂` is the one induced by `τ` from `α₁, α₂`.

This is the glue that makes `singleCompDerivedCompHomologyIsoRightDerived_naturality` applicable
to a derived functor whose unit is presented at a functor isomorphic to, but not spelled as,
`w(-) ∘ Qh`: a composite `Rw ⋙ G.mapDerivedCategory` is a right derived functor of `w ⋙ G` with
a unit written at `w(-) ∘ Qh ∘ G.mapDerivedCategory`, and the bridge is defined only for the
other spelling.

Both `IsRightDerivedFunctor` hypotheses are explicit arguments: they are statements about one
functor at two different units, so they cannot both be found by instance search. -/
theorem rightDerivedNatTrans_unit_iso (α₁ : F₁ ⟶ L ⋙ RF₁) (α₂ : F₂ ⟶ L ⋙ RF₂)
    (β₁ : G₁ ⟶ L ⋙ RF₁) (β₂ : G₂ ⟶ L ⋙ RF₂) (e₁ : G₁ ≅ F₁) (e₂ : G₂ ≅ F₂)
    (τ : F₁ ⟶ F₂) (σ : G₁ ⟶ G₂)
    (hα : RF₁.IsRightDerivedFunctor α₁ W) (hβ : RF₁.IsRightDerivedFunctor β₁ W)
    (hβ₁ : β₁ = e₁.hom ≫ α₁) (hβ₂ : β₂ = e₂.hom ≫ α₂)
    (hσ : σ = e₁.hom ≫ τ ≫ e₂.inv) :
    Functor.rightDerivedNatTrans RF₁ RF₂ β₁ β₂ W σ =
      Functor.rightDerivedNatTrans RF₁ RF₂ α₁ α₂ W τ := by
  let := hα
  let := hβ
  refine Functor.rightDerived_ext RF₁ β₁ W RF₂ _ _ ?_
  have hfac : α₁ ≫ Functor.whiskerLeft L (Functor.rightDerivedNatTrans RF₁ RF₂ α₁ α₂ W τ) =
      τ ≫ α₂ := Functor.rightDerivedNatTrans_fac RF₁ RF₂ α₁ α₂ W τ
  rw [Functor.rightDerivedNatTrans_fac, hβ₁, hβ₂, hσ, Category.assoc _ α₁ _, hfac]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Transport

/-! ### The induced morphism of right derived functors on the unbounded derived category -/

section

variable (w₁ w₂ : A ⥤ B) [w₁.Additive] [w₂.Additive]

/-- **The datum the universal property of right derivation consumes.** A natural transformation
`τ : w₁ ⟶ w₂` applied termwise to cochain complexes, read in the derived category: a morphism
`w₁(-) ∘ Qh ⟶ w₂(-) ∘ Qh` of functors `K(A) ⥤ D(B)`. -/
def mapHomotopyCategoryCompQhNatTrans (τ : w₁ ⟶ w₂) :
    w₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      w₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
    DerivedCategory.Qh

omit [EnoughInjectives A] [HasDerivedCategory A] in
/-- The components of `mapHomotopyCategoryCompQhNatTrans`. -/
lemma mapHomotopyCategoryCompQhNatTrans_app (τ : w₁ ⟶ w₂)
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (mapHomotopyCategoryCompQhNatTrans w₁ w₂ τ).app K =
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) := rfl

variable (Rw₁ Rw₂ : DerivedCategory A ⥤ DerivedCategory B)
  (α₁ : w₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw₁)
  (α₂ : w₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw₂)
  [Rw₁.IsRightDerivedFunctor α₁ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [Rw₂.IsRightDerivedFunctor α₂ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The morphism of right derived functors on the unbounded derived category induced by
`τ : w₁ ⟶ w₂`**, produced by the universal property of right derivation from
`mapHomotopyCategoryCompQhNatTrans`. -/
def derivedNatTrans (τ : w₁ ⟶ w₂) : Rw₁ ⟶ Rw₂ :=
  Functor.rightDerivedNatTrans Rw₁ Rw₂ α₁ α₂
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (mapHomotopyCategoryCompQhNatTrans w₁ w₂ τ)

omit [EnoughInjectives A]
    [Rw₂.IsRightDerivedFunctor α₂ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] in
/-- The defining equation of `derivedNatTrans`: it is compatible with the two units and with
`τ` applied termwise. -/
lemma derivedNatTrans_app (τ : w₁ ⟶ w₂) (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    α₁.app K ≫ (derivedNatTrans w₁ w₂ Rw₁ Rw₂ α₁ α₂ τ).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) ≫ α₂.app K :=
  Functor.rightDerivedNatTrans_app Rw₁ Rw₂ α₁ α₂ _ _ K

/-- **The derived side of the square**: the morphism `derivedNatTrans` read on the degree-`n`
cohomology of the derived functor applied to an object placed in degree `0`. -/
def singleCompDerivedCompHomologyNatTrans (τ : w₁ ⟶ w₂) (n : ℤ) :
    DerivedCategory.singleFunctor A 0 ⋙ Rw₁ ⋙ DerivedCategory.homologyFunctor B n ⟶
      DerivedCategory.singleFunctor A 0 ⋙ Rw₂ ⋙ DerivedCategory.homologyFunctor B n :=
  Functor.whiskerLeft (DerivedCategory.singleFunctor A 0)
    (Functor.whiskerRight (derivedNatTrans w₁ w₂ Rw₁ Rw₂ α₁ α₂ τ)
      (DerivedCategory.homologyFunctor B n))

omit [EnoughInjectives A]
    [Rw₂.IsRightDerivedFunctor α₂ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] in
/-- The components of `singleCompDerivedCompHomologyNatTrans`. -/
lemma singleCompDerivedCompHomologyNatTrans_app (τ : w₁ ⟶ w₂) (n : ℤ) (X : A) :
    (singleCompDerivedCompHomologyNatTrans w₁ w₂ Rw₁ Rw₂ α₁ α₂ τ n).app X =
      (DerivedCategory.homologyFunctor B n).map
        ((derivedNatTrans w₁ w₂ Rw₁ Rw₂ α₁ α₂ τ).app
          ((DerivedCategory.singleFunctor A 0).obj X)) := rfl

end

/-! ### The components of the bridge -/

section Components

variable (w : A ⥤ B) [w.Additive] (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw)
  [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)

/-- **The components of the bridge `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)`**, as the four-factor composite they
are: the augmentation to the extended chosen injective resolution, the inverse of the unit of
`Rw` there, the factorisation of the cohomology functor through the homotopy category, and the
inverse of the identification of `Rⁿw` with the cohomology of `w` applied to that resolution.

The definition is a six-fold `Iso.trans` two of whose factors are reassociations, so the
identity morphisms those contribute are removed here; see the implementation notes. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_hom_app (n : ℕ) (X : A) :
    (singleCompDerivedCompHomologyIsoRightDerived w Rw α hres n).hom.app X =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (Rw.map ((singleIsoResCompQh (A := A)).hom.app X)) ≫
        (DerivedCategory.homologyFunctor B (n : ℤ)).map
            ((resCompUnitIso w Rw α hres).inv.app X) ≫
          (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
              ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj
                (Stacks.DerivedIndexing.resH.obj X)) ≫
            (Stacks.DerivedIndexing.rightDerivedIsoRes w n).inv.app X := by
  have h : (singleCompDerivedCompHomologyIsoRightDerived w Rw α hres n).hom.app X =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          (Rw.map ((singleIsoResCompQh (A := A)).hom.app X)) ≫
        𝟙 _ ≫
          (DerivedCategory.homologyFunctor B (n : ℤ)).map
              ((resCompUnitIso w Rw α hres).inv.app X) ≫
            𝟙 _ ≫
              (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
                  ((w.mapHomotopyCategory (ComplexShape.up ℤ)).obj
                    (Stacks.DerivedIndexing.resH.obj X)) ≫
                (Stacks.DerivedIndexing.rightDerivedIsoRes w n).inv.app X := rfl
  rw [h, Category.id_comp, Category.id_comp]

end Components

/-! ### The bridge is natural in the functor variable -/

section Naturality

variable (w₁ w₂ : A ⥤ B) [w₁.Additive] [w₂.Additive]
  (Rw₁ Rw₂ : DerivedCategory A ⥤ DerivedCategory B)
  (α₁ : w₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw₁)
  (α₂ : w₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ Rw₂)
  [Rw₁.IsRightDerivedFunctor α₁ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [Rw₂.IsRightDerivedFunctor α₂ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  (τ : w₁ ⟶ w₂)

/-- **The bridge is natural in the functor variable, componentwise.** -/
theorem singleCompDerivedCompHomologyIsoRightDerived_naturality_app (n : ℕ) (X : A) :
    (singleCompDerivedCompHomologyNatTrans w₁ w₂ Rw₁ Rw₂ α₁ α₂ τ (n : ℤ)).app X ≫
        (singleCompDerivedCompHomologyIsoRightDerived w₂ Rw₂ α₂ hres n).hom.app X =
      (singleCompDerivedCompHomologyIsoRightDerived w₁ Rw₁ α₁ hres n).hom.app X ≫
        (NatTrans.rightDerived τ n).app X := by
  set Hn := DerivedCategory.homologyFunctor B (n : ℤ) with hHn
  set Hz := HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) (n : ℤ) with hHz
  set K := Stacks.DerivedIndexing.resH.obj X with hK
  set ρ := derivedNatTrans w₁ w₂ Rw₁ Rw₂ α₁ α₂ τ with hρ
  set s := (singleIsoResCompQh (A := A)).hom.app X with hs
  set tt := (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K with htt
  -- the four squares
  have h₁ : Hn.map (ρ.app ((DerivedCategory.singleFunctor A 0).obj X)) ≫
        Hn.map (Rw₂.map s) = Hn.map (Rw₁.map s) ≫
          Hn.map (ρ.app (DerivedCategory.Qh.obj K)) := by
    rw [← Hn.map_comp, ← Hn.map_comp]
    exact congrArg Hn.map (ρ.naturality s).symm
  have h₂ : Hn.map (ρ.app (DerivedCategory.Qh.obj K)) ≫
        Hn.map ((resCompUnitIso w₂ Rw₂ α₂ hres).inv.app X) =
      Hn.map ((resCompUnitIso w₁ Rw₁ α₁ hres).inv.app X) ≫
        Hn.map (DerivedCategory.Qh.map tt) := by
    rw [← Hn.map_comp, ← Hn.map_comp]
    exact congrArg Hn.map
      (Stacks.DerivedIndexing.comm_of_comm_inv ((resCompUnitIso w₁ Rw₁ α₁ hres).app X)
        ((resCompUnitIso w₂ Rw₂ α₂ hres).app X) (DerivedCategory.Qh.map tt)
        (ρ.app (DerivedCategory.Qh.obj K))
        (derivedNatTrans_app w₁ w₂ Rw₁ Rw₂ α₁ α₂ τ K))
  have h₃ : Hn.map (DerivedCategory.Qh.map tt) ≫
        (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
          ((w₂.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.app
          ((w₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫ Hz.map tt :=
    (DerivedCategory.homologyFunctorFactorsh B (n : ℤ)).hom.naturality tt
  have h₄ : Hz.map tt ≫ (Stacks.DerivedIndexing.rightDerivedIsoRes w₂ n).inv.app X =
      (Stacks.DerivedIndexing.rightDerivedIsoRes w₁ n).inv.app X ≫
        (NatTrans.rightDerived τ n).app X :=
    Stacks.DerivedIndexing.comm_of_comm_inv
      ((Stacks.DerivedIndexing.rightDerivedIsoRes w₁ n).app X)
      ((Stacks.DerivedIndexing.rightDerivedIsoRes w₂ n).app X)
      ((NatTrans.rightDerived τ n).app X) (Hz.map tt)
      (Stacks.DerivedIndexing.rightDerivedIsoRes_hom_app_naturality τ n X).symm
  rw [singleCompDerivedCompHomologyIsoRightDerived_hom_app,
    singleCompDerivedCompHomologyIsoRightDerived_hom_app,
    singleCompDerivedCompHomologyNatTrans_app]
  exact paste_squares₄ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

/-- **The bridge `Hⁿ(Rw(X[0])) ≅ Rⁿw(X)` is natural in the functor variable.** For additive
`w₁, w₂ : A ⥤ B` with right derived functors `Rw₁, Rw₂` on the unbounded derived category and
`τ : w₁ ⟶ w₂`, the morphism `Rw₁ ⟶ Rw₂` that the universal property of right derivation produces
from `τ`, read on the degree-`n` cohomology of the derived functor at an object placed in degree
`0`, corresponds under the bridge to Mathlib's `CategoryTheory.NatTrans.rightDerived τ n`. -/
theorem singleCompDerivedCompHomologyIsoRightDerived_naturality (n : ℕ) :
    singleCompDerivedCompHomologyNatTrans w₁ w₂ Rw₁ Rw₂ α₁ α₂ τ (n : ℤ) ≫
        (singleCompDerivedCompHomologyIsoRightDerived w₂ Rw₂ α₂ hres n).hom =
      (singleCompDerivedCompHomologyIsoRightDerived w₁ Rw₁ α₁ hres n).hom ≫
        NatTrans.rightDerived τ n :=
  NatTrans.ext (funext fun X ↦
    singleCompDerivedCompHomologyIsoRightDerived_naturality_app w₁ w₂ Rw₁ Rw₂ α₁ α₂ hres τ n X)

end Naturality

end Stacks.DerivedFunctor

end
