module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.DerivedSections
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.DerivedSections

/-!
# The mates of the restriction transformation under the coevaluation adjunctions

For `a' : V' ⟶ U'` in `C'`, the restriction transformation from the sections over `U'` to the
sections over `V'` has a mate under the coevaluation adjunctions over `U'` and over `V'`, and
so has the canonical derived restriction transformation under the derived coevaluation
adjunctions. This file computes the chain-level mate as reindexing of families of sections,
shows that the derived mate is the descent of the chain-level mate, and proves the
chain-level square relating the mate to restriction of scalars along `φ`. These are the inputs
to the compatibility of the derived sections computation with the restriction maps.

## Main definitions

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.coevRestrictionMate` and
  `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dCoevRestrictionMate`: the mates of
  the restriction transformation along `a' : V' ⟶ U'` and of the canonical derived restriction
  transformation under the coevaluation adjunctions over `U'` and over `V'`.

## Main results

* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.coevRestrictionMate_apply`: the
  mate of the restriction transformation is reindexing along `· ≫ a'`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.dCoevRestrictionMate_app_Q`: taking
  mates commutes with descent to the derived category — the mate of the canonical derived
  restriction transformation is the descent of the chain-level mate `coevRestrictionMate`.
* `Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.conjugateEquiv_app_eq`: a closed
  formula for a component of a conjugate transformation.
* `coevRestrictionMate_restrictScalarsSquare`: the chain-level restriction square for the
  coevaluations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.DerivedCategoryComparisons (mapDerivedCategoryCompIso
  mapDerivedCategoryCompIso_inv_app_Q mapDerivedCategoryIsoOfNatIso)

universe r v u v' u' w

namespace Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C' ⥤ C)
  (O : Cᵒᵖ ⥤ RingCat.{r}) (O' : C'ᵒᵖ ⥤ RingCat.{r}) (φ : F.op ⋙ O ⟶ O')
  (hO : ∀ (U : Cᵒᵖ) (x y : O.obj U), x * y = y * x)
  (hO' : ∀ (U' : C'ᵒᵖ) (x y : O'.obj U'), x * y = y * x)

attribute [local instance] HasDerivedCategory.standard

/-! ### Bookkeeping for the restriction square -/

section RestrictionBookkeeping

universe s₁ t₄ s₂ t₅

variable {E : Type t₄} [Category.{s₁} E]

/-- Dropping an identity from the middle of a composite. -/
private theorem drop_id {X Y Z W : E} (a : X ⟶ Y) (b : Y ⟶ Z) (e : Z ⟶ Z) (he : e = 𝟙 Z)
    (c : Z ⟶ W) : a ≫ b ≫ e ≫ c = a ≫ b ≫ c := by
  rw [he, Category.id_comp]

/-- Substituting the middle morphism of a composite of four. -/
private theorem congr_mid {X Y Z W V : E} (f : X ⟶ Y) (g : Y ⟶ Z) {m₁ m₂ : Z ⟶ W}
    (hm : m₁ = m₂) (k : W ⟶ V) : f ≫ g ≫ m₁ ≫ k = f ≫ g ≫ m₂ ≫ k := by
  rw [hm]

/-- Cancelling a pair of mutually inverse morphisms at the head of a composite. -/
private theorem cancel_head {X Y Z₁ Z₂ Z₃ : E} {a : X ⟶ Y} {b : Y ⟶ X} (hab : a ≫ b = 𝟙 X)
    {c : X ⟶ Z₁} {d : Z₁ ⟶ Z₂} {e : Z₂ ⟶ Z₃} {m : Y ⟶ Z₃} (h : m = b ≫ c ≫ d ≫ e) :
    a ≫ m = c ≫ d ≫ e := by
  rw [h, ← Category.assoc, hab, Category.id_comp]

/-- Cancelling, under a functor, a pair of mutually inverse morphisms at the head of a
composite. -/
private theorem cancel_head_map {D₁ : Type*} [Category D₁] (T : D₁ ⥤ E) {x₃ x₄ : D₁}
    {α₃ : x₃ ⟶ x₄} {β₁ : x₄ ⟶ x₃} (hβ : α₃ ≫ β₁ = 𝟙 x₃)
    {e₁ e₂ e₃ e₄ : E} {m : T.obj x₄ ⟶ e₄} {γ : T.obj x₃ ⟶ e₁} {qx : e₁ ⟶ e₂}
    {δ : e₂ ⟶ e₃} {ε : e₃ ⟶ e₄} (h : m = T.map β₁ ≫ γ ≫ qx ≫ δ ≫ ε) :
    T.map α₃ ≫ m = γ ≫ qx ≫ δ ≫ ε := by
  rw [h, ← Functor.map_comp_assoc, hβ, T.map_id, Category.id_comp]

/-- The unit square for a descended mate, from the naturality `h₁` of the descended
transformation, its value `h₂` at the image of a complex, the two cancellations `h₃` and `h₄` of a
canonical factorization against its inverse, the naturality `h₅` of the factorization of the outer
descent, and the chain-level unit square `h₆`. -/
private theorem unit_square_bookkeeping {B : Type t₅} [Category.{s₂} B] {T : B ⥤ E}
    {b₁ b₂ b₃ b₄ b₅ : B} {x d₁ d₂ d₃ d₄ d₅ : E}
    {f' : b₁ ⟶ b₂} {f : b₂ ⟶ b₁} {q : b₁ ⟶ b₃} {s : b₃ ⟶ b₄} {k : b₄ ⟶ b₅}
    {qV : x ⟶ d₁} {jV : d₁ ⟶ T.obj b₁} {qU : x ⟶ d₂} {jU : d₂ ⟶ d₃} {jU' : d₃ ⟶ d₂}
    {m : d₃ ⟶ d₄} {δ : d₄ ⟶ T.obj b₅} {δ₀ : d₃ ⟶ T.obj b₄} {qm : d₂ ⟶ d₅}
    {jV₂ : d₅ ⟶ T.obj b₃} {qmc : d₁ ⟶ d₅}
    (h₁ : m ≫ δ = δ₀ ≫ T.map k)
    (h₂ : δ₀ = jU' ≫ qm ≫ jV₂ ≫ T.map s)
    (h₃ : jU ≫ jU' = 𝟙 d₂)
    (h₄ : f' ≫ f = 𝟙 b₁)
    (h₅ : qmc ≫ jV₂ = jV ≫ T.map q)
    (h₆ : qV ≫ qmc = qU ≫ qm) :
    (qV ≫ jV ≫ T.map f') ≫ T.map (f ≫ q ≫ s ≫ k) = (qU ≫ jU ≫ m) ≫ δ := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, h₄, T.map_id, Category.id_comp, ← reassoc_of% h₅,
    reassoc_of% h₆, h₁, h₂]
  simp only [Category.assoc]
  rw [reassoc_of% h₃]

/-- The left-hand side of the derived restriction square: the derived mate at the image of a
complex, against the naturality of the derived coevaluation square and of the canonical
factorization of the descent of restriction of scalars. -/
private theorem bookL {D₁ : Type*} [Category D₁] (T : D₁ ⥤ E) {x₁ x₂ x₃ x₄ x₅ : D₁}
    {dmQ : x₁ ⟶ x₅} {α₁ : x₁ ⟶ x₂} {α₂ : x₂ ⟶ x₃} {α₃ : x₃ ⟶ x₄} {α₄ : x₄ ⟶ x₅}
    {e₀ e₁ e₂ e₃ e₄ e₅ : E}
    {ΔVX : T.obj x₅ ⟶ e₅} {ΔVQ : T.obj x₄ ⟶ e₄} {θ : e₄ ⟶ e₅}
    {γ : T.obj x₃ ⟶ e₁} {qx : e₁ ⟶ e₂} {δ : e₂ ⟶ e₃} {ε : e₃ ⟶ e₄}
    {γ' : T.obj x₂ ⟶ e₀} {q₂ : e₀ ⟶ e₁} {qL : e₀ ⟶ e₂}
    (h₀ : dmQ = α₁ ≫ α₂ ≫ α₃ ≫ α₄)
    (h₁ : T.map α₄ ≫ ΔVX = ΔVQ ≫ θ)
    (h₂ : T.map α₃ ≫ ΔVQ = γ ≫ qx ≫ δ ≫ ε)
    (h₃ : T.map α₂ ≫ γ = γ' ≫ q₂)
    (h₄ : q₂ ≫ qx = qL) :
    T.map dmQ ≫ ΔVX = T.map α₁ ≫ γ' ≫ qL ≫ δ ≫ ε ≫ θ := by
  rw [h₀, T.map_comp, T.map_comp, T.map_comp]
  simp only [Category.assoc]
  rw [h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄]

/-- The right-hand side of the derived restriction square: the derived coevaluation square and
the derived mate at the image of a complex, against the derived square of restrictions of
scalars. -/
private theorem bookR {D₂ : Type*} [Category D₂] (T' : D₂ ⥤ E) {d₁ d₂ d₃ d₄ d₅ d₆ : D₂}
    {Sinv : d₁ ⟶ d₆} {z₁ : d₁ ⟶ d₂} {z₂ : d₂ ⟶ d₃} {z₃ : d₃ ⟶ d₄} {z₄ : d₄ ⟶ d₅}
    {z₅ : d₅ ⟶ d₆} {z₁' : d₂ ⟶ d₁} {z₂' : d₃ ⟶ d₂}
    {x₁ x₂ x₃ x₄ w₁ cc y₃ y₇ : E}
    {ΔU : x₁ ⟶ cc} {dm'S : cc ⟶ T'.obj d₁}
    {s₁ : x₁ ⟶ x₂} {γ' : x₂ ⟶ x₃} {qσ : x₃ ⟶ x₄} {δ' : x₄ ⟶ w₁} {ε' : w₁ ⟶ cc}
    {dm'Q : w₁ ⟶ T'.obj d₂} {qm' : x₄ ⟶ y₃} {δ₂ : y₃ ⟶ T'.obj d₃}
    {qκ' : y₃ ⟶ y₇} {δ : y₇ ⟶ T'.obj d₄} {qR : x₃ ⟶ y₇}
    (h₁ : ΔU = s₁ ≫ γ' ≫ qσ ≫ δ' ≫ ε')
    (h₂ : ε' ≫ dm'S = dm'Q ≫ T'.map z₁')
    (h₃ : δ' ≫ dm'Q = qm' ≫ δ₂ ≫ T'.map z₂')
    (h₄ : Sinv = z₁ ≫ z₂ ≫ z₃ ≫ z₄ ≫ z₅)
    (h₅ : z₁' ≫ z₁ = 𝟙 d₂)
    (h₆ : z₂' ≫ z₂ = 𝟙 d₃)
    (h₇ : δ₂ ≫ T'.map z₃ = qκ' ≫ δ)
    (h₈ : qσ ≫ qm' ≫ qκ' = qR) :
    ΔU ≫ dm'S ≫ T'.map Sinv = s₁ ≫ γ' ≫ qR ≫ δ ≫ T'.map z₄ ≫ T'.map z₅ := by
  have hz : (z₂' ≫ z₁') ≫ z₁ ≫ z₂ ≫ z₃ ≫ z₄ ≫ z₅ = z₃ ≫ z₄ ≫ z₅ := by
    rw [Category.assoc, ← Category.assoc z₁' z₁, h₅, Category.id_comp, ← Category.assoc z₂' z₂,
      h₆, Category.id_comp]
  rw [h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% h₃, h₄, ← Functor.map_comp_assoc, ← Functor.map_comp, hz,
    T'.map_comp, T'.map_comp, reassoc_of% h₇, reassoc_of% h₈]

end RestrictionBookkeeping

/-! ### The two mates of the restriction transformation -/

section Mate

variable (R : C'ᵒᵖ ⥤ RingCat.{r})

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **The mate of the restriction transformation under the coevaluation adjunctions.** Restriction
along `a' : V' ⟶ U'` is a 2-square over taking sections over `U'` and over `V'`, which are the two
left adjoints, so it has a mate between the two coevaluations; by `coevRestrictionMate_apply` that
mate reindexes a family of sections along composition with `a'`. -/
def coevRestrictionMate {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    coevaluation.{r, v', u', w} R U' ⟶
      ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom ⋙
        coevaluation.{r, v', u', w} R V' :=
  (mateEquiv (coevaluationAdjunction.{r, v', u', w} R U')
    (coevaluationAdjunction.{r, v', u', w} R V')
    (TwoSquare.mk (𝟭 _) _ _ _
      ((Functor.leftUnitor _).hom ≫ PresheafOfModules.restriction R a')))

/-- **The mate of the restriction transformation is reindexing along `· ≫ a'`.** A family of
sections of the coevaluation over `U'` goes to the family over `V'` whose value at `d : W' ⟶ V'`
is its own value at `d ≫ a'`. -/
theorem coevRestrictionMate_apply {U' V' W' : C'ᵒᵖ} (a' : V' ⟶ U')
    (M : ModuleCat.{max u' v' r w} (R.obj U'))
    (x : ((coevaluation.{r, v', u', w} R U').obj M).obj W') (d : W' ⟶ V') :
    (((coevRestrictionMate.{r, v', u', w} R a').app M).app W').hom x d = x (d ≫ a') := by
  conv_rhs => rw [← Category.comp_id a']
  rfl

/-- **The coevaluation of a map of modules acts entrywise on families of sections**, the
coevaluation of a module being a product of copies of it. -/
theorem coevaluation_map_app_apply {U' W' : C'ᵒᵖ}
    {M₁ M₂ : ModuleCat.{max u' v' r w} (R.obj U')} (ψ : M₁ ⟶ M₂)
    (x : ((coevaluation.{r, v', u', w} R U').obj M₁).obj W') (c : W' ⟶ U') :
    (((coevaluation.{r, v', u', w} R U').map ψ).app W').hom x c = ψ.hom (x c) := rfl

/-- **The mate of the canonical derived restriction transformation under the derived coevaluation
adjunctions.** The derived sections over `U'` and over `V'` are left adjoints by
`dCoevaluationAdjunction` and the derived restriction transformation is a 2-square between them,
so it has a mate between the two derived coevaluations; by `dCoevRestrictionMate_app_Q` that mate
is the descent of `coevRestrictionMate`. -/
def dCoevRestrictionMate {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    dCoevaluation.{r, v', u', w} R U' ⟶
      DRestrict.{w} R a' ⋙ dCoevaluation.{r, v', u', w} R V' :=
  (mateEquiv (dCoevaluationAdjunction.{r, v', u', w} R U')
    (dCoevaluationAdjunction.{r, v', u', w} R V')
    (TwoSquare.mk (𝟭 _) _ _ _
      ((Functor.leftUnitor _).hom ≫ restrictionNatTrans.{w} R a')))

/-- **The unit identity characterizing the derived mate.** The unit of the derived coevaluation
adjunction over `U'` followed by the mate is the unit over `V'` followed by the derived
coevaluation of the restriction map; this is the unit square of `CategoryTheory.mateEquiv`. -/
theorem unit_dCoevRestrictionMate {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (K : DMod.{w} R) :
    (dCoevaluationAdjunction.{r, v', u', w} R U').unit.app K ≫
        (dCoevRestrictionMate.{r, v', u', w} R a').app ((RGamma.{w} R U').obj K) =
      (dCoevaluationAdjunction.{r, v', u', w} R V').unit.app K ≫
        (dCoevaluation.{r, v', u', w} R V').map (restrictionMap.{w} R a' K) := by
  have := unit_mateEquiv (dCoevaluationAdjunction.{r, v', u', w} R U')
    (dCoevaluationAdjunction.{r, v', u', w} R V')
    (TwoSquare.mk (𝟭 _) _ _ _
      ((Functor.leftUnitor _).hom ≫ restrictionNatTrans.{w} R a')) K
  simpa [dCoevRestrictionMate, restrictionNatTrans_app] using this

/-- The unit of the derived coevaluation adjunction, at the image of a cochain complex: it is
the image under `Q` of the chain-level unit, against the canonical factorizations of the two
descents. -/
private theorem dCoevaluationAdjunction_unit_app_Q (U' : C'ᵒᵖ)
    (P : CochainComplex (PresheafOfModules.{max u' v' r w} R) ℤ) :
    (dCoevaluationAdjunction.{r, v', u', w} R U').unit.app (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (coevaluationAdjunction.{r, v', u', w} R U').unit (ComplexShape.up ℤ)).app P) ≫
        (coevaluation.{r, v', u', w} R U').mapDerivedCategoryFactors.inv.app
          (((PresheafOfModules.evaluation.{max u' v' r w} R U').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (dCoevaluation.{r, v', u', w} R U').map
          ((PresheafOfModules.evaluation.{max u' v' r w} R
            U').mapDerivedCategoryFactors.inv.app P) := by
  let i₁ : CatCommSq
      ((PresheafOfModules.evaluation.{max u' v' r w} R U').mapHomologicalComplex
        (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q (RGamma.{w} R U') :=
    ⟨(PresheafOfModules.evaluation.{max u' v' r w} R U').mapDerivedCategoryFactors.symm⟩
  let i₂ : CatCommSq ((coevaluation.{r, v', u', w} R U').mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q DerivedCategory.Q
      (dCoevaluation.{r, v', u', w} R U') :=
    ⟨(coevaluation.{r, v', u', w} R U').mapDerivedCategoryFactors.symm⟩
  have h : dCoevaluationAdjunction.{r, v', u', w} R U' =
      ((coevaluationAdjunction.{r, v', u', w} R U').mapHomologicalComplex
        (ComplexShape.up ℤ)).localization
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (PresheafOfModules.{max u' v' r w} R) (ComplexShape.up ℤ))
        DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{max u' v' r w} (R.obj U'))
          (ComplexShape.up ℤ))
        (RGamma.{w} R U') (dCoevaluation.{r, v', u', w} R U') := rfl
  rw [h, Adjunction.localization_unit_app]
  rfl

/-- `dCoevaluation R U'` is the lift through the localization of the coevaluation on cochain
complexes. -/
private instance liftDCoevaluation (U' : C'ᵒᵖ) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{max u' v' r w} (R.obj U')) (ComplexShape.up ℤ))
      ((coevaluation.{r, v', u', w} R U').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      (dCoevaluation.{r, v', u', w} R U') :=
  ⟨(coevaluation.{r, v', u', w} R U').mapDerivedCategoryFactors⟩

/-- `DRestrict a' ⋙ dCoevaluation R V'` is the lift through the localization of the composite of
restriction of scalars and the coevaluation on cochain complexes. -/
private instance liftDRestrictCompDCoevaluation {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{max u' v' r w} (R.obj U')) (ComplexShape.up ℤ))
      ((ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom ⋙
        coevaluation.{r, v', u', w} R V').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)
      (DRestrict.{w} R a' ⋙ dCoevaluation.{r, v', u', w} R V') :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom).mapDerivedCategoryFactors
      (dCoevaluation.{r, v', u', w} R V') ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (coevaluation.{r, v', u', w} R V').mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm⟩

/-- The explicit descent of the chain-level mate to the derived categories: the lift through the
localization of the chain-level mate. -/
private def dCoevRestrictionDescent {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    dCoevaluation.{r, v', u', w} R U' ⟶
      DRestrict.{w} R a' ⋙ dCoevaluation.{r, v', u', w} R V' :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u' v' r w} (R.obj U')) (ComplexShape.up ℤ))
    ((coevaluation.{r, v', u', w} R U').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    ((ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom ⋙
      coevaluation.{r, v', u', w} R V').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    (dCoevaluation.{r, v', u', w} R U')
    (DRestrict.{w} R a' ⋙ dCoevaluation.{r, v', u', w} R V')
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      (coevRestrictionMate.{r, v', u', w} R a') (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The explicit descent, evaluated at the image of a cochain complex. -/
private theorem dCoevRestrictionDescent_app_Q {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (M : CochainComplex (ModuleCat.{max u' v' r w} (R.obj U')) ℤ) :
    (dCoevRestrictionDescent.{r, v', u', w} R a').app (DerivedCategory.Q.obj M) =
      (coevaluation.{r, v', u', w} R U').mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (coevRestrictionMate.{r, v', u', w} R a') (ComplexShape.up ℤ)).app M) ≫
        (coevaluation.{r, v', u', w} R V').mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        (dCoevaluation.{r, v', u', w} R V').map
          ((ModuleCat.restrictScalars.{max u' v' r w}
            (R.map a').hom).mapDerivedCategoryFactors.inv.app M) := by
  simp only [Functor.comp_obj, dCoevRestrictionDescent, liftDRestrictCompDCoevaluation,
    Localization.liftNatTrans_app, Localization.Lifting.iso, Functor.whiskerRight_app,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id, Category.id_comp]
  exact drop_id _ _ _ rfl _

/-- The chain-level unit square for the mate `coevRestrictionMate`, read on cochain
complexes. -/
private theorem unit_coevRestrictionMate_mapHomologicalComplex {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (P : CochainComplex (PresheafOfModules.{max u' v' r w} R) ℤ) :
    (NatTrans.mapHomologicalComplex (coevaluationAdjunction.{r, v', u', w} R V').unit
          (ComplexShape.up ℤ)).app P ≫
        ((coevaluation.{r, v', u', w} R V').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction R a')
            (ComplexShape.up ℤ)).app P) =
      (NatTrans.mapHomologicalComplex (coevaluationAdjunction.{r, v', u', w} R U').unit
          (ComplexShape.up ℤ)).app P ≫
        (NatTrans.mapHomologicalComplex (coevRestrictionMate.{r, v', u', w} R a')
          (ComplexShape.up ℤ)).app
          (((PresheafOfModules.evaluation.{max u' v' r w} R U').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h := unit_mateEquiv (coevaluationAdjunction.{r, v', u', w} R U')
    (coevaluationAdjunction.{r, v', u', w} R V')
    (TwoSquare.mk (𝟭 _) _ _ _
      ((Functor.leftUnitor _).hom ≫ PresheafOfModules.restriction R a')) (P.X n)
  simp only [Functor.id_obj, Functor.id_map, NatTrans.comp_app, Functor.leftUnitor_hom_app] at h
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  exact h.symm

/-- The unit square for the explicit descent, at the image of a cochain complex. -/
private theorem unit_dCoevRestrictionDescent_app_Q {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (P : CochainComplex (PresheafOfModules.{max u' v' r w} R) ℤ) :
    (dCoevaluationAdjunction.{r, v', u', w} R V').unit.app (DerivedCategory.Q.obj P) ≫
        (dCoevaluation.{r, v', u', w} R V').map
          (restrictionMap.{w} R a' (DerivedCategory.Q.obj P)) =
      (dCoevaluationAdjunction.{r, v', u', w} R U').unit.app (DerivedCategory.Q.obj P) ≫
        (dCoevRestrictionDescent.{r, v', u', w} R a').app
          ((RGamma.{w} R U').obj (DerivedCategory.Q.obj P)) := by
  have h₁ := (dCoevRestrictionDescent.{r, v', u', w} R a').naturality
    ((PresheafOfModules.evaluation.{max u' v' r w} R U').mapDerivedCategoryFactors.inv.app P)
  simp only [Functor.comp_obj, Functor.comp_map] at h₁
  have h₂ := dCoevRestrictionDescent_app_Q R a'
    (((PresheafOfModules.evaluation.{max u' v' r w} R U').mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)
  have h₅ :
      DerivedCategory.Q.map
          (((coevaluation.{r, v', u', w} R V').mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction R a')
              (ComplexShape.up ℤ)).app P)) ≫
        (coevaluation.{r, v', u', w} R V').mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((PresheafOfModules.evaluation.{max u' v' r w} R U').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) =
      (coevaluation.{r, v', u', w} R V').mapDerivedCategoryFactors.inv.app
          (((PresheafOfModules.evaluation.{max u' v' r w} R V').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        (dCoevaluation.{r, v', u', w} R V').map
          (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (PresheafOfModules.restriction R a') (ComplexShape.up ℤ)).app P)) :=
    (coevaluation.{r, v', u', w} R V').mapDerivedCategoryFactors.inv.naturality _
  have h₆ :
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (coevaluationAdjunction.{r, v', u', w} R V').unit (ComplexShape.up ℤ)).app P) ≫
        DerivedCategory.Q.map
          (((coevaluation.{r, v', u', w} R V').mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (PresheafOfModules.restriction R a')
              (ComplexShape.up ℤ)).app P)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (coevaluationAdjunction.{r, v', u', w} R U').unit (ComplexShape.up ℤ)).app P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (coevRestrictionMate.{r, v', u', w} R a') (ComplexShape.up ℤ)).app
          (((PresheafOfModules.evaluation.{max u' v' r w} R U').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      unit_coevRestrictionMate_mapHomologicalComplex]
  rw [dCoevaluationAdjunction_unit_app_Q R V' P, dCoevaluationAdjunction_unit_app_Q R U' P,
    restrictionMap_Q R a' P]
  exact unit_square_bookkeeping h₁ h₂ (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _) h₅ h₆

/-- The unit square for the explicit descent, at every object of the derived category. -/
private theorem unit_dCoevRestrictionDescent {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') (K : DMod.{w} R) :
    (dCoevaluationAdjunction.{r, v', u', w} R V').unit.app K ≫
        (dCoevaluation.{r, v', u', w} R V').map (restrictionMap.{w} R a' K) =
      (dCoevaluationAdjunction.{r, v', u', w} R U').unit.app K ≫
        (dCoevRestrictionDescent.{r, v', u', w} R a').app ((RGamma.{w} R U').obj K) := by
  have key : ((dCoevaluationAdjunction.{r, v', u', w} R V').unit ≫
        Functor.whiskerRight (restrictionNatTrans.{w} R a')
          (dCoevaluation.{r, v', u', w} R V') :
      𝟭 (DMod.{w} R) ⟶ RGamma.{w} R U' ⋙ DRestrict.{w} R a' ⋙
        dCoevaluation.{r, v', u', w} R V') =
      (dCoevaluationAdjunction.{r, v', u', w} R U').unit ≫
        Functor.whiskerLeft (RGamma.{w} R U')
          (dCoevRestrictionDescent.{r, v', u', w} R a') :=
    Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (PresheafOfModules.{max u' v' r w} R) (ComplexShape.up ℤ))
      fun P => unit_dCoevRestrictionDescent_app_Q R a' P
  exact NatTrans.congr_app key K

/-- **The derived mate is the descent of the chain-level mate.** -/
private theorem dCoevRestrictionMate_eq_descent {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    dCoevRestrictionMate.{r, v', u', w} R a' =
      dCoevRestrictionDescent.{r, v', u', w} R a' := by
  refine mateEquiv_eq_of_unit (dCoevaluationAdjunction.{r, v', u', w} R U')
    (dCoevaluationAdjunction.{r, v', u', w} R V')
    (TwoSquare.mk (𝟭 _) _ _ _
      ((Functor.leftUnitor _).hom ≫ restrictionNatTrans.{w} R a'))
    (TwoSquare.mk _ _ _ _ (dCoevRestrictionDescent.{r, v', u', w} R a')) fun K => ?_
  simpa only [Functor.id_obj, Functor.comp_obj, Functor.id_map, NatTrans.comp_app,
    Functor.leftUnitor_hom_app, Category.id_comp, restrictionNatTrans_app, TwoSquare.mk] using
    unit_dCoevRestrictionDescent R a' K

/-- **Taking mates commutes with descent to the derived category.** The mate of the derived
restriction transformation under the two derived coevaluation adjunctions, evaluated at the image
of a cochain complex `M`, is the image under `Q` of the mate of the chain-level restriction
transformation under the two chain-level coevaluation adjunctions, conjugated by the canonical
factorizations of the descents of the coevaluation over `U'`, of the coevaluation over `V'` and of
restriction of scalars along `R(a')`. -/
theorem dCoevRestrictionMate_app_Q {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (M : CochainComplex (ModuleCat.{max u' v' r w} (R.obj U')) ℤ) :
    (dCoevRestrictionMate.{r, v', u', w} R a').app (DerivedCategory.Q.obj M) =
      (coevaluation.{r, v', u', w} R U').mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (coevRestrictionMate.{r, v', u', w} R a') (ComplexShape.up ℤ)).app M) ≫
        (coevaluation.{r, v', u', w} R V').mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M) ≫
        (dCoevaluation.{r, v', u', w} R V').map
          ((ModuleCat.restrictScalars.{max u' v' r w}
            (R.map a').hom).mapDerivedCategoryFactors.inv.app M) := by
  rw [dCoevRestrictionMate_eq_descent, dCoevRestrictionDescent_app_Q]

/-- **Taking mates commutes with descent to the derived category**, with the two canonical
factorizations of the descents of `restrictScalars` and of the coevaluation over `V'` assembled
into the canonical factorization of the descent of their composite followed by the comparison of
the descent of a composite with the composite of the descents. -/
theorem dCoevRestrictionMate_app_Q' {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (M : CochainComplex (ModuleCat.{max u' v' r w} (R.obj U')) ℤ) :
    (dCoevRestrictionMate.{r, v', u', w} R a').app (DerivedCategory.Q.obj M) =
      (coevaluation.{r, v', u', w} R U').mapDerivedCategoryFactors.hom.app M ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (coevRestrictionMate.{r, v', u', w} R a') (ComplexShape.up ℤ)).app M) ≫
        (ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom ⋙
          coevaluation.{r, v', u', w} R V').mapDerivedCategoryFactors.inv.app M ≫
        (mapDerivedCategoryCompIso (ModuleCat.restrictScalars.{max u' v' r w} (R.map a').hom)
          (coevaluation.{r, v', u', w} R V')).hom.app (DerivedCategory.Q.obj M) := by
  rw [dCoevRestrictionMate_app_Q, factors_inv_comp_compIso_hom_app_Q]
  rfl

end Mate

/-! ### Conjugate transformations, pointwise -/

section Conjugate

universe s₂ s₃ t₅ t₆

variable {A : Type t₅} [Category.{s₂} A] {B : Type t₆} [Category.{s₃} B]
  {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}

/-- **Closed formula for a component of a conjugate transformation.** The component at `Y` is the
unit of the second adjunction followed by the image of the given transformation and of the counit
of the first. -/
theorem conjugateEquiv_app_eq (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) (Y : B) :
    (conjugateEquiv adj₁ adj₂ α).app Y =
      adj₂.unit.app (R₁.obj Y) ≫ R₂.map (α.app (R₁.obj Y) ≫ adj₁.counit.app Y) := by
  have hn := (conjugateEquiv adj₁ adj₂ α).naturality (adj₁.counit.app Y)
  have hu := unit_conjugateEquiv adj₁ adj₂ α (R₁.obj Y)
  have ht := adj₁.right_triangle_components (Y := Y)
  simp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [Functor.map_comp, ← Category.assoc, ← hu, Category.assoc, ← hn, ← Category.assoc, ht]
  simp

end Conjugate

/-! ### The chain-level restriction square for the coevaluations -/

section RestrictionSquare

variable (W' : C'ᵒᵖ)

/-- **The square of restrictions of scalars attached to `a' : V' ⟶ U'`.** Restricting along the
structure map at `U'` and then along `O(F a')` agrees with restricting along `O'(a')` and then
along the structure map at `V'`: both are restriction along the common diagonal, the underlying
square of rings commuting by naturality of `φ`. -/
def restrictScalarsStructureSquare {U' V' : C'ᵒᵖ} (a' : V' ⟶ U') :
    ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom ⋙
        ModuleCat.restrictScalars.{max u v u' v' r} ((F.op ⋙ O).map a').hom ≅
      ModuleCat.restrictScalars.{max u v u' v' r} (O'.map a').hom ⋙
        ModuleCat.restrictScalars.{max u v u' v' r} (φ.app V').hom :=
  (ModuleCat.restrictScalarsComp'.{max u v u' v' r} ((F.op ⋙ O).map a').hom (φ.app U').hom
      (φ.app V' ≫ O'.map a').hom (by rw [(φ.naturality a').symm]; rfl)).symm ≪≫
    ModuleCat.restrictScalarsComp'.{max u v u' v' r} (φ.app V').hom (O'.map a').hom
      (φ.app V' ≫ O'.map a').hom rfl

/-- **The square of restrictions of scalars is the identity on underlying elements**, restriction
of scalars leaving the underlying abelian group unchanged. -/
theorem restrictScalarsStructureSquare_hom_app_apply {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (Y : ModuleCat.{max u v u' v' r} (O'.obj U'))
    (z : ((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom ⋙
      ModuleCat.restrictScalars.{max u v u' v' r} ((F.op ⋙ O).map a').hom).obj Y)) :
    ((restrictScalarsStructureSquare F O O' φ a').hom.app Y).hom z = z := rfl

/-- **Unit then counit of the extension/restriction adjunction of modules is the identity on
underlying elements**, which is the right triangle identity of that adjunction. -/
theorem extendRestrict_unit_counit (U' : C'ᵒᵖ)
    (N : ModuleCat.{max u v u' v' r} (O'.obj U'))
    (m : ((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).obj N)) :
    ((Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{max u v u' v'}
          (φ.app U').hom).counit.app N).hom
        (((Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{max u v u' v'}
          (φ.app U').hom).unit.app
            ((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).obj N)).hom m) = m :=
  ConcreteCategory.congr_hom
    ((Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{max u v u' v'}
      (φ.app U').hom).right_triangle_components (Y := N)) m

/-- **The coevaluation/restriction-of-scalars square is the identity on families of
sections.** -/
theorem coevaluationRestrictScalarsSquare_hom_app_apply (U' : C'ᵒᵖ)
    (Y : ModuleCat.{max u v u' v' r} (O'.obj U'))
    (y : ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).obj
      ((coevaluation.{r, v', u', max u v} O' U').obj Y)).obj W') (c : W' ⟶ U') :
    ((((coevaluationRestrictScalarsSquare F O O' φ U').hom.app Y).app W').hom y) c = y c := by
  conv_rhs => rw [← Category.comp_id c]
  dsimp only [coevaluationRestrictScalarsSquare]
  rw [conjugateIsoEquiv_apply_hom, conjugateEquiv_app_eq]
  exact congrArg (fun m => (coevaluationProj.{r, v', u', max u v} O' U' Y).hom m)
    (extendRestrict_unit_counit F O O' φ U'
      (((coevaluation.{r, v', u', max u v} O' U').obj Y).obj U')
      ((((coevaluation.{r, v', u', max u v} O' U').obj Y).map c).hom y))

/-- **Restriction of scalars of presheaves of modules is the identity on underlying elements**, it
changing only the action of the ring. -/
theorem restrictScalars_map_app_apply {M₁ M₂ : PresheafOfModules.{max u v u' v' r} O'}
    (f : M₁ ⟶ M₂)
    (z : (((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).obj M₁).obj W')) :
    ((((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).map f).app W').hom z) =
      (f.app W').hom z := rfl

/-- **The chain-level restriction square for the coevaluations.** The mate of the restriction
transformation commutes with the coevaluation/restriction-of-scalars squares, through the square
of restrictions of scalars attached to `a'`. -/
theorem coevRestrictionMate_restrictScalarsSquare {U' V' : C'ᵒᵖ} (a' : V' ⟶ U')
    (Y : ModuleCat.{max u v u' v' r} (O'.obj U')) :
    (PresheafOfModules.restrictScalars.{max u v u' v' r} φ).map
          ((coevRestrictionMate.{r, v', u', max u v} O' a').app Y) ≫
        (coevaluationRestrictScalarsSquare F O O' φ V').hom.app
          ((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map a').hom).obj Y) =
      (coevaluationRestrictScalarsSquare F O O' φ U').hom.app Y ≫
        (coevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
            ((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).obj Y) ≫
          (coevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map
            ((restrictScalarsStructureSquare F O O' φ a').hom.app Y) := by
  apply PresheafOfModules.hom_ext
  intro W'
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  funext d
  have hL : ∀ u : ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).obj
        ((coevaluation.{r, v', u', max u v} O' U').obj Y)).obj W',
      (((coevaluationRestrictScalarsSquare F O O' φ V').hom.app
              ((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map a').hom).obj Y)).app W').hom
          ((((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).map
            ((coevRestrictionMate.{r, v', u', max u v} O' a').app Y)).app W').hom u) d =
        u (d ≫ a') := fun u =>
    (coevaluationRestrictScalarsSquare_hom_app_apply F O O' φ W' V' _ _ d).trans
      (coevRestrictionMate_apply.{r, v', u', max u v} O' a' Y u d)
  have hR : ∀ u : ((coevaluation.{r, v', u', max u v} (F.op ⋙ O) U').obj
        ((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).obj Y)).obj W',
      (((coevaluation.{r, v', u', max u v} (F.op ⋙ O) V').map
              ((restrictScalarsStructureSquare F O O' φ a').hom.app Y)).app W').hom
          ((((coevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a').app
            ((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).obj Y)).app W').hom u)
          d = u (d ≫ a') := fun u =>
    coevRestrictionMate_apply.{r, v', u', max u v} (F.op ⋙ O) a' _ u d
  simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply]
  rw [hL, hR, coevaluationRestrictScalarsSquare_hom_app_apply]

/-- **The chain-level restriction square, read on cochain complexes**: it is
`coevRestrictionMate_restrictScalarsSquare` in each degree. -/
theorem coevRestrictionMate_restrictScalarsSquare_mapHomologicalComplex {U' V' : C'ᵒᵖ}
    (a' : V' ⟶ U') (M : CochainComplex (ModuleCat.{max u v u' v' r} (O'.obj U')) ℤ) :
    ((PresheafOfModules.restrictScalars.{max u v u' v' r} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (coevRestrictionMate.{r, v', u', max u v} O' a')
          (ComplexShape.up ℤ)).app M) ≫
      (NatIso.mapHomologicalComplex (coevaluationRestrictScalarsSquare F O O' φ V')
          (ComplexShape.up ℤ)).hom.app
        (((ModuleCat.restrictScalars.{max u v u' v' r} (O'.map a').hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) =
    (NatIso.mapHomologicalComplex (coevaluationRestrictScalarsSquare F O O' φ U')
        (ComplexShape.up ℤ)).hom.app M ≫
      (NatTrans.mapHomologicalComplex (coevRestrictionMate.{r, v', u', max u v} (F.op ⋙ O) a')
          (ComplexShape.up ℤ)).app
        (((ModuleCat.restrictScalars.{max u v u' v' r} (φ.app U').hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≫
      ((coevaluation.{r, v', u', max u v} (F.op ⋙ O) V').mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex (restrictScalarsStructureSquare F O O' φ a')
          (ComplexShape.up ℤ)).hom.app M) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  exact coevRestrictionMate_restrictScalarsSquare F O O' φ a' (M.X n)

end RestrictionSquare

end Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent

end
