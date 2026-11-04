module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverACover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingCompatibilityTop

/-!
# The coherence of the dictionary of Situation 0D67 along a chain of three opens

Let `(X, 𝒪_X)` be a ringed space and `S` a system of locally given derived objects on it, as in
Situation 0D67.  `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrict` is *the
dictionary*: it identifies the restriction `S` displays, from an open `O` to a smaller open `U`,
with extension by zero along `O` followed by derived restriction to `U`.  What
`Stacks.DerivedGlueing.twoOpenGlueingOver_top_of_coherence` is still owed is that this dictionary
is coherent along a chain `W ≤ U ≤ O`: the dictionary over `W` is the comparison of restriction
in two steps, followed by the dictionary over `U`, followed by the factorisation of
[Stacks, Tag 0D5S] of derived restriction to `W` through `U`.  This file proves that coherence.

The proof is in three layers.  Transported along
`Stacks.DerivedGlueing.restrictionIsoMapDerivedCategory` and
`Stacks.DerivedGlueing.restrictionComp_eq_mapDerivedCategoryComp`, the system disappears from the
statement: what is left is an identity between the composition comparisons of the functors
induced on derived categories by extension by zero and by restriction, and that identity is
proved once and for all for four arbitrary exact functors, in
`Stacks.DerivedGlueing.compIso_comp_coherence`.  Putting the system back is the chase
`Stacks.DerivedGlueing.jStar_trans_chase`, and passing from the degreewise restriction to derived
restriction is `Stacks.DerivedGlueing.comp_transport`.

## Main definitions

* `Stacks.DerivedGlueing.derivedNatTrans`: the derived form of a natural transformation of exact
  functors.
* `Stacks.DerivedGlueing.derivedCompToId` and
  `Stacks.DerivedGlueing.derivedCompToIdOfIso`: the derived forms of a counit-shaped
  transformation `F ⋙ G ⟶ 𝟭` and of a unit-shaped isomorphism.
* `Stacks.DerivedGlueing.derivedJShriekCounit`: the derived counit of extension by zero on an
  open.
* `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoJStar`: the displayed restriction read as
  extension by zero followed by the *degreewise* restriction — the dictionary without its last
  step.

## Main results

* `Stacks.DerivedGlueing.compIso_comp_coherence`: **the coherence, for four arbitrary exact
  functors.**  For `a`, `b`, `d`, `e` and a counit-shaped `η : b ⋙ d ⟶ 𝟭`, the two ways of
  comparing `D(a) ⋙ D(b) ⋙ D(d) ⋙ D(e)` with `D(a ⋙ b) ⋙ D(d ⋙ e)` agree.
* `Stacks.DerivedGlueing.derivedCompToIdOfIso_hom_app_map`: the derived right-triangle identity
  for an adjunction whose unit is invertible.
* `Stacks.DerivedGlueing.dictionary_at_one_open`: the dictionary at one open, read as derived
  restriction of a single morphism.
* `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoJStar_hom_app_trans` and
  `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrict_hom_app_trans`: **the
  coherence of the dictionary along `W ≤ U ≤ O`**, in the degreewise and in the derived-pullback
  spelling.

## Implementation notes

Each step of the chase is stated as a lemma with every object and every morphism a variable and
applied by `exact`, so that each identification is paid as one definitional unification at
`default` transparency.  The two components of a comparison are taken as *morphisms* with their
cancellations as hypotheses rather than as a `CategoryTheory.Iso`: at the point of use they
arrive as `α.hom.app A` and `α.inv.app A`, and recovering `α.app A` from those is a higher-order
unification the elaborator does not solve.

`StacksFrontier/CategoryTheory/Localization/NatTransMapDerivedCategory.lean` is deliberately *not*
imported, although it carries the derived form of a natural transformation that
`Stacks.DerivedGlueing.derivedNatTrans` duplicates.  Importing it makes the application of
`Stacks.DerivedGlueing.twoOpenGlueingOver_top_of_coherence` fail with a kernel deterministic
timeout: its own import closure reaches
`StacksFrontier/AlgebraicGeometry/Perfect/Approximation/OpenSubscheme.lean`, after which the terms
elaborated here are no longer the ones that file's statement was elaborated against.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction

namespace Stacks.DerivedGlueing

universe w₀ w₁ w₂ w₃ v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃ u

section Generic

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] [HasDerivedCategory.{w₃} C]

/-- The identity comparison on the image of the localization. -/
theorem mapDerivedCategoryIdIso_hom_app_Q
    (P : HomologicalComplex A (ComplexShape.up ℤ)) :
    Stacks.Homology.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Q.obj P) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app P) := by
  simp [Stacks.Homology.mapDerivedCategoryIdIso, Localization.Lifting.iso]

/-- **The derived form of a natural transformation of exact functors.**  It is the lift through
`DerivedCategory.Q` of the degreewise transformation. -/
def derivedNatTrans {F G : A ⥤ B} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (η : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- `Stacks.DerivedGlueing.derivedNatTrans` on the image of the localization. -/
theorem derivedNatTrans_app_Q {F G : A ⥤ B} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (η : F ⟶ G)
    (P : HomologicalComplex A (ComplexShape.up ℤ)) :
    (derivedNatTrans η).app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app P) ≫
        G.mapDerivedCategoryFactors.inv.app P := by
  simp [derivedNatTrans, Localization.Lifting.iso]

/-- **The derived form of a counit-shaped transformation.** -/
def derivedCompToId (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)]
    [PreservesFiniteColimits (F ⋙ G)] (η : F ⋙ G ⟶ 𝟭 A) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶ 𝟭 (DerivedCategory A) :=
  (mapDerivedCategoryCompIso F G).hom ≫ derivedNatTrans η ≫
    Stacks.Homology.mapDerivedCategoryIdIso.hom

/-- `Stacks.DerivedGlueing.derivedCompToId` on the image of the localization. -/
theorem derivedCompToId_app_Q (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)]
    [PreservesFiniteColimits (F ⋙ G)] (η : F ⋙ G ⟶ 𝟭 A)
    (P : HomologicalComplex A (ComplexShape.up ℤ)) :
    (derivedCompToId F G η).app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app P ≫
            (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app P) := by
  simp only [derivedCompToId, NatTrans.comp_app, mapDerivedCategoryCompIso_hom_app_Q,
    derivedNatTrans_app_Q, mapDerivedCategoryIdIso_hom_app_Q, Category.assoc,
    Iso.inv_hom_id_app_assoc, DerivedCategory.Q.map_comp]

end Generic

section Coherence

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasDerivedCategory.{w₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

variable (a : C₀ ⥤ C₁) [a.Additive] [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  (b : C₁ ⥤ C₂) [b.Additive] [PreservesFiniteLimits b] [PreservesFiniteColimits b]
  (d : C₂ ⥤ C₁) [d.Additive] [PreservesFiniteLimits d] [PreservesFiniteColimits d]
  (e : C₁ ⥤ C₃) [e.Additive] [PreservesFiniteLimits e] [PreservesFiniteColimits e]
  [(a ⋙ b).Additive] [PreservesFiniteLimits (a ⋙ b)] [PreservesFiniteColimits (a ⋙ b)]
  [(b ⋙ d).Additive] [PreservesFiniteLimits (b ⋙ d)] [PreservesFiniteColimits (b ⋙ d)]
  [(d ⋙ e).Additive] [PreservesFiniteLimits (d ⋙ e)] [PreservesFiniteColimits (d ⋙ e)]
  [(a ⋙ e).Additive] [PreservesFiniteLimits (a ⋙ e)] [PreservesFiniteColimits (a ⋙ e)]

/-- **The chase behind `Stacks.DerivedGlueing.compIso_comp_coherence`**, in three arbitrary
categories with two arbitrary functors and every object and morphism a variable. -/
private theorem coherence_chase {𝒳 𝒴 𝒵 : Type*} [Category 𝒳] [Category 𝒴] [Category 𝒵]
    (D : 𝒳 ⥤ 𝒴) (E : 𝒴 ⥤ 𝒵) {x₀ x₁ x₂ x₃ : 𝒳} {y₁ y₂ y₃ : 𝒴} {z₁ z₂ z₃ z₄ z₅ : 𝒵}
    {Gab : x₀ ⟶ x₁} {pab : x₁ ⟶ x₂} {bpa : x₀ ⟶ x₃} {pb : x₃ ⟶ x₂}
    {pd : D.obj x₂ ⟶ y₁} {cq : D.obj x₃ ⟶ y₂} {cc : D.obj x₀ ⟶ y₃} {pa : y₃ ⟶ y₂}
    {qm : y₁ ⟶ y₂} {Gde : E.obj (D.obj x₁) ⟶ z₁} {Jab : z₁ ⟶ z₂}
    {Gdeq : E.obj (D.obj x₂) ⟶ z₂} {pde : z₂ ⟶ z₃} {pe₁ : E.obj y₁ ⟶ z₃}
    {Gae : E.obj y₃ ⟶ z₄} {pae : z₄ ⟶ z₅} {pe₂ : E.obj y₂ ⟶ z₅} {M : z₄ ⟶ z₁}
    {qtp : z₃ ⟶ z₅}
    (h1 : Gab ≫ pab = bpa ≫ pb) (h2 : Gdeq ≫ pde = E.map pd ≫ pe₁)
    (h3 : Gae ≫ pae = E.map pa ≫ pe₂) (h4 : M ≫ Jab ≫ pde ≫ qtp = pae)
    (h5 : cq = D.map pb ≫ pd ≫ qm) (h6 : D.map bpa ≫ cq = cc ≫ pa)
    (h7 : E.map (D.map pab) ≫ Gdeq = Gde ≫ Jab) (h8 : E.map qm ≫ pe₂ = pe₁ ≫ qtp)
    (hmono : Mono (Jab ≫ pde ≫ qtp)) :
    E.map (D.map Gab) ≫ Gde = E.map cc ≫ Gae ≫ M := by
  have hL : (E.map (D.map Gab) ≫ Gde) ≫ Jab ≫ pde ≫ qtp =
      E.map (D.map bpa) ≫ E.map (D.map pb) ≫ E.map pd ≫ pe₁ ≫ qtp :=
    calc (E.map (D.map Gab) ≫ Gde) ≫ Jab ≫ pde ≫ qtp
        = E.map (D.map Gab) ≫ (Gde ≫ Jab) ≫ pde ≫ qtp := by simp only [Category.assoc]
      _ = E.map (D.map Gab) ≫ (E.map (D.map pab) ≫ Gdeq) ≫ pde ≫ qtp := by rw [h7]
      _ = E.map (D.map (Gab ≫ pab)) ≫ (Gdeq ≫ pde) ≫ qtp := by
            simp only [Functor.map_comp, Category.assoc]
      _ = E.map (D.map (bpa ≫ pb)) ≫ (E.map pd ≫ pe₁) ≫ qtp := by rw [h1, h2]
      _ = E.map (D.map bpa) ≫ E.map (D.map pb) ≫ E.map pd ≫ pe₁ ≫ qtp := by
            simp only [Functor.map_comp, Category.assoc]
  have hR : (E.map cc ≫ Gae ≫ M) ≫ Jab ≫ pde ≫ qtp =
      E.map (D.map bpa) ≫ E.map (D.map pb) ≫ E.map pd ≫ pe₁ ≫ qtp :=
    calc (E.map cc ≫ Gae ≫ M) ≫ Jab ≫ pde ≫ qtp
        = E.map cc ≫ Gae ≫ M ≫ Jab ≫ pde ≫ qtp := by simp only [Category.assoc]
      _ = E.map cc ≫ Gae ≫ pae := by rw [h4]
      _ = E.map (cc ≫ pa) ≫ pe₂ := by
            rw [h3]
            simp only [Functor.map_comp, Category.assoc]
      _ = E.map (D.map bpa ≫ cq) ≫ pe₂ := by rw [h6]
      _ = E.map (D.map bpa) ≫ E.map (D.map pb) ≫ E.map pd ≫ E.map qm ≫ pe₂ := by
            rw [h5]
            simp only [Functor.map_comp, Category.assoc]
      _ = E.map (D.map bpa) ≫ E.map (D.map pb) ≫ E.map pd ≫ pe₁ ≫ qtp := by rw [h8]
  exact (cancel_mono (Jab ≫ pde ≫ qtp)).mp (hL.trans hR.symm)

/-- For exact functors `a`, `b`, `d`, `e`, a transformation `η : b ⋙ d ⟶ 𝟭` and an isomorphism
`θ : (a ⋙ b) ⋙ (d ⋙ e) ≅ a ⋙ e` whose hom is `a` whiskered with `η` whiskered with `e`, the two
comparisons of `D(a) ⋙ D(b) ⋙ D(d) ⋙ D(e)` with `D(a ⋙ b) ⋙ D(d ⋙ e)` agree: composing the
comparisons for `a ⋙ b` and for `d ⋙ e` equals `Stacks.DerivedGlueing.derivedCompToId` of `η`
followed by the comparisons for `a ⋙ e` and along `θ`. -/
theorem compIso_comp_coherence (η : b ⋙ d ⟶ 𝟭 C₁) (θ : (a ⋙ b) ⋙ (d ⋙ e) ≅ a ⋙ e)
    (hθ : θ.hom = Functor.whiskerLeft a (Functor.whiskerRight η e)) :
    (Functor.whiskerRight (mapDerivedCategoryCompIso a b).hom
          (d.mapDerivedCategory ⋙ e.mapDerivedCategory) ≫
        Functor.whiskerLeft (a ⋙ b).mapDerivedCategory (mapDerivedCategoryCompIso d e).hom :
      a.mapDerivedCategory ⋙ b.mapDerivedCategory ⋙ d.mapDerivedCategory ⋙
          e.mapDerivedCategory ⟶
        (a ⋙ b).mapDerivedCategory ⋙ (d ⋙ e).mapDerivedCategory) =
      (Functor.whiskerLeft a.mapDerivedCategory
          (Functor.whiskerRight (derivedCompToId b d η) e.mapDerivedCategory) :
        a.mapDerivedCategory ⋙ b.mapDerivedCategory ⋙ d.mapDerivedCategory ⋙
            e.mapDerivedCategory ⟶
          a.mapDerivedCategory ⋙ e.mapDerivedCategory) ≫
        (mapDerivedCategoryCompIso a e).hom ≫
        (mapDerivedCategoryComp (a ⋙ b) (d ⋙ e) (a ⋙ e) θ).hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C₀ (ComplexShape.up ℤ)) fun P => ?_
  have h1 := mapDerivedCategoryCompIso_hom_app_Q_comp a b P
  have h2 := mapDerivedCategoryCompIso_hom_app_Q_comp d e
    (((a ⋙ b).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have h3 := mapDerivedCategoryCompIso_hom_app_Q_comp a e P
  have h4 := mapDerivedCategoryComp_factors (a ⋙ b) (d ⋙ e) (a ⋙ e) θ P
  have h5 := derivedCompToId_app_Q b d η ((a.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
  have h6 := (derivedCompToId b d η).naturality (a.mapDerivedCategoryFactors.hom.app P)
  have h7 := (mapDerivedCategoryCompIso d e).hom.naturality
    ((a ⋙ b).mapDerivedCategoryFactors.hom.app P)
  have hθ' : (Functor.mapHomologicalComplexCompIso (Iso.refl ((a ⋙ b) ⋙ (d ⋙ e)))
          (ComplexShape.up ℤ)).hom.app P ≫
        (NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app P =
      (e.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app
            ((a.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app
            ((a.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) := by
    ext n
    simp [hθ]
  have h8 : e.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app
              ((a.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
            (Functor.mapHomologicalComplexIdIso C₁ (ComplexShape.up ℤ)).hom.app
              ((a.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))) ≫
        e.mapDerivedCategoryFactors.hom.app ((a.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
      e.mapDerivedCategoryFactors.hom.app ((d.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((a ⋙ b).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl ((a ⋙ b) ⋙ (d ⋙ e))) (ComplexShape.up ℤ)).hom.app P) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app P) := by
    rw [← DerivedCategory.Q.map_comp, hθ']
    exact e.mapDerivedCategoryFactors.hom.naturality _
  simp only [Functor.comp_map, Functor.id_map] at h6 h7
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj]
  refine coherence_chase d.mapDerivedCategory e.mapDerivedCategory h1 h2 h3 h4 h5 h6 h7 h8 ?_
  have : IsIso ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app P) :=
    inferInstanceAs
      (IsIso ((NatIso.mapHomologicalComplex θ (ComplexShape.up ℤ)).hom.app P))
  infer_instance

end Coherence

section Chases

/-- **The chase behind `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoJStar_hom_app_trans`**,
with two arbitrary functors and every object and morphism a variable.  The two components of
each comparison are taken as morphisms with their cancellations as hypotheses rather than as
`CategoryTheory.Iso`s, because at the point of use they arrive as `α.hom.app A` and
`α.inv.app A`, from which the elaborator cannot recover `α.app A`. -/
private theorem jStar_trans_chase {𝒱 𝒲 : Type*} [Category 𝒱] [Category 𝒲] (Φ R : 𝒱 ⥤ 𝒲)
    {Y Y' Z : 𝒱} {p₀ p₁ p₂ p₃ : 𝒲} {ρWO : p₀ ⟶ p₁} {gi₃ : p₁ ⟶ p₂} {g₃ : p₂ ⟶ p₁}
    {rc : p₀ ⟶ p₃} {ρWU : p₃ ⟶ R.obj Y} {gi₂ : R.obj Y ⟶ Φ.obj Y}
    {gi₂' : R.obj Y' ⟶ Φ.obj Y'} {g₂ : Φ.obj Y' ⟶ R.obj Y'} {M : p₁ ⟶ R.obj Y'}
    {Mi : R.obj Y' ⟶ p₁} {ρUO : Y ⟶ Y'} {gi₁ : Y' ⟶ Z} {g₁ : Z ⟶ Y'} {t : Φ.obj Z ⟶ p₂}
    (hn : R.map ρUO ≫ gi₂' = gi₂ ≫ Φ.map ρUO)
    (hc : ρWO ≫ M = rc ≫ ρWU ≫ R.map ρUO)
    (hs : Φ.map g₁ ≫ g₂ = t ≫ g₃ ≫ M)
    (h₁ : gi₁ ≫ g₁ = 𝟙 Y') (h₂ : gi₂' ≫ g₂ = 𝟙 (R.obj Y')) (h₃ : g₃ ≫ gi₃ = 𝟙 p₂)
    (hM : M ≫ Mi = 𝟙 p₁) :
    ρWO ≫ gi₃ = rc ≫ (ρWU ≫ gi₂) ≫ Φ.map (ρUO ≫ gi₁) ≫ t := by
  have ht : Φ.map g₁ ≫ g₂ ≫ Mi ≫ gi₃ = t := by
    rw [← Category.assoc (Φ.map g₁) g₂, hs]
    simp only [Category.assoc]
    rw [← Category.assoc M Mi, hM, Category.id_comp, h₃, Category.comp_id]
  have key : M ≫ gi₂' ≫ Φ.map gi₁ ≫ t = gi₃ := by
    rw [← ht, ← Category.assoc (Φ.map gi₁) (Φ.map g₁), ← Functor.map_comp, h₁,
      Φ.map_id, Category.id_comp, ← Category.assoc gi₂' g₂, h₂, Category.id_comp,
      ← Category.assoc M Mi, hM, Category.id_comp]
  rw [← key, reassoc_of% hc, reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]

/-- Transport of an identity of composites along a natural transformation. -/
private theorem comp_transport {𝒜 : Type*} [Category 𝒜] {a b c d e f : 𝒜} {x : a ⟶ d}
    {rc : a ⟶ b} {y : b ⟶ c} {sm : c ⟶ d} {p₁ : c ⟶ e} {p₂ : d ⟶ f} {dm : e ⟶ f}
    (hx : x = rc ≫ y ≫ sm) (hnat : sm ≫ p₂ = p₁ ≫ dm) :
    x ≫ p₂ = rc ≫ (y ≫ p₁) ≫ dm := by
  simp only [hx, Category.assoc, hnat]

end Chases

section RightTriangle

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)]

/-- **The derived form of a unit-shaped isomorphism.** -/
def derivedCompToIdOfIso (ε : F ⋙ G ≅ 𝟭 A) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  mapDerivedCategoryCompIso F G ≪≫ mapDerivedCategoryCongr ε ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso

/-- `Stacks.DerivedGlueing.derivedCompToIdOfIso` on the image of the localization. -/
theorem derivedCompToIdOfIso_hom_app_Q (ε : F ⋙ G ≅ 𝟭 A)
    (P : HomologicalComplex A (ComplexShape.up ℤ)) :
    (derivedCompToIdOfIso F G ε).hom.app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ)).hom.app P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app P) := by
  simp only [derivedCompToIdOfIso, Iso.trans_hom, NatTrans.comp_app,
    mapDerivedCategoryCompIso_hom_app_Q, mapDerivedCategoryCongr_hom_app_Q,
    mapDerivedCategoryIdIso_hom_app_Q, Category.assoc, Iso.inv_hom_id_app_assoc]

omit [HasDerivedCategory A] [Abelian B] [HasDerivedCategory B] [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)]
  [PreservesFiniteColimits (F ⋙ G)] in
/-- **The degreewise right-triangle identity for an adjunction whose unit is invertible.** -/
theorem unitIso_hom_app_eq_map_counit (adj : F ⊣ G) (ε : F ⋙ G ≅ 𝟭 A)
    (hε : ε.inv = adj.unit) (Y : B) : ε.hom.app (G.obj Y) = G.map (adj.counit.app Y) := by
  have h : ε.inv.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) := by
    rw [hε]
    exact adj.right_triangle_components Y
  exact ((cancel_epi (ε.inv.app (G.obj Y))).mp
    (h.trans (ε.inv_hom_id_app (G.obj Y)).symm)).symm

/-- A natural isomorphism to the identity, conjugated by an isomorphism of objects. -/
theorem natIso_id_app_conj {D : Type*} [Category D] {H : D ⥤ D} (α : H ≅ 𝟭 D) {x y : D}
    (ζ : x ≅ y) : α.hom.app x = H.map ζ.hom ≫ α.hom.app y ≫ ζ.inv := by
  simp

omit [HasDerivedCategory A] [HasDerivedCategory B] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] in
/-- `Stacks.DerivedGlueing.unitIso_hom_app_eq_map_counit` prolonged to complexes. -/
theorem mapHomologicalComplex_right_triangle (adj : F ⊣ G) (ε : F ⋙ G ≅ 𝟭 A)
    (hε : ε.inv = adj.unit) (Z : HomologicalComplex B (ComplexShape.up ℤ)) :
    (NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ)).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) ≫
        (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) =
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app Z ≫
          (Functor.mapHomologicalComplexIdIso B (ComplexShape.up ℤ)).hom.app Z) := by
  ext n
  simp [unitIso_hom_app_eq_map_counit F G adj ε hε]

/-- The factorization of an induced functor, conjugated. -/
theorem mapDerivedCategoryFactors_conj {Y' Z' : HomologicalComplex B (ComplexShape.up ℤ)}
    (ψ : Y' ⟶ Z') :
    G.mapDerivedCategory.map (DerivedCategory.Q.map ψ) =
      G.mapDerivedCategoryFactors.hom.app Y' ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) ≫
        G.mapDerivedCategoryFactors.inv.app Z' := by
  rw [← Category.assoc, ← cancel_mono (G.mapDerivedCategoryFactors.hom.app Z')]
  simpa using (G.mapDerivedCategoryFactors.hom.naturality ψ)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [(F ⋙ G).Additive]
  [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] in
/-- The tail of the derived right-triangle identity. -/
theorem derivedRightTriangle_tail (adj : F ⊣ G) (ε : F ⋙ G ≅ 𝟭 A) (hε : ε.inv = adj.unit)
    (Z : HomologicalComplex B (ComplexShape.up ℤ)) :
    G.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex ε (ComplexShape.up ℤ)).hom.app
              ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
          DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)).hom.app
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
            G.mapDerivedCategoryFactors.inv.app Z =
      G.mapDerivedCategory.map
          (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app Z)) ≫
        G.mapDerivedCategory.map
          (DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexIdIso B (ComplexShape.up ℤ)).hom.app Z)) := by
  rw [← Functor.map_comp, ← Functor.map_comp,
    mapDerivedCategoryFactors_conj G
      (Y' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) (Z' := Z)
      ((NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℤ)).app Z ≫
        (Functor.mapHomologicalComplexIdIso B (ComplexShape.up ℤ)).hom.app Z),
    ← mapHomologicalComplex_right_triangle F G adj ε hε Z, Functor.map_comp]
  simp only [Category.assoc, Functor.id_obj]

/-- **The derived right-triangle identity on the image of the localization.** -/
theorem derivedRightTriangle_app_Q (adj : F ⊣ G) (ε : F ⋙ G ≅ 𝟭 A) (hε : ε.inv = adj.unit)
    (Z : HomologicalComplex B (ComplexShape.up ℤ)) :
    (derivedCompToIdOfIso F G ε).hom.app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj Z)) =
      G.mapDerivedCategory.map
        ((derivedCompToId G F adj.counit).app (DerivedCategory.Q.obj Z)) := by
  have hconj := natIso_id_app_conj (derivedCompToIdOfIso F G ε)
    (G.mapDerivedCategoryFactors.app Z)
  simp only [Iso.app_hom, Iso.app_inv, Functor.comp_obj] at hconj
  rw [hconj, derivedCompToIdOfIso_hom_app_Q, derivedCompToId_app_Q]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc, DerivedCategory.Q.map_comp]
  rw [derivedRightTriangle_tail F G adj ε hε Z]

/-- **The derived right-triangle identity.** -/
theorem whiskerLeft_derivedCompToIdOfIso (adj : F ⊣ G) (ε : F ⋙ G ≅ 𝟭 A)
    (hε : ε.inv = adj.unit) :
    (Functor.whiskerLeft G.mapDerivedCategory (derivedCompToIdOfIso F G ε).hom :
      G.mapDerivedCategory ⋙ F.mapDerivedCategory ⋙ G.mapDerivedCategory ⟶
        G.mapDerivedCategory) =
      Functor.whiskerRight (derivedCompToId G F adj.counit) G.mapDerivedCategory :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso B (ComplexShape.up ℤ))
    fun Z => derivedRightTriangle_app_Q F G adj ε hε Z

/-- `Stacks.DerivedGlueing.whiskerLeft_derivedCompToIdOfIso` at an object. -/
theorem derivedCompToIdOfIso_hom_app_map (adj : F ⊣ G) (ε : F ⋙ G ≅ 𝟭 A)
    (hε : ε.inv = adj.unit) (N : DerivedCategory B) :
    (derivedCompToIdOfIso F G ε).hom.app (G.mapDerivedCategory.obj N) =
      G.mapDerivedCategory.map ((derivedCompToId G F adj.counit).app N) :=
  NatTrans.congr_app (whiskerLeft_derivedCompToIdOfIso F G adj ε hε) N

end RightTriangle

section Pure

/-- The component of a threefold composite of isomorphisms, split after the first factor. -/
theorem trans₃_hom_app {C D : Type*} [Category C] [Category D] {F₁ F₂ F₃ F₄ : C ⥤ D}
    (α : F₁ ≅ F₂) (β : F₂ ≅ F₃) (γ : F₃ ≅ F₄) (K : C) :
    (α ≪≫ β ≪≫ γ).hom.app K = (α ≪≫ β).hom.app K ≫ γ.hom.app K := by
  simp

/-- Naturality of an isomorphism of functors, read as a conjugation. -/
theorem natIso_hom_app_map_inv_app {C D : Type*} [Category C] [Category D] {F₁ F₂ : C ⥤ D}
    (α : F₁ ≅ F₂) {x y : C} (f : x ⟶ y) :
    α.hom.app x ≫ F₂.map f ≫ α.inv.app y = F₁.map f := by
  simp

/-- **The step that turns the dictionary at one open into derived restriction of a single
morphism**: every object and morphism is a variable and no derived category is mentioned. -/
theorem dictionaryStep_pure {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] {F' : 𝒜 ⥤ ℬ} {G' : ℬ ⥤ 𝒜}
    {R : ℬ ⥤ 𝒜} (dP : R ≅ G') {α : F' ⋙ G' ≅ 𝟭 𝒜} {c : G' ⋙ F' ⟶ 𝟭 ℬ}
    (hα : ∀ N : ℬ, α.hom.app (G'.obj N) = G'.map (c.app N))
    {M : 𝒜} {N : ℬ} (μ : M ⟶ G'.obj N)
    {m₁ : R.obj (F'.obj M) ⟶ M} (hm₁ : m₁ = dP.hom.app (F'.obj M) ≫ α.hom.app M)
    {m₂ : M ⟶ R.obj N} (hm₂ : m₂ = μ ≫ dP.inv.app N) :
    m₁ ≫ m₂ = R.map (F'.map μ ≫ c.app N) := by
  subst hm₁ hm₂
  have h : α.hom.app M ≫ μ = G'.map (F'.map μ ≫ c.app N) := by
    rw [Functor.map_comp, ← hα N]
    exact (α.hom.naturality μ).symm
  rw [Category.assoc, reassoc_of% h]
  exact natIso_hom_app_map_inv_app dP _

/-- `Stacks.DerivedGlueing.natIso_hom_app_map_inv_app` at a composite target. -/
theorem natIso_hom_app_map_inv_app₂ {𝒳 𝒰 𝒲 : Type*} [Category 𝒳] [Category 𝒰] [Category 𝒲]
    {dRW : 𝒳 ⥤ 𝒲} {dRU : 𝒳 ⥤ 𝒰} {dRi : 𝒰 ⥤ 𝒲} (α : dRW ≅ dRU ⋙ dRi) {x y : 𝒳} (f : x ⟶ y) :
    α.hom.app x ≫ dRi.map (dRU.map f) ≫ α.inv.app y = dRW.map f :=
  natIso_hom_app_map_inv_app α f

/-- **The component of the five-fold composite that defines the dictionary at a pair of
opens.**  Taken in its own declaration: the identities contributed by the associator and the
left unitor are cancelled here, where every functor is a variable, so that the assembly below
carries no `simp` call for the kernel to recheck at a concrete ringed space. -/
theorem dictionaryIncl_hom_app {𝒳 𝒰 𝒲 : Type*} [Category 𝒳] [Category 𝒰] [Category 𝒲]
    {SWU : 𝒰 ⥤ 𝒲} {jU : 𝒰 ⥤ 𝒳} {dRW : 𝒳 ⥤ 𝒲} {dRU : 𝒳 ⥤ 𝒰} {dRi : 𝒰 ⥤ 𝒲}
    (Phi : SWU ≅ jU ⋙ dRW) (rID : dRW ≅ dRU ⋙ dRi) (epsI : jU ⋙ dRU ≅ 𝟭 𝒰) (M : 𝒰) :
    (Phi ≪≫ Functor.isoWhiskerLeft jU rID ≪≫ (Functor.associator jU dRU dRi).symm ≪≫
        Functor.isoWhiskerRight epsI dRi ≪≫ Functor.leftUnitor dRi).hom.app M =
      Phi.hom.app M ≫ rID.hom.app (jU.obj M) ≫ dRi.map (epsI.hom.app M) := by
  simp

/-- **The assembly of the dictionary at a pair of opens**, with every object and morphism a
variable.  Only associativity and functoriality are used, so the proof term is small. -/
theorem assemble_pure {𝒳 𝒰 𝒲 : Type*} [Category 𝒳] [Category 𝒰] [Category 𝒲]
    {SWU : 𝒰 ⥤ 𝒲} {jU : 𝒰 ⥤ 𝒳} {dRW : 𝒳 ⥤ 𝒲} {dRU : 𝒳 ⥤ 𝒰} {dRi : 𝒰 ⥤ 𝒲}
    (Phi : SWU ≅ jU ⋙ dRW) (rID : dRW ≅ dRU ⋙ dRi) (epsI : jU ⋙ dRU ≅ 𝟭 𝒰)
    {kappa : SWU ≅ dRi}
    (hkappa : kappa = Phi ≪≫ Functor.isoWhiskerLeft jU rID ≪≫
      (Functor.associator jU dRU dRi).symm ≪≫ Functor.isoWhiskerRight epsI dRi ≪≫
      Functor.leftUnitor dRi)
    {M : 𝒰} {N : 𝒳} (θ : jU.obj M ⟶ N)
    {Lw : 𝒲} (p : Lw ⟶ SWU.obj M) (phi : M ⟶ dRU.obj N)
    (hC1 : epsI.hom.app M ≫ phi = dRU.map θ) :
    p ≫ kappa.hom.app M ≫ dRi.map phi ≫ rID.inv.app N = p ≫ Phi.hom.app M ≫ dRW.map θ := by
  rw [hkappa, dictionaryIncl_hom_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, hC1, natIso_hom_app_map_inv_app₂ rID θ]

end Pure

section Concrete

open Stacks.Cohomology.GlueingComplexes Stacks.Cohomology.DerivedOpenImmersion

variable {X : RingedSpace.{u, u}}

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The derived counit of extension by zero on `U`.** -/
def derivedJShriekCounit (U : Opens X.carrier) :
    (jStar U (underlyingRingSheaf X)).mapDerivedCategory ⋙
        (jShriek U (underlyingRingSheaf X)).mapDerivedCategory ⟶
      𝟭 (DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X))) :=
  derivedCompToId (jStar U (underlyingRingSheaf X)) (jShriek U (underlyingRingSheaf X))
    (jShriekAdjunction U (underlyingRingSheaf X)).counit

/-- **The displayed restriction read as extension by zero followed by the degreewise
restriction.**  This is the first two of the three steps of
`Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrict`; the third is the comparison
of the degreewise restriction with derived pullback. -/
def LocallyGiven.restrictionIsoJStar (S : LocallyGiven X) (O U : Opens X.carrier)
    (hUO : U ≤ O) :
    S.restriction U O hUO ≅
      (jShriek O (underlyingRingSheaf X)).mapDerivedCategory ⋙
        (jStar U (underlyingRingSheaf X)).mapDerivedCategory :=
  restrictionIsoMapDerivedCategory S U O hUO ≪≫
    (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar U (underlyingRingSheaf X))).symm

/-- `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoJStar` at an object, split into its two
factors. -/
theorem LocallyGiven.restrictionIsoJStar_hom_app (S : LocallyGiven X) (O U : Opens X.carrier)
    (hUO : U ≤ O) (K : OpenDerivedCategory X O) :
    (S.restrictionIsoJStar O U hUO).hom.app K =
      (restrictionIsoMapDerivedCategory S U O hUO).hom.app K ≫
        (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
          (jStar U (underlyingRingSheaf X))).inv.app K :=
  rfl

/-- The dictionary at an object, split at the comparison with derived pullback. -/
theorem restrictionIsoDerivedRestrict_hom_app (S : LocallyGiven X) (O U : Opens X.carrier)
    (hUO : U ≤ O) (K : OpenDerivedCategory X O) :
    (S.restrictionIsoDerivedRestrict O U hUO).hom.app K =
      (S.restrictionIsoJStar O U hUO).hom.app K ≫
        (derivedPullbackOpenRestrictionIso X U).inv.app
          ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K) :=
  trans₃_hom_app (restrictionIsoMapDerivedCategory S U O hUO)
    (mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar U (underlyingRingSheaf X))).symm
    (Functor.isoWhiskerLeft ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory)
      (derivedPullbackOpenRestrictionIso X U).symm) K

/-- The cancellation of extension by zero against its own restriction, at an object. -/
theorem derivedRestrictJShriekIso_hom_app (U : Opens X.carrier)
    (M : OpenDerivedCategory X U) :
    (derivedRestrictJShriekIso U).hom.app M =
      (derivedPullbackOpenRestrictionIso X U).hom.app
          ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory.obj M) ≫
        (derivedCompToIdOfIso (jShriek U (underlyingRingSheaf X))
          (jStar U (underlyingRingSheaf X)) (jShriekUnitIso U).symm).hom.app M :=
  rfl

/-- The inverse of the inverted unit isomorphism is the unit of the adjunction. -/
theorem jShriekUnitIso_symm_inv (U : Opens X.carrier) :
    ((jShriekUnitIso (X := X) U).symm).inv =
      (jShriekAdjunction U (underlyingRingSheaf X)).unit :=
  rfl

/-- **The dictionary at one open, read as derived restriction of a single morphism.** -/
theorem dictionary_at_one_open (S : LocallyGiven X) (O U : Opens X.carrier) (hUO : U ≤ O)
    (K : OpenDerivedCategory X O) :
    (derivedRestrictJShriekIso U).hom.app ((S.restriction U O hUO).obj K) ≫
        (S.restrictionIsoDerivedRestrict O U hUO).hom.app K =
      (derivedRestrict (X.ofRestrict U.isOpenEmbedding)).map
        ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory.map
            ((S.restrictionIsoJStar O U hUO).hom.app K) ≫
          (derivedJShriekCounit U).app
            ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) := by
  have hα : ∀ N : DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X)),
      (derivedCompToIdOfIso (jShriek U (underlyingRingSheaf X))
            (jStar U (underlyingRingSheaf X)) (jShriekUnitIso U).symm).hom.app
          ((jStar U (underlyingRingSheaf X)).mapDerivedCategory.obj N) =
        (jStar U (underlyingRingSheaf X)).mapDerivedCategory.map
          ((derivedJShriekCounit U).app N) := fun N =>
    derivedCompToIdOfIso_hom_app_map (jShriek U (underlyingRingSheaf X))
      (jStar U (underlyingRingSheaf X)) (jShriekAdjunction U (underlyingRingSheaf X))
      (jShriekUnitIso U).symm rfl N
  exact dictionaryStep_pure (derivedPullbackOpenRestrictionIso X U) hα
    ((S.restrictionIsoJStar O U hUO).hom.app K)
    (derivedRestrictJShriekIso_hom_app U ((S.restriction U O hUO).obj K))
    (restrictionIsoDerivedRestrict_hom_app S O U hUO K)

/-- `Stacks.DerivedGlueing.LocallyGiven.restrictionIsoDerivedRestrictIncl` written out. -/
theorem restrictionIsoDerivedRestrictIncl_eq (S : LocallyGiven X) {W U : Opens X.carrier}
    (hWU : W ≤ U) :
    S.restrictionIsoDerivedRestrictIncl hWU =
      S.restrictionIsoDerivedRestrict U W hWU ≪≫
        Functor.isoWhiskerLeft ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory)
          (restrictInclDerivedIso (X := X) hWU) ≪≫
        (Functor.associator ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory)
          (derivedRestrict (X.ofRestrict U.isOpenEmbedding))
          (derivedRestrict (restrictIncl (X := X) hWU))).symm ≪≫
        Functor.isoWhiskerRight (derivedRestrictJShriekIso U)
          (derivedRestrict (restrictIncl (X := X) hWU)) ≪≫
        Functor.leftUnitor (derivedRestrict (restrictIncl (X := X) hWU)) :=
  rfl

/-! ### The coherence of the dictionary for a chain of three opens -/

/-- **The coherence of the dictionary in the `j^*` spelling, for `W ≤ U ≤ O`.** -/
theorem LocallyGiven.restrictionIsoJStar_hom_app_trans (S : LocallyGiven X)
    (W U O : Opens X.carrier) (hWU : W ≤ U) (hUO : U ≤ O) (K : OpenDerivedCategory X O) :
    (S.restrictionIsoJStar O W (hWU.trans hUO)).hom.app K =
      (S.restrictionComp W U O hWU hUO).hom.app K ≫
        (S.restrictionIsoJStar U W hWU).hom.app ((S.restriction U O hUO).obj K) ≫
        (jStar W (underlyingRingSheaf X)).mapDerivedCategory.map
          ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory.map
              ((S.restrictionIsoJStar O U hUO).hom.app K) ≫
            (derivedJShriekCounit U).app
              ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) := by
  have hn := (mapDerivedCategoryCompIso (jShriek U (underlyingRingSheaf X))
      (jStar W (underlyingRingSheaf X))).inv.naturality
    ((restrictionIsoMapDerivedCategory S U O hUO).hom.app K)
  have hc := NatTrans.congr_app (restrictionComp_eq_mapDerivedCategoryComp S W U O hWU hUO) K
  have hs := NatTrans.congr_app (compIso_comp_coherence (jShriek O (underlyingRingSheaf X))
      (jStar U (underlyingRingSheaf X)) (jShriek U (underlyingRingSheaf X))
      (jStar W (underlyingRingSheaf X)) (jShriekAdjunction U (underlyingRingSheaf X)).counit
      (asIso (openModuleRestrictionComparison X W U O hWU hUO) :
        openModuleRestriction X U O hUO ⋙ openModuleRestriction X W U hWU ≅
          openModuleRestriction X W O (hWU.trans hUO)) rfl) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.comp_obj] at hc hs hn
  simp only [LocallyGiven.restrictionIsoJStar_hom_app, Functor.map_comp]
  exact jStar_trans_chase
    ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory ⋙
      (jStar W (underlyingRingSheaf X)).mapDerivedCategory)
    (openModuleRestriction X W U hWU).mapDerivedCategory hn hc hs
    ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar U (underlyingRingSheaf X))).inv_hom_id_app K)
    ((mapDerivedCategoryCompIso (jShriek U (underlyingRingSheaf X))
      (jStar W (underlyingRingSheaf X))).inv_hom_id_app
      ((openModuleRestriction X U O hUO).mapDerivedCategory.obj K))
    ((mapDerivedCategoryCompIso (jShriek O (underlyingRingSheaf X))
      (jStar W (underlyingRingSheaf X))).hom_inv_id_app K)
    ((mapDerivedCategoryComp (openModuleRestriction X U O hUO)
      (openModuleRestriction X W U hWU) (openModuleRestriction X W O (hWU.trans hUO))
      (asIso (openModuleRestrictionComparison X W U O hWU hUO))).hom_inv_id_app K)

/-- **The coherence of the dictionary for `W ≤ U ≤ O`, in the derived-pullback spelling.** -/
theorem LocallyGiven.restrictionIsoDerivedRestrict_hom_app_trans (S : LocallyGiven X)
    (W U O : Opens X.carrier) (hWU : W ≤ U) (hUO : U ≤ O) (K : OpenDerivedCategory X O) :
    (S.restrictionIsoDerivedRestrict O W (hWU.trans hUO)).hom.app K =
      (S.restrictionComp W U O hWU hUO).hom.app K ≫
        (S.restrictionIsoDerivedRestrict U W hWU).hom.app ((S.restriction U O hUO).obj K) ≫
        (derivedRestrict (X.ofRestrict W.isOpenEmbedding)).map
          ((jShriek U (underlyingRingSheaf X)).mapDerivedCategory.map
              ((S.restrictionIsoJStar O U hUO).hom.app K) ≫
            (derivedJShriekCounit U).app
              ((jShriek O (underlyingRingSheaf X)).mapDerivedCategory.obj K)) := by
  rw [restrictionIsoDerivedRestrict_hom_app S O W (hWU.trans hUO) K,
    restrictionIsoDerivedRestrict_hom_app S U W hWU ((S.restriction U O hUO).obj K)]
  exact comp_transport (S.restrictionIsoJStar_hom_app_trans W U O hWU hUO K)
    ((derivedPullbackOpenRestrictionIso X W).inv.naturality _)

end Concrete

end Stacks.DerivedGlueing

end
