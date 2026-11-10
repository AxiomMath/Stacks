module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualityCompactification
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageDualityComparison
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonical
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekPullbackComparisonCanonicalMaps

/-!
# The duality formula of [Stacks, Tag 0AU2] through the comparison maps of compactifications

Let `f : X ⟶ Y` be a morphism of `FTS_S`, `j` a compactification of `X` over `Y` with open
immersion `ι : X ⟶ X̄` and `f̄ : X̄ ⟶ Y`, and `K` a dualizing complex on `Y`. Under the
tensor–internal-Hom bijection of [Stacks, Tag 08J8], the isomorphism `f^!M ≅ D_X(Lf^* D_Y M)` of
[Stacks, Tag 0AU2] is, at the locally small model, the map
`Lf^* D_Y(M) ⊗ᴸ f^!M ⟶ f^!K` given by `L(ι)^*` of the comparison map
`Lf̄^* D_Y(M) ⊗ᴸ ā(M) ⟶ ā(D_Y(M) ⊗ᴸ M)` of Equation 48.8.0.1 followed by `f^!` of the evaluation.
The comparison maps of two compactifications are compatible with the comparison `α_g` of their
upper shriek functors, so the isomorphism of [Stacks, Tag 0AU2] does not depend on the
compactification.

## Main results

* `Stacks.Duality.UpperShriekDuality.pullTensorIso_hom_model`: the comparison
  `Lg^*(P ⊗ᴸ Q) ≅ Lg^*P ⊗ᴸ Lg^*Q` at the two models.
* `Stacks.Duality.UpperShriekDuality.tensorPullComparison_restriction`: the comparison of the
  tensor products for `f̄`, restricted along `ι`.
* `Stacks.Duality.UpperShriekDuality.comparison_map_curry_upperShriekDualityIso_hom_app`: the
  transpose of the isomorphism of [Stacks, Tag 0AU2] through the comparison map of `f̄`.
* `Stacks.Duality.UpperShriekDuality.upperShriekDualityIso_compactificationMap`: the isomorphism
  of [Stacks, Tag 0AU2] is compatible with the comparison `α_g` of two compactifications.

## References

* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
* [Stacks Project, Tag 0A9S](https://stacks.math.columbia.edu/tag/0A9S)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Duality.UpperShriekDuality

open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Duality.ProjectionFormulaMonoidal (tensorModelIso swapIso)

/-- The chase behind `pullTensorIso_hom_model`. -/
theorem pullTensor_model_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ P₅ Q₀ Q₁ Q₂ : C}
    (Gst : P₀ ⟶ P₃) (Gs : P₀ ⟶ P₁) (Gc : P₁ ⟶ P₂) (Gh : P₂ ⟶ P₃) (Gi : P₃ ⟶ P₂) (t : P₂ ⟶ P₄)
    (w w' : P₄ ⟶ P₅) (m' : P₀ ⟶ Q₀) (m : P₁ ≅ Q₁) (Lgs : Q₀ ⟶ Q₁) (Ld : Q₂ ⟶ Q₁)
    (Ldi : Q₁ ⟶ Q₂) (δ : Q₂ ⟶ P₅) (hG : Gst = Gs ≫ Gc ≫ Gh) (hhi : Gh ≫ Gi = 𝟙 _)
    (hd : Ldi ≫ Ld = 𝟙 _) (hn : Gs ≫ m.hom = m' ≫ Lgs) (hw : w = w')
    (hδ : δ = Ld ≫ m.inv ≫ Gc ≫ t ≫ w') :
    Gst ≫ (Gi ≫ t) ≫ w = m' ≫ Lgs ≫ Ldi ≫ δ := by
  subst hδ hG hw
  simp only [Category.assoc, reassoc_of% hd, reassoc_of% hhi]
  rw [← reassoc_of% hn, Iso.hom_inv_id_assoc]

section Tensor

variable {A B : Scheme.{u}} (g : A ⟶ B)

/-- `pullTensorIso` at the locally small model, as its three factors. -/
theorem comparison_map_pullTensorIso_hom (P Q : Std B) :
    (comparison A).functor.map (pullTensorIso g P Q).hom =
      (comparison A).functor.map ((pull g).map
        (((ProjectionFormulaLocallySmall.standardTensorIso B).inv.app P).app Q)) ≫
      (comparison A).functor.map
        ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
          g.toLRSHom.toShHom).app (P, Q)) ≫
      (comparison A).functor.map (((ProjectionFormulaLocallySmall.standardTensorIso A).hom.app
          ((pull g).obj P)).app ((pull g).obj Q)) := by
  simp only [Iso.app_hom, pullTensorNatIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp]
  rfl

/-- The tensor product of `pullModelIso` at the locally small model, as two whiskerings. -/
theorem canonicalTensor_map_pullModelIso_hom (P Q : Std B) :
    (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal A)).map
        ((pullModelIso g).hom.app P ×ₘ (pullModelIso g).hom.app Q) =
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor A.sheaf).map
          ((StacksDraft.DerivedModel.derivedPullbackModelIso g.toLRSHom.toShHom).hom.app P)).app _ ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor A.sheaf).obj _).map
          ((StacksDraft.DerivedModel.derivedPullbackModelIso g.toLRSHom.toShHom).hom.app Q) := by
  let := Scheme.Modules.canonicalDerivedMonoidal A
  exact MonoidalCategory.tensorHom_def _ _

/-- The comparison of the two derived tensor products of `D(𝒪_A)`, there and back. -/
theorem comparison_map_standardTensorIso_hom_inv (P Q : Std B) :
    (comparison A).functor.map (((ProjectionFormulaLocallySmall.standardTensorIso
      A).hom.app
          ((pull g).obj P)).app ((pull g).obj Q)) ≫
      (comparison A).functor.map (((ProjectionFormulaLocallySmall.standardTensorIso A).inv.app
          ((pull g).obj P)).app ((pull g).obj Q)) = 𝟙 _ := by
  exact Functor.map_hom_inv' _ (((ProjectionFormulaLocallySmall.standardTensorIso A).app
    ((pull g).obj P)).app ((pull g).obj Q))

/-- `Lg^*` of the comparison of the two models of `⊗ᴸ`, there and back. -/
theorem derivedPullback_map_tensorModelIso_inv_comp (P Q : Std B) :
    (Stacks.Duality.derivedPullback g).map ((tensorModelIso B).inv.app (P, Q)) ≫
      (Stacks.Duality.derivedPullback g).map
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso B.sheaf).hom.app
          P).app Q) = 𝟙 _ :=
  Functor.map_inv_hom' _ ((tensorModelIso B).app (P, Q))

/-- **`Lg^*(P ⊗ᴸ Q) ≅ Lg^*P ⊗ᴸ Lg^*Q` at the two models**: `pullTensorIso` read through the
comparisons of the models of `Lg^*` and of `⊗ᴸ` is the oplax tensorator of `Lg^*` at the locally
small model. -/
theorem pullTensorIso_hom_model (P Q : Std B) :
    (comparison A).functor.map (pullTensorIso g P Q).hom ≫
        ((comparison A).functor.map (((ProjectionFormulaLocallySmall.standardTensorIso A).inv.app
          ((pull g).obj P)).app ((pull g).obj Q)) ≫
          (tensorModelIso A).inv.app ((pull g).obj P, (pull g).obj Q)) ≫
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal A)).map
          ((pullModelIso g).hom.app P ×ₘ (pullModelIso g).hom.app Q) =
      (pullModelIso g).hom.app (((tensor B).obj P).obj Q) ≫
        (Stacks.Duality.derivedPullback g).map ((comparison B).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso B).inv.app P).app Q)) ≫
        (Stacks.Duality.derivedPullback g).map ((tensorModelIso B).inv.app (P, Q)) ≫
        @Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal B) _ _
          (Scheme.Modules.canonicalDerivedMonoidal A) (Stacks.Duality.derivedPullback g)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            g.toLRSHom.toShHom).toOplaxMonoidal
          ((comparison B).functor.obj P) ((comparison B).functor.obj Q) := by
  refine pullTensor_model_chase
    ((comparison A).functor.map (pullTensorIso g P Q).hom)
    ((comparison A).functor.map ((pull g).map
        (((ProjectionFormulaLocallySmall.standardTensorIso B).inv.app P).app Q)))
    ((comparison A).functor.map
        ((Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison
          g.toLRSHom.toShHom).app (P, Q)))
    ((comparison A).functor.map (((ProjectionFormulaLocallySmall.standardTensorIso A).hom.app
          ((pull g).obj P)).app ((pull g).obj Q)))
    ((comparison A).functor.map (((ProjectionFormulaLocallySmall.standardTensorIso A).inv.app
          ((pull g).obj P)).app ((pull g).obj Q)))
    ((tensorModelIso A).inv.app ((pull g).obj P, (pull g).obj Q))
    ((@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal A)).map
        ((pullModelIso g).hom.app P ×ₘ (pullModelIso g).hom.app Q))
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor A.sheaf).map
          ((StacksDraft.DerivedModel.derivedPullbackModelIso g.toLRSHom.toShHom).hom.app P)).app _ ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor A.sheaf).obj _).map
          ((StacksDraft.DerivedModel.derivedPullbackModelIso g.toLRSHom.toShHom).hom.app Q))
    ((pullModelIso g).hom.app (((tensor B).obj P).obj Q))
    ((pullModelIso g).app ((ProjectionFormulaMonoidal.standardTensor B).obj (P, Q)))
    ((Stacks.Duality.derivedPullback g).map ((comparison B).functor.map
        (((ProjectionFormulaLocallySmall.standardTensorIso B).inv.app P).app Q)))
    ((Stacks.Duality.derivedPullback g).map
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso B.sheaf).hom.app
          P).app Q))
    ((Stacks.Duality.derivedPullback g).map ((tensorModelIso B).inv.app (P, Q)))
    (@Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal B) _ _
          (Scheme.Modules.canonicalDerivedMonoidal A) (Stacks.Duality.derivedPullback g)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            g.toLRSHom.toShHom).toOplaxMonoidal
          ((comparison B).functor.obj P) ((comparison B).functor.obj Q))
    (comparison_map_pullTensorIso_hom g P Q) (comparison_map_standardTensorIso_hom_inv g P Q) ?_
    ((pullModelIso g).hom.naturality _) (canonicalTensor_map_pullModelIso_hom g P Q) ?_
  · exact derivedPullback_map_tensorModelIso_inv_comp g P Q
  · rw [derivedPullbackCanonicalMonoidal_δ_model g P Q]
    rfl

end Tensor

/-- The chase behind `map_pull_map_homEquiv_comp_pullModelConj_inv`. -/
theorem counit_model_chase {C D : Type*} [Category C] [Category D] (L : D ⥤ C)
    {P₀ P₁ P₂ : C} {S₀ S₁ S₂ : D} (Gph : P₀ ⟶ P₁) (pmcI : P₁ ⟶ P₂) (ε : L.obj S₂ ≅ P₂)
    (mT : P₀ ⟶ L.obj S₀) (mQ : P₁ ⟶ L.obj S₁) (Gh : S₀ ⟶ S₁) (εQ : S₁ ⟶ S₂) (x : S₀ ⟶ S₂)
    (h1 : Gph ≫ mQ = mT ≫ L.map Gh) (h2 : Gh ≫ εQ = x)
    (h3 : pmcI ≫ ε.inv = mQ ≫ L.map εQ) :
    Gph ≫ pmcI = mT ≫ L.map x ≫ ε.hom := by
  rw [← h2, L.map_comp, Category.assoc, ← reassoc_of% h1, ← reassoc_of% h3, Iso.inv_hom_id,
    Category.comp_id]

/-- `Lg^*` of a transpose under the comparison of the models, followed by `pullModelConj`: the
comparison of `Lg^*` at the two models, `Lg^*` of the original morphism and the counit. -/
theorem map_pull_map_homEquiv_comp_pullModelConj_inv {A₀ B₀ : Scheme.{u}} (g : A₀ ⟶ B₀)
    (T : Std B₀) (Q : DerivedCategory B₀.Modules) (x : (comparison B₀).functor.obj T ⟶ Q) :
    (comparison A₀).functor.map ((pull g).map ((comparison B₀).toAdjunction.homEquiv _ _ x)) ≫
        (comparison A₀).functor.map ((pullModelConj g).inv.app Q) =
      (pullModelIso g).hom.app T ≫ (Stacks.Duality.derivedPullback g).map x ≫
        (comparison A₀).counitIso.inv.app ((Stacks.Duality.derivedPullback g).obj Q) :=
  counit_model_chase (Stacks.Duality.derivedPullback g) _ _
    ((comparison A₀).counitIso.app ((Stacks.Duality.derivedPullback g).obj Q)).symm
    ((pullModelIso g).hom.app T) ((pullModelIso g).hom.app ((comparison B₀).inverse.obj Q))
    ((comparison B₀).functor.map ((comparison B₀).toAdjunction.homEquiv _ _ x))
    ((comparison B₀).counit.app Q) x
    ((pullModelIso g).hom.naturality ((comparison B₀).toAdjunction.homEquiv _ _ x))
    (((comparison B₀).toAdjunction.homEquiv_counit _ _ _).symm.trans
      (Equiv.symm_apply_apply _ _))
    (pullModelConj_inv_app_comp_counit g Q)

/-- The chase behind `tensorPullComparison_restriction`. -/
theorem tensor_restriction_chase {C : Type*} [Category C]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ Q₁ Q₂ Q₃ R₁ R₂ R₃ R₄ R₅ R₆ : C}
    (s₁ : P₀ ⟶ P₁) (s₂ : P₁ ⟶ P₂) (s₃ : P₂ ⟶ P₃) (s₄ : P₃ ⟶ P₄) (s₅ : P₄ ⟶ P₈)
    (lζ₁ : P₄ ⟶ P₅) (lζ₂ : P₅ ⟶ P₆) (lt : P₆ ⟶ P₇) (lsw : P₇ ⟶ P₈)
    (ζ'₁ : P₂ ⟶ Q₁) (ζ'₂ : Q₁ ⟶ Q₂) (U : Q₂ ⟶ Q₃) (μ₁ : Q₃ ⟶ P₆)
    (ζ₁ : P₀ ⟶ R₁) (ζ₂ : R₁ ⟶ R₂) (V : R₂ ⟶ Q₂) (U' : Q₃ ⟶ R₃) (μ₂ : R₃ ⟶ P₇)
    (wε : R₂ ⟶ R₄) (wk : R₄ ⟶ R₃) (sw : R₄ ⟶ R₅) (rk : R₅ ⟶ R₆) (μ₃ : R₆ ⟶ P₈)
    (i : R₅ ⟶ R₅) (hi : i = 𝟙 _) (hL : s₅ = lζ₁ ≫ lζ₂ ≫ lt ≫ lsw)
    (h₁ : s₃ ≫ s₄ ≫ lζ₁ ≫ lζ₂ = ζ'₁ ≫ ζ'₂ ≫ U ≫ μ₁)
    (h₂ : s₁ ≫ s₂ ≫ ζ'₁ ≫ ζ'₂ = ζ₁ ≫ ζ₂ ≫ V)
    (h₃ : μ₁ ≫ lt = U' ≫ μ₂) (h₄ : V ≫ U ≫ U' = wε ≫ wk)
    (h₅ : wk ≫ μ₂ ≫ lsw = sw ≫ rk ≫ μ₃) :
    s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ s₅ = (ζ₁ ≫ ζ₂ ≫ wε ≫ sw) ≫ i ≫ rk ≫ μ₃ := by
  subst hi hL
  simp only [Category.assoc, Category.id_comp]
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, h₅]

/-- Inverting the comparison of `pullTensorIso_hom_model`. -/
theorem inv_model_chase {C : Type*} [Category C] {P Q R₁ R₂ S T Z₁' Z₂' : C} (H : P ⟶ Q)
    (Hi : Q ⟶ P) (Z₁ : Q ⟶ Z₁') (Z₂ : Z₁' ⟶ Z₂') (U : Z₂' ⟶ T) (m : P ⟶ R₁) (L₁ : R₁ ⟶ R₂)
    (L₂ : R₂ ⟶ S) (δ : S ⟶ T) (μ : T ⟶ S) (hH : Hi ≫ H = 𝟙 _) (hδ : δ ≫ μ = 𝟙 _)
    (hP : H ≫ (Z₁ ≫ Z₂) ≫ U = m ≫ L₁ ≫ L₂ ≫ δ) :
    Hi ≫ m ≫ L₁ ≫ L₂ = Z₁ ≫ Z₂ ≫ U ≫ μ := by
  simp only [Category.assoc] at hP
  rw [← Category.id_comp (Z₁ ≫ _), ← hH, Category.assoc, reassoc_of% hP, hδ, Category.comp_id]

/-- Naturality of a composite of a transformation read through a functor and a second one. -/
theorem nat_two_chase {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {P₀ P₁ P₂ P₃ Q₀ : C}
    {R₁ R₂ : D} (x : P₀ ⟶ P₁) (y : P₁ ⟶ P₂) (s' : P₂ ⟶ P₃) (s : P₀ ⟶ Q₀) (z : Q₀ ⟶ P₃)
    (t' : G.obj P₃ ⟶ R₂) (t : G.obj Q₀ ⟶ R₁) (V : R₁ ⟶ R₂) (hst : (x ≫ y) ≫ s' = s ≫ z)
    (ht : G.map z ≫ t' = t ≫ V) :
    G.map x ≫ G.map y ≫ G.map s' ≫ t' = G.map s ≫ t ≫ V := by
  have h := congrArg G.map hst
  simp only [G.map_comp, Category.assoc] at h
  rw [reassoc_of% h, ht]

/-- Cancelling a comparison and its inverse. -/
theorem cancel_model_chase {C : Type*} [Category C] {P Q R S : C} (Ga : P ⟶ Q) (Gi : Q ⟶ P)
    (e : P ⟶ S) (m : Q ⟶ R) (L : R ⟶ S) (hc : Ga ≫ Gi = 𝟙 _) (hP : Gi ≫ e = m ≫ L) :
    Ga ≫ m ≫ L = e := by
  rw [← hP, ← Category.assoc, hc, Category.id_comp]

/-- Moving the composition isomorphism across the comparison of the models. -/
theorem comp_model_cancel {C : Type*} [Category C] {P Q R S U : C} (Gl : P ⟶ Q) (Gc : Q ⟶ P)
    (pf : P ⟶ U) (pι : Q ⟶ R) (Lp : R ⟶ S) (k : S ⟶ U) (k' : U ⟶ S) (hl : Gl ≫ Gc = 𝟙 _)
    (hk : k ≫ k' = 𝟙 _) (hC : Gc ≫ pf = pι ≫ Lp ≫ k) :
    Gl ≫ pι ≫ Lp = pf ≫ k' := by
  rw [← Category.comp_id Lp, ← hk, ← reassoc_of% hC, reassoc_of% hl]

/-- Composing three tensor products of morphisms. -/
theorem tensor_three_chase {C : Type*} [Category C] [MonoidalCategory C] {P₀ P₁ P₂ P₃ Q₀ Q₁ Q₂ Q₃
    R : C}
    (a : P₀ ⟶ P₁) (c : P₁ ⟶ P₂) (e : P₂ ⟶ P₃) (ε : P₀ ⟶ P₃) (b : Q₀ ⟶ Q₁) (d : Q₁ ⟶ Q₂)
    (f : Q₂ ⟶ Q₃) (p : Q₀ ⟶ R) (k : R ⟶ Q₃) (h₁ : a ≫ c ≫ e = ε) (h₂ : b ≫ d ≫ f = p ≫ k) :
    (tensor C).map (a ×ₘ b) ≫ (tensor C).map (c ×ₘ d) ≫ (tensor C).map (e ×ₘ f) =
      (tensor C).map (ε ×ₘ p) ≫ P₃ ◁ k := by
  change (a ⊗ₘ b) ≫ (c ⊗ₘ d) ≫ (e ⊗ₘ f) = (ε ⊗ₘ p) ≫ P₃ ◁ k
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, h₁, h₂, MonoidalCategory.tensorHom_def,
    MonoidalCategory.tensorHom_def,
    whiskerLeft_comp]
  simp only [Category.assoc]

/-- A lax braided functor, its tensorator and a whiskering. -/
theorem braided_whisker_chase {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.LaxBraided]
    (X Y : C) {Z : D} (k : Z ⟶ F.obj Y) :
    F.obj X ◁ k ≫ Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) Z).hom ≫ k ▷ F.obj X ≫ Functor.LaxMonoidal.μ F Y X := by
  rw [Functor.LaxBraided.braided, BraidedCategory.braiding_naturality_right_assoc]

section Restriction

variable {X₀ X₁ Y₀ : Scheme.{u}} (ι : X₀ ⟶ X₁) (f₁ : X₁ ⟶ Y₀) (f : X₀ ⟶ Y₀) (w : ι ≫ f₁ = f)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f₁] [QuasiSeparated f₁]
  [CompactSpace X₀] [QuasiSeparatedSpace X₀] [CompactSpace X₁] [QuasiSeparatedSpace X₁]
  [CompactSpace Y₀] [QuasiSeparatedSpace Y₀]

omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f₁] [QuasiSeparated f₁]
  [CompactSpace X₀] [QuasiSeparatedSpace X₀] [CompactSpace X₁] [QuasiSeparatedSpace X₁]
  [CompactSpace Y₀] [QuasiSeparatedSpace Y₀] in
/-- **The comparison of the tensor products restricted along `ι`.** For `ι ≫ f₁ = f`, the
comparison `tensorPullComparison` for `f₁` at `A`, restricted along `ι`, is, through the
comparisons of the models and of `L(ι)^*` of a tensor product, the one for `f` at `Lι^*A`
followed by `Lι^*Lf₁^* ≅ Lf^*` and the tensorator of `Lι^*` on `D_QCoh`. -/
theorem tensorPullComparison_restriction (A : quasiCoherentDerivedCategory X₁) (D : Std Y₀)
    (hD : qcoh Y₀ D) :
    (comparison X₀).functor.map (((tensor X₀).map ((pullModelConj ι).hom.app A.obj)).app
        ((pull f).obj D)) ≫
      (comparison X₀).functor.map
        (((tensor X₀).obj ((pull ι).obj ((comparison X₁).inverse.obj A.obj))).map
          ((pullCompIso ι f₁ f w).inv.app D)) ≫
      (comparison X₀).functor.map
        (pullTensorIso ι ((comparison X₁).inverse.obj A.obj) ((pull f₁).obj D)).inv ≫
      (pullModelIso ι).hom.app
        (((tensor X₁).obj ((comparison X₁).inverse.obj A.obj)).obj ((pull f₁).obj D)) ≫
      (Stacks.Duality.derivedPullback ι).map (tensorPullComparison f₁ A D hD) =
    tensorPullComparison f ((quasiCoherentDerivedPullback' ι).obj A) D hD ≫
      (((quasiCoherentDerivedTensorIsoCurriedTensor X₀).hom.app
        ((quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩))).app
          ((quasiCoherentDerivedPullback' ι).obj A)).hom ≫
      (((quasiCoherentDerivedPullbackCompIso ι f₁ ≪≫ quasiCoherentDerivedPullbackCongr w).inv.app
        (toQCoh ⟨D, hD⟩)) ▷ (quasiCoherentDerivedPullback' ι).obj A).hom ≫
      (Functor.LaxMonoidal.μ (quasiCoherentDerivedPullback' ι)
        ((quasiCoherentDerivedPullback' f₁).obj (toQCoh ⟨D, hD⟩)) A).hom := by
  have hL : (Stacks.Duality.derivedPullback ι).map (tensorPullComparison f₁ A D hD) =
      (Stacks.Duality.derivedPullback ι).map ((comparison X₁).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso X₁).inv.app
        ((comparison X₁).inverse.obj A.obj)).app ((pull f₁).obj D))) ≫
      (Stacks.Duality.derivedPullback ι).map ((tensorModelIso X₁).inv.app (((comparison
          X₁).inverse.obj A.obj), ((pull f₁).obj D))) ≫
      (Stacks.Duality.derivedPullback ι).map ((@MonoidalCategory.tensor _ _
          (Scheme.Modules.canonicalDerivedMonoidal X₁)).map
        ((comparison X₁).counitIso.hom.app A.obj ×ₘ
          (StacksDraft.DerivedModel.derivedPullbackModelIso f₁.toLRSHom.toShHom).hom.app D)) ≫
      (Stacks.Duality.derivedPullback ι).map ((swapIso X₁).hom.app (A,
          (quasiCoherentDerivedPullback' f₁).obj (toQCoh ⟨D, hD⟩))) :=
    ((Stacks.Duality.derivedPullback ι).map_comp _ _).trans (congrArg (_ ≫ ·)
      (((Stacks.Duality.derivedPullback ι).map_comp _ _).trans (congrArg (_ ≫ ·)
        ((Stacks.Duality.derivedPullback ι).map_comp _ _))))
  have h₁ := inv_model_chase
    ((comparison X₀).functor.map (pullTensorIso ι ((comparison X₁).inverse.obj A.obj) ((pull
        f₁).obj D)).hom)
    ((comparison X₀).functor.map (pullTensorIso ι ((comparison X₁).inverse.obj A.obj) ((pull
        f₁).obj D)).inv) _ _ _ _ _ _
    (@Functor.OplaxMonoidal.δ _ _ (Scheme.Modules.canonicalDerivedMonoidal X₁) _ _
          (Scheme.Modules.canonicalDerivedMonoidal X₀) (Stacks.Duality.derivedPullback ι)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            ι.toLRSHom.toShHom).toOplaxMonoidal
          ((comparison X₁).functor.obj ((comparison X₁).inverse.obj A.obj)) ((comparison
              X₁).functor.obj ((pull f₁).obj D)))
    (@Functor.LaxMonoidal.μ _ _ (Scheme.Modules.canonicalDerivedMonoidal X₁) _ _
          (Scheme.Modules.canonicalDerivedMonoidal X₀) (Stacks.Duality.derivedPullback ι)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            ι.toLRSHom.toShHom).toLaxMonoidal
          ((comparison X₁).functor.obj ((comparison X₁).inverse.obj A.obj)) ((comparison
              X₁).functor.obj ((pull f₁).obj D)))
    (Functor.map_inv_hom' _ _)
    (@Functor.Monoidal.δ_μ _ _ (Scheme.Modules.canonicalDerivedMonoidal X₁) _ _
          (Scheme.Modules.canonicalDerivedMonoidal X₀) (Stacks.Duality.derivedPullback ι)
          (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
            ι.toLRSHom.toShHom) ((comparison X₁).functor.obj ((comparison X₁).inverse.obj A.obj))
                ((comparison X₁).functor.obj ((pull f₁).obj D)))
    (pullTensorIso_hom_model ι ((comparison X₁).inverse.obj A.obj) ((pull f₁).obj D))
  have h₂ := nat_two_chase (comparison X₀).functor
    (((tensor X₀).map ((pullModelConj ι).hom.app A.obj)).app ((pull f).obj D))
    (((tensor X₀).obj ((pull ι).obj ((comparison X₁).inverse.obj A.obj))).map ((pullCompIso ι f₁ f
        w).inv.app D))
    (((ProjectionFormulaLocallySmall.standardTensorIso X₀).inv.app ((pull ι).obj ((comparison
        X₁).inverse.obj A.obj))).app
      ((pull ι).obj ((pull f₁).obj D)))
    (((ProjectionFormulaLocallySmall.standardTensorIso X₀).inv.app ((comparison X₀).inverse.obj
        ((quasiCoherentDerivedPullback' ι).obj A).obj)).app ((pull f).obj D))
    ((ProjectionFormulaMonoidal.standardTensor X₀).map (X := (((comparison X₀).inverse.obj
        ((quasiCoherentDerivedPullback' ι).obj A).obj), ((pull f).obj D)))
      (Y := ((pull ι).obj ((comparison X₁).inverse.obj A.obj), (pull ι).obj ((pull f₁).obj D)))
          ((pullModelConj ι).hom.app A.obj, (pullCompIso ι f₁ f w).inv.app D))
    ((tensorModelIso X₀).inv.app ((pull ι).obj ((comparison X₁).inverse.obj A.obj), (pull ι).obj
        ((pull f₁).obj D)))
    ((tensorModelIso X₀).inv.app (((comparison X₀).inverse.obj ((quasiCoherentDerivedPullback'
        ι).obj A).obj), ((pull f).obj D)))
    ((@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X₀)).map
      ((comparison X₀).functor.map ((pullModelConj ι).hom.app A.obj) ×ₘ
        (comparison X₀).functor.map ((pullCompIso ι f₁ f w).inv.app D)))
    ((Functor.uncurry.map (ProjectionFormulaLocallySmall.standardTensorIso X₀).inv).naturality
      (X := (((comparison X₀).inverse.obj ((quasiCoherentDerivedPullback' ι).obj A).obj), ((pull
          f).obj D))) (Y := ((pull ι).obj ((comparison X₁).inverse.obj A.obj), (pull ι).obj ((pull
              f₁).obj D)))
      ((pullModelConj ι).hom.app A.obj, (pullCompIso ι f₁ f w).inv.app D))
    ((tensorModelIso X₀).inv.naturality (X := (((comparison X₀).inverse.obj
        ((quasiCoherentDerivedPullback' ι).obj A).obj), ((pull f).obj D)))
      (Y := ((pull ι).obj ((comparison X₁).inverse.obj A.obj), (pull ι).obj ((pull f₁).obj D)))
      ((pullModelConj ι).hom.app A.obj, (pullCompIso ι f₁ f w).inv.app D))
  have h₃ := (@Functor.LaxMonoidal.μ_natural _ _ (Scheme.Modules.canonicalDerivedMonoidal X₁) _ _
    (Scheme.Modules.canonicalDerivedMonoidal X₀) (Stacks.Duality.derivedPullback ι)
    (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
      ι.toLRSHom.toShHom).toLaxMonoidal _ _ _ _ ((comparison X₁).counitIso.hom.app A.obj)
    ((StacksDraft.DerivedModel.derivedPullbackModelIso f₁.toLRSHom.toShHom).hom.app D)).symm
  have hP1 := cancel_model_chase
    ((comparison X₀).functor.map ((pullModelConj ι).hom.app A.obj))
    ((comparison X₀).functor.map ((pullModelConj ι).inv.app A.obj))
    ((comparison X₀).counit.app ((Stacks.Duality.derivedPullback ι).obj A.obj))
    ((pullModelIso ι).hom.app ((comparison X₁).inverse.obj A.obj))
    ((Stacks.Duality.derivedPullback ι).map ((comparison X₁).counitIso.hom.app A.obj))
    (Functor.map_hom_inv' _ ((pullModelConj ι).app A.obj))
    (pullModelConj_inv_app_comp_counit ι A.obj)
  have hC := comp_model_cancel
    ((comparison X₀).functor.map ((pullCompIso ι f₁ f w).inv.app D))
    ((comparison X₀).functor.map ((pullCompIso ι f₁ f w).hom.app D))
    ((pullModelIso f).hom.app D) ((pullModelIso ι).hom.app ((pull f₁).obj D))
    ((Stacks.Duality.derivedPullback ι).map ((pullModelIso f₁).hom.app D))
    ((Stacks.Duality.derivedPullbackCompIso ι f₁).hom.app ((comparison Y₀).functor.obj D) ≫
        eqToHom (congrArg (fun t : X₀ ⟶ Y₀ =>
          (Stacks.Duality.derivedPullback t).obj ((comparison Y₀).functor.obj D)) w))
    (eqToHom (congrArg (fun t : X₀ ⟶ Y₀ =>
          (Stacks.Duality.derivedPullback t).obj ((comparison Y₀).functor.obj D)) w).symm ≫
      (Stacks.Duality.derivedPullbackCompIso ι f₁).inv.app ((comparison Y₀).functor.obj D))
    (Functor.map_inv_hom' _ ((pullCompIso ι f₁ f w).app D))
    (by simp)
    (pullCompIso_hom_app_comp_pullModelIso_hom f₁ ι f w D)
  have hκ : ((quasiCoherentDerivedPullbackCompIso ι f₁ ≪≫ quasiCoherentDerivedPullbackCongr
      w).inv.app (toQCoh ⟨D, hD⟩)).hom =
      eqToHom (congrArg (fun t : X₀ ⟶ Y₀ =>
          (Stacks.Duality.derivedPullback t).obj ((comparison Y₀).functor.obj D)) w).symm ≫
      (Stacks.Duality.derivedPullbackCompIso ι f₁).inv.app ((comparison Y₀).functor.obj D) := by
    simp only [Iso.trans_inv, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
      quasiCoherentDerivedPullbackCompIso, quasiCoherentDerivedPullbackCongr,
      NatIso.ofComponents_inv_app, ObjectProperty.isoMk_inv, ObjectProperty.homMk_hom,
      eqToIso.inv, Iso.app_inv]
  have h₅ := congrArg InducedCategory.Hom.hom (braided_whisker_chase
    (quasiCoherentDerivedPullback' ι) A ((quasiCoherentDerivedPullback' f₁).obj (toQCoh ⟨D, hD⟩))
    ((quasiCoherentDerivedPullbackCompIso ι f₁ ≪≫ quasiCoherentDerivedPullbackCongr w).inv.app
        (toQCoh ⟨D, hD⟩)))
  have h₄ := @tensor_three_chase _ _ (Scheme.Modules.canonicalDerivedMonoidal X₀) _ _ _ _ _ _ _ _ _
    ((comparison X₀).functor.map ((pullModelConj ι).hom.app A.obj))
    ((pullModelIso ι).hom.app ((comparison X₁).inverse.obj A.obj))
    ((Stacks.Duality.derivedPullback ι).map ((comparison X₁).counitIso.hom.app A.obj))
    ((comparison X₀).counitIso.hom.app ((quasiCoherentDerivedPullback' ι).obj A).obj)
    ((comparison X₀).functor.map ((pullCompIso ι f₁ f w).inv.app D))
    ((pullModelIso ι).hom.app ((pull f₁).obj D))
    ((Stacks.Duality.derivedPullback ι).map ((pullModelIso f₁).hom.app D))
    ((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app D)
    ((quasiCoherentDerivedPullbackCompIso ι f₁ ≪≫ quasiCoherentDerivedPullbackCongr w).inv.app
        (toQCoh ⟨D, hD⟩)).hom hP1 (by rwa [hκ])
  have e₁ : (((quasiCoherentDerivedPullback' ι).obj A) ◁ (quasiCoherentDerivedPullbackCompIso ι f₁
      ≪≫ quasiCoherentDerivedPullbackCongr w).inv.app (toQCoh ⟨D, hD⟩)).hom =
      @MonoidalCategoryStruct.whiskerLeft _ _ (Scheme.Modules.canonicalDerivedMonoidal
          X₀).toMonoidalCategoryStruct
        ((quasiCoherentDerivedPullback' ι).obj A).obj _ _ ((quasiCoherentDerivedPullbackCompIso ι
            f₁ ≪≫ quasiCoherentDerivedPullbackCongr w).inv.app (toQCoh ⟨D, hD⟩)).hom := rfl
  have e₂ : (Functor.LaxMonoidal.μ (quasiCoherentDerivedPullback' ι) A
      ((quasiCoherentDerivedPullback' f₁).obj (toQCoh ⟨D, hD⟩))).hom =
      @Functor.LaxMonoidal.μ _ _ (Scheme.Modules.canonicalDerivedMonoidal X₁) _ _
          (Scheme.Modules.canonicalDerivedMonoidal X₀) (Stacks.Duality.derivedPullback ι)
        (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal
          ι.toLRSHom.toShHom).toLaxMonoidal A.obj ((quasiCoherentDerivedPullback' f₁).obj (toQCoh
              ⟨D, hD⟩)).obj ≫
        (Stacks.Duality.derivedPullback ι).map (𝟙 _) := rfl
  have e₃ : ((quasiCoherentDerivedPullback' ι).map (β_ A ((quasiCoherentDerivedPullback' f₁).obj
      (toQCoh ⟨D, hD⟩))).hom).hom =
      (Stacks.Duality.derivedPullback ι).map ((swapIso X₁).hom.app (A,
          ((quasiCoherentDerivedPullback' f₁).obj (toQCoh ⟨D, hD⟩)))) := rfl
  have e₄ : (β_ ((quasiCoherentDerivedPullback' ι).obj A) ((quasiCoherentDerivedPullback' f).obj
      (toQCoh ⟨D, hD⟩))).hom.hom = (swapIso X₀).hom.app (((quasiCoherentDerivedPullback' ι).obj
          A), ((quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩))) := rfl
  simp only [ObjectProperty.FullSubcategory.comp_hom] at h₅
  rw [e₁, e₂, CategoryTheory.Functor.map_id, Category.comp_id, e₃, e₄] at h₅
  exact tensor_restriction_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (((quasiCoherentDerivedTensorIsoCurriedTensor X₀).hom.app
        ((quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩))).app
          ((quasiCoherentDerivedPullback' ι).obj A)).hom rfl hL h₁ h₂ h₃ h₄ h₅

end Restriction

/-- Assembling the transpose of the duality formula from its restriction. -/
theorem bridge_chase {C D : Type*} [Category C] [Category D] (L : D ⥤ C)
    {P₀ P₁ P₂ P₃ P₄ P₅ R R₁ R₂ : C} {S₀ S₁ S₂ : D} (G : P₀ ⟶ P₅) (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂)
    (a₃ : P₂ ⟶ P₃) (a₄ : P₃ ⟶ P₄) (a₅ : P₄ ⟶ P₅) (m : P₃ ⟶ L.obj S₀) (x₁ : S₀ ⟶ S₁)
    (x₂ : S₁ ⟶ S₂) (e : L.obj S₂ ⟶ P₅) (r : P₀ ⟶ R) (i : R ⟶ R₁) (rk : R₁ ⟶ R₂)
    (μ : R₂ ⟶ L.obj S₁)
    (hG : G = a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅) (hA : a₄ ≫ a₅ = m ≫ L.map (x₁ ≫ x₂) ≫ e)
    (hB : a₁ ≫ a₂ ≫ a₃ ≫ m ≫ L.map x₁ = r ≫ i ≫ rk ≫ μ) :
    G = r ≫ i ≫ (rk ≫ μ ≫ L.map x₂) ≫ e := by
  subst hG
  rw [hA, L.map_comp]
  simp only [Category.assoc] at hB ⊢
  rw [reassoc_of% hB]

section Bridge

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left)) {K : Std Y.left} (hK : IsDualizing K)

/-- **The transpose of the duality formula of [Stacks, Tag 0AU2] through the comparison
map.** Under the tensor–internal-Hom bijection and the comparison of the models, the isomorphism
`f^!M ≅ D_X(Lf^* D_Y M)` is the comparison of the tensor products, `Lf^* ≅ Lι^* Lf̄^*`, the
tensorator of `Lι^*` and `Lι^*` of the comparison map of Equation 48.8.0.1 for `f̄` followed by
`ā` of the evaluation. -/
theorem comparison_map_curry_upperShriekDualityIso_hom_app (M : (plusCoh Y.left).FullSubcategory) :
    (comparison X.left).functor.map (curry X.left ((upperShriekStd f j).obj M)
        ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K)) (upperShriekDualizing f j hK)
        ((upperShriekDualityIso f j hK).hom.app M)) =
      tensorPullComparison f.left ((quasiCoherentDerivedPullback' j.immersion).obj
          ((twistedInverseImage j.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs
              j.toBase)).obj (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))) (((sheafHom
                  Y.left).obj (op M.obj)).obj K) (qcoh_dual hK M.obj M.property) ≫
        (((quasiCoherentDerivedTensorIsoCurriedTensor X.left).hom.app
          ((quasiCoherentDerivedPullback' f.left).obj (toQCoh ⟨(((sheafHom Y.left).obj (op
              M.obj)).obj K), qcoh_dual hK M.obj M.property⟩))).app
                  ((quasiCoherentDerivedPullback' j.immersion).obj ((twistedInverseImage j.toBase
                      (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj (toQCoh
                          ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)))).hom ≫
        ((quasiCoherentDerivedPullbackCompactificationIsoOfComp f j).inv.app (toQCoh ⟨(((sheafHom
            Y.left).obj (op M.obj)).obj K), qcoh_dual hK M.obj M.property⟩) ▷
                ((quasiCoherentDerivedPullback' j.immersion).obj ((twistedInverseImage j.toBase
                    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj (toQCoh
                        ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))) ≫
          Functor.LaxMonoidal.μ (quasiCoherentDerivedPullback' j.immersion)
            ((quasiCoherentDerivedPullback' j.toBase).obj (toQCoh ⟨(((sheafHom Y.left).obj (op
                M.obj)).obj K), qcoh_dual hK M.obj M.property⟩)) ((twistedInverseImage j.toBase
                    (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj (toQCoh
                        ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)) ≫
          (quasiCoherentDerivedPullback' j.immersion).map (compareWithPullbackTensor j.toBase
                  (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)
          (quasiCoherentDerivedPullbackTensorIso j.toBase).hom
          (twistedInverseImageAdjunction j.toBase
              (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)) (toQCoh ⟨(((sheafHom
                  Y.left).obj (op M.obj)).obj (dualizingObject hK).obj), qcoh_dual hK M.obj
                      M.property⟩)
          (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩) ≫
        (twistedInverseImage j.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs
            j.toBase)).map
          (dualEvaluation ⟨M.obj, plusCoh_le_qcoh _ M.property⟩ (((sheafHom Y.left).obj (op
              M.obj)).obj (dualizingObject hK).obj)
            (qcoh_dual hK M.obj M.property) (dualizingObject hK)
            (bidual Y.left (dualizingObject hK).obj M.obj)))).hom ≫
        (comparison X.left).counitIso.inv.app _ := by
  have h₁ := curry_upperShriekDualityIso_hom_app f j hK M
  have h₂ := curry_dualityIso_hom_app_eq_compareWithPullbackTensor j.toBase hK M
  dsimp only [dualizingObject] at h₁ h₂ ⊢
  have hG := (congrArg (comparison X.left).functor.map h₁).trans
    (((comparison X.left).functor.map_comp _ _).trans (congrArg (_ ≫ ·)
      (((comparison X.left).functor.map_comp _ _).trans (congrArg (_ ≫ ·)
        (((comparison X.left).functor.map_comp _ _).trans (congrArg (_ ≫ ·)
          ((comparison X.left).functor.map_comp _ _)))))))
  have hA := (congrArg (fun t => (comparison X.left).functor.map ((pull j.immersion).map t) ≫
      (comparison X.left).functor.map ((pullModelConj j.immersion).app
        ((rightAdjointStd j.toBase).obj (dualizingObject hK))).inv) h₂).trans
    (map_pull_map_homEquiv_comp_pullModelConj_inv (A₀ := X.left) j.immersion _ _ _)
  have hB := tensorPullComparison_restriction (X₀ := X.left) j.immersion j.toBase f.left
    (immersion_comp_toBase f j) ((twistedInverseImage j.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j.toBase)).obj (toQCoh ⟨M.obj,
            plusCoh_le_qcoh _ M.property⟩)) (((sheafHom Y.left).obj (op M.obj)).obj K)
    (qcoh_dual hK M.obj M.property)
  exact bridge_chase (Stacks.Duality.derivedPullback (X := X.left) j.immersion)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ hG hA hB

end Bridge

/-- A chain of four commutative squares. -/
theorem four_squares_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ Q₀ Q₁ Q₂ Q₃ Q₄ : C}
    (k : P₀ ⟶ Q₀) (s₁ : P₀ ⟶ P₁) (s₂ : P₁ ⟶ P₂) (s₃ : P₂ ⟶ P₃) (s₄ : P₃ ⟶ P₄)
    (t₁ : Q₀ ⟶ Q₁) (t₂ : Q₁ ⟶ Q₂) (t₃ : Q₂ ⟶ Q₃) (t₄ : Q₃ ⟶ Q₄)
    (u₁ : P₁ ⟶ Q₁) (u₂ : P₂ ⟶ Q₂) (u₃ : P₃ ⟶ Q₃) (u₄ : P₄ ⟶ Q₄)
    (h₁ : k ≫ t₁ = s₁ ≫ u₁) (h₂ : u₁ ≫ t₂ = s₂ ≫ u₂) (h₃ : u₂ ≫ t₃ = s₃ ≫ u₃)
    (h₄ : u₃ ≫ t₄ = s₄ ≫ u₄) :
    k ≫ t₁ ≫ t₂ ≫ t₃ ≫ t₄ = (s₁ ≫ s₂ ≫ s₃ ≫ s₄) ≫ u₄ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]

section Naturality

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]

omit [QuasiCompact f] [QuasiSeparated f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] in
/-- **Naturality of `tensorPullComparison` in the object of `D_QCoh(𝒪_X)`.** -/
theorem tensorPullComparison_naturality {A₁ A₂ : quasiCoherentDerivedCategory X} (α : A₁ ⟶ A₂)
    (D : Std Y) (hD : qcoh Y D) :
    (comparison X).functor.map (((tensor X).map ((comparison X).inverse.map α.hom)).app
        ((pull f).obj D)) ≫ tensorPullComparison f A₂ D hD =
      tensorPullComparison f A₁ D hD ≫
        (((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj
          (toQCoh ⟨D, hD⟩))).map α).hom := by
  have h₁ : (comparison X).functor.map (((tensor X).map ((comparison X).inverse.map α.hom)).app
        ((pull f).obj D)) ≫ (comparison X).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso X).inv.app
            ((comparison X).inverse.obj A₂.obj)).app ((pull f).obj D)) =
      (comparison X).functor.map
          (((ProjectionFormulaLocallySmall.standardTensorIso X).inv.app
            ((comparison X).inverse.obj A₁.obj)).app ((pull f).obj D)) ≫
        (comparison X).functor.map
          (((ProjectionFormulaMonoidal.standardTensorBifunctor X).map
            ((comparison X).inverse.map α.hom)).app ((pull f).obj D)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
      (ProjectionFormulaLocallySmall.standardTensorIso X).inv.naturality]
  have h₂ : (comparison X).functor.map
          (((ProjectionFormulaMonoidal.standardTensorBifunctor X).map
            ((comparison X).inverse.map α.hom)).app ((pull f).obj D)) ≫
        (tensorModelIso X).inv.app ((comparison X).inverse.obj A₂.obj, (pull f).obj D) =
      (tensorModelIso X).inv.app ((comparison X).inverse.obj A₁.obj, (pull f).obj D) ≫
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).functor.map ((comparison X).inverse.map α.hom) ×ₘ
            𝟙 ((comparison X).functor.obj ((pull f).obj D))) := by
    have e := (tensorModelIso X).inv.naturality
      (X := ((comparison X).inverse.obj A₁.obj, (pull f).obj D))
      (Y := ((comparison X).inverse.obj A₂.obj, (pull f).obj D))
      ((comparison X).inverse.map α.hom, 𝟙 _)
    have e₁ : (ProjectionFormulaMonoidal.standardTensor X ⋙
        ProjectionFormulaMonoidal.modelFunctor X).map
          (((comparison X).inverse.map α.hom, 𝟙 _) :
            ((comparison X).inverse.obj A₁.obj, (pull f).obj D) ⟶
              ((comparison X).inverse.obj A₂.obj, (pull f).obj D)) =
        (comparison X).functor.map
          (((ProjectionFormulaMonoidal.standardTensorBifunctor X).map
            ((comparison X).inverse.map α.hom)).app ((pull f).obj D)) := by
      change (comparison X).functor.map
        (((ProjectionFormulaMonoidal.standardTensorBifunctor X).map
          ((comparison X).inverse.map α.hom)).app ((pull f).obj D) ≫
          ((ProjectionFormulaMonoidal.standardTensorBifunctor X).obj
            ((comparison X).inverse.obj A₂.obj)).map (𝟙 _)) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    have e₂ : ((ProjectionFormulaMonoidal.modelFunctor X).prod
        (ProjectionFormulaMonoidal.modelFunctor X) ⋙
          @MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          (((comparison X).inverse.map α.hom, 𝟙 _) :
            ((comparison X).inverse.obj A₁.obj, (pull f).obj D) ⟶
              ((comparison X).inverse.obj A₂.obj, (pull f).obj D)) =
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).functor.map ((comparison X).inverse.map α.hom) ×ₘ
            𝟙 ((comparison X).functor.obj ((pull f).obj D))) := by
      change (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).functor.map ((comparison X).inverse.map α.hom) ×ₘ
            (comparison X).functor.map (𝟙 _)) = _
      rw [CategoryTheory.Functor.map_id]
    exact (congrArg (· ≫ _) e₁.symm).trans (e.trans (congrArg (_ ≫ ·) e₂))
  have h₃ : (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).functor.map ((comparison X).inverse.map α.hom) ×ₘ
            𝟙 ((comparison X).functor.obj ((pull f).obj D))) ≫
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).counitIso.hom.app A₂.obj ×ₘ
            (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app D) =
      (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          ((comparison X).counitIso.hom.app A₁.obj ×ₘ
            (StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).hom.app D) ≫
        (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          (α.hom ×ₘ 𝟙 _) := by
    refine ((Functor.map_comp _ _ _).symm.trans ?_).trans (Functor.map_comp _ _ _)
    refine congrArg _ (Prod.hom_ext ?_ ?_)
    · exact (comparison X).counitIso.hom.naturality α.hom
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  have h₄ : (@MonoidalCategory.tensor _ _ (Scheme.Modules.canonicalDerivedMonoidal X)).map
          (α.hom ×ₘ 𝟙 _) ≫
        (swapIso X).hom.app (A₂, (quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩)) =
      (swapIso X).hom.app (A₁, (quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩)) ≫
        (((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj
          (toQCoh ⟨D, hD⟩))).map α).hom := by
    have e := (swapIso X).hom.naturality
      (X := (A₁, (quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩)))
      (Y := (A₂, (quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩))) (α, 𝟙 _)
    have e' : (Stacks.Duality.quasiCoherentDerivedTensorSwap X ⋙ ObjectProperty.ι _).map
        ((α, 𝟙 _) : (A₁, (quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩)) ⟶
          (A₂, (quasiCoherentDerivedPullback' f).obj (toQCoh ⟨D, hD⟩))) =
        (((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj
          (toQCoh ⟨D, hD⟩))).map α).hom := by
      change (((quasiCoherentDerivedTensor X).map (𝟙 _)).app A₁ ≫
        ((quasiCoherentDerivedTensor X).obj _).map α).hom = _
      rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
      rfl
    rw [← e']
    exact e
  exact four_squares_chase _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

end Naturality

/-- Removing identities around a comparison map. -/
theorem id_comparison_chase {C D : Type*} [Category C] [Category D] (a : D ⥤ C) {P : C}
    {R S : D} (i₁ : P ⟶ P) (cmp : P ⟶ a.obj R) (i₂ : R ⟶ R) (ev : R ⟶ S) (h₁ : i₁ = 𝟙 P)
    (h₂ : i₂ = 𝟙 R) :
    (i₁ ≫ cmp ≫ a.map i₂) ≫ a.map ev = cmp ≫ a.map ev := by
  subst h₁ h₂
  simp

/-- The chase behind `comparisonMap_evaluation_compactificationMap`. -/
theorem evaluation_compactification_chase {C C₁ C₂ : Type*} [Category C] [Category C₁]
    [Category C₂] (L₁ : C₁ ⥤ C) (L₂ : C₂ ⥤ C) {P₀ P₁ Q₁ Q₂ : C} {A₁ A₂ B₁ : C₁}
    {A₁' A₂' B₂ : C₂} (a : P₀ ⟶ Q₁) (b₁ : P₀ ⟶ P₁) (m₁ : P₁ ⟶ L₁.obj A₁)
    (b₂ : Q₁ ⟶ Q₂) (m₂ : Q₂ ⟶ L₂.obj A₁') (x₁ : A₁ ⟶ B₁) (p₁ : A₁ ⟶ A₂) (q₁ : A₂ ⟶ B₁)
    (x₂ : A₁' ⟶ B₂) (p₂ : A₁' ⟶ A₂') (q₂ : A₂' ⟶ B₂) (αL : L₁.obj A₂ ⟶ L₂.obj A₂')
    (αZ : L₁.obj B₁ ⟶ L₂.obj B₂) (hx₁ : x₁ = p₁ ≫ q₁) (hx₂ : x₂ = p₂ ≫ q₂)
    (key : b₁ ≫ m₁ ≫ L₁.map p₁ ≫ αL = a ≫ b₂ ≫ m₂ ≫ L₂.map p₂)
    (n : L₁.map q₁ ≫ αZ = αL ≫ L₂.map q₂) :
    a ≫ b₂ ≫ m₂ ≫ L₂.map x₂ = (b₁ ≫ m₁ ≫ L₁.map x₁) ≫ αZ := by
  subst hx₁ hx₂
  simp only [Functor.map_comp, Category.assoc]
  rw [n, ← reassoc_of% key]

section CompactificationMap

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y : FTS S} (f : X ⟶ Y)
  (c₁ c₂ : CompactificationOf (Over.mk f.left)) (g : c₁.space ⟶ c₂.space)
  (hg : g ≫ c₂.toBase = c₁.toBase) (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)

/-- **The comparison map followed by an evaluation, for two compactifications.** For `E`, `L`, `Z`
in `D_QCoh(𝒪_Y)` and `ev : E ⊗ᴸ L ⟶ Z`, the map `Lf^*E ⊗ f^!L ⟶ f^!Z` given by `Lj^*` of the
comparison map of Equation 48.8.0.1 for `f̄` followed by `ā(ev)` is compatible with `α_g`. -/
theorem comparisonMap_evaluation_compactificationMap (E L Z : quasiCoherentDerivedCategory Y.left)
    (ev : ((quasiCoherentDerivedTensor Y.left).obj E).obj L ⟶ Z) :
    (quasiCoherentDerivedPullback' f.left).obj E ◁
        (upperShriekCompactificationMap f c₁ c₂ g hg sq).app L ≫
      (quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₂).inv.app E ▷
        (upperShriek f c₂).obj L ≫
      Functor.LaxMonoidal.μ (quasiCoherentDerivedPullback' c₂.immersion) _ _ ≫
      (quasiCoherentDerivedPullback' c₂.immersion).map
        (compareWithPullbackTensor c₂.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)
          (quasiCoherentDerivedPullbackTensorIso c₂.toBase).hom
          (twistedInverseImageAdjunction c₂.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)) E L ≫
        (twistedInverseImage c₂.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)).map ev) =
    ((quasiCoherentDerivedPullbackCompactificationIsoOfComp f c₁).inv.app E ▷
        (upperShriek f c₁).obj L ≫
      Functor.LaxMonoidal.μ (quasiCoherentDerivedPullback' c₁.immersion) _ _ ≫
      (quasiCoherentDerivedPullback' c₁.immersion).map
        (compareWithPullbackTensor c₁.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase)
          (quasiCoherentDerivedPullbackTensorIso c₁.toBase).hom
          (twistedInverseImageAdjunction c₁.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase)) E L ≫
        (twistedInverseImage c₁.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase)).map ev)) ≫
      (upperShriekCompactificationMap f c₁ c₂ g hg sq).app Z := by
  have key := fun c : CompactificationOf (Over.mk f.left) =>
    (congrArg (· ≫ (twistedInverseImage c.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)).map ev)
      (compareWithPullbackTensor_eq_comparisonMap c.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)
        (quasiCoherentDerivedPullbackTensorIso c.toBase).hom
        (quasiCoherentDerivedPullbackTensorIso_hom_app c.toBase)
        (twistedInverseImageAdjunction c.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase)) E L)).trans
      (id_comparison_chase _ _ _ _ ev rfl rfl)
  exact evaluation_compactification_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (key c₁) (key c₂)
    (comparisonMap_comp_upperShriekCompactificationMap f c₁ c₂ g hg sq E L)
    ((upperShriekCompactificationMap f c₁ c₂ g hg sq).naturality ev)

end CompactificationMap

section CompactificationData

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (c₁ c₂ : CompactificationOf (Over.mk f.left)) (g : c₁.space ⟶ c₂.space)
  (hg : g ≫ c₂.toBase = c₁.toBase) (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)
  {K : Std Y.left} (hK : IsDualizing K)

/-- The transformation `α_g : f^!_{c₁} ⟶ f^!_{c₂}` read at the standard model. -/
abbrev upperShriekStdMap : upperShriekStd f c₁ ⟶ upperShriekStd f c₂ :=
  Functor.whiskerLeft _ (Functor.whiskerRight (upperShriekCompactificationMap f c₁ c₂ g hg sq)
    (ObjectProperty.ι _ ⋙ (comparison X.left).inverse))

/-- `α_g` at the dualizing complex, read at the standard model. -/
abbrev upperShriekDualizingMap :
    upperShriekDualizing f c₁ hK ⟶ upperShriekDualizing f c₂ hK :=
  (comparison X.left).inverse.map
    ((upperShriekCompactificationMap f c₁ c₂ g hg sq).app (dualizingQCoh hK)).hom

/-- `upperShriekDualityIso_compactificationMap` at an object `M` of `D^+_Coh(𝒪_Y)`. -/
theorem upperShriekDualityIso_compactificationMap_app (M : (plusCoh Y.left).FullSubcategory) :
    (upperShriekStdMap f c₁ c₂ g hg sq).app M ≫ (upperShriekDualityIso f c₂ hK).hom.app M =
      (upperShriekDualityIso f c₁ hK).hom.app M ≫
        ((sheafHom X.left).obj (op ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj
          K)))).map (upperShriekDualizingMap f c₁ c₂ g hg sq hK) := by
  have b₁ := comparison_map_curry_upperShriekDualityIso_hom_app f c₁ hK M
  have b₂ := comparison_map_curry_upperShriekDualityIso_hom_app f c₂ hK M
  have hL := curry_naturality_left (X := X.left)
    ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
    (upperShriekDualizing f c₂ hK) ((upperShriekStdMap f c₁ c₂ g hg sq).app M)
    ((upperShriekDualityIso f c₂ hK).hom.app M)
  have hR := curry_naturality_right X.left ((upperShriekStd f c₁).obj M)
    ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
    (upperShriekDualizingMap f c₁ c₂ g hg sq hK) ((upperShriekDualityIso f c₁ hK).hom.app M)
  have h₁ := tensorPullComparison_naturality f.left
    (A₁ := (quasiCoherentDerivedPullback' c₁.immersion).obj ((twistedInverseImage c₁.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c₁.toBase)).obj
        (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)))
    (A₂ := (quasiCoherentDerivedPullback' c₂.immersion).obj ((twistedInverseImage c₂.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)).obj
        (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)))
    ((upperShriekCompactificationMap f c₁ c₂ g hg sq).app
      (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩))
    (((sheafHom Y.left).obj (op M.obj)).obj K) (qcoh_dual hK M.obj M.property)
  have h₂ := (ObjectProperty.FullSubcategory.comp_hom _ _ _).symm.trans
    ((congrArg InducedCategory.Hom.hom
      (((quasiCoherentDerivedTensorIsoCurriedTensor X.left).hom.app
        ((quasiCoherentDerivedPullback' f.left).obj (toQCoh ⟨(((sheafHom Y.left).obj (op
          M.obj)).obj K), qcoh_dual hK M.obj M.property⟩))).naturality
        ((upperShriekCompactificationMap f c₁ c₂ g hg sq).app
          (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩)))).trans
      (ObjectProperty.FullSubcategory.comp_hom _ _ _))
  have h₃ := (ObjectProperty.FullSubcategory.comp_hom _ _ _).symm.trans
    ((congrArg InducedCategory.Hom.hom
      (comparisonMap_evaluation_compactificationMap f c₁ c₂ g hg sq
        (toQCoh ⟨(((sheafHom Y.left).obj (op M.obj)).obj (dualizingObject hK).obj),
          qcoh_dual hK M.obj M.property⟩)
        (toQCoh ⟨M.obj, plusCoh_le_qcoh _ M.property⟩) (toQCoh (dualizingObject hK))
        (dualEvaluation ⟨M.obj, plusCoh_le_qcoh _ M.property⟩ (((sheafHom
            Y.left).obj (op M.obj)).obj (dualizingObject hK).obj)
          (qcoh_dual hK M.obj M.property) (dualizingObject hK)
          (bidual Y.left (dualizingObject hK).obj M.obj)))).trans
      (ObjectProperty.FullSubcategory.comp_hom _ _ _))
  have h₄ := (comparison X.left).counitIso.inv.naturality
    ((upperShriekCompactificationMap f c₁ c₂ g hg sq).app (dualizingQCoh hK)).hom
  dsimp only [dualizingObject] at b₁ b₂ h₃ ⊢
  apply (curry X.left ((upperShriekStd f c₁).obj M)
    ((pull f.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
    (upperShriekDualizing f c₂ hK)).injective
  refine hL.trans (Eq.trans ?_ hR.symm)
  apply (comparison X.left).functor.map_injective
  refine ((comparison X.left).functor.map_comp _ _).trans
    (Eq.trans ?_ ((comparison X.left).functor.map_comp _ _).symm)
  refine (congrArg (_ ≫ ·) b₂).trans (Eq.trans ?_ (congrArg (· ≫ _) b₁).symm)
  exact four_squares_chase _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

/-- **The isomorphism of [Stacks, Tag 0AU2] is compatible with change of compactification.** For a
morphism `g : X̄₁ ⟶ X̄₂` of compactifications of `X` over `Y` with `g⁻¹(X) = X`, the transformation
`α_g : f^!_{X̄₁} ⟶ f^!_{X̄₂}` carries the isomorphism `f^!M ≅ R𝓗om(Lf^* D_Y(M), f^!K)` for `X̄₁` to
the one for `X̄₂`, followed by `α_g` at `K`. -/
theorem upperShriekDualityIso_compactificationMap :
    upperShriekStdMap f c₁ c₂ g hg sq ≫ (upperShriekDualityIso f c₂ hK).hom =
      (upperShriekDualityIso f c₁ hK).hom ≫
        Functor.whiskerLeft ((plusCoh Y.left).ι ⋙ ((sheafHom Y.left).flip.obj K).rightOp ⋙
          (pull f.left).op)
          ((sheafHom X.left).flip.map (upperShriekDualizingMap f c₁ c₂ g hg sq hK)) := by
  ext M
  exact upperShriekDualityIso_compactificationMap_app f c₁ c₂ g hg sq hK M

end CompactificationData

end Stacks.Duality.UpperShriekDuality

end
