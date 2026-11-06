module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstVanishingAndSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplexIsAResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingOnCofinalCoverings

/-!
# Vanishing of cohomology on a family of objects

Let `B` be a family of objects of a site, stable under the objects and the iterated fibre
products occurring in every covering of one of its members. An abelian sheaf which vanishes on
every object of `B` has vanishing cohomology on every object of `B`.

The argument is a dimension shift. On an object of `B` the Čech cohomology of an injective
presheaf vanishes in positive degrees, because the integral Čech complex is a resolution; that
makes the sections functor on `B` exact on a short exact sequence of sheaves, and an induction
on the degree through the long exact sequence of a presentation by an injective object gives
the statement for every degree.

## Main definitions

* `Stacks.CechSite.iteratedFiberProduct` is the iterated fibre product over the target of a
  finite family of arrows of a covering.

## Main results

* `Stacks.CechSite.cohomology_isZero_of_isZero_on_covering_fiberProducts` is the vanishing
  criterion.

## Implementation notes

Iterated fibre products are products in the over-category: binary products there come from the
assumed pullbacks in the site, and its canonical terminal object supplies the empty product.
Sheaf cohomology is Mathlib's `CategoryTheory.Sheaf.H'`, and vanishing is `IsZero`.

The coverings used in the induction are cut down to a small model of the site
(`smallModelCover`), so that the Čech complex is indexed by a `v`-small family; this is what
lets the same statement be used on a large site that is only essentially small.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe x w' w v u

namespace Stacks.CechSite


private lemma isZero_product {β : Type*} {A : Type*} [Category A] [HasZeroObject A]
    [HasZeroMorphisms A] [HasProducts A] (f : β → A)
    (hf : ∀ b, IsZero (f b)) : IsZero (∏ᶜ f) :=
  (limit.isLimit (Discrete.functor f)).isZero_pt (Functor.isZero _ fun b ↦ hf b.as)

private noncomputable instance essentiallySmallSheafEnoughInjectives
    {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}] :
    EnoughInjectives (Sheaf J AddCommGrpCat.{v}) := by
  have : IsGrothendieckAbelian.{v} (Sheaf J AddCommGrpCat.{v}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{v} J AddCommGrpCat.{v}
  infer_instance

/-- **Čech-to-sheaf vanishing over an essentially small site.** Along a cofinal family of
coverings of a collection of objects closed under the fibre products occurring in them,
vanishing of positive-degree Čech cohomology gives vanishing of positive-degree sheaf
cohomology. -/
private theorem sheafCohomology_isZero_of_cechCohomology_isZero_of_essentiallySmall
    {C : Type u} [Category.{max v w} C] [EssentiallySmall.{max v w} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max v w}]
    [HasExt.{x} (Sheaf J AddCommGrpCat.{max v w})]
    (B : Set C)
    (Cov : ∀ U : C,
      Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
    (hProducts : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (F : Sheaf J AddCommGrpCat.{max v w})
    (hCech : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ), 0 < p →
        letI : ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (i a))) := hProducts E hE
        IsZero (cechCohomology E.1 F.obj p))
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' F p U) := by
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max v w} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  exact sheafCohomology_isZero_of_cechCohomology_isZero_of_enoughInjectives J B Cov
    hProducts hCovObjects hCovCofinal F hCech U hU p hp

private noncomputable def smallModelCover
    {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C] {U : C}
    (P : Presieve U) : PreZeroHypercover.{v} U := by
  let e := equivSmallModel.{v} C
  let I : Type v := Σ X : SmallModel.{v} C,
    {g : e.inverse.obj X ⟶ U //
      ∃ (Y : C) (f : Y ⟶ U), P f ∧ ∃ hX : X = e.functor.obj Y,
        g = eqToHom (congrArg e.inverse.obj hX) ≫ e.unitIso.inv.app Y ≫ f}
  exact {
    I₀ := I
    X i := e.inverse.obj i.1
    f i := i.2.1
  }

private lemma smallModelCover_presieve
    {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C] {U : C}
    (P : Presieve U) :
    (smallModelCover P).presieve₀ =
      P.bind (fun {Y} _ _ ↦
        Presieve.singleton ((equivSmallModel.{v} C).unitIso.inv.app Y)) := by
  funext Z g
  refine propext ⟨?_, ?_⟩
  · rintro ⟨⟨X, g', Y, f, hf, rfl, hg⟩⟩
    exact ⟨Y, (equivSmallModel.{v} C).unitIso.inv.app Y, f, hf, Presieve.singleton_self _,
      by simpa [smallModelCover] using hg.symm⟩
  · rintro ⟨Y, h, f, hf, hh, hfac⟩
    cases hh
    rw [← hfac]
    exact (smallModelCover P).presieve₀_f ⟨(equivSmallModel.{v} C).functor.obj Y,
      (equivSmallModel.{v} C).unitIso.inv.app Y ≫ f, Y, f, hf, rfl, by simp⟩

private lemma smallModelCover_isCover
    {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C] [HasPullbacks C]
    (K : Pretopology C) {U : C} (P : Presieve U) (hP : P ∈ K U) :
    (smallModelCover P).presieve₀ ∈ K U := by
  rw [smallModelCover_presieve]
  exact K.transitive P _ hP fun Y _ _ ↦
    K.has_isos ((equivSmallModel.{v} C).unitIso.inv.app Y)

/-- The iterated fibre product over `U` of a finite family selected from a family of arrows
with common target `U`. -/
def iteratedFiberProduct {C : Type u} [Category.{v} C] [HasPullbacks C] {U : C}
    (E : PreZeroHypercover.{w} U) {ι : Type*} [Finite ι] (s : ι → E.I₀) : C := by
  letI : HasBinaryProducts (Over U) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  letI : HasFiniteProducts (Over U) :=
    hasFiniteProducts_of_has_binary_and_terminal
  exact (piObj (fun i ↦ Over.mk (E.f (s i)))).left

/-- If an abelian sheaf vanishes on a family of objects which contains every member and every
iterated fibre product in each covering of one of its objects, then all its cohomology groups
on those objects vanish. -/
theorem cohomology_isZero_of_isZero_on_covering_fiberProducts
    {C : Type u} [Category.{v} C] [EssentiallySmall.{v} C]
    [HasPullbacks C] (K : Pretopology C)
    [HasSheafify K.toGrothendieck AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf K.toGrothendieck AddCommGrpCat.{v})]
    (B : Set C) (F : Sheaf K.toGrothendieck AddCommGrpCat.{v})
    (hF : ∀ V, V ∈ B → IsZero (F.obj.obj (op V)))
    (hB : ∀ (U : C), U ∈ B →
      ∀ (E : PreZeroHypercover.{max u v} U), E.presieve₀ ∈ K U →
        (∀ i, E.X i ∈ B) ∧
          ∀ (p : ℕ) (s : Fin (p + 1) → E.I₀), iteratedFiberProduct E s ∈ B)
    (U : C) (hU : U ∈ B) (p : ℕ) :
    IsZero (F.H' p U) := by
  rcases p with _ | p
  · rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact ⟨fun x y ↦ Abelian.Ext.addEquiv₀.injective <|
      ((sheafificationAdjunction K.toGrothendieck AddCommGrpCat.{v}).homEquiv _ _).injective <|
      ((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv (yoneda.obj U) F.obj).injective <|
      yonedaEquiv.injective <| (AddCommGrpCat.isZero_iff_subsingleton.mp (hF U hU)).elim _ _⟩
  · let Cov := fun V : C ↦ { E : { E : PreZeroHypercover.{v} V //
        E.sieve₀ ∈ K.toGrothendieck V } | V ∈ B ∧ E.1.presieve₀ ∈ K V }
    let (V : C) : HasFiniteProducts (Over V) :=
      letI : HasBinaryProducts (Over V) := Over.ConstructProducts.over_binaryProduct_of_pullback
      hasFiniteProducts_of_has_binary_and_terminal
    have hmem : ∀ {V : C} (E : PreZeroHypercover.{v} V), V ∈ B ∧ E.presieve₀ ∈ K V →
        (∀ i, E.X i ∈ B) ∧ ∀ q (s : Fin (q + 1) → E.I₀),
          (∏ᶜ (fun a ↦ Over.mk (E.f (s a)))).left ∈ B := fun E hE ↦ by
      have h := hB _ hE.1 E.shrink (by simpa using hE.2)
      exact ⟨fun i ↦ h.1 (E.toShrink.s₀ i), fun q s ↦ h.2 q fun a ↦ E.toShrink.s₀ (s a)⟩
    refine sheafCohomology_isZero_of_cechCohomology_isZero_of_essentiallySmall.{w', v, 0, u}
      (J := K.toGrothendieck) B Cov ?_ ?_ ?_ F ?_ U hU (p + 1)
      (Nat.succ_pos _)
    · intros
      infer_instance
    · exact fun E hE ↦ ⟨hE.1, hmem E.1 hE⟩
    · rintro V hV R ⟨P, hP, hPR⟩
      refine ⟨⟨smallModelCover P, _, smallModelCover_isCover K P hP, Sieve.le_generate _⟩,
        ⟨hV, smallModelCover_isCover K P hP⟩, ?_⟩
      rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff,
        Presieve.ofArrows_le_iff]
      rintro ⟨X, g, Y, f, hf, hX, hg⟩
      show R.arrows g
      rw [hg]
      simpa [Category.assoc] using R.downward_closed (hPR Y f hf)
        (eqToHom (congrArg (equivSmallModel.{v} C).inverse.obj hX) ≫
          (equivSmallModel.{v} C).unitIso.inv.app Y)
    · intro V E hE q hq
      apply ShortComplex.isZero_homology_of_isZero_X₂
      show IsZero (∏ᶜ (fun s : Fin (q + 1) → E.1.I₀ ↦
        F.obj.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.1.f (s a)))).left))))
      exact isZero_product _ fun s ↦ hF _ ((hmem E.1 hE).2 q s)


end Stacks.CechSite

end
