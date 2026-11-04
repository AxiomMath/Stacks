module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeBoxKunnethRingChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.UnderivedComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.BaseChangeTensorComparisonOnModels
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.AlgebraicGeometry.DeRham.NaiveCupProductInverseImageBase
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageBaseChange

/-!
# The relative Künneth map of the box product at two complexes concentrated in one degree

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, `W = X ×_S Y` with projections `p` and
`q`, and `ι_X : (X, 𝒪_X) ⟶ (X, a^{-1}𝒪_S)`, `ι_Y`, `ι_W` the identity-on-spaces morphisms to the
inverse-image ringed spaces. The relative Künneth map of [Stacks, Tag 0G4B] at complexes `𝓕^•`
and `𝓖^•` of finite-order differential operators is the Künneth map of [Stacks, Tag 0FLP] for the
inverse-image ringed spaces followed by steps (4) and (5). This file compares it, at complexes
with zero differential concentrated in one degree, with the Künneth map of the fibre product of
schemes, which is invertible by [Stacks, Tag 0FLQ]: the base case of [Stacks, Tag 0FMC].

## Main results

* `Stacks.Cohomology.BoxKunneth.derivedBaseChangeMap_Q_comparison`: the derived base change map of
  [Stacks, Tag 08HY] at the class of a complex, against the underived one.
* `Stacks.Cohomology.BoxKunneth.relativeBoxKunneth_chase`: the base-case coherence, from steps (4)
  and (5) on one side to the base change maps and the relative cup product of `ι_W` on the other,
  given the compatibility of a comparison of total complexes with the naive cup product.
* `Stacks.Cohomology.BoxKunneth.boxTotalToFstSnd` and `isIso_boxTotalToFstSnd`: that comparison,
  `Tot(𝓕^• ⊠ 𝓖^•) ⟶ ι_{W*}Tot(p^*𝓔₀ ⊗ q^*𝓜₀)`, for complexes concentrated in one degree each, and
  its invertibility.
* `Stacks.Cohomology.BoxKunneth.chain_identity`: the compatibility of `boxTotalToFstSnd` with the
  naive cup product, the remaining input of the chase.
* `Stacks.Cohomology.BoxKunneth.isIso_relativeBoxKunnethMap_single`: the base case of
  [Stacks, Tag 0FMC], the relative Künneth map at two flat objects placed in one degree each is an
  isomorphism.

## Implementation notes

The coherences are proved in abstract categories (`single_chase`, `baseChange_Q_chase`) and
instantiated once, with every input taken from the statement of the lemma that produces it
(`type_of%`, and the projections `rhsSnd`, `rhsMid`, `rhsLast₄`): the inputs mix the instance terms
of several import closures, which agree only after unfolding, and a restated input would have to be
re-elaborated against them. The underived base change map is given a declared type
(`underivedBaseChangeComplexMap`) so that its source and target are spelled as the targets of the
degreewise comparisons it is composed with.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRhamDirectImage
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces

namespace Stacks.Cohomology.BoxKunneth

section Abstract

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {D₁ : Type u₂} [Category.{v₂} D₁]
  (T : D ⥤ D ⥤ D) (T₁ : D₁ ⥤ D₁ ⥤ D₁) (R : D₁ ⥤ D)

/-- **The coherence of the base case, abstractly.** -/
theorem single_chase
    {LXQ LYQ LA LB QpA QqB TotAB Box QιTot QXp QYq TotXY QιP QιR QTotι LXK LYM : D}
    {L1K L1M QP QR QTot₁ : D₁}
    (lα : LXQ ⟶ LA) (lβ : LYQ ⟶ LB) (pA : LA ⟶ QpA) (pB : LB ⟶ QqB)
    (tAB : (T.obj QpA).obj QqB ⟶ TotAB) (cQ : TotAB ⟶ Box) (νQ : Box ⟶ QιTot)
    (pfT : QιTot ⟶ R.obj QTot₁)
    (lpX : LXQ ⟶ LXK) (lpY : LYQ ⟶ LYM) (bX : LXK ⟶ R.obj L1K) (bY : LYM ⟶ R.obj L1M)
    (cup₁ : (T.obj (R.obj L1K)).obj (R.obj L1M) ⟶ R.obj ((T₁.obj L1K).obj L1M))
    (cup₂ : (T.obj (R.obj QP)).obj (R.obj QR) ⟶ R.obj ((T₁.obj QP).obj QR))
    (pbX : L1K ⟶ QP) (pbY : L1M ⟶ QR) (tPR : (T₁.obj QP).obj QR ⟶ QTot₁)
    (pX : LXQ ⟶ QXp) (pY : LYQ ⟶ QYq) (uX : QXp ⟶ QιP) (uY : QYq ⟶ QιR)
    (pfP : QιP ⟶ R.obj QP) (pfR : QιR ⟶ R.obj QR)
    (tιPR : (T.obj QιP).obj QιR ⟶ QTotι) (nc : QTotι ⟶ QιTot)
    (tXY : (T.obj QXp).obj QYq ⟶ TotXY) (totφ : TotXY ⟶ QTotι) (totαβ : TotXY ⟶ TotAB)
    (pαX : QXp ⟶ QpA) (pβY : QYq ⟶ QqB)
    (h1X : lα ≫ pA = pX ≫ pαX) (h1Y : lβ ≫ pB = pY ≫ pβY)
    (h5X : lpX ≫ bX ≫ R.map pbX = pX ≫ uX ≫ pfP)
    (h5Y : lpY ≫ bY ≫ R.map pbY = pY ≫ uY ≫ pfR)
    (h2 : (T.map pαX).app QYq ≫ (T.obj QpA).map pβY ≫ tAB = tXY ≫ totαβ)
    (h3 : (T.map uX).app QYq ≫ (T.obj QιP).map uY ≫ tιPR = tXY ≫ totφ)
    (h4 : totαβ ≫ cQ ≫ νQ = totφ ≫ nc)
    (h6 : (Functor.uncurry.obj T).map (R.map pbX ×ₘ R.map pbY) ≫ cup₂ =
      cup₁ ≫ R.map ((Functor.uncurry.obj T₁).map (pbX ×ₘ pbY)))
    (h7 : (Functor.uncurry.obj T).map (pfP ×ₘ pfR) ≫ cup₂ ≫ R.map tPR = tιPR ≫ nc ≫ pfT) :
    (Functor.uncurry.obj T).map (lα ×ₘ lβ) ≫
        ((T.map pA).app LB ≫ (T.obj QpA).map pB ≫ tAB ≫ cQ) ≫ νQ ≫ pfT =
      (Functor.uncurry.obj T).map (lpX ×ₘ lpY) ≫
        ((Functor.uncurry.obj T).map (bX ×ₘ bY) ≫ cup₁) ≫
          R.map ((Functor.uncurry.obj T₁).map (pbX ×ₘ pbY) ≫ tPR) := by
  have u : ∀ {A A' B B' : D} (f : A ⟶ A') (g : B ⟶ B'),
      (Functor.uncurry.obj T).map (f ×ₘ g) = (T.map f).app B ≫ (T.obj A').map g := fun _ _ => rfl
  have e1 : (Functor.uncurry.obj T).map (lα ×ₘ lβ) ≫ (T.map pA).app LB ≫ (T.obj QpA).map pB =
      (Functor.uncurry.obj T).map (pX ×ₘ pY) ≫ (T.map pαX).app QYq ≫ (T.obj QpA).map pβY := by
    rw [← u, ← Functor.map_comp, ← u, ← Functor.map_comp, prod_comp, prod_comp, h1X, h1Y]
  have e2 : (Functor.uncurry.obj T).map (lpX ×ₘ lpY) ≫ (Functor.uncurry.obj T).map (bX ×ₘ bY) ≫
      (Functor.uncurry.obj T).map (R.map pbX ×ₘ R.map pbY) =
      (Functor.uncurry.obj T).map (pX ×ₘ pY) ≫ ((T.map uX).app QYq ≫ (T.obj QιP).map uY) ≫
        (Functor.uncurry.obj T).map (pfP ×ₘ pfR) := by
    rw [← u]
    simp only [← Functor.map_comp, prod_comp, h5X, h5Y]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% h6, reassoc_of% e2, h7, reassoc_of% h3, reassoc_of% e1, reassoc_of% h2,
    reassoc_of% h4]

/-- **The derived base change map at the class of a complex, abstractly.** -/
theorem baseChange_Q_chase {D : Type u₁} [Category.{v₁} D]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ P₁₁ : D}
    (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (c : P₂ ⟶ P₃) (bcQ : P₃ ⟶ P₄) (bcH : P₂ ⟶ P₅)
    (d : P₄ ⟶ P₅) (e : P₅ ⟶ P₆) (e' : P₆ ⟶ P₇) (dpcg : P₁ ⟶ P₈) (ubcH : P₈ ⟶ P₉)
    (un' : P₉ ⟶ P₆) (qh1 : P₈ ⟶ P₁₀) (Qφ : P₁₀ ⟶ P₁₁) (qi2 : P₁₁ ⟶ P₉)
    (H1 : c ≫ bcQ ≫ d = bcH) (H2 : b ≫ bcH ≫ e = dpcg ≫ ubcH ≫ un')
    (H3 : ubcH = qh1 ≫ Qφ ≫ qi2) {x : P₀ ⟶ P₃} {y : P₄ ⟶ P₇} {z : P₀ ⟶ P₁₀} {w : P₁₁ ⟶ P₇}
    (hx : x = a ≫ b ≫ c) (hy : y = d ≫ e ≫ e') (hz : z = a ≫ dpcg ≫ qh1)
    (hw : w = qi2 ≫ un' ≫ e') :
    x ≫ bcQ ≫ y = z ≫ Qφ ≫ w := by
  subst hx hy hz hw H3
  simp only [Category.assoc]
  rw [reassoc_of% H1, reassoc_of% H2]

/-- A composite of two functors carries an isomorphism and its inverse to inverse morphisms. -/
theorem map_map_hom_inv {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type*} [Category C₃] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) {P Q : C₁} (e : P ≅ Q) :
    G.map (F.map e.hom) ≫ G.map (F.map e.inv) = 𝟙 _ := by
  rw [← G.map_comp, ← F.map_comp, e.hom_inv_id, F.map_id, G.map_id]

/-- Cancelling a split monomorphism on the right of a commutative square. -/
theorem comp_eq_of_comp_eq_comp_id {D : Type u₁} [Category.{v₁} D] {P Q R T : D}
    (c : P ⟶ Q) (bcQ : Q ⟶ T) (bcH : P ⟶ R) (m : R ⟶ T) (d : T ⟶ R)
    (h : c ≫ bcQ = bcH ≫ m) (hid : m ≫ d = 𝟙 _) : c ≫ bcQ ≫ d = bcH := by
  rw [reassoc_of% h, hid, Category.comp_id]

/-- Moving an isomorphism across an equation. -/
theorem eq_comp_comp_inv {D : Type u₁} [Category.{v₁} D] {P Q R T : D} (x : P ⟶ Q)
    (e : Q ≅ R) (a : P ⟶ T) (b : T ⟶ R) (h : x ≫ e.hom = a ≫ b) : x = a ≫ b ≫ e.inv := by
  rw [← Category.assoc, ← h, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Three commutative squares pasted horizontally. -/
theorem paste_three {D : Type u₁} [Category.{v₁} D] {P₀ P₁ P₂ P₃ Q₀ Q₁ Q₂ Q₃ : D}
    (u : P₀ ⟶ Q₀) (q : P₀ ⟶ P₁) (q' : Q₀ ⟶ Q₁) (v : P₁ ⟶ Q₁) (d : P₁ ⟶ P₂) (d' : Q₁ ⟶ Q₂)
    (w : P₂ ⟶ Q₂) (k : P₂ ⟶ P₃) (k' : Q₂ ⟶ Q₃) (z : P₃ ⟶ Q₃)
    (h1 : u ≫ q' = q ≫ v) (h2 : v ≫ d' = d ≫ w) (h3 : w ≫ k' = k ≫ z) :
    u ≫ q' ≫ d' ≫ k' = (q ≫ d ≫ k) ≫ z := by
  rw [reassoc_of% h1, reassoc_of% h2, h3]
  simp only [Category.assoc]

/-- The second factor of the right-hand side of an equation `x = t ≫ s`. -/
abbrev rhsSnd {D : Type u₁} [Category.{v₁} D] {A B Z : D} {x : A ⟶ Z} {t : A ⟶ B} {s : B ⟶ Z}
    (_ : x = t ≫ s) : B ⟶ Z := s

/-- The middle factor of the right-hand side of an equation `x = t ≫ m ≫ p`. -/
abbrev rhsMid {D : Type u₁} [Category.{v₁} D] {A B C Z : D} {x : A ⟶ Z} {t : A ⟶ B} {m : B ⟶ C}
    {p : C ⟶ Z} (_ : x = t ≫ m ≫ p) : B ⟶ C := m

/-- The last factor of a fourfold composite on the right-hand side of an equation. -/
abbrev rhsLast₄ {D : Type u₁} [Category.{v₁} D] {A B C E Z : D} {x : A ⟶ Z} {p : A ⟶ B}
    {q : B ⟶ C} {r : C ⟶ E} {s : E ⟶ Z} (_ : x = p ≫ q ≫ r ≫ s) : E ⟶ Z := s

/-- The morphism a functor is applied to, read off an equation `F.map f = g` by unification. -/
abbrev mapArg {C₁ : Type*} [Category C₁] {C₂ : Type*} [Category C₂] {F : C₁ ⥤ C₂} {P Q : C₁}
    {f : P ⟶ Q} {g : F.obj P ⟶ F.obj Q} (_ : F.map f = g) : P ⟶ Q := f

section Total

variable {C₁ C₂ D' : Type*} [Category C₁] [Category C₂] [Category D'] [HasZeroMorphisms C₁]
  [HasZeroMorphisms C₂] [Preadditive D'] (F : C₁ ⥤ C₂ ⥤ D') [F.PreservesZeroMorphisms]
  [∀ X, (F.obj X).PreservesZeroMorphisms] (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
  [HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]

/-- A degree of a total complex all of whose summands vanish vanishes. -/
theorem isZero_mapBifunctor_X_of_isZero (n : ℤ)
    (hz : ∀ i j : ℤ, i + j = n → IsZero ((F.obj (K₁.X i)).obj (K₂.X j))) :
    IsZero ((HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.mapBifunctor.hom_ext fun i j h => (hz i j h).eq_of_src _ _

/-- The inclusion of a summand of a degree of a total complex all of whose other summands vanish
is an isomorphism. -/
theorem isIso_ιMapBifunctor_of_isZero (i j n : ℤ) (h : i + j = n)
    (hz : ∀ i' j' : ℤ, i' + j' = n → ¬ (i' = i ∧ j' = j) →
      IsZero ((F.obj (K₁.X i')).obj (K₂.X j'))) :
    IsIso (HomologicalComplex.ιMapBifunctor K₁ K₂ F (ComplexShape.up ℤ) i j n h) := by
  refine ⟨HomologicalComplex.mapBifunctorDesc fun i' j' h' => if h'' : i' = i ∧ j' = j then
    eqToHom (by rw [h''.1, h''.2]) else 0, ?_, ?_⟩
  · simp
  · refine HomologicalComplex.mapBifunctor.hom_ext fun i' j' h' => ?_
    by_cases h'' : i' = i ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := h''
      simp
    · exact (hz i' j' h' h'').eq_of_src _ _

/-- A tensor of two families, each vanishing off its own degree, vanishes off the pair of
degrees. -/
private theorem isZero_obj_obj_of_ne [HasZeroObject D'] {X : ℤ → C₁} {Y : ℤ → C₂} {n₁ n₂ : ℤ}
    (hX : ∀ p, p ≠ n₁ → IsZero (X p)) (hY : ∀ q, q ≠ n₂ → IsZero (Y q)) (p q : ℤ)
    (h : ¬ (p = n₁ ∧ q = n₂)) : IsZero ((F.obj (X p)).obj (Y q)) := by
  by_cases hp : p = n₁
  · exact (F.obj _).map_isZero (hY q fun hq => h ⟨hp, hq⟩)
  · exact (F.map_isZero (hX p hp)).obj _

end Total

end Abstract

attribute [local instance 100000] HasDerivedCategory.standard


universe u


section PullbackNaturality

variable {Z Z' : RingedSpace.{u, u}} (g : Z ⟶ Z')

/-- **The comparison `Lg^*(QC) ⟶ Q(g^*C)` is natural in the complex.** -/
theorem pullbackComplexComparison_naturality
    {C C' : CochainComplex (SheafOfModules.{u} (structureSheafRing Z')) ℤ} (φ : C ⟶ C') :
    (derivedPullback g).map (DerivedCategory.Q.map φ) ≫ pullbackComplexComparison g C' =
      pullbackComplexComparison g C ≫ DerivedCategory.Q.map
        (((RingedSpaceModuleAdjunction.modulePullback g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) :=
  paste_three _ _ _ _ _ _ _ _ _ _
    ((Functor.map_comp _ _ _).symm.trans ((congrArg (derivedPullback g).map
      (DerivedCategory.quotientCompQhIso_inv_naturality φ)).trans (Functor.map_comp _ _ _)))
    ((derivedPullbackComparison g).naturality ((HomotopyCategory.quotient _ _).map φ))
    (DerivedCategory.quotientCompQhIso_hom_naturality
      (((RingedSpaceModuleAdjunction.modulePullback g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ))

end PullbackNaturality

section BaseChange

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (sq : g' ≫ f = f' ≫ g)

/-- The underived base change map `g^*f_*A ⟶ f'_*g'^*A` on complexes, with source and target
spelled as the targets of the degreewise comparisons. -/
abbrev underivedBaseChangeComplexMap
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    ((RingedSpaceModuleAdjunction.modulePullback g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((pushforwardComplex f).obj A) ⟶
      (pushforwardComplex f').obj
        (((RingedSpaceModuleAdjunction.modulePullback g').mapHomologicalComplex
          (ComplexShape.up ℤ)).obj A) :=
  (NatTrans.mapHomologicalComplex
    (Stacks.AlgebraicGeometry.FlatSourceBaseChange.moduleBaseChangeSquare g' f' f g sq).natTrans
    (ComplexShape.up ℤ)).app A

/-- **The derived base change map at the class of a complex, against the degreewise one.** -/
theorem derivedBaseChangeMap_Q_comparison
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (derivedPullback g).map (pushforwardComparisonQ f A) ≫
      Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq
          (DerivedCategory.Q.obj A) ≫
        (derivedPushforward f').map (pullbackComplexComparison g' A) =
      pullbackComplexComparison g ((pushforwardComplex f).obj A) ≫
        DerivedCategory.Q.map (underivedBaseChangeComplexMap g' f' f g sq A) ≫
        pushforwardComparisonQ f'
          (((RingedSpaceModuleAdjunction.modulePullback g').mapHomologicalComplex
            (ComplexShape.up ℤ)).obj A) := by
  have hnat := Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_naturality g' f' f g sq
    ((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).hom.app A)
  have hid := map_map_hom_inv (derivedPullback g') (derivedPushforward f')
    ((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)).app A)
  have H1 := comp_eq_of_comp_eq_comp_id _ _ _ _ _ hnat hid
  have H2 := Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_Qh_comparison g' f' f g sq
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj A)
  have hq := Stacks.AlgebraicGeometry.FlatSourceBaseChange.underivedBaseChangeSquare_app_quotient
    g' f' f g sq A
  have hQ := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (structureSheafRing S')) ((NatTrans.mapHomologicalComplex
      (Stacks.AlgebraicGeometry.FlatSourceBaseChange.moduleBaseChangeSquare g' f' f g sq).natTrans
      (ComplexShape.up ℤ)).app A)
  have H3 := (congrArg (fun t => DerivedCategory.Qh.map t) hq).trans
    (eq_comp_comp_inv _ ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing S'))).app _) _ _ hQ)
  exact baseChange_Q_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 H3
    ((Functor.map_comp _ _ _).trans (congrArg _ (Functor.map_comp _ _ _)))
    ((Functor.map_comp _ _ _).trans (congrArg _ (Functor.map_comp _ _ _))) rfl rfl

end BaseChange

section Underlying

variable {Z T : Scheme.{u}} {c : Z ⟶ T}

/-- The underlying `𝒪_Z`-module of an object of the category of finite-order differential
operators, at the spelling of the tensor product of sheaves of modules. -/
abbrev underlyingModule (F : FiniteOrderDifferentialOperatorCategory c) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z.toRingedSpace :=
  F.module

/-- The underlying graded module of a complex of finite-order differential operators, as a
complex of `𝒪_Z`-modules with zero differential. -/
def underlyingComplex (K : CochainComplex (FiniteOrderDifferentialOperatorCategory c) ℤ) :
    CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z.toRingedSpace) ℤ where
  X n := underlyingModule (K.X n)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := Limits.zero_comp

/-- For a complex with zero differential, the direct image of its underlying graded module along
`(Z, 𝒪_Z) ⟶ (Z, c^{-1}𝒪_T)` is the complex read over `c^{-1}𝒪_T`, by the identity in each
degree. -/
def underlyingComplexHom (K : CochainComplex (FiniteOrderDifferentialOperatorCategory c) ℤ)
    (hK : ∀ n m, K.d n m = 0) :
    (pushforwardComplex (toInverseImageBase c)).obj (underlyingComplex K) ⟶
      ((FiniteOrderDifferentialOperatorCategory.toInverseImageModules c).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K where
  f n := 𝟙 ((FiniteOrderDifferentialOperatorCategory.toInverseImageModules c).obj (K.X n))
  comm' n m _ := by
    change 𝟙 _ ≫ (FiniteOrderDifferentialOperatorCategory.toInverseImageModules c).map (K.d n m) =
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase c)).map 0 ≫ 𝟙 _
    rw [hK, Functor.map_zero]
    exact (Category.id_comp _).trans ((Functor.map_zero _ _ _).symm.trans (Category.comp_id _).symm)

/-- The direct image along `(Z, 𝒪_Z) ⟶ (Z, c^{-1}𝒪_T)`, which is a restriction of scalars,
reflects zero objects. -/
theorem isZero_of_isZero_pushforward_toInverseImageBase
    (M : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z.toRingedSpace)
    (h : IsZero ((StacksDraft.KFlat.modulePushforward (toInverseImageBase c)).obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  have e := h.eq_of_src ((StacksDraft.KFlat.modulePushforward (toInverseImageBase c)).map (𝟙 M))
    ((StacksDraft.KFlat.modulePushforward (toInverseImageBase c)).map 0)
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact congrArg (fun f => (f.val.app U).hom x) e

/-- The underlying module of a zero object of the category of differential operators vanishes. -/
private theorem isZero_underlyingModule_of_isZero {F : FiniteOrderDifferentialOperatorCategory c}
    (h : IsZero F) : IsZero (underlyingModule F) :=
  isZero_of_isZero_pushforward_toInverseImageBase _
    ((FiniteOrderDifferentialOperatorCategory.toInverseImageModules c).map_isZero h)

end Underlying



section Chase

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
  (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]
  (E₀ : CochainComplex
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X.toRingedSpace) ℤ)
  (M₀ : CochainComplex
    (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y.toRingedSpace) ℤ)

/-- The complex `p^*𝓔₀` on `W = X ×_S Y`. -/
abbrev fstPullbackComplex :
    CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (pullback a b).toRingedSpace) ℤ :=
  (pullbackComplex (pullback.fst a b).toLRSHom.toShHom).obj E₀

/-- The complex `q^*𝓜₀` on `W = X ×_S Y`. -/
abbrev sndPullbackComplex :
    CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (pullback a b).toRingedSpace) ℤ :=
  (pullbackComplex (pullback.snd a b).toLRSHom.toShHom).obj M₀

/-- The total complex `Tot(p^*𝓔₀ ⊗_{𝒪_W} q^*𝓜₀)` on `W = X ×_S Y`. -/
abbrev fstSndTotal :
    CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
      (pullback a b).toRingedSpace) ℤ :=
  (totalComplexPair
      (Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf)).obj
    (fstPullbackComplex a b E₀, sndPullbackComplex a b M₀)

/-- The underived base change map `p⁻¹ι_{X*}𝓔₀ ⟶ ι_{W*}p^*𝓔₀` on complexes, for the first
projection. -/
abbrev fstUnderivedBaseChange :=
  underivedBaseChangeComplexMap (pullback.fst a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase a) (fstProjection a b)
    (toInverseImageBase_comp_fstProjection a b) E₀

/-- The underived base change map `q⁻¹ι_{Y*}𝓜₀ ⟶ ι_{W*}q^*𝓜₀` on complexes, for the second
projection. -/
abbrev sndUnderivedBaseChange :=
  underivedBaseChangeComplexMap (pullback.snd a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase b) (sndProjection a b)
    (toInverseImageBase_comp_sndProjection a b) M₀

/-- The total tensor complex on a pair of morphisms of complexes of `g^{-1}𝒪_S`-modules. -/
abbrev inverseImageTotalMap {W T : Scheme.{u}} {g : W ⟶ T}
    {K₁ L₁ K₂ L₂ : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules
      (SheafedSpace.sheaf (inverseImageBase g))) ℤ} (f : K₁ ⟶ L₁) (h : K₂ ⟶ L₂) :=
  HomologicalComplex.mapBifunctorMap f h
    (Stacks.SheafOfModules.Tensor.sheafTensor (SheafedSpace.sheaf (inverseImageBase g)))
    (ComplexShape.up ℤ)

variable (α : (pushforwardComplex (toInverseImageBase a)).obj E₀ ⟶ leftComplex a K)
    (β : (pushforwardComplex (toInverseImageBase b)).obj M₀ ⟶ rightComplex b L)

/-- The naturality of `Lp^* ⟶ p^*` at the comparison `ι_{X*}𝓔₀ ⟶ 𝓕^•`, one input of the chase. -/
theorem chase_pullbackNaturality_fst :
    type_of% (pullbackComplexComparison_naturality (fstProjection a b) α) :=
  pullbackComplexComparison_naturality (fstProjection a b) α

/-- The naturality of `Lq^* ⟶ q^*` at the comparison `ι_{Y*}𝓜₀ ⟶ 𝓖^•`. -/
theorem chase_pullbackNaturality_snd :
    type_of% (pullbackComplexComparison_naturality (sndProjection a b) β) :=
  pullbackComplexComparison_naturality (sndProjection a b) β

/-- The naturality of the derived-to-ordinary tensor comparison on `W` at the pullbacks of the
two comparisons. -/
theorem chase_toTensorNaturality_box :
    type_of% ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor_naturality
      (((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α)
      (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map β)) :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor_naturality
      (((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α)
      (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map β)

/-- The naturality of the derived-to-ordinary tensor comparison on `W` at the two underived base
change maps. -/
theorem chase_toTensorNaturality_baseChange :
    type_of% ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor_naturality
      (fstUnderivedBaseChange a b E₀) (sndUnderivedBaseChange a b M₀)) :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a)))).toTensor_naturality
      (fstUnderivedBaseChange a b E₀) (sndUnderivedBaseChange a b M₀)

/-- The derived base change map of the first projection at the class of `𝓔₀`. -/
theorem chase_baseChange_fst :
    type_of% (derivedBaseChangeMap_Q_comparison (pullback.fst a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase a) (fstProjection a b)
    (toInverseImageBase_comp_fstProjection a b) E₀) :=
  derivedBaseChangeMap_Q_comparison (pullback.fst a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase a) (fstProjection a b)
    (toInverseImageBase_comp_fstProjection a b) E₀

/-- The derived base change map of the second projection at the class of `𝓜₀`. -/
theorem chase_baseChange_snd :
    type_of% (derivedBaseChangeMap_Q_comparison (pullback.snd a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase b) (sndProjection a b)
    (toInverseImageBase_comp_sndProjection a b) M₀) :=
  derivedBaseChangeMap_Q_comparison (pullback.snd a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase b) (sndProjection a b)
    (toInverseImageBase_comp_sndProjection a b) M₀

/-- The naturality of the relative cup product of `ι_W` at the two pullback comparisons. -/
theorem chase_relativeCupProduct_natural :
    type_of% (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural
    (toInverseImageBase (pullback.fst a b ≫ a))
    (pullbackComplexComparison (pullback.fst a b).toLRSHom.toShHom E₀)
    (pullbackComplexComparison (pullback.snd a b).toLRSHom.toShHom M₀)) :=
  Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural
    (toInverseImageBase (pullback.fst a b ≫ a))
    (pullbackComplexComparison (pullback.fst a b).toLRSHom.toShHom E₀)
    (pullbackComplexComparison (pullback.snd a b).toLRSHom.toShHom M₀)

/-- [Stacks, Tag 0FP3] for `ι_W` at `p^*𝓔₀` and `q^*𝓜₀`. -/
theorem chase_naiveCupProduct :
    type_of% (naiveCupProduct_relativeCupProduct
    (toInverseImageBase (pullback.fst a b ≫ a))
    (fstPullbackComplex a b E₀) (sndPullbackComplex a b M₀)).symm :=
  (naiveCupProduct_relativeCupProduct (toInverseImageBase (pullback.fst a b ≫ a))
    (fstPullbackComplex a b E₀) (sndPullbackComplex a b M₀)).symm

/-- **The base-case coherence of the relative Künneth map.** For `ν` a comparison of the box total
complex with the direct image of `Tot(p^*𝓔₀ ⊗ q^*𝓜₀)` compatible with the step-(5) comparison and
the naive cup product (`h4`), the map `Lp^*(ι_{X*}𝓔₀) ⊗^𝐋 Lq^*(ι_{Y*}𝓜₀) ⟶ ...` obtained from
steps (4) and (5) agrees with the one obtained from the base change maps and the relative cup
product of `ι_W`. -/
theorem relativeBoxKunneth_chase
    (ν : DerivedCategory.Q.obj (boxTotalModules a b K L n₁ n₂) ⟶
      DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase (pullback.fst a b ≫ a))).obj
        (fstSndTotal a b E₀ M₀)))
    (h4 : rhsSnd (chase_toTensorNaturality_box a b K L E₀ M₀ α β) ≫
        rhsLast₄ (boxTotalDerivedComparison_eq a b K L n₁ n₂
          (boxTotalComparison a b K L n₁ n₂)) ≫ ν =
      rhsSnd (chase_toTensorNaturality_baseChange a b E₀ M₀) ≫
        rhsMid (chase_naiveCupProduct a b E₀ M₀)) :
    type_of% (single_chase
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (SheafedSpace.sheaf (pullback a b).toRingedSpace))
    (derivedPushforward (toInverseImageBase (pullback.fst a b ≫ a)))
    (h1X := chase_pullbackNaturality_fst a b K E₀ α)
    (h1Y := chase_pullbackNaturality_snd a b L M₀ β) (h5X := chase_baseChange_fst a b E₀)
    (h5Y := chase_baseChange_snd a b M₀) (h2 := chase_toTensorNaturality_box a b K L E₀ M₀ α β)
    (h3 := chase_toTensorNaturality_baseChange a b E₀ M₀) (h4 := h4)
    (h6 := chase_relativeCupProduct_natural a b E₀ M₀) (h7 := chase_naiveCupProduct a b E₀ M₀)) :=
  single_chase
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (SheafedSpace.sheaf (inverseImageBase (pullback.fst a b ≫ a))))
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      (SheafedSpace.sheaf (pullback a b).toRingedSpace))
    (derivedPushforward (toInverseImageBase (pullback.fst a b ≫ a)))
    (h1X := chase_pullbackNaturality_fst a b K E₀ α)
    (h1Y := chase_pullbackNaturality_snd a b L M₀ β) (h5X := chase_baseChange_fst a b E₀)
    (h5Y := chase_baseChange_snd a b M₀) (h2 := chase_toTensorNaturality_box a b K L E₀ M₀ α β)
    (h3 := chase_toTensorNaturality_baseChange a b E₀ M₀) (h4 := h4)
    (h6 := chase_relativeCupProduct_natural a b E₀ M₀) (h7 := chase_naiveCupProduct a b E₀ M₀)

section Concentrated

variable (hK0 : ∀ p q, K.d p q = 0) (hL0 : ∀ p q, L.d p q = 0)
  (hKz : ∀ p, p ≠ n₁ → IsZero (K.X p)) (hLz : ∀ q, q ≠ n₂ → IsZero (L.X q))

include hKz in
omit [K.IsStrictlyGE n₁] in
/-- Off its degree, the underlying module of a concentrated complex on `X` vanishes. -/
theorem isZero_underlyingModule_left (p : ℤ) (hp : p ≠ n₁) : IsZero (underlyingModule (K.X p)) :=
  isZero_underlyingModule_of_isZero (hKz p hp)

include hLz in
omit [L.IsStrictlyGE n₂] in
/-- Off its degree, the underlying module of a concentrated complex on `Y` vanishes. -/
theorem isZero_underlyingModule_right (q : ℤ) (hq : q ≠ n₂) : IsZero (underlyingModule (L.X q)) :=
  isZero_underlyingModule_of_isZero (hLz q hq)

include hKz hLz in
omit [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] in
/-- Off the pair of degrees, the summands of `Tot(p^*𝓔₀ ⊗ q^*𝓜₀)` vanish. -/
theorem isZero_fstSnd_summand (p q : ℤ) (h : ¬ (p = n₁ ∧ q = n₂)) :
    IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).obj
      ((fstPullbackComplex a b (underlyingComplex K)).X p)).obj
        ((sndPullbackComplex a b (underlyingComplex L)).X q)) :=
  isZero_obj_obj_of_ne _
    (fun p hp => (StacksDraft.KFlat.modulePullback _).map_isZero
      (isZero_underlyingModule_left a K n₁ hKz p hp))
    (fun q hq => (StacksDraft.KFlat.modulePullback _).map_isZero
      (isZero_underlyingModule_right b L n₂ hLz q hq)) p q h

include hKz hLz in
omit [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] in
/-- Off the pair of degrees, the summands of `Tot(𝓕^• ⊠ 𝓖^•)` vanish. -/
theorem isZero_box_summand (p q : ℤ) (h : ¬ (p = n₁ ∧ q = n₂)) :
    IsZero (((FiniteOrderDifferentialOperatorCategory.boxProductCurried a b).obj (K.X p)).obj
      (L.X q)) :=
  isZero_obj_obj_of_ne _ hKz hLz p q h

include hKz hLz in
/-- The inclusion of the only summand of `Tot(𝓕^• ⊠ 𝓖^•)` is an isomorphism. -/
theorem isIso_boxTotalι (n : ℤ) (h : n₁ + n₂ = n) :
    IsIso (boxTotalι a b K L n₁ n₂ n₁ n₂ n h) := by
  have := FiniteOrderDifferentialOperatorCategory.hasMapBifunctor_up_ℤ K L n₁ n₂
  rw [boxTotalι_eq]
  have := isIso_ιMapBifunctor_of_isZero
    (FiniteOrderDifferentialOperatorCategory.boxProductCurried a b)
    K L n₁ n₂ n h (fun p q _ hpq => isZero_box_summand a b K L n₁ n₂ hKz hLz p q hpq)
  exact Functor.map_isIso _ _

include hKz hLz in
omit [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] in
/-- The inclusion of the only summand of `Tot(p^*𝓔₀ ⊗ q^*𝓜₀)` is an isomorphism. -/
theorem isIso_ιFstSnd (n : ℤ) (h : n₁ + n₂ = n) :
    IsIso (HomologicalComplex.ιMapBifunctor (fstPullbackComplex a b (underlyingComplex K))
      (sndPullbackComplex a b (underlyingComplex L))
      (Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf)
      (ComplexShape.up ℤ) n₁ n₂ n h) :=
  isIso_ιMapBifunctor_of_isZero _ _ _ n₁ n₂ n h
    (fun p q _ hpq => isZero_fstSnd_summand a b K L n₁ n₂ hKz hLz p q hpq)

include hKz hLz in
/-- `Tot(𝓕^• ⊠ 𝓖^•)` vanishes outside degree `n₁ + n₂`. -/
theorem isZero_boxTotalModules_X (n : ℤ) (h : n₁ + n₂ ≠ n) :
    IsZero ((boxTotalModules a b K L n₁ n₂).X n) := by
  have := FiniteOrderDifferentialOperatorCategory.hasMapBifunctor_up_ℤ K L n₁ n₂
  refine (FiniteOrderDifferentialOperatorCategory.toInverseImageModules
    (pullback.fst a b ≫ a)).map_isZero ?_
  rw [boxTotal_eq]
  exact isZero_mapBifunctor_X_of_isZero _ _ _ n fun p q hpq =>
    isZero_box_summand a b K L n₁ n₂ hKz hLz p q fun h' => h (by obtain ⟨rfl, rfl⟩ := h'; exact hpq)

include hKz hLz in
/-- The direct image of `Tot(p^*𝓔₀ ⊗ q^*𝓜₀)` vanishes outside degree `n₁ + n₂`. -/
theorem isZero_pushforward_fstSndTotal_X (n : ℤ) (h : n₁ + n₂ ≠ n) :
    IsZero (((pushforwardComplex (toInverseImageBase (pullback.fst a b ≫ a))).obj
      (fstSndTotal a b (underlyingComplex K) (underlyingComplex L))).X n) :=
  (StacksDraft.KFlat.modulePushforward _).map_isZero
    (isZero_mapBifunctor_X_of_isZero _ _ _ n fun p q hpq =>
      isZero_fstSnd_summand a b K L n₁ n₂ hKz hLz p q fun h' =>
        h (by obtain ⟨rfl, rfl⟩ := h'; exact hpq))

/-- `𝓕 ⊠ 𝓖`, read over `f^{-1}𝒪_S`, is the direct image of `p^*𝓕 ⊗_{𝒪_W} q^*𝓖` along
`(W, 𝒪_W) ⟶ (W, f^{-1}𝒪_S)`; this is the identity, written between the two spellings. -/
abbrev boxProductRelativeToPushforward (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    (FiniteOrderDifferentialOperatorCategory.boxProductRelative a b).obj (F, G) ⟶
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf).obj
          ((StacksDraft.KFlat.modulePullback (pullback.fst a b).toLRSHom.toShHom).obj
            (underlyingModule F))).obj
          ((StacksDraft.KFlat.modulePullback (pullback.snd a b).toLRSHom.toShHom).obj
            (underlyingModule G))) :=
  𝟙 _

/-- **The comparison of the box total complex with the direct image of the total tensor complex
of the pullbacks**, for complexes concentrated in one degree each: in degree `n₁ + n₂` it is the
inverse of the inclusion of the only summand `𝓕 ⊠ 𝓖` followed by the inclusion of the only summand
`p^*𝓕 ⊗ q^*𝓖`, and it vanishes in the other degrees. -/
def boxTotalToFstSnd : boxTotalModules a b K L n₁ n₂ ⟶
    (pushforwardComplex (toInverseImageBase (pullback.fst a b ≫ a))).obj
      (fstSndTotal a b (underlyingComplex K) (underlyingComplex L)) where
  f n := if h : n₁ + n₂ = n then
      haveI := isIso_boxTotalι a b K L n₁ n₂ hKz hLz n h
      inv (boxTotalι a b K L n₁ n₂ n₁ n₂ n h) ≫
        boxProductRelativeToPushforward a b (K.X n₁) (L.X n₂) ≫
        (StacksDraft.KFlat.modulePushforward _).map (HomologicalComplex.ιMapBifunctor
          (fstPullbackComplex a b (underlyingComplex K))
          (sndPullbackComplex a b (underlyingComplex L))
          (Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf)
          (ComplexShape.up ℤ) n₁ n₂ n h)
    else 0
  comm' n m hnm := by
    have hnm' : n + 1 = m := hnm
    by_cases h : n₁ + n₂ = n
    · exact (isZero_pushforward_fstSndTotal_X a b K L n₁ n₂ hKz hLz m (by omega)).eq_of_tgt _ _
    · exact (isZero_boxTotalModules_X a b K L n₁ n₂ hKz hLz n h).eq_of_src _ _

/-- In degree `n₁ + n₂`, `boxTotalToFstSnd` is the displayed composite. -/
private theorem boxTotalToFstSnd_f_eq (n : ℤ) (h : n₁ + n₂ = n)
    [IsIso (boxTotalι a b K L n₁ n₂ n₁ n₂ n h)] :
    (boxTotalToFstSnd a b K L n₁ n₂ hKz hLz).f n =
      inv (boxTotalι a b K L n₁ n₂ n₁ n₂ n h) ≫
        boxProductRelativeToPushforward a b (K.X n₁) (L.X n₂) ≫
        (StacksDraft.KFlat.modulePushforward _).map (HomologicalComplex.ιMapBifunctor
          (fstPullbackComplex a b (underlyingComplex K))
          (sndPullbackComplex a b (underlyingComplex L))
          (Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf)
          (ComplexShape.up ℤ) n₁ n₂ n h) :=
  dite_eq_left h

include hKz hLz in
/-- The components of the comparison are isomorphisms. -/
theorem isIso_boxTotalToFstSnd_f (n : ℤ) :
    IsIso ((boxTotalToFstSnd a b K L n₁ n₂ hKz hLz).f n) := by
  by_cases h : n₁ + n₂ = n
  · have := isIso_boxTotalι a b K L n₁ n₂ hKz hLz n h
    have := isIso_ιFstSnd a b K L n₁ n₂ hKz hLz n h
    rw [boxTotalToFstSnd_f_eq a b K L n₁ n₂ hKz hLz n h]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' (inferInstanceAs (IsIso (𝟙 _)))
      (@Functor.map_isIso _ _ _ _ _ _ _ _ (isIso_ιFstSnd a b K L n₁ n₂ hKz hLz n h)))
  · exact ⟨⟨0, (isZero_boxTotalModules_X a b K L n₁ n₂ hKz hLz n h).eq_of_src _ _,
      (isZero_pushforward_fstSndTotal_X a b K L n₁ n₂ hKz hLz n h).eq_of_src _ _⟩⟩

include hKz hLz in
/-- **The comparison of the two total complexes is an isomorphism.** -/
theorem isIso_boxTotalToFstSnd : IsIso (boxTotalToFstSnd a b K L n₁ n₂ hKz hLz) :=
  have := isIso_boxTotalToFstSnd_f a b K L n₁ n₂ hKz hLz
  HomologicalComplex.Hom.isIso_of_components _

/-- The total tensor complex of the two comparisons `ι_{X*}𝓔₀ ⟶ 𝓕^•` and `ι_{Y*}𝓜₀ ⟶ 𝓖^•`,
read off the toTensor naturality the chase consumes. -/
abbrev chainLeft :=
  mapArg (Eq.refl (rhsSnd (chase_toTensorNaturality_box a b K L (underlyingComplex K)
    (underlyingComplex L) (underlyingComplexHom K hK0) (underlyingComplexHom L hL0))))

/-- The total tensor complex of the two underived base change maps. -/
abbrev chainRight :=
  mapArg (Eq.refl (rhsSnd (chase_toTensorNaturality_baseChange a b (underlyingComplex K)
    (underlyingComplex L))))

/-- The naive cup product of `ι_W` at `p^*𝓔₀` and `q^*𝓜₀`. -/
abbrev chainNaive :=
  mapArg (Eq.refl (rhsMid (chase_naiveCupProduct a b (underlyingComplex K) (underlyingComplex L))))

end Concentrated

end Chase

section Isos

variable {Z T : Scheme.{u}} (c : Z ⟶ T)

/-- **The derived direct image along `(Z, 𝒪_Z) ⟶ (Z, c^{-1}𝒪_T)` is computed degreewise**: the
comparison `Q(ι_*A) ⟶ Rι_*(QA)` is invertible. -/
theorem isIso_pushforwardComparisonQ_toInverseImageBase
    (A : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z.toRingedSpace) ℤ) :
    IsIso (pushforwardComparisonQ (toInverseImageBase c) A) := by
  have : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase c)) :=
    inferInstanceAs (PreservesFiniteColimits (pushforward (toInverseImageBase c)))
  have h3 : IsIso ((derivedPushforward (toInverseImageBase c)).map
      (((DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
          Z.toRingedSpace)).app A).hom)) :=
    ((derivedPushforward (toInverseImageBase c)).mapIso ((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
        Z.toRingedSpace)).app A)).isIso_hom
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso'
    (Stacks.Cohomology.ExactPushforwardAdjunction.isIso_derivedPushforwardUnit_app
      (toInverseImageBase c) _) h3)

section Concentrated

variable {c} (K : CochainComplex (FiniteOrderDifferentialOperatorCategory c) ℤ) (n : ℤ)
  (hKz : ∀ p, p ≠ n → IsZero (K.X p))

include hKz in
/-- The underlying graded module of a complex concentrated in degree `n` is isomorphic to a module
placed in degree `n`. -/
theorem exists_underlyingComplex_iso_single :
    ∃ M, Nonempty (underlyingComplex K ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj M) := by
  have hz : ∀ p, p ≠ n → IsZero ((underlyingComplex K).X p) := fun p hp =>
    isZero_underlyingModule_of_isZero (hKz p hp)
  have : (underlyingComplex K).IsStrictlyGE n :=
    ((underlyingComplex K).isStrictlyGE_iff n).2 fun p hp => hz p (by omega)
  have : (underlyingComplex K).IsStrictlyLE n :=
    ((underlyingComplex K).isStrictlyLE_iff n).2 fun p hp => hz p (by omega)
  exact (underlyingComplex K).exists_iso_single n

include hKz in
/-- **The underlying graded module of a complex concentrated in one degree with a flat term is
K-flat.** -/
theorem kFlat_underlyingComplex
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.sheaf)
      (underlyingModule (K.X n))) :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z.toRingedSpace
      (underlyingComplex K) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_underlyingComplex_iso_single K n hKz
  have hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.sheaf) M :=
    Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso
      ((HomologicalComplex.eval _ _ n).mapIso e ≪≫
        HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n M) hflat
  exact CochainComplex.KFlatBifunctor.KFlat.of_iso _
    (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat Z.sheaf _ hM n) e.symm

end Concentrated

/-- **A K-flat complex computes the derived pullback**: the comparison `Lg^*(QC) ⟶ Q(g^*C)` is
invertible at a K-flat complex. -/
theorem isIso_pullbackComplexComparison_of_kFlat {Z' Z'' : RingedSpace.{u, u}} (g : Z' ⟶ Z'')
    (C : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z'') ℤ)
    (hC : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z'' C) :
    IsIso (pullbackComplexComparison g C) := by
  have h2 := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    g C hC
  have h1 : IsIso ((derivedPullback g).map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing Z''))).inv.app C)) :=
    ((derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (structureSheafRing Z''))).app C).symm).isIso_hom
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 (((DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (structureSheafRing Z'))).app _).isIso_hom))

end Isos

section AbstractAssembly

/-- The chase for one summand of the chain identity: the two composites out of a summand agree once
each factor has been moved past the summand inclusions. -/
theorem summand_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ R₁ R₂ : C}
    {ι₁ : P₀ ⟶ P₁} {M₁f : P₁ ⟶ P₂} {cf : P₂ ⟶ P₃} {νf : P₃ ⟶ P₄} {M₂f : P₁ ⟶ R₂} {mf : R₂ ⟶ P₄}
    {x₁ : P₀ ⟶ Q₁} {ι₂ : Q₁ ⟶ P₂} {rb : Q₁ ⟶ Q₂} {bι : Q₂ ⟶ P₃} {e : Q₂ ⟶ Q₃} {y' : Q₃ ⟶ P₄}
    {x₂ : P₀ ⟶ R₁} {ι₃ : R₁ ⟶ R₂} {lax : R₁ ⟶ Q₃}
    (hrb : x₁ ≫ rb ≫ e = x₂ ≫ lax)
    (H5 : ι₁ ≫ M₂f = x₂ ≫ ι₃) (H1 : ι₁ ≫ M₁f = x₁ ≫ ι₂) (H3 : ι₂ ≫ cf = rb ≫ bι)
    (H4 : bι ≫ νf = e ≫ y') (H6 : ι₃ ≫ mf = lax ≫ y') :
    ι₁ ≫ M₁f ≫ cf ≫ νf = ι₁ ≫ M₂f ≫ mf := by
  rw [reassoc_of% H1, reassoc_of% H3, H4, reassoc_of% H5, H6, reassoc_of% hrb]

/-- The first factor of the right-hand side of an equation `x = t ≫ s`. -/
abbrev rhsFst {C : Type*} [Category C] {A B Z : C} {x : A ⟶ Z} {f : A ⟶ B} {g : B ⟶ Z}
    (_ : x = f ≫ g) : A ⟶ B := f

/-- Two morphisms of a bifunctor applied componentwise compose componentwise. -/
theorem bifunctor_map_comp_map {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    (T : C₁ ⥤ C₂ ⥤ C₃) {A A' A'' : C₁} {B B' B'' : C₂} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {g : B ⟶ B'} {g' : B' ⟶ B''} {F : A ⟶ A''} {G : B ⟶ B''} (hF : f ≫ f' = F)
    (hG : g ≫ g' = G) :
    ((T.map f).app B ≫ (T.obj A').map g) ≫ ((T.map f').app B' ≫ (T.obj A'').map g') =
      (T.map F).app B ≫ (T.obj A'').map G := by
  subst hF hG
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← Category.assoc ((T.obj A').map g), (T.map f').naturality g]
  simp only [Category.assoc]

/-- A composite through `rb = l₁ ≫ l₂`, regrouped along the two legs. -/
theorem comp_legs_eq {C : Type*} [Category C] {P₀ Q₁ Q₂ Q₃ Q₄ : C} {x₁ : P₀ ⟶ Q₁} {rb : Q₁ ⟶ Q₂}
    {l₁ : Q₁ ⟶ Q₃} {l₂ : Q₃ ⟶ Q₂} {e : Q₂ ⟶ Q₄} {x₂ : P₀ ⟶ Q₃} {lax : Q₃ ⟶ Q₄}
    (hrb : rb = l₁ ≫ l₂) (h : x₁ ≫ l₁ = x₂) (h' : l₂ ≫ e = lax) :
    x₁ ≫ rb ≫ e = x₂ ≫ lax := by
  rw [hrb, Category.assoc, reassoc_of% h, h']

/-- A functor carries an equation between a threefold and a twofold composite to the same equation
between the images. -/
theorem map_comp_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P₀ P₁ P₂ P₃ R : C}
    {f : P₀ ⟶ P₁} {g : P₁ ⟶ P₂} {h : P₂ ⟶ P₃} {k : P₀ ⟶ R} {l : R ⟶ P₃}
    (e : f ≫ g ≫ h = k ≫ l) : F.map f ≫ F.map g ≫ F.map h = F.map k ≫ F.map l := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, e]

/-- Naturality in each of two variables gives naturality in both at once. -/
theorem naturality_both {C D : Type*} [Category C] [Category D] (F : D ⥤ C) {s₀ s' s₂ : C}
    {t₀ t' t₂ : D} {nL : s₀ ⟶ s'} {nR : s' ⟶ s₂} {κ₀ : s₀ ⟶ F.obj t₀} {κ' : s' ⟶ F.obj t'}
    {κ₂ : s₂ ⟶ F.obj t₂} {mL : t₀ ⟶ t'} {mR : t' ⟶ t₂}
    (hL : nL ≫ κ' = κ₀ ≫ F.map mL) (hR : nR ≫ κ₂ = κ' ≫ F.map mR) :
    (nL ≫ nR) ≫ κ₂ = κ₀ ≫ F.map (mL ≫ mR) := by
  rw [Category.assoc, hR, reassoc_of% hL, F.map_comp]

/-- **The final step of the base case, abstractly.** If `κ₂ ≫ F.map btdc` and `κ₁ ≫ F.map bcc` are
related by the two naturality squares `nat1`, `nat2` with invertible horizontal maps and by the
chase `chase` with invertible `ν` and `Rm`, the first is invertible as soon as the second is. -/
theorem isIso_of_kunneth_chase {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {s₀ s₁ s₂ : C} {t₀ t₁ t₂ B B' R : D}
    {κ₀ : s₀ ⟶ F.obj t₀} {κ₁ : s₁ ⟶ F.obj t₁} {κ₂ : s₂ ⟶ F.obj t₂}
    {n₁ : s₀ ⟶ s₁} {n₂ : s₀ ⟶ s₂} {m₁ : t₀ ⟶ t₁} {m₂ : t₀ ⟶ t₂}
    {btdc : t₂ ⟶ B} {bcc : t₁ ⟶ R} {ν : B ⟶ B'} {Rm : R ⟶ B'}
    (nat1 : n₁ ≫ κ₁ = κ₀ ≫ F.map m₁) (nat2 : n₂ ≫ κ₂ = κ₀ ≫ F.map m₂)
    (chase : m₂ ≫ btdc ≫ ν = m₁ ≫ bcc ≫ Rm)
    (hn₁ : IsIso n₁) (hn₂ : IsIso n₂) (hν : IsIso ν) (hRm : IsIso Rm)
    (hJ : IsIso (κ₁ ≫ F.map bcc)) : IsIso (κ₂ ≫ F.map btdc) := by
  have h : n₂ ≫ (κ₂ ≫ F.map btdc) ≫ F.map ν = n₁ ≫ (κ₁ ≫ F.map bcc) ≫ F.map Rm := by
    simp only [Category.assoc]
    rw [reassoc_of% nat2, reassoc_of% nat1, ← F.map_comp, ← F.map_comp, ← F.map_comp,
      ← F.map_comp, chase]
  have e : κ₂ ≫ F.map btdc = inv n₂ ≫ n₁ ≫ (κ₁ ≫ F.map bcc) ≫ F.map Rm ≫ inv (F.map ν) := by
    rw [IsIso.eq_inv_comp, ← cancel_mono (F.map ν)]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    simpa only [Category.assoc] using h
  rw [e]
  infer_instance

/-- The first factor of the left-hand side of an equation `x ≫ y = w`. -/
abbrev eqLhsHead {D : Type*} [Category D] {P Q R : D} {x : P ⟶ Q} {y : Q ⟶ R} {w : P ⟶ R}
    (_ : x ≫ y = w) : P ⟶ Q := x

/-- The last factor of the left-hand side of an equation `x ≫ y ≫ z = x' ≫ y' ≫ z'`. -/
abbrev eqLhsLast {D : Type*} [Category D] {P Q R S T U : D} {x : P ⟶ Q} {y : Q ⟶ R} {z : R ⟶ S}
    {x' : P ⟶ T} {y' : T ⟶ U} {z' : U ⟶ S} (_ : x ≫ y ≫ z = x' ≫ y' ≫ z') : R ⟶ S := z

/-- The last factor of the right-hand side of an equation `x ≫ y ≫ z = x' ≫ y' ≫ z'`. -/
abbrev eqRhsLast {D : Type*} [Category D] {P Q R S T U : D} {x : P ⟶ Q} {y : Q ⟶ R} {z : R ⟶ S}
    {x' : P ⟶ T} {y' : T ⟶ U} {z' : U ⟶ S} (_ : x ≫ y ≫ z = x' ≫ y' ≫ z') : U ⟶ S := z'

/-- The middle factor of the right-hand side of an equation `x ≫ y ≫ z = x' ≫ y' ≫ z'`. -/
abbrev eqRhsMid {D : Type*} [Category D] {P Q R S T U : D} {x : P ⟶ Q} {y : Q ⟶ R} {z : R ⟶ S}
    {x' : P ⟶ T} {y' : T ⟶ U} {z' : U ⟶ S} (_ : x ≫ y ≫ z = x' ≫ y' ≫ z') : T ⟶ U := y'

/-- The morphism `c` of an invertibility statement `IsIso (κ ≫ F.map c)`. -/
abbrev isIsoCompMapArg {C D : Type*} [Category C] [Category D] {F : D ⥤ C} {s : C} {t r : D}
    {κ : s ⟶ F.obj t} {c : t ⟶ r} (_ : IsIso (κ ≫ F.map c)) : t ⟶ r := c

/-- Congruence of `(T.map f ×ₘ g) ≫ v` in `f` and `g`. -/
theorem uncurry_map_comp_congr {D : Type*} [Category D] (T : D ⥤ D ⥤ D) {A A' P P' R : D}
    {bX bX' : A ⟶ A'} {bY bY' : P ⟶ P'} (cup : (T.obj A').obj P' ⟶ R) (hX : bX = bX')
    (hY : bY = bY') :
    (Functor.uncurry.obj T).map (bX ×ₘ bY) ≫ cup =
      (Functor.uncurry.obj T).map (bX' ×ₘ bY') ≫ cup := by
  subst hX hY
  rfl

/-- `isIso_of_kunneth_chase` with the second-level map of the invertibility hypothesis given up to
an equation. -/
theorem isIso_of_kunneth_chase_of_eq {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {s₀ s₁ s₂ : C} {t₀ t₁ t₂ B B' R : D}
    {κ₀ : s₀ ⟶ F.obj t₀} {κ₁ : s₁ ⟶ F.obj t₁} {κ₂ : s₂ ⟶ F.obj t₂}
    {n₁ : s₀ ⟶ s₁} {n₂ : s₀ ⟶ s₂} {m₁ : t₀ ⟶ t₁} {m₂ : t₀ ⟶ t₂}
    {btdc : t₂ ⟶ B} {bcc bcc' : t₁ ⟶ R} {ν : B ⟶ B'} {Rm : R ⟶ B'}
    (nat1 : n₁ ≫ κ₁ = κ₀ ≫ F.map m₁) (nat2 : n₂ ≫ κ₂ = κ₀ ≫ F.map m₂)
    (chase : m₂ ≫ btdc ≫ ν = m₁ ≫ bcc ≫ Rm)
    (hn₁ : IsIso n₁) (hn₂ : IsIso n₂) (hν : IsIso ν) (hRm : IsIso Rm) (hc : bcc = bcc')
    (hJ : IsIso (κ₁ ≫ F.map bcc')) : IsIso (κ₂ ≫ F.map btdc) := by
  subst hc
  exact isIso_of_kunneth_chase F nat1 nat2 chase hn₁ hn₂ hν hRm hJ

end AbstractAssembly

section Assembly

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (K : CochainComplex (FiniteOrderDifferentialOperatorCategory a) ℤ)
  (L : CochainComplex (FiniteOrderDifferentialOperatorCategory b) ℤ)
  (n₁ n₂ : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂]
  (hK0 : ∀ p q, K.d p q = 0) (hL0 : ∀ p q, L.d p q = 0)
  (hKz : ∀ p, p ≠ n₁ → IsZero (K.X p)) (hLz : ∀ q, q ≠ n₂ → IsZero (L.X q))

/-- On the only summand, the comparison `boxTotalToFstSnd` is the inclusion of the only summand of
`Tot(p^*𝓔₀ ⊗ q^*𝓜₀)`. -/
theorem boxTotalι_comp_boxTotalToFstSnd (n : ℤ) (h : n₁ + n₂ = n) :
    boxTotalι a b K L n₁ n₂ n₁ n₂ n h ≫ (boxTotalToFstSnd a b K L n₁ n₂ hKz hLz).f n =
      boxProductRelativeToPushforward a b (K.X n₁) (L.X n₂) ≫
        (StacksDraft.KFlat.modulePushforward _).map (HomologicalComplex.ιMapBifunctor
          (fstPullbackComplex a b (underlyingComplex K))
          (sndPullbackComplex a b (underlyingComplex L))
          (Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf)
          (ComplexShape.up ℤ) n₁ n₂ n h) := by
  have := isIso_boxTotalι a b K L n₁ n₂ hKz hLz n h
  rw [boxTotalToFstSnd_f_eq a b K L n₁ n₂ hKz hLz n h]
  exact IsIso.hom_inv_id_assoc _ _

/-- The total tensor complex on a pair of morphisms of complexes of `g^{-1}𝒪_S`-modules, with the
instances seated as in `inverseImageTensorTotal`. -/
abbrev boxTotalMap {W T : Scheme.{u}} {g : W ⟶ T}
    {K₁ L₁ K₂ L₂ : CochainComplex (Modules (inverseImageBase g)) ℤ} (f : K₁ ⟶ L₁) (h : K₂ ⟶ L₂) :=
  @HomologicalComplex.mapBifunctorMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ K₁ L₁ K₂ L₂ f h
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (SheafedSpace.sheaf (inverseImageBase g)))
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
    (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
    (ComplexShape.up ℤ) _
    (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
      (SheafedSpace.sheaf (inverseImageBase g)) K₁ K₂)
    (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
      (SheafedSpace.sheaf (inverseImageBase g)) L₁ L₂) _

/-- The summand inclusion with the instances seated as in `inverseImageTensorTotal`. -/
abbrev boxTotalIota {W T : Scheme.{u}} {g : W ⟶ T}
    (K₁ K₂ : CochainComplex (Modules (inverseImageBase g)) ℤ) (i j n : ℤ) (h : i + j = n) :=
  @HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _ _ _ _ _ _ _ K₁ K₂
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (SheafedSpace.sheaf (inverseImageBase g)))
    (AlgebraicGeometry.SheafOfModules.tensorFunctor_preservesZeroMorphisms _ _ _)
    (fun M => AlgebraicGeometry.SheafOfModules.tensorFunctor_obj_preservesZeroMorphisms _ M _ _)
    (ComplexShape.up ℤ) _
    (Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor
      (SheafedSpace.sheaf (inverseImageBase g)) K₁ K₂) _ i j n h

/-- The total tensor complex of a pair of morphisms on one summand. -/
theorem ι_boxTotalMap {W T : Scheme.{u}} {g : W ⟶ T}
    {K₁ L₁ K₂ L₂ : CochainComplex (Modules (inverseImageBase g)) ℤ} (f : K₁ ⟶ L₁) (h : K₂ ⟶ L₂)
    (i j n : ℤ) (hij : i + j = n) :
    boxTotalIota K₁ K₂ i j n hij ≫ (boxTotalMap f h).f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (SheafedSpace.sheaf (inverseImageBase g))).map
          (f.f i)).app (K₂.X j) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor (SheafedSpace.sheaf (inverseImageBase g))).obj
          (L₁.X i)).map (h.f j) ≫ boxTotalIota L₁ L₂ i j n hij := by
  apply (config := { synthAssignedInstances := false }) HomologicalComplex.ι_mapBifunctorMap

/-- The step-(5) comparison on one summand is the degreewise comparison. -/
theorem iota_hom_box (n : ℤ) (hpq : n₁ + n₂ = n) :
    boxTotalIota (leftInverseImageComplex a b K) (rightInverseImageComplex a b L) n₁ n₂ n hpq ≫
      (boxTotalComparison a b K L n₁ n₂).hom.f n =
    FiniteOrderDifferentialOperatorCategory.relativeBoxComparison a b (K.X n₁) (L.X n₂) ≫
      boxTotalι a b K L n₁ n₂ n₁ n₂ n hpq :=
  (boxTotalComparison a b K L n₁ n₂).ι_hom n₁ n₂ n hpq

omit [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] in
/-- [Stacks, Tag 0FUU] (A2) at `p^*𝓔₀` and `q^*𝓜₀`: the naive cup product of `ι_W` on one summand
is the lax comparison. -/
theorem naiveCup_summand_box (n : ℤ) (hpq : n₁ + n₂ = n) :
    boxTotalIota
        ((pushforwardComplex (toInverseImageBase (pullback.fst a b ≫ a))).obj
          (((RingedSpaceModuleAdjunction.modulePullback
            (pullback.fst a b).toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (underlyingComplex K)))
        ((pushforwardComplex (toInverseImageBase (pullback.fst a b ≫ a))).obj
          (((RingedSpaceModuleAdjunction.modulePullback
            (pullback.snd a b).toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (underlyingComplex L))) n₁ n₂ n hpq ≫ (chainNaive a b K L).f n =
      inverseImageTensorLax (pullback.fst a b ≫ a)
        ((fstPullbackComplex a b (underlyingComplex K)).X n₁)
        ((sndPullbackComplex a b (underlyingComplex L)).X n₂) ≫
      (StacksDraft.KFlat.modulePushforward (toInverseImageBase (pullback.fst a b ≫ a))).map
        (HomologicalComplex.ιMapBifunctor (fstPullbackComplex a b (underlyingComplex K))
          (sndPullbackComplex a b (underlyingComplex L))
          (Stacks.SheafOfModules.Tensor.sheafTensor (pullback a b).toRingedSpace.sheaf)
          (ComplexShape.up ℤ) n₁ n₂ n hpq) :=
  ιMapBifunctor_naiveCupProduct_f_toInverseImageBase (pullback.fst a b ≫ a)
    (fstPullbackComplex a b (underlyingComplex K)) (sndPullbackComplex a b (underlyingComplex L))
    n₁ n₂ n hpq

/-- The degreewise underived base change map along a factorization `p ≫ c = g` is the comparison of
[Stacks, Tag 07XW] (A1). -/
theorem underivedBaseChangeComplexMap_ofFactors_f {W X' S' : Scheme.{u}} (p : W ⟶ X')
    (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g)
    (M : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'.toRingedSpace) ℤ) (n : ℤ) :
    (underivedBaseChangeComplexMap p.toLRSHom.toShHom (toInverseImageBase g) (toInverseImageBase c)
      (FiniteOrderDifferentialOperatorCategory.relativeInverseImageProjectionOfFactors p c g hg)
      (toInverseImageBase_comp_relativeInverseImageProjectionOfFactors p c g hg).symm M).f n =
    FiniteOrderDifferentialOperatorCategory.relativeInverseImageToPullbackOfFactors p c g hg
      (M.X n) :=
  moduleBaseChangeSquare_app_relativeOfFactors p c g hg (M.X n)

/-- The degreewise underived base change map of the first projection. -/
theorem fstUnderivedBaseChange_f (n : ℤ) :
    (fstUnderivedBaseChange a b (underlyingComplex K)).f n =
      relativeInverseImageToPullback (pullback.fst a b) a ((underlyingComplex K).X n) :=
  moduleBaseChangeSquare_app_relative (pullback.fst a b) a ((underlyingComplex K).X n)

/-- The second-projection half of the summand computation, for a generic factorization. -/
theorem pullbackβ_comp_ofFactors {W Y' S' : Scheme.{u}} (q : W ⟶ Y') (c : Y' ⟶ S') (g : W ⟶ S')
    (hg : q ≫ c = g) (q₂ : inverseImageBase g ⟶ inverseImageBase c)
    (sq : q.toLRSHom.toShHom ≫ toInverseImageBase c = toInverseImageBase g ≫ q₂)
    (L : CochainComplex (FiniteOrderDifferentialOperatorCategory c) ℤ) (hL0 : ∀ p q, L.d p q = 0)
    (n : ℤ)
    (r : (_root_.pullback q₂).obj ((pushforward (toInverseImageBase c)).obj (L.X n).module) ⟶
      (pushforward (toInverseImageBase g)).obj ((_root_.pullback q.toLRSHom.toShHom).obj
        (L.X n).module))
    (h : (⟨q₂, r⟩ : Σ q' : inverseImageBase g ⟶ inverseImageBase c,
        (_root_.pullback q').obj ((pushforward (toInverseImageBase c)).obj (L.X n).module) ⟶
          (pushforward (toInverseImageBase g)).obj
            ((_root_.pullback q.toLRSHom.toShHom).obj (L.X n).module)) =
      ⟨FiniteOrderDifferentialOperatorCategory.relativeInverseImageProjectionOfFactors q c g hg,
        FiniteOrderDifferentialOperatorCategory.relativeInverseImageToPullbackOfFactors q c g hg
          (L.X n).module⟩) :
    (((RingedSpaceModuleAdjunction.modulePullback q₂).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (underlyingComplexHom L hL0)).f n ≫ r =
    (underivedBaseChangeComplexMap q.toLRSHom.toShHom (toInverseImageBase g) (toInverseImageBase c)
      q₂ sq (underlyingComplex L)).f n := by
  cases h
  refine ((congrArg (· ≫ _)
    ((RingedSpaceModuleAdjunction.modulePullback _).map_id _)).trans (Category.id_comp _)).trans ?_
  exact (underivedBaseChangeComplexMap_ofFactors_f q c g hg (underlyingComplex L) n).symm

/-- The second-projection half of the summand computation. -/
theorem pullbackβ_comp_snd (n : ℤ) :
    (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (underlyingComplexHom L hL0)).f n ≫
      FiniteOrderDifferentialOperatorCategory.sndRelativeInverseImageToPullback a b (L.X n).module =
    (sndUnderivedBaseChange a b (underlyingComplex L)).f n :=
  pullbackβ_comp_ofFactors (pullback.snd a b) b (pullback.fst a b ≫ a) pullback.condition.symm
    (sndProjection a b) (toInverseImageBase_comp_sndProjection a b) L hL0 n
    (FiniteOrderDifferentialOperatorCategory.sndRelativeInverseImageToPullback a b (L.X n).module)
    rfl

/-- The first-projection half of the summand computation. -/
theorem pullbackα_comp_fst (n : ℤ) :
    (((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (underlyingComplexHom K hK0)).f n ≫
      relativeInverseImageToPullback (pullback.fst a b) a (K.X n).module =
    (fstUnderivedBaseChange a b (underlyingComplex K)).f n :=
  ((congrArg (· ≫ _)
    ((RingedSpaceModuleAdjunction.modulePullback _).map_id _)).trans (Category.id_comp _)).trans
    (fstUnderivedBaseChange_f a b K n).symm

omit [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] in
/-- `ι_boxTotalMap` at the pullbacks of the two comparisons `ι_*𝓔₀ ⟶ 𝓕^•`, reassociated. -/
theorem chain_ιLeft (n : ℤ) (hpq : n₁ + n₂ = n) :
    type_of% ((ι_boxTotalMap
      (((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (underlyingComplexHom K hK0))
      (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (underlyingComplexHom L hL0)) n₁ n₂ n hpq).trans
      (Category.assoc _ _ _).symm) :=
  (ι_boxTotalMap
      (((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (underlyingComplexHom K hK0))
      (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (underlyingComplexHom L hL0)) n₁ n₂ n hpq).trans
      (Category.assoc _ _ _).symm

omit [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] in
/-- `ι_boxTotalMap` at the two underived base change maps, reassociated. -/
theorem chain_ιRight (n : ℤ) (hpq : n₁ + n₂ = n) :
    type_of% ((ι_boxTotalMap (fstUnderivedBaseChange a b (underlyingComplex K))
      (sndUnderivedBaseChange a b (underlyingComplex L)) n₁ n₂ n hpq).trans
      (Category.assoc _ _ _).symm) :=
  (ι_boxTotalMap (fstUnderivedBaseChange a b (underlyingComplex K))
      (sndUnderivedBaseChange a b (underlyingComplex L)) n₁ n₂ n hpq).trans
      (Category.assoc _ _ _).symm

omit [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] in
/-- The first leg of the comparison on the summand, against the two underived base change maps. -/
theorem chain_leg (n : ℤ) (hpq : n₁ + n₂ = n) :
    rhsFst (chain_ιLeft a b K L n₁ n₂ hK0 hL0 n hpq) ≫
      FiniteOrderDifferentialOperatorCategory.relativeBoxComparisonLeg₁ a b (K.X n₁) (L.X n₂) =
    rhsFst (chain_ιRight a b K L n₁ n₂ n hpq) :=
  bifunctor_map_comp_map (Stacks.SheafOfModules.Tensor.sheafTensor (SheafedSpace.sheaf
      (inverseImageBase (pullback.fst a b ≫ a))))
      (B := (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((pushforwardComplex (toInverseImageBase b)).obj
              (underlyingComplex L))).X n₂)
      (B' := (_root_.pullback
        (FiniteOrderDifferentialOperatorCategory.sndRelativeInverseImageProjection a b)).obj
          ((pushforward (toInverseImageBase b)).obj (L.X n₂).module))
      (pullbackα_comp_fst a b K hK0 n₁) (pullbackβ_comp_snd a b L hL0 n₂)

/-- The two legs of the comparison on the summand. -/
theorem chain_legs (n : ℤ) (hpq : n₁ + n₂ = n) :
    rhsFst (chain_ιLeft a b K L n₁ n₂ hK0 hL0 n hpq) ≫ rhsFst (iota_hom_box a b K L n₁ n₂ n hpq) ≫
      rhsFst (boxTotalι_comp_boxTotalToFstSnd a b K L n₁ n₂ hKz hLz n hpq) =
    rhsFst (chain_ιRight a b K L n₁ n₂ n hpq) ≫ rhsFst (naiveCup_summand_box a b K L n₁ n₂ n hpq) :=
  comp_legs_eq
    (FiniteOrderDifferentialOperatorCategory.relativeBoxComparison_eq a b (K.X n₁) (L.X n₂))
    (chain_leg a b K L n₁ n₂ hK0 hL0 n hpq) (Category.comp_id _)

/-- **The chain identity on the summand `(n₁, n₂)`.** -/
theorem chain_summand (n : ℤ) (hpq : n₁ + n₂ = n) :
    boxTotalIota
        (((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((pushforwardComplex (toInverseImageBase a)).obj
            (underlyingComplex K)))
        (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((pushforwardComplex (toInverseImageBase b)).obj
            (underlyingComplex L))) n₁ n₂ n hpq ≫
      (boxTotalMap
        (((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (underlyingComplexHom K hK0))
        (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (underlyingComplexHom L hL0))).f n ≫
      (boxTotalComparison a b K L n₁ n₂).hom.f n ≫
        (boxTotalToFstSnd a b K L n₁ n₂ hKz hLz).f n =
    boxTotalIota
        (((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((pushforwardComplex (toInverseImageBase a)).obj
            (underlyingComplex K)))
        (((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((pushforwardComplex (toInverseImageBase b)).obj
            (underlyingComplex L))) n₁ n₂ n hpq ≫
      (boxTotalMap (fstUnderivedBaseChange a b (underlyingComplex K))
        (sndUnderivedBaseChange a b (underlyingComplex L))).f n ≫ (chainNaive a b K L).f n :=
  summand_chase (chain_legs a b K L n₁ n₂ hK0 hL0 hKz hLz n hpq) (chain_ιRight a b K L n₁ n₂ n hpq)
    (chain_ιLeft a b K L n₁ n₂ hK0 hL0 n hpq) (iota_hom_box a b K L n₁ n₂ n hpq)
    (boxTotalι_comp_boxTotalToFstSnd a b K L n₁ n₂ hKz hLz n hpq)
    (naiveCup_summand_box a b K L n₁ n₂ n hpq)

include hKz hLz in
omit [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] in
/-- Off the pair of degrees, the summands of the source of the chain identity vanish. -/
theorem isZero_chainLeft_summand (p q : ℤ) (h : ¬ (p = n₁ ∧ q = n₂)) :
    IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor (SheafedSpace.sheaf
      (inverseImageBase (pullback.fst a b ≫ a)))).obj
        ((((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((pushforwardComplex (toInverseImageBase a)).obj
            (underlyingComplex K))).X p)).obj
        ((((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((pushforwardComplex (toInverseImageBase b)).obj
            (underlyingComplex L))).X q)) := by
  by_cases hp : p = n₁
  · have hq : q ≠ n₂ := fun hq => h ⟨hp, hq⟩
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor (SheafedSpace.sheaf
      (inverseImageBase (pullback.fst a b ≫ a)))).obj _).map_isZero
      ((RingedSpaceModuleAdjunction.modulePullback (sndProjection a b)).map_isZero
        ((StacksDraft.KFlat.modulePushforward (toInverseImageBase b)).map_isZero
          (isZero_underlyingModule_right b L n₂ hLz q hq)))
  · exact (((Stacks.SheafOfModules.Tensor.sheafTensor (SheafedSpace.sheaf
      (inverseImageBase (pullback.fst a b ≫ a)))).map_isZero
      ((RingedSpaceModuleAdjunction.modulePullback (fstProjection a b)).map_isZero
        ((StacksDraft.KFlat.modulePushforward (toInverseImageBase a)).map_isZero
          (isZero_underlyingModule_left a K n₁ hKz p hp)))).obj _)

/-- **The chain identity**: the total tensor complex of the two comparisons followed by step (5)
and `boxTotalToFstSnd` is the total tensor complex of the two underived base change maps followed
by the naive cup product. -/
theorem chain_identity :
    chainLeft a b K L hK0 hL0 ≫ (boxTotalComparison a b K L n₁ n₂).hom ≫
      boxTotalToFstSnd a b K L n₁ n₂ hKz hLz = chainRight a b K L ≫ chainNaive a b K L := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply (config := { synthAssignedInstances := false }) HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases h : p = n₁ ∧ q = n₂
  · obtain ⟨rfl, rfl⟩ := h
    exact chain_summand a b K L _ _ hK0 hL0 hKz hLz n hpq
  · exact (isZero_chainLeft_summand a b K L n₁ n₂ hKz hLz p q h).eq_of_src _ _

/-- The hypothesis `h4` of `relativeBoxKunneth_chase` for `ν` the class of `boxTotalToFstSnd`. -/
theorem chain_derived :
    rhsSnd (chase_toTensorNaturality_box a b K L (underlyingComplex K) (underlyingComplex L)
        (underlyingComplexHom K hK0) (underlyingComplexHom L hL0)) ≫
      rhsLast₄ (boxTotalDerivedComparison_eq a b K L n₁ n₂ (boxTotalComparison a b K L n₁ n₂)) ≫
        DerivedCategory.Q.map (boxTotalToFstSnd a b K L n₁ n₂ hKz hLz) =
    rhsSnd (chase_toTensorNaturality_baseChange a b (underlyingComplex K) (underlyingComplex L)) ≫
      rhsMid (chase_naiveCupProduct a b (underlyingComplex K) (underlyingComplex L)) :=
  map_comp_comp_eq_map_comp DerivedCategory.Q (chain_identity a b K L n₁ n₂ hK0 hL0 hKz hLz)

/-- The naturality of the Künneth map at the two comparisons `ι_*𝓔₀ ⟶ 𝓕^•`. -/
theorem concentrated_naturality_underlying :
    type_of% (naturality_both
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a)))
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_left (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (DerivedCategory.Q.map (underlyingComplexHom K hK0))
      (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase b)).obj
        (underlyingComplex L))))
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_right (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (DerivedCategory.Q.obj (leftComplex a K))
      (DerivedCategory.Q.map (underlyingComplexHom L hL0)))) :=
  (naturality_both
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a)))
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_left (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (DerivedCategory.Q.map (underlyingComplexHom K hK0))
      (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase b)).obj
        (underlyingComplex L))))
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_right (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (DerivedCategory.Q.obj (leftComplex a K))
      (DerivedCategory.Q.map (underlyingComplexHom L hL0))))

/-- The naturality of the Künneth map at the two comparisons `Q(ι_*𝓔₀) ⟶ Rι_*(Q𝓔₀)`. -/
theorem concentrated_naturality_comparison :
    type_of% (naturality_both
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a)))
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_left (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (pushforwardComparisonQ (toInverseImageBase a) (underlyingComplex K))
      (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase b)).obj
        (underlyingComplex L))))
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_right (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) ((derivedPushforward (toInverseImageBase a)).obj
        (DerivedCategory.Q.obj (underlyingComplex K)))
      (pushforwardComparisonQ (toInverseImageBase b) (underlyingComplex L)))) :=
  (naturality_both
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a)))
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_left (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (pushforwardComparisonQ (toInverseImageBase a) (underlyingComplex K))
      (DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase b)).obj
        (underlyingComplex L))))
    (Stacks.Cohomology.DerivedKunneth.kunnethMap_natural_right (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) ((derivedPushforward (toInverseImageBase a)).obj
        (DerivedCategory.Q.obj (underlyingComplex K)))
      (pushforwardComparisonQ (toInverseImageBase b) (underlyingComplex L))))

/-- `relativeBoxKunneth_chase` for complexes concentrated in one degree, with `ν` the class of
`boxTotalToFstSnd`. -/
theorem concentrated_chase : type_of% (relativeBoxKunneth_chase a b K L n₁ n₂ (underlyingComplex K)
    (underlyingComplex L) (underlyingComplexHom K hK0) (underlyingComplexHom L hL0)
    (DerivedCategory.Q.map (boxTotalToFstSnd a b K L n₁ n₂ hKz hLz))
    (chain_derived a b K L n₁ n₂ hK0 hL0 hKz hLz)) :=
  relativeBoxKunneth_chase a b K L n₁ n₂ (underlyingComplex K)
    (underlyingComplex L) (underlyingComplexHom K hK0) (underlyingComplexHom L hL0)
    (DerivedCategory.Q.map (boxTotalToFstSnd a b K L n₁ n₂ hKz hLz))
    (chain_derived a b K L n₁ n₂ hK0 hL0 hKz hLz)

/-- The comparison `ι_*𝓔₀ ⟶ 𝓕^•` of a complex with zero differential is an isomorphism. -/
theorem isIso_underlyingComplexHom {Z T : Scheme.{u}} {c : Z ⟶ T}
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory c) ℤ) (hK : ∀ n m, K.d n m = 0) :
    IsIso (underlyingComplexHom K hK) :=
  have : ∀ n, IsIso ((underlyingComplexHom K hK).f n) := fun n =>
    (inferInstance : IsIso (𝟙 ((FiniteOrderDifferentialOperatorCategory.toInverseImageModules
      c).obj (K.X n))))
  HomologicalComplex.Hom.isIso_of_components _

/-- The horizontal map of `concentrated_naturality_underlying` is invertible. -/
theorem isIso_concentrated_naturality_underlying :
    IsIso (eqLhsHead (concentrated_naturality_underlying a b K L hK0 hL0)) := by
  have := isIso_underlyingComplexHom K hK0
  have := isIso_underlyingComplexHom L hL0
  exact IsIso.comp_isIso' ((Functor.mapIso _ (Functor.mapIso _
    (DerivedCategory.Q.mapIso (asIso (underlyingComplexHom K hK0))))).app _).isIso_hom
    (Functor.mapIso _ (Functor.mapIso _
      (DerivedCategory.Q.mapIso (asIso (underlyingComplexHom L hL0))))).isIso_hom

/-- The horizontal map of `concentrated_naturality_comparison` is invertible. -/
theorem isIso_concentrated_naturality_comparison :
    IsIso (eqLhsHead (concentrated_naturality_comparison a b K L)) := by
  have := isIso_pushforwardComparisonQ_toInverseImageBase a (underlyingComplex K)
  have := isIso_pushforwardComparisonQ_toInverseImageBase b (underlyingComplex L)
  exact IsIso.comp_isIso' ((Functor.mapIso _ (Functor.mapIso _
    (asIso (pushforwardComparisonQ (toInverseImageBase a) (underlyingComplex K))))).app _).isIso_hom
    (Functor.mapIso _ (Functor.mapIso _
      (asIso (pushforwardComparisonQ (toInverseImageBase b) (underlyingComplex L))))).isIso_hom

/-- The class of `boxTotalToFstSnd` followed by the comparison `Q(ι_*A) ⟶ Rι_*(QA)` is invertible.
-/
theorem isIso_concentrated_totalComparison :
    IsIso (eqLhsLast (concentrated_chase a b K L n₁ n₂ hK0 hL0 hKz hLz)) := by
  have := isIso_pushforwardComparisonQ_toInverseImageBase (pullback.fst a b ≫ a)
    (fstSndTotal a b (underlyingComplex K) (underlyingComplex L))
  exact IsIso.comp_isIso'
    (@Functor.map_isIso _ _ _ _ _ _ DerivedCategory.Q _
      (isIso_boxTotalToFstSnd a b K L n₁ n₂ hKz hLz))
    (asIso (pushforwardComparisonQ (toInverseImageBase (pullback.fst a b ≫ a))
      (fstSndTotal a b (underlyingComplex K) (underlyingComplex L)))).isIso_hom

include hKz hLz in
/-- For flat terms, `Rι_{W*}` of the pullback comparisons followed by the derived-to-ordinary
tensor comparison is invertible. -/
theorem isIso_concentrated_pullbackTensor
    (hK : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (underlyingModule (K.X n₁)))
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (underlyingModule (L.X n₂))) :
    IsIso (eqRhsLast (concentrated_chase a b K L n₁ n₂ hK0 hL0 hKz hLz)) := by
  have kK := kFlat_underlyingComplex K n₁ hKz hK
  have kL := kFlat_underlyingComplex L n₂ hLz hL
  have p1 := isIso_pullbackComplexComparison_of_kFlat (pullback.fst a b).toLRSHom.toShHom _ kK
  have p2 := isIso_pullbackComplexComparison_of_kFlat (pullback.snd a b).toLRSHom.toShHom _ kL
  have t := isIso_toTensor_of_kFlat (fstPullbackComplex a b (underlyingComplex K))
    (sndPullbackComplex a b (underlyingComplex L))
    (Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional _ _ kK)
  exact @Functor.map_isIso _ _ _ _ _ _
    (derivedPushforward (toInverseImageBase (pullback.fst a b ≫ a))) _
    (IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ (Functor.uncurry.obj _) _
      ((isIso_prod_iff _ _).mpr ⟨p1, p2⟩)) t)

/-- The underlying graded module of a complex of finite-order differential operators has
quasi-coherent cohomology sheaves. -/
theorem isQCohAll_underlyingComplex {Z T : Scheme.{u}} {c : Z ⟶ T}
    (K : CochainComplex (FiniteOrderDifferentialOperatorCategory c) ℤ) :
    AlgebraicGeometry.IsQCohAll (W := Z) (DerivedCategory.Q.obj (underlyingComplex K)) := fun j =>
  (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctorFactors Z.Modules j).app (underlyingComplex K) ≪≫
      ((underlyingComplex K).isoHomologyπ (j - 1) j (by simp) rfl).symm ≪≫
        (underlyingComplex K).iCyclesIso j (j + 1) (by simp) rfl).symm (K.X j).isQuasicoherent

/-- The derived base change map is the component of the derived base change square. -/
theorem derivedBaseChangeMap_eq_app {X' X'' S' S'' : RingedSpace.{u, u}} (g' : X' ⟶ X'')
    (f' : X' ⟶ S') (f : X'' ⟶ S'') (g : S' ⟶ S'') (sq : g' ≫ f = f' ≫ g)
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''))) :
    Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq A =
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare g' f' f g sq).app A :=
  rfl

/-- The derived base change map of the first projection, as a component of the square, spelled as
in `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_ringChange`. -/
theorem concentrated_baseChange_fst :
    type_of% (derivedBaseChangeMap_eq_app (X' := (pullback a b).toRingedSpace)
    (X'' := X.toRingedSpace)
    (S' := inverseImageBase (pullback.fst a b ≫ a)) (S'' := inverseImageBase a)
    (pullback.fst a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase a) (fstProjection a b)
    (toInverseImageBase_comp_fstProjection a b)
      (DerivedCategory.Q.obj (underlyingComplex K) : DerivedCategory X.Modules)) :=
  derivedBaseChangeMap_eq_app (X' := (pullback a b).toRingedSpace) (X'' := X.toRingedSpace)
    (S' := inverseImageBase (pullback.fst a b ≫ a)) (S'' := inverseImageBase a)
    (pullback.fst a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase a) (fstProjection a b)
    (toInverseImageBase_comp_fstProjection a b)
      (DerivedCategory.Q.obj (underlyingComplex K) : DerivedCategory X.Modules)

/-- The derived base change map of the second projection, as a component of the square, spelled as
in `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_ringChange`. -/
theorem concentrated_baseChange_snd :
    type_of% (derivedBaseChangeMap_eq_app (X' := (pullback a b).toRingedSpace)
    (X'' := Y.toRingedSpace)
    (S' := inverseImageBase (pullback.fst a b ≫ a)) (S'' := inverseImageBase b)
    (pullback.snd a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase b) (sndProjection a b)
    (toInverseImageBase_comp_sndProjection a b)
      (DerivedCategory.Q.obj (underlyingComplex L) : DerivedCategory Y.Modules)) :=
  derivedBaseChangeMap_eq_app (X' := (pullback a b).toRingedSpace) (X'' := Y.toRingedSpace)
    (S' := inverseImageBase (pullback.fst a b ≫ a)) (S'' := inverseImageBase b)
    (pullback.snd a b).toLRSHom.toShHom
    (toInverseImageBase (pullback.fst a b ≫ a)) (toInverseImageBase b) (sndProjection a b)
    (toInverseImageBase_comp_sndProjection a b)
      (DerivedCategory.Q.obj (underlyingComplex L) : DerivedCategory Y.Modules)

/-- [Stacks, Tag 0FLQ] read on the inverse-image ringed spaces at `Rι_{X*}(Q𝓔₀)` and
`Rι_{Y*}(Q𝓜₀)`, elaborated with the instances of this file. -/
theorem isIso_concentrated_kunnethMap
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : AlgebraicGeometry.TorIndependent a b) :
    type_of% (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_ringChange
      (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (toInverseImageBase a) (toInverseImageBase b)
      (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom (toInverseImageBase_comp_fstProjection a b)
      (toInverseImageBase_comp_sndProjection a b) a.toLRSHom.toShHom (toInverseImageBase_comp a)
      b.toLRSHom.toShHom (toInverseImageBase_comp b) (pullback.fst a b ≫ a).toLRSHom.toShHom
      (toInverseImageBase_comp (pullback.fst a b ≫ a)) rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b)
      (DerivedCategory.Q.obj (underlyingComplex K) : DerivedCategory X.Modules)
      (DerivedCategory.Q.obj (underlyingComplex L) : DerivedCategory Y.Modules)
      (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme a b hTor
        (DerivedCategory.Q.obj (underlyingComplex K)) (DerivedCategory.Q.obj (underlyingComplex L))
        (isQCohAll_underlyingComplex K) (isQCohAll_underlyingComplex L))) :=
  (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMap_ringChange
      (inverseImageBaseProjection a)
      (inverseImageBaseProjection b) (fstProjection a b) (sndProjection a b)
      (inverseImageBaseProjection (pullback.fst a b ≫ a)) (fstProjection_comp a b)
      (sndProjection_comp a b) (toInverseImageBase a) (toInverseImageBase b)
      (toInverseImageBase (pullback.fst a b ≫ a)) (pullback.fst a b).toLRSHom.toShHom
      (pullback.snd a b).toLRSHom.toShHom (toInverseImageBase_comp_fstProjection a b)
      (toInverseImageBase_comp_sndProjection a b) a.toLRSHom.toShHom (toInverseImageBase_comp a)
      b.toLRSHom.toShHom (toInverseImageBase_comp b) (pullback.fst a b ≫ a).toLRSHom.toShHom
      (toInverseImageBase_comp (pullback.fst a b ≫ a)) rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b)
      (DerivedCategory.Q.obj (underlyingComplex K) : DerivedCategory X.Modules)
      (DerivedCategory.Q.obj (underlyingComplex L) : DerivedCategory Y.Modules)
      (Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme a b hTor
        (DerivedCategory.Q.obj (underlyingComplex K)) (DerivedCategory.Q.obj (underlyingComplex L))
        (isQCohAll_underlyingComplex K) (isQCohAll_underlyingComplex L)))

include hK0 hL0 in
/-- The base change maps and the relative cup product of `ι_W`, as they appear in the chase,
against their spelling in `isIso_concentrated_kunnethMap`. -/
theorem concentrated_baseChange_cup
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : AlgebraicGeometry.TorIndependent a b) :
    eqRhsMid (concentrated_chase a b K L n₁ n₂ hK0 hL0 hKz hLz) =
      isIsoCompMapArg (isIso_concentrated_kunnethMap a b K L hTor) :=
  uncurry_map_comp_congr _ _ (concentrated_baseChange_fst a b K) (concentrated_baseChange_snd a b L)

include hK0 hL0 hKz hLz in
/-- **The relative Künneth map is invertible at two complexes with zero differential concentrated
in one degree with flat terms.** -/
theorem isIso_relativeBoxKunnethMap_of_concentrated
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : AlgebraicGeometry.TorIndependent a b)
    (hK : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf)
      (underlyingModule (K.X n₁)))
    (hL : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
      (underlyingModule (L.X n₂))) :
    IsIso (relativeBoxKunnethMap a b K L n₁ n₂) :=
  isIso_of_kunneth_chase_of_eq
    (derivedPushforward (inverseImageBaseProjection (pullback.fst a b ≫ a)))
    (concentrated_naturality_comparison a b K L)
    (concentrated_naturality_underlying a b K L hK0 hL0)
    (concentrated_chase a b K L n₁ n₂ hK0 hL0 hKz hLz)
    (isIso_concentrated_naturality_comparison a b K L)
    (isIso_concentrated_naturality_underlying a b K L hK0 hL0)
    (isIso_concentrated_totalComparison a b K L n₁ n₂ hK0 hL0 hKz hLz)
    (isIso_concentrated_pullbackTensor a b K L n₁ n₂ hK0 hL0 hKz hLz hK hL)
    (concentrated_baseChange_cup a b K L n₁ n₂ hK0 hL0 hKz hLz hTor)
    (isIso_concentrated_kunnethMap a b K L hTor)

end Assembly

/-- **The base case of [Stacks, Tag 0FMC].** Let `a : X ⟶ S` and `b : Y ⟶ S` be quasi-compact and
quasi-separated with `X` and `Y` Tor independent over `S`, and let `𝓔` and `𝓔'` be objects of the
categories of finite-order differential operators on `X` and `Y` with flat underlying modules.
Then the relative Künneth map of [Stacks, Tag 0G4B] at `𝓔[-i]` and `𝓔'[-j]` is an isomorphism. -/
theorem isIso_relativeBoxKunnethMap_single {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (hTor : AlgebraicGeometry.TorIndependent a b)
    (E : FiniteOrderDifferentialOperatorCategory a) (E' : FiniteOrderDifferentialOperatorCategory b)
    (i j : ℤ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) E.module)
    (hE' : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) E'.module) :
    IsIso (relativeBoxKunnethMap a b ((HomologicalComplex.single _ (ComplexShape.up ℤ) i).obj E)
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) j).obj E') i j) :=
  isIso_relativeBoxKunnethMap_of_concentrated a b _ _ i j (fun _ _ => rfl) (fun _ _ => rfl)
    (fun p hp => HomologicalComplex.isZero_single_obj_X (c := ComplexShape.up ℤ) (j := i) (A := E)
      (i := p) (hi := hp))
    (fun q hq => HomologicalComplex.isZero_single_obj_X (c := ComplexShape.up ℤ) (j := j) (A := E')
      (i := q) (hi := hq)) hTor
    ((HomologicalComplex.single_obj_X_self (c := ComplexShape.up ℤ) (j := i) (A := E)).symm ▸ hE)
    ((HomologicalComplex.single_obj_X_self (c := ComplexShape.up ℤ) (j := j) (A := E')).symm ▸ hE')


end Stacks.Cohomology.BoxKunneth

end
