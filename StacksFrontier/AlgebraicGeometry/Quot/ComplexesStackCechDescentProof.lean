module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentInterface
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackHomDescent
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Stacks 0DLA, Čech case, from 0DLA on the small étale sites

This file proves `AlgebraicGeometry.Space.cechDescentOfSmallEtaleHypercoverDescent` (the
proposition `AlgebraicGeometry.Space.CechDescentOfSmallEtaleHypercoverDescent`): Stacks 0DLA on the
small étale sites, for fppf hypercoverings of algebraic spaces, gives its Čech case
`AlgebraicGeometry.Space.ComplexesSituation.CechDescent`.

Let `C : CechCover T I` be a Čech covering in `Complexes_{X/Y}` and `R` a refinement of it indexed
by a type in `Type u`, with disjoint union `V` and fppf covering `q : V ⟶ T`. Stacks 0DLA is
applied to the base change `X ×_Y Č(V/T) ⟶ X_T` of the Čech nerve of `q`
(`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.nerve`):

* the input `K₀` is the pullback to `V` (through `V ×_T V ×_T ⋯` in degree zero) of the complex
  `K_0` glued from the restrictions of the `K_{σ k}`; the gluing isomorphism `α` on `V ×_T V` is
  the descent datum of `K_0`
  (`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.IsUnionTransport`), and
  its cocycle condition is that of the Čech covering, through the triple overlaps;
* the output `K` with `β : a₀^*K ≅ K₀` is an object of `Complexes_{X/Y}` over `T` (relative
  perfectness and the condition on the fibres descend); the isomorphisms `ψ i : a_i^*K ≅ K_i`
  descend along `T_i ×_T V ⟶ T_i` (morphisms of `Complexes_{X/Y}` descend, Stacks 0DLG), and
  their compatibility on the double overlaps is checked after the same base change.

## Implementation notes

The statements of Stacks 0DLA (`CategoryTheory.IsHypercoverDescentCocycle`,
`CategoryTheory.IsHypercoverDescentCompatible`) are generic in the pullback assignment. When the
kernel unfolds them, or any lemma generic in `pull` and in the family of categories, at the
derived pullbacks, it leaves beta-redexes inside the composition comparisons, and comparing those
with the native spelling makes it unfold the comparisons down to their `eqToHom`s. So the generic
lemmas here are stated with `@pull`, applied to the eta-reduced `@PullbackData.pull _ _ _ _ P`
(which is the native spelling), and the unfolded statements are moved to the native spelling by
congruence (`heq_congr`), never by `rw`.

## References

* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
* [Stacks Project, Tag 0DLH](https://stacks.math.columbia.edu/tag/0DLH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ComplexesSituation

variable {D : ComplexesSituation B S hS}


/-! ### The 0DLA cocycle condition from morphisms of `Complexes_{X/Y}` -/

section GenericCocycle

universe v₁ u₁ v₂ u₂ in
/-- The cocycle condition of Stacks 0DLA holds as soon as it holds for one choice of the vertices
of `U₂` with their presentations. -/
theorem isHypercoverDescentCocycle_of_one {A : Type u₁} [Category.{v₁} A] {D' : A → Type u₂}
    [∀ a, Category.{v₂} (D' a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D' b ⥤ D' a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {U₀ U₁ U₂ : A} (s t : U₁ ⟶ U₀) (e₀₁ e₁₂ e₀₂ : U₂ ⟶ U₁) {K₀ : D' U₀}
    (α : (pull s).obj K₀ ≅ (pull t).obj K₀) (v₀ v₁ v₂ : U₂ ⟶ U₀) (h₀ : e₀₁ ≫ s = v₀)
    (h₁ : e₀₁ ≫ t = v₁) (h₁' : e₁₂ ≫ s = v₁) (h₂ : e₁₂ ≫ t = v₂) (h₀' : e₀₂ ≫ s = v₀)
    (h₂' : e₀₂ ≫ t = v₂)
    (H : hypercoverEdgeRestrict pull comp α.hom e₀₁ h₀ h₁ ≫
        hypercoverEdgeRestrict pull comp α.hom e₁₂ h₁' h₂ =
      hypercoverEdgeRestrict pull comp α.hom e₀₂ h₀' h₂') :
    IsHypercoverDescentCocycle pull comp s t e₀₁ e₁₂ e₀₂ α := by
  intro w₀ w₁ w₂ g₀ g₁ g₁' g₂ g₀' g₂'
  obtain rfl : w₀ = v₀ := g₀.symm.trans h₀
  obtain rfl : w₁ = v₁ := g₁.symm.trans h₁
  obtain rfl : w₂ = v₂ := g₂.symm.trans h₂
  exact H

universe v₁ u₁ v₂ u₂ in
/-- The comparison `hypercoverPullTriangle` at two presentations of a morphism as a composite. -/
theorem hypercoverPullTriangle_hom_app_congr {A : Type u₁} [Category.{v₁} A] {D' : A → Type u₂}
    [∀ a, Category.{v₂} (D' a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D' b ⥤ D' a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k k' : a ⟶ c} (hk : f ≫ g = k) (hk' : f ≫ g = k')
    (M : D' c) :
    (hypercoverPullTriangle pull comp hk).hom.app M =
      eqToHom (congrArg (fun m : a ⟶ c => (pull m).obj M) (hk.symm.trans hk')) ≫
        (hypercoverPullTriangle pull comp hk').hom.app M := by
  subst hk hk'
  rw [eqToHom_refl, Category.id_comp]

universe v₁ u₁ v₂ u₂ in
/-- The inverse of the comparison `hypercoverPullTriangle` at two presentations of a morphism as
a composite. -/
theorem hypercoverPullTriangle_inv_app_congr {A : Type u₁} [Category.{v₁} A] {D' : A → Type u₂}
    [∀ a, Category.{v₂} (D' a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D' b ⥤ D' a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k k' : a ⟶ c} (hk : f ≫ g = k) (hk' : f ≫ g = k')
    (M : D' c) :
    (hypercoverPullTriangle pull comp hk).inv.app M =
      (hypercoverPullTriangle pull comp hk').inv.app M ≫
        eqToHom (congrArg (fun m : a ⟶ c => (pull m).obj M) (hk'.symm.trans hk)) := by
  subst hk hk'
  rw [eqToHom_refl, Category.comp_id]

/-- The morphism of base changes induced by a composite is the composite. -/
theorem relativeMap_comp {Z T₁ T₀ : SchemesOver D.Y} (h : Z ⟶ T₁) (h' : T₁ ⟶ T₀) :
    D.relativeMap h ≫ D.relativeMap h' = D.relativeMap (h ≫ h') :=
  (baseChangeMap_comp D.f h h').symm

/-- The composition comparison of `Complexes_{X/Y}` is the comparison `hypercoverPullTriangle`
of the derived pullbacks. -/
theorem compComparison_eq_hypercoverPullTriangle {Z T₁ T₀ : SchemesOver D.Y} (h : Z ⟶ T₁)
    (h' : T₁ ⟶ T₀) :
    D.compComparison h h' =
      hypercoverPullTriangle (smallEtaleDerivedPullbackData B S hS).pull
        (smallEtaleDerivedPullbackData B S hS).compIso (f := D.relativeMap h)
        (g := D.relativeMap h') (k := D.relativeMap (h ≫ h')) (relativeMap_comp h h') :=
  rfl

universe v₁ u₁ v₂ u₂ in
/-- The cocycle condition of Stacks 0DLA from one presentation of the three vertices of `U₂`, with
the comparisons of the pullbacks along equal composites given as `eqToHom`s: the shape the
restrictions of a gluing map along the three edges take after `restrictComparison_cocycle`. The
arguments `pull` and `comp` occur unexpanded (`@pull`), so that an instance at an eta-reduced
`@PullbackData.pull` has no beta-redex in its statement. -/
theorem isHypercoverDescentCocycle_of_edgeRestrict_eqToHom {A : Type u₁} [Category.{v₁} A]
    {D' : A → Type u₂} [∀ a, Category.{v₂} (D' a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D' b ⥤ D' a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {U₀ U₁ U₂ : A} (s t : U₁ ⟶ U₀) (e₀₁ e₁₂ e₀₂ : U₂ ⟶ U₁) {K₀ : D' U₀}
    (α : (pull s).obj K₀ ≅ (pull t).obj K₀) {k₀₁s k₀₁t k₁₂s k₁₂t k₀₂s k₀₂t : U₂ ⟶ U₀}
    (h₀₁s : e₀₁ ≫ s = k₀₁s) (h₀₁t : e₀₁ ≫ t = k₀₁t) (h₁₂s : e₁₂ ≫ s = k₁₂s)
    (h₁₂t : e₁₂ ≫ t = k₁₂t) (h₀₂s : e₀₂ ≫ s = k₀₂s) (h₀₂t : e₀₂ ≫ t = k₀₂t)
    (q₁ : k₀₁s = k₀₂s) (q₂ : k₀₁t = k₁₂s) (q₃ : k₁₂t = k₀₂t)
    (p₁ : (pull k₀₁s).obj K₀ = (pull k₀₂s).obj K₀) (p₂ : (pull k₀₁t).obj K₀ = (pull k₁₂s).obj K₀)
    (p₃ : (pull k₀₂t).obj K₀ = (pull k₁₂t).obj K₀)
    (H : hypercoverEdgeRestrict @pull @comp α.hom e₀₁ h₀₁s h₀₁t ≫ eqToHom p₂ ≫
        hypercoverEdgeRestrict @pull @comp α.hom e₁₂ h₁₂s h₁₂t =
      eqToHom p₁ ≫ hypercoverEdgeRestrict @pull @comp α.hom e₀₂ h₀₂s h₀₂t ≫ eqToHom p₃) :
    IsHypercoverDescentCocycle @pull @comp s t e₀₁ e₁₂ e₀₂ α := by
  intro v₀ v₁ v₂ g₀ g₁ g₁' g₂ g₀' g₂'
  subst q₁ q₂ q₃
  obtain rfl : k₀₁s = v₀ := h₀₁s.symm.trans g₀
  obtain rfl : k₀₁t = v₁ := h₀₁t.symm.trans g₁
  obtain rfl : k₁₂t = v₂ := h₁₂t.symm.trans g₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at H
  exact H

/-- The converse of `AlgebraicGeometry.Space.comp_fibreComp_eq_fibreComp`: if two fibres
`Functor.fibreComp τ nf ψ₁` and `Functor.fibreComp τ' mf ψ₂` agree through `x`, then `ψ₁` and
`ψ₂` agree through the comparison `nf ≫ inv mf`. -/
theorem comp_inv_eq_of_comp_fibreComp_eq {C₀ C₁ C₂ C₁' : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] [Category* C₁'] {Lp : C₁ ⥤ C₀}
    {La : C₂ ⥤ C₁} {Lpa : C₂ ⥤ C₀} {Lq : C₁' ⥤ C₀} {La' : C₂ ⥤ C₁'} {Lqa : C₂ ⥤ C₀}
    (τ : Lpa ≅ La ⋙ Lp) (τ' : Lqa ≅ La' ⋙ Lq) {M : C₂} {K₁ : C₁} {K₂ : C₁'} {Q : C₀}
    (ψ₁ : La.obj M ⟶ K₁) (ψ₂ : La'.obj M ⟶ K₂) (nf : Lp.obj K₁ ⟶ Q) (mf : Lq.obj K₂ ⟶ Q)
    [hmf : IsIso mf] (x : Lpa.obj M ⟶ Lqa.obj M)
    (h : x ≫ Functor.fibreComp τ' mf ψ₂ = Functor.fibreComp τ nf ψ₁) :
    τ.hom.app M ≫ Lp.map ψ₁ ≫ (nf ≫ inv mf) = x ≫ τ'.hom.app M ≫ Lq.map ψ₂ := by
  simp only [Functor.fibreComp] at h
  rw [← Category.assoc, ← Category.assoc, IsIso.comp_inv_eq]
  simp only [Category.assoc]
  exact h.symm

/-- The comparison `hypercoverPullTriangle` of the derived pullbacks on the small étale sites at
two presentations of a morphism as a composite (the instance at
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` of
`AlgebraicGeometry.Space.ComplexesSituation.hypercoverPullTriangle_hom_app_congr`, stated
directly so that no instance of a generic statement has to be compared with it). -/
theorem smallEtale_hypercoverPullTriangle_hom_app_congr {X Y Z : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : Y ⟶ Z} {k k' : X ⟶ Z} (hk : f ≫ g = k) (hk' : f ≫ g = k')
    (M : derivedModules B S hS Z) :
    (hypercoverPullTriangle (smallEtaleDerivedPullbackData B S hS).pull
        (smallEtaleDerivedPullbackData B S hS).compIso hk).hom.app M =
      eqToHom (congrArg (fun m : X ⟶ Z => ((smallEtaleDerivedPullbackData B S hS).pull m).obj M)
          (hk.symm.trans hk')) ≫
        (hypercoverPullTriangle (smallEtaleDerivedPullbackData B S hS).pull
          (smallEtaleDerivedPullbackData B S hS).compIso hk').hom.app M :=
  hypercoverPullTriangle_hom_app_congr _ _ hk hk' M

/-- The restriction `restrictComparison` of a gluing map along a morphism of test schemes is the
restriction `hypercoverEdgeRestrict` of Stacks 0DLA. Proved by unfolding both sides and comparing
them by congruence (`heq_congr`), so that the kernel only compares their constituents (the two
spellings of the composition comparison agree at the level of isomorphisms). -/
theorem restrictComparison_eq_hypercoverEdgeRestrict {Z₀ Z₁ Z : SchemesOver D.Y}
    {a b : Z₁ ⟶ Z₀} {M : derivedModules B S hS (D.space Z₀)}
    (φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).obj M ⟶
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap b)).obj M) (e : Z ⟶ Z₁) :
    D.restrictComparison φ e =
      hypercoverEdgeRestrict (@PullbackData.pull _ _ _ _ (smallEtaleDerivedPullbackData B S hS))
        (@PullbackData.compIso _ _ _ _ (smallEtaleDerivedPullbackData B S hS)) φ
        (D.relativeMap e) (relativeMap_comp e a) (relativeMap_comp e b) := by
  delta hypercoverEdgeRestrict ComplexesSituation.restrictComparison
  exact eq_of_heq (by heq_congr)

/-- **The cocycle condition of Stacks 0DLA from morphisms of `Complexes_{X/Y}`.** Let
`n, m : A₁ ⟶ A₀` be morphisms of `Complexes_{X/Y}` and `c₁, d, c₃ : Q ⟶ A₁` three morphisms with
`c₁ ≫ n = c₃ ≫ n`, `c₁ ≫ m = d ≫ n` and `d ≫ m = c₃ ≫ m`. Then the comparison
`α = homComparison n m : L n^* A₀ ≅ L m^* A₀` satisfies the cocycle condition for the vertex maps
`n, m` and the edges `c₁, d, c₃`. -/
theorem isHypercoverDescentCocycle_of_complexesHom {Q A₁ A₀ : ComplexesObject D}
    (c₁ d c₃ : ComplexesHom Q A₁) (n m : ComplexesHom A₁ A₀)
    (α : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap n.base)).obj A₀.E ≅
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj A₀.E)
    (hα : homComparison n m = α.hom)
    (e₁ : c₁.comp n = c₃.comp n) (e₂ : c₁.comp m = d.comp n) (e₃ : d.comp m = c₃.comp m) :
    IsHypercoverDescentCocycle
      (@PullbackData.pull _ _ _ _ (smallEtaleDerivedPullbackData B S hS))
      (@PullbackData.compIso _ _ _ _ (smallEtaleDerivedPullbackData B S hS))
      (D.relativeMap n.base) (D.relativeMap m.base)
      (D.relativeMap c₁.base) (D.relativeMap d.base) (D.relativeMap c₃.base) α := by
  have h₁ : c₁.base ≫ n.base = c₃.base ≫ n.base := congrArg ComplexesHom.base e₁
  have h₂ : c₁.base ≫ m.base = d.base ≫ n.base := congrArg ComplexesHom.base e₂
  have h₃ : d.base ≫ m.base = c₃.base ≫ m.base := congrArg ComplexesHom.base e₃
  have H := restrictComparison_cocycle c₁ d c₃ n m n m n m e₁ e₂ e₃ h₁ h₂ h₃
  rewrite [hα, restrictComparison_eq_hypercoverEdgeRestrict,
    restrictComparison_eq_hypercoverEdgeRestrict, restrictComparison_eq_hypercoverEdgeRestrict,
    relativeMapComparison_hom_app, relativeMapComparison_hom_app,
    relativeMapComparison_inv_app'] at H
  refine isHypercoverDescentCocycle_of_edgeRestrict_eqToHom
    (@PullbackData.pull _ _ _ _ (smallEtaleDerivedPullbackData B S hS))
    (@PullbackData.compIso _ _ _ _ (smallEtaleDerivedPullbackData B S hS))
    (D.relativeMap n.base) (D.relativeMap m.base) (D.relativeMap c₁.base)
    (D.relativeMap d.base) (D.relativeMap c₃.base) α (relativeMap_comp c₁.base n.base)
    (relativeMap_comp c₁.base m.base) (relativeMap_comp d.base n.base)
    (relativeMap_comp d.base m.base) (relativeMap_comp c₃.base n.base)
    (relativeMap_comp c₃.base m.base)
    (congrArg D.relativeMap h₁) (congrArg D.relativeMap h₂) (congrArg D.relativeMap h₃)
    (congrArg (fun k => ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj A₀.E)
      h₁)
    (congrArg (fun k => ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj A₀.E)
      h₂)
    (congrArg (fun k => ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj A₀.E)
      h₃.symm) ?_
  exact H

/-- **The compatibility of Stacks 0DLA as an equality in `Complexes_{X/Y}`.** If
`β : L a^* E ≅ A₀.E` is compatible (`IsHypercoverDescentCompatible`) with the comparison
`α = homComparison n m` of two morphisms `n, m : A₁ ⟶ A₀` over `n.base ≫ a = m.base ≫ a`, then
`n ≫ ⟨a, β⟩ = m ≫ ⟨a, β⟩`. The unfolded compatibility is moved to the native spelling of the
derived pullbacks by congruence (`heq_congr`). -/
theorem comp_eq_of_isHypercoverDescentCompatible {A₁ A₀ X : ComplexesObject D}
    (n m : ComplexesHom A₁ A₀) (a : A₀.T ⟶ X.T)
    (β : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).obj X.E ≅ A₀.E)
    (α : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap n.base)).obj A₀.E ≅
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).obj A₀.E)
    (hα : homComparison n m = α.hom) (hb : n.base ≫ a = m.base ≫ a)
    (hc : IsHypercoverDescentCompatible
      (@PullbackData.pull _ _ _ _ (smallEtaleDerivedPullbackData B S hS))
      (@PullbackData.compIso _ _ _ _ (smallEtaleDerivedPullbackData B S hS))
      (D.relativeMap a) (D.relativeMap n.base) (D.relativeMap m.base) α X.E β) :
    n.comp ⟨a, β.hom, Iso.isIso_hom β⟩ = m.comp ⟨a, β.hom, Iso.isIso_hom β⟩ := by
  refine comp_mk_eq_comp_mk n m β.hom β.hom _ _ hb ⟨?_⟩
  have h := hc (D.relativeMap (n.base ≫ a)) (relativeMap_comp n.base a)
    ((relativeMap_comp m.base a).trans (congrArg D.relativeMap hb.symm))
  have hN : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap n.base)).map β.inv ≫
      (hypercoverPullTriangle (smallEtaleDerivedPullbackData B S hS).pull
        (smallEtaleDerivedPullbackData B S hS).compIso (relativeMap_comp n.base a)).inv.app X.E ≫
      (hypercoverPullTriangle (smallEtaleDerivedPullbackData B S hS).pull
        (smallEtaleDerivedPullbackData B S hS).compIso
        ((relativeMap_comp m.base a).trans (congrArg D.relativeMap hb.symm))).hom.app X.E ≫
      ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap m.base)).map β.hom = α.hom :=
    (eq_of_heq (by heq_congr)).trans (h.trans (eq_of_heq (by heq_congr)))
  rw [smallEtale_hypercoverPullTriangle_hom_app_congr _ (relativeMap_comp m.base a),
    ← compComparison_eq_hypercoverPullTriangle, ← compComparison_eq_hypercoverPullTriangle] at hN
  rw [hα, ← hN, relativeMapComparison_hom_app]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]

/-- The converse of `AlgebraicGeometry.Space.ComplexesSituation.comp_mk_eq_comp_mk`: if the
composites `n ≫ ⟨a, ψ⟩` and `m ≫ ⟨a', ψ'⟩` agree, then `ψ` and `ψ'` are compatible with the
comparison `homComparison n m`. -/
theorem fibresCompatible_of_comp_mk_eq {Q A A' X : ComplexesObject D} (n : ComplexesHom Q A)
    (m : ComplexesHom Q A') {a : A.T ⟶ X.T} {a' : A'.T ⟶ X.T}
    (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a)).obj X.E ⟶ A.E)
    (ψ' : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap a')).obj X.E ⟶ A'.E)
    (hψ : IsIso ψ) (hψ' : IsIso ψ') (hb : n.base ≫ a = m.base ≫ a')
    (e : n.comp ⟨a, ψ, hψ⟩ = m.comp ⟨a', ψ', hψ'⟩) : FibresCompatible n m X.E hb ψ ψ' := by
  dsimp only [ComplexesHom.comp] at e
  exact ⟨comp_inv_eq_of_comp_fibreComp_eq (D.compComparison n.base a)
    (D.compComparison m.base a') ψ ψ' n.fibre m.fibre (hmf := m.isIso_fibre) _
    (relativeMapComparison_comp_fibre_of_mk_eq e hb)⟩

end GenericCocycle

namespace CechCover

variable {T : SchemesOver D.Y} {I : Type (u + 1)} {C : CechCover T I}

namespace SmallRefinement

variable (R : C.SmallRefinement)

/-! ### The vertices of the Čech nerve of a refinement -/

section Vertices

-- The schemes of a big fppf site over `S` have finite limits (Stacks 022K).
attribute [local instance] hasFiniteLimits_bigFppfOver_of_siteCategory

/-- The `i`-th vertex `V ×_T ⋯ ×_T V ⟶ V` of the Čech nerve of a refinement, as a morphism of test
schemes over `Y`. -/
abbrev nerveVertex (n : ℕ) (i : Fin (n + 1)) : R.testScheme n ⟶ R.unionTest :=
  CostructuredArrow.homMk (WidePullback.π (fun _ : Fin (n + 1) => R.q) i) (by
    change (schemeSpaceFunctor B S hS).map _ ≫ (schemeSpaceFunctor B S hS).map R.q ≫ T.hom =
      (schemeSpaceFunctor B S hS).map _ ≫ T.hom
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, WidePullback.π_arrow])

/-- The `i`-th vertex of the Čech nerve of a refinement composed with the morphism `V ⟶ T` is the
augmentation of the Čech nerve. -/
theorem vertex_comp_unionHom (n : ℕ) (i : Fin (n + 1)) :
    R.nerveVertex n i ≫ R.unionHom = R.testSchemeHom n :=
  CostructuredArrow.hom_ext _ _ (WidePullback.π_arrow _ _)

/-- The map of the Čech nerve of a refinement induced by `g : ⦋n⦌ ⟶ ⦋m⦌`, followed by the `i`-th
vertex, is the vertex `g i`. -/
theorem testSchemeMap_comp_vertex {n m : ℕ} (g : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    R.testSchemeMap g ≫ R.nerveVertex n i = R.nerveVertex m (g.toOrderHom i) :=
  CostructuredArrow.hom_ext _ _ (WidePullback.lift_π _ _ _ _ _)

/-- The maps of the Čech nerve of a refinement commute with the augmentations to `T`. -/
theorem testSchemeMap_comp_testSchemeHom {n m : ℕ} (g : ⦋n⦌ ⟶ ⦋m⦌) :
    R.testSchemeMap g ≫ R.testSchemeHom n = R.testSchemeHom m :=
  CostructuredArrow.hom_ext _ _ (WidePullback.lift_base _ _ _ _)

/-- Morphisms into a term of the Čech nerve of a refinement agree as soon as their vertices do. -/
theorem testScheme_hom_ext_of_vertex {Z : SchemesOver D.Y} {n : ℕ} {f g : Z ⟶ R.testScheme n}
    (h : ∀ i, f ≫ R.nerveVertex n i = g ≫ R.nerveVertex n i) : f = g := by
  refine CostructuredArrow.hom_ext _ _ (WidePullback.hom_ext _ _ _ (fun i => ?_) ?_)
  · simpa only [CostructuredArrow.comp_left, CostructuredArrow.homMk_left] using
      congrArg CommaMorphism.left (h i)
  · have h0 := congrArg CommaMorphism.left (h 0)
    simp only [CostructuredArrow.comp_left, CostructuredArrow.homMk_left] at h0
    rw [← WidePullback.π_arrow (fun _ : Fin (n + 1) => R.q) 0, ← Category.assoc, h0,
      Category.assoc]

/-- Morphisms into the degree-zero term of the Čech nerve of a refinement agree as soon as their
vertices do. -/
private theorem testScheme_zero_hom_ext {Z : SchemesOver D.Y} {f g : Z ⟶ R.testScheme 0}
    (h : f ≫ R.nerveVertex 0 0 = g ≫ R.nerveVertex 0 0) : f = g :=
  R.testScheme_hom_ext_of_vertex fun i => by
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h

/-- A morphism into a term of the Čech nerve of a refinement, given by its vertices over `T`. -/
theorem exists_testScheme_lift {Z : SchemesOver D.Y} {n : ℕ}
    (u : Fin (n + 1) → (Z ⟶ R.unionTest)) (t : Z ⟶ T) (hu : ∀ i, u i ≫ R.unionHom = t) :
    ∃ e : Z ⟶ R.testScheme n, ∀ i, e ≫ R.nerveVertex n i = u i := by
  have hu' : ∀ i, (u i).left ≫ R.q = t.left := fun i => by
    simpa only [CostructuredArrow.comp_left, CostructuredArrow.homMk_left] using
      congrArg CommaMorphism.left (hu i)
  refine ⟨CostructuredArrow.homMk (WidePullback.lift t.left (fun i => (u i).left) hu') ?_,
    fun i => CostructuredArrow.hom_ext _ _ (WidePullback.lift_π _ _ _ _ _)⟩
  show (schemeSpaceFunctor B S hS).map _ ≫ (schemeSpaceFunctor B S hS).map _ ≫ T.hom = Z.hom
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, WidePullback.lift_base]
  exact CostructuredArrow.w t

end Vertices

/-! ### The base change of the disjoint union along a test scheme over `T` -/

section Cover

variable {Z : SchemesOver D.Y} (z : Z ⟶ T)

/-- The base change `Z ×_T V` of the disjoint union of a refinement, as a test scheme over `Y`. -/
abbrev baseCoverTest : SchemesOver D.Y :=
  (sliceTest D Z).obj (Over.mk (pullback.fst z.left R.q))

/-- The projection `Z ×_T V ⟶ Z`. -/
abbrev baseCoverHom : R.baseCoverTest z ⟶ Z :=
  sliceTestHom D Z (Over.mk (pullback.fst z.left R.q))

/-- The projection `Z ×_T V ⟶ V`. -/
def baseCoverUnion : R.baseCoverTest z ⟶ R.unionTest :=
  CostructuredArrow.homMk (pullback.snd z.left R.q) (by
    change (schemeSpaceFunctor B S hS).map (pullback.snd z.left R.q) ≫
        (schemeSpaceFunctor B S hS).map R.q ≫ T.hom =
      (schemeSpaceFunctor B S hS).map (pullback.fst z.left R.q) ≫ Z.hom
    rw [← CostructuredArrow.w z, ← Category.assoc, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, pullback.condition])

/-- The square formed by the two projections of `Z ×_T V`, the morphism `z : Z ⟶ T` and `V ⟶ T`
commutes. -/
theorem coverHom_comp : R.baseCoverHom z ≫ z = R.baseCoverUnion z ≫ R.unionHom :=
  CostructuredArrow.hom_ext _ _ pullback.condition

/-- The square of underlying schemes formed by the two projections of `Z ×_T V`, the morphism
`z : Z ⟶ T` and `V ⟶ T` is a pullback square. -/
theorem isPullback_baseCover :
    IsPullback (R.baseCoverHom z).left (R.baseCoverUnion z).left z.left R.unionHom.left :=
  IsPullback.of_hasPullback z.left R.q

/-- The base change `Z ×_T V ⟶ Z` is a covering of the big fppf site. -/
theorem baseCover_mem_topology :
    Sieve.ofArrows (fun _ : PUnit.{u + 1} => pullback z.left R.q)
        (fun _ => pullback.fst z.left R.q) ∈ BigFppfOver.topology B S hS Z.left := by
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    ((BigFppfOver.topology B S hS).pullback_stable z.left R.covering)
  intro W g hg
  obtain ⟨_, a, e⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr
    ⟨PUnit.unit, pullback.lift g a e, (pullback.lift_fst _ _ _).symm⟩

end Cover

/-! ### The input of Stacks 0DLA -/

section Input

/-- **The complex `K₀`** of the input of Stacks 0DLA: `K_0` pulled back to the degree-zero term
`V` of the Čech nerve, as an object of `Complexes_{X/Y}`. -/
abbrev nerveObject : ComplexesObject D :=
  restrictComplex R.unionComplex (R.nerveVertex 0 0)

/-- The morphism from `K₀` to `K_0`. -/
abbrev nerveObjectHom : ComplexesHom R.nerveObject R.unionComplex :=
  restrictComplexHom R.unionComplex (R.nerveVertex 0 0)

/-- The pullback of `K₀` along the face `δ₁ : V ×_T V ⟶ V` (the first projection). -/
abbrev nerveObject₁ : ComplexesObject D :=
  restrictComplex R.nerveObject (R.testSchemeMap (SimplexCategory.δ (1 : Fin 2)))

/-- The morphism over the face `δ₁`. -/
abbrev nerveObjectFace₁ : ComplexesHom R.nerveObject₁ R.nerveObject :=
  restrictComplexHom R.nerveObject (R.testSchemeMap (SimplexCategory.δ (1 : Fin 2)))

/-- The map of the Čech nerve induced by `g : ⦋0⦌ ⟶ ⦋n⦌`, followed by the vertex `V ⟶ V` and the
morphism `V ⟶ T`, is the augmentation of the `n`-th term. -/
theorem testSchemeMap_comp_vertex_zero {n : ℕ} (g : ⦋0⦌ ⟶ ⦋n⦌) :
    R.testSchemeMap g ≫ R.nerveVertex 0 0 ≫ R.unionHom = R.testSchemeHom n := by
  rw [vertex_comp_unionHom, testSchemeMap_comp_testSchemeHom]

/-- **The gluing isomorphism of the input of Stacks 0DLA**, as a morphism of `Complexes_{X/Y}`
over the other face `δ₀ : V ×_T V ⟶ V`: the transport of `K₀` along the descent datum of `K_0`. -/
theorem exists_cechFace₀ :
    ∃ ν : ComplexesHom R.nerveObject₁ R.nerveObject,
      ν.base = R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)) ∧
        R.IsUnionTransport (R.nerveObjectFace₁.comp R.nerveObjectHom)
          (ν.comp R.nerveObjectHom) := by
  have hc : (R.nerveObjectFace₁.comp R.nerveObjectHom).base ≫ R.unionHom =
      (R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)) ≫ R.nerveVertex 0 0) ≫ R.unionHom := by
    show (R.testSchemeMap (SimplexCategory.δ (1 : Fin 2)) ≫ R.nerveVertex 0 0) ≫ R.unionHom = _
    rw [Category.assoc, Category.assoc, testSchemeMap_comp_vertex_zero,
      testSchemeMap_comp_vertex_zero]
  obtain ⟨a', ha', hT⟩ := IsUnionTransport.exists R (R.nerveObjectFace₁.comp R.nerveObjectHom) _ hc
  obtain ⟨ν, hν, hν'⟩ := exists_complexesHom_lift R.nerveObjectHom
    (R.testSchemeMap (SimplexCategory.δ (0 : Fin 2))) a' ha'.symm
  exact ⟨ν, hν, hν' ▸ hT⟩

end Input

/-! ### The cocycle condition of the input -/

section Cocycle

/-- The first edge `δ₂ : V ×_T V ×_T V ⟶ V ×_T V` of the Čech nerve. -/
abbrev edge₀₁ : R.testScheme 2 ⟶ R.testScheme 1 := R.testSchemeMap (SimplexCategory.δ (2 : Fin 3))

/-- The last edge `δ₀ : V ×_T V ×_T V ⟶ V ×_T V` of the Čech nerve. -/
abbrev edge₁₂ : R.testScheme 2 ⟶ R.testScheme 1 := R.testSchemeMap (SimplexCategory.δ (0 : Fin 3))

/-- The outer edge `δ₁ : V ×_T V ×_T V ⟶ V ×_T V` of the Čech nerve. -/
abbrev edge₀₂ : R.testScheme 2 ⟶ R.testScheme 1 := R.testSchemeMap (SimplexCategory.δ (1 : Fin 3))

/-- The face `δ₁ : V ×_T V ⟶ V`. -/
abbrev nerveFace₁ : R.testScheme 1 ⟶ R.testScheme 0 :=
  R.testSchemeMap (SimplexCategory.δ (1 : Fin 2))

/-- The face `δ₀ : V ×_T V ⟶ V`. -/
abbrev nerveFace₀ : R.testScheme 1 ⟶ R.testScheme 0 :=
  R.testSchemeMap (SimplexCategory.δ (0 : Fin 2))

/-- The outer edge followed by the face `δ₁` agrees with the first edge followed by `δ₁`. -/
theorem edge₀₂_comp_face₁ : R.edge₀₂ ≫ R.nerveFace₁ = R.edge₀₁ ≫ R.nerveFace₁ :=
  R.testScheme_zero_hom_ext (by simp only [Category.assoc, testSchemeMap_comp_vertex]; rfl)

/-- The last edge followed by the face `δ₁` agrees with the first edge followed by `δ₀`. -/
theorem edge₁₂_comp_face₁ : R.edge₁₂ ≫ R.nerveFace₁ = R.edge₀₁ ≫ R.nerveFace₀ :=
  R.testScheme_zero_hom_ext (by simp only [Category.assoc, testSchemeMap_comp_vertex]; rfl)

/-- The outer edge followed by the face `δ₀` agrees with the last edge followed by `δ₀`. -/
theorem edge₀₂_comp_face₀ : R.edge₀₂ ≫ R.nerveFace₀ = R.edge₁₂ ≫ R.nerveFace₀ :=
  R.testScheme_zero_hom_ext (by simp only [Category.assoc, testSchemeMap_comp_vertex]; rfl)

/-- A map `V ×_T V ×_T V ⟶ V ×_T V` of the Čech nerve, followed by a map `V ×_T V ⟶ V`, the vertex
`V ⟶ V` and the morphism `V ⟶ T`, is the augmentation of the second term. -/
theorem edge_face_vertex_unionHom (e : ⦋1⦌ ⟶ ⦋2⦌) (g : ⦋0⦌ ⟶ ⦋1⦌) :
    (R.testSchemeMap e ≫ R.testSchemeMap g ≫ R.nerveVertex 0 0) ≫ R.unionHom =
      R.testSchemeHom 2 := by
  rw [Category.assoc, Category.assoc, testSchemeMap_comp_vertex_zero,
    testSchemeMap_comp_testSchemeHom]

/-- **The cocycle condition of the transport**: for three morphisms `c₁`, `d`, `c₃` out of a
triple overlap, if `ν` is a transport of `ν₀` and `d ≫ ν₀ = c₁ ≫ ν`, `c₃ ≫ ν₀ = c₁ ≫ ν₀`, then
`d ≫ ν = c₃ ≫ ν`. -/
theorem IsUnionTransport.transport_cocycle {Q X A : ComplexesObject D} (c₁ d c₃ : ComplexesHom Q X)
    (ν₀ ν : ComplexesHom X A) (r : ComplexesHom A R.unionComplex)
    (hT : R.IsUnionTransport (ν₀.comp r) (ν.comp r)) (e₁ : c₃.comp ν₀ = c₁.comp ν₀)
    (e₂ : d.comp ν₀ = c₁.comp ν)
    (hc : (c₁.comp (ν₀.comp r)).base ≫ R.unionHom = (d.comp (ν.comp r)).base ≫ R.unionHom)
    (hb : (d.comp ν).base = (c₃.comp ν).base) : d.comp ν = c₃.comp ν := by
  refine complexesHom_cancel_right r hb ?_
  rw [ComplexesHom.assoc, ComplexesHom.assoc]
  have T₁ := hT.comp_left c₁
  have T₂ := hT.comp_left d
  have T₃ := hT.comp_left c₃
  rw [← ComplexesHom.assoc d, e₂, ComplexesHom.assoc] at T₂
  rw [← ComplexesHom.assoc c₃, e₁, ComplexesHom.assoc] at T₃
  exact IsUnionTransport.unique (T₁.trans T₂) T₃ hc (congrArg (· ≫ r.base) hb)

end Cocycle

/-! ### The output of Stacks 0DLA -/

section Output

/-- **Stacks 0DLA on the small étale sites at the Čech nerve of a refinement**, read with the
terms, the faces, the last vertices and the augmentation of the nerve as base changes of test
schemes (`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.nerve_left_obj`,
`nerve_left_map`, `nerve_hom_app`, all definitional). -/
theorem smallEtaleHypercoverDescent_nerve (h0DLA : SmallEtaleHypercoverDescent B S hS) :
    ∀ (K₀ : derivedModules B S hS (D.space (R.testScheme 0)))
      (α : ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (1 : Fin 2))))).obj K₀ ≅
        ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (0 : Fin 2))))).obj K₀),
      IsHypercoverDescentCocycle (smallEtaleDerivedPullbackData B S hS).pull
        (smallEtaleDerivedPullbackData B S hS).compIso
        (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (1 : Fin 2))))
        (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (0 : Fin 2))))
        (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (2 : Fin 3))))
        (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (0 : Fin 3))))
        (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (1 : Fin 3)))) α →
      IsSmallEtaleQuasicoherentComplex B S hS (D.space (R.testScheme 0)) K₀ →
      (∀ (n : ℕ) (t : ℤ), t < 0 →
        Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap
            (R.testSchemeMap (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))))).obj K₀ ⟶
          (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap
            (R.testSchemeMap (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))))).obj K₀)⟦t⟧)) →
      ∃ (K : derivedModules B S hS (D.space T))
        (β : ((smallEtaleDerivedPullbackData B S hS).pull
          (D.relativeMap (R.testSchemeHom 0))).obj K ≅ K₀),
        IsSmallEtaleQuasicoherentComplex B S hS (D.space T) K ∧
          IsHypercoverDescentCompatible (smallEtaleDerivedPullbackData B S hS).pull
            (smallEtaleDerivedPullbackData B S hS).compIso (D.relativeMap (R.testSchemeHom 0))
            (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (1 : Fin 2))))
            (D.relativeMap (R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)))) α K β :=
  h0DLA R.nerve R.isHypercovering_nerve

/-- The augmentation `V ⟶ T` of the Čech nerve in degree zero is a covering of the big fppf site:
its sieve contains that of `q`. -/
theorem ofArrows_testSchemeHom_zero_mem_topology :
    Sieve.ofArrows (fun _ : PUnit.{u + 2} => (R.testScheme 0).left)
      (fun _ => (R.testSchemeHom 0).left) ∈ BigFppfOver.topology B S hS T.left := by
  obtain ⟨e, he⟩ := R.exists_testScheme_lift (n := 0) (fun _ => 𝟙 R.unionTest) R.unionHom
    (fun _ => Category.id_comp _)
  have h' : e ≫ R.testSchemeHom 0 = R.unionHom := by
    rw [← R.vertex_comp_unionHom 0 0, ← Category.assoc, he 0, Category.id_comp]
  have h : e.left ≫ (R.testSchemeHom 0).left = R.q := congrArg CommaMorphism.left h'
  refine (BigFppfOver.topology B S hS).superset_covering ?_ R.covering
  intro W g hg
  obtain ⟨_, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, a ≫ e.left, by rw [Category.assoc, h]⟩

/-- The input `K₀` of Stacks 0DLA has quasi-coherent cohomology (it is relatively perfect). -/
theorem nerveObject_isSmallEtaleQuasicoherent :
    IsSmallEtaleQuasicoherentComplex B S hS (D.space (R.testScheme 0)) R.nerveObject.E :=
  hasQuasicoherentCohomology_of_isRelativelyPerfect R.nerveObject.relativelyPerfect

/-- The pullbacks `K_n` of the input `K₀` along the last vertices have no negative
self-extensions, as soon as no base change of a member of the covering has any. -/
theorem subsingleton_shift_nerveVertex
    (hneg : ∀ (i : I) (V : SchemesOver D.Y) (h : V ⟶ (C.X i).T) (n : ℤ), n < 0 →
      Subsingleton
        (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj (C.X i).E ⟶
          (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj (C.X i).E)⟦n⟧))
    (n : ℕ) (t : ℤ) (ht : t < 0) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap
        (R.testSchemeMap (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))))).obj R.nerveObject.E ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap
        (R.testSchemeMap (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n))))).obj
          R.nerveObject.E)⟦t⟧) :=
  R.subsingleton_shift_of_hom_unionComplex hneg
    ((restrictComplexHom R.nerveObject
      (R.testSchemeMap (SimplexCategory.const ⦋0⦌ ⦋n⦌ (Fin.last n)))).comp R.nerveObjectHom) t ht

/-- **The output `K` of Stacks 0DLA as an object of `Complexes_{X/Y}`** over `T`: relative
perfectness (Stacks 0DL1 with 0DL2) and the condition on the fibres (Stacks 0DLC (1)) descend
along the covering `V ⟶ T` from `K₀ ≅ La₀^*K`. -/
abbrev nerveOutput (K : derivedModules B S hS (D.space T))
    (β : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.testSchemeHom 0))).obj K ≅
      R.nerveObject.E)
    (hK : IsSmallEtaleQuasicoherentComplex B S hS (D.space T) K) : ComplexesObject D :=
  ⟨T, K, D.relativelyPerfectDescends T (fun _ : PUnit.{u + 2} => R.testScheme 0)
      (fun _ => R.testSchemeHom 0) R.ofArrows_testSchemeHom_zero_mem_topology K hK
      (fun _ => isRelativelyPerfect_of_iso β R.nerveObject.relativelyPerfect),
    noNegativeFibreExtDescends_of_existsNegativeExtLocus D (existsNegativeExtLocus_proved B S hS)
      T (fun _ : PUnit.{u + 2} => R.testScheme 0) (fun _ => R.testSchemeHom 0)
      R.ofArrows_testSchemeHom_zero_mem_topology K
      (D.relativelyPerfectDescends T (fun _ : PUnit.{u + 2} => R.testScheme 0)
        (fun _ => R.testSchemeHom 0) R.ofArrows_testSchemeHom_zero_mem_topology K hK
        (fun _ => isRelativelyPerfect_of_iso β R.nerveObject.relativelyPerfect))
      (fun _ => hasNoNegativeFibreExt_of_iso β R.nerveObject.noNegativeFibreExt)⟩

/-- The morphism `K₀ ⟶ K` of `Complexes_{X/Y}` over the augmentation, with comparison `β`. -/
abbrev nerveOutputHom (K : derivedModules B S hS (D.space T))
    (β : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (R.testSchemeHom 0))).obj K ≅
      R.nerveObject.E)
    (hK : IsSmallEtaleQuasicoherentComplex B S hS (D.space T) K) :
    ComplexesHom R.nerveObject (R.nerveOutput K β hK) :=
  ⟨R.testSchemeHom 0, β.hom, Iso.isIso_hom β⟩

/-- Two morphisms to `K_0` related to one morphism to a member of the covering differ by the
descent datum of `K_0`. -/
theorem isUnionTransport_of_isUnionRelated {A : ComplexesObject D}
    {a a' : ComplexesHom A R.unionComplex} {i : I} {x : ComplexesHom A (C.X i)}
    (h : R.IsUnionRelated a x) (h' : R.IsUnionRelated a' x) : R.IsUnionTransport a a' :=
  fun _ g _ _ hx' => (h'.comp_left R g).of_isRelated
    (IsRelated.symm (IsUnionRelated.isRelated hx' (h.comp_left R g)))

/-- **A morphism out of `K₀` equalizing the two faces equalizes related morphisms.** Let
`ω : K₀ ⟶ G` satisfy `δ₁ ≫ ω = ν ≫ ω` for the two morphisms `δ₁, ν : δ₁^*K₀ ⟶ K₀` over the two
faces, `ν` the transport of `δ₁` along the descent datum of `K_0`. Then `g₁ ≫ ω = g₂ ≫ ω` for any
two morphisms `g₁, g₂ : A ⟶ K₀` whose composites with `K₀ ⟶ K_0` are related to one morphism to a
member of the covering: they factor through `V ×_T V`. -/
theorem comp_eq_of_isUnionRelated (f₁ ν : ComplexesHom R.nerveObject₁ R.nerveObject)
    (hf₁ : f₁.base = R.nerveFace₁) (hν : ν.base = R.nerveFace₀)
    (hT : R.IsUnionTransport (f₁.comp R.nerveObjectHom) (ν.comp R.nerveObjectHom))
    {G : ComplexesObject D} (ω : ComplexesHom R.nerveObject G) (hω : f₁.comp ω = ν.comp ω)
    {A : ComplexesObject D} (g₁ g₂ : ComplexesHom A R.nerveObject) {i : I}
    (x : ComplexesHom A (C.X i)) (h₁ : R.IsUnionRelated (g₁.comp R.nerveObjectHom) x)
    (h₂ : R.IsUnionRelated (g₂.comp R.nerveObjectHom) x) : g₁.comp ω = g₂.comp ω := by
  have hb₁ : x.base ≫ C.a i = (g₁.base ≫ R.nerveVertex 0 0) ≫ R.unionHom := h₁.1
  have hb₂ : x.base ≫ C.a i = (g₂.base ≫ R.nerveVertex 0 0) ≫ R.unionHom := h₂.1
  obtain ⟨e, he⟩ := R.exists_testScheme_lift (n := 1)
    ![g₁.base ≫ R.nerveVertex 0 0, g₂.base ≫ R.nerveVertex 0 0]
    ((g₁.base ≫ R.nerveVertex 0 0) ≫ R.unionHom) (fun k => by
      fin_cases k
      · rfl
      · exact hb₂.symm.trans hb₁)
  have e₁ : e ≫ R.nerveFace₁ = g₁.base :=
    R.testScheme_zero_hom_ext (by rw [Category.assoc, R.testSchemeMap_comp_vertex]; exact he 0)
  have e₂ : e ≫ R.nerveFace₀ = g₂.base :=
    R.testScheme_zero_hom_ext (by rw [Category.assoc, R.testSchemeMap_comp_vertex]; exact he 1)
  obtain ⟨κ, hκ, hκ'⟩ := exists_complexesHom_lift f₁ e g₁ (by rw [hf₁, e₁])
  have hκν : κ.comp ν = g₂ := by
    refine complexesHom_cancel_right R.nerveObjectHom ?_ ?_
    · show κ.base ≫ ν.base = g₂.base
      rw [hκ, hν, e₂]
    · have T₁ := hT.comp_left κ
      rw [← ComplexesHom.assoc, hκ'] at T₁
      rw [ComplexesHom.assoc]
      refine IsUnionTransport.unique T₁ (R.isUnionTransport_of_isUnionRelated h₁ h₂) ?_ ?_
      · show (g₁.base ≫ R.nerveVertex 0 0) ≫ R.unionHom =
          (κ.base ≫ ν.base ≫ R.nerveVertex 0 0) ≫ R.unionHom
        rw [← Category.assoc, hκ, hν, e₂, ← hb₁, hb₂]
      · show κ.base ≫ ν.base ≫ R.nerveVertex 0 0 = g₂.base ≫ R.nerveVertex 0 0
        rw [← Category.assoc, hκ, hν, e₂]
  rw [← hκ', ComplexesHom.assoc, hω, ← ComplexesHom.assoc, hκν]

/-- **The morphisms `ψ i` descend.** With `ω` as in
`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.comp_eq_of_isUnionRelated`
lying over the augmentation, every member `K_i` of the covering has a morphism `Ψ : K_i ⟶ G` over
`a_i`, by descent along `T_i ×_T V ⟶ T_i` (Stacks 0DLG), with `y ≫ Ψ = g ≫ ω` whenever
`g ≫ (K₀ ⟶ K_0)` is related to `y`. -/
theorem exists_complexesHom_descended (f₁ ν : ComplexesHom R.nerveObject₁ R.nerveObject)
    (hf₁ : f₁.base = R.nerveFace₁) (hν : ν.base = R.nerveFace₀)
    (hT : R.IsUnionTransport (f₁.comp R.nerveObjectHom) (ν.comp R.nerveObjectHom))
    {G : ComplexesObject D} (hG : G.T = T) (ω : ComplexesHom R.nerveObject G)
    (hωb : ω.base ≫ eqToHom hG = R.testSchemeHom 0) (hω : f₁.comp ω = ν.comp ω) (i : I) :
    ∃ Ψ : ComplexesHom (C.X i) G, Ψ.base ≫ eqToHom hG = C.a i ∧
      ∀ {A : ComplexesObject D} (y : ComplexesHom A (C.X i)) (g : ComplexesHom A R.nerveObject),
        R.IsUnionRelated (g.comp R.nerveObjectHom) y → y.comp Ψ = g.comp ω := by
  subst hG
  simp only [eqToHom_refl, Category.comp_id] at hωb ⊢
  obtain ⟨a, ha, har⟩ := IsUnionRelated.exists_unionHom R
    (restrictComplexHom (C.X i) (R.baseCoverHom (C.a i))) (R.baseCoverUnion (C.a i))
    (R.coverHom_comp (C.a i))
  obtain ⟨e₀, he₀⟩ := R.exists_testScheme_lift (n := 0) (fun _ => R.baseCoverUnion (C.a i))
    (R.baseCoverUnion (C.a i) ≫ R.unionHom) (fun _ => rfl)
  obtain ⟨l, hl, hl'⟩ := exists_complexesHom_lift R.nerveObjectHom e₀ a ((he₀ 0).trans ha.symm)
  have hrel : ∀ {A' : ComplexesObject D} (g : ComplexesHom A' (restrictComplex (C.X i)
      (R.baseCoverHom (C.a i)))), R.IsUnionRelated ((g.comp l).comp R.nerveObjectHom)
        (g.comp (restrictComplexHom (C.X i) (R.baseCoverHom (C.a i)))) := fun g => by
    rw [ComplexesHom.assoc, hl']
    exact har.comp_left R g
  obtain ⟨Ψ, hΨb, hΨ⟩ := exists_complexesHom_of_descent (P := C.X i) (G := G) (C.a i)
    (pullback.fst (C.a i).left R.q) (R.baseCover_mem_topology (C.a i)) (l.comp ω) (by
      show l.base ≫ ω.base = R.baseCoverHom (C.a i) ≫ C.a i
      rw [hl, hωb, ← R.vertex_comp_unionHom 0 0, ← Category.assoc, he₀ 0, R.coverHom_comp])
    (fun A h₁ h₂ hh => by
      rw [← ComplexesHom.assoc, ← ComplexesHom.assoc]
      refine R.comp_eq_of_isUnionRelated f₁ ν hf₁ hν hT ω hω _ _ _ (hrel h₁) ?_
      rw [hh]
      exact hrel h₂)
  refine ⟨Ψ, hΨb, fun {A} y g hg => ?_⟩
  obtain ⟨θb, hθ₁, -⟩ := exists_hom_of_isPullback_left (R.isPullback_baseCover (C.a i)) y.base
    (g.base ≫ R.nerveVertex 0 0) hg.1
  obtain ⟨θ, -, hθ'⟩ := exists_complexesHom_lift
    (restrictComplexHom (C.X i) (R.baseCoverHom (C.a i))) θb y hθ₁
  rw [← hθ', ComplexesHom.assoc, hΨ, ← ComplexesHom.assoc]
  refine R.comp_eq_of_isUnionRelated f₁ ν hf₁ hν hT ω hω _ _ y ?_ hg
  rw [← hθ']
  exact hrel θ

end Output

end SmallRefinement

end CechCover

end ComplexesSituation

open ComplexesSituation ComplexesSituation.CechCover ComplexesSituation.CechCover.SmallRefinement in
/-- **Stacks 0DLA on the small étale sites gives its Čech case
`AlgebraicGeometry.Space.ComplexesSituation.CechDescent`.** A Čech covering `C` of `T` in
`Complexes_{X/Y}` is refined by a single fppf covering `q : V ⟶ T` out of a disjoint union of
schemes of the site; Stacks 0DLA is applied to the Čech nerve of `q` base changed to `X`
(`AlgebraicGeometry.Space.ComplexesSituation.CechCover.SmallRefinement.nerve`), with input the
pullback `K₀` of the complex `K_0` glued from the `K_i`, gluing map the descent datum of `K_0`
(its cocycle condition is the transport cocycle on `V ×_T V ×_T V`), and the vanishing of the
negative self-extensions from the hypothesis of `CechDescent`. The output `K` is an object of
`Complexes_{X/Y}` over `T`; the compatibility of `β : a₀^*K ≅ K₀` with the gluing map makes
`K₀ ⟶ K` equalize the two faces, so that it descends to morphisms `K_i ⟶ K` over the `a_i`
(Stacks 0DLG), whose comparisons are the `ψ i`; they are compatible on every double overlap since
both restrictions agree after the base change to `V`. -/
theorem cechDescentOfSmallEtaleHypercoverDescent :
    CechDescentOfSmallEtaleHypercoverDescent B S hS := by
  intro h0DLA D T I C hneg
  obtain ⟨R⟩ := C.nonempty_smallRefinement
  obtain ⟨⟨νb, νf, νi⟩, hν, hT⟩ := R.exists_cechFace₀
  change νb = R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)) at hν
  subst hν
  obtain ⟨⟨c₃b, c₃f, c₃i⟩, hc₃, hc₃'⟩ := exists_complexesHom_lift R.nerveObjectFace₁ R.edge₀₂
    ((restrictComplexHom R.nerveObject₁ R.edge₀₁).comp R.nerveObjectFace₁) R.edge₀₂_comp_face₁
  change c₃b = R.edge₀₂ at hc₃
  subst hc₃
  obtain ⟨⟨db, df, di⟩, hd, hd'⟩ := exists_complexesHom_lift R.nerveObjectFace₁ R.edge₁₂
    ((restrictComplexHom R.nerveObject₁ R.edge₀₁).comp
      (⟨R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)), νf, νi⟩ :
        ComplexesHom R.nerveObject₁ R.nerveObject)) R.edge₁₂_comp_face₁
  change db = R.edge₁₂ at hd
  subst hd
  have e₃ := IsUnionTransport.transport_cocycle R (restrictComplexHom R.nerveObject₁ R.edge₀₁)
    ⟨R.edge₁₂, df, di⟩ ⟨R.edge₀₂, c₃f, c₃i⟩ R.nerveObjectFace₁
    ⟨R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)), νf, νi⟩ R.nerveObjectHom hT hc₃' hd'
    (by
      show (R.edge₀₁ ≫ R.nerveFace₁ ≫ R.nerveVertex 0 0) ≫ R.unionHom =
        (R.edge₁₂ ≫ R.nerveFace₀ ≫ R.nerveVertex 0 0) ≫ R.unionHom
      rw [R.edge_face_vertex_unionHom, R.edge_face_vertex_unionHom])
    (by
      show R.edge₁₂ ≫ R.nerveFace₀ = R.edge₀₂ ≫ R.nerveFace₀
      exact R.edge₀₂_comp_face₀.symm)
  have hcoc := isHypercoverDescentCocycle_of_complexesHom
    (restrictComplexHom R.nerveObject₁ R.edge₀₁)
    ⟨R.edge₁₂, df, di⟩ ⟨R.edge₀₂, c₃f, c₃i⟩ R.nerveObjectFace₁
    ⟨R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)), νf, νi⟩ (@asIso _ _ _ _ νf νi).symm
    (Category.id_comp _) hc₃'.symm hd'.symm e₃
  obtain ⟨K, β, hK, hcompat⟩ := R.smallEtaleHypercoverDescent_nerve h0DLA R.nerveObject.E
    (@asIso _ _ _ _ νf νi).symm hcoc R.nerveObject_isSmallEtaleQuasicoherent
    (R.subsingleton_shift_nerveVertex hneg)
  have hω := comp_eq_of_isHypercoverDescentCompatible (X := R.nerveOutput K β hK)
    R.nerveObjectFace₁ ⟨R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)), νf, νi⟩
    (R.testSchemeHom 0) β (@asIso _ _ _ _ νf νi).symm (Category.id_comp _)
    ((R.testSchemeMap_comp_testSchemeHom _).trans (R.testSchemeMap_comp_testSchemeHom _).symm)
    hcompat
  choose Ψ hΨb hΨ using fun i => R.exists_complexesHom_descended R.nerveObjectFace₁
    ⟨R.testSchemeMap (SimplexCategory.δ (0 : Fin 2)), νf, νi⟩ rfl rfl hT
    (G := R.nerveOutput K β hK) rfl (R.nerveOutputHom K β hK) (Category.comp_id _) hω i
  have hΨb' : ∀ i, (Ψ i).base = C.a i := fun i => (Category.comp_id _).symm.trans (hΨb i)
  have hcomm : ∀ i j, (C.n i j).comp (Ψ i) = (C.m i j).comp (Ψ j) := by
    intro i j
    refine complexesHom_ext_of_descent (P := C.X₂ i j) ?_
      (pullback.fst ((C.n i j).base ≫ C.a i).left R.q) (R.baseCover_mem_topology _) ?_
    · show (C.n i j).base ≫ (Ψ i).base = (C.m i j).base ≫ (Ψ j).base
      rw [hΨb' i, hΨb' j]
      exact C.w i j
    obtain ⟨a₂, -, har₂⟩ := IsUnionRelated.exists_unionHom R
      ((restrictComplexHom (C.X₂ i j) (R.baseCoverHom ((C.n i j).base ≫ C.a i))).comp (C.n i j))
      (R.baseCoverUnion ((C.n i j).base ≫ C.a i)) (by
        show (R.baseCoverHom _ ≫ (C.n i j).base) ≫ C.a i = _
        rw [Category.assoc]
        exact R.coverHom_comp _)
    have har₂' := har₂.of_isRelated
      (y := (restrictComplexHom (C.X₂ i j) (R.baseCoverHom ((C.n i j).base ≫ C.a i))).comp
        (C.m i j)) ⟨_, rfl, rfl⟩
    obtain ⟨e₀, he₀⟩ := R.exists_testScheme_lift (n := 0) (fun _ => a₂.base)
      (a₂.base ≫ R.unionHom) (fun _ => rfl)
    obtain ⟨l, -, hl'⟩ := exists_complexesHom_lift R.nerveObjectHom e₀ a₂ (he₀ 0)
    rw [← ComplexesHom.assoc, ← ComplexesHom.assoc, hΨ i _ l (by rw [hl']; exact har₂),
      hΨ j _ l (by rw [hl']; exact har₂')]
  refine ⟨(R.nerveOutput K β hK).E,
    fun i => (D.relativeMapComparison (hΨb' i).symm).app _ ≪≫ asIso (Ψ i).fibre, hK,
    fun i j => ?_⟩
  have e := hcomm i j
  rw [← complexesHom_mk_trans_eq (Ψ i) (hΨb' i).symm,
    ← complexesHom_mk_trans_eq (Ψ j) (hΨb' j).symm] at e
  exact fibresCompatible_of_comp_mk_eq (C.n i j) (C.m i j) _ _ _ _ (C.w i j) e

end AlgebraicGeometry.Space

end
