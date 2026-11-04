module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescent

/-!
# Descent of quotients along an fpqc covering of a test scheme

In Situation 082M — a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` of a big fppf
site together with a quasi-coherent `𝒪_X`-module `F` — let `{g i : U i ⟶ T}` be a family of
test schemes over `Y` whose underlying morphisms of schemes form an fpqc covering.  This file
proves that the quotients of the modules `F_{U i}` descend along it, which is the content of the
proof of Stacks 082P: the base changes `{X_{U i} ⟶ X_T}` are an fpqc covering of `X_T`
(Stacks 03MR), and the bijection of Remark 08IU — whose two halves are
`AlgebraicGeometry.Space.eq_zero_of_modulePullback_map_eq_zero_of_isFpqcCovering` and
`AlgebraicGeometry.Space.exists_epi_of_isFpqcCovering`, both consequences of Stacks 04W8 —
descends a compatible family of quotients to a quotient of `F_T`.

## Main results

* `AlgebraicGeometry.Space.le_of_quotientRestrict_le_of_isFpqcCovering` and
  `AlgebraicGeometry.Space.eq_of_quotientRestrict_eq_of_isFpqcCovering`: a quotient is
  determined by its restrictions along an fpqc covering, with no hypothesis on the quotients.
* `AlgebraicGeometry.Space.exists_quotientRestrictOver_eq_of_isFpqcCovering`: a family of
  quasi-coherent quotients of the inverse images of a quasi-coherent module, agreeing on the
  pairwise fibre products, is the family of restrictions of a quasi-coherent quotient.
* `AlgebraicGeometry.Space.QuotientSituation.eq_of_quotientPullback_eq_of_isFpqcCovering` and
  `AlgebraicGeometry.Space.QuotientSituation.exists_quotientPullback_eq_of_isFpqcCovering`: the
  two halves for the quotients of Situation 082M along an fpqc covering of a test scheme.
* `AlgebraicGeometry.Space.QuotientSituation.isSheafFor_quotientSubfunctor`: the subfunctor of
  quotients cut out by a pullback-stable condition which descends along fpqc coverings satisfies
  the sheaf condition for the presieve of an fpqc covering of a test scheme.

## References

* [Stacks Project, Tag 082P](https://stacks.math.columbia.edu/tag/082P)
* [Stacks Project, Tag 08IU](https://stacks.math.columbia.edu/tag/08IU)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v

open QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/- The ambient-universe abelian structure on sheaves of modules does not apply to the modules on
an algebraic space, whose sections live in the universe of the site's morphisms; it is switched
off so that instance search finds the structure of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean` directly. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-! ### A quotient is determined by its restrictions -/

/-- **Containment of quotients is fpqc local, with no hypothesis.**  This is
`AlgebraicGeometry.Space.le_of_quotientRestrict_le` with the carried faithfulness clause of
Stacks 04W8 discharged, and without the quasi-coherence hypotheses that clause was stated
with. -/
theorem le_of_quotientRestrict_le_of_isFpqcCovering {I : Type v} {X : AlgebraicSpaces B S hS}
    {Z : I → AlgebraicSpaces B S hS} (p : ∀ i, Z i ⟶ X)
    (hp : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    {F : Modules.{u, u} B S hS X.1 X.2} {K K' : Subobject F}
    (h : ∀ i, quotientRestrict (p i) K ≤ quotientRestrict (p i) K') : K ≤ K' := by
  have hzero : K.arrow ≫ cokernel.π K'.arrow = 0 :=
    eq_zero_of_modulePullback_map_eq_zero_of_isFpqcCovering B S hS Z p hp _ fun i ↦
      modulePullback_map_arrow_comp_cokernel_π_eq_zero (p i) (h i)
  have hle := le_kernelSubobject (cokernel.π K'.arrow) K hzero
  rwa [kernelSubobject_cokernel_π] at hle

/-- **A quotient is determined by its restrictions along an fpqc covering**, with no
hypothesis on the quotients: the injectivity half of the bijection of Stacks 08IU. -/
theorem eq_of_quotientRestrict_eq_of_isFpqcCovering {I : Type v} {X : AlgebraicSpaces B S hS}
    {Z : I → AlgebraicSpaces B S hS} (p : ∀ i, Z i ⟶ X)
    (hp : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    {F : Modules.{u, u} B S hS X.1 X.2} {K K' : Subobject F}
    (h : ∀ i, quotientRestrict (p i) K = quotientRestrict (p i) K') : K = K' :=
  le_antisymm (le_of_quotientRestrict_le_of_isFpqcCovering p hp fun i ↦ (h i).le)
    (le_of_quotientRestrict_le_of_isFpqcCovering p hp fun i ↦ (h i).ge)

/-- A quotient of an inverse image is determined by its normalised restrictions along an fpqc
covering. -/
theorem eq_of_quotientRestrictOver_eq_of_isFpqcCovering {I : Type v}
    {X W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    {a : W ⟶ X} {aZ : ∀ i, Z i ⟶ X} (p : ∀ i, Z i ⟶ W) (hp : ∀ i, p i ≫ a = aZ i)
    (hcov : IsFpqcCovering B S hS fun i ↦ (p i).hom) (F : Modules.{u, u} B S hS X.1 X.2)
    {K K' : Subobject ((modulePullback B S hS a).obj F)}
    (h : ∀ i, quotientRestrictOver (p i) (hp i) F K = quotientRestrictOver (p i) (hp i) F K') :
    K = K' := by
  refine eq_of_quotientRestrict_eq_of_isFpqcCovering p hcov fun i ↦ ?_
  refine quotientTransport_injective ((modulePullbackTriangle B S hS (hp i)).app F) ?_
  rw [← quotientRestrictOver_eq_quotientTransport, ← quotientRestrictOver_eq_quotientTransport]
  exact h i

/-! ### Coherence of the comparisons on a pairwise fibre product -/

/-- **An abstract coherence of comparisons along a commuting square**, stated at variable
functors so that it is instantiated rather than re-proved at the inverse images of modules.
Given two factorisations `t ≪≫ s` of a functor `AP` through `A` along the two sides of a square,
which are related through `u ≪≫ v` to a single factorisation through `K₀ ≅ K₁`, the two
factorisations differ by the comparison `c` of the two sides. -/
theorem CategoryTheory.Iso.app_comp_map_comp_app_of_whisker {Cx Cw Cz₀ Cz₁ Cp : Type*}
    [Category* Cx] [Category* Cw] [Category* Cz₀] [Category* Cz₁] [Category* Cp]
    {A : Cx ⥤ Cw} {Q₀ : Cw ⥤ Cz₀} {Q₁ : Cw ⥤ Cz₁} {R₀ : Cz₀ ⥤ Cp} {R₁ : Cz₁ ⥤ Cp}
    {AZ₀ : Cx ⥤ Cz₀} {AZ₁ : Cx ⥤ Cz₁} {AP : Cx ⥤ Cp} {K₀ K₁ : Cw ⥤ Cp}
    (t₀ : AP ≅ AZ₀ ⋙ R₀) (t₁ : AP ≅ AZ₁ ⋙ R₁) (s₀ : AZ₀ ≅ A ⋙ Q₀) (s₁ : AZ₁ ≅ A ⋙ Q₁)
    (u₀ : AP ≅ A ⋙ K₀) (u₁ : AP ≅ A ⋙ K₁) (v₀ : K₀ ≅ Q₀ ⋙ R₀) (v₁ : K₁ ≅ Q₁ ⋙ R₁)
    (ε : K₀ ≅ K₁) (c : Q₀ ⋙ R₀ ≅ Q₁ ⋙ R₁)
    (H₀ : u₀ ≪≫ Functor.isoWhiskerLeft A v₀ =
      t₀ ≪≫ Functor.isoWhiskerRight s₀ R₀ ≪≫ Functor.associator A Q₀ R₀)
    (H₁ : u₁ ≪≫ Functor.isoWhiskerLeft A v₁ =
      t₁ ≪≫ Functor.isoWhiskerRight s₁ R₁ ≪≫ Functor.associator A Q₁ R₁)
    (Hε : u₀ ≪≫ Functor.isoWhiskerLeft A ε = u₁) (Hc : v₀ ≪≫ c = ε ≪≫ v₁) (X : Cx) :
    t₀.hom.app X ≫ R₀.map (s₀.hom.app X) ≫ c.hom.app (A.obj X) =
      t₁.hom.app X ≫ R₁.map (s₁.hom.app X) := by
  have key : (t₀ ≪≫ Functor.isoWhiskerRight s₀ R₀ ≪≫ Functor.associator A Q₀ R₀) ≪≫
      Functor.isoWhiskerLeft A c =
        t₁ ≪≫ Functor.isoWhiskerRight s₁ R₁ ≪≫ Functor.associator A Q₁ R₁ := by
    rw [← H₀, ← H₁, Iso.trans_assoc, ← Functor.isoWhiskerLeft_trans, Hc,
      Functor.isoWhiskerLeft_trans, ← Iso.trans_assoc, Hε]
  have h := congrArg (fun e ↦ e.hom.app X) key
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp, Category.comp_id, Category.assoc] using h

/-- **The comparison on a pairwise fibre product carries one projection to the other**, the
form in which the effectivity of Stacks 08IU consumes the coherence of
`CategoryTheory.Iso.app_comp_map_comp_app_of_whisker`.  If an isomorphism `σ` carries the two
projections read on `AP` to each other, it carries the two projections read on the sides of the
square to each other through `c`.  Stated at variable functors. -/
theorem CategoryTheory.Iso.map_comp_hom_eq_app_hom_comp_map_of_whisker {Cx Cw Cz₀ Cz₁ Cp : Type*}
    [Category* Cx] [Category* Cw] [Category* Cz₀] [Category* Cz₁] [Category* Cp]
    {A : Cx ⥤ Cw} {Q₀ : Cw ⥤ Cz₀} {Q₁ : Cw ⥤ Cz₁} {R₀ : Cz₀ ⥤ Cp} {R₁ : Cz₁ ⥤ Cp}
    {AZ₀ : Cx ⥤ Cz₀} {AZ₁ : Cx ⥤ Cz₁} {AP : Cx ⥤ Cp} {K₀ K₁ : Cw ⥤ Cp}
    (t₀ : AP ≅ AZ₀ ⋙ R₀) (t₁ : AP ≅ AZ₁ ⋙ R₁) (s₀ : AZ₀ ≅ A ⋙ Q₀) (s₁ : AZ₁ ≅ A ⋙ Q₁)
    (u₀ : AP ≅ A ⋙ K₀) (u₁ : AP ≅ A ⋙ K₁) (v₀ : K₀ ≅ Q₀ ⋙ R₀) (v₁ : K₁ ≅ Q₁ ⋙ R₁)
    (ε : K₀ ≅ K₁) (c : Q₀ ⋙ R₀ ≅ Q₁ ⋙ R₁)
    (H₀ : u₀ ≪≫ Functor.isoWhiskerLeft A v₀ =
      t₀ ≪≫ Functor.isoWhiskerRight s₀ R₀ ≪≫ Functor.associator A Q₀ R₀)
    (H₁ : u₁ ≪≫ Functor.isoWhiskerLeft A v₁ =
      t₁ ≪≫ Functor.isoWhiskerRight s₁ R₁ ≪≫ Functor.associator A Q₁ R₁)
    (Hε : u₀ ≪≫ Functor.isoWhiskerLeft A ε = u₁) (Hc : v₀ ≪≫ c = ε ≪≫ v₁) (X : Cx)
    {G₀ : Cz₀} {G₁ : Cz₁} (κ₀ : AZ₀.obj X ⟶ G₀) (κ₁ : AZ₁.obj X ⟶ G₁)
    (σ : R₀.obj G₀ ≅ R₁.obj G₁)
    (hσ : (t₀.hom.app X ≫ R₀.map κ₀) ≫ σ.hom = t₁.hom.app X ≫ R₁.map κ₁) :
    R₀.map ((s₀.app X).inv ≫ κ₀) ≫ σ.hom =
      (c.app (A.obj X)).hom ≫ R₁.map ((s₁.app X).inv ≫ κ₁) := by
  have key := CategoryTheory.Iso.app_comp_map_comp_app_of_whisker t₀ t₁ s₀ s₁ u₀ u₁ v₀ v₁ ε c
    H₀ H₁ Hε Hc X
  rw [← cancel_epi (t₀.hom.app X ≫ R₀.map (s₀.hom.app X))]
  have e₀ : (t₀.hom.app X ≫ R₀.map (s₀.hom.app X)) ≫ R₀.map ((s₀.app X).inv ≫ κ₀) =
      t₀.hom.app X ≫ R₀.map κ₀ := by
    simp only [Category.assoc, ← Functor.map_comp, Iso.app_inv, Iso.hom_inv_id_app_assoc]
  have e₁ : t₁.hom.app X ≫ R₁.map (s₁.hom.app X) ≫ R₁.map ((s₁.app X).inv ≫ κ₁) =
      t₁.hom.app X ≫ R₁.map κ₁ := by
    simp only [← Functor.map_comp, Iso.app_inv, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, e₀, hσ, Iso.app_hom, ← e₁, ← reassoc_of% key]
  simp only [Category.assoc]

/-- The form of `CategoryTheory.Iso.map_comp_hom_eq_app_hom_comp_map_of_whisker` in which the
components of `s₀`, `s₁` and `c` are replaced by isomorphisms with the same underlying morphisms
between the iterated images, so that it can be instantiated where those images are written
iteratively.  Stated at variable functors. -/
theorem CategoryTheory.Iso.map_comp_hom_eq_hom_comp_map_of_whisker {Cx Cw Cz₀ Cz₁ Cp : Type*}
    [Category* Cx] [Category* Cw] [Category* Cz₀] [Category* Cz₁] [Category* Cp]
    {A : Cx ⥤ Cw} {Q₀ : Cw ⥤ Cz₀} {Q₁ : Cw ⥤ Cz₁} {R₀ : Cz₀ ⥤ Cp} {R₁ : Cz₁ ⥤ Cp}
    {AZ₀ : Cx ⥤ Cz₀} {AZ₁ : Cx ⥤ Cz₁} {AP : Cx ⥤ Cp} {K₀ K₁ : Cw ⥤ Cp}
    (t₀ : AP ≅ AZ₀ ⋙ R₀) (t₁ : AP ≅ AZ₁ ⋙ R₁) (s₀ : AZ₀ ≅ A ⋙ Q₀) (s₁ : AZ₁ ≅ A ⋙ Q₁)
    (u₀ : AP ≅ A ⋙ K₀) (u₁ : AP ≅ A ⋙ K₁) (v₀ : K₀ ≅ Q₀ ⋙ R₀) (v₁ : K₁ ≅ Q₁ ⋙ R₁)
    (ε : K₀ ≅ K₁) (c : Q₀ ⋙ R₀ ≅ Q₁ ⋙ R₁)
    (H₀ : u₀ ≪≫ Functor.isoWhiskerLeft A v₀ =
      t₀ ≪≫ Functor.isoWhiskerRight s₀ R₀ ≪≫ Functor.associator A Q₀ R₀)
    (H₁ : u₁ ≪≫ Functor.isoWhiskerLeft A v₁ =
      t₁ ≪≫ Functor.isoWhiskerRight s₁ R₁ ≪≫ Functor.associator A Q₁ R₁)
    (Hε : u₀ ≪≫ Functor.isoWhiskerLeft A ε = u₁) (Hc : v₀ ≪≫ c = ε ≪≫ v₁) (X : Cx)
    (s₀' : AZ₀.obj X ≅ Q₀.obj (A.obj X)) (hs₀ : s₀'.hom = s₀.hom.app X)
    (s₁' : AZ₁.obj X ≅ Q₁.obj (A.obj X)) (hs₁ : s₁'.hom = s₁.hom.app X)
    (c' : R₀.obj (Q₀.obj (A.obj X)) ≅ R₁.obj (Q₁.obj (A.obj X)))
    (hc' : c'.hom = c.hom.app (A.obj X))
    {G₀ : Cz₀} {G₁ : Cz₁} (κ₀ : AZ₀.obj X ⟶ G₀) (κ₁ : AZ₁.obj X ⟶ G₁)
    (σ : R₀.obj G₀ ≅ R₁.obj G₁)
    (hσ : (t₀.hom.app X ≫ R₀.map κ₀) ≫ σ.hom = t₁.hom.app X ≫ R₁.map κ₁) :
    R₀.map (s₀'.inv ≫ κ₀) ≫ σ.hom = c'.hom ≫ R₁.map (s₁'.inv ≫ κ₁) := by
  have e₀ : s₀' = s₀.app X := Iso.ext hs₀
  have e₁ : s₁' = s₁.app X := Iso.ext hs₁
  have ec : c' = c.app (A.obj X) := Iso.ext hc'
  subst e₀ e₁ ec
  exact CategoryTheory.Iso.map_comp_hom_eq_app_hom_comp_map_of_whisker t₀ t₁ s₀ s₁ u₀ u₁ v₀ v₁
    ε c H₀ H₁ Hε Hc X κ₀ κ₁ σ hσ

section Coherence

variable {X W P : AlgebraicSpaces B S hS} (a : W ⟶ X) (F : Modules.{u, u} B S hS X.1 X.2)

/-- The comparison along a composite, followed by the transport along an equality of the first
factor, is the comparison along the other presentation. -/
theorem modulePullbackTriangle_trans_isoWhiskerLeft_eqToIso {k₀ k₁ : P ⟶ W} (w : k₀ = k₁)
    {aP : P ⟶ X} (h₀ : k₀ ≫ a = aP) (h₁ : k₁ ≫ a = aP) :
    modulePullbackTriangle B S hS h₀ ≪≫
        Functor.isoWhiskerLeft (modulePullback B S hS a)
          (eqToIso (congrArg (modulePullback B S hS) w)) =
      modulePullbackTriangle B S hS h₁ := by
  subst w
  simp

/-- The comparison of Stacks 03LU along a composite `r ≫ q`, followed by the canonical
comparison of the two sides of a commuting square, is the transport along the square followed by
the comparison along the other side. -/
theorem modulePullbackTriangle_rfl_trans_canonicalComparisonIso {Z₀ Z₁ : AlgebraicSpaces B S hS}
    (r₀ : P ⟶ Z₀) (r₁ : P ⟶ Z₁) (q₀ : Z₀ ⟶ W) (q₁ : Z₁ ⟶ W) (w : r₀ ≫ q₀ = r₁ ≫ q₁) :
    modulePullbackTriangle B S hS (rfl : r₀ ≫ q₀ = r₀ ≫ q₀) ≪≫
        canonicalComparisonIso B S hS r₀ r₁ q₀ q₁ w =
      eqToIso (congrArg (modulePullback B S hS) w) ≪≫
        modulePullbackTriangle B S hS (rfl : r₁ ≫ q₁ = r₁ ≫ q₁) := by
  rw [modulePullbackTriangle_rfl, modulePullbackTriangle_rfl, canonicalComparisonIso,
    Iso.symm_self_id_assoc]

/-- The comparison of an inverse image with an iterated inverse image along a factorisation is
the component of `AlgebraicGeometry.Space.modulePullbackTriangle` at the same equation. -/
theorem pullbackComparison_hom_eq_modulePullbackTriangle_hom_app_of_eq
    {A P' : AlgebraicSpaces B S hS}
    (g : P' ⟶ W) (p : W ⟶ A) (v : P' ⟶ A) (hv : g ≫ p = v) (M : Modules.{u, u} B S hS A.1 A.2) :
    (pullbackComparison B S hS g p v hv M).hom = (modulePullbackTriangle B S hS hv).hom.app M := by
  subst hv
  rw [pullbackComparison_rfl, modulePullbackTriangle_rfl]
  rfl

/-- The canonical comparison of two inverse images of a module is the component of the natural
isomorphism `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparisonIso`. -/
theorem canonicalComparison_hom_eq_canonicalComparisonIso_hom_app {A Q R : AlgebraicSpaces B S hS}
    (r₀ : P ⟶ Q) (r₁ : P ⟶ R) (q₀ : Q ⟶ A) (q₁ : R ⟶ A) (w : r₀ ≫ q₀ = r₁ ≫ q₁)
    (M : Modules.{u, u} B S hS A.1 A.2) :
    (canonicalComparison r₀ r₁ q₀ q₁ w M).hom =
      (canonicalComparisonIso B S hS r₀ r₁ q₀ q₁ w).hom.app M :=
  (congrArg Iso.hom (canonicalComparisonIso_app B S hS r₀ r₁ q₀ q₁ w M)).symm

end Coherence

/-! ### Effectivity for the normalised restrictions -/

/-- **The comparison of the two restrictions of a quotient on a pairwise fibre product.**  If an
isomorphism `σ` carries the projection onto the restriction of the quotient by `K i` along the
first factor to the projection onto the restriction of the quotient by `K j` along the second,
both read on `aP^*F`, then it carries the inverse images of the two projections
`p i ^* a^* F ⟶ F_i/K i` and `p j ^* a^* F ⟶ F_j/K j` to each other through the canonical
comparison of the two inverse images of `a^*F`. -/
theorem modulePullback_map_quotient_comp_eq_pairComparison
    (hc : ModulePushforwardCoherence B S hS)
    {I : Type v} {X W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    (a : W ⟶ X) {aZ : ∀ i, Z i ⟶ X} (p : ∀ i, Z i ⟶ W) (hp : ∀ i, p i ≫ a = aZ i)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (K : ∀ i, Subobject ((modulePullback B S hS (aZ i)).obj F))
    (hP : ∀ i j, pairSnd B S hS Z p i j ≫ aZ j = pairFst B S hS Z p i j ≫ aZ i) (i j : I)
    (σ : (modulePullback B S hS (pairFst B S hS Z p i j)).obj (cokernel (K i).arrow) ≅
      (modulePullback B S hS (pairSnd B S hS Z p i j)).obj (cokernel (K j).arrow))
    (hσ : Functor.conjQuotientProjection
        (modulePullbackTriangle B S hS (rfl : pairFst B S hS Z p i j ≫ aZ i = _)) (K i) ≫
          σ.hom =
      Functor.conjQuotientProjection (modulePullbackTriangle B S hS (hP i j)) (K j)) :
    (modulePullback B S hS (pairFst B S hS Z p i j)).map
        ((pullbackComparison B S hS (p i) a (aZ i) (hp i) F).inv ≫ cokernel.π (K i).arrow) ≫
          σ.hom =
      (pairComparison B S hS Z p ((modulePullback B S hS a).obj F) i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Z p i j)).map
          ((pullbackComparison B S hS (p j) a (aZ j) (hp j) F).inv ≫ cokernel.π (K j).arrow) := by
  have hk₀ : (pairFst B S hS Z p i j ≫ p i) ≫ a = pairFst B S hS Z p i j ≫ aZ i := by
    rw [Category.assoc, hp i]
  have hk₁ : (pairSnd B S hS Z p i j ≫ p j) ≫ a = pairFst B S hS Z p i j ≫ aZ i := by
    rw [Category.assoc, hp j, hP i j]
  exact CategoryTheory.Iso.map_comp_hom_eq_hom_comp_map_of_whisker
    (modulePullbackTriangle B S hS (rfl : pairFst B S hS Z p i j ≫ aZ i = _))
    (modulePullbackTriangle B S hS (hP i j))
    (modulePullbackTriangle B S hS (hp i)) (modulePullbackTriangle B S hS (hp j))
    (modulePullbackTriangle B S hS hk₀) (modulePullbackTriangle B S hS hk₁)
    (modulePullbackTriangle B S hS
      (rfl : pairFst B S hS Z p i j ≫ p i = pairFst B S hS Z p i j ≫ p i))
    (modulePullbackTriangle B S hS
      (rfl : pairSnd B S hS Z p i j ≫ p j = pairSnd B S hS Z p i j ≫ p j))
    (eqToIso (congrArg (modulePullback B S hS) (pair_condition B S hS Z p i j)))
    (canonicalComparisonIso B S hS (pairFst B S hS Z p i j) (pairSnd B S hS Z p i j)
      (p i) (p j) (pair_condition B S hS Z p i j))
    (hc.modulePullbackTriangle_comp rfl (hp i) rfl hk₀)
    (hc.modulePullbackTriangle_comp rfl (hp j) (hP i j) hk₁)
    (modulePullbackTriangle_trans_isoWhiskerLeft_eqToIso a (pair_condition B S hS Z p i j)
      hk₀ hk₁)
    (modulePullbackTriangle_rfl_trans_canonicalComparisonIso (pairFst B S hS Z p i j)
      (pairSnd B S hS Z p i j) (p i) (p j) (pair_condition B S hS Z p i j))
    F (pullbackComparison B S hS (p i) a (aZ i) (hp i) F)
    (pullbackComparison_hom_eq_modulePullbackTriangle_hom_app_of_eq (p i) a (aZ i) (hp i) F)
    (pullbackComparison B S hS (p j) a (aZ j) (hp j) F)
    (pullbackComparison_hom_eq_modulePullbackTriangle_hom_app_of_eq (p j) a (aZ j) (hp j) F)
    (pairComparison B S hS Z p ((modulePullback B S hS a).obj F) i j)
    (canonicalComparison_hom_eq_canonicalComparisonIso_hom_app (pairFst B S hS Z p i j)
      (pairSnd B S hS Z p i j) (p i) (p j) (pair_condition B S hS Z p i j)
      ((modulePullback B S hS a).obj F))
    (cokernel.π (K i).arrow) (cokernel.π (K j).arrow) σ hσ

/-- The kernel of an epimorphism `φ : a^*F ⟶ N` whose inverse image along `p` is the projection
onto `aZ^*F / K`, up to an isomorphism, restricts along `p` to `K`. -/
theorem quotientRestrictOver_kernelSubobject_eq {X W Z : AlgebraicSpaces B S hS} (a : W ⟶ X)
    {aZ : Z ⟶ X} (p : Z ⟶ W) (hp : p ≫ a = aZ) (F : Modules.{u, u} B S hS X.1 X.2)
    (K : Subobject ((modulePullback B S hS aZ).obj F)) {N : Modules.{u, u} B S hS W.1 W.2}
    (φ : (modulePullback B S hS a).obj F ⟶ N) [Epi φ]
    (e : (modulePullback B S hS p).obj N ≅ cokernel K.arrow)
    (hfac : (modulePullback B S hS p).map φ ≫ e.hom =
      (pullbackComparison B S hS p a aZ hp F).inv ≫ cokernel.π K.arrow) :
    quotientRestrictOver p hp F (kernelSubobject φ) = K := by
  have := Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS p)
  refine (Functor.conjSubobject_kernelSubobject_eq (modulePullbackTriangle B S hS hp) φ
    (cokernel.π K.arrow) e ?_).trans (kernelSubobject_cokernel_π K)
  rw [hfac, ← pullbackComparison_hom_eq_modulePullbackTriangle_hom_app_of_eq p a aZ hp F]
  exact Iso.hom_inv_id_assoc (pullbackComparison B S hS p a aZ hp F) _

/-- **The effectivity half of Stacks 08IU, for quotients of the inverse images of a
quasi-coherent module.**  Let `a : W ⟶ X`, let `F` be a quasi-coherent `𝒪_X`-module and let
`{p i : Z i ⟶ W}` be an fpqc covering with `p i ≫ a = aZ i`.  A family of quotients of the
`aZ i ^* F` with quasi-coherent quotient modules which agree on the pairwise fibre products is
the family of restrictions of a quotient of `a^*F` with quasi-coherent quotient module. -/
@[sga "1 VIII 1.8" "partial"]
theorem exists_quotientRestrictOver_eq_of_isFpqcCovering (hc : ModulePushforwardCoherence B S hS)
    {I : Type v} {X W : AlgebraicSpaces B S hS} {Z : I → AlgebraicSpaces B S hS}
    (a : W ⟶ X) {aZ : ∀ i, Z i ⟶ X} (p : ∀ i, Z i ⟶ W) (hp : ∀ i, p i ≫ a = aZ i)
    (hcov : IsFpqcCovering B S hS fun i ↦ (p i).hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (K : ∀ i, Subobject ((modulePullback B S hS (aZ i)).obj F))
    (hK : ∀ i, (cokernel (K i).arrow).IsQuasicoherentOnSite)
    (hcompat : ∀ i j, quotientRestrictOver (pairFst B S hS Z p i j) rfl F (K i) =
      quotientRestrictOver (pairSnd B S hS Z p i j)
        (by rw [← hp i, ← hp j, ← Category.assoc, ← Category.assoc,
          pair_condition B S hS Z p i j]) F (K j)) :
    ∃ K₀ : Subobject ((modulePullback B S hS a).obj F),
      (cokernel K₀.arrow).IsQuasicoherentOnSite ∧
        ∀ i, quotientRestrictOver (p i) (hp i) F K₀ = K i := by
  have hepi : ∀ {V V' : AlgebraicSpaces B S hS} (f : V ⟶ V'),
      (modulePullback B S hS f).PreservesEpimorphisms := fun f ↦
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS f)
  have hM : ((modulePullback B S hS a).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a F hF
  have hP : ∀ i j, pairSnd B S hS Z p i j ≫ aZ j = pairFst B S hS Z p i j ≫ aZ i := by
    intro i j
    rw [← hp i, ← hp j]
    simp only [← Category.assoc, pair_condition B S hS Z p i j]
  let π : ∀ i, (modulePullback B S hS (p i)).obj ((modulePullback B S hS a).obj F) ⟶
      cokernel (K i).arrow := fun i ↦
    (pullbackComparison B S hS (p i) a (aZ i) (hp i) F).inv ≫ cokernel.π (K i).arrow
  have hπ : ∀ i, Epi (π i) := fun i ↦
    epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) coequalizer.π_epi
  have hεepi : ∀ {Q : AlgebraicSpaces B S hS} (k : I) {r : Q ⟶ Z k} {aQ : Q ⟶ X}
      (hr : r ≫ aZ k = aQ),
      Epi (Functor.conjQuotientProjection (modulePullbackTriangle B S hS hr) (K k)) :=
    fun k r _ hr ↦ have := hepi r; Functor.epi_conjQuotientProjection _ _
  choose σ hσ using fun i j ↦
    have := hεepi i (rfl : pairFst B S hS Z p i j ≫ aZ i = _)
    have := hεepi j (hP i j)
    Abelian.exists_iso_of_kernelSubobject_eq
      (Functor.conjQuotientProjection
        (modulePullbackTriangle B S hS (rfl : pairFst B S hS Z p i j ≫ aZ i = _)) (K i))
      (Functor.conjQuotientProjection (modulePullbackTriangle B S hS (hP i j)) (K j))
      (hcompat i j)
  have hτ : ∀ i j, (modulePullback B S hS (pairFst B S hS Z p i j)).map (π i) ≫ (σ i j).hom =
      (pairComparison B S hS Z p ((modulePullback B S hS a).obj F) i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Z p i j)).map (π j) := fun i j ↦
    modulePullback_map_quotient_comp_eq_pairComparison hc a p hp F K hP i j (σ i j) (hσ i j)
  obtain ⟨N, hN, φ, e, hφ, hfac⟩ := exists_epi_of_isFpqcCovering B S hS Z p hcov
    ((modulePullback B S hS a).obj F) hM (fun i ↦ cokernel (K i).arrow) hK π hπ σ hτ
  refine ⟨kernelSubobject φ, SheafOfModules.IsQuasicoherentOnSite.of_iso
    (Abelian.cokernelKernelSubobjectIso φ).symm hN, fun i ↦ ?_⟩
  have := hφ
  exact quotientRestrictOver_kernelSubobject_eq a (p i) (hp i) F (K i) φ (e i) (hfac i)

/-! ### The quotients of Situation 082M along an fpqc covering of a test scheme -/

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- **A quotient of `F_T` is determined by its pullbacks along an fpqc covering of `T`**, with
no hypothesis on the quotient: the separatedness half of the proof of Stacks 082P. -/
theorem eq_of_quotientPullback_eq_of_isFpqcCovering {I : Type v} {T : SchemesOver D.Y}
    {U : I → SchemesOver D.Y} (g : ∀ i, U i ⟶ T)
    (hg : IsFpqcCovering B S hS fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom)
    {K K' : Subobject (D.baseChangeModule T)}
    (h : ∀ i, D.quotientPullback (g i) K = D.quotientPullback (g i) K') : K = K' :=
  eq_of_quotientRestrictOver_eq_of_isFpqcCovering (fun i ↦ D.relativeMap (g i))
    (fun i ↦ baseChangeMap_comp_projection D.f (g i)) (isFpqcCovering_baseChangeMap D.f g hg)
    D.F h

/-- **A compatible family of quasi-coherent quotients along an fpqc covering of a test scheme
descends**: the glueing half of the proof of Stacks 082P.  If the quotients of the `F_{U i}`
agree on the overlaps `U i ×_T U j`, they are the pullbacks of a quotient of `F_T` whose quotient
module is quasi-coherent. -/
@[sga "1 VIII 1.8" "partial"]
theorem exists_quotientPullback_eq_of_isFpqcCovering {I : Type v} {T : SchemesOver D.Y}
    {U : I → SchemesOver D.Y} (g : ∀ i, U i ⟶ T)
    (hg : IsFpqcCovering B S hS fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom)
    (K : ∀ i, Subobject (D.baseChangeModule (U i)))
    (hK : ∀ i, (D.quotientModule (U i) (K i)).IsQuasicoherentOnSite)
    (hcompat : ∀ i j, D.quotientPullback (D.toHomSituation.overlapTestFst (g i) (g j)) (K i) =
      D.quotientPullback (D.toHomSituation.overlapTestSnd (g i) (g j)) (K j)) :
    ∃ K₀ : Subobject (D.baseChangeModule T), (D.quotientModule T K₀).IsQuasicoherentOnSite ∧
      ∀ i, D.quotientPullback (g i) K₀ = K i := by
  refine exists_quotientRestrictOver_eq_of_isFpqcCovering (modulePushforwardCoherence B S hS)
    (D.sourceProjection T) (fun i ↦ D.relativeMap (g i))
    (fun i ↦ baseChangeMap_comp_projection D.f (g i)) (isFpqcCovering_baseChangeMap D.f g hg)
    D.F D.quasicoherent K hK fun i j ↦ ?_
  have hk₀ : D.toHomSituation.overlapTestComparison (g i) (g j) ≫
      baseChangeMap D.f (D.toHomSituation.overlapTestFst (g i) (g j)) =
        pairFst B S hS (fun i ↦ D.space (U i)) (fun i ↦ D.relativeMap (g i)) i j :=
    D.toHomSituation.overlapTestComparison_comp_baseChangeMap_fst (g i) (g j)
  have hk₁ : D.toHomSituation.overlapTestComparison (g i) (g j) ≫
      baseChangeMap D.f (D.toHomSituation.overlapTestSnd (g i) (g j)) =
        pairSnd B S hS (fun i ↦ D.space (U i)) (fun i ↦ D.relativeMap (g i)) i j :=
    D.toHomSituation.overlapTestComparison_comp_baseChangeMap_snd (g i) (g j)
  have h₁ : D.toHomSituation.overlapTestComparison (g i) (g j) ≫
      baseChangeProjection D.f (D.toHomSituation.overlapTest (g i) (g j)) =
        pairFst B S hS (fun i ↦ D.space (U i)) (fun i ↦ D.relativeMap (g i)) i j ≫
          baseChangeProjection D.f (U i) := by
    rw [← baseChangeMap_comp_projection D.f (D.toHomSituation.overlapTestFst (g i) (g j))]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ baseChangeProjection D.f (U i)) hk₀)
  refine (quotientRestrictOver_comp (modulePushforwardCoherence B S hS) hk₀
    (baseChangeMap_comp_projection D.f _) h₁ rfl D.F (K i)).symm.trans ?_
  refine Eq.trans ?_ (quotientRestrictOver_comp (modulePushforwardCoherence B S hS) hk₁
    (baseChangeMap_comp_projection D.f _) h₁ _ D.F (K j))
  exact congrArg (quotientRestrictOver _ h₁ D.F) (hcompat i j)

/-! ### The subfunctor of quotients cut out by a condition -/

/-- The subfunctor of the functor of quotients of Situation 082M cut out by a pullback-stable
condition on quotients: its value at a test scheme `T` is the set of quotients of `F_T`
satisfying the condition, and its action on a morphism of test schemes is pullback of
quotients. -/
def quotientSubfunctor (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T') :
    (SchemesOver D.Y)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Q T.unop
  map {_ _} m := ↾fun K ↦ ⟨D.quotientPullback m.unop K.1, hQ m.unop K.1 K.2⟩
  map_id T := congrArg TypeCat.ofHom (funext fun K ↦
    Subtype.ext (D.quotientPullback_id (modulePushforwardCoherence B S hS) T.unop K.1))
  map_comp m n := congrArg TypeCat.ofHom (funext fun K ↦
    Subtype.ext (D.quotientPullback_comp (modulePushforwardCoherence B S hS)
      n.unop m.unop K.1))

/-- The functor of quotients of Stacks 082N is the subfunctor cut out by its condition. -/
theorem quotientsFunctor_eq_quotientSubfunctor :
    D.quotientsFunctor = D.quotientSubfunctor D.quotients
      (fun m K hK ↦ D.quotientPullback_mem_quotients' m K hK) :=
  rfl

/-- The finite-presentation functor of quotients of Stacks 0CZL is the subfunctor cut out by its
condition. -/
theorem finitePresentationQuotientsFunctor_eq_quotientSubfunctor :
    D.finitePresentationQuotientsFunctor = D.quotientSubfunctor D.finitePresentationQuotients
      (fun m K hK ↦ D.quotientPullback_mem_finitePresentationQuotients m K hK) :=
  rfl

/-- **The sheaf condition for the presieve of an fpqc covering of a test scheme.**  The
subfunctor of quotients cut out by a pullback-stable condition `Q` satisfies the sheaf condition
for the presieve generated by an fpqc covering `{g i : U i ⟶ T}` of test schemes, as soon as the
quotients satisfying `Q` are quasi-coherent and `Q` descends along the covering: a quotient of
`F_T` with quasi-coherent quotient module all of whose pullbacks satisfy `Q` satisfies `Q`.

The amalgamation is
`AlgebraicGeometry.Space.QuotientSituation.exists_quotientPullback_eq_of_isFpqcCovering`, fed the
compatibility of the family on the overlaps `U i ×_T U j`, and its uniqueness is
`AlgebraicGeometry.Space.QuotientSituation.eq_of_quotientPullback_eq_of_isFpqcCovering`. -/
@[sga "1 VIII 1.8" "more general"]
theorem isSheafFor_quotientSubfunctor
    (Q : ∀ T : SchemesOver D.Y, Set (Subobject (D.baseChangeModule T)))
    (hQ : ∀ {T' T : SchemesOver D.Y} (m : T' ⟶ T) (K : Subobject (D.baseChangeModule T)),
      K ∈ Q T → D.quotientPullback m K ∈ Q T')
    (hQqc : ∀ (T : SchemesOver D.Y) (K : Subobject (D.baseChangeModule T)), K ∈ Q T →
      (D.quotientModule T K).IsQuasicoherentOnSite)
    {I : Type v} {T : SchemesOver D.Y} {U : I → SchemesOver D.Y} (g : ∀ i, U i ⟶ T)
    (hg : IsFpqcCovering B S hS fun i ↦ ((schemeSpaceFunctor B S hS).map (g i).left).hom)
    (hdesc : ∀ K₀ : Subobject (D.baseChangeModule T),
      (D.quotientModule T K₀).IsQuasicoherentOnSite →
        (∀ i, D.quotientPullback (g i) K₀ ∈ Q (U i)) → K₀ ∈ Q T) :
    Presieve.IsSheafFor (D.quotientSubfunctor Q hQ) (Presieve.ofArrows U g) := by
  intro x hx
  set K : ∀ i, Subobject (D.baseChangeModule (U i)) := fun i ↦
    (x (g i) (Presieve.ofArrows.mk i)).1 with hKdef
  have hKmem : ∀ i, K i ∈ Q (U i) := fun i ↦ (x (g i) (Presieve.ofArrows.mk i)).2
  have hcompat : ∀ i j,
      D.quotientPullback (D.toHomSituation.overlapTestFst (g i) (g j)) (K i) =
        D.quotientPullback (D.toHomSituation.overlapTestSnd (g i) (g j)) (K j) := fun i j ↦
    congrArg Subtype.val (hx (D.toHomSituation.overlapTestFst (g i) (g j))
      (D.toHomSituation.overlapTestSnd (g i) (g j)) (Presieve.ofArrows.mk i)
      (Presieve.ofArrows.mk j) (D.toHomSituation.overlapTest_condition (g i) (g j)))
  obtain ⟨K₀, hK₀qc, hK₀⟩ := D.exists_quotientPullback_eq_of_isFpqcCovering g hg K
    (fun i ↦ hQqc _ _ (hKmem i)) hcompat
  have hK₀mem : K₀ ∈ Q T := hdesc K₀ hK₀qc fun i ↦ (hK₀ i).symm ▸ hKmem i
  refine ⟨⟨K₀, hK₀mem⟩, ?_, fun t ht ↦ ?_⟩
  · rintro _ _ ⟨i⟩
    exact Subtype.ext (hK₀ i)
  · refine Subtype.ext (D.eq_of_quotientPullback_eq_of_isFpqcCovering g hg fun i ↦ ?_)
    exact (congrArg Subtype.val (ht (g i) (Presieve.ofArrows.mk i))).trans (hK₀ i).symm

end QuotientSituation

end AlgebraicGeometry.Space

end
