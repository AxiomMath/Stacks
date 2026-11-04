module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSectionsSheafified
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineTildeStalkCoherence

/-!
# The morphism factor of the chart comparison of Stacks 0DJ8, at a point of `U'`

For a base change chart `ch`, a complex `K` with quasi-coherent cohomology sheaves and a point `y`
of `Spec 𝒪_{X'}(U')`, the derived stalk at `y` of
`AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeTildeMap`, followed by the derived-pullback
stalk comparison of Stacks 0098 for `U' ⟶ X'`, is the identification at `U` given by
`AlgebraicGeometry.derivedStalkAffineSectionsIso`, together with the merges of the germ extensions
of scalars. Neither side contains a Spec–Γ unit or counit.

## Main results

* `StacksDraft.MorphismMatchChase`: equations between composites in a category, and their images
  under a functor, stated with every object and morphism a variable.
* `AlgebraicGeometry.derivedPullbackStalkCompIso_hom_app_comp`: the two-step derived stalk
  computation as the derived stalk of the Stacks 0D5S composition isomorphism followed by the
  one-step computation.
* `AlgebraicGeometry.derivedPullbackStalkIso_eqToHom_congr`: the stalk formula of Stacks 0098
  transported along an equality of morphisms of schemes.
* `AlgebraicGeometry.derivedAffineTildeStalk_inv_comp`: the affine coherence with the affine
  comparison square read backwards and the two germ extensions of scalars kept apart.
* `AlgebraicGeometry.BaseChangeChart.derivedStalk_sectionsBaseChangeTildeMap_comp`: **the
  morphism factor of the chart comparison at a point of `U'`.**
* `AlgebraicGeometry.BaseChangeChart.extendScalars_map_sectionsBaseChangeMap_eq`: the same with
  both Spec–Γ factors and Stacks 01HV at `𝒪_{X'}(U')` cancelled — the germ-localized chart
  identification of Stacks 0DJ8 (2) read as the derived-pullback stalk comparison of
  Stacks 0098 at `ch.incU' y`, through `AlgebraicGeometry.derivedStalkAffineSectionsIso` at `U`
  and at `U'`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open StacksDraft.DerivedExtensionScalarsComp

universe u

namespace StacksDraft.MorphismMatchChase

variable {C : Type*} [Category* C]

/-- A functor applied to a six-fold composite. -/
public theorem map_comp6 {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : D} (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃)
    (f₄ : a₃ ⟶ a₄) (f₅ : a₄ ⟶ a₅) (f₆ : a₅ ⟶ a₆) :
    F.map (f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆) =
      F.map f₁ ≫ F.map f₂ ≫ F.map f₃ ≫ F.map f₄ ≫ F.map f₅ ≫ F.map f₆ := by
  simp only [Functor.map_comp]

/-- A functor applied to an identity, absorbed into the composite that follows it. -/
public theorem map_id_comp {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E) {a : D}
    {Z : E} (w : F.obj a ⟶ Z) : F.map (𝟙 a) ≫ w = w := by
  rw [F.map_id, Category.id_comp]

/-- **The sixth factor of a six-fold composite of images cancelled against its inverse.** -/
public theorem comp6_cancel_sixth {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a₀ a₁ a₂ a₃ a₄ a₅ a₆ : D} (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (f₃ : a₂ ⟶ a₃)
    (f₄ : a₃ ⟶ a₄) (f₅ : a₄ ⟶ a₅) (f₆ : a₅ ⟶ a₆) (t : a₆ ⟶ a₅) (hft : f₆ ≫ t = 𝟙 a₅)
    {Z : E} (W : F.obj a₆ ⟶ Z) (w : F.obj a₅ ⟶ Z) (hW : W = F.map t ≫ w) :
    (F.map f₁ ≫ F.map f₂ ≫ F.map f₃ ≫ F.map f₄ ≫ F.map f₅ ≫ F.map f₆) ≫ W =
      F.map f₁ ≫ F.map f₂ ≫ F.map f₃ ≫ F.map f₄ ≫ F.map f₅ ≫ w := by
  subst hW
  have h6 : ∀ {Z' : E} (v : F.obj a₅ ⟶ Z'), F.map f₆ ≫ F.map t ≫ v = v := by
    intro Z' v
    rw [← Category.assoc, ← F.map_comp, hft, F.map_id, Category.id_comp]
  simp only [Category.assoc, h6]

/-- Replacing the fifth factor of a five-fold composite. -/
public theorem comp5_congr_fifth {A B D₁ D₂ D₃ D₄ : C} (p : A ⟶ B) (q : B ⟶ D₁) (r : D₁ ⟶ D₂)
    (s : D₂ ⟶ D₃) (t t' : D₃ ⟶ D₄) (h : t = t') : p ≫ q ≫ r ≫ s ≫ t = p ≫ q ≫ r ≫ s ≫ t' := by
  rw [h]

/-- Splitting the fourth and fifth factors of a six-fold composite into three. -/
public theorem comp_split_45 {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₁ B₂ : C} (p : A₀ ⟶ A₁) (q : A₁ ⟶ A₂)
    (r : A₂ ⟶ A₃) (s : A₃ ⟶ A₄) (t : A₄ ⟶ A₅) (u : A₅ ⟶ A₆)
    (m₁ : A₃ ⟶ B₁) (m₂ : B₁ ⟶ B₂) (m₃ : B₂ ⟶ A₅) (h : m₁ ≫ m₂ ≫ m₃ = s ≫ t) :
    p ≫ q ≫ r ≫ s ≫ t ≫ u = p ≫ q ≫ r ≫ m₁ ≫ m₂ ≫ m₃ ≫ u := by
  rw [← Category.assoc s t u, ← h, Category.assoc m₁ (m₂ ≫ m₃) u, Category.assoc m₂ m₃ u]

/-- **Two adjacent factors of a six-fold composite replaced by two others.** -/
public theorem comp6_congr_23 {A₀ A₁ A₂ A₃ A₄ A₅ B₁ : C} (p : A₀ ⟶ A₁) {q : A₁ ⟶ A₂}
    {r : A₂ ⟶ A₃} (s : A₃ ⟶ A₄) (t : A₄ ⟶ A₅) {v₁ : A₁ ⟶ B₁} {v₂ : B₁ ⟶ A₃}
    (h : q ≫ r = v₁ ≫ v₂) : p ≫ q ≫ r ≫ s ≫ t = p ≫ v₁ ≫ v₂ ≫ s ≫ t := by
  rw [← Category.assoc q r, h, Category.assoc]

/-- A four-fold composite with its first two factors bracketed. -/
public theorem comp4_assoc22 {A B D₁ D₂ D₃ : C} (p : A ⟶ B) (q : B ⟶ D₁) (r : D₁ ⟶ D₂)
    (s : D₂ ⟶ D₃) : p ≫ q ≫ r ≫ s = (p ≫ q) ≫ r ≫ s :=
  (Category.assoc p q (r ≫ s)).symm

/-- A functor carries a pair of mutually inverse morphisms to one. -/
public theorem map_comp_eq_id {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E) {a b : D}
    (p : a ⟶ b) (q : b ⟶ a) (h : p ≫ q = 𝟙 a) : F.map p ≫ F.map q = 𝟙 (F.obj a) := by
  rw [← F.map_comp, h, F.map_id]

/-- **An equation read with one isomorphism and a two-step isomorphism backwards**, with every
isomorphism given as a morphism together with the equation inverting it. -/
public theorem inv_comp_eq_comp_two_inv {X₀ X₁ X₂ X₃ X₄ P₁ : C}
    (ah : X₀ ⟶ X₁) (ai : X₁ ⟶ X₀) (ha : ai ≫ ah = 𝟙 X₁) (x : X₀ ⟶ X₂)
    (r₁ : X₂ ⟶ X₃) (r₁' : X₃ ⟶ X₂) (hr₁ : r₁ ≫ r₁' = 𝟙 X₂)
    (r₂ : X₃ ⟶ X₄) (r₂' : X₄ ⟶ X₃) (hr₂ : r₂ ≫ r₂' = 𝟙 X₃)
    (y₁ : X₁ ⟶ P₁) (y₂ : P₁ ⟶ X₄) (h : ah ≫ y₁ ≫ y₂ = x ≫ r₁ ≫ r₂) :
    ai ≫ x = y₁ ≫ y₂ ≫ r₂' ≫ r₁' := by
  rw [← (reassoc_of% ha) (y₁ ≫ y₂ ≫ r₂' ≫ r₁'), reassoc_of% h, reassoc_of% hr₂, hr₁,
    Category.comp_id]

/-- A functor carries an equation naming a composite to the equation between the images. -/
public theorem map_comp_of_eq {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a b d : D} (p : a ⟶ b) (q : b ⟶ d) (m : a ⟶ d) (h : p ≫ q = m) :
    F.map p ≫ F.map q = F.map m := by
  rw [← F.map_comp, h]

/-- Two factors merged under a functor and the result matched against a two-fold composite. -/
public theorem map_comp2_comp_eq {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a b d : D} (p : a ⟶ b) (q : b ⟶ d) (m : a ⟶ d) (hm : p ≫ q = m)
    {Z B₁ : E} (k : F.obj d ⟶ Z) (v₁ : F.obj a ⟶ B₁) (v₂ : B₁ ⟶ Z)
    (h : F.map m ≫ k = v₁ ≫ v₂) :
    F.map p ≫ F.map q ≫ k = v₁ ≫ v₂ := by
  rw [← Category.assoc, ← F.map_comp, hm, h]

/-- **Two factors under a functor split off an isomorphism's inverse.** -/
public theorem map_comp_split_of_inv {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {A B D₁ D₂ : D} (w₀ : A ⟶ B) (wi : B ⟶ A) (hw : wi ≫ w₀ = 𝟙 B) (m : B ⟶ D₁)
    (n : D₁ ⟶ D₂) (I : A ⟶ D₂) (hI : I = w₀ ≫ m ≫ n) :
    F.map m ≫ F.map n = F.map wi ≫ F.map I := by
  rw [hI, ← F.map_comp, ← F.map_comp, reassoc_of% hw]

/-- Replacing the third and fourth factors of a six-fold composite. -/
public theorem comp6_congr_34 {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₁ : C} (p : A₀ ⟶ A₁) (q : A₁ ⟶ A₂)
    {r : A₂ ⟶ A₃} {s : A₃ ⟶ A₄} (t : A₄ ⟶ A₅) (u : A₅ ⟶ A₆)
    {w₁ : A₂ ⟶ B₁} {w₂ : B₁ ⟶ A₄} (h : r ≫ s = w₁ ≫ w₂) :
    p ≫ q ≫ r ≫ s ≫ t ≫ u = p ≫ q ≫ w₁ ≫ w₂ ≫ t ≫ u := by
  rw [reassoc_of% h]

/-- Replacing the second, third and fourth factors of a seven-fold composite by two. -/
public theorem comp7_congr_234 {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ B₁ : C} (p : A₀ ⟶ A₁) {q : A₁ ⟶ A₂}
    {r : A₂ ⟶ A₃} {s : A₃ ⟶ A₄} (t : A₄ ⟶ A₅) (u : A₅ ⟶ A₆) (v : A₆ ⟶ A₇)
    {w₁ : A₁ ⟶ B₁} {w₂ : B₁ ⟶ A₄} (h : q ≫ r ≫ s = w₁ ≫ w₂) :
    p ≫ q ≫ r ≫ s ≫ t ≫ u ≫ v = p ≫ w₁ ≫ w₂ ≫ t ≫ u ≫ v := by
  rw [reassoc_of% h]

/-- A three-fold composite known to be a four-fold one, with a common tail. -/
public theorem comp3_eq_comp4_tail {A₀ A₁ A₂ A₃ B₁ B₂ B₃ Z : C} {p : A₀ ⟶ A₁} {q : A₁ ⟶ A₂}
    {r : A₂ ⟶ A₃} {s₁ : A₀ ⟶ B₁} {s₂ : B₁ ⟶ B₂} {s₃ : B₂ ⟶ B₃} {s₄ : B₃ ⟶ A₃}
    (h : p ≫ q ≫ r = s₁ ≫ s₂ ≫ s₃ ≫ s₄) (k : A₃ ⟶ Z) :
    p ≫ q ≫ r ≫ k = s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ k := by
  rw [reassoc_of% h]

/-- A two-fold composite known to be a three-fold one, with a common two-factor tail. -/
public theorem comp2_eq_comp3_tail2 {A₀ A₁ A₂ B₁ B₂ Z₁ Z₂ : C} {p : A₀ ⟶ A₁} {q : A₁ ⟶ A₂}
    {a : A₀ ⟶ B₁} {b : B₁ ⟶ B₂} {c : B₂ ⟶ A₂} (h : p ≫ q = a ≫ b ≫ c) (d : A₂ ⟶ Z₁)
    (e : Z₁ ⟶ Z₂) : p ≫ q ≫ d ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  rw [reassoc_of% h]

/-- A head factor cancelled against the inverse that follows it. -/
public theorem cancel_head {X₀ X₁ : C} (ah : X₀ ⟶ X₁) (ai : X₁ ⟶ X₀) (h : ah ≫ ai = 𝟙 X₀)
    {Z : C} (w : X₀ ⟶ Z) : ah ≫ ai ≫ w = w := by
  rw [← Category.assoc, h, Category.id_comp]

/-- **A transport of functors, applied at an object, undone by the transport of the object.** -/
public theorem eqToHom_app_comp_eqToHom {D E : Type*} [Category* D] [Category* E]
    {I : Type*} (F : I → (D ⥤ E)) {i j : I} (h : i = j) (N : D) :
    (eqToHom (congrArg F h)).app N ≫ eqToHom (congrArg (fun k => (F k).obj N) h.symm) =
      𝟙 ((F i).obj N) := by
  subst h
  simp

end StacksDraft.MorphismMatchChase

namespace AlgebraicGeometry

/-- The two-step derived stalk computation of an iterated derived pullback, as the derived stalk
of the composition isomorphism of Tag 0D5S followed by the one-step computation. -/
public theorem derivedPullbackStalkCompIso_hom_app_comp {Z₁ Z₂ Z₃ : Scheme.{u}}
    (p : Z₁ ⟶ Z₂) (q : Z₂ ⟶ Z₃) (z : Z₁) (K : DerivedCategory Z₃.Modules) :
    (derivedPullbackStalkCompIsoGeneral p q z).hom.app K =
      (derivedStalkFunctor z).map ((Stacks.Duality.derivedPullbackCompIso p q).hom.app K) ≫
        (derivedPullbackStalkIso (p ≫ q) z).hom.app K := by
  rw [derivedPullbackStalkCompIso_eq_general]
  rfl

/-- **The derived stalk formula of Stacks 0098 transported along an equality of morphisms.** -/
public theorem derivedPullbackStalkIso_eqToHom_congr {Z W : Scheme.{u}} {t t' : Z ⟶ W}
    (h : t = t') (y : Z) (K : DerivedCategory W.Modules) :
    (derivedStalkFunctor y).map (eqToHom (congrArg
          (fun s : Z ⟶ W => (Stacks.Duality.derivedPullback s).obj K) h)) ≫
        (derivedPullbackStalkIso t' y).hom.app K =
      (derivedPullbackStalkIso t y).hom.app K ≫ eqToHom (congrArg
        (fun s : Z ⟶ W =>
          (totalDerivedExtensionScalars.{u, u, u} (s.stalkMap y).hom).functor.obj
            ((derivedStalkFunctor (s y)).obj K)) h) := by
  subst h
  simp only [eqToHom_refl, Category.comp_id]
  exact StacksDraft.MorphismMatchChase.map_id_comp _ _

/-- **The affine Tag 0098 / Tag 08DW coherence, read with the affine comparison square and the
merge of the two extensions of scalars backwards.** This is
`AlgebraicGeometry.derivedAffineTildeStalkLeft_eq_right` with the inverse of the affine
comparison square on the left and the two germ extensions of scalars kept apart on the right. -/
public theorem derivedAffineTildeStalk_inv_comp {A A' : CommRingCat.{u}} (c : A ⟶ A')
    (y : Spec A') (N : DerivedCategory (ModuleCat.{u} A)) :
    (derivedStalkFunctor y).map ((affinePullbackComparison A A' c).inv.app N) ≫
        (derivedPullbackStalkIso (Spec.map c) y).hom.app
          ((tilde.functor A).mapDerivedCategory.obj N) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((Spec.map c).stalkMap y).hom).functor.map
          ((derivedTildeStalkIso A ((Spec.map c) y)).inv.app N) =
      (derivedTildeStalkIso A' y).inv.app
          ((totalDerivedExtensionScalars.{u, u, u} c.hom).functor.obj N) ≫
        (derivedExtensionScalarsCompIsoGeneral c.hom (specGermRingHom A' y)).hom.app N ≫
        eqToHom (congrArg
          (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj N)
          (specGermRingHom_stalkMap c y).symm) ≫
        (derivedExtensionScalarsCompIsoGeneral (specGermRingHom A ((Spec.map c) y))
            ((Spec.map c).stalkMap y).hom).inv.app N := by
  have hE := (((derivedAffineTildeStalkLeft_app c y N).symm.trans
    (congrArg (fun α => α.app N) (derivedAffineTildeStalkLeft_eq_right c y))).trans
      (derivedAffineTildeStalkRight_app c y N)).trans
    (StacksDraft.MorphismMatchChase.comp4_assoc22 _ _ _ _)
  exact StacksDraft.MorphismMatchChase.inv_comp_eq_comp_two_inv
    ((derivedStalkFunctor y).map ((affinePullbackComparison A A' c).hom.app N))
    ((derivedStalkFunctor y).map ((affinePullbackComparison A A' c).inv.app N))
    (StacksDraft.MorphismMatchChase.map_comp_eq_id (derivedStalkFunctor y) _ _
      ((affinePullbackComparison A A' c).inv_hom_id_app N))
    _ _ _
    ((derivedExtensionScalarsCompIsoGeneral (specGermRingHom A ((Spec.map c) y))
      ((Spec.map c).stalkMap y).hom).hom_inv_id_app N)
    _ _
    (StacksDraft.MorphismMatchChase.eqToHom_app_comp_eqToHom
      (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor)
      (specGermRingHom_stalkMap c y) N)
    _ _ hE

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The morphism factor of the chart comparison of Stacks 0DJ8, at a point of `U'`.** The
derived stalk at `y` of the chart's tilde-level identification
`AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeTildeMap`, followed by the derived-pullback
stalk comparison for `U' ⟶ X'`, is the derived stalk at `y` of `RΓ(U, K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U')`
read through `AlgebraicGeometry.derivedStalkAffineSectionsIso` at `U`: Stacks 01HV at
`𝒪_{X'}(U')` and the merge of the two germ extensions of scalars on the source side, the
localization of `RΓ(U,K)` at the point of `Spec 𝒪_X(U)` and the merge of the two germ maps along
`Spec ch.c ≫ ch.incU` on the target side. -/
public theorem derivedStalk_sectionsBaseChangeTildeMap_comp (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (y : Spec ch.A') :
    (derivedStalkFunctor y).map (ch.sectionsBaseChangeTildeMap K) ≫
        (derivedPullbackStalkCompIsoGeneral ch.incU' g' y).hom.app K =
      (derivedTildeStalkIso ch.A' y).inv.app
          ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
            ((affineDerivedSections ch.incU).obj K)) ≫
        (derivedExtensionScalarsCompIsoGeneral ch.c.hom (specGermRingHom ch.A' y)).hom.app
          ((affineDerivedSections ch.incU).obj K) ≫
        eqToHom (congrArg
          (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj
            ((affineDerivedSections ch.incU).obj K))
          (specGermRingHom_stalkMap ch.c y).symm) ≫
        (derivedExtensionScalarsCompIsoGeneral (specGermRingHom ch.A (Spec.map ch.c y))
            ((Spec.map ch.c).stalkMap y).hom).inv.app
          ((affineDerivedSections ch.incU).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((Spec.map ch.c).stalkMap y).hom).functor.map
          ((derivedStalkAffineSectionsIso ch.incU (Spec.map ch.c y) K hK).hom) ≫
        (derivedStalkExtensionCompIsoGeneral (Spec.map ch.c) ch.incU y).hom.app
          ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K) ≫
        eqToHom (congrArg
          (fun t : Spec ch.A' ⟶ X =>
            (totalDerivedExtensionScalars.{u, u, u} (t.stalkMap y).hom).functor.obj
              ((derivedStalkFunctor (t y)).obj K))
          ch.wU'U.symm) := by
  dsimp only [sectionsBaseChangeTildeMap]
  rw [StacksDraft.MorphismMatchChase.map_comp6]
  have hψ : (derivedTildeCompι ch.A).inv.app ((affineDerivedSections ch.incU).obj K) ≫
      (derivedTildeGlobalSectionsAdjunction ch.A).val.counit.app
        ((Stacks.Duality.derivedPullback ch.incU).obj K) =
      (tildeDerivedSectionsIso ch.incU K hK).hom := rfl
  refine Eq.trans (StacksDraft.MorphismMatchChase.comp6_cancel_sixth (derivedStalkFunctor y)
    _ _ _ _ _ _ ((Stacks.Duality.derivedPullbackCompIso ch.incU' g').hom.app K)
    ((Stacks.Duality.derivedPullbackCompIso ch.incU' g').inv_hom_id_app K) _ _
    (derivedPullbackStalkCompIso_hom_app_comp ch.incU' g' y K)) ?_
  refine Eq.trans (StacksDraft.MorphismMatchChase.comp5_congr_fifth _ _ _ _ _ _
    (derivedPullbackStalkIso_eqToHom_congr ch.wU'U.symm y K)) ?_
  refine Eq.trans (StacksDraft.MorphismMatchChase.comp_split_45 _ _ _ _ _ _ _ _ _
    ((derivedPullbackStalkCompIso_hom_app_general (Spec.map ch.c) ch.incU y K).symm.trans
      (derivedPullbackStalkCompIso_hom_app_comp (Spec.map ch.c) ch.incU y K))) ?_
  refine Eq.trans (StacksDraft.MorphismMatchChase.comp7_congr_234 _ _ _ _
    (StacksDraft.MorphismMatchChase.map_comp2_comp_eq (derivedStalkFunctor y) _ _ _
      (StacksDraft.MorphismMatchChase.map_comp_of_eq
        (Stacks.Duality.derivedPullback (Spec.map ch.c)) _ _ _ hψ) _ _ _
      ((derivedPullbackStalkIso (Spec.map ch.c) y).hom.naturality
        (tildeDerivedSectionsIso ch.incU K hK).hom))) ?_
  refine Eq.trans (StacksDraft.MorphismMatchChase.comp6_congr_34 _ _ _ _
    (StacksDraft.MorphismMatchChase.map_comp_split_of_inv
      (totalDerivedExtensionScalars.{u, u, u} ((Spec.map ch.c).stalkMap y).hom).functor
      ((derivedTildeStalkIso ch.A (Spec.map ch.c y)).hom.app
        ((affineDerivedSections ch.incU).obj K))
      ((derivedTildeStalkIso ch.A (Spec.map ch.c y)).inv.app
        ((affineDerivedSections ch.incU).obj K))
      ((derivedTildeStalkIso ch.A (Spec.map ch.c y)).inv_hom_id_app _) _ _ _
      (derivedStalkAffineSectionsIso_hom ch.incU (Spec.map ch.c y) K hK))) ?_
  exact StacksDraft.MorphismMatchChase.comp3_eq_comp4_tail
    (derivedAffineTildeStalk_inv_comp ch.c y ((affineDerivedSections ch.incU).obj K)) _

/-- **The germ-localized chart identification of Stacks 0DJ8 (2) is the derived-pullback stalk
comparison of Stacks 0098.** The chart's identification
`RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U') ⟶ RΓ(U', L(g')^*K)`, base changed along the germ map at `y` and
read through `AlgebraicGeometry.derivedStalkAffineSectionsIso` at `U'` and then along the stalk
comparison for `g'` at `ch.incU' y`, is the identification at `U` — the germ localization of
`RΓ(U,K)` at the point of `Spec 𝒪_X(U)` — with the two germ extensions of scalars merged on each
side. -/
public theorem extendScalars_map_sectionsBaseChangeMap_eq (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      ((Stacks.Duality.derivedPullback g').obj K)).IsQuasicoherent) (y : Spec ch.A') :
    (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom ch.A' y)).functor.map
          (ch.sectionsBaseChangeMap K) ≫
        (derivedStalkAffineSectionsIso ch.incU' y
          ((Stacks.Duality.derivedPullback g').obj K) hK').hom ≫
        (totalDerivedExtensionScalars.{u, u, u} (ch.incU'.stalkMap y).hom).functor.map
          ((derivedPullbackStalkIso g' (ch.incU' y)).hom.app K) ≫
        (derivedStalkExtensionCompIsoGeneral ch.incU' g' y).hom.app
          ((derivedStalkFunctor (g' (ch.incU' y))).obj K) =
      (derivedExtensionScalarsCompIsoGeneral ch.c.hom (specGermRingHom ch.A' y)).hom.app
          ((affineDerivedSections ch.incU).obj K) ≫
        eqToHom (congrArg
          (fun ψ => (totalDerivedExtensionScalars.{u, u, u} ψ).functor.obj
            ((affineDerivedSections ch.incU).obj K))
          (specGermRingHom_stalkMap ch.c y).symm) ≫
        (derivedExtensionScalarsCompIsoGeneral (specGermRingHom ch.A (Spec.map ch.c y))
            ((Spec.map ch.c).stalkMap y).hom).inv.app
          ((affineDerivedSections ch.incU).obj K) ≫
        (totalDerivedExtensionScalars.{u, u, u} ((Spec.map ch.c).stalkMap y).hom).functor.map
          ((derivedStalkAffineSectionsIso ch.incU (Spec.map ch.c y) K hK).hom) ≫
        (derivedStalkExtensionCompIsoGeneral (Spec.map ch.c) ch.incU y).hom.app
          ((derivedStalkFunctor (ch.incU (Spec.map ch.c y))).obj K) ≫
        eqToHom (congrArg
          (fun t : Spec ch.A' ⟶ X =>
            (totalDerivedExtensionScalars.{u, u, u} (t.stalkMap y).hom).functor.obj
              ((derivedStalkFunctor (t y)).obj K))
          ch.wU'U.symm) := by
  refine Eq.trans (StacksDraft.MorphismMatchChase.comp2_eq_comp3_tail2
    (ch.extendScalars_map_sectionsBaseChangeMap_comp K hK' y) _ _) ?_
  refine Eq.trans (StacksDraft.CompositionChase.comp3_congr_third _ _ _ _
    (derivedPullbackStalkCompIso_hom_app_general ch.incU' g' y K).symm) ?_
  refine Eq.trans (congrArg (fun z => (derivedTildeStalkIso ch.A' y).hom.app
      ((totalDerivedExtensionScalars.{u, u, u} ch.c.hom).functor.obj
        ((affineDerivedSections ch.incU).obj K)) ≫ z)
    (ch.derivedStalk_sectionsBaseChangeTildeMap_comp K hK y)) ?_
  exact StacksDraft.MorphismMatchChase.cancel_head _ _
    ((derivedTildeStalkIso ch.A' y).hom_inv_id_app _) _

end BaseChangeChart

end AlgebraicGeometry

end
