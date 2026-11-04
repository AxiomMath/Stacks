module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.ValuativeCriterionRefined
public import StacksCore.Tactic.StacksAttribute

/-!
# Valuative lifts for compactifications

Nagata's compactification theorem is proved by exhibiting, for a quasi-compact open immersion
`U ⟶ W` over a base `S`, enough valuative lifts for the structure morphism `W ⟶ S` that the
refined valuative criterion makes it proper. This file collects the lift-transport lemmas used
in that argument, together with the two statements that turn a supply of valuative lifts into a
quasi-compact compactification of `U` over `S`.

## Main results

* `Stacks.Compactification.valuativeLift_of_proper_common_chart` transports a valuative lift
  along a proper morphism `b : X' ⟶ X` into a common model `W`.
* `Stacks.Compactification.valuativeUnique_of_two_proper_common_charts` upgrades a choice of
  limit in one of two proper charts into a *unique* lift for a separated common model.
* `Stacks.Compactification.valuativeMap_lift_open_of_closedPoint_mem` factors a morphism out of
  the spectrum of a local ring through an open containing the image of the closed point.
* `Stacks.Compactification.valuativeLift_of_proper_open_chart`,
  `Stacks.Compactification.valuativeLift_of_proper_open_chart_to_common_model` and
  `Stacks.Compactification.valuativeLift_of_chosen_proper_limit_to_common_model` produce lifts
  from a proper chart whose chosen limit stays inside a trimmed open.
* `Stacks.Compactification.exists_factor_closedImmersion_of_schemeTheoreticallyDominant` and
  `Stacks.Compactification.schemeTheoreticallyDominant_genericOfValuativeCommSq` give the
  scheme-theoretic image input: the generic fibre of a valuative square is
  scheme-theoretically dominant, so a factorisation through a closed immersion extends.
* `Stacks.Compactification.valuative_map_factors_through_image`,
  `Stacks.Compactification.valuative_pair_factors_through_image` and
  `Stacks.Compactification.valuative_pair_not_in_disjoint_image_boundaries` move a pair of
  valuation limits into a scheme-theoretic image and rule out two simultaneously bad limits.
* `Stacks.Compactification.exists_compactification_of_dense_open_valuative` and
  `Stacks.Compactification.exists_compactification_of_valuative_ambient` build a quasi-compact
  `AlgebraicGeometry.CompactificationOf (Over.mk fU)` out of a supply of valuative lifts, the
  second one without assuming that the chosen open is dense in the ambient scheme.

## Implementation notes

All the lift-transport lemmas work with `AlgebraicGeometry.ValuativeCommSq`, so transporting a
lift means building an auxiliary square with the same valuation ring and fraction field and a
rearranged pair of maps, then applying the valuative criterion of the relevant proper morphism
through `AlgebraicGeometry.IsProper.eq_valuativeCriterion`.

`exists_compactification_of_dense_open_valuative` needs the ambient open to be dense, since the
refined valuative criterion `AlgebraicGeometry.universallyClosed_of_unique_lift_of_denseRange`
asks for a dense quasi-compact morphism. `exists_compactification_of_valuative_ambient` removes
that hypothesis by first replacing the ambient scheme with the scheme-theoretic image of the
open immersion: the open immersion is dominant onto its image, and a lift in the ambient scheme
descends to the image because the generic fibre of a valuative square is scheme-theoretically
dominant and the image inclusion is a closed immersion.

The ambient compactification is packaged as a `CategoryTheory.ObjectProperty.FullSubcategory`
object of `AlgebraicGeometry.CompactificationOf`, so the open immersion and the properness of
the structure morphism are supplied as the two halves of its `property` field.

## References

* [Stacks Project, Tag 0F40](https://stacks.math.columbia.edu/tag/0F40)
* [Stacks Project, Tag 0894](https://stacks.math.columbia.edu/tag/0894)
* [Stacks Project, Tag 0BX5](https://stacks.math.columbia.edu/tag/0BX5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Compactification

/-- A map from the spectrum of a local ring lands in an open as soon as its closed point does.
This is the form needed to move valuative lifts into a trimmed compactification chart. -/
theorem valuativeMap_lift_open_of_closedPoint_mem
    {X : Scheme.{u}} {R : Type u} [CommRing R] [IsLocalRing R]
    (U : X.Opens) (h : Spec (.of R) ⟶ X)
    (hx : h.base (IsLocalRing.closedPoint R) ∈ U) :
    ∃ k : Spec (.of R) ⟶ U.toScheme, k ≫ U.ι = h := by
  have hrange : Set.range h.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ (h ⁻¹ᵁ U : (Spec (.of R)).Opens) := by
      rw [Scheme.preimage_eq_top_of_closedPoint_mem h hx]
      trivial
    exact ⟨⟨h.base y, hy⟩, rfl⟩
  exact ⟨IsOpenImmersion.lift U.ι h hrange, IsOpenImmersion.lift_fac _ _ _⟩

/-- Every valuative square over a proper morphism has a lift. -/
private theorem nonempty_liftStruct_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (E : ValuativeCommSq f) : Nonempty E.commSq.LiftStruct := by
  have hf : IsProper f := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hf
  exact ⟨(hf.1.1.1 E).some.default⟩

/-- A valuative square for a common model `W` is lifted by a chosen limit in a chart `X`, as
soon as the chart is reached from the open `U` through a proper morphism `b : X' ⟶ X` admitting
a compatible morphism `j : X' ⟶ W`. -/
theorem valuativeLift_of_proper_common_chart
    {S U X X' W : Scheme.{u}} (fX : X ⟶ S) (fW : W ⟶ S)
    (u : U ⟶ X) (v : U ⟶ W) (v' : U ⟶ X')
    (b : X' ⟶ X) (j : X' ⟶ W) [IsProper b]
    (hvb : v' ≫ b = u) (hvj : v' ≫ j = v)
    (hbf : b ≫ fX = j ≫ fW)
    (D : ValuativeCommSq fW) (g : Spec (.of D.K) ⟶ U)
    (hg : g ≫ v = D.i₁)
    (hX : Spec (.of D.R) ⟶ X)
    (hXgeneric : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ hX = g ≫ u)
    (hXbase : hX ≫ fX = D.i₂) :
    Nonempty D.commSq.LiftStruct := by
  let E : ValuativeCommSq b := {
    R := D.R
    K := D.K
    i₁ := g ≫ v'
    i₂ := hX
    commSq := ⟨by
      calc
        (g ≫ v') ≫ b = g ≫ u := by
          simpa only [Category.assoc] using congrArg (g ≫ ·) hvb
        _ = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ hX :=
          hXgeneric.symm⟩ }
  obtain ⟨l⟩ := nonempty_liftStruct_of_isProper b E
  refine ⟨{
    l := l.l ≫ j
    fac_left := ?_
    fac_right := ?_ }⟩
  · calc
      Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ (l.l ≫ j) =
          (g ≫ v') ≫ j := by
            simpa [E, Category.assoc] using congrArg (· ≫ j) l.fac_left
      _ = g ≫ v := by
        simpa only [Category.assoc] using congrArg (g ≫ ·) hvj
      _ = D.i₁ := hg
  · calc
      (l.l ≫ j) ≫ fW = l.l ≫ (b ≫ fX) := by simp only [Category.assoc, hbf]
      _ = hX ≫ fX := by
        simpa only [Category.assoc] using congrArg (· ≫ fX) l.fac_right
      _ = D.i₂ := hXbase

/-- If every valuative square for a separated common model `W` admits a chosen limit in one of
two charts, each reached from `U` through a proper morphism, then the square has a unique
lift. -/
theorem valuativeUnique_of_two_proper_common_charts
    {S U X₁ X₂ X₁' X₂' W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) (fW : W ⟶ S)
    (u₁ : U ⟶ X₁) (u₂ : U ⟶ X₂) (v : U ⟶ W)
    (v₁ : U ⟶ X₁') (v₂ : U ⟶ X₂')
    (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
    (j₁ : X₁' ⟶ W) (j₂ : X₂' ⟶ W)
    [IsProper b₁] [IsProper b₂] [IsSeparated fW]
    (hvb₁ : v₁ ≫ b₁ = u₁) (hvb₂ : v₂ ≫ b₂ = u₂)
    (hvj₁ : v₁ ≫ j₁ = v) (hvj₂ : v₂ ≫ j₂ = v)
    (hbf₁ : b₁ ≫ f₁ = j₁ ≫ fW) (hbf₂ : b₂ ≫ f₂ = j₂ ≫ fW)
    (hchoice : ∀ (D : ValuativeCommSq fW) (g : Spec (.of D.K) ⟶ U),
      g ≫ v = D.i₁ →
      (∃ h : Spec (.of D.R) ⟶ X₁,
        Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h = g ≫ u₁ ∧
        h ≫ f₁ = D.i₂) ∨
      (∃ h : Spec (.of D.R) ⟶ X₂,
        Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h = g ≫ u₂ ∧
        h ≫ f₂ = D.i₂)) :
    ∀ (D : ValuativeCommSq fW) (g : Spec (.of D.K) ⟶ U),
      g ≫ v = D.i₁ → Nonempty (Unique D.commSq.LiftStruct) := by
  intro D g hg
  have : Subsingleton D.commSq.LiftStruct := IsSeparated.valuativeCriterion fW D
  have hLift : Nonempty D.commSq.LiftStruct := by
    rcases hchoice D g hg with ⟨h, hgeneric, hbase⟩ | ⟨h, hgeneric, hbase⟩
    · exact valuativeLift_of_proper_common_chart f₁ fW u₁ v v₁ b₁ j₁
        hvb₁ hvj₁ hbf₁ D g hg h hgeneric hbase
    · exact valuativeLift_of_proper_common_chart f₂ fW u₂ v v₂ b₂ j₂
        hvb₂ hvj₂ hbf₂ D g hg h hgeneric hbase
  exact ⟨uniqueOfSubsingleton hLift.some⟩

/-- A proper compactification chart supplies a valuative lift when its closed point avoids the
trimmed boundary. -/
theorem valuativeLift_of_proper_open_chart
    {S Y W : Scheme.{u}} (F : W ⟶ S) (Q : Y ⟶ S)
    (T : Y.Opens) (j : T.toScheme ⟶ W)
    [IsProper Q] (hj : j ≫ F = T.ι ≫ Q)
    (D : ValuativeCommSq F) (k : Spec (.of D.K) ⟶ T.toScheme)
    (hgeneric : k ≫ j = D.i₁)
    (hgood : ∀ h : Spec (.of D.R) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h = k ≫ T.ι →
      h ≫ Q = D.i₂ → h.base (IsLocalRing.closedPoint D.R) ∈ T) :
    Nonempty D.commSq.LiftStruct := by
  let E : ValuativeCommSq Q := {
    R := D.R
    K := D.K
    i₁ := k ≫ T.ι
    i₂ := D.i₂
    commSq := ⟨by
      calc
        (k ≫ T.ι) ≫ Q = k ≫ j ≫ F := by simp only [Category.assoc, hj]
        _ = D.i₁ ≫ F := by rw [← Category.assoc, hgeneric]
        _ = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ :=
          D.commSq.w⟩ }
  obtain ⟨l⟩ := nonempty_liftStruct_of_isProper Q E
  obtain ⟨h, hh⟩ := valuativeMap_lift_open_of_closedPoint_mem T l.l
    (hgood l.l l.fac_left l.fac_right)
  have hfac : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h = k :=
    (cancel_mono T.ι).1 (by rw [Category.assoc, hh]; exact l.fac_left)
  refine ⟨{
    l := h ≫ j
    fac_left := ?_
    fac_right := ?_ }⟩
  · rw [← Category.assoc, hfac, hgeneric]
  · calc
      (h ≫ j) ≫ F = h ≫ T.ι ≫ Q := by simp only [Category.assoc, hj]
      _ = l.l ≫ Q := by rw [← Category.assoc, hh]
      _ = D.i₂ := l.fac_right

/-- A valuative lift through a proper chart can be transported through an admissible common
model after its closed point lands in the chart's open. -/
theorem valuativeLift_of_proper_open_chart_to_common_model
    {S U Y X X' W : Scheme.{u}}
    (Q : Y ⟶ S) (fX : X ⟶ S) (fW : W ⟶ S)
    (T : Y.Opens) (t : T.toScheme ⟶ X)
    (u : U ⟶ X) (v : U ⟶ W) (v' : U ⟶ X')
    (b : X' ⟶ X) (j : X' ⟶ W)
    [IsProper Q] [IsProper b]
    (ht : t ≫ fX = T.ι ≫ Q)
    (hu : u ≫ fX = v ≫ fW)
    (hvb : v' ≫ b = u) (hvj : v' ≫ j = v)
    (hbf : b ≫ fX = j ≫ fW)
    (D : ValuativeCommSq fW) (g : Spec (.of D.K) ⟶ U)
    (hg : g ≫ v = D.i₁)
    (k : Spec (.of D.K) ⟶ T.toScheme) (hk : k ≫ t = g ≫ u)
    (hgood : ∀ h : Spec (.of D.R) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h = k ≫ T.ι →
      h ≫ Q = D.i₂ → h.base (IsLocalRing.closedPoint D.R) ∈ T) :
    Nonempty D.commSq.LiftStruct := by
  let E : ValuativeCommSq fX := {
    R := D.R
    K := D.K
    i₁ := g ≫ u
    i₂ := D.i₂
    commSq := ⟨by
      calc
        (g ≫ u) ≫ fX = g ≫ v ≫ fW := by
          rw [Category.assoc, hu]
        _ = D.i₁ ≫ fW := by rw [← Category.assoc, hg]
        _ = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ :=
          D.commSq.w⟩ }
  obtain ⟨l⟩ := valuativeLift_of_proper_open_chart fX Q T t ht E k
    (by simpa [E] using hk) hgood
  exact valuativeLift_of_proper_common_chart fX fW u v v' b j
    hvb hvj hbf D g hg l.l (by simpa [E] using l.fac_left) l.fac_right

/-- A chosen proper limit in the trimmed open gives a limit in the common ambient model. -/
theorem valuativeLift_of_chosen_proper_limit_to_common_model
    {S U Y X X' W : Scheme.{u}}
    (Q : Y ⟶ S) (fX : X ⟶ S) (fW : W ⟶ S)
    (T : Y.Opens) (t : T.toScheme ⟶ X)
    (u : U ⟶ X) (v : U ⟶ W) (v' : U ⟶ X')
    (b : X' ⟶ X) (j : X' ⟶ W)
    [IsProper b]
    (ht : t ≫ fX = T.ι ≫ Q)
    (hvb : v' ≫ b = u) (hvj : v' ≫ j = v)
    (hbf : b ≫ fX = j ≫ fW)
    (D : ValuativeCommSq fW) (g : Spec (.of D.K) ⟶ U)
    (hg : g ≫ v = D.i₁)
    (k : Spec (.of D.K) ⟶ T.toScheme) (hk : k ≫ t = g ≫ u)
    (h : Spec (.of D.R) ⟶ Y)
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h =
      k ≫ T.ι)
    (hbase : h ≫ Q = D.i₂)
    (hclosed : h.base (IsLocalRing.closedPoint D.R) ∈ T) :
    Nonempty D.commSq.LiftStruct := by
  obtain ⟨hT, hhT⟩ := valuativeMap_lift_open_of_closedPoint_mem T h hclosed
  have hTgeneric : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ hT = k :=
    (cancel_mono T.ι).1 (by rw [Category.assoc, hhT, hgeneric])
  exact valuativeLift_of_proper_common_chart fX fW u v v' b j
    hvb hvj hbf D g hg (hT ≫ t)
    (by rw [← Category.assoc, hTgeneric, hk])
    (by rw [Category.assoc, ht, ← Category.assoc, hhT, hbase])

/-- A map through a closed immersion extends across a schematically dense precomposition. -/
@[ega "IV 11.10.1" "(a) ⇒ (c), special case", ega "IV 20.3.8.7" "special case"]
theorem exists_factor_closedImmersion_of_schemeTheoreticallyDominant
    {A B C Z : Scheme.{u}} (d : A ⟶ B) (h : B ⟶ Z) (i : C ⟶ Z)
    [IsSchemeTheoreticallyDominant d] [IsClosedImmersion i]
    (g : A ⟶ C) (hg : g ≫ i = d ≫ h) :
    ∃ k : B ⟶ C, k ≫ i = h := by
  have hker : i.ker ≤ h.ker := by
    calc
      i.ker ≤ (g ≫ i).ker := g.le_ker_comp i
      _ = (d ≫ h).ker := by rw [hg]
      _ = d.ker.map h := Scheme.Hom.ker_comp d h
      _ = h.ker := by rw [d.ker_eq_bot, Scheme.IdealSheafData.map_bot]
  exact ⟨IsClosedImmersion.lift i h hker, IsClosedImmersion.lift_fac i h hker⟩

/-- The generic-point inclusion associated to a valuative square is schematically dominant. -/
theorem schemeTheoreticallyDominant_genericOfValuativeCommSq
    {X S : Scheme.{u}} (f : X ⟶ S) (D : ValuativeCommSq f) :
    IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))) := by
  let : CommRing D.R := D.commRing
  let : Field D.K := D.field
  let : ValuationRing D.R := D.valuationRing
  let : IsFractionRing D.R D.K := D.isFractionRing
  have hDominant : IsDominant
      (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))) := by
    apply isDominant_of_of_appTop_injective
    intro x y hxy
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of D.R)).hom).1
    apply FaithfulSMul.algebraMap_injective D.R D.K
    have h := congrArg (fun z => (Scheme.ΓSpecIso (.of D.K)).hom z) hxy
    have h1 :
        (((Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))).appTop ≫
          (Scheme.ΓSpecIso (.of D.K)).hom) x) =
        (((Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))).appTop ≫
          (Scheme.ΓSpecIso (.of D.K)).hom) y) := by
      simpa only [ConcreteCategory.comp_apply] using h
    rw [Scheme.ΓSpecIso_naturality] at h1
    simpa only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom] using h1
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- A map from the spectrum of a valuation ring factors through a closed immersion as soon as its
restriction to the fraction field does. -/
private theorem exists_factor_closedImmersion_of_valuativeCommSq
    {X S C Z : Scheme.{u}} (f : X ⟶ S) (D : ValuativeCommSq f) (i : C ⟶ Z)
    [IsClosedImmersion i] (h : Spec (.of D.R) ⟶ Z) (g : Spec (.of D.K) ⟶ C)
    (hg : g ≫ i = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h) :
    ∃ k : Spec (.of D.R) ⟶ C, k ≫ i = h :=
  have := schemeTheoreticallyDominant_genericOfValuativeCommSq f D
  exists_factor_closedImmersion_of_schemeTheoreticallyDominant _ h i g hg

/-- If the generic point of a valuation maps through a scheme-theoretic image, the whole
valuation maps through it. -/
theorem valuative_map_factors_through_image
    {X S Z : Scheme.{u}} (f : X ⟶ S) (D : ValuativeCommSq f)
    (a : Z ⟶ X) (h : Spec (.of D.R) ⟶ X)
    (g : Spec (.of D.K) ⟶ Z)
    (hg : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h = g ≫ a) :
    ∃ k : Spec (.of D.R) ⟶ a.image, k ≫ a.imageι = h := by
  exact exists_factor_closedImmersion_of_valuativeCommSq f D a.imageι h (g ≫ a.toImage)
    (by rw [Category.assoc, Scheme.Hom.toImage_imageι, hg])

/-- Two compatible valuation limits of a generic point in a fibre product remain in the
scheme-theoretic image of that generic family. -/
theorem valuative_pair_factors_through_image
    {S X₁ X₂ Z : Scheme.{u}} (Q₁ : X₁ ⟶ S) (Q₂ : X₂ ⟶ S)
    (a : Z ⟶ pullback Q₁ Q₂) (D : ValuativeCommSq Q₁)
    (g : Spec (.of D.K) ⟶ Z)
    (h₁ : Spec (.of D.R) ⟶ X₁) (h₂ : Spec (.of D.R) ⟶ X₂)
    (hbase : h₁ ≫ Q₁ = h₂ ≫ Q₂)
    (hgen₁ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h₁ =
      g ≫ a ≫ pullback.fst Q₁ Q₂)
    (hgen₂ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h₂ =
      g ≫ a ≫ pullback.snd Q₁ Q₂) :
    ∃ k : Spec (.of D.R) ⟶ a.image,
      k ≫ a.imageι = pullback.lift h₁ h₂ hbase := by
  have hg : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫
      pullback.lift h₁ h₂ hbase = g ≫ a := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using hgen₁
    · simpa only [Category.assoc, pullback.lift_snd] using hgen₂
  let D' : ValuativeCommSq (pullback.fst Q₁ Q₂) := {
    R := D.R
    K := D.K
    i₁ := g ≫ a
    i₂ := h₁
    commSq := ⟨hgen₁.symm⟩ }
  exact valuative_map_factors_through_image (pullback.fst Q₁ Q₂) D' a
    (pullback.lift h₁ h₂ hbase) g hg

/-- Disjoint closed boundary preimages in the scheme-theoretic image exclude two simultaneous
bad valuation limits. -/
theorem valuative_pair_not_in_disjoint_image_boundaries
    {S X₁ X₂ Z : Scheme.{u}} (Q₁ : X₁ ⟶ S) (Q₂ : X₂ ⟶ S)
    (a : Z ⟶ pullback Q₁ Q₂) (B₁ : Set X₁) (B₂ : Set X₂)
    (hdisj : Disjoint
      ((a.imageι ≫ pullback.fst Q₁ Q₂).base ⁻¹' B₁)
      ((a.imageι ≫ pullback.snd Q₁ Q₂).base ⁻¹' B₂))
    (D : ValuativeCommSq Q₁) (g : Spec (.of D.K) ⟶ Z)
    (h₁ : Spec (.of D.R) ⟶ X₁) (h₂ : Spec (.of D.R) ⟶ X₂)
    (hbase : h₁ ≫ Q₁ = h₂ ≫ Q₂)
    (hgen₁ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h₁ =
      g ≫ a ≫ pullback.fst Q₁ Q₂)
    (hgen₂ : Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ h₂ =
      g ≫ a ≫ pullback.snd Q₁ Q₂) :
    ¬(h₁.base (IsLocalRing.closedPoint D.R) ∈ B₁ ∧
      h₂.base (IsLocalRing.closedPoint D.R) ∈ B₂) := by
  obtain ⟨k, hk⟩ := valuative_pair_factors_through_image
    Q₁ Q₂ a D g h₁ h₂ hbase hgen₁ hgen₂
  rintro ⟨hbad₁, hbad₂⟩
  let x := k.base (IsLocalRing.closedPoint D.R)
  have hx₁ : (a.imageι ≫ pullback.fst Q₁ Q₂).base x ∈ B₁ := by
    have h := congrArg (fun f : Spec (.of D.R) ⟶ pullback Q₁ Q₂ =>
      (f ≫ pullback.fst Q₁ Q₂).base (IsLocalRing.closedPoint D.R)) hk
    have hbad' : (pullback.lift h₁ h₂ hbase ≫ pullback.fst Q₁ Q₂).base
        (IsLocalRing.closedPoint D.R) ∈ B₁ := by
      simpa only [pullback.lift_fst] using hbad₁
    simpa only [Category.assoc] using h.symm ▸ hbad'
  have hx₂ : (a.imageι ≫ pullback.snd Q₁ Q₂).base x ∈ B₂ := by
    have h := congrArg (fun f : Spec (.of D.R) ⟶ pullback Q₁ Q₂ =>
      (f ≫ pullback.snd Q₁ Q₂).base (IsLocalRing.closedPoint D.R)) hk
    have hbad' : (pullback.lift h₁ h₂ hbase ≫ pullback.snd Q₁ Q₂).base
        (IsLocalRing.closedPoint D.R) ∈ B₂ := by
      simpa only [pullback.lift_snd] using hbad₂
    simpa only [Category.assoc] using h.symm ▸ hbad'
  exact Set.disjoint_left.mp hdisj hx₁ hx₂

/-- An open immersion into a proper `S`-scheme is a quasi-compact compactification when it is
quasi-compact. -/
private theorem exists_compactification_of_isProper
    {S U X : Scheme.{u}} (fU : U ⟶ S) (u : U ⟶ X) (f : X ⟶ S) (hcomm : u ≫ f = fU)
    [IsProper f] [IsOpenImmersion u] [QuasiCompact u] :
    ∃ j : AlgebraicGeometry.CompactificationOf (Over.mk fU), QuasiCompact j.immersion := by
  let a : Over.mk fU ⟶ Over.mk f := Over.homMk u hcomm
  have haOpen : IsOpenImmersion a.left := by change IsOpenImmersion u; infer_instance
  refine ⟨⟨StructuredArrow.mk a, ⟨haOpen, show IsProper f from inferInstance⟩⟩, ?_⟩
  simpa [a, AlgebraicGeometry.CompactificationOf.immersion] using
    (inferInstance : QuasiCompact u)

/-- A quasi-compact, separated, finite-type morphism admitting unique valuative lifts along a
dense quasi-compact open immersion is proper, hence that open immersion is a quasi-compact
compactification. -/
theorem exists_compactification_of_dense_open_valuative
    {S U X : Scheme.{u}} (fU : U ⟶ S) (u : U ⟶ X) (f : X ⟶ S)
    (hcomm : u ≫ f = fU)
    [QuasiCompact f] [LocallyOfFiniteType f] [IsSeparated f]
    [QuasiCompact fU] [IsOpenImmersion u]
    (hdense : DenseRange u)
    (hvaluative : ∀ (D : AlgebraicGeometry.ValuativeCommSq f)
      (g : AlgebraicGeometry.Spec (.of D.K) ⟶ U),
      g ≫ u = D.i₁ → Nonempty (Unique D.commSq.LiftStruct)) :
    ∃ j : AlgebraicGeometry.CompactificationOf (Over.mk fU), QuasiCompact j.immersion := by
  have : QuasiCompact (u ≫ f) := by rw [hcomm]; infer_instance
  have : QuasiSeparated f := inferInstance
  have : QuasiCompact u := QuasiCompact.of_comp u f
  have huc : AlgebraicGeometry.UniversallyClosed f :=
    AlgebraicGeometry.universallyClosed_of_unique_lift_of_denseRange u f hdense hvaluative
  let : AlgebraicGeometry.UniversallyClosed f := huc
  have : AlgebraicGeometry.IsProper f :=
    (AlgebraicGeometry.isProper_iff f).2 ⟨inferInstance, huc, inferInstance⟩
  exact exists_compactification_of_isProper fU u f hcomm

/-- A valuative criterion proved in an ambient finite-type scheme can be used even when the
chosen open is not dense in that ambient scheme.  Restrict to its scheme-theoretic image
first. -/
theorem exists_compactification_of_valuative_ambient
    {S A U W : Scheme.{u}} [IsNoetherian S]
    (fU : U ⟶ S) (d : A ⟶ U) (v : U ⟶ W) (F : W ⟶ S)
    [LocallyOfFiniteType F] [QuasiCompact F] [IsSeparated F]
    [QuasiCompact fU] [QuasiCompact d] [IsOpenImmersion v]
    (hdense : DenseRange d)
    (hcomm : v ≫ F = fU)
    (hvaluative : ∀ (D : ValuativeCommSq F) (g : Spec (.of D.K) ⟶ A),
      g ≫ d ≫ v = D.i₁ → Nonempty D.commSq.LiftStruct) :
    ∃ j : AlgebraicGeometry.CompactificationOf (Over.mk fU),
      QuasiCompact j.immersion := by
  classical
  let E := v.image
  let i : E ⟶ W := v.imageι
  let w : U ⟶ E := v.toImage
  let G : E ⟶ S := i ≫ F
  have hw : w ≫ i = v := Scheme.Hom.toImage_imageι v
  have : QuasiCompact v := by
    have : QuasiCompact (v ≫ F) := by rw [hcomm]; infer_instance
    exact QuasiCompact.of_comp v F
  have : IsOpenImmersion w := AlgebraicGeometry.isOpenImmersion_toImage v (Or.inl inferInstance)
  have : IsNoetherian W := by
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian F
    have : CompactSpace W := (quasiCompact_iff_compactSpace F).mp inferInstance
    exact ⟨⟩
  have : LocallyOfFiniteType G := by dsimp [G]; infer_instance
  have : QuasiCompact G := by dsimp [G]; infer_instance
  have : IsSeparated G := by dsimp [G]; infer_instance
  have hGw : w ≫ G = fU := by
    calc
      w ≫ G = (w ≫ i) ≫ F := by simp only [G, Category.assoc]
      _ = v ≫ F := by rw [hw]
      _ = fU := hcomm
  have hvalE : ∀ (D : ValuativeCommSq G) (g : Spec (.of D.K) ⟶ A),
      g ≫ d ≫ w = D.i₁ → Nonempty D.commSq.LiftStruct := by
    intro D g hg
    let D' : ValuativeCommSq F := {
      R := D.R
      K := D.K
      i₁ := D.i₁ ≫ i
      i₂ := D.i₂
      commSq := ⟨by
        calc
          (D.i₁ ≫ i) ≫ F = D.i₁ ≫ G := by simp only [G, Category.assoc]
          _ = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ := D.commSq.w⟩ }
    have hg' : g ≫ d ≫ v = D'.i₁ := by
      dsimp [D']
      calc
        g ≫ d ≫ v = (g ≫ d ≫ w) ≫ i := by simp only [hw, Category.assoc]
        _ = D.i₁ ≫ i := by rw [hg]
    obtain ⟨l⟩ := hvaluative D' g hg'
    obtain ⟨k, hk⟩ := exists_factor_closedImmersion_of_valuativeCommSq G D i l.l D.i₁
      (by simpa [D'] using l.fac_left.symm)
    refine ⟨{
      l := k
      fac_left := ?_
      fac_right := ?_ }⟩
    · apply (cancel_mono i).1
      calc
        (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ k) ≫ i =
            Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ l.l := by
              rw [Category.assoc, hk]
        _ = D.i₁ ≫ i := by simpa [D'] using l.fac_left
    · calc
        k ≫ G = (k ≫ i) ≫ F := by simp only [G, Category.assoc]
        _ = l.l ≫ F := by rw [hk]
        _ = D.i₂ := l.fac_right
  have hvalUnique : ∀ (D : ValuativeCommSq G) (g : Spec (.of D.K) ⟶ A),
      g ≫ d ≫ w = D.i₁ → Nonempty (Unique D.commSq.LiftStruct) := by
    intro D g hg
    obtain ⟨l⟩ := hvalE D g hg
    have : Subsingleton D.commSq.LiftStruct := IsSeparated.valuativeCriterion G D
    exact ⟨Unique.mk ⟨l⟩ (fun x => Subsingleton.elim x l)⟩
  have : QuasiCompact w := by
    have : QuasiCompact (w ≫ i) := by rw [hw]; infer_instance
    exact QuasiCompact.of_comp w i
  have : QuasiCompact (d ≫ w) := inferInstance
  have hdw : DenseRange (d ≫ w) := by
    simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
      using DenseRange.comp w.denseRange hdense w.continuous
  have hclosed : UniversallyClosed G :=
    AlgebraicGeometry.universallyClosed_of_unique_lift_of_denseRange
      (d ≫ w) G hdw (by
        intro D g hg
        exact hvalUnique D g (by simpa only [Category.assoc] using hg))
  let : UniversallyClosed G := hclosed
  have : IsProper G :=
    (isProper_iff G).2 ⟨inferInstance, hclosed, inferInstance⟩
  exact exists_compactification_of_isProper fU w G hGw

end Stacks.Compactification

end
