module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingPicardSequence
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingPicardExactness
public import StacksFrontier.AlgebraicGeometry.Picard.FirstCohomologyNaturality

/-!
# Exactness at the Picard group, and the vanishing clause, for a glueing of two points

Let `k` be an algebraically closed field and let `f : X' ⟶ X` be the glueing of the two distinct
rational points `a` and `b` of an algebraic `k`-scheme `X'`, in the sense of
[Stacks, Tag 0C1J]. [Stacks, Tag 0C1M] records the exact sequence

`k^* ⟶ Pic(X) ⟶ Pic(X') ⟶ 0`,

whose first map is the gluing homomorphism `Stacks.GluePicard.picardGluingHom` and whose second
is pullback of Picard classes. Surjectivity on the right is
`Stacks.GluePicard.surjective_schemePullbackClassHom`, and injectivity on the left for a proper
`X'` whose two glued points lie on one connected component is
`Stacks.GluePicard.injective_picardGluingHom_of_connectedComponents_eq`. **This file proves the
two remaining clauses**: exactness in the middle, and that the first map is zero when the two
glued points lie on different connected components of `X'`.

Both come from the long exact cohomology sequence over the whole space of the short exact
sequence of sheaves of units

`1 ⟶ 𝒪_X^* ⟶ f_*𝒪_{X'}^* ⟶ (k^*)_x ⟶ 1`

of [Stacks, Tag 0C1J], whose relevant five terms are

`H⁰(X, f_*𝒪_{X'}^*) ⟶ k^* ⟶ H¹(X, 𝒪_X^*) ⟶ H¹(X, f_*𝒪_{X'}^*)`.

**Exactness at `Pic(X)`.** The kernel of the third map is the image of the connecting map, which
is the gluing homomorphism read through [Stacks, Tag 09NU]. The first Leray edge map
`H¹(X, f_*𝒪_{X'}^*) ⟶ H¹(X', 𝒪_{X'}^*)` of [Stacks, Tag 01F2] is injective, so that kernel is
also the kernel of the composite, and the composite is pullback of Picard classes by the
naturality of Tag 09NU in a morphism of schemes.

**Vanishing when `a` and `b` lie on different connected components.** Every scalar is then the
ratio of the two values of a unit on the whole of `X'`
(`Stacks.GluePicard.exists_globalUnit_sectionAt_eq_of_ne_connectedComponents`), that is, it is
in the image of `H⁰(X, f_*𝒪_{X'}^*) ⟶ k^*`; and two consecutive maps of the long exact sequence
compose to zero, so the connecting map kills it.

## Main results

* `Stacks.GluePicard.UnitsSequence.phi_eq_unitsPushforwardMap` — the first map of the chosen
  units sequence is pullback of units, both being `Units.map (f.app U)` on sections.
* `Stacks.GluePicard.h1map_unitsPushforwardMap_eq_zero_iff` — exactness of the long exact
  cohomology sequence of the units sequence at `H¹(X, 𝒪_X^*)`.
* `Stacks.GluePicard.h1NativeUnitsPullback_eq_zero_iff_exists_connectingHom` — the kernel of
  pullback on native first cohomology of the units sheaf is the image of the connecting map.
* `Stacks.GluePicard.schemePullbackClassHom_eq_zero_iff_exists_picardGluingHom` and
  `Stacks.GluePicard.exact_picardGluingHom_schemePullbackClassHom` — **exactness at `Pic(X)`**,
  the kernel of pullback being the image of the gluing homomorphism.
* `Stacks.GluePicard.connectingHom_eq_zero_of_unitRatioAt_eq` — a scalar that is the ratio of
  the two values of a unit on the whole of `X'` is killed by the connecting map.
* `Stacks.GluePicard.picardGluingHom_eq_zero_of_ne_connectedComponents` — **the gluing
  homomorphism is zero** when the two glued points lie on different connected components.

## Implementation notes

The units sequence of Tag 0C1J is produced as an existential statement and chosen once by
`Stacks.GluePicard.unitsSequence`, so its first map is opaque; it is identified with
`Stacks.GlueSquishUnits.unitsPushforwardMap` from the formula both satisfy on sections.

## References

* [Stacks Project, Tag 0C1M](https://stacks.math.columbia.edu/tag/0C1M)
* [Stacks Project, Tag 0C1J](https://stacks.math.columbia.edu/tag/0C1J)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.GluePicard

open Stacks.Cohomology.Generators (unitsSheaf)
open Stacks.Cohomology.AbelianColimit (abSections H'functor H'δ shortComplex_H'_exact₁
  H'δ_eq_postcomp_extClass H'map_eq_postcomp_mk₀
  postcomp_mk₀_g_comp_postcomp_extClass postcomp_extClass_comp_postcomp_mk₀_f)
open Stacks.GlueSquishUnits (unitRatioAt unitsPushforwardMap unitsPushforwardMap_app)
open Stacks.Picard.FirstCohomology (h1NativeUnitsPullback h1UnitsAddEquivOfScheme_naturality)

/-! ### The first map of the chosen units sequence -/

/-- **The first map of the chosen units sequence is pullback of units**: it equals
`Stacks.GlueSquishUnits.unitsPushforwardMap f`. -/
theorem UnitsSequence.phi_eq_unitsPushforwardMap {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) :
    S.phi = unitsPushforwardMap f := by
  apply Sheaf.hom_ext
  ext U s
  exact (S.phi_app U.unop (Additive.toMul s)).trans
    (unitsPushforwardMap_app f U.unop (Additive.toMul s)).symm

/-! ### Exactness of the cohomology sequence -/

/-- If two composable morphisms of abelian groups compose to zero, the second kills the image of
the first. -/
private theorem apply_eq_zero_of_comp_eq_zero {A B C : AddCommGrpCat.{u}} {f : A ⟶ B}
    {g : B ⟶ C} (h : f ≫ g = 0) (x : A) : g (f x) = 0 := by
  simpa using ConcreteCategory.congr_hom h x

/-- **Exactness at `H¹(X, 𝒪_X^*)` of the long exact cohomology sequence of the units sequence of
a glueing of two points**: a class killed by the map induced by `𝒪_X^* ⟶ f_*𝒪_{X'}^*` is the
image of a degree-zero class of the skyscraper under the connecting map. -/
theorem h1map_unitsPushforwardMap_eq_zero_iff {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b)
    (c : (H'functor (X := (X : Type u)) ⊤ 1).obj (unitsSheaf X.toRingedSpace)) :
    (H'functor (X := (X : Type u)) ⊤ 1).map (unitsPushforwardMap f) c = 0 ↔
      ∃ t : (H'functor (X := (X : Type u)) ⊤ 0).obj S.complex.X₃,
        H'δ S.complex_shortExact (⊤ : Opens (X : Type u)) (zero_add 1) t = c := by
  rw [← S.phi_eq_unitsPushforwardMap]
  refine ⟨fun hc => ?_, fun ht => ?_⟩
  · exact (ShortComplex.ab_exact_iff _).1
      (shortComplex_H'_exact₁ S.complex_shortExact (⊤ : Opens (X : Type u)) (zero_add 1)) c hc
  · obtain ⟨t, rfl⟩ := ht
    have hzero : H'δ S.complex_shortExact (⊤ : Opens (X : Type u)) (zero_add 1) ≫
        (H'functor (X := (X : Type u)) ⊤ 1).map S.complex.f = 0 := by
      rw [H'δ_eq_postcomp_extClass, H'map_eq_postcomp_mk₀]
      exact postcomp_extClass_comp_postcomp_mk₀_f S.complex_shortExact
        (⊤ : Opens (X : Type u)) (zero_add 1)
    exact apply_eq_zero_of_comp_eq_zero hzero t

/-- **The kernel of pullback on native first cohomology of the sheaf of units is the image of
the connecting map** of the units sequence of a glueing of two points. -/
theorem h1NativeUnitsPullback_eq_zero_iff_exists_connectingHom {k : Type u} [Field k]
    [IsAlgClosed k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b)
    (c : (H'functor (X := (X : Type u)) ⊤ 1).obj (unitsSheaf X.toRingedSpace)) :
    h1NativeUnitsPullback f c = 0 ↔
      ∃ d : Additive kˣ, AddCommGrpCat.Hom.hom' (connectingHom S) d = c :=
  (Stacks.SquishSheafSequence.h1NativeUnitsPullback_eq_zero_iff f c).trans
    ((h1map_unitsPushforwardMap_eq_zero_iff S c).trans
      (Stacks.SquishSheafSequence.exists_apply_eq_iff_of_eq_inv_comp
        ((h0Iso (X : Type u)).app S.complex.X₃) (sequenceTopIso S)
        (H'δ S.complex_shortExact (⊤ : Opens (X : Type u)) (zero_add 1)) (connectingHom S) rfl c))

/-! ### Exactness at the Picard group -/

/-- **Exactness at `Pic(X)` of the sequence of [Stacks, Tag 0C1M].** For `k` algebraically
closed and `f : X' ⟶ X` the glueing of the two rational points `a` and `b` of `X'`, a Picard
class of `X` pulls back to zero on `X'` exactly when it is the value of the gluing homomorphism
`Stacks.GluePicard.picardGluingHom` at a scalar; that is, the kernel of `Pic(X) ⟶ Pic(X')` is
the image of `k^* ⟶ Pic(X)`. -/
@[stacks 0C1M "exactness at Pic(X): the kernel of pullback is the image of k^*"]
theorem schemePullbackClassHom_eq_zero_iff_exists_picardGluingHom {k : Type u} [Field k]
    [IsAlgClosed k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) (L : Stacks.Picard.ofScheme X) :
    Stacks.Picard.schemePullbackClassHom f L = 0 ↔
      ∃ c : Additive kˣ, picardGluingHom f a b h c = L := by
  have hc : h1UnitsAddEquivOfScheme X ((h1UnitsAddEquivOfScheme X).symm L) = L :=
    (h1UnitsAddEquivOfScheme X).apply_symm_apply L
  have hpull : Stacks.Picard.schemePullbackClassHom f L =
      h1UnitsAddEquivOfScheme X'
        (h1NativeUnitsPullback f ((h1UnitsAddEquivOfScheme X).symm L)) :=
    ((h1UnitsAddEquivOfScheme_naturality f ((h1UnitsAddEquivOfScheme X).symm L)).trans
      (congrArg (fun y => Stacks.Picard.schemePullbackClassHom f y) hc)).symm
  have hrange : (∃ c : Additive kˣ, picardGluingHom f a b h c = L) ↔
      ∃ c : Additive kˣ,
        AddCommGrpCat.Hom.hom' (connectingHom (unitsSequence f a b h)) c =
          (h1UnitsAddEquivOfScheme X).symm L := by
    refine exists_congr fun c => Iff.trans ?_ (h1UnitsAddEquivOfScheme X).apply_eq_iff_eq
    rw [picardGluingHom_apply, hc]
  rw [hpull, AddEquiv.map_eq_zero_iff, hrange]
  exact h1NativeUnitsPullback_eq_zero_iff_exists_connectingHom (unitsSequence f a b h) _

/-- **Exactness at `Pic(X)` of the sequence of [Stacks, Tag 0C1M]**, in the `Function.Exact`
spelling: the kernel of pullback of Picard classes is the range of the gluing homomorphism. -/
@[stacks 0C1M "exactness at Pic(X): the kernel of pullback is the image of k^*"]
theorem exact_picardGluingHom_schemePullbackClassHom {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) :
    Function.Exact (picardGluingHom f a b h) (Stacks.Picard.schemePullbackClassHom f) :=
  fun L => (schemePullbackClassHom_eq_zero_iff_exists_picardGluingHom f a b h L).trans
    Set.mem_range.symm

/-! ### Vanishing of the gluing homomorphism on different connected components -/

/-- A unit whose value at `a` is `c` and whose value at `b` is `1` has ratio `c`. -/
private theorem unitRatioAt_eq_of_sectionAt_eq_of_sectionAt_eq_one {k : Type u} [Field k]
    {Y : Scheme.{u}} (a b : Spec (.of k) ⟶ Y) (U : Y.Opens)
    (ha : a.base (IsLocalRing.closedPoint k) ∈ U)
    (hb : b.base (IsLocalRing.closedPoint k) ∈ U) (s : Γ(Y, U)ˣ) (c : kˣ)
    (hsa : AlgebraicGeometry.sectionAt a U ha (s : Γ(Y, U)) = (c : k))
    (hsb : AlgebraicGeometry.sectionAt b U hb (s : Γ(Y, U)) = 1) :
    unitRatioAt a b U ha hb s = c := by
  have ha' : Units.map
      (Y.presheaf.germ U _ ha ≫ Scheme.stalkClosedPointTo a).hom.toMonoidHom s = c :=
    Units.ext hsa
  have hb' : Units.map
      (Y.presheaf.germ U _ hb ≫ Scheme.stalkClosedPointTo b).hom.toMonoidHom s = 1 :=
    Units.ext hsb
  change Units.map _ s * (Units.map _ s)⁻¹ = c
  rw [ha', hb', inv_one, mul_one]

/-- The quotient map of the units sequence on degree-zero cohomology followed by the connecting
map of the long exact sequence is zero. -/
private theorem h0map_comp_H'δ_eq_zero {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) :
    (H'functor (X := (X : Type u)) ⊤ 0).map S.complex.g ≫
        H'δ S.complex_shortExact (⊤ : Opens (X : Type u)) (zero_add 1) = 0 := by
  rw [H'map_eq_postcomp_mk₀, H'δ_eq_postcomp_extClass]
  exact postcomp_mk₀_g_comp_postcomp_extClass S.complex_shortExact
    (⊤ : Opens (X : Type u)) (zero_add 1)

/-- **A scalar lifted by the quotient map on sections over the whole space is killed by the
connecting map.** -/
theorem connectingHom_eq_zero_of_exists_section {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) (c : Additive kˣ)
    (ht : ∃ t : (abSections (X := (X : Type u)) ⊤).obj S.complex.X₂,
      (abSections (X := (X : Type u)) ⊤).map S.complex.g t = (sequenceTopIso S).inv c) :
    AddCommGrpCat.Hom.hom' (connectingHom S) c = 0 := by
  obtain ⟨t, hgt⟩ := ht
  have hnat := ConcreteCategory.congr_hom
    ((h0Iso (X : Type u)).inv.naturality S.complex.g) t
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [connectingHom_apply, ← hgt, hnat]
  exact apply_eq_zero_of_comp_eq_zero (h0map_comp_H'δ_eq_zero S) _

/-- **A scalar that is the ratio of the two values of a unit on the whole of `X'` is killed by
the connecting map** of the units sequence. -/
theorem connectingHom_eq_zero_of_unitRatioAt_eq {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    {f : X' ⟶ X} {a b : Spec (.of k) ⟶ X'} (S : UnitsSequence f a b) (c : Additive kˣ)
    (s : Γ(X', f ⁻¹ᵁ (⊤ : X.Opens))ˣ)
    (hs : unitRatioAt a b (f ⁻¹ᵁ (⊤ : X.Opens)) (Opens.mem_top _) (Opens.mem_top _) s =
      Additive.toMul c) :
    AddCommGrpCat.Hom.hom' (connectingHom S) c = 0 := by
  refine connectingHom_eq_zero_of_exists_section S c ⟨Additive.ofMul s, ?_⟩
  have hcval : (sequenceTopIso S).hom ((abSections (X := (X : Type u)) ⊤).map S.complex.g
      (Additive.ofMul s : (abSections (X := (X : Type u)) ⊤).obj S.complex.X₂)) = c :=
    (S.sequenceTopIso_map_g (Opens.mem_top _) (Opens.mem_top _)
      (Additive.ofMul s : (abSections (X := (X : Type u)) ⊤).obj S.complex.X₂)).trans
      (congrArg Additive.ofMul hs)
  rw [← hcval]
  exact (Iso.hom_inv_id_apply (sequenceTopIso S) _).symm

/-- **The first map of the sequence of [Stacks, Tag 0C1M] is zero when the two glued points lie
on different connected components of `X'`.** -/
@[stacks 0C1M "the first map is zero if a and b are on different connected components of X'"]
theorem picardGluingHom_eq_zero_of_ne_connectedComponents {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) ≠
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) :
    picardGluingHom f a b h = 0 := by
  refine AddMonoidHom.ext fun c => ?_
  obtain ⟨s, hsa, hsb⟩ :=
    exists_globalUnit_sectionAt_eq_of_ne_connectedComponents f a b h hab (Additive.toMul c)
  rw [AddMonoidHom.zero_apply, picardGluingHom_apply,
    connectingHom_eq_zero_of_unitRatioAt_eq (unitsSequence f a b h) c s
      (unitRatioAt_eq_of_sectionAt_eq_of_sectionAt_eq_one a b _ _ _ s _ hsa hsb), map_zero]

end Stacks.GluePicard

end
