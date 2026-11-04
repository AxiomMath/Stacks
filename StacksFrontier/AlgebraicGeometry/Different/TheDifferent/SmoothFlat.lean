module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FibrewiseFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.FibrewiseCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.Variety.MiracleFlatEtale
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of a quasi-finite morphism of smooth schemes

Let `X` and `Y` be smooth of relative dimension `n` over a locally Noetherian base `S` and let
`f : Y ⟶ X` be a locally quasi-finite morphism over `S`.  Then `f` is flat.

Flatness is checked on the fibres over `S` ([Stacks, Tag 039D]).  On a fibre both `X_s` and `Y_s`
are smooth of relative dimension `n` over the residue field `κ(s)`, so their local rings are
regular, and the dimension formula [Stacks, Tag 0A21] applied on both sides gives
`dim 𝒪_{Y_s, y} = dim 𝒪_{X_s, f y}`: the two topological dimensions are both `n`, and the two
transcendence degrees agree because quasi-finiteness makes the residue field extension finite.
Quasi-finiteness also makes the fibre ring `𝒪_{Y_s, y} / 𝔪_{X_s, f y} 𝒪_{Y_s, y}` Artinian, hence
zero-dimensional, so miracle flatness [Stacks, Tag 00R4] applies to the stalk map.

## Main results

* `Module.Flat.of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero`: miracle flatness with a
  zero-dimensional fibre ring in place of an unramifiedness hypothesis.
* `AlgebraicGeometry.isArtinianRing_stalk`: the local rings of a locally Artinian scheme are
  Artinian.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_smoothOfRelativeDimension`: a fibre of a
  morphism smooth of relative dimension `n` has dimension `n` at each of its points.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite_over_field`: a locally
  quasi-finite morphism between schemes of finite type over a field which have the same dimension
  at a point and its image preserves the Krull dimension of the local ring there.
* `Stacks.Discriminant.flat_fiberHom`: the induced morphism on fibres over `S` is flat.
* `Stacks.Discriminant.flat_of_locallyQuasiFinite`: **[Stacks, Tag 0BWJ]**, `f` is flat.

## Implementation notes

Three different `Algebra` structures on residue fields occur.  The dimension formula
`AlgebraicGeometry.topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk` supplies the `κ(s)`-algebra
structure on `κ(y)` induced by the structure morphism through global sections, inside its own
statement; `AlgebraicGeometry.Scheme.Hom.finite_residueField_of_quasiFiniteAt` supplies the
`κ(f y)`-algebra structure on `κ(y)` induced by `Scheme.Hom.residueFieldMap`.  That these form a
scalar tower is `AlgebraicGeometry.isScalarTower_residueField_of_comp`, which is the naturality of
`Scheme.Γevaluation`.  The statements below carry the first structure in the same `letI` spelling
as the dimension formula, so that `dsimp only` makes hypothesis and conclusion speak of one
instance.

## References

* [Stacks Project, Tag 0BWJ](https://stacks.math.columbia.edu/tag/0BWJ)
* [Stacks Project, Tag 039D](https://stacks.math.columbia.edu/tag/039D)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 02NG](https://stacks.math.columbia.edu/tag/02NG)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u

/-! ### Miracle flatness with a zero-dimensional fibre ring -/

/-- **Miracle flatness with a zero-dimensional fibre ring.**  A local homomorphism `R → S` from a
regular local ring to a Noetherian Cohen-Macaulay local ring of the same Krull dimension whose
fibre ring `S/𝔪_R S` is zero-dimensional is flat. -/
@[ega "IV 15.4.2" "e′)⇒b), partial", ega "IV 6.1.5" "special case"]
public theorem Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_quotient_eq_zero
    {R S : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hS : Module.IsMaximalCohenMacaulay S S)
    (hfib : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0)
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S := by
  refine Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add hS ?_
  rw [hfib, add_zero, hdim]

/-- A local homomorphism of regular local rings of the same Krull dimension with a
zero-dimensional fibre ring is flat. -/
public theorem Module.Flat.of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
    {R S : Type*} [CommRing R] [IsRegularLocalRing R] [CommRing S] [IsRegularLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hfib : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0)
    (hdim : ringKrullDim S = ringKrullDim R) :
    Module.Flat R S :=
  .of_isMaximalCohenMacaulay_of_ringKrullDim_quotient_eq_zero
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      S).2 hfib hdim

namespace AlgebraicGeometry

/-- The stalk map of a morphism of schemes at a point where both local rings are regular of the
same Krull dimension and where the fibre ring of the stalk map is zero-dimensional is flat. -/
public theorem flat_stalkMap_of_ringKrullDim_quotient_eq_zero {X Y : Scheme.{u}} (g : X ⟶ Y)
    (x : X) [IsRegularLocalRing (Y.presheaf.stalk (g.base x))]
    [IsRegularLocalRing (X.presheaf.stalk x)]
    (hfib : ringKrullDim ((X.presheaf.stalk x) ⧸
      Ideal.map (g.stalkMap x).hom (maximalIdeal (Y.presheaf.stalk (g.base x)))) = 0)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (g.base x))) :
    (g.stalkMap x).hom.Flat := by
  let : Algebra (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) :=
    (g.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  exact RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero hfib hdim)

/-! ### Zero-dimensional fibre rings of a locally quasi-finite morphism -/

/-- The local rings of a locally Artinian scheme are Artinian: the stalk at a point is a
localization of the Artinian ring of sections over an affine open neighbourhood. -/
public theorem isArtinianRing_stalk {X : Scheme.{u}} [IsLocallyArtinian X] (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsArtinianRing Γ(X, U) := IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨U, hU⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact IsArtinianRing.localization_artinian
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (X.presheaf.stalk x)

/-- **The fibre ring of the stalk map of a locally quasi-finite morphism is zero-dimensional.**
The quotient `𝒪_{X,x}/𝔪_{Y,g x}𝒪_{X,x}` is the local ring of the fibre `X_{g x}` at `x`, and that
fibre is locally Artinian. -/
public theorem ringKrullDim_quotient_stalk_eq_zero_of_locallyQuasiFinite {X Y : Scheme.{u}}
    (g : X ⟶ Y) [LocallyQuasiFinite g] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      Ideal.map (g.stalkMap x).hom (maximalIdeal (Y.presheaf.stalk (g.base x)))) = 0 := by
  have : IsArtinianRing ((g.fiber (g.base x)).presheaf.stalk (g.asFiber x)) :=
    isArtinianRing_stalk _
  rw [ringKrullDim_eq_of_ringEquiv (quotientStalkEquivFiberStalk g x)]
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-! ### The dimension of a fibre of a smooth morphism -/

/-- The dimension of the fibre of a morphism smooth of relative dimension `n` at a point
transported from the source is `n`. -/
private theorem topologicalKrullDimAt_fiber_transport {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n p] (x : X) {s : S} (h : p.base x = s) :
    topologicalKrullDimAt (p.fiber s) (h ▸ p.asFiber x) = (n : WithBot ℕ∞) := by
  cases h
  exact fiberDimensionAt_eq_of_smoothOfRelativeDimension p n x

/-- Transporting `Scheme.Hom.asFiber` along an equality of images does not change the image in the
source. -/
private theorem fiberι_transport_asFiber {X S : Scheme.{u}} (p : X ⟶ S) (x : X) {s : S}
    (h : p.base x = s) : (p.fiberι s) (h ▸ p.asFiber x) = x := by
  cases h
  exact p.fiberι_asFiber x

/-- **[Stacks, Tag 0B9D] at a point of the fibre.**  Every fibre of a morphism smooth of relative
dimension `n` has dimension `n` at each of its points. -/
public theorem topologicalKrullDimAt_fiber_eq_of_smoothOfRelativeDimension {X S : Scheme.{u}}
    (p : X ⟶ S) (n : ℕ) [SmoothOfRelativeDimension n p] (s : S) (z : p.fiber s) :
    topologicalKrullDimAt (p.fiber s) z = (n : WithBot ℕ∞) := by
  have hmem : p.fiberι s z ∈ p ⁻¹' {s} := by
    rw [← p.range_fiberι s]
    exact ⟨z, rfl⟩
  have h : p.base (p.fiberι s z) = s := hmem
  have hz : (h ▸ p.asFiber (p.fiberι s z) : p.fiber s) = z :=
    (p.fiberι s).isEmbedding.injective (by rw [fiberι_transport_asFiber])
  rw [← hz]
  exact topologicalKrullDimAt_fiber_transport p n _ h

/-! ### The dimension of the stalk is preserved by a quasi-finite morphism over a field -/

/-- The residue field of the source of a morphism over a field is an extension of the residue
field of the image in a tower over the base field: the two induced structures are compatible by
naturality of `Scheme.Γevaluation`. -/
public theorem isScalarTower_residueField_of_comp (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (g : Y ⟶ X) (hg : g ≫ pX = pY) (y : Y) :
    letI : Algebra k (X.residueField (g.base y)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation (g.base y)).hom.toAlgebra
    letI : Algebra k (Y.residueField y) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
    letI : Algebra (X.residueField (g.base y)) (Y.residueField y) :=
      (g.residueFieldMap y).hom.toAlgebra
    IsScalarTower k (X.residueField (g.base y)) (Y.residueField y) := by
  subst hg
  let : Algebra k (X.residueField (g.base y)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation (g.base y)).hom.toAlgebra
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (g ≫ pX).appTop ≫ Y.Γevaluation y).hom.toAlgebra
  let : Algebra (X.residueField (g.base y)) (Y.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  exact (Scheme.Γevaluation_naturality_apply g y
    (pX.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a))).symm

/-- Cancellation of a finite transcendence-degree term from the dimension formula. -/
private theorem eq_of_add_eq_natCast {a : ℕ∞} {b c : WithBot ℕ∞} {n : ℕ}
    (hb : (a : WithBot ℕ∞) + b = (n : WithBot ℕ∞))
    (hc : (a : WithBot ℕ∞) + c = (n : WithBot ℕ∞)) : b = c := by
  induction b using WithBot.recBotCoe with
  | bot => rw [WithBot.add_bot] at hb; simp at hb
  | coe b =>
    induction c using WithBot.recBotCoe with
    | bot => rw [WithBot.add_bot] at hc; simp at hc
    | coe c =>
      rw [← WithBot.coe_add] at hb hc
      have hb' : a + b = (n : ℕ∞) := by exact_mod_cast hb
      have hc' : a + c = (n : ℕ∞) := by exact_mod_cast hc
      have ha : a ≠ ⊤ := by
        rintro rfl
        rw [top_add] at hb'
        simp at hb'
      exact congrArg _ (WithTop.add_left_cancel ha (hb'.trans hc'.symm))

/-- **The Krull dimension of the local ring is preserved by a locally quasi-finite morphism of
schemes of finite type over a field at a point where the two schemes have the same dimension.**
The dimension formula [Stacks, Tag 0A21] on both sides reads the common dimension `n` as the
transcendence degree of the residue field plus the dimension of the local ring, and the two
transcendence degrees agree because quasi-finiteness makes the residue field extension finite
([Stacks, Tag 02NG]), hence algebraic. -/
public theorem ringKrullDim_stalk_eq_of_locallyQuasiFinite_over_field (k : Type u) [Field k]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (g : Y ⟶ X)
    (hg : g ≫ pX = pY) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [LocallyQuasiFinite g]
    {n : ℕ} (y : Y) (hX : topologicalKrullDimAt X (g.base y) = (n : WithBot ℕ∞))
    (hY : topologicalKrullDimAt Y y = (n : WithBot ℕ∞)) :
    ringKrullDim (Y.presheaf.stalk y) = ringKrullDim (X.presheaf.stalk (g.base y)) := by
  have hdX := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X pX (g.base y)
  have hdY := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y pY y
  have htr : let : Algebra k (X.residueField (g.base y)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation (g.base y)).hom.toAlgebra
      let : Algebra k (Y.residueField y) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
      Algebra.trdeg k (Y.residueField y) = Algebra.trdeg k (X.residueField (g.base y)) := by
    intro _ _
    let : Algebra (X.residueField (g.base y)) (Y.residueField y) :=
      (g.residueFieldMap y).hom.toAlgebra
    have := isScalarTower_residueField_of_comp k pX pY g hg y
    have : Module.Finite (X.residueField (g.base y)) (Y.residueField y) :=
      g.finite_residueField_of_quasiFiniteAt y (g.quasiFiniteAt y)
    have h0 : Algebra.trdeg (X.residueField (g.base y)) (Y.residueField y) = 0 :=
      trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)
    have hsum := trdeg_add_eq (A := ↥(Y.residueField y)) k ↥(X.residueField (g.base y))
    rw [h0, add_zero] at hsum
    exact hsum.symm
  dsimp only at hdX hdY htr
  rw [hX] at hdX
  rw [hY, htr] at hdY
  exact eq_of_add_eq_natCast hdY.symm hdX.symm

/-! ### Regularity of the local rings of a fibre of a smooth morphism -/

/-- A fibre of a morphism smooth of relative dimension `n` is smooth of relative dimension `n`
over the residue field of the point: smoothness of relative dimension `n` is stable under base
change. -/
public theorem smoothOfRelativeDimension_fiberToSpecResidueField {X S : Scheme.{u}} (p : X ⟶ S)
    (n : ℕ) [SmoothOfRelativeDimension n p] (s : S) :
    SmoothOfRelativeDimension n (p.fiberToSpecResidueField s) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).of_isPullback
    (IsPullback.of_hasPullback p (S.fromSpecResidueField s)) inferInstance

/-- A fibre of a morphism smooth of relative dimension `n` is smooth over the residue field. -/
private theorem smooth_fiberToSpecResidueField {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ)
    [SmoothOfRelativeDimension n p] (s : S) : Smooth (p.fiberToSpecResidueField s) :=
  have := smoothOfRelativeDimension_fiberToSpecResidueField p n s
  SmoothOfRelativeDimension.smooth n (p.fiberToSpecResidueField s)

/-- The local rings of a fibre of a morphism smooth of relative dimension `n` are regular: the
fibre is smooth over the residue field of the point. -/
@[ega "IV 17.5.8" "(iii), special case"]
public theorem isRegularLocalRing_stalk_fiber_of_smoothOfRelativeDimension {X S : Scheme.{u}}
    (p : X ⟶ S) (n : ℕ) [SmoothOfRelativeDimension n p] (s : S) (z : p.fiber s) :
    IsRegularLocalRing ((p.fiber s).presheaf.stalk z) :=
  have := smooth_fiberToSpecResidueField p n s
  isRegularLocalRing_stalk_of_smooth_over_field
    (k := ↥(S.residueField s)) (p.fiberToSpecResidueField s) z

end AlgebraicGeometry

namespace Stacks.Discriminant

/-! ### Tag 0BWJ, flatness -/

/-- **The induced morphism of fibres over `S` is flat.**  Both fibres are smooth of relative
dimension `n` over `κ(s)`, so their local rings are regular of the same Krull dimension, and the
fibre ring of the stalk map is zero-dimensional because the morphism of fibres is locally
quasi-finite; miracle flatness [Stacks, Tag 00R4] applies. -/
public theorem flat_fiberHom {S X Y : Scheme.{u}} (pX : X ⟶ S) (f : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n pX] [SmoothOfRelativeDimension n (f ≫ pX)]
    [LocallyQuasiFinite f] (s : S) : Flat (Stacks.Flatness.fiberHom f pX s) := by
  set g := Stacks.Flatness.fiberHom f pX s
  have : LocallyQuasiFinite g :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyQuasiFinite)
      (Stacks.Flatness.isPullback_fiberHom f pX s).flip inferInstance
  have := smooth_fiberToSpecResidueField pX n s
  have := smooth_fiberToSpecResidueField (f ≫ pX) n s
  refine Flat.of_stalkMap g fun z => ?_
  have : IsRegularLocalRing ((pX.fiber s).presheaf.stalk (g.base z)) :=
    isRegularLocalRing_stalk_fiber_of_smoothOfRelativeDimension pX n s (g.base z)
  have : IsRegularLocalRing (((f ≫ pX).fiber s).presheaf.stalk z) :=
    isRegularLocalRing_stalk_fiber_of_smoothOfRelativeDimension (f ≫ pX) n s z
  refine flat_stalkMap_of_ringKrullDim_quotient_eq_zero g z
    (ringKrullDim_quotient_stalk_eq_zero_of_locallyQuasiFinite g z) ?_
  exact ringKrullDim_stalk_eq_of_locallyQuasiFinite_over_field ↥(S.residueField s)
    (pX.fiberToSpecResidueField s) ((f ≫ pX).fiberToSpecResidueField s) g
    (Stacks.Flatness.fiberHom_fiberToSpecResidueField f pX s) z
    (topologicalKrullDimAt_fiber_eq_of_smoothOfRelativeDimension pX n s (g.base z))
    (topologicalKrullDimAt_fiber_eq_of_smoothOfRelativeDimension (f ≫ pX) n s z)

/-- **[Stacks, Tag 0BWJ], flatness.**  Let `X` and `Y` be smooth of relative dimension `n` over a
locally Noetherian base `S` and let `f : Y ⟶ X` be a locally quasi-finite morphism over `S`.
Then `f` is flat. -/
@[stacks 0BWJ "`f` is flat, the first assertion of the tag.  The base is assumed only locally
Noetherian; local Noetherianness of `X` and `Y` and flatness of `Y ⟶ S` are derived from
smoothness over `S`, not assumed"]
public theorem flat_of_locallyQuasiFinite {S X Y : Scheme.{u}} (pX : X ⟶ S) (f : Y ⟶ X) (n : ℕ)
    [IsLocallyNoetherian S] [SmoothOfRelativeDimension n pX]
    [SmoothOfRelativeDimension n (f ≫ pX)] [LocallyQuasiFinite f] : Flat f := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_smoothOfRelativeDimension pX n
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_smoothOfRelativeDimension (f ≫ pX) n
  have : Smooth (f ≫ pX) := SmoothOfRelativeDimension.smooth n (f ≫ pX)
  exact flat_of_flat_fiberHom f pX fun s => flat_fiberHom pX f n s

end Stacks.Discriminant

end
