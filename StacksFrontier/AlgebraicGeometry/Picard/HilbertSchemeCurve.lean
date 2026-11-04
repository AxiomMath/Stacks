module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineFibresRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeGroupSchemeQuotient
public import StacksFrontier.AlgebraicGeometry.HilbertFibreAffineOpen.Basic
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSeparated
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AlgClosedField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Hilbert schemes of points of a proper curve

For a proper curve `X` over a field `k` the degree-`d` Hilbert functors of `X` are representable
([Stacks, Tag 0B9I], first assertion of (1)): a proper curve carries an ample invertible module
(Tag 09ND), so every finite set of points lies in an affine open (Tag 0B9B), and Tag 0B9A
applies. For a smooth curve the representing schemes are smooth of relative dimension `d`
(Tag 0B9H) and proper, by induction along the point-addition morphisms (Tag 0B9G).

## Main results

* `AlgebraicGeometry.hasAffineFinitePointsInFibres_of_isCurve`: finite sets of points of a proper
  curve lie in affine opens.
* `Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_isCurve`: representability.
* `Stacks.Hilbert.smoothOfRelativeDimension_and_isProper_of_isCurve`: for a smooth proper curve,
  every representing scheme is smooth of relative dimension `d` and proper (Tag 0B9I, (1)).
* `Stacks.Hilbert.rationalPointsEquivEffectiveCartierDivisors`: rational points over field
  extensions are effective Cartier divisors of degree `d` (Tag 0B9I, (2)).
* `Stacks.Hilbert.isRelativeEffectiveCartierDivisor_univ_iso_prod_and_restrict_picardClass`: the
  universal divisor `D_univ ⊆ X ×_k H^{d+1}` is a relative effective Cartier divisor isomorphic to
  `H^d ×_k X`, and `𝒪(D_univ)` restricts to `𝒪_X(D)` on the fibre at a rational point (Tag 0B9J).
* `Stacks.Hilbert.isVariety_and_topologicalKrullDim_of_isCurve`: for a geometrically irreducible
  smooth proper curve, every representing scheme is a variety of dimension `d` (Tag 0B9I, (1)).

Tag 0B9I as a whole, with representability in (1) and the addition morphisms of (3), is assembled
in `StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeProperCurve`.

## References

* [Stacks Project, Tag 0B9I](https://stacks.math.columbia.edu/tag/0B9I)
* [Stacks Project, Tag 0B9B](https://stacks.math.columbia.edu/tag/0B9B)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Finite sets of points of a proper curve lie in affine opens**: a proper curve over a field
carries an ample invertible module (Tag 09ND). -/
theorem hasAffineFinitePointsInFibres_of_isCurve [IsProper f] [IsCurve k f] :
    HasAffineFinitePointsInFibres f := by
  have : IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  obtain ⟨A, hA, hample⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f))
  have : Stacks.Ample.IsInvertibleModule X A :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hA
  exact Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_modulesIsAmple f A hample

end AlgebraicGeometry

namespace Stacks.Hilbert

/-- **The Hilbert functors of a proper curve are representable** (Stacks 0B9I, the
representability in (1)). -/
theorem nonempty_representsHilbertFunctorOfRank_of_isCurve (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] (d : ℕ) :
    Nonempty (Σ H : Over (Spec (.of k)), RepresentsHilbertFunctorOfRank (Over.mk f) H d) :=
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  exists_representsHilbertFunctorOfRank_of_affineFibres (Over.mk f) d fun s x hx ↦ by
    obtain ⟨U, hU, hsub⟩ := hasAffineFinitePointsInFibres_of_isCurve k f s (Set.range x)
      (Set.finite_range x) (Set.range_subset_iff.2 hx)
    exact ⟨U, hU, fun i ↦ hsub ⟨i, rfl⟩⟩

/-- Properties of the structure morphism of a representing scheme do not depend on the choice of
the representing scheme: two representing schemes are isomorphic over `S`. -/
theorem hom_eq_comp_isoOver {S : Scheme.{u}} {X H H' : Over S} {d : ℕ}
    (h : RepresentsHilbertFunctorOfRank X H d) (h' : RepresentsHilbertFunctorOfRank X H' d) :
    H.hom = (h.isoOver h').hom.left ≫ H'.hom :=
  (Over.w (h.isoOver h').hom).symm

/-- The structure morphism of a product `H ×_S X` with a proper `X ⟶ S` is proper when that of
`H` is. -/
@[ega "II 5.4.2" "(iv), special case"]
theorem isProper_prod_hom {S : Scheme.{u}} (H X : Over S) [IsProper X.hom] [IsProper H.hom] :
    IsProper (H ⨯ X).hom := by
  have hpull : IsProper (pullback.fst H.hom X.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback H.hom X.hom).flip inferInstance
  have hsq : IsPullback (Over.prodLeftIsoPullback H X).hom
      ((prod.fst : H ⨯ X ⟶ H).left) (pullback.fst H.hom X.hom) (𝟙 H.left) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, Over.prodLeftIsoPullback_hom_fst]⟩
  have hfst : IsProper ((prod.fst : H ⨯ X ⟶ H).left) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) hsq hpull
  rw [← Over.w (prod.fst : H ⨯ X ⟶ H)]
  infer_instance

/-- Point addition `H ×_S X ⟶ H'` is surjective. -/
private theorem surjective_addPoint_left {S : Scheme.{u}} {X H H' : Over S} {d : ℕ}
    [IsSeparated X.hom] [SmoothOfRelativeDimension 1 X.hom]
    (hH : RepresentsHilbertFunctorOfRank X H d)
    (hH' : RepresentsHilbertFunctorOfRank X H' (d + 1)) : Surjective (addPoint hH hH').left :=
  have := (isPointAddition_addPoint hH hH').isFiniteLocallyFreeOfRank_left
  Stacks.Morphisms.surjective_of_isFiniteLocallyFreeOfRank _ (d + 1) (Nat.succ_ne_zero d)

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Stacks Project, Tag 0B9I, (1), smoothness and properness.** Let `X` be a smooth proper
curve over a field `k`. Every scheme representing the degree-`d` Hilbert functor of `X` is smooth
of relative dimension `d` and proper over `k`.

Smoothness is Tag 0B9H; properness follows by induction on `d` from the point-addition morphisms
`H^d ×_k X ⟶ H^{d+1}` of Tag 0B9G, which are finite locally free of degree `d + 1`, hence
surjective, so that `H^{d+1}` is universally closed over `k` (Tag 03GN), and separated by Tag
0B98. -/
@[stacks 0B9I "(1), ingredient: every representing scheme is smooth of relative dimension d and \
proper. The whole of (1), with representability, is \
Stacks.Hilbert.exists_representsHilbertFunctorOfRank_isVariety_of_isCurve"]
theorem smoothOfRelativeDimension_and_isProper_of_isCurve [IsProper f] [IsCurve k f] [Smooth f]
    (d : ℕ) (H : Over (Spec (.of k))) (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    SmoothOfRelativeDimension d H.hom ∧ IsProper H.hom := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    smoothOfRelativeDimension_one_of_isCurve k f
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : IsProper (Over.mk f).hom := inferInstanceAs (IsProper f)
  let Hc : ℕ → Over (Spec (.of k)) := fun d ↦
    (nonempty_representsHilbertFunctorOfRank_of_isCurve k f d).some.1
  let hHc : ∀ d, RepresentsHilbertFunctorOfRank (Over.mk f) (Hc d) d := fun d ↦
    (nonempty_representsHilbertFunctorOfRank_of_isCurve k f d).some.2
  have hsm : ∀ d, SmoothOfRelativeDimension d (Hc d).hom :=
    smoothOfRelativeDimension_of_represents Hc hHc
  have hpr (d : ℕ) : IsProper (Hc d).hom := by
    induction d with
    | zero =>
      have := isIso_hom_of_representsHilbertFunctorOfRank_zero (hHc 0)
      infer_instance
    | succ d ih =>
      have := isProper_prod_hom (Hc d) (Over.mk f)
      have := hsm (d + 1)
      have : Smooth (Hc (d + 1)).hom := SmoothOfRelativeDimension.smooth (d + 1) _
      have : IsSeparated (Hc (d + 1)).hom :=
        isSeparated_of_representsHilbertFunctorOfRank _ _ _ (hHc (d + 1))
      let p := addPoint (hHc d) (hHc (d + 1))
      have := surjective_addPoint_left (hHc d) (hHc (d + 1))
      have : UniversallyClosed (p.left ≫ (Hc (d + 1)).hom) := by
        rw [Over.w p]
        infer_instance
      have : UniversallyClosed (Hc (d + 1)).hom :=
        UniversallyClosed.of_comp_surjective p.left _
      exact ⟨⟩
  have := hsm d
  have := hpr d
  rw [hom_eq_comp_isoOver hH (hHc d)]
  have h0 : SmoothOfRelativeDimension (0 + d) ((hH.isoOver (hHc d)).hom.left ≫ (Hc d).hom) :=
    inferInstance
  rw [zero_add] at h0
  exact ⟨h0, inferInstance⟩

/-- An isomorphism of schemes carries irreducibility across. -/
theorem irreducibleSpace_of_iso {Y Y' : Scheme.{u}} (e : Y ≅ Y') [IrreducibleSpace Y] :
    IrreducibleSpace Y' :=
  Function.Surjective.irreducibleSpace e.hom.continuous (Scheme.homeoOfIso e).surjective

/-- **Stacks Project, Tag 0B9I, (1), the varieties.** Let `X` be a geometrically irreducible
smooth proper curve over a field `k`. Every scheme representing the degree-`d` Hilbert functor of
`X` is a variety of dimension `d` over `k`.

By induction on `d`: `H^0` is a point, and `H^{d+1}` is the image of the irreducible scheme
`H^d ×_k X` (Tag 038F) under the surjective point-addition morphism of Tag 0B9G; smooth and
connected over a field it is integral, and its dimension is its relative dimension `d`. -/
@[stacks 0B9I "(1), ingredient: every representing scheme is a variety of dimension d. The whole \
of (1), with representability, is \
Stacks.Hilbert.exists_representsHilbertFunctorOfRank_isVariety_of_isCurve"]
theorem isVariety_and_topologicalKrullDim_of_isCurve [IsProper f] [IsCurve k f] [Smooth f]
    [GeometricallyIrreducible f] (d : ℕ) (H : Over (Spec (.of k)))
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    IsVariety k H.hom ∧ topologicalKrullDim H.left = d := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    smoothOfRelativeDimension_one_of_isCurve k f
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : GeometricallyIrreducible (Over.mk f).hom := inferInstanceAs (GeometricallyIrreducible f)
  have : Smooth (Over.mk f).hom := inferInstanceAs (Smooth f)
  let Hc : ℕ → Over (Spec (.of k)) := fun d ↦
    (nonempty_representsHilbertFunctorOfRank_of_isCurve k f d).some.1
  let hHc : ∀ d, RepresentsHilbertFunctorOfRank (Over.mk f) (Hc d) d := fun d ↦
    (nonempty_representsHilbertFunctorOfRank_of_isCurve k f d).some.2
  have hirr (d : ℕ) : IrreducibleSpace (Hc d).left := by
    induction d with
    | zero =>
      have := isIso_hom_of_representsHilbertFunctorOfRank_zero (hHc 0)
      exact irreducibleSpace_of_iso (asIso (Hc 0).hom).symm
    | succ d ih =>
      have : IrreducibleSpace (Hc d ⨯ Over.mk f).left :=
        irreducibleSpace_of_iso (Over.prodLeftIsoPullback (Hc d) (Over.mk f)).symm
      exact Function.Surjective.irreducibleSpace (addPoint (hHc d) (hHc (d + 1))).left.continuous
        (surjective_addPoint_left (hHc d) (hHc (d + 1))).surj
  have : IrreducibleSpace H.left :=
    @irreducibleSpace_of_iso _ _ ((Over.forget _).mapIso (hH.isoOver (hHc d))).symm (hirr d)
  obtain ⟨_, _⟩ := smoothOfRelativeDimension_and_isProper_of_isCurve k f d H hH
  have : Smooth H.hom := SmoothOfRelativeDimension.smooth d _
  have : IsIntegral H.left := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth H.hom
  exact ⟨{ }, topologicalKrullDim_eq_of_smoothOfRelativeDimension H.hom d⟩

/-- The base change `X_{k'}` of `X` to a field extension `k'`, as a scheme over `k`. -/
abbrev fieldExtOver (k' : Type u) [Field k'] [Algebra k k'] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k')))

/-- **Stacks Project, Tag 0B9I, (2).** Let `X` be a smooth proper curve over a field `k` and `H`
a scheme representing the degree-`d` Hilbert functor of `X`. For a field extension `k'/k`, the
`k'`-rational points of `H` correspond bijectively to the effective Cartier divisors of degree
`d` on `X_{k'}`: the closed subschemes of `X_{k'}` which are effective Cartier divisors, finite
locally free of rank `d` over `k'`.

The correspondence is representability; every degree-`d` family over `k'` is an effective
Cartier divisor by Tag 0B9D. -/
@[stacks 0B9I "(2)"]
def rationalPointsEquivEffectiveCartierDivisors [IsProper f] [IsCurve k f] [Smooth f] (d : ℕ)
    (H : Over (Spec (.of k))) (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (k' : Type u) [Field k'] [Algebra k k'] :
    (fieldExtOver k k' ⟶ H) ≃
      {I : ((Over.pullback (fieldExtOver k k').hom).obj (Over.mk f)).left.IdealSheafData //
        Stacks.Divisors.IsEffectiveCartierDivisor I ∧
          Stacks.Morphisms.IsFiniteLocallyFreeOfRank
            (I.subschemeι ≫ ((Over.pullback (fieldExtOver k k').hom).obj (Over.mk f)).hom) d} :=
  haveI : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    smoothOfRelativeDimension_one_of_isCurve k f
  hH.family.trans
    { toFun := fun Z ↦ ⟨Z.ideal, Z.isEffectiveCartierDivisor_ideal, Z.isFiniteLocallyFreeOfRank⟩
      invFun := fun I ↦ ⟨I.1, I.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The divisor of a rational point of the Hilbert scheme is the ideal of the family it
classifies. -/
theorem rationalPointsEquivEffectiveCartierDivisors_apply [IsProper f] [IsCurve k f] [Smooth f]
    (d : ℕ) (H : Over (Spec (.of k))) (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (k' : Type u) [Field k'] [Algebra k k'] (x : fieldExtOver k k' ⟶ H) :
    (rationalPointsEquivEffectiveCartierDivisors k f d H hH k' x).1 = (hH.family x).ideal :=
  rfl

/-- **The universal divisor and `𝒪(D_univ)`.** Let `X` be a smooth proper curve over a field `k`
and `H` a scheme representing the degree-`d` Hilbert functor of `X`. The universal closed
subscheme `D_univ ⊆ H ×_k X` is a relative effective Cartier divisor over `H` (Tag 0B9D), and for
every rational point `[D]` of `H` the restriction of the invertible sheaf `𝒪(D_univ)` to the fibre
`[D] × X = X` is `𝒪_X(D)` (Tag 0C4U). This is part of Stacks Tag 0B9J; the whole remark is
`Stacks.Hilbert.isRelativeEffectiveCartierDivisor_univ_iso_prod_and_restrict_picardClass`. -/
theorem isRelativeEffectiveCartierDivisor_univ_and_restrict_picardClass [IsProper f] [IsCurve k f]
    [Smooth f] (d : ℕ) (H : Over (Spec (.of k)))
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d) :
    haveI : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
      smoothOfRelativeDimension_one_of_isCurve k f
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor ((Over.pullback H.hom).obj (Over.mk f)).hom
        (hH.family (𝟙 H)).ideal ∧
      ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ H,
        Stacks.Picard.schemePullbackClass (familyBaseChangeMap (Over.mk f) x)
          (hH.family (𝟙 H)).picardClass = (hH.family x).picardClass := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    smoothOfRelativeDimension_one_of_isCurve k f
  refine ⟨?_, fun x ↦ (hH.family (𝟙 H)).schemePullbackClass_picardClass _ _
    (by simpa only [Category.comp_id] using hH.naturality x (𝟙 H))⟩
  have : SmoothOfRelativeDimension 1 ((Over.pullback H.hom).obj (Over.mk f)).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback (Over.mk f).hom H.hom) inferInstance
  have := (hH.family (𝟙 H)).isFiniteLocallyFreeOfRank
  have : Stacks.Morphisms.IsFiniteLocallyFree ((hH.family (𝟙 H)).ideal.subschemeι ≫
      ((Over.pullback H.hom).obj (Over.mk f)).hom) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
  exact AlgebraicGeometry.isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree _ _

/-- **Stacks Project, Tag 0B9J.** Let `X` be a smooth proper curve over a field `k`, let `d ≥ 0`,
and let `H` and `H'` be schemes representing the Hilbert functors `Hilb^d_{X/k}` and
`Hilb^{d+1}_{X/k}` (they exist by Tag 0B9I). Write `D_univ ⊆ X ×_k H'` for the universal closed
subscheme. Then

* `D_univ` is a relative effective Cartier divisor over `H'` (Tag 0B9D);
* `D_univ` is isomorphic as a scheme to `H ×_k X`, by an isomorphism under which the inclusion
  `D_univ ⊆ X ×_k H'` becomes `(D, x) ↦ (x, D + x)`, the point and point addition
  `Stacks.Hilbert.addPoint` of Tag 0B9G (see the proof of Tag 0B9G);
* in particular `D_univ` is an effective Cartier divisor on `X ×_k H'` and its sheaf
  `𝒪(D_univ)` is invertible;
* for a `k`-rational point `[D]` of `H'`, classifying the effective Cartier divisor `D` of degree
  `d + 1` on the fibre `[D] × X = X ×_k k`, the restriction of `𝒪(D_univ)` to that fibre is
  `𝒪_X(D)`, as classes in the Picard group of the fibre.

The source assumes `X` geometrically irreducible, as in Tag 0B9I; that hypothesis is not used, and
is dropped. -/
@[stacks 0B9J]
theorem isRelativeEffectiveCartierDivisor_univ_iso_prod_and_restrict_picardClass [IsProper f]
    [IsCurve k f] [Smooth f] (d : ℕ) (H H' : Over (Spec (.of k)))
    (hH : RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (hH' : RepresentsHilbertFunctorOfRank (Over.mk f) H' (d + 1)) :
    haveI : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
      smoothOfRelativeDimension_one_of_isCurve k f
    haveI : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor ((Over.pullback H'.hom).obj (Over.mk f)).hom
        (hH'.family (𝟙 H')).ideal ∧
      (∃ e : (H ⨯ Over.mk f).left ≅ (hH'.family (𝟙 H')).ideal.subscheme,
        e.hom ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ pullback.fst f H'.hom =
            (prod.snd : H ⨯ Over.mk f ⟶ Over.mk f).left ∧
          e.hom ≫ (hH'.family (𝟙 H')).ideal.subschemeι ≫ pullback.snd f H'.hom =
            (addPoint hH hH').left) ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (hH'.family (𝟙 H')).ideal ∧
      AlgebraicGeometry.SheafOfModules.IsInvertible _
        (_root_.structureSheafRing
          ((Over.pullback H'.hom).obj (Over.mk f)).left.toRingedSpace).property
        (Stacks.Divisors.invertibleSheaf' (hH'.family (𝟙 H')).ideal) ∧
      ∀ x : Over.mk (𝟙 (Spec (.of k))) ⟶ H',
        Stacks.Picard.schemePullbackClass (familyBaseChangeMap (Over.mk f) x)
          (hH'.family (𝟙 H')).picardClass = (hH'.family x).picardClass := by
  have : SmoothOfRelativeDimension 1 (Over.mk f).hom :=
    smoothOfRelativeDimension_one_of_isCurve k f
  have : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  obtain ⟨hrel, hres⟩ := isRelativeEffectiveCartierDivisor_univ_and_restrict_picardClass k f
    (d + 1) H' hH'
  have := hrel.1
  exact ⟨hrel, (isPointAddition_addPoint hH hH').exists_iso_universalFamily_subscheme, hrel.1,
    Stacks.Divisors.invertibleSheaf_isInvertible _, hres⟩

end Stacks.Hilbert

end
