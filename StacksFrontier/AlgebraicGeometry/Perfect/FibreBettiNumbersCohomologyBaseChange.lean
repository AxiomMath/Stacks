module

public import StacksFrontier.AlgebraicGeometry.Perfect.FibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDirectImagePerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiConstructible
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.FlatDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Betti numbers of the fibres of a flat proper family, unconditionally

Let `f : X ⟶ S` be a proper morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of
finite presentation, flat over `S`. For `i ∈ ℤ` let `β_i(s) = dim_{κ(s)} H^i(X_s, ℱ_s)`, which is
`AlgebraicGeometry.FibreBetti.fibreBetti f ℱ i`. [Stacks, Tag 0BDN] says that the formation of
`β_i` commutes with arbitrary base change, that `β_i` is upper semi-continuous and that its level
sets are locally constructible. This file proves all three with no hypothesis beyond the source's.

## Main results

* `AlgebraicGeometry.FibreBetti.fibreBetti_eq_derivedFiberBetti`: the identification
  `H^i(X_s, ℱ_s) = H^i(Rf_*ℱ ⊗^L_{𝒪_S} κ(s))` of the source's proof, as an equality of `β_i` with
  the derived-fibre Betti function of `Rf_*ℱ`.
* `AlgebraicGeometry.FibreBetti.fibreBetti_pullback`: part (1), for one cartesian square.
* `AlgebraicGeometry.FibreBetti.fibreBetti_baseChange_upperSemicontinuous_isLocallyConstructible`:
  [Stacks, Tag 0BDN], all three parts.

## Implementation notes

The proof is the source's. By [Stacks, Tag 0B91] the object `K = Rf_*ℱ` is perfect, and for every
cartesian square `Rf'_*(g')^*ℱ ≅ Lg^*K`. Taking for the square the scheme-theoretic fibre over
`Spec κ(s) ⟶ S` identifies `β_i` with the derived-fibre Betti function of `K`, and then the three
parts are parts (1), (2) and (3) of [Stacks, Tag 0BDI]
(`AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti_derivedPullback`,
`AlgebraicGeometry.DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti` and
`AlgebraicGeometry.DerivedFibreBetti.isLocallyConstructible_derivedFiberBetti_preimage`).

Only the isomorphism class of `Lg^*K` enters, since `β_i` is a dimension. So the base-change
input is used as the existence of an isomorphism and no coherence of the unit constraints is
needed.

## References

* [Stacks Project, Tag 0BDN](https://stacks.math.columbia.edu/tag/0BDN)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.FibreBetti

/-! ### The fibre square -/

/-- **The scheme-theoretic fibre square.** The fibre `X_s` of `f` at `s` is the pullback of `f`
along `Spec κ(s) ⟶ S`. -/
@[ega "II 1.5.3",
  ega "III 4.7.1" "X_y = X ×_Y Spec(κ(y))",
  ega "IV 11.2.8" "partial",
  ega "IV 6.15.3",
  ega "IV 9.4.1" "partial"]
public theorem isPullback_fiberι_fiberToSpecResidueField {X S : Scheme.{u}} (f : X ⟶ S) (s : S) :
    IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f (S.fromSpecResidueField s) :=
  IsPullback.of_hasPullback _ _

/-- **The fibre cohomology computed by a derived fibre.** If `Rf_{s,*}ℱ_s` is isomorphic to the
derived pullback of `K` to `Spec κ(s)`, then `β_i(s)` is the value at `s` of the derived-fibre
Betti function of `K`. Both are the `κ(s)`-dimension of the degree-`i` cohomology of isomorphic
objects of `D(Spec κ(s))`. -/
public theorem fibreBetti_apply_eq_derivedFiberBetti_of_iso {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (i : ℤ) (s : S) (K : DerivedCategory S.Modules)
    (hK : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) K)
    (e : totalDirectImage (f.fiberToSpecResidueField s)
        ((Scheme.Modules.pullback (f.fiberι s)).obj F) ≅
      (derivedPullback (S.fromSpecResidueField s).toLRSHom.toShHom).obj K) :
    fibreBetti f F i s = DerivedFibreBetti.derivedFiberBetti S K hK i s :=
  ((moduleSpecΓFunctor (R := S.residueField s)).mapIso
    ((DerivedCategory.homologyFunctor (Spec (S.residueField s)).Modules i).mapIso
      e)).toLinearEquiv.finrank_eq

/-! ### The hypotheses are stable under base change -/

/-- **The hypotheses of [Stacks, Tag 0BDN] are stable under base change.** In a cartesian square,
`f'` is proper and of finite presentation because `f` is, and `(g')^*ℱ` is of finite
presentation ([Stacks, Tag 01BJ]) and flat over `S'` ([Stacks, Tag 01U8]). -/
public theorem isFlatFamily_pullback {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g) {F : X.Modules}
    (h : IsFlatFamily f F) : IsFlatFamily f' ((Scheme.Modules.pullback g').obj F) where
  finitePresentation :=
    ⟨MorphismProperty.of_isPullback hsq h.finitePresentation.locallyOfFinitePresentation,
      MorphismProperty.of_isPullback hsq h.finitePresentation.quasiCompact,
      MorphismProperty.of_isPullback hsq h.finitePresentation.quasiSeparated⟩
  isProper := MorphismProperty.of_isPullback hsq h.isProper
  isFinitePresentation :=
    have := h.isFinitePresentation
    Stacks.StalkFiniteType.isFinitePresentation_pullback g' F
  isFlatOver := by
    have := h.isFinitePresentation
    have : F.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation F
    have := isQuasicoherent_ringSheaf F
    exact modulePullback_isFlatOver hsq F h.isFlatOver

/-! ### Cohomology and base change -/

/-- **`Rf_*ℱ` is pseudo-coherent.** It is perfect by [Stacks, Tag 0B91], and a perfect object is
pseudo-coherent. -/
public theorem isPseudoCoherent_totalDirectImage {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    (h : IsFlatFamily f F) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (totalDirectImage f F) :=
  DerivedFibreBetti.isPseudoCoherent_of_isPerfect (X := S.toRingedSpace) _
    (ProperFlatDirectImage.isPerfect_derivedPushforwardModule f h.finitePresentation h.isProper F
      h.isFinitePresentation h.isFlatOver)

/-- **`Rf'_*(g')^*ℱ ≅ Lg^*Rf_*ℱ`** for a cartesian square and a flat family `(f, ℱ)`. -/
private theorem nonempty_totalDirectImage_iso_derivedPullback {X S X' S' : Scheme.{u}}
    {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g)
    {F : X.Modules} (h : IsFlatFamily f F) :
    Nonempty (totalDirectImage f' ((Scheme.Modules.pullback g').obj F) ≅
      (derivedPullback g.toLRSHom.toShHom).obj (totalDirectImage f F)) :=
  (ProperFlatDirectImage.nonempty_derivedPullback_derivedPushforwardModule_iso f
    h.finitePresentation F h.isFinitePresentation h.isFlatOver g f' g' hsq).map Iso.symm

/-- **`H^i(X_s, ℱ_s) = H^i(Rf_*ℱ ⊗^L_{𝒪_S} κ(s))`.** The Betti function `β_i` of the family is the
derived-fibre Betti function of `Rf_*ℱ`. This is the identification in the source's proof. It
comes from the base-change half of [Stacks, Tag 0B91], applied to the fibre square over
`Spec κ(s) ⟶ S`. -/
public theorem fibreBetti_eq_derivedFiberBetti {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules}
    (h : IsFlatFamily f F) (i : ℤ) :
    fibreBetti f F i = DerivedFibreBetti.derivedFiberBetti S (totalDirectImage f F)
      (isPseudoCoherent_totalDirectImage h) i := by
  funext s
  obtain ⟨e⟩ := nonempty_totalDirectImage_iso_derivedPullback
    (isPullback_fiberι_fiberToSpecResidueField f s) h
  exact fibreBetti_apply_eq_derivedFiberBetti_of_iso f F i s _ _ e

/-- **Part (1) of [Stacks, Tag 0BDN], for one cartesian square.** If `g : S' ⟶ S` is any
morphism and `X' = X ×_S S'`, then the Betti function of `(f', (g')^*ℱ)` is `β_i ∘ g`.

Both sides are derived-fibre Betti functions (`fibreBetti_eq_derivedFiberBetti`, which applies to
the base change by `isFlatFamily_pullback`). The two objects are related by
`Rf'_*(g')^*ℱ ≅ Lg^*Rf_*ℱ` ([Stacks, Tag 0B91]), and part (1) of [Stacks, Tag 0BDI] does the
rest. -/
public theorem fibreBetti_pullback {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} (hsq : IsPullback g' f' f g) {F : X.Modules}
    (h : IsFlatFamily f F) (i : ℤ) :
    fibreBetti f' ((Scheme.Modules.pullback g').obj F) i = fibreBetti f F i ∘ g.base := by
  obtain ⟨e⟩ := nonempty_totalDirectImage_iso_derivedPullback hsq h
  rw [fibreBetti_eq_derivedFiberBetti (isFlatFamily_pullback hsq h) i,
    derivedFiberBetti_eq_of_iso S' _
      (DerivedFibreBetti.isPseudoCoherent_derivedPullback g _ (isPseudoCoherent_totalDirectImage h))
      e i,
    DerivedFibreBetti.derivedFiberBetti_derivedPullback g _ _ i,
    fibreBetti_eq_derivedFiberBetti h i]

/-! ### Stacks 0BDN -/

/-- **[Stacks, Tag 0BDN].** Let `f : X ⟶ S` be a proper morphism of finite presentation and let
`ℱ` be an `𝒪_X`-module of finite presentation, flat over `S`. Fix `i ∈ ℤ` and let `β_i` be the
function `s ↦ dim_{κ(s)} H^i(X_s, ℱ_s)` (`AlgebraicGeometry.FibreBetti.fibreBetti`). Then

1. the formation of `β_i` commutes with arbitrary base change: for every cartesian square with
   `g : S' ⟶ S`, `f' : X' ⟶ S'` and `g' : X' ⟶ X`, the function `β_i` of `(f', (g')^*ℱ)` is
   `β_i ∘ g`;
2. `β_i` is upper semi-continuous;
3. every level set `β_i⁻¹{n}` is locally constructible in `S`.

The proof is the source's. By [Stacks, Tag 0B91], `β_i` is the derived-fibre Betti function of
the perfect object `Rf_*ℱ` (`fibreBetti_eq_derivedFiberBetti`), so the three parts are parts (1),
(2) and (3) of [Stacks, Tag 0BDI]. -/
@[stacks 0BDN, sga "6 III 5.7" "(ii), special case"]
public theorem fibreBetti_baseChange_upperSemicontinuous_isLocallyConstructible
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) [IsProper f] (F : X.Modules)
    [F.IsFinitePresentation] (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) :
    (∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
        IsPullback g' f' f g →
          fibreBetti f' ((Scheme.Modules.pullback g').obj F) i = fibreBetti f F i ∘ g.base) ∧
      UpperSemicontinuous (fibreBetti f F i) ∧
      ∀ n : ℕ, IsLocallyConstructible (fibreBetti f F i ⁻¹' {n}) := by
  have h : IsFlatFamily f F := ⟨hf, inferInstance, inferInstance, hflat⟩
  refine ⟨fun g f' g' hsq => fibreBetti_pullback hsq h i, ?_, fun n => ?_⟩
  · rw [fibreBetti_eq_derivedFiberBetti h i]
    exact DerivedFibreBetti.upperSemicontinuous_derivedFiberBetti S _ _ i
  · rw [fibreBetti_eq_derivedFiberBetti h i]
    exact DerivedFibreBetti.isLocallyConstructible_derivedFiberBetti_preimage S _ _ i n

end AlgebraicGeometry.FibreBetti

end
