module

public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPullbackGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# Blowing up complexes, II: Stacks tag 0F8V for a general base change

Let `(X, D, M)` be a triple as in Situation 0F8S, let `b : X' ⟶ X` be a morphism with the two
properties of Stacks tag 0GTY for it, and let `Q = Lη_{ℐ'} Lb^*M` be the perfect object of tag
0F8U.  Let `h : Y ⟶ X` be a morphism along which `E = h⁻¹D` is defined, and let `c : Y' ⟶ Y`
have the two properties of tag 0GTY for `(Y, E, Lh^*M)`.  Stacks tag 0F8V identifies
`Lη_{𝒥'} L(h ∘ c)^*M = L(Y' ⟶ X')^* Q` and, for an already good triple `(Y, E, Lh^*M)`,
`Lη_𝒥 Lh^*M = Lk^* Q` for the unique `k : Y ⟶ X'` with `h = b ∘ k`.

The morphism `h' : Y' ⟶ X'` is produced by property (2) of `b` applied to `c ∘ h`, which is
good for `(X, D, M)` by `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_comp`.  The
identification is tag 0F9X,
`AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullback_derivedEta_iso`, at the
triple `(X', b⁻¹D, Lb^*M)`, followed by the bookkeeping of
`AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_etaDerivedPullbackObject_comp`.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_comp`: a triple is good over `c ∘ h`
  exactly when its pullback along `h` has a good pullback along `c`.
* `AlgebraicGeometry.ComplexAndDivisorSituation`
  `.exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodBlowup`: **the displayed
  identification of tag 0F8V**, for the general `c`.
* `AlgebraicGeometry.ComplexAndDivisorSituation`
  `.exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver`: **the final assertion
  of tag 0F8V**, the case `c = 𝟙_Y`.

## References

* [Stacks Project, Tag 0F8V](https://stacks.math.columbia.edu/tag/0F8V)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The décalage of the pulled-back object depends on the morphism only.**  Two equal
morphisms give the same object; the two definedness proofs need no reconciliation, being
proofs of a `Prop`. -/
private theorem etaDerivedPullbackObject_congr (S : ComplexAndDivisorSituation.{u, d})
    {Z : Scheme.{u}} {a a' : Z ⟶ S.X} (haa : a = a')
    (ha : Stacks.Divisors.IsPullbackDefined a S.D)
    (ha' : Stacks.Divisors.IsPullbackDefined a' S.D) :
    S.etaDerivedPullbackObject a ha = S.etaDerivedPullbackObject a' ha' := by
  subst haa
  rfl

/-- A good triple stays good when its divisor is replaced by an equal one and its object by an
isomorphic one: a chart for one is a chart for the other, with the same open, equation and
complex. -/
private theorem isGoodTriple_of_eq_of_nonempty_iso {Z : Scheme.{u}} {D D' : Z.IdealSheafData}
    (hDD : D = D') (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (hD' : Stacks.Divisors.IsEffectiveCartierDivisor D')
    {M M' : DerivedCategory (OXMod.{u, u} Z.toRingedSpace)} (hM : RingedSpace.IsPerfect M)
    (hM' : RingedSpace.IsPerfect M') (e : Nonempty (M ≅ M'))
    (hgood : IsGoodTriple
      { X := Z, D := D, isEffectiveCartierDivisor := hD, M := M, isPerfect := hM }) :
    IsGoodTriple
      { X := Z, D := D', isEffectiveCartierDivisor := hD', M := M', isPerfect := hM' } := by
  subst hDD
  obtain ⟨e⟩ := e
  intro x hx
  obtain ⟨C, hxC, hprin⟩ := hgood x hx
  obtain ⟨E, ⟨hE⟩, hE'⟩ := C.represents
  exact ⟨{ U := C.U
           f := C.f
           regular := C.regular
           divisor_ideal := C.divisor_ideal
           complex := C.complex
           represents := ⟨E, ⟨hE ≪≫ e⟩, hE'⟩ }, hxC, hprin⟩

/-- **Pulling back in two steps is being good over the composite.**  The pullback of `(X, D, M)`
along `h` has its own pullback along `c` good exactly when `c ∘ h` is good for `(X, D, M)`.

The two triples `(Y', (c ∘ h)^{-1}D, L(c ∘ h)^*M)` and `(Y', c^{-1}(h^{-1}D), Lc^*Lh^*M)` have
the same scheme, the same divisor — `AlgebraicGeometry.Scheme.IdealSheafData.comap_comp` is an
equality of ideal sheaf data — and the same model of the derived category, and their objects are
isomorphic by `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullbackObject_comp`.
An affine chart for one is therefore an affine chart for the other, with the same open, the same
equation and the same complex, so the determinantal ideals and their principality are untouched;
and the isomorphism of objects may be used in either direction, which is why the two goodness
statements are equivalent and not merely one-way. -/
theorem isGoodOver_comp (S : ComplexAndDivisorSituation.{u, d}) {Y Y' : Scheme.{u}}
    (h : Y ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined h S.D) (c : Y' ⟶ Y)
    (hc : Stacks.Divisors.IsPullbackDefined c (S.D.comap h)) :
    S.IsGoodOver (c ≫ h) ↔ IsGoodTriple ((S.pullback h hD).pullback c hc) := by
  have hDD : S.D.comap (c ≫ h) = (S.D.comap h).comap c :=
    Scheme.IdealSheafData.comap_comp S.D c h
  have hch : Stacks.Divisors.IsPullbackDefined (c ≫ h) S.D := by
    rw [show Stacks.Divisors.IsPullbackDefined (c ≫ h) S.D =
      Stacks.Divisors.IsEffectiveCartierDivisor (S.D.comap (c ≫ h)) from rfl, hDD]
    exact hc
  obtain ⟨e⟩ := S.nonempty_derivedPullbackObject_comp h hD c
  exact ⟨fun hgood => isGoodTriple_of_eq_of_nonempty_iso hDD _ _ _ _ ⟨e.symm⟩ hgood.isGoodTriple,
    fun hgood => ⟨hch, isGoodTriple_of_eq_of_nonempty_iso hDD.symm _ _ _ _ ⟨e⟩ hgood⟩⟩

/-- **Stacks tag 0F8V, the displayed identification.**  Let `(X, D, M)` be a triple as in
Situation 0F8S, let `b : X' ⟶ X` have the two properties of tag 0GTY for `(X, D, M)`, and let
`Q = Lη_{ℐ'} Lb^*M` be the object of tag 0F8U.  Let `h : Y ⟶ X` be a morphism along which
`E = h^{-1}D` is defined and let `c : Y' ⟶ Y` have the two properties of tag 0GTY for
`(Y, E, Lh^*M)`.  Then there is a morphism `h' : Y' ⟶ X'` with `h' ∘ b = c ∘ h` — unique, by
property (2) of tag 0GTY — and for it

`Lη_{𝒥'} L(h ∘ c)^*M ≅ Lh'^* Q`,

where `𝒥'` is the ideal sheaf of `E' = c^{-1}E = (c ∘ h)^{-1}D`.

The morphism `h'` is produced by property (2) of `b` applied to `c ∘ h`, which is good for
`(X, D, M)` by `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodOver_comp`.  The
identification is tag 0F9X
(`AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_derivedPullback_derivedEta_iso`) at the
triple `(X', b^{-1}D, Lb^*M)`, which is good because `b` has property (1), followed by the
bookkeeping of
`AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_etaDerivedPullbackObject_comp`: the
divisor `h'^{-1}(b^{-1}D)` *is* the divisor `(h' ∘ b)^{-1}D`, and the two routes to the
pulled-back object agree. -/
@[stacks 0F8V "the displayed identification: for `b` with the two properties of tag 0GTY for \
(X, D, M) and `c` with those properties for (Y, E, Lh^* M), the morphism `h' : Y' -> X'` over \
`h . c` satisfies `L eta_{J'} L(h . c)^* M ≅ L h'^* Q`. The sentence identifying `Y'` with the \
strict transform of `Y` with respect to `b` rests on the moreover clause of tag 0GTY --- that \
over an affine chart the restriction of `b` is the blowing up in the product of the \
determinantal ideals --- and is proved alongside that clause, as \
AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.existsUnique_iso_strictTransform in \
GoodBlowupStrictTransform.lean"]
theorem exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodBlowup
    (S : ComplexAndDivisorSituation.{u, d}) {X' Y Y' : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : S.IsGoodBlowup b) (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) (c : Y' ⟶ Y)
    (hc : (S.pullback h hD).IsGoodBlowup c) :
    ∃ h' : Y' ⟶ X', h' ≫ b = c ≫ h ∧
      Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          h'.toLRSHom.toShHom).obj
            (S.etaDerivedPullbackObject b hb.isGoodOver.pullbackDefined) ≅
        S.etaDerivedPullbackObject (c ≫ h)
          ((S.isGoodOver_comp h hD c hc.isGoodOver.pullbackDefined).mpr
            hc.isGoodOver.isGoodTriple).pullbackDefined) := by
  have hgoodOver := (S.isGoodOver_comp h hD c hc.isGoodOver.pullbackDefined).mpr
    hc.isGoodOver.isGoodTriple
  obtain ⟨h', hh', -⟩ := hb.existsUnique_lift (c ≫ h) hgoodOver
  refine ⟨h', hh', ?_⟩
  have hbd := hb.isGoodOver.pullbackDefined
  have hhb : Stacks.Divisors.IsPullbackDefined (h' ≫ b) S.D := hh' ▸ hgoodOver.pullbackDefined
  have hk' : Stacks.Divisors.IsPullbackDefined h' (S.D.comap b) := by
    rw [show Stacks.Divisors.IsPullbackDefined h' (S.D.comap b) =
      Stacks.Divisors.IsEffectiveCartierDivisor ((S.D.comap b).comap h') from rfl,
      ← Scheme.IdealSheafData.comap_comp]
    exact hhb
  have hE : (𝟭 (DerivedCategory (OXMod.{u, u} X'.toRingedSpace))) ≅
      (Localization.uniq (DerivedCategory.Q (C := OXMod.{u, u} X'.toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} X'.toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} X'.toRingedSpace)
          (ComplexShape.up ℤ))).functor :=
    Localization.isoUniqFunctor _ _ _ (𝟭 _) (Functor.rightUnitor _)
  obtain ⟨e₁⟩ := (S.pullback b hbd).nonempty_derivedPullback_derivedEta_iso
    hb.isGoodOver.isGoodTriple h' hk'
  obtain ⟨e₂⟩ := S.nonempty_etaDerivedPullbackObject_comp b hbd h' hk' hhb
  exact ⟨(Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      h'.toLRSHom.toShHom).mapIso
        ((Stacks.Divisors.Eta.derivedEtaData (S.D.comap b)).functor.mapIso
          (hE.app (S.derivedPullbackObject b))) ≪≫ e₁ ≪≫ e₂ ≪≫
    eqToIso (S.etaDerivedPullbackObject_congr hh' hhb hgoodOver.pullbackDefined)⟩

/-- Let `b : X' ⟶ X` satisfy `IsGoodBlowup`. If moreover `(Y, E, Lh^*M)` is a good triple, then
the unique `k : Y ⟶ X'` with `h = b ∘ k` satisfies

`Lη_𝒥 Lh^*M ≅ Lk^* Q`.

This is `exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodBlowup` at `c = 𝟙_Y`,
which satisfies `IsGoodBlowup` for an already good triple by `isGoodBlowup_id`. -/
@[stacks 0F8V "the final assertion: for `b` with the two properties of tag 0GTY and `h` good \
for the triple, the unique `k` with `h = b . k` satisfies `L eta_J Lh^* M ≅ Lk^* Q`. It is the \
displayed identification at c = 1_Y; the displayed identification itself, for a general `c`, is \
exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodBlowup"]
theorem exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver
    (S : ComplexAndDivisorSituation.{u, d}) {X' Y : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : S.IsGoodBlowup b) (h : Y ⟶ S.X) (hh : S.IsGoodOver h) :
    ∃ k : Y ⟶ X', k ≫ b = h ∧
      Nonempty ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          k.toLRSHom.toShHom).obj
            (S.etaDerivedPullbackObject b hb.isGoodOver.pullbackDefined) ≅
        S.etaDerivedPullbackObject h hh.pullbackDefined) := by
  obtain ⟨k, hk, ⟨e⟩⟩ :=
    S.exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodBlowup b hb h
      hh.pullbackDefined (𝟙 Y) (isGoodBlowup_id
        ((S.pullback h hh.pullbackDefined).isGoodOver_of_flat (𝟙 _) hh.isGoodTriple))
  exact ⟨k, hk.trans (Category.id_comp h),
    ⟨e ≪≫ eqToIso (S.etaDerivedPullbackObject_congr (Category.id_comp h) _ hh.pullbackDefined)⟩⟩

end AlgebraicGeometry.ComplexAndDivisorSituation

end
