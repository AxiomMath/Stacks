module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstructionSubscheme
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPullbackGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroIdeal
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaBaseChangeGeneral

/-!
# The Chern classes of the graph construction of a pulled-back object

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `g : X ⟶ X'` be a
morphism of schemes locally of finite type over `S`, let `E'` be a perfect object of `D(𝒪_{X'})`
and `E ≅ Lg^*E'`, and assume the irreducible components of `X'` are quasi-compact. This is the
finiteness alternative (d) of Situation 0GUJ. The last paragraph of the proof of Stacks 0FB2
shows that the Chern classes of the object `Q` of the graph construction for `E` are then
defined. Let `b : W ⟶ 𝐏¹_X` and `b' : W' ⟶ 𝐏¹_{X'}` be the morphisms of Stacks 0GTY for the
triples `(𝐏¹_X, (𝐏¹_X)_∞, Lp^*E)` and `(𝐏¹_{X'}, (𝐏¹_{X'})_∞, Lp'^*E')`, and let
`φ : 𝐏¹_X ⟶ 𝐏¹_{X'}` be induced by `g`. Then:

* the composite `W ⟶ 𝐏¹_X ⟶ 𝐏¹_{X'}` is good for the second triple: the divisor at infinity
  of `𝐏¹_{X'}` pulls back to that of `𝐏¹_X`, and `L(φ ∘ b)^*Lp'^*E' ≅ Lb^*Lp^*E`, so the triple it
  pulls back is the triple that `b` pulls back, which is good;
* hence it factors as `b' ∘ k` for a morphism `k : W ⟶ W'` (Stacks 0GTY (2)), and
  `Q ≅ Lk^*Q'` by the last assertion of Stacks 0F8V;
* the Chern classes of `Q'` are defined because `X'` has quasi-compact irreducible components
  (alternative (b)), and so are those of its pullback `Q` (Stacks 0GUE (5)).

## Main results

* `Stacks.Chow.hasDefinedChernClasses_graphObject_of_derivedPullback_of_etaBaseChange` — the Chern
  classes of `Q` are defined under alternative (d).
* `Stacks.Chow.hasDefinedChernClasses_graphObject_of_localizedChernFiniteness`,
  `Stacks.Chow.hasDefinedChernClasses_of_localizedChernFiniteness` — the Chern classes of `Q`,
  and of `E`, are defined under condition (3) of Situation 0GUJ
  (`Stacks.Chow.LocalizedChernFiniteness`): under (a), (b), (c) by Stacks 0GUE and Stacks 0F90 (5),
  under (d) by the above.
* `Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_graphObject`,
  `Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_E` — the same in Situation 0GUJ.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodTriple_pullback_of_comap_eq`,
  `AlgebraicGeometry.ComplexAndDivisorSituation.nonempty_etaDerivedPullbackObject_iso_of_comap_eq`
  — two morphisms into the schemes of two triples that pull back the same divisor and isomorphic
  objects pull back triples that are good together and have isomorphic décalages.
* `Stacks.Chow.comap_familyBaseChange_ker_infinitySection` — the divisor at infinity of `𝐏¹_{X'}`
  pulls back to the divisor at infinity of `𝐏¹_X`.

## Implementation notes

The last assertion of Stacks 0F8V is `AlgebraicGeometry.ComplexAndDivisorSituation.`
`exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver`, proved unconditionally.

## References

* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0F8V](https://stacks.math.columbia.edu/tag/0F8V)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0GUE](https://stacks.math.columbia.edu/tag/0GUE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u d₁ d₂

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard

variable (S₁ : ComplexAndDivisorSituation.{u, d₁}) (S₂ : ComplexAndDivisorSituation.{u, d₂})
  {Y : Scheme.{u}} (h₁ : Y ⟶ S₁.X) (h₂ : Y ⟶ S₂.X)
  (hD₁ : Stacks.Divisors.IsPullbackDefined h₁ S₁.D)
  (hD₂ : Stacks.Divisors.IsPullbackDefined h₂ S₂.D)

/-- **Goodness of a pulled-back triple depends only on the divisor and the object it pulls
back.** If `h₁ : Y ⟶ X₁` and `h₂ : Y ⟶ X₂` pull the divisors of two triples back to the same
divisor of `Y`, and pull their objects back to isomorphic objects, then the triple `h₁` pulls
back is good exactly when the one `h₂` pulls back is: an affine chart of the one is an affine
chart of the other, with the same complex and the same determinantal ideals. -/
theorem isGoodTriple_pullback_of_comap_eq (hD : S₁.D.comap h₁ = S₂.D.comap h₂)
    (e : S₁.derivedPullbackObject h₁ ≅ S₂.derivedPullbackObject h₂)
    (hgood : (S₁.pullback h₁ hD₁).IsGoodTriple) : (S₂.pullback h₂ hD₂).IsGoodTriple := by
  intro y hy
  obtain ⟨C, hyC, hC⟩ := hgood y (show y ∈ (S₁.D.comap h₁).supportSet by rwa [hD])
  obtain ⟨E₀, ⟨i⟩, hE₀⟩ := C.represents
  have hdiv : (S₂.D.comap h₂).ideal C.U = Ideal.span {C.f} := hD ▸ C.divisor_ideal
  exact ⟨⟨C.U, C.f, C.regular, hdiv, C.complex, E₀, ⟨i ≪≫ e⟩, hE₀⟩, hyC, hC⟩

/-- **The décalage of a pulled-back triple depends only on the divisor and the object it pulls
back.** If `h₁ : Y ⟶ X₁` and `h₂ : Y ⟶ X₂` pull the divisors of two triples back to the same
divisor of `Y`, and pull their objects back to isomorphic objects, then the two décalages
`Lη Lh₁^*M₁` and `Lη Lh₂^*M₂` are isomorphic. -/
theorem nonempty_etaDerivedPullbackObject_iso_of_comap_eq (hD : S₁.D.comap h₁ = S₂.D.comap h₂)
    (e : S₁.derivedPullbackObject h₁ ≅ S₂.derivedPullbackObject h₂) :
    Nonempty (S₁.etaDerivedPullbackObject h₁ hD₁ ≅ S₂.etaDerivedPullbackObject h₂ hD₂) := by
  have H : ∀ (A B : Y.IdealSheafData) (_ : A = B)
      (hA : Stacks.Divisors.IsEffectiveCartierDivisor A)
      (hB : Stacks.Divisors.IsEffectiveCartierDivisor B) {K K' : DerivedCategory Y.Modules}
      (_ : K ≅ K'), Nonempty ((@Stacks.Divisors.Eta.derivedEtaData Y A hA).functor.obj K ≅
        (@Stacks.Divisors.Eta.derivedEtaData Y B hB).functor.obj K') := by
    rintro A _ rfl hA _ K K' e
    exact ⟨(@Stacks.Divisors.Eta.derivedEtaData Y A hA).functor.mapIso e⟩
  exact H _ _ hD hD₁ hD₂ e

end AlgebraicGeometry.ComplexAndDivisorSituation

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The infinity section of `𝐏¹_Y` is the base change of that of `𝐏¹_X`** along the morphism
`𝐏¹_Y ⟶ 𝐏¹_X` induced by any `i : Y ⟶ X`. -/
theorem isPullback_infinitySection_familyBaseChange {X Y S : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) :
    IsPullback (infinitySection (i ≫ f)) i (familyBaseChange f i) (infinitySection f) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (i ≫ f) (relativeProjectiveLine S ↘ S))
    (h₂₂ := pullback.fst f (relativeProjectiveLine S ↘ S)) (v₁₃ := i) ?_ ?_
    (isPullback_familyBaseChange f i)
  · simpa only [infinitySection_comp_fst] using IsPullback.id_horiz i
  · exact constantSection_comp_familyBaseChange f i integralInfinitySection

/-- **The divisor at infinity of `𝐏¹_X` pulls back to the divisor at infinity of `𝐏¹_Y`** along
the morphism `𝐏¹_Y ⟶ 𝐏¹_X` induced by any `i : Y ⟶ X`. -/
theorem comap_familyBaseChange_ker_infinitySection {X Y S : Scheme.{u}} (f : X ⟶ S)
    (i : Y ⟶ X) :
    (infinitySection f).ker.comap (familyBaseChange f i) = (infinitySection (i ≫ f)).ker :=
  (ker_eq_comap_ker_of_isPullback (isPullback_infinitySection_familyBaseChange f i)).symm

/-- **The Chern classes of the graph construction of a pulled-back object are defined.** Let
`g : X ⟶ X'` be a morphism over the base of chapter 42, with `X'` locally of finite type over it
and with quasi-compact irreducible components, let `E'` be perfect on `X'` and `E ≅ Lg^*E'`. Then
the Chern classes of the object `Q` of the graph construction for `E` are defined.

The composite `W ⟶ 𝐏¹_X ⟶ 𝐏¹_{X'}` is good for the triple of `E'`, hence factors through
`b' : W' ⟶ 𝐏¹_{X'}` by some `k` with `Q ≅ Lk^*Q'` (Stacks 0GTY, 0F8V); the Chern classes of `Q'`
are defined (Stacks 0GUE (3)), hence so are those of `Q` (Stacks 0GUE (5)). -/
theorem hasDefinedChernClasses_graphObject_of_derivedPullback_of_etaBaseChange
    (C : ChowSituation.{u}) {X X' : Scheme.{u}} (a : X ⟶ C.S) (a' : X' ⟶ C.S)
    [LocallyOfFiniteType a'] (g : X ⟶ X') (hg : g ≫ a' = a) (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (E' : DerivedCategory X'.Modules)
    (hE' : RingedSpace.IsPerfect (X := X'.toRingedSpace) E')
    (e : (derivedPullback g.toLRSHom.toShHom).obj E' ≅ E)
    (hX' : ∀ Z ∈ irreducibleComponents X', IsCompact Z) :
    HasDefinedChernClasses (graphObject a E hE) := by
  subst hg
  have hb := isGoodBlowup_graphBlowupToBase (g ≫ a') E hE
  have hb' := isGoodBlowup_graphBlowupToBase a' E' hE'
  let b := graphBlowupToBase (g ≫ a') E hE
  let φ := familyBaseChange a' g
  let p := pullback.fst (g ≫ a') (relativeProjectiveLine C.S ↘ C.S)
  let p' := pullback.fst a' (relativeProjectiveLine C.S ↘ C.S)
  -- the divisor at infinity of `𝐏¹_{X'}` pulls back along `φ ∘ b` to that of `𝐏¹_X` along `b`
  have hD : (graphTriple a' E' hE').D.comap (b ≫ φ) = (graphTriple (g ≫ a') E hE).D.comap b :=
    (Scheme.IdealSheafData.comap_comp _ b φ).trans
      (congrArg (fun J => Scheme.IdealSheafData.comap J b)
        (comap_familyBaseChange_ker_infinitySection a' g))
  have hpd : Stacks.Divisors.IsPullbackDefined (b ≫ φ) (graphTriple a' E' hE').D :=
    (congrArg Stacks.Divisors.IsEffectiveCartierDivisor hD).mpr hb.isGoodOver.pullbackDefined
  -- the objects pulled back along `φ ∘ b` and along `b` agree
  have hI : ∀ Z : Scheme.{u}, (𝟭 (DerivedCategory (OXMod.{u, u} Z.toRingedSpace))) ≅
      (Localization.uniq (DerivedCategory.Q (C := OXMod.{u, u} Z.toRingedSpace))
        (DerivedCategory.Q (C := OXMod.{u, u} Z.toRingedSpace))
        (HomologicalComplex.quasiIso (OXMod.{u, u} Z.toRingedSpace)
          (ComplexShape.up ℤ))).functor := fun Z =>
    Localization.isoUniqFunctor _ _ _ (𝟭 _) (Functor.rightUnitor _)
  have hm : (b ≫ p) ≫ g = (b ≫ φ) ≫ p' := by
    rw [Category.assoc, Category.assoc, familyBaseChange_comp_fst]
  have eM : Nonempty ((graphTriple (g ≫ a') E hE).derivedPullbackObject b ≅
      (graphTriple a' E' hE').derivedPullbackObject (b ≫ φ)) := by
    have e₁ : (graphTriple (g ≫ a') E hE).derivedPullbackObject b ≅
        (derivedPullback ((b ≫ p) ≫ g).toLRSHom.toShHom).obj E' :=
      (derivedPullback b.toLRSHom.toShHom).mapIso ((hI _).symm.app _) ≪≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
          b.toLRSHom.toShHom p.toLRSHom.toShHom).app E ≪≫
        (derivedPullback (b ≫ p).toLRSHom.toShHom).mapIso e.symm ≪≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
          (b ≫ p).toLRSHom.toShHom g.toLRSHom.toShHom).app E'
    rw [hm] at e₁
    exact ⟨e₁ ≪≫ ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (b ≫ φ).toLRSHom.toShHom p'.toLRSHom.toShHom).app E').symm ≪≫
      (derivedPullback (b ≫ φ).toLRSHom.toShHom).mapIso ((hI _).app _)⟩
  obtain ⟨eM⟩ := eM
  -- hence `φ ∘ b` is good for the triple of `E'`, and Stacks 0F8V applies
  have hgood : (graphTriple a' E' hE').IsGoodOver (b ≫ φ) :=
    { pullbackDefined := hpd
      isGoodTriple := ComplexAndDivisorSituation.isGoodTriple_pullback_of_comap_eq
        (graphTriple (g ≫ a') E hE) (graphTriple a' E' hE') b (b ≫ φ)
        hb.isGoodOver.pullbackDefined hpd hD.symm eM hb.isGoodOver.isGoodTriple }
  obtain ⟨k, -, ⟨e₂⟩⟩ :=
    ComplexAndDivisorSituation.exists_lift_and_nonempty_etaDerivedPullbackObject_iso_of_isGoodOver
      (graphTriple a' E' hE') (graphBlowupToBase a' E' hE') hb' (b ≫ φ) hgood
  obtain ⟨e₃⟩ := ComplexAndDivisorSituation.nonempty_etaDerivedPullbackObject_iso_of_comap_eq
    (graphTriple a' E' hE') (graphTriple (g ≫ a') E hE) (b ≫ φ) b hpd
    hb.isGoodOver.pullbackDefined hD eM.symm
  exact hasDefinedChernClasses_of_derivedPullback k _ _
    (hasDefinedChernClasses_graphObject_of_isCompact_irreducibleComponents C a' E' hE' hX')
    (e₃.symm ≪≫ e₂.symm)

/-- **Condition (3) of Situation 0GUJ** for an object `E` on a scheme `Y` locally of finite type
over the base through `sY`: `Y` is quasi-compact, or its irreducible components are, or `E` is
represented by a locally bounded complex of finite locally free modules, or `E` is the pullback of
a perfect object on a scheme over the base with quasi-compact irreducible components. -/
abbrev LocalizedChernFiniteness (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    (E : DerivedCategory (OXMod.{u, u, u} Y.toRingedSpace)) : Prop :=
  CompactSpace Y ∨ (∀ c ∈ irreducibleComponents Y, IsCompact c) ∨
    (∃ P : CochainComplex (OXMod.{u, u, u} Y.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E)) ∨
    (∃ (Y' : Scheme.{u}) (a' : Y' ⟶ C.S) (g : Y ⟶ Y')
        (E' : DerivedCategory (OXMod.{u, u, u} Y'.toRingedSpace)),
      LocallyOfFiniteType a' ∧ g ≫ a' = sY ∧
        Cohomology.PerfectComplexes.IsPerfect (X := Y'.toRingedSpace) E' ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          g.toLRSHom.toShHom).obj E' ≅ E) ∧
        ∀ c ∈ irreducibleComponents Y', IsCompact c)

/-- **The Chern classes of the object `Q` of the graph construction are defined under condition
(3) of Situation 0GUJ** (the second paragraph of the proof of Stacks 0FB2). If `X` is
quasi-compact or has quasi-compact irreducible components, so does `W`, `W ⟶ X` being proper, and
Stacks 0GUE applies; if `E` is represented by a locally bounded complex of finite locally free
modules, so is `Q`, by Stacks 0F90 (5). Under alternative (d) the morphism `W ⟶ W'` of the last
assertion of Stacks 0F8V pulls `Q'` back to `Q`:
`Stacks.Chow.hasDefinedChernClasses_graphObject_of_derivedPullback_of_etaBaseChange` applies. -/
theorem hasDefinedChernClasses_graphObject_of_localizedChernFiniteness (C : ChowSituation.{u})
    {X : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a] (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (hfin : LocalizedChernFiniteness C a E) :
    HasDefinedChernClasses (graphObject a E hE) := by
  rcases hfin with h | h | h | ⟨X', a', g, E', ha', hg, hE', ⟨eE⟩, hX'⟩
  · exact hasDefinedChernClasses_graphObject_of_compactSpace C a E hE
  · exact hasDefinedChernClasses_graphObject_of_isCompact_irreducibleComponents C a E hE h
  · exact hasDefinedChernClasses_graphObject_of_isLocallyBoundedFiniteLocallyFree C a E hE h
  · have := ha'
    exact hasDefinedChernClasses_graphObject_of_derivedPullback_of_etaBaseChange C a a' g hg E hE
      E' hE' eE hX'

/-- **The Chern classes of `E` are defined if those of the object `Q` of its graph construction
are**: `E` is isomorphic to `Q|_{X × {0}}` (Stacks 0F90 (2)), and the Chern classes of a derived
pullback are defined (Stacks 0GUE). -/
theorem hasDefinedChernClasses_of_graphObject {X S : Scheme.{u}} (f : X ⟶ S)
    (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hQ : HasDefinedChernClasses (graphObject f E hE)) : HasDefinedChernClasses E :=
  hasDefinedChernClasses_of_iso (hQ.derivedPullback _)
    (nonempty_derivedPullback_modificationSectionAtZero_graphObject f E hE).some

/-- **The Chern classes of a perfect object satisfying condition (3) of Situation 0GUJ are
defined**: those of the object `Q` of its graph construction are
(`Stacks.Chow.hasDefinedChernClasses_graphObject_of_localizedChernFiniteness`), and `E` is
`Q|_{X × {0}}` (`Stacks.Chow.hasDefinedChernClasses_of_graphObject`). -/
theorem hasDefinedChernClasses_of_localizedChernFiniteness (C : ChowSituation.{u})
    {X : Scheme.{u}} (a : X ⟶ C.S) [LocallyOfFiniteType a] (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (hfin : LocalizedChernFiniteness C a E) :
    HasDefinedChernClasses E :=
  hasDefinedChernClasses_of_graphObject a E hE
    (hasDefinedChernClasses_graphObject_of_localizedChernFiniteness C a E hE hfin)

namespace LocalizedSituation

variable (S : LocalizedSituation.{u})

/-- **The Chern classes of the object `Q` of the graph construction for `E` are defined in
Situation 0GUJ** (the second paragraph of the proof of Stacks 0FB2): condition (3) of the
situation, `Stacks.Chow.hasDefinedChernClasses_graphObject_of_localizedChernFiniteness`. -/
theorem hasDefinedChernClasses_graphObject :
    HasDefinedChernClasses (graphObject S.a S.E S.perfect) :=
  hasDefinedChernClasses_graphObject_of_localizedChernFiniteness S.base S.a S.E S.perfect
    S.finiteness

/-- **The Chern classes of `E` are defined in Situation 0GUJ**: `E ≅ Q|_{X × {0}}`, and those of
`Q` are (`Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_graphObject`,
`Stacks.Chow.hasDefinedChernClasses_of_graphObject`). -/
alias hasDefinedChernClasses_E := Stacks.Chow.LocalizedSituation.hasDefinedChernClasses

end LocalizedSituation

end Stacks.Chow

end
