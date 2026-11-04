module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj

/-!
# The base change of the relative Proj of a Rees algebra is functorial

`Stacks.Blowup.reesSituationBaseChange g I h` is the comparison morphism
`Proj_Z(⨁ₙ Jⁿ) ⟶ Proj_X(⨁ₙ ℐⁿ)` attached to a flat morphism `g : Z ⟶ X` of schemes and a
presentation `h : ℐ𝒪_Z = J` of a sheaf of ideals on `Z` as the inverse image of one on `X`.
This file proves that it composes:

```
reesSituationBaseChange q J hK ≫ reesSituationBaseChange g I hJ
  = reesSituationBaseChange (q ≫ g) I hKK
```

The general composition law
`Stacks.RelativeProj.Situation.relativeProjBaseChange_comp` asks for the identification along the
composite to be, degreewise, the composite of the two identifications read through the canonical
comparison `q^*(g^*𝒜ₙ) ≅ (q ≫ g)^*𝒜ₙ`. For the Rees algebras that hypothesis is **proved** here,
not assumed, and the proof is short because the Rees comparison has an *ambient* description: a
section of `ℐⁿ` is a section of `𝒪` subject to a condition, two homogeneous sections agree as
soon as their ambient sections do, and on ambient sections the Rees comparison is `g^♯`. So the
degreewise equation is `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` after the two sides have
been tested on twice pulled-back sections.

## Main results

* `Stacks.Blowup.reesPieceAmbient_reesGradedPullbackHom_pullbackSection_le`: the ambient
  description of the Rees comparison at an arbitrary open of the source, rather than at the whole
  preimage.
* `Stacks.Blowup.reesPieceAmbient_reesSituationTransportedPullbackHom_pullbackSection`: the same
  for the comparison transported along a presentation of the inverse image ideal.
* `Stacks.Blowup.reesSituationBaseChange_congr`: the comparison morphism depends on the morphism
  of base schemes only, not on the flatness instance or on the presentation of the ideal.
* `Stacks.Blowup.reesSituationTransportedPullbackHom_id`: along the identity the Rees comparison
  is the canonical identification of `(𝟙 X)^*𝒜` with `𝒜`.
* `Stacks.Blowup.reesSituationBaseChange_id`: **the identity law for the comparison morphism of
  the relative Proj of a Rees algebra.**
* `Stacks.Blowup.canHom_comp_reesSituationTransportedPullbackHom`: **the degreewise composition
  hypothesis, for the Rees comparisons.**
* `Stacks.Blowup.reesSituationBaseChange_comp`: **the composition law for the comparison morphism
  of the relative Proj of a Rees algebra.**

## Implementation notes

The reason the degreewise hypothesis is reachable here and not in general is recorded in
`StacksFrontier/AlgebraicGeometry/RelativeProjSituation/BaseChangeInG.lean`: over an open of the
source a section of `q^*(g^*A)` is not a pulled-back section, so nothing can be read off the
section formula alone. What replaces the missing pseudofunctoriality is
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_doublePullbackSection` — two morphisms out of a
twice-iterated pullback agreeing on twice pulled-back sections are equal, which is the adjunction
applied twice — together with `Stacks.Blowup.reesPieceAmbient_injective`. Neither is available
for an abstract graded algebra: the first needs the morphisms to be compared to be morphisms of
sheaves of modules out of an iterated pullback, which is exactly the shape here, and the second
is special to the Rees algebra.

Both opens of the source are written as the iterated preimage `q ⁻¹ᵁ (g ⁻¹ᵁ V)`, which is
`(q ≫ g) ⁻¹ᵁ V` by `rfl`, so the two spellings never have to be bridged.

The presentations `hJ`, `hK` and `hKK` of the three inverse image ideals are kept as separate
hypotheses rather than being derived from `AlgebraicGeometry.Scheme.IdealSheafData.comap_comp`:
that is the shape in which the blowup of an algebraic space supplies them, where each is an
instance of `AlgebraicGeometry.Space.comap_idealSheafDataOfChart` for a different morphism of
étale charts, and deriving one from the others would force a transport of a graded algebra along
an equality of sheaves of ideals.

No `@[stacks]` attribute is attached: this is a functoriality statement about a construction of
this development. In particular it does **not** discharge the equivalence-relation hypothesis of
Tag 085Q, which additionally needs the reflexivity, symmetry and transitivity legs of an étale
presentation to be recognised as the morphisms this law composes along.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace Stacks.Blowup

/-! ### The ambient description of the Rees comparison at an arbitrary open -/

/-- **The ambient description of `Φ` at an arbitrary open of the source.**
`Stacks.Blowup.reesPieceAmbient_reesGradedPullbackHom_pullbackSection` describes `Φ` on a section
pulled back to the whole preimage `g⁻¹V`; restricting to a smaller open `W` turns `g.app V` into
`g.appLE V W`. -/
theorem reesPieceAmbient_reesGradedPullbackHom_pullbackSection_le {Z X : Scheme.{u}} (g : Z ⟶ X)
    (I : X.IdealSheafData) (n : ℤ) (V : X.Opens) (W : Z.Opens) (hW : W ≤ g ⁻¹ᵁ V)
    (a : (reesPiece I n).val.obj (op V)) :
    reesPieceAmbient (I.comap g) n W
        (((reesGradedPullbackHom g I).app n).val.app (op W)
          (Scheme.Modules.pullbackSection g (reesPiece I n) V W hW a))
      = (g.appLE V W hW) (reesPieceAmbient I n V a) := by
  have key : ((reesGradedPullbackHom g I).app n).val.app (op W)
        (Scheme.Modules.pullbackSection g (reesPiece I n) V W hW a)
      = (reesPiece (I.comap g) n).val.map (homOfLE hW).op
          (((reesGradedPullbackHom g I).app n).val.app (op (g ⁻¹ᵁ V))
            (Scheme.Modules.pullbackSection g (reesPiece I n) V (g ⁻¹ᵁ V) le_rfl a)) := by
    rw [← pullbackSection_shrink g (reesPiece I n) V (g ⁻¹ᵁ V) W le_rfl hW hW a]
    exact PresheafOfModules.naturality_apply ((reesGradedPullbackHom g I).app n).val
      (homOfLE hW).op _
  rw [key]
  refine (reesPieceAmbient_restrict (I.comap g) n W (g ⁻¹ᵁ V) hW _).trans ?_
  rw [reesPieceAmbient_reesGradedPullbackHom_pullbackSection g I n V a, Scheme.Hom.appLE,
    CommRingCat.comp_apply]

/-- The ambient description of the Rees comparison transported along a presentation of the
inverse image ideal. -/
theorem reesPieceAmbient_reesSituationTransportedPullbackHom_pullbackSection {Z X : Scheme.{u}}
    (g : Z ⟶ X) (I : X.IdealSheafData) {J : Z.IdealSheafData} (h : I.comap g = J) (n : ℤ)
    (V : X.Opens) (W : Z.Opens) (hW : W ≤ g ⁻¹ᵁ V) (a : (reesPiece I n).val.obj (op V)) :
    reesPieceAmbient J n W
        (((reesSituationTransportedPullbackHom g I h).app n).val.app (op W)
          (Scheme.Modules.pullbackSection g (reesPiece I n) V W hW a))
      = (g.appLE V W hW) (reesPieceAmbient I n V a) := by
  subst h
  exact reesPieceAmbient_reesGradedPullbackHom_pullbackSection_le g I n V W hW a

/-! ### Congruence in the morphism -/

/-- **The comparison morphism depends only on the morphism of base schemes.** The flatness
instance and the presentation of the inverse image ideal are propositions, so two of each give the
same morphism; this is the congruence lemma needed to rewrite the morphism inside
`Stacks.Blowup.reesSituationBaseChange`, whose remaining arguments mention it. -/
theorem reesSituationBaseChange_congr {Z X : Scheme.{u}} {g g' : Z ⟶ X}
    [AlgebraicGeometry.Flat g] [AlgebraicGeometry.Flat g'] (e : g = g') (I : X.IdealSheafData)
    {J : Z.IdealSheafData} (h : I.comap g = J) (h' : I.comap g' = J) :
    reesSituationBaseChange g I h = reesSituationBaseChange g' I h' := by
  subst e; rfl

/-! ### The identity law -/

/-- Restricting a section along the identity morphism over one open does nothing. This is
`AlgebraicGeometry.Scheme.Hom.appLE_eq_app` for `𝟙 X`, where the resulting `(𝟙 X).app U` is the
identity by definition. -/
private theorem appLE_id_apply {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U le_rfl) r = r := by
  have h : Scheme.Hom.appLE (𝟙 X) U U le_rfl = Scheme.Hom.app (𝟙 X) U :=
    Scheme.Hom.appLE_eq_app (f := (𝟙 X : X ⟶ X)) (U := U)
  rw [h]
  rfl

/-- **The Rees comparison along the identity is the canonical identification of `(𝟙 X)^*𝒜` with
`𝒜`.** In negative degrees both sides land in a zero object; in nonnegative degrees they agree on
pulled-back sections because the ambient section of either value is the ambient section of the
argument, and a homogeneous section is determined by its ambient section. -/
theorem reesSituationTransportedPullbackHom_id {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.comap (𝟙 X) = I) :
    reesSituationTransportedPullbackHom (𝟙 X) I h
      = Stacks.Conormal.gradedPullbackId (reesSituation I).algebra := by
  refine SheafOfModules.GradedAlgebra.UnitalHom.ext fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · exact (reesPiece_negative_isZero I n hn).eq_of_tgt _ _
  refine hom_ext_of_pullbackSection (𝟙 X) fun U a => ?_
  refine reesPieceAmbient_injective I n hn ((𝟙 X) ⁻¹ᵁ U) ?_
  have hL : reesPieceAmbient I n ((𝟙 X) ⁻¹ᵁ U)
        (((reesSituationTransportedPullbackHom (𝟙 X) I h).app n).val.app (op ((𝟙 X) ⁻¹ᵁ U))
          (Scheme.Modules.pullbackSection (𝟙 X) (reesPiece I n) U ((𝟙 X) ⁻¹ᵁ U) le_rfl a))
      = reesPieceAmbient I n U a :=
    (reesPieceAmbient_reesSituationTransportedPullbackHom_pullbackSection (𝟙 X) I h n U
        ((𝟙 X) ⁻¹ᵁ U) le_rfl a).trans
      (appLE_id_apply U (reesPieceAmbient I n U a))
  have hR : reesPieceAmbient I n ((𝟙 X) ⁻¹ᵁ U)
        (((Stacks.Conormal.gradedPullbackId (reesSituation I).algebra).app n).val.app
          (op ((𝟙 X) ⁻¹ᵁ U))
          (Scheme.Modules.pullbackSection (𝟙 X) (reesPiece I n) U ((𝟙 X) ⁻¹ᵁ U) le_rfl a))
      = reesPieceAmbient I n U a :=
    congrArg (reesPieceAmbient I n U)
      (pullbackIdHom_pullbackSection_self (reesPiece I n) U a)
  exact hL.trans hR.symm

/-- **The identity law for the comparison morphism of the relative Proj of a Rees algebra.**
Comparing along `𝟙 X` is the identity. -/
theorem reesSituationBaseChange_id {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.comap (𝟙 X) = I) :
    reesSituationBaseChange (𝟙 X) I h = 𝟙 (reesSituation I).relativeProj :=
  (Stacks.RelativeProj.Situation.relativeProjBaseChange_congr (s := reesSituation I)
        (s' := reesSituation I) (𝟙 X)
        (fun m => isIso_reesSituationTransportedPullbackHom_app (𝟙 X) I h m)
        (fun m => Stacks.Conormal.isIso_gradedPullbackId_app (reesSituation I).algebra (m : ℤ))
        (reesSituationTransportedPullbackHom_id I h)).trans
    (Stacks.RelativeProj.Situation.relativeProjBaseChange_id (s := reesSituation I))

/-! ### The degreewise composition hypothesis -/

/-- **The degreewise composition hypothesis, for the Rees comparisons.** The canonical comparison
`q^*(g^*(ℐⁿ)) ≅ (q ≫ g)^*(ℐⁿ)` followed by the Rees comparison along `q ≫ g` is the pullback
along `q` of the Rees comparison along `g` followed by the Rees comparison along `q`.

Both sides are morphisms out of a twice-iterated pullback, so by
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_doublePullbackSection` it is enough to test them
on a twice pulled-back section, and by `Stacks.Blowup.reesPieceAmbient_injective` it is enough to
compare the ambient sections of the results. Those are `(q ≫ g).appLE` and the composite of
`g.appLE` with `q.appLE`, which agree by
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`. -/
theorem canHom_comp_reesSituationTransportedPullbackHom {Y Z X : Scheme.{u}} (q : Y ⟶ Z)
    (g : Z ⟶ X) (I : X.IdealSheafData) {J : Z.IdealSheafData} (hJ : I.comap g = J)
    {K : Y.IdealSheafData} (hK : J.comap q = K) (hKK : I.comap (q ≫ g) = K) (n : ℕ) :
    canHom q g (q ≫ g) rfl ((reesSituation I).algebra.piece (n : ℤ)) ≫
        (reesSituationTransportedPullbackHom (q ≫ g) I hKK).app (n : ℤ) =
      (Scheme.Modules.pullback q).map
          ((reesSituationTransportedPullbackHom g I hJ).app (n : ℤ)) ≫
        (reesSituationTransportedPullbackHom q J hK).app (n : ℤ) := by
  refine hom_ext_of_doublePullbackSection q g (F := reesPiece I (n : ℤ)) fun V a => ?_
  refine reesPieceAmbient_injective K (n : ℤ) (Int.natCast_nonneg n) (q ⁻¹ᵁ (g ⁻¹ᵁ V)) ?_
  have hleft : reesPieceAmbient K (n : ℤ) (q ⁻¹ᵁ (g ⁻¹ᵁ V))
        (((reesSituationTransportedPullbackHom (q ≫ g) I hKK).app (n : ℤ)).val.app
          (op (q ⁻¹ᵁ (g ⁻¹ᵁ V)))
          ((canHom q g (q ≫ g) rfl (reesPiece I (n : ℤ))).val.app (op (q ⁻¹ᵁ (g ⁻¹ᵁ V)))
            (doublePullbackSection q g (reesPiece I (n : ℤ)) V a)))
      = ((q ≫ g).appLE V (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl) (reesPieceAmbient I (n : ℤ) V a) := by
    have hcan : (canHom q g (q ≫ g) rfl (reesPiece I (n : ℤ))).val.app
          (op (q ⁻¹ᵁ (g ⁻¹ᵁ V))) (doublePullbackSection q g (reesPiece I (n : ℤ)) V a)
        = Scheme.Modules.pullbackSection (q ≫ g) (reesPiece I (n : ℤ)) V
            (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl a :=
      canHom_val_app_pullbackSection q g (q ≫ g) rfl (reesPiece I (n : ℤ)) V (g ⁻¹ᵁ V)
        (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl le_rfl le_rfl a
    rw [hcan]
    exact reesPieceAmbient_reesSituationTransportedPullbackHom_pullbackSection (q ≫ g) I hKK
      (n : ℤ) V (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl a
  have hright : reesPieceAmbient K (n : ℤ) (q ⁻¹ᵁ (g ⁻¹ᵁ V))
        (((reesSituationTransportedPullbackHom q J hK).app (n : ℤ)).val.app
          (op (q ⁻¹ᵁ (g ⁻¹ᵁ V)))
          (((Scheme.Modules.pullback q).map
              ((reesSituationTransportedPullbackHom g I hJ).app (n : ℤ))).val.app
            (op (q ⁻¹ᵁ (g ⁻¹ᵁ V))) (doublePullbackSection q g (reesPiece I (n : ℤ)) V a)))
      = (q.appLE (g ⁻¹ᵁ V) (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl)
          ((g.appLE V (g ⁻¹ᵁ V) le_rfl) (reesPieceAmbient I (n : ℤ) V a)) := by
    have hnat : ((Scheme.Modules.pullback q).map
            ((reesSituationTransportedPullbackHom g I hJ).app (n : ℤ))).val.app
          (op (q ⁻¹ᵁ (g ⁻¹ᵁ V))) (doublePullbackSection q g (reesPiece I (n : ℤ)) V a)
        = Scheme.Modules.pullbackSection q (reesPiece J (n : ℤ)) (g ⁻¹ᵁ V)
            (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl
            (((reesSituationTransportedPullbackHom g I hJ).app (n : ℤ)).val.app (op (g ⁻¹ᵁ V))
              (Scheme.Modules.pullbackSection g (reesPiece I (n : ℤ)) V (g ⁻¹ᵁ V) le_rfl a)) :=
      Scheme.Modules.pullbackSection_naturality q
        ((reesSituationTransportedPullbackHom g I hJ).app (n : ℤ)) (g ⁻¹ᵁ V)
        (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl
        (Scheme.Modules.pullbackSection g (reesPiece I (n : ℤ)) V (g ⁻¹ᵁ V) le_rfl a)
    rw [hnat]
    refine (reesPieceAmbient_reesSituationTransportedPullbackHom_pullbackSection q J hK (n : ℤ)
        (g ⁻¹ᵁ V) (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl
        (((reesSituationTransportedPullbackHom g I hJ).app (n : ℤ)).val.app (op (g ⁻¹ᵁ V))
          (Scheme.Modules.pullbackSection g (reesPiece I (n : ℤ)) V (g ⁻¹ᵁ V) le_rfl a))).trans ?_
    exact congrArg (fun z : Γ(Z, g ⁻¹ᵁ V) => (q.appLE (g ⁻¹ᵁ V) (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl) z)
      (reesPieceAmbient_reesSituationTransportedPullbackHom_pullbackSection g I hJ (n : ℤ) V
        (g ⁻¹ᵁ V) le_rfl a)
  have hLE : (q.appLE (g ⁻¹ᵁ V) (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl)
        ((g.appLE V (g ⁻¹ᵁ V) le_rfl) (reesPieceAmbient I (n : ℤ) V a))
      = ((q ≫ g).appLE V (q ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl) (reesPieceAmbient I (n : ℤ) V a) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  exact hleft.trans (hLE.symm.trans hright.symm)

/-! ### The composition law -/

/-- **The composition law for the comparison morphism of the relative Proj of a Rees algebra.**
For flat `q : Y ⟶ Z` and `g : Z ⟶ X` and presentations of the three inverse image ideals,
comparing along `g` and then along `q` is comparing along `q ≫ g`.

This is `Stacks.RelativeProj.Situation.relativeProjBaseChange_comp` with its degreewise
hypothesis supplied by
`Stacks.Blowup.canHom_comp_reesSituationTransportedPullbackHom`. -/
theorem reesSituationBaseChange_comp {Y Z X : Scheme.{u}} (q : Y ⟶ Z) (g : Z ⟶ X)
    [AlgebraicGeometry.Flat q] [AlgebraicGeometry.Flat g] (I : X.IdealSheafData)
    {J : Z.IdealSheafData} (hJ : I.comap g = J) {K : Y.IdealSheafData} (hK : J.comap q = K)
    (hKK : I.comap (q ≫ g) = K) :
    reesSituationBaseChange q J hK ≫ reesSituationBaseChange g I hJ =
      reesSituationBaseChange (q ≫ g) I hKK :=
  Stacks.RelativeProj.Situation.relativeProjBaseChange_comp (s := reesSituation I)
    (s' := reesSituation J) (s'' := reesSituation K) g q
    (reesSituationTransportedPullbackHom g I hJ)
    (fun m => isIso_reesSituationTransportedPullbackHom_app g I hJ m)
    (reesSituationTransportedPullbackHom q J hK)
    (fun m => isIso_reesSituationTransportedPullbackHom_app q J hK m)
    (reesSituationTransportedPullbackHom (q ≫ g) I hKK)
    (fun m => isIso_reesSituationTransportedPullbackHom_app (q ≫ g) I hKK m)
    (fun n => canHom_comp_reesSituationTransportedPullbackHom q g I hJ hK hKK n)

end Stacks.Blowup

end
