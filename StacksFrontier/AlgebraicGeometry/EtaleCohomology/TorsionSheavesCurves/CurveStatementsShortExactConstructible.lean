module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# Lemma 0A5C for the bundled statements, with the constructibility side condition proved

Lemma 0A5C of the source: for a short exact sequence `0 → F₁ → F → F₂ → 0` of abelian sheaves on
the small étale site of `X`, if statements (1) -- (8) of Situation 0A52 hold for `F₁` and `F₂`,
then they hold for `F`. This file proves that subsheaves and quotient sheaves of a constructible
abelian sheaf on the small étale site of a Noetherian scheme are constructible, in the sense of
`Stacks.EtaleCohomology.IsConstructibleEtaleAbelianSheaf`, and deduces the lemma for the bundle
`Stacks.EtaleCohomology.CurveStatements` over a Noetherian scheme `X` over a field, with
coefficients in `AddCommGrpCat.{u + 1}` for `X : Scheme.{u}`.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_of_mono` and
  `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_of_epi`: Proposition 09BH (2) on
  Mathlib's small étale site, for a Noetherian scheme.
* `Stacks.EtaleCohomology.CurveStatements.of_shortExact`: Lemma 0A5C for the bundle.
* `Stacks.EtaleCohomology.CurveStatements.biprod`: closure under binary direct sums.

## References

* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

section Constructible

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) [IsNoetherian X]
  [∀ (T T' : B.Scheme) (f : T' ⟶ T),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1}
      (AlgebraicGeometry.SmallEtale.topology B T.obj T.property)
      (AlgebraicGeometry.SmallEtale.topology B T'.obj T'.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : AlgebraicGeometry.SmallEtale B T.obj T.property),
    HasWeakSheafify
      ((AlgebraicGeometry.SmallEtale.topology B T.obj T.property).over V)
      AddCommGrpCat.{u + 1}]

/-- **Proposition 09BH (2), subsheaves, on Mathlib's small étale site.** A subsheaf of a
constructible abelian sheaf on the small étale site of a Noetherian scheme is constructible. -/
theorem isConstructibleEtaleAbelianSheaf_of_mono
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (i : G ⟶ F) [Mono i]
    (hF : IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX F) :
    IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX G := by
  exact isConstructibleAbelianSheaf_of_mono B (B.obj X hX)
    (smallEtaleUnderlyingSetCommutes B (B.obj X hX))
    (representableIsConstructibleSetSheaf B (B.obj X hX))
    (hasFiniteRepresentableCover B (B.obj X hX))
    ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.map i) hF

/-- **Proposition 09BH (2), quotient sheaves, on Mathlib's small étale site.** A quotient of a
constructible abelian sheaf on the small étale site of a Noetherian scheme is constructible. -/
theorem isConstructibleEtaleAbelianSheaf_of_epi
    {F Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (p : F ⟶ Q) [Epi p]
    (hF : IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX F) :
    IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX Q := by
  exact isConstructibleAbelianSheaf_of_epi B (B.obj X hX)
    (smallEtaleUnderlyingSetCommutes B (B.obj X hX))
    (representableIsConstructibleSetSheaf B (B.obj X hX))
    (hasFiniteRepresentableCover B (B.obj X hX))
    ((SmallEtale.sheafEquiv B X hX AddCommGrpCat.{u + 1}).inverse.map p) hF

/-- The sub- and the quotient sheaf of a short exact sequence whose middle term is constructible
are constructible, on the small étale site of a Noetherian scheme. -/
@[sga "4 IX 2.6" "(i bis), special case"]
theorem isConstructibleEtaleAbelianSheaf_of_shortExact
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})} (hS : S.ShortExact)
    (h₂ : IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX S.X₂) :
    IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX S.X₁ ∧
      IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  exact ⟨isConstructibleEtaleAbelianSheaf_of_mono B hX S.f h₂,
    isConstructibleEtaleAbelianSheaf_of_epi B hX S.g h₂⟩

end Constructible

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X] {π : X ⟶ Spec (.of k)}
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}

/-- Let `0 → F₁ → F → F₂ → 0` be a short exact sequence of abelian sheaves on the small étale
site of a Noetherian scheme `X` over a field. If statements (1) -- (8) of Situation 0A52 hold for
`F₁` and `F₂`, then they hold for `F`. -/
@[stacks 0A5C "all eight statements of 0A52 at once, at the coefficients AddCommGrpCat.{u+1}"]
theorem CurveStatements.of_shortExact (hS : S.ShortExact)
    (h₁ : CurveStatements.{u, 0, w} π S.X₁) (h₃ : CurveStatements.{u, 0, w} π S.X₃) :
    CurveStatements.{u, 0, w} π S.X₂ :=
  CurveStatements.of_shortExact_of_constructible hS h₁ h₃
    (fun B hX _ _ h ↦ isConstructibleEtaleAbelianSheaf_of_shortExact B hX hS h)

/-- **The eight statements are closed under binary direct sums**: if they hold for `F` and `G`,
then they hold for `F ⊞ G`. -/
theorem CurveStatements.biprod {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : CurveStatements.{u, 0, w} π F) (hG : CurveStatements.{u, 0, w} π G) :
    CurveStatements.{u, 0, w} π (F ⊞ G) :=
  CurveStatements.of_shortExact (ShortComplex.Splitting.ofHasBinaryBiproduct F G).shortExact
    hF hG

end Stacks.EtaleCohomology

end
