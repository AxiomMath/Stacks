module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback and proper pushforward across a fibre product square

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let

      X' --g'--> X
      |          |
      f'         f
      v          v
      Y' --g-->  Y

be a fibre product diagram of schemes locally of finite type over `S`, with `f` proper and `g`
flat of relative dimension `r`. Then `f'` is proper, `g'` is flat of relative dimension `r`, and
flat pullback commutes with proper pushforward on cycles:

`g^* f_* α = f'_* (g')^* α`  in  `Z_{k+r}(Y')`.

This file reduces the cycle identity to two sheaf-level inputs, coherence of the direct images
and cohomology and base change in degree zero, which enter the statements below as explicit
parameters. Both inputs are theorems of this repository, and the complete statement of Stacks
02RG, with all three assertions and no hypothesis beyond the source's, is
`Stacks.Chow.isProper_and_relativeDimension_and_flatPullback_properPushforward` in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeGenuine`.

## Main results

* `Stacks.Chow.flatPullback_properPushforward_cycleAssociatedToCoherentSheaf` — the cycle
  identity for `α = [F]_k` the cycle of a coherent `𝒪_X`-module `F`, given that the canonical
  comparison `g^* f_* F ⟶ f'_* (g')^* F` of
  `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is an isomorphism.
* `Stacks.Chow.flatPullback_properPushforward_cycleAssociatedToClosedSubscheme` — the same
  identity for `α = [W]` the cycle of a closed subscheme `W ⊆ X`, given flat base change for
  `i_* 𝒪_W`.
* `Stacks.Chow.flatPullback_properPushforward_of_finite_support` — the identity for an arbitrary
  *finitely supported* `k`-cycle `α`, given flat base change for the structure sheaves of the
  integral closed subschemes attached to the points of its support.
* `Stacks.Chow.flatPullback_properPushforward` — the identity for an arbitrary `k`-cycle `α`,
  under no support hypothesis, given the same flat base change isomorphisms.

## Implementation notes

The chain of the source proof is: proper pushforward of the cycle of a coherent sheaf is the
cycle of its direct image (Stacks 02R6), flat pullback of the cycle of a coherent sheaf is the
cycle of its inverse image (Stacks 02RE), and the cycle of a closed subscheme is the cycle of
the direct image of its structure sheaf (Stacks 02QY). Applying these four times reduces the
cycle identity to the equality of the cycles of `g^* f_* F` and of `f'_* (g')^* F`, hence to
those two sheaves being isomorphic.

That isomorphism is cohomology and base change in degree zero, Stacks 02KH, which is
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`. Coherence of
a direct image along a proper morphism is the proper mapping theorem, Stacks 02O5, which is
`AlgebraicGeometry.ProperCoherenceWitness.isCoherent_pushforward`. Both live in modules this file
does not import, so here they enter as parameters, and they are supplied in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeGenuine`.

The passage from a single closed subscheme to a general cycle uses the presentation of a finitely
supported cycle as a finite sum of fundamental cycles,
`Stacks.Chow.eq_finsetSum_cycleAssociatedToIntegralComponentAt`, together with additivity of the
two operations. A cycle group of chapter 42 is a group of *locally* finitely supported functions,
so that presentation covers the finitely supported cycles only. Lifting the identity to a general
cycle is a local statement at one point `y` of `Y'`: both sides have coefficient at `y` depending
on the cycle only through its restriction to the fibre of `f` over `g(y)`, and properness of `f`
makes the intersection of that fibre with the support finite. That lifting is carried out in
`Stacks.Chow.flatPullback_properPushforward`, by comparing the two coefficient formulas
`Stacks.Chow.properPushforward_apply` and `Stacks.Chow.flatPullback_apply` term by term against
`Stacks.Chow.cycleRestrict` of the cycle to that finite intersection.

## References

* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 02R6](https://stacks.math.columbia.edu/tag/02R6)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02NK](https://stacks.math.columbia.edu/tag/02NK)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

add_to_sga "1 IX 2.4" "partial" AlgebraicGeometry.IsProper.isStableUnderBaseChange
add_to_sga "1 VIII 4.8" "partial" AlgebraicGeometry.IsProper.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.IsProper.isStableUnderBaseChange
add_to_sga "6 X 7.5" "partial" AlgebraicGeometry.IsProper.isStableUnderBaseChange
add_to_ega "II 5.4.2" "more general" AlgebraicGeometry.IsProper.isStableUnderBaseChange
add_to_ega "III 4.3.4" "more general" AlgebraicGeometry.IsProper.isStableUnderBaseChange
add_to_ega "IV 2.7.1" "implication" AlgebraicGeometry.IsProper.isStableUnderBaseChange
add_to_sga "3 III 0.13" "partial" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "3 VIB 11.1" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "3 VIB 2.1.2" "partial" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "3 VIB 3.11" "fiber-flatness" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "3 VIIB 1.3.3" "(iii), special case" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "3 XIX 2.1" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "4 Vbis 3.3" "special case" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "6 0 2.9" "special case" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "6 XII 2.3" "(a)" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "6 XII 4.1" "(1)" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "7 VII 1.3.8" "partial" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "III 7.7.2" "special case" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "III 7.9.7" "special case" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "IV 11.5.4" "necessity" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "IV 2.1.4" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "IV 2.2.13" "(i)" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "IV 2.5.1" "special case" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "IV 20.6.9" "flatness of X' over S'" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "IV 21.15.9" "partial" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_ega "IV 7.3.5" "partial" AlgebraicGeometry.Flat.isStableUnderBaseChange
add_to_sga "3 VIB 2.1.2" "partial" AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange
add_to_ega "I 10.13.5" "(ii)" AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange
add_to_ega "I 6.3.4" "clause (iv)" AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange
add_to_ega "I 6.6.6" AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange
add_to_ega "II 3.5.5" "partial" AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange
add_to_ega "IV 1.3.4" AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange
add_to_ega "IV 2.7.1" "(iii)" AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange

/-! ### The cycle of a coherent sheaf -/

/-- The structure morphisms are compatible with `f'` when `f`, `g`, `g'` are, by commutativity of
the square. -/
private theorem comp_eq_of_isPullback {C : ChowSituation.{u}} {X Y X' Y' : Scheme.{u}}
    {sX : X ⟶ C.S} {sY : Y ⟶ C.S} {sX' : X' ⟶ C.S} {sY' : Y' ⟶ C.S}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX') : f' ≫ sY' = sX' := by
  rw [← hg, ← Category.assoc, ← hsq.w, Category.assoc, hf, hg']

/-- **The cycle identity of Stacks 02RG for the cycle of a coherent sheaf, given flat base change
for that sheaf.**
In a fibre product diagram

      X' --g'--> X
      |          |
      f'         f
      v          v
      Y' --g-->  Y

of schemes locally of finite type over the base of chapter 42, with `f` proper and `g` flat of
relative dimension `r`, let `F` be a coherent `𝒪_X`-module whose support has delta-dimension at
most `k`. If the canonical comparison morphism `g^* f_* F ⟶ f'_* (g')^* F` is an isomorphism —
flat base change in degree zero, Stacks 02KH, a parameter here — then

`g^* f_* [F]_k = f'_* (g')^* [F]_k`.

Indeed `f_* [F]_k = [f_* F]_k` and `f'_* [(g')^* F]_{k+r} = [f'_* (g')^* F]_{k+r}` by Stacks
02R6, while `g^* [f_* F]_k = [g^* f_* F]_{k+r}` and `(g')^* [F]_k = [(g')^* F]_{k+r}` by Stacks
02RE; the two resulting cycles are the cycles of isomorphic sheaves. -/
theorem flatPullback_properPushforward_cycleAssociatedToCoherentSheaf
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (F : X.Modules) [F.IsCoherent]
    [((Scheme.Modules.pushforward f).obj F).IsCoherent]
    [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F)).IsCoherent]
    (k : ℤ) (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ sX) ≤ (k : EInt))
    (hbc : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      hsq.w).app F)) :
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    flatPullback C sY' sY g hg r hgr k
        (properPushforward C sX sY f hf k (cycleAssociatedToCoherentSheaf C sX F k hFk)) =
      properPushforward C sX' sY' f'
        (by rw [← hg, ← Category.assoc, ← hsq.w, Category.assoc, hf, hg']) (k + (r : ℤ))
        (flatPullback C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k
          (cycleAssociatedToCoherentSheaf C sX F k hFk)) := by
  let : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian sX'
  let : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian sY'
  let : ((Scheme.Modules.pullback g').obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback g' F
  let : ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F)).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback g ((Scheme.Modules.pushforward f).obj F)
  rw [properPushforward_cycleAssociatedToCoherentSheaf C sX sY f hf F k hFk,
    flatPullback_cycleAssociatedToCoherentSheaf C sY' sY g hg r hgr
      ((Scheme.Modules.pushforward f).obj F) k
      (schemeDeltaDimension_reducedSupport_pushforward_le C sX sY f hf F hFk),
    flatPullback_cycleAssociatedToCoherentSheaf C sX' sX g' hg' r
      (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) F k hFk,
    properPushforward_cycleAssociatedToCoherentSheaf C sX' sY' f'
      (comp_eq_of_isPullback hsq hf hg hg') ((Scheme.Modules.pullback g').obj F) (k + (r : ℤ))
      (schemeDeltaDimension_support_pullback_le C sX' sX g' hg' r
        (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) F k hFk)]
  let := hbc
  let e : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj F) ≅
      (Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj F) :=
    asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app F)
  exact cycleAssociatedToCoherentSheaf_eq_of_iso C sY' e (k + (r : ℤ)) _ _

/-! ### The cycle of a closed subscheme -/

/-- **The cycle identity of Stacks 02RG for the cycle of a closed subscheme, given flat base
change for its structure sheaf.** In the fibre product diagram of
`Stacks.Chow.flatPullback_properPushforward_cycleAssociatedToCoherentSheaf`, let `i : W ⟶ X` be
a closed subscheme with `dim_δ(W) ≤ k`. If the canonical comparison morphism
`g^* f_* (i_* 𝒪_W) ⟶ f'_* (g')^* (i_* 𝒪_W)` is an isomorphism — Stacks 02KH, a parameter
here — then

`g^* f_* [W] = f'_* (g')^* [W]`  in  `Z_{k+r}(Y')`.

This is step (4) of the source proof: `[W] = [𝒪_W]_k` by Stacks 02QY, so the identity is the one
for the cycle of the coherent sheaf `i_* 𝒪_W`. -/
theorem flatPullback_properPushforward_cycleAssociatedToClosedSubscheme
    (C : ChowSituation.{u}) {X Y X' Y' W : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (i : W ⟶ X) [IsClosedImmersion i] (k : ℤ)
    (hW : schemeDeltaDimension C (i ≫ sX) ≤ (k : EInt))
    (hbc : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule W)))) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    ∀ [((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward i).obj (Ample.unitModule W))).IsCoherent]
      [((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pushforward i).obj (Ample.unitModule W)))).IsCoherent],
    flatPullback C sY' sY g hg r hgr k
        (properPushforward C sX sY f hf k (cycleAssociatedToClosedSubscheme C sX i k)) =
      properPushforward C sX' sY' f'
        (by rw [← hg, ← Category.assoc, ← hsq.w, Category.assoc, hf, hg']) (k + (r : ℤ))
        (flatPullback C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k
          (cycleAssociatedToClosedSubscheme C sX i k)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  intro _ _
  rw [cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf C sX i k hW]
  exact flatPullback_properPushforward_cycleAssociatedToCoherentSheaf C sX sY sX' sY' f g g' f'
    hsq hf hg hg' r hgr ((Scheme.Modules.pushforward i).obj (Ample.unitModule W)) k
    (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le C sX i hW) hbc

/-! ### A finitely supported cycle -/

/-- **The cycle identity of Stacks 02RG for a finitely supported cycle, given flat base
change.** In the fibre product diagram of
`Stacks.Chow.flatPullback_properPushforward_cycleAssociatedToCoherentSheaf`, let `α` be a
`k`-cycle on `X` whose support is finite. Granted, for the structure sheaf of each integral
closed subscheme `W_x ⊆ X` with generic point `x`, coherence of the two direct images
(Stacks 02O5) and the flat base change isomorphism (Stacks 02KH), one has

`g^* f_* α = f'_* (g')^* α`  in  `Z_{k+r}(Y')`.

This is steps (3) to (5) of the source proof, carried out by linearity: a finitely supported
cycle is the finite sum `∑ n_x [W_x]` of
`Stacks.Chow.eq_finsetSum_cycleAssociatedToIntegralComponentAt`, both sides of the identity are
homomorphisms of abelian groups, and on each summand the identity is
`Stacks.Chow.flatPullback_properPushforward_cycleAssociatedToClosedSubscheme`. -/
theorem flatPullback_properPushforward_of_finite_support
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (k : ℤ) (α : CycleGroup C sX k)
    (hfin : (Function.support (α.1 : X → ℤ)).Finite) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    (∀ x : X, ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme))).IsCoherent) →
    (∀ x : X, ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))).IsCoherent) →
    (∀ x : X, IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))) →
    flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k α) =
      properPushforward C sX' sY' f'
        (by rw [← hg, ← Category.assoc, ← hsq.w, Category.assoc, hf, hg']) (k + (r : ℤ))
        (flatPullback C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k α) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  intro hcoh hcoh' hbc
  have hgr' : AlgebraicGeometry.RelativeDimension g' r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr
  have hf' := comp_eq_of_isPullback hsq hf hg hg'
  have hdim : ∀ x ∈ hfin.toFinset, relativeDimension C.dimensionFunction sX x = k := fun x hx ↦
    (mem_cyclesOfDimension_iff_forall_point C sX k α.1).mp α.2 x (hfin.mem_toFinset.mp hx)
  let L : CycleGroup C sX k →+ CycleGroup C sY' (k + (r : ℤ)) :=
    (flatPullback C sY' sY g hg r hgr k).comp (properPushforwardHom C sX sY f hf k)
  let R : CycleGroup C sX k →+ CycleGroup C sY' (k + (r : ℤ)) :=
    (properPushforwardHom C sX' sY' f' hf' (k + (r : ℤ))).comp
      (flatPullback C sX' sX g' hg' r hgr' k)
  change L α = R α
  rw [eq_finsetSum_cycleAssociatedToIntegralComponentAt C sX k α hfin, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [map_zsmul, map_zsmul]
  refine congrArg (fun z ↦ α.1 x • z) ?_
  let : ((Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
        (Ample.unitModule (integralComponentAt x).subscheme))).IsCoherent := hcoh x
  let : ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
      ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
        (Ample.unitModule (integralComponentAt x).subscheme)))).IsCoherent := hcoh' x
  exact flatPullback_properPushforward_cycleAssociatedToClosedSubscheme C sX sY sX' sY' f g g' f'
    hsq hf hg hg' r hgr (integralComponentAt x).subschemeι k
    (le_of_eq (by rw [schemeDeltaDimension_integralComponentAt C sX x, hdim x hx])) (hbc x)

/-! ### An arbitrary cycle -/

/-- **The cycle identity of Stacks 02RG for an arbitrary cycle, given flat base change.** In the
fibre product diagram of
`Stacks.Chow.flatPullback_properPushforward_cycleAssociatedToCoherentSheaf`, let `α` be any
`k`-cycle on `X`. Granted, for the structure sheaf of each integral closed subscheme
`W_x ⊆ X` with generic point `x`, coherence of the two direct images (Stacks 02O5) and the flat
base change isomorphism (Stacks 02KH), one has

`g^* f_* α = f'_* (g')^* α`  in  `Z_{k+r}(Y')`.

Both sides are compared coefficient by coefficient. At a point `y` of `Y'` the coefficient of the
left-hand side is the coefficient of `f_* α` at `g(y)`, a locally finite sum over the fibre
`f⁻¹(g(y))`, times the flat pullback weight; the coefficient of the right-hand side is a locally
finite sum over `f'⁻¹(y)`, whose points are carried by `g'` into that same fibre because the
square commutes. So both coefficients at `y` depend on `α` only through its values on
`f⁻¹(g(y))`. Properness of `f` makes that fibre compact, hence makes its intersection with the
locally finite support of `α` finite, and `Stacks.Chow.cycleRestrict` to that intersection is a
finitely supported `k`-cycle agreeing with `α` on the fibre. The identity at `y` is therefore the
one already proved for a finitely supported cycle,
`Stacks.Chow.flatPullback_properPushforward_of_finite_support`. The sheaf-level inputs are
theorems of this repository, supplied in `Stacks.Chow.flatPullback_properPushforward_unconditional`.
-/
theorem flatPullback_properPushforward
    (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (k : ℤ) (α : CycleGroup C sX k) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    (∀ x : X, ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme))).IsCoherent) →
    (∀ x : X, ((Scheme.Modules.pushforward f').obj ((Scheme.Modules.pullback g').obj
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))).IsCoherent) →
    (∀ x : X, IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app
        ((Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
          (Ample.unitModule (integralComponentAt x).subscheme)))) →
    flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k α) =
      properPushforward C sX' sY' f'
        (by rw [← hg, ← Category.assoc, ← hsq.w, Category.assoc, hf, hg']) (k + (r : ℤ))
        (flatPullback C sX' sX g' hg' r
          (AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr) k α) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsProper f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  intro hcoh hcoh' hbc
  have hgr' : AlgebraicGeometry.RelativeDimension g' r :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr
  have hf' := comp_eq_of_isPullback hsq hf hg hg'
  -- the square commutes on points
  have hbase : ∀ x' : X', f.base (g'.base x') = g.base (f'.base x') := fun x' ↦
    congrArg (fun m : X' ⟶ Y ↦ m.base x') hsq.w
  have hmain : flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k α) =
      properPushforward C sX' sY' f' hf' (k + (r : ℤ))
        (flatPullback C sX' sX g' hg' r hgr' k α) := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro y
    -- the fibre of `f` over `g y` is compact, so it meets the support of `α` in a finite set
    obtain ⟨β, hβfin, hagree⟩ : ∃ β : CycleGroup C sX k,
        (Function.support (β.1 : X → ℤ)).Finite ∧
          ∀ x ∈ f.base ⁻¹' {g.base y}, β.1 x = α.1 x := by
      have hfibfin : (f.base ⁻¹' {g.base y} ∩ Function.support (α.1 : X → ℤ)).Finite :=
        α.1.locallyFiniteSupport.finite_inter_support_of_isCompact
          (f.isProperMap.isCompact_preimage (isCompact_singleton (x := g.base y)))
      refine ⟨cycleRestrict C sX k α
        (f.base ⁻¹' {g.base y} ∩ Function.support (α.1 : X → ℤ)), ?_, ?_⟩
      · refine hfibfin.subset fun x hx ↦ ?_
        by_contra hxs
        exact hx (cycleRestrict_apply_of_notMem C sX k α hxs)
      · intro x hx
        by_cases hxs : x ∈ f.base ⁻¹' {g.base y} ∩ Function.support (α.1 : X → ℤ)
        · exact cycleRestrict_apply_of_mem C sX k α hxs
        · rw [cycleRestrict_apply_of_notMem C sX k α hxs]
          exact (not_not.mp fun h ↦ hxs ⟨hx, Ne.symm h⟩)
    -- the left-hand coefficient at `y` sees `α` only on that fibre
    have hLHS : (flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k α)).1 y =
        (flatPullback C sY' sY g hg r hgr k (properPushforward C sX sY f hf k β)).1 y := by
      rw [flatPullback_apply, flatPullback_apply, properPushforward_apply,
        properPushforward_apply]
      refine congrArg (· * flatPullbackWeight C sY' g (k + (r : ℤ)) y) ?_
      exact finsum_mem_congr rfl fun x hx ↦ by rw [hagree x hx]
    -- so does the right-hand coefficient, because `g'` carries `f'⁻¹(y)` into that fibre
    have hRHS : (properPushforward C sX' sY' f' hf' (k + (r : ℤ))
          (flatPullback C sX' sX g' hg' r hgr' k α)).1 y =
        (properPushforward C sX' sY' f' hf' (k + (r : ℤ))
          (flatPullback C sX' sX g' hg' r hgr' k β)).1 y := by
      rw [properPushforward_apply, properPushforward_apply]
      refine finsum_mem_congr rfl fun x' hx' ↦ ?_
      have hmem : g'.base x' ∈ f.base ⁻¹' {g.base y} := by
        rw [Set.mem_preimage, Set.mem_singleton_iff, hbase x',
          Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx')]
      rw [flatPullback_apply, flatPullback_apply, hagree _ hmem]
    rw [hLHS, hRHS]
    exact congrArg (fun z : CycleGroup C sY' (k + (r : ℤ)) ↦ z.1 y)
      (flatPullback_properPushforward_of_finite_support C sX sY sX' sY' f g g' f' hsq hf hg hg'
        r hgr k β hβfin hcoh hcoh' hbc)
  exact hmain

end Stacks.Chow

end
