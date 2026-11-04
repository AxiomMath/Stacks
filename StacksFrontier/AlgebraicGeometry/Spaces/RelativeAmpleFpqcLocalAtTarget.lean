module

public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleBaseChangeCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleFpqcRepresentable
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleTestSchemeDescent
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedFpqcLocalAtTarget

/-!
# Relative ampleness is fpqc local on the base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let `L`
be an invertible `𝒪_X`-module, let `{gᵢ : Yᵢ ⟶ Y}` be an fpqc covering, let `fᵢ : Xᵢ ⟶ Yᵢ` be
the base change of `f` and `Lᵢ` the pullback of `L`. Stacks 0D3C says that `L` is ample on `X/Y`
if and only if `Lᵢ` is ample on `Xᵢ/Yᵢ` for every `i`.

## Main results

* `AlgebraicGeometry.Space.isAmpleOnBaseChange_of_isPullback`: the base-change clause of
  Stacks 0D36 descends a cartesian square — a test scheme of `Y'` is a test scheme of `Y`.
* `AlgebraicGeometry.Space.forall_isRelativelyAmple_baseChange_of_isRelativelyAmple`:
  **Stacks 0D3C, (1) implies (2)**, which is base change and uses nothing about the family.
* `AlgebraicGeometry.Space.exists_affineFpqcRefinement_isAmpleOnBaseChange`: **the reduction
  of Stacks 0D3C, (2) implies (1), to the scheme level.** From relative ampleness on the members
  of the covering, every affine scheme over `Y` carries a finite affine fpqc covering on each of
  whose members the base-change clause of Stacks 0D36 holds.
* `AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_isRelativelyAmple_baseChange`:
  **Stacks 0D3C**.

## Implementation notes

**Base changes are quantified as cartesian squares,** as in
`AlgebraicGeometry.Space.IsRelativelyAmple` and in
`AlgebraicGeometry.Space.IsAmpleOnBaseChange`: the family `fᵢ` is given together with
`pᵢ : Xᵢ ⟶ X` and the hypothesis that `(pᵢ, fᵢ, f, gᵢ)` is cartesian, and `Lᵢ` is
`AlgebraicGeometry.Space.modulePullback` of `L` along `pᵢ`.

**The route of (2) implies (1).** Relative ampleness is the base-change clause of Stacks 0D36 at
every scheme over `Y`, so it is enough to produce that clause at every affine scheme over `Y`
and then to spread it. The fpqc condition of Stacks 03MQ hands, over an affine `T ⟶ Y`, a finite
family of affine schemes `Vⱼ ⟶ T` covering `T` in the fpqc topology of schemes and each
factoring through some member `Yᵢ` of the covering. Over such a `Vⱼ` a cartesian square for `f`
is a cartesian square for `fᵢ` pasted with the one defining `fᵢ`, and the pullback of `L` to its
upper-left corner is the pullback of `Lᵢ`, so the clause at `Vⱼ` is the clause for `(fᵢ, Lᵢ)` at
the lift of `Vⱼ`. That is
`AlgebraicGeometry.Space.exists_affineFpqcRefinement_isAmpleOnBaseChange`, and it is proved
unconditionally.

**Finishing the descent.** For an invertible `L` the clause at every affine scheme over `Y` is
enough (Stacks 0D36,
`AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_affine_isAmpleOnBaseChange`, whose
spreading step is Stacks 01VJ). Over an affine `T ⟶ Y` with the finite affine fpqc
covering above, `f` is quasi-compact and separated because each `fᵢ` is (Stacks 0D34) and both
properties are fpqc local on the base (Stacks 041L, 0421); so the base change of `f` to `T` is a
scheme (`AlgebraicGeometry.Space.exists_isPullback_of_affineFpqcFamily`) and the pullback of `L`
to it is ample over `T` by the scheme case, Stacks 0D2P
(`AlgebraicGeometry.Space.exists_isRelativelyAmple_of_fpqcFamily`).

## References

* [Stacks Project, Tag 0D3C](https://stacks.math.columbia.edu/tag/0D3C)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
* [Stacks Project, Tag 0D36](https://stacks.math.columbia.edu/tag/0D36)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Transferring the base-change clause down a cartesian square -/

/-- Let `f' : X' ⟶ Y'` be a base change of `f : X ⟶ Y` along `g : Y' ⟶ Y` and let `L'` be the
pullback of an `𝒪_X`-module `L` to `X'`. A scheme `V` over `Y'` is a scheme over `Y`, and the
base-change clause of Stacks 0D36 for `(f', L')` at `V` is that clause for `(f, L)` at `V`.

A cartesian square for `f` over `V` factors uniquely through the square defining `f'`, which
makes it a cartesian square for `f'` over `V`, and the pullback of `L` to its upper-left corner
is the pullback of `L'` by `AlgebraicGeometry.Space.baseChangeModuleCompIso`. -/
theorem isAmpleOnBaseChange_of_isPullback {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {p : X' ⟶ X} {f' : X' ⟶ Y'} (hsq : IsPullback p f' f g)
    (L : Modules.{u, u} B S hS X.1 X.2) (V : BigFppfOver B S hS) (t : yoneda.obj V ⟶ Y'.1)
    (h : IsAmpleOnBaseChange B S hS f' ((modulePullback B S hS p).obj L) V t) :
    IsAmpleOnBaseChange B S hS f L V (t ≫ g.hom) := by
  have hsq' : IsPullback p.hom f'.hom f.hom g.hom := AlgebraicSpaces.isPullback_hom B S hS hsq
  obtain ⟨⟨U₀, q₀, p₀, hsq₀⟩, hamp⟩ := h
  refine ⟨⟨U₀, q₀, p₀ ≫ p.hom, hsq₀.paste_horiz hsq'⟩, fun U pU q htest => ?_⟩
  obtain ⟨pU', hsq₂, hpU⟩ :
      ∃ pU' : yoneda.obj U ⟶ X'.1, IsPullback pU' (yoneda.map q) f'.hom t ∧ pU' ≫ p.hom = pU :=
    ⟨_, htest.of_right' hsq', hsq'.lift_fst _ _ _⟩
  obtain ⟨hInv, hAmp⟩ := hamp U pU' q hsq₂
  have := hInv
  have e : baseChangeModule B S hS ((modulePullback B S hS p).obj L) U pU' ≅
      baseChangeModule B S hS L U pU :=
    (baseChangeModuleCompIso B S hS p L U pU').symm ≪≫
      eqToIso (congrArg (baseChangeModule B S hS L U) hpU)
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U pU) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
  exact ⟨inferInstance, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp hAmp⟩

/-! ### Stacks 0D3C -/

/-- A morphism property that is fpqc local on the target holds for `f` as soon as it holds for
the base changes `fᵢ` along the members of an fpqc covering of the target. -/
private theorem of_forall_isoPullback_fpqc {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {I : Type v} {Yᵢ Xᵢ : I → AlgebraicSpaces B S hS} {gᵢ : ∀ i, Yᵢ i ⟶ Y}
    {fᵢ : ∀ i, Xᵢ i ⟶ Yᵢ i} {pᵢ : ∀ i, Xᵢ i ⟶ X}
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.precoverage.{u, v} .fpqc B S hS)]
    (hsq : ∀ i, IsPullback (pᵢ i) (fᵢ i) f (gᵢ i))
    (hR : Presieve.ofArrows Yᵢ gᵢ ∈ Topology.precoverage.{u, v} .fpqc B S hS Y)
    (h : ∀ i, P (fᵢ i)) : P f := by
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (K := Topology.precoverage.{u, v} .fpqc B S hS) hR fun {U g} _ hg => ?_
  obtain ⟨i⟩ := hg
  refine (MorphismProperty.cancel_left_of_respectsIso P (hsq i).isoPullback.hom _).mp ?_
  rw [(hsq i).isoPullback_hom_snd]
  exact h i

section Fpqc

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {I : Type v}
  {Yᵢ Xᵢ : I → AlgebraicSpaces B S hS} {gᵢ : ∀ i, Yᵢ i ⟶ Y} {fᵢ : ∀ i, Xᵢ i ⟶ Yᵢ i}
  {pᵢ : ∀ i, Xᵢ i ⟶ X} (hsq : ∀ i, IsPullback (pᵢ i) (fᵢ i) f (gᵢ i))
  (L : Modules.{u, u} B S hS X.1 X.2)

include hsq

/-- **Stacks 0D3C, (1) implies (2).** If `L` is ample on `X/Y` then the pullback of `L` to the
base change of `f` along any member of the family is ample on that base change: this is the
base-change stability of Stacks 0D33, and nothing is asked of the family. -/
@[stacks 0D3C "(1) implies (2), unconditionally; the fpqc hypothesis on the family is not
needed for this direction"]
theorem forall_isRelativelyAmple_baseChange_of_isRelativelyAmple
    (hL : IsRelativelyAmple B S hS f L) (i : I) :
    IsRelativelyAmple B S hS (fᵢ i) ((modulePullback B S hS (pᵢ i)).obj L) :=
  isRelativelyAmple_baseChange (hsq i) L hL

/-- **The reduction of Stacks 0D3C, (2) implies (1), to the scheme level.** Assume the pullback
of `L` to each base change `Xᵢ` is ample on `Xᵢ/Yᵢ`. Then every affine scheme `T` over `Y`
admits a finite family of affine schemes over `T` which covers `T` in the fpqc topology of
schemes and on each of whose members the base-change clause of Stacks 0D36 for `(f, L)` holds.

The fpqc condition of Stacks 03MQ supplies the family together with a factorisation of each
member through some `Yᵢ`, and
`AlgebraicGeometry.Space.isAmpleOnBaseChange_of_isPullback` turns the clause for `(fᵢ, Lᵢ)` at
that factorisation into the clause for `(f, L)`. -/
@[stacks 0D3C "the unconditional half of (2) implies (1): the clause of Tag 0D36 on a finite
affine fpqc covering of each affine scheme over Y. Descending it to the scheme itself is
carried by `isRelativelyAmple_iff_forall_isRelativelyAmple_baseChange`"]
theorem exists_affineFpqcRefinement_isAmpleOnBaseChange
    (hfpqc : IsFpqcCovering B S hS fun i => (gᵢ i).hom)
    (h : ∀ i, IsRelativelyAmple B S hS (fᵢ i) ((modulePullback B S hS (pᵢ i)).obj L))
    (T : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y.1) :
    ∃ U : PreZeroHypercover.{u + 1} T, Finite U.I₀ ∧
      Presieve.map (BigAffineFppf.toScheme B S hS) U.presieve₀ ∈
        Scheme.fpqcPrecoverage ((BigAffineFppf.toScheme B S hS).obj T) ∧
      ∀ j : U.I₀, IsAmpleOnBaseChange B S hS f L
        ((BigAffineFppf.inclusion B S hS).obj (U.X j))
        (yoneda.map ((BigAffineFppf.inclusion B S hS).map (U.f j)) ≫ g) := by
  obtain ⟨U, hfin, hmem, hrefine⟩ := hfpqc.2 T g
  refine ⟨U, hfin, hmem, fun j => ?_⟩
  obtain ⟨i, a, ha⟩ := hrefine j
  have key := isAmpleOnBaseChange_of_isPullback (hsq i) L _ a
    (isAmpleOnBaseChange_of_isRelativelyAmple (h i) _ a)
  rwa [ha] at key

/-- **Stacks 0D3C.** Let `L` be an invertible `𝒪_X`-module, let `{gᵢ : Yᵢ ⟶ Y}` be an fpqc
covering, let `fᵢ : Xᵢ ⟶ Yᵢ` be the base change of `f : X ⟶ Y` and `Lᵢ` the pullback of `L`.
Then `L` is ample on `X/Y` if and only if `Lᵢ` is ample on `Xᵢ/Yᵢ` for every `i`.

The forward direction is base change. For the converse, `f` is quasi-compact and separated
(Stacks 0D34, 041L, 0421), the clause of Stacks 0D36 may be tested at the affine schemes over `Y`,
and at such a scheme it is
`AlgebraicGeometry.Space.exists_affineFpqcRefinement_isAmpleOnBaseChange` followed by
`AlgebraicGeometry.Space.exists_isPullback_of_affineFpqcFamily` and
`AlgebraicGeometry.Space.exists_isRelativelyAmple_of_fpqcFamily`. -/
@[stacks 0D3C "full equivalence, with the hypotheses of the source: L invertible and the
family an fpqc covering"]
theorem isRelativelyAmple_iff_forall_isRelativelyAmple_baseChange
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (hfpqc : IsFpqcCovering B S hS fun i => (gᵢ i).hom) :
    IsRelativelyAmple B S hS f L ↔
      ∀ i, IsRelativelyAmple B S hS (fᵢ i) ((modulePullback B S hS (pᵢ i)).obj L) := by
  refine ⟨fun hamp i => forall_isRelativelyAmple_baseChange_of_isRelativelyAmple hsq L hamp i,
    fun h => ?_⟩
  -- the covering, as a covering of the fpqc precoverage of algebraic spaces
  have hR : Presieve.ofArrows Yᵢ gᵢ ∈ Topology.precoverage.{u, v} .fpqc B S hS Y :=
    ⟨I, Yᵢ, gᵢ, rfl, Y.2, fun i => (Yᵢ i).2, hfpqc⟩
  -- `f` is quasi-compact and separated, these being fpqc local on the base (041L, 0421)
  have := quasiCompact_isLocalAtTarget_fpqc.{u, v} B S hS
  have := separated_isLocalAtTarget_fpqc.{u, v} B S hS
  have hqc : IsQuasiCompact B S hS f.hom :=
    of_forall_isoPullback_fpqc (quasiCompactProperty B S hS) hsq hR fun i => (h i).isQuasiCompact
  have hsep : IsSeparated B S hS f.hom :=
    of_forall_isoPullback_fpqc (separatedProperty B S hS) hsq hR fun i => (h i).isSeparated
  -- the clause of Stacks 0D36 at every affine scheme over `Y`
  refine (isRelativelyAmple_iff_forall_affine_isAmpleOnBaseChange f L hL).mpr
    fun T hT g => ?_
  obtain ⟨𝒰, hfin, hmem, hclause⟩ :=
    exists_affineFpqcRefinement_isAmpleOnBaseChange hsq L hfpqc h ⟨T, hT⟩ g
  have hmap : Presieve.map (BigAffineFppf.toScheme B S hS) 𝒰.presieve₀ =
      Presieve.ofArrows (fun j => (BigFppfOver.toScheme B S hS).obj
          ((BigAffineFppf.inclusion B S hS).obj (𝒰.X j)))
        (fun j => (BigFppfOver.toScheme B S hS).map
          ((BigAffineFppf.inclusion B S hS).map (𝒰.f j))) := by
    simp [PreZeroHypercover.presieve₀]
  refine ⟨exists_isPullback_of_affineFpqcFamily f L hL hqc hsep ⟨T, hT⟩ g 𝒰 hfin hmem hclause,
    fun U p q hsq' => ?_⟩
  exact exists_isRelativelyAmple_of_fpqcFamily f L hL g
    (fun j => (BigAffineFppf.inclusion B S hS).map (𝒰.f j)) (hmap ▸ hmem) hclause U p q hsq'

end Fpqc

end AlgebraicGeometry.Space

end
