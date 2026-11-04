module

public import StacksFrontier.AlgebraicGeometry.AmpleClosedImmersion.Converse
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.QuasiAffineAscent
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic

/-!
# The dévissage of the cohomological lift of Stacks Tag 09MS along a tower of thickenings

`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L` is the cohomological step of
[Stacks Project, Tag 09MS]: for every positive tensor power and every global section `t` of it on
the closed subscheme whose nonvanishing locus is affine, some positive tensor power of `L` carries
a global section `t'` with `i^{-1}(X_{t'}) = Z_t`. This file provides the *formal* half of the
source's reduction of that statement to the square-zero case — everything about the property that
is independent of the square-zero argument itself.

The content is three lemmas and one reduction.

* The property is invariant under isomorphism of the twisting module
  (`Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_congr`).
* The property **composes**: if `a : Z ⟶ W` is a thickening with the property for `b^* L` and `b`
  has the property for `L`, then `a ≫ b` has it for `L`
  (`Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_comp`).
* The property holds for an isomorphism
  (`Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_of_isIso`).
* Hence it holds for every *finite-order* thickening of a quasi-compact separated scheme as
  soon as it holds for every *first-order* thickening of one
  (`Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_of_isFirstOrderThickening`),
  the filtration being the tower of `Stacks.Thickenings.PowerFiltration`, each of whose steps is
  first order; and therefore for every thickening of a quasi-compact locally Noetherian scheme
  ([Stacks Project, Tag 01Y9], in the form
  `Stacks.Thickenings.isFiniteOrderThickening_of_isThickening`).

The first-order hypothesis is restricted to a quasi-compact separated ambient scheme, because that
is the case its proof covers: `Stacks.TwistedThickeningLift.exists_preimage_nonvanishingLocus_eq`
works on a finite affine cover whose pairwise intersections are affine. Every level of the
filtration is a closed subscheme of the ambient scheme, so it inherits both properties.

## Why the composition carries no exponent bookkeeping

The warning recorded at
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/Affine.lean`, on
`Stacks.Thickenings.AffineBasicOpenLifts.comp`, is that the untwisted composition is the
composition of *inverse images of opens*, with nothing to track, whereas lifting a *power of a
section* along a composite multiplies the exponents. That warning does not apply to
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` as that property is stated, and the reason is
visible in its statement: the degree `m` of the lift is existentially quantified and unconstrained,
and only the nonvanishing *locus* of the lift is controlled. So the exponents do multiply along the
composite — the degree produced over `W` is fed back into the property for `b`, which produces a
degree over `X` that is unrelated to `n` — and the statement absorbs that, because it never claims
a relation between the two degrees. What the composition does have to carry, and what the untwisted
one does not, is the twisting module: the property for the first factor is about `b^* L` and not
about `L`, so `(a ≫ b)^* L ≅ a^*(b^* L)` (`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`)
enters, and with it the invariance of the property under isomorphism of the module.

## Where the first-order case is proved

The first-order case — the hypothesis `hfirst` of
`Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_of_isFirstOrderThickening` — is
`Stacks.TwistedThickeningLift.sectionsLiftAfterPower_of_isFirstOrderThickening`
(`../TwistedThickeningLift/SectionsLift.lean`): the Čech argument of
`Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine` run in charts
of the invertible module.
`Stacks.TwistedThickeningLift.sectionsLiftAfterPower_of_isLocallyNoetherian`
feeds it to this file. No `stacks` attribute is attached in this file: nothing here states any part
of [Stacks Project, Tag 09MS], only a reduction to its first-order case.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory
open Stacks.AmpleClosedImmersion (SectionsLiftAfterPower)
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.AmpleThickeningDevissage

/-! ### Transport of a nonvanishing locus along an isomorphism of invertible modules -/

/-- **The nonvanishing open of a tensor power is unchanged by transporting the section along an
isomorphism of invertible modules.** This is `Stacks.Ample.nonvanishingLocus_congr` at
`Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso`, promoted from an equality of sets to an
equality of opens; `Stacks.Tag01VNChartBasis.isBasisNonvanishing_of_iso` performs the same
computation inline. -/
theorem powNonvanishingOpen_tensorPowModuleIsoOfIso {X : Scheme.{u}} {M N : X.Modules}
    [IsInvertibleModule X M] [IsInvertibleModule X N] (e : M ≅ N) (n : ℕ)
    (s : Γ(tensorPowModule X M (n : ℤ), ⊤)) :
    powNonvanishingOpen X N n
        (Scheme.Modules.Hom.app
          (Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso X M N e n).hom ⊤ s) =
      powNonvanishingOpen X M n s := by
  refine Opens.ext ?_
  rw [coe_powNonvanishingOpen, coe_powNonvanishingOpen,
    nonvanishingLocus_congr (Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso X M N e n) s]

/-- Every section of a tensor power has a transport along an isomorphism with the same
nonvanishing open. -/
private theorem exists_powNonvanishingOpen_eq_of_iso {X : Scheme.{u}} {M N : X.Modules}
    [IsInvertibleModule X M] [IsInvertibleModule X N] (e : M ≅ N) (n : ℕ)
    (s : Γ(tensorPowModule X M (n : ℤ), ⊤)) :
    ∃ s' : Γ(tensorPowModule X N (n : ℤ), ⊤),
      powNonvanishingOpen X N n s' = powNonvanishingOpen X M n s :=
  ⟨_, powNonvanishingOpen_tensorPowModuleIsoOfIso e n s⟩

/-! ### Invariance of the property under isomorphism of the twisting module -/

/-- **`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` is invariant under isomorphism of the
invertible module.** Both the section downstairs and the lift upstairs are transported along the
induced isomorphism of tensor powers, which moves neither nonvanishing locus. -/
theorem sectionsLiftAfterPower_congr {Z X : Scheme.{u}} (i : Z ⟶ X) {L L' : X.Modules}
    [IsInvertibleModule X L] [IsInvertibleModule X L'] (e : L ≅ L')
    (h : SectionsLiftAfterPower i L) : SectionsLiftAfterPower i L' := by
  intro n hn t haff
  obtain ⟨t₀, hZ⟩ := exists_powNonvanishingOpen_eq_of_iso
    ((modulePullback i.toLRSHom.toShHom).mapIso e).symm n t
  obtain ⟨m, hm, t', ht'⟩ := h n hn t₀ (by rw [hZ]; exact haff)
  obtain ⟨t'', ht''⟩ := exists_powNonvanishingOpen_eq_of_iso e m t'
  exact ⟨m, hm, t'', by rw [ht'', ht', hZ]⟩

/-! ### A sufficient condition: surjectivity of the pullback on global sections -/

/-- **The property holds as soon as every positive tensor power has its global sections pulled back
surjectively.** The lift is a preimage of the given section, and [Stacks Project, Tag 0H78] in the
form `Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection` identifies the two nonvanishing
loci. The affineness of the nonvanishing locus is not used, and the degree is not raised. -/
theorem sectionsLiftAfterPower_of_surjective_pullbackPowSection {Z X : Scheme.{u}} (i : Z ⟶ X)
    (L : X.Modules) [IsInvertibleModule X L]
    (hsurj : ∀ n : ℕ, Function.Surjective
      (Stacks.NonvanishingPullback.pullbackPowSection i L n)) :
    SectionsLiftAfterPower i L := by
  intro n hn t _
  obtain ⟨t', ht'⟩ := hsurj n t
  exact ⟨n, hn, t', ht' ▸ (Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection
    i L n t').symm⟩

/-! ### The property for an isomorphism -/

/-- **The module pullback along the identity is the identity**, read for a morphism of schemes:
`Stacks.PullbackPseudofunctor.modulePullbackIdIso` at the ringed space underlying `X`. -/
def pullbackModuleIdIso (X : Scheme.{u}) (L : X.Modules) : pullbackModule (𝟙 X) L ≅ L :=
  (Stacks.PullbackPseudofunctor.modulePullbackIdIso X.toRingedSpace).app L

/-- **The pullback along the inverse of an isomorphism undoes the pullback along it.** This is the
composition law `Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso` at `k⁻¹ ≫ k = 𝟙`, followed
by `Stacks.AmpleThickeningDevissage.pullbackModuleIdIso`. No unitality coherence of the pullback
pseudofunctor is involved: only the existence of the isomorphism is used, never its effect on
sections. -/
def pullbackModuleInvIso {Y Y' : Scheme.{u}} (k : Y ⟶ Y') [IsIso k] (L : Y'.Modules) :
    pullbackModule (inv k) (pullbackModule k L) ≅ L :=
  (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso (inv k) k L).symm ≪≫
    Stacks.RelativeAmpleBaseChange.pullbackModuleCongr (IsIso.inv_hom_id k) L ≪≫
    pullbackModuleIdIso Y' L

/-- **An isomorphism has the lifting property, for every invertible module.** Pull the section back
along the inverse isomorphism and read the result as a section of a power of `L` through
`Stacks.AmpleThickeningDevissage.pullbackModuleInvIso`; the nonvanishing locus upstairs then pulls
back to the given one because `k ≫ k⁻¹ = 𝟙`. -/
theorem sectionsLiftAfterPower_of_isIso {Y Y' : Scheme.{u}} (k : Y ⟶ Y') [IsIso k]
    (L : Y'.Modules) [IsInvertibleModule Y' L] : SectionsLiftAfterPower k L := by
  intro n hn t _
  obtain ⟨s, hs⟩ := exists_powNonvanishingOpen_eq_of_iso (pullbackModuleInvIso k L) n
    (Stacks.NonvanishingPullback.pullbackPowSection (inv k) (pullbackModule k L) n t)
  refine ⟨n, hn, s, ?_⟩
  rw [hs,
    Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection (inv k) (pullbackModule k L) n t,
    ← Scheme.Hom.comp_preimage, IsIso.hom_inv_id]
  simp

/-! ### The composition law -/

/-- **`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` composes along a thickening.** If
`a : Z ⟶ W` is a thickening with the property for `b^* L`, and `b : W ⟶ X` has the property for
`L`, then the composite has the property for `L`.

The nonvanishing open produced on `W` has affine inverse image, hence is itself affine by
`Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage`, which is what lets the property for
`b` be applied to it; this is the only use of the hypothesis that `a` is a thickening, and it is
the same use the untwisted `Stacks.Thickenings.AffineBasicOpenLifts.comp` makes. Inverse images
along the composite are inverse images along the two factors in turn, and the twisting module is
moved by `Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`. -/
theorem sectionsLiftAfterPower_comp {Z W X : Scheme.{u}} {a : Z ⟶ W} {b : W ⟶ X}
    (ha : Stacks.Thickenings.IsThickening a) (L : X.Modules) [IsInvertibleModule X L]
    (h₁ : SectionsLiftAfterPower a (pullbackModule b L)) (h₂ : SectionsLiftAfterPower b L) :
    SectionsLiftAfterPower (a ≫ b) L := by
  intro n hn t haff
  obtain ⟨t₀, hZ⟩ := exists_powNonvanishingOpen_eq_of_iso
    (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso a b L) n t
  obtain ⟨m, hm, s, hs⟩ := h₁ n hn t₀ (by rw [hZ]; exact haff)
  have hsaff : IsAffineOpen (powNonvanishingOpen W (pullbackModule b L) m s) :=
    (Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage ha _).mpr
      (by rw [hs, hZ]; exact haff)
  obtain ⟨p, hp, t', ht'⟩ := h₂ m hm s hsaff
  exact ⟨p, hp, t', by rw [Scheme.Hom.comp_preimage, ht', hs, hZ]⟩

/-! ### The reduction to the first-order case -/

/-- **For a finite-order thickening the property reduces to the first-order case.** Granted
`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` for every first-order thickening and every
invertible module on its ambient scheme, it holds for every finite-order thickening and every
invertible module.

This is the twisted analogue of
`Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening`, and its proof is the same
induction over `Stacks.Thickenings.PowerFiltration`: the thickening factors as the canonical
isomorphism onto level zero, followed by the first-order steps
`Stacks.Thickenings.PowerFiltration.baseStep`, followed by the inclusion of the top level, which
is an isomorphism because the relevant power of the ideal sheaf vanishes. The induction carries
the composite reaching each level, its being a thickening, the property for it — stated for the
pullback of `L` to that level — and its factorisation of the given morphism; the twisting module
is moved from one level to the next by
`Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_congr` along
`Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso`.

Unlike the untwisted statement, no quasi-affineness of the closed subscheme is carried, because the
first-order hypothesis here is not restricted to quasi-affine sources: the affineness the argument
needs is the affineness of the nonvanishing locus, which the property itself hypothesizes.

## Why `hfirst` asks for a quasi-compact separated ambient scheme

That is the generality in which the first-order case is proved
(`Stacks.TwistedThickeningLift.exists_preimage_nonvanishingLocus_eq`), whose finite affine cover
needs affine pairwise intersections. Each level of `Stacks.Thickenings.PowerFiltration` is a closed
subscheme of `Y'`, so it is quasi-compact and separated as soon as `Y'` is; this is how the
induction supplies the two instances to `hfirst` at every step. -/
theorem sectionsLiftAfterPower_of_isFirstOrderThickening
    (hfirst : ∀ (S S' : Scheme.{u}) (m : S ⟶ S'), Stacks.Thickenings.IsFirstOrderThickening m →
      ∀ _ : CompactSpace S', ∀ _ : S'.IsSeparated,
        ∀ N : S'.Modules, ∀ _ : IsInvertibleModule S' N, SectionsLiftAfterPower m N)
    {Y Y' : Scheme.{u}} {t : Y ⟶ Y'} (ht : Stacks.Thickenings.IsFiniteOrderThickening t)
    [CompactSpace Y'] [Y'.IsSeparated]
    (L : Y'.Modules) [IsInvertibleModule Y' L] :
    SectionsLiftAfterPower t L := by
  obtain ⟨hclosed, n, hn⟩ := ht
  have key : ∀ i : ℕ, ∃ c : Y ⟶ Stacks.Thickenings.PowerFiltration.baseLevel t i,
      Stacks.Thickenings.IsThickening c ∧
        SectionsLiftAfterPower c
          (pullbackModule (Stacks.Thickenings.PowerFiltration.baseInclusion t i) L) ∧
        c ≫ Stacks.Thickenings.PowerFiltration.baseInclusion t i = t := by
    intro i
    induction i with
    | zero =>
      have := Stacks.Thickenings.PowerFiltration.baseInitialMap_isIso t hclosed
      exact ⟨Stacks.Thickenings.PowerFiltration.baseInitialMap t,
        Stacks.Thickenings.isThickening_of_isIso _,
        sectionsLiftAfterPower_of_isIso _ _,
        Stacks.Thickenings.PowerFiltration.baseInitialMap_comp_inclusion t⟩
    | succ i ih =>
      obtain ⟨c, hc, hclift, hccomp⟩ := ih
      have hstep : Stacks.Thickenings.IsFirstOrderThickening
          (Stacks.Thickenings.PowerFiltration.baseStep t i) :=
        Stacks.Thickenings.PowerFiltration.baseStep_firstOrder t i
      -- The next level is a closed subscheme of `Y'`, so it inherits the quasi-compactness and
      -- the separatedness that `hfirst` asks of its ambient scheme.
      have : CompactSpace (Stacks.Thickenings.PowerFiltration.baseLevel t (i + 1)) :=
        QuasiCompact.compactSpace_of_compactSpace
          (Stacks.Thickenings.PowerFiltration.baseInclusion t (i + 1))
      have : (Stacks.Thickenings.PowerFiltration.baseLevel t (i + 1)).IsSeparated := by
        constructor
        rw [← Limits.terminal.comp_from
          (Stacks.Thickenings.PowerFiltration.baseInclusion t (i + 1))]
        infer_instance
      refine ⟨c ≫ Stacks.Thickenings.PowerFiltration.baseStep t i,
        Stacks.Thickenings.isThickening_comp hc hstep.isThickening, ?_, ?_⟩
      · refine sectionsLiftAfterPower_comp hc _ ?_
          (hfirst _ _ _ hstep inferInstance inferInstance _ inferInstance)
        refine sectionsLiftAfterPower_congr c ?_ hclift
        exact Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
            (Stacks.Thickenings.PowerFiltration.baseStep_comp_inclusion t i).symm L ≪≫
          Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso
            (Stacks.Thickenings.PowerFiltration.baseStep t i)
            (Stacks.Thickenings.PowerFiltration.baseInclusion t (i + 1)) L
      · rw [Category.assoc, Stacks.Thickenings.PowerFiltration.baseStep_comp_inclusion, hccomp]
  obtain ⟨c, hc, hclift, hccomp⟩ := key n
  have := Stacks.Thickenings.PowerFiltration.baseInclusion_isIso t hn
  have hcomp := sectionsLiftAfterPower_comp (b :=
      Stacks.Thickenings.PowerFiltration.baseInclusion t n) hc L hclift
    (sectionsLiftAfterPower_of_isIso _ _)
  rw [hccomp] at hcomp
  exact hcomp

/-- **The property for a thickening of a quasi-compact locally Noetherian scheme reduces to the
first-order case.** [Stacks Project, Tag 01Y9] in the form
`Stacks.Thickenings.isFiniteOrderThickening_of_isThickening` makes every such thickening of finite
order, and then
`Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_of_isFirstOrderThickening` applies.

The ambient scheme is quasi-compact because the closed subscheme is and a thickening is a
homeomorphism, so for a surjective closed immersion onto a locally Noetherian scheme — the
situation of [Stacks Project, Tag 09MS] — quasi-compactness of the source already suffices.

Separatedness of `Y'` is what the first-order hypothesis asks of each level of the filtration.
In the situation of [Stacks Project, Tag 09MS] it is not an extra assumption: when `t^* L` is
ample, `Y` is separated ([Stacks Project, Tag 01PY]) and so is `Y'` ([Stacks Project, Tag 09MQ]),
which is how `Stacks.TwistedThickeningLift.isAmple_of_isAmple_modulePullback` supplies it. -/
theorem sectionsLiftAfterPower_of_isThickening_of_isLocallyNoetherian
    (hfirst : ∀ (S S' : Scheme.{u}) (m : S ⟶ S'), Stacks.Thickenings.IsFirstOrderThickening m →
      ∀ _ : CompactSpace S', ∀ _ : S'.IsSeparated,
        ∀ N : S'.Modules, ∀ _ : IsInvertibleModule S' N, SectionsLiftAfterPower m N)
    {Y Y' : Scheme.{u}} {t : Y ⟶ Y'} (ht : Stacks.Thickenings.IsThickening t)
    [IsLocallyNoetherian Y'] [CompactSpace Y] [Y'.IsSeparated] (L : Y'.Modules)
    [IsInvertibleModule Y' L] :
    SectionsLiftAfterPower t L :=
  have : CompactSpace Y' := ht.homeomorph.compactSpace
  sectionsLiftAfterPower_of_isFirstOrderThickening hfirst
    (Stacks.Thickenings.isFiniteOrderThickening_of_isThickening ht) L

end Stacks.AmpleThickeningDevissage

end
