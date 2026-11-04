module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.GenericFibre
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.ChartFromGenerators
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreTrivialization
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericStalkGenerator
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MultiplierGlobalUnit
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.PullbackMeromorphicFamily
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
import StacksCore.Tactic.StacksAttribute

/-!
# An invertible module trivial on the generic fibre is pulled back from the base

Let `φ : X ⟶ Y` be a flat morphism of locally Noetherian schemes with integral fibres, `Y`
integral and normal, and `φ` quasi-compact or locally of finite type. An invertible
`𝒪_X`-module whose restriction to the generic fibre is trivial is isomorphic to `φ^*𝒩` for an
invertible `𝒪_Y`-module `𝒩`.

The family `φ^*(g_i) s` of meromorphic multipliers is turned here into the chart datum with
transition units that the descent consumes: the chart is the one whose preimage is the
generating locus of a member of the family, its generator is the restriction of that member,
and the transition unit of two chart generators is the pullback of the regular unit relating
the two multipliers.

## Main results

* `Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isPullMeromorphicFamily`: the
  conclusion from the family, its regular meromorphic section, and its generating property.
* `Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isTrivial_genericFiber`:
  [Stacks, Tag 0BD7] with the family carried as a hypothesis.
* `Stacks.InvertiblePullback`'s
  `exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_named_section`: the same with
  the family hypothesis naming its meromorphic section, which is what leaves only two conjuncts
  in it.

## Implementation notes

The transition unit is computed rather than chosen: the chart generator over `φ^{-1}(W)` is the
restriction of the family member `t i`, by `Stacks.SheafOfModules.generatorRestrict_val` and the
composition of two restrictions, so
`Stacks.InvertiblePullback.restrictₛₗ_eq_smul_of_isPullMeromorphicFamily` identifies the ratio
of two chart generators with the pullback of the unit relating the two multipliers, and
`Stacks.SheafOfModules.generatorRatio_unique` turns that identification into the datum.

That a chart is contained in the open carrying its family member is not part of the chart
construction, which only gives the equality of preimages; it is recovered from surjectivity of
`φ`, which is hypothesis (3) through `AlgebraicGeometry.Surjective.of_nonempty_fiber`.

The transition unit on the base is no longer assumed. On the intersection of two charts every
point of `X` above it lies in both generating loci, so
`Stacks.InvertiblePullback.exists_units_restrictₛₗ_eq_smul_of_forall_mem_generatingLocus`
produces the unit there from the regularity of `s` alone.

The attributes on the last two results carry a scope label. Their hypothesis `hfam` — the
family, the regularity of its meromorphic section, and its generating property — is the
conclusion of the penultimate paragraph of the source's proof; it is proved in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/LocalFamilyAgreement.lean`, whose
`Stacks.InvertiblePullback`'s
`exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_flat` carries the tag with no
scope label. The affine input `hfam` rests on is
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/AffineDescent.lean`. Normality of `Y` and
local Noetherianness of `X` are stated as the source states them but are consumed only inside
`hfam`, where the affine step uses them.

That `hfam` has three conjuncts and the `_of_named_section` variant two is a consequence of
where `s` is bound, not of any new mathematics about the family. With `s` existentially
quantified *inside* `hfam`'s own conclusion nothing outside can know which meromorphic section
it is, so the conjunct `IsRegularMeromorphicSection` is not deducible however much is known
about the section the first paragraph of the source builds. Naming it
`AlgebraicGeometry.meromorphicSectionOfGenericStalk X L m` for the generator `m` of the generic
stalk makes it deducible, from
`AlgebraicGeometry.isRegularMeromorphicSection_of_span_eq_top_grpStalk`. Neither form implies
the other: the named one pins `s`, which the source's proof does produce.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0BCM](https://stacks.math.columbia.edu/tag/0BCM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Meromorphic

universe u

namespace Stacks.InvertiblePullback

open Stacks.SheafOfModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (L : X.Modules)
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]

/-- **The conclusion of [Stacks, Tag 0BD7] from the family `φ^*(g_i) s`.** The family consists
of meromorphic multipliers `g i` on opens `A i` of the base together with the regular sections
`t i` of `ℒ` on `φ^{-1}(A i)` that the products are; `hs` says the common factor `s` is a
regular meromorphic section, and `hex` that some member generates `ℒ` at each point. The chart
whose preimage is the generating locus of a member then carries that member as a generator, and
the unit relating two multipliers over the intersection of two charts pulls back to the ratio
of two such generators. -/
theorem exists_isInvertible_pullback_iso_of_isPullMeromorphicFamily [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (s : MeromorphicSection X.sheaf L)
    {ι : Type*} {A : ι → Y.Opens}
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier)))
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamily f L s g t)
    (hex : ∀ z : X.toRingedSpace.carrier, ∃ i, z ∈ generatingLocus L (t i))
    (hfibre : ∀ y : Y, AlgebraicGeometry.IsIntegral (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    ∃ N : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat)).mp Y.IsSheaf) N ∧
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ L) := by
  classical
  have hne : ∀ y : Y, Nonempty (f.fiber y) := fun y => (hfibre y).nonempty
  have hsurj : Function.Surjective f.base := (Surjective.of_nonempty_fiber f hne).surj
  have hirr : ∀ y : Y, IsIrreducible (f.base ⁻¹' {y}) := by
    intro y
    have := hfibre y
    exact isIrreducible_preimage_singleton_of_isIntegral_fiber f y
  have hg := exists_isUnit_germ_restrictₛₗ_eq_smul_of_isPullMeromorphicFamily f L s g t hs ht
  have hagree := forall_mem_generatingLocus_iff_of_isPullMeromorphicFamily f L s g t hL ht hg
  obtain ⟨chart, hmem, hpre⟩ :=
    exists_chart_coe_preimage_eq_generatingLocus f L t hex hirr hagree hne hfinite
  choose idx hidx using hpre
  have hWU : ∀ y : Y, ((f ⁻¹ᵁ chart y : X.Opens) : Opens X.toRingedSpace.carrier) ≤
      (f ⁻¹ᵁ A (idx y) : X.Opens) := fun y z hz =>
    generatingLocus_le L (t (idx y)) ((hidx y).subset hz)
  have hle : ∀ y : Y, chart y ≤ A (idx y) := by
    intro y v hv
    obtain ⟨x, rfl⟩ := hsurj v
    exact hWU y hv
  have hgenex : ∀ y : Y, ∃ G : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ chart y),
      G.val = L.val.restrictₛₗ (homOfLE (hWU y)).op (t (idx y)) := fun y =>
    ⟨generatorSectionsOfForallGermNotMemMaximalIdeal L (t (idx y)) (f ⁻¹ᵁ chart y) (hWU y)
      fun z hz => notMem_maximalIdeal_smul_of_mem_generatingLocus L
        ((hidx y).subset hz) (hWU y hz), rfl⟩
  choose gen hgen using hgenex
  have hgenval : ∀ (y : Y) (W : Y.Opens) (hW : W ≤ chart y)
      (hp : ((f ⁻¹ᵁ W : X.Opens) : Opens X.toRingedSpace.carrier) ≤
        (f ⁻¹ᵁ A (idx y) : X.Opens)),
      (chartGen gen y hW).val = L.val.restrictₛₗ (homOfLE hp).op (t (idx y)) := by
    intro y W hW hp
    have h1 : (chartGen gen y hW).val =
        L.val.restrictₛₗ (homOfLE ((Opens.map f.base).map (homOfLE hW)).le).op ((gen y).val) :=
      rfl
    rw [h1, hgen y]
    exact (PresheafOfModules.map_comp_apply L.val (homOfLE (hWU y)).op
      ((Opens.map f.base).map (homOfLE hW)).op (t (idx y))).symm
  refine exists_isInvertible_pullback_iso_of_flat_of_inf gen hne hmem ?_
  intro i j
  have hAi : chart i ⊓ chart j ≤ A (idx i) := le_trans inf_le_left (hle i)
  have hAj : chart i ⊓ chart j ≤ A (idx j) := le_trans inf_le_right (hle j)
  have hgen : ∀ v : Y, v ∈ chart i ⊓ chart j → ∃ x : X, f.base x = v ∧
      x ∈ generatingLocus L (t (idx i)) ∧ x ∈ generatingLocus L (t (idx j)) := by
    rintro v hv
    obtain ⟨x, rfl⟩ := hsurj v
    exact ⟨x, rfl, (hidx i).subset hv.1, (hidx j).subset hv.2⟩
  obtain ⟨w, hw⟩ := exists_units_restrictₛₗ_eq_smul_of_forall_mem_generatingLocus f L s g t hs ht
    (idx i) (idx j) hAi hAj hgen
  refine ⟨w, ?_⟩
  have hpi : ((f ⁻¹ᵁ (chart i ⊓ chart j) : X.Opens) : Opens X.toRingedSpace.carrier) ≤
      (f ⁻¹ᵁ A (idx i) : X.Opens) := fun z hz => hAi hz
  have hpj : ((f ⁻¹ᵁ (chart i ⊓ chart j) : X.Opens) : Opens X.toRingedSpace.carrier) ≤
      (f ⁻¹ᵁ A (idx j) : X.Opens) := fun z hz => hAj hz
  have key := restrictₛₗ_eq_smul_of_isPullMeromorphicFamily f L s g t hL ht (idx i) (idx j)
    hAi hAj w.val hw hpi hpj
  refine generatorRatio_unique (X := X.toRingedSpace) L (f ⁻¹ᵁ (chart i ⊓ chart j))
    (chartGen gen j inf_le_right) (chartGen gen i inf_le_left) _ ?_
  rw [hgenval i (chart i ⊓ chart j) inf_le_left hpi,
    hgenval j (chart i ⊓ chart j) inf_le_right hpj]
  exact key

/-- The descent step of [Stacks, Tag 0BD7], with the family of meromorphic multipliers carried
as the hypothesis `hfam` rather than produced.

`hfam` asserts the source's own description of the family: the products `φ^*(g_i) s` are regular
sections, the factor `s` is a regular meromorphic section, and some member generates `ℒ` at every
point. Because that is a hypothesis here rather than a theorem, **no `@[stacks 0BD7]` attribute
is attached**: a registration may only sit on a declaration that proves the tag under the
source's hypotheses. The unconditional form, which produces the family and carries the tag, is
`Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_flat`
in `StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.LocalFamilyAgreement`. -/
theorem exists_isInvertible_pullback_iso_of_isTrivial_genericFiber
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsIntegral Y] [IsNormal Y]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (hfibre : ∀ y : Y, AlgebraicGeometry.IsIntegral (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f)
    (hgeneric : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))
    (hfam :
      letI : AlgebraicGeometry.IsIntegral (f.fiber (genericPoint Y)) := hfibre (genericPoint Y)
      letI : AlgebraicGeometry.IsIntegral X := isIntegral_of_flat_of_isIntegral_genericFiber f
      letI : Module (ringStalk X.toRingedSpace (genericPoint X))
          (grpStalk X.toRingedSpace L.val (genericPoint X)) :=
        Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace L.val
          (genericPoint X)
      (∃ m : grpStalk X.toRingedSpace L.val (genericPoint X),
        Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} = ⊤) →
      ∃ (s : MeromorphicSection X.sheaf L) (ι : Type u) (A : ι → Y.Opens)
        (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
        (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier))),
        IsRegularMeromorphicSection X.sheaf L s ∧
          IsPullMeromorphicFamily f L s g t ∧
            ∀ z : X.toRingedSpace.carrier, ∃ i, z ∈ generatingLocus L (t i)) :
    ∃ N : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat)).mp Y.IsSheaf) N ∧
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ L) := by
  have hne : ∀ y : Y, Nonempty (f.fiber y) := fun y => (hfibre y).nonempty
  have hsurj : Function.Surjective f.base :=
    (Surjective.of_nonempty_fiber f hne).surj
  have : AlgebraicGeometry.IsIntegral (f.fiber (genericPoint Y)) := hfibre (genericPoint Y)
  have : AlgebraicGeometry.IsIntegral X := isIntegral_of_flat_of_isIntegral_genericFiber f
  obtain ⟨s, ι, A, g, t, hs, ht, hex⟩ := hfam
    (exists_span_eq_top_stalk_genericPoint_of_isTrivial_genericFiber f hsurj L hgeneric)
  exact exists_isInvertible_pullback_iso_of_isPullMeromorphicFamily f L hL s g t hs ht hex
    hfibre hfinite

/-- **[Stacks, Tag 0BD7] with the family hypothesis naming its meromorphic section, and the
regularity conjunct discharged.** The hypothesis `hfam` of
`Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isTrivial_genericFiber`
existentially quantifies `s` inside its own conclusion, so nothing outside it can know that `s`
is the section the first paragraph of the source builds; its first conjunct,
`IsRegularMeromorphicSection`, is therefore not deducible there however much is known about that
section. Here `s` is `AlgebraicGeometry.meromorphicSectionOfGenericStalk X L m` for the generator
`m` of the generic stalk that the first paragraph produces, and the conjunct follows from
`AlgebraicGeometry.isRegularMeromorphicSection_of_span_eq_top_grpStalk`.

Two conjuncts remain in `hfam`: that the products `φ^*(g_i) s` are the regular sections `t i`,
and that some `t i` generates `ℒ` at every point. They are the penultimate paragraph of the
source's proof and are still owed. -/
theorem exists_isInvertible_pullback_iso_of_isTrivial_genericFiber_of_named_section
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsIntegral Y] [IsNormal Y]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (hfibre : ∀ y : Y, AlgebraicGeometry.IsIntegral (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f)
    (hgeneric : AlgebraicGeometry.SheafOfModules.IsTrivial
      (f.fiber (genericPoint Y)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (f.fiber (genericPoint Y)).IsSheaf)
      ((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj L))
    (hfam :
      letI : AlgebraicGeometry.IsIntegral (f.fiber (genericPoint Y)) := hfibre (genericPoint Y)
      letI : AlgebraicGeometry.IsIntegral X := isIntegral_of_flat_of_isIntegral_genericFiber f
      letI : Module (ringStalk X.toRingedSpace (genericPoint X))
          (grpStalk X.toRingedSpace L.val (genericPoint X)) :=
        Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace L.val
          (genericPoint X)
      letI : L.IsQuasicoherent :=
        Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible X L
      (∃ m : grpStalk X.toRingedSpace L.val (genericPoint X),
        Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} = ⊤) →
      ∃ (m : grpStalk X.toRingedSpace L.val (genericPoint X)) (ι : Type u) (A : ι → Y.Opens)
        (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
        (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier))),
        Submodule.span (ringStalk X.toRingedSpace (genericPoint X)) {m} = ⊤ ∧
          IsPullMeromorphicFamily f L (meromorphicSectionOfGenericStalk X L m) g t ∧
            ∀ z : X.toRingedSpace.carrier, ∃ i, z ∈ generatingLocus L (t i)) :
    ∃ N : Y.Modules,
      AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf
          ((Presheaf.isSheaf_iff_isSheaf_comp _ Y.presheaf
            (forget₂ CommRingCat RingCat)).mp Y.IsSheaf) N ∧
        Nonempty ((Scheme.Modules.pullback f).obj N ≅ L) := by
  have hne : ∀ y : Y, Nonempty (f.fiber y) := fun y => (hfibre y).nonempty
  have hsurj : Function.Surjective f.base :=
    (Surjective.of_nonempty_fiber f hne).surj
  have : AlgebraicGeometry.IsIntegral (f.fiber (genericPoint Y)) := hfibre (genericPoint Y)
  have : AlgebraicGeometry.IsIntegral X := isIntegral_of_flat_of_isIntegral_genericFiber f
  have : L.IsQuasicoherent :=
    Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible X L
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL
  obtain ⟨m, ι, A, g, t, hm, ht, hex⟩ := hfam
    (exists_span_eq_top_stalk_genericPoint_of_isTrivial_genericFiber f hsurj L hgeneric)
  exact exists_isInvertible_pullback_iso_of_isPullMeromorphicFamily f L hL _ g t
    (AlgebraicGeometry.isRegularMeromorphicSection_of_span_eq_top_grpStalk X L m hm) ht hex
    hfibre hfinite

end Stacks.InvertiblePullback

end
