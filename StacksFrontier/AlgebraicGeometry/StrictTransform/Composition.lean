module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Iterated

/-!
# Iterated strict transforms of a module: the comparison

Let `f : X ⟶ S` be a morphism of schemes, let `b : S₁ ⟶ S` and `c : S₂ ⟶ S₁` be a composable
pair and let `d : T ⟶ S` be identified with `c ≫ b` as an `S`-scheme. Given ideal sheaves `E` on
`S₁`, `E'` on `S₂` and `E''` on `T`, the strict transform along `c` of the strict transform along
`b` is compared with the strict transform along `d`, over the identification
`Stacks.IteratedBaseChange.iso` of the two base changes.

Both quotient maps out of `pr_X^*F` are epimorphisms, and the comparison is the statement that
they have the same kernel. Each becomes an isomorphism over the open `W` complementary to the
union of the two exceptional preimages — that part is pure geometry and is unconditional here,
since the support identity it needs is `Stacks.StrictTransform.iso_preimage_exceptionalPreimage`
and tag 02OS is now in the repository. The remaining input is that the iterated strict transform
has no nonzero local sections supported in that union: over the exceptional preimage of the
*second* blowup this is its defining property
(`Stacks.StrictTransform.supportedSections_sheaf_eq_zero`), and over the exceptional preimage of
the *first* one it is `Stacks.StrictTransform.supportedSections_sheaf_blowUp_union_eq_zero`
(`StacksFrontier/AlgebraicGeometry/StrictTransform/CompositionBlowUp.lean`). It is carried as the
hypothesis `hQJ` in this file and discharged there, where tag 080I part (1) is proved
unconditionally. **It is not an application of [Stacks, Tag 080H] part (2)**; see the
implementation notes.

## Main results

* `Stacks.StrictTransform.preimage_exceptionalPreimage_union_blowUp`: for a blowup the union of
  the two exceptional preimages is the inverse image of `Supp J ∪ Supp (exceptionalIdeal I)`,
  which is the shape [Stacks, Tag 080H] part (2) speaks in.
* `Stacks.StrictTransform.exists_sheaf_iso_comp`: the comparison of the two quotients, for an
  arbitrary iterated base change, from the support identity and the vanishing of supported
  sections.
* `Stacks.StrictTransform.exists_baseChange_iso_sheaf_iso_comp`: the same together with the
  identification of the two base changes and its two projection formulas, in the shape
  [Stacks, Tag 080I] part (1) states it, for an arbitrary iterated base change.
* `Stacks.StrictTransform.exists_baseChange_iso_sheaf_iso_comp_blowUp`: **[Stacks, Tag 080I]
  part (1)** for blowups, with the support identity discharged. The vanishing of supported
  sections remains as the hypothesis `hQJ`, which
  `StacksFrontier/AlgebraicGeometry/StrictTransform/CompositionBlowUp.lean` discharges; the tag
  sits there.

## Implementation notes

`Stacks.StrictTransform.exists_sheaf_iso_comp` is the fold point for tag 080I part (1). All of
its inputs except `hQJ` are theorems:

* the identification of the two base changes and its two projection formulas are
  `Stacks.IteratedBaseChange.iso`, `Stacks.IteratedBaseChange.iso_hom_fst` and
  `Stacks.IteratedBaseChange.iso_hom_snd`;
* the support identity `hZ` is `Stacks.StrictTransform.iso_preimage_exceptionalPreimage`, whose
  blowup form `Stacks.StrictTransform.iso_preimage_exceptionalPreimage_blowUp` is unconditional
  now that `AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support` ([Stacks, Tag 02OS]
  part (1)) is an instance;
* that each quotient map becomes an isomorphism over `W` is
  `Stacks.StrictTransform.isIso_restrictFunctor_map_π` transported by
  `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_pullback_map` and
  `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_le`;
* monomorphy of the unit on the pulled-back strict transform for `E''` is
  `AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_pullback`, applicable because
  the comparison of base changes is an isomorphism hence an open immersion;
* and the kernel comparison is `Stacks.Abelian.isoOfEpiSameKernel` fed by
  `AlgebraicGeometry.Scheme.Modules.comp_eq_zero_iff_restrictFunctor_map_eq_zero` at `W`.

`hQJ` is the remaining input. In the blowup shape it reads: the strict transform along the second
blowup of the strict transform along the first has no nonzero local sections supported in the
inverse image of `Supp J ∪ Supp (exceptionalIdeal I)`. It resembles [Stacks, Tag 080H]
part (2) for the morphism `pr_{S₁} : X ×_S S₁ ⟶ S₁`, the centre `J` and the effective Cartier
divisor `AlgebraicGeometry.exceptionalIdeal I` (an effective Cartier divisor by
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`), but it is not an application of it.
080H part (2) is `Stacks.StrictTransform.exists_baseChange_iso_sheaf_iso_mul`
(`StacksFrontier/AlgebraicGeometry/StrictTransform/DifferentCentres.lean`); it concludes an existential with a `Nonempty`
isomorphism where `hQJ` is a vanishing statement, and its own statement *takes* the isomorphism
of blowups as a hypothesis, so that route would need 080H part (1) as well. Instead `hQJ`
follows from 02OS(1), `supportedSectionsSubmodule_union_eq`, and the defining properties of the
two strict transforms, as `supportedSections_sheaf_blowUp_union_eq_zero`
(`StacksFrontier/AlgebraicGeometry/StrictTransform/CompositionBlowUp.lean`), and 080I part (1) does not depend on 080H: it
is proved unconditionally and tagged in `CompositionBlowUp.lean`.

The statements are given for an arbitrary module `F`, with no quasi-coherence hypothesis, which
is more general than the tag: `Stacks.StrictTransform.sheaf` is a cokernel and needs none. Where
`F` is quasi-coherent so is every strict transform occurring here, by the instances
`Stacks.StrictTransform.isQuasicoherent_sheaf` and
`Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal`.

Two spelling facts. The comparison is stated three times — flat,
then with the `let`-bindings the tag uses, then for blowups — because the kernel cannot check the
`let`-shaped statement directly against the flat one *at the concrete blowup morphisms*: doing so
is a `(kernel) deterministic timeout`, which no option reaches. Stating the `let`-shaped form for
an arbitrary `b`, `c`, `d` and applying it is free. And the open `W` over which both quotient maps
become isomorphisms is written `Stacks.IteratedBaseChange.iso … ⁻¹ᵁ exceptionalComplement f d E''`
using the *open* `Stacks.StrictTransform.exceptionalComplement`, not as the complement of the
closed `Stacks.StrictTransform.exceptionalPreimage`; the latter needs a `compl_compl` rewrite
under a binder that does not fire with `rw`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080H](https://stacks.math.columbia.edu/tag/080H)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.StrictTransform

open AlgebraicGeometry.Scheme.Modules hiding pullback

variable {X S S₁ S₂ T : Scheme.{u}}

/-- For a blowup of `S` in `I` followed by a blowup of the blowup in `J`, the union of the
inverse image of the first exceptional preimage and the second exceptional preimage is the
inverse image of `Supp J ∪ Supp (exceptionalIdeal I)` under the structure morphism of the
iterated base change. The right-hand side is the shape [Stacks, Tag 080H] part (2) speaks in. -/
public lemma preimage_exceptionalPreimage_union_blowUp (f : X ⟶ S) (I : S.IdealSheafData)
    (J : (AlgebraicGeometry.blowUp I).IdealSheafData) :
    (pullback.fst (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J)).base ⁻¹'
        exceptionalPreimage f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I) ∪
      exceptionalPreimage (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
        (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.exceptionalIdeal J) =
    (pullback.snd (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J) ≫ AlgebraicGeometry.blowUpToBase J).base ⁻¹'
      (J.supportSet ∪ (AlgebraicGeometry.exceptionalIdeal I).supportSet) := by
  have hpre {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (Z : Set C) :
      (p ≫ q).base ⁻¹' Z = p.base ⁻¹' (q.base ⁻¹' Z) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  have h1 : exceptionalPreimage (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
        (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.exceptionalIdeal J) =
      (pullback.snd (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J) ≫
        AlgebraicGeometry.blowUpToBase J).base ⁻¹' J.supportSet := by
    rw [hpre, ← supportSet_exceptionalIdeal J]
    rfl
  have h2 : (pullback.fst (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J)).base ⁻¹'
        exceptionalPreimage f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I) =
      (pullback.snd (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J) ≫ AlgebraicGeometry.blowUpToBase J).base ⁻¹'
        (AlgebraicGeometry.exceptionalIdeal I).supportSet := by
    rw [show exceptionalPreimage f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.exceptionalIdeal I) =
        (pullback.snd f (AlgebraicGeometry.blowUpToBase I)).base ⁻¹'
          (AlgebraicGeometry.exceptionalIdeal I).supportSet from rfl, ← hpre,
      pullback.condition (f := pullback.snd f (AlgebraicGeometry.blowUpToBase I))
        (g := AlgebraicGeometry.blowUpToBase J)]
  rw [h1, h2, ← Set.preimage_union, Set.union_comm]

/-- **The comparison of iterated strict transforms of a module.** Base changing `f` along `b` and
then along `c` is base changing it along `d` (`Stacks.IteratedBaseChange.iso`); under that
identification the strict transform along `c` of the strict transform along `b` is the strict
transform along `d`, compatibly with the quotient maps.

The two inputs are `hZ`, that the inverse image of the exceptional preimage for `E''` is the
union of the inverse image of the exceptional preimage for `E` and the exceptional preimage for
`E'` — which is `Stacks.StrictTransform.iso_preimage_exceptionalPreimage` — and `hQJ`, that the
iterated strict transform has no nonzero local sections supported in that union. For blowups
`hQJ` is `Stacks.StrictTransform.supportedSections_sheaf_blowUp_union_eq_zero`, **not** an
application of [Stacks, Tag 080H] part (2); see the implementation notes of this file. -/
public lemma exists_sheaf_iso_comp (f : X ⟶ S) (b : S₁ ⟶ S) (c : S₂ ⟶ S₁) (d : T ⟶ S)
    (e : Over.mk (c ≫ b) ≅ Over.mk d) (E : S₁.IdealSheafData) (E' : S₂.IdealSheafData)
    (E'' : T.IdealSheafData) (F : X.Modules)
    (hZ : (Stacks.IteratedBaseChange.iso f b c d e).hom.base ⁻¹' exceptionalPreimage f d E'' =
      (pullback.fst (pullback.snd f b) c).base ⁻¹' exceptionalPreimage f b E ∪
        exceptionalPreimage (pullback.snd f b) c E')
    (hQJ : ∀ (U : (baseChange (pullback.snd f b) c).Opens)
        (s : Γ(sheaf (pullback.snd f b) c E' (sheaf f b E F), U)),
        s ∈ (supportedSectionsSubmodule
          ((pullback.fst (pullback.snd f b) c).base ⁻¹' exceptionalPreimage f b E ∪
            exceptionalPreimage (pullback.snd f b) c E')
          (sheaf (pullback.snd f b) c E' (sheaf f b E F))).toSubmodule.obj (op U) → s = 0) :
    ∃ s : (Scheme.Modules.pullback (Stacks.IteratedBaseChange.iso f b c d e).hom).obj
        (sheaf f d E'' F) ≅ sheaf (pullback.snd f b) c E' (sheaf f b E F),
      (Scheme.Modules.pullback (Stacks.IteratedBaseChange.iso f b c d e).hom).map
          (π f d E'' F) ≫ s.hom =
        (((Scheme.Modules.pullbackComp (Stacks.IteratedBaseChange.iso f b c d e).hom
              (pullback.fst f d)).app F) ≪≫
          ((Scheme.Modules.pullbackCongr
              (Stacks.IteratedBaseChange.iso_hom_fst f b c d e)).app F) ≪≫
          ((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd f b) c)
              (pullback.fst f b)).symm.app F)).hom ≫
          (Scheme.Modules.pullback (pullback.fst (pullback.snd f b) c)).map
            (π f b E F) ≫ π (pullback.snd f b) c E' (sheaf f b E F) := by
  set f₁ := pullback.snd f b with hf₁
  set g := Stacks.IteratedBaseChange.iso f b c d e with hgdef
  set pI := pullback.fst f b with hpI
  set pJ := pullback.fst f₁ c with hpJ
  set pK := pullback.fst f d with hpK
  set QI := sheaf f b E F with hQI
  set QJ := sheaf f₁ c E' QI with hQJd
  set QK := sheaf f d E'' F with hQK
  set qI := π f b E F with hqI
  set qJ := π f₁ c E' QI with hqJ
  set qK := π f d E'' F with hqK
  set VI := exceptionalComplement f b E with hVI
  set VJ := exceptionalComplement f₁ c E' with hVJ
  set VK := exceptionalComplement f d E'' with hVK
  set W := g.hom ⁻¹ᵁ VK with hW
  have hWcompl : (W : Set (baseChange f₁ c)) =
      (g.hom.base ⁻¹' exceptionalPreimage f d E'')ᶜ := by
    rw [hW]
    ext x
    simp [hVK, exceptionalPreimage]
  set t : (Scheme.Modules.pullback g.hom).obj ((Scheme.Modules.pullback pK).obj F) ≅
      (Scheme.Modules.pullback pJ).obj ((Scheme.Modules.pullback pI).obj F) :=
    ((Scheme.Modules.pullbackComp g.hom pK).app F) ≪≫
      ((Scheme.Modules.pullbackCongr (Stacks.IteratedBaseChange.iso_hom_fst f b c d e)).app F) ≪≫
      ((Scheme.Modules.pullbackComp pJ pI).symm.app F) with ht
  set r := (Scheme.Modules.pullback g.hom).map qK with hr
  set q := t.hom ≫ (Scheme.Modules.pullback pJ).map qI ≫ qJ with hq
  change ∃ a : (Scheme.Modules.pullback g.hom).obj QK ≅ QJ, r ≫ a.hom = q
  have hWU : ∀ x ∈ W, x ∉ g.hom.base ⁻¹' exceptionalPreimage f d E'' := fun x hx => by
    rw [← Set.mem_compl_iff, ← hWcompl]; exact hx
  have hWI : W ≤ pJ ⁻¹ᵁ VI := fun x hx hi => hWU x hx (hZ ▸ Or.inl hi)
  have hWJ : W ≤ VJ := fun x hx hi => hWU x hx (hZ ▸ Or.inr hi)
  have : IsIso ((restrictFunctor VI.ι).map qI) := isIso_restrictFunctor_map_π f b E F
  have : IsIso ((restrictFunctor VJ.ι).map qJ) := isIso_restrictFunctor_map_π f₁ c E' QI
  have : IsIso ((restrictFunctor VK.ι).map qK) := isIso_restrictFunctor_map_π f d E'' F
  have : IsIso ((restrictFunctor W.ι).map r) :=
    isIso_restrictFunctor_map_pullback_map g.hom VK qK
  have : IsIso ((restrictFunctor (pJ ⁻¹ᵁ VI).ι).map ((Scheme.Modules.pullback pJ).map qI)) :=
    isIso_restrictFunctor_map_pullback_map pJ VI qI
  have : IsIso ((restrictFunctor W.ι).map ((Scheme.Modules.pullback pJ).map qI)) :=
    isIso_restrictFunctor_map_of_le hWI _
  have : IsIso ((restrictFunctor W.ι).map qJ) := isIso_restrictFunctor_map_of_le hWJ qJ
  have : IsIso ((restrictFunctor W.ι).map q) := by
    rw [hq, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hWc : ((W : Set (baseChange f₁ c)))ᶜ = g.hom.base ⁻¹' exceptionalPreimage f d E'' := by
    rw [hWcompl, compl_compl]
  have : IsOpenImmersion g.hom := inferInstance
  have : Mono ((restrictAdjunction W.ι).unit.app ((Scheme.Modules.pullback g.hom).obj QK)) :=
    mono_unit_app_of_supportedSections_eq_zero W _ (hWc ▸ supportedSections_eq_zero_of_pullback
      g.hom (exceptionalPreimage f d E'') QK (supportedSections_sheaf_eq_zero f d E'' F))
  have : Mono ((restrictAdjunction W.ι).unit.app QJ) :=
    mono_unit_app_of_supportedSections_eq_zero W _ (hWc ▸ hZ ▸ hQJ)
  have : Epi r := by rw [hr]; infer_instance
  have : Epi q := by rw [hq]; infer_instance
  have hkey : ∀ {A : (baseChange f₁ c).Modules}
      (a : A ⟶ (Scheme.Modules.pullback g.hom).obj ((Scheme.Modules.pullback pK).obj F)),
      a ≫ r = 0 ↔ a ≫ q = 0 := fun a =>
    (comp_eq_zero_iff_restrictFunctor_map_eq_zero W r a).trans
      (comp_eq_zero_iff_restrictFunctor_map_eq_zero W q a).symm
  exact ⟨Stacks.Abelian.isoOfEpiSameKernel r q hkey,
    Stacks.Abelian.isoOfEpiSameKernel_fac r q hkey⟩

/-- **The comparison of iterated strict transforms, in the shape [Stacks, Tag 080I] part (1)
states it**, for an arbitrary iterated base change: the identification `g` of the two base
changes, its two projection formulas, and the induced isomorphism of module sheaves commuting
with the quotient maps.

This is `Stacks.StrictTransform.exists_sheaf_iso_comp` packaged with
`Stacks.IteratedBaseChange.iso_hom_fst` and `Stacks.IteratedBaseChange.iso_hom_snd`. It is stated
for arbitrary `b`, `c`, `d` rather than only for blowups because the kernel cannot check this
`let`-shaped statement against the flat one at the concrete blowup morphisms; see the
implementation notes of this file. -/
public lemma exists_baseChange_iso_sheaf_iso_comp (f : X ⟶ S) (b : S₁ ⟶ S) (c : S₂ ⟶ S₁)
    (d : T ⟶ S) (e : Over.mk (c ≫ b) ≅ Over.mk d) (E : S₁.IdealSheafData)
    (E' : S₂.IdealSheafData) (E'' : T.IdealSheafData) (F : X.Modules)
    (hZ : (Stacks.IteratedBaseChange.iso f b c d e).hom.base ⁻¹' exceptionalPreimage f d E'' =
      (pullback.fst (pullback.snd f b) c).base ⁻¹' exceptionalPreimage f b E ∪
        exceptionalPreimage (pullback.snd f b) c E')
    (hQJ : ∀ (U : (baseChange (pullback.snd f b) c).Opens)
        (s : Γ(sheaf (pullback.snd f b) c E' (sheaf f b E F), U)),
        s ∈ (supportedSectionsSubmodule
          ((pullback.fst (pullback.snd f b) c).base ⁻¹' exceptionalPreimage f b E ∪
            exceptionalPreimage (pullback.snd f b) c E')
          (sheaf (pullback.snd f b) c E' (sheaf f b E F))).toSubmodule.obj (op U) → s = 0) :
    let f₁ : baseChange f b ⟶ S₁ := pullback.snd f b
    let pK := pullback.fst f d
    let pI := pullback.fst f b
    let pJ := pullback.fst f₁ c
    let FK := (Scheme.Modules.pullback pK).obj F
    let FI := (Scheme.Modules.pullback pI).obj F
    let QK := sheaf f d E'' F
    let QI := sheaf f b E F
    let QJ := sheaf f₁ c E' QI
    ∃ (g : baseChange f₁ c ≅ baseChange f d) (hg : g.hom ≫ pK = pJ ≫ pI),
      (g.hom ≫ pullback.snd f d = pullback.snd f₁ c ≫ e.hom.left) ∧
      ∃ s : (Scheme.Modules.pullback g.hom).obj QK ≅ QJ,
        let t : (Scheme.Modules.pullback g.hom).obj FK ≅ (Scheme.Modules.pullback pJ).obj FI :=
          ((Scheme.Modules.pullbackComp g.hom pK).app F) ≪≫
            ((Scheme.Modules.pullbackCongr hg).app F) ≪≫
            ((Scheme.Modules.pullbackComp pJ pI).symm.app F)
        let qK : FK ⟶ QK := π f d E'' F
        let qI : FI ⟶ QI := π f b E F
        let qJ : (Scheme.Modules.pullback pJ).obj QI ⟶ QJ := π f₁ c E' QI
        (Scheme.Modules.pullback g.hom).map qK ≫ s.hom =
          t.hom ≫ (Scheme.Modules.pullback pJ).map qI ≫ qJ :=
  ⟨Stacks.IteratedBaseChange.iso f b c d e,
    Stacks.IteratedBaseChange.iso_hom_fst f b c d e,
    Stacks.IteratedBaseChange.iso_hom_snd f b c d e,
    exists_sheaf_iso_comp f b c d e E E' E'' F hZ hQJ⟩

/-- **[Stacks, Tag 080I] part (1)**, in the shape that tag states it: for `b` the blowup of `S`
in `I`, `c` the blowup of the blowup in `J`, and `d` the blowup of `S` in a third centre `K`
whose support is `Supp I ∪ b(Supp J)`, the iterated strict transform of `F` agrees with the
strict transform in the composite centre, compatibly with both projections and with the quotient
maps.

The support identity is discharged — it is
`Stacks.StrictTransform.iso_preimage_exceptionalPreimage_blowUp`, unconditional now that
[Stacks, Tag 02OS] part (1) is the instance
`AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`. The hypothesis `hQJ` that remains
is `Stacks.StrictTransform.supportedSections_sheaf_blowUp_union_eq_zero`, which discharges it, so
tag 080I part (1) is proved unconditionally as
`Stacks.StrictTransform.strictTransformSheaf_comp_blowUp`
(`StacksFrontier/AlgebraicGeometry/StrictTransform/CompositionBlowUp.lean`). Because `hQJ` is a
hypothesis *here* rather than a theorem, **no `@[stacks 080I]` attribute is attached to this
declaration**: the tag asserts the comparison unconditionally and sits on the theorem in that
file. `hQJ` is **not** an application of [Stacks, Tag 080H] part (2): the two propositions have different shapes
(080H part (2) concludes an existential with an isomorphism, `hQJ` is a vanishing statement), and
080H part (2)'s own statement takes the isomorphism of blowups as a hypothesis. See the
implementation notes of this file. -/
public lemma exists_baseChange_iso_sheaf_iso_comp_blowUp (f : X ⟶ S) (I K : S.IdealSheafData)
    (J : (AlgebraicGeometry.blowUp I).IdealSheafData)
    (hK : K.supportSet = I.supportSet ∪
      (AlgebraicGeometry.blowUpToBase I).base '' J.supportSet)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase J ≫ AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase K))
    (F : X.Modules)
    (hQJ : ∀ (U : (baseChange (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J)).Opens)
        (s : Γ(sheaf (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.exceptionalIdeal J)
          (sheaf f (AlgebraicGeometry.blowUpToBase I)
            (AlgebraicGeometry.exceptionalIdeal I) F), U)),
        s ∈ (supportedSectionsSubmodule
            ((pullback.snd (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
              (AlgebraicGeometry.blowUpToBase J) ≫
                AlgebraicGeometry.blowUpToBase J).base ⁻¹'
              (J.supportSet ∪ (AlgebraicGeometry.exceptionalIdeal I).supportSet))
            (sheaf (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
              (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.exceptionalIdeal J)
              (sheaf f (AlgebraicGeometry.blowUpToBase I)
                (AlgebraicGeometry.exceptionalIdeal I) F))).toSubmodule.obj (op U) → s = 0) :
    let b := AlgebraicGeometry.blowUpToBase I
    let f₁ : baseChange f b ⟶ AlgebraicGeometry.blowUp I := pullback.snd f b
    let c := AlgebraicGeometry.blowUpToBase J
    let d := AlgebraicGeometry.blowUpToBase K
    let pK := pullback.fst f d
    let pI := pullback.fst f b
    let pJ := pullback.fst f₁ c
    let FK := (Scheme.Modules.pullback pK).obj F
    let FI := (Scheme.Modules.pullback pI).obj F
    let QK := sheaf f d (AlgebraicGeometry.exceptionalIdeal K) F
    let QI := sheaf f b (AlgebraicGeometry.exceptionalIdeal I) F
    let QJ := sheaf f₁ c (AlgebraicGeometry.exceptionalIdeal J) QI
    ∃ (g : baseChange f₁ c ≅ baseChange f d) (hg : g.hom ≫ pK = pJ ≫ pI),
      (g.hom ≫ pullback.snd f d = pullback.snd f₁ c ≫ e.hom.left) ∧
      ∃ s : (Scheme.Modules.pullback g.hom).obj QK ≅ QJ,
        let t : (Scheme.Modules.pullback g.hom).obj FK ≅ (Scheme.Modules.pullback pJ).obj FI :=
          ((Scheme.Modules.pullbackComp g.hom pK).app F) ≪≫
            ((Scheme.Modules.pullbackCongr hg).app F) ≪≫
            ((Scheme.Modules.pullbackComp pJ pI).symm.app F)
        let qK : FK ⟶ QK := π f d (AlgebraicGeometry.exceptionalIdeal K) F
        let qI : FI ⟶ QI := π f b (AlgebraicGeometry.exceptionalIdeal I) F
        let qJ : (Scheme.Modules.pullback pJ).obj QI ⟶ QJ :=
          π f₁ c (AlgebraicGeometry.exceptionalIdeal J) QI
        (Scheme.Modules.pullback g.hom).map qK ≫ s.hom =
          t.hom ≫ (Scheme.Modules.pullback pJ).map qI ≫ qJ :=
  exists_baseChange_iso_sheaf_iso_comp f (AlgebraicGeometry.blowUpToBase I)
    (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.blowUpToBase K) e
    (AlgebraicGeometry.exceptionalIdeal I) (AlgebraicGeometry.exceptionalIdeal J)
    (AlgebraicGeometry.exceptionalIdeal K) F
    (iso_preimage_exceptionalPreimage_blowUp f I K J hK e)
    (by rw [preimage_exceptionalPreimage_union_blowUp f I J]; exact hQJ)

end Stacks.StrictTransform

end
