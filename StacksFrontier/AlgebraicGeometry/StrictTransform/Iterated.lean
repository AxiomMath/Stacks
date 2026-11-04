module

public import StacksFrontier.AlgebraicGeometry.IteratedBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent

/-!
# Iterated strict transforms: the geometry of the comparison

Let `f : X ⟶ S` be a morphism of schemes, let `b : S₁ ⟶ S` and `c : S₂ ⟶ S₁` be a composable
pair, and let `d : T ⟶ S` be identified with `c ≫ b` as an `S`-scheme. Base changing `f` along
`b` and then along `c` gives the same scheme as base changing it along `d`
(`Stacks.IteratedBaseChange.iso`). This file transports the *exceptional preimage* of
`Stacks.StrictTransform` across that identification: given ideal sheaves `E` on `S₁`, `E'` on
`S₂` and `E''` on `T`, the inverse image of `pr_T^{-1}(Supp E'')` is the union of the inverse
image of `pr_{S₁}^{-1}(Supp E)` and of `pr_{S₂}^{-1}(Supp E')`, as soon as the corresponding
identity of supports holds on `S₂`.

For the blowup situation of tag 080I — `b` the blowup of `S` in `I`, `c` the blowup of the
blowup in `J`, `d` the blowup of `S` in a third centre `K` whose support is
`Supp I ∪ b(Supp J)` — that identity of supports on `S₂` follows from the identity
`b^{-1}(Supp K) = Supp(b^{-1}I) ∪ Supp J` on `S₁`, which in turn needs the blowup morphism to be
injective over the complement of its centre. See the implementation notes.

## Main results

* `AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq`: enlarging the support
  condition by a set on which the module has no nonzero sections over opens disjoint from the
  original set does not enlarge the submodule of supported sections.
* `Stacks.StrictTransform.injOn_of_isIso_morphismRestrict` and
  `Stacks.StrictTransform.injOn_preimage_of_isIso_morphismRestrict`: a morphism that restricts to
  an isomorphism over an open is injective over that open.
* `Stacks.StrictTransform.preimage_supportSet_union_of_injOn`: the identity
  `b^{-1}(Supp K) = b^{-1}(Supp I) ∪ Supp J` from `Supp K = Supp I ∪ b(Supp J)` and injectivity
  of `b` away from `Supp I`.
* `Stacks.StrictTransform.supportSet_exceptionalIdeal`: the support of the exceptional ideal of a
  blowup is the inverse image of the support of the centre.
* `Stacks.StrictTransform.preimage_supportSet_blowUp`: the previous two combined, for a blowup.
* `Stacks.StrictTransform.isOpenImmersion_preimage_ι_comp_fst` and
  `Stacks.StrictTransform.isOpenImmersion_exceptionalComplement_ι_comp_fst`: over an open where
  the second morphism is an isomorphism — for a blowup, away from the exceptional divisor — the
  projection of the base change to `X` is an open immersion.
* `Stacks.StrictTransform.exceptionalComplement_blowUp`: the open complement of the exceptional
  preimage of a blowup is the inverse image of the open complement of the centre.
* `Stacks.StrictTransform.iso_preimage_exceptionalPreimage`: **the transport**, in the generality
  of `Stacks.IteratedBaseChange.iso`.
* `Stacks.StrictTransform.iso_preimage_exceptionalPreimage_blowUp`: the transport in the shape
  tag 080I states it, from the hypothesis `Supp K = Supp I ∪ b(Supp J)` of that tag.

## Implementation notes

The transport `Stacks.StrictTransform.iso_preimage_exceptionalPreimage` mentions neither `b` nor
`f` in its hypothesis: everything it needs is the identity
`e_{hom}^{left,-1}(Supp E'') = c^{-1}(Supp E) ∪ Supp E'` of subsets of `S₂`, because
`Stacks.IteratedBaseChange.iso_hom_snd` identifies the composite of the transport with the
projection to `T` as the projection to `S₂` followed by `e.hom.left`, and the remaining
`pr_{S₁}` term is moved across by `CategoryTheory.Limits.pullback.condition`. That is why the
statement is free of blowups, and why the blowup instance below is a two-step rewrite.

**Injectivity away from the centre is [Stacks, Tag 02OS], and it IS now in the repository --
this paragraph used to deny it.** The declaration carrying the tag is
`AlgebraicGeometry.isIso_blowUp_restrict_compl_support`, with
`@[stacks 02OS "isomorphism_off_center"]`, in
`StacksFrontier/AlgebraicGeometry/Blowup/IsomorphismOffCenter/Basic.lean`; at the `.compl`
spelling of the open it is available to instance synthesis as the untagged wrapper
`AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support` in
`StacksFrontier/AlgebraicGeometry/Blowup/IsoOffCentre.lean`, whose body is that theorem. Both are
verified axiom-clean. So the three statements named below CAN now drop their hypothesis and become
unconditional, and **tag 080I's hypothesis `hK` is usable now** -- that work is not done here only
because this file is not the place for it. It is
carried here as the hypothesis `IsIso (AlgebraicGeometry.blowUpToBase I ∣_ I.support.compl)`,
which is literally the hypothesis `Stacks.Blowup.exists_nonempty_isTerminal_blowUp`
(`StacksFrontier/AlgebraicGeometry/Blowup/TerminalRelativeProj.lean`) already takes, and the
blowup instance of the `[IsIso (b ∣_ V)]` hypothesis of
`Stacks.Blowup.exists_hom_of_isOpenCover`
(`StacksFrontier/AlgebraicGeometry/Blowup/Existence.lean`). Nothing in the tree produces one,
so `Stacks.StrictTransform.preimage_supportSet_blowUp`,
`Stacks.StrictTransform.isOpenImmersion_exceptionalComplement_ι_comp_fst` and
`Stacks.StrictTransform.iso_preimage_exceptionalPreimage_blowUp` carry it and no `@[stacks]`
attribute. Discharging that hypothesis from the library's 02OS instance is a small, well-scoped
step not taken here. The three statements whose hypotheses mention only `b` and `V` —
`injOn_of_isIso_morphismRestrict`, `injOn_preimage_of_isIso_morphismRestrict` and
`isOpenImmersion_preimage_ι_comp_fst` — are unconditional in that generality and are the two
places tag 02OS is used at all in the tag 080I argument.

`Stacks.StrictTransform.exceptionalPreimage` is an `abbrev` for a preimage of
`AlgebraicGeometry.Scheme.IdealSheafData.support`, a `TopologicalSpace.Closeds`, whereas the
statement of tag 080I speaks of `AlgebraicGeometry.Scheme.IdealSheafData.supportSet`. The two are
the same term — `support` is `supportSet` bundled with its closedness — so the statements below
are phrased with `supportSet` throughout and the identifications are `rfl`.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Enlarging the support condition from a closed set `Z` to `Z ∪ W` does not change the
submodule of supported sections, provided `F` has no nonzero sections supported in `W` over any
open disjoint from `Z`. This is how the strict transform for a bigger centre is recognised as the
strict transform for the smaller one. -/
public lemma supportedSectionsSubmodule_union_eq (Z W : Set X) (hZ : IsClosed Z)
    (F : X.Modules)
    (h : ∀ U : X.Opens, (U : Set X) ∩ Z = ∅ → ∀ s : Γ(F, U),
      s ∈ (supportedSectionsSubmodule W F).toSubmodule.obj (op U) → s = 0) :
    supportedSectionsSubmodule (Z ∪ W) F = supportedSectionsSubmodule Z F := by
  ext ⟨U⟩ s
  refine (mem_supportedSectionsSubmodule_iff (Z ∪ W) F U s).trans
    (Iff.trans ?_ (mem_supportedSectionsSubmodule_iff Z F U s).symm)
  refine ⟨fun hs x hx hxZ ↦ ?_, fun hs x hx hx' ↦ hs x hx fun hxZ ↦ hx' (Or.inl hxZ)⟩
  set V : X.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ with hV
  have hxV : x ∈ V := ⟨hx, hxZ⟩
  have hle : V ≤ U := inf_le_left
  have ht : F.val.presheaf.map (homOfLE hle).op s ∈
      (supportedSectionsSubmodule W F).toSubmodule.obj (op V) := by
    refine (mem_supportedSectionsSubmodule_iff W F V _).mpr ?_
    intro y hyV hyW
    exact (TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hle) y hyV s).trans
      (hs y hyV.1 fun hy ↦ hy.elim (fun hyZ ↦ hyV.2 hyZ) hyW)
  have hV0 : (V : Set X) ∩ Z = ∅ := by
    ext y
    exact ⟨fun hy ↦ hy.1.2 hy.2, fun hy ↦ hy.elim⟩
  have h0 := h V hV0 _ ht
  exact (TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hle) x hxV s).symm.trans
    ((congrArg (fun t : Γ(F, V) ↦
        (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf V x hxV)) t) h0).trans
      (map_zero _))

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.StrictTransform

variable {X S S' S₁ S₂ T : Scheme.{u}}

/-- A morphism that restricts to an isomorphism over an open `V` is injective on the inverse
image of `V`. -/
public lemma injOn_of_isIso_morphismRestrict (b : S' ⟶ S) (V : S.Opens) [IsIso (b ∣_ V)] :
    Set.InjOn b.base ((b ⁻¹ᵁ V : S'.Opens) : Set S') := by
  have hinj : Function.Injective ((b ⁻¹ᵁ V).ι ≫ b).base := by
    rw [← morphismRestrict_ι, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact V.ι.isOpenEmbedding.injective.comp (b ∣_ V).isOpenEmbedding.injective
  intro x hx y hy h
  exact congrArg Subtype.val (@hinj ⟨x, hx⟩ ⟨y, hy⟩ h)

/-- Preimage-of-a-set form of `Stacks.StrictTransform.injOn_of_isIso_morphismRestrict`. -/
public lemma injOn_preimage_of_isIso_morphismRestrict (b : S' ⟶ S) (V : S.Opens)
    [IsIso (b ∣_ V)] : Set.InjOn b.base (b.base ⁻¹' (V : Set S)) :=
  injOn_of_isIso_morphismRestrict b V

/-- If the support of `K` is the support of `I` together with the image of the support of `J`,
and `b` is injective away from the support of `I`, then the inverse image of the support of `K`
is the inverse image of the support of `I` together with the support of `J`. -/
public lemma preimage_supportSet_union_of_injOn (b : S' ⟶ S) (I K : S.IdealSheafData)
    (J : S'.IdealSheafData) (hb : Set.InjOn b.base (b.base ⁻¹' I.supportSetᶜ))
    (hK : K.supportSet = I.supportSet ∪ b.base '' J.supportSet) :
    b.base ⁻¹' K.supportSet = b.base ⁻¹' I.supportSet ∪ J.supportSet := by
  rw [hK]
  ext z
  simp only [Set.mem_preimage, Set.mem_union]
  refine ⟨?_, ?_⟩
  · rintro (hz | ⟨y, hy, hyz⟩)
    · exact Or.inl hz
    · by_cases hzI : b.base z ∈ I.supportSet
      · exact Or.inl hzI
      · have hyI : b.base y ∉ I.supportSet := fun hy' ↦ hzI (hyz ▸ hy')
        exact Or.inr (hb hyI hzI hyz ▸ hy)
  · rintro (hz | hz)
    · exact Or.inl hz
    · exact Or.inr ⟨z, hz, rfl⟩

/-- The support of the exceptional ideal of a blowup is the inverse image of the support of the
centre. -/
public lemma supportSet_exceptionalIdeal (I : S.IdealSheafData) :
    (AlgebraicGeometry.exceptionalIdeal I).supportSet =
      (AlgebraicGeometry.blowUpToBase I).base ⁻¹' I.supportSet :=
  congrArg
    (fun C : Closeds (AlgebraicGeometry.blowUp I) ↦ (C : Set (AlgebraicGeometry.blowUp I)))
    (Scheme.IdealSheafData.support_comap I (AlgebraicGeometry.blowUpToBase I))

/-- **The support identity of [Stacks, Tag 080I] on the first blowup.** If the support of `K` is
the support of `I` together with the image of the support of `J` under the blowup of `I`, then
the inverse image of the support of `K` is the support of the exceptional ideal together with the
support of `J`.

The hypothesis `IsIso (blowUpToBase I ∣_ I.support.compl)` is [Stacks, Tag 02OS]; see the
implementation notes of this file. -/
public lemma preimage_supportSet_blowUp (I K : S.IdealSheafData)
    (J : (AlgebraicGeometry.blowUp I).IdealSheafData)
    [IsIso (AlgebraicGeometry.blowUpToBase I ∣_ I.support.compl)]
    (hK : K.supportSet = I.supportSet ∪
      (AlgebraicGeometry.blowUpToBase I).base '' J.supportSet) :
    (AlgebraicGeometry.blowUpToBase I).base ⁻¹' K.supportSet =
      (AlgebraicGeometry.exceptionalIdeal I).supportSet ∪ J.supportSet := by
  rw [supportSet_exceptionalIdeal]
  exact preimage_supportSet_union_of_injOn _ I K J
    (injOn_preimage_of_isIso_morphismRestrict _ I.support.compl) hK

/-- **Over an open where the second morphism is an isomorphism, the projection of the base change
to `X` is an open immersion.** This is what lets a vanishing statement about a module on `X` be
read off the base change away from the exceptional locus. -/
public lemma isOpenImmersion_preimage_ι_comp_fst (f : X ⟶ S) (b : S' ⟶ S) (V : S.Opens)
    [IsIso (b ∣_ V)] :
    IsOpenImmersion ((pullback.snd f b ⁻¹ᵁ (b ⁻¹ᵁ V)).ι ≫ pullback.fst f b) := by
  have h1 : f ≫ 𝟙 S = 𝟙 X ≫ f := by simp
  have h2 : ((b ⁻¹ᵁ V).ι ≫ b) ≫ 𝟙 S = (b ∣_ V) ≫ V.ι := by
    simp [morphismRestrict_ι b V]
  have hcomp : (pullbackLeftPullbackSndIso f b (b ⁻¹ᵁ V).ι).hom ≫
      pullback.map f ((b ⁻¹ᵁ V).ι ≫ b) f V.ι (𝟙 X) (b ∣_ V) (𝟙 S) h1 h2 ≫
        pullback.fst f V.ι =
      pullback.fst (pullback.snd f b) (b ⁻¹ᵁ V).ι ≫ pullback.fst f b := by
    rw [pullback.map, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  have hproj : (pullbackRestrictIsoRestrict (pullback.snd f b) (b ⁻¹ᵁ V)).inv ≫
      ((pullbackLeftPullbackSndIso f b (b ⁻¹ᵁ V).ι).hom ≫
        pullback.map f ((b ⁻¹ᵁ V).ι ≫ b) f V.ι (𝟙 X) (b ∣_ V) (𝟙 S) h1 h2 ≫
          pullback.fst f V.ι) =
      (pullback.snd f b ⁻¹ᵁ (b ⁻¹ᵁ V)).ι ≫ pullback.fst f b := by
    rw [hcomp, ← Category.assoc, pullbackRestrictIsoRestrict_inv_fst]
  rw [← hproj]
  have : IsIso (pullback.map f ((b ⁻¹ᵁ V).ι ≫ b) f V.ι (𝟙 X) (b ∣_ V) (𝟙 S) h1 h2) :=
    inferInstance
  infer_instance

/-- The open complement of the exceptional preimage of a blowup is the inverse image of the open
complement of the centre. -/
public lemma exceptionalComplement_blowUp (f : X ⟶ S) (I : S.IdealSheafData) :
    exceptionalComplement f (AlgebraicGeometry.blowUpToBase I)
        (AlgebraicGeometry.exceptionalIdeal I) =
      pullback.snd f (AlgebraicGeometry.blowUpToBase I) ⁻¹ᵁ
        (AlgebraicGeometry.blowUpToBase I ⁻¹ᵁ I.support.compl) := by
  refine Opens.ext ?_
  change (pullback.snd f (AlgebraicGeometry.blowUpToBase I)).base ⁻¹'
      ((AlgebraicGeometry.exceptionalIdeal I).supportSet)ᶜ = _
  rw [supportSet_exceptionalIdeal]
  rfl

/-- **Away from the exceptional divisor of a blowup, the projection of the base change to `X` is
an open immersion.** The hypothesis `IsIso (blowUpToBase I ∣_ I.support.compl)` is
[Stacks, Tag 02OS]; see the implementation notes of this file. -/
public lemma isOpenImmersion_exceptionalComplement_ι_comp_fst (f : X ⟶ S)
    (I : S.IdealSheafData) [IsIso (AlgebraicGeometry.blowUpToBase I ∣_ I.support.compl)] :
    IsOpenImmersion ((exceptionalComplement f (AlgebraicGeometry.blowUpToBase I)
        (AlgebraicGeometry.exceptionalIdeal I)).ι ≫
      pullback.fst f (AlgebraicGeometry.blowUpToBase I)) := by
  rw [exceptionalComplement_blowUp]
  exact isOpenImmersion_preimage_ι_comp_fst f _ I.support.compl

/-- The preimage of a set under a composite of morphisms is the iterated preimage. -/
private theorem preimage_comp {A B C : Scheme.{u}} (p : A ⟶ B) (q : B ⟶ C) (Z : Set C) :
    (p ≫ q).base ⁻¹' Z = p.base ⁻¹' (q.base ⁻¹' Z) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]

/-- **The transport of the exceptional preimage across an iterated base change.** Base changing
`f` along `b` and then along `c` is base changing it along `d`
(`Stacks.IteratedBaseChange.iso`); under that identification the inverse image of the exceptional
preimage for `E''` is the union of the inverse image of the exceptional preimage for `E` and the
exceptional preimage for `E'`, as soon as the corresponding identity of supports holds on `S₂`.

This is the geometric step of [Stacks, Tag 080I]: it is what makes the open over which the
iterated strict transform is unchanged the intersection of the two such opens. -/
public lemma iso_preimage_exceptionalPreimage (f : X ⟶ S) (b : S₁ ⟶ S) (c : S₂ ⟶ S₁)
    (d : T ⟶ S) (e : Over.mk (c ≫ b) ≅ Over.mk d) (E : S₁.IdealSheafData)
    (E' : S₂.IdealSheafData) (E'' : T.IdealSheafData)
    (hE : e.hom.left.base ⁻¹' E''.supportSet = c.base ⁻¹' E.supportSet ∪ E'.supportSet) :
    (Stacks.IteratedBaseChange.iso f b c d e).hom.base ⁻¹' exceptionalPreimage f d E'' =
      (pullback.fst (pullback.snd f b) c).base ⁻¹' exceptionalPreimage f b E ∪
        exceptionalPreimage (pullback.snd f b) c E' := by
  rw [show exceptionalPreimage f d E'' = (pullback.snd f d).base ⁻¹' E''.supportSet from rfl,
    ← preimage_comp, Stacks.IteratedBaseChange.iso_hom_snd, preimage_comp, hE, Set.preimage_union,
    show (pullback.snd (pullback.snd f b) c).base ⁻¹' (c.base ⁻¹' E.supportSet) =
      (pullback.snd (pullback.snd f b) c ≫ c).base ⁻¹' E.supportSet from (preimage_comp _ _ _).symm,
    ← pullback.condition (f := pullback.snd f b) (g := c), preimage_comp]
  rfl

/-- **The transport of [Stacks, Tag 080I] in the shape that tag states it.** The centres are a
blowup `b` of `S` in `I`, a blowup `c` of the blowup in `J`, and a third centre `K` on `S` whose
support is `Supp I ∪ b(Supp J)`; the exceptional ideals are the exceptional ideals of the three
blowups.

The hypothesis `IsIso (blowUpToBase I ∣_ I.support.compl)` is [Stacks, Tag 02OS]; see the
implementation notes of this file. -/
public lemma iso_preimage_exceptionalPreimage_blowUp (f : X ⟶ S) (I K : S.IdealSheafData)
    (J : (AlgebraicGeometry.blowUp I).IdealSheafData)
    [IsIso (AlgebraicGeometry.blowUpToBase I ∣_ I.support.compl)]
    (hK : K.supportSet = I.supportSet ∪
      (AlgebraicGeometry.blowUpToBase I).base '' J.supportSet)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase J ≫ AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase K)) :
    (Stacks.IteratedBaseChange.iso f (AlgebraicGeometry.blowUpToBase I)
          (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.blowUpToBase K) e).hom.base ⁻¹'
        exceptionalPreimage f (AlgebraicGeometry.blowUpToBase K)
          (AlgebraicGeometry.exceptionalIdeal K) =
      (pullback.fst (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
            (AlgebraicGeometry.blowUpToBase J)).base ⁻¹'
          exceptionalPreimage f (AlgebraicGeometry.blowUpToBase I)
            (AlgebraicGeometry.exceptionalIdeal I) ∪
        exceptionalPreimage (pullback.snd f (AlgebraicGeometry.blowUpToBase I))
          (AlgebraicGeometry.blowUpToBase J) (AlgebraicGeometry.exceptionalIdeal J) := by
  refine iso_preimage_exceptionalPreimage f _ _ _ e _ _ _ ?_
  rw [supportSet_exceptionalIdeal, supportSet_exceptionalIdeal, supportSet_exceptionalIdeal,
    ← preimage_comp, show e.hom.left ≫ AlgebraicGeometry.blowUpToBase K =
      AlgebraicGeometry.blowUpToBase J ≫ AlgebraicGeometry.blowUpToBase I from
      by simpa using Over.w e.hom,
    preimage_comp, preimage_supportSet_blowUp I K J hK, supportSet_exceptionalIdeal,
    Set.preimage_union]

end Stacks.StrictTransform

end
