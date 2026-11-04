module

public import StacksFrontier.AlgebraicGeometry.StrictTransform.Composition
public import StacksFrontier.AlgebraicGeometry.StrictTransform.DifferentCentres

/-!
# Iterated strict transforms of a module: [Stacks, Tag 080I] part (1), unconditionally

`Stacks.StrictTransform.exists_baseChange_iso_sheaf_iso_comp_blowUp`
(`StacksFrontier/AlgebraicGeometry/StrictTransform/Composition.lean`) is [Stacks, Tag 080I]
part (1) with one hypothesis `hQJ`: that the strict transform along the second blowup of the
strict transform along the first has no nonzero local sections supported in the inverse image of
`Supp J ∪ Supp (exceptionalIdeal I)`. This file proves `hQJ` and therefore the tag.

The Stacks Project obtains `hQJ` from [Stacks, Tag 080H] part (2), applied on `X ×_S Bl_I S`
over `Bl_I S` with centre `J` and effective Cartier divisor `b^{-1}Z = exceptionalIdeal I`: the
strict transform in `J` agrees with the strict transform in `J · b^{-1}Z`, whose defining
property is exactly the required vanishing. That route needs the isomorphism of blowups of tag
080H part (1), which is not in the repository (a chain of five absent tags; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/StrictTransform/DifferentCentres.lean`).

The route taken here reaches the same conclusion with no isomorphism of blowups at all, from the
*same* geometric input — that a blowup is an isomorphism away from its centre, [Stacks, Tag 02OS]
part (1), the instance `AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`. See the
implementation notes.

## Main results

* `Stacks.StrictTransform.supportedSections_sheaf_blowUp_union_eq_zero`: the strict transform
  along a blowup of a module with no nonzero local sections supported over `Supp D` has no
  nonzero local sections supported over `Supp J ∪ Supp D`. This is `hQJ` in general form, and it
  is the consequence of [Stacks, Tag 080H] that the proof of tag 080I uses.
* `Stacks.StrictTransform.strictTransformSheaf_comp_blowUp`: **[Stacks, Tag 080I] part (1)**,
  unconditionally.

## Implementation notes

`Stacks.StrictTransform.supportedSections_sheaf_blowUp_union_eq_zero` is proved by
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq`, which reduces the union
`Z ∪ W` of the exceptional preimage `Z` of the blowup and the inverse image `W` of `Supp D` to
`Z` alone, provided the strict transform has no nonzero sections supported in `W` over opens
disjoint from `Z`. Over such an open the quotient map onto the strict transform is an
isomorphism (`Stacks.StrictTransform.isIso_restrictFunctor_map_π` transported by
`AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_le`) and the projection `pr_X` of
the base change is an open immersion
(`Stacks.StrictTransform.isOpenImmersion_exceptionalComplement_ι_comp_fst`, which is where tag
02OS part (1) enters), so the sections in question are sections of a restriction of the module
itself and the hypothesis on it applies — this last step is
`AlgebraicGeometry.Scheme.Modules.supportedSections_restrict_pullback_eq_zero` fed into
`AlgebraicGeometry.Scheme.Modules.supportedSections_eq_zero_of_restrict_open`. With `Z ∪ W`
reduced to `Z` the conclusion is the defining property
`Stacks.StrictTransform.supportedSections_sheaf_eq_zero`.

So the two tags use one geometric input and differ in what they then do with it: tag 080H
part (2) compares two quotients of `pr_X^* F` with the same kernel, while this file enlarges the
support condition on a single quotient. Neither is deduced from the other here, and tag 080H
part (1) is needed for neither.

The statement is given for an arbitrary module `F`, with no quasi-coherence hypothesis, which is
more general than the tag: the strict transform is a cokernel and needs none. Where `F` is
quasi-coherent so is every strict transform occurring here, by the instances
`Stacks.StrictTransform.isQuasicoherent_sheaf` and
`Stacks.StrictTransform.quasiCompact_ι_compl_support_exceptionalIdeal`, so the tag's own
`[F.IsQuasicoherent]` and its consequence for the iterated transform are not assumptions but
theorems.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080H](https://stacks.math.columbia.edu/tag/080H)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.StrictTransform

open AlgebraicGeometry.Scheme.Modules hiding pullback

variable {X S : Scheme.{u}}

/-- **The strict transform along the blowup in `J` of a module with no nonzero local sections
supported over `Supp D` has no nonzero local sections supported over `Supp J ∪ Supp D`.**

Its defining property gives this for `Supp J` alone. Away from the exceptional divisor the
quotient map onto the strict transform is an isomorphism and the projection `pr_X` is an open
immersion ([Stacks, Tag 02OS] part (1)), so there the sections concerned are sections of a
restriction of `F` and `hF` applies; the two facts combine by
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq`.

This is the consequence of [Stacks, Tag 080H] that the proof of [Stacks, Tag 080I] uses, proved
without tag 080H part (1); see the implementation notes of this file. -/
public theorem supportedSections_sheaf_blowUp_union_eq_zero (f : X ⟶ S)
    (J D : S.IdealSheafData) (F : X.Modules)
    (hF : ∀ (V : X.Opens) (t : Γ(F, V)),
      t ∈ (supportedSectionsSubmodule (f.base ⁻¹' D.supportSet) F).toSubmodule.obj (op V) →
        t = 0)
    (U : (baseChange f (AlgebraicGeometry.blowUpToBase J)).Opens)
    (s : Γ(sheaf f (AlgebraicGeometry.blowUpToBase J)
      (AlgebraicGeometry.exceptionalIdeal J) F, U))
    (hs : s ∈ (supportedSectionsSubmodule
        ((pullback.snd f (AlgebraicGeometry.blowUpToBase J) ≫
          AlgebraicGeometry.blowUpToBase J).base ⁻¹' (J.supportSet ∪ D.supportSet))
        (sheaf f (AlgebraicGeometry.blowUpToBase J)
          (AlgebraicGeometry.exceptionalIdeal J) F)).toSubmodule.obj (op U)) : s = 0 := by
  set Z := exceptionalPreimage f (AlgebraicGeometry.blowUpToBase J)
    (AlgebraicGeometry.exceptionalIdeal J) with hZ
  set W := (pullback.fst f (AlgebraicGeometry.blowUpToBase J)).base ⁻¹'
    (f.base ⁻¹' D.supportSet) with hW
  have hZeq : Z = (pullback.snd f (AlgebraicGeometry.blowUpToBase J) ≫
      AlgebraicGeometry.blowUpToBase J).base ⁻¹' J.supportSet := by
    rw [hZ]
    change (pullback.snd f (AlgebraicGeometry.blowUpToBase J)).base ⁻¹'
      ((AlgebraicGeometry.exceptionalIdeal J).supportSet) = _
    rw [supportSet_exceptionalIdeal J]
    rfl
  have hWeq : W = (pullback.snd f (AlgebraicGeometry.blowUpToBase J) ≫
      AlgebraicGeometry.blowUpToBase J).base ⁻¹' D.supportSet := by
    rw [hW, ← pullback.condition (f := f) (g := AlgebraicGeometry.blowUpToBase J)]
    rfl
  have hT : (pullback.snd f (AlgebraicGeometry.blowUpToBase J) ≫
      AlgebraicGeometry.blowUpToBase J).base ⁻¹' (J.supportSet ∪ D.supportSet) = Z ∪ W := by
    rw [Set.preimage_union, hZeq, hWeq]
  have hprov : ∀ (V : (baseChange f (AlgebraicGeometry.blowUpToBase J)).Opens),
      (V : Set (baseChange f (AlgebraicGeometry.blowUpToBase J))) ∩ Z = ∅ →
      ∀ t : Γ(sheaf f (AlgebraicGeometry.blowUpToBase J)
        (AlgebraicGeometry.exceptionalIdeal J) F, V),
      t ∈ (supportedSectionsSubmodule W (sheaf f (AlgebraicGeometry.blowUpToBase J)
        (AlgebraicGeometry.exceptionalIdeal J) F)).toSubmodule.obj (op V) → t = 0 := by
    intro V hV t ht
    have hVle : V ≤ exceptionalComplement f (AlgebraicGeometry.blowUpToBase J)
        (AlgebraicGeometry.exceptionalIdeal J) := fun x hx hxZ =>
      (Set.disjoint_left.mp (Set.disjoint_iff_inter_eq_empty.mpr hV)) hx hxZ
    have hVoi : IsOpenImmersion
        ((exceptionalComplement f (AlgebraicGeometry.blowUpToBase J)
          (AlgebraicGeometry.exceptionalIdeal J)).ι ≫
            pullback.fst f (AlgebraicGeometry.blowUpToBase J)) :=
      isOpenImmersion_exceptionalComplement_ι_comp_fst f J
    have hoi : IsOpenImmersion
        (V.ι ≫ pullback.fst f (AlgebraicGeometry.blowUpToBase J)) := by
      rw [← Scheme.homOfLE_ι _ hVle, Category.assoc]
      exact IsOpenImmersion.comp _ _
    have hiso : IsIso ((restrictFunctor
        (exceptionalComplement f (AlgebraicGeometry.blowUpToBase J)
          (AlgebraicGeometry.exceptionalIdeal J)).ι).map
            (π f (AlgebraicGeometry.blowUpToBase J)
              (AlgebraicGeometry.exceptionalIdeal J) F)) :=
      isIso_restrictFunctor_map_π f (AlgebraicGeometry.blowUpToBase J)
        (AlgebraicGeometry.exceptionalIdeal J) F
    have hiso' : IsIso ((restrictFunctor V.ι).map
        (π f (AlgebraicGeometry.blowUpToBase J)
          (AlgebraicGeometry.exceptionalIdeal J) F)) :=
      isIso_restrictFunctor_map_of_le hVle _
    refine supportedSections_eq_zero_of_restrict_open _ W V ?_ t ht
    refine supportedSections_eq_zero_of_mono _
      (asIso ((restrictFunctor V.ι).map
        (π f (AlgebraicGeometry.blowUpToBase J)
          (AlgebraicGeometry.exceptionalIdeal J) F))).inv inferInstance ?_
    exact supportedSections_restrict_pullback_eq_zero
      (pullback.fst f (AlgebraicGeometry.blowUpToBase J)) (f.base ⁻¹' D.supportSet) F hF V
  have hZclosed : IsClosed Z :=
    (AlgebraicGeometry.exceptionalIdeal J).support.isClosed.preimage (by fun_prop)
  have hN : supportedSectionsSubmodule (Z ∪ W) (sheaf f (AlgebraicGeometry.blowUpToBase J)
      (AlgebraicGeometry.exceptionalIdeal J) F) =
      supportedSectionsSubmodule Z (sheaf f (AlgebraicGeometry.blowUpToBase J)
        (AlgebraicGeometry.exceptionalIdeal J) F) :=
    supportedSectionsSubmodule_union_eq Z W hZclosed _ hprov
  rw [hT, hN] at hs
  exact supportedSections_sheaf_eq_zero f (AlgebraicGeometry.blowUpToBase J)
    (AlgebraicGeometry.exceptionalIdeal J) F U s hs

/-- **[Stacks, Tag 080I] part (1).** For `b` the blowup of `S` in `I`, `c` the blowup of the
blowup in `J`, and `d` the blowup of `S` in a third centre `K` whose support is
`Supp I ∪ b(Supp J)`, the iterated strict transform of `F` agrees with the strict transform in
the composite centre, compatibly with both projections and with the quotient maps.

This is `Stacks.StrictTransform.exists_baseChange_iso_sheaf_iso_comp_blowUp` with its one
hypothesis `hQJ` discharged by
`Stacks.StrictTransform.supportedSections_sheaf_blowUp_union_eq_zero`, applied on the first base
change over the first blowup with centre `J` and divisor `AlgebraicGeometry.exceptionalIdeal I`,
whose own hypothesis is the defining property
`Stacks.StrictTransform.supportedSections_sheaf_eq_zero` of the first strict transform.
Unconditional. -/
@[stacks 080I "part (1): strict transform of a module"]
public theorem strictTransformSheaf_comp_blowUp (f : X ⟶ S) (I K : S.IdealSheafData)
    (J : (AlgebraicGeometry.blowUp I).IdealSheafData)
    (hK : K.supportSet = I.supportSet ∪
      (AlgebraicGeometry.blowUpToBase I).base '' J.supportSet)
    (e : Over.mk (AlgebraicGeometry.blowUpToBase J ≫ AlgebraicGeometry.blowUpToBase I) ≅
      Over.mk (AlgebraicGeometry.blowUpToBase K))
    (F : X.Modules) :
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
  exists_baseChange_iso_sheaf_iso_comp_blowUp f I K J hK e F
    (supportedSections_sheaf_blowUp_union_eq_zero
      (pullback.snd f (AlgebraicGeometry.blowUpToBase I)) J
      (AlgebraicGeometry.exceptionalIdeal I)
      (sheaf f (AlgebraicGeometry.blowUpToBase I)
        (AlgebraicGeometry.exceptionalIdeal I) F)
      (supportedSections_sheaf_eq_zero f (AlgebraicGeometry.blowUpToBase I)
        (AlgebraicGeometry.exceptionalIdeal I) F))

end Stacks.StrictTransform

end
