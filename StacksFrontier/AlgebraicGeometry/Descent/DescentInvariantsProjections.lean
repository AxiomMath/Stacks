module

public import StacksFrontier.AlgebraicGeometry.Descent.DescendedRingOpenSubset
import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BaseChangeTower

/-!
# The two projections of `Spec C ×_{Spec C₀} Spec C` for the invariants of a descent datum

Step 4 of the proof of [Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK) produces, from
the two pushout squares of [Stacks, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ) and an
isomorphism `Φ` of their apexes over `A ⊗_R A`, an `R`-subalgebra
`C₀ = ModuleCat.descentInvariants` of `C` with `C = A ⊗_R C₀`. Step 5 then descends an open
subscheme of `Spec C` to one of `Spec C₀`, and asks in return that the two preimages of that open
in `Spec C ×_{Spec C₀} Spec C` agree — the hypothesis `hcompat` of
`AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPushout`.

This file identifies that fibre product. The ring `Q` of the second pushout square — which is
`A ⊗_R C`, and in the proof of Tag 0APK is the ring of functions on `X ×_S E` — *is*
`C ⊗_{C₀} C`, with the two coprojections given by the `C`-leg `iC` of the first square read
through `Φ` and by the `C`-leg `kC` of the second. Consequently the condition on the two preimages
is a condition on the two comparison legs of Tag 0APJ, which is the form in which the commutative
diagram of the source delivers it.

## Main results

* `ModuleCat.descentInvariants_comp_transition` : on the subalgebra of invariants the two
  comparison legs agree. This is the invariance equation `ψ(c₀ ⊗ 1) = 1 ⊗ c₀` read in `Q`.
* `ModuleCat.isPushout_descentInvariants_transition` : `Q` is the pushout of `C₀ → C` along
  itself, with coprojections `iC ≫ Φ.hom` and `kC`.
* `ModuleCat.isPullback_specMap_descentInvariants` : the same square read through `Spec`, so that
  `Spec Q` is `Spec C ×_{Spec C₀} Spec C` with projections `Spec.map (iC ≫ Φ.hom)` and
  `Spec.map kC`.
* `ModuleCat.preimage_pullback_eq_of_preimage_specMap_eq` : **the compatibility hypothesis of step
  5, reduced to the two comparison legs.** An open of `Spec C` whose preimages under
  `Spec.map (iC ≫ Φ.hom)` and `Spec.map kC` agree has equal preimages under the two projections
  of `Spec C ×_{Spec C₀} Spec C`.

## Implementation notes

*Why the base-change hypothesis is explicit.* The identification of `Q` with `C ⊗_{C₀} C` is the
pushout of `C₀ → C` along itself obtained by cancelling the square `C = A ⊗_R C₀` out of the
square of Tag 0APJ, by `CategoryTheory.IsPushout.paste_vert_iff`. The cancellation needs
`Algebra.IsPushout R A C₀ C`, which is the conclusion of step 4
(`ModuleCat.isPushout_descentInvariants_of_isPushout`) and therefore carries faithful flatness of
`R → A` and the coassociativity hypothesis `hkey` with it. It is taken here as an explicit
hypothesis so that nothing in this file depends on `hkey`; a consumer supplies it from
`ModuleCat.isPushout_descentInvariants_of_isPushout`.

*Why the subalgebra is named rather than existentially quantified.*
`ModuleCat.exists_subalgebra_isPushout_and_existsUnique_opens_preimage_eq` hides `C₀` behind an
existential, so a consumer that destructs it can no longer see that `C₀` is
`ModuleCat.descentInvariants` and cannot apply the results below. The route that works is to use
`ModuleCat.isPushout_descentInvariants_of_isPushout` and
`AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPushout` directly at
`C₀ := ModuleCat.descentInvariants ...`, discharging `hcompat` with
`ModuleCat.preimage_pullback_eq_of_preimage_specMap_eq`.

*What is still owed for step 5.* The hypothesis of
`ModuleCat.preimage_pullback_eq_of_preimage_specMap_eq`, at the open `j(W)` of
`AlgebraicGeometry.subsetΓSpecOpens`, is *not* discharged anywhere. Naturality of `j`
(`AlgebraicGeometry.toΓSpec_base_sectionsRingOnSubsetMap`) gives the commutativity the source
reads off its diagram, but by itself that only yields the inclusion
`j'(W ×_S X) ⊆ (Spec.map _)⁻¹ j(W)` of subsets of `Spec Q`; the source's identification of the
preimage with the image needs that `j'` has image the preimage of the image of `j`, that is, that
the family of quasi-compact opens of `Spec C` cutting out the image of `j` base changes to the one
cutting out the image of `j'`. That comparison is not available.

No tag is placed: this is a step in the proof of Tag 0APK, and Tag 0APK is stated for arbitrary
fpqc covering families.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APJ](https://stacks.math.columbia.edu/tag/0APJ)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

namespace ModuleCat

/-- The underlying map of an isomorphism of schemes is surjective. -/
private alias surjective_base_of_iso := AlgebraicGeometry.surjective_hom_base_of_iso

variable {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra A C]
    [Algebra R C] [IsScalarTower R A C] {P Q : CommRingCat.{u}}
    {iC : CommRingCat.of C ⟶ P} {iA : CommRingCat.of A ⟶ P}
    {kA : CommRingCat.of A ⟶ Q} {kC : CommRingCat.of C ⟶ Q}

variable (hP : IsPushout (CommRingCat.ofHom (algebraMap R C))
      (CommRingCat.ofHom (algebraMap R A)) iC iA)
    (hQ : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R C)) kA kC)
    (Φ : P ≅ Q)
    (h1 : CommRingCat.ofHom (algebraMap A C) ≫ iC ≫ Φ.hom = kA)
    (h2 : iA ≫ Φ.hom = CommRingCat.ofHom (algebraMap A C) ≫ kC)

include h1 h2 in
/-- **On the subalgebra of invariants the two comparison legs of Stacks 0APJ agree.** For
`c₀ ∈ C₀` the invariance equation `ψ(c₀ ⊗ 1) = 1 ⊗ c₀` says exactly that `Φ(iC c₀) = kC c₀`. -/
lemma descentInvariants_comp_transition :
    CommRingCat.ofHom
          (algebraMap (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C) ≫
        iC ≫ Φ.hom =
      CommRingCat.ofHom
          (algebraMap (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C) ≫
        kC := by
  ext c
  have hc := c.2
  rw [mem_descentInvariants_iff] at hc
  have hu := algebraUnitTransition_algebraTransitionOfPushout hP hQ Φ h1 h2 (c : C)
  rw [algebraUnitTransition_apply] at hu
  rw [hc] at hu
  have hk := congrArg (CommRingCat.tensorProductIsoOfIsPushout hQ).hom.hom hu
  rw [CommRingCat.tensorProductIsoOfIsPushout_hom_one_tmul] at hk
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom]
  have hid : (CommRingCat.tensorProductIsoOfIsPushout hQ).hom.hom
        ((CommRingCat.tensorProductIsoOfIsPushout hQ).inv.hom (Φ.hom.hom (iC.hom (c : C)))) =
      Φ.hom.hom (iC.hom (c : C)) :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (CommRingCat.tensorProductIsoOfIsPushout hQ).inv_hom_id) _
  exact (hk.trans hid).symm

include h1 h2 in
/-- **The apex of the second square of Stacks 0APJ is `C ⊗_{C₀} C`.** If `C` is the base change of
`A` along `R → C₀`, then `Q` is the pushout of `C₀ → C` along itself, with coprojections the
`C`-leg of the first square read through `Φ` and the `C`-leg of the second square. -/
lemma isPushout_descentInvariants_transition
    (hpo : Algebra.IsPushout R A
      (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C) :
    IsPushout
      (CommRingCat.ofHom
        (algebraMap (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C))
      (CommRingCat.ofHom
        (algebraMap (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C))
      (iC ≫ Φ.hom) kC := by
  have sq1 := CommRingCat.isPushout_iff_isPushout.mpr hpo
  refine (IsPushout.paste_vert_iff sq1
    (descentInvariants_comp_transition hP hQ Φ h1 h2)).mp ?_
  rw [show CommRingCat.ofHom
        (algebraMap R (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2))) ≫
      CommRingCat.ofHom
        (algebraMap (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C) =
      CommRingCat.ofHom (algebraMap R C) from by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq R _ C).symm]
  rw [show CommRingCat.ofHom (algebraMap A C) ≫ iC ≫ Φ.hom = kA from h1]
  exact hQ

include h1 h2 in
/-- **`Spec Q` is `Spec C ×_{Spec C₀} Spec C`**, with the two projections given by the two
comparison legs of Stacks 0APJ. -/
theorem isPullback_specMap_descentInvariants
    (hpo : Algebra.IsPushout R A
      (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C) :
    IsPullback (Spec.map (iC ≫ Φ.hom)) (Spec.map kC)
      (Spec.map (CommRingCat.ofHom
        (algebraMap (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_descentInvariants_transition hP hQ Φ h1 h2 hpo)

include h1 h2 in
/-- **The compatibility hypothesis of step 5 of the proof of Stacks 0APK, reduced to the two
comparison legs of Stacks 0APJ.** A subset of `Spec C` whose preimages under the two legs
`Spec.map (iC ≫ Φ.hom)` and `Spec.map kC` agree has equal preimages under the two projections of
`Spec C ×_{Spec C₀} Spec C`, which is the hypothesis `hcompat` of
`AlgebraicGeometry.existsUnique_opens_preimage_eq_of_isPushout`. -/
theorem preimage_pullback_eq_of_preimage_specMap_eq
    (hpo : Algebra.IsPushout R A
      (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C)
    (W' : Set (Spec (CommRingCat.of C)))
    (hW : (Spec.map (iC ≫ Φ.hom)).base ⁻¹' W' = (Spec.map kC).base ⁻¹' W') :
    (pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap
            (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C)))
          (Spec.map (CommRingCat.ofHom (algebraMap
            (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C)))).base ⁻¹'
        W' =
      (pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap
            (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C)))
          (Spec.map (CommRingCat.ofHom (algebraMap
            (descentInvariants R A C (algebraTransitionOfPushout hP hQ Φ h1 h2)) C)))).base ⁻¹'
        W' := by
  have hpb := isPullback_specMap_descentInvariants hP hQ Φ h1 h2 hpo
  have hsurj := surjective_base_of_iso hpb.isoPullback
  refine hsurj.preimage_injective ?_
  refine Eq.trans
    (congrArg (fun m : _ ⟶ Spec (CommRingCat.of C) => (m.base ⁻¹' W' : Set _))
      hpb.isoPullback_hom_fst) (hW.trans ?_)
  exact (congrArg (fun m : _ ⟶ Spec (CommRingCat.of C) => (m.base ⁻¹' W' : Set _))
    hpb.isoPullback_hom_snd).symm

end ModuleCat

end

end
