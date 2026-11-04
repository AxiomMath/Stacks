module

public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.SupportedSectionsRestrict
public import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionBlowUp
public import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionScheme

/-!
# Iterated strict transforms of a module on the strict transform itself

[Stacks, Tag 080I] part (1) compares the iterated strict transform of a module *on the ambient
base change* `X ×_S S'`, and part (2) compares the strict transforms of the scheme. The triple
that the reductions of [Stacks, Tag 080Y] carry is neither of these: it is the module obtained by
restricting the strict transform of a module to the strict transform of the scheme, which is the
module of [Stacks, Tag 080D] regarded, via [Stacks, Tag 080E], as living on `X'` itself. This
file assembles the two parts of tag 080I into the comparison for that module.

## Main definitions

* `AlgebraicGeometry.strictTransformBlowUpModule`: the strict transform of a module, as a module
  on the strict transform of the scheme, for `AlgebraicGeometry.blowUp`.

## Main results

* `Stacks.ClosedImmersion.pullbackPushforwardCounitIso`: `i^* i_* G ≅ G` for a closed immersion.
* `AlgebraicGeometry.pushforwardStrictTransformBlowUpModuleIso`: the strict transform of a module
  is the direct image of its restriction to the strict transform of the scheme.
* `AlgebraicGeometry.exists_strictTransformBlowUpModule_iso_comp`: the comparison of iterated
  strict transforms for the module on the strict transform, i.e. [Stacks, Tag 080I] in the shape
  the reductions of [Stacks, Tag 080Y] need.

## Implementation notes

Two adjunction isomorphisms for the closed immersion `i : X' ⟶ X ×_S S'` carry the comparison
between the two readings of the strict transform of a module. The counit `i^* i_* G ≅ G` holds for
every module, because direct image along a closed immersion is fully faithful
([Stacks, Tag 08KS], `Stacks.ClosedImmersion.fullyFaithfulPushforward`) and a fully faithful right
adjoint has invertible counit. The unit `Q ≅ i_* i^* Q` holds at `Q` the strict transform of a
module because tag 080E part (2) (`AlgebraicGeometry.strictTransformSheafBlowUpIso`) already
exhibits `Q` as a direct image along `X' ⟶ X ×_S S'`, so `Q` lies in the essential image of `i_*`
and `CategoryTheory.Adjunction.isIso_unit_app_iff_mem_essImage` applies.

With those two in hand, tag 080G for the closed immersion `i`
(`AlgebraicGeometry.sheafPushforwardIso`) moves the second strict transform between the ambient
base change and the strict transform of `X`, and the two parts of tag 080I finish the comparison.

## References

* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 080G](https://stacks.math.columbia.edu/tag/080G)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

/-- **The counit of `i^* ⊣ i_*` along a closed immersion is an isomorphism**: `i^* i_* G ≅ G` for
every `𝒪_Z`-module `G`. Direct image along a closed immersion is fully faithful
([Stacks, Tag 08KS]) and a fully faithful right adjoint has invertible counit. -/
public def pullbackPushforwardCounitIso (G : Z.Modules) :
    (Scheme.Modules.pullback i).obj ((Scheme.Modules.pushforward i).obj G) ≅ G :=
  haveI := full_pushforward i
  haveI := faithful_pushforward i
  asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)

end Stacks.ClosedImmersion

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **The strict transform of a module, as a module on the strict transform of the scheme**, for
`AlgebraicGeometry.blowUp`.

This is the counterpart of `Stacks.Blowup.strictTransformModule`, which is the same construction
for the other realization `Stacks.Blowup.blowUp` of the blowup; the two are compared by
`Stacks.Blowup.pullbackStrictTransformModuleIso`. -/
public abbrev strictTransformBlowUpModule (f : X ⟶ S) (I : S.IdealSheafData) (F : X.Modules) :
    (Stacks.StrictTransform.scheme f (blowUpToBase I) (exceptionalIdeal I)).Modules :=
  (Scheme.Modules.pullback
      (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι).obj
    (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)

/-- **The strict transform of a module is the direct image of the module it carries on the strict
transform of the scheme.** [Stacks, Tag 080E] part (2) exhibits the strict transform of `F` as a
direct image along the closed immersion `X' ⟶ X ×_S S'`, so the unit of `i^* ⊣ i_*` is an
isomorphism there. -/
public def pushforwardStrictTransformBlowUpModuleIso (f : X ⟶ S) (I : S.IdealSheafData)
    (F : X.Modules) :
    (Scheme.Modules.pushforward
          (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι).obj
        (strictTransformBlowUpModule f I F) ≅
      Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F := by
  haveI := Stacks.ClosedImmersion.full_pushforward
    (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι
  haveI := Stacks.ClosedImmersion.faithful_pushforward
    (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι
  have hess : (Scheme.Modules.pushforward
      (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι).essImage
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) :=
    ⟨(Scheme.Modules.pushforward (strictTransformBlowUpComapIso f I).hom).obj
        (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase (I.comap f))
          (exceptionalIdeal (I.comap f)) F),
      ⟨(Scheme.Modules.pushforwardComp (strictTransformBlowUpComapIso f I).hom
          (Stacks.StrictTransform.ideal f (blowUpToBase I)
            (exceptionalIdeal I)).subschemeι).app _ ≪≫
        (strictTransformSheafBlowUpIso f I F).symm⟩⟩
  haveI : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι).unit.app
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :=
    (Adjunction.isIso_unit_app_iff_mem_essImage _).mpr hess
  exact (asIso ((Scheme.Modules.pullbackPushforwardAdjunction
    (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι).unit.app
    (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F))).symm

/-- The closed immersion of the strict transform of `X` into the base change, abbreviated for the
length of the statements below. -/
private abbrev stIdealι (f : X ⟶ S) (I : S.IdealSheafData) :
    Stacks.StrictTransform.scheme f (blowUpToBase I) (exceptionalIdeal I) ⟶
      Stacks.StrictTransform.baseChange f (blowUpToBase I) :=
  (Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I)).subschemeι

/-- **[Stacks, Tag 080I] for the module on the strict transform.** For `b` the blowup of `S` in
`I`, `c` the blowup of that blowup in `J`, and `d` the blowup of `S` in a third centre `K` whose
support is `Supp I ∪ b(Supp J)`, the strict transform along `c` of the strict transform of
`F/X/S` agrees with the strict transform of `F/X/S` along `d` — as a scheme over the blowup and
as a module on that scheme. -/
public theorem exists_strictTransformBlowUpModule_iso_comp (f : X ⟶ S) (I K : S.IdealSheafData)
    (J : (blowUp I).IdealSheafData)
    (hK : K.supportSet = I.supportSet ∪ (blowUpToBase I).base '' J.supportSet)
    (e : Over.mk (blowUpToBase J ≫ blowUpToBase I) ≅ Over.mk (blowUpToBase K))
    (F : X.Modules) [F.IsQuasicoherent] :
    ∃ k : Stacks.StrictTransform.scheme (strictTransformToBlowUp f I) (blowUpToBase J)
        (exceptionalIdeal J) ≅
      Stacks.StrictTransform.scheme f (blowUpToBase K) (exceptionalIdeal K),
      k.hom ≫ strictTransformToBlowUp f K =
          strictTransformToBlowUp (strictTransformToBlowUp f I) J ≫ e.hom.left ∧
        Nonempty (strictTransformBlowUpModule (strictTransformToBlowUp f I) J
            (strictTransformBlowUpModule f I F) ≅
          (Scheme.Modules.pullback k.hom).obj (strictTransformBlowUpModule f K F)) := by
  obtain ⟨g, hg, hgS, s, _hs⟩ :=
    Stacks.StrictTransform.strictTransformSheaf_comp_blowUp f I K J hK e F
  obtain ⟨k, hkX, hkS⟩ := Stacks.StrictTransform.strictTransform_comp_blowUp f I K J hK e
  have : IsClosedImmersion (baseChangeInducedMap (stIdealι f I)
      (pullback.snd f (blowUpToBase I)) (blowUpToBase J)) :=
    MorphismProperty.of_isPullback (isPullback_baseChangeInducedMap (stIdealι f I)
      (pullback.snd f (blowUpToBase I)) (blowUpToBase J)) inferInstance
  refine ⟨k, ?_, ⟨?_⟩⟩
  · simp only [strictTransformToBlowUp, Category.assoc]
    exact hkS
  · have hidentify : k.hom ≫ stIdealι f K =
        stIdealι (strictTransformToBlowUp f I) J ≫
          baseChangeInducedMap (stIdealι f I) (pullback.snd f (blowUpToBase I))
            (blowUpToBase J) ≫ g.hom := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, hg]
        rw [← Category.assoc (baseChangeInducedMap (stIdealι f I)
          (pullback.snd f (blowUpToBase I)) (blowUpToBase J)), baseChangeInducedMap_fst]
        simp only [Category.assoc]
        exact hkX
      · simp only [Category.assoc, hgS]
        rw [← Category.assoc (baseChangeInducedMap (stIdealι f I)
          (pullback.snd f (blowUpToBase I)) (blowUpToBase J)), baseChangeInducedMap_snd]
        exact hkS
    have hr : (Scheme.Modules.pushforward (baseChangeInducedMap (stIdealι f I)
            (pullback.snd f (blowUpToBase I)) (blowUpToBase J))).obj
          (Stacks.StrictTransform.sheaf (strictTransformToBlowUp f I) (blowUpToBase J)
            (exceptionalIdeal J) (strictTransformBlowUpModule f I F)) ≅
        (Scheme.Modules.pullback g.hom).obj
          (Stacks.StrictTransform.sheaf f (blowUpToBase K) (exceptionalIdeal K) F) :=
      AlgebraicGeometry.sheafPushforwardIso (stIdealι f I) (pullback.snd f (blowUpToBase I))
          (blowUpToBase J) (exceptionalIdeal J) (strictTransformBlowUpModule f I F) ≪≫
        Stacks.SupportedQuotient.supportedSectionsCokernelIso
          (Stacks.StrictTransform.exceptionalPreimage (pullback.snd f (blowUpToBase I))
            (blowUpToBase J) (exceptionalIdeal J))
          ((Scheme.Modules.pullback (pullback.fst (pullback.snd f (blowUpToBase I))
              (blowUpToBase J))).mapIso
            (pushforwardStrictTransformBlowUpModuleIso f I F)) ≪≫ s.symm
    exact (Scheme.Modules.pullback (stIdealι (strictTransformToBlowUp f I) J)).mapIso
        ((Stacks.ClosedImmersion.pullbackPushforwardCounitIso
            (baseChangeInducedMap (stIdealι f I) (pullback.snd f (blowUpToBase I))
              (blowUpToBase J)) _).symm ≪≫
          (Scheme.Modules.pullback (baseChangeInducedMap (stIdealι f I)
            (pullback.snd f (blowUpToBase I)) (blowUpToBase J))).mapIso hr ≪≫
          (Scheme.Modules.pullbackComp (baseChangeInducedMap (stIdealι f I)
            (pullback.snd f (blowUpToBase I)) (blowUpToBase J)) g.hom).app _) ≪≫
      (Scheme.Modules.pullbackComp (stIdealι (strictTransformToBlowUp f I) J)
        (baseChangeInducedMap (stIdealι f I) (pullback.snd f (blowUpToBase I))
          (blowUpToBase J) ≫ g.hom)).app _ ≪≫
      (Scheme.Modules.pullbackCongr hidentify.symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp k.hom (stIdealι f K)).app _).symm

end AlgebraicGeometry

end
