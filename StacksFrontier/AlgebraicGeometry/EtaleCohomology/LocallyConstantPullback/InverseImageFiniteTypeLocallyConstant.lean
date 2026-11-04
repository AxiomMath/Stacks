module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleInverseImage

/-!
# Finite-type local constancy is stable under inverse image

`Stacks.ConstantSheaf.IsFiniteLocallyConstant` is carried along inverse image by Tag 093R, proved
as `Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback_of_coverPreserving` for a morphism
of sites and as `AlgebraicGeometry.isFiniteLocallyConstant_smallEtaleSheafPullback` for small
étale base change. This file proves the same for the module-coefficient condition of Tag 03RW (3),
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`, which asks the constant value to be finitely
generated over the coefficient ring rather than finite as a set.

## Main results

* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_cover` — one trivializing covering of a
  final object suffices for finite-type local constancy.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_sheafPullback` — **Tag 093R for sheaves of
  modules**: the inverse image of a finite-type locally constant sheaf of modules along a
  continuous functor of sites is finite-type locally constant.
* `AlgebraicGeometry.isFiniteTypeLocallyConstant_smallEtaleSheafPullback_of_overPost` — the same
  for small étale base change, given that the pushforward along the slice of the base change is a
  right adjoint. `AlgebraicGeometry.isFiniteTypeLocallyConstant_smallEtaleSheafPullback` reaches
  the same conclusion and asks nothing of the slice pushforward.

## Implementation notes

**No `@[stacks 093R]` attribute appears in this file.** The source states the tag for an arbitrary
morphism of topoi, whose inverse image need not be induced by a functor between the two sites;
what is proved here is the inverse image induced by a functor of *sites*, and for module
coefficients rather than the sheaves of sets the tag speaks of. The tag's covering set is
therefore not complete here, and an unqualified attribute would report the whole tag as
formalized. `Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafPullback_of_coverPreserving`, the
same statement for a concrete coefficient category, does carry the tag, with a note recording
that it is the inverse image along a morphism of sites that is covered; the statement here could
carry such a note too, and does not only because the module-coefficient condition of Tag 03RW (3)
is not one of the conditions Tag 093R lists.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u' r

namespace Stacks.ConstantSheaf

/-- **A single covering of a final object suffices for finite-type local constancy.**

This is `Stacks.ConstantSheaf.isFiniteLocallyConstant_of_cover` with finiteness of the value
replaced by finite generation. -/
public lemma isFiniteTypeLocallyConstant_of_cover {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type r) [Ring R] [HasPullbacks C]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)]
    {T : C} (hT : IsTerminal T) (F : Sheaf J (ModuleCat.{w} R))
    {I : Type*} {X : I → C} {f : ∀ i, X i ⟶ T}
    (hf : Sieve.ofArrows X f ∈ J T)
    (hc : ∀ i, ∃ E : ModuleCat.{w} R, ModuleCat.isFG R E ∧ Nonempty
      ((constantSheaf (J.over (X i)) (ModuleCat.{w} R)).obj E ≅
        (J.overPullback (ModuleCat.{w} R) (X i)).obj F)) :
    IsFiniteTypeLocallyConstant R J F := by
  intro U
  refine ⟨Σ V : C, {g : V ⟶ U // (Sieve.pullback (hT.from U) (Sieve.ofArrows X f)).arrows g},
    fun p => p.1, fun p => p.2.1,
    sieve_ofArrows_arrows_mem J _ (J.pullback_stable (hT.from U) hf), fun p => ?_⟩
  have h1 : (Sieve.ofArrows X f).arrows (p.2.1 ≫ hT.from U) := p.2.2
  rw [hT.hom_ext (p.2.1 ≫ hT.from U) (hT.from p.1)] at h1
  obtain ⟨i, h, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp h1
  obtain ⟨E, hE, ⟨c⟩⟩ := hc i
  exact ⟨E, hE, ⟨constantIsoOverPullbackOfMap J (ModuleCat.{w} R) h F E c⟩⟩

/-- **Tag 093R for sheaves of modules.** The inverse image of a finite-type locally constant sheaf
of modules along a continuous functor of sites is finite-type locally constant. -/
public lemma isFiniteTypeLocallyConstant_sheafPullback {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (R : Type r) [Ring R]
    [HasFiniteLimits C] [HasFiniteLimits D]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} R)]
    [∀ V : D, HasWeakSheafify (K.over V) (ModuleCat.{w} R)]
    (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
    [(G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).IsRightAdjoint]
    [∀ X : C, (Over.post (X := X) G).IsContinuous (J.over X) (K.over (G.obj X))]
    [∀ X : C, ((Over.post (X := X) G).sheafPushforwardContinuous (ModuleCat.{w} R)
      (J.over X) (K.over (G.obj X))).IsRightAdjoint]
    (hG : CoverPreserving J K G)
    (F : Sheaf J (ModuleCat.{w} R)) (hF : IsFiniteTypeLocallyConstant R J F) :
    IsFiniteTypeLocallyConstant R K
      ((G.sheafPullback (ModuleCat.{w} R) J K).obj F) := by
  obtain ⟨I, X, f, hf, hc⟩ := hF (⊤_ C)
  refine isFiniteTypeLocallyConstant_of_cover K R
    (IsTerminal.isTerminalObj G (⊤_ C) terminalIsTerminal) _
    (sieve_ofArrows_map_mem J K G hG hf) fun i => ?_
  obtain ⟨E, hE, ⟨c⟩⟩ := hc i
  exact ⟨E, hE, ⟨constantIsoOverPullbackSheafPullback J K (ModuleCat.{w} R) G (X i) F E c⟩⟩

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- **Tag 093R for sheaves of modules on small étale sites.** The inverse image of a finite-type
locally constant sheaf of modules along small étale base change is finite-type locally constant.

This is the hypothesis `hPImmersion` of
`AlgebraicGeometry.isStratifiedSheaf_tfae` for the stratum condition of Tag 03RW (3), and it holds
for an arbitrary morphism, not only for an immersion.

The pushforward along the slice `CategoryTheory.Over.post` of the base change is assumed to be a
right adjoint; `AlgebraicGeometry.isFiniteTypeLocallyConstant_smallEtaleSheafPullback` has the
same conclusion without that assumption. -/
public theorem isFiniteTypeLocallyConstant_smallEtaleSheafPullback_of_overPost
    {S T : B.Scheme} (f : T ⟶ S)
    (R : Type r) [Ring R]
    [∀ U : SmallEtale B S.obj S.property,
      HasWeakSheafify ((SmallEtale.topology B S.obj S.property).over U) (ModuleCat.{w} R)]
    [∀ V : SmallEtale B T.obj T.property,
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} R)]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{w} R)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ X : SmallEtale B S.obj S.property,
      ((Over.post (X := X) (smallEtaleBaseChange B f)).sheafPushforwardContinuous
        (ModuleCat.{w} R)
        ((SmallEtale.topology B S.obj S.property).over X)
        ((SmallEtale.topology B T.obj T.property).over
          ((smallEtaleBaseChange B f).obj X))).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{w} R))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B S.obj S.property) F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B T.obj T.property)
      (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{w} R)
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj F) :=
  Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_sheafPullback _ _ R _
    (smallEtaleBaseChange_coverPreserving B f) F hF

end AlgebraicGeometry

end
