module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ClosedImmersionAscent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.CompletionAnnihilationDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AnnihilatedFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageChow

/-!
# Essential surjectivity on the subschemes `V(𝒦 ᵉ⁺¹)`

Let `A` be Noetherian and complete with respect to `I`, let `f : X ⟶ Spec A` be proper, set
`𝓘 = I · 𝒪_X`, and let `𝒦 ⊆ 𝒪_X` be a quasi-coherent ideal sheaf. If every coherent `𝓘`-adic
system on `X` killed by `𝒦 ᵉ⁺¹` is in the essential image of the completion functor of `X`, then
the completion functor of the closed subscheme `X_e = V(𝒦 ᵉ⁺¹)` is essentially surjective, and
hence an equivalence: hypothesis (1) of [Stacks, Tag 088A] in the situation of [Stacks, Tag 088C].

## Main results

* `Stacks.Coherent.isoOfWhiskerRightPushforwardIso`: an isomorphism of inverse systems of
  `𝒪_X`-modules between two termwise direct images along a closed immersion comes from an
  isomorphism of the systems upstairs.
* `Stacks.Algebraization.essSurj_completionFunctor_comap_subschemeι_of_essImage`: essential
  surjectivity of the completion functor of `V(𝒦 ᵉ⁺¹)`, from the statement that every coherent
  `𝓘`-adic system on `X` killed by `𝒦 ᵉ⁺¹` is in the essential image of the completion functor
  of `X`.
* `Stacks.Algebraization.essSurj_completionFunctor_comap_subschemeι_forall`: the same, for every
  `e` at once.
* `Stacks.Algebraization.isEquivalence_completionFunctor_comap_subschemeι_of_essImage`: the
  completion functor of `V(𝒦 ᵉ⁺¹)` is an equivalence.

## Implementation notes

Both local Noetherianity instances are introduced with `letI` in the statements, as in
`Stacks.Algebraization.fullyFaithful_completionFunctor_comap_subschemeι`: they follow from
properness of `f` and of `i ≫ f`.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization

/-- **An isomorphism between two termwise direct images along a closed immersion comes from an
isomorphism upstairs.** -/
public def isoOfWhiskerRightPushforwardIso {Z X : Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    {A B : ℕᵒᵖ ⥤ Z.Modules}
    (W : A ⋙ Scheme.Modules.pushforward i ≅ B ⋙ Scheme.Modules.pushforward i) : A ≅ B where
  hom := ((bijective_whiskerRight_pushforward i A B).surjective W.hom).choose
  inv := ((bijective_whiskerRight_pushforward i B A).surjective W.inv).choose
  hom_inv_id := by
    refine (bijective_whiskerRight_pushforward i A A).injective ?_
    have h1 := ((bijective_whiskerRight_pushforward i A B).surjective W.hom).choose_spec
    have h2 := ((bijective_whiskerRight_pushforward i B A).surjective W.inv).choose_spec
    change Functor.whiskerRight (_ ≫ _) (Scheme.Modules.pushforward i) =
      Functor.whiskerRight (𝟙 A) (Scheme.Modules.pushforward i)
    rw [Functor.whiskerRight_comp, h1, h2, W.hom_inv_id, Functor.whiskerRight_id']
  inv_hom_id := by
    refine (bijective_whiskerRight_pushforward i B B).injective ?_
    have h1 := ((bijective_whiskerRight_pushforward i A B).surjective W.hom).choose_spec
    have h2 := ((bijective_whiskerRight_pushforward i B A).surjective W.inv).choose_spec
    change Functor.whiskerRight (_ ≫ _) (Scheme.Modules.pushforward i) =
      Functor.whiskerRight (𝟙 B) (Scheme.Modules.pushforward i)
    rw [Functor.whiskerRight_comp, h2, h1, W.inv_hom_id, Functor.whiskerRight_id']

end Stacks.Coherent

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent
open Stacks.AlgebraicGeometry.Tag087TCoherentImage

/-- **Essential surjectivity of the completion functor of `V(𝒦 ᵉ⁺¹)`.** Let `A` be Noetherian
and complete with respect to `I`, let `f : X ⟶ Spec A` be proper and set `𝓘 = I · 𝒪_X`. Assume
that every coherent `𝓘`-adic system on `X` killed by `𝒦 ᵉ⁺¹` lies in the essential image of the
completion functor of `X`. Then the completion functor of the closed subscheme `V(𝒦 ᵉ⁺¹)`, along
the inverse image of `𝓘`, is essentially surjective. -/
public theorem essSurj_completionFunctor_comap_subschemeι_of_essImage
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData) (e : ℕ)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        IsSystemAnnihilatedBy (K ^ (e + 1)) 𝓖.obj →
          (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((K ^ (e + 1)).subschemeι ≫ f)
    (completionFunctor (K ^ (e + 1)).subscheme
      ((baseIdealSheaf A I f).comap (K ^ (e + 1)).subschemeι)).EssSurj := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((K ^ (e + 1)).subschemeι ≫ f)
  obtain ⟨hff⟩ := fullyFaithful_completionFunctor_of_isProper A I f
  refine ⟨fun G => ?_⟩
  have hP : Stacks.Coherent.IsCoherentAdicSystem (baseIdealSheaf A I f)
      (G.obj ⋙ Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι) :=
    isCoherentAdicSystem_pushforward_closedImmersion (K ^ (e + 1)).subschemeι
      (baseIdealSheaf A I f) G.obj G.property
  have hpow : ∀ n : ℕ, idealPowerMultiple K (e + 1)
      ((Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι).obj (G.obj.obj (op n))) = ⊥ :=
    fun n => (annihilatedByKer_subschemeι_pow_iff K (e + 1) _).mp
      (annihilatedByKer_pushforward (K ^ (e + 1)).subschemeι (G.obj.obj (op n)))
  have hann : IsSystemAnnihilatedBy (K ^ (e + 1))
      (G.obj ⋙ Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι) := fun n =>
    le_bot_iff.mp ((idealPowerMultiple_le_of_pow_le
      (by simp) _).trans (hpow n).le)
  obtain ⟨H, ⟨eH⟩⟩ := hInd ⟨_, hP⟩ hann
  have eHsys : ((completionFunctor X (baseIdealSheaf A I f)).obj H).obj ≅
      G.obj ⋙ Scheme.Modules.pushforward (K ^ (e + 1)).subschemeι :=
    (ObjectProperty.ι _).mapIso eH
  have hHann : idealPowerMultiple K (e + 1) H.obj = ⊥ := by
    refine (idealPowerMultiple_pow_one K (e + 1) H.obj).symm.trans
      (idealPowerMultiple_eq_bot_of_completion_eq_bot (baseIdealSheaf A I f) (K ^ (e + 1))
        hff H fun n => ?_)
    exact (idealPowerMultiple_pow_one K (e + 1) _).trans
      (idealPowerMultiple_eq_bot_of_iso K (eHsys.app (op n)) (e + 1) (hpow n))
  have hHcoh : H.obj.IsCoherent := H.property
  obtain ⟨S, hScoh, ⟨eS⟩⟩ := exists_isCoherent_pushforward_iso (K ^ (e + 1)).subschemeι H.obj
    ((annihilatedByKer_subschemeι_pow_iff K (e + 1) H.obj).mpr hHann)
  refine ⟨⟨S, hScoh⟩, ⟨?_⟩⟩
  refine ObjectProperty.isoMk _ (isoOfWhiskerRightPushforwardIso (K ^ (e + 1)).subschemeι ?_)
  refine (pushforwardCompletionIso (K ^ (e + 1)).subschemeι (baseIdealSheaf A I f)
    ⟨S, hScoh⟩).symm ≪≫ ?_
  exact (ObjectProperty.ι _).mapIso
    ((completionFunctor X (baseIdealSheaf A I f)).mapIso (ObjectProperty.isoMk _ eS)) ≪≫ eHsys

/-- **Essential surjectivity on every subscheme `V(𝒦 ᵉ⁺¹)` at once**: if for every `e` each
coherent `𝓘`-adic system on `X` killed by `𝒦 ᵉ⁺¹` lies in the essential image of the completion
functor of `X`, then the completion functor of every `V(𝒦 ᵉ⁺¹)` is essentially surjective. -/
public theorem essSurj_completionFunctor_comap_subschemeι_forall
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ (e : ℕ) (𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f)),
        IsSystemAnnihilatedBy (K ^ (e + 1)) 𝓖.obj →
          (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ e : ℕ,
      letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian ((K ^ (e + 1)).subschemeι ≫ f)
      (completionFunctor (K ^ (e + 1)).subscheme
        ((baseIdealSheaf A I f).comap (K ^ (e + 1)).subschemeι)).EssSurj :=
  fun e => essSurj_completionFunctor_comap_subschemeι_of_essImage A I f K e (hInd e)

/-- **Hypothesis (1) of [Stacks, Tag 088A].** If every coherent `𝓘`-adic system on `X` killed by
`𝒦 ᵉ⁺¹` lies in the essential image of the completion functor of `X`, then the completion functor
of the closed subscheme `V(𝒦 ᵉ⁺¹)` along the inverse image of `𝓘` is an equivalence. -/
public theorem isEquivalence_completionFunctor_comap_subschemeι_of_essImage
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData) (e : ℕ)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        IsSystemAnnihilatedBy (K ^ (e + 1)) 𝓖.obj →
          (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((K ^ (e + 1)).subschemeι ≫ f)
    (completionFunctor (K ^ (e + 1)).subscheme
      ((baseIdealSheaf A I f).comap (K ^ (e + 1)).subschemeι)).IsEquivalence := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian (K ^ (e + 1)).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((K ^ (e + 1)).subschemeι ≫ f)
  obtain ⟨hff⟩ := fullyFaithful_completionFunctor_comap_subschemeι A I f (K ^ (e + 1))
  let _ := hff.full
  let _ := hff.faithful
  let _ := essSurj_completionFunctor_comap_subschemeι_of_essImage A I f K e hInd
  exact { }

end Stacks.Algebraization

end
