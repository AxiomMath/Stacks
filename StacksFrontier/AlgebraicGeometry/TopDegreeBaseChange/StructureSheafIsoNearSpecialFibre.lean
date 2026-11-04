module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseFlatnessAndVanishingNearSpecialFibre
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FirstDirectImageBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport

/-!
# The structure sheaf near a special fibre

This file assembles [Stacks, Tag 0E7L]: for `X --f--> Y --q--> S` and `s ∈ S` under the
hypotheses of the tag there is an open `Y_s ⊆ V ⊆ Y` over which `Y` and `X` are flat over `S`,
the fibres of `f` have dimension at most one, `R¹f_* 𝒪_X` vanishes and `𝒪_V ≅ f_* 𝒪_X|_V`, all
five persisting after base change along any `S' ⟶ S`.

## Main results

* `conclusions_of_isOpen`: the five conclusions and their persistence on an open, from their
  pointwise form together with the two clauses of [Stacks, Tag 0E7K] over that open.

## References

* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
* [Stacks Project, Tag 0E7K](https://stacks.math.columbia.edu/tag/0E7K)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

variable {X Y S : Scheme.{u}}

/-- **The conclusions of [Stacks, Tag 0E7L] on an open, from their pointwise form.** Let
`X --f--> Y --q--> S` with `f` proper and `V ⊆ Y` open. Suppose `f⁻¹(V)` is flat over `S`, the
fibres of `f` over `V` have dimension at most one, `R¹f_* 𝒪_X|_V = 0`, `𝒪_Y ⟶ f_* 𝒪_X` is
bijective on the stalks at the points of `V`, and — the two clauses of [Stacks, Tag 0E7K] for
`f⁻¹(V) ⟶ V ⟶ S` — `(f ∣_ V)_* 𝒪` is flat over `S` and its formation commutes with base change
along every `S' ⟶ S`. Then `V` is flat over `S`, `𝒪_V ≅ (f ∣_ V)_* 𝒪`, and after base change of
`f⁻¹(V) ⟶ V` along any `S' ⟶ S` all five conclusions of the tag hold again. -/
theorem conclusions_of_isOpen (f : X ⟶ Y) (q : Y ⟶ S) [IsProper f] (V : Y.Opens)
    (hflatX : Flat ((f ⁻¹ᵁ V).ι ≫ (f ≫ q)))
    (hdim : ∀ y : Y, y ∈ V → topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj (firstDirectImageStructureSheaf f)))
    (hbij : ∀ y : Y, y ∈ V → Function.Bijective
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor Y y).map
        (Scheme.Modules.unitToPushforwardUnit f)))
    (hFflat : IsFlatOver (V.ι ≫ q).toLRSHom.toShHom (directImageStructureSheaf (f ∣_ V)))
    (hbc : ∀ ⦃S' : Scheme.{u}⦄ (h : S' ⟶ S),
      IsIso (directImageStructureSheafBaseChangeMap (f ∣_ V) (pullback.fst (V.ι ≫ q) h))) :
    Flat (V.ι ≫ q) ∧ IsZero (firstDirectImageStructureSheaf (f ∣_ V)) ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit (f ∣_ V)) ∧
      ∀ ⦃S' : Scheme.{u}⦄ (h : S' ⟶ S),
        Flat (pullback.snd (V.ι ≫ q) h) ∧
        Flat (pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h) ≫ pullback.snd (V.ι ≫ q) h) ∧
        (∀ y' : (pullback (V.ι ≫ q) h : Scheme.{u}), topologicalKrullDim
          ((pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h)).fiber y') ≤
            ((1 : ℕ) : WithBot ℕ∞)) ∧
        IsZero (firstDirectImageStructureSheaf
          (pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h))) ∧
        IsIso (Scheme.Modules.unitToPushforwardUnit
          (pullback.snd (f ∣_ V) (pullback.fst (V.ι ≫ q) h))) := by
  have hdimV : ∀ v : V.toScheme,
      topologicalKrullDim ((f ∣_ V).fiber v) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_fiber_morphismRestrict_le f V 1 hdim
  have hRV : IsZero (firstDirectImageStructureSheaf (f ∣_ V)) :=
    IsZero.of_iso hR (firstDirectImageRestrictIso f V)
  have hiso : IsIso (Scheme.Modules.unitToPushforwardUnit (f ∣_ V)) :=
    isIso_of_bijective_modulesStalkFunctor_map _ fun v =>
      bijective_stalk_unitToPushforwardUnit_of_isPullback
        (isPullback_morphismRestrict f V).flip v (hbij _ v.2)
  have hflatV : Flat (f ∣_ V ≫ V.ι ≫ q) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    exact hflatX
  have hq : Flat (V.ι ≫ q) :=
    flat_of_isIso_unitToPushforwardUnit_of_isFlatOver (f ∣_ V) (V.ι ≫ q) hiso hFflat
  refine ⟨hq, hRV, hiso, fun S' h => ?_⟩
  set g := pullback.fst (V.ι ≫ q) h
  have hsqV : IsPullback g (pullback.snd (V.ι ≫ q) h) (V.ι ≫ q) h :=
    IsPullback.of_hasPullback _ _
  have hsqX : IsPullback (pullback.fst (f ∣_ V) g) (pullback.snd (f ∣_ V) g) (f ∣_ V) g :=
    IsPullback.of_hasPullback _ _
  refine ⟨MorphismProperty.of_isPullback hsqV ‹_›, ?_, fun y' => ?_, ?_, ?_⟩
  · have := hsqX.paste_vert hsqV
    exact MorphismProperty.of_isPullback this hflatV
  · exact topologicalKrullDim_fiber_le_of_isPullback hsqX 1 y' (hdimV _)
  · exact (isZero_pullback_firstDirectImage_iff (f ∣_ V) hdimV g).1 (Functor.map_isZero _ hRV)
  · have := hbc h
    have hc := unitToPushforwardUnit_comp_directImageStructureSheafBaseChangeMap (f ∣_ V) g
    have : IsIso ((Scheme.Modules.pullbackUnitIso g).hom ≫
        Scheme.Modules.unitToPushforwardUnit (pullback.snd (f ∣_ V) g)) := by
      rw [hc]; infer_instance
    exact IsIso.of_isIso_comp_left (Scheme.Modules.pullbackUnitIso g).hom _

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
