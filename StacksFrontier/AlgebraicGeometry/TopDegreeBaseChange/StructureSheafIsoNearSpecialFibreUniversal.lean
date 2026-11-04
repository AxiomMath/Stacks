module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreReduction
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport

/-!
# `𝒪_Y ≅ f_*𝒪_X` and `R¹f_*𝒪_X = 0` over a neighbourhood of a point of the base

Let `X --f--> Y --q--> S` be a commutative triangle of schemes, `s ∈ S`, and assume the
hypotheses of [Stacks, Tag 0E7L] at `s`, with moreover `q` universally closed. Then there is an
open neighbourhood `U₀` of `s` such that for **every** cartesian base change of `f` along a
scheme `S' ⟶ S` landing in `U₀`, that is for every pair of cartesian squares

```
X' --a--> X
|f'       |f
Y' --b--> Y
|q'       |q
S' --h--> S
```

with `h(S') ⊆ U₀`, the map `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` is an isomorphism and `R¹f'_*𝒪_{X'} = 0`.

This is the scheme-theoretic step of the proof of [Stacks, Tag 0E88]: [Stacks, Tag 0E7L] gives
an open `V` of `Y` containing `Y_s` over which the two conclusions hold universally, and since
`q` is closed the complement of `q(Y ∖ V)` is an open neighbourhood of `s` over which `Y`
lies inside `V`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isPullback_lift_of_range_subset`: a cartesian
  square over `q` whose top morphism lands in an open `V` of `Y` is cartesian over `V ⟶ S`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.exists_isOpen_forall_isPullback_of_specialFibre`:
  the statement above.

## References

* [Stacks Project, Tag 0E88](https://stacks.math.columbia.edu/tag/0E88)
* [Stacks Project, Tag 0E7L](https://stacks.math.columbia.edu/tag/0E7L)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

/-- **A cartesian square over `q` whose top morphism lands in an open `V` is cartesian over
`V ⟶ S`.** If `IsPullback b q' q h` and `b = b' ≫ V.ι`, then `IsPullback b' q' (V.ι ≫ q) h`:
`V.ι` is a monomorphism, so lifts into `Y'` of maps into `V` are lifts of their composites with
`V.ι`. -/
theorem isPullback_lift_of_comp {Y Y' S S' : Scheme.{u}} {q : Y ⟶ S} {h : S' ⟶ S}
    {b : Y' ⟶ Y} {q' : Y' ⟶ S'} (H : IsPullback b q' q h) (V : Y.Opens) (b' : Y' ⟶ V)
    (hb : b' ≫ V.ι = b) : IsPullback b' q' (V.ι ≫ q) h := by
  refine ⟨⟨by rw [← Category.assoc, hb, H.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ H.lift (c.fst ≫ V.ι) c.snd (by rw [Category.assoc, c.condition]))
    (fun c ↦ ?_) (fun c ↦ H.lift_snd _ _ _) (fun c m h₁ h₂ ↦ ?_)⟩⟩
  · rw [← cancel_mono V.ι, Category.assoc, hb]
    exact H.lift_fst _ _ _
  · exact H.hom_ext (by rw [H.lift_fst, ← hb, ← Category.assoc, h₁]) (by rw [H.lift_snd, h₂])

/-- **`𝒪_Y ≅ f_*𝒪_X` and `R¹f_*𝒪_X = 0` over a neighbourhood of `s`, for every cartesian base
change.** Let `X --f--> Y --q--> S` be a commutative triangle of schemes and `s ∈ S` satisfying
the hypotheses of [Stacks, Tag 0E7L] (`exists_isOpen_isIso_unitToPushforwardUnit_of_specialFibre`),
and assume `q` universally closed. Then there is an open neighbourhood `U₀` of `s` such that for
every pair of cartesian squares `X' --a--> X`, `Y' --b--> Y` over `f`, and `Y' --b--> Y`,
`S' --h--> S` over `q`, with `h` landing in `U₀`, the base change `f' : X' ⟶ Y'` has
`𝒪_{Y'} ≅ f'_*𝒪_{X'}` and `R¹f'_*𝒪_{X'} = 0`.

[Stacks, Tag 0E7L] gives an open `V ⊇ Y_s` over which both conclusions hold after every base
change `S' ⟶ S`. The image under `q` of the closed set `Y ∖ V` is closed and misses `s`; its
complement is `U₀`. Over `U₀` the morphism `b` lands in `V`, so `Y'` is the base change of
`V ⟶ S` (`isPullback_lift_of_comp`), and `f'` is the base change of the morphism of
[Stacks, Tag 0E7L] along an isomorphism, which transports both conclusions
(`isZero_and_isIso_of_isPullback`). -/
theorem exists_isOpen_forall_isPullback_of_specialFibre {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (q : Y ⟶ S) (s : S) [LocallyOfFinitePresentation (f ≫ q)] [LocallyOfFinitePresentation q]
    [IsProper f] [UniversallyClosed q]
    (hflat : ∀ x : X, (f ≫ q) x = s → IsFlatAt (f ≫ q).toLRSHom.toShHom x)
    (hdim : ∀ y : q.fiber s, topologicalKrullDim ((Stacks.Flatness.fiberHom f q s).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f (q.fiberι s))))
    (hiso : IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f (q.fiberι s)))) :
    ∃ U₀ : S.Opens, s ∈ U₀ ∧ ∀ ⦃S' Y' X' : Scheme.{u}⦄ (h : S' ⟶ S) (b : Y' ⟶ Y)
      (q' : Y' ⟶ S') (a : X' ⟶ X) (f' : X' ⟶ Y'), (∀ t, h t ∈ U₀) →
        IsPullback b q' q h → IsPullback a f' f b →
        IsIso (Scheme.Modules.unitToPushforwardUnit f') ∧
          IsZero (firstDirectImageStructureSheaf f') := by
  obtain ⟨V, hVs, -, -, -, -, -, hbc⟩ :=
    exists_isOpen_isIso_unitToPushforwardUnit_of_specialFibre f q s hflat hdim hR hiso
  refine ⟨⟨(q.base '' (V : Set Y)ᶜ)ᶜ, (q.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩,
    ?_, ?_⟩
  · rintro ⟨y, hy, hys⟩
    exact hy (hVs y hys)
  intro S' Y' X' h b q' a f' hh H1 H2
  have hbV (y' : Y') : b y' ∈ V := by
    by_contra hn
    exact hh (q' y') ⟨b y', hn, by rw [← Scheme.Hom.comp_apply, H1.w, Scheme.Hom.comp_apply]⟩
  let b' : Y' ⟶ V := IsOpenImmersion.lift V.ι b (by
    rintro _ ⟨y', rfl⟩
    simpa using hbV y')
  have hb' : b' ≫ V.ι = b := IsOpenImmersion.lift_fac _ _ _
  have H1' := isPullback_lift_of_comp H1 V b' hb'
  obtain ⟨-, -, hq3, hq4, hq5⟩ := hbc h
  set fst₁ := pullback.fst (V.ι ≫ q) h
  set f₁ := pullback.snd (f ∣_ V) fst₁
  have Hr : IsPullback (pullback.fst (f ∣_ V) fst₁ ≫ (f ⁻¹ᵁ V).ι) f₁ f (fst₁ ≫ V.ι) :=
    (IsPullback.of_hasPullback (f ∣_ V) fst₁).paste_horiz (isPullback_morphismRestrict f V).flip
  have : IsProper f₁ := MorphismProperty.of_isPullback Hr inferInstance
  have he : H1'.isoPullback.hom ≫ fst₁ ≫ V.ι = b := by
    rw [← Category.assoc, IsPullback.isoPullback_hom_fst, hb']
  let k : X' ⟶ pullback (f ∣_ V) fst₁ :=
    Hr.lift a (f' ≫ H1'.isoPullback.hom) (by rw [H2.w, Category.assoc, he])
  have H : IsPullback k f' f₁ H1'.isoPullback.hom :=
    IsPullback.of_right (by rwa [Hr.lift_fst, he]) (Hr.lift_snd _ _ _) Hr
  exact (isZero_and_isIso_of_isPullback H hq3 hq4 hq5).symm

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange
