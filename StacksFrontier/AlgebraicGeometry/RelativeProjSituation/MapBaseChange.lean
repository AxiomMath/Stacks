module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj

/-!
# `Proj` of a base change is the base change of `Proj`

Let `f : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings with `ℬ₊ ≤ 𝒜₊.map f`, so that
`AlgebraicGeometry.Proj.map f` is defined, and suppose that `ℬ` is obtained from `𝒜` by extending
the degree-zero scalars along `ℬ₀`. The content of Stacks tag 01N2 is then that the square

```
Proj ℬ  ⟶ Spec (ℬ 0)
  |             |
  v             v
Proj 𝒜  ⟶ Spec (𝒜 0)
```

is cartesian. This file proves that from the chart hypothesis alone: the base-change hypothesis
is asked for only on the standard affine charts, as
`Stacks.Proj.IsBaseChangeOnCharts`, where it says that

`Spec (Away ℬ (f s)) = Spec (Away 𝒜 s) ×_{Spec (𝒜 0)} Spec (ℬ 0)`

for every homogeneous `s` of positive degree — the chart-level statement that extension of
scalars commutes with degree-zero localization. From that alone the whole square above is
cartesian.

The cartesian square itself needs nothing of `Spec (ℬ 0) ⟶ Spec (𝒜 0)`: the comparison into the
fibre product is an isomorphism because being an isomorphism is Zariski-local at the target and
the fibre product is covered by the base changes of the standard affine charts of `Proj 𝒜`, on
each of which the comparison *is* the chart hypothesis.

Assuming in addition that `Spec (ℬ 0) ⟶ Spec (𝒜 0)` is an open immersion gives more: the chart
squares then give that `Proj.map f` is an open immersion, because being an open immersion is
Zariski-local at the target and the charts `Spec (Away 𝒜 s)` cover `Proj 𝒜`; and the image of
`Proj.map f` is computed chart by chart against `Stacks.Proj.opens_eq_of_awayι_preimage_eq`.

## Main definitions

* `Stacks.Proj.IsBaseChangeOnCharts` is the chart-level base-change hypothesis, and
  `Stacks.Proj.IsBaseChangeOnCharts.of_isPushout` reduces it to a pushout of rings.

## Main results

* `AlgebraicGeometry.IsOpenImmersion.opensRange_eq_preimage_opensRange`: in a cartesian square
  whose two vertical maps are open immersions, the image of one is the preimage of the image of
  the other.
* `AlgebraicGeometry.Proj.SpecMap_awayMap_fromZeroRingHom`: the chart base-change square commutes.
  This too is unconditional, and it is the square that
  `Stacks.Proj.IsBaseChangeOnCharts` asks to be cartesian.
* `AlgebraicGeometry.Proj.isOpenImmersion_map`: under the chart hypothesis, `Proj.map f` is an
  open immersion.
* `AlgebraicGeometry.Proj.opensRange_map`: its image is the part of `Proj 𝒜` lying over the image
  of `Spec (ℬ 0) ⟶ Spec (𝒜 0)`.
* `AlgebraicGeometry.Proj.isPullback_toSpecZero_map`: **the cartesian square above**, from the
  chart hypothesis alone — no assumption on `Spec (ℬ 0) ⟶ Spec (𝒜 0)`.

## Implementation notes

`Stacks.Proj.IsBaseChangeOnCharts` is phrased as cartesianness of a square of affine schemes
rather than as an isomorphism `Away ℬ (f s) ≅ ℬ₀ ⊗_{𝒜₀} Away 𝒜 s`, for two reasons: the square is
the form in which the conclusion is used, and the tensor product cannot even be formed unless the
two gradings are indexed by submodules over a common base, which the `SetLike` interface of
`AlgebraicGeometry.Proj.map` does not provide.

`AlgebraicGeometry.Scheme.Hom.opensRange` takes the open-immersion property as an instance
argument, so an equation between morphisms cannot be rewritten underneath it — the motive of the
rewrite mentions the instance. Every image computation here therefore goes through
`AlgebraicGeometry.IsOpenImmersion.opensRange_eq_preimage_opensRange`, which is applied to a
cartesian square rather than rewritten into one.

No `@[stacks]` attribute is attached. Tag 01N2 asserts the square is cartesian for a base change
`ℬ = R' ⊗_R 𝒜`, and what is proved here is that it is cartesian as soon as the chart squares are;
the identification of `Away ℬ (f s)` with the base change of `Away 𝒜 s`, which is the ring-level
half of 01N2, is not proved here. See
`StacksFrontier/RingTheory/GradedAlgebra/Proj/StandardOpenBaseChange.lean` for that half in the case
of a literal tensor product.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public section

open CategoryTheory Limits HomogeneousIdeal HomogeneousLocalization Graded

universe u

namespace AlgebraicGeometry

/-- **In a cartesian square whose two vertical maps are open immersions, the image of one is the
preimage of the image of the other.** This is the `W = ⊤` case of
`AlgebraicGeometry.IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback`. -/
theorem IsOpenImmersion.opensRange_eq_preimage_opensRange {X Y U V : Scheme.{u}} {g : X ⟶ Y}
    {g' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iU] [IsOpenImmersion iV]
    (H : IsPullback g' iU iV g) : iU.opensRange = g ⁻¹ᵁ iV.opensRange := by
  simpa using IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤

namespace Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **The chart base-change square commutes.** On the chart of a homogeneous `s`, the comparison
`Spec (Away ℬ (f s)) ⟶ Spec (Away 𝒜 s)` is a morphism over `Spec (ℬ 0) ⟶ Spec (𝒜 0)`. This is
`AlgebraicGeometry.Proj.awayMap_comp_fromZeroRingHom` read through `Spec`. -/
theorem SpecMap_awayMap_fromZeroRingHom (f : 𝒜 →+*ᵍ ℬ) (s : A) :
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫
        Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers s))) =
      Spec.map (CommRingCat.ofHom (fromZeroRingHom ℬ (Submonoid.powers (f s)))) ≫
        Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    awayMap_comp_fromZeroRingHom]

end Proj

end AlgebraicGeometry

namespace Stacks.Proj

open AlgebraicGeometry AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **The chart-level base-change hypothesis.** For every homogeneous `s` of positive degree the
commuting square `AlgebraicGeometry.Proj.SpecMap_awayMap_fromZeroRingHom` is cartesian, that is

`Spec (Away ℬ (f s)) = Spec (Away 𝒜 s) ×_{Spec (𝒜 0)} Spec (ℬ 0)`.

Equivalently, the degree-zero localization `Away 𝒜 s` turns into `Away ℬ (f s)` under extension
of scalars from `𝒜 0` to `ℬ 0`. -/
abbrev IsBaseChangeOnCharts (f : 𝒜 →+*ᵍ ℬ) : Prop :=
  ∀ {i : ℕ} (_hi : 0 < i) (s : A) (_hs : s ∈ 𝒜 i),
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (Spec.map (CommRingCat.ofHom (fromZeroRingHom ℬ (Submonoid.powers (f s)))))
      (Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers s))))
      (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))

/-- **The chart hypothesis is a statement about rings.** It holds as soon as
`Away ℬ (f s) = Away 𝒜 s ⊗_{𝒜 0} ℬ 0` as a pushout of commutative rings, for every homogeneous
`s` of positive degree; `Spec` turns that pushout into the required pullback. -/
theorem IsBaseChangeOnCharts.of_isPushout (f : 𝒜 →+*ᵍ ℬ)
    (H : ∀ {i : ℕ} (_hi : 0 < i) (s : A) (_hs : s ∈ 𝒜 i),
      IsPushout (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers s)))
        (CommRingCat.ofHom f.gradedZeroRingHom) (CommRingCat.ofHom (Away.map f s))
        (CommRingCat.ofHom (fromZeroRingHom ℬ (Submonoid.powers (f s))))) :
    IsBaseChangeOnCharts f := fun hi s hs ↦
  isPullback_SpecMap_of_isPushout _ _ _ _ (H hi s hs)

end Stacks.Proj

namespace AlgebraicGeometry.Proj

open Stacks.Proj

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {f : 𝒜 →+*ᵍ ℬ}

/-- Under the chart hypothesis, the comparison of charts is an open immersion: it is the base
change of `Spec (ℬ 0) ⟶ Spec (𝒜 0)`. -/
theorem isOpenImmersion_SpecMap_awayMap
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))]
    (H : IsBaseChangeOnCharts f) {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Away.map f s))) :=
  MorphismProperty.of_isPullback (H hi s hs).flip inferInstance

/-- A morphism property respecting isomorphisms holds for `pullback.snd` as soon as it holds for
the second projection of any pullback square on the same cospan. -/
private theorem prop_pullback_snd_of_isPullback {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    {X Y Z T : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z} {fst : T ⟶ X} {snd : T ⟶ Y}
    (h : IsPullback fst snd f g) [HasPullback f g] (H : P snd) : P (pullback.snd f g) := by
  rwa [← h.isoPullback_hom_snd, P.cancel_left_of_respectsIso] at H

/-- **`Proj.map f` is an open immersion.** Being an open immersion is Zariski-local at the target,
the standard affine charts `Spec (Away 𝒜 s)` cover `Proj 𝒜`, and over each of them `Proj.map f`
is the chart comparison `Spec (Away ℬ (f s)) ⟶ Spec (Away 𝒜 s)` by
`AlgebraicGeometry.Proj.isPullback_awayι_map`. -/
theorem isOpenImmersion_map (hf : ℬ₊ ≤ 𝒜₊.map f)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))]
    (H : IsBaseChangeOnCharts f) : IsOpenImmersion (Proj.map f hf) := by
  refine IsZariskiLocalAtTarget.of_openCover (affineOpenCover 𝒜).openCover ?_
  rintro ⟨i, a⟩
  have hsq := (isPullback_awayι_map f hf i.2 (a : A) a.2).flip
  show IsOpenImmersion (pullback.snd (Proj.map f hf) (awayι 𝒜 (a : A) a.2 i.2))
  exact prop_pullback_snd_of_isPullback (P := @IsOpenImmersion) hsq
    (isOpenImmersion_SpecMap_awayMap H i.2 (a : A) a.2)

/-- The part of the image of `Proj.map f` visible in the standard affine chart of a homogeneous
`s` is the image of the chart comparison. This is unconditional once `Proj.map f` is known to be
an open immersion. -/
theorem awayι_preimage_opensRange_map (hf : ℬ₊ ≤ 𝒜₊.map f) [IsOpenImmersion (Proj.map f hf)]
    {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (Away.map f s)))] :
    awayι 𝒜 s hs hi ⁻¹ᵁ (Proj.map f hf).opensRange =
      (Spec.map (CommRingCat.ofHom (Away.map f s))).opensRange :=
  (IsOpenImmersion.opensRange_eq_preimage_opensRange
    (isPullback_awayι_map f hf hi s hs).flip).symm

/-- **The image of `Proj.map f` is the part of `Proj 𝒜` over the image of
`Spec (ℬ 0) ⟶ Spec (𝒜 0)`.** Both sides are opens of `Proj 𝒜`, so they may be compared on the
standard affine charts, where the statement is the chart hypothesis. -/
theorem opensRange_map (hf : ℬ₊ ≤ 𝒜₊.map f)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))]
    [IsOpenImmersion (Proj.map f hf)] (H : IsBaseChangeOnCharts f) :
    (Proj.map f hf).opensRange =
      toSpecZero 𝒜 ⁻¹ᵁ (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)).opensRange := by
  refine opens_eq_of_awayι_preimage_eq 𝒜 fun hi s hs ↦ ?_
  have := isOpenImmersion_SpecMap_awayMap H hi s hs
  rw [awayι_preimage_opensRange_map hf hi s hs,
    IsOpenImmersion.opensRange_eq_preimage_opensRange (H hi s hs).flip,
    ← Scheme.Hom.comp_preimage, awayι_toSpecZero]

/-- **The cartesian square of Stacks tag 01N2.** If the chart squares are cartesian, then

```
Proj ℬ  ⟶ Spec (ℬ 0)
  |             |
  v             v
Proj 𝒜  ⟶ Spec (𝒜 0)
```

is cartesian: `Proj ℬ` is the base change of `Proj 𝒜` along `Spec (ℬ 0) ⟶ Spec (𝒜 0)`.

Nothing is assumed about `Spec (ℬ 0) ⟶ Spec (𝒜 0)`. The comparison `c : Proj ℬ ⟶ Proj 𝒜 ×_{Spec
(𝒜 0)} Spec (ℬ 0)` is an isomorphism because being an isomorphism is Zariski-local at the target
and the fibre product is covered by the base changes of the standard affine charts of `Proj 𝒜`:
over the chart of a homogeneous `s`, the part of `Proj ℬ` lying over it is `Spec (Away ℬ (f s))`
by `AlgebraicGeometry.Proj.isPullback_awayι_map`, the corresponding piece of the fibre product is
`Spec (Away 𝒜 s) ×_{Spec (𝒜 0)} Spec (ℬ 0)`, and the chart hypothesis says exactly that the
comparison between them is an isomorphism. -/
theorem isPullback_toSpecZero_map (hf : ℬ₊ ≤ 𝒜₊.map f) (H : IsBaseChangeOnCharts f) :
    IsPullback (toSpecZero ℬ) (Proj.map f hf)
      (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜) := by
  have comm : toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom f.gradedZeroRingHom) =
      Proj.map f hf ≫ toSpecZero 𝒜 := (map_toSpecZero f hf).symm
  have HQ := IsPullback.of_hasPullback
    (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜)
  set c := pullback.lift (toSpecZero ℬ) (Proj.map f hf) comm with hcdef
  have hcfst : c ≫ pullback.fst (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))
      (toSpecZero 𝒜) = toSpecZero ℬ := pullback.lift_fst _ _ _
  have hcsnd : c ≫ pullback.snd (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom))
      (toSpecZero 𝒜) = Proj.map f hf := pullback.lift_snd _ _ _
  have hiso : IsIso c := by
    show (MorphismProperty.isomorphisms Scheme) c
    refine IsZariskiLocalAtTarget.of_openCover
      (((affineOpenCover 𝒜).openCover).pullback₁ (pullback.snd
        (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))) ?_
    rintro ⟨i, a⟩
    show (MorphismProperty.isomorphisms Scheme)
      (pullback.snd c (pullback.fst (pullback.snd
        (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))
        (awayι 𝒜 (a : A) a.2 i.2)))
    have S2 := (isPullback_awayι_map f hf i.2 (a : A) a.2).flip
    have B := IsPullback.of_hasPullback (pullback.snd
      (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))
      (awayι 𝒜 (a : A) a.2 i.2)
    have hγcomm : (awayι ℬ (f (a : A)) (map_mem f a.2) i.2 ≫ c) ≫ pullback.snd
        (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜) =
        Spec.map (CommRingCat.ofHom (Away.map f (a : A))) ≫ awayι 𝒜 (a : A) a.2 i.2 := by
      rw [Category.assoc, hcsnd]
      exact awayι_comp_map f hf i.2 (a : A) a.2
    set γ := pullback.lift (awayι ℬ (f (a : A)) (map_mem f a.2) i.2 ≫ c)
      (Spec.map (CommRingCat.ofHom (Away.map f (a : A)))) hγcomm with hγdef
    have hγfst : γ ≫ pullback.fst (pullback.snd
        (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))
        (awayι 𝒜 (a : A) a.2 i.2) =
        awayι ℬ (f (a : A)) (map_mem f a.2) i.2 ≫ c := pullback.lift_fst _ _ _
    have hγsnd : γ ≫ pullback.snd (pullback.snd
        (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))
        (awayι 𝒜 (a : A) a.2 i.2) =
        Spec.map (CommRingCat.ofHom (Away.map f (a : A))) := pullback.lift_snd _ _ _
    have T : IsPullback (awayι ℬ (f (a : A)) (map_mem f a.2) i.2) γ c
        (pullback.fst (pullback.snd
          (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))
          (awayι 𝒜 (a : A) a.2 i.2)) := by
      refine IsPullback.of_bot ?_ hγfst.symm B
      rw [hγsnd, hcsnd]
      exact S2
    have P1 := H i.2 (a : A) a.2
    have P2 : IsPullback
        (pullback.snd (pullback.snd
          (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))
          (awayι 𝒜 (a : A) a.2 i.2))
        (pullback.fst (pullback.snd
          (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))
          (awayι 𝒜 (a : A) a.2 i.2) ≫
          pullback.fst (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) (toSpecZero 𝒜))
        (awayι 𝒜 (a : A) a.2 i.2 ≫ toSpecZero 𝒜)
        (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) :=
      IsPullback.paste_vert B.flip HQ.flip
    have P1' : IsPullback (Spec.map (CommRingCat.ofHom (Away.map f (a : A))))
        (Spec.map (CommRingCat.ofHom (fromZeroRingHom ℬ (Submonoid.powers (f (a : A))))))
        (awayι 𝒜 (a : A) a.2 i.2 ≫ toSpecZero 𝒜)
        (Spec.map (CommRingCat.ofHom f.gradedZeroRingHom)) := by
      rw [awayι_toSpecZero 𝒜 (a : A) a.2 i.2]; exact P1
    have hγiso : IsIso γ := by
      have he : γ = P1'.isoPullback.hom ≫ P2.isoPullback.inv := by
        refine P2.hom_ext ?_ ?_
        · rw [hγsnd, Category.assoc, P2.isoPullback_inv_fst, P1'.isoPullback_hom_fst]
        · rw [Category.assoc, P2.isoPullback_inv_snd, P1'.isoPullback_hom_snd,
            ← Category.assoc, hγfst, Category.assoc, hcfst]
          exact awayι_toSpecZero ℬ (f (a : A)) (map_mem f a.2) i.2
      rw [he]
      infer_instance
    exact prop_pullback_snd_of_isPullback (P := MorphismProperty.isomorphisms Scheme) T hγiso
  exact IsPullback.of_iso_pullback ⟨comm⟩ (asIso c) hcfst hcsnd

end AlgebraicGeometry.Proj

end
