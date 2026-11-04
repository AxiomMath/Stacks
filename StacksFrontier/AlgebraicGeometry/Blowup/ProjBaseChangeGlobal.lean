module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjChartSquare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Proj` commutes with base change

Let `A` be a graded `R`-algebra with grading `𝒜 : ℕ → Submodule R A` and let `S` be an
`R`-algebra. `StacksFrontier/AlgebraicGeometry/Blowup/ProjChartSquare.lean` proves that the standard
affine chart of `Proj (S ⊗[R] A)` attached to `1 ⊗ₜ a` is the fibre product of the chart of
`Proj A` attached to `a` with `Spec` of the degree-zero part of the base change. This file
globalizes that statement from one chart to the whole of `Proj`: the squares

```
Proj (S ⊗[R] A) ⟶ Proj A            Proj (S ⊗[R] A) ⟶ Proj A
      |                |                    |              |
      v                v                    v              v
Spec (S ⊗[R] 𝒜) 0 ⟶ Spec (𝒜 0)          Spec S     ⟶    Spec R
```

are cartesian. The right-hand one is the square of Stacks tag 01N2 part (2), with `ψ` the
canonical inclusion `A → S ⊗[R] A`.

The globalization is `AlgebraicGeometry.Scheme.isPullback_of_openCover`: cartesianness of a
square of schemes may be checked after pulling the top-right corner back along an open cover of
itself. The cover used is `AlgebraicGeometry.Proj.affineOpenCover`, by the standard affine charts
`Spec (Away 𝒜 a)` of `Proj A`, and the pullback of `Proj (S ⊗[R] A) ⟶ Proj A` along one of them
is identified with the base-changed chart `Spec (Away (S ⊗[R] 𝒜) (1 ⊗ₜ a))` by
`AlgebraicGeometry.Proj.isPullback_awayι_map`.

## Main results

* `AlgebraicGeometry.Proj.isPullback_awayι_map`: for any graded ring homomorphism
  `f : 𝒜 →+*ᵍ ℬ` with `ℬ₊ ≤ 𝒜₊.map f`, the standard affine chart of `Proj ℬ` attached to `f s`
  is the fibre product of the chart of `Proj 𝒜` attached to `s` with `Proj ℬ`. Equivalently,
  `D₊(f s)` is the preimage of `D₊(s)`.
* `AlgebraicGeometry.Proj.isIso_map`: a graded ring homomorphism with a two-sided graded inverse
  induces an isomorphism of projective spectra.
* `AlgebraicGeometry.Proj.opensRange_eq_preimage_of_isPullback`: in a cartesian square whose
  bottom edge is an open immersion, the image of the left edge is the preimage of the image of
  the bottom edge.
* `Stacks.ProjBaseChange.isPullback_map_toSpecZero`: the base-change square of projective spectra
  over the degree-zero parts is cartesian.
* `Stacks.ProjBaseChange.isPullback_map_Spec`: **`Proj` commutes with base change.** The
  base-change square of projective spectra over `Spec S ⟶ Spec R` is cartesian.
* `Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap` and
  `Stacks.ProjBaseChange.isPullback_map_Spec_projZeroRingHom`: the same square with the structure
  morphism of `Proj A` written through the degree-zero projection `A → 𝒜 0`.
* `Stacks.ProjBaseChange.isOpenImmersion_map` and
  `Stacks.ProjBaseChange.opensRange_map`: if `Spec S ⟶ Spec R` is an open immersion then so is
  `Proj (S ⊗[R] A) ⟶ Proj A`, with image the preimage of the image of `Spec S`.
* `Stacks.ProjBaseChange.isPullback_map_of_baseChange`,
  `Stacks.ProjBaseChange.isOpenImmersion_map_of_baseChange` and
  `Stacks.ProjBaseChange.opensRange_map_of_baseChange`: the same three statements for a graded
  ring `ℬ` only *isomorphic* to the base change. These are the two hypotheses
  `Stacks.RelativeProj.Data.isOpenImmersion_map` and
  `Stacks.RelativeProj.Data.opensRange_map` ask for, at the level of rings.

## Implementation notes

The index type of `AlgebraicGeometry.Proj.affineOpenCover` is a sigma type only definitionally,
and the Mathlib lemmas describing the cover (`Scheme.AffineOpenCover.openCover_f`) are proved with
the backward transparency flag that this repository forbids, so they do not fire under `rw`/`simp`
here. The chart condition is therefore discharged by
destructing the cover index and applying a separately stated chart-local lemma
(`Stacks.ProjBaseChange.isPullback_pullbackSnd_awayι`), letting definitional unfolding match the
cover's morphism with `AlgebraicGeometry.Proj.awayι`.

The two squares of this file are related by the degree-zero square
`Stacks.ProjBaseChange.isPullback_Spec_gradedZeroRingHom`: the second is the vertical paste of
the first with it.

Tag 01N2 is stated for an arbitrary graded ring homomorphism `ψ : A → B` together with an
identification `B = R' ⊗_R A`; `Stacks.ProjBaseChange.isPullback_map_Spec` is the case where `B`
is the tensor product itself and `ψ` the canonical inclusion, and
`Stacks.ProjBaseChange.isPullback_map_of_baseChange` is the general case. Part (1) of the tag,
that the morphism of projective spectra is everywhere defined, is
`Stacks.AlgebraicGeometry.ProjShared.mapDomain_baseChange`, whose covering criterion is fed by
`Stacks.ProjBaseChange.irrelevant_le_map`; part (3), that the comparison maps on the twisting
sheaves are isomorphisms, is `Stacks.ProjBaseChange.isIso_twistMap_includeRight` in
`StacksFrontier/AlgebraicGeometry/Blowup/ProjBaseChangeTwist.lean`.

No `@[stacks 01NO]` attribute is attached: that tag is this statement in Situation 01NN, for the
values of a quasi-coherent graded `𝒪_S`-algebra on two affine opens `U ⊆ U'`, and the step from
this file's statement to it is the quasi-coherence input `𝒜(U) = 𝒪_S(U) ⊗_{𝒪_S(U')} 𝒜(U')` of
tag 01I9, which needs a notion of quasi-coherent graded `𝒪_S`-algebra that the library does not
have. For the graded algebra relevant to the blowup, the Rees algebra of an ideal sheaf `ℐ`, that
input is the graded isomorphism
`𝒪_S(U) ⊗_{𝒪_S(V)} reesAlgebra (ℐ V) ≅ reesAlgebra (ℐ U)`, which is not proved here either; the
ideal-theoretic half of it is Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`
applied to `ℐ ^ n`, and the missing half is flatness of `𝒪_S(U)` over `𝒪_S(V)`.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct HomogeneousIdeal
open HomogeneousLocalization Graded CommRingCat

universe u

namespace AlgebraicGeometry.Proj

/-! ### The chart of `Proj ℬ` over a chart of `Proj 𝒜` -/

section Chart

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- **The standard affine chart of `Proj ℬ` is the fibre product of the corresponding chart of
`Proj 𝒜` with `Proj ℬ`.** For `s : A` homogeneous of positive degree, the square formed by
`Spec (Away ℬ (f s)) ⟶ Spec (Away 𝒜 s)`, the two chart immersions and `Proj.map f` is cartesian.
This is the statement that `D₊(f s)` is the preimage of `D₊(s)` under `Proj.map f`, in the form
needed to check a statement about `Proj.map f` chart by chart. -/
theorem isPullback_awayι_map (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) {i : ℕ} (hi : 0 < i) (s : A)
    (hs : s ∈ 𝒜 i) :
    IsPullback (Spec.map (ofHom (Away.map f s))) (awayι ℬ (f s) (map_mem f hs) hi)
      (awayι 𝒜 s hs hi) (Proj.map f hf) :=
  IsOpenImmersion.isPullback _ _ _ _ (awayι_comp_map f hf hi s hs) <| by
    rw [opensRange_awayι, opensRange_awayι]
    exact map_preimage_basicOpen f hf s

end Chart

/-! ### `Proj` of an isomorphism of graded rings -/

section IsIso

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- If `f.comp g` is the identity then `Proj.map f` followed by `Proj.map g` is the identity. -/
private theorem map_comp_map_eq_id {f : 𝒜 →+*ᵍ ℬ} (hf : ℬ₊ ≤ 𝒜₊.map f) {g : ℬ →+*ᵍ 𝒜}
    (hg : 𝒜₊ ≤ ℬ₊.map g) (h : f.comp g = GradedRingHom.id ℬ) :
    Proj.map f hf ≫ Proj.map g hg = 𝟙 _ := by
  rw [← map_comp g f hg hf]
  exact (map_congr h _ (by simp)).trans map_id

/-- **A graded ring homomorphism with a two-sided graded inverse induces an isomorphism of
projective spectra.** Mathlib's `AlgebraicGeometry.Proj.map_comp` and
`AlgebraicGeometry.Proj.map_id` make `Proj.map` a functor, so this is functoriality applied to an
isomorphism; the inverse is given as data because Mathlib has no bundled isomorphism of graded
rings. -/
theorem isIso_map {f : 𝒜 →+*ᵍ ℬ} (hf : ℬ₊ ≤ 𝒜₊.map f) {g : ℬ →+*ᵍ 𝒜} (hg : 𝒜₊ ≤ ℬ₊.map g)
    (hfg : g.comp f = GradedRingHom.id 𝒜) (hgf : f.comp g = GradedRingHom.id ℬ) :
    IsIso (Proj.map f hf) := by
  exact ⟨Proj.map g hg, map_comp_map_eq_id hf hg hgf, map_comp_map_eq_id hg hf hfg⟩

end IsIso

/-! ### Ranges in a cartesian square along an open immersion -/

section OpensRange

/-- In a cartesian square whose bottom edge `iV` is an open immersion, the image of the left edge
`iU` is the preimage of the image of `iV`. This is the converse of the second hypothesis of
`AlgebraicGeometry.IsOpenImmersion.isPullback`, which builds a cartesian square out of exactly
that equality. The instance `IsOpenImmersion iU` is not a real hypothesis — it follows from the
square by `CategoryTheory.MorphismProperty.of_isPullback` — but it is needed to form
`Scheme.Hom.opensRange iU` in the statement. -/
theorem opensRange_eq_preimage_of_isPullback {X Y U V : Scheme.{u}} {g : X ⟶ Y} {f' : U ⟶ V}
    {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV] [IsOpenImmersion iU]
    (H : IsPullback f' iU iV g) : iU.opensRange = g ⁻¹ᵁ iV.opensRange := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤
  rwa [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.image_top_eq_opensRange] at h

end OpensRange

end AlgebraicGeometry.Proj

namespace Stacks.ProjBaseChange

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (S : Type u) [CommRing S] [Algebra R S]

/-! ### The base-change square over the degree-zero parts -/

/-- **The base-changed chart is the chart of `Proj A` pulled back along
`Stacks.ProjBaseChange.map`.** This is `AlgebraicGeometry.Proj.isPullback_awayι_map` for the
base-change homomorphism, written with the base change's own notation. -/
theorem isPullback_awayι_map {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) (hd : 0 < d) :
    IsPullback (Spec.map (ofHom (awayMap 𝒜 S a)))
      (Proj.awayι (grading 𝒜 S) ((1 : S) ⊗ₜ[R] a) (tmul_one_mem 𝒜 S ha) hd)
      (Proj.awayι 𝒜 a ha hd) (map 𝒜 S) :=
  Proj.isPullback_awayι_map (includeRight 𝒜 S) (irrelevant_le_map 𝒜 S) hd a ha

/-- The chart-local form of `Stacks.ProjBaseChange.isPullback_map_toSpecZero`, stated for the
categorical pullback of `Stacks.ProjBaseChange.map` along a chart immersion of `Proj A`. This is
the shape that `AlgebraicGeometry.Scheme.isPullback_of_openCover` asks for; it is obtained from
the chart-level base-change square by transporting along the identification of that categorical
pullback with the base-changed chart. -/
theorem isPullback_pullbackSnd_awayι {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) (hd : 0 < d) :
    IsPullback (pullback.snd (map 𝒜 S) (Proj.awayι 𝒜 a ha hd))
      (pullback.fst (map 𝒜 S) (Proj.awayι 𝒜 a ha hd) ≫ Proj.toSpecZero (grading 𝒜 S))
      (Proj.awayι 𝒜 a ha hd ≫ Proj.toSpecZero 𝒜)
      (Spec.map (ofHom (includeRight 𝒜 S).gradedZeroRingHom)) := by
  have hC := (isPullback_awayι_map 𝒜 S ha hd).flip
  refine (isPullback_Spec_awayMap_toZero 𝒜 S ha).of_iso hC.isoPullback (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    exact hC.isoPullback_hom_snd.symm
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, hC.isoPullback_hom_fst, Proj.awayι_toSpecZero]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rw [Proj.awayι_toSpecZero]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- **The base-change square of projective spectra over the degree-zero parts is cartesian.**
`Proj (S ⊗[R] A)` is the fibre product of `Proj A` with `Spec` of the degree-zero part of the
base-changed grading over `Spec (𝒜 0)`. -/
theorem isPullback_map_toSpecZero :
    IsPullback (map 𝒜 S) (Proj.toSpecZero (grading 𝒜 S)) (Proj.toSpecZero 𝒜)
      (Spec.map (ofHom (includeRight 𝒜 S).gradedZeroRingHom)) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Proj.affineOpenCover 𝒜).openCover fun j ↦ ?_
  obtain ⟨i, a⟩ := j
  exact isPullback_pullbackSnd_awayι 𝒜 S a.2 i.2

/-! ### The base-change square over the base rings -/

/-- **`Proj` commutes with base change.** For a graded `R`-algebra `A` and an `R`-algebra `S`, the
square formed by `Proj (S ⊗[R] A) ⟶ Proj A` and the two structure morphisms to `Spec S` and
`Spec R` is cartesian.

This is the special case of the fibre-product square of Stacks tag 01N2 part (2) in which `B` is
the tensor product `S ⊗[R] A` itself and `ψ` the canonical inclusion `A → S ⊗[R] A`. The tag
states it for any `B` carrying an identification `B = S ⊗[R] A`, which is
`Stacks.ProjBaseChange.isPullback_map_of_baseChange`; part (1) of the tag is
`Stacks.ProjBaseChange.irrelevant_le_map`. -/
@[ega "II 2.8.10" "fibre product square", ega "II 2.8.9" "partial"]
theorem isPullback_map_Spec :
    IsPullback (map 𝒜 S)
      (Proj.toSpecZero (grading 𝒜 S) ≫ Spec.map (ofHom (algebraMap S ↥(grading 𝒜 S 0))))
      (Proj.toSpecZero 𝒜 ≫ Spec.map (ofHom (algebraMap R ↥(𝒜 0))))
      (Spec.map (ofHom (algebraMap R S))) :=
  (isPullback_map_toSpecZero 𝒜 S).paste_vert (isPullback_Spec_gradedZeroRingHom 𝒜 S)

/-- The structure map `R → 𝒜 0` of the degree-zero part of a graded `R`-algebra is the
degree-zero projection of the structure map `R → A`: a scalar lands in degree zero, so projecting
it there changes nothing. -/
theorem projZeroRingHom'_comp_algebraMap :
    (GradedRing.projZeroRingHom' 𝒜).comp (algebraMap R A) = algebraMap R ↥(𝒜 0) :=
  RingHom.ext fun r ↦ by
    rw [RingHom.comp_apply,
      show algebraMap R A r = ((algebraMap R ↥(𝒜 0) r : ↥(𝒜 0)) : A) from rfl,
      GradedRing.projZeroRingHom'_apply_coe]

/-- `Stacks.ProjBaseChange.isPullback_map_Spec` with the structure morphism `Proj A ⟶ Spec R`
written through the degree-zero projection `A → 𝒜 0` rather than through the structure map
`R → 𝒜 0`. The two agree by `Stacks.ProjBaseChange.projZeroRingHom'_comp_algebraMap`; this is the
spelling in which the statement of tag 01N2 is phrased. -/
@[ega "II 2.8.9" "partial"]
theorem isPullback_map_Spec_projZeroRingHom :
    IsPullback (map 𝒜 S)
      (Proj.toSpecZero (grading 𝒜 S) ≫ Spec.map (ofHom (algebraMap S ↥(grading 𝒜 S 0))))
      (Proj.toSpecZero 𝒜 ≫
        Spec.map (ofHom ((GradedRing.projZeroRingHom' 𝒜).comp (algebraMap R A))))
      (Spec.map (ofHom (algebraMap R S))) :=
  projZeroRingHom'_comp_algebraMap 𝒜 ▸ isPullback_map_Spec 𝒜 S

/-! ### The open-immersion case -/

section OpenImmersion

variable [IsOpenImmersion (Spec.map (ofHom (algebraMap R S)))]

/-- **The base change of `Proj` along an open immersion of affine bases is an open immersion.**
If `Spec S ⟶ Spec R` is an open immersion — for instance if `S` is a localization of `R` at one
element, or more generally if `Spec S` is an affine open of `Spec R` — then so is
`Proj (S ⊗[R] A) ⟶ Proj A`. -/
instance isOpenImmersion_map : IsOpenImmersion (map 𝒜 S) :=
  MorphismProperty.of_isPullback (isPullback_map_Spec 𝒜 S).flip inferInstance

/-- **The image of the base change of `Proj` along an open immersion of affine bases.** The open
subscheme `Proj (S ⊗[R] A)` of `Proj A` is the preimage of the open subscheme `Spec S` of
`Spec R` under the structure morphism `Proj A ⟶ Spec R`. Together with
`Stacks.ProjBaseChange.isOpenImmersion_map` this is the form of the base-change statement that
`Stacks.RelativeProj.Data` asks for. -/
theorem opensRange_map :
    (map 𝒜 S).opensRange =
      (Proj.toSpecZero 𝒜 ≫ Spec.map (ofHom (algebraMap R ↥(𝒜 0)))) ⁻¹ᵁ
        (Spec.map (ofHom (algebraMap R S))).opensRange :=
  Proj.opensRange_eq_preimage_of_isPullback (isPullback_map_Spec 𝒜 S).flip

end OpenImmersion

/-! ### The form `Stacks.RelativeProj.Data` asks for -/

section Transport

variable {B τ : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ}
  [GradedRing ℬ] {f : 𝒜 →+*ᵍ ℬ} (hf : ℬ₊ ≤ 𝒜₊.map f) {e : grading 𝒜 S →+*ᵍ ℬ}
  (he : ℬ₊ ≤ (grading 𝒜 S)₊.map e) {e' : ℬ →+*ᵍ grading 𝒜 S}
  (he' : (grading 𝒜 S)₊ ≤ ℬ₊.map e')
  (hee' : e'.comp e = GradedRingHom.id (grading 𝒜 S)) (he'e : e.comp e' = GradedRingHom.id ℬ)
  (hfe : f = e.comp (includeRight 𝒜 S))

include hfe in
/-- A graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` that factors as the base change `𝒜 → S ⊗[R] 𝒜`
followed by a graded isomorphism `S ⊗[R] 𝒜 ≅ ℬ` induces on projective spectra the base-change
morphism of `Stacks.ProjBaseChange.map` preceded by an isomorphism. -/
theorem map_eq_comp_of_baseChange : Proj.map f hf = Proj.map e he ≫ map 𝒜 S := by
  refine (Proj.map_congr hfe hf
    (irrelevant_le_map_comp (irrelevant_le_map 𝒜 S) he)).trans ?_
  exact Proj.map_comp (includeRight 𝒜 S) e (irrelevant_le_map 𝒜 S) he

include he he' hee' he'e hfe in
/-- **Stacks Project, Tag 01N2, part (2).** If `ℬ` is isomorphic, as a graded ring, to the base
change `S ⊗[R] 𝒜`, compatibly with `f` — the tag's identification `B = R' ⊗_R A` — then the
square formed by `Proj ℬ ⟶ Proj 𝒜` and the structure morphisms to `Spec S` and `Spec R` is
cartesian.
The structure morphism of `Proj ℬ` is written through the isomorphism, since nothing identifies
the degree-zero part of `ℬ` with `S` intrinsically. -/
theorem isPullback_map_of_baseChange :
    IsPullback (Proj.map f hf)
      (Proj.map e he ≫ Proj.toSpecZero (grading 𝒜 S) ≫
        Spec.map (ofHom (algebraMap S ↥(grading 𝒜 S 0))))
      (Proj.toSpecZero 𝒜 ≫ Spec.map (ofHom (algebraMap R ↥(𝒜 0))))
      (Spec.map (ofHom (algebraMap R S))) := by
  have hiso := Proj.isIso_map he he' hee' he'e
  have hcomp := map_eq_comp_of_baseChange 𝒜 S hf he hfe
  refine (isPullback_map_Spec 𝒜 S).of_iso (asIso (Proj.map e he)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [hcomp]
  · simp
  · simp
  · simp

variable [IsOpenImmersion (Spec.map (ofHom (algebraMap R S)))]

include he he' hee' he'e hfe in
/-- **The first of the two hypotheses `Stacks.RelativeProj.Data` asks for.** If `ℬ` is a graded
ring isomorphic to the base change `S ⊗[R] 𝒜` under the given homomorphism `f`, and
`Spec S ⟶ Spec R` is an open immersion, then `Proj ℬ ⟶ Proj 𝒜` is an open immersion. -/
theorem isOpenImmersion_map_of_baseChange : IsOpenImmersion (Proj.map f hf) :=
  MorphismProperty.of_isPullback
    (isPullback_map_of_baseChange 𝒜 S hf he he' hee' he'e hfe).flip inferInstance

include he he' hee' he'e hfe in
/-- **The second of the two hypotheses `Stacks.RelativeProj.Data` asks for.** With the
hypotheses of `Stacks.ProjBaseChange.isOpenImmersion_map_of_baseChange`, the open subscheme
`Proj ℬ` of `Proj 𝒜` is the preimage of the open subscheme `Spec S` of `Spec R` under the
structure morphism `Proj 𝒜 ⟶ Spec R`. The instance `IsOpenImmersion (Proj.map f hf)` is not a
real hypothesis — it is `Stacks.ProjBaseChange.isOpenImmersion_map_of_baseChange` — but it is
needed to form `Scheme.Hom.opensRange` in the statement. -/
theorem opensRange_map_of_baseChange [IsOpenImmersion (Proj.map f hf)] :
    (Proj.map f hf).opensRange =
      (Proj.toSpecZero 𝒜 ≫ Spec.map (ofHom (algebraMap R ↥(𝒜 0)))) ⁻¹ᵁ
        (Spec.map (ofHom (algebraMap R S))).opensRange :=
  Proj.opensRange_eq_preimage_of_isPullback
    (isPullback_map_of_baseChange 𝒜 S hf he he' hee' he'e hfe).flip

end Transport

end Stacks.ProjBaseChange

end
