module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.RestrictIso
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedComparison

/-!
# Shrinking an affine chart until the reduced complement is flat, and finite, underneath

Let `U₀` be an open of a scheme `T`, let `W` be an open of `T` and let `ξ` be a point of `W`
outside `U₀` whose closure contains all of `(W : Set T) ∩ (U₀ : Set T)ᶜ`. The *reduced
complement* in a chart `W'` is the reduced induced scheme on the locally closed subset
`(W' : Set T) ∩ (U₀ : Set T)ᶜ`. This file shows that the chart can be shrunk around `ξ` — to an
affine open `W' ≤ W` still containing `ξ` — so that a prescribed morphism becomes flat, or
finite, over the reduced complement of the smaller chart.

Both halves rest on one geometric fact, which is the content of this file and which no existing
lemma supplied: **cutting a locally closed subset down by an open set of the ambient scheme is an
open immersion on reduced induced schemes.** That is, for `Z₁ = Z₀ ∩ O` with `O` open, the
comparison morphism
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedComparison` from the
reduced induced scheme on `Z₁` to the one on `Z₀` is an open immersion, identifying `(Z₀ ∩ O)_red`
with the part of `(Z₀)_red` lying over `O`. Without that identification a property proved over an
open of `(Z₀)_red` — which is what generic flatness and generic finiteness produce — says nothing
about the reduced complement of a shrunken chart, which is what the Noetherian induction of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) needs.

## Main results

* `AlgebraicGeometry.isOpenImmersion_reducedInducedComparison_of_eq_inter`: **the comparison
  morphism of reduced induced schemes along `Z₀ ∩ O ⊆ Z₀` is an open immersion**, for `O` an open
  of the ambient scheme.
* `AlgebraicGeometry.pullback_snd_reducedInducedComparison_of_le` and
  `AlgebraicGeometry.pullback_snd_reducedInducedInclusion_of_le`: a property local at the target
  that holds over an open of `(Z₀)_red` containing the image of the comparison morphism holds
  after base change to `(Z₀ ∩ O)_red`, for a morphism to `(Z₀)_red` and for one to the ambient
  scheme respectively.
* `AlgebraicGeometry.exists_isAffineOpen_flat_pullback_snd_reducedInducedInclusion`: **the chart
  can be shrunk until a finite morphism to the ambient scheme becomes flat over the reduced
  complement** — the flatness half of step 4 of the induction.
* `AlgebraicGeometry.exists_isAffineOpen_isFinite_pullback_snd_reducedInducedComparison`: **the
  chart can be shrunk until an étale, quasi-compact, quasi-separated morphism over the reduced
  complement becomes finite** — the finiteness half of the same step.

## Implementation notes

The statement of the flatness half is phrased with
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedInclusion`, the canonical
morphism of the reduced induced scheme on a locally closed subset into the ambient scheme, and
not with a vanishing ideal sheaf on `T` itself: `(W' : Set T) ∩ (U₀ : Set T)ᶜ` is closed in the
chart `W'` and not in `T`, so it is not the support of an ideal sheaf on `T`. Indeed asking for a
chart in which it *were* closed in `T` is impossible as soon as the flat locus is a proper open
of the complement — on `T` the affine plane with `U₀` the complement of a line, an open set meets
the line in a set closed in `T` only if it contains the whole line. The canonical morphism is
nevertheless a vanishing-ideal subscheme inclusion followed by an open immersion, by definition of
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedInclusion`, so nothing of
the closed-subscheme structure is lost.

The open immersion statement is proved from the universal property of the reduced induced scheme
rather than by comparing ideal sheaves. The part of `(Z₀)_red` over `O` is reduced and has image
exactly `Z₀ ∩ O`, so it factors through `(Z₀ ∩ O)_red`; conversely the comparison morphism has
image inside that open part, so it factors through it; the two factorizations are mutually inverse
because the canonical morphisms to the ambient scheme are monomorphisms.

Generic flatness is used in the module-free form
`AlgebraicGeometry.exists_dense_open_flat_finitePresentation_structureSheaf` of Tag 052B; only
reducedness of the base is needed, which the reduced induced scheme has by construction, so
irreducibility of the complement is not a hypothesis of the flatness half. The finiteness half
does need it, since Tag 02NW is a statement about a generic point of an irreducible component.

## References

* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

/-! ### Two generalities about restriction to an open of the target -/

/-- A property local at the target which holds after restriction to an open of the target holds
after restriction to any smaller open. -/
theorem morphismRestrict_of_le (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) {V Ω : Y.Opens} (hle : V ≤ Ω) (h : P (f ∣_ Ω)) :
    P (f ∣_ V) :=
  (P.arrow_mk_iso_iff (Stacks.RestrictIso.morphismRestrictRestrictLE f hle)).mp
    (IsZariskiLocalAtTarget.restrict h _)

/-- Transport of a property of a base-changed morphism along an equality of the morphism being
base changed along. -/
theorem pullback_snd_congr (P : MorphismProperty Scheme.{u}) {A B C : Scheme.{u}} (g : A ⟶ C)
    {q q' : B ⟶ C} (h : q = q') (hq : P (pullback.snd g q)) : P (pullback.snd g q') := by
  subst h
  exact hq

/-- The intersection of an open set with the complement of an open set is locally closed. -/
theorem isLocallyClosed_inter_compl {X : Scheme.{u}} (A B : X.Opens) :
    IsLocallyClosed ((A : Set X) ∩ (B : Set X)ᶜ) :=
  ⟨(A : Set X), (B : Set X)ᶜ, A.isOpen, B.isOpen.isClosed_compl, rfl⟩

/-! ### Cutting a locally closed subset down by an open set of the ambient scheme -/

/-- **The comparison morphism of reduced induced schemes along the inclusion of a locally closed
subset cut down by an open set of the ambient scheme is an open immersion.** For `Z₁ = Z₀ ∩ O`
with `O` an open of `X`, this identifies the reduced induced scheme on `Z₁` with the part of the
reduced induced scheme on `Z₀` lying over `O`.

The open part is reduced and its image in `X` is exactly `Z₁`, so the universal property
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.reducedInducedLift` factors it through
the reduced induced scheme on `Z₁`; conversely the comparison morphism has image inside the open
part by
`Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.range_reducedInducedComparison`, so it
factors through it. The canonical morphisms to `X` are monomorphisms, so the two factorizations
are mutually inverse and the comparison morphism is an isomorphism followed by an open
immersion. -/
theorem isOpenImmersion_reducedInducedComparison_of_eq_inter {X : Scheme.{u}} (Z₀ Z₁ : Set X)
    (hZ₀ : IsLocallyClosed Z₀) (hZ₁ : IsLocallyClosed Z₁) (O : X.Opens)
    (hZ₁eq : Z₁ = Z₀ ∩ (O : Set X)) (hsub : Z₁ ⊆ Z₀) :
    IsOpenImmersion (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub) := by
  have hrangeP : Set.range ((reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι ≫
      reducedInducedInclusion Z₀ hZ₀) ⊆ Z₁ := by
    rintro y ⟨x, rfl⟩
    rw [hZ₁eq, Scheme.Hom.comp_apply]
    exact ⟨(range_inclusion Z₀ hZ₀).le ⟨_, rfl⟩, x.2⟩
  have hrangec : Set.range (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub) ⊆
      Set.range (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι := by
    rw [range_reducedInducedComparison, Scheme.Opens.range_ι]
    exact fun y hy ↦ (hZ₁eq ▸ hy : reducedInducedInclusion Z₀ hZ₀ y ∈ Z₀ ∩ (O : Set X)).2
  let a : (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).toScheme ⟶ reducedInducedScheme Z₁ hZ₁ :=
    reducedInducedLift Z₁ hZ₁ _ hrangeP
  have ha : a ≫ reducedInducedInclusion Z₁ hZ₁ =
      (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι ≫ reducedInducedInclusion Z₀ hZ₀ :=
    reducedInducedLift_inclusion Z₁ hZ₁ _ hrangeP
  let b : reducedInducedScheme Z₁ hZ₁ ⟶ (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).toScheme :=
    IsOpenImmersion.lift _ _ hrangec
  have hb : b ≫ (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι =
      reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub :=
    IsOpenImmersion.lift_fac _ _ hrangec
  have hci : reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub ≫ reducedInducedInclusion Z₀ hZ₀ =
      reducedInducedInclusion Z₁ hZ₁ :=
    reducedInducedComparison_inclusion Z₁ Z₀ hZ₁ hZ₀ hsub
  have hba : b ≫ a = 𝟙 _ := (cancel_mono (reducedInducedInclusion Z₁ hZ₁)).mp (by
    calc (b ≫ a) ≫ reducedInducedInclusion Z₁ hZ₁
        = b ≫ (a ≫ reducedInducedInclusion Z₁ hZ₁) := Category.assoc _ _ _
      _ = b ≫ ((reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι ≫
            reducedInducedInclusion Z₀ hZ₀) := congrArg (b ≫ ·) ha
      _ = (b ≫ (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι) ≫
            reducedInducedInclusion Z₀ hZ₀ := (Category.assoc _ _ _).symm
      _ = reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub ≫
            reducedInducedInclusion Z₀ hZ₀ := congrArg (· ≫ reducedInducedInclusion Z₀ hZ₀) hb
      _ = reducedInducedInclusion Z₁ hZ₁ := hci
      _ = 𝟙 _ ≫ reducedInducedInclusion Z₁ hZ₁ := (Category.id_comp _).symm)
  have hab : a ≫ b = 𝟙 _ := (cancel_mono ((reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι ≫
      reducedInducedInclusion Z₀ hZ₀)).mp (by
    calc (a ≫ b) ≫ ((reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι ≫
            reducedInducedInclusion Z₀ hZ₀)
        = a ≫ ((b ≫ (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι) ≫
            reducedInducedInclusion Z₀ hZ₀) := by
          simp only [Category.assoc]
      _ = a ≫ (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub ≫
            reducedInducedInclusion Z₀ hZ₀) :=
          congrArg (a ≫ ·) (congrArg (· ≫ reducedInducedInclusion Z₀ hZ₀) hb)
      _ = a ≫ reducedInducedInclusion Z₁ hZ₁ := congrArg (a ≫ ·) hci
      _ = (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι ≫ reducedInducedInclusion Z₀ hZ₀ := ha
      _ = 𝟙 _ ≫ ((reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O).ι ≫
            reducedInducedInclusion Z₀ hZ₀) := (Category.id_comp _).symm)
  have : IsIso b := ⟨a, hba, hab⟩
  rw [← hb]
  infer_instance

/-! ### Transporting a property along the comparison morphism -/

/-- A property local at the target that holds for a morphism to the reduced induced scheme on `Z₀`
restricted over an open containing the image of the comparison morphism holds for its base change
along the comparison morphism. -/
theorem pullback_snd_reducedInducedComparison_of_le (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {X : Scheme.{u}} (Z₀ Z₁ : Set X) (hZ₀ : IsLocallyClosed Z₀)
    (hZ₁ : IsLocallyClosed Z₁) (hsub : Z₁ ⊆ Z₀)
    [IsOpenImmersion (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub)] {E : Scheme.{u}}
    (h : E ⟶ reducedInducedScheme Z₀ hZ₀) (Ω : (reducedInducedScheme Z₀ hZ₀).Opens)
    (hΩ : (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub).opensRange ≤ Ω) (hP : P (h ∣_ Ω)) :
    P (pullback.snd h (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub)) :=
  (P.arrow_mk_iso_iff (morphismRestrictOpensRange h _)).mp
    (morphismRestrict_of_le P h hΩ hP)

/-- A property local at the target that holds for the base change to the reduced induced scheme on
`Z₀` of a morphism to the ambient scheme, restricted over an open containing the image of the
comparison morphism, holds for the base change of that morphism to the reduced induced scheme on
`Z₁`.

The base change to `Z₁` is the base change along the comparison morphism of the base change to
`Z₀`, by `CategoryTheory.Limits.pullbackLeftPullbackSndIso`. -/
theorem pullback_snd_reducedInducedInclusion_of_le (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {X Y : Scheme.{u}} (g : Y ⟶ X) (Z₀ Z₁ : Set X)
    (hZ₀ : IsLocallyClosed Z₀) (hZ₁ : IsLocallyClosed Z₁) (hsub : Z₁ ⊆ Z₀)
    [IsOpenImmersion (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub)]
    (Ω : (reducedInducedScheme Z₀ hZ₀).Opens)
    (hΩ : (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub).opensRange ≤ Ω)
    (hP : P (pullback.snd g (reducedInducedInclusion Z₀ hZ₀) ∣_ Ω)) :
    P (pullback.snd g (reducedInducedInclusion Z₁ hZ₁)) := by
  refine pullback_snd_congr P g (reducedInducedComparison_inclusion Z₁ Z₀ hZ₁ hZ₀ hsub) ?_
  have e : Arrow.mk (pullback.snd (pullback.snd g (reducedInducedInclusion Z₀ hZ₀))
        (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub)) ≅
      Arrow.mk (pullback.snd g (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub ≫
        reducedInducedInclusion Z₀ hZ₀)) :=
    Arrow.isoMk (pullbackLeftPullbackSndIso g (reducedInducedInclusion Z₀ hZ₀)
      (reducedInducedComparison Z₁ Z₀ hZ₁ hZ₀ hsub)) (Iso.refl _) (by simp)
  refine (P.arrow_mk_iso_iff e).mp ?_
  exact pullback_snd_reducedInducedComparison_of_le P Z₀ Z₁ hZ₀ hZ₁ hsub _ Ω hΩ hP

/-! ### Reading an open of the reduced induced scheme off the ambient scheme -/

/-- A nonempty open of the reduced induced scheme on a locally closed subset contained in the
closure of a point `ξ` is the preimage of an open of the ambient scheme through `ξ`.

The canonical morphism is an embedding, so the open is the preimage of some ambient open; that
ambient open meets the subset, hence meets the closure of `ξ`, hence contains `ξ`. -/
theorem exists_isOpen_preimage_eq_of_subset_closure {X : Scheme.{u}} (Z₀ : Set X)
    (hZ₀ : IsLocallyClosed Z₀) {ξ : X} (hclos : Z₀ ⊆ closure {ξ})
    (V : (reducedInducedScheme Z₀ hZ₀).Opens)
    (hV : (V : Set (reducedInducedScheme Z₀ hZ₀)).Nonempty) :
    ∃ O : X.Opens, ξ ∈ O ∧ reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O = V := by
  obtain ⟨Oset, hOopen, hOeq⟩ :=
    (isEmbedding_reducedInducedInclusion Z₀ hZ₀).toIsInducing.isOpen_iff.mp V.isOpen
  refine ⟨⟨Oset, hOopen⟩, ?_, TopologicalSpace.Opens.ext hOeq⟩
  obtain ⟨x, hx⟩ := hV
  have h1 : reducedInducedInclusion Z₀ hZ₀ x ∈ Oset := by rw [← hOeq] at hx; exact hx
  have h2 : reducedInducedInclusion Z₀ hZ₀ x ∈ Z₀ := (range_inclusion Z₀ hZ₀).le ⟨x, rfl⟩
  obtain ⟨z, hzO, hz⟩ := mem_closure_iff.mp (hclos h2) Oset hOopen h1
  exact (Set.mem_singleton_iff.mp hz) ▸ hzO

/-! ### The flatness half of step 4 -/

/-- Generic flatness over the reduced complement, with the dense open read off the ambient scheme:
for `g` finite and `Z₀` a locally closed subset contained in the closure of one of its points
`ξ`, there is an open `O` of the ambient scheme through `ξ` over which the base change of `g` to
the reduced induced scheme on `Z₀` is flat. -/
theorem exists_isOpen_flat_morphismRestrict_pullback_snd_reducedInducedInclusion
    {X Y : Scheme.{u}} (g : Y ⟶ X) [IsFinite g] (Z₀ : Set X) (hZ₀ : IsLocallyClosed Z₀) {ξ : X}
    (hξ : ξ ∈ Z₀) (hclos : Z₀ ⊆ closure {ξ}) :
    ∃ O : X.Opens, ξ ∈ O ∧
      Flat (pullback.snd g (reducedInducedInclusion Z₀ hZ₀) ∣_
        (reducedInducedInclusion Z₀ hZ₀ ⁻¹ᵁ O)) := by
  have hne : Nonempty (reducedInducedScheme Z₀ hZ₀) := by
    obtain ⟨x, -⟩ := (range_inclusion Z₀ hZ₀).ge hξ
    exact ⟨x⟩
  obtain ⟨V, hVdense, hVflat, -⟩ := exists_dense_open_flat_finitePresentation_structureSheaf
    (pullback.snd g (reducedInducedInclusion Z₀ hZ₀))
  obtain ⟨O, hξO, hOV⟩ :=
    exists_isOpen_preimage_eq_of_subset_closure Z₀ hZ₀ hclos V hVdense.nonempty
  refine ⟨O, hξO, ?_⟩
  rw [hOV, ← Scheme.Hom.resLE_eq_morphismRestrict]
  exact hVflat

/-- **The affine chart can be shrunk around `ξ` until a finite morphism to the ambient scheme
becomes flat over the reduced complement.** This is the flatness half of step 4 of the Noetherian
induction of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP): over an affine open
`W'` of `T` through `ξ` and contained in `W`, the base change of the finite surjection `g` to the
reduced induced scheme on `(W' : Set T) ∩ (U₀ : Set T)ᶜ` is flat.

Generic flatness, Tag 052B, makes the base change flat over a dense open of the reduced induced
scheme on `(W : Set T) ∩ (U₀ : Set T)ᶜ`; that open is the preimage of an ambient open through
`ξ`, and an affine open `W'` of `T` through `ξ` inside it cuts the complement down to a piece
whose reduced induced scheme sits inside the flat locus as an open subscheme, by
`AlgebraicGeometry.isOpenImmersion_reducedInducedComparison_of_eq_inter`. -/
theorem exists_isAffineOpen_flat_pullback_snd_reducedInducedInclusion {T Y : Scheme.{u}}
    (g : Y ⟶ T) [IsFinite g] (U₀ W : T.Opens) (ξ : T) (hξW : ξ ∈ W) (hξU₀ : ξ ∉ U₀)
    (hclos : (W : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ}) :
    ∃ (W' : T.Opens) (_ : (W' : Set T) ⊆ (W : Set T)), ξ ∈ W' ∧ IsAffineOpen W' ∧
      Flat (pullback.snd g (reducedInducedInclusion ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
        (isLocallyClosed_inter_compl W' U₀))) := by
  obtain ⟨O, hξO, hflat⟩ := exists_isOpen_flat_morphismRestrict_pullback_snd_reducedInducedInclusion
    g ((W : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W U₀) ⟨hξW, hξU₀⟩ hclos
  obtain ⟨-, ⟨W', hW'aff, rfl⟩, hξW', hW'sub⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (show ξ ∈ (W : Set T) ∩ (O : Set T) from ⟨hξW, hξO⟩) (W.isOpen.inter O.isOpen)
  have hW'W : (W' : Set T) ⊆ (W : Set T) := fun y hy ↦ (hW'sub hy).1
  have hW'O : (W' : Set T) ⊆ (O : Set T) := fun y hy ↦ (hW'sub hy).2
  have hsub : (W' : Set T) ∩ (U₀ : Set T)ᶜ ⊆ (W : Set T) ∩ (U₀ : Set T)ᶜ :=
    fun y hy ↦ ⟨hW'W hy.1, hy.2⟩
  have hinter : (W' : Set T) ∩ (U₀ : Set T)ᶜ =
      ((W : Set T) ∩ (U₀ : Set T)ᶜ) ∩ (W' : Set T) :=
    Set.Subset.antisymm (fun y hy ↦ ⟨⟨hW'W hy.1, hy.2⟩, hy.1⟩) fun y hy ↦ ⟨hy.2, hy.1.2⟩
  have hOI : IsOpenImmersion (reducedInducedComparison ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
      ((W : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W' U₀)
      (isLocallyClosed_inter_compl W U₀) hsub) :=
    isOpenImmersion_reducedInducedComparison_of_eq_inter _ _ (isLocallyClosed_inter_compl W U₀)
      (isLocallyClosed_inter_compl W' U₀) W' hinter hsub
  have hzl : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.Flat)
  refine ⟨W', hW'W, hξW', hW'aff, ?_⟩
  refine pullback_snd_reducedInducedInclusion_of_le (@Flat) g _ _
    (isLocallyClosed_inter_compl W U₀) (isLocallyClosed_inter_compl W' U₀) hsub _ ?_ hflat
  intro y hy
  have hmem : reducedInducedInclusion ((W : Set T) ∩ (U₀ : Set T)ᶜ)
      (isLocallyClosed_inter_compl W U₀) y ∈ (W' : Set T) ∩ (U₀ : Set T)ᶜ :=
    (range_reducedInducedComparison ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
      ((W : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W' U₀)
      (isLocallyClosed_inter_compl W U₀) hsub).le hy
  exact hW'O hmem.1

/-! ### The finiteness half of step 4 -/

/-- An étale, quasi-compact, quasi-separated morphism is finite over an affine open neighbourhood
of a generic point of an irreducible component of its target.

The fibre over such a point is finite because the morphism is étale and quasi-compact,
`AlgebraicGeometry.finite_preimage_singleton_of_etale_of_quasiCompact`, and Tag 02NW turns a
finite fibre over a generic point into finiteness over an affine neighbourhood. -/
theorem exists_isAffineOpen_isFinite_morphismRestrict_of_etale {E S : Scheme.{u}} (h : E ⟶ S)
    [Etale h] [QuasiCompact h] [QuasiSeparated h] (η : S) (hη : η ∈ genericPoints S) :
    ∃ V : S.Opens, η ∈ V ∧ IsAffineOpen V ∧ IsFinite (h ∣_ V) := by
  have : LocallyOfFiniteType h := inferInstance
  obtain ⟨V, hηV, hfin⟩ :=
    (finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict h η hη).mp
      (finite_preimage_singleton_of_etale_of_quasiCompact h η)
  exact ⟨V.1, hηV, V.2, hfin⟩

/-- **The affine chart can be shrunk around `ξ` until an étale, quasi-compact, quasi-separated
morphism over the reduced complement becomes finite.** This is the finiteness half of step 4 of
the Noetherian induction of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP): over an
affine open `W'` of `T` through `ξ` and contained in `W`, the base change of `h` along the
comparison morphism to the reduced induced scheme on `(W' : Set T) ∩ (U₀ : Set T)ᶜ` is finite.

The complement is irreducible with `ξ` as its generic point, so the reduced induced scheme on it
is irreducible and `h` is finite over an affine open neighbourhood of its generic point by
`AlgebraicGeometry.exists_isAffineOpen_isFinite_morphismRestrict_of_etale`; that neighbourhood is
the preimage of an ambient open through `ξ`, and an affine open `W'` of `T` through `ξ` inside it
cuts the complement down to a piece sitting inside it as an open subscheme. -/
theorem exists_isAffineOpen_isFinite_pullback_snd_reducedInducedComparison {T : Scheme.{u}}
    (U₀ W : T.Opens) (ξ : T) (hξW : ξ ∈ W)
    (hirr : IsIrreducible ((W : Set T) ∩ (U₀ : Set T)ᶜ))
    (hclos : (W : Set T) ∩ (U₀ : Set T)ᶜ ⊆ closure {ξ}) {E : Scheme.{u}}
    (h : E ⟶ reducedInducedScheme ((W : Set T) ∩ (U₀ : Set T)ᶜ)
      (isLocallyClosed_inter_compl W U₀))
    [Etale h] [QuasiCompact h] [QuasiSeparated h] :
    ∃ (W' : T.Opens) (hW'W : (W' : Set T) ⊆ (W : Set T)), ξ ∈ W' ∧ IsAffineOpen W' ∧
      IsFinite (pullback.snd h (reducedInducedComparison ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
        ((W : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W' U₀)
        (isLocallyClosed_inter_compl W U₀) (Set.inter_subset_inter_left _ hW'W))) := by
  have hirrsp : IrreducibleSpace (reducedInducedScheme ((W : Set T) ∩ (U₀ : Set T)ᶜ)
      (isLocallyClosed_inter_compl W U₀)) :=
    irreducibleSpace_reducedInducedScheme _ (isLocallyClosed_inter_compl W U₀) hirr
  have hη : genericPoint (reducedInducedScheme ((W : Set T) ∩ (U₀ : Set T)ᶜ)
      (isLocallyClosed_inter_compl W U₀)) ∈
      genericPoints (reducedInducedScheme ((W : Set T) ∩ (U₀ : Set T)ᶜ)
        (isLocallyClosed_inter_compl W U₀)) := by
    rw [genericPoints_eq_singleton]
    exact rfl
  obtain ⟨V, hηV, -, hVfin⟩ := exists_isAffineOpen_isFinite_morphismRestrict_of_etale h _ hη
  obtain ⟨O, hξO, hOV⟩ := exists_isOpen_preimage_eq_of_subset_closure
    ((W : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W U₀) hclos V ⟨_, hηV⟩
  obtain ⟨-, ⟨W', hW'aff, rfl⟩, hξW', hW'sub⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (show ξ ∈ (W : Set T) ∩ (O : Set T) from ⟨hξW, hξO⟩) (W.isOpen.inter O.isOpen)
  have hW'W : (W' : Set T) ⊆ (W : Set T) := fun y hy ↦ (hW'sub hy).1
  have hW'O : (W' : Set T) ⊆ (O : Set T) := fun y hy ↦ (hW'sub hy).2
  have hsub : (W' : Set T) ∩ (U₀ : Set T)ᶜ ⊆ (W : Set T) ∩ (U₀ : Set T)ᶜ :=
    Set.inter_subset_inter_left _ hW'W
  have hinter : (W' : Set T) ∩ (U₀ : Set T)ᶜ =
      ((W : Set T) ∩ (U₀ : Set T)ᶜ) ∩ (W' : Set T) :=
    Set.Subset.antisymm (fun y hy ↦ ⟨⟨hW'W hy.1, hy.2⟩, hy.1⟩) fun y hy ↦ ⟨hy.2, hy.1.2⟩
  have hOI : IsOpenImmersion (reducedInducedComparison ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
      ((W : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W' U₀)
      (isLocallyClosed_inter_compl W U₀) hsub) :=
    isOpenImmersion_reducedInducedComparison_of_eq_inter _ _ (isLocallyClosed_inter_compl W U₀)
      (isLocallyClosed_inter_compl W' U₀) W' hinter hsub
  have hzl : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) := by
    have hint : IsZariskiLocalAtTarget (@IsIntegralHom : MorphismProperty Scheme.{u}) :=
      @HasAffineProperty.instIsZariskiLocalAtTarget _ _ IsIntegralHom.hasAffineProperty
    have hft : IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtTarget _ (Q := RingHom.FiniteType)
    rw [IsFinite.eq_inf]
    exact @MorphismProperty.IsLocalAtTarget.inf _ _ Scheme.zariskiPrecoverage _ _ hint hft
  refine ⟨W', hW'W, hξW', hW'aff, ?_⟩
  refine pullback_snd_reducedInducedComparison_of_le (@IsFinite) _ _
    (isLocallyClosed_inter_compl W U₀) (isLocallyClosed_inter_compl W' U₀) hsub h V ?_ hVfin
  rw [← hOV]
  intro y hy
  have hmem : reducedInducedInclusion ((W : Set T) ∩ (U₀ : Set T)ᶜ)
      (isLocallyClosed_inter_compl W U₀) y ∈ (W' : Set T) ∩ (U₀ : Set T)ᶜ :=
    (range_reducedInducedComparison ((W' : Set T) ∩ (U₀ : Set T)ᶜ)
      ((W : Set T) ∩ (U₀ : Set T)ᶜ) (isLocallyClosed_inter_compl W' U₀)
      (isLocallyClosed_inter_compl W U₀) hsub).le hy
  exact hW'O hmem.1

end AlgebraicGeometry

end
