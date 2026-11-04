module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The dimension formula for a Cohen-Macaulay morphism

For a Cohen-Macaulay morphism locally of finite type between locally Noetherian schemes, the
dimension of the source at a point is the dimension of the target at its image plus the dimension
of the fibre at that point:
`dim_x(X) = dim_{f x}(Y) + dim_x(X_{f x})`.

The proof is the source's. A Cohen-Macaulay morphism is flat with Cohen-Macaulay fibres, so its
source decomposes into open pieces of constant relative dimension (Tag 02NM); on the piece
through `x` the fibre dimension is a fixed `d`, and the formula reduces to the statement that a
flat morphism of relative dimension `d` raises the local dimension by exactly `d`. That in turn
reduces, after shrinking to open neighbourhoods realizing both local dimensions and using that a
flat morphism locally of finite presentation is open, to the global statement for a surjective
morphism, where both sides are suprema of Krull dimensions of local rings (Tag 04MU) and the
comparison at each point is the dimension formula for a flat local homomorphism of Noetherian
local rings.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_eq_add_of_relativeDimension` is
  **Stacks Tag 0AFE**: a flat morphism locally of finite type of relative dimension `d` between
  locally Noetherian schemes raises the local dimension by `d`.
* `AlgebraicGeometry.topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber` is
  **Stacks Tag 0AFG**.

## Implementation notes

Cohen-Macaulayness of a morphism is `AlgebraicGeometry.Scheme.Hom.IsCohenMacaulay` of Tag 045R,
which takes as an argument a proof that every fibre is locally Noetherian; for a morphism locally
of finite type that proof is available, and the statement below takes it as an explicit argument
so that the hypothesis reads as the source's.

The dimension formula for a flat local homomorphism is main's
`ringKrullDim_eq_add_ringKrullDim_closedFibre`, and the closed fibre of the homomorphism of
stalks is identified with the stalk of the scheme-theoretic fibre by
`AlgebraicGeometry.quotientStalkEquivFiberStalk`.

## References

* [Stacks Project, Tag 0AFE](https://stacks.math.columbia.edu/tag/0AFE)
* [Stacks Project, Tag 0AFG](https://stacks.math.columbia.edu/tag/0AFG)
* [Stacks Project, Tag 045R](https://stacks.math.columbia.edu/tag/045R)
* [Stacks Project, Tag 045S](https://stacks.math.columbia.edu/tag/045S)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Adding a fixed value to a supremum of values that are not `⊥` may be done termwise.

No nonemptiness assumption on the index type is needed: over an empty index type both sides are
the supremum of the empty family, namely `⊥`. -/
private lemma add_iSup_of_ne_bot {ι : Type*} (a : WithBot ℕ∞) (g : ι → WithBot ℕ∞)
    (hg : ∀ i, g i ≠ ⊥) : a + ⨆ i, g i = ⨆ i, a + g i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  cases a with
  | bot => simp
  | coe a =>
    let h : ι → ℕ∞ := fun i ↦ WithBot.unbotD (α := ℕ∞) 0 (g i)
    have hgh : ∀ i, g i = (h i : WithBot ℕ∞) := by
      intro i
      cases hi : g i with
      | bot => exact (hg i hi).elim
      | coe b => simp [h, hi]
    have hsup : (⨆ i, g i) = ((⨆ i, h i : ℕ∞) : WithBot ℕ∞) :=
      (iSup_congr hgh).trans (WithBot.coe_iSup (f := h) (OrderTop.bddAbove _)).symm
    rw [hsup, ← WithBot.coe_add, ENat.add_iSup,
      WithBot.coe_iSup (f := fun i ↦ a + h i) (OrderTop.bddAbove _)]
    exact iSup_congr fun i ↦ by rw [WithBot.coe_add, ← hgh i]

/-- The Krull dimension of a nontrivial local ring is not `⊥`. -/
@[ega "0 16.1.1" "special case"]
private lemma ringKrullDim_ne_bot_of_isLocalRing (R : Type*) [CommRing R] [IsLocalRing R] :
    ringKrullDim R ≠ ⊥ :=
  ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial

/-- The dimension formula for the local rings of a flat morphism: the Krull dimension of the
local ring of the source is that of the local ring of the target plus that of the local ring of
the fibre. -/
@[ega "IV 6.1.2" "more general"]
private lemma ringKrullDim_stalk_eq_add {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (Y.presheaf.stalk (f x)) +
        ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have h := ringKrullDim_eq_add_ringKrullDim_closedFibre R S (Flat.stalkMap f x)
  have he := ringKrullDim_eq_of_ringEquiv (quotientStalkEquivFiberStalk f x)
  simpa only [R, S] using
    h.trans (congrArg (fun n : WithBot ℕ∞ ↦ ringKrullDim R + n) he)

/-- The Krull dimension of the local ring of a fibre is unchanged by transporting the base point
along an equality. -/
private lemma ringKrullDim_fiber_stalk_cast {X Y : Scheme.{u}} (f : X ⟶ Y) {y y' : Y} (h : y = y')
    (z : f.fiber y) :
    ringKrullDim ((f.fiber y).presheaf.stalk z) =
      ringKrullDim ((f.fiber y').presheaf.stalk (h ▸ z)) := by cases h; rfl

/-- An open neighbourhood of a point inside a neighbourhood realizing the local dimension also
realizes it. -/
private lemma topologicalKrullDim_eq_topologicalKrullDimAt_of_subset {T : Type*}
    [TopologicalSpace T] {t : T} {A B : Set T} (hA : IsOpen A) (htA : t ∈ A) (hAB : A ⊆ B)
    (hB : topologicalKrullDimAt T t = topologicalKrullDim B) :
    topologicalKrullDim A = topologicalKrullDimAt T t :=
  le_antisymm ((topologicalKrullDim_le_of_subset hAB).trans hB.ge)
    ((topologicalKrullDimAt_isLeast T t).2 ⟨A, htA, hA, rfl⟩)

/-- For a surjective flat morphism of relative dimension `d` between nonempty locally Noetherian
schemes, the dimension of the source is the dimension of the target plus `d`: both are suprema of
Krull dimensions of local rings, and the local dimension formula compares them termwise. -/
private theorem topologicalKrullDim_eq_add_of_surjective {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
    {d : ℕ} (hf : RelativeDimension f d) (hsurj : Function.Surjective f) (hne : Nonempty X) :
    topologicalKrullDim X = topologicalKrullDim Y + (d : WithBot ℕ∞) := by
  have : Nonempty Y := ⟨f hne.some⟩
  have hFdim : ∀ y, Nonempty (f.fiber y) →
      (⨆ z : f.fiber y, ringKrullDim ((f.fiber y).presheaf.stalk z)) = (d : WithBot ℕ∞) := by
    intro y hy
    rw [← topologicalKrullDim_eq_iSup_krullDimOfRing_stalk (f.fiber y)]
    exact (hf y hy).2
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X,
    topologicalKrullDim_eq_iSup_krullDimOfRing_stalk Y]
  refine le_antisymm (iSup_le fun x ↦ ?_) ?_
  · rw [ringKrullDim_stalk_eq_add f x]
    calc ringKrullDim (Y.presheaf.stalk (f x)) +
          ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
        ≤ ringKrullDim (Y.presheaf.stalk (f x)) + (d : WithBot ℕ∞) := by
          gcongr
          exact hFdim (f x) ⟨f.asFiber x⟩ ▸ le_iSup (fun w : f.fiber (f x) ↦
            ringKrullDim ((f.fiber (f x)).presheaf.stalk w)) (f.asFiber x)
      _ ≤ (⨆ y : Y, ringKrullDim (Y.presheaf.stalk y)) + (d : WithBot ℕ∞) := by
          gcongr
          exact le_iSup (fun y : Y ↦ ringKrullDim (Y.presheaf.stalk y)) (f x)
  · rw [show (⨆ y : Y, ringKrullDim (Y.presheaf.stalk y)) + (d : WithBot ℕ∞) =
        ⨆ y : Y, ringKrullDim (Y.presheaf.stalk y) + (d : WithBot ℕ∞) by
      rw [add_comm, add_iSup_of_ne_bot (d : WithBot ℕ∞)
        (fun y : Y ↦ ringKrullDim (Y.presheaf.stalk y))
        fun y ↦ ringKrullDim_ne_bot_of_isLocalRing _]
      exact iSup_congr fun y ↦ add_comm _ _]
    refine iSup_le fun y ↦ ?_
    obtain ⟨x, hx⟩ := hsurj y
    have hneF : Nonempty (f.fiber y) := ⟨(f.fiberHomeo y).symm ⟨x, hx⟩⟩
    rw [← hFdim y hneF, add_iSup_of_ne_bot _ _ fun z ↦ ringKrullDim_ne_bot_of_isLocalRing _]
    refine iSup_le fun z ↦ ?_
    have hbase : f (f.fiberι y z) = y := by
      simpa using (f.fiberHomeo y z).property
    have hfiberDim : ringKrullDim ((f.fiber y).presheaf.stalk z) =
        ringKrullDim ((f.fiber (f (f.fiberι y z))).presheaf.stalk
          (f.asFiber (f.fiberι y z))) := by
      have hdim := ringKrullDim_fiber_stalk_cast f hbase (f.asFiber (f.fiberι y z))
      rw [Scheme.Hom.cast_asFiber_fiberι f y z hbase] at hdim
      exact hdim.symm
    rw [show ringKrullDim (Y.presheaf.stalk y) =
      ringKrullDim (Y.presheaf.stalk (f (f.fiberι y z))) by rw [hbase], hfiberDim,
      ← ringKrullDim_stalk_eq_add f (f.fiberι y z)]
    exact le_iSup (fun x : X ↦ ringKrullDim (X.presheaf.stalk x)) (f.fiberι y z)

/-- **Stacks Project, Tag 0AFE.** A flat morphism locally of finite type of relative dimension
`d` between locally Noetherian schemes raises the local dimension by `d`:
`dim_x(X) = dim_{f x}(Y) + d`.

This is also the input to the dimension formula for a Cohen-Macaulay morphism. -/
@[stacks 0AFE]
public theorem topologicalKrullDimAt_eq_add_of_relativeDimension {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f] [LocallyOfFiniteType f]
    {d : ℕ} (hf : RelativeDimension f d) (x : X) :
    topologicalKrullDimAt X x = topologicalKrullDimAt Y (f x) + (d : WithBot ℕ∞) := by
  obtain ⟨⟨Ux, hxUx, hUx, hdimUx⟩, -⟩ := topologicalKrullDimAt_isLeast X x
  obtain ⟨⟨Vy, hyVy, hVy, hdimVy⟩, -⟩ := topologicalKrullDimAt_isLeast Y (f x)
  let W : X.Opens := (⟨Ux, hUx⟩ : X.Opens) ⊓ f ⁻¹ᵁ (⟨Vy, hVy⟩ : Y.Opens)
  have hxW : x ∈ W := ⟨hxUx, hyVy⟩
  have hdimW : topologicalKrullDim W.toScheme = topologicalKrullDimAt X x := by
    exact topologicalKrullDim_eq_topologicalKrullDimAt_of_subset W.2 hxW (fun _ hz ↦ hz.1) hdimUx
  have hopen : IsOpenMap (W.ι ≫ f) :=
    IsOpenMap.comp (f := W.ι) (g := f) (Scheme.Hom.isOpenMap f) W.ι.isOpenEmbedding.isOpenMap
  let V : Y.Opens := ⟨Set.range (W.ι ≫ f), hopen.isOpen_range⟩
  have hyV : f x ∈ V := ⟨⟨x, hxW⟩, rfl⟩
  have hdimV : topologicalKrullDim V.toScheme = topologicalKrullDimAt Y (f x) := by
    refine topologicalKrullDim_eq_topologicalKrullDimAt_of_subset V.2 hyV ?_ hdimVy
    rintro y ⟨w, rfl⟩
    exact w.2.2
  have hWV : W ≤ f ⁻¹ᵁ V := fun w hw ↦ ⟨⟨w, hw⟩, rfl⟩
  have hcomp : f.resLE V W hWV ≫ V.ι = W.ι ≫ f := Scheme.Hom.resLE_comp_ι f hWV
  have hsurj : Function.Surjective (f.resLE V W hWV) := by
    intro v
    obtain ⟨w, hw⟩ := v.property
    refine ⟨w, Subtype.ext ?_⟩
    calc V.ι (f.resLE V W hWV w) = (f.resLE V W hWV ≫ V.ι) w :=
          (Scheme.Hom.comp_apply _ _ w).symm
      _ = (W.ι ≫ f) w := congrArg (fun k : W.toScheme ⟶ Y ↦ k w) hcomp
      _ = V.ι v := hw
  have hrel : RelativeDimension (f.resLE V W hWV) d :=
    RelativeDimension.of_comp_isOpenImmersion _ V.ι (W.ι ≫ f) hcomp
      (RelativeDimension.comp_isOpenImmersion W.ι f hf)
  rw [← hdimW, ← hdimV]
  exact topologicalKrullDim_eq_add_of_surjective (f.resLE V W hWV) hrel hsurj ⟨⟨x, hxW⟩⟩

/-- **Stacks Project, Tag 0AFG.** For a Cohen-Macaulay morphism locally of finite type between
locally Noetherian schemes, the dimension of the source at a point is the dimension of the target
at its image plus the dimension of the fibre at that point. -/
@[stacks 0AFG]
public theorem topologicalKrullDimAt_eq_add_topologicalKrullDimAt_fiber {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hfib : ∀ y : Y, IsLocallyNoetherian (f.fiber y))
    (hcm : Scheme.Hom.IsCohenMacaulay f hfib) (x : X) :
    topologicalKrullDimAt X x =
      topologicalKrullDimAt Y (f x) +
        topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  obtain ⟨hflat, hfibCM⟩ := (isCohenMacaulay_iff_flat_and_fibers f hfib).mp hcm
  have : Flat f := hflat
  have : LocallyOfFinitePresentation f := inferInstance
  obtain ⟨d, hxU⟩ : ∃ d : ℕ, x ∈ relativeDimensionOpen f hfibCM d :=
    Opens.mem_iSup.mp (by rw [iSup_relativeDimensionOpen f hfibCM]; trivial)
  let U : X.Opens := relativeDimensionOpen f hfibCM d
  have hrel : RelativeDimension (U.ι ≫ f) d := relativeDimensionOpen_relativeDimension f hfibCM d
  have hdimU : topologicalKrullDimAt X x = topologicalKrullDimAt U.toScheme ⟨x, hxU⟩ :=
    Topology.IsOpenEmbedding.topologicalKrullDimAt_eq
      (IsOpen.isOpenEmbedding_subtypeVal U.2) ⟨x, hxU⟩
  rw [hdimU, topologicalKrullDimAt_eq_add_of_relativeDimension (U.ι ≫ f) hrel ⟨x, hxU⟩,
    topologicalKrullDimAt_fiber_eq_of_relativeDimension f U d hrel x hxU]
  rfl

end AlgebraicGeometry

end
