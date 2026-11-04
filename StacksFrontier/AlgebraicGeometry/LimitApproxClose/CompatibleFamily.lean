module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StageColimit

/-!
# The stagewise-compatible charting family, and its image in the ring being added

For the glueing in the proof of Tag 07RN, `Stacks.StageSubalgebra.specLeg` takes a charting
family `b` of the rings at the stages which is *compatible* with the transition maps.  This file
constructs such a family, and computes the inverse image of the union of its standard opens along
the spectra of the legs of `Stacks.StageSubalgebra.ringCocone`.

## Main definitions and results

* `Stacks.FibreProduct.famMk` is the family: at a stage `k`, the compatible pair consisting of a
  *stage-independent* element `g l` of the ring being added and a lift `f k l` of its image.
  `Stacks.FibreProduct.diagramMap_famMk` is its compatibility: the transition map of the diagram
  of fibre products acts on the second component only, so the first components agree by
  **reflexivity** and the second is the hypothesis on the lifts
  (`Stacks.FibreProduct.fst_diagramMap` and `Stacks.FibreProduct.snd_diagramMap`, both `rfl`).

* `Stacks.transportedFam` produces the compatible lifts themselves, from lifts at a single stage
  below all others — which is the shape "after shrinking `I`" leaves the index in, every stage of
  `↥(Set.Ici i₀)` lying above `i₀`.  `Stacks.map_transportedFam` is the compatibility and
  `Stacks.app_transportedFam` says the lifts still lift, by the naturality of a cocone with
  constant vertex.

* `Stacks.StageSubalgebra.preimage_SpecMap_ringCocone_iSup_basicOpen` is the computation that the
  cone of step (iii) needs: the inverse image, along the spectrum of the leg of
  `Stacks.StageSubalgebra.ringCocone`, of the union of the standard opens of the charting family
  read inside a distinguished subalgebra, is the union of the standard opens of the `g l` inside
  the spectrum of the ring being added.

## Implementation notes

* The stages and the rings are in the single universe `u`.  The family-making part needs only a
  category; the transported lifts need a preorder with a stage below all others.

* The first component of a transported compatible pair is unchanged *by reflexivity*, so the
  first of the two equations `Stacks.FibreProduct.ext` asks for is literally `rfl`.

* The transition used to transport a lift is `CategoryTheory.homOfLE` of an inequality, and two
  such for the same pair of stages agree only because the homs of a preorder are a subsingleton;
  `Subsingleton.elim` is what lets `CategoryTheory.Functor.map_comp` fire.

* The leg of `Stacks.StageSubalgebra.ringCocone` applied to an element of a distinguished
  subalgebra is the cocone leg applied to the underlying element, by reflexivity, which is why
  the inverse-image computation closes with `AlgebraicGeometry.SpecMap_preimage_iSup_basicOpen`
  and a congruence rather than with any rewriting under the supremum.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks

/-! ### Compatible lifts from one stage below all others -/

section Transported

variable {K : Type u} [Preorder K] (F : K ⥤ CommRingCat.{u}) (k₀ : K) (hk₀ : ∀ k : K, k₀ ≤ k)
  {n : ℕ} (f₀ : Fin n → F.obj k₀)

/-- A family at one stage, transported to every stage above it. -/
def transportedFam (k : K) (l : Fin n) : F.obj k := F.map (homOfLE (hk₀ k)) (f₀ l)

/-- The transported family is compatible with the transition maps. -/
lemma map_transportedFam {k k' : K} (u : k ⟶ k') (l : Fin n) :
    F.map u (transportedFam F k₀ hk₀ f₀ k l) = transportedFam F k₀ hk₀ f₀ k' l := by
  rw [transportedFam, transportedFam, ← ConcreteCategory.comp_apply, ← F.map_comp,
    Subsingleton.elim (homOfLE (hk₀ k) ≫ u) (homOfLE (hk₀ k'))]

/-- The transported family still lifts what the original family lifted. -/
lemma app_transportedFam {R : CommRingCat.{u}} (τ : F ⟶ (Functor.const K).obj R) (k : K)
    (l : Fin n) : τ.app k (transportedFam F k₀ hk₀ f₀ k l) = τ.app k₀ (f₀ l) := by
  rw [transportedFam]
  exact FibreProduct.app_naturality F τ (homOfLE (hk₀ k)) (f₀ l)

end Transported

/-! ### The charting family of the fibre products -/

namespace FibreProduct

variable {K : Type u} [Category.{u} K] (F : K ⥤ CommRingCat.{u}) {R : CommRingCat.{u}}
  (τ : F ⟶ (Functor.const K).obj R) {B : CommRingCat.{u}} (s : B ⟶ R) {n : ℕ} (g : Fin n → B)
  (f : ∀ k : K, Fin n → F.obj k) (hf : ∀ (k : K) (l : Fin n), τ.app k (f k l) = s (g l))

/-- **The charting family of the fibre products.**  At a stage it is the compatible pair made of
a stage-independent element of the ring being added and a lift of its image. -/
def famMk (k : K) (l : Fin n) : obj s (τ.app k) := mk s (τ.app k) (g l) (f k l) (hf k l).symm

/-- The first component of the charting family is the stage-independent element. -/
@[simp]
lemma fst_famMk (k : K) (l : Fin n) : fst s (τ.app k) (famMk F τ s g f hf k l) = g l := rfl

/-- The second component of the charting family is the lift at that stage. -/
@[simp]
lemma snd_famMk (k : K) (l : Fin n) : snd s (τ.app k) (famMk F τ s g f hf k l) = f k l := rfl

/-- **The charting family is compatible with the transition maps.**  The first components agree
by reflexivity, the transition acting on the second component only; the second is the
compatibility of the lifts. -/
lemma diagramMap_famMk (hcomp : ∀ {k k' : K} (u : k ⟶ k') (l : Fin n), F.map u (f k l) = f k' l)
    {k k' : K} (u : k ⟶ k') (l : Fin n) :
    diagramMap F τ s u (famMk F τ s g f hf k l) = famMk F τ s g f hf k' l :=
  ext s (τ.app k') rfl (hcomp u l)

end FibreProduct

/-! ### The image of the charting family in the ring being added -/

namespace StageSubalgebra

variable {K : Type u} [Preorder K] {F : K ⥤ CommRingCat.{u}}
  {P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop} {B : CommRingCat.{u}}
  (τ : F ⟶ (Functor.const K).obj B) {n : ℕ} (c : ∀ k : K, Fin n → F.obj k) (g : Fin n → B)
  (hc : ∀ (k : K) (l : Fin n), τ.app k (c k l) = g l)

include hc in
/-- **The image of the charting family in the ring being added.**  The inverse image, along the
spectrum of the leg of `Stacks.StageSubalgebra.ringCocone`, of the union of the standard opens of
the charting family inside a distinguished subalgebra is the union of the standard opens of the
stage-independent elements. -/
lemma preimage_SpecMap_ringCocone_iSup_basicOpen (j : StageSubalgebra F P)
    (hmem : ∀ l, c (stage j) l ∈ sub j) :
    Spec.map ((ringCocone (P := P) τ).ι.app j) ⁻¹ᵁ
        (⨆ l, PrimeSpectrum.basicOpen (⟨c (stage j) l, hmem l⟩ : sub j) :
          (Spec (CommRingCat.of (sub j))).Opens) =
      (⨆ l, PrimeSpectrum.basicOpen (g l) : (Spec B).Opens) := by
  refine (SpecMap_preimage_iSup_basicOpen ((ringCocone (P := P) τ).ι.app j)
    (fun l ↦ (⟨c (stage j) l, hmem l⟩ : sub j))).trans ?_
  exact iSup_congr fun l ↦ congrArg PrimeSpectrum.basicOpen (hc (stage j) l)

end StageSubalgebra

end Stacks
