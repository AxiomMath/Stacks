module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.SmoothAtIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizationTransport

/-!
# Replacing the base of a normalized base change by an isomorphic one

Let `f : X ⟶ T` be a morphism, let `i : S ⟶ T` and let `s : S' ⟶ T`'s factorisation through `i`
be by an **isomorphism** `s : S' ⟶ S`, so that the base change of `f` along `s ≫ i` and the base
change along `i` differ only by the identification `s` of their bases.  **Then the normalization
of `X ×_T S'` is smooth over `S'` at every generic point of every one of its fibres exactly when
the normalization of `X ×_T S` is smooth over `S` at every generic point of every one of its
fibres.**

This is the last transport the reduced fibre theorem needs.  Its last paragraph produces the
final base as the integral closure of `B₀` — the base the *first* paragraph produced — in the
final field extension `L₁`, whereas Tag 09IL names the final base as the integral closure of the
original `A` in `L₁`.  Those two are the same subring of `L₁`, by
`integralClosure_eq_restrictScalars_of_isIntegral`, but they are different *types*: the
conclusion has to move along a ring isomorphism of the bases, and with it the pullback, the
normalization, the structure morphism, the fibres and the generic-point condition.

The pullbacks are compared by pasting the cartesian square of `f` along `s ≫ i` with the square
whose horizontal arrows are `s` and the identity of `T`, cartesian because both are
isomorphisms; the normalizations then by
`AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_of_iso`; and smoothness and the
generic-point condition by `InfinitesimalLifting.smoothAt_iso_hom_iff` and
`AlgebraicGeometry.mem_genericPoints_asFiber_iso_hom_iff`, which move both across an
isomorphism of squares — the base moving too.

## Main results

* `AlgebraicGeometry.isPullback_fst_snd_comp_of_isIso`: the base change of `f` along `s ≫ i` is
  a base change of `f` along `i` when `s` is an isomorphism.
* `AlgebraicGeometry.exists_normalizationScheme_iso_pullback_comp_of_isIso`: the two normalized
  base changes are isomorphic, by an isomorphism carrying one structure morphism to the other
  through `s`.
* `AlgebraicGeometry.smoothAt_normalization_pullback_of_isIso_base`: smoothness at every generic
  point of every fibre transports from the one normalized base change to the other.
* `AlgebraicGeometry.mem_genericPoints_asFiber_fiberι`: a generic point of the fibre over a
  named point is a generic point of its own fibre, read in the ambient scheme.

## Implementation notes

The finiteness-of-irreducible-components witnesses are propositions, so the normalizations named
with different such proofs are the same type and no transport along them is needed.

The base morphism of the base change being replaced is taken as a morphism `j` together with an
equation `j = s ≫ i` rather than as the composite itself: a consumer meets it in whatever shape
its own statement produced, and the equation is discharged there instead of by rewriting a
morphism that the finiteness witness and the normalization both mention.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X T S S' : Scheme.{u}}

/-- **The base change of `f` along `s ≫ i` is a base change of `f` along `i` when `s` is an
isomorphism.**  The cartesian square of `f` along `s ≫ i` is pasted with the square whose
horizontal arrows are `s` and the identity of `T`, cartesian because both are isomorphisms. -/
theorem isPullback_fst_snd_comp_of_isIso (f : X ⟶ T) (i : S ⟶ T) (s : S' ⟶ S) [IsIso s] :
    IsPullback (pullback.fst f (s ≫ i)) (pullback.snd f (s ≫ i) ≫ s) f i := by
  have ht : IsPullback s (s ≫ i) i (𝟙 T) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hs : IsPullback (pullback.snd f (s ≫ i)) (pullback.fst f (s ≫ i)) (s ≫ i) f :=
    (IsPullback.of_hasPullback f (s ≫ i)).flip
  have hpaste := (hs.paste_horiz ht).flip
  rwa [Category.comp_id] at hpaste

/-- **The normalized base changes along `s ≫ i` and along `i` are isomorphic when `s` is an
isomorphism**, by an isomorphism carrying the structure morphism over `S` to the structure
morphism over `S'` followed by `s`. -/
theorem exists_normalizationScheme_iso_pullback_comp_of_isIso (f : X ⟶ T) (i : S ⟶ T)
    (s : S' ⟶ S) [IsIso s]
    (h₁ : ∀ U : (pullback f (s ≫ i) : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f (s ≫ i) : Scheme.{u})) → (irreducibleComponents U).Finite)
    (h₂ : ∀ U : (pullback f i : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f i : Scheme.{u})) → (irreducibleComponents U).Finite) :
    ∃ d : (pullback f (s ≫ i) : Scheme.{u}).normalizationScheme h₁ ≅
        (pullback f i : Scheme.{u}).normalizationScheme h₂,
      d.hom ≫ ((pullback f i : Scheme.{u}).normalization h₂ ≫ pullback.snd f i) =
        ((pullback f (s ≫ i) : Scheme.{u}).normalization h₁ ≫
          pullback.snd f (s ≫ i)) ≫ s := by
  set θ := (isPullback_fst_snd_comp_of_isIso f i s).isoPullback with hθ
  obtain ⟨d, hd⟩ := Scheme.exists_normalizationScheme_iso_of_iso θ h₁ h₂
  refine ⟨d, ?_⟩
  have hθsnd : θ.hom ≫ pullback.snd f i = pullback.snd f (s ≫ i) ≫ s :=
    (isPullback_fst_snd_comp_of_isIso f i s).isoPullback_hom_snd
  rw [← Category.assoc, hd, Category.assoc, hθsnd, Category.assoc]

/-- **Smoothness at every generic point of every fibre transports between the two normalized
base changes.**  If the normalization of `X ×_T S'` is smooth over `S'` at every generic point
of every one of its fibres, and `S' ⟶ S` is an isomorphism over `T`, then the normalization of
`X ×_T S` is smooth over `S` at every generic point of every one of its fibres. -/
theorem smoothAt_normalization_pullback_of_isIso_base (f : X ⟶ T) (i : S ⟶ T) (s : S' ⟶ S)
    [IsIso s] (j : S' ⟶ T) (hj : j = s ≫ i)
    (h₁ : ∀ U : (pullback f j : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f j : Scheme.{u})) → (irreducibleComponents U).Finite)
    (h₂ : ∀ U : (pullback f i : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f i : Scheme.{u})) → (irreducibleComponents U).Finite)
    [LocallyOfFinitePresentation ((pullback f i : Scheme.{u}).normalization h₂ ≫
      pullback.snd f i)]
    (H : ∀ y : (pullback f j : Scheme.{u}).normalizationScheme h₁,
      ((pullback f j : Scheme.{u}).normalization h₁ ≫ pullback.snd f j).asFiber y ∈
        genericPoints ↥(((pullback f j : Scheme.{u}).normalization h₁ ≫
          pullback.snd f j).fiber
            (((pullback f j : Scheme.{u}).normalization h₁ ≫ pullback.snd f j).base y)) →
      InfinitesimalLifting.SmoothAt ((pullback f j : Scheme.{u}).normalization h₁ ≫
        pullback.snd f j) y) :
    ∀ z : (pullback f i : Scheme.{u}).normalizationScheme h₂,
      ((pullback f i : Scheme.{u}).normalization h₂ ≫ pullback.snd f i).asFiber z ∈
        genericPoints ↥(((pullback f i : Scheme.{u}).normalization h₂ ≫
          pullback.snd f i).fiber
            (((pullback f i : Scheme.{u}).normalization h₂ ≫ pullback.snd f i).base z)) →
      InfinitesimalLifting.SmoothAt ((pullback f i : Scheme.{u}).normalization h₂ ≫
        pullback.snd f i) z := by
  subst hj
  set g₁ := (pullback f (s ≫ i) : Scheme.{u}).normalization h₁ ≫
    pullback.snd f (s ≫ i) with hg₁
  set g₂ := (pullback f i : Scheme.{u}).normalization h₂ ≫ pullback.snd f i with hg₂
  obtain ⟨d, hd⟩ := exists_normalizationScheme_iso_pullback_comp_of_isIso f i s h₁ h₂
  have : LocallyOfFinitePresentation g₁ := by
    have hsplit : (d.hom ≫ g₂) ≫ inv s = g₁ := by
      rw [hd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← hsplit]
    infer_instance
  intro z hz
  set y := d.inv.base z with hy
  have hdy : d.hom.base y = z := by
    rw [hy, ← Scheme.Hom.comp_apply, d.inv_hom_id]; simp
  have hgp := mem_genericPoints_asFiber_iso_hom_iff d (asIso s) g₁ g₂ hd y
  rw [hdy] at hgp
  have hsm := (InfinitesimalLifting.smoothAt_iso_hom_iff d (asIso s) g₁ g₂ hd y).mp
    (H y (hgp.mpr hz))
  rwa [hdy] at hsm

/-- **A generic point of the fibre over a named point is a generic point of its own fibre**, the
latter condition being read in the ambient scheme.  This matches the two forms in which the
generic points of the fibres of a morphism are named: as points of `f.fiber s` for a point `s`
of the target, and as points of the source lying over their own image. -/
theorem mem_genericPoints_asFiber_fiberι (f : X ⟶ T) (t : T) (y : f.fiber t)
    (hy : y ∈ genericPoints ↥(f.fiber t)) :
    f.asFiber (f.fiberι t y) ∈ genericPoints ↥(f.fiber (f.base (f.fiberι t y))) := by
  have hι : Topology.IsInducing (f.fiberι t).base := (f.fiberι t).isEmbedding.isInducing
  have hbt : f.base (f.fiberι t y) = t := by
    have hmem : f.fiberι t y ∈ (f.base ⁻¹' {t} : Set X) :=
      f.range_fiberι t ▸ Set.mem_range_self y
    simpa using hmem
  rw [mem_genericPoints_iff_isMax] at hy
  rw [mem_genericPoints_asFiber_iff]
  intro x' hspec hfx
  have hx'mem : x' ∈ (f.base ⁻¹' {t} : Set X) := by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hfx, hbt]
  set w : f.fiber t := (f.fiberHomeo t).symm ⟨x', hx'mem⟩ with hw
  have hwι : f.fiberι t w = x' := f.fiberι_fiberHomeo_symm t ⟨x', hx'mem⟩
  have h1 : y ≤ w := Scheme.le_iff_specializes.mpr
    (hι.specializes_iff.mp (by rw [hwι]; exact hspec))
  have h2 : f.fiberι t y ⤳ x' := by
    have hle := hι.specializes_iff.mpr (Scheme.le_iff_specializes.mp (hy h1))
    rwa [hwι] at hle
  exact (h2.antisymm hspec).symm.eq

end AlgebraicGeometry

end
