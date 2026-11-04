module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.RationalPointFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsomorphismOnFibre
import StacksCore.Tactic.StacksAttribute

/-!
# Trivializing a smooth proper family from a graph over its fibre

Let `S` be a scheme of finite type over a field `k` with `k`-rational point `s`, let `g : Y ⟶ S`
be proper, and let `X = Y_s ×_k S ⟶ S` be the constant family with fibre `Y_s = Y ×_S Spec k`.
Suppose given a scheme `Z` over `S`, proper over `S` and flat over `S` at the points above `s`,
together with `S`-morphisms `Z ⟶ X` and `Z ⟶ Y` which are isomorphisms on the fibre over `s`.
Then `Y` is constant near `s`: there is an open `U ⊆ S` containing `s` with `Y|_U ≅ Y_s ×_k U`
over `U`.

## Main results

* `AlgebraicGeometry.exists_opens_nonempty_overPullback_iso_of_isIso_fiber`: two morphisms out of
  a common proper source, flat above `s`, each an isomorphism on the fibre at a point `s` of the
  base, have targets isomorphic over an open neighbourhood of `s`.
* `AlgebraicGeometry.exists_isIso_residueField_hom_of_isSection`: at a `k`-rational point the
  residue field is `k`, and the point is the induced morphism from its residue field.
* `AlgebraicGeometry.isIso_overPullback_fromSpecResidueField_of_isSection`: consequently a
  morphism over `S` that is an isomorphism after base change along a `k`-rational point is one
  after base change along the residue field of the point that it picks out.
* `AlgebraicGeometry.constantFamilyOverPullbackIso`: the constant family with fibre `Y_s`
  restricts over an open `U ⊆ S` to the constant family over `U` with the same fibre.
* `AlgebraicGeometry.exists_opens_nonempty_iso_constantFamily_of_isIso_fibre`: the above
  combined, in the form the conclusion of [Stacks, Tag 0G0R] takes.

## Implementation notes

The spreading out is [Stacks, Tag 0G0Q] in the form
`AlgebraicGeometry.exists_isIso_baseChange_of_flatAt_of_isIso_fiber`, which asks for flatness of
the common source over `S` only at the points above `s` — all that the source's proof of 0G0Q
uses — applied to each of `Z ⟶ X` and
`Z ⟶ Y`; the two neighbourhoods it returns are intersected, which needs that base change to a
smaller open of the base preserves being an isomorphism
(`AlgebraicGeometry.isIso_overPullback_of_le`). Both morphisms then become isomorphisms of
schemes over the intersection, and since `CategoryTheory.Over.forget` reflects isomorphisms they
become isomorphisms in `Over U`, which compose to the trivialization.

A `k`-rational point is a section `s : Spec k ⟶ S` of the structure morphism, while
[Stacks, Tag 0G0Q] takes the fibre at a topological point of `S` along
`AlgebraicGeometry.Scheme.fromSpecResidueField`. The two are bridged by
`AlgebraicGeometry.isIso_descResidueField_of_isSection` in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/NoDeformations/RationalPointFibre.lean`: `s`
factors as `Spec.map ψ ≫ S.fromSpecResidueField x` through the point `x` it picks out, and
`ψ : κ(x) ⟶ k` is an isomorphism. Base change along the isomorphism `Spec.map ψ` then reflects
being an isomorphism.

The restriction of the constant family is the pullback pasting isomorphism
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`: both `(Y_s ×_k S) ×_S U` and `Y_s ×_k U` are
the pullback of `Y_s ⟶ Spec k` along `U ⟶ S ⟶ Spec k`.

Finite type over `k` is the conjunction `[LocallyOfFiniteType q] [QuasiCompact q]`, which makes
`S` Noetherian, as [Stacks, Tag 0G0Q] requires: locally Noetherian because `Spec k` is and `q`
is locally of finite type, quasi-compact because `Spec k` is and `q` is quasi-compact. Since
`Spec k` has a single point, the conclusion's `Set.range s.base ⊆ U` is exactly that the point
`s` picks out lies in `U`.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0Q](https://stacks.math.columbia.edu/tag/0G0Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Shrink

variable {S : Scheme.{u}}

/-- Base change of a morphism over `S` to a smaller open of the base preserves being an
isomorphism. -/
theorem isIso_overPullback_of_le {X Y : Over S} (p : X ⟶ Y) {U V : S.Opens} (hUV : U ≤ V)
    (hV : IsIso ((Over.pullback V.ι).map p).left) :
    IsIso ((Over.pullback U.ι).map p).left := by
  rw [← S.homOfLE_ι hUV]
  exact overPullback_map_comp (MorphismProperty.isomorphisms Scheme.{u}) V.ι (S.homOfLE hUV) p hV

/-- Base change along an isomorphism of bases reflects being an isomorphism. -/
theorem isIso_left_of_isIso_overPullback_of_isIso {A B : Scheme.{u}} (t : A ⟶ B) [IsIso t]
    {P Q : Over B} (m : P ⟶ Q) (hm : IsIso ((Over.pullback t).map m).left) : IsIso m.left := by
  have : IsIso (Limits.pullback.fst P.hom t) := inferInstance
  have : IsIso (Limits.pullback.fst Q.hom t) := inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms Scheme.{u})
    (Arrow.isoMk (asIso (Limits.pullback.fst P.hom t)) (asIso (Limits.pullback.fst Q.hom t))
      (overPullback_isPullback t P Q m).w)).mp hm

/-- A morphism over `S` whose base change to an open `U` of the base is an isomorphism of schemes
is an isomorphism of schemes over `U`. -/
theorem isIso_overPullback_map {X Y : Over S} (p : X ⟶ Y) (U : S.Opens)
    (h : IsIso ((Over.pullback U.ι).map p).left) : IsIso ((Over.pullback U.ι).map p) := by
  have : IsIso ((Over.forget U.toScheme).map ((Over.pullback U.ι).map p)) := h
  exact isIso_of_reflects_iso _ (Over.forget U.toScheme)

/-- Two morphisms out of a common source, proper over a Noetherian base `S` and flat over `S` at
the points above `s`, which are both isomorphisms on the fibre over `s`, have targets isomorphic
over an open neighbourhood of `s`. -/
theorem exists_opens_nonempty_overPullback_iso_of_isIso_fiber [IsNoetherian S]
    {X Y Z : Over S} (a : Z ⟶ X) (b : Z ⟶ Y)
    [IsProper X.hom] [IsProper Y.hom] [IsProper Z.hom] (s : S)
    (hZflat : ∀ z : Z.left, Z.hom z = s →
      AlgebraicGeometry.IsFlatAt Z.hom.toLRSHom.toShHom z)
    (ha : IsIso ((Over.pullback (S.fromSpecResidueField s)).map a).left)
    (hb : IsIso ((Over.pullback (S.fromSpecResidueField s)).map b).left) :
    ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((Over.pullback U.ι).obj X ≅ (Over.pullback U.ι).obj Y) := by
  have := ha
  obtain ⟨U₁, hs₁, h₁⟩ := exists_isIso_baseChange_of_flatAt_of_isIso_fiber a s hZflat
  have := hb
  obtain ⟨U₂, hs₂, h₂⟩ := exists_isIso_baseChange_of_flatAt_of_isIso_fiber b s hZflat
  refine ⟨U₁ ⊓ U₂, ⟨hs₁, hs₂⟩, ?_⟩
  have := isIso_overPullback_map a (U₁ ⊓ U₂) (isIso_overPullback_of_le a inf_le_left h₁)
  have := isIso_overPullback_map b (U₁ ⊓ U₂) (isIso_overPullback_of_le b inf_le_right h₂)
  exact ⟨(asIso ((Over.pullback (U₁ ⊓ U₂).ι).map a)).symm ≪≫
    asIso ((Over.pullback (U₁ ⊓ U₂).ι).map b)⟩

end Shrink

section RationalPoint

variable {k : Type u} [Field k] {S : Scheme.{u}}

/-- **The residue field at a `k`-rational point is `k`.** A section `s : Spec k ⟶ S` of a
structure morphism `q : S ⟶ Spec k` is `Spec.map ψ ≫ S.fromSpecResidueField x` for the point `x`
it picks out and an isomorphism `ψ : κ(x) ⟶ k`.

This is the existential form of `AlgebraicGeometry.isIso_descResidueField_of_isSection`, which
names the isomorphism. -/
theorem exists_isIso_residueField_hom_of_isSection {q : S ⟶ Spec (.of k)}
    {s : Spec (.of k) ⟶ S} (hs : s ≫ q = 𝟙 _) :
    ∃ ψ : S.residueField (s.base (IsLocalRing.closedPoint k)) ⟶ CommRingCat.of k,
      IsIso ψ ∧
        Spec.map ψ ≫ S.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)) = s :=
  ⟨S.descResidueField (Scheme.stalkClosedPointTo s),
    isIso_descResidueField_of_isSection q s hs,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k S s⟩

/-- A morphism over `S` which is an isomorphism after base change along a `k`-rational point `s`
is an isomorphism after base change along the residue field of the point `s` picks out. -/
theorem isIso_overPullback_fromSpecResidueField_of_isSection {q : S ⟶ Spec (.of k)}
    {s : Spec (.of k) ⟶ S} (hs : s ≫ q = 𝟙 _) {X Y : Over S} (p : X ⟶ Y)
    (h : IsIso ((Over.pullback s).map p).left) :
    IsIso ((Over.pullback
      (S.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)))).map p).left := by
  obtain ⟨ψ, hψ, hfac⟩ := exists_isIso_residueField_hom_of_isSection hs
  have h₁ : IsIso ((Over.pullback (Spec.map ψ ≫
      S.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)))).map p).left := by
    rw [hfac]; exact h
  have h₂ := (overPullback_map_comp_iff (MorphismProperty.isomorphisms Scheme.{u})
    (S.fromSpecResidueField (s.base (IsLocalRing.closedPoint k))) (Spec.map ψ) p).mp h₁
  have := hψ
  have : IsIso (Spec.map ψ) := inferInstance
  exact isIso_left_of_isIso_overPullback_of_isIso (Spec.map ψ) _ h₂

end RationalPoint

section ConstantFamily

variable {k : Type u} [Field k] {S Y : Scheme.{u}}
  (q : S ⟶ Spec (.of k)) (g : Y ⟶ S) (s : Spec (.of k) ⟶ S)

/-- **The constant family restricts to a constant family.** Over an open `U ⊆ S` the constant
family `Y_s ×_k S` is the constant family `Y_s ×_k U` with the same fibre: both are the pullback
of `Y_s ⟶ Spec k` along `U ⟶ S ⟶ Spec k`. -/
def constantFamilyOverPullbackIso (U : S.Opens) :
    (Over.pullback U.ι).obj (Over.mk (constantFamilyπ q g s)) ≅
      Over.mk (Limits.pullback.snd (fibreAtRationalPointπ g s) (U.ι ≫ q)) :=
  Over.isoMk (pullbackLeftPullbackSndIso (fibreAtRationalPointπ g s) q U.ι) (by simp)

/-- **A graph over the fibre trivializes a proper family near a rational point.** Let `S` be of
finite type over a field `k` with `k`-rational point `s`, let `g : Y ⟶ S` be proper and let
`X = Y_s ×_k S` be the constant family with fibre `Y_s`. A scheme `Z` over `S`, proper over `S`
and flat over `S` at the points above `s`, with `S`-morphisms to `X` and to `Y` that are
isomorphisms on the fibre of `S` at the point `s` picks out, makes `Y` constant near `s`: there
is an open `U ⊆ S` containing `s` with `Y|_U ≅ Y_s ×_k U` over `U`. -/
theorem exists_opens_nonempty_iso_constantFamily_of_isIso_fibre
    [LocallyOfFiniteType q] [QuasiCompact q] [IsProper g]
    {Z : Over S} (a : Z ⟶ Over.mk (constantFamilyπ q g s)) (b : Z ⟶ Over.mk g)
    [IsProper Z.hom]
    (hZflat : ∀ z : Z.left, Z.hom z = s.base (IsLocalRing.closedPoint k) →
      AlgebraicGeometry.IsFlatAt Z.hom.toLRSHom.toShHom z)
    (ha : IsIso ((Over.pullback
      (S.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)))).map a).left)
    (hb : IsIso ((Over.pullback
      (S.fromSpecResidueField (s.base (IsLocalRing.closedPoint k)))).map b).left) :
    ∃ U : S.Opens, Set.range s.base ⊆ (U : Set S) ∧
      Nonempty ((Over.pullback U.ι).obj (Over.mk g) ≅
        Over.mk (Limits.pullback.snd (fibreAtRationalPointπ g s) (U.ι ≫ q))) := by
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian S := ⟨⟩
  have : IsProper (Over.mk (constantFamilyπ q g s)).hom := by
    dsimp only [Over.mk_hom, constantFamilyπ, fibreAtRationalPointπ]
    infer_instance
  have : IsProper (Over.mk g).hom := by dsimp only [Over.mk_hom]; infer_instance
  obtain ⟨U, hsU, ⟨e⟩⟩ := exists_opens_nonempty_overPullback_iso_of_isIso_fiber b a
    (s.base (IsLocalRing.closedPoint k)) hZflat hb ha
  refine ⟨U, Set.range_subset_iff.mpr fun p => ?_, ⟨e ≪≫ constantFamilyOverPullbackIso q g s U⟩⟩
  rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
  exact hsU

/-- **A graph over the fibre at a `k`-rational point trivializes a proper family near it.** The
previous statement with the two fibrewise hypotheses taken, as in [Stacks, Tag 0G0R], along the
`k`-rational point `s : Spec k ⟶ S` itself rather than along the residue field of the point it
picks out. -/
theorem exists_opens_nonempty_iso_constantFamily_of_isIso_fibre_of_isSection
    [LocallyOfFiniteType q] [QuasiCompact q] [IsProper g] (hs : s ≫ q = 𝟙 _)
    {Z : Over S} (a : Z ⟶ Over.mk (constantFamilyπ q g s)) (b : Z ⟶ Over.mk g)
    [IsProper Z.hom]
    (hZflat : ∀ z : Z.left, Z.hom z = s.base (IsLocalRing.closedPoint k) →
      AlgebraicGeometry.IsFlatAt Z.hom.toLRSHom.toShHom z)
    (ha : IsIso ((Over.pullback s).map a).left)
    (hb : IsIso ((Over.pullback s).map b).left) :
    ∃ U : S.Opens, Set.range s.base ⊆ (U : Set S) ∧
      Nonempty ((Over.pullback U.ι).obj (Over.mk g) ≅
        Over.mk (Limits.pullback.snd (fibreAtRationalPointπ g s) (U.ι ≫ q))) :=
  exists_opens_nonempty_iso_constantFamily_of_isIso_fibre q g s a b hZflat
    (isIso_overPullback_fromSpecResidueField_of_isSection hs a ha)
    (isIso_overPullback_fromSpecResidueField_of_isSection hs b hb)

end ConstantFamily

end AlgebraicGeometry

end
