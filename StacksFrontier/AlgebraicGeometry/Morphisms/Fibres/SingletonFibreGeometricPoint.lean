module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable

/-!
# A singleton fibre with purely inseparable residue extension carries one point of a field

Let `g : E ⟶ V` be a morphism of schemes whose fibre over the image of a point `z` of `E` is the
single point `z`, and suppose the residue field extension `κ(g z) ⊂ κ(z)` is purely inseparable.
Then for every field `k` there is at most one morphism `Spec k ⟶ E` over a given morphism
`Spec k ⟶ V` hitting `g z`: the fibre condition pins down the image point, and pure
inseparability pins down the embedding of the residue field. In particular a geometric point of
`V` has at most one lift to `E`.

Alongside it this file records the shrinking step that accompanies such a fibre: if `g` is a closed
map — for instance finite — and the fibre over a point `v` of `V` lies in an open `O` of `E`, then
an open neighbourhood of `v` has its whole preimage inside `O`. Removing the image of the closed
complement of `O` is all there is to it, and this is the move that replaces a base by a smaller one
in the étale-localisation arguments for a locally quasi-finite morphism.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.exists_opens_preimage_subset_of_isClosedMap` and
  `AlgebraicGeometry.exists_opens_preimage_subset_of_isFinite` — shrinking the base so that the
  whole preimage lands in a prescribed open.
* `AlgebraicGeometry.residueFieldHom_eq_of_isPurelyInseparable` — two embeddings of the residue
  field at a point into a field which agree on the residue field of the image point agree.
* `AlgebraicGeometry.eq_of_comp_eq_of_preimage_singleton_of_isPurelyInseparable` and
  `AlgebraicGeometry.subsingleton_lift_of_preimage_singleton_of_isPurelyInseparable` — the
  uniqueness of the lift, and its `Subsingleton` form.

## Implementation notes

Both statements about morphisms out of the spectrum of a field go through Mathlib's
`AlgebraicGeometry.Scheme.SpecToEquivOfField`, which presents such a morphism as a point together
with an embedding of its residue field. Writing the two morphisms in that form turns the two image
points into *variables*, which is what makes them substitutable: the hypothesis that one of them
equals `z` is then an equation between local variables rather than an equation about a projection
of a composite, and the residue fields in play become literally the residue field at `z` with no
`AlgebraicGeometry.Scheme.residueFieldCongr` transport anywhere.

Pure inseparability is used only through Mathlib's
`IsPurelyInseparable.injective_comp_algebraMap`, which is a statement about ring homomorphisms, so
no algebra-homomorphism bundling is needed either. It is *assumed* in the form
`RingHom.IsPurelyInseparable` of the residue field map rather than as an `IsPurelyInseparable`
under a `letI`-introduced algebra structure: the two are definitionally the same, and the former
is the shape in which Stacks 02LM
(`AlgebraicGeometry.exists_etale_finite_opens_of_isolated_fiber_points`) delivers it, so no
transport is needed at the call site.

The field `k` is not assumed algebraically closed, and `g` is not assumed finite or even
quasi-compact: the uniqueness statement needs nothing beyond the fibre being a single point and the
residue extension there being purely inseparable.

## References

* [Stacks Project, Tag 04DH](https://stacks.math.columbia.edu/tag/04DH)
* [Stacks Project, Tag 02LM](https://stacks.math.columbia.edu/tag/02LM)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- If the fibre of a closed morphism over a point `v` of the target lies inside an open `O` of the
source, then some open neighbourhood of `v` has its entire preimage inside `O`.

The complement of `O` is closed, so its image is closed and misses `v`; the complement of that
image is the required neighbourhood. -/
public theorem exists_opens_preimage_subset_of_isClosedMap {E V : Scheme.{u}} (g : E ⟶ V)
    (hg : IsClosedMap g.base) (O : E.Opens) (v : V)
    (hfib : g.base ⁻¹' {v} ⊆ (O : Set E)) :
    ∃ W : V.Opens, v ∈ W ∧ g.base ⁻¹' (W : Set V) ⊆ (O : Set E) := by
  refine ⟨⟨(g.base '' (O : Set E)ᶜ)ᶜ, (hg _ O.2.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨e, he, rfl⟩
    exact he (hfib rfl)
  · intro e he
    by_contra hO
    exact he ⟨e, hO, rfl⟩

/-- The shrinking step for a finite morphism, which is a closed map. -/
public theorem exists_opens_preimage_subset_of_isFinite {E V : Scheme.{u}} (g : E ⟶ V)
    [IsFinite g] (O : E.Opens) (v : V) (hfib : g.base ⁻¹' {v} ⊆ (O : Set E)) :
    ∃ W : V.Opens, v ∈ W ∧ g.base ⁻¹' (W : Set V) ⊆ (O : Set E) :=
  exists_opens_preimage_subset_of_isClosedMap g g.isClosedMap O v hfib

/-- Two embeddings of the residue field at a point `p` of `E` into a field `k` are equal as soon as
the two morphisms `Spec k ⟶ V` they induce by composition with `g` are equal.

Composing with `g` replaces the embedding `φ` of `κ(p)` by the embedding `κ(g p) ⟶ κ(p) ⟶ k`, so
the hypothesis says exactly that `φ` and `φ'` restrict to the same homomorphism on `κ(g p)`; pure
inseparability of `κ(p)` over `κ(g p)` says that no two embeddings do. -/
public theorem residueFieldHom_eq_of_isPurelyInseparable {E V : Scheme.{u}} (g : E ⟶ V) (p : E)
    {k : Type u} [Field k] (φ φ' : E.residueField p ⟶ CommRingCat.of k)
    (hpure : (g.residueFieldMap p).hom.IsPurelyInseparable)
    (hcomp : (Spec.map φ ≫ E.fromSpecResidueField p) ≫ g =
      (Spec.map φ' ≫ E.fromSpecResidueField p) ≫ g) :
    φ = φ' := by
  let : Algebra (V.residueField (g.base p)) (E.residueField p) :=
    (g.residueFieldMap p).hom.toAlgebra
  have hpi : IsPurelyInseparable (V.residueField (g.base p)) (E.residueField p) := hpure
  have key : g.residueFieldMap p ≫ φ = g.residueFieldMap p ≫ φ' := by
    have hrw : ∀ ψ : E.residueField p ⟶ CommRingCat.of k,
        (Spec.map ψ ≫ E.fromSpecResidueField p) ≫ g =
          (Scheme.SpecToEquivOfField k V).symm
            ⟨g.base p, g.residueFieldMap p ≫ ψ⟩ := by
      intro ψ
      simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [hrw φ, hrw φ'] at hcomp
    have h2 := (Scheme.SpecToEquivOfField k V).symm.injective hcomp
    simpa using h2
  apply CommRingCat.hom_ext
  refine IsPurelyInseparable.injective_comp_algebraMap
    (V.residueField (g.base p)) (E.residueField p) k ?_
  exact congrArg CommRingCat.Hom.hom key

/-- In a singleton fibre over `g z`, a morphism `Spec k ⟶ E` whose composite with `g` hits `g z`
hits `z`. -/
private theorem base_closedPoint_eq_of_comp_eq_of_preimage_singleton {E V : Scheme.{u}}
    (g : E ⟶ V) (z : E) (hfib : g.base ⁻¹' {g.base z} = {z}) {k : Type u} [Field k]
    (l : Spec (CommRingCat.of k) ⟶ E) (v : Spec (CommRingCat.of k) ⟶ V) (hl : l ≫ g = v)
    (hv : v.base (IsLocalRing.closedPoint k) = g.base z) :
    l.base (IsLocalRing.closedPoint k) = z := by
  subst hl
  exact (Set.ext_iff.mp hfib _).mp hv

/-- **Uniqueness of the lift of a point of a field through a singleton fibre.** If the fibre of
`g : E ⟶ V` over `g z` is the single point `z` and the residue extension `κ(g z) ⊂ κ(z)` is purely
inseparable, then two morphisms `Spec k ⟶ E` with the same composite to `V`, one of which hits `z`,
are equal.

The fibre condition forces the second morphism to hit `z` as well, and
`AlgebraicGeometry.residueFieldHom_eq_of_isPurelyInseparable` then identifies the two embeddings of
`κ(z)`. -/
public theorem eq_of_comp_eq_of_preimage_singleton_of_isPurelyInseparable {E V : Scheme.{u}}
    (g : E ⟶ V) (z : E) (hfib : g.base ⁻¹' {g.base z} = {z})
    {k : Type u} [Field k] (l l' : Spec (CommRingCat.of k) ⟶ E)
    (hcomp : l ≫ g = l' ≫ g) (hz : l.base (IsLocalRing.closedPoint k) = z)
    (hpure : (g.residueFieldMap z).hom.IsPurelyInseparable) :
    l = l' := by
  have hz' := base_closedPoint_eq_of_comp_eq_of_preimage_singleton g z hfib l' (l ≫ g)
    hcomp.symm (congrArg g.base hz)
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k E).symm.surjective l
  obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField k E).symm.surjective l'
  have hbp : ∀ (q : E) (ψ : E.residueField q ⟶ CommRingCat.of k),
      ((Scheme.SpecToEquivOfField k E).symm ⟨q, ψ⟩).base
        (IsLocalRing.closedPoint k) = q := by
    intro q ψ
    rw [Scheme.SpecToEquivOfField_symm_apply]
    exact Scheme.fromSpecResidueField_apply q _
  have hpz : p = z := (hbp p φ).symm.trans hz
  have hp'z : p' = z := (hbp p' φ').symm.trans hz'
  subst hpz hp'z
  rw [Scheme.SpecToEquivOfField_symm_apply, Scheme.SpecToEquivOfField_symm_apply] at hcomp ⊢
  rw [residueFieldHom_eq_of_isPurelyInseparable g p' φ φ' hpure hcomp]

/-- The `Subsingleton` form of the uniqueness of the lift: over a fixed morphism `v : Spec k ⟶ V`
hitting the image of `z`, the morphisms `Spec k ⟶ E` lifting it form a subsingleton. -/
public theorem subsingleton_lift_of_preimage_singleton_of_isPurelyInseparable {E V : Scheme.{u}}
    (g : E ⟶ V) (z : E) (hfib : g.base ⁻¹' {g.base z} = {z})
    {k : Type u} [Field k] (v : Spec (CommRingCat.of k) ⟶ V)
    (hv : v.base (IsLocalRing.closedPoint k) = g.base z)
    (hpure : (g.residueFieldMap z).hom.IsPurelyInseparable) :
    Subsingleton {l : Spec (CommRingCat.of k) ⟶ E // l ≫ g = v} :=
  ⟨fun l l' => Subtype.ext <|
    eq_of_comp_eq_of_preimage_singleton_of_isPurelyInseparable g z hfib l.1 l'.1
      (l.2.trans l'.2.symm)
      (base_closedPoint_eq_of_comp_eq_of_preimage_singleton g z hfib l.1 v l.2 hv) hpure⟩

end AlgebraicGeometry

end
