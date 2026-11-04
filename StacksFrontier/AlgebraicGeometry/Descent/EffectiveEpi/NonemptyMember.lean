module

public import StacksFrontier.CategoryTheory.Sites.Representable.EffectiveEpiFamily

/-!
# Nonempty members of effective epimorphic families over a field

An effective epimorphic family of schemes, or of affine schemes, whose target is the
spectrum of a field has a member whose underlying topological space is nonempty. This is the
pointwise input to joint surjectivity of a universal effective epimorphic family: base
changing to the residue field of a point reduces surjectivity at that point to this
statement.

## Main results

* `AlgebraicGeometry.exists_nonempty_scheme_of_isEffectiveEpiFamily` is the statement in the
  category of schemes.
* `AlgebraicGeometry.exists_nonempty_affineScheme_of_isEffectiveEpiFamily` is the statement
  in the category of affine schemes.

## Implementation notes

Both follow from a purely categorical lemma: if every member of an effective epimorphic
family admits at most one map to a fixed object `Y` whenever a chosen type is empty, then two
distinct maps out of the target force some member's type to be nonempty. Taking `Y` to be the
spectrum of `k × k` and the two maps to be induced by the projections supplies the required
pair. For an affine scheme, nonemptiness refers to the underlying scheme.

## References

* [Stacks Project, Lemma 35.13.3 (Tag 0EUB)](https://stacks.math.columbia.edu/tag/0EUB)
-/

@[expose] public section

universe w u

namespace AlgebraicGeometry

open CategoryTheory Opposite

/-- If each member of an effective epimorphic family has at most one map to `Y` as soon as
`Q i` is empty, then two distinct maps from the target to `Y` force some `Q i` to be
nonempty. -/
private theorem exists_nonempty_of_isEffectiveEpiFamily
    {C : Type (u + 1)} [Category.{u} C] {I : Type w} {B Y : C}
    (X : I → C) (p : ∀ i, X i ⟶ B)
    (h : StacksEffectiveEpi.IsEffectiveEpiFamily X p)
    (Q : I → Type u)
    (empty_hom : ∀ i, IsEmpty (Q i) → ∀ a b : X i ⟶ Y, a = b)
    (a b : B ⟶ Y) (hab : a ≠ b) :
    ∃ i, Nonempty (Q i) := by
  by_contra hn
  have hp : ∀ i, p i ≫ a = p i ≫ b := fun i ↦ empty_hom i ⟨fun x ↦ hn ⟨i, ⟨x⟩⟩⟩ _ _
  obtain ⟨t, ht, ht_unique⟩ := h.2 Y (fun i ↦ p i ≫ a) fun i j Z r s hrs ↦ by
    rw [← Category.assoc, ← Category.assoc, hrs.w]
  exact hab ((ht_unique a fun _ ↦ rfl).trans (ht_unique b fun i ↦ (hp i).symm).symm)

/-- The two projections `k × k ⟶ k` are distinct ring homomorphisms. -/
private theorem ofHom_fst_ne_ofHom_snd (k : Type u) [Field k] :
    CommRingCat.ofHom (RingHom.fst k k) ≠ CommRingCat.ofHom (RingHom.snd k k) := fun e ↦ by
  simpa using congr_arg (fun q ↦ q.hom (1, 0)) e

/-- An effective epimorphic family of schemes over the spectrum of a field has a nonempty
member. -/
theorem exists_nonempty_scheme_of_isEffectiveEpiFamily
    {k : Type u} [Field k] {I : Type w}
    (V : I → Scheme.{u})
    (f : ∀ i, V i ⟶ Spec (CommRingCat.of k))
    (h : StacksEffectiveEpi.IsEffectiveEpiFamily V f) :
    ∃ i, Nonempty (V i) := by
  refine exists_nonempty_of_isEffectiveEpiFamily V f h (fun i ↦ V i)
    (Y := Spec (CommRingCat.of (k × k)))
    (fun i hi a b ↦ by
      let _ : IsEmpty (V i) := hi
      exact (isInitialOfIsEmpty (X := V i)).hom_ext a b)
    (Spec.map (CommRingCat.ofHom (RingHom.fst k k)))
    (Spec.map (CommRingCat.ofHom (RingHom.snd k k)))
    fun e ↦ ofHom_fst_ne_ofHom_snd k (Spec.map_injective e)

/-- An effective epimorphic family of affine schemes over the spectrum of a field has a
nonempty member. -/
theorem exists_nonempty_affineScheme_of_isEffectiveEpiFamily
    {k : Type u} [Field k] {I : Type w}
    (V : I → AffineScheme.{u})
    (f : ∀ i, V i ⟶ AffineScheme.Spec.obj (op (CommRingCat.of k)))
    (h : StacksEffectiveEpi.IsEffectiveEpiFamily V f) :
    ∃ i, Nonempty (V i).obj := by
  refine exists_nonempty_of_isEffectiveEpiFamily V f h (fun i ↦ (V i).obj)
    (Y := AffineScheme.Spec.obj (op (CommRingCat.of (k × k))))
    (fun i hi a b ↦ by
      let _ : IsEmpty (V i).obj := hi
      exact AffineScheme.forgetToScheme.map_injective
        ((isInitialOfIsEmpty (X := (V i).obj)).hom_ext _ _))
    (AffineScheme.Spec.map (CommRingCat.ofHom (RingHom.fst k k)).op)
    (AffineScheme.Spec.map (CommRingCat.ofHom (RingHom.snd k k)).op)
    fun e ↦ ofHom_fst_ne_ofHom_snd k (Quiver.Hom.op_inj (AffineScheme.Spec.map_injective e))

end AlgebraicGeometry
