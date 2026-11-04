module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Points of a fibre product above a point with an isomorphic residue field

Let `f : X ⟶ S` and `g : Z ⟶ S` be morphisms of schemes and let `z : Z` be a point at which the
residue field map `κ(g z) ⟶ κ(z)` of `g` is an isomorphism. Then every point `x : X` with
`f x = g z` has exactly one preimage in `X ×_S Z`, and at that preimage the residue field map of
`pullback.fst f g` is an isomorphism: the fibre product does not split the point `(x, z)` and does
not enlarge the residue field of `x`.

Both statements come from the classification of the points of a fibre product,
`AlgebraicGeometry.Scheme.Pullback.carrierEquiv`: the points above `(x, z)` are the primes of
`κ(x) ⊗_{κ(g z)} κ(z)`, and when `κ(g z) ⟶ κ(z)` is an isomorphism so is the canonical map
`κ(x) ⟶ κ(x) ⊗_{κ(g z)} κ(z)`, since a pushout along an isomorphism is one. A field has a unique
prime, which gives the uniqueness of the point, and the tensor product mediates the residue field
of the fibre product at it, which gives the statement about residue fields.

## Main results

* `AlgebraicGeometry.Scheme.Pullback.exists_unique_point_of_isIso_residueFieldMap`: there is
  exactly one point of `X ×_S Z` above `x` and `z`.
* `AlgebraicGeometry.Scheme.Pullback.isIso_residueFieldMap_fst_of_isIso_residueFieldMap`: at such
  a point the residue field map of `pullback.fst f g` is an isomorphism.

## Implementation notes

`AlgebraicGeometry.Scheme.Pullback.Triplet.tensor` is a pushout of residue fields in
`CommRingCat`, so the isomorphism `κ(x) ⟶ κ(x) ⊗_{κ(g z)} κ(z)` is Mathlib's
`CategoryTheory.Limits.pushout_inl_iso_of_right_iso` rather than a computation with
`Algebra.TensorProduct.rid`; this avoids transporting the hypothesis across the comparison
between the pushout and the concrete tensor product.

Uniqueness is proved by injectivity of `carrierEquiv`, with the two primes identified by the
subsingleton instance on the spectrum of a field pulled back along the surjection
`κ(x) ⟶ κ(x) ⊗_{κ(g z)} κ(z)`.

The residue field statement is proved from the splitting criterion for a map of fields into a
residue field: such a map is injective, and a factorization of the canonical morphism from the
residue field through its `Spec` splits it, so it is both a monomorphism and a split epimorphism.
Here the factorization is Mathlib's `AlgebraicGeometry.Scheme.Pullback.ofPointTensor_SpecTensorTo`
corrected by the inverse of the pushout isomorphism. The same criterion is used, as a file-local
lemma, in `StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points`.

## References

* [Stacks Project, Tag 01JT](https://stacks.math.columbia.edu/tag/01JT)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {X Z S : Scheme.{u}} {f : X ⟶ S} {g : Z ⟶ S}

/-- If the residue field map of `g` at `T.y` is an isomorphism, then so is the canonical map
`κ(T.x) ⟶ κ(T.x) ⊗_{κ(T.s)} κ(T.y)`, being a pushout of an isomorphism. -/
private lemma isIso_tensorInl (T : Triplet f g) (hres : IsIso (g.residueFieldMap T.y)) :
    IsIso T.tensorInl := by
  have := hres
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) := inferInstance
  change IsIso (pushout.inl ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
    ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
  infer_instance

/-- If the residue field map of `g` at `T.y` is an isomorphism, then `κ(T.x) ⊗_{κ(T.s)} κ(T.y)`
has a unique prime, so the points of the fibre product above `(T.x, T.y)` are unique. -/
private lemma subsingleton_spec_tensor (T : Triplet f g)
    (hres : IsIso (g.residueFieldMap T.y)) : Subsingleton ↥(Spec T.tensor) := by
  have := isIso_tensorInl T hres
  exact (PrimeSpectrum.comap_injective_of_surjective (T.tensorInl).hom
    (ConcreteCategory.bijective_of_isIso T.tensorInl).2).subsingleton

/-- Let `f : X ⟶ S` and `g : Z ⟶ S` be morphisms of schemes, let `z : Z` be a point at which the
residue field map of `g` is an isomorphism, and let `x : X` be a point with `f x = g z`. Then
`X ×_S Z` has exactly one point above `x` and `z`. -/
public theorem exists_unique_point_of_isIso_residueFieldMap
    {X Z S : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) (x : X) (z : Z)
    (hxz : f x = g z) (hres : IsIso (g.residueFieldMap z)) :
    ∃! w : ↥(pullback f g), pullback.fst f g w = x ∧ pullback.snd f g w = z := by
  obtain ⟨w, hw₁, hw₂⟩ := exists_preimage_pullback x z hxz
  subst hw₁ hw₂
  -- `(carrierEquiv w).fst` is the triple `(x, z, f x)`, so its tensor product is `κ(x)`.
  have : Subsingleton ↥(Spec (carrierEquiv w).fst.tensor) := subsingleton_spec_tensor _ hres
  refine ⟨w, ⟨rfl, rfl⟩, fun v hv ↦ carrierEquiv.injective (carrierEquiv_eq_iff.mpr ?_)⟩
  exact ⟨Triplet.ext hv.1 hv.2, Subsingleton.elim _ _⟩

/-- Let `f : X ⟶ S` and `g : Z ⟶ S` be morphisms of schemes and let `z : Z` be a point at which
the residue field map of `g` is an isomorphism. Then at a point `w` of `X ×_S Z` above `x : X`
and `z`, the residue field map `κ(x) ⟶ κ(w)` of `pullback.fst f g` is an isomorphism. -/
public theorem isIso_residueFieldMap_fst_of_isIso_residueFieldMap
    {X Z S : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S) (x : X) (z : Z)
    (hres : IsIso (g.residueFieldMap z)) (w : ↥(pullback f g))
    (hw₁ : pullback.fst f g w = x) (hw₂ : pullback.snd f g w = z) :
    IsIso ((pullback.fst f g).residueFieldMap w) := by
  subst hw₂
  cases hw₁
  obtain ⟨ι, -, hι⟩ := (isIso_tensorInl (Triplet.ofPoint w) hres).out
  have hfac : (Triplet.ofPoint w).tensorInl ≫ ofPointTensor w =
      (pullback.fst f g).residueFieldMap w :=
    pushout.inl_desc _ _ (residueFieldCongr_inv_residueFieldMap_ofPoint w)
  -- The canonical morphism from `Spec κ(x)` to the fibre product through the tensor product.
  have htri : Spec.map ((Triplet.ofPoint w).tensorInl ≫ ofPointTensor w) ≫
      Spec.map ι ≫ (Triplet.ofPoint w).SpecTensorTo =
      (pullback f g).fromSpecResidueField w := by
    rw [Spec.map_comp, Category.assoc,
      ← Category.assoc (Spec.map (Triplet.ofPoint w).tensorInl), ← Spec.map_comp, hι,
      Spec.map_id, Category.id_comp, ofPointTensor_SpecTensorTo]
  -- A map of fields into a residue field whose `Spec` factors the canonical morphism from that
  -- residue field is an isomorphism: it is injective, and the factorization splits it.
  have key : ∀ {K : Type u} [Field K] (ψ : CommRingCat.of K ⟶ (pullback f g).residueField w)
      (a : Spec (CommRingCat.of K) ⟶ pullback f g),
      Spec.map ψ ≫ a = (pullback f g).fromSpecResidueField w → IsIso ψ := by
    intro K _ ψ a h
    obtain ⟨⟨y, k⟩, rfl⟩ := (Scheme.SpecToEquivOfField K (pullback f g)).symm.surjective a
    simp only [Scheme.SpecToEquivOfField_symm_apply] at h
    have hy : y = w := by
      have h₁ : (pullback f g).fromSpecResidueField y (Spec.map k (Spec.map ψ default)) =
          (pullback f g).fromSpecResidueField w default :=
        congrArg (fun m : Spec ((pullback f g).residueField w) ⟶ pullback f g ↦ m default) h
      simpa using h₁
    subst y
    have : Mono ψ := ConcreteCategory.mono_of_injective ψ ψ.hom.injective
    have : IsSplitEpi ψ := ⟨⟨k, by
      simpa only [← Spec.map_inj, Spec.map_comp, Spec.map_id,
        ← cancel_mono ((pullback f g).fromSpecResidueField w), Category.assoc,
        Category.id_comp] using h⟩⟩
    exact isIso_of_mono_of_isSplitEpi ψ
  exact key _ _ (.trans (congrArg
    (fun u ↦ Spec.map u ≫ Spec.map ι ≫ (Triplet.ofPoint w).SpecTensorTo) hfac.symm) htri)

end AlgebraicGeometry.Scheme.Pullback
