module

public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelativeSizeBound

/-!
# Glueing affine base changes over a scheme under a uniform ring-size bound

Let `T` be an object of the big fppf site over `S` and `π : F ⟶ yoneda.obj T` a morphism from a
sheaf. Suppose `T` is covered by affine open objects `V i ⟶ T` of the site and the base change of
`π` to each `V i` is represented by an affine object `W i` whose ring of global sections has
cardinality at most a single cardinal `κ` below the cutoff. Then `F` is represented by an object
of the site, affine over `T`. No bound is asked of the index type of the covering.

The uniform bound cannot be dropped: over a cutoff of cofinality `ℵ₁` a disjoint union of `ℵ₁`
spectra of fields, with polynomial rings in cofinally many variables over each, glues to a scheme
of size at least the cutoff. With it, every chart has size `max ℵ₀ #Γ(W i, ⊤) ≤ max ℵ₀ κ`
(Stacks 000P).

## Main results

* `AlgebraicGeometry.Space.exists_representing_affine_over_of_openCover_of_mk_le`: a sheaf over
  `T` whose base changes to an affine open covering of `T` are represented by affine objects with
  rings of global sections of cardinality at most `κ < B.cutoff` is represented by an object of
  the site, affine over `T`.

## References

* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Glueing affine base changes under a uniform bound on their rings.** A sheaf `F` over an
object `T` of the big fppf site whose base change to each member of an affine open covering of
`T` is represented by an affine object with ring of global sections of cardinality at most one
cardinal `κ` below the cutoff is represented by an object of the site, affine over `T`. The index
type of the covering is arbitrary. -/
theorem exists_representing_affine_over_of_openCover_of_mk_le
    {T : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) (π : F ⟶ yoneda.obj T)
    {ι : Type u} {V W : ι → BigFppfOver B S hS}
    {u : ∀ i, V i ⟶ T} {p : ∀ i, W i ⟶ V i} {q : ∀ i, yoneda.obj (W i) ⟶ F}
    (hu : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (u i)))
    (hucov : ∀ y : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u i)))
    (hpb : ∀ i, IsPullback (q i) (yoneda.map (p i)) π (yoneda.map (u i)))
    (hV : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i)))
    (hW : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W i)))
    {κ : Cardinal.{u}} (hκ : κ < B.cutoff)
    (hΓ : ∀ i, #Γ((BigFppfOver.toScheme B S hS).obj (W i), ⊤) ≤ κ) :
    ∃ (Y : BigFppfOver B S hS) (e : F ≅ yoneda.obj Y) (P : Y ⟶ T),
      e.inv ≫ π = yoneda.map P ∧
        _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map P) :=
  exists_representing_over_of_openCover_of_size_le B S hS isZariskiLocalAtTarget_isAffineHom hF
    π hu hucov hpb (fun i => by have := hV i; have := hW i; infer_instance)
    (max_lt B.aleph0_lt_cutoff hκ) fun i => by
      have := hW i
      rw [Scheme.size_of_isAffine]
      exact max_le_max le_rfl (hΓ i)

end AlgebraicGeometry.Space

end
