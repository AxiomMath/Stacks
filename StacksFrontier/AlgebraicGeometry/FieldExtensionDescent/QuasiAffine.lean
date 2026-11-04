module

public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.AmpleOpening
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.FiniteDegree
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.ResidueField
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.NormQuasiAffine.Basic

/-!
# Quasi-affineness descends along any field extension

Let `X` be a scheme over a field `k`. If the base change `X_K` of `X` to some field extension
`K/k` is quasi-affine, then `X` is quasi-affine.

## Main results

* `AlgebraicGeometry.isQuasiAffine_of_finite_base_change`: if the base change of `X` along the
  spectrum of a nonzero finite `k`-algebra is quasi-affine, then so is `X`.
* `AlgebraicGeometry.isQuasiAffine_of_finiteType_base_change`: if the base change of `X` along the
  spectrum of a nonzero `k`-algebra of finite type is quasi-affine, then so is `X`.
* `AlgebraicGeometry.FieldExtensionDescent.exists_isQuasiAffine_baseChangeDiagram_obj`: if `X` is
  quasi-compact and quasi-separated and `X_K` is quasi-affine, then the base change of `X` to some
  finitely generated `k`-subalgebra of `K` is quasi-affine.
* `AlgebraicGeometry.isQuasiAffine_of_fieldExtension`: if `X_K` is quasi-affine for some field
  extension `K/k`, then `X` is quasi-affine.

## Implementation notes

The hypothesis of `AlgebraicGeometry.isQuasiAffine_of_fieldExtension` is stated at
`pullback f (Spec.map (algebraMap k K))`, while the limit presentation of the base change by the
finitely generated subalgebras of `K` is stated at `pullback (Spec.map (algebraMap k K)) f`. The
two are exchanged by `CategoryTheory.Limits.pullbackSymmetry`, whose components are isomorphisms
and hence affine morphisms.

## References

* [Stacks Project, Tag 0BDD](https://stacks.math.columbia.edu/tag/0BDD)
* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 01Z5](https://stacks.math.columbia.edu/tag/01Z5)
* [Stacks Project, Tag 0BD5](https://stacks.math.columbia.edu/tag/0BD5)
* [Stacks Project, Tag 0BCK](https://stacks.math.columbia.edu/tag/0BCK)
* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- If the base change of a scheme over a field `k` along the spectrum of a nonzero finite
`k`-algebra `A` is quasi-affine, then so is the scheme itself. -/
public theorem isQuasiAffine_of_finite_base_change (k A : Type u) [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] [Module.Finite k A] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (h : Scheme.IsQuasiAffine
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f)) :
    Scheme.IsQuasiAffine X :=
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) (Module.finrank k A) :=
    isFiniteLocallyFreeOfRank_SpecMap_algebraMap k A
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) f) (Module.finrank k A) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (f := Spec.map (CommRingCat.ofHom (algebraMap k A))) (d := Module.finrank k A)
      (IsPullback.of_hasPullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f)
  Stacks.Divisors.isQuasiAffine_of_isFiniteLocallyFreeOfRank
    (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k A))) f) (Module.finrank k A)
    Module.finrank_pos

/-- If the base change of a scheme over a field `k` along the spectrum of a nonzero `k`-algebra
`A` of finite type is quasi-affine, then so is the scheme itself. -/
public theorem isQuasiAffine_of_finiteType_base_change (k A : Type u) [Field k] [CommRing A]
    [Nontrivial A] [Algebra k A] [Algebra.FiniteType k A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (h : Scheme.IsQuasiAffine
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k A))) f)) :
    Scheme.IsQuasiAffine X := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have hfin : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ m))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ m))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨r, hr⟩ := exists_isAffineHom_pullback_of_comp
    (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ m))))
    (Spec.map (CommRingCat.ofHom (algebraMap k A))) f
  exact isQuasiAffine_of_finite_base_change k (A ⧸ m) f
    (Scheme.IsQuasiAffine.of_isAffineHom ((pullback.congrHom hspec rfl).hom ≫ r))

end AlgebraicGeometry

namespace AlgebraicGeometry.FieldExtensionDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X] (f : X ⟶ Spec (.of k))

/-- If the base change `X_K` of a quasi-compact and quasi-separated scheme `X` over `k` is
quasi-affine, then so is the base change of `X` to some finitely generated `k`-subalgebra of
`K`. -/
public theorem exists_isQuasiAffine_baseChangeDiagram_obj
    (h : Scheme.IsQuasiAffine
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)) :
    ∃ i : (FGSubalgebra k K)ᵒᵖ, Scheme.IsQuasiAffine ((baseChangeDiagram k K f).obj i) :=
  have : Scheme.IsQuasiAffine (baseChangeLimitCone k K f).cone.pt := h
  Scheme.exists_isQuasiAffine_of_isLimit' (baseChangeDiagram k K f) _
    (baseChangeLimitCone k K f).isLimit

end AlgebraicGeometry.FieldExtensionDescent

namespace AlgebraicGeometry

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

/-- Let `k` be a field and `X` a scheme over `k`. If `X_K` is quasi-affine for some field
extension `K/k`, then `X` is quasi-affine. -/
@[stacks 0BDD]
public theorem isQuasiAffine_of_fieldExtension
    (h : Scheme.IsQuasiAffine
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) :
    Scheme.IsQuasiAffine X := by
  have hsymm : Scheme.IsQuasiAffine
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) f) :=
    Scheme.IsQuasiAffine.of_isAffineHom
      (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap k K))) f).hom
  have hcs : CompactSpace X :=
    compactSpace_of_surjective (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)
  have hqs : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_surjective_of_quasiCompact
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) f)
  obtain ⟨i, hi⟩ :=
    FieldExtensionDescent.exists_isQuasiAffine_baseChangeDiagram_obj k K f hsymm
  exact isQuasiAffine_of_finiteType_base_change k (i.unop : Subalgebra k K) f hi

end AlgebraicGeometry

end
