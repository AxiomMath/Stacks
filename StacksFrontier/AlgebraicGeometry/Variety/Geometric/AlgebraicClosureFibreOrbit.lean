module

public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.GaloisInvariantClosed
public import StacksFrontier.RingTheory.TensorProduct.AlgebraicClosureOrbit
import all StacksFrontier.AlgebraicGeometry.Variety.Geometric.GaloisInvariantClosed

/-!
# The automorphisms of an algebraic closure act transitively on a geometric fibre

For a scheme `X` over a field `k` and an algebraic closure `K` of `k`, the self-maps of
`X ×_{Spec k} Spec K` induced by `k`-automorphisms of `K` are isomorphisms, and they act
transitively on the points of the base change lying above a fixed point of `X`.

The base field is **arbitrary**.  The companion result
`AlgebraicGeometry.galoisBaseChangeMap_fiber_orbit` asks for `IsGalois k K`, which fails for an
algebraic closure over an imperfect field, and it is not merely unprovable there: the
fixed-field statement `Algebra.IsInvariant` it rests on is false, because a purely inseparable
element of `K` is fixed by every `k`-automorphism.  What replaces it is
`Stacks.AlgClosureOrbit.exists_algEquiv_comap_eq`, which needs no separability.

## Main results

* `AlgebraicGeometry.isIso_galoisBaseChangeMap` — the self-map induced by a `k`-automorphism of
  the extension is an isomorphism.
* `AlgebraicGeometry.exists_galoisBaseChangeMap_base_eq_of_isAlgClosure` — two points of the
  base change with the same image in `X` lie in one orbit.

## Implementation notes

The reduction to the affine case follows
`AlgebraicGeometry.galoisBaseChangeMap_fiber_orbit`, with one change that removes the need for
a general base ring: rather than an affine open chart around the point, the chart used is
`X.fromSpecResidueField x`, whose source is the spectrum of a **field**.  That is what lets the
algebraic input be stated for a field extension `κ/k` rather than for an arbitrary
`k`-algebra, and it also makes two steps free — the source of the chart is a one-point space,
so the two points of the fibre of the chart's base change automatically agree over it, and the
prime of `κ ⊗[k] K` contracts to the zero ideal of `κ` on both sides, so no hypothesis
relating the two contractions is needed.

The identification of the base change of `Spec κ` with `Spec (κ ⊗[k] K)`, and the fact that the
self-map corresponds to the automorphism of the tensor product, are
`AlgebraicGeometry.galoisBaseChangeMap_pullbackSpecIso`; it carries no separability hypothesis,
which is why the `import all` above reaches it rather than restating it.

## References

* [Stacks Project, Tag 04KP](https://stacks.math.columbia.edu/tag/04KP)
* [Stacks Project, Tag 038B](https://stacks.math.columbia.edu/tag/038B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **The self-map of a base change induced by a `k`-automorphism of the extension is an
isomorphism**, with inverse the self-map induced by the inverse automorphism. -/
theorem isIso_galoisBaseChangeMap (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) (σ : K ≃ₐ[k] K) :
    IsIso (galoisBaseChangeMap k K X f σ) := by
  have key : ∀ τ : K ≃ₐ[k] K,
      CommRingCat.ofHom τ.symm.toRingEquiv.toRingHom ≫
        CommRingCat.ofHom τ.toRingEquiv.toRingHom = 𝟙 (CommRingCat.of K) := by
    intro τ
    apply CommRingCat.hom_ext
    ext b
    change τ (τ.symm b) = b
    simp
  have hcomp : ∀ τ : K ≃ₐ[k] K,
      galoisBaseChangeMap k K X f τ ≫ galoisBaseChangeMap k K X f τ.symm = 𝟙 _ := by
    intro τ
    apply pullback.hom_ext
    · rw [Category.assoc, galoisBaseChangeMap_fst, galoisBaseChangeMap_fst, Category.id_comp]
    · rw [Category.assoc, galoisBaseChangeMap_snd, ← Category.assoc, galoisBaseChangeMap_snd,
        Category.assoc, ← AlgebraicGeometry.Spec.map_comp, key, AlgebraicGeometry.Spec.map_id,
        Category.comp_id, Category.id_comp]
  exact ⟨galoisBaseChangeMap k K X f σ.symm, hcomp σ,
    by simpa only [AlgEquiv.symm_symm] using hcomp σ.symm⟩

/-- **The self-map of a base change induced by a `k`-automorphism is natural in the scheme.** -/
private theorem pullback_map_comp_galoisBaseChangeMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k)) (i : Y ⟶ X)
    (hi : fY = i ≫ f) (σ : K ≃ₐ[k] K) :
    pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) i (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hi]) (by simp) ≫ galoisBaseChangeMap k K X f σ =
      galoisBaseChangeMap k K Y fY σ ≫
        pullback.map fY (Spec.map (CommRingCat.ofHom (algebraMap k K))) f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) i (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, hi]) (by simp) := by
  apply pullback.hom_ext
  · rw [Category.assoc, galoisBaseChangeMap_fst, Category.assoc]
    dsimp only [pullback.map]
    rw [pullback.lift_fst, ← Category.assoc, galoisBaseChangeMap_fst]
  · rw [Category.assoc, galoisBaseChangeMap_snd, Category.assoc]
    dsimp only [pullback.map]
    rw [← Category.assoc, pullback.lift_snd, Category.comp_id]
    exact (galoisBaseChangeMap_snd k K Y fY σ).symm

/-- **Over the spectrum of a field extension `R/k`, any two points of the base change to an
algebraic closure of `k` lie in one orbit of its automorphism group.** -/
private theorem exists_galoisBaseChangeMap_base_eq_of_isAlgClosure_of_field
    (k R K : Type u) [Field k] [Field R] [Field K] [Algebra k R] [Algebra k K]
    [IsAlgClosure k K]
    (y z : (pullback (Spec.map (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    ∃ σ : K ≃ₐ[k] K, (galoisBaseChangeMap k K (Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) σ).base y = z := by
  let e := pullbackSpecIso k R K
  let p : PrimeSpectrum (R ⊗[k] K) := e.hom.base y
  let p' : PrimeSpectrum (R ⊗[k] K) := e.hom.base z
  obtain ⟨σ, hσ⟩ := Stacks.AlgClosureOrbit.exists_algEquiv_comap_eq k R K p.asIdeal p'.asIdeal
  have hpSpec : PrimeSpectrum.comap (tensorGaloisAut k K R σ).toRingEquiv.toRingHom p = p' :=
    PrimeSpectrum.ext hσ
  refine ⟨σ, e.hom.isEmbedding.injective ?_⟩
  rw [galoisBaseChangeMap_pullbackSpecIso k K R σ]
  have hinv : e.inv.base (PrimeSpectrum.comap
      (tensorGaloisAut k K R σ).toRingEquiv.toRingHom p) = z := by
    simpa [p'] using congrArg e.inv.base hpSpec
  exact congrArg e.hom.base hinv

/-- **Two points of the base change of a scheme to an algebraic closure that have the same
image in the scheme lie in one orbit of the automorphism group of the closure.**  The base
field is arbitrary; no separability is assumed. -/
theorem exists_galoisBaseChangeMap_base_eq_of_isAlgClosure
    (k K : Type u) [Field k] [Field K] [Algebra k K] [IsAlgClosure k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    (y z : (pullback f (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hyz : (pullback.fst f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))).base y =
      (pullback.fst f (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k K)))).base z) :
    ∃ σ : K ≃ₐ[k] K, (galoisBaseChangeMap k K X f σ).base y = z := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let x := (pullback.fst f g).base y
  let R : Type u := ↥(X.residueField x)
  let i : Spec (CommRingCat.of R) ⟶ X := X.fromSpecResidueField x
  let φ : CommRingCat.of k ⟶ CommRingCat.of R := Spec.preimage (i ≫ f)
  let _ : Algebra k R := φ.hom.toAlgebra
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap k R)) = i ≫ f := Spec.map_preimage _
  let m := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap k R))) g f g i
    (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hbase]) (by simp)
  have hmap : Set.range m.base = (pullback.fst f g).base ⁻¹' {x} := by
    rw [← X.range_fromSpecResidueField x, Scheme.Pullback.range_map]
    simp [g, i]
  obtain ⟨yR, hyR⟩ : y ∈ Set.range m.base := by rw [hmap]; rfl
  obtain ⟨zR, hzR⟩ : z ∈ Set.range m.base := by rw [hmap]; exact hyz.symm
  obtain ⟨σ, hσ⟩ := exists_galoisBaseChangeMap_base_eq_of_isAlgClosure_of_field k R K yR zR
  refine ⟨σ, ?_⟩
  rw [← hyR, ← hzR, ← hσ, ← Scheme.Hom.comp_apply,
    pullback_map_comp_galoisBaseChangeMap k K f _ i hbase σ, Scheme.Hom.comp_apply]

end AlgebraicGeometry

end
