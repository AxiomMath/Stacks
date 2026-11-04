module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine charts of a base change along an affine morphism of affine schemes

Let `f : X ⟶ S` be a morphism of affine schemes and `b : S' ⟶ S` any morphism. An affine chart
`c : Spec T ⟶ S'` of the second factor whose composite to `S` is `Spec` of the structure map of
`T` over `Γ(S, ⊤)` produces an affine chart

  `Spec (Γ(X, ⊤) ⊗_{Γ(S, ⊤)} T) ⟶ X ×_S S'`

of the base change, open whenever `c` is, and inducing on `X` the structure map
`Γ(X, ⊤) ⟶ Γ(X, ⊤) ⊗_{Γ(S, ⊤)} T` of the tensor product.

That last identity is what the chart-level computation of a strict transform
(`Stacks.StrictTransform.affineChartSheafIso`, and the predicate
`Stacks.StrictTransform.ChartFreeOfRank` built on it) asks of a chart, and it is why the charts
here are built at all: the conclusion of [Stacks, Tag 0810] is a statement about the chart
algebras `S ⊗_R R[I/a]`, and reading it on the strict transform of [Stacks, Tag 080D] requires
exhibiting those algebras as charts of the base change.

## Main definitions

* `Stacks.StrictTransform.affinePullbackSpecIso`: the fibre product of two affine schemes over an
  affine scheme is the spectrum of the tensor product of their global sections. This is
  `AlgebraicGeometry.pullbackSpecIso` with the two morphisms given as morphisms of schemes rather
  than as `Spec` of ring maps.
* `Stacks.StrictTransform.affineBaseChangeChartMap`: the chart of the base change described
  above.

## Main results

* `Stacks.StrictTransform.affinePullbackSpecIso_inv_fst` and
  `Stacks.StrictTransform.affinePullbackSpecIso_inv_snd`: the two projections of that
  identification.
* `Stacks.StrictTransform.isOpenImmersion_affineBaseChangeChartMap`: the chart is an open
  immersion when `c` is.
* `Stacks.StrictTransform.affineBaseChangeChartMap_fst`: the chart induces the structure map of
  the tensor product on `X`.
* `Stacks.StrictTransform.affineBaseChangeChartMap_snd`: the chart lies over `c` through
  `Algebra.TensorProduct.includeRight`.

## Implementation notes

The `Γ(S, ⊤)`-algebra structure on `Γ(X, ⊤)` is the one `f` induces, installed as a `let` in each
statement rather than assumed: `f.appTop.hom.toAlgebra`. Its structure map is `f.appTop` on the
nose, which is the bridge between `AlgebraicGeometry.Scheme.isoSpec_hom_naturality` — which
speaks of `Spec.map f.appTop` — and `AlgebraicGeometry.pullbackSpecIso`, which speaks of
`Spec.map (CommRingCat.ofHom (algebraMap _ _))`.

`AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion` gives the open immersion: the chart is the
identification above followed by `CategoryTheory.Limits.pullback.map` along `𝟙 X`, `c` and `𝟙 S`,
and the two outer legs are an open immersion and an identity.

## References

* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.StrictTransform

variable {X S S' : Scheme.{u}}

/-- **The fibre product of two affine schemes over an affine scheme is the spectrum of the tensor
product of their global sections.** This is `AlgebraicGeometry.pullbackSpecIso` for morphisms
`f : X ⟶ S` and `g : Spec T ⟶ S` of schemes, rather than for `Spec` of two ring maps: the
hypothesis `hg` presents `g` as `Spec` of the structure map of `T`, and
`AlgebraicGeometry.Scheme.isoSpec_hom_naturality` presents `f` as `Spec` of `f.appTop`. -/
public def affinePullbackSpecIso [IsAffine X] [IsAffine S] (f : X ⟶ S) (T : Type u) [CommRing T]
    [Algebra Γ(S, ⊤) T] (g : Spec (CommRingCat.of T) ⟶ S)
    (hg : g ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    pullback f g ≅ Spec (CommRingCat.of (Γ(X, ⊤) ⊗[Γ(S, ⊤)] T)) := by
  letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have he : CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤)) = f.appTop := by ext x; rfl
  have hf : f ≫ S.isoSpec.hom = X.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤))) := by
    simpa only [he] using (Scheme.isoSpec_hom_naturality f).symm
  have hg' : g ≫ S.isoSpec.hom =
      (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T)) := by
    simpa only [Category.id_comp] using hg
  exact asIso (pullback.map f g _ _ X.isoSpec.hom (𝟙 _) S.isoSpec.hom hf hg') ≪≫
    pullbackSpecIso Γ(S, ⊤) Γ(X, ⊤) T

/-- The two projections of `Stacks.StrictTransform.affinePullbackSpecIso` are those of
`AlgebraicGeometry.pullbackSpecIso`, the first read through `X.isoSpec`. -/
private theorem affinePullbackSpecIso_inv_comp [IsAffine X] [IsAffine S] (f : X ⟶ S) (T : Type u)
    [CommRing T] [Algebra Γ(S, ⊤) T] (g : Spec (CommRingCat.of T) ⟶ S)
    (hg : g ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (affinePullbackSpecIso f T g hg).inv ≫ pullback.fst f g ≫ X.isoSpec.hom =
        (pullbackSpecIso Γ(S, ⊤) Γ(X, ⊤) T).inv ≫ pullback.fst _ _ ∧
      (affinePullbackSpecIso f T g hg).inv ≫ pullback.snd f g =
        (pullbackSpecIso Γ(S, ⊤) Γ(X, ⊤) T).inv ≫ pullback.snd _ _ := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have hf : f ≫ S.isoSpec.hom = X.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤))) :=
    (Scheme.isoSpec_hom_naturality f).symm
  have hg' : g ≫ S.isoSpec.hom =
      (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T)) :=
    hg.trans (Category.id_comp _).symm
  set m := pullback.map f g (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) Γ(X, ⊤))))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T)))
    X.isoSpec.hom (𝟙 _) S.isoSpec.hom hf hg' with hm_def
  have hm : m ≫ pullback.fst _ _ = pullback.fst f g ≫ X.isoSpec.hom ∧
      m ≫ pullback.snd _ _ = pullback.snd f g := by
    simp only [hm_def, pullback.map, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
      and_self]
  have hinv : (affinePullbackSpecIso f T g hg).inv = (pullbackSpecIso Γ(S, ⊤) Γ(X, ⊤) T).inv ≫
      inv m := rfl
  rw [hinv, ← hm.1, ← hm.2]
  simp

/-- The projection to `X` of `Stacks.StrictTransform.affinePullbackSpecIso`, read through
`X.isoSpec`: it is `Spec` of the structure map `Γ(X, ⊤) ⟶ Γ(X, ⊤) ⊗_{Γ(S, ⊤)} T`. -/
public theorem affinePullbackSpecIso_inv_fst [IsAffine X] [IsAffine S] (f : X ⟶ S) (T : Type u)
    [CommRing T] [Algebra Γ(S, ⊤) T] (g : Spec (CommRingCat.of T) ⟶ S)
    (hg : g ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (affinePullbackSpecIso f T g hg).inv ≫ pullback.fst f g ≫ X.isoSpec.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] T))) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  exact (affinePullbackSpecIso_inv_comp f T g hg).1.trans
    (pullbackSpecIso_inv_fst' Γ(S, ⊤) Γ(X, ⊤) T)

/-- The projection to `Spec T` of `Stacks.StrictTransform.affinePullbackSpecIso`: it is `Spec` of
`Algebra.TensorProduct.includeRight`. -/
public theorem affinePullbackSpecIso_inv_snd [IsAffine X] [IsAffine S] (f : X ⟶ S) (T : Type u)
    [CommRing T] [Algebra Γ(S, ⊤) T] (g : Spec (CommRingCat.of T) ⟶ S)
    (hg : g ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (affinePullbackSpecIso f T g hg).inv ≫ pullback.snd f g =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        T →ₐ[Γ(S, ⊤)] Γ(X, ⊤) ⊗[Γ(S, ⊤)] T).toRingHom) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  exact (affinePullbackSpecIso_inv_comp f T g hg).2.trans
    (pullbackSpecIso_inv_snd Γ(S, ⊤) Γ(X, ⊤) T)

/-- **An affine chart of a base change.** For `f : X ⟶ S` with `X` and `S` affine, `b : S' ⟶ S`
any morphism and `c : Spec T ⟶ S'` a chart of `S'` whose composite to `S` is `Spec` of the
structure map of `T`, the spectrum of `Γ(X, ⊤) ⊗_{Γ(S, ⊤)} T` maps to `X ×_S S'`.

It is `Stacks.StrictTransform.affinePullbackSpecIso` for `c ≫ b` followed by the comparison of
`X ×_S Spec T` with `X ×_S S'`. -/
public def affineBaseChangeChartMap [IsAffine X] [IsAffine S] (f : X ⟶ S) (b : S' ⟶ S)
    (T : Type u) [CommRing T] [Algebra Γ(S, ⊤) T] (c : Spec (CommRingCat.of T) ⟶ S')
    (hc : (c ≫ b) ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    Spec (CommRingCat.of (Γ(X, ⊤) ⊗[Γ(S, ⊤)] T)) ⟶ pullback f b :=
  (affinePullbackSpecIso f T (c ≫ b) hc).inv ≫
    pullback.map f (c ≫ b) f b (𝟙 _) c (𝟙 _) (by simp) (by simp)

/-- The chart of a base change is an open immersion when the chart of the second factor is. -/
public theorem isOpenImmersion_affineBaseChangeChartMap [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (b : S' ⟶ S) (T : Type u) [CommRing T] [Algebra Γ(S, ⊤) T]
    (c : Spec (CommRingCat.of T) ⟶ S') [IsOpenImmersion c]
    (hc : (c ≫ b) ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    IsOpenImmersion (affineBaseChangeChartMap f b T c hc) := by
  dsimp only [affineBaseChangeChartMap]
  infer_instance

/-- **The chart of a base change induces the structure map of the tensor product on `X`.** -/
public theorem affineBaseChangeChartMap_fst [IsAffine X] [IsAffine S] (f : X ⟶ S) (b : S' ⟶ S)
    (T : Type u) [CommRing T] [Algebra Γ(S, ⊤) T] (c : Spec (CommRingCat.of T) ⟶ S')
    (hc : (c ≫ b) ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    (affineBaseChangeChartMap f b T c hc ≫ pullback.fst f b) ≫ X.isoSpec.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] T))) := by
  dsimp only [affineBaseChangeChartMap]
  simp only [Category.assoc, pullback.map, pullback.lift_fst_assoc, Category.id_comp]
  exact affinePullbackSpecIso_inv_fst f T (c ≫ b) hc

/-- **The chart of a base change lies over the chart of the second factor.** The projection to
`S'` is `Spec` of `Algebra.TensorProduct.includeRight` followed by `c`. -/
public theorem affineBaseChangeChartMap_snd [IsAffine X] [IsAffine S] (f : X ⟶ S) (b : S' ⟶ S)
    (T : Type u) [CommRing T] [Algebra Γ(S, ⊤) T] (c : Spec (CommRingCat.of T) ⟶ S')
    (hc : (c ≫ b) ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    affineBaseChangeChartMap f b T c hc ≫ pullback.snd f b =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        T →ₐ[Γ(S, ⊤)] Γ(X, ⊤) ⊗[Γ(S, ⊤)] T).toRingHom) ≫ c := by
  dsimp only [affineBaseChangeChartMap]
  simp only [Category.assoc, pullback.map, pullback.lift_snd]
  rw [← Category.assoc, affinePullbackSpecIso_inv_snd]

end Stacks.StrictTransform

end
