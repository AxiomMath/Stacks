module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatGlobalFunctions

/-!
# Global functions under a field extension

Let `X` be a separated algebraic space over a field `k` whose structure morphism is flat and of
finite presentation, with `k = H⁰(X, 𝒪_X)`. Then `K = H⁰(X_K, 𝒪_{X_K})` for every field
extension `K/k`. This is flat base change for global functions (Cohomology of Spaces, Lemma
073K, in degree `0`): `X` has a surjective étale atlas `W` with `W` and `W ×_X W` affine, global
functions are the equalizer of the two restriction maps, and the exactness of the equalizer
sequence is preserved by the flat extension of scalars along `k → K`
(`AlgHom.EqualizerTensorExact.of_flat`).

## Main results

* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_fieldBaseChange`

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) {k : Type u} [Field k] {hk : B.Contains (Spec (.of k))}
  {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}

/-- **`k = H⁰(X, 𝒪)` is preserved by field extensions.** For a separated algebraic space `X`
over a field `k`, flat and of finite presentation over `k`, with `k = H⁰(X, 𝒪_X)`, every field
extension `K/k` whose spectrum lies in the site has `K = H⁰(X_K, 𝒪_{X_K})`. -/
theorem bijective_algebraMap_globalFunctions_fieldBaseChange
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk)))) (hsep : IsSeparated B (Spec (.of k)) hk f)
    (hflat : IsFlat B (Spec (.of k)) hk f) (hfp : IsFinitePresentation B (Spec (.of k)) hk f)
    (h : Function.Bijective (algebraMap k (globalFunctions B (Spec (.of k)) hk X)))
    (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K))) :
    Function.Bijective (algebraMap K
      (globalFunctions B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK))) := by
  obtain ⟨W, R, p, r₁, r₂, hps, hpe, hR, hW, hRa, -, -, -, -⟩ :=
    exists_affine_atlas_flat_finitePresentation B hX f hsep hflat hfp
  let := siteObjectAlgebra B k W
  let := siteObjectAlgebra B k R
  refine (bijective_algebraMap_globalFunctions_relocalizeRestrict_iff B X hX p hps hpe r₁ r₂ hR
    hW hRa (specMapOfExtension B k hk K hK) rfl).mpr ?_
  exact ((bijective_algebraMap_globalFunctions_iff B X hX p hps hpe r₁ r₂ hR).mp h).of_flat

end AlgebraicGeometry.Space

end
