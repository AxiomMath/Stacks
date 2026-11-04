module

public import Mathlib.Algebra.Field.ULift
public import StacksFrontier.Algebra.Homology.SpectralSequence.KunnethTor
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.VanishingOverField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Künneth isomorphism over a field

Let `k` be a field and let `K` and `L` be cohomologically bounded complexes of `k`-vector
spaces. The Künneth short exact sequence
```
0 ⟶ ⨁_{i + j = n} Hⁱ(K) ⊗ Hʲ(L) ⟶ Hⁿ(K ⊗^L L) ⟶ ⨁_{i + j = n + 1} Tor₁(Hⁱ(K), Hʲ(L)) ⟶ 0
```
of a Dedekind domain applies to `k`, and its third term vanishes because every `k`-module is
flat. Hence the first edge map is an isomorphism and the cohomology of the derived tensor
product is the direct sum of the tensor products of the cohomologies.

## Main results

* `CochainComplex.Kunneth.nonempty_kunnethIso_of_field`: over a field the cohomology of the
  derived tensor product of two cohomologically bounded complexes is the direct sum of the
  tensor products of their cohomology modules in complementary degrees.

## Implementation notes

As in the Künneth short exact sequence, the field and the two complexes have independent
universes; they are lifted to a common universe and their scalars transported along
`ULift.ringEquiv`, because the monoidal structure on modules requires the modules and the ring
to share a universe. The isomorphism is therefore stated for the transported complexes.

The derived tensor product appearing in the conclusion is the canonical one, identified with
the ordinary total tensor product of the K-flat replacements produced by the Künneth spectral
sequence through the canonical comparison of `CochainComplex.DerivedTensor`.

## References

* [The Stacks Project, Tag 0H80](https://stacks.math.columbia.edu/tag/0H80)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex.Kunneth

universe u v w

/-- **The Künneth isomorphism over a field.** For two cohomologically bounded complexes of
vector spaces over a field, the `n`-th cohomology of the derived tensor product is the direct
sum of the tensor products `Hⁱ ⊗ Hʲ` over all `i + j = n`: the Künneth short exact sequence of
a Dedekind domain degenerates, since the first Tor module of two vector spaces vanishes. -/
@[ega "III 6.7.8.1" "special case"]
public theorem nonempty_kunnethIso_of_field (k : Type u) [Field k] :
    let S := ULift.{max v w} k
    let U : ModuleCat.{v} k ⥤ ModuleCat.{max u v w} S :=
      ModuleCat.uliftFunctor.{max u w} k ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom
    let V : ModuleCat.{w} k ⥤ ModuleCat.{max u v w} S :=
      ModuleCat.uliftFunctor.{max u v} k ⋙ ModuleCat.restrictScalars ULift.ringEquiv.toRingHom
    ∀ (K : CochainComplex (ModuleCat.{v} k) ℤ) (L : CochainComplex (ModuleCat.{w} k) ℤ)
      (aK bK aL bL : ℤ) [K.IsGE aK] [K.IsLE bK] [L.IsGE aL] [L.IsLE bL] (n : ℤ),
      let K' := (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      let L' := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      Nonempty ((∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = n} ↦
            K'.homology ij.1.1 ⊗ L'.homology ij.1.2) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{max u v w} S) n).obj
            (((canonicalDerivedTensorProductFunctor S).obj (DerivedCategory.Q.obj K')).obj
              (DerivedCategory.Q.obj L'))) := by
  classical
  dsimp only
  intro K L aK bK aL bL _ _ _ _ n
  obtain ⟨P, Q, f, g, hf, hg, hP, hQ, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, hlast⟩ :=
    (tor_isZero_and_exists_kunneth_shortExact.{u, v, w} k).2 K L aK bK aL bL
  obtain ⟨_, _, _, _, _, _, _, _, ι, π, hιπ, _, _, _, _, hSE⟩ := hlast n
  -- The third term of the Künneth sequence is a coproduct of first Tor modules of vector
  -- spaces, hence zero.
  have hz : IsZero (ShortComplex.mk ι π hιπ).X₃ :=
    (colimit.isColimit _).isZero_pt
      (Functor.isZero _ fun _ => isZero_Tor'_one_of_field _ _)
  have : Epi ι := hSE.exact.epi_f (hz.eq_of_tgt _ _)
  have : Mono ι := hSE.mono_f
  have : IsIso ι := isIso_of_mono_of_epi ι
  -- The K-flat replacements compute the derived tensor product.
  have := hf
  have := hg
  exact ⟨(asIso ι).trans (((DerivedCategory.homologyFunctor _ n).mapIso
      (((canonicalDerivedTensorProductFunctor _).mapIso
            (asIso (DerivedCategory.Q.map f)).symm).app _ ≪≫
          ((canonicalDerivedTensorProductFunctor _).obj
            (DerivedCategory.Q.obj P)).mapIso (asIso (DerivedCategory.Q.map g)).symm ≪≫
          (canonicalDerivedTensorProduct _).comparison P Q hP hQ) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app (P ⊗ Q)).symm)⟩

end CochainComplex.Kunneth

end
