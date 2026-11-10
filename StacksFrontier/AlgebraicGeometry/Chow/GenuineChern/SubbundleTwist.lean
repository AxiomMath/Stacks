module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TwistPullbackIso
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymGenNatural

/-!
# The twist of `𝐏(𝒢)` restricts to the twist of `𝐏(𝒬)`

Let `g : 𝒢 ⟶ 𝒬` be an epimorphism of finite locally free modules on a scheme `X`, and
`ι : 𝐏(𝒬) ⟶ 𝐏(𝒢)` the induced closed immersion of projective bundles
(`Stacks.Chow.GenuineChern.bundleEmbedding`). Then `ι^*𝒪_{𝐏(𝒢)}(1) ≅ 𝒪_{𝐏(𝒬)}(1)`, by the unique
isomorphism carrying the pulled-back tautological quotient of `𝒢` to the tautological quotient of
`𝒬` precomposed with `g`.

## Main definitions

* `Stacks.Chow.GenuineChern.bundleEmbeddingTwistIso`: the isomorphism
  `ι^*(bundleTwist 𝒢) ≅ bundleTwist 𝒬`.

## Main results

* `Stacks.Chow.GenuineChern.existsUnique_bundleEmbeddingTwistIso`: its existence and uniqueness
  under the compatibility with the tautological quotients.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.Chow.GenuineChern

variable {X : Scheme.{u}} {G Q : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q]
  (g : G ⟶ Q) [Epi g]

/-- The embedding is a morphism over the base, in the form of a square over `𝟙 X`. -/
theorem bundleEmbedding_comp_toBase :
    bundleEmbedding g ≫ (relativeProj (schemeSheafGradedAlgebra G (bundlePieces G))).toBase =
      (relativeProj (schemeSheafGradedAlgebra Q (bundlePieces Q))).toBase ≫ 𝟙 X :=
  (bundleEmbedding_comp_bundleProj g).trans (Category.comp_id _).symm

/-- The composite of the identification `(𝟙 X)^*𝒢 ≅ 𝒢` with `g` is an epimorphism. -/
instance : Epi ((Scheme.Modules.pullbackId X).hom.app G ≫ g) :=
  @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso (((Scheme.Modules.pullbackId X).app G).hom)) _ ‹_›

/-- On affine charts, `bundleEmbedding g` is the morphism of `Proj`s induced by a morphism of
graded section algebras sending the degree-one generator of a section of `𝒢` to the degree-one
generator of its image in `𝒬`. -/
theorem bundleEmbedding_chart (x' : X) :
    ∃ (U' : X.Opens) (hU' : IsAffineOpen U') (_ : x' ∈ U') (U : X.Opens) (hU : IsAffineOpen U)
      (hUU' : U' ≤ (𝟙 X) ⁻¹ᵁ U)
      (φ : (schemeSheafGradedAlgebra G (bundlePieces G)).grading U →+*ᵍ
        (schemeSheafGradedAlgebra Q (bundlePieces Q)).grading U')
      (hφ : HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra Q (bundlePieces Q)).grading U') ≤
        (HomogeneousIdeal.irrelevant ((schemeSheafGradedAlgebra G (bundlePieces G)).grading U)).map
          φ),
      (relativeProj (schemeSheafGradedAlgebra Q (bundlePieces Q))).chart U' hU' ≫
          bundleEmbedding g =
        AlgebraicGeometry.Proj.map φ hφ ≫
          (relativeProj (schemeSheafGradedAlgebra G (bundlePieces G))).chart U hU ∧
      ∀ x : Γ(G, U),
        φ (DirectSum.of ((schemeSheafGradedAlgebra G (bundlePieces G)).sectionPieces U) 1
            ((Scheme.Modules.symmetricAlgebraGen X G).val.app (op U) x)) =
          DirectSum.of ((schemeSheafGradedAlgebra Q (bundlePieces Q)).sectionPieces U') 1
            ((Scheme.Modules.symmetricAlgebraGen X Q).val.app (op U')
              (Q.val.map (homOfLE hUU').op
                (((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv G Q
                  ((Scheme.Modules.pullbackId X).hom.app G ≫ g)).val.app (op U) x))) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := x') (U := ⊤) trivial
  refine ⟨U, hU, hxU, U, hU, le_rfl,
    (schemeSheafGradedAlgebraHom g (bundlePieces G) (bundlePieces Q)).sectionHom U,
    Stacks.AlgebraicGeometry.ProjBundleSurjection.irrelevant_le_map_sectionHom
      (surjectiveOnAffineSections_bundle g) hU, ?_, fun x => ?_⟩
  · refine (chart_comp_bundleEmbedding g U hU).trans ?_
    rw [Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap_eq_map]
    rfl
  · refine (sectionHom_of_symmetricAlgebraGen g (bundlePieces G) (bundlePieces Q) U x).trans ?_
    refine congrArg (fun z => DirectSum.of
      ((schemeSheafGradedAlgebra Q (bundlePieces Q)).sectionPieces U) 1
        ((Scheme.Modules.symmetricAlgebraGen X Q).val.app (op U) z)) ?_
    refine Eq.trans ?_ (congrArg (Q.val.map (homOfLE (le_rfl : U ≤ (𝟙 X) ⁻¹ᵁ U)).op)
      (homEquiv_pullbackId_comp_apply g U x)).symm
    change _ = Q.presheaf.map (𝟙 (op U)) _
    rw [CategoryTheory.Functor.map_id]
    rfl

/-- There is a unique isomorphism `ι^*𝒪_{𝐏(𝒢)}(1) ≅ 𝒪_{𝐏(𝒬)}(1)` carrying the pulled-back
tautological quotient of `𝒢` to the tautological quotient of `𝒬` precomposed with `g`. -/
theorem existsUnique_bundleEmbeddingTwistIso :
    ∃! φ : (Scheme.Modules.pullback (bundleEmbedding g)).obj (bundleTwist G) ≅ bundleTwist Q,
      twistQuotientPullback (𝟙 X) (bundlePieces G) (bundlePieces Q) (bundleEmbedding g)
          (bundleEmbedding_comp_toBase g) ≫ φ.hom =
        twistQuotientTarget (𝟙 X) (bundlePieces Q) ((Scheme.Modules.pullbackId X).hom.app G ≫ g) :=
  existsUnique_twistIso (𝟙 X) (bundlePieces G) (bundlePieces Q)
    ((Scheme.Modules.pullbackId X).hom.app G ≫ g) (bundleEmbedding g)
    (bundleEmbedding_comp_toBase g) (bundleEmbedding_chart g)

/-- The isomorphism `ι^*𝒪_{𝐏(𝒢)}(1) ≅ 𝒪_{𝐏(𝒬)}(1)` carrying the pulled-back tautological quotient
of `𝒢` to the tautological quotient of `𝒬` precomposed with `g`. -/
def bundleEmbeddingTwistIso :
    (Scheme.Modules.pullback (bundleEmbedding g)).obj (bundleTwist G) ≅ bundleTwist Q :=
  (existsUnique_bundleEmbeddingTwistIso g).exists.choose

/-- The isomorphism `bundleEmbeddingTwistIso g` carries the pulled-back tautological quotient of
`𝒢` to the tautological quotient of `𝒬` precomposed with `g`. -/
theorem twistQuotientPullback_comp_bundleEmbeddingTwistIso :
    twistQuotientPullback (𝟙 X) (bundlePieces G) (bundlePieces Q) (bundleEmbedding g)
        (bundleEmbedding_comp_toBase g) ≫ (bundleEmbeddingTwistIso g).hom =
      twistQuotientTarget (𝟙 X) (bundlePieces Q) ((Scheme.Modules.pullbackId X).hom.app G ≫ g) :=
  (existsUnique_bundleEmbeddingTwistIso g).exists.choose_spec

end Stacks.Chow.GenuineChern

end
