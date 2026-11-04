module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.Algebra.Homology.InjectiveDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationStrictlyPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.StrictlyPerfectIsKFlat
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.KInjectiveRestrictionAlongOverMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.HomologyLocalityPerDegree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor

/-!
# The evaluation morphism of derived internal Homs at a pseudo-coherent source

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. Stacks 0A97 supplies the
evaluation morphism

`ev : RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`.

Over a ring, More on Algebra, Lemmas 15.100.1 and 15.100.2 (Stacks 0A68 and 0A69) say that `ev`
is an isomorphism when `K` is pseudo-coherent, `L` is bounded below and `M` has finite injective
dimension, and when every truncation of `K` is pseudo-coherent, `L` and `M` have finite injective
dimension and `RSheafHom(L, M)` has finite Tor dimension. This file proves the sheaf-level forms of
both statements, with the finite injective dimension of `L` and `M` asked for locally, on the
members of a family of objects covering the final object. They are the affine-local content of
Stacks 0G4I, run directly on sheaves rather than through `D(A)`.

## The argument

Invertibility of `ev` is checked **one cohomological degree `n` at a time, locally on the site,
with a covering family depending on `n`**
(`isIso_derivedSheafHomEvaluation_of_coversTop_degreewise`). This reduction is the one Stacks 08JJ
makes at the level of all degrees at once (`isIso_derivedSheafHomEvaluation_of_coversTop`), with
`Stacks.SheafOfModules.quasiIso_of_coversTop_degreewise` in place of
`Stacks.SheafOfModules.quasiIso_of_coversTop`; the dependence of the family on `n` is forced,
because pseudo-coherence only gives strictly perfect approximations in degrees above some `m`,
over a covering depending on `m`.

Over a member of such a covering the degree-`n` statement is a **range comparison** along a
distinguished triangle `K' ⟶ K ⟶ Z ⟶ K'[1]`
(`isIso_homologyMap_derivedSheafHomEvaluation_of_triangle`): both sides of `ev` carry the triangle
to distinguished triangles — the source because the derived tensor product is exact, the target
by Stacks 08JC applied twice — and if `RSheafHom(L, M) ⊗^L_O Z` and
`RSheafHom(RSheafHom(Z, L), M)` vanish near degree `n`, invertibility on `Hⁿ` passes from `K'` to
`K` by the naturality of `ev` in its source. The two vanishings come from cohomological bounds:
`RSheafHom` out of a bounded-above object into a bounded-below one is bounded below
(`isGE_derivedSheafHom`), out of a bounded-below object into one represented by a K-injective
complex in degrees `≤ d` is bounded above (`isLE_derivedSheafHom`), the derived tensor product is
right t-exact, and a Tor bound bounds a tensor product below.

* At a strictly perfect approximation `Q(P) ⟶ K`, the cone is bounded above, and the range
  comparison gives `isIso_homologyMap_derivedSheafHomEvaluation_of_approximation`; at `Q(P)` the
  evaluation morphism is invertible outright (`quasiIso_evaluationMap_of_isStrictlyPerfect`).
  This is the pseudo-coherent case.
* At the truncation triangle `τ_{≤ N} K ⟶ K ⟶ τ_{≥ N + 1} K`, the third vertex is bounded below,
  and the range comparison reduces the general case to the truncation.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_isPseudoCoherent`: `ev` is an
  isomorphism for `K` pseudo-coherent, `L` bounded below and `M` of finite injective dimension
  locally. The sheaf-level form of Stacks 0A68 (2).
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_truncLE_isPseudoCoherent`:
  `ev` is an isomorphism for every truncation of `K` pseudo-coherent, `L` and `M` of finite
  injective dimension locally and `RSheafHom(L, M)` of Tor amplitude bounded below. The
  sheaf-level form of Stacks 0A69.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_coversTop_degreewise`: the
  degreewise local criterion.
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHomEvaluation_iff_ofModels` and
  `AlgebraicGeometry.RingedSite.isIso_homologyMap_restrictComplexMap_evaluationMap`: the two
  degree-`n` inputs of that criterion, the model criterion and the restriction square.

## Implementation notes

The finite injective dimension of `M` over a member `U` of the covering gives a K-injective
complex in bounded degrees representing `M|_U`; over the members `W ⟶ U` of the covering on which
the approximations live it is restricted along the arrow `W ⟶ U`
(`exists_isKInjective_isStrictlyLE_restrictAlong`), restriction along an arrow of the site
preserving K-injectivity by Stacks 08FI (`Stacks.Cohomology.Localization.isKInjective_overMap`).
So no condition on the iterated slices of the site is needed.

The derived internal Hom datum on the slices is `derivedInternalHomOfBifunctor`, whose bifunctor
is the one Stacks 08JC is proved for, and the derived tensor product there is the canonical one;
the degreewise criterion passes through the evaluation morphism of complexes, which depends on
neither, so the conclusions hold for any derived tensor product and derived internal Hom datum
on the site itself.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A68](https://stacks.math.columbia.edu/tag/0A68)
* [Stacks Project, Tag 0A69](https://stacks.math.columbia.edu/tag/0A69)
* [Stacks Project, Tag 0G4I](https://stacks.math.columbia.edu/tag/0G4I)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0A5S](https://stacks.math.columbia.edu/tag/0A5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pretriangulated
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

section RangeComparison

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **The evaluation morphism at a strictly perfect source is invertible.** -/
theorem isIso_derivedSheafHomEvaluation_Q_of_isStrictlyPerfect
    (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    {M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (eM : DerivedCategory.Q.obj I ≅ M) :
    IsIso (derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj P) L M) :=
  (isIso_derivedSheafHomEvaluation_iff_quasiIso_ofModels X T Hd _ L M
    (kFlat_of_isStrictlyPerfect X P hP) (Iso.refl _) (kInjectiveModelIso X L) eM).2
    (quasiIso_evaluationMap_of_isStrictlyPerfect X P (kInjectiveModel X L) I hP)

/-- **Invertibility of the evaluation morphism on cohomology in one degree passes along a
triangle whose third vertex is negligible there.** Let `K' ⟶ K ⟶ Z ⟶ K'[1]` be a distinguished
triangle of `D(O)`. If `RSheafHom(L, M) ⊗^L_O Z` and `RSheafHom(RSheafHom(Z, L), M)` both have no
cohomology in degrees `n - 1` and `n`, and the evaluation morphism at `K'` is invertible on
`Hⁿ`, then so is the evaluation morphism

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`.

The two sides of the evaluation morphism carry the triangle to distinguished triangles — the
source because the derived tensor product is exact, the target by Stacks 08JC applied twice —
whose third vertices are the two objects in question, so both maps induced by `K' ⟶ K` are
invertible on `Hⁿ`; the naturality of the evaluation morphism in its source concludes. The
vanishing is asked for in the form it is produced in, as a bound above or a bound below. -/
theorem isIso_homologyMap_derivedSheafHomEvaluation_of_triangle
    (K' K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (α : K' ⟶ K) (g : K ⟶ Z) (h : Z ⟶ K'⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α g h ∈ distTriang _) (n : ℤ)
    (hK' : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (derivedSheafHomEvaluation X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (derivedInternalHomOfBifunctor X) K' L M)))
    (h₁ : (∃ N, (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)).obj Z).IsLE N ∧ N + 1 < n) ∨
      (∃ N, (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)).obj Z).IsGE N ∧ n < N))
    (h₂ : (∃ N, (((derivedSheafHomBifunctor X).obj
        (op (((derivedSheafHomBifunctor X).obj (op Z)).obj L))).obj M).IsLE N ∧ N + 1 < n) ∨
      (∃ N, (((derivedSheafHomBifunctor X).obj
        (op (((derivedSheafHomBifunctor X).obj (op Z)).obj L))).obj M).IsGE N ∧ n < N)) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (derivedSheafHomEvaluation X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (derivedInternalHomOfBifunctor X) K L M)) := by
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct X
  let Hd := derivedInternalHomOfBifunctor X
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n
  let E := ((derivedSheafHomBifunctor X).obj (op L)).obj M
  have hTT := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj E).map_distinguished
    _ hT
  have hu : IsIso (H.map ((T.tensor.obj E).map α)) := by
    rcases h₁ with ⟨N, hN, hn⟩ | ⟨N, hN, hn⟩
    · exact Stacks.TruncationLevel.isIso_homologyMap_mor₁ _ hTT n
        ((DerivedCategory.isLE_iff _ N).1 hN n (by omega))
        ((DerivedCategory.isLE_iff _ N).1 hN (n - 1) (by omega))
    · exact DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hTT n N hN hn
  obtain ⟨δ₁, hT₁⟩ := exists_distinguished_derivedSheafHom X L (Triangle.mk α g h) hT
  obtain ⟨δ₂, hT₂⟩ := exists_distinguished_derivedSheafHom X M _ hT₁
  have hv : IsIso (H.map (((derivedSheafHomBifunctor X).flip.obj M).map
      (((derivedSheafHomBifunctor X).flip.obj L).map α.op).op)) := by
    rcases h₂ with ⟨N, hN, hn⟩ | ⟨N, hN, hn⟩
    · exact Stacks.TruncationLevel.isIso_homologyMap_mor₁ _ hT₂ n
        ((DerivedCategory.isLE_iff _ N).1 hN n (by omega))
        ((DerivedCategory.isLE_iff _ N).1 hN (n - 1) (by omega))
    · exact DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _ hT₂ n N hN hn
  have hnat := derivedSheafHomEvaluation_natural X T Hd α (𝟙 L) (𝟙 M)
  have hsrc : derivedTensorMap X T (derivedSheafHomMap X Hd (𝟙 L) (𝟙 M)) α =
      (T.tensor.obj E).map α := by
    simp [derivedTensorMap, E, Hd]
  have htgt : derivedSheafHomMap X Hd (derivedSheafHomMap X Hd α (𝟙 L)) (𝟙 M) =
      ((derivedSheafHomBifunctor X).flip.obj M).map
        (((derivedSheafHomBifunctor X).flip.obj L).map α.op).op := by
    simp [derivedSheafHomMap, Hd]
  rw [hsrc, htgt] at hnat
  have heq := congrArg H.map hnat
  rw [Functor.map_comp, Functor.map_comp] at heq
  have hcomp : IsIso (H.map ((T.tensor.obj E).map α) ≫
      H.map (derivedSheafHomEvaluation X T Hd K L M)) := by
    rw [heq]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hK' hv
  exact IsIso.of_isIso_comp_left (H.map ((T.tensor.obj E).map α)) _

/-- **The evaluation morphism is invertible on cohomology in a range determined by an
approximation of its source.** Let `α : Q(P) ⟶ K` be a morphism of `D(O)` from a strictly perfect
complex, invertible on cohomology above `m` and surjective in degree `m`; let `L` have no
cohomology below `b`, and let `M` be represented by a K-injective complex concentrated in degrees
`≤ d`. Then

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`

is an isomorphism on cohomology in every degree `n > d - b + m`.

The cone `Z` of `α` has no cohomology above `m - 1`. So `RSheafHom(L, M)`, which has none above
`d - b`, tensored with `Z` has none above `d - b + m - 1`; and `RSheafHom(Z, L)` has none below
`b - m + 1`, so `RSheafHom(RSheafHom(Z, L), M)` has none above `d - b + m - 1` either. At the
strictly perfect source the evaluation morphism is invertible. -/
theorem isIso_homologyMap_derivedSheafHomEvaluation_of_approximation
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    (α : DerivedCategory.Q.obj P ⟶ K) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).map α))
    (b : ℤ) (hL : L.IsGE b)
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] (d : ℤ)
    [CochainComplex.IsStrictlyLE I d] (eM : DerivedCategory.Q.obj I ≅ M)
    (n : ℤ) (hn : d - b + m < n) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (derivedSheafHomEvaluation X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (derivedInternalHomOfBifunctor X) K L M)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  have hZ : Z.IsLE (m - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation _ hT m hiso hepi
  have hE : (((derivedSheafHomBifunctor X).obj (op L)).obj M).IsLE (d - b) :=
    isLE_derivedSheafHom X L M b d hL I eM
  have hEZ : (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (((derivedSheafHomBifunctor X).obj (op L)).obj M)).obj Z).IsLE (d - b + (m - 1)) := by
    have := hE
    have := hZ
    exact Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor _ _ Z (d - b) (m - 1)
  have hZL : (((derivedSheafHomBifunctor X).obj (op Z)).obj L).IsGE (b - (m - 1)) :=
    isGE_derivedSheafHom X Z L (m - 1) b hZ hL
  have hZLM : (((derivedSheafHomBifunctor X).obj
      (op (((derivedSheafHomBifunctor X).obj (op Z)).obj L))).obj M).IsLE
      (d - (b - (m - 1))) :=
    isLE_derivedSheafHom X _ M (b - (m - 1)) d hZL I eM
  have hdP := isIso_derivedSheafHomEvaluation_Q_of_isStrictlyPerfect X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (derivedInternalHomOfBifunctor X)
    hP L eM
  exact isIso_homologyMap_derivedSheafHomEvaluation_of_triangle X _ K L M α g h hT n
    inferInstance (Or.inl ⟨_, hEZ, by omega⟩) (Or.inl ⟨_, hZLM, by omega⟩)

/-- **The evaluation morphism is invertible on cohomology in a range determined by an
approximation of its source, with the two cohomological bounds asked for directly.** This is
`isIso_homologyMap_derivedSheafHomEvaluation_of_approximation` with the K-injective model of `M`
concentrated in degrees `≤ d` replaced by the only two consequences that proof draws from it:

* `RSheafHom(L, M)` has no cohomology above `d - b`;
* `RSheafHom(RSheafHom(Z, L), M)` has no cohomology above `d - b + m - 1`, for `Z` the cone of
  the approximation `α`.

An injective-dimension hypothesis on `M` gives both, through `isLE_derivedSheafHom`; so does any
other source of the same two bounds. Over a scheme the second one is available for a dualizing
complex `M` with a bound `d` depending only on an affine open, where the sheafification of a
bounded complex of injective modules is *not* known to be a bounded complex of injective sheaves
(Stacks 0CRZ) and the hypothesis of the earlier statement is therefore out of reach.

The cone `Z` is only determined up to isomorphism, so the second bound is asked for at every
cone of `α`; a single cone would do, the statement being invariant under isomorphism of the
third vertex. -/
theorem isIso_homologyMap_derivedSheafHomEvaluation_of_approximation_of_isLE
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    (α : DerivedCategory.Q.obj P ⟶ K) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).map α))
    (b d : ℤ) (hL : L.IsGE b)
    (hE : (((derivedSheafHomBifunctor X).obj (op L)).obj M).IsLE (d - b))
    (hZ : ∀ (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (g : K ⟶ Z)
      (h : Z ⟶ (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧), Triangle.mk α g h ∈ distTriang _ →
      (((derivedSheafHomBifunctor X).obj
        (op (((derivedSheafHomBifunctor X).obj (op Z)).obj L))).obj M).IsLE
          (d - (b - (m - 1))))
    (n : ℤ) (hn : d - b + m < n) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (derivedSheafHomEvaluation X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (derivedInternalHomOfBifunctor X) K L M)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  have hZLE : Z.IsLE (m - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation _ hT m hiso hepi
  have hEZ : (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (((derivedSheafHomBifunctor X).obj (op L)).obj M)).obj Z).IsLE (d - b + (m - 1)) := by
    have := hE
    have := hZLE
    exact Stacks.SheafOfModules.DerivedTensorProduct.isLE_tensor _ _ Z (d - b) (m - 1)
  have hZLM := hZ Z g h hT
  have hdP := isIso_derivedSheafHomEvaluation_Q_of_isStrictlyPerfect X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (derivedInternalHomOfBifunctor X)
    hP L (kInjectiveModelIso X M)
  exact isIso_homologyMap_derivedSheafHomEvaluation_of_triangle X _ K L M α g h hT n
    inferInstance (Or.inl ⟨_, hEZ, by omega⟩) (Or.inl ⟨_, hZLM, by omega⟩)

/-- **The evaluation morphism is invertible on cohomology in one degree when a truncation of its
source is approximated by a strictly perfect complex and four cohomological bounds hold.** Let
`N` be an integer, let `α : Q(P) ⟶ τ_{≤ N} K` be a morphism from a strictly perfect complex,
invertible on cohomology above `m` and surjective in degree `m`, and let `L` have no cohomology
below `b`. If

* `RSheafHom(L, M)` has no cohomology above `d - b`,
* `RSheafHom(RSheafHom(Z, L), M)` has no cohomology above `d - b + m - 1` for `Z` a cone of `α`,
* `RSheafHom(L, M) ⊗^L_O τ_{≥ N + 1} K` has no cohomology below `e₁ > n`, and
* `RSheafHom(RSheafHom(τ_{≥ N + 1} K, L), M)` has no cohomology below `e₂ > n`,

then `RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)` is invertible on `Hⁿ`, for
`n > d - b + m`.

The first two bounds give invertibility at `τ_{≤ N} K`
(`isIso_homologyMap_derivedSheafHomEvaluation_of_approximation_of_isLE`); the last two say that
the third vertex of the truncation triangle `τ_{≤ N} K ⟶ K ⟶ τ_{≥ N + 1} K` contributes nothing
in degree `n`, so invertibility passes to `K`
(`isIso_homologyMap_derivedSheafHomEvaluation_of_triangle`). This is the degreewise content of
Stacks 0A69 run on sheaves, with every finiteness hypothesis replaced by the bounds it is there
to produce. -/
theorem isIso_homologyMap_derivedSheafHomEvaluation_of_truncLE_approximation
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (N : ℤ)
    {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    (α : DerivedCategory.Q.obj P ⟶
      (DerivedCategory.TStructure.t (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).truncLE N |>.obj K)
    (m : ℤ)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).map α))
    (b d : ℤ) (hL : L.IsGE b)
    (hE : (((derivedSheafHomBifunctor X).obj (op L)).obj M).IsLE (d - b))
    (hZ : ∀ (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
      (g : ((DerivedCategory.TStructure.t
        (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).truncLE N).obj K
          ⟶ Z)
      (h : Z ⟶ (DerivedCategory.Q.obj P)⟦(1 : ℤ)⟧), Triangle.mk α g h ∈ distTriang _ →
      (((derivedSheafHomBifunctor X).obj
        (op (((derivedSheafHomBifunctor X).obj (op Z)).obj L))).obj M).IsLE
          (d - (b - (m - 1))))
    (n : ℤ) (hn : d - b + m < n)
    (e₁ e₂ : ℤ) (hn₁ : n < e₁) (hn₂ : n < e₂)
    (hT₁ : (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)).obj
      (((DerivedCategory.TStructure.t
        (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).truncGE
            (N + 1)).obj K)).IsGE e₁)
    (hT₂ : (((derivedSheafHomBifunctor X).obj (op (((derivedSheafHomBifunctor X).obj
        (op (((DerivedCategory.TStructure.t
          (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).truncGE
              (N + 1)).obj K))).obj L))).obj M).IsGE
      e₂) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (derivedSheafHomEvaluation X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (derivedInternalHomOfBifunctor X) K L M)) := by
  have hK' := isIso_homologyMap_derivedSheafHomEvaluation_of_approximation_of_isLE X _ L M hP α m
    hiso hepi b d hL hE hZ n hn
  exact isIso_homologyMap_derivedSheafHomEvaluation_of_triangle X _ K L M _ _ _
    ((DerivedCategory.TStructure.t (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).triangleLEGE_distinguished
      N (N + 1) rfl K)
    n hK' (Or.inr ⟨e₁, hT₁, hn₁⟩) (Or.inr ⟨e₂, hT₂, hn₂⟩)

/-- The range comparison `isIso_homologyMap_derivedSheafHomEvaluation_of_approximation` for an
approximation `Q(P) ⟶ Q(N)` given by a morphism of complexes, with the hypotheses read on the
cohomology of complexes, and the K-injective model of `M` taken to be `I` itself. -/
private theorem isIso_homologyMap_evaluation_of_approximation_of_complexes
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {P N I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P) (α : P ⟶ N) (m : ℤ)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) (b : ℤ) (hL : L.IsGE b)
    [I.IsKInjective] (d : ℤ) [CochainComplex.IsStrictlyLE I d] (n : ℤ) (hn : d - b + m < n) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (derivedSheafHomEvaluation X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (derivedInternalHomOfBifunctor X) (DerivedCategory.Q.obj N) L
        (DerivedCategory.Q.obj I))) := by
  have hepi' : Epi ((DerivedCategory.homologyFunctor _ m).map (DerivedCategory.Q.map α)) := by
    have hc : Epi ((DerivedCategory.homologyFunctor _ m).map (DerivedCategory.Q.map α) ≫
        (DerivedCategory.homologyFunctorFactors _ m).hom.app N) := by
      rw [DerivedCategory.homologyFunctorFactors_hom_naturality α m]
      exact epi_comp' inferInstance hepi
    exact (epi_comp_iff_of_isIso _ _).1 hc
  exact isIso_homologyMap_derivedSheafHomEvaluation_of_approximation X _ L _ hP
    (DerivedCategory.Q.map α) m
    (fun j hj => (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ j) α).2
      (hiso j hj))
    hepi' b hL d (Iso.refl _) n hn

end RangeComparison

section Models

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- A commuting square with invertible vertical edges: after any functor, the two horizontal
edges are invertible together. -/
private theorem isIso_map_iff_of_square {D D' : Type*} [Category D] [Category D'] (F : D ⥤ D')
    {P₁ P₂ P₃ P₄ : D} {f : P₁ ⟶ P₂} {v : P₂ ⟶ P₄} {w : P₁ ⟶ P₃} {g : P₃ ⟶ P₄} [IsIso w]
    [IsIso v] (h : f ≫ v = w ≫ g) : IsIso (F.map f) ↔ IsIso (F.map g) := by
  have h' : F.map f ≫ F.map v = F.map w ≫ F.map g := by
    rw [← F.map_comp, ← F.map_comp, h]
  constructor
  · intro _
    have hg : inv (F.map w) ≫ F.map f ≫ F.map v = F.map g := by rw [h', IsIso.inv_hom_id_assoc]
    rw [← hg]
    infer_instance
  · intro _
    have hf : F.map w ≫ F.map g ≫ inv (F.map v) = F.map f := by
      rw [← Category.assoc, ← h', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← hf]
    infer_instance

/-- **Invertibility of the evaluation morphism on cohomology in one degree depends only on the
isomorphism classes of the three objects.** This is the three-variable naturality of the
evaluation morphism along three isomorphisms, read on `Hⁿ`. -/
theorem isIso_homologyMap_derivedSheafHomEvaluation_iff_of_iso
    (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
    {K K' L L' M M' : DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (eK : K ≅ K') (eL : L ≅ L') (eM : M ≅ M') (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
        (derivedSheafHomEvaluation X T Hd K L M)) ↔
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
        (derivedSheafHomEvaluation X T Hd K' L' M')) := by
  have : IsIso (derivedSheafHomMap X Hd eL.inv eM.hom) :=
    isIso_derivedSheafHomMap X Hd eL.inv eM.hom
  have : IsIso (derivedSheafHomMap X Hd eK.hom eL.inv) :=
    isIso_derivedSheafHomMap X Hd eK.hom eL.inv
  have : IsIso (derivedTensorMap X T (derivedSheafHomMap X Hd eL.inv eM.hom) eK.hom) :=
    isIso_derivedTensorMap X T _ _
  have : IsIso (derivedSheafHomMap X Hd
      (derivedSheafHomMap X Hd eK.hom eL.inv) eM.hom) :=
    isIso_derivedSheafHomMap X Hd _ _
  exact isIso_map_iff_of_square (DerivedCategory.homologyFunctor _ n)
    (derivedSheafHomEvaluation_natural X T Hd eK.hom eL.inv eM.hom).symm

/-- **Invertibility of the evaluation morphism on cohomology in one degree is invertibility of
the evaluation morphism of internal Hom complexes on cohomology in that degree, at any models.**
This is `isIso_derivedSheafHomEvaluation_iff_quasiIso_ofModels` read one degree at a time: the
two conjugations it consists of survive the degree-`n` cohomology functor. -/
theorem isIso_homologyMap_derivedSheafHomEvaluation_iff_ofModels
    (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective]
    (eA : DerivedCategory.Q.obj A ≅ K) (eB : DerivedCategory.Q.obj B ≅ L)
    (eC : DerivedCategory.Q.obj C ≅ M) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
        (derivedSheafHomEvaluation X T Hd K L M)) ↔
      IsIso (HomologicalComplex.homologyMap (evaluationMap X A B C) n) := by
  let H := DerivedCategory.homologyFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n
  have : IsIso (derivedSheafHomMap X Hd eB.inv eC.hom) :=
    isIso_derivedSheafHomMap X Hd eB.inv eC.hom
  have : IsIso (derivedSheafHomMap X Hd eA.hom eB.inv) :=
    isIso_derivedSheafHomMap X Hd eA.hom eB.inv
  have : IsIso (derivedTensorMap X T (derivedSheafHomMap X Hd eB.inv eC.hom) eA.hom) :=
    isIso_derivedTensorMap X T _ _
  have : IsIso (derivedSheafHomMap X Hd
      (derivedSheafHomMap X Hd eA.hom eB.inv) eC.hom) :=
    isIso_derivedSheafHomMap X Hd _ _
  have htransport : IsIso (H.map (derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C))) ↔
      IsIso (H.map (derivedSheafHomEvaluation X T Hd K L M)) :=
    isIso_map_iff_of_square H
      (derivedSheafHomEvaluation_natural X T Hd eA.hom eB.inv eC.hom).symm
  have hmodel : IsIso (H.map (derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C))) ↔
      IsIso (H.map (DerivedCategory.Q.map (evaluationMap X A B C))) :=
    isIso_map_iff_of_square H (derivedSheafHomEvaluation_model X T Hd A B C hA)
  exact htransport.symm.trans (hmodel.trans
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ n) _))

end Models

section Slice

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **The restriction of the evaluation morphism of Stacks 0A92 to a slice is invertible on
cohomology in one degree as soon as the evaluation morphism formed over that slice is.** This is
`quasiIso_restrictComplexMap_evaluationMap` one degree at a time: the square
`evaluationMap_restrict_square` identifies the two morphisms of complexes up to invertible
morphisms of complexes, which the degree-`n` homology functor keeps invertible. -/
theorem isIso_homologyMap_restrictComplexMap_evaluationMap (U : X.C)
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap (evaluationMap (X.over U)
      (restrictComplex X A U) (restrictComplex X B U) (restrictComplex X C U)) n)) :
    IsIso (HomologicalComplex.homologyMap (restrictComplexMap X U (evaluationMap X A B C)) n) := by
  have hcmOuter : IsIso ((derivedHomRestriction X U).complexMap
      (sheafHomComplex X A B).obj C) :=
    isIso_of_isInternalHomRestrictionMap X U (sheafHomComplex X A B).obj C _
      ((derivedHomRestriction X U).complexMap_isRestriction (sheafHomComplex X A B).obj C)
  have hcmMid : IsIso ((derivedHomRestriction X U).complexMap B C) :=
    isIso_of_isInternalHomRestrictionMap X U B C _
      ((derivedHomRestriction X U).complexMap_isRestriction B C)
  have hcmInner : IsIso ((derivedHomRestriction X U).complexMap A B) :=
    isIso_of_isInternalHomRestrictionMap X U A B _
      ((derivedHomRestriction X U).complexMap_isRestriction A B)
  have htt : IsIso (tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap B C)
      (𝟙 (restrictComplex X A U))) :=
    isIso_tensorTotalMap_hom_id (X.over U)
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap B C) hcmMid)
      (restrictComplex X A U)
  have hhm : IsIso (homMap (X.over U) ((derivedHomRestriction X U).complexMap A B)
      (𝟙 (restrictComplex X C U))) :=
    isIso_homMap_hom_id (X.over U)
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap A B) hcmInner)
      (restrictComplex X C U)
  have hsq : restrictComplexMap X U (evaluationMap X A B C) ≫
        (derivedHomRestriction X U).complexMap (sheafHomComplex X A B).obj C =
      (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫
        (tensorTotalMap (X.over U) ((derivedHomRestriction X U).complexMap B C)
            (𝟙 (restrictComplex X A U)) ≫
          evaluationMap (X.over U) (restrictComplex X A U) (restrictComplex X B U)
              (restrictComplex X C U) ≫
            homMap (X.over U) ((derivedHomRestriction X U).complexMap A B)
              (𝟙 (restrictComplex X C U))) :=
    (Iso.hom_inv_id_assoc (tensorTotalOverIso X U (sheafHomComplex X B C).obj A) _).symm.trans
      (congrArg
        (fun z => (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫ z)
        (evaluationMap_restrict_square X U A B C))
  let H := HomologicalComplex.homologyFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) (ComplexShape.up ℤ) n
  have hev : IsIso (H.map (evaluationMap (X.over U) (restrictComplex X A U)
      (restrictComplex X B U) (restrictComplex X C U))) := h
  have hHcm : IsIso (H.map ((derivedHomRestriction X U).complexMap
      (sheafHomComplex X A B).obj C)) :=
    Iso.isIso_hom (H.mapIso
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap (sheafHomComplex X A B).obj C)
        hcmOuter))
  have hHR : IsIso (H.map (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫
      H.map (tensorTotalMap (X.over U)
          ((derivedHomRestriction X U).complexMap B C) (𝟙 (restrictComplex X A U))) ≫
        H.map (evaluationMap (X.over U) (restrictComplex X A U)
            (restrictComplex X B U) (restrictComplex X C U)) ≫
          H.map (homMap (X.over U)
            ((derivedHomRestriction X U).complexMap A B) (𝟙 (restrictComplex X C U)))) :=
    Iso.isIso_hom
      (H.mapIso (tensorTotalOverIso X U (sheafHomComplex X B C).obj A) ≪≫
        H.mapIso (@asIso _ _ _ _ _ htt) ≪≫
          @asIso _ _ _ _ _ hev ≪≫ H.mapIso (@asIso _ _ _ _ _ hhm))
  have hfac : H.map (restrictComplexMap X U (evaluationMap X A B C)) ≫
        H.map ((derivedHomRestriction X U).complexMap (sheafHomComplex X A B).obj C) =
      H.map (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫
        H.map (tensorTotalMap (X.over U)
            ((derivedHomRestriction X U).complexMap B C) (𝟙 (restrictComplex X A U))) ≫
          H.map (evaluationMap (X.over U) (restrictComplex X A U)
              (restrictComplex X B U) (restrictComplex X C U)) ≫
            H.map (homMap (X.over U)
              ((derivedHomRestriction X U).complexMap A B) (𝟙 (restrictComplex X C U))) :=
    (CategoryTheory.Functor.map_comp _ _ _).symm.trans
      ((congrArg H.map hsq).trans
        ((CategoryTheory.Functor.map_comp _ _ _).trans
          (congrArg
            (fun z => H.map (tensorTotalOverIso X U (sheafHomComplex X B C).obj A).hom ≫ z)
            ((CategoryTheory.Functor.map_comp _ _ _).trans
              (congrArg
                (fun z => H.map (tensorTotalMap (X.over U)
                    ((derivedHomRestriction X U).complexMap B C)
                    (𝟙 (restrictComplex X A U))) ≫ z)
                (CategoryTheory.Functor.map_comp _ _ _))))))
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ hHcm hHR hfac

/-- **Invertibility of the evaluation morphism of derived internal Homs may be checked one
cohomological degree at a time, locally, with a covering family depending on the degree.** If for
every integer `n` there is a family of objects covering the final object over each member `V` of
which the evaluation morphism at objects isomorphic to the restrictions `K|_V`, `L|_V`, `M|_V`
is invertible on `Hⁿ`, then the evaluation morphism

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`

is an isomorphism, for any derived tensor product and any derived internal Hom datum on `X`.

The evaluation morphism at `K`, `L`, `M` is invertible exactly when the evaluation morphism of
internal Hom complexes at models is a quasi-isomorphism; the K-flat model of `K` is chosen with
K-flat restrictions to every slice; quasi-isomorphy is checked degree by degree on the covering
families (`Stacks.SheafOfModules.quasiIso_of_coversTop_degreewise`), restriction commutes with the
evaluation morphism of complexes up to invertible morphisms, and on the slice the degree-`n`
model criterion returns to the restricted derived objects. -/
theorem isIso_derivedSheafHomEvaluation_of_coversTop_degreewise
    (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ n : ℤ, ∃ (κ : Type u) (V : κ → X.C), X.J.CoversTop V ∧ ∀ k,
      ∃ K' L' M' : DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (V k)).O)),
        Nonempty (K' ≅
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (V k)).mapDerivedCategory.obj K) ∧
        Nonempty (L' ≅
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (V k)).mapDerivedCategory.obj L) ∧
        Nonempty (M' ≅
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              (V k)).mapDerivedCategory.obj M) ∧
        IsIso ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (V k)).O)) n).map
          (derivedSheafHomEvaluation (X.over (V k))
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over (V k)))
            (derivedInternalHomOfBifunctor (X.over (V k))) K' L' M'))) :
    IsIso (derivedSheafHomEvaluation X T Hd K L M) := by
  obtain ⟨A, fA, hAkf, -, hAq, -, hArestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O
      (kFlatModel X K)
  have hfA : IsIso (DerivedCategory.Q.map fA) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hAq
  let eA : DerivedCategory.Q.obj A ≅ K := @asIso _ _ _ _ _ hfA ≪≫ kFlatModelIso X K
  rw [isIso_derivedSheafHomEvaluation_iff_quasiIso_ofModels X T Hd K L M hAkf eA
    (kInjectiveModelIso X L) (kInjectiveModelIso X M)]
  choose κ V hV hiso using h
  refine Stacks.SheafOfModules.quasiIso_of_coversTop_degreewise hV _ fun n k => ?_
  refine isIso_homologyMap_restrictComplexMap_evaluationMap X (V n k) A _ _ n ?_
  have : (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (V n k)).O)) ℤ from
      restrictComplex X (kInjectiveModel X L) (V n k)).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V n k) (kInjectiveModel X L)
  have : (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over (V n k)).O)) ℤ from
      restrictComplex X (kInjectiveModel X M) (V n k)).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V n k) (kInjectiveModel X M)
  obtain ⟨K', L', M', ⟨eK⟩, ⟨eL⟩, ⟨eM⟩, hK'⟩ := hiso n k
  exact (isIso_homologyMap_derivedSheafHomEvaluation_iff_ofModels (X.over (V n k))
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over (V n k)))
    (derivedInternalHomOfBifunctor (X.over (V n k))) K' L' M' (hArestr (V n k))
    (restrictModelIso X (V n k) eA ≪≫ eK.symm)
    (restrictModelIso X (V n k) (kInjectiveModelIso X L) ≪≫ eL.symm)
    (restrictModelIso X (V n k) (kInjectiveModelIso X M) ≪≫ eM.symm) n).1 hK'

/-- **The degree-`n` invertibility of the evaluation morphism formed over an object `V` of the
site, at the restrictions of `K`, `L`, `M` themselves.** This is the per-member hypothesis of
`isIso_derivedSheafHomEvaluation_of_coversTop_degreewise` with the three objects over `V` taken
to be the restrictions `K|_V`, `L|_V`, `M|_V` rather than objects isomorphic to them.

It is named rather than written out at each use because the two spellings
`Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O` and
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V` of the restricted sheaf of rings are
equal only up to unfolding, and so
are the instances the derived tensor product and the derived internal hom datum over `X.over V`
carry: a producer and a consumer that both speak of this definition agree on the nose, whereas
two independent spellings of the same statement are compared by a deep definitional unfolding. -/
def IsIsoHomologyMapEvaluationOver
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (V : X.C) : Prop :=
  IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O)) n).map
    (derivedSheafHomEvaluation (X.over V)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over V))
      (derivedInternalHomOfBifunctor (X.over V))
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategory.obj L)
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategory.obj M)))

/-- **The degreewise local criterion, with the covering taken at the restrictions themselves.**
This is `isIso_derivedSheafHomEvaluation_of_coversTop_degreewise` phrased at
`IsIsoHomologyMapEvaluationOver`: the three identity isomorphisms the criterion asks for are
supplied here, once, rather than at the call site. -/
theorem isIso_derivedSheafHomEvaluation_of_coversTop_isIsoHomologyMapEvaluationOver
    (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ n : ℤ, ∃ (κ : Type u) (V : κ → X.C), X.J.CoversTop V ∧ ∀ k,
      IsIsoHomologyMapEvaluationOver X K L M n (V k)) :
    IsIso (derivedSheafHomEvaluation X T Hd K L M) := by
  refine isIso_derivedSheafHomEvaluation_of_coversTop_degreewise X T Hd K L M fun n => ?_
  obtain ⟨κ, V, hV, hiso⟩ := h n
  exact ⟨κ, V, hV, fun k =>
    ⟨_, _, _, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, hiso k⟩⟩

/-- Restricting a K-injective complex of `O|_U`-modules concentrated in degrees `[c, d]` along
an arrow `f : W ⟶ U` of the site gives a K-injective complex of `O|_W`-modules concentrated in
degrees `[c, d]`, whose class is the restriction to `W` of any object of `D(O)` whose restriction
to `U` it represents. -/
theorem exists_isKInjective_isStrictlyLE_restrictAlong
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {U W : X.C} (f : W ⟶ U) (I : CochainComplex (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ)
    [I.IsKInjective] (c d : ℤ) [CochainComplex.IsStrictlyGE I c] [CochainComplex.IsStrictlyLE I d]
    (eI : DerivedCategory.Q.obj I ≅
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.obj M) :
    ∃ I' : CochainComplex
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
      I'.IsKInjective ∧ CochainComplex.IsStrictlyGE I' c ∧ CochainComplex.IsStrictlyLE I' d ∧
        Nonempty (DerivedCategory.Q.obj I' ≅
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
              W).mapDerivedCategory.obj M) := by
  let G := SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  let : PreservesFiniteLimits G :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits f
  let : PreservesFiniteColimits G :=
    Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits f
  let Im := kInjectiveModel X M
  have hK : CochainComplex.IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    Stacks.Cohomology.Localization.isKInjective_overMap X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f I
  have hLE : CochainComplex.IsStrictlyLE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      d := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact G.map_isZero (CochainComplex.isZero_of_isStrictlyLE I d i hi)
  have hGE : CochainComplex.IsStrictlyGE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      c := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact G.map_isZero (CochainComplex.isZero_of_isStrictlyGE I c i hi)
  let e₁ : DerivedCategory.Q.obj I ≅ DerivedCategory.Q.obj (restrictComplex X Im U) :=
    eI ≪≫ (restrictModelIso X U (kInjectiveModelIso X M)).symm
  let e₂ : DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (restrictComplex X Im U)) :=
    (G.mapDerivedCategoryFactors.app I).symm ≪≫ G.mapDerivedCategory.mapIso e₁ ≪≫
      G.mapDerivedCategoryFactors.app _
  let e₃ : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (restrictComplex X Im U) ≅
      restrictComplex X Im W :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).app Im
  exact ⟨_, hK, hGE, hLE, ⟨e₂ ≪≫ DerivedCategory.Q.mapIso e₃ ≪≫
    restrictModelIso X W (kInjectiveModelIso X M)⟩⟩

/-- If the sieves generated by presieves `S i` cover the `V i`, for `V` covering the final object,
then the arrows of the `S i` form a covering family. -/
private theorem coversTop_sigma_generate {C : Type*} [Category C] (J : GrothendieckTopology C)
    {ι : Type*} (V : ι → C) (hV : J.CoversTop V) (S : ∀ i, Presieve (V i))
    (hS : ∀ i, Sieve.generate (S i) ∈ J (V i)) :
    J.CoversTop (fun k : Σ i, Σ W : C, { f : W ⟶ V i // S i f } => k.2.1) := by
  intro Z
  refine J.transitive (hV Z) _ ?_
  rintro Y g ⟨i, ⟨c₀⟩⟩
  refine J.superset_covering ?_ (J.pullback_stable c₀ (hS i))
  rintro W' p ⟨W, e, f, hf, hfac⟩
  exact ⟨⟨i, W, f, hf⟩, ⟨e⟩⟩

/-- A lower cohomological bound on an object of `D(O)` is inherited by its restriction to a
slice. -/
private theorem isGE_overFunctor_obj (Y : RingedSite.{u, u, u})
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V : Y.C, HasSheafify (Y.J.over V) AddCommGrpCat.{u}]
    [∀ V : Y.C, (Y.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (b : ℤ) (hE : E.IsGE b) (W : Y.C) :
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      W).mapDerivedCategory.obj E).IsGE b := by
  have hJGE : (DerivedCategory.Q.obj (kInjectiveModel Y E)).IsGE b := by
    have := hE
    exact DerivedCategory.TStructure.t.isGE_of_iso (kInjectiveModelIso Y E).symm b
  have := isGE_Q_obj_restrictComplex Y W (kInjectiveModel Y E) b hJGE
  exact DerivedCategory.TStructure.t.isGE_of_iso (restrictModelIso Y W (kInjectiveModelIso Y E)) b

/-- **The evaluation morphism of derived internal Homs is an isomorphism at a pseudo-coherent
source, a cohomologically bounded-below intermediate object and a target of finite injective
dimension locally.** Let `K`, `L`, `M` be objects of `D(O)` with `K` pseudo-coherent
(Stacks 08FT), the cohomology of `L` vanishing in degrees `≪ 0`, and `M` of finite injective
dimension (Stacks 0A5S) on each member of a family of objects covering the final object. Then

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`

is an isomorphism, for any derived tensor product and derived internal Hom datum.

It is checked one degree `n` at a time (`isIso_derivedSheafHomEvaluation_of_coversTop_degreewise`).
Over a member `V` of the covering where `M` is represented by a complex of injectives in degrees
`≤ d`, pseudo-coherence of `K` from degree `m = n - d + b - 1` gives a covering of `V` over each
member of which `K` is approximated in degrees `≥ m` by a strictly perfect complex; there the
range comparison `isIso_homologyMap_derivedSheafHomEvaluation_of_approximation` applies in degree
`n`. -/
theorem isIso_derivedSheafHomEvaluation_of_isPseudoCoherent
    (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPseudoCoherent K) (hL : DerivedCategoryB.IsBoundedBelow L)
    (hM : ∃ (ι : Type u) (V : ι → X.C), X.J.CoversTop V ∧ ∀ i,
      StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (V i)).mapDerivedCategory.obj M)) :
    IsIso (derivedSheafHomEvaluation X T Hd K L M) := by
  classical
  obtain ⟨N, hN, ⟨eN⟩⟩ := hK
  obtain ⟨b, hb⟩ := hL
  have hLGE : L.IsGE b := (DerivedCategory.isGE_iff L b).mpr hb
  obtain ⟨ι, V, hV, hMV⟩ := hM
  choose c d I hIc hId hIinj eI using hMV
  have hIK : ∀ i, (I i).IsKInjective := fun i => by
    have := hIc i
    have := hIinj i
    exact CochainComplex.isKInjective_of_injective (I i) (c i)
  refine isIso_derivedSheafHomEvaluation_of_coversTop_degreewise X T Hd K L M fun n => ?_
  have hS := fun i => hN (n - d i + b - 1) (V i)
  choose S hS hdata using hS
  refine ⟨Σ i, Σ W : X.C, { f : W ⟶ V i // S i f }, fun k => k.2.1, ?_, ?_⟩
  · exact coversTop_sigma_generate X.J V hV S hS
  · rintro ⟨i, W, f, hf⟩
    obtain ⟨P, hP, α₀, hαiso, hαepi⟩ := hdata i f hf
    have h₁ := hIK i
    have h₂ := hId i
    have h₃ := hIc i
    have e₀ := (eI i).some
    have hex := exists_isKInjective_isStrictlyLE_restrictAlong X M (U := V i) (W := W) f
      (I := I i) (c i) (d i) (eI := e₀.symm)
    obtain ⟨I', hI'K, -, hI'LE, ⟨eI'⟩⟩ := hex
    have : (show CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from
      I').IsKInjective := hI'K
    have : CochainComplex.IsStrictlyLE (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from I') (d i) :=
          hI'LE
    have hLW := isGE_overFunctor_obj X L b hLGE W
    refine ⟨DerivedCategory.Q.obj (restrictComplex X N W), _, DerivedCategory.Q.obj I',
      ⟨restrictModelIso X W eN⟩, ⟨Iso.refl _⟩, ⟨eI'⟩, ?_⟩
    exact isIso_homologyMap_evaluation_of_approximation_of_complexes (X.over W) _ hP α₀
      (n - d i + b - 1) hαiso hαepi b hLW (d i) n (by omega)

/-- **The evaluation morphism of derived internal Homs is an isomorphism when the intermediate
and target objects have finite injective dimension locally and the derived internal Hom between
them has Tor amplitude bounded below.** Let `K`, `L`, `M` be objects of `D(O)` with every
truncation `τ_{≤ N} K` pseudo-coherent (Stacks 08FT), `L` and `M` each of finite injective
dimension (Stacks 0A5S) on the members of a family of objects covering the final object, and
`RSheafHom(L, M)` of Tor amplitude in `[a, ∞)`. Then

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`

is an isomorphism, for any derived tensor product and derived internal Hom datum. This is the
sheaf-level form of Stacks 0A69.

It is checked one degree `n` at a time (`isIso_derivedSheafHomEvaluation_of_coversTop_degreewise`).
Over an object `V` mapping to a member of each of the two coverings, `L` and `M` are represented
by K-injective complexes in degrees `[c_L, d_L]` and `[c_M, d_M]`, restricted from those members;
there the truncation `τ_{≤ N} K` for `N` large enough is
approximated in degrees `≥ m` by a strictly perfect complex over the members of a covering of
`V`, which gives invertibility on `Hⁿ` at `τ_{≤ N} K`
(`isIso_homologyMap_derivedSheafHomEvaluation_of_approximation`); the third vertex
`τ_{≥ N + 1} K` of the truncation triangle contributes nothing in degrees near `n`, by the Tor
bound on the source side and by the two injective bounds on the target side
(`isIso_homologyMap_derivedSheafHomEvaluation_of_triangle`). -/
theorem isIso_derivedSheafHomEvaluation_of_truncLE_isPseudoCoherent
    (T : Stacks.SheafOfModules.DerivedTensorProduct X) (Hd : DerivedInternalHom X)
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : ∀ N : ℤ, X.IsPseudoCoherent ((DerivedCategory.TStructure.t.truncLE N).obj K))
    (hL : ∃ (ι : Type u) (V : ι → X.C), X.J.CoversTop V ∧ ∀ i,
      StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (V i)).mapDerivedCategory.obj L))
    (hM : ∃ (ι : Type u) (V : ι → X.C), X.J.CoversTop V ∧ ∀ i,
      StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (V i)).mapDerivedCategory.obj M))
    (a : ℤ) (hE : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (((derivedSheafHomBifunctor X).obj (op L)).obj M) a) :
    IsIso (derivedSheafHomEvaluation X T Hd K L M) := by
  classical
  -- a bounded K-injective model of an object of finite injective dimension over a member of a
  -- covering, restricted to anything mapping to that member
  have hmodel : ∀ (E : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) {U Z : X.C} (_ : Z ⟶ U),
      StacksDraft.InjectiveDimension.HasFiniteInjectiveDimension
        ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.obj E) →
      ∃ (c d : ℤ) (I : CochainComplex (SheafOfModules.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z)) ℤ),
        I.IsKInjective ∧ CochainComplex.IsStrictlyGE I c ∧ CochainComplex.IsStrictlyLE I d ∧
          Nonempty (DerivedCategory.Q.obj I ≅
            (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                Z).mapDerivedCategory.obj E) := by
    intro E U Z g ⟨c, d, I, hIc, hId, hIinj, ⟨eI⟩⟩
    have := hIc
    have := hId
    have := hIinj
    have : I.IsKInjective := CochainComplex.isKInjective_of_injective I c
    obtain ⟨I', h₁, h₂, h₃, h₄⟩ :=
      exists_isKInjective_isStrictlyLE_restrictAlong X E g I c d eI.symm
    exact ⟨c, d, I', h₁, h₂, h₃, h₄⟩
  -- the common refinement of the two coverings
  obtain ⟨ιL, VL, hVL, hLV₀⟩ := hL
  obtain ⟨ιM, VM, hVM, hMV₀⟩ := hM
  let ι := Σ Z : X.C, (Σ i, Z ⟶ VL i) × (Σ j, Z ⟶ VM j)
  let V : ι → X.C := fun k => k.1
  have hV : X.J.CoversTop V := by
    intro U
    refine X.J.superset_covering ?_ (X.J.intersection_covering (hVL U) (hVM U))
    rintro Z g ⟨⟨i, ⟨a⟩⟩, ⟨j, ⟨b⟩⟩⟩
    exact ⟨⟨Z, ⟨i, a⟩, ⟨j, b⟩⟩, ⟨𝟙 Z⟩⟩
  choose cL dL J hJK hJc hJd eJ using fun k : ι => hmodel L k.2.1.2 (hLV₀ k.2.1.1)
  choose cM dM I hIK hIc hId eI using fun k : ι => hmodel M k.2.2.2 (hMV₀ k.2.2.1)
  refine isIso_derivedSheafHomEvaluation_of_coversTop_degreewise X T Hd K L M fun n => ?_
  let N : ι → ℤ := fun i => max (n - a) (n + dL i - cM i)
  choose NN hNN eNN using fun i => hK (N i)
  choose S hS hdata using fun i => hNN i (n - dM i + cL i - 1) (V i)
  refine ⟨Σ i, Σ W : X.C, { f : W ⟶ V i // S i f }, fun k => k.2.1, ?_, ?_⟩
  · exact coversTop_sigma_generate X.J V hV S hS
  · rintro ⟨i, W, f, hf⟩
    obtain ⟨P, hP, α₀, hαiso, hαepi⟩ := hdata i f hf
    have := hJK i
    have := hJc i
    have := hJd i
    have := hIK i
    have := hIc i
    have := hId i
    have eJ₀ := (eJ i).some
    have eI₀ := (eI i).some
    have hexJ := exists_isKInjective_isStrictlyLE_restrictAlong X L (U := V i) (W := W) f
      (I := J i) (cL i) (dL i) (eI := eJ₀)
    have hexI := exists_isKInjective_isStrictlyLE_restrictAlong X M (U := V i) (W := W) f
      (I := I i) (cM i) (dM i) (eI := eI₀)
    obtain ⟨J', hJ'K, hJ'GE, hJ'LE, ⟨eJ'⟩⟩ := hexJ
    obtain ⟨I', hI'K, hI'GE, hI'LE, ⟨eI'⟩⟩ := hexI
    have : (show CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from
      J').IsKInjective := hJ'K
    have : CochainComplex.IsStrictlyGE (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from J')
          (cL i) := hJ'GE
    have : CochainComplex.IsStrictlyLE (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from J')
          (dL i) := hJ'LE
    have : (show CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from
      I').IsKInjective := hI'K
    have : CochainComplex.IsStrictlyGE (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from I')
          (cM i) := hI'GE
    have : CochainComplex.IsStrictlyLE (show CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from I')
          (dM i) := hI'LE
    let F := (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        W).mapDerivedCategory
    let t := DerivedCategory.TStructure.t (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    refine ⟨F.obj K, F.obj L, DerivedCategory.Q.obj I', ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨eI'⟩, ?_⟩
    have hT := F.map_distinguished _ (t.triangleLEGE_distinguished (N i) (N i + 1) rfl K)
    have hLW : (F.obj L).IsGE (cL i) :=
      DerivedCategory.TStructure.t.isGE_of_iso eJ' (cL i)
    -- the evaluation morphism at the truncation, on `Hⁿ`
    have h₀ := isIso_homologyMap_evaluation_of_approximation_of_complexes (X.over W) _ hP α₀
      (I := I') (n - dM i + cL i - 1) hαiso hαepi (cL i) hLW (dM i) n (by omega)
    have hK' := (isIso_homologyMap_derivedSheafHomEvaluation_iff_of_iso (X.over W) _ _
      (restrictModelIso X W (eNN i).some) (Iso.refl (F.obj L))
      (Iso.refl (DerivedCategory.Q.obj I')) n).1 h₀
    -- the bounds at the third vertex `τ_{≥ N + 1} K`
    have hZ : (F.obj ((t.truncGE (N i + 1)).obj K)).IsGE (N i + 1) :=
      isGE_overFunctor_obj X _ (N i + 1) inferInstance W
    have hEW : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over W))
        (((derivedSheafHomBifunctor (X.over W)).obj (op (F.obj L))).obj
          (DerivedCategory.Q.obj I')) a :=
      (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_derivedRestriction
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) W
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over W)) _ a hE).of_iso
        ((((derivedSheafHomBifunctor (X.over W)).obj (op (F.obj L))).mapIso eI') ≪≫
          ((derivedHomRestriction X W).iso L M).symm)
    have hZL : (((derivedSheafHomBifunctor (X.over W)).obj
        (op (F.obj ((t.truncGE (N i + 1)).obj K)))).obj (F.obj L)).IsLE (dL i - (N i + 1)) :=
      isLE_derivedSheafHom (X.over W) _ _ (N i + 1) (dL i) hZ J' eJ'
    have hN₁ : n - a ≤ N i := le_max_left _ _
    have hN₂ : n + dL i - cM i ≤ N i := le_max_right _ _
    have hIGE : (DerivedCategory.Q.obj I').IsGE (cM i) := by
      have : CochainComplex.IsStrictlyGE (show CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over W).O)) ℤ from I')
            (cM i) := hI'GE
      infer_instance
    refine isIso_homologyMap_derivedSheafHomEvaluation_of_triangle (X.over W) _ _ _ _ _ _ _ hT
      n hK' (Or.inr ⟨a + (N i + 1), ?_, by omega⟩)
      (Or.inr ⟨cM i - (dL i - (N i + 1)), ?_, by omega⟩)
    · exact Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE _ _ _
        a (N i + 1) hEW hZ
    · exact isGE_derivedSheafHom (X.over W) _ _ (dL i - (N i + 1)) (cM i) hZL hIGE

end Slice

end AlgebraicGeometry.RingedSite

end
