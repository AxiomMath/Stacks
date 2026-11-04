module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.CoveringApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.HomologyLocalityPerDegree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal of Stacks 0BYS at a pseudo-coherent source: Stacks 0ATN part (3)

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. The diagonal morphism
of Stacks 0BYS

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism as soon as `M` is **pseudo-coherent**, the cohomology of `L` vanishes in
degrees `≪ 0` and `K` has **finite Tor dimension**. This is Stacks 0ATN part (3), stated by
`isIso_derivedTensorHomDiagonal_of_isPseudoCoherent`.

## The argument

Fix an integer `a` with `K` of Tor amplitude in `[a, ∞]` and an integer `b` below which the
cohomology of `L` vanishes. The diagonal is an isomorphism exactly when the complex-level
morphism of Stacks 0BYR at one choice of models is a quasi-isomorphism
(`isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels`), and that is checked one cohomological
degree at a time, locally on the site — with a covering family allowed to depend on the degree,
by `Stacks.SheafOfModules.quasiIso_of_coversTop_degreewise`. The dependence is unavoidable: over a
member of a covering, pseudo-coherence gives a strictly perfect approximation of `M` only in
degrees above some `m`, and the covering it comes with depends on `m`, while the degree `n` that is
being checked forces `m` to be taken below `a + b - n`.

In degree `n` the comparison is `isIso_homologyMap_derivedTensorHomDiagonal_of_approximation`. On
the slice the approximation `α : P ⟶ M` has a cone `Z` concentrated in degrees `≤ m - 1`, by the
dual of Stacks 05TC. Applying `RSheafHom(-, L)` to the triangle of `α` (Stacks 08JC) and then
`K ⊗^L_O -` (which is exact) produces a distinguished triangle whose first vertex is
`K ⊗^L_O RSheafHom(Z, L)`, and that object has no cohomology below `a + b - m + 1`: the internal
Hom out of a bounded-above object into a bounded-below one is bounded below
(`isGE_derivedSheafHom`) and a Tor bound on one tensor factor shifts a lower bound on the other
(`isGE_tensor_of_hasTorAmplitudeGE`). Applying `RSheafHom(-, K ⊗^L_O L)` instead gives a triangle
whose first vertex has no cohomology below the same bound. So both maps induced by `α` on the two
sides of the diagonal are isomorphisms on `Hⁿ` for `n < a + b - m`, and since the diagonal at the
strictly perfect `P` is an isomorphism outright (Stacks 0ATN part (1) in its globally strictly
perfect form), the naturality square of Stacks 0BYS in the source of the internal Hom gives the
degree-`n` statement for `M`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedTensorHomDiagonal_of_approximation`: the
  range comparison, the degree-`n` invertibility of the diagonal at a source approximated in
  degrees above `m` by a globally strictly perfect complex.
* `AlgebraicGeometry.RingedSite.isIso_homologyMap_restrictComplexMap_of_approximation`: the same,
  carried to the restriction to a member of a covering of the complex-level morphism of
  Stacks 0BYR formed on the whole site.
* `AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent`:
  **Stacks 0ATN part (3)**.

## Implementation notes

The range comparison is stated with the approximating object presented as the class of a complex
with finitely many nonzero terms, each a direct summand of a finite free `O`-module, rather than
as a perfect object: it is applied on a slice, where pseudo-coherence hands over exactly such a
complex, and in that form it needs no condition on the slices of the slice.

The passage from the slice back to the whole site is the one the perfect case uses,
`restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap`, with quasi-isomorphy replaced
throughout by invertibility in a single degree. Translating between the cohomology of a morphism
of complexes and the cohomology of its class is
`CategoryTheory.DerivedCategory.homologyFunctorFactors`, used through the three private lemmas
below.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Remark 20.49.12 (Tag 0BYS)](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Lemma 20.49.9 (Tag 08JC)](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Definition 20.47.1 (Tag 08FT)](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Definition 20.48.2 (Tag 08FZ)](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Lemma 013D (Tag 05TC)](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

/-- **In a distinguished triangle whose first vertex is bounded below by `n`, the second morphism
is invertible on cohomology in every degree below `n - 1`.** This is
`CategoryTheory.DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃` read on the rotated triangle,
whose third vertex is the shift of the first vertex of the given one. -/
private theorem isIso_homologyMap_mor₂_of_isGE₁ {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C)) (i n : ℤ) (hGE : T.obj₁.IsGE n)
    (hi : i < n - 1) :
    IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₂) := by
  have := hGE
  have hsh : (T.obj₁⟦(1 : ℤ)⟧).IsGE (n - 1) :=
    DerivedCategory.TStructure.t.isGE_shift T.obj₁ n 1 (n - 1) (by omega)
  exact DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ T.rotate (rot_of_distTriang _ hT)
    i (n - 1) hsh hi

/-- **The cohomology of the class of a morphism of complexes is the cohomology of that
morphism**, as a commuting square against the comparison of the two homology functors. -/
private theorem homologyFunctor_Q_map_square {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (g : K ⟶ L) (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map g) ≫
        ((DerivedCategory.homologyFunctorFactors C n).app L).hom =
      ((DerivedCategory.homologyFunctorFactors C n).app K).hom ≫
        HomologicalComplex.homologyMap g n := by
  simpa only [Iso.app_hom] using DerivedCategory.homologyFunctorFactors_hom_naturality g n

/-- A morphism of complexes invertible on cohomology in degree `n` has a class invertible on
cohomology in degree `n`. -/
private theorem isIso_homologyFunctor_Q_map_of_isIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (g : K ⟶ L) (n : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap g n)) :
    IsIso ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map g)) := by
  have hc : IsIso ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map g) ≫
      ((DerivedCategory.homologyFunctorFactors C n).app L).hom) := by
    rw [homologyFunctor_Q_map_square]
    exact IsIso.comp_isIso' (Iso.isIso_hom _) h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((DerivedCategory.homologyFunctorFactors C n).app L).hom (Iso.isIso_hom _) hc

/-- A morphism of complexes surjective on cohomology in degree `n` has a class surjective on
cohomology in degree `n`. -/
private theorem epi_homologyFunctor_Q_map_of_epi {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (g : K ⟶ L) (n : ℤ)
    (h : Epi (HomologicalComplex.homologyMap g n)) :
    Epi ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map g)) := by
  have hc : Epi ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map g) ≫
      ((DerivedCategory.homologyFunctorFactors C n).app L).hom) := by
    rw [homologyFunctor_Q_map_square]
    exact epi_comp' inferInstance h
  exact (epi_comp_iff_of_isIso _
    ((DerivedCategory.homologyFunctorFactors C n).app L).hom).1 hc

/-- A morphism of complexes whose class is invertible on cohomology in degree `n` is itself
invertible on cohomology in degree `n`. -/
private theorem isIso_homologyMap_of_isIso_homologyFunctor_Q_map {C : Type*} [Category C]
    [Abelian C] [HasDerivedCategory C] {K L : CochainComplex C ℤ} (g : K ⟶ L) (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map g))) :
    IsIso (HomologicalComplex.homologyMap g n) := by
  have hc : IsIso (((DerivedCategory.homologyFunctorFactors C n).app K).hom ≫
      HomologicalComplex.homologyMap g n) := by
    rw [← homologyFunctor_Q_map_square]
    exact IsIso.comp_isIso' h (Iso.isIso_hom _)
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    ((DerivedCategory.homologyFunctorFactors C n).app K).hom _ (Iso.isIso_hom _) hc

section RangeComparison

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **The diagonal of Stacks 0BYS is invertible on cohomology in a range determined by an
approximation of its source.** Let `NP` be a complex with finitely many nonzero terms, each a
direct summand of a finite free `O`-module, and let `α : NP ⟶ M` be a morphism of `D(O)` which is
an isomorphism on cohomology in every degree above `m` and a surjection on cohomology in degree
`m`. If `K` has Tor amplitude in `[a, ∞]` and the cohomology of `L` vanishes below `b`, then

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism on cohomology in every degree `n < a + b - m`. -/
public theorem isIso_homologyMap_derivedTensorHomDiagonal_of_approximation
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {NP : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hPbdd : {i : ℤ | ¬ IsZero (NP.X i)}.Finite)
    (hPterm : ∀ i, IsFiniteFreeSummand X (NP.X i))
    (α : DerivedCategory.Q.obj NP ⟶ M) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).map α))
    (a b n : ℤ)
    (hKamp : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K a)
    (hLGE : L.IsGE b) (hn : n < a + b - m) :
    IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (derivedTensorHomDiagonal X K L M)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  have hZ : Z.IsLE (m - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation _ hT m hiso hepi
  have hKL : (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L).IsGE
      (a + b) :=
    Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE _ K L a b
      hKamp hLGE
  have hHL : (((derivedSheafHomBifunctor X).obj (op Z)).obj L).IsGE (b - (m - 1)) :=
    isGE_derivedSheafHom X Z L (m - 1) b hZ hLGE
  have hHKL : (((derivedSheafHomBifunctor X).obj (op Z)).obj
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)).IsGE
      ((a + b) - (m - 1)) :=
    isGE_derivedSheafHom X Z _ (m - 1) (a + b) hZ hKL
  obtain ⟨δ₁, hT₁⟩ := exists_distinguished_derivedSheafHom X L (Triangle.mk α g h) hT
  obtain ⟨δ₂, hT₂⟩ := exists_distinguished_derivedSheafHom X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)
    (Triangle.mk α g h) hT
  have hTT := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map_distinguished
    _ hT₁
  have hu : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).map
        (((derivedSheafHomBifunctor X).map α.op).app L))) := by
    refine isIso_homologyMap_mor₂_of_isGE₁ _ hTT n (a + (b - (m - 1))) ?_ (by omega)
    exact Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE _ K _
      a (b - (m - 1)) hKamp hHL
  have hv : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (((derivedSheafHomBifunctor X).map α.op).app
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L))) :=
    isIso_homologyMap_mor₂_of_isGE₁ _ hT₂ n ((a + b) - (m - 1)) hHKL (by omega)
  have hdP : IsIso (derivedTensorHomDiagonal X K L (DerivedCategory.Q.obj NP)) :=
    isIso_derivedTensorHomDiagonal_of_isFiniteFreeSummand X K L _ (Iso.refl _) hPbdd hPterm
  have hnat := derivedTensorHomDiagonal_natural_hom X K L α
  have heq := congrArg
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map hnat
  rw [Functor.map_comp, Functor.map_comp] at heq
  have hcomp : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (derivedTensorHomDiagonal X K L M) ≫
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
        (((derivedSheafHomBifunctor X).map α.op).app
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L))) := by
    rw [← heq]
    have := hu
    have := hdP
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (((derivedSheafHomBifunctor X).map α.op).app
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L)))

end RangeComparison

section Assembly

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The complex-level morphism of Stacks 0BYR restricts to a morphism invertible on cohomology
in a range, over a member of a covering carrying an approximation of the source.** The
hypotheses are the data of the models on the site over `U`: `A|_U` is K-flat, `I` and `J` are
K-injective, `A|_U` carries the Tor bound `a` and `I|_U` the cohomological bound `b`, and `N|_U`
receives a map `α` from a strictly perfect complex which is an isomorphism on cohomology above
`m` and a surjection in degree `m`. Then the restriction to `U` of the morphism of Stacks 0BYR
formed on `X` is invertible on cohomology in every degree `n < a + b - m`.

The degree-`n` invertibility of the diagonal over `U` is the range comparison, the models
criterion turns it into the corresponding statement for the morphism of complexes formed over
`U`, and `restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap` carries that to the
restriction of the morphism formed on `X`. -/
public theorem isIso_homologyMap_restrictComplexMap_of_approximation
    (U : X.C)
    {A I N J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat (X.over U).O (restrictComplex X A U))
    (q : tensorTotal X A I ⟶ J) [QuasiIso q]
    {P : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ}
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) P)
    (α : P ⟶ restrictComplex X N U) (m : ℤ)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m))
    (a b n : ℤ)
    (hKamp : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over U))
      (DerivedCategory.Q.obj (restrictComplex X A U)) a)
    (hLGE : (DerivedCategory.Q.obj (restrictComplex X I U)).IsGE b)
    (hn : n < a + b - m) :
    IsIso (HomologicalComplex.homologyMap
      (restrictComplexMap X U (derivedTensorHomMapOfModels X (N := N) q)) n) := by
  have hcmJ : IsIso ((derivedHomRestriction X U).complexMap N J) :=
    isIso_of_isInternalHomRestrictionMap X U N J _
      ((derivedHomRestriction X U).complexMap_isRestriction N J)
  have hcmI : IsIso ((derivedHomRestriction X U).complexMap N I) :=
    isIso_of_isInternalHomRestrictionMap X U N I _
      ((derivedHomRestriction X U).complexMap_isRestriction N I)
  have htt : IsIso (tensorTotalMap (X.over U) (𝟙 (restrictComplex X A U))
      ((derivedHomRestriction X U).complexMap N I)) :=
    isIso_tensorTotalMap_id_iso (X.over U) (restrictComplex X A U) _ _
      (@asIso _ _ _ _ ((derivedHomRestriction X U).complexMap N I) hcmI)
  have hQq : IsIso (DerivedCategory.Q.map (restrictComplexMap X U q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have : (show CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
      restrictComplex X I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  have : (show CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) ℤ from
      restrictComplex X J U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U J
  have hq2 : IsIso (DerivedCategory.Q.map ((tensorTotalOverIso X U A I).inv ≫
      restrictComplexMap X U q)) := by
    have hmap : DerivedCategory.Q.map ((tensorTotalOverIso X U A I).inv ≫
          restrictComplexMap X U q) =
        DerivedCategory.Q.map (tensorTotalOverIso X U A I).inv ≫
          DerivedCategory.Q.map (restrictComplexMap X U q) :=
      Functor.map_comp _ _ _
    rw [hmap]
    exact Iso.isIso_hom (DerivedCategory.Q.mapIso (tensorTotalOverIso X U A I).symm ≪≫
      @asIso _ _ _ _ (DerivedCategory.Q.map (restrictComplexMap X U q)) hQq)
  have hdiag : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) n).map
      (derivedTensorHomDiagonal (X.over U)
        (DerivedCategory.Q.obj (restrictComplex X A U))
        (DerivedCategory.Q.obj (restrictComplex X I U))
        (DerivedCategory.Q.obj (restrictComplex X N U)))) :=
    isIso_homologyMap_derivedTensorHomDiagonal_of_approximation (X.over U) _ _ _
      hP.bounded (fun i => IsDirectSummandOfFiniteFree.isFiniteFreeSummand (X.over U)
        (hP.termDirectSummand i)) (DerivedCategory.Q.map α) m
      (fun i hi => isIso_homologyFunctor_Q_map_of_isIso α i (hiso i hi))
      (epi_homologyFunctor_Q_map_of_epi α m hepi) a b n hKamp hLGE hn
  have hinner : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) n).map
      (DerivedCategory.Q.map
      (derivedTensorHomMapOfModels (X.over U) (N := restrictComplex X N U)
        ((tensorTotalOverIso X U A I).inv ≫ restrictComplexMap X U q)))) := by
    rw [← derivedTensorHomDiagonal_eq_ofModels (X.over U)
      (DerivedCategory.Q.obj (restrictComplex X A U))
      (DerivedCategory.Q.obj (restrictComplex X I U))
      (DerivedCategory.Q.obj (restrictComplex X N U))
      hA (Iso.refl _) (Iso.refl _) (Iso.refl _) _ hq2]
    rw [Functor.map_comp, Functor.map_comp]
    have := hdiag
    infer_instance
  have hfac := restrictComplexMap_derivedTensorHomMapOfModels_comp_complexMap X U (N := N) q
  have hD := isIso_homologyMap_of_isIso_homologyFunctor_Q_map _ n hinner
  refine @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ ?_ ?_
    (((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      (congrArg (HomologicalComplex.homologyMap · n) hfac)).trans
      ((HomologicalComplex.homologyMap_comp _ _ n).trans
        (congrArg (_ ≫ ·) (HomologicalComplex.homologyMap_comp _ _ n))))
  · exact (HomologicalComplex.homologyFunctor _ _ n).map_isIso _
  · exact IsIso.comp_isIso' (Iso.isIso_hom ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (tensorTotalOverIso X U A (sheafHomComplex X N I).obj)))
      (IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _
        (HomologicalComplex.homologyFunctor _ _ n) _ htt) hD)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **The diagonal of Stacks 0BYS is an isomorphism at a pseudo-coherent source, a
cohomologically bounded-below target and a tensor factor of Tor amplitude in `[a, ∞)`.** For
objects `K`, `L`, `M` of `D(O)` with `M` pseudo-coherent, the cohomology of `L` vanishing in
degrees `≪ 0` and `K` of Tor amplitude in `[a, ∞)`,

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism.

Pseudo-coherence is `AlgebraicGeometry.RingedSite.IsPseudoCoherent`, Tor amplitude in `[a, ∞)`
is `Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE` for the canonical derived
tensor product, and boundedness below is vanishing of the cohomology sheaves in degrees `≪ 0`.
-/
@[stacks 0ATN "part (3), with the tensor factor of Tor amplitude in [a, ∞) rather than of \
finite Tor dimension"]
public theorem isIso_derivedTensorHomDiagonal_of_isPseudoCoherent_of_hasTorAmplitudeGE
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : ℤ)
    (hM : X.IsPseudoCoherent M)
    (hL : DerivedCategoryB.IsBoundedBelow L)
    (hK : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K a) :
    IsIso (derivedTensorHomDiagonal X K L M) := by
  classical
  obtain ⟨N, hN, ⟨eN⟩⟩ := hM
  obtain ⟨A, fA, hAkf, hAflat, hAq, hAepi, hArestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O
      (kFlatModel X K)
  have hfA : IsIso (DerivedCategory.Q.map fA) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hAq
  obtain ⟨b, hb⟩ := hL
  have hLGE : L.IsGE b := (DerivedCategory.isGE_iff L b).mpr hb
  have hIGE : (DerivedCategory.Q.obj (kInjectiveModel X L)).IsGE b := by
    have := hLGE
    exact DerivedCategory.TStructure.t.isGE_of_iso (kInjectiveModelIso X L).symm b
  have hq : IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app
      (tensorTotal X A (kInjectiveModel X L)))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  rw [isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels X K L M hAkf
    (asIso (DerivedCategory.Q.map fA) ≪≫ kFlatModelIso X K) (kInjectiveModelIso X L) eN
    ((kInjectiveAugmentation X).app (tensorTotal X A (kInjectiveModel X L))) hq]
  have hfam : ∀ n : ℤ, ∃ (κ : Type u) (V : κ → X.C), X.J.CoversTop V ∧
      ∀ k, ∃ P : CochainComplex
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V k))) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V k)) P ∧
          ∃ α : P ⟶ X.restrictComplex N (V k),
            (∀ j : ℤ, a + b - n - 1 < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
              Epi (HomologicalComplex.homologyMap α (a + b - n - 1)) := fun n =>
    exists_coversTop_isStrictlyPerfect_of_isPseudoCoherentComplexFrom X N (a + b - n - 1)
      (hN (a + b - n - 1))
  choose κ V hV hPdata using hfam
  refine Stacks.SheafOfModules.quasiIso_of_coversTop_degreewise hV _ ?_
  intro n k
  obtain ⟨P, hP, α, hiso, hepi⟩ := hPdata n k
  have hpl : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V n k)) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits (V n k)
  have hpc : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V n k)) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits (V n k)
  have hKampU : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over (V n k)))
      (DerivedCategory.Q.obj (restrictComplex X A (V n k))) a :=
    (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_derivedRestriction
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) (V n k)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (X.over (V n k))) K a hK).of_iso
      (restrictModelIso X (V n k) (asIso (DerivedCategory.Q.map fA) ≪≫ kFlatModelIso X K))
  exact isIso_homologyMap_restrictComplexMap_of_approximation X (V n k) (hArestr (V n k)) _ hP α
    (a + b - n - 1) hiso hepi a b n hKampU
    (isGE_Q_obj_restrictComplex X (V n k) _ b hIGE) (by omega)

omit [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 0ATN part (3): the diagonal of Stacks 0BYS is an isomorphism at a pseudo-coherent
source, a cohomologically bounded-below target and a tensor factor of finite Tor dimension.**
For objects `K`, `L`, `M` of `D(O)` with `M` pseudo-coherent, the cohomology of `L` vanishing in
degrees `≪ 0` and `K` of finite Tor dimension,

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism.

The three hypotheses are the site-level notions: pseudo-coherence is
`AlgebraicGeometry.RingedSite.IsPseudoCoherent` of Stacks 08FT, finite Tor dimension is
`Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension` of Stacks 08FZ for the
canonical derived tensor product, and boundedness below is vanishing of the cohomology sheaves
in degrees `≪ 0`. -/
@[stacks 0ATN "part (3)"]
public theorem isIso_derivedTensorHomDiagonal_of_isPseudoCoherent
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hM : X.IsPseudoCoherent M)
    (hL : DerivedCategoryB.IsBoundedBelow L)
    (hK : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K) :
    IsIso (derivedTensorHomDiagonal X K L M) := by
  obtain ⟨a, b₀, hab, hamp⟩ :=
    (Stacks.SheafOfModules.DerivedTensorProduct.hasFiniteTorDimension_iff _ K).1 hK
  exact isIso_derivedTensorHomDiagonal_of_isPseudoCoherent_of_hasTorAmplitudeGE X K L M a hM hL
    (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_hasTorAmplitude _ _ a b₀
      hamp)

end Assembly

end AlgebraicGeometry.RingedSite

end
