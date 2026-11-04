module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.SpectralSequence.Tor
public import StacksFrontier.Homology.KFlat.ProjectiveResolution
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# The derived tensor product of two modules computes `Tor`

Let `A` be a commutative ring and let `M` and `N` be `A`-modules. Placing both in degree zero
and forming the canonical derived tensor product of [Stacks, Tag 0BYI] gives an object of the
derived category of `A`-modules whose cohomology in degree `-i` is `Tor_i^A(M, N)`:

`H^{-i}(M[0] ⊗^L_A N[0]) ≅ Tor_i^A(M, N)`.

Here `Tor_i^A(M, N)` is Mathlib's `CategoryTheory.Tor (ModuleCat A) i`, which derives the
*second* variable, while the derived tensor product above is computed from a K-flat — here
projective — resolution of the *first*. The Koszul braiding of the tensor product of modules
exchanges the variables, and the resolution of the first variable becomes a resolution computing
the left derived functors of `N ⊗ -`.

## Main definitions

* `Stacks.DerivedTensor.tensorResolutionHomologyIso`: tensoring a K-flat complex with a
  resolution of a module computes the same homology as tensoring it with the module termwise.
* `Stacks.DerivedTensor.torIsoOfKFlatResolution`: a K-flat resolution of `M` computes
  `Tor_n(M, X)` as the degree `-n` homology of its termwise tensor product with `X`.
* `Stacks.DerivedTensor.homologyIsoTor`: **the identification
  `H^{-i}(M[0] ⊗^L_A N[0]) ≅ Tor_i^A(M, N)`.**

## Main results

* `Stacks.DerivedTensor.isZero_homology_iff_isZero_tor`: the vanishing of
  `H^{-i}(M[0] ⊗^L_A N[0])` is the vanishing of `Tor_i^A(M, N)`.

## Implementation notes

`Stacks.DerivedTensor.homologyZeroIsoTensorProduct` is the degree-zero case of
`homologyIsoTor`, read through `Functor.leftDerivedZeroIsoSelf`. No Tor balancing
([Stacks, Tag 00M1]) is needed: the braiding
`CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight` is applied to the *termwise* tensor
complex, before any derived functor is formed, so the two sides are computed from a resolution
of the same variable throughout.

The derived category model is `CategoryTheory.HasDerivedCategory.standard`, because
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` is defined in that model.

## References

* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 08BP](https://stacks.math.columbia.edu/tag/08BP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedTensor

/-- Tensoring a K-flat complex with a resolution of `Z` computes the same homology as tensoring
it with `Z` termwise. -/
def tensorResolutionHomologyIso
    {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    (Z : ModuleCat.{u} R) {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (ε : P ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj Z)
    [QuasiIso ε] (n : ℤ) :
    (HomologicalComplex.mapBifunctor K P
        (CochainComplex.Tor.moduleTensorBifunctor R) (ComplexShape.up ℤ)).homology n ≅
      (((tensorLeft Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n := by
  let : QuasiIso ((TrightCochain K).map ε) :=
    CochainComplex.DerivedTensor.quasiIso_tright_map K hK ε
  exact HomologicalComplex.homologyMapIso (CochainComplex.DerivedTensor.tensorFlipIso K P) n ≪≫
    isoOfQuasiIsoAt ((TrightCochain K).map ε) n ≪≫
      HomologicalComplex.homologyMapIso (TotalTensorComplex.SingleTensor.singleTensorIso Z K) n

/-- A K-flat resolution of `M` computes `Tor_n(M, X)` as the degree `-n` homology of its
termwise tensor product with `X`. -/
def torIsoOfKFlatResolution {R : Type u} [CommRing R]
    {M : ModuleCat.{u} R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (ε : P ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M)
    [QuasiIso ε] [P.IsStrictlyLE 0] (hP : P.KFlat)
    (X : ModuleCat.{u} R) (n : ℤ) :
    (((tensorLeft X).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology (-n) ≅
      CochainComplex.Tor.TorInDegree.{u, u} R n M X := by
  by_cases hn : 0 ≤ n
  · let Q := ProjectiveResolution.of X
    let F := (CochainComplex.Tor.moduleTensorBifunctor.{u, u} R).obj M
    let C := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
    have he : ComplexShape.embeddingDownNat.f n.toNat = -n := by
      change -(n.toNat : ℤ) = -n
      rw [Int.toNat_of_nonneg hn]
    have eT : (C.extend ComplexShape.embeddingDownNat).homology (-n) ≅
        C.homology n.toNat :=
      HomologicalComplex.extendHomologyIso C ComplexShape.embeddingDownNat he
    have eP : (F.leftDerived n.toNat).obj X ≅ C.homology n.toNat :=
      Q.isoLeftDerivedObj F n.toNat
    have e₀ : (((tensorLeft M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        Q.cochainComplex).homology (-n) ≅
        (C.extend ComplexShape.embeddingDownNat).homology (-n) :=
      HomologicalComplex.homologyMapIso
        (HomologicalComplex.mapHomologicalComplexExtendIso (tensorLeft M) Q.complex
          ComplexShape.embeddingDownNat).symm (-n)
    have e := (tensorResolutionHomologyIso P hP X Q.π' (-n)).symm ≪≫
      HomologicalComplex.homologyMapIso
        (CochainComplex.DerivedTensor.tensorFlipIso P Q.cochainComplex) (-n) ≪≫
      tensorResolutionHomologyIso Q.cochainComplex
        (_root_.CochainComplex.KFlat.kFlat_projectiveResolution Q) M ε (-n) ≪≫
      e₀ ≪≫ eT ≪≫ eP.symm
    simpa only [CochainComplex.Tor.TorInDegree, dite_eq_left hn] using e
  · have hX : IsZero ((((tensorLeft X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P).X (-n)) :=
      (tensorLeft X).map_isZero (CochainComplex.isZero_of_isStrictlyLE P 0 (-n) (by lia))
    exact (ShortComplex.isZero_homology_of_isZero_X₂ _ hX).iso
      (by
        rw [ModuleCat.isZero_iff_subsingleton]
        unfold CochainComplex.Tor.TorInDegree
        simp only [dite_eq_right (show ¬ 0 ≤ n by lia)]
        infer_instance)

/-- **The derived tensor product computes `Tor`: `H^{-i}(M[0] ⊗^L_A N[0]) ≅ Tor_i^A(M, N)`.**

The degree `-i` cohomology of the canonical derived tensor product of two modules placed in
degree zero is their `i`-th Tor module. -/
def homologyIsoTor
    (A : Type u) [CommRing A] (M N : ModuleCat.{u} A) (i : ℕ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) ≅
      (((Tor (ModuleCat.{u} A) i).obj M).obj N) := by
  let Q := ProjectiveResolution.of M
  let P := Q.cochainComplex
  let M₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  let N₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N
  let : QuasiIso Q.π' := inferInstance
  let : P.IsStrictlyLE 0 := inferInstance
  have hP : P.KFlat := _root_.CochainComplex.KFlat.kFlat_projectiveResolution Q
  have hbounded : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (P.X j) :=
    ⟨0, fun j hj => CochainComplex.isZero_of_isStrictlyLE P 0 j hj⟩
  have hflat : ∀ j : ℤ, Module.Flat A (P.X j) := by
    intro j
    have : Module.Projective A (P.X j) := ModuleCat.projective_of_module_projective _
    infer_instance
  let eP : DerivedCategory.Q.obj P ≅ M₀ := asIso (DerivedCategory.Q.map Q.π')
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))
  let eRep := H.mapIso
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A).mapIso eP).app N₀)
  let eComparison := StacksDraft.TorAmplitude.certifiedTensorHomologyIsoOfFlat
    (StacksDraft.TorAmplitude.canonicalTensorComparison A)
    (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived A)
    P hbounded hflat N (-(i : ℤ))
  let eFlip := (NatIso.mapHomologicalComplex
    (BraidedCategory.tensorLeftIsoTensorRight N) (ComplexShape.up ℤ)).app P
  let eTor := torIsoOfKFlatResolution Q.π' hP N (i : ℤ)
  have eTor' :
      (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology (-(i : ℤ)) ≅
        (((Tor (ModuleCat.{u} A) i).obj M).obj N) := by
    change (((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology
        (-(i : ℤ)) ≅
      ((((CochainComplex.Tor.moduleTensorBifunctor A).obj M).leftDerived i).obj N)
    simpa only [P, CochainComplex.Tor.TorInDegree,
      dite_eq_left (show 0 ≤ (i : ℤ) by lia),
      Int.toNat_natCast] using eTor
  exact eRep.symm ≪≫ eComparison ≪≫
    HomologicalComplex.homologyMapIso eFlip.symm (-(i : ℤ)) ≪≫ eTor'

/-- **The vanishing of `H^{-i}(M[0] ⊗^L_A N[0])` is the vanishing of `Tor_i^A(M, N)`.** -/
theorem isZero_homology_iff_isZero_tor
    (A : Type u) [CommRing A] (M N : ModuleCat.{u} A) (i : ℕ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))) ↔
      IsZero (((Tor (ModuleCat.{u} A) i).obj M).obj N) :=
  (homologyIsoTor A M N i).isZero_iff

end Stacks.DerivedTensor

end
