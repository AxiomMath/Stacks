module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.DerivedPullbackOfATilde
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffinePullbackSections
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.TransportAlongAnIsomorphism

/-!
# The derived-fibre Euler characteristic on an affine chart

Let `R` be a ring and `P` a bounded complex of finite projective `R`-modules. The derived-fibre
Euler characteristic of the associated object `P̃` of `D(𝒪_{Spec R})` at a prime `𝔭` is
`∑ (-1)^i rank_𝔭(P^i)`. Consequently, if an object `E` of `D(𝒪_X)` on a scheme `X` is, on an
affine open `V`, the derived sheafification of such a complex of `Γ(X, V)`-modules, then the
derived-fibre Euler characteristic of `E` at a point of `V` is computed by the ranks of the
terms of that complex at the corresponding prime.

## Main results

* `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_tildeComplex`: the derived-fibre Euler
  characteristic of `P̃` at `𝔭` is `∑ (-1)^i rank_𝔭(P^i)`.
* `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_eq_of_derivedRestrict_iso`: the same
  value for an object of `D(𝒪_X)` whose restriction to an affine open `V` is identified, along
  `V ≅ Spec Γ(X, V)`, with `P̃`.
* `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_eq_zero_of_isRankZeroScheme`: an object of
  rank zero, in the sense of `AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroScheme`, has
  vanishing derived-fibre Euler characteristic.

## Implementation notes

At a prime `𝔭` the derived fibre of `P̃` is computed by the degreewise pullback along
`Spec κ(𝔭) ⟶ Spec R`, because `P` is K-flat (Stacks 064K) and so is `P̃`. That morphism is the
spectrum of a ring map `R → κ(𝔭)`, so by Stacks 01I9 the global sections of the pullback of
`(P^i)^~` are `κ(𝔭) ⊗_R P^i`, of dimension `rank_𝔭(P^i)`. The alternating sum of the dimensions
of the cohomology of a bounded complex of finite-dimensional vector spaces is that of its terms.

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open scoped TensorProduct

namespace AlgebraicGeometry.DerivedFibreBetti

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The rank of a finite projective module at a point of `Spec R` is the dimension of its fibre
there.** For the canonical morphism `Spec κ(𝔭) ⟶ Spec R`, which is the spectrum of a ring map
`φ : R → κ(𝔭)`, the `κ(𝔭)`-vector space `κ(𝔭) ⊗_R N` has dimension `rank_𝔭(N)`. -/
theorem finrank_tensor_eq_rankAtStalk (R : CommRingCat.{u}) (p : Spec R)
    (φ : R ⟶ (Spec R).residueField p)
    (hφ : Spec.map φ = (Spec R).fromSpecResidueField p) (N : Type u) [AddCommGroup N]
    [Module R N] [Module.Finite R N] [Module.Projective R N] :
    letI := φ.hom.toAlgebra
    Module.finrank ((Spec R).residueField p) (((Spec R).residueField p) ⊗[R] N) =
      Module.rankAtStalk N p := by
  let := φ.hom.toAlgebra
  let s : Spec ((Spec R).residueField p) := IsLocalRing.closedPoint _
  have h₂ := Module.rankAtStalk_baseChange (R := R) (M := N) s
  have h₃ : s.comap (algebraMap R ((Spec R).residueField p)) = p := by
    have := (Spec R).fromSpecResidueField_apply p s
    rwa [← hφ] at this
  rw [h₃] at h₂
  exact (congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := (Spec R).residueField p) (M := ((Spec R).residueField p) ⊗[R] N)) s).symm.trans h₂

/-- The terms of a complex that is strictly `≥ a` and strictly `≤ b` vanish outside `[a, b]`. -/
private theorem isZero_X_of_notMem_Icc {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    {i : ℤ} (hi : i ∉ Set.Icc a b) : IsZero (C.X i) := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
  rcases hi with h | h
  exacts [C.isZero_of_isStrictlyGE a i h, C.isZero_of_isStrictlyLE b i h]

/-- For a complex concentrated in degrees `-1` and `0`, the alternating sum of the ranks of its
terms at a prime is the rank of the degree `0` term minus that of the degree `-1` term. -/
theorem finsum_negOnePow_rankAtStalk_of_twoTerm {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (hGE : C.IsStrictlyGE (-1))
    (hLE : C.IsStrictlyLE 0) (q : PrimeSpectrum R) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (C.X i) q : ℤ) =
      (Module.rankAtStalk (C.X 0) q : ℤ) - Module.rankAtStalk (C.X (-1)) q := by
  classical
  have hzero (i : ℤ) (hi : i ∉ ({-1, 0} : Finset ℤ)) : Module.rankAtStalk (C.X i) q = 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    have : Subsingleton (C.X i) := ModuleCat.subsingleton_of_isZero
      (isZero_X_of_notMem_Icc C (-1) 0 fun h => hi (by rw [Set.mem_Icc] at h; omega))
    exact congrFun Module.rankAtStalk_eq_zero_of_subsingleton q
  rw [finsum_eq_sum_of_support_subset (s := ({-1, 0} : Finset ℤ))]
  · rw [Finset.sum_pair (by decide)]
    simp only [Int.negOnePow_neg, Int.negOnePow_one, Int.negOnePow_zero, Units.val_neg,
      Units.val_one]
    ring
  · intro i hi
    by_contra h
    exact hi (by simp only [hzero i (by simpa using h), Nat.cast_zero, mul_zero])

open Stacks.Cohomology.DerivedPullbackOfATilde in
/-- **The derived-fibre Euler characteristic of the sheaf associated with a bounded complex of
finite projective modules.** For a bounded complex `P` of finite projective `R`-modules, the
derived-fibre Euler characteristic of `P̃` at a prime `𝔭` of `R` is `∑ (-1)^i rank_𝔭(P^i)`.

The derived fibre at `𝔭` is the degreewise pullback of `P̃` along `Spec κ(𝔭) ⟶ Spec R`, as `P̃` is
K-flat; its terms are, on global sections, the vector spaces `κ(𝔭) ⊗_R P^i` by Stacks 01I9, and
the Euler characteristic of a bounded complex of finite-dimensional vector spaces is the
alternating sum of the dimensions of its terms. -/
theorem chiDerivedFibre_tildeComplex (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)]
    (hpc : RingedSpace.IsPseudoCoherent (X := (Spec R).toRingedSpace)
      (DerivedCategory.Q.obj (tildeComplex P)))
    (p : Spec R) :
    chiDerivedFibre (Spec R) (DerivedCategory.Q.obj (tildeComplex P)) hpc p =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (P.X i) p : ℤ) := by
  classical
  let k := (Spec R).residueField p
  let g := (Spec R).fromSpecResidueField p
  let f := g.toLRSHom.toShHom
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ k, Spec.map φ = g := ⟨Spec.preimage g, Spec.map_preimage g⟩
  let := φ.hom.toAlgebra
  let G := moduleSpecΓFunctor (R := k)
  let F : SheafOfModules.{u} (structureSheafRing (Spec R).toRingedSpace) ⥤ (Spec k).Modules :=
    modulePullback f
  have hGa : G.Additive := additive_moduleSpecΓFunctor
  have hFa : F.Additive := modulePullback_additive f
  have hGH : G.PreservesHomology := preservesHomology_moduleSpecΓFunctor (Field.toIsField _)
  let T := tildeComplex P
  let B := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj T
  let C := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj B
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R k)) = g := hφ
  let eTerm (i : ℤ) : C.X i ≃ₗ[k] k ⊗[R] P.X i :=
    (G.mapIso (eqToIso (congrArg (fun h => (Scheme.Modules.pullback h).obj (tilde (P.X i)))
      hg.symm))).toLinearEquiv.trans (pullbackTildeΓTensorEquiv (R := R) (S := k) (P.X i))
  have hfin (i : ℤ) : Module.Finite k (C.X i) := Module.Finite.equiv (eTerm i).symm
  have hsupp : {i : ℤ | ¬ IsZero (C.X i)}.Finite := by
    refine (Set.finite_Icc a b).subset fun i hi => ?_
    by_contra hab
    exact hi (Functor.map_isZero G (Functor.map_isZero F
      (Functor.map_isZero (tildeFunctor R) (isZero_X_of_notMem_Icc P a b hab))))
  let eD := derivedPullbackTildeIso f P (CochainComplex.KFlat.kFlat_of_flat P b)
  let eH (i : ℤ) : G.obj ((DerivedCategory.homologyFunctor (Spec k).Modules i).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj
        (DerivedCategory.Q.obj T))) ≅ C.homology i :=
    G.mapIso ((DerivedCategory.homologyFunctor _ i).mapIso eD ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app B) ≪≫
      ((B.sc i).mapHomologyIso G).symm
  calc
    chiDerivedFibre (Spec R) (DerivedCategory.Q.obj T) hpc p =
        HomologicalComplex.homologyEulerChar C :=
      finsum_congr fun i => congrArg (fun r : ℕ => (i.negOnePow : ℤ) * (r : ℤ))
        (eH i).toLinearEquiv.finrank_eq
    _ = HomologicalComplex.eulerChar C :=
      StacksDraft.Perfect.homologyEulerChar_eq_eulerChar C hfin hsupp
    _ = ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (P.X i) p : ℤ) :=
      finsum_congr fun i => congrArg (fun r : ℕ => (i.negOnePow : ℤ) * (r : ℤ))
        ((eTerm i).finrank_eq.trans (finrank_tensor_eq_rankAtStalk R p φ hφ (P.X i)))

open Stacks.Cohomology.DerivedPullbackOfATilde in
/-- **The derived-fibre Euler characteristic read on an affine chart.** Let `E₀` be a complex of
`𝒪_X`-modules whose class is pseudo-coherent, and let `V` be an affine open of `X` on which the
class of `E₀` is, along `V ≅ Spec Γ(X, V)`, the derived sheafification of a bounded complex `P` of
finite projective `Γ(X, V)`-modules. Then at a point `x` of `V` the derived-fibre Euler
characteristic of `E₀` is `∑ (-1)^i rank_𝔭(P^i)`, for `𝔭` the prime of `Γ(X, V)` corresponding
to `x`.

Base change along the open immersion `V ⟶ X` and along `V ≅ Spec Γ(X, V)` (Stacks 0BDI) moves
the computation to `Spec Γ(X, V)`, where it is `chiDerivedFibre_tildeComplex`. -/
theorem chiDerivedFibre_eq_of_derivedRestrict_iso {X : Scheme.{u}}
    (E₀ : CochainComplex X.Modules ℤ)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) (DerivedCategory.Q.obj E₀))
    {V : X.Opens} (hV : IsAffineOpen V) (P : CochainComplex (ModuleCat.{u} Γ(X, V)) ℤ)
    (a b : ℤ) (hGE : P.IsStrictlyGE a) (hLE : P.IsStrictlyLE b)
    (hfin : ∀ i, Module.Finite Γ(X, V) (P.X i)) (hproj : ∀ i, Module.Projective Γ(X, V) (P.X i))
    (e : (RingedSpace.derivedRestrictModules X.toRingedSpace V).obj
        (DerivedCategory.Q.obj E₀) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (Stacks.Cohomology.TransportAlongIso.ringedSpaceIsoOfSchemeIso hV.isoSpec).hom).obj
        ((tilde.functor Γ(X, V)).mapDerivedCategory.obj (DerivedCategory.Q.obj P)))
    (x : X) (hx : x ∈ V) :
    chiDerivedFibre X (DerivedCategory.Q.obj E₀) hpc x =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) *
        (Module.rankAtStalk (P.X i) (hV.primeIdealOf ⟨x, hx⟩) : ℤ) := by
  have hperf : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec Γ(X, V)).toRingedSpace)
      (DerivedCategory.Q.obj (tildeComplexMod P)) :=
    (isPerfect_tildeComplex_iff P).2 ⟨P, a, b, inferInstance, inferInstance,
      fun i => inferInstance, fun i => inferInstance, ⟨Iso.refl _⟩⟩
  have hpcT : RingedSpace.IsPseudoCoherent (X := (Spec Γ(X, V)).toRingedSpace)
      (DerivedCategory.Q.obj (tildeComplex P)) :=
    (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'
      (X := (Spec Γ(X, V)).toRingedSpace) _).1
      (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect
        (X := (Spec Γ(X, V)).toRingedSpace) _ hperf)
  let e₁ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        V.ι.toLRSHom.toShHom).obj (DerivedCategory.Q.obj E₀) ≅
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        hV.isoSpec.hom.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (tildeComplex P)) :=
    derivedPullbackOpenQIso V E₀ ≪≫
      (RingedSpace.derivedRestrictModulesObjQIso X.toRingedSpace V E₀).symm ≪≫ e ≪≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        hV.isoSpec.hom.toLRSHom.toShHom).mapIso
        ((tilde.functor Γ(X, V)).mapDerivedCategoryFactors.app P)
  have h₁ := congrFun (chiDerivedFibre_derivedPullback V.ι (DerivedCategory.Q.obj E₀) hpc)
    ⟨x, hx⟩
  have h₂ := congrFun (chiDerivedFibre_congr V.toScheme
    (isPseudoCoherent_derivedPullback V.ι (DerivedCategory.Q.obj E₀) hpc)
    (isPseudoCoherent_derivedPullback hV.isoSpec.hom _ hpcT) e₁) ⟨x, hx⟩
  have h₃ := congrFun (chiDerivedFibre_derivedPullback hV.isoSpec.hom
    (DerivedCategory.Q.obj (tildeComplex P)) hpcT) ⟨x, hx⟩
  exact h₁.symm.trans (h₂.trans (h₃.trans
    (chiDerivedFibre_tildeComplex Γ(X, V) P a b hpcT (hV.isoSpec.hom ⟨x, hx⟩))))

/-- **A rank-zero object has vanishing derived-fibre Euler characteristic.** If the class of a
complex of `𝒪_X`-modules is pseudo-coherent and of rank zero in the sense of
`AlgebraicGeometry.DeterminantTwoTerm.IsRankZeroScheme`, then its derived-fibre Euler
characteristic vanishes at every point: near each point it is the derived sheafification of a
two-term complex of finite projective modules whose terms have equal rank at every prime. -/
theorem chiDerivedFibre_eq_zero_of_isRankZeroScheme {X : Scheme.{u}}
    (E₀ : CochainComplex X.Modules ℤ)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) (DerivedCategory.Q.obj E₀))
    (h0 : DeterminantTwoTerm.IsRankZeroScheme (DerivedCategory.Q.obj E₀)) (x : X) :
    chiDerivedFibre X (DerivedCategory.Q.obj E₀) hpc x = 0 := by
  obtain ⟨V, hV, hxV, M, ⟨P, hP⟩, ⟨e⟩⟩ := h0 x
  rw [chiDerivedFibre_eq_of_derivedRestrict_iso E₀ hpc hV P.complex (-1) 0 P.strictlyGE
      P.strictlyLE P.finite P.projective
      (e ≪≫ (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (Stacks.Cohomology.TransportAlongIso.ringedSpaceIsoOfSchemeIso hV.isoSpec).hom).mapIso
        ((tilde.functor Γ(X, V)).mapDerivedCategory.mapIso P.iso)) x hxV,
    finsum_negOnePow_rankAtStalk_of_twoTerm _ P.strictlyGE P.strictlyLE,
    ← hP (hV.primeIdealOf ⟨x, hxV⟩), sub_self]

end AlgebraicGeometry.DerivedFibreBetti

end
