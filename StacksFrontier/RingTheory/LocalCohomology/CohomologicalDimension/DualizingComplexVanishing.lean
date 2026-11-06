module

public import Mathlib.CategoryTheory.Localization.Linear
public import StacksFrontier.Algebra.Homology.HomologyFunctorLinear
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.MinimalPrimeNonvanishing
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.HartshorneLichtenbaum
public import StacksFrontier.RingTheory.LocalCohomology.TopDegreeDivisibility
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.RingTheory.LocalCohomology.ArtinianOverLocalRing

/-!
# Hartshorne–Lichtenbaum vanishing from a dualizing complex

Let `A` be a Noetherian local ring of dimension `d` with a normalized dualizing complex
`ω_A^•`, and let `I ⊆ A` be an ideal. If the degree-zero local cohomology
`H^0_{V(I)}(ω_A^•)` vanishes, then the cohomological dimension of `I` is strictly less
than `d`.

Write `ω_A = H^{-d}(ω_A^•)`. The cohomology modules `H^{-i}(ω_A^•)` are finite and vanish
outside `0 ≤ i ≤ d`, and the support of `H^{-i}(ω_A^•)` has dimension at most `i`; so prime
avoidance produces an element `f ∈ A` lying outside every minimal prime `p` with
`dim(A/p) = d` and annihilating `H^i(ω_A^•)` for every `i > -d`. On the truncation
`U = τ_{≥ -d + 1}ω_A^•`, which is bounded, the endomorphism `f • 𝟙` is therefore zero on every
homology object, hence nilpotent, say `(f • 𝟙_U)^{n + 1} = 0`. Applying the triangulated,
`A`-linear functor `RΓ_{V(I)}` and taking homology, `f^{n + 1}` annihilates
`H^{-1}_{V(I)}(U)`. The truncation triangle `ω_A[d] → ω_A^• → U` becomes, after `RΓ_{V(I)}`, a
distinguished triangle whose homology sequence contains

`H^{-1}_{V(I)}(U) → H^0_{V(I)}(ω_A[d]) → H^0_{V(I)}(ω_A^•) = 0`,

so `f^{n + 1}` annihilates `H^0_{V(I)}(ω_A[d]) = H^d_{V(I)}(ω_A)` as well. Multiplication by
`f` is surjective on that module, so `f^{n + 1}` is too, and the module vanishes. Finally `ω_A`
is nonzero at every minimal prime of dimension `d`, so Hartshorne–Lichtenbaum vanishing for a
single module applies and bounds the cohomological dimension.

## Main results

* `Stacks.LocalCohomology.cohomologicalDimension_lt_of_isZero_homology_localCohomologyDerived` —
  **Stacks 0EB4**: the strict bound `cd(A, I) < dim(A)`.

## Implementation notes

Local cohomology with support in `V(I)` is taken in the coreflection model of Stacks 0A6Q:
`Stacks.LocalCohomology.localCohomologyDerived` is `RΓ_{V(I)}` as an endofunctor of `D(A)`, and
`Stacks.LocalCohomology.localCohomologyModule` is its homology on a module placed in degree
zero. That is the model in which the cohomological dimension, Stacks 0EB2 and Stacks 0EB3 are
stated here, so the whole argument stays inside it and no model comparison is needed. Over a
Noetherian ring it agrees with the supported-sections model of Stacks 0EF4, which is Stacks
0955, available as
`Stacks.LocalCohomology.isIso_compareSectionsWithSupportLocalCohomology_app`.

Three inputs the argument needs about `RΓ_{V(I)}` are supplied here. That it is triangulated and
shift-compatible comes from the adjunction of Stacks 0A6R, as in
`StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated`. That it is `A`-linear is
proved by the general statement that a right adjoint of an `R`-linear functor is `R`-linear:
the inverse of the adjunction bijection is `R`-linear because the inclusion of a full
subcategory is, so testing `G(a • 𝟙) = a • 𝟙` against it suffices. Linearity of the homology
functor on `D(A)` is inherited from the homology functor on cochain complexes along the
localization.

The module universe equals the ring universe. That is what the single-module form of
Hartshorne–Lichtenbaum vanishing is stated at, and the argument needs `ω_A` to be a module in
that universe; nothing is lost, since the statement is about finite modules over a Noetherian
ring.

The dimension of `A` is carried as a natural number `d` together with
`ringKrullDim A = (d : WithBot ℕ∞)`, matching the adjacent statements in this directory, and the
local-cohomology degree and the cohomological dimension are integers.

## References

* [Stacks Project, Tag 0EB4](https://stacks.math.columbia.edu/tag/0EB4)
* [Stacks Project, Tag 0EB2](https://stacks.math.columbia.edu/tag/0EB2)
* [Stacks Project, Tag 0EB3](https://stacks.math.columbia.edu/tag/0EB3)
* [Stacks Project, Tag 0A7V](https://stacks.math.columbia.edu/tag/0A7V)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

attribute [local instance] derivedPowerTorsionProperty_isClosedUnderIsomorphisms
  derivedPowerTorsionProperty_isTriangulated

/-- Local cohomology with support in `V(I)` is `A`-linear: it is the right adjoint of the
inclusion of the derived objects with `I`-power-torsion cohomology, and that inclusion is
`A`-linear because it is the identity on morphisms. -/
private theorem localCohomologyFunctor_linear
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Functor.Linear A (Dualizing.localCohomologyFunctor.{u, u} A I hI) :=
  rightAdjoint_linear (R := A) (Dualizing.localCohomologyAdjunction.{u, u} A I hI)

/-- **A ghost endomorphism of a bounded object is nilpotent.** If `X` lies in the interval
`[a, a + n]` of the standard t-structure and `f : X ⟶ X` induces the zero map on every homology
object, then `f ^ (n + 1) = 0`.

The induction is on the length of the interval: for `n = 0` the object is concentrated in a
single degree and `f = 0`; in general the truncation triangle at `a + n` writes `f` as a
composite through the truncation, on which the inductive hypothesis applies. -/
private lemma ghostEndo_pow_zero
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    (a : ℤ) (n : ℕ) (X : DerivedCategory 𝒜)
    [X.IsGE a] [X.IsLE (a + n)]
    (f : End X)
    (hf : ∀ i : ℤ, (DerivedCategory.homologyFunctor 𝒜 i).map f.asHom = 0) :
    f ^ (n + 1) = 0 := by
  classical
  induction n generalizing X with
  | zero =>
      have : X.IsLE a := by simpa using (inferInstance : X.IsLE (a + (0 : ℕ)))
      have hf0 : f = 0 := End.ext (by rw [hom_eq_zero_of_isLE_isGE X X a f.asHom (hf a)]; rfl)
      rw [hf0]
      simp
  | succ n ih =>
      let b := a + (n : ℤ)
      let hX := X.exists_iso_Q_obj_of_isGE_of_isLE a (a + (n + 1 : ℕ))
      let K := Classical.choose hX
      have hKdata := Classical.choose_spec hX
      have hKGE : K.IsStrictlyGE a := hKdata.1
      have hKLE : K.IsStrictlyLE (a + (n + 1 : ℕ)) := hKdata.2.1
      let e : X ≅ DerivedCategory.Q.obj K := Classical.choice hKdata.2.2
      let X' := DerivedCategory.Q.obj K
      let f' : End X' := .of (e.inv ≫ f.asHom ≫ e.hom)
      have hf' (i : ℤ) : (DerivedCategory.homologyFunctor 𝒜 i).map f'.asHom = 0 := by
        dsimp [f']
        rw [Functor.map_comp, Functor.map_comp, hf i]
        simp
      have : K.IsStrictlyGE a := hKGE
      have : K.IsStrictlyLE (a + (n + 1 : ℕ)) := hKLE
      have : X'.IsLE (a + (n + 1 : ℕ)) := by
        rw [DerivedCategory.isLE_Q_obj_iff]
        infer_instance
      let T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X'
      have hobj₂ : T.obj₂ = X' := by rfl
      let fT : End T.obj₂ := hobj₂.symm ▸ f'
      have hfT (i : ℤ) : (DerivedCategory.homologyFunctor 𝒜 i).map fT.asHom = 0 := by
        cases hobj₂
        exact hf' i
      have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1)
        (by omega) X'
      have : T.obj₁.IsGE a := by
        rw [show T.obj₁ = (DerivedCategory.TStructure.t.truncLE b).obj X' from rfl]
        infer_instance
      have : T.obj₁.IsLE b := by
        rw [show T.obj₁ = (DerivedCategory.TStructure.t.truncLE b).obj X' from rfl]
        infer_instance
      have : T.obj₃.IsGE (b + 1) := by
        rw [show T.obj₃ = (DerivedCategory.TStructure.t.truncGE (b + 1)).obj X' from rfl]
        infer_instance
      have : T.obj₂.IsLE (b + 1) := by
        rw [hobj₂]
        have hb : b + 1 = a + (n + 1 : ℕ) := by dsimp [b]; omega
        rw [hb]
        infer_instance
      have hzero₂ : fT.asHom ≫ T.mor₂ = 0 :=
        hom_eq_zero_of_isLE_isGE T.obj₂ T.obj₃ (b + 1) (fT.asHom ≫ T.mor₂) <| by
          rw [Functor.map_comp, hfT (b + 1), zero_comp]
      obtain ⟨h, hh⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT fT.asHom hzero₂
      let q : End T.obj₁ := .of (T.mor₁ ≫ h)
      have hq (i : ℤ) : (DerivedCategory.homologyFunctor 𝒜 i).map q.asHom = 0 := by
        by_cases hi : i ≤ b
        · have hiota : IsIso ((DerivedCategory.homologyFunctor 𝒜 i).map T.mor₁) := by
            apply isIso_homology_mor₁ T hT i
            · exact DerivedCategory.isZero_of_isGE _ (b + 1) i (by omega)
            · exact DerivedCategory.isZero_of_isGE _ (b + 1) (i - 1) (by omega)
          have hcomp : (DerivedCategory.homologyFunctor 𝒜 i).map h ≫
              (DerivedCategory.homologyFunctor 𝒜 i).map T.mor₁ = 0 := by
            rw [← Functor.map_comp, ← hh, hfT i]
          have hhzero : (DerivedCategory.homologyFunctor 𝒜 i).map h = 0 := by
            apply (cancel_mono ((DerivedCategory.homologyFunctor 𝒜 i).map T.mor₁)).1
            simpa using hcomp
          show (DerivedCategory.homologyFunctor 𝒜 i).map (T.mor₁ ≫ h) = 0
          rw [Functor.map_comp, hhzero, comp_zero]
        · exact (DerivedCategory.isZero_of_isLE T.obj₁ b i (by omega)).eq_of_src _ _
      have hqpow : q ^ (n + 1) = 0 := ih T.obj₁ q hq
      have hpower (m : ℕ) : (fT ^ (m + 1)).asHom = h ≫ (q ^ m).asHom ≫ T.mor₁ := by
        induction m with
        | zero => simp [q, hh]
        | succ m ihm =>
            rw [pow_succ' fT (m + 1), End.mul_asHom, ihm, hh, pow_succ' q m, End.mul_asHom]
            simp [q, Category.assoc]
      have hfpow : f' ^ (n + 2) = 0 := by
        have hfTpow : fT ^ (n + 2) = 0 := by
          ext
          rw [hpower (n + 1), hqpow]
          simp
        cases hobj₂
        exact hfTpow
      have hconj (m : ℕ) : (f' ^ m).asHom = e.inv ≫ (f ^ m).asHom ≫ e.hom := by
        induction m with
        | zero => simp [f', X']
        | succ m ihm =>
            rw [pow_succ', End.mul_asHom, ihm, pow_succ', End.mul_asHom]
            simp [f', Category.assoc]
      have hpow : (f ^ (n + 2)).asHom = e.hom ≫ (f' ^ (n + 2)).asHom ≫ e.inv := by
        rw [hconj]
        simp [Category.assoc]
      rw [hfpow] at hpow
      ext
      simpa using hpow

/-- A functor carries powers of an endomorphism to powers of its image. -/
private lemma map_end_pow {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (X : C) (f : End X) (n : ℕ) :
    ((F.mapEnd X) f) ^ n = (F.mapEnd X) (f ^ n) :=
  (map_pow (F.mapEnd X) f n).symm

/-- **A normalized dualizing complex has no cohomology below degree `-dim A`.** For a degree `i`
below `-dim A` at which the complex is already known to be bounded below, the degree-`i`
cohomology module is zero.

The degree-`i` cohomology is detected by `Ext^i(A, ω_A^•)`, because `A` placed in degree zero is
in `D^{≤0}` and `ω_A^•` is in `D^{≥i}`; and that Ext group vanishes below degree `-dim A` by the
degree bound of Stacks 0A7U, since `A` has support dimension `dim A`. -/
private theorem subsingleton_homology_of_isNormalizedDualizingComplex_of_lt
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) (d : ℕ)
    (hd : ringKrullDim A = (d : WithBot ℕ∞)) (i : ℤ) (hi : i < -(d : ℤ))
    (hGE : K.IsGE i) :
    Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  have hsupport : Module.supportDim A A = (d : WithBot ℕ∞) := by
    rw [Module.supportDim_self_eq_ringKrullDim, hd]
  have hExt : Subsingleton (DerivedCategory.Ext S K i) := by
    refine not_nontrivial_iff_subsingleton.mp fun hnt ↦ ?_
    have := (Dualizing.ext_degree_mem_Icc_of_nontrivial K hK d hsupport i hnt).1
    omega
  have hbij := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    S K 0 i i i (by simp) (by rfl)
  have hHom : Subsingleton
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj S ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) :=
    hbij.2.subsingleton
  let q := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{u} A) 0).app (ModuleCat.of A A)
  refine ⟨fun x y => ?_⟩
  let X := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K
  let fx : ModuleCat.of A A ⟶ X := ModuleCat.ofHom (LinearMap.toSpanSingleton A X x)
  let fy : ModuleCat.of A A ⟶ X := ModuleCat.ofHom (LinearMap.toSpanSingleton A X y)
  have hxy : fx = fy := (cancel_epi q.hom).mp (hHom.allEq _ _)
  simpa [fx, fy] using congrArg (fun f : ModuleCat.of A A ⟶ X => f.hom (1 : A)) hxy

/-- **A normalized dualizing complex lies in degrees `≥ -dim A`.** Its cohomology vanishes below
that degree, so stepwise from the lower end of a bounded interval containing the complex the
bound improves to `-dim A`. -/
private theorem isGE_neg_dimension_of_isNormalizedDualizingComplex
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) (d : ℕ)
    (hd : ringKrullDim A = (d : WithBot ℕ∞)) : K.IsGE (-(d : ℤ)) := by
  obtain ⟨a, b, I, hIge, hIle, hI, ⟨eI⟩⟩ := hK.1.finiteInjectiveDimension
  have : I.IsStrictlyGE a := hIge
  have hbase : K.IsGE a := by
    rw [DerivedCategory.isGE_iff]
    intro j hj
    exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).mapIso eI).isZero_iff.mpr
      (DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj I) a j hj)
  by_cases hai : a ≤ -(d : ℤ)
  · let n : ℕ := (-(d : ℤ) - a).toNat
    have hN : a + (n : ℤ) = -(d : ℤ) := by dsimp [n]; omega
    have hstep : ∀ n' : ℕ, n' ≤ n → K.IsGE (a + (n' : ℤ)) := by
      intro n' hn'
      induction n' with
      | zero => simpa using hbase
      | succ n' ih =>
          have hprev := ih (by omega)
          have hdeg : a + (n' : ℤ) < -(d : ℤ) := by omega
          have hzero := subsingleton_homology_of_isNormalizedDualizingComplex_of_lt
            K hK d hd (a + (n' : ℤ)) hdeg hprev
          rw [DerivedCategory.isGE_iff]
          intro j hj
          by_cases hjlt : j < a + (n' : ℤ)
          · exact DerivedCategory.isZero_of_isGE K (a + (n' : ℤ)) j hjlt
          · obtain rfl : j = a + (n' : ℤ) := by omega
            exact ModuleCat.isZero_iff_subsingleton.mpr hzero
    rw [← hN]
    exact hstep n le_rfl
  · rw [DerivedCategory.isGE_iff]
    intro j hj
    exact DerivedCategory.isZero_of_isGE K a j (by omega)

/-- **Prime avoidance, in the form used below.** An ideal contained in none of finitely many
prime ideals has an element lying in none of them. -/
private lemma exists_mem_notMem_of_forall_not_le {A : Type u} [CommRing A]
    (ps : Finset (Ideal A)) (hprime : ∀ p ∈ ps, p.IsPrime) (J : Ideal A)
    (hnot : ∀ p ∈ ps, ¬ J ≤ p) :
    ∃ f ∈ J, ∀ p ∈ ps, f ∉ p := by
  have hsub : ¬ ((J : Set A) ⊆ ⋃ p ∈ (ps : Set (Ideal A)), (p : Set A)) := by
    rw [Ideal.subset_union_prime (f := fun p : Ideal A => p) (⊥ : Ideal A) (⊥ : Ideal A)
      fun p hp _ _ => hprime p hp]
    exact fun ⟨p, hp, hle⟩ ↦ hnot p hp hle
  obtain ⟨f, hfJ, hf⟩ := Set.not_subset.mp hsub
  exact ⟨f, hfJ, fun p hp hfp => hf (Set.mem_biUnion hp hfp)⟩

/-- **The element `f` of the proof of Stacks 0EB4.** For a normalized dualizing complex `ω_A^•`
over a Noetherian local ring of dimension `d` there is an element `f ∈ A` outside every minimal
prime `p` with `dim(A/p) = d` which annihilates `H^i(ω_A^•)` for every `i` in `[-d + 1, c]`.

The product of those annihilators is contained in no minimal prime `p` with `dim(A/p) = d`: a
prime containing the product contains one of the factors, so `p` lies in the support of
`H^i(ω_A^•)` for some `i ≥ -d + 1`, and by Stacks 0A7V that forces `i = -d`. Prime avoidance then
produces the element. -/
private lemma exists_avoidsTopMinimalPrimes_mem_annihilator_homology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (d : ℕ) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) (c : ℤ) :
    ∃ f : A, (∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
        ringKrullDim (A ⧸ p.asIdeal) = (d : WithBot ℕ∞) → f ∉ p.asIdeal) ∧
      ∀ i ∈ Finset.Icc (-(d : ℤ) + 1) c, f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  classical
  let s : Finset ℤ := Finset.Icc (-(d : ℤ) + 1) c
  let J : Ideal A := s.prod fun i => Module.annihilator A
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing (R := A)
  let ps : Finset (Ideal A) := hfin.toFinset.filter fun p =>
    ringKrullDim (A ⧸ p) = (d : WithBot ℕ∞)
  have hmin : ∀ p ∈ ps, IsMinimalPrime p ∧ ringKrullDim (A ⧸ p) = (d : WithBot ℕ∞) :=
    fun p hp ↦ (Finset.mem_filter.mp hp).imp_left hfin.mem_toFinset.mp
  have hprime : ∀ p ∈ ps, p.IsPrime := fun p hp => (hmin p hp).1.1.1
  have hnot : ∀ p ∈ ps, ¬ J ≤ p := by
    intro p hp hle
    obtain ⟨hpmin, hdim⟩ := hmin p hp
    let q : PrimeSpectrum A := ⟨p, hpmin.1.1⟩
    obtain ⟨i, hi, hAnn⟩ := (hpmin.1.1.prod_le).mp hle
    let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K
    have : Module.Finite A N := hK.1.finiteCohomology i
    have hmem : q ∈ Module.support A N := Module.mem_support_iff_of_finite.mpr hAnn
    rw [Module.mem_support_iff] at hmem
    have hdegree := (Dualizing.nontrivial_localized_homology_iff_eq_neg_dimension
      K hK q hpmin d hdim i).mp hmem
    have hi' : -(d : ℤ) + 1 ≤ i := (Finset.mem_Icc.mp hi).1
    omega
  obtain ⟨f, hfJ, hfavoid⟩ := exists_mem_notMem_of_forall_not_le ps hprime J hnot
  exact ⟨f, fun p hp hdim ↦
    hfavoid p.asIdeal (Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hp, hdim⟩),
    fun i hi ↦ (Ideal.prod_le_inf.trans (Finset.inf_le hi)) hfJ⟩

/-- **Stacks Project, Tag 0EB4.** Let `A` be a Noetherian local ring of dimension `d` with a
normalized dualizing complex `ω_A^•`, and let `I ⊆ A` be an ideal. If `H^0_{V(I)}(ω_A^•) = 0`,
then the cohomological dimension of `I` is strictly less than `d`.

Write `ω_A = H^{-d}(ω_A^•)`. Choose `f ∈ A` outside every minimal prime of dimension `d` which
annihilates `H^i(ω_A^•)` for `i > -d`; then `f` acts as zero on every homology object of
`U = τ_{≥ -d + 1}ω_A^•`, so `f • 𝟙_U` is nilpotent, and therefore a power of `f` annihilates
`H^{-1}_{V(I)}(U)`. The truncation triangle `ω_A[d] → ω_A^• → U` gives, after applying
`RΓ_{V(I)}`, the exact sequence `H^{-1}_{V(I)}(U) → H^0_{V(I)}(ω_A[d]) → H^0_{V(I)}(ω_A^•) = 0`,
so that same power of `f` annihilates `H^d_{V(I)}(ω_A)`. By Stacks 0EB3 multiplication by `f` is
surjective on `H^d_{V(I)}(ω_A)`, whence `H^d_{V(I)}(ω_A) = 0`, and `ω_A` is supported at every
`d`-dimensional minimal prime by Stacks 0A7V, so Stacks 0EB2 applies. -/
@[stacks 0EB4]
theorem cohomologicalDimension_lt_of_isZero_homology_localCohomologyDerived
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K) (I : Ideal A)
    (hvan : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      ((localCohomologyDerived A I (Ideal.fg_of_isNoetherianRing I)).obj K))) :
    cohomologicalDimension A I (Ideal.fg_of_isNoetherianRing I) < (d : ℤ) := by
  classical
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  let C := ModuleCat.{u} A
  let M := (DerivedCategory.homologyFunctor C (-(d : ℤ))).obj K
  have hMfin : Module.Finite A M := hK.1.finiteCohomology (-(d : ℤ))
  have hM : ∀ p : PrimeSpectrum A, IsMinimalPrime p.asIdeal →
      ringKrullDim (A ⧸ p.asIdeal) = (d : WithBot ℕ∞) → p ∈ Module.support A M :=
    fun p hp hdim ↦ Module.mem_support_iff.mpr <|
      (Dualizing.nontrivial_localized_homology_iff_eq_neg_dimension
        K hK p hp d hdim (-(d : ℤ))).mpr rfl
  have htop : IsZero (localCohomologyModule A I hI M (d : ℤ)) := by
    let P := Dualizing.derivedPowerTorsionProperty.{u, u} A I hI
    let G := Dualizing.localCohomologyFunctor.{u, u} A I hI
    let adj : P.ι ⊣ G := Dualizing.localCohomologyAdjunction.{u, u} A I hI
    let : P.ι.CommShift ℤ := inferInstance
    let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
    let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
    have : G.IsTriangulated := adj.isTriangulated_rightAdjoint
    have : Functor.Linear A G := localCohomologyFunctor_linear A I hI
    let RF := G ⋙ P.ι
    let H0 := DerivedCategory.homologyFunctor C 0
    let Hm := DerivedCategory.homologyFunctor C (-1)
    have : Functor.Linear A H0 := inferInstance
    have : Functor.Linear A Hm := inferInstance
    -- `K` is bounded: above by the injective amplitude, below by `-d`.
    obtain ⟨a, b, Jc, hJge, hJle, hJinj, eJn⟩ := hK.1.finiteInjectiveDimension
    let eJ : K ≅ DerivedCategory.Q.obj Jc := Classical.choice eJn
    have : Jc.IsStrictlyLE b := hJle
    have hKle : K.IsLE b := by
      rw [DerivedCategory.isLE_iff]
      intro j hj
      exact ((DerivedCategory.homologyFunctor C j).mapIso eJ).isZero_iff.mpr
        (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj Jc) b j hj)
    let lo : ℤ := -(d : ℤ) + 1
    have hlodef : lo = -(d : ℤ) + 1 := rfl
    let c : ℤ := max b lo
    have hleC : lo ≤ c := le_max_right b lo
    let n : ℕ := (c - lo).toNat
    have hn : lo + (n : ℤ) = c := by dsimp only [n]; omega
    obtain ⟨f, hfavoid, hfann⟩ :=
      exists_avoidsTopMinimalPrimes_mem_annihilator_homology A d K hK c
    have : K.IsGE (-(d : ℤ)) :=
      isGE_neg_dimension_of_isNormalizedDualizingComplex A K hK d hd
    have : K.IsLE b := hKle
    let U := (DerivedCategory.TStructure.t.truncGE lo).obj K
    have : U.IsGE lo := by
      rw [show U = (DerivedCategory.TStructure.t.truncGE lo).obj K from rfl]
      infer_instance
    have : U.IsLE c := by
      rw [DerivedCategory.isLE_iff]
      intro j hj
      exact DerivedCategory.isZero_of_isLE U b j (lt_of_le_of_lt (le_max_left b lo) hj)
    have : U.IsLE (lo + n) := by rw [hn]; infer_instance
    let T := (DerivedCategory.TStructure.t.triangleLEGE (-(d : ℤ)) lo rfl).obj K
    have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished (-(d : ℤ)) lo rfl K
    have hobj₁ : T.obj₁ = (DerivedCategory.TStructure.t.truncLE (-(d : ℤ))).obj K := rfl
    -- `f • 𝟙` is a ghost endomorphism of the truncation `U`, hence nilpotent.
    let fU : End U := .of (f • 𝟙 U)
    have hfU : ∀ i : ℤ, (DerivedCategory.homologyFunctor C i).map fU.asHom = 0 := by
      intro i
      by_cases hlow : i < lo
      · exact (DerivedCategory.isZero_of_isGE U lo i hlow).eq_of_src _ _
      · by_cases hhigh : c < i
        · exact (DerivedCategory.isZero_of_isLE U c i hhigh).eq_of_src _ _
        · have hi : i ∈ Finset.Icc lo c := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          let Hi := DerivedCategory.homologyFunctor C i
          have : Functor.Linear A Hi := inferInstance
          have hKzero : Hi.map (f • 𝟙 T.obj₂) = 0 := by
            rw [Functor.map_smul, Hi.map_id]
            apply ModuleCat.hom_ext
            ext x
            show f • x = 0
            exact Module.mem_annihilator.mp (hfann i hi) x
          have hπ : IsIso (Hi.map T.mor₂) := by
            apply isIso_homology_mor₂ T hT i
            · rw [hobj₁]
              exact DerivedCategory.isZero_of_isLE _ (-(d : ℤ)) i (by omega)
            · rw [hobj₁]
              exact DerivedCategory.isZero_of_isLE _ (-(d : ℤ)) (i + 1) (by omega)
          have hnat : (f • 𝟙 T.obj₂) ≫ T.mor₂ = T.mor₂ ≫ (f • 𝟙 T.obj₃) := by
            simp [Linear.comp_smul, Linear.smul_comp]
          have hcomp : Hi.map T.mor₂ ≫ Hi.map (f • 𝟙 T.obj₃) = 0 := by
            rw [← Functor.map_comp, ← hnat, Functor.map_comp, hKzero, zero_comp]
          show Hi.map (f • 𝟙 T.obj₃) = 0
          apply (cancel_epi (Hi.map T.mor₂)).1
          simpa using hcomp
    have hnil : fU ^ (n + 1) = 0 := ghostEndo_pow_zero lo n U fU hfU
    -- Nilpotency survives `RΓ_{V(I)}` and taking homology, where it reads as a power of `f`.
    let gU : End (RF.obj U) := RF.mapEnd U fU
    have hgU : gU ^ (n + 1) = 0 := by
      show ((RF.mapEnd U) fU) ^ (n + 1) = 0
      rw [map_end_pow RF U fU (n + 1), hnil]
      exact End.ext (RF.map_zero U U)
    let gm : End (Hm.obj (RF.obj U)) := Hm.mapEnd (RF.obj U) gU
    have hgmNil : gm ^ (n + 1) = 0 := by
      show ((Hm.mapEnd (RF.obj U)) gU) ^ (n + 1) = 0
      rw [map_end_pow Hm (RF.obj U) gU (n + 1), hgU]
      exact End.ext (Hm.map_zero _ _)
    have hgmApply : ∀ x : Hm.obj (RF.obj U), gm.asHom.hom x = f • x := by
      intro x
      have hscalar : gm.asHom = f • 𝟙 (Hm.obj (RF.obj U)) := by
        show Hm.map (RF.map (f • 𝟙 U)) = _
        rw [Functor.map_smul, Functor.map_smul]
        simp
      rw [hscalar]
      show (f • 𝟙 (Hm.obj (RF.obj U))).hom x = f • x
      rw [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_apply]
    have hgmPow : ∀ (m : ℕ) (x : Hm.obj (RF.obj U)), (gm ^ m).asHom.hom x = f ^ m • x := by
      intro m
      induction m with
      | zero => intro x; simp
      | succ m ih =>
          intro x
          rw [pow_succ', End.mul_asHom, ModuleCat.hom_comp]
          show gm.asHom.hom ((gm ^ m).asHom.hom x) = _
          rw [hgmApply, ih, smul_smul, ← pow_succ']
    have hkillU : ∀ x : Hm.obj (RF.obj U), f ^ (n + 1) • x = 0 := fun x ↦
      (hgmPow (n + 1) x).symm.trans (congrArg (fun q : End (Hm.obj (RF.obj U)) => q.asHom.hom x) hgmNil)
    -- The connecting map of the truncation triangle transports that to the bottom truncation.
    let TR : Triangle (DerivedCategory C) := RF.mapTriangle.obj T
    have hTR : TR ∈ distinguishedTriangles := RF.map_distinguished T hT
    have hzeroK : IsZero (H0.obj TR.obj₂) := hvan
    have hex := (ShortComplex.moduleCat_exact_iff _).1
      (H0.homologySequence_exact₁ TR hTR (-1) 0 rfl)
    let δ := H0.homologySequenceδ TR (-1) 0 rfl
    have hkillA : ∀ x : H0.obj TR.obj₁, f ^ (n + 1) • x = 0 := by
      intro x
      have hx : (H0.map TR.mor₁).hom x = 0 := by
        rw [hzeroK.eq_of_tgt (H0.map TR.mor₁) 0]
        simp
      obtain ⟨y, hy⟩ := hex x hx
      change δ.hom y = x at hy
      have hy0 : f ^ (n + 1) • y = 0 := hkillU y
      rw [← hy]
      exact (δ.hom.map_smul (f ^ (n + 1)) y).symm.trans (by rw [hy0]; exact map_zero _)
    -- Identify the bottom truncation with `ω_A` placed in degree `-d`.
    have : T.obj₁.IsGE (-(d : ℤ)) := by rw [hobj₁]; infer_instance
    have : T.obj₁.IsLE (-(d : ℤ)) := by rw [hobj₁]; infer_instance
    obtain ⟨N, ⟨eA⟩⟩ := T.obj₁.exists_iso_singleFunctor_obj_of_isGE_of_isLE (-(d : ℤ))
    let Hbot := DerivedCategory.homologyFunctor C (-(d : ℤ))
    have hAtoM : T.obj₁ ≅ (DerivedCategory.singleFunctor C (-(d : ℤ))).obj M := by
      let eH := Hbot.mapIso eA ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C (-(d : ℤ))).app N
      have hiso : IsIso (Hbot.map T.mor₁) := by
        apply isIso_homology_mor₁ T hT (-(d : ℤ))
        · exact DerivedCategory.isZero_of_isGE U lo (-(d : ℤ)) (by omega)
        · exact DerivedCategory.isZero_of_isGE U lo (-(d : ℤ) - 1) (by omega)
      let eMor : Hbot.obj T.obj₁ ≅ Hbot.obj T.obj₂ := @asIso _ _ _ _ _ hiso
      exact eA ≪≫ (DerivedCategory.singleFunctor C (-(d : ℤ))).mapIso (eH.symm ≪≫ eMor)
    let S0 := (DerivedCategory.singleFunctor C 0).obj M
    let eTop : H0.obj (RF.obj T.obj₁) ≅
        (DerivedCategory.homologyFunctor C (d : ℤ)).obj (RF.obj S0) :=
      H0.mapIso (RF.mapIso (hAtoM ≪≫
          (((DerivedCategory.singleFunctors C).shiftIso (d : ℤ) (-(d : ℤ)) 0 (by omega)).app
            M).symm) ≪≫ (RF.commShiftIso (d : ℤ)).app S0) ≪≫
        (H0.shiftIso (d : ℤ) 0 (d : ℤ) (by omega)).app (RF.obj S0)
    show IsZero ((DerivedCategory.homologyFunctor C (d : ℤ)).obj (RF.obj S0))
    have htopKill : ∀ x : (DerivedCategory.homologyFunctor C (d : ℤ)).obj (RF.obj S0),
        f ^ (n + 1) • x = 0 := by
      intro x
      have hx : f ^ (n + 1) • eTop.inv.hom x = 0 := hkillA _
      have hInv : eTop.hom.hom (eTop.inv.hom x) = x := by
        show (eTop.inv ≫ eTop.hom).hom x = x
        rw [eTop.inv_hom_id]
        rfl
      rw [← hInv, ← map_smul eTop.hom.hom, hx, map_zero]
    -- Multiplication by `f` is surjective on the top local cohomology of `ω_A`, so a power of
    -- `f` is too, and that forces the module to vanish.
    have hsurj := surjective_smul_top_localCohomologyModule_of_avoidsTopMinimalPrimes.{u, u}
      A d hd f hfavoid I hI M
    have hpowSurj : ∀ m : ℕ,
        Function.Surjective (fun x : (DerivedCategory.homologyFunctor C (d : ℤ)).obj
          (RF.obj S0) => f ^ m • x) := by
      intro m
      induction m with
      | zero => intro x; exact ⟨x, by simp⟩
      | succ m ih =>
          intro x
          obtain ⟨z, rfl⟩ := hsurj x
          obtain ⟨y, rfl⟩ := ih z
          exact ⟨y, by simp [pow_succ', mul_smul]⟩
    have hzeroX : ∀ z : (DerivedCategory.homologyFunctor C (d : ℤ)).obj (RF.obj S0), z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := hpowSurj (n + 1) z
      exact htopKill w
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun x y => (hzeroX x).trans (hzeroX y).symm⟩
  exact cohomologicalDimension_lt_of_isZero_localCohomologyModule A d hd I M hM htop

end Stacks.LocalCohomology

end
