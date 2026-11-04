module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleChange
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationRefinement
public import StacksFrontier.RingTheory.QuasiFinite.Basic

/-!
# Finite-open factorizations of a composite quasi-finite algebra

To compose relative dualizing modules along `A → B → C` one needs a finite-open factorization
of `C` over the intermediate algebra of a chosen factorization of `B` over `A`. This file
produces one, together with the facts about a single finite-open factorization that make it
possible: the target is of finite type and quasi-finite over the intermediate algebra, so
Zariski's main theorem applies again.

The common mechanism is that the distinguished opens of the target coming from elements of the
intermediate algebra cover it, and on each of them the structure map is an away localization.
Both finite type and quasi-finiteness are local in that sense.

## Main definitions

* `Stacks.Discriminant.dualizingModule.factorizationTargetCover` is the covering family of
  elements of the target.
* `Stacks.Discriminant.dualizingModule.canonicalFactorization` is a finite-open factorization
  depending only on the algebra, not on a given factorization.
* `Stacks.Discriminant.dualizingModule.retargetFactorization` transports a finite-open
  factorization along an isomorphism of its target.
* `Stacks.Discriminant.dualizingModule.restrictBaseFactorization` reads a finite-open
  factorization as one over a smaller base.
* `Stacks.Discriminant.dualizingModule.compositeFiniteOpenFactorization` is a finite-open
  factorization of the composite.
* `Stacks.Discriminant.dualizingModule.tensorEpiLmulEquiv` identifies a scalar extension along
  a ring epimorphism with the algebra itself.

## Main results

* `Stacks.Discriminant.dualizingModule.finiteType_of_finiteOpenFactorization` and
  `Stacks.Discriminant.dualizingModule.quasiFinite_of_finiteOpenFactorization`: the target of a
  finite-open factorization is of finite type and quasi-finite over the intermediate algebra.

## Implementation notes

`canonicalFactorization` is extracted from `quasiFinite_exists_finite_subalgebra` by
`Classical.choose`, so two finite-open factorizations of the same algebra give the same
canonical one definitionally. That is what lets the composition map be defined without
reference to the factorizations it is built from.

## References

* [Stacks Project, Tag 0BT4](https://stacks.math.columbia.edu/tag/0BT4)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

namespace Stacks.Discriminant

namespace dualizingModule

/-- The elements of the target that generate a distinguished open contained in the image
of the spectrum of the intermediate algebra. These cover the target. -/
def factorizationTargetCover {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) : Set B :=
  {b | ∃ g : F.middle,
    (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum F.middle)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) ∧
    algebraMap F.middle B g = b}

/-- The distinguished opens coming from the intermediate algebra cover the spectrum of the
target, i.e. the corresponding elements generate the unit ideal. -/
lemma factorizationTargetCover_span {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Ideal.span (factorizationTargetCover F) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨M, hM, hspan⟩ := Ideal.ne_top_iff_exists_maximal.mp hne
  let q : PrimeSpectrum B := ⟨M, hM.isPrime⟩
  let p := PrimeSpectrum.comap (algebraMap F.middle B) q
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hp, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) from ⟨q, rfl⟩)
      F.isOpenEmbedding_comap.isOpen_range
  have hnot : algebraMap F.middle B g ∉ q.asIdeal := by
    simpa [p, PrimeSpectrum.comap_asIdeal] using hp
  exact hnot (hspan (Ideal.subset_span ⟨g, hg, rfl⟩))

/-- On a distinguished open coming from the intermediate algebra, the target is an away
localization of the intermediate algebra. -/
private lemma nonempty_away_algEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (g : F.middle)
    (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum F.middle)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap F.middle B))) :
    Nonempty (Localization.Away g ≃ₐ[F.middle] Localization.Away (algebraMap F.middle B g)) :=
  ⟨AlgEquiv.ofBijective (Localization.awayMapₐ (Algebra.ofId F.middle B) g)
    (F.awayMap_bijective g hg)⟩

/-- The target of a finite-open factorization is of finite type over the intermediate
algebra. -/
lemma finiteType_of_finiteOpenFactorization {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Algebra.FiniteType F.middle B := by
  classical
  apply Algebra.FiniteType.of_span_eq_top_target (factorizationTargetCover F)
    (factorizationTargetCover_span F)
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨e⟩ := nonempty_away_algEquiv F g hg
  exact Algebra.FiniteType.equiv inferInstance e

/-- An algebra is quasi-finite as soon as it is quasi-finite after inverting each element of a
set generating the unit ideal. -/
lemma quasiFinite_of_span_eq_top {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (s : Set S) (hs : Ideal.span s = ⊤)
    (H : ∀ r ∈ s, Algebra.QuasiFinite R (Localization.Away r)) :
    Algebra.QuasiFinite R S := by
  obtain ⟨t, ht, htspan⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  let s₀ : Set S := t
  rw [Algebra.quasiFinite_iff]
  intro P hP
  have hfin (r : s₀) :
      Module.Finite P.ResidueField (P.Fiber (Localization.Away r.1)) := by
    have hq : Algebra.QuasiFinite R (Localization.Away r.1) := H r.1 (ht r.2)
    infer_instance
  let φ (r : s₀) : P.Fiber S →ₐ[P.ResidueField]
      P.Fiber (Localization.Away r.1) :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let f : P.Fiber S →ₐ[P.ResidueField]
      Π r : s₀, P.Fiber (Localization.Away r.1) := AlgHom.pi φ
  have : Module.Finite P.ResidueField
      (Π r : s₀, P.Fiber (Localization.Away r.1)) := Module.Finite.pi
  have : IsNoetherian P.ResidueField
      (Π r : s₀, P.Fiber (Localization.Away r.1)) :=
    isNoetherian_of_isNoetherianRing_of_finite ..
  suffices Function.Injective f from .of_injective f.toLinearMap this
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply eq_zero_of_localization _ fun J hJ => ?_
  let I := (PrimeSpectrum.primesOverOrderIsoFiber R S P).symm ⟨J, inferInstance⟩
  have hnot : ¬ s₀ ⊆ I.1 := fun h =>
    Ideal.IsPrime.ne_top' (top_le_iff.mp (htspan.symm.trans_le (Ideal.span_le.mpr h)))
  obtain ⟨r, hrs, hrI⟩ := Set.not_subset.mp hnot
  have hrJ : Algebra.TensorProduct.includeRight r ∉ J := by
    simpa [Submonoid.powers_le] using! hrI
  let fS : S →+* Localization.AtPrime J :=
    (algebraMap (P.Fiber S) (Localization.AtPrime J)).comp
      Algebra.TensorProduct.includeRight.toRingHom
  let : Algebra S (Localization.AtPrime J) := fS.toAlgebra
  let : IsScalarTower R S (Localization.AtPrime J) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      rw [IsScalarTower.algebraMap_apply R (P.Fiber S) (Localization.AtPrime J)]
      show (algebraMap (P.Fiber S) (Localization.AtPrime J))
          (algebraMap R (P.Fiber S) x) =
        (algebraMap (P.Fiber S) (Localization.AtPrime J))
          (Algebra.TensorProduct.includeRight (algebraMap R S x))
      rw [Algebra.TensorProduct.algebraMap_apply']
      rfl)
  have hunit : IsUnit ((IsScalarTower.toAlgHom R S (Localization.AtPrime J)) r) := by
    show IsUnit (algebraMap (P.Fiber S) (Localization.AtPrime J)
      (Algebra.TensorProduct.includeRight r))
    exact IsLocalization.map_units (M := J.primeCompl) (Localization.AtPrime J)
      ⟨Algebra.TensorProduct.includeRight r, hrJ⟩
  let g : Localization.Away r →ₐ[R] Localization.AtPrime J :=
    IsLocalization.Away.liftAlgHom r (f := IsScalarTower.toAlgHom R S
      (Localization.AtPrime J)) hunit
  let ψ : P.Fiber (Localization.Away r) →ₐ[P.ResidueField] Localization.AtPrime J :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) g (fun _ _ => .all _ _)
  have hgcomp : g.comp (IsScalarTower.toAlgHom R S (Localization.Away r)) =
      IsScalarTower.toAlgHom R S (Localization.AtPrime J) := by
    ext b
    simp [g, IsLocalization.Away.liftAlgHom]
  have hψ : ψ.comp (φ ⟨r, hrs⟩) = IsScalarTower.toAlgHom _ _ _ := by
    ext a
    calc
      ((ψ.comp (φ ⟨r, hrs⟩)).restrictScalars R).comp
          Algebra.TensorProduct.includeRight a =
        g (algebraMap S (Localization.Away r) a) := by
          simp [φ, ψ]
      _ = (IsScalarTower.toAlgHom R S (Localization.AtPrime J)) a :=
        congrArg (fun k : S →ₐ[R] Localization.AtPrime J => k a) hgcomp
      _ = ((IsScalarTower.toAlgHom P.ResidueField (P.Fiber S)
          (Localization.AtPrime J)).restrictScalars R).comp
          Algebra.TensorProduct.includeRight a := by
        show fS a = _
        rfl
  exact (congrArg (fun g => g a) hψ).symm.trans
    (show ψ (f a ⟨r, hrs⟩) = 0 by simp only [ha, Pi.zero_apply, map_zero])

/-- The target of a finite-open factorization is quasi-finite over the intermediate
algebra. -/
lemma quasiFinite_of_finiteOpenFactorization {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Algebra.QuasiFinite F.middle B := by
  classical
  apply quasiFinite_of_span_eq_top (factorizationTargetCover F)
    (factorizationTargetCover_span F)
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨e⟩ := nonempty_away_algEquiv F g hg
  exact (Algebra.QuasiFinite.iff_of_algEquiv e).mp
    (Algebra.QuasiFinite.of_isLocalization (Submonoid.powers g))

/-- A finite-open factorization of a quasi-finite algebra whose intermediate algebra is a
subalgebra of the target, chosen once and for all. Any finite-open factorization gives rise to
the same one, which is what makes it usable as a reference choice. -/
noncomputable def canonicalFactorization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    FiniteOpenFactorization.{u, v, v} A B := by
  have : Algebra.FiniteType F.middle B := finiteType_of_finiteOpenFactorization F
  have : Algebra.FiniteType A B := Algebra.FiniteType.trans (R := A) (S := F.middle) (A := B)
    inferInstance inferInstance
  have : Algebra.QuasiFinite F.middle B := quasiFinite_of_finiteOpenFactorization F
  have : Algebra.QuasiFinite A B := Algebra.QuasiFinite.trans A F.middle B
  let h := quasiFinite_exists_finite_subalgebra (R := A) (S := B)
  let K := Classical.choose h
  have hK := Classical.choose_spec h
  exact {
    middle := K
    commRingMiddle := inferInstance
    algebraMiddle := inferInstance
    algebraTarget := K.val.toRingHom.toAlgebra
    scalarTower := IsScalarTower.of_algebraMap_eq' rfl
    finite_middle := hK.2.1
    isOpenEmbedding_comap := hK.2.2.1
    awayMap_bijective := hK.2.2.2 }

/-- Transporting a finite-open factorization along an algebra isomorphism of its target, as a
reducible abbreviation: the intermediate algebra is unchanged, and the constructions on relative
dualizing modules below need that to be visible to unification. -/
abbrev retargetFactorization
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : FiniteOpenFactorization.{u, v, x} A B) (e : B ≃ₐ[A] C) :
    FiniteOpenFactorization.{u, w, x} A C := by
  letI : Algebra F.middle C := (e.toRingHom.comp (algebraMap F.middle B)).toAlgebra
  have ht : IsScalarTower A F.middle C := IsScalarTower.of_algebraMap_eq' (by
    ext a
    simp only [RingHom.comp_apply, RingHom.algebraMap_toAlgebra,
      ← IsScalarTower.algebraMap_apply A F.middle B]
    exact (e.commutes a).symm)
  have he : Function.Surjective (PrimeSpectrum.comap e.toRingHom) :=
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm.surjective
  have hc : PrimeSpectrum.comap (algebraMap F.middle C) =
      (PrimeSpectrum.comap (algebraMap F.middle B)) ∘
        (PrimeSpectrum.comap e.toRingHom) := by
    ext p r
    rfl
  have hr : Set.range (PrimeSpectrum.comap (algebraMap F.middle C)) =
      Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) := by
    rw [hc, Set.range_comp, he.range_eq, Set.image_univ]
  refine {
    middle := F.middle
    commRingMiddle := inferInstance
    algebraMiddle := inferInstance
    algebraTarget := inferInstance
    scalarTower := ht
    finite_middle := inferInstance
    isOpenEmbedding_comap := ?_
    awayMap_bijective := ?_ }
  · rw [hc]
    exact F.isOpenEmbedding_comap.comp
      (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm.isOpenEmbedding
  · intro g hg
    rw [hr] at hg
    have hb := F.awayMap_bijective g hg
    constructor
    · rw [Localization.awayMap_injective_iff]
      intro a ha
      exact (Localization.awayMap_injective_iff.mp hb.1) a (e.injective (ha.trans e.map_zero.symm))
    · rw [Localization.awayMap_surjective_iff]
      intro c
      obtain ⟨b, n, hn⟩ := (Localization.awayMap_surjective_iff.mp hb.2) (e.symm c)
      refine ⟨b, n, ?_⟩
      change e (algebraMap F.middle B b) = e (algebraMap F.middle B g) ^ n * c
      simpa only [map_mul, map_pow, e.apply_symm_apply] using congrArg e hn

/-- The algebra structure on the intermediate algebra of a finite-open factorization, read over
a smaller base. -/
abbrev restrictBaseAlgebra
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C] [Algebra A R] [Algebra R C]
    (K : FiniteOpenFactorization.{v, w, x} R C) : Algebra A K.middle :=
  ((algebraMap R K.middle).comp (algebraMap A R)).toAlgebra

/-- The intermediate algebra of a finite-open factorization, read over a smaller base, is still
an algebra under the original base. -/
lemma restrictBase_isScalarTower_middle
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C] [Algebra A R] [Algebra R C]
    (K : FiniteOpenFactorization.{v, w, x} R C) :
    letI := restrictBaseAlgebra (A := A) K
    IsScalarTower A R K.middle :=
  let := restrictBaseAlgebra (A := A) K
  IsScalarTower.of_algebraMap_eq' rfl

/-- Reading the intermediate algebra over a smaller base is compatible with the map to the
target. -/
lemma restrictBase_isScalarTower_target
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C]
    [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
    (K : FiniteOpenFactorization.{v, w, x} R C) :
    letI := restrictBaseAlgebra (A := A) K
    IsScalarTower A K.middle C := by
  let := restrictBaseAlgebra (A := A) K
  let := restrictBase_isScalarTower_middle (A := A) K
  exact IsScalarTower.of_algebraMap_eq' (by
    ext a
    simp only [RingHom.comp_apply, IsScalarTower.algebraMap_apply A R C,
      IsScalarTower.algebraMap_apply A R K.middle,
      ← IsScalarTower.algebraMap_apply R K.middle C])

/-- The intermediate algebra of a finite-open factorization over a ring that is finite over a
smaller base is finite over that smaller base. -/
lemma restrictBase_finite
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C] [Algebra A R] [Algebra R C]
    [Module.Finite A R]
    (K : FiniteOpenFactorization.{v, w, x} R C) :
    letI := restrictBaseAlgebra (A := A) K
    Module.Finite A K.middle := by
  let := restrictBaseAlgebra (A := A) K
  let := restrictBase_isScalarTower_middle (A := A) K
  exact Module.Finite.trans R K.middle

/-- A finite-open factorization over a ring that is finite over a smaller base is also one
over that smaller base, with the same intermediate algebra. -/
abbrev restrictBaseFactorization
    {A : Type u} {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C]
    [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
    [Module.Finite A R]
    (K : FiniteOpenFactorization.{v, w, x} R C) :
    FiniteOpenFactorization.{u, w, x} A C where
  middle := K.middle
  commRingMiddle := K.commRingMiddle
  algebraMiddle := restrictBaseAlgebra (A := A) K
  algebraTarget := K.algebraTarget
  scalarTower := restrictBase_isScalarTower_target (A := A) K
  finite_middle := restrictBase_finite (A := A) K
  isOpenEmbedding_comap := K.isOpenEmbedding_comap
  awayMap_bijective := K.awayMap_bijective

/-- A finite-open factorization of the composite of two quasi-finite algebras, over the
intermediate algebra of the first factorization. -/
noncomputable def compositeFiniteOpenFactorization
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{v, w, y} B C)
    [Algebra F.middle C] [IsScalarTower F.middle B C] :
    FiniteOpenFactorization.{x, w, w} F.middle C := by
  classical
  haveI : Algebra.FiniteType F.middle B := finiteType_of_finiteOpenFactorization F
  letI : Algebra G.middle C := G.algebraTarget
  letI : IsScalarTower B G.middle C := G.scalarTower
  haveI : Algebra.FiniteType G.middle C := finiteType_of_finiteOpenFactorization G
  haveI : Algebra.FiniteType B C :=
    Algebra.FiniteType.trans (R := B) (S := G.middle) (A := C) inferInstance inferInstance
  haveI : Algebra.FiniteType F.middle C :=
    Algebra.FiniteType.trans (R := F.middle) (S := B) (A := C) inferInstance inferInstance
  haveI : Algebra.QuasiFinite F.middle B := quasiFinite_of_finiteOpenFactorization F
  haveI : Algebra.QuasiFinite G.middle C := quasiFinite_of_finiteOpenFactorization G
  haveI : Algebra.QuasiFinite B C :=
    Algebra.QuasiFinite.trans (R := B) (S := G.middle) (T := C)
  haveI : Algebra.QuasiFinite F.middle C :=
    Algebra.QuasiFinite.trans (R := F.middle) (S := B) (T := C)
  let hmodel := quasiFinite_exists_finite_subalgebra (R := F.middle) (S := C)
  let K := Classical.choose hmodel
  have hK := Classical.choose_spec hmodel
  refine ⟨↥K, inferInstance, inferInstance, K.val.toRingHom.toAlgebra,
    IsScalarTower.of_algebraMap_eq' rfl, hK.2.1, hK.2.2.1, hK.2.2.2⟩

/-- Scalar extension along a ring epimorphism `R → B` does nothing: for any `R`-algebra `C`
under `B`, the algebra `B ⊗[R] C` is `C`. -/
noncomputable def tensorEpiLmulEquiv
    {R : Type u} {B : Type v} {C : Type w}
    [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
    (hepi : Algebra.IsEpi R B) : B ⊗[R] C ≃ₐ[B] C := by
  letI : Algebra.IsEpi R B := hepi
  letI : Algebra B (B ⊗[R] C) := Algebra.TensorProduct.leftAlgebra
  let f₀ : B ⊗[R] C →ₐ[R] C :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R B C) (AlgHom.id R C)
      (fun _ _ => Commute.all _ _)
  let f : B ⊗[R] C →ₐ[B] C := {
    toRingHom := f₀.toRingHom
    commutes' := by
      intro b
      change f₀ ((Algebra.TensorProduct.includeLeft :
        B →ₐ[B] B ⊗[R] C) b) = algebraMap B C b
      simp [f₀]
  }
  have hfun (x : B ⊗[R] C) : f x = TensorProduct.lid' R B C x := by
    induction x using TensorProduct.induction_on with
    | zero => simp [f]
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul b c => simp [f, f₀, TensorProduct.lid'_apply_tmul, Algebra.smul_def]
  exact AlgEquiv.ofBijective f ⟨fun x y hxy => (TensorProduct.lid' R B C).injective
    ((hfun x).symm.trans (hxy.trans (hfun y))), fun c => ⟨1 ⊗ₜ[R] c, by simp [f, f₀]⟩⟩

/-- The identification `B ⊗[R] C ≃ₐ[B] C` along a ring epimorphism multiplies out a pure
tensor. -/
lemma tensorEpiLmulEquiv_tmul
    {R : Type u} {B : Type v} {C : Type w}
    [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
    (hepi : Algebra.IsEpi R B) (b : B) (c : C) :
    tensorEpiLmulEquiv hepi (b ⊗ₜ[R] c) = algebraMap B C b * c := by
  simp [tensorEpiLmulEquiv]

end dualizingModule

end Stacks.Discriminant
