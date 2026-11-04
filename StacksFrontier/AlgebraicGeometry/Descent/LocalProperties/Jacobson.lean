module

public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Criterion
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.RingTheory.Ideal.GoingDown.Criteria
public import StacksFrontier.RingTheory.Jacobson.Constructions
public import StacksFrontier.Topology.Jacobson.OpenCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Being Jacobson is local in the fppf topology

A scheme is Jacobson if and only if the members of an fppf covering family are Jacobson.

## Main results

* `AlgebraicGeometry.isJacobsonRing_of_faithfullyFlat_quasiFinite` descends the Jacobson
  property of rings along a faithfully flat quasi-finite algebra.
* `AlgebraicGeometry.jacobsonSpace_isLocal_fppf` gives fppf locality of the Jacobson
  property.

## Implementation notes

Being Jacobson is `JacobsonSpace` on the underlying topological space of the scheme.
Ascent is the Jacobson property of the source of a morphism of locally finite type.
Descent factors a faithfully flat algebra of finite presentation through a quasi-finite
faithfully flat one; on the quasi-finite part the fibres of the map of spectra are finite,
while the characterization of Stacks Tag 034J makes a non-Jacobson base produce an infinite
fibre.

## References

* [Stacks Project, Tag 0368](https://stacks.math.columbia.edu/tag/0368)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0368.** The Jacobson property of rings descends along a
faithfully flat quasi-finite algebra. -/
theorem isJacobsonRing_of_faithfullyFlat_quasiFinite {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] [Algebra.QuasiFinite A B]
    (hB : IsJacobsonRing B) : IsJacobsonRing A := by
  classical
  by_contra hA
  obtain ⟨p, f, hp, hf, hsingleton, -⟩ :=
    exists_prime_vCapD_singleton_isField_of_not_isJacobsonRing hA
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  have : p.asIdeal.IsPrime := p.isPrime
  have : m.IsPrime := hm.isPrime
  obtain ⟨m', hm'⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) ⟨m, hm.isPrime⟩
  have hm'ideal : Ideal.comap (algebraMap A B) m'.asIdeal = m :=
    congrArg PrimeSpectrum.asIdeal hm'
  have : m'.asIdeal.LiesOver m := ⟨hm'ideal.symm⟩
  obtain ⟨q, hqm, hqprime, hqover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p.asIdeal) m'.asIdeal hpm
  have hqcontract : Ideal.comap (algebraMap A B) q = p.asIdeal := hqover.over.symm
  let q' : PrimeSpectrum B := ⟨q, hqprime⟩
  have hqnotmax : ¬ q'.asIdeal.IsMaximal := by
    intro hqmax
    have hqeq : q = m'.asIdeal := hqmax.eq_of_le m'.isPrime.ne_top hqm
    have hpeq : p.asIdeal = m := by rw [← hqcontract, hqeq, hm'ideal]
    exact hp (hpeq ▸ hm)
  have hfB : algebraMap A B f ∉ q := by rwa [← hqcontract, Ideal.mem_comap] at hf
  have hsubset : vCapD q' (algebraMap A B f) ⊆
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {p} := by
    intro r hr
    change q ≤ r.asIdeal ∧ algebraMap A B f ∉ r.asIdeal at hr
    have hp_le : p.asIdeal ≤ Ideal.comap (algebraMap A B) r.asIdeal := by
      rw [← hqcontract]
      exact Ideal.comap_mono hr.1
    have hf_not : f ∉ Ideal.comap (algebraMap A B) r.asIdeal := by
      simpa [Ideal.mem_comap] using hr.2
    have hrp : PrimeSpectrum.comap (algebraMap A B) r ∈ vCapD p f := ⟨hp_le, hf_not⟩
    rwa [hsingleton, Set.mem_singleton_iff] at hrp
  exact (Algebra.QuasiFinite.finite_comap_preimage_singleton (R := A) (S := B) p).not_infinite
    ((vCapD_infinite_of_isJacobsonRing hB q' (algebraMap A B f) hqnotmax hfB).mono hsubset)

private instance jacobsonSpace_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun X : Scheme.{u} => JacobsonSpace X) where
  of_iso {X _Y} e hX :=
    have : JacobsonSpace X := hX
    JacobsonSpace.of_isClosedEmbedding (Scheme.homeoOfIso e.symm).isClosedEmbedding

private instance jacobsonSpace_isLocal_zariski :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => JacobsonSpace X)
      Scheme.zariskiPrecoverage :=
  isLocal_zariskiPrecoverage_of_openCover _
    (fun {X} U hX =>
      have : JacobsonSpace X := hX
      JacobsonSpace.of_isOpenEmbedding (X := U.toScheme) U.ι.isOpenEmbedding)
    fun _ hU h => (jacobsonSpace_iff_of_isOpenCover hU).mpr h

/-- The ring of global sections of an affine Jacobson scheme is a Jacobson ring. -/
@[ega "IV 10.4.2" "special case"]
private theorem isJacobsonRing_of_jacobsonSpace {X : Scheme.{u}} [IsAffine X]
    (hX : JacobsonSpace X) : IsJacobsonRing Γ(X, ⊤) :=
  have : JacobsonSpace X := hX
  PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mpr
    (JacobsonSpace.of_isClosedEmbedding X.isoSpec.hom.homeomorph.symm.isClosedEmbedding)

/-- An affine scheme whose ring of global sections is Jacobson is Jacobson. -/
@[ega "IV 10.4.2" "special case"]
private theorem jacobsonSpace_of_isJacobsonRing {X : Scheme.{u}} [IsAffine X]
    (hX : IsJacobsonRing Γ(X, ⊤)) : JacobsonSpace X :=
  have : JacobsonSpace (PrimeSpectrum Γ(X, ⊤)) :=
    PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp hX
  JacobsonSpace.of_isClosedEmbedding X.isoSpec.hom.homeomorph.isClosedEmbedding

/-- **Stacks Project, Tag 0368.** Being Jacobson is local for fppf coverings of schemes. -/
@[stacks 0368]
instance jacobsonSpace_isLocal_fppf :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => JacobsonSpace X)
      Scheme.fppfPrecoverage := by
  refine isLocal_fppfPrecoverage_of_affine (fun X : Scheme.{u} => JacobsonSpace X) ?_ ?_
  · intro X S _ _ f _ hfp hSjac
    have : JacobsonSpace S := hSjac
    have : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
    exact LocallyOfFiniteType.jacobsonSpace f
  · intro X S hX hS f hflat hfp hsurj hXjac
    have : IsAffine X := hX
    have : IsAffine S := hS
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
    have : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
    have : Module.FaithfullyFlat Γ(S, ⊤) Γ(X, ⊤) :=
      RingHom.faithfullyFlat_algebraMap_iff.mp <| by
        simpa [RingHom.algebraMap_toAlgebra] using
          (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨hflat, hsurj⟩
    have : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
      RingHom.finitePresentation_algebraMap.mp
        (by simpa [RingHom.algebraMap_toAlgebra] using f.finitePresentation_appTop)
    obtain ⟨B', _, _, _, _, _, _, _⟩ :=
      Algebra.exists_quasiFinite_faithfullyFlat_finitePresentation
        (R := Γ(S, ⊤)) (S := Γ(X, ⊤))
    have : IsJacobsonRing Γ(X, ⊤) := isJacobsonRing_of_jacobsonSpace hXjac
    have : Algebra.FiniteType Γ(X, ⊤) B' :=
      Algebra.FiniteType.of_restrictScalars_finiteType Γ(S, ⊤) Γ(X, ⊤) B'
    exact jacobsonSpace_of_isJacobsonRing <| isJacobsonRing_of_faithfullyFlat_quasiFinite
      (A := Γ(S, ⊤)) (B := B') (isJacobsonRing_of_finiteType (A := Γ(X, ⊤)))

end AlgebraicGeometry
