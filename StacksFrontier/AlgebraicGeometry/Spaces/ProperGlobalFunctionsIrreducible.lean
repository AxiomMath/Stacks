module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsDescent
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Criteria
public import StacksFrontier.RingTheory.GeometricallyIrreducible.SeparableClosure
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Geometric irreducibility of the global functions of a proper algebraic space over a field

Let `k` be a field and let `X` be a proper algebraic space over `k` with
`A = H⁰(X, 𝒪_X) = AlgebraicGeometry.Space.globalFunctions`.  This file proves the content of
parts (5) and (6) of Tag 0DMY:  if `X` is geometrically connected then `A` is geometrically
irreducible over `k`, granted that `A` is finite dimensional.  The statements with finiteness
obtained from properness are in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalFunctionsGeometric`.

## Main results

* `Stacks.ArtinianLocalBaseChange.irreducibleSpace_primeSpectrum_tensorProduct`: the
  commutative-algebra heart.  For a local `k`-algebra `R` with a one-point spectrum, finite over
  `k`, whose base change to an algebraic closure of `k` has connected spectrum,
  `Spec (R ⊗_k K)` is irreducible for *every* field extension `K/k`, in every universe.
* `AlgebraicGeometry.Space.irreducibleSpace_primeSpectrum_globalFunctions_tensorProduct_of_finite`:
  for a proper geometrically connected `X` with finite dimensional global functions, the
  spectrum of `A ⊗_k K` is irreducible for every field extension `K/k`.

## Implementation notes

**How geometric irreducibility of `A` is spelled.**  `Algebra.IsGeometricallyIrreducible` puts
the field and the algebra in one universe, since it passes through `Spec`.  Here `k` is in
`Type u` — the universe of the site — while `A` is a ring of sections and lives in
`Type (u + 1)`, so that predicate cannot be applied to the pair `(k, A)`.  The conclusion is
therefore written in the form the source's definition (Tag 037L) takes, as irreducibility of
`Spec (A ⊗_k K)` for every field extension `K/k`;  and `K` is left in an arbitrary universe `v`,
so that nothing is quantified away.  Taking `v := u + 1` gives the statement over the extensions
of the universe `A` itself lives in.

**The argument, and why the one-field criterion is not enough.**  Separable descent
(`AlgebraicGeometry.Space.connectedSpace_primeSpectrum_tensorProduct_of_isGeometricallyConnected`)
gives connectedness of `Spec (A' ⊗_k k')` only for those `k'` whose spectrum lies in the chosen
big fppf site, `A'` being a model of `A` in the universe of the site;  that is all geometric
connectedness of `X` quantifies over.  Tag 037K
(`AlgebraicGeometry.geometricallyIrreducible_tfae`) decides geometric irreducibility from the
single extension `k̄/k`, but it is stated for a field and an algebra in one universe, so applying
it to `A` would quantify only over the extensions in the universe *below* `A`;  that would be a
weaker statement than the source's.  What is used instead is that `A` is an Artinian local ring,
by finiteness and part (2) at the single connected component of `|X|`:

1. the maximal ideal of `A` consists of nilpotents, so `Spec (A ⊗_k K)` and
   `Spec (κ ⊗_k K)` are homeomorphic for `κ` the residue field of `A` and any `K` — the kernel
   of `A ⊗_k K ⟶ κ ⊗_k K` is the extension of a nil ideal, hence lies in the nilradical;
2. `κ` is a field finite over `k` and lies in the universe of the site, so Tag 037K applies to
   it:  from irreducibility of `Spec (κ ⊗_k k̄)`, which descent gives, Tag 0G33
   (`separableClosure.eq_bot_iff_geometricallyIrreducible`) makes the separable closure of `k`
   in `κ` trivial, i.e. `κ/k` purely inseparable;
3. base change along a purely inseparable extension is a universal homeomorphism, and the
   statement of that in the library,
   `irreducibleSpace_baseChange_purelyInseparable`, is universe-polymorphic:  it gives
   irreducibility of `Spec (K ⊗_k κ)` for an arbitrary field extension `K/k`;
4. step 1 carries that back to `Spec (A ⊗_k K)`.

Geometric connectedness is load-bearing and is used in step 2 at `k' = k̄`:  connectedness of
`|X|` alone would not do, as `A = ℚ(i)` over `k = ℚ` shows — a field, hence local, whose base
change `ℚ(i) ⊗_ℚ ℚ̄ = ℚ̄ × ℚ̄` is disconnected.

## References

* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 037K](https://stacks.math.columbia.edu/tag/037K)
* [Stacks Project, Tag 037L](https://stacks.math.columbia.edu/tag/037L)
* [Stacks Project, Tag 0G33](https://stacks.math.columbia.edu/tag/0G33)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped TensorProduct

universe u v w

namespace Stacks.ArtinianLocalBaseChange

/-- **The maximal ideal of a local ring with a one-point spectrum consists of nilpotents, and so
does its extension to any base change.**  The maximal ideal is then the only prime, hence the
nilradical, and the image of a nilpotent element is nilpotent. -/
theorem map_maximalIdeal_le_nilradical (k : Type u) [Field k] (R : Type v) [CommRing R]
    [Algebra k R] [IsLocalRing R] [Subsingleton (PrimeSpectrum R)] (T : Type w) [CommRing T]
    [Algebra k T] :
    (IsLocalRing.maximalIdeal R).map (algebraMap R (R ⊗[k] T)) ≤ nilradical (R ⊗[k] T) := by
  have hm : IsLocalRing.maximalIdeal R ≤ nilradical R := by
    rw [nilradical_eq_sInf]
    refine le_sInf fun J hJ => ?_
    have h : (⟨IsLocalRing.maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩ :
        PrimeSpectrum R) = ⟨J, hJ⟩ := Subsingleton.elim _ _
    exact le_of_eq (congrArg PrimeSpectrum.asIdeal h)
  rw [Ideal.map_le_iff_le_comap]
  exact fun x hx => (mem_nilradical.mp (hm hx)).map (algebraMap R (R ⊗[k] T))

/-- **The spectra of `R ⊗_k T` and of `κ ⊗_k T` are homeomorphic**, for `R` a local ring with a
one-point spectrum, `κ` its residue field and `T` any `k`-algebra:  `κ ⊗_k T` is the quotient of
`R ⊗_k T` by the extension of the maximal ideal, which consists of nilpotents, and a quotient by
an ideal of nilpotents does not change the spectrum. -/
@[sga "3 VIA 0.4" "special case"]
def primeSpectrumResidueFieldTensorHomeomorph (k : Type u) [Field k] (R : Type v) [CommRing R]
    [Algebra k R] [IsLocalRing R] [Subsingleton (PrimeSpectrum R)] (T : Type w) [CommRing T]
    [Algebra k T] :
    PrimeSpectrum (IsLocalRing.ResidueField R ⊗[k] T) ≃ₜ PrimeSpectrum (R ⊗[k] T) :=
  have e : IsLocalRing.ResidueField R ⊗[k] T ≃ₐ[k]
      (R ⊗[k] T) ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R (R ⊗[k] T)) :=
    Algebra.TensorProduct.quotientTensorEquiv k T R _
  (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).trans
    ((PrimeSpectrum.isHomeomorph_comap (Ideal.Quotient.mk _)
      (fun x => ⟨1, one_pos, by simpa using Ideal.Quotient.mk_surjective x⟩)
      (by rw [Ideal.mk_ker]; exact map_maximalIdeal_le_nilradical k R T)).homeomorph _)

/-- Swapping the factors of a tensor product induces a homeomorphism of the spectra. -/
private def primeSpectrumTensorCommHomeomorph (k : Type u) [Field k] (A : Type v) (B : Type w)
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] :
    PrimeSpectrum (A ⊗[k] B) ≃ₜ PrimeSpectrum (B ⊗[k] A) :=
  PrimeSpectrum.homeomorphOfRingEquiv (Algebra.TensorProduct.comm k A B).toRingEquiv

/-- **Geometric irreducibility from the single extension `k̄/k`, at an arbitrary universe.**  Let
`R` be a local `k`-algebra with a one-point spectrum, finite over the field `k`, and suppose the
spectrum of `R ⊗_k k̄` is connected for an algebraic closure `k̄` of `k`.  Then the spectrum of
`R ⊗_k K` is irreducible for *every* field extension `K/k`, in any universe.

The residue field `κ` of `R` has the same spectrum after any base change
(`Stacks.ArtinianLocalBaseChange.primeSpectrumResidueFieldTensorHomeomorph`), so `Spec (κ ⊗_k k̄)`
is irreducible — connected by hypothesis, and a connected spectrum of an algebra integral over a
field is a single point.  Tag 037K and Tag 0G33 then make `κ/k` purely inseparable, and base
change along a purely inseparable extension is a universal homeomorphism, which is the one step
of the argument that is universe-polymorphic. -/
theorem irreducibleSpace_primeSpectrum_tensorProduct (k : Type u) [Field k] (R : Type u)
    [CommRing R] [Algebra k R] (hfin : Module.Finite k R) (hloc : IsLocalRing R)
    (hsub : Subsingleton (PrimeSpectrum R))
    (hconn : ConnectedSpace (PrimeSpectrum (R ⊗[k] AlgebraicClosure k))) (K : Type v) [Field K]
    [Algebra k K] :
    IrreducibleSpace (PrimeSpectrum (R ⊗[k] K)) := by
  have := hfin
  have := hloc
  have := hsub
  have hpi : IsPurelyInseparable k (IsLocalRing.ResidueField R) := by
    refine (separableClosure.eq_bot_iff (F := k) (E := IsLocalRing.ResidueField R)).1
      ((separableClosure.eq_bot_iff_geometricallyIrreducible k _).2
        (((AlgebraicGeometry.geometricallyIrreducible_tfae k (IsLocalRing.ResidueField R)
          (SeparableClosure k) (AlgebraicClosure k)).out 4 5).mp ?_))
    have : ConnectedSpace (PrimeSpectrum (AlgebraicClosure k ⊗[k] R)) :=
      (primeSpectrumTensorCommHomeomorph k (AlgebraicClosure k) R).connectedSpace_iff.mpr hconn
    exact (primeSpectrumResidueFieldTensorHomeomorph k R
      (AlgebraicClosure k)).irreducibleSpace_iff.mpr
        ((primeSpectrumTensorCommHomeomorph k (AlgebraicClosure k) R).irreducibleSpace_iff.mp
          (AlgebraicGeometry.ProperSectionsGeom.irreducibleSpace_primeSpectrum_of_isIntegral
            (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] R)))
  have hFK : IrreducibleSpace (PrimeSpectrum (IsLocalRing.ResidueField R ⊗[k] K)) :=
    (primeSpectrumTensorCommHomeomorph k K _).irreducibleSpace_iff.mp
      (irreducibleSpace_baseChange_purelyInseparable k K _)
  exact (primeSpectrumResidueFieldTensorHomeomorph k R K).irreducibleSpace_iff.mp hFK

end Stacks.ArtinianLocalBaseChange

namespace AlgebraicGeometry.Space

section Tag0DMY

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
    (X : (BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hS X)
    (f : X ⟶ yoneda.obj (baseObject k B hS))

include hX

/-- **The global functions of a proper geometrically connected algebraic space with finite
dimensional global functions are geometrically irreducible:**  the spectrum of `A ⊗_k K` is
irreducible for every field extension `K/k`, in every universe.

`|X|` is connected by
`AlgebraicGeometry.Space.connectedSpace_points_of_isGeometricallyConnected`, so a componentwise
factorization of the global functions has a single factor and identifies `A` with it;  that
factor is Artinian and local, so `Spec A` is a single point.  Transporting `A` to a `k`-algebra
`A'` in the universe of the site — possible because it is finite over `k` — the descent step
`AlgebraicGeometry.Space.connectedSpace_primeSpectrum_tensorProduct_of_isGeometricallyConnected`
applied to an algebraic closure of `k` makes `Spec (A' ⊗_k k̄)` connected, and
`Stacks.ArtinianLocalBaseChange.irreducibleSpace_primeSpectrum_tensorProduct` turns that single
extension into irreducibility of `Spec (A' ⊗_k K)` for every `K`. -/
theorem irreducibleSpace_primeSpectrum_globalFunctions_tensorProduct_of_finite
    (hf : IsProper B (Spec (.of k)) hS f)
    (hfin : Module.Finite k (globalFunctions B (Spec (.of k)) hS X))
    (hconn : IsGeometricallyConnected B k hS X) :
    ∀ (K : Type v) [Field K] [Algebra k K],
      IrreducibleSpace
        (PrimeSpectrum (globalFunctions B (Spec (.of k)) hS X ⊗[k] K)) := by
  classical
  intro K _ _
  obtain ⟨fac⟩ := nonempty_componentwiseArtinianFactorization_of_isProper_of_field k B hS X hX f hf
  have hXconn : ConnectedSpace (points B (Spec (.of k)) hS X) :=
    connectedSpace_points_of_isGeometricallyConnected k B hS X hconn
  let _ : Unique (ConnectedComponents (points B (Spec (.of k)) hS X)) :=
    uniqueOfSubsingleton (Classical.arbitrary _)
  let (c : ConnectedComponents (points B (Spec (.of k)) hS X)) :
      Algebra k (componentFunctions B (Spec (.of k)) hS X c) := fac.factorAlgebra c
  let e₀ : globalFunctions B (Spec (.of k)) hS X ≃ₐ[k]
      componentFunctions B (Spec (.of k)) hS X default :=
    fac.equivalence.trans (AlgEquiv.ofRingEquiv
      (f := RingEquiv.piUnique fun c => componentFunctions B (Spec (.of k)) hS X c)
      (fun _ => rfl))
  have _ := fac.isArtinian default
  have _ := fac.isLocal default
  have hsub₀ : Subsingleton (PrimeSpectrum (componentFunctions B (Spec (.of k)) hS X default)) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum _
  have : Small.{u} (globalFunctions B (Spec (.of k)) hS X) :=
    Module.Finite.small (R := k) (M := globalFunctions B (Spec (.of k)) hS X)
  let eA : Shrink.{u} (globalFunctions B (Spec (.of k)) hS X) ≃ₐ[k]
      globalFunctions B (Spec (.of k)) hS X :=
    Shrink.algEquiv k (globalFunctions B (Spec (.of k)) hS X)
  have hfinS := Module.Finite.equiv (R := k) eA.symm.toLinearEquiv
  let e' : componentFunctions B (Spec (.of k)) hS X default ≃ₐ[k]
      Shrink.{u} (globalFunctions B (Spec (.of k)) hS X) := e₀.symm.trans eA.symm
  have hntS := e'.injective.nontrivial
  have hlocS := IsLocalRing.of_surjective' e'.toRingEquiv.toRingHom e'.surjective
  have hsubS := (PrimeSpectrum.homeomorphOfRingEquiv e'.toRingEquiv).toEquiv.symm.subsingleton
  have hA' : B.Contains (Spec (.of (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)))) :=
    @Scheme.size_Spec_lt_of_finiteType _ B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k
      (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)) _ _ _
      (@Module.Finite.finiteType k (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)) _ _ _
        hfinS) hS
  have hconnbar := connectedSpace_primeSpectrum_tensorProduct_of_isGeometricallyConnected k B hS
    X hX (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)) hA' hconn eA.symm
    (AlgebraicClosure k) (contains_specAlgebraicClosure B k hS)
  exact (PrimeSpectrum.homeomorphOfRingEquiv (Algebra.TensorProduct.congr eA
    (AlgEquiv.refl : K ≃ₐ[k] K)).toRingEquiv).irreducibleSpace_iff.mp
      (Stacks.ArtinianLocalBaseChange.irreducibleSpace_primeSpectrum_tensorProduct k
        (Shrink.{u} (globalFunctions B (Spec (.of k)) hS X)) hfinS hlocS hsubS hconnbar K)

end Tag0DMY

end AlgebraicGeometry.Space

end
