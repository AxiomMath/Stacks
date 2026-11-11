module

public import Mathlib.RingTheory.FiniteStability
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.FieldExtensionBaseChange
public import StacksFrontier.RingTheory.Dualizing.GorensteinCriteria
public import StacksFrontier.RingTheory.Dualizing.InvertibleTransport
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizing
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingBaseChangeHomology
import all StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible

/-!
# Gorenstein fibres and invertibility of the relative dualizing complex

Let `φ : R → A` be a flat homomorphism of finite type of Noetherian rings.  The fibres
`A ⊗_R κ(q)` of `φ` are Gorenstein for every prime `q ⊆ R` exactly when the relative dualizing
complex `ω^•_{A/R} = φ^!(R)` is an invertible object of `D(A)`.

## Main results

* `Dualizing.isGorensteinRing_fiber_iff_isInvertible_upperShriekFunctor_unit` —
  **[Stacks, Tag 0E4C]**: the fibres of a flat finite type homomorphism of Noetherian rings are
  Gorenstein if and only if its relative dualizing complex is invertible.
* `Dualizing.nonempty_iso_of_isInvertible_of_homology_iso` — two objects of `D(B)` with
  isomorphic cohomology modules are isomorphic when one of them is invertible.
* `Dualizing.isDualizingComplex_derivedExtensionScalars_upperShriekFunctor_unit_of_field` —
  [Stacks, Tag 0BZW] (2)(b): every base change of `ω^•_{A/R}` to a field is a dualizing complex
  for the fibre ring.

## Implementation notes

Both directions turn on the same identification: the derived base change of `ω^•_{A/R}` along
`R → κ(q)` is the relative dualizing complex of the fibre over `κ(q)`, which is
[Stacks, Tag 0BZV] case (2).  Only a weak form of it is used.  The cohomology modules of the two
sides agree as modules over the fibre ring,
`Dualizing.nonempty_homology_iso_relativeDualizing_baseChange_of_flatAlgebra`, and in each
direction of the equivalence one of the two sides is invertible — the derived base change of
`ω^•_{A/R}` when (2) holds, the relative dualizing complex of a Gorenstein fibre when (1) holds.
An invertible object is perfect with projective cohomology modules ([Stacks, Tag 0FNT]), so both
sides are the direct sums of their shifted cohomology modules ([Stacks, Tag 0GM4]), and are
therefore isomorphic.  That is `Dualizing.nonempty_iso_of_isInvertible_of_homology_iso`.

Upper shriek depends on the presentation and is well defined only up to isomorphism, that
independence being [Stacks, Tag 0BZJ], which this library has unconditionally as
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso`.  The statement is nonetheless
made for an arbitrary polynomial presentation rather than for a canonical `φ^!`, that being the
stronger reading and one that depends on Tag 0BZJ not at all; the fibre is presented by
`Dualizing.PolynomialPresentation.baseChange`, and the derived tensor product `- ⊗_A^L` is the
canonical total left derived extension of scalars.

The fibre of `ω^•_{A/R}` at a maximal ideal `m ⊆ A` is computed by factoring `A → κ(m)` through
the fibre ring `A ⊗_R κ(q)`, where `q` is the prime of `R` under `m`.  No correspondence between
the primes of `A` over `q` and the primes of the fibre ring is needed: `κ(m)` is made an algebra
over `A ⊗_R κ(q)` directly, by the universal property of the base change `AlgHom.liftEquiv`
applied to `A → κ(m)`.

What the source's proof does with [Stacks, Tag 0BYP] is done here in two steps, because
`ω^•_{A/R}` is *not* perfect over `A` without hypothesis (1) — [Stacks, Tag 0BZW] (1)(a) gives
only `Dᵇ_Coh(A)`, that is pseudo-coherence.  Perfectness is obtained from [Stacks, Tag 068W],
`StacksDraft.Perfect.isPerfect_iff_isPerfect_at_primes_of_isBoundedBelow_and_stalkwise_criteria`,
whose fibrewise input is supplied by the very fibre computation the rank argument needs; the rank
argument is then
`DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank`
followed by [Stacks, Tag 0FNT].

## References

* [Stacks Project, Tag 0E4C](https://stacks.math.columbia.edu/tag/0E4C)
* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
* [Stacks Project, Tag 0BZV](https://stacks.math.columbia.edu/tag/0BZV)
* [Stacks Project, Tag 0BZL](https://stacks.math.columbia.edu/tag/0BZL)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
* [Stacks Project, Tag 068W](https://stacks.math.columbia.edu/tag/068W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The relative dualizing complex `ω^•_{A/R} = φ^!(R)` read at a polynomial presentation `p` of
`φ`: the value of algebraic upper shriek at the base ring placed in cohomological degree zero. -/
private abbrev relativeDualizing {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
    (p : PolynomialPresentation f) : DerivedCategory (ModuleCat.{u} A) :=
  p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))

/-- Derived base change along `h : A →+* K` read through an intermediate ring: if `h = g ∘ f` and
the derived base change of `X` along `f` is `Y`, then the derived base change of `X` along `h` is
the derived base change of `Y` along `g`.  This is the composition isomorphism
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp`. -/
private def derivedFibreIso {A B K : Type u} [CommRing A] [CommRing B] [CommRing K]
    (f : A →+* B) (g : B →+* K) (h : A →+* K) (hh : g.comp f = h)
    {X : DerivedCategory (ModuleCat.{u} A)} {Y : DerivedCategory (ModuleCat.{u} B)}
    (e : (totalDerivedExtensionScalars.{u, u, u} f).functor.obj X ≅ Y) :
    (totalDerivedExtensionScalars.{u, u, u} h).functor.obj X ≅
      (totalDerivedExtensionScalars.{u, u, u} g).functor.obj Y := by
  subst hh
  exact ((totalDerivedExtensionScalarsComp f g).app X).symm ≪≫
    (totalDerivedExtensionScalars.{u, u, u} g).functor.mapIso e

/-- The fibre `R' ⊗_R A` of a homomorphism of finite type over a Noetherian ring is Noetherian:
it is of finite type over `R'` because `A` is of finite type over `R`. -/
theorem isNoetherianRing_baseChange {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (R' : Type u) [CommRing R'] [IsNoetherianRing R'] [Algebra R R']
    (p : PolynomialPresentation (algebraMap R A)) :
    IsNoetherianRing (TensorProduct R R' A) :=
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  Algebra.FiniteType.isNoetherianRing R' (TensorProduct R R' A)

/-- **[Stacks, Tag 0BZV] case (2) at the canonical derived tensor product.**  For a flat
homomorphism of finite type of Noetherian rings, the derived base change of `ω^•_{A/R}` along
`R → R'` is `ω^•_{A'/R'}`, where `A' = R' ⊗_R A`. -/
private theorem nonempty_iso_relativeDualizing_baseChange {R A : Type u} [CommRing R]
    [CommRing A] [IsNoetherianRing R] [Algebra R A] (R' : Type u) [CommRing R'] [Algebra R R']
    (p : PolynomialPresentation (algebraMap R A))
    (hflat : (algebraMap R A).Flat) :
    Nonempty ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).functor.obj (relativeDualizing p) ≅
        relativeDualizing (p.baseChange (R' := R'))) :=
  relativeDualizingComplexBaseChange_of_flatAlgebra p hflat _
    (totalDerivedExtensionScalars.{u, u, u} _).comparison
    (totalDerivedExtensionScalars.{u, u, u} _).isLeftDerived

/-- **Two objects of `D(B)` with isomorphic cohomology modules are isomorphic if one of them is
invertible.**  An invertible object is perfect with finite projective cohomology modules
([Stacks, Tag 0FNT]), so both objects are bounded with projective cohomology, and each is the
direct sum of its shifted cohomology modules by [Stacks, Tag 0GM4]. -/
theorem nonempty_iso_of_isInvertible_of_homology_iso {B : Type u} [CommRing B]
    (X Y : DerivedCategory (ModuleCat.{u} B))
    (hY : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
      MonoidalCategory.IsInvertible Y)
    (h : ∀ i : ℤ, Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj X ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj Y)) :
    Nonempty (X ≅ Y) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  obtain ⟨hperf, -, hfp, -⟩ :=
    (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit Y).2 hY
  obtain ⟨P, a, b, _, _, _, _, ⟨e⟩⟩ := hperf
  have : Y.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso e.symm a
  have : Y.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  have : X.IsGE a := (X.isGE_iff a).2 fun i hi =>
    (Y.isZero_of_isGE a i hi).of_iso (h i).some
  have : X.IsLE b := (X.isLE_iff b).2 fun i hi =>
    (Y.isZero_of_isLE b i hi).of_iso (h i).some
  have hpY (i : ℤ) :
      Projective ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj Y) := by
    have := (hfp i).2
    infer_instance
  have hpX (i : ℤ) :
      Projective ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj X) :=
    Projective.of_iso (h i).some.symm (hpY i)
  obtain ⟨jX⟩ :=
    DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero.{u}
      X a b (fun i _ p _ hp x => by
        have := hpX i
        exact x.eq_zero_of_hasProjectiveDimensionLT 1 (by omega))
  obtain ⟨jY⟩ :=
    DerivedCategory.nonempty_iso_biproduct_singleFunctor_obj_homology_of_forall_ext_eq_zero.{u}
      Y a b (fun i _ p _ hp x => by
        have := hpY i
        exact x.eq_zero_of_hasProjectiveDimensionLT 1 (by omega))
  exact ⟨jX ≪≫ biproduct.mapIso (fun i =>
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) i.1).mapIso (h i.1).some) ≪≫ jY.symm⟩

/-- **[Stacks, Tag 0BZV] case (2) when one side is invertible.**  For a flat homomorphism of
finite type of Noetherian rings, the derived base change of `ω^•_{A/R}` along `R → R'` is
`ω^•_{A'/R'}` as soon as one of the two is invertible in `D(A')`: their cohomology modules agree,
which suffices by `Dualizing.nonempty_iso_of_isInvertible_of_homology_iso`. -/
private theorem nonempty_iso_relativeDualizing_baseChange_of_isInvertible {R A : Type u}
    [CommRing R] [CommRing A] [IsNoetherianRing R] [Algebra R A] (R' : Type u) [CommRing R']
    [Algebra R R'] (p : PolynomialPresentation (algebraMap R A))
    (hflat : (algebraMap R A).Flat) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (TensorProduct R R' A)).choose
    (MonoidalCategory.IsInvertible ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).functor.obj (relativeDualizing p)) ∨
      MonoidalCategory.IsInvertible (relativeDualizing (p.baseChange (R' := R')))) →
    Nonempty ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R R' A).toRingHom).functor.obj (relativeDualizing p) ≅
        relativeDualizing (p.baseChange (R' := R'))) := by
  rintro (h | h)
  · exact ⟨(nonempty_iso_of_isInvertible_of_homology_iso _ _ h fun i =>
      ⟨(nonempty_homology_iso_relativeDualizing_baseChange_of_flatAlgebra (R' := R') p hflat
        i).some.symm⟩).some.symm⟩
  · exact nonempty_iso_of_isInvertible_of_homology_iso _ _ h
      (nonempty_homology_iso_relativeDualizing_baseChange_of_flatAlgebra (R' := R') p hflat)

/-- **[Stacks, Tag 0BZL] over a field.**  The relative dualizing complex of the fibre over a field
`R'` is a dualizing complex for the fibre ring: upper shriek carries a dualizing complex to a
dualizing complex, and `R'` placed in degree zero is one for `R'`. -/
private theorem isDualizingComplex_relativeDualizing_baseChange {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] (R' : Type u) [Field R'] [Algebra R R']
    [IsNoetherianRing (TensorProduct R R' A)] (p : PolynomialPresentation (algebraMap R A)) :
    IsDualizingComplex (relativeDualizing (p.baseChange (R' := R'))) :=
  PolynomialPresentation.upperShriekFunctor_isDualizingComplex _ _
    (isDualizingComplex_single_self_field R')

/-- Being a dualizing complex depends on the object only through its isomorphism class: transport
an injective representative, the finiteness of each cohomology module, and the hypothesis of the
homothety condition along the isomorphism. -/
private theorem isDualizingComplex_of_iso {B : Type u} [CommRing B] [IsNoetherianRing B]
    {K L : DerivedCategory (ModuleCat.{u} B)} (e : K ≅ L) (hK : IsDualizingComplex K) :
    IsDualizingComplex L := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
    exact ⟨a, b, I, hge, hle, hinj, ⟨e.symm ≪≫ eI⟩⟩
  · intro i
    let : Module.Finite B ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj K) :=
      hK.finiteCohomology i
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).mapIso e).toLinearEquiv
  · rintro I ⟨eI⟩ hinj hbound
    exact hK.homothetyQuasiIso I ⟨eI ≪≫ e.symm⟩ hinj hbound

/-- **[Stacks, Tag 0BZW] (2)(b).**  Let `φ : R → A` be a flat homomorphism of finite type of
Noetherian rings, presented by `p`, and let `R → k` be any homomorphism to a field.  Then the
derived base change of `ω^•_{A/R} = φ^!(R)` along the coprojection `A → k ⊗_R A` is a dualizing
complex for the fibre ring `k ⊗_R A`.

The route is the source's.  Base change for the relative dualizing complex, [Stacks, Tag 0BZV]
case (2) at `R' = k`, identifies that derived base change with the relative dualizing complex
`ω^•_{A'/k}` of the base-changed map `k → A' = k ⊗_R A`; and `ω^•_{A'/k}` is a dualizing complex
for `A'` by [Stacks, Tag 0BZL], a field placed in degree zero being a dualizing complex for
itself.  The fibre ring is Noetherian because it is of finite type over `k`. -/
theorem isDualizingComplex_derivedExtensionScalars_upperShriekFunctor_unit_of_field
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (k : Type u) [Field k] [Algebra R k]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat) :
    letI : IsNoetherianRing (TensorProduct R k A) := isNoetherianRing_baseChange k p
    IsDualizingComplex
      ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeRight :
            A →ₐ[R] TensorProduct R k A).toRingHom).functor.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  let : IsNoetherianRing (TensorProduct R k A) := isNoetherianRing_baseChange k p
  exact isDualizingComplex_of_iso
    (nonempty_iso_relativeDualizing_baseChange k p hflat).some.symm
    (isDualizingComplex_relativeDualizing_baseChange k p)

/-- **The derived fibre of `ω^•_{A/R}` at a maximal ideal, when every fibre ring is Gorenstein.**
It has a single nonzero cohomology module, which is one dimensional over the residue field, and
it vanishes in all low degrees.

Let `m ⊆ A` be maximal and `q ⊆ R` the prime under it.  The residue field `κ(m)` is an algebra
over the fibre ring `A ⊗_R κ(q)` by the universal property of the base change, compatibly with
`A → κ(m)`, so the derived fibre of `ω^•_{A/R}` at `m` is the derived fibre at `κ(m)` of the
relative dualizing complex of the fibre.  That complex is a dualizing complex for the fibre ring,
so [Stacks, Tag 0DW9] (1)(a) turns Gorensteinness of the fibre into its invertibility, which is
inherited by its derived base change to `κ(m)`; over a field an invertible object is a one
dimensional vector space placed in a single degree. -/
private theorem exists_finrank_derivedFibre_relativeDualizing {R A : Type u} [CommRing R]
    [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A] [Algebra R A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (hGor : ∀ (q : Ideal R) [q.IsPrime], letI := isNoetherianRing_baseChange q.ResidueField p
      IsGorensteinRing (q.Fiber A))
    (m : Ideal A) [m.IsMaximal] :
    ∃ n a : ℤ,
      (∀ i : ℤ, Module.finrank m.ResidueField
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A m.ResidueField)).functor.obj (relativeDualizing p))) =
        if i = n then 1 else 0) ∧
      ∀ i : ℤ, i < a → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A m.ResidueField)).functor.obj (relativeDualizing p))) := by
  set q : Ideal R := m.comap (algebraMap R A) with hq
  have : q.IsPrime := Ideal.IsPrime.comap _
  let : Algebra R m.ResidueField :=
    ((algebraMap A m.ResidueField).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A m.ResidueField := .of_algebraMap_eq' rfl
  let : Algebra q.ResidueField m.ResidueField :=
    (Ideal.ResidueField.map q m (algebraMap R A) rfl).toAlgebra
  have : IsScalarTower R q.ResidueField m.ResidueField :=
    .of_algebraMap_eq fun r =>
      (Ideal.ResidueField.map_algebraMap q m (algebraMap R A) rfl r).symm
  let L : q.Fiber A →ₐ[q.ResidueField] m.ResidueField :=
    AlgHom.liftEquiv R q.ResidueField A m.ResidueField
      (IsScalarTower.toAlgHom R A m.ResidueField)
  have hL : L.toRingHom.comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] q.Fiber A).toRingHom =
      algebraMap A m.ResidueField :=
    congrArg AlgHom.toRingHom
      ((AlgHom.liftEquiv R q.ResidueField A m.ResidueField).left_inv
        (IsScalarTower.toAlgHom R A m.ResidueField))
  let : Algebra (q.Fiber A) m.ResidueField := L.toRingHom.toAlgebra
  have hcomp : (algebraMap (q.Fiber A) m.ResidueField).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] q.Fiber A).toRingHom =
      algebraMap A m.ResidueField := hL
  have : IsNoetherianRing (q.Fiber A) := isNoetherianRing_baseChange q.ResidueField p
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    (q.Fiber A)).choose
  have hInvFibre : MonoidalCategory.IsInvertible
      (relativeDualizing (p.baseChange (R' := q.ResidueField))) :=
    (isGorensteinRing_iff_isInvertible_canonical _
      (isDualizingComplex_relativeDualizing_baseChange q.ResidueField p)).mp (hGor q)
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    m.ResidueField).choose
  have hInv := DerivedCategory.Invertible.isInvertible_derivedExtensionScalars
    (algebraMap (q.Fiber A) m.ResidueField) _ hInvFibre
  obtain ⟨e₀⟩ := nonempty_iso_relativeDualizing_baseChange_of_isInvertible q.ResidueField p hflat
    (.inr hInvFibre)
  let e := derivedFibreIso
    (Algebra.TensorProduct.includeRight : A →ₐ[R] q.Fiber A).toRingHom
    (algebraMap (q.Fiber A) m.ResidueField) (algebraMap A m.ResidueField) hcomp e₀
  obtain ⟨n, hn⟩ :=
    DerivedCategory.Invertible.exists_finrank_homology_eq_ite_of_isInvertible_field
      m.ResidueField _ hInv
  obtain ⟨a, b, hvan, -⟩ :=
    ((DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit _).2 hInv).2.1
  refine ⟨n, a, fun i => ?_, fun i hi => ?_⟩
  · rw [LinearEquiv.finrank_eq ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} m.ResidueField) i).mapIso e).toLinearEquiv]
    exact hn i
  · exact (hvan i (by simp only [Set.mem_Icc]; omega)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).mapIso e)

open StacksDraft.Perfect in
/-- **The relative dualizing complex of a flat homomorphism of finite type is perfect once its
derived fibres vanish in low degrees.**  It is pseudo-coherent and bounded below by
[Stacks, Tag 0BZW] (1)(a), the presentation being perfect because `φ` is flat; the fibrewise
criterion of [Stacks, Tag 068W] then upgrades that to perfectness.

This is the step at which the source's appeal to [Stacks, Tag 0BYP] is replaced: `ω^•_{A/R}` is
not perfect over `A` for a general flat `φ`, only pseudo-coherent, so the perfectness needed by
the rank argument has to come from the Gorenstein hypothesis through the fibres. -/
private theorem isPerfect_relativeDualizing {R A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra R A]
    (p : PolynomialPresentation (algebraMap R A)) (hflat : (algebraMap R A).Flat)
    (hvan : ∀ m : MaximalSpectrum A, ∃ a : ℤ, ∀ i : ℤ, i < a → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.asIdeal.ResidueField) i).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A m.asIdeal.ResidueField)).functor.obj (relativeDualizing p)))) :
    StacksDraft.Perfect.IsPerfect (relativeDualizing p) := by
  have hbdd := p.upperShriekFunctor_unit_derivedCategoryBBounded.{u, 0}
    (p.isPerfectModule_of_flat hflat)
  let eU : p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R (ULift.{0} R))) ≅ relativeDualizing p :=
    p.upperShriekFunctor.{u, 0}.mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (ULift.moduleEquiv : ULift.{0} R ≃ₗ[R] R).toModuleIso)
  have hPC : StacksDraft.PseudoCoherence.IsPseudoCoherent (relativeDualizing p) :=
    (isPseudoCoherent_of_derivedCategoryBMinus.{u, 0} ⟨hbdd.1.2, hbdd.2⟩).ofIso eU
  have hGE : ∃ n : ℤ, (relativeDualizing p).IsGE n := by
    obtain ⟨n, hn⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).1 hbdd.1.1
    exact ⟨n, Triangulated.TStructure.isGE_of_iso DerivedCategory.TStructure.t eU n⟩
  have H := isPerfect_iff_isPerfect_at_primes_of_isBoundedBelow_and_stalkwise_criteria.{u, u}
    (relativeDualizing p) hPC
  exact (H.2.2.2.2 hGE).mpr (H.2.1.mpr (H.2.2.2.1.mpr hvan))

/-- **Stacks Project, Tag 0E4C.**  Let `φ : R → A` be a flat homomorphism of finite type of
Noetherian rings.  Then the fibres `A ⊗_R κ(q)` are Gorenstein for every prime `q ⊆ R` if and
only if the relative dualizing complex `ω^•_{A/R} = φ^!(R)` is an invertible object of `D(A)`.

The statement is made for an arbitrary polynomial presentation `p` of `φ`, so it holds for every
model of `φ^!`. -/
@[stacks 0E4C]
theorem isGorensteinRing_fiber_iff_isInvertible_upperShriekFunctor_unit
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A)) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
    (∀ (q : Ideal R) [q.IsPrime], letI := isNoetherianRing_baseChange q.ResidueField p
        IsGorensteinRing (q.Fiber A)) ↔
      MonoidalCategory.IsInvertible
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory A).choose
  have hflat : (algebraMap R A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  constructor
  · intro hGor
    have hfibre := fun m : MaximalSpectrum A => have := m.isMaximal
      exists_finrank_derivedFibre_relativeDualizing p hflat hGor m.asIdeal
    refine (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit _).1.mpr
      (DerivedCategory.Invertible.isLocallyShiftedUnit_of_isPerfect_of_maximalFibre_finrank _
        (isPerfect_relativeDualizing p hflat
          (fun m => ⟨(hfibre m).choose_spec.choose, (hfibre m).choose_spec.choose_spec.2⟩))
        fun m hm => ?_)
    obtain ⟨n, a, hn, -⟩ := hfibre ⟨m, hm⟩
    exact ⟨n, hn⟩
  · intro hInv q _
    have : IsNoetherianRing (q.Fiber A) := isNoetherianRing_baseChange q.ResidueField p
    let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (q.Fiber A)).choose
    have hInvX := DerivedCategory.Invertible.isInvertible_derivedExtensionScalars
      (Algebra.TensorProduct.includeRight : A →ₐ[R] q.Fiber A).toRingHom _ hInv
    obtain ⟨e₀⟩ := nonempty_iso_relativeDualizing_baseChange_of_isInvertible q.ResidueField p
      hflat (.inl hInvX)
    exact (isGorensteinRing_iff_isInvertible_canonical _
      (isDualizingComplex_relativeDualizing_baseChange q.ResidueField p)).mpr
      (isInvertible_of_iso e₀ hInvX)

end Dualizing

end
