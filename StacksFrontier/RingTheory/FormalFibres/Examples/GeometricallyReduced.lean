module

public import Mathlib
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Unramified.Field
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.FieldTheory.SeparableAlgebraic.Localization
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.CohenMacaulay.LocusBaseChange
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty
public import StacksFrontier.RingTheory.GeometricallyNormal.Defs
public import StacksFrontier.RingTheory.GeometricallyNormal.Localization
public import StacksFrontier.RingTheory.GeometricallyNormal.Separable
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.GeometricallyReduced.Separable
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.Reduced
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Serre.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Serre.FlatAscent
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.CohenMacaulay.Support

@[expose] public section

/-!
# Formal fibre properties: geometric reducedness

Stacks Project, Chapter 15 "More on Algebra". The tag treated here is

0BIW.

## Tag 0BIW — Geometric reducedness and properties of formal fibres

Geometric reducedness satisfies properties (A)--(E) used in the study of formal fibres: it is
preserved by finitely generated field extension, is detected on local rings, ascends through a
regular map in a composite of flat maps, descends through a faithfully flat map, and is preserved
when the base field is enlarged by a separable algebraic extension.

### Main definitions

No new definitions are introduced.

### Main results

* `geometricReducedness_satisfies_formalFibre_properties`: properties (A)--(E) hold
  for geometric reducedness.

### Implementation notes

A regular ring map is expressed as a flat map whose fibres are geometrically regular. The fibre
of `A → B` at `p` is `p.Fiber B = κ(p) ⊗[A] B`. Compatibility of the maps in a tower is
recorded by `IsScalarTower`, and a separable algebraic field extension is
`Algebra.IsSeparable`.

### References

* [Stacks Project, Tag 0BIW](https://stacks.math.columbia.edu/tag/0BIW)

-/

/-! ### Stacks Tag 0BIW -/

section

section

set_option maxRecDepth 4096

public section

open scoped TensorProduct

universe u v w

private noncomputable def fiberMap
    (A : Type u) (B : Type v) (C : Type w) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (p : Ideal A) [p.IsPrime] : p.Fiber B →ₐ[p.ResidueField] p.Fiber C :=
  Algebra.TensorProduct.lTensor p.ResidueField (IsScalarTower.toAlgHom A B C)

private theorem fiberMap_injective
    (A : Type u) (B : Type v) (C : Type w) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.FaithfullyFlat B C] (p : Ideal A) [p.IsPrime] :
    Function.Injective (fiberMap A B C p) := by
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.includeRight.toRingHom.toAlgebra
  intro x y h
  let e := Algebra.IsPushout.cancelBaseChangeAlg A p.ResidueField B (p.Fiber B) C
  have he : e.symm.toAlgHom.comp (fiberMap A B C p) =
      Algebra.TensorProduct.includeLeft := by
    simpa [e, fiberMap] using
      (Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor A B C p.ResidueField)
  have hleft : x ⊗ₜ[B] (1 : C) = y ⊗ₜ[B] (1 : C) := by
    have hh := congrArg e.symm h
    change (Algebra.TensorProduct.includeLeft :
      p.Fiber B →ₐ[p.ResidueField] p.Fiber B ⊗[B] C) x =
      (Algebra.TensorProduct.includeLeft :
      p.Fiber B →ₐ[p.ResidueField] p.Fiber B ⊗[B] C) y
    rw [← he]
    exact hh
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := B) (B := C)
    (p.Fiber B)
  simpa using congrArg (TensorProduct.comm B (p.Fiber B) C) hleft

private theorem Algebra.IsGeometricallyReduced.of_faithfullyFlat
    {k A B : Type*} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [Module.FaithfullyFlat A B] [Algebra.IsGeometricallyReduced k B] :
    Algebra.IsGeometricallyReduced k A :=
  Algebra.IsGeometricallyReduced.of_injective
    (IsScalarTower.toAlgHom k A B) (FaithfulSMul.algebraMap_injective A B)

private theorem isReduced_of_geometricallyReduced_localizations
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      Algebra.IsGeometricallyReduced k (Localization.AtPrime p)) : IsReduced R := by
  refine isReduced_ofLocalizationMaximal R fun p hp ↦ ?_
  have := h p
  exact Algebra.isReduced_of_isGeometricallyReduced k

private theorem geometricReducedness_of_geometricLocalizations
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      Algebra.IsGeometricallyReduced k (Localization.AtPrime p)) :
    Algebra.IsGeometricallyReduced k R := by
  classical
  have : IsReduced R := isReduced_of_geometricallyReduced_localizations k R h
  let ι := {p : Ideal R // p ∈ minimalPrimes R}
  have : Finite ι := (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
  let : Fintype ι := Fintype.ofFinite ι
  have : ∀ i : ι, i.1.IsPrime := fun i ↦ Ideal.IsMinimalPrime.isPrime i.2
  let g : ∀ i : ι, R →ₐ[k] Localization.AtPrime i.1 := fun i ↦ by
    have : i.1.IsPrime := Ideal.IsMinimalPrime.isPrime i.2
    exact IsScalarTower.toAlgHom k R (Localization.AtPrime i.1)
  have hg : Function.Injective (AlgHom.pi g) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    have hm : x ∈ sInf (minimalPrimes R) := Ideal.mem_sInf.mpr fun p hp ↦ by
      have : p.IsPrime := Ideal.IsMinimalPrime.isPrime hp
      have hzero : (algebraMap R (Localization.AtPrime p)) x = 0 := by
        simpa [g] using congrFun hx (⟨p, hp⟩ : ι)
      obtain ⟨s, hs⟩ :=
        (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) x).mp hzero
      have hprod : (s : R) * x ∈ p := hs ▸ p.zero_mem
      exact (‹p.IsPrime›.mem_or_mem hprod).resolve_left s.property
    simpa [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced] using hm
  have : ∀ i : ι,
      IsReduced (AlgebraicClosure k ⊗[k] Localization.AtPrime i.1) := by
    intro i
    have : i.1.IsPrime := Ideal.IsMinimalPrime.isPrime i.2
    have : Algebra.IsGeometricallyReduced k (Localization.AtPrime i.1) := h i.1
    exact (Algebra.isGeometricallyReduced_field_iff k _).mp inferInstance
  have hprod : IsReduced
      (AlgebraicClosure k ⊗[k] (∀ i : ι, Localization.AtPrime i.1)) :=
    isReduced_of_injective
      (Algebra.TensorProduct.piRight k k (AlgebraicClosure k)
        (fun i : ι ↦ Localization.AtPrime i.1)) (AlgEquiv.injective _)
  have hinj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id k (AlgebraicClosure k)) (AlgHom.pi g)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hg
  exact (Algebra.isGeometricallyReduced_field_iff k R).mpr
    (isReduced_of_injective _ hinj)

private theorem geometricReducedness_localizes
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [Algebra.IsGeometricallyReduced k R] (p : Ideal R) [p.IsPrime] :
    Algebra.IsGeometricallyReduced k (Localization.AtPrime p) := by
  let L := AlgebraicClosure k
  let T := Localization.AtPrime p
  let M := p.primeCompl
  let f : (L ⊗[k] R) →ₐ[k] (L ⊗[k] T) :=
    Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k R T)
  let : Algebra (L ⊗[k] R) (L ⊗[k] T) := f.toRingHom.toAlgebra
  let : Algebra L (L ⊗[k] T) := Algebra.TensorProduct.leftAlgebra
  have : IsScalarTower L (L ⊗[k] R) (L ⊗[k] T) :=
    .of_algebraMap_eq (by
      intro x
      change (algebraMap L (L ⊗[k] T)) x = f (x ⊗ₜ[k] (1 : R))
      have hmap : f (x ⊗ₜ[k] (1 : R)) = x ⊗ₜ[k] (1 : T) := by
        simp [f]
      rw [hmap]
      change (algebraMap L (L ⊗[k] T)) x =
        (algebraMap L L) x ⊗ₜ[k] (1 : T)
      exact Algebra.TensorProduct.algebraMap_apply
        (R := k) (S := L) (A := L) (B := T) x)
  have : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L)))
      (L ⊗[k] T) := by
    apply IsLocalization.tensorProduct_tensorProduct_right k L M T
    ext
    simp [f, RingHom.algebraMap_toAlgebra]
  have hred : IsReduced (L ⊗[k] R) :=
    (Algebra.isGeometricallyReduced_field_iff k R).mp inferInstance
  exact (Algebra.isGeometricallyReduced_field_iff k T).mpr
    (isReduced_localizationPreserves
      (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L)))
      (L ⊗[k] T) hred)

private theorem geometricReducedness_iff_geometricLocalizations
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
    [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
      Algebra.IsGeometricallyReduced k (Localization.AtPrime p)) ↔
      Algebra.IsGeometricallyReduced k R :=
  ⟨geometricReducedness_of_geometricLocalizations k R,
    fun _ p _ ↦ geometricReducedness_localizes k R p⟩

private theorem geometricReducedness_baseChange_of_allFields
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R] [Algebra k k'] [Algebra k R]
    (h : ∀ (L : Type v) [Field L] [Algebra k L], IsReduced (L ⊗[k] R)) :
    Algebra.IsGeometricallyReduced k' (k' ⊗[k] R) := by
  have hred : IsReduced (AlgebraicClosure k' ⊗[k] R) := h _
  exact (Algebra.isGeometricallyReduced_field_iff k' (k' ⊗[k] R)).mpr
    (isReduced_of_injective
      (Algebra.TensorProduct.cancelBaseChange k k' k' (AlgebraicClosure k') R)
      (AlgEquiv.injective _))

private theorem geometricReducedness_fibers_descend
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Module.Flat A B] [Module.FaithfullyFlat B C]
    (h : ∀ (p : Ideal A) [p.IsPrime],
      Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber C)) :
    ∀ (p : Ideal A) [p.IsPrime],
      Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber B) := by
  intro p hp
  have := h p
  exact Algebra.IsGeometricallyReduced.of_injective (fiberMap A B C p)
    (fiberMap_injective A B C p)

/-- Reducedness after field extension is independent of the universe of the extension. -/
private theorem isReduced_tensorProduct_field
    (k : Type u) (K : Type v) (R : Type w)
    [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R]
    [Algebra.IsGeometricallyReduced k R] : IsReduced (K ⊗[k] R) := by
  have hsmall : ∀ (L : Type u) [Field L] [Algebra k L], IsReduced (L ⊗[k] R) :=
    ((Algebra.isGeometricallyReduced_tfae k (ringExpChar k) R
      (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)).out 6 5).mp
      ‹Algebra.IsGeometricallyReduced k R›
  suffices IsReduced (R ⊗[k] K) from
    isReduced_of_injective (Algebra.TensorProduct.comm k K R) (AlgEquiv.injective _)
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    ((Subalgebra.fg_iff_finiteType B).mp hB)
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let T := MvPolynomial (Fin n) k ⧸ RingHom.ker f
  have : IsDomain T := Function.Injective.isDomain e.toRingHom e.injective
  have : IsReduced (FractionRing T ⊗[k] R) := hsmall (FractionRing T)
  have : IsReduced (R ⊗[k] FractionRing T) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k R (FractionRing T))
      (AlgEquiv.injective _)
  let g : B →ₐ[k] FractionRing T := (IsScalarTower.toAlgHom k T (FractionRing T)).comp
    e.symm.toAlgHom
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id k R) g)
    (Module.Flat.lTensor_preserves_injective_linearMap _
      ((FaithfulSMul.algebraMap_injective T (FractionRing T)).comp e.symm.injective))

private theorem geometricReducedness_baseChange_algebraic
    (k : Type u) (k' : Type v) (R : Type w)
    [Field k] [Field k'] [CommRing R] [Algebra k k'] [Algebra k R]
    [Algebra.IsAlgebraic k k']
    (h : Algebra.IsGeometricallyReduced k R) :
    Algebra.IsGeometricallyReduced k' (k' ⊗[k] R) :=
  geometricReducedness_baseChange_of_allFields k k' R
    fun L _ _ ↦ isReduced_tensorProduct_field k L R

/-- A finite extension of the residue field preserves Noetherianness of a fibre. -/
theorem isNoetherianRing_finite_extension_fiber
    (A : Type u) (C : Type v) [CommRing A] [CommRing C]
    [Algebra A C] [IsNoetherianRing C] (p : Ideal A) [p.IsPrime]
    (K : Type w) [Field K] [Algebra p.ResidueField K]
    [FiniteDimensional p.ResidueField K] :
    IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber C) := by
  let : Algebra C (p.Fiber C) := Algebra.TensorProduct.rightAlgebra
  have : IsNoetherianRing (p.Fiber C) :=
    isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ (S := C) p).symm.toRingEquiv
  have : IsNoetherianRing (p.Fiber C ⊗[p.ResidueField] K) :=
    Algebra.FiniteType.isNoetherianRing (p.Fiber C) (p.Fiber C ⊗[p.ResidueField] K)
  exact isNoetherianRing_of_ringEquiv _
    (Algebra.TensorProduct.comm p.ResidueField (p.Fiber C) K).toRingEquiv

/-- Fibres of a base change of a map with geometrically reduced fibres are reduced. -/
private theorem isReduced_fiber_baseChange
    (B : Type u) (C : Type v) (D : Type w)
    [CommRing B] [CommRing C] [CommRing D] [Algebra B C] [Algebra B D]
    (q : Ideal B) [q.IsPrime] (Q : Ideal D) [Q.IsPrime] [Q.LiesOver q]
    [Algebra.IsGeometricallyReduced q.ResidueField (q.Fiber C)] :
    IsReduced (Q.Fiber (D ⊗[B] C)) := by
  let : Algebra q.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.mapₐ q Q (Algebra.ofId B D) (Ideal.over_def Q q)).toRingHom.toAlgebra
  have : IsScalarTower B q.ResidueField Q.ResidueField :=
    .of_algebraMap_eq fun x ↦
      ((Ideal.ResidueField.mapₐ q Q (Algebra.ofId B D)
        (Ideal.over_def Q q)).commutes x).symm
  have : IsReduced (Q.ResidueField ⊗[q.ResidueField] q.Fiber C) :=
    isReduced_tensorProduct_field q.ResidueField Q.ResidueField (q.Fiber C)
  exact isReduced_of_injective
    ((Algebra.TensorProduct.cancelBaseChange B D D Q.ResidueField C).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange B q.ResidueField q.ResidueField
        Q.ResidueField C).symm.toRingEquiv) (RingEquiv.injective _)

/-- Reducedness ascends under base change of a flat map with geometrically reduced fibres. -/
private theorem isReduced_of_flat_geometricFibres_baseChange
    (B : Type u) (C : Type v) (D : Type w)
    [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] [Algebra B D] [Module.Flat B C]
    [IsNoetherianRing D] [IsNoetherianRing (D ⊗[B] C)] [IsReduced D]
    (hgeo : ∀ (q : Ideal B) [q.IsPrime],
      Algebra.IsGeometricallyReduced q.ResidueField (q.Fiber C)) :
    IsReduced (D ⊗[B] C) := by
  apply isReduced_of_flat_of_isReduced_fiber (R := D)
  intro Q _
  let q : Ideal B := Q.comap (algebraMap B D)
  have : q.IsPrime := inferInstance
  have : Q.LiesOver q := ⟨rfl⟩
  have : Algebra.IsGeometricallyReduced q.ResidueField (q.Fiber C) := hgeo q
  exact isReduced_fiber_baseChange B C D q Q

/-- Geometrically reduced fibres are preserved by composition of flat maps of Noetherian
rings. -/
private theorem geometricReducedness_fibers_comp
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing B] [IsNoetherianRing C] [Module.Flat B C]
    (hB : ∀ (p : Ideal A) [p.IsPrime],
      Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber B))
    (hC : ∀ (q : Ideal B) [q.IsPrime],
      Algebra.IsGeometricallyReduced q.ResidueField (q.Fiber C))
    (p : Ideal A) [p.IsPrime] :
    Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber C) := by
  apply ((Algebra.isGeometricallyReduced_tfae p.ResidueField
    (ringExpChar p.ResidueField) (p.Fiber C)
    (perfectClosure p.ResidueField (AlgebraicClosure p.ResidueField))
    (AlgebraicClosure p.ResidueField)).out 1 6).mp
  intro K _ _ _ _
  let : Algebra A K :=
    ((algebraMap p.ResidueField K).comp (algebraMap A p.ResidueField)).toAlgebra
  have : IsScalarTower A p.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber B) :=
    isNoetherianRing_finite_extension_fiber A B p K
  have : IsNoetherianRing (K ⊗[p.ResidueField] p.Fiber C) :=
    isNoetherianRing_finite_extension_fiber A C p K
  let eB := Algebra.TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField K B
  let eC := Algebra.TensorProduct.cancelBaseChange A p.ResidueField p.ResidueField K C
  have : IsNoetherianRing (K ⊗[A] B) :=
    isNoetherianRing_of_ringEquiv _ eB.toRingEquiv
  have : IsNoetherianRing (K ⊗[A] C) :=
    isNoetherianRing_of_ringEquiv _ eC.toRingEquiv
  have := hB p
  have : IsReduced (K ⊗[A] B) := isReduced_of_injective eB.symm (AlgEquiv.injective _)
  have : IsReduced (B ⊗[A] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm A B K) (AlgEquiv.injective _)
  have : IsNoetherianRing (B ⊗[A] K) :=
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A B K).symm.toRingEquiv
  let eBC : ((B ⊗[A] K) ⊗[B] C) ≃+* (K ⊗[A] C) :=
    ((Algebra.TensorProduct.comm B C (B ⊗[A] K)).symm.trans
      (Algebra.TensorProduct.cancelBaseChange A B B C K)).toRingEquiv.trans
        (Algebra.TensorProduct.comm A C K).toRingEquiv
  have : IsNoetherianRing ((B ⊗[A] K) ⊗[B] C) :=
    isNoetherianRing_of_ringEquiv _ eBC.symm
  have : IsReduced ((B ⊗[A] K) ⊗[B] C) :=
    isReduced_of_flat_geometricFibres_baseChange B C (B ⊗[A] K) hC
  have : IsReduced (K ⊗[A] C) := isReduced_of_injective eBC.symm eBC.symm.injective
  exact isReduced_of_injective eC (AlgEquiv.injective _)

/-- **Stacks 0BIW.** Geometric reducedness satisfies properties (A)--(E) for formal fibres:
base change by a finitely generated field extension, detection on local rings, ascent along a
regular map, faithfully flat descent, and separable algebraic extension of the base field. -/
@[stacks 0BIW, ega "IV 7.5.3" "(viii) reduced", ega "IV 7.9.7" "partial"]
public theorem geometricReducedness_satisfies_formalFibre_properties :
    (∀ (k : Type u) (k' : Type v) (R : Type w) [Field k] [Field k'] [CommRing R]
      [Algebra k k'] [Algebra k R] [Algebra.EssFiniteType k k'] [IsNoetherianRing R],
      Algebra.IsGeometricallyReduced k R →
        Algebra.IsGeometricallyReduced k' (k' ⊗[k] R)) ∧
    (∀ (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ (p : Ideal R) [p.IsPrime],
        Algebra.IsGeometricallyReduced k (Localization.AtPrime p)) ↔
          Algebra.IsGeometricallyReduced k R) ∧
    (∀ (A : Type u) (B : Type v) (C : Type w)
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ (p : Ideal A) [p.IsPrime],
        Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber B)) →
      (∀ (q : Ideal B) [q.IsPrime],
        Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C)) →
      ∀ (p : Ideal A) [p.IsPrime],
        Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber C)) ∧
    (∀ (A : Type u) (B : Type v) (C : Type w)
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ (p : Ideal A) [p.IsPrime],
        Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber C)) →
      ∀ (p : Ideal A) [p.IsPrime],
        Algebra.IsGeometricallyReduced p.ResidueField (p.Fiber B)) ∧
    (∀ (k : Type u) (k' : Type v) (R : Type w)
      [Field k] [Field k'] [CommRing R]
      [Algebra k k'] [Algebra k R] [Algebra k' R] [IsScalarTower k k' R]
      [Algebra.IsSeparable k k'] [IsNoetherianRing R],
      Algebra.IsGeometricallyReduced k R → Algebra.IsGeometricallyReduced k' R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k k' R _ _ _ _ _ _ _ _
    exact geometricReducedness_baseChange_of_allFields k k' R
      (fun L _ _ ↦ isReduced_tensorProduct_field k L R)
  · exact geometricReducedness_iff_geometricLocalizations
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hB hC
    apply geometricReducedness_fibers_comp A B C hB
    intro q _
    have := hC q
    exact Algebra.isGeometricallyReduced_of_isGeometricallyRegular q.ResidueField (q.Fiber C)
  · exact geometricReducedness_fibers_descend
  · intro k k' R _ _ _ _ _ _ _ _ _ h
    exact (Algebra.isGeometricallyReduced_iff_of_isSeparable k k' R).mp h

end

end

end

end
