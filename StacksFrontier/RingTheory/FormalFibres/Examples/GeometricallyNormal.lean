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
# Formal fibre properties: geometric normality

Stacks Project, Chapter 15 "More on Algebra". The tag treated here is

0BIX.

## Tag 0BIX — Geometric normality and properties of formal fibres

Geometric normality satisfies properties (A)--(E) used in the study of formal fibres: it is
preserved by finitely generated field extension, is detected on local rings, ascends through a
regular map in a composite of flat maps, descends through a faithfully flat map, and is preserved
when the base field is enlarged by a separable algebraic extension.

### Main definitions

No new definitions are introduced.

### Main results

* `geometricNormality_satisfies_formalFibre_properties`: properties (A)--(E) hold for
  geometric normality.

### Implementation notes

A regular ring map is expressed as a flat map whose fibres are geometrically regular. The fibre
of `A → B` at `p` is `p.Fiber B = κ(p) ⊗[A] B`. Compatibility of the maps in a tower is recorded
by `IsScalarTower`, and a separable algebraic field extension is `Algebra.IsSeparable`.

### References

* [Stacks Project, Tag 0BIX](https://stacks.math.columbia.edu/tag/0BIX)

-/

/-! ### Stacks Tag 0BIX -/

section

section

set_option maxRecDepth 4096

@[expose] public section

open scoped TensorProduct

universe u v w

private theorem essFiniteType_small {k : Type u} {K : Type v} [Field k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] : Small.{u} K := by
  let S := Algebra.EssFiniteType.subalgebra k K
  have : Small.{u} S := Algebra.FiniteType.small (R := k)
  have : Small.{u} (Algebra.EssFiniteType.submonoid k K) := inferInstance
  exact small_of_surjective (IsLocalization.mk'_surjective (S := K)
    (Algebra.EssFiniteType.submonoid k K))

/-- Normality of `L ⊗[k] R` follows from normality of `F ⊗[k] R` for all essentially finite type
field extensions `F` of `k` in the universe of `k`. -/
private theorem isNormalRing_tensorProduct_of_forall_essFiniteType
    {k : Type u} {L : Type v} {R : Type*} [Field k] [Field L] [Algebra k L] [CommRing R]
    [Algebra k R]
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
      IsNormalRing (K ⊗[k] R)) : IsNormalRing (L ⊗[k] R) := by
  apply isNormalRing_tensorProduct_of_forall_fg_intermediateField
  intro F hF
  have : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
  have : Small.{u} F := essFiniteType_small (k := k)
  have : Algebra.EssFiniteType k (Shrink.{u} F) :=
    (Algebra.EssFiniteType.iff_of_algEquiv (Shrink.algEquiv k F)).mpr inferInstance
  exact IsNormalRing.congr
    (Algebra.TensorProduct.congr (Shrink.algEquiv k F) (AlgEquiv.refl)).toRingEquiv
    (h (Shrink.{u} F))

private theorem normal_baseChange_any {k : Type u} {L : Type v} {R : Type*}
    [Field k] [Field L] [Algebra k L] [CommRing R] [Algebra k R]
    (h : Algebra.IsGeometricallyNormal k R) : IsNormalRing (L ⊗[k] R) :=
  isNormalRing_tensorProduct_of_forall_essFiniteType fun K _ _ _ => h.isNormalRing_tensorProduct K

private theorem isGeometricallyNormal_of_forall_essFiniteType
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
      IsNormalRing (K ⊗[k] R)) : Algebra.IsGeometricallyNormal k R :=
  ⟨fun _ _ _ => isNormalRing_tensorProduct_of_forall_essFiniteType h⟩

private theorem geo_baseChange {k : Type u} {K : Type v} {R : Type*}
    [Field k] [Field K] [CommRing R] [Algebra k K] [Algebra k R]
    (h : Algebra.IsGeometricallyNormal k R) :
    Algebra.IsGeometricallyNormal K (K ⊗[k] R) := by
  refine ⟨fun L _ _ => ?_⟩
  let : Algebra k L := Algebra.compHom L (algebraMap k K)
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  exact IsNormalRing.congr
    (Algebra.TensorProduct.cancelBaseChange k K L L R).symm.toRingEquiv
    (normal_baseChange_any h)

private theorem geo_of_all_local {k : Type u} {R : Type v} [Field k] [CommRing R]
    [Algebra k R]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      Algebra.IsGeometricallyNormal k (Localization.AtPrime p)) :
    Algebra.IsGeometricallyNormal k R := by
  refine ⟨fun K _ _ => ?_⟩
  intro q hq
  let f : R →ₐ[k] K ⊗[k] R := Algebra.TensorProduct.includeRight
  let p : Ideal R := q.comap f.toRingHom
  have : p.IsPrime := hq.comap _
  let T := K ⊗[k] R
  let U := K ⊗[k] Localization.AtPrime p
  let M : Submonoid T := p.primeCompl.map f.toMonoidHom
  let : Algebra T U :=
    (Algebra.TensorProduct.map (AlgHom.id k K)
      (IsScalarTower.toAlgHom k R (Localization.AtPrime p))).toRingHom.toAlgebra
  have htower : IsScalarTower K T U := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [T, U, RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have hloc : IsLocalization M U :=
    IsLocalization.tensorProduct_tensorProduct_right k K p.primeCompl (Localization.AtPrime p)
      (by ext a; simp [RingHom.algebraMap_toAlgebra])
  have hM : M ≤ q.primeCompl := by
    rintro _ ⟨r, hr, rfl⟩
    exact hr
  let : Algebra U (Localization.AtPrime q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ q.primeCompl hM
  have : IsScalarTower T U (Localization.AtPrime q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ q.primeCompl hM
  have : IsLocalization (q.primeCompl.map (algebraMap T U)) (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ q.primeCompl hM
  exact ((h p).isNormalRing_tensorProduct K).isLocalization
    (q.primeCompl.map (algebraMap T U)) (Localization.AtPrime q) |>.of_isLocalRing

private theorem geo_local_iff {k : Type u} {R : Type v} [Field k] [CommRing R]
    [Algebra k R] :
    (∀ (p : Ideal R) [p.IsPrime],
      Algebra.IsGeometricallyNormal k (Localization.AtPrime p)) ↔
    Algebra.IsGeometricallyNormal k R :=
  ⟨geo_of_all_local, fun _ p _ ↦ .of_isLocalization p.primeCompl⟩

private theorem tensor_map_faithfullyFlat {k R S K : Type*}
    [CommRing k] [CommRing R] [CommRing S] [CommRing K]
    [Algebra k R] [Algebra k S] [Algebra k K]
    [Algebra R S] [IsScalarTower k R S] [Module.FaithfullyFlat R S] :
    let : Algebra (R ⊗[k] K) (S ⊗[k] K) :=
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R S) (AlgHom.id k K)).toRingHom.toAlgebra
    Module.FaithfullyFlat (R ⊗[k] K) (S ⊗[k] K) := by
  let : Algebra (R ⊗[k] K) (S ⊗[k] K) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R S) (AlgHom.id k K)).toRingHom.toAlgebra
  have : IsScalarTower R (R ⊗[k] K) (S ⊗[k] K) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  have : IsScalarTower k R (S ⊗[k] K) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [IsScalarTower.algebraMap_apply k R S]
  have : IsScalarTower k (R ⊗[k] K) (S ⊗[k] K) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.IsPushout R S (R ⊗[k] K) (S ⊗[k] K) :=
    Algebra.IsPushout.tensorProduct_tensorProduct k K R S
      (by ext x; simp [RingHom.algebraMap_toAlgebra])
  have : Algebra.IsPushout R (R ⊗[k] K) S (S ⊗[k] K) :=
    Algebra.IsPushout.symm inferInstance
  have e : (R ⊗[k] K) ⊗[R] S ≃ₐ[R ⊗[k] K] (S ⊗[k] K) :=
    Algebra.IsPushout.equiv R (R ⊗[k] K) S (S ⊗[k] K)
  exact Module.FaithfullyFlat.of_linearEquiv (R ⊗[k] K)
    ((R ⊗[k] K) ⊗[R] S) e.symm.toLinearEquiv

private theorem geo_of_faithfullyFlat {k : Type u} {R : Type v} {S : Type*}
    [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Module.FaithfullyFlat R S]
    (h : Algebra.IsGeometricallyNormal k S) :
    Algebra.IsGeometricallyNormal k R := by
  refine ⟨fun K _ _ => ?_⟩
  let : Algebra (R ⊗[k] K) (S ⊗[k] K) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k R S) (AlgHom.id k K)).toRingHom.toAlgebra
  have : Module.FaithfullyFlat (R ⊗[k] K) (S ⊗[k] K) :=
    tensor_map_faithfullyFlat
  have hnormal : IsNormalRing (S ⊗[k] K) :=
    IsNormalRing.congr (Algebra.TensorProduct.comm k K S).toRingEquiv
      (h.isNormalRing_tensorProduct K)
  have hdesc : IsNormalRing (R ⊗[k] K) :=
    isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat hnormal
  exact IsNormalRing.congr (Algebra.TensorProduct.comm k R K).toRingEquiv hdesc

private theorem geo_congr {k : Type u} {R S : Type*} [Field k]
    [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (e : R ≃ₐ[k] S) (h : Algebra.IsGeometricallyNormal k R) :
    Algebra.IsGeometricallyNormal k S := by
  refine ⟨fun K _ _ => ?_⟩
  exact IsNormalRing.congr
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e).toRingEquiv
    (h.isNormalRing_tensorProduct K)

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem geo_tensor_left_of_ff {A B C K : Type*}
    [CommRing A] [CommRing B] [CommRing C] [Field K]
    [Algebra A B] [Algebra A C] [Algebra A K]
    [Algebra B C] [IsScalarTower A B C] [Module.FaithfullyFlat B C]
    (h : Algebra.IsGeometricallyNormal K (K ⊗[A] C)) :
    Algebra.IsGeometricallyNormal K (K ⊗[A] B) := by
  have h' : Algebra.IsGeometricallyNormal K (C ⊗[A] K) :=
    geo_congr (Algebra.TensorProduct.commRight A K C) h
  let : Algebra (B ⊗[A] K) (C ⊗[A] K) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B C) (AlgHom.id A K)).toRingHom.toAlgebra
  have : IsScalarTower K (B ⊗[A] K) (C ⊗[A] K) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  have : Module.FaithfullyFlat (B ⊗[A] K) (C ⊗[A] K) :=
    tensor_map_faithfullyFlat
  exact geo_congr (Algebra.TensorProduct.commRight A K B).symm
    (geo_of_faithfullyFlat h')

private theorem partD (A : Type u) (B : Type v) (C : Type*)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [Module.Flat A B] [Module.FaithfullyFlat B C]
    (hC : ∀ (p : Ideal A) [p.IsPrime],
      Algebra.IsGeometricallyNormal p.ResidueField (p.Fiber C)) :
    ∀ (p : Ideal A) [p.IsPrime],
      Algebra.IsGeometricallyNormal p.ResidueField (p.Fiber B) := by
  intro p _
  exact geo_tensor_left_of_ff (A := A) (B := B) (C := C) (K := p.ResidueField) (hC p)

end

private theorem normal_of_separable_diagonal (k k' A : Type*)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A]
    [Algebra k' A] [IsScalarTower k k' A] [Algebra.IsSeparable k k']
    (h : IsNormalRing (k' ⊗[k] A)) : IsNormalRing A := by
  let D := k' ⊗[k] k'
  let m : D →ₐ[k] k' := Algebra.TensorProduct.lmul' (R := k) (S := k')
  let : Algebra D k' := m.toRingHom.toAlgebra
  have : Algebra.IsAlgebraic k k' := Algebra.IsSeparable.isAlgebraic k k'
  obtain ⟨S, hS⟩ := exists_isLocalization_lmul'_of_isSeparable_isAlgebraic k k'
  have : IsLocalization S k' := hS
  let : Algebra k' D := Algebra.TensorProduct.leftAlgebra
  have : IsScalarTower k' D k' := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [D, m, RingHom.algebraMap_toAlgebra]
  let T := A ⊗[k'] D
  let U := A ⊗[k'] k'
  let : Algebra A T := Algebra.TensorProduct.leftAlgebra
  let : Algebra A U := Algebra.TensorProduct.leftAlgebra
  let : SMul A T := (inferInstance : Algebra A T).toSMul
  let : SMul A U := (inferInstance : Algebra A U).toSMul
  let f : T →ₐ[k'] U := Algebra.TensorProduct.map (AlgHom.id k' A)
    (IsScalarTower.toAlgHom k' D k')
  let : Algebra T U := f.toRingHom.toAlgebra
  have : IsScalarTower A T U := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    simp [T, U, f, RingHom.algebraMap_toAlgebra]
  have : IsLocalization (S.map (Algebra.TensorProduct.includeRight (R := k')
      (A := A) (B := D))) U := by
    apply IsLocalization.tensorProduct_tensorProduct_right k' A S k'
    exact congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.map_comp_includeRight (AlgHom.id k' A)
        (IsScalarTower.toAlgHom k' D k'))
  have hT : IsNormalRing T :=
    IsNormalRing.congr
      ((Algebra.TensorProduct.cancelBaseChange k k' k' A k').toRingEquiv.trans
        (Algebra.TensorProduct.comm k A k').toRingEquiv).symm h
  have hU : IsNormalRing U := hT.isLocalization
    (S.map (Algebra.TensorProduct.includeRight (R := k') (A := A) (B := D))) U
  exact IsNormalRing.congr (Algebra.TensorProduct.rid k' A A).toRingEquiv hU

set_option backward.isDefEq.respectTransparency false in
/-- An essentially finite-type base change of a regular ring homomorphism is regular. -/
private theorem isRegularRingHom_baseChange_of_essFiniteType
    {R : Type u} {Λ : Type v} {R' : Type w}
    [CommRing R] [CommRing Λ] [CommRing R'] [Algebra R Λ] [Algebra R R']
    [Algebra.EssFiniteType R R']
    (h : IsRegularRingHom (algebraMap R Λ)) :
    IsRegularRingHom
      (Algebra.TensorProduct.includeRight (R := R) (A := Λ) (B := R')).toRingHom := by
  let : Algebra R' (Λ ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  rw [isRegularRingHom_algebraMap_iff] at h
  rw [isRegularRingHom_iff_of_eq_algebraMap _ (by rfl)]
  constructor
  · let : Module.Flat R Λ := RingHom.flat_algebraMap_iff.mp h.1
    change Module.Flat R' (Λ ⊗[R] R')
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight R R' Λ).symm.toLinearEquiv
  · intro p' hp'
    have : p'.IsPrime := hp'
    let p : Ideal R := p'.comap (algebraMap R R')
    have : p.IsPrime := Ideal.IsPrime.comap (algebraMap R R')
    have : p'.LiesOver p := ⟨rfl⟩
    let := Localization.AtPrime.algebraOfLiesOver p p'
    let : Algebra p.ResidueField (p.Fiber Λ) := Algebra.TensorProduct.leftAlgebra
    let e₁ := Algebra.TensorProduct.congr
      (AlgEquiv.refl : p'.ResidueField ≃ₐ[R'] p'.ResidueField)
      (Algebra.TensorProduct.commRight R R' Λ).symm
    let e₂ := (Algebra.TensorProduct.cancelBaseChange R R' p'.ResidueField
      p'.ResidueField Λ).trans
      (Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField
        p'.ResidueField Λ).symm
    let e : p'.Fiber (Λ ⊗[R] R') ≃ₐ[p'.ResidueField]
        p'.ResidueField ⊗[p.ResidueField] (p.Fiber Λ) :=
      AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv.trans e₂.toRingEquiv) (fun x => by
        change e₂ (e₁ (algebraMap p'.ResidueField _ x)) = algebraMap p'.ResidueField _ x
        rw [show e₁ (algebraMap p'.ResidueField _ x) =
            algebraMap p'.ResidueField _ x by
          simp [e₁, Algebra.TensorProduct.algebraMap_apply]]
        exact e₂.commutes x)
    have hp := h.2 p
    have : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber Λ) := hp.2
    have : Algebra.EssFiniteType p.ResidueField p'.ResidueField := by
      have : Algebra.EssFiniteType R p'.ResidueField := .comp R R' _
      exact .of_comp R _ _
    let : CommRing (p'.ResidueField ⊗[p.ResidueField] (p.Fiber Λ)) :=
      Algebra.TensorProduct.instCommRing
    have : Algebra.IsGeometricallyRegular p'.ResidueField
        (p'.ResidueField ⊗[p.ResidueField] (p.Fiber Λ)) :=
      Stacks.GeometricallyRegular.SeparableBase.isGeometricallyRegular_tensorProduct
        p.ResidueField p'.ResidueField (p.Fiber Λ)
    have hg : Algebra.IsGeometricallyRegular p'.ResidueField (p'.Fiber (Λ ⊗[R] R')) :=
      Algebra.IsGeometricallyRegular.of_algEquiv e.symm
    refine ⟨?_, hg⟩
    have := (Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct
      (k := p'.ResidueField) (R := p'.Fiber (Λ ⊗[R] R')) p'.ResidueField).toIsNoetherian
    exact isNoetherianRing_of_ringEquiv _
      (Algebra.TensorProduct.lid p'.ResidueField (p'.Fiber (Λ ⊗[R] R'))).toRingEquiv

private theorem isNormalRing_tensorProduct_of_regular
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.EssFiniteType R T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (h : IsRegularRingHom (algebraMap R S)) (hT : IsNormalRing T) :
    IsNormalRing (S ⊗[R] T) := by
  let : Algebra T (S ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have hr := isRegularRingHom_baseChange_of_essFiniteType (R' := T) h
  rw [isRegularRingHom_iff_of_eq_algebraMap _ (by rfl)] at hr
  have : Module.Flat T (S ⊗[R] T) := RingHom.flat_algebraMap_iff.mp hr.1
  have : IsNoetherianRing (S ⊗[R] T) := Algebra.EssFiniteType.isNoetherianRing S _
  exact isNormalRing_of_flat_of_isGeometricallyRegular_fiber T (S ⊗[R] T)
    hT (fun p _ => (hr.2 p).2)

private theorem isGeometricallyNormal_fiber_of_flat_of_isGeometricallyRegular_fiber
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing B] [IsNoetherianRing C] [Module.Flat B C]
    (hB : ∀ (p : Ideal A) [p.IsPrime],
      Algebra.IsGeometricallyNormal p.ResidueField (p.Fiber B))
    (hC : ∀ (q : Ideal B) [q.IsPrime],
      Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C)) :
    ∀ (p : Ideal A) [p.IsPrime],
      Algebra.IsGeometricallyNormal p.ResidueField (p.Fiber C) := by
  intro p _
  apply isGeometricallyNormal_of_forall_essFiniteType
  intro K _ _ _
  let : Algebra A K := Algebra.compHom K (algebraMap A p.ResidueField)
  have : IsScalarTower A p.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType A K := Algebra.EssFiniteType.comp A p.ResidueField K
  have hKB : IsNormalRing (B ⊗[A] K) :=
    IsNormalRing.congr
      ((Algebra.TensorProduct.cancelBaseChange A p.ResidueField K K B).toRingEquiv.trans
        (Algebra.TensorProduct.comm A K B).toRingEquiv)
      (normal_baseChange_any (hB p))
  have hreg : IsRegularRingHom (algebraMap B C) := by
    rw [isRegularRingHom_algebraMap_iff]
    refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, fun q _ => ⟨?_, hC q⟩⟩
    have : IsNoetherianRing (C ⊗[B] q.ResidueField) :=
      Algebra.EssFiniteType.isNoetherianRing C _
    exact isNoetherianRing_of_ringEquiv _
      (Algebra.TensorProduct.comm B C q.ResidueField).toRingEquiv
  have : IsNoetherianRing (B ⊗[A] K) := Algebra.EssFiniteType.isNoetherianRing B _
  have hnormal := isNormalRing_tensorProduct_of_regular (T := B ⊗[A] K) hreg hKB
  exact IsNormalRing.congr
    (((Algebra.TensorProduct.cancelBaseChange A B C C K).toRingEquiv.trans
      (Algebra.TensorProduct.comm A C K).toRingEquiv).trans
      (Algebra.TensorProduct.cancelBaseChange A p.ResidueField K K C).symm.toRingEquiv)
    hnormal

/-- Geometric normality satisfies properties (A)--(E) for formal fibres: base change by a
finitely generated field extension, detection on local rings, ascent along a regular map,
faithfully flat descent, and separable algebraic extension of the base field. -/
@[stacks 0BIX, ega "IV 7.3.10" "special case"]
public theorem geometricNormality_satisfies_formalFibre_properties :
    (∀ (k : Type u) (k' : Type v) (R : Type w) [Field k] [Field k'] [CommRing R]
      [Algebra k k'] [Algebra k R] [Algebra.EssFiniteType k k'] [IsNoetherianRing R],
      Algebra.IsGeometricallyNormal k R →
        Algebra.IsGeometricallyNormal k' (k' ⊗[k] R)) ∧
    (∀ (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R]
      [IsNoetherianRing R],
      (∀ (p : Ideal R) [p.IsPrime],
        Algebra.IsGeometricallyNormal k (Localization.AtPrime p)) ↔
          Algebra.IsGeometricallyNormal k R) ∧
    (∀ (A : Type u) (B : Type v) (C : Type w)
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.Flat B C],
      (∀ (p : Ideal A) [p.IsPrime],
        Algebra.IsGeometricallyNormal p.ResidueField (p.Fiber B)) →
      (∀ (q : Ideal B) [q.IsPrime],
        Algebra.IsGeometricallyRegular q.ResidueField (q.Fiber C)) →
      ∀ (p : Ideal A) [p.IsPrime],
        Algebra.IsGeometricallyNormal p.ResidueField (p.Fiber C)) ∧
    (∀ (A : Type u) (B : Type v) (C : Type w)
      [CommRing A] [CommRing B] [CommRing C]
      [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
      [Module.Flat A B] [Module.FaithfullyFlat B C],
      (∀ (p : Ideal A) [p.IsPrime],
        Algebra.IsGeometricallyNormal p.ResidueField (p.Fiber C)) →
      ∀ (p : Ideal A) [p.IsPrime],
        Algebra.IsGeometricallyNormal p.ResidueField (p.Fiber B)) ∧
    (∀ (k : Type u) (k' : Type v) (R : Type w)
      [Field k] [Field k'] [CommRing R]
      [Algebra k k'] [Algebra k R] [Algebra k' R] [IsScalarTower k k' R]
      [Algebra.IsSeparable k k'] [IsNoetherianRing R],
      Algebra.IsGeometricallyNormal k R → Algebra.IsGeometricallyNormal k' R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k K R _ _ _ _ _ _ _ h
    exact geo_baseChange h
  · intro k R _ _ _ _
    exact geo_local_iff
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ hB hC
    exact isGeometricallyNormal_fiber_of_flat_of_isGeometricallyRegular_fiber A B C hB hC
  · exact partD
  · intro k K R _ _ _ _ _ _ _ _ _ h
    exact (Algebra.isGeometricallyNormal_iff_of_isSeparable k K R).mp h

end

end

end

end
