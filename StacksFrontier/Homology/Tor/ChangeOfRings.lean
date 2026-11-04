module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.RingTheory.ChangeOfRings.ExtendScalarsRingIso
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.RingTheory.PseudoCoherentMap.Locality
public import StacksFrontier.Algebra.Homology.KFlat
import StacksFrontier.Homology.KFlat.Flat
import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# The two module structures on a derived tensor product can differ

For `R = k[x, y]`, `A = R/(xy)`, and `N = R/(x)`, the two ways of retaining an
`A`-module structure on the derived tensor product of `N` and `A` over `R` need not agree.
The two displayed free resolutions produce respectively `N[1] ⊕ N` and the complex
`A → A` whose differential is multiplication by `x`, and these objects of `D(A)` are not
isomorphic.

## Main definitions

* `CochainComplex.DerivedChangeOfRings.nodalRingResolution` is the displayed `xy`-resolution
  complex over `R`.
* `CochainComplex.DerivedChangeOfRings.xAxisResolution` is the displayed `x`-resolution complex
  over `R`.
* `CochainComplex.DerivedChangeOfRings.tensorXAxisWithRestrictedNodalRing` and
  `CochainComplex.DerivedChangeOfRings.tensorRestrictedXAxisWithNodalRing` are the two
  resolution-derived tensor complexes, retaining the `A`-action from the indicated factor.
* `CochainComplex.DerivedChangeOfRings.DerivedTensorComparison` packages the augmentations, their
  resolution properties, and the canonical identifications in the derived category.

## Main results

* `CochainComplex.DerivedChangeOfRings.derivedTensorModuleStructuresDiffer` constructs the two
  resolutions and their canonical comparisons and asserts that the resulting objects of `D(A)`
  are not isomorphic.

## Implementation notes

This file covers only the counterexample of Stacks tag 08YT from the section "Derived change of
rings"; the remaining results of that section are not treated here.

The polynomial ring is `MvPolynomial Bool k`, with `false` and `true` naming `x` and `y`.
A derived tensor is defined exactly as in the source section: choose the displayed K-flat
resolution, tensor it with the other factor, and apply the localization functor to the resulting
complex. Extension of scalars equips the tensor complex with the action coming from the specified
`A`-module factor.

## References

* [The Stacks Project, Tag 08YT](https://stacks.math.columbia.edu/tag/08YT)
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex HomologicalComplex

universe u v

namespace CochainComplex.DerivedChangeOfRings

attribute [local instance] HasDerivedCategory.standard

/-- The polynomial ring `R = k[x, y]`, with variables indexed by `Bool`. -/
public abbrev PolynomialRing (k : Type u) [CommRing k] := MvPolynomial Bool k

/-- The variable `x` in `R = k[x, y]`. -/
public abbrev xVariable (k : Type u) [CommRing k] : PolynomialRing k := MvPolynomial.X false

/-- The variable `y` in `R = k[x, y]`. -/
public abbrev yVariable (k : Type u) [CommRing k] : PolynomialRing k := MvPolynomial.X true

/-- The ideal `(xy)` in `R = k[x, y]`. -/
public abbrev nodalRelationIdeal (k : Type u) [CommRing k] : Ideal (PolynomialRing k) :=
  Ideal.span {xVariable k * yVariable k}

/-- The ring `A = k[x, y]/(xy)`. -/
public abbrev NodalRing (k : Type u) [CommRing k] :=
  PolynomialRing k ⧸ nodalRelationIdeal k

/-- The quotient map `R → A`. -/
public abbrev nodalRingMap (k : Type u) [CommRing k] : PolynomialRing k →+* NodalRing k :=
  Ideal.Quotient.mk (nodalRelationIdeal k)

/-- The image `x̄` of `x` in `A = k[x, y]/(xy)`. -/
public abbrev xClass (k : Type u) [CommRing k] : NodalRing k := nodalRingMap k (xVariable k)

/-- The image `ȳ` of `y` in `A = k[x, y]/(xy)`. -/
public abbrev yClass (k : Type u) [CommRing k] : NodalRing k := nodalRingMap k (yVariable k)

/-- The ideal `(x̄)` in `A = k[x, y]/(xy)`. -/
public abbrev xAxisIdeal (k : Type u) [CommRing k] : Ideal (NodalRing k) :=
  Ideal.span {xClass k}

/-- The `A`-module `N = A/(x̄)`. -/
public abbrev XAxisModule (k : Type u) [CommRing k] := NodalRing k ⧸ xAxisIdeal k

/-- The source presentation `R/(x)` of the module `N`. -/
public abbrev PolynomialXAxisModule (k : Type u) [CommRing k] :=
  PolynomialRing k ⧸ Ideal.span {xVariable k}

/-- A module, regarded as a cochain complex concentrated in degree zero. -/
public abbrev singleModule (A : Type u) [Ring A] (M : Type v) [AddCommGroup M] [Module A M] :
    CochainComplex (ModuleCat.{v} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj (ModuleCat.of A M)

/-- Multiplication by `a` on a module, as an endomorphism of its degree-zero complex. -/
public abbrev scalarMultiplication {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M]
    [Module A M] (a : A) : singleModule A M ⟶ singleModule A M :=
  (CochainComplex.singleFunctor (ModuleCat.{v} A) 0).map
    (ModuleCat.ofHom (LinearMap.lsmul A M a))

/-- The displayed free resolution complex of `A_R`, namely `R → R` with differential
multiplication by `xy`. -/
public def nodalRingResolution (k : Type u) [CommRing k] :
    CochainComplex (ModuleCat (PolynomialRing k)) ℤ :=
  CochainComplex.mappingCone
    (scalarMultiplication (PolynomialRing k) (xVariable k * yVariable k))

/-- The displayed free resolution complex of `R/(x)`, namely `R → R` with differential
multiplication by `x`. -/
public def xAxisResolution (k : Type u) [CommRing k] :
    CochainComplex (ModuleCat (PolynomialRing k)) ℤ :=
  CochainComplex.mappingCone (scalarMultiplication (PolynomialRing k) (xVariable k))

/-- Tensor the K-flat `xy`-resolution of `A_R` with `N`. Extension of scalars followed by
tensoring over `A` retains the `A`-action from `N`, and is canonically `N ⊗_R P_A`. -/
public def tensorXAxisWithRestrictedNodalRing (k : Type u) [CommRing k] :
    CochainComplex (ModuleCat (NodalRing k)) ℤ :=
  (tensorLeft (singleModule (NodalRing k) (XAxisModule k))).obj
    ((CochainComplex.extendScalars (nodalRingMap k)).obj (nodalRingResolution k))

/-- Tensor the K-flat `x`-resolution of `N_R` with `A`. Extension of scalars is
`A ⊗_R P_N`, so its `A`-action is supplied by the second factor `A`. -/
public def tensorRestrictedXAxisWithNodalRing (k : Type u) [CommRing k] :
    CochainComplex (ModuleCat (NodalRing k)) ℤ :=
  (CochainComplex.extendScalars (nodalRingMap k)).obj (xAxisResolution k)

/-- The genuine object `N ⊗_R^ᴸ A_R` of `D(A)`, computed from the displayed K-flat
resolution of `A_R`. -/
public def derivedTensorXAxisWithRestrictedNodalRing (k : Type u) [CommRing k] :
    DerivedCategory (ModuleCat (NodalRing k)) :=
  DerivedCategory.Q.obj (tensorXAxisWithRestrictedNodalRing k)

/-- The genuine object `N_R ⊗_R^ᴸ A` of `D(A)`, computed from the displayed K-flat
resolution of `N_R`. -/
public def derivedTensorRestrictedXAxisWithNodalRing (k : Type u) [CommRing k] :
    DerivedCategory (ModuleCat (NodalRing k)) :=
  DerivedCategory.Q.obj (tensorRestrictedXAxisWithNodalRing k)

/-- The complex `N[1] ⊕ N` in `A`-modules. -/
public def splitXAxisComplex (k : Type u) [CommRing k] :
    CochainComplex (ModuleCat (NodalRing k)) ℤ :=
  (singleModule (NodalRing k) (XAxisModule k))⟦(1 : ℤ)⟧ ⊞
    singleModule (NodalRing k) (XAxisModule k)

/-- The two-term complex `A → A` whose differential is multiplication by `x̄`. -/
public def xMultiplicationComplex (k : Type u) [CommRing k] :
    CochainComplex (ModuleCat (NodalRing k)) ℤ :=
  CochainComplex.mappingCone (scalarMultiplication (NodalRing k) (xClass k))

/-- The augmentation and K-flatness data for the displayed resolutions, the canonical
identifications of the resulting genuine derived tensors with their explicit models, and their
non-isomorphism. -/
public structure DerivedTensorComparison (k : Type u) [CommRing k] where
  /-- The presentation `A/(x̄)` of `N` agrees with the source presentation `R/(x)`. -/
  xAxisEquiv : XAxisModule k ≃+* PolynomialXAxisModule k
  /-- The quotient equivalence commutes with the quotient maps from `R`. -/
  xAxisEquiv_mk (r : PolynomialRing k) :
    xAxisEquiv (Ideal.Quotient.mk (xAxisIdeal k) (nodalRingMap k r)) =
      Ideal.Quotient.mk (Ideal.span {xVariable k}) r
  /-- The augmentation of the displayed `xy`-resolution to `A_R`. -/
  nodalRingAugmentation : nodalRingResolution k ⟶
    singleModule (PolynomialRing k)
      ((ModuleCat.restrictScalars (nodalRingMap k)).obj
        (ModuleCat.of (NodalRing k) (NodalRing k)))
  /-- The displayed `xy`-complex is a resolution of `A_R`. -/
  nodalRingAugmentation_quasiIso : QuasiIso nodalRingAugmentation
  /-- The displayed `xy`-resolution is K-flat over `R`. -/
  nodalRingResolution_kFlat : (nodalRingResolution k).KFlat
  /-- The augmentation of the displayed `x`-resolution to `R/(x)`. -/
  xAxisAugmentation : xAxisResolution k ⟶
    singleModule (PolynomialRing k) (PolynomialXAxisModule k)
  /-- The displayed `x`-complex is a resolution of `R/(x)`. -/
  xAxisAugmentation_quasiIso : QuasiIso xAxisAugmentation
  /-- The displayed `x`-resolution is K-flat over `R`. -/
  xAxisResolution_kFlat : (xAxisResolution k).KFlat
  /-- Computing `N ⊗_R^ᴸ A_R` with the `xy`-resolution gives `N[1] ⊕ N` in `D(A)`. -/
  tensorXAxisWithRestrictedNodalRingIsoSplit :
    derivedTensorXAxisWithRestrictedNodalRing k ≅
      DerivedCategory.Q.obj (splitXAxisComplex k)
  /-- Computing `N_R ⊗_R^ᴸ A` with the `x`-resolution gives the complex `A → A`. -/
  tensorRestrictedXAxisWithNodalRingIsoXMultiplication :
    derivedTensorRestrictedXAxisWithNodalRing k ≅
      DerivedCategory.Q.obj (xMultiplicationComplex k)
  /-- The two genuine derived tensor objects, with their different `A`-actions, are not
  isomorphic in `D(A)`. -/
  not_iso : ¬ Nonempty
    (derivedTensorRestrictedXAxisWithNodalRing k ≅
      derivedTensorXAxisWithRestrictedNodalRing k)

/-- Annihilator of the image of `a` in `k[x, y]/(xy)`, when `a * b = x * y` and `a` is a
non-zero-divisor. -/
private theorem annihilator_aux (k : Type u) [CommRing k] (a b : PolynomialRing k)
    (hab : a * b = xVariable k * yVariable k) (ha : ∀ p q, a * p = a * q → p = q)
    (element : NodalRing k) :
    nodalRingMap k a * element = 0 ↔ element ∈ Ideal.span {nodalRingMap k b} := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective element
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    have hp : p = b * q := ha _ _ (by rw [hq, ← hab, mul_assoc])
    exact ⟨nodalRingMap k q, by rw [hp, map_mul]⟩
  · rintro ⟨q, hq⟩
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hq)
    refine ⟨q + a * r, ?_⟩
    have hp : p = a * b * r + b * q := by rw [hab, ← hr, sub_add_cancel]
    rw [hp, ← hab]
    ring

private theorem x_annihilator (k : Type u) [CommRing k]
    (element : NodalRing k) :
    xClass k * element = 0 ↔ element ∈ Ideal.span {yClass k} :=
  annihilator_aux k _ _ rfl (fun _ _ h => MvPolynomial.X_mul_cancel_left_iff.mp h) element

private theorem y_annihilator (k : Type u) [CommRing k]
    (element : NodalRing k) :
    yClass k * element = 0 ↔ element ∈ Ideal.span {xClass k} :=
  annihilator_aux k _ _ (mul_comm _ _) (fun _ _ h => MvPolynomial.X_mul_cancel_left_iff.mp h)
    element

private theorem scalarCone_augmentation_quasiIso {R : Type u} [CommRing R]
    (a : R) (ha : Function.Injective (fun r : R => a * r)) :
    ∃ ε : CochainComplex.mappingCone (scalarMultiplication R a) ⟶
      singleModule R (R ⧸ Ideal.span {a}), QuasiIso ε := by
  let f : ModuleCat.of R R ⟶ ModuleCat.of R R :=
    ModuleCat.ofHom (LinearMap.lsmul R R a)
  let g : ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ Ideal.span {a}) :=
    ModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap
  have hfg : f ≫ g = 0 := by
    ext
    show Ideal.Quotient.mk (Ideal.span {a}) (a * 1) = 0
    rw [mul_one, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton a)
  let S := ShortComplex.mk f g hfg
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S (by
    intro r
    show Ideal.Quotient.mk (Ideal.span {a}) r = 0 ↔ ∃ s, a * s = r
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact exists_congr (fun s => eq_comm)) ha (Ideal.Quotient.mk_surjective)
  let S' := S.map (CochainComplex.singleFunctor (ModuleCat R) 0)
  have : PreservesFiniteLimits (CochainComplex.singleFunctor (ModuleCat R) 0) :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single (ModuleCat R) (.up ℤ) 0))
  have : PreservesFiniteColimits (CochainComplex.singleFunctor (ModuleCat R) 0) :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single (ModuleCat R) (.up ℤ) 0))
  exact ⟨CochainComplex.mappingCone.descShortComplex S',
    CochainComplex.mappingCone.quasiIso_descShortComplex (hS.map_of_exact _)⟩

private theorem axis_augmentation_quasiIso (k : Type u) [CommRing k] :
    ∃ ε : xAxisResolution k ⟶ singleModule (PolynomialRing k)
      (PolynomialXAxisModule k), QuasiIso ε :=
  scalarCone_augmentation_quasiIso (xVariable k)
    (fun _ _ h => MvPolynomial.X_mul_cancel_left_iff.mp h)

private theorem nodal_augmentation_quasiIso (k : Type u) [CommRing k] :
    ∃ ε : nodalRingResolution k ⟶ singleModule (PolynomialRing k)
      ((ModuleCat.restrictScalars (nodalRingMap k)).obj
        (ModuleCat.of (NodalRing k) (NodalRing k))), QuasiIso ε :=
  scalarCone_augmentation_quasiIso (xVariable k * yVariable k) (fun p q h =>
    MvPolynomial.X_mul_cancel_left_iff.mp
      (MvPolynomial.X_mul_cancel_left_iff.mp (by simpa only [mul_assoc] using h)))

private theorem nodalRelationIdeal_le_x (k : Type u) [CommRing k] :
    nodalRelationIdeal k ≤ Ideal.span {xVariable k} := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show xVariable k * yVariable k ∈ Ideal.span {xVariable k}
  rw [Ideal.mem_span_singleton]
  exact ⟨yVariable k, rfl⟩

private def xAxisQuotientEquiv (k : Type u) [CommRing k] :
    XAxisModule k ≃+* PolynomialXAxisModule k :=
  (Ideal.quotEquivOfEq (by simp [Ideal.map_span])).trans
    (DoubleQuot.quotQuotEquivQuotOfLE (nodalRelationIdeal_le_x k))

private theorem xAxisQuotientEquiv_mk (k : Type u) [CommRing k]
    (r : PolynomialRing k) :
    xAxisQuotientEquiv k (Ideal.Quotient.mk (xAxisIdeal k) (nodalRingMap k r)) =
      Ideal.Quotient.mk (Ideal.span {xVariable k}) r :=
  DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk r (nodalRelationIdeal_le_x k)

private theorem single_projective {R : Type u} [CommRing R] (n : ℤ) :
    Projective ((singleModule R R).X n) := by
  by_cases hn : n = 0
  · subst n
    exact Projective.of_iso (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).symm inferInstance
  · exact (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) n hn).projective

private theorem scalarCone_projective {R : Type u} [CommRing R] (a : R) (n : ℤ) :
    Projective ((mappingCone (scalarMultiplication R a)).X n) := by
  have := single_projective (R := R) (n+1)
  have := single_projective (R := R) n
  exact Projective.of_iso
    (homotopyCofiber.XIsoBiprod (scalarMultiplication R a) n (n+1) rfl).symm inferInstance

private theorem scalarCone_isStrictlyLE {R : Type u} [CommRing R] (a : R) :
    (mappingCone (scalarMultiplication R a)).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  rw [mappingCone.isZero_X_iff]
  exact ⟨isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) (n+1) (by omega),
    isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) n (by omega)⟩

private theorem scalarCone_kFlat {R : Type u} [CommRing R] (a : R) :
    (mappingCone (scalarMultiplication R a)).KFlat := by
  have := scalarCone_isStrictlyLE a
  have (n : ℤ) : Projective ((mappingCone (scalarMultiplication R a)).X n) :=
    scalarCone_projective a n
  exact _root_.CochainComplex.KFlat.kFlat_of_flat _ 0

private theorem axis_resolution_kFlat (k : Type u) [CommRing k] :
    (xAxisResolution k).KFlat ∧ (nodalRingResolution k).KFlat :=
  ⟨scalarCone_kFlat _, scalarCone_kFlat _⟩

open DerivedCategory in
private theorem exists_quasiIso_of_nonempty_iso {C : Type*} [Category C] [Abelian C]
    (P L : CochainComplex C ℤ) [P.IsKProjective]
    (h : Nonempty (Q.obj P ≅ Q.obj L)) : ∃ f : P ⟶ L, QuasiIso f := by
  obtain ⟨e⟩ := h
  let q := HomotopyCategory.quotient C (.up ℤ)
  let t := quotientCompQhIso C
  obtain ⟨g, hg⟩ := (IsKProjective.Qh_map_bijective P (q.obj L)).surjective
    ((t.app P).hom ≫ e.hom ≫ (t.app L).inv)
  let f := q.preimage g
  have hf : Q.map f = e.hom := by
    have ht := t.hom.naturality f
    dsimp only [Functor.comp_map] at ht
    rw [Functor.map_preimage, hg] at ht
    apply (cancel_epi (t.app P).hom).mp
    simpa using ht.symm
  have : IsIso (Q.map f) := by rw [hf]; infer_instance
  exact ⟨f, (isIso_Q_map_iff_quasiIso C f).mp inferInstance⟩

private def xAxisOrigin (k : Type u) [CommRing k] : XAxisModule k →+* k :=
  (Ideal.Quotient.lift (Ideal.span {xVariable k})
    (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => 0)) (by
      intro r hr
      obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp hr
      simp)).comp (xAxisQuotientEquiv k).toRingHom

private theorem xAxisOrigin_y_smul (k : Type u) [CommRing k] (n : XAxisModule k) :
    xAxisOrigin k (yClass k • n) = 0 := by
  show xAxisOrigin k (Ideal.Quotient.mk (xAxisIdeal k) (yClass k) * n) = 0
  rw [map_mul]
  have h : xAxisOrigin k (Ideal.Quotient.mk (xAxisIdeal k) (yClass k)) = 0 := by
    dsimp only [xAxisOrigin, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [xAxisQuotientEquiv_mk]
    simp
  rw [h, zero_mul]

private theorem not_surjective_on_xCycles (k : Type u) [CommRing k] [Nontrivial k]
    (f : NodalRing k →ₗ[NodalRing k] XAxisModule k) :
    ¬ ∀ n : XAxisModule k, ∃ a : NodalRing k, xClass k * a = 0 ∧ f a = n := by
  intro h
  obtain ⟨a, ha, hfa⟩ := h 1
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ((x_annihilator k a).mp ha)
  have hzero : xAxisOrigin k (f a) = 0 := by
    rw [hb]
    show xAxisOrigin k (f (yClass k • b)) = 0
    rw [map_smul]
    exact xAxisOrigin_y_smul k _
  rw [hfa, map_one] at hzero
  exact one_ne_zero hzero

set_option backward.isDefEq.respectTransparency false in
private def mapSingleConeIso {C : Type u} {D : Type v} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
    {M : C} {N : D} (f : M ⟶ M) (g : N ⟶ N) (e : F.obj M ≅ N)
    (h : e.hom ≫ g = F.map f ≫ e.hom) :
    (F.mapHomologicalComplex (.up ℤ)).obj
        (mappingCone ((singleFunctor C 0).map f)) ≅
      mappingCone ((singleFunctor D 0).map g) := by
  let t := F.mapCochainComplexSingleFunctor 0
  let e' := t.app M ≪≫ (singleFunctor D 0).mapIso e
  refine mappingCone.mapHomologicalComplexIso _ F ≪≫
    homotopyCofiber.mapArrowIso _ _ (fun n => ⟨n-1, by simp⟩)
      (Arrow.isoMk e' e' ?_)
  dsimp only [e', Iso.trans_hom, Functor.mapIso_hom, Arrow.mk_hom]
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_comp, ← Category.assoc]
  simpa only [Category.assoc, Functor.comp_map, Iso.app_hom] using
    congrArg (· ≫ (singleFunctor D 0).map e.hom) (t.hom.naturality f).symm

private theorem extendScalarsRingIso_scalar {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) :
    (φ.extendScalarsRingIso).hom ≫ ModuleCat.ofHom (LinearMap.lsmul S S (φ a)) =
      (ModuleCat.extendScalars φ).map (ModuleCat.ofHom (LinearMap.lsmul R R a)) ≫
        (φ.extendScalarsRingIso).hom := by
  let := φ.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro r
  show φ a * (r • (1 : S)) = (a * r) • (1 : S)
  simp only [Algebra.smul_def, map_mul, mul_one]
  rfl

private def extendScalarsScalarConeIso {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) :
    (CochainComplex.extendScalars φ).obj (mappingCone (scalarMultiplication R a)) ≅
      mappingCone (scalarMultiplication S (φ a)) := by
  letI : (ModuleCat.extendScalars φ).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj φ).isLeftAdjoint
  have : PreservesBinaryBiproducts (ModuleCat.extendScalars φ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (ModuleCat.extendScalars φ).Additive := Functor.additive_of_preservesBinaryBiproducts _
  exact mapSingleConeIso (ModuleCat.extendScalars φ) _ _ (φ.extendScalarsRingIso)
    (extendScalarsRingIso_scalar φ a)

private def tensorScalarConeIso {R : Type u} [CommRing R] (N : ModuleCat.{u} R) (a : R) :
    (tensorLeft ((singleFunctor (ModuleCat R) 0).obj N)).obj
        (mappingCone (scalarMultiplication R a)) ≅
      mappingCone ((singleFunctor (ModuleCat R) 0).map
        (ModuleCat.ofHom (LinearMap.lsmul R N a))) := by
  refine StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso N _ ≪≫
    mapSingleConeIso (tensorLeft N) _ _ (ρ_ N) ?_
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro n r
  change a • (r • n) = (a * r) • n
  rw [mul_smul]

open CategoryTheory.Pretriangulated in
private def zeroConeDerivedIso {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj (mappingCone (0 : K ⟶ K)) ≅
      DerivedCategory.Q.obj (K⟦(1 : ℤ)⟧ ⊞ K) := by
  let T := DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle (0 : K ⟶ K))
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished _
  have hz : T.rotate.mor₃ = 0 := by
    change -(CategoryTheory.shiftFunctor _ (1 : ℤ)).map (DerivedCategory.Q.map (0 : K ⟶ K)) = 0
    simp
  let e := (exists_iso_binaryBiproduct_of_distTriang T.rotate
    (rot_of_distTriang _ hT) hz).choose
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := C)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact e ≪≫ biprod.braiding _ _ ≪≫
    biprod.mapIso ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app K).symm (Iso.refl _) ≪≫
      (DerivedCategory.Q.mapBiprod (K⟦(1 : ℤ)⟧) K).symm

private def tensorRestrictedXAxisWithNodalRingIsoXMultiplication
    (k : Type u) [CommRing k] :
    derivedTensorRestrictedXAxisWithNodalRing k ≅
      DerivedCategory.Q.obj (xMultiplicationComplex k) :=
  DerivedCategory.Q.mapIso (extendScalarsScalarConeIso (nodalRingMap k) (xVariable k))

private def tensorXAxisWithRestrictedNodalRingIsoSplit (k : Type u) [CommRing k] :
    derivedTensorXAxisWithRestrictedNodalRing k ≅
      DerivedCategory.Q.obj (splitXAxisComplex k) := by
  let N := ModuleCat.of (NodalRing k) (XAxisModule k)
  let e := (tensorLeft (singleModule (NodalRing k) (XAxisModule k))).mapIso
      (extendScalarsScalarConeIso (nodalRingMap k) (xVariable k * yVariable k)) ≪≫
    tensorScalarConeIso N (nodalRingMap k (xVariable k * yVariable k))
  have hz : nodalRingMap k (xVariable k * yVariable k) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hf : (singleFunctor (ModuleCat (NodalRing k)) 0).map
      (ModuleCat.ofHom (LinearMap.lsmul (NodalRing k) N
        (nodalRingMap k (xVariable k * yVariable k)))) = 0 := by
    rw [hz]
    simp
  exact DerivedCategory.Q.mapIso (e ≪≫ eqToIso (by rw [hf])) ≪≫
    zeroConeDerivedIso (singleModule (NodalRing k) (XAxisModule k))

private def scalarConeNegOneIso {R : Type u} [CommRing R] (a : R) :
    (mappingCone (scalarMultiplication R a)).X (-1) ≅ ModuleCat.of R R where
  hom := (mappingCone.fst (scalarMultiplication R a)).1.v (-1) 0 (by decide) ≫
    (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).hom
  inv := (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv ≫
    (mappingCone.inl (scalarMultiplication R a)).v 0 (-1) (by decide)
  hom_inv_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hz : (mappingCone.snd (scalarMultiplication R a)).v (-1) (-1) (by decide) = 0 :=
      (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) (-1) (by decide)).eq_of_tgt _ _
    simpa only [hz, zero_comp, add_zero] using
      mappingCone.id_X (scalarMultiplication R a) (-1) 0 (by decide)
  inv_hom_id := by simp

private theorem scalarConeNegOneIso_hom_comp {R : Type u} [CommRing R] (a : R) :
    (scalarConeNegOneIso a).hom ≫ ModuleCat.ofHom (LinearMap.lsmul R R a) =
      (mappingCone (scalarMultiplication R a)).d (-1) 0 ≫
        (mappingCone.snd (scalarMultiplication R a)).v 0 0 (by decide) ≫
          (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).hom := by
  have h := mappingCone.d_snd_v (scalarMultiplication R a) (-1) 0 (by decide)
  simp only [singleFunctor_obj_d, comp_zero, add_zero] at h
  dsimp only [scalarConeNegOneIso]
  rw [← Category.assoc, h]
  simp only [scalarMultiplication, singleFunctor, singleFunctors, single_map_f_self,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem surjective_cycles_to_single {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (N : ModuleCat.{u} R) (j : ℤ)
    (f : P ⟶ (singleFunctor (ModuleCat R) j).obj N)
    [Epi (homologyMap f j)] :
    Function.Surjective ((P.iCycles j ≫ f.f j ≫ (singleObjXSelf (.up ℤ) j N).hom).hom) := by
  have h : P.iCycles j ≫ f.f j ≫ (singleObjXSelf (.up ℤ) j N).hom =
      P.homologyπ j ≫ homologyMap f j ≫ (singleObjHomologySelfIso (.up ℤ) j N).hom := by
    dsimp only [singleFunctor, singleFunctors] at f ⊢
    rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
      singleObjCyclesSelfIso_hom, cyclesMap_i_assoc]
  rw [h]
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem xMultiplication_not_iso_split (k : Type u) [CommRing k]
    [Nontrivial k] : ¬ Nonempty (DerivedCategory.Q.obj (xMultiplicationComplex k) ≅
      DerivedCategory.Q.obj (splitXAxisComplex k)) := by
  intro h
  let P := xMultiplicationComplex k
  let N := ModuleCat.of (NodalRing k) (XAxisModule k)
  let S := (singleFunctor (ModuleCat (NodalRing k)) 0).obj N
  have : P.IsStrictlyLE 0 := scalarCone_isStrictlyLE (xClass k)
  have (n : ℤ) : Projective (P.X n) := scalarCone_projective (xClass k) n
  have : P.IsKProjective := isKProjective_of_projective P 0
  obtain ⟨f, hf⟩ := exists_quasiIso_of_nonempty_iso P (S⟦(1 : ℤ)⟧ ⊞ S) h
  let e : S⟦(1 : ℤ)⟧ ≅ (singleFunctor (ModuleCat (NodalRing k)) (-1)).obj N :=
    ((singleFunctors (ModuleCat (NodalRing k))).shiftIso (1 : ℤ) (-1) 0
    (by decide)).app N
  let g : S⟦(1 : ℤ)⟧ ⊞ S ⟶ (singleFunctor (ModuleCat (NodalRing k)) (-1)).obj N :=
    biprod.fst ≫ e.hom
  let α := f ≫ g
  have : IsSplitEpi g := ⟨⟨e.inv ≫ biprod.inl, by simp [g]⟩⟩
  have : Epi (homologyMap g (-1)) :=
    inferInstanceAs (Epi ((homologyFunctor _ (.up ℤ) (-1)).map g))
  have : Epi (homologyMap α (-1)) := by
    dsimp only [α]
    rw [homologyMap_comp]
    infer_instance
  let i := scalarConeNegOneIso (xClass k)
  let l : ModuleCat.of (NodalRing k) (NodalRing k) ⟶ N :=
    i.inv ≫ α.f (-1) ≫ (singleObjXSelf (.up ℤ) (-1) N).hom
  apply not_surjective_on_xCycles k l.hom
  intro n
  obtain ⟨c, hc⟩ := surjective_cycles_to_single P N (-1) α n
  refine ⟨i.hom ((P.iCycles (-1)) c), ?_, ?_⟩
  · have hz : P.iCycles (-1) ≫ i.hom ≫
        ModuleCat.ofHom (LinearMap.lsmul (NodalRing k) (NodalRing k) (xClass k)) = 0 := by
      dsimp only [i, P, xMultiplicationComplex]
      rw [scalarConeNegOneIso_hom_comp, ← Category.assoc, iCycles_d, zero_comp]
    exact congr($(hz) c)
  · show (P.iCycles (-1) ≫ i.hom ≫ l) c = n
    simpa only [l, Category.assoc, Iso.hom_inv_id_assoc, ModuleCat.hom_comp] using hc

/-- In the example `R = k[x,y]`, `A = R/(xy)`, and `N = R/(x)`, the objects
`N_R ⊗_R^ᴸ A` and `N ⊗_R^ᴸ A_R` of `D(A)` are not isomorphic. The returned data
includes the two displayed K-flat resolutions and augmentations, their quasi-isomorphism
certificates, and the canonical identifications with `A → A` and `N[1] ⊕ N`. -/
@[stacks 08YT, no_expose]
public noncomputable def derivedTensorModuleStructuresDiffer
    (k : Type u) [CommRing k] [Nontrivial k] :
    DerivedTensorComparison k := by
  let e₁ := tensorRestrictedXAxisWithNodalRingIsoXMultiplication k
  let e₂ := tensorXAxisWithRestrictedNodalRingIsoSplit k
  exact
    { xAxisEquiv := xAxisQuotientEquiv k
      xAxisEquiv_mk := xAxisQuotientEquiv_mk k
      nodalRingAugmentation := (nodal_augmentation_quasiIso k).choose
      nodalRingAugmentation_quasiIso := (nodal_augmentation_quasiIso k).choose_spec
      nodalRingResolution_kFlat := (axis_resolution_kFlat k).2
      xAxisAugmentation := (axis_augmentation_quasiIso k).choose
      xAxisAugmentation_quasiIso := (axis_augmentation_quasiIso k).choose_spec
      xAxisResolution_kFlat := (axis_resolution_kFlat k).1
      tensorXAxisWithRestrictedNodalRingIsoSplit := e₂
      tensorRestrictedXAxisWithNodalRingIsoXMultiplication := e₁
      not_iso := fun ⟨e⟩ => xMultiplication_not_iso_split k ⟨e₁.symm ≪≫ e ≪≫ e₂⟩ }

end CochainComplex.DerivedChangeOfRings

end
