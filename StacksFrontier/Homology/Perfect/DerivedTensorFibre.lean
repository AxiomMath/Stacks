module

public import StacksFrontier.Homology.Perfect.FibreCriterion
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensorComparisonLeft

/-!
# The derived fibre of a pseudo-coherent complex is its derived tensor product with `κ(p)`

Let `R` be a commutative ring, `p ⊂ R` a prime ideal and `K` a pseudo-coherent object of `D(R)`.
The derived fibre of `K` at `p` is computed on a bounded-above finite free representative `P` of
`K` by the termwise extension of scalars `P ⊗_R κ(p)`, and this is the shape in which
`StacksDraft.Perfect.FibreCohomologyVanishes` records the vanishing of one of its cohomology
modules. This module identifies that condition with the vanishing of the corresponding cohomology
module of the canonical derived tensor product `K ⊗_R^𝐋 κ(p)[0]` on `D(R)`, and records the
comparison of the two cohomology modules itself, not merely of their vanishing.

## Main results

* `fibreCohomologyVanishes_of_isZero_homology_derivedTensor_single_residueField` (in the
  namespace `StacksDraft.Perfect`): if `H^i(K ⊗_R^𝐋 κ(p)[0])` vanishes in `D(R)` then `K`
  satisfies `StacksDraft.Perfect.FibreCohomologyVanishes p K i`.
* `isZero_homology_derivedTensor_single_residueField_of_fibreCohomologyVanishes` (in the same
  namespace): the converse implication.
* `nonempty_restrictScalars_homology_totalDerivedExtensionScalars_iso_homology_derivedTensor_single_residueField`
  (in the same namespace): the degree-`i` cohomology of the derived fibre taken in `D(κ(p))`,
  restricted along `R → κ(p)`, is isomorphic to the degree-`i` cohomology of `K ⊗_R^𝐋 κ(p)[0]`
  taken in `D(R)`.
* `finrank_homology_totalDerivedExtensionScalars_eq_one_of_nonempty_iso_quotient`,
  `finrank_homology_totalDerivedExtensionScalars_eq_zero_of_isZero` (in the same namespace): for
  a maximal ideal `m` of `A`, `H^i` of the `D(κ(m))`-fibre is one-dimensional over `κ(m)` when
  `H^i(K ⊗_A^𝐋 (A / m)[0])` is `A / m` as an `A`-module, and zero-dimensional when that module
  vanishes.

## Implementation notes

A bounded-above complex of finite free modules is K-flat by [stacks 064K], so
`CochainComplex.DerivedTensor.OneSided.nonempty_comparisonLeft_of_kFlat` computes the derived
tensor product of such a representative with `κ(p)[0]` as the total tensor complex, which
`HomologicalComplex.mapBifunctorSingleRightIso` identifies with `κ(p)` tensored termwise into `P`.
The termwise extension of scalars of `P` to `κ(p)`, restricted back along `R → κ(p)`, is that
complex.

Only the case in which the ring and the modules live in the same universe is treated.

## References

* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 068U](https://stacks.math.columbia.edu/tag/068U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-- An `A`-algebra `B`, viewed as an `A`-module, is the restriction of scalars along
`algebraMap A B` of `B` viewed as a module over itself. -/
private def algebraRestrictScalarsIso (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat.of A B ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) :=
  LinearEquiv.toModuleIso
    (m₂ := ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)).isModule)
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => Algebra.smul_def r x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Restricting the base change `S ⊗_R -` back along `algebraMap R S` is tensoring with `S`
viewed as an `R`-module. -/
private def extendRestrictScalarsTensorIso {R : Type u} [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] :
    ModuleCat.extendScalars (algebraMap R S) ⋙ ModuleCat.restrictScalars (algebraMap R S) ≅
      (curriedTensor (ModuleCat.{u} R)).obj (ModuleCat.of R S) :=
  (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      ModuleCat.extendScalars (algebraMap R S) ⋙
          ModuleCat.restrictScalars (algebraMap R S) ≅
        (curriedTensor (ModuleCat.{u} R)).obj
          ((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S))) ≪≫
    (curriedTensor (ModuleCat.{u} R)).mapIso (algebraRestrictScalarsIso R S).symm

/-- The termwise extension of scalars of `P` to `S`, restricted back along `algebraMap R S`, is
the complex obtained by tensoring `S` termwise into `P`. -/
private def extendRestrictScalarsComplexIso {R : Type u} [CommRing R] (S : Type u) [CommRing S]
    [Algebra R S] (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
      (((curriedTensor (ModuleCat.{u} R)).obj (ModuleCat.of R S)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P :=
  (NatIso.mapHomologicalComplex (extendRestrictScalarsTensorIso S) (ComplexShape.up ℤ)).app P

/-- Restriction of scalars neither creates nor destroys the vanishing of a cohomology module of
a cochain complex. -/
private theorem isZero_homology_mapRestrictScalars_iff {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (X : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    IsZero ((((ModuleCat.restrictScalars f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X).homology i) ↔
      IsZero (X.homology i) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl

/-- A bounded-above complex of finite free modules is K-flat. -/
private theorem kFlat_of_isBoundedAboveFiniteFree {R : Type u} [CommRing R]
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P) :
    CochainComplex.KFlat.{u, u} P := by
  obtain ⟨b, hb⟩ := hP.upperBound
  have (n : ℤ) : Module.Flat R (P.X n) :=
    have := (hP.finiteFree n).2
    Module.Flat.of_free
  exact CochainComplex.KFlat.kFlat_of_flat.{u, u} P b

/-- The derived tensor product of a K-flat complex `P` with a module placed in degree zero is
isomorphic to the complex obtained by tensoring that module termwise into `P`. -/
private theorem nonempty_derivedTensor_single_iso_tensorComplex {R : Type u} [CommRing R]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (N : ModuleCat.{u} R) :
    Nonempty ((T.tensor.obj (DerivedCategory.Q.obj P)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ≅
        DerivedCategory.Q.obj
          ((((curriedTensor (ModuleCat.{u} R)).obj N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) := by
  refine (CochainComplex.DerivedTensor.OneSided.nonempty_comparisonLeft_of_kFlat T P
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) hP).map fun e => ?_
  exact (T.tensor.obj (DerivedCategory.Q.obj P)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app N) ≪≫ e ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.mapBifunctorSingleRightIso (curriedTensor (ModuleCat.{u} R)) P N ≪≫
        (NatIso.mapHomologicalComplex
          ((BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} R)).app N).symm
          (ComplexShape.up ℤ)).app P)

/-- For a bounded-above finite free representative `P` of `K`, the degree-`i` cohomology of
`K ⊗_R^𝐋 κ(p)[0]` in `D(R)` is the cohomology of the termwise extension of scalars of `P` to
`κ(p)`, restricted back along `R → κ(p)`. -/
private def homologyDerivedTensorIsoRestrictScalarsHomology {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (K : DerivedCategory (ModuleCat.{u} R))
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree P)
    (e : DerivedCategory.Q.obj P ≅ K) (i : ℤ) :
    (((ModuleCat.restrictScalars (algebraMap R p.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (residueFieldComplex.{u, u} p P)).homology i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R p.ResidueField))) :=
  have e₂ := (nonempty_derivedTensor_single_iso_tensorComplex
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) P
    (kFlat_of_isBoundedAboveFiniteFree hP) (ModuleCat.of R p.ResidueField)).some
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) i).mapIso
      (extendRestrictScalarsComplexIso p.ResidueField P) ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (e₂.symm ≪≫ Iso.app
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.mapIso e) _)

/-- Let `R` be a commutative ring, `p` a prime of `R`, `K` a pseudo-coherent object of `D(R)` and
`i` an integer. If the degree-`i` cohomology of the canonical derived tensor product
`K ⊗_R^𝐋 κ(p)[0]` vanishes, then `K` satisfies the derived-fibre vanishing condition
`StacksDraft.Perfect.FibreCohomologyVanishes p K i`. -/
public theorem fibreCohomologyVanishes_of_isZero_homology_derivedTensor_single_residueField
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R p.ResidueField))))) :
    FibreCohomologyVanishes.{u, u} p K i := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  refine ⟨P, hP, ⟨e⟩, ?_⟩
  rw [← isZero_homology_mapRestrictScalars_iff (algebraMap R p.ResidueField)
    (residueFieldComplex.{u, u} p P) i]
  exact h.of_iso (homologyDerivedTensorIsoRestrictScalarsHomology p K P hP e i)

/-- The converse of
`fibreCohomologyVanishes_of_isZero_homology_derivedTensor_single_residueField`: the
derived-fibre vanishing condition `StacksDraft.Perfect.FibreCohomologyVanishes p K i` implies
that the degree-`i` cohomology of the canonical derived tensor product `K ⊗_R^𝐋 κ(p)[0]`
vanishes. -/
public theorem isZero_homology_derivedTensor_single_residueField_of_fibreCohomologyVanishes
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ)
    (h : FibreCohomologyVanishes.{u, u} p K i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R p.ResidueField)))) := by
  obtain ⟨P, hP, ⟨e⟩, hzero⟩ := h
  rw [← isZero_homology_mapRestrictScalars_iff (algebraMap R p.ResidueField)
    (residueFieldComplex.{u, u} p P) i] at hzero
  exact hzero.of_iso (homologyDerivedTensorIsoRestrictScalarsHomology p K P hP e i).symm

/-- For a pseudo-coherent object `K` of `D(R)` and a prime `p`, the degree-`i` cohomology of the
derived fibre `K ⊗_R^𝐋 κ(p)` taken in `D(κ(p))`, the derived extension of scalars
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, restricted along
`R → κ(p)` is isomorphic to the degree-`i` cohomology of the derived tensor product
`K ⊗_R^𝐋 κ(p)[0]` taken in `D(R)`. -/
public theorem nonempty_restrictScalars_homology_totalDerivedExtensionScalars_iso_homology_derivedTensor_single_residueField
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) :
    Nonempty ((ModuleCat.restrictScalars (algebraMap R p.ResidueField)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) i).obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap R p.ResidueField)).functor.obj K)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
            (ModuleCat.of R p.ResidueField)))) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hP.upperBound
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R p.ResidueField)
  let F := ModuleCat.restrictScalars.{u} (algebraMap R p.ResidueField)
  have hPle : P.IsStrictlyLE b := hb
  have (j : ℤ) : Module.Free R (P.X j) := (hP.finiteFree j).2
  have (j : ℤ) : Module.Projective R (P.X j) := inferInstance
  have : ∀ j, Projective (P.X j) := fun j => ModuleCat.projective_of_categoryTheory_projective _
  have hc : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  have eA : (residueFieldComplex.{u, u} p P).homology i ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) i).obj
        (D.functor.obj K) :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} p.ResidueField) i).app
        (residueFieldComplex.{u, u} p P)).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) i).mapIso
        ((@asIso _ _ _ _ (D.comparison.app P) hc).symm ≪≫ D.functor.mapIso e)
  have eC : (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (residueFieldComplex.{u, u} p P)).homology i) ≅
      F.obj ((residueFieldComplex.{u, u} p P).homology i) :=
    ShortComplex.mapHomologyIso ((residueFieldComplex.{u, u} p P).sc i) F
  exact ⟨(F.mapIso eA).symm ≪≫ eC.symm ≪≫
    homologyDerivedTensorIsoRestrictScalarsHomology p K P hP e i⟩

/-- An isomorphism between the restrictions of scalars of two `κ`-modules along a surjective
`A → κ` is a `κ`-linear equivalence. -/
private def linearEquivOfRestrictScalarsIso {A κ : Type u} [CommRing A] [CommRing κ]
    (f : A →+* κ) (hf : Function.Surjective f) (X Y : ModuleCat.{u} κ)
    (e : (ModuleCat.restrictScalars f).obj X ≅ (ModuleCat.restrictScalars f).obj Y) :
    X ≃ₗ[κ] Y :=
  let g := e.toLinearEquiv
  { toFun := g
    map_add' := g.map_add
    map_smul' := by
      intro c x
      obtain ⟨a, rfl⟩ := hf c
      exact g.map_smul a x
    invFun := g.symm
    left_inv := g.left_inv
    right_inv := g.right_inv }

/-- A `κ`-module whose restriction of scalars along `A → κ` is a zero object has `κ`-dimension
zero. -/
private theorem finrank_eq_zero_of_isZero_restrictScalars {A κ : Type u} [CommRing A]
    [CommRing κ] [Nontrivial κ] (f : A →+* κ) (X : ModuleCat.{u} κ)
    (h : IsZero ((ModuleCat.restrictScalars f).obj X)) :
    Module.finrank κ X = 0 := by
  have hs := ModuleCat.subsingleton_of_isZero h
  have : Subsingleton X := ⟨fun a b => @Subsingleton.allEq _ hs a b⟩
  exact Module.finrank_zero_of_subsingleton

/-- For a maximal ideal `m` of `A`, the quotient `A / m` and the residue field `κ(m)` are
isomorphic as `A`-modules. -/
private def quotientIsoResidueField {A : Type u} [CommRing A] (m : Ideal A) [m.IsMaximal] :
    ModuleCat.of A (A ⧸ m) ≅ ModuleCat.of A m.ResidueField :=
  LinearEquiv.toModuleIso
    (LinearEquiv.ofBijective
      (IsScalarTower.toAlgHom A (A ⧸ m) m.ResidueField).toLinearMap
      m.bijective_algebraMap_quotient_residueField)

/-- For a maximal ideal `m` of `A`, the degree-`i` cohomology modules of `K ⊗_A^𝐋 (A / m)[0]` and
of `K ⊗_A^𝐋 κ(m)[0]` are isomorphic as `A`-modules. -/
private def homologyDerivedTensorQuotientIsoResidueField {A : Type u} [CommRing A] (m : Ideal A)
    [m.IsMaximal] (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (A ⧸ m)))) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A m.ResidueField))) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso (quotientIsoResidueField m)))

/-- Let `m` be a maximal ideal of `A` and `K` a pseudo-coherent object of `D(A)`. If
`H^i(K ⊗_A^𝐋 (A / m)[0])` is `A / m` as an `A`-module, then the degree-`i` cohomology of the
derived fibre of `K` at `m`, taken in `D(κ(m))`, is one-dimensional over `κ(m)`. -/
public theorem finrank_homology_totalDerivedExtensionScalars_eq_one_of_nonempty_iso_quotient
    {A : Type u} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (h : Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (A ⧸ m)))) ≅ ModuleCat.of A (A ⧸ m))) :
    Module.finrank m.ResidueField
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A m.ResidueField)).functor.obj K)) = 1 := by
  obtain ⟨h⟩ := h
  obtain ⟨eFib⟩ :=
    nonempty_restrictScalars_homology_totalDerivedExtensionScalars_iso_homology_derivedTensor_single_residueField
      m K hK i
  have e : (ModuleCat.restrictScalars (algebraMap A m.ResidueField)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap A m.ResidueField)).functor.obj K)) ≅
      (ModuleCat.restrictScalars (algebraMap A m.ResidueField)).obj
        (ModuleCat.of m.ResidueField m.ResidueField) :=
    eFib ≪≫ (homologyDerivedTensorQuotientIsoResidueField m K i).symm ≪≫ h ≪≫
      quotientIsoResidueField m ≪≫ algebraRestrictScalarsIso A m.ResidueField
  have : (DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A m.ResidueField)).functor.obj K) ≃ₗ[m.ResidueField] m.ResidueField :=
    linearEquivOfRestrictScalarsIso (algebraMap A m.ResidueField)
      m.algebraMap_residueField_surjective _ _ e
  rw [this.finrank_eq, Module.finrank_self]

/-- Let `m` be a maximal ideal of `A` and `K` a pseudo-coherent object of `D(A)`. If
`H^i(K ⊗_A^𝐋 (A / m)[0])` vanishes, then the degree-`i` cohomology of the derived fibre of `K`
at `m`, taken in `D(κ(m))`, is zero-dimensional over `κ(m)`. -/
public theorem finrank_homology_totalDerivedExtensionScalars_eq_zero_of_isZero
    {A : Type u} [CommRing A] (m : Ideal A) [m.IsMaximal]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (A ⧸ m)))))) :
    Module.finrank m.ResidueField
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} m.ResidueField) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A m.ResidueField)).functor.obj K)) = 0 := by
  obtain ⟨eFib⟩ :=
    nonempty_restrictScalars_homology_totalDerivedExtensionScalars_iso_homology_derivedTensor_single_residueField
      m K hK i
  have hz := (h.of_iso (homologyDerivedTensorQuotientIsoResidueField m K i).symm).of_iso eFib
  exact finrank_eq_zero_of_isZero_restrictScalars (algebraMap A m.ResidueField) _ hz

end StacksDraft.Perfect

end
