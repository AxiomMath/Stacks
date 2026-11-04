module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionTensorBaseChange
public import StacksFrontier.Deformation.ToposThickening.CurvatureBaseChange

/-!
# Base change of the canonical obstruction map

Let `fR : R' → R` and `fS : S' → S` be surjections of commutative rings with square-zero
kernels `I` and `J`, fitting into a commuting square with `a : R' → S'` and `b : R → S`, and
let `K` be a bounded-above object of `D(R)`. Derived base change `β = - ⊗ᴸ_R S` carries the
canonical obstruction morphism `ω_K : K ⟶ (K ⊗ᴸ_R I/I²)[2]` of `K` to the canonical obstruction
morphism of `β K`, read through a canonical comparison
`β(K ⊗ᴸ_R I/I²) ⟶ (β K) ⊗ᴸ_S J/J²` of the two targets.

This is part (3) of Stacks 0DYR. The curvature chain maps of a free differential lift and of
its base change agree (`LiftedDifferentialCurvature.hom_baseChange`), and derived base change
carries the derived tensor comparison of the lift to that of its base change
(`LiftedDifferentialCurvature.tensorComparison_baseChange`); the passage from the cochain level
to the derived category uses the compatibility of the comparison `β ∘ Q ⟶ Q ∘ (S ⊗_R -)` with
the translation functors.

## Main definitions

* `Deformation.Obstruction.baseChangeRepresentativeIso`: a K-flat free representative `P` of `K`
  base-changes to a representative `S ⊗_R P` of `β K`.
* `Deformation.Obstruction.obstructionTargetBaseChangeMap`: the comparison
  `β(K ⊗ᴸ_R I/I²) ⟶ (β K) ⊗ᴸ_S J/J²` computed through such a representative and a K-flat
  resolution of `I/I²`.

## Main results

* `Deformation.Obstruction.canonicalObstructionMap_baseChange`: **Stacks 0DYR(3)**, the base
  change of the canonical obstruction morphism of `K` is the canonical obstruction morphism of
  `β K`.
* `Deformation.Obstruction.isCanonicalObstructionMap_baseChange`: the same statement for any
  pair of morphisms satisfying the lifted-differential characterization.
* `Deformation.Obstruction.isIso_obstructionTargetBaseChangeMap`: the comparison of the two
  targets is an isomorphism when `a` and `b` are flat and `J = I · S'`.
* `Deformation.Obstruction.exists_isIso_obstructionTargetBaseChange`: consequently the two
  obstruction morphisms correspond under an isomorphism of their targets, with no choice of
  representative in the statement.

## Implementation notes

The square needs no flatness and no cartesian hypothesis on the kernels: the identity of the
two obstruction morphisms holds for any commuting square of four rings whose two vertical maps
are surjective, so it is available at a localization square `R' → (R')_g`. Flatness of
`a : R' → S'` and of `b : R → S` together with `J = I · S'` enter only to make the comparison of
the targets an isomorphism. Flatness of `S` over `R` alone does not suffice, even for a
cartesian square: see `Deformation.Obstruction.BaseFlatNotEnough.not_injective`.

The comparison of the targets depends on the chosen representative and resolution, which is why
it appears as an argument of the main statement rather than as a canonical morphism; the
obstruction morphisms themselves do not, being characterized uniquely by
`Deformation.Obstruction.existsUnique_isCanonicalObstructionMap`.

## References

* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars CochainComplex.DerivedExtensionScalars
  CochainComplex.DerivedTensor
open StacksDraft.TorAmplitude
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Deformation.Obstruction

attribute [local instance] extendScalars_additive

variable {R' R S' S : Type u} [CommRing R'] [CommRing R] [CommRing S'] [CommRing S]
  (fR : R' →+* R) (hfR : Function.Surjective fR)
  (fS : S' →+* S) (hfS : Function.Surjective fS)
  (a : R' →+* S') (b : R →+* S) (hcomm : b.comp fR = fS.comp a)

/-! ### Base change of a free representative -/

/-- If every term of `P` is a free `R`-module, every term of its base change `S ⊗_R P` is a free
`S`-module. -/
lemma free_mapCochainComplex (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ n, Module.Free R (P.X n)) (n : ℤ) :
    Module.Free S (((mapCochainComplex b).obj P).X n) := by
  have := hfree n
  let : Algebra R S := b.toAlgebra
  exact Module.Free.of_basis
    (Algebra.TensorProduct.basis S (Module.Free.chooseBasis R (P.X n)))

/-- The base change `S ⊗_R P` of a complex `P` concentrated in degrees `≤ m` is concentrated in
degrees `≤ m`. -/
lemma isStrictlyLE_mapCochainComplex (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    [P.IsStrictlyLE m] : ((mapCochainComplex b).obj P).IsStrictlyLE m := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Functor.map_isZero (ModuleCat.extendScalars.{u, u, u} b)
    (P.isZero_of_isStrictlyLE m i hi)

/-- Derived base change of the square of a lifted differential is the square of the
base-changed lifted differential. -/
private lemma derivedCurvature_baseChange
    {P : CochainComplex (ModuleCat.{u} R) ℤ} {L : FreeDifferentialLift fR P}
    (c : LiftedDifferentialCurvature fR hfR P L)
    (cS : LiftedDifferentialCurvature fS hfS ((mapCochainComplex b).obj P)
      (L.baseChange hfR hfS a b hcomm))
    {V : DerivedCategory (ModuleCat.{u} R)} {W : DerivedCategory (ModuleCat.{u} S)}
    (gR : DerivedCategory.Q.obj (P ⊗ kernelComplex fR hfR) ⟶ V)
    (gS : DerivedCategory.Q.obj ((mapCochainComplex b).obj P ⊗ kernelComplex fS hfS) ⟶ W)
    (Θ : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj V ⟶ W)
    (htail : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map gR ≫ Θ =
      (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app
          (P ⊗ kernelComplex fR hfR) ≫
        DerivedCategory.Q.map (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P) ≫ gS) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
        (DerivedCategory.Q.map c.hom ≫
          (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (P ⊗ kernelComplex fR hfR) ≫
          (shiftFunctor (DerivedCategory (ModuleCat.{u} R)) (2 : ℤ)).map gR) ≫
      ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.commShiftIso (2 : ℤ)).hom.app V ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ)).map Θ =
      (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app P ≫
        DerivedCategory.Q.map cS.hom ≫
        (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
          ((mapCochainComplex b).obj P ⊗ kernelComplex fS hfS) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ)).map gS := by
  have hcomp : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
        ((DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (P ⊗ kernelComplex fR hfR)) ≫
      ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.commShiftIso (2 : ℤ)).hom.app
        (DerivedCategory.Q.obj (P ⊗ kernelComplex fR hfR)) =
      ((DerivedCategory.Q ⋙
          (derivedExtensionScalarsGeneral.{u, u, u} b).functor).commShiftIso (2 : ℤ)).hom.app
        (P ⊗ kernelComplex fR hfR) :=
    (Functor.CommShift.comp_commShiftIso_hom_app DerivedCategory.Q
      (derivedExtensionScalarsGeneral.{u, u, u} b).functor (2 : ℤ)
      (P ⊗ kernelComplex fR hfR)).symm
  have hnat : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
        (DerivedCategory.Q.map c.hom) ≫
      (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app
        ((shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (2 : ℤ)).obj
          (P ⊗ kernelComplex fR hfR)) =
      (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app P ≫
        DerivedCategory.Q.map ((mapCochainComplex b).map c.hom) :=
    (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.naturality c.hom
  have hEcs : ((extensionOfScalarsComplexGeneral.{u, u, u} b).commShiftIso (2 : ℤ)).hom.app
        (P ⊗ kernelComplex fR hfR) =
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, u} b).mapCochainComplexShiftIso (2 : ℤ)).hom.app
          (P ⊗ kernelComplex fR hfR)) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        ((mapCochainComplex b).obj (P ⊗ kernelComplex fR hfR)) :=
    extensionOfScalarsComplexGeneral_commShiftIso_hom_app.{u, u, u} b (2 : ℤ)
      (P ⊗ kernelComplex fR hfR)
  have hnatR := reassoc_of% hnat
  have hEcsR := reassoc_of% hEcs
  have hQ : DerivedCategory.Q.map ((mapCochainComplex b).map c.hom) ≫
      DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, u} b).mapCochainComplexShiftIso (2 : ℤ)).hom.app
            (P ⊗ kernelComplex fR hfR)) ≫
        (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
          ((mapCochainComplex b).obj (P ⊗ kernelComplex fR hfR)) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ)).map
          (DerivedCategory.Q.map (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P) ≫ gS) =
      DerivedCategory.Q.map cS.hom ≫
        (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
          ((mapCochainComplex b).obj P ⊗ kernelComplex fS hfS) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ)).map gS := by
    rw [CategoryTheory.Functor.map_comp
        (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ))
        (DerivedCategory.Q.map (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P)) gS,
      ← Functor.commShiftIso_hom_naturality_assoc _
        (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P) (2 : ℤ),
      ← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Category.assoc, ← c.hom_baseChange fR hfR fS hfS a b hcomm L cS]
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
    Category.assoc, Functor.commShiftIso_hom_naturality_assoc _ gR (2 : ℤ),
    ← CategoryTheory.Functor.map_comp
      (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ))
      ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.map gR) Θ,
    htail, reassoc_of% hcomp,
    CategoryTheory.Functor.map_comp
      (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ))
      ((derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app (P ⊗ kernelComplex fR hfR))
      (DerivedCategory.Q.map (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P) ≫ gS),
    NatTrans.shift_app_comm_assoc (derivedExtensionScalarsGeneral.{u, u, u} b).comparison
      (2 : ℤ) (P ⊗ kernelComplex fR hfR),
    hnatR, hEcsR]
  refine Eq.trans ?_ ((derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app P ≫= hQ)
  exact (Category.assoc _ _ _).trans (_ ≫= (_ ≫= Category.assoc _ _ _))

/-- A K-flat free representative of `K` base-changes to a representative of its base change. -/
noncomputable def baseChangeRepresentativeIso
    {K : DerivedCategory (ModuleCat.{u} R)}
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (e : DerivedCategory.Q.obj P ≅ K) :
    DerivedCategory.Q.obj ((mapCochainComplex b).obj P) ≅
      (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K :=
  (kFlatComparisonIso b P hP).symm ≪≫
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.mapIso e

/-- The inverse of `baseChangeRepresentativeIso` is the image of `e.inv` under derived base change
followed by the comparison `β (Q P) ⟶ Q (S ⊗_R P)`. -/
lemma baseChangeRepresentativeIso_inv
    {K : DerivedCategory (ModuleCat.{u} R)}
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (e : DerivedCategory.Q.obj P ≅ K) :
    (baseChangeRepresentativeIso b P hP e).inv =
      (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map e.inv ≫
        (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app P := rfl

/-- The comparison carrying the base change of the obstruction target to the obstruction
target of the base change. -/
noncomputable def obstructionTargetBaseChangeMap
    {K : DerivedCategory (ModuleCat.{u} R)}
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (e : DerivedCategory.Q.obj P ≅ K)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hQq : IsIso (DerivedCategory.Q.map q)) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj
        (((canonicalDerivedTensorProductFunctor R).obj K).obj (squareZeroKernelObject fR hfR)) ⟶
      ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K)).obj
        (squareZeroKernelObject fS hfS) :=
  (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
      (((canonicalDerivedTensorProductFunctor R).map e.inv).app
        (squareZeroKernelObject fR hfR)) ≫
    tensorComparisonBaseChangeMap fR hfR fS hfS a b hcomm P hP T hT q hQq ≫
    ((canonicalDerivedTensorProductFunctor S).map
        (baseChangeRepresentativeIso b P hP e).hom).app (squareZeroKernelObject fS hfS)

/-- Derived base change along `b` carries any morphism `ωR` satisfying the lifted-differential
characterization of the canonical obstruction morphism of `K` for `fR` to any such morphism `ωS`
of `β K` for `fS`, read through `obstructionTargetBaseChangeMap`. -/
theorem isCanonicalObstructionMap_baseChange
    {K : DerivedCategory (ModuleCat.{u} R)}
    {ωR : K ⟶ (((canonicalDerivedTensorProductFunctor R).obj K).obj
      (squareZeroKernelObject fR hfR))⟦(2 : ℤ)⟧}
    (hωR : IsCanonicalObstructionMap fR hfR K ωR)
    {ωS : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K ⟶
      (((canonicalDerivedTensorProductFunctor S).obj
        ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K)).obj
          (squareZeroKernelObject fS hfS))⟦(2 : ℤ)⟧}
    (hωS : IsCanonicalObstructionMap fS hfS
      ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K) ωS)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (hPLE : P.IsStrictlyLE m)
    (hfree : ∀ n, Module.Free R (P.X n)) (hP : P.KFlat)
    (e : DerivedCategory.Q.obj P ≅ K)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℤ) (hTLE : T.IsStrictlyLE k)
    (hTproj : ∀ i, Projective (T.X i)) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hq : QuasiIso q)
    (hQq : IsIso (DerivedCategory.Q.map q)) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map ωR ≫
        ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.commShiftIso (2 : ℤ)).hom.app
          (((canonicalDerivedTensorProductFunctor R).obj K).obj
            (squareZeroKernelObject fR hfR)) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ)).map
          (obstructionTargetBaseChangeMap fR hfR fS hfS a b hcomm P hP e T hT q hQq) =
      ωS := by
  have := hPLE
  have hfreeS : ∀ n, Module.Free S (((mapCochainComplex b).obj P).X n) :=
    free_mapCochainComplex b P hfree
  have hPSLE : ((mapCochainComplex b).obj P).IsStrictlyLE m :=
    isStrictlyLE_mapCochainComplex b P m
  obtain ⟨L⟩ := hωR.exists_lift P hfree
  obtain ⟨c⟩ := hωR.exists_curvature P m hPLE hfree L
  obtain ⟨cS⟩ := hωS.exists_curvature ((mapCochainComplex b).obj P) m hPSLE hfreeS
    (L.baseChange hfR hfS a b hcomm)
  rw [show hP = c.isKFlat from rfl]
  rw [hωR.eq_curvature P m hPLE hfree e L c,
    hωS.eq_curvature ((mapCochainComplex b).obj P) m hPSLE hfreeS
      (baseChangeRepresentativeIso b P c.isKFlat e) (L.baseChange hfR hfS a b hcomm) cS]
  dsimp only [LiftedDifferentialCurvature.toDerived]
  set gR := c.tensorComparison ≫
    ((canonicalDerivedTensorProductFunctor R).map e.hom).app
      (squareZeroKernelObject fR hfR) with hgR
  set gS := cS.tensorComparison ≫
    ((canonicalDerivedTensorProductFunctor S).map
      (baseChangeRepresentativeIso b P c.isKFlat e).hom).app
      (squareZeroKernelObject fS hfS) with hgS
  have hcancel : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
        (((canonicalDerivedTensorProductFunctor R).map e.hom).app
          (squareZeroKernelObject fR hfR)) ≫
      (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
        (((canonicalDerivedTensorProductFunctor R).map e.inv).app
          (squareZeroKernelObject fR hfR)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← NatTrans.comp_app,
      ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
      NatTrans.id_app, CategoryTheory.Functor.map_id]
  have htail : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map gR ≫
      obstructionTargetBaseChangeMap fR hfR fS hfS a b hcomm P c.isKFlat e T hT q hQq =
      (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app
          (P ⊗ kernelComplex fR hfR) ≫
        DerivedCategory.Q.map (kernelTensorBaseChangeMap fR hfR fS hfS a b hcomm P) ≫ gS := by
    rw [hgR, hgS, obstructionTargetBaseChangeMap, CategoryTheory.Functor.map_comp,
      Category.assoc, reassoc_of% hcancel,
      reassoc_of% (c.tensorComparison_baseChange fR hfR fS hfS a b hcomm cS T k hTLE hTproj hT
        q hq hQq)]
    exact (derivedExtensionScalarsGeneral.{u, u, u} b).comparison.app
      (P ⊗ kernelComplex fR hfR) ≫= Category.assoc _ _ _
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    derivedCurvature_baseChange fR hfR fS hfS a b hcomm c cS gR gS _ htail,
    baseChangeRepresentativeIso_inv]
  exact (Category.assoc _ _ _).symm


/-! ### The comparison of the two targets is an isomorphism -/

/-- For flat `a` and `b` and `J = I · S'` the comparison of the two obstruction targets is an
isomorphism: so are the comparison of the derived tensor products and the two functorial
transports by the representative. -/
theorem isIso_obstructionTargetBaseChangeMap
    (hJ : RingHom.ker fS = Ideal.map a (RingHom.ker fR)) (ha : a.Flat) (hb : b.Flat)
    {K : DerivedCategory (ModuleCat.{u} R)}
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (e : DerivedCategory.Q.obj P ≅ K)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hq : QuasiIso q)
    (hQq : IsIso (DerivedCategory.Q.map q)) :
    IsIso (obstructionTargetBaseChangeMap fR hfR fS hfS a b hcomm P hP e T hT q hQq) := by
  have := hQq
  have := isIso_tensorComparisonBaseChangeMap fR hfR fS hfS a b hcomm hJ ha hb P hP T hT q hq hQq
  rw [obstructionTargetBaseChangeMap]
  infer_instance

/-! ### Part (3) of Stacks 0DYR -/

/-- A square-zero kernel stays square-zero after base change along a cartesian square: the
kernel of `fS` is generated by the image of the kernel of `fR`. -/
lemma ker_sq_eq_bot_baseChange
    (hJ : RingHom.ker fS = Ideal.map a (RingHom.ker fR))
    (hI : RingHom.ker fR ^ 2 = ⊥) : RingHom.ker fS ^ 2 = ⊥ := by
  rw [hJ, ← Ideal.map_pow, hI, Ideal.map_bot]

/-- **The canonical obstruction morphism is compatible with base change.** Derived base change
along `b` carries the canonical obstruction morphism of a bounded-above `K` for the square-zero
surjection `fR` to the canonical obstruction morphism of its base change for `fS`, read through
the comparison of the two targets attached to a bounded-above free K-flat representative `P` of
`K` and a K-flat resolution `q` of `I/I²`. -/
@[stacks 0DYR "part (3)"]
theorem canonicalObstructionMap_baseChange
    (hI : RingHom.ker fR ^ 2 = ⊥)
    (hJ : RingHom.ker fS = Ideal.map a (RingHom.ker fR))
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (hPLE : P.IsStrictlyLE m)
    (hfree : ∀ n, Module.Free R (P.X n)) (hP : P.KFlat)
    (e : DerivedCategory.Q.obj P ≅ K)
    (T : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℤ) (hTLE : T.IsStrictlyLE k)
    (hTproj : ∀ i, Projective (T.X i)) (hT : T.KFlat)
    (q : T ⟶ kernelComplex fR hfR) (hq : QuasiIso q)
    (hQq : IsIso (DerivedCategory.Q.map q)) :
    (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map
        (canonicalObstructionMap fR hfR hI K hK).1 ≫
      ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.commShiftIso (2 : ℤ)).hom.app
          (((canonicalDerivedTensorProductFunctor R).obj K).obj
            (squareZeroKernelObject fR hfR)) ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ)).map
          (obstructionTargetBaseChangeMap fR hfR fS hfS a b hcomm P hP e T hT q hQq) =
      (canonicalObstructionMap fS hfS (ker_sq_eq_bot_baseChange fR fS a hJ hI)
        ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K)
        ((derivedExtensionScalarsGeneral.{u, u, u} b).maps_boundedAbove ⟨K, hK⟩)).1 :=
  isCanonicalObstructionMap_baseChange fR hfR fS hfS a b hcomm
    (canonicalObstructionMap fR hfR hI K hK).2
    (canonicalObstructionMap fS hfS (ker_sq_eq_bot_baseChange fR fS a hJ hI)
      ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K)
      ((derivedExtensionScalarsGeneral.{u, u, u} b).maps_boundedAbove ⟨K, hK⟩)).2
    P m hPLE hfree hP e T k hTLE hTproj hT q hq hQq

include hcomm in
/-- Part (3) of Stacks 0DYR with no choice of representative in the statement: the base change
of the canonical obstruction morphism is the canonical obstruction morphism of the base change,
under an isomorphism of their targets. -/
theorem exists_isIso_obstructionTargetBaseChange
    (hJ : RingHom.ker fS = Ideal.map a (RingHom.ker fR)) (ha : a.Flat) (hb : b.Flat)
    {K : DerivedCategory (ModuleCat.{u} R)}
    {ωR : K ⟶ (((canonicalDerivedTensorProductFunctor R).obj K).obj
      (squareZeroKernelObject fR hfR))⟦(2 : ℤ)⟧}
    (hωR : IsCanonicalObstructionMap fR hfR K ωR)
    {ωS : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K ⟶
      (((canonicalDerivedTensorProductFunctor S).obj
        ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K)).obj
          (squareZeroKernelObject fS hfS))⟦(2 : ℤ)⟧}
    (hωS : IsCanonicalObstructionMap fS hfS
      ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K) ωS) :
    ∃ Θ : (derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj
        (((canonicalDerivedTensorProductFunctor R).obj K).obj
          (squareZeroKernelObject fR hfR)) ⟶
      ((canonicalDerivedTensorProductFunctor S).obj
          ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.obj K)).obj
        (squareZeroKernelObject fS hfS),
      IsIso Θ ∧
        (derivedExtensionScalarsGeneral.{u, u, u} b).functor.map ωR ≫
            ((derivedExtensionScalarsGeneral.{u, u, u} b).functor.commShiftIso (2 : ℤ)).hom.app
              (((canonicalDerivedTensorProductFunctor R).obj K).obj
                (squareZeroKernelObject fR hfR)) ≫
            (shiftFunctor (DerivedCategory (ModuleCat.{u} S)) (2 : ℤ)).map Θ =
          ωS := by
  obtain ⟨P, m, hPLE, hfree, ⟨e⟩⟩ := hωR.exists_free_representative
  have := hPLE
  have hproj : ∀ n, Projective (P.X n) := fun n => by
    have := hfree n
    infer_instance
  have hP : P.KFlat := kFlat_of_isStrictlyLE_projective P m hproj
  obtain ⟨T, k, q, hTLE, hTproj, hq⟩ := exists_projective_kernelComplex_resolution fR hfR
  have := hTLE
  have := hq
  have hT : T.KFlat := kFlat_of_isStrictlyLE_projective T k hTproj
  have hQq : IsIso (DerivedCategory.Q.map q) := inferInstance
  exact ⟨obstructionTargetBaseChangeMap fR hfR fS hfS a b hcomm P hP e T hT q hQq,
    isIso_obstructionTargetBaseChangeMap fR hfR fS hfS a b hcomm hJ ha hb P hP e T hT q hq hQq,
    isCanonicalObstructionMap_baseChange fR hfR fS hfS a b hcomm hωR hωS P m hPLE hfree hP e
      T k hTLE hTproj hT q hq hQq⟩

end Deformation.Obstruction

end
