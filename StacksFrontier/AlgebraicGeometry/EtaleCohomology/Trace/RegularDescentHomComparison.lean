module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AcyclicTwistResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BaseChangeTwistCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RegularDescentCompactSupportHom
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTrace

/-!
# `RΓ_c(X_k̄, Hom_R(M, D))` as `Hom_R(M, -)` of an injective model of `RΓ_c(X_k̄, D)`

Let `D` be a sheaf of modules over a Noetherian `A`-algebra `R` on `X_étale`, with
`X ⟶ X̄` a compactification over a finite field, such that `F' = (j_! D)|_{X̄_k̄}` is locally
injective: `Hom_R(N₂, F') ⟶ Hom_R(N₁, F')` is an epimorphism of sheaves for every injection
`N₁ ⟶ N₂` of finite `R`-modules. Let `F' ⟶ T` be an injective resolution and
`J = Γ(Spec k̄, g_* T)` the resulting model of `RΓ_c(X_k̄, D)`. For every finite `R`-module `M`
which is an `(R, Λ)`-bimodule with `A` acting centrally through `Λ`,
`RΓ_c(X_k̄, Hom_R(M, D)) ≅ Hom_R(M, J)` in `D(Λ)`, compatibly with the Frobenius `π_X^*`:
`Hom_R(M, T)` is a resolution of `Hom_R(M, F') = (j_! Hom_R(M, D))|_{X̄_k̄}` by sheaves acyclic
everywhere.

This is the comparison behind Step 7 of the proof of [Stacks, Tag 03UG].

## Main results

* `Stacks.EtaleCohomology.isLimit_kernelFork_f_zero_of_quasiIso`,
  `Stacks.EtaleCohomology.quasiIso_of_isLimit_kernelFork_f_zero`: a complex concentrated in degree
  zero mapping to a complex in nonnegative degrees, exact in positive degrees.

## Implementation notes

The statements involve `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius`, defined in the
model `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

section Single

variable {C : Type*} [Category* C] [Abelian C] {K I : CochainComplex C ℤ} [K.IsStrictlyGE 0]
  [K.IsStrictlyLE 0] [I.IsStrictlyGE 0] (φ : K ⟶ I)

omit [K.IsStrictlyGE 0] [I.IsStrictlyGE 0] in
/-- A map from a complex concentrated in degree zero to a complex `I` composes with the
differential `I.d 0 1` to zero in degree zero. -/
lemma f_zero_comp_d_eq_zero : φ.f 0 ≫ I.d 0 1 = 0 := by
  rw [φ.comm, (K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt (K.d 0 1) 0, zero_comp]

omit [K.IsStrictlyGE 0] in
/-- For a complex concentrated in degree zero, the inclusion of the cycles in degree zero is an
isomorphism. -/
lemma isIso_iCycles_zero : IsIso (K.iCycles 0) :=
  K.isIso_iCycles 0 1 (by simp) ((K.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _)

omit [K.IsStrictlyLE 0] in
/-- For a complex in nonnegative degrees, the projection from the cycles in degree zero to the
homology in degree zero is an isomorphism. -/
lemma isIso_homologyπ_zero : IsIso (K.homologyπ 0) :=
  K.isIso_homologyπ (-1) 0 (by simp) ((K.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _)

/-- **A quasi-isomorphism from a complex concentrated in degree zero to a complex in nonnegative
degrees is a kernel of the first differential in degree zero.** -/
def isLimit_kernelFork_f_zero_of_quasiIso [QuasiIso φ] :
    IsLimit (KernelFork.ofι (φ.f 0) (f_zero_comp_d_eq_zero φ)) := by
  haveI := isIso_iCycles_zero (K := K)
  haveI := isIso_homologyπ_zero (K := K)
  haveI := isIso_homologyπ_zero (K := I)
  haveI : IsIso (HomologicalComplex.homologyMap φ 0) :=
    (quasiIsoAt_iff_isIso_homologyMap φ 0).1 inferInstance
  haveI : IsIso (HomologicalComplex.cyclesMap φ 0) := by
    have : IsIso (HomologicalComplex.cyclesMap φ 0 ≫ I.homologyπ 0) := by
      rw [← HomologicalComplex.homologyπ_naturality φ 0]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (I.homologyπ 0)
  refine IsLimit.ofIsoLimit (I.cyclesIsKernel 0 1 (by simp))
    (Fork.ext ((asIso (HomologicalComplex.cyclesMap φ 0)).symm ≪≫ asIso (K.iCycles 0)) ?_)
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
    Fork.ι_ofι]
  rw [← HomologicalComplex.cyclesMap_i, IsIso.inv_hom_id_assoc]

/-- **A complex concentrated in degree zero mapping to a complex in nonnegative degrees, exact in
positive degrees, by a kernel of the first differential in degree zero, is a
quasi-isomorphism.** -/
lemma quasiIso_of_isLimit_kernelFork_f_zero (hI : ∀ q : ℤ, 1 ≤ q → I.ExactAt q)
    (h : IsLimit (KernelFork.ofι (φ.f 0) (f_zero_comp_d_eq_zero φ))) : QuasiIso φ := by
  rw [quasiIso_iff]
  intro i
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact (quasiIsoAt_iff_exactAt φ i ((K.exactAt_iff i).2 (ShortComplex.exact_of_isZero_X₂ _
      (K.isZero_of_isStrictlyGE 0 i hi)))).2
      ((I.exactAt_iff i).2 (ShortComplex.exact_of_isZero_X₂ _ (I.isZero_of_isStrictlyGE 0 i hi)))
  · have := isIso_iCycles_zero (K := K)
    have := isIso_homologyπ_zero (K := K)
    have := isIso_homologyπ_zero (K := I)
    let e := IsLimit.conePointUniqueUpToIso h (I.cyclesIsKernel 0 1 (by simp))
    have he : e.hom ≫ I.iCycles 0 = φ.f 0 :=
      IsLimit.conePointUniqueUpToIso_hom_comp h (I.cyclesIsKernel 0 1 (by simp))
        WalkingParallelPair.zero
    have hc : HomologicalComplex.cyclesMap φ 0 = K.iCycles 0 ≫ e.hom := by
      rw [← cancel_mono (I.iCycles 0), HomologicalComplex.cyclesMap_i, Category.assoc, he]
    have : IsIso (HomologicalComplex.cyclesMap φ 0) := by
      rw [hc]
      infer_instance
    have hh : HomologicalComplex.homologyMap φ 0 =
        inv (K.homologyπ 0) ≫ HomologicalComplex.cyclesMap φ 0 ≫ I.homologyπ 0 := by
      rw [← HomologicalComplex.homologyπ_naturality, IsIso.inv_hom_id_assoc]
    rw [quasiIsoAt_iff_isIso_homologyMap, hh]
    infer_instance
  · exact (quasiIsoAt_iff_exactAt φ i ((K.exactAt_iff i).2 (ShortComplex.exact_of_isZero_X₂ _
      (K.isZero_of_isStrictlyLE 0 i hi)))).2 (hI i hi)

end Single

/-! ### The resolution -/

section Resolution

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) {R : Type} [Ring R]
  (D : EtaleModules.{u, 0} R X)

/-- **An injective resolution of `(j_! D)|_{X̄_k̄}` with a lift of the Frobenius twist**: a
quasi-isomorphism `ψ` into a complex `T` of injectives in nonnegative degrees, with a twist
`T ⟶ π̄_* T` compatible with the Frobenius twist of `(j_! D)|_{X̄_k̄}` in the derived category. -/
structure CompactSupportTwistResolution where
  /-- the resolution -/
  T : CochainComplex.Plus (EtaleModules.{u, 0} R (fieldBaseChange (Over.mk j.toBase) kbar))
  /-- the resolution map -/
  ψ : (etaleModuleInverseImage.{u, 0} R
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D)) ⟶ T
  /-- the resolution map is a quasi-isomorphism -/
  quasiIso : QuasiIso ψ.hom
  /-- every term of the resolution is injective -/
  injective : ∀ n, Injective (T.obj.X n)
  /-- the resolution is concentrated in nonnegative degrees -/
  isStrictlyGE : T.obj.IsStrictlyGE 0
  /-- the twist of the resolution -/
  twist : T ⟶ (etaleModuleDirectImage.{u, 0} R
    (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.obj T
  /-- the twist of the resolution lifts the Frobenius twist of `(j_! D)|_{X̄_k̄}` in the derived
  category -/
  twist_comm : DerivedCategory.Plus.Q.map
      (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} R
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
                ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D)))
          (Y := (etaleModuleDirectImage.{u, 0} R
            (geometricFrobeniusBaseChange (Over.mk j.toBase)
              kbar p q hcard)).mapCochainComplexPlus.obj
              ((etaleModuleInverseImage.{u, 0} R
                (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
                ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
                  ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))))
          ((NatTrans.mapHomologicalComplex
            (frobeniusBaseChangeTwist.{u, 0} R (Over.mk j.toBase) kbar p q hcard)
              (ComplexShape.up ℤ)).app
                ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
                  ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D)).obj) ≫
        (etaleModuleDirectImage.{u, 0} R
          (geometricFrobeniusBaseChange (Over.mk j.toBase)
            kbar p q hcard)).mapCochainComplexPlus.map ψ) =
    DerivedCategory.Plus.Q.map (ψ ≫ twist)

attribute [instance] CompactSupportTwistResolution.quasiIso
  CompactSupportTwistResolution.injective CompactSupportTwistResolution.isStrictlyGE

/-- An additive functor carries a complex in degrees `≥ n` to one. -/
lemma isStrictlyGE_mapHomologicalComplex {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [Preadditive C₁] [Preadditive C₂] [HasZeroObject C₁] [HasZeroObject C₂] (F : C₁ ⥤ C₂)
    [F.Additive] (K : CochainComplex C₁ ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n :=
  (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi =>
    F.map_isZero (K.isZero_of_isStrictlyGE n i hi)

/-- The direct image along the Frobenius of a bounded below complex of injectives is
`K`-injective. -/
private theorem isKInjective_directImage_frobenius
    (T : CochainComplex.Plus (EtaleModules.{u, 0} R (fieldBaseChange (Over.mk j.toBase) kbar)))
    (hT : ∀ n, Injective (T.obj.X n)) :
    ((etaleModuleDirectImage.{u, 0} R
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.obj
        T).obj.IsKInjective := by
  have := hT
  obtain ⟨b, hb⟩ := ((etaleModuleDirectImage.{u, 0} R
    (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.obj
      T).property
  have : ∀ n, Injective (((etaleModuleDirectImage.{u, 0} R
    (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.obj
      T).obj.X n) := fun n =>
    inferInstanceAs (Injective ((etaleModuleDirectImage.{u, 0} R
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).obj (T.obj.X n)))
  exact CochainComplex.isKInjective_of_injective _ b

/-- **Twisted injective resolutions exist.** -/
theorem CompactSupportTwistResolution.nonempty :
    Nonempty (CompactSupportTwistResolution j kbar p q hcard D) := by
  let K := (etaleModuleInverseImage.{u, 0} R
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))
  let P := etaleModuleDirectImage.{u, 0} R
    (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
  have : K.obj.IsStrictlyGE 0 :=
    @isStrictlyGE_mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ _ 0
      (@isStrictlyGE_mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ _ 0
        (inferInstanceAs (((CochainComplex.singleFunctor _ 0).obj D).IsStrictlyGE 0)))
  obtain ⟨Rs, -, hge⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0 K.obj
  let T : CochainComplex.Plus _ := ⟨Rs.cocomplex, Rs.boundedBelow⟩
  let ψ : K ⟶ T := ObjectProperty.homMk Rs.ι
  have hq : QuasiIso ψ.hom := inferInstanceAs (QuasiIso Rs.ι)
  have hinj : ∀ n, Injective (T.obj.X n) := fun n => inferInstanceAs (Injective (Rs.cocomplex.X n))
  have : IsIso (DerivedCategory.Q.map ψ.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 hq
  have := isKInjective_directImage_frobenius j kbar p q hcard T hinj
  let τ : K ⟶ P.mapCochainComplexPlus.obj K := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} R (Over.mk j.toBase) kbar p q hcard) (ComplexShape.up ℤ)).app
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D)).obj)
  obtain ⟨g, hg⟩ := StacksDraft.DerivedHom.exists_eq_Q_map_of_isKInjective T.obj
    (P.mapCochainComplexPlus.obj T).obj
    (CategoryTheory.inv (DerivedCategory.Q.map ψ.hom) ≫
      DerivedCategory.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ).hom)
  refine ⟨⟨T, ψ, hq, hinj, hge,
    ObjectProperty.homMk g, DerivedCategory.Plus.ι.map_injective ?_⟩⟩
  change DerivedCategory.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ).hom =
    DerivedCategory.Q.map (ψ.hom ≫ g)
  rw [DerivedCategory.Q.map_comp ψ.hom g, hg, IsIso.hom_inv_id_assoc]

omit [Fintype k] in
/-- The complex `(j_! D)|_{X̄_k̄}`, placed in degree zero, is concentrated in degrees `≥ 0`. -/
lemma isStrictlyGE_compactSupportSingle :
    ((etaleModuleInverseImage.{u, 0} R
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))).obj.IsStrictlyGE 0 :=
  @isStrictlyGE_mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ _ 0
    (@isStrictlyGE_mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ _ 0
      (inferInstanceAs (((CochainComplex.singleFunctor _ 0).obj D).IsStrictlyGE 0)))

omit [Fintype k] in
/-- The complex `(j_! D)|_{X̄_k̄}`, placed in degree zero, is concentrated in degrees `≤ 0`. -/
lemma isStrictlyLE_compactSupportSingle :
    ((etaleModuleInverseImage.{u, 0} R
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))).obj.IsStrictlyLE 0 :=
  @Stacks.Homology.isStrictlyLE_mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ _ 0
    (@Stacks.Homology.isStrictlyLE_mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ _ 0
      (inferInstanceAs (((CochainComplex.singleFunctor _ 0).obj D).IsStrictlyLE 0)))

variable {A : Type} [CommRing A] [Algebra A R] [IsNoetherianRing R] {D}

/-- **`Hom_R(M, -)` of the resolution of a locally injective `(j_! D)|_{X̄_k̄}` is a resolution of
`Hom_R(M, (j_! D)|_{X̄_k̄})`**, `M` a finite `R`-module, coefficients in `A`. -/
theorem quasiIso_map_homSheaf_compactSupportTwistResolution
    (hD : ∀ {N₁ N₂ : ModuleCat.{u + 1} R} [Module.Finite R N₁] [Module.Finite R N₂]
      (v : N₁ ⟶ N₂) [Mono v], Epi ((homSheafPrecomp (A := A) v
        (fieldBaseChange (Over.mk j.toBase) kbar)).app
          ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj D))))
    (Rs : CompactSupportTwistResolution j kbar p q hcard D) (M : ModuleCat.{u + 1} R)
    [Module.Finite R M] :
    QuasiIso (((homSheaf A M (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map Rs.ψ.hom) := by
  let Y := fieldBaseChange (Over.mk j.toBase) kbar
  let gi := etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let jx := etaleModuleExtensionByZero.{u, 0} R j.immersion
  have := isStrictlyGE_compactSupportSingle j kbar D
  have := isStrictlyLE_compactSupportSingle j kbar D
  have := preservesFiniteLimits_homSheaf (A := A) M Y
  -- the term in degree zero is `(j_! D)|_{X̄_k̄}` up to isomorphism, hence locally injective
  let e := gi.mapIso (jx.mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 D))
  have hF : ∀ {N₁ N₂ : ModuleCat.{u + 1} R} [Module.Finite R N₁] [Module.Finite R N₂]
      (v : N₁ ⟶ N₂) [Mono v], Epi ((homSheafPrecomp (A := A) v Y).app
        (((etaleModuleInverseImage.{u, 0} R
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          (jx.mapCochainComplexPlus.obj
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))).obj.X 0)) :=
    fun {N₁ N₂} _ _ v _ => by
      have h := hD v
      have hn := (homSheafPrecomp (A := A) v Y).naturality e.hom
      have : (homSheafPrecomp (A := A) v Y).app _ =
          (homSheaf A N₂ Y).map e.hom ≫ (homSheafPrecomp (A := A) v Y).app _ ≫
            (homSheaf A N₁ Y).map e.inv := by
        rw [← Category.assoc, hn, Category.assoc, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
          CategoryTheory.Functor.map_id, Category.comp_id]
      have key : Epi ((homSheaf A N₂ Y).map e.hom ≫ (homSheafPrecomp (A := A) v Y).app _ ≫
          (homSheaf A N₁ Y).map e.inv) := inferInstance
      rw [← this] at key
      exact key
  let Kc := ((etaleModuleInverseImage.{u, 0} R
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
      ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))).obj
  have hKc : Kc.IsStrictlyLE 0 := isStrictlyLE_compactSupportSingle j kbar D
  have hT : ∀ q : ℤ, 1 ≤ q → Rs.T.obj.ExactAt q := fun q hq =>
    (quasiIsoAt_iff_exactAt Rs.ψ.hom q ((Kc.exactAt_iff q).2
      (ShortComplex.exact_of_isZero_X₂ _ (Kc.isZero_of_isStrictlyLE 0 q (by omega))))).1
        inferInstance
  have hex := exactAt_homSheaf_of_locallyInjective (A := A) _ hF Rs.T.obj Rs.injective
    (Rs.ψ.hom.f 0) (f_zero_comp_d_eq_zero Rs.ψ.hom)
    (isLimit_kernelFork_f_zero_of_quasiIso Rs.ψ.hom) hT
  have := @isStrictlyGE_mapHomologicalComplex _ _ _ _ _ _ _ _ (homSheaf A M Y) _ _ 0
    (isStrictlyGE_compactSupportSingle j kbar D)
  have := @Stacks.Homology.isStrictlyLE_mapHomologicalComplex _ _ _ _ _ _ _ _ (homSheaf A M Y) _ _ 0
    (isStrictlyLE_compactSupportSingle j kbar D)
  have := @isStrictlyGE_mapHomologicalComplex _ _ _ _ _ _ _ _ (homSheaf A M Y) _ _ 0
    Rs.isStrictlyGE
  refine quasiIso_of_isLimit_kernelFork_f_zero _ (fun q hq => ?_)
    (KernelFork.mapIsLimit _ (isLimit_kernelFork_f_zero_of_quasiIso Rs.ψ.hom) (homSheaf A M Y))
  obtain ⟨q', rfl⟩ : ∃ q' : ℕ, q = q' + 1 := ⟨(q - 1).toNat, by omega⟩
  exact hex q' M

variable {Λ : Type} [Ring Λ] [Algebra A Λ] (M : ModuleCat.{u + 1} R) [Module.Finite R M]
  (ρ : Λ →+* (End M)ᵐᵒᵖ) (hρ : ∀ a : A, ρ (algebraMap A Λ a) = centralScalars M a)

include hρ in
/-- **`Hom_R(M, -)` commutes with `(j_! -)|_{X̄_k̄}`**, on bounded below complexes. -/
def compactSupportHomIso (L : CochainComplex.Plus (EtaleModules.{u, 0} R X)) :
    (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
          ((etaleModuleHom M ρ X).mapCochainComplexPlus.obj L)) ≅
      (etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, 0} R
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj L)) :=
  haveI : IsIso (compactSupportCoefficientMate (homFunctor M ρ) (Over.mk j.toBase) kbar
      j.immersion) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun G => ?_
    rw [compactSupportCoefficientMate_app]
    have h₁ := isIso_coefficientMate_extensionByZero_homFunctor M ρ hρ j.immersion G
    have h₂ := isIso_coefficientMate_inverseImage_homFunctor M ρ hρ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G)
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ (etaleModuleInverseImage.{u, 0} Λ
        (fieldBaseChangeProj (Over.mk j.toBase) kbar)) _ h₁) h₂
  haveI : (sheafCompose X.smallEtaleTopology (homFunctor M ρ)).Additive :=
    etaleModuleHom_additive M ρ X
  haveI : (sheafCompose (Over.mk f).left.smallEtaleTopology (homFunctor M ρ)).Additive :=
    etaleModuleHom_additive M ρ X
  haveI : (etaleModuleInverseImage.{u, 0} Λ
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).Additive :=
    (etaleModuleInverseImageAdj.{u, 0} Λ _).left_adjoint_additive
  haveI : (etaleModuleInverseImage.{u, 0} R
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).Additive :=
    (etaleModuleInverseImageAdj.{u, 0} R _).left_adjoint_additive
  haveI : (sheafCompose (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology
      (homFunctor M ρ)).Additive := etaleModuleHom_additive M ρ _
  ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex (asIso (compactSupportCoefficientMate
    (homFunctor M ρ) (Over.mk j.toBase) kbar j.immersion)) (ComplexShape.up ℤ)).app L.obj)

omit [Module.Finite R M] [IsNoetherianRing R] in
/-- The composition isomorphism of direct images commutes with `Hom_R(M, -)`. -/
lemma directImageComp_hom_app_etaleModuleHom {X₁ X₂ X₃ : Scheme.{u}} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (f₁₂ : X₁ ⟶ X₃) (h : f₁₂ = f₁ ≫ f₂) (G : EtaleModules.{u, 0} R X₁) :
    (etaleModuleDirectImageComp.{u, 0} Λ f₁ f₂ f₁₂ h).hom.app ((etaleModuleHom M ρ X₁).obj G) =
      (etaleModuleHom M ρ X₃).map
        ((etaleModuleDirectImageComp.{u, 0} R f₁ f₂ f₁₂ h).hom.app G) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  change 𝟙 _ ≫ (homFunctor M ρ).map (G.obj.map _) = (homFunctor M ρ).map (𝟙 _ ≫ G.obj.map _)
  simp only [Category.id_comp]

omit [Module.Finite R M] [IsNoetherianRing R] in
/-- Direct image commutes with `Hom_R(M, -)` on morphisms. -/
lemma directImage_map_etaleModuleHom {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ X₂)
    {G G' : EtaleModules.{u, 0} R X₁} (x : G ⟶ G') :
    (etaleModuleDirectImage.{u, 0} Λ f₁).map ((etaleModuleHom M ρ X₁).map x) =
      (etaleModuleHom M ρ X₂).map ((etaleModuleDirectImage.{u, 0} R f₁).map x) := by
  apply Sheaf.hom_ext
  rfl

omit [Module.Finite R M] in
/-- **Global sections commute with `Hom_R(M, -)`**: both are sections over the final object. -/
def globalSectionsEtaleModuleHomIso (S : Scheme.{u}) :
    etaleModuleHom M ρ S ⋙ etaleModuleGlobalSections.{u, 0} Λ S ≅
      etaleModuleGlobalSections.{u, 0} R S ⋙ homFunctor M ρ :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal) ≪≫
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      etaleModuleHom M ρ S ⋙
          (sheafSections S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (⊤_ S.Etale)) ≅
        (sheafSections S.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (op (⊤_ S.Etale)) ⋙
          homFunctor M ρ) ≪≫
    Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections S.smallEtaleTopology
      (ModuleCat.{u + 1} R) terminalIsTerminal).symm _

omit [Module.Finite R M] [IsNoetherianRing R] in
/-- **The chain model of the Frobenius commutes with `Hom_R(M, -)`**: on
`Γ(Spec k̄, g_* Hom_R(M, T)) = Hom_R(M, Γ(Spec k̄, g_* T))` the endomorphism induced by the twist
`Hom_R(M, T) ⟶ π̄_* Hom_R(M, T)` is `Hom_R(M, -)` of the one induced by `T ⟶ π̄_* T`. -/
lemma twistChainEndo_etaleModuleHom
    (T : CochainComplex.Plus (EtaleModules.{u, 0} R (fieldBaseChange (Over.mk j.toBase) kbar)))
    (tw : T ⟶ (etaleModuleDirectImage.{u, 0} R (geometricFrobeniusBaseChange (Over.mk j.toBase)
      kbar p q hcard)).mapCochainComplexPlus.obj T) :
    (Functor.twistChainEndo (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
          (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
        ((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj T)
        ((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
          tw)).hom ≫
      ((NatIso.mapHomologicalComplex (globalSectionsEtaleModuleHomIso M ρ (Spec (.of kbar)))
        (ComplexShape.up ℤ)).app (((etaleModuleDirectImage.{u, 0} R
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T.obj)).hom =
    ((NatIso.mapHomologicalComplex (globalSectionsEtaleModuleHomIso M ρ (Spec (.of kbar)))
        (ComplexShape.up ℤ)).app (((etaleModuleDirectImage.{u, 0} R
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj T.obj)).hom ≫
      ((homFunctor M ρ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (Functor.twistChainEndo (etaleModuleDirectImage.{u, 0} R
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
          (etaleModuleDirectImage.{u, 0} R
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
            (etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar)))
          (etaleModuleDirectImageComp.{u, 0} R
            (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
            (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
            T tw).hom := by
  ext n : 1
  have hθ := directImageComp_hom_app_etaleModuleHom M ρ
    (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
    (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm (T.obj.X n)
  have hn := (globalSectionsEtaleModuleHomIso M ρ (Spec (.of kbar))).hom.naturality
    ((etaleModuleDirectImage.{u, 0} R
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).map (tw.hom.f n) ≫
      (etaleModuleDirectImageComp.{u, 0} R
        (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm).hom.app
        (T.obj.X n))
  change (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).map
      ((etaleModuleDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).map
          ((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).map (tw.hom.f n)) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ
          (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm).hom.app
          ((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).obj (T.obj.X n))) ≫
      (globalSectionsEtaleModuleHomIso M ρ (Spec (.of kbar))).hom.app
        ((etaleModuleDirectImage.{u, 0} R
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).obj (T.obj.X n)) =
    (globalSectionsEtaleModuleHomIso M ρ (Spec (.of kbar))).hom.app
        ((etaleModuleDirectImage.{u, 0} R
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).obj (T.obj.X n)) ≫
      (homFunctor M ρ).map ((etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))).map
        ((etaleModuleDirectImage.{u, 0} R
          (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).map (tw.hom.f n) ≫
          (etaleModuleDirectImageComp.{u, 0} R
            (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
            (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q
              hcard).symm).hom.app (T.obj.X n)))
  refine Eq.trans ?_ hn
  refine congrArg (fun z => (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).map z ≫ _) ?_
  rw [hθ, directImage_map_etaleModuleHom]
  exact ((etaleModuleHom M ρ _).map_comp _ _).symm

include hρ in
/-- **`RΓ_c(X_k̄, Hom_R(M, D))` is `Hom_R(M, J)`** for the model `J = Γ(Spec k̄, g_* T)` of
`RΓ_c(X_k̄, D)` given by a twisted injective resolution `T` of the locally injective
`(j_! D)|_{X̄_k̄}`, compatibly with `π_X^*` and the chain endomorphism of `J` induced by the twist
of `T`. -/
theorem exists_compactSupportHomModel [IsSepClosed kbar]
    (hD : ∀ {N₁ N₂ : ModuleCat.{u + 1} R} [Module.Finite R N₁] [Module.Finite R N₂]
      (v : N₁ ⟶ N₂) [Mono v], Epi ((homSheafPrecomp (A := A) v
        (fieldBaseChange (Over.mk j.toBase) kbar)).app
          ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj D))))
    (Rs : CompactSupportTwistResolution j kbar p q hcard D) :
    ∃ E : DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ((etaleModuleHom M ρ X).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))) ≅
      DerivedCategory.Q.obj (((homFunctor M ρ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, 0} R
            (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
              Rs.T)).obj),
      DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} Λ f j kbar p q hcard
          ((etaleModuleHom M ρ X).mapCochainComplexPlus.obj
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D))) ≫ E.hom =
        E.hom ≫ DerivedCategory.Q.map (((homFunctor M ρ).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (Functor.twistChainEndo
            (etaleModuleDirectImage.{u, 0} R
              (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
            (etaleModuleDirectImage.{u, 0} R
              (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
            (etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar)))
            (etaleModuleDirectImageComp.{u, 0} R
              (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
              (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
              (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
              (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
            Rs.T Rs.twist).hom) := by
  let e := compactSupportHomIso j kbar M ρ hρ
    ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj D)
  let ψΛ := e.hom ≫ (etaleModuleHom M ρ
    (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map Rs.ψ
  have : QuasiIso ψΛ.hom := by
    have h1 : QuasiIso (((etaleModuleHom M ρ
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      Rs.ψ.hom) :=
      quasiIso_map_etaleModuleHom_of_central M ρ hρ _
        (quasiIso_map_homSheaf_compactSupportTwistResolution j kbar p q hcard hD Rs M)
    have : IsIso e.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso e).hom)
    have : QuasiIso e.hom.hom := inferInstance
    exact quasiIso_comp e.hom.hom (((etaleModuleHom M ρ
      (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      Rs.ψ.hom)
      (hφ' := h1)
  have hT₁ : ∀ n, (etaleModuleDirectImage.{u, 0} Λ
    (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).rightAcyclic
      (((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        Rs.T).obj.X n) := fun n =>
    rightAcyclic_directImage_of_isAcyclicEverywhere
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)) _
      (isAcyclicEverywhere_etaleModuleHom_of_injective_of_central M ρ hρ (Rs.T.obj.X n))
  have hT₂ : ∀ n, (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar))).rightAcyclic
      ((etaleModuleDirectImage.{u, 0} Λ
        (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).obj
        (((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
        Rs.T).obj.X n)) :=
    fun n => Functor.rightAcyclic_of_exact _ _
  let KR := (etaleModuleInverseImage.{u, 0} R
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
    ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
      ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj D))
  let KΛ := (etaleModuleInverseImage.{u, 0} Λ
    (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus.obj
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
      ((etaleModuleHom M ρ X).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj D)))
  let τR : KR ⟶ (etaleModuleDirectImage.{u, 0} R
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.obj
        KR := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} R (Over.mk j.toBase) kbar p q hcard) (ComplexShape.up ℤ)).app
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj D)).obj)
  let τΛ : KΛ ⟶ (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.obj
        KΛ := ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex
      (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard) (ComplexShape.up ℤ)).app
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus.obj
          ((etaleModuleHom M ρ X).mapCochainComplexPlus.obj
            ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj D))).obj)
  have hκ : τΛ.hom ≫ ((etaleModuleDirectImage.{u, 0} Λ
    (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map e.hom.hom =
      e.hom.hom ≫ ((etaleModuleHom M ρ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        τR.hom := by
    ext n : 1
    exact frobeniusBaseChangeTwist_app_comp_compactSupportCoefficientMate (homFunctor M ρ)
      (Over.mk j.toBase) kbar p q hcard j.immersion
        (((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R X) 0).obj D).obj.X n)
  have hg : DerivedCategory.Plus.Q.map (τΛ ≫ (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.map
        ψΛ) =
      DerivedCategory.Plus.Q.map (ψΛ ≫
        (etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
          Rs.twist) := by
    have := isKInjective_directImage_frobenius j kbar p q hcard Rs.T Rs.injective
    have h₀ : DerivedCategory.Q.map
      (τR ≫ (etaleModuleDirectImage.{u, 0} R
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapCochainComplexPlus.map
      Rs.ψ).hom =
        DerivedCategory.Q.map (Rs.ψ ≫ Rs.twist).hom := DerivedCategory.Plus.ι.congr_map
          Rs.twist_comm
    have h₁ := DerivedCategory.Q_map_eq_of_homotopy _
      ((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomotopy
      (CochainComplex.homotopyOfQMapEq h₀))
    simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
      DerivedCategory.Q.map_comp] at h₁
    apply DerivedCategory.Plus.ι.map_injective
    change DerivedCategory.Q.map (τΛ.hom ≫
      ((etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapHomologicalComplex _).map
        (e.hom.hom ≫ ((etaleModuleHom M ρ
          (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).map Rs.ψ.hom)) =
      DerivedCategory.Q.map ((e.hom.hom ≫
        ((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex
        _).map Rs.ψ.hom) ≫
        ((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex
          _).map Rs.twist.hom)
    have hL := ((congrArg (τΛ.hom ≫ ·)
      (((etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_comp e.hom.hom
        (((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map Rs.ψ.hom))).trans (Category.assoc _ _ _).symm).trans
      ((congrArg (· ≫ ((etaleModuleDirectImage.{u, 0} Λ
        (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((etaleModuleHom M ρ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        Rs.ψ.hom)) hκ).trans (Category.assoc _ _ _))
    refine (congrArg DerivedCategory.Q.map hL).trans ?_
    refine (DerivedCategory.Q.map_comp _ _).trans ?_
    refine (congrArg (DerivedCategory.Q.map e.hom.hom ≫ ·)
      ((DerivedCategory.Q.map_comp _ _).trans h₁)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (DerivedCategory.Q.map_comp _ _).symm).trans ?_
    exact (DerivedCategory.Q.map_comp _ _).symm
  have hc := Functor.twistAcyclicResolutionIso_hom_comp
    (etaleModuleDirectImage.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard))
      (etaleModuleDirectImage.{u, 0} Λ
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, 0} Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk j.toBase) kbar p q hcard).symm)
    ψΛ hT₁ hT₂ τΛ
    ((etaleModuleHom M ρ (fieldBaseChange (Over.mk j.toBase) kbar)).mapCochainComplexPlus.map
      Rs.twist) hg
  let γ' := globalSectionsEtaleModuleHomIso M ρ (Spec (.of kbar))
  let γ := (NatIso.mapHomologicalComplex γ' (ComplexShape.up ℤ)).app
    (((etaleModuleDirectImage.{u, 0} R
      (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Rs.T.obj)
  refine ⟨Functor.twistAcyclicResolutionIso _ _ ψΛ hT₁ hT₂ ≪≫ DerivedCategory.Q.mapIso γ, ?_⟩
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ DerivedCategory.Q.map γ.hom) hc).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ?_).trans (Category.assoc _ _ _).symm
  refine (DerivedCategory.Q.map_comp _ _).symm.trans
    ((congrArg DerivedCategory.Q.map ?_).trans (DerivedCategory.Q.map_comp _ _))
  exact twistChainEndo_etaleModuleHom j kbar p q hcard M ρ Rs.T Rs.twist

end Resolution

end Stacks.EtaleCohomology
