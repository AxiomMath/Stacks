module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckConjugacyTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilComparisonConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectOfCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionInduction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# Perfectness of the complexes in Steps 8 and 9 of the trace formula for curves

Let `f : V ⟶ U` be a connected finite étale cover of a smooth curve over a finite field `k`, with
smooth projective compactification `j : V ⟶ V̄` (`AlgebraicGeometry.CoverCompactification`), and
`A = ℤ/ℓⁿ` with `ℓ` invertible in `k`. The core vanishing theorem
`Stacks.EtaleCohomology.conjugacyTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero` of
the proof of [Stacks, Tag 03UG] uses four complexes, and this file proves that each is perfect.

* `RΓ(V̄_k̄, (j_! A)|_{V̄_k̄})`, the cohomology with compact support of `V_k̄`. This is
  [Stacks, Tag 03TV] for the constant sheaf, which lies in `D_ctf`.
* `RΓ(V̄_k̄, A)`. It is [Stacks, Tag 03TV] on the projective curve `V̄` compactified by itself.
* `RΓ(W_k̄, A)` for the boundary `W = V̄ ∖ V`, which is finite étale over `k`. It is the direct
  sum of the stalks.
* `Γ(k̄, A) = A` in degree zero.

## Main results

* `Stacks.EtaleCohomology.isPerfect_coverCompactification_extensionByZeroConstant`
* `Stacks.EtaleCohomology.isPerfect_coverCompactification_selfMapCohomology`
* `Stacks.EtaleCohomology.isPerfect_coverCompactification_boundarySelfMapCohomology`
* `Stacks.EtaleCohomology.isPerfect_baseSectionsComplex_zmodConstant`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 8 and 9.
* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace AlgebraicGeometry.CoverCompactification

variable {k : Type u} [Field k] [PerfectField k] {U Ub V : Scheme.{u}}
  {pUb : Ub ⟶ Spec (.of k)} {jU : U ⟶ Ub} {f : V ⟶ U} (C : CoverCompactification k pUb jU f)

omit [PerfectField k] in
/-- `V̄` is projective over `k`: a proper curve over a field is projective. -/
theorem isProjective_q : IsProjective C.q :=
  Stacks.EtaleCohomology.isProjective_of_isProper_of_isCurve C.q

/-- `j : V ⟶ V̄` as a compactification of `V` over `k`. -/
def toCompactificationOf : CompactificationOf (Over.mk (C.j ≫ C.q)) :=
  ⟨StructuredArrow.mk (Y := Over.mk C.q) (Over.homMk (U := Over.mk (C.j ≫ C.q)) C.j rfl),
    ⟨inferInstanceAs (IsOpenImmersion C.j), inferInstanceAs (IsProper C.q)⟩⟩

end AlgebraicGeometry.CoverCompactification

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-! ### A finite projective module in degree zero -/

section General

/-- **A finite projective module in degree zero is perfect.** -/
theorem isPerfect_single_of_finite_projective (R : Type) [Ring R]
    (A : ModuleCat.{u + 1} R) [Module.Finite R A] [Module.Projective R A] :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{u + 1} R) (ComplexShape.up ℤ) 0).obj A)) := by
  let P := (HomologicalComplex.single (ModuleCat.{u + 1} R) (ComplexShape.up ℤ) 0).obj A
  let e₀ : P.X 0 ≃ₗ[R] A :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).toLinearEquiv
  refine ⟨P, 0, 0,
    inferInstanceAs (CochainComplex.IsStrictlyGE ((HomologicalComplex.single
      (ModuleCat.{u + 1} R) (ComplexShape.up ℤ) 0).obj A) 0),
    inferInstanceAs (CochainComplex.IsStrictlyLE ((HomologicalComplex.single
      (ModuleCat.{u + 1} R) (ComplexShape.up ℤ) 0).obj A) 0),
    fun i => ?_, fun i => ?_, ⟨Iso.refl _⟩⟩ <;> obtain rfl | hi := eq_or_ne i 0
  · exact Module.Finite.equiv e₀.symm
  · have : Subsingleton (P.X i) :=
      ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    infer_instance
  · exact Module.Projective.of_equiv e₀.symm
  · have : Subsingleton (P.X i) :=
      ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    infer_instance

end General

section Cover

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U Ub V : Scheme.{u}}
  {pUb : Ub ⟶ Spec (.of k)} {jU : U ⟶ Ub} {f : V ⟶ U}
  (C : CoverCompactification k pUb jU f) (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar] (ℓ n : ℕ) [Fact ℓ.Prime]

omit [Fintype k] [PerfectField k] in
/-- **`RΓ(V̄_k̄, (j_! A)|_{V̄_k̄})` is perfect**: the cohomology with compact support of `V_k̄`
with coefficients in the constant sheaf `A = ℤ/ℓⁿ` ([Stacks, Tag 03TV]). -/
theorem isPerfect_coverCompactification_extensionByZeroConstant :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
        (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
              (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex (ZMod (ℓ ^ n)) C.toOver C.j
                (zmodSingleComplex.{u} ℓ n))))))) := by
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({C.Vb, V} : Set Scheme.{u})
  let Xb : B.Scheme := ⟨C.Vb, hB _ (by simp)⟩
  have hV : B.Contains V := hB _ (by simp)
  have hctf := isCtf_restriction (B := B) (Λ := ZMod (ℓ ^ n)) hV C.j
    (isCtf_constantCoefficients B (ZMod (ℓ ^ n)) Xb)
  have : IsLocallyNoetherian C.Vb := LocallyOfFiniteType.isLocallyNoetherian C.q
  have : CompactSpace C.Vb := QuasiCompact.compactSpace_of_compactSpace C.q
  have : IsNoetherian C.Vb := ⟨⟩
  have : TopologicalSpace.NoetherianSpace V := C.j.isOpenEmbedding.isInducing.noetherianSpace
  exact isPerfect_compactSupportFrobeniusCohomology_of_isCtf_of_isProjective B (ZMod (ℓ ^ n))
    (X := ⟨V, hV⟩) (f := C.j ≫ C.q) C.toCompactificationOf kbar Xb.property
    (inferInstanceAs (IsCurve k C.q)) C.isProjective_q _ hctf

omit [Fintype k] [PerfectField k] in
/-- **`RΓ(V̄_k̄, A)` is perfect**, for the projective curve `V̄` ([Stacks, Tag 03TV]). -/
theorem isPerfect_coverCompactification_selfMapCohomology [Finite k] :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))) := by
  have := Fintype.ofFinite k
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({C.Vb} : Set Scheme.{u})
  exact isPerfect_selfMapCohomology_constant_of_ofProper (ZMod (ℓ ^ n)) (X := C.Vb) C.q kbar
    (zmodSingleComplex.{u} ℓ n)
    (isPerfect_compactSupportFrobeniusCohomology_constantCoefficients B (ZMod (ℓ ^ n))
      (X := ⟨C.Vb, hB _ (by simp)⟩) C.q C.isProjective_q kbar)

/-- The stalk of a constant complex at a geometric point is the complex of values. -/
def pointStalkComplexConstantIso {X : Scheme.{u}} (Λ : Type) [Ring Λ] (s : GeometricPoint X)
    (N : CochainComplex.Plus (ModuleCat.{u + 1} Λ)) :
    (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapCochainComplexPlus.obj N).obj ≅
      N.obj :=
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    moduleCat_hasLimitsOfSize.{u, u, 0, u + 1} Λ
  let e := CategoryTheory.Sites.constantSheafFiberNatIso
    (D := ModuleCat.{u + 1} Λ) (J := X.smallEtaleTopology) (Scheme.pointSmallEtale s.hom)
  HomologicalComplex.Hom.isoOfComponents (fun n => e.app (N.obj.X n))
    (fun i j _ => (e.hom.naturality (N.obj.d i j)).symm)

omit [Fintype k] [Algebra.IsAlgebraic k kbar] [Fact ℓ.Prime] in
/-- **`RΓ(W_k̄, A)` is perfect** for the boundary `W = V̄ ∖ V`, finite étale over `k`: it is the
direct sum of the stalks. -/
theorem isPerfect_coverCompactification_boundarySelfMapCohomology [Finite k] :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.boundaryOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))) := by
  have := Fintype.ofFinite k
  have : Finite C.boundary := by
    have h : Set.Finite (Set.range C.boundaryι.base) := by
      rw [show Set.range C.boundaryι.base = (Set.range C.j.base)ᶜ from
        Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _]
      exact C.finite_compl
    have := h.to_subtype
    exact Finite.of_injective_finite_range C.boundaryι.isClosedEmbedding.injective
  have hfin : IsFinite (C.boundaryι ≫ C.q) := by
    have : LocallyQuasiFinite (C.boundaryι ≫ C.q) :=
      (locallyQuasiFinite_iff_finite_preimage_singleton).2 fun _ => Set.toFinite _
    exact IsFinite.of_isProper_of_locallyQuasiFinite _
  have : Etale C.boundaryOver.hom :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_of_isFinite_of_isReduced (C.boundaryι ≫ C.q)
  have : IsFinite C.boundaryOver.hom := hfin
  refine isPerfect_selfMapCohomology_constant_of_frobeniusRestriction (ZMod (ℓ ^ n)) C.boundaryOver
    kbar (zmodSingleComplex.{u} ℓ n) ?_
  exact isPerfect_frobeniusRestriction_of_etale (ZMod (ℓ ^ n)) C.boundaryOver kbar _ fun s =>
    StacksDraft.Perfect.isPerfect_of_iso.{0, u + 1, u + 2}
      (DerivedCategory.Q.mapIso (pointStalkComplexConstantIso (ZMod (ℓ ^ n)) s _))
      (isPerfect_constantCoefficientComplex.{u, 0} (ZMod (ℓ ^ n)))

omit [Fintype k] [PerfectField k] [Algebra.IsAlgebraic k kbar] in
/-- **`Γ(k̄, A) = A` in degree zero is perfect.** -/
theorem isPerfect_baseSectionsComplex_zmodConstant (hℓ : (ℓ : k) ≠ 0) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex (ZMod (ℓ ^ n))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)).obj)) := by
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero⟩
  have hN : ((ℓ ^ n : ℕ) : kbar) ≠ 0 := by
    rw [Nat.cast_pow, ← map_natCast (algebraMap k kbar)]
    exact pow_ne_zero _ ((map_ne_zero _).mpr hℓ)
  let F := constantSheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod (ℓ ^ n)))
  let G := sheafToPresheaf (Spec (.of kbar)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod (ℓ ^ n))) ⋙
    (CategoryTheory.evaluation (Spec (.of kbar)).Etaleᵒᵖ (ModuleCat.{u + 1} (ZMod (ℓ ^ n)))).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of kbar)))))
  let M := ModuleCat.of (ZMod (ℓ ^ n)) (ULift.{u + 1} (ZMod (ℓ ^ n)))
  let e : baseSectionsComplex (ZMod (ℓ ^ n))
      (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)).obj ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (G.obj (F.obj M)) :=
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).app (F.obj M)
  obtain ⟨E₀⟩ := nonempty_constantSections_addEquiv (Ω := kbar) (ℓ ^ n) hN
  let L : G.obj (F.obj M) ≃ₗ[ZMod (ℓ ^ n)] ZMod (ℓ ^ n) :=
    { E₀ with map_smul' := ZMod.map_smul E₀.toAddMonoidHom }
  have : Module.Finite (ZMod (ℓ ^ n)) (G.obj (F.obj M)) := Module.Finite.equiv L.symm
  have : Module.Projective (ZMod (ℓ ^ n)) (G.obj (F.obj M)) := Module.Projective.of_equiv L.symm
  exact StacksDraft.Perfect.isPerfect_of_iso.{0, u + 1, u + 2} (DerivedCategory.Q.mapIso e)
    (isPerfect_single_of_finite_projective (ZMod (ℓ ^ n)) _)

end Cover

end Stacks.EtaleCohomology

end
