module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportRestrictScalarsNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTwistComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.DerivedFunctorTrace
public import StacksFrontier.CategoryTheory.Trace.Sorites.ConjugacyTraceVanishing

/-!
# The conjugacy traces of `π_U^*` on `RΓ_c(U_k̄, D(A[H]))` vanish

Let `U` be a smooth curve over a finite field `k` without `k`-rational points, `G : V ⟶ U` a
connected finite étale Galois covering with group `H`, and `A = ℤ/ℓⁿ` with `ℓ` invertible in
`k`. The descent sheaf `N = D(A[H])` of the regular representation (the sheaf `f_* A` with its
`A[H]`-module structure) is a sheaf of `A[H]`-modules on `U`. Granted that `RΓ_c(U_k̄, N)` is a
perfect complex of `A[H]`-modules, let `T = Tr_{A[H]}(π_U^* | RΓ_c(U_k̄, N)) ∈ A[H]^♮`. For every
`g ∈ H` the conjugacy trace (`Stacks.Trace.conjugacyTrace`) of `T` vanishes:

`κ_g(T) = Tr_A(g⁻¹ ∘ π_U^* | RΓ_c(U_k̄, N)) = Tr_A((g⁻¹ π_V)^* | RΓ_c(V_k̄, A)) = 0`.

Consequently `T` dies in every quotient of `A[H]^♮` killed by `ℓ^m` when `n` is large compared
with `m` and `#H` (`Stacks.Trace.map_eq_zero_of_conjugacyTrace_eq_zero`).

## Main results

* `conjugacyTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero`:
  every conjugacy trace of `T` vanishes.
* `map_perfectDerivedTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero`:
  `T` dies in every quotient of `A[H]^♮` killed by `ℓ^m`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 7 and 8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U : Scheme.{u}} {H : Type} [Group H]
  [Fintype H] {pU : U ⟶ Spec (.of k)} [IsCurve k pU] [Smooth pU]
  (J : CompactificationOf (Over.mk pU))
  (G : EtaleGaloisCovering U H) [IsFinite (G.cover.hom : G.cover.left ⟶ U)]
  [ConnectedSpace G.cover.left] [ConnectedSpace ((𝟭 Scheme).obj G.cover.left)]
  (C : CoverCompactification k (Over.mk J.toBase).hom J.immersion
    (G.cover.hom : G.cover.left ⟶ U))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- A chase through three commutative squares: if `θ` commutes with `r`, `E` carries `θ` to `Θ`
and `r` to `π`, then `E` carries `θ ≫ r` to `π ≫ Θ`. -/
private theorem comp_eq_of_comm_squares {D : Type*} [Category* D] {X Y : D} (E : X ⟶ Y)
    (θ r : X ⟶ X) (Θ π : Y ⟶ Y) (h₁ : θ ≫ r = r ≫ θ) (h₂ : θ ≫ E = E ≫ Θ)
    (h₃ : r ≫ E = E ≫ π) : (θ ≫ r) ≫ E = E ≫ π ≫ Θ := by
  rw [h₁, Category.assoc, h₂, reassoc_of% h₃]

omit [IsCurve k pU] [Smooth pU] in
/-- **The conjugacy traces of `Tr_{A[H]}(π_U^* | RΓ_c(U_k̄, D(A[H])))` vanish**, for `A = ℤ/ℓⁿ`,
`U(k) = ∅`, granted perfectness of the complexes involved. -/
theorem conjugacyTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero
    [Algebra.IsAlgebraic k kbar] (ℓ n : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (hn : 1 ≤ n)
    [IsEmpty (rationalPoints pU)]
    (hperf : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf))))
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
        (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
              (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex (ZMod (ℓ ^ n)) C.toOver C.j
                (zmodSingleComplex.{u} ℓ n))))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.boundaryOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))))
    (hΓ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex (ZMod (ℓ ^ n))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)).obj)))
    (g : H) :
    Stacks.Trace.conjugacyTrace.{0, 0, u + 1} (ZMod (ℓ ^ n)) H g
      (perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ n)) H) ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0}
          (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf)))) = 0 := by
  let K' := (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0}
    (MonoidAlgebra (ZMod (ℓ ^ n)) H) U) 0).obj G.regularDescentSheaf
  let θ := Stacks.Trace.groupElementAction.{0, 0, u + 1} (ZMod (ℓ ^ n)) H g
  let E := compactSupportFrobeniusCohomologyRestrictScalarsIso
    (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H)) pU J kbar K'
  have hΦ := Stacks.Trace.preservesFiniteProjective_groupAlgebraRestriction.{0, 0, u + 1}
    (ZMod (ℓ ^ n)) H
  have hres : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((ModuleCat.restrictScalars.{u + 1}
        (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))).mapDerivedCategoryPlus.obj
        (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
          K'))) :=
    isPerfect_mapDerivedCategory_of_preservesFiniteProjective _ hΦ hperf
  have hY : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ n)) pU J kbar
        ((etaleModuleRestrictScalars (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
          U).mapCochainComplexPlus.obj K'))) :=
    (Functor.isPerfect_iff_of_iso (DerivedCategory.Plus.ι.mapIso E)).1 hres
  have hθπ := (Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θ).naturality
    (canonicalCompactSupportFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar p q hcard
      K')
  have hθ := compactSupportFrobeniusCohomologyRestrictScalarsIso_naturality
    (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H)) θ pU J kbar K'
  have hπ : (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} (ZMod (ℓ ^ n))
        H).mapDerivedCategoryPlus.map
        (canonicalCompactSupportFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar p q
          hcard K') ≫
        E.hom = E.hom ≫ canonicalCompactSupportFrobenius.{u, 0} (ZMod (ℓ ^ n)) pU J kbar p q hcard
          ((etaleModuleRestrictScalars (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
            U).mapCochainComplexPlus.obj K') :=
    restrictScalars_canonicalCompactSupportFrobenius
      (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H)) pU J kbar p q hcard K'
  have hconj : DerivedCategory.Plus.ι.map
        ((Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans θ).app
            (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
              K') ≫
          (ModuleCat.restrictScalars.{u + 1}
              (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n))
                (M := H))).mapDerivedCategoryPlus.map
            (canonicalCompactSupportFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar p q
              hcard K')) ≫ (DerivedCategory.Plus.ι.mapIso E).hom =
      (DerivedCategory.Plus.ι.mapIso E).hom ≫ DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} (ZMod (ℓ ^ n)) pU J kbar p q hcard
            ((etaleModuleRestrictScalars
              (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
                U).mapCochainComplexPlus.obj K') ≫
          (compactSupportFrobeniusFunctor.{u, 0} (ZMod (ℓ ^ n)) pU J kbar).map
            (etaleModuleRestrictScalarsComplexEndo
              (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H)) θ K')) := by
    simp only [Functor.mapIso_hom, ← Functor.map_comp]
    exact congrArg _ (comp_eq_of_comm_squares _ _ _ _ _ hθπ.symm hθ hπ)
  rw [Stacks.Trace.conjugacyTrace,
    ← perfectDerivedTrace_mapDerivedCategoryPlus _ θ hΦ _ hperf _ hres,
    perfectDerivedTrace_congr _ _ ⟨_, hY⟩ (DerivedCategory.Plus.ι.mapIso E) _ _ hconj,
    canonicalCompactSupportFrobenius_comp_map_eq_derivedTwistEndo]
  have : IsProper (Over.mk J.toBase).hom := inferInstanceAs (IsProper J.toBase)
  exact perfectDerivedTrace_groupElementAction_regularDescent_eq_zero (Over.mk J.toBase)
    (show J.immersion ≫ (Over.mk J.toBase).hom = pU from Over.w J.obj.hom) G C g kbar p q hcard
    ℓ n hℓ hn hY hZ hp₂ hp₃ hΓ


omit [IsCurve k pU] [Smooth pU] in
/-- **`Tr_{A[H]}(π_U^* | RΓ_c(U_k̄, D(A[H])))` dies in every quotient killed by `ℓ^m`**, for
`A = ℤ/ℓⁿ` with `n ≥ m + v` whenever `ℓ^v` divides `#H`, `U(k) = ∅`, granted perfectness. -/
theorem map_perfectDerivedTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero
    [Algebra.IsAlgebraic k kbar] (ℓ n : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (hn : 1 ≤ n)
    [IsEmpty (rationalPoints pU)]
    (hperf : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf))))
    (hZ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleGlobalSections.{u, 0} (ZMod (ℓ ^ n))
        (Spec (.of kbar))).rightDerivedFunctorPlus.obj
        ((etaleModuleDirectImage.{u, 0} (ZMod (ℓ ^ n))
          (pullback.snd C.toOver.hom (specAlgebraMap k kbar))).rightDerivedFunctorPlus.obj
          (DerivedCategory.Plus.Q.obj
            ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ n))
              (fieldBaseChangeProj C.toOver kbar)).mapCochainComplexPlus.obj
              (extensionByZeroConstantComplex (ZMod (ℓ ^ n)) C.toOver C.j
                (zmodSingleComplex.{u} ℓ n))))))))
    (hp₂ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.toOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))))
    (hp₃ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Plus.ι.obj (selfMapCohomology.{u, 0} (ZMod (ℓ ^ n))
        (pullback.snd C.boundaryOver.hom (specAlgebraMap k kbar))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)))))
    (hΓ : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2}
      (DerivedCategory.Q.obj (baseSectionsComplex (ZMod (ℓ ^ n))
        (etaleModuleConstantComplex (ZMod (ℓ ^ n)) kbar (zmodSingleComplex.{u} ℓ n)).obj)))
    {m : ℕ} {M : Type*} [AddCommGroup M]
    (Ψ : AdditiveCommutatorQuotient (MonoidAlgebra (ZMod (ℓ ^ n)) H) →+ M)
    (hM : ∀ y : M, (ℓ ^ m) • y = 0) (hnm : ∀ v : ℕ, ℓ ^ v ∣ Fintype.card H → m + v ≤ n) :
    Ψ (perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ n)) H) ⟨_, hperf⟩
        (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0}
          (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj G.regularDescentSheaf)))) = 0 :=
  Stacks.Trace.map_eq_zero_of_conjugacyTrace_eq_zero H _
    (fun g => conjugacyTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero J G C kbar p q
      hcard ℓ n hℓ hn hperf hZ hp₂ hp₃ hΓ g) Ψ hM hnm

end Stacks.EtaleCohomology

end
