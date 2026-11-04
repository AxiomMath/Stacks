module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantExtensionByZeroSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportIntegralCover
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ClopenInsideAffineOpen

/-!
# `H⁰_c` of a constant sheaf on an affine curve vanishes

Let `j : X ⟶ X̄` be a compactification over a finite field `k` and `k̄` an algebraically closed
extension. If every nonempty clopen subset of `X̄_k̄` meets the complement of `X_k̄`, then
`H⁰_c(X_k̄, M) = 0` for every constant sheaf `M`: it is `Γ(X̄_k̄, (j_! M)|_{X̄_k̄})`, and
`(j_! M)|_{X̄_k̄}` is the extension by zero of the constant sheaf `M` on `X_k̄`, which has no
nonzero global section (`isZero_extensionByZero_constant_smallEtaleIdObject`).

For an affine `V` with a smooth projective compactification `V̄` over `k` (such as a connected
finite étale cover of an affine smooth curve, `AlgebraicGeometry.CoverCompactification`) the
hypothesis holds: `V̄_k̄` is proper and smooth of relative dimension one and `V_k̄` is affine, so
no nonempty clopen subset of `V̄_k̄` lies in `V_k̄`
(`AlgebraicGeometry.eq_empty_of_isClopen_of_subset_range_of_isAffine`). This is the
non-projective assertion `H⁰_c(X_k̄, ℱ) = 0` of [Stacks, Tag 03VL] for a constant sheaf.

## Main results

* `Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_zero_constant`.
* `Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_zero_constant_of_isAffine`.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (Λ : Type) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)

/-- The reduced closed complement of `X_k̄` in `X̄_k̄`. -/
abbrev compactificationFieldBaseChangeComplement :
    Scheme.IdealSheafData (pullback j.toBase (specAlgebraMap k kbar)) :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range (compactificationFieldBaseChangeImmersion f j kbar).base)ᶜ,
      (compactificationFieldBaseChangeImmersion f j kbar).isOpenEmbedding.isOpen_range
        |>.isClosed_compl⟩ :
        TopologicalSpace.Closeds _)

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsAlgClosed kbar] in
/-- The image of `X_k̄` in `X̄_k̄` is the complement of the reduced closed complement
`compactificationFieldBaseChangeComplement`. -/
lemma range_compactificationFieldBaseChangeImmersion_eq :
    Set.range (compactificationFieldBaseChangeImmersion f j kbar).base =
      (Set.range (compactificationFieldBaseChangeComplement f j kbar).subschemeι.base)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact (compl_compl _).symm

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsAlgClosed kbar] in
/-- **`H⁰_c(X_k̄, M) = 0` for a constant sheaf `M`** as soon as every nonempty clopen subset of
`X̄_k̄` meets the complement of `X_k̄`. -/
theorem isZero_compactSupportFrobeniusCohomologyGroup_zero_constant
    (hY : ∀ Z : Set ↥(pullback j.toBase (specAlgebraMap k kbar) : Scheme.{u}), IsClopen Z →
      Z.Nonempty → ∃ y ∈ Z, y ∉ Set.range (compactificationFieldBaseChangeImmersion f j kbar)) :
    IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M),
        CochainComplex.plus_singleFunctor_obj _⟩ 0) := by
  let i := (compactificationFieldBaseChangeComplement f j kbar).subschemeι
  have hij := range_compactificationFieldBaseChangeImmersion_eq f j kbar
  have hY' : ∀ Z : Set ↥(pullback j.toBase (specAlgebraMap k kbar) : Scheme.{u}), IsClopen Z →
      Z.Nonempty → ∃ w, i w ∈ Z := by
    intro Z hZ hne
    obtain ⟨y, hyZ, hy⟩ := hY Z hZ hne
    obtain ⟨w, rfl⟩ : y ∈ Set.range i.base := by
      rwa [← compl_compl (Set.range i.base), ← hij]
    exact ⟨w, hyZ⟩
  let MYb := (constantSheaf (pullback j.toBase (specAlgebraMap k kbar)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).obj M
  let G := (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
  let e : G ≅ (etaleModuleExtensionByZero.{u, 0} Λ
      (compactificationFieldBaseChangeImmersion f j kbar)).obj
      ((etaleModuleRestriction.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar)).obj
        MYb) :=
    ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} Λ f j kbar).app _).symm ≪≫
      (etaleModuleExtensionByZero.{u, 0} Λ
          (compactificationFieldBaseChangeImmersion f j kbar)).mapIso
        ((etaleModuleInverseImageConstantIso.{u, 0} Λ
            (pullback.fst f (specAlgebraMap k kbar))).app M ≪≫
          ((etaleModuleInverseImageConstantIso.{u, 0} Λ
            (compactificationFieldBaseChangeImmersion f j kbar)).app M).symm ≪≫
          (etaleModuleInverseImageRestrictionIso.{u, 0} Λ
            (compactificationFieldBaseChangeImmersion f j kbar)).app MYb)
  have hG : IsZero
      (G.obj.obj (op (smallEtaleIdObject (pullback j.toBase (specAlgebraMap k kbar))))) :=
    (isZero_extensionByZero_constant_smallEtaleIdObject Λ M i
        (compactificationFieldBaseChangeImmersion f j kbar) hij hY').of_iso
      ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
        (op (smallEtaleIdObject (pullback j.toBase (specAlgebraMap k kbar))))).mapIso e)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ ((0 : ℕ) : ℤ)).mapIso
    (compactSupportFrobeniusCohomologySingleIso f j kbar
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))
  refine isZero_homology_derivedDirectImageSections_of_subsingleton_sheafH Λ _ G 0 ?_
  have hs : Subsingleton
      (((etaleModuleUnderlyingAbelian (pullback j.toBase (specAlgebraMap k kbar)) Λ).obj G).obj.obj
        (op (smallEtaleIdObject (pullback j.toBase (specAlgebraMap k kbar))))) :=
    have := ModuleCat.subsingleton_of_isZero hG
    ⟨fun a b => Subsingleton.elim
      (α := G.obj.obj (op (smallEtaleIdObject (pullback j.toBase (specAlgebraMap k kbar))))) a b⟩
  exact @Equiv.subsingleton _ _
    (Sheaf.H.equiv₀ _
      (isTerminalSmallEtaleIdObject (pullback j.toBase (specAlgebraMap k kbar)))).toEquiv hs

section Cover

variable {k : Type u} [Field k] [Finite k] {U Ub V : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] {pUb : Ub ⟶ Spec (.of k)} [IsProper pUb] {jU : U ⟶ Ub}
  [IsOpenImmersion jU] (hjU : jU ≫ pUb = pU) {f : V ⟶ U} [IsFinite f] [Etale f] [ConnectedSpace V]
  (C : CoverCompactification k pUb jU f) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (Λ : Type) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)

omit [IsAlgClosed kbar] in
/-- **`H⁰_c(V_k̄, M) = 0` for a constant sheaf on an affine curve `V`** with a smooth projective
compactification `V̄` over the finite field `k`: no nonempty clopen subset of `V̄_k̄` lies in the
affine `V_k̄`. -/
theorem isZero_compactSupportFrobeniusCohomologyGroup_zero_constant_of_isAffine [IsAffine V]
    [LocallyOfFiniteType (f ≫ pU)] [QuasiCompact (f ≫ pU)] [IsSeparated (f ≫ pU)] :
    IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ (f ≫ pU) (C.compactification hjU) kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj
        ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M),
        CochainComplex.plus_singleFunctor_obj _⟩ 0) := by
  refine isZero_compactSupportFrobeniusCohomologyGroup_zero_constant (f ≫ pU)
    (C.compactification hjU) kbar Λ M fun Z hZ hne => ?_
  have : SmoothOfRelativeDimension 1
      (pullback.snd (C.compactification hjU).toBase (specAlgebraMap k kbar)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) (inferInstanceAs (SmoothOfRelativeDimension 1 C.q))
  by_contra! hcon
  exact hne.ne_empty (eq_empty_of_isClopen_of_subset_range_of_isAffine
    (pullback.snd (C.compactification hjU).toBase (specAlgebraMap k kbar))
    (compactificationFieldBaseChangeImmersion (f ≫ pU) (C.compactification hjU) kbar) Z hZ hcon)

end Cover

end Stacks.EtaleCohomology

end
