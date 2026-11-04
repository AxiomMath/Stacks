module

public import StacksFrontier.AlgebraicGeometry.ProEtale.QuasiCompactFinalObject
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenPoint
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.LocallyConstantTrivialization
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemProDominated
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.AdicReductionSections
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.AdicCompletionModel
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Module.AdicSystem.RowReductionHomology
public import StacksFrontier.Topology.Sheaves.Modules.StalkKFlat

/-!
# Mittag-Leffler for the sections of the reductions of a complex with constant reductions

Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an ideal and `K`
an object of the derived category of sheaves of `Λ`-modules on `X_proét`. Suppose that every
reduction `K ⊗_Λ^L Λ/Iⁿ` is isomorphic in `D(X_proét, Λ/Iⁿ)` to the constant complex
`\underline{E_n}` of an object `E_n` of `D(Λ/Iⁿ)`, and that `E_1` is pseudo-coherent. Then the
inverse system `n ↦ H⁰(X, K ⊗_Λ^L \underline{Λ/Iⁿ})` satisfies the Mittag-Leffler condition.

This is the core of Stacks 09C5. The argument does not compare the `E_n` along transition maps,
which need not be compatible:

* for a K-flat complex `P` representing `K` and a point `x` of `X`, each `E_n` is the reduction
  `Λ/Iⁿ ⊗_Λ N` of the fibre `N` of `P` at the point of `X_proét` attached to `x`
  (`Stacks.ModuleSheaf.nonempty_iso_extendScalars_sheafFiber`);
* the tower of the reductions of `N`, the first of them pseudo-coherent, has an adic model, a
  bounded above complex `F` of finite free modules over the completion `Λ^∧` with
  `Λ/Iⁿ ⊗_{Λ^∧} F ≅ Λ/Iⁿ ⊗_Λ N` (Stacks 0CQF,
  `StacksDraft.DerivedInverseLimit.exists_isBoundedAboveFiniteFree_adicCompletion_iso`);
* the sections system of the reductions of the constant complex `\underline{F}` is
  `j ↦ Γ(X, \underline{H⁰(F/IʲF)})`, which is Mittag-Leffler because sections over `X` are exact
  and the cohomology of the adic reductions of a complex of finite modules over a Noetherian
  ring is Mittag-Leffler by the Artin–Rees lemma;
* for each `n` the isomorphism of the `n`-th reductions of `P` and `\underline{F}` identifies
  the truncations of the two sections systems to the indices `j ≤ n`, and the Mittag-Leffler
  condition depends only on such truncations
  (`Stacks.ModuleSheaf.isMittagLefflerCategorical_reductionSections_of_adicModel`).

## Main results

* `AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_comp_constantSheaf_comp_sheafSections`:
  over a weakly contractible affine scheme, global sections of the constant sheaves attached to a
  Mittag-Leffler system of modules form a Mittag-Leffler system.
* `AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_constantComplexReductionSections`:
  the sections of the reductions of a constant complex of finite modules form a Mittag-Leffler
  system.
* `AlgebraicGeometry.ProEtale.exists_isBoundedAboveFiniteFree_extendScalars_iso`: the adic
  model of a K-flat complex with constant reductions.
* `AlgebraicGeometry.ProEtale.derivedReductionSectionsSystem`: the inverse system
  `n ↦ H⁰(X, K ⊗_Λ^L \underline{Λ/Iⁿ})`.
* `AlgebraicGeometry.ProEtale.isMittagLefflerCategorical_reductionSections_of_constant`: the
  Mittag-Leffler condition for the sections of the reductions.

## References

* [Stacks Project, Tag 09C5](https://stacks.math.columbia.edu/tag/09C5)
* [Stacks Project, Tag 0CQF](https://stacks.math.columbia.edu/tag/0CQF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

section Sections

variable {X : Scheme.{u}} [IsAffine X] (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
  (R : Type (max (u + 1) w)) [CommRing R]
include hX

/-- Global sections of sheaves of modules over a weakly contractible affine scheme, taken over
the chosen final object of `X_proét`, are exact. -/
theorem preservesFiniteColimits_sheafSections_terminal_of_isWeaklyContractibleObj :
    PreservesFiniteColimits ((sheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} R)).obj (op (⊤_ X.ProEt))) := by
  have := Scheme.ProEt.preservesFiniteColimits_sheafSections_mk_id hX R
  exact preservesFiniteColimits_of_natIso ((sheafSections (Scheme.ProEt.topology X)
    (ModuleCat.{max (u + 1) w} R)).mapIso
      (terminalIsTerminal.uniqueUpToIso (Scheme.ProEt.isTerminal_mk_id (X := X))).op)

/-- **Mittag-Leffler for global sections of constant sheaves.** Over a weakly contractible
affine scheme `X`, the global sections of the constant sheaves `\underline{G_n}` attached to a
Mittag-Leffler inverse system of modules `G` form a Mittag-Leffler inverse system: the constant
sheaf functor and global sections over `X` are both exact. -/
theorem isMittagLefflerCategorical_comp_constantSheaf_comp_sheafSections
    {G : ℕᵒᵖ ⥤ ModuleCat.{max (u + 1) w} R} (hG : IsMittagLefflerCategorical G) :
    IsMittagLefflerCategorical (G ⋙ constantSheaf (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} R) ⋙ (sheafSections (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} R)).obj (op (⊤_ X.ProEt))) := by
  have := preservesFiniteColimits_sheafSections_terminal_of_isWeaklyContractibleObj.{u, w} hX R
  let U := constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R) ⋙
    (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)).obj
      (op (⊤_ X.ProEt))
  have : U.Additive := U.additive_of_preserves_binary_products
  exact hG.map G U

section ConstantModel

attribute [local instance] Sheaf.monoidalCategory Stacks.ModuleSheaf.derivedMonoidal

/-- **Mittag-Leffler for sections of the reductions of a constant complex.** Over a weakly
contractible affine scheme `X`, let `F` be a complex of finite modules over a Noetherian ring
`R` whose constant complex `\underline{F}` is K-flat, and `𝔞 ⊆ R` an ideal. Then the inverse
system `j ↦ Γ(X, H⁰(\underline{F} ⊗_R^L \underline{R/𝔞ʲ}))`, read over any ring mapping to `R`,
is Mittag-Leffler: it is `j ↦ Γ(X, \underline{H⁰(F/𝔞ʲF)})`, and the cohomology of the adic
reductions of `F` is Mittag-Leffler by the Artin–Rees lemma. -/
theorem isMittagLefflerCategorical_constantComplexReductionSections [IsNoetherianRing R]
    (𝔞 : Ideal R) (F : CochainComplex (ModuleCat.{max (u + 1) w} R) ℤ)
    (hF : ∀ n, Module.Finite R (F.X n))
    (hW : CochainComplex.KFlatBifunctor.KFlatLeft
      (MonoidalCategory.curriedTensor (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} R)))
      (((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F))
    {B : Type (max (u + 1) w)} [CommRing B] (φ : B →+* R) :
    IsMittagLefflerCategorical
      (adicQuotientModuleSystem R 𝔞 (ModuleCat.of R R) ⋙
        constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R) ⋙
          DerivedCategory.singleFunctor _ 0 ⋙ MonoidalCategory.tensorLeft (DerivedCategory.Q.obj
            (((constantSheaf (Scheme.ProEt.topology X)
              (ModuleCat.{max (u + 1) w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)) ⋙
            DerivedCategory.homologyFunctor _ 0 ⋙
              (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)).obj
                (op (⊤_ X.ProEt)) ⋙
                ModuleCat.restrictScalars.{max (u + 1) w} φ) := by
  have h0 :=
    Stacks.PseudoCoherent.AdicCompletion.isMittagLefflerCategorical_adicQuotient_rowFunctor_homology
      𝔞 F hF 0
  have h1 := (isMittagLefflerCategorical_comp_constantSheaf_comp_sheafSections hX R h0).map _
    (ModuleCat.restrictScalars.{max (u + 1) w} φ)
  exact IsMittagLefflerCategorical.of_natIso
    (Functor.isoWhiskerLeft (adicQuotientModuleSystem R 𝔞 (ModuleCat.of R R))
      (Functor.isoWhiskerRight
        (Stacks.ModuleSheaf.constantComplexReductionSectionsIso F hW (⊤_ X.ProEt))
        (ModuleCat.restrictScalars.{max (u + 1) w} φ))) h1

end ConstantModel

end Sections

section Defs

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
  CochainComplex.braidedCategory Stacks.ModuleSheaf.derivedMonoidal

variable (X : Scheme.{u})

/-- The constant complex functor `D(R) ⥤ D(X_proét, R)`: the derived functor of the exact
constant sheaf functor. -/
abbrev constantDerivedFunctor (R : Type (max (u + 1) w)) [CommRing R] :
    DerivedCategory (ModuleCat.{max (u + 1) w} R) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)) :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)).mapDerivedCategory

/-- The inverse system `n ↦ H⁰(X, K ⊗_Λ^L \underline{Λ/Iⁿ})` of `Λ`-modules attached to an object
`K` of the derived category of sheaves of `Λ`-modules on `X_proét`: the derived tensor product
of `K` with the tower of constant sheaves `n ↦ \underline{Λ/Iⁿ}` placed in degree zero, whose
transition maps are induced by the reductions `Λ/Iⁿ⁺¹ → Λ/Iⁿ`, followed by degree-zero
cohomology and sections over the final object of `X_proét`. -/
def derivedReductionSectionsSystem (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) :
    ℕᵒᵖ ⥤ ModuleCat.{max (u + 1) w} Λ :=
  adicQuotientModuleSystem Λ I (ModuleCat.of Λ Λ) ⋙
    constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) ⋙
      DerivedCategory.singleFunctor _ 0 ⋙ tensorLeft K ⋙
        DerivedCategory.homologyFunctor _ 0 ⋙
          (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
            (op (⊤_ X.ProEt))

variable {X}

/-- Over the empty scheme the final object of `X_proét` is covered by the empty sieve, so the
sections over it of every sheaf vanish. -/
theorem subsingleton_sheafSections_terminal_of_isEmpty [IsEmpty X] {R : Type (max (u + 1) w)}
    [CommRing R] (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)) :
    Subsingleton (((sheafSections (Scheme.ProEt.topology X)
      (ModuleCat.{max (u + 1) w} R)).obj (op (⊤_ X.ProEt))).obj F) := by
  have hZ : (⊥ : Sieve (⊤_ X.ProEt)) ∈ Scheme.ProEt.topology X (⊤_ X.ProEt) :=
    Scheme.ProEt.bot_mem_topology_of_isEmpty _
      ⟨fun z => isEmptyElim (show X from (⊤_ X.ProEt).hom.base z)⟩
  exact ModuleCat.isZero_iff_subsingleton.1 (Sheaf.isTerminalOfBotCover _ _ hZ).isZero

/-- Extension of scalars of a K-flat complex of sheaves of modules on `X_proét` is K-flat in the
first variable of the tensor product. -/
theorem kFlatLeft_extendScalars_of_kFlat {R S : Type (max (u + 1) w)} [CommRing R] [CommRing S]
    (f : R →+* S)
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)) ℤ}
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R))) P) :
    CochainComplex.KFlatBifunctor.KFlatLeft
      (curriedTensor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} S)))
      (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X) f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _
    (Stacks.ModuleSheaf.kFlat_extendScalars (Scheme.ProEt.topology X) f hP)

/-- The constant complex of a bounded above complex of finite free modules is K-flat. -/
theorem kFlat_constantSheaf_of_isBoundedAboveFiniteFree {R : Type (max (u + 1) w)} [CommRing R]
    {F : CochainComplex (ModuleCat.{max (u + 1) w} R) ℤ}
    (hF : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree F) :
    CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} R)))
      (((constantSheaf (Scheme.ProEt.topology X)
        (ModuleCat.{max (u + 1) w} R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) := by
  let J := Scheme.ProEt.topology X
  let cA := constantSheaf J (ModuleCat.{max (u + 1) w} R)
  let W := (cA.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  obtain ⟨b, hb⟩ := hF.upperBound
  have : CochainComplex.IsStrictlyLE W b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun k hk => cA.map_isZero (F.isZero_of_isStrictlyLE b k hk)
  exact Stacks.ModuleSheaf.kFlat_of_isStrictlyLE W b fun n => by
    have := (hF.finiteFree n).2
    exact Stacks.ModuleSheaf.sheafifiedFree_constantSheaf_obj J (F.X n)

end Defs

section Reduction

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
  CochainComplex.braidedCategory Stacks.ModuleSheaf.derivedMonoidal

variable {X : Scheme.{u}} [IsAffine X] (hX : ProetaleWContractible.IsWeaklyContractibleObj X)
  {Λ : Type (max (u + 1) w)} [CommRing Λ] (I : Ideal Λ)
include hX

/-- **The adic model of a K-flat complex with constant reductions.** Let `X` be a nonempty
weakly contractible affine scheme, `Λ` a ring, `I ⊆ Λ` an ideal and `P` a K-flat complex of
sheaves of `Λ`-modules on `X_proét` all of whose reductions `Λ/Iⁿ⁺¹ ⊗_Λ P` are isomorphic in
`D(X_proét, Λ/Iⁿ⁺¹)` to constant complexes `\underline{E_n}`, the first `E_0` being
pseudo-coherent. Then there is a bounded above complex `F` of finite free modules over the
completion `Λ^∧` such that for every `n` the reductions `Λ/Iⁿ⁺¹ ⊗_Λ P` and
`Λ/Iⁿ⁺¹ ⊗_{Λ^∧} \underline{F}` are isomorphic in `D(X_proét, Λ/Iⁿ⁺¹)`.

Indeed `E_n` is the reduction `Λ/Iⁿ⁺¹ ⊗_Λ N` of the fibre `N` of `P` at a point of `X_proét`,
and Stacks 0CQF, applied to the tower of the reductions of `N`, produces `F`. The isomorphisms
need not be compatible as `n` varies. -/
theorem exists_isBoundedAboveFiniteFree_extendScalars_iso [Nonempty X]
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P)
    (hconst : ∀ n : ℕ, ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1))),
      Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        (constantDerivedFunctor X (Λ ⧸ I ^ (n + 1))).obj E))
    (hE₀ : ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ 1)),
      StacksDraft.PseudoCoherence.IsPseudoCoherent E ∧
      Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk (I ^ 1))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        (constantDerivedFunctor X (Λ ⧸ I ^ 1)).obj E)) :
    ∃ F : CochainComplex (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ)) ℤ,
      StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree F ∧ ∀ n : ℕ,
        Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
          DerivedCategory.Q.obj
            (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
              (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              (((constantSheaf (Scheme.ProEt.topology X)
                (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ))).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj F))) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let J := Scheme.ProEt.topology X
  let Φ := Scheme.ProEt.clopenPoint hX x
  let N := ((Stacks.ModuleSheaf.moduleSheafFiber Λ Φ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  have hN : ∀ n : ℕ, CochainComplex.KFlat.{max (u + 1) w, max (u + 1) w}
      (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N) := fun n =>
    kFlat_baseChange _ _
      ((CochainComplex.kFlat_iff_kFlatBifunctor N).2 (Stacks.ModuleSheaf.kFlat_sheafFiber Φ hP))
  have hE : ∀ n : ℕ, ∀ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1))),
      Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars J
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        (constantDerivedFunctor X (Λ ⧸ I ^ (n + 1))).obj E) →
      Nonempty (E ≅ DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N)) := fun n E ⟨e₀⟩ =>
    Stacks.ModuleSheaf.nonempty_iso_extendScalars_sheafFiber Φ _ hP E
      (Stacks.ModuleSheaf.derivedExtendScalarsObjIso J _ hP ≪≫ e₀)
  have hN₀ : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj
      (((ModuleCat.extendScalars (Ideal.Quotient.mk (I ^ 1))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)) := by
    obtain ⟨E, hEpc, he⟩ := hE₀
    obtain ⟨e₁⟩ := hE 0 E he
    exact hEpc.ofIso e₁
  obtain ⟨F, hF, hFN⟩ :=
    StacksDraft.DerivedInverseLimit.exists_isBoundedAboveFiniteFree_adicCompletion_iso I N hN hN₀
  refine ⟨F, hF, fun n => ?_⟩
  obtain ⟨E, ⟨e₀⟩⟩ := hconst n
  obtain ⟨e₁⟩ := hE n E ⟨e₀⟩
  obtain ⟨e₂⟩ := hFN n
  let f := (AdicCompletion.evalₐ I (n + 1)).toRingHom
  let cS := constantSheaf J (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1)))
  exact ⟨e₀ ≪≫ cS.mapDerivedCategory.mapIso (e₁ ≪≫ e₂.symm) ≪≫
    cS.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso
        (Stacks.ModuleSheaf.extendScalarsConstantSheafIso J f).symm (ComplexShape.up ℤ)).app F ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).app F).symm)⟩

/-- The comparison step of the Mittag-Leffler argument: a K-flat complex `P` whose reductions are
those of the constant complex of a bounded above complex `F` of finite free modules over the
completion `Λ^∧`, by isomorphisms which need not be compatible as `n` varies, has
Mittag-Leffler sections of its derived reductions. -/
theorem isMittagLefflerCategorical_reductionSections_of_adicModel [IsNoetherianRing Λ]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (eP : DerivedCategory.Q.obj P ≅ K)
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P)
    {F : CochainComplex (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ)) ℤ}
    (hF : StacksDraft.PseudoCoherence.IsBoundedAboveFiniteFree F)
    (hψ : ∀ n : ℕ,
        Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
          DerivedCategory.Q.obj
            (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
              (AdicCompletion.evalₐ I (n + 1)).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj
              (((constantSheaf (Scheme.ProEt.topology X)
                (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ))).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj F)))) :
    IsMittagLefflerCategorical (derivedReductionSectionsSystem X Λ I K) := by
  have hW := kFlat_constantSheaf_of_isBoundedAboveFiniteFree (X := X) hF
  have hW' := CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hW
  exact Stacks.ModuleSheaf.isMittagLefflerCategorical_reductionSections_of_adicModel I
    (IsNoetherian.noetherian I) (⊤_ X.ProEt) eP
    (CochainComplex.KFlatMonoidal.kFlatLeft_of_kFlat _ hP)
    (fun n => kFlatLeft_extendScalars_of_kFlat _ hP)
    hW' (fun n => kFlatLeft_extendScalars_of_kFlat _ hW) (fun n => (hψ n).some)
    (isMittagLefflerCategorical_constantComplexReductionSections hX _ (I.map (algebraMap Λ _)) F
      (fun n => (hF.finiteFree n).1) hW'
      (algebraMap Λ _))

/-- **Mittag-Leffler for the sections of the reductions of a complex with constant
reductions.** Let `X` be a weakly contractible affine scheme, `Λ` a Noetherian ring, `I ⊆ Λ` an
ideal and `K` an object of the derived category of sheaves of `Λ`-modules on `X_proét`,
represented by a K-flat complex `P`. Suppose that every reduction `Λ/Iⁿ⁺¹ ⊗_Λ P` is isomorphic
in `D(X_proét, Λ/Iⁿ⁺¹)` to a constant complex `\underline{E_n}`, with `E_0` pseudo-coherent.
Then the inverse system `n ↦ H⁰(X, K ⊗_Λ^L \underline{Λ/Iⁿ})` is Mittag-Leffler. -/
theorem isMittagLefflerCategorical_reductionSections_of_constant [IsNoetherianRing Λ]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (eP : DerivedCategory.Q.obj P ≅ K)
    (hP : CochainComplex.KFlatBifunctor.KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P)
    (hconst : ∀ n : ℕ, ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ (n + 1))),
      Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        (constantDerivedFunctor X (Λ ⧸ I ^ (n + 1))).obj E))
    (hE₀ : Nonempty X → ∃ E : DerivedCategory (ModuleCat.{max (u + 1) w} (Λ ⧸ I ^ 1)),
      StacksDraft.PseudoCoherence.IsPseudoCoherent E ∧
      Nonempty (DerivedCategory.Q.obj
          (((Stacks.ModuleSheaf.extendScalars (Scheme.ProEt.topology X)
            (Ideal.Quotient.mk (I ^ 1))).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
        (constantDerivedFunctor X (Λ ⧸ I ^ 1)).obj E)) :
    IsMittagLefflerCategorical (derivedReductionSectionsSystem X Λ I K) := by
  rcases isEmpty_or_nonempty X with hXe | hXne
  · refine isMittagLefflerCategorical_of_forall_exists_range_eq _ fun i =>
      ⟨i, le_rfl, fun k _ => ?_⟩
    have : Subsingleton ((derivedReductionSectionsSystem X Λ I K).obj (op i)) :=
      subsingleton_sheafSections_terminal_of_isEmpty _
    exact Subsingleton.elim _ _
  obtain ⟨F, hF, hψ⟩ := exists_isBoundedAboveFiniteFree_extendScalars_iso (Λ := Λ) hX I (P := P)
    hP hconst (hE₀ hXne)
  exact isMittagLefflerCategorical_reductionSections_of_adicModel hX I eP hP hF hψ

end Reduction

end AlgebraicGeometry.ProEtale

end
