module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsUniversalModel
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsCechBaseChange
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsObstructionOverBase
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsPerfectComplex

/-!
# The obstruction spaces of Stacks 07YH are the degree-one cohomology of `N ⊗_Λ M`

Let `Λ` be Noetherian, let `g : W ⟶ Spec Λ` be proper and let `𝓕` be a coherent `𝒪_W`-module
flat over `Λ`.  [Stacks, Tag 07VL] supplies a finite complex `N` of finite projective
`Λ`-modules which universally computes the cohomology of `𝓕`, and [Stacks, Tag 07YW] asserts
that the obstruction spaces of the obstruction theory of [Stacks, Tag 07YH] are

`𝒪_x(M) = H¹(N ⊗_Λ M)`

for every `Λ`-algebra `A` and every `A`-module `M`.  This file proves that.

The obstruction space is `H¹(W_A, 𝓕_A ⊗_A M)` — the value at `M` of
`Deformation.Artin.SectionsSheaf.obstructionFunctor` — and the right-hand side is the degree-one
homology of `M ⊗_A (N ⊗_Λ A)`, whose degree-`i` term is `M ⊗_Λ Nⁱ` by
`Deformation.Artin.SectionsPerfectComplex.tensorComplexXLinearEquiv`.  Composing with
`Deformation.Artin.SectionsPerfectComplex.nonempty_derivedCohomology_two_iso_homology_one` turns
it into the source's reformulation `𝒪_x(M) = H²(K ⊗^𝐋_A M)` with `K = (N ⊗_Λ A)[-1]`.

## The chain

Writing `U` for a finite affine open cover of `W` with affine finite intersections and `U'` for
its inverse image on `W_A`:

1. `𝒪_x(M) = H¹(W_A, 𝓕_A ⊗_A M) ≅ H¹` of the `A`-linear alternating Čech model of
   `𝓕_A ⊗_A M` — `obstructionFunctorHomologyIso`, which is
   `Deformation.Artin.SectionsSheaf.cohomologyRestrictIso` followed by
   `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.homologyBaseAlternatingCechComplexIso`;
2. the model of `𝓕_A ⊗_A M` is `M ⊗_A` the model of `𝓕_A` —
   `Deformation.Artin.SectionsCechBaseChange.baseAlternatingCechTensorIso`;
3. the model of `𝓕_A` and `N ⊗_Λ A` are isomorphic in `D(A)` and both K-flat, so they have the
   same `M ⊗_A -` homology — `nonempty_homology_tensorComplex_iso`.

## Main definitions

* `Deformation.Artin.SectionsObstructionModel.obstructionFunctorHomologyIso`: step 1.

## Main results

* `…SectionsObstructionModel.nonempty_derivedTensorProduct_single_iso_of_iso`: the derived
  tensor product `M[0] ⊗^𝐋 Y` is the degreewise `M ⊗_A G` for **any** K-flat `G` representing
  `Y`, not only for `Y = Q(G)`.  Stated this way it needs no functoriality of the derived tensor
  product in its first variable, which is not available.
* `…SectionsObstructionModel.nonempty_homology_tensorComplex_iso`: **a derived isomorphism
  between two K-flat complexes survives tensoring with a module**, degreewise, on homology.
* `…SectionsObstructionModel.flat_baseAlternatingCechComplexBaseChange_X`: the Čech model on the
  base change is termwise flat over the new base.
* `…SectionsObstructionModel.exists_finiteProjectiveModel_obstructionSpace`: **the assertion**,
  with the source's hypotheses and no others.
* `…SectionsObstructionModel.exists_finiteProjectiveModel_homology_iso_obstruction`: the complex
  `N` of the source and the degree-two reformulation, with no carried input.

## Implementation notes

**Flatness of `𝓕_A` over `A` is never used, and could not be.**  [Stacks, Tag 05VW] — base
change of flatness of a sheaf — is not proved in this development.  Termwise flatness of the
model on `W_A` is instead read off
`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexBaseChangeIso`: that
model *is* the extension of scalars along `Λ → A` of the model downstairs, which is termwise flat
over `Λ` because `𝓕` is flat over `Λ`, and extension of scalars carries a flat module to a flat
module.

**`SectionsSheaf.wComparison` is not used.**  `Deformation.Artin.SectionsSheaf.abCohomology` is
the cohomology δ-functor postcomposed with `forget₂ (ModuleCat R) AddCommGrpCat`, so
`wComparison` compares functors into `AddCommGrpCat`; routing this statement through it would
give an isomorphism of abelian groups where the source asserts one of `A`-modules.  The
comparison used here, `SectionsSheaf.cohomologyRestrictIso`, stays in `ModuleCat A`.

**Why a separate module.**  The three assertions of the tag would naturally sit together in
`StacksFrontier/Deformation/Artin/Obstruction/SectionsPerfectComplex.lean`, but the Čech comparison
of step 2 imports that file, so the carrier for this assertion cannot live there.

## References

* [Stacks Project, Tag 07YW](https://stacks.math.columbia.edu/tag/07YW)
* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

namespace Deformation.Artin.SectionsObstructionModel

attribute [local instance 10000] HasDerivedCategory.standard

open Deformation.Artin.SectionsPerfectComplex

variable {A : Type u} [CommRing A]

/-- `nonempty_derivedTensorProduct_single_iso` for an arbitrary derived object with a K-flat
representative. -/
theorem nonempty_derivedTensorProduct_single_iso_of_iso
    (Y : DerivedCategory (ModuleCat.{u} A))
    (G : CochainComplex (ModuleCat.{u} A) ℤ) (hG : CochainComplex.KFlat.{u, u} G)
    (e : DerivedCategory.Q.obj G ≅ Y) (M : ModuleCat.{u} A) :
    Nonempty ((CochainComplex.DerivedTensor.derivedTensorProduct.{u, u, _} Y).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      DerivedCategory.Q.obj ((tensorComplex M).obj G)) := by
  obtain ⟨α⟩ :=
    (CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution.{u, u, _}
      Y G G (𝟙 G) hG
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app G ≪≫ e)).1
  refine ⟨?_⟩
  refine (CochainComplex.DerivedTensor.derivedTensorProduct.{u, u, _} Y).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M ≪≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app _).symm) ≪≫ ?_
  refine α.app _ ≪≫ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app _ ≪≫ ?_
  exact DerivedCategory.Q.mapIso
    (HomologicalComplex.mapBifunctorSingleLeftIso (curriedTensor (ModuleCat.{u} A)) M G)

/-- **A derived isomorphism between two K-flat complexes is an isomorphism after tensoring with
a module.** -/
theorem nonempty_homology_tensorComplex_iso
    (C D : CochainComplex (ModuleCat.{u} A) ℤ)
    (hC : CochainComplex.KFlat.{u, u} C) (hD : CochainComplex.KFlat.{u, u} D)
    (e : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj D) (M : ModuleCat.{u} A) (i : ℤ) :
    Nonempty (((tensorComplex M).obj C).homology i ≅ ((tensorComplex M).obj D).homology i) := by
  obtain ⟨eC⟩ := nonempty_derivedTensorProduct_single_iso_of_iso
    (DerivedCategory.Q.obj D) C hC e M
  obtain ⟨eD⟩ := nonempty_derivedTensorProduct_single_iso_of_iso
    (DerivedCategory.Q.obj D) D hD (Iso.refl _) M
  have eQ : DerivedCategory.Q.obj ((tensorComplex M).obj C) ≅
      DerivedCategory.Q.obj ((tensorComplex M).obj D) := eC.symm ≪≫ eD
  exact ⟨((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eQ ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app _⟩

/-! ### Termwise flatness of the base-changed Čech model -/

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

/-- **The `A`-linear Čech model on the base change is termwise flat over `A`.**  Stacks 05VW —
base change of flatness of a sheaf — is not available; instead the model on the base change is
the extension of scalars of the model downstairs
(`baseAlternatingCechComplexBaseChangeIso`), which is termwise flat over `Λ`, and extension of
scalars carries a flat module to a flat module. -/
theorem flat_baseAlternatingCechComplexBaseChange_X
    {Λ A : Type u} [CommRing Λ] [CommRing A] (φ : Λ →+* A)
    {W W' : Scheme.{u}} {g : W ⟶ Spec (.of Λ)} [IsSeparated g] {g' : W' ⟶ Spec (.of A)}
    {p : W' ⟶ W} (hsq : IsPullback p g' g (Spec.map (CommRingCat.ofHom φ)))
    (F : W.Modules) [F.IsQuasicoherent] {I : Type u} [Finite I]
    (U : I → W.Opens) (hU : (⊤ : W.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))
    (hflat : IsFlatOver g.toLRSHom.toShHom F) (n : ℤ) :
    Module.Flat A ((baseAlternatingCechComplex g' (fun i ↦ p ⁻¹ᵁ U i)
      (top_eq_iSup_preimage p U hU) ((Scheme.Modules.pullback p).obj F)).X n) := by
  let : Algebra Λ A := φ.toAlgebra
  have h1 := flat_baseAlternatingCechComplex_X g U hU F hUaff hflat n
  have hbase : Module.Flat A
      ((HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n).obj
        (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (baseAlternatingCechComplex g U hU F))) := by
    change Module.Flat A (TensorProduct Λ A ((baseAlternatingCechComplex g U hU F).X n : Type u))
    infer_instance
  exact Module.Flat.of_linearEquiv
    ((HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n).mapIso
      (baseAlternatingCechComplexBaseChangeIso φ hsq F U hU hUaff)).symm.toLinearEquiv

/-! ### The obstruction module as the homology of the Čech model -/

open Deformation.Artin.SectionsSheaf

/-- **The obstruction module of Stacks 07YH is the degree-one homology of the `A`-linear
alternating Čech model of `𝓕 ⊗_A M`.** -/
def obstructionFunctorHomologyIso {A : Type u} [CommRing A] {X : Scheme.{u}}
    (π : X ⟶ Spec (CommRingCat.of A)) (F : X.Modules) {I : Type u} [LinearOrder I]
    (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))
    (M : ModuleCat.{u} A) [F.IsQuasicoherent] :
    (obstructionFunctor π F).obj M ≅
      (baseAlternatingCechComplex π U hU ((tensorSheafFunctor π F).obj M)).homology 1 :=
  ((cohomologyRestrictIso π 1).app ((tensorSheafFunctor π F).obj M)).symm ≪≫
    (homologyBaseAlternatingCechComplexIso π U hU ((tensorSheafFunctor π F).obj M) haff 1).symm

/-! ### Assertion (b) of Stacks 07YW -/

open Deformation.Artin.SectionsPerfectComplex (tensorComplex)
open Deformation.Artin.SectionsCechBaseChange (baseAlternatingCechTensorIso)

/-- **[Stacks, Tag 07YW], the obstruction spaces.** Let `Λ` be Noetherian, let
`g : W ⟶ Spec Λ` be proper and let `𝓕` be a coherent `𝒪_W`-module flat over `Λ`. Then there is a
finite complex `N` of finite projective `Λ`-modules such that, for every `Λ`-algebra `A`, every
cartesian square exhibiting `W_A` as the base change of `W`, and every `A`-module `M`,

`𝒪_x(M) = H¹(W_A, 𝓕_A ⊗_A M) ≅ H¹((N ⊗_Λ A) ⊗_A M)`,

the obstruction space of the obstruction theory of [Stacks, Tag 07YH] at `M`. In degree `i` the
right-hand complex is `M ⊗_Λ Nⁱ` by
`Deformation.Artin.SectionsPerfectComplex.tensorComplexXLinearEquiv`, so the right-hand side is
the source's `H¹(N ⊗_Λ M)`.

Composed with
`Deformation.Artin.SectionsPerfectComplex.nonempty_derivedCohomology_two_iso_homology_one` this
is the source's reformulation `𝒪_x(M) = H²(K ⊗^𝐋_A M)` with `K = (N ⊗_Λ A)[-1]`. -/
@[stacks 07YW "the obstruction spaces of the example of Tag 07YH are 𝒪_x(M) = H¹(N ⊗_Λ M)"]
theorem exists_finiteProjectiveModel_obstructionSpace {Λ : Type u} [CommRing Λ]
    {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of Λ)) (F : W.Modules)
    [IsNoetherianRing Λ] [IsProper g] [F.IsCoherent]
    (hflat : IsFlatOver g.toLRSHom.toShHom F) :
    ∃ (N : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ),
      N.IsStrictlyGE a ∧ N.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite Λ (N.X i)) ∧ (∀ i : ℤ, Module.Projective Λ (N.X i)) ∧
        ∀ (A : Type u) [CommRing A] (φ : Λ →+* A) {W' : Scheme.{u}}
          {g' : W' ⟶ Spec (CommRingCat.of A)} {p : W' ⟶ W}
          (_hsq : IsPullback p g' g (Spec.map (CommRingCat.ofHom φ)))
          (M : ModuleCat.{u} A),
          Nonempty ((obstructionFunctor g' ((Scheme.Modules.pullback p).obj F)).obj M ≅
            ((tensorComplex M).obj (extendScalarsComplex φ N)).homology 1) := by
  classical
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  obtain ⟨N, a, b, hGE, hLE, hfin, hproj, hiso⟩ :=
    exists_finiteProjectiveModel_derivedIso g F hflat
  refine ⟨N, a, b, hGE, hLE, hfin, hproj, ?_⟩
  intro A _ φ W' g' p hsq M
  obtain ⟨I, hI, hIlin, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper g
  have := hI
  have := hIlin
  have hLE' : N.IsStrictlyLE b := hLE
  have hU' : (⊤ : W'.Opens) = ⨆ i, p ⁻¹ᵁ U i := top_eq_iSup_preimage p U hU
  have haff' : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, (p ⁻¹ᵁ U (s k))) :=
    iInf_preimage_isAffineOpen φ hsq U hUaff
  obtain ⟨eN⟩ := hiso φ hsq
  have hQ : DerivedCategory.Q.obj
        (baseAlternatingCechComplex g' (fun i ↦ p ⁻¹ᵁ U i) hU'
          ((Scheme.Modules.pullback p).obj F)) ≅
      DerivedCategory.Q.obj (extendScalarsComplex φ N) :=
    alternatingCechIsoDerivedGlobalSectionsOverBase g' (fun i ↦ p ⁻¹ᵁ U i) hU'
      ((Scheme.Modules.pullback p).obj F) haff' ≪≫ eN
  have hKC : CochainComplex.KFlat.{u, u}
      (baseAlternatingCechComplex g' (fun i ↦ p ⁻¹ᵁ U i) hU'
        ((Scheme.Modules.pullback p).obj F)) :=
    @CochainComplex.KFlat.kFlat_of_flat.{u, u} A _ _ (Fintype.card I : ℤ) inferInstance
      (fun n ↦ flat_baseAlternatingCechComplexBaseChange_X φ hsq F U hU hUaff hflat n)
  have hLEN : (extendScalarsComplex φ N).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact (ModuleCat.extendScalars φ).map_isZero (N.isZero_of_isStrictlyLE b j hj)
  have hflatN : ∀ n : ℤ, Module.Flat A ((extendScalarsComplex φ N).X n) := by
    intro n
    let : Algebra Λ A := φ.toAlgebra
    have := hproj n
    have : Module.Flat Λ (N.X n) := Module.Flat.of_projective
    change Module.Flat A (TensorProduct Λ A (N.X n : Type u))
    infer_instance
  have hKN : CochainComplex.KFlat.{u, u} (extendScalarsComplex φ N) :=
    @CochainComplex.KFlat.kFlat_of_flat.{u, u} A _ _ b hLEN hflatN
  obtain ⟨tr⟩ := nonempty_homology_tensorComplex_iso _ _ hKC hKN hQ M 1
  refine ⟨?_⟩
  refine obstructionFunctorHomologyIso g' ((Scheme.Modules.pullback p).obj F)
      (fun i ↦ p ⁻¹ᵁ U i) hU' haff' M ≪≫ ?_
  refine (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) 1).mapIso
      (baseAlternatingCechTensorIso g' M ((Scheme.Modules.pullback p).obj F)
        (fun i ↦ p ⁻¹ᵁ U i) haff' hU') ≪≫ ?_
  exact tr

/-! ### The finite complex `N`, with no carried input -/

/-- **[Stacks, Tag 07YW], the complex `N`.** Let `Λ` be Noetherian, let `g : W ⟶ Spec Λ` be
proper and let `𝓕` be a coherent `𝒪_W`-module flat over `Λ`. Then there is a finite complex `N`
of finite projective `Λ`-modules which universally computes the cohomology of `𝓕` — for every
base change `φ : Λ → Λ'`, `Hⁱ(W_{Λ'}, 𝓕_{Λ'}) ≅ Hⁱ(N ⊗_Λ Λ')` — and, writing
`K = (N ⊗_Λ A)[-1]` for a `Λ`-algebra `A`, the degree-one cohomology of `N ⊗_Λ M` is the
degree-two cohomology of `K ⊗^𝐋_A M` for every `A`-module `M`.

This is `Deformation.Artin.SectionsPerfectComplex.exists_finiteProjectiveModel_obstruction`
without its binder `_haffineBase`, the affine-base case of [Stacks, Tag 02O5], which that proof
never uses: [Stacks, Tag 07VL]
(`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_finiteProjectiveModel_homology_iso`)
is unconditional. -/
@[stacks 07YW "there exists a finite complex N of finite projective Λ-modules which \
  universally computes the cohomology of 𝓕"]
theorem exists_finiteProjectiveModel_homology_iso_obstruction {Λ : Type u} [CommRing Λ]
    {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of Λ)) (F : W.Modules)
    [IsNoetherianRing Λ] [IsProper g] [F.IsCoherent]
    (hflat : IsFlatOver g.toLRSHom.toShHom F) :
    ∃ (N : CochainComplex (ModuleCat.{u} Λ) ℤ) (a b : ℤ),
      N.IsStrictlyGE a ∧ N.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite Λ (N.X i)) ∧ (∀ i : ℤ, Module.Projective Λ (N.X i)) ∧
        (∀ {Λ' : Type u} [CommRing Λ'] (φ : Λ →+* Λ') {W' : Scheme.{u}}
          {g' : W' ⟶ Spec (.of Λ')} {p : W' ⟶ W}
          (_hsq : IsPullback p g' g (Spec.map (CommRingCat.ofHom φ))) (i : ℤ),
          Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} Λ') i).obj
              (derivedGlobalSectionsOverBase g' ((Scheme.Modules.pullback p).obj F)) ≅
            (extendScalarsComplex φ N).homology i)) ∧
        ∀ (A : Type u) [CommRing A] (φ : Λ →+* A) (M : ModuleCat.{u} A),
          Nonempty ((Deformation.Artin.derivedCohomology A
                (DerivedCategory.Q.obj
                  (Deformation.Artin.SectionsPerfectComplex.shiftedBaseChange φ N)) 2).obj M ≅
            ((tensorComplex M).obj (extendScalarsComplex φ N)).homology 1) := by
  obtain ⟨N, a, b, hGE, hLE, hfin, hproj, hcomp⟩ :=
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_finiteProjectiveModel_homology_iso
      g F hflat
  have hNflat : ∀ i : ℤ, Module.Flat Λ (N.X i) := fun i =>
    have := hproj i; Module.Flat.of_projective
  exact ⟨N, a, b, hGE, hLE, hfin, hproj, hcomp, fun A _ φ M =>
    Deformation.Artin.SectionsPerfectComplex.nonempty_derivedCohomology_two_iso_homology_one
      φ N b hNflat M⟩

end Deformation.Artin.SectionsObstructionModel

end
