module

public import StacksFrontier.AlgebraicGeometry.Spaces.CechStructureSheafComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCohomologyUniformVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangePushforwardTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageCartesian
public import StacksFrontier.Homology.KFlat.TensorExactAboveQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseObjectNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionAlongIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage

/-!
# Base change of the Čech complex of the structure sheaf

Let `X` be an algebraic space over `Spec A` with a surjective étale chart `U` with affine scheme,
and let `C` be the Čech complex `Γ(U, 𝒪) → Γ(U ×_X U, 𝒪) → ⋯` of the structure sheaf
(`AlgebraicGeometry.Space.cechStructureComplex`). For an `A`-algebra `A'` whose spectrum lies in
the site, `A' ⊗_A C` is the Čech complex for `U` of the quasi-coherent `𝒪_X`-module `g'_*𝒪_{X'}`,
the direct image of the structure sheaf of the base change `X' = X ×_{Spec A} Spec A'`: over an
affine chart `V` of `X` the functions of `V ×_X X'` are `A' ⊗_A 𝒪(V)`, naturally in `V`. Its
cohomology is therefore `H^*(X, g'_*𝒪_{X'})`, which vanishes from a degree independent of `A'`
when `X` is quasi-compact and quasi-separated (Stacks 073G, in the form of
`AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_globalSections_of_qcqs`). Taking
`A' = A/I` for the ideals `I` of `A` gives the hypothesis of the K-flatness criterion
`CochainComplex.KFlat.kFlat_of_rTensor_quotient_exact`.

## Main results

* `AlgebraicGeometry.Space.exact_cechComplex_d_of_isZero_rightDerived`: the Čech complex of a
  quasi-coherent module is exact where its cohomology vanishes.
* `AlgebraicGeometry.Space.exists_addEquiv_unitSectionsOverBase` and
  `AlgebraicGeometry.Space.baseChangeChartTensorEquiv_naturality`:
  `𝒪_{X'}(V ×_X X') = A' ⊗_A 𝒪_X(V)` over affine charts, naturally.
* `AlgebraicGeometry.Space.exact_lTensor_cechComplexOverBase_unit`: `A' ⊗_A C` is exact where
  `H^*(X, g'_*𝒪_{X'})` vanishes.
* `AlgebraicGeometry.Space.exists_exact_rTensor_quotient_cechStructureComplex`: for `X` proper
  over `Spec A`, `C ⊗_A A/I` is exact above a degree independent of `I`.

No declaration of this file carries a `stacks` attribute.

## References

* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial ComplexShape
open Stacks.Cohomology.SiteModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace CategoryTheory.InjectiveResolution

/-- The image of an injective resolution under an additive functor is exact in a positive degree
`m` as soon as the `m`-th right derived functor vanishes at the resolved object. -/
lemma exactAt_mapHomologicalComplex_cochainComplex_of_isZero {A B : Type*} [Category* A]
    [Category* B] [Abelian A] [Abelian B] [HasInjectiveResolutions A] (G : A ⥤ B) [G.Additive]
    {F : A} (J : InjectiveResolution F) (m : ℕ) (hG : IsZero ((G.rightDerived m).obj F)) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J.cochainComplex).ExactAt m := by
  refine HomologicalComplex.ExactAt.of_iso ?_
    (G.mapExtendIso J.cocomplex ComplexShape.embeddingUpNat).symm
  refine (HomologicalComplex.extend_exactAt_iff
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)
    ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f m)).2 ?_
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ m).2 ?_
  exact hG.of_iso (J.isoRightDerivedObj G m).symm

end CategoryTheory.InjectiveResolution

namespace Stacks.CechTop

variable {C : Type*} [Category* C] (U : C) [∀ n : ℕ, HasProduct (fun _ : Fin (n + 1) => U)]

/-- The Čech differential of a presheaf of abelian groups, elementwise. -/
theorem cechComplex_d_apply_eq_sum (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (x : (cechComplex U P).X n) :
    (cechComplex U P).d n (n + 1) x = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.map ((cechNerve U).map (SimplexCategory.δ i).op).op x := by
  rw [cechComplex_d]
  have key : ∀ {P Q : AddCommGrpCat.{u}} {ι : Type} (t : Finset ι) (g : ι → (P ⟶ Q)) (y : P),
      (∑ i ∈ t, g i) y = ∑ i ∈ t, g i y := by
    intro P Q ι t g y
    induction t using Finset.cons_induction with
    | empty => rfl
    | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, AddCommGrpCat.hom_add_apply, ih]
  exact key (P := P.obj (op ((cechNerve U).obj (op ⦋n⦌))))
    (Q := P.obj (op ((cechNerve U).obj (op ⦋n + 1⦌)))) Finset.univ _ x

/-- The Čech differential of a presheaf of modules, elementwise. -/
theorem cechComplex_d_apply_eq_sum_moduleCat {R : Type*} [Ring R] (P : Cᵒᵖ ⥤ ModuleCat.{u} R)
    (n : ℕ) (x : (cechComplex U P).X n) :
    (cechComplex U P).d n (n + 1) x = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      P.map ((cechNerve U).map (SimplexCategory.δ i).op).op x := by
  rw [cechComplex_d]
  have key : ∀ {P Q : ModuleCat.{u} R} {ι : Type} (t : Finset ι) (g : ι → (P ⟶ Q)) (y : P),
      (∑ i ∈ t, g i) y = ∑ i ∈ t, g i y := by
    intro P Q ι t g y
    induction t using Finset.cons_induction with
    | empty => rfl
    | cons a t ha ih => rw [Finset.sum_cons, Finset.sum_cons, ← ih]; rfl
  exact key (P := P.obj (op ((cechNerve U).obj (op ⦋n⦌))))
    (Q := P.obj (op ((cechNerve U).obj (op ⦋n + 1⦌)))) Finset.univ _ x

end Stacks.CechTop

namespace CochainComplex

open TensorProduct

/-- Exactness of a tensored `ℕ`-graded complex in a positive degree is the same as the exactness of
its extension by zero to `ℤ`, tensored on the other side. -/
theorem exact_rTensor_extend_iff {R : Type u} [CommRing R] (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (M : Type u) [AddCommGroup M] [Module R M] (m : ℕ) :
    Function.Exact
        (LinearMap.rTensor M ((K.extend ComplexShape.embeddingUpNat).d (m : ℤ)
          ((m + 1 : ℕ) : ℤ)).hom)
        (LinearMap.rTensor M ((K.extend ComplexShape.embeddingUpNat).d ((m + 1 : ℕ) : ℤ)
          ((m + 1 + 1 : ℕ) : ℤ)).hom) ↔
      Function.Exact (LinearMap.lTensor M (K.d m (m + 1)).hom)
        (LinearMap.lTensor M (K.d (m + 1) (m + 1 + 1)).hom) := by
  let e : ∀ j : ℕ, M ⊗[R] K.X j ≃+ (K.extend ComplexShape.embeddingUpNat).X (j : ℤ) ⊗[R] M :=
    fun j => ((TensorProduct.comm R M (K.X j)).trans
      (LinearEquiv.rTensor M (K.extendXIso ComplexShape.embeddingUpNat
        (i := j) (i' := (j : ℤ)) rfl).toLinearEquiv.symm)).toAddEquiv
  have hcomm : ∀ j : ℕ, (LinearMap.rTensor M ((K.extend ComplexShape.embeddingUpNat).d (j : ℤ)
      ((j + 1 : ℕ) : ℤ)).hom).toAddMonoidHom.comp (e j : M ⊗[R] K.X j →+ _) =
      AddMonoidHom.comp (e (j + 1) : M ⊗[R] K.X (j + 1) →+ _)
        (LinearMap.lTensor M (K.d j (j + 1)).hom).toAddMonoidHom := by
    intro j
    refine AddMonoidHom.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul a c =>
      have h₁ : e j (a ⊗ₜ c) = (K.extendXIso ComplexShape.embeddingUpNat
          (i := j) (i' := (j : ℤ)) rfl).inv c ⊗ₜ a := rfl
      have h₂ : e (j + 1) (a ⊗ₜ (K.d j (j + 1)) c) = (K.extendXIso ComplexShape.embeddingUpNat
          (i := j + 1) (i' := ((j + 1 : ℕ) : ℤ)) rfl).inv ((K.d j (j + 1)) c) ⊗ₜ a := rfl
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_ofClass,
        LinearMap.toAddMonoidHom_coe, LinearMap.lTensor_tmul, h₁, h₂, LinearMap.rTensor_tmul]
      congr 1
      rw [HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat (i' := (j : ℤ))
        (j' := ((j + 1 : ℕ) : ℤ)) (i := j) (j := j + 1) rfl rfl]
      change ((K.extendXIso ComplexShape.embeddingUpNat (i := j) (i' := (j : ℤ)) rfl).inv ≫
        (K.extendXIso ComplexShape.embeddingUpNat (i := j) (i' := (j : ℤ)) rfl).hom ≫
          K.d j (j + 1) ≫ (K.extendXIso ComplexShape.embeddingUpNat (i := j + 1)
            (i' := ((j + 1 : ℕ) : ℤ)) rfl).inv) c = _
      rw [Iso.inv_hom_id_assoc]
      rfl
  exact Function.Exact.iff_of_ladder_addEquiv
    (f₁₂ := (LinearMap.lTensor M (K.d m (m + 1)).hom).toAddMonoidHom)
    (f₂₃ := (LinearMap.lTensor M (K.d (m + 1) (m + 1 + 1)).hom).toAddMonoidHom)
    (g₁₂ := (LinearMap.rTensor M ((K.extend ComplexShape.embeddingUpNat).d (m : ℤ)
      ((m + 1 : ℕ) : ℤ)).hom).toAddMonoidHom)
    (g₂₃ := (LinearMap.rTensor M ((K.extend ComplexShape.embeddingUpNat).d ((m + 1 : ℕ) : ℤ)
      ((m + 1 + 1 : ℕ) : ℤ)).hom).toAddMonoidHom) _ _ _ (hcomm m) (hcomm (m + 1))

end CochainComplex

namespace AlgebraicGeometry.Space

attribute [local instance] CategoryTheory.Limits.hasProduct_fin_succ_of_hasBinaryProducts

section CechExact

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
  (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- The `𝒪_X`-modules on the small étale site of `X` have enough injectives. -/
local instance : EnoughInjectives (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
  enoughInjectives_modules B (Spec (.of A)) hA X hX

attribute [local instance] hasSheafify_smallEtaleRingedSite_spec

/-- The topology of the small étale ringed site of `X` satisfies `WEqualsLocallyBijective` for
abelian groups, as the small étale topology of `X` does. -/
local instance :
    (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((SmallEtale.topology B (Spec (.of A)) hA X).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- **The Čech complex of a quasi-coherent module is exact where its cohomology vanishes.** Let
`X` be an algebraic space over `Spec A` with affine intersections, `U` a surjective étale chart
with affine scheme and `𝓜` a quasi-coherent `𝒪_X`-module with `H^{m+1}(X, 𝓜) = 0`. Then the
Čech complex `Γ(U, 𝓜) → Γ(U ×_X U, 𝓜) → ⋯` of abelian groups is exact in degree `m + 1`. -/
theorem exact_cechComplex_d_of_isZero_rightDerived
    (hsep : HasAffineIntersections B (Spec (.of A)) hA X)
    (U : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)
    (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U)
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (hM : M.IsQuasicoherentOnSite) (m : ℕ)
    (h : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived (m + 1)).obj M)) :
    Function.Exact
      ((Stacks.CechTop.cechComplex U M.val.presheaf).d m (m + 1)).hom
      ((Stacks.CechTop.cechComplex U M.val.presheaf).d (m + 1) (m + 1 + 1)).hom := by
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
  let R := InjectiveResolution.of M
  obtain ⟨T, φ, ψ, hφ, hψ⟩ :=
    exists_quasiIso_cechComplexOverBase A B hA X hX hsep U hUs hUa M hM R
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  -- the cohomology over the base vanishes in degree `m + 1`
  have h₁ : IsZero (((globalSectionsOverSpec A B hA X hX).rightDerived (m + 1)).obj M) :=
    IsZero.of_iso ((ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).map_isZero h)
      ((Functor.rightDerivedCompIso Γ
        (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) (m + 1)).app M)
  have h₂ := InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex_of_isZero
    (globalSectionsOverSpec A B hA X hX) R (m + 1) h₁
  -- transport along the two quasi-isomorphisms
  have h₃ : T.ExactAt ((m + 1 : ℕ) : ℤ) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₂ ⊢
    exact h₂.of_iso (@asIso _ _ _ _ _ ((quasiIsoAt_iff_isIso_homologyMap φ _).1 inferInstance)).symm
  have h₄ : ((cechComplexOverBase A B hA X hX U).obj M).ExactAt ((m + 1 : ℕ) : ℤ) := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at h₃ ⊢
    exact h₃.of_iso (@asIso _ _ _ _ _ ((quasiIsoAt_iff_isIso_homologyMap ψ _).1 inferInstance))
  -- back to the `ℕ`-graded complex in the universe of the schemes
  have h₅ := (HomologicalComplex.extend_exactAt_iff _ embeddingUpNat
    (ComplexShape.embeddingUpNat_f (m + 1))).1 h₄
  have h₆ : (Stacks.CechTop.cechComplexOverBase U
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
      (baseRingHom A B hA X hX) M).ExactAt (m + 1) := by
    rw [HomologicalComplex.exactAt_iff] at h₅ ⊢
    exact (ShortComplex.exact_map_iff_of_faithful _ (ModuleCat.uliftFunctor.{u + 1} A)).1 h₅
  rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff] at h₆
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := h₆ x
      ((Stacks.CechTop.cechComplexOverBase_d_apply _ _ _ M (m + 1) x).trans hx)
    exact ⟨y, (Stacks.CechTop.cechComplexOverBase_d_apply _ _ _ M m y).symm.trans hy⟩
  · rintro ⟨y, rfl⟩
    exact congrArg (fun f => (ConcreteCategory.hom f) y)
      ((Stacks.CechTop.cechComplex _ M.val.presheaf).d_comp_d m (m + 1) (m + 1 + 1))

end CechExact

section BaseChange

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
  (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
  {A' : Type u} [CommRing A'] {hA' : B.Contains (Spec (.of A'))} (g : B.obj hA' ⟶ B.obj hA)

/-- The cartesian square of Stacks 073J for the base change of an algebraic space over `Spec A`
along a morphism `Spec A' ⟶ Spec A` of the site, with the structure sheaf as coefficient. -/
abbrev specBaseChangeDiagram : BaseChangeDiagram B (Spec (.of A)) hA where
  X' := pullback (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) ⟶
      ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))), isAlgebraicSpace_yoneda _ _ _ _⟩)
    (ObjectProperty.homMk (yoneda.map
        (Over.homMk g (by simp) : Over.mk g ⟶ Over.mk (𝟙 (B.obj hA)))) :
      (⟨yoneda.obj (Over.mk g), isAlgebraicSpace_yoneda _ _ _ _⟩ :
        AlgebraicSpaces B (Spec (.of A)) hA) ⟶
      ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))), isAlgebraicSpace_yoneda _ _ _ _⟩)
  X := ⟨X, hX⟩
  Y' := ⟨yoneda.obj (Over.mk g), isAlgebraicSpace_yoneda _ _ _ _⟩
  Y := ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))), isAlgebraicSpace_yoneda _ _ _ _⟩
  g' := pullback.fst _ _
  f' := pullback.snd _ _
  f := ObjectProperty.homMk f
  g := ObjectProperty.homMk (yoneda.map (Over.homMk g (by simp) :
    Over.mk g ⟶ Over.mk (𝟙 (B.obj hA))))
  isPullback := IsPullback.of_hasPullback _ _
  F := SheafOfModules.unit _
  isQuasicoherent := isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    isCartesianOnAffineCharts_unit

/-- The projection `g' : X' ⟶ X` of the base change square `specBaseChangeDiagram` is
relatively representable. -/
theorem relativelyRepresentable_specBaseChangeDiagram_g' :
    yoneda.relativelyRepresentable (specBaseChangeDiagram hX f g).g'.hom :=
  (specBaseChangeDiagram hX f g).relativelyRepresentable_g'
    (isAffineSpace_yoneda _ _ _ _ (inferInstanceAs (IsAffine (Spec (.of A)))))
    (isAffineSpace_yoneda _ _ _ _ (inferInstanceAs (IsAffine (Spec (.of A')))))

/-- The projection `g' : X' ⟶ X` of the base change square `specBaseChangeDiagram` is affine, as
the base change of the morphism `Spec A' ⟶ Spec A` of affine schemes. -/
theorem isAffineHom_specBaseChangeDiagram_g' :
    IsAffineHom B (Spec (.of A)) hA (specBaseChangeDiagram hX f g).g'.hom := by
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (Over.mk g)) :=
    inferInstanceAs (IsAffine (Spec (.of A')))
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj
      (Over.mk (𝟙 (B.obj hA)))) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  exact isAffineHom_of_isPullback' B (Spec (.of A)) hA
    (AlgebraicSpaces.isPullback_hom B (Spec (.of A)) hA
      (specBaseChangeDiagram hX f g).isPullback).flip
    (isAffineHom_yoneda_map B (Spec (.of A)) hA _)

end BaseChange

section ChartTensor

open TensorProduct

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
  (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))
  {A' : Type u} [CommRing A'] [Algebra A A'] {hA' : B.Contains (Spec (.of A'))}
  (g : B.obj hA' ⟶ B.obj hA)

/-- The identity chart of `Spec A`. -/
abbrev specIdChart : SmallEtale B (Spec (.of A)) hA (yoneda.obj (Over.mk (𝟙 (B.obj hA)))) :=
  idEtaleChart B (Spec (.of A)) hA (Over.mk (𝟙 (B.obj hA)))

/-- The identity chart of `Spec A'`, over `Spec A`. -/
abbrev specIdChart' : SmallEtale B (Spec (.of A)) hA (yoneda.obj (Over.mk g)) :=
  idEtaleChart B (Spec (.of A)) hA (Over.mk g)

/-- The structure morphism of the identity chart of `Spec A` is an isomorphism. -/
instance isIso_specIdChart_obj_hom : IsIso (specIdChart (hA := hA)).obj.hom :=
  inferInstanceAs (IsIso (𝟙 _))

/-- The structure morphism of the identity chart of `Spec A'` is an isomorphism. -/
instance isIso_specIdChart'_obj_hom : IsIso (specIdChart' g).obj.hom :=
  inferInstanceAs (IsIso (𝟙 _))

/-- `A ≅ Γ(Spec A)`. -/
abbrev specRingEquiv : A ≃+* baseChartRing B (Spec (.of A)) hA
    (specBaseChangeDiagram hX f g).Y (specIdChart (hA := hA)) :=
  (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv

/-- `A' ≅ Γ(Spec A')`. -/
abbrev specRingEquiv' : A' ≃+* baseChartRing B (Spec (.of A)) hA
    (specBaseChangeDiagram hX f g).Y' (specIdChart' g) :=
  (Scheme.ΓSpecIso (.of A')).symm.commRingCatIsoToRingEquiv

/-- The structure morphism of a chart of `X`, read through the identity chart of `Spec A`. -/
theorem toScheme_map_baseChartHom_specIdChart (V : SmallEtale B (Spec (.of A)) hA X) :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map
        (baseChartHom B (Spec (.of A)) hA
          (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) ⟶
            ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))), isAlgebraicSpace_yoneda _ _ _ _⟩)
          (specIdChart (hA := hA)) V) =
      B.inclusion.map ((SmallEtale.toOver B (Spec (.of A)) hA X).obj V).hom := by
  have h := Over.w (baseChartHom B (Spec (.of A)) hA
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) ⟶
      ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))), isAlgebraicSpace_yoneda _ _ _ _⟩)
    (specIdChart (hA := hA)) V)
  change B.inclusion.map _ = _
  rw [← h]
  exact (congrArg B.inclusion.map (Category.comp_id _)).symm

/-- The sections of the structure sheaf over a chart, as a module over the base ring. -/
abbrev unitSectionsOverBase (V : SmallEtale B (Spec (.of A)) hA X) : ModuleCat.{u} A :=
  Stacks.CechTop.sectionsOverBaseObj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
    (baseRingHom A B hA X hX) (SheafOfModules.unit _) (op V)

/-- **The `A`-module structure of the Čech complex on the functions of a chart is the algebra
structure over `Γ(Spec A)`**, through `A ≅ Γ(Spec A)`. -/
theorem smul_unitSectionsOverBase (V : SmallEtale B (Spec (.of A)) hA X) (a : A)
    (c : unitSectionsOverBase hX V) :
    letI := baseChartAlgebra B (Spec (.of A)) hA
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) ⟶
        ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))), isAlgebraicSpace_yoneda _ _ _ _⟩)
      (specIdChart (hA := hA)) V
    (show (Γ(chartScheme V, ⊤) : Type u) from
        @HSMul.hSMul A (unitSectionsOverBase hX V) (unitSectionsOverBase hX V) _ a c) =
      algebraMap (baseChartRing B (Spec (.of A)) hA
        ⟨yoneda.obj (Over.mk (𝟙 (B.obj hA))), isAlgebraicSpace_yoneda _ _ _ _⟩
          (specIdChart (hA := hA))) (Γ(chartScheme V, ⊤) : Type u)
        ((Scheme.ΓSpecIso (.of A)).inv a) * (show (Γ(chartScheme V, ⊤) : Type u) from c) := by
  change (((Scheme.ΓSpecIso (.of A)).inv ≫ Scheme.Γ.map ((B.inclusion.map
    ((SmallEtale.toOver B (Spec (.of A)) hA X).obj V).hom).op)).hom a) * _ = _
  rw [← toScheme_map_baseChartHom_specIdChart hX f V]
  rfl

/-- The structure morphism `Spec A' ⟶ Spec A` of the base change square, read through the
identity charts, is the spectrum of the algebra map. -/
private theorem toScheme_map_baseChartHom_specIdChart_g
    (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A A'))) :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map (baseChartHom B (Spec (.of A)) hA
      (specBaseChangeDiagram hX f g).g (specIdChart (hA := hA)) (specIdChart' g)) =
      Spec.map (CommRingCat.ofHom (algebraMap A A')) :=
  (congrArg B.inclusion.map ((Category.comp_id _).symm.trans
    (Over.w (baseChartHom B (Spec (.of A)) hA (specBaseChangeDiagram hX f g).g
      (specIdChart (hA := hA)) (specIdChart' g))))).trans hg

variable {g} in
/-- The structure morphism `Spec A' ⟶ Spec A`, read through the identity charts. -/
theorem algebraMap_specRingEquiv
    (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A A'))) (a : A) :
    letI := baseChartAlgebra B (Spec (.of A)) hA (specBaseChangeDiagram hX f g).g
      (specIdChart (hA := hA)) (specIdChart' g)
    algebraMap (baseChartRing B (Spec (.of A)) hA (specBaseChangeDiagram hX f g).Y
        (specIdChart (hA := hA)))
      (baseChartRing B (Spec (.of A)) hA (specBaseChangeDiagram hX f g).Y' (specIdChart' g))
      ((Scheme.ΓSpecIso (.of A)).inv a) = (Scheme.ΓSpecIso (.of A')).inv (algebraMap A A' a) := by
  change ((BigFppfOver.toScheme B (Spec (.of A)) hA).map (baseChartHom B (Spec (.of A)) hA
    (specBaseChangeDiagram hX f g).g (specIdChart (hA := hA)) (specIdChart' g))).appTop.hom
      ((Scheme.ΓSpecIso (.of A)).inv a) = _
  rw [toScheme_map_baseChartHom_specIdChart_g hX f g hg]
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A A')))).symm

variable {g} (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A A')))
  (hg' : yoneda.relativelyRepresentable (specBaseChangeDiagram hX f g).g'.hom)

include hg in
/-- **The functions on the base change of an affine chart are a tensor product**:
`𝒪_{X'}(V ×_X X') = A' ⊗_A 𝒪_X(V)` for an affine chart `V` of `X`, an elementary tensor
`a' ⊗ c` being the product of the pullbacks of `a'` and of `c`. -/
theorem exists_addEquiv_unitSectionsOverBase (V : SmallEtale B (Spec (.of A)) hA X)
    [IsAffine (chartScheme V)] :
    ∃ e : A' ⊗[A] unitSectionsOverBase hX V ≃+
        (Γ(chartScheme ((specBaseChangeDiagram hX f g).baseChangeChart hg' V), ⊤) : Type u),
      ∀ a c, e (a ⊗ₜ c) = @HMul.hMul
        (Γ(chartScheme ((specBaseChangeDiagram hX f g).baseChangeChart hg' V), ⊤) : Type u)
        (Γ(chartScheme ((specBaseChangeDiagram hX f g).baseChangeChart hg' V), ⊤) : Type u)
        (Γ(chartScheme ((specBaseChangeDiagram hX f g).baseChangeChart hg' V), ⊤) : Type u) _
        ((specBaseChangeDiagram hX f g).baseChangeChartBaseHom hg' (specIdChart' g) V
          ((Scheme.ΓSpecIso (.of A')).inv a))
        (((BigFppfOver.toScheme B (Spec (.of A)) hA).map
          ((specBaseChangeDiagram hX f g).baseChangeChartProjection hg' V)).appTop.hom c) := by
  have hpb := (specBaseChangeDiagram hX f g).isPullback_chartScheme_baseChangeChart hg'
    (specIdChart (hA := hA)) (specIdChart' g) V
  have h₁ : (BigFppfOver.toScheme B (Spec (.of A)) hA).map
      (baseChartHom B (Spec (.of A)) hA (specBaseChangeDiagram hX f g).f
        (specIdChart (hA := hA)) V) =
      B.inclusion.map ((SmallEtale.toOver B (Spec (.of A)) hA X).obj V).hom :=
    toScheme_map_baseChartHom_specIdChart hX f V
  have h₂ := toScheme_map_baseChartHom_specIdChart_g hX f g hg
  rw [h₁, h₂] at hpb
  exact @exists_addEquiv_tensor_of_isPullback_spec A A' _ _ _ _ _ ‹IsAffine (chartScheme V)›
    _ _ _ hpb

/-- The direct image `g'_*𝒪_{X'}` of the structure sheaf of the base change. -/
abbrev baseChangeUnitPushforward : Modules.{u, u} B (Spec (.of A)) hA X hX :=
  (smallBaseChangeModulePushforward B (Spec (.of A)) hA (specBaseChangeDiagram hX f g).g' hg').obj
    (SheafOfModules.unit _)

/-- The chosen identification `A' ⊗_A 𝒪_X(V) ≅ (g'_*𝒪_{X'})(V) = 𝒪_{X'}(V ×_X X')` over an affine
chart `V`. -/
noncomputable def baseChangeChartTensorEquiv (V : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)
    (hV : IsAffine (chartScheme V)) :
    A' ⊗[A] unitSectionsOverBase hX V ≃+
      (baseChangeUnitPushforward hX f hg').val.presheaf.obj (op V) :=
  (exists_addEquiv_unitSectionsOverBase hX f hg hg' V).choose

/-- `baseChangeChartTensorEquiv` sends `a ⊗ c` to the product, in the sections of the chart
`V ×_X X'`, of the pullback of `a ∈ A' = Γ(Spec A')` along the structure morphism of that chart
over `Spec A'` and of the pullback of `c ∈ 𝒪_X(V)` along the projection `V ×_X X' ⟶ V`. -/
theorem baseChangeChartTensorEquiv_tmul (V : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)
    (hV : IsAffine (chartScheme V)) (a : A') (c : unitSectionsOverBase hX V) :
    @id (Γ(chartScheme ((specBaseChangeDiagram hX f g).baseChangeChart hg' V), ⊤) : Type u)
      (baseChangeChartTensorEquiv hX f hg hg' V hV (a ⊗ₜ c)) = @HMul.hMul
        (Γ(chartScheme ((specBaseChangeDiagram hX f g).baseChangeChart hg' V), ⊤) : Type u)
        (Γ(chartScheme ((specBaseChangeDiagram hX f g).baseChangeChart hg' V), ⊤) : Type u)
        (Γ(chartScheme ((specBaseChangeDiagram hX f g).baseChangeChart hg' V), ⊤) : Type u) _
        ((specBaseChangeDiagram hX f g).baseChangeChartBaseHom hg' (specIdChart' g) V
          ((Scheme.ΓSpecIso (.of A')).inv a))
        (((BigFppfOver.toScheme B (Spec (.of A)) hA).map
          ((specBaseChangeDiagram hX f g).baseChangeChartProjection hg' V)).appTop.hom c) :=
  have := hV
  (exists_addEquiv_unitSectionsOverBase hX f hg hg' V).choose_spec a c

/-- **The chart identification is natural in the chart.** -/
theorem baseChangeChartTensorEquiv_naturality
    {V V' : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C} (k : V' ⟶ V)
    (hV : IsAffine (chartScheme V)) (hV' : IsAffine (chartScheme V'))
    (x : A' ⊗[A] unitSectionsOverBase hX V) :
    ((baseChangeUnitPushforward hX f hg').val.presheaf.map k.op)
        (baseChangeChartTensorEquiv hX f hg hg' V hV x) =
      baseChangeChartTensorEquiv hX f hg hg' V' hV'
        (LinearMap.lTensor A' (Stacks.CechTop.sectionsOverBaseMap
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
          (baseRingHom A B hA X hX) (SheafOfModules.unit _) k.op).hom x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a c =>
    simp only [LinearMap.lTensor_tmul]
    have h₁ := baseChangeChartTensorEquiv_tmul hX f hg hg' V hV a c
    have h₂ := baseChangeChartTensorEquiv_tmul hX f hg hg' V' hV' a
      ((Stacks.CechTop.sectionsOverBaseMap (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
          (baseRingHom A B hA X hX) (SheafOfModules.unit _) k.op).hom c)
    dsimp only [id] at h₁ h₂
    refine Eq.trans ?_ h₂.symm
    refine (congrArg ((specBaseChangeDiagram hX f g).baseChangeChartRestrict hg' k) h₁).trans ?_
    refine (map_mul ((specBaseChangeDiagram hX f g).baseChangeChartRestrict hg' k) _ _).trans ?_
    exact congrArg₂ (· * ·)
      ((specBaseChangeDiagram hX f g).baseChangeChartRestrict_baseHom hg' (specIdChart' g) k _)
      ((specBaseChangeDiagram hX f g).baseChangeChartRestrict_algebraMap hg' k c)

/-- The degree-`n` term of the ladder `A' ⊗_A Č(U, 𝒪_X) ≅ Č(U, g'_*𝒪_{X'})`. -/
noncomputable def cechChartEquiv (hsep : HasAffineIntersections B (Spec (.of A)) hA X)
    (U : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) (n : ℕ) :
    A' ⊗[A] (Stacks.CechTop.cechComplexOverBase U
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
      (baseRingHom A B hA X hX) (SheafOfModules.unit _)).X n ≃+
    (Stacks.CechTop.cechComplex U (baseChangeUnitPushforward hX f hg').val.presheaf).X n :=
  baseChangeChartTensorEquiv hX f hg hg' _
    (isAffineChart_cechNerve B (Spec (.of A)) hA X hsep hUa n)

/-- The ladder of the Čech complexes commutes with the differentials. -/
theorem cechChartEquiv_comm (hsep : HasAffineIntersections B (Spec (.of A)) hA X)
    (U : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) (n : ℕ) :
    ((Stacks.CechTop.cechComplex U (baseChangeUnitPushforward hX f hg').val.presheaf).d
        n (n + 1)).hom.comp (cechChartEquiv hX f hg hg' hsep U hUa n).toAddMonoidHom =
    AddMonoidHom.comp (cechChartEquiv hX f hg hg' hsep U hUa (n + 1)).toAddMonoidHom
      (LinearMap.lTensor A' ((Stacks.CechTop.cechComplexOverBase U
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        (baseRingHom A B hA X hX) (SheafOfModules.unit _)).d n (n + 1)).hom).toAddMonoidHom := by
  refine AddMonoidHom.ext fun x => ?_
  change ((Stacks.CechTop.cechComplex U (baseChangeUnitPushforward hX f hg').val.presheaf).d
      n (n + 1)) (cechChartEquiv hX f hg hg' hsep U hUa n x) =
    cechChartEquiv hX f hg hg' hsep U hUa (n + 1)
      (LinearMap.lTensor A' ((Stacks.CechTop.cechComplexOverBase U
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        (baseRingHom A B hA X hX) (SheafOfModules.unit _)).d n (n + 1)).hom x)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a c =>
    have h₁ := Stacks.CechTop.cechComplex_d_apply_eq_sum_moduleCat U
      (Stacks.CechTop.sectionsOverBase
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        (baseRingHom A B hA X hX) (SheafOfModules.unit _)) n c
    have h₃ : cechChartEquiv hX f hg hg' hsep U hUa (n + 1)
        (LinearMap.lTensor A' ((Stacks.CechTop.cechComplexOverBase U
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
          (baseRingHom A B hA X hX) (SheafOfModules.unit _)).d n (n + 1)).hom (a ⊗ₜ c)) =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • cechChartEquiv hX f hg hg' hsep U hUa (n + 1)
          (a ⊗ₜ ((Stacks.CechTop.sectionsOverBase
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
            (baseRingHom A B hA X hX) (SheafOfModules.unit _)).map
              ((Stacks.CechTop.cechNerve U).map (SimplexCategory.δ i).op).op c)) := by
      rw [LinearMap.lTensor_tmul, h₁]
      refine (congrArg (cechChartEquiv hX f hg hg' hsep U hUa (n + 1))
        (TensorProduct.tmul_sum _ _ _)).trans ((map_sum _ _ _).trans ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (congrArg _ (map_zsmul (TensorProduct.mk A A' _ a) _ _)).trans (map_zsmul _ _ _)
    refine (Stacks.CechTop.cechComplex_d_apply_eq_sum U
      (baseChangeUnitPushforward hX f hg').val.presheaf n _).trans (Eq.trans ?_ h₃.symm)
    refine Finset.sum_congr rfl fun i _ => ?_
    exact congrArg _ (baseChangeChartTensorEquiv_naturality hX f hg hg' _ _ _ (a ⊗ₜ c))

/-- The direct image `g'_*𝒪_{X'}` of the structure sheaf of the base change is quasi-coherent. -/
private theorem isQuasicoherentOnSite_baseChangeUnitPushforward
    (_hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A A'))) :
    (baseChangeUnitPushforward hX f hg').IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom _ hg'
    (isAffineHom_specBaseChangeDiagram_g' hX f g)
    (isQuasicoherentOnSite_of_isCartesianOnAffineCharts _ isCartesianOnAffineCharts_unit)

/-- The `𝒪_X`-modules on the small étale site of `X` have enough injectives. -/
local instance : EnoughInjectives (Modules.{u, u} B (Spec (.of A)) hA X hX) :=
  enoughInjectives_modules B (Spec (.of A)) hA X hX

include hg in
/-- **Base change of the Čech complex of the structure sheaf is exact where the cohomology of
`g'_*𝒪_{X'}` vanishes.** For an algebraic space `X` over `Spec A` with affine intersections, a
surjective étale chart `U` with affine scheme, an `A`-algebra `A'` whose spectrum lies in the
site and a degree `m + 1` in which `H^{m+1}(X, g'_*𝒪_{X'}) = 0`, the complex `A' ⊗_A Č(U, 𝒪_X)`
is exact in degree `m + 1`. -/
theorem exact_lTensor_cechComplexOverBase_unit
    (hsep : HasAffineIntersections B (Spec (.of A)) hA X)
    (U : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).C)
    (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) (m : ℕ)
    (hvan : IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived (m + 1)).obj
          (baseChangeUnitPushforward hX f hg'))) :
    Function.Exact
      (LinearMap.lTensor A' ((Stacks.CechTop.cechComplexOverBase U
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        (baseRingHom A B hA X hX) (SheafOfModules.unit _)).d m (m + 1)).hom)
      (LinearMap.lTensor A' ((Stacks.CechTop.cechComplexOverBase U
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        (baseRingHom A B hA X hX) (SheafOfModules.unit _)).d (m + 1) (m + 1 + 1)).hom) := by
  have hG := isQuasicoherentOnSite_baseChangeUnitPushforward hX f hg' hg
  have hL := exact_cechComplex_d_of_isZero_rightDerived A B hA X hX hsep U hUs hUa _ hG m hvan
  exact (Function.Exact.iff_of_ladder_addEquiv _ _ _
    (cechChartEquiv_comm hX f hg hg' hsep U hUa m)
    (cechChartEquiv_comm hX f hg hg' hsep U hUa (m + 1))).1 hL

end ChartTensor

section KFlat

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
  (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hA))))

/-- **The Čech complex of the structure sheaf of a proper flat algebraic space over `Spec A`, for
a surjective affine étale chart, has exact tensor products with every cyclic `A`-module in high
degrees**: there is `N` such that `C ⊗_A A/I` is exact in every degree `> N`, for every ideal
`I`. Indeed `C ⊗_A A/I` is the Čech complex of the quasi-coherent module `g'_*𝒪_{X_{A/I}}` on `X`,
whose cohomology vanishes from the uniform degree of Stacks 073G on. -/
theorem exists_exact_rTensor_quotient_cechStructureComplex
    (hprop : IsProper B (Spec (.of A)) hA f)
    (U : SmallEtale B (Spec (.of A)) hA X) (hUs : IsSurjective B (Spec (.of A)) hA U.obj.hom)
    (hUa : IsAffineChart B (Spec (.of A)) hA X U) :
    ∃ N : ℤ, ∀ (I : Ideal A) (k : ℤ), N < k →
      Function.Exact
        (LinearMap.rTensor (A ⧸ I) ((cechStructureComplex A B hA X hX U).d (k - 1) k).hom)
        (LinearMap.rTensor (A ⧸ I) ((cechStructureComplex A B hA X hX U).d k (k + 1)).hom) := by
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
  have hsep : HasAffineIntersections B (Spec (.of A)) hA X :=
    hasAffineIntersections_of_isSeparated A B hA X hX f hprop.1
  obtain ⟨N, hN⟩ := exists_forall_isZero_rightDerived_globalSections_of_qcqs A B hA
    B.contains_terminal X hX (isQuasiCompactSpace_of_isProper_baseObject A B hA X hX f hprop)
    (isAbsolutelyQuasiSeparated_of_isProper_baseObject A B hA X hX f hprop)
  refine ⟨N, fun I k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = ((m + 1 : ℕ) : ℤ) := ⟨(k - 1).toNat, by omega⟩
  have hA' := AlgebraicGeometry.FormalSpace.contains_spec_quotient B hA I
  let g : B.obj hA' ⟶ B.obj hA :=
    ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))))
  have hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ I))) := rfl
  have hg' := relativelyRepresentable_specBaseChangeDiagram_g' hX f g
  have hG := isQuasicoherentOnSite_baseChangeUnitPushforward hX f hg' hg
  have hex := exact_lTensor_cechComplexOverBase_unit hX f hg hg' hsep U hUs hUa m
    (hN _ hG (m + 1) (by omega))
  have h₁ : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
  have h₂ : ((m + 1 : ℕ) : ℤ) + 1 = ((m + 1 + 1 : ℕ) : ℤ) := by omega
  rw [h₁, h₂]
  exact (CochainComplex.exact_rTensor_extend_iff _ (A ⧸ I) m).2 hex

end KFlat

end AlgebraicGeometry.Space

end
