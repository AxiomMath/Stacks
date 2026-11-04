module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.TransposeCompatible
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ExistenceHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ClosedTowerSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded

/-!
# Embedding a finite tower over the adic fibres into an algebraic space affine over `X`

Let `A` be a Noetherian ring complete along `I`, `f : X ⟶ Spec A` separated and of finite type,
and `y_n : Y_n ⟶ X_n` a tower over the adic fibres `X_n = X ×_{Spec A} Spec (A / I ^ (n + 1))` with
cartesian squares, `Y_0 ⟶ X_0` finite and `Y_0` proper over `Spec (A / I)`.  Grothendieck's
existence theorem gives a coherent `ℱ` on `X` restricting to the system `((y_n)_* 𝒪)_n`; the
adjoint surjections `ℱ ⟶ (Y_n ⟶ X)_* 𝒪` embed every `Y_n` as a closed subspace of
`P = \underline{Spec}_X(Sym ℱ)`, compatibly with the transitions.  This is the first half of the
proof of Stacks 0A01.

## Main results

* `AlgebraicGeometry.Space.exists_isClosedImmersion_tower_of_isFinite`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (B : BigFppfSite.{u})
  (hA : B.Contains (Spec (.of A)))
  {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B (Spec (.of A)) hA X) (f : X ⟶ yoneda.obj (baseObject A B hA))

/-- **A finite tower over the adic fibres embeds into an algebraic space affine and of finite
presentation over `X`.**  Let `A` be Noetherian and complete along `I`, `f : X ⟶ Spec A`
separated of finite type, and `y_n : Y_n ⟶ X_n` with cartesian squares over the transitions
`X_n ⟶ X_{n + 1}`, `Y_0 ⟶ X_0` finite and `Y_0 ⟶ Spec (A / I)` proper (the tower is indexed
from `0`, `X_n` being the fibre over `Spec (A / I ^ (n + 1))`).  Then there are `p : P ⟶ X` affine
and of finite presentation and closed immersions `g_n : Y_n ⟶ P` with `g_n ≫ p = y_n ≫ ι_n` and
`t_n ≫ g_{n + 1} = g_n`. -/
theorem exists_isClosedImmersion_tower_of_isFinite [IsAdicComplete I A]
    (hsep : IsSeparated B (Spec (.of A)) hA f) (hft : IsFiniteType B (Spec (.of A)) hA f)
    (Y : ℕ → AlgebraicSpaces B (Spec (.of A)) hA) (y : ∀ n, Y n ⟶ adicFibreSpace A I B hA hX f n)
    (tY : ∀ n, Y n ⟶ Y (n + 1))
    (hcart : ∀ n, IsPullback (tY n) (y n) (y (n + 1)) (adicFibreSuccHom A I B hA hX f n))
    (hfin0 : IsFinite B (Spec (.of A)) hA (y 0).hom)
    (hprop : IsProper B (Spec (.of A)) hA ((y 0).hom ≫ adicFibreSnd A I B hA f 0)) :
    ∃ (P : AlgebraicSpaces B (Spec (.of A)) hA) (p : P ⟶ ⟨X, hX⟩),
      IsAffineHom B (Spec (.of A)) hA p.hom ∧ IsFinitePresentation B (Spec (.of A)) hA p.hom ∧
      ∃ g : ∀ n, Y n ⟶ P, (∀ n, g n ≫ p = y n ≫ adicFibreFstHom A I B hA hX f n) ∧
        (∀ n, IsClosedImmersion B (Spec (.of A)) hA (g n).hom) ∧ (∀ n, tY n ≫ g (n + 1) = g n) := by
  let := fact_hasEtaleLocalProperty_isLocallyNoetherian_of_baseObject A B hA hX f hft.1
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_adicFibre A I B hA hX f hft.1
  have hcomm := adicFibreSuccHom_comp_adicFibreFstHom A I B hA hX f
  have hfin := isFinite_of_isPullback_tower Y y tY hcart hfin0
  have hi := isClosedImmersion_adicFibreFstHom A I B hA hX f
  have hker := fun n M => kerIdealSmul_adicFibreFstHom_eq_idealPowerMultiple A I B hA hX f n M
  have hcoh := isCoherent_finiteTowerAffine A I B hA hX f y hfin hft.1
  -- the coherent system `((y_n)_* 𝒪)_n` and its proper support
  have hG := hasProperSupport_affineTowerSystem_zero A I B hA hX f hft.1 hsep
    (finiteTowerAffine A I B hA hX f y hfin) tY hcart
    hcoh
    (universallyClosed_of_isFinite B (Spec (.of A)) hA (Y 0).2
      (adicFibreSpace A I B hA hX f 0).2 (hfin 0)) hprop
  -- Grothendieck's existence theorem
  have := existenceEssSurj_holds A I B hA hX f hsep hft
  obtain ⟨M, -, ⟨eM⟩⟩ := exists_hasProperSupport_iso_thickeningRestriction B (Spec (.of A)) hA
    (X := ⟨X, hX⟩) (adicFibreFstHom A I B hA hX f) (adicFibreSuccHom A I B hA hX f)
    hcomm hi
    hN
    hker (isQuasicoherentOnSite_baseIdealSheaf A ⟨X, hX⟩ I)
    (isAlgebraicSpace_yoneda B _ hA (baseObject A B hA)) f hft.1
    (finiteTowerSystem A I B hA hX f y tY hcart hfin hft.1) hG
  have hMqc : M.obj.IsQuasicoherentOnSite := M.property.toIsQuasicoherentOnSite
  have hMfp : M.obj.IsFinitePresentationOnSite :=
    SheafOfModules.isFinitePresentationOnSite_of_isCoherentOnSite M.obj
      M.property.toIsCoherentOnSite
  -- `P = \underline{Spec}_X(Sym ℱ)`
  let Sym := symmetricAlgebraSheaf B (Spec (.of A)) hA
    (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) M.obj
  have hSymqc : Sym.IsQuasicoherent :=
    isQuasicoherent_symmetricAlgebraSheaf B (Spec (.of A)) hA ⟨X, hX⟩ M.obj hMqc
  have hSymbd : AlgebraSheaf.SectionsBelowCutoff B (Spec (.of A)) hA Sym :=
    sectionsBelowCutoff_symmetricAlgebraSheaf B (Spec (.of A)) hA ⟨X, hX⟩ M.obj hMqc hMfp
  let Pa := boundedRelativeSpec B (Spec (.of A)) hA ⟨Sym, hSymqc⟩ hSymbd
  let eP : pushforwardAlgebra B (Spec (.of A)) hA Pa.obj ≅ Sym :=
    pushforwardAlgebraBoundedRelativeSpecIso B (Spec (.of A)) hA ⟨Sym, hSymqc⟩ hSymbd
  -- the module maps `ℱ ⟶ (Y_n ⟶ X)_* 𝒪`
  let φ := towerModuleHom B (Spec (.of A)) hA (X := ⟨X, hX⟩) (adicFibreFstHom A I B hA hX f)
    (adicFibreSuccHom A I B hA hX f) hcomm
    hN
    (finiteTowerAffine A I B hA hX f y hfin) tY hcart
    hcoh M eM.hom
  have hφ : ∀ n, Epi (φ n) := fun n => epi_towerModuleHom B (Spec (.of A)) hA (X := ⟨X, hX⟩)
    (adicFibreFstHom A I B hA hX f)
    (adicFibreSuccHom A I B hA hX f) hcomm
    hN
    (finiteTowerAffine A I B hA hX f y hfin) tY hcart
    hcoh hi M eM n
  have hXqc : IsQuasiCompactSpace B (Spec (.of A)) hA X :=
    isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B (Spec (.of A)) hA
      (X := ⟨X, hX⟩) (Y := ⟨yoneda.obj (baseObject A B hA), isAlgebraicSpace_yoneda B _ hA _⟩)
      (ObjectProperty.homMk f) hft.2
      (isAffineSpace_yoneda B _ hA (baseObject A B hA) (inferInstanceAs (IsAffine (Spec (.of A)))))
  -- the towers `Y_n` read over `X` are affine over `X`
  let Q : ∀ n, AffineOver B (Spec (.of A)) hA (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) :=
    fun n => ⟨towerOver B (Spec (.of A)) hA (adicFibreFstHom A I B hA hX f)
      (finiteTowerAffine A I B hA hX f y hfin) n,
      isAffineHom_comp B (Spec (.of A)) hA (y n).hom (adicFibreFstHom A I B hA hX f n).hom
        (IsFinite.isAffineHom (hfin n))
        (isAffineHom_of_isClosedImmersion B (Spec (.of A)) hA _ (hi n))⟩
  -- the morphisms `Y_n ⟶ P` over `X`
  let gO : ∀ n, (Q n).obj ⟶ Pa.obj := fun n =>
    (overHomEquivPushforwardAlgebraHom B (Spec (.of A)) hA (Q n).obj Pa).symm
      (eP.hom ≫ SymAlgSheaf.algebraLift B (Spec (.of A)) hA ⟨X, hX⟩
        (pushforwardAlgebra B (Spec (.of A)) hA (Q n).obj) M.obj (φ n))
  have hgO : ∀ n, pushforwardAlgebraMap B (Spec (.of A)) hA (gO n) =
      eP.hom ≫ SymAlgSheaf.algebraLift B (Spec (.of A)) hA ⟨X, hX⟩
        (pushforwardAlgebra B (Spec (.of A)) hA (Q n).obj) M.obj (φ n) := fun n =>
    pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm B (Spec (.of A)) hA _ Pa _
  have hcl : ∀ n, IsClosedImmersion B (Spec (.of A)) hA (gO n).left.hom := fun n =>
    isClosedImmersion_of_pushforwardAlgebraMap_eq_algebraLift B (Spec (.of A)) hA hXqc hMqc Pa (Q n)
      eP (φ n) (hφ n) (gO n) (hgO n)
  -- the module maps are compatible along the tower
  have hk := fun n =>
    adjunct_comp_pushforwardAlgebraMap_of_isPullback B (Spec (.of A)) hA
      (adicFibreSuccHom A I B hA hX f n) (adicFibreFstHom A I B hA hX f (n + 1))
      (adicFibreFstHom A I B hA hX f n) (hcomm n)
      (finiteTowerAffine A I B hA hX f y hfin n) (finiteTowerAffine A I B hA hX f y hfin (n + 1))
      (tY n) (hcart n) M.obj
      (((thickeningRestriction B (Spec (.of A)) hA (X := ⟨X, hX⟩) (adicFibreFstHom A I B hA hX f)
        (adicFibreSuccHom A I B hA hX f) hcomm
        hN).obj
          M).transitionIso n)
      (TowerSystem.restriction_obj_transitionIso _ _ _ _ M n)
      ((finiteTowerSystem A I B hA hX f y tY hcart hfin hft.1).transitionIso n)
      (isPushforwardTransposeCompatible_cartesianTransition B (Spec (.of A)) hA
        (adicFibreSuccHom A I B hA hX f n) (adicFibreFstHom A I B hA hX f (n + 1))
        (finiteTowerAffine A I B hA hX f y hfin n) (finiteTowerAffine A I B hA hX f y hfin (n + 1))
        (tY n) (hcart n))
      (eM.hom.app n) (eM.hom.app (n + 1)) (eM.hom.comm n)
  have hcomp : ∀ n, towerOverHom B (Spec (.of A)) hA (adicFibreFstHom A I B hA hX f)
      (adicFibreSuccHom A I B hA hX f) hcomm
      (finiteTowerAffine A I B hA hX f y hfin) tY hcart n ≫ gO (n + 1) = gO n := fun n =>
    comp_eq_of_pushforwardAlgebraMap_eq_algebraLift B (Spec (.of A)) hA hMqc Pa eP (φ n) (φ (n + 1))
      (gO n) (gO (n + 1)) (hgO n) (hgO (n + 1)) _ (hk n)
  have hPfp : IsFinitePresentation B (Spec (.of A)) hA Pa.obj.hom.hom :=
    isFinitePresentation_of_isFinitePresentation_pushforwardAlgebra B (Spec (.of A)) hA hXqc Pa
      (AlgebraSheaf.IsFinitePresentation.of_iso eP.symm
        (isFinitePresentation_symmetricAlgebraSheaf B (Spec (.of A)) hA ⟨X, hX⟩ M.obj hMqc hMfp))
  refine ⟨Pa.obj.left, Pa.obj.hom, Pa.2, hPfp, fun n => (gO n).left, fun n => Over.w (gO n),
    hcl, fun n => congrArg CommaMorphism.left (hcomp n)⟩

end AlgebraicGeometry.Space

end
