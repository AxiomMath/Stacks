module

public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.Tower
public import StacksFrontier.AlgebraicGeometry.PolarizedAlgebraization.ChartTransition
public import StacksFrontier.RingTheory.GradedTowerLimit.Basic
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayFlatOverBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjFlat.GradedPieces
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.SpecTarget
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFree
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# The graded rings of global sections of the truncated section algebras of a polarized tower

For a polarized tower `(X_n ⟶ Spec R_n, ℒ_n)` (`Stacks.PolarizedAlgebraization.PolarizedTower`) and
the cut `d₀` of [Stacks, Tag 0D4F], the truncated section algebras
`𝒜'_n = 𝒪 ⊕ ⨁_{d ≥ d₀} (f_n)_* ℒ_n^{⊗ d}` of the levels have graded rings of global sections
`A_n = Γ(Spec R_n, 𝒜'_n)`, and pulling sections back along the transitions gives graded ring maps
`A_{n + 1} ⟶ A_n`. This is a tower of graded algebras in the sense of
`Stacks.GradedTowerLimit.GradedTower`, over the inverse system `n ↦ Γ(Spec R_n, 𝒪)`, and it is
admissible: its pieces are finite projective (they are the global sections of finite locally free
modules on affine schemes), its degree-zero parts are the base rings, `A_{n + 1}` base changes to
`A_n`, and `A_0` is of finite presentation.

## Main definitions

* `Stacks.PolarizedAlgebraization.PolarizedTower.globalRing`: the inverse system
  `n ↦ Γ(Spec R_n, 𝒪)`.
* `Stacks.PolarizedAlgebraization.PolarizedTower.sectionTower`: the tower of graded rings of global
  sections.

## Main results

* `Stacks.PolarizedAlgebraization.PolarizedTower.isAdmissible_sectionTower`.

## References

* [Stacks Project, Tag 0D4T](https://stacks.math.columbia.edu/tag/0D4T)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjectiveDeformation
open Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily

universe u

namespace Stacks.PolarizedAlgebraization

namespace PolarizedTower

variable (T : PolarizedTower.{u})

/-- **The inverse system of rings of global functions** `n ↦ Γ(Spec R_n, 𝒪)`. -/
abbrev globalRing : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  T.R ⋙ Scheme.Spec.rightOp ⋙ Scheme.Γ

/-- The transition maps of the global rings are the transition maps of the rings, read through
`Γ(Spec R, 𝒪) ≅ R`. -/
theorem globalRing_tr (n : ℕ) :
    Stacks.GradedTowerLimit.tr T.globalRing n =
      (Scheme.ΓSpecIso _).hom ≫ T.ringMap (Nat.le_succ n) ≫ (Scheme.ΓSpecIso _).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

/-- `globalRing_tr` on elements. -/
theorem globalRing_tr_apply (n : ℕ) (x : T.globalRing.obj (op (n + 1))) :
    (Stacks.GradedTowerLimit.tr T.globalRing n).hom x =
      (Scheme.ΓSpecIso (T.R.obj (op n))).inv.hom
        ((T.ringMap (Nat.le_succ n)).hom ((Scheme.ΓSpecIso (T.R.obj (op (n + 1)))).hom.hom x)) := by
  rw [globalRing_tr]
  rfl

/-- The transition maps of the global rings are surjective. -/
theorem surjective_globalRing (n : ℕ) :
    Function.Surjective (Stacks.GradedTowerLimit.tr T.globalRing n).hom := by
  intro y
  obtain ⟨z, hz⟩ := T.surjective n ((Scheme.ΓSpecIso (T.R.obj (op n))).hom.hom y)
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (T.R.obj (op (n + 1)))).hom).2 z
  refine ⟨x, (T.globalRing_tr_apply n x).trans ?_⟩
  rw [hx]
  exact (congrArg _ hz).trans
    (congrArg (fun φ => φ.hom y) (Scheme.ΓSpecIso (T.R.obj (op n))).hom_inv_id)

/-- The transition maps of the global rings have locally nilpotent kernels. -/
theorem ker_globalRing_le_nilradical (n : ℕ) :
    RingHom.ker (Stacks.GradedTowerLimit.tr T.globalRing n).hom ≤
      nilradical (T.globalRing.obj (op (n + 1))) := by
  intro x hx
  rw [RingHom.mem_ker, globalRing_tr_apply] at hx
  have h0 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (T.R.obj (op n))).inv).1
    (hx.trans (map_zero _).symm)
  have hn := T.ker_le_nilradical n (RingHom.mem_ker.mpr h0)
  rw [mem_nilradical] at hn ⊢
  exact (IsNilpotent.map_iff
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (T.R.obj (op (n + 1)))).hom).1).mp hn

end PolarizedTower

/-- The base change of global sections carries the structure map to the structure map. -/
theorem sectionBaseChange_strHom {S S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (A : SheafGradedAlgebra S) (g : S' ⟶ S) (r : Γ(S, ⊤)) :
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A g (topSite S)
        (topSite S') (top_le_preimage_top g) (A.strHom ⊤ r) =
      (A.pullback g).strHom ⊤ (g.appLE ⊤ ⊤ (top_le_preimage_top g) r) := by
  rw [SheafGradedAlgebra.strHom_apply,
    Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange_of,
    SheafGradedAlgebra.strHom_apply]
  congr 1
  have h1 := Stacks.RelativeProj.Situation.pullbackSection_smul_appLE g (A.piece ((0 : ℕ) : ℤ))
    ⊤ ⊤ (top_le_preimage_top g) r (A.one ⊤)
  refine h1.trans ?_
  congr 1

/-- `sectionTransition` carries the structure map to the structure map. -/
theorem sectionTransition_strHom {S S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    {A : SheafGradedAlgebra S} {g : S' ⟶ S} {A' : SheafGradedAlgebra S'}
    (ψ : Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom (A.pullback g) A')
    (r : Γ(S, ⊤)) :
    sectionTransition ψ (A.strHom ⊤ r) = A'.strHom ⊤ (g.appLE ⊤ ⊤ (top_le_preimage_top g) r) := by
  show ψ.sectionHom ⊤ (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange A
    g (topSite S) (topSite S') (top_le_preimage_top g) (A.strHom ⊤ r)) = _
  rw [sectionBaseChange_strHom]
  exact Stacks.AlgebraicGeometry.ProjBundleSurjection.sectionHom_strHom ψ ⊤ _

/-- **The global sections of a finite locally free module on `Spec R` are a finite projective
module** over the ring of global functions: the module is quasi-coherent, being of finite
presentation, so it is the sheaf associated with its global sections, and [Stacks, Tag 05JM] and
[Stacks, Tag 00NX] read finite local freeness off on those. -/
theorem finite_projective_sections_of_isFiniteLocallyFree {R : CommRingCat.{u}}
    (F : (Spec R).Modules)
    (hF : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    Module.Finite Γ(Spec R, ⊤) Γ(F, ⊤) ∧ Module.Projective Γ(Spec R, ⊤) Γ(F, ⊤) := by
  have hfp :=
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.isFinitePresentation F hF
  have hqc : F.IsQuasicoherent := by
    obtain ⟨σ, -⟩ := _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData F
    exact σ.isQuasicoherent
  have hIso : IsIso F.fromTildeΓ := (isQuasicoherent_iff_isIso_fromTildeΓ F).mp hqc
  have h₁ : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (tilde (moduleSpecΓFunctor.obj F)) :=
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (h := hF)
      (asIso F.fromTildeΓ).symm
  obtain ⟨hfin, hproj⟩ := (Module.isFiniteLocallyFree_iff_finite_projective _ _).mp
    ((tilde_isFiniteLocallyFree_iff ↑R ↑(moduleSpecΓFunctor.obj F)).mp
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr h₁))
  let φ : R ≃+* Γ(Spec R, ⊤) := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv φ
  have := RingHomInvPair.of_ringEquiv_symm φ
  let e : moduleSpecΓFunctor.obj F ≃ₛₗ[(φ : R →+* Γ(Spec R, ⊤))] Γ(F, ⊤) :=
    { toFun := id
      invFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Module.Finite.of_surjective (e : moduleSpecΓFunctor.obj F →ₛₗ[(φ : R →+* Γ(Spec R, ⊤))]
    Γ(F, ⊤)) e.surjective, Module.Projective.of_equiv e⟩

/-- Over an open `U`, acting on the transported unit section of a module equal to the structure
sheaf is a bijection from the functions on `U`. -/
theorem bijective_smul_eqToHom_unitSections {S : Scheme.{u}} {M : S.Modules}
    (h : M = _root_.SheafOfModules.unit S.ringCatSheaf) (U : S.Opens) :
    Function.Bijective fun r : Γ(S, U) => r •
      ((eqToHom h.symm).app U
        ((Stacks.AlgebraicGeometry.ProjF1Dehomogenization.unitSections S.ringCatSheaf).eval
          (op U)) : Γ(M, U)) := by
  subst h
  refine ⟨fun r s hrs => ?_, fun x => ⟨x, ?_⟩⟩
  · exact (mul_one r).symm.trans (hrs.trans (mul_one s))
  · exact mul_one (M := Γ(S, U)) x

open scoped ChangeOfRings in
/-- **Base change of global sections between affine schemes, through `appTop`**: for a morphism
`f : Y ⟶ X` of affine schemes and a quasi-coherent `F` on `X`, pulling sections back gives
`Γ(Y, 𝒪) ⊗_{Γ(X, 𝒪)} Γ(X, F) ≅ Γ(Y, f^* F)`. This is
`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` over the whole of both schemes, with its
ring map `f.appLE ⊤ ⊤ _` replaced by the equal `f.appTop`. -/
theorem exists_pullbackSectionsBaseChangeIso_top {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ β : (ModuleCat.extendScalars f.appTop.hom).obj (ModuleCat.of Γ(X, ⊤) Γ(F, ⊤)) ≅
        ModuleCat.of Γ(Y, ⊤) Γ((Scheme.Modules.pullback f).obj F, ⊤),
      ∀ (r : Γ(Y, ⊤)) (a : Γ(F, ⊤)), β.hom (r ⊗ₜ[Γ(X, ⊤), f.appTop.hom] a) =
        r • (show Γ((Scheme.Modules.pullback f).obj F, ⊤) from
          Scheme.Modules.pullbackSection f F ⊤ ⊤ (top_le_preimage_top f) a) := by
  have gen : ∀ φ : Γ(X, ⊤) ⟶ Γ(Y, ⊤), φ = f.appTop →
      ∀ β₀ : (ModuleCat.extendScalars φ.hom).obj (ModuleCat.of Γ(X, ⊤) Γ(F, ⊤)) ≅
        ModuleCat.of Γ(Y, ⊤) Γ((Scheme.Modules.pullback f).obj F, ⊤),
      (∀ (r : Γ(Y, ⊤)) (a : Γ(F, ⊤)), β₀.hom (r ⊗ₜ[Γ(X, ⊤), φ.hom] a) =
        r • (show Γ((Scheme.Modules.pullback f).obj F, ⊤) from
          Scheme.Modules.pullbackSection f F ⊤ ⊤ (top_le_preimage_top f) a)) →
      ∃ β : (ModuleCat.extendScalars f.appTop.hom).obj (ModuleCat.of Γ(X, ⊤) Γ(F, ⊤)) ≅
          ModuleCat.of Γ(Y, ⊤) Γ((Scheme.Modules.pullback f).obj F, ⊤),
        ∀ (r : Γ(Y, ⊤)) (a : Γ(F, ⊤)), β.hom (r ⊗ₜ[Γ(X, ⊤), f.appTop.hom] a) =
          r • (show Γ((Scheme.Modules.pullback f).obj F, ⊤) from
            Scheme.Modules.pullbackSection f F ⊤ ⊤ (top_le_preimage_top f) a) := by
    rintro φ rfl β₀ hβ₀
    exact ⟨β₀, hβ₀⟩
  refine gen (f.appLE ⊤ ⊤ (top_le_preimage_top f)) (Scheme.Hom.appLE_eq_app f)
    (affinePullbackSectionsBaseChangeIso f F (isAffineOpen_top _) (isAffineOpen_top _)
      (top_le_preimage_top f)) fun r a => ?_
  rw [affinePullbackSectionsBaseChangeIso_tmul, affinePullbackSectionsBaseChangeIso_one_tmul]

namespace PolarizedTower

variable (T : PolarizedTower.{u}) (d₀ : ℕ) (hd₀ : 0 < d₀)

/-- The truncated section algebra of level `n`, on `Spec R_n`. -/
abbrev alg (n : ℕ) : SheafGradedAlgebra (Spec (T.R.obj (op n))) :=
  (T.deformation n).truncatedSectionAlgebra d₀ hd₀

/-- The transition of graded rings of global sections, `A_{n + 1} ⟶ A_n`. -/
abbrev sectionMap (n : ℕ) :
    (T.alg d₀ hd₀ (n + 1)).grading ⊤ →+*ᵍ (T.alg d₀ hd₀ n).grading ⊤ :=
  sectionTransition (AdmissibleDeformation.algebraPullbackSheafHom (T.deformationHom n) d₀ hd₀)

/-- The `Γ(Spec R_n, 𝒪)`-algebra structure of the ring of global sections of `𝒜'_n`. -/
@[instance_reducible]
def sectionAlgebra (n : ℕ) :
    Algebra (T.globalRing.obj (op n)) ((T.alg d₀ hd₀ n).sectionRing ⊤) :=
  (T.alg d₀ hd₀ n).sectionRingAlgebra ⊤

/-- The transition of graded rings of global sections carries the structure map to the structure
map, over the transition of the global rings. -/
theorem sectionMap_strHom (n : ℕ) (r : Γ(Spec (T.R.obj (op (n + 1))), ⊤)) :
    T.sectionMap d₀ hd₀ n ((T.alg d₀ hd₀ (n + 1)).strHom ⊤ r) =
      (T.alg d₀ hd₀ n).strHom ⊤ ((Stacks.GradedTowerLimit.tr T.globalRing n).hom r) := by
  refine (sectionTransition_strHom _ r).trans ?_
  congr 1

/-- **The tower of graded rings of global sections** `A_n = Γ(Spec R_n, 𝒜'_n)`, graded by
`Γ(Spec R_n, 𝒪)`-submodules, with the transitions `sectionMap`. -/
def sectionTower : Stacks.GradedTowerLimit.GradedTower T.globalRing where
  A n := (T.alg d₀ hd₀ n).sectionRing ⊤
  algebra n := T.sectionAlgebra d₀ hd₀ n
  𝒜 n := letI := T.sectionAlgebra d₀ hd₀ n
    GradedRing.toSubmodules ((T.alg d₀ hd₀ n).grading ⊤) ((T.alg d₀ hd₀ n).strHom_mem ⊤)
  gradedAlgebra n := letI := T.sectionAlgebra d₀ hd₀ n
    GradedRing.instGradedRingToSubmodules _ _
  ρ n := (T.sectionMap d₀ hd₀ n).toRingHom
  ρ_mem n _ _ hx := (T.sectionMap d₀ hd₀ n).map_mem hx
  ρ_algebraMap n r := T.sectionMap_strHom d₀ hd₀ n r

/-- The transitions of `sectionTower` are the maps `sectionMap`. -/
@[simp] theorem sectionTower_ρ (n : ℕ) :
    (T.sectionTower d₀ hd₀).ρ n = (T.sectionMap d₀ hd₀ n).toRingHom := rfl

/-- **The tower of global sections is compatible with base change** when the transition
`φ_n^* 𝒜'_{n + 1} ⟶ 𝒜'_n` is an isomorphism in degree `d`: the base change map
`Rₙ ⊗ (A_{n + 1})_d ⟶ (A_n)_d` is the base change of global sections of the quasi-coherent
`𝒜'_{n + 1, d}` along the morphism of affine schemes `Spec R_n ⟶ Spec R_{n + 1}`, followed by the
sections of that isomorphism. -/
theorem bijective_baseChangeMap (n d : ℕ)
    (hiso : IsIso ((AdmissibleDeformation.algebraPullbackHom (T.deformationHom n) d₀ hd₀).app
      (d : ℤ))) :
    Function.Bijective ((T.sectionTower d₀ hd₀).baseChangeMap n d) := by
  let := (T.alg d₀ hd₀ (n + 1)).sectionRingAlgebra ⊤
  let := (T.alg d₀ hd₀ n).sectionRingAlgebra ⊤
  let : Algebra Γ(Spec (T.R.obj (op (n + 1))), ⊤) Γ(Spec (T.R.obj (op n)), ⊤) :=
    (Stacks.GradedTowerLimit.tr T.globalRing n).hom.toAlgebra
  let g := T.baseMap (Nat.le_succ n)
  let ψ := AdmissibleDeformation.algebraPullbackSheafHom (T.deformationHom n) d₀ hd₀
  have : IsIso (ψ.app (d : ℤ)) := hiso
  let F := (T.alg d₀ hd₀ (n + 1)).piece (d : ℤ)
  obtain ⟨β, hβ⟩ := exists_pullbackSectionsBaseChangeIso_top g F
  let e := (T.alg d₀ hd₀ (n + 1)).gradingEquiv ⊤ d
  let e' := (T.alg d₀ hd₀ n).gradingEquiv ⊤ d
  let G : TensorProduct Γ(Spec (T.R.obj (op (n + 1))), ⊤) Γ(Spec (T.R.obj (op n)), ⊤)
      Γ((T.alg d₀ hd₀ (n + 1)).piece (d : ℤ), ⊤) →+ (T.sectionTower d₀ hd₀).𝒜 n d :=
    e'.toAddMonoidHom.comp (((ψ.app (d : ℤ)).app ⊤).hom.comp β.hom.hom.toAddMonoidHom)
  have hG : Function.Bijective G :=
    e'.bijective.comp ((ConcreteCategory.bijective_of_isIso ((ψ.app (d : ℤ)).app ⊤)).comp
      (ConcreteCategory.bijective_of_isIso β.hom))
  let E := LinearEquiv.lTensor Γ(Spec (T.R.obj (op n)), ⊤) e
  have key : ∀ t, (T.sectionTower d₀ hd₀).baseChangeMap n d (E t) = G t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact (congrArg _ (map_zero E)).trans ((map_zero _).trans (map_zero G).symm)
    | tmul r a =>
      have hρ : (T.sectionTower d₀ hd₀).trPiece n d (e a) =
          e' ((ψ.app (d : ℤ)).app ⊤ (Scheme.Modules.pullbackSection g _ ⊤ ⊤
            (top_le_preimage_top g) a)) :=
        Subtype.ext <| (congrArg (ψ.sectionHom ⊤)
          (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sectionBaseChange_of _ g
            (topSite _) (topSite _) (top_le_preimage_top g) d a)).trans
          (Stacks.AlgebraicGeometry.RelativeProjMapDomain.SheafGradedAlgebraHom.sectionHom_of ψ ⊤ _)
      have hE : E (TensorProduct.tmul _ r a) = TensorProduct.tmul _ r (e a) :=
        LinearEquiv.lTensor_tmul _ _ _ _
      exact ((congrArg _ hE).trans
        ((T.sectionTower d₀ hd₀).baseChangeMap_tmul n d r (e a))).trans
        ((congrArg (fun x : GradedRing.toSubmodules ((T.alg d₀ hd₀ n).grading ⊤)
            ((T.alg d₀ hd₀ n).strHom_mem ⊤) d => r • x) hρ).trans
          ((map_smul e' r _).symm.trans (congrArg e'
            ((Scheme.Modules.Hom.app_smul _ r _).symm.trans (congrArg _ (hβ r a).symm)))))
    | add x y hx hy =>
      exact (congrArg _ (map_add E x y)).trans ((map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add G x y).symm))
  have h : ⇑((T.sectionTower d₀ hd₀).baseChangeMap n d) = G ∘ E.symm :=
    funext fun t => (congrArg _ (E.apply_symm_apply t).symm).trans (key (E.symm t))
  rw [h]
  exact hG.comp E.symm.bijective

/-- **The tower of global sections is admissible**, given the conclusions of
[Stacks, Tag 0D4F] at the cut `d₀`: the pieces `𝒜'_d`, `d ≥ d₀`, are finite locally free; the
truncated section algebra of each level is of finite presentation over the whole base; and the
transitions `φ_n^* 𝒜'_{n + 1} ⟶ 𝒜'_n` are isomorphisms. -/
theorem isAdmissible_sectionTower
    (hflf : ∀ (n d : ℕ), d₀ ≤ d →
      _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (R := (T.deformation n).S'.ringCatSheaf) ((T.deformation n).sectionPiece d))
    (hfp : ∀ n : ℕ, RingHom.FinitePresentation ((T.alg d₀ hd₀ n).strHom ⊤))
    (hiso : ∀ (n : ℕ) (k : ℤ),
      IsIso ((AdmissibleDeformation.algebraPullbackHom (T.deformationHom n) d₀ hd₀).app k)) :
    (T.sectionTower d₀ hd₀).IsAdmissible := by
  have hone : ∀ n : ℕ, Function.Bijective fun r : Γ(Spec (T.R.obj (op n)), ⊤) =>
      r • (T.alg d₀ hd₀ n).one ⊤ := fun n =>
    bijective_smul_eqToHom_unitSections
      (Stacks.AlgebraicGeometry.SectionAlgebra.tailPiece_eq_unit
        (T.deformation n).laurentPushforward d₀ rfl) ⊤
  have hzero : ∀ n : ℕ, Function.Bijective fun r : T.globalRing.obj (op n) =>
      (⟨algebraMap (T.globalRing.obj (op n)) ((T.sectionTower d₀ hd₀).A n) r,
        SetLike.algebraMap_mem_graded ((T.sectionTower d₀ hd₀).𝒜 n) r⟩ :
          (T.sectionTower d₀ hd₀).𝒜 n 0) := by
    intro n
    let := T.sectionAlgebra d₀ hd₀ n
    have h : (fun r : T.globalRing.obj (op n) =>
        (⟨algebraMap (T.globalRing.obj (op n)) ((T.sectionTower d₀ hd₀).A n) r,
          SetLike.algebraMap_mem_graded ((T.sectionTower d₀ hd₀).𝒜 n) r⟩ :
            (T.sectionTower d₀ hd₀).𝒜 n 0)) =
        (T.alg d₀ hd₀ n).gradingEquiv ⊤ 0 ∘
          fun r : Γ(Spec (T.R.obj (op n)), ⊤) => r • (T.alg d₀ hd₀ n).one ⊤ :=
      funext fun r => Subtype.ext (SheafGradedAlgebra.strHom_apply _ _ _)
    rw [h]
    exact (LinearEquiv.bijective _).comp (hone n)
  have hpieces : ∀ n d : ℕ,
      Module.Finite (T.globalRing.obj (op n)) ((T.sectionTower d₀ hd₀).𝒜 n d) ∧
        Module.Projective (T.globalRing.obj (op n)) ((T.sectionTower d₀ hd₀).𝒜 n d) := by
    intro n d
    let := T.sectionAlgebra d₀ hd₀ n
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · let e := LinearEquiv.ofBijective
        ((Algebra.linearMap (T.globalRing.obj (op n)) ((T.sectionTower d₀ hd₀).A n)).codRestrict
          ((T.sectionTower d₀ hd₀).𝒜 n 0) fun r => SetLike.algebraMap_mem_graded _ r) (hzero n)
      exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
    · suffices h : Module.Finite Γ(Spec (T.R.obj (op n)), ⊤) Γ((T.alg d₀ hd₀ n).piece (d : ℤ), ⊤) ∧
          Module.Projective Γ(Spec (T.R.obj (op n)), ⊤) Γ((T.alg d₀ hd₀ n).piece (d : ℤ), ⊤) by
        obtain ⟨h1, h2⟩ := h
        let := (T.alg d₀ hd₀ n).sectionRingAlgebra ⊤
        show Module.Finite Γ(Spec (T.R.obj (op n)), ⊤) (GradedRing.toSubmodules
            ((T.alg d₀ hd₀ n).grading ⊤) ((T.alg d₀ hd₀ n).strHom_mem ⊤) d) ∧
          Module.Projective Γ(Spec (T.R.obj (op n)), ⊤) (GradedRing.toSubmodules
            ((T.alg d₀ hd₀ n).grading ⊤) ((T.alg d₀ hd₀ n).strHom_mem ⊤) d)
        exact ⟨Module.Finite.equiv ((T.alg d₀ hd₀ n).gradingEquiv ⊤ d),
          Module.Projective.of_equiv' ((T.alg d₀ hd₀ n).gradingEquiv ⊤ d)⟩
      by_cases hdd : d₀ ≤ d
      · obtain ⟨e⟩ := AdmissibleDeformation.IsTruncatedSectionAlgebraWithComparison.piece_iso _
          ((T.deformation n).isTruncatedSectionAlgebraWithComparison_truncatedSectionAlgebra d₀ hd₀)
          d hdd
        exact finite_projective_sections_of_isFiniteLocallyFree _
          (_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (h := hflf n d hdd)
            e.symm)
      · have h0 : ∀ a : Γ((T.alg d₀ hd₀ n).piece (d : ℤ), ⊤), a = 0 := fun a =>
          Stacks.AlgebraicGeometry.SectionAlgebra.eq_zero_of_tailPiece
            (T.deformation n).laurentPushforward d₀ (by omega) (by omega) (op ⊤) a
        have : Subsingleton Γ((T.alg d₀ hd₀ n).piece (d : ℤ), ⊤) :=
          ⟨fun a b => (h0 a).trans (h0 b).symm⟩
        exact ⟨inferInstance, inferInstance⟩
  refine ⟨T.surjective_globalRing, T.ker_globalRing_le_nilradical, fun n d => (hpieces n d).1,
    fun n d => (hpieces n d).2, hzero, fun n d => T.bijective_baseChangeMap d₀ hd₀ n d (hiso n d),
    hfp 0⟩

end PolarizedTower

end Stacks.PolarizedAlgebraization

end
