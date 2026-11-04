module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.Deformation.ToposThickening.BaseThickeningExtensionClass
public import StacksFrontier.Deformation.ToposThickening.InverseImageExtensionSolutions
public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Parametrizing the solutions of a deformation problem of ringed topoi (Stacks 0GQ9)

In the situation (08UF) of **Stacks 08UF** — a first order thickening
`t : (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` with ideal `𝒥`, a morphism
`f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)`, an `𝒪`-module `𝒢` and `c : f⁻¹𝒥 ⟶ 𝒢` — the proof of
**Stacks 0GQ9** reads a solution as a square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of
`(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras (classified by **Stacks 0GQ5** for `t ∘ f`) together with a morphism
`(Sh(𝒞), 𝒪') ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` over `(Sh(ℬ'), 𝒪_{ℬ'})` compatible with `f` and `c` — "of
course this is the same thing as saying `𝒪'` is a solution". This file proves that
identification and assembles **Stacks 0GQ9** from it, from **Stacks 0GQ5** for `t ∘ f` and from
**Stacks 0GQ7** for `(Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` and `c`.

## Main definitions

* `Deformation.ToposThickening.RingedToposExtensionProblem.compProblem`: the problem of
  **Stacks 0GQ5** for `t ∘ f` and `𝒢`.
* `.prescribedPullbackMap`: the prescribed map read as an `𝒪`-linear map `c : f^*𝒥 ⟶ 𝒢`.
* `.toCompSolution`, `.toCompatibleHom`, `.ofCompatibleHom`: the identification of solutions
  with extensions carrying a compatible lift.
* `.classesEquivCompClasses`: isomorphism classes of solutions as the classes of extensions of
  `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras containing a solution.
* `.derivedExtFibre`: the fibre of `Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)`
  over the image of `ξ`.
* `.solutionClassesEquivDerivedExtFibre`: **Stacks 0GQ9**, the canonical bijection.

## Main results

* `.exists_mk_toCompSolution_iff`: such a class contains a solution exactly when a compatible
  lift exists.
* `.solutionClassesEquivDerivedExtFibre_mk`: the bijection sends `[𝒪']` to the class of `𝒪'`
  under **Stacks 0GQ5** for `t ∘ f`.

## Implementation notes

The input is a problem `S : RingedToposExtensionProblem X B` of **Stacks 08UF**; nothing else is
carried. `t`, `𝒥`, the extension `𝒪_{ℬ'}` and `ξ` are built in
`StacksFrontier/Deformation/ToposThickening/BaseThickeningExtensionClass.lean`. The problem records
`f⁻¹𝒥` as `S.I` with its identification with the kernel of `f⁻¹(t^♯)`; the inverse image of the
base ideal `𝒥` is identified with it (`invBaseIdealToIdeal`, from the left exactness of `f⁻¹`), and
the prescribed map is transposed to the `𝒪`-linear `c : f^*𝒥 ⟶ 𝒢` (`prescribedPullbackMap`)
through which the image of `ξ` is formed. `Lf^*` is
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback`, the map
`Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)` is precomposition with the canonical
map `Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}} ⟶ NL_{𝒪/𝒪_{ℬ'}}`
(`Deformation.ToposThickening.LiftingMorphismDerived.restrictExtClass`), and the image of `ξ` is
`Deformation.ToposThickening.LiftingMorphismDerived.pullbackExtClass`. All ringed topoi are
`RingedTopos.{u, u, u}`, as **Stacks 0GQ5** (applied to `t`, with source `(Sh(ℬ), 𝒪_ℬ)`) requires.

## References

* [Stacks Project, Tag 0GQ9](https://stacks.math.columbia.edu/tag/0GQ9)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafFunctorId)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Deformation.ToposThickening.InverseImageExtension (invImage baseIso invIdeal invKernelIncl
  invKernelIncl_mem invIdealPreimage invKernelIncl_invIdealPreimage prescribedAdjoint
  restrictedIdeal comp_fSharpInverseImage_eq Data)

universe u v w

namespace Deformation.ToposThickening.RingedToposExtensionProblem

section SectionwiseLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M N P : SheafOfModules.{w} R}

/-- The factorization of a morphism `a : M ⟶ P` of sheaves of modules through a morphism
`i : N ⟶ P` which is injective on sections and whose sections contain those of `a`. -/
def sectionwiseLift (i : N ⟶ P) (a : M ⟶ P) (hi : ∀ U, Function.Injective (i.val.app U))
    (ha : ∀ U m, ∃ n, i.val.app U n = a.val.app U m) : M ⟶ N where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun m => (ha U m).choose
          map_add' := fun m m' => hi U <| (ha U _).choose_spec.trans <| by
            rw [map_add, map_add, (ha U m).choose_spec, (ha U m').choose_spec]
          map_smul' := fun r m => hi U <| (ha U _).choose_spec.trans <| by
            rw [map_smul, map_smul, (ha U m).choose_spec]
            rfl }
      naturality := fun {U V} f => by
        ext m
        apply hi V
        exact (ha V _).choose_spec.trans ((PresheafOfModules.naturality_apply a.val f m).trans
          ((congrArg (fun y => P.val.map f y) (ha U m).choose_spec.symm).trans
            (PresheafOfModules.naturality_apply i.val f _).symm)) }

/-- The lift followed by `i` is `a`, on sections. -/
theorem sectionwiseLift_val_app (i : N ⟶ P) (a : M ⟶ P)
    (hi : ∀ U, Function.Injective (i.val.app U))
    (ha : ∀ U m, ∃ n, i.val.app U n = a.val.app U m) (U : Cᵒᵖ) (m : M.val.obj U) :
    i.val.app U ((sectionwiseLift i a hi ha).val.app U m) = a.val.app U m :=
  (ha U m).choose_spec

/-- The lift followed by `i` is `a`. -/
theorem sectionwiseLift_comp (i : N ⟶ P) (a : M ⟶ P)
    (hi : ∀ U, Function.Injective (i.val.app U))
    (ha : ∀ U m, ∃ n, i.val.app U n = a.val.app U m) :
    sectionwiseLift i a hi ha ≫ i = a := by
  ext U m
  exact sectionwiseLift_val_app i a hi ha U m

end SectionwiseLift

variable {X B : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})]
  (S : RingedToposExtensionProblem X B)

/-! ### The problem of Stacks 0GQ5 for `t ∘ f` -/

/-- The composite `t ∘ f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ), 𝒪_{ℬ'})`. -/
abbrev compBase : RingedToposHom X S.thickenedBase := S.baseThickening.comp S.f

/-- The problem of **Stacks 0GQ5** for `t ∘ f` and `𝒢`: its solutions are the square-zero
extensions `0 ⟶ 𝒢 ⟶ 𝒪' ⟶ 𝒪 ⟶ 0` of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras. -/
abbrev compProblem : RingedToposExtensionProblem X S.thickenedBase :=
  ofTrivialBase S.compBase S.G

/-- The comparison `(t ∘ f)⁻¹𝒪_{ℬ'} ≅ f⁻¹𝒪_{ℬ'}`: the inverse image along the composite is the
iterated inverse image, and the inverse image along the identity of `Sh(ℬ)` is the identity. -/
def compBaseIso : (inverseImageCommRingFunctor S.compBase.toToposHom).obj S.baseExtension ≅
    (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension :=
  (baseIso S.baseThickening S.f).symm ≪≫
    (invImage S.f).mapIso ((pullbackCommRingSheafFunctorId B.J).app S.baseExtension)

/-- The structure map of `t ∘ f` is `f⁻¹(t^♯) ≫ f^♯`, read through `compBaseIso`. -/
theorem compBaseIso_hom_comp_fSharpInverseImage :
    S.compBaseIso.hom ≫ (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction ≫
        S.f.fSharpInverseImage = S.compBase.fSharpInverseImage := by
  rw [comp_fSharpInverseImage_eq, baseThickening_fSharpInverseImage]
  refine Eq.trans ?_ (congrArg (fun m => (baseIso S.baseThickening S.f).inv ≫ m ≫
    S.f.fSharpInverseImage) (Functor.map_comp (invImage S.f)
      ((pullbackCommRingSheafFunctorId B.J).hom.app S.baseExtension) S.baseReduction).symm)
  simp only [compBaseIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

/-! ### The prescribed map `c`, read as an `𝒪`-linear map `f^*𝒥 ⟶ 𝒢` -/

/-- `f⁻¹(t^♯) : f⁻¹𝒪_{ℬ'} ⟶ f⁻¹𝒪_ℬ`, on underlying sheaves of rings. -/
abbrev invBaseReduction :
    (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension) ⟶
      (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O) :=
  (sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction)

omit [X.J.HasSheafCompose (forget CommRingCat)] in
/-- The inclusion of the inverse-image base ideal is injective on sections. -/
theorem idealInclusion_injective (U : X.Cᵒᵖ) :
    Function.Injective (S.idealInclusion.val.app U) := by
  intro a b h
  obtain ⟨x, -, hx⟩ := S.idealUniversal U _ (S.idealZero U a)
  exact (hx a rfl).trans (hx b h.symm).symm

/-- `f⁻¹(t^♯)` is locally surjective, `f⁻¹` preserving epimorphisms. -/
instance isLocallySurjective_invBaseReduction :
    Sheaf.IsLocallySurjective S.invBaseReduction :=
  haveI := InverseImageExtension.isLocallySurjective_invImage_map S.f S.baseReduction
    S.baseLocallySurjective
  ⟨fun {_} s ↦ Presheaf.imageSieve_mem X.J
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom s⟩

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify B.J AddCommGrpCat.{u}] [B.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison `f⁻¹𝒥 ⟶ S.I` over `f⁻¹𝒪_{ℬ'}`: both are the kernel of `f⁻¹(t^♯)`. -/
def invBaseIdealToIdealRestricted :
    (SheafOfModules.restrictScalars S.invBaseReduction).obj
        (invIdeal S.f (F := S.baseIdeal)) ⟶
      (SheafOfModules.restrictScalars S.invBaseReduction).obj S.I :=
  sectionwiseLift S.idealInclusion (invKernelIncl S.baseThickeningSolution S.f)
    S.idealInclusion_injective (fun U x => by
      obtain ⟨a, ha, -⟩ := S.idealUniversal U _
        (invKernelIncl_mem S.baseThickeningSolution S.f U x)
      exact ⟨a, ha⟩)

/-- **The comparison `f⁻¹𝒥 ⟶ S.I`**, `f⁻¹𝒪_ℬ`-linear: the inverse image of the base ideal and the
ideal of the problem are both the kernel of `f⁻¹(t^♯)`. -/
def invBaseIdealToIdeal : invIdeal S.f (F := S.baseIdeal) ⟶ S.I :=
  (Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      S.invBaseReduction).preimage
    S.invBaseIdealToIdealRestricted

/-- The comparison `f⁻¹𝒥 ⟶ S.I` is compatible with the two inclusions into `f⁻¹𝒪_{ℬ'}`. -/
theorem idealInclusion_invBaseIdealToIdeal (U : X.Cᵒᵖ)
    (x : (invIdeal S.f (F := S.baseIdeal)).val.obj U) :
    S.idealInclusion.val.app U (S.invBaseIdealToIdeal.val.app U x) =
      (invKernelIncl S.baseThickeningSolution S.f).val.app U x := by
  have h := congrArg (fun φ => φ.val.app U x)
    ((Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective
      S.invBaseReduction).map_preimage S.invBaseIdealToIdealRestricted)
  exact (congrArg (S.idealInclusion.val.app U) h).trans <| sectionwiseLift_val_app
    S.idealInclusion (invKernelIncl S.baseThickeningSolution S.f) S.idealInclusion_injective _ U x

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The prescribed map of (08UF), as an `𝒪`-linear map `c : f^*𝒥 ⟶ 𝒢`**: the adjoint, under
extension and restriction of scalars along `f^♯`, of the `f⁻¹𝒪_ℬ`-linear map
`f⁻¹𝒥 ≅ S.I ⟶ 𝒢` of the problem. -/
def prescribedPullbackMap :
    S.f.toRingedToposModulesHom.pullbackModules.obj S.baseIdeal ⟶ S.G :=
  ((Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction X.J
    (Stacks.Sheaves.RingedToposModules.fSharpCommRing S.f.toRingedToposModulesHom)
    (Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf S.f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf B.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).homEquiv _ _).symm
    (S.invBaseIdealToIdeal ≫ S.c)

/-- The adjoint of `prescribedPullbackMap` is `f⁻¹𝒥 ≅ S.I ⟶ 𝒢`. -/
theorem prescribedAdjoint_prescribedPullbackMap :
    prescribedAdjoint S.f S.prescribedPullbackMap = S.invBaseIdealToIdeal ≫ S.c :=
  Equiv.apply_symm_apply _ _

/-- The section of the kernel of `f⁻¹(t^♯)` given by a section of `S.I`. -/
def idealKernelSection (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    Stacks.Sites.Conormal.kernelIdeal
      ((invImage S.f).map S.baseThickeningSolution.reduction).hom U :=
  ⟨S.idealInclusion.val.app U x, S.idealZero U x⟩

/-- **`c` on the kernel of `f⁻¹(t^♯)` is the prescribed map of the problem.** -/
theorem prescribedAdjoint_invIdealPreimage (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    (prescribedAdjoint S.f S.prescribedPullbackMap).val.app U
        (invIdealPreimage S.baseThickeningSolution S.f U (S.idealKernelSection U x)) =
      S.c.val.app U x := by
  rw [S.prescribedAdjoint_prescribedPullbackMap]
  change S.c.val.app U (S.invBaseIdealToIdeal.val.app U _) = _
  congr 1
  refine S.idealInclusion_injective U ?_
  rw [S.idealInclusion_invBaseIdealToIdeal]
  exact invKernelIncl_invIdealPreimage S.baseThickeningSolution S.f U _

/-! ### Solutions as extensions of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras with a compatible lift -/

/-- A solution of (08UF), read as a square-zero extension of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras: a
solution of the problem of **Stacks 0GQ5** for `t ∘ f` and `𝒢`. -/
def toCompSolution (P : S.CompatibleFirstOrderThickening) :
    S.compProblem.CompatibleFirstOrderThickening where
  extension := P.extension
  reduction := P.reduction
  locallySurjective := P.locallySurjective
  squareZero := P.squareZero
  baseMap := S.compBaseIso.hom ≫ P.baseMap
  baseMap_reduction :=
    (Category.assoc _ _ _).trans (((congrArg (S.compBaseIso.hom ≫ ·) P.baseMap_reduction).trans
      S.compBaseIso_hom_comp_fSharpInverseImage).trans ((Category.id_comp _).symm.trans
        (congrArg (· ≫ S.compBase.fSharpInverseImage)
          ((inverseImageCommRingFunctor S.compBase.toToposHom).map_id S.baseExtension).symm)))
  kernelInclusion := P.kernelInclusion
  kernelZero := P.kernelZero
  kernelUniversal := P.kernelUniversal
  baseMap_ideal := fun U a => by
    have h : IsIso S.compProblem.baseReduction := inferInstance
    rw [S.compProblem.idealInclusion_val_app_eq_zero h U a,
      S.compProblem.c_val_app_eq_zero h U a, map_zero]
    exact (map_zero _).symm

/-- The datum of **Stacks 0GQ8** comparing a square-zero extension `𝒪'` of
`(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras with the extension `𝒪_{ℬ'}` of `𝒪_ℬ` by `𝒥` along `f` and `c`. -/
abbrev liftData (Q : S.compProblem.CompatibleFirstOrderThickening) :
    Data S.baseThickening S.f :=
  Data.ofSolutions (g := S.f) S.baseThickeningSolution Q S.prescribedPullbackMap

/-- The map from `f⁻¹𝒪_{ℬ'}` of a solution is a morphism `(Sh(𝒞), 𝒪') ⟶ (Sh(ℬ), 𝒪_{ℬ'})` over
`(Sh(ℬ), 𝒪_{ℬ'})` compatible with `f` and `c`. -/
def toCompatibleHom (P : S.CompatibleFirstOrderThickening) :
    (S.liftData (S.toCompSolution P)).CompatibleHom where
  hom := P.baseMap
  base_comm := by
    change (invImage S.f).map ((pullbackCommRingSheafFunctorId B.J).hom.app S.baseExtension) ≫
        P.baseMap = (baseIso S.baseThickening S.f).hom ≫ S.compBaseIso.hom ≫ P.baseMap
    simp only [compBaseIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  proj_comm := P.baseMap_reduction
  kernel_comm := fun U s => by
    obtain ⟨x, hx, -⟩ := S.idealUniversal U s.1 s.2
    have hs : s = S.idealKernelSection U x := Subtype.ext hx.symm
    subst hs
    refine (P.baseMap_ideal U x).trans ?_
    change P.kernelInclusion.val.app U (S.c.val.app U x) =
      P.kernelInclusion.val.app U ((prescribedAdjoint S.f S.prescribedPullbackMap).val.app U
        (invIdealPreimage S.baseThickeningSolution S.f U (S.idealKernelSection U x)))
    rw [S.prescribedAdjoint_invIdealPreimage]

/-- A square-zero extension of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras together with a morphism
`(Sh(𝒞), 𝒪') ⟶ (Sh(ℬ), 𝒪_{ℬ'})` compatible with `f` and `c` is a solution of (08UF). -/
def ofCompatibleHom (Q : S.compProblem.CompatibleFirstOrderThickening)
    (h : (S.liftData Q).CompatibleHom) : S.CompatibleFirstOrderThickening where
  extension := Q.extension
  reduction := Q.reduction
  locallySurjective := Q.locallySurjective
  squareZero := Q.squareZero
  baseMap := h.hom
  baseMap_reduction := h.proj_comm
  kernelInclusion := Q.kernelInclusion
  kernelZero := Q.kernelZero
  kernelUniversal := Q.kernelUniversal
  baseMap_ideal := fun U x => by
    refine (h.kernel_comm U (S.idealKernelSection U x)).trans ?_
    change Q.kernelInclusion.val.app U ((prescribedAdjoint S.f S.prescribedPullbackMap).val.app U
        (invIdealPreimage S.baseThickeningSolution S.f U (S.idealKernelSection U x))) = _
    rw [S.prescribedAdjoint_invIdealPreimage]
    rfl

/-- The map from `f⁻¹𝒪_{ℬ'}` of a lift, read through `compBaseIso`, is the structure map of the
extension of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras. -/
theorem compBaseIso_hom_comp_compatibleHom (Q : S.compProblem.CompatibleFirstOrderThickening)
    (h : (S.liftData Q).CompatibleHom) : S.compBaseIso.hom ≫ h.hom = Q.baseMap := by
  have hb : (invImage S.f).map ((pullbackCommRingSheafFunctorId B.J).hom.app S.baseExtension) ≫
      h.hom = (baseIso S.baseThickening S.f).hom ≫ Q.baseMap := h.base_comm
  exact (Category.assoc _ _ _).trans
    ((congrArg ((baseIso S.baseThickening S.f).inv ≫ ·) hb).trans (Iso.inv_hom_id_assoc _ _))

/-- An isomorphism of solutions of (08UF) is one of the extensions of
`(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras. -/
def isoCompSolution {P₁ P₂ : S.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso P₁ P₂) :
    CompatibleFirstOrderThickening.Iso (S.toCompSolution P₁) (S.toCompSolution P₂) where
  hom := e.hom
  reduction_comm := e.reduction_comm
  baseMap_comm := (Category.assoc _ _ _).trans (congrArg (S.compBaseIso.hom ≫ ·) e.baseMap_comm)
  kernel_comm := e.kernel_comm

/-- An isomorphism of the extensions of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras underlying two solutions of
(08UF) is one of the solutions. -/
def isoOfCompSolution {P₁ P₂ : S.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso (S.toCompSolution P₁) (S.toCompSolution P₂)) :
    CompatibleFirstOrderThickening.Iso P₁ P₂ where
  hom := e.hom
  reduction_comm := e.reduction_comm
  baseMap_comm := (cancel_epi S.compBaseIso.hom).1 ((Category.assoc _ _ _).symm.trans
    e.baseMap_comm)
  kernel_comm := e.kernel_comm

omit [X.J.HasSheafCompose (forget AddCommGrpCat)] [B.J.HasSheafCompose (forget AddCommGrpCat)]
  [HasSheafify B.J AddCommGrpCat] [B.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasWeakSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Two solutions are isomorphic exactly when their underlying extensions are. -/
theorem isomorphic_iff_compSolution (P₁ P₂ : S.CompatibleFirstOrderThickening) :
    CompatibleFirstOrderThickening.Isomorphic P₁ P₂ ↔
      CompatibleFirstOrderThickening.Isomorphic (S.toCompSolution P₁) (S.toCompSolution P₂) :=
  ⟨fun ⟨e⟩ => ⟨S.isoCompSolution e⟩, fun ⟨e⟩ => ⟨S.isoOfCompSolution e⟩⟩

/-- The solution built from an extension and a compatible lift has that extension as its
underlying extension of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras. -/
def toCompSolutionOfCompatibleHomIso (Q : S.compProblem.CompatibleFirstOrderThickening)
    (h : (S.liftData Q).CompatibleHom) :
    CompatibleFirstOrderThickening.Iso (S.toCompSolution (S.ofCompatibleHom Q h)) Q where
  hom := CategoryTheory.Iso.refl Q.extension
  reduction_comm := Category.id_comp _
  baseMap_comm := (Category.comp_id _).trans (S.compBaseIso_hom_comp_compatibleHom Q h)
  kernel_comm := fun _ _ => rfl

/-- A compatible lift transported along an isomorphism of extensions. -/
def compatibleHomOfIso {Q₁ Q₂ : S.compProblem.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso Q₁ Q₂) (h : (S.liftData Q₁).CompatibleHom) :
    (S.liftData Q₂).CompatibleHom where
  hom := h.hom ≫ e.hom.hom
  base_comm := by
    have hb : (invImage S.f).map ((pullbackCommRingSheafFunctorId B.J).hom.app S.baseExtension) ≫
        h.hom = (baseIso S.baseThickening S.f).hom ≫ Q₁.baseMap := h.base_comm
    change (invImage S.f).map ((pullbackCommRingSheafFunctorId B.J).hom.app S.baseExtension) ≫
        h.hom ≫ e.hom.hom = (baseIso S.baseThickening S.f).hom ≫ Q₂.baseMap
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ e.hom.hom) hb).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e.baseMap_comm)))
  proj_comm := by
    have hp : h.hom ≫ Q₁.reduction = _ := h.proj_comm
    exact (Category.assoc _ _ _).trans ((congrArg (h.hom ≫ ·) e.reduction_comm).trans hp)
  kernel_comm := fun U s => by
    change e.hom.hom.hom.app U (h.hom.hom.app U s.1) = _
    rw [h.kernel_comm U s]
    exact e.kernel_comm U _

/-! ### Isomorphism classes -/

/-- **Isomorphism classes of solutions of (08UF) are the isomorphism classes of square-zero
extensions of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras containing a solution.** -/
def classesEquivCompClasses :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      {q : CompatibleFirstOrderThickening.IsomorphismClasses S.compProblem //
        ∃ P : S.CompatibleFirstOrderThickening,
          Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _)
            (S.toCompSolution P) = q} :=
  Equiv.ofBijective
    (Quotient.lift (fun P => ⟨Quotient.mk _ (S.toCompSolution P), P, rfl⟩)
      (fun _ _ h => Subtype.ext (Quotient.sound ((S.isomorphic_iff_compSolution _ _).1 h))))
    ⟨fun p₁ p₂ h => by
      induction p₁ using Quotient.ind
      induction p₂ using Quotient.ind
      exact Quotient.sound ((S.isomorphic_iff_compSolution _ _).2
        (Quotient.exact (congrArg Subtype.val h))),
    fun ⟨q, P, hP⟩ => ⟨Quotient.mk _ P, Subtype.ext hP⟩⟩

/-- The class of a solution goes to the class of its underlying extension. -/
theorem classesEquivCompClasses_mk (P : S.CompatibleFirstOrderThickening) :
    (S.classesEquivCompClasses (Quotient.mk _ P)).1 =
      Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _) (S.toCompSolution P) :=
  rfl

/-- **"Of course this is the same thing as saying `𝒪'` is a solution of (08UF)."** The class of a
square-zero extension `𝒪'` of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras contains a solution if and only if
there is a morphism `(Sh(𝒞), 𝒪') ⟶ (Sh(ℬ), 𝒪_{ℬ'})` over `(Sh(ℬ), 𝒪_{ℬ'})` compatible with `f`
and `c`. -/
theorem exists_mk_toCompSolution_iff (Q : S.compProblem.CompatibleFirstOrderThickening) :
    (∃ P : S.CompatibleFirstOrderThickening,
        Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _) (S.toCompSolution P) =
          Quotient.mk _ Q) ↔
      Nonempty (S.liftData Q).CompatibleHom := by
  constructor
  · rintro ⟨P, hP⟩
    obtain ⟨e⟩ := Quotient.exact hP
    exact ⟨S.compatibleHomOfIso e (S.toCompatibleHom P)⟩
  · rintro ⟨h⟩
    exact ⟨S.ofCompatibleHom Q h, Quotient.sound ⟨S.toCompSolutionOfCompatibleHomIso Q h⟩⟩

/-! ### The fibre of Stacks 0GQ9 -/

section Fibre

attribute [local instance 10000] HasDerivedCategory.standard

open Deformation.ToposThickening.LiftingMorphismDerived (pullbackExtClass restrictExtClass
  nonempty_compatibleHom_iff)

/-- **The fibre of `Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)` over the image of
`ξ`**: the classes `ζ` whose restriction along the canonical map
`Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}} ⟶ NL_{𝒪/𝒪_{ℬ'}}` is the image of `ξ` under `Lf^*` and `c`. -/
abbrev derivedExtFibre : Type _ :=
  {ζ : Stacks.SheafOfModules.naiveCotangentExt.{u, u, u, u} X.J
      ((inverseImageCommRingFunctor S.compBase.toToposHom).obj S.baseExtension) X.O
      S.compBase.fSharpInverseImage S.G 1 //
    restrictExtClass S.baseThickening S.f ζ =
      pullbackExtClass S.f S.prescribedPullbackMap S.baseThickeningClass}

/-- **A class of square-zero extensions of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras is a class of solutions of
(08UF) exactly when its class in `Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢)` lies over the image of `ξ`**: the
identification of solutions with extensions carrying a compatible lift, followed by
**Stacks 0GQ7** for `(Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ'), 𝒪_{ℬ'})` and `c`. -/
theorem exists_mk_toCompSolution_iff_restrictExtClass_eq
    (Q : S.compProblem.CompatibleFirstOrderThickening) :
    (∃ P : S.CompatibleFirstOrderThickening,
        Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _) (S.toCompSolution P) =
          Quotient.mk _ Q) ↔
      restrictExtClass S.baseThickening S.f
          (squareZeroExtensionClassesEquiv S.compBase S.G (Quotient.mk _ Q)) =
        pullbackExtClass S.f S.prescribedPullbackMap S.baseThickeningClass :=
  (S.exists_mk_toCompSolution_iff Q).trans
    ((nonempty_compatibleHom_iff S.f S.baseThickeningSolution Q S.prescribedPullbackMap).trans
      eq_comm)

/-- **Stacks Project, Tag 0GQ9.** Let `t : (Sh(ℬ), 𝒪_ℬ) ⟶ (Sh(ℬ'), 𝒪_{ℬ'})`, `𝒥 = Ker(t^♯)`,
`f : (Sh(𝒞), 𝒪) ⟶ (Sh(ℬ), 𝒪_ℬ)`, `𝒢` and `c : f⁻¹𝒥 ⟶ 𝒢` be as in (08UF) — the problem `S` —
and let `ξ ∈ Ext¹_{𝒪_ℬ}(NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒥)` be the element corresponding to the extension
`𝒪_{ℬ'}` of `𝒪_ℬ` by `𝒥` via **Stacks 0GQ5** (`baseThickeningClass`). The set of isomorphism
classes of solutions is canonically bijective to the fibre of
`Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢) ⟶ Ext¹_𝒪(Lf^*NL_{𝒪_ℬ/𝒪_{ℬ'}}, 𝒢)` over the image of `ξ`
(`derivedExtFibre`), `Lf^*` being the derived pullback of **Stacks 06YY**.

The bijection is the one of the source's proof: the class of a solution `𝒪'` goes to the
element of `Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢)` which **Stacks 0GQ5** for `t ∘ f` attaches to `𝒪'` as an
extension of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras (`solutionClassesEquivDerivedExtFibre_mk`); that the
classes so obtained are exactly the fibre is **Stacks 0GQ7**. -/
@[stacks 0GQ9]
def solutionClassesEquivDerivedExtFibre :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃ S.derivedExtFibre :=
  S.classesEquivCompClasses.trans
    ((squareZeroExtensionClassesEquiv S.compBase S.G).subtypeEquiv fun q => by
      induction q using Quotient.ind with
      | _ Q => exact S.exists_mk_toCompSolution_iff_restrictExtClass_eq Q)

/-- **The bijection of Stacks 0GQ9 is the canonical one**: the class of a solution `𝒪'` goes to
the element of `Ext¹_𝒪(NL_{𝒪/𝒪_{ℬ'}}, 𝒢)` that **Stacks 0GQ5** for `t ∘ f` attaches to `𝒪'`,
read as a square-zero extension of `(t ∘ f)⁻¹𝒪_{ℬ'}`-algebras. -/
@[stacks 0GQ9]
theorem solutionClassesEquivDerivedExtFibre_mk (P : S.CompatibleFirstOrderThickening) :
    (S.solutionClassesEquivDerivedExtFibre (Quotient.mk _ P)).1 =
      squareZeroExtensionClassesEquiv S.compBase S.G
        (Quotient.mk (CompatibleFirstOrderThickening.isomorphicSetoid _) (S.toCompSolution P)) :=
  rfl

end Fibre

end Deformation.ToposThickening.RingedToposExtensionProblem

end
