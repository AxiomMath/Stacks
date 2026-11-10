module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorDualSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.LocalHom
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentTensor
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DivisorClassFaithful
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.HullCoherentReflexive
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.NormalCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneTensorMonoid
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SheafHomReflexive
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DepthCoherence.ReflexiveExtension
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Adjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `(ℋom(ℱ, 𝒪_X) ⊗ 𝒢)^∨∨ ≅ ℋom(ℱ, 𝒢)` for coherent reflexive modules

Let `X` be an integral locally Noetherian normal scheme and let `ℱ` and `𝒢` be coherent
reflexive `𝒪_X`-modules. The canonical map

`(ℋom_{𝒪_X}(ℱ, 𝒪_X) ⊗_{𝒪_X} 𝒢)^∨∨ ⟶ ℋom_{𝒪_X}(ℱ, 𝒢)`

is an **isomorphism**. This is the first assertion of
[Stacks, Tag 0EBL](https://stacks.math.columbia.edu/tag/0EBL).

## Main definitions

* `tensorDualToSheafHomModule`: the canonical map `𝒢 ⊗ ℱ^∨ ⟶ ℋom(ℱ, 𝒢)`,
  `g ⊗ λ ↦ (v ↦ λ(v) • g)`.
* `dualTensorToSheafHomModule`: the canonical map `ℱ^∨ ⊗ 𝒢 ⟶ ℋom(ℱ, 𝒢)`, the braiding of the
  tensor product followed by `tensorDualToSheafHomModule`.
* `dualTensorHullToSheafHom`: the map `(ℱ^∨ ⊗ 𝒢)^∨∨ ⟶ ℋom(ℱ, 𝒢)` of [Stacks, Tag 0EBL], the
  unique extension of the previous map along `ℱ^∨ ⊗ 𝒢 ⟶ (ℱ^∨ ⊗ 𝒢)^∨∨`
  (`toDoubleDual_comp_dualTensorHullToSheafHom`).
* `stalkDualTensorEquiv`: the linear equivalence `𝒢_x ⊗ (ℱ^∨)_x ≃ Hom(ℱ_x, 𝒢_x)` at a point
  where `ℱ_x` is finite projective.

## Main results

* `bijective_stalkMapOfHom_tensorDualToSheafHomModule`: at a point where `ℱ_x` is finite
  projective the canonical map `𝒢 ⊗ ℱ^∨ ⟶ ℋom(ℱ, 𝒢)` is bijective on stalks.
* `isIso_dualTensorHullToSheafHom`: the first assertion of [Stacks, Tag 0EBL].

## References

* [Stacks Project, Tag 0EBL](https://stacks.math.columbia.edu/tag/0EBL)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf unitModule stalkMapOfHom dualStalkEquiv
  stalkMapOfHom_germ dualStalkEquiv_germ dualPairing)
open Stacks.SheafOfModules.SheafHomStalk (internalSheafHom
  sheafHomStalkLinearEquivOfFinitePresentation)
open Stacks.AlgebraicGeometry.ReflexiveEquivalence (bijective_stalkMapOfHom_toDoubleDual
  isCoherent_doubleDual isCoherent_dualSheaf isIso_of_restrict_of_isIso_unit
  isIso_restrict_of_isIso_stalkMapOfHom_on_range openImmersionStalkRingEquiv
  restrictStalkSemilinearEquiv)
open Stacks.SheafOfModules.TensorStalkRingedSpace (tensorStalkIso tensorStalkIso_germ
  toTensorSheafSection stalkModule)

universe u

namespace AlgebraicGeometry.CoherentReflexive

attribute [local instance] Stacks.SheafOfModules.commRingStructureSheafObj
  Stacks.SheafOfModules.moduleStructureSheafObj

variable {X : Scheme.{u}}

/-- The germ at `x` of a local section of an `𝒪_X`-module, as an element of the stalk
`M.presheaf.stalk x`. -/
noncomputable abbrev germModule (M : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(M, U)) : M.presheaf.stalk x :=
  Stacks.SheafOfModules.SheafHomStalk.germAt M U x hx s

/-- The scalar action on a stalk of [Stacks, Tag 01CB] is
`AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf`. -/
theorem stalkModule_eq_moduleStalkPresheaf (M : X.Modules) (x : X) :
    stalkModule X.toRingedSpace M.val x = Scheme.Modules.moduleStalkPresheaf M x :=
  Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace M.val x

/-- **The stalk of a tensor product is the tensor product of the stalks** ([Stacks, Tag 01CB]),
for any module structures `iM`, `iN`, `iT` on the stalks equal to those of that tag: there is a
linear equivalence sending the germ of a local pure tensor `m ⊗ n` to `germ m ⊗ germ n`. -/
theorem exists_tensorModulesStalkIso (M N : X.Modules) (x : X)
    (iM : Module (X.presheaf.stalk x) (M.presheaf.stalk x))
    (iN : Module (X.presheaf.stalk x) (N.presheaf.stalk x))
    (iT : Module (X.presheaf.stalk x) ((tensorModules M N).presheaf.stalk x))
    (hM : stalkModule X.toRingedSpace M.val x = iM)
    (hN : stalkModule X.toRingedSpace N.val x = iN)
    (hT : stalkModule X.toRingedSpace (tensorModules M N).val x = iT) :
    letI := iM
    letI := iN
    letI := iT
    ∃ e : (tensorModules M N).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
        (M.presheaf.stalk x ⊗[X.presheaf.stalk x] N.presheaf.stalk x),
      ∀ (U : X.Opens) (hxU : x ∈ U) (m : Γ(M, U)) (n : Γ(N, U)),
        e (germModule (tensorModules M N) x U hxU
            (toTensorSheafSection X.toRingedSpace M N (op U)
              (m ⊗ₜ[X.presheaf.obj (op U)] n)))
          = (germModule M x U hxU m) ⊗ₜ[X.presheaf.stalk x] (germModule N x U hxU n) := by
  subst hM hN hT
  exact ⟨tensorStalkIso X.toRingedSpace x M N,
    fun U hxU m n => tensorStalkIso_germ X.toRingedSpace x M N U hxU m n⟩

/-- The internal hom `ℋom_{𝒪_X}(ℰ, ℱ)` as an `𝒪_X`-module. -/
@[ega "0 4.1.5" "partial"]
noncomputable abbrev sheafHomModule (E F : X.Modules) : X.Modules :=
  (internalSheafHom X.toTopCat X.sheaf E F).obj

/-- **The canonical map `𝒢 ⊗ ℰ^∨ ⟶ ℋom_{𝒪_X}(ℰ, 𝒢)`** on a scheme: it sends a local pure
tensor `g ⊗ λ` to the rank one operator `v ↦ λ(v) • g`. -/
noncomputable abbrev tensorDualToSheafHomModule (E F : X.Modules) :
    tensorModules F (dualSheaf E) ⟶ sheafHomModule E F :=
  Stacks.SheafOfModules.tensorDualToSheafHom X.presheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property E F

/-- On stalks, `tensorDualToSheafHomModule` sends the germ of a local pure tensor `f ⊗ λ` to the
germ of the rank one operator `v ↦ λ(v) • f`. -/
theorem stalkMapOfHom_tensorDualToSheafHomModule_germ (E F : X.Modules) (x : X) (U : X.Opens)
    (hxU : x ∈ U)
    (f : Γ(F, U)) (lam : Γ(dualSheaf E, U)) :
    stalkMapOfHom (tensorDualToSheafHomModule E F) x
        (germModule (tensorModules F (dualSheaf E)) x U hxU
          (toTensorSheafSection X.toRingedSpace F (dualSheaf E) (op U)
            (f ⊗ₜ[X.presheaf.obj (op U)] lam)))
      = germModule (sheafHomModule E F) x U hxU
          (Stacks.SheafOfModules.rankOneHomSection X.presheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property f lam) :=
  (stalkMapOfHom_germ (tensorDualToSheafHomModule E F) x U hxU _).trans <|
    congrArg (TopCat.Presheaf.germ (C := Ab.{u}) (sheafHomModule E F).val.presheaf U x hxU)
      (Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection X.presheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property E F (op U) f lam)

/-- The stalk comparison `ℋom(ℰ, ℱ)_x ≃ Hom(ℰ_x, ℱ_x)` of [Stacks, Tag 01CP], for `ℰ` of finite
presentation. -/
noncomputable abbrev sheafHomModuleStalkEquiv (E F : X.Modules) [E.IsFinitePresentation] (x : X) :
    (sheafHomModule E F).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (E.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) :=
  (sheafHomStalkLinearEquivOfFinitePresentation
    (internalSheafHom X.toTopCat X.sheaf E F) x).equiv

/-- The value `λ(m) ∈ Γ(X, U)` of a local functional `λ` on `ℰ` over `U` at a section `m` of `ℰ`
over `U`. -/
noncomputable abbrev dualEvalModule (E : X.Modules) {U : X.Opens} (lam : Γ(dualSheaf E, U))
    (m : Γ(E, U)) : Γ(X, U) :=
  dualPairing E lam (Over.mk (𝟙 U)) m

/-- **The rank one operator, read off on sections over the open it is defined on**: it sends a
section `m` of `ℰ` over `U` to `λ(m) • f`. -/
theorem sectionsEquiv_rankOneHomSection_app (E F : X.Modules) (U : X.Opens)
    (f : Γ(F, U)) (lam : Γ(dualSheaf E, U)) (m : Γ(E, U)) :
    (((internalSheafHom X.toTopCat X.sheaf E F).sectionsEquiv U
        (Stacks.SheafOfModules.rankOneHomSection X.presheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property f lam)).val.app
          (op (Over.mk (𝟙 U)))) m
      = dualEvalModule E lam m • f := by
  refine (Stacks.SheafOfModules.rankOneHomSection_app X.presheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property f lam (op (Over.mk (𝟙 U))) m).trans ?_
  congr 1
  exact Stacks.SheafOfModules.resSection_self (L := F) f

/-- **The stalk comparison of [Stacks, Tag 01CP] on the germ of a rank one operator**: it sends
the germ of `v ↦ λ(v) • f` and the germ of a section `m` of `ℰ` over the same open to
`germ λ(m) • germ f`. -/
theorem sheafHomModuleStalkEquiv_germ_rankOneSection (E F : X.Modules) [E.IsFinitePresentation]
    (x : X)
    (U : X.Opens) (hxU : x ∈ U) (f : Γ(F, U)) (lam : Γ(dualSheaf E, U)) (m : Γ(E, U)) :
    sheafHomModuleStalkEquiv E F x
        (germModule (sheafHomModule E F) x U hxU
          (Stacks.SheafOfModules.rankOneHomSection X.presheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property f lam))
        (germModule E x U hxU m)
      = X.presheaf.germ U x hxU (dualEvalModule E lam m) • germModule F x U hxU f :=
  ((sheafHomStalkLinearEquivOfFinitePresentation
    (internalSheafHom X.toTopCat X.sheaf E F) x).germ_apply U hxU _ m).trans <|
    (congrArg (TopCat.Presheaf.germ (C := Ab.{u}) F.val.presheaf U x hxU)
      (sectionsEquiv_rankOneHomSection_app E F U f lam m)).trans <|
    PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hxU (dualEvalModule E lam m) f

/-- The rank one operator `v ↦ λ(v) • f` as a section of `ℋom(ℰ, ℱ)` over `U`, for sections `f`
of `ℱ` and `λ` of `ℰ^∨` over `U`. -/
noncomputable abbrev rankOneSectionModule {E F : X.Modules} {U : X.Opens} (f : Γ(F, U))
    (lam : Γ(dualSheaf E, U)) : Γ(sheafHomModule E F, U) :=
  Stacks.SheafOfModules.rankOneHomSection X.presheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property f lam

/-- The stalk comparison of [Stacks, Tag 01CP] sends the germ of `v ↦ λ(v) • f` and the germ of a
section `m` of `ℰ` over the same open to `λ_x(m_x) • f_x`, where the germ `λ_x` is read as a
functional on `ℰ_x` through the dual stalk comparison. -/
theorem sheafHomModuleStalkEquiv_germ_germ (E F : X.Modules) [E.IsFinitePresentation] (x : X)
    (U : X.Opens) (hxU : x ∈ U) (f : Γ(F, U)) (lam : Γ(dualSheaf E, U)) (e : Γ(E, U)) :
    sheafHomModuleStalkEquiv E F x
        (germModule (sheafHomModule E F) x U hxU (rankOneSectionModule f lam))
        (germModule E x U hxU e)
      = dualStalkEquiv E x (germModule (dualSheaf E) x U hxU lam) (germModule E x U hxU e)
          • germModule F x U hxU f :=
  (sheafHomModuleStalkEquiv_germ_rankOneSection E F x U hxU f lam e).trans
    (congrArg (fun r : X.presheaf.stalk x => r • germModule F x U hxU f)
      (dualStalkEquiv_germ E x U hxU lam e).symm)

/-- The germ at `x` of the restriction of a section to `W ≤ U` is the germ of the section. -/
theorem germModule_res (M : X.Modules) (x : X) {U W : X.Opens} (h : W ≤ U) (hxU : x ∈ U)
    (hxW : x ∈ W) (s : Γ(M, U)) :
    germModule M x W hxW (M.presheaf.map (homOfLE h).op s) = germModule M x U hxU s :=
  TopCat.Presheaf.germ_res_apply (C := Ab.{u}) M.val.presheaf (homOfLE h) x hxW s

/-- The restriction of the rank one operator `v ↦ λ(v) • f` to `W ≤ U` is the rank one operator
of the restrictions of `f` and `λ`. -/
theorem rankOneSectionModule_res (E F : X.Modules) {U W : X.Opens} (h : W ≤ U) (f : Γ(F, U))
    (lam : Γ(dualSheaf E, U)) :
    (sheafHomModule E F).presheaf.map (homOfLE h).op (rankOneSectionModule f lam)
      = rankOneSectionModule (F.presheaf.map (homOfLE h).op f)
          ((dualSheaf E).presheaf.map (homOfLE h).op lam) :=
  (Stacks.SheafOfModules.rankOneHomSection_naturality X.presheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property (homOfLE h).op f lam).symm

/-- **The stalk comparison on the germ of a rank one operator, evaluated at an arbitrary element
of the stalk of `ℰ`**: the germ of `v ↦ λ(v) • f` sends `v ∈ ℰ_x` to `λ_x(v) • f_x`. -/
theorem sheafHomModuleStalkEquiv_germ_apply (E F : X.Modules) [E.IsFinitePresentation] (x : X)
    (U : X.Opens) (hxU : x ∈ U) (f : Γ(F, U)) (lam : Γ(dualSheaf E, U))
    (v : E.presheaf.stalk x) :
    sheafHomModuleStalkEquiv E F x
        (germModule (sheafHomModule E F) x U hxU (rankOneSectionModule f lam)) v
      = dualStalkEquiv E x (germModule (dualSheaf E) x U hxU lam) v • germModule F x U hxU f := by
  obtain ⟨V, hxV, e, he⟩ := TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) E.val.presheaf v
  have hv : v = germModule E x V hxV e := he.symm
  subst hv
  have hxW : x ∈ U ⊓ V := Stacks.SheafOfModules.SheafHomStalk.mem_inf hxU hxV
  have hUW : (U ⊓ V : X.Opens) ≤ U := inf_le_left
  have hVW : (U ⊓ V : X.Opens) ≤ V := inf_le_right
  rw [← germModule_res E x hVW hxV hxW e, ← germModule_res F x hUW hxU hxW f,
    ← germModule_res (dualSheaf E) x hUW hxU hxW lam,
    ← germModule_res (sheafHomModule E F) x hUW hxU hxW (rankOneSectionModule f lam),
    rankOneSectionModule_res E F hUW f lam]
  exact sheafHomModuleStalkEquiv_germ_germ E F x (U ⊓ V) hxW _ _ _

/-! ### The algebraic comparison map -/

/-- **The algebraic rank-one isomorphism at a stalk**: for `ℱ_x` finite projective the map
`𝒢_x ⊗ (ℱ^∨)_x → Hom(ℱ_x, 𝒢_x)`, `m ⊗ n ↦ (v ↦ n(v) • m)`, is a linear equivalence. -/
noncomputable def stalkDualTensorEquiv (E F : X.Modules) [E.IsFinitePresentation] (x : X)
    [Module.Finite (X.presheaf.stalk x) (E.presheaf.stalk x)]
    [Module.Projective (X.presheaf.stalk x) (E.presheaf.stalk x)] :
    (F.presheaf.stalk x ⊗[X.presheaf.stalk x] (dualSheaf E).presheaf.stalk x)
      ≃ₗ[X.presheaf.stalk x]
      (E.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) :=
  (TensorProduct.comm (X.presheaf.stalk x) (F.presheaf.stalk x)
      ((dualSheaf E).presheaf.stalk x)).trans
    ((TensorProduct.congr (dualStalkEquiv E x)
        (LinearEquiv.refl (X.presheaf.stalk x) (F.presheaf.stalk x))).trans
      (dualTensorHomEquiv (X.presheaf.stalk x) (E.presheaf.stalk x) (F.presheaf.stalk x)))

/-- `stalkDualTensorEquiv` sends a pure tensor `m ⊗ n` to the rank one operator
`v ↦ n(v) • m`, where `n` is read as a functional on `ℰ_x` through the dual stalk comparison of
[Stacks, Tag 01CP]. -/
theorem stalkDualTensorEquiv_tmul (E F : X.Modules) [E.IsFinitePresentation] (x : X)
    [Module.Finite (X.presheaf.stalk x) (E.presheaf.stalk x)]
    [Module.Projective (X.presheaf.stalk x) (E.presheaf.stalk x)]
    (m : F.presheaf.stalk x) (n : (dualSheaf E).presheaf.stalk x) (v : E.presheaf.stalk x) :
    stalkDualTensorEquiv E F x (m ⊗ₜ[X.presheaf.stalk x] n) v = dualStalkEquiv E x n v • m := by
  change dualTensorHom (X.presheaf.stalk x) (E.presheaf.stalk x) (F.presheaf.stalk x)
      (dualStalkEquiv E x n ⊗ₜ[X.presheaf.stalk x] m) v = _
  rw [dualTensorHom_apply]

/-! ### Bijectivity of the stalk map -/

/-- **The canonical map `𝒢 ⊗ ℰ^∨ ⟶ ℋom(ℰ, 𝒢)` is bijective on the stalk at a point where
`ℰ_x` is finite projective.** -/
@[ega "0 5.4.2" "partial"]
theorem bijective_stalkMapOfHom_tensorDualToSheafHomModule (E F : X.Modules)
    [E.IsFinitePresentation] (x : X)
    [Module.Finite (X.presheaf.stalk x) (E.presheaf.stalk x)]
    [Module.Projective (X.presheaf.stalk x) (E.presheaf.stalk x)] :
    Function.Bijective (stalkMapOfHom (tensorDualToSheafHomModule E F) x) := by
  obtain ⟨e1, he1⟩ := exists_tensorModulesStalkIso F (dualSheaf E) x _ _ _
    (stalkModule_eq_moduleStalkPresheaf F x)
    (stalkModule_eq_moduleStalkPresheaf (dualSheaf E) x)
    (stalkModule_eq_moduleStalkPresheaf (tensorModules F (dualSheaf E)) x)
  have hcomp : ∀ w, sheafHomModuleStalkEquiv E F x
        (stalkMapOfHom (tensorDualToSheafHomModule E F) x (e1.symm w))
      = stalkDualTensorEquiv E F x w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul m n =>
        obtain ⟨U1, hx1, f0, hf0⟩ :=
          TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) F.val.presheaf m
        obtain ⟨U2, hx2, l0, hl0⟩ :=
          TopCat.Presheaf.exists_germ_eq (C := Ab.{u}) (dualSheaf E).val.presheaf n
        have hxW : x ∈ U1 ⊓ U2 := Stacks.SheafOfModules.SheafHomStalk.mem_inf hx1 hx2
        have hres : ∀ (M : X.Modules) {U : X.Opens} (h : U1 ⊓ U2 ≤ U) (hxU : x ∈ U) (s : Γ(M, U))
            (t : M.presheaf.stalk x), germModule M x U hxU s = t →
            t = germModule M x (U1 ⊓ U2) hxW (M.presheaf.map (homOfLE h).op s) :=
          fun M U h hxU s t hs => ((germModule_res M x h hxU hxW s).trans hs).symm
        obtain rfl := hres F inf_le_left hx1 f0 m hf0
        obtain rfl := hres (dualSheaf E) inf_le_right hx2 l0 n hl0
        rw [e1.symm_apply_eq.mpr (he1 (U1 ⊓ U2) hxW _ _).symm,
          stalkMapOfHom_tensorDualToSheafHomModule_germ]
        exact LinearMap.ext fun v =>
          (sheafHomModuleStalkEquiv_germ_apply E F x (U1 ⊓ U2) hxW _ _ v).trans
            (stalkDualTensorEquiv_tmul E F x _ _ v).symm
    | add w1 w2 ih1 ih2 => simp only [map_add, ih1, ih2]
  have hfun : (sheafHomModuleStalkEquiv E F x) ∘ (stalkMapOfHom (tensorDualToSheafHomModule E F) x)
      = (stalkDualTensorEquiv E F x) ∘ e1 := by
    funext z
    change sheafHomModuleStalkEquiv E F x (stalkMapOfHom (tensorDualToSheafHomModule E F) x z)
      = stalkDualTensorEquiv E F x (e1 z)
    rw [← hcomp (e1 z), LinearEquiv.symm_apply_apply]
  exact (Function.Bijective.of_comp_iff' (sheafHomModuleStalkEquiv E F x).bijective _).mp
    (hfun ▸ (stalkDualTensorEquiv E F x).bijective.comp e1.bijective)

/-! ### The global statement -/

/-- The canonical map `ℱ^∨ ⊗ 𝒢 ⟶ ℋom(ℱ, 𝒢)`: the braiding followed by
`tensorDualToSheafHomModule`. -/
noncomputable abbrev dualTensorToSheafHomModule (E F : X.Modules) :
    tensorModules (dualSheaf E) F ⟶ sheafHomModule E F :=
  (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
    (dualSheaf E) F).hom ≫ tensorDualToSheafHomModule E F

section Global

open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive toDoubleDual reflexiveHull
  reflexiveHullHomEquiv isFinitePresentation_dualSheaf)

variable [IsIntegral X] [IsLocallyNoetherian X]

omit [IsIntegral X] in
/-- The tensor product `ℰ^∨ ⊗ ℱ` of coherent modules on a locally Noetherian scheme is
coherent. -/
theorem isCoherent_tensorModules_dual (E F : X.Modules) [E.IsCoherent] [F.IsCoherent] :
    (tensorModules (dualSheaf E) F).IsCoherent :=
  @AlgebraicGeometry.SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace (dualSheaf E) F
    (isCoherent_dualSheaf E) ‹_›

/-- **The canonical map `(ℱ^∨ ⊗ 𝒢)^∨∨ ⟶ ℋom(ℱ, 𝒢)`** of [Stacks, Tag 0EBL]. -/
noncomputable def dualTensorHullToSheafHom (E F : X.Modules) [E.IsCoherent] [F.IsCoherent]
    (hF : IsReflexive F) : reflexiveHull (tensorModules (dualSheaf E) F) ⟶ sheafHomModule E F :=
  have : (tensorModules (dualSheaf E) F).IsCoherent := isCoherent_tensorModules_dual E F
  have : IsIso (toDoubleDual (dualSheaf (dualSheaf (tensorModules (dualSheaf E) F)))) :=
    isReflexive_reflexiveHull X (tensorModules (dualSheaf E) F)
  have : IsIso (toDoubleDual (sheafHomModule E F)) := sheafHom_isReflexive X E F hF
  (reflexiveHullHomEquiv (tensorModules (dualSheaf E) F) (sheafHomModule E F)).symm
    (dualTensorToSheafHomModule E F)

/-- **The map of [Stacks, Tag 0EBL] is pinned down**: precomposing it with the canonical map
`ℱ^∨ ⊗ 𝒢 ⟶ (ℱ^∨ ⊗ 𝒢)^∨∨` gives back the canonical map `ℱ^∨ ⊗ 𝒢 ⟶ ℋom(ℱ, 𝒢)`. -/
theorem toDoubleDual_comp_dualTensorHullToSheafHom (E F : X.Modules) [E.IsCoherent]
    [F.IsCoherent] (hF : IsReflexive F) :
    toDoubleDual (tensorModules (dualSheaf E) F) ≫ dualTensorHullToSheafHom E F hF
      = dualTensorToSheafHomModule E F :=
  have : (tensorModules (dualSheaf E) F).IsCoherent := isCoherent_tensorModules_dual E F
  have : IsIso (toDoubleDual (dualSheaf (dualSheaf (tensorModules (dualSheaf E) F)))) :=
    isReflexive_reflexiveHull X (tensorModules (dualSheaf E) F)
  have : IsIso (toDoubleDual (sheafHomModule E F)) := sheafHom_isReflexive X E F hF
  (reflexiveHullHomEquiv (tensorModules (dualSheaf E) F) (sheafHomModule E F)).apply_symm_apply
    (dualTensorToSheafHomModule E F)

omit [IsIntegral X] in
/-- If the restriction of a quasi-coherent module `M` to an open `U` is finite locally free, the
stalk of `M` at every point of `U` is free. -/
theorem free_stalk_of_isFiniteLocallyFree_restrict (U : X.Opens) (M : X.Modules)
    [M.IsQuasicoherent]
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (M.restrict U.ι))
    (y : U.toScheme) :
    Module.Free (X.presheaf.stalk (U.ι y)) (M.presheaf.stalk (U.ι y)) := by
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : (M.restrict U.ι).IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor U.ι M
  have hfree := ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae
    (M.restrict U.ι)).out 4 2).mp h
  have _h₁ : RingHomInvPair
      (openImmersionStalkRingEquiv U.ι y :
        U.toScheme.presheaf.stalk y →+* X.presheaf.stalk (U.ι y))
      ((openImmersionStalkRingEquiv U.ι y).symm :
        X.presheaf.stalk (U.ι y) →+* U.toScheme.presheaf.stalk y) :=
    RingHomInvPair.of_ringEquiv _
  have _h₂ : RingHomInvPair
      ((openImmersionStalkRingEquiv U.ι y).symm :
        X.presheaf.stalk (U.ι y) →+* U.toScheme.presheaf.stalk y)
      (openImmersionStalkRingEquiv U.ι y :
        U.toScheme.presheaf.stalk y →+* X.presheaf.stalk (U.ι y)) :=
    RingHomInvPair.of_ringEquiv_symm _
  have _h₃ := hfree.2 y
  exact Module.Free.of_equiv (restrictStalkSemilinearEquiv U.ι M y)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The stalk of `ℱ^∨ ⊗ 𝒢` at a point where both stalks are finite free is reflexive. -/
theorem isReflexive_stalk_tensorModules_dual (E F : X.Modules) [E.IsCoherent] [F.IsCoherent] (y : X)
    (hE : Module.Free (X.presheaf.stalk y) (E.presheaf.stalk y))
    (hF : Module.Free (X.presheaf.stalk y) (F.presheaf.stalk y)) :
    Module.IsReflexive (X.presheaf.stalk y) ((tensorModules (dualSheaf E) F).presheaf.stalk y) := by
  have : E.IsFinitePresentation := isFinitePresentation_of_isCoherent E
  have : Module.Finite (X.presheaf.stalk y) (E.presheaf.stalk y) :=
    Scheme.Modules.finite_stalk_of_isCoherent E y
  have : Module.Finite (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    Scheme.Modules.finite_stalk_of_isCoherent F y
  have : Module.Free (X.presheaf.stalk y) ((dualSheaf E).presheaf.stalk y) :=
    Module.Free.of_equiv (dualStalkEquiv E y).symm
  have : Module.Finite (X.presheaf.stalk y) ((dualSheaf E).presheaf.stalk y) :=
    Module.Finite.equiv (dualStalkEquiv E y).symm
  obtain ⟨e, -⟩ := exists_tensorModulesStalkIso (dualSheaf E) F y _ _ _
    (stalkModule_eq_moduleStalkPresheaf (dualSheaf E) y)
    (stalkModule_eq_moduleStalkPresheaf F y)
    (stalkModule_eq_moduleStalkPresheaf (tensorModules (dualSheaf E) F) y)
  exact Module.equiv e.symm

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The internal hom of two coherent modules on a locally Noetherian scheme is coherent
([Stacks, Tag 01CQ]). -/
theorem isCoherent_sheafHomModule (E F : X.Modules) [E.IsCoherent] [F.IsCoherent] :
    (sheafHomModule E F).IsCoherent :=
  have : E.IsFinitePresentation := isFinitePresentation_of_isCoherent E
  @Stacks.SheafOfModules.InternalHom.isCoherent_sheafInternalHom'.{u} X inferInstance X.sheaf E F
    ‹_› ‹_›

variable [IsNormal X]

/-- Let `X` be an integral locally Noetherian normal scheme and let `ℱ` and `𝒢` be coherent
reflexive `𝒪_X`-modules. Then the canonical map

`(ℋom_{𝒪_X}(ℱ, 𝒪_X) ⊗_{𝒪_X} 𝒢)^∨∨ ⟶ ℋom_{𝒪_X}(ℱ, 𝒢)`

is an isomorphism. -/
@[stacks 0EBL "the comparison (ℋom(ℱ, 𝒪_X) ⊗ 𝒢)^∨∨ → ℋom(ℱ, 𝒢) is an isomorphism"]
theorem isIso_dualTensorHullToSheafHom (E F : X.Modules) [E.IsCoherent] [F.IsCoherent]
    (hE : IsReflexive E) (hF : IsReflexive F) :
    IsIso (dualTensorHullToSheafHom E F hF) := by
  have hAcoh : (tensorModules (dualSheaf E) F).IsCoherent := isCoherent_tensorModules_dual E F
  have : E.IsFinitePresentation := isFinitePresentation_of_isCoherent E
  have : F.IsFinitePresentation := isFinitePresentation_of_isCoherent F
  have : (tensorModules (dualSheaf E) F).IsFinitePresentation :=
    isFinitePresentation_of_isCoherent _
  have : (dualSheaf (tensorModules (dualSheaf E) F)).IsFinitePresentation :=
    isFinitePresentation_dualSheaf _
  have : (sheafHomModule E F).IsCoherent := isCoherent_sheafHomModule E F
  have : E.IsQuasicoherent := isQuasicoherent_of_isCoherent E
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : (reflexiveHull (tensorModules (dualSheaf E) F)).IsCoherent :=
    isCoherent_doubleDual _
  obtain ⟨U1, hc1, hlf1, -⟩ :=
    ((isReflexive_isTorsionFree_propertyS2_extension_tfae X E).out 1 3).mp hE
  obtain ⟨U2, hc2, hlf2, -⟩ :=
    ((isReflexive_isTorsionFree_propertyS2_extension_tfae X F).out 1 3).mp hF
  have hc := two_le_codimension_compl_inf U1 U2 hc1 hc2
  have hdepth := two_le_depth_stalk_of_notMem_of_two_le_codimension (U1 ⊓ U2) hc
  have hres : IsIso ((Scheme.Modules.restrictFunctor (U1 ⊓ U2).ι).map
      (dualTensorHullToSheafHom E F hF)) := by
    refine isIso_restrict_of_isIso_stalkMapOfHom_on_range (U1 ⊓ U2).ι _ fun z hz => ?_
    obtain ⟨u, rfl⟩ := Scheme.Hom.mem_opensRange.mp hz
    have hfE : Module.Free (X.presheaf.stalk ((U1 ⊓ U2).ι u))
        (E.presheaf.stalk ((U1 ⊓ U2).ι u)) :=
      free_stalk_of_isFiniteLocallyFree_restrict U1 E hlf1 ⟨u.1, u.2.1⟩
    have hfF : Module.Free (X.presheaf.stalk ((U1 ⊓ U2).ι u))
        (F.presheaf.stalk ((U1 ⊓ U2).ι u)) :=
      free_stalk_of_isFiniteLocallyFree_restrict U2 F hlf2 ⟨u.1, u.2.2⟩
    have : Module.Finite (X.presheaf.stalk ((U1 ⊓ U2).ι u))
        (E.presheaf.stalk ((U1 ⊓ U2).ι u)) :=
      Scheme.Modules.finite_stalk_of_isCoherent E _
    have hth := bijective_stalkMapOfHom_tensorDualToSheafHomModule E F ((U1 ⊓ U2).ι u)
    have hbr := Stacks.AlgebraicGeometry.ReflexiveModules.bijective_stalkMapOfHom
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
        (dualSheaf E) F).hom
      (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.2
        (dualSheaf E) F).isIso_hom ((U1 ⊓ U2).ι u)
    have hdd := bijective_stalkMapOfHom_toDoubleDual
      (tensorModules (dualSheaf E) F) ((U1 ⊓ U2).ι u)
      (isReflexive_stalk_tensorModules_dual E F _ hfE hfF)
    have hpin := toDoubleDual_comp_dualTensorHullToSheafHom E F hF
    have hcomp : Function.Bijective
        ((stalkMapOfHom (dualTensorHullToSheafHom E F hF) ((U1 ⊓ U2).ι u)) ∘
          (stalkMapOfHom (toDoubleDual (tensorModules (dualSheaf E) F)) ((U1 ⊓ U2).ι u))) := by
      have hfe : (stalkMapOfHom (dualTensorHullToSheafHom E F hF) ((U1 ⊓ U2).ι u)) ∘
            (stalkMapOfHom (toDoubleDual (tensorModules (dualSheaf E) F)) ((U1 ⊓ U2).ι u))
          = (stalkMapOfHom (tensorDualToSheafHomModule E F) ((U1 ⊓ U2).ι u)) ∘
            (stalkMapOfHom (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf
              X.ringCatSheaf.2 (dualSheaf E) F).hom ((U1 ⊓ U2).ι u)) := by
        funext m
        rw [Function.comp_apply, Function.comp_apply,
          ← Stacks.AlgebraicGeometry.ReflexiveModules.stalkMapOfHom_comp_apply, hpin]
        exact Stacks.AlgebraicGeometry.ReflexiveModules.stalkMapOfHom_comp_apply _ _ _ m
      rw [hfe]
      exact hth.comp hbr
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      ((Function.Bijective.of_comp_iff _ hdd).mp hcomp)
  exact isIso_of_restrict_of_isIso_unit (U1 ⊓ U2) _
    (Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive (U1 ⊓ U2) _
      (isReflexive_reflexiveHull X (tensorModules (dualSheaf E) F)) hdepth)
    (Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive (U1 ⊓ U2) _
      (sheafHom_isReflexive X E F hF) hdepth)
    hres

end Global

end AlgebraicGeometry.CoherentReflexive

end
