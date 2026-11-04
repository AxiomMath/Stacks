module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicUnitFromSystem
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.TensorComparisonAssociator
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraAssembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraMultiplicationDescent

/-!
# The associativity and left unit laws of the descended multiplication

`AlgebraicGeometry.existsUnique_multiplication_of_adicAlgebraModuleSystem` descends the
multiplications of a cartesian system `(B n)` of quasi-coherent algebra sheaves to a morphism
`μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩` on the algebraization `𝒩`. This file proves that the induced multiplication on
local sections is associative and has the descended unit as a left unit, and assembles the
resulting `Stacks.FundamentalGroup.ModuleAlgebraData` on `𝒩`.

## Main definitions

* `AlgebraicGeometry.properModule`: the algebraization, as an object of
  `AlgebraicGeometry.Scheme.Modules`.
* `AlgebraicGeometry.moduleAlgebraDataOfAdicAlgebraModuleSystem`: the
  `Stacks.FundamentalGroup.ModuleAlgebraData` on the algebraization.

## Main results

* `AlgebraicGeometry.mulPresheafOfHom_assoc`: the sheaf-level identity
  `(μ ▷ E) ≫ μ = α ≫ (E ◁ μ) ≫ μ` makes the induced multiplication associative on local
  sections.
* `AlgebraicGeometry.mulPresheafOfHom_one_mul`: the sheaf-level identity
  `λ⁻¹ ≫ (η ▷ E) ≫ μ = 𝟙 E` makes `η(1)` a left unit on local sections.
* `AlgebraicGeometry.eq_of_map_eq_tensorCube`: two morphisms out of the tensor cube of the
  algebraization that agree on every adic thickening are equal.
* `AlgebraicGeometry.hom_assoc_of_adicAlgebraMulApp`: the descended multiplication is
  associative.
* `AlgebraicGeometry.hom_one_of_adicAlgebraMulApp`: the descended unit is a left unit for the
  descended multiplication.
* `AlgebraicGeometry.exists_moduleAlgebraData_of_adicAlgebraModuleSystem`: the algebraization
  carries a `Stacks.FundamentalGroup.ModuleAlgebraData`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
open Stacks.Algebraization (HasProperSupport)
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.RelativeSpec.AlgebraSheaf (multiplication unitModuleMap)
open Stacks.AffineAlgebraEquivalence (algebraPullback)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)
open Stacks.PullbackTensorCoherence (tmul tensor_hom_ext₂ whiskerLeft_tmul whiskerRight_tmul
  associator_hom_tmul leftUnitor_hom_tmul oneSec)
open Stacks.SheafOfModules (comp_val_app_apply)

universe u

namespace AlgebraicGeometry

attribute [local instance] monoidalOfScheme moduleOnSectionsAtSchemePresheaf

/-! ### The section-level associativity from the sheaf-level one -/

/-- If `μ : E ⊗ E ⟶ E` satisfies the sheaf-level associativity
`(μ ▷ E) ≫ μ = α ≫ (E ◁ μ) ≫ μ` on the tensor cube, then the multiplication
`AlgebraicGeometry.mulPresheafOfHom E μ` is associative on local sections. -/
public theorem mulPresheafOfHom_assoc {Y : Scheme.{u}} (E : Y.Modules)
    (μ : (E ⊗ E : Y.Modules) ⟶ E)
    (hassoc : (μ ▷ E) ≫ μ = (α_ E E E).hom ≫ (E ◁ μ) ≫ μ)
    (U : (Y.Opens)ᵒᵖ) (x y z : E.val.obj U) :
    PresheafOfModules.Hom.app (mulPresheafOfHom E μ) U
        (PresheafOfModules.Hom.app (mulPresheafOfHom E μ) U (x ⊗ₜ[Γ(Y, U.unop)] y) ⊗ₜ z) =
      PresheafOfModules.Hom.app (mulPresheafOfHom E μ) U
        (x ⊗ₜ PresheafOfModules.Hom.app (mulPresheafOfHom E μ) U (y ⊗ₜ[Γ(Y, U.unop)] z)) := by
  refine Eq.trans ?_ (Eq.trans (congrArg
    (fun k : (E ⊗ E : Y.Modules) ⊗ E ⟶ E =>
      (k.val.app U).hom (tmul Y.toRingedSpace (E ⊗ E : Y.Modules) E U
        (tmul Y.toRingedSpace E E U x y) z)) hassoc) ?_)
  · exact ((comp_val_app_apply _ _ U _).trans
      (congrArg (fun t => (μ.val.app U).hom t)
        (whiskerRight_tmul μ U (tmul Y.toRingedSpace E E U x y) z))).symm
  · exact (comp_val_app_apply _ _ U _).trans
      ((congrArg (fun t => (((E ◁ μ) ≫ μ).val.app U).hom t)
          (associator_hom_tmul U x y z)).trans
        ((comp_val_app_apply _ _ U _).trans
          (congrArg (fun t => (μ.val.app U).hom t)
            (whiskerLeft_tmul μ U x (tmul Y.toRingedSpace E E U y z)))))

/-- The algebraization `P.obj.obj`, as an object of `AlgebraicGeometry.Scheme.Modules`. -/
public def properModule {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (P : Stacks.Algebraization.CoherentModulesProperOver f) : X.Modules := P.obj.obj


/-! ### The section-level left unit law from the sheaf-level one -/

/-- If `λ⁻¹ ≫ (η ▷ E) ≫ μ` is the identity of `E`, then `η(1)` is a left unit for the
multiplication `AlgebraicGeometry.mulPresheafOfHom E μ` on local sections. -/
public theorem mulPresheafOfHom_one_mul {Y : Scheme.{u}} (E : Y.Modules)
    (μ : (E ⊗ E : Y.Modules) ⟶ E) (η : (𝟙_ Y.Modules) ⟶ E)
    (hone : (λ_ E).inv ≫ (η ▷ E) ≫ μ = 𝟙 E)
    (U : (Y.Opens)ᵒᵖ) (x : E.val.obj U) :
    PresheafOfModules.Hom.app (mulPresheafOfHom E μ) U
        (η.val.app U (1 : Γ(Y, U.unop)) ⊗ₜ x) = x := by
  have hunitor : ((λ_ E).hom.val.app U).hom
      (tmul Y.toRingedSpace (𝟙_ Y.Modules) E U (oneSec Y.toRingedSpace U) x) = x := by
    refine (leftUnitor_hom_tmul U (oneSec Y.toRingedSpace U) x).trans ?_
    simp [Stacks.PullbackTensorCoherence.oneSec]
  have hinv : ((λ_ E).inv.val.app U).hom x =
      tmul Y.toRingedSpace (𝟙_ Y.Modules) E U (oneSec Y.toRingedSpace U) x :=
    (congrArg ((λ_ E).inv.val.app U).hom hunitor).symm.trans
      (Stacks.SheafOfModules.inv_val_app_hom_val_app
        (show ((𝟙_ Y.Modules) ⊗ E : Y.Modules) ≅ E from λ_ E) U _)
  refine Eq.trans ?_ (congrArg (fun k : E ⟶ E => (k.val.app U).hom x) hone)
  exact (((congrArg (fun t => (μ.val.app U).hom t)
        (whiskerRight_tmul η U (oneSec Y.toRingedSpace U) x)).symm.trans
      (congrArg (fun t => (μ.val.app U).hom (((η ▷ E).val.app U).hom t)) hinv.symm)).trans
    ((comp_val_app_apply _ _ U _).symm.trans (comp_val_app_apply _ _ U _).symm))

/-! ### The descent of the associativity and of the left unit law -/

section Descent

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
  (hpullback : ∀ {T S : Scheme.{u}} (g : T ⟶ S) (E : AlgebraSheaf S),
    AlgebraSheaf.IsQuasicoherent E → AlgebraPullbackModuleIso g E)
  (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n))
  (hqc : ∀ n, AlgebraSheaf.IsQuasicoherent (B n))
  (hBtrans : ∀ n, Nonempty
    ((algebraPullback (adicBaseChangeSucc A I f n)).obj (B (n + 1)) ≅ B n))
  (hMcoh : ∀ n, _root_.SheafOfModules.IsCoherent.{u} (AlgebraSheaf.underlyingModule (B n)))
  (hM0 : HasProperSupport (pullback.snd f (adicThickeningι A I 0))
    (AlgebraSheaf.underlyingModule (B 0)))
  (P : Stacks.Algebraization.CoherentModulesProperOver f)
  (e : (adicThickeningCompletionFunctor A I f).obj P ≅
    adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0)

/-- The two directions of an isomorphism of adic systems cancel on each component:
`e.inv.app n ≫ e.hom.app n = 𝟙`. -/
public theorem inv_app_comp_hom_app (n : ℕ) :
    e.inv.app n ≫ e.hom.app n = 𝟙 (AlgebraSheaf.underlyingModule (B n)) :=
  congrArg (fun t : adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0 ⟶
      adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0 => t.app n) e.inv_hom_id

/-- If `μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩` restricts to `AlgebraicGeometry.adicAlgebraMulApp` on every adic
thickening, then the two bracketings `(μ ▷ 𝒩) ≫ μ` and `α ≫ (𝒩 ◁ μ) ≫ μ` agree after pullback
to the `n`-th thickening. -/
public theorem map_assoc_adicAlgebraMulApp
    (μ : (properModule P ⊗ properModule P) ⟶ properModule P)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (n : ℕ) :
    (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map
        ((μ ▷ properModule P) ≫ μ) =
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map
        ((α_ (properModule P) (properModule P) (properModule P)).hom ≫ (properModule P ◁ μ) ≫ μ) :=
  map_assoc_of_tensorDescentApp (pullback.fst f (adicThickeningι A I n)) (properModule P) μ
    (e.hom.app n) (e.inv.app n)
    (inv_app_comp_hom_app A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (multiplication (B n))
    (multiplication_assoc (B n) (multiplication (B n)) rfl) (hμ n)

omit [IsNoetherianRing A] in
/-- The underlying module of `AlgebraicGeometry.tensorCubeProperOver` is the tensor cube
`(𝒩 ⊗ 𝒩) ⊗ 𝒩` of the algebraization. -/
public theorem tensorCubeProperOver_obj_obj :
    (tensorCubeProperOver f (properModule P) P.obj.property P.property).obj.obj =
      (properModule P ⊗ properModule P) ⊗ properModule P := rfl

/-- If the Stacks 088F functor is an equivalence, two morphisms between the underlying modules
of coherent modules proper over `f` that agree after pullback to every adic thickening are
equal. -/
private theorem eq_of_map_eq_of_isEquivalence
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    {Q Q' : Stacks.Algebraization.CoherentModulesProperOver f} (L R : Q.obj.obj ⟶ Q'.obj.obj)
    (h : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map L =
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map R) :
    L = R := by
  have := h088F
  have hmap : (adicThickeningCompletionFunctor A I f).map (⟨⟨L⟩⟩ : Q ⟶ Q') =
      (adicThickeningCompletionFunctor A I f).map ⟨⟨R⟩⟩ :=
    AdicCoherentModuleSystem.Hom.ext (funext h)
  exact congrArg (fun t : Q ⟶ Q' => t.hom.hom)
    (Functor.map_injective (adicThickeningCompletionFunctor A I f) hmap)

/-- If the Stacks 088F functor is an equivalence, two morphisms out of the tensor cube of the
algebraization that agree after pullback to every adic thickening are equal. -/
public theorem eq_of_map_eq_tensorCube
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (L R : ((properModule P ⊗ properModule P) ⊗ properModule P) ⟶ properModule P)
    (h : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map L =
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map R) :
    L = R :=
  eq_of_map_eq_of_isEquivalence A I f h088F
    (Q := tensorCubeProperOver f (properModule P) P.obj.property P.property) (Q' := P) L R h

/-- If the Stacks 088F functor is an equivalence and `μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩` restricts to
`AlgebraicGeometry.adicAlgebraMulApp` on every adic thickening, then `μ` is associative:
`(μ ▷ 𝒩) ≫ μ = α ≫ (𝒩 ◁ μ) ≫ μ`. -/
public theorem hom_assoc_of_adicAlgebraMulApp
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (μ : (properModule P ⊗ properModule P) ⟶ properModule P)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n) :
    (μ ▷ properModule P) ≫ μ =
      (α_ (properModule P) (properModule P) (properModule P)).hom ≫
        (properModule P ◁ μ) ≫ μ :=
  eq_of_map_eq_tensorCube A I f P h088F _ _
    (map_assoc_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e μ hμ)

/-- If the Stacks 088F functor is an equivalence and `μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩` restricts to
`AlgebraicGeometry.adicAlgebraMulApp` on every adic thickening, then the multiplication
`AlgebraicGeometry.mulPresheafOfHom 𝒩 μ` is associative on local sections. -/
public theorem mulPresheafOfHom_assoc_of_adicAlgebraMulApp
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (μ : (properModule P ⊗ properModule P) ⟶ properModule P)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (U : (X.Opens)ᵒᵖ) (x y z : (properModule P).val.obj U) :
    PresheafOfModules.Hom.app (mulPresheafOfHom (properModule P) μ) U
        (PresheafOfModules.Hom.app (mulPresheafOfHom (properModule P) μ) U
          (x ⊗ₜ[Γ(X, U.unop)] y) ⊗ₜ z) =
      PresheafOfModules.Hom.app (mulPresheafOfHom (properModule P) μ) U
        (x ⊗ₜ PresheafOfModules.Hom.app (mulPresheafOfHom (properModule P) μ) U
          (y ⊗ₜ[Γ(X, U.unop)] z)) :=
  mulPresheafOfHom_assoc (properModule P) μ
    (hom_assoc_of_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e h088F μ hμ) U x y z

/-- If the Stacks 088F functor is an equivalence, two endomorphisms of the algebraization that
agree after pullback to every adic thickening are equal. -/
public theorem eq_of_map_eq_self
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (L R : properModule P ⟶ properModule P)
    (h : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map L =
        (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map R) :
    L = R :=
  eq_of_map_eq_of_isEquivalence A I f h088F (Q := P) (Q' := P) L R h

/-- The two directions of an isomorphism of adic systems cancel on each component:
`e.hom.app n ≫ e.inv.app n = 𝟙`. -/
public theorem hom_app_comp_inv_app (n : ℕ) :
    e.hom.app n ≫ e.inv.app n =
      𝟙 (adicThickeningCompletion A I f P.obj.obj n) :=
  congrArg (fun t : (adicThickeningCompletionFunctor A I f).obj P ⟶
      (adicThickeningCompletionFunctor A I f).obj P => t.app n) e.hom_inv_id

/-- If `μ` and `η` restrict to the multiplication and the unit of `B n` on every adic
thickening, then `λ⁻¹ ≫ (η ▷ 𝒩) ≫ μ` pulls back to the identity on the `n`-th thickening. -/
public theorem map_one_adicAlgebraMulApp
    (μ : (properModule P ⊗ properModule P) ⟶ properModule P)
    (η : (𝟙_ X.Modules) ⟶ properModule P)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (hη : ∀ n : ℕ,
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso
            (pullback.fst f (adicThickeningι A I n))).inv ≫
          (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map η =
        unitModuleMap (B n) ≫ e.inv.app n)
    (n : ℕ) :
    (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map
        ((λ_ (properModule P)).inv ≫ (η ▷ properModule P) ≫ μ) =
      𝟙 ((Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).obj
        (properModule P)) :=
  map_one_of_tensorDescentApp (pullback.fst f (adicThickeningι A I n)) (properModule P) μ η
    (e.hom.app n) (e.inv.app n)
    (inv_app_comp_hom_app A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (hom_app_comp_inv_app A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (multiplication (B n)) (unitModuleMap (B n))
    (unitModuleMap_comp_multiplication (B n) (multiplication (B n)) rfl (unitModuleMap (B n)) rfl)
    (hμ n) (hη n)

/-- If the Stacks 088F functor is an equivalence and `μ`, `η` restrict to the multiplication
and the unit of `B n` on every adic thickening, then `λ⁻¹ ≫ (η ▷ 𝒩) ≫ μ = 𝟙 𝒩`. -/
public theorem hom_one_of_adicAlgebraMulApp
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (μ : (properModule P ⊗ properModule P) ⟶ properModule P)
    (η : (𝟙_ X.Modules) ⟶ properModule P)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (hη : ∀ n : ℕ,
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso
            (pullback.fst f (adicThickeningι A I n))).inv ≫
          (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map η =
        unitModuleMap (B n) ≫ e.inv.app n) :
    (λ_ (properModule P)).inv ≫ (η ▷ properModule P) ≫ μ = 𝟙 (properModule P) :=
  eq_of_map_eq_self A I f P h088F _ _ fun n =>
    (map_one_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e μ η hμ hη n).trans
      ((Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map_id
        (properModule P)).symm

/-- If the Stacks 088F functor is an equivalence and `μ`, `η` restrict to the multiplication
and the unit of `B n` on every adic thickening, then `η(1)` is a left unit for
`AlgebraicGeometry.mulPresheafOfHom 𝒩 μ` on local sections. -/
public theorem mulPresheafOfHom_one_mul_of_adicAlgebraMulApp
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (μ : (properModule P ⊗ properModule P) ⟶ properModule P)
    (η : (𝟙_ X.Modules) ⟶ properModule P)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (hη : ∀ n : ℕ,
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso
            (pullback.fst f (adicThickeningι A I n))).inv ≫
          (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map η =
        unitModuleMap (B n) ≫ e.inv.app n)
    (U : (X.Opens)ᵒᵖ) (x : (properModule P).val.obj U) :
    PresheafOfModules.Hom.app (mulPresheafOfHom (properModule P) μ) U
        (η.val.app U (1 : Γ(X, U.unop)) ⊗ₜ x) = x :=
  mulPresheafOfHom_one_mul (properModule P) μ η
    (hom_one_of_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e h088F μ η hμ hη) U x

/-! ### The four fields and the three laws, assembled -/

/-- The `Stacks.FundamentalGroup.ModuleAlgebraData` on the algebraization with unit `η` and
multiplication `AlgebraicGeometry.mulPresheafOfHom 𝒩 μ`, for `μ` and `η` restricting to the
multiplication and the unit of `B n` on every adic thickening. -/
public def moduleAlgebraDataOfAdicAlgebraModuleSystem
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (μ : (properModule P ⊗ properModule P) ⟶ properModule P)
    (η : (𝟙_ X.Modules) ⟶ properModule P)
    (hμ : ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n)
    (hη : ∀ n : ℕ,
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso
            (pullback.fst f (adicThickeningι A I n))).inv ≫
          (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map η =
        unitModuleMap (B n) ≫ e.inv.app n) :
    Stacks.FundamentalGroup.ModuleAlgebraData (properModule P) where
  unit := η
  mul := mulPresheafOfHom (properModule P) μ
  mul_comm := mulPresheafOfHom_comm_of_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0
    P e h088F μ hμ
  mul_assoc := mulPresheafOfHom_assoc_of_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh
    hM0 P e h088F μ hμ
  one_mul := mulPresheafOfHom_one_mul_of_adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh
    hM0 P e h088F μ η hμ hη

include hpullback hqc hBtrans hMcoh hM0 e in
/-- If `A` is `I`-adically complete and the Stacks 088F functor is an equivalence, then the
algebraization carries a `Stacks.FundamentalGroup.ModuleAlgebraData`. -/
public theorem exists_moduleAlgebraData_of_adicAlgebraModuleSystem [IsAdicComplete I A]
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence) :
    Nonempty (Stacks.FundamentalGroup.ModuleAlgebraData (properModule P)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨μ, hμ, -⟩ := existsUnique_multiplication_of_adicAlgebraModuleSystem A I f hpullback B
    hqc hBtrans hMcoh hM0 P e h088F
  obtain ⟨η, hη⟩ := exists_unit_of_adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh
    hM0 P e
  exact ⟨moduleAlgebraDataOfAdicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0 P e
    h088F μ η hμ hη⟩

end Descent

end AlgebraicGeometry

end
