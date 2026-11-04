module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicTensorSystemComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CanonicalTensorProperSupport

/-!
# The multiplication of a system of algebra sheaves, descended to the algebraization

Let `(B n)` be a cartesian system of quasi-coherent algebra sheaves on the adic thickenings `Xₙ`,
`AlgebraicGeometry.adicAlgebraModuleSystem` the adic system of modules underlying it, and `𝒩` a
coherent module with proper support together with an isomorphism `e` of its completion with that
system. Granted the Stacks 088F equivalence, the multiplications of the `B n` come from a unique
morphism `μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩`.

## Main definitions

* `AlgebraicGeometry.adicAlgebraMulApp`: the `n`-th component, the multiplication of `B n` read
  as a morphism out of the restriction of `𝒩 ⊗ 𝒩` to `Xₙ` through the comparison of
  [Stacks, Tag 01CD] and the two directions of `e`.
* `AlgebraicGeometry.adicAlgebraMulSystemHom`: the morphism of adic systems out of the completion
  of the tensor square `AlgebraicGeometry.tensorSquareProperOver` with these components.
* `AlgebraicGeometry.mulPresheafOfHom`: the morphism of presheaves of modules out of the pointwise
  tensor square obtained from a morphism `μ` out of the sheafified one by composing with the
  sheafification unit.

## Main results

* `AlgebraicGeometry.adicAlgebraMulApp_comm`: the components commute with the transitions of the
  two completions.
* `AlgebraicGeometry.existsUnique_multiplication_of_adicAlgebraModuleSystem`: there is exactly one
  `μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩` restricting to `AlgebraicGeometry.adicAlgebraMulApp` on every adic thickening.
* `AlgebraicGeometry.mulPresheafOfHom_app`: `AlgebraicGeometry.mulPresheafOfHom` on local
  sections.

## Implementation notes

Several declarations take the module underlying their source as a binder `{T}` with an equation
`hT`, and `subst` it. Stated with the tensor square written out, the identification of that square
with the module of `AlgebraicGeometry.tensorSquareProperOver` sits under
`AlgebraicGeometry.adicThickeningCompletion` at the fibre product
`AlgebraicGeometry.adicBaseChange A I f n`, where unifying the two spellings times out; as a
binder it is the bare equation `AlgebraicGeometry.tensorSquareProperOver_obj_obj`, proved by
`rfl`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Algebraization (HasProperSupport)
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.RelativeSpec.AlgebraSheaf (multiplication)
open Stacks.AffineAlgebraEquivalence (algebraPullback)

universe u

namespace AlgebraicGeometry

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

/-! ### The component on a thickening -/

/-- The multiplication of the algebra sheaf `B n`, read as a morphism out of the restriction
`vₙ^*(𝒩 ⊗ 𝒩)` of the tensor square of `𝒩`: split the restriction by the comparison of
[Stacks, Tag 01CD], carry each factor to `B n` by `e`, multiply, and come back by `e⁻¹`. This is
`AlgebraicGeometry.tensorDescentApp` at `w = vₙ`, `N = 𝒩`, `M` the module underlying `B n` and
`mul` its multiplication. -/
public abbrev adicAlgebraMulApp (n : ℕ) :
    adicThickeningCompletion A I f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj
        (P.obj.obj)) n ⟶
      adicThickeningCompletion A I f P.obj.obj n :=
  tensorDescentApp (pullback.fst f (adicThickeningι A I n)) P.obj.obj
    (AlgebraSheaf.underlyingModule (B n)) (e.hom.app n) (e.inv.app n) (multiplication (B n))

/-! ### The compatibility with the transitions -/

/-- The family `AlgebraicGeometry.adicAlgebraMulApp` commutes with the transitions of the two
completions. -/
public theorem adicAlgebraMulApp_comm (n : ℕ) :
    (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map
          (adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e (n + 1)) ≫
        (adicThickeningCompletionTransition A I f P.obj.obj n).hom =
      (adicThickeningCompletionTransition A I f
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj
            (P.obj.obj)) n).hom ≫
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n :=
  tensorDescentApp_comm (adicBaseChangeSucc A I f n)
    (pullback.fst f (adicThickeningι A I (n + 1))) (adicBaseChangeSucc_fst A I f n) P.obj.obj
    (multiplication (B (n + 1))) (multiplication (B n))
    ((adicAlgebraModuleSystem A I f hpullback B hqc hBtrans hMcoh hM0).transitionIso n).hom
    (e.hom.app (n + 1)) (e.hom.app n) (e.inv.app (n + 1)) (e.inv.app n)
    (pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition A I f n P.obj.obj)
    (pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition A I f n
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj (P.obj.obj)))
    (multiplication_comp_adicAlgebraModuleSystem_transitionIso A I f hpullback B hqc hBtrans
      hMcoh hM0 n)
    (e.hom.comm n) (e.inv.comm n)

/-! ### Descent statements with the source module named by an equation -/

section Named

variable {T : X.Modules}

/-- A family of morphisms on the thickenings compatible with the transitions is a morphism of
the adic systems, with the module underlying the source named by an equation `hT`. -/
public def homOfAdicThickeningFamily
    (Pt Q : Stacks.Algebraization.CoherentModulesProperOver f) (hT : Pt.obj.obj = T)
    (m : ∀ n : ℕ, adicThickeningCompletion A I f T n ⟶
      adicThickeningCompletion A I f Q.obj.obj n)
    (hm : ∀ n : ℕ,
      (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (m (n + 1)) ≫
          (adicThickeningCompletionTransition A I f Q.obj.obj n).hom =
        (adicThickeningCompletionTransition A I f T n).hom ≫ m n) :
    (adicThickeningCompletionFunctor A I f).obj Pt ⟶
      (adicThickeningCompletionFunctor A I f).obj Q := by
  subst hT
  exact { app := m, comm := hm }

/-- `AlgebraicGeometry.existsUnique_hom_of_adicThickeningCompletion` with the module underlying
the source named by an equation `hT`; at `hT := rfl` it is that statement. -/
public theorem existsUnique_hom_of_adicThickeningCompletion_of_eq
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence)
    (Pt Q : Stacks.Algebraization.CoherentModulesProperOver f) (hT : Pt.obj.obj = T)
    (m : ∀ n : ℕ, adicThickeningCompletion A I f T n ⟶
      adicThickeningCompletion A I f Q.obj.obj n)
    (hm : ∀ n : ℕ,
      (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map (m (n + 1)) ≫
          (adicThickeningCompletionTransition A I f Q.obj.obj n).hom =
        (adicThickeningCompletionTransition A I f T n).hom ≫ m n) :
    ∃! μ : T ⟶ Q.obj.obj, ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ = m n := by
  subst hT
  exact existsUnique_hom_of_adicThickeningCompletion A I f h088F Pt Q m hm

end Named

/-! ### The morphism of systems, and the descended multiplication -/

omit [IsNoetherianRing A] in
/-- The module underlying `AlgebraicGeometry.tensorSquareProperOver` is the tensor square
sheaf. -/
public theorem tensorSquareProperOver_obj_obj' :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj (P.obj.obj)) =
      (tensorSquareProperOver f P.obj.obj P.obj.property P.property).obj.obj :=
  rfl

omit [IsNoetherianRing A] in
/-- `AlgebraicGeometry.tensorSquareProperOver_obj_obj'` read the other way. -/
public theorem tensorSquareProperOver_obj_obj :
    (tensorSquareProperOver f P.obj.obj P.obj.property P.property).obj.obj =
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj
        (P.obj.obj)) :=
  rfl

/-- `AlgebraicGeometry.adicAlgebraMulApp` with its source named by an equation: for
`hT : 𝒩 ⊗ 𝒩 = T` this is the same family, read as a family out of the completion of `T`. -/
public def adicAlgebraMulAppOfEq {T : X.Modules}
    (hT : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj (P.obj.obj)) = T)
    (n : ℕ) :
    adicThickeningCompletion A I f T n ⟶ adicThickeningCompletion A I f P.obj.obj n := by
  subst hT
  exact adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n

/-- `AlgebraicGeometry.adicAlgebraMulAppOfEq` along a reflexivity proof is
`AlgebraicGeometry.adicAlgebraMulApp`. -/
public theorem adicAlgebraMulAppOfEq_rfl (n : ℕ) :
    adicAlgebraMulAppOfEq A I f hpullback B hqc hBtrans hMcoh hM0 P e rfl n =
      adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n :=
  rfl

/-- `AlgebraicGeometry.adicAlgebraMulApp_comm` for `AlgebraicGeometry.adicAlgebraMulAppOfEq`, so
with the module of the source a binder. -/
public theorem adicAlgebraMulAppOfEq_comm {T : X.Modules}
    (hT : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj (P.obj.obj)) = T)
    (n : ℕ) :
    (Scheme.Modules.pullback (adicBaseChangeSucc A I f n)).map
          (adicAlgebraMulAppOfEq A I f hpullback B hqc hBtrans hMcoh hM0 P e hT (n + 1)) ≫
        (adicThickeningCompletionTransition A I f P.obj.obj n).hom =
      (adicThickeningCompletionTransition A I f T n).hom ≫
        adicAlgebraMulAppOfEq A I f hpullback B hqc hBtrans hMcoh hM0 P e hT n := by
  subst hT
  rw [adicAlgebraMulAppOfEq_rfl, adicAlgebraMulAppOfEq_rfl]
  exact adicAlgebraMulApp_comm A I f hpullback B hqc hBtrans hMcoh hM0 P e n

/-- The morphism of adic systems `AlgebraicGeometry.homOfAdicThickeningFamily` given by the
family `AlgebraicGeometry.adicAlgebraMulAppOfEq`, out of the completion of an object `Pt` of
`Stacks.Algebraization.CoherentModulesProperOver f` whose module is the tensor square. -/
public def adicAlgebraMulSystemHomOfEq
    (Pt : Stacks.Algebraization.CoherentModulesProperOver f)
    (hT : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj (P.obj.obj)) =
      Pt.obj.obj) :
    (adicThickeningCompletionFunctor A I f).obj Pt ⟶
      (adicThickeningCompletionFunctor A I f).obj P :=
  homOfAdicThickeningFamily A I f Pt P rfl
    (adicAlgebraMulAppOfEq A I f hpullback B hqc hBtrans hMcoh hM0 P e hT)
    (adicAlgebraMulAppOfEq_comm A I f hpullback B hqc hBtrans hMcoh hM0 P e hT)

/-- **The morphism of adic systems out of the completion of the tensor square**: the morphism, in
`AlgebraicGeometry.AdicCoherentModuleSystem A I f`, from the completion of
`AlgebraicGeometry.tensorSquareProperOver` to the completion of `𝒩`, whose `n`-th component is
the multiplication of `B n` read through `e` and the comparison of [Stacks, Tag 01CD]. -/
public def adicAlgebraMulSystemHom :
    (adicThickeningCompletionFunctor A I f).obj
        (tensorSquareProperOver f P.obj.obj P.obj.property P.property) ⟶
      (adicThickeningCompletionFunctor A I f).obj P :=
  adicAlgebraMulSystemHomOfEq A I f hpullback B hqc hBtrans hMcoh hM0 P e
    (tensorSquareProperOver f P.obj.obj P.obj.property P.property)
    (tensorSquareProperOver_obj_obj' A f P)

/-- **The multiplication of a cartesian system of algebra sheaves descends to the
algebraization.** Granted the Stacks 088F equivalence, there is exactly one morphism
`μ : 𝒩 ⊗ 𝒩 ⟶ 𝒩` whose restriction to the `n`-th adic thickening is
`AlgebraicGeometry.adicAlgebraMulApp` — the multiplication of `B n` read through `e` and the
comparison of [Stacks, Tag 01CD]. -/
public theorem existsUnique_multiplication_of_adicAlgebraModuleSystem
    (h088F : (adicThickeningCompletionFunctor A I f).IsEquivalence) :
    ∃! μ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj
        (P.obj.obj)) ⟶ P.obj.obj, ∀ n : ℕ,
      (Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).map μ =
        adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e n :=
  existsUnique_hom_of_adicThickeningCompletion_of_eq A I f
    (T := (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj (P.obj.obj)).obj (P.obj.obj)))
    h088F
    (tensorSquareProperOver f P.obj.obj P.obj.property P.property) P
    (tensorSquareProperOver_obj_obj A f P)
    (adicAlgebraMulApp A I f hpullback B hqc hBtrans hMcoh hM0 P e)
    (adicAlgebraMulApp_comm A I f hpullback B hqc hBtrans hMcoh hM0 P e)

end Descent

/-! ### From the descended morphism to the field of a `ModuleAlgebraData` -/

section Field

open Stacks.SheafOfModules.TensorStalkRingedSpace (sheafifyUnit toTensorSheafSection)

/-- The module structure on sections over the ring of sections spelled through
`AlgebraicGeometry.Scheme.presheaf`, as
`Stacks.SheafOfModules.TensorStalkRingedSpace.presheafTensor` writes it; instance search does not
find it through `AlgebraicGeometry.Scheme.ringCatSheaf`. -/
local instance moduleOnSectionsAtSchemePresheaf {Y : Scheme.{u}} (E : Y.Modules)
    (U : (Y.Opens)ᵒᵖ) : Module (Y.presheaf.obj U) (E.val.obj U) :=
  inferInstanceAs (Module (Y.ringCatSheaf.obj.obj U) (E.val.obj U))

/-- The morphism of presheaves of modules out of the pointwise tensor square of `E` attached to
a morphism `μ` out of the sheafified tensor square: its composite with the sheafification unit.
This is the reverse of `Stacks.RelativeSpec.AlgebraSheaf.multiplication`, which transposes a
presheaf-level multiplication to a sheaf-level one along the same adjunction. -/
public def mulPresheafOfHom {Y : Scheme.{u}} (E : Y.Modules)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ E) :
    (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf) E.val E.val) ⟶ E.val :=
  sheafifyUnit Y.toRingedSpace
      (PresheafOfModules.tensorObj (O := Y.toRingedSpace.presheaf) E.val E.val) ≫ μ.val

/-- `AlgebraicGeometry.mulPresheafOfHom` on local sections is `μ` evaluated at the
sheafification-unit image `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`. -/
public theorem mulPresheafOfHom_app {Y : Scheme.{u}} (E : Y.Modules)
    (μ : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj (E)).obj (E)) ⟶ E)
    (U : (Y.Opens)ᵒᵖ)
    (t : TensorProduct (Y.presheaf.obj U) (E.val.obj U) (E.val.obj U)) :
    PresheafOfModules.Hom.app (mulPresheafOfHom E μ) U t =
      (μ.val.app U).hom (toTensorSheafSection Y.toRingedSpace E E U t) :=
  rfl

end Field

end AlgebraicGeometry

end
