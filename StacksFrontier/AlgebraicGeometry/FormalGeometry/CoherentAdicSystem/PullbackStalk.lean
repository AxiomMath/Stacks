module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# Germs of the pullback unit generate the stalks of a pullback

Let `f : X ⟶ Y` be a morphism of schemes and `M` an `𝒪_Y`-module. The unit of the adjunction
`f^* ⊣ f_*` sends a section `s` of `M` over an open `W ⊆ Y` to a section of `f^*M` over
`f⁻¹W`; the germs at a point `x` of the sections so obtained generate the stalk `(f^*M)_x` as a
module over `𝒪_{X,x}`.

This is the only consequence of the stalk formula
`(f^*M)_x = 𝒪_{X,x} ⊗_{𝒪_{Y,f x}} M_{f x}` of Tag 0098 that the comparison of ideal-power
multiples under pullback needs, and it is stated here in the form that comparison consumes: a
scalar annihilating the image of every unit germ under a morphism out of `f^*M` annihilates the
image of the whole stalk.

## Main results

* `Stacks.Algebraization.pullbackStalk_hom_eq_zero` — a linear map out of `(f^*M)_x` vanishing
  on every unit germ is zero.
* `Stacks.Algebraization.smul_stalkMap_eq_zero` — the annihilation form used by the comparison
  of ideal-power multiples.

## Implementation notes

The stalk is spelled `TopCat.Presheaf.stalk M.val.presheaf x`, with the `𝒪_{X,x}`-module
structure Mathlib puts on the stalk of a presheaf of modules. This is the spelling in which
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` states the stalk formula and
in which `Stacks.ModuleSkyscraper.stalkMapLinear` computes the map induced by a morphism, so no
transport between two module structures on the stalk is needed.

Generation is read off the stalk formula by induction on the tensor product: a pure tensor
`a ⊗ m` is `a • (1 ⊗ m)`, the equivalence carries `1 ⊗ germ s` to the germ of the unit image of
`s`, and every element of `M_{f x}` is a germ.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry TensorProduct

universe u

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf structureSheafRing

namespace Stacks.Algebraization

variable {X Y : Scheme.{u}}

/-- The adjunction `f^* ⊣ f_*` for sheaves of modules on schemes, in the ringed-space spelling
for which the stalk formula of Tag 0098 is available. -/
public abbrev schemeModuleAdjunction (f : X ⟶ Y) :
    Scheme.Modules.pullback f ⊣ Scheme.Modules.pushforward f :=
  modulePullbackPushforwardAdjunction f.toLRSHom.toShHom

/-- **A linear map vanishing on the preimages of the pure tensors `1 ⊗ m` is zero**, for a module
presented by a linear equivalence with a base change `A ⊗_R N`: a pure tensor `a ⊗ m` is
`a • (1 ⊗ m)`, so those preimages generate. -/
public theorem eq_zero_of_eq_zero_on_one_tmul {R A N T P : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A] [AddCommMonoid N] [Module R N] [AddCommMonoid T] [Module A T]
    [AddCommMonoid P] [Module A P] (e : T ≃ₗ[A] TensorProduct R A N) (α : T →ₗ[A] P)
    (h : ∀ m : N, α (e.symm ((1 : A) ⊗ₜ[R] m)) = 0) (z : T) : α z = 0 := by
  have key : ∀ t, α (e.symm t) = 0 := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a m =>
      have ha : (a ⊗ₜ[R] m : TensorProduct R A N) = a • ((1 : A) ⊗ₜ[R] m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ha, map_smul, map_smul, h, smul_zero]
    | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  simpa only [LinearEquiv.symm_apply_apply] using key (e z)

/-- The germ at `x` of the image under the unit of `f^* ⊣ f_*` of a section of `M` over an open
neighbourhood of `f x`. These germs generate the stalk of `f^*M` at `x`. -/
public abbrev unitGerm (f : X ⟶ Y) (x : X) (M : Y.Modules) (W : Y.Opens) (hw : f x ∈ W)
    (s : Γ(M, W)) :
    (modulesStalkFunctor X x).obj ((Scheme.Modules.pullback f).obj M) :=
  (((Scheme.Modules.pullback f).obj M).presheaf.germ (f ⁻¹ᵁ W) x hw).hom
    (((schemeModuleAdjunction f).unit.app M).app W s)

/-- **A linear map out of the stalk of a pullback vanishing on every unit germ is zero.**

By the stalk formula of Tag 0098 the stalk is `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} M_{f x}`, with the germ of
the unit image of a section `s` corresponding to `1 ⊗ germ s`; every element of `M_{f x}` is a
germ, so `Stacks.Algebraization.eq_zero_of_eq_zero_on_one_tmul` applies. -/
public theorem pullbackStalk_hom_eq_zero (f : X ⟶ Y) (x : X) (M : Y.Modules)
    {A : ModuleCat.{u} ↑(X.presheaf.stalk x)}
    (α : (modulesStalkFunctor X x).obj ((Scheme.Modules.pullback f).obj M) ⟶ A)
    (h : ∀ (W : Y.Opens) (hw : f x ∈ W) (s : Γ(M, W)), α.hom (unitGerm f x M W hw s) = 0)
    (z : (modulesStalkFunctor X x).obj ((Scheme.Modules.pullback f).obj M)) : α.hom z = 0 := by
  let _ : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ : Algebra ↑(Y.presheaf.stalk (f.toLRSHom.toShHom.hom.base x)) ↑(X.presheaf.stalk x) :=
    (f.toLRSHom.toShHom.hom.stalkMap x).hom.toAlgebra
  obtain ⟨e, he⟩ := exists_modulePullbackStalkLinearEquiv f.toLRSHom.toShHom M x
  refine eq_zero_of_eq_zero_on_one_tmul e α.hom (fun m => ?_) z
  obtain ⟨W, hw, s, hm⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
  subst hm
  exact (congrArg (fun t => α.hom (e.symm t)) (he W hw s)).symm.trans
    ((congrArg α.hom (e.symm_apply_apply _)).trans (h W hw s))

/-- The stalk map of a morphism of `𝒪_X`-modules, on a germ. -/
public theorem modulesStalkFunctor_map_germ {M N : X.Modules} (g : M ⟶ N) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) :
    ((modulesStalkFunctor X x).map g).hom ((M.presheaf.germ U x hx).hom s) =
      (N.presheaf.germ U x hx).hom (g.app U s) :=
  stalkMapLinear_germ g.val x U hx s

/-- Taking germs is compatible with the scalar action on the stalk. -/
public theorem germ_smul {M : X.Modules} (x : X) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) (s : Γ(M, U)) :
    (M.presheaf.germ U x hx).hom (r • s) =
      (X.presheaf.germ U x hx).hom r •
        (show (modulesStalkFunctor X x).obj M from (M.presheaf.germ U x hx).hom s) :=
  germ_smul' M.val x U hx r s

/-- **The annihilation form of generation by unit germs.** A scalar of `𝒪_{X,x}` annihilating
the image under `g` of every germ coming from the unit of `f^* ⊣ f_*` annihilates the image
under `g` of the whole stalk of `f^*M` at `x`. -/
public theorem smul_stalkMap_eq_zero (f : X ⟶ Y) (x : X) (M : Y.Modules) {N : X.Modules}
    (g : (Scheme.Modules.pullback f).obj M ⟶ N) (ρ : ↑(X.presheaf.stalk x))
    (h : ∀ (W : Y.Opens) (hw : f x ∈ W) (s : Γ(M, W)),
      ρ • ((modulesStalkFunctor X x).map g).hom (unitGerm f x M W hw s) = 0)
    (z : (modulesStalkFunctor X x).obj ((Scheme.Modules.pullback f).obj M)) :
    ρ • ((modulesStalkFunctor X x).map g).hom z = 0 :=
  pullbackStalk_hom_eq_zero f x M (A := (modulesStalkFunctor X x).obj N)
    ((modulesStalkFunctor X x).map g ≫ (ρ • 𝟙 ((modulesStalkFunctor X x).obj N))) h z

end Stacks.Algebraization

end
