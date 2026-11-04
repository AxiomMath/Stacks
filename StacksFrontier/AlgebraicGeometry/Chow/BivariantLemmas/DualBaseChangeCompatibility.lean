module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackUnitTensorExtensionality
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap

/-!
# The dual base-change map and composition of morphisms

Let `t : W ⟶ Y` and `g : Y ⟶ X` be morphisms of schemes and `N` a module on `X`.  The dual
base-change map `Stacks.Chow.pullbackDualMap` of [Stacks Project, Tag 0GMX] is defined for one
morphism at a time, and this file compares the map of the composite `t ≫ g` with the two maps of
the factors: the dual base-change map of `t ≫ g` agrees, modulo the pullback-composition
comparison `AlgebraicGeometry.Scheme.Modules.pullbackComp`, with the dual base-change map of `g`
pulled back along `t` followed by the dual base-change map of `t`.

## Main results

* `Stacks.Chow.pullbackEvaluation_comp` — the pulled-back evaluation pairing of a composite is
  the pulled-back evaluation pairing of the second factor, transported along the
  pullback-composition comparison and along the dual base-change map of the first factor.
* `Stacks.Chow.pullbackDualMap_comp` — **the dual base-change map is compatible with composition
  of morphisms of schemes.**

## Implementation notes

Both statements are equalities of morphisms, and neither is proved by unfolding the construction
of `Stacks.Chow.pullbackDualMap`.  The pairing identity is proved by evaluating both sides on the
pure tensors of the canonical images of local sections of `N^∨` and of `N`, which determine a
morphism out of a tensor product of two inverse images
(`Stacks.PullbackUnitGenerators.tensor_hom_ext_of_unitSections`); on those sections both sides
are computed by `Stacks.Chow.pullbackEvaluation_unit_tmul` and
`AlgebraicGeometry.Scheme.Modules.pullbackComp_inv_unit`, and the composite of the two structure
morphisms appears as the structure morphism of the composite.  The map identity is then read off
the pairing identity by `Stacks.Chow.pullbackDualMap_eval`, which computes the dual base-change
map against evaluation, and extensionality for morphisms into a dual module.

The sections fed to the dual base-change map of the composite are arbitrary, not canonical
images, and that is the point: the two canonical images in the pairing identity sit on the *other*
side of `Stacks.Chow.pullbackDualMap_eval`, which is an identity for every local section.

The pullback is spelled `RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom` where
`Stacks.Chow.pullbackDualMap` is involved and `AlgebraicGeometry.Scheme.Modules.pullback g` where
the comparison of Mathlib is; the two are definitionally equal and the crossings happen inside
proofs given by `exact`, which tolerates them, rather than inside a `rw`, which does not.

## References

* [Stacks Project, Tag 0GMX](https://stacks.math.columbia.edu/tag/0GMX)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.TensorStalkRingedSpace (tensorSheafMap_app_toTensorSheafSection)
open Stacks.PullbackUnitGenerators
open scoped TensorProduct

universe u

namespace Stacks.Chow

noncomputable section

variable {W Y X : Scheme.{u}}

/-! ### Tools -/

/-- The inverse of an isomorphism of modules undoes it on local sections. -/
theorem iso_inv_val_app_hom_val_app {S : Scheme.{u}} {A B : S.Modules} (e : A ≅ B)
    (V : S.Opens) (x : A.val.obj (op V)) :
    e.inv.val.app (op V) (e.hom.val.app (op V) x) = x :=
  (comp_val_app e.hom e.inv V x).symm.trans
    (congrArg (fun f : A ⟶ A => f.val.app (op V) x) e.hom_inv_id)

/-- The tensor product of two morphisms of modules carries the pure tensor of two local
sections to the pure tensor of their images.  This is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection` at the
spelling `Stacks.Chow.tensorSheafPure` of a pure tensor. -/
theorem tensorSheafMap_tensorSheafPure {S : Scheme.{u}} {A A' B B' : S.Modules} (φ : A ⟶ A')
    (ψ : B ⟶ B') (V : S.Opens) (a : A.val.obj (op V)) (b : B.val.obj (op V)) :
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((S.toRingedSpace)).presheaf, ((S.toRingedSpace)).IsSheaf⟩)).map
        ((φ, ψ) : (_, _) ⟶ (_, _)))).val.app (op V)
        (tensorSheafPure S A B V (a ⊗ₜ[S.presheaf.obj (op V)] b)) =
      tensorSheafPure S A' B' V
        (φ.val.app (op V) a ⊗ₜ[S.presheaf.obj (op V)] ψ.val.app (op V) b) :=
  tensorSheafMap_app_toTensorSheafSection S.toRingedSpace A B A' B' φ ψ V a b

/-- A morphism of modules applied to equal local sections. -/
theorem val_app_congr {S : Scheme.{u}} {A B : S.Modules} (φ : A ⟶ B) (V : S.Opens)
    {x y : A.val.obj (op V)} (h : x = y) :
    φ.val.app (op V) x = φ.val.app (op V) y :=
  congrArg (φ.val.app (op V)) h

/-- The pure tensor of two local sections depends only on the two sections. -/
theorem tensorSheafPure_congr {S : Scheme.{u}} (A B : S.Modules) (V : S.Opens)
    {a a' : A.val.obj (op V)} {b b' : B.val.obj (op V)} (ha : a = a') (hb : b = b') :
    tensorSheafPure S A B V (a ⊗ₜ[S.presheaf.obj (op V)] b) =
      tensorSheafPure S A B V (a' ⊗ₜ[S.presheaf.obj (op V)] b') := by
  rw [ha, hb]

/-- **Extensionality for morphisms into a dual module, at the terminal object of each slice
site.**  Two morphisms `F ⟶ G^∨` whose local functionals agree on the local sections of `G` over
the same open are equal: a section of `G^∨` over an open is determined by its values at the
terminal object of the slice sites over all smaller opens, which the restrictions of the section
reach. -/
theorem hom_ext_dualSheaf_of_terminal {S : Scheme.{u}} {F G : S.Modules} {j k : F ⟶ dualSheaf G}
    (h : ∀ (U : S.Opens) (x : F.val.obj (op U)) (y : G.val.obj (op U)),
      dualPairing G (Scheme.Modules.Hom.app j U x) (Over.mk (𝟙 U)) y =
        dualPairing G (Scheme.Modules.Hom.app k U x) (Over.mk (𝟙 U)) y) :
    j = k := by
  refine hom_ext_dualSheaf (fun U x V y => ?_)
  have hj : Scheme.Modules.Hom.app j V.left (F.presheaf.map (homOfLE (leOfHom V.hom)).op x) =
      (dualSheaf G).presheaf.map (homOfLE (leOfHom V.hom)).op
        (Scheme.Modules.Hom.app j U x) :=
    PresheafOfModules.naturality_apply j.val (homOfLE (leOfHom V.hom)).op x
  have hk : Scheme.Modules.Hom.app k V.left (F.presheaf.map (homOfLE (leOfHom V.hom)).op x) =
      (dualSheaf G).presheaf.map (homOfLE (leOfHom V.hom)).op
        (Scheme.Modules.Hom.app k U x) :=
    PresheafOfModules.naturality_apply k.val (homOfLE (leOfHom V.hom)).op x
  refine (Stacks.AlgebraicGeometry.ReflexiveModules.dualPairing_terminal G
      (Scheme.Modules.Hom.app j U x) V y).symm.trans ?_
  refine Eq.trans ?_ (Stacks.AlgebraicGeometry.ReflexiveModules.dualPairing_terminal G
      (Scheme.Modules.Hom.app k U x) V y)
  rw [← hj, ← hk]
  exact h V.left _ y

/-- **Extensionality for morphisms out of a tensor product of two pullbacks along one
morphism.**  Two such agree as soon as they agree on the pure tensors of the canonical images of
local sections over a common open: an arbitrary local section of a pullback lies, on a covering
sieve, in the span of restricted canonical images, and two canonical images over two opens
restrict to canonical images over their intersection. -/
theorem tensor_hom_ext_of_pullbackUnit {Z S : Scheme.{u}} (f : Z ⟶ S) (A B : S.Modules)
    {C : Z.Modules}
    {u v : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((Z.toRingedSpace)).presheaf, ((Z.toRingedSpace)).IsSheaf⟩).obj
          (((modulePullback f.toLRSHom.toShHom).obj A))).obj
          (((modulePullback f.toLRSHom.toShHom).obj B))) ⟶ C}
    (h : ∀ (U : S.Opens) (a : A.val.obj (op U)) (b : B.val.obj (op U)),
      u.val.app (op (f ⁻¹ᵁ U)) (tensorSheafPure Z
          ((modulePullback f.toLRSHom.toShHom).obj A)
          ((modulePullback f.toLRSHom.toShHom).obj B) (f ⁻¹ᵁ U)
          (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app A).val.app
              (op U) a ⊗ₜ[Z.presheaf.obj (op (f ⁻¹ᵁ U))]
            ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app B).val.app
              (op U) b)) =
        v.val.app (op (f ⁻¹ᵁ U)) (tensorSheafPure Z
          ((modulePullback f.toLRSHom.toShHom).obj A)
          ((modulePullback f.toLRSHom.toShHom).obj B) (f ⁻¹ᵁ U)
          (((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app A).val.app
              (op U) a ⊗ₜ[Z.presheaf.obj (op (f ⁻¹ᵁ U))]
            ((modulePullbackPushforwardAdjunction f.toLRSHom.toShHom).unit.app B).val.app
              (op U) b))) :
    u = v := by
  refine tensor_hom_ext_of_unitSections f.toLRSHom.toShHom f.toLRSHom.toShHom A B
    (fun U x y hx hy => ?_)
  obtain ⟨V₁, g₁, s, rfl⟩ := hx
  obtain ⟨V₂, g₂, m, rfl⟩ := hy
  have hle : U.unop ≤ (Opens.map f.base).obj (V₁.unop ⊓ V₂.unop) := fun z hz =>
    ⟨leOfHom g₁.unop hz, leOfHom g₂.unop hz⟩
  let V₀ : (Opens S.carrier)ᵒᵖ := op (V₁.unop ⊓ V₂.unop)
  let i : (opensMap f.toLRSHom.toShHom).op.obj V₀ ⟶ U := (homOfLE hle).op
  let h₁ : V₁ ⟶ V₀ := (homOfLE (inf_le_left : V₁.unop ⊓ V₂.unop ≤ V₁.unop)).op
  let h₂ : V₂ ⟶ V₀ := (homOfLE (inf_le_right : V₁.unop ⊓ V₂.unop ≤ V₂.unop)).op
  have key : ∀ (M : S.Modules) (V' : (Opens S.carrier)ᵒᵖ) (k : V' ⟶ V₀)
      (g' : (opensMap f.toLRSHom.toShHom).op.obj V' ⟶ U) (x : M.val.obj V'),
      ((modulePullback f.toLRSHom.toShHom).obj M).val.map g'
          (pullbackUnitSection f.toLRSHom.toShHom M V' x) =
        ((modulePullback f.toLRSHom.toShHom).obj M).val.map i
          (pullbackUnitSection f.toLRSHom.toShHom M V₀ (M.val.map k x)) := by
    intro M V' k g' x
    rw [Subsingleton.elim g' ((opensMap f.toLRSHom.toShHom).op.map k ≫ i),
      PresheafOfModules.map_comp_apply]
    exact congrArg _ (pullbackUnitSection_naturality f.toLRSHom.toShHom M k x).symm
  rw [key A V₁ h₁ g₁ s, key B V₂ h₂ g₂ m]
  exact (tensorEvalMap_restrict u i _ _).symm.trans
    ((congrArg (fun z => C.val.map i z)
        (h V₀.unop (A.val.map h₁ s) (B.val.map h₂ m))).trans
      (tensorEvalMap_restrict v i _ _))

/-! ### The compatibility -/

/-- **The pulled-back evaluation pairing of a composite.**  The pairing
`(t ≫ g)^*(N^∨) ⊗ (t ≫ g)^*N ⟶ 𝒪_W` obtained by pulling back the evaluation pairing of `N`
along `t ≫ g` is the pairing `t^*((g^*N)^∨) ⊗ t^*(g^*N) ⟶ 𝒪_W` of the second factor, precomposed
with the pullback-composition comparison of [Stacks Project, Tag 0097] and with the dual
base-change map of `g` pulled back along `t`. -/
theorem pullbackEvaluation_comp (t : W ⟶ Y) (g : Y ⟶ X) (N : X.Modules) :
    pullbackEvaluation (t ≫ g) N =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullbackComp t g).inv.app (dualSheaf N) ≫
            (Scheme.Modules.pullback t).map (pullbackDualMap g N)),
          ((Scheme.Modules.pullbackComp t g).inv.app N)) : (_, _) ⟶ (_, _))) ≫
        pullbackEvaluation t ((Scheme.Modules.pullback g).obj N) := by
  refine tensor_hom_ext_of_pullbackUnit (t ≫ g) (dualSheaf N) N (fun U s m => ?_)
  have hA : ((Scheme.Modules.pullbackComp t g).inv.app (dualSheaf N) ≫
        (Scheme.Modules.pullback t).map (pullbackDualMap g N)).val.app
        (op ((t ≫ g) ⁻¹ᵁ U))
        (((modulePullbackPushforwardAdjunction (t ≫ g).toLRSHom.toShHom).unit.app
          (dualSheaf N)).val.app (op U) s) =
      ((modulePullbackPushforwardAdjunction t.toLRSHom.toShHom).unit.app
          (dualSheaf ((modulePullback g.toLRSHom.toShHom).obj N))).val.app (op (g ⁻¹ᵁ U))
        ((pullbackDualMap g N).val.app (op (g ⁻¹ᵁ U))
          (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
            (dualSheaf N)).val.app (op U) s)) :=
    (comp_val_app _ _ _ _).trans
      ((congrArg (fun z => ((Scheme.Modules.pullback t).map
            (pullbackDualMap g N)).val.app (op ((t ≫ g) ⁻¹ᵁ U)) z)
          (Scheme.Modules.pullbackComp_inv_unit t g (dualSheaf N) U s)).trans
        (pullback_map_unit_app t (pullbackDualMap g N) (g ⁻¹ᵁ U) _))
  have hB : ((Scheme.Modules.pullbackComp t g).inv.app N).val.app (op ((t ≫ g) ⁻¹ᵁ U))
        (((modulePullbackPushforwardAdjunction (t ≫ g).toLRSHom.toShHom).unit.app
          N).val.app (op U) m) =
      ((modulePullbackPushforwardAdjunction t.toLRSHom.toShHom).unit.app
          ((modulePullback g.toLRSHom.toShHom).obj N)).val.app (op (g ⁻¹ᵁ U))
        (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app N).val.app
          (op U) m) :=
    Scheme.Modules.pullbackComp_inv_unit t g N U m
  have hinner : (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullbackComp t g).inv.app (dualSheaf N) ≫
            (Scheme.Modules.pullback t).map (pullbackDualMap g N)),
          ((Scheme.Modules.pullbackComp t g).inv.app N)) : (_, _) ⟶ (_, _)))).val.app
        (op ((t ≫ g) ⁻¹ᵁ U))
        (tensorSheafPure W ((modulePullback (t ≫ g).toLRSHom.toShHom).obj (dualSheaf N))
          ((modulePullback (t ≫ g).toLRSHom.toShHom).obj N) ((t ≫ g) ⁻¹ᵁ U)
          (((modulePullbackPushforwardAdjunction (t ≫ g).toLRSHom.toShHom).unit.app
              (dualSheaf N)).val.app (op U) s ⊗ₜ[W.presheaf.obj (op ((t ≫ g) ⁻¹ᵁ U))]
            ((modulePullbackPushforwardAdjunction (t ≫ g).toLRSHom.toShHom).unit.app
              N).val.app (op U) m)) =
      tensorSheafPure W
          ((modulePullback t.toLRSHom.toShHom).obj
            (dualSheaf ((modulePullback g.toLRSHom.toShHom).obj N)))
          ((modulePullback t.toLRSHom.toShHom).obj
            ((modulePullback g.toLRSHom.toShHom).obj N)) ((t ≫ g) ⁻¹ᵁ U)
        (((modulePullbackPushforwardAdjunction t.toLRSHom.toShHom).unit.app
              (dualSheaf ((modulePullback g.toLRSHom.toShHom).obj N))).val.app
            (op (g ⁻¹ᵁ U))
            ((pullbackDualMap g N).val.app (op (g ⁻¹ᵁ U))
              (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app
                (dualSheaf N)).val.app (op U) s)) ⊗ₜ[W.presheaf.obj (op ((t ≫ g) ⁻¹ᵁ U))]
          ((modulePullbackPushforwardAdjunction t.toLRSHom.toShHom).unit.app
              ((modulePullback g.toLRSHom.toShHom).obj N)).val.app (op (g ⁻¹ᵁ U))
            (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app N).val.app
              (op U) m)) :=
    (tensorSheafMap_tensorSheafPure _ _ _ _ _).trans (tensorSheafPure_congr _ _ _ hA hB)
  refine (pullbackEvaluation_unit_tmul (t ≫ g) N U s m).trans ?_
  refine Eq.symm ((comp_val_app _ _ _ _).trans ?_)
  refine (val_app_congr _ _ hinner).trans ?_
  refine (pullbackEvaluation_unit_tmul t ((modulePullback g.toLRSHom.toShHom).obj N)
    (g ⁻¹ᵁ U) _ _).trans ?_
  exact congrArg (fun z => (t.app (g ⁻¹ᵁ U)).hom z)
    ((pullbackDualMap_eval g N (g ⁻¹ᵁ U) _ _).trans
      (pullbackEvaluation_unit_tmul g N U s m))

/-- **The dual base-change map is compatible with composition of morphisms of schemes.**  For
`t : W ⟶ Y`, `g : Y ⟶ X` and a module `N` on `X`, the dual base-change map
`(t ≫ g)^*(N^∨) ⟶ ((t ≫ g)^* N)^∨` of [Stacks Project, Tag 0GMX] agrees — modulo the
pullback-composition comparison `AlgebraicGeometry.Scheme.Modules.pullbackComp` of
[Stacks Project, Tag 0097] on the source and on the module being dualised — with the dual
base-change map of `g` pulled back along `t`, followed by the dual base-change map of `t`. -/
theorem pullbackDualMap_comp (t : W ⟶ Y) (g : Y ⟶ X) (N : X.Modules) :
    (Scheme.Modules.pullbackComp t g).hom.app (dualSheaf N) ≫
        pullbackDualMap (t ≫ g) N ≫
          dualMap ((Scheme.Modules.pullbackComp t g).hom.app N) =
      (Scheme.Modules.pullback t).map (pullbackDualMap g N) ≫
        pullbackDualMap t ((Scheme.Modules.pullback g).obj N) := by
  refine hom_ext_dualSheaf_of_terminal (fun V a b => ?_)
  have hcb : ((Scheme.Modules.pullbackComp t g).inv.app N).val.app (op V)
      (((Scheme.Modules.pullbackComp t g).hom.app N).val.app (op V) b) = b :=
    iso_inv_val_app_hom_val_app ((Scheme.Modules.pullbackComp t g).app N) V b
  have hca : ((Scheme.Modules.pullbackComp t g).inv.app (dualSheaf N) ≫
        (Scheme.Modules.pullback t).map (pullbackDualMap g N)).val.app (op V)
        (((Scheme.Modules.pullbackComp t g).hom.app (dualSheaf N)).val.app (op V) a) =
      ((Scheme.Modules.pullback t).map (pullbackDualMap g N)).val.app (op V) a :=
    (comp_val_app _ _ _ _).trans
      (congrArg (fun z => ((Scheme.Modules.pullback t).map
          (pullbackDualMap g N)).val.app (op V) z)
        (iso_inv_val_app_hom_val_app ((Scheme.Modules.pullbackComp t g).app (dualSheaf N))
          V a))
  have hstep : (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((W.toRingedSpace)).presheaf, ((W.toRingedSpace)).IsSheaf⟩)).map
        ((((Scheme.Modules.pullbackComp t g).inv.app (dualSheaf N) ≫
            (Scheme.Modules.pullback t).map (pullbackDualMap g N)),
          ((Scheme.Modules.pullbackComp t g).inv.app N)) : (_, _) ⟶ (_, _)))).val.app
        (op V)
        (tensorSheafPure W ((modulePullback (t ≫ g).toLRSHom.toShHom).obj (dualSheaf N))
          ((modulePullback (t ≫ g).toLRSHom.toShHom).obj N) V
          (((Scheme.Modules.pullbackComp t g).hom.app (dualSheaf N)).val.app (op V) a
            ⊗ₜ[W.presheaf.obj (op V)]
            ((Scheme.Modules.pullbackComp t g).hom.app N).val.app (op V) b)) =
      tensorSheafPure W
          ((modulePullback t.toLRSHom.toShHom).obj
            (dualSheaf ((modulePullback g.toLRSHom.toShHom).obj N)))
          ((modulePullback t.toLRSHom.toShHom).obj
            ((modulePullback g.toLRSHom.toShHom).obj N)) V
        (((Scheme.Modules.pullback t).map (pullbackDualMap g N)).val.app (op V) a
          ⊗ₜ[W.presheaf.obj (op V)] b) :=
    (tensorSheafMap_tensorSheafPure _ _ _ _ _).trans (tensorSheafPure_congr _ _ _ hca hcb)
  have hL : (((pullbackDualMap (t ≫ g) N).val.app (op V)
            (((Scheme.Modules.pullbackComp t g).hom.app (dualSheaf N)).val.app (op V) a)).app
          (op (Over.mk (𝟙 V)))).hom
        (((Scheme.Modules.pullbackComp t g).hom.app N).val.app (op V) b) =
      (pullbackEvaluation t ((modulePullback g.toLRSHom.toShHom).obj N)).val.app (op V)
        (tensorSheafPure W
          ((modulePullback t.toLRSHom.toShHom).obj
            (dualSheaf ((modulePullback g.toLRSHom.toShHom).obj N)))
          ((modulePullback t.toLRSHom.toShHom).obj
            ((modulePullback g.toLRSHom.toShHom).obj N)) V
          (((Scheme.Modules.pullback t).map (pullbackDualMap g N)).val.app (op V) a
            ⊗ₜ[W.presheaf.obj (op V)] b)) := by
    refine (pullbackDualMap_eval (t ≫ g) N V _ _).trans ?_
    rw [pullbackEvaluation_comp t g N]
    exact (comp_val_app _ _ _ _).trans (val_app_congr _ _ hstep)
  exact hL.trans (pullbackDualMap_eval t ((modulePullback g.toLRSHom.toShHom).obj N) V _ b).symm

end

end Stacks.Chow

end
