module

public import StacksFrontier.Deformation.ToposThickening.TrivialExtension
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.TensorSheafSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# The trivial extension `ℱ ⊕ (I ⊗_O ℱ)` is the extension of scalars of `ℱ` along the splitting

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I`, and let `π` be a trivialization of it, with splitting `π^♯ : O ⟶ O'` of the structure
map `q : O' ⟶ O`, so that `O' = O ⊕ I`. For an `O`-module `ℱ`, the trivial extension
`F'_{1,triv} = ℱ ⊕ (I ⊗_O ℱ)` of Stacks 08MI, with action
`r · (m, k) = (q r · m, q r · k + d r ⊗ m)`, is `O' ⊗_{π^♯, O} ℱ`: an `O'`-linear map out of it is
the same as an `O`-linear map out of `ℱ` into the restriction of scalars along `π^♯`. So it is the
value at `ℱ` of any left adjoint of restriction of scalars along `π^♯`.

## Main definitions

* `Deformation.ToposThickening.trivialExtensionIncl`: the `O`-linear inclusion `m ↦ (m, 0)` of
  `ℱ` into the trivial extension read along the splitting.
* `Deformation.ToposThickening.trivialExtensionDesc`: the `O'`-linear map out of the trivial
  extension extending an `O`-linear map `g` out of `ℱ`, `(m, k) ↦ g(m) + τ(k)` with
  `τ(a ⊗ m) = a · g(m)`.
* `Deformation.ToposThickening.trivialExtensionIsoOfAdjunction`: for a left adjoint `L` of
  restriction of scalars along the splitting, `L ℱ ≅ ℱ ⊕ (I ⊗_O ℱ)`.

## Main results

* `Deformation.ToposThickening.trivialExtension_hom_ext`: an `O'`-linear map out of the trivial
  extension is determined by its restriction to `ℱ`.
* `Deformation.ToposThickening.trivialExtensionIncl_comp_desc`: the extension property.

## References

* [Stacks Project, Tag 08MI](https://stacks.math.columbia.edu/tag/08MI)
* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {i : RingedToposHom X Y}

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

section Incl

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  (hi : FirstOrderThickening i) (π : Trivialization i)
  (F K : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))
  (c : ((Stacks.SheafOfModules.Tensor.sheafTensor
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K)

/-- **The inclusion `m ↦ (m, 0)` of `ℱ` into the trivial extension**, which is `O`-linear for the
action of `O` through the splitting `π^♯`: the derivation kills the image of the splitting. -/
noncomputable def trivialExtensionIncl :
    F ⟶ (splitRestriction i hi π).obj (trivialExtensionModule hi π F K c) :=
  ⟨{ app := fun U => ModuleCat.ofHom
        (X := F.val.obj U)
        (Y := ((splitRestriction i hi π).obj (trivialExtensionModule hi π F K c)).val.obj U) {
          toFun := fun m => (m, 0)
          map_add' := fun a b => Prod.ext rfl (add_zero 0).symm
          map_smul' := fun a m => by
            refine Eq.trans ?_
              (trivialExtensionModule_smul hi π F K c U (splitApp hi π U a) (m, 0)).symm
            refine Prod.ext ?_ ?_
            · change a • m = structureApp i U (splitApp hi π U a) • m
              rw [structureApp_splitApp]
            · change (0 : K.val.obj U) = structureApp i U (splitApp hi π U a) • (0 : K.val.obj U) +
                extensionPairing hi F K c U (trivializationDerivation hi π U (splitApp hi π U a)) m
              rw [trivializationDerivation_splitApp, extensionPairing_zero_left, smul_zero,
                add_zero] }
     naturality := fun {U V} f => by
       ext m
       exact Prod.ext rfl (K.val.map f).hom.map_zero.symm }⟩

/-- The inclusion on sections. -/
theorem trivialExtensionIncl_val_app (U : Y.Cᵒᵖ) (m : F.val.obj U) :
    (trivialExtensionIncl hi π F K c).val.app U m =
      (show (trivialExtensionModule hi π F K c).val.obj U from (m, 0)) := rfl

/-- A section `a` of the ideal acts on `(m, 0)` by `(0, c(a ⊗ m))`. -/
theorem idealSection_smul_incl (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (m : F.val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from idealSection hi U a) •
        (show (trivialExtensionModule hi π F K c).val.obj U from (m, 0)) =
      (show (trivialExtensionModule hi π F K c).val.obj U from
        (0, extensionPairing hi F K c U a m)) := by
  refine (trivialExtensionModule_smul hi π F K c U (idealSection hi U a) (m, 0)).trans ?_
  refine Prod.ext ?_ ?_
  · change structureApp i U (idealSection hi U a) • m = 0
    rw [structureApp_idealSection, zero_smul]
  · change structureApp i U (idealSection hi U a) • (0 : K.val.obj U) +
      extensionPairing hi F K c U (trivializationDerivation hi π U (idealSection hi U a)) m =
        extensionPairing hi F K c U a m
    rw [smul_zero, zero_add, trivializationDerivation_idealSection]

end Incl

section Universal

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  (hi : FirstOrderThickening i) (π : Trivialization i)
  (F : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)))

/-- The trivial extension `ℱ ⊕ (I ⊗_O ℱ)` of Stacks 08MI attached to the identity of
`I ⊗_O ℱ`. -/
noncomputable abbrev idealTrivialExtensionModule :
    SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  trivialExtensionModule hi π F (idealTensorModule hi F) (𝟙 _)

/-- **An `O'`-linear map out of the trivial extension is determined by its restriction to `ℱ`**:
it is determined on `(m, 0)`, and on `(0, a ⊗ m) = a · (m, 0)` by `O'`-linearity. -/
theorem trivialExtension_hom_ext
    {N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {φ ψ : (idealTrivialExtensionModule hi π F) ⟶ N}
    (h : trivialExtensionIncl hi π F _ (𝟙 _) ≫ (splitRestriction i hi π).map φ =
      trivialExtensionIncl hi π F _ (𝟙 _) ≫ (splitRestriction i hi π).map ψ) : φ = ψ := by
  have h₁ : ∀ (U : Y.Cᵒᵖ) (m : F.val.obj U),
      φ.val.app U (show (idealTrivialExtensionModule hi π F).val.obj U from (m, 0)) =
      ψ.val.app U (show (idealTrivialExtensionModule hi π F).val.obj U from (m, 0)) :=
    fun U m => congrArg (fun g => g.val.app U m) h
  have h₂ : trivialExtensionInr hi π F _ (𝟙 _) ≫ φ = trivialExtensionInr hi π F _ (𝟙 _) ≫ ψ := by
    refine tensorSheaf_restrict_hom_ext ((pushforwardCommRingFunctor i.toToposHom).obj X.O)
      ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp) fun U a m => ?_
    have e := idealSection_smul_incl hi π F _ (𝟙 _) U a m
    change φ.val.app U (show (idealTrivialExtensionModule hi π F).val.obj U from
        (0, extensionPairing hi F _ (𝟙 _) U a m)) =
      ψ.val.app U (show (idealTrivialExtensionModule hi π F).val.obj U from
        (0, extensionPairing hi F _ (𝟙 _) U a m))
    rw [← e, (φ.val.app U).hom.map_smul, (ψ.val.app U).hom.map_smul, h₁]
  ext U z
  have hz : z = (show (idealTrivialExtensionModule hi π F).val.obj U from (z.1, 0)) +
      (trivialExtensionInr hi π F _ (𝟙 _)).val.app U z.2 :=
    Prod.ext (add_zero _).symm (zero_add _).symm
  rw [hz, map_add, map_add, h₁]
  exact congrArg (fun k => ψ.val.app U
      (show (idealTrivialExtensionModule hi π F).val.obj U from (z.1, 0)) + k)
    (congrArg (fun g => g.val.app U z.2) h₂)

variable {N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Y.J AddCommGrpCat] in
/-- The splitting carries the action of `O` on the ideal to multiplication in `O'`. -/
theorem idealSection_smul_split (U : Y.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U) (a : hi.I.val.obj U) :
    idealSection hi U (r • a) = splitApp hi π U r * idealSection hi U a :=
  (congrArg (fun x => idealSection hi U (x • a)) (structureApp_splitApp hi π U r)).symm.trans
    (idealSection_smul hi U _ a)

/-- The pairing `a ⊗ m ↦ a · g(m)` on sections. -/
noncomputable def trivialExtensionDescPairing (g : F ⟶ (splitRestriction i hi π).obj N)
    (U : Y.Cᵒᵖ) :
    hi.I.val.obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U]
      F.val.obj U →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U]
        ((splitRestriction i hi π).obj N).val.obj U :=
  LinearMap.mk₂ _ (fun a m => (show ((splitRestriction i hi π).obj N).val.obj U from
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from idealSection hi U a) •
        (show N.val.obj U from g.val.app U m)))
    (fun a b m => (congrArg (· • (show N.val.obj U from g.val.app U m))
      (idealSection_add hi U a b)).trans (add_smul _ _ _))
    (fun r a m => (congrArg (· • (show N.val.obj U from g.val.app U m))
      (idealSection_smul_split hi π U r a)).trans (mul_smul _ _ _))
    (fun a m n => (congrArg (fun x => (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
      from idealSection hi U a) • (show N.val.obj U from x)) (map_add (g.val.app U).hom m n)).trans
        (smul_add _ _ _))
    (fun r a m => (congrArg (fun x => (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
      from idealSection hi U a) • (show N.val.obj U from x)) ((g.val.app U).hom.map_smul r m)).trans
        (by
          change (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
              from idealSection hi U a) •
                (splitApp hi π U r • (show N.val.obj U from g.val.app U m)) =
            splitApp hi π U r • ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U
              from idealSection hi U a) • (show N.val.obj U from g.val.app U m))
          rw [smul_smul, smul_smul, mul_comm]))

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify Y.J AddCommGrpCat] in
/-- The pairing `trivialExtensionDescPairing` sends `(a, m)` to `a · g(m)`. -/
theorem trivialExtensionDescPairing_apply (g : F ⟶ (splitRestriction i hi π).obj N) (U : Y.Cᵒᵖ)
    (a : hi.I.val.obj U) (m : F.val.obj U) :
    trivialExtensionDescPairing hi π F g U a m =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from idealSection hi U a) •
        (show N.val.obj U from g.val.app U m) := rfl

/-- **The map `τ : I ⊗_O ℱ ⟶ N`, `a ⊗ m ↦ a · g(m)`**, `O`-linear for the action of `O` on `N`
through the splitting. -/
noncomputable def trivialExtensionDescKernel (g : F ⟶ (splitRestriction i hi π).obj N) :
    { l : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I ⟶
          (splitRestriction i hi π).obj N //
      ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (m : F.val.obj U),
        l.val.app U (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
          (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] m)) =
        trivialExtensionDescPairing hi π F g U a m } :=
  tensorSheafLift ((pushforwardCommRingFunctor i.toToposHom).obj X.O)
    (trivialExtensionDescPairing hi π F g) fun {U V} f a m => by
      change (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj V from
          idealSection hi V (hi.I.val.map f a)) • (show N.val.obj V from
            g.val.app V (F.val.map f m)) = N.val.map f ((show
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from idealSection hi U a) •
                (show N.val.obj U from g.val.app U m))
      rw [N.val.map_smul, idealSection_naturality]
      exact congrArg (fun x => _ • (show N.val.obj V from x))
        (PresheafOfModules.naturality_apply g.val f m)

/-- **The ideal kills the image of `τ`**: `τ` is a sum, locally, of products `a · g(m)` with `a` in
the square-zero ideal. -/
theorem idealSection_smul_descKernel (g : F ⟶ (splitRestriction i hi π).obj N) (U : Y.Cᵒᵖ)
    (b : hi.I.val.obj U)
    (k : (((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I).val.obj U) :
    (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from idealSection hi U b) •
      (show N.val.obj U from (trivialExtensionDescKernel hi π F g).1.val.app U k) = 0 := by
  let p := (PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)).unit.app
    (PresheafOfModules.tensorObj hi.I.val F.val)
  let τ := (trivialExtensionDescKernel hi π F g).1
  have : Presheaf.IsLocallySurjective Y.J ((PresheafOfModules.toPresheaf _).map p) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app (J := Y.J)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj)
      (PresheafOfModules.tensorObj hi.I.val F.val)
  apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem Y.J
    ((PresheafOfModules.toPresheaf _).map p) k)
  rintro V t ⟨x, hx⟩
  change p.app (Opposite.op V) x = _ at hx
  change N.val.map t.op ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
      idealSection hi U b) • (show N.val.obj U from τ.val.app U k)) = N.val.map t.op 0
  rw [N.val.map_smul, map_zero, ← idealSection_naturality]
  let r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V) :=
    idealSection hi (Opposite.op V) (hi.I.val.map t.op b)
  let μ : N.val.obj (Opposite.op V) →+ N.val.obj (Opposite.op V) :=
    DistribSMul.toAddMonoidHom _ r
  have hτ : N.val.map t.op (τ.val.app U k) = τ.val.app (Opposite.op V) (p.app (Opposite.op V) x) :=
    (PresheafOfModules.naturality_apply τ.val t.op k).symm.trans
      (congrArg (τ.val.app (Opposite.op V)) hx.symm)
  change μ (N.val.map t.op (τ.val.app U k)) = 0
  rw [hτ]
  clear hτ hx
  let φ : (hi.I.val.obj (Opposite.op V) ⊗[((pushforwardCommRingFunctor i.toToposHom).obj
      X.O).obj.obj (Opposite.op V)] F.val.obj (Opposite.op V)) →+ N.val.obj (Opposite.op V) :=
    μ.comp ((τ.val.app (Opposite.op V)).hom.toAddMonoidHom.comp
      (p.app (Opposite.op V)).hom.toAddMonoidHom)
  change hi.I.val.obj (Opposite.op V) ⊗[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj
    (Opposite.op V)] F.val.obj (Opposite.op V) at x
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero φ
  | tmul a m =>
    refine (congrArg μ ((trivialExtensionDescKernel hi π F g).2 (Opposite.op V) a m)).trans ?_
    change r • ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V) from
      idealSection hi (Opposite.op V) a) • (show N.val.obj (Opposite.op V) from
        g.val.app (Opposite.op V) m)) = 0
    rw [smul_smul, idealSection_mul_idealSection, zero_smul]
  | add x y hx hy => exact (map_add φ x y).trans ((congrArg₂ (· + ·) hx hy).trans (add_zero 0))

/-- **The `O'`-linear map out of the trivial extension extending `g`**: `(m, k) ↦ g(m) + τ(k)`.
It is `O'`-linear because `r · (m, k) = (q r · m, q r · k + d r ⊗ m)` with `r = π^♯(q r) + d r`,
and the ideal kills the image of `τ`. -/
noncomputable def trivialExtensionDesc (g : F ⟶ (splitRestriction i hi π).obj N) :
    idealTrivialExtensionModule hi π F ⟶ N :=
  ⟨{ app := fun U => ModuleCat.ofHom
        (X := (idealTrivialExtensionModule hi π F).val.obj U) (Y := N.val.obj U) {
          toFun := fun z => (show N.val.obj U from g.val.app U z.1) +
            (show N.val.obj U from (trivialExtensionDescKernel hi π F g).1.val.app U z.2)
          map_add' := fun z z' => by
            change (show N.val.obj U from g.val.app U (z.1 + z'.1)) +
                (show N.val.obj U from (trivialExtensionDescKernel hi π F g).1.val.app U
                  (z.2 + z'.2)) = _
            rw [map_add, map_add]
            exact add_add_add_comm _ _ _ _
          map_smul' := fun r z => by
            let q := structureApp i U r
            let G : F.val.obj U → N.val.obj U := fun m => g.val.app U m
            let T : (((Stacks.SheafOfModules.Tensor.sheafTensor
                ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
                  hi.I).val.obj U →
                N.val.obj U := fun k => (trivialExtensionDescKernel hi π F g).1.val.app U k
            have hfst : (r • z).1 = q • z.1 := trivialExtensionModule_smul_fst hi π F _ _ U r z
            have hsnd : (r • z).2 = q • z.2 +
                extensionPairing hi F _ (𝟙 _) U (trivializationDerivation hi π U r) z.1 :=
              trivialExtensionModule_smul_snd hi π F _ _ U r z
            have hd : idealSection hi U (trivializationDerivation hi π U r) =
                r - splitApp hi π U q := idealSection_trivializationDerivation hi π U r
            have hg : G (q • z.1) = splitApp hi π U q • G z.1 :=
              (g.val.app U).hom.map_smul q z.1
            have hTa : ∀ x y, T (x + y) = T x + T y := fun x y =>
              map_add ((trivialExtensionDescKernel hi π F g).1.val.app U).hom x y
            have hτ : T (q • z.2) = splitApp hi π U q • T z.2 :=
              ((trivialExtensionDescKernel hi π F g).1.val.app U).hom.map_smul q z.2
            have hτd : T (extensionPairing hi F _ (𝟙 _) U (trivializationDerivation hi π U r) z.1) =
                (r - splitApp hi π U q) • G z.1 :=
              ((trivialExtensionDescKernel hi π F g).2 U _ z.1).trans
                (congrArg (· • G z.1) hd)
            have hr : r • T z.2 = splitApp hi π U q • T z.2 := by
              rw [← sub_eq_zero, ← sub_smul, ← hd]
              exact idealSection_smul_descKernel hi π F g U _ z.2
            change G (r • z).1 + T (r • z).2 = r • (G z.1 + T z.2)
            rw [hfst, hsnd, hTa, hg, hτ, hτd, smul_add, hr, sub_smul]
            abel }
     naturality := fun {U V} f => by
       ext z
       change (show N.val.obj V from g.val.app V ((F.val.map f) z.1)) +
           (show N.val.obj V from (trivialExtensionDescKernel hi π F g).1.val.app V
             ((((Stacks.SheafOfModules.Tensor.sheafTensor
               ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj
                 hi.I).val.map f z.2)) =
         N.val.map f ((show N.val.obj U from g.val.app U z.1) +
           (show N.val.obj U from (trivialExtensionDescKernel hi π F g).1.val.app U z.2))
       rw [map_add]
       exact congrArg₂ (· + ·) (PresheafOfModules.naturality_apply g.val f z.1)
         (PresheafOfModules.naturality_apply (trivialExtensionDescKernel hi π F g).1.val f z.2) }⟩

/-- **The extension property**: `trivialExtensionDesc` restricts to `g` on `ℱ`. -/
theorem trivialExtensionIncl_comp_desc (g : F ⟶ (splitRestriction i hi π).obj N) :
    trivialExtensionIncl hi π F _ (𝟙 _) ≫
        (splitRestriction i hi π).map (trivialExtensionDesc hi π F g) = g := by
  ext U m
  let T : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).flip.obj F).obj hi.I).val.obj U →
      N.val.obj U := fun k => (trivialExtensionDescKernel hi π F g).1.val.app U k
  let G : F.val.obj U → N.val.obj U := fun m => g.val.app U m
  change G m + T 0 = G m
  exact (congrArg (G m + ·)
      (map_zero ((trivialExtensionDescKernel hi π F g).1.val.app U).hom)).trans
    (add_zero _)

/-- **`ℱ ⊕ (I ⊗_O ℱ)` is `O' ⊗_{π^♯, O} ℱ`**: for any left adjoint `L` of restriction of scalars
along the splitting `π^♯`, the map `L ℱ ⟶ ℱ ⊕ (I ⊗_O ℱ)` adjoint to `m ↦ (m, 0)` is an
isomorphism; its inverse is `trivialExtensionDesc` of the unit. -/
noncomputable def trivialExtensionIsoOfAdjunction
    {L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) ⥤
        SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (adj : L ⊣ splitRestriction i hi π) :
    L.obj F ≅ idealTrivialExtensionModule hi π F where
  hom := (adj.homEquiv _ _).symm (trivialExtensionIncl hi π F _ (𝟙 _))
  inv := trivialExtensionDesc hi π F (adj.unit.app F)
  hom_inv_id := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply, CategoryTheory.Functor.map_comp,
      ← Category.assoc, ← Adjunction.homEquiv_apply, Equiv.apply_symm_apply,
      trivialExtensionIncl_comp_desc, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    apply trivialExtension_hom_ext
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc, trivialExtensionIncl_comp_desc,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The identification `L ℱ ≅ ℱ ⊕ (I ⊗_O ℱ)` is the transpose of `m ↦ (m, 0)`. -/
theorem trivialExtensionIsoOfAdjunction_hom
    {L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) ⥤
        SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (adj : L ⊣ splitRestriction i hi π) :
    (trivialExtensionIsoOfAdjunction hi π F adj).hom =
      (adj.homEquiv _ _).symm (trivialExtensionIncl hi π F _ (𝟙 _)) := rfl

/-- The inclusion `ℱ ⟶ ℱ ⊕ (I ⊗_O ℱ)` followed by the projection is the identification of `ℱ`
with its restriction of scalars to `O'` and back along the splitting. -/
theorem trivialExtensionIncl_comp_fst :
    trivialExtensionIncl hi π F (idealTensorModule hi F) (𝟙 _) ≫
        (splitRestriction i hi π).map (trivialExtensionFst hi π F _ (𝟙 _)) =
      (splitRestrictionRestrictScalarsIso i hi π F).inv := by
  ext U m
  rfl

/-- **The projection `L ℱ ≅ ℱ ⊕ (I ⊗_O ℱ) ⟶ q^*ℱ` is the transpose of the identification
`ℱ = π^♯^* q^* ℱ`.** -/
theorem trivialExtensionIsoOfAdjunction_hom_comp_fst
    {L : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)) ⥤
        SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (adj : L ⊣ splitRestriction i hi π) :
    (trivialExtensionIsoOfAdjunction hi π F adj).hom ≫ trivialExtensionFst hi π F _ (𝟙 _) =
      (adj.homEquiv _ _).symm (splitRestrictionRestrictScalarsIso i hi π F).inv :=
  (adj.homEquiv_naturality_right_symm _ _).symm.trans
    (congrArg (adj.homEquiv _ _).symm (trivialExtensionIncl_comp_fst hi π F))

end Universal

end Deformation.ToposThickening

end
