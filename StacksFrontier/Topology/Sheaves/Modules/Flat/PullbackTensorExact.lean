module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.RingTheory.Flat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafFlatCover
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Pullback followed by tensoring with a module flat over the target is exact

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `F` be an `𝒪_X`-module
flat over `Y`, that is, one whose stalk at every `x` is flat over `𝒪_{Y, f x}`. Then the
functor

`Mod(𝒪_Y) ⟶ Mod(𝒪_X)`, `G ↦ f^*G ⊗_{𝒪_X} F`

is exact.

Exactness is checked on stalks. Writing `R = 𝒪_{Y, f x}`, `S = 𝒪_{X, x}`, `M = F_x` and
`N = G_{f x}`, the stalk of `f^*G ⊗_{𝒪_X} F` at `x` is

`(f^*G)_x ⊗_S M ≃ (S ⊗_R N) ⊗_S M ≃ M ⊗_S (S ⊗_R N) ≃ M ⊗_R N`,

naturally in `G`, by Stacks 0098 and Stacks 01CB; so the functor becomes `N ↦ M ⊗_R N` on
stalks, which is exact exactly because `M` is flat over `R`.

## Main definitions

* `Stacks.SheafOfModules.pullbackTensorFunctor`: the functor `G ↦ f^*G ⊗_{𝒪_X} F`.

## Main results

* `Stacks.SheafOfModules.pullbackTensorFunctor_exact`: that functor is exact when `F` is flat
  over `Y`.
* `Stacks.SheafOfModules.additive_pullbackTensorFunctor` and
  `Stacks.SheafOfModules.preservesZeroMorphisms_pullbackTensorFunctor`: it is additive, hence
  preserves zero morphisms, with no hypothesis on `F`.

## Implementation notes

The functor is the composite of the pullback `RingedSpaceModuleAdjunction.modulePullback` with
`Stacks.sheafTensorRight`, so no new tensor product or pullback is introduced; in particular
`(Stacks.sheafTensorRight X.sheaf F).obj P` is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf X P F` on the nose, which is what
lets the Stacks 01CB stalk comparison apply to it.

Every stalk statement is written at the Tag 01CB spelling of the module structure on a stalk,
because that is the one `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` and
`Stacks.RingedSpace.pullbackStalkEquiv` are stated over; the translation to Mathlib's
instance is already performed once and for all in `pullbackStalkEquiv`, and is not repeated
here.

The naturality of `Stacks.RingedSpace.pullbackStalkEquiv` in the module argument is proved
here from its germ characterisation, which is the only description of the pullback's sections
available: the pullback is an abstract left adjoint.

Exactness is Mathlib's `exactFunctor`, and the two halves are produced from
`Functor.PreservesHomology`, which `Functor.preservesHomology_of_map_exact` extracts from
exactness of the images of short complexes.

The route from the stalk formula to exactness is broken into one lemma per step
(`exact_stalkMapL`, `exact_lTensor_stalkMapL`, `exact_stalkMapL_tensorSheafMap`,
`stalkShortComplex_map_exact`, `map_exact_of_exact`), and the diagram chase itself is isolated
in `exact_of_addEquiv_ladder`, which speaks only of abelian groups and bare maps.  Carrying the
chase out directly on the stalks re-solves the unification
`(pullbackTensorFunctor f F).obj G ≟ tensorSheaf X (f^*G) F` at every step of the chase, which
is where the heartbeats went: `Stacks.sheafTensorRight` is defined by a tactic block with two
`let`s, so each of those unifications unfolds them again.  Stated as `pullbackTensorFunctor_obj`
and `pullbackTensorFunctor_map` the identification costs a single `rfl` apiece, and the chase
never sees it.

For the same reason the additivity of the composite is *applied* rather than searched for: the
two factors are typed over `Stacks.commRingSheafToRingSheaf X.sheaf` and over
`structureSheafRing X`, so the preadditive structure of `Mod(𝒪_X)` is
reached by two different routes and instance search, which works at `instances` transparency,
does not cross them.

## References

* [Stacks Project, Tag 0GMU](https://stacks.math.columbia.edu/tag/0GMU)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules

open Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (F : SheafOfModules.{u} (structureSheafRing X))

/-- The functor from `𝒪_Y`-modules to `𝒪_X`-modules which sends `G` to `f^*G ⊗_{𝒪_X} F`. -/
noncomputable def pullbackTensorFunctor :
    SheafOfModules.{u} (structureSheafRing Y) ⥤ SheafOfModules.{u} (structureSheafRing X) :=
  modulePullback f ⋙ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj F)

/-- `G ↦ f^*G ⊗_{𝒪_X} F` sends `G` to the Tag 01CB tensor product sheaf of `f^*G` and `F`. -/
private theorem pullbackTensorFunctor_obj (G : SheafOfModules.{u} (structureSheafRing Y)) :
    (pullbackTensorFunctor f F).obj G =
      ((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f G)).obj F := rfl

/-- `G ↦ f^*G ⊗_{𝒪_X} F` sends `φ` to the Tag 01CB tensor product of `f^*φ` with `𝟙 F`. -/
private theorem pullbackTensorFunctor_map {G G' : SheafOfModules.{u} (structureSheafRing Y)}
    (φ : G ⟶ G') :
    (pullbackTensorFunctor f F).map φ =
      (Functor.uncurry.obj (Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).map
          (X := (pullbackSheaf f G, F)) (Y := (pullbackSheaf f G', F))
          ((pullbackFunctor f).map φ, 𝟙 F) := by
  refine Eq.trans ?_ (Tensor.sheafTensor_uncurry_map.{u, u, u, u, u}
    ⟨X.presheaf, X.IsSheaf⟩ ((pullbackFunctor f).map φ) (𝟙 F)).symm
  change (sheafifyFunctor X).map
      ((Stacks.tensorRight (O := X.presheaf) F.val).map ((pullbackFunctor f).map φ).val) =
    (sheafifyFunctor X).map
      (PresheafOfModules.tensorHom (O := X.presheaf)
        ((pullbackFunctor f).map φ).val (𝟙 F.val))
  apply congrArg (sheafifyFunctor X).map
  apply PresheafOfModules.hom_ext
  intro openSet
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext leftSection rightSection
  exact (Stacks.tensorRight_map_app_tmul (O := X.presheaf) F.val
    ((pullbackFunctor f).map φ).val openSet leftSection rightSection).trans
      (PresheafOfModules.tensorHom_tmul (O := X.presheaf)
        ((pullbackFunctor f).map φ).val (𝟙 F.val) openSet leftSection rightSection).symm

/-! ### The stalk of the pullback, naturally in the module -/

/-- The linear stalk map of a morphism of sheaves of modules on the germ of a section. -/
private lemma stalkMapL_grpGerm {Z : RingedSpace.{u, u}}
    {A B : SheafOfModules.{u} (structureSheafRing Z)} (φ : A ⟶ B) (z : Z.carrier)
    (U : Opens Z.carrier) (hz : z ∈ U) (s : A.val.obj (op U)) :
    stalkMapL Z A.val B.val φ.val z (grpGerm Z A.val z U hz s) =
      grpGerm Z B.val z U hz ((φ.val.app (op U)).hom s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply' U z hz
    ((PresheafOfModules.toPresheaf (O Z)).map φ.val) s

/-- Flatness of a module is carried across an equality of the module structure it is
restricted from. -/
private lemma flat_compHom_of_moduleEq {R S M : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] (φ : R →+* S) {i j : Module S M} (h : i = j)
    (hf : letI := i; letI : Module R M := Module.compHom M φ; Module.Flat R M) :
    letI := j; letI : Module R M := Module.compHom M φ; Module.Flat R M := by
  cases h
  exact hf

/-- **Naturality of Stacks 0098.** The stalk comparison `(f^*G)_x ≃ S ⊗_R G_{f x}` of
`Stacks.RingedSpace.pullbackStalkEquiv` is natural in `G`. It is pinned down by its value on
the germs of pullback-unit images of sections, which is where the proof takes place. -/
private theorem pullbackStalkEquiv_natural
    (G G' : SheafOfModules.{u} (structureSheafRing Y)) (φ : G ⟶ G') (x : X.carrier)
    (z : ↑(grpStalk X (pullbackSheaf f G).val x)) :
    letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    pullbackStalkEquiv f G' x
        (stalkMapL X (pullbackSheaf f G).val (pullbackSheaf f G').val
          ((pullbackFunctor f).map φ).val x z) =
      TensorProduct.AlgebraTensorModule.map
        (LinearMap.id : ↑(ringStalk X x) →ₗ[↑(ringStalk X x)] ↑(ringStalk X x))
        (stalkMapL Y G.val G'.val φ.val (f.hom.base x))
        (pullbackStalkEquiv f G x z) := by
  let _ : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  set e := pullbackStalkEquiv f G x
  set e' := pullbackStalkEquiv f G' x
  set α := stalkMapL X (pullbackSheaf f G).val (pullbackSheaf f G').val
    ((pullbackFunctor f).map φ).val x with hα
  set β := stalkMapL Y G.val G'.val φ.val (f.hom.base x) with hβ
  set t := TensorProduct.AlgebraTensorModule.map
    (LinearMap.id : ↑(ringStalk X x) →ₗ[↑(ringStalk X x)] ↑(ringStalk X x)) β with ht
  have hgen : ∀ n : ↑(grpStalk Y G.val (f.hom.base x)),
      e' (α (e.symm ((1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))] n))) =
        t ((1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))] n) := by
    intro n
    obtain ⟨V, hx, s, rfl⟩ := exists_grpGerm_eq Y G.val (f.hom.base x) n
    have h1 : e.symm ((1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))]
          grpGerm Y G.val (f.hom.base x) V hx s) =
        grpGerm X (pullbackSheaf f G).val x ((opensMap f).obj V) hx
          (pullbackUnit f G (op V) s) :=
      pullbackStalkEquiv_symm_one_tmul f G x V hx s
    have h2 : α (grpGerm X (pullbackSheaf f G).val x ((opensMap f).obj V) hx
          (pullbackUnit f G (op V) s)) =
        grpGerm X (pullbackSheaf f G').val x ((opensMap f).obj V) hx
          (pullbackUnit f G' (op V) ((φ.val.app (op V)).hom s)) := by
      rw [hα]
      refine (stalkMapL_grpGerm ((pullbackFunctor f).map φ) x ((opensMap f).obj V) hx _).trans ?_
      exact congrArg (grpGerm X (pullbackSheaf f G').val x ((opensMap f).obj V) hx)
        (pullbackUnit_naturality f φ (op V) s)
    have h3 : e' (grpGerm X (pullbackSheaf f G').val x ((opensMap f).obj V) hx
          (pullbackUnit f G' (op V) ((φ.val.app (op V)).hom s))) =
        (1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))]
          grpGerm Y G'.val (f.hom.base x) V hx ((φ.val.app (op V)).hom s) :=
      pullbackStalkEquiv_germ f G' x V hx _
    have h4 : t ((1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))]
          grpGerm Y G.val (f.hom.base x) V hx s) =
        (1 : ↑(ringStalk X x)) ⊗ₜ[↑(ringStalk Y (f.hom.base x))]
          grpGerm Y G'.val (f.hom.base x) V hx ((φ.val.app (op V)).hom s) := by
      rw [ht, TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, hβ,
        stalkMapL_grpGerm φ (f.hom.base x) V hx s]
    rw [h1, h2, h3, h4]
  have key : e'.toLinearMap ∘ₗ α ∘ₗ e.symm.toLinearMap = t := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a n
    rw [TensorProduct.tmul_eq_smul_one_tmul]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.map_smul]
    exact congrArg (fun w => a • w) (hgen n)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply] using LinearMap.congr_fun key (e z)

/-! ### The stalk of `f^*G ⊗ F`, naturally in `G` -/

section StalkTensor

variable (G : SheafOfModules.{u} (structureSheafRing Y)) (x : X.carrier)

/-- **The stalk of `f^*G ⊗_{𝒪_X} F` at `x` is `F_x ⊗_{𝒪_{Y, f x}} G_{f x}`.** Only the
additive structure is recorded, because the left-hand side is an `𝒪_{X,x}`-module while the
right-hand side is only an `𝒪_{Y, f x}`-module. -/
private noncomputable def pullbackTensorStalkAddEquiv :
    letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
      Module.compHom _ (f.hom.stalkMap x).hom
    ↑(grpStalk X
        (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f G)).obj F).val x) ≃+
      TensorProduct ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x)
        ↑(grpStalk Y G.val (f.hom.base x)) := by
  let tensorProduct :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj
      (pullbackSheaf f G)).obj F
  letI := stalkModule X tensorProduct.val x
  letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  letI : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  letI : IsScalarTower ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x)
      ↑(grpStalk X F.val x) := SMul.comp.isScalarTower (f.hom.stalkMap x).hom
  exact (tensorStalkIso X x (pullbackSheaf f G) F).toAddEquiv.trans <|
    (TensorProduct.comm ↑(ringStalk X x) ↑(grpStalk X (pullbackSheaf f G).val x)
        ↑(grpStalk X F.val x)).toAddEquiv.trans <|
      (TensorProduct.congr (LinearEquiv.refl ↑(ringStalk X x) ↑(grpStalk X F.val x))
          (pullbackStalkEquiv f G x)).toAddEquiv.trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange
          ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) ↑(ringStalk X x)
          ↑(grpStalk X F.val x) ↑(grpStalk Y G.val (f.hom.base x))).toAddEquiv

end StalkTensor

/-- **Naturality of the stalk comparison.** Under
`Stacks.SheafOfModules.pullbackTensorStalkAddEquiv` the stalk map of
`(pullbackTensorFunctor f F).map φ` becomes `F_x ⊗ φ_{f x}`. -/
private theorem pullbackTensorStalkAddEquiv_natural
    {G G' : SheafOfModules.{u} (structureSheafRing Y)} (φ : G ⟶ G') (x : X.carrier)
    (z : ↑(grpStalk X
      (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f G)).obj F).val x)) :
    letI : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    letI : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
      Module.compHom _ (f.hom.stalkMap x).hom
    pullbackTensorStalkAddEquiv f F G' x
        (stalkMapL X
          (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f G)).obj F).val
          (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f G')).obj F).val
          ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
          (((pullbackFunctor f).map φ, 𝟙 F) : (_, _) ⟶ (_, _))).val x z) =
      LinearMap.lTensor ↑(grpStalk X F.val x)
        (stalkMapL Y G.val G'.val φ.val (f.hom.base x))
        (pullbackTensorStalkAddEquiv f F G x z) := by
  let sourceTensor :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj
      (pullbackSheaf f G)).obj F
  let targetTensor :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj
      (pullbackSheaf f G')).obj F
  let := stalkModule X sourceTensor.val x
  let := stalkModule X targetTensor.val x
  set R := ↑(ringStalk Y (f.hom.base x))
  set S := ↑(ringStalk X x)
  set M := ↑(grpStalk X F.val x)
  let _ : Algebra R S := (f.hom.stalkMap x).hom.toAlgebra
  let _ : Module R M := Module.compHom _ (f.hom.stalkMap x).hom
  let _ : IsScalarTower R S M := SMul.comp.isScalarTower (f.hom.stalkMap x).hom
  set β := stalkMapL Y G.val G'.val φ.val (f.hom.base x)
  set eP := pullbackStalkEquiv f G x
  set eP' := pullbackStalkEquiv f G' x
  set eT := tensorStalkIso X x (pullbackSheaf f G) F
  set eT' := tensorStalkIso X x (pullbackSheaf f G') F
  set α := stalkMapL X (pullbackSheaf f G).val (pullbackSheaf f G').val
    ((pullbackFunctor f).map φ).val x
  -- the identity on `F` induces the identity on stalks
  have hid : stalkMapL X F.val F.val (𝟙 F : F ⟶ F).val x = LinearMap.id := by
    refine LinearMap.ext fun m => ?_
    obtain ⟨U, hxU, t, rfl⟩ := exists_grpGerm_eq X F.val x m
    exact stalkMapL_grpGerm (𝟙 F) x U hxU t
  -- Tag 01CB is natural
  have hTz : eT' (stalkMapL X _ _
      ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        (((pullbackFunctor f).map φ, 𝟙 F) : (_, _) ⟶ (_, _))).val x z) =
      TensorProduct.map α LinearMap.id (eT z) := by
    have hz := DFunLike.congr_fun
      (TensorStalkRingedSpace.tensorStalkIso_natural X x (pullbackSheaf f G) F
        (pullbackSheaf f G') F ((pullbackFunctor f).map φ) (𝟙 F)) z
    rw [hid] at hz
    exact hz.symm
  change TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M _
      (TensorProduct.congr (LinearEquiv.refl S M) eP'
        (TensorProduct.comm S ↑(grpStalk X (pullbackSheaf f G').val x) M
          (eT' (stalkMapL X _ _
            ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
          (((pullbackFunctor f).map φ, 𝟙 F) : (_, _) ⟶ (_, _))).val x z)))) =
    LinearMap.lTensor M β
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M _
        (TensorProduct.congr (LinearEquiv.refl S M) eP
          (TensorProduct.comm S ↑(grpStalk X (pullbackSheaf f G).val x) M (eT z))))
  rw [hTz, (TensorProduct.map_comm (LinearMap.id : M →ₗ[S] M) α (eT z)).symm]
  have hmap : ∀ w : TensorProduct S M ↑(grpStalk X (pullbackSheaf f G).val x),
      TensorProduct.congr (LinearEquiv.refl S M) eP'
          (TensorProduct.map (LinearMap.id : M →ₗ[S] M) α w) =
        TensorProduct.map (LinearMap.id : M →ₗ[S] M)
          (TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) β)
          (TensorProduct.congr (LinearEquiv.refl S M) eP w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | add a b ha hb => simp [ha, hb]
    | tmul m p =>
      simp only [TensorProduct.map_tmul, TensorProduct.congr_tmul, LinearMap.id_apply,
        LinearEquiv.refl_apply]
      exact congrArg (m ⊗ₜ[S] ·) (pullbackStalkEquiv_natural f G G' φ x p)
  rw [hmap]
  exact (LinearMap.congr_fun
    (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange (M := M) R S S β) _).symm

/-! ### Exactness -/

/-- `G ↦ f^*G ⊗_{𝒪_X} F` is additive, both of its factors being so.  The general instance for
a composite is *applied* rather than searched for, because the two factors reach the preadditive
structure of `Mod(𝒪_X)` through two different spellings of the structure sheaf and instance
search does not cross them. -/
noncomputable instance additive_pullbackTensorFunctor :
    (pullbackTensorFunctor f F).Additive := by
  let := Tensor.sheafTensor_additive.{u, u, u, u, u} X.sheaf
  exact show (modulePullback f ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj F).Additive from
    @Functor.instAdditiveComp _ _ _ _ _ _ (modulePullback f) (modulePullback_additive f) _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj F)
      (Functor.flip_obj_additive
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) F)

/-- `G ↦ f^*G ⊗_{𝒪_X} F` preserves zero morphisms, being additive. -/
noncomputable instance preservesZeroMorphisms_pullbackTensorFunctor :
    (pullbackTensorFunctor f F).PreservesZeroMorphisms :=
  @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
    (additive_pullbackTensorFunctor f F)

/-- **Exactness transfers along a ladder of additive equivalences.** Stated for bare maps
between abelian groups, so that no unification with the sheaf-theoretic types the ladder is
applied to happens inside the argument. -/
private lemma exact_of_addEquiv_ladder {A₁ A₂ A₃ B₁ B₂ B₃ : Type*}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
    (e₁ : A₁ ≃+ B₁) (e₂ : A₂ ≃+ B₂) (e₃ : A₃ ≃+ B₃)
    {u : A₁ → A₂} {v : A₂ → A₃} {p : B₁ → B₂} {q : B₂ → B₃}
    (hpq : Function.Exact p q) (hu : ∀ z, e₂ (u z) = p (e₁ z))
    (hv : ∀ z, e₃ (v z) = q (e₂ z)) :
    Function.Exact u v := by
  intro z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := (hpq (e₂ z)).mp (by rw [← hv z, hz, map_zero])
    refine ⟨e₁.symm w, e₂.injective ?_⟩
    rw [hu (e₁.symm w), e₁.apply_symm_apply, hw]
  · rintro ⟨w, rfl⟩
    refine e₃.injective ?_
    rw [hv (u w), hu w, map_zero]
    exact (hpq (p (e₁ w))).mpr (Set.mem_range_self _)

/-- **Flatness over `Y`, at one point.** The stalk `F_x` is flat over `𝒪_{Y, f x}`, stated at
the Tag 01CB module structure on the stalk rather than at Mathlib's. -/
private lemma flat_stalk_of_isFlatOver (hF : AlgebraicGeometry.IsFlatOver f F) (x : X.carrier) :
    letI : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
      Module.compHom _ (f.hom.stalkMap x).hom
    Module.Flat ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
  flat_compHom_of_moduleEq (f.hom.stalkMap x).hom (stalkModule_eq X F.val x).symm (hF x)

/-- The stalk at `y` of an exact short complex of `𝒪_Y`-modules is an exact pair of linear
maps. -/
private lemma exact_stalkMapL
    (S : ShortComplex (SheafOfModules.{u} (structureSheafRing Y))) (hS : S.Exact)
    (y : Y.carrier) :
    Function.Exact (stalkMapL Y S.X₁.val S.X₂.val S.f.val y)
      (stalkMapL Y S.X₂.val S.X₃.val S.g.val y) :=
  (ShortComplex.ab_exact_iff_function_exact
      (AlgebraicGeometry.SheafOfModules.stalkShortComplex (structureSheafRing Y) S y)).mp
    ((AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
      (structureSheafRing Y) S).mp hS y)

/-- Tensoring the stalk complex of `S` at `f x` with `F_x` over `𝒪_{Y, f x}` keeps it exact,
because `F_x` is flat over `𝒪_{Y, f x}`. -/
private lemma exact_lTensor_stalkMapL (hF : AlgebraicGeometry.IsFlatOver f F)
    (S : ShortComplex (SheafOfModules.{u} (structureSheafRing Y))) (hS : S.Exact)
    (x : X.carrier) :
    letI : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
      Module.compHom _ (f.hom.stalkMap x).hom
    Function.Exact
      (LinearMap.lTensor ↑(grpStalk X F.val x)
        (stalkMapL Y S.X₁.val S.X₂.val S.f.val (f.hom.base x)))
      (LinearMap.lTensor ↑(grpStalk X F.val x)
        (stalkMapL Y S.X₂.val S.X₃.val S.g.val (f.hom.base x))) := by
  let _ : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  let _ := flat_stalk_of_isFlatOver f F hF x
  exact Module.Flat.lTensor_exact ↑(grpStalk X F.val x) (exact_stalkMapL S hS (f.hom.base x))

/-- The stalk at `x` of the complex obtained from `S` by applying `G ↦ f^*G ⊗_{𝒪_X} F` is
exact: under the stalk formula it is the previous complex. -/
private lemma exact_stalkMapL_tensorSheafMap (hF : AlgebraicGeometry.IsFlatOver f F)
    (S : ShortComplex (SheafOfModules.{u} (structureSheafRing Y))) (hS : S.Exact)
    (x : X.carrier) :
    Function.Exact
      (stalkMapL X
        (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f S.X₁)).obj F).val
        (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f S.X₂)).obj F).val
        ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
          (((pullbackFunctor f).map S.f, 𝟙 F) : (_, _) ⟶ (_, _))).val x)
      (stalkMapL X
        (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f S.X₂)).obj F).val
        (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f S.X₃)).obj F).val
        ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
          (((pullbackFunctor f).map S.g, 𝟙 F) : (_, _) ⟶ (_, _))).val x) := by
  let _ : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  let _ : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  exact exact_of_addEquiv_ladder (pullbackTensorStalkAddEquiv f F S.X₁ x)
    (pullbackTensorStalkAddEquiv f F S.X₂ x) (pullbackTensorStalkAddEquiv f F S.X₃ x)
    (exact_lTensor_stalkMapL f F hF S hS x)
    (fun z => pullbackTensorStalkAddEquiv_natural f F S.f x z)
    (fun z => pullbackTensorStalkAddEquiv_natural f F S.g x z)

/-- The stalk at `x` of the image of `S` under `G ↦ f^*G ⊗_{𝒪_X} F` is exact. -/
@[ega "0 6.7.2" "special case"]
private lemma stalkShortComplex_map_exact (hF : AlgebraicGeometry.IsFlatOver f F)
    (S : ShortComplex (SheafOfModules.{u} (structureSheafRing Y))) (hS : S.Exact)
    (x : X.carrier) :
    (AlgebraicGeometry.SheafOfModules.stalkShortComplex (structureSheafRing X)
      (S.map (pullbackTensorFunctor f F)) x).Exact := by
  apply (ShortComplex.ab_exact_iff_function_exact _).2
  exact (congrArg₂
    (fun (first : (pullbackTensorFunctor f F).obj S.X₁ ⟶ (pullbackTensorFunctor f F).obj S.X₂)
        (second : (pullbackTensorFunctor f F).obj S.X₂ ⟶ (pullbackTensorFunctor f F).obj S.X₃) =>
      Function.Exact
        (stalkMapL X ((pullbackTensorFunctor f F).obj S.X₁).val
          ((pullbackTensorFunctor f F).obj S.X₂).val first.val x)
        (stalkMapL X ((pullbackTensorFunctor f F).obj S.X₂).val
          ((pullbackTensorFunctor f F).obj S.X₃).val second.val x))
    (pullbackTensorFunctor_map f F S.f) (pullbackTensorFunctor_map f F S.g)).mpr
      (exact_stalkMapL_tensorSheafMap f F hF S hS x)

/-- `G ↦ f^*G ⊗_{𝒪_X} F` carries an exact short complex to an exact short complex. -/
private lemma map_exact_of_exact (hF : AlgebraicGeometry.IsFlatOver f F)
    (S : ShortComplex (SheafOfModules.{u} (structureSheafRing Y))) (hS : S.Exact) :
    (S.map (pullbackTensorFunctor f F)).Exact :=
  (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
      (structureSheafRing X) (S.map (pullbackTensorFunctor f F))).2
    fun x => stalkShortComplex_map_exact f F hF S hS x

/-- **Stacks Project, Tag 0GMU.** If `F` is an `𝒪_X`-module flat over `Y`, then the functor
`G ↦ f^*G ⊗_{𝒪_X} F` is exact. -/
@[stacks 0GMU, sga "4 V 1.7" "(ii) ⇒ (i)"]
theorem pullbackTensorFunctor_exact (hF : AlgebraicGeometry.IsFlatOver f F) :
    exactFunctor (SheafOfModules.{u} (structureSheafRing Y))
      (SheafOfModules.{u} (structureSheafRing X)) (pullbackTensorFunctor f F) := by
  let _ : (pullbackTensorFunctor f F).PreservesHomology :=
    Functor.preservesHomology_of_map_exact _ fun S hS => map_exact_of_exact f F hF S hS
  let _ : ∀ {A B : SheafOfModules.{u} (structureSheafRing Y)} (g : A ⟶ B),
      PreservesLimit (parallelPair g 0) (pullbackTensorFunctor f F) := fun g =>
    Functor.PreservesHomology.preservesKernels (F := pullbackTensorFunctor f F) g
  let _ : ∀ {A B : SheafOfModules.{u} (structureSheafRing Y)} (g : A ⟶ B),
      PreservesColimit (parallelPair g 0) (pullbackTensorFunctor f F) := fun g =>
    Functor.PreservesHomology.preservesCokernels (F := pullbackTensorFunctor f F) g
  exact (exactFunctor_iff (pullbackTensorFunctor f F)).2
    ⟨Functor.preservesFiniteLimits_of_preservesKernels _,
      Functor.preservesFiniteColimits_of_preservesCokernels _⟩

/-! ### Stalkwise split monomorphisms -/

open scoped ZeroObject

/-- **`G ↦ f^*G ⊗_{𝒪_X} F` carries a morphism which is split injective on the stalks at the
images of the points of `X` to a monomorphism**, with no hypothesis on `F`.  On the stalk at `x`
the image of `φ` is `F_x ⊗_{𝒪_{Y, f x}} φ_{f x}` (`pullbackTensorStalkAddEquiv_natural`), and
tensoring keeps a split injection split injective. -/
theorem pullbackTensorFunctor_map_mono {G G' : SheafOfModules.{u} (structureSheafRing Y)}
    (φ : G ⟶ G')
    (hφ : ∀ x : X.carrier, ∃ r : ↑(grpStalk Y G'.val (f.hom.base x))
        →ₗ[↑(ringStalk Y (f.hom.base x))] ↑(grpStalk Y G.val (f.hom.base x)),
      r ∘ₗ stalkMapL Y G.val G'.val φ.val (f.hom.base x) = LinearMap.id) :
    Mono ((pullbackTensorFunctor f F).map φ) := by
  let S := ShortComplex.mk (0 : 0 ⟶ (pullbackTensorFunctor f F).obj G)
    ((pullbackTensorFunctor f F).map φ) zero_comp
  refine (ShortComplex.exact_iff_mono S rfl).mp ?_
  refine (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact
    (structureSheafRing X) S).2 fun x => ?_
  refine (ShortComplex.ab_exact_iff_function_exact _).2 ?_
  have hinj : Function.Injective (stalkMapL X
      (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f G)).obj F).val
      (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj (pullbackSheaf f G')).obj F).val
      ((Functor.uncurry.obj (Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
          (((pullbackFunctor f).map φ, 𝟙 F) : (_, _) ⟶ (_, _))).val x) := by
    obtain ⟨r, hr⟩ := hφ x
    let _ : Algebra ↑(ringStalk Y (f.hom.base x)) ↑(ringStalk X x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    let _ : Module ↑(ringStalk Y (f.hom.base x)) ↑(grpStalk X F.val x) :=
      Module.compHom _ (f.hom.stalkMap x).hom
    have hl : Function.Injective (LinearMap.lTensor ↑(grpStalk X F.val x)
        (stalkMapL Y G.val G'.val φ.val (f.hom.base x))) := by
      have hc : LinearMap.lTensor ↑(grpStalk X F.val x) r ∘ₗ
          LinearMap.lTensor ↑(grpStalk X F.val x)
            (stalkMapL Y G.val G'.val φ.val (f.hom.base x)) = LinearMap.id := by
        rw [← LinearMap.lTensor_comp, hr, LinearMap.lTensor_id]
      exact Function.LeftInverse.injective (LinearMap.congr_fun hc)
    intro z₁ z₂ h
    apply (pullbackTensorStalkAddEquiv f F G x).injective
    apply hl
    rw [← pullbackTensorStalkAddEquiv_natural f F φ x z₁,
      ← pullbackTensorStalkAddEquiv_natural f F φ x z₂, h]
  have actualInjective : Function.Injective
      (stalkMapL X ((pullbackTensorFunctor f F).obj G).val
        ((pullbackTensorFunctor f F).obj G').val ((pullbackTensorFunctor f F).map φ).val x) :=
    (congrArg (fun morphism : (pullbackTensorFunctor f F).obj G ⟶
        (pullbackTensorFunctor f F).obj G' =>
      Function.Injective (stalkMapL X ((pullbackTensorFunctor f F).obj G).val
        ((pullbackTensorFunctor f F).obj G').val morphism.val x))
      (pullbackTensorFunctor_map f F φ)).mpr hinj
  intro z
  constructor
  · intro hz
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (actualInjective (hz.trans (map_zero _).symm)).symm
  · rintro ⟨w, rfl⟩
    simp

end Stacks.SheafOfModules
