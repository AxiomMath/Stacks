module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantDual
public import StacksFrontier.AlgebraicGeometry.Duality.FundamentalClassDeterminantConverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map of [Stacks, Tag 0E9Y] and its isomorphism locus

Let `X` be a locally ringed space and let

`E₁ --α--> E₀ --π--> F ⟶ 0`

be an exact sequence of `O_X`-modules with `E₁` and `E₀` finite locally free of ranks `r₁` and
`r₀`. [Stacks, Tag 0E9Y] asserts that there is a canonical map

`⋀^{r₀ - r₁} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₀} E₀`,
`s₁ ∧ ⋯ ∧ s_r ↦ (t₁^∨ ∧ ⋯ ∧ t_{r₁}^∨) ⊗ (α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r)`

(`t` a local basis of `E₁`, `t^∨` the dual basis, `s̃ᵢ` local lifts of the `sᵢ`), which is an
isomorphism on the stalk at `x` if and only if `F` is locally free of rank `r₀ - r₁` on an open
neighbourhood of `x`. This file constructs that map and proves the criterion.

## The construction

Write `L = ⋀^{r₁} E₁`, `D = ⋀^{r₁}(E₁^∨)` and `r = r₀ - r₁ ≥ 0`. Two maps are already available:

* the pairing `P : L ⊗ ⋀^{r} F ⟶ ⋀^{r₀} E₀`, `(t₁ ∧ ⋯ ∧ t_{r₁}) ⊗ (s₁ ∧ ⋯ ∧ s_r) ↦
  α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r` (`Stacks.Duality.detSheafPairing`), and
* the determinant pairing `D ⊗ L ⟶ O_X`, `(λ₁ ∧ ⋯ ∧ λ_{r₁}) ⊗ (e₁ ∧ ⋯ ∧ e_{r₁}) ↦ det λᵢ(eⱼ)`,
  which is an isomorphism because `E₁` is finite locally free of rank `r₁`
  (`Stacks.Duality.isIso_detDualPairing`).

The inverse of the second is a coevaluation `O_X ⟶ D ⊗ L` sending `1` to
`(t₁^∨ ∧ ⋯ ∧ t_{r₁}^∨) ⊗ (t₁ ∧ ⋯ ∧ t_{r₁})` on any open carrying a local basis
(`Stacks.Duality.detCoev_app_one`), and the canonical map is

`⋀^{r} F ≅ O_X ⊗ ⋀^{r} F ⟶ (D ⊗ L) ⊗ ⋀^{r} F ≅ D ⊗ (L ⊗ ⋀^{r} F) ⟶ D ⊗ ⋀^{r₀} E₀`

(`Stacks.Duality.detSourceMap`). It satisfies the source's formula
(`Stacks.Duality.detSourceMap_wedge`), for every local basis of `E₁` and every choice of lifts,
which is the precise sense in which it is canonical. For `r₁ > r₀` the source reads
`⋀^{r₀ - r₁} F` as the zero sheaf; here `⋀^{r₀ - r₁} F` is the piece of degree `r₀ - r₁ ∈ ℤ` of
the exterior algebra of `F`, which is zero in negative degrees, and the map is zero
(`Stacks.Duality.sheafDeterminantMap`).

## The criterion

The first three maps in the composite are isomorphisms, and the stalk of `D` at any point is
free of rank one (`Stacks.Duality.nonempty_stalk_exteriorPower_dual_linearEquiv`), so the canonical
map is bijective on the stalk at `x` exactly when `P` is
(`Stacks.Duality.bijective_stalkMapL_detSourceMap_iff`). Over the local ring `O_x` that happens
exactly when `Fₓ` is free of rank `r` (`Stacks.Duality.bijective_stalkMapL_detSheafPairing_iff`),
and since `F` is of finite presentation, exactly when `F` is free of rank `r` near `x`
([Stacks, Tag 0B8J]). For `r₁ > r₀` the map is zero into a sheaf whose stalks are free of rank
one, so it is never bijective on a stalk.

## Main definitions

* `Stacks.Duality.detCoev`: the coevaluation `O_X ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₁} E₁`.
* `Stacks.Duality.detSourceMap`: the canonical map `⋀^{r} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₁ + r} E₀`.
* `Stacks.Duality.sheafDeterminantMap`: the same, indexed as in the source, from
  `⋀^{r₀ - r₁} F` with `r₀ - r₁ ∈ ℤ`.
* `Stacks.Duality.locallyRingedSpaceDeterminantMap`: the same on a locally ringed space, for the
  exterior powers of the space.

## Main results

* `Stacks.Duality.detSourceMap_wedge`: the local formula of the source.
* `Stacks.Duality.bijective_stalkMapL_sheafDeterminantMap_iff`: the criterion on a space whose
  stalk at `x` is a local ring.
* `Stacks.Duality.isIso_stalkMap_locallyRingedSpaceDeterminantMap_iff`: **[Stacks, Tag 0E9Y].**

## Implementation notes

"`F` is locally free of rank `r` on an open neighbourhood of `x`" is stated as the existence of an
open `U ∋ x` and a trivialization `F|_U ≅ O_U^{⊕ ι}` with `ι ≃ Fin r`, in the sense of
[Stacks, Tag 01C9] (`LocallyFreeRank.Trivialization`): the two are equivalent, a locally free
sheaf being free on a smaller neighbourhood of each point.

## References

* [Stacks Project, Tag 0E9Y](https://stacks.math.columbia.edu/tag/0E9Y)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf CategoryTheory.MonoidalCategory
open Stacks.SheafOfModules.TopWedge
open scoped TensorProduct

universe u

attribute [local implicit_reducible] structureSheafRing AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.Duality

section TensorStalk

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  (D : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  {G G' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (f : G ⟶ G') (x : ↥X)

/-- Tensoring a morphism on the left with `D`. -/
noncomputable def tensorLeftHom :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj D).obj G ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj D).obj G' :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj D).map f

/-- On sections over `W`, `tensorLeftHom D f` sends the image of `d ⊗ₜ g` under the
sheafification unit to the image of `d ⊗ₜ f g`. -/
theorem tensorLeftHom_unit (W : Opens ↥X) (d : D.val.obj (op W)) (g : G.val.obj (op W)) :
    (tensorLeftHom D f).val.app (op W) ((PresheafOfModules.tensorSheafUnit D G).app (op W)
        (d ⊗ₜ g)) =
      (PresheafOfModules.tensorSheafUnit D G').app (op W) (d ⊗ₜ f.val.app (op W) g) := by
  have mapUnit := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    Osharp D G
    (@CategoryStruct.id (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)) _ D) f (op W) d g
  rwa [(Stacks.SheafOfModules.Tensor.sheafTensor Osharp).map_id D,
    NatTrans.id_app ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj D) G,
    Category.id_comp] at mapUnit

/-- Left tensoring on the germ of a local pure tensor. -/
theorem stalkMapL_tensorLeft_tensorSheafGerm (W : Opens ↥X) (hxW : x ∈ W)
    (d : D.val.obj (op W)) (g : G.val.obj (op W)) :
    PresheafOfModules.stalkMapL x
        (tensorLeftHom D f).val
        (PresheafOfModules.tensorSheafGerm Osharp D G x W hxW d g) =
      PresheafOfModules.tensorSheafGerm Osharp D G' x W hxW d (f.val.app (op W) g) :=
  (PresheafOfModules.stalkMapL_germ x _ W hxW _).trans
    (congrArg (TopCat.Presheaf.germ (PresheafOfModules.tensorSheafVal Osharp D G').presheaf W x
      hxW) (tensorLeftHom_unit D f W d g))

/-- Left tensoring on stalks, on a pure tensor of germs. -/
theorem tensorSheafStalkEquiv_stalkMapL_tensorLeft_germ (W : Opens ↥X) (hxW : x ∈ W)
    (d : D.val.obj (op W)) (g : G.val.obj (op W)) :
    PresheafOfModules.tensorSheafStalkEquiv Osharp D G' x
        (PresheafOfModules.stalkMapL x
          (tensorLeftHom D f).val
          ((PresheafOfModules.tensorSheafStalkEquiv Osharp D G x).symm
            (TopCat.Presheaf.germ D.val.presheaf W x hxW d ⊗ₜ
              TopCat.Presheaf.germ G.val.presheaf W x hxW g))) =
      TopCat.Presheaf.germ D.val.presheaf W x hxW d ⊗ₜ
        PresheafOfModules.stalkMapL x f.val (TopCat.Presheaf.germ G.val.presheaf W x hxW g) := by
  have hsymm : (PresheafOfModules.tensorSheafStalkEquiv Osharp D G x).symm
      (TopCat.Presheaf.germ D.val.presheaf W x hxW d ⊗ₜ
        TopCat.Presheaf.germ G.val.presheaf W x hxW g) =
      PresheafOfModules.tensorSheafGerm Osharp D G x W hxW d g :=
    (LinearEquiv.symm_apply_eq _).2
      (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp D G x W hxW _ _).symm
  refine Eq.trans (congrArg (fun t => PresheafOfModules.tensorSheafStalkEquiv Osharp D G' x
    (PresheafOfModules.stalkMapL x
      (tensorLeftHom D f).val t)) hsymm) ?_
  refine Eq.trans (congrArg (PresheafOfModules.tensorSheafStalkEquiv Osharp D G' x)
    (stalkMapL_tensorLeft_tensorSheafGerm D f x W hxW d g)) ?_
  refine Eq.trans (PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm Osharp D G' x W hxW
    d (f.val.app (op W) g)) ?_
  exact congrArg (fun t => TopCat.Presheaf.germ D.val.presheaf W x hxW d ⊗ₜ t)
    (PresheafOfModules.stalkMapL_germ x f.val W hxW g).symm

/-- **Left tensoring on stalks.** Under the identification of the stalk of a tensor product
sheaf with the tensor product of the stalks (Tag 01CB), the stalk of `D ⊗ f` is `D_x ⊗ f_x`. -/
theorem tensorSheafStalkEquiv_stalkMapL_tensorLeft
    (z : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp D G).presheaf x)) :
    PresheafOfModules.tensorSheafStalkEquiv Osharp D G' x
        (PresheafOfModules.stalkMapL x
          (tensorLeftHom D f).val z) =
      LinearMap.lTensor (↑(TopCat.Presheaf.stalk D.val.presheaf x))
        (PresheafOfModules.stalkMapL x f.val)
        (PresheafOfModules.tensorSheafStalkEquiv Osharp D G x z) := by
  refine ExteriorAlgebra.linearEquiv_comp_eq_lTensor _ _ _ _ (fun a b => ?_) z
  refine forall_common_germ₂ D.val.presheaf G.val.presheaf x 1 1 (fun _ => a) (fun _ => b)
    (fun W hxW s t hs ht => ?_)
  rw [← hs 0, ← ht 0]
  exact tensorSheafStalkEquiv_stalkMapL_tensorLeft_germ D f x W hxW (s 0) (t 0)

/-- **Left tensoring with a sheaf whose stalk is free of rank one detects bijectivity on that
stalk.** -/
theorem bijective_stalkMapL_tensorLeftHom_iff
    (eD : ↑(TopCat.Presheaf.stalk D.val.presheaf x) ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ↑(TopCat.Presheaf.stalk Osharp.obj x)) :
    Function.Bijective (PresheafOfModules.stalkMapL x (tensorLeftHom D f).val) ↔
      Function.Bijective (PresheafOfModules.stalkMapL x f.val) := by
  have h : ⇑(PresheafOfModules.stalkMapL x (tensorLeftHom D f).val) =
      ⇑(PresheafOfModules.tensorSheafStalkEquiv Osharp D G' x).symm ∘
        ⇑(LinearMap.lTensor (↑(TopCat.Presheaf.stalk D.val.presheaf x))
          (PresheafOfModules.stalkMapL x f.val)) ∘
        ⇑(PresheafOfModules.tensorSheafStalkEquiv Osharp D G x) := by
    funext z
    exact (LinearEquiv.eq_symm_apply _).2 (tensorSheafStalkEquiv_stalkMapL_tensorLeft D f x z)
  rw [h, Function.Bijective.of_comp_iff' (LinearEquiv.bijective _),
    Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]
  exact ExteriorAlgebra.bijective_lTensor_iff eD _

end TensorStalk

/-! ### Stalk maps of composites and of isomorphisms -/

section StalkComp

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {M N P : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- The stalk map at `x` of a composite `f ≫ g` is the composite of the stalk maps. -/
theorem stalkMapL_comp_apply (f : M ⟶ N) (g : N ⟶ P) (x : ↥X)
    (z : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    PresheafOfModules.stalkMapL x (f ≫ g).val z =
      PresheafOfModules.stalkMapL x g.val (PresheafOfModules.stalkMapL x f.val z) := by
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf z
  refine (PresheafOfModules.stalkMapL_germ x (f ≫ g).val U hU s).trans ?_
  refine Eq.trans ?_ (congrArg (PresheafOfModules.stalkMapL x g.val)
    (PresheafOfModules.stalkMapL_germ x f.val U hU s)).symm
  exact (_root_.SheafOfModules.stalkMapL_germ_comp x f g (f ≫ g) rfl U hU s).symm

/-- The stalk map at `x` of an isomorphism of sheaves of modules is bijective. -/
theorem bijective_stalkMapL_of_isIso (f : M ⟶ N) [IsIso f] (x : ↥X) :
    Function.Bijective (PresheafOfModules.stalkMapL x f.val) :=
  (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap f).1 inferInstance x

/-- Precomposing with an isomorphism does not change bijectivity on stalks. -/
theorem bijective_stalkMapL_iso_comp_iff (e : M ⟶ N) [IsIso e] (g : N ⟶ P) (x : ↥X) :
    Function.Bijective (PresheafOfModules.stalkMapL x (e ≫ g).val) ↔
      Function.Bijective (PresheafOfModules.stalkMapL x g.val) := by
  have h : ⇑(PresheafOfModules.stalkMapL x (e ≫ g).val) =
      ⇑(PresheafOfModules.stalkMapL x g.val) ∘ ⇑(PresheafOfModules.stalkMapL x e.val) :=
    funext (stalkMapL_comp_apply e g x)
  rw [h]
  exact Function.Bijective.of_comp_iff _ (bijective_stalkMapL_of_isIso e x)

/-- Postcomposing with an isomorphism does not change bijectivity on stalks. -/
theorem bijective_stalkMapL_comp_iso_iff (g : M ⟶ N) (e : N ⟶ P) [IsIso e] (x : ↥X) :
    Function.Bijective (PresheafOfModules.stalkMapL x (g ≫ e).val) ↔
      Function.Bijective (PresheafOfModules.stalkMapL x g.val) := by
  have h : ⇑(PresheafOfModules.stalkMapL x (g ≫ e).val) =
      ⇑(PresheafOfModules.stalkMapL x e.val) ∘ ⇑(PresheafOfModules.stalkMapL x g.val) :=
    funext (stalkMapL_comp_apply g e x)
  rw [h]
  exact Function.Bijective.of_comp_iff' (bijective_stalkMapL_of_isIso e x) _

end StalkComp

/-! ### The canonical map in the source's form -/

section Source

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {E₁ E₀ F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A₁ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E₁)
  (A₀ : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) E₀)
  (AF : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) F)
  (A₁d : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (dualMod E₁))
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ r : ℕ)

/-- The coevaluation `O_X ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₁} E₁`, the inverse of the determinant
pairing. -/
noncomputable def detCoev [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    E₁ r₁] :
    _root_.SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁d.exteriorPower r₁)).obj
        (A₁.exteriorPower r₁) :=
  @inv _ _ _ _ (detDualPairing A₁d A₁ r₁) (isIso_detDualPairing A₁d A₁ r₁)

/-- The coevaluation `detCoev A₁ A₁d r₁` is an isomorphism. -/
instance isIso_detCoev [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    E₁ r₁] : IsIso (detCoev A₁ A₁d r₁) :=
  @IsIso.inv_isIso _ _ _ _ (detDualPairing A₁d A₁ r₁) (isIso_detDualPairing A₁d A₁ r₁)

/-- The isomorphism `⋀^{r} F ≅ (⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₁} E₁) ⊗ ⋀^{r} F ≅
⋀^{r₁}(E₁^∨) ⊗ (⋀^{r₁} E₁ ⊗ ⋀^{r} F)` through which the canonical map factors: the left
unitor, the coevaluation `detCoev` tensored with `⋀^{r} F`, and the associator. -/
noncomputable def detSourcePrefixIso
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] :
    AF.exteriorPower r ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁d.exteriorPower r₁)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁.exteriorPower r₁)).obj
        (AF.exteriorPower r)) :=
  letI := Stacks.TensorSheafWorld.monoidalCategory Osharp
  (λ_ (AF.exteriorPower r)).symm ≪≫
    whiskerRightIso (asIso (detCoev A₁ A₁d r₁)) (AF.exteriorPower r) ≪≫
    α_ (A₁d.exteriorPower r₁) (A₁.exteriorPower r₁) (AF.exteriorPower r)

/-- **The canonical map of [Stacks, Tag 0E9Y]**
`⋀^{r} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₁ + r} E₀`. -/
noncomputable def detSourceMap [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] :
    AF.exteriorPower r ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁d.exteriorPower r₁)).obj
        (A₀.exteriorPower (r₁ + r)) :=
  (detSourcePrefixIso A₁ AF A₁d r₁ r).hom ≫
    tensorLeftHom (A₁d.exteriorPower r₁) (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r)

/-- The monoidal structure of Tag 01CA on sheaves of modules on a space. -/
noncomputable abbrev monoidalOpens : MonoidalCategory (_root_.SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :=
  Stacks.TensorSheafWorld.monoidalCategory Osharp

attribute [local instance] monoidalOpens

/-- The inverse of an isomorphism undoes it on local sections. -/
private theorem inv_val_app_eq_of_hom_val_app_eq
    {M N : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (e : M ≅ N) (V : Opens ↥X) {y : M.val.obj (op V)} {z : N.val.obj (op V)}
    (h : e.hom.val.app (op V) y = z) : e.inv.val.app (op V) z = y :=
  h ▸ congrArg (fun m => m.val.app (op V) y) e.hom_inv_id

/-- The inverse of the left unitor on a local section. -/
theorem leftUnitor_inv_val_app
    (M : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (V : Opens ↥X) (y : M.val.obj (op V)) :
    (λ_ M).inv.val.app (op V) y =
      (PresheafOfModules.tensorSheafUnit (𝟙_ _) M).app (op V) (unitOneAt V ⊗ₜ y) := by
  have hh := Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit Osharp
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property M (op V)
    (1 : (toRingCat (Opens.grothendieckTopology ↥X) Osharp).obj.obj (op V)) y
  rw [one_smul] at hh
  exact inv_val_app_eq_of_hom_val_app_eq (λ_ M) V hh

/-- On an open carrying a local frame `t` of `E₁` with dual frame `t^∨`, the coevaluation sends
`1` to `(t₁^∨ ∧ ⋯ ∧ t_{r₁}^∨) ⊗ (t₁ ∧ ⋯ ∧ t_{r₁})`. -/
theorem detCoev_app_one
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    {V : Opens ↥X} (fr : LocalFrame E₁ r₁ V) :
    (detCoev A₁ A₁d r₁).val.app (op V) (unitOneAt V) =
      (PresheafOfModules.tensorSheafUnit (A₁d.exteriorPower r₁) (A₁.exteriorPower r₁)).app (op V)
        (wedgeSec A₁d (op V) r₁ fr.b.lam ⊗ₜ wedgeSec A₁ (op V) r₁ fr.b.e) := by
  exact inv_val_app_eq_of_hom_val_app_eq
    (@asIso _ _ _ _ (detDualPairing A₁d A₁ r₁) (isIso_detDualPairing A₁d A₁ r₁)) V
    ((detDualPairing_wedge A₁d A₁ r₁ (op V) fr.b.lam fr.b.e).trans fr.det_eq_one)

/-- The coevaluation tensored with `⋀^{r} F`, on a local section. -/
theorem detCoev_whiskerRight_val_app
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    {V : Opens ↥X} (fr : LocalFrame E₁ r₁ V) (y : (AF.exteriorPower r).val.obj (op V)) :
    (detCoev A₁ A₁d r₁ ▷ AF.exteriorPower r).val.app (op V)
        ((PresheafOfModules.tensorSheafUnit (𝟙_ _) (AF.exteriorPower r)).app (op V)
          (unitOneAt V ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit _ (AF.exteriorPower r)).app (op V)
        ((PresheafOfModules.tensorSheafUnit (A₁d.exteriorPower r₁) (A₁.exteriorPower r₁)).app
          (op V) (wedgeSec A₁d (op V) r₁ fr.b.lam ⊗ₜ wedgeSec A₁ (op V) r₁ fr.b.e) ⊗ₜ y) := by
  refine (Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit Osharp
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property (op V)
    (detCoev A₁ A₁d r₁) (AF.exteriorPower r) (unitOneAt V) y).trans ?_
  exact congrArg (fun z => (PresheafOfModules.tensorSheafUnit _ (AF.exteriorPower r)).app (op V)
    (z ⊗ₜ y)) (detCoev_app_one A₁ A₁d r₁ fr)

/-- The isomorphism through which the canonical map factors, on a local section. -/
theorem detSourcePrefixIso_hom_wedge
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    {V : Opens ↥X} (fr : LocalFrame E₁ r₁ V) (y : (AF.exteriorPower r).val.obj (op V)) :
    (detSourcePrefixIso A₁ AF A₁d r₁ r).hom.val.app (op V) y =
      (PresheafOfModules.tensorSheafUnit (A₁d.exteriorPower r₁) _).app (op V)
        (wedgeSec A₁d (op V) r₁ fr.b.lam ⊗ₜ
          (PresheafOfModules.tensorSheafUnit (A₁.exteriorPower r₁) (AF.exteriorPower r)).app
            (op V) (wedgeSec A₁ (op V) r₁ fr.b.e ⊗ₜ y)) := by
  have h3 := Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit Osharp
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp).property
    (A₁d.exteriorPower r₁) (A₁.exteriorPower r₁) (AF.exteriorPower r) (op V)
    (wedgeSec A₁d (op V) r₁ fr.b.lam) (wedgeSec A₁ (op V) r₁ fr.b.e) y
  change (α_ (A₁d.exteriorPower r₁) (A₁.exteriorPower r₁) (AF.exteriorPower r)).hom.val.app
      (op V) ((detCoev A₁ A₁d r₁ ▷ AF.exteriorPower r).val.app (op V)
        ((λ_ (AF.exteriorPower r)).inv.val.app (op V) y)) = _
  rw [leftUnitor_inv_val_app, detCoev_whiskerRight_val_app A₁ AF A₁d r₁ r fr y]
  exact h3

/-- **The local formula of [Stacks, Tag 0E9Y] for the canonical map.** On an open `V` on which
`E₁` has a local basis `t₁, …, t_{r₁}` with dual basis `t₁^∨, …, t_{r₁}^∨`, for local sections
`s₁, …, s_r` of `F` and **any** local lifts `s̃ᵢ` of them to `E₀`, the canonical map sends

`s₁ ∧ ⋯ ∧ s_r ↦ (t₁^∨ ∧ ⋯ ∧ t_{r₁}^∨) ⊗ (α(t₁) ∧ ⋯ ∧ α(t_{r₁}) ∧ s̃₁ ∧ ⋯ ∧ s̃_r)`.

This is the formula by which the source defines the map. -/
theorem detSourceMap_wedge [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    {V : Opens ↥X} (fr : LocalFrame E₁ r₁ V) (s : Fin r → F.val.obj (op V))
    (l : Fin r → E₀.val.obj (op V)) (hl : ∀ i, π.val.app (op V) (l i) = s i) :
    (detSourceMap A₁ A₀ AF A₁d α π hαπ hS r₁ r).val.app (op V) (wedgeSec AF (op V) r s) =
      (PresheafOfModules.tensorSheafUnit (A₁d.exteriorPower r₁) (A₀.exteriorPower (r₁ + r))).app
        (op V) (wedgeSec A₁d (op V) r₁ fr.b.lam ⊗ₜ
          wedgeSec A₀ (op V) (r₁ + r) (Fin.append (fun i => α.val.app (op V) (fr.b.e i)) l)) := by
  change (tensorLeftHom (A₁d.exteriorPower r₁)
    (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r)).val.app (op V)
      ((detSourcePrefixIso A₁ AF A₁d r₁ r).hom.val.app (op V) (wedgeSec AF (op V) r s)) = _
  rw [detSourcePrefixIso_hom_wedge A₁ AF A₁d r₁ r fr]
  refine (tensorLeftHom_unit _ _ V _ _).trans ?_
  exact congrArg (fun z => (PresheafOfModules.tensorSheafUnit (A₁d.exteriorPower r₁)
    (A₀.exteriorPower (r₁ + r))).app (op V) (wedgeSec A₁d (op V) r₁ fr.b.lam ⊗ₜ z))
    (detSheafPairing_wedge A₁ A₀ AF α π hαπ hS r₁ r (op V) fr.b.e s l hl)

/-- **The canonical map is bijective on a stalk exactly when the pairing is.** -/
theorem bijective_stalkMapL_detSourceMap_iff [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] (x : ↥X) :
    Function.Bijective (PresheafOfModules.stalkMapL x
        (detSourceMap A₁ A₀ AF A₁d α π hαπ hS r₁ r).val) ↔
      Function.Bijective (PresheafOfModules.stalkMapL x
        (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r).val) := by
  obtain ⟨eD⟩ := nonempty_stalk_exteriorPower_dual_linearEquiv A₁d A₁ r₁ x
  exact (@bijective_stalkMapL_iso_comp_iff _ _ _ _ _ (detSourcePrefixIso A₁ AF A₁d r₁ r).hom
      (Iso.isIso_hom (detSourcePrefixIso A₁ AF A₁d r₁ r))
      (tensorLeftHom (A₁d.exteriorPower r₁)
        (detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r)) x).trans
    (bijective_stalkMapL_tensorLeftHom_iff _ _ x eD)

/-! ### Freeness of the stalk and freeness near the point -/

section Trivialization

attribute [local implicit_reducible] LocallyFreeRank.toRingSheaf

variable {X' : TopCat.{u}} {O' : Sheaf (Opens.grothendieckTopology ↥X') CommRingCat.{u}}

/-- A trivialization of `F` on `U`, in the sense of [Stacks, Tag 01C9], from an isomorphism of
`F|_U` with a free sheaf of modules on the slice site. -/
noncomputable def trivializationOfOverIso
    (M : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X') O'))
    (U : Opens ↥X') {I : Type u} (e : M.over U ≅ _root_.SheafOfModules.free I) :
    LocallyFreeRank.Trivialization X' (LocallyFreeRank.toRingSheaf X' O') M U :=
  ⟨I, (_root_.SheafOfModules.mapFreeIso (U.sheafOfModulesEquivOver
        (LocallyFreeRank.toRingSheaf X' O')).functor I
      (U.sheafOfModulesEquivOverUnit (LocallyFreeRank.toRingSheaf X' O')) ≪≫
    (U.sheafOfModulesEquivOver (LocallyFreeRank.toRingSheaf X' O')).functor.mapIso e.symm).symm⟩

/-- The index type of `trivializationOfOverIso M U e` is the index type `I` of the free
sheaf. -/
theorem trivializationOfOverIso_ι
    (M : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X') O'))
    (U : Opens ↥X') {I : Type u} (e : M.over U ≅ _root_.SheafOfModules.free I) :
    (trivializationOfOverIso M U e).ι = I := rfl

/-- A trivialization of rank `r` on a neighbourhood of `x` gives a basis of the stalk. -/
theorem nonempty_basis_stalk_of_trivialization
    (M : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X') O'))
    (x : ↥X') {U : Opens ↥X'} (hx : x ∈ U) {r : ℕ}
    (t : LocallyFreeRank.Trivialization X' (LocallyFreeRank.toRingSheaf X' O') M U)
    (ht : Nonempty (t.ι ≃ Fin r)) :
    Nonempty (Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk O'.obj x)
      ↑(TopCat.Presheaf.stalk M.val.presheaf x)) := by
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp X' O' M x hx t
  exact ⟨Module.Basis.ofRepr (e.trans (Finsupp.domLCongr ht.some))⟩

end Trivialization

attribute [local implicit_reducible] LocallyFreeRank.toRingSheaf in
/-- **The isomorphism criterion of [Stacks, Tag 0E9Y] for the canonical map.** On a space whose
structure-sheaf stalk at `x` is a local ring, the canonical map
`⋀^{r} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₁+r} E₀` is bijective on the stalk at `x` if and only if `F` is
free of rank `r` on an open neighbourhood of `x`. -/
theorem bijective_stalkMapL_detSourceMap_iff_exists_trivialization [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ (r₁ + r)]
    (x : ↥X) [IsLocalRing ↑(TopCat.Presheaf.stalk Osharp.obj x)] :
    Function.Bijective (PresheafOfModules.stalkMapL x
        (detSourceMap A₁ A₀ AF A₁d α π hαπ hS r₁ r).val) ↔
      ∃ U : Opens ↥X, x ∈ U ∧ ∃ t : LocallyFreeRank.Trivialization X
        (LocallyFreeRank.toRingSheaf X Osharp) F U, Nonempty (t.ι ≃ Fin r) := by
  rw [bijective_stalkMapL_detSourceMap_iff]
  constructor
  · intro hb
    obtain ⟨U, hx, ⟨e⟩⟩ :=
      exists_nhd_iso_free_of_bijective_stalkMapL_detSheafPairing A₁ A₀ AF α π hαπ hS r₁ r x hb
    exact ⟨U, hx, trivializationOfOverIso F U e, ⟨Equiv.ulift⟩⟩
  · rintro ⟨U, hx, t, ht⟩
    exact (bijective_stalkMapL_detSheafPairing_iff A₁ A₀ AF α π hαπ hS r₁ r x).2
      (nonempty_basis_stalk_of_trivialization F x hx t ht)

/-- **The canonical map of [Stacks, Tag 0E9Y] with the source's indexing**
`⋀^{r₀ - r₁} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₀} E₀`. The exterior degree `r₀ - r₁` is an integer, and
the exterior power in a negative degree is the zero sheaf (the negative-degree piece of the
exterior algebra), so for `r₁ > r₀` this is the zero map, as in the source. -/
noncomputable def sheafDeterminantMap [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] (r₀ : ℕ) :
    AF.exterior.piece ((r₀ : ℤ) - r₁) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁d.exteriorPower r₁)).obj
        (A₀.exteriorPower r₀) :=
  if h : r₁ ≤ r₀ then
    eqToHom (congrArg AF.exterior.piece (by omega)) ≫
      detSourceMap A₁ A₀ AF A₁d α π hαπ hS r₁ (r₀ - r₁) ≫
      eqToHom (congrArg (fun n => ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
        (A₁d.exteriorPower r₁)).obj (A₀.exteriorPower n)) (Nat.add_sub_cancel' h))
  else
    @Zero.zero _ (CategoryTheory.Limits.HasZeroMorphisms.zero
      (AF.exterior.piece ((r₀ : ℤ) - r₁))
      (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A₁d.exteriorPower r₁)).obj
        (A₀.exteriorPower r₀)))

/-- The stalk of a top exterior power of a finite locally free sheaf is free of rank one. -/
theorem nonempty_stalk_exteriorPower_self_linearEquiv {M : _root_.SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X) M)
    (n : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M n]
    (x : ↥X) :
    Nonempty (↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x) ≃ₗ[
      ↑(TopCat.Presheaf.stalk Osharp.obj x)] ↑(TopCat.Presheaf.stalk Osharp.obj x)) := by
  have := Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower A n n
  rw [Nat.choose_self] at this
  obtain ⟨e⟩ := nonempty_stalkLinearEquiv_finsupp (A.exteriorPower n) 1 x
  exact ⟨e.trans (Finsupp.LinearEquiv.finsuppUnique _ _ _)⟩

/-- In a negative degree the stalk of the exterior power vanishes. -/
theorem subsingleton_stalk_exterior_piece_of_neg {n : ℤ} (hn : n < 0) (x : ↥X) :
    Subsingleton ↑(TopCat.Presheaf.stalk (AF.exterior.piece n).val.presheaf x) := by
  have hzero : ∀ (W : Opens ↥X) (hW : x ∈ W) (s : (AF.exterior.piece n).val.obj (op W)),
      TopCat.Presheaf.germ (AF.exterior.piece n).val.presheaf W x hW s = 0 := fun W hW s =>
    (congrArg _ (AF.exteriorPiece_eq_zero_of_neg n hn (op W) s)).trans (map_zero _)
  refine ⟨fun a b => ?_⟩
  obtain ⟨U, hU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ a
  obtain ⟨V, hV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ b
  rw [hzero U hU s, hzero V hV t]

include A₁ in
/-- The stalk of the target of the canonical map is free of rank one, in particular nonzero
over a nonzero ring. -/
theorem nontrivial_stalk_target
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] (r₀ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ r₀] (x : ↥X)
    [Nontrivial ↑(TopCat.Presheaf.stalk Osharp.obj x)] :
    Nontrivial ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal Osharp
      (A₁d.exteriorPower r₁) (A₀.exteriorPower r₀)).presheaf x) := by
  obtain ⟨eD⟩ := nonempty_stalk_exteriorPower_dual_linearEquiv A₁d A₁ r₁ x
  obtain ⟨eM⟩ := nonempty_stalk_exteriorPower_self_linearEquiv A₀ r₀ x
  let e := (PresheafOfModules.tensorSheafStalkEquiv Osharp (A₁d.exteriorPower r₁)
    (A₀.exteriorPower r₀) x).trans ((TensorProduct.congr eD eM).trans
      (TensorProduct.lid _ _))
  exact e.toEquiv.nontrivial

attribute [local implicit_reducible] LocallyFreeRank.toRingSheaf in
/-- **The isomorphism criterion of [Stacks, Tag 0E9Y], with the source's indexing.** If the
stalk of the structure sheaf at `x` is a local ring, the canonical map
`⋀^{r₀ - r₁} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₀} E₀` is bijective on the stalk at `x` if and only if
`r₁ ≤ r₀` and `F` is free of rank `r₀ - r₁` on an open neighbourhood of `x`. -/
theorem bijective_stalkMapL_sheafDeterminantMap_iff [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] (r₀ : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ r₀]
    (x : ↥X) [IsLocalRing ↑(TopCat.Presheaf.stalk Osharp.obj x)] :
    Function.Bijective (PresheafOfModules.stalkMapL x
        (sheafDeterminantMap A₁ A₀ AF A₁d α π hαπ hS r₁ r₀).val) ↔
      r₁ ≤ r₀ ∧ ∃ U : Opens ↥X, x ∈ U ∧ ∃ t : LocallyFreeRank.Trivialization X
        (LocallyFreeRank.toRingSheaf X Osharp) F U, Nonempty (t.ι ≃ Fin (r₀ - r₁)) := by
  by_cases h : r₁ ≤ r₀
  · have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀
        (r₁ + (r₀ - r₁)) := by rwa [Nat.add_sub_cancel' h]
    rw [and_iff_right h]
    refine Iff.trans ?_ (bijective_stalkMapL_detSourceMap_iff_exists_trivialization A₁ A₀ AF A₁d
      α π hαπ hS r₁ (r₀ - r₁) x)
    unfold sheafDeterminantMap
    rw [dif_pos h]
    have hdeg : ((r₀ : ℤ) - r₁) = ((r₀ - r₁ : ℕ) : ℤ) := by omega
    have hpiece : ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
          (A₁d.exteriorPower r₁)).obj (A₀.exteriorPower (r₁ + (r₀ - r₁))) =
        ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
          (A₁d.exteriorPower r₁)).obj (A₀.exteriorPower r₀) :=
      congrArg (fun n => ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj
        (A₁d.exteriorPower r₁)).obj (A₀.exteriorPower n)) (Nat.add_sub_cancel' h)
    rw [@bijective_stalkMapL_iso_comp_iff _ _ _ _ _
        (eqToHom (congrArg AF.exterior.piece hdeg))
        (Iso.isIso_hom (eqToIso (congrArg AF.exterior.piece hdeg)))
        (detSourceMap A₁ A₀ AF A₁d α π hαπ hS r₁ (r₀ - r₁) ≫ eqToHom hpiece) x,
      @bijective_stalkMapL_comp_iso_iff _ _ _ _ _
        (detSourceMap A₁ A₀ AF A₁d α π hαπ hS r₁ (r₀ - r₁)) (eqToHom hpiece)
        (Iso.isIso_hom (eqToIso hpiece)) x]
  · refine iff_of_false (fun hb => ?_) (fun h' => h h'.1)
    have := nontrivial_stalk_target A₁ A₀ A₁d r₁ r₀ x
    have := subsingleton_stalk_exterior_piece_of_neg AF (n := (r₀ : ℤ) - r₁) (by omega) x
    obtain ⟨y, hy⟩ := exists_ne (0 : ↑(TopCat.Presheaf.stalk (PresheafOfModules.tensorSheafVal
      Osharp (A₁d.exteriorPower r₁) (A₀.exteriorPower r₀)).presheaf x))
    obtain ⟨z, hz⟩ := hb.2 y
    rw [Subsingleton.elim z 0, map_zero] at hz
    exact hy hz.symm

end Source

/-! ### On a locally ringed space, for the exterior powers of the space -/

section LocallyRingedSpace

open AlgebraicGeometry RingedSpaceModuleAdjunction

variable (Y : AlgebraicGeometry.LocallyRingedSpace.{u})
  {E₁ E₀ F : _root_.SheafOfModules.{u}
    (toRingCat (Opens.grothendieckTopology ↥Y.toRingedSpace.carrier) Y.toRingedSpace.sheaf)}
  (α : E₁ ⟶ E₀) (π : E₀ ⟶ F) (hαπ : α ≫ π = 0)
  (hS : (ShortComplex.mk α π hαπ).Exact) (r₁ r₀ : ℕ)

/-- **The canonical map of [Stacks, Tag 0E9Y] on a locally ringed space**,
`⋀^{r₀ - r₁} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₀} E₀`, for *the* exterior powers of the space
(`SheafOfModules.ringedSpaceAlgebras`), the dual `E₁^∨ = SheafHom(E₁, O_X)`, and the integer
exterior degree `r₀ - r₁` (the exterior power in a negative degree being the zero sheaf). -/
noncomputable def locallyRingedSpaceDeterminantMap [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁] :
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace F).exterior.piece
        ((r₀ : ℤ) - r₁) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj
        ((_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace (dualMod E₁)).exteriorPower
        r₁)).obj
        ((_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace E₀).exteriorPower r₀) :=
  sheafDeterminantMap (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace E₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace E₀)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace F)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace (dualMod E₁)) α π hαπ hS r₁ r₀

attribute [local implicit_reducible] LocallyFreeRank.toRingSheaf in
/-- **[Stacks, Tag 0E9Y].** Let `X` be a locally ringed space and `E₁ --α--> E₀ --π--> F ⟶ 0` an
exact sequence of `O_X`-modules with `E₁` and `E₀` finite locally free of ranks `r₁` and `r₀`.
The canonical map `⋀^{r₀ - r₁} F ⟶ ⋀^{r₁}(E₁^∨) ⊗ ⋀^{r₀} E₀` is an isomorphism on the stalk at
`x` if and only if `F` is locally free of rank `r₀ - r₁` on an open neighbourhood of `x`: that
is, `r₀ - r₁` is a natural number and `F` is free of that rank on some open `U ∋ x`. -/
@[stacks 0E9Y]
theorem isIso_stalkMap_locallyRingedSpaceDeterminantMap_iff [Epi π]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E₀ r₀]
    (x : ↥Y.toRingedSpace.carrier) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology ↥Y.toRingedSpace.carrier) Y.toRingedSpace.sheaf) x
        (locallyRingedSpaceDeterminantMap Y α π hαπ hS r₁ r₀)) ↔
      r₁ ≤ r₀ ∧ ∃ U : Opens ↥Y.toRingedSpace.carrier, x ∈ U ∧
        ∃ t : LocallyFreeRank.Trivialization Y.toRingedSpace.carrier
          (LocallyFreeRank.toRingSheaf Y.toRingedSpace.carrier Y.toRingedSpace.sheaf) F U,
          Nonempty (t.ι ≃ Fin (r₀ - r₁)) := by
  have : IsLocalRing ↑(TopCat.Presheaf.stalk Y.toRingedSpace.sheaf.obj x) := Y.isLocalRing x
  rw [ConcreteCategory.isIso_iff_bijective]
  exact bijective_stalkMapL_sheafDeterminantMap_iff
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace E₁)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace E₀)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace F)
    (_root_.SheafOfModules.ringedSpaceAlgebras Y.toRingedSpace (dualMod E₁)) α π hαπ hS r₁ r₀ x

end LocallyRingedSpace

end Stacks.Duality

end
