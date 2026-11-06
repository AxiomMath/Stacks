module

public import StacksFrontier.AlgebraicGeometry.RingedSpace.TorsionFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import Mathlib.Algebra.GroupWithZero.Action.Regular

/-!
# Torsion freeness over the target, on submodules and from the sections

Let `f : X ⟶ Y` be a morphism of ringed spaces and `F` an `𝒪_X`-module.  Torsion freeness of
`F` over `Y` at a point `x` asks that the regular elements of the local ring `𝒪_{Y, f(x)}` act
injectively on the stalk `F_x` (`AlgebraicGeometry.IsTorsionFreeOverAt`).  This file proves two
facts about that condition.

First, it passes to submodules: a monomorphism `G ⟶ F` of `𝒪_X`-modules is injective on stalks
and linear over `𝒪_{X, x}`, so a regular element acting injectively on `F_x` acts injectively on
`G_x`.

Second, it can be read on the sections.  Suppose every regular element `a` of `𝒪_{Y, f(x)}`
divides the germ of a section `r` of `𝒪_Y` over a neighbourhood `V` of `f(x)` whose pullback
acts injectively on the sections of `F` over every open `U ∋ x` inside `f⁻¹(V)`.  Then `F` is
torsion free over `Y` at `x`: if `a • m = 0` in `F_x`, then also `r • m = 0`, and `m` is the germ
of a section killed by `r` on a smaller open, hence zero there.

## Main results

* `AlgebraicGeometry.stalkMap_smul`: the stalk map of a morphism of `𝒪_X`-modules is linear over
  the local ring `𝒪_{X, x}`.
* `AlgebraicGeometry.IsTorsionFreeOverAt.of_mono` and
  `AlgebraicGeometry.IsTorsionFreeOver.of_mono`: torsion freeness over the target passes to
  submodules.
* `AlgebraicGeometry.isTorsionFreeOverAt_of_forall_dvd_germ`: the criterion on sections above.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable {X Y : AlgebraicGeometry.RingedSpace.{u}}

/-- **The stalk map of a morphism of `𝒪_X`-modules is linear over the local ring `𝒪_{X, x}`.**
The stalk of an `𝒪_X`-module carries the action of the commutative local ring of `X` at `x`, and
the map induced on stalks by a morphism of modules commutes with it: on germs this is the
linearity of the morphism over the sections of `𝒪_X`. -/
theorem stalkMap_smul {G F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)} (φ : G ⟶ F) (x : X) :
    let MG : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := G.val
    let MF : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
    let ψ : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MG.presheaf x →
        TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MF.presheaf x :=
      fun m => (SheafOfModules.stalkMap _ x φ).hom m
    ∀ (b : X.presheaf.stalk x) (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MG.presheaf x),
      ψ (b • m) = b • ψ m := by
  intro MG MF ψ b m
  obtain ⟨Ub, hxb, b', rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf b
  obtain ⟨Um, hxm, m', rfl⟩ := TopCat.Presheaf.exists_germ_eq MG.presheaf m
  let U : Opens X := Ub ⊓ Um
  have hxU : x ∈ U := ⟨hxb, hxm⟩
  let iUb : U ⟶ Ub := homOfLE inf_le_left
  let iUm : U ⟶ Um := homOfLE inf_le_right
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf iUb x hxU b',
    ← TopCat.Presheaf.germ_res_apply MG.presheaf iUm x hxU m']
  set b'' : X.presheaf.obj (op U) := X.presheaf.map iUb.op b'
  set m'' : MG.obj (op U) := MG.map iUm.op m'
  let φU : MG.obj (op U) → MF.obj (op U) := fun n => φ.val.app (op U) n
  have hψ : ∀ n : MG.obj (op U), ψ (TopCat.Presheaf.germ MG.presheaf U x hxU n) =
      TopCat.Presheaf.germ MF.presheaf U x hxU (φU n) := fun n =>
    SheafOfModules.stalkMap_germ _ x φ U hxU n
  calc ψ (X.presheaf.germ U x hxU b'' • TopCat.Presheaf.germ MG.presheaf U x hxU m'')
      = ψ (TopCat.Presheaf.germ MG.presheaf U x hxU (b'' • m'')) :=
        congrArg ψ (PresheafOfModules.germ_smul MG x U hxU b'' m'').symm
    _ = TopCat.Presheaf.germ MF.presheaf U x hxU (φU (b'' • m'')) := hψ _
    _ = TopCat.Presheaf.germ MF.presheaf U x hxU (b'' • φU m'') :=
        congrArg _ ((φ.val.app (op U)).hom.map_smul b'' m'')
    _ = X.presheaf.germ U x hxU b'' • TopCat.Presheaf.germ MF.presheaf U x hxU (φU m'') :=
        PresheafOfModules.germ_smul MF x U hxU b'' _
    _ = X.presheaf.germ U x hxU b'' • ψ (TopCat.Presheaf.germ MG.presheaf U x hxU m'') :=
        congrArg _ (hψ m'').symm

variable (f : X ⟶ Y)

/-- **Torsion freeness over the target passes to submodules, at a point.**  If `G ⟶ F` is a
monomorphism of `𝒪_X`-modules and `F` is torsion free over `Y` at `x`, so is `G`: the stalk
map is injective and linear over `𝒪_{X, x}`, hence over `𝒪_{Y, f(x)}`. -/
theorem IsTorsionFreeOverAt.of_mono {G F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)} (φ : G ⟶ F) [Mono φ]
    {x : X} (h : IsTorsionFreeOverAt f F x) : IsTorsionFreeOverAt f G x := by
  let MG : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := G.val
  let MF : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MF.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  let : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MG.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  have : Module.IsTorsionFree (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MF.presheaf x) := h
  show Module.IsTorsionFree (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MG.presheaf x)
  let ψ : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MG.presheaf x →
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MF.presheaf x :=
    fun m => (SheafOfModules.stalkMap _ x φ).hom m
  exact Function.Injective.moduleIsTorsionFree (R := Y.presheaf.stalk (f.hom.base x)) ψ
    ((SheafOfModules.mono_iff_injective_stalkMap φ).1 inferInstance x)
    (fun a m => stalkMap_smul φ x ((f.hom.stalkMap x).hom a) m)

/-- **Torsion freeness over the target passes to submodules.**  A submodule of an `𝒪_X`-module
torsion free over `Y` is torsion free over `Y`. -/
theorem IsTorsionFreeOver.of_mono {G F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)} (φ : G ⟶ F) [Mono φ]
    (h : IsTorsionFreeOver f F) : IsTorsionFreeOver f G :=
  fun x => (h x).of_mono f φ

/-- **Torsion freeness over the target is invariant under isomorphism.** -/
theorem IsTorsionFreeOver.of_iso {G F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)} (e : G ≅ F)
    (h : IsTorsionFreeOver f F) : IsTorsionFreeOver f G :=
  h.of_mono f e.hom

/-- **Torsion freeness over the target, read on the sections.**  Let `x` be a point of `X` and
suppose that every regular element `a` of the local ring `𝒪_{Y, f(x)}` divides the germ at `f(x)`
of a section `r` of `𝒪_Y` over an open `V ∋ f(x)` such that, for every open `U ∋ x` of `X`
contained in `f⁻¹(V)`, the restriction to `U` of the pullback of `r` acts injectively on the
sections of `F` over `U`.  Then `F` is torsion free over `Y` at `x`. -/
theorem isTorsionFreeOverAt_of_forall_dvd_germ (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)) (x : X)
    (h : ∀ a : Y.presheaf.stalk (f.hom.base x), IsRegular a →
      ∃ (V : Opens Y) (hV : f.hom.base x ∈ V) (r : Y.presheaf.obj (op V)),
        a ∣ Y.presheaf.germ V (f.hom.base x) hV r ∧
        ∀ (U : Opens X) (_ : x ∈ U) (hUV : U ≤ (Opens.map f.hom.base).obj V),
          Function.Injective fun m : (show PresheafOfModules.{u}
              (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) from F.val).obj (op U) =>
            (X.presheaf.map (homOfLE hUV).op (f.hom.c.app (op V) r) : X.presheaf.obj (op U)) •
              m) :
    IsTorsionFreeOverAt f F x := by
  let MF : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) := F.val
  let : Module (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MF.presheaf x) :=
    Module.compHom _ (f.hom.stalkMap x).hom
  show Module.IsTorsionFree (Y.presheaf.stalk (f.hom.base x))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) MF.presheaf x)
  refine ⟨fun a ha => ?_⟩
  obtain ⟨V, hV, r, ⟨c, hc⟩, hinj⟩ := h a ha
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro m hm
  have hrm : ((f.hom.stalkMap x).hom (Y.presheaf.germ V (f.hom.base x) hV r)) • m = 0 := by
    rw [hc, map_mul, mul_comm, mul_smul]
    show ((f.hom.stalkMap x).hom c) • (a • m) = 0
    rw [hm, smul_zero]
  obtain ⟨U₀, hxU₀, m', rfl⟩ := TopCat.Presheaf.exists_germ_eq MF.presheaf m
  let U : Opens X := U₀ ⊓ (Opens.map f.hom.base).obj V
  have hxU : x ∈ U := ⟨hxU₀, hV⟩
  let iU₀ : U ⟶ U₀ := homOfLE inf_le_left
  have hUV : U ≤ (Opens.map f.hom.base).obj V := inf_le_right
  let s : X.presheaf.obj (op U) := X.presheaf.map (homOfLE hUV).op (f.hom.c.app (op V) r)
  let m'' : MF.obj (op U) := MF.map iU₀.op m'
  have hgerm : (f.hom.stalkMap x).hom (Y.presheaf.germ V (f.hom.base x) hV r) =
      X.presheaf.germ U x hxU s := by
    rw [PresheafedSpace.stalkMap_germ_apply]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hUV) x hxU _).symm
  have hm'' : TopCat.Presheaf.germ MF.presheaf U₀ x hxU₀ m' =
      TopCat.Presheaf.germ MF.presheaf U x hxU m'' :=
    (TopCat.Presheaf.germ_res_apply MF.presheaf iU₀ x hxU m').symm
  rw [hgerm, hm''] at hrm
  change X.presheaf.germ U x hxU s • TopCat.Presheaf.germ MF.presheaf U x hxU m'' = 0 at hrm
  rw [← PresheafOfModules.germ_smul MF x U hxU,
    ← map_zero (TopCat.Presheaf.germ MF.presheaf U x hxU).hom] at hrm
  obtain ⟨W, hxW, iWU, iWU', heq⟩ := TopCat.Presheaf.germ_eq MF.presheaf x hxU hxU _ _ hrm
  have hWV : W ≤ (Opens.map f.hom.base).obj V := (leOfHom iWU).trans hUV
  have hzero : MF.map iWU.op m'' = 0 := by
    refine hinj W hxW hWV ?_
    show X.presheaf.map (homOfLE hWV).op (f.hom.c.app (op V) r) • MF.map iWU.op m'' =
      X.presheaf.map (homOfLE hWV).op (f.hom.c.app (op V) r) • 0
    rw [smul_zero]
    have h1 : MF.map iWU.op (s • m'') = 0 := heq.trans (map_zero _)
    rw [PresheafOfModules.map_smul] at h1
    refine Eq.trans ?_ h1
    congr 1
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp (homOfLE hUV).op iWU.op) _
  rw [hm'', ← TopCat.Presheaf.germ_res_apply MF.presheaf iWU x hxW m'']
  exact (congrArg _ hzero).trans (TopCat.Presheaf.germ MF.presheaf W x hxW).hom.map_zero

end AlgebraicGeometry

end
