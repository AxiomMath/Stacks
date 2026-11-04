module

public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# A finite locally free sheaf of rank `n` has a local basis of germs

Let `X` be a scheme and let `ℰ` be a sheaf of `𝒪_X`-modules which is finite locally free of
rank `n`. Then every point `x` has an open neighbourhood `W` carrying `n` sections
`a : Fin n → Γ(ℰ, W)` whose germs at `x` form an `𝒪_{X,x}`-basis of the stalk `ℰ_x`, in the
form that `c ↦ ∑ j, c j • germ_x (a j)` is a bijection `(Fin n → 𝒪_{X,x}) → ℰ_x`.

## Main results

* `Stacks.SheafOfModules.exists_sections_germ_basis_of_nonempty_stalkBasis`: on a ringed space,
  a basis of a stalk indexed by `Fin n` is realised by `n` sections on a neighbourhood.
* `AlgebraicGeometry.nonempty_stalkBasis_of_isFiniteLocallyFreeOfRank`: the stalk of a finite
  locally free module of rank `n` admits a basis indexed by `Fin n`.
* `AlgebraicGeometry.exists_germ_basis_of_isFiniteLocallyFreeOfRank`: a finite locally free
  module of rank `n` has, around every point, `n` sections whose germs form a basis of the stalk.
* `AlgebraicGeometry.exists_germ_basis_of_isFiniteLocallyFreeOfRank_one`: the same at `n = 1`,
  stated with a single section.
* `AlgebraicGeometry.exists_germ_basis_unit`: the structure sheaf has a local germ basis of one
  element.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}}

/-- If the stalk `ℰ_x` has a basis over `𝒪_{X,x}` indexed by `Fin n`, then there are an open
`W ∋ x` and sections `a : Fin n → ℰ(W)` such that `c ↦ ∑ j, c j • germ_x (a j)` is a bijection
`(Fin n → 𝒪_{X,x}) → ℰ_x`. -/
theorem exists_sections_germ_basis_of_nonempty_stalkBasis
    (E : _root_.SheafOfModules.{u} (structureSheafRing X)) {n : ℕ} (x : X.carrier)
    (hbas : Nonempty (Module.Basis (Fin n) (ringStalk X x) (grpStalk X E.val x))) :
    ∃ (W : Opens X.carrier) (hx : x ∈ W) (a : Fin n → E.val.obj (op W)),
      Function.Bijective fun c : Fin n → ringStalk X x =>
        ∑ j, c j • grpGerm X E.val x W hx (a j) := by
  obtain ⟨bas⟩ := hbas
  choose V hV m hm using fun j : Fin n =>
    TopCat.Presheaf.exists_germ_eq (C := AddCommGrpCat.{u}) E.val.presheaf (bas j)
  obtain ⟨W, hxW, hle⟩ := exists_nbhd_le x V hV
  refine ⟨W, hxW, fun j => E.val.map (homOfLE (hle j)).op (m j), ?_⟩
  have ha : ∀ j, grpGerm X E.val x W hxW (E.val.map (homOfLE (hle j)).op (m j)) = bas j :=
    fun j => (TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) E.val.presheaf
      (homOfLE (hle j)) x hxW (m j)).trans (hm j)
  have hfun : (fun c : Fin n → ringStalk X x =>
      ∑ j, c j • grpGerm X E.val x W hxW (E.val.map (homOfLE (hle j)).op (m j)))
      = bas.equivFun.symm := by
    funext c
    rw [bas.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun j _ => congrArg (fun z => c j • z) (ha j)
  rw [hfun]
  exact bas.equivFun.symm.bijective

end Stacks.SheafOfModules

namespace AlgebraicGeometry

/-- The stalk at `x` of a finite locally free sheaf of modules of rank `n` on a scheme has a
basis indexed by `Fin n` over the local ring `𝒪_{X,x}`. -/
theorem nonempty_stalkBasis_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}}
    (E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (n : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) E n) (x : X) :
    Nonempty (Module.Basis (Fin n) (ringStalk X.toRingedSpace x)
      (grpStalk X.toRingedSpace E.val x)) := by
  rw [show Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace E.val x
      = PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.toRingedSpace.presheaf) E.val x from
        Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace E.val x]
  obtain ⟨q, hq, hr⟩ := hE.exists_isFiniteLocallyFreeOfRankData
  have hflf : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E :=
    { exists_isFiniteLocallyFreeData :=
        ⟨q, hq, { isFiniteType := fun i => ⟨Finite.of_equiv (Fin n) (hr i).some.symm⟩ }⟩ }
  obtain ⟨hft, hfree, -⟩ :=
    @Scheme.Modules.isFiniteType_and_free_stalks_and_isLocallyConstant_fiberRank X E hflf
  let A := ToType (ringStalk X.toRingedSpace x)
  let M := ToType (grpStalk X.toRingedSpace E.val x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.toRingedSpace.presheaf) E.val x
  have : Module.Free A M := hfree x
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u} E := hft
  have : Module.Finite A M := _root_.SheafOfModules.finite_stalk X.sheaf E x
  have : IsLocalRing A := X.isLocalRing x
  let b := Module.Free.chooseBasis A M
  let : Fintype (Module.Free.ChooseBasisIndex A M) := Fintype.ofFinite _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A M) = n :=
    (Module.finrank_eq_card_chooseBasisIndex A M).symm.trans
      ((@Scheme.Modules.fiberRank_eq_finrank_stalk X E x hft (hfree x)).symm.trans
        (@Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank X E n hE x))
  exact ⟨b.reindex (Fintype.equivFinOfCardEq hcard)⟩

/-- A finite locally free sheaf of modules `ℰ` of rank `n` on a scheme has, around every point
`x`, an open `W` and sections `a : Fin n → ℰ(W)` such that `c ↦ ∑ j, c j • germ_x (a j)` is a
bijection `(Fin n → 𝒪_{X,x}) → ℰ_x`. -/
theorem exists_germ_basis_of_isFiniteLocallyFreeOfRank {X : Scheme.{u}}
    (E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (n : ℕ)
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) E n) (x : X) :
    ∃ (W : X.Opens) (hx : x ∈ W) (a : Fin n → E.val.obj (op W)),
      Function.Bijective fun c : Fin n → ringStalk X.toRingedSpace x =>
        ∑ j, c j • grpGerm X.toRingedSpace E.val x W hx (a j) :=
  Stacks.SheafOfModules.exists_sections_germ_basis_of_nonempty_stalkBasis E x
    (nonempty_stalkBasis_of_isFiniteLocallyFreeOfRank E n hE x)

/-- A finite locally free sheaf of modules `ℰ` of rank one on a scheme has, around every point
`x`, an open `W` and a section `a ∈ ℰ(W)` such that `c ↦ c • germ_x a` is a bijection
`𝒪_{X,x} → ℰ_x`. -/
theorem exists_germ_basis_of_isFiniteLocallyFreeOfRank_one {X : Scheme.{u}}
    (E : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) E 1) (x : X) :
    ∃ (W : X.Opens) (hx : x ∈ W) (a : E.val.obj (op W)),
      Function.Bijective fun c : ringStalk X.toRingedSpace x =>
        c • grpGerm X.toRingedSpace E.val x W hx a := by
  obtain ⟨W, hx, a, hbij⟩ := exists_germ_basis_of_isFiniteLocallyFreeOfRank E 1 hE x
  refine ⟨W, hx, a 0, ?_⟩
  have hfun : (fun c : ringStalk X.toRingedSpace x =>
        c • grpGerm X.toRingedSpace E.val x W hx (a 0))
      = (fun c : Fin 1 → ringStalk X.toRingedSpace x =>
        ∑ j, c j • grpGerm X.toRingedSpace E.val x W hx (a j))
        ∘ (fun c : ringStalk X.toRingedSpace x => fun _ : Fin 1 => c) := by
    funext c
    exact (Finset.sum_singleton (f := fun j : Fin 1 =>
      c • grpGerm X.toRingedSpace E.val x W hx (a j)) 0).symm
  rw [hfun]
  exact hbij.comp
    ⟨fun c c' h => congrFun h 0, fun c => ⟨c 0, funext fun j => congrArg c (Subsingleton.elim 0 j)⟩⟩

/-- The structure sheaf `𝒪_X` of a scheme, as a sheaf of modules over itself, has around every
point `x` an open `W` and sections `a : Fin 1 → 𝒪_X(W)` such that `c ↦ ∑ j, c j • germ_x (a j)`
is a bijection `(Fin 1 → 𝒪_{X,x}) → 𝒪_{X,x}`. -/
theorem exists_germ_basis_unit {X : Scheme.{u}} (x : X) :
    ∃ (W : X.Opens) (hx : x ∈ W)
      (a : Fin 1 → (_root_.SheafOfModules.unit
        (structureSheafRing X.toRingedSpace)).val.obj (op W)),
      Function.Bijective fun c : Fin 1 → ringStalk X.toRingedSpace x =>
        ∑ j, c j • grpGerm X.toRingedSpace
          (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val x W hx (a j) := by
  refine exists_germ_basis_of_isFiniteLocallyFreeOfRank _ 1 ?_ x
  obtain ⟨q, hq, hr⟩ :=
    (Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_unit
      (R := structureSheafRing X.toRingedSpace)).exists_isFiniteLocallyFreeOfRankData
  exact { exists_isFiniteLocallyFreeOfRankData := ⟨q, hq, hr⟩ }

end AlgebraicGeometry

end
