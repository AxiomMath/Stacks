module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.Stalks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Injectivity near a stalk of a morphism into a coherent module

Let `φ : G ⟶ F` be a morphism of sheaves of modules with `G` of finite type and `F` coherent.
If the induced map on the stalk at a point `x` is injective, then the restriction of `φ` to
some open neighbourhood of `x` is a monomorphism.

Coherence of `F` makes the kernel `K` of `φ` of finite type, and injectivity on the stalk at `x`
says that `K_x` vanishes. Stacks 01B8, applied to the zero map into `K`, then gives a
neighbourhood on which every stalk of `K` vanishes, and vanishing of the kernel stalks is
injectivity of the stalk maps, hence — by the sheaf-theoretic criterion — injectivity of the
restricted morphism on sections.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.SheafOfModules.exists_isMono_over_of_stalk_injective`: an open neighbourhood on which
  the restricted morphism is a monomorphism.

## Implementation notes

Restriction to an open set is `SheafOfModules.Hom.over`, the morphism on the over-site of that
open; being a monomorphism there is injectivity of the restricted sheaf morphism. The stalk map
is the map of underlying additive stalks. The statement is for an arbitrary sheaf of rings on a
topological space, which covers a ringed space's structure sheaf.

Stacks 01B8 is stated for a sheaf of rings on a *ringed space*, so an auxiliary ringed space
with the same underlying topological space is supplied by `auxiliaryRingedSpace`; its structure
sheaf plays no role, since the statement applied only involves `R`.

## References

* [Stacks Project, Tag 01C0](https://stacks.math.columbia.edu/tag/01C0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}}
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  {G F : _root_.SheafOfModules.{u} R}

/-- A ringed space with underlying space `X`, used only to feed the ringed-space form of
Stacks 01B8; its structure sheaf is the constant sheaf of integers. -/
private noncomputable def auxiliaryRingedSpace (X : TopCat.{u}) :
    AlgebraicGeometry.RingedSpace.{u, u} :=
  { carrier := X
    presheaf :=
      (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
        (CommRingCat.of (ULift.{u} ℤ)) |>.obj
    IsSheaf :=
      ((CategoryTheory.constantSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
        (CommRingCat.of (ULift.{u} ℤ))).property }

private noncomputable def zeroModulePresheaf
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    PresheafOfModules.{u} R.obj :=
  { obj := fun U => ModuleCat.of (R.obj.obj U) (ULift.{u, 0} Unit)
    map := fun _ => 0
    map_id := by intro U; ext z; cases z with | up z => cases z; rfl
    map_comp := by intro U V W f g; ext z; cases z with | up z => cases z; rfl }

private theorem subsingleton_zeroModulePresheaf_obj
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    Subsingleton (ToType ((zeroModulePresheaf R).presheaf.obj (op U))) := by
  change Subsingleton (ULift.{u, 0} Unit)
  infer_instance

/-- An additive group all of whose elements are zero is a zero object. -/
private theorem isZero_of_forall_eq_zero {A : AddCommGrpCat.{u}} (h : ∀ a : A, a = 0) :
    IsZero A :=
  have : Subsingleton A := ⟨fun a b => (h a).trans (h b).symm⟩
  AddCommGrpCat.isZero_of_subsingleton _

private noncomputable def zeroModuleSheaf
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    _root_.SheafOfModules.{u} R where
  val := zeroModulePresheaf R
  isSheaf := by
    exact (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).2 fun ι U _ _ =>
      ⟨0, fun i => (subsingleton_zeroModulePresheaf_obj R (U i)).elim _ _,
        fun _ _ => (subsingleton_zeroModulePresheaf_obj R (iSup U)).elim _ _⟩

private theorem stalk_subsingleton_of_pointwise_subsingleton
    (P : TopCat.Presheaf AddCommGrpCat.{u} X)
    (hP : ∀ U : Opens X, Subsingleton (P.obj (op U))) (x : X) :
    Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) P x) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨U, hxU, s, rfl⟩ := P.exists_germ_eq a
  obtain ⟨V, hxV, t, rfl⟩ := P.exists_germ_eq b
  have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  have hs : P.map (homOfLE inf_le_left).op s = P.map (homOfLE inf_le_right).op t :=
    hP (U ⊓ V) |>.elim _ _
  rw [← P.germ_res_apply (homOfLE inf_le_left) x hxW s,
    ← P.germ_res_apply (homOfLE inf_le_right) x hxW t, hs]

private theorem mono_toSheaf_of_mono {M N : _root_.SheafOfModules.{u} R}
    (f : M ⟶ N) [Mono f] : Mono ((_root_.SheafOfModules.toSheaf R).map f) := by
  rw [Sheaf.Hom.mono_iff_presheaf_mono, NatTrans.mono_iff_mono_app]
  intro U
  change Mono ((forget₂ (ModuleCat (R.obj.obj U)) AddCommGrpCat).map
    ((_root_.SheafOfModules.evaluation R U).map f))
  exact Functor.map_mono (forget₂ (ModuleCat (R.obj.obj U)) AddCommGrpCat)
    ((_root_.SheafOfModules.evaluation R U).map f)

private theorem stalk_mono_of_explicit_mono {A B : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : A ⟶ B) (hf : Mono f) (x : X) :
    Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom) :=
  TopCat.Presheaf.stalk_mono_of_mono f x

private theorem exists_stalk_isZero_neighborhood
    (M : _root_.SheafOfModules.{u} R) [M.IsFiniteType] (x : X)
    (hx : IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} x).obj M.val.presheaf)) :
    ∃ U : Opens X, x ∈ U ∧ ∀ y : X, y ∈ U →
      IsZero ((TopCat.Presheaf.stalkFunctor Ab.{u} y).obj M.val.presheaf) := by
  let Xr := auxiliaryRingedSpace X
  let φ : zeroModuleSheaf R ⟶ M := 0
  have hsurj : Stacks.SheafOfModules.LocallySurjective.SurjOnStalk (X := Xr) (R := R) φ x := by
    intro a
    refine ⟨0, ?_⟩
    obtain rfl : a = 0 := (AddCommGrpCat.subsingleton_of_isZero hx).elim _ _
    simp [φ]
  obtain ⟨U, hxU, hU⟩ := Stacks.SheafOfModules.LocallySurjective.main_theorem (X := Xr) (R := R) φ
    (show _root_.SheafOfModules.IsFiniteType.{u, u, u} M from inferInstance) x hsurj
  refine ⟨U, hxU, fun y hy => ?_⟩
  have hsource : Subsingleton ((TopCat.Presheaf.stalkFunctor Ab.{u} y).obj
      (zeroModuleSheaf R).val.presheaf) := by
    exact stalk_subsingleton_of_pointwise_subsingleton _
      (subsingleton_zeroModulePresheaf_obj R) y
  refine isZero_of_forall_eq_zero fun a => ?_
  obtain ⟨c, hc⟩ := hU y hy a
  obtain rfl : c = 0 := hsource.elim _ _
  have hzero : (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
        (Stacks.SheafOfModules.LocallySurjective.underlyingAb (X := Xr) (R := R) φ))) 0 = 0 := by
    simp [Stacks.SheafOfModules.LocallySurjective.underlyingAb, φ]
  exact hc.symm.trans hzero

private theorem stalk_injective_of_kernel_stalk_isZero
    (φ : G ⟶ F) (x : X)
    (hK : IsZero ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).obj
      (kernel φ))) :
    Function.Injective (ConcreteCategory.hom
      ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).map φ)) := by
  let S : ShortComplex (_root_.SheafOfModules.{u} R) := ShortComplex.kernelSequence φ
  have hSx := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact R S).mp
    (ShortComplex.kernelSequence_exact φ) x
  let T := AlgebraicGeometry.SheafOfModules.stalkShortComplex R S x
  let gx := T.g
  intro a b hab
  change (ConcreteCategory.hom gx) a = (ConcreteCategory.hom gx) b at hab
  have hmem : a - b ∈ gx.hom.ker := by
    change gx.hom (a - b) = 0
    exact (map_sub (ConcreteCategory.hom gx) a b).trans (sub_eq_zero.mpr hab)
  obtain ⟨c, hc⟩ := (ShortComplex.ab_exact_iff_ker_le_range).mp hSx hmem
  obtain rfl : c = 0 := (AddCommGrpCat.subsingleton_of_isZero hK).elim _ _
  -- `hc` lives at `↑T.X₂` and the goal at `↑(Fst.obj G)`; those are the same type, but only
  -- after unfolding `stalkShortComplex`, which `simp` will not do. So state the equation at
  -- `T.X₂` and let `exact`'s defeq check cross the boundary.
  exact sub_eq_zero.mp (hc.symm.trans (map_zero _))

/-- **Stacks Project, Tag 01C0.** A morphism from a finite-type sheaf of modules to a coherent
sheaf of modules which is injective on one stalk is injective after restriction to a
neighbourhood of that point. -/
@[stacks 01C0]
theorem exists_isMono_over_of_stalk_injective
    (φ : G ⟶ F) [G.IsFiniteType] [F.IsCoherent] (x : X)
    (hx : Function.Injective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val)))) :
    ∃ U : Opens X, x ∈ U ∧ Mono (φ.over U) := by
  let K := kernel φ
  -- `SheafOfModules.IsCoherent` and `Stacks.SheafOfModules.IsCoherent` are the same two-field
  -- class under two names; `isFiniteType_kernel_of_isCoherent` asks for the latter, so convert
  -- field by field, as `Stacks.SheafOfModules.isCoherent_iff_isFinitePresentation` does.
  have hCoh : IsCoherent F :=
    ⟨_root_.SheafOfModules.IsCoherent.isFiniteType,
      _root_.SheafOfModules.IsCoherent.kernel_isFiniteType⟩
  have : K.IsFiniteType := isFiniteType_kernel_of_isCoherent φ
  have hKx : IsZero ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x).obj K) := by
    let Fst := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor R x
    have hx' : Function.Injective (ConcreteCategory.hom (Fst.map φ)) := hx
    have hkinj : Function.Injective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((_root_.SheafOfModules.toSheaf R).map (kernel.ι φ)).hom))) :=
      (AddCommGrpCat.mono_iff_injective _).1
        (stalk_mono_of_explicit_mono _ (mono_toSheaf_of_mono (kernel.ι φ)) x)
    have hk (c : Fst.obj K) : (ConcreteCategory.hom (Fst.map φ))
        ((ConcreteCategory.hom (Fst.map (kernel.ι φ))) c) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, kernel.condition, Functor.map_zero]
      simp
    exact isZero_of_forall_eq_zero fun a => hkinj (hx' ((hk a).trans (hk 0).symm))
  obtain ⟨U, hxU, hKU⟩ := exists_stalk_isZero_neighborhood K x hKx
  have hφy : ∀ y : X, y ∈ U → Function.Injective
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((PresheafOfModules.toPresheaf R.obj).map φ.val))) :=
    fun y hy => stalk_injective_of_kernel_stalk_isZero φ y (hKU y hy)
  refine ⟨U, hxU, ?_⟩
  apply (_root_.SheafOfModules.forget (R.over U)).mono_of_mono_map
  apply (PresheafOfModules.toPresheaf (R.over U).obj).mono_of_mono_map
  refine (NatTrans.mono_iff_mono_app _).2 fun V => ?_
  let W := Opposite.op V.unop.left
  have hApp := TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
      (C := AddCommGrpCat.{u})
      (((_root_.SheafOfModules.toSheaf R).map φ).hom) V.unop.left
      (fun y hy => by
        change Function.Injective (ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
            (((_root_.SheafOfModules.toSheaf R).map φ).hom)))
        exact hφy y ((V.unop.hom.le : V.unop.left ≤ U) hy))
  have hGroup : Mono ((forget₂ (ModuleCat (R.obj.obj W)) AddCommGrpCat).map
      ((_root_.SheafOfModules.evaluation R W).map φ)) :=
    (AddCommGrpCat.mono_iff_injective _).2 hApp
  have heq :
      (((PresheafOfModules.toPresheaf (R.over U).obj).map
        ((_root_.SheafOfModules.forget (R.over U)).map (φ.over U))).app V) =
      (forget₂ (ModuleCat (R.obj.obj W)) AddCommGrpCat).map
        ((_root_.SheafOfModules.evaluation R W).map φ) := by
    ext a
    rfl
  exact heq ▸ hGroup

end Stacks.SheafOfModules

end
