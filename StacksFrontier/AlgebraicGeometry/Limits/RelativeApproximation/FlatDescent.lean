module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.AffineOpen
import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Algebra.DirectLimit.Descent
public import StacksFrontier.RingTheory.Flat.ClosedSubset
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus

/-!
# Descending relative flatness of a finitely presented module

Let a scheme be the limit of a cofiltered inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms. A finitely presented quasi-coherent module on a scheme
of finite presentation over one stage, which becomes flat over another such scheme after pullback
to the limit, is already flat after pullback to some later stage.

## Main results

* `AlgebraicGeometry.eventually_isFlatOver_modulePullback`: flatness of a finitely presented
  module descends to a finite stage.

## Implementation notes

Schemes over a stage are objects of its over category, so all the morphisms and module pullbacks
in the statement are the canonical ones supplied by `CategoryTheory.Over.pullback` and the
pullback projections. An essentially small cofiltered category stands in for the directed indexing
set of the source: smallness is relative to the scheme universe, because the source takes limits
in the category of all schemes and a limit taken in a smaller universe need not remain a limit
after enlarging it. The object and morphism universes of the indexing category remain independent.

On an affine chart the module on the inverse limit is the module at the initial stage tensored
with the colimit of the coordinate rings, which is what reduces the statement to the directed
flatness theorem for modules over a filtered colimit of rings.

## References

* [Stacks Project, Tag 05LY](https://stacks.math.columbia.edu/tag/05LY)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open scoped TensorProduct

universe w v u

namespace AlgebraicGeometry

/-! ### Reading a module on a scheme as a module on its underlying ringed space

`AlgebraicGeometry.Scheme.Modules` is *by definition* the sheaves of modules on the underlying
ringed space, but it is a `def`, so typeclass search does not cross between the two spellings. The
three lemmas below state that identification once, as checked facts, and everything downstream
goes through them instead of relying on the elaborator to unfold. -/

/-- Quasi-coherence of a module on a scheme, read on the underlying ringed space. -/
public lemma isQuasicoherent_ringSheaf {X : Scheme.{u}} (F : X.Modules)
    [hF : F.IsQuasicoherent] :
    SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F := hF

/-- Quasi-coherence of a module on the underlying ringed space, read on the scheme. -/
private lemma isQuasicoherent_scheme {X : Scheme.{u}}
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [hF : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F := hF

/-- Finite presentation of a module on the underlying ringed space, read on the scheme. -/
private lemma isFinitePresentation_scheme {X : Scheme.{u}}
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [hF : SheafOfModules.IsFinitePresentation.{u, u, u}
      (R := structureSheafRing X.toRingedSpace) F] :
    SheafOfModules.IsFinitePresentation.{u, u, u} (R := X.ringCatSheaf) F := hF

/-- **Stacks 01U8** for a morphism of schemes: the pullback of a quasi-coherent module flat over
the base is flat over the new base. -/
private lemma pullback_isFlatOver {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g)
    (F : X.Modules) [hF : F.IsQuasicoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsFlatOver f'.toLRSHom.toShHom ((Scheme.Modules.pullback g').obj F) :=
  @modulePullback_isFlatOver _ _ _ _ f g g' f' h F hF hflat

/-- **Stacks 01BQ** for a morphism of schemes: the pullback of a finitely presented module is
finitely presented. -/
private lemma pullback_isFinitePresentation {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    [hF : F.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj F).IsFinitePresentation :=
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ f.toLRSHom.toShHom F hF


/-- The stages obtained by pulling a scheme over `D.obj i₀` back along all
arrows into `i₀` form a limit diagram. -/
private noncomputable def isLimit_baseChange_diagram
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i₀ : I) (X₀ : Over (D.obj i₀)) :
    IsLimit ((Over.pullback X₀.hom ⋙ Over.forget _).mapCone
      ((Over.conePost D i₀).obj c)) :=
  isLimitOfPreserves (Over.pullback X₀.hom ⋙ Over.forget _) (Over.isLimitConePost i₀ hc)

/-- In the affine case, every stage of the base-changed diagram is affine. -/
private lemma isAffine_baseChange_stage
    {I : Type v} [Category.{w} I] (D : I ⥤ Scheme.{u}) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (X₀ : Over (D.obj i₀)) [IsAffine X₀.left] (A : Over i₀) :
    IsAffine ((Over.post D ⋙ Over.pullback X₀.hom ⋙ Over.forget _).obj A) := by
  have : IsAffineHom (D.map A.hom) := inferInstance
  exact IsAffine.of_isPullback
    (IsPullback.of_hasPullback (D.map A.hom) X₀.hom).flip

/-- Global sections of the affine base-change diagram form a filtered colimit. -/
private lemma sections_colimit_baseChange_diagram
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (X₀ : Over (D.obj i₀)) [IsAffine X₀.left] :
    let _F := Over.post D ⋙ Over.pullback X₀.hom ⋙ Over.forget _
    let c' := (Over.pullback X₀.hom ⋙ Over.forget _).mapCone
      ((Over.conePost D i₀).obj c)
    Nonempty (IsColimit (Scheme.Γ.mapCocone c'.op)) := by
  let F := Over.post D ⋙ Over.pullback X₀.hom ⋙ Over.forget _
  let c' : Cone F := (Over.pullback X₀.hom ⋙ Over.forget _).mapCone
    ((Over.conePost D i₀).obj c)
  have : ∀ {A B : Over i₀} (g : A ⟶ B), IsAffineHom (F.map g) := by
    intro A B g
    have : IsAffineHom ((Over.post D).map g).left := by
      change IsAffineHom (D.map g.left)
      infer_instance
    exact MorphismProperty.overPullbackMap (P := @IsAffineHom) X₀.hom
      ((Over.post D).map g) inferInstance
  have (A : Over i₀) : IsAffine (F.obj A) := isAffine_baseChange_stage D i₀ X₀ A
  have (A : Over i₀) : CompactSpace (F.obj A) := inferInstance
  have (A : Over i₀) : QuasiSeparatedSpace (F.obj A) := inferInstance
  have : ∀ A : (Over i₀)ᵒᵖ, IsAffine (F.op.obj A).unop := fun A =>
    isAffine_baseChange_stage D i₀ X₀ A.unop
  exact ⟨isColimitOfPreserves Scheme.Γ (isLimit_baseChange_diagram D c hc i₀ X₀).op⟩

/-- A directed colimit of rings whose structure maps respect a fixed algebra
structure is a directed colimit in the elementwise sense used by flat descent. -/
private theorem isDirectedColimit_of_ringCocone
    {R : Type u} [CommRing R] {α : Type v} [Preorder α]
    [Nonempty α] [IsDirected α (· ≤ ·)] (F : α ⥤ CommRingCat.{u})
    (c : Cocone F) [∀ i, Algebra R (F.obj i)] [Algebra R c.pt]
    (b : ∀ i j (_h : i ≤ j), F.obj i →ₐ[R] F.obj j)
    (g : ∀ i, F.obj i →ₐ[R] c.pt)
    (hb : ∀ i j (h : i ≤ j), (b i j h).toRingHom = (F.map (homOfLE h)).hom)
    (hg : ∀ i, (g i).toRingHom = (c.ι.app i).hom)
    (hc : IsColimit ((forget CommRingCat.{u}).mapCocone c)) :
    IsDirectedColimit (fun i => F.obj i) (fun i j h => b i j h) c.pt g := by
  have hb_apply : ∀ i j (h : i ≤ j) x,
      b i j h x = (F.map (homOfLE h)).hom x := fun i j h x =>
    congrArg (fun f : F.obj i →+* F.obj j => f x) (hb i j h)
  have hg_apply : ∀ i x, g i x = (c.ι.app i).hom x := fun i x =>
    congrArg (fun f : F.obj i →+* c.pt => f x) (hg i)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk x
    rw [hb_apply, hb_apply, hb_apply]
    exact (ConcreteCategory.congr_hom
      (F.map_comp (homOfLE hij) (homOfLE hjk)) x).symm
  · intro i x
    rw [hb_apply]
    exact ConcreteCategory.congr_hom (F.map_id i) x
  · intro i j hij x
    rw [hg_apply, hg_apply, hb_apply]
    exact ConcreteCategory.congr_hom (c.w (homOfLE hij)) x
  · intro x
    obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ⟨i, a, (hg_apply i a).trans ha⟩
  · intro i x hx
    have he : ((forget CommRingCat.{u}).mapCocone c).ι.app i x =
        ((forget CommRingCat.{u}).mapCocone c).ι.app i (0 : F.obj i) := by
      change (c.ι.app i).hom x = (c.ι.app i).hom 0
      rw [← hg_apply, hx]
      simp
    obtain ⟨j, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hc x (0 : F.obj i)).mp he
    refine ⟨j, leOfHom f, ?_⟩
    rw [hb_apply, Subsingleton.elim (homOfLE (leOfHom f)) f]
    simpa using hf

/-- Base changing a directed system of algebras along a module `M` gives a directed system, for
any family of maps that agree with `rTensor` of the algebra maps. -/
private theorem directedSystem_rTensor
    {α : Type v} [Preorder α] {R : Type u} [CommRing R]
    {B : α → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (f : ∀ i j, i ≤ j → B i →ₐ[R] B j) (M : Type u) [AddCommGroup M] [Module R M]
    (hid : ∀ i x, f i i le_rfl x = x)
    (hcomp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
      f j k hjk (f i j hij x) = f i k (hij.trans hjk) x)
    (n : ∀ i j, i ≤ j → B i ⊗[R] M → B j ⊗[R] M)
    (hn : ∀ i j h x, n i j h x = LinearMap.rTensor M (f i j h).toLinearMap x) :
    DirectedSystem (fun i => B i ⊗[R] M) (fun i j h => n i j h) := by
  constructor
  · intro i x
    rw [hn, show (f i i le_rfl).toLinearMap = LinearMap.id from LinearMap.ext (hid i)]
    exact LinearMap.rTensor_id_apply M (B i) x
  · intro k j i hij hjk x
    rw [hn j k hjk, hn i j hij, hn i k _, ← LinearMap.rTensor_comp_apply]
    exact congrArg (fun l => LinearMap.rTensor M l x) (LinearMap.ext (hcomp i j k hij hjk))

/-! ### The affine module colimit bridge

For an affine chart, the module on the inverse limit is obtained by tensoring the
module at the initial stage with the colimit of the source rings.  The following
lemma packages the elementwise colimit data required by Stacks 02JO (3). -/

private theorem tensor_module_colimit_data
    {α : Type v} [Preorder α] [Nonempty α] [IsDirected α (· ≤ ·)]
    (R : Type u) [CommRing R]
    (B : α → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (f : ∀ i j, i ≤ j → B i →ₐ[R] B j)
    (S : Type u) [CommRing S] [Algebra R S]
    (g : ∀ i, B i →ₐ[R] S)
    (hc : IsDirectedColimit B f S g)
    (M : Type u) [AddCommGroup M] [Module R M] :
    let N : α → Type u := fun i => B i ⊗[R] M
    let q : ∀ i j, i ≤ j → N i →ₗ[R] N j := fun i j h =>
      LinearMap.rTensor M (f i j h).toLinearMap
    let ν : ∀ i, N i →ₗ[R] S ⊗[R] M := fun i =>
      LinearMap.rTensor M (g i).toLinearMap
    (∀ i j (h : i ≤ j) x, ν j (q i j h x) = ν i x) ∧
      (∀ y : S ⊗[R] M, ∃ i x, ν i x = y) ∧
      (∀ i x, ν i x = 0 → ∃ j, ∃ h : i ≤ j, q i j h x = 0) := by
  classical
  let N : α → Type u := fun i => B i ⊗[R] M
  let q : ∀ i j, i ≤ j → N i →ₗ[R] N j := fun i j h =>
    LinearMap.rTensor M (f i j h).toLinearMap
  let ν : ∀ i, N i →ₗ[R] S ⊗[R] M := fun i =>
    LinearMap.rTensor M (g i).toLinearMap
  have hrc : IsRingColimit R B f S g := by
    refine ⟨fun i _ x => hc.map_id i x, fun i j k hij hjk x => hc.map_comp hij hjk x,
      fun i j h x => hc.comp h x, hc.jointly_surjective, fun i a b hab => ?_⟩
    obtain ⟨j, h, hj⟩ := hc.exists_eq_zero (a - b) (by rw [map_sub, sub_eq_zero]; exact hab)
    refine ⟨j, h, ?_⟩
    change f i j h (a - b) = 0 at hj
    rwa [map_sub, sub_eq_zero] at hj
  have hdsB : DirectedSystem B (fun i j h => (f i j h).toLinearMap) :=
    hrc.directedSystem
  have hdsN : DirectedSystem N (fun i j h => q i j h) :=
    directedSystem_rTensor f M hc.map_id (fun _ _ _ hij hjk x => hc.map_comp hij hjk x) _
      fun _ _ _ _ => rfl
  let DL := Module.DirectLimit B (fun i j h => (f i j h).toLinearMap)
  let eB : DL ≃ₗ[R] S := hrc.linearEquivDirectLimit R B f S g
  let eN : S ⊗[R] M ≃ₗ[R] Module.DirectLimit N (fun i j h => q i j h) :=
    (LinearEquiv.rTensor M eB.symm).trans
      (TensorProduct.directLimitLeft (fun i j h => (f i j h).toLinearMap) M)
  have heB (i : α) (x : B i) : eB.symm (g i x) =
      Module.DirectLimit.of R α B (fun i j h => (f i j h).toLinearMap) i x :=
    eB.symm_apply_eq.mpr (hrc.linearEquivDirectLimit_of R B f S g i x).symm
  have heN (i : α) (x : N i) : eN (ν i x) =
      Module.DirectLimit.of R α N (fun i j h => q i j h) i x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
        change (TensorProduct.directLimitLeft
          (fun i j h => (f i j h).toLinearMap) M)
          (eB.symm (g i b) ⊗ₜ[R] m) = _
        rw [heB i b]
        exact TensorProduct.directLimitLeft_tmul_of
          (fun i j h => (f i j h).toLinearMap) M b m
    | add x y hx hy => simp [map_add, hx, hy]
  refine ⟨fun i j h x => ?_, fun y => ?_, fun i x hx => ?_⟩
  · change LinearMap.rTensor M (g j).toLinearMap
        (LinearMap.rTensor M (f i j h).toLinearMap x) = _
    rw [← LinearMap.rTensor_comp_apply]
    have hgf : (g j).toLinearMap.comp (f i j h).toLinearMap =
        (g i).toLinearMap := by
      ext y
      exact hc.comp h y
    rw [hgf]
  · obtain ⟨i, x, hx⟩ := Module.DirectLimit.exists_of (eN y)
    exact ⟨i, x, eN.injective (by rw [heN, hx])⟩
  · exact Module.DirectLimit.of.zero_exact (by rw [← heN, hx, map_zero])

/-! ### Flatness in the tensor module colimit

The module on an affine source chart at each stage is obtained from its
initial module by extension of scalars.  This bridge applies the directed
flatness theorem to that system, using the elementwise module-colimit data
above. -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem tensor_module_eventually_flat
    {α : Type v} [PartialOrder α] [Nonempty α] [IsDirected α (· ≤ ·)]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (A : α → Type u) (B : α → Type u)
    [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
    {R₀ : Type u} [CommRing R₀] (M₀ : Type u) [AddCommGroup M₀]
    [Module R₀ M₀] [Module.FinitePresentation R₀ M₀]
    [Algebra R₀ S] [∀ i, Algebra R₀ (B i)]
    (a : ∀ i j, i ≤ j → A i →+* A j)
    (bAlg : ∀ i j (_h : i ≤ j), B i →ₐ[R₀] B j)
    [∀ i, Algebra (A i) (B i)]
    [DirectedSystem A (fun i j h => a i j h)]
    [DirectedSystem B (fun i j h => (bAlg i j h).toRingHom)]
    (hab : ∀ i j (h : i ≤ j),
      (bAlg i j h).toRingHom.comp (algebraMap (A i) (B i)) =
        (algebraMap (A j) (B j)).comp (a i j h))
    (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S)
    (hρ : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x)
    (hσ : ∀ i j (h : i ≤ j) x,
      σ j ((bAlg i j h).toRingHom x) = σ i x)
    (hρσ : ∀ i, (σ i).comp (algebraMap (A i) (B i)) =
      (algebraMap R S).comp (ρ i))
    (hρs : ∀ r, ∃ i x, ρ i x = r)
    (hρz : ∀ i x, ρ i x = 0 → ∃ j, ∃ h : i ≤ j, a i j h x = 0)
    (hσs : ∀ s, ∃ i x, σ i x = s)
    (hσz : ∀ i x, σ i x = 0 →
      ∃ j, ∃ h : i ≤ j, (bAlg i j h).toRingHom x = 0)
    (hpush : ∀ i j (h : i ≤ j),
      IsPushout (CommRingCat.ofHom (a i j h))
        (CommRingCat.ofHom (algebraMap (A i) (B i)))
        (CommRingCat.ofHom (algebraMap (A j) (B j)))
        (CommRingCat.ofHom (bAlg i j h).toRingHom))
    (g : ∀ i, B i →ₐ[R₀] S)
    (hc : IsDirectedColimit B bAlg S g)
    (hσg : ∀ i, σ i = (g i).toRingHom)
    (hflat : letI : Module R (S ⊗[R₀] M₀) :=
      Module.compHom _ (algebraMap R S); Module.Flat R (S ⊗[R₀] M₀))
    (hfp : ∀ i, Algebra.FinitePresentation (A i) (B i)) :
    ∃ i, ∀ j, i ≤ j →
      letI := Module.compHom (B j ⊗[R₀] M₀) (algebraMap (A j) (B j))
      Module.Flat (A j) (B j ⊗[R₀] M₀) := by
  classical
  let N : α → Type u := fun i => B i ⊗[R₀] M₀
  let b : ∀ i j (h : i ≤ j), B i →+* B j := fun i j h => (bAlg i j h).toRingHom
  let n : ∀ i j (h : i ≤ j), N i →ₛₗ[b i j h] N j := fun i j h =>
    (bAlg i j h).rTensorSemilinear M₀
  let ν : ∀ i, N i →ₛₗ[σ i] (S ⊗[R₀] M₀) := fun i =>
    { toFun := LinearMap.rTensor M₀ (g i).toLinearMap
      map_add' := (LinearMap.rTensor M₀ (g i).toLinearMap).map_add
      map_smul' := fun r x => by
        rw [hσg i]; exact (g i).rTensorSemilinear M₀ |>.map_smul' r x }
  have hn_eq : ∀ i j (h : i ≤ j) x,
      n i j h x = LinearMap.rTensor M₀ (bAlg i j h).toLinearMap x := by
    intro i j h x
    induction x using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simp [n, hx, hy]
  have hν_eq : ∀ i x,
      ν i x = LinearMap.rTensor M₀ (g i).toLinearMap x := by
    intro i x
    induction x using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y => simp [ν]
  have hdata := tensor_module_colimit_data R₀ B bAlg S g hc M₀
  have hcompat : ∀ i j (h : i ≤ j) x, ν j (n i j h x) = ν i x := fun i j h x => by
    rw [hn_eq i j h x, hν_eq j, hν_eq i]; exact hdata.1 i j h x
  have hsurj : ∀ y : S ⊗[R₀] M₀, ∃ i x, ν i x = y := fun y => by
    obtain ⟨i, x, hx⟩ := hdata.2.1 y
    exact ⟨i, x, (hν_eq i x).trans hx⟩
  have hzero : ∀ i x, ν i x = 0 → ∃ j, ∃ h : i ≤ j, n i j h x = 0 := fun i x hx => by
    obtain ⟨j, h, hj⟩ := hdata.2.2 i x ((hν_eq i x).symm.trans hx)
    exact ⟨j, h, (hn_eq i j h x).trans hj⟩
  have hn : DirectedSystem N (fun i j h => n i j h) :=
    directedSystem_rTensor bAlg M₀ (fun _ x => DirectedSystem.map_self' _ x)
      (fun _ _ _ hij hjk x => DirectedSystem.map_map' (fun i j h => (bAlg i j h).toRingHom)
        hij hjk x) _ hn_eq
  let : Module R (S ⊗[R₀] M₀) := Module.compHom _ (algebraMap R S)
  let : SMul R (S ⊗[R₀] M₀) :=
    (Module.compHom (S ⊗[R₀] M₀) (algebraMap R S)).toSMul
  let : Module S (S ⊗[R₀] M₀) := inferInstance
  have : IsScalarTower R S (S ⊗[R₀] M₀) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R (S ⊗[R₀] M₀) := hflat
  exact Module.Flat.eventually_flat_of_directed
    (R := R) (S := S) (S ⊗[R₀] M₀) a b n hab ρ σ ν
    hρ hσ hcompat hρσ hρs hρz hσs hσz hsurj hzero hpush
    (fun i j h => AlgHom.isBaseChange_rTensorSemilinear (bAlg i j h) M₀) hfp
    (fun _ => inferInstance)

private theorem eventually_flat_tensor_of_cocones
    {α : Type v} [PartialOrder α] [Nonempty α] [IsDirected α (· ≤ ·)]
    (A B : α ⥤ CommRingCat.{u}) (cA : Cocone A) (cB : Cocone B)
    (hcA : IsColimit ((forget CommRingCat).mapCocone cA))
    (hcB : IsColimit ((forget CommRingCat).mapCocone cB))
    (p : A ⟶ B) (pLimit : cA.pt ⟶ cB.pt)
    (hp : ∀ i, p.app i ≫ cB.ι.app i = cA.ι.app i ≫ pLimit)
    (R₀ : CommRingCat.{u}) (q : (Functor.const α).obj R₀ ⟶ B)
    (qLimit : R₀ ⟶ cB.pt) (hq : ∀ i, q.app i ≫ cB.ι.app i = qLimit)
    (M : ModuleCat.{u} R₀) [Module.FinitePresentation R₀ M]
    (hfp : ∀ i, (p.app i).hom.FinitePresentation)
    (hfpLimit : pLimit.hom.FinitePresentation)
    (hpush : ∀ i j (h : i ≤ j),
      IsPushout (A.map (homOfLE h)) (p.app i) (p.app j) (B.map (homOfLE h)))
    (hflat : letI : Algebra R₀ cB.pt := qLimit.hom.toAlgebra
      letI := Module.compHom (cB.pt ⊗[R₀] M) pLimit.hom
      Module.Flat cA.pt (cB.pt ⊗[R₀] M)) :
    ∃ i : α, letI : Algebra R₀ (B.obj i) := (q.app i).hom.toAlgebra
      letI := Module.compHom (B.obj i ⊗[R₀] M) (p.app i).hom
      Module.Flat (A.obj i) (B.obj i ⊗[R₀] M) := by
  let : Algebra R₀ cB.pt := qLimit.hom.toAlgebra
  let (i : α) : Algebra R₀ (B.obj i) := (q.app i).hom.toAlgebra
  let : Algebra cA.pt cB.pt := pLimit.hom.toAlgebra
  let (i : α) : Algebra (A.obj i) (B.obj i) := (p.app i).hom.toAlgebra
  let a (i j : α) (h : i ≤ j) := (A.map (homOfLE h)).hom
  let b (i j : α) (h : i ≤ j) : B.obj i →ₐ[R₀] B.obj j :=
    { __ := (B.map (homOfLE h)).hom
      commutes' := fun r =>
        (ConcreteCategory.congr_hom (q.naturality (homOfLE h)) r).symm }
  let g (i : α) : B.obj i →ₐ[R₀] cB.pt :=
    { __ := (cB.ι.app i).hom
      commutes' := fun r => ConcreteCategory.congr_hom (hq i) r }
  have hcol : IsDirectedColimit (fun i => B.obj i) b cB.pt g :=
    isDirectedColimit_of_ringCocone B cB b g (fun _ _ _ => rfl) (fun _ => rfl) hcB
  have : DirectedSystem (fun i => A.obj i) (fun i j h => a i j h) :=
    ⟨fun i x => ConcreteCategory.congr_hom (A.map_id i) x, fun i j k hjk hij x =>
      (ConcreteCategory.congr_hom (A.map_comp (homOfLE hjk) (homOfLE hij)) x).symm⟩
  have : DirectedSystem (fun i => B.obj i) (fun i j h => (b i j h).toRingHom) :=
    ⟨fun i x => hcol.map_id i x, fun i j k hjk hij x => hcol.map_comp hjk hij x⟩
  have hAz : ∀ i (x : A.obj i), (cA.ι.app i).hom x = 0 →
      ∃ j, ∃ h : i ≤ j, a i j h x = 0 := by
    intro i x hx
    obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcA x 0).mp
      (by simpa using hx)
    refine ⟨j, leOfHom f, ?_⟩
    have he : homOfLE (leOfHom f) = f := Subsingleton.elim _ _
    simpa [a, he] using hf
  have : Algebra.FinitePresentation cA.pt cB.pt := hfpLimit
  obtain ⟨i, hi⟩ := tensor_module_eventually_flat (fun i => A.obj i) (fun i => B.obj i)
    M a b
    (fun i j h => CommRingCat.hom_ext_iff.mp (p.naturality (homOfLE h)).symm)
    (fun i => (cA.ι.app i).hom) (fun i => (cB.ι.app i).hom)
    (fun i j h x => ConcreteCategory.congr_hom (cA.w (homOfLE h)) x)
    (fun i j h x => hcol.comp h x)
    (fun i => CommRingCat.hom_ext_iff.mp (hp i))
    (Types.jointly_surjective_of_isColimit hcA) hAz hcol.jointly_surjective
    (fun i x hx => hcol.exists_eq_zero x hx)
    hpush g hcol (fun _ => rfl) hflat hfp
  exact ⟨i, hi i le_rfl⟩

/-- On affine schemes, relative flatness of a quasi-coherent module is equivalent
to flatness of its module of global sections over the target ring. -/
private theorem flatOver_iff_flat_sections
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] :
    IsFlatOver f.toLRSHom.toShHom F ↔
      (letI : Module Γ(S, ⊤) Γ(F, ⊤) :=
        Module.compHom _ (f.appLE ⊤ ⊤ (by simp)).hom
       Module.Flat Γ(S, ⊤) Γ(F, ⊤)) := by
  let : Module Γ(S, ⊤) Γ(F, ⊤) :=
    Module.compHom _ (f.appLE ⊤ ⊤ (by simp)).hom
  refine ⟨fun hF => ?_, fun hM => ?_⟩
  · have hcrit : ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens)
        (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V),
        let : Module Γ(S, V) Γ(F, U) :=
          Module.compHom _ (f.appLE V U hUV).hom
        Module.Flat Γ(S, V) Γ(F, U) :=
      ((isFlatOver_tfae f F).out 1 2).mp hF
    exact hcrit ⊤ (isAffineOpen_top X) ⊤ (isAffineOpen_top S) (by simp)
  · have hiff :
        (∃ (J : Type u) (V : J → S.Opens), TopologicalSpace.IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens) (hU : (⨆ i, U i) = f ⁻¹ᵁ V j),
            (∀ i, IsAffineOpen (U i)) ∧
            ∀ i, let hUV : U i ≤ f ⁻¹ᵁ V j := (le_iSup U i).trans hU.le
                 let : Module Γ(S, V j) Γ(F, U i) :=
                   Module.compHom _ (f.appLE (V j) (U i) hUV).hom
                 Module.Flat Γ(S, V j) Γ(F, U i)) ↔
          IsFlatOver f.toLRSHom.toShHom F :=
      (isFlatOver_tfae f F).out 4 1 rfl rfl
    refine hiff.mp ⟨PUnit, fun _ => ⊤, TopologicalSpace.IsOpenCover.mk (by simp),
      fun _ => isAffineOpen_top S, fun _ => ⟨PUnit, fun _ => ⊤, by simp,
        fun _ => isAffineOpen_top X, fun _ => by simpa using hM⟩⟩

/-- The affine pullback formula written intrinsically for affine schemes rather
than for spectra. The two `isoSpec` identifications reduce it to the
tilde--pullback comparison `AlgebraicGeometry.specPullbackSectionsIso`. -/
private noncomputable def affinePullbackSectionsIso
    {X T : Scheme.{u}} [IsAffine X] [IsAffine T]
    (q : T ⟶ X) (F : X.Modules) [F.IsQuasicoherent] :
    (moduleSpecΓFunctor (R := CommRingCat.of Γ(T, ⊤))).obj
        ((Scheme.Modules.pullback (T.isoSpec.inv)).obj
          ((Scheme.Modules.pullback q).obj F)) ≅
    (ModuleCat.extendScalars q.appTop.hom).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of Γ(X, ⊤))).obj
          ((Scheme.Modules.pullback (X.isoSpec.inv)).obj F)) := by
  haveI : ((Scheme.Modules.pullback (X.isoSpec.inv)).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent X.isoSpec.inv F
  have eMid :
      (Scheme.Modules.pullback (T.isoSpec.inv ≫ q)).obj F ≅
        (Scheme.Modules.pullback (Spec.map q.appTop ≫ X.isoSpec.inv)).obj F := by
    rw [← Scheme.isoSpec_inv_naturality q]
  let e :
      (Scheme.Modules.pullback (T.isoSpec.inv)).obj
          ((Scheme.Modules.pullback q).obj F) ≅
        (Scheme.Modules.pullback (Spec.map q.appTop)).obj
          ((Scheme.Modules.pullback (X.isoSpec.inv)).obj F) :=
    (Scheme.Modules.pullbackComp T.isoSpec.inv q).app F ≪≫ eMid ≪≫
      ((Scheme.Modules.pullbackComp (Spec.map q.appTop) X.isoSpec.inv).app F).symm
  exact (moduleSpecΓFunctor (R := CommRingCat.of Γ(T, ⊤))).mapIso e ≪≫
    specPullbackSectionsIso (CommRingCat.of Γ(X, ⊤))
      (CommRingCat.of Γ(T, ⊤)) q.appTop
      ((Scheme.Modules.pullback (X.isoSpec.inv)).obj F)


section Stalks

open TopologicalSpace


/-- An isomorphism of schemes maps `inv j x` to `x`. -/
private theorem apply_inv_apply_of_isIso {W X : Scheme.{u}} (j : W ⟶ X) [IsIso j] (x : X) :
    j (inv j x) = x := by
  rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

private theorem isFlatOverAt_pullback_open_iff
    {W X S : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ S) (F : X.Modules) (w : W) :
    IsFlatOverAt (j ≫ f).toLRSHom.toShHom
        ((Scheme.Modules.pullback j).obj F) w ↔
      IsFlatOverAt f.toLRSHom.toShHom F (j w) :=
  (flatOverAt_iff_of_iso (j ≫ f)
    ((Scheme.Modules.restrictFunctorIsoPullback j).app F).symm w).trans
      (AlgebraicGeometry.isFlatOverAt_restrict_iff j f F w)

private theorem isFlatOver_pullback_iso_iff
    {W X S : Scheme.{u}} (j : W ⟶ X) [IsIso j]
    (f : X ⟶ S) (F : X.Modules) :
    IsFlatOver (j ≫ f).toLRSHom.toShHom
        ((Scheme.Modules.pullback j).obj F) ↔
      IsFlatOver f.toLRSHom.toShHom F := by
  refine ⟨fun h x => ?_, fun h w => (isFlatOverAt_pullback_open_iff j f F w).mpr (h _)⟩
  simpa only [apply_inv_apply_of_isIso] using
    (isFlatOverAt_pullback_open_iff j f F (inv j x)).mp (h _)

private theorem isFlatOverAt_chart_iff
    {U V X Y : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (f : X ⟶ Y) (p : U ⟶ V) (hp : p ≫ b = a ≫ f)
    (F : X.Modules) [F.IsQuasicoherent] (x : U) :
    IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pullback a).obj F) x ↔
      IsFlatOverAt f.toLRSHom.toShHom F (a x) := by
  have : ((Scheme.Modules.pullback a).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent a F
  rw [← isFlatOverAt_comp_iff_of_etale p b
    ((Scheme.Modules.pullback a).obj F) x, hp]
  exact isFlatOverAt_pullback_open_iff a f F x

end Stalks


/-- The base-change comparison morphisms `Z ×_S X ⟶ Z ×_S Y` of `f : X ⟶ Y`, assembled into a
natural transformation over the whole category of schemes over `S`. Naturality over all of
`Over S`, rather than over a diagram of stages, is what makes the comparison available at the
legs of a limit cone. -/
private noncomputable def baseChangeNatTrans
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Over.pullback X.hom ⋙ Over.forget X.left ⟶
      Over.pullback Y.hom ⋙ Over.forget Y.left where
  app Z := baseChangeMap Z.hom X Y f
  naturality A B g :=
    (baseChangeTransition_isPullback B.hom A.hom g.left g.w X Y f).w.symm

@[simp]
private theorem baseChangeNatTrans_app
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) (Z : Over S) :
    (baseChangeNatTrans f).app Z = baseChangeMap Z.hom X Y f :=
  rfl

private theorem baseChangeNatTrans_equifibered
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    NatTrans.Equifibered (baseChangeNatTrans f) := by
  intro A B g
  apply IsPullback.of_bot (v₂₁ := pullback.fst A.hom Y.hom)
    (v₂₂ := pullback.fst B.hom Y.hom)
  · simp only [baseChangeNatTrans_app, baseChangeMap_fst]
    exact (overPullback_isPullback X.hom A B g).flip
  · exact (baseChangeNatTrans f).naturality g
  · exact (overPullback_isPullback Y.hom A B g).flip

private theorem isFlatOver_baseChangeNatTrans_iff
    {S T : Scheme.{u}} (g : T ⟶ S) (X Y : Over S) (f : X ⟶ Y)
    (F : X.left.Modules) [F.IsQuasicoherent] :
    IsFlatOver ((baseChangeNatTrans f).app (Over.mk g)).toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.snd g X.hom)).obj F) ↔
      IsFlatOver ((Over.pullback g).map f).left.toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst X.hom g)).obj F) := by
  let a := (pullbackSymmetry X.hom g).hom
  let b := (pullbackSymmetry Y.hom g).hom
  let f' := (baseChangeNatTrans f).app (Over.mk g)
  let F' := (Scheme.Modules.pullback (pullback.snd g X.hom)).obj F
  have : IsIso a := inferInstance
  have : IsIso b := inferInstance
  have : F'.IsQuasicoherent :=
    pullback_isQuasicoherent (pullback.snd g X.hom) F
  have hp : ((Over.pullback g).map f).left ≫ b = a ≫ f' := by
    apply pullback.hom_ext <;>
      simp [a, b, f', baseChangeNatTrans_app, baseChangeMap, Over.pullback_map_left]
  have eq : a ≫ pullback.snd g X.hom = pullback.fst X.hom g := by
    simp [a]
  let ei : (Scheme.Modules.pullback a).obj F' ≅
      (Scheme.Modules.pullback (pullback.fst X.hom g)).obj F :=
    (Scheme.Modules.pullbackComp a (pullback.snd g X.hom)).app F ≪≫
      (by rw [eq])
  rw [← isFlatOver_iff_of_iso ((Over.pullback g).map f).left ei]
  refine ⟨fun h x =>
    (isFlatOverAt_chart_iff a b f' ((Over.pullback g).map f).left hp F' x).mpr (h (a x)),
    fun h y => ?_⟩
  have hy := apply_inv_apply_of_isIso a y
  change IsFlatOverAt f'.toLRSHom.toShHom F' y
  have ht := (isFlatOverAt_chart_iff a b f' ((Over.pullback g).map f).left hp F'
    (inv a y)).mp (h (inv a y))
  rw [hy] at ht
  exact ht


private theorem isFlatOver_baseChangeNatTrans_of_hom
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (F : X.left.Modules) [F.IsQuasicoherent]
    {A B : Over S} (g : A ⟶ B)
    (hflat : IsFlatOver ((baseChangeNatTrans f).app B).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.snd B.hom X.hom)).obj F)) :
    IsFlatOver ((baseChangeNatTrans f).app A).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.snd A.hom X.hom)).obj F) := by
  let a := ((Over.pullback X.hom).map g).left
  let G := (Scheme.Modules.pullback (pullback.snd B.hom X.hom)).obj F
  have : G.IsQuasicoherent :=
    pullback_isQuasicoherent (pullback.snd B.hom X.hom) F
  have ha : a ≫ pullback.snd B.hom X.hom = pullback.snd A.hom X.hom := by
    simp only [a, Over.pullback_map_left, Over.pullback_obj_left, pullback.lift_snd]
  let ei : (Scheme.Modules.pullback a).obj G ≅
      (Scheme.Modules.pullback (pullback.snd A.hom X.hom)).obj F :=
    (Scheme.Modules.pullbackComp a (pullback.snd B.hom X.hom)).app F ≪≫
      (by rw [ha])
  exact (isFlatOver_iff_of_iso _ ei).mp
    (pullback_isFlatOver (baseChangeNatTrans_equifibered f g) G hflat)

private theorem isFlatOverAt_baseChange_chart_iff
    {S T : Scheme.{u}} (g : T ⟶ S) {U V X Y : Over S}
    (a : U ⟶ X) (b : V ⟶ Y) (f : X ⟶ Y) (p : U ⟶ V)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left]
    (hp : p ≫ b = a ≫ f) (F : X.left.Modules) [F.IsQuasicoherent]
    (x : ((Over.pullback g).obj U).left) :
    IsFlatOverAt ((Over.pullback g).map p).left.toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst U.hom g)).obj
          ((Scheme.Modules.pullback a.left).obj F)) x ↔
      IsFlatOverAt ((Over.pullback g).map f).left.toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst X.hom g)).obj F)
        (((Over.pullback g).map a).left x) := by
  let a' := ((Over.pullback g).map a).left
  let b' := ((Over.pullback g).map b).left
  let G := (Scheme.Modules.pullback (pullback.fst X.hom g)).obj F
  have : G.IsQuasicoherent :=
    pullback_isQuasicoherent (pullback.fst X.hom g) F
  have : IsOpenImmersion a' :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) g a inferInstance
  have : IsOpenImmersion b' :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) g b inferInstance
  have ha : a' ≫ pullback.fst X.hom g = pullback.fst U.hom g ≫ a.left := by
    simp only [a', Over.pullback_map_left, Over.pullback_obj_left, pullback.lift_fst]
  let ei : (Scheme.Modules.pullback a').obj G ≅
      (Scheme.Modules.pullback (pullback.fst U.hom g)).obj
        ((Scheme.Modules.pullback a.left).obj F) :=
    (Scheme.Modules.pullbackComp a' (pullback.fst X.hom g)).app F ≪≫
      (by rw [ha]) ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst U.hom g) a.left).app F).symm
  rw [← flatOverAt_iff_of_iso ((Over.pullback g).map p).left ei x]
  apply isFlatOverAt_chart_iff a' b' ((Over.pullback g).map f).left
    ((Over.pullback g).map p).left _ G x
  have he := congrArg (fun t : U ⟶ Y => (Over.pullback g).map t) hp
  simp only [Functor.map_comp] at he
  exact congrArg Over.Hom.left he

private theorem flatOver_iff_flat_affineSections
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (F : X.Modules) [F.IsQuasicoherent] :
    IsFlatOver f.toLRSHom.toShHom F ↔
      (let M := (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
        ((Scheme.Modules.pullback X.isoSpec.inv).obj F)
       letI : Module Γ(Y, ⊤) M := Module.compHom M f.appTop.hom
       Module.Flat Γ(Y, ⊤) M) := by
  let G := (Scheme.Modules.pullback X.isoSpec.inv).obj F
  have : G.IsQuasicoherent :=
    pullback_isQuasicoherent X.isoSpec.inv F
  rw [← isFlatOver_pullback_iso_iff X.isoSpec.inv f F,
    flatOver_iff_flat_sections]
  let M := (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj G
  have hm : Module.compHom Γ(G, ⊤) ((X.isoSpec.inv ≫ f).appLE ⊤ ⊤ (by simp)).hom =
      Module.compHom M f.appTop.hom := by
    apply Module.ext'
    intro r m
    change ((X.isoSpec.inv ≫ f).appLE ⊤ ⊤ (by simp)).hom r • m = _
    have h : (X.isoSpec.inv ≫ f).appLE ⊤ ⊤ (by simp) =
        f.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).inv := by
      change (X.isoSpec.inv ≫ f).appTop = _
      rw [Scheme.Hom.comp_appTop, Stacks.RelativeSpec.isoSpec_inv_appTop]
    rw [h]
    rfl
  change @Module.Flat _ _ _ _ (Module.compHom Γ(G, ⊤)
      ((X.isoSpec.inv ≫ f).appLE ⊤ ⊤ (by simp)).hom) ↔
    @Module.Flat _ _ _ _ (Module.compHom M f.appTop.hom)
  rw [hm]
  rfl

private theorem flatOver_pullback_iff_flat_tensor
    {X T V : Scheme.{u}} [IsAffine X] [IsAffine T] [IsAffine V]
    (q : T ⟶ X) (f : T ⟶ V) (F : X.Modules) [F.IsQuasicoherent] :
    IsFlatOver f.toLRSHom.toShHom ((Scheme.Modules.pullback q).obj F) ↔
      (let M := (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
        ((Scheme.Modules.pullback X.isoSpec.inv).obj F)
       letI := q.appTop.hom.toAlgebra
       letI := Module.compHom (Γ(T, ⊤) ⊗[Γ(X, ⊤)] M) f.appTop.hom
       Module.Flat Γ(V, ⊤) (Γ(T, ⊤) ⊗[Γ(X, ⊤)] M)) := by
  have : ((Scheme.Modules.pullback q).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent q F
  rw [flatOver_iff_flat_affineSections]
  let := q.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  let M := (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
    ((Scheme.Modules.pullback X.isoSpec.inv).obj F)
  let N := (moduleSpecΓFunctor (R := Γ(T, ⊤))).obj
    ((Scheme.Modules.pullback T.isoSpec.inv).obj ((Scheme.Modules.pullback q).obj F))
  let : Module Γ(V, ⊤) N := Module.compHom N f.appTop.hom
  let : Module Γ(V, ⊤) (Γ(T, ⊤) ⊗[Γ(X, ⊤)] M) :=
    Module.compHom _ f.appTop.hom
  let : IsScalarTower Γ(V, ⊤) Γ(T, ⊤) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower Γ(V, ⊤) Γ(T, ⊤) (Γ(T, ⊤) ⊗[Γ(X, ⊤)] M) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : N ≃ₗ[Γ(T, ⊤)] (Γ(T, ⊤) ⊗[Γ(X, ⊤)] M) :=
    (affinePullbackSectionsIso q F).toLinearEquiv
  -- The comparison is `Γ(T, ⊤)`-linear, hence `Γ(V, ⊤)`-linear through the scalar tower.
  let e' : N ≃ₗ[Γ(V, ⊤)] (Γ(T, ⊤) ⊗[Γ(X, ⊤)] M) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun c x => by
        change e (f.appTop.hom c • x) = f.appTop.hom c • e x
        exact e.map_smul _ _ }
  exact Module.Flat.equiv_iff e'

private theorem eventually_isFlatOver_affine_diagram
    {J : Type v} [Category.{w} J]
    {α : Type u} [PartialOrder α] [Nonempty α] [IsDirected α (· ≤ ·)]
    (e : α ⥤ Jᵒᵖ) [e.Final]
    (X Y : J ⥤ Scheme.{u}) (cX : Cone X) (cY : Cone Y)
    [∀ j, IsAffine (X.obj j)] [∀ j, IsAffine (Y.obj j)]
    [IsAffine cX.pt] [IsAffine cY.pt]
    (hcX : IsColimit (Scheme.Γ.mapCocone cX.op))
    (hcY : IsColimit (Scheme.Γ.mapCocone cY.op))
    (f : X ⟶ Y) (fLimit : cX.pt ⟶ cY.pt)
    (hf : ∀ j, cX.π.app j ≫ f.app j = fLimit ≫ cY.π.app j)
    (X₀ : Scheme.{u}) [IsAffine X₀]
    (q : X ⟶ (Functor.const J).obj X₀) (qLimit : cX.pt ⟶ X₀)
    (hq : ∀ j, cX.π.app j ≫ q.app j = qLimit)
    (F : X₀.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    [∀ j, LocallyOfFinitePresentation (f.app j)] [LocallyOfFinitePresentation fLimit]
    (hpush : NatTrans.Equifibered f)
    (hflat : IsFlatOver fLimit.toLRSHom.toShHom ((Scheme.Modules.pullback qLimit).obj F)) :
    ∃ j, IsFlatOver (f.app j).toLRSHom.toShHom
      ((Scheme.Modules.pullback (q.app j)).obj F) := by
  let A := e ⋙ Y.op ⋙ Scheme.Γ
  let B := e ⋙ X.op ⋙ Scheme.Γ
  let cA : Cocone A := (Scheme.Γ.mapCocone cY.op).whisker e
  let cB : Cocone B := (Scheme.Γ.mapCocone cX.op).whisker e
  let p : A ⟶ B := Functor.whiskerLeft e (Functor.whiskerRight (NatTrans.op f) Scheme.Γ)
  let r : (Functor.const α).obj Γ(X₀, ⊤) ⟶ B :=
    { app := fun i => (q.app (e.obj i).unop).appTop
      naturality := by
        intro i j h
        change (q.app (e.obj j).unop).appTop =
          (q.app (e.obj i).unop).appTop ≫
            (X.map (e.map h).unop).appTop
        rw [← Scheme.Hom.comp_appTop]
        congr 1
        simp }
  let M := (moduleSpecΓFunctor (R := Γ(X₀, ⊤))).obj
    ((Scheme.Modules.pullback X₀.isoSpec.inv).obj F)
  have : ((Scheme.Modules.pullback X₀.isoSpec.inv).obj F).IsQuasicoherent :=
    pullback_isQuasicoherent X₀.isoSpec.inv F
  have : ((Scheme.Modules.pullback X₀.isoSpec.inv).obj F).IsFinitePresentation :=
    pullback_isFinitePresentation X₀.isoSpec.inv F
  have : Module.FinitePresentation Γ(X₀, ⊤) M :=
    finitePresentation_sections_of_affine _
  have hcA : IsColimit ((forget CommRingCat).mapCocone cA) :=
    isColimitOfPreserves (forget CommRingCat)
      ((Functor.Final.isColimitWhiskerEquiv e _).symm hcY)
  have hcB : IsColimit ((forget CommRingCat).mapCocone cB) :=
    isColimitOfPreserves (forget CommRingCat)
      ((Functor.Final.isColimitWhiskerEquiv e _).symm hcX)
  obtain ⟨i, hi⟩ := eventually_flat_tensor_of_cocones A B cA cB hcA hcB p fLimit.appTop
    (fun i => by
      change (f.app (e.obj i).unop).appTop ≫ (cX.π.app (e.obj i).unop).appTop =
        (cY.π.app (e.obj i).unop).appTop ≫ fLimit.appTop
      simpa only [← Scheme.Hom.comp_appTop] using
        congrArg Scheme.Hom.appTop (hf (e.obj i).unop))
    Γ(X₀, ⊤) r qLimit.appTop
    (fun i => by
      change (q.app (e.obj i).unop).appTop ≫ (cX.π.app (e.obj i).unop).appTop = _
      rw [← Scheme.Hom.comp_appTop, hq]) M
    (fun i => (f.app (e.obj i).unop).finitePresentation_appTop)
    fLimit.finitePresentation_appTop
    (fun i j h => by
      exact (isPushout_appTop_of_isPullback
        (hpush (e.map (homOfLE h)).unop)).flip)
    ((flatOver_pullback_iff_flat_tensor qLimit fLimit F).mp hflat)
  have : IsAffine (((Functor.const J).obj X₀).obj (e.obj i).unop) :=
    inferInstanceAs (IsAffine X₀)
  exact ⟨(e.obj i).unop,
    (flatOver_pullback_iff_flat_tensor (q.app (e.obj i).unop)
      (f.app (e.obj i).unop) F).mpr hi⟩

private lemma exists_small_directed_cofinal_over
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    [EssentiallySmall.{u} I] (i : I) :
    ∃ (α : Type u) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·))
      (_ : Nonempty α) (e : α ⥤ (Over i)ᵒᵖ), e.Final := by
  have : EssentiallySmall.{u} (Over i) := by
    change EssentiallySmall.{u} (CostructuredArrow (𝟭 I) i)
    infer_instance
  let E := equivSmallModel.{u} (Over i)
  have : IsCofiltered (SmallModel.{u} (Over i)) := IsCofiltered.of_equivalence E
  obtain ⟨α, _, _, _, e, he⟩ := IsFiltered.exists_directed ((SmallModel.{u} (Over i))ᵒᵖ)
  exact ⟨α, inferInstance, inferInstance, inferInstance, e ⋙ E.inverse.op, inferInstance⟩

private theorem eventually_isFlatOver_affine_baseChange
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    (i : I) (X Y : Over (D.obj i)) [IsAffine X.left] [IsAffine Y.left]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f.left]
    (F : X.left.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : IsFlatOver ((Over.pullback (c.π.app i)).map f).left.toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst X.hom (c.π.app i))).obj F)) :
    ∃ (j : I) (g : j ⟶ i), IsFlatOver
      ((Over.pullback (D.map g)).map f).left.toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.fst X.hom (D.map g))).obj F) := by
  let DX := Over.post D ⋙ Over.pullback X.hom ⋙ Over.forget _
  let DY := Over.post D ⋙ Over.pullback Y.hom ⋙ Over.forget _
  let c₀ := (Over.conePost D i).obj c
  let cX : Cone DX := (Over.pullback X.hom ⋙ Over.forget _).mapCone c₀
  let cY : Cone DY := (Over.pullback Y.hom ⋙ Over.forget _).mapCone c₀
  have (a : Over i) : IsAffine (DX.obj a) := isAffine_baseChange_stage D i X a
  have (a : Over i) : IsAffine (DY.obj a) := isAffine_baseChange_stage D i Y a
  have : IsAffine cX.pt :=
    Scheme.isAffine_of_isLimit cX (isLimit_baseChange_diagram D c hc i X)
  have : IsAffine cY.pt :=
    Scheme.isAffine_of_isLimit cY (isLimit_baseChange_diagram D c hc i Y)
  let f' : DX ⟶ DY := Functor.whiskerLeft (Over.post D) (baseChangeNatTrans f)
  let fLimit : cX.pt ⟶ cY.pt := (baseChangeNatTrans f).app c₀.pt
  let q : DX ⟶ (Functor.const (Over i)).obj X.left :=
    { app := fun a => pullback.snd (D.map a.hom) X.hom
      naturality := by
        intro a b g
        dsimp [DX, Over.pullback]
        exact pullback.lift_snd _ _ _ }
  let qLimit : cX.pt ⟶ X.left := pullback.snd (c.π.app i) X.hom
  have (a : Over i) : LocallyOfFinitePresentation (f'.app a) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (baseChangeMap_isPullback (D.map a.hom) X Y f).flip inferInstance
  have : LocallyOfFinitePresentation fLimit :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (baseChangeMap_isPullback (c.π.app i) X Y f).flip inferInstance
  have hdir : ∃ (α : Type u) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·))
      (_ : Nonempty α) (e : α ⥤ (Over i)ᵒᵖ), e.Final :=
    exists_small_directed_cofinal_over i
  obtain ⟨α, _, _, _, e, he⟩ := hdir
  obtain ⟨hcX⟩ := sections_colimit_baseChange_diagram D c hc i X
  obtain ⟨hcY⟩ := sections_colimit_baseChange_diagram D c hc i Y
  obtain ⟨a, ha⟩ := eventually_isFlatOver_affine_diagram e DX DY cX cY hcX hcY
    f' fLimit (fun a => (baseChangeNatTrans f).naturality (c₀.π.app a))
    X.left q qLimit (fun a => by
      dsimp [q, qLimit, cX, c₀, Over.pullback]
      exact pullback.lift_snd _ _ _) F
    ((baseChangeNatTrans_equifibered f).whiskerLeft (Over.post D))
    ((isFlatOver_baseChangeNatTrans_iff (c.π.app i) X Y f F).mpr hflat)
  exact ⟨a.left, a.hom,
    (isFlatOver_baseChangeNatTrans_iff (D.map a.hom) X Y f F).mp ha⟩

/-- If a finitely presented quasi-coherent module at one stage of a cofiltered
inverse system becomes flat over the base-changed target at the limit, it is
flat over that target after passing to some later stage. -/
@[stacks 05LY, ega "IV 11.2.6" "(ii)"]
theorem eventually_isFlatOver_modulePullback
    {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (X Y : Over (D.obj i))
    (hX : FinitePresentation X.hom) (hY : FinitePresentation Y.hom)
    (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace))
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : IsFlatOver
      ((Over.pullback (c.π.app i)).map f).left.toLRSHom.toShHom
      ((modulePullback
        (pullback.fst X.hom (c.π.app i)).toLRSHom.toShHom).obj F)) :
    ∃ (j : I) (e : j ⟶ i), IsFlatOver
      ((Over.pullback (D.map e)).map f).left.toLRSHom.toShHom
      ((modulePullback
        (pullback.fst X.hom (D.map e)).toLRSHom.toShHom).obj F) := by
  classical
  let : QuasiCompact X.hom := hX.2.1
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : LocallyOfFinitePresentation X.hom := hX.1
  let : LocallyOfFinitePresentation Y.hom := hY.1
  let : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by simpa only [Over.w] using hX.1
  let : LocallyOfFinitePresentation f.left := locallyOfFinitePresentation_of_comp f.left Y.hom
  obtain ⟨C, hCfinite, hCaffine, V, b, p, hVaffine, hb, hp⟩ :=
    exists_finite_affine_charts f.left
  let : Finite C.I₀ := hCfinite
  let (j : C.I₀) : IsAffine (C.X j) := hCaffine j
  let (j : C.I₀) : IsAffine (V j) := hVaffine j
  let (j : C.I₀) : IsOpenImmersion (b j) := hb j
  let U₀ (j : C.I₀) : Over (D.obj i) := Over.mk (C.f j ≫ X.hom)
  let V₀ (j : C.I₀) : Over (D.obj i) := Over.mk (b j ≫ Y.hom)
  let a₀ (j : C.I₀) : U₀ j ⟶ X := Over.homMk (C.f j)
  let b₀ (j : C.I₀) : V₀ j ⟶ Y := Over.homMk (b j)
  let p₀ (j : C.I₀) : U₀ j ⟶ V₀ j := Over.homMk (p j) (by
    change p j ≫ (b j ≫ Y.hom) = C.f j ≫ X.hom
    rw [← Category.assoc, hp, Category.assoc, Over.w])
  have (j : C.I₀) : IsAffine (U₀ j).left := hCaffine j
  have (j : C.I₀) : IsAffine (V₀ j).left := hVaffine j
  have (j : C.I₀) : IsOpenImmersion (a₀ j).left := C.map_prop j
  have (j : C.I₀) : IsOpenImmersion (b₀ j).left := hb j
  have hp₀ (j : C.I₀) : p₀ j ≫ b₀ j = a₀ j ≫ f := by ext; exact hp j
  have hFqc : SheafOfModules.IsQuasicoherent (R := X.left.ringCatSheaf) F :=
    isQuasicoherent_scheme F
  have hFfp : SheafOfModules.IsFinitePresentation.{u, u, u} (R := X.left.ringCatSheaf) F :=
    isFinitePresentation_scheme F
  let F₀ (j : C.I₀) := (Scheme.Modules.pullback (C.f j)).obj F
  have (j : C.I₀) : (F₀ j).IsQuasicoherent :=
    pullback_isQuasicoherent (C.f j) F
  have (j : C.I₀) : (F₀ j).IsFinitePresentation :=
    pullback_isFinitePresentation (C.f j) F
  have (j : C.I₀) : LocallyOfFinitePresentation (p₀ j).left :=
    have : LocallyOfFinitePresentation (p j ≫ b j) := by rw [hp j]; infer_instance
    locallyOfFinitePresentation_of_comp (p j) (b j)
  let P (A : Over i) (j : C.I₀) : Prop :=
    IsFlatOver ((baseChangeNatTrans (p₀ j)).app ((Over.post D).obj A)).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.snd (D.map A.hom) (U₀ j).hom)).obj (F₀ j))
  have hP {A B : Over i} (g : A ⟶ B) (j : C.I₀) : P B j → P A j :=
    isFlatOver_baseChangeNatTrans_of_hom (p₀ j) (F₀ j) ((Over.post D).map g)
  have hstage (j : C.I₀) : ∃ A : Over i, P A j := by
    have hflat₀ : IsFlatOver ((Over.pullback (c.π.app i)).map (p₀ j)).left.toLRSHom.toShHom
        ((Scheme.Modules.pullback (pullback.fst (U₀ j).hom (c.π.app i))).obj (F₀ j)) := by
      intro x
      exact (isFlatOverAt_baseChange_chart_iff (c.π.app i) (a₀ j) (b₀ j) f
        (p₀ j) (hp₀ j) F x).mpr (hflat _)
    obtain ⟨k, g, hg⟩ := eventually_isFlatOver_affine_baseChange D c hc i
      (U₀ j) (V₀ j) (p₀ j) (F₀ j) hflat₀
    exact ⟨Over.mk g,
      (isFlatOver_baseChangeNatTrans_iff (D.map g) (U₀ j) (V₀ j) (p₀ j) (F₀ j)).mpr hg⟩
  obtain ⟨A, hA⟩ := common_stage_of_finite i P hP hstage
  refine ⟨A.left, A.hom, fun x => ?_⟩
  obtain ⟨j, y, hy⟩ := C.exists_eq ((pullback.fst X.hom (D.map A.hom)) x)
  obtain ⟨z, hz, rfl⟩ := Scheme.exists_preimage_of_isPullback
    (overPullback_isPullback (D.map A.hom) (U₀ j) X (a₀ j)) y x hy
  exact (isFlatOverAt_baseChange_chart_iff (D.map A.hom) (a₀ j) (b₀ j) f (p₀ j) (hp₀ j) F z).mp
    ((isFlatOver_baseChangeNatTrans_iff (D.map A.hom) (U₀ j) (V₀ j) (p₀ j) (F₀ j)).mp (hA j) z)

end AlgebraicGeometry

end

end
