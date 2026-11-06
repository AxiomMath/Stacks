module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherence on a chaotic site

A site carries the chaotic (indiscrete) topology when its Grothendieck topology is the bottom
one: the only covering sieve of an object is the maximal sieve. On such a site a presheaf is
automatically a sheaf, and a sheaf of modules over the structure sheaf of a ringed site is
quasi-coherent exactly when every restriction map becomes an isomorphism after extension of
scalars.

Concretely, for a morphism `f : U ⟶ V` of the site and a sheaf of modules `F`, extension of
scalars along the ring restriction map `O(f) : O(V) ⟶ O(U)` produces a canonical comparison
map `F(V) ⊗_{O(V)} O(U) ⟶ F(U)`, the adjoint transpose of the restriction map `F(f)` under the
extension/restriction of scalars adjunction. The main result says that `F` is quasi-coherent if
and only if all of these comparison maps are isomorphisms.

## Main definitions

* `Stacks.SheafOfModules.canonicalMap`: the comparison map
  `F(V) ⊗_{O(V)} O(U) ⟶ F(U)` attached to a morphism `f : U ⟶ V` of the site.

## Main results

* `Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso`: on a ringed site whose
  topology is the bottom one, a sheaf of modules is quasi-coherent if and only if all its
  canonical comparison maps are isomorphisms.
* `Stacks.SheafOfModules.botTopologyOver`: the topology induced by the bottom topology on a
  slice is again the bottom topology.
* `Stacks.SheafOfModules.botWEqualsLocallyBijective`: the morphisms of abelian sheaves on a
  chaotic site inverted by sheafification are exactly the locally bijective ones.

## Implementation notes

The chaotic topology is expressed as `X.J = ⊥` rather than by a typeclass, so that the result
can be applied to a slice of a chaotic site, whose induced topology is again the bottom one
(`Stacks.SheafOfModules.botTopologyOver`).

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, the sheaf-theoretic predicate for an
arbitrary site, whose global presentations are expressed by universal properties and therefore
need no sheafification instance. The companion presheaf-level development
`ChaoticQCoh.QuasiCoherent` phrases the same notion for a presheaf of modules over a presheaf
of rings, with presentations written in terms of free presheaves of modules; the two are
compared in `Stacks.SheafOfModules.quasiCoherent_iff_isQuasicoherentOnSite`. They are kept
apart because Mathlib's free presheaf of modules functor forces the indexing universe of a
presentation to agree with the ring universe, which the sheaf-theoretic predicate does not.

## References

* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.SheafOfModules

universe u v w r m k t

variable (X : RingedSite.{u, v, w})
    (F : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- A covering family for the bottom topology contains a split epimorphism. -/
public theorem splitArrow_of_bot_cover {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {U : C} {I : Type*} (V : I → C)
    (f : ∀ i, V i ⟶ U) (hJ : J = ⊥)
    (hc : Sieve.ofArrows V f ∈ J U) :
    ∃ i, ∃ s : U ⟶ V i, s ≫ f i = 𝟙 U := by
  rw [hJ, GrothendieckTopology.bot_covering] at hc
  have hid : Sieve.ofArrows V f (𝟙 U) := by
    rw [hc]
    simp
  obtain ⟨i, s, hs⟩ := (Sieve.mem_ofArrows_iff V f (𝟙 U)).mp hid
  exact ⟨i, s, hs.symm⟩

/-- The topology induced on a slice by the bottom topology is again the bottom topology. -/
public theorem botTopologyOver {C : Type u} [Category.{v} C] (V : C) :
    (⊥ : GrothendieckTopology C).over V = ⊥ := by
  apply GrothendieckTopology.ext
  funext Y
  ext S
  simp [GrothendieckTopology.mem_over_iff]

/-- Quasi-coherence on the bottom topology supplies a global presentation after a
split epimorphism over each object. -/
public theorem splitPresentation_of_isQuasicoherent
    (hX : X.J = ⊥) (hF : F.IsQuasicoherentOnSite) (V : X.C) :
    ∃ (W : X.C) (f : W ⟶ V) (s : V ⟶ W),
      s ≫ f = 𝟙 V ∧ (F.over W).HasGlobalPresentation := by
  obtain ⟨I, W, f, hc, hpres⟩ := hF.locally_hasGlobalPresentation V
  obtain ⟨i, s, hs⟩ := splitArrow_of_bot_cover W f hX hc
  exact ⟨W i, f i, s, hs, hpres i⟩

/-- The maps inverted by sheafification on the bottom topology are precisely the
locally bijective maps, at every additive-group universe. -/
public theorem botWEqualsLocallyBijective
    {C : Type u} [Category.{v} C] :
    (⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m} := by
  let J : GrothendieckTopology C := ⊥
  let : HasWeakSheafify J AddCommGrpCat.{m} := inferInstance
  let : J.HasSheafCompose (forget AddCommGrpCat.{m}) := by
    apply hasSheafCompose_of_preservesLimitsOfSize
  have hiso (P : Cᵒᵖ ⥤ AddCommGrpCat.{m}) : IsIso (toSheafify J P) :=
    let S : Sheaf J AddCommGrpCat.{m} := ⟨P, Presheaf.isSheaf_bot P⟩
    have e : P ≅ (sheafToPresheaf J AddCommGrpCat.{m}).obj S := Iso.refl P
    Adjunction.isIso_unit_app_of_iso (sheafificationAdjunction J AddCommGrpCat) e
  let : ∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{m}, Presheaf.IsLocallyInjective J (toSheafify J P) :=
    fun P => have := hiso P; inferInstance
  let : ∀ P : Cᵒᵖ ⥤ AddCommGrpCat.{m}, Presheaf.IsLocallySurjective J (toSheafify J P) :=
    fun P => have := hiso P; inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.mk'
    (C := C) (J := J) (A := AddCommGrpCat.{m})

/-- On the bottom topology, evaluation of a sheaf of modules at any object preserves
colimits. This follows from exactness of the forgetful functor and pointwise colimits
of presheaves. -/
private theorem moduleEvaluationPreservesColimitBot
    {C : Type u} [Category.{v} C]
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r}) (U : Cᵒᵖ)
    (K : Type m) [Category.{m} K] :
    PreservesColimitsOfShape K (_root_.SheafOfModules.evaluation.{m} R U) := by
  let : HasWeakSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{m} := inferInstance
  let : (⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{m} :=
    botWEqualsLocallyBijective (C := C)
  let G := forget₂ (ModuleCat.{m} (R.obj.obj U)) AddCommGrpCat.{m}
  have hToSheaf : PreservesColimitsOfShape K (_root_.SheafOfModules.toSheaf R) := by
    let : PreservesColimitsOfSize.{max u m, m} (_root_.SheafOfModules.toSheaf R) :=
      AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits (R := R)
    have hsmall : PreservesColimitsOfSize.{m, m} (_root_.SheafOfModules.toSheaf R) :=
      preservesColimitsOfSize_of_univLE.{max u m, m, m, m}
        (_root_.SheafOfModules.toSheaf R)
    exact hsmall.preservesColimitsOfShape
  have hEquiv : PreservesColimitsOfShape K
      (sheafBotEquivalence (C := C) AddCommGrpCat.{m}).functor := by
    infer_instance
  have hEval : PreservesColimitsOfShape K
      ((CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{m}).obj U) := by
    infer_instance
  have hcomp : PreservesColimitsOfShape K
      (_root_.SheafOfModules.evaluation.{m} R U ⋙ G) := by
    show PreservesColimitsOfShape K
      (_root_.SheafOfModules.toSheaf R ⋙
        (sheafBotEquivalence (C := C) AddCommGrpCat.{m}).functor ⋙
        (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{m}).obj U)
    let := hToSheaf
    let := hEquiv
    let := hEval
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (_root_.SheafOfModules.evaluation.{m} R U) G

/-- Evaluation sends a cokernel presentation on a bottom site to the
corresponding cokernel presentation of modules. -/
private noncomputable def moduleEvaluationPreservesCokernelBot
    {C : Type u} [Category.{v} C]
    (R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{r}) (U : Cᵒᵖ)
    {Q P M : _root_.SheafOfModules.{m} R} (a : Q ⟶ P) (b : P ⟶ M) (hab : a ≫ b = 0)
    (hc : IsColimit (CokernelCofork.ofπ b hab)) :
    IsColimit (CokernelCofork.ofπ
      ((_root_.SheafOfModules.evaluation.{m} R U).map b)
      (by rw [← Functor.map_comp, hab, Functor.map_zero])) := by
  let E := _root_.SheafOfModules.evaluation.{m} R U
  let e := ULiftHomULiftCategory.equiv.{m, m, 0, 0} WalkingParallelPair
  have he : PreservesColimitsOfShape (ULiftHom.{m} (ULift.{m} WalkingParallelPair)) E :=
    moduleEvaluationPreservesColimitBot R U (ULiftHom.{m} (ULift.{m} WalkingParallelPair))
  letI : PreservesColimitsOfShape WalkingParallelPair E :=
    preservesColimitsOfShape_of_equiv e.symm E
  have hp : PreservesColimit (parallelPair a 0) E := by infer_instance
  letI : PreservesColimit (parallelPair a 0) E := hp
  letI : E.Additive := by infer_instance
  exact CokernelCofork.mapIsColimit (CokernelCofork.ofπ b hab) hc E

/-- The corresponding pointwise evaluation result for cokernels. -/
private noncomputable def moduleEvaluationPreservesCokernelOfBot
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (hJ : J = ⊥) (R : Sheaf J RingCat.{r}) (U : Cᵒᵖ)
    {Q P M : _root_.SheafOfModules.{m} R} (a : Q ⟶ P) (b : P ⟶ M) (hab : a ≫ b = 0)
    (hc : IsColimit (CokernelCofork.ofπ b hab)) :
    IsColimit (CokernelCofork.ofπ ((_root_.SheafOfModules.evaluation.{m} R U).map b)
      (by rw [← Functor.map_comp, hab, Functor.map_zero])) := by
  cases hJ
  exact moduleEvaluationPreservesCokernelBot R U a b hab hc

/-- The canonical extension-of-scalars map on sections along `f`. -/
public noncomputable def canonicalMap {U V : X.C} (f : U ⟶ V) :
    (ModuleCat.extendScalars (X.O.obj.map f.op).hom).obj
      (F.val.obj (Opposite.op V)) ⟶ F.val.obj (Opposite.op U) :=
  ((ModuleCat.extendRestrictScalarsAdj (X.O.obj.map f.op).hom).homEquiv _ _).symm
    (F.val.map f.op)

private noncomputable def siteEvaluation (U : X.Cᵒᵖ) :
    _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      ModuleCat.{max w m} (X.O.obj.obj U) where
  obj M := M.val.obj U
  map f := f.val.app U

private instance siteEvaluationAdditive (U : X.Cᵒᵖ) :
    (siteEvaluation.{u,v,w,m} X U).Additive where
  map_add := by intros; ext x; rfl

private noncomputable def baseChangeNat {U V : X.C} (f : U ⟶ V) :
    siteEvaluation.{u,v,w,m} X (Opposite.op V) ⋙
      ModuleCat.extendScalars (X.O.obj.map f.op).hom ⟶
    siteEvaluation.{u,v,w,m} X (Opposite.op U) where
  app M := ((ModuleCat.extendRestrictScalarsAdj (X.O.obj.map f.op).hom).homEquiv _ _).symm
    (M.val.map f.op)
  naturality {M N} g :=
    (ModuleCat.extendRestrictScalarsAdj (X.O.obj.map f.op).hom).homEquiv_naturality_right_square
      (g.val.app (Opposite.op V)) (N.val.map f.op) (M.val.map f.op)
      (g.val.app (Opposite.op U)) (g.val.naturality f.op).symm

/-- The sections of `X.ringSheaf` at an object are by construction those of the structure
sheaf `X.O`, so the sections of a sheaf of modules are a module over the latter. -/
private noncomputable instance moduleSectionsStructureSheaf
    (M : _root_.SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.Cᵒᵖ) :
    Module (X.O.obj.obj U) (M.val.obj U) :=
  inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (M.val.obj U))

/-- The same identification for the scalar action on a restriction of scalars along a
restriction map of `X.ringSheaf`. -/
private noncomputable instance smulRestrictScalarsStructureSheaf {U V : X.C} (f : U ⟶ V)
    (M : _root_.SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SMul (X.O.obj.obj (Opposite.op U))
      ((ModuleCat.restrictScalars
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom).obj
        (M.val.obj (Opposite.op U))) :=
  inferInstanceAs (SMul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (Opposite.op U))
    (M.val.obj (Opposite.op U)))

/-- The sections of the unit sheaf of modules at `Y` are the sections of the ring sheaf, and
therefore act on a restriction of scalars along a restriction map into `Y`. -/
private noncomputable instance smulUnitRestrictScalars {Y Z : X.Cᵒᵖ} (g : Z ⟶ Y)
    (M : _root_.SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    SMul ((_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.obj Y)
      ((ModuleCat.restrictScalars
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (SMul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Y)
    ((ModuleCat.restrictScalars
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map g).hom).obj (M.val.obj Y)))

/-- The adjoint transpose of an `R`-linear map `g : A ⟶ B` along a ring homomorphism
`φ : R →+* S` sends a pure tensor `a ⊗ₜ s` to `a • g s`. -/
private theorem extendRestrictScalarsAdj_homEquiv_symm_tmul {R S : Type k} [CommRing R]
    [CommRing S] (φ : R →+* S) (A : ModuleCat.{max t k} R) (B : ModuleCat.{max t k} S)
    (g : A ⟶ (ModuleCat.restrictScalars φ).obj B) (a : S) (s : A) :
    (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv A B).symm g).hom (a ⊗ₜ s)
      = a • g.hom s := rfl

private theorem baseChangeNat_tmul {U V : X.C} (f : U ⟶ V)
    (M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : M.val.obj (Opposite.op V)) (a : X.O.obj.obj (Opposite.op U)) :
    ((baseChangeNat X f).app M).hom (a ⊗ₜ s) = a • M.val.map f.op s :=
  extendRestrictScalarsAdj_homEquiv_symm_tmul (X.O.obj.map f.op).hom _ _
    (M.val.map f.op) a s

/-- `baseChangeNat_tmul` with the morphism applied through the concrete-category
coercion. -/
private theorem baseChangeNat_apply_tmul {U V : X.C} (f : U ⟶ V)
    (M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (s : M.val.obj (Opposite.op V)) (a : X.O.obj.obj (Opposite.op U)) :
    (baseChangeNat X f).app M (a ⊗ₜ s) = a • M.val.map f.op s :=
  baseChangeNat_tmul X f M s a

/-- Base change of the free module of rank one. The adjoint transpose along `φ : R →+* S` of a
map `ULift R ⟶ ULift S` given by `φ` on underlying elements is an isomorphism, with inverse
`s ↦ s ⊗ₜ 1`. -/
private theorem isIso_homEquiv_symm_of_ulift {R S : Type k} [CommRing R] [CommRing S]
    (φ : R →+* S)
    (g : ModuleCat.of R (ULift.{t} R) ⟶
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of S (ULift.{t} S)))
    (hg : ∀ r : ULift.{t} R, (g.hom r).down = φ r.down) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv
      (ModuleCat.of R (ULift.{t} R)) (ModuleCat.of S (ULift.{t} S))).symm g) := by
  let := φ.toAlgebra
  let d' : ULift.{t} S →ₗ[S]
      (ModuleCat.extendScalars φ).obj (ModuleCat.of R (ULift.{t} R)) := {
    toFun := fun s => s.down ⊗ₜ (ULift.up (1 : R))
    map_add' := fun s t => TensorProduct.add_tmul _ _ _
    map_smul' := fun a s => rfl }
  have hR : ∀ s : ULift.{t} S,
      (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv
        (ModuleCat.of R (ULift.{t} R)) (ModuleCat.of S (ULift.{t} S))).symm g)
          (s.down ⊗ₜ (ULift.up (1 : R))) = s := by
    intro s
    refine (extendRestrictScalarsAdj_homEquiv_symm_tmul φ _ _ g s.down
      (ULift.up (1 : R))).trans ?_
    apply ULift.down_injective
    exact (congrArg (s.down * ·)
      ((hg (ULift.up (1 : R))).trans (map_one φ))).trans (mul_one s.down)
  have hL : ∀ z, d' ((((ModuleCat.extendRestrictScalarsAdj φ).homEquiv
      (ModuleCat.of R (ULift.{t} R)) (ModuleCat.of S (ULift.{t} S))).symm g) z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact (congrArg (d' ·) (map_zero _)).trans (map_zero d')
    | add x y hx hy =>
      exact (congrArg (d' ·) (map_add _ x y)).trans
        ((map_add d' _ _).trans (congrArg₂ _ hx hy))
    | tmul a x =>
      have key : ∀ b : S, ((b • g.hom x).down : S) = x.down • b := fun b =>
        (congrArg (b * ·) (hg x)).trans (mul_comm b (φ x.down))
      have hx1 : x.down • (ULift.up (1 : R) : ULift.{t} R) = x :=
        ULift.down_injective (mul_one x.down)
      exact (congrArg (d' ·)
          (extendRestrictScalarsAdj_homEquiv_symm_tmul φ _ _ g a x)).trans
        ((congrArg (fun y => d' (ULift.up y)) (key a)).trans
          ((TensorProduct.smul_tmul x.down a (ULift.up (1 : R))).trans
            (congrArg (a ⊗ₜ ·) hx1)))
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (Function.bijective_iff_has_inverse.mpr ⟨fun y => d' y, hL, hR⟩)

private theorem baseChangeNat_isIso_unit {U V : X.C} (f : U ⟶ V) :
    IsIso ((baseChangeNat.{u,v,w,m} X f).app
      (_root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :=
  isIso_homEquiv_symm_of_ulift.{w,m} (X.O.obj.map f.op).hom
    ((_root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.map f.op)
    fun _ => rfl

private theorem siteEvaluation_preservesColimits_of_bot (hX : X.J = ⊥) (U : X.Cᵒᵖ) :
    PreservesColimitsOfSize.{max w m, max w m}
      (siteEvaluation.{u,v,w,m} X U) := by
  constructor
  intro K _
  have aux {J : GrothendieckTopology X.C} (hJ : J = ⊥)
      (R : Sheaf J RingCat.{w}) :
      PreservesColimitsOfShape K (_root_.SheafOfModules.evaluation.{max w m} R U) := by
    subst J
    exact moduleEvaluationPreservesColimitBot R U K
  exact aux hX (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

private theorem baseChangeNat_isIso_coproduct (hX : X.J = ⊥)
    {U V : X.C} (f : U ⟶ V) (I : Type (max w m))
    (P : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ι : ∀ _ : I, _root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) :
    IsIso ((baseChangeNat X f).app P) := by
  let := siteEvaluation_preservesColimits_of_bot.{u,v,w,m} X hX (Opposite.op V)
  let := siteEvaluation_preservesColimits_of_bot.{u,v,w,m} X hX (Opposite.op U)
  let : IsIso (Functor.whiskerLeft
      (Discrete.functor (fun _ : I => _root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
      (baseChangeNat X f)) := by
    let : ∀ i : Discrete I, IsIso ((Functor.whiskerLeft
        (Discrete.functor (fun _ : I => _root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
        (baseChangeNat X f)).app i) :=
      fun _ => baseChangeNat_isIso_unit X f
    exact NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit
    (L := siteEvaluation X (Opposite.op V) ⋙ ModuleCat.extendScalars (X.O.obj.map f.op).hom)
    (L' := siteEvaluation X (Opposite.op U))
    (Discrete.functor (fun _ : I => _root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (baseChangeNat X f) (Cofan.mk P ι) hP

private theorem baseChangeNat_isIso_cokernel (hX : X.J = ⊥)
    {U V : X.C} (f : U ⟶ V)
    {Q P M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (a : Q ⟶ P) (b : P ⟶ M) (hab : a ≫ b = 0)
    (hc : IsColimit (CokernelCofork.ofπ b hab))
    [IsIso ((baseChangeNat X f).app Q)] [IsIso ((baseChangeNat X f).app P)] :
    IsIso ((baseChangeNat X f).app M) := by
  let := siteEvaluation_preservesColimits_of_bot.{u,v,w,m} X hX (Opposite.op V)
  let := siteEvaluation_preservesColimits_of_bot.{u,v,w,m} X hX (Opposite.op U)
  let : PreservesColimitsOfSize.{0,0}
      (siteEvaluation.{u,v,w,m} X (Opposite.op V)) :=
    preservesColimitsOfSize_shrink _
  let : PreservesColimitsOfSize.{0,0}
      (siteEvaluation.{u,v,w,m} X (Opposite.op U)) :=
    preservesColimitsOfSize_shrink _
  let : IsIso (Functor.whiskerLeft (parallelPair a 0) (baseChangeNat X f)) := by
    let (i : WalkingParallelPair) :
        IsIso ((Functor.whiskerLeft (parallelPair a 0) (baseChangeNat X f)).app i) := by
      cases i <;> dsimp <;> infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit
    (L := siteEvaluation X (Opposite.op V) ⋙ ModuleCat.extendScalars (X.O.obj.map f.op).hom)
    (L' := siteEvaluation X (Opposite.op U))
    (parallelPair a 0) (baseChangeNat X f) (CokernelCofork.ofπ b hab) hc


private theorem baseChangeNat_isIso_ulift_iff
    (M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : U ⟶ V) :
    IsIso ((baseChangeNat X f).app
      (_root_.SheafOfModules.uliftForPresentation.{u,v,w,max w m,k} M)) ↔
    IsIso ((baseChangeNat X f).app M) := by
  let := (X.O.obj.map f.op).hom.toAlgebra
  let e := TensorProduct.congr
    (LinearEquiv.refl (X.O.obj.obj (Opposite.op V)) (X.O.obj.obj (Opposite.op U)))
    (ULift.moduleEquiv (R := X.O.obj.obj (Opposite.op V))
      (M := M.val.obj (Opposite.op V)))
  let c := (baseChangeNat X f).app M
  let c' := (baseChangeNat X f).app
    (_root_.SheafOfModules.uliftForPresentation.{u,v,w,max w m,k} M)
  have he (z : (ModuleCat.extendScalars (X.O.obj.map f.op).hom).obj
      ((_root_.SheafOfModules.uliftForPresentation.{u,v,w,max w m,k} M).val.obj (Opposite.op V))) :
      c (e z) = (c' z).down := by
    induction z using TensorProduct.induction_on with
    | zero =>
      exact (congrArg (c ·) (map_zero e)).trans
        ((map_zero _).trans (congrArg ULift.down (map_zero _)).symm)
    | add x y hx hy =>
      refine ((congrArg (c ·) (map_add e x y)).trans
        ((map_add _ _ _).trans (congrArg₂ _ hx hy))).trans ?_
      exact congrArg ULift.down (map_add _ x y).symm
    | tmul a s =>
      show c (a ⊗ₜ s.down) = (c' (a ⊗ₜ s)).down
      exact (baseChangeNat_apply_tmul X f M s.down a).trans
        (congrArg ULift.down (baseChangeNat_apply_tmul X f
          (_root_.SheafOfModules.uliftForPresentation.{u,v,w,max w m,k} M) s a)).symm
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  constructor
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y h
      apply e.symm.injective
      apply hi
      apply ULift.down_injective
      exact (he (e.symm x)).symm.trans
        ((congrArg (c ·) (e.apply_symm_apply x)).trans
          (h.trans ((congrArg (c ·) (e.apply_symm_apply y)).symm.trans (he (e.symm y)))))
    · intro y
      obtain ⟨z, hz⟩ := hs (ULift.up y)
      exact ⟨e z, (he z).trans (congrArg ULift.down hz)⟩
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y h
      apply e.injective
      apply hi
      exact (he x).trans ((congrArg ULift.down h).trans (he y).symm)
    · intro y
      obtain ⟨z, hz⟩ := hs y.down
      refine ⟨e.symm z, ULift.down_injective ?_⟩
      exact (he (e.symm z)).symm.trans
        ((congrArg (c ·) (e.apply_symm_apply z)).trans hz)

private theorem baseChangeNat_isIso_of_globalPresentation
    (hX : X.J = ⊥) (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : M.HasGlobalPresentation) {U V : X.C} (f : U ⟶ V) :
    IsIso ((baseChangeNat.{u,v,w,0} X f).app M) := by
  obtain ⟨I, K, P, Q, ι, κ, hP, hQ, a, b, hab, hc⟩ := hM
  have := baseChangeNat_isIso_coproduct.{u,v,w,max u v w} X hX f I P ι hP.some
  have := baseChangeNat_isIso_coproduct.{u,v,w,max u v w} X hX f K Q κ hQ.some
  have h := baseChangeNat_isIso_cokernel X hX f a b hab hc.some
  exact (baseChangeNat_isIso_ulift_iff.{u,v,w,0,max u v w} X M f).mp h

private noncomputable def sliceRingedSite (V : X.C) : RingedSite.{max u v,v,w} where
  C := Over V
  J := X.J.over V
  O := X.O.over V

/-- The slice of a chaotic ringed site is again chaotic. -/
private theorem sliceRingedSite_J_eq_bot (hX : X.J = ⊥) (V : X.C) :
    (sliceRingedSite X V).J = ⊥ := by
  dsimp [sliceRingedSite]
  rw [hX, botTopologyOver]
  rfl

private theorem canonicalMap_isIso_of_isQuasicoherent
    (hX : X.J = ⊥) (hF : F.IsQuasicoherentOnSite) {U V : X.C} (f : U ⟶ V) :
    IsIso (canonicalMap X F f) := by
  obtain ⟨W, p, s, hs, hW⟩ := splitPresentation_of_isQuasicoherent X F hX hF V
  let Y := sliceRingedSite X W
  have hY : Y.J = ⊥ := sliceRingedSite_J_eq_bot X hX _
  let g : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk f rfl
  exact baseChangeNat_isIso_of_globalPresentation Y hY (F.over W) hW g


private noncomputable def terminalSectionHom (T : X.C) (hT : IsTerminal T)
    (M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (x : M.val.obj (Opposite.op T)) :
    _root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ M where
  val := {
    app := fun Y => ModuleCat.ofHom (show
      ULift.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Y)
        →ₗ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Y] M.val.obj Y from {
      toFun := fun a => a.down • M.val.map (hT.from Y.unop).op x
      map_add' := fun a b => add_smul a.down b.down _
      map_smul' := fun a b => by
        change (a * b.down) • _ = a • (b.down • _)
        exact mul_smul _ _ _ })
    naturality := by
      intro Y Z f
      ext a
      change ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom a.down •
          M.val.map (hT.from Z.unop).op x =
        M.val.map f (a.down • M.val.map (hT.from Y.unop).op x)
      have hf : (hT.from Y.unop).op ≫ f = (hT.from Z.unop).op := by
        apply Quiver.Hom.unop_inj
        exact hT.hom_ext _ _
      exact (congrArg (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f).hom a.down • ·)
          ((M.val.congr_map_apply hf x).symm.trans
            (M.val.map_comp_apply (hT.from Y.unop).op f x))).trans
        (M.val.map_smul f a.down (M.val.map (hT.from Y.unop).op x)).symm }

/-- The sections of `terminalSectionHom` are the multiples of the restriction of `x`. -/
private theorem terminalSectionHom_val_app_up (T : X.C) (hT : IsTerminal T)
    (M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (x : M.val.obj (Opposite.op T))
    (Y : X.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Y) :
    ((terminalSectionHom X T hT M x).val.app Y).hom (ULift.up r)
      = r • M.val.map (hT.from Y.unop).op x := rfl

private theorem terminalSectionHom_app (T : X.C) (hT : IsTerminal T)
    (M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (x : M.val.obj (Opposite.op T)) :
    ((terminalSectionHom X T hT M x).val.app (Opposite.op T)).hom
      (ULift.up (1 : X.O.obj.obj (Opposite.op T))) = x := by
  have ht : (hT.from T).op = 𝟙 (Opposite.op T) := congrArg Quiver.Hom.op (hT.hom_ext _ (𝟙 T))
  refine (terminalSectionHom_val_app_up X T hT M x (Opposite.op T) 1).trans ?_
  refine (one_smul _ _).trans ((M.val.congr_map_apply ht x).trans ?_)
  exact CategoryTheory.congr_fun (M.val.map_id (Opposite.op T)) x

private theorem terminalSectionHom_comp (T : X.C) (hT : IsTerminal T)
    {M N : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (x : M.val.obj (Opposite.op T)) (g : M ⟶ N) :
    terminalSectionHom X T hT M x ≫ g =
      terminalSectionHom X T hT N (g.val.app (Opposite.op T) x) := by
  ext Y a
  have key : ∀ r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Y,
      (ConcreteCategory.hom (g.val.app Y)) (r • M.val.map (hT.from Y.unop).op x)
        = r • N.val.map (hT.from Y.unop).op (g.val.app (Opposite.op T) x) := fun r =>
    (map_smul (ConcreteCategory.hom (g.val.app Y)) r
        (M.val.map (hT.from Y.unop).op x)).trans
      (congrArg (r • ·) (PresheafOfModules.naturality_apply g.val (hT.from Y.unop).op x))
  exact ((congrArg (fun z => (ConcreteCategory.hom (g.val.app Y)) z)
        (terminalSectionHom_val_app_up X T hT M x Y a.down)).trans (key a.down)).trans
    (terminalSectionHom_val_app_up X T hT N (g.val.app (Opposite.op T) x) Y a.down).symm

private theorem terminalSectionHom_zero (T : X.C) (hT : IsTerminal T)
    (M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    terminalSectionHom X T hT M 0 = 0 := by
  ext Y a
  have key : ∀ r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Y,
      r • M.val.map (hT.from Y.unop).op (0 : M.val.obj (Opposite.op T)) = 0 := fun r =>
    (congrArg (r • ·) (map_zero _)).trans (smul_zero r)
  exact (terminalSectionHom_val_app_up X T hT M 0 Y a.down).trans (key a.down)


/-- Sections of a morphism of sheaves of modules over a smaller object of the site are
recovered from sections over a larger one by extension of scalars, as soon as the comparison
maps of the source and the target are isomorphisms. -/
private theorem isIso_siteEvaluation_map_of_isIso_baseChangeNat
    {M N : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : N ⟶ M)
    {U V : X.C} (f : U ⟶ V)
    [IsIso ((baseChangeNat X f).app N)] [IsIso ((baseChangeNat X f).app M)]
    [IsIso ((siteEvaluation X (Opposite.op V)).map g)] :
    IsIso ((siteEvaluation X (Opposite.op U)).map g) := by
  have : IsIso ((baseChangeNat X f).app N ≫ (siteEvaluation X (Opposite.op U)).map g) := by
    rw [← (baseChangeNat X f).naturality g]
    show IsIso ((ModuleCat.extendScalars (X.O.obj.map f.op).hom).map
      ((siteEvaluation X (Opposite.op V)).map g) ≫ (baseChangeNat X f).app M)
    infer_instance
  exact IsIso.of_isIso_comp_left ((baseChangeNat X f).app N) _

/-- A morphism of sheaves of modules that is an isomorphism on the sections over every object
of the site is an isomorphism, the forgetful functor to presheaves of modules reflecting
isomorphisms and isomorphisms of presheaves being detected objectwise. -/
private theorem isIso_of_isIso_siteEvaluation_map
    {M N : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : N ⟶ M)
    (hg : ∀ U : X.C, IsIso ((siteEvaluation X (Opposite.op U)).map g)) : IsIso g := by
  let e := PresheafOfModules.isoMk (fun U => by
    have : IsIso (g.val.app U) := hg U.unop
    exact asIso (g.val.app U)) (fun _ _ f => g.val.naturality f)
  have : IsIso g.val := show IsIso e.hom from inferInstance
  have : IsIso
      ((_root_.SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map g) := by
    show IsIso g.val
    infer_instance
  exact (_root_.SheafOfModules.fullyFaithfulForget
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).isIso_of_isIso_map g

private theorem presentation_of_baseChange_isIso (hX : X.J = ⊥)
    (T : X.C) (hT : IsTerminal T)
    (M : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : ∀ (U : X.C), IsIso ((baseChangeNat X (hT.from U)).app M)) :
    ∃ (I K : Type (max w m))
      (P Q : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ι : ∀ _ : I, _root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ P)
      (κ : ∀ _ : K, _root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶ Q),
      Nonempty (IsColimit (Cofan.mk P ι)) ∧ Nonempty (IsColimit (Cofan.mk Q κ)) ∧
      ∃ (a : Q ⟶ P) (b : P ⟶ M) (hab : a ≫ b = 0),
        Nonempty (IsColimit (CokernelCofork.ofπ b hab)) := by
  classical
  let : HasWeakSheafify X.J AddCommGrpCat.{max w m} := by rw [hX]; infer_instance
  let : X.J.WEqualsLocallyBijective AddCommGrpCat.{max w m} := by
    rw [hX]
    exact botWEqualsLocallyBijective
  have : ∀ J : Type (max m w), HasColimitsOfShape (Discrete J)
      (PresheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
    fun J => PresheafOfModules.hasColimitsOfShape _ _
  have : ∀ J : Type (max m w), HasColimitsOfShape (Discrete J)
      (_root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    fun J => SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _
  let A := _root_.SheafOfModules.uliftForPresentation.{u,v,w,w,m}
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let I := M.val.obj (Opposite.op T)
  let P : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    ∐ (fun _ : I => A)
  let b : P ⟶ M := Sigma.desc (fun x => terminalSectionHom X T hT M x)
  let K := {x : P.val.obj (Opposite.op T) // b.val.app (Opposite.op T) x = 0}
  let Q : _root_.SheafOfModules.{max w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    ∐ (fun _ : K => A)
  let a : Q ⟶ P := Sigma.desc (fun x => terminalSectionHom X T hT P x.1)
  have hab : a ≫ b = 0 := by
    apply Sigma.hom_ext
    intro x
    rw [Sigma.ι_desc_assoc, terminalSectionHom_comp, x.2, terminalSectionHom_zero, comp_zero]
  let E := siteEvaluation.{u,v,w,m} X (Opposite.op T)
  have hb : Function.Surjective (E.map b).hom := by
    intro x
    refine ⟨(Sigma.ι (fun _ : I => A) x).val.app (Opposite.op T)
      (ULift.up (1 : X.O.obj.obj (Opposite.op T))), ?_⟩
    show ((Sigma.ι (fun _ : I => A) x ≫ b).val.app (Opposite.op T)).hom _ = x
    exact (congrArg (fun h : A ⟶ M => (h.val.app (Opposite.op T)).hom
        (ULift.up (1 : X.O.obj.obj (Opposite.op T))))
      (Sigma.ι_desc (fun x => terminalSectionHom X T hT M x) x)).trans
      (terminalSectionHom_app X T hT M x)
  have hex : Function.Exact (E.map a).hom (E.map b).hom := by
    intro x
    constructor
    · intro hx
      let k : K := ⟨x, hx⟩
      refine ⟨(Sigma.ι (fun _ : K => A) k).val.app (Opposite.op T)
        (ULift.up (1 : X.O.obj.obj (Opposite.op T))), ?_⟩
      show ((Sigma.ι (fun _ : K => A) k ≫ a).val.app (Opposite.op T)).hom _ = x
      rw [Sigma.ι_desc]
      exact terminalSectionHom_app X T hT P x
    · rintro ⟨y, rfl⟩
      exact congrArg (fun g : Q ⟶ M => (E.map g).hom y) hab
  let N := cokernel a
  let g : N ⟶ M := cokernel.desc a b hab
  have hg : cokernel.π a ≫ g = b := cokernel.π_desc a b hab
  have hEc : IsColimit (CokernelCofork.ofπ (E.map (cokernel.π a))
      (by rw [← Functor.map_comp, cokernel.condition, Functor.map_zero])) :=
    moduleEvaluationPreservesCokernelOfBot hX (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (Opposite.op T) a (cokernel.π a) (cokernel.condition a) (cokernelIsCokernel a)
  have hEb := ModuleCat.isColimitCokernelCofork (E.map a) (E.map b) hex hb
  have : IsIso (E.map g) := by
    have he : E.map g = (hEc.coconePointUniqueUpToIso hEb).hom := by
      apply Cofork.IsColimit.hom_ext hEc
      show E.map (cokernel.π a) ≫ E.map g = _
      rw [← Functor.map_comp, hg]
      exact (hEc.comp_coconePointUniqueUpToIso_hom hEb WalkingParallelPair.one).symm
    rw [he]
    infer_instance
  have hgU (U : X.C) : IsIso ((siteEvaluation X (Opposite.op U)).map g) := by
    let f := hT.from U
    have := baseChangeNat_isIso_coproduct X hX f I P _ (coproductIsCoproduct _)
    have := baseChangeNat_isIso_coproduct X hX f K Q _ (coproductIsCoproduct _)
    have := baseChangeNat_isIso_cokernel X hX f a (cokernel.π a)
      (cokernel.condition a) (cokernelIsCokernel a)
    have := hM U
    exact isIso_siteEvaluation_map_of_isIso_baseChangeNat X g f
  have : IsIso g := isIso_of_isIso_siteEvaluation_map X g hgU
  have hc : IsColimit (CokernelCofork.ofπ b hab) :=
    Cofork.isColimitOfIsos _ (cokernelIsCokernel a) _ (Iso.refl _) (Iso.refl _) (asIso g)
  exact ⟨I, K, P, Q, Sigma.ι _, Sigma.ι _, ⟨coproductIsCoproduct _⟩,
    ⟨coproductIsCoproduct _⟩, a, b, hab, ⟨hc⟩⟩

/-- A module sheaf on a chaotic site is quasi-coherent precisely when its
canonical base-change maps are isomorphisms. -/
@[stacks 0GZN]
public theorem isQuasicoherent_iff_canonicalMap_isIso
    (hX : X.J = ⊥) :
    F.IsQuasicoherentOnSite ↔
      ∀ ⦃U V : X.C⦄ (f : U ⟶ V), IsIso (canonicalMap X F f) := by
  constructor
  · exact fun h _ _ f => canonicalMap_isIso_of_isQuasicoherent X F hX h f
  · intro h
    constructor
    intro V
    refine ⟨PUnit.{max u v + 1}, fun _ => V, fun _ => 𝟙 V, ?_, ?_⟩
    · rw [hX, GrothendieckTopology.bot_covering]
      apply top_unique
      intro U f _
      exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, f, by simp⟩
    · intro _
      let Y := sliceRingedSite X V
      have hY : Y.J = ⊥ := sliceRingedSite_J_eq_bot X hX _
      let M := _root_.SheafOfModules.uliftForPresentation.{max u v,v,w,w,max u v w} (F.over V)
      have hM (U : Y.C) : IsIso ((baseChangeNat Y (Over.mkIdTerminal.from U)).app M) := by
        apply (baseChangeNat_isIso_ulift_iff.{max u v,v,w,0,max u v w}
          Y (F.over V) _).mpr
        exact h (Over.mkIdTerminal.from U).left
      exact presentation_of_baseChange_isIso.{max u v,v,w,max u v w}
        Y hY (Over.mk (𝟙 V)) Over.mkIdTerminal M hM

end Stacks.SheafOfModules

end
