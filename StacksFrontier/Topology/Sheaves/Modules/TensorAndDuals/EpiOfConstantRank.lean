module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.FiniteType
public import StacksCore.RingTheory.OrezchProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
public import StacksFrontier.Topology.Sheaves.EpiMono.Defs
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Surjections between finite locally free sheaves of the same rank

A morphism between two finite locally free sheaves of modules of the same constant rank `r`
on a ringed space is an isomorphism as soon as it is an epimorphism.

Epimorphy of a morphism of sheaves of modules is local surjectivity of the underlying
morphism of presheaves of abelian groups, so near every point finitely many generating
sections of the target lift; over a small enough neighbourhood both sheaves are free of rank
`r` on bases given by their generating sections, and a surjective endomorphism of a finite
free module over a commutative ring is injective. Local injectivity and local surjectivity
together make the morphism an isomorphism.

## Main definitions

* `Stacks.SheafOfModules.freeEvaluationBasis`: the sections of a free sheaf of modules over an
  object of the site, as a free module.
* `Stacks.SheafOfModules.generatingSectionsBasis`: the basis of sections determined by a
  finite family of generating sections whose associated morphism is an isomorphism.

## Main results

* `Stacks.SheafOfModules.isIso_iff_epi_of_isFiniteLocallyFreeOfRank`: the equivalence of
  Stacks 089Q.
* `Stacks.SheafOfModules.injective_of_surjective_of_linearEquiv_fin`: a surjective
  endomorphism of a finite free module is injective.
* `Stacks.SheafOfModules.weakSheafify_of_siteEquivalence`: weak sheafification transports
  along an equivalence of sites.
* `Stacks.SheafOfModules.exists_lifts_finite`: a locally surjective morphism lifts a finite
  family of sections on one neighbourhood.

## Implementation notes

`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` carries sheafification
hypotheses only for the slices of the site, so the global ones the argument needs are
recovered from the slice over the top open set, along the equivalence between that slice and
the site itself; that is what `weakSheafify_of_siteEquivalence` is for. The strong
`HasSheafify` is then supplied by
`AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective`.

The ringed space is taken with its space and its rings in one universe,
`AlgebraicGeometry.RingedSpace.{u, u}`. This is not a choice: the structure sheaf of rings
`StrictlyPerfect.structureSheafOfRings` is defined only there, because `sheafCompose` along
`forget₂ CommRingCat RingCat` needs `RingCat.{u}` to have limits indexed by the site of open
sets. It is the case that `AlgebraicGeometry.Scheme.{u}` supplies. A binder
`RingedSpace.{u, v}` is not well typed against `structureSheafOfRings`, which
forces the two universe arguments to agree; `RingedSpace.{u, u}` is the same statement, made
well typed, and not a restriction of anything that elaborates.

## References

* [Stacks Project, Tag 089Q](https://stacks.math.columbia.edu/tag/089Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  TopologicalSpace Opposite

universe u v

namespace Stacks.SheafOfModules

/-- A surjective endomorphism of a finite free module of rank `r`, read through two bases,
is injective. This is the Orzech property of a commutative ring. -/
@[sga "3 X 3.8" "Free case"]
lemma injective_of_surjective_of_linearEquiv_fin
    {R : Type u} [CommRing R] {r : ℕ}
    {M N : Type u} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (eM : M ≃ₗ[R] (Fin r → R)) (eN : N ≃ₗ[R] (Fin r → R))
    (hf : Function.Surjective f) : Function.Injective f := by
  let g : Module.End R (Fin r → R) := eN.toLinearMap.comp (f.comp eM.symm.toLinearMap)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨z, hz⟩ := hf (eN.symm y)
    exact ⟨eM z, by simp [g, hz]⟩
  have hginj := (OrzechProperty.bijective_of_surjective_endomorphism g hg).1
  exact fun x y hxy => eM.injective (hginj (by simp [g, hxy]))

/-- Weak sheafification transports along an equivalence of sites whose inverse is a dense
subsite. -/
theorem weakSheafify_of_siteEquivalence
    {C D : Type*} [Category C] [Category D]
    (e : C ≌ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (A : Type*) [Category A] [e.inverse.IsDenseSubsite K J]
    [HasWeakSheafify J A] : HasWeakSheafify K A := by
  let F : (Dᵒᵖ ⥤ A) ⥤ Sheaf K A :=
    e.symm.op.congrLeft.functor ⋙ presheafToSheaf J A ⋙ (e.sheafCongr J K A).functor
  let adj₁ := e.symm.op.congrLeft.toAdjunction.comp (sheafificationAdjunction J A)
  let adj := adj₁.comp (e.sheafCongr J K A).toAdjunction
  let iso : (e.sheafCongr J K A).inverse ⋙ sheafToPresheaf J A ⋙
      e.symm.op.congrLeft.inverse ≅ sheafToPresheaf K A :=
    NatIso.ofComponents (fun P => e.symm.op.congrLeft.unitIso.symm.app P.obj)
      fun f => e.symm.op.congrLeft.unitIso.symm.hom.naturality f.hom
  exact ⟨F, ⟨adj.ofNatIsoRight iso⟩⟩

section

variable {C : Type v} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (I : Type u) [Finite I] (Y : Cᵒᵖ)

/-- Evaluation of sheaves of modules at an object of the site is an additive functor. -/
local instance : (_root_.SheafOfModules.evaluation.{u} R Y).Additive where
  map_add := rfl

/-- The sections of a free sheaf of modules over an object of the site form a free module on
the same index set, because evaluation preserves finite coproducts. -/
noncomputable def freeEvaluationBasis :
    Module.Basis I (R.obj.obj Y) ((_root_.SheafOfModules.free (R := R) I).val.obj Y) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let ev := _root_.SheafOfModules.evaluation.{u} R Y
  letI := PreservesFiniteCoproducts.of_preserves_binary_and_initial ev I
  let hc := isColimitCofanMkObjOfIsColimit ev _ _
    (_root_.SheafOfModules.isColimitFreeCofan (R := R) I)
  let hd := ModuleCat.coproductCoconeIsColimit
    (fun _ : I => ev.obj (_root_.SheafOfModules.unit R))
  let e := hc.coconePointUniqueUpToIso hd
  exact (Pi.basisFun (R.obj.obj Y) I).map
    ((e.toLinearEquiv.trans DFinsupp.linearEquivFunOnFintype).symm)

/-- The basis of `freeEvaluationBasis` consists of the images of `1` under the coprojections
of the free sheaf. -/
lemma freeEvaluationBasis_apply (i : I) :
    freeEvaluationBasis R I Y i =
      (_root_.SheafOfModules.ιFree (R := R) i).val.app Y (1 : R.obj.obj Y) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let ev := _root_.SheafOfModules.evaluation.{u} R Y
  have := PreservesFiniteCoproducts.of_preserves_binary_and_initial ev I
  let hc := isColimitCofanMkObjOfIsColimit ev _ _
    (_root_.SheafOfModules.isColimitFreeCofan (R := R) I)
  let hd := ModuleCat.coproductCoconeIsColimit
    (fun _ : I => ev.obj (_root_.SheafOfModules.unit R))
  have h := hd.comp_coconePointUniqueUpToIso_hom hc (Discrete.mk i)
  have h' := congrArg (fun k => k (1 : R.obj.obj Y)) h
  show (hc.coconePointUniqueUpToIso hd).inv
    ((DFinsupp.linearEquivFunOnFintype (R := R.obj.obj Y)).symm (Pi.basisFun (R.obj.obj Y) I i)) = _
  have hb : (DFinsupp.linearEquivFunOnFintype (R := R.obj.obj Y)).symm
      (Pi.basisFun (R.obj.obj Y) I i) =
      DirectSum.lof (R.obj.obj Y) I (fun _ => R.obj.obj Y) i 1 := by
    ext j
    show (Pi.basisFun (R.obj.obj Y) I i) j =
      (DFinsupp.single (β := fun _ : I => R.obj.obj Y) i (1 : R.obj.obj Y)) j
    by_cases hij : i = j <;> simp [Pi.basisFun_apply, hij]
  exact (congrArg (ConcreteCategory.hom (hc.coconePointUniqueUpToIso hd).inv) hb).trans h'

/-- A finite family of generating sections whose associated morphism from the free sheaf is
an isomorphism is a basis of the sections over every object of the site. -/
noncomputable def generatingSectionsBasis (M : _root_.SheafOfModules.{u} R)
    (s : M.GeneratingSections) [Finite s.I] [IsIso s.π] (Y : Cᵒᵖ) :
    Module.Basis s.I (R.obj.obj Y) (M.val.obj Y) :=
  (freeEvaluationBasis R s.I Y).map
    ((_root_.SheafOfModules.evaluation R Y).mapIso (asIso s.π)).toLinearEquiv

/-- The basis of `generatingSectionsBasis` consists of the generating sections themselves. -/
lemma generatingSectionsBasis_apply (M : _root_.SheafOfModules.{u} R)
    (s : M.GeneratingSections) [Finite s.I] [IsIso s.π] (Y : Cᵒᵖ) (i : s.I) :
    generatingSectionsBasis R M s Y i = (s.s i).val Y := by
  show s.π.val.app Y (freeEvaluationBasis R s.I Y i) = _
  rw [freeEvaluationBasis_apply]
  have h := congrArg M.unitHomEquiv
    (_root_.SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply s.π i)
  simp only [Equiv.apply_symm_apply, _root_.SheafOfModules.GeneratingSections.π] at h
  exact congrArg (fun t : M.sections => t.val Y) h.symm

end

/-- A locally surjective morphism of presheaves of abelian groups on a space lifts a finite
family of sections simultaneously, on a single smaller neighbourhood of any given point. -/
lemma exists_lifts_finite
    {X : TopCat.{v}} {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    [hf : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f]
    {I : Type u} [Finite I] (U : Opens X) (s : I → Q.obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧
      ∀ j, ∃ t, f.app (op V) t = Q.map i.op (s j) := by
  classical
  choose V i ht hxV using fun j => hf.imageSieve_mem (s j) x hx
  let W := U ⊓ ⨅ j, V j
  have hWV (j : I) : W ≤ V j := le_trans inf_le_right (iInf_le V j)
  have hxW : x ∈ W := by
    refine ⟨hx, ?_⟩
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr hxV
  refine ⟨W, homOfLE inf_le_left, hxW, fun j => ?_⟩
  obtain ⟨t, ht⟩ := ht j
  refine ⟨P.map (homOfLE (hWV j)).op t, ?_⟩
  rw [NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply, ← Q.map_comp]
  rfl

/-- Near any point, a finite locally free sheaf of rank `r` has locally free generators indexed
by a type equivalent to `Fin r`. -/
private lemma exists_finite_free_generators
    {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
    [∀ U : Opens X, ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    (M : _root_.SheafOfModules.{u} R) (r : ℕ)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank M r] (x : X) :
    ∃ (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) (i : q.I), x ∈ q.X i ∧
      q.IsLocallyFreeData ∧ Finite (q.generators i).I ∧ Nonempty ((q.generators i).I ≃ Fin r) := by
  obtain ⟨q, hq, hr⟩ := hM.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff X q.X).mp q.coversTop).exists_mem x
  exact ⟨q, i, hi, hq, Finite.of_equiv (Fin r) (hr i).some.symm, hr i⟩

/-- **Stacks 089Q.** A morphism between finite locally free sheaves of modules of the same
rank is an isomorphism if and only if it is surjective. -/
@[stacks 089Q]
theorem isIso_iff_epi_of_isFiniteLocallyFreeOfRank
    (X : RingedSpace.{u, u})
    [∀ U : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
    [∀ U : Opens X, ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    {F G : _root_.SheafOfModules.{u} (StrictlyPerfect.structureSheafOfRings X)} (r : ℕ)
    [@AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank _ _ _
      (StrictlyPerfect.structureSheafOfRings X) _ _ F r]
    [@AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank _ _ _
      (StrictlyPerfect.structureSheafOfRings X) _ _ G r] (f : F ⟶ G) :
    IsIso f ↔ Epi f := by
  constructor
  · intro hf
    have : IsIso f := hf
    infer_instance
  · intro hf
    classical
    let R := StrictlyPerfect.structureSheafOfRings X
    let J := Opens.grothendieckTopology X.carrier
    let U : Opens X.carrier := ⊤
    let G₀ := Over.forget U
    have : G₀.IsEquivalence :=
      (Over.equivalenceOfIsTerminal (Limits.isTerminalTop : IsTerminal U)).isEquivalence_functor
    have : G₀.IsDenseSubsite (J.over U) J := by
      have htop : J.over U = G₀.inducedTopology J := by
        ext Y S
        rw [GrothendieckTopology.mem_over_iff]
        rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
        rfl
      rw [htop]
      infer_instance
    let e : Over U ≌ Opens X.carrier := G₀.asEquivalence
    have : e.functor.IsCocontinuous (J.over U) J := by
      show G₀.IsCocontinuous (J.over U) J
      infer_instance
    have : e.inverse.IsCocontinuous J (J.over U) := by
      have h : CoverPreserving (J.over U) J e.functor := by
        show CoverPreserving (J.over U) J G₀
        exact GrothendieckTopology.over_forget_coverPreserving J U
      exact (e.symm.toAdjunction.isCocontinuous_iff_coverPreserving
        J (J.over U)).2 h
    have : e.symm.inverse.IsDenseSubsite (J.over U) J := by
      show G₀.IsDenseSubsite (J.over U) J
      infer_instance
    have : e.inverse.IsDenseSubsite J (J.over U) := by
      exact e.isDenseSubsite_inverse_of_isCocontinuous (J.over U) J
    have : HasWeakSheafify J AddCommGrpCat.{u} :=
      weakSheafify_of_siteEquivalence e (J.over U) J AddCommGrpCat.{u}
    have : (G₀.sheafPushforwardContinuous AddCommGrpCat.{u} (J.over U) J).EssSurj := by
      show (e.symm.sheafCongr J (J.over U) AddCommGrpCat.{u}).functor.EssSurj
      infer_instance
    have : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
      GrothendieckTopology.WEqualsLocallyBijective.transport J (J.over U) G₀
        (GrothendieckTopology.over_forget_coverPreserving J U)
    have : HasSheafify J AddCommGrpCat.{u} :=
      AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    let h := (_root_.SheafOfModules.forget R).map f
    let φ := (PresheafOfModules.toPresheaf R.obj).map h
    have hloc : Presheaf.IsLocallySurjective J φ :=
      EpiMono.isLocallySurjective_of_epi f
    have hnear : ∀ (T : Opens X) (x : X), x ∈ T →
        ∃ (V : Opens X) (i : V ⟶ T), x ∈ V ∧
          Function.Injective (f.val.app (op V)) := by
      intro T x hxT
      obtain ⟨qF, iF, hiF, hqF, hFfin, hrF⟩ := exists_finite_free_generators F r x
      obtain ⟨qG, iG, hiG, hqG, hGfin, hrG⟩ := exists_finite_free_generators G r x
      let W := T ⊓ (qF.X iF ⊓ qG.X iG)
      have hxW : x ∈ W := ⟨hxT, hiF, hiG⟩
      let aG : W ⟶ qG.X iG := homOfLE (le_trans inf_le_right inf_le_right)
      let s : (qG.generators iG).I → G.val.obj (op W) :=
        fun j => ((qG.generators iG).s j).val (op (Over.mk aG))
      obtain ⟨V, k, hxV, hlift⟩ := exists_lifts_finite φ W s x hxW
      let aF : V ⟶ qF.X iF := k ≫ homOfLE (le_trans inf_le_right inf_le_left)
      let aG' : V ⟶ qG.X iG := k ≫ aG
      let A := R.obj.obj (op V)
      let : CommRing A := inferInstanceAs (CommRing (X.presheaf.obj (op V)))
      let bF : Module.Basis (qF.generators iF).I A (F.val.obj (op V)) :=
        generatingSectionsBasis (R.over (qF.X iF)) (F.over (qF.X iF))
          (qF.generators iF) (op (Over.mk aF))
      let bG : Module.Basis (qG.generators iG).I A (G.val.obj (op V)) :=
        generatingSectionsBasis (R.over (qG.X iG)) (G.over (qG.X iG))
          (qG.generators iG) (op (Over.mk aG'))
      let fV : F.val.obj (op V) →ₗ[A] G.val.obj (op V) := (f.val.app (op V)).hom
      have hsurj : Function.Surjective fV := by
        rw [← LinearMap.range_eq_top]
        apply top_unique
        rw [← bG.span_eq]
        refine Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => ?_)
        obtain ⟨t, ht⟩ := hlift j
        refine ⟨t, ?_⟩
        rw [show bG j = ((qG.generators iG).s j).val (op (Over.mk aG')) from
          generatingSectionsBasis_apply _ _ _ _ j]
        let l : Over.mk aG' ⟶ Over.mk aG := Over.homMk k (by rfl)
        exact ht.trans (((qG.generators iG).s j).property l.op)
      have hinj : Function.Injective fV :=
        injective_of_surjective_of_linearEquiv_fin fV
          (bF.reindex hrF.some).equivFun
          (bG.reindex hrG.some).equivFun hsurj
      exact ⟨V, k ≫ homOfLE inf_le_left, hxV, hinj⟩
    have hlinj : Presheaf.IsLocallyInjective J φ := by
      refine ⟨?_⟩
      intro T a b hab x hx
      obtain ⟨V, i, hxV, hi⟩ := hnear T.unop x hx
      refine ⟨V, i, ?_, hxV⟩
      apply hi
      show φ.app (op V) (F.val.presheaf.map i.op a) =
        φ.app (op V) (F.val.presheaf.map i.op b)
      exact (NatTrans.naturality_apply φ i.op a).trans
        ((congrArg (G.val.presheaf.map i.op) hab).trans
          (NatTrans.naturality_apply φ i.op b).symm)
    have : IsIso ((_root_.SheafOfModules.toSheaf R).map f) :=
      (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hlinj, hloc⟩
    exact isIso_of_reflects_iso f (_root_.SheafOfModules.toSheaf R)


end Stacks.SheafOfModules
