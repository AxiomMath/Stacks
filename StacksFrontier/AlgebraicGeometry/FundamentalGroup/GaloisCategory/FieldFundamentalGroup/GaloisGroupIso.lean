module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.FieldFundamentalGroup.FiberComparison

/-!
# The étale fundamental group of a field: the absolute Galois group

Let `K` be a field with separable closure `L` and an algebraically closed algebraic extension
`Ω ⊇ L`. Transporting the tautological action of `Gal(L/K)` through the equivalence
`FÉt_{Spec K} ≌ ContAction FintypeCat Gal(L/K)` and identifying both sides with automorphism
groups of fibre functors produces the canonical isomorphism of profinite groups
`Gal(L/K) ≃ₜ* π₁(Spec K, x)`.

## Main results

* `AlgebraicGeometry.galoisEquivEtaleFundamentalGroup` — the canonical isomorphism of profinite
  groups, with `AlgebraicGeometry.galoisEquivEtaleFundamentalGroup_apply` specifying its action
  on geometric fibres.

## Implementation notes

Both automorphism-group topologies in play are the one of Tag 0BMR; the group isomorphism is
assembled from three continuous isomorphisms, the profinite-completion universal property of
Tag 0BMU, and the Galois-functor data of Tag 0BN5, each of which contributes a continuous
bijection whose inverse is continuous because the source is compact and the target Hausdorff.

## References

* [Stacks Project, Tag 0BNE](https://stacks.math.columbia.edu/tag/0BNE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete
open scoped CategoryTheory.PreGaloisCategory

universe u v w

namespace AlgebraicGeometry


/-- For a functor `H` to finite sets, composing with the inclusion of finite sets into types is a
continuous isomorphism of automorphism groups. -/
public def autFintypeInclContinuousMulEquiv {D : Type (u + 1)} [Category.{u, u + 1} D]
    (H : D ⥤ FintypeCat.{u}) :
    @ContinuousMulEquiv (Aut H)
      (CategoryTheory.PreGaloisCategory.instTopologicalSpaceAutFunctorFintypeCat H)
      (Aut ((Functor.whiskeringRight D FintypeCat.{u} (Type u)).obj
        FintypeCat.incl |>.obj H))
      (CategoryTheory.functorAutomorphismTopology
        (((Functor.whiskeringRight D FintypeCat.{u} (Type u)).obj
          FintypeCat.incl).obj H)) _ _ := by
  let W : (D ⥤ FintypeCat.{u}) ⥤ (D ⥤ Type u) :=
    (Functor.whiskeringRight D FintypeCat.{u} (Type u)).obj FintypeCat.incl
  let hW := (Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight D
  let m := W.mapAut H
  let me := hW.autMulEquivOfFullyFaithful H
  letI : TopologicalSpace (Aut H) :=
    CategoryTheory.PreGaloisCategory.instTopologicalSpaceAutFunctorFintypeCat H
  letI : IsTopologicalGroup (Aut H) := inferInstance
  letI : TopologicalSpace (Aut (W.obj H)) :=
    CategoryTheory.functorAutomorphismTopology (W.obj H)
  letI : IsTopologicalGroup (Aut (W.obj H)) :=
    CategoryTheory.functorAutomorphismIsTopologicalGroup (W.obj H)
  have hmcont : Continuous m := by
    let (X : D) : TopologicalSpace ((W.obj H).obj X) := ⊥
    let (X : D) : DiscreteTopology ((W.obj H).obj X) := ⟨rfl⟩
    let (X : D) : TopologicalSpace (Equiv.Perm ((W.obj H).obj X)) := autTopology
    let : TopologicalSpace (∀ X : D, Equiv.Perm ((W.obj H).obj X)) := inferInstance
    apply continuous_induced_rng.mpr
    change Continuous (fun σ : Aut H => fun X : D => ((m σ).app X).toEquiv)
    rw [continuous_pi_iff]
    intro X
    let : TopologicalSpace (FintypeCat.incl.obj (H.obj X)) := ⊥
    let : DiscreteTopology (FintypeCat.incl.obj (H.obj X)) := ⟨rfl⟩
    let : TopologicalSpace (H.obj X ≅ H.obj X) := ⊥
    let : DiscreteTopology (H.obj X ≅ H.obj X) := ⟨rfl⟩
    change Continuous (fun σ : Aut H => (FintypeCat.incl.mapIso (σ.app X)).toEquiv)
    have hcomp : Continuous (CategoryTheory.PreGaloisCategory.autEmbedding H) :=
      continuous_induced_dom
    have hev : Continuous (fun σ : Aut H =>
        CategoryTheory.PreGaloisCategory.autEmbedding H σ X) :=
      (continuous_apply X).comp hcomp
    have hconv : Continuous (fun τ : H.obj X ≅ H.obj X =>
        (FintypeCat.incl.mapIso τ).toEquiv) := continuous_of_discreteTopology
    exact hconv.comp hev
  letI : ∀ X : D, Finite ((W.obj H).obj X) := fun X => (H.obj X).property
  have hprof : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop (Aut (W.obj H)) :=
    CategoryTheory.isProfiniteGrp_functorAutomorphismTopology (W.obj H)
  letI : CompactSpace (Aut (W.obj H)) := hprof.1
  letI : T2Space (Aut (W.obj H)) := hprof.2.1
  exact {
    toMulEquiv := me
    continuous_toFun := hmcont
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := me.toEquiv) hmcont }

/-- A profinite completion map out of a profinite group is bijective. -/
public theorem _root_.CategoryTheory.IsProfiniteCompletion.bijective
    {G : Type u} {P : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] {c : G →ₜ* P}
    (hcG : CategoryTheory.IsProfiniteCompletion.{u, v, u} c)
    (hG : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop G)
    (hcP : CategoryTheory.IsProfiniteCompletion.{u, v, v} c) :
    Function.Bijective c := by
  obtain ⟨f, hf⟩ := (hcG.2 G hG).2 (ContinuousMonoidHom.id G)
  have hfc (x : G) : f (c x) = x := DFunLike.congr_fun hf x
  have hcf : c.comp f = ContinuousMonoidHom.id _ := by
    apply (hcP.2 P hcP.1).1
    apply ContinuousMonoidHom.ext
    intro x
    show c (f (c x)) = c x
    rw [hfc]
  exact ⟨fun x y hxy => (hfc x).symm.trans ((congrArg f hxy).trans (hfc y)),
    fun y => ⟨f y, DFunLike.congr_fun hcf y⟩⟩

/-- For a profinite group `G`, the canonical map from `G` to the automorphism group of the
forgetful functor on finite continuous `G`-sets is an isomorphism of topological groups. -/
public def canonicalContinuousMulEquiv (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    letI : TopologicalSpace (Aut (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙
      FintypeCat.incl)) := CategoryTheory.functorAutomorphismTopology _
    G ≃ₜ* Aut (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl) := by
  let F' : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u} :=
    forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}
  letI : TopologicalSpace (Aut (F' ⋙ FintypeCat.incl)) :=
    CategoryTheory.functorAutomorphismTopology _
  letI : IsTopologicalGroup (Aut (F' ⋙ FintypeCat.incl)) :=
    CategoryTheory.functorAutomorphismIsTopologicalGroup _
  let c : G →ₜ* Aut (F' ⋙ FintypeCat.incl) := CategoryTheory.canonicalHom G
  have hcompG : CategoryTheory.IsProfiniteCompletion.{u, u + 1, u} c :=
    CategoryTheory.profiniteCompletionEquiv_forgetAut.{u, u} G
  have hcompP : CategoryTheory.IsProfiniteCompletion.{u, u + 1, u + 1} c :=
    CategoryTheory.profiniteCompletionEquiv_forgetAut.{u, u + 1} G
  have hP : Stacks.Chapter05.Tag_0BR1.IsProfiniteTop (Aut (F' ⋙ FintypeCat.incl)) := hcompP.1
  letI : CompactSpace (Aut (F' ⋙ FintypeCat.incl)) := hP.1
  letI : T2Space (Aut (F' ⋙ FintypeCat.incl)) := hP.2.1
  let m := MulEquiv.ofBijective c.toMonoidHom
    (hcompG.bijective ⟨inferInstance, inferInstance, inferInstance⟩ hcompP)
  exact {
    toMulEquiv := m
    continuous_toFun := c.continuous_toFun
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := m.toEquiv) c.continuous_toFun }

/-- The homomorphism induced along an equivalence and an isomorphism of fibre functors is an
isomorphism of topological groups. -/
public def _root_.CategoryTheory.Equivalence.autContinuousMulEquivOfFiberIso
    {C D : Type*} [Category C] [Category D] (E : C ≌ D)
    {F : C ⥤ FintypeCat.{u}} {F' : D ⥤ FintypeCat.{u}} (t : E.functor ⋙ F' ≅ F)
    [CompactSpace (Aut F')] [T2Space (Aut F)] : Aut F' ≃ₜ* Aut F :=
  let data := CategoryTheory.galoisFunctorDataOfFiberIso F F' E.functor t
  have hbij : Function.Bijective data.hom := by
    change Function.Bijective data.hom.toMonoidHom
    rw [data.hom_toMonoidHom]
    let W := (Functor.whiskeringLeft C D FintypeCat.{u}).obj E.functor
    let hW : W.FullyFaithful := (Equivalence.congrLeft E).fullyFaithfulInverse
    change Function.Bijective (fun x => t.conjAut (W.mapAut F' x))
    exact t.conjAut.bijective.comp
      (Functor.FullyFaithful.autMulEquivOfFullyFaithful (f := W) hW F').bijective
  { toMulEquiv := MulEquiv.ofBijective data.hom.toMonoidHom hbij
    continuous_toFun := data.hom.continuous_toFun
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective data.hom.toMonoidHom hbij).toEquiv)
      data.hom.continuous_toFun }

/-- The canonical isomorphism from the absolute Galois group to the étale
fundamental group: its action on a fibre is precomposition on the corresponding
separable-closure point. -/
@[stacks 0BNE "part (2)",
  sga "1 IX 6.1" "π₁(Spec k, special case",
  sga "1 V 8.1" "special case",
  sga "4½ Arcata 2.4.1"]
public noncomputable def galoisEquivEtaleFundamentalGroup
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω] :
    Gal(L/K) ≃ₜ*
      EtaleFundamentalGroup (Spec (.of K))
        (algebraicClosureGeometricPoint K Ω) := by
  classical
  let C := FiniteEtaleOver (Spec (.of K))
  let G := Gal(L/K)
  let FType := finiteEtaleFiberFunctor (algebraicClosureGeometricPoint K Ω)
  let E := finiteEtaleEquivalenceGaloisSets K L Ω
  let F : C ⥤ FintypeCat.{u} := algebraicClosureFiberFintypeFunctor K L Ω
  let F' : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u} :=
    forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}
  let t : E.functor ⋙ F' ≅ F := finiteEtaleFiberActionIso K L Ω
  letI : TopologicalSpace (Aut (F' ⋙ FintypeCat.incl)) :=
    CategoryTheory.functorAutomorphismTopology _
  letI : IsTopologicalGroup (Aut (F' ⋙ FintypeCat.incl)) :=
    CategoryTheory.functorAutomorphismIsTopologicalGroup _
  letI : TopologicalSpace (Aut (((Functor.whiskeringRight
      (ContAction FintypeCat.{u} G) FintypeCat.{u} (Type u)).obj
      FintypeCat.incl).obj F')) :=
    CategoryTheory.functorAutomorphismTopology
      (((Functor.whiskeringRight (ContAction FintypeCat.{u} G)
        FintypeCat.{u} (Type u)).obj FintypeCat.incl).obj F')
  letI : TopologicalSpace (Aut (F ⋙ FintypeCat.incl)) :=
    CategoryTheory.functorAutomorphismTopology _
  letI : IsTopologicalGroup (Aut (F ⋙ FintypeCat.incl)) :=
    CategoryTheory.functorAutomorphismIsTopologicalGroup _
  letI : TopologicalSpace (Aut (((Functor.whiskeringRight C FintypeCat.{u}
      (Type u)).obj FintypeCat.incl).obj F)) :=
    CategoryTheory.functorAutomorphismTopology
      (((Functor.whiskeringRight C FintypeCat.{u} (Type u)).obj
        FintypeCat.incl).obj F)
  letI : ∀ Y : C, Finite (FType.obj Y) := fun Y =>
    finite_finiteEtaleFiber_algebraicClosureGeometricPoint K L Ω Y
  letI : ∀ Y : C, Finite ((F ⋙ FintypeCat.incl).obj Y) := fun Y => (F.obj Y).property
  letI : ∀ Y : ContAction FintypeCat.{u} G,
      Finite ((F' ⋙ FintypeCat.incl).obj Y) := fun Y => Y.obj.V.property
  let eLimit := InfiniteGalois.continuousMulEquivToLimit K L
  letI : CompactSpace G := eLimit.symm.compactSpace
  letI : T2Space G := eLimit.symm.t2Space
  letI : TotallyDisconnectedSpace G := eLimit.symm.totallyDisconnectedSpace
  let eG : G ≃ₜ* Aut (F' ⋙ FintypeCat.incl) := canonicalContinuousMulEquiv G
  letI : TopologicalSpace (Aut FType) :=
    CategoryTheory.functorAutomorphismTopology FType
  letI : IsTopologicalGroup (Aut FType) :=
    CategoryTheory.functorAutomorphismIsTopologicalGroup FType
  letI : T2Space (Aut (F ⋙ FintypeCat.incl)) :=
    (CategoryTheory.isProfiniteGrp_functorAutomorphismTopology (F ⋙ FintypeCat.incl)).2.1
  change G ≃ₜ* Aut FType
  exact eG.trans ((autFintypeInclContinuousMulEquiv F').symm.trans
    ((E.autContinuousMulEquivOfFiberIso t).trans (autFintypeInclContinuousMulEquiv F)))

/-- The homomorphism of Galois-functor data intertwines the fibre isomorphism. -/
public theorem _root_.CategoryTheory.GaloisFunctorData.hom_app_fiberIso_hom_apply
    {C C' : Type*} [Category C] [Category C']
    {F : C ⥤ FintypeCat.{u}} {F' : C' ⥤ FintypeCat.{u}} {H : C ⥤ C'} {t : H ⋙ F' ≅ F}
    (data : GaloisFunctorData F F' H t) (a : Aut F') (Y : C) (x : (F'.obj (H.obj Y)).obj) :
    ConcreteCategory.hom ((data.hom a).hom.app Y) (ConcreteCategory.hom (t.hom.app Y) x) =
      ConcreteCategory.hom (t.hom.app Y) (ConcreteCategory.hom (a.hom.app (H.obj Y)) x) := by
  have hcomm := (data.actionIso.hom.app Y).hom.comm a
  simp only [data.actionIso_hom_app Y] at hcomm
  let A := ((PreGaloisCategory.functorToContAction F ⋙
    ContAction.res FintypeCat data.hom).obj Y).obj.ρ a
  let B := ((H ⋙ PreGaloisCategory.functorToContAction F').obj Y).obj.ρ a
  have hcommx := ConcreteCategory.congr_hom hcomm (ConcreteCategory.hom (t.hom.app Y) x)
  change ConcreteCategory.hom (t.inv.app Y)
      (ConcreteCategory.hom A (ConcreteCategory.hom (t.hom.app Y) x)) =
    ConcreteCategory.hom B
      (ConcreteCategory.hom (t.inv.app Y) (ConcreteCategory.hom (t.hom.app Y) x)) at hcommx
  have h' : ConcreteCategory.hom A (ConcreteCategory.hom (t.hom.app Y) x) =
      ConcreteCategory.hom (t.hom.app Y) (ConcreteCategory.hom B x) :=
    ((FintypeCat.inv_hom_id_apply (t.app Y) _).symm.trans
      (congrArg (ConcreteCategory.hom (t.hom.app Y)) hcommx)).trans
      (congrArg (fun z => ConcreteCategory.hom (t.hom.app Y) (ConcreteCategory.hom B z))
        (FintypeCat.hom_inv_id_apply (t.app Y) x))
  exact h'

/-- `galoisEquivEtaleFundamentalGroup` acts on a geometric fibre through the Galois action
transported along `finiteEtaleFiberIso`. -/
public theorem galoisEquivEtaleFundamentalGroup_app_finiteEtaleFiberIso_hom
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    (Y : FiniteEtaleOver (Spec (.of K))) (σ : Gal(L/K))
    (y : ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj) :
    (((galoisEquivEtaleFundamentalGroup K L Ω) σ).app Y).hom
        ((finiteEtaleFiberIso K L Ω).hom.app Y y) =
      (finiteEtaleFiberIso K L Ω).hom.app Y
        (ConcreteCategory.hom
          (((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.ρ σ) y) := by
  classical
  let G := Gal(L/K)
  let E := finiteEtaleEquivalenceGaloisSets K L Ω
  let F := algebraicClosureFiberFintypeFunctor K L Ω
  let F' : ContAction FintypeCat.{u} G ⥤ FintypeCat.{u} :=
    forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}
  let tAction : E.functor ⋙ F' ≅ F := finiteEtaleFiberActionIso K L Ω
  let data := CategoryTheory.galoisFunctorDataOfFiberIso F F' E.functor tAction
  let eSource : Aut F ≃* Aut (F ⋙ FintypeCat.incl) :=
    ((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight
      (FiniteEtaleOver (Spec (.of K)))).autMulEquivOfFullyFaithful F
  let eAction : Aut F' ≃* Aut (F' ⋙ FintypeCat.incl) :=
    ((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight
      (ContAction FintypeCat.{u} G)).autMulEquivOfFullyFaithful F'
  let : TopologicalSpace (Aut (F' ⋙ FintypeCat.incl)) :=
    CategoryTheory.functorAutomorphismTopology (F' ⋙ FintypeCat.incl)
  let : IsTopologicalGroup (Aut (F' ⋙ FintypeCat.incl)) :=
    CategoryTheory.functorAutomorphismIsTopologicalGroup (F' ⋙ FintypeCat.incl)
  let c : G →ₜ* Aut (F' ⋙ FintypeCat.incl) := CategoryTheory.canonicalHom G
  let a := eAction.symm (c σ)
  have hpreimage (x : (E.functor.obj Y).obj.V.obj) :
      ConcreteCategory.hom (a.hom.app (E.functor.obj Y)) x =
        ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ) x := by
    have h := congrArg
      (fun γ : Aut (F' ⋙ FintypeCat.incl) =>
        ConcreteCategory.hom (γ.hom.app (E.functor.obj Y)) x)
      (eAction.apply_symm_apply (c σ))
    change ConcreteCategory.hom (a.hom.app (E.functor.obj Y)) x =
      ConcreteCategory.hom (((CategoryTheory.canonicalHom G) σ).hom.app
        (E.functor.obj Y)) x at h
    rwa [CategoryTheory.canonicalHom_apply] at h
  show ConcreteCategory.hom ((eSource (data.hom a)).hom.app Y)
      (ConcreteCategory.hom ((finiteEtaleFiberIso K L Ω).hom.app Y) y) =
    ConcreteCategory.hom ((finiteEtaleFiberIso K L Ω).hom.app Y)
      (ConcreteCategory.hom ((E.functor.obj Y).obj.ρ σ) y)
  calc
    _ = ConcreteCategory.hom ((data.hom a).hom.app Y)
        (ConcreteCategory.hom (tAction.hom.app Y) y) := rfl
    _ = ConcreteCategory.hom (tAction.hom.app Y)
        (ConcreteCategory.hom (a.hom.app (E.functor.obj Y)) y) :=
      data.hom_app_fiberIso_hom_apply a Y y
    _ = _ := by
      rw [hpreimage]
      rfl

/-- A point over `L` whose extension to `Ω` lies over `Spec K` lies over `Spec K` itself. -/
public theorem comp_eq_spec_algebraMap_of_spec_comp_eq
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of K)) (f : Spec (.of L) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ f ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :
    f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  have hgeom : Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ (f ≫ g) =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [h, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    ext k
    exact IsScalarTower.algebraMap_apply K L Ω k
  have hr : Spec.homEquiv (f ≫ g) ≫ CommRingCat.ofHom (algebraMap L Ω) =
      CommRingCat.ofHom (algebraMap K L) ≫ CommRingCat.ofHom (algebraMap L Ω) := by
    simpa [Spec.homEquiv, Spec.preimage_comp] using congrArg Spec.preimage hgeom
  have hr' : Spec.homEquiv (f ≫ g) = CommRingCat.ofHom (algebraMap K L) :=
    CommRingCat.hom_ext <| RingHom.ext fun k => (algebraMap L Ω).injective
      (congrArg (fun φ : CommRingCat.of K ⟶ CommRingCat.of Ω => φ.hom k) hr)
  apply Spec.homEquiv.injective
  simpa [Spec.homEquiv] using hr'

/-- The canonical group isomorphism acts on geometric fibres through the
absolute Galois action on separable-closure points. -/
@[stacks 0BNE "part (2): action formula",
  sga "1 V 8.1" "Canonicity clause",
  sga "4½ Arcata 2.4.2" "partial"]
public theorem galoisEquivEtaleFundamentalGroup_apply
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [IsSepClosure K L] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    (Y : FiniteEtaleOver (Spec (.of K)))
    (σ : Gal(L/K))
    (p : finiteEtaleFiber
      (algebraicClosureGeometricPoint K Ω) Y)
    (f : Spec (.of L) ⟶ Y.left)
    (hf : p.1 = Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ f) :
    ((((galoisEquivEtaleFundamentalGroup K L Ω) σ).app Y).hom p).1 =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ f := by
  classical
  have hbase : f ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    comp_eq_spec_algebraMap_of_spec_comp_eq K L Ω Y.hom f (by
      rw [← Category.assoc, ← hf]
      exact p.2)
  let y := (finiteEtaleFiberIso K L Ω).inv.app Y p
  have hy : (finiteEtaleFiberIso K L Ω).hom.app Y y = p := by
    dsimp [y]
    exact congrArg (fun g => g p)
      (congrArg (fun η => η.app Y) (finiteEtaleFiberIso K L Ω).inv_hom_id)
  let y' : ((finiteEtaleEquivalenceGaloisSets K L Ω).functor.obj Y).obj.V.obj := y
  have hpoint : separableFiberEquiv K L Ω Y y' = ⟨f, hbase⟩ :=
    (algebraicPointExtensionEquiv K L Ω Y).injective <| Subtype.ext <|
      (finiteEtaleFiberIso_apply K L Ω Y y').symm.trans ((congrArg Subtype.val hy).trans hf)
  rw [← hy, galoisEquivEtaleFundamentalGroup_app_finiteEtaleFiberIso_hom K L Ω Y σ y',
    finiteEtaleFiberIso_apply, separableFiberEquiv_smul, congrArg Subtype.val hpoint]

end AlgebraicGeometry

end
