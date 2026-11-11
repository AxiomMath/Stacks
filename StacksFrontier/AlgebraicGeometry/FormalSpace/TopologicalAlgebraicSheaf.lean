module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Category.TopCommRingCat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TopologicalSheaf
public import StacksFrontier.CategoryTheory.Sites.Point.ElementColimitSkyscraper
public import StacksFrontier.CategoryTheory.Sites.SheafificationOfClosedSubobjects
public import StacksFrontier.Topology.Algebra.RingColimits
public import StacksFrontier.Topology.Algebra.RingLimits

/-!
# Sheaves of topological abelian groups, rings and modules on a site

Stacks 0AI4 discusses sheafification of presheaves of topological spaces and states that the
same arguments work for presheaves of topological abelian groups, topological rings and
topological modules over a given topological ring. This file records those variants, for

* `TopModuleCat R`, topological modules over a topological ring `R` (Mathlib);
* `TopAddCommGrpCat`, topological abelian groups, realised as topological modules over the
  discrete ring `ℤ` (`TopAddCommGrpCat.of` and `TopAddCommGrpCat.homEquiv` identify its objects
  and morphisms with topological abelian groups and continuous additive maps);
* `TopCommRingCat`, topological (commutative) rings (Mathlib; its limits and colimits are in
  `StacksFrontier.Topology.Algebra.RingLimits` and `StacksFrontier.Topology.Algebra.RingColimits`).

For each of them: sheaves have limits, computed sectionwise; every map from a fixed presheaf to
a sheaf factors through a subsheaf of bounded size; sheafification exists; and for a point `p` of
the site given by `u : C ⥤ Sets` satisfying conditions (1) and (2) of Stacks 00Y5, the skyscraper
presheaf `U ↦ ∏_{x ∈ u(U)} M` is a sheaf and `F_p = (F^#)_p`.

The common argument is `CategoryTheory.HasClosedSubobjects` (substructures, here submodules and
subrings, with the induced topology) and `CategoryTheory.HasSmallModels` (structures transported
to subsets of a fixed set), fed into
`CategoryTheory.exists_bounded_subsheaf_factorization_of_closedSubobjects` and
`CategoryTheory.hasWeakSheafify_of_closedSubobjects`.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w v u

/-! ## Topological modules -/

namespace TopModuleCat

variable {R : Type w} [Ring R] [TopologicalSpace R]

/-- A submodule of a topological module, with the subspace topology, as an object. -/
noncomputable abbrev subObj (X : TopModuleCat.{w} R) (M : Submodule R X) : TopModuleCat.{w} R :=
  haveI : ContinuousAdd M := continuousAdd_induced M.subtype
  haveI : ContinuousSMul R M := continuousSMul_induced M.subtype
  TopModuleCat.of R M

omit [TopologicalSpace R] in
lemma isClosedSub_sInter_aux {X : Type*} [AddCommGroup X] [Module R X]
    (𝒮 : Set (Set X)) (h : ∀ S ∈ 𝒮, ∃ M : Submodule R X, (M : Set X) = S) :
    ((sInf {N : Submodule R X | (N : Set X) ∈ 𝒮} : Submodule R X) : Set X) = ⋂₀ 𝒮 := by
  rw [Submodule.coe_sInf]
  ext x
  simp only [Set.mem_iInter, Set.mem_sInter, Set.mem_ofPred_eq]
  constructor
  · intro hx S hS
    obtain ⟨N, rfl⟩ := h S hS
    exact hx N hS
  · intro hx N hN
    exact hx _ hN

omit [TopologicalSpace R] in
lemma isClosedSub_sUnion_aux {X : Type*} [AddCommGroup X] [Module R X]
    (𝒮 : Set (Set X)) (hne : 𝒮.Nonempty) (hd : DirectedOn (· ⊆ ·) 𝒮)
    (h : ∀ S ∈ 𝒮, ∃ M : Submodule R X, (M : Set X) = S) :
    ((sSup {N : Submodule R X | (N : Set X) ∈ 𝒮} : Submodule R X) : Set X) = ⋃₀ 𝒮 := by
  have hne' : {N : Submodule R X | (N : Set X) ∈ 𝒮}.Nonempty := by
    obtain ⟨S, hS⟩ := hne
    obtain ⟨N, hN⟩ := h S hS
    exact ⟨N, show (N : Set X) ∈ 𝒮 from hN ▸ hS⟩
  have hd' : DirectedOn (· ≤ ·) {N : Submodule R X | (N : Set X) ∈ 𝒮} := by
    intro N₁ h₁ N₂ h₂
    obtain ⟨S₃, h₃, hs₁, hs₂⟩ := hd _ h₁ _ h₂
    obtain ⟨N₃, hN₃⟩ := h S₃ h₃
    refine ⟨N₃, show (N₃ : Set X) ∈ 𝒮 from hN₃ ▸ h₃, ?_, ?_⟩
    · exact SetLike.coe_subset_coe.1 (hN₃ ▸ hs₁)
    · exact SetLike.coe_subset_coe.1 (hN₃ ▸ hs₂)
  ext x
  rw [SetLike.mem_coe, Submodule.mem_sSup_of_directed hne' hd', Set.mem_sUnion]
  constructor
  · rintro ⟨N, hN, hx⟩
    exact ⟨_, hN, hx⟩
  · rintro ⟨S, hS, hx⟩
    obtain ⟨N, rfl⟩ := h S hS
    exact ⟨N, hS, hx⟩

noncomputable instance : HasClosedSubobjects (TopModuleCat.{w} R) where
  IsClosedSub X S := ∃ M : Submodule R X, (M : Set X) = S
  isClosedSub_range f := ⟨LinearMap.range f.hom.toLinearMap, LinearMap.coe_range _⟩
  isClosedSub_preimage f := by
    rintro _ ⟨M, rfl⟩
    exact ⟨M.comap f.hom.toLinearMap, Submodule.comap_coe _ _⟩
  isClosedSub_sInter 𝒮 h := ⟨_, isClosedSub_sInter_aux 𝒮 h⟩
  isClosedSub_sUnion 𝒮 hne hd h := ⟨_, isClosedSub_sUnion_aux 𝒮 hne hd h⟩
  sub X _ hS := subObj X hS.choose
  subι X _ hS := ConcreteCategory.ofHom (C := TopModuleCat.{w} R) (X := subObj X hS.choose)
    (Y := X) ⟨hS.choose.subtype, continuous_subtype_val⟩
  injective_subι _ _ _ := Subtype.val_injective
  range_subι X S hS := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hS.choose_spec.subset y.2
    · intro hx
      exact ⟨⟨x, hS.choose_spec.symm.subset hx⟩, rfl⟩
  subLift {E X} S hS f h := ConcreteCategory.ofHom (C := TopModuleCat.{w} R) (X := E)
    (Y := subObj X hS.choose)
    ⟨f.hom.toLinearMap.codRestrict hS.choose fun x =>
      hS.choose_spec.symm.subset (h ⟨x, rfl⟩),
      f.hom.continuous.subtype_mk _⟩
  subLift_subι _ _ _ _ := rfl

/-- The structure of a topological module on a type. -/
structure TopModuleStr (R : Type w) [Ring R] [TopologicalSpace R] (S : Type w) where
  [instAddCommGroup : AddCommGroup S]
  [instModule : Module R S]
  [instTop : TopologicalSpace S]
  [instContinuousAdd : ContinuousAdd S]
  [instContinuousSMul : ContinuousSMul R S]

/-- The topological module given by a structure on a subset of a fixed set. -/
noncomputable def ofStr {T : Type w} (m : Σ S : Set T, TopModuleStr R S) : TopModuleCat.{w} R :=
  letI := m.2.instAddCommGroup
  letI := m.2.instModule
  letI := m.2.instTop
  haveI := m.2.instContinuousAdd
  haveI := m.2.instContinuousSMul
  TopModuleCat.of R m.1

noncomputable instance : HasSmallModels (TopModuleCat.{w} R) where
  Model κ := Σ S : Set κ.ord.ToType, TopModuleStr R S
  toObj m := ofStr m
  exists_iso κ X h := by
    let j : X ↪ κ.ord.ToType := Classical.choice (Cardinal.lift_mk_le'.1 (by simpa using h))
    let S : Set κ.ord.ToType := Set.range j
    let e : X ≃ S := Equiv.ofInjective j j.injective
    let : AddCommGroup S := e.symm.addCommGroup
    let eA : S ≃+ X := e.symm.addEquiv
    let : Module R S := eA.module R
    let L : S ≃ₗ[R] X := eA.linearEquiv R
    let : TopologicalSpace S := TopologicalSpace.induced L inferInstance
    let str : TopModuleStr R S :=
      { instContinuousAdd := continuousAdd_induced L
        instContinuousSMul := continuousSMul_induced L }
    refine ⟨⟨S, str⟩, ⟨TopModuleCat.ofIso (X := ofStr ⟨S, str⟩)
      { L with
        continuous_toFun := continuous_induced_dom
        continuous_invFun := continuous_induced_rng.2
          (continuous_id.congr fun x => (L.apply_symm_apply x).symm) }⟩⟩

instance : PreservesLimitsOfSize.{w, w} (forget (TopModuleCat.{w} R)) := by
  rw [← HasForget₂.forget_comp (C := TopModuleCat.{w} R) (D := TopCat.{w})]
  infer_instance

end TopModuleCat

/-! ## Topological abelian groups -/

/-- The category of topological abelian groups, realised as the category of topological modules
over the discrete ring `ℤ` (lifted to the universe `w`). A topological `ℤ`-module is exactly a
topological abelian group: see `TopAddCommGrpCat.of` and `TopAddCommGrpCat.homEquiv`. -/
abbrev TopAddCommGrpCat : Type (w + 1) := TopModuleCat.{w} (ULift.{w} ℤ)

namespace TopAddCommGrpCat

/-- A topological abelian group, as an object of `TopAddCommGrpCat`, with its canonical
`ℤ`-module structure. -/
noncomputable abbrev of (M : Type w) [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] : TopAddCommGrpCat.{w} :=
  haveI : ContinuousSMul (ULift.{w} ℤ) M :=
    ⟨continuous_prod_of_discrete_left.2 fun n => continuous_zsmul n.down⟩
  TopModuleCat.of (ULift.{w} ℤ) M

/-- The morphisms of `TopAddCommGrpCat` are exactly the continuous additive maps. -/
noncomputable def homEquiv (X Y : TopAddCommGrpCat.{w}) :
    (X ⟶ Y) ≃ ContinuousAddMonoidHom X Y where
  toFun f := ⟨f.hom.toLinearMap.toAddMonoidHom, f.hom.continuous⟩
  invFun g := ConcreteCategory.ofHom (C := TopAddCommGrpCat.{w}) (X := X) (Y := Y)
    ⟨{ toFun := g
       map_add' := map_add g
       map_smul' := fun n x => by
         have h : ((n.down : ℤ) : ULift.{w} ℤ) = n := ULift.ext (by simp)
         rw [RingHom.id_apply, ← h, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
         exact map_zsmul g n.down x }, g.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TopAddCommGrpCat

/-! ## Topological commutative rings -/

namespace TopCommRingCat

/-- A subring of a topological commutative ring, with the subspace topology, as an object. -/
abbrev subObj (X : TopCommRingCat.{w}) (M : Subring X) : TopCommRingCat.{w} :=
  TopCommRingCat.of M

lemma isClosedSub_sInter_aux {X : Type*} [CommRing X]
    (𝒮 : Set (Set X)) (h : ∀ S ∈ 𝒮, ∃ M : Subring X, (M : Set X) = S) :
    ((sInf {N : Subring X | (N : Set X) ∈ 𝒮} : Subring X) : Set X) = ⋂₀ 𝒮 := by
  rw [Subring.coe_sInf]
  ext x
  simp only [Set.mem_iInter, Set.mem_sInter, Set.mem_ofPred_eq]
  constructor
  · intro hx S hS
    obtain ⟨N, rfl⟩ := h S hS
    exact hx N hS
  · intro hx N hN
    exact hx _ hN

lemma isClosedSub_sUnion_aux {X : Type*} [CommRing X]
    (𝒮 : Set (Set X)) (hne : 𝒮.Nonempty) (hd : DirectedOn (· ⊆ ·) 𝒮)
    (h : ∀ S ∈ 𝒮, ∃ M : Subring X, (M : Set X) = S) :
    ((sSup {N : Subring X | (N : Set X) ∈ 𝒮} : Subring X) : Set X) = ⋃₀ 𝒮 := by
  have hne' : {N : Subring X | (N : Set X) ∈ 𝒮}.Nonempty := by
    obtain ⟨S, hS⟩ := hne
    obtain ⟨N, hN⟩ := h S hS
    exact ⟨N, show (N : Set X) ∈ 𝒮 from hN ▸ hS⟩
  have hd' : DirectedOn (· ≤ ·) {N : Subring X | (N : Set X) ∈ 𝒮} := by
    intro N₁ h₁ N₂ h₂
    obtain ⟨S₃, h₃, hs₁, hs₂⟩ := hd _ h₁ _ h₂
    obtain ⟨N₃, hN₃⟩ := h S₃ h₃
    refine ⟨N₃, show (N₃ : Set X) ∈ 𝒮 from hN₃ ▸ h₃, ?_, ?_⟩
    · exact SetLike.coe_subset_coe.1 (hN₃ ▸ hs₁)
    · exact SetLike.coe_subset_coe.1 (hN₃ ▸ hs₂)
  rw [Subring.coe_sSup_of_directedOn hne' hd']
  ext x
  simp only [Set.mem_iUnion, Set.mem_sUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨N, hN, hx⟩
    exact ⟨_, hN, hx⟩
  · rintro ⟨S, hS, hx⟩
    obtain ⟨N, rfl⟩ := h S hS
    exact ⟨N, hS, hx⟩

noncomputable instance : HasClosedSubobjects TopCommRingCat.{w} where
  IsClosedSub X S := ∃ M : Subring X, (M : Set X) = S
  isClosedSub_range f := ⟨f.1.range, RingHom.coe_range _⟩
  isClosedSub_preimage f := by
    rintro _ ⟨M, rfl⟩
    exact ⟨M.comap f.1, Subring.coe_comap _ _⟩
  isClosedSub_sInter 𝒮 h := ⟨_, isClosedSub_sInter_aux 𝒮 h⟩
  isClosedSub_sUnion 𝒮 hne hd h := ⟨_, isClosedSub_sUnion_aux 𝒮 hne hd h⟩
  sub X _ hS := subObj X hS.choose
  subι X _ hS := ⟨hS.choose.subtype, continuous_subtype_val⟩
  injective_subι _ _ _ := Subtype.val_injective
  range_subι X S hS := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hS.choose_spec.subset y.2
    · intro hx
      exact ⟨⟨x, hS.choose_spec.symm.subset hx⟩, rfl⟩
  subLift {E X} S hS f h :=
    ⟨f.1.codRestrict hS.choose fun x =>
      hS.choose_spec.symm.subset (h ⟨x, rfl⟩),
      f.2.subtype_mk _⟩
  subLift_subι _ _ _ _ := rfl

/-- The structure of a topological commutative ring on a type. -/
structure TopCommRingStr (S : Type w) where
  [instCommRing : CommRing S]
  [instTop : TopologicalSpace S]
  [instIsTopologicalRing : IsTopologicalRing S]

/-- The topological commutative ring given by a structure on a subset of a fixed set. -/
def ofStr {T : Type w} (m : Σ S : Set T, TopCommRingStr S) : TopCommRingCat.{w} :=
  letI := m.2.instCommRing
  letI := m.2.instTop
  haveI := m.2.instIsTopologicalRing
  TopCommRingCat.of m.1

noncomputable instance : HasSmallModels TopCommRingCat.{w} where
  Model κ := Σ S : Set κ.ord.ToType, TopCommRingStr S
  toObj m := ofStr m
  exists_iso κ X h := by
    let j : X ↪ κ.ord.ToType := Classical.choice (Cardinal.lift_mk_le'.1 (by simpa using h))
    let S : Set κ.ord.ToType := Set.range j
    let e : X ≃ S := Equiv.ofInjective j j.injective
    let : CommRing S := e.symm.commRing
    let L : S ≃+* X := e.symm.ringEquiv
    let : TopologicalSpace S := TopologicalSpace.induced L inferInstance
    have h₁ : ContinuousAdd S := continuousAdd_induced L
    have h₂ : ContinuousMul S := continuousMul_induced L
    have h₃ : ContinuousNeg S :=
      @IsTopologicalAddGroup.toContinuousNeg _ _ _ (isTopologicalAddGroup_induced L)
    have : IsTopologicalRing S := { }
    let str : TopCommRingStr S := { }
    refine ⟨⟨S, str⟩, ⟨⟨⟨L.toRingHom, continuous_induced_dom⟩,
      ⟨L.symm.toRingHom, continuous_induced_rng.2
        (continuous_id.congr fun x => (L.apply_symm_apply x).symm)⟩,
      Subtype.ext (RingHom.ext fun x => L.symm_apply_apply x),
      Subtype.ext (RingHom.ext fun x => L.apply_symm_apply x)⟩⟩⟩

instance : PreservesLimitsOfSize.{w, w} (forget TopCommRingCat.{w}) := by
  rw [← HasForget₂.forget_comp (C := TopCommRingCat.{w}) (D := TopCat.{w})]
  infer_instance

end TopCommRingCat

/-! ## The variants of Stacks 0AI4 -/

namespace CategoryTheory.TopologicalSheaf

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private instance preservesLimitsOfSize_forget_topModuleCat
    (R : Type (max u v w)) [Ring R] [TopologicalSpace R] :
    PreservesLimitsOfSize.{v, max v u} (forget (TopModuleCat.{max u v w} R)) :=
  preservesLimitsOfSize_of_univLE.{max u v w, max u v w, v, max v u} _

private instance preservesLimitsOfSize_forget_topCommRingCat :
    PreservesLimitsOfSize.{v, max v u} (forget TopCommRingCat.{max u v w}) :=
  preservesLimitsOfSize_of_univLE.{max u v w, max u v w, v, max v u} _

/-- **Stacks 0AI4** (limits), for sheaves of topological modules over a topological ring `R`:
`Sh(C, TopMod_R)` has limits, the inclusion into presheaves preserves them, and limits of
presheaves are computed sectionwise. -/
@[stacks 0AI4 "limits (topological modules)"]
theorem hasLimits_sheaf_topModuleCat (R : Type (max u v w)) [Ring R] [TopologicalSpace R] :
    HasLimitsOfSize.{max u v w, max u v w} (Sheaf J (TopModuleCat.{max u v w} R)) ∧
      PreservesLimitsOfSize.{max u v w, max u v w}
        (sheafToPresheaf J (TopModuleCat.{max u v w} R)) ∧
      ∀ U : Cᵒᵖ, PreservesLimitsOfSize.{max u v w, max u v w}
        ((evaluation Cᵒᵖ (TopModuleCat.{max u v w} R)).obj U) :=
  ⟨inferInstance, inferInstance, fun _ => inferInstance⟩

/-- **Stacks 0AI4** (limits), for sheaves of topological abelian groups. -/
@[stacks 0AI4 "limits (topological abelian groups)"]
theorem hasLimits_sheaf_topAddCommGrpCat :
    HasLimitsOfSize.{max u v w, max u v w} (Sheaf J TopAddCommGrpCat.{max u v w}) ∧
      PreservesLimitsOfSize.{max u v w, max u v w}
        (sheafToPresheaf J TopAddCommGrpCat.{max u v w}) ∧
      ∀ U : Cᵒᵖ, PreservesLimitsOfSize.{max u v w, max u v w}
        ((evaluation Cᵒᵖ TopAddCommGrpCat.{max u v w}).obj U) :=
  hasLimits_sheaf_topModuleCat J _

/-- **Stacks 0AI4** (limits), for sheaves of topological rings. -/
@[stacks 0AI4 "limits (topological rings)"]
theorem hasLimits_sheaf_topCommRingCat :
    HasLimitsOfSize.{max u v w, max u v w} (Sheaf J TopCommRingCat.{max u v w}) ∧
      PreservesLimitsOfSize.{max u v w, max u v w}
        (sheafToPresheaf J TopCommRingCat.{max u v w}) ∧
      ∀ U : Cᵒᵖ, PreservesLimitsOfSize.{max u v w, max u v w}
        ((evaluation Cᵒᵖ TopCommRingCat.{max u v w}).obj U) :=
  ⟨inferInstance, inferInstance, fun _ => inferInstance⟩

/-- **Stacks 0AI4** (bounded subsheaf), for sheaves of topological modules over a topological
ring `R`: any map from a fixed presheaf to a sheaf factors through a subsheaf whose values have
cardinality bounded by a cardinal depending only on the site and the presheaf. -/
@[stacks 0AI4 "bounded_subsheaf (topological modules)"]
theorem exists_bounded_subsheaf_factorization_topModuleCat
    (R : Type (max u v w)) [Ring R] [TopologicalSpace R]
    (F : Cᵒᵖ ⥤ TopModuleCat.{max u v w} R) :
    ∃ κ : Cardinal.{max u v w}, ∀ (G : Sheaf J (TopModuleCat.{max u v w} R)) (f : F ⟶ G.obj),
      ∃ (G' : Sheaf J (TopModuleCat.{max u v w} R)) (i : G' ⟶ G), Mono i ∧
        (∀ U : Cᵒᵖ, Cardinal.mk (G'.obj.obj U) ≤ κ) ∧ ∃ f' : F ⟶ G'.obj, f' ≫ i.hom = f :=
  exists_bounded_subsheaf_factorization_of_closedSubobjects F

/-- **Stacks 0AI4** (bounded subsheaf), for sheaves of topological abelian groups. -/
@[stacks 0AI4 "bounded_subsheaf (topological abelian groups)"]
theorem exists_bounded_subsheaf_factorization_topAddCommGrpCat
    (F : Cᵒᵖ ⥤ TopAddCommGrpCat.{max u v w}) :
    ∃ κ : Cardinal.{max u v w}, ∀ (G : Sheaf J TopAddCommGrpCat.{max u v w}) (f : F ⟶ G.obj),
      ∃ (G' : Sheaf J TopAddCommGrpCat.{max u v w}) (i : G' ⟶ G), Mono i ∧
        (∀ U : Cᵒᵖ, Cardinal.mk (G'.obj.obj U) ≤ κ) ∧ ∃ f' : F ⟶ G'.obj, f' ≫ i.hom = f :=
  exists_bounded_subsheaf_factorization_topModuleCat J _ F

/-- **Stacks 0AI4** (bounded subsheaf), for sheaves of topological rings. -/
@[stacks 0AI4 "bounded_subsheaf (topological rings)"]
theorem exists_bounded_subsheaf_factorization_topCommRingCat
    (F : Cᵒᵖ ⥤ TopCommRingCat.{max u v w}) :
    ∃ κ : Cardinal.{max u v w}, ∀ (G : Sheaf J TopCommRingCat.{max u v w}) (f : F ⟶ G.obj),
      ∃ (G' : Sheaf J TopCommRingCat.{max u v w}) (i : G' ⟶ G), Mono i ∧
        (∀ U : Cᵒᵖ, Cardinal.mk (G'.obj.obj U) ≤ κ) ∧ ∃ f' : F ⟶ G'.obj, f' ≫ i.hom = f :=
  exists_bounded_subsheaf_factorization_of_closedSubobjects F

/-- **Stacks 0AI4** (sheafification), for presheaves of topological modules over a topological
ring `R`: the inclusion of sheaves into presheaves has a left adjoint. -/
@[stacks 0AI4 "sheafification (topological modules)"]
noncomputable instance hasWeakSheafify_topModuleCat (R : Type (max u v w)) [Ring R]
    [TopologicalSpace R] : HasWeakSheafify J (TopModuleCat.{max u v w} R) :=
  hasWeakSheafify_of_closedSubobjects J

/-- **Stacks 0AI4** (sheafification), for presheaves of topological abelian groups. -/
@[stacks 0AI4 "sheafification (topological abelian groups)"]
noncomputable instance hasWeakSheafify_topAddCommGrpCat :
    HasWeakSheafify J TopAddCommGrpCat.{max u v w} :=
  hasWeakSheafify_topModuleCat J _

/-- **Stacks 0AI4** (sheafification), for presheaves of topological rings. -/
@[stacks 0AI4 "sheafification (topological rings)"]
noncomputable instance hasWeakSheafify_topCommRingCat :
    HasWeakSheafify J TopCommRingCat.{max u v w} :=
  hasWeakSheafify_of_closedSubobjects J

end

section Point

variable {C : Type w} [SmallCategory C] {K : Precoverage C} [K.HasPullbacks]
  [K.IsStableUnderBaseChange] {u : C ⥤ Type w}

/-- **Stacks 0AI4** (the sheaf `U ↦ Map(u(U), M)`), for topological modules over a topological
ring `R`, topological abelian groups (`R = ℤ`) and, by
`isSheaf_skyscraperPresheaf_topCommRingCat`, topological rings: for a point of the site given by
`u : C ⥤ Sets` satisfying conditions (1) and (2) of Stacks 00Y5 and a topological module `M`, the
presheaf `U ↦ ∏_{x ∈ u(U)} M` (the product in `TopModuleCat R`, i.e. with the product topology) is
a sheaf. -/
@[stacks 0AI4 "point_mapping_sheaf (topological modules and abelian groups)"]
theorem isSheaf_skyscraperPresheaf_topModuleCat (R : Type w) [Ring R] [TopologicalSpace R]
    (h₁ : ∀ ⦃X : C⦄ (P : Presieve X), P ∈ K X → ∀ x : u.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : P f) (y : u.obj Y), u.map f y = x)
    (h₂ : ∀ ⦃X : C⦄ (P : Presieve X), P ∈ K X → ∀ ⦃Y Z : C⦄ (f : Y ⟶ X), P f →
      ∀ (g : Z ⟶ X) [HasPullback f g], Function.Bijective (pullbackComparison u f g))
    (M : TopModuleCat.{w} R) :
    Presheaf.IsSheaf K.toGrothendieck (ElementColimit.skyscraperPresheaf u M) :=
  ElementColimit.isSheaf_skyscraperPresheaf h₁ h₂ M

/-- **Stacks 0AI4** (the sheaf `U ↦ Map(u(U), M)`), for topological rings: the presheaf
`U ↦ ∏_{x ∈ u(U)} M` (the product in `TopCommRingCat`, with the product topology) is a sheaf. -/
@[stacks 0AI4 "point_mapping_sheaf (topological rings)"]
theorem isSheaf_skyscraperPresheaf_topCommRingCat
    (h₁ : ∀ ⦃X : C⦄ (P : Presieve X), P ∈ K X → ∀ x : u.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : P f) (y : u.obj Y), u.map f y = x)
    (h₂ : ∀ ⦃X : C⦄ (P : Presieve X), P ∈ K X → ∀ ⦃Y Z : C⦄ (f : Y ⟶ X), P f →
      ∀ (g : Z ⟶ X) [HasPullback f g], Function.Bijective (pullbackComparison u f g))
    (M : TopCommRingCat.{w}) :
    Presheaf.IsSheaf K.toGrothendieck (ElementColimit.skyscraperPresheaf u M) :=
  ElementColimit.isSheaf_skyscraperPresheaf h₁ h₂ M

/-- **Stacks 0AI4** (sheafification commutes with stalks), for presheaves of topological modules
over a topological ring `R` (and so of topological abelian groups, `R = ℤ`): for a point of the
site given by `u : C ⥤ Sets` satisfying conditions (1) and (2) of Stacks 00Y5, the canonical map
`F_p ⟶ (F^#)_p` is an isomorphism, the stalk being the colimit in `TopModuleCat R` over the
category of neighbourhoods. -/
@[stacks 0AI4 "stalk_preservation (topological modules and abelian groups)"]
theorem isIso_elementColimit_map_toSheafify_topModuleCat (R : Type w) [Ring R]
    [TopologicalSpace R]
    (h₁ : ∀ ⦃X : C⦄ (P : Presieve X), P ∈ K X → ∀ x : u.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : P f) (y : u.obj Y), u.map f y = x)
    (h₂ : ∀ ⦃X : C⦄ (P : Presieve X), P ∈ K X → ∀ ⦃Y Z : C⦄ (f : Y ⟶ X), P f →
      ∀ (g : Z ⟶ X) [HasPullback f g], Function.Bijective (pullbackComparison u f g))
    (F : Cᵒᵖ ⥤ TopModuleCat.{w} R) :
    IsIso ((elementColimit u (TopModuleCat.{w} R)).map (toSheafify K.toGrothendieck F)) :=
  ElementColimit.isIso_elementColimit_map_toSheafify h₁ h₂ F

/-- **Stacks 0AI4** (sheafification commutes with stalks), for presheaves of topological rings:
the canonical map `F_p ⟶ (F^#)_p` is an isomorphism, the stalk being the colimit in
`TopCommRingCat` over the category of neighbourhoods. -/
@[stacks 0AI4 "stalk_preservation (topological rings)"]
theorem isIso_elementColimit_map_toSheafify_topCommRingCat
    (h₁ : ∀ ⦃X : C⦄ (P : Presieve X), P ∈ K X → ∀ x : u.obj X,
      ∃ (Y : C) (f : Y ⟶ X) (_ : P f) (y : u.obj Y), u.map f y = x)
    (h₂ : ∀ ⦃X : C⦄ (P : Presieve X), P ∈ K X → ∀ ⦃Y Z : C⦄ (f : Y ⟶ X), P f →
      ∀ (g : Z ⟶ X) [HasPullback f g], Function.Bijective (pullbackComparison u f g))
    (F : Cᵒᵖ ⥤ TopCommRingCat.{w}) :
    IsIso ((elementColimit u TopCommRingCat.{w}).map (toSheafify K.toGrothendieck F)) :=
  ElementColimit.isIso_elementColimit_map_toSheafify h₁ h₂ F

end Point

end CategoryTheory.TopologicalSheaf
