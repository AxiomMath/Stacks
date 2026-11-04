module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PointSheaf
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree

/-!
# A coherent module with zero-dimensional support is a sum of point-supported pieces

Let `X` be a scheme whose underlying space is Noetherian and `𝓕` a coherent `𝒪_X`-module with
`dim Supp(𝓕) ≤ 0`. Then `Supp(𝓕) = {x₁, …, xₙ}` is a finite set of closed points, and
`𝓕 ≅ ⨁ᵢ j_{i!} j_i^* 𝓕`, where `j_i : Uᵢ → X` is the inclusion of an affine open neighbourhood
of `xᵢ` containing no other point of the support. Each summand is coherent with support exactly
`{xᵢ}`. This is the reduction of the construction of [Stacks, Section 0G07] to sheaves
supported at a single closed point, inside an affine open.

The decomposition map is the sum `⨁ᵢ j_{i!} j_i^* 𝓕 ⟶ 𝓕` of the counits of `j_{i!} ⊣ j_i^*`; it
is an isomorphism on stalks, because at `xᵢ` the only summand with nonzero stalk is the `i`-th one,
whose counit is an isomorphism on stalks over `Uᵢ`, and off the support every stalk vanishes.
Coherence of the summands follows because each is a direct summand, hence the kernel of an
endomorphism, of `𝓕` ([Stacks, Tag 01BY]).

## Main results

* `CategoryTheory.Limits.isIso_map_biproduct_desc_of_isZero`: an additive functor sends
  `biproduct.desc f` to an isomorphism if it kills every summand but one and sends the
  remaining component to an isomorphism.
* `ExtensionByZeroModules.isIso_stalk_counit_app_of_mem`: the counit `j_! j^* G ⟶ G` is an
  isomorphism on stalks at points of `U`.
* `Orlov.exists_iso_biproduct_of_topologicalKrullDim_supp_le_zero`: the decomposition.

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (Φ : C ⥤ D) [Φ.Additive] {J : Type} [Fintype J] {A : J → C} [HasBiproduct A]

/-- An additive functor which kills every summand of a finite biproduct kills the biproduct. -/
theorem isZero_obj_biproduct_of_isZero (h : ∀ j, IsZero (Φ.obj (A j))) :
    IsZero (Φ.obj (⨁ A)) := by
  rw [IsZero.iff_id_eq_zero, ← Φ.map_id, ← biproduct.total, Φ.map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Φ.map_comp, (h j).eq_zero_of_tgt (Φ.map (biproduct.π A j)), zero_comp]

/-- **An additive functor inverts `biproduct.desc f` if it kills all summands but one.** If
`Φ (A j) = 0` for `j ≠ i` and `Φ (f i)` is an isomorphism, then `Φ (biproduct.desc f)` is an
isomorphism: `Φ` sends the inclusion of the `i`-th summand to an isomorphism. -/
theorem isIso_map_biproduct_desc_of_isZero {B : C} (f : ∀ j, A j ⟶ B) (i : J)
    (h : ∀ j, j ≠ i → IsZero (Φ.obj (A j))) [IsIso (Φ.map (f i))] :
    IsIso (Φ.map (biproduct.desc f)) := by
  have hpi : Φ.map (biproduct.π A i) ≫ Φ.map (biproduct.ι A i) = 𝟙 _ := by
    rw [← Φ.map_comp, ← Φ.map_id, ← biproduct.total, Φ.map_sum,
      Finset.sum_eq_single i (fun j _ hj => by
        rw [Φ.map_comp, (h j hj).eq_zero_of_tgt (Φ.map (biproduct.π A j)), zero_comp])
        (fun hi => (hi (Finset.mem_univ i)).elim)]
  have : IsIso (Φ.map (biproduct.ι A i)) :=
    ⟨⟨Φ.map (biproduct.π A i), by rw [← Φ.map_comp, biproduct.ι_π_self, Φ.map_id], hpi⟩⟩
  have : IsIso (Φ.map (biproduct.ι A i) ≫ Φ.map (biproduct.desc f)) := by
    rw [← Φ.map_comp, biproduct.ι_desc]
    infer_instance
  exact IsIso.of_isIso_comp_left (Φ.map (biproduct.ι A i)) _

end CategoryTheory.Limits

namespace ExtensionByZeroModules

variable {X : TopCat.{u}} (U : Opens X) (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **The counit `j_!(j^*G) ⟶ G` is an isomorphism on stalks at points of `U`**: `j^*` of it is
split by the unit, which is invertible, and stalks at points of `U` are stalks of the
restriction. -/
theorem isIso_stalk_counit_app_of_mem (G : SheafOfModules.{u} O) (x : X) (hx : x ∈ U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((toAb O).map ((jShriekAdjunction U O).counit.app G))) := by
  have := isIso_jShriekAdjunction_unit U O
  set φ := (jShriekAdjunction U O).counit.app G
  have hR : IsIso ((jStar U O).map φ) :=
    isIso_of_hom_comp_eq_id _ ((jShriekAdjunction U O).right_triangle_components G)
  have hwhisk : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op ((toAb O).map φ)) := by
    rw [← toAb_jStar_map U O φ]
    exact Functor.map_isIso (toAb (resRing U O)) ((jStar U O).map φ)
  have hw : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : Usp U)).map
      (Functor.whiskerLeft (TopCat.Presheaf.imF U).op ((toAb O).map φ))) :=
    Functor.map_isIso _ _
  simpa using (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
    ((toAb O).map φ) ⟨x, hx⟩).mp hw

end ExtensionByZeroModules

namespace Stacks.AlgebraicGeometry.DerivedVarieties.Orlov

open _root_.AlgebraicGeometry ExtensionByZeroModules

/-- **A retract of a coherent module is coherent**: if `s ≫ p = 𝟙 A` with `s : A ⟶ F` and `F`
coherent, then `A` is the kernel of the endomorphism `𝟙 F - p ≫ s` of `F`, hence coherent
([Stacks, Tag 01BY]). -/
theorem isCoherent_of_comp_eq_id {T : Type u} [TopologicalSpace T]
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} {A F : SheafOfModules.{u} R}
    (s : A ⟶ F) (p : F ⟶ A) (hsp : s ≫ p = 𝟙 A) (hF : F.IsCoherent) : A.IsCoherent := by
  let q : F ⟶ F := 𝟙 F - p ≫ s
  have hkq := Stacks.AlgebraicGeometry.ProperMapping.isCoherent_kernel hF hF q
  have hsq : s ≫ q = 0 := by
    simp only [q, Preadditive.comp_sub, Category.comp_id, reassoc_of% hsp, sub_self]
  have hιq : kernel.ι q ≫ p ≫ s = kernel.ι q := by
    have h := kernel.condition q
    simp only [q, Preadditive.comp_sub, Category.comp_id] at h
    exact (sub_eq_zero.mp h).symm
  let e : A ≅ kernel q :=
    { hom := kernel.lift q s hsq
      inv := kernel.ι q ≫ p
      hom_inv_id := by simp [hsp]
      inv_hom_id := by
        rw [← cancel_mono (kernel.ι q)]
        simp [hιq] }
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e

variable {X : Scheme.{u}}

/-- A closed subset `S` of dimension `≤ 0` of a scheme with Noetherian underlying space is a
finite set of distinct closed points `x i`, each with an affine open `W i ∋ x i` with
`W i ∩ S = {x i}`. -/
private theorem exists_isAffineOpen_inter_eq_singleton [NoetherianSpace X] {S : Set X}
    (hS : IsClosed S) (hdim : topologicalKrullDim S ≤ 0) :
    ∃ (n : ℕ) (x : Fin n → X) (W : Fin n → X.Opens), Function.Injective x ∧ Set.range x = S ∧
      (∀ i, IsClosed ({x i} : Set X)) ∧ (∀ i, IsAffineOpen (W i)) ∧ (∀ i, x i ∈ W i) ∧
      ∀ i, (W i : Set X) ∩ S = {x i} := by
  classical
  have : QuasiSober S := hS.isClosedEmbedding_subtypeVal.quasiSober
  have : Finite S := Set.finite_univ_iff.mp
    (Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero hdim)
  have hcl : ∀ y ∈ S, IsClosed ({y} : Set X) := fun y hy => by
    simpa using hS.isClosedMap_subtype_val _
      (Stacks.Topology.Dimension.isClosed_singleton_of_topologicalKrullDim_le_zero hdim ⟨y, hy⟩)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  let x : Fin n → X := fun i => (e.symm i : X)
  have hxS : ∀ i, x i ∈ S := fun i => (e.symm i).2
  have hxinj : Function.Injective x := fun i j h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range x = S := by
    ext y
    refine ⟨fun ⟨i, hi⟩ => hi ▸ hxS i, fun hy => ⟨e ⟨y, hy⟩, by simp [x]⟩⟩
  have hV : ∀ i, IsOpen (⋂ j ∈ (Finset.univ.erase i), ({x j}ᶜ : Set X)) := fun i =>
    isOpen_biInter_finset fun j _ => (hcl _ (hxS j)).isOpen_compl
  have hxV : ∀ i, x i ∈ (⟨_, hV i⟩ : X.Opens) := fun i => by
    show x i ∈ ⋂ j ∈ (Finset.univ.erase i), ({x j}ᶜ : Set X)
    simp only [Set.mem_iInter, Finset.mem_erase, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun j ⟨hji, _⟩ h => hji (hxinj h).symm
  choose W hWaff hxW hWV using fun i => exists_isAffineOpen_mem_and_subset (hxV i)
  have hxWj : ∀ i j, x j ∈ W i → j = i := fun i j hj => by
    by_contra hne
    have h := hWV i hj
    simp only [Opens.coe_mk, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true,
      Set.mem_compl_iff, Set.mem_singleton_iff] at h
    exact h j hne rfl
  refine ⟨n, x, W, hxinj, hrange, fun i => hcl _ (hxS i), hWaff, hxW, fun i => ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun ⟨hy, hyS⟩ => ?_, ?_⟩
  · obtain ⟨j, rfl⟩ : y ∈ Set.range x := hrange ▸ hyS
    rw [hxWj i j hy]
  · rintro rfl
    exact ⟨hxW i, hxS i⟩

/-- The counit `j_! j^* 𝓕 ⟶ 𝓕` is an isomorphism on stalks (as modules) at points of `U`. -/
private theorem isIso_stalkFunctor_map_counit_app_of_mem (U : X.Opens)
    (𝓕 : SheafOfModules X.ringCatSheaf) (y : X) (hy : y ∈ U) :
    IsIso ((_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y).map
      ((jShriekAdjunction U X.ringCatSheaf).counit.app 𝓕)) := by
  set φ := (_root_.AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y).map
    ((jShriekAdjunction U X.ringCatSheaf).counit.app 𝓕)
  have : IsIso ((forget₂ _ AddCommGrpCat.{u}).map φ) :=
    isIso_stalk_counit_app_of_mem U X.ringCatSheaf 𝓕 y hy
  exact isIso_of_reflects_iso _ (forget₂ _ AddCommGrpCat.{u})

/-- The support of the extension by zero `j_!(j^*𝓕)` of the restriction of `𝓕` to an open `U` is
`U ∩ Supp(𝓕)`. -/
private theorem supp_jShriek_obj_jStar_obj (U : X.Opens) (𝓕 : X.Modules) :
    SheafOfModules.supp
        ((jShriek U X.ringCatSheaf).obj ((jStar U X.ringCatSheaf).obj 𝓕) : X.Modules) =
      (U : Set X) ∩ SheafOfModules.supp 𝓕 := by
  let O := X.ringCatSheaf
  let ι : X.Modules ⥤ SheafOfModules.{u} O := { obj := fun M => M, map := fun f => f }
  ext y
  refine (mem_supp_iff_not_isZero_stalkFunctor X _ y).trans ?_
  rw [Set.mem_inter_iff, mem_supp_iff_not_isZero_stalkFunctor]
  by_cases hy : y ∈ U
  · let ε : ((jShriek U O).obj ((jStar U O).obj 𝓕) : X.Modules) ⟶ 𝓕 :=
      (jShriekAdjunction U O).counit.app 𝓕
    let Φ : X.Modules ⥤ _ := ι ⋙ _root_.AlgebraicGeometry.SheafOfModules.stalkFunctor O y
    have : IsIso (Φ.map ε) := isIso_stalkFunctor_map_counit_app_of_mem U 𝓕 y hy
    exact ⟨fun h => ⟨hy, fun h0 => h (h0.of_iso (asIso (Φ.map ε)))⟩,
      fun h h0 => h.2 (h0.of_iso (asIso (Φ.map ε)).symm)⟩
  · exact ⟨fun h => (h ((_root_.AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff
      O y _).2 (isZero_stalk_jShriek U O _ y hy))).elim, fun h => (hy h.1).elim⟩

/-- **A coherent module with zero-dimensional support is a finite sum of coherent modules each
supported at one closed point inside an affine open.** Let `X` be a scheme with Noetherian
underlying space and `𝓕` a coherent `𝒪_X`-module with `dim Supp(𝓕) ≤ 0`. Then there are
`n` distinct closed points `x i` with `Supp(𝓕) = {x i}`, affine opens `U i ∋ x i` with
`U i ∩ Supp(𝓕) = {x i}`, and coherent modules `𝓕ᵢ i` with `Supp(𝓕ᵢ i) = {x i}` (so of
zero-dimensional support), such that `𝓕 ≅ ⨁ᵢ 𝓕ᵢ i`. The summand `𝓕ᵢ i` is `j_{i!} j_i^* 𝓕` for
the inclusion `j_i : U i → X`. -/
theorem exists_iso_biproduct_of_topologicalKrullDim_supp_le_zero [NoetherianSpace X]
    (𝓕 : X.Modules) (h𝓕 : 𝓕.IsCoherent)
    (hdim : topologicalKrullDim (SheafOfModules.supp 𝓕) ≤ 0) :
    ∃ (n : ℕ) (𝓕ᵢ : Fin n → X.Modules) (U : Fin n → X.affineOpens) (x : Fin n → X),
      Function.Injective x ∧ Set.range x = SheafOfModules.supp 𝓕 ∧
      (∀ i, IsClosed ({x i} : Set X)) ∧ (∀ i, x i ∈ (U i : X.Opens)) ∧
      (∀ i, ((U i : X.Opens) : Set X) ∩ SheafOfModules.supp 𝓕 = {x i}) ∧
      (∀ i, (𝓕ᵢ i).IsCoherent) ∧ (∀ i, SheafOfModules.supp (𝓕ᵢ i) = {x i}) ∧
      (∀ i, topologicalKrullDim (SheafOfModules.supp (𝓕ᵢ i)) = 0) ∧
      Nonempty (𝓕 ≅ ⨁ 𝓕ᵢ) := by
  classical
  obtain ⟨n, x, W, hxinj, hrange, hcl, hWaff, hxW, hWS⟩ := exists_isAffineOpen_inter_eq_singleton
    (Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent 𝓕 h𝓕) hdim
  have hxS : ∀ i, x i ∈ SheafOfModules.supp 𝓕 := fun i => hrange.subset (Set.mem_range_self i)
  let O := X.ringCatSheaf
  let 𝓕ᵢ : Fin n → X.Modules := fun i => (jShriek (W i) O).obj ((jStar (W i) O).obj 𝓕)
  let ε : ∀ i, 𝓕ᵢ i ⟶ 𝓕 := fun i => (jShriekAdjunction (W i) O).counit.app 𝓕
  let ι : X.Modules ⥤ SheafOfModules.{u} O := { obj := fun M => M, map := fun f => f }
  have : ι.Additive := ⟨rfl⟩
  let Φ : ∀ y : X, X.Modules ⥤ _ := fun y =>
    ι ⋙ _root_.AlgebraicGeometry.SheafOfModules.stalkFunctor O y
  have hsupp : ∀ i, SheafOfModules.supp (𝓕ᵢ i) = {x i} := fun i =>
    (supp_jShriek_obj_jStar_obj (W i) 𝓕).trans (hWS i)
  have hzero : ∀ i y, y ≠ x i → IsZero ((Φ y).obj (𝓕ᵢ i)) := fun i y hy =>
    not_imp_comm.1 (mem_supp_iff_not_isZero_stalkFunctor X (𝓕ᵢ i) y).2 (by rw [hsupp]; exact hy)
  have hσ : IsIso (biproduct.desc ε) := by
    suffices IsIso (ι.map (biproduct.desc ε)) from
      (show ι.FullyFaithful from { preimage := fun f => f }).isIso_of_isIso_map _
    rw [_root_.AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map]
    intro y
    show IsIso ((Φ y).map (biproduct.desc ε))
    by_cases hyS : y ∈ SheafOfModules.supp 𝓕
    · obtain ⟨i, rfl⟩ : y ∈ Set.range x := hrange ▸ hyS
      have : IsIso ((Φ (x i)).map (ε i)) :=
        isIso_stalkFunctor_map_counit_app_of_mem (W i) 𝓕 (x i) (hxW i)
      exact isIso_map_biproduct_desc_of_isZero (Φ (x i)) ε i
        fun j hj => hzero j (x i) fun h => hj (hxinj h).symm
    · exact (isZero_obj_biproduct_of_isZero (Φ y)
        fun j => hzero j y fun h => hyS (h ▸ hxS j)).isIso
        (not_imp_comm.1 (mem_supp_iff_not_isZero_stalkFunctor X 𝓕 y).2 hyS) _
  refine ⟨n, 𝓕ᵢ, fun i => ⟨W i, hWaff i⟩, x, hxinj, hrange, hcl, hxW, hWS, fun i => ?_, hsupp,
    fun i => ?_, ⟨(asIso (biproduct.desc ε)).symm⟩⟩
  · let p : 𝓕 ⟶ 𝓕ᵢ i := inv (biproduct.desc ε) ≫ biproduct.π 𝓕ᵢ i
    have hsp : ε i ≫ p = 𝟙 _ := by
      simp only [p]
      rw [← biproduct.ι_desc ε i, Category.assoc, IsIso.hom_inv_id_assoc, biproduct.ι_π_self]
    have hsp' : ι.map (ε i) ≫ ι.map p = 𝟙 (ι.obj (𝓕ᵢ i)) := by
      rw [← CategoryTheory.Functor.map_comp, hsp, CategoryTheory.Functor.map_id]
    exact isCoherent_of_comp_eq_id (ι.map (ε i)) (ι.map p) hsp' h𝓕
  · rw [hsupp i]
    exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _)
      (Order.krullDim_nonneg_iff.mpr
        ⟨⟨closure {⟨x i, rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩)

end Stacks.AlgebraicGeometry.DerivedVarieties.Orlov
