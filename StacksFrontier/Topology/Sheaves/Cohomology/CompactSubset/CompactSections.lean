module

public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.Topology.Compact.ShrinkingCover

/-!
# Sections of a sheaf along a quasi-compact subset

Let `X` be a topological space, let `F` be a sheaf on `X` with values in a concrete category, and
let `K ⊆ X` be quasi-compact. This file proves the two statements which say that the sections of
`F` along `K` are the sections of `F` on the open neighbourhoods of `K`:

* sections of `F` which agree *near* every point of a subset agree on an open neighbourhood of
  that subset — no compactness needed;
* local sections on an open cover of `K` which agree near every point of `K` can be *shrunk* to a
  cover whose members they agree on outright, hence glued to a single section on an open
  neighbourhood of `K`.

Equivalently, writing `i : K → X` for the inclusion, the canonical map

`colim_{U ⊇ K open} F(U) ⟶ Γ(K, i^{-1}F)`

is injective by the first statement and surjective by the second.

## Main results

* `Stacks.Topology.exists_opens_restrict_eq_of_locallyEqOn`: two sections agreeing near every
  point of a subset agree on an open neighbourhood of it.
* `Stacks.Topology.exists_opens_glue_of_isCompact_of_pairwiseSeparated`: local sections on an
  open cover of a quasi-compact `K` whose distinct points are separated by disjoint opens of `X`,
  which agree near every point of `K`, glue after shrinking the cover to a section on an open
  neighbourhood of `K`; `Stacks.Topology.exists_opens_glue_of_isCompact` is its `T2Space X`
  corollary.
* `Stacks.Topology.exists_opens_restrict_eq_of_germ_eqOn` and
  `Stacks.Topology.exists_opens_germ_eq_of_isCompact`: the same two statements phrased with germs
  and stalks.

## References

* [Stacks Project, Tag 0CY5](https://stacks.math.columbia.edu/tag/0CY5)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite

namespace Stacks.Topology

universe v u w

section StalkFree

variable {C : Type u} [Category.{w} C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {X : TopCat.{v}}

/-- Restricting a section twice along inclusions of opens is restricting it once. -/
theorem map_op_comp_apply (F : TopCat.Presheaf C X) {U V W : Opens X}
    (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W) (s : ToType (F.obj (op W))) :
    F.map f.op (F.map g.op s) = F.map h.op s := by
  rw [← ConcreteCategory.comp_apply, ← F.map_comp, ← op_comp, Subsingleton.elim (f ≫ g) h]

variable [HasLimitsOfSize.{v, v} C] [(forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{v, v} (forget C)]

/-- Two sections of a sheaf which agree on some open neighbourhood of each point of a subset `T`
agree on a single open neighbourhood of `T`. -/
theorem exists_opens_restrict_eq_of_locallyEqOn
    (F : TopCat.Sheaf C X) {U V : Opens X} (s : ToType (F.presheaf.obj (op U)))
    (t : ToType (F.presheaf.obj (op V))) {T : Set X}
    (h : ∀ x ∈ T, ∃ (N : Opens X) (_ : x ∈ N) (iNU : N ⟶ U) (iNV : N ⟶ V),
      F.presheaf.map iNU.op s = F.presheaf.map iNV.op t) :
    ∃ (A : Opens X) (_ : T ⊆ A.1) (iAU : A ⟶ U) (iAV : A ⟶ V),
      F.presheaf.map iAU.op s = F.presheaf.map iAV.op t := by
  choose N hxN iNU iNV heq using fun x : T => h x x.2
  have hAU : (⨆ x : T, N x) ≤ U := iSup_le fun x => (iNU x).le
  have hAV : (⨆ x : T, N x) ≤ V := iSup_le fun x => (iNV x).le
  refine ⟨⨆ x : T, N x, fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxN ⟨y, hy⟩⟩,
    homOfLE hAU, homOfLE hAV, ?_⟩
  refine F.eq_of_locally_eq' N _ (fun x => Opens.leSupr N x) le_rfl _ _ fun x => ?_
  rw [map_op_comp_apply F.presheaf (Opens.leSupr N x) (homOfLE hAU) (iNU x),
    map_op_comp_apply F.presheaf (Opens.leSupr N x) (homOfLE hAV) (iNV x)]
  exact heq x

/-- **Gluing sections along a quasi-compact subset, separation assumed only along the subset.**
Let `K` be a quasi-compact subset of `X` any two of whose distinct points are separated by
disjoint opens of `X`, covered by opens `W i` carrying sections `sec i` of a sheaf `F` which
agree on some open neighbourhood of every point of `K ⊓ W i ⊓ W j`. Then the cover can be shrunk
to a cover `V i ⊆ W i` of `K` on which the `sec i` glue: there is a section of `F` on the open
neighbourhood `⨆ i, V i` of `K` restricting to each `sec i`. -/
theorem exists_opens_glue_of_isCompact_of_pairwiseSeparated
    (F : TopCat.Sheaf C X) {K : Set X} (hK : IsCompact K)
    (hsep : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    {ι : Type*} (W : ι → Opens X) (sec : ∀ i, ToType (F.presheaf.obj (op (W i))))
    (hcover : K ⊆ ⋃ i, (W i : Set X))
    (hloc : ∀ i j : ι, ∀ x ∈ K ∩ (W i : Set X) ∩ (W j : Set X),
      ∃ (N : Opens X) (_ : x ∈ N) (iNi : N ⟶ W i) (iNj : N ⟶ W j),
        F.presheaf.map iNi.op (sec i) = F.presheaf.map iNj.op (sec j)) :
    ∃ (V : ι → Opens X) (iVW : ∀ i, V i ⟶ W i), K ⊆ (⨆ i, V i : Opens X).1 ∧
      ∃ s : ToType (F.presheaf.obj (op (⨆ i, V i))),
        ∀ i, F.presheaf.map (Opens.leSupr V i).op s = F.presheaf.map (iVW i).op (sec i) := by
  classical
  choose A hTA iAi iAj heqA using fun i j : ι =>
    exists_opens_restrict_eq_of_locallyEqOn F (sec i) (sec j)
      (T := K ∩ (W i : Set X) ∩ (W j : Set X)) (hloc i j)
  obtain ⟨V, hVopen, hVcover, hVW, -, hVinter⟩ :=
    TopologicalSpace.exists_isOpen_refinement_of_isCompact_of_pairwiseSeparated K hK hsep
      1 ι (fun i => (W i : Set X)) (fun i => (W i).2)
      (fun τ => (A (τ 0) (τ 1) : Set X)) (fun τ => (A (τ 0) (τ 1)).2) hcover
      (fun τ => by
        have hswap : (⋂ k : Fin 2, (W (τ k) : Set X)) =
            (W (τ 0) : Set X) ∩ (W (τ 1) : Set X) := by
          ext y
          simp only [Set.mem_iInter, Set.mem_inter_iff, Fin.forall_fin_two]
        rw [hswap]
        refine Set.Subset.antisymm
          (fun y hy => ⟨⟨(iAi _ _).le hy.1, (iAj _ _).le hy.1⟩, hy.2⟩)
          (fun y hy => ⟨hTA _ _ ⟨⟨hy.2, hy.1.1⟩, hy.1.2⟩, hy.2⟩))
  have hVA : ∀ i j : ι, (V i ∩ V j : Set X) ⊆ (A i j : Set X) := by
    intro i j y hy
    have hmem : y ∈ ⋂ k : Fin 2, V ((fun k : Fin 2 => if k = 0 then i else j) k) := by
      refine Set.mem_iInter.2 fun k => ?_
      fin_cases k
      · simpa using hy.1
      · simpa using hy.2
    simpa using hVinter (fun k : Fin 2 => if k = 0 then i else j) hmem
  let Us : ι → Opens X := fun i => ⟨V i, hVopen i⟩
  have hUsW : ∀ i : ι, Us i ≤ W i := fun i => hVW i
  let sf : ∀ i : ι, ToType (F.presheaf.obj (op (Us i))) := fun i =>
    F.presheaf.map (homOfLE (hUsW i)).op (sec i)
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf Us sf := by
    intro i j
    have hc : Us i ⊓ Us j ≤ A i j := fun y hy => hVA i j ⟨hy.1, hy.2⟩
    have key : ∀ (k : ι) (a : Us i ⊓ Us j ⟶ Us k) (g : A i j ⟶ W k),
        F.presheaf.map a.op (sf k) = F.presheaf.map (homOfLE hc).op (F.presheaf.map g.op (sec k)) :=
      fun k a g => (map_op_comp_apply F.presheaf a _ (homOfLE hc ≫ g) _).trans
        (map_op_comp_apply F.presheaf _ _ _ _).symm
    rw [key i _ (iAi i j), key j _ (iAj i j), heqA i j]
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing Us sf hcompat
  exact ⟨Us, fun i => homOfLE (hUsW i),
    fun x hx => Opens.mem_iSup.2 (Set.mem_iUnion.1 (hVcover hx)), s, hs⟩

/-- **Gluing sections along a quasi-compact subset of a Hausdorff space**: the case of
`exists_opens_glue_of_isCompact_of_pairwiseSeparated` in which the separation of the points of
`K` comes from Hausdorffness of the ambient space. -/
theorem exists_opens_glue_of_isCompact [T2Space X]
    (F : TopCat.Sheaf C X) {K : Set X} (hK : IsCompact K)
    {ι : Type*} (W : ι → Opens X) (sec : ∀ i, ToType (F.presheaf.obj (op (W i))))
    (hcover : K ⊆ ⋃ i, (W i : Set X))
    (hloc : ∀ i j : ι, ∀ x ∈ K ∩ (W i : Set X) ∩ (W j : Set X),
      ∃ (N : Opens X) (_ : x ∈ N) (iNi : N ⟶ W i) (iNj : N ⟶ W j),
        F.presheaf.map iNi.op (sec i) = F.presheaf.map iNj.op (sec j)) :
    ∃ (V : ι → Opens X) (iVW : ∀ i, V i ⟶ W i), K ⊆ (⨆ i, V i : Opens X).1 ∧
      ∃ s : ToType (F.presheaf.obj (op (⨆ i, V i))),
        ∀ i, F.presheaf.map (Opens.leSupr V i).op s = F.presheaf.map (iVW i).op (sec i) :=
  exists_opens_glue_of_isCompact_of_pairwiseSeparated F hK
    (fun _ _ _ _ hxy => t2_separation hxy) W sec hcover hloc

end StalkFree

section Germs

variable {C : Type u} [Category.{v} C] {FC : C → C → Type w} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable {X : TopCat.{v}}
variable [HasColimits C] [PreservesFilteredColimits (forget C)]
variable [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]

/-- Two sections of a sheaf whose germs agree at every point of a subset `T` already agree on an
open neighbourhood of `T`. This is the germ form of
`Stacks.Topology.exists_opens_restrict_eq_of_locallyEqOn`. -/
theorem exists_opens_restrict_eq_of_germ_eqOn
    (F : TopCat.Sheaf C X) {U V : Opens X} (s : ToType (F.presheaf.obj (op U)))
    (t : ToType (F.presheaf.obj (op V))) {T : Set X} (hTU : T ⊆ U.1) (hTV : T ⊆ V.1)
    (h : ∀ x, ∀ hx : x ∈ T, F.presheaf.germ U x (hTU hx) s = F.presheaf.germ V x (hTV hx) t) :
    ∃ (A : Opens X) (_ : T ⊆ A.1) (iAU : A ⟶ U) (iAV : A ⟶ V),
      F.presheaf.map iAU.op s = F.presheaf.map iAV.op t :=
  exists_opens_restrict_eq_of_locallyEqOn F s t fun x hx =>
    F.presheaf.germ_eq x (hTU hx) (hTV hx) s t (h x hx)

/-- **Sections along a quasi-compact subset, in germs.** Let `K` be a quasi-compact subset of `X`
any two of whose distinct points are separated by disjoint opens of `X`, and let `σ` assign to
each point of `X` an element of the stalk of the sheaf `F`. If `σ` is locally sectional along `K`
— every point of `K` has an open neighbourhood `W` carrying a section of `F` whose germ at each
point of `K ⊓ W` is the prescribed one — then `σ` is the germ family of a single section of `F`
on an open neighbourhood of `K`. -/
theorem exists_opens_germ_eq_of_isCompact_of_pairwiseSeparated
    (F : TopCat.Sheaf C X) {K : Set X} (hK : IsCompact K)
    (hsep : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (σ : ∀ x : X, ToType (F.presheaf.stalk x))
    (hσ : ∀ x ∈ K, ∃ (W : Opens X) (_ : x ∈ W) (s : ToType (F.presheaf.obj (op W))),
      ∀ y, ∀ _ : y ∈ K, ∀ hyW : y ∈ W, σ y = F.presheaf.germ W y hyW s) :
    ∃ (U : Opens X) (hKU : K ⊆ U.1) (s : ToType (F.presheaf.obj (op U))),
      ∀ x, ∀ hx : x ∈ K, σ x = F.presheaf.germ U x (hKU hx) s := by
  classical
  choose W hxW sec hagree using fun x : K => hσ x x.2
  obtain ⟨V, iVW, hKV, s, hs⟩ :=
    exists_opens_glue_of_isCompact_of_pairwiseSeparated F hK hsep W sec
      (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
      (fun i j x hx => F.presheaf.germ_eq x hx.1.2 hx.2 (sec i) (sec j)
        ((hagree i x hx.1.1 hx.1.2).symm.trans (hagree j x hx.1.1 hx.2)))
  refine ⟨⨆ i, V i, hKV, s, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hKV hx)
  rw [← F.presheaf.germ_res_apply (Opens.leSupr V i) x hi s, hs i,
    F.presheaf.germ_res_apply (iVW i) x hi (sec i)]
  exact hagree i x hx ((iVW i).le hi)

/-- **Sections along a quasi-compact subset of a Hausdorff space, in germs**: the case of
`exists_opens_germ_eq_of_isCompact_of_pairwiseSeparated` in which the separation of the points of
`K` comes from Hausdorffness of the ambient space. -/
theorem exists_opens_germ_eq_of_isCompact [T2Space X]
    (F : TopCat.Sheaf C X) {K : Set X} (hK : IsCompact K)
    (σ : ∀ x : X, ToType (F.presheaf.stalk x))
    (hσ : ∀ x ∈ K, ∃ (W : Opens X) (_ : x ∈ W) (s : ToType (F.presheaf.obj (op W))),
      ∀ y, ∀ _ : y ∈ K, ∀ hyW : y ∈ W, σ y = F.presheaf.germ W y hyW s) :
    ∃ (U : Opens X) (hKU : K ⊆ U.1) (s : ToType (F.presheaf.obj (op U))),
      ∀ x, ∀ hx : x ∈ K, σ x = F.presheaf.germ U x (hKU hx) s :=
  exists_opens_germ_eq_of_isCompact_of_pairwiseSeparated F hK
    (fun _ _ _ _ hxy => t2_separation hxy) σ hσ

end Germs

end Stacks.Topology

end
