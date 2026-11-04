module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Gluing a submodule of a module on a scheme across a two-element open cover

A submodule of an `𝒪_X`-module `M` in the sense of `SheafOfModules.Submodule` is a family of
submodules of the sections of `M`, stable under restriction, whose membership condition is local.
Such families are closed under sectionwise intersection, which is what makes them a convenient
vehicle for gluing: if `X = W ∪ V` and a submodule is prescribed on `W` and on `V`, the two
prescriptions are combined by an intersection rather than by a construction.

The device is the *`V`-saturation* `Stacks.AlgebraicGeometry.Subsheaf.sat V N`, whose sections over
an open `T` are the sections of `M` whose restriction to `T ⊓ V` is a section of `N`. It agrees
with `N` on opens contained in `V` and imposes no condition away from `V`, so for `C ≤ B` agreeing
with `B` over `W ⊓ V` the submodule `inter B (sat V C)` is `B` on opens contained in `W` and `C` on
opens contained in `V`.

## Main definitions

* `Stacks.AlgebraicGeometry.Subsheaf.res` is restriction of sections of an `𝒪_X`-module along an
  inclusion of opens.
* `Stacks.AlgebraicGeometry.Subsheaf.satObj` and `Stacks.AlgebraicGeometry.Subsheaf.sat` are the
  `V`-saturation of a submodule, sectionwise and as a submodule.
* `Stacks.AlgebraicGeometry.Subsheaf.inter` is the sectionwise intersection of two submodules.

## Main results

* `Stacks.AlgebraicGeometry.Subsheaf.mem_of_local`: membership in a submodule is a local
  condition, in the form of an open cover of the domain of definition of a section.
* `Stacks.AlgebraicGeometry.Subsheaf.sat_obj_of_le`: saturation changes nothing on opens contained
  in `V`.
* `Stacks.AlgebraicGeometry.Subsheaf.inter_sat_obj_of_le_left` and
  `Stacks.AlgebraicGeometry.Subsheaf.inter_sat_obj_of_le_right`: **the gluing lemma.** For `C ≤ B`
  which agree on the opens contained in `W ⊓ V`, the submodule `inter B (sat V C)` equals `B` on
  opens contained in `W` and equals `C` on opens contained in `V`.

## Implementation notes

The structure field `SheafOfModules.Submodule.map` is phrased with `PresheafOfModules.restrictₛₗ`
and the sections of `M` over an open `T` are displayed as `M.val.obj (op T)` rather than as
`Γ(M, T)`; the two are definitionally equal but not syntactically so, which defeats `rewrite`
inside the structure fields. Every rewriting step is therefore factored into a standalone lemma
whose binders carry the `Γ(M, T)` form, and the structure fields only apply those lemmas.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Subsheaf

variable {X : Scheme.{u}} {M : X.Modules}

/-- Restriction of a section of an `𝒪_X`-module along an inclusion of opens. -/
noncomputable def res (M : X.Modules) {T T' : X.Opens} (h : T' ≤ T) (s : Γ(M, T)) : Γ(M, T') :=
  M.presheaf.map (homOfLE h).op s

/-- Restriction is transitive. -/
lemma res_res {T T' T'' : X.Opens} (h : T' ≤ T) (h' : T'' ≤ T') (s : Γ(M, T)) :
    res M h' (res M h s) = res M (h'.trans h) s := by
  rw [res, res, res, ← comp_apply, ← Functor.map_comp]; rfl

/-- Restriction along the identity inclusion is the identity. -/
lemma res_self {T : X.Opens} (h : T ≤ T) (s : Γ(M, T)) : res M h s = s := by
  rw [res, show (homOfLE h).op = 𝟙 (op T) from rfl, CategoryTheory.Functor.map_id]; rfl

/-- Membership in a submodule is local: a section all of whose restrictions to the members of an
open cover of its domain of definition lie in the submodule lies in the submodule. -/
lemma mem_of_local (N : SheafOfModules.Submodule M) {T : X.Opens} (s : Γ(M, T))
    (h : ∀ x ∈ T, ∃ (V : X.Opens) (hV : V ≤ T), x ∈ V ∧ res M hV s ∈ N.obj (op V)) :
    s ∈ N.obj (op T) := by
  refine N.isSheaf s ?_
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨V, hV, hxV, hmem⟩ := h x hx
  exact ⟨V, homOfLE hV, hmem, hxV⟩

/-- A submodule is stable under restriction of sections. -/
lemma mem_of_le (N : SheafOfModules.Submodule M) {T T' : X.Opens} (h : T' ≤ T) {s : Γ(M, T)}
    (hs : s ∈ N.obj (op T)) : res M h s ∈ N.obj (op T') :=
  N.map_mem (homOfLE h).op hs

/-- Restricting twice into a submodule: the transitive form of `mem_of_le`. -/
lemma mem_of_res_mem (N : SheafOfModules.Submodule M) {T T' T'' : X.Opens} (h : T' ≤ T)
    (h' : T'' ≤ T') (h'' : T'' ≤ T) {s : Γ(M, T)} (hs : res M h s ∈ N.obj (op T')) :
    res M h'' s ∈ N.obj (op T'') := by
  have h3 := mem_of_le N h' hs
  rw [res_res] at h3
  exact h3

/-- The sections over `T` whose restriction to `T ⊓ V` is a section of `N`. -/
noncomputable def satObj (V : X.Opens) (N : SheafOfModules.Submodule M) (T : X.Opens) :
    Submodule Γ(X, T) Γ(M, T) :=
  (N.obj (op (T ⊓ V))).comap (M.val.restrictₛₗ (homOfLE (inf_le_left : T ⊓ V ≤ T)).op)

/-- Membership in `satObj`, spelled with `res`. -/
lemma mem_satObj {V : X.Opens} {N : SheafOfModules.Submodule M} {T : X.Opens} {s : Γ(M, T)} :
    s ∈ satObj V N T ↔ res M (inf_le_left : T ⊓ V ≤ T) s ∈ N.obj (op (T ⊓ V)) := Iff.rfl

/-- `satObj` is stable under restriction of sections. -/
lemma mem_satObj_res (V : X.Opens) (N : SheafOfModules.Submodule M) {T T' : X.Opens} (h : T' ≤ T)
    {s : Γ(M, T)} (hs : s ∈ satObj V N T) : res M h s ∈ satObj V N T' := by
  rw [mem_satObj, res_res]
  exact mem_of_res_mem N inf_le_left (inf_le_inf_right V h) _ (mem_satObj.mp hs)

/-- Membership in `satObj` is itself a local condition. -/
lemma mem_satObj_of_local (V : X.Opens) (N : SheafOfModules.Submodule M) {T : X.Opens}
    (s : Γ(M, T))
    (h : ∀ x ∈ T, ∃ (P : X.Opens) (hP : P ≤ T), x ∈ P ∧ res M hP s ∈ satObj V N P) :
    s ∈ satObj V N T := by
  refine mem_satObj.mpr (mem_of_local N _ fun x hx => ?_)
  obtain ⟨P, hP, hxP, hmem⟩ := h x hx.1
  refine ⟨P ⊓ V, inf_le_inf_right _ hP, ⟨hxP, hx.2⟩, ?_⟩
  simpa only [res_res] using mem_satObj.mp hmem

/-- The **`V`-saturation** of a submodule `N` of `M`: its sections over an open `T` are the
sections of `M` over `T` whose restriction to `T ⊓ V` is a section of `N`. It agrees with `N` on
the opens contained in `V` and imposes no condition on an open disjoint from `V`. -/
noncomputable def sat (V : X.Opens) (N : SheafOfModules.Submodule M) :
    SheafOfModules.Submodule M where
  obj T := satObj V N T.unop
  map {T T'} f s hs := mem_satObj_res V N (leOfHom f.unop) hs
  isSheaf := by
    intro T s hs
    rw [Opens.mem_grothendieckTopology] at hs
    refine mem_satObj_of_local V N s fun x hx => ?_
    obtain ⟨P, f, hmem, hxP⟩ := hs x hx
    exact ⟨P, leOfHom f, hxP, hmem⟩

/-- Membership in the `V`-saturation. -/
lemma mem_sat_iff (V : X.Opens) (N : SheafOfModules.Submodule M) {T : X.Opens} (s : Γ(M, T)) :
    s ∈ (sat V N).obj (op T) ↔ res M (inf_le_left : T ⊓ V ≤ T) s ∈ N.obj (op (T ⊓ V)) := Iff.rfl

/-- A section of `N` over an open contained in `V` is recovered from its restriction to the
intersection with `V`. -/
lemma mem_of_res_inf_mem (V : X.Opens) (N : SheafOfModules.Submodule M) {T : X.Opens} (hT : T ≤ V)
    (s : Γ(M, T)) (hs : res M (inf_le_left : T ⊓ V ≤ T) s ∈ N.obj (op (T ⊓ V))) :
    s ∈ N.obj (op T) := by
  rw [← res_self le_rfl s]
  exact mem_of_res_mem N inf_le_left (le_inf le_rfl hT) le_rfl hs

/-- On the opens contained in `V`, the `V`-saturation agrees with the submodule. -/
lemma sat_obj_of_le (V : X.Opens) (N : SheafOfModules.Submodule M) {T : X.Opens} (hT : T ≤ V) :
    (sat V N).obj (op T) = N.obj (op T) :=
  le_antisymm (fun s hs => mem_of_res_inf_mem V N hT s hs)
    (fun s hs => (show res M (inf_le_left : T ⊓ V ≤ T) s ∈ N.obj (op (T ⊓ V)) from
      mem_of_le N _ hs))

/-- A submodule is contained in each of its saturations. -/
lemma le_sat (V : X.Opens) (N : SheafOfModules.Submodule M) (T : X.Opens) :
    N.obj (op T) ≤ (sat V N).obj (op T) :=
  fun s hs => (mem_sat_iff V N s).mpr (mem_of_le N _ hs)

/-- Saturation is monotone. -/
lemma sat_mono (V : X.Opens) {N N' : SheafOfModules.Submodule M}
    (h : ∀ T : X.Opens, N.obj (op T) ≤ N'.obj (op T)) (T : X.Opens) :
    (sat V N).obj (op T) ≤ (sat V N').obj (op T) :=
  fun _ hs => (mem_sat_iff V N' _).mpr (h _ ((mem_sat_iff V N _).mp hs))

/-- The sectionwise intersection of two submodules of `M`. The infimum of the complete lattice
`SheafOfModules.Submodule M` is computed sectionwise and would do, but its instances are stated
for a sheaf of rings on a site and are not found for the sheaf of rings of a scheme. -/
noncomputable def inter (B C : SheafOfModules.Submodule M) : SheafOfModules.Submodule M where
  obj T := B.obj T ⊓ C.obj T
  map f := le_inf (inf_le_left.trans (B.map f)) (inf_le_right.trans (C.map f))
  isSheaf := by
    intro T s hs
    rw [Opens.mem_grothendieckTopology] at hs
    refine ⟨mem_of_local B s fun x hx => ?_, mem_of_local C s fun x hx => ?_⟩
    · obtain ⟨P, f, hmem, hxP⟩ := hs x hx
      exact ⟨P, leOfHom f, hxP, hmem.1⟩
    · obtain ⟨P, f, hmem, hxP⟩ := hs x hx
      exact ⟨P, leOfHom f, hxP, hmem.2⟩

/-- The sections of a sectionwise intersection. -/
lemma inter_obj (B C : SheafOfModules.Submodule M) (T : X.Opens) :
    (inter B C).obj (op T) = B.obj (op T) ⊓ C.obj (op T) := rfl

section Gluing

variable (W V : X.Opens) (B C : SheafOfModules.Submodule M)

/-- **The gluing lemma, first half.** If `B` is contained in `C` on the opens contained in
`W ⊓ V`, then `inter B (sat V C)` agrees with `B` on the opens contained in `W`. -/
theorem inter_sat_obj_of_le_left
    (hagree : ∀ P : X.Opens, P ≤ W ⊓ V → B.obj (op P) ≤ C.obj (op P))
    {T : X.Opens} (hT : T ≤ W) : (inter B (sat V C)).obj (op T) = B.obj (op T) := by
  refine le_antisymm (fun s hs => hs.1) (fun s hs => ⟨hs, ?_⟩)
  refine (mem_sat_iff V C s).mpr ?_
  exact hagree (T ⊓ V) (le_inf (inf_le_left.trans hT) inf_le_right) (mem_of_le B _ hs)

/-- **The gluing lemma, second half.** If `C` is contained in `B` sectionwise, then
`inter B (sat V C)` agrees with `C` on the opens contained in `V`. -/
theorem inter_sat_obj_of_le_right (hCB : ∀ P : X.Opens, C.obj (op P) ≤ B.obj (op P))
    {T : X.Opens} (hT : T ≤ V) : (inter B (sat V C)).obj (op T) = C.obj (op T) := by
  have h : (sat V C).obj (op T) = C.obj (op T) := sat_obj_of_le V C hT
  exact le_antisymm (fun s hs => h.le hs.2) (fun s hs => ⟨hCB _ hs, h.ge hs⟩)

/-- A sectionwise intersection agrees with its first factor on any family of opens on which the
first factor is contained in the second. -/
theorem inter_obj_of_le_left (hagree : ∀ P : X.Opens, P ≤ W → B.obj (op P) ≤ C.obj (op P))
    {T : X.Opens} (hT : T ≤ W) : (inter B C).obj (op T) = B.obj (op T) :=
  le_antisymm (fun _ hs => hs.1) (fun _ hs => ⟨hs, hagree T hT hs⟩)

/-- A sectionwise intersection agrees with its second factor on any family of opens on which the
second factor is contained in the first. -/
theorem inter_obj_of_le_right (hagree : ∀ P : X.Opens, P ≤ V → C.obj (op P) ≤ B.obj (op P))
    {T : X.Opens} (hT : T ≤ V) : (inter B C).obj (op T) = C.obj (op T) :=
  le_antisymm (fun _ hs => hs.2) (fun _ hs => ⟨hagree T hT hs, hs⟩)

end Gluing

end Stacks.AlgebraicGeometry.Subsheaf
