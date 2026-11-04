module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# Glueing subalgebras of a fixed algebra sheaf along a family of opens

Let `X` be a scheme and `A` a sheaf of commutative `𝒪_X`-algebras, i.e. an object of
`Stacks.RelativeSpec.AlgebraSheaf X = CategoryTheory.Under X.sheaf`. A *concrete subalgebra*
of `A`, `Stacks.RelativeSpec.AlgebraSheaf.Subalg A`, is a subring of `A(U)` for each open `U`
of `X`, containing the image of `Γ(X, U)`, stable under the restriction maps of `A`, and
*local*: a section of `A` lying in the subring locally lies in it. This file glues such
subalgebras along a family of opens of `X`.

Given opens `W i` of `X` and subalgebras `C i` of `A` which agree over every open contained in
two members of the family, `glue W C` is the subalgebra of `A` whose sections over an open `U`
are the sections of `A` over `U` whose restriction to `U ⊓ W i` lies in `C i` for every `i`;
over an open contained in `W j` it is `C j`. The family need not cover `X` or be finite, and `A`
need not be quasi-coherent.

## Main definitions

* `Subalg`: a concrete subalgebra of an algebra sheaf.
* `IsGlued`: the membership condition: the restriction to `U ⊓ W i` lies in `C i`, for all `i`.
* `localGlue`: that condition as a subring of `A(U)`.
* `glue`: the glued subalgebra of `A`.
* `Agree`: the agreement hypothesis on the pieces.

## Main results

* `glue_obj_of_le`: if the `C i` agree over every open contained in two members of the family,
  then over an open contained in `W j` the glued subalgebra is `C j`.
* `mem_glue_of_cover`: a section of `A` over `U` lies in the glued subalgebra as soon as `U` is
  covered by opens, each contained in some member of the family, over which the restriction of
  the section lies in the corresponding piece.
* `agree_pair`: for a two-member family the agreement hypothesis is a single equality over the
  overlap.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.RelativeSpec.AlgebraSheaf

variable {X : Scheme.{u}} {A : AlgebraSheaf X}

/-! ### Restriction of sections of an algebra sheaf -/

/-- Restriction of a section of an algebra sheaf along an inclusion of opens. -/
abbrev resElem (A : AlgebraSheaf X) {U V : X.Opens} (h : V ≤ U) (x : sections A U) :
    sections A V :=
  (A.right.obj.map (homOfLE h).op).hom x

/-- Restricting twice is restricting once. -/
theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : sections A U) :
    (A.right.obj.map (homOfLE h₂).op).hom ((A.right.obj.map (homOfLE h₁).op).hom x) =
      (A.right.obj.map (homOfLE (h₂.trans h₁)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← A.right.obj.map_comp]
  rfl

/-- Restricting along the identity does nothing. -/
theorem res_self {U : X.Opens} (x : sections A U) :
    (A.right.obj.map (homOfLE (le_refl U)).op).hom x = x := by
  rw [show (homOfLE (le_refl U)).op = 𝟙 _ from rfl, A.right.obj.map_id]
  rfl

/-- The image in `A` of a section of the structure sheaf restricts to the image of its
restriction. -/
theorem res_app {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (A.right.obj.map (homOfLE h).op).hom ((A.hom.hom.app (op U)).hom a) =
      (A.hom.hom.app (op V)).hom (X.presheaf.map (homOfLE h).op a) :=
  (congr($(presheaf_map_comp_app A h).hom a)).symm

/-! ### Concrete subalgebras of an algebra sheaf -/

/-- A concrete subalgebra of an algebra sheaf `A`: a subring of the sections of `A` over each open
of `X`, containing the image of the structure sheaf, stable under the restriction maps of `A`, and
local — a section lying in the subring near every point of its open lies in it. -/
structure Subalg (A : AlgebraSheaf X) where
  /-- The subring of sections over each open. -/
  obj : (U : X.Opens) → Subring (sections A U)
  /-- The subring contains the image of the structure sheaf, so it is a subalgebra. -/
  algebraMap_mem (U : X.Opens) (a : Γ(X, U)) : (A.hom.hom.app (op U)).hom a ∈ obj U
  /-- Membership is stable under the restriction maps of `A`. -/
  map_mem {U V : X.Opens} (h : V ≤ U) {x : sections A U} (hx : x ∈ obj U) :
    (A.right.obj.map (homOfLE h).op).hom x ∈ obj V
  /-- Membership is a local condition. -/
  isSheaf {U : X.Opens} (s : sections A U)
    (hs : ∀ x ∈ U, ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧
      (A.right.obj.map (homOfLE h).op).hom s ∈ obj V) : s ∈ obj U

namespace Subalg

/-- Two concrete subalgebras with the same subrings of sections are equal. -/
@[ext]
theorem ext {C D : Subalg A} (h : C.obj = D.obj) : C = D := by
  cases C
  cases D
  congr

/-- The largest subalgebra of `A` is `A` itself. -/
instance instTop : Top (Subalg A) where
  top :=
    { obj _ := ⊤
      algebraMap_mem _ _ := Subring.mem_top _
      map_mem _ _ _ := Subring.mem_top _
      isSheaf _ _ := Subring.mem_top _ }

/-- The sections of the largest subalgebra over `U` are all of `A(U)`. -/
@[simp] theorem top_obj (U : X.Opens) : (⊤ : Subalg A).obj U = ⊤ := rfl

end Subalg

/-! ### The glued subalgebra -/

section Glue

variable {ι : Type*} (W : ι → X.Opens) (C : ι → Subalg A)

/-- A section of `A` over `U` is *glued from* `C` along `W` if its restriction to `U ⊓ W i`
lies in `C i`, for every `i`. This is the membership condition of `glue W C`. -/
def IsGlued {U : X.Opens} (s : sections A U) : Prop :=
  ∀ i, (A.right.obj.map (homOfLE (inf_le_left : U ⊓ W i ≤ U)).op).hom s ∈ (C i).obj (U ⊓ W i)

/-- The sections of `A` over `U` glued from `C` along `W`, as a subring of `A(U)`. -/
def localGlue (U : X.Opens) : Subring (sections A U) where
  carrier := {s | IsGlued W C s}
  one_mem' i := by
    rw [map_one]
    exact Subring.one_mem _
  mul_mem' {a b} ha hb i := by
    rw [map_mul]
    exact Subring.mul_mem _ (ha i) (hb i)
  zero_mem' i := by
    rw [map_zero]
    exact Subring.zero_mem _
  add_mem' {a b} ha hb i := by
    rw [map_add]
    exact Subring.add_mem _ (ha i) (hb i)
  neg_mem' {a} ha i := by
    rw [map_neg]
    exact Subring.neg_mem _ (ha i)

/-- Membership in `localGlue W C U` is being glued from `C` along `W`. -/
theorem mem_localGlue_iff {U : X.Opens} (s : sections A U) :
    s ∈ localGlue W C U ↔ IsGlued W C s :=
  Iff.rfl

/-- The glued subalgebra of `A`: over an open `U` its sections are the sections of `A` whose
restriction to `U ⊓ W i` lies in `C i`, for every `i`. -/
def glue : Subalg A where
  obj U := localGlue W C U
  algebraMap_mem U a i := by
    rw [res_app]
    exact (C i).algebraMap_mem _ _
  map_mem {U V} h {x} hx i := by
    simpa only [res_res] using (C i).map_mem (inf_le_inf_right (W i) h) (hx i)
  isSheaf {U} s hs i := by
    refine (C i).isSheaf _ fun x hx ↦ ?_
    obtain ⟨V, hVU, hxV, hmem⟩ := hs x hx.1
    exact ⟨V ⊓ W i, inf_le_inf_right (W i) hVU, ⟨hxV, hx.2⟩, by simpa only [res_res] using hmem i⟩

/-- The sections of `glue W C` over `U` form the subring `localGlue W C U`. -/
theorem glue_obj (U : X.Opens) : (glue W C).obj U = localGlue W C U :=
  rfl

/-- Membership in the glued subalgebra is being glued from `C` along `W`. -/
theorem mem_glue_iff {U : X.Opens} (s : sections A U) :
    s ∈ (glue W C).obj U ↔ IsGlued W C s :=
  Iff.rfl

end Glue

/-! ### The glueing identity -/

section Agree

variable {ι : Type*} (W : ι → X.Opens) (C : ι → Subalg A)

/-- The agreement hypothesis: two pieces agree over every open contained in both of their
members of the family. -/
def Agree : Prop :=
  ∀ (i j : ι) (V : X.Opens), V ≤ W i → V ≤ W j → (C i).obj V = (C j).obj V

/-- If the pieces agree over every open contained in two members of the family, then over an open
contained in `W j` the glued subalgebra is `C j`. -/
theorem glue_obj_of_le (hagree : Agree W C) {U : X.Opens} {j : ι} (hUW : U ≤ W j) :
    (glue W C).obj U = (C j).obj U := by
  refine SetLike.ext fun s ↦ ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · simpa only [res_res, res_self] using (C j).map_mem (le_inf le_rfl hUW : U ≤ U ⊓ W j) (h j)
  · rw [hagree i j (U ⊓ W i) inf_le_right (inf_le_left.trans hUW)]
    exact (C j).map_mem (inf_le_left : U ⊓ W i ≤ U) h

/-- A section of `A` over `U` lies in the glued subalgebra as soon as `U` is covered by opens, each
contained in some member of the family, over which the restriction of the section lies in the
corresponding piece. -/
theorem mem_glue_of_cover (hagree : Agree W C) {U : X.Opens} (s : sections A U)
    (hcov : ∀ x ∈ U, ∃ (V : X.Opens) (k : ι) (hVU : V ≤ U), V ≤ W k ∧ x ∈ V ∧
      (A.right.obj.map (homOfLE hVU).op).hom s ∈ (C k).obj V) :
    s ∈ (glue W C).obj U := by
  refine (glue W C).isSheaf s fun x hx ↦ ?_
  obtain ⟨V, k, hVU, hVW, hxV, hmem⟩ := hcov x hx
  exact ⟨V, hVU, hxV, by rwa [glue_obj_of_le W C hagree hVW]⟩

end Agree

/-! ### The two-member family -/

section Pair

/-- For a two-member family the agreement hypothesis is a single equality over each open contained
in both members. -/
theorem agree_pair (W : Bool → X.Opens) (C : Bool → Subalg A)
    (h : ∀ V : X.Opens, V ≤ W false → V ≤ W true → (C false).obj V = (C true).obj V) :
    Agree W C := by
  rintro (_ | _) (_ | _) V hi hj
  exacts [rfl, h V hi hj, (h V hj hi).symm, rfl]

end Pair

end Stacks.RelativeSpec.AlgebraSheaf

end
