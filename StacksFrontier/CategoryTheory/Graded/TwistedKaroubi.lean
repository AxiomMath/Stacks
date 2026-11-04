module

public import StacksFrontier.CategoryTheory.Graded.Category

/-!
# The twisted Karoubi envelope of a graded category

For a category `C` graded over a ring `R`, a *twisted idempotent* is a triple `(X, p, m)` of an
object `X`, a degree-zero idempotent `p` of `X` and an integer twist `m`. A morphism
`(X, p, m) ⟶ (Y, q, n)` is a homogeneous morphism `X ⟶ Y` of degree `n - m` lying in
`p ≫ (-) ≫ q`, that is, fixed by both idempotents. These form an `R`-linear category.

Applied to the graded category of correspondences between smooth projective schemes over a field
this is the category `M_k` of Chow motives of Stacks Section 0FG9: the triple `(X, p, m)` is a
motive, and the morphisms are `q ∘ Corr^{n-m}(X, Y) ∘ p`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi`: the triples `(X, p, m)`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.homSubmodule`: the morphisms
  `(X, p, m) ⟶ (Y, q, n)`, as the submodule of the morphisms `X ⟶ Y` of degree `n - m` fixed
  by `p` and `q`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.functorOfGrade`: the functor
  `X ↦ (G X, 𝟙, 0)`, `f ↦ G f` induced by a functor `G` into `C` landing in degree zero.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.mem_homSubmodule_iff`: the morphisms
  `(X, p, m) ⟶ (Y, q, n)` are exactly the composites `p ≫ c ≫ q` with `c` homogeneous of degree
  `n - m`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.instLinear`: the twisted Karoubi envelope is
  `R`-linear.

## Implementation notes

The morphisms are a subtype of the ambient morphism module, so composition, addition and scalar
multiplication are those of `C` and every law is inherited by `Subtype.ext`. Only one degree of
the ambient morphisms is used between two given triples, the one fixed by the twists, so no
dependent casts between homogeneous pieces arise.

## References

* [Stacks Project, Section 0FG9](https://stacks.math.columbia.edu/tag/0FG9)
* [Stacks Project, Tag 0FGA](https://stacks.math.columbia.edu/tag/0FGA)
* [Stacks Project, Tag 09L2](https://stacks.math.columbia.edu/tag/09L2)
-/

@[expose] public section

namespace CategoryTheory.GradedCategory

universe w v u u'

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C] [GradedCategory R C]

/-- A twisted idempotent of a graded category: a triple `(X, p, m)` of an object `X`, an
idempotent endomorphism `p` of `X` homogeneous of degree zero, and an integer twist `m`. -/
structure TwistedKaroubi where
  /-- The underlying object. -/
  X : C
  /-- The idempotent. -/
  p : X ⟶ X
  /-- The idempotent is homogeneous of degree zero. -/
  p_mem : p ∈ grade (R := R) X X 0
  /-- The idempotent is idempotent. -/
  idem : p ≫ p = p
  /-- The twist. -/
  twist : ℤ

namespace TwistedKaroubi

variable {R C}

/-- A composite `f ≫ c ≫ g` with `f` and `g` of degree zero has the degree of `c`. -/
theorem comp_comp_mem {X Y Z W : C} {d : ℤ} {f : X ⟶ Y} {c : Y ⟶ Z} {g : Z ⟶ W}
    (hf : f ∈ grade (R := R) X Y 0) (hc : c ∈ grade (R := R) Y Z d)
    (hg : g ∈ grade (R := R) Z W 0) : f ≫ c ≫ g ∈ grade (R := R) X W d := by
  have h := comp_mem (R := R) (comp_mem (R := R) hg hc) hf
  rwa [zero_add, add_zero] at h

/-- The morphisms `(X, p, m) ⟶ (Y, q, n)`: the morphisms `X ⟶ Y` homogeneous of degree `n - m`
that are fixed by `p` on the source side and by `q` on the target side. -/
def homSubmodule (M N : TwistedKaroubi R C) : Submodule R (M.X ⟶ N.X) where
  carrier := {a | a ∈ grade (R := R) M.X N.X (N.twist - M.twist) ∧ M.p ≫ a = a ∧ a ≫ N.p = a}
  zero_mem' := ⟨Submodule.zero_mem _, by simp, by simp⟩
  add_mem' ha hb := ⟨Submodule.add_mem _ ha.1 hb.1,
    by rw [Preadditive.comp_add, ha.2.1, hb.2.1], by rw [Preadditive.add_comp, ha.2.2, hb.2.2]⟩
  smul_mem' r a ha := ⟨Submodule.smul_mem _ r ha.1,
    by rw [Linear.comp_smul, ha.2.1], by rw [Linear.smul_comp, ha.2.2]⟩

/-- A morphism `a : X ⟶ Y` lies in the morphism submodule of `(X, p, m)` and `(Y, q, n)` if and
only if it is homogeneous of degree `n - m`, `p ≫ a = a` and `a ≫ q = a`. -/
theorem mem_homSubmodule {M N : TwistedKaroubi R C} {a : M.X ⟶ N.X} :
    a ∈ homSubmodule M N ↔
      a ∈ grade (R := R) M.X N.X (N.twist - M.twist) ∧ M.p ≫ a = a ∧ a ≫ N.p = a :=
  Iff.rfl

/-- The morphisms `(X, p, m) ⟶ (Y, q, n)` are exactly the composites `p ≫ c ≫ q` with `c` a
morphism `X ⟶ Y` homogeneous of degree `n - m`: in the notation of correspondences,
`Hom((X, p, m), (Y, q, n)) = q ∘ Corr^{n-m}(X, Y) ∘ p`. -/
theorem mem_homSubmodule_iff {M N : TwistedKaroubi R C} {a : M.X ⟶ N.X} :
    a ∈ homSubmodule M N ↔
      ∃ c ∈ grade (R := R) M.X N.X (N.twist - M.twist), a = M.p ≫ c ≫ N.p := by
  refine ⟨fun h => ⟨a, h.1, by rw [h.2.2, h.2.1]⟩, ?_⟩
  rintro ⟨c, hc, rfl⟩
  refine ⟨comp_comp_mem M.p_mem hc N.p_mem, ?_, ?_⟩
  · rw [← Category.assoc, M.idem]
  · rw [Category.assoc, Category.assoc, N.idem]

/-- The idempotent `p` lies in the morphism submodule of `(X, p, m)` with itself. -/
theorem p_mem_homSubmodule (M : TwistedKaroubi R C) : M.p ∈ homSubmodule M M := by
  refine ⟨?_, M.idem, M.idem⟩
  rw [sub_self]
  exact M.p_mem

/-- The morphism submodules are closed under composition. -/
theorem comp_mem_homSubmodule {M N P : TwistedKaroubi R C} {a : M.X ⟶ N.X} {b : N.X ⟶ P.X}
    (ha : a ∈ homSubmodule M N) (hb : b ∈ homSubmodule N P) : a ≫ b ∈ homSubmodule M P := by
  refine ⟨?_, by rw [← Category.assoc, ha.2.1], by rw [Category.assoc, hb.2.2]⟩
  have h := comp_mem (R := R) hb.1 ha.1
  have e : P.twist - N.twist + (N.twist - M.twist) = P.twist - M.twist := by omega
  rwa [e] at h

/-- The twisted Karoubi envelope is a category: composition is the composition of `C`, and the
identity of `(X, p, m)` is `p`. -/
instance instCategory : Category.{v} (TwistedKaroubi R C) where
  Hom M N := homSubmodule M N
  id M := ⟨M.p, p_mem_homSubmodule M⟩
  comp f g := ⟨f.1 ≫ g.1, comp_mem_homSubmodule f.2 g.2⟩
  id_comp f := Subtype.ext f.2.2.1
  comp_id f := Subtype.ext f.2.2.2
  assoc _ _ _ := Subtype.ext (Category.assoc _ _ _)

/-- The underlying morphism of `C` of a morphism of the twisted Karoubi envelope. -/
abbrev Hom.val {M N : TwistedKaroubi R C} (f : M ⟶ N) : M.X ⟶ N.X :=
  Subtype.val (p := fun a => a ∈ homSubmodule M N) f

/-- Two morphisms of the twisted Karoubi envelope are equal if their underlying morphisms of `C`
are equal. -/
@[ext]
theorem hom_ext {M N : TwistedKaroubi R C} {f g : M ⟶ N} (h : f.val = g.val) : f = g :=
  Subtype.ext h

/-- The underlying morphism of a morphism `M ⟶ N` lies in the morphism submodule of `M` and
`N`. -/
theorem val_mem {M N : TwistedKaroubi R C} (f : M ⟶ N) : f.val ∈ homSubmodule M N :=
  f.2

/-- A morphism of `C` lying in the morphism submodule, as a morphism of the twisted Karoubi
envelope. -/
abbrev Hom.mk {M N : TwistedKaroubi R C} (a : M.X ⟶ N.X) (ha : a ∈ homSubmodule M N) : M ⟶ N :=
  ⟨a, ha⟩

/-- The underlying morphism of `Hom.mk a ha` is `a`. -/
@[simp]
theorem Hom.mk_val {M N : TwistedKaroubi R C} (a : M.X ⟶ N.X) (ha : a ∈ homSubmodule M N) :
    (Hom.mk a ha).val = a :=
  rfl

/-- The underlying morphism of the identity of `(X, p, m)` is `p`. -/
@[simp]
theorem id_val (M : TwistedKaroubi R C) : (𝟙 M : M ⟶ M).val = M.p :=
  rfl

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
@[simp]
theorem comp_val {M N P : TwistedKaroubi R C} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).val = f.val ≫ g.val :=
  rfl

/-- The twisted Karoubi envelope is preadditive, with the addition of `C`. -/
instance instPreadditive : Preadditive (TwistedKaroubi R C) where
  homGroup M N := inferInstanceAs (AddCommGroup (homSubmodule M N))
  add_comp _ _ _ _ _ _ := Subtype.ext (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := Subtype.ext (Preadditive.comp_add _ _ _ _ _ _)

/-- The underlying morphism of a sum is the sum of the underlying morphisms. -/
@[simp]
theorem add_val {M N : TwistedKaroubi R C} (f g : M ⟶ N) : (f + g).val = f.val + g.val :=
  rfl

/-- The underlying morphism of the zero morphism is zero. -/
@[simp]
theorem zero_val (M N : TwistedKaroubi R C) : (0 : M ⟶ N).val = 0 :=
  rfl

/-- The underlying morphism of a negation is the negation of the underlying morphism. -/
@[simp]
theorem neg_val {M N : TwistedKaroubi R C} (f : M ⟶ N) : (-f).val = -f.val :=
  rfl

/-- The underlying morphism of a difference is the difference of the underlying morphisms. -/
@[simp]
theorem sub_val {M N : TwistedKaroubi R C} (f g : M ⟶ N) : (f - g).val = f.val - g.val :=
  rfl

/-- The twisted Karoubi envelope is `R`-linear, with the scalar multiplication of `C`. -/
instance instLinear : Linear R (TwistedKaroubi R C) where
  homModule M N := inferInstanceAs (Module R (homSubmodule M N))
  smul_comp _ _ _ _ _ _ := Subtype.ext (Linear.smul_comp _ _ _ _ _ _)
  comp_smul _ _ _ _ _ _ := Subtype.ext (Linear.comp_smul _ _ _ _ _ _)

/-- The underlying morphism of `r • f` is `r` times the underlying morphism of `f`. -/
@[simp]
theorem smul_val {M N : TwistedKaroubi R C} (r : R) (f : M ⟶ N) : (r • f).val = r • f.val :=
  rfl

/-- The morphisms `(X, p, m) ⟶ (Y, q, n)` of the twisted Karoubi envelope are, as an `R`-module,
the submodule `p ≫ (-) ≫ q` of the degree-`(n - m)` morphisms `X ⟶ Y`. -/
def homLinearEquiv (M N : TwistedKaroubi R C) : (M ⟶ N) ≃ₗ[R] homSubmodule M N :=
  LinearEquiv.refl R _

/-! ### The functor induced by a functor landing in degree zero -/

section Functor

variable {D : Type u'} [Category D] (G : D ⥤ C) (hG : ∀ {X Y : D} (f : X ⟶ Y),
  G.map f ∈ grade (R := R) (G.obj X) (G.obj Y) 0)

/-- The triple `(X, 𝟙, 0)` of an object of `C`. -/
@[simps]
def ofObj (X : C) : TwistedKaroubi R C where
  X := X
  p := 𝟙 X
  p_mem := id_mem X
  idem := Category.comp_id _
  twist := 0

/-- The morphisms `(X, 𝟙, 0) ⟶ (Y, 𝟙, 0)` are exactly the morphisms `X ⟶ Y` homogeneous of
degree zero. -/
theorem mem_homSubmodule_ofObj {X Y : C} {a : X ⟶ Y} :
    a ∈ homSubmodule (ofObj (R := R) X) (ofObj (R := R) Y) ↔ a ∈ grade (R := R) X Y 0 := by
  show a ∈ grade (R := R) X Y (0 - 0) ∧ 𝟙 X ≫ a = a ∧ a ≫ 𝟙 Y = a ↔ _
  rw [sub_self, Category.id_comp, Category.comp_id]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl, rfl⟩⟩

/-- A functor `G : D ⥤ C` whose maps are homogeneous of degree zero induces the functor
`X ↦ (G X, 𝟙, 0)`, `f ↦ G f` into the twisted Karoubi envelope. -/
@[simps]
def functorOfGrade : D ⥤ TwistedKaroubi R C where
  obj X := ofObj (G.obj X)
  map f := Hom.mk (G.map f) (mem_homSubmodule_ofObj.2 (hG f))
  map_id X := hom_ext (G.map_id X)
  map_comp f g := hom_ext (G.map_comp f g)

end Functor

end TwistedKaroubi

end CategoryTheory.GradedCategory
