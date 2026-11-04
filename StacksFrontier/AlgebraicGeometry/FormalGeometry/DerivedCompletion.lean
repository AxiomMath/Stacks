module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Reflection onto a property of objects, from a completion functor

Let `(C, O)` be a ringed site and `I ⊂ O` a sheaf of ideals of finite type. Stacks, Tag 099F,
asserts that the inclusion of the derived-complete objects `D_comp(O) ⥤ D(O)` has a left
adjoint, and the source proves it in two movements. First one constructs a candidate
completion functor: there is a map `K ⟶ O` in `D(O)` whose restriction to any object of the
site over which `I` is finitely generated is the extended alternating Čech complex on a set of
generators (Tag 099E), and one puts `Φ = RSheafHom(K, -)` with `η : id ⟶ Φ` the map induced by
`K ⟶ O`. Then one checks two things: that `Φ E` is always derived complete, and that `η_E` is
an isomorphism whenever `E` is already derived complete.

This file isolates the second movement as a statement of pure category theory, for an
arbitrary property of objects `P` of an arbitrary category and an arbitrary endofunctor `Φ`
with a map `η : 𝟭 ⟶ Φ`. The reason to separate it is that the two checks of the source are
*not* sufficient on their own: what the argument needs in addition is that `Φ η_X` be an
isomorphism, equivalently — given the other two hypotheses — that `Φ η_X = η_{Φ X}`. Section
`CompletionUnitSharpness` below exhibits a two-object category in which `Φ E` always satisfies
`P`, `η_E` is an isomorphism whenever `E` satisfies `P`, and yet the inclusion of `P` has no
left adjoint at all; so the extra hypothesis cannot simply be dropped. For the completion
functor of Tag 099B it holds, because `Φ η_X` and `η_{Φ X}` are both the map
`RSheafHom(K, E) ⟶ RSheafHom(K ⊗ K, E)` induced by the multiplication of the idempotent
algebra `K`.

## Main results

* `Stacks.Algebraization.bijective_precomp_completionUnit`: precomposition with `η_X` is a
  bijection from the maps `Φ X ⟶ Z` to the maps `X ⟶ Z`, for every `Z` satisfying `P`. This is
  the universal property of `η_X : X ⟶ Φ X` as a reflection of `X` into `P`.
* `Stacks.Algebraization.isRightAdjoint_ι_of_completionFunctor`: consequently the inclusion of
  the full subcategory of objects satisfying `P` has a left adjoint.
* `Stacks.Algebraization.completionAdjunction`: the adjunction itself, with reflector
  `Stacks.Algebraization.completionReflector`, whose unit is `η`
  (`Stacks.Algebraization.completionAdjunction_unit_app`).
* `Stacks.Algebraization.leftAdjointCompιIsoOfCompletionFunctor`: any left adjoint of the
  inclusion, followed by the inclusion, is `Φ`, by an isomorphism carrying the unit to `η`
  (`Stacks.Algebraization.unit_comp_leftAdjointCompιIsoOfCompletionFunctor_hom`).
* `Stacks.Algebraization.isRightAdjoint_ι_of_idempotentCompletionFunctor`: the same conclusion
  from `Φ η_X = η_{Φ X}` in place of the invertibility of `Φ η_X`.
* `Stacks.Algebraization.CompletionUnitSharpness.exists_completionFunctor_and_not_isRightAdjoint_ι`:
  the hypothesis on `Φ η_X` is not redundant — a two-object category in which the other two
  hypotheses hold and the inclusion has no left adjoint.

## Implementation notes

Only the invertibility of `η_Z` for `Z` satisfying `P` is used for surjectivity of
precomposition; the invertibility of `Φ η_X` is used only for injectivity. No closure
properties of `P` are needed, in particular `P` is not assumed closed under isomorphisms, and
`Φ` is not assumed additive, exact or triangulated: the statement is about the bare
`(Φ, η)` data.

The left adjoint is produced by `CategoryTheory.Adjunction.adjunctionOfEquivLeft`, which builds
the functor out of the bijections on morphisms, so no naturality beyond that of `η` has to be
supplied.

## References

* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace Stacks.Algebraization

section Reflection

variable {D : Type u} [Category.{v} D] {P : ObjectProperty D} {Φ : D ⥤ D} (η : 𝟭 D ⟶ Φ)

/-- Naturality of a map `η : 𝟭 D ⟶ Φ`, with the identity functor evaluated away. -/
theorem comp_app_unit {X Y : D} (f : X ⟶ Y) :
    f ≫ η.app Y = η.app X ≫ Φ.map f := by
  simpa using η.naturality f

/-- **The universal property of a completion.** Let `Φ : D ⥤ D` and `η : 𝟭 D ⟶ Φ` be such that
`η_Z` is an isomorphism for every `Z` satisfying `P`, and such that `Φ η_X` is an isomorphism
for every `X`. Then precomposition with `η_X` is a bijection from the morphisms `Φ X ⟶ Z` to
the morphisms `X ⟶ Z`, for every `Z` satisfying `P`; that is, `η_X` exhibits `Φ X` as the
reflection of `X` into the objects satisfying `P`. -/
theorem bijective_precomp_completionUnit
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X)))
    (X : D) {Z : D} (hZ : P Z) :
    Function.Bijective (fun g : Φ.obj X ⟶ Z ↦ η.app X ≫ g) := by
  have := hη Z hZ
  refine ⟨fun g g' hgg' ↦ ?_, fun f ↦ ⟨Φ.map f ≫ inv (η.app Z), ?_⟩⟩
  · replace hgg' : η.app X ≫ g = η.app X ≫ g' := hgg'
    have := hΦη X
    have hmap : Φ.map g = Φ.map g' := by
      rw [← cancel_epi (Φ.map (η.app X)), ← Φ.map_comp, ← Φ.map_comp, hgg']
    rw [← cancel_mono (η.app Z), comp_app_unit η g, comp_app_unit η g', hmap]
  · show η.app X ≫ Φ.map f ≫ inv (η.app Z) = f
    have h : f ≫ η.app Z = η.app X ≫ Φ.map f := comp_app_unit η f
    rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The reflection bijection of `bijective_precomp_completionUnit`, as an equivalence between a
morphism type of the full subcategory of objects satisfying `P` and a morphism type of the
ambient category. -/
def completionHomEquiv (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X)))
    (X : D) (Z : P.FullSubcategory) :
    ((⟨Φ.obj X, hΦ X⟩ : P.FullSubcategory) ⟶ Z) ≃ (X ⟶ P.ι.obj Z) :=
  P.fullyFaithfulι.homEquiv.trans
    (Equiv.ofBijective _ (bijective_precomp_completionUnit η hη hΦη X Z.property))

/-- The reflection equivalence is precomposition of the inclusion of a morphism of the full
subcategory with the unit. -/
theorem completionHomEquiv_apply (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X)))
    (X : D) (Z : P.FullSubcategory) (f : (⟨Φ.obj X, hΦ X⟩ : P.FullSubcategory) ⟶ Z) :
    completionHomEquiv η hΦ hη hΦη X Z f = η.app X ≫ P.ι.map f :=
  rfl

/-- The reflection equivalence is natural in the target. -/
theorem completionHomEquiv_naturality (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X)))
    (X : D) (Z Z' : P.FullSubcategory) (g : Z ⟶ Z')
    (h : (⟨Φ.obj X, hΦ X⟩ : P.FullSubcategory) ⟶ Z) :
    completionHomEquiv η hΦ hη hΦη X Z' (h ≫ g) =
      completionHomEquiv η hΦ hη hΦη X Z h ≫ P.ι.map g := by
  show η.app X ≫ P.ι.map (h ≫ g) = (η.app X ≫ P.ι.map h) ≫ P.ι.map g
  simp

/-- **The reflector of a completion functor**: the left adjoint of the inclusion of the objects
satisfying `P`, built out of the reflection bijections of `completionHomEquiv`. On objects it is
`X ↦ Φ X`. -/
def completionReflector (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X))) :
    D ⥤ P.FullSubcategory :=
  Adjunction.leftAdjointOfEquiv (completionHomEquiv η hΦ hη hΦη)
    (completionHomEquiv_naturality η hΦ hη hΦη)

/-- **The reflection adjunction of a completion functor**, `completionReflector ⊣ ι`. -/
def completionAdjunction (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X))) :
    completionReflector η hΦ hη hΦη ⊣ P.ι :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The unit of the reflection adjunction of a completion functor is `η`. -/
theorem completionAdjunction_unit_app (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X))) (X : D) :
    (completionAdjunction η hΦ hη hΦη).unit.app X = η.app X := by
  show η.app X ≫ P.ι.map (𝟙 (⟨Φ.obj X, hΦ X⟩ : P.FullSubcategory)) = η.app X
  simp

/-- **The reflector of a completion functor, followed by the inclusion, is `Φ`.** The two agree
on objects on the nose; on morphisms, `Φ f` is the unique map out of `Φ X` whose composite with
`η_X` is `f ≫ η_Y`, by naturality of `η`. -/
def completionReflectorCompιIso (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X))) :
    completionReflector η hΦ hη hΦη ⋙ P.ι ≅ Φ :=
  NatIso.ofComponents (fun X ↦ Iso.refl (Φ.obj X)) fun {X Y} f ↦ by
    have key : η.app X ≫ P.ι.map ((completionReflector η hΦ hη hΦη).map f) = f ≫ η.app Y := by
      change completionHomEquiv η hΦ hη hΦη X _ ((completionHomEquiv η hΦ hη hΦη X _).symm
        (f ≫ completionHomEquiv η hΦ hη hΦη Y _ (𝟙 _))) = _
      rw [Equiv.apply_symm_apply, completionHomEquiv_apply]
      simp
    have h : P.ι.map ((completionReflector η hΦ hη hΦη).map f) = Φ.map f :=
      (bijective_precomp_completionUnit η hη hΦη X (hΦ Y)).1 (key.trans (comp_app_unit η f))
    exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm)

/-- **The inclusion of a completion-stable property of objects is a right adjoint.** If
`Φ : D ⥤ D` and `η : 𝟭 D ⟶ Φ` are such that `Φ X` satisfies `P` for every `X`, that `η_Z` is an
isomorphism for every `Z` satisfying `P`, and that `Φ η_X` is an isomorphism for every `X`,
then the inclusion of the full subcategory of objects satisfying `P` has a left adjoint. This
is the final step of the proof of Tag 099F, and of Tag 099B before it. -/
theorem isRightAdjoint_ι_of_completionFunctor (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X))) :
    (P.ι).IsRightAdjoint :=
  (completionAdjunction η hΦ hη hΦη).isRightAdjoint

/-- **Any left adjoint of the inclusion, followed by the inclusion, is the completion functor**,
by a natural isomorphism carrying the unit of the adjunction to `η`. -/
def leftAdjointCompιIsoOfCompletionFunctor [P.ι.IsRightAdjoint] (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X))) :
    P.ι.leftAdjoint ⋙ P.ι ≅ Φ :=
  Functor.isoWhiskerRight
      ((Adjunction.ofIsRightAdjoint P.ι).leftAdjointUniq (completionAdjunction η hΦ hη hΦη))
      P.ι ≪≫
    completionReflectorCompιIso η hΦ hη hΦη

/-- The isomorphism `leftAdjointCompιIsoOfCompletionFunctor` carries the unit of the
adjunction to `η`. -/
theorem unit_app_comp_leftAdjointCompιIsoOfCompletionFunctor_hom_app [P.ι.IsRightAdjoint]
    (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X))) (X : D) :
    (Adjunction.ofIsRightAdjoint P.ι).unit.app X ≫
        (leftAdjointCompιIsoOfCompletionFunctor η hΦ hη hΦη).hom.app X = η.app X := by
  show (Adjunction.ofIsRightAdjoint P.ι).unit.app X ≫
      (P.ι.map (((Adjunction.ofIsRightAdjoint P.ι).leftAdjointUniq
        (completionAdjunction η hΦ hη hΦη)).hom.app X) ≫ 𝟙 _) = η.app X
  rw [Category.comp_id, Adjunction.unit_leftAdjointUniq_hom_app,
    completionAdjunction_unit_app]

/-- The isomorphism `leftAdjointCompιIsoOfCompletionFunctor` carries the unit of the
adjunction to `η`, as natural transformations. -/
theorem unit_comp_leftAdjointCompιIsoOfCompletionFunctor_hom [P.ι.IsRightAdjoint]
    (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z)) (hΦη : ∀ X : D, IsIso (Φ.map (η.app X))) :
    (Adjunction.ofIsRightAdjoint P.ι).unit ≫
        (leftAdjointCompιIsoOfCompletionFunctor η hΦ hη hΦη).hom = η :=
  NatTrans.ext (funext fun X ↦
    unit_app_comp_leftAdjointCompιIsoOfCompletionFunctor_hom_app η hΦ hη hΦη X)

/-- The inclusion of a completion-stable property of objects is a right adjoint, with the
invertibility of `Φ η_X` replaced by the equality `Φ η_X = η_{Φ X}` which holds for the
completion functors built as derived internal Hom out of an idempotent algebra. -/
theorem isRightAdjoint_ι_of_idempotentCompletionFunctor (hΦ : ∀ X : D, P (Φ.obj X))
    (hη : ∀ Z : D, P Z → IsIso (η.app Z))
    (hcomm : ∀ X : D, Φ.map (η.app X) = η.app (Φ.obj X)) :
    (P.ι).IsRightAdjoint :=
  isRightAdjoint_ι_of_completionFunctor η hΦ hη
    fun X ↦ by
      rw [hcomm X]
      exact hη _ (hΦ X)

end Reflection

/-! ### The hypothesis on `Φ η` is not redundant

The two conditions that the proof of Tag 099F verifies — that `Φ E` always lies in the
subcategory, and that `η_E` is invertible for `E` in the subcategory — do not by themselves
give a left adjoint to the inclusion. This section exhibits a category with two objects in
which they hold and the inclusion is not a right adjoint; the failure is exactly that
`Φ η` is not invertible. -/

namespace CompletionUnitSharpness

/-- The two objects of the counterexample. -/
inductive Obj : Type
  /-- The object whose reflection into the subcategory does not exist. -/
  | src : Obj
  /-- The unique object of the subcategory. -/
  | tgt : Obj

/-- The morphisms of the counterexample: one morphism `src ⟶ src`, one morphism `src ⟶ tgt`,
none from `tgt` to `src`, and the two-element monoid `{1, m}` with `m² = m` as the
endomorphisms of `tgt`, encoded as `Bool` with `true` the identity and `false` the
non-invertible idempotent `m`. -/
def Hom : Obj → Obj → Type
  | .src, .src => PUnit
  | .src, .tgt => PUnit
  | .tgt, .src => PEmpty
  | .tgt, .tgt => Bool

/-- The identity morphisms. -/
def Hom.id : (X : Obj) → Hom X X
  | .src => PUnit.unit
  | .tgt => true

/-- Composition of morphisms; on the endomorphisms of `tgt` it is conjunction of booleans,
whose unit is `true` and whose other element `false` is idempotent. -/
def Hom.comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  | .src, .src, .src, _, _ => PUnit.unit
  | .src, .src, .tgt, _, _ => PUnit.unit
  | .src, .tgt, .src, _, g => g.elim
  | .src, .tgt, .tgt, _, _ => PUnit.unit
  | .tgt, .src, _, f, _ => f.elim
  | .tgt, .tgt, .src, _, g => g.elim
  | .tgt, .tgt, .tgt, f, g => f && g

/-- The counterexample category. -/
instance : Category Obj where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    rintro ⟨⟩ ⟨⟩ f <;>
      first
        | exact f.elim
        | exact Subsingleton.elim (α := PUnit) _ _
        | exact Bool.true_and f
  comp_id := by
    rintro ⟨⟩ ⟨⟩ f <;>
      first
        | exact f.elim
        | exact Subsingleton.elim (α := PUnit) _ _
        | exact Bool.and_true f
  assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ f g h <;>
      first
        | exact f.elim
        | exact g.elim
        | exact h.elim
        | exact Subsingleton.elim (α := PUnit) _ _
        | exact Bool.and_assoc f g h

/-- The non-invertible idempotent endomorphism of `tgt`. -/
def m : Hom Obj.tgt Obj.tgt := false

/-- The idempotent `m` is not the identity of `tgt`. -/
theorem id_ne_m : (𝟙 Obj.tgt : Obj.tgt ⟶ Obj.tgt) ≠ m := by
  intro h
  have h' : (true : Bool) = false := h
  simp at h'

/-- There is exactly one morphism `src ⟶ tgt`. -/
theorem hom_src_tgt_eq (a b : Obj.src ⟶ Obj.tgt) : a = b :=
  Subsingleton.elim (α := PUnit) a b

/-- The candidate completion functor: it sends everything to `tgt`, is the identity on the
endomorphisms of `tgt`, and sends the unique morphism `src ⟶ tgt` to the idempotent `m`. -/
def completion : Obj ⥤ Obj where
  obj _ := Obj.tgt
  map := by
    rintro ⟨⟩ ⟨⟩ f
    exacts [true, false, f.elim, f]
  map_id := by rintro ⟨⟩ <;> rfl
  map_comp := by rintro ⟨⟩ ⟨⟩ ⟨⟩ f g <;> first | exact f.elim | exact g.elim | rfl

/-- The candidate unit: the unique morphism `src ⟶ tgt`, and the identity of `tgt`. -/
def completionUnit : 𝟭 Obj ⟶ completion where
  app := by rintro ⟨⟩; exacts [PUnit.unit, true]
  naturality := by
    rintro ⟨⟩ ⟨⟩ f
    exacts [rfl, rfl, f.elim, (Bool.and_true f).trans (Bool.true_and f).symm]

/-- The property of objects singling out `tgt`. -/
def P : ObjectProperty Obj := fun Z ↦ Z = Obj.tgt

/-- Every value of the candidate completion functor lies in the subcategory. -/
theorem prop_completion_obj (X : Obj) : P (completion.obj X) := rfl

/-- The candidate unit is an isomorphism at every object of the subcategory. -/
theorem isIso_completionUnit_app (Z : Obj) (hZ : P Z) : IsIso (completionUnit.app Z) := by
  obtain rfl : Z = Obj.tgt := hZ
  exact ⟨⟨𝟙 _, rfl, rfl⟩⟩

/-- The missing hypothesis really fails here: `completion` applied to the unit at `src` is the
non-invertible idempotent `m`. -/
theorem not_isIso_map_completionUnit_app :
    ¬ IsIso (completion.map (completionUnit.app Obj.src)) := by
  intro h
  obtain ⟨b, hb, -⟩ := h.out
  have hb' : (false : Bool) = true := hb
  simp at hb'

/-- **The hypothesis `IsIso (Φ η_X)` of `isRightAdjoint_ι_of_completionFunctor` cannot be
dropped.** In this two-object category there is an endofunctor `Φ` and a map `η : 𝟭 ⟶ Φ` such
that `Φ X` satisfies `P` for every `X` and `η_Z` is an isomorphism for every `Z` satisfying
`P` — the two conditions checked in the proof of Tag 099F — and yet the inclusion of the full
subcategory of objects satisfying `P` has no left adjoint: the object `src` has no reflection,
because there is a single morphism `src ⟶ tgt` while `tgt` has two endomorphisms. -/
theorem exists_completionFunctor_and_not_isRightAdjoint_ι :
    (∀ X : Obj, P (completion.obj X)) ∧
      (∀ Z : Obj, P Z → IsIso (completionUnit.app Z)) ∧ ¬ (P.ι).IsRightAdjoint := by
  refine ⟨prop_completion_obj, isIso_completionUnit_app, fun hadj ↦ ?_⟩
  obtain ⟨L, ⟨adj⟩⟩ := hadj.exists_leftAdjoint
  let T : P.FullSubcategory := ⟨Obj.tgt, rfl⟩
  have h2 : 𝟙 T = ObjectProperty.homMk (P := P) m := by
    rw [← cancel_epi (P.isoMk (eqToIso ((L.obj Obj.src).property : _ = Obj.tgt)) :
      L.obj Obj.src ≅ T).hom]
    exact (adj.homEquiv Obj.src T).injective (hom_src_tgt_eq _ _)
  exact id_ne_m (by simpa using congrArg (fun f : T ⟶ T ↦ P.ι.map f) h2)

end CompletionUnitSharpness

end Stacks.Algebraization

end
