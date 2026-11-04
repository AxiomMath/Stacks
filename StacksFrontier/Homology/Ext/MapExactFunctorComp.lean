module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Ext along a composite of exact functors, and along isomorphic exact functors

For exact functors `F : C ⥤ D` and `G : D ⥤ E` between abelian categories, carrying an
`Ext`-class along `F ⋙ G` is carrying it along `F` and then along `G`; and for an isomorphism
`α : F ≅ F'` of exact functors, carrying a class along `F'` is carrying it along `F` and then
conjugating with the components of `α`.

Both are proved by dimension shifting in the second variable, as
`Stacks.Homology.ext_mapExactFunctor_of_isoId` is: in degree zero they are the functoriality and
the naturality of `α`, and the step from degree `n` to degree `n + 1` writes a class as a
composite with the class of an injective presentation, which an exact functor carries to the class
of the image presentation (`CategoryTheory.Abelian.Ext.mapExactFunctor_extClass`).

## Main definitions

* `Stacks.Homology.extConj` — a class conjugated by morphisms on the source and the target.

## Main results

* `Stacks.Homology.ext_mapExactFunctor_comp_functor` — `Ext` along `F ⋙ G` is `Ext` along `F`
  followed by `Ext` along `G`.
* `Stacks.Homology.ext_mapExactFunctor_of_iso` — `Ext` along `F'` is the conjugate by `α : F ≅ F'`
  of `Ext` along `F`.
* `Stacks.Homology.ext_mapExactFunctor_id` — `Ext` along the identity functor is the identity.
* `Stacks.Homology.extConj_extConj`, `Stacks.Homology.extConj_mapExactFunctor` — conjugation
  composes, and commutes with an exact functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' w'' v v' v'' u u' u''

namespace Stacks.Homology

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {E : Type u''} [Category.{v''} E] [Abelian E]

/-- Dimension shifting: a statement about classes in degree `n + 1` follows from the statement for
the classes `y.comp hS.extClass` over all short exact sequences `hS`. -/
private theorem ext_succ_induction [HasExt.{w} C] [EnoughInjectives C] {A : C} {n : ℕ}
    {motive : ∀ B : C, Ext.{w} A B (n + 1) → Prop} (B : C) (x : Ext.{w} A B (n + 1))
    (h : ∀ (S : ShortComplex C) (hS : S.ShortExact) (y : Ext.{w} A S.X₃ n),
      motive S.X₁ (y.comp hS.extClass rfl)) : motive B x := by
  let I : InjectivePresentation B := Classical.arbitrary _
  let S := ShortComplex.mk _ _ (cokernel.condition I.f)
  have hinj : Injective S.X₂ := I.injective
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl
  exact h S hS y

/-- **`Ext` along a composite of exact functors is the composite of the two maps on `Ext`.** -/
theorem ext_mapExactFunctor_comp_functor [HasExt.{w} C] [HasExt.{w'} D] [HasExt.{w''} E]
    [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (A : C)
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)] :
    ∀ (n : ℕ) (B : C) (x : Ext.{w} A B n),
      (x.mapExactFunctor (F ⋙ G) : Ext.{w''} ((F ⋙ G).obj A) ((F ⋙ G).obj B) n) =
        ((x.mapExactFunctor F : Ext.{w'} (F.obj A) (F.obj B) n).mapExactFunctor G :
          Ext.{w''} (G.obj (F.obj A)) (G.obj (F.obj B)) n) := by
  intro n
  induction n with
  | zero =>
    intro B x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (X := A) (Y := B)).2 x
    rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]
    rfl
  | succ n ih =>
    intro B x
    induction B, x using ext_succ_induction with | _ S hS y =>
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
      ih S.X₃ y, Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass,
      Ext.mapExactFunctor_extClass]

/-- **`Ext` along the identity functor is the identity.** -/
theorem ext_mapExactFunctor_id [HasExt.{w} C] [EnoughInjectives C] (A : C) :
    ∀ (n : ℕ) (B : C) (x : Ext.{w} A B n),
      (x.mapExactFunctor (𝟭 C) : Ext.{w} A B n) = x := by
  intro n
  induction n with
  | zero =>
    intro B x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (X := A) (Y := B)).2 x
    rw [Ext.mapExactFunctor_mk₀]
    rfl
  | succ n ih =>
    intro B x
    induction B, x using ext_succ_induction with | _ S hS y =>
    rw [Ext.mapExactFunctor_comp, ih S.X₃ y, Ext.mapExactFunctor_extClass]

/-- **`Ext` along isomorphic exact functors.** For an isomorphism `α : F ≅ F'` of exact functors,
the image of a class along `F'` is its image along `F`, precomposed with the component of `α⁻¹`
at the source and postcomposed with the component of `α` at the target. -/
theorem ext_mapExactFunctor_of_iso [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
    (F F' : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (α : F ≅ F') (A : C) :
    ∀ (n : ℕ) (B : C) (x : Ext.{w} A B n),
      (x.mapExactFunctor F' : Ext.{w'} (F'.obj A) (F'.obj B) n) =
        (Ext.mk₀ (α.inv.app A)).comp
          ((x.mapExactFunctor F : Ext.{w'} (F.obj A) (F.obj B) n).comp (Ext.mk₀ (α.hom.app B))
            (add_zero n)) (zero_add n) := by
  intro n
  induction n with
  | zero =>
    intro B x
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (X := A) (Y := B)).2 x
    rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
    congr 1
    rw [α.hom.naturality f]
    simp
  | succ n ih =>
    intro B x
    induction B, x using ext_succ_induction with | _ S hS y =>
    let φ : S.map F ⟶ S.map F' :=
      { τ₁ := α.hom.app S.X₁
        τ₂ := α.hom.app S.X₂
        τ₃ := α.hom.app S.X₃
        comm₁₂ := (α.hom.naturality S.f).symm
        comm₂₃ := (α.hom.naturality S.g).symm }
    have hnat := ShortComplex.ShortExact.extClass_naturality (hS.map_of_exact F)
      (hS.map_of_exact F') φ
    calc
      (y.comp hS.extClass rfl).mapExactFunctor F'
          = (y.mapExactFunctor F').comp (hS.map_of_exact F').extClass rfl := by
            rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
      _ = ((Ext.mk₀ (α.inv.app A)).comp
              ((y.mapExactFunctor F).comp (Ext.mk₀ (α.hom.app S.X₃)) (add_zero n))
              (zero_add n)).comp (hS.map_of_exact F').extClass rfl := by
            rw [ih S.X₃ y]
      _ = (Ext.mk₀ (α.inv.app A)).comp
              ((y.mapExactFunctor F).comp
                ((Ext.mk₀ (α.hom.app S.X₃)).comp (hS.map_of_exact F').extClass (zero_add 1))
                rfl) (zero_add (n + 1)) := by
            rw [Ext.comp_assoc _ _ _ (zero_add n) rfl (by lia),
              Ext.comp_assoc _ _ _ (add_zero n) (zero_add 1) (by lia)]
      _ = (Ext.mk₀ (α.inv.app A)).comp
              (((y.comp hS.extClass rfl).mapExactFunctor F).comp
                (Ext.mk₀ (α.hom.app S.X₁)) (add_zero (n + 1))) (zero_add (n + 1)) := by
            rw [← hnat, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
              Ext.comp_assoc_of_third_deg_zero]

section Conj

variable [HasExt.{w} C]

/-- **An `Ext`-class conjugated by morphisms**: `x : Ext X Y n` precomposed with `a : X' ⟶ X` and
postcomposed with `b : Y ⟶ Y'`. -/
def extConj {X' X Y Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y') {n : ℕ} (x : Ext.{w} X Y n) :
    Ext.{w} X' Y' n :=
  (Ext.mk₀ a).comp (x.comp (Ext.mk₀ b) (add_zero n)) (zero_add n)

/-- Conjugating by identities is the identity. -/
theorem extConj_id {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) : extConj (𝟙 X) (𝟙 Y) x = x := by
  simp [extConj]

/-- Two successive conjugations are the conjugation by the composites. -/
theorem extConj_extConj {X'' X' X Y Y' Y'' : C} (a : X'' ⟶ X') (b : Y' ⟶ Y'') (a' : X' ⟶ X)
    (b' : Y ⟶ Y') {n : ℕ} (x : Ext.{w} X Y n) :
    extConj a b (extConj a' b' x) = extConj (a ≫ a') (b' ≫ b) x := by
  simp only [extConj, Ext.mk₀_comp_mk₀_assoc, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

/-- Conjugation is additive. -/
theorem extConj_add {X' X Y Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y') {n : ℕ} (x y : Ext.{w} X Y n) :
    extConj a b (x + y) = extConj a b x + extConj a b y := by
  simp only [extConj, Ext.add_comp, Ext.comp_add]

/-- Conjugating by `eqToHom` of reflexivity proofs is the identity. -/
theorem extConj_eqToHom {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) (h : X = X) (h' : Y = Y) :
    extConj (eqToHom h) (eqToHom h') x = x := by
  simp [extConj]

/-- Conjugating by the identity on the source is postcomposition. -/
theorem extConj_id_left {X Y Y' : C} (b : Y ⟶ Y') {n : ℕ} (x : Ext.{w} X Y n) :
    extConj (𝟙 X) b x = x.comp (Ext.mk₀ b) (add_zero n) := by
  simp [extConj]

/-- `extConj` as an additive map. -/
def extConjHom {X' X Y Y' : C} (a : X' ⟶ X) (b : Y ⟶ Y') (n : ℕ) :
    Ext.{w} X Y n →+ Ext.{w} X' Y' n where
  toFun := extConj a b
  map_zero' := by simp [extConj, Ext.zero_comp, Ext.comp_zero]
  map_add' := extConj_add a b

/-- Conjugation commutes with carrying a class along an exact functor. -/
theorem extConj_mapExactFunctor [HasExt.{w'} D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {X' X Y Y' : C} (a : X' ⟶ X)
    (b : Y ⟶ Y') {n : ℕ} (x : Ext.{w} X Y n) :
    ((extConj a b x).mapExactFunctor F : Ext.{w'} (F.obj X') (F.obj Y') n) =
      extConj (F.map a) (F.map b) (x.mapExactFunctor F : Ext.{w'} (F.obj X) (F.obj Y) n) := by
  simp only [extConj, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- **`Ext` along isomorphic exact functors, in `extConj` form.** -/
theorem ext_mapExactFunctor_of_iso' [HasExt.{w'} D] [EnoughInjectives C]
    (F F' : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (α : F ≅ F')
    {A B : C} {n : ℕ} (x : Ext.{w} A B n) :
    (x.mapExactFunctor F' : Ext.{w'} (F'.obj A) (F'.obj B) n) =
      extConj (α.inv.app A) (α.hom.app B) (x.mapExactFunctor F : Ext.{w'} (F.obj A) (F.obj B) n) :=
  ext_mapExactFunctor_of_iso F F' α A n B x

end Conj

end Stacks.Homology

end
