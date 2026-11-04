module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalarsColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ExtendScalarsBaseChange

/-!
# Base change of extensions of scalars of presheaves of modules along a diagram of rings

Let `A` be a presheaf of not necessarily commutative rings on a category `C`, let `M` be a
presheaf of `A`-modules, and let `k ↦ B_k` be a diagram of presheaves of rings equipped with
compatible morphisms `β_k : A ⟶ B_k`, with a cocone `B` and `γ : A ⟶ B`. Each objectwise
extension of scalars `B_k ⊗_A M`, read back as a presheaf of `A`-modules
`Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj (β_k) M`, is joined to the others by the
base change morphisms `baseChangeTo`, giving a diagram of presheaves of `A`-modules. At each
object `V` of `C`, its transitions and the base changes to `B ⊗_A M` are the transitions and
legs of the algebraic diagram of extensions of scalars along `A(V) → B_k(V)` of
`StacksFrontier.Algebra.Category.ModuleCat.NoncommExtendScalarsColimit`.

## Implementation notes

The identification with the algebraic diagram rests on a single computation: `baseChangeTo`
sends a pure tensor `b ⊗ m` to `ρ(b) ⊗ m` (`baseChangeTo_app_ptmul`). It is not a `rfl`: the
adjoint transpose produces `ρ(b) * 1` rather than `ρ(b)`.

## Main definitions

* `Stacks.NoncommChangeOfRings.Presheaf.ptmul`: a pure tensor, read in the sections of
  `restrictExtendObj`.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeDiagram`: the diagram `k ↦ B_k ⊗_A M` of
  presheaves of `A`-modules, with the base change morphisms
  `baseChangeTo (β k) (𝔅.map f) M (β k') (hβ f)` as its transitions.

## Main results

* `Stacks.NoncommChangeOfRings.Presheaf.unit_app_apply`: the unit of the objectwise extension
  of scalars sends `m` to `1 ⊗ m`.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_app_ptmul`: the base change sends
  `b ⊗ m` to `ρ(b) ⊗ m`.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_app_eq_transition`: at `V`, a transition of
  `baseChangeDiagram` is the transition of the algebraic diagram.
* `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_app_eq_leg`: at `V`, the base change along
  a coprojection is the corresponding leg of the algebraic cocone.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct PresheafOfModules

universe w' w v₁ u₁ u

namespace Stacks.NoncommChangeOfRings.Presheaf

/-! ### Pure tensors in the sections of an extension of scalars -/

section Tmul

variable {C : Type u₁} [Category.{v₁} C] {A B B' : Cᵒᵖ ⥤ RingCat.{u}}

/-- A pure tensor `b ⊗ m`, read in the sections at `V` of `restrictExtendObj γ M`, which are the
relative tensor product `B(V) ⊗_{A(V)} M(V)` up to two unfoldings. -/
noncomputable def ptmul (γ : A ⟶ B) (M : PresheafOfModules.{u} A) (V : Cᵒᵖ) (b : B.obj V)
    (m : M.obj V) : ↑((restrictExtendObj γ M).obj V) := tmul (γ.app V).hom b m

variable (γ : A ⟶ B) (M : PresheafOfModules.{u} A) (V : Cᵒᵖ)

/-- A pure tensor with left factor `0` vanishes. -/
lemma ptmul_zero_left (m : M.obj V) : ptmul γ M V 0 m = 0 := zero_tmul (γ.app V).hom m

/-- A pure tensor is additive in its left factor. -/
lemma ptmul_add_left (b b' : B.obj V) (m : M.obj V) :
    ptmul γ M V (b + b') m = ptmul γ M V b m + ptmul γ M V b' m :=
  add_tmul (γ.app V).hom b b' m

/-- A pure tensor with left factor `-b` is the negative of the one with left factor `b`. -/
lemma ptmul_neg_left (b : B.obj V) (m : M.obj V) : ptmul γ M V (-b) m = -ptmul γ M V b m :=
  (congrArg (mk (γ.app V).hom ↑(M.obj V)) (TensorProduct.neg_tmul b m)).trans
    (map_neg (mk (γ.app V).hom ↑(M.obj V)) _)

/-- Induction on pure tensors in the sections of `restrictExtendObj`. -/
lemma ptmul_induction_on {motive : ↑((restrictExtendObj γ M).obj V) → Prop}
    (x : ↑((restrictExtendObj γ M).obj V)) (zero : motive 0)
    (pure : ∀ (b : B.obj V) (m : M.obj V), motive (ptmul γ M V b m))
    (add : ∀ u v, motive u → motive v → motive (u + v)) : motive x :=
  induction_on (γ.app V).hom (motive := motive) x zero pure add

/-- Two `A(V)`-linear maps out of the sections of `restrictExtendObj γ M` agree as soon as they
agree on pure tensors. -/
lemma ptmul_hom_ext {P : ModuleCat.{u} (A.obj V)}
    {x y : (restrictExtendObj γ M).obj V ⟶ P}
    (H : ∀ (b : B.obj V) (m : M.obj V), x (ptmul γ M V b m) = y (ptmul γ M V b m)) : x = y := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  refine ptmul_induction_on γ M V (motive := fun z => x z = y z) z ?_ H ?_
  · rw [map_zero, map_zero]
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]

/-- The identity morphism of a presheaf of modules, read on a section. -/
lemma hom_app_id_apply {M : PresheafOfModules.{u} A} (V : Cᵒᵖ) (z : M.obj V) :
    Hom.app (𝟙 M) V z = z := rfl

/-- A composite of morphisms of presheaves of modules, read on a section. -/
lemma hom_app_comp_apply {M N P : PresheafOfModules.{u} A} (x : M ⟶ N) (y : N ⟶ P)
    (V : Cᵒᵖ) (z : M.obj V) : Hom.app (x ≫ y) V z = Hom.app y V (Hom.app x V z) := rfl

/-- **The unit of the objectwise extension of scalars sends `m` to `1 ⊗ m`.** -/
lemma unit_app_apply (m : M.obj V) :
    Hom.app ((extendScalarsAdjunction.{u} γ).unit.app M) V m = ptmul γ M V 1 m := rfl

/-- **The base change along a triangle sends `b ⊗ m` to `ρ(b) ⊗ m`.** -/
lemma baseChange_app_ptmul (ρ : B ⟶ B') (b : B.obj V) (m : M.obj V) :
    Hom.app (baseChange γ ρ M) V (ptmul γ M V b m) =
      ptmul (γ ≫ ρ) M V ((ρ.app V).hom b) m := by
  have h : Hom.app (baseChange γ ρ M) V (ptmul γ M V b m) =
      ptmul (γ ≫ ρ) M V ((ρ.app V).hom b * 1) m := rfl
  rw [h, mul_one]

/-- **The base change along a triangle sends `b ⊗ m` to `ρ(b) ⊗ m`**, with the target read
along a morphism `δ` merely equal to the composite. -/
lemma baseChangeTo_app_ptmul (ρ : B ⟶ B') (δ : A ⟶ B') (hδ : γ ≫ ρ = δ) (b : B.obj V)
    (m : M.obj V) :
    Hom.app (baseChangeTo γ ρ M δ hδ) V (ptmul γ M V b m) =
      ptmul δ M V ((ρ.app V).hom b) m := by
  subst hδ
  simp only [baseChangeTo, eqToHom_refl, Category.comp_id]
  exact baseChange_app_ptmul γ M V ρ b m

end Tmul

/-! ### The diagram of base changes and its cocone -/

section Diagram

variable {C : Type u₁} [Category.{v₁} C] {A : Cᵒᵖ ⥤ RingCat.{u}} {K : Type w}
  [Category.{w'} K] {𝔅 : K ⥤ (Cᵒᵖ ⥤ RingCat.{u})} {c : Cocone 𝔅}
  (β : ∀ k, A ⟶ 𝔅.obj k) (hβ : ∀ {k k' : K} (f : k ⟶ k'), β k ≫ 𝔅.map f = β k')
  (γ : A ⟶ c.pt) (hγ : ∀ k, β k ≫ c.ι.app k = γ) (M : PresheafOfModules.{u} A)

include hβ in
/-- **The diagram `k ↦ B_k ⊗_A M`** of presheaves of `A`-modules, with the base change
morphisms as its transitions. -/
noncomputable def baseChangeDiagram : K ⥤ PresheafOfModules.{u} A where
  obj k := restrictExtendObj (β k) M
  map {k k'} f := baseChangeTo (β k) (𝔅.map f) M (β k') (hβ f)
  map_id k := PresheafOfModules.hom_ext fun V =>
    ptmul_hom_ext (β k) M V fun b m => by
      rw [baseChangeTo_app_ptmul, hom_app_id_apply, 𝔅.map_id k]
      rfl
  map_comp {k k' k''} f f' := PresheafOfModules.hom_ext fun V =>
    ptmul_hom_ext (β k) M V fun b m => by
      rw [baseChangeTo_app_ptmul, hom_app_comp_apply, baseChangeTo_app_ptmul,
        baseChangeTo_app_ptmul, 𝔅.map_comp f f']
      rfl

/-- The transition of `baseChangeDiagram` along `f` is the base change along `𝔅.map f`. -/
lemma baseChangeDiagram_map {k k' : K} (f : k ⟶ k') :
    (baseChangeDiagram β hβ M).map f = baseChangeTo (β k) (𝔅.map f) M (β k') (hβ f) := rfl

/-- A leg of the cocone absorbs the constant functor's transition. -/
lemma baseChangeTo_comp_const_map (k : K) {k' : K} (f : k ⟶ k') :
    baseChangeTo (β k) (c.ι.app k) M γ (hγ k) ≫
        ((Functor.const K).obj (restrictExtendObj γ M)).map f =
      baseChangeTo (β k) (c.ι.app k) M γ (hγ k) := Category.comp_id _

/-- A transition of the diagram followed by a leg, with the transition spelled out. -/
lemma baseChangeDiagram_map_comp_leg {k k' : K} (f : k ⟶ k') :
    (baseChangeDiagram β hβ M).map f ≫ baseChangeTo (β k') (c.ι.app k') M γ (hγ k') =
      baseChangeTo (β k) (𝔅.map f) M (β k') (hβ f) ≫
        baseChangeTo (β k') (c.ι.app k') M γ (hγ k') :=
  congrArg (fun x : restrictExtendObj (β k) M ⟶ restrictExtendObj (β k') M =>
      x ≫ baseChangeTo (β k') (c.ι.app k') M γ (hγ k')) (baseChangeDiagram_map β hβ M f)

end Diagram

/-! ### The sections of the base change -/

section Sections

variable {C : Type u₁} [Category.{v₁} C] {A : Cᵒᵖ ⥤ RingCat.{u}} {K : Type w}
  [Category.{w'} K] {𝔅 : K ⥤ (Cᵒᵖ ⥤ RingCat.{u})} {c : Cocone 𝔅}
  (β : ∀ k, A ⟶ 𝔅.obj k) (hβ : ∀ {k k' : K} (f : k ⟶ k'), β k ≫ 𝔅.map f = β k')
  (γ : A ⟶ c.pt) (hγ : ∀ k, β k ≫ c.ι.app k = γ) (M : PresheafOfModules.{u} A)
  (V : Cᵒᵖ)

/-- A triangle of presheaves of rings, read on a section. -/
private theorem comp_app_hom_apply {B B' B'' : Cᵒᵖ ⥤ RingCat.{u}} (φ : B ⟶ B') (ψ : B' ⟶ B'')
    (δ : B ⟶ B'') (h : φ ≫ ψ = δ) (a : ↑(B.obj V)) :
    (ψ.app V).hom ((φ.app V).hom a) = (δ.app V).hom a := by
  subst h
  rfl

/-- The diagram of rings obtained by evaluating the diagram of presheaves of rings at `V`. -/
noncomputable abbrev ringDiagramAt : K ⥤ RingCat.{u} :=
  𝔅 ⋙ (CategoryTheory.evaluation Cᵒᵖ RingCat.{u}).obj V

/-- The cocone of rings obtained by evaluating the cocone of presheaves of rings at `V`. -/
noncomputable abbrev ringCoconeAt : Cocone (ringDiagramAt (𝔅 := 𝔅) V) :=
  ((CategoryTheory.evaluation Cᵒᵖ RingCat.{u}).obj V).mapCocone c

/-- The structure morphism `A(V) → B_k(V)`. -/
noncomputable abbrev βAt (k : K) : ↑(A.obj V) →+* ↑((ringDiagramAt (𝔅 := 𝔅) V).obj k) :=
  ((β k).app V).hom

include hβ in
/-- The structure morphisms `A(V) → B_k(V)` are compatible with the transitions of the evaluated
diagram. -/
lemma hβAt : ∀ {k k' : K} (f : k ⟶ k') (a : ↑(A.obj V)),
    ((ringDiagramAt (𝔅 := 𝔅) V).map f).hom (βAt β V k a) = βAt β V k' a := by
  intro k k' f a
  exact comp_app_hom_apply V _ _ _ (hβ f) a

/-- The structure morphism `A(V) → B(V)`. -/
noncomputable abbrev γAt : ↑(A.obj V) →+* ↑(ringCoconeAt (c := c) V).pt := (γ.app V).hom

include hγ in
/-- The legs of the evaluated cocone carry `A(V) → B_k(V)` to the structure morphism
`A(V) → B(V)`. -/
lemma hγAt : ∀ (k : K) (a : ↑(A.obj V)),
    ((ringCoconeAt (c := c) V).ι.app k).hom (βAt β V k a) = γAt γ V a := by
  intro k a
  exact comp_app_hom_apply V _ _ _ (hγ k) a

include hβ in
/-- **The sections at `V` of a transition morphism of the diagram are the transition morphism of
the algebraic diagram of base changes.** -/
lemma baseChangeTo_app_eq_transition {k k' : K} (f : k ⟶ k') :
    Hom.app (baseChangeTo (β k) (𝔅.map f) M (β k') (hβ f)) V =
      (Colimit.transition (βAt β V) (hβAt β hβ V) (M.obj V) f :
        (restrictExtendObj (β k) M).obj V ⟶ (restrictExtendObj (β k') M).obj V) :=
  ptmul_hom_ext (β k) M V fun b m => by
    rw [baseChangeTo_app_ptmul]
    rfl

include hγ in
/-- **The sections at `V` of a base change along a coprojection are the corresponding leg of the
algebraic cocone.** -/
lemma baseChangeTo_app_eq_leg (k : K) :
    Hom.app (baseChangeTo (β k) (c.ι.app k) M γ (hγ k)) V =
      (Colimit.leg (βAt β V) (hβAt β hβ V) (γAt γ V) (hγAt β γ hγ V) (M.obj V) k :
        (restrictExtendObj (β k) M).obj V ⟶ (restrictExtendObj γ M).obj V) :=
  ptmul_hom_ext (β k) M V fun b m => by
    rw [baseChangeTo_app_ptmul]
    rfl

end Sections

end Stacks.NoncommChangeOfRings.Presheaf

end
