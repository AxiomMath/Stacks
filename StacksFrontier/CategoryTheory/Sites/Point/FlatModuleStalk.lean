module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCriterionConverse
public import Mathlib.RingTheory.Flat.EquationalCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a flat sheaf of modules is a flat module

Let `(C, O)` be a ringed site, `F` a flat sheaf of `O`-modules and `Φ` a point of `C`.  Stacks
05VB asserts that the stalk `F_Φ` is a flat `O_Φ`-module.

## Main results

* `Stacks.exists_toPresheafFiber_fin` and `Stacks.exists_toPresheafModuleFiber_fin`: finitely
  many elements of the stalk of a presheaf, respectively of a presheaf of modules, are
  simultaneously germs of sections over one common neighbourhood of the point.
* `Stacks.isFlatModuleStalk_of_isFlat`: **Stacks 05VB**.

## Implementation notes

**The route is not the source's.**  Stacks derives 05VB from 05VD (a pullback of a flat module
is flat) by reading the point as a morphism of ringed topoi `(Sh(pt), O_Φ) ⟶ (Sh(C), O)`, as in
Stacks 05V6.  Neither 05VD nor that reading is available in this development.  Instead the proof
here goes through the *equational* criterion on both sides:

* over the ring `O_Φ`, Mathlib's `Module.Flat.of_forall_isTrivialRelation` (Stacks 00HK) reduces
  flatness to: every relation `∑ fᵢ xᵢ = 0` is trivial, i.e. `xᵢ = ∑ⱼ aᵢⱼ yⱼ` with
  `∑ᵢ fᵢ aᵢⱼ = 0`;
* over the sheaf `F`, Stacks 08FC gives exactly the sheaf-level form of that statement, local on
  the site: `Stacks.SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations`.

The two are joined by three facts about a point of a site, all already present: the category of
neighbourhoods `Φ.fiber.Elements` is cofiltered, so finitely many germs are germs over one
neighbourhood (`exists_toPresheafFiber_fin` below); a germ vanishes iff the section vanishes on a
smaller neighbourhood (`Stacks.toPresheafModuleFiber_eq_iff`); and a covering sieve is hit by the
point (`Φ.jointly_surjective`), which is what turns the *local* factorisation 08FC supplies into
a factorisation of germs.

**The two spellings of the stalk ring.**  The stalk of a sheaf of modules is a module over the
`RingCat`-valued stalk `R_Φ` of the underlying sheaf of rings, while `Stacks.moduleStalk` presents
it over the `CommRingCat`-valued stalk `O_Φ` by restriction of scalars along
`Stacks.commRingSheafFiberIso`.  Germs of sections of `O` are produced here only in the `RingCat`
spelling and transported with that isomorphism, so no compatibility of the comparison map with
the colimit injections is needed.  Multiplication is commuted only on the `CommRingCat` side,
where it is available.

**Universes.** `C : Type u` with `Category.{v} C`, and the module universe is `max v w`, which is
the shape Stacks 08FC is stated at; `LocallySmall.{max v w} C` and `Φ : J.Point.{max v w}` follow.
No universe is collapsed.

## References

* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 00HK](https://stacks.math.columbia.edu/tag/00HK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' v' u' v u w

namespace Stacks

/-! ### Finitely many germs live over one neighbourhood -/

section CommonNeighbourhood

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  (Φ : J.Point.{w})

omit [LocallySmall.{w} C] in
/-- Two neighbourhoods of a point of a site are both refined by a third: this is
cofilteredness of `Φ.fiber.Elements`, read off the underlying objects of `C`. -/
lemma exists_common_neighbourhood {U V : C} (x : Φ.fiber.obj U) (y : Φ.fiber.obj V) :
    ∃ (W : C) (z : Φ.fiber.obj W) (f : W ⟶ U) (g : W ⟶ V),
      Φ.fiber.map f z = x ∧ Φ.fiber.map g z = y :=
  ⟨(IsCofiltered.min (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).1,
    (IsCofiltered.min (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).2,
    (IsCofiltered.minToLeft (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).1,
    (IsCofiltered.minToRight (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).1,
    (IsCofiltered.minToLeft (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).2,
    (IsCofiltered.minToRight (Φ.fiber.elementsMk U x) (Φ.fiber.elementsMk V y)).2⟩

section Presheaf

variable {A : Type u'} [Category.{v'} A] [HasColimitsOfSize.{w, w} A]
  {FC : A → A → Type*} {CC : A → Type w'} [∀ X Y : A, FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w'} A FC] [PreservesFilteredColimitsOfSize.{w, w} (forget A)]

/-- Finitely many elements of the stalk of a presheaf at a point of a site are simultaneously
germs of sections over one common neighbourhood.  The category of neighbourhoods is cofiltered,
which is what lets the neighbourhoods produced one element at a time be merged. -/
lemma exists_toPresheafFiber_fin (P : Cᵒᵖ ⥤ A) :
    ∀ {l : ℕ} (p : Fin l → ToType ((Φ.presheafFiber (A := A)).obj P)),
      ∃ (X : C) (x : Φ.fiber.obj X) (z : Fin l → ToType (P.obj (op X))),
        ∀ i, Φ.toPresheafFiber X x P (z i) = p i := by
  intro l
  induction l with
  | zero =>
      intro p
      obtain ⟨E⟩ := (IsCofiltered.nonempty : Nonempty Φ.fiber.Elements)
      exact ⟨E.1, E.2, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ l ih =>
      intro p
      obtain ⟨U, x, z, hz⟩ := ih (fun i ↦ p i.succ)
      obtain ⟨V, y, t, ht⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) (p 0)
      obtain ⟨W, wpt, g₁, g₂, hg₁, hg₂⟩ := exists_common_neighbourhood Φ x y
      refine ⟨W, wpt, Fin.cons (P.map g₂.op t) (fun i ↦ P.map g₁.op (z i)), ?_⟩
      intro i
      induction i using Fin.cases with
      | zero =>
          rw [Fin.cons_zero, Φ.toPresheafFiber_w_apply g₂ wpt P t, hg₂, ht]
      | succ j =>
          rw [Fin.cons_succ, Φ.toPresheafFiber_w_apply g₁ wpt P (z j), hg₁, hz j]

end Presheaf

/-- Finitely many elements of the stalk of a presheaf of modules at a point of a site are
simultaneously germs of sections over one common neighbourhood. -/
lemma exists_toPresheafModuleFiber_fin {R : Cᵒᵖ ⥤ RingCat.{w}} (M : PresheafOfModules.{w} R) :
    ∀ {l : ℕ} (p : Fin l → (presheafModuleFiber Φ R).obj M),
      ∃ (X : C) (x : Φ.fiber.obj X) (z : Fin l → M.obj (op X)),
        ∀ i, toPresheafModuleFiber Φ M X x (z i) = p i := by
  intro l
  induction l with
  | zero =>
      intro p
      obtain ⟨E⟩ := (IsCofiltered.nonempty : Nonempty Φ.fiber.Elements)
      exact ⟨E.1, E.2, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ l ih =>
      intro p
      obtain ⟨U, x, z, hz⟩ := ih (fun i ↦ p i.succ)
      obtain ⟨V, y, t, ht⟩ := toPresheafModuleFiber_jointly_surjective Φ M (p 0)
      obtain ⟨W, wpt, g₁, g₂, hg₁, hg₂⟩ := exists_common_neighbourhood Φ x y
      refine ⟨W, wpt, Fin.cons (M.map g₂.op t) (fun i ↦ M.map g₁.op (z i)), ?_⟩
      intro i
      induction i using Fin.cases with
      | zero =>
          change toPresheafModuleFiber Φ M W wpt (M.map g₂.op t) = p 0
          rw [← toPresheafModuleFiber_w Φ M g₂ wpt t, hg₂, ht]
      | succ j =>
          change toPresheafModuleFiber Φ M W wpt (M.map g₁.op (z j)) = p j.succ
          rw [← toPresheafModuleFiber_w Φ M g₁ wpt (z j), hg₁, hz j]

end CommonNeighbourhood

/-! ### Stacks 05VB -/

section Flat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{max v w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max v w} RingCat.{max v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max v w}]
  [HasWeakSheafify J AddCommGrpCat.{max v w}]
  {O : Sheaf J CommRingCat.{max v w}}

/-- **Stacks 05VB.**  The stalk at a point of a site of a flat sheaf of `O`-modules is a flat
module over the stalk of `O`. -/
@[stacks 05VB]
theorem isFlatModuleStalk_of_isFlat
    (F : _root_.SheafOfModules.{max v w} (commRingSheafToRingSheaf O))
    (hF : SheafOfModules.IsFlat F) (Φ : J.Point.{max v w}) :
    IsFlatModuleStalk Φ O F := by
  -- `e` identifies the `RingCat`-valued stalk of the underlying sheaf of rings with the
  -- `CommRingCat`-valued stalk of `O`; the module structure on `moduleStalk` is restriction of
  -- scalars along `e.inv`.
  set e := commRingSheafFiberIso Φ O with he
  set Mp := (_root_.SheafOfModules.forget (commRingSheafToRingSheaf O)).obj F with hMp
  have hcrit := (SheafOfModules.isFlat_iff_hasLocalSingleRelationFactorizations F).1 hF
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hfx
  -- Lift the scalars `f` to germs of sections of `O` and the elements `x` to germs of sections
  -- of `F`, over one common neighbourhood `(U, u)`.
  obtain ⟨U₁, u₁, a₁, ha₁⟩ :=
    exists_toPresheafFiber_fin Φ (A := RingCat.{max v w})
      (commRingSheafToRingSheaf O).obj (fun i ↦ e.inv.hom (f i))
  obtain ⟨U₂, u₂, s₂, hs₂⟩ := exists_toPresheafModuleFiber_fin Φ Mp x
  obtain ⟨U, u, c₁, c₂, hc₁, hc₂⟩ := exists_common_neighbourhood Φ u₁ u₂
  set a : Fin l → (commRingSheafToRingSheaf O).obj.obj (op U) :=
    fun i ↦ (commRingSheafToRingSheaf O).obj.map c₁.op (a₁ i) with hadef
  set s : Fin l → Mp.obj (op U) := fun i ↦ Mp.map c₂.op (s₂ i) with hsdef
  have ha : ∀ i, Φ.toPresheafFiber U u (commRingSheafToRingSheaf O).obj (a i) = e.inv.hom (f i) :=
    fun i ↦ by
      rw [hadef, Φ.toPresheafFiber_w_apply c₁ u (commRingSheafToRingSheaf O).obj (a₁ i), hc₁,
        ha₁ i]
  have hs : ∀ i, toPresheafModuleFiber Φ Mp U u (s i) = x i := fun i ↦ by
    rw [hsdef, ← toPresheafModuleFiber_w Φ Mp c₂ u (s₂ i), hc₂, hs₂ i]
  -- The comparison isomorphism is a bijection, and is used in both directions.
  have hinvhom : ∀ r, e.inv.hom (e.hom.hom r) = r := fun _ ↦ by simp
  have hhominv : ∀ c, e.hom.hom (e.inv.hom c) = c := fun _ ↦ by simp
  -- The relation `∑ fᵢ xᵢ = 0` is the germ of `∑ aᵢ sᵢ`, hence that section vanishes on a
  -- smaller neighbourhood `(V, v)`.
  have hgerm : toPresheafModuleFiber Φ Mp U u (∑ i, a i • s i) = 0 := by
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) hfx
    rw [toPresheafModuleFiber_smul, ha i, hs i]
    rfl
  obtain ⟨V, g, v, hgv, hvan⟩ :=
    (toPresheafModuleFiber_eq_iff Φ Mp U u (∑ i, a i • s i) 0).1 (by rw [hgerm, map_zero])
  have hrel : ∑ i, (commRingSheafToRingSheaf O).obj.map g.op (a i) • Mp.map g.op (s i) = 0 := by
    have h1 : ∑ i, (commRingSheafToRingSheaf O).obj.map g.op (a i) • Mp.map g.op (s i)
        = Mp.map g.op (∑ i, a i • s i) := by
      rw [map_sum]
      exact (Finset.sum_congr rfl fun i _ ↦ Mp.map_smul g.op (a i) (s i)).symm
    rw [h1, hvan, map_zero]
  -- Stacks 08FC gives a covering sieve of `V` on each member of which the sections factor
  -- through a finite free module by a matrix annihilating the relation.
  obtain ⟨S, hS, hfac⟩ := hcrit V l (fun i ↦ (commRingSheafToRingSheaf O).obj.map g.op (a i))
    (fun i ↦ Mp.map g.op (s i)) hrel
  -- The point hits that covering sieve.
  obtain ⟨W, h, hhS, wpt, hwpt⟩ := Φ.jointly_surjective S hS v
  obtain ⟨k, t, B, hB₁, hB₂⟩ := hfac h hhS
  have hfi : ∀ i, Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj
      ((commRingSheafToRingSheaf O).obj.map h.op
        ((commRingSheafToRingSheaf O).obj.map g.op (a i))) = e.inv.hom (f i) := fun i ↦ by
    rw [Φ.toPresheafFiber_w_apply h wpt (commRingSheafToRingSheaf O).obj
        ((commRingSheafToRingSheaf O).obj.map g.op (a i)), hwpt,
      Φ.toPresheafFiber_w_apply g v (commRingSheafToRingSheaf O).obj (a i), hgv, ha i]
  refine ⟨k,
    fun i j ↦ e.hom.hom (Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj (B j i)),
    fun j ↦ toPresheafModuleFiber Φ Mp W wpt (t j), ?_, ?_⟩
  · -- `xᵢ = ∑ⱼ aᵢⱼ yⱼ`
    intro i
    have hxi : toPresheafModuleFiber Φ Mp W wpt (Mp.map h.op (Mp.map g.op (s i))) = x i := by
      rw [← toPresheafModuleFiber_w Φ Mp h wpt (Mp.map g.op (s i)), hwpt,
        ← toPresheafModuleFiber_w Φ Mp g v (s i), hgv, hs i]
    have hall : toPresheafModuleFiber Φ Mp W wpt (Mp.map h.op (Mp.map g.op (s i)))
        = ∑ j : Fin k, Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj (B j i) •
            toPresheafModuleFiber Φ Mp W wpt (t j) :=
      (congrArg (fun z ↦ toPresheafModuleFiber Φ Mp W wpt z) (hB₁ i)).trans
        ((map_sum (toPresheafModuleFiber Φ Mp W wpt) _ _).trans
          (Finset.sum_congr rfl fun j _ ↦ toPresheafModuleFiber_smul Φ Mp W wpt (B j i) (t j)))
    refine hxi.symm.trans (hall.trans (Finset.sum_congr rfl fun j _ ↦ ?_))
    exact (congrArg (fun r ↦ r • toPresheafModuleFiber Φ Mp W wpt (t j))
      (hinvhom (Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj (B j i)))).symm
  · -- `∑ᵢ fᵢ aᵢⱼ = 0`
    intro j
    have hgerm0 : ∑ i : Fin l,
        Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj (B j i) * e.inv.hom (f i) = 0 := by
      have h0 : Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj
          (∑ i : Fin l, B j i * (commRingSheafToRingSheaf O).obj.map h.op
            ((commRingSheafToRingSheaf O).obj.map g.op (a i))) = 0 := by
        rw [hB₂ j 0, map_zero]
      rw [map_sum] at h0
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
      rw [map_mul, hfi i]
    have hfinal : ∑ i : Fin l, e.hom.hom
        (Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj (B j i) * e.inv.hom (f i))
          = 0 := by
      rw [← map_sum, hgerm0, map_zero]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) hfinal
    change f i * e.hom.hom (Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj (B j i))
        = e.hom.hom (Φ.toPresheafFiber W wpt (commRingSheafToRingSheaf O).obj (B j i)
            * e.inv.hom (f i))
    rw [map_mul, hhominv]
    exact mul_comm _ _

end Flat

end Stacks

end
