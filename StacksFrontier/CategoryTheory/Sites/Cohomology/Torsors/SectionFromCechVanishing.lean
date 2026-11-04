module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FirstCocycles

/-!
# A pseudo-torsor with local sections and vanishing first Čech cohomology has a section

Let `C` be a category, let `E = {U_i → X}` be a family of morphisms whose finite iterated fibre
products exist, let `Θ` be a presheaf of abelian groups on `C` and let `F` be a presheaf of
sets on which `Θ` acts, objectwise and compatibly with restriction, simply transitively. If `F`
satisfies the sheaf condition for `E`, has a section over every member of `E`, and the first
Čech cohomology `Ȟ¹(E, Θ)` vanishes, then `F` has a section over `X`.

This is the argument of [Stacks Project, Tag 03AJ] read off on a single covering family: the
differences of chosen local sections form a Čech `1`-cocycle, a cochain of which it is the
coboundary corrects the local sections so that they agree on the pairwise fibre products, and
the sheaf condition glues them.

## Main results

* `Stacks.CechSite.nonempty_of_subsingleton_cechH1`: the statement above.

## Implementation notes

Neither a sheaf condition on `Θ` nor any cohomological machinery beyond the explicit cocycles
`Stacks.CechSite.cocycles1` is used, and the action is asked for only where it is used: an
`AddAction` on every set of sections, simple transitivity on every set of sections (an empty set
of sections satisfies it vacuously), and compatibility with the restriction maps. This is the
form in which an action of a sheaf of abelian groups on a pseudo-torsor is usually *produced*,
for instance for the sheaf of lifts of an infinitesimal lifting problem, so a consumer does not
have to package it as a `Stacks.Cohomology.Torsors.PseudoTorsor` first. The torsor-theoretic
form of the same conclusion, for a torsor under a sheaf on a site with `Ext` groups, is
`Stacks.Cohomology.Torsors.isTrivial_of_subsingleton_cechH1`.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
-/

@[expose] public section

universe t a w v u

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C] {X : C} (E : PreZeroHypercover.{w} X)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- The projection from an iterated fibre product of members of `E` to one of its factors. -/
noncomputable abbrev cechProj {n : ℕ} (k : Fin (n + 1) → E.I₀) (m : Fin (n + 1)) :
    (∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left ⟶ E.X (k m) :=
  (Pi.π (fun j ↦ Over.mk (E.f (k j))) m).left

/-- A face projection followed by a factor projection is a factor projection. -/
lemma faceProjection_left_comp_cechProj {n : ℕ} (k : Fin (n + 2) → E.I₀) (j : Fin (n + 2))
    (m : Fin (n + 1)) :
    (faceProjection E k j).left ≫ cechProj E (fun b ↦ k (j.succAbove b)) m =
      cechProj E k (j.succAbove m) := by
  rw [cechProj, cechProj, ← Over.comp_left, faceProjection, Pi.lift_π]

attribute [local instance] singletonProjection_isIso

variable [HasProducts.{w} AddCommGrpCat.{a}]
    (Θ : Cᵒᵖ ⥤ AddCommGrpCat.{a}) (F : Cᵒᵖ ⥤ Type t)

/-- **A pseudo-torsor with sections on a covering family and vanishing first Čech cohomology
has a global section.** Let `Θ` act on the sets of sections of `F` simply transitively and
compatibly with restriction, let `F` satisfy the sheaf condition for the family `E`, and let
`F` have a section over every member of `E`. If `Ȟ¹(E, Θ)` vanishes, `F` has a section over
the target of `E`. -/
theorem nonempty_of_subsingleton_cechH1 [∀ U : Cᵒᵖ, AddAction (Θ.obj U) (F.obj U)]
    (hF : (Presieve.ofArrows E.X E.f).IsSheafFor F)
    (hbij : ∀ (U : Cᵒᵖ) (s : F.obj U), Function.Bijective (fun θ : Θ.obj U ↦ θ +ᵥ s))
    (hnat : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (θ : Θ.obj U) (s : F.obj U),
      F.map k (θ +ᵥ s) = (Θ.map k).hom θ +ᵥ F.map k s)
    (hs : ∀ i, Nonempty (F.obj (op (E.X i))))
    (hH : Subsingleton (cechH1 E Θ)) : Nonempty (F.obj (op X)) := by
  let s : ∀ i, F.obj (op (E.X i)) := fun i ↦ Classical.choice (hs i)
  -- the difference of two sections
  let δ : ∀ {U : Cᵒᵖ} (_ _ : F.obj U), Θ.obj U :=
    fun {U} x y ↦ (Equiv.ofBijective _ (hbij U y)).symm x
  have hδ : ∀ {U : Cᵒᵖ} (x y : F.obj U), δ x y +ᵥ y = x :=
    fun {U} x y ↦ (Equiv.ofBijective _ (hbij U y)).apply_symm_apply x
  have hδuniq : ∀ {U : Cᵒᵖ} (x y : F.obj U) (θ : Θ.obj U), θ +ᵥ y = x → δ x y = θ :=
    fun {U} x y θ h ↦ (hbij U y).1 ((hδ x y).trans h.symm)
  have hδmap : ∀ {U V : Cᵒᵖ} (k : U ⟶ V) (x y : F.obj U),
      (Θ.map k).hom (δ x y) = δ (F.map k x) (F.map k y) := fun k x y ↦
    (hδuniq _ _ _ (by rw [← hnat, hδ])).symm
  -- the restrictions of the chosen sections to the iterated fibre products
  let R : ∀ {n : ℕ} (k : Fin (n + 1) → E.I₀) (m : Fin (n + 1)),
      F.obj (op (∏ᶜ (fun j ↦ Over.mk (E.f (k j))) : Over X).left) :=
    fun k m ↦ F.map (cechProj E k m).op (s (k m))
  have hR : ∀ {n : ℕ} (k : Fin (n + 2) → E.I₀) (j : Fin (n + 2)) (m : Fin (n + 1)),
      F.map (faceProjection E k j).left.op (R (fun b ↦ k (j.succAbove b)) m) =
        R k (j.succAbove m) := by
    intro n k j m
    change F.map _ (F.map _ _) = F.map _ _
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, faceProjection_left_comp_cechProj]
  -- the cocycle of differences
  let c : cechCochain E Θ 1 := fun k ↦ δ (R k 0) (R k 1)
  have hc : c ∈ cocycles1 E Θ := by
    rw [mem_cocycles1_iff']
    intro k
    simp only [c, hδmap, hR]
    change δ (R k 1) (R k 2) + δ (R k 0) (R k 1) = δ (R k 0) (R k 2)
    refine (hδuniq _ _ _ ?_).symm
    rw [add_comm (δ (R k 1) (R k 2)), add_vadd, hδ, hδ]
  obtain ⟨t, ht⟩ := (cls_eq_zero_iff E Θ ⟨c, hc⟩).1 (Subsingleton.elim _ _)
  -- the correction, read on the members of the family
  let τ : ∀ i, Θ.obj (op (E.X i)) := fun i ↦
    (Θ.map (inv (singletonProjection E i)).left.op).hom (t fun _ ↦ i)
  have ht' : ∀ l : Fin 1 → E.I₀, t l = (Θ.map (cechProj E l 0).op).hom (τ (l 0)) := by
    intro l
    obtain ⟨i, rfl⟩ : ∃ i, l = fun _ ↦ i := ⟨l 0, by ext j; exact congrArg l (Fin.eq_zero j)⟩
    change _ = (Θ.map (singletonProjection E i).left.op).hom
      ((Θ.map (inv (singletonProjection E i)).left.op).hom (t fun _ ↦ i))
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ← Over.comp_left,
      IsIso.hom_inv_id, Over.id_left, op_id, Θ.map_id]
    rfl
  let s' : ∀ i, F.obj (op (E.X i)) := fun i ↦ τ i +ᵥ s i
  -- the corrected sections agree on the pairwise fibre products
  have hpair : ∀ k : Fin 2 → E.I₀,
      F.map (cechProj E k 0).op (s' (k 0)) = F.map (cechProj E k 1).op (s' (k 1)) := by
    intro k
    have hk := congrFun ht k
    rw [cechDifferential_zero_apply, ht', ht'] at hk
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at hk
    rw [faceProjection_left_comp_cechProj, faceProjection_left_comp_cechProj] at hk
    change _ = δ (R k 0) (R k 1) at hk
    simp only [s', hnat]
    change _ +ᵥ R k 0 = _ +ᵥ R k 1
    rw [← hδ (R k 0) (R k 1), ← hk, ← add_vadd]
    exact congrArg (· +ᵥ R k 1) (add_sub_cancel _ _)
  -- glue
  refine ((Presieve.isSheafFor_arrows_iff _ _).1 hF s' ?_).exists.elim fun x _ ↦ ⟨x⟩
  intro i j Z gi gj hij
  let k : Fin 2 → E.I₀ := ![i, j]
  let l : Over.mk (gi ≫ E.f i) ⟶ ∏ᶜ (fun b : Fin 2 ↦ Over.mk (E.f (k b))) :=
    Pi.lift (Fin.cases (Over.homMk gi) (Fin.cases (Over.homMk gj hij.symm) finZeroElim))
  have h₀ : l.left ≫ cechProj E k 0 = gi := congrArg Over.Hom.left (Pi.lift_π _ 0)
  have h₁ : l.left ≫ cechProj E k 1 = gj := congrArg Over.Hom.left (Pi.lift_π _ 1)
  have hh := congrArg (F.map l.left.op) (hpair k)
  rwa [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp,
    h₀, h₁] at hh

end Stacks.CechSite

end
