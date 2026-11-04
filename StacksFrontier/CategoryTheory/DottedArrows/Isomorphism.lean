module

public import StacksFrontier.CategoryTheory.DottedArrows.Faithful
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification

/-!
# Recognising isomorphic dotted arrows

Fix a 2-commutative square in the 2-category of categories fibred in groupoids over a base
category `C`, filled by `γ`, whose right-hand edge `f` is faithful on underlying functors. Two
dotted arrows `a` and `b` for it are isomorphic as soon as their diagonals are connected
objectwise *compatibly with the two `β`s*: the compatibility with the two `α`s, and the naturality
of the connecting family, are then automatic.

The criterion is given in three forms: with the connecting morphisms required to lie over
identities, without that requirement, and with the connecting morphisms given only on a family of
objects that is essentially surjective onto the base of the square.

## Main results

* `CategoryTheory.DottedArrow.beta_naturality`: naturality of `β`, with the composite functor on
  the right-hand side spelled out.
* `CategoryTheory.DottedArrow.isIso_beta_app`: each component of `β` is invertible.
* `CategoryTheory.DottedArrow.pasting_app_eq`: the pasting equation of two dotted arrows on
  components.
* `CategoryTheory.DottedArrow.nonempty_iso_of_forall_hom_isHomLift`: the criterion, with the
  connecting morphisms required to lie over identities.
* `CategoryTheory.DottedArrow.nonempty_iso_of_forall_hom`: the criterion without that
  requirement.
* `CategoryTheory.DottedArrow.nonempty_iso_of_forall_hom_of_essSurj`: the criterion checked only
  on an essentially surjective family.

## References

* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {S T X Y : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} C}
  {x : S ⟶ X} {j : S ⟶ T} {f : X ⟶ Y} {y : T ⟶ Y} {γ : (j ≫ y) ⟶ (x ≫ f)}

namespace DottedArrow

/-- **Naturality of the `β` of a dotted arrow**, with the right-hand composite spelled out as an
iterated `map` rather than as the `map` of a composite. -/
theorem beta_naturality (a : DottedArrow x j f y γ) {z z' : T.val.obj} (i : z ⟶ z') :
    y.hom.toFunctor.map i ≫ a.β.hom.toNatTrans.app z' =
      a.β.hom.toNatTrans.app z ≫ f.hom.toFunctor.map (a.a.hom.toFunctor.map i) :=
  a.β.hom.toNatTrans.naturality i

/-- Each component of the `β` of a dotted arrow is invertible. -/
theorem isIso_beta_app (a : DottedArrow x j f y γ) (z : T.val.obj) :
    IsIso (a.β.hom.toNatTrans.app z) :=
  have : IsIso (X := y.hom.toFunctor) a.β.hom.toNatTrans :=
    CatFiberedInGroupoids.isIso_toNatTrans a.β
  inferInstance

/-- **`CategoryTheory.DottedArrow.pasting_eq` on components**: for two dotted arrows `a` and `b`,
at each object `z`, the component of `a.β` at `j z` followed by `f` applied to the component of
`a.α` at `z` equals the same composite for `b`. -/
theorem pasting_app_eq (a b : DottedArrow x j f y γ) (z : S.val.obj) :
    a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫
        f.hom.toFunctor.map (a.α.hom.toNatTrans.app z) =
      b.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫
        f.hom.toFunctor.map (b.α.hom.toNatTrans.app z) := by
  have h := congrArg (fun t => t.hom.toNatTrans.app z) (DottedArrow.pasting_eq a b)
  change a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ 𝟙 _ ≫
      f.hom.toFunctor.map (a.α.hom.toNatTrans.app z) =
    b.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ 𝟙 _ ≫
      f.hom.toFunctor.map (b.α.hom.toNatTrans.app z) at h
  exact ((congrArg (fun t => a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ t)
      (Category.id_comp (f.hom.toFunctor.map (a.α.hom.toNatTrans.app z)))).symm.trans h).trans
    (congrArg (fun t => b.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ t)
      (Category.id_comp (f.hom.toFunctor.map (b.α.hom.toNatTrans.app z))))

/-- **Two dotted arrows connected objectwise over identities are isomorphic.** Given, for each
object `z` of the base of the square, a morphism `θ z` between the two diagonals at `z` which
lies over an identity and carries `a.β` to `b.β`, the family `θ` is automatically natural and
automatically compatible with the two `α`s, so it is an isomorphism of dotted arrows. -/
theorem nonempty_iso_of_forall_hom_isHomLift [f.hom.toFunctor.Faithful]
    (a b : DottedArrow x j f y γ)
    (h : ∀ z : T.val.obj, ∃ θ : a.a.hom.toFunctor.obj z ⟶ b.a.hom.toFunctor.obj z,
      X.val.p.IsHomLift (𝟙 (T.val.p.obj z)) θ ∧
        b.β.hom.toNatTrans.app z = a.β.hom.toNatTrans.app z ≫ f.hom.toFunctor.map θ) :
    Nonempty (a ≅ b) := by
  classical
  choose θ hθ hβ using h
  have hiso : ∀ z, IsIso (a.β.hom.toNatTrans.app z) := isIso_beta_app a
  let η : a.a ⟶ b.a := ⟨{
    app := θ
    naturality := by
      intro z z' i
      refine f.hom.toFunctor.map_injective ?_
      rw [Functor.map_comp, Functor.map_comp]
      refine (cancel_epi (a.β.hom.toNatTrans.app z)).mp ?_
      refine Eq.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ f.hom.toFunctor.map (θ z'))
            (beta_naturality a i).symm).trans (Category.assoc _ _ _))) ?_
      refine Eq.trans (congrArg (fun t => y.hom.toFunctor.map i ≫ t) (hβ z').symm) ?_
      refine Eq.trans (beta_naturality b i) ?_
      exact (congrArg (fun t => t ≫ f.hom.toFunctor.map (b.a.hom.toFunctor.map i))
        (hβ z)).trans (Category.assoc _ _ _)
    isHomLift' := hθ }⟩
  have hβ' : b.β = a.β ≫ (η ▷ f) :=
    Bicategory.InducedBicategory.hom₂_ext
      (BasedNatTrans.ext _ _ (NatTrans.ext (funext hβ)))
  have hα : a.α = (j ◁ η) ≫ b.α := by
    refine Bicategory.InducedBicategory.hom₂_ext
      (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
    funext z
    refine f.hom.toFunctor.map_injective ?_
    refine (cancel_epi (a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z))).mp ?_
    show a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫
        f.hom.toFunctor.map (a.α.hom.toNatTrans.app z) =
      a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫
        f.hom.toFunctor.map (θ (j.hom.toFunctor.obj z) ≫ b.α.hom.toNatTrans.app z)
    refine Eq.trans (pasting_app_eq a b z) ?_
    refine Eq.trans (congrArg (fun t => t ≫
      f.hom.toFunctor.map (b.α.hom.toNatTrans.app z)) (hβ (j.hom.toFunctor.obj z))) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun t => a.β.hom.toNatTrans.app (j.hom.toFunctor.obj z) ≫ t)
      (f.hom.toFunctor.map_comp (θ (j.hom.toFunctor.obj z))
        (b.α.hom.toNatTrans.app z)).symm
  exact ⟨asIso (show a ⟶ b from ⟨η, hα, hβ'⟩)⟩

/-- **Two dotted arrows connected objectwise are isomorphic**: given, for each object `z` of the
base of the square, a morphism `θ z` between the two diagonals at `z` carrying `a.β` to `b.β`,
the dotted arrows `a` and `b` are isomorphic. No verticality is required of the `θ z`. -/
theorem nonempty_iso_of_forall_hom [f.hom.toFunctor.Faithful]
    (a b : DottedArrow x j f y γ)
    (h : ∀ z : T.val.obj, ∃ θ : a.a.hom.toFunctor.obj z ⟶ b.a.hom.toFunctor.obj z,
      b.β.hom.toNatTrans.app z = a.β.hom.toNatTrans.app z ≫ f.hom.toFunctor.map θ) :
    Nonempty (a ≅ b) := by
  refine nonempty_iso_of_forall_hom_isHomLift a b fun z => ?_
  obtain ⟨θ, hθ⟩ := h z
  refine ⟨θ, ?_, hθ⟩
  have hisoz : IsIso (a.β.hom.toNatTrans.app z) := isIso_beta_app a z
  have hliftβ : Y.val.p.IsHomLift (𝟙 (T.val.p.obj z)) (a.β.hom.toNatTrans.app z) :=
    a.β.hom.isHomLift' z
  have hliftb : Y.val.p.IsHomLift (𝟙 (T.val.p.obj z)) (b.β.hom.toNatTrans.app z) :=
    b.β.hom.isHomLift' z
  have hmap : f.hom.toFunctor.map θ =
      inv (a.β.hom.toNatTrans.app z) ≫ b.β.hom.toNatTrans.app z :=
    ((IsIso.inv_comp_eq (a.β.hom.toNatTrans.app z)).mpr hθ).symm
  have hinv : Y.val.p.IsHomLift (𝟙 (T.val.p.obj z))
      (inv (a.β.hom.toNatTrans.app z)) :=
    IsHomLift.lift_id_inv_isIso Y.val.p (T.val.p.obj z) (a.β.hom.toNatTrans.app z)
  have hlift : Y.val.p.IsHomLift (𝟙 (T.val.p.obj z)) (f.hom.toFunctor.map θ) := by
    rw [hmap]
    exact IsHomLift.comp_of_lift_id Y.val.p (T.val.p.obj z)
      (inv (a.β.hom.toNatTrans.app z)) (b.β.hom.toNatTrans.app z)
  exact Functor.isHomLift_of_isHomLift_map f.hom.w _ _

/-- **The criterion needs only be checked on an essentially surjective family.** If `r` is
essentially surjective onto the base of the square, connecting morphisms carrying `a.β` to `b.β`
at the objects `r.obj z` suffice for `a` and `b` to be isomorphic. -/
theorem nonempty_iso_of_forall_hom_of_essSurj [f.hom.toFunctor.Faithful]
    {A : Type*} [Category A] (r : A ⥤ T.val.obj) [r.EssSurj]
    (a b : DottedArrow x j f y γ)
    (h : ∀ z : A, ∃ θ : a.a.hom.toFunctor.obj (r.obj z) ⟶ b.a.hom.toFunctor.obj (r.obj z),
      b.β.hom.toNatTrans.app (r.obj z) =
        a.β.hom.toNatTrans.app (r.obj z) ≫ f.hom.toFunctor.map θ) :
    Nonempty (a ≅ b) := by
  refine nonempty_iso_of_forall_hom a b fun z => ?_
  obtain ⟨z', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage r z
  obtain ⟨θ, hθ⟩ := h z'
  refine ⟨a.a.hom.toFunctor.map e.inv ≫ θ ≫ b.a.hom.toFunctor.map e.hom, ?_⟩
  refine Eq.symm ?_
  rw [Functor.map_comp, Functor.map_comp]
  refine Eq.trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (f.hom.toFunctor.map θ ≫
        f.hom.toFunctor.map (b.a.hom.toFunctor.map e.hom)))
      (beta_naturality a e.inv).symm).trans (Category.assoc _ _ _))) ?_
  refine Eq.trans (congrArg (fun t => y.hom.toFunctor.map e.inv ≫ t)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun t => t ≫ f.hom.toFunctor.map (b.a.hom.toFunctor.map e.hom))
        hθ.symm))) ?_
  refine Eq.trans (congrArg (fun t => y.hom.toFunctor.map e.inv ≫ t)
    (beta_naturality b e.hom).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ b.β.hom.toNatTrans.app z)
    ((y.hom.toFunctor.map_comp e.inv e.hom).symm.trans
      ((congrArg y.hom.toFunctor.map e.inv_hom_id).trans
        (y.hom.toFunctor.map_id z)))) ?_
  exact Category.id_comp _

end DottedArrow

end CategoryTheory

end
