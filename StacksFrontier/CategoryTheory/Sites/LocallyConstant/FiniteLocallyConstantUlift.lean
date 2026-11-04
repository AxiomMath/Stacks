module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoefficientUniverseLiftEssImage
public import Mathlib.Data.Fintype.Shrink

/-!
# Finite locally constant abelian sheaves and the universe lift of the coefficients

Let `(C, J)` be a site. This file compares finite local constancy of abelian sheaves at two
coefficient universes `AddCommGrpCat.{w}` and `AddCommGrpCat.{max w t}`, along the universe lift
`sheafCompose J AddCommGrpCat.uliftFunctor`.

* A finite abelian group is small, so the constant sheaf on it is the universe lift of a constant
  sheaf with finite value one universe down.
* Hence finite local constancy reflects along the universe lift, and a finite locally constant
  sheaf at the large universe has `w`-small groups of sections as soon as the site is `w`-small.
* A sheaf whose sections over the objects of a cover-dense subcategory are small has small
  sections everywhere.

## Main results

* `Stacks.ConstantSheaf.preservesSheafification_uliftFunctor_of_max`: the universe lift from
  the size `max u₁ v₁` of the site preserves sheafification.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_of_sheafCompose_uliftFunctor`: finite local
  constancy reflects along the universe lift.
* `Stacks.ConstantSheaf.small_of_isFiniteLocallyConstant`: a finite locally constant sheaf has
  small sections.
* `Stacks.ConstantSheaf.small_of_isCoverDense`: smallness of sections is detected on a
  cover-dense subcategory.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v₁ u₁ v₂ u₂

namespace Stacks.ConstantSheaf

/-- **The universe lift of abelian groups from the size of the site preserves sheafification.**
On a site `C : Type u₁` with morphisms in `Type v₁`, the plus construction computes
sheafification at both coefficient universes `max u₁ v₁` and `max u₁ v₁ t`; the forgetful functor
of the larger one preserves the filtered colimits of the size of the site. -/
theorem preservesSheafification_uliftFunctor_of_max {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, max u₁ v₁} := by
  have : PreservesFilteredColimitsOfSize.{max u₁ v₁, max u₁ v₁}
      (forget AddCommGrpCat.{max u₁ v₁ t}) :=
    preservesFilteredColimitsOfSize_shrink.{max u₁ v₁, t, max u₁ v₁, t} _
  exact GrothendieckTopology.instPreservesSheafification J _

/-- A `w`-small abelian group at the universe `max w t` is the universe lift of its shrinking. -/
def uliftShrinkIso (E : AddCommGrpCat.{max w t}) [Small.{w} E] :
    AddCommGrpCat.uliftFunctor.{t, w}.obj (AddCommGrpCat.of (Shrink.{w} E)) ≅ E :=
  (AddEquiv.ulift.trans Shrink.addEquiv).toAddCommGrpIso

/-- Sections of isomorphic abelian sheaves are small together. -/
theorem small_obj_of_iso {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {F G : Sheaf J AddCommGrpCat.{t}} (e : F ≅ G) (U : Cᵒᵖ) (h : Small.{w} (G.obj.obj U)) :
    Small.{w} (F.obj.obj U) :=
  (small_congr (((sheafToPresheaf J _).mapIso e).app U).addCommGroupIsoToAddEquiv.toEquiv).2 h

section

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

section Constant

variable [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{max w t}]
  [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, w}]

/-- **The constant sheaf on a small group is a universe lift**: the constant sheaf on `E` is the
universe lift of the constant sheaf on the shrinking of `E`. -/
def constantSheafUliftShrinkIso (E : AddCommGrpCat.{max w t}) [Small.{w} E] :
    (sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj
        ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (Shrink.{w} E))) ≅
      (constantSheaf J AddCommGrpCat.{max w t}).obj E :=
  (constantCommuteCompose J AddCommGrpCat.uliftFunctor.{t, w}).app _ ≪≫
    (constantSheaf J AddCommGrpCat.{max w t}).mapIso (uliftShrinkIso E)

end Constant

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max w t}]
  [∀ U : C, (J.over U).PreservesSheafification AddCommGrpCat.uliftFunctor.{t, w}]

/-- **Finite local constancy reflects along the universe lift.** If the universe lift of an
abelian sheaf `H` is finite locally constant, so is `H`: on a trivializing covering the finite
constant value is the lift of its shrinking, and the lift of sheaves is fully faithful. -/
theorem isFiniteLocallyConstant_of_sheafCompose_uliftFunctor (H : Sheaf J AddCommGrpCat.{w})
    (hH : IsFiniteLocallyConstant J
      ((sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj H)) :
    IsFiniteLocallyConstant J H where
  exists_finite_cover U := by
    obtain ⟨I, X, f, hf, h⟩ := hH.exists_finite_cover U
    refine ⟨I, X, f, hf, fun i ↦ ?_⟩
    obtain ⟨E, hE, ⟨e⟩⟩ := h i
    have : Finite E := hE
    refine ⟨AddCommGrpCat.of (Shrink.{w} E), inferInstance, ⟨?_⟩⟩
    exact (sheafCompose (J.over (X i)) AddCommGrpCat.uliftFunctor.{t, w}).preimageIso
      (constantSheafUliftShrinkIso.{w, t} (J.over (X i)) E ≪≫ e)

/-- Sections of an abelian sheaf over `V` are determined by their restrictions along a family of
arrows generating a covering sieve. -/
private theorem injective_restrict_of_generate_mem {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (F : Sheaf J AddCommGrpCat.{t}) {V : C} {ι : Type*}
    (Y : ι → C) (g : ∀ i, Y i ⟶ V) (hg : Sieve.generate (Presieve.ofArrows Y g) ∈ J V) :
    Function.Injective fun (x : F.obj.obj (op V)) i ↦ F.obj.map (g i).op x := fun x y hxy ↦ by
  refine (Presieve.isSeparatedFor_iff_generate.2
    (((isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose J (forget AddCommGrpCat.{t})).obj F).property).isSeparated _ hg)).ext
    fun Z h hh ↦ ?_
  obtain ⟨i⟩ := hh
  exact congrFun hxy i

/-- **A finite locally constant abelian sheaf has small sections.** Its sections over `U` inject
into the product, over a trivializing covering indexed by a `w`-small type, of the sections over
its members; there the sheaf is constant on a finite group, hence the universe lift of a sheaf at
the universe `w`. -/
theorem small_of_isFiniteLocallyConstant [UnivLE.{max u₁ v₁, w}]
    (F : Sheaf J AddCommGrpCat.{max w t}) (hF : IsFiniteLocallyConstant J F) (U : C) :
    Small.{w} (F.obj.obj (op U)) := by
  obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
  have hX : ∀ i, Small.{w} (F.obj.obj (op (X i))) := fun i ↦ by
    obtain ⟨E, hE, ⟨e⟩⟩ := h i
    have : Finite E := hE
    exact small_obj_of_iso (constantSheafUliftShrinkIso.{w, t} (J.over (X i)) E ≪≫ e).symm
      (op (Over.mk (𝟙 (X i))))
      ⟨⟨_, ⟨Equiv.ulift⟩⟩⟩
  exact small_of_injective (injective_restrict_of_generate_mem F X f hf)

end

/-- **Smallness of sections is detected on a cover-dense subcategory.** If the sections of an
abelian sheaf over the images of the objects of a cover-dense functor `G` are small, so are all
its sections: those over `V` inject into the product of the sections over all `G W ⟶ V`. -/
theorem small_of_isCoverDense {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) (K : GrothendieckTopology D) [G.IsCoverDense K] [UnivLE.{max u₁ v₂, w}]
    (F : Sheaf K AddCommGrpCat.{t}) (hF : ∀ W : C, Small.{w} (F.obj.obj (op (G.obj W))))
    (V : D) : Small.{w} (F.obj.obj (op V)) := by
  let R : Presieve V := Presieve.ofArrows (fun p : Σ W : C, G.obj W ⟶ V ↦ G.obj p.1)
    (fun p ↦ p.2)
  have hR : Sieve.generate R ∈ K V := by
    refine K.superset_covering ?_ (G.is_cover_of_isCoverDense K V)
    rintro Y f ⟨h⟩
    exact ⟨G.obj h.obj, h.lift, h.map,
      Presieve.ofArrows.mk (Y := fun p : Σ W : C, G.obj W ⟶ V ↦ G.obj p.1) (f := fun p ↦ p.2)
        ⟨h.obj, h.map⟩, h.fac⟩
  exact small_of_injective
    (injective_restrict_of_generate_mem F (fun p : Σ W : C, G.obj W ⟶ V ↦ G.obj p.1)
      (fun p ↦ p.2) hR)

end Stacks.ConstantSheaf
