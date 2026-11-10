module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories
public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksCore.Tactic.StacksAttribute

/-!
# Full faithfulness from a spanning set

An exact functor of triangulated categories having both adjoints is fully faithful as soon as it
is fully faithful on a set of objects which detects zero objects from both sides, including after
all shifts. The proof shows first that the unit of the right adjunction is an isomorphism at every
member of the spanning set, by placing its cone in the right orthogonal of the shifted span, and
then that the counit of the left adjunction is an isomorphism everywhere.

## Main results

* `AlgebraicGeometry.fullyFaithful_of_bijective_on_spanning_set`: it is enough to check full
  faithfulness on a two-sided spanning set.

## Implementation notes

Vanishing of a Hom group is expressed by `Subsingleton` for the corresponding morphism type, and
being a zero object by `CategoryTheory.Limits.IsZero`. Only pretriangulated categories are needed:
the octahedron axiom is not used. The map on shifted Hom groups is the map induced by the functor
followed by its specified comparison with the shift. Full faithfulness is returned as the
inhabited standard `CategoryTheory.Functor.FullyFaithful` structure.

## References

* [Orlov-K3, Lemma 2.15]
* [Stacks Project, Tag 0G24](https://stacks.math.columbia.edu/tag/0G24)
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

/-- Postcomposition with an isomorphism is a bijection on Hom groups. -/
private lemma bijective_postcomp_iso {C : Type*} [Category C] {A X Y : C}
    (e : X ≅ Y) : Function.Bijective (fun f : A ⟶ X ↦ f ≫ e.hom) :=
  e.homToEquiv.bijective

/-- Bijectivity of postcomposition with a fixed map is invariant under isomorphisms of the
source. -/
private lemma bijective_postcomp_source_iso {C : Type*} [Category C]
    {A A' X Y : C} (f : X ⟶ Y) (e : A ≅ A')
    (h : Function.Bijective (fun g : A' ⟶ X => g ≫ f)) :
    Function.Bijective (fun g : A ⟶ X => g ≫ f) := by
  convert (e.symm.homFromEquiv (Z := Y)).bijective.comp
      (h.comp (e.homFromEquiv (Z := X)).bijective) using 1 with g
  funext g
  simp [Iso.homFromEquiv_apply, Category.assoc]

/-- For an adjunction compatible with the shift, postcomposition with the shifted unit is
bijective as soon as the left adjoint is bijective on the corresponding shifted Hom group. -/
private lemma bijective_postcomp_shifted_unit
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    {F : C ⥤ D} {R : D ⥤ C} (adj : F ⊣ R)
    [HasShift C ℤ] [HasShift D ℤ] [F.CommShift ℤ] [R.CommShift ℤ]
    [adj.CommShift ℤ] (E E' : C) (i : ℤ)
    (h : Function.Bijective (fun f : E' ⟶ (shiftFunctor C i).obj E =>
      F.map f ≫ (F.commShiftIso i).hom.app E)) :
    Function.Bijective (fun f : E' ⟶ (shiftFunctor C i).obj E =>
      f ≫ (shiftFunctor C i).map (adj.unit.app E)) := by
  let q := F.commShiftIso i
  let r := R.commShiftIso i
  have hF : Function.Bijective (fun f : E' ⟶ (shiftFunctor C i).obj E => F.map f) :=
    ((Function.Bijective.of_comp_iff'
      (bijective_postcomp_iso (q.app E)) _).mp (by simpa [Function.comp_def] using h))
  have hR : Function.Bijective (fun f : E' ⟶ (shiftFunctor C i).obj E =>
      adj.homEquiv E' (F.obj ((shiftFunctor C i).obj E)) (F.map f)) :=
    (adj.homEquiv E' (F.obj ((shiftFunctor C i).obj E))).bijective.comp hF
  let e : R.obj (F.obj ((shiftFunctor C i).obj E)) ≅
      (shiftFunctor C i).obj ((F ⋙ R).obj E) :=
    (asIso (R.map (q.hom.app E))) ≪≫ (r.app (F.obj E))
  have h' : Function.Bijective (fun f : E' ⟶ (shiftFunctor C i).obj E =>
      adj.homEquiv E' (F.obj ((shiftFunctor C i).obj E)) (F.map f) ≫ e.hom) :=
    (bijective_postcomp_iso e).comp hR
  convert h' using 1
  · funext f
    simp only [Adjunction.homEquiv_unit]
    calc
      f ≫ (shiftFunctor C i).map (adj.unit.app E) =
          f ≫ (adj.unit.app ((shiftFunctor C i).obj E) ≫
            R.map ((F.commShiftIso i).hom.app E) ≫
              (R.commShiftIso i).hom.app (F.obj E)) := by
        rw [adj.shift_unit_app i E]
      _ = adj.unit.app E' ≫ R.map (F.map f) ≫ e.hom := by
        calc
          f ≫ adj.unit.app ((shiftFunctor C i).obj E) ≫
              R.map ((F.commShiftIso i).hom.app E) ≫
                (R.commShiftIso i).hom.app (F.obj E) =
              (adj.unit.app E' ≫ R.map (F.map f)) ≫
                R.map ((F.commShiftIso i).hom.app E) ≫
                  (R.commShiftIso i).hom.app (F.obj E) := by
            rw [← Category.assoc, ← adj.unit_naturality f]
          _ = adj.unit.app E' ≫ R.map (F.map f) ≫ e.hom := by
            dsimp [e, q, r]
            simp [Category.assoc]
    simp [Category.assoc]

/-- The objects isomorphic to a shift of a member of `S`. -/
private def shiftSpan {C : Type u} [Category.{v} C] [HasShift C ℤ]
    (S : Set C) : C → Prop := fun A =>
  ∃ E : C, E ∈ S ∧ ∃ n : ℤ, Nonempty ((shiftFunctor C n).obj E ≅ A)

/-- The shifted span of a set is invariant under all shifts. -/
private lemma shiftSpan_invariant {C : Type u} [Category.{v} C] [HasShift C ℤ]
    (S : Set C) : Stacks.Triangulated.RightOrthogonal.InvariantUnderAllShifts (shiftSpan S) := by
  rintro m A ⟨E, hE, n, ⟨e⟩⟩
  exact ⟨(shiftFunctor C (n + m)).obj E, ⟨E, hE, n + m, ⟨Iso.refl _⟩⟩,
    ⟨((shiftFunctorAdd' C n m (n + m) rfl).app E ≪≫ (shiftFunctor C m).mapIso e).symm⟩⟩

/-- Postcomposition with `f` is bijective on maps out of `A` shifted by `n` as soon as
postcomposition with the `(-n)`-shift of `f` is bijective on maps out of `A`. -/
private lemma bijective_postcomp_of_shift
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {A X Y : C} (f : X ⟶ Y) (n : ℤ)
    (h : Function.Bijective (fun g : A ⟶ X⟦-n⟧ => g ≫ f⟦-n⟧')) :
    Function.Bijective (fun g : A⟦n⟧ ⟶ X => g ≫ f) := by
  let adj := (shiftEquiv' C n (-n) (add_neg_cancel n)).toAdjunction
  let E1 := adj.homEquiv A X
  let E2 := adj.homEquiv A Y
  have key : (fun g : A⟦n⟧ ⟶ X => g ≫ f) =
      (fun g : A ⟶ Y⟦-n⟧ => E2.symm g) ∘
        (fun g : A ⟶ X⟦-n⟧ => g ≫ f⟦-n⟧') ∘
        (fun g : A⟦n⟧ ⟶ X => E1 g) := by
    funext g
    change g ≫ f = E2.symm (E1 g ≫ f⟦-n⟧')
    exact E2.eq_symm_apply.mpr (adj.homEquiv_naturality_right g f)
  rw [key]
  exact E2.symm.bijective.comp (h.comp E1.bijective)

/-- Precomposition with the `n`-shift of `f` is bijective as soon as precomposition with `f` is
bijective on maps into the `(-n)`-shift of the target. -/
private lemma bijective_precomp_shift
    {C : Type u} [Category.{v} C] [HasShift C ℤ]
    {X Y A : C} (f : X ⟶ Y) (n : ℤ)
    (h : Function.Bijective (fun g : Y ⟶ A⟦-n⟧ => f ≫ g)) :
    Function.Bijective (fun g : Y⟦n⟧ ⟶ A => f⟦n⟧' ≫ g) := by
  let adj := (shiftEquiv' C n (-n) (add_neg_cancel n)).toAdjunction
  let E1 := adj.homEquiv Y A
  let E2 := adj.homEquiv X A
  have key :
      (fun g : Y⟦n⟧ ⟶ A => f⟦n⟧' ≫ g) =
      (fun g : Y ⟶ A⟦-n⟧ => E2.symm (f ≫ g)) ∘
        (fun g : Y⟦n⟧ ⟶ A => E1 g) := by
    funext g
    change f⟦n⟧' ≫ g = E2.symm (f ≫ E1 g)
    exact E2.eq_symm_apply.mpr (adj.homEquiv_naturality_left f g)
  rw [key]
  exact E2.symm.bijective.comp (h.comp E1.bijective)

/-- An object right-orthogonal to the shifted span of `S` is zero, when `S` detects zero objects
by maps from all shifts of its members. -/
private lemma isZero_of_rightOrthogonal_shiftSpan
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : Set C) (h_from : ∀ K : C,
      (∀ E : C, E ∈ S → ∀ i : ℤ, Subsingleton (E ⟶ K⟦i⟧)) → IsZero K)
    {K : C} (horth : Stacks.Triangulated.RightOrthogonal.InRightOrthogonal (shiftSpan S) K) :
    IsZero K := by
  apply h_from K
  intro E hE i
  have hzero (f : E ⟶ K⟦i⟧) : f = 0 := by
    let adj := (shiftEquiv' C (-i) i (neg_add_cancel i)).toAdjunction
    let e := adj.homEquiv E K
    have he0 : e.symm (0 : E ⟶ K⟦i⟧) = 0 := by
      change (adj.homEquiv E K).symm
        (0 : E ⟶ (shiftEquiv' C (-i) i (neg_add_cancel i)).inverse.obj K) = 0
      rw [adj.homEquiv_counit]
      simp
    exact e.symm.injective
      ((horth (E⟦-i⟧) ⟨E, hE, -i, ⟨Iso.refl _⟩⟩ (e.symm f)).trans he0.symm)
  exact subsingleton_of_forall_eq 0 hzero

/-- If the unit of a shift-compatible adjunction is an isomorphism at `X`, it is an isomorphism at
every shift of `X`. -/
private lemma isIso_unit_shift_of_isIso
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [HasShift C ℤ] [HasShift D ℤ] {F : C ⥤ D} {R : D ⥤ C}
    (adj : F ⊣ R) [F.CommShift ℤ] [R.CommShift ℤ] [adj.CommShift ℤ]
    (X : C) (i : ℤ) [IsIso (adj.unit.app X)] :
    IsIso (adj.unit.app ((shiftFunctor C i).obj X)) := by
  let tail := R.map ((F.commShiftIso i).hom.app X) ≫
    (R.commShiftIso i).hom.app (F.obj X)
  have : IsIso tail := by infer_instance
  have : IsIso (adj.unit.app ((shiftFunctor C i).obj X) ≫ tail) := by
    rw [← adj.shift_unit_app i X]
    infer_instance
  exact IsIso.of_isIso_comp_right (adj.unit.app ((shiftFunctor C i).obj X)) tail

/-- Precomposition with the counit of the left adjunction is bijective on maps into an object at
which the unit of the right adjunction is an isomorphism. -/
private lemma bijective_precomp_leftCounit
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    {L : D ⥤ C} {F : C ⥤ D} {R : D ⥤ C}
    (adjL : L ⊣ F) (adjR : F ⊣ R) (K A : C)
    [IsIso (adjR.unit.app A)] :
    Function.Bijective (fun f : K ⟶ A => adjL.counit.app K ≫ f) := by
  let E1 := adjL.homEquiv (F.obj K) A
  let E2 := adjR.homEquiv K (F.obj A)
  have hη : Function.Bijective (fun f : K ⟶ A => f ≫ adjR.unit.app A) :=
    bijective_postcomp_iso (asIso (adjR.unit.app A))
  have key : (fun f : K ⟶ A => adjL.counit.app K ≫ f) =
      E1.symm ∘ E2.symm ∘ (fun f : K ⟶ A => f ≫ adjR.unit.app A) := by
    funext f
    apply E1.injective
    simp only [Function.comp_apply]
    calc
      E1 (adjL.counit.app K ≫ f) = F.map f := by
        change adjL.homEquiv (F.obj K) A (adjL.counit.app K ≫ f) = F.map f
        rw [Adjunction.homEquiv_unit]
        simp [Functor.map_comp]
      _ = E2.symm (f ≫ adjR.unit.app A) := by
        change F.map f = (adjR.homEquiv K (F.obj A)).symm (f ≫ adjR.unit.app A)
        rw [Adjunction.homEquiv_counit]
        simp [Functor.map_comp, Category.assoc]
      _ = E1 (E1.symm (E2.symm (f ≫ adjR.unit.app A))) := (E1.apply_symm_apply _).symm
  rw [key]
  exact E1.symm.bijective.comp (E2.symm.bijective.comp hη)

/-- The unit of a shift-compatible adjunction is an isomorphism at every member of a set `S`
detecting zero objects by maps from its shifts, provided `F` is bijective on all shifted Hom groups
between members of `S`. -/
private lemma isIso_unit_app_of_mem_spanning_set
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ]
    {F : C ⥤ D} {R : D ⥤ C} (adjR : F ⊣ R) [F.CommShift ℤ] [R.CommShift ℤ] [adjR.CommShift ℤ]
    (S : Set C)
    (h_from : ∀ K : C,
      (∀ E : C, E ∈ S → ∀ i : ℤ, Subsingleton (E ⟶ K⟦i⟧)) → IsZero K)
    (h_bijective : ∀ E : C, E ∈ S → ∀ E' : C, E' ∈ S → ∀ i : ℤ,
      Function.Bijective (fun f : E ⟶ E'⟦i⟧ ↦
        F.map f ≫ (F.commShiftIso i).hom.app E'))
    {E : C} (hE : E ∈ S) : IsIso (adjR.unit.app E) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (adjR.unit.app E)
  let T : Triangle C := Triangle.mk (adjR.unit.app E) g h
  have hbij : ∀ A : C, shiftSpan S A →
      Function.Bijective (fun f : A ⟶ T.obj₁ => f ≫ T.mor₁) := by
    rintro A ⟨E', hE', n, ⟨e⟩⟩
    exact bijective_postcomp_source_iso _ e.symm
      (bijective_postcomp_of_shift _ n
        (bijective_postcomp_shifted_unit adjR E E' (-n) (h_bijective E' hE' E hE (-n))))
  have horth : Stacks.Triangulated.RightOrthogonal.InRightOrthogonal (shiftSpan S) Z :=
    (Stacks.Triangulated.RightOrthogonal.inRightOrthogonal_iff_postcomp_bijective
      (shiftSpan S) (shiftSpan_invariant S) T hT).2 hbij
  exact (T.isZero₃_iff_isIso₁ hT).mp (isZero_of_rightOrthogonal_shiftSpan S h_from horth)

/-- The counit of the left adjunction is an isomorphism at every object, provided the unit of the
right adjunction is an isomorphism on a set `S` detecting zero objects by maps to its shifts. -/
private lemma isIso_leftCounit_app_of_isIso_unit
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [HasShift D ℤ]
    {L : D ⥤ C} {F : C ⥤ D} {R : D ⥤ C} (adjL : L ⊣ F) (adjR : F ⊣ R)
    [F.CommShift ℤ] [R.CommShift ℤ] [adjR.CommShift ℤ] (S : Set C)
    (h_to : ∀ K : C,
      (∀ E : C, E ∈ S → ∀ i : ℤ, Subsingleton (K ⟶ E⟦i⟧)) → IsZero K)
    (hUnit : ∀ E : C, E ∈ S → IsIso (adjR.unit.app E)) (K : C) :
    IsIso (adjL.counit.app K) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (adjL.counit.app K)
  let T : Triangle C := Triangle.mk (adjL.counit.app K) g h
  have hzero : ∀ E : C, E ∈ S → ∀ i : ℤ, ∀ f : Z ⟶ E⟦i⟧, f = 0 := by
    intro E hE i f
    have := hUnit E hE
    have := isIso_unit_shift_of_isIso adjR E i
    have := isIso_unit_shift_of_isIso adjR ((shiftFunctor C i).obj E) (-1)
    have hpreEi := bijective_precomp_leftCounit adjL adjR K ((shiftFunctor C i).obj E)
    have hpreShift := bijective_precomp_shift (adjL.counit.app K) 1
      (bijective_precomp_leftCounit adjL adjR K
        ((shiftFunctor C (-1 : ℤ)).obj ((shiftFunctor C i).obj E)))
    have h12 : adjL.counit.app K ≫ T.mor₂ = 0 := by
      simpa [T] using comp_distTriang_mor_zero₁₂ T hT
    have h31 : T.mor₃ ≫ (shiftFunctor C 1).map (adjL.counit.app K) = 0 := by
      simpa [T] using comp_distTriang_mor_zero₃₁ T hT
    have hker : T.mor₂ ≫ f = 0 := by
      apply hpreEi.injective
      change adjL.counit.app K ≫ (T.mor₂ ≫ f) = adjL.counit.app K ≫ 0
      rw [← Category.assoc, h12, zero_comp, comp_zero]
    obtain ⟨q, hq⟩ := T.yoneda_exact₃ hT f hker
    obtain ⟨q', hq'⟩ := hpreShift.surjective q
    calc
      f = T.mor₃ ≫ q := hq
      _ = T.mor₃ ≫ ((shiftFunctor C (1 : ℤ)).map (adjL.counit.app K) ≫ q') := by
        rw [← hq']
      _ = 0 := by rw [← Category.assoc, h31, zero_comp]
  exact (T.isZero₃_iff_isIso₁ hT).mp
    (h_to Z fun E hE i => subsingleton_of_forall_eq 0 (hzero E hE i))

/-- **Stacks Project, Tag 0G24.** Let `F : C ⥤ D` be an exact functor of
pre-triangulated categories which has both adjoints. If a set `S` detects zero objects by maps
from and to all shifts of its members, and `F` induces bijections on all shifted Hom sets between
members of `S`, then `F` is fully faithful. -/
@[stacks 0G24]
public theorem fullyFaithful_of_bijective_on_spanning_set
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [F.IsLeftAdjoint] [F.IsRightAdjoint] (S : Set C)
    (h_from : ∀ K : C,
      (∀ E : C, E ∈ S → ∀ i : ℤ, Subsingleton (E ⟶ K⟦i⟧)) → IsZero K)
    (h_to : ∀ K : C,
      (∀ E : C, E ∈ S → ∀ i : ℤ, Subsingleton (K ⟶ E⟦i⟧)) → IsZero K)
    (h_bijective : ∀ E : C, E ∈ S → ∀ E' : C, E' ∈ S → ∀ i : ℤ,
      Function.Bijective (fun f : E ⟶ E'⟦i⟧ ↦
        F.map f ≫ (F.commShiftIso i).hom.app E')) :
    Nonempty F.FullyFaithful := by
  let R := F.rightAdjoint
  let L := F.leftAdjoint
  let adjR : F ⊣ R := Adjunction.ofIsLeftAdjoint F
  let adjL : L ⊣ F := Adjunction.ofIsRightAdjoint F
  let : R.CommShift ℤ := adjR.rightAdjointCommShift ℤ
  let : adjR.CommShift ℤ := adjR.commShift_of_leftAdjoint ℤ
  have := isIso_leftCounit_app_of_isIso_unit adjL adjR S h_to
    fun _ hE => isIso_unit_app_of_mem_spanning_set adjR S h_from h_bijective hE
  have : IsIso adjL.counit := NatIso.isIso_of_isIso_app _
  exact ⟨adjL.fullyFaithfulROfIsIsoCounit⟩

end AlgebraicGeometry
