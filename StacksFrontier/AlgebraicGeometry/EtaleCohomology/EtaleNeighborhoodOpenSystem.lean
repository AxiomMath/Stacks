module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationBaseChangeLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictHenselizationOpenFactor
public import Mathlib.CategoryTheory.Presentable.Directed

/-!
# The étale neighbourhoods of a geometric point over an open neighbourhood of it

Let `s` be a geometric point of a scheme `S` and `U` an open subscheme of `S` containing the
image of `s`. The affine étale neighbourhoods of `s` whose structure morphism lands in `U` form a
small cofiltered category, initial among all étale neighbourhoods of `s`, so the strict
henselization `Spec(𝒪^{sh}_{S,s})` is also their limit, now as a scheme over `U`; and that
category is in turn the target of an initial functor from a directed partially ordered set
([Stacks, Tag 0032]).

This is the shape in which [Stacks, Tag 03Q6] — a directed system of algebras over a ring `A` —
applies to the strict henselization, for `U = Spec A` affine.

## Main definitions

* `AlgebraicGeometry.etaleNeighborhoodOpenIndex` — the small affine étale neighbourhoods of `s`
  lying over `U`.
* `AlgebraicGeometry.etaleNeighborhoodOpenInclusion` — its inclusion into all étale
  neighbourhoods, which is initial.
* `AlgebraicGeometry.etaleNeighborhoodOpenOverDiagram` — those neighbourhoods as schemes over `U`.
* `AlgebraicGeometry.strictHenselizationOpenOverCone` — the strict henselization over `U`, as a
  cone on that diagram.

## Main results

* `AlgebraicGeometry.exists_etaleNeighborhood_range_subset` — every étale neighbourhood of `s` is
  refined by one lying over `U`.
* `AlgebraicGeometry.isLimitStrictHenselizationOpenOverCone` — the strict henselization is the
  limit, over `U`, of the étale neighbourhoods lying over `U`.
* `AlgebraicGeometry.exists_directed_etaleNeighborhoodOpenIndex` — an initial functor from the
  opposite of a nonempty directed partial order into those neighbourhoods.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (U : S.Opens) (hU : s.hom (closedPoint s.residueField) ∈ U)

/-- The structure morphism to `S` of an étale neighbourhood of `s`. -/
abbrev etaleNeighborhoodStructureMap (V : (geometricPointFiber B S hS s).Elements) :
    (etaleNeighborhoodDiagram B S hS s).obj V ⟶ S :=
  (etaleNeighborhoodStructureMaps B S hS s).app V

include hU in
/-- **Every étale neighbourhood of `s` is refined by one lying over `U`**: restrict it to an
affine open of the preimage of `U` through which the lift of `s` factors. -/
theorem exists_etaleNeighborhood_range_subset (W : (geometricPointFiber B S hS s).Elements) :
    ∃ V : (geometricPointFiber B S hS s).Elements,
      Set.range (etaleNeighborhoodStructureMap B S hS s V) ⊆ U ∧ Nonempty (V ⟶ W) := by
  let w : (SmallEtale.toScheme B S hS).obj W.1 ⟶ S := B.inclusion.map W.1.obj.hom
  have hx : W.2.1 (default : s.source) ∈ w ⁻¹ᵁ U := by
    show (W.2.1 ≫ w) (default : s.source) ∈ U
    have h : W.2.1 ≫ w = s.hom := W.2.2
    rw [h, Subsingleton.elim (default : s.source) (closedPoint s.residueField)]
    exact hU
  obtain ⟨R, j, hj, y, hy, hjU⟩ : ∃ (R : CommRingCat.{u})
      (j : Spec R ⟶ (SmallEtale.toScheme B S hS).obj W.1)
      (_ : IsOpenImmersion j) (y : s.source ⟶ Spec R), y ≫ j = W.2.1 ∧
        Set.range j ⊆ w ⁻¹ᵁ U := by
    obtain ⟨R, j, _, hj, hjU⟩ := Scheme.exists_affine_mem_range_and_range_subset hx
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j W.2.1 ?_, hjU⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  have hjf : Etale (j ≫ B.inclusion.map W.1.obj.hom) := inferInstance
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ B.inclusion.map W.1.obj.hom)).trans_lt hS
  let V : SmallEtale B S hS :=
    ⟨Over.mk (ObjectProperty.homMk (j ≫ B.inclusion.map W.1.obj.hom) :
      B.obj (Spec R) hR ⟶ B.obj S hS), hjf⟩
  have hyS : y ≫ B.inclusion.map V.obj.hom = s.hom := by
    show y ≫ (j ≫ B.inclusion.map W.1.obj.hom) = s.hom
    rw [← Category.assoc, hy]
    exact W.2.2
  refine ⟨⟨V, ⟨y, hyS⟩⟩, ?_, ⟨⟨ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk j) ?_), ?_⟩⟩⟩
  · rintro _ ⟨z, rfl⟩
    exact hjU ⟨z, rfl⟩
  · apply ObjectProperty.hom_ext
    rfl
  · exact Subtype.ext hy

/-- The members of the chosen small affine family of étale neighbourhoods of `s` whose structure
morphism lands in `U`. -/
def etaleNeighborhoodOpenProperty : ObjectProperty (etaleNeighborhoodAffineIndex B S hS s) :=
  fun a => Set.range (etaleNeighborhoodStructureMap B S hS s
    ((etaleNeighborhoodAffineInclusion B S hS s).obj a)) ⊆ U

/-- **The small affine étale neighbourhoods of `s` lying over `U`.** -/
abbrev etaleNeighborhoodOpenIndex : Type u :=
  (etaleNeighborhoodOpenProperty B S hS s U).FullSubcategory

/-- The inclusion of the affine étale neighbourhoods lying over `U` into all étale
neighbourhoods of `s`. -/
abbrev etaleNeighborhoodOpenInclusion :
    etaleNeighborhoodOpenIndex B S hS s U ⥤ (geometricPointFiber B S hS s).Elements :=
  (etaleNeighborhoodOpenProperty B S hS s U).ι ⋙ etaleNeighborhoodAffineInclusion B S hS s

/-- The structure morphism of a refinement lands in the image of the refined neighbourhood. -/
theorem range_etaleNeighborhoodStructureMaps_subset
    {V W : (geometricPointFiber B S hS s).Elements} (g : V ⟶ W) :
    Set.range (etaleNeighborhoodStructureMap B S hS s V) ⊆
      Set.range (etaleNeighborhoodStructureMap B S hS s W) := by
  have h := (etaleNeighborhoodStructureMaps B S hS s).naturality g
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
  rintro _ ⟨z, rfl⟩
  refine ⟨(etaleNeighborhoodDiagram B S hS s).map g z, ?_⟩
  show _ = ((etaleNeighborhoodStructureMaps B S hS s).app V) z
  rw [← h]
  rfl

include hU in
/-- Every étale neighbourhood of `s` is refined by an affine one lying over `U`. -/
theorem etaleNeighborhoodOpenIndex_weaklyInitial (W : (geometricPointFiber B S hS s).Elements) :
    ∃ a, Nonempty ((etaleNeighborhoodOpenInclusion B S hS s U).obj a ⟶ W) := by
  obtain ⟨V, hV, ⟨g⟩⟩ := exists_etaleNeighborhood_range_subset B S hS s U hU W
  obtain ⟨a, ⟨g'⟩⟩ := etaleNeighborhoodAffineIndex_weaklyInitial B S hS s V
  exact ⟨⟨a, (range_etaleNeighborhoodStructureMaps_subset B S hS s g').trans hV⟩, ⟨g' ≫ g⟩⟩

include hU in
/-- The affine étale neighbourhoods of `s` lying over `U` form a cofiltered category. -/
theorem isCofiltered_etaleNeighborhoodOpenIndex :
    IsCofiltered (etaleNeighborhoodOpenIndex B S hS s U) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (etaleNeighborhoodOpenInclusion B S hS s U)
    (etaleNeighborhoodOpenIndex_weaklyInitial B S hS s U hU)

include hU in
/-- The inclusion of the affine étale neighbourhoods lying over `U` is initial. -/
theorem initial_etaleNeighborhoodOpenInclusion :
    (etaleNeighborhoodOpenInclusion B S hS s U).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    (etaleNeighborhoodOpenInclusion B S hS s U)
    (etaleNeighborhoodOpenIndex_weaklyInitial B S hS s U hU)

/-! ### The neighbourhoods and the strict henselization over `U` -/

/-- The structure morphism to `U` of an affine étale neighbourhood lying over `U`. -/
def etaleNeighborhoodToOpen (a : etaleNeighborhoodOpenIndex B S hS s U) :
    (etaleNeighborhoodDiagram B S hS s).obj ((etaleNeighborhoodOpenInclusion B S hS s U).obj a) ⟶
      U :=
  IsOpenImmersion.lift U.ι (etaleNeighborhoodStructureMap B S hS s
    ((etaleNeighborhoodOpenInclusion B S hS s U).obj a)) (by rw [Scheme.Opens.range_ι]; exact a.2)

/-- The structure morphism to `U` followed by the inclusion `U.ι` is the structure morphism to
`S`. -/
@[reassoc (attr := simp)]
theorem etaleNeighborhoodToOpen_ι (a : etaleNeighborhoodOpenIndex B S hS s U) :
    etaleNeighborhoodToOpen B S hS s U a ≫ U.ι =
      etaleNeighborhoodStructureMap B S hS s
        ((etaleNeighborhoodOpenInclusion B S hS s U).obj a) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The structure morphisms to `U`, as a natural transformation to the constant functor. -/
def etaleNeighborhoodOpenStructureMaps :
    etaleNeighborhoodOpenInclusion B S hS s U ⋙ etaleNeighborhoodDiagram B S hS s ⟶
      (Functor.const (etaleNeighborhoodOpenIndex B S hS s U)).obj (U : Scheme.{u}) where
  app a := etaleNeighborhoodToOpen B S hS s U a
  naturality a b g := by
    rw [← cancel_mono U.ι]
    have h := (etaleNeighborhoodStructureMaps B S hS s).naturality
      ((etaleNeighborhoodOpenInclusion B S hS s U).map g)
    simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
      Functor.comp_obj, Functor.comp_map, Category.assoc, etaleNeighborhoodToOpen_ι] using h

/-- **The affine étale neighbourhoods of `s` lying over `U`, as a diagram of schemes over `U`.** -/
abbrev etaleNeighborhoodOpenOverDiagram :
    etaleNeighborhoodOpenIndex B S hS s U ⥤ Over (U : Scheme.{u}) :=
  Over.lift (etaleNeighborhoodOpenInclusion B S hS s U ⋙ etaleNeighborhoodDiagram B S hS s)
    (etaleNeighborhoodOpenStructureMaps B S hS s U)

/-- The strict henselization, cut down to the affine neighbourhoods lying over `U`. -/
abbrev strictHenselizationOpenCone :
    Cone (etaleNeighborhoodOpenInclusion B S hS s U ⋙ etaleNeighborhoodDiagram B S hS s) :=
  (strictHenselizationCone B S hS s).whisker (etaleNeighborhoodOpenInclusion B S hS s U)

include hU in
/-- The strict henselization is the limit of the affine étale neighbourhoods lying over `U`. -/
def isLimitStrictHenselizationOpenCone :
    IsLimit (strictHenselizationOpenCone B S hS s U) :=
  haveI := initial_etaleNeighborhoodOpenInclusion B S hS s U hU
  (Functor.Initial.isLimitWhiskerEquiv (etaleNeighborhoodOpenInclusion B S hS s U) _).symm
    (strictHenselizationConeIsLimit B S hS s)

/-- The legs of the strict henselization cone, followed by the structure morphisms to `U`, are
the factorization of the strict henselization through `U`. -/
theorem strictHenselizationOpenCone_π_comp (a : etaleNeighborhoodOpenIndex B S hS s U) :
    (strictHenselizationOpenCone B S hS s U).π.app a ≫
        (etaleNeighborhoodOpenStructureMaps B S hS s U).app a =
      strictHenselizationToOpen B S hS s U hU := by
  refine Mono.right_cancellation (f := U.ι) _ _ ?_
  show ((strictHenselizationOpenCone B S hS s U).π.app a ≫
    etaleNeighborhoodToOpen B S hS s U a) ≫ U.ι = _
  rw [Category.assoc, etaleNeighborhoodToOpen_ι]
  exact (strictHenselizationCone_π_comp_hom_eq B S hS s _).trans
    (strictHenselizationToOpen_ι B S hS s U hU).symm

/-- **The strict henselization as a cone, over `U`, on the affine étale neighbourhoods of `s`
lying over `U`.** -/
abbrev strictHenselizationOpenOverCone : Cone (etaleNeighborhoodOpenOverDiagram B S hS s U) :=
  Over.liftCone _ (etaleNeighborhoodOpenStructureMaps B S hS s U)
    (strictHenselizationOpenCone B S hS s U) (strictHenselizationToOpen B S hS s U hU)
    (strictHenselizationOpenCone_π_comp B S hS s U hU)

/-- **The strict henselization is the limit, over `U`, of the affine étale neighbourhoods of `s`
lying over `U`.** -/
def isLimitStrictHenselizationOpenOverCone :
    IsLimit (strictHenselizationOpenOverCone B S hS s U hU) :=
  haveI := isCofiltered_etaleNeighborhoodOpenIndex B S hS s U hU
  haveI : Nonempty (etaleNeighborhoodOpenIndex B S hS s U) := IsCofiltered.nonempty
  Over.isLimitLiftCone _ _ _ _ _ (isLimitStrictHenselizationOpenCone B S hS s U hU)

include hU in
/-- **[Stacks, Tag 0032] for the neighbourhoods over `U`**: there is a nonempty directed partial
order `α` and an initial functor `αᵒᵖ ⥤` (the affine étale neighbourhoods of `s` over `U`). -/
theorem exists_directed_etaleNeighborhoodOpenIndex :
    ∃ (α : Type u) (_ : PartialOrder α) (_ : IsDirected α (· ≤ ·)) (_ : Nonempty α)
      (F : αᵒᵖ ⥤ etaleNeighborhoodOpenIndex B S hS s U), F.Initial := by
  have := isCofiltered_etaleNeighborhoodOpenIndex B S hS s U hU
  obtain ⟨α, _, _, _, F, _⟩ :=
    IsFiltered.exists_directed (etaleNeighborhoodOpenIndex B S hS s U)ᵒᵖ
  exact ⟨α, _, inferInstance, inferInstance, F.leftOp, inferInstance⟩

end AlgebraicGeometry

end
