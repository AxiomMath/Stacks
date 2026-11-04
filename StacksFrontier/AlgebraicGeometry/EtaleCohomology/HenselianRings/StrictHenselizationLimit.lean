module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeHenselization
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber

/-!
# The strict henselization as the limit of the étale neighborhoods

Let `B` be a big étale site containing a scheme `S` and let `s` be a geometric point of `S`. The
étale local ring at `s` is by definition the colimit of the rings of global functions over the
étale neighborhoods of `s`, so its spectrum — the strict henselization of `S` at `s` — ought to
be the limit of those neighborhoods in the category of schemes. This file proves that.

The point of the statement is that it converts information about the strict henselization into
information at a single étale neighborhood: a morphism between base changes to the limit of a
cofiltered inverse system of schemes with affine transition morphisms descends to one of the
stages, and two morphisms that agree after base change to the limit already agree at a stage.
That is Stacks Tag 01ZM parts (2) and (3), and both are stated for an *essentially small* index
category. So the limit is also exhibited over a small cofinal family of affine neighborhoods,
which is the form those results consume.

## Main definitions

* `AlgebraicGeometry.etaleNeighborhoodDiagram` is the diagram of underlying schemes of the étale
  neighborhoods of a geometric point, and `AlgebraicGeometry.etaleNeighborhoodSections` the
  associated diagram of rings of global functions, whose colimit is the étale local ring.
* `AlgebraicGeometry.geometricPointBaseNeighborhood` is the base itself, carrying the identity
  structure morphism, as an étale neighborhood of the point.
* `AlgebraicGeometry.etaleNeighborhoodAffineIndex` is a small cofinal family of affine étale
  neighborhoods, included by `AlgebraicGeometry.etaleNeighborhoodAffineInclusion` and giving the
  subdiagram `AlgebraicGeometry.etaleNeighborhoodAffineDiagram`.
* `AlgebraicGeometry.strictHenselizationCone` is the cone on the neighborhood diagram with vertex
  the strict henselization, and `AlgebraicGeometry.strictHenselizationAffineCone` its
  restriction to the small affine family.
* `AlgebraicGeometry.strictHenselizationConeToBase` is the leg of the cone at the base, a
  morphism from the strict henselization to `S`.

## Main results

* `AlgebraicGeometry.exists_affine_etaleNeighborhood`: every étale neighborhood of a geometric
  point is refined by an affine one.
* `AlgebraicGeometry.isTerminal_geometricPointBaseNeighborhood`: the base is the terminal étale
  neighborhood, so the leg of a cone at it is the only morphism to `S` the cone determines, and
  `AlgebraicGeometry.strictHenselizationCone_π_comp_hom` says every other leg factors through it.
* `AlgebraicGeometry.hasLimit_etaleNeighborhoodDiagram`: the neighborhood diagram has a limit.
* `AlgebraicGeometry.etaleNeighborhoodAffineLimitRingEquiv`: global functions on the limit of the
  small affine family are the étale local ring.
* `AlgebraicGeometry.strictHenselizationConeIsLimit` and
  `AlgebraicGeometry.strictHenselizationAffineConeIsLimit`: **the strict henselization is the
  limit of the étale neighborhoods**, over the whole neighborhood category and over the small
  affine family.
* `AlgebraicGeometry.etaleNeighborhoodAffineLimitSectionsRingCatIso_π_appTop`: restricting a
  global function along a limit projection and reading it in the étale local ring is the colimit
  structure map of the sections diagram. With
  `AlgebraicGeometry.strictHenselizationAffineCone_π_app`, which writes each leg of the affine
  cone as that limit projection preceded by the identification of the strict henselization with
  the limit, this computes the cone on sections.

## Implementation notes

The neighborhood category is cofiltered but it is not small: its objects live one universe above
the schemes, and their underlying schemes are not affine. Both problems are solved at once by
passing to a small cofinal family of *affine* neighborhoods, which exists because every étale
neighborhood contains an affine open through which the point factors, and because the
neighborhood category is initially small at the universe of the schemes
(`AlgebraicGeometry.geometricPointFiber_initiallySmall`). Over such a family the transition
morphisms are morphisms of affine schemes, hence affine, so the limit exists
(`AlgebraicGeometry.hasLimit_of_isCofiltered_of_isAffineHom`) and global sections take it to the
colimit of the sections (`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`). Cofinality then
transports both the limit and the colimit back to the whole neighborhood category.

The sections diagram is `CommRingCat`-valued while the étale local ring is a colimit in
`RingCat`. The two colimits agree because the forgetful functor `CommRingCat ⥤ RingCat`
preserves filtered colimits; that is available only for a small index, which is a second reason
to compute over the small affine family.

The leg of the cone at the base is **not** proved here to agree with
`AlgebraicGeometry.strictHenselizationToBase`, the structure morphism built from the
ordinary-to-étale germ map in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SchemeHenselization`. Both are
morphisms from the spectrum of the étale local ring to `S`. **They are identified**, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationConeBase`, by
`AlgebraicGeometry.strictHenselizationConeToBase_eq` — so a consumer phrased in terms of
`strictHenselizationToBase`, for instance
`AlgebraicGeometry.finite_baseChange_strictHenselization_decomposition`, can use the cone built
here directly. That file also records the leg identity on global functions,
`strictHenselizationCone_π_appTop`, which is the germ computation the identification rests on.

## References

* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- The diagram of étale neighborhoods of a geometric point, sending a neighborhood to its
underlying scheme. -/
abbrev etaleNeighborhoodDiagram : (geometricPointFiber B S hS s).Elements ⥤ Scheme.{u} :=
  CategoryOfElements.π (geometricPointFiber B S hS s) ⋙ SmallEtale.toScheme B S hS

/-- The diagram of rings of global functions on the étale neighborhoods of a geometric point.
Its colimit is the étale local ring. -/
abbrev etaleNeighborhoodSections :
    (geometricPointFiber B S hS s).Elementsᵒᵖ ⥤ CommRingCat.{u} :=
  (etaleNeighborhoodDiagram B S hS s).op ⋙ Scheme.Γ

/-! ### The base as the terminal neighborhood -/

/-- The base, with its identity structure morphism and the geometric point itself as the chosen
lift, as an étale neighborhood of that point. -/
def geometricPointBaseNeighborhood : (geometricPointFiber B S hS s).Elements :=
  ⟨⟨Over.mk (𝟙 (B.obj S hS)), (inferInstance : Etale (𝟙 S))⟩, ⟨s.hom, by simp⟩⟩

/-- The underlying scheme of the base neighborhood is the base. -/
theorem etaleNeighborhoodDiagram_obj_geometricPointBaseNeighborhood :
    (etaleNeighborhoodDiagram B S hS s).obj (geometricPointBaseNeighborhood B S hS s) = S :=
  rfl

/-- The base is the terminal étale neighborhood of a geometric point: the unique morphism of
neighborhoods to it is the structure morphism. -/
def isTerminal_geometricPointBaseNeighborhood :
    IsTerminal (geometricPointBaseNeighborhood B S hS s) := by
  refine IsTerminal.ofUniqueHom (fun U => ⟨ObjectProperty.homMk
    (Over.homMk U.1.obj.hom (Category.comp_id _)), Subtype.ext U.2.2⟩) (fun U f => ?_)
  apply Subtype.ext
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact Over.w ((SmallEtale.inclusion B S hS).map f.1)

/-! ### A small cofinal family of affine neighborhoods -/

/-- Every étale neighborhood of a geometric point is refined by an affine one: choose an affine
open of the neighborhood through which the point factors, and restrict the structure morphism
to it. -/
theorem exists_affine_etaleNeighborhood (U : (geometricPointFiber B S hS s).Elements) :
    ∃ V : (geometricPointFiber B S hS s).Elements,
      IsAffine ((SmallEtale.toScheme B S hS).obj V.1) ∧ Nonempty (V ⟶ U) := by
  obtain ⟨R, j, hj, y, hy⟩ : ∃ (R : CommRingCat.{u})
      (j : Spec R ⟶ (SmallEtale.toScheme B S hS).obj U.1)
      (_ : IsOpenImmersion j) (y : s.source ⟶ Spec R), y ≫ j = U.2.1 := by
    obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := U.2.1.base (default : s.source)) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j U.2.1 ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ B.inclusion.map U.1.obj.hom)).trans_lt hS
  let V : SmallEtale B S hS :=
    ⟨Over.mk (ObjectProperty.homMk (j ≫ B.inclusion.map U.1.obj.hom) :
      B.obj (Spec R) hR ⟶ B.obj S hS), (inferInstance : Etale (j ≫ B.inclusion.map U.1.obj.hom))⟩
  have hyS : y ≫ j ≫ B.inclusion.map U.1.obj.hom = s.hom := by
    rw [← Category.assoc, hy]
    exact U.2.2
  refine ⟨⟨V, ⟨y, hyS⟩⟩, (inferInstance : IsAffine (Spec R)), ⟨⟨ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk j) ?_), Subtype.ext hy⟩⟩⟩
  apply ObjectProperty.hom_ext
  rfl

/-- There is a small, fully faithful, cofinal index for the neighborhood diagram all of whose
values are affine: the full subcategory on the affine refinements of a small weakly initial set
of neighborhoods, replaced by a small model. -/
theorem exists_smallAffineEtaleNeighborhoodIndex :
    ∃ (A : Type u) (_ : SmallCategory A) (q : A ⥤ (geometricPointFiber B S hS s).Elements)
      (_ : q.Full) (_ : q.Faithful),
      (∀ U, ∃ a, Nonempty (q.obj a ⟶ U)) ∧
      ∀ a, IsAffine ((etaleNeighborhoodDiagram B S hS s).obj (q.obj a)) := by
  obtain ⟨T, hT, hTw⟩ := InitiallySmall.exists_small_weakly_initial_set.{u}
    (geometricPointFiber B S hS s).Elements
  have : Small.{u} T := hT
  choose V hVa hVm using fun t : T => exists_affine_etaleNeighborhood B S hS s t.1
  let s₀ : Set (geometricPointFiber B S hS s).Elements := Set.range V
  have haff : ∀ W ∈ s₀, IsAffine ((SmallEtale.toScheme B S hS).obj W.1) :=
    Set.forall_mem_range.2 hVa
  let e := equivSmallModel.{u} (ObjectProperty.FullSubcategory (· ∈ s₀))
  refine ⟨SmallModel.{u} (ObjectProperty.FullSubcategory (· ∈ s₀)), inferInstance,
    e.inverse ⋙ ObjectProperty.ι (· ∈ s₀), inferInstance, inferInstance, fun U => ?_,
    fun a => haff _ (e.inverse.obj a).2⟩
  obtain ⟨t, ht, ⟨f⟩⟩ := hTw U
  exact ⟨e.functor.obj ⟨V ⟨t, ht⟩, Set.mem_range_self _⟩,
    ⟨(ObjectProperty.ι (· ∈ s₀)).map (e.unitIso.app _).inv ≫ (hVm ⟨t, ht⟩).some ≫ f⟩⟩

/-- A chosen small cofinal family of affine étale neighborhoods of a geometric point. -/
def etaleNeighborhoodAffineIndex : Type u :=
  (exists_smallAffineEtaleNeighborhoodIndex B S hS s).choose

/-- The category structure on the chosen small affine family of étale neighborhoods. -/
instance smallCategory_etaleNeighborhoodAffineIndex :
    SmallCategory (etaleNeighborhoodAffineIndex B S hS s) :=
  (exists_smallAffineEtaleNeighborhoodIndex B S hS s).choose_spec.choose

/-- The inclusion of the chosen small affine family into the étale neighborhoods. -/
def etaleNeighborhoodAffineInclusion :
    etaleNeighborhoodAffineIndex B S hS s ⥤ (geometricPointFiber B S hS s).Elements :=
  (exists_smallAffineEtaleNeighborhoodIndex B S hS s).choose_spec.choose_spec.choose

/-- The inclusion of the chosen small affine family into the étale neighborhoods is full. -/
instance full_etaleNeighborhoodAffineInclusion :
    (etaleNeighborhoodAffineInclusion B S hS s).Full :=
  (exists_smallAffineEtaleNeighborhoodIndex B S hS
    s).choose_spec.choose_spec.choose_spec.choose

/-- The inclusion of the chosen small affine family into the étale neighborhoods is faithful. -/
instance faithful_etaleNeighborhoodAffineInclusion :
    (etaleNeighborhoodAffineInclusion B S hS s).Faithful :=
  (exists_smallAffineEtaleNeighborhoodIndex B S hS
    s).choose_spec.choose_spec.choose_spec.choose_spec.choose

/-- Every étale neighborhood of the point is refined by a member of the chosen small affine
family. -/
theorem etaleNeighborhoodAffineIndex_weaklyInitial
    (U : (geometricPointFiber B S hS s).Elements) :
    ∃ a, Nonempty ((etaleNeighborhoodAffineInclusion B S hS s).obj a ⟶ U) :=
  (exists_smallAffineEtaleNeighborhoodIndex B S hS
    s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 U

/-- The subdiagram of the neighborhood diagram on the chosen small affine family. -/
abbrev etaleNeighborhoodAffineDiagram :
    etaleNeighborhoodAffineIndex B S hS s ⥤ Scheme.{u} :=
  etaleNeighborhoodAffineInclusion B S hS s ⋙ etaleNeighborhoodDiagram B S hS s

/-- Every member of the chosen small affine family of étale neighborhoods is an affine scheme. -/
instance isAffine_etaleNeighborhoodAffineDiagram_obj (a : etaleNeighborhoodAffineIndex B S hS s) :
    IsAffine ((etaleNeighborhoodAffineDiagram B S hS s).obj a) :=
  (exists_smallAffineEtaleNeighborhoodIndex B S hS
    s).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2 a

/-- The chosen small affine family of étale neighborhoods is cofiltered. -/
instance isCofiltered_etaleNeighborhoodAffineIndex :
    IsCofiltered (etaleNeighborhoodAffineIndex B S hS s) :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (etaleNeighborhoodAffineInclusion B S hS s)
    (etaleNeighborhoodAffineIndex_weaklyInitial B S hS s)

/-- The inclusion of the chosen small affine family into the étale neighborhoods is initial. -/
instance initial_etaleNeighborhoodAffineInclusion :
    (etaleNeighborhoodAffineInclusion B S hS s).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
    (etaleNeighborhoodAffineInclusion B S hS s)
    (etaleNeighborhoodAffineIndex_weaklyInitial B S hS s)

/-! ### The limit -/

/-- **The étale neighborhoods of a geometric point have a limit of schemes.** The limit is
computed over the small cofinal family of affine neighborhoods, where the transition morphisms
are affine. -/
instance hasLimit_etaleNeighborhoodDiagram :
    HasLimit (etaleNeighborhoodDiagram B S hS s) :=
  Functor.Initial.hasLimit_of_comp (etaleNeighborhoodAffineInclusion B S hS s)

/-- The limit of the small cofinal family of affine neighborhoods is affine, every limit
projection of a system with affine transition morphisms being affine. -/
instance isAffine_limit_etaleNeighborhoodAffineDiagram :
    IsAffine (limit (etaleNeighborhoodAffineDiagram B S hS s)) := by
  obtain ⟨a⟩ := IsCofiltered.nonempty (C := etaleNeighborhoodAffineIndex B S hS s)
  have := isAffineHom_π_app (etaleNeighborhoodAffineDiagram B S hS s)
    (limit.cone _) (limit.isLimit _) a
  exact isAffine_of_isAffineHom
    ((limit.cone (etaleNeighborhoodAffineDiagram B S hS s)).π.app a)

/-- Global functions on the limit of the small affine family are the colimit of the global
functions over all étale neighborhoods. -/
def etaleNeighborhoodAffineLimitSectionsIso :
    Γ(limit (etaleNeighborhoodAffineDiagram B S hS s), ⊤) ≅
      colimit (etaleNeighborhoodSections B S hS s) :=
  ((nonempty_isColimit_Γ_mapCocone (etaleNeighborhoodAffineDiagram B S hS s)
        (limit.cone _) (limit.isLimit _)).some.coconePointUniqueUpToIso
      (colimit.isColimit ((etaleNeighborhoodAffineDiagram B S hS s).op ⋙ Scheme.Γ))).trans
    (Functor.Final.colimitIso (etaleNeighborhoodAffineInclusion B S hS s).op
      (etaleNeighborhoodSections B S hS s))

/-- The underlying ring of the colimit of the sections diagram is the étale local ring: the
forgetful functor from commutative rings to rings preserves the filtered colimit over the small
affine family, and cofinality transports it back. -/
def etaleLocalRingIsoColimitSections :
    (forget₂ CommRingCat RingCat).obj (colimit (etaleNeighborhoodSections B S hS s)) ≅
      etaleLocalRing B S hS s :=
  ((forget₂ CommRingCat RingCat).mapIso
      (Functor.Final.colimitIso (etaleNeighborhoodAffineInclusion B S hS s).op
        (etaleNeighborhoodSections B S hS s)).symm).trans
    ((preservesColimitIso (forget₂ CommRingCat RingCat)
        ((etaleNeighborhoodAffineInclusion B S hS s).op ⋙
          etaleNeighborhoodSections B S hS s)).trans
      (Functor.Final.colimitIso (etaleNeighborhoodAffineInclusion B S hS s).op
        (etaleNeighborhoodSections B S hS s ⋙ forget₂ CommRingCat RingCat)))

/-- Global functions on the limit of the small affine family of étale neighborhoods are the
étale local ring at the point, as an isomorphism of rings. -/
def etaleNeighborhoodAffineLimitSectionsRingCatIso :
    (forget₂ CommRingCat RingCat).obj
        Γ(limit (etaleNeighborhoodAffineDiagram B S hS s), ⊤) ≅ etaleLocalRing B S hS s :=
  ((forget₂ CommRingCat RingCat).mapIso
      (etaleNeighborhoodAffineLimitSectionsIso B S hS s)).trans
    (etaleLocalRingIsoColimitSections B S hS s)

/-- Global functions on the limit of the small affine family of étale neighborhoods are the
étale local ring at the point. -/
def etaleNeighborhoodAffineLimitRingEquiv :
    Γ(limit (etaleNeighborhoodAffineDiagram B S hS s), ⊤) ≃+* etaleLocalRing B S hS s :=
  Iso.ringCatIsoToRingEquiv (etaleNeighborhoodAffineLimitSectionsRingCatIso B S hS s)

/-! ### The limit projections on sections

Restricting a global function from a member of the small affine family to the limit, and then
reading the result as an element of the étale local ring, is taking the germ of that function at
the geometric point — that is, the structure map of the colimit defining the étale local ring.
-/

/-- A morphism that composes with `g` to a colimit structure map of `q ⋙ G` composes with `g`
and the cofinality isomorphism to the corresponding structure map of `G`. -/
private theorem comp_comp_colimitIso_hom_of_comp_eq {C J K : Type*} [Category C] [Category J]
    [Category K] (q : J ⥤ K) [q.Final] (G : K ⥤ C) [HasColimit G]
    {X : C} {j : J} {x : (q ⋙ G).obj j ⟶ X} {g : X ⟶ colimit (q ⋙ G)}
    (h : x ≫ g = colimit.ι (q ⋙ G) j) :
    x ≫ g ≫ (Functor.Final.colimitIso q G).hom = colimit.ι G (q.obj j) := by
  rw [← Category.assoc, h, Functor.Final.ι_colimitIso_hom]

/-- Restriction along a limit projection, followed by the identification of the sections of the
limit with the colimit of the sections, is the colimit structure map. -/
theorem etaleNeighborhoodAffineLimitSectionsIso_π_appTop
    (a : etaleNeighborhoodAffineIndex B S hS s) :
    ((limit.cone (etaleNeighborhoodAffineDiagram B S hS s)).π.app a).appTop ≫
        (etaleNeighborhoodAffineLimitSectionsIso B S hS s).hom =
      colimit.ι (etaleNeighborhoodSections B S hS s)
        (op ((etaleNeighborhoodAffineInclusion B S hS s).obj a)) :=
  comp_comp_colimitIso_hom_of_comp_eq (etaleNeighborhoodAffineInclusion B S hS s).op
    (etaleNeighborhoodSections B S hS s)
    ((IsColimit.comp_coconePointUniqueUpToIso_hom
      (nonempty_isColimit_Γ_mapCocone (etaleNeighborhoodAffineDiagram B S hS s)
        (limit.cone _) (limit.isLimit _)).some
      (colimit.isColimit ((etaleNeighborhoodAffineDiagram B S hS s).op ⋙ Scheme.Γ)) (op a)).trans
      (congrFun (colimit.cocone_ι
        (F := (etaleNeighborhoodAffineDiagram B S hS s).op ⋙ Scheme.Γ)) (op a)))

/-- The identification of the colimit of the sections with the étale local ring carries each
colimit structure map of commutative rings to the corresponding one of rings. -/
theorem etaleLocalRingIsoColimitSections_ι (a : etaleNeighborhoodAffineIndex B S hS s) :
    (forget₂ CommRingCat RingCat).map (colimit.ι (etaleNeighborhoodSections B S hS s)
          (op ((etaleNeighborhoodAffineInclusion B S hS s).obj a))) ≫
        (etaleLocalRingIsoColimitSections B S hS s).hom =
      colimit.ι (etaleNeighborhoodSections B S hS s ⋙ forget₂ CommRingCat RingCat)
        (op ((etaleNeighborhoodAffineInclusion B S hS s).obj a)) := by
  set F := forget₂ CommRingCat RingCat.{u}
  set q := (etaleNeighborhoodAffineInclusion B S hS s).op
  set G := etaleNeighborhoodSections B S hS s
  refine (Category.assoc _ _ _).symm.trans (comp_comp_colimitIso_hom_of_comp_eq q (G ⋙ F) ?_)
  rw [Functor.mapIso_hom, Iso.symm_hom, ← F.map_comp]
  erw [Functor.Final.ι_colimitIso_inv q G (op a)]
  exact ι_preservesColimitIso_hom F (q ⋙ G) (op a)

/-- **Restriction to the limit is the germ at the geometric point.** Restricting a global
function along a limit projection and reading the result in the étale local ring is the colimit
structure map of the sections diagram. -/
theorem etaleNeighborhoodAffineLimitSectionsRingCatIso_π_appTop
    (a : etaleNeighborhoodAffineIndex B S hS s) :
    (forget₂ CommRingCat RingCat).map
        ((limit.cone (etaleNeighborhoodAffineDiagram B S hS s)).π.app a).appTop ≫
      (etaleNeighborhoodAffineLimitSectionsRingCatIso B S hS s).hom =
      colimit.ι (etaleNeighborhoodSections B S hS s ⋙ forget₂ CommRingCat RingCat)
        (op ((etaleNeighborhoodAffineInclusion B S hS s).obj a)) := by
  rw [etaleNeighborhoodAffineLimitSectionsRingCatIso, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc, ← Functor.map_comp, etaleNeighborhoodAffineLimitSectionsIso_π_appTop]
  exact etaleLocalRingIsoColimitSections_ι B S hS s a

/-- The strict henselization is the limit of the small cofinal family of affine étale
neighborhoods. -/
def strictHenselizationIsoAffineLimit :
    strictHenselization B S hS s ≅ limit (etaleNeighborhoodAffineDiagram B S hS s) :=
  (Scheme.Spec.mapIso
      (RingEquiv.toCommRingCatIso (etaleNeighborhoodAffineLimitRingEquiv B S hS s)).op).trans
    (limit (etaleNeighborhoodAffineDiagram B S hS s)).isoSpec.symm

/-- **The strict henselization of a scheme at a geometric point is the limit of the étale
neighborhoods of that point.** -/
def strictHenselizationIsoLimit :
    strictHenselization B S hS s ≅ limit (etaleNeighborhoodDiagram B S hS s) :=
  (strictHenselizationIsoAffineLimit B S hS s).trans
    (Functor.Initial.limitIso (etaleNeighborhoodAffineInclusion B S hS s)
      (etaleNeighborhoodDiagram B S hS s))

/-- The cone on the diagram of étale neighborhoods of a geometric point whose vertex is the
strict henselization at that point. -/
def strictHenselizationCone : Cone (etaleNeighborhoodDiagram B S hS s) :=
  (limit.cone (etaleNeighborhoodDiagram B S hS s)).extend
    (strictHenselizationIsoLimit B S hS s).hom

/-- The vertex of the strict henselization cone is the strict henselization. -/
@[simp]
theorem strictHenselizationCone_pt :
    (strictHenselizationCone B S hS s).pt = strictHenselization B S hS s :=
  rfl

/-- **The strict henselization cone is a limit cone.** -/
def strictHenselizationConeIsLimit : IsLimit (strictHenselizationCone B S hS s) :=
  IsLimit.extendIso (strictHenselizationIsoLimit B S hS s).hom
    (limit.isLimit (etaleNeighborhoodDiagram B S hS s))

/-- The restriction of the strict henselization cone to the small cofinal family of affine étale
neighborhoods. This is the shape the descent results of Stacks Tag 01ZM consume, their index
category being required to be essentially small. -/
def strictHenselizationAffineCone : Cone (etaleNeighborhoodAffineDiagram B S hS s) :=
  (strictHenselizationCone B S hS s).whisker (etaleNeighborhoodAffineInclusion B S hS s)

/-- The vertex of the restricted strict henselization cone is the strict henselization. -/
@[simp]
theorem strictHenselizationAffineCone_pt :
    (strictHenselizationAffineCone B S hS s).pt = strictHenselization B S hS s :=
  rfl

/-- **The strict henselization is the limit of the small cofinal family of affine étale
neighborhoods.** -/
def strictHenselizationAffineConeIsLimit : IsLimit (strictHenselizationAffineCone B S hS s) :=
  (Functor.Initial.isLimitWhiskerEquiv (etaleNeighborhoodAffineInclusion B S hS s)
    (strictHenselizationCone B S hS s)).symm (strictHenselizationConeIsLimit B S hS s)

/-- The leg of the strict henselization cone at a member of the small affine family is the
identification of the strict henselization with the limit of that family, followed by the limit
projection. Together with
`AlgebraicGeometry.etaleNeighborhoodAffineLimitSectionsRingCatIso_π_appTop` this computes the leg
on sections. -/
theorem strictHenselizationAffineCone_π_app (a : etaleNeighborhoodAffineIndex B S hS s) :
    (strictHenselizationAffineCone B S hS s).π.app a =
      (strictHenselizationIsoAffineLimit B S hS s).hom ≫
        limit.π (etaleNeighborhoodAffineDiagram B S hS s) a := by
  simp [strictHenselizationAffineCone, strictHenselizationCone, strictHenselizationIsoLimit,
    Functor.Initial.limitIso]

/-- The morphism from the strict henselization to the base determined by the limit cone: its leg
at the terminal neighborhood. -/
def strictHenselizationConeToBase : strictHenselization B S hS s ⟶ S :=
  (strictHenselizationCone B S hS s).π.app (geometricPointBaseNeighborhood B S hS s)

/-- Every leg of the strict henselization cone lies over the base. -/
theorem strictHenselizationCone_π_comp_hom (U : (geometricPointFiber B S hS s).Elements) :
    (strictHenselizationCone B S hS s).π.app U ≫ B.inclusion.map U.1.obj.hom =
      strictHenselizationConeToBase B S hS s :=
  (strictHenselizationCone B S hS s).w
    ((isTerminal_geometricPointBaseNeighborhood B S hS s).from U)

end AlgebraicGeometry

end
