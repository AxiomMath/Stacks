module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.GeneralizationsOfCohomology
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullbackDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerived.DerivedDeltaFunctor
public import StacksFrontier.Cotangent.CohomologyPresheaf.SiteSectionsComparison
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# The stalk of a higher direct image along a spectral map

Let `f : X ⟶ Y` be a spectral map of spectral spaces, let `y` be a point of `Y`, let `E ⊆ Y` be
the set of points specializing to `y` and let `F` be a sheaf of abelian groups on `X`. This file
proves [Stacks, Tag 0A3E]: for every `p`

`(R^p f_* F)_y = H^p(f⁻¹(E), F|_{f⁻¹(E)})`.

The inverse image `f⁻¹(E)` is the *specialization fibre* `Stacks.Topology.specializationFiber f y`,
the set of points of `X` whose image specializes to `y`.

## Main definitions

* `Stacks.Topology.specializationFiber` is the set of points of `X` whose image specializes
  to `y`.
* `Stacks.Topology.preimageOpenNhds` sends an open neighbourhood of `y` to the open neighbourhood
  of the specialization fibre which is its inverse image.
* `Stacks.Topology.fiberSectionsOfStalk` is the degree-zero comparison, from the stalk at `y` of
  `f_* F` to the global sections of the restriction of `F` to the specialization fibre.

## Main results

* `Stacks.Topology.isStableCompact_specializationFiber`: the specialization fibre of a spectral
  map is quasi-compact and stable under generalization.
* `Stacks.Topology.initial_preimageOpenNhds`: the inverse images of the open neighbourhoods of
  `y` are cofinal among the open neighbourhoods of the specialization fibre.
* `Stacks.Topology.fiberSectionsOfStalkIso`: the degree-zero statement, as an isomorphism of
  functors of the abelian sheaf.
* `Stacks.Topology.sheafStalkFunctor_preservesHomology`: taking stalks of abelian sheaves is
  exact.
* `Stacks.Topology.rightAcyclic_globalSections_restriction`: the restriction of an injective
  abelian sheaf to the specialization fibre is acyclic for global sections.
* `Stacks.Topology.higherDirectImageStalkIso`: the stalk at `y` of `R^p f_* F` is the `p`-th
  cohomology of the restriction of `F` to the specialization fibre.
* `Stacks.Topology.nonempty_higherDirectImageStalkIso_cohomologyPresheaf` is the same statement
  in the `Ext`-model of cohomology.

## References

* [Stacks Project, Tag 0A3E](https://stacks.math.columbia.edu/tag/0A3E)
* [Stacks Project, Tag 0A3D](https://stacks.math.columbia.edu/tag/0A3D)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

namespace Stacks.Topology

universe u

variable {X Y : TopCat.{u}}

/-! ### The specialization fibre -/

/-- The inverse image of the set of points specializing to `y`: the points of `X` whose image
specializes to `y`. -/
def specializationFiber (f : X ⟶ Y) (y : Y) : Set X := {x | f x ⤳ y}

/-- A point lies in the specialization fibre of `y` iff its image specializes to `y`. -/
@[simp]
theorem mem_specializationFiber {f : X ⟶ Y} {y : Y} {x : X} :
    x ∈ specializationFiber f y ↔ f x ⤳ y := Iff.rfl

/-- The specialization fibre is stable under generalization: it is its own generalization
locus. -/
theorem specializationFiber_eq_generalizationsOf (f : X ⟶ Y) (y : Y) :
    specializationFiber f y =
      SpectralSubset.generalizationsOf (specializationFiber f y) := by
  ext x
  refine ⟨fun hx ↦ ⟨x, hx, specializes_refl x⟩, ?_⟩
  rintro ⟨z, hz, hxz⟩
  exact (f.hom.map_specializes hxz).trans hz

/-- The inverse image of a quasi-compact open neighbourhood of `y` under a spectral map is
open and quasi-compact. -/
private theorem isOpen_and_isCompact_preimage {f : X ⟶ Y} (hf : IsSpectralMap f) {y : Y}
    (V : SpectralSubset.CompactOpenNeighborhood ({y} : Set Y)) :
    IsOpen (f ⁻¹' (V : Set Y)) ∧ IsCompact (f ⁻¹' (V : Set Y)) :=
  ⟨V.2.1.preimage hf.continuous, hf.isCompact_preimage_of_isOpen V.2.1 V.2.2.1⟩

variable [SpectralSpace Y]

/-- **The specialization fibre is the intersection of the inverse images of the quasi-compact
open neighbourhoods of `y`.** -/
theorem specializationFiber_eq_iInter_preimage (f : X ⟶ Y) (y : Y) :
    specializationFiber f y =
      ⋂ V : SpectralSubset.CompactOpenNeighborhood ({y} : Set Y), f ⁻¹' (V : Set Y) := by
  have h : SpectralSubset.generalizationsOf ({y} : Set Y) =
      ⋂ V : SpectralSubset.CompactOpenNeighborhood ({y} : Set Y), (V : Set Y) :=
    SpectralSubset.generalizationsOf_eq_iInter_compactOpenNeighborhood _ isCompact_singleton
  ext x
  simp only [mem_specializationFiber, Set.mem_iInter, Set.mem_preimage]
  refine ⟨fun hx V ↦ hx.mem_open V.2.1 (V.2.2.2 rfl), fun hx ↦ ?_⟩
  obtain ⟨z, hz, hxz⟩ : f x ∈ SpectralSubset.generalizationsOf ({y} : Set Y) :=
    h ▸ Set.mem_iInter.2 hx
  exact (Set.mem_singleton_iff.1 hz) ▸ hxz

variable [SpectralSpace X]

/-- **The specialization fibre of a spectral map is quasi-compact and stable under
generalization.** -/
theorem isStableCompact_specializationFiber {f : X ⟶ Y} (hf : IsSpectralMap f) (y : Y) :
    SpectralSubset.IsStableCompact (specializationFiber f y) := by
  have hInter : SpectralSubset.IsInterCompactOpen (specializationFiber f y) := by
    refine ⟨Set.range fun V : SpectralSubset.CompactOpenNeighborhood ({y} : Set Y) ↦
      f ⁻¹' (V : Set Y), ?_, ?_⟩
    · rw [specializationFiber_eq_iInter_preimage f y, Set.sInter_range]
    · rintro _ ⟨V, rfl⟩
      exact isOpen_and_isCompact_preimage hf V
  exact ((SpectralSubset.characterizations_equiv (specializationFiber f y)).2.1).2
    (((SpectralSubset.characterizations_equiv (specializationFiber f y)).2.2.1).2 hInter)

/-- **The inverse images of the open neighbourhoods of `y` are cofinal among the open
neighbourhoods of the specialization fibre.** -/
theorem exists_preimage_subset {f : X ⟶ Y} (hf : IsSpectralMap f) (y : Y) {A : Set X}
    (hA : IsOpen A) (hWA : specializationFiber f y ⊆ A) :
    ∃ V : Opens Y, y ∈ V ∧ f ⁻¹' (V : Set Y) ⊆ A := by
  obtain ⟨V, hV⟩ := SpectralSubset.exists_subset_of_subset_isOpen
    (fun V : SpectralSubset.CompactOpenNeighborhood ({y} : Set Y) ↦ f ⁻¹' (V : Set Y))
    (isOpen_and_isCompact_preimage hf)
    (fun V W ↦ (directed_of (· ≥ ·) V W).imp fun _ h ↦
      Set.subset_inter (Set.preimage_mono h.1) (Set.preimage_mono h.2))
    _ (specializationFiber_eq_iInter_preimage f y) A hA hWA
  exact ⟨⟨(V : Set Y), V.2.1⟩, V.2.2.2 rfl, hV⟩

/-! ### The inverse images of the open neighbourhoods of `y` -/

/-- The inverse image of an open neighbourhood of `y` is an open neighbourhood of the
specialization fibre, functorially in the inclusion. -/
def preimageOpenNhds (f : X ⟶ Y) (y : Y) :
    OpenNhds y ⥤ OpenNhdsSet (specializationFiber f y) where
  obj V := ⟨(Opens.map f).obj V.1, fun _ hx ↦ hx.mem_open V.1.2 V.2⟩
  map {_ _} a := ObjectProperty.homMk ((Opens.map f).map ((OpenNhds.inclusion y).map a))
  map_id _ := ObjectProperty.hom_ext _ (Subsingleton.elim _ _)
  map_comp _ _ := ObjectProperty.hom_ext _ (Subsingleton.elim _ _)

/-- **The inverse images of the open neighbourhoods of `y` are cofinal among the open
neighbourhoods of the specialization fibre.** -/
theorem initial_preimageOpenNhds {f : X ⟶ Y} (hf : IsSpectralMap f) (y : Y) :
    (preimageOpenNhds f y).Initial :=
  Functor.initial_of_exists_of_isCofiltered _
    (fun A ↦ by
      obtain ⟨V, hyV, hVA⟩ :=
        exists_preimage_subset hf y (A := (A.obj : Set X)) A.obj.isOpen A.property
      exact ⟨⟨V, hyV⟩, ⟨ObjectProperty.homMk (homOfLE hVA)⟩⟩)
    (fun {_ c} _ _ ↦ ⟨c, 𝟙 c, ObjectProperty.hom_ext _ (Subsingleton.elim _ _)⟩)

/-! ### The degree-zero comparison -/

noncomputable section DegreeZero

/-- Pushforward of abelian sheaves along `f`, in the spelling of the category of abelian sheaves
in which cohomology is taken. -/
abbrev pushforwardSheafFunctor (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f

/-- The stalk at `y` of an abelian sheaf on `Y`, as a functor. -/
abbrev sheafStalkFunctor (y : Y) :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y

variable (f : X ⟶ Y) (y : Y)

/-- Restriction of an abelian sheaf on `X` to the specialization fibre, followed by global
sections: the degree-zero cohomology of the restriction, as a functor. -/
abbrev fiberSectionsFunctor :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  restrictionFunctor X (specializationFiber f y) ⋙
    sectionsFunctor (TopCat.of (specializationFiber f y))

omit [SpectralSpace X] [SpectralSpace Y] in
/-- The specialization fibre is contained in the inverse image of every open neighbourhood
of `y`. -/
theorem top_le_map_preimage (V : OpenNhds y) :
    (⊤ : Opens (TopCat.of (specializationFiber f y))) ≤
      (Opens.map (Stacks.subsetInclusion X (specializationFiber f y))).obj
        ((Opens.map f).obj V.1) :=
  fun z _ ↦ (mem_specializationFiber.1 z.2).mem_open V.1.2 V.2

/-- The presheaf underlying the pushforward of `F` along `f`. -/
abbrev pushforwardPresheaf (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Y.Presheaf AddCommGrpCat.{u} :=
  (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
    ((pushforwardSheafFunctor f).obj F)

omit [SpectralSpace X] [SpectralSpace Y] in
/-- The stalk diagram of `f_* F` at `y` is the diagram of sections of `F` over the inverse
images of the open neighbourhoods of `y`. -/
theorem preimageOpenNhds_comp_neighborhoodSections
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (preimageOpenNhds f y).op ⋙ neighborhoodSections F (specializationFiber f y) =
      (OpenNhds.inclusion y).op ⋙ pushforwardPresheaf f F :=
  rfl

/-- **The degree-zero comparison at a single sheaf.** The stalk at `y` of `f_* F` — the colimit
of the sections of `F` on the inverse images of the open neighbourhoods of `y` — maps to the
global sections of the restriction of `F` to the specialization fibre. It is the degree-zero
comparison `Stacks.Topology.subsetSectionsMap` of [Stacks, Tag 09V3] along the specialization
fibre, precomposed with the passage from the colimit over the inverse images of the open
neighbourhoods of `y` to the colimit over all open neighbourhoods of the fibre. -/
def fiberSectionsOfStalkApp (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (pushforwardSheafFunctor f ⋙ sheafStalkFunctor y).obj F ⟶ (fiberSectionsFunctor f y).obj F :=
  colimit.pre (neighborhoodSections F (specializationFiber f y)) (preimageOpenNhds f y).op ≫
    subsetSectionsMap F (specializationFiber f y)

omit [SpectralSpace X] [SpectralSpace Y] in
/-- The degree-zero comparison carries the germ at `y` of a section of `F` on `f⁻¹(V)` to the
section it induces on the specialization fibre. -/
theorem fiberSectionsOfStalkApp_germ
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (V : Opens Y) (hy : y ∈ V)
    (s : ToType ((pushforwardPresheaf f F).obj (op V))) :
    fiberSectionsOfStalkApp f y F ((pushforwardPresheaf f F).germ V y hy s) =
      ambientSection (Stacks.subsetInclusion X (specializationFiber f y)) F
        (top_le_map_preimage f y ⟨V, hy⟩) s := by
  have hpre : colimit.pre (neighborhoodSections F (specializationFiber f y))
        (preimageOpenNhds f y).op ((pushforwardPresheaf f F).germ V y hy s) =
      colimit.ι (neighborhoodSections F (specializationFiber f y))
        (op ((preimageOpenNhds f y).obj ⟨V, hy⟩)) s :=
    (ConcreteCategory.comp_apply _ _ s).symm.trans
      (ConcreteCategory.congr_hom
        (colimit.ι_pre (neighborhoodSections F (specializationFiber f y))
          (preimageOpenNhds f y).op (op ⟨V, hy⟩)) s)
  exact (ConcreteCategory.comp_apply _ _ _).trans
    ((congrArg (subsetSectionsMap F (specializationFiber f y)) hpre).trans
      (subsetSectionsMap_ι F (specializationFiber f y)
        (op ((preimageOpenNhds f y).obj ⟨V, hy⟩)) s))

/-- **The degree-zero comparison**, natural in the abelian sheaf. -/
def fiberSectionsOfStalk :
    pushforwardSheafFunctor f ⋙ sheafStalkFunctor y ⟶ fiberSectionsFunctor f y where
  app F := fiberSectionsOfStalkApp f y F
  naturality F G β := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun V hy ↦
      ConcreteCategory.hom_ext _ _ fun s ↦ ?_
    refine (ConcreteCategory.comp_apply _ _ s).trans ?_
    refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ s).symm
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ _).symm
    refine ((congrArg (fiberSectionsOfStalkApp f y G)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply V y hy
        ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          ((pushforwardSheafFunctor f).map β)) s)).trans
      (fiberSectionsOfStalkApp_germ f y G V hy _)).trans ?_
    exact ((ambientSection_naturality_apply
        (Stacks.subsetInclusion X (specializationFiber f y)) β
        (top_le_map_preimage f y ⟨V, hy⟩) s).symm).trans
      (congrArg ((fiberSectionsFunctor f y).map β)
        (fiberSectionsOfStalkApp_germ f y F V hy s)).symm

/-- **The degree-zero comparison is an isomorphism.** The stalk at `y` of `f_* F` is the group
of global sections of the restriction of `F` to the specialization fibre. -/
theorem isIso_fiberSectionsOfStalkApp (hf : IsSpectralMap f)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    IsIso (fiberSectionsOfStalkApp f y F) := by
  have hinit : (preimageOpenNhds f y).Initial := initial_preimageOpenNhds hf y
  have hσ : IsIso (subsetSectionsMap F (specializationFiber f y)) := by
    suffices IsIso ((CategoryTheory.forget AddCommGrpCat.{u}).map
        (subsetSectionsMap F (specializationFiber f y))) from
      isIso_of_reflects_iso _ (CategoryTheory.forget AddCommGrpCat.{u})
    rw [isIso_iff_bijective]
    exact ⟨injective_subsetSectionsMap F (specializationFiber f y),
      surjective_subsetSectionsMap_of_isStableCompact F
        (isStableCompact_specializationFiber hf y)⟩
  exact IsIso.comp_isIso' (Functor.Final.colimit_pre_isIso _) hσ

/-- **The stalk at `y` of `f_* F` is the group of global sections of `F` restricted to the
specialization fibre**, naturally in `F`. -/
def fiberSectionsOfStalkIso (hf : IsSpectralMap f) :
    pushforwardSheafFunctor f ⋙ sheafStalkFunctor y ≅ fiberSectionsFunctor f y :=
  have : ∀ F, IsIso ((fiberSectionsOfStalk f y).app F) := fun F ↦
    isIso_fiberSectionsOfStalkApp f y hf F
  have : IsIso (fiberSectionsOfStalk f y) := NatIso.isIso_of_isIso_app _
  asIso (fiberSectionsOfStalk f y)

end DegreeZero

/-! ### Exactness of the stalk functor on abelian sheaves -/

noncomputable section Stalks

omit [SpectralSpace X] [SpectralSpace Y]

/-- The stalk at a point of an abelian sheaf is an additive functor of the sheaf. -/
instance sheafStalkFunctor_additive (y : Y) : (sheafStalkFunctor y).Additive :=
  inferInstanceAs (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).Additive

/-- The stalk at a point of an abelian sheaf is a left exact functor of the sheaf. -/
instance sheafStalkFunctor_preservesFiniteLimits (y : Y) :
    PreservesFiniteLimits (sheafStalkFunctor y) :=
  inferInstanceAs (PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y))

/-- The stalk at a point of an abelian sheaf is a right exact functor of the sheaf. -/
instance sheafStalkFunctor_preservesFiniteColimits (y : Y) :
    PreservesFiniteColimits (sheafStalkFunctor y) :=
  inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.forget AddCommGrpCat.{u} Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y))

/-- **The stalk functor on abelian sheaves is exact, so it preserves homology.** -/
instance sheafStalkFunctor_preservesHomology (y : Y) :
    (sheafStalkFunctor y).PreservesHomology :=
  Functor.preservesHomologyOfExact (sheafStalkFunctor y)

end Stalks

/-! ### Stacks 0A3E -/

noncomputable section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

omit [SpectralSpace X] [SpectralSpace Y] in
/-- Pushforward of abelian sheaves is additive. -/
instance pushforwardSheafFunctor_additive (f : X ⟶ Y) :
    (pushforwardSheafFunctor f).Additive where
  map_add := rfl

variable (f : X ⟶ Y) (y : Y)

/-- **The restriction of an injective abelian sheaf to the specialization fibre is acyclic for
global sections.** -/
theorem rightAcyclic_globalSections_restriction (hf : IsSpectralMap f)
    (I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective I] :
    (sectionsFunctor (TopCat.of (specializationFiber f y))).rightAcyclic
      ((restrictionFunctor X (specializationFiber f y)).obj I) := by
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology
      (TopCat.of (specializationFiber f y))) AddCommGrpCat.{u}) := hasExt_of_enoughInjectives _
  have hinj : Injective (C := TopCat.Sheaf AddCommGrpCat.{u} X) I := ‹Injective I›
  exact IsZero.of_iso (isZero_cohomologyPresheaf_pullback_of_injective_of_isStableCompact I
      (isStableCompact_specializationFiber hf y) p hp)
    (Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections
      (Opens.grothendieckTopology (TopCat.of (specializationFiber f y)))
      ((restrictionFunctor X (specializationFiber f y)).obj I) p ⊤).symm

/-- Let `f : X ⟶ Y` be a spectral map of spectral spaces, let `y` be a point of `Y`, let `E` be the
set of points of `Y` specializing to `y` and let `F` be a sheaf of abelian groups on `X`. Then for
every `p` the stalk at `y` of the `p`-th higher direct image of `F` is the `p`-th cohomology of the
restriction of `F` to `f⁻¹(E)`:

`(R^p f_* F)_y = H^p(f⁻¹(E), F|_{f⁻¹(E)})`.

Here `f⁻¹(E)` is `Stacks.Topology.specializationFiber f y`, the set of points of `X` whose image
specializes to `y`, and cohomology is the right derived functor of global sections. -/
@[stacks 0A3E]
def higherDirectImageStalkIso (hf : IsSpectralMap f) (p : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((pushforwardSheafFunctor f).rightDerived p ⋙ sheafStalkFunctor y).obj F ≅
      ((sectionsFunctor (TopCat.of (specializationFiber f y))).rightDerived p).obj
        ((restrictionFunctor X (specializationFiber f y)).obj F) :=
  (Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedPostcomposeIso
      (F := pushforwardSheafFunctor f) (sheafStalkFunctor y) p).app F ≪≫
    (Stacks.Cohomology.CechDelta.rightDerivedIsoOfIso
      (fiberSectionsOfStalkIso f y hf) p).app F ≪≫
    Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso
      (restrictionFunctor X (specializationFiber f y))
      (sectionsFunctor (TopCat.of (specializationFiber f y)))
      (fun I _ ↦ rightAcyclic_globalSections_restriction f y hf I) F
      (Functor.rightAcyclic_of_exact _ _) p

/-- **Stacks 0A3E in the `Ext`-model of cohomology.** The stalk at `y` of the `p`-th higher
direct image of `F` is isomorphic to the degree-`p` cohomology of the restriction of `F` to the
specialization fibre in the model `CategoryTheory.Sheaf.cohomologyPresheaf` — the `Ext`-group out
of the free abelian sheaf — which is the model [Stacks, Tag 0A3D] is stated in. -/
theorem nonempty_higherDirectImageStalkIso_cohomologyPresheaf (hf : IsSpectralMap f) (p : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology
      (TopCat.of (specializationFiber f y))) AddCommGrpCat.{u})] :
    Nonempty (((pushforwardSheafFunctor f).rightDerived p ⋙ sheafStalkFunctor y).obj F ≅
      ((((restrictionFunctor X (specializationFiber f y)).obj F).cohomologyPresheaf p).obj
        (op ⊤))) :=
  ⟨higherDirectImageStalkIso f y hf p F ≪≫
    (Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections
      (Opens.grothendieckTopology (TopCat.of (specializationFiber f y)))
      ((restrictionFunctor X (specializationFiber f y)).obj F) p ⊤).symm⟩

end Derived

end Stacks.Topology

end
