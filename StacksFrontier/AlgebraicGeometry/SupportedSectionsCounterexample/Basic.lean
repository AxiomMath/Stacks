module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Sections supported on a closed subset: a functor which is left exact but not exact

Let `Z` be a closed subset of a ringed space `X`. The functor `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of
sections supported on `Z` is left exact, being a right adjoint; this file shows it is not exact
in general, which is the last assertion of Stacks 0G6N.

The counterexample is the two-point Sierpinski space `{c, o}`, whose open sets are `∅`, `{o}`
and the whole space, with `Z = {c}` the closed point. A presheaf on this space is a sheaf as
soon as its value on `∅` is terminal, because every covering sieve of a nonempty open set
contains the identity. The structure sheaf is taken to be the skyscraper `R` at the open point
`o`, the `𝒪_X`-module `F` is the skyscraper `M` at `o`, and `G` is the skyscraper `M` at the
closed point `c`; the morphism `F ⟶ G` is an isomorphism on global sections and the zero map on
`{o}`, so it is surjective on sections of every open set, hence an epimorphism.

Now `H_Z(F) = 0`: a section of `F` whose germ at `o` vanishes is already zero, because `F` has
the same sections on `{o}` as on the whole space. On the other hand `H_Z(G) ≠ 0`: the global
section `m` of `G` restricts to zero on `{o}`, so its germ at `o` vanishes and its support is
contained in `{c} = Z`. A functor sending an epimorphism between these to an epimorphism would
send `0 ⟶ H_Z(G)` to an epimorphism, forcing `H_Z(G) = 0`.

## Main definitions

* `Stacks.SupportedSectionsCounterexample.Pt`: the two points, with the Sierpinski topology.
* `Stacks.SupportedSectionsCounterexample.ringedSpace`: the Sierpinski space with the
  skyscraper `R` at the open point as structure sheaf.
* `Stacks.SupportedSectionsCounterexample.openSheaf`,
  `Stacks.SupportedSectionsCounterexample.closedSheaf`: the skyscraper `𝒪_X`-modules at the
  open and at the closed point.
* `Stacks.SupportedSectionsCounterexample.skyscraperHom`: the epimorphism between them.

## Main results

* `Stacks.SupportedSectionsCounterexample.isSheaf_of_isTerminal`: a presheaf on the Sierpinski
  space whose value on `∅` is terminal is a sheaf.
* `Stacks.SupportedSectionsCounterexample.epi_skyscraperHom`: the morphism of the
  counterexample is an epimorphism, being surjective on sections over every open set.
* `Stacks.SupportedSectionsCounterexample.isZero_supportedSections_openSheaf` and
  `Stacks.SupportedSectionsCounterexample.not_isZero_supportedSections_closedSheaf`: `H_Z` of
  its source is zero and `H_Z` of its target is not.
* `Stacks.SupportedSectionsCounterexample.exists_epi_not_epi_supportedSectionsOnClosedFunctor_map`:
  **Stacks 0G6N**, `H_Z` does not preserve epimorphisms in general.
* `exists_not_preservesFiniteColimits_supportedSectionsOnClosedFunctor`: **Stacks 0G6N**,
  `H_Z` is not exact in general: it does not preserve finite colimits.

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.SupportedSectionsCounterexample

/-! ### The Sierpinski space -/

/-- The two points of the Sierpinski space: `closedPt` is a closed point and `openPt` is an
open point, the only open set containing `closedPt` being the whole space. -/
inductive Pt : Type u
  | closedPt : Pt
  | openPt : Pt

/-- The Sierpinski topology: a set is open when it contains the open point as soon as it
contains the closed point, i.e. the open sets are `∅`, `{openPt}` and the whole space. -/
instance : TopologicalSpace Pt.{u} where
  IsOpen s := Pt.closedPt ∈ s → Pt.openPt ∈ s
  isOpen_univ _ := Set.mem_univ _
  isOpen_inter _ _ hs ht h := ⟨hs h.1, ht h.2⟩
  isOpen_sUnion _ hS := fun ⟨t, ht, hct⟩ => ⟨t, ht, hS t ht hct⟩

/-- The Sierpinski space as an object of `TopCat`. -/
abbrev space : TopCat.{u} := TopCat.of Pt.{u}

/-- An open set containing the closed point contains the open point. -/
theorem openPt_mem_of_closedPt_mem {U : Opens space.{u}} (h : Pt.closedPt ∈ U) :
    Pt.openPt ∈ U :=
  U.isOpen h

/-- The only open set containing the closed point is the whole space. -/
theorem eq_top_of_closedPt_mem {U : Opens space.{u}} (h : Pt.closedPt ∈ U) : U = ⊤ := by
  ext x
  simp only [Opens.coe_top, Set.mem_univ, iff_true]
  cases x
  · exact h
  · exact openPt_mem_of_closedPt_mem h

/-- Every nonempty open set of the Sierpinski space has a point which is contained in no
smaller open set: the closed point if the open set is the whole space, the open point
otherwise. -/
theorem exists_le_of_mem {U : Opens space.{u}} (hU : U ≠ ⊥) :
    ∃ x ∈ U, ∀ V : Opens space.{u}, x ∈ V → U ≤ V := by
  by_cases hc : Pt.closedPt ∈ U
  · refine ⟨Pt.closedPt, hc, fun V hV => ?_⟩
    rw [eq_top_of_closedPt_mem hV]
    exact le_top
  · have ho : Pt.openPt ∈ U := by
      rcases Set.eq_empty_or_nonempty (U : Set Pt.{u}) with h | ⟨x, hx⟩
      · exact absurd (Opens.ext h) hU
      · cases x
        · exact absurd hx hc
        · exact hx
    refine ⟨Pt.openPt, ho, fun V hV y hy => ?_⟩
    cases y
    · exact absurd hy hc
    · exact hV

/-- A presheaf on the Sierpinski space whose value on the empty open set is terminal is a
sheaf: every covering sieve of a nonempty open set contains the identity. -/
theorem isSheaf_of_isTerminal {C : Type*} [Category C] (F : TopCat.Presheaf C space.{u})
    (it : IsTerminal <| F.obj <| op ⊥) : F.IsSheaf := fun c U s hs => by
  obtain rfl | hne := eq_or_ne U ⊥
  · intro _ _
    rw [@existsUnique_iff_exists _ ⟨fun _ _ => _⟩]
    · refine ⟨it.from _, fun U hU hs => IsTerminal.hom_ext ?_ _ _⟩
      rwa [le_bot_iff.1 hU.le]
    · apply it.hom_ext
  · convert! Presieve.isSheafFor_top (F ⋙ coyoneda.obj (@op C c))
    rw [Sieve.arrows_eq_top_iff, ← Sieve.id_mem_iff_eq_top]
    obtain ⟨x, hxU, hmin⟩ := exists_le_of_mem hne
    obtain ⟨V, f, hf, hxV⟩ := hs x hxU
    obtain rfl : V = U := le_antisymm f.le (hmin V hxV)
    convert! hf

/-- The open set `{openPt}`, the complement of the closed point. -/
def openSet : Opens space.{u} where
  carrier := {Pt.openPt}
  is_open' h := absurd h (by simp)

/-- The closed subset `{closedPt}` of the Sierpinski space. -/
def closedSet : Set space.{u} := {Pt.closedPt}

/-- The closed point is a closed subset: its complement is the open point. -/
theorem isClosed_closedSet : IsClosed (closedSet.{u}) :=
  ⟨fun h => absurd rfl h⟩

/-- Two elements of `PLift p` with `p` a proposition are equal. -/
theorem plift_ext {p : Prop} (a b : PLift p) : a = b := by
  cases a
  cases b
  rfl

/-! ### The ringed space -/

/-- The sections of the structure sheaf over `U`: a copy of `R` if the open point lies in `U`,
the trivial ring otherwise. -/
abbrev ringSections (R : Type u) (U : (Opens space.{u})ᵒᵖ) : Type u :=
  PLift (Pt.openPt ∈ (unop U : Opens space.{u})) → R

/-- The restriction map of the structure sheaf, precomposition along the inclusion of open
sets. -/
def resRingHom (R : Type u) [CommRing R] {U V : (Opens space.{u})ᵒᵖ} (i : U ⟶ V) :
    ringSections R U →+* ringSections R V where
  toFun s h := s (PLift.up (i.unop.le h.down))
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The structure sheaf of the counterexample: the skyscraper `R` at the open point. -/
def structurePresheaf (R : Type u) [CommRing R] : space.{u}.Presheaf CommRingCat.{u} where
  obj U := CommRingCat.of (ringSections R U)
  map i := CommRingCat.ofHom (resRingHom R i)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying presheaf of (not necessarily commutative) rings of the structure sheaf. -/
abbrev ringPresheaf (R : Type u) [CommRing R] : (Opens space.{u})ᵒᵖ ⥤ RingCat.{u} :=
  structurePresheaf R ⋙ forget₂ CommRingCat.{u} RingCat.{u}

/-- The ring of sections of the structure sheaf over `∅` is trivial. -/
instance subsingleton_ringSections_bot (R : Type u) [CommRing R] :
    Subsingleton (ringSections R (op (⊥ : Opens space.{u}))) :=
  ⟨fun _ _ => funext fun h => h.down.elim⟩

/-- A subsingleton object of `CommRingCat` is terminal. -/
def commRingCatIsTerminal (A : CommRingCat.{u}) [Subsingleton A] : IsTerminal A := by
  refine IsTerminal.ofUnique (h := fun Y => ?_) A
  refine ⟨⟨CommRingCat.ofHom ⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _⟩, Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩⟩,
    fun _ => ?_⟩
  apply CommRingCat.hom_ext
  ext
  exact Subsingleton.elim _ _

/-- The structure presheaf, the skyscraper `R` at the open point, is a sheaf. -/
theorem structurePresheaf_isSheaf (R : Type u) [CommRing R] :
    (structurePresheaf R).IsSheaf := by
  refine isSheaf_of_isTerminal _ (@commRingCatIsTerminal _ ?_)
  exact inferInstanceAs (Subsingleton (ringSections R (op (⊥ : Opens space.{u}))))

/-- The Sierpinski space with the skyscraper `R` at the open point as its structure sheaf. -/
def ringedSpace (R : Type u) [CommRing R] : AlgebraicGeometry.RingedSpace.{u, u} where
  carrier := space
  presheaf := structurePresheaf R
  IsSheaf := structurePresheaf_isSheaf R

/-! ### The two skyscraper modules and the epimorphism between them -/

/-- The sections over `U` of the skyscraper `M` at the open point: a copy of `M` if the open
point lies in `U`, zero otherwise. -/
abbrev openSections (M : Type u) (U : (Opens space.{u})ᵒᵖ) : Type u :=
  PLift (Pt.openPt ∈ (unop U : Opens space.{u})) → M

/-- The sections over `U` of the skyscraper `M` at the closed point: a copy of `M` if the
closed point lies in `U`, zero otherwise. The outer factor, indexed by the open point, is there
so that the sections form a module over `ringSections R U` pointwise. -/
abbrev closedSections (M : Type u) (U : (Opens space.{u})ᵒᵖ) : Type u :=
  PLift (Pt.openPt ∈ (unop U : Opens space.{u})) →
    PLift (Pt.closedPt ∈ (unop U : Opens space.{u})) → M

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The sections over `U` of the skyscraper `M` at the open point form a module over the sections
of the structure sheaf over `U`, acting pointwise. -/
instance moduleOpenSections (U : (Opens space.{u})ᵒᵖ) :
    Module ↥((ringPresheaf R).obj U) (openSections M U) :=
  inferInstanceAs (Module (ringSections R U) (openSections M U))

/-- The sections over `U` of the skyscraper `M` at the closed point form a module over the
sections of the structure sheaf over `U`, acting pointwise. -/
instance moduleClosedSections (U : (Opens space.{u})ᵒᵖ) :
    Module ↥((ringPresheaf R).obj U) (closedSections M U) :=
  inferInstanceAs (Module (ringSections R U) (closedSections M U))

/-- The skyscraper `M` at the open point, as a presheaf of `𝒪_X`-modules. -/
noncomputable def openPresheaf : PresheafOfModules.{u} (ringPresheaf R) where
  obj U := ModuleCat.of ((ringPresheaf R).obj U) (openSections M U)
  map {_U V} i := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars ((ringPresheaf R).map i).hom).obj
        (ModuleCat.of ((ringPresheaf R).obj V) (openSections M V)))
    { toFun := fun s h => s (PLift.up (i.unop.le h.down))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The skyscraper `M` at the closed point, as a presheaf of `𝒪_X`-modules. -/
noncomputable def closedPresheaf : PresheafOfModules.{u} (ringPresheaf R) where
  obj U := ModuleCat.of ((ringPresheaf R).obj U) (closedSections M U)
  map {_U V} i := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars ((ringPresheaf R).map i).hom).obj
        (ModuleCat.of ((ringPresheaf R).obj V) (closedSections M V)))
    { toFun := fun s h k => s (PLift.up (i.unop.le h.down)) (PLift.up (i.unop.le k.down))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The skyscraper at the open point has a single section over `∅`. -/
instance subsingleton_openSections_bot (M : Type u) [AddCommGroup M] :
    Subsingleton (openSections M (op (⊥ : Opens space.{u}))) :=
  ⟨fun _ _ => funext fun h => h.down.elim⟩

/-- The skyscraper at the closed point has a single section over `∅`. -/
instance subsingleton_closedSections_bot (M : Type u) [AddCommGroup M] :
    Subsingleton (closedSections M (op (⊥ : Opens space.{u}))) :=
  ⟨fun _ _ => funext fun h => h.down.elim⟩

/-- A presheaf of `𝒪_X`-modules with a single section over `∅` is a sheaf. -/
private theorem isSheaf_presheaf_of_subsingleton_bot {R : (Opens space.{u})ᵒᵖ ⥤ RingCat.{u}}
    (P : PresheafOfModules.{u} R) (h : Subsingleton (P.obj (op ⊥))) :
    Presheaf.IsSheaf (Opens.grothendieckTopology space.{u}) P.presheaf :=
  isSheaf_of_isTerminal _ (IsZero.isTerminal (@AddCommGrpCat.isZero_of_subsingleton _ h))

/-- The skyscraper `M` at the open point is a sheaf. -/
theorem openPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology space.{u}) (openPresheaf R M).presheaf :=
  isSheaf_presheaf_of_subsingleton_bot _ (subsingleton_openSections_bot M)

/-- The skyscraper `M` at the closed point is a sheaf. -/
theorem closedPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology space.{u}) (closedPresheaf R M).presheaf :=
  isSheaf_presheaf_of_subsingleton_bot _ (subsingleton_closedSections_bot M)

/-- The skyscraper `M` at the open point, as a sheaf of `𝒪_X`-modules on `ringedSpace R`. -/
noncomputable def openSheaf : _root_.SheafOfModules.{u} (structureSheafRing (ringedSpace R)) where
  val := openPresheaf R M
  isSheaf := openPresheaf_isSheaf R M

/-- The skyscraper `M` at the closed point, as a sheaf of `𝒪_X`-modules on
`ringedSpace R`. -/
noncomputable def closedSheaf : _root_.SheafOfModules.{u} (structureSheafRing (ringedSpace R)) where
  val := closedPresheaf R M
  isSheaf := closedPresheaf_isSheaf R M

/-- The morphism from the skyscraper at the open point to the skyscraper at the closed point
which is the identity on global sections. On sections over `U` it sends `s` to the constant
function with value `s`; this is linear over the structure sheaf because the structure sheaf is
itself a skyscraper at the open point. -/
noncomputable def skyscraperPresheafHom : openPresheaf R M ⟶ closedPresheaf R M where
  app _ := ModuleCat.ofHom
    { toFun := fun s h _ => s h
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  naturality _ := rfl

/-- The morphism from the skyscraper at the open point to the skyscraper at the closed point
which is the identity on global sections. -/
noncomputable def skyscraperHom : openSheaf R M ⟶ closedSheaf R M :=
  ⟨skyscraperPresheafHom R M⟩

/-- On sections over every open set `U`, the map from the skyscraper at the open point to the
skyscraper at the closed point sending `s` to the constant function with value `s` is
surjective. -/
theorem skyscraperHom_surjective (M : Type u) [AddCommGroup M] (U : (Opens space.{u})ᵒᵖ) :
    Function.Surjective (fun (s : openSections M U) => (fun h _ => s h : closedSections M U)) := by
  intro t
  by_cases hc : Pt.closedPt ∈ (unop U : Opens space.{u})
  · refine ⟨fun h => t h (PLift.up hc), ?_⟩
    funext h k
    rw [plift_ext k (PLift.up hc)]
  · refine ⟨0, ?_⟩
    funext h k
    exact absurd k.down hc

/-- The morphism `skyscraperHom R M` is an epimorphism of sheaves of `𝒪_X`-modules. -/
instance epi_skyscraperHom : Epi (skyscraperHom R M) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (Presheaf.isLocallySurjective_of_surjective _ _ (skyscraperHom_surjective M))

/-! ### The sections supported on the closed point -/

/-- The skyscraper at the closed point has a single section over `{openPt}`. -/
instance subsingleton_closedSections_openSet (M : Type u) [AddCommGroup M] :
    Subsingleton (closedSections M (op openSet.{u})) :=
  ⟨fun _ _ => funext fun _ => funext fun k => nomatch k.down⟩

/-- A section of the skyscraper at the open point whose germ at the open point vanishes is
zero: the open point has a smallest open neighbourhood, on which the sections are the same. -/
theorem openSections_eq_zero (U : Opens space.{u}) (s : (openPresheaf R M).obj (op U))
    (h : ∀ ho : Pt.openPt ∈ U,
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (openSheaf R M)).sectionGerm U
        Pt.openPt ho s = 0) :
    s = 0 := by
  by_cases ho : Pt.openPt ∈ U
  · obtain ⟨W, hoW, j, hj⟩ :=
      ((AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
        (openSheaf R M)).sectionGerm_eq_zero_iff U Pt.openPt ho s).mp (h ho)
    funext hx
    exact congrFun hj (PLift.up hoW)
  · funext hx
    exact absurd hx.down ho

/-- Every section of the skyscraper at the open point whose support is contained in the closed
point is zero: the germ at the open point of such a section vanishes. -/
theorem openSections_eq_zero_of_suppSection (U : Opens space.{u})
    (s : (openPresheaf R M).obj (op U))
    (hs : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (openSheaf R M)).suppSection U s
      ⊆ closedSet.{u} ∩ (U : Set space.{u})) :
    s = 0 := by
  refine openSections_eq_zero R M U s fun ho => ?_
  by_contra hne
  exact nomatch (hs ⟨ho, hne⟩).1

/-- Every section of the subsheaf of sections of the skyscraper at the open point supported on
the closed point is zero. -/
theorem supportedSections_openSheaf_eq_zero (U : (Opens space.{u})ᵒᵖ)
    (t : (supportedSectionsSheaf closedSet.{u} (openSheaf R M)).1.val.obj U) : t = 0 := by
  have hsupp := (mem_supportedSectionsSheafι_range_iff closedSet.{u} (openSheaf R M) U
    ((supportedSectionsSheafι closedSet.{u} (openSheaf R M)).val.app U t)).mp ⟨t, rfl⟩
  refine (supportedSectionsSheaf closedSet.{u} (openSheaf R M)).2.2.1 U ?_
  rw [map_zero]
  exact openSections_eq_zero_of_suppSection R M (unop U) _ hsupp

/-- `H_Z` of the skyscraper at the open point is zero. -/
theorem isZero_supportedSections_openSheaf :
    IsZero ((supportedSectionsFunctor (ringedSpace R) closedSet.{u}).obj (openSheaf R M)) := by
  rw [IsZero.iff_id_eq_zero]
  refine _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext t
  exact supportedSections_openSheaf_eq_zero R M U t

/-- The global section of the skyscraper at the closed point with value `m`. -/
def closedGlobalSection (M : Type u) (m : M) : closedSections M (op (⊤ : Opens space.{u})) :=
  fun _ _ => m

/-- The germ at the open point of the global section `m` of the skyscraper at the closed point
vanishes: that section restricts to zero on `{openPt}`. -/
theorem sectionGerm_closedGlobalSection_openPt (m : M) (ho : Pt.openPt ∈ (⊤ : Opens space.{u})) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (closedSheaf R M)).sectionGerm ⊤
      Pt.openPt ho (closedGlobalSection M m) = 0 :=
  ((AlgebraicGeometry.SheafOfModules.moduleSheafOfModules
    (closedSheaf R M)).sectionGerm_eq_zero_iff ⊤ Pt.openPt ho
      (closedGlobalSection M m)).mpr
    ⟨openSet, rfl, homOfLE le_top,
      @Subsingleton.elim (closedSections M (op openSet.{u}))
        (subsingleton_closedSections_openSet M) _ _⟩

/-- The support of the global section `m` of the skyscraper at the closed point is contained in
the closed point. -/
theorem suppSection_closedGlobalSection (m : M) :
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules (closedSheaf R M)).suppSection ⊤
      (closedGlobalSection M m) ⊆ closedSet.{u} ∩ ((⊤ : Opens space.{u}) : Set space.{u}) := by
  rintro x ⟨hxU, hne⟩
  cases x
  · exact ⟨rfl, hxU⟩
  · exact absurd (sectionGerm_closedGlobalSection_openPt R M m hxU) hne

/-- The global section of the skyscraper at the closed point with value a nonzero `m` is
nonzero. -/
theorem closedGlobalSection_ne_zero (m : M) (hm : m ≠ 0) :
    closedGlobalSection M m ≠ (0 : closedSections M (op (⊤ : Opens space.{u}))) := fun h =>
  hm (congrFun (congrFun h (PLift.up trivial)) (PLift.up trivial))

/-- `H_Z` of the skyscraper at the closed point is nonzero: its global section `m` is supported
on the closed point. -/
theorem not_isZero_supportedSections_closedSheaf (m : M) (hm : m ≠ 0) :
    ¬ IsZero ((supportedSectionsFunctor (ringedSpace R) closedSet.{u}).obj (closedSheaf R M)) := by
  intro h
  obtain ⟨t, ht⟩ := (mem_supportedSectionsSheafι_range_iff closedSet.{u} (closedSheaf R M)
    (op ⊤) (closedGlobalSection M m)).mpr (suppSection_closedGlobalSection R M m)
  have hι : supportedSectionsSheafι closedSet.{u} (closedSheaf R M) = 0 := h.eq_of_src _ _
  refine closedGlobalSection_ne_zero M m hm ?_
  rw [← ht, hι]
  rfl

/-! ### `H_Z` is left exact but not exact -/

/-- `H_Z(F)` on the closed subset `Z` is zero exactly when the subsheaf of sections of `F`
supported on `Z` is zero. -/
private theorem isZero_supportedSectionsOnClosedFunctor_obj_iff
    (X : AlgebraicGeometry.RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    IsZero ((supportedSectionsOnClosedFunctor X Z hZ).obj F) ↔
      IsZero ((supportedSectionsFunctor X Z).obj F) := by
  have iso := (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).app F
  refine ⟨fun h => IsZero.of_iso (Functor.map_isZero (modulePushforward
    (RingedSpace.inverseImageProjection X (ClosedImmersionSheaves.closedSubsetInclusion Z))) h)
    iso.symm, fun h => ?_⟩
  rw [IsZero.iff_id_eq_zero]
  refine (fullyFaithfulModulePushforwardClosedSubset X Z hZ).map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 (IsZero.of_iso h iso)

/-- **Stacks 0G6N.** The functor `H_Z` does not preserve the epimorphism from the skyscraper at
the open point onto the skyscraper at the closed point: the source is sent to zero and the
target is not. -/
theorem not_epi_map_skyscraperHom (m : M) (hm : m ≠ 0) :
    ¬ Epi ((supportedSectionsOnClosedFunctor (ringedSpace R) closedSet.{u}
      isClosed_closedSet).map (skyscraperHom R M)) := by
  intro hepi
  have hF := (isZero_supportedSectionsOnClosedFunctor_obj_iff _ _ isClosed_closedSet _).2
    (isZero_supportedSections_openSheaf R M)
  have hzero : (supportedSectionsOnClosedFunctor (ringedSpace R) closedSet.{u}
      isClosed_closedSet).map (skyscraperHom R M) = 0 := hF.eq_of_src _ _
  have hG : IsZero ((supportedSectionsOnClosedFunctor (ringedSpace R) closedSet.{u}
      isClosed_closedSet).obj (closedSheaf R M)) := by
    rw [IsZero.iff_id_eq_zero]
    refine (cancel_epi ((supportedSectionsOnClosedFunctor (ringedSpace R) closedSet.{u}
      isClosed_closedSet).map (skyscraperHom R M))).1 ?_
    rw [hzero, zero_comp, zero_comp]
  exact not_isZero_supportedSections_closedSheaf R M m hm
    ((isZero_supportedSectionsOnClosedFunctor_obj_iff _ _ _ _).1 hG)

/-- The functor `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of sections supported on a closed subset does not
preserve epimorphisms in general: on the two-point Sierpinski space with `Z` the closed point,
the skyscraper at the open point surjects onto the skyscraper at the closed point, `H_Z` of the
source is zero and `H_Z` of the target is not. -/
@[stacks 0G6N "H_Z does not preserve epimorphisms in general"]
theorem exists_epi_not_epi_supportedSectionsOnClosedFunctor_map :
    ∃ (X : AlgebraicGeometry.RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
      (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) (φ : F ⟶ G),
      Epi φ ∧ ¬ Epi ((supportedSectionsOnClosedFunctor X Z hZ).map φ) :=
  ⟨ringedSpace (ULift.{u} ℤ), closedSet.{u}, isClosed_closedSet,
    openSheaf (ULift.{u} ℤ) (ULift.{u} ℤ), closedSheaf (ULift.{u} ℤ) (ULift.{u} ℤ),
    skyscraperHom (ULift.{u} ℤ) (ULift.{u} ℤ), inferInstance,
    not_epi_map_skyscraperHom (ULift.{u} ℤ) (ULift.{u} ℤ) 1 one_ne_zero⟩

/-- The functor `H_Z : Mod(𝒪_X) ⥤ Mod(𝒪_X|_Z)` of sections supported on a closed subset is left
exact
(`Stacks.Cohomology.SupportedComplexes.supportedSectionsOnClosedFunctor_preservesFiniteLimits`)
but is *not* exact in general: it does not preserve finite colimits, since a functor preserving
finite colimits preserves epimorphisms, which `H_Z` does not. -/
@[stacks 0G6N "H_Z is not exact in general"]
theorem exists_not_preservesFiniteColimits_supportedSectionsOnClosedFunctor :
    ∃ (X : AlgebraicGeometry.RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z),
      ¬ PreservesFiniteColimits (supportedSectionsOnClosedFunctor X Z hZ) := by
  refine ⟨ringedSpace (ULift.{u} ℤ), closedSet.{u}, isClosed_closedSet, fun h => ?_⟩
  have : PreservesColimitsOfShape WalkingSpan
      (supportedSectionsOnClosedFunctor (ringedSpace (ULift.{u} ℤ)) closedSet.{u}
        isClosed_closedSet) := h.preservesFiniteColimits _
  exact not_epi_map_skyscraperHom (ULift.{u} ℤ) (ULift.{u} ℤ) 1 one_ne_zero
    (Functor.map_epi _ _)

end Stacks.SupportedSectionsCounterexample

end
