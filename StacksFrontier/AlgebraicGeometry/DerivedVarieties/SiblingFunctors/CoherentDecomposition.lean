module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Decomposition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PointSupportDecomposition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.SkyscraperUnit
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MorphismVanishing
public import StacksFrontier.AlgebraicGeometry.Groupoids.CoherentColimit
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic

/-!
# The coherent modules on a Noetherian scheme split along its isolated points

Let `X` be a scheme whose underlying space is Noetherian. A point `x` of `X` is *isolated* if
`{x}` is open and closed; there are finitely many of them, each one being an irreducible
component of `X`, and together they form an open and closed subset `X₀` of `X`. Every coherent
`𝒪_X`-module `𝓕` is the direct sum of its extension by zero from the complement `X₁` of `X₀` and
of its extensions by zero from the isolated points, and there are no nonzero morphisms between
coherent modules supported on disjoint open and closed subsets. This is the decomposition
`X = X₁ ⊔ ∐_{x ∈ X₀} {x}` of the proof of [Stacks, Tag 0G0C], as an orthogonal decomposition of
the abelian category `Coh(𝒪_X)` (`AlgebraicGeometry.OrthogonalDecomposition`).

When `X` is reduced the local ring at an isolated point is a field, so the coherent modules
supported at an isolated point form a semisimple category: every epimorphism between them splits.

## Main definitions

* `AlgebraicGeometry.isolatedPoints`: the points `x` with `{x}` open and closed.
* `AlgebraicGeometry.cohDecomposition`: the orthogonal decomposition of `Coh(𝒪_X)`, indexed by
  `Option (Fin n)` for an enumeration of the isolated points.

## Main results

* `AlgebraicGeometry.isolatedPoints_finite`, `AlgebraicGeometry.isClopen_isolatedPoints`.
* `AlgebraicGeometry.mem_isolatedPoints_of_mem_genericPoints_of_isClosed`: a generic point of an
  irreducible component which is a closed point is isolated.
* `AlgebraicGeometry.exists_section_of_supp_subset_singleton`: on a reduced scheme, an
  epimorphism of modules supported at an isolated point splits.

## References

* [Stacks Project, Tag 0G0C](https://stacks.math.columbia.edu/tag/0G0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

open ExtensionByZeroModules

/-! ### Isolated points -/

section IsolatedPoints

variable (X : Scheme.{u})

/-- **The isolated points of `X`**: the points `x` for which `{x}` is open and closed. -/
def isolatedPoints : Set X := {x | IsClopen ({x} : Set X)}

variable {X}

/-- An isolated point is an irreducible component of `X`. -/
lemma singleton_mem_irreducibleComponents_of_isClopen {x : X} (hx : IsClopen ({x} : Set X)) :
    ({x} : Set X) ∈ irreducibleComponents X := by
  refine ⟨isIrreducible_singleton, fun Z hZ hxZ => ?_⟩
  have hsub : Z ⊆ closure (Z ∩ {x}) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hZ.isPreirreducible hx.isOpen
      ⟨x, hxZ rfl, rfl⟩
  intro z hz
  simpa [hx.isClosed.closure_eq] using closure_mono Set.inter_subset_right (hsub hz)

/-- A Noetherian space has finitely many isolated points. -/
lemma isolatedPoints_finite [NoetherianSpace X] : (isolatedPoints X).Finite := by
  refine Set.Finite.of_finite_image (f := fun x : X => ({x} : Set X)) ?_
    (Set.injOn_of_injective (fun x y h => Set.singleton_injective h))
  refine (NoetherianSpace.finite_irreducibleComponents (α := X)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  exact singleton_mem_irreducibleComponents_of_isClopen hx

/-- The isolated points form an open set. -/
lemma isOpen_isolatedPoints : IsOpen (isolatedPoints X) :=
  isOpen_iff_forall_mem_open.2 fun x hx => ⟨{x}, Set.singleton_subset_iff.2 hx, hx.isOpen, rfl⟩

/-- In a Noetherian space the isolated points form a closed set. -/
lemma isClosed_isolatedPoints [NoetherianSpace X] : IsClosed (isolatedPoints X) := by
  simpa using isolatedPoints_finite.isClosed_biUnion fun x (hx : x ∈ isolatedPoints X) =>
    hx.isClosed

/-- In a Noetherian space the isolated points form an open and closed set. -/
lemma isClopen_isolatedPoints [NoetherianSpace X] : IsClopen (isolatedPoints X) :=
  ⟨isClosed_isolatedPoints, isOpen_isolatedPoints⟩

/-- **A generic point of an irreducible component which is closed is isolated.** -/
lemma mem_isolatedPoints_of_mem_genericPoints_of_isClosed [NoetherianSpace X] {x : X}
    (hx : x ∈ genericPoints X) (hcl : IsClosed ({x} : Set X)) : x ∈ isolatedPoints X := by
  have hcomp : ({x} : Set X) ∈ irreducibleComponents X := hcl.closure_eq ▸ hx
  have hcompl : ({x} : Set X)ᶜ = ⋃ C ∈ irreducibleComponents X \ {({x} : Set X)}, C := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_sdiff,
      exists_prop]
    refine ⟨fun hy => ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
      fun h => hy (h ▸ mem_irreducibleComponent : y ∈ ({x} : Set X))⟩, mem_irreducibleComponent⟩,
      ?_⟩
    rintro ⟨C, ⟨hC, hCx⟩, hyC⟩ rfl
    have hle : ({y} : Set X) ⊆ C := Set.singleton_subset_iff.mpr hyC
    exact hCx ((hcomp.2 hC.1 hle).antisymm hle)
  refine ⟨hcl, isClosed_compl_iff.mp ?_⟩
  rw [hcompl]
  exact ((NoetherianSpace.finite_irreducibleComponents (α := X)).subset
    Set.sdiff_subset).isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

end IsolatedPoints

/-! ### The pieces of `X` -/

section Pieces

variable (X : Scheme.{u}) [IsNoetherian X]

/-- A Noetherian scheme has finitely many isolated points. -/
instance finite_isolatedPoints : Finite (isolatedPoints X) :=
  (isolatedPoints_finite (X := X)).to_subtype

/-- An enumeration of the isolated points of `X`. -/
def isolatedPointsEnum : Fin (Nat.card (isolatedPoints X)) ≃ isolatedPoints X :=
  (Finite.equivFin _).symm

/-- The open and closed pieces of the decomposition of `X`: the complement of the isolated points,
and each isolated point. -/
def cohDecompositionOpen : Option (Fin (Nat.card (isolatedPoints X))) → X.Opens
  | none => ⟨(isolatedPoints X)ᶜ, isClosed_isolatedPoints.isOpen_compl⟩
  | some j => ⟨{(isolatedPointsEnum X j : X)}, (isolatedPointsEnum X j).2.isOpen⟩

variable {X}

/-- The piece indexed by `none` is the complement of the isolated points. -/
lemma mem_cohDecompositionOpen_none {y : X} :
    y ∈ cohDecompositionOpen X none ↔ y ∉ isolatedPoints X := Iff.rfl

/-- The piece indexed by `some j` is the `j`-th isolated point. -/
lemma mem_cohDecompositionOpen_some {y : X} {j : Fin (Nat.card (isolatedPoints X))} :
    y ∈ cohDecompositionOpen X (some j) ↔ y = (isolatedPointsEnum X j : X) := Iff.rfl

/-- The pieces cover `X`. -/
lemma exists_mem_cohDecompositionOpen (y : X) : ∃ i, y ∈ cohDecompositionOpen X i := by
  by_cases hy : y ∈ isolatedPoints X
  · refine ⟨some ((isolatedPointsEnum X).symm ⟨y, hy⟩), ?_⟩
    rw [mem_cohDecompositionOpen_some, Equiv.apply_symm_apply]
  · exact ⟨none, hy⟩

/-- The pieces are pairwise disjoint. -/
lemma eq_of_mem_cohDecompositionOpen {y : X} {i k : Option (Fin (Nat.card (isolatedPoints X)))}
    (hi : y ∈ cohDecompositionOpen X i) (hk : y ∈ cohDecompositionOpen X k) : i = k := by
  rcases i with _ | i <;> rcases k with _ | k <;>
    simp only [mem_cohDecompositionOpen_none, mem_cohDecompositionOpen_some] at hi hk
  · rfl
  · exact (hi (hk ▸ (isolatedPointsEnum X k).2)).elim
  · exact (hk (hi ▸ (isolatedPointsEnum X i).2)).elim
  · exact congrArg some ((isolatedPointsEnum X).injective (Subtype.ext (hi.symm.trans hk)))

omit [IsNoetherian X] in
/-- The support is invariant under isomorphism. -/
lemma supp_eq_of_iso {M N : X.Modules} (e : M ≅ N) :
    SheafOfModules.supp M = SheafOfModules.supp N := by
  ext y
  rw [← not_iff_not, Scheme.Modules.notMem_supp_iff_isZero_stalk,
    Scheme.Modules.notMem_supp_iff_isZero_stalk]
  exact ((Scheme.Modules.stalkFunctor X y).mapIso e).isZero_iff

/-- **A morphism between coherent modules with disjoint supports is zero.** -/
lemma eq_zero_of_disjoint_supp {M N : X.Modules} (hM : M.IsCoherent) (hN : N.IsCoherent)
    (h : Disjoint (SheafOfModules.supp M) (SheafOfModules.supp N)) (f : M ⟶ N) : f = 0 := by
  have := GroupoidScheme.isQuasicoherent_of_isCoherent M hM
  have := GroupoidScheme.isQuasicoherent_of_isCoherent N hN
  apply eq_zero_of_stalkFunctor_map_eq_zero_on_associatedPoints
  intro x hx
  have hxN := associatedPoints_subset_support N hx
  have hxM : x ∉ SheafOfModules.supp M := fun hxM => h.ne_of_mem hxM hxN rfl
  exact ((Scheme.Modules.notMem_supp_iff_isZero_stalk M x).mp hxM).eq_of_src _ _

/-- The extension by zero from the `i`-th piece of the restriction of `M` to it. -/
abbrev pieceSummand (i : Option (Fin (Nat.card (isolatedPoints X)))) (M : X.Modules) :
    X.Modules :=
  (jShriek (cohDecompositionOpen X i) X.ringCatSheaf).obj
    ((jStar (cohDecompositionOpen X i) X.ringCatSheaf).obj M)

/-- The counit `j_! j^* M ⟶ M` for the `i`-th piece. -/
abbrev pieceSummandCounit (i : Option (Fin (Nat.card (isolatedPoints X)))) (M : X.Modules) :
    pieceSummand i M ⟶ M :=
  (jShriekAdjunction (cohDecompositionOpen X i) X.ringCatSheaf).counit.app M

/-- The stalk of `pieceSummand i M` vanishes off the `i`-th piece. -/
lemma isZero_stalk_pieceSummand (i : Option (Fin (Nat.card (isolatedPoints X)))) (M : X.Modules)
    (y : X) (hy : y ∉ cohDecompositionOpen X i) :
    IsZero ((Scheme.Modules.stalkFunctor X y).obj (pieceSummand i M)) :=
  (_root_.AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff X.ringCatSheaf y _).2
    (isZero_stalk_jShriek (cohDecompositionOpen X i) X.ringCatSheaf _ y hy)

/-- On the `i`-th piece the counit `pieceSummandCounit i M` is an isomorphism on stalks. -/
lemma isIso_stalk_pieceSummandCounit (i : Option (Fin (Nat.card (isolatedPoints X))))
    (M : X.Modules) (y : X) (hy : y ∈ cohDecompositionOpen X i) :
    IsIso ((Scheme.Modules.stalkFunctor X y).map (pieceSummandCounit i M)) := by
  have : IsIso ((forget₂ _ AddCommGrpCat.{u}).map
      ((Scheme.Modules.stalkFunctor X y).map (pieceSummandCounit i M))) :=
    isIso_stalk_counit_app_of_mem (cohDecompositionOpen X i) X.ringCatSheaf M y hy
  exact isIso_of_reflects_iso _ (forget₂ _ AddCommGrpCat.{u})

/-- `pieceSummand i M` is supported in the `i`-th piece. -/
lemma supp_pieceSummand_subset (i : Option (Fin (Nat.card (isolatedPoints X))))
    (M : X.Modules) :
    SheafOfModules.supp (pieceSummand i M) ⊆ (cohDecompositionOpen X i : Set X) := fun y =>
  not_imp_not.mp fun h =>
    (Scheme.Modules.notMem_supp_iff_isZero_stalk _ y).mpr (isZero_stalk_pieceSummand i M y h)

/-- **Every module is the sum of its extensions by zero from the pieces**: the sum of the counits
is an isomorphism. -/
instance isIso_biproduct_desc_pieceSummandCounit (M : X.Modules) :
    IsIso (biproduct.desc fun i => pieceSummandCounit i M) := by
  let ι : X.Modules ⥤ SheafOfModules.{u} X.ringCatSheaf := { obj := fun M => M, map := fun f => f }
  let ιff : ι.FullyFaithful := { preimage := fun f => f }
  suffices IsIso (ι.map (biproduct.desc fun i => pieceSummandCounit i M)) from
    ιff.isIso_of_isIso_map _
  have : ι.Additive := ⟨rfl⟩
  let Φ : ∀ y : X, X.Modules ⥤ _ := fun y =>
    ι ⋙ _root_.AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y
  rw [_root_.AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map]
  intro y
  change IsIso ((Φ y).map (biproduct.desc fun i => pieceSummandCounit i M))
  obtain ⟨i, hi⟩ := exists_mem_cohDecompositionOpen y
  have : IsIso ((Φ y).map (pieceSummandCounit i M)) := isIso_stalk_pieceSummandCounit i M y hi
  exact CategoryTheory.Limits.isIso_map_biproduct_desc_of_isZero
    (Φ y) (fun i => pieceSummandCounit i M) i
    fun k hk => isZero_stalk_pieceSummand k M y fun hk' =>
      hk (eq_of_mem_cohDecompositionOpen hk' hi)

/-- The extension by zero from a piece of the restriction of a coherent module is coherent. -/
lemma isCoherent_pieceSummand (i : Option (Fin (Nat.card (isolatedPoints X)))) (M : X.Modules)
    (hM : M.IsCoherent) : (pieceSummand i M).IsCoherent := by
  let p : M ⟶ pieceSummand i M :=
    inv (biproduct.desc fun i => pieceSummandCounit i M) ≫ biproduct.π _ i
  have hsp : pieceSummandCounit i M ≫ p = 𝟙 _ := by
    simp only [p]
    rw [← biproduct.ι_desc (fun i => pieceSummandCounit i M) i, Category.assoc,
      IsIso.hom_inv_id_assoc, biproduct.ι_π_self]
  exact Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.isCoherent_of_comp_eq_id
    (pieceSummandCounit i M) p hsp hM

end Pieces

/-! ### Modules supported at an isolated point -/

section IsolatedPoint

open Stacks.AlgebraicGeometry.DerivedVarieties.Orlov in
/-- **A module supported at a closed point `x` is the skyscraper of its stalk**: the unit of the
stalk-skyscraper adjunction is an isomorphism. -/
lemma isIso_stalkSkyscraperAdjunction_unit_app {X : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) (M : SheafOfModules.{u} X.ringCatSheaf)
    (hM : SheafOfModules.supp M ⊆ {x}) :
    IsIso ((SheafOfModules.stalkSkyscraperAdjunction X.ringCatSheaf x).unit.app M) := by
  rw [_root_.AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map]
  intro y
  by_cases hy : y = x
  · subst hy
    have := isIso_stalkSkyscraperAdjunction_counit X y
    exact IsIso.of_isIso_fac_right
      ((SheafOfModules.stalkSkyscraperAdjunction X.ringCatSheaf y).left_triangle_components M)
  · have h0 : IsZero ((SheafOfModules.stalkFunctor X.ringCatSheaf y).obj M) :=
      (Scheme.Modules.notMem_supp_iff_isZero_stalk M y).mp fun h => hy (hM h)
    have h1 := isZero_stalkFunctor_skyscraperObj_of_ne X x hx hy
      ((SheafOfModules.stalkFunctor X.ringCatSheaf x).obj M)
    exact h0.isIso h1 _

/-- An isolated point is maximal for the specialization order. -/
lemma isMax_of_isClopen {X : Scheme.{u}} {x : X} (hx : IsClopen ({x} : Set X)) : IsMax x := by
  intro y hxy
  rw [Set.mem_singleton_iff.mp ((show y ⤳ x from hxy).mem_open hx.isOpen rfl)]

/-- **The local ring at an isolated point of a reduced scheme is a field.** -/
lemma isField_stalk_of_isClopen {X : Scheme.{u}} [IsReduced X] {x : X}
    (hx : IsClopen ({x} : Set X)) :
    IsField (TopCat.Presheaf.stalk (C := RingCat.{u}) X.ringCatSheaf.obj x) :=
  MulEquiv.isField (isField_stalk_of_isMax (isMax_of_isClopen hx))
    (StacksDraft.StalkRingComparison.stalkRingEquiv X x).toMulEquiv

/-- **On a reduced scheme, an epimorphism between modules supported at an isolated point
splits.** -/
lemma exists_section_of_supp_subset_singleton {X : Scheme.{u}} [IsReduced X] {x : X}
    (hx : IsClopen ({x} : Set X)) {M M' : SheafOfModules.{u} X.ringCatSheaf}
    (hM : SheafOfModules.supp M ⊆ {x}) (hM' : SheafOfModules.supp M' ⊆ {x}) (p : M ⟶ M')
    [Epi p] : ∃ s : M' ⟶ M, s ≫ p = 𝟙 M' := by
  let adj := SheafOfModules.stalkSkyscraperAdjunction X.ringCatSheaf x
  have hη := isIso_stalkSkyscraperAdjunction_unit_app x hx.isClosed M hM
  have hη' := isIso_stalkSkyscraperAdjunction_unit_app x hx.isClosed M' hM'
  let px := (SheafOfModules.stalkFunctor X.ringCatSheaf x).map p
  have hpx : Function.Surjective px := (ModuleCat.epi_iff_surjective px).mp inferInstance
  let := (isField_stalk_of_isClopen hx).toField
  obtain ⟨g, hg⟩ := px.hom.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hpx)
  let sx : (SheafOfModules.stalkFunctor X.ringCatSheaf x).obj M' ⟶
      (SheafOfModules.stalkFunctor X.ringCatSheaf x).obj M := ModuleCat.ofHom g
  have hsx : sx ≫ px = 𝟙 _ := ModuleCat.hom_ext hg
  refine ⟨adj.homEquiv _ _ sx ≫ inv (adj.unit.app M), ?_⟩
  have hmono : Mono (adj.unit.app M') := @IsIso.mono_of_iso _ _ _ _ _ hη'
  rw [← @cancel_mono _ _ _ _ _ (adj.unit.app M') hmono]
  have hnat : p ≫ adj.unit.app M' = adj.unit.app M ≫ (SheafOfModules.skyscraperFunctor
      X.ringCatSheaf x).map px := adj.unit.naturality p
  simp only [Category.assoc, hnat, IsIso.inv_hom_id_assoc, Category.id_comp]
  rw [← adj.homEquiv_naturality_right, hsx, adj.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end IsolatedPoint

/-! ### The decomposition of `Coh(𝒪_X)` -/

section Decomposition

attribute [local instance 100000] CoherentAbelian.coherentModulesAbelian

/-- The finite biproducts of `Coh(𝒪_X)`, from its abelian structure. -/
abbrev cohHasFiniteBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts (SheafOfModules.CoherentModules X.ringCatSheaf) :=
  Abelian.hasFiniteBiproducts

attribute [local instance] cohHasFiniteBiproducts

variable (X : Scheme.{u}) [IsNoetherian X]

/-- The pieces of `Coh(𝒪_X)`: the coherent modules supported in one of the open and closed
pieces of `X`. -/
def cohPiece (i : Option (Fin (Nat.card (isolatedPoints X)))) :
    ObjectProperty (SheafOfModules.CoherentModules X.ringCatSheaf) :=
  fun G => SheafOfModules.supp G.obj ⊆ (cohDecompositionOpen X i : Set X)

variable {X}

/-- Each piece of `Coh(𝒪_X)` is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_cohPiece (i : Option (Fin (Nat.card (isolatedPoints X)))) :
    (cohPiece X i).IsClosedUnderIsomorphisms where
  of_iso {G G'} e hG := by
    have h : SheafOfModules.supp G.obj = SheafOfModules.supp G'.obj :=
      supp_eq_of_iso (M := G.obj) (N := G'.obj) ((ObjectProperty.ι _).mapIso e)
    change SheafOfModules.supp G'.obj ⊆ _
    rw [← h]
    exact hG

/-- There are no nonzero morphisms between coherent modules in different pieces. -/
lemma cohPiece_hom_eq_zero (i j : Option (Fin (Nat.card (isolatedPoints X)))) (hij : i ≠ j)
    {G G' : SheafOfModules.CoherentModules X.ringCatSheaf} (hG : cohPiece X i G)
    (hG' : cohPiece X j G') (f : G ⟶ G') : f = 0 :=
  ObjectProperty.hom_ext _ <| eq_zero_of_disjoint_supp G.property G'.property
    (Set.disjoint_left.2 fun _ hy hy' => hij (eq_of_mem_cohDecompositionOpen (hG hy) (hG' hy')))
    f.hom

/-- **Every coherent module is the sum of its extensions by zero from the pieces.** -/
lemma exists_iso_biproduct_cohPiece (G : SheafOfModules.CoherentModules X.ringCatSheaf) :
    ∃ Y : Option (Fin (Nat.card (isolatedPoints X))) →
        SheafOfModules.CoherentModules X.ringCatSheaf,
      (∀ i, cohPiece X i (Y i)) ∧ Nonempty (G ≅ ⨁ Y) := by
  let Y : Option (Fin (Nat.card (isolatedPoints X))) →
      SheafOfModules.CoherentModules X.ringCatSheaf :=
    fun i => ⟨pieceSummand i G.obj, isCoherent_pieceSummand i G.obj G.property⟩
  exact ⟨Y, fun i => supp_pieceSummand_subset i G.obj,
    ⟨(ObjectProperty.fullyFaithfulι _).preimageIso <|
      (@asIso _ _ _ _ _ (isIso_biproduct_desc_pieceSummandCounit G.obj)).symm ≪≫
        ((ObjectProperty.ι _).mapBiproduct Y).symm⟩⟩

variable (X)

/-- **The orthogonal decomposition of `Coh(𝒪_X)`** along the isolated points of `X`. -/
def cohDecomposition :
    OrthogonalDecomposition (SheafOfModules.CoherentModules X.ringCatSheaf)
      (Option (Fin (Nat.card (isolatedPoints X)))) where
  piece := cohPiece X
  isClosedUnderIsomorphisms_piece := inferInstance
  hom_eq_zero := cohPiece_hom_eq_zero
  exists_iso_biproduct := exists_iso_biproduct_cohPiece

end Decomposition

end AlgebraicGeometry

end
