module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite

/-!
# Subterminal sheaves on the spaces-étale site of an algebraic space

A *subterminal* sheaf on the spaces-étale site of an algebraic space `X` is a subfunctor of
the terminal sheaf: a sheaf with at most one section over every algebraic space étale over
`X`. Such a sheaf is the same thing as an open subspace of `X` — the sheaf of those étale
spaces over `X` whose structure morphism factors through the subspace — and the open subspace
is unique.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleTerminalSheaf` is the terminal sheaf of sets on the
  spaces-étale site of `X`, whose subfunctors are the subterminal sheaves.
* `AlgebraicGeometry.Space.openSubspaceSheaf` is the subterminal sheaf attached to an open
  subspace: it has a section over an étale space exactly when the structure morphism of that
  space factors through the subspace.

## Main results

* `AlgebraicGeometry.Space.existsUnique_openSubspace_of_subterminalSheaf`: every subterminal
  sheaf on the spaces-étale site of `X` is `openSubspaceSheaf` of a unique open subspace.

## Implementation notes

An open subspace is a subfunctor of the presheaf underlying `X` whose inclusion is an open
immersion of algebraic spaces (Stacks 02YU, part (2)), and the subterminal sheaf is a
subfunctor of the terminal sheaf, so the conclusion is an equality of subfunctors rather than
an unspecified isomorphism.

Given a subterminal sheaf `F`, the open subspace is produced from the set of points of `X`
lying in the image of some étale space over which `F` has a section. That set is open because
an étale morphism is open on points (Stacks 03IR), and it is the point set of a unique open
subspace by the order isomorphism of Stacks 03BZ. Conversely that subspace has a section of
`F`: the étale spaces over which `F` has a section cover it, and `F` is a sheaf, so the
sections amalgamate — compatibility is automatic because the terminal sheaf has at most one
section over each object. Factorization through the subspace is matched with containment of
point sets by Stacks 03IE, and uniqueness follows because the point set of the subspace is
determined by `F`.

## References

* [Stacks Project, Tag 04K8](https://stacks.math.columbia.edu/tag/04K8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- The terminal sheaf of sets on the spaces-étale site of `X`: it has exactly one section
over every algebraic space étale over `X`. Its subfunctors are the subterminal sheaves. -/
abbrev spacesEtaleTerminalSheaf : (SpacesEtale B S hS X)ᵒᵖ ⥤ Type :=
  (Sheaf.terminal (SpacesEtale.topology B S hS X) Types.isTerminalPUnit).obj

/-- An open subspace of `X`, read as an object of the spaces-étale site: an open immersion is
étale. -/
noncomputable def openSubspaceObject
    (W : {W : Subfunctor X.1 // IsOpenSubspace B S hS W}) :
    SpacesEtale B S hS X := by
  let Y : AlgebraicSpaces B S hS := ⟨W.1.toFunctor, W.2.1⟩
  let i : Y ⟶ X := ObjectProperty.homMk W.1.ι
  have hi : IsEtale B S hS i.hom := by
    have hprop : (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) ≤
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
      fun _ _ g (_ : AlgebraicGeometry.IsOpenImmersion g) ↦ inferInstance
    have hprop' :
        MorphismProperty.inverseImage
            (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS) ≤
          MorphismProperty.inverseImage
            (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS) := fun _ _ g hg ↦ hprop _ hg
    exact isEtale_of_presheaf_etale B S hS
      (MorphismProperty.relative_monotone hprop' _ W.2.2)
  exact ⟨Over.mk i, hi⟩

/-- The set of points of `X` over which a subterminal sheaf is supported: those lying in the
image of an étale space over which the sheaf has a section. -/
noncomputable def supportedPoints (F : Subfunctor (spacesEtaleTerminalSheaf B S hS X)) :
    Set (points B S hS X.1) :=
  {x | ∃ (U : SpacesEtale B S hS X) (_s : F.obj (op U))
      (y : points B S hS ((SpacesEtale.toSpaces B S hS X).obj U).1),
      pointsMap B S hS ((SpacesEtale.toSpaces B S hS X).obj U).1 U.1.hom.hom y = x}

/-- The support of a subterminal sheaf is open: it is a union of images of étale morphisms,
each open by Stacks 03IR. -/
theorem isOpen_supportedPoints (F : Subfunctor (spacesEtaleTerminalSheaf B S hS X)) :
    @IsOpen _ (pointTopology B S hS X.1) (supportedPoints B S hS X F) := by
  let _ : TopologicalSpace (points B S hS X.1) := pointTopology B S hS X.1
  have hunion : supportedPoints B S hS X F =
      ⋃ U : SpacesEtale B S hS X, ⋃ _s : F.obj (op U),
        Set.range (pointsMap B S hS ((SpacesEtale.toSpaces B S hS X).obj U).1
          U.1.hom.hom) := by
    ext x
    simp only [supportedPoints, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range]
  rw [hunion]
  refine isOpen_iUnion fun U ↦ ?_
  let _ : TopologicalSpace (points B S hS U.obj.left.obj) :=
    pointTopology B S hS U.obj.left.obj
  refine isOpen_iUnion fun _s ↦ ?_
  exact (isOpenMap_pointsMap_of_isEtale B S hS U.1.hom.hom
    ((SpacesEtale.toSpaces B S hS X).obj U).property X.property U.2).isOpen_range

/-- A factorization of the structure morphism of an étale space through an open subspace, read
as a morphism of the spaces-étale site. -/
noncomputable def siteArrowOfFactor (W : {W : Subfunctor X.1 // IsOpenSubspace B S hS W})
    (U : SpacesEtale B S hS X) (g : U.1.left.1 ⟶ W.1.toFunctor)
    (hg : g ≫ W.1.ι = U.1.hom.hom) :
    U ⟶ openSubspaceObject B S hS X W :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk g)
    (ObjectProperty.hom_ext _ hg))

/-- The open subspace of `X` cut out by the support of a subterminal sheaf. -/
noncomputable def supportedOpenSubspace (F : Subfunctor (spacesEtaleTerminalSheaf B S hS X)) :
    {W : Subfunctor X.1 // IsOpenSubspace B S hS W} :=
  let _ : TopologicalSpace (points B S hS X.1) := pointTopology B S hS X.1
  (openSubspacesOrderIso B S hS X.1 X.property).symm
    ⟨supportedPoints B S hS X F, isOpen_supportedPoints B S hS X F⟩

/-- The points of the open subspace cut out by a subterminal sheaf are its support. -/
theorem supportedOpenSubspace_points (F : Subfunctor (spacesEtaleTerminalSheaf B S hS X)) :
    Set.range (pointsMap B S hS (supportedOpenSubspace B S hS X F).1.toFunctor
      (supportedOpenSubspace B S hS X F).1.ι) = supportedPoints B S hS X F := by
  let _ : TopologicalSpace (points B S hS X.1) := pointTopology B S hS X.1
  rw [← openSubspacesOrderIso_apply B S hS X.1 X.property
    (supportedOpenSubspace B S hS X F)]
  simp [supportedOpenSubspace]

/-- An étale space over which a subterminal sheaf has a section maps into any open subspace
whose points are the support of that sheaf. -/
theorem supportedObject_factors (F : Subfunctor (spacesEtaleTerminalSheaf B S hS X))
    (W : {W : Subfunctor X.1 // IsOpenSubspace B S hS W})
    (hWpoints : Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
      supportedPoints B S hS X F)
    (U : SpacesEtale B S hS X) (s : F.obj (op U)) :
    ∃ g : U.1.left.1 ⟶ W.1.toFunctor, g ≫ W.1.ι = U.1.hom.hom := by
  refine (factorsThrough_openSubspace_iff_points B S hS X.property
    ((SpacesEtale.toSpaces B S hS X).obj U).property W.1 W.2 U.1.hom.hom).2 ?_
  rintro x ⟨y, rfl⟩
  rw [hWpoints]
  exact ⟨U, s, y, rfl⟩

/-- The subterminal sheaf attached to an open subspace of `X`: it has a section over an étale
space exactly when the structure morphism of that space factors through the subspace. -/
noncomputable def openSubspaceSheaf (W : {W : Subfunctor X.1 // IsOpenSubspace B S hS W}) :
    Subfunctor (spacesEtaleTerminalSheaf B S hS X) where
  obj U := {_x | ∃ g : U.unop.1.left.1 ⟶ W.1.toFunctor, g ≫ W.1.ι = U.unop.1.hom.hom}
  map {_ _} f := by
    rintro x ⟨g, hg⟩
    refine ⟨f.unop.hom.left.hom ≫ g, ?_⟩
    rw [Category.assoc, hg]
    exact congrArg (fun k ↦ k.hom) (Over.w f.unop.hom)

/-- A subterminal sheaf has a section over the open subspace cut out by its support: the étale
spaces over which it has a section cover that subspace, and it is a sheaf. -/
theorem supportedOpenSubspace_has_section (F : Subfunctor (spacesEtaleTerminalSheaf B S hS X))
    (W : {W : Subfunctor X.1 // IsOpenSubspace B S hS W})
    (hWpoints : Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
      supportedPoints B S hS X F)
    (hF : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) F.toFunctor) :
    Nonempty (F.obj (op (openSubspaceObject B S hS X W))) := by
  classical
  choose g hg using fun (U : SpacesEtale B S hS X) (s : F.obj (op U)) ↦
    supportedObject_factors B S hS X F W hWpoints U s
  let Wsite := openSubspaceObject B S hS X W
  let I := Σ U : SpacesEtale B S hS X, Σ _s : F.obj (op U),
    points B S hS ((SpacesEtale.toSpaces B S hS X).obj U).1
  let Y : I → SpacesEtale B S hS X := fun i ↦ i.1
  let f : (i : I) → Y i ⟶ Wsite := fun i ↦
    siteArrowOfFactor B S hS X W i.1 (g i.1 i.2.1) (hg i.1 i.2.1)
  let E : PreZeroHypercover.{u + 1} Wsite := ⟨I, Y, f⟩
  have hcov : SpacesEtale.IsCovering B S hS X ⟨Wsite, E⟩ := by
    intro x
    have hx : pointsMap B S hS W.1.toFunctor W.1.ι x ∈ supportedPoints B S hS X F := by
      rw [← hWpoints]
      exact ⟨x, rfl⟩
    obtain ⟨U, s, y, hxy⟩ := hx
    refine ⟨⟨U, s, y⟩, y, ?_⟩
    dsimp [Wsite, openSubspaceObject, SpacesEtale.toSpaces] at x hxy ⊢
    apply pointsMap_injective_of_mono B S hS W.1.ι
    show pointsMap B S hS W.1.toFunctor W.1.ι
        (pointsMap B S hS U.1.left.1 (g U s) y) =
      pointsMap B S hS W.1.toFunctor W.1.ι x
    simpa only [pointsMap_comp, Function.comp_apply] using
      (congrArg (fun k ↦ pointsMap B S hS U.1.left.1 k y) (hg U s)).trans hxy
  have hsf : Presieve.IsSheafFor F.toFunctor E.presieve₀ :=
    (Presieve.isSheafFor_iff_generate E.presieve₀).2 <|
      (isSheaf_iff_isSheaf_of_type (SpacesEtale.topology B S hS X) F.toFunctor).1 hF
        (Sieve.generate E.presieve₀) (Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hcov⟩)
  let family : Presieve.FamilyOfElements F.toFunctor E.presieve₀ :=
    fun {V} g hg ↦ by
      have hm : ∃ k, ∃ e : V ≅ Y k, e.hom ≫ f k = g := by
        cases hg with
        | mk k => exact ⟨k, Iso.refl _, rfl⟩
      exact F.toFunctor.map
        (Classical.choose (Classical.choose_spec hm)).hom.op (Classical.choose hm).2.1
  have hcompatible : family.Compatible := by
    intro V₁ V₂ T a b g₁ g₂ _ha _hb _hab
    refine Subtype.ext ?_
    have : Subsingleton ((spacesEtaleTerminalSheaf B S hS X).obj (op T)) :=
      inferInstanceAs (Subsingleton PUnit)
    exact this.elim _ _
  exact ⟨hsf.amalgamate family hcompatible⟩

/-- A subterminal sheaf represented by an open subspace has that subspace's points as its
support. -/
theorem supportedPoints_eq_range_of_representation
    (F : Subfunctor (spacesEtaleTerminalSheaf B S hS X))
    (W : {W : Subfunctor X.1 // IsOpenSubspace B S hS W})
    (hFW : F = openSubspaceSheaf B S hS X W) :
    supportedPoints B S hS X F =
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) := by
  subst hFW
  ext x
  constructor
  · rintro ⟨U, s, y, rfl⟩
    obtain ⟨g, hg⟩ := s.2
    refine ⟨pointsMap B S hS ((SpacesEtale.toSpaces B S hS X).obj U).1 g y, ?_⟩
    rw [← hg, pointsMap_comp, Function.comp_apply]
  · rintro ⟨y, rfl⟩
    let U := openSubspaceObject B S hS X W
    let s : (openSubspaceSheaf B S hS X W).obj (op U) :=
      ⟨PUnit.unit, ⟨𝟙 _, by simp [U, openSubspaceObject]⟩⟩
    exact ⟨U, s, y, rfl⟩

/-- **Stacks 04K8.** Every subsheaf of the terminal sheaf on the spaces-étale site of an
algebraic space is the sheaf of a unique open subspace. -/
@[stacks 04K8]
theorem existsUnique_openSubspace_of_subterminalSheaf
    (F : Subfunctor (spacesEtaleTerminalSheaf B S hS X))
    (hF : Presheaf.IsSheaf (SpacesEtale.topology B S hS X) F.toFunctor) :
    ∃! W : {W : Subfunctor X.1 // IsOpenSubspace B S hS W},
      F = openSubspaceSheaf B S hS X W := by
  let W := supportedOpenSubspace B S hS X F
  have hWpoints := supportedOpenSubspace_points B S hS X F
  have hrep : F = openSubspaceSheaf B S hS X W := by
    refine Subfunctor.ext ?_
    ext U x
    constructor
    · intro hx
      exact supportedObject_factors B S hS X F W hWpoints U.unop ⟨x, hx⟩
    · rintro ⟨g, hg⟩
      exact (F.toFunctor.map (siteArrowOfFactor B S hS X W U.unop g hg).op
        (Classical.choice (supportedOpenSubspace_has_section B S hS X F W hWpoints hF))).property
  refine ⟨W, hrep, fun V hFV ↦ ?_⟩
  let _ : TopologicalSpace (points B S hS X.1) := pointTopology B S hS X.1
  refine (openSubspacesOrderIso B S hS X.1 X.property).injective ?_
  ext x
  show x ∈ (openSubspacesOrderIso B S hS X.1 X.property V).1 ↔
    x ∈ (openSubspacesOrderIso B S hS X.1 X.property W).1
  rw [openSubspacesOrderIso_apply B S hS X.1 X.property V,
    openSubspacesOrderIso_apply B S hS X.1 X.property W,
    ← supportedPoints_eq_range_of_representation B S hS X F V hFV,
    ← supportedOpenSubspace_points B S hS X F]

end AlgebraicGeometry.Space

end
