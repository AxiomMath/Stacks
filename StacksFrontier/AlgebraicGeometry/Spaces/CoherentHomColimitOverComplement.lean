module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModule
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Morphisms from ideal-power multiples over the complement of a closed subspace

Let `X` be an algebraic space over a scheme `S`, let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of
ideals, let `Z = V(ℐ)` be the closed subspace it cuts out and let `U = X ∖ Z`.  For `𝒪_X`-modules
`𝒢` and `ℱ` this file constructs the canonical map

`colim_n Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ) ⟶ Hom_{𝒪_U}(𝒢|_U, ℱ|_U)`

and identifies it on each leg of the colimit.

The open subspace `U` is taken to be the one cut out by the unit locus of `ℐ`, which is the
complement of the closed subspace of [Stacks, Tag 03MB] by
`AlgebraicGeometry.Space.openComplement_eq_openSubspaceOfPoints_idealUnitLocus`; taking the unit
locus as the primitive avoids choosing the closed subspace out of an existence statement.
Restriction to `U` is the étale restriction of `𝒪_X`-modules along the open immersion
`j : U ⟶ X`, which on an étale chart of `U` is the identity on sections.

## Main definitions

* `AlgebraicGeometry.Space.idealComplement` is the open subspace `U = X ∖ V(ℐ)`, with
  `AlgebraicGeometry.Space.idealComplementι` the open immersion `j : U ⟶ X`.
* `AlgebraicGeometry.Space.restrictToIdealComplement` is restriction of modules to `U`.
* `AlgebraicGeometry.Space.idealPowRestrictIso` is the isomorphism `(ℐⁿ 𝒢)|_U ≅ 𝒢|_U`.
* `AlgebraicGeometry.Space.homSystem` is the direct system `n ↦ Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ)` and
  `AlgebraicGeometry.Space.homRestrict` the morphism `𝒢|_U ⟶ ℱ|_U` attached to a morphism
  `ℐⁿ 𝒢 ⟶ ℱ`.
* `AlgebraicGeometry.Space.canonicalMapToHomRestrict` is the canonical map above, the arrow of
  the first display of [Stacks, Tag 07UM], and
  `AlgebraicGeometry.Space.canonicalMapToSections` is its `𝒢 = 𝒪_X` case
  `colim_n Hom_{𝒪_X}(ℐⁿ, ℱ) ⟶ Γ(U, ℱ|_U)`, the arrow of the second display.

## Main results

* `AlgebraicGeometry.Space.idealPowSubmodule_obj_pc_eq_top`: over an étale chart of `U` the
  submodule `ℐⁿ 𝒢` is all of `𝒢`, because the charts on which `ℐ` is the whole structure sheaf
  cover such a chart.  This is what makes `idealPowRestrictIso` an isomorphism.
* `AlgebraicGeometry.Space.canonicalMapToHomRestrict_ι`: the canonical map on the image of the
  `n`-th leg of the colimit is `homRestrict`.  This pins the canonical map down.

## Implementation notes

**No comparison isomorphism is needed for the second display.**  Étale restriction of modules is
restriction along postcomposition of charts with `j`, with the identity change of scalars, and
postcomposition leaves the underlying scheme of a chart — hence its ring of regular functions —
unchanged.  So `𝒪_X|_U` and `𝒪_U` are not merely isomorphic but *equal*, and
`AlgebraicGeometry.Space.restrictToIdealComplement_unit_eq` holds by `rfl`.  The second display
is therefore the first display at `𝒢 = 𝒪_X` composed with `SheafOfModules.unitHomEquiv`, and
nothing has to be transported: a reader looking for the comparison map between `𝒪_X|_U` and
`𝒪_U` should not build one.

No `@[stacks 07UM]` attribute is placed here: Tag 07UM asserts that the canonical maps
constructed below are *bijective*, and only their construction and the identification of their
legs are proved here.  The attribute sits on the two statements of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentHomColimitBijective.lean` —
`AlgebraicGeometry.Space.canonicalMapToHomRestrict_bijective` for the first display and
`AlgebraicGeometry.Space.canonicalMapToSections_bijective` for the "in particular" display, the
bijectivity of `AlgebraicGeometry.Space.canonicalMapToSections` below.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS) (I : IdealSheaves B S hS X.1 X.2)

/-! ### The open complement `U = X ∖ V(ℐ)` -/

/-- `U = X ∖ V(ℐ)`, as a subfunctor of `X`: the open subspace cut out by the unit locus of the
sheaf of ideals. -/
def idealComplementSubfunctor : Subfunctor X.1 :=
  openSubspaceOfPoints B S hS X.1 (idealUnitLocus B S hS X I)

/-- The complement of `V(ℐ)` is an open subspace of `X`. -/
theorem isOpenSubspace_idealComplementSubfunctor :
    IsOpenSubspace B S hS (idealComplementSubfunctor B S hS X I) :=
  isOpenSubspace_openSubspaceOfPoints B S hS X.2 _ (isOpen_idealUnitLocus B S hS X I)

/-- `U = X ∖ V(ℐ)` as an algebraic space over `S`. -/
def idealComplement : AlgebraicSpaces B S hS :=
  ⟨(idealComplementSubfunctor B S hS X I).toFunctor,
    (isOpenSubspace_idealComplementSubfunctor B S hS X I).1⟩

/-- The open immersion `j : U ⟶ X` of the complement of `V(ℐ)`. -/
def idealComplementι : idealComplement B S hS X I ⟶ X :=
  ObjectProperty.homMk (idealComplementSubfunctor B S hS X I).ι

/-- The inclusion of the complement of `V(ℐ)` is étale, being an open immersion. -/
theorem isEtale_idealComplementι :
    IsEtale B S hS (idealComplementι B S hS X I).hom :=
  Space.isEtale_of_isOpenImmersion B S hS
    (isOpenSubspace_idealComplementSubfunctor B S hS X I).2

/-- Restriction of `𝒪_X`-modules to `U = X ∖ V(ℐ)`, along the open immersion `j : U ⟶ X`. -/
def restrictToIdealComplement :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      Modules.{u, u} B S hS (idealComplement B S hS X I).1
        (idealComplement B S hS X I).2 :=
  etaleModulePullback B S hS (idealComplementι B S hS X I)
    (isEtale_idealComplementι B S hS X I)

/-- The chart of `X` obtained from a chart of `U` by composing with `j : U ⟶ X`. -/
abbrev pc (V : SmallEtale B S hS (idealComplement B S hS X I).1) :
    SmallEtale B S hS X.1 :=
  (smallEtalePostcomp B S hS (idealComplementι B S hS X I)
    (isEtale_idealComplementι B S hS X I)).obj V

/-! ### `ℐⁿ 𝒢` and `𝒢` agree over `U` -/


/-- A point of an étale chart of `U = X ∖ V(ℐ)`, pushed into `X`, lies in the unit locus of
`ℐ`. -/
private theorem mem_idealUnitLocus_pc
    (V : SmallEtale B S hS (idealComplement B S hS X I).1)
    (y : points B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj (pc B S hS X I V)))) :
    pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj (pc B S hS X I V)))
        (pc B S hS X I V).1.hom y ∈ idealUnitLocus B S hS X I := by
  have h2 : pointsMap B S hS (idealComplement B S hS X I).1
      (idealComplementι B S hS X I).hom
      (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS (idealComplement B S hS X I).1).obj V))
        V.1.hom y) ∈ idealUnitLocus B S hS X I :=
    (range_pointsMap_ι_openSubspaceOfPoints B S hS (F := X.1)
      (idealUnitLocus B S hS X I)).le ⟨_, rfl⟩
  show pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS (idealComplement B S hS X I).1).obj V))
      (V.1.hom ≫ (idealComplementι B S hS X I).hom) y ∈ idealUnitLocus B S hS X I
  rw [pointsMap_comp]
  exact h2

/-- The charts on which `ℐ` is the whole structure sheaf cover an étale chart of
`U = X ∖ V(ℐ)`. -/
private theorem unitSieve_mem_topology
    (V : SmallEtale B S hS (idealComplement B S hS X I).1) :
    unitSieve B S hS X I (pc B S hS X I V) ∈
      SmallEtale.topology B S hS X.1 (pc B S hS X I V) := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  obtain ⟨y, hy⟩ := surjective_pointsToScheme B S hS
    ((SmallEtale.toOver B S hS X.1).obj (pc B S hS X I V)) x
  obtain ⟨W, g, hW, w, hw⟩ := (mem_idealUnitLocus_iff_exists_over B S hS X I
    (pc B S hS X I V) y).1 (mem_idealUnitLocus_pc B S hS X I V y)
  refine ⟨W, g, hW, pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W) w, ?_⟩
  rw [← pointsToScheme_pointsMap_yoneda, hw]
  exact hy

/-- Over a chart on which `ℐ` is the whole structure sheaf, every section of `𝒢` is a section of
`ℐⁿ 𝒢`: the unit ideal already generates there. -/
private theorem map_mem_idealPowSubmodule_of_eq_top (n : ℕ)
    (G : Modules.{u, u} B S hS X.1 X.2) {W₀ Y : SmallEtale B S hS X.1} (g : Y ⟶ W₀)
    (hY : I.obj (op Y) = ⊤) (z : G.val.obj (op W₀)) :
    G.val.map g.op z ∈ (idealPowSubmodule I n G).obj (op Y) := by
  have hring : Stacks.Sites.ringSectionIdeal I (op Y) = ⊤ := hY
  have hle := Stacks.Sites.pow_smul_le_idealPowSmul (M := G) I n ⊤ (op Y)
  rw [hring, Ideal.top_pow, Submodule.top_smul] at hle
  exact hle (mem_top_submodule_obj B S hS X.1 X.2 G (W := op Y) (G.val.map g.op z))

/-- **Over an étale chart of `U = X ∖ V(ℐ)` the submodule `ℐⁿ 𝒢` is all of `𝒢`.** -/
theorem idealPowSubmodule_obj_pc_eq_top (n : ℕ) (G : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS (idealComplement B S hS X I).1) :
    (idealPowSubmodule I n G).obj (op (pc B S hS X I V)) = ⊤ := by
  refine eq_top_iff.2 fun z _ => (idealPowSubmodule I n G).isSheaf z ?_
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (unitSieve_mem_topology B S hS X I V)
  intro Y g hg
  exact map_mem_idealPowSubmodule_of_eq_top B S hS X I n G g hg z

/-- Every section of `𝒢` over an étale chart of `U = X ∖ V(ℐ)` lies in `ℐⁿ 𝒢`. -/
theorem mem_idealPowSubmodule_pc (n : ℕ) (G : Modules.{u, u} B S hS X.1 X.2)
    (V : SmallEtale B S hS (idealComplement B S hS X I).1)
    (z : G.val.obj (op (pc B S hS X I V))) :
    z ∈ (idealPowSubmodule I n G).obj (op (pc B S hS X I V)) := by
  rw [idealPowSubmodule_obj_pc_eq_top B S hS X I n G V]
  exact Submodule.mem_top

/-- The restriction to `U` of the inclusion `ℐⁿ 𝒢 ⟶ 𝒢` is bijective on sections. -/
theorem bijective_restrictToIdealComplement_map_idealPowModuleι (n : ℕ)
    (G : Modules.{u, u} B S hS X.1 X.2)
    (V : (SmallEtale B S hS (idealComplement B S hS X I).1)ᵒᵖ) :
    Function.Bijective
      ((((restrictToIdealComplement B S hS X I).map
        (idealPowModuleι I n G)).val.app V).hom) :=
  ⟨fun _ _ hab => Subtype.ext hab,
    fun z => ⟨⟨z, mem_idealPowSubmodule_pc B S hS X I n G V.unop z⟩, rfl⟩⟩

/-- The restriction to `U` of the inclusion `ℐⁿ 𝒢 ⟶ 𝒢` is an isomorphism. -/
instance isIso_restrictToIdealComplement_map_idealPowModuleι (n : ℕ)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    IsIso ((restrictToIdealComplement B S hS X I).map (idealPowModuleι I n G)) := by
  have hall : ∀ V, IsIso (((SheafOfModules.forget
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (idealComplement B S hS X I).1
          (idealComplement B S hS X I).2).O)) ⋙ PresheafOfModules.toPresheaf _).map
      ((restrictToIdealComplement B S hS X I).map (idealPowModuleι I n G))).app V) := by
    intro V
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_restrictToIdealComplement_map_idealPowModuleι B S hS X I n G V
  have : IsIso ((SheafOfModules.forget
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (idealComplement B S hS X I).1
          (idealComplement B S hS X I).2).O)) ⋙ PresheafOfModules.toPresheaf _).map
      ((restrictToIdealComplement B S hS X I).map (idealPowModuleι I n G))) :=
    NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

/-- **`(ℐⁿ 𝒢)|_U ≅ 𝒢|_U`**: away from `V(ℐ)` the unit ideal already generates, so `ℐⁿ 𝒢` is all
of `𝒢` there. -/
def idealPowRestrictIso (n : ℕ) (G : Modules.{u, u} B S hS X.1 X.2) :
    (restrictToIdealComplement B S hS X I).obj (idealPowModule I n G) ≅
      (restrictToIdealComplement B S hS X I).obj G :=
  asIso ((restrictToIdealComplement B S hS X I).map (idealPowModuleι I n G))

/-- The isomorphism `(ℐⁿ 𝒢)|_U ≅ 𝒢|_U` is the restriction of the inclusion of `ℐⁿ 𝒢` in `𝒢`. -/
@[simp] theorem idealPowRestrictIso_hom (n : ℕ) (G : Modules.{u, u} B S hS X.1 X.2) :
    (idealPowRestrictIso B S hS X I n G).hom =
      (restrictToIdealComplement B S hS X I).map (idealPowModuleι I n G) := rfl

/-! ### The direct system `n ↦ Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ)` and the canonical map -/

/-- The direct system `n ↦ Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ)`, the transition maps being precomposition with
the inclusions `ℐⁿ 𝒢 ⟶ ℐᵏ 𝒢` for `k ≤ n`. -/
def homSystem (G F : Modules.{u, u} B S hS X.1 X.2) : ℕ ⥤ AddCommGrpCat.{u + 1} where
  obj n := AddCommGrpCat.of (idealPowModule I n G ⟶ F)
  map {k n} h := AddCommGrpCat.ofHom
    (Preadditive.leftComp F (idealPowModuleHomOfLE I G (leOfHom h)))
  map_id n := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => by
    change idealPowModuleHomOfLE I G (le_refl n) ≫ φ = φ
    rw [show idealPowModuleHomOfLE I G (le_refl n) = 𝟙 _ from rfl, Category.id_comp])
  map_comp {k m n} h h' := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ => by
    change idealPowModuleHomOfLE I G (leOfHom (h ≫ h')) ≫ φ
      = idealPowModuleHomOfLE I G (leOfHom h') ≫
        (idealPowModuleHomOfLE I G (leOfHom h) ≫ φ)
    rw [← Category.assoc, Stacks.SheafOfModules.Submodule.homOfLE_comp_homOfLE])

/-- A transition map of the system `n ↦ Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ)` is precomposition with an inclusion
of the filtration. -/
@[simp] theorem homSystem_map (G F : Modules.{u, u} B S hS X.1 X.2) {k n : ℕ} (h : k ⟶ n)
    (φ : idealPowModule I k G ⟶ F) :
    (homSystem B S hS X I G F).map h φ = idealPowModuleHomOfLE I G (leOfHom h) ≫ φ := rfl

/-- The isomorphisms `(ℐⁿ 𝒢)|_U ≅ 𝒢|_U` are compatible with the inclusions of the
filtration. -/
theorem map_idealPowModuleHomOfLE_comp_idealPowRestrictIso_hom
    (G : Modules.{u, u} B S hS X.1 X.2) {k n : ℕ} (h : k ≤ n) :
    (restrictToIdealComplement B S hS X I).map (idealPowModuleHomOfLE I G h) ≫
        (idealPowRestrictIso B S hS X I k G).hom =
      (idealPowRestrictIso B S hS X I n G).hom := by
  rw [idealPowRestrictIso_hom, idealPowRestrictIso_hom, ← Functor.map_comp,
    idealPowModuleHomOfLE_comp_ι]

/-- The inverses of the isomorphisms `(ℐⁿ 𝒢)|_U ≅ 𝒢|_U` are compatible with the inclusions of
the filtration. -/
theorem idealPowRestrictIso_inv_comp_map_idealPowModuleHomOfLE
    (G : Modules.{u, u} B S hS X.1 X.2) {k n : ℕ} (h : k ≤ n) :
    (idealPowRestrictIso B S hS X I n G).inv ≫
        (restrictToIdealComplement B S hS X I).map (idealPowModuleHomOfLE I G h) =
      (idealPowRestrictIso B S hS X I k G).inv := by
  rw [show (restrictToIdealComplement B S hS X I).map (idealPowModuleHomOfLE I G h)
      = (idealPowRestrictIso B S hS X I n G).hom ≫
        (idealPowRestrictIso B S hS X I k G).inv from
    (Iso.eq_comp_inv _).mpr
      (map_idealPowModuleHomOfLE_comp_idealPowRestrictIso_hom B S hS X I G h),
    Iso.inv_hom_id_assoc]

/-- The morphism `𝒢|_U ⟶ ℱ|_U` attached to a morphism `φ : ℐⁿ 𝒢 ⟶ ℱ`: the inverse of
`(ℐⁿ 𝒢)|_U ≅ 𝒢|_U` followed by the restriction of `φ`. -/
def homRestrict {G F : Modules.{u, u} B S hS X.1 X.2} {n : ℕ}
    (φ : idealPowModule I n G ⟶ F) :
    (restrictToIdealComplement B S hS X I).obj G ⟶
      (restrictToIdealComplement B S hS X I).obj F :=
  (idealPowRestrictIso B S hS X I n G).inv ≫ (restrictToIdealComplement B S hS X I).map φ

/-- Restricting a morphism out of `ℐⁿ 𝒢` to `U` is additive. -/
theorem homRestrict_add {G F : Modules.{u, u} B S hS X.1 X.2} {n : ℕ}
    (φ ψ : idealPowModule I n G ⟶ F) :
    homRestrict B S hS X I (φ + ψ) =
      homRestrict B S hS X I φ + homRestrict B S hS X I ψ := by
  show (idealPowRestrictIso B S hS X I n G).inv ≫
      ((restrictToIdealComplement B S hS X I).map φ
        + (restrictToIdealComplement B S hS X I).map ψ) = _
  rw [Preadditive.comp_add]
  rfl

/-- Precomposing with an inclusion `ℐⁿ 𝒢 ⟶ ℐᵏ 𝒢` does not change the restriction to `U`, so
`homRestrict` is a cocone on the system `n ↦ Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ)`. -/
theorem homRestrict_idealPowModuleHomOfLE {G F : Modules.{u, u} B S hS X.1 X.2} {k n : ℕ}
    (h : k ≤ n) (φ : idealPowModule I k G ⟶ F) :
    homRestrict B S hS X I (idealPowModuleHomOfLE I G h ≫ φ) =
      homRestrict B S hS X I φ := by
  rw [homRestrict, homRestrict, Functor.map_comp, ← Category.assoc,
    idealPowRestrictIso_inv_comp_map_idealPowModuleHomOfLE]

/-- The cocone on `n ↦ Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ)` whose leg at `n` restricts a morphism `ℐⁿ 𝒢 ⟶ ℱ` to
a morphism `𝒢|_U ⟶ ℱ|_U`. -/
def homRestrictCocone (G F : Modules.{u, u} B S hS X.1 X.2) :
    Limits.Cocone (homSystem B S hS X I G F) where
  pt := AddCommGrpCat.of ((restrictToIdealComplement B S hS X I).obj G ⟶
    (restrictToIdealComplement B S hS X I).obj F)
  ι :=
    { app := fun n => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun φ : idealPowModule I n G ⟶ F => homRestrict B S hS X I φ)
          (homRestrict_add B S hS X I))
      naturality := fun {k n} h => by
        simp only [Functor.const_obj_map]
        exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ =>
          homRestrict_idealPowModuleHomOfLE B S hS X I (leOfHom h) φ) }

/-- **The canonical map `colim_n Hom_{𝒪_X}(ℐⁿ 𝒢, ℱ) ⟶ Hom_{𝒪_U}(𝒢|_U, ℱ|_U)`**, where
`U = X ∖ V(ℐ)`.

It is the map `AlgebraicGeometry.Space.canonicalMapToHomRestrict_ι` identifies: a morphism
`φ : ℐⁿ 𝒢 ⟶ ℱ` goes to the restriction of `φ` to `U`, read through the isomorphism
`(ℐⁿ 𝒢)|_U ≅ 𝒢|_U`.  [Stacks, Tag 07UM] asserts that it is bijective when `X` is Noetherian,
`𝒢` is coherent and `ℱ` is quasi-coherent. -/
def canonicalMapToHomRestrict (G F : Modules.{u, u} B S hS X.1 X.2) :
    Limits.colimit (homSystem B S hS X I G F) ⟶
      AddCommGrpCat.of ((restrictToIdealComplement B S hS X I).obj G ⟶
        (restrictToIdealComplement B S hS X I).obj F) :=
  Limits.colimit.desc _ (homRestrictCocone B S hS X I G F)

/-- The canonical map on the image of the `n`-th leg of the colimit is `homRestrict`. -/
theorem canonicalMapToHomRestrict_ι (G F : Modules.{u, u} B S hS X.1 X.2) (n : ℕ)
    (φ : idealPowModule I n G ⟶ F) :
    canonicalMapToHomRestrict B S hS X I G F
        (Limits.colimit.ι (homSystem B S hS X I G F) n φ) =
      homRestrict B S hS X I φ :=
  congr($(Limits.colimit.ι_desc (homRestrictCocone B S hS X I G F) n) φ)

/-! ### Sections over the complement -/

/-- The structure sheaf of `X` restricted to `U = X ∖ V(ℐ)` is the structure sheaf of `U`, on
the nose: étale restriction of modules changes neither the charts nor their rings of regular
functions. -/
theorem restrictToIdealComplement_unit_eq :
    (restrictToIdealComplement B S hS X I).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)))
      = SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (idealComplement B S hS X I).1 (idealComplement B S hS X I).2).O)) := rfl

/-- **The canonical map `colim_n Hom_{𝒪_X}(ℐⁿ, ℱ) ⟶ Γ(U, ℱ|_U)`**, where `U = X ∖ V(ℐ)`.

This is the `𝒢 = 𝒪_X` case of `AlgebraicGeometry.Space.canonicalMapToHomRestrict`, read through
`SheafOfModules.unitHomEquiv` and the identification
`AlgebraicGeometry.Space.restrictToIdealComplement_unit_eq` of `𝒪_X|_U` with `𝒪_U`.  It is the
arrow of the second display of [Stacks, Tag 07UM]. -/
def canonicalMapToSections (F : Modules.{u, u} B S hS X.1 X.2) :
    ((Limits.colimit (homSystem B S hS X I
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)))
          F) : AddCommGrpCat.{u + 1})) →
      ((restrictToIdealComplement B S hS X I).obj F).sections :=
  fun z => SheafOfModules.unitHomEquiv _
    (canonicalMapToHomRestrict B S hS X I
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) F z)

end AlgebraicGeometry.Space

end
