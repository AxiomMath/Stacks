module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# Birational morphisms of algebraic spaces: the schematic locus and generic charts

The conclusion of Stacks 086U (a representable open subspace with dense point set), the
scheme representing the schematic locus and its open immersion, the field-valued
representative of a generic point on the schematic locus, the local ring
`AlgebraicGeometry.Space.genericLocalRing` at a generic point, and schematic open charts
`AlgebraicGeometry.Space.GenericChart` with their local rings.

See `StacksFrontier.AlgebraicGeometry.Spaces.BirationalMorphism` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The conclusion of Stacks 086U.** An algebraic space over `S` has a representable open
subspace whose set of points is dense in its space of points.

A decent algebraic space has one, by Stacks 086U; see
`AlgebraicGeometry.Space.hasDenseRepresentableOpenSubspace_of_isDecentSpace`. -/
abbrev HasDenseRepresentableOpenSubspace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  letI := pointTopology B S hS F
  ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧ G.toFunctor.IsRepresentable ∧
    DenseRange (pointsMap B S hS G.toFunctor G.ι)

/-- An algebraic space in which every nonempty open subspace contains a nonempty
representable open subspace has a representable open subspace with dense point set. This is
Stacks 03JH, the local-to-global reduction behind Stacks 086U. -/
theorem hasDenseRepresentableOpenSubspace_of_forall_isOpenSubspace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hnonempty : ∀ G : Subfunctor F, IsOpenSubspace B S hS G →
      (Set.range (pointsMap B S hS G.toFunctor G.ι)).Nonempty →
      ∃ H : Subfunctor F, H ≤ G ∧ IsOpenSubspace B S hS H ∧
        H.toFunctor.IsRepresentable ∧
        (Set.range (pointsMap B S hS H.toFunctor H.ι)).Nonempty) :
    HasDenseRepresentableOpenSubspace B S hS F :=
  exists_denseRange_isRepresentable_isOpenSubspace_of_isAlgebraicSpace B S hS hF hnonempty

private theorem genericPoints_mem_dense_open_of_finiteComponents
    {X : Type u} [TopologicalSpace X]
    (hfinite : (irreducibleComponents X).Finite) {D : Set X}
    (hD : IsOpen D) (hdense : Dense D) {x : X}
    (hx : x ∈ genericPoints X) : x ∈ D := by
  let C : Set X := closure ({x} : Set X)
  have hC : C ∈ irreducibleComponents X := hx
  let O : Set X := (⋃₀ (irreducibleComponents X \ {C}))ᶜ
  have hOopen : IsOpen O := by
    change IsOpen ((⋃₀ (irreducibleComponents X \ {C}))ᶜ)
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfinite.sdiff.isClosed_biUnion fun V hV =>
      isClosed_of_mem_irreducibleComponents V hV.1
  have hclosure : closure O = C :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfinite C hC
  have hOne : O.Nonempty := by
    have hnotSubset : ¬ C ⊆ ⋃₀ (irreducibleComponents X \ {C}) := by
      intro hsub
      have hmem := mem_of_subset_sUnion_irreducibleComponents C hC _
        hfinite.sdiff Set.sdiff_subset hsub
      exact hmem.2 (by simp)
    obtain ⟨z, hzC, hznot⟩ := Set.not_subset.mp hnotSubset
    exact ⟨z, by simpa [O] using hznot⟩
  obtain ⟨z, hzO, hzD⟩ := hdense.inter_open_nonempty O hOopen hOne
  have hzC : z ∈ C := by
    have : z ∈ closure O := subset_closure hzO
    simpa [hclosure, C] using this
  exact (specializes_iff_mem_closure.mpr hzC).mem_open hD hzD

/-- The scheme representing the schematic locus of an algebraic space. -/
noncomputable def schematicScheme
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    BigFppfOver B S hS := by
  letI : (schematicLocus B S hS F).toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2
  exact (schematicLocus B S hS F).toFunctor.reprX

/-- The canonical open immersion of the scheme representing the schematic locus. -/
noncomputable def schematicChart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    yoneda.obj (schematicScheme B S hS hF) ⟶ F := by
  let G := schematicLocus B S hS F
  letI : G.toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2
  exact G.toFunctor.reprW.hom ≫ G.ι

/-- The canonical chart of the schematic locus is an open immersion. -/
theorem isOpenImmersion_schematicChart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    IsOpenImmersion B S hS (schematicChart B S hS hF) := by
  let G := schematicLocus B S hS F
  let : G.toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2
  change IsOpenImmersion B S hS (G.toFunctor.reprW.hom ≫ G.ι)
  exact MorphismProperty.RespectsIso.precomp _ G.toFunctor.reprW.hom G.ι
    ((isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).1).2

/-- A generic point has a field-valued representative on the schematic locus. -/
theorem exists_schematicRepresentative
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F)) :
    ∃ p : FieldValuedPoint B S hS
        (yoneda.obj (schematicScheme B S hS hF)),
      pointsMap B S hS _ (schematicChart B S hS hF)
        (p.class B S hS _) = x := by
  classical
  let : TopologicalSpace (points B S hS F) :=
    pointTopology B S hS F
  obtain ⟨G, hG, hGrep, hDense⟩ :=
    hdense
  have hxrange : x ∈ Set.range (pointsMap B S hS G.toFunctor G.ι) :=
    genericPoints_mem_dense_open_of_finiteComponents hfinite
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS G.ι hG.2) hDense hx
  obtain ⟨z, hz⟩ := hxrange
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  let Z := schematicLocus B S hS F
  let : Z.toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hF).2
  let j : G.toFunctor ⟶ Z.toFunctor :=
    Subfunctor.homOfLe
      (le_schematicLocus B S hS F G hG hGrep)
  let α : G.toFunctor ⟶ yoneda.obj (schematicScheme B S hS hF) :=
    j ≫ Z.toFunctor.reprW.inv
  refine ⟨FieldValuedPoint.map B S hS G.toFunctor α p, ?_⟩
  rw [pointsMap_class]
  have hcomp : α ≫ schematicChart B S hS hF = G.ι := by
    dsimp [α, schematicChart, schematicScheme, Z, j]
    simp [Category.assoc]
  calc
    _ = pointsMap B S hS G.toFunctor
        (α ≫ schematicChart B S hS hF) (p.class B S hS G.toFunctor) :=
      (congrFun (pointsMap_comp B S hS _ α (schematicChart B S hS hF))
        (p.class B S hS G.toFunctor)).symm
    _ = pointsMap B S hS G.toFunctor G.ι
        (p.class B S hS G.toFunctor) := by rw [hcomp]
    _ = x := hz

/-- A fixed lift of a generic point to the schematic locus. -/
noncomputable def schematicRepresentative
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F)) :
    FieldValuedPoint B S hS
      (yoneda.obj (schematicScheme B S hS hF)) :=
  (exists_schematicRepresentative B S hS hF hdense hfinite x hx).choose

/-- The local ring of an algebraic space at a generic point, computed on its
schematic locus. -/
noncomputable def genericLocalRing
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F)) : CommRingCat.{u} :=
  ((BigFppfOver.toScheme B S hS).obj
    (schematicScheme B S hS hF)).presheaf.stalk
      (schemePoint B S hS (schematicScheme B S hS hF)
        (schematicRepresentative B S hS hF hdense hfinite x hx))

/-- The local ring on the schematic locus is a local ring. -/
noncomputable instance genericLocalRing.isLocalRing
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F)) :
    IsLocalRing (genericLocalRing B S hS hF hdense hfinite x hx) := by
  unfold genericLocalRing
  infer_instance

/-- A schematic open chart around a point of an algebraic space. -/
structure GenericChart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : points B S hS F) where
  /-- The scheme over `S` serving as the chart. -/
  U : BigFppfOver B S hS
  /-- The morphism from the representable functor of `U` to `F`. -/
  immersion : yoneda.obj U ⟶ F
  /-- The morphism `immersion` is an open immersion. -/
  isOpen : IsOpenImmersion B S hS immersion
  /-- A field-valued point of `U`. -/
  point : FieldValuedPoint B S hS (yoneda.obj U)
  /-- The point `point` maps to `x` under `immersion`. -/
  mapsTo : pointsMap B S hS _ immersion
    (point.class B S hS _) = x

/-- The distinguished chart at a generic point, given by the schematic locus. -/
noncomputable def schematicGenericChart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    (hdense : HasDenseRepresentableOpenSubspace B S hS F)
    (hfinite : (letI := pointTopology B S hS F
      (irreducibleComponents (points B S hS F)).Finite))
    (x : points B S hS F)
    (hx : letI := pointTopology B S hS F
      x ∈ genericPoints (points B S hS F)) :
    GenericChart B S hS x where
  U := schematicScheme B S hS hF
  immersion := schematicChart B S hS hF
  isOpen := isOpenImmersion_schematicChart B S hS hF
  point := schematicRepresentative B S hS hF hdense hfinite x hx
  mapsTo := (exists_schematicRepresentative B S hS hF hdense hfinite x hx).choose_spec

/-- The local ring of a schematic chart at its given point. -/
noncomputable abbrev GenericChart.localRing
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {x : points B S hS F}
    (c : GenericChart B S hS x) : CommRingCat.{u} :=
  ((BigFppfOver.toScheme B S hS).obj c.U).presheaf.stalk
    (schemePoint B S hS c.U c.point)

end AlgebraicGeometry.Space

end
