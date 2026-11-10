module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated

/-!
# Comparisons between the conditions on an algebraic space

Stacks 03JX lists nine conditions `(α)` to `(ι)` on an algebraic space `X` over a scheme `S`
and relates them by a diagram of implications; Stacks 03KE asserts that seven of them are
Zariski local, that is, that `X` satisfies the condition as soon as it has a Zariski open
covering by open subspaces which do. The conditions themselves are collected in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions`; this file proves comparisons
between them.

## Main results

Implications of the diagram of Stacks 03JX:

* `AlgebraicGeometry.Space.isRepresentable_of_isQuasiSeparatedScheme`: `(ι) ⇒ (θ)`.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme`: `(ι) ⇒ (η)`.
* `AlgebraicGeometry.Space.isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated`:
  `(η) ⇒ (ζ)`.
* `AlgebraicGeometry.Space.hasFiniteChartFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers`:
  `(γ) ⇒ (α)`.
* `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers`:
  `(γ) ⇒ (β)`.
* `AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_of_alpha_and_beta`:
  `(α) + (β) ⇒ (γ)`, and
  `AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_iff_alpha_and_beta`
  for the resulting equivalence `(γ) ⇔ (α) + (β)`.

Zariski locality, from Stacks 03KE:

* `AlgebraicGeometry.Space.isRepresentable_of_isZariskiCover`: the case `(θ)`.
* `AlgebraicGeometry.Space.isAbsolutelyZariskiLocallyQuasiSeparated_of_isZariskiCover`: the
  case `(ζ)`.
* `AlgebraicGeometry.Space.hasFiniteChartFibersAtEveryPoint_of_isZariskiCover`: the case
  `(α)`.
* `AlgebraicGeometry.Space.hasFiniteRelationFibersAtEveryPoint_of_isZariskiCover`: the case
  `(β)`.
* `AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_of_isZariskiCover`: the
  case `(γ)`.

Along the way:

* `AlgebraicGeometry.Space.exists_affine_etale_chart_of_point`: every point of an algebraic
  space over `S` is the image of a point of an affine étale chart of it.

## References

* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03JU](https://stacks.math.columbia.edu/tag/03JU)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03KE](https://stacks.math.columbia.edu/tag/03KE)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u u₁ u₂ u₃

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The conditions `(ι)`, `(θ)`, `(η)` and `(ζ)` -/

/-- Condition `(ι)` implies condition `(θ)`: an algebraic space which is a quasi-separated
scheme is representable. -/
@[stacks 03JX "(iota) implies (theta)"]
theorem isRepresentable_of_isQuasiSeparatedScheme
    (h : IsQuasiSeparatedScheme B S hS X) : X.IsRepresentable := by
  obtain ⟨U, -, ⟨r⟩⟩ := h
  exact r.isRepresentable

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- Condition `(η)` implies condition `(ζ)`: a quasi-separated algebraic space is Zariski
locally quasi-separated. -/
@[stacks 03JX "(eta) implies (zeta)", stacks 03DY "part (2): Zariski locally quasi-separated"]
theorem isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (h : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ X := by
  have halg : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ X) :=
    isAlgebraicSpace_relocalize B ⟨S, hS⟩ ⟨⊤_ Scheme.{u}, hZ⟩ ⟨terminal.from S⟩ X hX
  exact ⟨PUnit.{u + 1}, fun _ ↦ ⊤, isZariskiCover_top halg, fun _ ↦
    isQuasiSeparatedOver_of_iso B (⊤_ Scheme.{u}) hZ
      (asIso (Subfunctor.ι (⊤ : Subfunctor (viewOverIntegers B S hS hZ X)))).symm h⟩

/-- An isomorphism of presheaves on the site has every property pulled back from a property
of schemes which respects isomorphisms and holds for the identities. -/
private theorem presheaf_inverseImage_of_isIso (P : MorphismProperty Scheme.{u})
    (hiso : P.RespectsIso) (hid : ∀ T : Scheme.{u}, P (𝟙 T))
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (hf : IsIso f) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS))) f := by
  have _ : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage P
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
    ⟨fun T ↦ by
      change P ((BigFppfOver.toScheme B S hS).map (𝟙 T))
      rw [CategoryTheory.Functor.map_id]
      exact hid _⟩
  exact MorphismProperty.presheaf_of_isIso _ f

/-- Condition `(ι)` implies condition `(η)`: an algebraic space which is a quasi-separated
scheme is a quasi-separated algebraic space. -/
@[stacks 03JX "(iota) implies (eta)"]
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme
    (h : IsQuasiSeparatedScheme B S hS X) : IsAbsolutelyQuasiSeparated B S hS hZ X := by
  obtain ⟨U, hU, ⟨hrep⟩⟩ := h
  let e : yoneda.obj U ≅ X := Functor.representableByEquiv hrep
  have hX : IsAlgebraicSpace B S hS X :=
    (isAlgebraicSpace_yoneda B S hS U).of_iso e
  refine isQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ X hX
    ⟨U, e.hom, hU, ?_, ?_, Or.inl ?_⟩
  · exact presheaf_inverseImage_of_isIso B S hS
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      MorphismProperty.IsStableUnderBaseChange.respectsIso (fun _ ↦ inferInstance) e.hom
      inferInstance
  · exact presheaf_inverseImage_of_isIso B S hS
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      MorphismProperty.IsStableUnderBaseChange.respectsIso (fun _ ↦ inferInstance) e.hom
      inferInstance
  · exact presheaf_inverseImage_of_isIso B S hS
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      MorphismProperty.IsStableUnderBaseChange.respectsIso (fun _ ↦ inferInstance)
      (pullback.fst e.hom e.hom) inferInstance

/-! ### The conditions `(α)`, `(β)` and `(γ)` -/

/-- Condition `(γ)` implies condition `(α)`: if every affine étale chart has finite fibres
together with its self-intersection, then every affine étale chart has finite fibres. -/
@[stacks 03JX "(gamma) implies (alpha)"]
theorem hasFiniteChartFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers
    (h : HasFiniteChartAndRelationFibersAtEveryPoint B S hS X) :
    HasFiniteChartFibersAtEveryPoint B S hS X :=
  fun x U hU φ hφ ↦ (h x U hU φ hφ).1

/-- Every point of an algebraic space over `S` is the image of a point of an affine étale
chart of it. -/
theorem exists_affine_etale_chart_of_point (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    ∃ (V : BigFppfOver B S hS) (ψ : yoneda.obj V ⟶ X) (y : points B S hS (yoneda.obj V)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) ψ ∧
      pointsMap B S hS (yoneda.obj V) ψ y = x := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  obtain ⟨q, hq⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U a).mp haSurj x
  obtain ⟨-, ⟨V₀, hV₀, rfl⟩, hmem, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsToScheme B S hS U q)) isOpen_univ
  obtain ⟨V, j, hjOpen, hjRange, hVaff⟩ :=
    BigFppfOver.exists_affineOpen_restrict B S hS U ⟨V₀, hV₀⟩
  obtain ⟨y, hy⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS j q
    (by rw [hjRange]; exact hmem)
  have _ : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) := hjOpen
  refine ⟨V, yoneda.map j ≫ a, y, hVaff,
    etale_comp_of_scheme B S hS j a inferInstance haEtale, ?_⟩
  rw [pointsMap_comp_apply, hy, hq]

/-- Condition `(γ)` implies condition `(β)`, in the form of condition (1) of Stacks 03JU:
for an algebraic space satisfying `(γ)`, every point has an étale chart and a pair of points
above it whose relation fibre is finite. -/
@[stacks 03JX "(gamma) implies (beta)"]
theorem hasFiniteRelationFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers
    (hX : IsAlgebraicSpace B S hS X)
    (h : HasFiniteChartAndRelationFibersAtEveryPoint B S hS X) :
    HasFiniteRelationFibersAtEveryPoint B S hS X := by
  intro x
  obtain ⟨V, ψ, y, hVaff, hψ, hy⟩ := exists_affine_etale_chart_of_point B S hS X hX x
  refine ⟨V, ψ, y, y, (isEtale_iff_presheaf_of_yoneda B S hS ψ).2 hψ, hy, hy, ?_⟩
  change {r : points B S hS (pullback ψ ψ) |
    pointsMap B S hS (pullback ψ ψ) (pullback.fst ψ ψ) r = y ∧
    pointsMap B S hS (pullback ψ ψ) (pullback.snd ψ ψ) r = y}.Finite
  refine ((h x V hVaff ψ hψ).2).subset ?_
  rintro r ⟨hr, -⟩
  change pointsMap B S hS (pullback ψ ψ) (pullback.fst ψ ψ ≫ ψ) r ∈ ({x} : Set _)
  rwa [pointsMap_comp_apply, hr]

/-- Conditions `(α)` and `(β)` imply condition `(γ)`: an algebraic space all of whose affine
étale charts have finite fibres and all of whose points have a finite relation fibre satisfies
condition `(γ)`. -/
@[stacks 03JX "(alpha) and (beta) imply (gamma)"]
theorem hasFiniteChartAndRelationFibersAtEveryPoint_of_alpha_and_beta
    (hX : IsAlgebraicSpace B S hS X)
    (hα : HasFiniteChartFibersAtEveryPoint B S hS X)
    (hβ : HasFiniteRelationFibersAtEveryPoint B S hS X) :
    HasFiniteChartAndRelationFibersAtEveryPoint B S hS X := by
  intro x U hUaff φ hφ
  have hchart := hα x U hUaff φ hφ
  refine ⟨hchart, ?_⟩
  have hetale : IsEtale B S hS φ := (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφ
  have hevery : HasFiniteRelationFiberAtEveryEtaleChart B S hS X x :=
    (hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS X hX x).1 (hβ x)
  have hcover : pointsMap B S hS (pullback φ φ) (pullback.fst φ φ ≫ φ) ⁻¹' {x} ⊆
      ⋃ a ∈ pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x},
        ⋃ b ∈ pointsMap B S hS (yoneda.obj U) φ ⁻¹' {x},
          {r : points B S hS (pullback φ φ) |
            pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r = a ∧
            pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r = b} := by
    intro r hr
    have hfst : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.fst φ φ) r) = x := by
      rwa [Set.mem_preimage, Set.mem_singleton_iff, pointsMap_comp_apply] at hr
    have hsnd : pointsMap B S hS (yoneda.obj U) φ
        (pointsMap B S hS (pullback φ φ) (pullback.snd φ φ) r) = x := by
      rwa [Set.mem_preimage, Set.mem_singleton_iff, pullback.condition, pointsMap_comp_apply] at hr
    exact Set.mem_biUnion hfst (Set.mem_biUnion hsnd ⟨rfl, rfl⟩)
  exact (hchart.biUnion fun a ha ↦ hchart.biUnion fun b hb ↦ hevery U φ a b hetale ha hb).subset
    hcover

/-- Condition `(γ)` is equivalent to conditions `(α)` and `(β)` together: for an algebraic
space over `S`, finiteness of the fibres of every affine étale chart together with its
self-intersection is equivalent to finiteness of the fibres of every affine étale chart
together with finiteness of one relation fibre at every point. -/
@[stacks 03JX "(gamma) iff (alpha) and (beta)"]
theorem hasFiniteChartAndRelationFibersAtEveryPoint_iff_alpha_and_beta
    (hX : IsAlgebraicSpace B S hS X) :
    HasFiniteChartAndRelationFibersAtEveryPoint B S hS X ↔
      HasFiniteChartFibersAtEveryPoint B S hS X ∧
        HasFiniteRelationFibersAtEveryPoint B S hS X :=
  ⟨fun h ↦ ⟨hasFiniteChartFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers B S hS X h,
      hasFiniteRelationFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers B S hS X hX h⟩,
    fun h ↦ hasFiniteChartAndRelationFibersAtEveryPoint_of_alpha_and_beta
      B S hS X hX h.1 h.2⟩

/-! ### Zariski locality -/

/-- A subfunctor of a sheaf which is itself a sheaf and whose inclusion is locally
surjective is the whole sheaf. -/
private theorem subfunctor_eq_top_of_isLocallySurjective {C : Type u₁} [Category.{u₂} C]
    {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type u₃} (A : Subfunctor F)
    (hF : Presieve.IsSheaf J F) (hA : Presieve.IsSheaf J A.toFunctor)
    (hls : Presheaf.IsLocallySurjective J A.ι) : A = ⊤ := by
  have hcover (U : C) (x : F.obj (Opposite.op U)) : A.sieveOfSection x ∈ J U := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J A.ι x)
    rintro V f ⟨a, ha⟩
    change F.map f.op x ∈ A.obj (Opposite.op V)
    rw [← ha]
    exact a.property
  refine le_antisymm le_top fun U x _ ↦ ?_
  exact (A.isSheaf_iff hF).1 hA U x (hcover U.unop x)

/-- Condition `(θ)` is Zariski local: an algebraic space with a Zariski open covering by
representable open subspaces is representable. -/
@[stacks 03KE "the case (theta)"]
theorem isRepresentable_of_isZariskiCover (hX : IsAlgebraicSpace B S hS X)
    (I : Type u) (Xᵢ : I → Subfunctor X) (hcover : IsZariskiCover B S hS I Xᵢ)
    (hθ : ∀ i : I, (Xᵢ i).toFunctor.IsRepresentable) : X.IsRepresentable := by
  obtain ⟨hZopen, hZrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX
  set Z := schematicLocus B S hS X with hZdef
  have hle : ∀ i, Xᵢ i ≤ Z :=
    fun i ↦ le_schematicLocus B S hS X (Xᵢ i) (hcover.1 i) (hθ i)
  have hfac : (Sigma.desc fun i ↦ Subfunctor.homOfLe (hle i)) ≫ Z.ι =
      Sigma.desc fun i ↦ (Xᵢ i).ι := by
    ext i : 1
    simp [Subfunctor.homOfLe_ι]
  let _ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i ↦ (Xᵢ i).ι) := hcover.2
  have hZls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) Z.ι :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hfac
  have hZtop : Z = ⊤ :=
    subfunctor_eq_top_of_isLocallySurjective Z
      ((isSheaf_iff_isSheaf_of_type _ X).1 hX.isSheaf)
      ((isSheaf_iff_isSheaf_of_type _ Z.toFunctor).1 hZopen.1.isSheaf) hZls
  rw [hZtop] at hZrep
  let _ : (⊤ : Subfunctor X).toFunctor.IsRepresentable := hZrep
  exact isRepresentable_of_natIso _ (asIso (Subfunctor.ι (⊤ : Subfunctor X)))

/-- A point of an algebraic space with a Zariski open covering lies on one of the members. -/
private theorem exists_mem_range_pointsMap_ι_of_isZariskiCover
    (hX : IsAlgebraicSpace B S hS X) (I : Type u) (Xᵢ : I → Subfunctor X)
    (hcover : IsZariskiCover B S hS I Xᵢ) (x : points B S hS X) :
    ∃ (i : I) (y : points B S hS (Xᵢ i).toFunctor),
      pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι y = x := by
  have hmem : x ∈ ⋃ i, Set.range (pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι) := by
    rw [(isZariskiCover_iff_iUnion_points B S hS X hX I Xᵢ hcover.1).mp hcover]
    exact Set.mem_univ x
  exact Set.mem_iUnion.mp hmem

/-- Condition `(α)` is Zariski local: an algebraic space with a Zariski open covering by open
subspaces satisfying condition `(α)` satisfies condition `(α)`. -/
@[stacks 03KE "the case (alpha)"]
theorem hasFiniteChartFibersAtEveryPoint_of_isZariskiCover (hX : IsAlgebraicSpace B S hS X)
    (I : Type u) (Xᵢ : I → Subfunctor X) (hcover : IsZariskiCover B S hS I Xᵢ)
    (hα : ∀ i : I, HasFiniteChartFibersAtEveryPoint B S hS (Xᵢ i).toFunctor) :
    HasFiniteChartFibersAtEveryPoint B S hS X := by
  classical
  intro x U hUaff φ hφ
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  set T := (BigFppfOver.toScheme B S hS).obj U with hT
  set e := schemePointsHomeomorph B S hS U with he
  have hopen : ∀ i, IsOpen (Set.range (pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι)) :=
    fun i ↦ isOpen_range_pointsMap_of_isEtale B S hS (Xᵢ i).ι (hcover.1 i).1 hX
      (isEtale_ι_of_isOpenSubspace (hcover.1 i))
  set W : I → Set T := fun i ↦ e.symm ⁻¹' (pointsMap B S hS (yoneda.obj U) φ ⁻¹'
    Set.range (pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι)) with hW
  have hWopen : ∀ i, IsOpen (W i) := fun i ↦
    ((hopen i).preimage (continuous_pointsMap B S hS φ)).preimage e.symm.continuous
  have hWmem : ∀ (i : I) (z : points B S hS (yoneda.obj U)),
      pointsToScheme B S hS U z ∈ W i ↔ pointsMap B S hS (yoneda.obj U) φ z ∈
        Set.range (pointsMap B S hS (Xᵢ i).toFunctor (Xᵢ i).ι) := by
    intro i z
    simp only [hW, Set.mem_preimage]
    rw [show e.symm (pointsToScheme B S hS U z) = z from e.symm_apply_apply z]
  have hWcover : ∀ t : T, ∃ i, t ∈ W i := by
    intro t
    obtain ⟨i, hi⟩ := exists_mem_range_pointsMap_ι_of_isZariskiCover B S hS X hX I Xᵢ hcover
      (pointsMap B S hS (yoneda.obj U) φ (e.symm t))
    exact ⟨i, hi⟩
  set J := {p : Σ _ : I, T.affineOpens // ((p.2 : T.Opens) : Set T) ⊆ W p.1} with hJ
  have hJcover : (Set.univ : Set T) ⊆ ⋃ j : J, ((j.1.2 : T.Opens) : Set T) := by
    rintro t -
    obtain ⟨i, hi⟩ := hWcover t
    obtain ⟨-, ⟨V₀, hV₀, rfl⟩, htV, hVsub⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open hi (hWopen i)
    exact Set.mem_iUnion.mpr ⟨⟨⟨i, ⟨V₀, hV₀⟩⟩, hVsub⟩, htV⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun j : J ↦ ((j.1.2 : T.Opens) : Set T)) (fun j ↦ (j.1.2 : T.Opens).isOpen) hJcover
  choose V inc hincOpen hincRange hVaff using fun j : J ↦
    BigFppfOver.exists_affineOpen_restrict B S hS U j.1.2
  have hincEtale : ∀ j : J, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map (inc j) ≫ φ) := by
    intro j
    have _ : AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (inc j)) := hincOpen j
    exact etale_comp_of_scheme B S hS (inc j) φ inferInstance hφ
  have hfactor : ∀ j : J, ∃ g : yoneda.obj (V j) ⟶ (Xᵢ j.1.1).toFunctor,
      g ≫ (Xᵢ j.1.1).ι = yoneda.map (inc j) ≫ φ := by
    intro j
    refine (factorsThrough_openSubspace_iff_points B S hS hX
      (isAlgebraicSpace_yoneda B S hS (V j)) (Xᵢ j.1.1) (hcover.1 j.1.1) _).2 ?_
    rintro - ⟨w, rfl⟩
    set z := pointsMap B S hS (yoneda.obj (V j)) (yoneda.map (inc j)) w with hz
    have hmem : pointsToScheme B S hS U z ∈ ((j.1.2 : T.Opens) : Set T) := by
      rw [hz, pointsToScheme_pointsMap, ← hincRange j]
      exact Set.mem_range_self _
    rw [pointsMap_comp_apply]
    exact (hWmem j.1.1 z).1 (j.2 hmem)
  have hfinite : ∀ j : J, (pointsMap B S hS (yoneda.obj (V j))
      (yoneda.map (inc j) ≫ φ) ⁻¹' {x}).Finite := by
    intro j
    obtain ⟨g, hg⟩ := hfactor j
    have hgEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g :=
      MorphismProperty.presheaf_of_comp_mono _ (by rw [hg]; exact hincEtale j)
    rcases Set.eq_empty_or_nonempty (pointsMap B S hS (yoneda.obj (V j))
      (yoneda.map (inc j) ≫ φ) ⁻¹' {x}) with hempty | ⟨p, hp⟩
    · rw [hempty]
      exact Set.finite_empty
    · refine (hα j.1.1 (pointsMap B S hS (yoneda.obj (V j)) g p) (V j) (hVaff j) g
        hgEtale).subset fun q hq ↦ ?_
      refine pointsMap_injective_of_mono B S hS (Xᵢ j.1.1).ι ?_
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hg]
      exact hq.trans hp.symm
  refine ((s.finite_toSet.biUnion fun j _ ↦ (hfinite j).image
    (pointsMap B S hS (yoneda.obj (V j)) (yoneda.map (inc j)))).subset fun q hq ↦ ?_)
  obtain ⟨j, hjs, hjmem⟩ :=
    Set.mem_iUnion₂.mp (hs (Set.mem_univ (pointsToScheme B S hS U q)))
  obtain ⟨r, hr⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS (inc j) q
    (by rw [hincRange j]; exact hjmem)
  refine Set.mem_biUnion hjs ⟨r, ?_, hr⟩
  rwa [Set.mem_preimage, pointsMap_comp_apply, hr]

/-- A cartesian square stays cartesian after composing both maps into its corner with a
monomorphism. -/
private theorem isPullback_comp_mono {C : Type u₁} [Category.{u₂} C] {W A A' Z Z' : C}
    {p : W ⟶ A} {q : W ⟶ A'} {f : A ⟶ Z} {g : A' ⟶ Z} (h : IsPullback p q f g)
    (m : Z ⟶ Z') [Mono m] : IsPullback p q (f ≫ m) (g ≫ m) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono f g m
    (PullbackCone.mk p q h.w) h.isLimit)

/-- Condition `(β)` is Zariski local: an algebraic space with a Zariski open covering by open
subspaces satisfying condition `(β)` satisfies condition `(β)`. -/
@[stacks 03KE "the case (beta)"]
theorem hasFiniteRelationFibersAtEveryPoint_of_isZariskiCover
    (hX : IsAlgebraicSpace B S hS X) (I : Type u) (Xᵢ : I → Subfunctor X)
    (hcover : IsZariskiCover B S hS I Xᵢ)
    (hβ : ∀ i : I, HasFiniteRelationFibersAtEveryPoint B S hS (Xᵢ i).toFunctor) :
    HasFiniteRelationFibersAtEveryPoint B S hS X := by
  intro x
  obtain ⟨i, y, hy⟩ :=
    exists_mem_range_pointsMap_ι_of_isZariskiCover B S hS X hX I Xᵢ hcover x
  obtain ⟨U, f, a, b, hf, ha, hb, hfin⟩ := hβ i y
  refine ⟨U, f ≫ (Xᵢ i).ι, a, b,
    isEtale_comp B S hS hf (isEtale_ι_of_isOpenSubspace (hcover.1 i)),
    by rw [pointsMap_comp_apply, ha]; exact hy,
    by rw [pointsMap_comp_apply, hb]; exact hy, ?_⟩
  have hpb : IsPullback (pullback.fst f f) (pullback.snd f f)
      (f ≫ (Xᵢ i).ι) (f ≫ (Xᵢ i).ι) :=
    isPullback_comp_mono (IsPullback.of_hasPullback f f) (Xᵢ i).ι
  change {r : points B S hS (pullback (f ≫ (Xᵢ i).ι) (f ≫ (Xᵢ i).ι)) |
    pointsMap B S hS _ (pullback.fst (f ≫ (Xᵢ i).ι) (f ≫ (Xᵢ i).ι)) r = a ∧
    pointsMap B S hS _ (pullback.snd (f ≫ (Xᵢ i).ι) (f ≫ (Xᵢ i).ι)) r = b}.Finite
  refine (hfin.image (pointsMap B S hS (pullback f f) hpb.isoPullback.hom)).subset ?_
  rintro r ⟨hr₁, hr₂⟩
  refine ⟨pointsMap B S hS _ hpb.isoPullback.inv r, ⟨?_, ?_⟩,
    (pointsHomeomorphOfIso B S hS hpb.isoPullback).right_inv r⟩
  · rwa [← pointsMap_comp_apply, hpb.isoPullback_inv_fst]
  · rwa [← pointsMap_comp_apply, hpb.isoPullback_inv_snd]

/-- Condition `(γ)` is Zariski local: an algebraic space with a Zariski open covering by open
subspaces satisfying condition `(γ)` satisfies condition `(γ)`. -/
@[stacks 03KE "the case (gamma)"]
theorem hasFiniteChartAndRelationFibersAtEveryPoint_of_isZariskiCover
    (hX : IsAlgebraicSpace B S hS X) (I : Type u) (Xᵢ : I → Subfunctor X)
    (hcover : IsZariskiCover B S hS I Xᵢ)
    (hγ : ∀ i : I, HasFiniteChartAndRelationFibersAtEveryPoint B S hS (Xᵢ i).toFunctor) :
    HasFiniteChartAndRelationFibersAtEveryPoint B S hS X := by
  have h : ∀ i : I, HasFiniteChartFibersAtEveryPoint B S hS (Xᵢ i).toFunctor ∧
      HasFiniteRelationFibersAtEveryPoint B S hS (Xᵢ i).toFunctor := fun i ↦
    (hasFiniteChartAndRelationFibersAtEveryPoint_iff_alpha_and_beta B S hS
      (Xᵢ i).toFunctor (hcover.1 i).1).1 (hγ i)
  exact (hasFiniteChartAndRelationFibersAtEveryPoint_iff_alpha_and_beta
      B S hS X hX).2
    ⟨hasFiniteChartFibersAtEveryPoint_of_isZariskiCover B S hS X hX I Xᵢ hcover
        fun i ↦ (h i).1,
      hasFiniteRelationFibersAtEveryPoint_of_isZariskiCover B S hS X hX I Xᵢ hcover
        fun i ↦ (h i).2⟩

section Relocalize

variable {C : Type u₁} [Category.{u} C]

/-- A section of a presheaf is locally in the image of a morphism descended from a
coproduct exactly when it is locally in the image of one of the members. -/
private theorem imageSieve_sigmaDesc_iff {I : Type u} {F : I → Cᵒᵖ ⥤ Type u}
    {G : Cᵒᵖ ⥤ Type u} (f : ∀ i, F i ⟶ G) {A T : C} (x : G.obj (Opposite.op A))
    (g : T ⟶ A) :
    Presheaf.imageSieve (Sigma.desc f) x g ↔
      ∃ i, ∃ y : (F i).obj (Opposite.op T), (f i).app _ y = G.map g.op x := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨⟨i⟩, z, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation Cᵒᵖ (Type u)).obj (Opposite.op T))
        (colimit.isColimit (Discrete.functor F))) y
    change (Sigma.desc f).app _ ((Sigma.ι F i).app _ z) = _ at hy
    exact ⟨i, z, by
      simpa only [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc] using hy⟩
  · rintro ⟨i, y, hy⟩
    exact ⟨(Sigma.ι F i).app _ y, by
      simpa only [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc] using hy⟩

/-- Local surjectivity of a jointly descended family is inherited by the relocalization of
the family along a morphism of the base. -/
private theorem relocalize_sigmaDesc_isLocallySurjective (J : GrothendieckTopology C)
    {V W : C} (f : V ⟶ W) {I : Type u} {F : I → (Over V)ᵒᵖ ⥤ Type u}
    {G : (Over V)ᵒᵖ ⥤ Type u} (α : ∀ i, F i ⟶ G)
    (hα : Presheaf.IsLocallySurjective (J.over V) (Sigma.desc α)) :
    Presheaf.IsLocallySurjective (J.over W)
      (Sigma.desc fun i ↦ (OverShriek.relocalizePresheafFunctor f).map (α i)) := by
  constructor
  intro A p
  change {p : Σ ψ : A.left ⟶ V, G.obj (Opposite.op (Over.mk ψ)) // p.1 ≫ f = A.hom} at p
  change Sieve.overEquiv A _ ∈ J A.left
  have h := hα.imageSieve_mem p.val.2
  change Sieve.overEquiv (Over.mk p.val.1) _ ∈ J A.left at h
  refine J.superset_covering ?_ h
  intro T g hg
  rw [Sieve.overEquiv_iff] at hg ⊢
  obtain ⟨i, y, hy⟩ := (imageSieve_sigmaDesc_iff (C := Over V) (F := F) (G := G) α
    p.val.2 _).mp hg
  refine (imageSieve_sigmaDesc_iff (C := Over W)
      (F := fun i ↦ (OverShriek.relocalizePresheafFunctor f).obj (F i))
      (G := (OverShriek.relocalizePresheafFunctor f).obj G)
      (fun i ↦ (OverShriek.relocalizePresheafFunctor f).map (α i))
      (show ((OverShriek.relocalizePresheafFunctor f).obj G).obj (Opposite.op A) from p)
      _).mpr ⟨i, ⟨⟨g ≫ p.val.1, y⟩, ?_⟩, ?_⟩
  · change (g ≫ p.val.1) ≫ f = g ≫ A.hom
    rw [Category.assoc, p.property]
  · exact Subtype.ext (congrArg (Sigma.mk (g ≫ p.val.1)) hy)

/-- Local surjectivity passes to a two-step family: if a family is jointly locally
surjective and each of its members is covered by a family of its own, the composites are
jointly locally surjective. -/
private theorem sigmaDesc_comp_isLocallySurjective (J : GrothendieckTopology C) {I : Type u}
    {K : I → Type u} {F : I → Cᵒᵖ ⥤ Type u} {G : ∀ i, K i → Cᵒᵖ ⥤ Type u}
    {Y : Cᵒᵖ ⥤ Type u} (f : ∀ i, F i ⟶ Y) (g : ∀ i j, G i j ⟶ F i)
    (hf : Presheaf.IsLocallySurjective J (Sigma.desc f))
    (hg : ∀ i, Presheaf.IsLocallySurjective J (Sigma.desc (g i))) :
    Presheaf.IsLocallySurjective J
      (Sigma.desc fun p : Σ i, K i ↦ g p.1 p.2 ≫ f p.1) := by
  constructor
  intro A x
  apply J.transitive (hf.imageSieve_mem x)
  intro T t ht
  obtain ⟨i, y, hy⟩ := (imageSieve_sigmaDesc_iff f x t).mp ht
  refine J.superset_covering ?_ ((hg i).imageSieve_mem y)
  intro W w hw
  obtain ⟨j, z, hz⟩ := (imageSieve_sigmaDesc_iff (g i) y w).mp hw
  refine (imageSieve_sigmaDesc_iff _ x (w ≫ t)).mpr ⟨⟨i, j⟩, z, ?_⟩
  change (f i).app _ ((g i j).app _ z) = _
  rw [hz, NatTrans.naturality_apply, hy, op_comp, Y.map_comp_apply]

end Relocalize

/-- The lower-shriek extension of presheaves from the big fppf site of `S` to the big fppf
site of the terminal scheme, as a functor. -/
private noncomputable abbrev toIntegers :
    ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :=
  OverShriek.relocalizePresheafFunctor (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)

/-- The range of an open immersion with algebraic source is an open subspace. -/
private theorem isOpenSubspace_range_of_isOpenImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) [Mono p]
    (hF : IsAlgebraicSpace B S hS F) (hp : IsOpenImmersion B S hS p) :
    IsOpenSubspace B S hS (Subfunctor.range p) := by
  refine ⟨hF.of_iso (asIso (Subfunctor.toRange p)), ?_⟩
  have hfac : (asIso (Subfunctor.toRange p)).inv ≫ p = (Subfunctor.range p).ι :=
    (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι p).symm
  rw [← hfac]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hp

/-- Condition `(ζ)` is Zariski local: an algebraic space with a Zariski open covering by open
subspaces which are Zariski locally quasi-separated is Zariski locally quasi-separated. -/
@[stacks 03KE "the case (zeta)"]
theorem isAbsolutelyZariskiLocallyQuasiSeparated_of_isZariskiCover
    (I : Type u) (Xᵢ : I → Subfunctor X) (hcover : IsZariskiCover B S hS I Xᵢ)
    (hζ : ∀ i : I, IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ (Xᵢ i).toFunctor) :
    IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ X := by
  classical
  have _ : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  choose K U hU hq using hζ
  let ι₀ : ∀ i, viewOverIntegers B S hS hZ (Xᵢ i).toFunctor ⟶
      viewOverIntegers B S hS hZ X := fun i ↦ (toIntegers B S hS hZ).map (Xᵢ i).ι
  have hιOpen : ∀ i, IsOpenImmersion B (⊤_ Scheme.{u}) hZ (ι₀ i) := fun i ↦
    OverShriek.presheaf_map_relocalize _ (fun _ hk ↦ hk) (hcover.1 i).2
  have hfsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ)
      (Sigma.desc ι₀) :=
    relocalize_sigmaDesc_isLocallySurjective B.topology _ _ hcover.2
  set a := fun p : Σ i, K i ↦ (U p.1 p.2).ι ≫ ι₀ p.1 with ha
  have haOpen : ∀ p, IsOpenImmersion B (⊤_ Scheme.{u}) hZ (a p) := fun p ↦
    MorphismProperty.comp_mem _ _ _ ((hU p.1).1 p.2).2 (hιOpen p.1)
  have hamono : ∀ p, Mono (a p) := by
    intro p
    have hle : MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ) ≤
        MorphismProperty.monomorphisms (BigFppfOver B (⊤_ Scheme.{u}) hZ) := by
      intro A A' k hk
      have hmono : Mono ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map k) :=
        AlgebraicGeometry.IsOpenImmersion.le_monomorphisms _ hk
      exact ⟨fun b c hbc ↦ Functor.map_injective (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)
        ((cancel_mono ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map k)).1
          (congrArg (fun m ↦ (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map m) hbc))⟩
    exact MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
      (MorphismProperty.relative_monotone hle _ (haOpen p))
  refine ⟨Σ i, K i, fun p ↦ Subfunctor.range (a p), ⟨fun p ↦ ?_, ?_⟩, fun p ↦ ?_⟩
  · have _ : Mono (a p) := hamono p
    exact isOpenSubspace_range_of_isOpenImmersion B (⊤_ Scheme.{u}) hZ (a p)
      ((hU p.1).1 p.2).1 (haOpen p)
  · have hstep := sigmaDesc_comp_isLocallySurjective
      (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ) ι₀
      (fun i j ↦ (U i j).ι) hfsurj fun i ↦ (hU i).2
    constructor
    intro A x
    refine (BigFppfOver.topology B (⊤_ Scheme.{u}) hZ).superset_covering ?_
      (hstep.imageSieve_mem x)
    intro T t ht
    obtain ⟨p, y, hy⟩ := (imageSieve_sigmaDesc_iff a x t).mp ht
    exact (imageSieve_sigmaDesc_iff (fun p ↦ (Subfunctor.range (a p)).ι) x t).mpr
      ⟨p, (Subfunctor.toRange (a p)).app _ y, hy⟩
  · have _ : Mono (a p) := hamono p
    exact isQuasiSeparatedOver_of_iso B (⊤_ Scheme.{u}) hZ
      (asIso (Subfunctor.toRange (a p))) (hq p.1 p.2)

/-! ### The implication `(θ) ⇒ (ζ)` -/

/-- An open immersion from an affine object of the site has an open subspace as its range,
and that open subspace is a quasi-separated scheme. -/
private theorem isOpenSubspace_and_isQuasiSeparatedScheme_range
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W : BigFppfOver B S hS) (p : yoneda.obj W ⟶ F)
    [Mono p] (hp : IsOpenImmersion B S hS p)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    IsOpenSubspace B S hS (Subfunctor.range p) ∧
      IsQuasiSeparatedScheme B S hS (Subfunctor.range p).toFunctor :=
  ⟨isOpenSubspace_range_of_isOpenImmersion B S hS p (isAlgebraicSpace_yoneda B S hS W) hp,
    W, inferInstance, ⟨Functor.representableByEquiv.symm (asIso (Subfunctor.toRange p))⟩⟩

/-- Condition `(θ)` implies condition `(ζ)`: a representable algebraic space over `S` is
Zariski locally quasi-separated. -/
@[stacks 03JX "(theta) implies (zeta)"]
theorem isAbsolutelyZariskiLocallyQuasiSeparated_of_isRepresentable
    (hX : IsAlgebraicSpace B S hS X) (h : X.IsRepresentable) :
    IsAbsolutelyZariskiLocallyQuasiSeparated B S hS hZ X := by
  classical
  obtain ⟨U, ⟨hrep⟩⟩ := h.has_representation
  let e : yoneda.obj U ≅ X := Functor.representableByEquiv hrep
  have _ : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have _ : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  choose V inc hincOpen hincRange hVaff using fun W :
      ((BigFppfOver.toScheme B S hS).obj U).affineOpens ↦
    BigFppfOver.exists_affineOpen_restrict B S hS U W
  have hmono : ∀ W, Mono (yoneda.map (inc W) ≫ e.hom) := by
    intro W
    have _ : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (inc W)) := hincOpen W
    have _ : Mono (inc W) := Functor.mono_of_mono_map (BigFppfOver.toScheme B S hS)
      (inferInstance : Mono ((BigFppfOver.toScheme B S hS).map (inc W)))
    infer_instance
  have hopen : ∀ W, IsOpenImmersion B S hS (yoneda.map (inc W) ≫ e.hom) := by
    intro W
    refine MorphismProperty.comp_mem _ _ _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (inc W)).2 (hincOpen W)) ?_
    exact presheaf_inverseImage_of_isIso B S hS
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      MorphismProperty.IsStableUnderBaseChange.respectsIso (fun _ ↦ inferInstance) e.hom
      inferInstance
  have hdata : ∀ W, IsOpenSubspace B S hS (Subfunctor.range (yoneda.map (inc W) ≫ e.hom)) ∧
      IsQuasiSeparatedScheme B S hS
        (Subfunctor.range (yoneda.map (inc W) ≫ e.hom)).toFunctor := by
    intro W
    have _ := hmono W
    exact isOpenSubspace_and_isQuasiSeparatedScheme_range B S hS (V W) _ (hopen W) (hVaff W)
  refine isAbsolutelyZariskiLocallyQuasiSeparated_of_isZariskiCover B S hS X hZ
    ((BigFppfOver.toScheme B S hS).obj U).affineOpens
    (fun W ↦ Subfunctor.range (yoneda.map (inc W) ≫ e.hom)) ?_ fun W ↦
      isAbsolutelyZariskiLocallyQuasiSeparated_of_isAbsolutelyQuasiSeparated B S hS _ hZ
        (hdata W).1.1 (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
          (hdata W).2)
  refine (isZariskiCover_iff_iUnion_points B S hS X hX _ _ fun W ↦ (hdata W).1).2 ?_
  refine Set.eq_univ_iff_forall.2 fun x ↦ ?_
  set y := pointsMap B S hS X e.inv x with hy
  have hyx : pointsMap B S hS (yoneda.obj U) e.hom y = x :=
    (pointsHomeomorphOfIso B S hS e).right_inv x
  obtain ⟨-, ⟨W₀, hW₀, rfl⟩, hmem, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (pointsToScheme B S hS U y)) isOpen_univ
  obtain ⟨r, hr⟩ := exists_pointsMap_yonedaMap_eq_of_mem_range B S hS (inc ⟨W₀, hW₀⟩) y
    (by rw [hincRange ⟨W₀, hW₀⟩]; exact hmem)
  have _ := hmono ⟨W₀, hW₀⟩
  refine Set.mem_iUnion.2 ⟨⟨W₀, hW₀⟩, ?_⟩
  rw [range_pointsMap_ι_range B S hS (yoneda.map (inc ⟨W₀, hW₀⟩) ≫ e.hom)]
  exact ⟨r, by rw [pointsMap_comp_apply, hr, hyx]⟩

end AlgebraicGeometry.Space

end
