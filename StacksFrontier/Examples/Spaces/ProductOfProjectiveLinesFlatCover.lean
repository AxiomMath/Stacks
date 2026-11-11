module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProductsFlat
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.InfiniteProductsSurjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.Examples.Spaces.ProductOfProjectiveLinesCover

/-!
# A surjective covering of the functor of infinite tuples of points of a scheme

Let `P` be a separated scheme and `q : X ⟶ P` an affine morphism from an affine scheme. The
morphism of presheaves `powCover q : X^ι ⟶ powPresheaf ι P` of
`StacksFrontier/Examples/Spaces/ProductOfProjectiveLinesCover.lean` has, as base change along a
scheme-valued point `B` of `powPresheaf ι P` with source `T`, the product over `T` of the base
changes `X ×_{q, P, Bᵢ} T` of `q` along the components `Bᵢ : T ⟶ P` of `B`. Properties of the
structure morphism of an infinite product of affine morphisms therefore give properties of
`powCover q`: it is surjective, flat and universally open as soon as `q` is flat and universally
open and every point of `P` with values in a field lifts along `q`.

For `P = ℙ¹` and `q` the morphism to `ℙ¹` from the disjoint union of its two standard affine
charts, all hypotheses hold, and the functor `(ℙ¹)^∞` receives from the affine scheme
`(𝔸¹ ⊔ 𝔸¹)^∞` a representable morphism of presheaves which is surjective, flat, universally open
and quasi-compact.

## Main definitions

* `AlgebraicGeometry.powCoverFactor`: the base change of `q` along a component of a
  scheme-valued point of `powPresheaf ι P`, as a scheme over the source of that point.
* `AlgebraicGeometry.powCoverProductIso`: the product of these base changes is the base change
  of `powCover q` constructed in `AlgebraicGeometry.powPresheaf.fibre`.
* `AlgebraicGeometry.projectiveLineCoordChart` and `AlgebraicGeometry.projectiveLineCoordChartι`:
  the standard affine chart of `ℙ¹` where a given homogeneous coordinate does not vanish.
* `AlgebraicGeometry.projectiveLineChartCover` and `AlgebraicGeometry.projectiveLineChartCoverπ`:
  the disjoint union of the two standard charts, an affine scheme, and its map to `ℙ¹`.
* `AlgebraicGeometry.projectiveLinePowFlatCover`: the induced morphism to `(ℙ¹)^∞` from the
  `ULift ℕ`-fold product of that affine scheme.

## Main results

* `AlgebraicGeometry.presheaf_powCover_of_product`: a property of morphisms of schemes that
  respects isomorphisms holds for `powCover q`, in the sense of
  `CategoryTheory.MorphismProperty.presheaf`, as soon as it holds for the structure morphisms of
  all the products of base changes of `q`.
* `AlgebraicGeometry.universallyOpen_presheaf_powCover_of_isOpenMap`: universal openness of
  `powCover q` follows from openness of those structure morphisms.
* `AlgebraicGeometry.surjective_presheaf_powCover`, `AlgebraicGeometry.flat_presheaf_powCover`
  and `AlgebraicGeometry.universallyOpen_presheaf_powCover`: `powCover q` is surjective, flat and
  universally open, under the corresponding hypotheses on `q`.
* `AlgebraicGeometry.exists_comp_projectiveLineChartCoverπ`: every point of `ℙ¹` with values in
  a field lifts to the disjoint union of the two standard charts.
* `AlgebraicGeometry.surjective_presheaf_projectiveLinePowFlatCover`,
  `AlgebraicGeometry.flat_presheaf_projectiveLinePowFlatCover`,
  `AlgebraicGeometry.universallyOpen_presheaf_projectiveLinePowFlatCover` and
  `AlgebraicGeometry.quasiCompact_presheaf_projectiveLinePowFlatCover`: the four properties of
  the covering of `(ℙ¹)^∞`, collected in
  `AlgebraicGeometry.exists_surjective_flat_universallyOpen_quasiCompact_projectiveLinePow`.

## Implementation notes

The base change of `powCover q` along `B` is the closed subscheme
`AlgebraicGeometry.powPresheaf.fibre (powCover q) B` of `X^ι × T`. It is compared with the
product, in the category of schemes over `T`, of the objects `X ×_{q, P, Bᵢ} T ⟶ T`, which exists
by `AlgebraicGeometry.hasProduct_of_isAffineHom` because `q` is affine. Both represent the same
data: a morphism `b : W ⟶ T` together with a lift of every `Bᵢ ∘ b` along `q`, and the two
comparison morphisms are mutually inverse by the extensionality of each side.

Universal openness is not a property of a single base change: the base changes of
`fibre (powCover q) B ⟶ T` along morphisms `T' ⟶ T` are again base changes of `powCover q`, by
pasting pullback squares of presheaves, which is
`CategoryTheory.MorphismProperty.relative.universally`. The base changes of an infinite product
of universally open affine morphisms are again such products, so openness of the structure
morphism of every such product suffices; that openness is
`AlgebraicGeometry.isOpenMap_product_hom`, which needs the lifting of points with values in a
field. Surjectivity and flatness are `AlgebraicGeometry.surjective_product_hom` and
`AlgebraicGeometry.flat_product_hom`.

The covering of `ℙ¹` used is the disjoint union of the two standard affine charts rather than
the morphism `SL₂ ⟶ ℙ¹` of the Stacks Project's argument; any flat universally open affine
morphism from an affine scheme to `ℙ¹` along which every point with values in a field lifts
serves equally.

## References

* [Stacks Project, Tag 078F](https://stacks.math.columbia.edu/tag/078F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}
  [PreservesLimitsOfShape WalkingCospan F] {P : MorphismProperty C}

/-- If every represented base change of a morphism `f` satisfies `P`, then every represented
base change of it satisfies `P` universally: a base change of a represented base change is
again a represented base change, when `F` preserves pullbacks. -/
lemma relative.universally {X Y : D} {f : X ⟶ Y} (hf : P.relative F f) :
    P.universally.relative F f :=
  ⟨hf.rep, fun _ _ g fst _ h _ _ i₁ i₂ f' sq ↦
    hf.property (F.map i₂ ≫ g) (F.map i₁ ≫ fst) f' ((sq.flip.map F).paste_horiz h)⟩

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

namespace powPresheaf

variable {ι : Type u} {P T : Scheme.{u}}

/-- The `i`-th component `T ⟶ P` of a scheme-valued point of `powPresheaf ι P` with source
`T`. -/
def component (B : yoneda.obj T ⟶ powPresheaf ι P) (i : ι) : T ⟶ P := yonedaEquiv B i

end powPresheaf

open powPresheaf

section FibreProduct

variable {ι : Type u} {X P : Scheme.{u}} [IsAffine X] [P.IsSeparated] (q : X ⟶ P)
  [IsAffineHom q] {T : Scheme.{u}} (B : yoneda.obj T ⟶ powPresheaf ι P)

/-- The base change of `q : X ⟶ P` along the `i`-th component `T ⟶ P` of a scheme-valued point
`B` of `powPresheaf ι P`, as a scheme over `T`. -/
abbrev powCoverFactor (i : ι) : Over T := Over.mk (pullback.snd q (component B i))

omit [IsAffine X] [P.IsSeparated] in
/-- The base change of an affine morphism along a component of a scheme-valued point is
affine. -/
instance isAffineHom_powCoverFactor_hom (i : ι) : IsAffineHom (powCoverFactor q B i).hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q _)
    ‹IsAffineHom q›

omit [IsAffine X] [P.IsSeparated] in
/-- The base changes of an affine morphism along the components of a scheme-valued point have a
product over the source of that point. -/
instance hasProduct_powCoverFactor : HasProduct (powCoverFactor q B) :=
  hasProduct_of_isAffineHom T _ fun i ↦ (powCoverFactor q B i).hom

/-- The comparison morphism from the product of the base changes of `q` along the components
of `B` to the base change of `powCover q` along `B`. -/
def powCoverProductToFibre :
    ∏ᶜ powCoverFactor q B ⟶ Over.mk (fibreι (powCover (ι := ι) q) B ≫ prod.snd) :=
  Over.homMk
    (fibreLift (powCover q) B
      (affinePowLift ι X fun i ↦ (Pi.π (powCoverFactor q B) i).left ≫ pullback.fst _ _)
      (∏ᶜ powCoverFactor q B).hom fun i ↦ by
        change _ = _ ≫ component B i
        rw [yonedaEquiv_powCover, affinePowLift_π_assoc, Category.assoc, pullback.condition,
          ← Over.w (Pi.π (powCoverFactor q B) i)]
        simp)
    (by simp)

/-- The comparison morphism from the base change of `powCover q` along `B` to the product of
the base changes of `q` along the components of `B`. -/
def powCoverFibreToProduct :
    Over.mk (fibreι (powCover (ι := ι) q) B ≫ prod.snd) ⟶ ∏ᶜ powCoverFactor q B :=
  Pi.lift fun i ↦ Over.homMk
    (pullback.lift (fibreι (powCover q) B ≫ prod.fst ≫ affinePowπ ι X i)
      (fibreι (powCover q) B ≫ prod.snd)
      (by simpa [component] using fibreι_comp (powCover q) B i))
    (pullback.lift_snd _ _ _)

omit [P.IsSeparated] in
/-- The comparison morphism to the base change of `powCover q` along `B`, followed by the
inclusion of that base change into `X^ι × T`. -/
@[reassoc (attr := simp)]
lemma powCoverProductToFibre_left_fibreι :
    (powCoverProductToFibre q B).left ≫ fibreι (powCover q) B =
      prod.lift
        (affinePowLift ι X fun i ↦ (Pi.π (powCoverFactor q B) i).left ≫ pullback.fst _ _)
        (∏ᶜ powCoverFactor q B).hom := by
  simp [powCoverProductToFibre]

/-- The components of the comparison morphism to the product of the base changes of `q`. -/
@[reassoc (attr := simp)]
lemma powCoverFibreToProduct_left_π_left (i : ι) :
    (powCoverFibreToProduct q B).left ≫ (Pi.π (powCoverFactor q B) i).left =
      pullback.lift (fibreι (powCover q) B ≫ prod.fst ≫ affinePowπ ι X i)
        (fibreι (powCover q) B ≫ prod.snd)
        (by simpa [component] using fibreι_comp (powCover q) B i) := by
  rw [← Over.comp_left, powCoverFibreToProduct, Pi.lift_comp_π]
  rfl

/-- The base change of `powCover q` along a scheme-valued point `B` of `powPresheaf ι P` is the
product over the source of `B` of the base changes of `q` along the components of `B`. -/
def powCoverProductIso :
    ∏ᶜ powCoverFactor q B ≅ Over.mk (fibreι (powCover (ι := ι) q) B ≫ prod.snd) where
  hom := powCoverProductToFibre q B
  inv := powCoverFibreToProduct q B
  hom_inv_id := by
    refine Pi.hom_ext _ _ fun i ↦ Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · simp only [Over.comp_left, Category.assoc, Category.id_comp,
        powCoverFibreToProduct_left_π_left_assoc]
      rw [pullback.lift_fst]
      simp
    · simp only [Over.comp_left, Category.assoc, Category.id_comp,
        powCoverFibreToProduct_left_π_left_assoc]
      rw [pullback.lift_snd]
      simpa using (Over.w (Pi.π (powCoverFactor q B) i)).symm
  inv_hom_id := by
    refine Over.OverMorphism.ext ((cancel_mono (fibreι (powCover q) B)).1 (prod.hom_ext ?_ ?_))
    · refine affinePow_hom_ext ι X fun i ↦ ?_
      simp only [Over.comp_left, Category.assoc,
        powCoverProductToFibre_left_fibreι, prod.lift_fst_assoc, affinePowLift_π,
        powCoverFibreToProduct_left_π_left_assoc]
      rw [pullback.lift_fst]
      simp
    · simp

/-- A property of morphisms of schemes that respects isomorphisms holds for the base change of
`powCover q` along `B` as soon as it holds for the structure morphism of the product of the
base changes of `q` along the components of `B`. -/
theorem fibreι_comp_snd_of_product {P' : MorphismProperty Scheme.{u}} [P'.RespectsIso]
    (h : P' (∏ᶜ powCoverFactor q B).hom) :
    P' (fibreι (powCover (ι := ι) q) B ≫ prod.snd) := by
  refine (P'.arrow_mk_iso_iff (Arrow.isoMk ((Over.forget T).mapIso (powCoverProductIso q B))
    (Iso.refl _) ?_)).1 h
  simpa using Over.w (powCoverProductIso q B).hom

/-- A property of morphisms of schemes that respects isomorphisms holds for `powCover q`, in
the sense of `CategoryTheory.MorphismProperty.presheaf`, as soon as it holds for the structure
morphism of every product of base changes of `q` along the components of a scheme-valued point
of `powPresheaf ι P`. -/
theorem presheaf_powCover_of_product {P' : MorphismProperty Scheme.{u}} [P'.RespectsIso]
    (h : ∀ (T : Scheme.{u}) (B : yoneda.obj T ⟶ powPresheaf ι P),
      P' (∏ᶜ powCoverFactor q B).hom) :
    MorphismProperty.presheaf P' (powCover (ι := ι) q) :=
  MorphismProperty.relative.of_exists fun T B ↦
    ⟨fibre _ B, yoneda.map (fibreι _ B ≫ prod.fst), fibreι _ B ≫ prod.snd, isPullback_fibre _ B,
      fibreι_comp_snd_of_product q B (h T B)⟩

/-- `powCover q` is universally open, in the sense of `CategoryTheory.MorphismProperty.presheaf`,
as soon as the structure morphism of every product of base changes of `q` along the components
of a scheme-valued point of `powPresheaf ι P` is an open map. -/
theorem universallyOpen_presheaf_powCover_of_isOpenMap
    (h : ∀ (T : Scheme.{u}) (B : yoneda.obj T ⟶ powPresheaf ι P),
      IsOpenMap (∏ᶜ powCoverFactor q B).hom.base) :
    MorphismProperty.presheaf (C := Scheme.{u}) @UniversallyOpen (powCover (ι := ι) q) := by
  rw [UniversallyOpen.eq]
  exact (presheaf_powCover_of_product (P' := topologically @IsOpenMap) q h).universally

end FibreProduct

section Lifting

variable {X P : Scheme.{u}} (q : X ⟶ P)

/-- If every point of `P` with values in a field lifts along `q`, then so does every point of
the source of a base change of `q`. -/
theorem exists_comp_pullback_snd_eq
    (hq : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ P), ∃ y, y ≫ q = x)
    {T : Scheme.{u}} (g : T ⟶ P) (K : Type u) [Field K] (x : Spec (.of K) ⟶ T) :
    ∃ y : Spec (.of K) ⟶ pullback q g, y ≫ pullback.snd q g = x := by
  obtain ⟨y, hy⟩ := hq K (x ≫ g)
  exact ⟨pullback.lift y x hy, pullback.lift_snd _ _ _⟩

/-- A morphism along which every point with values in a field lifts is surjective. -/
theorem surjective_of_exists_comp_eq
    (hq : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ P), ∃ y, y ≫ q = x) : Surjective q := by
  refine ⟨fun s ↦ ?_⟩
  obtain ⟨y, hy⟩ := hq (P.residueField s) (P.fromSpecResidueField s)
  let z : Spec (P.residueField s) := IsLocalRing.closedPoint (P.residueField s)
  refine ⟨y z, ?_⟩
  rw [← Scheme.Hom.comp_apply, hy, Scheme.fromSpecResidueField_apply]

end Lifting

section PowCoverProperties

variable {ι : Type u} {X P : Scheme.{u}} [IsAffine X] [P.IsSeparated] (q : X ⟶ P)
  [IsAffineHom q]

/-- `powCover q` is surjective, in the sense of `CategoryTheory.MorphismProperty.presheaf`, when
every point of `P` with values in a field lifts along `q`. -/
theorem surjective_presheaf_powCover
    (hq : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ P), ∃ y, y ≫ q = x) :
    MorphismProperty.presheaf (C := Scheme.{u}) @Surjective (powCover (ι := ι) q) := by
  have : Surjective q := surjective_of_exists_comp_eq q hq
  refine presheaf_powCover_of_product q fun T B ↦ ?_
  have (i : ι) : Surjective (powCoverFactor q B i).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q _)
      ‹Surjective q›
  exact surjective_product_hom T _ fun i ↦ (powCoverFactor q B i).hom

/-- `powCover q` is flat, in the sense of `CategoryTheory.MorphismProperty.presheaf`, when `q`
is flat. -/
theorem flat_presheaf_powCover [Flat q] :
    MorphismProperty.presheaf (C := Scheme.{u}) @Flat (powCover (ι := ι) q) := by
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine presheaf_powCover_of_product q fun T B ↦ ?_
  have (i : ι) : Flat (powCoverFactor q B i).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q _)
      ‹Flat q›
  exact flat_product_hom T _ fun i ↦ (powCoverFactor q B i).hom

/-- `powCover q` is universally open, in the sense of `CategoryTheory.MorphismProperty.presheaf`,
when `q` is universally open and every point of `P` with values in a field lifts along `q`. -/
theorem universallyOpen_presheaf_powCover [UniversallyOpen q]
    (hq : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ P), ∃ y, y ≫ q = x) :
    MorphismProperty.presheaf (C := Scheme.{u}) @UniversallyOpen (powCover (ι := ι) q) := by
  refine universallyOpen_presheaf_powCover_of_isOpenMap q fun T B ↦ ?_
  have (i : ι) : UniversallyOpen (powCoverFactor q B i).hom :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q _)
      ‹UniversallyOpen q›
  refine isOpenMap_product_hom T _ (fun i ↦ (powCoverFactor q B i).hom) ?_
  intro K _ x i
  exact exists_comp_pullback_snd_eq q hq (component B i) K x

end PowCoverProperties

section ProjectiveLineCharts

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard affine chart of `ℙ¹` where the homogeneous coordinate `T_b` does not vanish:
the spectrum of the degree-zero part of the localization of `ℤ[T₀, T₁]` at `T_b`. -/
def projectiveLineCoordChart (b : Fin 2) : Scheme.{u} :=
  Spec (.of <| HomogeneousLocalization.Away
    (MvPolynomial.homogeneousSubmodule (Fin 2) (ULift.{u} ℤ)) (MvPolynomial.X b))

/-- The standard affine charts of `ℙ¹` are affine. -/
instance isAffine_projectiveLineCoordChart (b : Fin 2) :
    IsAffine (projectiveLineCoordChart.{u} b) :=
  inferInstanceAs (IsAffine (Spec _))

/-- The homogeneous coordinates of `ℤ[T₀, T₁]` are homogeneous of degree one. -/
lemma mvPolynomialX_mem_homogeneousSubmodule_one' (b : Fin 2) :
    (MvPolynomial.X b : MvPolynomial (Fin 2) (ULift.{u} ℤ)) ∈
      MvPolynomial.homogeneousSubmodule (Fin 2) (ULift.{u} ℤ) 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X _ _)

/-- The inclusion of the standard affine chart of `ℙ¹` where `T_b` does not vanish. -/
def projectiveLineCoordChartι (b : Fin 2) :
    projectiveLineCoordChart.{u} b ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  Proj.awayι _ (MvPolynomial.X b) (mvPolynomialX_mem_homogeneousSubmodule_one'.{u} b) Nat.one_pos

/-- The inclusion of a standard affine chart of `ℙ¹` is an open immersion. -/
instance isOpenImmersion_projectiveLineCoordChartι (b : Fin 2) :
    IsOpenImmersion (projectiveLineCoordChartι.{u} b) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι ..))

/-- The image of the standard affine chart of `ℙ¹` where `T_b` does not vanish is the standard
open set `D₊(T_b)`. -/
lemma opensRange_projectiveLineCoordChartι (b : Fin 2) :
    (projectiveLineCoordChartι.{u} b).opensRange =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ULift.{u} ℤ))
        (MvPolynomial.X b) :=
  Proj.opensRange_awayι ..

/-- The disjoint union of the two standard affine charts of `ℙ¹`. -/
abbrev projectiveLineChartCover : Scheme.{u} := ∐ projectiveLineCoordChart.{u}

/-- The disjoint union of the two standard affine charts of `ℙ¹` is affine. -/
instance isAffine_projectiveLineChartCover : IsAffine projectiveLineChartCover.{u} :=
  inferInstanceAs (IsAffine (∐ _))

/-- The morphism from the disjoint union of the two standard affine charts of `ℙ¹` to `ℙ¹`. -/
def projectiveLineChartCoverπ : projectiveLineChartCover.{u} ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  Sigma.desc projectiveLineCoordChartι

/-- The morphism from the disjoint union of the two standard charts to `ℙ¹` is affine: its
source is affine and `ℙ¹` is separated. -/
instance isAffineHom_projectiveLineChartCoverπ : IsAffineHom projectiveLineChartCoverπ.{u} :=
  IsAffineHom.of_comp _ (terminal.from (projectiveSpaceAtUniverse.{u} 1))

/-- The morphism from the disjoint union of the two standard charts to `ℙ¹` is flat, being an
open immersion on each chart. -/
instance flat_projectiveLineChartCoverπ : Flat projectiveLineChartCoverπ.{u} :=
  inferInstanceAs (Flat (Sigma.desc _))

/-- The morphism from the disjoint union of the two standard charts to `ℙ¹` is universally
open, being an open immersion on each chart. -/
instance universallyOpen_projectiveLineChartCoverπ :
    UniversallyOpen projectiveLineChartCoverπ.{u} :=
  IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance

/-- Every point of `ℙ¹` with values in a field lifts to the disjoint union of the two standard
affine charts: its image lies in the locus where one of the two homogeneous coordinates does not
vanish. -/
theorem exists_comp_projectiveLineChartCoverπ (K : Type u) [Field K]
    (x : Spec (.of K) ⟶ projectiveSpaceAtUniverse.{u} 1) :
    ∃ y, y ≫ projectiveLineChartCoverπ.{u} = x := by
  have hx : x (IsLocalRing.closedPoint K) ∈ (⨆ i : Fin (1 + 1), Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i)) := by
    rw [Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top]
    trivial
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have : Set.range x ⊆ Set.range (projectiveLineCoordChartι.{u} b) := by
    rw [← Scheme.Hom.coe_opensRange (projectiveLineCoordChartι.{u} b),
      opensRange_projectiveLineCoordChartι]
    rintro _ ⟨z, rfl⟩
    obtain rfl := Subsingleton.elim z (IsLocalRing.closedPoint K)
    exact hb
  refine ⟨IsOpenImmersion.lift _ x this ≫ Sigma.ι projectiveLineCoordChart.{u} b, ?_⟩
  rw [projectiveLineChartCoverπ, Category.assoc, Sigma.ι_desc, IsOpenImmersion.lift_fac]

/-- The morphism from the disjoint union of the two standard charts to `ℙ¹` is surjective. -/
instance surjective_projectiveLineChartCoverπ : Surjective projectiveLineChartCoverπ.{u} :=
  surjective_of_exists_comp_eq _ exists_comp_projectiveLineChartCoverπ

end ProjectiveLineCharts

section ProjectiveLinePow

/-- The covering morphism of `(ℙ¹)^∞` attached to the disjoint union of the two standard affine
charts of `ℙ¹`: the `ULift ℕ`-fold product of that affine scheme, mapping to `(ℙ¹)^∞` by the
union of the chart inclusions in every component. -/
def projectiveLinePowFlatCover :
    yoneda.obj (affinePow (ULift.{u} ℕ) projectiveLineChartCover.{u}) ⟶ projectiveLinePow.{u} :=
  powCover projectiveLineChartCoverπ.{u}

/-- The covering morphism of `(ℙ¹)^∞` by an affine scheme is surjective. -/
theorem surjective_presheaf_projectiveLinePowFlatCover :
    MorphismProperty.presheaf (C := Scheme.{u}) @Surjective projectiveLinePowFlatCover.{u} :=
  surjective_presheaf_powCover _ exists_comp_projectiveLineChartCoverπ

/-- The covering morphism of `(ℙ¹)^∞` by an affine scheme is flat. -/
theorem flat_presheaf_projectiveLinePowFlatCover :
    MorphismProperty.presheaf (C := Scheme.{u}) @Flat projectiveLinePowFlatCover.{u} :=
  flat_presheaf_powCover _

/-- The covering morphism of `(ℙ¹)^∞` by an affine scheme is universally open. -/
theorem universallyOpen_presheaf_projectiveLinePowFlatCover :
    MorphismProperty.presheaf (C := Scheme.{u}) @UniversallyOpen projectiveLinePowFlatCover.{u} :=
  universallyOpen_presheaf_powCover _ exists_comp_projectiveLineChartCoverπ

/-- The covering morphism of `(ℙ¹)^∞` by an affine scheme is quasi-compact. -/
theorem quasiCompact_presheaf_projectiveLinePowFlatCover :
    MorphismProperty.presheaf (C := Scheme.{u}) @QuasiCompact projectiveLinePowFlatCover.{u} :=
  quasiCompact_presheaf_powCover _

/-- `(ℙ¹)^∞` receives from an affine scheme a morphism of presheaves which is representable,
surjective, flat, universally open and quasi-compact. -/
theorem exists_surjective_flat_universallyOpen_quasiCompact_projectiveLinePow :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (f : yoneda.obj U ⟶ projectiveLinePow.{u}),
      MorphismProperty.presheaf @Surjective f ∧ MorphismProperty.presheaf @Flat f ∧
        MorphismProperty.presheaf @UniversallyOpen f ∧
          MorphismProperty.presheaf @QuasiCompact f :=
  ⟨_, inferInstance, projectiveLinePowFlatCover, surjective_presheaf_projectiveLinePowFlatCover,
    flat_presheaf_projectiveLinePowFlatCover, universallyOpen_presheaf_projectiveLinePowFlatCover,
    quasiCompact_presheaf_projectiveLinePowFlatCover⟩

end ProjectiveLinePow

end AlgebraicGeometry

end
