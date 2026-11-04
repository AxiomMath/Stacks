module

public import StacksFrontier.AlgebraicGeometry.Morphisms.JacobsonPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.Deformation.Artin.Infinitesimal.SiteContainment
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheory
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityOpenRestriction

/-!
# The geometric reduction at the start of the proof of Stacks 07YU

[Stacks, Tag 07YU] begins: *we may first shrink `U` to an affine scheme such that `u₀` is a
closed point and such that `U → S` maps into an affine open `Spec Λ`.* This file carries that
reduction out. Given an object `x` of a category fibred in groupoids over the big fppf site of
`S`, lying over a scheme `U` locally of finite type over `S`, and a finite type point `u₀` of
`U`, it produces an affine chart `Spec Λ ⊆ S`, a `Deformation.Artin.ChartedObject` for that
chart whose ring is the ring of an affine open `Spec A ⊆ U` containing `u₀` as a closed point,
and an arrow from it to `x` lying over the open immersion `Spec A ⟶ U`.

## Main definitions

* `Deformation.Artin.chartOfAffineOpen` — the affine chart `Spec Γ(S, Λ) ⊆ S` of an affine open
  `Λ` of `S`.
* `Deformation.Artin.restrictedSiteAlgebra`, `Deformation.Artin.restrictedAffineObject`,
  `Deformation.Artin.restrictedChartedObject` — the restriction of `x` to an affine open of its
  base, as an `S`-algebra in the site, as an object over such an algebra, and as a charted
  object for a chart the structure morphism factors through.
* `Deformation.Artin.ChartedData` — the output of the reduction: the chart, the ring `A` of the
  affine open with its finite type `Λ`-algebra structure, the open immersion `Spec A ⟶ U`, and
  the factorization of `Spec A ⟶ S` through the chart.

## Main results

* `Deformation.Artin.exists_affineOpen_isClosed_mapsTo` — the topological input: a finite type
  point has an affine open neighbourhood in which it is closed and which maps into a prescribed
  open of the base.
* `Deformation.Artin.exists_chartedData` — the reduction itself, together with the point of
  `Spec A` above `u₀` and its closedness.
* `Deformation.Artin.exists_restrictedLift` — the cartesian lift of `x` to `Spec A`, with the
  identification of the morphism of schemes its structure arrow lies over.
* `Deformation.Artin.isFiniteTypePoint_of_isOpenImmersion` — a point of an open subscheme is a
  finite type point of it as soon as its image is a finite type point, which is what lets the
  conclusion of [Stacks, Tag 07YN] be read back on `U`.
* `Deformation.Artin.contains_spec_squareZeroRing_differentials` — the square-zero extension by
  the differentials lies in the site, which is the side condition every statement about the
  canonical element of the tangent functor carries.

## Implementation notes

The ring of the charted object is `Γ(U, W)` for an affine open `W`, and the two morphisms of
schemes it comes with are `AlgebraicGeometry.IsAffineOpen.fromSpec` for `W` and for the chart.
The `Λ`-algebra structure is the one `AlgebraicGeometry.Scheme.Hom.appLE` gives, which is also
what makes `A` of finite type over `Λ` — `AlgebraicGeometry.Scheme.Hom.finiteType_appLE` — and
whose compatibility with the two `fromSpec`s is
`AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`. No ring map is read off a morphism of
schemes and no `Algebra` instance is transported, so the structure attached to `A` is the one
its finite type is stated about.

`Spec A` lies in the site because an open subscheme of a scheme in the site is no larger than
it (`AlgebraicGeometry.Scheme.size_coe_opens_le`) and the size of a scheme is an isomorphism
invariant.

The containment of `Spec A[Ω_{A/Λ}]` in the site is not an extra hypothesis: `Ω_{A/Λ}` is a
finite `A`-module because `A` is of finite type over `Λ`, a finite module is no larger than
`max ℵ₀ #A`, and `Deformation.Artin.contains_spec_squareZeroRing_of_mk_le` turns that bound into
membership in a site already containing `Spec A`.

Closedness of the point above `u₀`, and the converse direction of the correspondence of finite
type points, are both the statement that a continuous injection reflects closed points
(`preimage_closedPoints_subset`), applied to the map from `Spec A` to the open `W` through which
`Spec A ⟶ U` factors.

The base of `x` is written `B.inclusion.obj (p.obj x).left` throughout rather than through an
equality `(p ⋙ Over.post B.inclusion).obj x = U` for a named `U`: the morphism of the site
underlying the restriction has to be produced by `CategoryTheory.Functor.preimage` on the
*site's* object, and a transport along such an equality would put an `eqToHom` into every one of
these definitions.

## References

* [Stacks Project, Tag 07YU](https://stacks.math.columbia.edu/tag/07YU)
* [Stacks Project, Tag 07YN](https://stacks.math.columbia.edu/tag/07YN)
* [Stacks Project, Tag 02J2](https://stacks.math.columbia.edu/tag/02J2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

/-! ### A closed affine neighbourhood of a finite type point inside a prescribed open -/

/-- A point whose image under an open embedding into `T` is closed in an open `V` containing the
range of the embedding is closed. -/
private theorem isClosed_singleton_of_isOpenEmbedding {Y T : Type*} [TopologicalSpace Y]
    [TopologicalSpace T] {g : Y → T} (hg : Topology.IsOpenEmbedding g) {V : Set T}
    (hV : ∀ y, g y ∈ V) (y : Y) (h : IsClosed ({(⟨g y, hV y⟩ : V)} : Set V)) :
    IsClosed ({y} : Set Y) :=
  mem_closedPoints_iff.mp (preimage_closedPoints_subset (f := fun s => (⟨g s, hV s⟩ : V))
    (fun _ _ hab => hg.injective (congrArg Subtype.val hab))
    (hg.continuous.subtype_mk _) (mem_closedPoints_iff.mpr h))

/-- The map `Spec Γ(T, W) ⟶ T` of an affine open `W` lands in `W`. -/
private theorem fromSpec_base_mem {T : Scheme.{u}} {W : T.Opens} (hW : IsAffineOpen W)
    (t : Spec Γ(T, W)) : hW.fromSpec.base t ∈ W := by
  have ht : hW.fromSpec.base t ∈ Set.range hW.fromSpec.base := ⟨t, rfl⟩
  rwa [hW.range_fromSpec] at ht

/-- A finite type point `t₀` of a scheme `T` over `S`, whose image lies in a prescribed open
`Λ` of `S`, has an affine open neighbourhood in `T` in which it is closed and which still maps
into `Λ`. -/
public theorem exists_affineOpen_isClosed_mapsTo {T S : Scheme.{u}} (f : T ⟶ S) {t₀ : T}
    (ht₀ : IsFiniteTypePoint t₀) {Λ : S.Opens} (hΛ : f t₀ ∈ Λ) :
    ∃ (V : T.Opens) (ht₀V : t₀ ∈ V),
      IsAffineOpen V ∧ IsClosed ({(⟨t₀, ht₀V⟩ : V)} : Set V) ∧ V ≤ f ⁻¹ᵁ Λ := by
  have hmem : t₀ ∈ T.finiteTypePoints := ht₀
  rw [T.finiteTypePoints_eq_iUnion_affineOpens] at hmem
  obtain ⟨W, x, hxc, rfl⟩ := Set.mem_iUnion.mp hmem
  have hxO : (x : T) ∈ (W.1 ⊓ f ⁻¹ᵁ Λ : T.Opens) := ⟨x.2, hΛ⟩
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVsub⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hxO (W.1 ⊓ f ⁻¹ᵁ Λ).isOpen
  have hVW : V ≤ W.1 := fun y hy => (hVsub hy).1
  have hVΛ : V ≤ f ⁻¹ᵁ Λ := fun y hy => (hVsub hy).2
  refine ⟨V, hxV, hVaff, ?_, hVΛ⟩
  exact mem_closedPoints_iff.mp (preimage_closedPoints_subset
    (Set.inclusion_injective hVW) (continuous_inclusion hVW) hxc)

/-! ### Finite type points of an open subscheme -/

/-- **An open immersion reflects finite type points.** A point of the source whose image is a
finite type point is a finite type point: the image is closed in some open of the target, and
the preimage of that open is an open of the source in which the point is closed. -/
public theorem isFiniteTypePoint_of_isOpenImmersion {T T' : Scheme.{u}} (f : T' ⟶ T)
    [IsOpenImmersion f] (t : T') (ht : IsFiniteTypePoint (f.base t)) : IsFiniteTypePoint t := by
  have hmem : f.base t ∈ T.finiteTypePoints := ht
  rw [T.finiteTypePoints_eq_iUnion_opens] at hmem
  obtain ⟨V, y, hyc, hyeq⟩ := Set.mem_iUnion.mp hmem
  have htV : t ∈ f ⁻¹ᵁ V := by
    show f.base t ∈ V
    rw [← hyeq]
    exact y.2
  show t ∈ T'.finiteTypePoints
  rw [T'.finiteTypePoints_eq_iUnion_opens]
  refine Set.mem_iUnion.mpr ⟨f ⁻¹ᵁ V, ⟨t, htV⟩, ?_, rfl⟩
  refine isClosed_singleton_of_isOpenEmbedding (g := fun s : (f ⁻¹ᵁ V : T'.Opens) => f.base s.1)
    (f.isOpenEmbedding.comp (f ⁻¹ᵁ V).isOpen.isOpenEmbedding_subtypeVal) (fun s => s.2)
    ⟨t, htV⟩ ?_
  rw [show (⟨f.base t, htV⟩ : V) = y from Subtype.ext hyeq.symm]
  exact mem_closedPoints_iff.mp hyc

/-! ### A finite module is no larger than its ring -/

/-- The cardinality of a finite power of a ring is bounded by the ring's own size bound. -/
private theorem mk_fun_le_max (A : Type u) (n : ℕ) :
    Cardinal.mk (Fin n → A) ≤ max Cardinal.aleph0 (Cardinal.mk A) := by
  induction n with
  | zero =>
    have h : Cardinal.mk (Fin 0 → A) = 1 := Cardinal.mk_eq_one _
    rw [h]
    exact le_trans Cardinal.one_le_aleph0 (le_max_left _ _)
  | succ n ih =>
    rw [Cardinal.mk_congr (Fin.succFunEquiv A n), Cardinal.mk_prod, Cardinal.lift_id,
      Cardinal.lift_id]
    refine le_trans (Cardinal.mul_le_max _ _) ?_
    exact max_le (max_le ih (le_max_right _ _)) (le_max_left _ _)

/-- A finite module over a commutative ring `A` has cardinality at most `max ℵ₀ #A`: it is a
quotient of a finite power of `A`. -/
public theorem mk_le_max_of_module_finite (A : Type u) [CommRing A] (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Cardinal.mk M ≤ max Cardinal.aleph0 (Cardinal.mk A) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  exact le_trans (Cardinal.mk_le_of_surjective hf) (mk_fun_le_max A n)

/-- **The square-zero extension by the differentials lies in the site.** For `A` of finite type
over `Λ` whose spectrum lies in a big fppf site, the spectrum of `A[Ω_{A/Λ}]` lies there too:
the module of differentials is a finite `A`-module. -/
public theorem contains_spec_squareZeroRing_differentials (B : BigFppfSite.{u}) {Λ A : Type u}
    [CommRing Λ] [CommRing A] [Algebra Λ A] [Algebra.FiniteType Λ A]
    (hA : B.Contains (Spec (CommRingCat.of A))) :
    B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))) := by
  have : Algebra.EssFiniteType Λ A := Algebra.EssFiniteType.of_finiteType Λ A
  refine contains_spec_squareZeroRing_of_mk_le B hA A (differentialsModule Λ A)
    (le_max_right _ _) ?_
  exact mk_le_max_of_module_finite A (Ω[A⁄Λ])

/-! ### The affine chart attached to an affine open of the base -/

/-- The affine chart `Spec Γ(S, Λ) ⊆ S` of an affine open `Λ` of `S`. -/
public def chartOfAffineOpen {S : Scheme.{u}} {Λ : S.Opens} (hΛ : IsAffineOpen Λ) :
    AffineChart S where
  ring := Γ(S, Λ)
  immersion := hΛ.fromSpec
  isOpenImmersion := hΛ.isOpenImmersion_fromSpec

/-! ### The scheme-theoretic half of the reduction -/

/-- **Shrinking to an affine open in a chart.** A finite type point `u₀` of a scheme `T`
locally of finite type over `S` lies in an affine open `W` of `T` whose image is contained in
an affine open `Λ` of `S`, and the point of `Spec Γ(T, W)` above `u₀` is closed. -/
public theorem exists_affineOpen_chart_data {T S : Scheme.{u}} (f : T ⟶ S)
    {u₀ : T} (hu₀ : IsFiniteTypePoint u₀) :
    ∃ (Λ : S.Opens) (_hΛ : IsAffineOpen Λ) (W : T.Opens) (hW : IsAffineOpen W),
      W ≤ f ⁻¹ᵁ Λ ∧ ∃ w₀ : Spec Γ(T, W),
        hW.fromSpec.base w₀ = u₀ ∧ IsClosed ({w₀} : Set (Spec Γ(T, W))) := by
  obtain ⟨Λ, hΛ, hΛmem, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := f.base u₀) (U := ⊤) (Set.mem_univ _)
  obtain ⟨W, hu₀W, hW, hclosed, hWΛ⟩ := exists_affineOpen_isClosed_mapsTo f hu₀ hΛmem
  obtain ⟨w₀, hw₀⟩ : u₀ ∈ Set.range hW.fromSpec.base := by
    rw [hW.range_fromSpec]; exact hu₀W
  refine ⟨Λ, hΛ, W, hW, hWΛ, w₀, hw₀, ?_⟩
  exact isClosed_singleton_of_isOpenEmbedding hW.fromSpec.isOpenEmbedding
    (fromSpec_base_mem hW) w₀ (by subst hw₀; exact hclosed)

/-! ### The charted object attached to an affine open of the base -/

section Charted

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (jA : Spec (CommRingCat.of A) ⟶ B.inclusion.obj (p.obj x).left)

/-- The `S`-algebra of an affine open of the base of an object `x` of the fibred category. -/
public def restrictedSiteAlgebra : SiteAlgebra B S hS where
  carrier := A
  mem := hA
  toBase := B.inclusion.preimage (X := B.obj hA) jA ≫ (p.obj x).hom

/-- The structure morphism of `Deformation.Artin.restrictedSiteAlgebra`. -/
public theorem toScheme_restrictedSiteAlgebra :
    (restrictedSiteAlgebra B S hS p x hA jA).toScheme =
      jA ≫ B.inclusion.map (p.obj x).hom := by
  show B.inclusion.map (B.inclusion.preimage (X := B.obj hA) jA ≫ (p.obj x).hom) = _
  rw [B.inclusion.map_comp, B.inclusion.map_preimage]

variable (hmaps : MapsIntoAffineOpen S (jA ≫ B.inclusion.map (p.obj x).hom))

/-- The object of the fibred category over the affine open, as an object over an `S`-algebra
in the sense of clause (1) of Stacks 07YP. -/
public def restrictedAffineObject
    (obj : p.Fiber (restrictedSiteAlgebra B S hS p x hA jA).over) : AffineObject B S hS p where
  alg := restrictedSiteAlgebra B S hS p x hA jA
  mapsIntoAffineOpen := by
    rw [toScheme_restrictedSiteAlgebra]
    exact hmaps
  obj := obj

/-- The morphism of the site underlying the restriction to the affine open. -/
public def restrictedSiteHom : (restrictedSiteAlgebra B S hS p x hA jA).over ⟶ p.obj x :=
  Over.homMk (B.inclusion.preimage (X := B.obj hA) jA) rfl

/-- The morphism of schemes underlying `Deformation.Artin.restrictedSiteHom`. -/
public theorem toScheme_map_restrictedSiteHom :
    (BigFppfOver.toScheme B S hS).map (restrictedSiteHom B S hS p x hA jA) = jA :=
  B.inclusion.map_preimage (X := B.obj hA) (Y := (p.obj x).left) jA

/-- **The cartesian lift to the affine open.** The object `x` restricts along the open
immersion `Spec A ⟶ U`, and the restriction comes with an arrow to `x` whose underlying
morphism of schemes is that open immersion. -/
public theorem exists_restrictedLift (hp : p.IsFiberedInGroupoids) :
    ∃ (obj : p.Fiber (restrictedSiteAlgebra B S hS p x hA jA).over) (ρ : obj.1 ⟶ x),
      schemeMap (p ⋙ Over.post B.inclusion)
        (congrArg ((Over.post B.inclusion).obj) obj.2) rfl ρ = jA := by
  obtain ⟨y, φ, hφ⟩ := hp.exists_lift (restrictedSiteHom B S hS p x hA jA) x rfl
  have := hφ
  refine ⟨⟨y, IsHomLift.domain_eq p (restrictedSiteHom B S hS p x hA jA) φ⟩, φ, ?_⟩
  refine Eq.trans (schemeMap_eq_of_isHomLift B S hS p (restrictedSiteHom B S hS p x hA jA) φ
    (congrArg ((Over.post B.inclusion).obj)
      (IsHomLift.domain_eq p (restrictedSiteHom B S hS p x hA jA) φ)) rfl rfl rfl) ?_
  rw [toScheme_map_restrictedSiteHom]
  show 𝟙 _ ≫ jA ≫ 𝟙 _ = jA
  rw [Category.id_comp, Category.comp_id]

variable (c : AffineChart S) [Algebra c.ring A]
  (hfac : Spec.map (CommRingCat.ofHom (algebraMap c.ring A)) ≫ c.immersion =
    jA ≫ B.inclusion.map (p.obj x).hom)

/-- The object of the fibred category over the affine open, as a charted object for the chart
`c`. Its ring is the prescribed `A` and its `c.ring`-algebra structure the prescribed one. -/
public def restrictedChartedObject
    (obj : p.Fiber (restrictedSiteAlgebra B S hS p x hA jA).over) :
    ChartedObject B S hS p c where
  obj := restrictedAffineObject B S hS p x hA jA hmaps obj
  algebra := inferInstanceAs (Algebra c.ring A)
  factorization := hfac.trans (toScheme_restrictedSiteAlgebra B S hS p x hA jA).symm

end Charted

/-! ### The data produced by the reduction -/

section Data

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)

/-- **The output of the geometric reduction at the start of Stacks 07YU**: an affine chart
`Spec Λ ⊆ S`, a `Λ`-algebra `A` of finite type whose spectrum lies in the site, an open
immersion `Spec A ⟶ U` into the base of `x`, and the factorization of `Spec A ⟶ S` through the
chart. -/
public structure ChartedData where
  /-- The affine chart `Spec Λ ⊆ S`. -/
  chart : AffineChart S
  /-- The ring `A` of the affine open of the base. -/
  ring : Type u
  [commRing : CommRing ring]
  [algebra : Algebra chart.ring ring]
  [finiteType : Algebra.FiniteType chart.ring ring]
  /-- `Spec A` lies in the site. -/
  mem : B.Contains (Spec (CommRingCat.of ring))
  /-- The open immersion of `Spec A` into the base of `x`. -/
  immersion : Spec (CommRingCat.of ring) ⟶ B.inclusion.obj (p.obj x).left
  [isOpenImmersion : IsOpenImmersion immersion]
  /-- `Spec A ⟶ S` maps into an affine open of `S`. -/
  mapsIntoAffineOpen :
    MapsIntoAffineOpen S (immersion ≫ B.inclusion.map (p.obj x).hom)
  /-- The structure morphism of `Spec A` factors through the chart by its algebra structure. -/
  factorization :
    Spec.map (CommRingCat.ofHom (algebraMap chart.ring ring)) ≫ chart.immersion =
      immersion ≫ B.inclusion.map (p.obj x).hom

attribute [instance] ChartedData.commRing ChartedData.algebra ChartedData.finiteType
  ChartedData.isOpenImmersion

/-- **The geometric reduction at the start of the proof of Stacks 07YU.** A finite type point
`u₀` of the base of `x`, which is locally of finite type over `S`, lies in an affine open
`Spec A ⊆ U` which maps into an affine open `Spec Λ ⊆ S` and in which `u₀` is closed. -/
public theorem exists_chartedData
    (hT : B.Contains (B.inclusion.obj (p.obj x).left))
    [LocallyOfFiniteType (B.inclusion.map (p.obj x).hom)]
    (u₀ : B.inclusion.obj (p.obj x).left) (hu₀ : IsFiniteTypePoint u₀) :
    ∃ (D : ChartedData B S hS p x) (w₀ : Spec (CommRingCat.of D.ring)),
      D.immersion.base w₀ = u₀ ∧ IsClosed ({w₀} : Set (Spec (CommRingCat.of D.ring))) := by
  obtain ⟨Λ, hΛ, W, hW, hWΛ, w₀, hw₀, hw₀c⟩ :=
    exists_affineOpen_chart_data (B.inclusion.map (p.obj x).hom) hu₀
  refine ⟨{ chart := chartOfAffineOpen hΛ
            ring := Γ(B.inclusion.obj (p.obj x).left, W)
            algebra := ((B.inclusion.map (p.obj x).hom).appLE Λ W hWΛ).hom.toAlgebra
            finiteType := (B.inclusion.map (p.obj x).hom).finiteType_appLE hΛ hW hWΛ
            mem := ?_
            immersion := hW.fromSpec
            mapsIntoAffineOpen := ?_
            factorization := ?_ }, w₀, hw₀, hw₀c⟩
  · show (Spec Γ(B.inclusion.obj (p.obj x).left, W)).size < B.cutoff
    rw [← Scheme.size_congr hW.isoSpec]
    exact (Scheme.size_coe_opens_le _ W).trans_lt hT
  · exact ⟨Λ, hΛ, fun y => hWΛ (fromSpec_base_mem hW y)⟩
  · exact IsAffineOpen.SpecMap_appLE_fromSpec (B.inclusion.map (p.obj x).hom) hΛ hW hWΛ

/-! ### The residue point of a point of the chart -/

/-- The residue point of a point of a scheme over `S` lands in the chart as soon as the point
itself does. -/
public theorem range_residuePoint_subset {T : Scheme.{u}} (f : T ⟶ S) (t : T)
    {Λ : Type u} [CommRing Λ] (iΛ : Spec (CommRingCat.of Λ) ⟶ S)
    (h : f.base t ∈ Set.range iΛ.base) :
    Set.range (T.fromSpecResidueField t ≫ f).base ⊆ Set.range iΛ.base := by
  rintro _ ⟨s, rfl⟩
  have hs : (T.fromSpecResidueField t ≫ f).base s = f.base t := by
    show f.base ((T.fromSpecResidueField t).base s) = f.base t
    rw [Scheme.fromSpecResidueField_apply]
  rw [hs]
  exact h

end Data

end Deformation.Artin

end
