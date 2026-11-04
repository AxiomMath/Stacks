module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine charts of a fibre product of schemes

For morphisms of schemes `a : X ⟶ S` and `b : Y ⟶ S`, a triple of affine opens `W ⊆ S`,
`U ⊆ a⁻¹(W)`, `V ⊆ b⁻¹(W)` cuts out an affine open of the fibre product `X ×_S Y`, namely
`Spec (Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V))`, and such triples cover `X ×_S Y`. The two projections of
the fibre product restrict on this chart to `Spec` of the two structure maps
`Γ(X, U) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` and `Γ(Y, V) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)`.

## Main definitions

* `Stacks.FibreProductAffineChart.affineChart`: the chart itself, for arbitrary open immersions
  `Spec A ⟶ X`, `Spec B ⟶ Y` over a monomorphism `Spec R ⟶ S`.
* `Stacks.FibreProductAffineChart.Chart`: the index of the chart cover, a triple of affine opens
  with the two containments.
* `Stacks.FibreProductAffineChart.Chart.ι`: the open immersion of a chart into `X ×_S Y`, before
  the chart is identified with the spectrum of a tensor product.
* `Stacks.FibreProductAffineChart.Chart.specIso`: that identification.
* `Stacks.FibreProductAffineChart.openCover`: the resulting open cover of `X ×_S Y` by affine
  schemes.

## Main results

* `Stacks.FibreProductAffineChart.affineChart_fst` and
  `Stacks.FibreProductAffineChart.affineChart_snd` identify the two projections on a chart with
  `Spec` of the two algebra maps into the tensor product.
* `Stacks.FibreProductAffineChart.mem_range_pullbackMap` and
  `Stacks.FibreProductAffineChart.opensRange_pullbackMap`: the image of `X' ×_{S'} Y'` in
  `X ×_S Y` is the intersection of the preimages of the images of `X' ⟶ X` and `Y' ⟶ Y`.
* `Stacks.FibreProductAffineChart.exists_chart_mem`: the charts cover.

## Implementation notes

The chart is assembled from `AlgebraicGeometry.pullbackSpecIso`, which identifies
`Spec A ×_{Spec R} Spec B` with `Spec (A ⊗_R B)`, and `CategoryTheory.Limits.pullback.map`, which
maps that fibre product into `X ×_S Y`; `AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion`
is what makes the second an open immersion. Both halves are stated for arbitrary morphisms
`Spec A ⟶ X`, `Spec B ⟶ Y`, `Spec R ⟶ S` rather than for `IsAffineOpen.fromSpec`, so that no
concrete comparison isomorphism has to be unfolded while they are being used.

The cover is produced as a `CategoryTheory.Precoverage.ZeroHypercover` through
`AlgebraicGeometry.Scheme.Cover.mkOfCovers`, whose surjectivity field is a proposition; the
charts are the fibre products `Spec Γ(X, U) ×_{Spec Γ(S, W)} Spec Γ(Y, V)` themselves, with
`Chart.specIso` recording separately that each is the spectrum of a tensor product. Writing the
tensor product into the type of the cover would force the two induced algebra structures into the
type as well.

That the charts cover is proved by lifting the open subscheme
`fst⁻¹(U) ∩ snd⁻¹(V)` of `X ×_S Y` into the chart along the universal property of open
immersions, which avoids computing the underlying set of a fibre product of schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry CommRingCat RingHomClass TopologicalSpace

namespace Stacks.FibreProductAffineChart

universe u

variable {X Y S : Scheme.{u}}

/-! ### The image of a map of fibre products -/

section Range

variable {X' Y' S' : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} {a' : X' ⟶ S'} {b' : Y' ⟶ S'}
  {u : X' ⟶ X} {v : Y' ⟶ Y} {w : S' ⟶ S} [IsOpenImmersion u] [IsOpenImmersion v] [Mono w]

/-- A point of `X ×_S Y` whose two projections lie in the images of the open immersions
`u : X' ⟶ X` and `v : Y' ⟶ Y` lies in the image of `X' ×_{S'} Y'`, provided the two squares
commute over a monomorphism `w : S' ⟶ S`. -/
theorem mem_range_pullbackMap (hu : a' ≫ w = u ≫ a) (hv : b' ≫ w = v ≫ b)
    (z : ↥(pullback a b)) (hz₁ : (pullback.fst a b).base z ∈ u.opensRange)
    (hz₂ : (pullback.snd a b).base z ∈ v.opensRange) :
    z ∈ Set.range (pullback.map a' b' a b u v w hu hv) := by
  set Z : (pullback a b).Opens :=
    pullback.fst a b ⁻¹ᵁ u.opensRange ⊓ pullback.snd a b ⁻¹ᵁ v.opensRange with hZ
  have hzZ : z ∈ Z := ⟨hz₁, hz₂⟩
  have h₁ : Set.range (Z.ι ≫ pullback.fst a b) ⊆ Set.range u := by
    rintro _ ⟨p, rfl⟩
    exact p.2.1
  have h₂ : Set.range (Z.ι ≫ pullback.snd a b) ⊆ Set.range v := by
    rintro _ ⟨p, rfl⟩
    exact p.2.2
  have e₁ : IsOpenImmersion.lift u (Z.ι ≫ pullback.fst a b) h₁ ≫ u =
      Z.ι ≫ pullback.fst a b := IsOpenImmersion.lift_fac _ _ _
  have e₂ : IsOpenImmersion.lift v (Z.ι ≫ pullback.snd a b) h₂ ≫ v =
      Z.ι ≫ pullback.snd a b := IsOpenImmersion.lift_fac _ _ _
  have hl : IsOpenImmersion.lift u (Z.ι ≫ pullback.fst a b) h₁ ≫ a' =
      IsOpenImmersion.lift v (Z.ι ≫ pullback.snd a b) h₂ ≫ b' := by
    rw [← cancel_mono w, Category.assoc, Category.assoc, hu, hv, ← Category.assoc,
      ← Category.assoc, e₁, e₂, Category.assoc, Category.assoc, pullback.condition]
  have hk : pullback.lift _ _ hl ≫ pullback.map a' b' a b u v w hu hv = Z.ι := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, e₁]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, e₂]
  obtain ⟨p, hp⟩ : ∃ p : ↥Z.toScheme, Z.ι p = z := ⟨⟨z, hzZ⟩, rfl⟩
  refine ⟨(pullback.lift _ _ hl) p, ?_⟩
  rw [← Scheme.Hom.comp_apply, hk]
  exact hp

/-- The image of `X' ×_{S'} Y'` in `X ×_S Y` is the intersection of the preimages of the images
of the open immersions `u : X' ⟶ X` and `v : Y' ⟶ Y` under the two projections. -/
theorem opensRange_pullbackMap (hu : a' ≫ w = u ≫ a) (hv : b' ≫ w = v ≫ b) :
    (pullback.map a' b' a b u v w hu hv).opensRange =
      pullback.fst a b ⁻¹ᵁ u.opensRange ⊓ pullback.snd a b ⁻¹ᵁ v.opensRange := by
  refine le_antisymm ?_ fun z hz => mem_range_pullbackMap hu hv z hz.1 hz.2
  rintro _ ⟨p, rfl⟩
  refine ⟨⟨pullback.fst a' b' p, ?_⟩, ⟨pullback.snd a' b' p, ?_⟩⟩
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  · rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd]

end Range

/-! ### The affine chart -/

section AffineChart

variable (a : X ⟶ S) (b : Y ⟶ S) (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (u : Spec (.of A) ⟶ X) (v : Spec (.of B) ⟶ Y)
  (w : Spec (.of R) ⟶ S)
  (hu : Spec.map (ofHom (algebraMap R A)) ≫ w = u ≫ a)
  (hv : Spec.map (ofHom (algebraMap R B)) ≫ w = v ≫ b)

/-- An affine chart of the fibre product `X ×_S Y`: given open immersions `Spec A ⟶ X` and
`Spec B ⟶ Y` lying over a monomorphism `Spec R ⟶ S` along the two structure maps, this is the
induced open immersion `Spec (A ⊗_R B) ⟶ X ×_S Y`. -/
def affineChart : Spec (.of (A ⊗[R] B)) ⟶ pullback a b :=
  (pullbackSpecIso R A B).inv ≫ pullback.map _ _ a b u v w hu hv

/-- An affine chart is `AlgebraicGeometry.pullbackSpecIso` followed by the canonical map of
fibre products. -/
theorem affineChart_eq : affineChart a b R A B u v w hu hv =
    (pullbackSpecIso R A B).inv ≫ pullback.map _ _ a b u v w hu hv := rfl

/-- An affine chart `Spec (A ⊗_R B) ⟶ X ×_S Y` is an open immersion. -/
instance isOpenImmersion_affineChart [IsOpenImmersion u] [IsOpenImmersion v] [Mono w] :
    IsOpenImmersion (affineChart a b R A B u v w hu hv) :=
  show IsOpenImmersion
    ((pullbackSpecIso R A B).inv ≫ pullback.map _ _ a b u v w hu hv) from inferInstance

/-- On an affine chart the first projection of `X ×_S Y` is `Spec` of the algebra map
`A ⟶ A ⊗_R B`, followed by the open immersion `Spec A ⟶ X`. -/
@[reassoc]
theorem affineChart_fst : affineChart a b R A B u v w hu hv ≫ pullback.fst a b =
    Spec.map (ofHom (algebraMap A (A ⊗[R] B))) ≫ u := by
  rw [affineChart_eq, Category.assoc, pullback.lift_fst, pullbackSpecIso_inv_fst'_assoc]

/-- On an affine chart the second projection of `X ×_S Y` is `Spec` of the algebra map
`B ⟶ A ⊗_R B`, followed by the open immersion `Spec B ⟶ Y`. -/
@[reassoc]
theorem affineChart_snd : affineChart a b R A B u v w hu hv ≫ pullback.snd a b =
    Spec.map (ofHom (R := B) (S := A ⊗[R] B) (toRingHom Algebra.TensorProduct.includeRight))
      ≫ v := by
  rw [affineChart_eq, Category.assoc, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]

/-- The image of an affine chart is the intersection of the preimages of the images of
`Spec A ⟶ X` and `Spec B ⟶ Y` under the two projections. -/
theorem opensRange_affineChart [IsOpenImmersion u] [IsOpenImmersion v] [Mono w] :
    (affineChart a b R A B u v w hu hv).opensRange =
      pullback.fst a b ⁻¹ᵁ u.opensRange ⊓ pullback.snd a b ⁻¹ᵁ v.opensRange := by
  rw [← opensRange_pullbackMap hu hv]
  refine TopologicalSpace.Opens.ext (Set.Subset.antisymm ?_ ?_) <;> rintro _ ⟨p, rfl⟩
  · exact ⟨(pullbackSpecIso R A B).inv p, by rw [affineChart_eq, Scheme.Hom.comp_apply]⟩
  · refine ⟨(pullbackSpecIso R A B).hom p, ?_⟩
    rw [affineChart_eq, ← Scheme.Hom.comp_apply, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]

end AffineChart

/-! ### The chart cover -/

/-- The index of the affine chart cover of a fibre product `X ×_S Y`: an affine open `W` of `S`
together with affine opens `U` of `X` and `V` of `Y` mapping into `W`. -/
structure Chart (a : X ⟶ S) (b : Y ⟶ S) where
  /-- The open of the base. -/
  base : S.Opens
  /-- The open of the first factor. -/
  left : X.Opens
  /-- The open of the second factor. -/
  right : Y.Opens
  /-- The open of the base is affine. -/
  isAffineOpen_base : IsAffineOpen base
  /-- The open of the first factor is affine. -/
  isAffineOpen_left : IsAffineOpen left
  /-- The open of the second factor is affine. -/
  isAffineOpen_right : IsAffineOpen right
  /-- The open of the first factor maps into the open of the base. -/
  le_left : left ≤ a ⁻¹ᵁ base
  /-- The open of the second factor maps into the open of the base. -/
  le_right : right ≤ b ⁻¹ᵁ base

namespace Chart

variable {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

/-- The structure map `Γ(S, W) ⟶ Γ(X, U)` of a chart. -/
abbrev leftHom : Γ(S, c.base) ⟶ Γ(X, c.left) := a.appLE c.base c.left c.le_left

/-- The structure map `Γ(S, W) ⟶ Γ(Y, V)` of a chart. -/
abbrev rightHom : Γ(S, c.base) ⟶ Γ(Y, c.right) := b.appLE c.base c.right c.le_right

/-- The open immersion `Spec Γ(X, U) ⟶ X` of a chart's first factor. -/
abbrev fromSpecLeft : Spec Γ(X, c.left) ⟶ X := c.isAffineOpen_left.fromSpec

/-- The open immersion `Spec Γ(Y, V) ⟶ Y` of a chart's second factor. -/
abbrev fromSpecRight : Spec Γ(Y, c.right) ⟶ Y := c.isAffineOpen_right.fromSpec

/-- The open immersion `Spec Γ(S, W) ⟶ S` of a chart's base. -/
abbrev fromSpecBase : Spec Γ(S, c.base) ⟶ S := c.isAffineOpen_base.fromSpec

/-- The first structure map of a chart lies over the base: `Spec Γ(X, U) ⟶ Spec Γ(S, W) ⟶ S`
is `Spec Γ(X, U) ⟶ X ⟶ S`. -/
theorem specMap_leftHom_fromSpec :
    Spec.map c.leftHom ≫ c.fromSpecBase = c.fromSpecLeft ≫ a :=
  IsAffineOpen.SpecMap_appLE_fromSpec a c.isAffineOpen_base c.isAffineOpen_left c.le_left

/-- The second structure map of a chart lies over the base: `Spec Γ(Y, V) ⟶ Spec Γ(S, W) ⟶ S`
is `Spec Γ(Y, V) ⟶ Y ⟶ S`. -/
theorem specMap_rightHom_fromSpec :
    Spec.map c.rightHom ≫ c.fromSpecBase = c.fromSpecRight ≫ b :=
  IsAffineOpen.SpecMap_appLE_fromSpec b c.isAffineOpen_base c.isAffineOpen_right c.le_right

/-- The open immersion of a chart `Spec Γ(X, U) ×_{Spec Γ(S, W)} Spec Γ(Y, V)` into the fibre
product `X ×_S Y`. -/
def ι : pullback (Spec.map c.leftHom) (Spec.map c.rightHom) ⟶ pullback a b :=
  pullback.map _ _ a b c.fromSpecLeft c.fromSpecRight c.fromSpecBase
    c.specMap_leftHom_fromSpec c.specMap_rightHom_fromSpec

/-- The open immersion of a chart is the canonical map of fibre products. -/
theorem ι_eq : c.ι = pullback.map _ _ a b c.fromSpecLeft c.fromSpecRight c.fromSpecBase
    c.specMap_leftHom_fromSpec c.specMap_rightHom_fromSpec := rfl

/-- The map of a chart into the fibre product `X ×_S Y` is an open immersion. -/
instance isOpenImmersion_ι : IsOpenImmersion c.ι :=
  Scheme.pullback_map_isOpenImmersion (Spec.map c.leftHom) (Spec.map c.rightHom) a b
    c.fromSpecLeft c.fromSpecRight c.fromSpecBase
    c.specMap_leftHom_fromSpec c.specMap_rightHom_fromSpec

/-- On a chart the first projection of `X ×_S Y` is the first projection of the chart followed by
the open immersion `Spec Γ(X, U) ⟶ X`. -/
@[reassoc (attr := simp)]
theorem ι_fst : c.ι ≫ pullback.fst a b =
    pullback.fst (Spec.map c.leftHom) (Spec.map c.rightHom) ≫ c.fromSpecLeft :=
  pullback.lift_fst _ _ _

/-- On a chart the second projection of `X ×_S Y` is the second projection of the chart followed
by the open immersion `Spec Γ(Y, V) ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem ι_snd : c.ι ≫ pullback.snd a b =
    pullback.snd (Spec.map c.leftHom) (Spec.map c.rightHom) ≫ c.fromSpecRight :=
  pullback.lift_snd _ _ _

/-- The image of a chart is the intersection of the preimages of its two factors under the two
projections of `X ×_S Y`. -/
theorem opensRange_ι :
    c.ι.opensRange = pullback.fst a b ⁻¹ᵁ c.left ⊓ pullback.snd a b ⁻¹ᵁ c.right := by
  have h := opensRange_pullbackMap c.specMap_leftHom_fromSpec c.specMap_rightHom_fromSpec
  rw [show c.fromSpecLeft.opensRange = c.left from IsAffineOpen.opensRange_fromSpec _,
    show c.fromSpecRight.opensRange = c.right from IsAffineOpen.opensRange_fromSpec _] at h
  exact h

/-- A point of `X ×_S Y` whose two projections lie in the two factors of a chart lies in that
chart. -/
theorem mem_range_ι (z : ↥(pullback a b)) (h₁ : (pullback.fst a b).base z ∈ c.left)
    (h₂ : (pullback.snd a b).base z ∈ c.right) : z ∈ Set.range c.ι :=
  by rw [← Scheme.Hom.coe_opensRange, c.opensRange_ι]; exact ⟨h₁, h₂⟩

/-- A chart is the spectrum of the tensor product `Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)`, for any algebra
structures realizing the two structure maps of the chart. -/
def specIso [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
    (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
    (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom) :
    pullback (Spec.map c.leftHom) (Spec.map c.rightHom) ≅
      Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))) :=
  pullback.congrHom (congrArg Spec.map hl.symm) (congrArg Spec.map hr.symm) ≪≫
    pullbackSpecIso _ _ _

section SpecIso

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)

/-- Read backwards, `Stacks.FibreProductAffineChart.Chart.specIso` sends the first projection of
the chart to `Spec` of the algebra map `Γ(X, U) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)`. -/
@[reassoc]
theorem specIso_inv_fst : (c.specIso hl hr).inv ≫
    pullback.fst (Spec.map c.leftHom) (Spec.map c.rightHom) =
      Spec.map (ofHom (algebraMap Γ(X, c.left) (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))) := by
  show ((pullbackSpecIso _ _ _).inv ≫ (pullback.congrHom _ _).inv) ≫ _ = _
  rw [Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id,
    pullbackSpecIso_inv_fst']

/-- Read backwards, `Stacks.FibreProductAffineChart.Chart.specIso` sends the second projection of
the chart to `Spec` of the algebra map `Γ(Y, V) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)`. -/
@[reassoc]
theorem specIso_inv_snd : (c.specIso hl hr).inv ≫
    pullback.snd (Spec.map c.leftHom) (Spec.map c.rightHom) =
      Spec.map (ofHom (R := Γ(Y, c.right)) (S := Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        (toRingHom Algebra.TensorProduct.includeRight)) := by
  show ((pullbackSpecIso _ _ _).inv ≫ (pullback.congrHom _ _).inv) ≫ _ = _
  rw [Category.assoc, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id,
    pullbackSpecIso_inv_snd]

/-- A chart, read through `Stacks.FibreProductAffineChart.Chart.specIso` as the spectrum of a
tensor product, is the affine chart `Stacks.FibreProductAffineChart.affineChart`. -/
theorem specIso_inv_ι : (c.specIso hl hr).inv ≫ c.ι =
    affineChart a b Γ(S, c.base) Γ(X, c.left) Γ(Y, c.right)
      c.fromSpecLeft c.fromSpecRight c.fromSpecBase
      (by rw [hl]; exact c.specMap_leftHom_fromSpec)
      (by rw [hr]; exact c.specMap_rightHom_fromSpec) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, ι_fst, affineChart_fst, specIso_inv_fst_assoc]
  · rw [Category.assoc, ι_snd, affineChart_snd, specIso_inv_snd_assoc]

end SpecIso

end Chart

/-- Every point of a fibre product `X ×_S Y` lies in some affine chart. -/
theorem exists_chart_mem (a : X ⟶ S) (b : Y ⟶ S) (z : ↥(pullback a b)) :
    ∃ c : Chart a b, z ∈ Set.range c.ι := by
  obtain ⟨W, hW, hsW, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S)
      (U := ⊤) (x := a.base ((pullback.fst a b).base z)) trivial
  obtain ⟨U, hU, hxU, hUW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)
      (U := a ⁻¹ᵁ W) (x := (pullback.fst a b).base z) hsW
  have hb : b.base ((pullback.snd a b).base z) = a.base ((pullback.fst a b).base z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition]
  obtain ⟨V, hV, hyV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)
      (U := b ⁻¹ᵁ W) (x := (pullback.snd a b).base z)
      (by rw [Scheme.Hom.mem_preimage, hb]; exact hsW)
  exact ⟨⟨W, U, V, hW, hU, hV, hUW, hVW⟩, Chart.mem_range_ι _ z hxU hyV⟩

/-- The affine chart cover of a fibre product `X ×_S Y`: the charts are the fibre products
`Spec Γ(X, U) ×_{Spec Γ(S, W)} Spec Γ(Y, V)`, which are affine, and
`Stacks.FibreProductAffineChart.Chart.specIso` identifies each with the spectrum of the tensor
product `Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)`. -/
def openCover (a : X ⟶ S) (b : Y ⟶ S) : (pullback a b).OpenCover :=
  Scheme.Cover.mkOfCovers (Chart a b)
    (fun c => pullback (Spec.map c.leftHom) (Spec.map c.rightHom)) (fun c => c.ι)
    fun z => by obtain ⟨c, p, hp⟩ := exists_chart_mem a b z; exact ⟨c, p, hp⟩

/-- Each member of the affine chart cover of `X ×_S Y` is an affine scheme. -/
instance isAffine_openCover_X (a : X ⟶ S) (b : Y ⟶ S) (c : (openCover a b).I₀) :
    IsAffine ((openCover a b).X c) :=
  inferInstanceAs (IsAffine (pullback (Spec.map (Chart.leftHom c)) (Spec.map (Chart.rightHom c))))

end Stacks.FibreProductAffineChart

end
