module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelRegularLocus
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelOrigin
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedSubschemeSmoothPullback
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.RegularGerm
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocality
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalOnSource
public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleComposition

/-!
# Étale nodal charts and the blowup of a nodal family in a singular point

Let `R` be a discrete valuation ring and `f : X ⟶ Spec R` a morphism. An *étale nodal chart of
exponent `n`* at a point `x` of `X` is the datum of [Stacks, Tag 0CDD] at `x`, normalised so that
the chosen point lies over the origin of the local model: an étale extension `R → R'` of discrete
valuation rings with uniformizer `π`, a scheme `U` with étale morphisms `U ⟶ X` and
`U ⟶ Spec R'[u, v]/(uv - πⁿ)` compatible over `Spec R`, and a point of `U` over `x` mapping to the
origin `(π, u, v)`.

The main result is the inductive step of [Stacks, Tag 0CDE]: if `f` is at-worst-nodal of relative
dimension one, `x` is a closed point and there is a chart of exponent `n ≥ 2` at `x`, then the
blowup `X'` of `X` in `x` is again at-worst-nodal of relative dimension one over `R`, and at every
point of `X'` over `x` at which `X'` is not regular there is a chart of exponent `n - 2`. Away from
`x` the blowup is an isomorphism, so regularity and charts carry over.

The proof is the source's. The chart is shrunk until the chosen point is the only point of `U`
over `x` and the only point of `U` over the origin; then the scheme-theoretic inverse images of `x`
and of the origin in `U` are both the reduced point, because inverse images along étale morphisms
of reduced closed subschemes are reduced
(`AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_of_smooth`). Blowing up commutes
with flat base change ([Stacks, Tag 0805]), so the blowup of `U` in that point is at once the base
change of `X'` and the base change of the blowup of the local model at its origin, which is
computed in [Stacks, Tag 0CDC].

## Main definitions

* `Stacks.SemistableReduction.NodalChartAt` — an étale nodal chart of exponent `n` at a point.

## Main results

* `Stacks.SemistableReduction.NodalChartAt.nonempty_transfer` — charts transfer along étale
  morphisms.
* `Stacks.SemistableReduction.NodalChartAt.exists_preimage_eq_singleton` — a chart can be shrunk
  until its chosen point is alone in its two fibres.
* `Stacks.SemistableReduction.NodalChartAt.two_le_of_not_isRegularLocalRing` — a chart at a
  point where `X` is not regular has exponent at least two.
* `Stacks.SemistableReduction.blowUp_nodalChartAt` — **the blowup step.**

## References

* [Stacks Project, Tag 0CDE](https://stacks.math.columbia.edu/tag/0CDE)
* [Stacks Project, Tag 0CDD](https://stacks.math.columbia.edu/tag/0CDD)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.SemistableReduction

open Scheme.IdealSheafData

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **An étale nodal chart of exponent `n` at a point.** For `f : X ⟶ Spec R` and `x : X`: an
étale extension `R → R'` of discrete valuation rings with an irreducible element `π`, a scheme
`U` with étale morphisms `U ⟶ X` and `U ⟶ Spec R'[u, v]/(uv - πⁿ)` compatible over `Spec R`, and
a point of `U` over `x` whose image in the local model is the origin `(π, u, v)`. -/
public structure NodalChartAt {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (x : X) (n : ℕ) where
  /-- The étale extension of the base. -/
  R' : Type u
  /-- Its ring structure. -/
  [commRing : CommRing R']
  /-- It is a domain. -/
  [isDomain : IsDomain R']
  /-- It is a discrete valuation ring. -/
  [isDiscreteValuationRing : IsDiscreteValuationRing R']
  /-- It is an `R`-algebra. -/
  [algebra : Algebra R R']
  /-- The extension is étale. -/
  [etale : Algebra.Etale R R']
  /-- The uniformizer of the local model. -/
  π : R'
  /-- It is irreducible. -/
  irreducible : Irreducible π
  /-- The étale neighbourhood. -/
  U : Scheme.{u}
  /-- The étale morphism to `X`. -/
  toX : U ⟶ X
  /-- The étale morphism to the local model. -/
  toModel : U ⟶ nodalModel R' π n
  /-- The morphism to `X` is étale. -/
  etale_toX : Etale toX
  /-- The morphism to the local model is étale. -/
  etale_toModel : Etale toModel
  /-- The two morphisms are compatible over `Spec R`. -/
  comm : toX ≫ f = toModel ≫ nodalModelHom R' π n ≫
    Spec.map (CommRingCat.ofHom (algebraMap R R'))
  /-- The chosen point. -/
  pt : U
  /-- It lies over `x`. -/
  pt_mem : toX.base pt = x
  /-- It lies over the origin of the local model. -/
  pt_origin : (toModel.base pt).asIdeal = nodalModelOrigin R' π n

attribute [instance] NodalChartAt.commRing NodalChartAt.isDomain
  NodalChartAt.isDiscreteValuationRing NodalChartAt.algebra NodalChartAt.etale

namespace NodalChartAt

variable {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {x : X} {n : ℕ}

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Charts transfer along étale morphisms.** If `ψ : Y ⟶ X` and `φ : Y ⟶ X'` are étale and
compatible over `Spec R`, a chart at `ψ y` for `f` gives a chart at `φ y` for `f'`, of the same
exponent: base change the chart along `ψ`. -/
public theorem nonempty_transfer (c : NodalChartAt f x n) {Y X' : Scheme.{u}} (ψ : Y ⟶ X)
    [Etale ψ] (φ : Y ⟶ X') [Etale φ] (f' : X' ⟶ Spec (.of R)) (h : ψ ≫ f = φ ≫ f') (y : Y)
    (hy : ψ.base y = x) : Nonempty (NodalChartAt f' (φ.base y) n) := by
  have := c.etale_toX
  have := c.etale_toModel
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := c.toX) (g := ψ)
    c.pt y (c.pt_mem.trans hy.symm)
  refine ⟨{
    R' := c.R'
    π := c.π
    irreducible := c.irreducible
    U := pullback c.toX ψ
    toX := pullback.snd c.toX ψ ≫ φ
    toModel := pullback.fst c.toX ψ ≫ c.toModel
    etale_toX := inferInstance
    etale_toModel := inferInstance
    comm := ?_
    pt := p
    pt_mem := ?_
    pt_origin := ?_ }⟩
  · rw [Category.assoc, ← h, ← pullback.condition_assoc, c.comm, Category.assoc]
  · change φ.base ((pullback.snd c.toX ψ).base p) = φ.base y
    rw [hp₂]
  · change (c.toModel.base ((pullback.fst c.toX ψ).base p)).asIdeal = _
    rw [hp₁]
    exact c.pt_origin

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **A chart can be shrunk until its chosen point is alone in its two fibres.** The fibres of
the two étale morphisms through the chosen point are discrete, so an open neighbourhood of the
point meets each of them only in the point. -/
public theorem exists_preimage_eq_singleton (c : NodalChartAt f x n) :
    ∃ c' : NodalChartAt f x n, c'.toX.base ⁻¹' {x} = {c'.pt} ∧
      c'.toModel.base ⁻¹' {c'.toModel.base c'.pt} = {c'.pt} := by
  have := c.etale_toX
  have := c.etale_toModel
  obtain ⟨O₁, hO₁, hO₁s⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (c.toX.isDiscrete_preimage_singleton x) c.pt c.pt_mem
  obtain ⟨O₂, hO₂, hO₂s⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (c.toModel.isDiscrete_preimage_singleton (c.toModel.base c.pt)) c.pt rfl
  have hpt₁ : c.pt ∈ O₁ := (hO₁s.symm ▸ Set.mem_singleton c.pt : c.pt ∈ O₁ ∩ _).1
  have hpt₂ : c.pt ∈ O₂ := (hO₂s.symm ▸ Set.mem_singleton c.pt : c.pt ∈ O₂ ∩ _).1
  have key {Z : Type u} {g : c.U → Z} {a : Z} {O W : Set c.U} (hO : O ∩ g ⁻¹' {a} = {c.pt})
      (hW : W ⊆ O) (hpt : c.pt ∈ W) (ha : g c.pt = a) :
      (fun z : W ↦ g z.1) ⁻¹' {a} = {⟨c.pt, hpt⟩} := by
    ext z
    refine ⟨fun hz ↦ Subtype.ext ?_, fun hz ↦ ?_⟩
    · have : z.1 ∈ O ∩ g ⁻¹' {a} := ⟨hW z.2, hz⟩
      rwa [hO] at this
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ha
  let V : c.U.Opens := ⟨O₁ ∩ O₂, hO₁.inter hO₂⟩
  have hV : c.pt ∈ V := ⟨hpt₁, hpt₂⟩
  refine ⟨{
    R' := c.R'
    π := c.π
    irreducible := c.irreducible
    U := V.toScheme
    toX := V.ι ≫ c.toX
    toModel := V.ι ≫ c.toModel
    etale_toX := inferInstance
    etale_toModel := inferInstance
    comm := by simp only [Category.assoc, c.comm]
    pt := ⟨c.pt, hV⟩
    pt_mem := c.pt_mem
    pt_origin := c.pt_origin }, ?_, ?_⟩
  · exact key hO₁s Set.inter_subset_left hV c.pt_mem
  · exact key hO₂s Set.inter_subset_right hV rfl

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **A chart at a point where the scheme is not regular has exponent at least two.** Regularity
of local rings is preserved and reflected by étale morphisms, the origin of the local model of
exponent zero is not a point, and the local model of exponent one is regular. -/
public theorem two_le_of_not_isRegularLocalRing (c : NodalChartAt f x n)
    (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x)) : 2 ≤ n := by
  have := c.etale_toX
  have := c.etale_toModel
  have hU : ¬ IsRegularLocalRing (c.U.presheaf.stalk c.pt) := by
    rw [isRegularLocalRing_stalk_iff_of_etale c.toX, c.pt_mem]
    exact hx
  rw [isRegularLocalRing_stalk_iff_of_etale c.toModel] at hU
  by_contra hn
  interval_cases n
  · have hprime := (c.toModel.base c.pt).isPrime
    rw [c.pt_origin, nodalModelOrigin_zero_eq_top] at hprime
    exact hprime.ne_top rfl
  · exact hU ((isRegular_nodalModel_one c.irreducible).isRegularLocalRing_stalk _)

end NodalChartAt

section BlowUp

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {x : X} (hx : IsClosed ({x} : Set X))

/-- The complement of a closed point, as an open subscheme. -/
private def complOpen : X.Opens := ⟨{x}ᶜ, hx.isOpen_compl⟩

/-- Away from the centre the blowup of a closed point is an isomorphism. -/
private theorem isIso_blowUpToBase_restrict_complOpen :
    IsIso (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) ∣_ complOpen hx) := by
  refine isIso_blowUpToBase_restrict_of_subset_compl_support _ _ ?_
  rw [coe_support_vanishingIdeal]
  exact fun z hz ↦ hz

/-- The restriction of `b` to the complement of a closed point commutes with the inclusions on
points. -/
private theorem complOpen_ι_base_morphismRestrict {Y : Scheme.{u}} (b : Y ⟶ X)
    (q : (b ⁻¹ᵁ complOpen hx).toScheme) :
    (complOpen hx).ι.base ((b ∣_ complOpen hx).base q) = b.base q.1 := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
  rfl

/-- **Away from the centre the blowup of a closed point is injective on points.** -/
public theorem blowUpToBase_injective_of_ne
    {y₁ y₂ : blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))}
    (h₁ : (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y₁ ≠ x)
    (h : (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y₁ =
      (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y₂) : y₁ = y₂ := by
  set b := blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))
  have := isIso_blowUpToBase_restrict_complOpen hx
  have hy₁ : y₁ ∈ b ⁻¹ᵁ complOpen hx := h₁
  have hy₂ : y₂ ∈ b ⁻¹ᵁ complOpen hx := show b.base y₂ ∈ ({x}ᶜ : Set X) from h ▸ h₁
  let p₁ : (b ⁻¹ᵁ complOpen hx).toScheme := ⟨y₁, hy₁⟩
  let p₂ : (b ⁻¹ᵁ complOpen hx).toScheme := ⟨y₂, hy₂⟩
  have heq : (b ∣_ complOpen hx).base p₁ = (b ∣_ complOpen hx).base p₂ := by
    apply (complOpen hx).ι.isOpenEmbedding.injective
    rwa [complOpen_ι_base_morphismRestrict, complOpen_ι_base_morphismRestrict]
  exact congrArg Subtype.val ((b ∣_ complOpen hx).isOpenEmbedding.injective heq)

/-- **Away from the centre the blowup of a closed point is surjective on points.** -/
public theorem exists_blowUpToBase_eq_of_ne {t : X} (ht : t ≠ x) :
    ∃ y : blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)),
      (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y = t := by
  set b := blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))
  have := isIso_blowUpToBase_restrict_complOpen hx
  obtain ⟨z, hz⟩ := (b ∣_ complOpen hx).surjective (⟨t, ht⟩ : (complOpen hx).toScheme)
  refine ⟨z.1, ?_⟩
  rw [← complOpen_ι_base_morphismRestrict hx b z, hz]
  rfl

/-- **Away from the centre the blowup of a closed point does not change local rings**: at a
point of the blowup not lying over `x`, its local ring is regular exactly when the local ring of
`X` at the image point is. -/
public theorem isRegularLocalRing_stalk_blowUp_iff_of_ne
    (y : blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))
    (hy : (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y ≠ x) :
    IsRegularLocalRing ((blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).presheaf.stalk y) ↔
      IsRegularLocalRing (X.presheaf.stalk
        ((blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y)) := by
  set b := blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))
  have := isIso_blowUpToBase_restrict_complOpen hx
  have hyU : y ∈ b ⁻¹ᵁ complOpen hx := hy
  let y₀ : (b ⁻¹ᵁ complOpen hx).toScheme := ⟨y, hyU⟩
  have h₁ := isRegularLocalRing_stalk_iff_of_isOpenImmersion (b ⁻¹ᵁ complOpen hx).ι y₀
  have h₂ := isRegularLocalRing_stalk_iff_of_etale (b ∣_ complOpen hx) y₀
  have h₃ := isRegularLocalRing_stalk_iff_of_isOpenImmersion (complOpen hx).ι
    ((b ∣_ complOpen hx).base y₀)
  rw [complOpen_ι_base_morphismRestrict hx b y₀] at h₃
  exact h₁.symm.trans (h₂.trans h₃)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **Away from the centre charts lift to the blowup of a closed point.** -/
public theorem NodalChartAt.nonempty_blowUp_of_ne
    (y : blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))
    (hy : (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y ≠ x) {m : ℕ}
    (c : NodalChartAt f ((blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y) m) :
    Nonempty (NodalChartAt (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) ≫ f) y m) := by
  set b := blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))
  have := isIso_blowUpToBase_restrict_complOpen hx
  have hyU : y ∈ b ⁻¹ᵁ complOpen hx := hy
  let y₀ : (b ⁻¹ᵁ complOpen hx).toScheme := ⟨y, hyU⟩
  exact c.nonempty_transfer ((b ∣_ complOpen hx) ≫ (complOpen hx).ι)
    (b ⁻¹ᵁ complOpen hx).ι (b ≫ f) (by rw [Category.assoc, morphismRestrict_ι_assoc]) y₀
    (by rw [Scheme.Hom.comp_apply]; exact complOpen_ι_base_morphismRestrict hx b y₀)

omit [IsDomain R] [IsDiscreteValuationRing R] in
variable {f} in
/-- **The blowup step of [Stacks, Tag 0CDE].** Let `f : X ⟶ Spec R` be at-worst-nodal of relative
dimension one, `x` a closed point of `X` and suppose there is an étale nodal chart of exponent
`n ≥ 2` at `x`. Let `b : X' ⟶ X` be the blowup of `X` in `x`. Then `X' ⟶ Spec R` is again
at-worst-nodal of relative dimension one, and at every point of `X'` over `x` at which `X'` is not
regular there is an étale nodal chart of exponent `n - 2`.

After shrinking the chart, the scheme-theoretic inverse images of `x` and of the origin of the
local model in the chart are the same reduced point. By [Stacks, Tag 0805] the blowup of the
chart in that point is both the base change of `X'` and the base change of the blowup of the local
model at its origin, which is described by [Stacks, Tag 0CDC]: it is at-worst-nodal over `R'`,
hence over `R` ([Stacks, Tag 0CD8]), and regular away from the origin of its central chart, the
local model of exponent `n - 2`. Being at-worst-nodal is étale local on the source
([Stacks, Tag 0C5D]), and off `x` the blowup is an isomorphism. -/
public theorem blowUp_nodalChartAt (hf : IsAtWorstNodalOfRelativeDimensionOne f) {n : ℕ}
    (c : NodalChartAt f x n) (hn : 2 ≤ n) :
    IsAtWorstNodalOfRelativeDimensionOne
        (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) ≫ f) ∧
      ∀ y : blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)),
        (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).base y = x →
        ¬ IsRegularLocalRing ((blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).presheaf.stalk y) →
          Nonempty (NodalChartAt (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) ≫ f)
            y (n - 2)) := by
  obtain ⟨c, hcX, hcM⟩ := c.exists_preimage_eq_singleton
  have := c.etale_toX
  have := c.etale_toModel
  set M := vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hM
  set b := blowUpToBase M with hb
  have hπ := c.irreducible
  have hmax : (Ideal.span {c.π}).IsMaximal := isMaximal_span_singleton_of_irreducible hπ
  have h1 : 1 ≤ n := by omega
  have hoC := isClosed_singleton_nodalModelOriginPoint hmax h1
  have hwo : c.toModel.base c.pt = nodalModelOriginPoint hmax h1 := PrimeSpectrum.ext c.pt_origin
  set Mo := vanishingIdeal (⟨{nodalModelOriginPoint hmax h1}, hoC⟩ :
    Closeds (nodalModel c.R' c.π n)) with hMo
  -- The two inverse images of the centres agree.
  have hcomap : M.comap c.toX = Mo.comap c.toModel := by
    rw [comap_vanishingIdeal_of_smooth c.toX _
        ⟨c.toX.base ⁻¹' {x}, hx.preimage c.toX.continuous⟩ rfl,
      comap_vanishingIdeal_of_smooth c.toModel _
        ⟨c.toModel.base ⁻¹' {nodalModelOriginPoint hmax h1}, hoC.preimage c.toModel.continuous⟩
        rfl]
    congr 1
    ext1
    change c.toX.base ⁻¹' {x} = c.toModel.base ⁻¹' {nodalModelOriginPoint hmax h1}
    rw [hcX, ← hwo, hcM]
  set I := M.comap c.toX with hI
  obtain ⟨h₁, sq₁⟩ := exists_isPullback_blowUpToBase_comap c.toX M
  obtain ⟨h₂, sq₂⟩ : ∃ h₂ : blowUp I ⟶ blowUp Mo,
      IsPullback (blowUpToBase I) h₂ c.toModel (blowUpToBase Mo) := by
    rw [hcomap]
    exact exists_isPullback_blowUpToBase_comap c.toModel Mo
  have he₁ : Etale h₁ := MorphismProperty.of_isPullback (P := @Etale) sq₁ inferInstance
  have he₂ : Etale h₂ := MorphismProperty.of_isPullback (P := @Etale) sq₂ inferInstance
  -- The blowup of the local model at its origin.
  obtain ⟨κ⟩ := nonempty_over_iso_blowUpToBase_nodalModelOriginPoint hmax h1
  let e := (Over.forget _).mapIso κ
  have he : e.inv ≫ nodalModelBlowupHom c.R' c.π n = blowUpToBase Mo := by
    have : e.hom ≫ blowUpToBase Mo = nodalModelBlowupHom c.R' c.π n := Over.w κ.hom
    rw [← this, Iso.inv_hom_id_assoc]
  let τ : blowUp I ⟶ nodalModelBlowup c.R' c.π n := h₂ ≫ e.inv
  have hτE : Etale τ := inferInstance
  have hSpec : Etale (Spec.map (CommRingCat.ofHom (algebraMap R c.R'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have hτ : τ ≫ nodalModelBlowupToBase c.R' c.π n ≫
      Spec.map (CommRingCat.ofHom (algebraMap R c.R')) = h₁ ≫ b ≫ f := by
    rw [← reassoc_of% sq₁.w, c.comm, reassoc_of% sq₂.w, ← reassoc_of% he]
    simp only [τ, nodalModelBlowupToBase, Category.assoc]
  have hnodal₁ : IsAtWorstNodalOfRelativeDimensionOne (h₁ ≫ b ≫ f) := by
    rw [← hτ]
    exact isAtWorstNodalOfRelativeDimensionOne_comp_etale _ τ
      (isAtWorstNodalOfRelativeDimensionOne_comp_etale_base _ _
        (isAtWorstNodalOfRelativeDimensionOne_nodalModelBlowupToBase hπ.ne_zero hn))
  -- The points over `x` come from the chart.
  have hlift : ∀ y : blowUp M, b.base y = x → ∃ y' : blowUp I,
      (blowUpToBase I).base y' = c.pt ∧ h₁.base y' = y := fun y hy ↦
    AlgebraicGeometry.Scheme.exists_preimage_of_isPullback sq₁ c.pt y (c.pt_mem.trans hy.symm)
  have hiso := isIso_blowUpToBase_restrict_complOpen hx
  refine ⟨?_, fun y hy hyreg ↦ ?_⟩
  · -- Nodality, étale locally on the source.
    let V : ULift.{u} Bool → Scheme.{u} := fun i ↦
      if i.down then blowUp I else (b ⁻¹ᵁ complOpen hx).toScheme
    let g : ∀ i, V i ⟶ blowUp M := fun i ↦
      match i with
      | ⟨true⟩ => h₁
      | ⟨false⟩ => (b ⁻¹ᵁ complOpen hx).ι
    have hcov : Presieve.ofArrows V g ∈ Scheme.etalePrecoverage (blowUp M) := by
      refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr ⟨fun z ↦ ?_, fun i ↦ ?_⟩
      · by_cases hz : b.base z = x
        · obtain ⟨y', -, hy'⟩ := hlift z hz
          exact ⟨⟨true⟩, y', hy'⟩
        · exact ⟨⟨false⟩, ⟨z, hz⟩, rfl⟩
      · rcases i with ⟨_ | _⟩
        · exact (inferInstance : Etale (b ⁻¹ᵁ complOpen hx).ι)
        · exact he₁
    refine (isAtWorstNodalOfRelativeDimensionOne_iff_of_etaleCovering _ g hcov).mpr fun i ↦ ?_
    rcases i with ⟨_ | _⟩
    · change IsAtWorstNodalOfRelativeDimensionOne ((b ⁻¹ᵁ complOpen hx).ι ≫ b ≫ f)
      rw [← morphismRestrict_ι_assoc]
      exact isAtWorstNodalOfRelativeDimensionOne_comp_etale _ _
        (isAtWorstNodalOfRelativeDimensionOne_comp_etale f (complOpen hx).ι hf)
    · exact hnodal₁
  · -- A singular point over `x` lifts to the chart, and then lies at the central origin.
    obtain ⟨y', -, hy'⟩ := hlift y hy
    have hy'reg : ¬ IsRegularLocalRing ((blowUp I).presheaf.stalk y') := by
      rw [isRegularLocalRing_stalk_iff_of_etale h₁, hy']
      exact hyreg
    rw [isRegularLocalRing_stalk_iff_of_etale τ] at hy'reg
    obtain ⟨jc, hjcoi, hjcw, hjc⟩ :=
      exists_isOpenImmersion_nodalModel_sub_two_of_not_isRegularLocalRing hπ hn
    obtain ⟨z, hz₁, hz₂⟩ := hjc (τ.base y') hy'reg
    obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := τ) (g := jc)
      y' z hz₁.symm
    refine ⟨{
      R' := c.R'
      π := c.π
      irreducible := hπ
      U := pullback τ jc
      toX := pullback.fst τ jc ≫ h₁
      toModel := pullback.snd τ jc
      etale_toX := inferInstance
      etale_toModel := inferInstance
      comm := ?_
      pt := p
      pt_mem := ?_
      pt_origin := ?_ }⟩
    · rw [Category.assoc, ← hτ, pullback.condition_assoc, reassoc_of% hjcw]
    · change h₁.base ((pullback.fst τ jc).base p) = y
      rw [hp₁, hy']
    · rw [hp₂, hz₂]

end BlowUp

end Stacks.SemistableReduction

end
