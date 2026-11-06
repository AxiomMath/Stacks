module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartCover
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartLifts
public import StacksFrontier.RingTheory.Etale.LiftFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

/-!
# A smooth morphism of algebraic spaces is formally smooth

This file proves the implication of Stacks 04AM from smoothness to formal smoothness for an
arbitrary morphism of algebraic spaces (`AlgebraicGeometry.Space.formallySmooth_of_isSmooth'`),
with no hypothesis beyond smoothness.

Let `f : X ⟶ Y` be smooth, `i : T ⟶ T'` a square-zero closed immersion of affine objects of the
site, `x` a section of `X` over `T` and `y` a section of `Y` over `T'` with `f x = y|_T`. Base
changing along `y` reduces the problem to a smooth morphism `p : X' ⟶ h_{T'}` and a section `x'`
of `X'` over `T` lying over `i`, to be extended over `T'`. Write `A' = Γ(T')` and `A = Γ(T)`.

* `x'` factors, on a surjective étale affine cover `W ⟶ T`, through one affine étale chart `Z` of
  `X'` (`AlgebraicGeometry.Space.exists_affine_chart_cover`); the ring `C = Γ(Z)` is smooth over
  `A'` because `p` is smooth, and the chart has unique infinitesimal lifts because it is étale
  (`AlgebraicGeometry.Space.chartUniqueLifts_of_formallyEtale`).
* The étale, faithfully flat `A`-algebra `Γ(W)` lifts to an étale, faithfully flat `A'`-algebra
  `B'` with `A ⊗_{A'} B' ≅ Γ(W)` (Stacks 04D1, `Stacks.exists_etale_faithfullyFlat_lift`).
* `AlgebraicGeometry.Space.RelSec.exists_lift_of_chart` — the torsor of local lifts, trivialised
  by the flat base change of the module of differences of lifts and faithful flatness of `B'` —
  extends `x'` over `T'`.

## Main results

* `AlgebraicGeometry.Space.formallySmooth_of_isSmooth'`: **Stacks 04AM**, condition (1) implies
  condition (2), formal smoothness part.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SquareZeroLift Stacks.LocalThickening
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Rings of global sections of affine objects -/

section Sections

variable {T T' : BigFppfOver B S hS}

/-- A square-zero closed immersion of affine objects is surjective on rings of global
sections. -/
theorem surjective_appTop_of_isSquareZeroClosedImmersion
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    {i : T ⟶ T'} (hi : IsSquareZeroClosedImmersion B S hS i) :
    Function.Surjective ((BigFppfOver.toScheme B S hS).map i).appTop.hom := by
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hi.1
  exact (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map i)).2

/-- The kernel of the map on rings of global sections induced by a square-zero closed immersion
of affine objects has square zero. -/
theorem ker_appTop_sq_of_isSquareZeroClosedImmersion
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    {i : T ⟶ T'} (hi : IsSquareZeroClosedImmersion B S hS i) :
    RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom ^ 2 = ⊥ := by
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) := hi.1
  have h := congrArg (fun J : Scheme.IdealSheafData ((BigFppfOver.toScheme B S hS).obj T') =>
    J.ideal ⟨⊤, isAffineOpen_top _⟩) hi.2
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at h
  rwa [Scheme.Hom.ker_apply] at h

end Sections

/-! ### Affine objects over the spectrum of a ring -/

section IsoSpecBase

variable {B S hS} {A' : Type u} [CommRing A'] (s₀ : Spec (.of A') ⟶ S)

/-- The `R`-algebra structure on the ring of global sections of an object over `Spec R`. -/
@[instance_reducible]
def baseAlgebra {R : Type u} [CommRing R] [Algebra A' R] (hR : B.Contains (Spec (.of R)))
    {V : BigFppfOver B S hS} (v : V ⟶ specOver B S hS s₀ R hR) :
    Algebra R Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  (((BigFppfOver.toScheme B S hS).map v).appTop.hom.comp
    (Scheme.ΓSpecIso (.of R)).inv.hom).toAlgebra

/-- For an affine object `V` over `Spec R`, the morphism `V ⟶ Spec R` factors as the
identification of `V` with the spectrum of its ring of global sections followed by `Spec` of
the algebra map of `AlgebraicGeometry.Space.baseAlgebra`. -/
theorem specMap_baseAlgebra {R : Type u} [CommRing R] [Algebra A' R]
    (hR : B.Contains (Spec (.of R))) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ specOver B S hS s₀ R hR) :
    letI := baseAlgebra s₀ hR v
    ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) =
      (BigFppfOver.toScheme B S hS).map v := by
  let := baseAlgebra s₀ hR v
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (specOver B S hS s₀ R hR)) :=
    inferInstanceAs (IsAffine (Spec (.of R)))
  have h : CommRingCat.ofHom (algebraMap R Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) =
      (Scheme.ΓSpecIso (.of R)).inv ≫ ((BigFppfOver.toScheme B S hS).map v).appTop := rfl
  rw [h, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
    show ((BigFppfOver.toScheme B S hS).obj (specOver B S hS s₀ R hR)).isoSpec.hom =
      (Spec (.of R)).isoSpec.hom from rfl, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id]
  exact Category.comp_id _

/-- **An affine object is the spectrum of its ring of global sections**, as an object over `S`
through `Spec A'`, for an `A'`-algebra structure on the ring compatible with the structure
morphisms. -/
def isoSpecOverOf {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [Algebra A' Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (h : ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A' Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) ≫
        s₀ = B.inclusion.map V.hom) :
    V ≅ specOver B S hS s₀ Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
      (contains_spec_sections B S hS V) :=
  Over.isoMk (B.inclusion.preimageIso ((BigFppfOver.toScheme B S hS).obj V).isoSpec) (by
    apply B.inclusion.map_injective
    rwa [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage])

/-- The inverse of `AlgebraicGeometry.Space.isoSpecOverOf` is, as a morphism of schemes, the
inverse of the identification of `V` with the spectrum of its ring of global sections. -/
theorem toScheme_map_isoSpecOverOf_inv {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [Algebra A' Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (h : ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A' Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) ≫
        s₀ = B.inclusion.map V.hom) :
    (BigFppfOver.toScheme B S hS).map (isoSpecOverOf s₀ h).inv =
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.inv := by
  show B.inclusion.map (B.inclusion.preimageIso _).inv = _
  rw [Functor.preimageIso_inv, Functor.map_preimage]

/-- The compatibility of `AlgebraicGeometry.Space.isoSpecOverOf` for the algebra structure of a
morphism to `Spec R`, `R` an `A'`-algebra. -/
theorem specMap_baseAlgebra_comp {R : Type u} [CommRing R] [Algebra A' R]
    (hR : B.Contains (Spec (.of R))) {V : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] (v : V ⟶ specOver B S hS s₀ R hR)
    [Algebra A' Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    (hA : letI := baseAlgebra s₀ hR v
      algebraMap A' Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) =
        (algebraMap R Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)).comp (algebraMap A' R)) :
    ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A' Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) ≫
        s₀ = B.inclusion.map V.hom := by
  let := baseAlgebra s₀ hR v
  rw [hA, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, ← Category.assoc,
    specMap_baseAlgebra s₀ hR v]
  have hv := congrArg B.inclusion.map (Over.w v)
  rwa [B.inclusion.map_comp] at hv

/-- The underlying morphism of schemes of the structure map `Spec Γ ⟶ Spec A'` as a morphism of
`specOver` objects. -/
private theorem toScheme_map_specOverHom_ofId {R : Type u} [CommRing R] [Algebra A' R]
    (hA' : B.Contains (Spec (.of A'))) (hR : B.Contains (Spec (.of R))) :
    (BigFppfOver.toScheme B S hS).map (specOverHom B S hS s₀ hA' hR (Algebra.ofId A' R)) =
      Spec.map (CommRingCat.ofHom (algebraMap A' R)) := rfl

/-- For an affine object `V` over `Spec A'`, the inverse of `isoSpecOverOf` followed by the
structure map `v` is the morphism of `specOver` objects given by the structure algebra map. -/
private theorem isoSpecOverOf_inv_comp_baseAlgebra (hA' : B.Contains (Spec (.of A')))
    {V : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (v : V ⟶ specOver B S hS s₀ A' hA') :
    letI := baseAlgebra s₀ hA' v
    ∀ h, (isoSpecOverOf s₀ h).inv ≫ v = specOverHom B S hS s₀ hA'
      (contains_spec_sections B S hS V)
      (Algebra.ofId A' Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) := by
  intro h
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, toScheme_map_isoSpecOverOf_inv, toScheme_map_specOverHom_ofId,
    ← specMap_baseAlgebra s₀ hA' v, Iso.inv_hom_id_assoc]

end IsoSpecBase

/-! ### The lifting problem over spectra of algebras -/

section Main

variable {B S hS} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A smooth morphism of algebraic spaces solves the lifting problems over spectra of
algebras.** Let `A' → A` be surjective with square-zero kernel, with `Spec A' ⟶ S` fixed, `x` a
section of `X` over `Spec A` and `y` a section of `Y` over `Spec A'` with `f x = y|_{Spec A}`.
Then `x` extends to a section of `X` over `Spec A'` mapping to `y`. -/
theorem exists_lift_specOver_of_isSmooth (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsSmooth B S hS f)
    {A' A : Type u} [CommRing A'] [CommRing A] [Algebra A' A] (s₀ : Spec (.of A') ⟶ S)
    [hA'site : InSite B A'] [hAsite : InSite B A]
    (hsurj : Function.Surjective (algebraMap A' A)) (hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (x : X.obj (op (specOver B S hS s₀ A hAsite.out)))
    (y : Y.obj (op (specOver B S hS s₀ A' hA'site.out)))
    (hxy : f.app _ x = Y.map (specOverHom B S hS s₀ hA'site.out hAsite.out
      (Algebra.ofId A' A)).op y) :
    ∃ w, X.map (specOverHom B S hS s₀ hA'site.out hAsite.out (Algebra.ofId A' A)).op w = x ∧
      f.app _ w = y := by
  classical
  have hA' := hA'site.out
  let T₀ := specOver B S hS s₀ A' hA'
  -- the base change of `f` along `y`
  let yT : yoneda.obj T₀ ⟶ Y := yonedaEquiv.symm y
  have : HasLimit (cospan f yT) := HasLimitsOfShape.has_limit _
  set X':= pullback f yT
  set p : X' ⟶ yoneda.obj T₀ := pullback.snd f yT
  have hX' : IsAlgebraicSpace B S hS X' :=
    isAlgebraicSpace_pullback B S hS f yT hX (isAlgebraicSpace_yoneda B S hS T₀) hY
  have hp : IsSmooth B S hS p :=
    (isSmooth_isStableUnderBaseChange_of_isEtaleLocal B S hS
      AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk yT : (⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩ :
          AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)) hf
  -- the section of `X'` over `Spec A`
  set iA := specOverHom B S hS s₀ hA' hAsite.out (Algebra.ofId A' A)
  have hw : yonedaEquiv.symm x ≫ f = yoneda.map iA ≫ yT := by
    rw [yonedaEquiv_symm_naturality_right, hxy]
    exact (yonedaEquiv_symm_naturality_left iA (F := Y) y).symm
  set g : yoneda.obj (specOver B S hS s₀ A hAsite.out) ⟶ X' :=
    pullback.lift (yonedaEquiv.symm x) (yoneda.map iA) hw with hg
  have hgp : g ≫ p = yoneda.map iA := pullback.lift_snd _ _ _
  have hgf : g ≫ pullback.fst f yT = yonedaEquiv.symm x := pullback.lift_fst _ _ _
  set ξ : RelSec p A := ⟨yonedaEquiv g, by
    rw [← yonedaEquiv_comp, hgp, yonedaEquiv_yoneda_map]⟩ with hξ
  -- an affine étale chart on an étale affine cover
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (specOver B S hS s₀ A hAsite.out)) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  obtain ⟨Z, W, c, m, π, hZ, hW, hcE, hπE, hπS, hmc⟩ := exists_affine_chart_cover B S hS hX' g
  -- the chart is smooth over `Spec A'`
  set ψ : Z ⟶ T₀ := yoneda.preimage (c ≫ p)
  have hψ : yoneda.map ψ = c ≫ p := yoneda.map_preimage _
  have hψs : AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map ψ) :=
    hp Z T₀ c (𝟙 _) ψ hcE (presheaf_etale_id B S hS T₀) (by rw [hψ, Category.comp_id])
  let : Algebra A' Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) := baseAlgebra s₀ hA' ψ
  have hCsite : InSite B Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) :=
    ⟨contains_spec_sections B S hS Z⟩
  have hZcompat := specMap_baseAlgebra_comp s₀ hA' ψ rfl
  set eZ := isoSpecOverOf s₀ hZcompat
  have heZψ := isoSpecOverOf_inv_comp_baseAlgebra s₀ hA' ψ hZcompat
  have hCsm : Algebra.Smooth A' Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) := by
    have h : AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom
        (algebraMap A' Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)))) := by
      rw [← toScheme_map_specOverHom_ofId (hS := hS) s₀ hA' hCsite.out, ← heZψ, Functor.map_comp]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth), CommRingCat.hom_ofHom,
      RingHom.smooth_algebraMap] at h
    exact h
  -- the chart over `Spec Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)`
  set c' : yoneda.obj (specOver B S hS s₀ Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      hCsite.out) ⟶ X' := yoneda.map eZ.inv ≫ c
  have hc'E : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf c' :=
    etale_comp_of_scheme B S hS eZ.inv c (by infer_instance) hcE
  have hcp : c' ≫ p = yoneda.map (specOverHom B S hS s₀ hA' hCsite.out
      (Algebra.ofId A' Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤))) := by
    rw [Category.assoc, ← hψ, ← Functor.map_comp, heZψ]
  set φ := relChartSection c' hcp
  have hφ : ChartUniqueLifts φ :=
    chartUniqueLifts_of_formallyEtale c' (formallyEtale_of_etale B S hS c' hc'E) hcp
  -- the cover as the spectrum of an étale, faithfully flat `A`-algebra
  set πA : W ⟶ T₀ := π ≫ iA
  let : Algebra A' Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) := baseAlgebra s₀ hA' πA
  have hWsite : InSite B Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
    ⟨contains_spec_sections B S hS W⟩
  have hWcompat := specMap_baseAlgebra_comp s₀ hA' πA rfl
  set eW := isoSpecOverOf s₀ hWcompat
  have heWπA := isoSpecOverOf_inv_comp_baseAlgebra s₀ hA' πA hWcompat
  obtain ⟨τA, hτA, -⟩ := existsUnique_specOverHom (hA' := hA') (eW.inv ≫ π) (by
    rw [Category.assoc]; exact heWπA)
  let : Algebra A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) := τA.toRingHom.toAlgebra
  have : IsScalarTower A' A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun a => (τA.commutes a).symm
  have hπτ : (BigFppfOver.toScheme B S hS).map π = (BigFppfOver.toScheme B S hS).map eW.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤))) := by
    have hτ : Spec.map (CommRingCat.ofHom (algebraMap A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)))
        = (BigFppfOver.toScheme B S hS).map (specOverHom B S hS s₀ hAsite.out hWsite.out τA) :=
      rfl
    rw [hτ, hτA, ← Functor.map_comp, Iso.hom_inv_id_assoc]
  have hτW : Spec.map (CommRingCat.ofHom (algebraMap A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)))
      = (BigFppfOver.toScheme B S hS).map eW.inv ≫ (BigFppfOver.toScheme B S hS).map π := by
    rw [hπτ, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hWet : Algebra.Etale A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) := by
    have h : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom
        (algebraMap A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)))) := by
      rw [hτW]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale), CommRingCat.hom_ofHom,
      RingHom.etale_algebraMap] at h
    exact h
  have hWff : Module.FaithfullyFlat A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) := by
    refine Module.FaithfullyFlat.of_comap_surjective ?_
    have h : Surjective (Spec.map (CommRingCat.ofHom
        (algebraMap A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)))) := by
      rw [hτW]
      infer_instance
    rw [surjective_iff] at h
    exact h
  -- the lift of the cover to `Spec A'`
  obtain ⟨B', _, _, hB'et, hB'ff, e, he⟩ := Stacks.exists_etale_faithfullyFlat_lift
    (A' := A') (A := A) (B := Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) hsurj hI
  have : InSite B B' := ⟨Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit A' B' hA'⟩
  -- the chart over the cover
  obtain ⟨ζW, hζW, -⟩ := existsUnique_specOverHom (hA' := hA') (eW.inv ≫ m ≫ eZ.hom) (by
    have hmψ : m ≫ ψ = π ≫ iA := by
      apply yoneda.map_injective
      rw [Functor.map_comp, Functor.map_comp, hψ, ← Category.assoc, hmc, Category.assoc, hgp]
    rw [Category.assoc, Category.assoc, ← heZψ, Iso.hom_inv_id_assoc, hmψ]
    exact heWπA)
  set ζ : Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) →ₐ[A'] A ⊗[A'] B' :=
    e.symm.toAlgHom.comp ζW with hζdef
  set t := specOverHom B S hS s₀ hWsite.out (inSite_tensorProduct (B := B)).out
    (e.symm.toAlgHom : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →ₐ[A'] A ⊗[A'] B')
  have hinclL : (e.symm.toAlgHom.comp τA : A →ₐ[A'] A ⊗[A'] B') =
      Algebra.TensorProduct.includeLeft := by
    ext a
    show e.symm (algebraMap A Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) a) = a ⊗ₜ 1
    rw [← he a, AlgEquiv.symm_apply_apply]
  have hζchart : IsChartOf φ ξ ζ := by
    refine RelSec.ext ?_
    rw [chartSection_map]
    show c.app _ (specOverHom B S hS s₀ hCsite.out _ ζ ≫ eZ.inv) =
      X'.map (specOverHom B S hS s₀ hAsite.out _ Algebra.TensorProduct.includeLeft).op
        (yonedaEquiv g)
    have h1 : specOverHom B S hS s₀ hCsite.out (inSite_tensorProduct (B := B)).out ζ ≫ eZ.inv =
        t ≫ eW.inv ≫ m := by
      rw [hζdef, ← specOverHom_comp (hR' := hWsite.out), hζW]
      simp [t]
    have h2 : t ≫ eW.inv ≫ π = specOverHom B S hS s₀ hAsite.out
        (inSite_tensorProduct (B := B)).out Algebra.TensorProduct.includeLeft := by
      rw [← hτA]
      show specOverHom B S hS s₀ hWsite.out (inSite_tensorProduct (B := B)).out
        (e.symm.toAlgHom : Γ((BigFppfOver.toScheme B S hS).obj W, ⊤) →ₐ[A'] A ⊗[A'] B') ≫ _ = _
      rw [specOverHom_comp, hinclL]
    rw [h1, yonedaEquiv_naturality]
    show c.app _ ((t ≫ eW.inv) ≫ m) = (yoneda.map _ ≫ g).app _ (𝟙 _)
    rw [← h2]
    have hmc' := congrArg (fun h => h.app (op (specOver B S hS s₀ (A ⊗[A'] B')
      (inSite_tensorProduct (B := B)).out)) (t ≫ eW.inv)) hmc
    simp only [NatTrans.comp_app, types_comp_apply, yoneda_map_app] at hmc'
    exact hmc'
  -- the lift, and the section of `X` it gives
  obtain ⟨w, hw⟩ := RelSec.exists_lift_of_chart hsurj hI hφ hζchart hX' (B' := B')
  refine ⟨(pullback.fst f yT).app _ w.1, ?_, ?_⟩
  · have h := congrArg (fun z : RelSec p A => (pullback.fst f yT).app _ z.1) hw
    simp only [RelSec.map_val] at h
    rw [← NatTrans.naturality_apply, h]
    show (pullback.fst f yT).app _ (yonedaEquiv g) = x
    rw [← yonedaEquiv_comp, hgf, Equiv.apply_symm_apply]
  · rw [← NatTrans.comp_app_apply, pullback.condition, NatTrans.comp_app_apply]
    have hpw : p.app _ w.1 = 𝟙 T₀ := by
      rw [w.2, specOverHom_congr (algHom_self_ext (Algebra.ofId A' A') (AlgHom.id A' A')),
        specOverHom_id]
    show yT.app _ (p.app _ w.1) = y
    rw [hpw]
    exact Y.map_id_apply _ y

/-- **Stacks 04AM, (1) implies (2), formal smoothness.** A smooth morphism of algebraic spaces
over `S` is formally smooth.

The test objects are affine; identifying them with the spectra of their rings of global
sections, `AlgebraicGeometry.Space.exists_lift_specOver_of_isSmooth` solves the lifting
problem. -/
theorem formallySmooth_of_isSmooth' (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsSmooth B S hS f) : FormallySmooth f := by
  classical
  intro T T' hT hT' i hi x y hxy
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map i).appTop.hom.toAlgebra
  have hsurj := surjective_appTop_of_isSquareZeroClosedImmersion B S hS hi
  have hI := ker_appTop_sq_of_isSquareZeroClosedImmersion B S hS hi
  have : InSite B Γ((BigFppfOver.toScheme B S hS).obj T', ⊤) :=
    ⟨contains_spec_sections B S hS T'⟩
  have : InSite B Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
    ⟨contains_spec_sections B S hS T⟩
  let eT := isoSpecOver B S hS i rfl
  let eT' := isoSpecOverSelf B S hS T'
  obtain ⟨w, hw, hfw⟩ := exists_lift_specOver_of_isSmooth hX hY hf (specStructure B S hS T')
    hsurj hI (X.map eT.inv.op x) (Y.map eT'.inv.op y)
    (by
      rw [NatTrans.naturality_apply, hxy, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply, ← op_comp, ← op_comp, isoSpecOver_inv_comp])
  have hiT : i ≫ eT'.hom = eT.hom ≫ specOverHom B S hS (specStructure B S hS T')
      (contains_spec_sections B S hS T') (contains_spec_sections B S hS T) (Algebra.ofId _ _) := by
    calc i ≫ eT'.hom = eT.hom ≫ (eT.inv ≫ i) ≫ eT'.hom := by simp
      _ = _ := by
        rw [isoSpecOver_inv_comp]
        simp [eT']
  refine ⟨X.map eT'.hom.op w, ?_, ?_⟩
  · rw [← Functor.map_comp_apply, ← op_comp, hiT, op_comp, Functor.map_comp_apply,
      hw, ← Functor.map_comp_apply, ← op_comp, Iso.hom_inv_id, op_id,
      Functor.map_id_apply]
  · rw [NatTrans.naturality_apply, hfw, ← Functor.map_comp_apply, ← op_comp,
      Iso.hom_inv_id, op_id, Functor.map_id_apply]

/-- **Stacks 04AM.** A morphism of algebraic spaces over `S` is smooth exactly when it is locally
of finite presentation and formally smooth. -/
@[stacks 04AM]
theorem isSmooth_iff_isLocallyOfFinitePresentation_and_formallySmooth
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsSmooth B S hS f ↔ IsLocallyOfFinitePresentation B S hS f ∧ FormallySmooth f :=
  ⟨fun hf => ⟨isLocallyOfFinitePresentation_of_isSmooth B S hS hf,
      formallySmooth_of_isSmooth' hX hY hf⟩,
    fun h => isSmooth_of_isLocallyOfFinitePresentation_of_formallySmooth h.1 h.2⟩

end Main

end AlgebraicGeometry.Space

end
