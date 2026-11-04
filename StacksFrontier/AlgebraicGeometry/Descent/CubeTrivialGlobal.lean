module

public import StacksFrontier.AlgebraicGeometry.Descent.CubeTrivialClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The theorem of the cube over an arbitrary base

This file assembles the openness step (`Stacks.Cube.exists_basicOpen_nonvanishing`) and the
closedness step (`Stacks.Cube.nonempty_iso_unit_fibre_of_forall_away`) of the proof of
[Stacks, Tag 0BF4] over a general base.

## Main results

* `Stacks.Cube.isPullback_baseChange`: the base change of a fibre product square along a morphism
  of the base is a fibre product square.
* `Stacks.Cube.geometricallyIntegral_comp`: a fibre product of two flat, locally finitely
  presented, geometrically integral morphisms is geometrically integral
  ([Stacks, Tag 038K] with [Stacks, Tag 035Z]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.DescentLocusComparison

universe u

namespace Stacks.Cube

variable {Z X Y P : Scheme.{u}} {fX : X ⟶ Z} {fY : Y ⟶ Z} {r : P ⟶ X} {q : P ⟶ Y}

/-- The base change of `r : P ⟶ X` along `t : T ⟶ Z`, between the canonical base changes. -/
abbrev baseChangeFst (H : IsPullback r q fX fY) {T : Scheme.{u}} (t : T ⟶ Z) :
    pullback (r ≫ fX) t ⟶ pullback fX t :=
  pullback.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _)
    (by rw [Category.assoc]; exact pullback.condition)

/-- The base change of `q : P ⟶ Y` along `t : T ⟶ Z`, between the canonical base changes. -/
abbrev baseChangeSnd (H : IsPullback r q fX fY) {T : Scheme.{u}} (t : T ⟶ Z) :
    pullback (r ≫ fX) t ⟶ pullback fY t :=
  pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _)
    (by rw [Category.assoc, ← H.w]; exact pullback.condition)

/-- **Base change of a fibre product square.** If `P = X ×_Z Y`, then for every `t : T ⟶ Z`,
`P ×_Z T = (X ×_Z T) ×_T (Y ×_Z T)`. -/
theorem isPullback_baseChange (H : IsPullback r q fX fY) {T : Scheme.{u}} (t : T ⟶ Z) :
    IsPullback (baseChangeFst H t) (baseChangeSnd H t) (pullback.snd fX t)
      (pullback.snd fY t) := by
  have h1 : baseChangeFst H t ≫ pullback.snd fX t = pullback.snd (r ≫ fX) t :=
    pullback.lift_snd _ _ _
  have h2 : baseChangeSnd H t ≫ pullback.snd fY t = pullback.snd (r ≫ fX) t :=
    pullback.lift_snd _ _ _
  have h3 : baseChangeFst H t ≫ pullback.fst fX t = pullback.fst (r ≫ fX) t ≫ r :=
    pullback.lift_fst _ _ _
  have h4 : baseChangeSnd H t ≫ pullback.fst fY t = pullback.fst (r ≫ fX) t ≫ q :=
    pullback.lift_fst _ _ _
  have hs : IsPullback (pullback.fst (r ≫ fX) t) (baseChangeFst H t ≫ pullback.snd fX t)
      (r ≫ fX) t := by
    rw [h1]
    exact IsPullback.of_hasPullback (r ≫ fX) t
  have hX : IsPullback (pullback.fst (r ≫ fX) t) (baseChangeFst H t) r (pullback.fst fX t) :=
    IsPullback.of_bot hs h3.symm (IsPullback.of_hasPullback fX t)
  have hbig : IsPullback (baseChangeSnd H t ≫ pullback.fst fY t) (baseChangeFst H t) fY
      (pullback.snd fX t ≫ t) := by
    rw [h4, ← pullback.condition]
    exact hX.paste_horiz H.flip
  exact (IsPullback.of_right hbig (by rw [h1, h2]) (IsPullback.of_hasPullback fY t)).flip

/-- **A fibre product of geometrically integral morphisms is geometrically integral.** For
`P = X ×_Z Y` with `X ⟶ Z` and `Y ⟶ Z` flat, locally of finite presentation and geometrically
integral, so is `P ⟶ Z`: it is geometrically irreducible as a composite of universally open
geometrically irreducible morphisms, and geometrically reduced since its base change to a field
`K` is the product over `K` of two geometrically reduced `K`-schemes ([Stacks, Tag 035Z]). -/
@[ega "IV 4.5.8" "(ii), special case", ega "IV 4.6.5" "(ii), special case"]
theorem geometricallyIntegral_comp (H : IsPullback r q fX fY)
    [Flat fX] [LocallyOfFinitePresentation fX] [GeometricallyIntegral fX]
    [Flat fY] [LocallyOfFinitePresentation fY] [GeometricallyIntegral fY] :
    GeometricallyIntegral (r ≫ fX) := by
  have : Flat r := MorphismProperty.of_isPullback H.flip inferInstance
  have : LocallyOfFinitePresentation r := MorphismProperty.of_isPullback H.flip inferInstance
  have : GeometricallyIrreducible r := MorphismProperty.of_isPullback H.flip inferInstance
  have : GeometricallyIrreducible (r ≫ fX) := GeometricallyIrreducible.comp r fX
  have : GeometricallyReduced (r ≫ fX) := by
    rw [GeometricallyReduced.eq_geometrically, geometrically_iff_of_isClosedUnderIsomorphisms]
    intro K _ t
    set fX₀ := pullback.snd fX t
    set fY₀ := pullback.snd fY t
    have : GeometricallyReduced (pullback.fst fX₀ fY₀ ≫ fX₀) :=
      geometricallyReduced_pullback_over_field fX₀ fY₀
    have : IsReduced (pullback fX₀ fY₀) :=
      GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian (pullback.fst fX₀ fY₀ ≫ fX₀)
    exact isReduced_of_isOpenImmersion (isPullback_baseChange H t).isoPullback.hom
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- Triviality of a pullback is inherited along a factorization. -/
theorem nonempty_iso_unit_pullback_of_fac {X₁ X₂ X₃ : Scheme.{u}} (k : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (g' : X₁ ⟶ X₃) (h : k ≫ g = g') (L : X₃.Modules)
    (e : Nonempty ((Scheme.Modules.pullback g).obj L ≅ Scheme.unitModule X₂)) :
    Nonempty ((Scheme.Modules.pullback g').obj L ≅ Scheme.unitModule X₁) :=
  ⟨((Scheme.Modules.pullbackCongr h).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp k g).app L).symm ≪≫
    (Scheme.Modules.pullback k).mapIso e.some ≪≫ Scheme.Modules.pullbackUnitIso k⟩

/-- Triviality of an iterated pullback is triviality of the pullback along the composite. -/
theorem nonempty_iso_unit_pullback_pullback {X₁ X₂ X₃ : Scheme.{u}} (k : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (L : X₃.Modules)
    (e : Nonempty ((Scheme.Modules.pullback (k ≫ g)).obj L ≅ Scheme.unitModule X₁)) :
    Nonempty ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj L) ≅
      Scheme.unitModule X₁) :=
  ⟨(Scheme.Modules.pullbackComp k g).app L ≪≫ e.some⟩

/-- Triviality of the pullback along `g` gives triviality of the pullback along `a` of the
pullback along `b`, when `k ≫ g = a ≫ b`. -/
private theorem nonempty_iso_unit_pullback_pullback_of_fac {X₁ X₂ X₃ X₄ : Scheme.{u}}
    (k : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (a : X₁ ⟶ X₄) (b : X₄ ⟶ X₃) (h : k ≫ g = a ≫ b) (L : X₃.Modules)
    (e : Nonempty ((Scheme.Modules.pullback g).obj L ≅ Scheme.unitModule X₂)) :
    Nonempty ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj L) ≅
      Scheme.unitModule X₁) :=
  nonempty_iso_unit_pullback_pullback _ _ L (nonempty_iso_unit_pullback_of_fac k g _ h L e)

/-- **Triviality on the fibre over a point gives triviality over every field point with that
image.** A morphism `t : Spec K ⟶ Z` with image `z` factors through `Spec κ(z)`. -/
theorem nonempty_iso_unit_fibre_of_residueField {P : Scheme.{u}} (p : P ⟶ Z) (L : P.Modules)
    (z : Z)
    (hz : Nonempty ((Scheme.Modules.pullback (pullback.fst p (Z.fromSpecResidueField z))).obj
      L ≅ Scheme.unitModule (pullback p (Z.fromSpecResidueField z))))
    {K : Type u} [Field K] (t : Spec (.of K) ⟶ Z) (ht : t.base (IsLocalRing.closedPoint K) = z) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst p t)).obj L ≅
      Scheme.unitModule (pullback p t)) := by
  subst ht
  have hfac := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z t
  set m := Spec.map (Z.descResidueField (Scheme.stalkClosedPointTo t))
  exact nonempty_iso_unit_pullback_of_fac
    (pullback.lift (pullback.fst p t) (pullback.snd p t ≫ m)
      (by rw [Category.assoc, hfac]; exact pullback.condition))
    (pullback.fst p (Z.fromSpecResidueField _)) (pullback.fst p t) (pullback.lift_fst _ _ _) L hz

/-- A morphism from the spectrum of a field to `Spec R` hitting `x` factors through
`Spec κ(x)`. -/
theorem exists_fac_algebraMap_residueField {R : Type u} [CommRing R] (x : PrimeSpectrum R)
    {K : Type u} [Field K] (t : Spec (.of K) ⟶ Spec (.of R))
    (ht : t.base (IsLocalRing.closedPoint K) = x) :
    ∃ m : Spec (.of K) ⟶ Spec (.of x.asIdeal.ResidueField),
      m ≫ Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)) = t := by
  subst ht
  refine ⟨Spec.map ((Spec (.of R)).descResidueField (Scheme.stalkClosedPointTo t)) ≫
    Spec.map (Scheme.Spec.residueFieldIso (.of R) _).inv, ?_⟩
  rw [Category.assoc, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]

/-- `Spec κ(x) ⟶ Spec R` sends every point to `x`. -/
private theorem base_spec_map_algebraMap_residueField {R : Type u} [CommRing R]
    (x : PrimeSpectrum R) (y : Spec (.of x.asIdeal.ResidueField)) :
    (Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField))).base y = x := by
  rw [Subsingleton.elim y (IsLocalRing.closedPoint _)]
  apply PrimeSpectrum.ext
  change Ideal.comap _ (IsLocalRing.maximalIdeal _) = x.asIdeal
  rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
  exact Ideal.ker_algebraMap_residueField x.asIdeal

variable (H : IsPullback r q fX fY)
  [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX] [GeometricallyIntegral fX]
  [IsProper fY] [Flat fY] [LocallyOfFinitePresentation fY] [GeometricallyIntegral fY]
  (σ : Z ⟶ X) (τ : Z ⟶ Y) (hσ : σ ≫ fX = 𝟙 _) (hτ : τ ≫ fY = 𝟙 _)
  (j₁ : Y ⟶ P) (hj₁r : j₁ ≫ r = fY ≫ σ) (hj₁q : j₁ ≫ q = 𝟙 Y)
  (j₂ : X ⟶ P) (hj₂r : j₂ ≫ r = 𝟙 X) (hj₂q : j₂ ≫ q = fX ≫ τ)
  (L : P.Modules) [Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L]
  (e₁ : Nonempty ((Scheme.Modules.pullback j₁).obj L ≅ Scheme.unitModule Y))
  (e₂ : Nonempty ((Scheme.Modules.pullback j₂).obj L ≅ Scheme.unitModule X))

include H hσ hτ hj₁r hj₁q hj₂r hj₂q e₁ e₂ in
/-- **The openness step of the theorem of the cube.** If `L` is trivial on the fibre of
`P ⟶ Z` over `z`, then it is trivial over the preimage of an affine open neighbourhood of `z`. -/
theorem exists_isAffineOpen_trivial (z : Z)
    (hz : Nonempty ((Scheme.Modules.pullback (pullback.fst (r ≫ fX) (Z.fromSpecResidueField z))).obj
      L ≅ Scheme.unitModule (pullback (r ≫ fX) (Z.fromSpecResidueField z)))) :
    ∃ U : Z.Opens, z ∈ U ∧ IsAffineOpen U ∧
      Nonempty ((Scheme.Modules.pullback ((r ≫ fX) ⁻¹ᵁ U).ι).obj L ≅
        Scheme.unitModule ((r ≫ fX) ⁻¹ᵁ U)) := by
  classical
  -- an affine chart adapted to the two sections
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hzV₀, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  obtain ⟨_, ⟨U', hU', rfl⟩, hσU', hU'V₀⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show σ.base z ∈ fX ⁻¹ᵁ V₀ by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hσ]
      exact hzV₀) (fX ⁻¹ᵁ V₀).isOpen
  obtain ⟨_, ⟨V', hV', rfl⟩, hτV', hV'V₀⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show τ.base z ∈ fY ⁻¹ᵁ V₀ by
      rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, hτ]
      exact hzV₀) (fY ⁻¹ᵁ V₀).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVsub⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show z ∈ V₀ ⊓ σ ⁻¹ᵁ U' ⊓ τ ⁻¹ᵁ V' from ⟨⟨hzV₀, hσU'⟩, hτV'⟩)
      (V₀ ⊓ σ ⁻¹ᵁ U' ⊓ τ ⁻¹ᵁ V').isOpen
  let A : Type u := Γ(Z, V)
  let ι : Spec (.of A) ⟶ Z := hV.fromSpec
  have : IsOpenImmersion ι := hV.isOpenImmersion_fromSpec
  have hιr : Set.range ι.base = V := hV.range_fromSpec
  have hιV : ∀ w, ι.base w ∈ V := fun w => by
    rw [← SetLike.mem_coe, ← hιr]; exact Set.mem_range_self w
  -- the base change to `A`
  set fXA := pullback.snd fX ι
  set fYA := pullback.snd fY ι
  have HA := isPullback_baseChange H ι
  set rA := baseChangeFst H ι
  set qA := baseChangeSnd H ι
  have hrA : rA ≫ fXA = pullback.snd (r ≫ fX) ι := pullback.lift_snd _ _ _
  have hrA' : rA ≫ pullback.fst fX ι = pullback.fst (r ≫ fX) ι ≫ r := pullback.lift_fst _ _ _
  have hqA' : qA ≫ pullback.fst fY ι = pullback.fst (r ≫ fX) ι ≫ q := pullback.lift_fst _ _ _
  have hqA : qA ≫ fYA = pullback.snd (r ≫ fX) ι := pullback.lift_snd _ _ _
  set σA : Spec (.of A) ⟶ pullback fX ι := pullback.lift (ι ≫ σ) (𝟙 _)
    (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  set τA : Spec (.of A) ⟶ pullback fY ι := pullback.lift (ι ≫ τ) (𝟙 _)
    (by rw [Category.assoc, hτ, Category.comp_id, Category.id_comp])
  set j₁A : pullback fY ι ⟶ pullback (r ≫ fX) ι := pullback.lift (pullback.fst fY ι ≫ j₁)
    (pullback.snd fY ι) (by
      rw [Category.assoc, reassoc_of% hj₁r, hσ, Category.comp_id]; exact pullback.condition)
  set j₂A : pullback fX ι ⟶ pullback (r ≫ fX) ι := pullback.lift (pullback.fst fX ι ≫ j₂)
    (pullback.snd fX ι) (by
      rw [Category.assoc, reassoc_of% hj₂r]; exact pullback.condition)
  have hj₁rA : j₁A ≫ rA = fYA ≫ σA := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hrA', pullback.lift_fst_assoc, Category.assoc, hj₁r, Category.assoc,
        pullback.lift_fst, ← Category.assoc, pullback.condition, Category.assoc]
    · rw [Category.assoc, Category.assoc, hrA, pullback.lift_snd, pullback.lift_snd,
        Category.comp_id]
  have hj₁qA : j₁A ≫ qA = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hqA', pullback.lift_fst_assoc, Category.assoc, hj₁q, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, hqA, pullback.lift_snd, Category.id_comp]
  have hj₂rA : j₂A ≫ rA = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hrA', pullback.lift_fst_assoc, Category.assoc, hj₂r, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, hrA, pullback.lift_snd, Category.id_comp]
  have hj₂qA : j₂A ≫ qA = fXA ≫ τA := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hqA', pullback.lift_fst_assoc, Category.assoc, hj₂q, Category.assoc,
        pullback.lift_fst, ← Category.assoc, pullback.condition, Category.assoc]
    · rw [Category.assoc, Category.assoc, hqA, pullback.lift_snd, pullback.lift_snd,
        Category.comp_id]
  set gA := pullback.fst (r ≫ fX) ι
  set LA := (Scheme.Modules.pullback gA).obj L
  have e₁A : Nonempty ((Scheme.Modules.pullback j₁A).obj LA ≅ Scheme.unitModule _) :=
    nonempty_iso_unit_pullback_pullback_of_fac (pullback.fst fY ι) j₁ _ _
      (pullback.lift_fst _ _ _).symm L e₁
  have e₂A : Nonempty ((Scheme.Modules.pullback j₂A).obj LA ≅ Scheme.unitModule _) :=
    nonempty_iso_unit_pullback_pullback_of_fac (pullback.fst fX ι) j₂ _ _
      (pullback.lift_fst _ _ _).symm L e₂
  -- the affine opens containing the sections
  set U₀ := pullback.fst fX ι ⁻¹ᵁ U'
  have hU₀ : IsAffineOpen U₀ := by
    have := Stacks.AlgebraicGeometry.isAffineOpen_inf_preimage_of_isPullback
      (IsPullback.of_hasPullback fX ι) hV₀ hU' (isAffineOpen_top (Spec (.of A))) hU'V₀
      (fun w _ => (hVsub (hιV w)).1.1)
    rwa [Scheme.Hom.preimage_top, inf_top_eq] at this
  set V₁ := pullback.fst fY ι ⁻¹ᵁ V'
  have hV₁ : IsAffineOpen V₁ := by
    have := Stacks.AlgebraicGeometry.isAffineOpen_inf_preimage_of_isPullback
      (IsPullback.of_hasPullback fY ι) hV₀ hV' (isAffineOpen_top (Spec (.of A))) hV'V₀
      (fun w _ => (hVsub (hιV w)).1.1)
    rwa [Scheme.Hom.preimage_top, inf_top_eq] at this
  have hσU₀ : σA ⁻¹ᵁ U₀ = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    show (σA ≫ pullback.fst fX ι).base w ∈ U'
    rw [pullback.lift_fst, Scheme.Hom.comp_apply]
    exact (hVsub (hιV w)).1.2
  have hτV₁ : τA ⁻¹ᵁ V₁ = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    show (τA ≫ pullback.fst fY ι).base w ∈ V'
    rw [pullback.lift_fst, Scheme.Hom.comp_apply]
    exact (hVsub (hιV w)).2
  -- the prime of `A` at `z`, and the fibre over it
  set pz := hV.primeIdealOf ⟨z, hzV⟩
  have hpz : ι.base pz = z := hV.fromSpec_primeIdealOf ⟨z, hzV⟩
  set χ := algebraMap A pz.asIdeal.ResidueField
  set sp : Spec (.of pz.asIdeal.ResidueField) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom χ)
  have hfib := nonempty_iso_unit_fibre_of_residueField (r ≫ fX) L z hz (sp ≫ ι)
    ((congrArg ι.base (base_spec_map_algebraMap_residueField pz _)).trans hpz)
  have e' : Nonempty ((Scheme.Modules.pullback (pullback.fst (rA ≫ fXA) sp)).obj LA ≅
      Scheme.unitModule (pullback (rA ≫ fXA) sp)) :=
    nonempty_iso_unit_pullback_pullback_of_fac
      (pullback.lift (pullback.fst (rA ≫ fXA) sp ≫ gA) (pullback.snd (rA ≫ fXA) sp) (by
        rw [Category.assoc, pullback.condition, ← hrA, ← Category.assoc, pullback.condition,
          Category.assoc]))
      (pullback.fst (r ≫ fX) (sp ≫ ι)) _ _ (pullback.lift_fst _ _ _) L hfib
  -- the openness step over `A`
  obtain ⟨a, ha, s, hs⟩ := exists_basicOpen_nonvanishing HA σA τA (pullback.lift_snd _ _ _)
    (pullback.lift_snd _ _ _) j₁A hj₁rA hj₁qA j₂A hj₂rA hj₂qA LA e₁A.some e₂A.some U₀ hU₀ hσU₀
    V₁ hV₁ hτV₁ pz.asIdeal (IsPullback.of_hasPullback _ _) e'
  -- the neighbourhood of `z`
  let D : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen a
  refine ⟨ι ''ᵁ D, ⟨pz, ha, hpz⟩,
    (IsAffineOpen.Spec_basicOpen (R := .of A) a).image_of_isOpenImmersion ι, ?_⟩
  set W := (r ≫ fX) ⁻¹ᵁ (ι ''ᵁ D)
  have hWrange : Set.range W.ι.base ⊆ Set.range gA.base := by
    rw [Scheme.Opens.range_ι, Scheme.Pullback.range_fst]
    rintro y ⟨w, -, hw⟩
    exact ⟨w, hw⟩
  set k := IsOpenImmersion.lift gA W.ι hWrange
  have hk : k ≫ gA = W.ι := IsOpenImmersion.lift_fac _ _ _
  have hall : k.base ⁻¹' Stacks.Ample.nonvanishingLocus LA s = Set.univ := by
    refine Set.eq_univ_of_forall fun y => hs _ ?_
    obtain ⟨w, hwD, hw⟩ := y.2
    have h1 : (pullback.snd (r ≫ fX) ι ≫ ι).base (k.base y) = (r ≫ fX).base y.1 := by
      rw [← pullback.condition, ← Scheme.Hom.comp_apply, ← Category.assoc, hk]
      rfl
    have hinj : w = (pullback.snd (r ≫ fX) ι).base (k.base y) :=
      ι.isOpenEmbedding.injective (hw.trans h1.symm)
    show (rA ≫ fXA).base (k.base y) ∈ D
    rw [hrA, ← hinj]
    exact hwD
  rw [Stacks.NonvanishingPullback.preimage_nonvanishingLocus k LA s] at hall
  obtain ⟨e⟩ := nonempty_iso_unit_of_nonvanishingLocus_eq_univ _ _ hall
  exact ⟨((Scheme.Modules.pullbackCongr hk).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp k gA).app L).symm ≪≫ e⟩

omit [IsProper fY] [IsProper fX] in
include H in
/-- **The closedness step of the theorem of the cube.** If every neighbourhood of `z` meets the
set of points over a neighbourhood of which `L` is trivial, then `L` is trivial on the fibre
over `z`. -/
theorem nonempty_iso_unit_fibre_of_mem_closure [IsProper fX] [IsProper fY] (z : Z)
    (hz : z ∈ closure {w : Z | ∃ U : Z.Opens, w ∈ U ∧
      Nonempty ((Scheme.Modules.pullback ((r ≫ fX) ⁻¹ᵁ U).ι).obj L ≅
        Scheme.unitModule ((r ≫ fX) ⁻¹ᵁ U))}) :
    Nonempty ((Scheme.Modules.pullback (pullback.fst (r ≫ fX) (Z.fromSpecResidueField z))).obj
      L ≅ Scheme.unitModule (pullback (r ≫ fX) (Z.fromSpecResidueField z))) := by
  classical
  have : IsProper r := MorphismProperty.of_isPullback H.flip inferInstance
  have : Flat r := MorphismProperty.of_isPullback H.flip inferInstance
  have : LocallyOfFinitePresentation r := MorphismProperty.of_isPullback H.flip inferInstance
  have : GeometricallyIntegral (r ≫ fX) := geometricallyIntegral_comp H
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  let A : Type u := Γ(Z, V)
  let ι : Spec (.of A) ⟶ Z := hV.fromSpec
  have : IsOpenImmersion ι := hV.isOpenImmersion_fromSpec
  set h := pullback.snd (r ≫ fX) ι
  set gA := pullback.fst (r ≫ fX) ι
  set LA := (Scheme.Modules.pullback gA).obj L
  set pz := hV.primeIdealOf ⟨z, hzV⟩
  have hpz : ι.base pz = z := hV.fromSpec_primeIdealOf ⟨z, hzV⟩
  -- the closedness step over `A`
  have hA := Stacks.Cube.nonempty_iso_unit_fibre_of_forall_away h LA pz.asIdeal (by
    intro a ha
    have hzD : z ∈ ι ''ᵁ (PrimeSpectrum.basicOpen a : (Spec (.of A)).Opens) := ⟨pz, ha, hpz⟩
    obtain ⟨w, hwD, U, hwU, ⟨eU⟩⟩ := mem_closure_iff.1 hz _ (ι ''ᵁ _).isOpen hzD
    obtain ⟨qw, hqD, hqw⟩ := hwD
    have : qw.asIdeal.IsPrime := qw.isPrime
    refine ⟨qw.asIdeal, qw.isPrime, hqD, ?_⟩
    set sq : Spec (.of qw.asIdeal.ResidueField) ⟶ Spec (.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A qw.asIdeal.ResidueField))
    have hsq := base_spec_map_algebraMap_residueField qw
    have hrange : Set.range (pullback.fst h sq ≫ gA).base ⊆
        Set.range ((r ≫ fX) ⁻¹ᵁ U).ι.base := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (pullback.fst h sq ≫ gA ≫ r ≫ fX).base y ∈ U
      rw [pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hsq]
      convert hwU
      exact hqw
    exact nonempty_iso_unit_pullback_pullback_of_fac (IsOpenImmersion.lift _ _ hrange) _ _ _
      (IsOpenImmersion.lift_fac _ _ _) L ⟨eU⟩)
  -- back to the fibre over `z`
  have hzr : Set.range (Z.fromSpecResidueField z).base ⊆ Set.range ι.base := by
    rw [Scheme.range_fromSpecResidueField, hV.range_fromSpec]
    simpa using hzV
  set t' := IsOpenImmersion.lift ι (Z.fromSpecResidueField z) hzr
  have ht' : t' ≫ ι = Z.fromSpecResidueField z := IsOpenImmersion.lift_fac _ _ _
  have ht'p : ∀ y, t'.base y = pz := by
    intro y
    apply ι.isOpenEmbedding.injective
    show (t' ≫ ι).base y = ι.base pz
    rw [ht', hpz]
    exact Scheme.fromSpecResidueField_apply z y
  obtain ⟨m₀, hm₀⟩ := exists_fac_algebraMap_residueField pz t' (ht'p _)
  set sp := Spec.map (CommRingCat.ofHom (algebraMap A pz.asIdeal.ResidueField))
  let m : Spec (Z.residueField z) ⟶ Spec (.of pz.asIdeal.ResidueField) := m₀
  have hm : m ≫ sp = t' := hm₀
  set kA : pullback (r ≫ fX) (Z.fromSpecResidueField z) ⟶ pullback (r ≫ fX) ι :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t') (by
      rw [Category.assoc, ht']; exact pullback.condition)
  set k : pullback (r ≫ fX) (Z.fromSpecResidueField z) ⟶ pullback h sp :=
    pullback.lift kA (pullback.snd _ _ ≫ m) (by
      rw [Category.assoc, hm]; exact pullback.lift_snd _ _ _)
  have hk : k ≫ pullback.fst h sp ≫ gA = pullback.fst (r ≫ fX) (Z.fromSpecResidueField z) := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  exact nonempty_iso_unit_pullback_of_fac k _ _ hk L
    ⟨((Scheme.Modules.pullbackComp (pullback.fst h sp) gA).app L).symm ≪≫ hA.some⟩

include H hσ hτ hj₁r hj₁q hj₂r hj₂q e₁ e₂ in
/-- **Local triviality in the theorem of the cube.** If `Z` is connected and `L` is trivial on
one fibre of `P ⟶ Z`, then every point of `Z` has an affine open neighbourhood over whose preimage
`L` is trivial: the set of points with such a neighbourhood is open by definition, closed by the
closedness step and the openness step, and nonempty by the openness step. -/
theorem forall_exists_isAffineOpen_trivial [ConnectedSpace Z] (z₀ : Z)
    (hz₀ : Nonempty ((Scheme.Modules.pullback (pullback.fst (r ≫ fX)
      (Z.fromSpecResidueField z₀))).obj L ≅
        Scheme.unitModule (pullback (r ≫ fX) (Z.fromSpecResidueField z₀)))) (z : Z) :
    ∃ U : Z.Opens, z ∈ U ∧ IsAffineOpen U ∧
      Nonempty ((Scheme.Modules.pullback ((r ≫ fX) ⁻¹ᵁ U).ι).obj L ≅
        Scheme.unitModule ((r ≫ fX) ⁻¹ᵁ U)) := by
  have key := exists_isAffineOpen_trivial H σ τ hσ hτ j₁ hj₁r hj₁q j₂ hj₂r hj₂q L e₁ e₂
  set W : Set Z := {w : Z | ∃ U : Z.Opens, w ∈ U ∧
      Nonempty ((Scheme.Modules.pullback ((r ≫ fX) ⁻¹ᵁ U).ι).obj L ≅
        Scheme.unitModule ((r ≫ fX) ⁻¹ᵁ U))}
  have hopen : IsOpen W := isOpen_iff_forall_mem_open.2 fun w ⟨U, hwU, hU⟩ =>
    ⟨U, fun w' hw' => ⟨U, hw', hU⟩, U.isOpen, hwU⟩
  have hclosed : IsClosed W := closure_subset_iff_isClosed.1 fun w hw => by
    obtain ⟨U, hwU, -, hU⟩ := key w (nonempty_iso_unit_fibre_of_mem_closure H L w hw)
    exact ⟨U, hwU, hU⟩
  obtain ⟨U₀, hzU₀, -, hU₀⟩ := key z₀ hz₀
  have hW : W = Set.univ :=
    (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨z₀, U₀, hzU₀, hU₀⟩)
  obtain ⟨U, hzU, hU⟩ : z ∈ W := hW ▸ Set.mem_univ z
  exact key z
    (nonempty_iso_unit_fibre_of_mem_closure H L z (subset_closure ⟨U, hzU, hU⟩))

end Stacks.Cube

end
