module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.AffineAlmostBlowUpFppfCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AlmostBlowUpSheafGluing
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusColimitHSheaf
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty

/-!
# The sheaf `𝒪^{perf} = colim_F 𝒪` on the big fppf site

Let `p` be a prime number and `S` a scheme over `𝔽_p`, and let `(Sch/S)_h` be a big h site
over `S`. The underlying category also carries the fppf topology, which is coarser. Stacks,
Section 0EWS, sets `𝒪^{perf} = colim_F 𝒪`, the colimit in the category of fppf sheaves of rings
of the system

`𝒪 →^F 𝒪 →^F 𝒪 →^F ⋯`

where `F : f ↦ f^p` is the Frobenius endomorphism of the structure sheaf. This file constructs
that colimit and shows it is an h sheaf: it is the sheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)` of global functions
on absolute weak normalizations, with the cocone whose leg at stage `n` sends a function to the
`pⁿ`-th root of its pullback.

## Main definitions

* `AlgebraicGeometry.BigHOver.structureSheafFppf`: the structure sheaf `X ↦ Γ(X, 𝒪_X)`, a sheaf
  of rings for the fppf topology.
* `AlgebraicGeometry.BigHOver.frobeniusFppf`: its Frobenius endomorphism, over `𝔽_p`.
* `AlgebraicGeometry.BigHOver.frobeniusSystemFppf`: the system `𝒪 →^F 𝒪 →^F ⋯` of fppf sheaves
  of rings.
* `AlgebraicGeometry.BigHOver.awnRingSheaf`: the h sheaf of rings `X ↦ Γ(Xᵃʷⁿ, 𝒪)`.
* `AlgebraicGeometry.BigHOver.perfectionCocone`: the cocone on the Frobenius system with vertex
  the fppf sheaf underlying `X ↦ Γ(Xᵃʷⁿ, 𝒪)`.

## Main results

* `AlgebraicGeometry.BigHOver.isSheaf_fppfTopology_iff`: a presheaf of sets is an fppf sheaf
  exactly when it satisfies the sheaf condition for every fppf covering family.
* `AlgebraicGeometry.BigHOver.isColimitPerfectionCocone`: the cocone is a colimit in the
  category of fppf sheaves of rings, so `colim_F 𝒪` is the fppf sheaf underlying the h sheaf
  `X ↦ Γ(Xᵃʷⁿ, 𝒪)`.

## References

* [Stacks Project, Tag 0EWS](https://stacks.math.columbia.edu/tag/0EWS)
* [Stacks Project, Tag 0EVK](https://stacks.math.columbia.edu/tag/0EVK)
* [Stacks Project, Tag 0EVW](https://stacks.math.columbia.edu/tag/0EVW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.Presheaf

variable {C : Type*} [Category* C] (G : Cᵒᵖ ⥤ CommRingCat.{u}) (p : ℕ) [Fact p.Prime]
  (hp : ∀ X, (p : G.obj X) = 0)

/-- **The Frobenius of a presheaf of rings in characteristic `p`.** For a presheaf of commutative
rings in which the prime `p` vanishes, taking `p`-th powers is a map of presheaves of rings. -/
def frobeniusRingHom : G ⟶ G where
  app X := CommRingCat.ofHom (Stacks.Frobenius.primePowerEndomorphism (G.obj X) p (hp X))
  naturality X Y f := by
    ext a
    simp [Stacks.Frobenius.primePowerEndomorphism_apply, map_pow]

/-- The Frobenius of a presheaf of rings raises a section to its `p`-th power. -/
theorem frobeniusRingHom_app_apply (X : Cᵒᵖ) (a : G.obj X) :
    (frobeniusRingHom G p hp).app X a = a ^ p :=
  Stacks.Frobenius.primePowerEndomorphism_apply _ p (hp X) a

end CategoryTheory.Presheaf

namespace AlgebraicGeometry.BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fppf topology on the big h category -/

/-- The fppf precoverage on the big h category over `S` is stable under base change. -/
instance fppfPrecoverage_isStableUnderBaseChange :
    (fppfPrecoverage B S hS).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} {X₀} {X} f hR {Y} g {P} p₁ p₂ h := by
    obtain ⟨E, hE, hEf⟩ := hR
    let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
    have _ : PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := inferInstance
    refine ⟨⟨ι, P, p₁⟩, rfl, ?_⟩
    have hR' : Presieve.ofArrows (fun i ↦ (BigHOver.toScheme B S hS).obj (X i))
        (fun i ↦ (BigHOver.toScheme B S hS).map (f i)) ∈
          Scheme.fppfPrecoverage ((BigHOver.toScheme B S hS).obj X₀) := by
      rwa [PreZeroHypercover.presieve₀_map, hE, Presieve.map_ofArrows] at hEf
    exact Precoverage.mem_coverings_of_isPullback _ hR' _ _ _
      (fun i ↦ (h i).map (BigHOver.toScheme B S hS))

/-- **The fppf sheaf condition, family by family.** A presheaf of sets on the big h category
over `S` is a sheaf for the fppf topology exactly when it satisfies the sheaf condition for
every family of morphisms of the site whose underlying family of morphisms of schemes is an fppf
covering. -/
theorem isSheaf_fppfTopology_iff (F : (BigHOver B S hS)ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf (fppfTopology B S hS) F ↔
      ∀ (X : BigHOver B S hS) (E : PreZeroHypercover.{u + 1} X),
        (E.map (BigHOver.toScheme B S hS)).presieve₀ ∈
          Scheme.fppfPrecoverage ((BigHOver.toScheme B S hS).obj X) →
        Presieve.IsSheafFor F E.presieve₀ := by
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  exact ⟨fun h X E hE ↦ h _ ⟨E, rfl, hE⟩, fun h X R ⟨E, hR, hE⟩ ↦ hR ▸ h X E hE⟩

/-! ### The structure sheaf -/

/-- Global functions on schemes satisfy the sheaf condition for every fppf covering family. -/
theorem isSheafFor_Γ_of_mem_fppfPrecoverage {X : Scheme.{u}} {R : Presieve X}
    (hR : R ∈ Scheme.fppfPrecoverage X) :
    Presieve.IsSheafFor (Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat.{u}) R := by
  let e : yoneda.obj (Spec (CommRingCat.of (MvPolynomial PUnit.{u + 1} (ULift.{u} ℤ)))) ≅
      Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat.{u} :=
    NatIso.ofComponents (fun T ↦ ((AffineSpace.toSpecMvPolyIntEquiv PUnit.{u + 1}).trans
      (Equiv.funUnique _ _)).toIso) (by
        intro T T' f
        ext g
        exact AffineSpace.toSpecMvPolyIntEquiv_comp _ f.unop g _)
  exact Presieve.isSheafFor_iso e <| (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology) _).isSheafFor R
    (Precoverage.generate_mem_toGrothendieck hR)

/-- The presheaf of global functions on the big h category over `S` is a sheaf for the fppf
topology. -/
theorem isSheaf_globalFunctions_fppfTopology :
    Presieve.IsSheaf (fppfTopology B S hS) (globalFunctions B S hS) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  have _ : PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := inferInstance
  rw [isSheaf_fppfTopology_iff]
  intro X E hE
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks (BigHOver.toScheme B S hS)
    (Scheme.Γ.{u} ⋙ CategoryTheory.forget CommRingCat.{u}) E.presieve₀,
    ← PreZeroHypercover.presieve₀_map]
  exact isSheafFor_Γ_of_mem_fppfPrecoverage hE

/-- **The structure sheaf of the big fppf site.** The presheaf `X ↦ Γ(X, 𝒪_X)` of rings on the
big h category over `S`, as a sheaf for the fppf topology. -/
def structureSheafFppf : Sheaf (fppfTopology B S hS) CommRingCat.{u} :=
  ⟨sectionsRingPresheaf B S hS, by
    have _ : ReflectsLimitsOfSize.{u, u + 1} (CategoryTheory.forget CommRingCat.{u}) :=
      { reflectsLimitsOfShape := fun {J} _ =>
        { reflectsLimit := fun {D} =>
          { reflects := fun {c} hc => ⟨isLimit_of_isLimit_forget c hc⟩ } } }
    exact Presheaf.isSheaf_of_isSheaf_comp (fppfTopology B S hS)
      (sectionsRingPresheaf B S hS) (CategoryTheory.forget CommRingCat.{u})
      ((isSheaf_iff_isSheaf_of_type _ _).mpr (isSheaf_globalFunctions_fppfTopology B S hS))⟩

/-- The underlying presheaf of `structureSheafFppf` is `X ↦ Γ(X, 𝒪_X)`. -/
@[simp]
theorem structureSheafFppf_obj :
    (structureSheafFppf B S hS).obj = sectionsRingPresheaf B S hS :=
  rfl

/-! ### Affine objects cover in the fppf topology -/

/-- The family of affine opens of an object of the site has an fppf covering as underlying
family of morphisms of schemes. -/
theorem affineCover_map_mem_fppfPrecoverage (X : BigHOver B S hS) :
    ((preZeroHypercoverOfOpenCover (affineCover X)).map (BigHOver.toScheme B S hS)).presieve₀ ∈
      Scheme.fppfPrecoverage ((BigHOver.toScheme B S hS).obj X) :=
  Scheme.zariskiPrecoverage_le_fppfPrecoverage _ (by
    simpa [preZeroHypercoverOfOpenCover, PreZeroHypercover.presieve₀, PreZeroHypercover.map]
      using (affineCover X).mem₀)

/-- The family of affine opens of an object of the site is an fppf covering family. -/
theorem affineCover_mem_fppfPrecoverage (X : BigHOver B S hS) :
    (preZeroHypercoverOfOpenCover (affineCover X)).presieve₀ ∈ fppfPrecoverage B S hS X :=
  ⟨_, rfl, affineCover_map_mem_fppfPrecoverage B S hS X⟩

/-- The sieve generated by the affine opens of an object of the site covers it in the fppf
topology. -/
theorem generate_affineCover_mem_fppfTopology (X : BigHOver B S hS) :
    Sieve.generate (preZeroHypercoverOfOpenCover (affineCover X)).presieve₀ ∈
      fppfTopology B S hS X :=
  Precoverage.generate_mem_toGrothendieck (affineCover_mem_fppfPrecoverage B S hS X)

variable {B S hS}

/-- Two sections of an fppf sheaf of sets which agree after restriction to every object with
affine underlying scheme are equal. -/
theorem ext_of_isAffine_fppf {T : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (hT : Presieve.IsSheaf (fppfTopology B S hS) T) {X : BigHOver B S hS} {x y : T.obj (op X)}
    (h : ∀ (V : BigHOver B S hS), IsAffine ((BigHOver.toScheme B S hS).obj V) →
      ∀ f : V ⟶ X, T.map f.op x = T.map f.op y) : x = y := by
  refine ((isSheaf_fppfTopology_iff B S hS T).mp hT X _
    (affineCover_map_mem_fppfPrecoverage B S hS X)).isSeparatedFor.ext ?_
  rintro V f ⟨i⟩
  exact h _ (isAffine_affineCover X i) _

/-- A map of presheaves of sets on the big h category over `S` which is injective on every object
with affine underlying scheme is locally injective for the fppf topology. -/
theorem isLocallyInjective_fppf_of_injective_isAffine {P F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (φ : P ⟶ F) (h : ∀ X : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj X) →
      Function.Injective (φ.app (op X))) :
    Presheaf.IsLocallyInjective (fppfTopology B S hS) φ := by
  refine ⟨fun {X} a b hab ↦ ?_⟩
  refine (fppfTopology B S hS).superset_covering ?_
    (generate_affineCover_mem_fppfTopology B S hS X.unop)
  rw [Sieve.generate_le_iff]
  rintro V f ⟨i⟩
  refine h _ (isAffine_affineCover X.unop i) ?_
  change φ.app _ (P.map _ a) = φ.app _ (P.map _ b)
  rw [NatTrans.naturality_apply φ, NatTrans.naturality_apply φ, hab]

/-- A map of presheaves of sets on the big h category over `S` which is surjective on every
object with affine underlying scheme is locally surjective for the fppf topology. -/
theorem isLocallySurjective_fppf_of_surjective_isAffine {P F : (BigHOver B S hS)ᵒᵖ ⥤ Type v}
    (φ : P ⟶ F) (h : ∀ X : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj X) →
      Function.Surjective (φ.app (op X))) :
    Presheaf.IsLocallySurjective (fppfTopology B S hS) φ := by
  refine ⟨fun {X} s ↦ ?_⟩
  refine (fppfTopology B S hS).superset_covering ?_
    (generate_affineCover_mem_fppfTopology B S hS X)
  rw [Sieve.generate_le_iff]
  rintro V f ⟨i⟩
  exact h _ (isAffine_affineCover X i) _

variable (B S hS)

/-! ### The h sheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)` -/

/-- **The h sheaf `𝒪^h`.** Global functions on absolute weak normalizations, as a sheaf of rings
for the h topology on the big h category over `S` (Stacks 0EVU). -/
def awnRingSheaf : Sheaf (BigHOver.topology B S hS) CommRingCat.{u} :=
  ⟨absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS),
    isSheaf_absoluteWeakNormalizationSections B S hS⟩

/-- The underlying presheaf of `awnRingSheaf` is `X ↦ Γ(Xᵃʷⁿ, 𝒪)`. -/
@[simp]
theorem awnRingSheaf_obj :
    (awnRingSheaf B S hS).obj = absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS) :=
  rfl

/-- The fppf sheaf of rings underlying the h sheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)`. -/
def awnRingSheafFppf : Sheaf (fppfTopology B S hS) CommRingCat.{u} :=
  ⟨(awnRingSheaf B S hS).obj,
    (awnRingSheaf B S hS).property.of_le (fppfTopology_le_topology B S hS)⟩

/-- The fppf sheaf `awnRingSheafFppf` has the same underlying presheaf as `awnRingSheaf`. -/
@[simp]
theorem awnRingSheafFppf_obj : (awnRingSheafFppf B S hS).obj = (awnRingSheaf B S hS).obj :=
  rfl

/-! ### Frobenius -/

section Frobenius

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

omit [Fact p.Prime] in
include hSp in
/-- On the big h site over a scheme over `𝔽_p`, the prime `p` vanishes in the global functions on
the absolute weak normalization of every object. -/
theorem natCast_eq_zero_awn (X : (BigHOver B S hS)ᵒᵖ) :
    (p : (awnRingSheaf B S hS).obj.obj X) = 0 := by
  have h := congrArg ((BigHOver.toScheme B S hS).obj X.unop).absoluteWeakNormalizationHom.appTop
    (natCast_eq_zero_of_isInCharacteristic hSp X.unop)
  rwa [map_natCast, map_zero] at h

/-- The Frobenius `f ↦ f^p` of the presheaf of rings `X ↦ Γ(X, 𝒪_X)` over a scheme over `𝔽_p`. -/
def frobeniusSections : sectionsRingPresheaf B S hS ⟶ sectionsRingPresheaf B S hS :=
  Presheaf.frobeniusRingHom (sectionsRingPresheaf B S hS) p
    (fun X ↦ natCast_eq_zero_of_isInCharacteristic hSp X.unop)

/-- The Frobenius of `X ↦ Γ(X, 𝒪_X)` raises a function to its `p`-th power. -/
theorem frobeniusSections_app_apply (X : (BigHOver B S hS)ᵒᵖ)
    (a : (sectionsRingPresheaf B S hS).obj X) :
    (frobeniusSections B S hS p hSp).app X a = a ^ p :=
  Presheaf.frobeniusRingHom_app_apply _ p _ X a

/-- **The Frobenius endomorphism `F : 𝒪 ⟶ 𝒪`, `f ↦ f^p`,** of the structure sheaf of the big fppf
site over a scheme `S` over `𝔽_p`, as a map of sheaves of rings. -/
def frobeniusFppf : structureSheafFppf B S hS ⟶ structureSheafFppf B S hS :=
  ObjectProperty.homMk (frobeniusSections B S hS p hSp)

/-- The underlying map of presheaves of `frobeniusFppf` is `frobeniusSections`. -/
@[simp]
theorem frobeniusFppf_hom : (frobeniusFppf B S hS p hSp).hom = frobeniusSections B S hS p hSp :=
  rfl

/-- **The system `𝒪 →^F 𝒪 →^F 𝒪 →^F ⋯`** of sheaves of rings on the big fppf site over a scheme
over `𝔽_p`, all of whose transition maps are the Frobenius endomorphism. -/
def frobeniusSystemFppf : ℕ ⥤ Sheaf (fppfTopology B S hS) CommRingCat.{u} :=
  Functor.ofSequence (X := fun _ ↦ structureSheafFppf B S hS) (fun _ ↦ frobeniusFppf B S hS p hSp)

/-- Every transition map of the Frobenius system is the Frobenius endomorphism. -/
theorem frobeniusSystemFppf_map_succ (n : ℕ) :
    (frobeniusSystemFppf B S hS p hSp).map (homOfLE n.le_succ) = frobeniusFppf B S hS p hSp :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The Frobenius `f ↦ f^p` of `X ↦ Γ(Xᵃʷⁿ, 𝒪)`, as a map of presheaves of rings. -/
def awnRingFrobenius : (awnRingSheaf B S hS).obj ⟶ (awnRingSheaf B S hS).obj :=
  Presheaf.frobeniusRingHom (awnRingSheaf B S hS).obj p (natCast_eq_zero_awn B S hS p hSp)

/-- Over a scheme over `𝔽_p` the Frobenius of `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is an isomorphism of presheaves
of rings. -/
instance isIso_awnRingFrobenius : IsIso (awnRingFrobenius B S hS p hSp) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have := isIso_awnFrobenius B S hS p hSp
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  have he : ⇑(ConcreteCategory.hom ((awnRingFrobenius B S hS p hSp).app X)) =
      (awnFrobenius B S hS p).app X :=
    funext fun a ↦ (Presheaf.frobeniusRingHom_app_apply _ p _ X a).trans
      (awnFrobenius_app B S hS p X.unop a).symm
  rw [he]
  exact (isIso_iff_bijective _).mp inferInstance

/-- The `p`-th root of a function on the absolute weak normalization, raised to the `p`-th power,
is the function. -/
theorem inv_awnRingFrobenius_app_apply_pow (X : (BigHOver B S hS)ᵒᵖ)
    (a : (awnRingSheaf B S hS).obj.obj X) :
    ((inv (awnRingFrobenius B S hS p hSp)).app X a) ^ p = a := by
  rw [← Presheaf.frobeniusRingHom_app_apply _ p (natCast_eq_zero_awn B S hS p hSp)]
  change ((inv (awnRingFrobenius B S hS p hSp)).app X ≫ (awnRingFrobenius B S hS p hSp).app X) a = a
  rw [← NatTrans.comp_app, IsIso.inv_hom_id, NatTrans.id_app, CommRingCat.id_apply]

/-- **The stage maps of the Frobenius colimit.** The map of presheaves of rings from the structure
sheaf to `X ↦ Γ(Xᵃʷⁿ, 𝒪)` at stage `n`, sending a function to the `pⁿ`-th root of its pullback to
the absolute weak normalization. -/
def perfectionStage : ℕ → (sectionsRingPresheaf B S hS ⟶ (awnRingSheaf B S hS).obj)
  | 0 => absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS)
  | n + 1 => perfectionStage n ≫ inv (awnRingFrobenius B S hS p hSp)

/-- The stage maps of presheaves of rings have the stage maps of
`AlgebraicGeometry.BigHOver.awnCocone` as underlying maps of sets. -/
theorem perfectionStage_app_apply (n : ℕ) (X : (BigHOver B S hS)ᵒᵖ)
    (a : (sectionsRingPresheaf B S hS).obj X) :
    (perfectionStage B S hS p hSp n).app X a = awnStageFun B S hS p hSp n X.unop a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have := isIso_awnFrobenius B S hS p hSp
    apply ((isIso_iff_bijective ((awnFrobenius B S hS p).app X)).mp inferInstance).1
    change ((inv (awnRingFrobenius B S hS p hSp)).app X
        ((perfectionStage B S hS p hSp n).app X a)) ^ p =
      (awnStageFun B S hS p hSp (n + 1) X.unop a) ^ p
    rw [inv_awnRingFrobenius_app_apply_pow, ih]
    exact (awnFrobeniusInv_pow B S hS p hSp X.unop _).symm

/-- The stage maps are compatible with the Frobenius transition maps. -/
theorem frobeniusSections_comp_perfectionStage (n : ℕ) :
    frobeniusSections B S hS p hSp ≫ perfectionStage B S hS p hSp (n + 1) =
      perfectionStage B S hS p hSp n := by
  ext X a
  change (perfectionStage B S hS p hSp (n + 1)).app X
      ((frobeniusSections B S hS p hSp).app X a) = (perfectionStage B S hS p hSp n).app X a
  rw [perfectionStage_app_apply, perfectionStage_app_apply, frobeniusSections_app_apply]
  exact congrArg (fun φ : globalFunctions B S hS ⟶ awnSections B S hS ↦ φ.app X a)
    (frobeniusSectionsHom_comp_awnStage B S hS p hSp n)

/-- **The cocone exhibiting `colim_F 𝒪`.** The cocone on the Frobenius system of fppf sheaves of
rings with vertex the fppf sheaf underlying `X ↦ Γ(Xᵃʷⁿ, 𝒪)`, whose leg at stage `n` sends a
function to the `pⁿ`-th root of its pullback to the absolute weak normalization. -/
def perfectionCocone : Cocone (frobeniusSystemFppf B S hS p hSp) where
  pt := awnRingSheafFppf B S hS
  ι := NatTrans.ofSequence (fun n ↦ ObjectProperty.homMk (perfectionStage B S hS p hSp n))
    (fun n ↦ by
      rw [frobeniusSystemFppf_map_succ]
      exact Sheaf.hom_ext
        ((frobeniusSections_comp_perfectionStage B S hS p hSp n).trans (Category.comp_id _).symm))

/-- The leg of `perfectionCocone` at stage `n` has underlying map of presheaves
`perfectionStage n`. -/
@[simp]
theorem perfectionCocone_ι_app_hom (n : ℕ) :
    ((perfectionCocone B S hS p hSp).ι.app n).hom = perfectionStage B S hS p hSp n :=
  rfl

/-! ### The cocone is a colimit -/

/-- Over an object with affine underlying scheme, two global functions on the absolute weak
normalization are the stage `n` images of two global functions, for a common `n`. -/
theorem exists_awnStageFun_eq_pair (X : BigHOver B S hS)
    (hX : IsAffine ((BigHOver.toScheme B S hS).obj X))
    (x y : Γ(((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalization, ⊤)) :
    ∃ (n : ℕ) (a b : Γ((BigHOver.toScheme B S hS).obj X, ⊤)),
      awnStageFun B S hS p hSp n X a = x ∧ awnStageFun B S hS p hSp n X b = y := by
  obtain ⟨x', hx'⟩ := (bijective_awnComparison_app B S hS p hSp X).2 x
  obtain ⟨y', hy'⟩ := (bijective_awnComparison_app B S hS p hSp X).2 y
  obtain ⟨n, a, rfl⟩ := exists_colimitStage_eq B S hS p X x'
  obtain ⟨m, b, rfl⟩ := exists_colimitStage_eq B S hS p X y'
  refine ⟨n + m, a ^ p ^ m, b ^ p ^ n, ?_, ?_⟩
  · rw [← awnComparison_colimitStage, ← colimitStage_add, ← hx']
  · rw [← awnComparison_colimitStage, Nat.add_comm, ← colimitStage_add, ← hy']

/-- The stage maps are additive. -/
theorem awnStageFun_add (n : ℕ) (X : BigHOver B S hS)
    (a b : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    awnStageFun B S hS p hSp n X (a + b) =
      awnStageFun B S hS p hSp n X a + awnStageFun B S hS p hSp n X b :=
  (perfectionStage_app_apply B S hS p hSp n (op X) (a + b)).symm.trans
    ((map_add ((perfectionStage B S hS p hSp n).app (op X)).hom a b).trans
      (congrArg₂ (· + ·) (perfectionStage_app_apply B S hS p hSp n (op X) a)
        (perfectionStage_app_apply B S hS p hSp n (op X) b)))

/-- The stage maps are multiplicative. -/
theorem awnStageFun_mul (n : ℕ) (X : BigHOver B S hS)
    (a b : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    awnStageFun B S hS p hSp n X (a * b) =
      awnStageFun B S hS p hSp n X a * awnStageFun B S hS p hSp n X b :=
  (perfectionStage_app_apply B S hS p hSp n (op X) (a * b)).symm.trans
    ((map_mul ((perfectionStage B S hS p hSp n).app (op X)).hom a b).trans
      (congrArg₂ (· * ·) (perfectionStage_app_apply B S hS p hSp n (op X) a)
        (perfectionStage_app_apply B S hS p hSp n (op X) b)))

/-- The stage maps send `1` to `1`. -/
theorem awnStageFun_one (n : ℕ) (X : BigHOver B S hS) :
    awnStageFun B S hS p hSp n X 1 = 1 :=
  (perfectionStage_app_apply B S hS p hSp n (op X) 1).symm.trans
    (map_one ((perfectionStage B S hS p hSp n).app (op X)).hom)

/-- The legs of a cocone on the Frobenius system are compatible with taking `p`-th powers. -/
theorem frobeniusSystemFppf_cocone_ι_succ_app_pow (s : Cocone (frobeniusSystemFppf B S hS p hSp))
    (n : ℕ) (X : (BigHOver B S hS)ᵒᵖ) (a : (sectionsRingPresheaf B S hS).obj X) :
    (s.ι.app (n + 1)).hom.app X (a ^ p) = (s.ι.app n).hom.app X a := by
  have h := congrArg (fun φ ↦ φ.hom.app X a) (s.w (homOfLE n.le_succ))
  simp only [frobeniusSystemFppf_map_succ] at h
  rw [← h, ← frobeniusSections_app_apply B S hS p hSp]
  rfl

/-- Every cocone of fppf sheaves of rings on the Frobenius system induces a unique map of
presheaves of sets from `X ↦ Γ(Xᵃʷⁿ, 𝒪)` to its vertex which is compatible with the stage maps. -/
theorem existsUnique_awnSections_hom (s : Cocone (frobeniusSystemFppf B S hS p hSp)) :
    ∃! χ : awnSections B S hS ⟶ s.pt.obj ⋙ CategoryTheory.forget CommRingCat.{u},
      ∀ (n : ℕ) (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)),
        χ.app (op X) (awnStageFun B S hS p hSp n X a) = (s.ι.app n).hom.app (op X) a := by
  have := CommRingCat.adj.rightAdjoint_preservesLimits.{u, u + 1}
  let T : (BigHOver B S hS)ᵒᵖ ⥤ Type u := s.pt.obj ⋙ CategoryTheory.forget CommRingCat.{u}
  have hT : Presheaf.IsSheaf (fppfTopology B S hS) T :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget CommRingCat.{u}) s.pt.property
  let c : Cocone (frobeniusSectionsSequence B S hS p) :=
    { pt := T
      ι := NatTrans.ofSequence
        (fun n ↦ Functor.whiskerRight (s.ι.app n).hom (CategoryTheory.forget CommRingCat.{u}))
        (fun n ↦ by
          rw [frobeniusSectionsSequence_map_succ]
          ext X a
          exact frobeniusSystemFppf_cocone_ι_succ_app_pow B S hS p hSp s n X a) }
  let ψ : frobeniusColimitSections B S hS p ⟶ T := colimit.desc _ c
  have hψ (n : ℕ) (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
      ψ.app (op X) (colimitStage B S hS p n X a) = (s.ι.app n).hom.app (op X) a :=
    ConcreteCategory.congr_hom (congr_app (colimit.ι_desc c n) (op X)) a
  have := isLocallyInjective_fppf_of_injective_isAffine (awnComparison B S hS p hSp)
    (fun X _ ↦ (bijective_awnComparison_app B S hS p hSp X).1)
  have := isLocallySurjective_fppf_of_surjective_isAffine (awnComparison B S hS p hSp)
    (fun X _ ↦ (bijective_awnComparison_app B S hS p hSp X).2)
  obtain ⟨χ, hχ, hχu⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective (fppfTopology B S hS)
    (awnComparison B S hS p hSp) ψ hT
  refine ⟨χ, fun n X a ↦ ?_, fun χ' h' ↦ hχu _ (colimit.hom_ext fun n ↦ ?_)⟩
  · rw [← awnComparison_colimitStage, ← hψ, ← hχ]
    rfl
  · ext X a
    change χ'.app X ((awnComparison B S hS p hSp).app X (colimitStage B S hS p n X.unop a)) =
      ψ.app X (colimitStage B S hS p n X.unop a)
    exact (congrArg (χ'.app X) (awnComparison_colimitStage B S hS p hSp n X.unop a)).trans
      ((h' n X.unop a).trans (hψ n X.unop a).symm)

/-- A binary operation on rings, compatible with ring homomorphisms, that is respected by a map
of presheaves from `X ↦ Γ(Xᵃʷⁿ, 𝒪)` to an fppf sheaf of rings over every object with affine
underlying scheme is respected over every object. -/
private theorem awnSections_hom_map_op_of_isAffine
    (μ : ∀ {R : Type u} [CommRing R], R → R → R)
    (hμ : ∀ {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R') (x y : R),
      φ (μ x y) = μ (φ x) (φ y))
    {G : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u}}
    (hG : Presieve.IsSheaf (fppfTopology B S hS) (G ⋙ CategoryTheory.forget CommRingCat.{u}))
    (χ : awnSections B S hS ⟶ G ⋙ CategoryTheory.forget CommRingCat.{u})
    (h : ∀ V : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj V) →
      ∀ x y : Γ(((BigHOver.toScheme B S hS).obj V).absoluteWeakNormalization, ⊤),
        χ.app (op V) (μ x y) = μ (χ.app (op V) x) (χ.app (op V) y))
    (X : (BigHOver B S hS)ᵒᵖ) (x y : (awnRingSheaf B S hS).obj.obj X) :
    χ.app X (μ x y) = μ (χ.app X x) (χ.app X y) := by
  refine ext_of_isAffine_fppf hG (fun V hV f ↦ ?_)
  calc (G ⋙ CategoryTheory.forget CommRingCat.{u}).map f.op (χ.app X (μ x y))
      = χ.app (op V) (μ ((awnRingSheaf B S hS).obj.map f.op x)
          ((awnRingSheaf B S hS).obj.map f.op y)) :=
        (NatTrans.naturality_apply χ f.op _).symm.trans
          (congrArg _ (hμ ((awnRingSheaf B S hS).obj.map f.op).hom x y))
    _ = _ := (h V hV _ _).trans (congrArg₂ μ (NatTrans.naturality_apply χ f.op x)
          (NatTrans.naturality_apply χ f.op y))
    _ = _ := (hμ (G.map f.op).hom _ _).symm

variable {B S hS} in
/-- A map of presheaves of sets from `X ↦ Γ(Xᵃʷⁿ, 𝒪)` to an fppf sheaf of rings which is additive
over every object with affine underlying scheme is additive. -/
theorem awnSections_hom_map_add_of_isAffine {G : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u}}
    (hG : Presieve.IsSheaf (fppfTopology B S hS) (G ⋙ CategoryTheory.forget CommRingCat.{u}))
    (χ : awnSections B S hS ⟶ G ⋙ CategoryTheory.forget CommRingCat.{u})
    (h : ∀ V : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj V) →
      ∀ x y : Γ(((BigHOver.toScheme B S hS).obj V).absoluteWeakNormalization, ⊤),
        χ.app (op V) (x + y) = χ.app (op V) x + χ.app (op V) y)
    (X : (BigHOver B S hS)ᵒᵖ) (x y : (awnRingSheaf B S hS).obj.obj X) :
    χ.app X (x + y) = χ.app X x + χ.app X y :=
  awnSections_hom_map_op_of_isAffine B S hS (· + ·) (fun φ x y ↦ map_add φ x y) hG χ h X x y

variable {B S hS} in
/-- A map of presheaves of sets from `X ↦ Γ(Xᵃʷⁿ, 𝒪)` to an fppf sheaf of rings which is
multiplicative over every object with affine underlying scheme is multiplicative. -/
theorem awnSections_hom_map_mul_of_isAffine {G : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u}}
    (hG : Presieve.IsSheaf (fppfTopology B S hS) (G ⋙ CategoryTheory.forget CommRingCat.{u}))
    (χ : awnSections B S hS ⟶ G ⋙ CategoryTheory.forget CommRingCat.{u})
    (h : ∀ V : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj V) →
      ∀ x y : Γ(((BigHOver.toScheme B S hS).obj V).absoluteWeakNormalization, ⊤),
        χ.app (op V) (x * y) = χ.app (op V) x * χ.app (op V) y)
    (X : (BigHOver B S hS)ᵒᵖ) (x y : (awnRingSheaf B S hS).obj.obj X) :
    χ.app X (x * y) = χ.app X x * χ.app X y :=
  awnSections_hom_map_op_of_isAffine B S hS (· * ·) (fun φ x y ↦ map_mul φ x y) hG χ h X x y

/-- A map of presheaves of sets from `X ↦ Γ(Xᵃʷⁿ, 𝒪)` to the vertex of a cocone on the Frobenius
system which is compatible with the stage maps is additive over objects with affine underlying
scheme. -/
theorem awnSections_hom_map_add_of_isAffine_of_stage
    (s : Cocone (frobeniusSystemFppf B S hS p hSp))
    (χ : awnSections B S hS ⟶ s.pt.obj ⋙ CategoryTheory.forget CommRingCat.{u})
    (hχ : ∀ (n : ℕ) (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)),
      χ.app (op X) (awnStageFun B S hS p hSp n X a) = (s.ι.app n).hom.app (op X) a)
    (X : BigHOver B S hS) (hX : IsAffine ((BigHOver.toScheme B S hS).obj X))
    (x y : Γ(((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalization, ⊤)) :
    χ.app (op X) (x + y) = χ.app (op X) x + χ.app (op X) y := by
  obtain ⟨n, a, b, rfl, rfl⟩ := exists_awnStageFun_eq_pair B S hS p hSp X hX x y
  rw [← awnStageFun_add, hχ, hχ, hχ]
  exact map_add ((s.ι.app n).hom.app (op X)).hom a b

/-- A map of presheaves of sets from `X ↦ Γ(Xᵃʷⁿ, 𝒪)` to the vertex of a cocone on the Frobenius
system which is compatible with the stage maps is multiplicative over objects with affine
underlying scheme. -/
theorem awnSections_hom_map_mul_of_isAffine_of_stage
    (s : Cocone (frobeniusSystemFppf B S hS p hSp))
    (χ : awnSections B S hS ⟶ s.pt.obj ⋙ CategoryTheory.forget CommRingCat.{u})
    (hχ : ∀ (n : ℕ) (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)),
      χ.app (op X) (awnStageFun B S hS p hSp n X a) = (s.ι.app n).hom.app (op X) a)
    (X : BigHOver B S hS) (hX : IsAffine ((BigHOver.toScheme B S hS).obj X))
    (x y : Γ(((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalization, ⊤)) :
    χ.app (op X) (x * y) = χ.app (op X) x * χ.app (op X) y := by
  obtain ⟨n, a, b, rfl, rfl⟩ := exists_awnStageFun_eq_pair B S hS p hSp X hX x y
  rw [← awnStageFun_mul, hχ, hχ, hχ]
  exact map_mul ((s.ι.app n).hom.app (op X)).hom a b

/-- **`colim_F 𝒪` exists and is the fppf sheaf underlying `X ↦ Γ(Xᵃʷⁿ, 𝒪)`.** Every cocone of
fppf sheaves of rings on the Frobenius system factors uniquely through the cocone
`AlgebraicGeometry.BigHOver.perfectionCocone`. -/
theorem existsUnique_perfectionCocone_desc (s : Cocone (frobeniusSystemFppf B S hS p hSp)) :
    ∃! d : (perfectionCocone B S hS p hSp).pt ⟶ s.pt,
      ∀ n, (perfectionCocone B S hS p hSp).ι.app n ≫ d = s.ι.app n := by
  have := CommRingCat.adj.rightAdjoint_preservesLimits.{u, u + 1}
  have hT : Presieve.IsSheaf (fppfTopology B S hS)
      (s.pt.obj ⋙ CategoryTheory.forget CommRingCat.{u}) := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (CategoryTheory.forget CommRingCat.{u}) s.pt.property)
  obtain ⟨χ, hkey, hχu⟩ := existsUnique_awnSections_hom B S hS p hSp s
  have hone (X : BigHOver B S hS) : χ.app (op X) 1 = 1 :=
    (congrArg (χ.app (op X)) (awnStageFun_one B S hS p hSp 0 X).symm).trans
      ((hkey 0 X 1).trans (map_one ((s.ι.app 0).hom.app (op X)).hom))
  have hadd := awnSections_hom_map_add_of_isAffine (G := s.pt.obj) hT χ
    (awnSections_hom_map_add_of_isAffine_of_stage B S hS p hSp s χ hkey)
  have hmul := awnSections_hom_map_mul_of_isAffine (G := s.pt.obj) hT χ
    (awnSections_hom_map_mul_of_isAffine_of_stage B S hS p hSp s χ hkey)
  have hzero (X : (BigHOver B S hS)ᵒᵖ) : χ.app X 0 = 0 := by
    have h := hadd X 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  let d : (perfectionCocone B S hS p hSp).pt ⟶ s.pt := ObjectProperty.homMk
    { app X := CommRingCat.ofHom
        { toFun := χ.app X
          map_one' := hone X.unop
          map_mul' := hmul X
          map_zero' := hzero X
          map_add' := hadd X }
      naturality X Y f := by
        ext x
        exact NatTrans.naturality_apply χ f x }
  have hd (n : ℕ) : (perfectionCocone B S hS p hSp).ι.app n ≫ d = s.ι.app n := by
    refine Sheaf.hom_ext ?_
    ext X a
    exact (congrArg (χ.app X) (perfectionStage_app_apply B S hS p hSp n X a)).trans
      (hkey n X.unop a)
  refine ⟨d, hd, fun d' hd' ↦ Sheaf.hom_ext ?_⟩
  have hd'χ : Functor.whiskerRight d'.hom (CategoryTheory.forget CommRingCat.{u}) = χ :=
    hχu _ fun n X a ↦ (congrArg (d'.hom.app (op X))
      (perfectionStage_app_apply B S hS p hSp n (op X) a).symm).trans
        (congrArg (fun φ ↦ φ.hom.app (op X) a) (hd' n))
  ext X x
  exact congrArg (fun φ ↦ φ.app X x) hd'χ

/-- **`𝒪^{perf} = colim_F 𝒪`.** On the big fppf site over a scheme `S` over `𝔽_p`, the colimit of
the system `𝒪 →^F 𝒪 →^F ⋯` in the category of sheaves of rings is the fppf sheaf underlying the
h sheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)`, the leg at stage `n` sending a function to the `pⁿ`-th root of its
pullback to the absolute weak normalization. -/
def isColimitPerfectionCocone : IsColimit (perfectionCocone B S hS p hSp) where
  desc s := (existsUnique_perfectionCocone_desc B S hS p hSp s).exists.choose
  fac s := (existsUnique_perfectionCocone_desc B S hS p hSp s).exists.choose_spec
  uniq s _m hm := (existsUnique_perfectionCocone_desc B S hS p hSp s).unique hm
    (existsUnique_perfectionCocone_desc B S hS p hSp s).exists.choose_spec

end Frobenius

end AlgebraicGeometry.BigHOver
