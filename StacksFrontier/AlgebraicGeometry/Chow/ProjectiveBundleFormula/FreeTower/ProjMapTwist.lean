module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.Hyperplane
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Epi
public import StacksFrontier.AlgebraicGeometry.ProjDegreeOneTriv.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# The twist comparison of `Proj.map` into projective space

Let `φ : ℤ[T₀, …, Tₙ] →+*ᵍ ℬ` be a homomorphism of graded rings such that the images `φ(Tᵢ)`
generate the irrelevant ideal of `ℬ`, so that `Proj.map φ : Proj ℬ ⟶ ℙⁿ_ℤ` is defined
everywhere. The canonical comparison `θ : (Proj.map φ)^*𝒪(1) ⟶ 𝒪_{Proj ℬ}(1)` of
`Stacks.ProjTwistComparison.twistMap` carries the pulled-back coordinate `Tᵢ` to the section of
`𝒪(1)` attached to `φ(Tᵢ)`, and it is an isomorphism of invertible sheaves. So the pullback of
`(𝒪(1), (T₀, …, Tₙ))` along `Proj.map φ` is `(𝒪(1), (φ(T₀), …, φ(Tₙ)))`.

An invertible module with `n + 1` global sections which is identified with the tautological pair
of a morphism `g` to `ℙⁿ_ℤ` on an open cover is the pullback of `𝒪(1)` along `g`.

## Main results

* `Stacks.Chow.FreeTower.twistMap_degreeSection`: `θ` carries the pullback of the section
  attached to `a` to the section attached to `φ a`.
* `Stacks.Chow.FreeTower.isIso_twistMap_of_cover`: `θ` is an isomorphism.
* `Stacks.Chow.FreeTower.projMapTwistIso`: the isomorphism `(Proj.map φ)^*𝒪(1) ≅ 𝒪(1)`, and
  `Stacks.Chow.FreeTower.projMapTwistIso_pullbackCoordSection`: it carries the pullback of `Tᵢ`
  to the section attached to `φ(Tᵢ)`.
* `Stacks.Chow.FreeTower.exists_iso_pullback_of_isTautologicalOn`: local identifications with the
  tautological pair give a global one.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf degreeSection)
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.ProjectiveSpaceModuli Stacks.ProjectiveFromSections
open Stacks.AmpleProjectiveImmersion Stacks.TwistPullbackPinned Stacks.SectionsToProjectiveSpace

universe u

namespace Stacks.Chow.FreeTower

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- The pullback of a global section is the value of the unit of the pullback--pushforward
adjunction at it. -/
theorem pullbackGlobalSections_eq_unitSection {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    (s : Γ(F, ⊤)) :
    pullbackGlobalSections f F s =
      Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection f F ⊤ s := by
  show ((Scheme.Modules.pullback f).obj F).presheaf.map
      (eqToHom (by simp : (⊤ : X.Opens) = f ⁻¹ᵁ ⊤)).op
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) ⊤ s) = _
  exact Functor.map_id_apply _ _ _

section General

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)

/-- The comparison `(Proj.map φ)^*𝒪(1) ⟶ 𝒪(1)` carries the pullback of the section attached to
`a ∈ 𝒜₁` to the section attached to `φ a`. -/
theorem twistMap_degreeSection (a : 𝒜 1) :
    (Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)).val.app (op ⊤)
      (pullbackGlobalSections (AlgebraicGeometry.Proj.map φ hφ)
        (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) (degreeSection 𝒜 1 a)) =
      degreeSection ℬ 1 ⟨φ a, φ.map_mem a.2⟩ := by
  refine (congrArg (CategoryTheory.ConcreteCategory.hom
    ((Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)).val.app (op ⊤)))
    (pullbackGlobalSections_eq_unitSection (AlgebraicGeometry.Proj.map φ hφ)
      (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) (degreeSection 𝒜 1 a))).trans ?_
  refine (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.app_homEquiv_symm
    (AlgebraicGeometry.Proj.map φ hφ)
    (Stacks.ProjTwistComparison.pushforwardTwistMap φ hφ ((1 : ℕ) : ℤ)) ⊤ _).trans ?_
  refine Subtype.ext (funext fun y => ?_)
  show Stacks.ProjTwistComparison.fibreMap φ hφ y.1 ((degreeSection 𝒜 1 a).1 ⟨_, trivial⟩) = _
  rw [degreeSection_apply]
  refine (Stacks.ProjTwistComparison.fibreMap_mk φ hφ y.1 (a : A) 1).trans ?_
  refine Eq.trans ?_ (degreeSection_apply ℬ 1 ⟨φ a, φ.map_mem a.2⟩ ⟨y.1, trivial⟩).symm
  congr 1
  exact Subtype.ext (map_one φ)


/-- The twist comparison `(Proj.map φ)^*𝒪(1) ⟶ 𝒪(1)` is an epimorphism as soon as the standard
opens of the images of degree-one elements cover `Proj ℬ`. -/
theorem epi_twistMap_of_cover
    (hcov : ∀ x : AlgebraicGeometry.Proj ℬ, ∃ a : 𝒜 1,
      x ∈ AlgebraicGeometry.Proj.basicOpen ℬ (φ a)) :
    Epi (Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)) := by
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun U t x hx => ?_
  obtain ⟨a, ha⟩ := hcov x
  set V : (AlgebraicGeometry.Proj ℬ).Opens := U ⊓ AlgebraicGeometry.Proj.basicOpen ℬ (φ a)
  have hVb : V ≤ ProjectiveSpectrum.basicOpen ℬ (φ a) := fun _ h => h.2
  have hVU : V ≤ U := inf_le_left
  obtain ⟨r, hr⟩ := (Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection
    ℬ (φ.map_mem a.2) hVb).2 ((twistingSheaf ℬ ((1 : ℕ) : ℤ)).val.map (homOfLE hVU).op t)
  set M := (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).obj
    (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))
  set s₀ := pullbackGlobalSections (AlgebraicGeometry.Proj.map φ hφ)
    (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) (degreeSection 𝒜 1 a)
  refine ⟨V, hVU, ⟨hx, ha⟩, (M.smul r).asHom.hom (M.val.map (homOfLE (le_top : V ≤ ⊤)).op s₀), ?_⟩
  refine (Stacks.AlgebraicGeometry.RelativeProjDegreeOne.app_smul_map
    (Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)) (le_top : V ≤ ⊤) s₀ r).trans ?_
  rwa [twistMap_degreeSection]

/-- The twist comparison of `Proj.map φ` is an isomorphism when the standard opens of the images
of degree-one elements cover `Proj ℬ` and `𝒪_{Proj ℬ}(1)` and `𝒪_{Proj 𝒜}(1)` are invertible. -/
theorem isIso_twistMap_of_cover
    [AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj ℬ).presheaf
      (AlgebraicGeometry.Proj ℬ).ringCatSheaf.2 (twistingSheaf ℬ ((1 : ℕ) : ℤ))]
    [AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj 𝒜).presheaf
      (AlgebraicGeometry.Proj 𝒜).ringCatSheaf.2 (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))]
    (hcov : ∀ x : AlgebraicGeometry.Proj ℬ, ∃ a : 𝒜 1,
      x ∈ AlgebraicGeometry.Proj.basicOpen ℬ (φ a)) :
    IsIso (Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ)) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj ℬ).presheaf
      (AlgebraicGeometry.Proj ℬ).ringCatSheaf.2
      ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.map φ hφ)).obj
        (twistingSheaf 𝒜 ((1 : ℕ) : ℤ))) :=
    @Stacks.Divisors.pullback_isInvertible _ _ (AlgebraicGeometry.Proj.map φ hφ)
      (twistingSheaf 𝒜 ((1 : ℕ) : ℤ)) ‹_›
  Stacks.AlgebraicGeometry.ProjTwistMono.isIso_of_epi_of_isInvertible _
    (epi_twistMap_of_cover φ hφ hcov)

end General


/-! ### The tautological pair of `Proj.map` into projective space -/

section Coord

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable {B τ : Type u} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {ℬ : ℕ → τ}
  [GradedRing ℬ] {m : ℕ} (φ : coordGrading.{u} m →+*ᵍ ℬ)
  (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant (coordGrading.{u} m)).map φ)

/-- `Proj.map φ`, as a morphism to the integral model of projective space. -/
abbrev projMap : AlgebraicGeometry.Proj ℬ ⟶ projectiveSpaceAtUniverse.{u} m :=
  AlgebraicGeometry.Proj.map φ hφ

include hφ in
/-- The standard opens of the images of the coordinates cover `Proj ℬ`. -/
theorem exists_mem_basicOpen_map_X (x : AlgebraicGeometry.Proj ℬ) :
    ∃ i : Fin (m + 1), x ∈ AlgebraicGeometry.Proj.basicOpen ℬ (φ (MvPolynomial.X i)) := by
  have hint : ⨆ i : Fin (m + 1),
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} m) (MvPolynomial.X i) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ _
      (AlgebraicGeometry.projectiveSpaceOver.irrelevant_coordGrading_le_span_X m)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hint.ge
    (show (projMap φ hφ).base x ∈
      (⊤ : (projectiveSpaceAtUniverse.{u} m).Opens) from trivial))
  exact ⟨i, hi⟩

variable [AlgebraicGeometry.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj ℬ).presheaf
  (AlgebraicGeometry.Proj ℬ).ringCatSheaf.2 (twistingSheaf ℬ ((1 : ℕ) : ℤ))]

/-- The pullback of `𝒪(1)` along `Proj.map φ` is `𝒪(1)`. -/
def projMapTwistIso :
    (Scheme.Modules.pullback (projMap φ hφ)).obj
        (twistingSheafAtUniverse.{u} m) ≅ twistingSheaf ℬ ((1 : ℕ) : ℤ) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (coordGrading.{u} m)).presheaf
      (AlgebraicGeometry.Proj (coordGrading.{u} m)).ringCatSheaf.2
      (twistingSheaf (coordGrading.{u} m) ((1 : ℕ) : ℤ)) :=
    isInvertible_twistingSheafAtUniverse m
  have := isIso_twistMap_of_cover φ hφ fun x => by
    obtain ⟨i, hi⟩ := exists_mem_basicOpen_map_X φ hφ x
    exact ⟨⟨MvPolynomial.X i, X_mem_coordGrading_one i⟩, hi⟩
  asIso (Stacks.ProjTwistComparison.twistMap φ hφ ((1 : ℕ) : ℤ))

/-- Under `Stacks.Chow.FreeTower.projMapTwistIso`, the pullback of `Tᵢ` along `Proj.map φ` is the
section attached to `φ(Tᵢ)`. -/
theorem projMapTwistIso_pullbackCoordSection (i : Fin (m + 1)) :
    Scheme.Modules.Hom.app (projMapTwistIso φ hφ).hom ⊤
        (pullbackCoordSection (projMap φ hφ) i) =
      degreeSection ℬ 1 ⟨φ (MvPolynomial.X i), φ.map_mem (X_mem_coordGrading_one i)⟩ :=
  twistMap_degreeSection φ hφ ⟨MvPolynomial.X i, X_mem_coordGrading_one i⟩

end Coord

/-! ### From local identifications to a global one -/

section LocalToGlobal

variable {P : Scheme.{u}} {n : ℕ} (L : P.Modules) [Stacks.Ample.IsInvertibleModule P L]
  (s : Fin (n + 1) → Γ(L, ⊤)) (g : P ⟶ projectiveSpaceAtUniverse.{u} n)

/-- `L` with the sections `s` is identified with the tautological pair of `g` after pullback
along `c`. -/
def IsTautologicalOn {Y : Scheme.{u}} (c : Y ⟶ P) : Prop :=
  ∃ δ : (Scheme.Modules.pullback c).obj L ≅
      (Scheme.Modules.pullback (c ≫ g)).obj (twistingSheafAtUniverse.{u} n),
    ∀ i, Scheme.Modules.Hom.app δ.hom ⊤ (pullbackGlobalSections c L (s i)) =
      pullbackCoordSection (c ≫ g) i

variable {L s g}

/-- `pullbackGlobalSections` agrees with
`Stacks.NonvanishingPullback.pullbackGlobalSection`. -/
theorem pullbackGlobalSections_eq_nonvanishingPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (t : Γ(M, ⊤)) :
    pullbackGlobalSections f M t = Stacks.NonvanishingPullback.pullbackGlobalSection f M t := by
  show ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
      (Stacks.NonvanishingPullback.pullbackGlobalSection f M t) = _
  exact Functor.map_id_apply _ _ _

/-- If on an open cover of `P` the pair `(L, s)` is identified with the tautological pair of `g`,
compatibly with the sections, then the sections `s` generate the stalks of `L`. -/
theorem generatesStalks_of_isTautologicalOn
    (h : ∀ x : P, ∃ (Y : Scheme.{u}) (c : Y ⟶ P) (_ : IsOpenImmersion c),
      x ∈ Set.range c.base ∧ IsTautologicalOn L s g c) :
    GeneratesStalks s := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  obtain ⟨Y, c, _, ⟨y, rfl⟩, δ, hδ⟩ := h x
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks _ (tautological (c ≫ g)).generates y
  refine ⟨i, ?_⟩
  have hi' : y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback c).obj L)
      (pullbackGlobalSections c L (s i)) := by
    rw [← Stacks.Ample.nonvanishingLocus_congr δ, hδ i]
    exact hi
  rw [pullbackGlobalSections_eq_nonvanishingPullback] at hi'
  exact (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff c L (s i) y).mp hi'

/-- If on an open cover of `P` the pair `(L, s)` is
identified with the tautological pair of `g`, compatibly with the sections, then `L` is the
pullback of `𝒪(1)` along `g`, with `s` going to the pulled-back coordinates. -/
theorem exists_iso_pullback_of_isTautologicalOn
    (h : ∀ x : P, ∃ (Y : Scheme.{u}) (c : Y ⟶ P) (_ : IsOpenImmersion c),
      x ∈ Set.range c.base ∧ IsTautologicalOn L s g c) :
    ∃ β : L ≅ (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n),
      ∀ i, Scheme.Modules.Hom.app β.hom ⊤ (s i) = pullbackCoordSection g i := by
  let t : GeneratingTuple P n :=
    { bundle := L
      isInvertible := inferInstance
      coord := s
      generates := generatesStalks_of_isTautologicalOn h }
  set g' := (pointsEquiv P n).symm ⟦t⟧
  have hg' : Isomorphic (tautological g') t := isomorphic_tautological_pointsEquiv_symm t
  have hloc : ∀ {Y : Scheme.{u}} (c : Y ⟶ P), IsTautologicalOn L s g c → c ≫ g' = c ≫ g :=
    fun c ⟨δ, hδ⟩ => eq_of_isomorphic_tautological (isomorphic_trans
      (isomorphic_tautological_comp c g')
      (isomorphic_trans (pullbackTuple_isomorphic c hg') ⟨δ, hδ⟩))
  have hgg : g' = g := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨Y, c, _, hx, hc⟩ := h x
    refine ⟨c.opensRange, hx, ?_⟩
    rw [← Scheme.Hom.isoOpensRange_inv_comp c, Category.assoc, Category.assoc, hloc c hc]
  exact isomorphic_symm (hgg ▸ hg')

end LocalToGlobal

end Stacks.Chow.FreeTower

end
