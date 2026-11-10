module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistLocalRestriction
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.WeightSplittingNaturality

/-!
# The degreewise inclusion `𝒪_P(m) ⟶ π_* 𝒪_L`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `P = Proj A`, and let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`. Over a standard open `D₊(f)` of a
positive-degree homogeneous element,
`Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp` is the inclusion of
`Γ(D₊(f), 𝒪_P(m))` in `Γ(D₊(f), π_* 𝒪_L)` as a map of modules over `Γ(P, D₊(f))`. This file
glues those local maps into a morphism of sheaves of `𝒪_P`-modules

  `𝒪_P(m) ⟶ π_* 𝒪_L`,

for every `m ≥ 0`, which is the degreewise half of the presentation
`π_* 𝒪_L = ⨁_{m ≥ 0} 𝒪_P(m)`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistStandardOpenHomData`: the local maps as a
  `Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistHom`: the morphism `𝒪_P(m) ⟶ π_* 𝒪_L` of
  sheaves of `𝒪_P`-modules, for `m` a natural number.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneIota`: the same family read on the homogeneous
  pieces of `Stacks.AlgebraicGeometry.ProjConeTwist.nonnegTwistAlgebra`, so indexed by all of
  `ℤ`, the negative pieces mapping by the morphism out of the zero sheaf.

## Main results

* `ProjectiveSpectrum.localizedMap_eq_localizedRingMap`: for the regular module, the restriction
  map `M_f → M_g` of localized modules is the restriction map `A_f → A_g` of localizations.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistAwayHom_degreeZeroRingMap`: the degreewise
  inclusion commutes with restriction, read in the degree-zero localizations of `B`.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp_restrict`: the same compatibility read on
  sections.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistApp_degree_indep`: the local map depends only
  on the standard open, not on the degree in which the element cutting it out is homogeneous.
* `Stacks.AlgebraicGeometry.ProjConeTwist.coneTwistHom_app`: the glued morphism restricts on each
  standard open to the local map.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation

namespace ProjectiveSpectrum

universe u w t

/-- The grading action used for a naturally graded ring acting on an integer-graded module. -/
local instance instVAddNatInt : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {S : Type u} {σ : Type w} {τ : Type t} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ S] [AddSubgroupClass τ S] (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- The unit of a localization, read as the image of `1` under the localization map of the
regular module. -/
private theorem mkLinearMap_one (f : S) :
    (LocalizedModule.mkLinearMap (Submonoid.powers f) S 1) = (1 : Localization.Away f) :=
  OreLocalization.one_def.symm

/-- For the regular module, the restriction map `M_f → M_g` of localized modules is the
restriction map `A_f → A_g` of localizations. -/
theorem localizedMap_eq_localizedRingMap (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (z : LocalizedModule.Away f S) :
    (moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg).localizedMap z =
      localizedRingMap 𝒜 f g hf hg hfg z := by
  let := Module.compHom (R := Localization.Away g) (S := Localization.Away f)
    (LocalizedModule.Away (R := S) g S) (localizedRingMap 𝒜 f g hf hg hfg).toRingHom
  have h1 : z = z • (LocalizedModule.mkLinearMap (Submonoid.powers f) S 1) := by
    rw [mkLinearMap_one]
    exact (mul_one z).symm
  rw [h1, LinearMap.map_smul, (moduleRestrictionMaps 𝒜 𝒨 f g hf hg hfg).map_mk 1,
    mkLinearMap_one, mkLinearMap_one]
  exact (mul_one _).trans (congrArg (localizedRingMap 𝒜 f g hf hg hfg) (mul_one z)).symm

end ProjectiveSpectrum

namespace Stacks.AlgebraicGeometry.ProjConeTwist

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A}

/-! ### The image of a standard open under `ψ` -/

/-- `ψ f` is homogeneous of positive degree as soon as `f` is. -/
theorem exists_psi_mem {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    ∃ e : ℕ, 0 < e ∧ psi 𝒜 f ∈ grading 𝒜 e :=
  ⟨d, hd, GradedRingHom.map_mem (psi 𝒜) hf⟩

/-- `ψ` carries an inclusion of standard opens of `P` to one of standard opens of `L`. -/
theorem basicOpen_psi_le {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 g) ≤
      ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f) := by
  change AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g) ≤
    AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 f)
  rw [← pi_preimage_basicOpen 𝒜 f d hf hd, ← pi_preimage_basicOpen 𝒜 g e hg he]
  exact fun x hx => hfg hx

/-! ### The restriction compatibility of the degreewise inclusion -/

/-- Restriction maps of the structure sheaf of `L` only depend on their source and target. -/
private theorem presheaf_map_hom_congr
    {X Y : ((AlgebraicGeometry.Proj (grading 𝒜)).Opens)ᵒᵖ} (a b : X ⟶ Y)
    (x : (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.obj X) :
    ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map a).hom x =
      ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map b).hom x := by
  rw [Subsingleton.elim a b]

/-- The degreewise inclusion commutes with restriction between two standard opens, read in the
degree-zero localizations of the truncation algebra. -/
@[stacks 0EKG "the degreewise inclusion of the sections of O_P(m) into the degree-zero \
localization of the truncation algebra commutes with restriction between two standard opens"]
theorem coneTwistAwayHom_degreeZeroRingMap (m : ℕ) {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    coneTwistAwayHom 𝒜 m e hg he
        (((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.map (homOfLE hfg).op).hom s) =
      ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (psi 𝒜 g)
        (exists_psi_mem 𝒜 hf hd) (exists_psi_mem 𝒜 hg he)
        (basicOpen_psi_le 𝒜 hf hd hg he hfg) (coneTwistAwayHom 𝒜 m d hf hd s) := by
  refine awayToLocalization_injective 𝒜 e hg ?_
  have h1 := awayToLocalization_awayGradingEquivSectionsTwist_symm 𝒜 e hg he m
    (((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.map (homOfLE hfg).op).hom s)
  have h2 := awayToLocalization_degreeZeroRingMap 𝒜 ⟨d, hd, hf⟩ ⟨e, he, hg⟩
    (exists_psi_mem 𝒜 hf hd) (exists_psi_mem 𝒜 hg he) hfg
    (basicOpen_psi_le 𝒜 hf hd hg he hfg) (coneTwistAwayHom 𝒜 m d hf hd s)
  have h3 := awayToLocalization_awayGradingEquivSectionsTwist_symm 𝒜 d hf hd m s
  have h4 := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_map_homOfLE
    𝒜 hf hd hg he hfg (m : ℤ) s
  have h5 := ProjectiveSpectrum.localizedMap_eq_localizedRingMap 𝒜
    (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 (m : ℤ)) f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd (m : ℤ) s :
      LocalizedModule.Away f A))
  exact ((h1.trans h4).trans h5).trans
    (h2.trans (congrArg (ProjectiveSpectrum.localizedRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg)
      h3)).symm

/-- The identification `B_{(ψ f)} = Γ(L, D₊(ψ f))` intertwines the degree-zero restriction map
of `B` with the restriction map of `𝒪_L`. -/
theorem awayToSection_degreeZeroRingMap_psi {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e)
    (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) :
    (AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 g)).hom
        (ProjectiveSpectrum.degreeZeroRingMap (grading 𝒜) (psi 𝒜 f) (psi 𝒜 g)
          (exists_psi_mem 𝒜 hf hd) (exists_psi_mem 𝒜 hg he)
          (basicOpen_psi_le 𝒜 hf hd hg he hfg) z) =
      ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
          (homOfLE (basicOpen_psi_le 𝒜 hf hd hg he hfg)).op).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom z) := by
  have h := ProjectiveSpectrum.basicOpenIsoAway_restrict (grading 𝒜) (psi 𝒜 f) (psi 𝒜 g) d e
    (GradedRingHom.map_mem (psi 𝒜) hf) hd (GradedRingHom.map_mem (psi 𝒜) hg) he
    (basicOpen_psi_le 𝒜 hf hd hg he hfg)
  rw [AlgebraicGeometry.Proj.basicOpenIsoAway_hom,
    AlgebraicGeometry.Proj.basicOpenIsoAway_hom] at h
  exact congrArg (fun φ : CommRingCat.of
    (HomogeneousLocalization.Away (grading 𝒜) (psi 𝒜 f)) ⟶
      Γ(AlgebraicGeometry.Proj (grading 𝒜),
        AlgebraicGeometry.Proj.basicOpen (grading 𝒜) (psi 𝒜 g)) =>
    CommRingCat.Hom.hom φ z) h

/-- The local degreewise inclusion commutes with restriction to a smaller standard open. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to pi_* O_L over standard opens is compatible \
with restriction between two standard opens"]
theorem coneTwistApp_restrict (m : ℕ) {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e)
    (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (coneTwistApp 𝒜 m e hg he).hom
        (((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.map (homOfLE hfg).op).hom s) =
      ((Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE hfg).op).hom
        ((coneTwistApp 𝒜 m d hf hd).hom s) := by
  have hψfg := basicOpen_psi_le 𝒜 hf hd hg he hfg
  have hcomp : ∀ {X Y Z : ((AlgebraicGeometry.Proj (grading 𝒜)).Opens)ᵒᵖ} (a : X ⟶ Y) (b : Y ⟶ Z)
      (x : (AlgebraicGeometry.Proj (grading 𝒜)).presheaf.obj X),
      ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map b).hom
          (((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map a).hom x) =
        ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map (a ≫ b)).hom x := by
    intro X Y Z a b x
    rw [(AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map_comp]
    rfl
  have hL : (coneTwistApp 𝒜 m e hg he).hom
        (((ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.map (homOfLE hfg).op).hom s) =
      ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map ((homOfLE hψfg).op ≫
          (eqToHom (pi_preimage_basicOpen 𝒜 g e hg he)).op)).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
          (coneTwistAwayHom 𝒜 m d hf hd s)) := by
    refine (coneTwistApp_apply 𝒜 m e hg he _).trans ?_
    refine Eq.trans (congrArg (fun w => ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
        (eqToHom (pi_preimage_basicOpen 𝒜 g e hg he)).op).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 g)).hom w))
      (coneTwistAwayHom_degreeZeroRingMap 𝒜 m hf hd hg he hfg s)) ?_
    rw [awayToSection_degreeZeroRingMap_psi 𝒜 hf hd hg he hfg]
    exact hcomp _ _ _
  have hR : ((Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE hfg).op).hom
        ((coneTwistApp 𝒜 m d hf hd).hom s) =
      ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
          ((eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op ≫
            ((Opens.map (pi 𝒜).base).map (homOfLE hfg)).op)).hom
        ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
          (coneTwistAwayHom 𝒜 m d hf hd s)) := by
    refine Eq.trans (congrArg
      ((Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.map (homOfLE hfg).op).hom
      (coneTwistApp_apply 𝒜 m d hf hd s)) ?_
    exact hcomp (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op
      ((Opens.map (pi 𝒜).base).map (homOfLE hfg)).op _
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact presheaf_map_hom_congr 𝒜 _ _ _

/-- The local degreewise inclusion depends only on the standard open, not on the degree in
which the element cutting it out is homogeneous. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to pi_* O_L over one standard open depends only \
on that open, not on the degree of the element cutting it out"]
theorem coneTwistApp_degree_indep (m : ℕ) {d d' : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hf' : f ∈ 𝒜 d') (hd' : 0 < d') :
    coneTwistApp 𝒜 m d hf hd = coneTwistApp 𝒜 m d' hf' hd' := by
  refine ConcreteCategory.hom_ext _ _ fun s => (coneTwistApp_apply 𝒜 m d hf hd s).trans
    (Eq.trans ?_ (coneTwistApp_apply 𝒜 m d' hf' hd' s).symm)
  refine Eq.trans (congrArg (fun w => ((AlgebraicGeometry.Proj (grading 𝒜)).presheaf.map
      (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op).hom
      ((AlgebraicGeometry.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom w))
    (awayGradingEquivSectionsTwist_symm_degree_indep 𝒜 hf hd hf' hd' m s)) ?_
  exact presheaf_map_hom_congr 𝒜 _ _ _

/-! ### Gluing the local maps -/

section Glue

open Stacks.AlgebraicGeometry.ProjTwistComparison

/-- The local degreewise inclusion attached to a positive-degree homogeneous element, with a
degree for it chosen. -/
def coneTwistStandardOpenApp (m : ℕ) (p : PositiveElem 𝒜) :
    (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ)).val.obj
        (op (positiveBasicOpen 𝒜 p)) ⟶
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)).val.obj
        (op (positiveBasicOpen 𝒜 p)) :=
  coneTwistApp 𝒜 m (Classical.choose p.2) (Classical.choose_spec p.2).2
    (Classical.choose_spec p.2).1

/-- The local data of the degreewise inclusion: the maps on the sections over the
positive-degree standard opens, together with their compatibility with restriction. -/
def coneTwistStandardOpenHomData (m : ℕ) :
    StandardOpenHomData 𝒜 (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 (m : ℤ))
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)) where
  app := coneTwistStandardOpenApp 𝒜 m
  app_restrict p q h s :=
    coneTwistApp_restrict 𝒜 m (Classical.choose_spec p.2).2 (Classical.choose_spec p.2).1
      (Classical.choose_spec q.2).2 (Classical.choose_spec q.2).1 h s

/-- The degreewise inclusion `𝒪_P(m) ⟶ π_* 𝒪_L`, for `m ≥ 0`: the morphism of sheaves of
`𝒪_P`-modules glued from the local maps over the standard opens of positive-degree homogeneous
elements. -/
@[stacks 0EKG "the degreewise inclusion O_P(m) to pi_* O_L as a morphism of sheaves of \
O_P-modules, for the truncation cone and a nonnegative degree m"]
def coneTwistHom (m : ℕ) :
    ProjectiveSpectrum.Proj.twistingSheaf 𝒜 (m : ℤ) ⟶
      Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜) :=
  homOfStandardOpenHomData 𝒜 (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 (m : ℤ))
    (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)) (coneTwistStandardOpenHomData 𝒜 m)

/-- The glued morphism restricts on a standard open to the local degreewise inclusion. -/
@[stacks 0EKG "the global degreewise inclusion restricts on each standard open to the local one"]
theorem coneTwistHom_app (m : ℕ) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (coneTwistHom 𝒜 m).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 f)) =
      coneTwistApp 𝒜 m d hf hd :=
  (homOfStandardOpenHomData_app 𝒜 (ProjectiveSpectrum.Proj.twistGrading (S := A) 𝒜 (m : ℤ))
      (Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)) (coneTwistStandardOpenHomData 𝒜 m)
      ⟨f, d, hd, hf⟩).trans
    (coneTwistApp_degree_indep 𝒜 m _ _ hf hd)

/-- The inclusion of each homogeneous piece of `⨁_{m ≥ 0} 𝒪_P(m)` in `π_* 𝒪_L`: the glued
degreewise inclusion in a nonnegative degree, and the morphism out of the zero sheaf in a
negative one. -/
@[stacks 0EKG "the inclusion of each homogeneous piece of the nonnegative twist algebra in \
pi_* O_L, for the truncation cone"]
def coneIota : ∀ n : ℤ, nonnegTwistingSheaf 𝒜 n ⟶
    Stacks.Morphisms.pushforwardStructureSheaf (pi 𝒜)
  | (m : ℕ) => coneTwistHom 𝒜 m
  | .negSucc k =>
    (isZero_nonnegTwistingSheaf 𝒜 (Int.negSucc_lt_zero k)).to_ _

/-- In a nonnegative degree `m`, `coneIota` is the degreewise inclusion `coneTwistHom 𝒜 m`. -/
@[simp] theorem coneIota_natCast (m : ℕ) : coneIota 𝒜 (m : ℤ) = coneTwistHom 𝒜 m := rfl

end Glue

end Stacks.AlgebraicGeometry.ProjConeTwist

end
