module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecTwistPushforwardAlgebra
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistGlobalMap

/-!
# The degreewise inclusion `𝒪_P(m) ⟶ π_* 𝒪_L(i)` over a standard open

Let `A = ⨁_{d ≥ 0} A_d` be a graded ring, `P = Proj A`, and let `π : L = Proj B ⟶ P` be the cone
attached to the truncation algebra `B = ⨁_{d ≥ 0} A_{≥ d}`. Fix an integer `i`. For `f ∈ A_d`
homogeneous of positive degree, `π⁻¹(D₊(f)) = D₊(ψ f)`, so the sections of `π_* 𝒪_L(i)` over
`D₊(f)` are the sections of `𝒪_L(i)` over `D₊(ψ f)`, that is `(B[1/ψ f])_i`; and for `m ≥ i`
the sections of `𝒪_P(m)` over `D₊(f)` are `(A[1/f])_m`, which sits inside `(B[1/ψ f])_i` by
`Stacks.Truncation.twistPieceIncl`. This file turns that inclusion into a map of modules over
`Γ(P, D₊(f))`,

  `Γ(D₊(f), 𝒪_P(m)) ⟶ Γ(D₊(f), π_* 𝒪_L(i))`,

and proves that it commutes with restriction between standard opens.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.twistLift`: the inclusion
  `Γ(D₊(f), 𝒪_P(m)) →+ Γ(D₊(ψ f), 𝒪_L(i))`.
* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.twistPushforwardApp`: the same read in
  `Γ(D₊(f), π_* 𝒪_L(i))`, as a morphism of modules over `Γ(P, D₊(f))`.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.twistLift_smul`: `twistLift` is
  semilinear for `HomogeneousLocalization.Away.map ψ f`.
* `Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward.twistPushforwardApp_restrict`: the local
  map commutes with restriction between standard opens.

## References

* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory Opposite
open TopologicalSpace
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjConeTwist

namespace Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A}

/-- The direct image `π_* 𝒪_L(i)` along the cone projection of the truncation algebra, as a
sheaf of `𝒪_P`-modules. -/
abbrev twistPushforward (i : ℤ) : (AlgebraicGeometry.Proj 𝒜).Modules :=
  (Scheme.Modules.pushforward (pi 𝒜)).obj (twistingSheaf (grading 𝒜) i)

/-! ### The inclusion on sections -/

/-- For `m ≥ i`, the inclusion `Γ(D₊(f), 𝒪_P(m)) → Γ(D₊(ψ f), 𝒪_L(i))`: the inclusion
`(A[1/f])_m → (B[1/ψ f])_i` of `Stacks.Truncation.twistPieceIncl`, read on sections. -/
def twistLift {i m : ℤ} (him : i ≤ m) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) →+
      (twistingSheaf (grading 𝒜) i).val.obj
        (op (ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f))) :=
  (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading (grading 𝒜) ((psi 𝒜).map_mem hf)
      hd i).symm.toAddMonoidHom.comp
    ((twistPieceIncl 𝒜 hf hd him).comp
      (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m).toAddMonoidHom)

/-- The sections of `𝒪_L(i)` over `D₊(ψ f)`, read in `A[1/f]`. -/
def twistSectionsToLocalization (i : ℤ) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (twistingSheaf (grading 𝒜) i).val.obj
        (op (ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f))) →+ Localization.Away f :=
  (twistPieceToLocalization 𝒜 hf i).comp
    (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading (grading 𝒜) ((psi 𝒜).map_mem hf)
      hd i).toAddMonoidHom

/-- `twistSectionsToLocalization` is `locToLocalization` of the standard-open description. -/
theorem twistSectionsToLocalization_apply (i : ℤ) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (x : (twistingSheaf (grading 𝒜) i).val.obj
        (op (ProjectiveSpectrum.basicOpen (grading 𝒜) (psi 𝒜 f)))) :
    twistSectionsToLocalization 𝒜 i hf hd x =
      locToLocalization 𝒜 ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
        (grading 𝒜) ((psi 𝒜).map_mem hf) hd i x : LocalizedModule.Away (psi 𝒜 f) _)) :=
  rfl

/-- **The sections of `𝒪_L(i)` over `D₊(ψ f)` embed in `A[1/f]`.** -/
theorem twistSectionsToLocalization_injective (i : ℤ) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Function.Injective (twistSectionsToLocalization 𝒜 i hf hd) :=
  (twistPieceToLocalization_injective 𝒜 hf hd i).comp (AddEquiv.injective _)

/-- Read in `A[1/f]`, the inclusion `twistLift` is the standard-open description of the section
it starts from. -/
@[simp] theorem twistSectionsToLocalization_twistLift {i m : ℤ} (him : i ≤ m) {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    twistSectionsToLocalization 𝒜 i hf hd (twistLift 𝒜 him hf hd s) =
      ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m s :
        LocalizedModule.Away f A) : Localization.Away f) := by
  simp only [twistSectionsToLocalization, twistLift, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  exact twistPieceToLocalization_twistPieceIncl 𝒜 hf hd him _

/-- **`twistLift` is semilinear for `HomogeneousLocalization.Away.map ψ f`.** -/
theorem twistLift_smul {i m : ℤ} (him : i ≤ m) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (r : HomogeneousLocalization.Away 𝒜 f)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    twistLift 𝒜 him hf hd ((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom r • s) =
      (ProjectiveSpectrum.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
          (HomogeneousLocalization.Away.map (psi 𝒜) f r) • twistLift 𝒜 him hf hd s := by
  refine twistSectionsToLocalization_injective 𝒜 i hf hd ?_
  have h1 := twistSectionsToLocalization_twistLift 𝒜 him hf hd
    ((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom r • s)
  have h2 := twistSectionsToLocalization_twistLift 𝒜 him hf hd s
  have h3 := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul 𝒜 hf hd m r s
  have h4 := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul (grading 𝒜)
    ((psi 𝒜).map_mem hf) hd i (HomogeneousLocalization.Away.map (psi 𝒜) f r)
    (twistLift 𝒜 him hf hd s)
  have h5 := awayToLocalization_map_psi 𝒜 d hf r
  refine h1.trans (Eq.trans ?_ (twistSectionsToLocalization_apply 𝒜 i hf hd _).symm)
  refine (congrArg (fun z : LocalizedModule.Away f A => (z : Localization.Away f)) h3).trans ?_
  refine Eq.trans ?_ (congrArg (fun z : LocalizedModule.Away (psi 𝒜 f) (TruncationRing 𝒜) =>
    locToLocalization 𝒜 (z : Localization.Away (psi 𝒜 f))) h4).symm
  rw [twistSectionsToLocalization_apply] at h2
  change r.val * _ = locToLocalization 𝒜 ((HomogeneousLocalization.Away.map (psi 𝒜) f r).val * _)
  rw [map_mul, h2]
  exact congrArg (· * _) h5.symm

/-! ### The local map -/

attribute [local instance] Stacks.AlgebraicGeometry.ProjConeTwist.instTwistSectionsModule

/-- The local inclusion `Γ(D₊(f), 𝒪_P(m)) → Γ(D₊(f), π_* 𝒪_L(i))`, for `m ≥ i`, as an additive
map: `twistLift` followed by the transport along `π⁻¹(D₊(f)) = D₊(ψ f)`. -/
def twistPushforwardAddHom (i m : ℤ) (him : i ≤ m) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) →+
      (twistPushforward 𝒜 i).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :=
  ((twistingSheaf (grading 𝒜) i).val.map
    (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op).hom.toAddMonoidHom.comp
      (twistLift 𝒜 him hf hd)

/-- `twistPushforwardAddHom` is `twistLift` followed by the transport. -/
theorem twistPushforwardAddHom_apply (i m : ℤ) (him : i ≤ m) (d : ℕ) (hf : f ∈ 𝒜 d)
    (hd : 0 < d) (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    twistPushforwardAddHom 𝒜 i m him d hf hd s =
      (twistingSheaf (grading 𝒜) i).val.map
        (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op (twistLift 𝒜 him hf hd s) :=
  rfl

/-- The local inclusion `Γ(D₊(f), 𝒪_P(m)) ⟶ Γ(D₊(f), π_* 𝒪_L(i))`, for `m ≥ i`, as a morphism of
modules over the sections of `𝒪_P` on `D₊(f)`: `twistLift` followed by the transport along
`π⁻¹(D₊(f)) = D₊(ψ f)`. -/
@[stacks 0EKF "the inclusion O_P(m) to pi_* O_L(i), m ≥ i, over one standard open D+(f), as a \
map of modules over the sections of O_P there"]
def twistPushforwardApp (i m : ℤ) (him : i ≤ m) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) ⟶
      (twistPushforward 𝒜 i).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f)) := by
  letI iN : Module (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
      ((twistPushforward 𝒜 i).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :=
    ((twistPushforward 𝒜 i).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))).isModule
  let L : ((twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) →ₗ[
      (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj ⋙
        forget₂ CommRingCat.{u} RingCat.{u}).obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)))]
      ((twistPushforward 𝒜 i).val.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒜 f))) :=
    { toFun := twistPushforwardAddHom 𝒜 i m him d hf hd
      map_add' := (twistPushforwardAddHom 𝒜 i m him d hf hd).map_add
      map_smul' := by
        intro r s
        obtain ⟨a, rfl⟩ := awayToSection_surjective 𝒜 hf hd r
        have h1 := twistLift_smul 𝒜 him hf hd a s
        have h2 := (twistingSheaf (grading 𝒜) i).val.map_smul
          (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op
          ((ProjectiveSpectrum.Proj.awayToSection (grading 𝒜) (psi 𝒜 f)).hom
            (HomogeneousLocalization.Away.map (psi 𝒜) f a)) (twistLift 𝒜 him hf hd s)
        have h3 := awayToSection_pi_app 𝒜 d hf hd a
        refine (twistPushforwardAddHom_apply 𝒜 i m him d hf hd _).trans ?_
        refine (congrArg (fun z => (twistingSheaf (grading 𝒜) i).val.map
          (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op z) h1).trans ?_
        refine h2.trans ?_
        refine (congrArg (fun z : ((sheafCompose (Opens.grothendieckTopology
            (ProjectiveSpectrum.top (grading 𝒜))) (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (ProjectiveSpectrum.Proj.structureSheaf (grading 𝒜))).obj.obj
                (op (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)) =>
          z • @id ((twistingSheaf (grading 𝒜) i).val.obj
                (op (pi 𝒜 ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)))
            ((twistingSheaf (grading 𝒜) i).val.map
              (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op (twistLift 𝒜 him hf hd s)))
          h3).trans ?_
        rfl }
  exact @ModuleCat.ofHom _ _ _ _ _ _ _ iN L

/-- The components of the local map. -/
theorem twistPushforwardApp_apply (i m : ℤ) (him : i ≤ m) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (twistPushforwardApp 𝒜 i m him d hf hd).hom s = twistPushforwardAddHom 𝒜 i m him d hf hd s :=
  rfl

/-! ### Compatibility with restriction -/

/-- **`twistLift` commutes with restriction between two standard opens.** -/
theorem twistLift_restrict {i m : ℤ} (him : i ≤ m) {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    twistLift 𝒜 him hg he ((twistingSheaf 𝒜 m).val.map (homOfLE hfg).op s) =
      (twistingSheaf (grading 𝒜) i).val.map
        (homOfLE (basicOpen_psi_le 𝒜 hf hd hg he hfg)).op (twistLift 𝒜 him hf hd s) := by
  refine twistSectionsToLocalization_injective 𝒜 i hg he ?_
  have h1 := twistSectionsToLocalization_twistLift 𝒜 him hg he
    ((twistingSheaf 𝒜 m).val.map (homOfLE hfg).op s)
  have h2 := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_map_homOfLE 𝒜
    hf hd hg he hfg m s
  have h3 := ProjectiveSpectrum.localizedMap_eq_localizedRingMap 𝒜
    (twistGrading (S := A) 𝒜 m) f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading 𝒜 hf hd m s :
      LocalizedModule.Away f A))
  have h4 := twistSectionsToLocalization_apply 𝒜 i hg he
    ((twistingSheaf (grading 𝒜) i).val.map
      (homOfLE (basicOpen_psi_le 𝒜 hf hd hg he hfg)).op (twistLift 𝒜 him hf hd s))
  have h5 := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_map_homOfLE
    (grading 𝒜) ((psi 𝒜).map_mem hf) hd ((psi 𝒜).map_mem hg) he
    (basicOpen_psi_le 𝒜 hf hd hg he hfg) i (twistLift 𝒜 him hf hd s)
  have h6 := ProjectiveSpectrum.localizedMap_eq_localizedRingMap (grading 𝒜)
    (twistGrading (S := TruncationRing 𝒜) (grading 𝒜) i) (psi 𝒜 f) (psi 𝒜 g)
    (exists_psi_mem 𝒜 hf hd) (exists_psi_mem 𝒜 hg he) (basicOpen_psi_le 𝒜 hf hd hg he hfg)
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading (grading 𝒜)
      ((psi 𝒜).map_mem hf) hd i (twistLift 𝒜 him hf hd s) :
        LocalizedModule.Away (psi 𝒜 f) (TruncationRing 𝒜)))
  have h7 := locToLocalization_localizedRingMap 𝒜 ⟨d, hd, hf⟩ ⟨e, he, hg⟩
    (exists_psi_mem 𝒜 hf hd) (exists_psi_mem 𝒜 hg he) hfg (basicOpen_psi_le 𝒜 hf hd hg he hfg)
    ((Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading (grading 𝒜)
      ((psi 𝒜).map_mem hf) hd i (twistLift 𝒜 him hf hd s) :
        LocalizedModule.Away (psi 𝒜 f) (TruncationRing 𝒜)))
  have h8 := twistSectionsToLocalization_twistLift 𝒜 him hf hd s
  rw [twistSectionsToLocalization_apply] at h8
  refine h1.trans (Eq.trans ?_ h4.symm)
  refine (congrArg (fun z : LocalizedModule.Away g A => (z : Localization.Away g))
    (h2.trans h3)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z : LocalizedModule.Away (psi 𝒜 g) (TruncationRing 𝒜) =>
    locToLocalization 𝒜 (z : Localization.Away (psi 𝒜 g))) (h5.trans h6)).symm
  refine Eq.trans ?_ h7.symm
  exact congrArg (ProjectiveSpectrum.localizedRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg) h8.symm

/-- The restriction maps of the direct image `φ_* F` are those of `F` over the preimages. -/
theorem pushforward_map_eq {X Y : Scheme.{u}} (φ : Y ⟶ X) (F : Y.Modules) {U V : X.Opens}
    (h : V ≤ U) (y : Γ((Scheme.Modules.pushforward φ).obj F, U)) :
    ((Scheme.Modules.pushforward φ).obj F).val.map (homOfLE h).op y =
      F.val.map ((TopologicalSpace.Opens.map φ.base).map (homOfLE h)).op
        (y : Γ(F, φ ⁻¹ᵁ U)) :=
  rfl

/-- **The local inclusion commutes with restriction to a smaller standard open.** -/
@[stacks 0EKF "the inclusion O_P(m) to pi_* O_L(i) over standard opens is compatible with \
restriction between two standard opens"]
theorem twistPushforwardApp_restrict (i m : ℤ) (him : i ≤ m) {d e : ℕ} (hf : f ∈ 𝒜 d)
    (hd : 0 < d) (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (twistingSheaf 𝒜 m).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (twistPushforwardApp 𝒜 i m him e hg he).hom
        ((twistingSheaf 𝒜 m).val.map (homOfLE hfg).op s) =
      (twistPushforward 𝒜 i).val.map (homOfLE hfg).op
        ((twistPushforwardApp 𝒜 i m him d hf hd).hom s) := by
  have hL := (twistingSheaf (grading 𝒜) i).val.map_comp_apply
    (homOfLE (basicOpen_psi_le 𝒜 hf hd hg he hfg)).op
    (eqToHom (pi_preimage_basicOpen 𝒜 g e hg he)).op (twistLift 𝒜 him hf hd s)
  have hR := (twistingSheaf (grading 𝒜) i).val.map_comp_apply
    (eqToHom (pi_preimage_basicOpen 𝒜 f d hf hd)).op
    ((TopologicalSpace.Opens.map (pi 𝒜).base).map (homOfLE hfg)).op (twistLift 𝒜 him hf hd s)
  refine (twistPushforwardApp_apply 𝒜 i m him e hg he _).trans ?_
  refine (twistPushforwardAddHom_apply 𝒜 i m him e hg he _).trans ?_
  refine (congrArg (fun z => (twistingSheaf (grading 𝒜) i).val.map
    (eqToHom (pi_preimage_basicOpen 𝒜 g e hg he)).op z)
    (twistLift_restrict 𝒜 him hf hd hg he hfg s)).trans ?_
  refine hL.symm.trans ?_
  refine Eq.trans ?_ (pushforward_map_eq (pi 𝒜) (twistingSheaf (grading 𝒜) i) hfg _).symm
  refine Eq.trans ?_ (congrArg (fun z => (twistingSheaf (grading 𝒜) i).val.map
    ((TopologicalSpace.Opens.map (pi 𝒜).base).map (homOfLE hfg)).op z)
    ((twistPushforwardApp_apply 𝒜 i m him d hf hd s).trans
      (twistPushforwardAddHom_apply 𝒜 i m him d hf hd s))).symm
  refine Eq.trans ?_ hR
  exact congrArg (fun φ => (twistingSheaf (grading 𝒜) i).val.map φ (twistLift 𝒜 him hf hd s))
    (Subsingleton.elim _ _)

end Stacks.AlgebraicGeometry.ProjAndSpecTwistPushforward

end
