module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitSection
public import StacksFrontier.AlgebraicGeometry.TwistTensor.UniversalVeroneseSections

/-!
# The universal family on `U_d` is compatible with the identity

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, let `d ≥ 1` and let `U_d ⊆ X` be the
open of Equation 27.12.0.1. [Stacks, Tag 01N9] names `(d, 𝒪_{U_d}(d), ψ^d)` the universal family
of the functor of triples, which asserts in particular that the morphism `U_d ⟶ U_d` classified
by that family — the one [Stacks, Tag 01N8] attaches to it — is the **identity**.

This file proves it, in the form the classification of [Stacks, Tag 01N8] is stated in: the pair
`(𝟙_{U_d}, id)` is compatible with `ψ^d` in the sense of
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible`.

## Main results

* `Stacks.AlgebraicGeometry.ProjUniversalCompatible.isCompatible_universalVeroneseSections`:
  **the universal family is compatible with the identity of `U_d`**, the isomorphism
  `α : (𝟙)⁎𝒪_{U_d}(d) ≅ 𝒪_{U_d}(d)` being the identity. With the uniqueness half of [Stacks, Tag
  01N8] this says that the morphism `U_d ⟶ U_d` the universal family classifies is the identity,
  which is drawn in
  `StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorSurjective.lean`.

## Implementation notes

**The two clauses of `IsCompatible`, and what each needs.**

*Degree one* asserts `α(ψ^d_𝟙(x)) = ψ^d(x)`. The left-hand side is the global section of
`𝒪_{U_d}(d)` attached to `x`, pulled back along the identity; the right-hand side is that same
section read on the first tensor power `𝒪_{U_d}(d)^{⊗ 1}` through
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat` and brought back by the left
unitor. So the clause is the statement that `thetaNat` in degree one **is** the left unitor, up
to the transport between the twist degrees `d` and `1 · d`: that is `thetaNat_one_hom` below,
which is `Stacks.AlgebraicGeometry.ThetaMul.theta_one_eq` with the two degree transports composed
into one.

*Degree `n`* asserts the local identity `ψ(a)|_V = φ^♯(a/f^n) · ψ(f)^n|_V`. For the universal
family `φ` is the open immersion `U_d ⟶ X`, so `φ^♯` is restriction of sections and the identity
is the one on `X` itself: over `D₊(f)` the global section of `𝒪_X(nd)` attached to a homogeneous
`a` of degree `nd` is the fraction `a/f^n` times the one attached to `f ^ n`. That is
`resTop_degreeSection_eq_smul_pow`, the pointwise computation of
`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_degreeSection_eq_smul` with the degree and
the exponent of the denominator freed. It is carried to `U_d` by the semilinearity of the
pullback of a section and then through `thetaNat`, which is a morphism of `𝒪_{U_d}`-modules and
so commutes with restriction and with the scalar action.

**No `@[stacks]` attribute.** What is proved is a step towards the surjectivity half of [Stacks,
Tag 01NC] and not a clause of [Stacks, Tag 01N9]: the clauses of that tag recorded in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjDegreeOpenRepresents.lean` are the universal
family itself and the representability of `F_d`, and the identity classified here is used in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorSurjective.lean`.

## References

* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization (Away)
open Stacks.AlgebraicGeometry.CommonDegreeTwist (restrictedTwist restrictedDegreeSection)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjChartCocycleMatch (twistDeg resTop_pullbackSectionHom)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents (universalTwist)
open Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple
open Stacks.AlgebraicGeometry.ProjTwistSections (degreeSection_apply)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen (twist theta thetaNat twistOneIso)
open Stacks.AlgebraicGeometry.ThetaMul (theta_one_eq)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjUniversalCompatible

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-! ### The comparison of the tensor powers in degree one -/

/-- **Cancelling an isomorphism against a factorisation of its inverse.** If `α.hom` factors as
`u` followed by `e` and `e` is split by `e'`, then `α.inv` followed by `u` is `e'`. Stated in a
bare category with every object and morphism free, so that it can be applied to a goal mixing two
spellings of one object. -/
private theorem inv_comp_of_hom_eq {C : Type*} [Category C] {X Y Z : C} (α : X ≅ Y) (u : X ⟶ Z)
    (e : Z ⟶ Y) (e' : Y ⟶ Z) (h : α.hom = u ≫ e) (he : e ≫ e' = 𝟙 Z) :
    α.inv ≫ u = e' :=
  calc α.inv ≫ u = α.inv ≫ (u ≫ e) ≫ e' := by rw [Category.assoc, he, Category.comp_id]
    _ = α.inv ≫ α.hom ≫ e' := by rw [h]
    _ = e' := α.inv_hom_id_assoc e'

/-- **The comparison `𝒪_{U_d}(d)^{⊗ n} ≅ 𝒪_{U_d}(nd)` in degree `n = 1` is the left unitor**, up
to the transport between the twist degrees `d` and `1 · d`.

`Stacks.AlgebraicGeometry.ThetaMul.theta_one_eq` identifies the comparison in degree one with
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistOneIso`, which is the left unitor
followed by the transport between the degrees `d` and `d · 1`; composing that transport with the
one `thetaNat` adds leaves a single transport. -/
theorem thetaNat_one_hom :
    (thetaNat 𝒮 d 1).hom
      = (unitorPow (universalTwist 𝒮 d)).hom ≫
        eqToHom (congrArg (fun j : ℕ => restrictedTwist 𝒮 (degreeOpen 𝒮 d) (j : ℤ))
          (one_mul d).symm) := by
  rw [show (thetaNat 𝒮 d 1).hom
        = (theta 𝒮 d 1).hom ≫ eqToHom (congrArg (restrictedTwist 𝒮 (degreeOpen 𝒮 d))
            (show (d : ℤ) * (1 : ℕ) = ((1 * d : ℕ) : ℤ) from by push_cast; ring)) from rfl,
    theta_one_eq,
    show (twistOneIso 𝒮 d).hom
        = (unitorPow (universalTwist 𝒮 d)).hom ≫
          eqToHom (congrArg (restrictedTwist 𝒮 (degreeOpen 𝒮 d))
            (show (d : ℤ) = (d : ℤ) * 1 from by ring)) from rfl]
  exact Eq.trans (Category.assoc _ _ _)
    (congrArg (fun z => (unitorPow (universalTwist 𝒮 d)).hom ≫ z) (eqToHom_trans _ _))

/-- **The inverse of the comparison in degree one, followed by the left unitor, is the transport
between the twist degrees `1 · d` and `d`.** This is `thetaNat_one_hom` with the unitor moved to
the other side. -/
theorem thetaNat_one_inv_comp :
    (thetaNat 𝒮 d 1).inv ≫ (unitorPow (universalTwist 𝒮 d)).hom
      = eqToHom (congrArg (fun j : ℕ => restrictedTwist 𝒮 (degreeOpen 𝒮 d) (j : ℤ))
          (one_mul d)) :=
  inv_comp_of_hom_eq _ _ _ _ (thetaNat_one_hom 𝒮 d)
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))

/-- The transport along an equality of twist degrees carries the restricted global section of an
element to the restricted global section of that same element read in the other degree. -/
theorem eqToHom_app_restrictedDegreeSection {k : ℕ} (hk : k = d) (x : 𝒮 k)
    (hx : (x : S) ∈ 𝒮 d) :
    Scheme.Modules.Hom.app
        (eqToHom (congrArg (fun j : ℕ => restrictedTwist 𝒮 (degreeOpen 𝒮 d) (j : ℤ)) hk)) ⊤
        (restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) k x)
      = restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) d ⟨(x : S), hx⟩ := by
  subst hk
  simp

/-- **The degree-one clause of compatibility, for the universal family and the identity.** The
degree-one value of the universal family's graded map, read in `𝒪_{U_d}(d)` through the left
unitor, is the global section of `𝒪_X(d)` attached to the element, pulled back along the
identity of `U_d`. -/
theorem unitorPow_hom_app_universalVeroneseSections (x : 𝒮 (1 * d)) (hx : (x : S) ∈ 𝒮 d) :
    (unitorPow (universalTwist 𝒮 d)).hom.app ⊤ ((universalVeroneseSections 𝒮 d).toFun 1 x)
      = pullbackDegreeSection 𝒮 (𝟙 (degreeOpen 𝒮 d).toScheme) ⟨(x : S), hx⟩ := by
  rw [universalVeroneseSections_toFun,
    show pullbackDegreeSection 𝒮 (𝟙 (degreeOpen 𝒮 d).toScheme) ⟨(x : S), hx⟩
        = restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) d ⟨(x : S), hx⟩ from
      pullbackDegreeSection_eq_pullbackGlobalSection 𝒮 _ _,
    ← eqToHom_app_restrictedDegreeSection 𝒮 d (one_mul d) x hx]
  refine Eq.trans ?_ (congrArg
    (fun φ => Scheme.Modules.Hom.app φ ⊤ (restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) (1 * d) x))
    (thetaNat_one_inv_comp 𝒮 d))
  rfl

/-! ### The local identity on `Proj 𝒜` and on `U_d` -/

section ProjSide

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **On `D₊(f)` the degree-`nd` section of `a` is the fraction `a/f^n` times the degree-`nd`
section of `f ^ n`**, for `f` homogeneous of degree `d` and `a` homogeneous of degree `nd`.

This is `Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_degreeSection_eq_smul` with the
common degree freed from `d` and the exponent of the denominator freed from `1`; the pointwise
computation is the same, the local value of the degree-`k` section of an element being the
fraction `element / 1` in every degree
(`Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply`) and the local value of
`AlgebraicGeometry.Proj.awayToSection` being the fraction itself. -/
theorem resTop_degreeSection_eq_smul_pow {f : S} (hf : f ∈ 𝒮 d) (n : ℕ) (x : S)
    (hx : x ∈ 𝒮 (n • d)) (a : 𝒮 (n * d)) (ha : (a : S) = x) (b : 𝒮 (n * d))
    (hb : (b : S) = f ^ n) :
    resTop (twistDeg 𝒮 (d := n * d)) (degreeSection 𝒮 (n * d) a)
          (AlgebraicGeometry.Proj.basicOpen 𝒮 f)
      = (AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n x hx) •
        resTop (twistDeg 𝒮 (d := n * d)) (degreeSection 𝒮 (n * d) b)
          (AlgebraicGeometry.Proj.basicOpen 𝒮 f) := by
  refine Subtype.ext (funext fun z => ?_)
  have hs : ∀ c : 𝒮 (n * d),
      (resTop (twistDeg 𝒮 (d := n * d)) (degreeSection 𝒮 (n * d) c)
        (AlgebraicGeometry.Proj.basicOpen 𝒮 f)).1 z = Localization.mk (c : S) 1 :=
    fun c => degreeSection_apply 𝒮 (n * d) c _
  have hR : ((AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n x hx) •
        resTop (twistDeg 𝒮 (d := n * d)) (degreeSection 𝒮 (n * d) b)
          (AlgebraicGeometry.Proj.basicOpen 𝒮 f)).1 z =
      HomogeneousLocalization.val
          (((AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n x hx)).1 z) *
        (resTop (twistDeg 𝒮 (d := n * d)) (degreeSection 𝒮 (n * d) b)
          (AlgebraicGeometry.Proj.basicOpen 𝒮 f)).1 z := rfl
  have hval : HomogeneousLocalization.val
      (((AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n x hx)).1 z) =
      Localization.mk x ⟨f ^ n, _⟩ := rfl
  rw [hs a, hR, hval, hs b, Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [ha, hb]; ring))

end ProjSide

/-- The restricted global section of `𝒪_X(k)` attached to a homogeneous element is the pullback
of that global section along the open immersion `U_d ⟶ X`, in the spelling
`AlgebraicGeometry.pullbackSectionHom` uses; the two differ by the restriction along
`⊤ ⟶ ι ⁻¹ᵁ ⊤`, which is the identity. -/
theorem restrictedDegreeSection_eq_pullbackSectionHom (k : ℕ) (a : 𝒮 k) :
    restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) k a
      = pullbackSectionHom (degreeOpen 𝒮 d).ι (twistingSheaf 𝒮 (k : ℤ)) ⊤ ⊤ (by simp)
          (degreeSection 𝒮 k a) :=
  (Stacks.PullbackUnitSection.pullbackSectionHom_top_eq (degreeOpen 𝒮 d).ι
    (twistingSheaf 𝒮 (k : ℤ)) (by simp) (degreeSection 𝒮 k a)).symm

/-- **The local identity on `U_d`**: over an open mapping into `D₊(f)` the restricted global
section of `𝒪_{U_d}(nd)` attached to `a` is the restriction of the fraction `a/f^n` times the one
attached to `f ^ n`.

This is `resTop_degreeSection_eq_smul_pow` pulled back along the open immersion: pulling a
section back is semilinear (`AlgebraicGeometry.pullbackSectionHom_smul`) and compatible with
shrinking the open upstairs (`AlgebraicGeometry.pullbackSectionHom_map`) and downstairs
(`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_pullbackSectionHom`). -/
theorem resTop_restrictedDegreeSection_eq_smul {f : S} (hf : f ∈ 𝒮 d) (n : ℕ) (x : S)
    (hx : x ∈ 𝒮 (n • d)) (a : 𝒮 (n * d)) (ha : (a : S) = x) (b : 𝒮 (n * d))
    (hb : (b : S) = f ^ n) {V : (degreeOpen 𝒮 d).toScheme.Opens}
    (hV : V ≤ (degreeOpen 𝒮 d).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 f) :
    resTop (restrictedTwist 𝒮 (degreeOpen 𝒮 d) ((n * d : ℕ) : ℤ))
        (restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) (n * d) a) V
      = (degreeOpen 𝒮 d).ι.appLE (AlgebraicGeometry.Proj.basicOpen 𝒮 f) V hV
          ((AlgebraicGeometry.Proj.awayToSection 𝒮 f).hom (Away.mk 𝒮 hf n x hx))
        • resTop (restrictedTwist 𝒮 (degreeOpen 𝒮 d) ((n * d : ℕ) : ℤ))
            (restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) (n * d) b) V := by
  have hres : ∀ c : 𝒮 (n * d),
      resTop (restrictedTwist 𝒮 (degreeOpen 𝒮 d) ((n * d : ℕ) : ℤ))
          (restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) (n * d) c) V
        = pullbackSectionHom (degreeOpen 𝒮 d).ι (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ))
            (AlgebraicGeometry.Proj.basicOpen 𝒮 f) V hV
            (resTop (twistDeg 𝒮 (d := n * d)) (degreeSection 𝒮 (n * d) c)
              (AlgebraicGeometry.Proj.basicOpen 𝒮 f)) := fun c =>
    Eq.trans
      (congrArg (fun z => resTop (restrictedTwist 𝒮 (degreeOpen 𝒮 d) ((n * d : ℕ) : ℤ)) z V)
        (restrictedDegreeSection_eq_pullbackSectionHom 𝒮 d (n * d) c))
      (Eq.trans
        (resTop_pullbackSectionHom (degreeOpen 𝒮 d).ι (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)) ⊤
          (by simp) (by simp) le_top (degreeSection 𝒮 (n * d) c))
        (pullbackSectionHom_map (degreeOpen 𝒮 d).ι (twistingSheaf 𝒮 ((n * d : ℕ) : ℤ)) ⊤
          (AlgebraicGeometry.Proj.basicOpen 𝒮 f) le_top V hV (by simp)
          (degreeSection 𝒮 (n * d) c)).symm)
  rw [hres a, hres b, resTop_degreeSection_eq_smul_pow 𝒮 d hf n x hx a ha b hb]
  exact pullbackSectionHom_smul _ _ _ _ _ _ _

/-- **The degree-`n` clause of compatibility, for the universal family and the identity.** The
comparison `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.thetaNat` is a morphism of
`𝒪_{U_d}`-modules, so it carries the local identity `resTop_restrictedDegreeSection_eq_smul` from
the twist `𝒪_{U_d}(nd)` to the tensor power `𝒪_{U_d}(d)^{⊗ n}` the graded map of a triple is
indexed by. -/
theorem resTop_universalVeroneseSections_eq_smul (f : 𝒮 d)
    (V : (degreeOpen 𝒮 d).toScheme.Opens)
    (hV : V ≤ (degreeOpen 𝒮 d).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S))
    (n : ℕ) (y : S) (hy : y ∈ 𝒮 (n • d)) (a : 𝒮 (n * d)) (hay : (a : S) = y) :
    resTop (natTensorPow (universalTwist 𝒮 d) n) ((universalVeroneseSections 𝒮 d).toFun n a) V
      = (degreeOpen 𝒮 d).ι.appLE (AlgebraicGeometry.Proj.basicOpen 𝒮 (f : S)) V hV
          ((AlgebraicGeometry.Proj.awayToSection 𝒮 (f : S)).hom (Away.mk 𝒮 f.2 n y hy))
        • resTop (natTensorPow (universalTwist 𝒮 d) n)
            ((universalVeroneseSections 𝒮 d).pow f.2 n) V := by
  have hfn : ((f : S) ^ n) ∈ 𝒮 (n * d) :=
    Stacks.MorphismToProj.HomogeneousRatios.pow_mem f.2 n
  have hT : ∀ c : 𝒮 (n * d),
      resTop (natTensorPow (universalTwist 𝒮 d) n) ((universalVeroneseSections 𝒮 d).toFun n c) V
        = (thetaNat 𝒮 d n).inv.app V
            (resTop (restrictedTwist 𝒮 (degreeOpen 𝒮 d) ((n * d : ℕ) : ℤ))
              (restrictedDegreeSection 𝒮 (degreeOpen 𝒮 d) (n * d) c) V) := fun c =>
    Stacks.TensorPowerTrivialize.resTop_app (thetaNat 𝒮 d n).inv _ V
  rw [hT a,
    show (universalVeroneseSections 𝒮 d).pow f.2 n
        = (universalVeroneseSections 𝒮 d).toFun n ⟨(f : S) ^ n, hfn⟩ from rfl,
    hT ⟨(f : S) ^ n, hfn⟩,
    resTop_restrictedDegreeSection_eq_smul 𝒮 d f.2 n y hy a hay ⟨(f : S) ^ n, hfn⟩ rfl]
  exact Scheme.Modules.Hom.app_smul _ _ _

/-! ### The universal family and the identity -/

/-- **The universal family `(d, 𝒪_{U_d}(d), ψ^d)` of [Stacks, Tag 01N9] is compatible with the
identity of `U_d`**, in the sense of
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible`, the isomorphism
`α : (𝟙_{U_d})⁎𝒪_{U_d}(d) ≅ 𝒪_{U_d}(d)` being the identity — the two modules are the same object,
`𝒪_{U_d}(d)` being written in [Stacks, Tag 01N9] as the pullback of `𝒪_X(d)` along `𝟙 ≫ ι`.

The degree-one clause is `unitorPow_hom_app_universalVeroneseSections` and the degree-`n` clause
is `resTop_universalVeroneseSections_eq_smul`. -/
theorem isCompatible_universalVeroneseSections :
    IsCompatible (A := S) 𝒮 (universalVeroneseSections 𝒮 d)
      ⟨𝟙 (degreeOpen 𝒮 d).toScheme, Iso.refl _⟩ :=
  ⟨fun x => by
      have hx : (x : S) ∈ 𝒮 d := by simpa using x.2
      rw [twistCast_hom_app_psiPullbackHom 𝒮 (𝟙 (degreeOpen 𝒮 d).toScheme) x hx]
      exact (unitorPow_hom_app_universalVeroneseSections 𝒮 d x hx).symm,
    fun f V hV n y hy a hay =>
      resTop_universalVeroneseSections_eq_smul 𝒮 d f V hV n y hy a hay⟩

end Stacks.AlgebraicGeometry.ProjUniversalCompatible

end
