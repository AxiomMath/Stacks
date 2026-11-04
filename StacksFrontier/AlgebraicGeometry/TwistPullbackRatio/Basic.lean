module

public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.TwistSectionOn
public import StacksFrontier.AlgebraicGeometry.ProjDegreeOneTriv.Basic
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers

/-!
# The transition ratio of the pulled-back hyperplane sheaf, on sections

The twist half of [Stacks, Tag 01NE] — `Stacks.AmpleImmersionReduction.TwistPullback`, the first
of the four named inputs of [Stacks, Tag 01VS] — asks for an isomorphism `M ≅ g ^* 𝒪(1)` for a
morphism `g : X ⟶ ℙⁿ_ℤ` pinned on each chart `X_{sᵢ}` by a generating family `s` of global
sections of an invertible `M`. Two of its three halves are proved in
`StacksDraft/AlgebraicGeometry/F3/TwistPullbackChart/`, and what those files record as the one
remaining proposition is the comparison of the two chart trivializations of `g ^* 𝒪(1)` on an
overlap. This file proves the **arithmetic content** of that comparison: the identity between the
pulled-back coordinate sections out of which the comparison is computed.

## The identity

`Tᵢ` is homogeneous of degree one in the homogeneous coordinate ring, so [Stacks, Tag 01MP]
attaches to it a global section `degreeSection 𝒮 1 Tᵢ` of `𝒪(1)` on `Proj 𝒮`, and [Stacks, Tag
01MS] makes that section a free generator of `𝒪(1)` over `D₊(Tᵢ)`
(`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection`). On `D₊(Tᵢ)` the
degree-zero fraction `Tⱼ/Tᵢ` is a section of the structure sheaf, through Mathlib's
`AlgebraicGeometry.Proj.awayToSection`, and the identity

> `Tⱼ|_{D₊(Tᵢ)} = (Tⱼ/Tᵢ) · Tᵢ|_{D₊(Tᵢ)}`

is `Stacks.TwistPullbackRatio.degreeSection_res_eq`. It is proved pointwise: the value of
`degreeSection 𝒮 1 a` at a point is the fraction `a / 1`
(`Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply`), the value of
`awayToSection` is the fraction itself (`AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`
is defined by `HomogeneousLocalization.mapId`, so the value is `rfl`), and the product of the two
is `p / 1` in the local ring.

The identity is then pushed along an arbitrary morphism `c : W ⟶ Proj 𝒮` by semilinearity of the
unit of the pullback--pushforward adjunction on sections, which is
`Stacks.TwistPullbackRatio.pbSec_smul`, giving
`Stacks.TwistPullbackRatio.pbSec_coordSectionOn`. For a *pinned* chart morphism the scalar is
computed: the pullback of `Tⱼ/Tᵢ` along `toProjectiveSpaceAtUniverse t ht` with `tᵢ = 1` is `tⱼ`
(`Stacks.TwistPullbackRatio.appLE_coordFraction`), which is the value that
`StacksFrontier/AlgebraicGeometry/TwistPullbackChart/Chart.lean` names as the one the residual
proposition has to be computed from.

## Main definitions

* `Stacks.TwistPullbackRatio.O1`: `𝒪(1)` on `Proj 𝒮`, at the `Scheme.Modules` spelling.
* `Stacks.TwistPullbackRatio.pbSec`: a section pulled back along a morphism of schemes, in the
  `Γ(·, ·)` spelling. This is
  `Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn` with the sections written at the
  spelling on which the scalar action is found; the two are equal by `rfl`
  (`Stacks.TwistPullbackRatio.pbSec_eq`), so every structural lemma of that file applies.
* `Stacks.TwistPullbackRatio.coordFraction`: the degree-zero fraction `Tⱼ/Tᵢ` of the homogeneous
  coordinate ring.
* `Stacks.TwistPullbackRatio.coordSectionOn`: the degree-one section `Tⱼ` of `𝒪(1)`, restricted
  to the standard chart `D₊(Tᵢ)`.

## Main results

* `Stacks.TwistPullbackRatio.degreeSection_res_eq`: **on `D₊(q)`, the degree-one section of `p`
  is the fraction `p/q` times the degree-one section of `q`**, for any two elements `p`, `q` of
  degree one of any graded ring.
* `Stacks.TwistPullbackRatio.pbSec_smul`: **the unit of the pullback--pushforward adjunction is
  semilinear on sections**: a pulled-back scalar multiple is the pullback of the scalar times the
  pulled-back section.
* `Stacks.TwistPullbackRatio.pbSec_coordSectionOn`: **the identity after pullback along an
  arbitrary morphism to `Proj` of the homogeneous coordinate ring.**
* `Stacks.TwistPullbackRatio.appLE_awayToSection`: the effect of a morphism
  `Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse` on the sections of the structure
  sheaf over a standard chart is `Stacks.ProjGlobalSectionsAppTop.projAwayHom`.
* `Stacks.TwistPullbackRatio.projAwayHom_coordFraction`,
  `Stacks.TwistPullbackRatio.appLE_coordFraction`: **the pullback of `Tⱼ/Tᵢ` along a pinned chart
  morphism is `tⱼ`.**

## Implementation notes

**The `Γ` spelling is not optional.** `pullbackSectionOn` is stated with `M.val.obj (op T)`, and
at that spelling the scalar action of `Γ(X, f ⁻¹ᵁ T)` is not found by instance search — the type
arrives wrapped in `ModuleCat.restrictScalars`, and the reported error names a missing `HSMul`
rather than the spelling mismatch it is. `pbSec` is the same map with its source and target
written as `Γ(M, T)` and `Γ(f ^* M, f ⁻¹ᵁ T)`, where Mathlib registers the module structures, and
`AlgebraicGeometry.Scheme.Modules.Hom.app_smul` then applies verbatim: the module structure of a
pushforward is restriction of scalars along `AlgebraicGeometry.Scheme.Hom.app`, so the two
statements are definitionally the same and `pbSec_smul` is that lemma under `exact`.

**The two spellings of the integral model, again.** `appLE_awayToSection` combines
`Stacks.SectionsToProjectiveSpace.resLE_toProjectiveSpaceAtUniverse`,
`Stacks.ProjGlobalSectionsAppTop.topIso_inv_resLE_appTop` and
`Stacks.ProjGlobalSectionsAppTop.toBasicOpenOfGlobalSections_appTop`. The last two cannot be
chained by `rw`: the composite differs only in which proof term fills the degree hypothesis, and
`rw` matches syntactically. They are chained with `congrArg` and `Eq.trans` instead, and the
trailing isomorphism is cancelled with `CategoryTheory.cancel_mono` — the same term-mode
discipline the sibling file records.

**The proposition is stated over `c ⁻¹ᵁ D₊(Tᵢ)`, not over `⊤`.** Writing it over `⊤` needs the
hypothesis that `c` factors through the chart, hence a transport along
`c ⁻¹ᵁ D₊(Tᵢ) = ⊤`; over the preimage the statement holds for *every* morphism `c` with no
hypothesis at all, and the consumer that knows the preimage is everything transports once.

## What is not done

**`Stacks.AmpleImmersionReduction.TwistPullback` is not proved, and this file does not close it.**
What it supplies is the arithmetic identity the comparison of the two chart trivializations is
computed from. Two things are still owed, and neither is here:

* **that the pulled-back coordinate section is a free generator** — equivalently, that the
  trivialization `Stacks.TwistPullbackChart.pullbackTwistRestrictIsoUnitChart` carries
  `pbSec g 𝒪(1) D₊(Tᵢ) (coordSectionOn i i)` to `1`. On `D₊(Tᵢ)` the section `Tᵢ` *is* a free
  generator of `𝒪(1)`, by
  `Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection`; what is missing is
  the transport of that statement along the pullback, which is a chase through
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`,
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
  `Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso`. The section-level lemmas for the
  first two are proved
  (`Stacks.AlgebraicGeometry.PullbackUnit.pullbackComp_hom_pullbackSectionOn`,
  `Stacks.AlgebraicGeometry.ProjMapCard.pullbackUnit_eq_restrictFunctorIsoPullback`); the one for
  `pullbackObjUnitIso` is not.
* **the assembly**: the local morphisms `M|_{X_{sᵢ}} ⟶ (g ^* 𝒪(1))|_{X_{sᵢ}}` sending `sᵢ` to the
  pulled-back `Tᵢ`, their compatibility on overlaps, and the glueing by
  `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`.

**No Stacks tag attribute is attached, and none is owed.** Tag 01VS is not proved and nothing
below is one of its assertions; Tag 01NE is a representability statement; Tag 01MP's degree-one
section and Tag 01MS's trivialization already carry their attributes at
`Stacks.AlgebraicGeometry.ProjTwistSections` and
`Stacks.AlgebraicGeometry.ProjTrivialization.twistingSheafOverBasicOpenIsoUnit`, and nothing below
restates either.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open HomogeneousLocalization

namespace Stacks.TwistPullbackRatio

universe u w

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- `O(1)` on `Proj S`, as a module on the scheme. -/
noncomputable abbrev O1 : (AlgebraicGeometry.Proj 𝒮).Modules := twistingSheaf 𝒮 (1 : ℤ)

/-- **On `D₊(q)` the degree-one section of `p` is the fraction `p/q` times the degree-one section
of `q`**, for any two degree-one elements of a graded ring.

Both sides are compared pointwise. The value of `degreeSection 𝒮 1 a` at a point is the fraction
`a / 1`; the value of `AlgebraicGeometry.Proj.awayToSection` at a point is the fraction itself,
because that map is `HomogeneousLocalization.mapId` and `HomogeneousLocalization.map_mk` is `rfl`;
and the scalar action on the sections of the twisting sheaf is multiplication of the values. What
is left is `p / 1 = (p / q) · (q / 1)` in the local ring. -/
theorem degreeSection_res_eq {p q : S} (hp : p ∈ 𝒮 1) (hq : q ∈ 𝒮 1) :
    (O1 𝒮).presheaf.map
        (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
        (degreeSection 𝒮 1 ⟨p, hp⟩) =
      (AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
          (Away.mk 𝒮 hq 1 p (by simpa using hp)) •
        (O1 𝒮).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 1 ⟨q, hq⟩) := by
  refine Subtype.ext (funext fun x => ?_)
  have key : ∀ (a : S) (ha : a ∈ 𝒮 1), ((O1 𝒮).presheaf.map
        (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
        (degreeSection 𝒮 1 ⟨a, ha⟩)).1 x =
      Localization.mk a (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    fun a ha => degreeSection_apply 𝒮 1 ⟨a, ha⟩ _
  have hR : ((AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
          (Away.mk 𝒮 hq 1 p (by simpa using hp)) •
        (O1 𝒮).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 1 ⟨q, hq⟩)).1 x =
      HomogeneousLocalization.val
          (((AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
            (Away.mk 𝒮 hq 1 p (by simpa using hp))).1 x) *
        ((O1 𝒮).presheaf.map
          (homOfLE (le_top (a := AlgebraicGeometry.Proj.basicOpen 𝒮 q))).op
          (degreeSection 𝒮 1 ⟨q, hq⟩)).1 x := rfl
  have hval : HomogeneousLocalization.val
      (((AlgebraicGeometry.Proj.awayToSection 𝒮 q).hom
        (Away.mk 𝒮 hq 1 p (by simpa using hp))).1 x) =
      Localization.mk p ⟨q ^ 1, _⟩ := rfl
  rw [key p hp, hR, hval, key q hq, Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp; ring))

section Semilinear

open Stacks.AlgebraicGeometry.PullbackUnit

variable {X Y : Scheme.{u}}

/-- A section pulled back, in the `Γ` spelling. -/
noncomputable def pbSec (f : X ⟶ Y) (M : Y.Modules) (T : Y.Opens) (s : Γ(M, T)) :
    Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ T) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app T s

/-- `pbSec` is `Stacks.AlgebraicGeometry.PullbackUnit.pullbackSectionOn`; only the spelling of
the sections differs. -/
theorem pbSec_eq (f : X ⟶ Y) (M : Y.Modules) (T : Y.Opens) (s : Γ(M, T)) :
    pbSec f M T s = pullbackSectionOn f M T s := rfl

/-- **The unit of the pullback--pushforward adjunction is semilinear on sections.** The module
structure of a pushforward is restriction of scalars along
`AlgebraicGeometry.Scheme.Hom.app`, so this is
`AlgebraicGeometry.Scheme.Modules.Hom.app_smul` at the unit. -/
theorem pbSec_smul (f : X ⟶ Y) (M : Y.Modules) (T : Y.Opens) (r : Γ(Y, T)) (s : Γ(M, T)) :
    pbSec f M T (r • s) = f.app T r • pbSec f M T s :=
  Scheme.Modules.Hom.app_smul _ r s

end Semilinear

/-! ### Prop R, chart form -/

section Chart

open Stacks.AlgebraicGeometry.PullbackUnit Stacks.ProjGlobalSectionsAppTop
open Stacks.SectionsToProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V : Scheme.{u}} {n : ℕ}

/-- **The effect of a morphism to the integral model on the sections of the structure sheaf over a
standard chart is `Stacks.ProjGlobalSectionsAppTop.projAwayHom`.** The morphism restricted to the
chart is Mathlib's `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections`, whose effect on sections
is known; the two statements are chained in term mode, for the reason in the
implementation notes. -/
theorem appLE_awayToSection (t : Fin (n + 1) → Γ(V, ⊤))
    (ht : Ideal.span (Set.range t) = ⊤) (i : Fin (n + 1))
    (z : Away (coordGrading.{u} n) (MvPolynomial.X i)) :
    (toProjectiveSpaceAtUniverse t ht).appLE
          (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
          (V.basicOpen (sectionsHom t (MvPolynomial.X i)))
          (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom t)
            (map_irrelevant_eq_top t ht) Nat.one_pos (X_mem_coordGrading_one i)).ge
        ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom z) =
      projAwayHom (coordGrading.{u} n) (sectionsHom t) z := by
  have h1 := topIso_inv_resLE_appTop (toProjectiveSpaceAtUniverse t ht)
    (U := AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (V := V.basicOpen (sectionsHom t (MvPolynomial.X i)))
    (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom t)
      (map_irrelevant_eq_top t ht) Nat.one_pos (X_mem_coordGrading_one i)).ge
  rw [resLE_toProjectiveSpaceAtUniverse t ht i] at h1
  have h2 := toBasicOpenOfGlobalSections_appTop (coordGrading.{u} n) (sectionsHom t)
    Nat.one_pos (X_mem_coordGrading_one i)
  have h3 := (congrArg (fun k => (AlgebraicGeometry.Proj.basicOpenIsoAway (coordGrading.{u} n)
      (MvPolynomial.X i) (X_mem_coordGrading_one i) Nat.one_pos).hom ≫ k) h1).symm.trans h2
  have h5 := (cancel_mono
    ((V.basicOpen (sectionsHom t (MvPolynomial.X i))).topIso.inv)).mp
      ((Category.assoc _ _ _).trans h3)
  exact CategoryTheory.ConcreteCategory.congr_hom h5 z


/-- The degree-zero fraction `Tⱼ / Tᵢ` on the standard chart `D₊(Tᵢ)`. -/
noncomputable def coordFraction (i j : Fin (n + 1)) :
    Away (coordGrading.{u} n) (MvPolynomial.X i) :=
  Away.mk (coordGrading.{u} n) (X_mem_coordGrading_one i) 1 (MvPolynomial.X j)
    (by simpa using X_mem_coordGrading_one j)

/-- **The chart's ring homomorphism sends `Tⱼ/Tᵢ` to `tⱼ`** when `tᵢ = 1`. The inverse of
`(tᵢ)|·` is supplied to
`Stacks.ProjGlobalSectionsAppTop.projAwayHom_apply_mk_of_mul_eq_one` as `1`, so no `Units` is
transported. -/
theorem projAwayHom_coordFraction (t : Fin (n + 1) → Γ(V, ⊤)) (i j : Fin (n + 1))
    (hti : t i = 1) :
    projAwayHom (coordGrading.{u} n) (sectionsHom t) (coordFraction.{u} i j) =
      resTop (V.basicOpen (sectionsHom t (MvPolynomial.X i))) (t j) := by
  have h1 : sectionsHom t (MvPolynomial.X i) = 1 := by rw [sectionsHom_X, hti]
  have hv : resTop (V.basicOpen (sectionsHom t (MvPolynomial.X i)))
      (sectionsHom t (MvPolynomial.X i)) * 1 = 1 := by rw [h1, map_one, mul_one]
  rw [coordFraction, projAwayHom_apply_mk_of_mul_eq_one (coordGrading.{u} n) (sectionsHom t)
    (X_mem_coordGrading_one i) 1 (MvPolynomial.X j) _ hv, one_pow, mul_one]
  simp only [sectionsHom_X]

/-- The restriction of the degree-one global section `Tⱼ` of `𝒪(1)` to the chart `D₊(Tᵢ)`. -/
noncomputable def coordSectionOn (i j : Fin (n + 1)) :
    Γ(O1 (coordGrading.{u} n),
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) :=
  (O1 (coordGrading.{u} n)).presheaf.map (homOfLE le_top).op
    (degreeSection (coordGrading.{u} n) 1 ⟨MvPolynomial.X j, X_mem_coordGrading_one j⟩)

/-- **The ratio proposition of Tag 01VS, in section form.** Over the preimage of the standard
chart `D₊(Tᵢ)`, the pullback of the degree-one section `Tⱼ` is the pullback of the degree-zero
fraction `Tⱼ/Tᵢ` times the pullback of `Tᵢ`. -/
theorem pbSec_coordSectionOn {W : Scheme.{u}} (c : W ⟶ AlgebraicGeometry.Proj (coordGrading.{u} n))
    (i j : Fin (n + 1)) :
    pbSec c (O1 (coordGrading.{u} n))
        (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
        (coordSectionOn.{u} i j) =
      c.app (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
          ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
            (MvPolynomial.X i)).hom (coordFraction.{u} i j)) •
        pbSec c (O1 (coordGrading.{u} n))
          (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
          (coordSectionOn.{u} i i) :=
  (congrArg (pbSec c (O1 (coordGrading.{u} n))
    (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)))
    (degreeSection_res_eq (coordGrading.{u} n) (X_mem_coordGrading_one j)
      (X_mem_coordGrading_one i))).trans (pbSec_smul ..)

/-- **The pullback of the fraction `Tⱼ/Tᵢ` along a pinned chart morphism is `tⱼ`.** -/
theorem appLE_coordFraction (t : Fin (n + 1) → Γ(V, ⊤))
    (ht : Ideal.span (Set.range t) = ⊤) (i j : Fin (n + 1)) (hti : t i = 1) :
    (toProjectiveSpaceAtUniverse t ht).appLE
          (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
          (V.basicOpen (sectionsHom t (MvPolynomial.X i)))
          (Proj.fromOfGlobalSections_preimage_basicOpen (coordGrading.{u} n) (sectionsHom t)
            (map_irrelevant_eq_top t ht) Nat.one_pos (X_mem_coordGrading_one i)).ge
        ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
          (coordFraction.{u} i j)) =
      resTop (V.basicOpen (sectionsHom t (MvPolynomial.X i))) (t j) :=
  (appLE_awayToSection t ht i _).trans (projAwayHom_coordFraction t i j hti)

end Chart

end Stacks.TwistPullbackRatio

end
