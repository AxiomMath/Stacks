module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleVeroneseRestrict

/-!
# The Veronese restriction of a graded map `ψ : A → Γ_*(T, L)`, and the two morphisms it defines

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`. Two constructions attach a morphism
into `Proj 𝒜` to such a `ψ`:

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued`, the morphism
  `r_{L, ψ} : U(ψ) ⟶ Proj 𝒜`, built from the charts of *all* homogeneous elements of positive
  degree; and
* `Stacks.AlgebraicGeometry.ProjChartCocycle.glued`, built from the charts of the homogeneous
  elements of one fixed degree `d > 0` and requiring that the sections `ψ(A_d)` generate `L ^⊗ d`.

The second takes as input a graded map `A^{(d)} → Γ_*(T, L ^⊗ d)`, which is `ψ` restricted to the
Veronese subring. The two families of charts agree, and so do the two morphisms where both are
defined.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedVeronese.veroneseAt` — the Veronese restriction
  `ψ|_{A^{(d)}} : A^{(d)} → Γ_*(T, L ^⊗ d)` of a graded map, in the degreewise spelling
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`. Its degree-`n` component is the
  degree-`nd` component of `ψ` read backwards through the comparison `(L ^⊗ d) ^⊗ n ≅ L ^⊗ (dn)`.
* `Stacks.AlgebraicGeometry.ProjChartGradedVeronese.gluedVeronese` — the morphism
  `Stacks.AlgebraicGeometry.ProjChartCocycle.glued` attached to that restriction, for a `ψ` whose
  degree-`d` values generate.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedVeronese.ratioOf_iso` — a ratio of two sections is
  unchanged by an isomorphism of the module they live on.
* `Stacks.AlgebraicGeometry.ProjChartGradedVeronese.nonvanishingOpen_veroneseAt_pow_one` — the
  nonvanishing open of the trivialising section of the restriction is `T_{ψ(f)}` itself.
* `Stacks.AlgebraicGeometry.ProjChartGradedVeronese.lift_veroneseAt_eq` — the two
  dehomogenisation ring maps `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` agree.
* `Stacks.AlgebraicGeometry.ProjChartGradedVeronese.chartToProj_veroneseAt` — the two charts
  `T_{ψ(f)} ⟶ Proj 𝒜` agree.
* `Stacks.AlgebraicGeometry.ProjChartGradedVeronese.homOfLE_glued_eq_gluedVeronese` — the
  morphism `r_{L, ψ}` and the morphism attached to `ψ|_{A^{(d)}}` agree, as morphisms out of the
  union of the degree-`d` nonvanishing opens.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop resTop_app)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartCocycle (ratioOf homogeneousRatios_toFun_eq)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjChartGradedPullback (ratioOf_den_congr)
open Stacks.AlgebraicGeometry.ProjVeroneseRestrict
open Stacks.GradedSections (powCongr)
open Stacks.MorphismToProj (HomogeneousRatios)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedVeronese

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Ratios and isomorphisms of modules -/

/-- A ratio of two sections is unchanged by an isomorphism of the module they live on: if `t`
and `x` are global sections of `M ^⊗ n` and `t` does not vanish on `V`, then the regular function
`x / t` on `V` is also the ratio of the images of `x` and `t` under any isomorphism
`M ^⊗ n ≅ N ^⊗ m`. -/
theorem ratioOf_iso {Y : Scheme.{u}} (M N : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
    [Stacks.Ample.IsInvertibleModule Y N] {n m : ℕ}
    (e : (natTensorPow M n : Y.Modules) ≅ natTensorPow N m) {V : Y.Opens}
    (t x : Γ(natTensorPow M n, ⊤)) (hV : V ≤ nonvanishingOpen Y (natTensorPow M n) t)
    (hV' : V ≤ nonvanishingOpen Y (natTensorPow N m) (e.hom.app ⊤ t)) :
    ratioOf N (e.hom.app ⊤ t) hV' (e.hom.app ⊤ x) = ratioOf M t hV x := by
  refine Stacks.AlgebraicGeometry.ProjChartCocycle.ratioOf_eq_of_resTop_eq N _ hV' ?_
  have h0 := congrArg (fun z : Γ(natTensorPow M n, V) => e.hom.app V z)
    (Stacks.AlgebraicGeometry.ProjChartCocycle.resTop_eq_ratioOf_smul M t hV x)
  simp only at h0
  rwa [← resTop_app, Scheme.Modules.Hom.app_smul, ← resTop_app] at h0

/-! ### The Veronese restriction of a graded map -/

section Veronese

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L]

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- The values of a graded map are compatible with transport along an equality of degrees. -/
theorem powCongr_app_toFun (ψ : GradedSections 𝒜 L) {n₁ n₂ : ℕ} (e : n₁ = n₂) (x : A)
    (h₁ : x ∈ 𝒜 n₁) (h₂ : x ∈ 𝒜 n₂) :
    (powCongr L e).app ⊤ (ψ.toFun n₁ ⟨x, h₁⟩) = ψ.toFun n₂ ⟨x, h₂⟩ := by
  subst e
  rfl

/-- The degree-`n` component of the Veronese restriction of `ψ` at weight `d`: the degree-`dn`
component of `ψ`, read backwards through the comparison `(L ^⊗ d) ^⊗ n ≅ L ^⊗ (dn)`. -/
def veroneseComp (ψ : GradedSections 𝒜 L) (d n : ℕ) :
    𝒜 (n * d) →+ Γ(natTensorPow (natTensorPow L d) n, ⊤) :=
  (appTopHom (powVeroneseIso L d n).inv).comp
    ((ψ.toFun (d * n)).comp (gradedCast 𝒜 (Nat.mul_comm n d)))

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- The value of the degree-`n` component of the restriction, with the homogeneous element read at
the degree `dn` where the values of `ψ` live rather than transported. -/
theorem veroneseComp_apply (ψ : GradedSections 𝒜 L) (d n : ℕ) (x : 𝒜 (n * d)) (y : 𝒜 (d * n))
    (hxy : (y : A) = (x : A)) :
    veroneseComp 𝒜 ψ d n x = (powVeroneseIso L d n).inv.app ⊤ (ψ.toFun (d * n) y) :=
  congrArg _ (congrArg (ψ.toFun (d * n)) (Subtype.ext hxy.symm))

/-- The Veronese restriction `ψ|_{A^{(d)}} : A^{(d)} → Γ_*(T, L ^⊗ d)` of a graded map, in the
degreewise spelling `Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`. -/
def veroneseAt (ψ : GradedSections 𝒜 L) (d : ℕ) :
    VeroneseSections 𝒜 d (natTensorPow L d) where
  toFun n := veroneseComp 𝒜 ψ d n
  map_mul n m a b ab hab := by
    have ha' : ((a : A)) ∈ 𝒜 (d * n) := mem_graded_of_eq 𝒜 (Nat.mul_comm n d) a.2
    have hb' : ((b : A)) ∈ 𝒜 (d * m) := mem_graded_of_eq 𝒜 (Nat.mul_comm m d) b.2
    have hab1 : ((ab : A)) ∈ 𝒜 (d * n + d * m) := mem_graded_of_eq 𝒜 (by ring) ab.2
    have hab2 : ((ab : A)) ∈ 𝒜 (d * (n + m)) := mem_graded_of_eq 𝒜 (by ring) ab.2
    rw [veroneseComp_apply 𝒜 ψ d (n + m) ab ⟨(ab : A), hab2⟩ rfl,
      veroneseComp_apply 𝒜 ψ d n a ⟨(a : A), ha'⟩ rfl,
      veroneseComp_apply 𝒜 ψ d m b ⟨(b : A), hb'⟩ rfl]
    refine Eq.trans (congrArg ((powVeroneseIso L d (n + m)).inv.app ⊤) ?_)
      (inv_app_hom_app (powVeroneseIso L d (n + m)) _)
    rw [mulSections_powVeroneseIso, hom_app_inv_app, hom_app_inv_app,
      ← ψ.map_mul (d * n) (d * m) ⟨(a : A), ha'⟩ ⟨(b : A), hb'⟩ ⟨(ab : A), hab1⟩ hab]
    exact (powCongr_app_toFun 𝒜 ψ (Nat.mul_add d n m).symm (ab : A) hab1 hab2).symm

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- The degree-`n` component of `veroneseAt 𝒜 ψ d` is `veroneseComp 𝒜 ψ d n`. -/
@[simp] theorem veroneseAt_toFun (ψ : GradedSections 𝒜 L) (d n : ℕ) :
    (veroneseAt 𝒜 ψ d).toFun n = veroneseComp 𝒜 ψ d n := rfl

/-! ### The trivialising sections of the restriction, and their nonvanishing opens -/

variable (ψ : GradedSections 𝒜 L) {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- The `n`-th power of the trivialising section of the Veronese restriction at `f` is the value
of `ψ` at `f ^ n`, read through the comparison. -/
theorem veroneseAt_pow (n : ℕ) (hfn : (f : A) ^ n ∈ 𝒜 (d * n)) :
    (veroneseAt 𝒜 ψ d).pow hf n
      = (powVeroneseIso L d n).inv.app ⊤ (ψ.toFun (d * n) ⟨f ^ n, hfn⟩) := by
  rw [VeroneseSections.pow]
  exact veroneseComp_apply 𝒜 ψ d n _ ⟨f ^ n, hfn⟩ rfl

/-- The nonvanishing open of a power of the trivialising section of the restriction is the
nonvanishing open of the corresponding value of `ψ`. -/
theorem nonvanishingOpen_veroneseAt_pow (n : ℕ) (hfn : (f : A) ^ n ∈ 𝒜 (d * n)) :
    nonvanishingOpen T (natTensorPow (natTensorPow L d) n) ((veroneseAt 𝒜 ψ d).pow hf n)
      = nonvanishingOpen T (natTensorPow L (d * n)) (ψ.toFun (d * n) ⟨f ^ n, hfn⟩) := by
  rw [veroneseAt_pow 𝒜 ψ hf n hfn]
  exact Opens.ext (Stacks.Ample.nonvanishingLocus_congr (powVeroneseIso L d n).symm _)

/-- The nonvanishing open of the trivialising section of the restriction at `f` is
`T_{ψ(f)}`. -/
theorem nonvanishingOpen_veroneseAt_pow_one :
    nonvanishingOpen T (natTensorPow (natTensorPow L d) 1) ((veroneseAt 𝒜 ψ d).pow hf 1)
      = nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩) := by
  have hfn : (f : A) ^ 1 ∈ 𝒜 (d * 1) := by rwa [pow_one, Nat.mul_one]
  rw [nonvanishingOpen_veroneseAt_pow 𝒜 ψ hf 1 hfn]
  exact ψ.nonvanishingOpen_congr hfn hf (Nat.mul_one d) (pow_one f)

/-! ### The two chart ring maps agree -/

/-- A ratio of two values of the Veronese restriction is the corresponding ratio of two values
of `ψ`. -/
theorem ratioOf_veroneseAt {V : T.Opens} (n : ℕ) (a : 𝒜 (n * d)) (y : 𝒜 (d * n))
    (hy : (y : A) = (a : A)) (hfn : (f : A) ^ n ∈ 𝒜 (n * d)) (hfd : (f : A) ^ n ∈ 𝒜 (d * n))
    (hden : V ≤ nonvanishingOpen T (natTensorPow (natTensorPow L d) n)
      ((veroneseAt 𝒜 ψ d).toFun n ⟨f ^ n, hfn⟩))
    (hden' : V ≤ nonvanishingOpen T (natTensorPow L (d * n))
      (ψ.toFun (d * n) ⟨f ^ n, hfd⟩)) :
    ratioOf (natTensorPow L d) ((veroneseAt 𝒜 ψ d).toFun n ⟨f ^ n, hfn⟩) hden
        ((veroneseAt 𝒜 ψ d).toFun n a)
      = ratioOf L (ψ.toFun (d * n) ⟨f ^ n, hfd⟩) hden' (ψ.toFun (d * n) y) := by
  have h2 : (veroneseAt 𝒜 ψ d).toFun n ⟨f ^ n, hfn⟩
      = (powVeroneseIso L d n).inv.app ⊤ (ψ.toFun (d * n) ⟨f ^ n, hfd⟩) :=
    veroneseComp_apply 𝒜 ψ d n ⟨f ^ n, hfn⟩ ⟨f ^ n, hfd⟩ rfl
  have hden2 : V ≤ nonvanishingOpen T (natTensorPow (natTensorPow L d) n)
      ((powVeroneseIso L d n).inv.app ⊤ (ψ.toFun (d * n) ⟨f ^ n, hfd⟩)) := h2 ▸ hden
  have h1 : (veroneseAt 𝒜 ψ d).toFun n a
      = (powVeroneseIso L d n).inv.app ⊤ (ψ.toFun (d * n) y) :=
    veroneseComp_apply 𝒜 ψ d n a y hy
  rw [h1, ratioOf_den_congr (natTensorPow L d) h2 hden hden2]
  exact ratioOf_iso L (natTensorPow L d) (powVeroneseIso L d n).symm _ _ hden' hden2

/-- The dehomogenisation ring map `A_{(f)} ⟶ Γ(T_{ψ(f)}, 𝒪_T)` of the Veronese restriction is
that of `ψ`. -/
theorem lift_veroneseAt_eq (hd : 0 < d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    (hW : V ≤ nonvanishingOpen T (natTensorPow (natTensorPow L d) 1)
      ((veroneseAt 𝒜 ψ d).pow hf 1)) :
    ((veroneseAt 𝒜 ψ d).homogeneousRatios hf hW).lift hd
      = (ψ.homogeneousRatios hf hV).lift hd := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun n x hx => ?_
  have hxm : x ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using hx
  have hxd : x ∈ 𝒜 (d * n) := mem_graded_of_eq 𝒜 (Nat.mul_comm n d) hxm
  have hfn : (f : A) ^ n ∈ 𝒜 (n * d) := HomogeneousRatios.pow_mem hf n
  have hfd : (f : A) ^ n ∈ 𝒜 (d * n) := mem_graded_of_eq 𝒜 (Nat.mul_comm n d) hfn
  have hden' : V ≤ nonvanishingOpen T (natTensorPow L (d * n))
      (ψ.toFun (d * n) ⟨f ^ n, hfd⟩) := by
    rw [ψ.nonvanishingOpen_congr hfd hfn (Nat.mul_comm d n) rfl]
    exact ψ.le_nonvanishingOpen_pow hf hV n
  rw [HomogeneousRatios.lift_mk _ hd n x hx ⟨x, hxm⟩ rfl,
    ψ.lift_mk hf hV hd n x hx ⟨x, hxm⟩ rfl,
    homogeneousRatios_toFun_eq (veroneseAt 𝒜 ψ d) hf hW n ⟨x, hxm⟩]
  exact (ratioOf_veroneseAt 𝒜 ψ n ⟨x, hxm⟩ ⟨x, hxd⟩ rfl hfn hfd _ hden').trans
    (ψ.ratioOf_congr hfd hxd hfn hxm hden' (ψ.le_nonvanishingOpen_pow hf hV n)
      (Nat.mul_comm d n) rfl rfl)

/-- The degree-`d` chart at `f` of the Veronese restriction, read into `Proj 𝒜`, is the chart
of `ψ` at `f`. -/
theorem chartToProj_veroneseAt (hd : 0 < d) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d ⟨f, hf⟩))
    (hW : V ≤ nonvanishingOpen T (natTensorPow (natTensorPow L d) 1)
      ((veroneseAt 𝒜 ψ d).pow hf 1)) :
    Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜
        ((veroneseAt 𝒜 ψ d).toDegreeOpen hf hW hd)
      = ψ.chartToProj hf hV hd := by
  rw [VeroneseSections.toDegreeOpen, HomogeneousRatios.toProj_toDegreeOpen,
    HomogeneousRatios.chartToProj, GradedSections.chartToProj,
    HomogeneousRatios.chartToProj, HomogeneousRatios.toSpecAway,
    HomogeneousRatios.toSpecAway, lift_veroneseAt_eq 𝒜 ψ hf hd hV hW]

end Veronese

/-! ### The two morphisms agree -/

section Compare

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {d : ℕ} (hd : 0 < d)
  (hgen : ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g) = ⊤)

/-- The nonvanishing open of a degree-`d` value of `ψ` lies in the nonvanishing open of the
corresponding trivialising section of the Veronese restriction. -/
theorem le_nonvanishingOpen_veroneseAt (g : 𝒜 d) :
    nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)
      ≤ nonvanishingOpen T (natTensorPow (natTensorPow L d) 1)
          ((veroneseAt 𝒜 ψ d).pow g.2 1) :=
  (nonvanishingOpen_veroneseAt_pow_one 𝒜 ψ g.2).ge

/-- The morphism `T ⟶ U_d` into the degree-`d` open of `Proj 𝒜` attached to the Veronese
restriction `ψ|_{A^{(d)}}`, for a graded map whose degree-`d` values generate `L ^⊗ d` on all of
`T`. -/
def gluedVeronese : T ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).toScheme :=
  Stacks.AlgebraicGeometry.ProjChartCocycle.glued 𝒜 (veroneseAt 𝒜 ψ d) hd
    (le_nonvanishingOpen_veroneseAt 𝒜 ψ) hgen

/-- On `T_{ψ(f)}`, for `f` homogeneous of degree `d`, the morphism `gluedVeronese` read into
`Proj 𝒜` is the dehomogenisation chart of `f`. -/
theorem ι_gluedVeronese (g : 𝒜 d) :
    (nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)).ι
        ≫ Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜 (gluedVeronese 𝒜 ψ hd hgen)
      = ψ.chartToProj g.2 le_rfl hd := by
  rw [Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj, ← Category.assoc, gluedVeronese,
    Stacks.AlgebraicGeometry.ProjChartCocycle.ι_glued 𝒜 (veroneseAt 𝒜 ψ d) hd
      (le_nonvanishingOpen_veroneseAt 𝒜 ψ) hgen g]
  exact chartToProj_veroneseAt 𝒜 ψ g.2 hd le_rfl (le_nonvanishingOpen_veroneseAt 𝒜 ψ g)

include hd in
/-- The union of the degree-`d` nonvanishing opens lies in `U(ψ)`. -/
theorem iSup_nonvanishingOpen_le_coveringOpen :
    (⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)) ≤ ψ.coveringOpen :=
  iSup_le fun g => ψ.nonvanishingOpenAt_le_coveringOpen_of_pos g.2 hd

/-- The morphism `r_{L, ψ}` agrees with `gluedVeronese`, the morphism attached to `ψ|_{A^{(d)}}`,
as morphisms out of the union of the degree-`d` nonvanishing opens — which under the generation
hypothesis is all of `T`. -/
theorem homOfLE_glued_eq_gluedVeronese :
    T.homOfLE (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd) ≫ ψ.glued
      = (⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)).ι
          ≫ Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜
              (gluedVeronese 𝒜 ψ hd hgen) := by
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun g : 𝒜 d => nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g))) _ _ fun g => ?_
  have hL : T.homOfLE (le_iSup
        (fun g : 𝒜 d => nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)) g)
      ≫ T.homOfLE (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd) ≫ ψ.glued
      = ψ.chartToProj g.2 le_rfl hd := by
    rw [← Category.assoc, T.homOfLE_homOfLE]
    exact ψ.homOfLE_glued_of_pos g.2 hd
  have hR : T.homOfLE (le_iSup
        (fun g : 𝒜 d => nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)) g)
      ≫ (⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)).ι
          ≫ Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜 (gluedVeronese 𝒜 ψ hd hgen)
      = ψ.chartToProj g.2 le_rfl hd := by
    rw [← Category.assoc, T.homOfLE_ι]
    exact ι_gluedVeronese 𝒜 ψ hd hgen g
  exact hL.trans hR.symm

end Compare

end Stacks.AlgebraicGeometry.ProjChartGradedVeronese

end
