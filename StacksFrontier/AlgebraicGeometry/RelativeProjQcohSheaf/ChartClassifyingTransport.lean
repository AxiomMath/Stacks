module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClassifying
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartFdRepresentation

/-!
# The chart-wise representation of `F_d` is a classifying morphism for the chart's graded ring

Let `S` be a scheme, `A` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `U` an affine
open of `S` and `d ≥ 1`. `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.chartEquiv` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartFdRepresentation` represents the
functor `F_d` of Section 01NS for the restricted algebra `A|_U` by the degree-`d` open of
`Γ(U, A)`. Its morphism is *not* presented as a [Stacks, Tag 01N8] classifying morphism for the
graded ring `𝒜(U)`: it is the classifying morphism for the graded ring of **global** sections of
`A|_U`, postcomposed with the identification of schemes
`...RelativeProjBridge.SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme`. The change of chart
`...ProjChartGradedClassifying.toProj_classifyingHom_comp_projInclusionMap`, on the other hand, is
stated for the classifying morphisms of `𝒜(Z)` and `𝒜(V)` themselves, and so does not apply to it.

This file removes that mismatch: `Fd.toProj_chartEquiv_mk` says that the chart-wise morphism of
`Fd.chartEquiv`, read into `Proj 𝒜(U)`, **is** the Tag 01N8 classifying morphism of the graded
ring `𝒜(U)` attached to the Veronese family of the quadruple, read across the same identification.
With it the change of chart is applicable to `Fd.chartEquiv`, which is what the descent of
[Stacks, Tag 01NU] along the charts — residue (i) of [Stacks, Tag 01NY] — needs.

## Main results

* `AlgebraicGeometry.Proj.congr_of_grading`, `AlgebraicGeometry.Proj.congr_index`,
  `AlgebraicGeometry.Proj.degreeOpen_heq_congr` and
  `AlgebraicGeometry.Proj.degreeOpen_heq_congr_index`: the congruences for
  `AlgebraicGeometry.Proj` and for `AlgebraicGeometry.Proj.degreeOpen` as an open of it, in the
  two shapes `AlgebraicGeometry.Proj.degreeOpen_toScheme_congr` and
  `...degreeOpen_toScheme_congr_index` of
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictDegreeOpen` have for the degree-`d`
  open alone.
* `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.toProj_classifyingHom_congr`: **the Tag 01N8
  classifying morphism transported along an identification of the graded ring**, with every
  instance an argument.
* `...RelativeProjQcohSheaf.restrict_ι_proj` and `...restrict_ι_degreeOpen_heq`: the
  identification `Proj Γ(⊤, A|_U) = Proj 𝒜(U)` and the heterogeneous equality of the two
  degree-`d` opens inside it.
* `...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_mk`: **the chart-wise morphism of a quadruple
  for `A|_U` is the Tag 01N8 classifying morphism of `𝒜(U)`**, as morphisms into `Proj 𝒜(U)`.

## Main definitions

* `...RelativeProjQcohSheaf.Fd.chartClass`: **the chart-wise class of a quadruple for `A` over an
  open `V` of the base** — the restriction of quadruples the change of chart consumes, in the
  shape that composes.

## Main results (continued)

* `...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_comp_projInclusionMap`: **the change of chart for
  the chart-wise representation of `F_d`** — for affine opens `Z ≤ U` of the base whose chart-wise
  quadruples have Veronese families related by `comapVeronese`, the chart-wise morphism of `Z`
  followed by the [Stacks, Tag 01NO] transition is the chart-wise morphism of `U`. That relation
  of the Veronese families is a hypothesis here and is **proved** for the chart-wise classes of
  one quadruple, as `...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting` of
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassComap`.

## Implementation notes

**Every instance is an argument, and none is compared.** The two gradings
`(A.restrict U.ι).grading ⊤` and `A.grading (U.ι ''ᵁ ⊤)` are the same term, by
`...SheafGradedAlgebra.restrict_grading`; their `GradedRing` instances are *not* the same term,
and comparing them makes the kernel unfold the whole `GradedRing`/`DirectSum` tower over
`A.sectionRing` and time out. The implementation notes of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictDegreeOpen` record that measurement
and the discipline it forces, which is followed here: the congruences below take the `GradedRing`
instance explicitly on each side and identify the two by
`AlgebraicGeometry.Proj.gradedRing_eq` — a `GradedRing` carries no choice — rather than by defeq,
and the five cheap identifications they consume are supplied as the named lemmas
`...SheafGradedAlgebra.restrict_ι_sectionRing_image` and its siblings.

**Why the datum is a hypothesis and not a transport.** The Veronese family of the quadruple is a
`...ProjChartFromRatios.VeroneseSections` for the grading of the *global* sections of `A|_U`, and
the conclusion speaks of one for `A.grading U`. Rather than form the transport, which would carry
the mismatched instance into the statement, `Fd.toProj_chartEquiv_mk` takes the family for
`A.grading U` as an argument together with a heterogeneous equality to the Veronese family — the
shape every caller can discharge by `cast`/`HEq.rfl` at the instance it already has.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u v w

namespace AlgebraicGeometry.Proj

/-- **The congruence for `AlgebraicGeometry.Proj` in its grading**, as schemes, in the shape
`AlgebraicGeometry.Proj.degreeOpen_toScheme_congr` has for the degree-`d` open: every datum of the
two sides is a separate argument — the carrier, the ring, the `CommRing` and `SetLike` instances,
the grading, and, explicitly, the `GradedRing` instance. The hypotheses compare the first five;
the `AddSubgroupClass` instances need no hypothesis, being proofs of a proposition, and the
`GradedRing` instances need none either, by `AlgebraicGeometry.Proj.gradedRing_eq`. -/
theorem congr_of_grading {σ₁ σ₂ : Type v} {R₁ R₂ : Type u}
    [cr₁ : CommRing R₁] [cr₂ : CommRing R₂] [sl₁ : SetLike σ₁ R₁] [sl₂ : SetLike σ₂ R₂]
    [asc₁ : AddSubgroupClass σ₁ R₁] [asc₂ : AddSubgroupClass σ₂ R₂]
    (𝒜 : ℕ → σ₁) (ℬ : ℕ → σ₂) (i : GradedRing 𝒜) (j : GradedRing ℬ)
    (hR : R₁ = R₂) (hσ : σ₁ = σ₂) (hcr : HEq cr₁ cr₂) (hsl : HEq sl₁ sl₂) (h𝒜 : HEq 𝒜 ℬ) :
    (@AlgebraicGeometry.Proj R₁ σ₁ cr₁ sl₁ asc₁ 𝒜 i)
      = (@AlgebraicGeometry.Proj R₂ σ₂ cr₂ sl₂ asc₂ ℬ j) := by
  subst hR
  subst hσ
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq hsl
  obtain rfl := eq_of_heq h𝒜
  obtain rfl := gradedRing_eq i j
  rfl

/-- **The congruence for `AlgebraicGeometry.Proj` along an equality of indices**, for a family of
graded rings indexed by a type: the projective spectra at two equal indices are the same scheme.
This is the half of an identification where nothing has to be unfolded and `subst` does all the
work. -/
theorem congr_index {ι : Type*} {σ : ι → Type v} {R : ι → Type u}
    [∀ a, CommRing (R a)] [∀ a, SetLike (σ a) (R a)] [∀ a, AddSubgroupClass (σ a) (R a)]
    (𝒜 : ∀ a, ℕ → σ a) [∀ a, GradedRing (𝒜 a)] {a b : ι} (h : a = b) :
    AlgebraicGeometry.Proj (𝒜 a) = AlgebraicGeometry.Proj (𝒜 b) := by
  subst h; rfl

/-- **The degree-`d` opens of two identified gradings are heterogeneously equal**, as opens of the
two projective spectra. The hypotheses are those of
`AlgebraicGeometry.Proj.congr_of_grading`. -/
theorem degreeOpen_heq_congr {σ₁ σ₂ : Type v} {R₁ R₂ : Type u}
    [cr₁ : CommRing R₁] [cr₂ : CommRing R₂] [sl₁ : SetLike σ₁ R₁] [sl₂ : SetLike σ₂ R₂]
    [asc₁ : AddSubgroupClass σ₁ R₁] [asc₂ : AddSubgroupClass σ₂ R₂]
    (𝒜 : ℕ → σ₁) (ℬ : ℕ → σ₂) (i : GradedRing 𝒜) (j : GradedRing ℬ)
    (hR : R₁ = R₂) (hσ : σ₁ = σ₂) (hcr : HEq cr₁ cr₂) (hsl : HEq sl₁ sl₂) (h𝒜 : HEq 𝒜 ℬ)
    (d : ℕ) :
    HEq (@AlgebraicGeometry.Proj.degreeOpen σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i d)
      (@AlgebraicGeometry.Proj.degreeOpen σ₂ R₂ cr₂ sl₂ asc₂ ℬ j d) := by
  subst hR
  subst hσ
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq hsl
  obtain rfl := eq_of_heq h𝒜
  obtain rfl := gradedRing_eq i j
  rfl

/-- **The degree-`d` opens at two equal indices of a family of graded rings are heterogeneously
equal**, as opens of the two projective spectra. -/
theorem degreeOpen_heq_congr_index {ι : Type*} {σ : ι → Type v} {R : ι → Type u}
    [∀ a, CommRing (R a)] [∀ a, SetLike (σ a) (R a)] [∀ a, AddSubgroupClass (σ a) (R a)]
    (𝒜 : ∀ a, ℕ → σ a) [∀ a, GradedRing (𝒜 a)] {a b : ι} (h : a = b) (d : ℕ) :
    HEq (AlgebraicGeometry.Proj.degreeOpen (𝒜 a) d)
      (AlgebraicGeometry.Proj.degreeOpen (𝒜 b) d) := by
  subst h; rfl

end AlgebraicGeometry.Proj

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### The inclusion of an open across an identification of the ambient scheme -/

/-- **The inclusion of an open commutes with an identification of the ambient scheme.** For
schemes identified by `hX` and opens of them identified by `hV`, the identification of the two
opens *as schemes* followed by the inclusion of the second is the inclusion of the first followed
by `hX`.

The equality of the two opens as schemes is an argument rather than derived from `hV`, so that a
caller can pass a proof it already has; by proof irrelevance any two proofs of it give the same
`CategoryTheory.eqToHom`. -/
theorem eqToHom_comp_ι {X X' : Scheme.{u}} (hX : X = X') {V : X.Opens} {V' : X'.Opens}
    (hV : HEq V V') (hVs : V.toScheme = V'.toScheme) :
    eqToHom hVs ≫ V'.ι = V.ι ≫ eqToHom hX := by
  subst hX
  obtain rfl := eq_of_heq hV
  simp

/-! ### The classifying morphism of Tag 01N8 across an identification of the graded ring -/

/-- **The classifying morphism of [Stacks, Tag 01N8] transported along an identification of the
graded ring.** The two gradings, their carriers, their rings and the `CommRing`/`SetLike`
instances are separate arguments compared by hypotheses, the `GradedRing` instance is explicit on
each side and is never compared, and the Tag 01N8 datum is given on each side together with a
heterogeneous equality.

Read into the two projective spectra, which the hypothesis `hProj` identifies, the two classifying
morphisms agree. See the implementation notes of this file for why every instance has to be an
argument. -/
theorem toProj_classifyingHom_congr {σ₁ σ₂ : Type w} {R₁ R₂ : Type u}
    [cr₁ : CommRing R₁] [cr₂ : CommRing R₂] [sl₁ : SetLike σ₁ R₁] [sl₂ : SetLike σ₂ R₂]
    [asc₁ : AddSubgroupClass σ₁ R₁] [asc₂ : AddSubgroupClass σ₂ R₂]
    (𝒜 : ℕ → σ₁) (ℬ : ℕ → σ₂) (i : GradedRing 𝒜) (j : GradedRing ℬ)
    (hR : R₁ = R₂) (hσ : σ₁ = σ₂) (hcr : HEq cr₁ cr₂) (hsl : HEq sl₁ sl₂) (h𝒜 : HEq 𝒜 ℬ)
    {d : ℕ} (hd : 0 < d) {Y : Scheme.{u}} {L : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y L]
    (ψ : @VeroneseSections σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i d Y L)
    (ψ' : @VeroneseSections σ₂ R₂ cr₂ sl₂ asc₂ ℬ j d Y L) (hψ : HEq ψ ψ')
    (hgen : ⨆ g : 𝒜 d, nonvanishingOpen Y L (@psiSection σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i d Y L ψ g) = ⊤)
    (hgen' : ⨆ g : ℬ d, nonvanishingOpen Y L (@psiSection σ₂ R₂ cr₂ sl₂ asc₂ ℬ j d Y L ψ' g) = ⊤)
    (hProj : (@AlgebraicGeometry.Proj R₁ σ₁ cr₁ sl₁ asc₁ 𝒜 i)
      = (@AlgebraicGeometry.Proj R₂ σ₂ cr₂ sl₂ asc₂ ℬ j)) :
    (@toProj σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i Y d
        (@classifyingHom σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i Y d L _ hd ψ hgen)) ≫ eqToHom hProj
      = @toProj σ₂ R₂ cr₂ sl₂ asc₂ ℬ j Y d
        (@classifyingHom σ₂ R₂ cr₂ sl₂ asc₂ ℬ j Y d L _ hd ψ' hgen') := by
  subst hR
  subst hσ
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq hsl
  obtain rfl := eq_of_heq h𝒜
  obtain rfl := AlgebraicGeometry.Proj.gradedRing_eq i j
  obtain rfl := eq_of_heq hψ
  simp

/-! ### The identification of the two projective spectra of an affine open of the base -/

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens)

/-- **The projective spectrum of the graded ring of global sections of `A|_U` is the projective
spectrum of the graded ring of sections of `A` over the image of `⊤`**, as schemes. The
restriction half of the identification. -/
theorem restrict_ι_proj_image :
    AlgebraicGeometry.Proj ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens))
      = AlgebraicGeometry.Proj (A.grading (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) :=
  AlgebraicGeometry.Proj.congr_of_grading _ _ _ _
    (SheafGradedAlgebra.restrict_ι_sectionRing_image A U)
    (SheafGradedAlgebra.restrict_ι_addSubgroup_eq A U)
    (SheafGradedAlgebra.restrict_ι_commRing_heq A U)
    (SheafGradedAlgebra.restrict_ι_setLike_heq A U)
    (SheafGradedAlgebra.restrict_ι_grading_heq A U)

/-- **The projective spectrum of the graded ring of global sections of `A|_U` is the projective
spectrum of `𝒜(U)`**, as schemes. This is the ambient identification
`...SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme` lives inside. -/
theorem restrict_ι_proj :
    AlgebraicGeometry.Proj ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens))
      = AlgebraicGeometry.Proj (A.grading U) :=
  (restrict_ι_proj_image A U).trans
    (AlgebraicGeometry.Proj.congr_index (fun W : S.Opens => A.grading W) U.ι_image_top)

/-- The degree-`d` open of the graded ring of global sections of `A|_U` and the degree-`d` open of
the graded ring of sections of `A` over the image of `⊤` are heterogeneously equal. -/
theorem restrict_ι_degreeOpen_heq_image (d : ℕ) :
    HEq (degreeOpen ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) d)
      (degreeOpen (A.grading (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) d) :=
  AlgebraicGeometry.Proj.degreeOpen_heq_congr _ _ _ _
    (SheafGradedAlgebra.restrict_ι_sectionRing_image A U)
    (SheafGradedAlgebra.restrict_ι_addSubgroup_eq A U)
    (SheafGradedAlgebra.restrict_ι_commRing_heq A U)
    (SheafGradedAlgebra.restrict_ι_setLike_heq A U)
    (SheafGradedAlgebra.restrict_ι_grading_heq A U) d

/-- **The degree-`d` open of the graded ring of global sections of `A|_U` and the degree-`d` open
of `𝒜(U)` are heterogeneously equal**, as opens of the two identified projective spectra. The
corresponding equality of the two *schemes* is
`...SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme`. -/
theorem restrict_ι_degreeOpen_heq (d : ℕ) :
    HEq (degreeOpen ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) d)
      (degreeOpen (A.grading U) d) :=
  (restrict_ι_degreeOpen_heq_image A U d).trans
    (AlgebraicGeometry.Proj.degreeOpen_heq_congr_index (fun W : S.Opens => A.grading W)
      U.ι_image_top d)

/-! ### The same four identifications at the open `U` itself

`...SheafGradedAlgebra.restrict_ι_sectionRing_image` and its siblings compare the global sections
of `A|_U` with the sections of `A` over the *image* `U.ι ''ᵁ ⊤`. The transport of the classifying
morphism consumes them at `U` itself, which is the image half composed with the index half; the
index half is proved by generalising the open to a variable, where `subst` applies. -/

/-- The carriers of the grading of the global sections of `A|_U` and of the grading of `𝒜(U)` are
the same type of additive subgroups. -/
theorem restrict_ι_addSubgroup_eq_top :
    (AddSubgroup ((A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)) : Type u)
      = AddSubgroup (A.sectionRing U) :=
  congrArg (fun W : S.Opens => (AddSubgroup (A.sectionRing W) : Type u)) U.ι_image_top

/-- The `CommRing` structure on the global sections of `A|_U` and the one on `𝒜(U)` agree. -/
theorem restrict_ι_commRing_heq_top :
    HEq (inferInstance : CommRing ((A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)))
      (inferInstance : CommRing (A.sectionRing U)) := by
  exact (SheafGradedAlgebra.restrict_ι_commRing_heq A U).trans
    (congr_arg_heq (fun W : S.Opens => (inferInstance : CommRing (A.sectionRing W)))
      U.ι_image_top)

/-- The `SetLike` structure on the additive subgroups of the global sections of `A|_U` and the one
on those of `𝒜(U)` agree. -/
theorem restrict_ι_setLike_heq_top :
    HEq (inferInstance :
        SetLike (AddSubgroup ((A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)))
          ((A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)))
      (inferInstance : SetLike (AddSubgroup (A.sectionRing U)) (A.sectionRing U)) := by
  exact (SheafGradedAlgebra.restrict_ι_setLike_heq A U).trans
    (congr_arg_heq (fun W : S.Opens =>
      (inferInstance : SetLike (AddSubgroup (A.sectionRing W)) (A.sectionRing W)))
      U.ι_image_top)

/-! ### The chart-wise morphism is a classifying morphism for the chart's graded ring -/

/-- **The chart-wise morphism of a quadruple for `A|_U` is the [Stacks, Tag 01N8] classifying
morphism of the graded ring `𝒜(U)`**, as morphisms into `Proj 𝒜(U)`.

`...RelativeProjQcohSheaf.Fd.chartEquiv` is the bijection of [Stacks, Tag 01NU] for the restricted
algebra `A|_U`, whose morphism is the Tag 01N8 classifying morphism of the graded ring of
*global* sections of `A|_U`, followed by the identification of schemes
`...SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme`. This says that identification carries it
to the Tag 01N8 classifying morphism of `𝒜(U)` attached to the same datum — the Veronese family
`...RelativeProjQcohSheaf.veroneseSections` of the quadruple, read at the grading of `𝒜(U)`.

That is what makes the change of chart
`...ProjChartGradedClassifying.toProj_classifyingHom_comp_projInclusionMap`, which is stated for
the classifying morphisms of the graded rings `𝒜(Z)`, `𝒜(V)` of homogeneous sections, applicable
to the chart-wise representation of `F_d`. -/
theorem Fd.toProj_chartEquiv_mk (hU : IsAffineOpen U) {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    (f : T ⟶ U.toScheme) (P : Quadruple f (situationAlgebra (A.restrict U.ι)) (k : ℤ))
    {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L] (hL : P.L = L)
    (ψ : VeroneseSections (A.grading U) k L)
    (hψ : HEq (veroneseSections P.twisting) ψ)
    (hgen : ⨆ g : A.grading U k,
      nonvanishingOpen T L (psiSection (A.grading U) ψ g) = ⊤) :
    toProj (A.grading U) (Fd.chartEquiv A U hU hk T (Fd.mk f P))
      = toProj (A.grading U) (classifyingHom (A.grading U) hk ψ hgen) := by
  subst hL
  have : IsAffine U.toScheme := hU
  have hqc : ∀ n : ℤ, ((situationAlgebra (A.restrict U.ι)).piece n).IsQuasicoherent :=
    fun n => (A.restrict U.ι).isQuasicoherent n
  show (classifyingHom ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) hk
          (veroneseSections P.twisting)
          (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc P)
        ≫ eqToHom (SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme A U k))
      ≫ (degreeOpen (A.grading U) k).ι = _
  rw [Category.assoc, eqToHom_comp_ι (restrict_ι_proj A U)
    (restrict_ι_degreeOpen_heq A U k)
    (SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme A U k), ← Category.assoc]
  exact toProj_classifyingHom_congr _ _ _ _
    (SheafGradedAlgebra.restrict_ι_sectionRing_top A U)
    (restrict_ι_addSubgroup_eq_top A U) (restrict_ι_commRing_heq_top A U)
    (restrict_ι_setLike_heq_top A U) (SheafGradedAlgebra.restrict_ι_grading_top A U)
    hk _ ψ hψ _ hgen (restrict_ι_proj A U)


/-! ### The change of chart for the chart-wise representation of `F_d` -/

/-- **The change of chart for the chart-wise representation of `F_d`.** Let `Z ≤ U` be affine opens
of the base, `T` a test scheme and `P_Z`, `P_U` quadruples over `T` of weight `k ≥ 1` for the
restricted algebras `A|_Z` and `A|_U`, with the *same* invertible module `L` on `T`. Suppose their
Veronese families are related by the restriction `𝒜(U) → 𝒜(Z)`, i.e. that the family of `P_U` is
`...ProjChartGradedClassifying.comapVeronese` of the family of `P_Z`. Then the chart-wise morphism
of `P_Z` into `Proj 𝒜(Z)`, followed by the transition morphism of [Stacks, Tag 01NO], is the
chart-wise morphism of `P_U` into `Proj 𝒜(U)`.

This is the agreement of the chart-wise morphisms of two affine opens of the base that the descent
of [Stacks, Tag 01NU] along the charts — residue (i) of [Stacks, Tag 01NY] — needs, read off the
change of chart `...ProjChartGradedClassifying.toProj_classifyingHom_comp_projInclusionMap` for the
classifying morphism of [Stacks, Tag 01N8] through `Fd.toProj_chartEquiv_mk`.

**What is a hypothesis here, and where it is discharged.** That the two Veronese families are
related by `comapVeronese` is assumed here, not constructed. It is **constructed** for the
chart-wise classes of one quadruple for `A` on `S`, by
`...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassComap`, out of the restriction of
quadruples `Fd.chartClass` below, the computation
`...RelativeProjQcohSheaf.veroneseSections_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassVeronese` of its Veronese family,
and the two transports the clause string names. So the change of chart is unconditional where it
is used, and what residue (i) over a general base still owes is not this but the Zariski sheaf
property of `F_d`; see the clause string. -/
theorem Fd.toProj_chartEquiv_comp_projInclusionMap {Z : S.Opens} (hZU : Z ≤ U)
    (hZ : IsAffineOpen Z) (hU : IsAffineOpen U) {k : ℕ} (hk : 0 < k) {T : Scheme.{u}}
    {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
    (fZ : T ⟶ Z.toScheme) (PZ : Quadruple fZ (situationAlgebra (A.restrict Z.ι)) (k : ℤ))
    (fU : T ⟶ U.toScheme) (PU : Quadruple fU (situationAlgebra (A.restrict U.ι)) (k : ℤ))
    (hLZ : PZ.L = L) (hLU : PU.L = L)
    (ψ : VeroneseSections (A.grading Z) k L)
    (hψZ : HEq (veroneseSections PZ.twisting) ψ)
    (hψU : HEq (veroneseSections PU.twisting)
      (ProjChartGradedClassifying.comapVeronese (A.res hZU) ψ))
    (hgen : ⨆ g : A.grading U k, nonvanishingOpen T L
      (psiSection (A.grading U) (ProjChartGradedClassifying.comapVeronese (A.res hZU) ψ) g) = ⊤) :
    toProj (A.grading Z) (Fd.chartEquiv A Z hZ hk T (Fd.mk fZ PZ))
        ≫ RelativeProj.projInclusionMap A Z U hZU hZ hU
      = toProj (A.grading U) (Fd.chartEquiv A U hU hk T (Fd.mk fU PU)) := by
  rw [Fd.toProj_chartEquiv_mk A Z hZ hk fZ PZ hLZ ψ hψZ
      (ProjChartGradedClassifying.iSup_nonvanishingOpen_psiSection_comapVeronese
        (A.res hZU) ψ hgen),
    Fd.toProj_chartEquiv_mk A U hU hk fU PU hLU _ hψU hgen]
  exact ProjChartGradedClassifying.toProj_classifyingHom_comp_projInclusionMap A hZU hZ hU ψ hk
    hgen


/-! ### The chart-wise class of a quadruple for `A` over an open of the base

This is the restriction of quadruples the change of chart above needs, in the only shape that
composes. The shape that does *not* is the obvious one: there is no map from quadruples for `A|_U`
to quadruples for `A|_Z` built from `...Fd.restrictPullbackEquiv` alone, because
`(A.restrict U.ι).restrict (S.homOfLE h)` is **not** `A.restrict Z.ι` — the two differ by
`Set.image_comp` on the image opens, and `rfl` for them fails. In the descent neither
chart class is obtained from the other: both come from **one** quadruple for `A` on `S`, each by a
single base change along the inclusion of its own affine open, and no composition of two
restrictions occurs. -/

/-- **The chart-wise class of a quadruple for `A` over an open `V` of the base.** A quadruple for
Situation 01NN's algebra `A` over a morphism factoring as `g_V ≫ V.ι : T ⟶ V ⟶ S` is, in two
steps, a point of `F_d(T)` for the *restriction* `A|_V`, whose projective spectrum is the chart of
`V`: `...RelativeProjQcohSheaf.Fd.baseChangeDownQ` of [Stacks, Tag 01NT] reads the class over the
chosen factorization as a class for the inverse image `V.ι^*A`, and
`...RelativeProjQcohSheaf.Fd.pullbackRestrictEquiv` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransport` carries that to the
restriction spelling.

This is the input of `Fd.chartEquiv`, and so the source of the chart-wise morphisms the descent of
[Stacks, Tag 01NU] along the charts glues. The class is taken over a *chosen* factorization
through `V`, as `Fd.baseChangeDownQ` is: that is what makes two different affine opens `Z ≤ U` of
the base produce classes of one quadruple without either being a restriction of the other. -/
def Fd.chartClass (V : S.Opens) {k : ℤ} {T : Scheme.{u}} (gV : T ⟶ V.toScheme)
    (q : Quotient (Quadruple.setoid (gV ≫ V.ι) (situationAlgebra A) k)) :
    Fd (situationAlgebra (A.restrict V.ι)) k T :=
  Fd.pullbackRestrictEquiv A V.ι k T (Fd.baseChangeDownQ V.ι (situationAlgebra A) k gV q)

/-- The morphism to the base recorded by a chart-wise class is the chosen factorization. -/
@[simp] theorem Fd.chartClass_fst (V : S.Opens) {k : ℤ} {T : Scheme.{u}} (gV : T ⟶ V.toScheme)
    (q : Quotient (Quadruple.setoid (gV ≫ V.ι) (situationAlgebra A) k)) :
    (Fd.chartClass A V gV q).1 = gV := rfl

/-- **The chart-wise class of the class of a quadruple is the class of its chart-wise quadruple**:
the base change of [Stacks, Tag 01NT] followed by the transport along the inverse of the
comparison `...RelativeProjQcohSheaf.restrictPullbackUnitalHom` of the two spellings of the
restriction.

This is the unfolding a computation of the Veronese family of a chart-wise class starts from. The
transport is along `...RelativeProjQcohSheaf.unitalHomInverse` of `restrictPullbackUnitalHom`,
which is the inverse of an adjoint transpose of the unit of the restriction adjunction, so the
value of the transported `ψ` on a global section is indeed not available by *unfolding* — but it
is available: `...RelativeProjQcohSheaf.veroneseSections_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassVeronese` computes it, and the
route reads the transported `ψ` on the restriction-adjunction *unit image* of a section of `𝒜`
over an open of the base, where only the forward maps occur and the inverse cancels against its
own forward component once. -/
theorem Fd.chartClass_mk (V : S.Opens) {k : ℤ} {T : Scheme.{u}} (gV : T ⟶ V.toScheme)
    (P : Quadruple (gV ≫ V.ι) (situationAlgebra A) k) :
    Fd.chartClass A V gV (Quotient.mk _ P)
      = Fd.mk gV ((P.baseChangeDown V.ι gV (situationAlgebra A) k).algebraTransport
          (unitalHomInverse (restrictPullbackUnitalHom A V.ι)
            (isIso_restrictPullbackUnitalHom_app_forall A V.ι))
          (isIso_unitalHomInverse_app (restrictPullbackUnitalHom A V.ι)
            (isIso_restrictPullbackUnitalHom_app_forall A V.ι))) := rfl

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
