module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassVeronese

/-!
# The chart-wise Veronese families of two nested opens of the base are related by restriction

Let `S` be a scheme, `A` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `Z ≤ U` opens of
`S` and `d ≥ 1`. `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.chartClass` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport` reads a quadruple
for `A` over a morphism `g : T ⟶ S` factoring through an open `V` of the base as a point of
`F_d(T)` for the restriction `A|_V`, and
`...RelativeProjQcohSheaf.veroneseSections_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassVeronese` computes the Veronese
family of that chart-wise class: on a homogeneous global section of `A|_V` it is the original
quadruple's transposed map over the open `V.ι ''ᵁ ⊤` of the base.

For `Z ≤ U` the Veronese family of the chart-wise class at `U` is
`...ProjChartGradedClassifying.comapVeronese` along the restriction `𝒜(U) → 𝒜(Z)` of the Veronese
family of the chart-wise class at `Z` (`chartVeronese_eq_comap`).

## Main results

* `...RelativeProjQcohSheaf.veroneseSections_ext`: two Veronese families with the same degreewise
  components agree.
* `...RelativeProjQcohSheaf.veroneseSections_toFun_heq` and
  `...RelativeProjQcohSheaf.exists_veroneseSections_heq`: **the Veronese family transported along
  an identification of the graded ring**, with every instance an argument and none compared; and
  `...RelativeProjQcohSheaf.veroneseSections_restrict_toFun_heq`,
  `...RelativeProjQcohSheaf.exists_veroneseSections_restrict` at the two spellings of the grading
  of the global sections of a restriction.
* `...RelativeProjQcohSheaf.Twisting.sectionHom_heq`: **the transposed maps of two heterogeneously
  equal twistings over equal base morphisms agree on sections.**
* `...RelativeProjQcohSheaf.chartTwisting`: the chart-wise transposed map, named.
* `...RelativeProjQcohSheaf.veroneseSections_chartTwisting_toFun_res`: **the chart-wise Veronese
  family at `Z`, on a restricted section, is the chart-wise Veronese family at `U`** — the
  computational core.
* `...RelativeProjQcohSheaf.chartVeronese_eq_comap`: **the Veronese family of the chart-wise class
  at `U` is `comapVeronese` of the one at `Z`.**

## Implementation notes

*The two factorizations.* One morphism `g : T ⟶ S` factors as `g_Z ≫ Z.ι` and as `g_U ≫ U.ι`, and
the transposed map of a twisting takes values in sections over the preimage of the open along the
base morphism, so the two factorizations give two *different terms* for one open of `T`. The
transport is `...RelativeProjQcohSheaf.Twisting.sectionHom_heq` below: two twistings that are
heterogeneously equal over two equal base morphisms have the same transposed map on sections, read
across any morphism between the two preimage opens. Which morphism does not matter — the category
of opens is thin — so it is an argument, as in `ChartClassVeronese`.

*The grading.* The Veronese family of a chart-wise class is a family for the grading
`(A.restrict V.ι).grading ⊤` of the global sections of `A|_V`, and `comapVeronese` of the
restriction `A.res` is one for `A.grading V`. The two gradings are the *same term* at the image
open `V.ι ''ᵁ ⊤` (`...SheafGradedAlgebra.restrict_grading` is `rfl`), and the remaining step from
`V.ι ''ᵁ ⊤` to `V` is an equality of opens. So every statement below takes that equality of opens
as a hypothesis with the open a *variable*, where `subst` applies; after it the two spellings of
each grading differ only in their `GradedRing` instance, which the transport lemmas
`veroneseSections_toFun_heq` and `exists_veroneseSections_heq` identify by
`AlgebraicGeometry.Proj.gradedRing_eq`.

**Every instance is an argument, and none is compared**, as in
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport`: the `GradedRing`
instances of the two spellings of a grading are not the same term, and comparing them unfolds the
whole `GradedRing`/`DirectSum` tower over `A.sectionRing` and times out the kernel.

**The restriction morphisms on the test scheme are arguments.** All the opens of `T` that occur are
equal to `⊤`, so every restriction map between the sections over them agrees by
`Subsingleton.elim`; rather than fix one, the statements take the morphism as an argument and
`...RelativeProjQcohSheaf.top_le_preimage_image_top` supplies one. For the same reason the proofs
compose the three restrictions that occur and then replace the composite by the one the statement
carries, rather than rewriting them one by one.

**The core computation is written in term mode.** Its goal mixes
`(A.restrict V.ι).sectionPieces ⊤` with `A.sectionPieces (V.ι ''ᵁ ⊤)` and
`(situationAlgebra A).piece (↑(n * k))` with `(situationAlgebra A).piece (↑n * ↑k)`; those are
equal by `rfl` but not at the `implicit` transparency `rw` checks its motives at, so `rw` reports
that it cannot find its pattern. `Eq.trans` and `congrArg` check the same identities at default
transparency.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u v

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### Restriction along an identity -/

/-- **A presheaf of modules restricts along an identity by the identity**, on sections. Stated
once, polymorphically, so that it can be applied by `exact` at whichever spelling of the open a
goal carries: `rw`ing an identity into place instead leaves the object of the identity in the
spelling the rewrite produced, which the `simp` normal form of `PresheafOfModules.map_id` does not
match. -/
theorem restrictₛₗ_id_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{v}}
    (M : PresheafOfModules.{u} R) {X : Cᵒᵖ} (x : M.obj X) : M.restrictₛₗ (𝟙 X) x = x := by
  simp

/-! ### Extensionality for a Veronese family -/

/-- **Two Veronese families with the same degreewise components agree.** The only other field of
`...ProjChartFromRatios.VeroneseSections` is a proposition. -/
theorem veroneseSections_ext {σ : Type v} {R : Type u} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}}
    {L : Y.Modules} {ψ ψ' : VeroneseSections 𝒜 d L}
    (h : ∀ (n : ℕ) (x : 𝒜 (n * d)), ψ.toFun n x = ψ'.toFun n x) : ψ = ψ' := by
  suffices hs : ∀ χ χ' : VeroneseSections 𝒜 d L, χ.toFun = χ'.toFun → χ = χ' from
    hs ψ ψ' (funext fun n => AddMonoidHom.ext (h n))
  rintro ⟨t, hm⟩ ⟨t', hm'⟩ ht
  obtain rfl : t = t' := ht
  rfl

/-! ### The Veronese family transported along an identification of the graded ring -/

/-- **The degreewise components of two heterogeneously equal Veronese families agree.** The two
gradings, their carriers, their rings and the `CommRing`/`SetLike` instances are separate
arguments compared by hypotheses, and the `GradedRing` instance is explicit on each side and is
never compared: the two are identified by `AlgebraicGeometry.Proj.gradedRing_eq`. See the
implementation notes of this file. -/
theorem veroneseSections_toFun_heq {σ₁ σ₂ : Type v} {R₁ R₂ : Type u}
    [cr₁ : CommRing R₁] [cr₂ : CommRing R₂] [sl₁ : SetLike σ₁ R₁] [sl₂ : SetLike σ₂ R₂]
    [asc₁ : AddSubgroupClass σ₁ R₁] [asc₂ : AddSubgroupClass σ₂ R₂]
    (𝒜 : ℕ → σ₁) (ℬ : ℕ → σ₂) (i : GradedRing 𝒜) (j : GradedRing ℬ)
    (hR : R₁ = R₂) (hσ : σ₁ = σ₂) (hcr : HEq cr₁ cr₂) (hsl : HEq sl₁ sl₂) (h𝒜 : HEq 𝒜 ℬ)
    {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
    (ψ : @VeroneseSections σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i d Y L)
    (ψ' : @VeroneseSections σ₂ R₂ cr₂ sl₂ asc₂ ℬ j d Y L) (hψ : HEq ψ ψ')
    (n : ℕ) (x : 𝒜 (n * d)) (y : ℬ (n * d)) (hxy : HEq x y) :
    ψ.toFun n x = ψ'.toFun n y := by
  subst hR
  subst hσ
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq hsl
  obtain rfl := eq_of_heq h𝒜
  obtain rfl := AlgebraicGeometry.Proj.gradedRing_eq i j
  obtain rfl := eq_of_heq hψ
  obtain rfl := eq_of_heq hxy
  rfl

/-- **A Veronese family can be read at an identified graded ring.** The hypotheses are those of
`veroneseSections_toFun_heq`; as there, no instance is compared. -/
theorem exists_veroneseSections_heq {σ₁ σ₂ : Type v} {R₁ R₂ : Type u}
    [cr₁ : CommRing R₁] [cr₂ : CommRing R₂] [sl₁ : SetLike σ₁ R₁] [sl₂ : SetLike σ₂ R₂]
    [asc₁ : AddSubgroupClass σ₁ R₁] [asc₂ : AddSubgroupClass σ₂ R₂]
    (𝒜 : ℕ → σ₁) (ℬ : ℕ → σ₂) (i : GradedRing 𝒜) (j : GradedRing ℬ)
    (hR : R₁ = R₂) (hσ : σ₁ = σ₂) (hcr : HEq cr₁ cr₂) (hsl : HEq sl₁ sl₂) (h𝒜 : HEq 𝒜 ℬ)
    {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
    (ψ : @VeroneseSections σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i d Y L) :
    ∃ ψ' : @VeroneseSections σ₂ R₂ cr₂ sl₂ asc₂ ℬ j d Y L, HEq ψ ψ' := by
  subst hR
  subst hσ
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq hsl
  obtain rfl := eq_of_heq h𝒜
  obtain rfl := AlgebraicGeometry.Proj.gradedRing_eq i j
  exact ⟨ψ, HEq.rfl⟩

/-! ### The two spellings of the grading of the global sections of a restriction -/

section Restrict

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens) {U' : S.Opens} {k : ℕ}
  {T : Scheme.{u}} (L : T.Modules)

/-- `veroneseSections_toFun_heq` at the two spellings of the grading of the global sections of
`A|_U`. The open `U'` the second grading is read at is a variable given with the equality
`U.ι ''ᵁ ⊤ = U'`, which `subst` removes; the five identifications that are left are
`...SheafGradedAlgebra.restrict_ι_sectionRing_image` and its siblings. -/
theorem veroneseSections_restrict_toFun_heq
    (hU' : U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = U')
    (ψ : VeroneseSections ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) k L)
    (ψ' : VeroneseSections (A.grading U') k L) (hψ : HEq ψ ψ') (n : ℕ)
    (x : (A.restrict U.ι).grading (⊤ : U.toScheme.Opens) (n * k))
    (y : A.grading U' (n * k)) (hxy : HEq x y) :
    ψ.toFun n x = ψ'.toFun n y := by
  subst hU'
  exact veroneseSections_toFun_heq _ _ _ _
    (SheafGradedAlgebra.restrict_ι_sectionRing_image A U)
    (SheafGradedAlgebra.restrict_ι_addSubgroup_eq A U)
    (SheafGradedAlgebra.restrict_ι_commRing_heq A U)
    (SheafGradedAlgebra.restrict_ι_setLike_heq A U)
    (SheafGradedAlgebra.restrict_ι_grading_heq A U) ψ ψ' hψ n x y hxy

/-- A Veronese family for the grading of the global sections of `A|_U` read at the grading of
`𝒜(U')`, for any open `U'` the image `U.ι ''ᵁ ⊤` is known to be. -/
theorem exists_veroneseSections_restrict
    (hU' : U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = U')
    (ψ : VeroneseSections ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) k L) :
    ∃ ψ' : VeroneseSections (A.grading U') k L, HEq ψ ψ' := by
  subst hU'
  exact exists_veroneseSections_heq _ _ _ _
    (SheafGradedAlgebra.restrict_ι_sectionRing_image A U)
    (SheafGradedAlgebra.restrict_ι_addSubgroup_eq A U)
    (SheafGradedAlgebra.restrict_ι_commRing_heq A U)
    (SheafGradedAlgebra.restrict_ι_setLike_heq A U)
    (SheafGradedAlgebra.restrict_ι_grading_heq A U) ψ

/-- `veroneseSections_restrict_toFun_heq` with one and the same element on both sides, at the
image open itself. -/
theorem veroneseSections_restrict_toFun_image
    (ψ : VeroneseSections ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) k L)
    (ψ' : VeroneseSections
      (A.grading (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) k L)
    (hψ : HEq ψ ψ') (n : ℕ)
    (y : A.grading (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)) (n * k)) :
    ψ.toFun n y = ψ'.toFun n y :=
  veroneseSections_restrict_toFun_heq A U L rfl ψ ψ' hψ n y y HEq.rfl

end Restrict

/-! ### The transposed map of a twisting read over an equal base morphism -/

namespace Twisting

variable {T S : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **Two heterogeneously equal twistings over two equal base morphisms have the same transposed
map on sections.** The target of `...RelativeProjQcohSheaf.Twisting.sectionHom` mentions the base
morphism — the values are sections over its preimage of the open — so the two values live on two
different terms for one open of `T`. This says they agree across any morphism between those two
opens; all such morphisms agree, the category of opens being thin, so the morphism is an
argument.

This is what reconciles the two factorizations `g_Z ≫ Z.ι` and `g_U ≫ U.ι` of one morphism
`T ⟶ S` in the comparison of two charts. -/
theorem sectionHom_heq {g g' : T ⟶ S} (hg : g = g') (χ : Twisting g A d L)
    (χ' : Twisting g' A d L) (hχ : HEq χ χ') (i : ℤ)
    (W : (Opens S.toRingedSpace.carrier)ᵒᵖ) (x : (A.piece (i * d)).val.obj W)
    (e : ((opensMap (ringedSpaceHom g)).op.obj W) ⟶ ((opensMap (ringedSpaceHom g')).op.obj W)) :
    χ'.sectionHom i W x
      = ((laurent L).piece i).val.restrictₛₗ e (χ.sectionHom i W x) := by
  subst hg
  obtain rfl := eq_of_heq hχ
  refine Eq.trans ?_ (congrArg
    (fun r => ((laurent L).piece i).val.restrictₛₗ r (χ.sectionHom i W x))
    (Subsingleton.elim (𝟙 ((opensMap (ringedSpaceHom g)).op.obj W)) e))
  exact (restrictₛₗ_id_apply ((laurent L).piece i).val (χ.sectionHom i W x)).symm

end Twisting

/-! ### The chart-wise transposed map -/

section Chart

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (V : S.Opens) {k : ℕ} {T : Scheme.{u}}
  (gV : T ⟶ V.toScheme) {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-- **The transposed map of the chart-wise class of a quadruple**, named: the map `ψ` of a
quadruple for `A` over a morphism factoring as `g_V ≫ V.ι : T ⟶ V ⟶ S`, base-changed along `V.ι`
by [Stacks, Tag 01NT] and then transported along the inverse comparison of the two spellings of
the restriction. This is the twisting of `...RelativeProjQcohSheaf.Fd.chartClass`, by
`...RelativeProjQcohSheaf.Fd.chartClass_mk`. -/
def chartTwisting (χ : Twisting (gV ≫ V.ι) (situationAlgebra A) (k : ℤ) L) :
    Twisting gV (situationAlgebra (A.restrict V.ι)) (k : ℤ) L :=
  Twisting.algebraTransport
    (unitalHomInverse (restrictPullbackUnitalHom A V.ι)
      (isIso_restrictPullbackUnitalHom_app_forall A V.ι))
    (χ.baseChangeDown V.ι gV (situationAlgebra A) (k : ℤ))

/-- `...RelativeProjQcohSheaf.veroneseSections_chartTwisting` at the named chart-wise transposed
map: the Veronese family of a chart-wise class, evaluated on a homogeneous global section of
`A|_V`, is the original quadruple's transposed map over the open `V.ι ''ᵁ ⊤` of the base. -/
theorem veroneseSections_chartTwisting'
    (χ : Twisting (gV ≫ V.ι) (situationAlgebra A) (k : ℤ) L) (n : ℕ)
    (a : (A.restrict V.ι).grading (⊤ : V.toScheme.Opens) (n * k))
    (e : (op ((opensMap (ringedSpaceHom (gV ≫ V.ι))).obj
            (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)))
          : (Opens T.toRingedSpace.carrier)ᵒᵖ) ⟶ op (⊤ : Opens T.toRingedSpace.carrier)) :
    (veroneseSections (chartTwisting A V gV χ)).toFun n a
      = (powCompare L n).inv.app ⊤
          (((laurent L).piece (n : ℤ)).val.restrictₛₗ e
            (χ.sectionHom (n : ℤ)
              (op (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)))
              ((a : (A.restrict V.ι).sectionRing (⊤ : V.toScheme.Opens)) (n * k)))) :=
  veroneseSections_chartTwisting A V gV χ n a e

end Chart

/-! ### The chart-wise Veronese families at two nested opens -/

section Comap

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) {Z U : S.Opens} {k : ℕ} {T : Scheme.{u}}
  (gZ : T ⟶ Z.toScheme) (gU : T ⟶ U.toScheme) {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L]

/-- **The computational core: the chart-wise Veronese family at `Z`, on a restricted section, is
the chart-wise Veronese family at `U`.** Let `g_Z ≫ Z.ι = g_U ≫ U.ι` be two factorizations of one
morphism `T ⟶ S` and let `χ_U`, `χ_Z` be heterogeneously equal twistings over them. Then the
Veronese family of the chart-wise class at `Z` evaluated on a homogeneous global section of `A|_Z`
which is the restriction of one of `A|_U` agrees with the Veronese family of the chart-wise class
at `U` evaluated on the latter.

Three inputs. `veroneseSections_chartTwisting'` computes both sides as the transposed map of the
twisting over the image opens; `...RelativeProjQcohSheaf.sectionHom_resPiece` moves the
restriction of the graded ring of sections past the transposed map; and `Twisting.sectionHom_heq`
reconciles the two factorizations. What is left is three restriction maps on `T` composing to a
fourth, and all four agree because the category of opens is thin. -/
theorem veroneseSections_chartTwisting_toFun_res
    (hZU : Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier)
      ≤ U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))
    (hbase : gU ≫ U.ι = gZ ≫ Z.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χZ : Twisting (gZ ≫ Z.ι) (situationAlgebra A) (k : ℤ) L) (hχ : HEq χU χZ) (n : ℕ)
    (a : (A.restrict U.ι).grading (⊤ : U.toScheme.Opens) (n * k))
    (b : (A.restrict Z.ι).grading (⊤ : Z.toScheme.Opens) (n * k))
    (hab : (b : (A.restrict Z.ι).sectionRing (⊤ : Z.toScheme.Opens)) (n * k)
      = A.resPiece hZU (n * k)
          ((a : (A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)) (n * k))) :
    (veroneseSections (chartTwisting A Z gZ χZ)).toFun n b
      = (veroneseSections (chartTwisting A U gU χU)).toFun n a := by
  set a' := (a : (A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)) (n * k) with ha'
  set X := χU.sectionHom (n : ℤ)
    (op (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) a' with hX
  set eZ := (homOfLE (top_le_preimage_image_top (V := Z) (gV := gZ))).op with heZ
  set eU := (homOfLE (top_le_preimage_image_top (V := U) (gV := gU))).op with heU
  set mU := (opensMap (ringedSpaceHom (gU ≫ U.ι))).op.map (homOfLE hZU).op with hmU
  set e₁ := eqToHom (congrArg
    (fun w : T ⟶ S => ((opensMap (ringedSpaceHom w)).op.obj
      (op (Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier)))
        : (Opens T.toRingedSpace.carrier)ᵒᵖ)) hbase) with he₁
  have hZcomp : χZ.sectionHom (n : ℤ)
        (op (Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier)))
        (A.resPiece hZU (n * k) a')
      = ((laurent L).piece (n : ℤ)).val.restrictₛₗ e₁
          (((laurent L).piece (n : ℤ)).val.restrictₛₗ mU X) :=
    (Twisting.sectionHom_heq hbase χU χZ hχ (n : ℤ)
          (op (Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier)))
          (A.resPiece hZU (n * k) a') e₁).trans
      (congrArg (fun z => ((laurent L).piece (n : ℤ)).val.restrictₛₗ e₁ z)
        (sectionHom_resPiece A χU n hZU a'))
  refine Eq.trans (veroneseSections_chartTwisting' A Z gZ χZ n b eZ) ?_
  refine Eq.trans ?_ (veroneseSections_chartTwisting' A U gU χU n a eU).symm
  refine congrArg (fun z => (powCompare L n).inv.app ⊤ z) ?_
  refine Eq.trans (congrArg
    (fun y => ((laurent L).piece (n : ℤ)).val.restrictₛₗ eZ
      (χZ.sectionHom (n : ℤ)
        (op (Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier))) y)) hab) ?_
  refine Eq.trans (congrArg
    (fun z => ((laurent L).piece (n : ℤ)).val.restrictₛₗ eZ z) hZcomp) ?_
  refine Eq.trans
    (PresheafOfModules.map_comp_apply ((laurent L).piece (n : ℤ)).val e₁ eZ _).symm ?_
  refine Eq.trans
    (PresheafOfModules.map_comp_apply ((laurent L).piece (n : ℤ)).val mU (e₁ ≫ eZ) X).symm ?_
  exact congrArg (fun r => ((laurent L).piece (n : ℤ)).val.restrictₛₗ r X)
    (Subsingleton.elim _ eU)

/-- **The chart-wise Veronese family at `Z` on the restriction of a section, paired with the
section.** `veroneseSections_chartTwisting_toFun_res` with the element of `𝒜(Z.ι ''ᵁ ⊤)` taken to
be the image of the one of `𝒜(U.ι ''ᵁ ⊤)` under the restriction `A.res`, whose degreewise
description is `...SheafGradedAlgebra.resRingHom_apply`. Its own declaration for the reason
`veroneseSections_restrict_toFun_image` is. -/
theorem veroneseSections_chartTwisting_toFun_comap
    (hZU : Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier)
      ≤ U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))
    (hbase : gU ≫ U.ι = gZ ≫ Z.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χZ : Twisting (gZ ≫ Z.ι) (situationAlgebra A) (k : ℤ) L) (hχ : HEq χU χZ) (n : ℕ)
    (y : A.grading (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)) (n * k)) :
    (veroneseSections (chartTwisting A Z gZ χZ)).toFun n
        ⟨A.res hZU (y : A.sectionRing (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))),
          GradedRingHom.map_mem (A.res hZU) y.2⟩
      = (veroneseSections (chartTwisting A U gU χU)).toFun n y :=
  veroneseSections_chartTwisting_toFun_res A gZ gU hZU hbase χU χZ hχ n y _
    (A.resRingHom_apply hZU
      (y : A.sectionRing (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) (n * k))

/-- **`chartVeronese_eq_comap` degreewise, at the image opens.** -/
theorem chartVeronese_image_toFun_eq_comap_toFun
    (hZU : Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier)
      ≤ U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))
    (hbase : gU ≫ U.ι = gZ ≫ Z.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χZ : Twisting (gZ ≫ Z.ι) (situationAlgebra A) (k : ℤ) L) (hχ : HEq χU χZ)
    (ψZ : VeroneseSections
      (A.grading (Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier))) k L)
    (ψU : VeroneseSections
      (A.grading (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier))) k L)
    (hψZ : HEq (veroneseSections (chartTwisting A Z gZ χZ)) ψZ)
    (hψU : HEq (veroneseSections (chartTwisting A U gU χU)) ψU)
    (n : ℕ)
    (y : A.grading (U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier)) (n * k)) :
    ψU.toFun n y = (ProjChartGradedClassifying.comapVeronese (A.res hZU) ψZ).toFun n y :=
  ((veroneseSections_restrict_toFun_image A U L _ ψU hψU n y).symm.trans
      (veroneseSections_chartTwisting_toFun_comap A gZ gU hZU hbase χU χZ hχ n y).symm).trans
    (veroneseSections_restrict_toFun_image A Z L _ ψZ hψZ n _)

/-- **`chartVeronese_eq_comap` degreewise.** Split off as its own declaration: the degreewise
identity and the extensionality each carry their own comparison of the two spellings of a
grading, and together they exceed the heartbeat budget of one declaration. -/
theorem chartVeronese_toFun_eq_comap_toFun {Z' U' : S.Opens}
    (hZ' : Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier) = Z')
    (hU' : U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = U') (hZU : Z' ≤ U')
    (hbase : gU ≫ U.ι = gZ ≫ Z.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χZ : Twisting (gZ ≫ Z.ι) (situationAlgebra A) (k : ℤ) L) (hχ : HEq χU χZ)
    (ψZ : VeroneseSections (A.grading Z') k L) (ψU : VeroneseSections (A.grading U') k L)
    (hψZ : HEq (veroneseSections (chartTwisting A Z gZ χZ)) ψZ)
    (hψU : HEq (veroneseSections (chartTwisting A U gU χU)) ψU)
    (n : ℕ) (y : A.grading U' (n * k)) :
    ψU.toFun n y = (ProjChartGradedClassifying.comapVeronese (A.res hZU) ψZ).toFun n y := by
  subst hZ'
  subst hU'
  exact chartVeronese_image_toFun_eq_comap_toFun A gZ gU hZU hbase χU χZ hχ ψZ ψU hψZ hψU n y

/-- **The Veronese family of the chart-wise class at `U` is `comapVeronese` of the one at `Z`.**
For `Z' ≤ U'` the images of the two opens, two factorizations `g_Z ≫ Z.ι = g_U ≫ U.ι` of one
morphism `T ⟶ S`, and heterogeneously equal twistings `χ_U`, `χ_Z` over them, the Veronese
families of the chart-wise classes at `Z` and at `U`, read at the gradings `𝒜(Z')` and `𝒜(U')` of
homogeneous sections, are related by `...ProjChartGradedClassifying.comapVeronese` along the
restriction `𝒜(U') → 𝒜(Z')`. The opens `Z'`, `U'` are given together with the equalities
`Z.ι ''ᵁ ⊤ = Z'` and `U.ι ''ᵁ ⊤ = U'`. -/
theorem chartVeronese_eq_comap {Z' U' : S.Opens}
    (hZ' : Z.ι ''ᵁ (⊤ : Opens Z.toScheme.toRingedSpace.carrier) = Z')
    (hU' : U.ι ''ᵁ (⊤ : Opens U.toScheme.toRingedSpace.carrier) = U') (hZU : Z' ≤ U')
    (hbase : gU ≫ U.ι = gZ ≫ Z.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χZ : Twisting (gZ ≫ Z.ι) (situationAlgebra A) (k : ℤ) L) (hχ : HEq χU χZ)
    (ψZ : VeroneseSections (A.grading Z') k L) (ψU : VeroneseSections (A.grading U') k L)
    (hψZ : HEq (veroneseSections (chartTwisting A Z gZ χZ)) ψZ)
    (hψU : HEq (veroneseSections (chartTwisting A U gU χU)) ψU) :
    ψU = ProjChartGradedClassifying.comapVeronese (A.res hZU) ψZ :=
  veroneseSections_ext fun n y =>
    chartVeronese_toFun_eq_comap_toFun A gZ gU hZ' hU' hZU hbase χU χZ hχ ψZ ψU hψZ hψU n y

/-- For `Z ≤ U` opens of the base, two factorizations `g_Z ≫ Z.ι = g_U ≫ U.ι` of one morphism
`T ⟶ S` and heterogeneously equal twistings over them, a Veronese family `ψ_Z` for `𝒜(Z)`
heterogeneously equal to the one of the chart-wise class at `Z` determines the one of the
chart-wise class at `U`: it is `comapVeronese` of `ψ_Z` along the restriction `𝒜(U) → 𝒜(Z)`. -/
theorem heq_comapVeronese_chartTwisting (hZU : Z ≤ U) (hbase : gU ≫ U.ι = gZ ≫ Z.ι)
    (χU : Twisting (gU ≫ U.ι) (situationAlgebra A) (k : ℤ) L)
    (χZ : Twisting (gZ ≫ Z.ι) (situationAlgebra A) (k : ℤ) L) (hχ : HEq χU χZ)
    (ψZ : VeroneseSections (A.grading Z) k L)
    (hψZ : HEq (veroneseSections (chartTwisting A Z gZ χZ)) ψZ) :
    HEq (veroneseSections (chartTwisting A U gU χU))
      (ProjChartGradedClassifying.comapVeronese (A.res hZU) ψZ) := by
  obtain ⟨ψU, hψU⟩ := exists_veroneseSections_restrict A U L U.ι_image_top
    (veroneseSections (chartTwisting A U gU χU))
  exact hψU.trans (heq_of_eq (chartVeronese_eq_comap A gZ gU Z.ι_image_top U.ι_image_top hZU
    hbase χU χZ hχ ψZ ψU hψZ hψU))

end Comap

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
