module

public import StacksFrontier.AlgebraicGeometry.Blowup.SecondCentreExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAffineChartRees
import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
import StacksFrontier.AlgebraicGeometry.Spaces.BlowupReesProjContains
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback
import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange

/-!
# The second centre of a blowup of an algebraic space, on a chart

Let `X` be a quasi-compact algebraic space over `S`, let `Z ⊆ X` be a closed subspace of finite
presentation, let `b : X' ⟶ X` be the blowup of `X` in `Z` (Stacks 085U) with exceptional
divisor `E = b⁻¹(Z)`, and let `Z' ⊆ X'` be a closed subspace of finite presentation.  Write
`Z' + dE` for the sum of Stacks 083U of `Z'` with `d` copies of `E` and `C_d ⊆ X` for the
scheme-theoretic image (Stacks 082X) of `Z' + dE ⟶ X`.  The local computation behind Stacks
0860 (through 085R) is that for some `d > 0`

`b⁻¹(C_d) = Z' + dE`,

and that on an affine étale chart `V` of `X`, over which `b` is the scheme blowup
`U' = V ×_X X' ⟶ V`, this is cut out by a finite type ideal `J ⊆ 𝓘_Z^d` on `V` with
`b⁻¹J · 𝒪_{U'} = 𝓘_E^d · 𝓘_{Z'}`, the scheme-level second centre of Stacks 080B.

## Main definitions

* `AlgebraicGeometry.Space.exceptionalSum`: the closed subspace `Z' + dE` of `X'`.
* `AlgebraicGeometry.Space.exceptionalSumImage`: its scheme-theoretic image `C_d` in `X`.

## Main results

* `AlgebraicGeometry.Space.exists_chart_secondCentre`: the whole statement on the chart: the
  affine chart, the cartesian square, `d`, `J`, the inclusion `J ⊆ 𝓘_{C_d}`, the criterion
  `J ⊆ 𝓘_T ⟹ b⁻¹(T) ⊆ Z' + dE`, the equality `b⁻¹(C_d) = Z' + dE` and its chart form
  `𝓘_{Z' + dE}|_{U'} = π⁻¹𝓘_{C_d}|_V · 𝒪_{U'}`.
* `AlgebraicGeometry.Space.exists_preimage_exceptionalSumImage_eq`: `b⁻¹(C_d) = Z' + dE`.
* `AlgebraicGeometry.Space.exists_chart_le_chartKer_exceptionalSumImage`: the chart clauses in
  the form used to approximate `C_d` by a finitely presented closed subspace.
* `AlgebraicGeometry.Space.le_chartKer_exceptionalSumImage_and_of_comap_eq`: the chart argument
  itself, for an arbitrary quasi-compact `b` and cartesian chart square.

Along the way:

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_injective_of_flat_of_surjective`: inverse
  image of ideal sheaves along a flat surjective morphism of schemes is injective.
* `AlgebraicGeometry.Space.chartKer_sumClosedSubspaces_eq_mul`: on *every* scheme chart the
  chart ideal sheaf of a sum is the product of those of the summands (Stacks 083U).
* `AlgebraicGeometry.Space.le_of_chartKer_le`: an inclusion of closed subspaces may be checked
  on the chart ideal sheaves of one surjective étale chart.
* `Stacks.Blowup.exists_secondCentre_of_iso`: Stacks 080B for a blowup named up to
  isomorphism over the base.

## Implementation notes

The degree `d` is the one of the scheme-level second centre, so that `J` itself satisfies
`π⁻¹J · 𝒪_{U'} = 𝓘_{Z' + dE}` and no power of `𝓘_Z` has to be adjoined.  The inclusion
`J ⊆ 𝓘_{C_d}` is where flatness is used: the scheme-theoretic image of the quasi-compact
morphism `Z' + dE ⟶ X` commutes with the flat base change `V ⟶ X` (Stacks 089E), and on `V`
the image is contained in the closed subscheme `V(J)` because `Z' + dE` lies over it.  The
quasi-compactness of `b` is Stacks 085Z, and the three site-size side conditions of the
construction of Stacks 085Q are discharged by
`AlgebraicGeometry.Space.contains_reesProj_of_isFinitePresentation`.

## References

* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
* [Stacks Project, Tag 085R](https://stacks.math.columbia.edu/tag/085R)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 085Z](https://stacks.math.columbia.edu/tag/085Z)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 089E](https://stacks.math.columbia.edu/tag/089E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Faithfully flat morphisms detect ideal sheaves -/

/-- **The kernel of a flat surjective morphism of schemes is zero.** A flat morphism is
injective on stalks, and every point of the target is the image of a point of the source. -/
theorem Scheme.Hom.ker_eq_bot_of_flat_of_surjective {V W : Scheme.{u}} (q : V ⟶ W) [Flat q]
    [Surjective q] : q.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : W.affineOpens ↦ U)
    (iSup_affineOpens_eq_top W) fun U ↦ ?_
  simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  refine le_antisymm (fun s hs ↦ ?_) bot_le
  have h0 : (q.app U.1).hom s = 0 := q.ideal_ker_le U hs
  have key (y : V) (hy : q y ∈ U.1) : W.presheaf.germ U.1 (q y) hy s = 0 := by
    refine q.stalkMap_injective_of_flat y ?_
    rw [map_zero, Scheme.Hom.germ_stalkMap_apply, h0, map_zero]
  refine Ideal.mem_bot.mpr (TopCat.Presheaf.section_ext W.sheaf U.1 s 0 fun x hx ↦ ?_)
  obtain ⟨y, rfl⟩ := Surjective.surj (f := q) x
  rw [map_zero]
  exact key y hx

/-- **An ideal sheaf is the direct image of its inverse image along a flat surjective
morphism.** -/
theorem Scheme.IdealSheafData.map_comap_of_flat_of_surjective {V W : Scheme.{u}} (q : V ⟶ W)
    [Flat q] [Surjective q] (I : W.IdealSheafData) : (I.comap q).map q = I := by
  have h1 : (I.comap q).subschemeι ≫ q =
      (I.comapIso q).hom ≫ pullback.snd q I.subschemeι ≫ I.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst I q, Category.assoc, pullback.condition]
  calc (I.comap q).map q
      = ((I.comap q).subschemeι ≫ q).ker := by
        rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι]
    _ = ((I.comapIso q).hom ≫ pullback.snd q I.subschemeι ≫ I.subschemeι).ker := by rw [h1]
    _ = (pullback.snd q I.subschemeι ≫ I.subschemeι).ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = (pullback.snd q I.subschemeι).ker.map I.subschemeι :=
        (Scheme.IdealSheafData.map_ker _ _).symm
    _ = I := by
        rw [Scheme.Hom.ker_eq_bot_of_flat_of_surjective, Scheme.IdealSheafData.map_bot,
          Scheme.IdealSheafData.ker_subschemeι]

/-- **The inverse image of ideal sheaves along a flat surjective morphism is injective.** -/
theorem Scheme.IdealSheafData.comap_injective_of_flat_of_surjective {V W : Scheme.{u}}
    (q : V ⟶ W) [Flat q] [Surjective q] {I J : W.IdealSheafData}
    (h : I.comap q = J.comap q) : I = J := by
  rw [← map_comap_of_flat_of_surjective q I, ← map_comap_of_flat_of_surjective q J, h]

end AlgebraicGeometry

namespace Stacks.Blowup

open _root_.AlgebraicGeometry

/-- **The second centre, for a blowup named up to isomorphism over the base.** -/
theorem exists_secondCentre_of_iso {Y T : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : Y.IdealSheafData) (hI : I.IsFiniteType) (g : T ⟶ Y)
    (e : T ≅ AlgebraicGeometry.blowUp I) (he : e.hom ≫ AlgebraicGeometry.blowUpToBase I = g)
    (Z : T.IdealSheafData) (hZ : Z.IsFiniteType) :
    ∃ (d : ℕ) (J : Y.IdealSheafData), 0 < d ∧ J.IsFiniteType ∧ J ≤ I ^ d ∧
      J.comap g = I.comap g ^ d * Z := by
  obtain ⟨d, J, hd, hJ, hJI, hJZ⟩ := exists_secondCentre I hI (Z.comap e.inv) (hZ.comap _)
  refine ⟨d, J, hd, hJ, hJI, ?_⟩
  have h2 : (Z.comap e.inv).comap e.hom = Z := by
    rw [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id]
  rw [← he, Scheme.IdealSheafData.comap_comp, hJZ, Stacks.IdealSheaf.comap_mul,
    Stacks.IdealSheaf.comap_pow, h2, Scheme.IdealSheafData.comap_comp]

end Stacks.Blowup

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_BlowupSecondCentreChart :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_BlowupSecondCentreChart
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Closed immersions of the site and their kernels -/

/-- **Every ideal sheaf on a scheme of the site is the kernel of a closed immersion of the
site.** The closed subscheme it cuts out is no larger than the scheme, hence in the site. -/
theorem exists_isClosedImmersion_ker_eq {V : BigFppfOver B S hS}
    (K : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData) :
    ∃ (R : BigFppfOver B S hS) (q : R ⟶ V),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q) ∧
      ((BigFppfOver.toScheme B S hS).map q).ker = K := by
  have hI : B.Contains K.subscheme :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact K.subschemeι) V.left.property
  let qI : B.obj hI ⟶ V.left := B.inclusion.preimage (X := B.obj hI) (Y := V.left)
    K.subschemeι
  have hqI : B.inclusion.map qI = K.subschemeι :=
    B.inclusion.map_preimage (X := B.obj hI) (Y := V.left) K.subschemeι
  refine ⟨Over.mk (qI ≫ V.hom), Over.homMk qI, ?_, ?_⟩
  · show AlgebraicGeometry.IsClosedImmersion (B.inclusion.map qI)
    rw [hqI]; infer_instance
  · show (B.inclusion.map qI).ker = _
    rw [hqI, Scheme.IdealSheafData.ker_subschemeι]

/-- **Ranges of represented morphisms compare oppositely to kernels.** -/
theorem ker_le_of_range_yoneda_map_le {T R V : BigFppfOver B S hS} (j : R ⟶ V) (g : T ⟶ V)
    (h : Subfunctor.range (yoneda.map g) ≤ Subfunctor.range (yoneda.map j)) :
    ((BigFppfOver.toScheme B S hS).map j).ker ≤ ((BigFppfOver.toScheme B S hS).map g).ker := by
  obtain ⟨l, hl⟩ := h (op T) (show g ∈ (Subfunctor.range (yoneda.map g)).obj (op T) from
    ⟨𝟙 T, by simp⟩)
  change l ≫ j = g at hl
  rw [← hl, (BigFppfOver.toScheme B S hS).map_comp]
  exact Scheme.Hom.le_ker_comp _ _

/-- **A morphism of the site factors through a closed immersion of the site whose kernel is
contained in its own.** -/
theorem exists_comp_eq_of_ker_le_of_isClosedImmersion {T R V : BigFppfOver B S hS} (j : R ⟶ V)
    (g : T ⟶ V)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (h : ((BigFppfOver.toScheme B S hS).map j).ker ≤
      ((BigFppfOver.toScheme B S hS).map g).ker) :
    ∃ l : T ⟶ R, l ≫ j = g := by
  set k := IsClosedImmersion.lift ((BigFppfOver.toScheme B S hS).map j)
    ((BigFppfOver.toScheme B S hS).map g) h
  have hk : k ≫ (BigFppfOver.toScheme B S hS).map j = (BigFppfOver.toScheme B S hS).map g :=
    IsClosedImmersion.lift_fac _ _ h
  have hk₀ : B.inclusion.preimage k ≫ j.left = g.left := by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp, B.inclusion.map_preimage k]
    exact hk
  exact ⟨Over.homMk (B.inclusion.preimage k)
    (by rw [← j.w, ← Category.assoc, hk₀, g.w]), Over.OverMorphism.ext hk₀⟩

/-! ### Chart ideal sheaves -/

/-- **The chart ideal sheaf of a sum is the product, on every scheme chart.** -/
theorem chartKer_sumClosedSubspaces_eq_mul (X : AlgebraicSpaces B S hS)
    (D₁ D₂ : ClosedSubspaces B S hS X.1) {U : BigFppfOver B S hS} (φ : yoneda.obj U ⟶ X.1) :
    chartKer B S hS X (sumClosedSubspaces B S hS X D₁ D₂) φ =
      chartKer B S hS X D₁ φ * chartKer B S hS X D₂ φ := by
  have hE := atlasHom_etale B S hS X
  have hSu := atlasHom_surjective B S hS X
  set h := hE.rep.snd φ
  set k := hE.rep.fst' φ
  have : Etale ((BigFppfOver.toScheme B S hS).map h) := hE.property_snd φ
  have : Surjective ((BigFppfOver.toScheme B S hS).map h) := hSu.property_snd φ
  have hw : yoneda.map k ≫ atlasHom B S hS X = yoneda.map h ≫ φ := by
    rw [hE.rep.map_fst' φ]; exact hE.rep.w φ
  refine Scheme.IdealSheafData.comap_injective_of_flat_of_surjective
    ((BigFppfOver.toScheme B S hS).map h) ?_
  have key : ∀ D : ClosedSubspaces B S hS X.1,
      (chartKer B S hS X D φ).comap ((BigFppfOver.toScheme B S hS).map h) =
        (chartKer B S hS X D (atlasHom B S hS X)).comap
          ((BigFppfOver.toScheme B S hS).map k) := fun D =>
    (comap_chartKer B S hS X D φ h _ rfl).trans
      (comap_chartKer B S hS X D (atlasHom B S hS X) k _ hw).symm
  rw [Stacks.IdealSheaf.comap_mul, key, key D₁, key D₂, chartKer_sumClosedSubspaces,
    Stacks.IdealSheaf.comap_mul]

/-- **A closed subspace is contained in another as soon as it is on one surjective étale
chart.** -/
theorem le_of_chartKer_le (X : AlgebraicSpaces B S hS) (Z W : ClosedSubspaces B S hS X.1)
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X.1}
    (hfS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hfE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (h : chartKer B S hS X W φ ≤ chartKer B S hS X Z φ) : Z.1 ≤ W.1 := by
  intro T x hx
  set U' : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk φ, hfE⟩
  set τ : yoneda.obj T.unop ⟶ X.1 := yonedaEquiv.symm x with hτ
  refine mem_obj_of_surjective_etale B S hS X.2.isSheaf W.1 W.2.1.isSheaf
    (hfE.rep.snd τ) (hfS.property_snd τ) (hfE.property_snd τ) _ ?_
  have hw : yoneda.map (hfE.rep.fst' τ) ≫ φ = yoneda.map (hfE.rep.snd τ) ≫ τ := by
    rw [hfE.rep.map_fst' τ]
    exact hfE.rep.w τ
  have hval : X.1.map (hfE.rep.snd τ).op x =
      U'.1.hom.app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) := by
    rw [show U'.1.hom = φ from rfl,
      ← yonedaEquiv_yoneda_map_comp B S hS φ (hfE.rep.fst' τ), hw,
      ← yonedaEquiv_naturality, hτ, Equiv.apply_symm_apply]
  have hZ : U'.1.hom.app (op (hfE.rep.pullback τ)) (hfE.rep.fst' τ) ∈
      Z.1.obj (op (hfE.rep.pullback τ)) := by
    rw [← hval]
    exact Z.1.map (hfE.rep.snd τ).op hx
  rw [hval]
  exact (mem_obj_iff_ker_le B S hS X W U' _).2
    (h.trans ((mem_obj_iff_ker_le B S hS X Z U' _).1 hZ))

/-! ### The sum `Z' + dE` and its scheme-theoretic image -/

section SecondCentre

variable {X X' : AlgebraicSpaces B S hS}

/-- **The closed subspace `Z' + d·E` of `X'`**, for `E = b⁻¹(Z)`: the sum of Stacks 083U of `Z'`
with `d` copies of the inverse image of `Z`. -/
abbrev exceptionalSum (b : X' ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (d : ℕ) : ClosedSubspaces B S hS X'.1 :=
  sumClosedSubspacesList X' (fun _ : Unit => preimageClosedSubspace b Z) Z'
    (List.replicate d ())

/-- **The scheme-theoretic image in `X` of `Z' + d·E`**, Stacks 082X applied to the composite
`Z' + d·E ⟶ X' ⟶ X`. -/
abbrev exceptionalSumImage (b : X' ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (d : ℕ) : ClosedSubspaces B S hS X.1 :=
  schemeTheoreticImage B S hS ((exceptionalSum b Z Z' d).1.ι ≫ b.hom) X.2

/-- **`Z' + d·E` lies in the inverse image of its scheme-theoretic image.** A morphism factors
through its scheme-theoretic image. -/
theorem exceptionalSum_le_preimage_exceptionalSumImage (b : X' ⟶ X)
    (Z : ClosedSubspaces B S hS X.1) (Z' : ClosedSubspaces B S hS X'.1) (d : ℕ) :
    (exceptionalSum b Z Z' d).1 ≤
      (preimageClosedSubspace b (exceptionalSumImage b Z Z' d)).1 := fun T x hx =>
  range_le_schemeTheoreticImageSubfunctor B S hS ((exceptionalSum b Z Z' d).1.ι ≫ b.hom) T
    ⟨⟨x, hx⟩, rfl⟩

/-- **The chart ideal sheaf of `Z' + d·E` is `𝓘_E^d · 𝓘_{Z'}`**, on every scheme chart. -/
theorem chartKer_exceptionalSum (b : X' ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) {U : BigFppfOver B S hS} (r : yoneda.obj U ⟶ X'.1) :
    ∀ d : ℕ, chartKer B S hS X' (exceptionalSum b Z Z' d) r =
      chartKer B S hS X' (preimageClosedSubspace b Z) r ^ d * chartKer B S hS X' Z' r
  | 0 => by rw [pow_zero, one_mul]; rfl
  | d + 1 => by
    show chartKer B S hS X' (sumClosedSubspaces B S hS X' (preimageClosedSubspace b Z)
      (exceptionalSum b Z Z' d)) r = _
    rw [chartKer_sumClosedSubspaces_eq_mul, chartKer_exceptionalSum b Z Z' r d, pow_succ',
      mul_assoc]

/-- **The chart ideal sheaf of an inverse image, on a chart lying over a chart.** -/
theorem chartKer_preimageClosedSubspace (b : X' ⟶ X) (T : ClosedSubspaces B S hS X.1)
    {V U' : BigFppfOver B S hS} (p : yoneda.obj V ⟶ X.1) (π : U' ⟶ V)
    (r : yoneda.obj U' ⟶ X'.1)
    (hrE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    (hw : yoneda.map π ≫ p = r ≫ b.hom) :
    chartKer B S hS X' (preimageClosedSubspace b T) r =
      (chartKer B S hS X T p).comap ((BigFppfOver.toScheme B S hS).map π) :=
  chartKer_preimage B S hS b T ⟨CostructuredArrow.mk r, hrE⟩ p π hw

/-- **The second centre on a chart, from its pullback identity.**

Let `b : X' ⟶ X` be a quasi-compact morphism of algebraic spaces, `Z ⊆ X` and `Z' ⊆ X'` closed
subspaces, and suppose given a cartesian square of presheaves
`U' ⟶ X'` over `p : V ⟶ X`, with `p` étale and the base change `r : U' ⟶ X'` surjective and
étale, `V` and `U'` schemes of the site and `π : U' ⟶ V` a morphism of the site.  If an ideal
sheaf `J` on `V` satisfies `π⁻¹J · 𝒪_{U'} = (π⁻¹𝓘_Z)^d · 𝓘_{Z'}` on `U'`, then

* `J` is contained in the chart ideal sheaf at `p` of the scheme-theoretic image `C` of
  `Z' + d·E ⟶ X`, and
* every closed subspace `T ⊆ X` whose chart ideal sheaf at `p` contains `J` has
  `b⁻¹(T) ⊆ Z' + d·E`.

The first clause is Stacks 089E (the scheme-theoretic image of the quasi-compact morphism
`Z' + d·E ⟶ X` commutes with the flat base change `p`) together with the minimality of the
scheme-theoretic image on `V`; the second is the one-chart criterion
`AlgebraicGeometry.Space.le_of_chartKer_le` at `r`. -/
theorem le_chartKer_exceptionalSumImage_and_of_comap_eq (b : X' ⟶ X)
    (hb : IsQuasiCompact B S hS b.hom) (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) {V U' : BigFppfOver B S hS} (p : yoneda.obj V ⟶ X.1)
    (hp : IsEtale B S hS p) (π : U' ⟶ V) (r : yoneda.obj U' ⟶ X'.1)
    (hrS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    (hrE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    (sq : IsPullback (yoneda.map π) r p b.hom) (d : ℕ)
    (J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (hJ : J.comap ((BigFppfOver.toScheme B S hS).map π) =
      (chartKer B S hS X Z p).comap ((BigFppfOver.toScheme B S hS).map π) ^ d *
        chartKer B S hS X' Z' r) :
    J ≤ chartKer B S hS X (exceptionalSumImage b Z Z' d) p ∧
      ∀ T : ClosedSubspaces B S hS X.1, J ≤ chartKer B S hS X T p →
        (preimageClosedSubspace b T).1 ≤ (exceptionalSum b Z Z' d).1 := by
  set D := exceptionalSum b Z Z' d with hD
  have hw : yoneda.map π ≫ p = r ≫ b.hom := sq.w
  -- the chart ideal sheaf of `D` at `r` is the inverse image of `J`
  have hDker : chartKer B S hS X' D r = J.comap ((BigFppfOver.toScheme B S hS).map π) := by
    rw [hD, chartKer_exceptionalSum,
      chartKer_preimageClosedSubspace b Z p π r hrE hw, hJ]
  refine ⟨?_, fun T hT => ?_⟩
  · -- a closed immersion of the site cutting out `J`
    obtain ⟨R, q, hq, hqK⟩ := exists_isClosedImmersion_ker_eq J
    have := hq
    -- the base change of `D` to `U'`, followed by `π`, factors through it
    set jD := D.2.2.rep.snd r
    have hjD : ((BigFppfOver.toScheme B S hS).map q).ker ≤
        ((BigFppfOver.toScheme B S hS).map (jD ≫ π)).ker := by
      rw [hqK, Functor.map_comp, ← Scheme.IdealSheafData.map_ker]
      refine (Scheme.IdealSheafData.map_gc _).le_iff_le.1 ?_
      exact (hDker.symm.trans (chartKer_eq B S hS X' D r)).le
    obtain ⟨l, hl⟩ := exists_comp_eq_of_ker_le_of_isClosedImmersion q (jD ≫ π) hjD
    -- the image morphism and its base change along `p`
    set g : D.1.toFunctor ⟶ X.1 := D.1.ι ≫ b.hom with hg
    have hgqc : IsQuasiCompact B S hS g :=
      isQuasiCompact_comp B S hS X'.2 X.2 D.1.ι b.hom
        (isQuasiCompact_of_isClosedImmersion' B S hS D.2.2) hb
    set s' : pullback g p ⟶ yoneda.obj U' :=
      sq.lift (pullback.snd g p) (pullback.fst g p ≫ D.1.ι)
        (by rw [Category.assoc, ← pullback.condition])
    have hs'r : s' ≫ r = pullback.fst g p ≫ D.1.ι := sq.lift_snd _ _ _
    have hs'π : s' ≫ yoneda.map π = pullback.snd g p := sq.lift_fst _ _ _
    set k : pullback g p ⟶ yoneda.obj (D.2.2.rep.pullback r) :=
      (D.2.2.rep.isPullback r).lift (pullback.fst g p) s' hs'r.symm
    have hk : k ≫ yoneda.map jD = s' := (D.2.2.rep.isPullback r).lift_snd _ _ _
    have hrange : Subfunctor.range (pullback.snd g p) ≤ Subfunctor.range (yoneda.map q) := by
      have hfac : pullback.snd g p = (k ≫ yoneda.map l) ≫ yoneda.map q := by
        rw [Category.assoc, ← yoneda.map_comp, hl, yoneda.map_comp, ← Category.assoc, hk, hs'π]
      rw [hfac]
      exact Subfunctor.range_comp_le _ _
    have himg : schemeTheoreticImageSubfunctor B S hS (pullback.snd g p) ≤
        Subfunctor.range (yoneda.map q) :=
      schemeTheoreticImageSubfunctor_le B S hS _
        (isClosedSubspace_range_yoneda_map B S hS q hq) hrange
    have hflat := schemeTheoreticImageSubfunctor_pullback_snd_of_isFlat_of_isQuasiCompact
      B S hS (ObjectProperty.homMk p : schemeSpace V ⟶ X)
      (ObjectProperty.homMk g : (⟨D.1.toFunctor, D.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (isFlat_of_isEtale B S hS hp) hgqc
    set C := exceptionalSumImage b Z Z' d with hC
    have hCr : Subfunctor.range (yoneda.map (C.2.2.rep.snd p)) =
        schemeTheoreticImageSubfunctor B S hS (pullback.snd g p) := by
      rw [range_yoneda_snd_eq_preimage B S hS p C.2.2.rep]
      exact hflat.symm
    rw [← hqK]
    exact ker_le_of_range_yoneda_map_le q (C.2.2.rep.snd p) (hCr.le.trans himg)
  · refine le_of_chartKer_le X' _ D hrS hrE ?_
    rw [hDker, chartKer_preimageClosedSubspace b T p π r hrE hw]
    exact Scheme.IdealSheafData.comap_mono _ hT

end SecondCentre

/-! ### The second centre of a blowup of a quasi-compact algebraic space -/

section Main

variable {X X' : AlgebraicSpaces B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **The second centre of a blowup of a quasi-compact algebraic space, on an affine chart.**

Let `X` be a quasi-compact algebraic space, `Z ⊆ X` a closed subspace of finite presentation,
`b : X' ⟶ X` the blowup of `X` in `Z` and `Z' ⊆ X'` a closed subspace of finite presentation.
There are a degree `d > 0`, a surjective étale chart `p : V ⟶ X` by an affine scheme of the site,
the cartesian square `U' = V ×_X X'` with its projections `π : U' ⟶ V` and `r : U' ⟶ X'` (a
morphism of the site and a surjective étale chart of `X'`), and a finite type ideal sheaf `J` on
`V` with `J ⊆ 𝓘_Z^d` and `π⁻¹J · 𝒪_{U'} = 𝓘_{Z' + dE}` on `U'`, such that, for `C` the
scheme-theoretic image of `Z' + dE ⟶ X`:

* `J ⊆ 𝓘_C` on `V`;
* every closed subspace `T ⊆ X` with `J ⊆ 𝓘_T` on `V` has `b⁻¹(T) ⊆ Z' + dE`;
* `b⁻¹(C) = Z' + dE`; and
* on the chart, `𝓘_{Z' + dE} = π⁻¹𝓘_C · 𝒪_{U'}`.

The chart is the affine étale atlas of the quasi-compact space `X`; over it `b` is the relative
`Proj` of the Rees algebra of `𝓘_Z|_V`, which is the scheme blowup (Stacks 085S and 085R,
`AlgebraicGeometry.Space.exists_iso_schemeSpace_reesProjChart_of_isEtale`); `d` and `J` are
those of the scheme-level second centre `Stacks.Blowup.exists_secondCentre` (Stacks 080B /
0803 at the Rees algebra), and the rest is
`AlgebraicGeometry.Space.le_chartKer_exceptionalSumImage_and_of_comap_eq`. -/
theorem exists_chart_secondCentre (hX : IsQuasiCompactSpace B S hS X.1)
    {Z : ClosedSubspaces B S hS X.1} (hZfp : IsFinitePresentation B S hS Z.1.ι)
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    {Z' : ClosedSubspaces B S hS X'.1} (hZ'fp : IsFinitePresentation B S hS Z'.1.ι) :
    ∃ (d : ℕ) (V U' : BigFppfOver B S hS) (p : yoneda.obj V ⟶ X.1) (π : U' ⟶ V)
      (r : yoneda.obj U' ⟶ X'.1) (J : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf r ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf r ∧
      IsPullback (yoneda.map π) r p b.hom ∧
      0 < d ∧ J.IsFiniteType ∧ J ≤ chartKer B S hS X Z p ^ d ∧
      J.comap ((BigFppfOver.toScheme B S hS).map π) =
        chartKer B S hS X' (exceptionalSum b Z Z' d) r ∧
      J ≤ chartKer B S hS X (exceptionalSumImage b Z Z' d) p ∧
      (∀ T : ClosedSubspaces B S hS X.1, J ≤ chartKer B S hS X T p →
        (preimageClosedSubspace b T).1 ≤ (exceptionalSum b Z Z' d).1) ∧
      preimageClosedSubspace b (exceptionalSumImage b Z Z' d) = exceptionalSum b Z Z' d ∧
      chartKer B S hS X' (exceptionalSum b Z Z' d) r =
        (chartKer B S hS X (exceptionalSumImage b Z Z' d) p).comap
          ((BigFppfOver.toScheme B S hS).map π) := by
  -- an affine surjective étale chart of `X`
  obtain ⟨V, a, haff, haS, haE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  have := haff
  have haEp := presheaf_etale_of_isEtale B S hS haE
  set aS : schemeSpace V ⟶ X := ObjectProperty.homMk a with haSdef
  set ZV := preimageClosedSubspace aS Z with hZV
  have hZVfp : IsFinitePresentation B S hS ZV.1.ι := isFinitePresentation_ι_preimage aS Z hZfp
  obtain ⟨hcU, hcR, hcRR⟩ :=
    contains_reesProj_of_isFinitePresentation ZV hZVfp (selfPresentation B S hS V)
  -- the base change of `b` to the chart is the relative `Proj` of the Rees algebra
  have sqF := AlgebraicSpaces.isPullback_fiberProduct B S hS aS b
  obtain ⟨e, he⟩ := exists_iso_schemeSpace_reesProjChart_of_isEtale hb V haE hcU hcR hcRR sqF
  set I₀ := reesChartIdeal (centreIdeal ZV) (isCartesianOnAffineCharts_centreIdeal ZV)
    (selfPresentation B S hS V) with hI₀
  set U' := reesProjChart (centreIdeal ZV) (isCartesianOnAffineCharts_centreIdeal ZV)
    (selfPresentation B S hS V) hcU
  set π : U' ⟶ V := reesProjChartHom (centreIdeal ZV) (isCartesianOnAffineCharts_centreIdeal ZV)
    (selfPresentation B S hS V) hcU with hπ
  have sqA : IsPullback (schemeSpaceMap π)
      (e.inv ≫ (ObjectProperty.homMk (pullback.snd aS.hom b.hom) :
        AlgebraicSpaces.fiberProduct B S hS aS b ⟶ X')) aS b :=
    IsPullback.of_iso sqF e (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]; exact he.symm)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
  set r : yoneda.obj U' ⟶ X'.1 :=
    (e.inv ≫ (ObjectProperty.homMk (pullback.snd aS.hom b.hom) :
      AlgebraicSpaces.fiberProduct B S hS aS b ⟶ X')).hom with hr
  have sqP : IsPullback (yoneda.map π) r a b.hom := AlgebraicSpaces.isPullback_hom B S hS sqA
  have hrS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqP haS
  have hrE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqP haEp
  -- the Rees chart ideal is the chart ideal sheaf of `Z`
  have hI : I₀ = chartKer B S hS X Z a := by
    rw [hI₀, ← ker_rep_snd_eq_reesChartIdeal B S hS (schemeSpace V) ZV
      (selfPresentation B S hS V)]
    show chartKer B S hS (schemeSpace V) (preimageClosedSubspace aS Z) (𝟙 _) = _
    rw [chartKer_preimageClosedSubspace aS Z a (𝟙 V) (𝟙 _) (selfPresentation B S hS V).etale
      (by rw [CategoryTheory.Functor.map_id, Category.id_comp]; exact (Category.id_comp _).symm),
      CategoryTheory.Functor.map_id, Scheme.IdealSheafData.comap_id]
  -- quasi-compactness of `b`
  have hbqc : IsQuasiCompact B S hS b.hom :=
    (isProper_of_isBlowupAlong_of_hasReesProjChartInSite B S hS Z b hZfp
      ⟨V, aS, haE, isSurjective_of_presheafSurjective B S hS a haS, hcU, hcR, hcRR⟩ hb).2.1.2
  -- the scheme-level second centre on the chart
  have hI₀ft : I₀.IsFiniteType := fg_ideal_reesChartIdeal_preimage B S hS Z hZfp V aS
  have hZ'ft : (chartKer B S hS X' Z' r).IsFiniteType :=
    (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
      (Z := ⟨Z'.1.toFunctor, Z'.2.1⟩) (X := X') (ObjectProperty.homMk Z'.1.ι) Z'.2.2
      hrE hrS).1 hZ'fp
  obtain ⟨d, J, hd, hJft, hJI, hJZ⟩ := Stacks.Blowup.exists_secondCentre_of_iso I₀ hI₀ft
    ((BigFppfOver.toScheme B S hS).map π) (Stacks.Blowup.reesSituationBlowUpIso I₀)
    ((Stacks.Blowup.reesSituationBlowUpIso_hom_blowUpToBase I₀).trans
      (toScheme_map_reesProjChartHom (centreIdeal ZV) (isCartesianOnAffineCharts_centreIdeal ZV)
        (selfPresentation B S hS V) hcU).symm)
    (chartKer B S hS X' Z' r) hZ'ft
  rw [hI] at hJI hJZ
  obtain ⟨h₁, h₂⟩ := le_chartKer_exceptionalSumImage_and_of_comap_eq b hbqc Z Z' a haE π r
    hrS hrE sqP d J hJZ
  have hpre : preimageClosedSubspace b (exceptionalSumImage b Z Z' d) =
      exceptionalSum b Z Z' d :=
    Subtype.ext (le_antisymm (h₂ _ h₁) (exceptionalSum_le_preimage_exceptionalSumImage b Z Z' d))
  refine ⟨d, V, U', a, π, r, J, haff, haS, haEp, hrS, hrE, sqP, hd, hJft, hJI, ?_, h₁, h₂, hpre,
    ?_⟩
  · rw [hJZ, chartKer_exceptionalSum, chartKer_preimageClosedSubspace b Z a π r hrE sqP.w]
  · rw [← chartKer_preimageClosedSubspace b _ a π r hrE sqP.w, hpre]

/-- **The second centre, as Stacks 0860 consumes it: `b⁻¹(C) = Z' + dE`.**  For `X`
quasi-compact, `Z ⊆ X` and `Z' ⊆ X'` of finite presentation and `b` the blowup of `X` in `Z`,
some degree `d > 0` has the inverse image along `b` of the scheme-theoretic image `C` of
`Z' + dE ⟶ X` equal to `Z' + dE`. -/
theorem exists_preimage_exceptionalSumImage_eq (hX : IsQuasiCompactSpace B S hS X.1)
    {Z : ClosedSubspaces B S hS X.1} (hZfp : IsFinitePresentation B S hS Z.1.ι)
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    {Z' : ClosedSubspaces B S hS X'.1} (hZ'fp : IsFinitePresentation B S hS Z'.1.ι) :
    ∃ d : ℕ, 0 < d ∧
      preimageClosedSubspace b (exceptionalSumImage b Z Z' d) = exceptionalSum b Z Z' d := by
  obtain ⟨d, -, -, -, -, -, -, -, -, -, -, -, -, hd, -, -, -, -, -, hpre, -⟩ :=
    exists_chart_secondCentre hX hZfp hb hZ'fp
  exact ⟨d, hd, hpre⟩

/-- **The second centre on a compact étale chart, in the shape the approximation step uses.**
There are a degree `d`, an étale chart `p : V ⟶ X` with `V` compact and a finite type ideal
sheaf `J₀` on `V` contained in the chart ideal sheaf of the scheme-theoretic image `C` of
`Z' + dE ⟶ X`, such that every closed subspace `T ⊆ X` whose chart ideal sheaf at `p` contains
`J₀` has `b⁻¹(T) ⊆ Z' + dE`. -/
theorem exists_chart_le_chartKer_exceptionalSumImage (hX : IsQuasiCompactSpace B S hS X.1)
    {Z : ClosedSubspaces B S hS X.1} (hZfp : IsFinitePresentation B S hS Z.1.ι)
    {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Z b)
    {Z' : ClosedSubspaces B S hS X'.1} (hZ'fp : IsFinitePresentation B S hS Z'.1.ι) :
    ∃ (d : ℕ) (V : BigFppfOver B S hS) (p : yoneda.obj V ⟶ X.1)
      (J₀ : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj V) ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      J₀.IsFiniteType ∧ J₀ ≤ chartKer B S hS X (exceptionalSumImage b Z Z' d) p ∧
      ∀ T : ClosedSubspaces B S hS X.1, J₀ ≤ chartKer B S hS X T p →
        (preimageClosedSubspace b T).1 ≤ (exceptionalSum b Z Z' d).1 := by
  obtain ⟨d, V, -, p, -, -, J, haff, -, hpE, -, -, -, -, hJft, -, -, h₁, h₂, -, -⟩ :=
    exists_chart_secondCentre hX hZfp hb hZ'fp
  have := haff
  exact ⟨d, V, p, J, inferInstance, hpE, hJft, h₁, h₂⟩

end Main

end AlgebraicGeometry.Space

end
