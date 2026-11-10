module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# Finite type on reductions for maps of affine charts

Let `S` be a scheme contained in a big fppf site `B`. This file proves the two inputs of the
comparison of condition (4) of **Stacks 0GC7** with conditions (1)–(3) that concern a single
map of charts.

* The affine computation of the proof of Stacks 0GC7: for a continuous homomorphism
  `g : A → R` of countably indexed weakly admissible topological rings over `S`, the map
  `Spf R ⟶ Spf A` is locally of finite type on reductions exactly when `g` has the property of
  **Stacks 0GC2**, that `A ⧸ 𝔞 → R ⧸ 𝔯` be of finite type. By **Stacks 0GB6** the reductions
  are the stages `Spec (A ⧸ 𝔞)` and `Spec (R ⧸ 𝔯)` at the ideals of topologically nilpotent
  elements, and the morphism of reductions is the spectrum of the induced ring map. Through
  **Stacks 0AIK** (a countably indexed affine formal algebraic space is a formal spectrum) and
  **Stacks 0AN0** (a map of formal spectra comes from a continuous homomorphism) this is the
  statement `AlgebraicGeometry.FormalSpace.ChartPropertyIsFiniteTypeOnReductions`.
* The passage of condition (4) to a representable étale square: if `f : X ⟶ Y` is a morphism
  of formal algebraic spaces which is locally of finite type on reductions, then so is the
  upper map `U ⟶ V` of any square whose vertical maps `U ⟶ X`, `V ⟶ Y` are representable
  étale. The morphisms of reductions `U_red ⟶ X_red` and `V_red ⟶ Y_red` are étale, so étale
  charts of `U_red` and `V_red` are étale charts of `X_red` and `Y_red`; this is the étale
  locality of Stacks 040Y in the direction (1) ⟹ (3) of Stacks 0ANL, read on reductions.

Together they give the implication (4) ⟹ (1) of Stacks 0GC7 for locally countably indexed
formal algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnReductions_formalSpectrumMap_iff`: the
  affine computation for a presented map of formal spectra.
* `AlgebraicGeometry.FormalSpace.chartPropertyIsFiniteTypeOnReductions`: the affine computation
  for countably indexed affine formal algebraic spaces.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnReductions.of_etaleSquare`: condition
  (4) passes to representable étale squares over a morphism of formal algebraic spaces.
* `FormalSpace.hasPropertyOnEveryAffineEtaleDiagram_of_isLocallyOfFiniteTypeOnReductions`: the
  implication (4) ⟹ (1) of Stacks 0GC7.

## References

* [Stacks Project, Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)
* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
* [Stacks Project, Tag 0GB6](https://stacks.math.columbia.edu/tag/0GB6)
* [Stacks Project, Tag 0GC2](https://stacks.math.columbia.edu/tag/0GC2)
* [Stacks Project, Tag 0GC7](https://stacks.math.columbia.edu/tag/0GC7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reductions and isomorphisms -/

/-- A reduction of `X` is a reduction of every sheaf isomorphic to `X`, along the composite of
its inclusion with the isomorphism. -/
theorem IsReduction.comp_iso {X X' Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (h : IsReduction B S hS X Xred i) (e : X ≅ X') :
    IsReduction B S hS X' Xred (i ≫ e.hom) := by
  have _ : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have : IsIso e.hom.hom :=
    Functor.map_isIso (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) e.hom
  exact isReduction_of_isRepresentableThickening B S hS (i ≫ e.hom) h.algebraic h.reduced
    (MorphismProperty.RespectsIso.postcomp _ e.hom.hom i.hom h.isRepresentableThickening)

/-- Being locally of finite type on reductions is unchanged by composing with isomorphisms on
either side: reductions of the source and the target of `t` are reductions of the source and
the target of `e.hom ≫ t ≫ e'.hom`, and the compatibility of a morphism between them with the
two maps is the same condition. -/
theorem IsLocallyOfFiniteTypeOnReductions.iso_comp_comp {U U' V V' : FppfSheaf B S hS}
    (e : U' ≅ U) (t : U ⟶ V) (e' : V ≅ V')
    (ht : IsLocallyOfFiniteTypeOnReductions B S hS t) :
    IsLocallyOfFiniteTypeOnReductions B S hS (e.hom ≫ t ≫ e'.hom) := by
  intro Ured Vred iU iV hU hV tred htred
  refine ht Ured Vred (iU ≫ e.hom) (iV ≫ e'.inv) (hU.comp_iso B S hS e)
    (hV.comp_iso B S hS e'.symm) tred ?_
  rw [← Category.assoc, htred]
  simp

/-! ### The morphism of reductions of a map of formal spectra -/

/-- The every-étale-chart condition is unchanged by composing with isomorphisms of presheaves
on both sides. -/
private theorem holdsOnEveryEtaleChartULift_comp_iso (P : MorphismProperty Scheme.{u})
    {F G K L : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ⟶ G) [IsIso e] (f : G ⟶ K)
    (e' : K ⟶ L) [IsIso e'] (hf : Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P f) :
    Space.HoldsOnEveryEtaleChartULift.{u + 1} B S hS P (e ≫ f ≫ e') :=
  Space.holdsOnEveryEtaleChartULift_precomp B S hS P e _
    (Space.holdsOnEveryEtaleChartULift_postcomp B S hS P e' _ hf)

/-- A morphism of the site whose underlying morphism of schemes is locally of finite type is
locally of finite type after sheafified Yoneda, and conversely: on the subcanonical big fppf
site the sheafified Yoneda image of an object is its universe-lifted Yoneda presheaf. -/
theorem isLocallyOfFiniteTypeULift_sheafifiedYoneda_map_iff {V U : BigFppfOver B S hS}
    (k : V ⟶ U) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k).hom ↔
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k) := by
  have hnat : ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map k).hom =
      (sheafifiedYonedaObjIso B S hS V).inv ≫ (uliftYoneda.{u + 1}).map k ≫
        (sheafifiedYonedaObjIso B S hS U).hom := by
    rw [sheafifiedYonedaObjIso_naturality, Iso.inv_hom_id_assoc]
    rfl
  rw [hnat]
  constructor
  · intro h
    refine prop_of_holdsOnEveryEtaleChartULift B S hS k ?_
    have h₁ := holdsOnEveryEtaleChartULift_comp_iso B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u}) (sheafifiedYonedaObjIso B S hS V).hom _
      (sheafifiedYonedaObjIso B S hS U).inv h
    rwa [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] at h₁
  · intro h
    exact holdsOnEveryEtaleChartULift_comp_iso B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u}) (sheafifiedYonedaObjIso B S hS V).inv _
      (sheafifiedYonedaObjIso B S hS U).hom
      (Space.isLocallyOfFiniteTypeULift_uliftYoneda_map B S hS k h)

variable {B S hS}
variable {A R : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [IsLinearTopology R R]

/-- **The affine computation of Stacks 0GC7.** Let `g : A → R` be a continuous homomorphism of
countably indexed weakly admissible topological rings over `S`. The map of formal spectra
`Spf R ⟶ Spf A` is locally of finite type on reductions exactly when `g` has the property of
**Stacks 0GC2**: the induced map `A ⧸ 𝔞 → R ⧸ 𝔯` of the quotients by the ideals of
topologically nilpotent elements is of finite type.

By **Stacks 0GB6** the stages `Spec (A ⧸ 𝔞)` and `Spec (R ⧸ 𝔯)` are reductions of `Spf A` and
`Spf R`, the morphism between them induced by `g` is the spectrum of `A ⧸ 𝔞 → R ⧸ 𝔯`, and any
other reductions and morphism between them are isomorphic to these. -/
theorem isLocallyOfFiniteTypeOnReductions_formalSpectrumMap_iff
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hcA : (nhds (0 : A)).IsCountablyGenerated)
    (hR : TopologicalRing.IsWeaklyAdmissible R) (hcR : (nhds (0 : R)).IsCountablyGenerated)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS R) (g : ContinuousHom D E) :
    IsLocallyOfFiniteTypeOnReductions B S hS (formalSpectrumMap hA g) ↔
      Rig.IsFiniteTypeOnReductions g.toRingHom g.continuous := by
  have hle : (TopologicalRing.nilIdx hA.1).1 ≤
      Ideal.comap g.toRingHom (TopologicalRing.nilIdx hR.1).1 :=
    TopologicalRing.topologicalNilradical_le_comap g.toRingHom g.continuous
  have hDred := isReduction_formalSpectrum hA D
    (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS D hA hcA)
  have hEred := isReduction_formalSpectrum hR E
    (QuotientSystem.hasLargeSite_of_isCountablyGenerated B S hS E hR hcR)
  have hspec := formalSpectrumMap_spec hA g _ _ hle
  have hk : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (g.stageMap _ _ hle))).hom ↔
      Rig.IsFiniteTypeOnReductions g.toRingHom g.continuous :=
    (isLocallyOfFiniteTypeULift_sheafifiedYoneda_map_iff B S hS _).trans
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff
        (P := @AlgebraicGeometry.LocallyOfFiniteType.{u})
        (φ := CommRingCat.ofHom (Ideal.quotientMap _ g.toRingHom hle)))
  refine ⟨fun h ↦ hk.mp (h _ _ _ _ hEred hDred _ hspec.symm),
    fun hg Ured Vred iU iV hU hV tred htred ↦ ?_⟩
  obtain ⟨σ, hσ, -⟩ := hU.universal _ hEred.algebraic hEred.reduced _
  obtain ⟨τ, hτ, -⟩ := hV.universal _ hDred.algebraic hDred.reduced _
  have : IsIso σ := IsReduction.isIso_of_comp_eq B S hS hEred hU hσ
  have : IsIso τ := IsReduction.isIso_of_comp_eq B S hS hDred hV hτ
  have hσinv : inv σ ≫ formalSpectrumInclusion E
      (OrderDual.toDual (TopologicalRing.nilIdx hR.1)) = iU :=
    (congrArg (fun m ↦ inv σ ≫ m) hσ.symm).trans (IsIso.inv_hom_id_assoc σ iU)
  obtain ⟨_, _, huniq⟩ := hV.universal Ured hU.algebraic hU.reduced
    (iU ≫ formalSpectrumMap hA g)
  have htred' : tred = inv σ ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      ((BigAffineFppf.inclusion B S hS).map (g.stageMap _ _ hle)) ≫ τ := by
    refine (huniq tred htred).trans (huniq _ ?_).symm
    change (inv σ ≫ _ ≫ τ) ≫ iV = iU ≫ formalSpectrumMap hA g
    exact ((Category.assoc _ _ _).trans (congrArg (fun x ↦ inv σ ≫ x)
      ((Category.assoc _ _ _).trans (congrArg (fun x ↦ _ ≫ x) hτ)))).trans
      ((congrArg (fun x ↦ inv σ ≫ x) hspec.symm).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun x ↦ x ≫ formalSpectrumMap hA g) hσinv)))
  rw [htred']
  exact holdsOnEveryEtaleChartULift_comp_iso B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) (inv σ).hom _ τ.hom (hk.mpr hg)

variable (B S hS)

/-- **The affine computation of Stacks 0GC7, on charts.** A map `t : U ⟶ V` of countably
indexed affine formal algebraic spaces over `S` is locally of finite type on reductions exactly
when the arrow of `WAdm^{count}` presenting it has the property of **Stacks 0GC2**, for every
presentation.

A countably indexed affine formal algebraic space is the formal spectrum of a countably indexed
weakly admissible topological ring (**Stacks 0AIK**), and a map of formal spectra comes from a
unique continuous homomorphism (**Stacks 0AN0**); this reduces both directions to
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnReductions_formalSpectrumMap_iff`. -/
theorem chartPropertyIsFiniteTypeOnReductions :
    ChartPropertyIsFiniteTypeOnReductions B S hS := by
  intro U V t _ _ hUc hVc
  constructor
  · intro ht A R _ _ _ _ _ _ _ _ hCA hCR hA D E eU eV g hg
    have hspf : IsLocallyOfFiniteTypeOnReductions B S hS (formalSpectrumMap hA g) := by
      simpa [hg] using IsLocallyOfFiniteTypeOnReductions.iso_comp_comp B S hS eU.symm t eV ht
    exact fun _ _ ↦ ⟨g.continuous, (isLocallyOfFiniteTypeOnReductions_formalSpectrumMap_iff hA
      hCA.2 hCR.1 hCR.2 D E g).mp hspf⟩
  · intro ht
    obtain ⟨R, _, _, _, _, E, hR, hcR, ⟨eU⟩⟩ :=
      exists_quotientSystem_of_isCountablyIndexed B S hS hUc
    obtain ⟨A, _, _, _, _, D, hA, hcA, ⟨eV⟩⟩ :=
      exists_quotientSystem_of_isCountablyIndexed B S hS hVc
    obtain ⟨g, hg, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hR
      (eU.inv ≫ t ≫ eV.hom)
    have htg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv := by
      rw [hg]
      simp
    obtain ⟨hgc, hgred⟩ := (TopologicalRing.finiteTypeOnReductionsProperty_iff g.toRingHom).mp
      (ht A R ⟨hA, hcA⟩ ⟨hR, hcR⟩ hA D E eU eV g htg)
    rw [htg]
    exact IsLocallyOfFiniteTypeOnReductions.iso_comp_comp B S hS eU _ eV.symm
      ((isLocallyOfFiniteTypeOnReductions_formalSpectrumMap_iff hA hcA hR hcR D E g).mpr hgred)

/-! ### Condition (4) on a representable étale square -/

/-- **Condition (4) of Stacks 0GC7 passes to representable étale squares.** Let `f : X ⟶ Y` be
a morphism of formal algebraic spaces over `S` which is locally of finite type on reductions,
and let `a : U ⟶ X`, `b : V ⟶ Y` be representable étale with `a ≫ f = t ≫ b`. Then `t` is
locally of finite type on reductions.

Reductions `X_red` and `Y_red` exist by **Stacks 0AIN**; given reductions of `U` and `V` and a
morphism `t_red` between them compatible with `t`, the universal property of the reductions
supplies `a_red : U_red ⟶ X_red`, `b_red : V_red ⟶ Y_red` and `f_red : X_red ⟶ Y_red` with
`t_red ≫ b_red = a_red ≫ f_red`. The morphisms `a_red` and `b_red` are étale, so étale charts
of `U_red` and `V_red` compose to étale charts of `X_red` and `Y_red`, over which `f_red` is
locally of finite type. This is the direction (1) ⟹ (3) of Stacks 0ANL, read on reductions, by
the étale locality of Stacks 040Y. -/
theorem IsLocallyOfFiniteTypeOnReductions.of_etaleSquare {X Y U V : FppfSheaf B S hS}
    (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hsq : a ≫ f = t ≫ b) (hf : IsLocallyOfFiniteTypeOnReductions B S hS f) :
    IsLocallyOfFiniteTypeOnReductions B S hS t := by
  intro Ured Vred iU iV hU hV tred htred
  obtain ⟨Xred, iX, hXr⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS X hX
  obtain ⟨Yred, iY, hYr⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS Y hY
  obtain ⟨fred, hfred, -⟩ := hYr.universal Xred hXr.algebraic hXr.reduced (iX ≫ f)
  obtain ⟨aR, haR, -⟩ := hXr.universal Ured hU.algebraic hU.reduced (iU ≫ a)
  obtain ⟨bR, hbR, -⟩ := hYr.universal Vred hV.algebraic hV.reduced (iV ≫ b)
  obtain ⟨_, _, huniq⟩ := hYr.universal Ured hU.algebraic hU.reduced (iU ≫ a ≫ f)
  have hcomm : tred ≫ bR = aR ≫ fred := by
    refine (huniq _ ?_).trans (huniq _ ?_).symm
    · change (tred ≫ bR) ≫ iY = iU ≫ a ≫ f
      rw [Category.assoc, hbR, reassoc_of% htred, hsq]
    · change (aR ≫ fred) ≫ iY = iU ≫ a ≫ f
      rw [Category.assoc, hfred, reassoc_of% haR]
  have haE := IsReduction.isEtaleULift_map B S hS hU hXr ha.1 ha.2 haR
  have hbE := IsReduction.isEtaleULift_map B S hS hV hYr hb.1 hb.2 hbR
  intro A B' α β h hα hβ hsqh
  refine hf Xred Yred iX iY hXr hYr fred hfred A B' (α ≫ aR.hom) (β ≫ bR.hom) h
    (haE A α hα) (hbE B' β hβ) ?_
  rw [← Category.assoc, hsqh, Category.assoc, Category.assoc]
  exact congrArg (fun m : Ured ⟶ Yred ↦ α ≫ m.hom) hcomm

/-- **Stacks 0GC7, condition (4) implies condition (1).** For a morphism `f : X ⟶ Y` of locally
countably indexed formal algebraic spaces over `S` which is locally of finite type on
reductions, every square with affine formal algebraic spaces `U`, `V` and representable étale
maps `U ⟶ X`, `V ⟶ Y` has upper map given by an arrow of `WAdm^{count}` with the property of
**Stacks 0GC2**.

The upper map is locally of finite type on reductions by
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnReductions.of_etaleSquare`, the affine
charts are countably indexed by the implication (2) ⟹ (1) of **Stacks 0AKX**, and the affine
computation `AlgebraicGeometry.FormalSpace.chartPropertyIsFiniteTypeOnReductions` applies. -/
theorem hasPropertyOnEveryAffineEtaleDiagram_of_isLocallyOfFiniteTypeOnReductions
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hf : IsLocallyOfFiniteTypeOnReductions B S hS f) :
    HasPropertyOnEveryAffineEtaleDiagram B S hS TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty f :=
  fun U V a b t hU hV ha hb hsq ↦
    (chartPropertyIsFiniteTypeOnReductions B S hS t hU hV
      (isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS X hX U a
        hU ha)
      (isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS Y hY V b
        hV hb)).1
      (IsLocallyOfFiniteTypeOnReductions.of_etaleSquare B S hS f a b t hX.1 hY.1 ha hb hsq hf)

end AlgebraicGeometry.FormalSpace

end
