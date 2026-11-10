module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartStalk

/-!
# The comparison `g⁻¹h_V ⟶ chartFiber f V` is bijective on stalks

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces and
`f : X ⟶ Y` a morphism compatible with the charts of `g`.  This file assembles, from the
Hensel lifting step at a geometric stalk, the bijectivity at every geometric point of the
comparison `g⁻¹h_V ⟶ chartFiber f V` for every affine étale chart `V` of `Y`, which is what makes
`(g, g♯)` 2-isomorphic to `(f_small, f♯)` in the proof of Stacks 04KL.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
  (x : GeometricPoint B S hS X.1)

attribute [local instance] smallEtaleTopology_subcanonical

/-- The two projections from the stalk of `g⁻¹h_{V ×_Y V'}` exhibit it as the product of the
stalks of `g⁻¹h_V` and `g⁻¹h_{V'}`. -/
noncomputable def invStalkProdIsLimit (V V' : SmallEtale B S hS Y.1) :
    IsLimit (BinaryFan.mk
      ((invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
        (SmallEtale.prodFst B S hS Y.1 V V')))
      ((invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
        (SmallEtale.prodSnd B S hS Y.1 V V')))) :=
  (isLimitMapConeBinaryFanEquiv ((SmallEtale.topology B S hS Y.1).yoneda ⋙ invStalk g x) _ _)
    (isLimitOfPreserves ((SmallEtale.topology B S hS Y.1).yoneda ⋙ invStalk g x)
      (SmallEtale.prodIsLimit B S hS Y.1 V V'))

/-- **Elements of the stalk of `g⁻¹h_{V ×_Y V'}`: existence of pairs.** -/
theorem exists_invStalk_prod (V V' : SmallEtale B S hS Y.1)
    (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V))
    (σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V')) :
    ∃ τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
        (SmallEtale.prodObj B S hS Y.1 V V')),
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (SmallEtale.prodFst B S hS Y.1 V V')) τ = σ ∧
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (SmallEtale.prodSnd B S hS Y.1 V V')) τ = σ' := by
  let h := invStalkProdIsLimit g x V V'
  let c : BinaryFan _ _ := BinaryFan.mk (P := PUnit.{u + 1}) (↾fun _ ↦ σ) (↾fun _ ↦ σ')
  refine ⟨h.lift c PUnit.unit, ?_, ?_⟩
  · exact congrArg (fun φ : (PUnit.{u + 1} : Type u) ⟶ _ ↦ φ PUnit.unit)
      (h.fac c ⟨WalkingPair.left⟩)
  · exact congrArg (fun φ : (PUnit.{u + 1} : Type u) ⟶ _ ↦ φ PUnit.unit)
      (h.fac c ⟨WalkingPair.right⟩)

/-- **Elements of the stalk of `g⁻¹h_{V ×_Y V'}`: uniqueness.** -/
theorem invStalk_prod_ext (V V' : SmallEtale B S hS Y.1)
    {τ τ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
        (SmallEtale.prodObj B S hS Y.1 V V'))}
    (h₁ : (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (SmallEtale.prodFst B S hS Y.1 V V')) τ =
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (SmallEtale.prodFst B S hS Y.1 V V')) τ')
    (h₂ : (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (SmallEtale.prodSnd B S hS Y.1 V V')) τ =
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (SmallEtale.prodSnd B S hS Y.1 V V')) τ') : τ = τ' := by
  have := BinaryFan.IsLimit.hom_ext (invStalkProdIsLimit g x V V')
    (f := (↾fun _ : PUnit.{u + 1} ↦ τ)) (g := ↾fun _ ↦ τ')
    (by ext; exact h₁) (by ext; exact h₂)
  exact congrArg (fun φ ↦ φ PUnit.unit) this

/-! ### Morphisms of charts -/

/-- `chartFiberMap f` sends a composite of morphisms of charts to the composite of the maps. -/
theorem chartFiberMap_comp (f : X ⟶ Y) {V V' V'' : SmallEtale B S hS Y.1} (j : V'' ⟶ V')
    (k : V' ⟶ V) : chartFiberMap f (j ≫ k) = chartFiberMap f j ≫ chartFiberMap f k := by
  ext U c
  exact Subtype.ext (Category.assoc _ _ _).symm

/-- The map of stalks `chartStalkMap f x` induced by a composite of morphisms of charts is the
composite of the induced maps. -/
theorem chartStalkMap_comp (f : X ⟶ Y) {V V' V'' : SmallEtale B S hS Y.1} (j : V'' ⟶ V')
    (k : V' ⟶ V) (t : chartStalk f x V'') :
    chartStalkMap f x (j ≫ k) t = chartStalkMap f x k (chartStalkMap f x j t) := by
  change (sitePt x).presheafFiber.map (chartFiberMap f (j ≫ k)) t = _
  rw [chartFiberMap_comp, Functor.map_comp]
  rfl

/-- A morphism of charts of `Y` whose underlying morphism of schemes has image in an open `O` of
the chart scheme of the target factors through the restriction of the target to `O`. -/
def chartHomToOpen (P : SmallEtale B S hS Y.1)
    (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).Opens) {D : SmallEtale B S hS Y.1}
    (k : D ⟶ P) (h : Set.range ((BigFppfOver.toScheme B S hS).map k.hom.left) ⊆ O) :
    D ⟶ chartOpenRestriction B S hS Y.1 P O :=
  ObjectProperty.homMk (CostructuredArrow.homMk (liftToOpenRestriction P O k.hom.left h) (by
    change yoneda.map (liftToOpenRestriction P O k.hom.left h) ≫
      (yoneda.map (chartOpenRestrictionHom B S hS Y.1 P O).hom.left ≫ P.1.hom) = D.1.hom
    rw [← Category.assoc, ← Functor.map_comp, liftToOpenRestriction_comp]
    exact CostructuredArrow.w k.hom))

/-- The factorisation `chartHomToOpen P O k h`, followed by the inclusion of the restriction of
`P` to `O`, is `k`. -/
@[simp]
theorem chartHomToOpen_comp (P : SmallEtale B S hS Y.1)
    (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).Opens) {D : SmallEtale B S hS Y.1}
    (k : D ⟶ P) (h : Set.range ((BigFppfOver.toScheme B S hS).map k.hom.left) ⊆ O) :
    chartHomToOpen P O k h ≫ chartOpenRestrictionHom B S hS Y.1 P O = k :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (liftToOpenRestriction_comp _ _ _ _))

/-- Points in the image of the inclusion of the restriction of `P` to `O` lie in `O`. -/
private theorem base_map_chartOpenRestrictionHom_mem (P : SmallEtale B S hS Y.1)
    (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).Opens)
    (w : chartSch (chartOpenRestriction B S hS Y.1 P O)) :
    ((BigFppfOver.toScheme B S hS).map (chartOpenRestrictionHom B S hS Y.1 P O).hom.left).base w
      ∈ O := by
  have hι : (BigFppfOver.toScheme B S hS).map (chartOpenRestrictionHom B S hS Y.1 P O).hom.left =
      Scheme.Opens.ι O := chartOpenRestrictionHom_toScheme B S hS Y.1 P O
  rw [hι]
  exact Subtype.property _

/-- The underlying morphism of schemes of a morphism of étale charts is étale. -/
instance etale_toScheme_map_chartHom {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V V' : SmallEtale B S hS F} (c : V' ⟶ V) :
    Etale ((BigFppfOver.toScheme B S hS).map c.hom.left) :=
  etale_of_etale_charts B S hS V'.obj.hom V.obj.hom V'.property V.property c.hom.left
    (CostructuredArrow.w c.hom)

/-! ### The comparison on stalks -/

variable {g} {hover : IsChartOverBase g} {f : X ⟶ Y} (hf : OverBase.IsChartCompatible hover f)

/-- The comparison `g⁻¹h_V ⟶ chartFiber f V` on stalks at `x̄`. -/
abbrev stalkComparison' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V) → chartStalk f x V :=
  (sitePt x).presheafFiber.map (OverBase.invRepComparison hf V)

/-- The comparison on stalks is natural in the affine chart. -/
theorem stalkComparison_map' {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V)
    (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V')) :
    stalkComparison' x hf V ((invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map j) σ) =
      chartStalkMap f x j (stalkComparison' x hf V' σ) := by
  change ((sitePt x).presheafFiber.map
      (g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map j)).hom ≫
    (sitePt x).presheafFiber.map (OverBase.invRepComparison hf V)) σ = _
  rw [← Functor.map_comp, invRepComparison_naturality', Functor.map_comp]
  rfl

/-- **Local bijectivity from bijectivity on stalks.** The geometric points form a conservative
family of points of the small étale site (Stacks 04K5), so a map of presheaves which is bijective
on all geometric stalks is a local isomorphism. -/
theorem W_invRepComparison_of_bijective' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (h : ∀ x : GeometricPoint B S hS X.1, Function.Bijective (stalkComparison' x hf V)) :
    (SmallEtale.topology B S hS X.1).W (OverBase.invRepComparison hf V) := by
  have : HasSheafify (SmallEtale.topology B S hS X.1) (Type u) :=
    SmallEtale.instHasSheafify B S hS X.1 (Type u)
  rw [(isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1 X.2).W_iff]
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hΦ
  exact (isIso_iff_bijective _).2 (h x)

/-! ### Surjectivity and injectivity on stalks -/

/-- The Hensel lifting property of the comparison along a morphism `c : V' ⟶ V₀` of affine charts:
a germ of a chart map into `V'` over the image of an element `σ₀` of the stalk of `g⁻¹h_{V₀}` comes
from an element of the stalk of `g⁻¹h_{V'}` over `σ₀`. -/
def RelSurjAt' {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
    (c : V' ⟶ V₀) : Prop :=
  ∀ (σ₀ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))
    (t' : chartStalk f x V'), chartStalkMap f x c t' = stalkComparison' x hf V₀ σ₀ →
      ∃ σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' = σ₀ ∧
          stalkComparison' x hf V' σ' = t'

/-- The uniqueness of the Hensel lift along a morphism `c : V' ⟶ V₀` of affine charts. -/
def RelInjAt' {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
    (c : V' ⟶ V₀) : Prop :=
  ∀ σ' σ'' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
    (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' =
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ'' →
      stalkComparison' x hf V' σ' = stalkComparison' x hf V' σ'' → σ' = σ''

/-- **Surjectivity of the comparison on stalks**, from the Hensel lifting property and the
existence of some element of the stalk of `g⁻¹h_{V₀}` for an affine chart `V₀`. -/
theorem stalkComparison_surjective' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (hRS : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelSurjAt' x hf c)
    (h₀ : ∃ (V₀ : SmallEtale B S hS Y.1) (_ : IsAffine (chartSch V₀)),
      Nonempty ((invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))) :
    Function.Surjective (stalkComparison' x hf V) := by
  intro t
  obtain ⟨V₀, _, ⟨σ₀⟩⟩ := h₀
  let P := SmallEtale.prodObj B S hS Y.1 V V₀
  obtain ⟨p, hp₁, hp₂⟩ := exists_chartStalk_prod f x V V₀ t (stalkComparison' x hf V₀ σ₀)
  obtain ⟨U, y, c, rfl⟩ := (sitePt x).toPresheafFiber_jointly_surjective
    (P := (chartFiber B S hS f P).toFunctor) p
  obtain ⟨O, tW, htW⟩ := exists_chartStalkMap_eq_of_cover f x P y c
    (fun O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens ↦ O.1)
    (fun z ↦ by rw [AlgebraicGeometry.iSup_affineOpens_eq_top]; trivial)
  let W := chartOpenRestriction B S hS Y.1 P O.1
  let ι : W ⟶ P := chartOpenRestrictionHom B S hS Y.1 P O.1
  have : IsAffine (chartSch W) := O.2
  obtain ⟨σW, hσW₀, hσW⟩ := hRS (ι ≫ SmallEtale.prodSnd B S hS Y.1 V V₀) σ₀ tW (by
    rw [chartStalkMap_comp, htW, hp₂])
  refine ⟨(invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
    (ι ≫ SmallEtale.prodFst B S hS Y.1 V V₀)) σW, ?_⟩
  rw [stalkComparison_map', hσW, chartStalkMap_comp, htW, hp₁]

/-- **Injectivity of the comparison on stalks**, from the Hensel lifting property, its
uniqueness, and the lifting of elements of the stalks of `g⁻¹h_P` to affine opens of `P`. -/
theorem stalkComparison_injective' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (hRS : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelSurjAt' x hf c)
    (hRI : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelInjAt' x hf c)
    (hT1 : ∀ (P : SmallEtale B S hS Y.1)
      (τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj P)),
      ∃ (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens)
        (τ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
          (chartOpenRestriction B S hS Y.1 P O.1))),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (chartOpenRestrictionHom B S hS Y.1 P O.1)) τ' = τ) :
    Function.Injective (stalkComparison' x hf V) := by
  intro σ₁ σ₂ h₁₂
  let J := SmallEtale.topology B S hS Y.1
  let Q := invStalk g x
  let P := SmallEtale.prodObj B S hS Y.1 V V
  let p₁ := SmallEtale.prodFst B S hS Y.1 V V
  let p₂ := SmallEtale.prodSnd B S hS Y.1 V V
  obtain ⟨τ₁, hτ₁₁, hτ₁₂⟩ := exists_invStalk_prod g x V V σ₁ σ₂
  obtain ⟨τ₂, hτ₂₁, hτ₂₂⟩ := exists_invStalk_prod g x V V σ₂ σ₂
  obtain ⟨Oa, σa, hσa⟩ := hT1 P τ₁
  obtain ⟨Ob, σb, hσb⟩ := hT1 P τ₂
  let Wa := chartOpenRestriction B S hS Y.1 P Oa.1
  let Wb := chartOpenRestriction B S hS Y.1 P Ob.1
  let ιa : Wa ⟶ P := chartOpenRestrictionHom B S hS Y.1 P Oa.1
  let ιb : Wb ⟶ P := chartOpenRestrictionHom B S hS Y.1 P Ob.1
  have : IsAffine (chartSch Wa) := Oa.2
  have : IsAffine (chartSch Wb) := Ob.2
  have hcomp : ∀ {W : SmallEtale B S hS Y.1} [IsAffine (chartSch W)] (ι : W ⟶ P)
      (σ : Q.obj (J.yoneda.obj W)) (q : P ⟶ V),
      chartStalkMap f x q (chartStalkMap f x ι (stalkComparison' x hf W σ)) =
        stalkComparison' x hf V (Q.map (J.yoneda.map q) (Q.map (J.yoneda.map ι) σ)) := by
    intro W _ ι σ q
    rw [← chartStalkMap_comp, ← stalkComparison_map', Functor.map_comp, Functor.map_comp]
    rfl
  have hab : chartStalkMap f x ιa (stalkComparison' x hf Wa σa) =
      chartStalkMap f x ιb (stalkComparison' x hf Wb σb) := by
    refine chartStalk_prod_ext f x V V ?_ ?_
    · rw [hcomp, hcomp, hσa, hσb, hτ₁₁, hτ₂₁, h₁₂]
    · rw [hcomp, hcomp, hσa, hσb, hτ₁₂, hτ₂₂]
  obtain ⟨U, y, ca, cb, hca, hcb, hcab⟩ := exists_rep_of_chartStalkMap_eq f x ιa ιb _ _ hab
  -- the representative of the germ into `Wa` lands in the preimage of `Ob`
  let Oab := ((BigFppfOver.toScheme B S hS).map ιa.hom.left) ⁻¹ᵁ Ob.1
  have hrange : ∀ z, ((BigFppfOver.toScheme B S hS).map ca.1).base z ∈ Oab := by
    intro z
    change ((BigFppfOver.toScheme B S hS).map ca.1 ≫
      (BigFppfOver.toScheme B S hS).map ιa.hom.left).base z ∈ Ob.1
    rw [← Functor.map_comp, hcab, Functor.map_comp, Scheme.Hom.comp_apply]
    exact base_map_chartOpenRestrictionHom_mem P Ob.1 _
  obtain ⟨e, tD, htD⟩ := exists_chartStalkMap_eq_of_cover f x Wa y ca
    (fun e : {e : Γ(chartSch Wa, ⊤) // (chartSch Wa).basicOpen e ≤ Oab} ↦
      (chartSch Wa).basicOpen e.1) (fun z ↦ by
        obtain ⟨e, he, hze⟩ := (isAffineOpen_top (chartSch Wa)).exists_basicOpen_le
          ⟨_, hrange z⟩ trivial
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨e, he⟩, hze⟩)
  let D := chartOpenRestriction B S hS Y.1 Wa ((chartSch Wa).basicOpen e.1)
  let ιD : D ⟶ Wa := chartOpenRestrictionHom B S hS Y.1 Wa ((chartSch Wa).basicOpen e.1)
  have : IsAffine (chartSch D) := (isAffineOpen_top (chartSch Wa)).basicOpen e.1
  rw [hca] at htD
  obtain ⟨σD, hσD, hcD⟩ := hRS ιD σa tD htD
  have hDrange : Set.range ((BigFppfOver.toScheme B S hS).map (ιD ≫ ιa).hom.left) ⊆ Ob.1 := by
    rintro _ ⟨w, rfl⟩
    change ((BigFppfOver.toScheme B S hS).map ιD.hom.left ≫
      (BigFppfOver.toScheme B S hS).map ιa.hom.left).base w ∈ Ob.1
    rw [Scheme.Hom.comp_apply]
    exact e.2 (base_map_chartOpenRestrictionHom_mem Wa _ w)
  let kb : D ⟶ Wb := chartHomToOpen P Ob.1 (ιD ≫ ιa) hDrange
  have hkb : kb ≫ ιb = ιD ≫ ιa := chartHomToOpen_comp P Ob.1 (ιD ≫ ιa) hDrange
  let σa' := Q.map (J.yoneda.map kb) σD
  have hτ : Q.map (J.yoneda.map ιb) σa' = τ₁ := by
    change (Q.map (J.yoneda.map kb) ≫ Q.map (J.yoneda.map ιb)) σD = τ₁
    rw [← Functor.map_comp, ← Functor.map_comp, hkb, Functor.map_comp, Functor.map_comp]
    change Q.map (J.yoneda.map ιa) (Q.map (J.yoneda.map ιD) σD) = τ₁
    rw [hσD, hσa]
  have hc : stalkComparison' x hf Wb σa' = stalkComparison' x hf Wb σb := by
    apply chartStalkMap_injective f x ιb
    rw [stalkComparison_map', ← chartStalkMap_comp, hkb, chartStalkMap_comp, hcD, htD]
    exact hab
  have hσ : σa' = σb := hRI (ιb ≫ p₂) σa' σb (by
    rw [Functor.map_comp, Functor.map_comp]
    change Q.map (J.yoneda.map p₂) (Q.map (J.yoneda.map ιb) σa') =
      Q.map (J.yoneda.map p₂) (Q.map (J.yoneda.map ιb) σb)
    rw [hτ, hσb, hτ₁₂, hτ₂₂]) hc
  rw [← hτ₁₁, ← hτ₂₁, ← hτ, ← hσb, hσ]

/-! ### The original forms, over a terminal base

The declarations of this section are the forms over a terminal base `S`, with
`hS₀ : IsTerminal S` as their hypothesis on the base. The primed declarations above are the same
constructions under `hover : AlgebraicGeometry.Space.IsChartOverBase g`, which
`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal` derives from `hS₀`. -/

section TopBaseForm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
  (x : GeometricPoint B S hS X.1)

attribute [local instance] smallEtaleTopology_subcanonical

variable {hS₀ : IsTerminal S} {g} {f : X ⟶ Y} (hf : IsChartCompatible hS₀ g f)

/-- The comparison `g⁻¹h_V ⟶ chartFiber f V` on stalks at `x̄`. -/
abbrev stalkComparison (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V) → chartStalk f x V :=
  (sitePt x).presheafFiber.map (invRepComparison hf V)

/-- The comparison on stalks is natural in the affine chart. -/
theorem stalkComparison_map {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V)
    (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V')) :
    stalkComparison x hf V ((invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map j) σ) =
      chartStalkMap f x j (stalkComparison x hf V' σ) :=
  stalkComparison_map' (hover := isChartOverBase_of_isTerminal hS₀ g) x hf j σ

/-- **Local bijectivity from bijectivity on stalks.** The geometric points form a conservative
family of points of the small étale site (Stacks 04K5), so a map of presheaves which is bijective
on all geometric stalks is a local isomorphism. -/
theorem W_invRepComparison_of_bijective (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (h : ∀ x : GeometricPoint B S hS X.1, Function.Bijective (stalkComparison x hf V)) :
    (SmallEtale.topology B S hS X.1).W (invRepComparison hf V) :=
  W_invRepComparison_of_bijective' (hover := isChartOverBase_of_isTerminal hS₀ g) hf V h

/-- The Hensel lifting property of the comparison along a morphism `c : V' ⟶ V₀` of affine charts:
a germ of a chart map into `V'` over the image of an element `σ₀` of the stalk of `g⁻¹h_{V₀}` comes
from an element of the stalk of `g⁻¹h_{V'}` over `σ₀`. -/
def RelSurjAt {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
    (c : V' ⟶ V₀) : Prop :=
  ∀ (σ₀ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))
    (t' : chartStalk f x V'), chartStalkMap f x c t' = stalkComparison x hf V₀ σ₀ →
      ∃ σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' = σ₀ ∧
          stalkComparison x hf V' σ' = t'

/-- The uniqueness of the Hensel lift along a morphism `c : V' ⟶ V₀` of affine charts. -/
def RelInjAt {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
    (c : V' ⟶ V₀) : Prop :=
  ∀ σ' σ'' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
    (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' =
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ'' →
      stalkComparison x hf V' σ' = stalkComparison x hf V' σ'' → σ' = σ''

/-- **Surjectivity of the comparison on stalks**, from the Hensel lifting property and the
existence of some element of the stalk of `g⁻¹h_{V₀}` for an affine chart `V₀`. -/
theorem stalkComparison_surjective (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (hRS : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelSurjAt x hf c)
    (h₀ : ∃ (V₀ : SmallEtale B S hS Y.1) (_ : IsAffine (chartSch V₀)),
      Nonempty ((invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))) :
    Function.Surjective (stalkComparison x hf V) :=
  stalkComparison_surjective' (hover := isChartOverBase_of_isTerminal hS₀ g) x hf V hRS h₀

/-- **Injectivity of the comparison on stalks**, from the Hensel lifting property, its
uniqueness, and the lifting of elements of the stalks of `g⁻¹h_P` to affine opens of `P`. -/
theorem stalkComparison_injective (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (hRS : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelSurjAt x hf c)
    (hRI : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelInjAt x hf c)
    (hT1 : ∀ (P : SmallEtale B S hS Y.1)
      (τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj P)),
      ∃ (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens)
        (τ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
          (chartOpenRestriction B S hS Y.1 P O.1))),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (chartOpenRestrictionHom B S hS Y.1 P O.1)) τ' = τ) :
    Function.Injective (stalkComparison x hf V) :=
  stalkComparison_injective' (hover := isChartOverBase_of_isTerminal hS₀ g) x hf V hRS hRI hT1

end TopBaseForm

end AlgebraicGeometry.Space
