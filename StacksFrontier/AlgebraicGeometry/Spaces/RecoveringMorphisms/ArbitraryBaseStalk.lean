module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseTwoIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Bijectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.HenselLift

/-!
# The stalk comparison of Stacks 04KL over an arbitrary base scheme

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces over a base
scheme `S` whose chart morphisms are over `S` (`AlgebraicGeometry.Space.IsChartOverBase`),
`f : X ⟶ Y` a morphism compatible with the charts of `g`
(`AlgebraicGeometry.Space.OverBase.IsChartCompatible`) and `x̄` a geometric point of `X`. When
the stalks are strictly henselian and `g♯` is local, the comparison `g⁻¹h_V ⟶ chartFiber f V` has
the Hensel lifting property and its uniqueness on the stalks at `x̄` relative to an étale morphism
of affine charts with a standard presentation; from these, and the lifting of stalk elements to
affine opens, the comparison is bijective on stalks.

## Main results

* `AlgebraicGeometry.Space.OverBase.W_invRepComparison_of_bijective`: a comparison bijective on
  all geometric stalks is a local isomorphism.
* `AlgebraicGeometry.Space.OverBase.stalkComparison_surjective`,
  `AlgebraicGeometry.Space.OverBase.stalkComparison_injective`: bijectivity on stalks from the
  Hensel lifting property and its uniqueness.
* `AlgebraicGeometry.Space.OverBase.exists_stalk_lift`: existence of the Hensel lift.
* `AlgebraicGeometry.Space.OverBase.stalk_lift_unique`: uniqueness of the Hensel lift.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.OverBase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] smallEtaleTopology_subcanonical

open Sheaf

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for finite products of sheaves on the small étale site times out
/-- Finite products of sheaves of sets on a small étale site, supplied directly: under Lean
v4.35.0 instance search for them times out in this file. -/
local instance (priority := high) hasFiniteProducts_sheaf_arbitraryBaseStalk
    {Z : AlgebraicSpaces B S hS} :
    HasFiniteProducts (Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) :=
  inferInstance

/-- `F ↦ (g⁻¹F)_x̄` preserves finite products, supplied directly: under Lean v4.35.0 instance
search for it times out in this file. -/
local instance (priority := high) preservesFiniteProducts_invStalk_arbitraryBaseStalk
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (x : GeometricPoint B S hS X.1) : PreservesFiniteProducts (invStalk g x) :=
  ⟨fun n => PreservesFiniteLimits.preservesFiniteLimits (Discrete (Fin n))⟩

/-! ### The comparison on stalks -/

section Bijectivity

variable {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  (x : GeometricPoint B S hS X.1) {hb : IsChartOverBase g} {f : X ⟶ Y}
  (hfb : IsChartCompatible hb f)

/-- The comparison `g⁻¹h_V ⟶ chartFiber f V` on stalks at `x̄`. -/
abbrev stalkComparison (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V) → chartStalk f x V :=
  (sitePt x).presheafFiber.map (invRepComparison hfb V)

/-- The comparison on stalks is natural in the affine chart. -/
theorem stalkComparison_map {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V)
    (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V')) :
    stalkComparison x hfb V ((invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map j) σ) =
      chartStalkMap f x j (stalkComparison x hfb V' σ) := by
  change ((sitePt x).presheafFiber.map
      (g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map j)).hom ≫
    (sitePt x).presheafFiber.map (invRepComparison hfb V)) σ = _
  rw [← Functor.map_comp, invRepComparison_naturality, Functor.map_comp]
  rfl

/-- Functoriality of `g⁻¹h_•` on stalks, applied to an element of the stalk. -/
private theorem invStalk_map_yoneda_map_comp {V₁ V₂ V₃ : SmallEtale B S hS Y.1} (a : V₁ ⟶ V₂)
    (b : V₂ ⟶ V₃) (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₁)) :
    (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map (a ≫ b)) σ =
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map b)
        ((invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map a) σ) := by
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- A point of the open restriction of a chart maps into the open. -/
private theorem chartOpenRestrictionHom_base_mem (P : SmallEtale B S hS Y.1)
    (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).Opens)
    (w : (BigFppfOver.toScheme B S hS).obj (chartOpenRestriction B S hS Y.1 P O).1.left) :
    ((BigFppfOver.toScheme B S hS).map (chartOpenRestrictionHom B S hS Y.1 P O).hom.left).base w
      ∈ O := by
  have hι : (BigFppfOver.toScheme B S hS).map (chartOpenRestrictionHom B S hS Y.1 P O).hom.left =
      Scheme.Opens.ι O := chartOpenRestrictionHom_toScheme B S hS Y.1 P O
  rw [hι]
  exact Subtype.property _

/-- **Local bijectivity from bijectivity on stalks.** A comparison `g⁻¹h_V ⟶ chartFiber f V`
which is bijective on all geometric stalks is a local isomorphism. -/
theorem W_invRepComparison_of_bijective (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (h : ∀ x : GeometricPoint B S hS X.1, Function.Bijective (stalkComparison x hfb V)) :
    (SmallEtale.topology B S hS X.1).W (invRepComparison hfb V) := by
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
def RelSurjAt {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
    (c : V' ⟶ V₀) : Prop :=
  ∀ (σ₀ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))
    (t' : chartStalk f x V'), chartStalkMap f x c t' = stalkComparison x hfb V₀ σ₀ →
      ∃ σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' = σ₀ ∧
          stalkComparison x hfb V' σ' = t'

/-- The uniqueness of the Hensel lift along a morphism `c : V' ⟶ V₀` of affine charts. -/
def RelInjAt {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
    (c : V' ⟶ V₀) : Prop :=
  ∀ σ' σ'' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
    (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' =
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ'' →
      stalkComparison x hfb V' σ' = stalkComparison x hfb V' σ'' → σ' = σ''

/-- **Surjectivity of the comparison on stalks**, from the Hensel lifting property and the
existence of some element of the stalk of `g⁻¹h_{V₀}` for an affine chart `V₀`. -/
theorem stalkComparison_surjective (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (hRS : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelSurjAt x hfb c)
    (h₀ : ∃ (V₀ : SmallEtale B S hS Y.1) (_ : IsAffine (chartSch V₀)),
      Nonempty ((invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))) :
    Function.Surjective (stalkComparison x hfb V) := by
  intro t
  obtain ⟨V₀, _, ⟨σ₀⟩⟩ := h₀
  let P := SmallEtale.prodObj B S hS Y.1 V V₀
  obtain ⟨p, hp₁, hp₂⟩ := exists_chartStalk_prod f x V V₀ t (stalkComparison x hfb V₀ σ₀)
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
  rw [stalkComparison_map, hσW, chartStalkMap_comp, htW, hp₁]

/-- **Injectivity of the comparison on stalks**, from the Hensel lifting property, its
uniqueness, and the lifting of elements of the stalks of `g⁻¹h_P` to affine opens of `P`. -/
theorem stalkComparison_injective (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (hRS : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelSurjAt x hfb c)
    (hRI : ∀ {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
      (c : V' ⟶ V₀), RelInjAt x hfb c)
    (hT1 : ∀ (P : SmallEtale B S hS Y.1)
      (τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj P)),
      ∃ (O : ((BigFppfOver.toScheme B S hS).obj P.1.left).affineOpens)
        (τ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj
          (chartOpenRestriction B S hS Y.1 P O.1))),
        (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map
          (chartOpenRestrictionHom B S hS Y.1 P O.1)) τ' = τ) :
    Function.Injective (stalkComparison x hfb V) := by
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
      chartStalkMap f x q (chartStalkMap f x ι (stalkComparison x hfb W σ)) =
        stalkComparison x hfb V (Q.map (J.yoneda.map q) (Q.map (J.yoneda.map ι) σ)) := by
    intro W _ ι σ q
    rw [← chartStalkMap_comp, ← stalkComparison_map, invStalk_map_yoneda_map_comp]
  have hab : chartStalkMap f x ιa (stalkComparison x hfb Wa σa) =
      chartStalkMap f x ιb (stalkComparison x hfb Wb σb) := by
    refine chartStalk_prod_ext f x V V ?_ ?_
    · rw [hcomp, hcomp, hσa, hσb, hτ₁₁, hτ₂₁, h₁₂]
    · rw [hcomp, hcomp, hσa, hσb, hτ₁₂, hτ₂₂]
  obtain ⟨U, y, ca, cb, hca, hcb, hcab⟩ := exists_rep_of_chartStalkMap_eq f x ιa ιb _ _ hab
  let Oab := ((BigFppfOver.toScheme B S hS).map ιa.hom.left) ⁻¹ᵁ Ob.1
  have hrange : ∀ z, ((BigFppfOver.toScheme B S hS).map ca.1).base z ∈ Oab := by
    intro z
    change ((BigFppfOver.toScheme B S hS).map ca.1 ≫
      (BigFppfOver.toScheme B S hS).map ιa.hom.left).base z ∈ Ob.1
    rw [← Functor.map_comp, hcab, Functor.map_comp, Scheme.Hom.comp_apply]
    exact chartOpenRestrictionHom_base_mem P Ob.1 _
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
    exact e.2 (chartOpenRestrictionHom_base_mem Wa _ w)
  let kb : D ⟶ Wb := chartHomToOpen P Ob.1 (ιD ≫ ιa) hDrange
  have hkb : kb ≫ ιb = ιD ≫ ιa := chartHomToOpen_comp P Ob.1 (ιD ≫ ιa) hDrange
  let σa' := Q.map (J.yoneda.map kb) σD
  have hτ : Q.map (J.yoneda.map ιb) σa' = τ₁ := by
    rw [← invStalk_map_yoneda_map_comp, hkb, invStalk_map_yoneda_map_comp, hσD, hσa]
  have hc : stalkComparison x hfb Wb σa' = stalkComparison x hfb Wb σb := by
    apply chartStalkMap_injective f x ιb
    rwa [stalkComparison_map, ← chartStalkMap_comp, hkb, chartStalkMap_comp, hcD, htD]
  have hσ : σa' = σb := hRI (ιb ≫ p₂) σa' σb (by
    rw [invStalk_map_yoneda_map_comp, invStalk_map_yoneda_map_comp, hτ, hσb, hτ₁₂, hτ₂₂]) hc
  rw [← hτ₁₁, ← hτ₂₁, ← hτ, ← hσb, hσ]

end Bijectivity

/-! ### The coordinates of the stalk comparison -/

section Comparison

variable {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  {hb : IsChartOverBase g}
  {f : X ⟶ Y} (hfb : IsChartCompatible hb f) (x : GeometricPoint B S hS X.1)

/-- **The coordinates of the image of an element of the stalk of `g⁻¹h_V` are computed by
`g♯`.** For `σ` in the stalk of `g⁻¹h_V` and `b ∈ Γ(V, 𝒪_V)`, the germ of the pullback of `b`
along the chart map attached to `σ` is the image under `R ⟶ 𝒪_{X,x̄}` of `(g⁻¹b)(σ)`. -/
theorem stalk_chartFiberCoordinate_invRepComparison (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V))
    (b : Γ(chartSch V, ⊤)) :
    (sitePt x).presheafFiber.map (chartFiberCoordinate B S hS f V b)
        ((sitePt x).presheafFiber.map (invRepComparison hfb V) σ) =
      invStalkRingHom g x (stalkCoordRingHom g x V σ b) := by
  have h1 := invRepComparison_comp_chartFiberCoordinate hfb V b
  have h2 := congrArg (fun m ↦ ((sitePt x).presheafFiber.map m :
    (sitePt x).presheafFiber.obj (invRep g V).obj → _) σ) h1
  simp only [Functor.map_comp] at h2
  refine h2.trans ?_
  change (sitePt x).sheafFiber.map (g.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm b) ≫ g.fSharpSet) σ = _
  rw [Functor.map_comp, types_comp_apply]
  rfl

end Comparison

/-! ### The henselian lifting at the stalk -/

section Lift

variable {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  {hb : IsChartOverBase g}
  {f : X ⟶ Y} (hfb : IsChartCompatible hb f) (x : GeometricPoint B S hS X.1)
  {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
  (c : V' ⟶ V₀) {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(chartSch V₀, ⊤)}
  (pres : Stacks.EtaleCohomology.StandardPresentationOver (chartSch V')
    ((BigFppfOver.toScheme B S hS).map c.hom.left) P)

variable [StrictlyHenselianLocalRing (invStalkRing g x)]
  [StrictlyHenselianLocalRing (structureStalk x)]

include pres in
/-- **Relative surjectivity of the stalk comparison.** Let `σ₀` be an element of the stalk at `x̄`
of `g⁻¹h_{V₀}` and `t'` a germ at `x̄` of a chart map into `V'` over `f` whose composite with `c`
is the image of `σ₀`. Then `t'` is the image of an element of the stalk of `g⁻¹h_{V'}` lying over
`σ₀`. -/
theorem exists_stalk_lift (hφ : IsLocalHom (invStalkRingHom g x))
    (hetale : ∀ ψ : Γ(chartSch V₀, ⊤) →+* invStalkRing g x,
      Algebra.Etale (invStalkRing g x) (MvPolynomial (Fin n) (invStalkRing g x) ⧸
        Ideal.span (Set.range fun j => MvPolynomial.map ψ (P j))))
    (σ₀ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))
    (t' : chartStalk f x V')
    (ht : chartStalkMap f x c t' = (sitePt x).presheafFiber.map (invRepComparison hfb V₀) σ₀) :
    ∃ σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' = σ₀ ∧
        (sitePt x).presheafFiber.map (invRepComparison hfb V') σ' = t' := by
  let ψ := stalkCoordRingHom g x V₀ σ₀
  let φ := invStalkRingHom g x
  let ρ := chartCoordRingHom f x t'
  have hρ : ρ.comp ((BigFppfOver.toScheme B S hS).map c.hom.left).appTop.hom = φ.comp ψ := by
    ext b
    rw [RingHom.comp_apply, chartCoordRingHom_apply, RingHom.comp_apply,
      ← stalk_chartFiberCoordinate_invRepComparison hfb x V₀ σ₀ b, ← ht,
      ← types_comp_apply ((sitePt x).presheafFiber.map _), ← Functor.map_comp]
    exact (congrArg (fun m ↦ ((sitePt x).presheafFiber.map m :
      (sitePt x).presheafFiber.obj (chartFiber B S hS f V').toFunctor → _) t')
      (chartFiberMap_comp_chartFiberCoordinate f c b)).symm
  have hsolX : MvPolynomial.IsSolution P (φ.comp ψ) (fun i ↦ ρ (presCoord c pres i)) :=
    hρ ▸ MvPolynomial.isSolution_comp _ ρ (isSolution_presCoord c pres)
  have := hetale ψ
  obtain ⟨r, hr, hry⟩ := (bijOn_solutions_of_etale φ hφ n
    (fun j => MvPolynomial.map ψ (P j))).2.2 (show ∀ i, _ from fun i ↦ by
      rw [MvPolynomial.map_map]; exact hsolX i)
  let z : (invStalk g x).obj (presSource (V₀ := V₀) (n := n)) :=
    Functor.prodObjMk σ₀ (Functor.piObjMk r)
  have hzr : ∀ i, (invStalk g x).map
      (prod.snd ≫ Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i) z = r i := fun i ↦ by
    rw [Functor.map_comp, types_comp_apply, Functor.map_snd_prodObjMk, Functor.map_piπ_piObjMk]
  have hz : (invStalk g x).map (presEval P) z =
      (invStalk g x).map (presZero (V₀ := V₀) (n := n)) z := by
    refine (invStalk_map_presEval_eq_iff g x z).2 ?_
    have h1 : (invStalk g x).map prod.fst z = σ₀ := Functor.map_fst_prodObjMk _ _
    rwa [h1, funext hzr]
  obtain ⟨σ', hσ', -⟩ := existsUnique_map_presι c pres (invStalk g x) z hz
  have hσ₀ : (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' = σ₀ := by
    rw [← invStalk_map_presι_fst g x c pres, hσ']
    exact Functor.map_fst_prodObjMk _ _
  refine ⟨σ', hσ₀, stalk_chartFiber_ext x c pres _ _ ?_ fun i ↦ ?_⟩
  · change _ = chartStalkMap f x c t'
    rw [ht, ← hσ₀]
    change ((sitePt x).presheafFiber.map (invRepComparison hfb V') ≫
      (sitePt x).presheafFiber.map (chartFiberMap f c)) σ' =
      ((sitePt x).presheafFiber.map (g.toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom ≫
        (sitePt x).presheafFiber.map (invRepComparison hfb V₀)) σ'
    rw [← Functor.map_comp, ← Functor.map_comp, invRepComparison_naturality]
  · refine (stalk_chartFiberCoordinate_invRepComparison hfb x V' σ' _).trans ?_
    rw [← invStalk_map_presι_snd g x c pres, hσ', ← chartCoordRingHom_apply]
    rw [hzr]
    exact congrFun hry i

include pres in
/-- **Relative injectivity of the stalk comparison.** Two elements of the stalk of `g⁻¹h_{V'}`
lying over the same element of the stalk of `g⁻¹h_{V₀}` and with the same germ of chart map are
equal. -/
theorem stalk_lift_unique (hφ : IsLocalHom (invStalkRingHom g x))
    (hetale : ∀ ψ : Γ(chartSch V₀, ⊤) →+* invStalkRing g x,
      Algebra.Etale (invStalkRing g x) (MvPolynomial (Fin n) (invStalkRing g x) ⧸
        Ideal.span (Set.range fun j => MvPolynomial.map ψ (P j))))
    (σ' σ'' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'))
    (h₀ : (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' =
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ'')
    (hc : (sitePt x).presheafFiber.map (invRepComparison hfb V') σ' =
      (sitePt x).presheafFiber.map (invRepComparison hfb V') σ'') : σ' = σ'' := by
  let σ₀ := (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ'
  let ψ := stalkCoordRingHom g x V₀ σ₀
  have := hetale ψ
  have hz : ∀ τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
      (invStalk g x).map (presEval P) ((invStalk g x).map (presι c pres) τ) =
        (invStalk g x).map (presZero (V₀ := V₀) (n := n)) ((invStalk g x).map (presι c pres) τ) :=
    fun τ ↦ by
      rw [← types_comp_apply ((invStalk g x).map _), ← Functor.map_comp,
        ← types_comp_apply ((invStalk g x).map _) ((invStalk g x).map (presZero)),
        ← Functor.map_comp, presι_comp_presEval]
  have hsol : ∀ τ, (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) τ = σ₀ →
      MvPolynomial.IsSolution P ψ (fun i ↦ stalkCoordRingHom g x V' τ (presCoord c pres i)) :=
    fun τ hτ ↦ by
      have := (invStalk_map_presEval_eq_iff g x _).1 (hz τ)
      rw [invStalk_map_presι_fst, hτ] at this
      simpa only [invStalk_map_presι_snd] using this
  have hr : (fun i ↦ stalkCoordRingHom g x V' σ' (presCoord c pres i)) =
      (fun i ↦ stalkCoordRingHom g x V' σ'' (presCoord c pres i)) :=
    (bijOn_solutions_of_etale (invStalkRingHom g x) hφ n
      (fun j => MvPolynomial.map ψ (P j))).2.1 (hsol σ' rfl) (hsol σ'' h₀.symm) (funext fun i ↦ by
        change invStalkRingHom g x _ = invStalkRingHom g x _
        rw [← stalk_chartFiberCoordinate_invRepComparison hfb,
          ← stalk_chartFiberCoordinate_invRepComparison hfb, hc])
  have hzz : (invStalk g x).map (presι c pres) σ'' = (invStalk g x).map (presι c pres) σ' := by
    refine Functor.prodObjMk_ext ?_ (Functor.piObjMk_ext fun i ↦ ?_)
    · rw [invStalk_map_presι_fst, invStalk_map_presι_fst, h₀]
    · rw [← types_comp_apply ((invStalk g x).map _), ← Functor.map_comp,
        ← types_comp_apply ((invStalk g x).map _) ((invStalk g x).map (Pi.π _ i)),
        ← Functor.map_comp, invStalk_map_presι_snd, invStalk_map_presι_snd]
      exact (congrFun hr i).symm
  exact ((existsUnique_map_presι c pres (invStalk g x) _ (hz σ')).unique rfl hzz)

end Lift

end AlgebraicGeometry.Space.OverBase
