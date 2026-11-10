module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RepresentableEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.InverseImageStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.TwoIso
public import StacksFrontier.RingTheory.Henselian.EtaleLifting

/-!
# Lifting chart maps through the stalk of `g⁻¹h_V`: the henselian step of Stacks 04KL

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces, `f` a
morphism of algebraic spaces compatible with the charts of `g`, and `x̄` a geometric point of `X`.
For an étale morphism `c : V' ⟶ V₀` of affine étale charts of `Y` with a standard presentation
`Γ(V') = Γ(V₀)[x₁, …, xₙ]/(P₁, …, Pₙ)`, the comparison `g⁻¹h_V ⟶ chartFiber f V` at the stalk
at `x̄` is bijective *relative to `V₀`*: over a fixed element of the stalk of `g⁻¹h_{V₀}`, the
elements of the stalk of `g⁻¹h_{V'}` correspond bijectively to the germs of chart maps into
`V'`.  This is the step of the proof of Stacks 04KL (through Stacks 04I6) where the strict
henselianity of the stalks and the locality of `g♯` are used, through Stacks 04GX.

## Main results

* `AlgebraicGeometry.Space.stalk_chartFiberCoordinate_invRepComparison'`: the coordinates of the
  image of an element of the stalk of `g⁻¹h_V` are computed by `g♯`.
* `AlgebraicGeometry.Space.exists_stalk_lift'`: existence of the lift (relative surjectivity).
* `AlgebraicGeometry.Space.stalk_lift_unique'`: uniqueness of the lift (relative injectivity).

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] smallEtaleTopology_subcanonical

open Sheaf

set_option synthInstance.maxHeartbeats 400000 in
-- synthesizing `HasFiniteProducts` for sheaves on the small étale site exceeds the default
/-- Finite products of sheaves of sets on a small étale site, supplied directly: under Lean
v4.35.0 instance search for them times out in this file. -/
local instance (priority := high) hasFiniteProducts_sheaf_henselLift
    {Z : AlgebraicSpaces B S hS} :
    HasFiniteProducts (Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) :=
  inferInstance

/-- `F ↦ (g⁻¹F)_x̄` preserves finite products, supplied directly: under Lean v4.35.0 instance
search for it times out in this file. -/
local instance (priority := high) preservesFiniteProducts_invStalk_henselLift
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (x : GeometricPoint B S hS X.1) : PreservesFiniteProducts (invStalk g x) :=
  ⟨fun n => PreservesFiniteLimits.preservesFiniteLimits (Discrete (Fin n))⟩

section Germ

variable (x : GeometricPoint B S hS X.1)

/-- **The germ at `x̄` of a regular function on an étale chart `U` with a lift `ū` of `x̄`**, a
ring map `Γ(U, 𝒪_U) ⟶ 𝒪_{X,x̄}`. -/
def germRingHom (U : SmallEtale B S hS X.1) (ū : (sitePt x).fiber.obj U) :
    Γ(chartSch U, ⊤) →+* structureStalk x where
  toFun b := (sitePt x).toPresheafFiber U ū (ringSheaf (ringO X)).obj b
  map_one' := by
    have h := ringOneObj_naturality (ringO X) (Functor.whiskerLeft
      (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u))
      ((sitePt x).toPresheafFiberNatTrans U ū)) (P := sectionsFunctor _ (op U))
    exact (congrArg _ (sectionsFunctor_map_ringOneHom (ringO X) (op U) default).symm).trans h
  map_mul' a b := by
    have h := ringMulObj_naturality (ringO X) (Functor.whiskerLeft
      (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u))
      ((sitePt x).toPresheafFiberNatTrans U ū)) (P := sectionsFunctor _ (op U)) a b
    exact (congrArg _ (sectionsFunctor_map_ringMulHom (ringO X) (op U) a b).symm).trans h
  map_zero' := by
    have h := ringZeroObj_naturality (ringO X) (Functor.whiskerLeft
      (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u))
      ((sitePt x).toPresheafFiberNatTrans U ū)) (P := sectionsFunctor _ (op U))
    exact (congrArg _ (sectionsFunctor_map_ringZeroHom (ringO X) (op U) default).symm).trans h
  map_add' a b := by
    have h := ringAddObj_naturality (ringO X) (Functor.whiskerLeft
      (sheafToPresheaf (SmallEtale.topology B S hS X.1) (Type u))
      ((sitePt x).toPresheafFiberNatTrans U ū)) (P := sectionsFunctor _ (op U)) a b
    exact (congrArg _ (sectionsFunctor_map_ringAddHom (ringO X) (op U) a b).symm).trans h

/-- `germRingHom` is the germ of the section. -/
theorem germRingHom_apply (U : SmallEtale B S hS X.1) (ū : (sitePt x).fiber.obj U)
    (b : Γ(chartSch U, ⊤)) :
    germRingHom x U ū b = (sitePt x).toPresheafFiber U ū (ringSheaf (ringO X)).obj b :=
  rfl

end Germ

section Comparison

variable {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  {hover : IsChartOverBase g}
  {f : X ⟶ Y} (hf : OverBase.IsChartCompatible hover f) (x : GeometricPoint B S hS X.1)

/-- **The coordinates of the image of an element of the stalk of `g⁻¹h_V` are computed by
`g♯`.** For `σ` in the stalk of `g⁻¹h_V` and `b ∈ Γ(V, 𝒪_V)`, the germ of the pullback of `b`
along the chart map attached to `σ` is the image under `R ⟶ 𝒪_{X,x̄}` of `(g⁻¹b)(σ)`. -/
theorem stalk_chartFiberCoordinate_invRepComparison' (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V))
    (b : Γ(chartSch V, ⊤)) :
    (sitePt x).presheafFiber.map (chartFiberCoordinate B S hS f V b)
        ((sitePt x).presheafFiber.map (OverBase.invRepComparison hf V) σ) =
      invStalkRingHom g x (stalkCoordRingHom g x V σ b) := by
  have h1 := invRepComparison_comp_chartFiberCoordinate' hf V b
  have h2 := congrArg (fun m ↦ ((sitePt x).presheafFiber.map m :
    (sitePt x).presheafFiber.obj (invRep g V).obj → _) σ) h1
  simp only [Functor.map_comp] at h2
  refine h2.trans ?_
  change (sitePt x).sheafFiber.map (g.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm b) ≫ g.fSharpSet) σ = _
  rw [Functor.map_comp_apply]
  rfl

end Comparison

/-! ### The original forms, over a terminal base

The declarations of this section are the forms over a terminal base `S`, with
`hS₀ : IsTerminal S` as their hypothesis on the base. The primed declarations above are the same
constructions under `hover : AlgebraicGeometry.Space.IsChartOverBase g`, which
`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal` derives from `hS₀`. -/

section ComparisonBaseForm

variable {hS₀ : IsTerminal S}
  {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  {f : X ⟶ Y} (hf : IsChartCompatible hS₀ g f) (x : GeometricPoint B S hS X.1)

/-- **The coordinates of the image of an element of the stalk of `g⁻¹h_V` are computed by
`g♯`.** For `σ` in the stalk of `g⁻¹h_V` and `b ∈ Γ(V, 𝒪_V)`, the germ of the pullback of `b`
along the chart map attached to `σ` is the image under `R ⟶ 𝒪_{X,x̄}` of `(g⁻¹b)(σ)`. -/
theorem stalk_chartFiberCoordinate_invRepComparison (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (σ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V))
    (b : Γ(chartSch V, ⊤)) :
    (sitePt x).presheafFiber.map (chartFiberCoordinate B S hS f V b)
        ((sitePt x).presheafFiber.map (invRepComparison hf V) σ) =
      invStalkRingHom g x (stalkCoordRingHom g x V σ b) :=
  stalk_chartFiberCoordinate_invRepComparison' (hover := isChartOverBase_of_isTerminal hS₀ g) hf x
    V σ b

end ComparisonBaseForm

/-! ### Charts over an étale chart with a standard presentation -/

section Presentation

/-- Two morphisms of étale charts with the same underlying morphism of schemes are equal. -/
theorem smallEtale_hom_ext {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V : SmallEtale B S hS F}
    {a b : U ⟶ V}
    (h : (BigFppfOver.toScheme B S hS).map a.hom.left =
      (BigFppfOver.toScheme B S hS).map b.hom.left) :
    a = b :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    ((BigFppfOver.toScheme B S hS).map_injective h))

/-- The compatibility with the structure morphisms needed to build `chartHomOver`. -/
theorem chartHomOver_aux {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V' V₀ : SmallEtale B S hS F}
    (c : V' ⟶ V₀) (t : U ⟶ V₀) (v : chartSch U ⟶ chartSch V')
    (hv : v ≫ (BigFppfOver.toScheme B S hS).map c.hom.left =
      (BigFppfOver.toScheme B S hS).map t.hom.left) :
    v ≫ B.inclusion.map V'.obj.left.hom = B.inclusion.map U.obj.left.hom := by
  have h1 := congrArg B.inclusion.map (Over.w c.hom.left)
  have h2 := congrArg B.inclusion.map (Over.w t.hom.left)
  rw [Functor.map_comp] at h1 h2
  rw [← h1, ← Category.assoc]
  exact (congrArg (· ≫ B.inclusion.map V₀.obj.left.hom) hv).trans h2

/-- A morphism of schemes `U ⟶ V'` over a morphism of étale charts `c : V' ⟶ V₀`, lying over a
morphism of charts `t : U ⟶ V₀`, as a morphism of étale charts. -/
def chartHomOver {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U V' V₀ : SmallEtale B S hS F}
    (c : V' ⟶ V₀) (t : U ⟶ V₀) (v : chartSch U ⟶ chartSch V')
    (hv : v ≫ (BigFppfOver.toScheme B S hS).map c.hom.left =
      (BigFppfOver.toScheme B S hS).map t.hom.left) : U ⟶ V' :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (BigFppfOver.homOfCompEq B S hS v (chartHomOver_aux c t v hv)) (by
      have hc : BigFppfOver.homOfCompEq B S hS v (chartHomOver_aux c t v hv) ≫ c.hom.left =
          t.hom.left :=
        (BigFppfOver.toScheme B S hS).map_injective (by
          rwa [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq])
      change yoneda.map _ ≫ V'.obj.hom = U.obj.hom
      rw [← CostructuredArrow.w c.hom, ← Category.assoc, ← Functor.map_comp, hc]
      exact CostructuredArrow.w t.hom))

/-- The underlying morphism of schemes of `chartHomOver` is the given one. -/
@[simp]
theorem toScheme_map_chartHomOver {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V' V₀ : SmallEtale B S hS F} (c : V' ⟶ V₀) (t : U ⟶ V₀) (v : chartSch U ⟶ chartSch V')
    (hv : v ≫ (BigFppfOver.toScheme B S hS).map c.hom.left =
      (BigFppfOver.toScheme B S hS).map t.hom.left) :
    (BigFppfOver.toScheme B S hS).map (chartHomOver c t v hv).hom.left = v :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS v (chartHomOver_aux c t v hv)

/-- `chartHomOver` lies over the given chart map. -/
theorem chartHomOver_comp {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V' V₀ : SmallEtale B S hS F} (c : V' ⟶ V₀) (t : U ⟶ V₀) (v : chartSch U ⟶ chartSch V')
    (hv : v ≫ (BigFppfOver.toScheme B S hS).map c.hom.left =
      (BigFppfOver.toScheme B S hS).map t.hom.left) :
    chartHomOver c t v hv ≫ c = t :=
  smallEtale_hom_ext (by
    change (BigFppfOver.toScheme B S hS).map ((chartHomOver c t v hv).hom.left ≫ c.hom.left) = _
    rw [Functor.map_comp, toScheme_map_chartHomOver, hv])

variable {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
  (c : V' ⟶ V₀) {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(chartSch V₀, ⊤)}
  (pres : Stacks.EtaleCohomology.StandardPresentationOver (chartSch V')
    ((BigFppfOver.toScheme B S hS).map c.hom.left) P)

/-- The coordinate functions `x₁, …, xₙ` of the presentation, as regular functions on `V'`. -/
def presCoord (i : Fin n) : Γ(chartSch V', ⊤) :=
  pres.iso.inv.hom (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X i))

/-- The coordinate functions of the presentation are a solution of the system, over the
structure map `Γ(V₀) ⟶ Γ(V')`. -/
theorem isSolution_presCoord :
    MvPolynomial.IsSolution P ((BigFppfOver.toScheme B S hS).map c.hom.left).appTop.hom
      (presCoord c pres) := by
  let e := Stacks.EtaleCohomology.homOverEquivSolutions (chartSch V') (chartSch V')
    ((BigFppfOver.toScheme B S hS).map c.hom.left)
    ((BigFppfOver.toScheme B S hS).map c.hom.left) P pres
  have he : (e ⟨𝟙 _, Category.id_comp _⟩).1 = presCoord c pres := by
    funext i
    exact (Stacks.EtaleCohomology.homOverEquivSolutions_apply_coe _ _ _ _ P pres _ i).trans
      (by rw [Scheme.Hom.id_appTop, Category.comp_id]; rfl)
  exact he ▸ (e ⟨𝟙 _, Category.id_comp _⟩).2

/-- The coordinate of the solution attached to a morphism over `V₀` is the pullback of the
coordinate function. -/
theorem homOverEquivSolutions_coe_eq {U : Scheme.{u}} {pU : U ⟶ chartSch V₀}
    (w : {w : U ⟶ chartSch V' // w ≫ (BigFppfOver.toScheme B S hS).map c.hom.left = pU})
    (i : Fin n) :
    (Stacks.EtaleCohomology.homOverEquivSolutions U (chartSch V')
      ((BigFppfOver.toScheme B S hS).map c.hom.left) pU P pres w).1 i =
        w.1.appTop.hom (presCoord c pres i) :=
  Stacks.EtaleCohomology.homOverEquivSolutions_apply_coe _ _ _ _ P pres w i

/-- **Morphisms into `V'` over `V₀` are determined by the pullbacks of the coordinates.** -/
theorem eq_of_presCoord {U : Scheme.{u}} (w₁ w₂ : U ⟶ chartSch V')
    (h : w₁ ≫ (BigFppfOver.toScheme B S hS).map c.hom.left =
      w₂ ≫ (BigFppfOver.toScheme B S hS).map c.hom.left)
    (hc : ∀ i, w₁.appTop.hom (presCoord c pres i) = w₂.appTop.hom (presCoord c pres i)) :
    w₁ = w₂ := by
  let e := Stacks.EtaleCohomology.homOverEquivSolutions U (chartSch V')
    ((BigFppfOver.toScheme B S hS).map c.hom.left)
    (w₁ ≫ (BigFppfOver.toScheme B S hS).map c.hom.left) P pres
  exact congrArg Subtype.val (e.injective (a₁ := ⟨w₁, rfl⟩) (a₂ := ⟨w₂, h.symm⟩)
    (Subtype.ext (funext fun i ↦ by
      rw [homOverEquivSolutions_coe_eq, homOverEquivSolutions_coe_eq, hc i])))

/-- The sheaf `h_{V₀} × 𝒪_Yⁿ` on the small étale site of `Y`. -/
abbrev presSource : Sheaf (SmallEtale.topology B S hS Y.1) (Type u) :=
  (SmallEtale.topology B S hS Y.1).yoneda.obj V₀ ⨯ ∏ᶜ (fun _ : Fin n => ringSheaf (ringO Y))

/-- The sheaf `𝒪_Yⁿ` on the small étale site of `Y`. -/
abbrev presTarget : Sheaf (SmallEtale.topology B S hS Y.1) (Type u) :=
  ∏ᶜ (fun _ : Fin n => ringSheaf (ringO Y))

variable (P) in
/-- The map `h_{V₀} × 𝒪_Yⁿ ⟶ 𝒪_Yⁿ`, `(v, a) ↦ (Pⱼ(a))ⱼ` with the coefficients of `Pⱼ` pulled back
along `v`. -/
def presEval : presSource (V₀ := V₀) (n := n) ⟶ presTarget (Y := Y) (n := n) :=
  Pi.lift fun j => evalHom (ringO_mul_comm Y) (yonedaRingHom V₀) (P j)

/-- The zero map `h_{V₀} × 𝒪_Yⁿ ⟶ 𝒪_Yⁿ`. -/
def presZero : presSource (V₀ := V₀) (n := n) ⟶ presTarget (Y := Y) (n := n) :=
  Pi.lift fun _ => 0

/-- The map `h_{V'} ⟶ h_{V₀} × 𝒪_Yⁿ` given by `c` and the coordinate functions. -/
def presι : (SmallEtale.topology B S hS Y.1).yoneda.obj V' ⟶ presSource (V₀ := V₀) (n := n) :=
  prod.lift ((SmallEtale.topology B S hS Y.1).yoneda.map c)
    (Pi.lift fun i => secToHom V' (presCoord c pres i))

omit [IsAffine (chartSch V₀)] in
/-- Evaluating the sections of the coordinate-pullback ring map gives the pullback of regular
functions. -/
theorem sectionsEvalRingHom_comp_yonedaRingHom (U : SmallEtale B S hS Y.1)
    (v : (sectionsFunctor _ (op U)).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀)) :
    (sectionsEvalRingHom (op U) v).comp (yonedaRingHom V₀) =
      ((BigFppfOver.toScheme B S hS).map (show U ⟶ V₀ from v).hom.left).appTop.hom := by
  ext b
  exact sectionsFunctor_map_secToHom V₀ b U v

omit [IsAffine (chartSch V₀)] in
/-- On sections, the `j`-th component of `presEval` is the evaluation of `Pⱼ`. -/
theorem sectionsFunctor_map_presEval (U : SmallEtale B S hS Y.1)
    (z : (sectionsFunctor _ (op U)).obj (presSource (V₀ := V₀) (n := n))) (j : Fin n) :
    (sectionsFunctor _ (op U)).map (presEval P ≫ Pi.π _ j) z =
      MvPolynomial.eval (fun i => (show Γ(chartSch U, ⊤) from (sectionsFunctor _ (op U)).map
          (prod.snd ≫ Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i) z))
        (MvPolynomial.map ((BigFppfOver.toScheme B S hS).map
          (show U ⟶ V₀ from (sectionsFunctor _ (op U)).map prod.fst z).hom.left).appTop.hom
          (P j)) := by
  rw [presEval, Pi.lift_comp_π]
  refine (sectionsFunctor_map_evalHom (ringO_mul_comm Y) (yonedaRingHom V₀) (P j) (op U) z).trans
    ?_
  rw [sectionsEvalRingHom_comp_yonedaRingHom]
  rfl

omit [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] in
/-- On sections, the first component of `presι` is postcomposition with `c`. -/
theorem sectionsFunctor_map_presι_fst (U : SmallEtale B S hS Y.1)
    (s' : (sectionsFunctor _ (op U)).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V')) :
    (show U ⟶ V₀ from (sectionsFunctor _ (op U)).map prod.fst
      ((sectionsFunctor _ (op U)).map (presι c pres) s')) = (show U ⟶ V' from s') ≫ c := by
  change (sectionsFunctor _ (op U)).map (presι c pres ≫ prod.fst) s' = _
  rw [presι, prod.lift_fst]
  rfl

omit [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] in
/-- On sections, the coordinate components of `presι` are the pullbacks of the coordinate
functions. -/
theorem sectionsFunctor_map_presι_snd (U : SmallEtale B S hS Y.1)
    (s' : (sectionsFunctor _ (op U)).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'))
    (i : Fin n) :
    (show Γ(chartSch U, ⊤) from (sectionsFunctor _ (op U)).map
        (prod.snd ≫ Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i)
        ((sectionsFunctor _ (op U)).map (presι c pres) s')) =
      ((BigFppfOver.toScheme B S hS).map (show U ⟶ V' from s').hom.left).appTop.hom
        (presCoord c pres i) := by
  change (sectionsFunctor _ (op U)).map (presι c pres ≫ prod.snd ≫ Pi.π _ i) s' = _
  rw [presι, prod.lift_snd_assoc, Pi.lift_comp_π, sectionsFunctor_map_secToHom]
  rfl

/-- **`presι` equalizes the polynomial map and zero.** -/
theorem presι_comp_presEval :
    presι c pres ≫ presEval P = presι c pres ≫ presZero (V₀ := V₀) (n := n) := by
  refine hom_ext_sections fun U s' ↦ ?_
  obtain ⟨U⟩ := U
  refine Functor.piObjMk_ext fun j ↦ ?_
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, Category.assoc, Category.assoc,
    Functor.map_comp_apply, sectionsFunctor_map_presEval, presZero, Pi.lift_comp_π,
    Functor.map_comp_apply, sectionsFunctor_map_hom_ringZero]
  simp only [sectionsFunctor_map_presι_snd, sectionsFunctor_map_presι_fst]
  have hcomp : (BigFppfOver.toScheme B S hS).map ((show U ⟶ V' from s') ≫ c).hom.left =
      (BigFppfOver.toScheme B S hS).map (show U ⟶ V' from s').hom.left ≫
        (BigFppfOver.toScheme B S hS).map c.hom.left :=
    (BigFppfOver.toScheme B S hS).map_comp _ _
  rw [hcomp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  exact MvPolynomial.isSolution_comp (A' := Γ(chartSch U, ⊤)) _
    ((BigFppfOver.toScheme B S hS).map (show U ⟶ V' from s').hom.left).appTop.hom
    (isSolution_presCoord c pres) j

/-- **Sectionwise, `presι` is the equalizer of the polynomial map and zero**: by the equalizer
presentation of Stacks 04I6 step (2), a chart map `U ⟶ V'` over `V₀` is the same thing as a
solution over `Γ(U)` of the presented system. -/
theorem existsUnique_sectionsFunctor_presι (U : SmallEtale B S hS Y.1)
    (z : (sectionsFunctor _ (op U)).obj (presSource (V₀ := V₀) (n := n)))
    (hz : (sectionsFunctor _ (op U)).map (presEval P) z =
      (sectionsFunctor _ (op U)).map (presZero (V₀ := V₀) (n := n)) z) :
    ∃! s', (sectionsFunctor _ (op U)).map (presι c pres) s' = z := by
  let t : U ⟶ V₀ := (sectionsFunctor _ (op U)).map prod.fst z
  let b : Fin n → Γ(chartSch U, ⊤) := fun i ↦ (sectionsFunctor _ (op U)).map
    (prod.snd ≫ Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i) z
  have hsol : MvPolynomial.IsSolution P ((BigFppfOver.toScheme B S hS).map t.hom.left).appTop.hom
      b := by
    intro j
    have h := congrArg ((sectionsFunctor _ (op U)).map
      (Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) j)) hz
    rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply,
      sectionsFunctor_map_presEval, presZero, Pi.lift_comp_π, sectionsFunctor_map_hom_ringZero] at h
  let e := Stacks.EtaleCohomology.homOverEquivSolutions (chartSch U) (chartSch V')
    ((BigFppfOver.toScheme B S hS).map c.hom.left)
    ((BigFppfOver.toScheme B S hS).map t.hom.left) P pres
  let w := e.symm ⟨b, hsol⟩
  have hw : ∀ i, w.1.appTop.hom (presCoord c pres i) = b i := fun i ↦ by
    rw [← homOverEquivSolutions_coe_eq c pres w i]
    exact congrFun (congrArg Subtype.val (e.apply_symm_apply ⟨b, hsol⟩)) i
  have key : ∀ s' : U ⟶ V', (sectionsFunctor _ (op U)).map (presι c pres) s' = z ↔
      ((BigFppfOver.toScheme B S hS).map s'.hom.left = w.1) := by
    refine fun s' ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · refine eq_of_presCoord c pres _ _ ?_ fun i ↦ ?_
      · rw [← Functor.map_comp, w.2]
        congr 1
        have := sectionsFunctor_map_presι_fst c pres U s'
        rw [h] at this
        exact congrArg (fun q : U ⟶ V₀ ↦ q.hom.left) this.symm
      · rw [hw i, ← sectionsFunctor_map_presι_snd c pres U s', h]
    · refine Functor.prodObjMk_ext ?_ (Functor.piObjMk_ext fun i ↦ ?_)
      · refine (sectionsFunctor_map_presι_fst c pres U s').trans ?_
        exact smallEtale_hom_ext (((BigFppfOver.toScheme B S hS).map_comp s'.hom.left
          c.hom.left).trans (by rw [h, w.2]))
      · rw [← Functor.map_comp_apply]
        refine (sectionsFunctor_map_presι_snd c pres U s' i).trans ?_
        rw [h, hw i]
        change _ = ((sectionsFunctor _ (op U)).map prod.snd ≫
          (sectionsFunctor _ (op U)).map (Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i)) z
        rw [← Functor.map_comp]
  refine ⟨chartHomOver c t w.1 w.2, (key _).2 (toScheme_map_chartHomOver _ _ _ _), ?_⟩
  intro s' hs'
  exact smallEtale_hom_ext (((key s').1 hs').trans (toScheme_map_chartHomOver _ _ _ _).symm)

/-- **`h_{V'}` is the equalizer of the polynomial map and zero**, as sheaves on the small étale
site of `Y`: the equalizer presentation of Stacks 04I6 step (2), relative to `V₀`. -/
def presIsLimit : IsLimit (Fork.ofι (presι c pres) (presι_comp_presEval c pres)) := by
  refine isLimitOfReflects (sheafToPresheaf (SmallEtale.topology B S hS Y.1) (Type u))
    (evaluationJointlyReflectsLimits _ fun U ↦ ?_)
  refine (isLimitMapConeForkEquiv (sheafToPresheaf _ (Type u) ⋙ (evaluation _ (Type u)).obj U)
    (presι_comp_presEval c pres)).symm ?_
  exact Nonempty.some ((Types.type_equalizer_iff_unique _ _).2 fun y hy ↦
    existsUnique_sectionsFunctor_presι c pres U.unop y hy)

/-- **The equalizer property after a left exact functor.** For a functor `G` from sheaves on
`Y_étale` to sets preserving finite limits — in the application, the stalk at `x̄` of `g⁻¹` — an
element of `G(h_{V₀} × 𝒪_Yⁿ)` on which the polynomial map and zero agree comes from a unique
element of `G(h_{V'})`. -/
theorem existsUnique_map_presι (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u) ⥤ Type u)
    [PreservesFiniteLimits G] (z : G.obj (presSource (V₀ := V₀) (n := n)))
    (hz : G.map (presEval P) z = G.map (presZero (V₀ := V₀) (n := n)) z) :
    ∃! s', G.map (presι c pres) s' = z :=
  Types.unique_of_type_equalizer _ _ (isLimitForkMapOfIsLimit G _ (presIsLimit c pres)) z hz

end Presentation

/-! ### The germs of chart maps -/

section ChartGerms

variable (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- The germ at `x̄` of the pullback of a regular function `b` on `V` along a germ `t` of a chart
map into `V` over `f`. -/
abbrev chartStalkCoord {V : SmallEtale B S hS Y.1}
    (t : (sitePt x).presheafFiber.obj (chartFiber B S hS f V).toFunctor) (b : Γ(chartSch V, ⊤)) :
    structureStalk x :=
  (sitePt x).presheafFiber.map (chartFiberCoordinate B S hS f V b) t

/-- The germ of a pullback along the germ of a chart map is computed on a representative. -/
theorem chartCoord_toPresheafFiber {V : SmallEtale B S hS Y.1} (W : SmallEtale B S hS X.1)
    (w : (sitePt x).fiber.obj W) (tW : (chartFiber B S hS f V).toFunctor.obj (op W))
    (b : Γ(chartSch V, ⊤)) :
    chartStalkCoord f x ((sitePt x).toPresheafFiber W w (chartFiber B S hS f V).toFunctor tW) b =
      germRingHom x W w (((BigFppfOver.toScheme B S hS).map tW.val).appTop.hom b) := by
  change ((sitePt x).toPresheafFiber W w (chartFiber B S hS f V).toFunctor ≫
    (sitePt x).presheafFiber.map (chartFiberCoordinate B S hS f V b)) tW = _
  rw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  rfl

/-- **The germ of a chart map induces a ring map on regular functions.** -/
def chartCoordRingHom {V : SmallEtale B S hS Y.1}
    (t : (sitePt x).presheafFiber.obj (chartFiber B S hS f V).toFunctor) :
    Γ(chartSch V, ⊤) →+* structureStalk x :=
  let h := (sitePt x).toPresheafFiber_jointly_surjective (P := (chartFiber B S hS f V).toFunctor) t
  (germRingHom x h.choose h.choose_spec.choose).comp
    ((BigFppfOver.toScheme B S hS).map h.choose_spec.choose_spec.choose.val).appTop.hom

/-- `chartCoordRingHom` is `chartStalkCoord`. -/
theorem chartCoordRingHom_apply {V : SmallEtale B S hS Y.1}
    (t : (sitePt x).presheafFiber.obj (chartFiber B S hS f V).toFunctor) (b : Γ(chartSch V, ⊤)) :
    chartCoordRingHom f x t b = chartStalkCoord f x t b := by
  let h := (sitePt x).toPresheafFiber_jointly_surjective (P := (chartFiber B S hS f V).toFunctor) t
  conv_rhs => rw [← h.choose_spec.choose_spec.choose_spec]
  rw [chartCoord_toPresheafFiber]
  rfl

variable {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
  (c : V' ⟶ V₀) {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(chartSch V₀, ⊤)}
  (pres : Stacks.EtaleCohomology.StandardPresentationOver (chartSch V')
    ((BigFppfOver.toScheme B S hS).map c.hom.left) P)

/-- The map of presheaves `chartFiber f V' ⟶ chartFiber f V₀ × 𝒪_Xⁿ` recording the composite
with `c` and the pullbacks of the coordinate functions. -/
def presChartTheta : (chartFiber B S hS f V').toFunctor ⟶
    (chartFiber B S hS f V₀).toFunctor ⨯
      ∏ᶜ (fun _ : Fin n => (structureSetSheaf B S hS X).obj) :=
  prod.lift (chartFiberMap f c)
    (Pi.lift fun i => chartFiberCoordinate B S hS f V' (presCoord c pres i))

/-- `presChartTheta` is a monomorphism: chart maps into `V'` over `V₀` are determined by the
pullbacks of the coordinate functions. -/
instance mono_presChartTheta : Mono (presChartTheta f c pres) := by
  refine (NatTrans.mono_iff_mono_app _).2 fun U ↦ (mono_iff_injective _).2 fun d₁ d₂ h ↦ ?_
  let E := (evaluation (SmallEtale B S hS X.1)ᵒᵖ (Type u)).obj U
  have h₁ := congrArg (E.map prod.fst) (show E.map (presChartTheta f c pres) d₁ =
    E.map (presChartTheta f c pres) d₂ from h)
  rw [← types_comp_apply (E.map _), ← types_comp_apply (E.map _) (E.map prod.fst),
    ← Functor.map_comp, presChartTheta, prod.lift_fst] at h₁
  have h₂ : ∀ i, E.map (chartFiberCoordinate B S hS f V' (presCoord c pres i)) d₁ =
      E.map (chartFiberCoordinate B S hS f V' (presCoord c pres i)) d₂ := fun i ↦ by
    have := congrArg (E.map (prod.snd ≫ Pi.π _ i)) (show E.map (presChartTheta f c pres) d₁ =
      E.map (presChartTheta f c pres) d₂ from h)
    rwa [← types_comp_apply (E.map _), ← types_comp_apply (E.map _) (E.map (prod.snd ≫ _)),
      ← Functor.map_comp, presChartTheta, prod.lift_snd_assoc, Pi.lift_comp_π] at this
  apply Subtype.ext
  apply (BigFppfOver.toScheme B S hS).map_injective
  refine eq_of_presCoord c pres _ _ ?_ fun i ↦ h₂ i
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun q ↦ (BigFppfOver.toScheme B S hS).map (Subtype.val q)) h₁

end ChartGerms

/-! ### The henselian lifting at the stalk -/

section Lift

variable {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  {hover : IsChartOverBase g}
  {f : X ⟶ Y} (hf : OverBase.IsChartCompatible hover f) (x : GeometricPoint B S hS X.1)
  {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
  (c : V' ⟶ V₀) {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(chartSch V₀, ⊤)}
  (pres : Stacks.EtaleCohomology.StandardPresentationOver (chartSch V')
    ((BigFppfOver.toScheme B S hS).map c.hom.left) P)

omit [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] in
variable (g) in
/-- The coordinate ring map of an element of the stalk of `g⁻¹h_{V'}`, composed with
`Γ(V₀) ⟶ Γ(V')`, is the coordinate ring map of its image in the stalk of `g⁻¹h_{V₀}`. -/
theorem stalkCoordRingHom_map
    (σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'))
    (b : Γ(chartSch V₀, ⊤)) :
    stalkCoordRingHom g x V₀
        ((invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ') b =
      stalkCoordRingHom g x V' σ'
        (((BigFppfOver.toScheme B S hS).map c.hom.left).appTop.hom b) := by
  rw [stalkCoordRingHom_apply, stalkCoordRingHom_apply, ← Functor.map_comp_apply]
  congr 2

omit [IsAffine (chartSch V₀)] in
variable (g) in
/-- On the stalk, the polynomial map and zero agree exactly on the solutions. -/
theorem invStalk_map_presEval_eq_iff
    (z : (invStalk g x).obj (presSource (V₀ := V₀) (n := n))) :
    (invStalk g x).map (presEval P) z = (invStalk g x).map (presZero (V₀ := V₀) (n := n)) z ↔
      MvPolynomial.IsSolution P (stalkCoordRingHom g x V₀ ((invStalk g x).map prod.fst z))
        (fun i ↦ (invStalk g x).map (prod.snd ≫ Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i)
          z) := by
  have key : ∀ j, (invStalk g x).map (presEval P ≫ Pi.π _ j) z =
      MvPolynomial.eval (fun i ↦ (invStalk g x).map
          (prod.snd ≫ Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i) z)
        (MvPolynomial.map (stalkCoordRingHom g x V₀ ((invStalk g x).map prod.fst z)) (P j)) :=
    fun j ↦ by
      rw [presEval, Pi.lift_comp_π]
      exact map_evalHom (ringO_mul_comm Y) (yonedaRingHom V₀) (P j) (invStalk g x) z
  have key0 : ∀ j, (invStalk g x).map (presZero (V₀ := V₀) (n := n) ≫ Pi.π _ j) z = 0 :=
    fun j ↦ by
      rw [presZero, Pi.lift_comp_π]
      exact map_hom_ringZero (invStalk g x) z
  refine ⟨fun h j ↦ ?_, fun h ↦ Functor.piObjMk_ext fun j ↦ ?_⟩
  · have := congrArg ((invStalk g x).map (Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) j)) h
    rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply, key, key0] at this
  · rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, key, key0]
    exact h j

/-- An element of the stalk of `chartFiber f V'` is determined by its image in the stalk of
`chartFiber f V₀` and by the germs of the pullbacks of the coordinate functions. -/
theorem stalk_chartFiber_ext
    (t₁ t₂ : (sitePt x).presheafFiber.obj (chartFiber B S hS f V').toFunctor)
    (h₁ : (sitePt x).presheafFiber.map (chartFiberMap f c) t₁ =
      (sitePt x).presheafFiber.map (chartFiberMap f c) t₂)
    (h₂ : ∀ i, chartStalkCoord f x t₁ (presCoord c pres i) =
      chartStalkCoord f x t₂ (presCoord c pres i)) :
    t₁ = t₂ := by
  have hm : Mono ((sitePt x).presheafFiber.map (presChartTheta f c pres)) := inferInstance
  refine (mono_iff_injective _).1 hm ?_
  refine Functor.prodObjMk_ext ?_ (Functor.piObjMk_ext fun i ↦ ?_)
  · rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, presChartTheta, prod.lift_fst]
    exact h₁
  · have e : presChartTheta f c pres ≫ prod.snd ≫ Pi.π _ i =
        chartFiberCoordinate B S hS f V' (presCoord c pres i) := by
      rw [presChartTheta, prod.lift_snd_assoc, Pi.lift_comp_π]
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, e]
    exact h₂ i

omit [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] in
variable (g) in
/-- On the stalk, the first component of `presι` is the image along `c`. -/
theorem invStalk_map_presι_fst
    (σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V')) :
    (invStalk g x).map prod.fst ((invStalk g x).map (presι c pres) σ') =
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' := by
  rw [← Functor.map_comp_apply, presι, prod.lift_fst]

omit [IsAffine (chartSch V₀)] [IsAffine (chartSch V')] in
variable (g) in
/-- On the stalk, the coordinate components of `presι` are the coordinate ring maps. -/
theorem invStalk_map_presι_snd
    (σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V')) (i : Fin n) :
    (invStalk g x).map (prod.snd ≫ Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i)
        ((invStalk g x).map (presι c pres) σ') =
      stalkCoordRingHom g x V' σ' (presCoord c pres i) := by
  rw [← Functor.map_comp_apply, presι, prod.lift_snd_assoc, Pi.lift_comp_π]
  rfl

variable [StrictlyHenselianLocalRing (invStalkRing g x)]
  [StrictlyHenselianLocalRing (structureStalk x)]

include pres in
/-- **Relative surjectivity of the stalk comparison (Stacks 04KL, via 04I6 and 04GX).** Let
`σ₀` be an element of the stalk at `x̄` of `g⁻¹h_{V₀}` and `t'` a germ at `x̄` of a chart map into
`V'` over `f` whose composite with `c` is the image of `σ₀`.  Then `t'` is the image of an
element of the stalk of `g⁻¹h_{V'}` lying over `σ₀`. -/
theorem exists_stalk_lift' (hφ : IsLocalHom (invStalkRingHom g x))
    (hetale : ∀ ψ : Γ(chartSch V₀, ⊤) →+* invStalkRing g x,
      Algebra.Etale (invStalkRing g x) (MvPolynomial (Fin n) (invStalkRing g x) ⧸
        Ideal.span (Set.range fun j => MvPolynomial.map ψ (P j))))
    (σ₀ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))
    (t' : chartStalk f x V')
    (ht : chartStalkMap f x c t' =
      (sitePt x).presheafFiber.map (OverBase.invRepComparison hf V₀) σ₀) :
    ∃ σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' = σ₀ ∧
        (sitePt x).presheafFiber.map (OverBase.invRepComparison hf V') σ' = t' := by
  let ψ := stalkCoordRingHom g x V₀ σ₀
  let φ := invStalkRingHom g x
  let ρ := chartCoordRingHom f x t'
  have hρ : ρ.comp ((BigFppfOver.toScheme B S hS).map c.hom.left).appTop.hom = φ.comp ψ := by
    ext b
    rw [RingHom.comp_apply, chartCoordRingHom_apply, RingHom.comp_apply,
      ← stalk_chartFiberCoordinate_invRepComparison' hf x V₀ σ₀ b, ← ht]
    rw [← Functor.map_comp_apply]
    exact (congrArg (fun m ↦ ((sitePt x).presheafFiber.map m :
      (sitePt x).presheafFiber.obj (chartFiber B S hS f V').toFunctor → _) t')
      (chartFiberMap_comp_chartFiberCoordinate f c b)).symm
  have hsolX : MvPolynomial.IsSolution P (φ.comp ψ) (fun i ↦ ρ (presCoord c pres i)) :=
    hρ ▸ MvPolynomial.isSolution_comp _ ρ (isSolution_presCoord c pres)
  have := hetale ψ
  obtain ⟨r, hr, hry⟩ := (bijOn_solutions_of_etale φ hφ n
    (fun j => MvPolynomial.map ψ (P j))).2.2 (show ∀ i, _ from fun i ↦ by
      rw [MvPolynomial.map_map]
      exact hsolX i)
  let z : (invStalk g x).obj (presSource (V₀ := V₀) (n := n)) :=
    Functor.prodObjMk σ₀ (Functor.piObjMk r)
  have hzr : ∀ i, (invStalk g x).map (prod.snd ≫ Pi.π (fun _ : Fin n => ringSheaf (ringO Y)) i) z =
      r i := fun i ↦ by
    rw [Functor.map_comp_apply, Functor.map_snd_prodObjMk, Functor.map_piπ_piObjMk]
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
    change ((sitePt x).presheafFiber.map (OverBase.invRepComparison hf V') ≫
      (sitePt x).presheafFiber.map (chartFiberMap f c)) σ' =
      ((sitePt x).presheafFiber.map (g.toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom ≫
        (sitePt x).presheafFiber.map (OverBase.invRepComparison hf V₀)) σ'
    rw [← Functor.map_comp, ← Functor.map_comp, invRepComparison_naturality']
  · refine (stalk_chartFiberCoordinate_invRepComparison' hf x V' σ' _).trans ?_
    rw [← invStalk_map_presι_snd g x c pres, hσ', ← chartCoordRingHom_apply, hzr i]
    exact congrFun hry i

include pres in
/-- **Relative injectivity of the stalk comparison.** Two elements of the stalk of `g⁻¹h_{V'}`
lying over the same element of the stalk of `g⁻¹h_{V₀}` and with the same germ of chart map are
equal. -/
theorem stalk_lift_unique' (hφ : IsLocalHom (invStalkRingHom g x))
    (hetale : ∀ ψ : Γ(chartSch V₀, ⊤) →+* invStalkRing g x,
      Algebra.Etale (invStalkRing g x) (MvPolynomial (Fin n) (invStalkRing g x) ⧸
        Ideal.span (Set.range fun j => MvPolynomial.map ψ (P j))))
    (σ' σ'' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'))
    (h₀ : (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' =
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ'')
    (hc : (sitePt x).presheafFiber.map (OverBase.invRepComparison hf V') σ' =
      (sitePt x).presheafFiber.map (OverBase.invRepComparison hf V') σ'') : σ' = σ'' := by
  let σ₀ := (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ'
  let ψ := stalkCoordRingHom g x V₀ σ₀
  have := hetale ψ
  have hz : ∀ τ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
      (invStalk g x).map (presEval P) ((invStalk g x).map (presι c pres) τ) =
        (invStalk g x).map (presZero (V₀ := V₀) (n := n)) ((invStalk g x).map (presι c pres) τ) :=
    fun τ ↦ by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, presι_comp_presEval]
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
        rw [← stalk_chartFiberCoordinate_invRepComparison' hf,
          ← stalk_chartFiberCoordinate_invRepComparison' hf, hc])
  have hzz : (invStalk g x).map (presι c pres) σ'' = (invStalk g x).map (presι c pres) σ' := by
    refine Functor.prodObjMk_ext ?_ (Functor.piObjMk_ext fun i ↦ ?_)
    · rw [invStalk_map_presι_fst, invStalk_map_presι_fst, h₀]
    · rw [← Functor.map_comp_apply _ prod.snd, ← Functor.map_comp_apply _ prod.snd,
        invStalk_map_presι_snd, invStalk_map_presι_snd]
      exact (congrFun hr i).symm
  exact (existsUnique_map_presι c pres (invStalk g x) _ (hz σ')).unique rfl hzz

end Lift

/-! ### The original forms, over a terminal base

The declarations of this section are the forms over a terminal base `S`, with
`hS₀ : IsTerminal S` as their hypothesis on the base. The primed declarations above are the same
constructions under `hover : AlgebraicGeometry.Space.IsChartOverBase g`, which
`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal` derives from `hS₀`. -/

section LiftBaseForm

variable {hS₀ : IsTerminal S}
  {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  {f : X ⟶ Y} (hf : IsChartCompatible hS₀ g f) (x : GeometricPoint B S hS X.1)
  {V₀ V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V₀)] [IsAffine (chartSch V')]
  (c : V' ⟶ V₀) {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(chartSch V₀, ⊤)}
  (pres : Stacks.EtaleCohomology.StandardPresentationOver (chartSch V')
    ((BigFppfOver.toScheme B S hS).map c.hom.left) P)

variable [StrictlyHenselianLocalRing (invStalkRing g x)]
  [StrictlyHenselianLocalRing (structureStalk x)]

include pres in
/-- **Relative surjectivity of the stalk comparison (Stacks 04KL, via 04I6 and 04GX).** Let
`σ₀` be an element of the stalk at `x̄` of `g⁻¹h_{V₀}` and `t'` a germ at `x̄` of a chart map into
`V'` over `f` whose composite with `c` is the image of `σ₀`.  Then `t'` is the image of an
element of the stalk of `g⁻¹h_{V'}` lying over `σ₀`. -/
theorem exists_stalk_lift (hφ : IsLocalHom (invStalkRingHom g x))
    (hetale : ∀ ψ : Γ(chartSch V₀, ⊤) →+* invStalkRing g x,
      Algebra.Etale (invStalkRing g x) (MvPolynomial (Fin n) (invStalkRing g x) ⧸
        Ideal.span (Set.range fun j => MvPolynomial.map ψ (P j))))
    (σ₀ : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V₀))
    (t' : chartStalk f x V')
    (ht : chartStalkMap f x c t' = (sitePt x).presheafFiber.map (invRepComparison hf V₀) σ₀) :
    ∃ σ' : (invStalk g x).obj ((SmallEtale.topology B S hS Y.1).yoneda.obj V'),
      (invStalk g x).map ((SmallEtale.topology B S hS Y.1).yoneda.map c) σ' = σ₀ ∧
        (sitePt x).presheafFiber.map (invRepComparison hf V') σ' = t' :=
  exists_stalk_lift' (hover := isChartOverBase_of_isTerminal hS₀ g) hf x c pres hφ hetale σ₀ t' ht

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
    (hc : (sitePt x).presheafFiber.map (invRepComparison hf V') σ' =
      (sitePt x).presheafFiber.map (invRepComparison hf V') σ'') : σ' = σ'' :=
  stalk_lift_unique' (hover := isChartOverBase_of_isTerminal hS₀ g) hf x c pres hφ hetale σ' σ''
    h₀ hc

end LiftBaseForm

end AlgebraicGeometry.Space
