module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldStalkChartRatio

/-!
# The ratio of the restricted generator to `s_ξ` is the pullback of the unit of the chart

Let `X` be a decent algebraic space, `Z ⊂ X` a prime divisor, `ℒ` an invertible `𝒪_X`-module
free on `e` over an étale chart `V`, `W' = V ×_X Z`, and let `Q` be an étale chart of
`Spec 𝒪_{U, u}` over the base change of `V`, over which the inverse image of `e` is `v · s_ξ`
for a regular function `v` on `Q`.  On `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q`, an étale chart of
`Spec κ(u)` over `W'`, the ratio `w` of the inverse image of `e|_Z` to the image of `s_ξ`
(`AlgebraicGeometry.Space.PrimeDivisor.genericFieldChartRatio`) is the pullback of `v` along
`P → Q` (`AlgebraicGeometry.Space.PrimeDivisor.genericFieldChartRatio_stalkBaseChange_eq`).

The two inverse images of `e` to `P`, through `Spec 𝒪_{U, u}` and through `Z`, agree under
`c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)`
(`Space.PrimeDivisor.modulePullbackChartValue_genericFieldPullbackIso_stalkBaseChange`), by the
comparison of two factorizations of a morphism on chart sections, and the image of `s_ξ` on `P` is
read through the same identification.

## Implementation notes

The kernel reduces `eqToHom h` by K-like reduction whenever it compares two terms containing it
which are not syntactically equal, and the two inverse images `(c ≫ j)^*ℒ` and `(ρ_Z ≫ ι)^*ℒ`
are not usefully definitionally equal.  The identification `c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)` therefore
enters only as a variable `I` with an equation `hI` identifying it with the composite
(`AlgebraicGeometry.Space.modulePullbackCompIso_trans_eqToIso_hom_apply_of_eq`), every
unfolding is done with `I` abstract, and chart diagrams are given by their components.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (V : SmallEtale B S hS X)
    (e : (W' : SmallEtale B S hS X) → (W' ⟶ V) → L.val.obj (op W'))
    (hcompat : ∀ (W₁ W₂ : SmallEtale B S hS X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))

/-- The restricted generator, read through the definition of `ℒ|_Z` along `Z.inclusionHom`. -/
theorem PrimeDivisor.baseChangeChartGenerator_eq_modulePullbackChartFMap_inclusionHom
    (W' : SmallEtale B S hS Z.subspace.toFunctor) (k : W' ⟶ Z.baseChangeChart B S hS hX V) :
    @Eq ((Z.restrictModule B S hS hX L).val.obj (op W'))
      (Z.baseChangeChartGenerator B S hS hX L V e W' k)
      ((modulePullbackChartFMap B S hS (Z.inclusionHom B S hS hX) L).app
        (Z.baseChangeChartGeneratorDiagram B S hS hX V k)
        (e V (𝟙 V))) := by
  unfold PrimeDivisor.baseChangeChartGenerator
  rfl

/-- The chart sections along the two spellings `Z.inclusionHom` and `Z.inclusion` of the
inclusion of a prime divisor agree. -/
theorem PrimeDivisor.modulePullbackChartFMap_inclusionHom_eq
    (d : ChartDiagram B S hS Z.subspace.toFunctor X (Z.inclusionHom B S hS hX).hom)
    (s : L.val.obj (op d.V)) :
    (modulePullbackChartFMap B S hS (Z.inclusionHom B S hS hX) L).app d s =
      (modulePullbackChartFMap B S hS (Z.inclusion B S hS hX) L).app d s :=
  congrArg (fun F ↦ ModuleFMap.app F d s)
    (rfl : modulePullbackChartFMap B S hS (Z.inclusionHom B S hS hX) L =
      modulePullbackChartFMap B S hS (Z.inclusion B S hS hX) L)

/-- **The restricted generator over `W' = V ×_X Z` itself**, at the chart diagram `(W', V)` given
by its components, along `Z.inclusion`. -/
theorem PrimeDivisor.baseChangeChartGenerator_id_eq_modulePullbackChartFMap
    (hb : (Z.baseChangeChart B S hS hX V).1.hom ≫ (Z.inclusion B S hS hX).hom =
      yoneda.map ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map
        (𝟙 (Z.baseChangeChart B S hS hX V)) ≫ (Z.baseChangeChartDiagram B S hS hX V).g) ≫
          V.1.hom) :
    Z.baseChangeChartGenerator B S hS hX L V e (Z.baseChangeChart B S hS hX V)
        (𝟙 (Z.baseChangeChart B S hS hX V)) =
      (modulePullbackChartFMap B S hS (Z.inclusion B S hS hX) L).app
        ⟨Z.baseChangeChart B S hS hX V, V,
          (SmallEtale.toOver B S hS Z.subspace.toFunctor).map (𝟙 (Z.baseChangeChart B S hS hX V)) ≫
            (Z.baseChangeChartDiagram B S hS hX V).g, hb⟩ (e V (𝟙 V)) := by
  have h3 : (modulePullbackChartFMap B S hS (Z.inclusion B S hS hX) L).app
      (Z.baseChangeChartGeneratorDiagram B S hS hX V (𝟙 (Z.baseChangeChart B S hS hX V)))
      (e V (𝟙 V)) =
      (modulePullbackChartFMap B S hS (Z.inclusion B S hS hX) L).app
        ⟨Z.baseChangeChart B S hS hX V, V,
          (SmallEtale.toOver B S hS Z.subspace.toFunctor).map (𝟙 (Z.baseChangeChart B S hS hX V)) ≫
            (Z.baseChangeChartDiagram B S hS hX V).g, hb⟩ (e V (𝟙 V)) := rfl
  exact ((Z.baseChangeChartGenerator_eq_modulePullbackChartFMap_inclusionHom B S hS hX L V e _
    (𝟙 (Z.baseChangeChart B S hS hX V))).trans
    (Z.modulePullbackChartFMap_inclusionHom_eq B S hS hX L _ _)).trans h3

/-- The value of a chart section at a chart diagram given by its components. -/
theorem modulePullbackChartValue_mk_eq {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (τ : (modulePullback B S hS f).obj M ⟶ N) {U : SmallEtale B S hS X.1}
    {V : SmallEtale B S hS Y.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom) (s : M.val.obj (op V)) :
    modulePullbackChartValue B S hS f M N τ ⟨U, V, a, ha⟩ s =
      (τ.val.app (op U)).hom ((modulePullbackChartFMap B S hS f M).app ⟨U, V, a, ha⟩ s) :=
  rfl

section General

variable {X' Y₁ Y₂ T : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_trans_eqToIso_hom_apply` for an isomorphism
`I` given together with an equation identifying it with the composite. -/
theorem modulePullbackCompIso_trans_eqToIso_hom_apply_of_eq
    (f₁ : X' ⟶ Y₁) (g₁ : Y₁ ⟶ T) (f₂ : X' ⟶ Y₂) (g₂ : Y₂ ⟶ T)
    (M : Modules.{u, u} B S hS T.1 T.2)
    (h : (modulePullback B S hS (f₂ ≫ g₂)).obj M = (modulePullback B S hS (f₁ ≫ g₁)).obj M)
    (I : (modulePullback B S hS f₂).obj ((modulePullback B S hS g₂).obj M) ≅
      (modulePullback B S hS f₁).obj ((modulePullback B S hS g₁).obj M))
    (hI : I = (modulePullbackCompIso B S hS f₂ g₂).app M ≪≫ eqToIso h ≪≫
        ((modulePullbackCompIso B S hS f₁ g₁).app M).symm)
    (hfg : f₂ ≫ g₂ = f₁ ≫ g₁)
    {U : SmallEtale B S hS X'.1} {V₁ : SmallEtale B S hS Y₁.1} {V₂ : SmallEtale B S hS Y₂.1}
    {W : SmallEtale B S hS T.1}
    (a₁ : (SmallEtale.toOver B S hS X'.1).obj U ⟶ (SmallEtale.toOver B S hS Y₁.1).obj V₁)
    (b₁ : (SmallEtale.toOver B S hS Y₁.1).obj V₁ ⟶ (SmallEtale.toOver B S hS T.1).obj W)
    (a₂ : (SmallEtale.toOver B S hS X'.1).obj U ⟶ (SmallEtale.toOver B S hS Y₂.1).obj V₂)
    (b₂ : (SmallEtale.toOver B S hS Y₂.1).obj V₂ ⟶ (SmallEtale.toOver B S hS T.1).obj W)
    (ha₁ : U.1.hom ≫ f₁.hom = yoneda.map a₁ ≫ V₁.1.hom)
    (hb₁ : V₁.1.hom ≫ g₁.hom = yoneda.map b₁ ≫ W.1.hom)
    (ha₂ : U.1.hom ≫ f₂.hom = yoneda.map a₂ ≫ V₂.1.hom)
    (hb₂ : V₂.1.hom ≫ g₂.hom = yoneda.map b₂ ≫ W.1.hom)
    (hab : a₂ ≫ b₂ = a₁ ≫ b₁) (s : M.val.obj (op W)) :
    modulePullbackChartValue B S hS f₂ ((modulePullback B S hS g₂).obj M)
        ((modulePullback B S hS f₁).obj ((modulePullback B S hS g₁).obj M)) I.hom
        ⟨U, V₂, a₂, ha₂⟩ ((modulePullbackChartFMap B S hS g₂ M).app ⟨V₂, W, b₂, hb₂⟩ s) =
      (modulePullbackChartFMap B S hS f₁ ((modulePullback B S hS g₁).obj M)).app
        ⟨U, V₁, a₁, ha₁⟩ ((modulePullbackChartFMap B S hS g₁ M).app ⟨V₁, W, b₁, hb₁⟩ s) := by
  refine (modulePullbackChartValue_mk_eq B S hS f₂ ((modulePullback B S hS g₂).obj M)
    ((modulePullback B S hS f₁).obj ((modulePullback B S hS g₁).obj M)) I.hom a₂ ha₂
    ((modulePullbackChartFMap B S hS g₂ M).app ⟨V₂, W, b₂, hb₂⟩ s)).trans ?_
  subst hI
  exact modulePullbackCompIso_trans_eqToIso_hom_apply B S hS f₁ g₁ f₂ g₂ M h hfg a₁ b₁ a₂ b₂
    ha₁ hb₁ ha₂ hb₂ hab s

end General

/-- `c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)` is the composite of the composition isomorphisms. -/
theorem PrimeDivisor.genericFieldPullbackIso_eq :
    Z.genericFieldPullbackIso B S hS hX hdec L =
      (modulePullbackCompIso B S hS (Z.genericFieldToStalk B S hS hX hdec)
        (Z.genericStalkMorphism B S hS hX hdec)).app L ≪≫
      eqToIso (by rw [Z.genericFieldMorphism_comp_inclusion B S hS hX hdec]) ≪≫
      ((modulePullbackCompIso B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.inclusion B S hS hX)).app L).symm :=
  rfl

variable (Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V)

/-- **The two inverse images of `e` to `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q`.**  Through
`Spec 𝒪_{U, u}` and through `Z`, under `c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)`, the inverse image of `e` to `P`
is the inverse image of the restricted generator `e|_Z` along `P → W'`. -/
theorem PrimeDivisor.modulePullbackChartValue_genericFieldPullbackIso_stalkBaseChange_aux
    (hQ : Q.1.hom ≫ (Z.genericStalkMorphism B S hS hX hdec).hom =
      yoneda.map ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) ≫ V.1.hom)
    (hb : (Z.baseChangeChart B S hS hX V).1.hom ≫ (Z.inclusion B S hS hX).hom =
      yoneda.map ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map
        (𝟙 (Z.baseChangeChart B S hS hX V)) ≫ (Z.baseChangeChartDiagram B S hS hX V).g) ≫
          V.1.hom)
    (hc : (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).1.hom ≫
        (Z.genericFieldToStalk B S hS hX hdec).hom =
      yoneda.map ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom) ≫
        Q.1.hom) :
    modulePullbackChartValue B S hS (Z.genericFieldToStalk B S hS hX hdec)
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
        ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
          (Z.restrictModule B S hS hX L))
        (Z.genericFieldPullbackIso B S hS hX hdec L).hom
        ⟨Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q, Q,
          (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom, hc⟩
        ((modulePullbackChartFMap B S hS (Z.genericStalkMorphism B S hS hX hdec) L).app
          ⟨Q, V, (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
            (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g, hQ⟩ (e V (𝟙 V))) =
      (modulePullbackChartFMap B S hS (Z.genericFieldMorphism B S hS hX hdec)
          ((modulePullback B S hS (Z.inclusion B S hS hX)).obj L)).app
        ⟨Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q, Z.baseChangeChart B S hS hX V,
          Z.genericFieldStalkBaseChangeToChart B S hS hX hdec V Q ι,
          Z.genericFieldStalkBaseChangeToChart_comm B S hS hX hdec V Q ι⟩
        ((modulePullbackChartFMap B S hS (Z.inclusion B S hS hX) L).app
          ⟨Z.baseChangeChart B S hS hX V, V,
            (SmallEtale.toOver B S hS Z.subspace.toFunctor).map
              (𝟙 (Z.baseChangeChart B S hS hX V)) ≫
              (Z.baseChangeChartDiagram B S hS hX V).g, hb⟩ (e V (𝟙 V))) := by
  have hab : (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom ≫
      (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g =
      Z.genericFieldStalkBaseChangeToChart B S hS hX hdec V Q ι ≫
        (SmallEtale.toOver B S hS Z.subspace.toFunctor).map (𝟙 (Z.baseChangeChart B S hS hX V)) ≫
          (Z.baseChangeChartDiagram B S hS hX V).g := by
    refine (Z.genericFieldStalkBaseChangeToChart_comp_g B S hS hX hdec V Q ι).symm.trans ?_
    refine congrArg (Z.genericFieldStalkBaseChangeToChart B S hS hX hdec V Q ι ≫ ·) ?_
    exact ((congrArg (· ≫ (Z.baseChangeChartDiagram B S hS hX V).g)
      (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)).symm
  exact (modulePullbackCompIso_trans_eqToIso_hom_apply_of_eq B S hS
    (U := Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)
    (V₁ := Z.baseChangeChart B S hS hX V) (V₂ := Q) (W := V)
    (Z.genericFieldMorphism B S hS hX hdec) (Z.inclusion B S hS hX)
    (Z.genericFieldToStalk B S hS hX hdec) (Z.genericStalkMorphism B S hS hX hdec) L _
    (Z.genericFieldPullbackIso B S hS hX hdec L) (Z.genericFieldPullbackIso_eq B S hS hX hdec L)
    (Z.genericFieldMorphism_comp_inclusion B S hS hX hdec).symm
    (Z.genericFieldStalkBaseChangeToChart B S hS hX hdec V Q ι)
    ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map (𝟙 (Z.baseChangeChart B S hS hX V)) ≫
      (Z.baseChangeChartDiagram B S hS hX V).g)
    ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom)
    ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g)
    (Z.genericFieldStalkBaseChangeToChart_comm B S hS hX hdec V Q ι) hb
    hc hQ hab
    (e V (𝟙 V)))

/-- **The two inverse images of `e` to `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q`.**  Through
`Spec 𝒪_{U, u}` and through `Z`, under `c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)`, the inverse image of `e` to `P`
is the inverse image of the restricted generator `e|_Z` along `P → W'`. -/
theorem PrimeDivisor.modulePullbackChartValue_genericFieldPullbackIso_stalkBaseChange
    (hQ : Q.1.hom ≫ (Z.genericStalkMorphism B S hS hX hdec).hom =
      yoneda.map ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) ≫ V.1.hom)
    (hb : (Z.baseChangeChart B S hS hX V).1.hom ≫ (Z.inclusion B S hS hX).hom =
      yoneda.map ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map
        (𝟙 (Z.baseChangeChart B S hS hX V)) ≫ (Z.baseChangeChartDiagram B S hS hX V).g) ≫
          V.1.hom)
    (hc : (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).1.hom ≫
        (Z.genericFieldToStalk B S hS hX hdec).hom =
      yoneda.map ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom) ≫
        Q.1.hom) :
    modulePullbackChartValue B S hS (Z.genericFieldToStalk B S hS hX hdec)
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
        ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
          (Z.restrictModule B S hS hX L))
        (Z.genericFieldPullbackIso B S hS hX hdec L).hom
        ⟨Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q, Q,
          (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom, hc⟩
        ((modulePullbackChartFMap B S hS (Z.genericStalkMorphism B S hS hX hdec) L).app
          ⟨Q, V, (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
            (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g, hQ⟩ (e V (𝟙 V))) =
      (modulePullbackChartFMap B S hS (Z.genericFieldMorphism B S hS hX hdec)
          (Z.restrictModule B S hS hX L)).app
        (Z.genericFieldChartDiagram B S hS hX hdec V
          (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)
          (Z.genericFieldStalkBaseChangeToChart B S hS hX hdec V Q ι)
          (Z.genericFieldStalkBaseChangeToChart_comm B S hS hX hdec V Q ι))
        (Z.baseChangeChartGenerator B S hS hX L V e (Z.baseChangeChart B S hS hX V)
          (𝟙 (Z.baseChangeChart B S hS hX V))) := by
  rw [Z.baseChangeChartGenerator_id_eq_modulePullbackChartFMap B S hS hX L V e hb]
  exact Z.modulePullbackChartValue_genericFieldPullbackIso_stalkBaseChange_aux B S hS hX
    hdec L V e Q ι hQ hb hc

/-- The square `(P, Spec κ(u)) → (Q, Spec 𝒪_{U, u})` of charts over the closed point. -/
theorem PrimeDivisor.genericFieldStalkBaseChange_toId_comp
    (hc : (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).1.hom ≫
        (Z.genericFieldToStalk B S hS hX hdec).hom =
      yoneda.map ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom) ≫
        Q.1.hom) :
    (SmallEtale.toOver B S hS (Z.genericFieldSpace B S hS hX hdec).1).map
        (chartToIdEtaleChart B S hS (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)) ≫
        (Z.genericFieldToStalkChartDiagram B S hS hX hdec).g =
      (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom ≫
        (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map
          (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)) := by
  apply yoneda.map_injective
  refine (yoneda.map_comp _ _).trans ?_
  refine (congrArg (· ≫ yoneda.map (Z.genericFieldToStalkChartDiagram B S hS hX hdec).g)
    (Functor.map_preimage yoneda _)).trans ?_
  refine hc.trans ?_
  refine Eq.trans ?_ (yoneda.map_comp _ _).symm
  refine congrArg (yoneda.map ((Z.representable_genericFieldToStalk B S hS hX hdec).snd
    Q.obj.hom) ≫ ·) ?_
  refine Eq.trans (CostructuredArrow.w ι.hom).symm ?_
  refine Eq.trans ?_ (yoneda.map_comp ι.hom.left
    (yoneda.preimage (Z.genericStalkBaseChangeChart B S hS hX hdec V).obj.hom)).symm
  exact congrArg (yoneda.map ι.hom.left ≫ ·) (Functor.map_preimage yoneda _).symm

/-- The image of `s_ξ` on a chart over `Spec κ(u)`, unfolded. -/
theorem PrimeDivisor.genericFieldGenerator_eq_modulePullbackChartValue
    (W : SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1)
    (k : W ⟶ Z.genericFieldChart B S hS hX hdec) :
    Z.genericFieldGenerator B S hS hX hdec L hL W k =
      (((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
        (Z.restrictModule B S hS hX L)).val.map k.op).hom
        (modulePullbackChartValue B S hS (Z.genericFieldToStalk B S hS hX hdec)
          ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L) _
          (Z.genericFieldPullbackIso B S hS hX hdec L).hom
          (Z.genericFieldToStalkChartDiagram B S hS hX hdec)
          (Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
            (𝟙 (Z.genericStalkChart B S hS hX hdec)))) := by
  unfold PrimeDivisor.genericFieldGenerator PrimeDivisor.genericFibreGenerator
  rfl

/-- **The image of `s_ξ` on `P`**: through `c^*(j^*ℒ) ≅ ρ_Z^*(ℒ|_Z)`, the inverse image along the
closed point of the generator `s_ξ` on `Q` is the image of `s_ξ` in the fibre restricted to `P`. -/
theorem PrimeDivisor.modulePullbackChartValue_genericFieldPullbackIso_genericStalkGenerator
    (hc : (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).1.hom ≫
        (Z.genericFieldToStalk B S hS hX hdec).hom =
      yoneda.map ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom) ≫
        Q.1.hom) :
    modulePullbackChartValue B S hS (Z.genericFieldToStalk B S hS hX hdec)
        ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
        ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
          (Z.restrictModule B S hS hX L))
        (Z.genericFieldPullbackIso B S hS hX hdec L).hom
        ⟨Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q, Q,
          (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom, hc⟩
        (Z.genericStalkGenerator B S hS hX hdec L hL Q
          (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V))) =
      Z.genericFieldGenerator B S hS hX hdec L hL
        (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)
        (chartToIdEtaleChart B S hS (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)) := by
  have h1 := modulePullbackChartValue_map B S hS (Z.genericFieldToStalk B S hS hX hdec)
    ((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L)
    ((modulePullback B S hS (Z.genericFieldMorphism B S hS hX hdec)).obj
      (Z.restrictModule B S hS hX L))
    (Z.genericFieldPullbackIso B S hS hX hdec L).hom
    (Z.genericFieldToStalkChartDiagram B S hS hX hdec)
    ⟨Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q, Q,
      (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom, hc⟩
    (chartToIdEtaleChart B S hS (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q))
    (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V))
    (Z.genericFieldStalkBaseChange_toId_comp B S hS hX hdec V Q ι hc)
    (Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
      (𝟙 (Z.genericStalkChart B S hS hX hdec)))
  have h2 : (((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L).val.map
      (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)).op).hom
        (Z.genericStalkGenerator B S hS hX hdec L hL (Z.genericStalkChart B S hS hX hdec)
          (𝟙 (Z.genericStalkChart B S hS hX hdec))) =
      Z.genericStalkGenerator B S hS hX hdec L hL Q
        (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V)) :=
    (Z.genericStalkGenerator_compat B S hS hX hdec L hL _ Q _ _).trans
      (congrArg (Z.genericStalkGenerator B S hS hX hdec L hL Q) (Category.comp_id _))
  rw [← h2]
  exact h1.trans (Z.genericFieldGenerator_eq_modulePullbackChartValue B S hS hX hdec L hL _ _).symm

include hcompat in
/-- **The ratio `w` of `e|_Z` to `s_ξ` on `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q` is the pullback of
the regular function `v` on `Q` with `e|_Q = v · s_ξ|_Q`.** -/
theorem PrimeDivisor.genericFieldChartRatio_stalkBaseChange_eq
    (hQ : Q.1.hom ≫ (Z.genericStalkMorphism B S hS hX hdec).hom =
      yoneda.map ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) ≫ V.1.hom)
    (hb : (Z.baseChangeChart B S hS hX V).1.hom ≫ (Z.inclusion B S hS hX).hom =
      yoneda.map ((SmallEtale.toOver B S hS Z.subspace.toFunctor).map
        (𝟙 (Z.baseChangeChart B S hS hX V)) ≫ (Z.baseChangeChartDiagram B S hS hX V).g) ≫
          V.1.hom)
    (hc : (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).1.hom ≫
        (Z.genericFieldToStalk B S hS hX hdec).hom =
      yoneda.map ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom) ≫
        Q.1.hom)
    (v : chartRing B S hS (Z.genericStalkSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).2 Q)
    (hv : modulePullbackChartSectionRestrict B S hS (Z.genericStalkMorphism B S hS hX hdec) L
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V) (e V (𝟙 V)) (𝟙 Q ≫ ι) =
      v • Z.genericStalkGenerator B S hS hX hdec L hL Q
        (ι ≫ chartToIdEtaleChart B S hS (Z.genericStalkBaseChangeChart B S hS hX hdec V))) :
    Z.genericFieldChartRatio B S hS hX hdec L hL V e
        (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)
        (Z.genericFieldStalkBaseChangeToChart B S hS hX hdec V Q ι)
        (Z.genericFieldStalkBaseChangeToChart_comm B S hS hX hdec V Q ι) =
      chartDiagramPullback B S hS (Z.genericFieldToStalk B S hS hX hdec)
        ⟨Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q, Q,
          (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom, hc⟩ v := by
  have key := (Z.modulePullbackChartValue_genericFieldPullbackIso_stalkBaseChange B S hS hX hdec
    L V e Q ι hQ hb hc).symm
  rw [Z.modulePullbackChartFMap_genericStalk_eq_restrict B S hS hX hdec L V e hcompat Q ι hQ, hv,
    modulePullbackChartValue_smul,
    Z.modulePullbackChartValue_genericFieldPullbackIso_genericStalkGenerator B S hS hX hdec
      L hL V Q ι hc] at key
  exact (Z.bijective_smul_genericFieldGenerator B S hS hX hdec L hL
    (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q)
    (chartToIdEtaleChart B S hS (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q))).1
    ((Z.modulePullbackChartFMap_baseChangeChartGenerator_eq_genericFieldChartRatio_smul B S hS
      hX hdec L hL V e _ _ _).symm.trans key)

end AlgebraicGeometry.Space

end
