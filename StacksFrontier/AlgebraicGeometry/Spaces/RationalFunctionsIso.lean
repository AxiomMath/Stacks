module

public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsChartIndependence

/-!
# Rational functions along an isomorphism

Let `e : X ≅ X'` be an isomorphism of algebraic spaces over a scheme `S`. A dense open subspace
`U ⊆ X` corresponds to the dense open subspace `e(U) = (e⁻¹)⁻¹(U)` of `X'`, and a morphism
`U → Y` to the morphism `e(U) → U → Y`. This is compatible with agreement on dense open
subspaces, so it carries rational maps `X ⇢ Y` to rational maps `X' ⇢ Y`, and for `Y` the
affine line it is a homomorphism of the rings of rational functions of Stacks 0EMP,

`e_* : R(X) → R(X')`.

It commutes with evaluation: the value of `e_* f` along a morphism `W → X → X'` is the value of
`f` along `W → X`. In particular, for an étale affine chart `c : U → X`, the pullback of `e_* f`
to the total ring of fractions of `Γ(U, 𝒪_U)` along `e ∘ c` is the pullback of `f` along `c`.

## Main definitions

* `AlgebraicGeometry.Space.PartialMap.mapIso` and `AlgebraicGeometry.Space.RationalMap.mapIso`:
  a partial or rational map transported along an isomorphism of the source.
* `AlgebraicGeometry.Space.rationalFunctionsMapIso`: the ring homomorphism `R(X) → R(X')`.

## Main results

* `AlgebraicGeometry.Space.evalSiteRingHom_rationalFunctionsMapIso`: evaluation commutes with
  the transport.
* `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_rationalFunctionsMapIso`: the
  same for the pullback to an étale affine chart.

## References

* [Stacks Project, Tag 0EMM](https://stacks.math.columbia.edu/tag/0EMM)
* [Stacks Project, Tag 0EMP](https://stacks.math.columbia.edu/tag/0EMP)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    (hX' : IsAlgebraicSpace B S hS X')

/-- The image of a dense open subspace under an isomorphism, read as the inverse image along the
inverse isomorphism, is a dense open subspace. -/
theorem isDenseOpenSubspace_preimage_inv (e : X ≅ X') {U : Subfunctor X}
    (hU : IsDenseOpenSubspace B S hS hX U) :
    IsDenseOpenSubspace B S hS hX' (U.preimage e.inv) := by
  refine ⟨isOpenSubspace_preimage B S hS e.inv U hX hX' hU.1, ?_⟩
  have hpts : Set.range (pointsMap B S hS (U.preimage e.inv).toFunctor (U.preimage e.inv).ι) =
      pointsMap B S hS X' e.inv ⁻¹' Set.range (pointsMap B S hS U.toFunctor U.ι) := by
    simpa using (preimage_image_pointsMap_of_isPullback B S hS
      (Subfunctor.isPullback_preimage e.inv U) Set.univ).symm
  rw [hpts]
  exact hU.2.preimage (pointsHomeomorphOfIso B S hS e.symm).isOpenMap

namespace PartialMap

/-- A partial map transported along an isomorphism `e : X ≅ X'` of its source: the domain is the
image of the domain, and the morphism is the composite through `e⁻¹`. -/
@[simps]
def mapIso (e : X ≅ X') (f : PartialMap B S hS hX Y) : PartialMap B S hS hX' Y where
  domain := f.domain.preimage e.inv
  dense_open_domain := isDenseOpenSubspace_preimage_inv hX' e f.dense_open_domain
  hom := f.domain.fromPreimage e.inv ≫ f.hom

/-- Transport along an isomorphism respects agreement on a dense open subspace. -/
theorem equivalent_mapIso (e : X ≅ X') {f g : PartialMap B S hS hX Y}
    (h : Equivalent B S hS f g) : Equivalent B S hS (f.mapIso hX' e) (g.mapIso hX' e) := by
  obtain ⟨W, hW, hWf, hWg, hfg⟩ := h
  refine ⟨W.preimage e.inv, isDenseOpenSubspace_preimage_inv hX' e hW,
    fun T y hy => hWf T hy, fun T y hy => hWg T hy, ?_⟩
  change W.fromPreimage e.inv ≫ Subfunctor.homOfLe hWf ≫ f.hom =
    W.fromPreimage e.inv ≫ Subfunctor.homOfLe hWg ≫ g.hom
  rw [hfg]

end PartialMap

/-- A rational map transported along an isomorphism of its source. -/
def RationalMap.mapIso (e : X ≅ X') : RationalMap B S hS hX Y → RationalMap B S hS hX' Y :=
  Quotient.map (PartialMap.mapIso hX' e) fun _ _ h => PartialMap.equivalent_mapIso hX' e h

/-- The transport of the rational map of a partial map `f` is the rational map of the transport of
`f`. -/
@[simp]
theorem RationalMap.mapIso_toRationalMap (e : X ≅ X') (f : PartialMap B S hS hX Y) :
    RationalMap.mapIso hX' e (f.toRationalMap B S hS) = (f.mapIso hX' e).toRationalMap B S hS :=
  rfl

/-- Two morphisms to the relative affine line with the same coordinates are equal. -/
private theorem hom_ext_affineLineCoordinate {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a b : Z ⟶ affineLineFunctor B S hS}
    (h : ∀ T x, affineLineCoordinate B S hS T (a.app T x) =
      affineLineCoordinate B S hS T (b.app T x)) : a = b := by
  ext T x
  exact affineLineCoordinate_injective B S hS T (h T x)

/-- A rational function represented on a common dense open subspace, transported. -/
private theorem mapIso_restrict (e : X ≅ X')
    (f : PartialMap B S hS hX (affineLineFunctor B S hS)) {V : Subfunctor X}
    (hV : IsDenseOpenSubspace B S hS hX V) (hVf : V ≤ f.domain) :
    RationalMap.mapIso hX' e (f.toRationalMap B S hS) =
      PartialMap.toRationalMap B S hS
        (⟨V.preimage e.inv, isDenseOpenSubspace_preimage_inv hX' e hV,
          V.fromPreimage e.inv ≫ Subfunctor.homOfLe hVf ≫ f.hom⟩ :
            PartialMap B S hS hX' (affineLineFunctor B S hS)) := by
  rw [← toRationalMap_restrict B S hS hX f hV hVf, RationalMap.mapIso_toRationalMap]
  rfl

/-- A transported representative with a prescribed morphism. -/
private theorem toRationalMap_mapIso_mk (e : X ≅ X') {U : Subfunctor X}
    (hU : IsDenseOpenSubspace B S hS hX U) {ν : U.toFunctor ⟶ affineLineFunctor B S hS}
    {ν' : (U.preimage e.inv).toFunctor ⟶ affineLineFunctor B S hS}
    (h : ∀ T x, affineLineCoordinate B S hS T (ν'.app T x) =
      affineLineCoordinate B S hS T ((U.fromPreimage e.inv ≫ ν).app T x)) :
    RationalMap.mapIso hX' e (PartialMap.toRationalMap B S hS
        (⟨U, hU, ν⟩ : PartialMap B S hS hX (affineLineFunctor B S hS))) =
      PartialMap.toRationalMap B S hS
        (⟨U.preimage e.inv, isDenseOpenSubspace_preimage_inv hX' e hU, ν'⟩ :
          PartialMap B S hS hX' (affineLineFunctor B S hS)) := by
  rw [hom_ext_affineLineCoordinate h]
  rfl

/-- **Rational functions along an isomorphism.** The ring homomorphism `R(X) → R(X')` induced
by an isomorphism `e : X ≅ X'` of algebraic spaces over `S`. -/
def rationalFunctionsMapIso (e : X ≅ X') :
    rationalFunctions B S hS hX →+* rationalFunctions B S hS hX' where
  toFun := RationalMap.mapIso hX' e
  map_one' := by
    obtain ⟨-, o, -, ho, -, hoR⟩ :=
      exists_zero_one_rep B S hS hX ⊤ (isDenseOpenSubspace_top B S hS hX)
    obtain ⟨-, o', -, ho', -, hoR'⟩ := exists_zero_one_rep B S hS hX'
      ((⊤ : Subfunctor X).preimage e.inv)
      (isDenseOpenSubspace_preimage_inv hX' e (isDenseOpenSubspace_top B S hS hX))
    rw [← hoR, ← hoR']
    exact toRationalMap_mapIso_mk hX' e _ fun T x => (ho' T x).trans (ho T _).symm
  map_mul' x y := by
    obtain ⟨f, rfl⟩ := RationalMap.exists_rep B S hS x
    obtain ⟨g, rfl⟩ := RationalMap.exists_rep B S hS y
    obtain ⟨V, hV, hVf, hVg⟩ :=
      exists_isDenseOpenSubspace_le B S hS hX f.dense_open_domain g.dense_open_domain
    obtain ⟨n, hn, hnR⟩ := exists_mul_rep B S hS hX V hV
      (Subfunctor.homOfLe hVf ≫ f.hom) (Subfunctor.homOfLe hVg ≫ g.hom)
    obtain ⟨n', hn', hnR'⟩ := exists_mul_rep B S hS hX' (V.preimage e.inv)
      (isDenseOpenSubspace_preimage_inv hX' e hV)
      (V.fromPreimage e.inv ≫ Subfunctor.homOfLe hVf ≫ f.hom)
      (V.fromPreimage e.inv ≫ Subfunctor.homOfLe hVg ≫ g.hom)
    change RationalMap.mapIso hX' e _ = RationalMap.mapIso hX' e _ * RationalMap.mapIso hX' e _
    rw [← toRationalMap_restrict B S hS hX f hV hVf, ← toRationalMap_restrict B S hS hX g hV hVg,
      ← hnR, toRationalMap_mapIso_mk hX' e hV (ν' := n') fun T z => (hn' T z).trans (hn T _).symm,
      hnR']
    rfl
  map_zero' := by
    obtain ⟨z, -, hz, -, hzR, -⟩ :=
      exists_zero_one_rep B S hS hX ⊤ (isDenseOpenSubspace_top B S hS hX)
    obtain ⟨z', -, hz', -, hzR', -⟩ := exists_zero_one_rep B S hS hX'
      ((⊤ : Subfunctor X).preimage e.inv)
      (isDenseOpenSubspace_preimage_inv hX' e (isDenseOpenSubspace_top B S hS hX))
    rw [← hzR, ← hzR']
    exact toRationalMap_mapIso_mk hX' e _ fun T x => (hz' T x).trans (hz T _).symm
  map_add' x y := by
    obtain ⟨f, rfl⟩ := RationalMap.exists_rep B S hS x
    obtain ⟨g, rfl⟩ := RationalMap.exists_rep B S hS y
    obtain ⟨V, hV, hVf, hVg⟩ :=
      exists_isDenseOpenSubspace_le B S hS hX f.dense_open_domain g.dense_open_domain
    obtain ⟨a, ha, haR⟩ := exists_add_rep B S hS hX V hV
      (Subfunctor.homOfLe hVf ≫ f.hom) (Subfunctor.homOfLe hVg ≫ g.hom)
    obtain ⟨a', ha', haR'⟩ := exists_add_rep B S hS hX' (V.preimage e.inv)
      (isDenseOpenSubspace_preimage_inv hX' e hV)
      (V.fromPreimage e.inv ≫ Subfunctor.homOfLe hVf ≫ f.hom)
      (V.fromPreimage e.inv ≫ Subfunctor.homOfLe hVg ≫ g.hom)
    change RationalMap.mapIso hX' e _ = RationalMap.mapIso hX' e _ + RationalMap.mapIso hX' e _
    rw [← toRationalMap_restrict B S hS hX f hV hVf, ← toRationalMap_restrict B S hS hX g hV hVg,
      ← haR, toRationalMap_mapIso_mk hX' e hV (ν' := a') fun T z => (ha' T z).trans (ha T _).symm,
      haR']
    rfl

/-- The ring homomorphism `rationalFunctionsMapIso` sends a rational function to its transport
`RationalMap.mapIso`. -/
theorem rationalFunctionsMapIso_apply (e : X ≅ X') (x : rationalFunctions B S hS hX) :
    rationalFunctionsMapIso hX' e x = RationalMap.mapIso hX' e x :=
  rfl

/-- **Evaluation commutes with the transport of rational functions.** For a morphism
`m : W → X` meeting every dense open subspace, the value of `e_* f` along `m' = e ∘ m` is the
value of `f` along `m`. -/
theorem evalSiteRingHom_rationalFunctionsMapIso (e : X ≅ X') {W : BigFppfOver B S hS}
    {m : yoneda.obj W ⟶ X} {m' : yoneda.obj W ⟶ X'} (hmm' : m' = m ≫ e.hom)
    (hm : FactorsThroughDenseOpens B S hS hX W m) (hm' : FactorsThroughDenseOpens B S hS hX' W m')
    (x : rationalFunctions B S hS hX) :
    evalSiteRingHom B S hS hX' hm' (rationalFunctionsMapIso hX' e x) =
      evalSiteRingHom B S hS hX hm x := by
  subst hmm'
  obtain ⟨f, rfl⟩ := RationalMap.exists_rep B S hS x
  obtain ⟨j, hj⟩ := hm f.domain f.dense_open_domain
  have hrange : Subfunctor.range (m ≫ e.hom) ≤ f.domain.preimage e.inv := by
    rintro T - ⟨t, rfl⟩
    change e.inv.app T (e.hom.app T (m.app T t)) ∈ f.domain.obj T
    rw [← hj]
    simp
  rw [rationalFunctionsMapIso_apply, RationalMap.mapIso_toRationalMap,
    evalSiteRingHom_eq B S hS hX' hm' (f.mapIso hX' e) (Subfunctor.lift (m ≫ e.hom) hrange)
      (Subfunctor.lift_ι _ _),
    evalSiteRingHom_eq B S hS hX hm f j hj]
  congr 2
  refine NatTrans.ext (funext fun T => ?_)
  ext t
  change f.hom.app T _ = f.hom.app T _
  congr 1
  refine Subtype.ext ?_
  change e.inv.app T (e.hom.app T (m.app T t)) = (j.app T t).1
  rw [← hj]
  simp

/-- **The pullback to an étale affine chart commutes with the transport.** For an étale chart
`c : U → X` whose scheme is affine, reduced and locally Noetherian, the pullback of `e_* f` to
`Q(Γ(U, 𝒪_U))` along `e ∘ c` is the pullback of `f` along `c`. -/
theorem rationalFunctionsToTotalFractionRing_rationalFunctionsMapIso (e : X ≅ X')
    (U : BigFppfOver B S hS) [IsAffine U.left.1] [IsReduced U.left.1]
    [IsLocallyNoetherian U.left.1] (c : yoneda.obj U ⟶ X) (hc : IsEtale B S hS c)
    (c' : yoneda.obj U ⟶ X') (hc' : IsEtale B S hS c') (hcc' : c' = c ≫ e.hom)
    (x : rationalFunctions B S hS hX) :
    rationalFunctionsToTotalFractionRing B S hS hX' U c' hc' (rationalFunctionsMapIso hX' e x) =
      rationalFunctionsToTotalFractionRing B S hS hX U c hc x := by
  unfold rationalFunctionsToTotalFractionRing
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.left.1, ⊤)))).hom.hom
    (evalSiteRingHom_rationalFunctionsMapIso hX' e (by rw [hcc', Category.assoc])
      (factorsThroughDenseOpens_totalFractionObject B S hS hX U c hc) _ x)

end AlgebraicGeometry.Space

end
