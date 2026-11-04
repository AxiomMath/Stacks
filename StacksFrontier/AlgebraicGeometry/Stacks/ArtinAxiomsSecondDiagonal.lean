module

public import StacksFrontier.AlgebraicGeometry.Spaces.ArtinAxiomsAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphismRepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ArtinCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointSizeBound
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalRepresentableOfDiagonalPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalCriterion
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.Deformation.Artin.FormalObject.DiagonalBaseChangeEffective
public import StacksFrontier.Deformation.Artin.Versality.DiagonalBaseChangeOpenness
public import StacksFrontier.Deformation.ArtinCriteria.DiagonalBaseChangeTangent

/-!
# Artin's axioms with a representable second diagonal (Stacks 07Y5)

**Stacks 07Y5.** Let `S` be a locally Noetherian scheme and `𝒳` a category fibred in groupoids
over `(Sch/S)_{fppf}` such that `Δ_Δ : 𝒳 ⟶ 𝒳 ×_{𝒳 × 𝒳} 𝒳` is representable by algebraic spaces,
`𝒳` satisfies Artin's axioms [-1], [0], [1], [2], [3], [4], [5] of Section 07XJ, and the local
rings of `S` at its finite type points are G-rings. Then `𝒳` is an algebraic stack.

The proof is the source's. For an affine scheme `V` locally of finite presentation over `S` and a
point `y` of `𝒳 × 𝒳` over `V`, the 2-fibre product `𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` is
fibred in setoids, and its functor of isomorphism classes `Y` satisfies the hypotheses of
Proposition 07Y1:

* its diagonal is representable by Stacks 07WG (from `Δ_Δ`), transported along the exchange of
  the two factors of the 2-fibre product;
* axiom [-1] comes from axiom [-1] for `𝒳`, axiom [0] from Stacks 0432 and 05UI, axiom [1] from
  Stacks 07XM, axiom [2] from Stacks 07WQ and 07WR, axiom [3] from Stacks 07X1 and 07X2, axiom [4]
  from Stacks 07X8 and 07X9, axiom [5] from openness of versality for `Δ`.

The core of the proof of Proposition 07Y1 (for a category fibred in setoids) then makes `Y` an
algebraic space, and its atlas, a scheme locally of finite type over `S` mapping smoothly and
surjectively onto `Y`, makes `Y` locally of finite type over `S` by Stacks 06NR. By Stacks 07WH
(with the set-theoretic condition of its footnote) the diagonal of `𝒳` is representable, and
Lemma 07Y4 concludes.

## Main results

* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_diagonalPointCategory`: the diagonal of `𝒴`
  is representable by algebraic spaces once `Δ_Δ` is.
* `AlgebraicGeometry.Space.isAlgebraicSpace_and_exists_isLocallyOfFiniteType_of_artinAxioms`:
  the algebraic space of the core of Stacks 07Y1 is locally of finite type over `S`.
* `AlgebraicGeometry.Stack.isAlgebraicSpace_diagonalPointFunctorOverBase_of_artinAxioms`: `Y` is
  an algebraic space locally of finite type over `S`.
* `AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_artinAxioms_of_secondDiagonal`: the
  diagonal of `𝒳` is representable.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_artinAxioms_of_secondDiagonal`: **Stacks 07Y5**.

## References

* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
* [Stacks Project, Tag 07Y1](https://stacks.math.columbia.edu/tag/07Y1)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 07WH](https://stacks.math.columbia.edu/tag/07WH)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

open AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The algebraic space of the core of Stacks 07Y1 is locally of finite type over `S`.** Under
the hypotheses of `AlgebraicGeometry.Space.isAlgebraicSpace_isoClassPresheafModel_of_artinAxioms`,
the model of the presheaf of isomorphism classes of `𝒵` is an algebraic space whose structure
morphism is locally of finite type.

The atlas of the proof, a scheme `W` locally of finite type over `S`
(`AlgebraicGeometry.Space.exists_locallyOfFiniteType_smooth_surjective_atlas_of_artinAxioms`),
maps onto the model by a smooth surjective morphism, which is a surjection of fppf sheaves; as
`W → S` is locally of finite type, Stacks 06NR concludes. -/
theorem isAlgebraicSpace_and_exists_isLocallyOfFiniteType_of_artinAxioms
    [IsLocallyNoetherian S]
    (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    [𝒵.val.p.IsFibered] [𝒵.val.p.IsFiberedInSetoids]
    [CategoryTheory.FunctorToTypes.Small.{u} 𝒵.val.p.isoClassPresheaf]
    (hdiag : HasRepresentableDiagonal B S hS 𝒵)
    (hsize : IsSizeBounded B S hS 𝒵)
    (hsheaf : Presheaf.IsSheaf ((AlgebraicGeometry.etaleTopology B).over (B.obj hS))
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒵.val.p))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒵)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒵.val.p 𝒵.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒵)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B S hS 𝒵.val.p,
      Deformation.Artin.FormalObject.IsEffective B S hS 𝒵.val.p 𝒵.property ξ)
    (hopen : ∀ U : Over S, LocallyOfFiniteType U.hom →
      ∀ (y : 𝒵.val.obj) (hy : (𝒵.val.p ⋙ Over.post B.inclusion).obj y = U) (u : U.left),
        AlgebraicGeometry.IsFiniteTypePoint u →
        Deformation.Artin.IsVersalAt U (𝒵.val.p ⋙ Over.post B.inclusion) u y hy →
        ∃ V : U.left.Opens, u ∈ V.1 ∧
          ∀ u' : U.left, u' ∈ V.1 →
            AlgebraicGeometry.IsFiniteTypePoint u' →
            Deformation.Artin.IsVersalAt U (𝒵.val.p ⋙ Over.post B.inclusion) u' y hy)
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace B S hS (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒵.val.p) ∧
      ∃ t : CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒵.val.p ⟶
          yoneda.obj (Over.mk (𝟙 (B.obj hS))),
        IsLocallyOfFiniteType B S hS t := by
  classical
  have hY := isAlgebraicSpace_isoClassPresheafModel_of_artinAxioms B S hS 𝒵 hdiag hsize hsheaf
    hlimit hRS htangent heffective hopen hG
  refine ⟨hY, (baseYoneda_isTerminal B S hS).from _, ?_⟩
  obtain ⟨W, hW, g, hrep, hsurj, hsmooth⟩ :=
    exists_locallyOfFiniteType_smooth_surjective_atlas_of_artinAxioms B S hS 𝒵 hdiag hsize
      hsheaf hlimit hRS htangent heffective hopen hG
  -- the atlas, read on the models of the presheaves of isomorphism classes
  let 𝒰 := schemeFibredCategory B S hS W
  obtain ⟨h𝒰set, h𝒰iso⟩ := (isRepresentableByAlgebraicSpace_iff B S hS 𝒰).1
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  let : 𝒰.val.p.IsFibered := 𝒰.isFiberedInGroupoids.isFibered
  have : CategoryTheory.FunctorToTypes.Small.{u} 𝒰.val.p.isoClassPresheaf :=
    small_isoClassPresheaf_of_isAlgebraicSpaceIsoClassPresheaf B S hS _ h𝒰iso
  let 𝒵s : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk 𝒵.val inferInstance
  let 𝒰s : CatFiberedInSetoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInSetoids.mk 𝒰.val h𝒰set
  let fs : 𝒰s ⟶ 𝒵s := Bicategory.InducedBicategory.mkHom g
  let a := CategoryTheory.Functor.isoClassPresheafModelMap.{u} 𝒰s.val.p 𝒵s.val.p
    (CatFiberedInGroupoids.homFunctor_comp_p fs)
  have ha : IsoClassCompatible B S hS fs
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒰s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒵s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒰s.val.p)
      (CategoryTheory.Functor.isoClassPresheafModelEquiv.{u} 𝒵s.val.p) a := fun V z =>
    CategoryTheory.Functor.isoClassPresheafModelMap_app_isoClassMk.{u} 𝒰s.val.p 𝒵s.val.p _ z
  have hfrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInSetoids.inclusion.map fs).hom := hrep
  have harep := (isoClassMap_isRepresentableByAlgebraicSpaces_iff_model.{u, u, u + 1}
    B S hS fs a ha).2 hfrep
  have hasurj := (isoClassMap_holdsOnEverySchemePoint_iff_model.{u, u, u + 1, u + 1} B S hS fs
    (surjectiveMorphismProperty B S hS) a ha hfrep).2 hsurj
  have hasmooth := (isoClassMap_holdsOnEverySchemePoint_iff_model.{u, u, u + 1, u + 1} B S hS fs
    (smoothMorphismProperty B S hS) a ha hfrep).2 hsmooth
  -- a smooth surjective morphism is a surjection of sheaves
  have hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a :=
    Presheaf.isLocallySurjective_of_le
      (GrothendieckTopology.over_le_over_of_le (etaleTopology_le_topology B) (B.obj hS)) a
      (isLocallySurjective_etaleTopology_of_space_atlas_smooth B S hS a harep hasurj hasmooth)
  -- the model of the presheaf of isomorphism classes of `(Sch/W)_{fppf}` is `h_W`
  let eW (U : (BigFppfOver B S hS)ᵒᵖ) : 𝒰.val.p.isoClassPresheaf.obj U ≃ (yoneda.obj W).obj U :=
    PresheafOfCategories.elementsIsoClassEquiv (yoneda.obj W)
      (PresheafOfCategories.sliceElementsEquivalenceOver W) U.unop
  have hnatW : ∀ ⦃U U' : (BigFppfOver B S hS)ᵒᵖ⦄ (f : U ⟶ U')
      (z : 𝒰.val.p.isoClassPresheaf.obj U),
      eW U' (𝒰.val.p.isoClassPresheaf.map f z) = (yoneda.obj W).map f (eW U z) :=
    fun _ _ f z => PresheafOfCategories.elementsIsoClassEquiv_naturality 𝒰.isFiberedInGroupoids
      (yoneda.obj W) (PresheafOfCategories.sliceElementsEquivalenceOver W) f.unop z
  let iW : CategoryTheory.Functor.isoClassPresheafModel.{u} 𝒰.val.p ≅ yoneda.obj W :=
    CategoryTheory.Functor.isoClassPresheafModelIso.{u} 𝒰.val.p eW hnatW
  have hfloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (iW.inv ≫ a) :=
    have := hloc
    inferInstance
  have hcomp : IsLocallyOfFiniteType B S hS
      ((iW.inv ≫ a) ≫ (baseYoneda_isTerminal B S hS).from _) := by
    rw [(baseYoneda_isTerminal B S hS).hom_ext ((iW.inv ≫ a) ≫ _)
      (yoneda.map (Over.homMk W.hom : W ⟶ Over.mk (𝟙 (B.obj hS))))]
    exact (isLocallyOfFiniteType_yoneda_map_iff B S hS _).2 hW
  exact isLocallyOfFiniteType_of_comp_of_locallySurjective B S hS
    (isAlgebraicSpace_yoneda B S hS W) hY (isAlgebraicSpace_yoneda B S hS _) (iW.inv ≫ a) _
    hcomp hfloc

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {V : BigFppfOver B S hS}
  {y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj}

variable (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)

/-- **The category `𝒴` of the proof of Stacks 07Y5**: the 2-fibre product
`(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`, as a category fibred in groupoids over `(Sch/S)_{fppf}`
through its structure functor. -/
abbrev diagonalPointCategory : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (diagonalPointFibreOverBase B S hS 𝒳 V y))
    (diagonalPointFibreOverBase_isFiberedInGroupoids hy)

/-- **The diagonal of `𝒴` is representable by algebraic spaces** once the second diagonal of `𝒳`
is (the step "`Δ_𝒴` is representable by algebraic spaces by condition (1) and Lemma 07WG" of the
proof of Stacks 07Y5). Stacks 07WG gives this for `𝒳 ×_{Δ, 𝒳 × 𝒳, y} (Sch/V)_{fppf}`, and
exchanging the two factors is an equivalence over the site. -/
theorem hasRepresentableDiagonal_diagonalPointCategory
    (hΔΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
        (diagonalBasedFunctor B S hS 𝒳))) :
    HasRepresentableDiagonal B S hS (diagonalPointCategory hy) := by
  let 𝒱 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (Over.map V.hom))
      (Functor.IsFiberedInGroupoids.over_map V.hom)
  let g : 𝒱.val ⥤ᵇ (CatFiberedInGroupoids.product 𝒳 𝒳).val := ⟨y, hy⟩
  let 𝒲 := twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒱
    (diagonalBasedFunctor B S hS 𝒳) g
  have hswap : (TwoFibreProductOver.swap 𝒳.val.p (Over.map V.hom)
      (CatFiberedInGroupoids.product 𝒳 𝒳).val.p (diagonalBasedFunctor B S hS 𝒳).toFunctor
      y).IsEquivalence := inferInstance
  let e : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p (diagonalPointCategory hy).val.p :=
    StacksRepresentableCFG.equivalenceOverOfIsEquivalence 𝒲.property
      (diagonalPointCategory hy).property
      (TwoFibreProductOver.swap 𝒳.val.p (Over.map V.hom)
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p (diagonalBasedFunctor B S hS 𝒳).toFunctor y)
      rfl hswap
  exact (hasRepresentableDiagonal_iff_of_equivalence B S hS e.toBasedEquivalence).1
    ((hasRepresentableDiagonal_iff B S hS 𝒲).2
      (isRepresentableByAlgebraicSpaces_diagonal_baseChange_of_secondDiagonal.{u, u, u + 1, u, u}
        B S hS 𝒳 𝒱 g hΔΔ (Stacks.RepresentableMorphism.isRepresentableCFG_overMap V)))

/-- **`Y` is an algebraic space locally of finite type over `S`** (the second paragraph of the
proof of Stacks 07Y5). Let `S` be locally Noetherian, `𝒳` a category fibred in groupoids over
`(Sch/S)_{fppf}` whose second diagonal is representable by algebraic spaces and which satisfies
Artin's axioms [-1] (in the arrows half of the footnote of Section 07XJ), [0], [1], [2], [3], [4],
let `V` be an affine scheme locally of finite presentation over `S` and `y` a point of `𝒳 × 𝒳`
over `V` such that `Δ` satisfies openness of versality at `y`, and let the local rings of `S` at
its finite type points be G-rings. Then the functor `Y` of isomorphism classes of
`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` is an algebraic space locally of finite type over `S`.

The hypotheses of the core of Stacks 07Y1 for `𝒴` are
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_diagonalPointCategory` (Stacks 07WG),
`AlgebraicGeometry.Stack.diagonalPointFibreOverBase_isSizeBounded` (axiom [-1]),
`AlgebraicGeometry.Stack.isSheaf_diagonalPointFunctorOverBase` (Stacks 0432, 05UI),
`AlgebraicGeometry.Stack.isLimitPreserving_of_equivalenceOver_diagonalPointFibreOverBase`
(Stacks 07XM), `Deformation.Artin.satisfiesRS_diagonalBaseChange` (Stacks 07WQ, 07WR),
`Deformation.Artin.hasFiniteDimensionalTangentSpacesOf_diagonalBaseChange` (Stacks 07X1, 07X2),
`Deformation.Artin.isEffective_of_equivalenceOver_diagonalBaseChange` (Stacks 07X8, 07X9) and
`Deformation.Artin.hasOpenVersality_diagonalBaseChange`. -/
theorem isAlgebraicSpace_diagonalPointFunctorOverBase_of_artinAxioms [IsLocallyNoetherian S]
    [IsAffine V.left.1] (hV : LocallyOfFinitePresentation (B.inclusion.map V.hom))
    (hΔΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
        (diagonalBasedFunctor B S hS 𝒳)))
    (hsize : ∃ T₀ : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        Cardinal.lift.{u, u + 1} (Cardinal.mk (Σ a b : 𝒳.val.p.Fiber U, a ⟶ b)) ≤
          Cardinal.lift.{u + 1, u} T₀.left.1.size)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (hInf : Deformation.Artin.HasFiniteDimensionalInfinitesimalAutomorphismsOf B S hS 𝒳.val.p)
    (happrox : (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p 𝒳.property).IsEquivalence)
    (hopenΔ : Deformation.Artin.HasOpenVersality
      (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
        (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (diagonalBasedFunctor B S hS 𝒳).toFunctor ⋙ Over.post B.inclusion))
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicSpace B S hS (diagonalPointFunctorOverBase hy) ∧
      ∃ t : diagonalPointFunctorOverBase hy ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))),
        Space.IsLocallyOfFiniteType B S hS t := by
  let : (diagonalPointCategory hy).val.p.IsFibered :=
    (diagonalPointFibreOverBase_isFiberedInGroupoids hy).isFibered
  let : (diagonalPointCategory hy).val.p.IsFiberedInSetoids :=
    diagonalPointFibreOverBase_isFiberedInSetoids hy
  let : CategoryTheory.FunctorToTypes.Small.{u}
      (diagonalPointCategory hy).val.p.isoClassPresheaf :=
    small_isoClassPresheaf_diagonalPointFibreOverBase hy
  have : LocallyOfFinitePresentation (B.inclusion.map V.hom) := hV
  have : (AlgebraicGeometry.etaleTopology B).Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le (etaleTopology_le_topology B)
  exact Space.isAlgebraicSpace_and_exists_isLocallyOfFiniteType_of_artinAxioms
    B S hS (diagonalPointCategory hy)
    (hasRepresentableDiagonal_diagonalPointCategory hy hΔΔ)
    (diagonalPointFibreOverBase_isSizeBounded (y := y) hsize)
    (isSheaf_diagonalPointFunctorOverBase hy (AlgebraicGeometry.etaleTopology B) hstack)
    (isLimitPreserving_of_equivalenceOver_diagonalPointFibreOverBase B S hS 𝒳 hlimit V hV y hy
      (diagonalPointCategory hy) (StacksRepresentableCFG.EquivalenceOver.refl _))
    (Deformation.Artin.satisfiesRS_diagonalBaseChange B S hS 𝒳 hRS V y hy)
    ((Deformation.Artin.hasFiniteDimensionalTangentSpaces_iff B S hS _).2
      (Deformation.Artin.hasFiniteDimensionalTangentSpacesOf_diagonalBaseChange B S hS 𝒳 hRS
        htangent hInf V y hy))
    (fun ξ => Deformation.Artin.isEffective_of_equivalenceOver_diagonalBaseChange 𝒳
      happrox V y hy (StacksRepresentableCFG.EquivalenceOver.refl _) _ ξ)
    (Deformation.Artin.hasOpenVersality_diagonalBaseChange B S hS 𝒳 V y hopenΔ)
    hG

omit hy

/-- **The diagonal of `𝒳` is representable by algebraic spaces** under the hypotheses of
Stacks 07Y5 (its first paragraph, with the set-theoretic condition of the footnote): every functor
`Y` is an algebraic space locally of finite type over `S`
(`AlgebraicGeometry.Stack.isAlgebraicSpace_diagonalPointFunctorOverBase_of_artinAxioms`), so
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_isAlgebraicSpace_diagonalPointFunctorOverBase`
(Stacks 07WH) applies, with the bound of axiom [-1] as the size of the object `T` it provides. -/
theorem hasRepresentableDiagonal_of_artinAxioms_of_secondDiagonal [IsLocallyNoetherian S]
    (hΔΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
        (diagonalBasedFunctor B S hS 𝒳)))
    (hsize : ∃ T₀ : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        Cardinal.lift.{u, u + 1} (Cardinal.mk (Σ a b : 𝒳.val.p.Fiber U, a ⟶ b)) ≤
          Cardinal.lift.{u + 1, u} T₀.left.1.size)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (hInf : Deformation.Artin.HasFiniteDimensionalInfinitesimalAutomorphismsOf B S hS 𝒳.val.p)
    (happrox : (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p 𝒳.property).IsEquivalence)
    (hopenΔ : ∀ V : BigFppfOver B S hS, LocallyOfFiniteType (B.inclusion.map V.hom) →
      ∀ (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj),
        y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom →
        Deformation.Artin.HasOpenVersality
          (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
            (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
            (diagonalBasedFunctor B S hS 𝒳).toFunctor ⋙ Over.post B.inclusion))
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    HasRepresentableDiagonal B S hS 𝒳 := by
  obtain ⟨T₀, hT₀⟩ := hsize
  refine hasRepresentableDiagonal_of_isAlgebraicSpace_diagonalPointFunctorOverBase hlimit hstack
    T₀.left.1.size T₀.left.2 hT₀ fun V hVaff hVlfp y hy => ?_
  have : IsAffine V.left.1 := hVaff
  have : LocallyOfFinitePresentation (B.inclusion.map V.hom) := hVlfp
  exact isAlgebraicSpace_diagonalPointFunctorOverBase_of_artinAxioms hy hVlfp hΔΔ ⟨T₀, hT₀⟩
    hstack hlimit hRS htangent hInf happrox (hopenΔ V inferInstance y hy) hG

section Statement

universe z

variable (B S hS)

/-- **Lemma 07Y4, with axiom [0] for the étale topology and axiom [4] as an equivalence**, the form
in which the proof of Stacks 07Y5 closes: a category fibred in groupoids over a locally Noetherian
`S` with representable diagonal satisfying axioms [-1] (the isomorphism-class half), [0], [1],
[2], the tangent half of [3], [4] and openness of versality, over a base whose local rings at
finite type points are G-rings, is an algebraic stack. Axiom [4] gives the effectivity of every
formal object, an equivalence being essentially surjective. -/
theorem isAlgebraicStack_of_artinAxioms_of_isEquivalence_approximationFunctor
    [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hdiag : HasRepresentableDiagonal B S hS 𝒳)
    (hsize : IsSizeBounded B S hS 𝒳)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (happrox : (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p 𝒳.property).IsEquivalence)
    (hopen : Deformation.Artin.HasOpenVersality (𝒳.val.p ⋙ Over.post B.inclusion))
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicStack.{u, z, u, u + 1} B S hS 𝒳.val :=
  isAlgebraicStack_of_artinAxioms.{u, u, u + 1, z} B S hS 𝒳 hdiag hsize hstack hlimit hRS
    htangent (fun ξ => happrox.essSurj.mem_essImage ξ) hopen hG

/-- **Stacks 07Y5 (Artin's axioms, second diagonal form).** Let `S` be a locally Noetherian
scheme and `𝒳` a category fibred in groupoids over the big fppf site of `S`. Assume that

1. the second diagonal `Δ_Δ : 𝒳 ⟶ 𝒳 ×_{𝒳 × 𝒳} 𝒳` is representable by algebraic spaces,
2. `𝒳` satisfies Artin's axioms of Section 07XJ: [-1] the cardinalities of the sets of
   isomorphism classes of objects and of the sets of arrows of the fibres of `𝒳` over the finite
   type fields over `S` are bounded by the size of one object of the site; [0] `𝒳` is a stack
   in groupoids for the étale topology; [1] `𝒳` is limit preserving; [2] `𝒳` satisfies the
   Rim–Schlessinger condition; [3] the tangent spaces and the infinitesimal automorphism spaces
   of `𝒳` at the finite type field-valued points are finite dimensional; [4] the functor of
   Stacks 07X6 from objects over complete local bases to formal objects is an equivalence;
   [5] `𝒳` and `Δ : 𝒳 ⟶ 𝒳 × 𝒳` satisfy openness of versality (Stacks 07XQ: for `Δ`, for every
   scheme `V` locally of finite type over `S` and every point `y` of `𝒳 × 𝒳` over `V`, the
   2-fibre product `(Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` has openness of versality), and
3. the local rings `𝒪_{S,s}` at the finite type points `s` of `S` are G-rings.

Then `𝒳` is an algebraic stack.

Openness of versality is written out (`Deformation.Artin.HasOpenVersality`) rather than through
`Deformation.Artin.IsOpenVersality`, whose fibred-in-groupoids hypothesis over all schemes over
`S` cannot hold for a category over the bounded big fppf site. A point `y` of `𝒳 × 𝒳` over `V` is
given, by the 2-Yoneda lemma, as a 1-morphism `(Sch/V)_{fppf} ⟶ 𝒳 × 𝒳` over the site.

The proof is the source's:
`AlgebraicGeometry.Stack.hasRepresentableDiagonal_of_artinAxioms_of_secondDiagonal` makes the
diagonal representable (Stacks 07WH, 07WG and Proposition 07Y1 for the functors `Y`), and
Lemma 07Y4 concludes. -/
@[stacks 07Y5]
theorem isAlgebraicStack_of_artinAxioms_of_secondDiagonal [IsLocallyNoetherian S]
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hΔΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
        (diagonalBasedFunctor B S hS 𝒳)))
    (hsize : ∃ T : BigFppfOver B S hS,
      ∀ (U : BigFppfOver B S hS) (k : Type u) [Field k],
        U.left.1 = Spec (.of k) → Deformation.Artin.IsFiniteTypeOver B S hS U →
        Cardinal.lift.{u, u + 1}
            (Cardinal.mk (Quotient (isIsomorphicSetoid (𝒳.val.p.Fiber U)))) ≤
          Cardinal.lift.{u + 1, u} T.left.1.size ∧
        Cardinal.lift.{u, u + 1} (Cardinal.mk (Σ a b : 𝒳.val.p.Fiber U, a ⟶ b)) ≤
          Cardinal.lift.{u + 1, u} T.left.1.size)
    (hstack : 𝒳.val.p.IsStackInGroupoids.{u + 1}
      ((AlgebraicGeometry.etaleTopology B).over (B.obj hS)))
    (hlimit : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRS B S hS 𝒳.val.p 𝒳.property)
    (htangent : HasFiniteDimensionalTangentSpaces B S hS 𝒳)
    (hInf : Deformation.Artin.HasFiniteDimensionalInfinitesimalAutomorphismsOf B S hS 𝒳.val.p)
    (happrox : (Deformation.Artin.approximationFunctor B S hS 𝒳.val.p 𝒳.property).IsEquivalence)
    (hopen : Deformation.Artin.HasOpenVersality (𝒳.val.p ⋙ Over.post B.inclusion))
    (hopenΔ : ∀ V : BigFppfOver B S hS, LocallyOfFiniteType (B.inclusion.map V.hom) →
      ∀ (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj),
        y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom →
        Deformation.Artin.HasOpenVersality
          (TwoFibreProductOver.fst (Over.map V.hom) 𝒳.val.p
            (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
            (diagonalBasedFunctor B S hS 𝒳).toFunctor ⋙ Over.post B.inclusion))
    (hG : ∀ s : S, AlgebraicGeometry.IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    IsAlgebraicStack.{u, z, u, u + 1} B S hS 𝒳.val := by
  obtain ⟨T, hT⟩ := hsize
  exact isAlgebraicStack_of_artinAxioms_of_isEquivalence_approximationFunctor B S hS 𝒳
    (hasRepresentableDiagonal_of_artinAxioms_of_secondDiagonal hΔΔ
      ⟨T, fun U k _ hU hft => (hT U k hU hft).2⟩ hstack hlimit hRS htangent hInf happrox hopenΔ
      hG)
    ⟨T, fun U k _ hU hft => (hT U k hU hft).1⟩ hstack hlimit hRS htangent happrox hopen hG

end Statement

end AlgebraicGeometry.Stack

end
