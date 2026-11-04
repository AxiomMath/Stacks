module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicAffineOpenSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.RationalFunctionsAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart

/-!
# The meromorphic function of a rational function, read on an affine étale chart

Let `X` be an algebraic space over a scheme `S` satisfying the three hypotheses of Stacks 0ENA,
let `P` be a presentation of its schematic locus at the codimension-zero points and let `U` be
an affine, reduced, locally Noetherian étale chart of `X`, with `A = Γ(U, 𝒪_U)`.

A rational function `f` on `X` has two images in the total ring of fractions `Q(A)`:

* its meromorphic function `R(X) → Γ(X, 𝒦_X)` of Stacks 0ENA, evaluated at the chart `U`, where
  `𝒦_X(U) = Q(A)` by Stacks 0EN6, part (2); and
* its pullback along `Spec Q(A) → U → X`, which is defined because that morphism factors
  through every dense open subspace of `X`
  (`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing`, the first half of Stacks
  0ENK).

**The two agree**: both are one and the same fraction `p / q` of regular functions on `U`.

## Main results

* `AlgebraicGeometry.ΓSpecIso_hom_fromSpecTotalFractionRing_appTop`: pulling a global function
  back along `Spec Q(Γ(T, 𝒪_T)) ⟶ T` is the structure map of the total ring of fractions.
* `AlgebraicGeometry.Space.appTop_chartCoord`: the coordinate of a representative at a chart,
  pulled back along an arbitrary morphism of the site into that chart, is the coordinate at the
  composite factorization.
* `AlgebraicGeometry.Space.exists_eq_mk'_rationalFunctionsToTotalFractionRing`: **the two images
  of a rational function in `Q(A)` are the same fraction of regular functions on `U`.**

## References

* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0ENA](https://stacks.math.columbia.edu/tag/0ENA)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

/-- The global functions on an affine scheme map to the global functions on the spectrum of
their total ring of fractions by the structure map of that total ring of fractions. -/
theorem ΓSpecIso_hom_fromSpecTotalFractionRing_appTop (T : Scheme.{u}) [IsAffine T]
    (a : Γ(T, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(T, ⊤)))).hom
        (T.fromSpecTotalFractionRing.appTop a) =
      algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)) a := by
  have hinv : (T.isoSpec.inv).appTop = (Scheme.ΓSpecIso Γ(T, ⊤)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(T, ⊤)).hom, Iso.hom_inv_id,
      ← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ,
      Scheme.Hom.id_appTop]
  rw [Scheme.fromSpecTotalFractionRing, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hinv,
    ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
  exact congrArg (fun y : Γ(T, ⊤) ↦ algebraMap Γ(T, ⊤) (FractionRing Γ(T, ⊤)) y)
    ((Scheme.ΓSpecIso Γ(T, ⊤)).inv_hom_id_apply a)

namespace Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **The coordinate of a representative, pulled back along an arbitrary morphism of the site
into the chart**, is the coordinate at the composite factorization; the source of the morphism
need not be an étale chart of `X`. -/
theorem appTop_chartCoord {W : Subfunctor X.1}
    (ν : W.toFunctor ⟶ affineLineFunctor B S hS) {U : SmallEtale B S hS X.1}
    (τ : yoneda.obj U.obj.left ⟶ W.toFunctor) {T : BigFppfOver B S hS} (k : T ⟶ U.obj.left) :
    ((BigFppfOver.toScheme B S hS).map k).appTop (chartCoord ν U τ) =
      affineLineCoordinate B S hS (op T) (ν.app (op T) (yonedaEquiv (yoneda.map k ≫ τ))) := by
  rw [chartCoord, ← yonedaEquiv_naturality, NatTrans.naturality_apply, affineLineCoordinate_map]
  rfl

/-- A morphism of representable presheaves is the image under `yoneda` of the morphism of the
site it corresponds to. -/
theorem map_yonedaEquiv_eq {A A' : BigFppfOver B S hS} (h : yoneda.obj A ⟶ yoneda.obj A') :
    yoneda.map (yonedaEquiv h) = h :=
  yonedaEquiv.injective (yonedaEquiv_yoneda_map (yonedaEquiv h))

/-- **The pullback of a rational function to `Spec Q(A)`, from a relation between regular
functions over `U ×_X C`.** Let `C` be an étale chart whose structure morphism is an open
immersion with dense point set — a generic chart of
`AlgebraicGeometry.Space.GenericChartIn`, for instance — through which a representative `g` of a
rational function factors, and let `p` and `q` be regular functions on `U` whose relation with
the coordinate of `g` over `U ×_X C` is the asserted one. Then the pullback of the rational
function along `Spec Q(A) → U → X` satisfies the same relation with the images of `p` and `q`. -/
private theorem mul_algebraMap_eq_of_chartCoord_mul_eq
    (U : SmallEtale B S hS X.1) [IsAffine U.obj.left.left.1] [IsReduced U.obj.left.left.1]
    [IsLocallyNoetherian U.obj.left.left.1]
    (g : PartialMap B S hS X.2 (affineLineFunctor B S hS))
    (C : SmallEtale B S hS X.1) (hCopen : IsOpenImmersion B S hS C.1.hom)
    (hCdense : DenseRange (pointsMap B S hS (yoneda.obj C.obj.left) C.1.hom))
    (hCmono : Mono C.1.hom)
    (τ₀ : yoneda.obj C.obj.left ⟶ g.domain.toFunctor) (hτ₀ : τ₀ ≫ g.domain.ι = C.1.hom)
    (p q : Γ(U.obj.left.left.1, ⊤))
    (hrest : chartCoord g.hom (SmallEtale.prodObj B S hS X.1 U C)
            (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀) *
          ((structurePresheaf B S hS X.1).map
            (SmallEtale.prodFst B S hS X.1 U C).op).hom q =
        ((structurePresheaf B S hS X.1).map (SmallEtale.prodFst B S hS X.1 U C).op).hom p) :
    rationalFunctionsToTotalFractionRing B S hS X.2 U.obj.left U.1.hom
            ((isEtale_iff_presheaf_of_yoneda B S hS U.1.hom).2 U.property)
            (PartialMap.toRationalMap B S hS g) *
          algebraMap Γ(U.obj.left.left.1, ⊤) (FractionRing Γ(U.obj.left.left.1, ⊤)) q =
      algebraMap Γ(U.obj.left.left.1, ⊤) (FractionRing Γ(U.obj.left.left.1, ⊤)) p := by
  have := hCmono
  have hτ : (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀) ≫ g.domain.ι =
      (SmallEtale.prodObj B S hS X.1 U C).1.hom := by
    rw [Category.assoc, hτ₀]
    exact (CodimensionZeroPresentation.prodObj_hom U C).symm
  have hZdense : Dense (Set.range (pointsMap B S hS (Subfunctor.range C.1.hom).toFunctor
      (Subfunctor.range C.1.hom).ι)) := by
    have h := range_pointsMap_ι_chartRange C hCopen
    rw [chartRange_eq_range] at h
    rw [h]
    exact hCdense
  have hZ : IsDenseOpenSubspace B S hS X.2 (Subfunctor.range C.1.hom) :=
    ⟨isOpenSubspace_chartRange C hCopen, hZdense⟩
  have hι : inv (Subfunctor.toRange C.1.hom) ≫ C.1.hom = (Subfunctor.range C.1.hom).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι C.1.hom).symm
  obtain ⟨j, hj⟩ := factorsThroughDenseOpens_totalFractionObject B S hS X.2 U.obj.left U.1.hom
    ((isEtale_iff_presheaf_of_yoneda B S hS U.1.hom).2 U.property) _ hZ
  have hkCmap : yoneda.map (yonedaEquiv (j ≫ inv (Subfunctor.toRange C.1.hom))) =
      j ≫ inv (Subfunctor.toRange C.1.hom) := map_yonedaEquiv_eq _
  have hcond : yoneda.map (totalFractionObjectMap B S hS U.obj.left) ≫ U.1.hom =
      yoneda.map (yonedaEquiv (j ≫ inv (Subfunctor.toRange C.1.hom))) ≫ C.1.hom := by
    rw [hkCmap, Category.assoc, hι]
    exact hj.symm
  obtain ⟨k, hkfst, hksnd⟩ : ∃ k : totalFractionObject B S hS U.obj.left ⟶
      (SmallEtale.prodObj B S hS X.1 U C).obj.left,
      k ≫ (SmallEtale.prodFst B S hS X.1 U C).hom.left =
          totalFractionObjectMap B S hS U.obj.left ∧
        k ≫ (SmallEtale.prodSnd B S hS X.1 U C).hom.left =
          yonedaEquiv (j ≫ inv (Subfunctor.toRange C.1.hom)) :=
    ⟨U.property.rep.lift' _ _ hcond, U.property.rep.lift'_fst _ _ _,
      U.property.rep.lift'_snd _ _ _⟩
  have hpull : ∀ x : Γ(U.obj.left.left.1, ⊤),
      ((BigFppfOver.toScheme B S hS).map k).appTop
          (((structurePresheaf B S hS X.1).map
            (SmallEtale.prodFst B S hS X.1 U C).op).hom x) =
        ((BigFppfOver.toScheme B S hS).map
          (totalFractionObjectMap B S hS U.obj.left)).appTop x := fun x => by
    have hcomp : ((BigFppfOver.toScheme B S hS).map
            (SmallEtale.prodFst B S hS X.1 U C).hom.left).appTop ≫
          ((BigFppfOver.toScheme B S hS).map k).appTop =
        ((BigFppfOver.toScheme B S hS).map
          (totalFractionObjectMap B S hS U.obj.left)).appTop := by
      rw [← Scheme.Hom.comp_appTop, ← Functor.map_comp, hkfst]
    exact ConcreteCategory.congr_hom hcomp x
  have hfacj : (yoneda.map k ≫
        (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀)) ≫ g.domain.ι =
      yoneda.map (totalFractionObjectMap B S hS U.obj.left) ≫ U.1.hom := by
    rw [Category.assoc, hτ, CodimensionZeroPresentation.prodObj_hom U C,
      ← Functor.map_comp_assoc, hksnd, ← hcond]
  have hcoord1 : ((BigFppfOver.toScheme B S hS).map k).appTop
        (chartCoord g.hom (SmallEtale.prodObj B S hS X.1 U C)
          (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀)) =
      affineLineCoordinate B S hS (op (totalFractionObject B S hS U.obj.left))
        (yonedaEquiv ((yoneda.map k ≫
          (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀)) ≫ g.hom)) := by
    rw [appTop_chartCoord g.hom _ _, yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_comp]
  have hcoord : ((BigFppfOver.toScheme B S hS).map k).appTop
        (chartCoord g.hom (SmallEtale.prodObj B S hS X.1 U C)
          (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀)) =
      evalSiteRingHom B S hS X.2
        (factorsThroughDenseOpens_totalFractionObject B S hS X.2 U.obj.left U.1.hom
          ((isEtale_iff_presheaf_of_yoneda B S hS U.1.hom).2 U.property))
        (PartialMap.toRationalMap B S hS g) :=
    hcoord1.trans (evalSiteRingHom_eq B S hS X.2 _ g _ hfacj).symm
  have hA : ∀ x : Γ(U.obj.left.left.1, ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.obj.left.left.1, ⊤)))).hom
          (((BigFppfOver.toScheme B S hS).map k).appTop
            (((structurePresheaf B S hS X.1).map
              (SmallEtale.prodFst B S hS X.1 U C).op).hom x)) =
        algebraMap Γ(U.obj.left.left.1, ⊤) (FractionRing Γ(U.obj.left.left.1, ⊤)) x :=
    fun x => (congrArg (Scheme.ΓSpecIso
        (CommRingCat.of (FractionRing Γ(U.obj.left.left.1, ⊤)))).hom (hpull x)).trans
      (ΓSpecIso_hom_fromSpecTotalFractionRing_appTop U.obj.left.left.1 x)
  have hlhs : rationalFunctionsToTotalFractionRing B S hS X.2 U.obj.left U.1.hom
        ((isEtale_iff_presheaf_of_yoneda B S hS U.1.hom).2 U.property)
        (PartialMap.toRationalMap B S hS g) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Γ(U.obj.left.left.1, ⊤)))).hom
        (((BigFppfOver.toScheme B S hS).map k).appTop
          (chartCoord g.hom (SmallEtale.prodObj B S hS X.1 U C)
            (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀))) :=
    congrArg (Scheme.ΓSpecIso
      (CommRingCat.of (FractionRing Γ(U.obj.left.left.1, ⊤)))).hom hcoord.symm
  refine (congrArg (fun z ↦ z *
    algebraMap Γ(U.obj.left.left.1, ⊤) (FractionRing Γ(U.obj.left.left.1, ⊤)) q) hlhs).trans ?_
  exact (((congrArg (fun z ↦ (Scheme.ΓSpecIso
              (CommRingCat.of (FractionRing Γ(U.obj.left.left.1, ⊤)))).hom
              (((BigFppfOver.toScheme B S hS).map k).appTop
                (chartCoord g.hom (SmallEtale.prodObj B S hS X.1 U C)
                  (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀))) * z)
            (hA q).symm).trans
          (map_mul (Scheme.ΓSpecIso
            (CommRingCat.of (FractionRing Γ(U.obj.left.left.1, ⊤)))).hom.hom _ _).symm).trans
        ((congrArg (fun y ↦ (Scheme.ΓSpecIso
            (CommRingCat.of (FractionRing Γ(U.obj.left.left.1, ⊤)))).hom y)
          (map_mul ((BigFppfOver.toScheme B S hS).map k).appTop.hom _ _).symm).trans
          ((congrArg (fun y ↦ (Scheme.ΓSpecIso
              (CommRingCat.of (FractionRing Γ(U.obj.left.left.1, ⊤)))).hom
              (((BigFppfOver.toScheme B S hS).map k).appTop y)) hrest).trans (hA p))))

variable (P : CodimensionZeroPresentation B S hS X.1)
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)

include P hwa hfin in
/-- **The meromorphic function of a rational function and its pullback to `Spec Q(A)` are the
same fraction of regular functions on the chart.**  For an affine, reduced, locally Noetherian
étale chart `U` of `X` with `A = Γ(U, 𝒪_U)` and a rational function `f` on `X` there are a
regular function `p` on `U` and a nonzerodivisor `q` of `A` with

* `m · q = p` in `𝒦_X(U)`, for `m` the value at `U` of the meromorphic function of `f`, and
* `f = p / q` in `Q(A)`, for the pullback of `f` along `Spec Q(A) → U → X`. -/
theorem exists_eq_mk'_rationalFunctionsToTotalFractionRing
    (U : SmallEtale B S hS X.1) [IsAffine U.obj.left.left.1] [IsReduced U.obj.left.left.1]
    [IsLocallyNoetherian U.obj.left.left.1]
    (f : rationalFunctions B S hS X.2) :
    ∃ (p : Γ(U.obj.left.left.1, ⊤)) (q : (Γ(U.obj.left.left.1, ⊤))⁰),
      (rationalToMeromorphic P hwa hfin f).val (op U) *
            chartToMeromorphic U (q : Γ(U.obj.left.left.1, ⊤)) =
          chartToMeromorphic U p ∧
        rationalFunctionsToTotalFractionRing B S hS X.2 U.obj.left U.1.hom
            ((isEtale_iff_presheaf_of_yoneda B S hS U.1.hom).2 U.property) f =
          IsLocalization.mk' (FractionRing Γ(U.obj.left.left.1, ⊤)) p q := by
  let : Algebra ((structurePresheaf B S hS X.1).obj (op U))
      ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.obj (op U)) :=
    ((toMeromorphicFunctionSheaf B S hS X.1 X.2).hom.app (op U)).hom.toAlgebra
  have := isFractionRing_meromorphicFunctionSheaf_obj B S hS X hwa hfin U
    (inferInstanceAs (IsAffine U.obj.left.left.1))
  obtain ⟨g, hg⟩ := RationalMap.exists_rep B S hS f
  obtain ⟨C, hCgen, hCopen, hCdense, τ₀, hτ₀⟩ :=
    exists_isGenericChart_factoring P hfin g.dense_open_domain
  obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj
    (((structurePresheaf B S hS X.1).obj (op U)))⁰
    ((rationalToMeromorphic P hwa hfin f).val (op U))
  refine ⟨p, q, hpq, ?_⟩
  have hvalU' : (rationalToMeromorphic P hwa hfin f).val
        (op (SmallEtale.prodObj B S hS X.1 U C)) =
      chartToMeromorphic (SmallEtale.prodObj B S hS X.1 U C)
        (chartCoord g.hom (SmallEtale.prodObj B S hS X.1 U C)
          (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀)) := by
    rw [← hg]
    refine rationalToMeromorphic_val P hwa hfin g (SmallEtale.prodObj B S hS X.1 U C) _ ?_
    rw [Category.assoc, hτ₀]
    exact (CodimensionZeroPresentation.prodObj_hom U C).symm
  have hrest : chartCoord g.hom (SmallEtale.prodObj B S hS X.1 U C)
          (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀) *
        ((structurePresheaf B S hS X.1).map (SmallEtale.prodFst B S hS X.1 U C).op).hom
          (q : (structurePresheaf B S hS X.1).obj (op U)) =
      ((structurePresheaf B S hS X.1).map (SmallEtale.prodFst B S hS X.1 U C).op).hom p := by
    have key : chartToMeromorphic (SmallEtale.prodObj B S hS X.1 U C)
          (chartCoord g.hom (SmallEtale.prodObj B S hS X.1 U C)
              (yoneda.map (SmallEtale.prodSnd B S hS X.1 U C).hom.left ≫ τ₀) *
            ((structurePresheaf B S hS X.1).map (SmallEtale.prodFst B S hS X.1 U C).op).hom
              (q : (structurePresheaf B S hS X.1).obj (op U))) =
        chartToMeromorphic (SmallEtale.prodObj B S hS X.1 U C)
          (((structurePresheaf B S hS X.1).map
            (SmallEtale.prodFst B S hS X.1 U C).op).hom p) := by
      rw [map_mul (chartToMeromorphic (SmallEtale.prodObj B S hS X.1 U C)),
        chartToMeromorphic_naturality, chartToMeromorphic_naturality, ← hvalU',
        ← meromorphicFunction_val_naturality (rationalToMeromorphic P hwa hfin f)
          (SmallEtale.prodFst B S hS X.1 U C),
        ← map_mul ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
          (SmallEtale.prodFst B S hS X.1 U C).op).hom]
      exact congrArg ((meromorphicFunctionSheaf B S hS X.1 X.2).obj.map
        (SmallEtale.prodFst B S hS X.1 U C).op).hom hpq
    exact injective_toMeromorphicFunctionSheaf_app B S hS X hwa hfin
      (SmallEtale.prodObj B S hS X.1 U C) key
  refine (IsLocalization.eq_mk'_iff_mul_eq (M := (Γ(U.obj.left.left.1, ⊤))⁰)).mpr ?_
  rw [← hg]
  exact mul_algebraMap_eq_of_chartCoord_mul_eq U g C hCopen hCdense hCgen.mono τ₀ hτ₀ p
    (q : (structurePresheaf B S hS X.1).obj (op U)) hrest

end Space

end AlgebraicGeometry

end
