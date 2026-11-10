module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorEpi
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.Hartogs
public import StacksFrontier.Homology.Injectives.Sheaf.DiagramChasing
import StacksCore.Tactic.StacksAttribute

/-!
# The exactness in the middle of the fundamental exact sequence of Stacks 03RI

Let `X` be a smooth curve over a field `k`, with generic point `η`, function field `K` and
inclusion `j : Spec K ⟶ X`. The fundamental exact sequence of Stacks 03RI is
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`.
This file proves that the sequence is exact in the middle, and hence short exact.

## Main results

* `Stacks.EtaleCohomology.exists_units_appTop_eq_of_forall_genericFibreOrd_eq_zero`: a section of
  `j_* 𝐆_{m,η}` over an integral étale `X`-scheme whose order of vanishing is zero at every
  codimension-one point is the restriction of an invertible global function.
* `Stacks.EtaleCohomology.imageSieve_multiplicativeDirectImageComparison_mem_of_isCurve`: a
  section of `j_* 𝐆_{m,η}` over an étale `X`-scheme killed by the second map is étale locally the
  restriction of an invertible global function.
* `Stacks.EtaleCohomology.exact_divisorSequenceOfCurve`: the sequence is exact in the middle.
* `Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve`: the sequence is short exact.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the vanishing of the
  higher cohomology of `𝐆_m` on a smooth curve.
* [Stacks Project, Tag 031T](https://stacks.math.columbia.edu/tag/031T): algebraic Hartogs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

attribute [local instance]
  Stacks.EtaleCohomology.isLocallyNoetherian_etale_left
  Stacks.EtaleCohomology.noetherianSpace_affineEtale_left

/-! ### A point of a curve of codimension one is closed -/

/-- A point of codimension one on a curve is a closed point. -/
theorem isClosed_singleton_of_coheight_eq_one {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] {x : X} (hx : coheight x = 1) :
    IsClosed ({x} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  by_contra hzx
  have hsp : x ⤳ z := specializes_iff_mem_closure.mpr hz
  have hlt : z < x := by
    refine lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr hsp, fun hge => ?_⟩
    exact hzx (Set.mem_singleton_iff.mpr
      (hsp.antisymm (Scheme.le_iff_specializes.mp hge)).eq.symm)
  have h2 : (2 : ℕ∞) ≤ coheight z := by
    have h := Order.coheight_add_one_le hlt
    rwa [hx, one_add_one_eq_two] at h
  have hle : (coheight z : WithBot ℕ∞) ≤ 1 :=
    (coheight_le_topologicalKrullDim z).trans_eq
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g))
  have hle' : coheight z ≤ (1 : ℕ∞) := by exact_mod_cast hle
  exact absurd (le_trans h2 hle') (by decide)

/-! ### A point of an étale scheme lies under a point of the fibre -/

/-- Every point of `Z` over `x` is the image of a point of the fibre `Z ×_X Spec κ(x)`. -/
theorem exists_pullback_fst_fromSpecResidueField_eq {X Z : Scheme.{u}} (q : Z ⟶ X) {x : X}
    {z : Z} (hz : q.base z = x) :
    ∃ p : ↥(pullback q (X.fromSpecResidueField x)),
      (pullback.fst q (X.fromSpecResidueField x)).base p = z := by
  change z ∈ Set.range _
  rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  exact hz

/-! ### Two injectivity statements -/

namespace closedPointDivisorSheaf

/-- A family of sections of the skyscrapers whose image in `⨁_x (i_x)_* 𝐙` vanishes is the zero
family. -/
theorem eq_zero_of_sheafSectionOfDirectSum_eq_zero (X : Scheme.{u}) (U : X.Etale)
    (f : DirectSum ↥(closedPoints X)
      fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj.obj (op U))
    (hf : sheafSectionOfDirectSum.{u, v} X U f = 0) (x : closedPoints X) :
    f x = 0 := by
  let _ : DecidableEq ↥(closedPoints X) := Classical.decEq _
  let π : closedPointDivisorSheaf.{u, v} X ⟶ closedPointSkyscraper.{u, v} X x :=
    Sigma.π (closedPointSkyscraper.{u, v} X) x
  have hself : ι.{u, v} X x ≫ π = 𝟙 (closedPointSkyscraper.{u, v} X x) :=
    Sigma.ι_π_eq_id (closedPointSkyscraper.{u, v} X) x
  have hne : ∀ y : closedPoints X, y ≠ x → ι.{u, v} X y ≫ π = 0 := fun _ hy =>
    Sigma.ι_π_of_ne (closedPointSkyscraper.{u, v} X) hy
  have happ : ∀ (y : closedPoints X)
      (b : ToType ((closedPointSkyscraper.{u, v} X y).obj.obj (op U))),
      (π.hom.app (op U)).hom (((ι.{u, v} X y).hom.app (op U)).hom b) =
        ((ι.{u, v} X y ≫ π).hom.app (op U)).hom b := fun _ _ => rfl
  have key : ∀ h : DirectSum ↥(closedPoints X)
      fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj.obj (op U),
      (π.hom.app (op U)).hom (sheafSectionOfDirectSum.{u, v} X U h) = h x := by
    intro h
    induction h using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero, DFinsupp.zero_apply]
    | of y b =>
      have hs : sheafSectionOfDirectSum.{u, v} X U (DirectSum.of _ y b) =
          ((ι.{u, v} X y).hom.app (op U)).hom b := by
        rw [sheafSectionOfDirectSum, DirectSum.toAddMonoid_of]
      rw [hs, happ y b]
      by_cases hy : y = x
      · subst hy
        rw [hself, DirectSum.of_eq_same]
        simp
      · rw [hne y hy, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hy)]
        simp
    | add p q hp hq =>
      rw [map_add, map_add, hp, hq]
      exact (DFinsupp.add_apply p q x).symm
  rw [← key f, hf, map_zero]

end closedPointDivisorSheaf

/-- The `x`-component of the second map of Stacks 03RI vanishes only if every order of vanishing
on the fibre over `x` does. -/
theorem forall_etaleGenericFibreOrdOfPoint_eq_zero_of_eq_zero {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsNormal X] (U : X.Etale) [IsLocallyNoetherian U.left]
    (x : X) (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ))
    (h : integerSkyscraperDivisorOfPoint.{u, v} U x a = 0)
    (p : ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left) :
    etaleGenericFibreOrdOfPoint U
      ((pullback.fst U.hom (X.fromSpecResidueField x)) p) a = 0 := by
  have hinj : Function.Injective
      (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).inv.hom :=
    (ConcreteCategory.bijective_of_isIso
      (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).inv).1
  have hzero : residueFibreOrdOfPoint.{u, v} U x a = 0 := by
    refine hinj ?_
    rw [map_zero]
    exact (AddMonoidHom.comp_apply _ _ a).symm.trans h
  exact ULift.up_injective ((residueFibreOrdOfPoint_apply.{u, v} U x a p).symm.trans
    (congrFun (congrArg LocallyConstant.toFun hzero) p))

/-! ### The commutative algebra of the middle exactness -/

/-- **A section of `j_* 𝐆_{m,η}` over an integral étale `X`-scheme whose order of vanishing is
zero at every codimension-one point is the restriction of an invertible global function.** -/
theorem exists_units_appTop_eq_of_forall_genericFibreOrd_eq_zero {X U : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsNormal X] [AlgebraicGeometry.IsIntegral U]
    [IsLocallyNoetherian U] (q : U ⟶ X) [Etale q]
    (a : (Γ(pullback q (genericPointInclusion X), ⊤))ˣ)
    (h : ∀ y : U, coheight y = 1 → genericFibreOrd q y (Additive.ofMul a) = 0) :
    ∃ s : (Γ(U, ⊤))ˣ,
      Units.map (pullback.fst q (genericPointInclusion X)).appTop.hom.toMonoidHom s = a := by
  have : IsNormal U := isNormal_of_etale q
  have hiso := isIso_genericFibreToFunctionField q
  have hord : ∀ y : U, coheight y = 1 →
      Scheme.ord ((Units.map (genericFibreToFunctionField q).hom.toMonoidHom a :
        U.functionFieldˣ) : U.functionField) y = 0 := fun y hy => by
    rw [Units.coe_map]
    exact (genericFibreOrd_apply q y (Additive.ofMul a)).symm.trans (h y hy)
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.exists_globalUnit_of_forall_ord_eq_zero
      (Units.map (genericFibreToFunctionField q).hom.toMonoidHom a) hord
  rw [Units.coe_map] at hs
  refine ⟨s, Units.ext ((ConcreteCategory.bijective_of_isIso (genericFibreToFunctionField q)).1 ?_)⟩
  exact (congrArg (fun φ => (CommRingCat.Hom.hom φ) (s : Γ(U, ⊤)))
    (appTop_genericFibreToFunctionField q)).trans hs

/-- **On an étale scheme over a curve, a section of `j_* 𝐆_{m,η}` killed by the second map of
Stacks 03RI has order of vanishing zero at every codimension-one point.** -/
private theorem etaleGenericFibreOrdOfPoint_eq_zero_of_closedPointDivisorSheafSection_eq_zero
    {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [IsNormal X]
    (V : X.Etale) [IsLocallyNoetherian V.left] [NoetherianSpace V.left]
    (b : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ)
    (h : closedPointDivisorSheafSection.{u, v} V (Additive.ofMul b) = 0) (y : V.left)
    (hy : coheight y = 1) : etaleGenericFibreOrdOfPoint V y (Additive.ofMul b) = 0 := by
  have : Etale V.hom := V.prop
  have hcl : IsClosed ({V.hom.base y} : Set X) :=
    isClosed_singleton_of_coheight_eq_one g ((coheight_eq_of_etale V.hom y).trans hy)
  obtain ⟨p, hp⟩ := exists_pullback_fst_fromSpecResidueField_eq (X := X) V.hom (z := y) rfl
  have hcomp : closedPointDivisorSections.{u, v} V (Additive.ofMul b) ⟨V.hom.base y, hcl⟩ = 0 :=
    closedPointDivisorSheaf.eq_zero_of_sheafSectionOfDirectSum_eq_zero.{u, v} X V _
      ((closedPointDivisorSheafSection_apply.{u, v} V (Additive.ofMul b)).symm.trans h) _
  have hcomp' : integerSkyscraperDivisorOfPoint.{u, v} V (V.hom.base y) (Additive.ofMul b) = 0 :=
    (closedPointDivisorSections_apply.{u, v} V (Additive.ofMul b) ⟨_, hcl⟩).symm.trans hcomp
  have := forall_etaleGenericFibreOrdOfPoint_eq_zero_of_eq_zero.{u, v} V _ (Additive.ofMul b)
    hcomp' p
  rwa [hp] at this

/-! ### The middle exactness on sections over an arbitrary étale `X`-scheme -/

/-- **A section of `j_* 𝐆_{m,η}` over an étale scheme over a smooth curve that is killed by the
second map of Stacks 03RI is étale locally the restriction of an invertible global function.** -/
theorem imageSieve_multiplicativeDirectImageComparison_mem_of_isCurve {k : Type u} [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] (U : X.Etale)
    (a : ToType (((genericPointDirectImage.{u, v} X).obj
      (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj (op U)))
    (hd : (divisorSequenceSecondMapOfCurve.{u, v} g).hom.app (op U) a = 0) :
    Presheaf.imageSieve
        (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom a ∈
      X.smallEtaleTopology U := by
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : Etale U.hom := U.prop
  have key : ∀ w : U.left, ∃ (W : X.AffineEtale)
      (ψ : (Scheme.AffineEtale.Spec X).obj W ⟶ U),
      Presheaf.imageSieve
          (multiplicativeDirectImageComparison.{u, v} (genericPointInclusion X)).hom a ψ ∧
        w ∈ Set.range ψ.left.base := by
    intro w
    obtain ⟨W, φ, hint, -, hw, -⟩ :=
      exists_affineEtale_isIntegral U (⊤ : U.left.Opens) (show w ∈ (⊤ : U.left.Opens) from trivial)
    have := hint
    have hEt : Etale ((Scheme.AffineEtale.Spec X).obj W).hom :=
      ((Scheme.AffineEtale.Spec X).obj W).prop
    obtain ⟨b, hb⟩ := Stacks.Kummer.ofUnit_surjective.{u, v}
      (X := Spec X.functionField)
      (U := (smallEtaleBaseChange (genericPointInclusion X)).obj
        ((Scheme.AffineEtale.Spec X).obj W))
      (((genericPointDirectImage.{u, v} X).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.map φ.op a)
    have hdW : (divisorSequenceSecondMapOfCurve.{u, v} g).hom.app
        (op ((Scheme.AffineEtale.Spec X).obj W))
        (Stacks.Kummer.ofUnit.{u, v} b) = 0 := by
      rw [hb, NatTrans.naturality_apply
        (divisorSequenceSecondMapOfCurve.{u, v} g).hom φ.op a, hd, map_zero]
    have hsec : closedPointDivisorSheafSection.{u, v}
        ((Scheme.AffineEtale.Spec X).obj W) (Additive.ofMul b) = 0 := by
      refine Eq.trans ?_ hdW
      refine Eq.symm (Eq.trans (congrArg
        (fun ψ : ((genericPointDirectImage.{u, v} X).obj
            (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj
              (op ((Scheme.AffineEtale.Spec X).obj W)) ⟶
            (closedPointDivisorSheaf.{u, v} X).obj.obj
              (op ((Scheme.AffineEtale.Spec X).obj W)) => ψ.hom (ULift.up (Additive.ofMul b)))
        (divisorSequenceSecondMap_hom_app.{u, v} X W))
        (affineEtaleDivisorApp_apply.{u, v} X W (ULift.up (Additive.ofMul b))))
    have hord0 := etaleGenericFibreOrdOfPoint_eq_zero_of_closedPointDivisorSheafSection_eq_zero
      g ((Scheme.AffineEtale.Spec X).obj W) b hsec
    have hI : AlgebraicGeometry.IsIntegral
        ((𝟭 Scheme).obj ((Scheme.AffineEtale.Spec X).obj W).left) :=
      inferInstanceAs (AlgebraicGeometry.IsIntegral ((Scheme.AffineEtale.Spec X).obj W).left)
    have hN : IsLocallyNoetherian
        ((𝟭 Scheme).obj ((Scheme.AffineEtale.Spec X).obj W).left) :=
      inferInstanceAs (IsLocallyNoetherian ((Scheme.AffineEtale.Spec X).obj W).left)
    obtain ⟨s, hs⟩ := exists_units_appTop_eq_of_forall_genericFibreOrd_eq_zero
      (X := X) ((Scheme.AffineEtale.Spec X).obj W).hom b
      (fun y hy => (etaleGenericFibreOrdOfPoint_eq_etaleGenericFibreOrd
        ((Scheme.AffineEtale.Spec X).obj W) y (Additive.ofMul b)).symm.trans (hord0 y hy))
    refine ⟨W, φ, ⟨Stacks.Kummer.ofUnit.{u, v} s, ?_⟩, hw⟩
    rw [multiplicativeDirectImageComparison_app_ofUnit, hs, ← hb]
  choose W ψ hS hmem using key
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff ψ).mpr ?_)
  · intro T f hf
    obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff
      (fun i : U.left => (Scheme.AffineEtale.Spec X).obj (W i)) ψ f).mp hf
    exact Sieve.downward_closed _ (hS i) c
  · exact Set.iUnion_eq_univ_iff.mpr fun y => ⟨y, hmem y⟩

/-! ### The exactness in the middle, and Stacks 03RI -/

/-- For a smooth curve `X` over a field, the fundamental exact sequence
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0` is exact in the middle: the kernel of
the divisor map `j_* 𝐆_{m,η} ⟶ ⨁_{x ∈ X_0} (i_x)_* 𝐙` is the image of `𝐆_{m,X}`. -/
@[stacks 03RI "the exactness in the middle of the sequence for a smooth curve over a field: a
section of j_* G_m killed by the divisor map is étale locally an invertible global function"]
theorem exact_divisorSequenceOfCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] :
    (ShortComplex.mk
      (multiplicativeDirectImageComparison.{u, u + 1} (genericPointInclusion X))
      (divisorSequenceSecondMapOfCurve.{u, u + 1} g)
      (multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve.{u, u + 1}
        g)).Exact :=
  Stacks.Injectives.exact_of_forall_exists_local_lift X.smallEtaleTopology fun V av hav =>
    ⟨_, imageSieve_multiplicativeDirectImageComparison_mem_of_isCurve.{u, u + 1} g V av hav,
      fun _ _ hφ => hφ⟩

/-- Let `X` be a smooth curve over a field `k`, let `η` be its generic point with inclusion
`j : η ⟶ X`, and let `X_0` be its set of closed points with inclusions `i_x`. Then

`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`

is a short exact sequence of étale sheaves on `X`. -/
@[stacks 03RI "the fundamental exact sequence for a smooth curve over a field, as a short exact
sequence of étale sheaves"]
theorem shortExact_divisorSequenceOfCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] :
    (ShortComplex.mk
      (multiplicativeDirectImageComparison.{u, u + 1} (genericPointInclusion X))
      (divisorSequenceSecondMapOfCurve.{u, u + 1} g)
      (multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve.{u, u + 1}
        g)).ShortExact :=
  ShortComplex.ShortExact.mk' (exact_divisorSequenceOfCurve.{u} g)
    (mono_multiplicativeDirectImageComparison_genericPointInclusion.{u, u + 1} X)
    (epi_divisorSequenceSecondMapOfCurve.{u, u + 1} g)

end Stacks.EtaleCohomology

end
