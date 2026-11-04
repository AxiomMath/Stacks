module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductProjections
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# The exterior product on Chow groups

Let `k` be a field and let `X` and `Y` be schemes locally of finite type over `k`. For integral
closed subschemes `X' ⊆ X` of dimension `n` and `Y' ⊆ Y` of dimension `m` the product
`X' ×_k Y'` is a closed subscheme of `X ×_k Y` of dimension `n + m`, and the rule

  `[X'] × [Y'] = [X' ×_k Y']_{n+m}`

extends `ℤ`-bilinearly to the exterior product of cycles
`Z_n(X) ⟶ Z_m(Y) ⟶ Z_{n+m}(X ×_k Y)`, which is `Stacks.Chow.exteriorProduct`. This file proves
that the exterior product is well defined modulo rational equivalence in each variable, and
assembles the descended map

  `× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m}(X ×_k Y)`.

## Main definitions

* `Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres`: flat pullback
  along the projections `v_x : closure {x} ×_k Y ⟶ Y` carries cycles rationally equivalent to zero
  to cycles rationally equivalent to zero.
* `Stacks.Chow.chowExteriorProduct`: the exterior product on Chow groups,
  `CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m}(X ×_k Y)`.

## Main results

* `Stacks.Chow.exteriorProduct_mem_rationalEquivalences_right`,
  `Stacks.Chow.exteriorProduct_mem_rationalEquivalences_left`: the exterior product of cycles
  carries a cycle rationally equivalent to zero, in either variable, to a cycle rationally
  equivalent to zero.
* `Stacks.Chow.chowExteriorProduct_tmul_mk`: on a pure tensor of cycle classes the descended map
  is the class of the exterior product of the two cycles.
* `Stacks.Chow.relativeDimension_pointClosureFibreSnd`: the projection `closure {x} ×_k Y ⟶ Y`
  has relative dimension the dimension of `closure {x}`.
* `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_forall`: the
  predicate above follows from the same property of flat pullback along every flat morphism to
  `Y`.
* `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds`: the
  predicate above holds.

## References

* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBU](https://stacks.math.columbia.edu/tag/0FBU)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Notation for the product of a point closure with the second factor -/

/-- The ideal sheaf on `X ×_S Y` cutting out `closure {x} ×_S Y`, the inverse image of the reduced
closure of `x : X` under the first projection. -/
private abbrev pointClosureFibre {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) :
    (pullback f g : Scheme.{u}).IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)

/-! ### Coefficients of a closed subscheme of a closed subscheme -/

/-- If an ideal sheaf `I` on `Q` contains the kernel of a closed immersion `j : W ⟶ Q`, then the
second projection of the fibre product of `j` with the closed immersion of the subscheme of `I` is
an isomorphism. -/
private theorem isIso_pullback_snd_subschemeι_of_ker_le {Q W : Scheme.{u}}
    (I : Q.IdealSheafData) (j : W ⟶ Q) [IsClosedImmersion j] (hI : j.ker ≤ I) :
    IsIso (pullback.snd j I.subschemeι) := by
  have hker : j.ker ≤ I.subschemeι.ker := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  have hl : IsClosedImmersion.lift j I.subschemeι hker ≫ j = I.subschemeι :=
    IsClosedImmersion.lift_fac j I.subschemeι hker
  refine ⟨pullback.lift (IsClosedImmersion.lift j I.subschemeι hker) (𝟙 I.subscheme)
    (by simp [hl]), ?_, ?_⟩
  · refine pullback.hom_ext ?_ (by simp)
    refine (cancel_mono j).1 ?_
    simp [hl, ← pullback.condition]
  · simp

/-- The closed subscheme cut out by an ideal sheaf `I` containing the kernel of a closed immersion
`j : W ⟶ Q` is also cut out, inside `W`, by the inverse image `I.comap j`. -/
private def comapSubschemeIsoOfKerLE {Q W : Scheme.{u}} (I : Q.IdealSheafData) (j : W ⟶ Q)
    [IsClosedImmersion j] (hI : j.ker ≤ I) : (I.comap j).subscheme ≅ I.subscheme :=
  haveI := isIso_pullback_snd_subschemeι_of_ker_le I j hI
  (I.comapIso j).trans (asIso (pullback.snd j I.subschemeι))

private theorem comapSubschemeIsoOfKerLE_hom {Q W : Scheme.{u}} (I : Q.IdealSheafData)
    (j : W ⟶ Q) [IsClosedImmersion j] (hI : j.ker ≤ I) :
    (comapSubschemeIsoOfKerLE I j hI).hom ≫ I.subschemeι = (I.comap j).subschemeι ≫ j := by
  have := isIso_pullback_snd_subschemeι_of_ker_le I j hI
  show ((I.comapIso j).hom ≫ pullback.snd j I.subschemeι) ≫ I.subschemeι = _
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- Generic points of the closed subscheme cut out by an ideal sheaf `I` containing the kernel of
a closed immersion `j : W ⟶ Q` are the generic points of the subscheme cut out inside `W` by the
inverse image `I.comap j`. -/
private theorem exists_genericPoints_comap_of_ker_le {Q W : Scheme.{u}} (I : Q.IdealSheafData)
    (j : W ⟶ Q) [IsClosedImmersion j] (hI : j.ker ≤ I) (ζ : genericPoints I.subscheme) :
    ∃ ζ' : genericPoints (I.comap j).subscheme,
      I.subschemeι.base ζ.1 = j.base ((I.comap j).subschemeι.base ζ'.1) := by
  refine ⟨⟨(comapSubschemeIsoOfKerLE I j hI).inv.base ζ.1,
    (genericPointsIso (comapSubschemeIsoOfKerLE I j hI).symm ζ).2⟩, ?_⟩
  have hhom := congrArg (fun q : (I.comap j).subscheme ⟶ Q ↦
    q ((comapSubschemeIsoOfKerLE I j hI).inv.base ζ.1))
    (comapSubschemeIsoOfKerLE_hom I j hI)
  simp only [Scheme.Hom.comp_apply] at hhom
  have hinv : (comapSubschemeIsoOfKerLE I j hI).hom.base
      ((comapSubschemeIsoOfKerLE I j hI).inv.base ζ.1) = ζ.1 := by
    simp
  rw [← hhom, hinv]

/-- Generic points of the closed subscheme cut out by the inverse image of an ideal sheaf along an
isomorphism are the generic points of the subscheme the ideal sheaf itself cuts out. -/
private theorem exists_genericPoints_comap_of_isIso {A B : Scheme.{u}} (ε : A ≅ B)
    (M : B.IdealSheafData) (ζ : genericPoints (M.comap ε.hom).subscheme) :
    ∃ ξ : genericPoints M.subscheme,
      M.subschemeι.base ξ.1 = ε.hom.base ((M.comap ε.hom).subschemeι.base ζ.1) := by
  refine ⟨⟨(comapSubschemeIsoOfIsIso ε.hom M).hom.base ζ.1,
    (genericPointsIso (comapSubschemeIsoOfIsIso ε.hom M) ζ).2⟩, ?_⟩
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun q : (M.comap ε.hom).subscheme ⟶ B ↦ q ζ.1)
    (comapSubschemeIsoOfIsIso_hom_subschemeι ε.hom M)

/-- The coefficient at a point `j w` of the closed subscheme cut out by an ideal sheaf `I`
containing the kernel of a closed immersion `j : W ⟶ Q` is the coefficient at `w` of the closed
subscheme of `W` cut out by the inverse image `I.comap j`. -/
private theorem closedSubschemeCycleCoeff_comap_of_isClosedImmersion (C : ChowSituation.{u})
    {Q W : Scheme.{u}} (p : Q ⟶ C.S) [LocallyOfFiniteType p] (j : W ⟶ Q) [IsClosedImmersion j]
    (I : Q.IdealSheafData) (hI : j.ker ≤ I) (k : ℤ) (w : W) :
    closedSubschemeCycleCoeff C p I.subschemeι k (j.base w) =
      closedSubschemeCycleCoeff C (j ≫ p) (I.comap j).subschemeι k w := by
  rw [← closedSubschemeCycleCoeff_eq_of_iso C p ((I.comap j).subschemeι ≫ j) I.subschemeι
    (comapSubschemeIsoOfKerLE I j hI) (comapSubschemeIsoOfKerLE_hom I j hI) k (j.base w)]
  exact closedSubschemeCycleCoeff_comp_isClosedImmersion C (j ≫ p) p j rfl
    (I.comap j).subschemeι k w

/-- The coefficient of a closed subscheme is unchanged by an isomorphism of the ambient scheme
over the base. -/
theorem closedSubschemeCycleCoeff_comap_of_isIso (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (ι : A ⟶ B) [IsIso ι] (hι : ι ≫ sB = sA) (I : B.IdealSheafData)
    (J : A.IdealSheafData) (hJ : J = I.comap ι) (k : ℤ) (a : A) :
    closedSubschemeCycleCoeff C sA J.subschemeι k a =
      closedSubschemeCycleCoeff C sB I.subschemeι k (ι.base a) := by
  subst hJ
  rw [closedSubschemeCycleCoeff_of_isIso_ambient C sA sB ι hι (I.comap ι).subschemeι k a]
  exact closedSubschemeCycleCoeff_eq_of_iso C sB ((I.comap ι).subschemeι ≫ ι) I.subschemeι
    (comapSubschemeIsoOfIsIso ι I) (comapSubschemeIsoOfIsIso_hom_subschemeι ι I) k (ι.base a)

/-! ### The product of a point closure with the second factor -/

/-- The inverse image of the reduced closure of `x : X` under the first projection, as a closed
subscheme of `X ×_S Y`, is the fibre product `closure {x} ×_S Y`. -/
def pointClosureFibreIso {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (x : X) :
    (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subscheme) ≅
      pullback ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g :=
  ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comapIso (pullback.fst f g)).trans
    ((pullbackSymmetry (pullback.fst f g) (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι).trans
      (pullbackRightPullbackFstIso f g (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι))

/-- The isomorphism `Stacks.Chow.pointClosureFibreIso` carries the projection to `Y` of the fibre
product to the projection to `Y` of `X ×_S Y`, restricted to the closed subscheme. -/
theorem pointClosureFibreIso_hom_snd {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X) :
    (pointClosureFibreIso f g x).hom ≫ pullback.snd ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g =
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
        pullback.snd f g := by
  simp only [pointClosureFibreIso, Iso.trans_hom, Category.assoc,
    pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- The isomorphism `Stacks.Chow.pointClosureFibreIso` carries the projection to `closure {x}` of
the fibre product, followed by the closed immersion of `closure {x}` into `X`, to the projection
to `X` of `X ×_S Y`, restricted to the closed subscheme. -/
theorem pointClosureFibreIso_hom_fst {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X) :
    (pointClosureFibreIso f g x).hom ≫ pullback.fst ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g ≫
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι =
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
        pullback.fst f g := by
  simp only [pointClosureFibreIso, Iso.trans_hom, Category.assoc,
    pullbackRightPullbackFstIso_hom_fst_assoc, pullbackSymmetry_hom_comp_fst_assoc,
    ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- The square exhibiting `closure {x} ×_S Y` as a fibre product: its projection to `Y` is the
base change along `g` of the structure morphism of the reduced closure of `x`. -/
private theorem isPullback_pointClosureFibre {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X) :
    IsPullback ((pointClosureFibreIso f g x).hom ≫
        pullback.fst ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g)
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
          pullback.snd f g)
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pointClosureFibreIso f g x) rfl
    (pointClosureFibreIso_hom_snd f g x)
  rw [← pointClosureFibreIso_hom_snd f g x, Category.assoc, Category.assoc, pullback.condition]

/-- Over the spectrum of a field, the projection `closure {x} ×_S Y ⟶ Y` of the product of the
reduced closure of a point `x` of `X` with `Y` has relative dimension the relative dimension of
`x` over the base. -/
theorem relativeDimension_pointClosureFibreSnd (C : ChowSituation.{u}) [Subsingleton C.S]
    [JacobsonSpace C.S] (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (k : ℤ) (x : X)
    (hx : relativeDimension C.dimensionFunction f x = k) :
    AlgebraicGeometry.RelativeDimension
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
          pullback.snd f g) k.toNat := by
  have hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hgen : I.subschemeι.base (genericPoint I.subscheme) = x :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x
  have hdim : topologicalKrullDim I.subscheme = ((k.toNat : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_relativeDimension_toNat C hδ f I.subschemeι
      (genericPoint I.subscheme) (genericPoint_spec I.subscheme), hgen, hx]
  have hrel : AlgebraicGeometry.RelativeDimension (I.subschemeι ≫ f) k.toNat := by
    intro s _
    have hpre : (I.subschemeι ≫ f).base ⁻¹' ({s} : Set C.S) = Set.univ := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    let e : (I.subschemeι ≫ f).fiber s ≃ₜ I.subscheme :=
      ((I.subschemeι ≫ f).fiberHomeo s).trans
        ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ I.subscheme))
    have hirr : IrreducibleSpace ((I.subschemeι ≫ f).fiber s) :=
      e.irreducibleSpace_iff.mpr inferInstance
    refine ⟨TopologicalSpace.Equidimensional.of_preirreducibleSpace _, ?_⟩
    rwa [IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  exact AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_pointClosureFibre f g x) hrel

/-- The inverse image under `ι_x : closure {x} ×_S Y ⟶ X ×_S Y` of the ideal sheaf of the product
`closure {x} ×_S closure {y}` is the inverse image of the reduced closure of `y` under the
projection `v_x : closure {x} ×_S Y ⟶ Y`. -/
private theorem comap_exteriorProductIdeal_subschemeι {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (x : X) (y : Y) :
    (exteriorProductIdeal f g x y).comap ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).comap
        (((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
            pullback.snd f g) := by
  set K : (pullback f g : Scheme.{u}).IdealSheafData :=
    (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst f g) with hK
  have hkill : K.comap K.subschemeι = ⊥ := by
    have h := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion K.subschemeι K.subschemeι
    rw [K.ker_subschemeι] at h
    rw [← h, Scheme.Hom.ker_eq_bot_of_isIso]
  rw [exteriorProductIdeal, ← hK, Scheme.IdealSheafData.comap_sup, hkill, bot_sup_eq,
    ← Scheme.IdealSheafData.comap_comp]

/-- The kernel of the closed immersion of `closure {x} ×_S Y` into `X ×_S Y` lies in the ideal sheaf
of the product `closure {x} ×_S closure {y}`. -/
private theorem ker_pointClosureFibre_le_exteriorProductIdeal {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) (x : X) (y : Y) :
    (pointClosureFibre f g x).subschemeι.ker ≤ exteriorProductIdeal f g x y := by
  rw [Scheme.IdealSheafData.ker_subschemeι, exteriorProductIdeal]
  exact le_sup_left

/-- A point of `X ×_S Y` lies in the support of `closure {x} ×_S Y` exactly when its first
projection lies in the closure of `x`. -/
private theorem mem_support_pointClosureFibre_iff {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (x : X) (z : (pullback f g : Scheme.{u})) :
    z ∈ ((pointClosureFibre f g x).support : Set (pullback f g : Scheme.{u})) ↔
      (pullback.fst f g).base z ∈ closure ({x} : Set X) := by
  simp [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- A generic point of the product `closure {x} ×_S closure {y}`, read first inside
`closure {x} ×_S Y` and then inside `X ×_S Y`, projects to `x`. -/
private theorem fst_genericPoint_of_eq_comap {S X Y : Scheme.{u}} [Subsingleton S] [IsIntegral S]
    (f : X ⟶ S) (g : Y ⟶ S) (x : X) (y : Y)
    (L : (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subscheme).IdealSheafData)
    (hL : L = ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap
      (pullback.snd ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g)).comap
          (pointClosureFibreIso f g x).hom)
    (ζ : genericPoints L.subscheme) :
    (pullback.fst f g).base
        (((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set X))).comap
          (pullback.fst f g)).subschemeι.base (L.subschemeι.base ζ.1)) = x := by
  subst hL
  have hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  obtain ⟨ξ, hξ⟩ := exists_genericPoints_comap_of_isIso (pointClosureFibreIso f g x)
    ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).comap
      (pullback.snd ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g)) ζ
  have hfst := congrArg (fun q : ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subscheme ⟶ X ↦
    q ((((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).comap
        (pullback.snd ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g)).comap
            (pointClosureFibreIso f g x).hom).subschemeι.base ζ.1))
    (pointClosureFibreIso_hom_fst f g x)
  simp only [Scheme.Hom.comp_apply] at hfst
  rw [← hfst, ← hξ,
    fst_genericPoint_pointClosurePullback ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g y ξ]
  exact Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure x

/-- The multiplicity of `closure {x} ×_S closure {y}` at a point of `X ×_S Y` whose first
projection is not `x` is zero. -/
theorem exteriorProductWeight_eq_zero_of_ne (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (k : ℤ) (x : X) (y : Y) (z : (pullback f g : Scheme.{u}))
    (hz : (pullback.fst f g).base z ≠ x) :
    exteriorProductWeight C f g k x y z = 0 := by
  classical
  have hc : (exteriorProductIdeal f g x y).comap ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι =
      ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({y} : Set Y))).comap
        (pullback.snd ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set X))).subschemeι ≫ f) g)).comap
            (pointClosureFibreIso f g x).hom := by
    rw [comap_exteriorProductIdeal_subschemeι f g x, ← pointClosureFibreIso_hom_snd f g x,
      Scheme.IdealSheafData.comap_comp]
  unfold exteriorProductWeight closedSubschemeCycleCoeff
  refine dite_eq_right ?_
  rintro ⟨ζ, hζ, -⟩
  refine hz ?_
  obtain ⟨ζ', hζ'⟩ := exists_genericPoints_comap_of_ker_le (exteriorProductIdeal f g x y)
    ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι
    (ker_pointClosureFibre_le_exteriorProductIdeal f g x y) ζ
  rw [← hζ, hζ']
  exact fst_genericPoint_of_eq_comap f g x y _ hc ζ'

/-! ### Flat pullback along the projections of the products with the point closures -/

/-- For every point `x` of `X` and every relative dimension `r` of the flat projection
`v_x : closure {x} ×_S Y ⟶ Y`, flat pullback of `m`-cycles along `v_x` carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero. -/
def FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres (C : ChowSituation.{u})
    [Subsingleton C.S] [IsIntegral C.S] {X Y : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (m : ℤ) : Prop :=
  ∀ (x : X) (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
          pullback.snd f g) r),
    haveI : Flat (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
          pullback.snd f g) := flat_pointClosurePullback_snd f g x
    FlatPullbackFactorsThroughRationalEquivalence C
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
          (pullback.fst f g ≫ f)) g
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).comap (pullback.fst f g)).subschemeι ≫
          pullback.snd f g)
      (by rw [Category.assoc, pullback.condition]) r hr m

/-- `Stacks.Chow.FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres` follows from
the same property of flat pullback along every flat morphism over the base to `Y` of fixed relative
dimension. -/
theorem flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_forall
    (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (m : ℤ)
    (h : ∀ {X' : Scheme.{u}} (sX' : X' ⟶ C.S) (_ : LocallyOfFiniteType sX') (v : X' ⟶ Y)
      (_ : LocallyOfFiniteType v) (_ : Flat v) (hbase : v ≫ g = sX') (r : ℕ)
      (hv : AlgebraicGeometry.RelativeDimension v r),
      FlatPullbackFactorsThroughRationalEquivalence C sX' g v hbase r hv m) :
    FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres C f g m :=
  fun x r hr ↦ h _ inferInstance _ inferInstance (flat_pointClosurePullback_snd f g x) _ r hr

/-- Over the spectrum of a field, flat pullback of `m`-cycles along each projection
`v_x : closure {x} ×_S Y ⟶ Y` carries cycles rationally equivalent to zero to cycles rationally
equivalent to zero. -/
theorem flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds
    (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (m : ℤ) :
    FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres C f g m :=
  flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_of_forall C f g m
    fun sX' hsX' v hv hvflat hbase r hr ↦ by
      have := hsX'
      have := hv
      have := hvflat
      exact flatPullbackFactorsThroughRationalEquivalence_general C sX' g v hbase r hr m

/-! ### Local finiteness of the family of products with the point closures -/

/-- The family of the inverse images, under the first projection of `X ×_S Y`, of the reduced
closures of the points in the support of a cycle on `X` is locally finite. -/
private theorem locallyFinite_comap_pointClosure {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (c : AlgebraicCycle X ℤ) :
    LocallyFinite fun x : c.support ↦
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({(x : X)} : Set X))).comap
          (pullback.fst f g)).support : Set (pullback f g : Scheme.{u})) := by
  classical
  intro z
  obtain ⟨t, ht, hfin⟩ := c.supportLocallyFiniteWithinDomain' ((pullback.fst f g).base z) trivial
  obtain ⟨U, hUt, hU, hzU⟩ := mem_nhds_iff.1 ht
  refine ⟨(pullback.fst f g).base ⁻¹' U,
    ((hU.preimage (pullback.fst f g).continuous).mem_nhds hzU), ?_⟩
  have hpre : ((fun x : c.support ↦ (x : X)) ⁻¹' (t ∩ c.support)).Finite :=
    hfin.preimage (fun a _ b _ hab ↦ Subtype.ext hab)
  have hfinU : {x : c.support | (x : X) ∈ U}.Finite := hpre.subset fun x hx ↦ ⟨hUt hx, x.2⟩
  refine hfinU.subset ?_
  rintro x ⟨w, hw, hwU⟩
  exact (isGenericPoint_closure (x := (x : X))).mem_open_set_iff hU |>.2
    ⟨(pullback.fst f g).base w, (mem_support_pointClosureFibre_iff f g x w).1 hw, hwU⟩

/-! ### The exterior product descends -/

open Classical in
/-- For a point `x` in the support of `α` and a cycle `β` rationally equivalent to zero, there is
an `(n + m)`-cycle on `closure {x} ×_S Y`, rationally equivalent to zero, whose pushforward to
`X ×_S Y` agrees with `α × β` at the points over `x` and vanishes elsewhere. -/
private theorem exists_exteriorProductSummand (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (n m : ℤ) (hn : 0 ≤ n)
    (hfac : FlatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres C f g m)
    (α : CycleGroup C f n) {β : CycleGroup C g m} (hβ : β ∈ rationalEquivalences C g m)
    (x : X) (hx : α.1 x ≠ 0) :
    ∃ a : CycleGroup C ((pointClosureFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m),
      a ∈ rationalEquivalences C
          ((pointClosureFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m) ∧
        ∀ z : (pullback f g : Scheme.{u}),
          (properPushforward C ((pointClosureFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
            (pullback.fst f g ≫ f) (pointClosureFibre f g x).subschemeι rfl (n + m) a).1 z =
            if (pullback.fst f g).base z = x then exteriorProductCoeff C f g n m α β z else 0 := by
  classical
  have : Flat ((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g) :=
    flat_pointClosurePullback_snd f g x
  have hbase : ((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g) ≫ g =
      (pointClosureFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f) := by
    rw [Category.assoc, pullback.condition]
  have hdeg : m + ((n.toNat : ℕ) : ℤ) = n + m := by
    rw [Int.toNat_of_nonneg hn, add_comm]
  have hrel : AlgebraicGeometry.RelativeDimension
      ((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g) n.toNat :=
    relativeDimension_pointClosureFibreSnd C hδ f g n x
      ((mem_cyclesOfDimension_iff_forall_point C f n α.1).1 α.2 x hx)
  refine ⟨hdeg ▸ flatPullback C ((pointClosureFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) g
    ((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g) hbase n.toNat hrel m
    (α.1 x • β), ?_, ?_⟩
  · exact mem_rationalEquivalences_cast C _ hdeg
      (hfac x n.toNat hrel _ ((rationalEquivalences C g m).zsmul_mem hβ (α.1 x)))
  · intro z
    by_cases hz : z ∈ Set.range (pointClosureFibre f g x).subschemeι.base
    · obtain ⟨w, rfl⟩ := hz
      have hpt : (pullback.snd f g).base ((pointClosureFibre f g x).subschemeι.base w) =
          ((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g).base w :=
        (Scheme.Hom.comp_apply _ _ w).symm
      rw [properPushforward_apply_image_of_isClosedImmersion, val_cycleGroup_cast C _ hdeg,
        flatPullback_apply]
      have hsmul : ((α.1 x • β : CycleGroup C g m)).1
          (((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g).base w) =
          α.1 x * β.1 (((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g).base w) := by
        simp
      have hwt : flatPullbackWeight C
            ((pointClosureFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f))
            ((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g)
            (m + ((n.toNat : ℕ) : ℤ)) w =
          exteriorProductWeight C f g (n + m) x
            (((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g).base w)
            ((pointClosureFibre f g x).subschemeι.base w) := by
        rw [hdeg, exteriorProductWeight,
          closedSubschemeCycleCoeff_comap_of_isClosedImmersion C (pullback.fst f g ≫ f)
            (pointClosureFibre f g x).subschemeι _
            (ker_pointClosureFibre_le_exteriorProductIdeal f g x _) (n + m) w,
          comap_exteriorProductIdeal_subschemeι f g x
            (((pointClosureFibre f g x).subschemeι ≫ pullback.snd f g).base w),
          flatPullbackWeight]
      rw [hsmul, hwt]
      by_cases hw : (pullback.fst f g).base ((pointClosureFibre f g x).subschemeι.base w) = x
      · rw [ite_eq_left hw, exteriorProductCoeff, hw, hpt]
      · rw [ite_eq_right hw, exteriorProductWeight_eq_zero_of_ne C f g (n + m) x _ _ hw,
          mul_zero]
    · rw [properPushforward_apply_of_notMem_range C
        ((pointClosureFibre f g x).subschemeι ≫ (pullback.fst f g ≫ f)) (pullback.fst f g ≫ f)
        (pointClosureFibre f g x).subschemeι rfl (n + m) _ hz]
      refine (ite_eq_right fun hzx ↦ hz ?_).symm
      rw [(pointClosureFibre f g x).range_subschemeι]
      exact (mem_support_pointClosureFibre_iff f g x z).2 (hzx ▸ subset_closure rfl)

/-- The exterior product of an `n`-cycle on `X` with an `m`-cycle on `Y` which is rationally
equivalent to zero is rationally equivalent to zero. -/
@[stacks 0FBV "well defined in the second variable, unconditionally"]
theorem exteriorProduct_mem_rationalEquivalences_right (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (n m : ℤ)
    (α : CycleGroup C f n) {β : CycleGroup C g m} (hβ : β ∈ rationalEquivalences C g m) :
    exteriorProduct C f g n m α β ∈ rationalEquivalences C (pullback.fst f g ≫ f) (n + m) := by
  classical
  by_cases hn : 0 ≤ n
  · have ha : ∀ x : α.1.support, ∃ a : CycleGroup C
        ((pointClosureFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m),
        a ∈ rationalEquivalences C
            ((pointClosureFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f)) (n + m) ∧
          ∀ z : (pullback f g : Scheme.{u}),
            (properPushforward C
              ((pointClosureFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f))
              (pullback.fst f g ≫ f) (pointClosureFibre f g x.1).subschemeι rfl (n + m) a).1 z =
              if (pullback.fst f g).base z = x.1 then exteriorProductCoeff C f g n m α β z
              else 0 := fun x ↦
      exists_exteriorProductSummand C hδ f g n m hn
        (flatPullbackFactorsThroughRationalEquivalenceOnPointClosureFibres_holds C f g m)
        α hβ x.1 x.2
    choose a hamem hapush using ha
    have hsum : ∀ z : (pullback f g : Scheme.{u}),
        (exteriorProduct C f g n m α β).1 z = ∑ᶠ x : α.1.support,
          (properPushforward C ((pointClosureFibre f g x.1).subschemeι ≫ (pullback.fst f g ≫ f))
            (pullback.fst f g ≫ f) (pointClosureFibre f g x.1).subschemeι rfl (n + m)
            (a x)).1 z := by
      intro z
      simp_rw [hapush]
      by_cases hz : α.1 ((pullback.fst f g).base z) = 0
      · have hterm : ∀ x : α.1.support,
            (if (pullback.fst f g).base z = x.1 then exteriorProductCoeff C f g n m α β z
              else 0) = 0 := by
          intro x
          by_cases hx : (pullback.fst f g).base z = x.1
          · rw [ite_eq_left hx, exteriorProductCoeff, hz, zero_mul, zero_mul]
          · rw [ite_eq_right hx]
        rw [finsum_eq_zero_of_forall_eq_zero hterm]
        show exteriorProductCoeff C f g n m α β z = 0
        rw [exteriorProductCoeff, hz, zero_mul, zero_mul]
      · rw [finsum_eq_single _ (⟨(pullback.fst f g).base z, hz⟩ : α.1.support)]
        · rw [ite_eq_left rfl]
          rfl
        · intro x hx
          exact ite_eq_right fun hxx ↦ hx (Subtype.ext hxx.symm)
    exact rationallyEquivalentToZero_finsum_of_closedSupports C (pullback.fst f g ≫ f) (n + m)
      (fun x : α.1.support ↦ pointClosureFibre f g x.1) (locallyFinite_comap_pointClosure f g α.1)
      a hamem hsum
  · have hα : α = 0 := by
      refine Subtype.ext (DFunLike.ext _ _ fun x ↦ ?_)
      by_contra hx
      refine hn ?_
      have hdim := (mem_cyclesOfDimension_iff_forall_point C f n α.1).1 α.2 x
        fun h ↦ hx (by rw [h]; rfl)
      rw [← hdim]
      exact relativeDimension_nonneg C hδ f x
    rw [hα, map_zero]
    exact (rationalEquivalences C (pullback.fst f g ≫ f) (n + m)).zero_mem

/-- The exterior product is symmetric: the coefficient of `α × β` at a point of `X ×_S Y` is the
coefficient of `β × α` at the corresponding point of `Y ×_S X`, the two points corresponding under
the isomorphism exchanging the two factors. -/
private theorem exteriorProductCoeff_pullbackSymmetry (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S) [LocallyOfFiniteType g] (n m : ℤ)
    (α : CycleGroup C f n) (β : CycleGroup C g m) (w : (pullback g f : Scheme.{u})) :
    exteriorProductCoeff C f g n m α β ((pullbackSymmetry f g).inv.base w) =
      exteriorProductCoeff C g f m n β α w := by
  set e : (pullback f g : Scheme.{u}) ≅ (pullback g f : Scheme.{u}) := pullbackSymmetry f g with he
  have hfst : (pullback.fst f g).base (e.inv.base w) = (pullback.snd g f).base w := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : (pullback g f : Scheme.{u}) ⟶ X ↦ q w) (pullbackSymmetry_inv_comp_fst f g)
  have hsnd : (pullback.snd f g).base (e.inv.base w) = (pullback.fst g f).base w := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : (pullback g f : Scheme.{u}) ⟶ Y ↦ q w) (pullbackSymmetry_inv_comp_snd f g)
  have hbase : e.inv ≫ (pullback.fst f g ≫ f) = pullback.fst g f ≫ g := by
    rw [← Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.condition]
  have hideal : exteriorProductIdeal g f ((pullback.fst g f).base w)
        ((pullback.snd g f).base w) =
      (exteriorProductIdeal f g ((pullback.snd g f).base w)
        ((pullback.fst g f).base w)).comap e.inv := by
    rw [exteriorProductIdeal, exteriorProductIdeal, Scheme.IdealSheafData.comap_sup,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, he,
      pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd]
    exact sup_comm _ _
  rw [exteriorProductCoeff, exteriorProductCoeff, hfst, hsnd, exteriorProductWeight,
    exteriorProductWeight, add_comm m n,
    ← closedSubschemeCycleCoeff_comap_of_isIso C (pullback.fst g f ≫ g) (pullback.fst f g ≫ f)
      e.inv hbase
      (exteriorProductIdeal f g ((pullback.snd g f).base w) ((pullback.fst g f).base w))
      (exteriorProductIdeal g f ((pullback.fst g f).base w) ((pullback.snd g f).base w))
      hideal (n + m) w]
  ring

/-- The exterior product of an `n`-cycle on `X` which is rationally equivalent to zero with an
`m`-cycle on `Y` is rationally equivalent to zero. -/
@[stacks 0FBV "well defined in the first variable, unconditionally"]
theorem exteriorProduct_mem_rationalEquivalences_left (C : ChowSituation.{u}) [Subsingleton C.S]
    [IsIntegral C.S] [JacobsonSpace C.S]
    (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (n m : ℤ)
    {α : CycleGroup C f n} (hα : α ∈ rationalEquivalences C f n) (β : CycleGroup C g m) :
    exteriorProduct C f g n m α β ∈ rationalEquivalences C (pullback.fst f g ≫ f) (n + m) := by
  set e : (pullback f g : Scheme.{u}) ≅ (pullback g f : Scheme.{u}) := pullbackSymmetry f g with he
  have hbase : e.inv ≫ (pullback.fst f g ≫ f) = pullback.fst g f ≫ g := by
    rw [← Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.condition]
  have hswap : exteriorProduct C g f m n β α ∈
      rationalEquivalences C (pullback.fst g f ≫ g) (m + n) :=
    exteriorProduct_mem_rationalEquivalences_right C hδ g f m n β hα
  have hcast : ((add_comm m n ▸ exteriorProduct C g f m n β α :
      CycleGroup C (pullback.fst g f ≫ g) (n + m))) ∈
      rationalEquivalences C (pullback.fst g f ≫ g) (n + m) :=
    mem_rationalEquivalences_cast C (pullback.fst g f ≫ g) (add_comm m n) hswap
  have hpf := properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion e.inv C
    (pullback.fst g f ≫ g) (pullback.fst f g ≫ f) hbase (n + m) _ hcast
  have hval : properPushforward C (pullback.fst g f ≫ g) (pullback.fst f g ≫ f) e.inv hbase
        (n + m) (add_comm m n ▸ exteriorProduct C g f m n β α) =
      exteriorProduct C f g n m α β := by
    refine Subtype.ext (DFunLike.ext _ _ fun z ↦ ?_)
    obtain ⟨w, rfl⟩ := (Scheme.homeoOfIso e.symm).surjective z
    rw [show (Scheme.homeoOfIso e.symm) w = e.inv.base w from rfl,
      properPushforward_apply_image_of_isClosedImmersion C (pullback.fst g f ≫ g)
        (pullback.fst f g ≫ f) e.inv hbase (n + m) _ w,
      val_cycleGroup_cast C (pullback.fst g f ≫ g) (add_comm m n)]
    exact (exteriorProductCoeff_pullbackSymmetry C f g n m α β w).symm
  rwa [hval] at hpf

/-! ### The descent to Chow groups -/

/-- A bilinear map of abelian groups descends to the quotients by three subgroups, provided it
carries each of the first two into the third. -/
def quotientAddSubgroupBilinearMap {A B D : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (NA : AddSubgroup A) (NB : AddSubgroup B) (ND : AddSubgroup D)
    (b : A →+ B →+ D) (hA : ∀ a ∈ NA, ∀ c, b a c ∈ ND) (hB : ∀ a c, c ∈ NB → b a c ∈ ND) :
    A ⧸ NA →+ B ⧸ NB →+ D ⧸ ND :=
  QuotientAddGroup.lift NA
    { toFun := fun a ↦ QuotientAddGroup.map NB ND (b a) (hB a)
      map_zero' := by
        ext c
        change QuotientAddGroup.mk (b 0 c) = 0
        simp
      map_add' := fun a a' ↦ by
        ext c
        change QuotientAddGroup.mk (b (a + a') c) =
          QuotientAddGroup.mk (b a c) + QuotientAddGroup.mk (b a' c)
        simp }
    fun a ha ↦ by
      ext c
      exact (QuotientAddGroup.eq_zero_iff _).2 (hA a ha c)

/-- The map out of the tensor product of two quotients induced by a bilinear map carrying each of
two subgroups into a third. -/
def quotientAddSubgroupTensorMap {A B D : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (NA : AddSubgroup A) (NB : AddSubgroup B) (ND : AddSubgroup D)
    (b : A →+ B →+ D) (hA : ∀ a ∈ NA, ∀ c, b a c ∈ ND) (hB : ∀ a c, c ∈ NB → b a c ∈ ND) :
    TensorProduct ℤ (A ⧸ NA) (B ⧸ NB) →+ D ⧸ ND :=
  (TensorProduct.lift
    { toFun := fun a ↦ (quotientAddSubgroupBilinearMap NA NB ND b hA hB a).toIntLinearMap
      map_add' := fun a a' ↦ by
        ext c
        exact congrArg (fun h : (B ⧸ NB) →+ (D ⧸ ND) ↦ h c)
          ((quotientAddSubgroupBilinearMap NA NB ND b hA hB).map_add a a')
      map_smul' := fun r a ↦ by
        ext c
        exact congrArg (fun h : (B ⧸ NB) →+ (D ⧸ ND) ↦ h c)
          ((quotientAddSubgroupBilinearMap NA NB ND b hA hB).map_zsmul r a) }).toAddMonoidHom

/-- The map out of a tensor product of quotients induced by a bilinear map sends a pure tensor of
classes to the class of the value of the bilinear map. -/
theorem quotientAddSubgroupTensorMap_tmul {A B D : Type u} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (NA : AddSubgroup A) (NB : AddSubgroup B) (ND : AddSubgroup D)
    (b : A →+ B →+ D) (hA : ∀ a ∈ NA, ∀ c, b a c ∈ ND) (hB : ∀ a c, c ∈ NB → b a c ∈ ND)
    (a : A) (c : B) :
    quotientAddSubgroupTensorMap NA NB ND b hA hB
        (TensorProduct.tmul ℤ (QuotientAddGroup.mk a) (QuotientAddGroup.mk c)) =
      QuotientAddGroup.mk (b a c) :=
  rfl

/-- The exterior product on Chow groups,

  `× : CH_n(X) ⊗_ℤ CH_m(Y) ⟶ CH_{n+m}(X ×_k Y)`,

for `X` and `Y` locally of finite type over a field: the exterior product of cycles,
`Stacks.Chow.exteriorProduct`, read modulo rational equivalence. -/
@[stacks 0FBV]
def chowExteriorProduct (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S]
    [JacobsonSpace C.S] (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (n m : ℤ) :
    TensorProduct ℤ (chowGroup C f n) (chowGroup C g m) →+
      chowGroup C (pullback.fst f g ≫ f) (n + m) :=
  quotientAddSubgroupTensorMap (rationalEquivalences C f n) (rationalEquivalences C g m)
    (rationalEquivalences C (pullback.fst f g ≫ f) (n + m)) (exteriorProduct C f g n m)
    (fun _ hα _ ↦ exteriorProduct_mem_rationalEquivalences_left C hδ f g n m hα _)
    (fun _ _ hβ ↦ exteriorProduct_mem_rationalEquivalences_right C hδ f g n m _ hβ)

/-- On a pure tensor of cycle classes the exterior product on Chow groups is the
class of the exterior product of the two cycles. -/
@[simp]
theorem chowExteriorProduct_tmul_mk (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S]
    [JacobsonSpace C.S] (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0)
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (g : Y ⟶ C.S)
    [LocallyOfFiniteType g] (n m : ℤ)
    (α : CycleGroup C f n) (β : CycleGroup C g m) :
    chowExteriorProduct C hδ f g n m
        (TensorProduct.tmul ℤ (QuotientAddGroup.mk α) (QuotientAddGroup.mk β)) =
      QuotientAddGroup.mk (exteriorProduct C f g n m α β) :=
  rfl

end Stacks.Chow

end
