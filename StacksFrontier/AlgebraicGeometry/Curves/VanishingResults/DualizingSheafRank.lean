module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.Situation
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GenericPointSupport
public import StacksFrontier.AlgebraicGeometry.ColimitClose.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Irreducible
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.AmpleReducedDimensionOne.Extension
public import StacksFrontier.AlgebraicGeometry.Ample.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMultiplication
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf of an integral proper curve has rank one

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — assume `X` integral. The dualizing sheaf `ω_X = H^{-1}(ω_X^•)` of
[Stacks, Tag 0BS2] has rank at most one: every coherent submodule of `ω_X` has fibre rank at most
one at the generic point. Consequently a rank one coherent submodule `ℱ ⊆ ω_X` whose cokernel has
no global sections is all of `ω_X`. This is the input to the equality case of
[Stacks, Tag 0E3A], where the source uses that `ω_X` is invertible on the nonempty Gorenstein
locus ([Stacks, Tag 0BFQ]).

## Main results

* `AlgebraicGeometry.tensorLeft_map_smul`: tensoring by a module is `k`-linear, and
  `AlgebraicGeometry.tensorLeftHomLinearEquiv`: tensoring by an invertible module identifies
  Hom-spaces `k`-linearly.
* `AlgebraicGeometry.invertibleCurveDegree_tensorPower`: `deg(N^{⊗ n}) = n · deg(N)`.
* `CohenMacaulayCurveSituation.not_isAffine` and
  `CohenMacaulayCurveSituation.exists_isInvertible_invertibleCurveDegree_pos`: an integral `X`
  carries an invertible module of positive degree.
* `CohenMacaulayCurveSituation.fiberRank_genericPoint_le_one_of_mono`: coherent submodules of
  `ω_X` have rank at most one.
* `CohenMacaulayCurveSituation.isIso_of_subsingleton_sections_cokernel`: a rank one coherent
  submodule of `ω_X` with sectionless cokernel is `ω_X`.

## The argument

The rank is detected by twisting. Let `N` be invertible of degree `d > 0` and `𝒢 ⊆ ω_X` coherent
of rank `r`. For `m ≥ 1` the module `N^{⊗ -m}` has negative degree, so no sections, and
Riemann-Roch gives `h^1(N^{⊗ -m}) = md - 1 + g`; by clause (5) of [Stacks, Tag 0BS2] this is the
dimension of `Hom(N^{⊗ -m}, ω_X)`, which contains `Hom(N^{⊗ -m}, 𝒢) ≅ H^0(N^{⊗ m} ⊗ 𝒢)`, of
dimension at least `χ(N^{⊗ m} ⊗ 𝒢) = rmd + χ(𝒢)` by [Stacks, Tag 0AYV]. Letting `m` grow forces
`r ≤ 1`. The positive degree module is a power of an ample module ([Stacks, Tag 09NX]) with a
section whose nonvanishing locus is affine, hence not all of the non-affine `X`, so the section
vanishes somewhere ([Stacks, Tag 0B40]).

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0E3A](https://stacks.math.columbia.edu/tag/0E3A)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Tensoring on the left commutes with multiplication by a scalar of the base field.** -/
theorem tensorLeftFunctor_map_baseScalar (A M : X.Modules) (c : k) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
        X.ringCatSheaf.2⟩).obj A)).map
        ((baseScalar k (Over.mk f) c).app M) =
      (baseScalar k (Over.mk f) c).app
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
            X.ringCatSheaf.2⟩).obj A)).obj M) := by
  let adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
    X.ringCatSheaf.2
  let Av : PresheafOfModules
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf) := A.val
  let Mv : PresheafOfModules
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf) := M.val
  let m : Mv ⟶ Mv := ((baseScalar k (Over.mk f) c).app M).val
  have key : (tensorLeft Av).map m ≫ adj.unit.app ((tensorLeft Av).obj Mv) =
      adj.unit.app ((tensorLeft Av).obj Mv) ≫
        (SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf
          X.presheaf X.ringCatSheaf.2) ⋙ PresheafOfModules.restrictScalars (𝟙 _)).map
          ((baseScalar k (Over.mk f) c).app
            ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
                X.ringCatSheaf.2⟩).obj A)).obj M)) := by
    refine PresheafOfModules.hom_ext fun U => ?_
    refine ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
    let r : (X.presheaf ⋙ forget₂ CommRingCat RingCat).obj U :=
      baseRingToSections k (Over.mk f) U c
    exact (congrArg ((adj.unit.app ((tensorLeft Av).obj Mv)).app U).hom
      (TensorProduct.tmul_smul r x y)).trans
        (((adj.unit.app ((tensorLeft Av).obj Mv)).app U).hom.map_smul r (x ⊗ₜ y))
  exact (adj.homEquiv ((tensorLeft Av).obj Mv) _).injective <| (adj.homEquiv_unit _ _ _).trans
    (((adj.unit.naturality ((tensorLeft Av).map m)).symm.trans key).trans
      (adj.homEquiv_unit _ _ _).symm)

/-- **Tensoring on the left by a module `A`**, as an endofunctor of `X.Modules`:
`Stacks.SheafOfModules.tensorLeftFunctor` at the structure sheaf of `X`. -/
def Scheme.Modules.tensorLeft (A : X.Modules) : X.Modules ⥤ X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨X.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
      X.ringCatSheaf.2⟩).obj A)

/-- **Tensoring on the left by a module is `k`-linear.** -/
theorem tensorLeft_map_smul (A : X.Modules) (c : k) {M N : X.Modules} (g : M ⟶ N) :
    letI : Linear k X.Modules := modulesLinearOverField k f
    (Scheme.Modules.tensorLeft A).map (c • g) = c • (Scheme.Modules.tensorLeft A).map g := by
  let : Linear k X.Modules := modulesLinearOverField k f
  have h := (Scheme.Modules.tensorLeft A).map_comp ((baseScalar k (Over.mk f) c).app M) g
  rwa [show (Scheme.Modules.tensorLeft A).map ((baseScalar k (Over.mk f) c).app M) =
    (baseScalar k (Over.mk f) c).app ((Scheme.Modules.tensorLeft A).obj M) from
    tensorLeftFunctor_map_baseScalar k f A M c] at h

/-- **`deg(N^{⊗ n}) = n · deg(N)`** for an invertible module `N` and every integer `n`. -/
theorem invertibleCurveDegree_tensorPower [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (n : ℤ) :
    @invertibleCurveDegree k _ X f _ hdim
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 N n)
        (Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
          X.ringCatSheaf.2 N n) =
      n * invertibleCurveDegree k f hdim N :=
  invertibleCurveDegree_tensorPower_eq_mul k f hdim N
    (@invertibleCurveDegree_tensorSheaf_eq_add k _ X f _ hdim) n

/-- **The degree of a restricted tensor power.** For a morphism `i : Y ⟶ X` from a proper scheme
`Y` of dimension at most one over `k` and an invertible `𝒪_X`-module `𝒩`,
`deg(i^*(𝒩^{⊗ m})) = m · deg(i^* 𝒩)` for every integer `m`: pullback commutes with the integral
tensor powers (`Stacks.TensorPowerPullback.pullbackIntPowIso`). -/
theorem invertibleCurveDegree_pullback_tensorPower {k : Type u} [Field k] {Y : Scheme.{u}}
    (i : Y ⟶ X) (g : Y ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim Y ≤ 1)
    (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N] (m : ℤ)
    [hP : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 N m))]
    [hQ : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj N)] :
    invertibleCurveDegree k g hdim ((Scheme.Modules.pullback i).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 N m)) =
      m * invertibleCurveDegree k g hdim ((Scheme.Modules.pullback i).obj N) := by
  have hT := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible Y.presheaf
    Y.ringCatSheaf.2 ((Scheme.Modules.pullback i).obj N) m
  have e : (Scheme.Modules.pullback i).obj
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 N m) ≅
      Stacks.SheafOfModules.Invertible.tensorPower Y.presheaf Y.ringCatSheaf.2
        ((Scheme.Modules.pullback i).obj N) m :=
    Stacks.TensorPowerPullback.pullbackIntPowIso i.toLRSHom.toShHom N m
  exact (@invertibleCurveDegree_eq_of_iso k _ Y g _ hdim _ _ hP hT e).trans
    (invertibleCurveDegree_tensorPower k g hdim _ m)

/-- **Tensoring by an invertible module identifies Hom-spaces `k`-linearly**:
`Hom(A, B) ≃ₗ[k] Hom(P ⊗ A, P ⊗ B)`. -/
def tensorLeftHomLinearEquiv (P : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P] (A B : X.Modules) :
    letI : Linear k X.Modules := modulesLinearOverField k f
    (A ⟶ B) ≃ₗ[k] ((Scheme.Modules.tensorLeft P).obj A ⟶ (Scheme.Modules.tensorLeft P).obj B) :=
  letI : Linear k X.Modules := modulesLinearOverField k f
  haveI : (Scheme.Modules.tensorLeft P).IsEquivalence :=
    (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ P).mp ‹_›
  haveI : (Scheme.Modules.tensorLeft P).Additive :=
    Functor.additive_of_preserves_binary_products _
  { (Functor.FullyFaithful.ofFullyFaithful (Scheme.Modules.tensorLeft P)).homEquiv with
    map_add' := fun g h => (Scheme.Modules.tensorLeft P).map_add
    map_smul' := fun c g => tensorLeft_map_smul k f P c g }

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- A proper integral one-dimensional scheme over `k` is a curve. -/
theorem isCurve [IsIntegral S.X] : IsCurve S.k S.f :=
  { topologicalKrullDim_eq_one := S.dimension_one }

/-- A scheme proper over a field is locally Noetherian. -/
instance isLocallyNoetherian_X : IsLocallyNoetherian S.X :=
  LocallyOfFiniteType.isLocallyNoetherian S.f

/-- **An integral `X` has an invertible module of positive degree.** An ample invertible module
exists ([Stacks, Tag 09NX]); some positive power of it has a global section with affine
nonvanishing locus, which is not all of `X` since `X` is not affine, so the section vanishes at a
point and the degree of that power is positive ([Stacks, Tag 0B40], part (2)). -/
theorem exists_isInvertible_invertibleCurveDegree_pos [IsIntegral S.X] :
    ∃ (N : S.X.Modules) (_ : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 N),
      0 < invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) N := by
  have : IsNoetherian S.X := isNoetherian_of_locallyOfFiniteType S.f
  have : S.X.IsSeparated := ⟨by
    rw [show terminal.from S.X = S.f ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  obtain ⟨A, hA, -, hx⟩ :=
    Stacks.AmpleReducedDimensionOne.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      S.X (le_of_eq S.dimension_one)
  obtain ⟨n, -, s, hxs, haff⟩ := hx (genericPoint S.X)
  have hN : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2
      (Stacks.SheafOfModules.Invertible.tensorPower S.X.presheaf S.X.ringCatSheaf.2 A (n : ℤ)) :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible S.X.presheaf
      S.X.ringCatSheaf.2 A (n : ℤ)
  refine ⟨_, hN, @invertibleCurveDegree_pos_of_eval_top_ne_zero S.k _ S.X S.f _ _
    (le_of_eq S.dimension_one) _ hN s (eval_top_ne_zero_of_mem_nonvanishingLocus _ s hxs) ?_⟩
  by_contra hall
  push Not at hall
  have htop : Stacks.SheafOfModules.nonvanishingOpen
      (X := S.X.toLocallyRingedSpace.toRingedSpace) _ s = ⊤ :=
    eq_top_iff.mpr fun y _ => hall y
  rw [htop] at haff
  have : IsAffine (⊤ : S.X.Opens) := haff
  exact S.not_isAffine (IsAffine.of_isIso S.X.topIso.inv)

/-- **An invertible module of negative degree has no global sections** ([Stacks, Tag 0B40],
part (1)). -/
theorem finrank_cohomologyOverField_zero_eq_zero_of_invertibleCurveDegree_neg [IsIntegral S.X]
    (Q : S.X.Modules) [hQ : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 Q]
    (h : invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) Q < 0) :
    Module.finrank S.k (cohomologyOverField S.k S.f Q 0) = 0 := by
  by_contra hne
  have hnt : Nontrivial (cohomologyOverField S.k S.f Q 0) :=
    Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hne)
  have hnt' : Nontrivial Γ(Q, ⊤) :=
    (cohomologyOverFieldZeroEquivSections S.k S.f Q).symm.nontrivial
  obtain ⟨t, ht⟩ := exists_ne (0 : Γ(Q, ⊤))
  obtain ⟨s, hs⟩ := (bijective_sections_eval_top Q).2 t
  have h0 := @invertibleCurveDegree_nonneg_of_eval_top_ne_zero S.k _ S.X S.f _ _
    (le_of_eq S.dimension_one) Q hQ s (fun h0 => ht (hs.symm.trans h0))
  omega

/-- **`N^{⊗ m} ⊗ N^{⊗ -m} ≅ 𝒪_X`** for an invertible module `N`. -/
def tensorPowerNegIso (N : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 N] (m : ℤ) :
    (Scheme.Modules.tensorLeft
        (Stacks.SheafOfModules.Invertible.tensorPower S.X.presheaf S.X.ringCatSheaf.2 N m)).obj
      (Stacks.SheafOfModules.Invertible.tensorPower S.X.presheaf S.X.ringCatSheaf.2 N (-m)) ≅
      structureSheafModule S.X :=
  Stacks.SheafOfModules.TensorPower.tensorPowerMulIso S.X.presheaf S.X.ringCatSheaf.2 N m (-m) ≪≫
    Stacks.SheafOfModules.TensorPower.tensorPowerReindex S.X.presheaf S.X.ringCatSheaf.2 N
      (add_neg_cancel m)

/-- **The key count.** For `G ⊆ ω_X` coherent with fibre rank `r` at the generic point, an
invertible `N` of degree `d` and `m ≥ 1`: `r m d + χ(G) ≤ m d + g - 1`. The right side is
`h^1(N^{⊗ -m}) = dim Hom(N^{⊗ -m}, ω_X)`, the left side bounds
`h^0(N^{⊗ m} ⊗ G) = dim Hom(N^{⊗ -m}, G)` from below. -/
theorem fiberRank_mul_le_of_mono [IsIntegral S.X] (G : S.X.Modules) [hG : G.IsCoherent]
    (ι : G ⟶ Stacks.Duality.dualizingSheafOverField S.f) [Mono ι] (N : S.X.Modules)
    [hN : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 N]
    (hd : 0 < invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) N) (m : ℕ) (hm : 1 ≤ m) :
    (Scheme.Modules.fiberRank G (genericPoint S.X) : ℤ) * m *
        invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) N +
        @eulerCharacteristic S.k _ S.X S.f _ G hG ≤
      m * invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) N + genus S.f - 1 := by
  let : Linear S.k S.X.Modules := modulesLinearOverField S.k S.f
  have := S.isCurve
  have hdim : topologicalKrullDim S.X ≤ 1 := le_of_eq S.dimension_one
  set d := invertibleCurveDegree S.k S.f hdim N
  let A : S.X.Modules :=
    Stacks.SheafOfModules.Invertible.tensorPower S.X.presheaf S.X.ringCatSheaf.2 N m
  let B : S.X.Modules :=
    Stacks.SheafOfModules.Invertible.tensorPower S.X.presheaf S.X.ringCatSheaf.2 N (-m)
  have hA : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 A :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible S.X.presheaf S.X.ringCatSheaf.2 N _
  have hB : SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 B :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible S.X.presheaf S.X.ringCatSheaf.2 N _
  have hdegA : invertibleCurveDegree S.k S.f hdim A = m * d :=
    invertibleCurveDegree_tensorPower S.k S.f hdim N m
  have hdegB : invertibleCurveDegree S.k S.f hdim B = -m * d := by
    rw [invertibleCurveDegree_tensorPower S.k S.f hdim N (-m)]
  -- `Hom(B, G) ≃ₗ H^0(A ⊗ G)`.
  let Θ : (B ⟶ G) ≃ₗ[S.k] cohomologyOverField S.k S.f ((Scheme.Modules.tensorLeft A).obj G) 0 :=
    (tensorLeftHomLinearEquiv S.k S.f A B G).trans <|
      (Linear.homCongr S.k (S.tensorPowerNegIso N m) (Iso.refl _)).trans
        (unitHomLinearEquivCohomologyZero S.k S.f _)
  -- `Hom(B, ω_X) ≃ₗ H^1(X, B)^∨`.
  have hBc : B.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k S.f B 1
  have hBq : B.IsQuasicoherent := isQuasicoherent_of_isCoherent B
  let Δ := Stacks.Duality.homDualizingSheafLinearEquiv S.f hdim B hBq
  have := finiteDimensional_cohomologyOverField_of_isProper S.k S.f B 1
  have : FiniteDimensional S.k (B ⟶ Stacks.Duality.dualizingSheafOverField S.f) :=
    LinearEquiv.finiteDimensional Δ.symm
  have h1 : Module.finrank S.k (B ⟶ G) ≤
      Module.finrank S.k (B ⟶ Stacks.Duality.dualizingSheafOverField S.f) :=
    LinearMap.finrank_le_finrank_of_injective (f := Linear.rightComp S.k B ι)
      (fun a b h => (cancel_mono ι).mp h)
  rw [Δ.finrank_eq, Subspace.dual_finrank_eq, Θ.finrank_eq] at h1
  -- Riemann-Roch for `B`, which has no sections.
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus S.k S.f hdim B
  rw [S.finrank_cohomologyOverField_zero_eq_zero_of_invertibleCurveDegree_neg B (by
    rw [hdegB]
    nlinarith), hdegB] at hRR
  -- Riemann-Roch for `A ⊗ G`.
  have hcAG : ((Scheme.Modules.tensorLeft A).obj G).IsCoherent :=
    isCoherent_tensorSheaf_of_isCurve S.k S.f A 1 G
  have hχ := eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add S.k S.f A 1 G hcAG
  rw [← invertibleCurveDegree_eq_curveDegree, hdegA] at hχ
  have hχ' := @eulerCharacteristic_eq_finsum S.k _ S.X S.f _ _ hcAG
  rw [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero S.k S.f _
    (isZero_cohomologyOverField_two_le S.k S.f hdim _)] at hχ'
  change @eulerCharacteristic S.k _ S.X S.f _ ((Scheme.Modules.tensorLeft A).obj G) hcAG = _
    at hχ
  have h1' : (Module.finrank S.k (cohomologyOverField S.k S.f
      ((Scheme.Modules.tensorLeft A).obj G) 0) : ℤ) ≤ m * d + genus S.f - 1 := by
    have := Int.ofNat_le.mpr h1
    push_cast at this hRR
    linarith
  have hnn : (0 : ℤ) ≤ Module.finrank S.k (cohomologyOverField S.k S.f
      ((Scheme.Modules.tensorLeft A).obj G) 1) := Int.natCast_nonneg _
  push_cast at hχ
  nlinarith

/-- **The dualizing sheaf has rank at most one**: a coherent `𝒪_X`-submodule of `ω_X` has fibre
rank at most one at the generic point of the integral `X`. -/
theorem fiberRank_genericPoint_le_one_of_mono [IsIntegral S.X] (G : S.X.Modules) [hG : G.IsCoherent]
    (ι : G ⟶ Stacks.Duality.dualizingSheafOverField S.f) [Mono ι] :
    Scheme.Modules.fiberRank G (genericPoint S.X) ≤ 1 := by
  obtain ⟨N, hN, hd⟩ := S.exists_isInvertible_invertibleCurveDegree_pos
  set χ := @eulerCharacteristic S.k _ S.X S.f _ G hG
  set d := invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) N
  set r := (Scheme.Modules.fiberRank G (genericPoint S.X) : ℤ)
  set M : ℕ := genus S.f + χ.natAbs + 1
  have h := S.fiberRank_mul_le_of_mono G ι N hd M (by omega)
  by_contra hr
  have hr2 : (2 : ℤ) ≤ r := by omega
  have hM : ((M : ℕ) : ℤ) = genus S.f + χ.natAbs + 1 := by push_cast [M]; ring
  have habs : -χ ≤ (χ.natAbs : ℤ) := by omega
  have hMd : (M : ℤ) ≤ M * d := le_mul_of_one_le_right (by omega) (by omega)
  nlinarith

/-- **A finite type quasi-coherent submodule of `ω_X / ℱ` is zero**, when `ℱ ⊆ ω_X` is coherent
of rank one and `ω_X / ℱ` has no global sections. Its preimage in `ω_X` is coherent, hence of rank
at most one, so the submodule has rank zero; it is then supported in dimension zero, and such a
module is the direct sum of its stalks along its support ([Stacks, Tag 0AYT], part (2)), which
vanishes with its global sections. -/
theorem isZero_of_subobject_cokernel [IsIntegral S.X] (F : S.X.Modules) [hFc : F.IsCoherent]
    (hF1 : Scheme.Modules.fiberRank F (genericPoint S.X) = 1)
    (φ : F ⟶ Stacks.Duality.dualizingSheafOverField S.f) [Mono φ]
    (hQ : Subsingleton Γ(cokernel φ, ⊤)) (G : Subobject (cokernel φ))
    (hGq : (G : S.X.Modules).IsQuasicoherent) (hGf : (G : S.X.Modules).IsFiniteType) :
    IsZero (G : S.X.Modules) := by
  have : IsNoetherian S.X := isNoetherian_of_locallyOfFiniteType S.f
  have hdim : topologicalKrullDim S.X ≤ 1 := le_of_eq S.dimension_one
  set N : S.X.Modules := (G : S.X.Modules)
  set j : N ⟶ cokernel φ := G.arrow
  set π := cokernel.π φ
  have hNc : N.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isQuasicoherent_isFiniteType N
  -- The preimage `P` of `N` in `ω_X`, an extension of `N` by `ℱ`.
  have hS : (ShortComplex.mk φ π (cokernel.condition φ)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel φ) inferInstance inferInstance
  have hw : (0 : F ⟶ N) ≫ j = φ ≫ π := by rw [zero_comp, cokernel.condition]
  have hzero : pullback.lift (0 : F ⟶ N) φ hw ≫ pullback.fst j π = 0 := pullback.lift_fst _ _ _
  have hT : (ShortComplex.mk (pullback.lift (0 : F ⟶ N) φ hw) (pullback.fst j π)
      hzero).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (Stacks.SheafOfModules.isLimitKernelForkPullbackFst j π hS.fIsKernel _ hzero
          (pullback.lift_snd _ _ _))
      mono_f := mono_of_mono_fac (pullback.lift_snd (0 : F ⟶ N) φ hw)
      epi_g := inferInstance }
  have hPc : (pullback j π).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_X₂_of_shortExact hT hFc hNc
  have hP := S.fiberRank_genericPoint_le_one_of_mono (pullback j π) (pullback.snd j π)
  -- Fibre ranks add at the generic point.
  have hfield : IsField (S.X.presheaf.stalk (genericPoint S.X)) :=
    (inferInstance : Field S.X.functionField).toIsField
  have : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : N.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have : (pullback j π).IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hlen := length_stalk_add_of_shortExact hT (genericPoint S.X)
  have hlF := length_stalk_eq_fiberRank_of_isField F _ hfield
  have hlP := length_stalk_eq_fiberRank_of_isField (pullback j π) _ hfield
  have hfin : ∀ M : S.X.Modules, M.IsFiniteType →
      Module.length (S.X.presheaf.stalk (genericPoint S.X))
      (M.presheaf.stalk (genericPoint S.X)) ≠ ⊤ := fun M _ => by
    let : Field (S.X.presheaf.stalk (genericPoint S.X)) := hfield.toField
    have : Module.Finite (S.X.presheaf.stalk (genericPoint S.X))
        (M.presheaf.stalk (genericPoint S.X)) := SheafOfModules.finite_stalk S.X.sheaf M _
    exact Module.length_ne_top
  have hN0 : Module.length (S.X.presheaf.stalk (genericPoint S.X))
      (N.presheaf.stalk (genericPoint S.X)) = 0 := by
    change Module.length _ ((pullback j π).presheaf.stalk _) =
      Module.length _ (F.presheaf.stalk _) + Module.length _ (N.presheaf.stalk _) at hlen
    rw [hlen, ENat.toNat_add (hfin F ‹_›) (hfin N ‹_›), hlF, hF1] at hlP
    have h0 : (Module.length (S.X.presheaf.stalk (genericPoint S.X))
      (N.presheaf.stalk (genericPoint S.X))).toNat = 0 := by omega
    exact (ENat.toNat_eq_zero.mp h0).resolve_right (hfin N ‹_›)
  -- So `N` misses the generic point and is supported in dimension zero.
  have hη : genericPoint S.X ∉ SheafOfModules.supp N := by
    intro hmem
    have : Nontrivial (N.presheaf.stalk (genericPoint S.X)) :=
      (SheafOfModules.mem_supp_iff_nontrivial_stalk N _).mp hmem
    exact (Module.length_pos (R := S.X.presheaf.stalk (genericPoint S.X))
      (M := N.presheaf.stalk (genericPoint S.X))).ne' hN0
  have hsupp := topologicalKrullDim_supp_le_zero_of_genericPoint_notMem hdim N
    inferInstance hη
  -- Its global sections vanish, hence so do its stalks along the support.
  have hΓ : Subsingleton Γ(N, ⊤) :=
    (Scheme.Modules.injective_app_of_mono j ⊤).subsingleton
  refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty N ?_
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hbij := bijective_suppGermHom_of_supp_le_zero S.k S.f N hsupp
  have hsub : Subsingleton (∀ y : ↥(SheafOfModules.supp N),
      (Scheme.Modules.presheaf N).stalk y.1) := hbij.surjective.subsingleton
  classical
  obtain ⟨a, ha⟩ := hx
  let i : ↥(SheafOfModules.supp N) := ⟨x, ⟨a, ha⟩⟩
  let a' : (Scheme.Modules.presheaf N).stalk i.1 := a
  have := congrFun (Subsingleton.elim (Pi.single (M := fun y : ↥(SheafOfModules.supp N) =>
    (Scheme.Modules.presheaf N).stalk y.1) i a') 0) i
  rw [Pi.single_eq_same] at this
  exact ha this

/-- **An injective map `ℱ ⟶ ω_X` out of a coherent module of rank one is an isomorphism as soon
as its cokernel has no global sections.** Every finite type quasi-coherent submodule of the
cokernel vanishes (`isZero_of_subobject_cokernel`), and a quasi-coherent module is the union of
those ([Stacks, Tag 01PG]). -/
theorem isIso_of_subsingleton_sections_cokernel [IsIntegral S.X] (F : S.X.Modules)
    [hFc : F.IsCoherent] (hF1 : Scheme.Modules.fiberRank F (genericPoint S.X) = 1)
    (φ : F ⟶ Stacks.Duality.dualizingSheafOverField S.f) [Mono φ]
    (hQ : Subsingleton Γ(cokernel φ, ⊤)) : IsIso φ := by
  have : (cokernel φ).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent S.X.ringCatSheaf).prop_cokernel φ
      (isQuasicoherent_of_isCoherent F) (Stacks.Duality.isQuasicoherent_dualizingSheafOverField S.f)
  have : CompactSpace S.X := QuasiCompact.compactSpace_of_compactSpace S.f
  have : QuasiSeparatedSpace S.X := quasiSeparatedSpace_of_quasiSeparated S.f
  have hz : IsZero (cokernel φ) := by
    rw [IsZero.iff_id_eq_zero]
    exact
      (Stacks.AlgebraicGeometry.Tag01PGColimitClose.isColimit_finiteTypeQuasicoherentSubobjectCocone
        (cokernel φ)).hom_ext fun G =>
      (S.isZero_of_subobject_cokernel F hF1 φ hQ G.obj G.property.1 G.property.2).eq_of_src _ _
  have : Epi φ := Preadditive.epi_of_isZero_cokernel φ hz
  exact isIso_of_mono_of_epi φ

end CohenMacaulayCurveSituation

end AlgebraicGeometry
