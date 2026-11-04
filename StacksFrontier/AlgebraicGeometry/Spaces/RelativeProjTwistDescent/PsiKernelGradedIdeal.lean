module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjClosedSubspaceQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjDegreeIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjF1Generated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiKernelAtlas

/-!
# The pieces of `ℐ = ker(𝒜 ⟶ ⨁_d π_*i_*i^*𝒪_P(d))` for a closed subspace (Stacks 085L)

In Situation 0849 let `π : P = Proj_X(𝒜) ⟶ X` be the relative Proj and `i : Z ⟶ P` a closed
subspace.  The kernel `ℐ_d` of the canonical map `𝒜_d ⟶ π_*i_*i^*𝒪_P(d)`, the adjoint of
`ψ_d : π^*𝒜_d ⟶ 𝒪_P(d)` followed by the unit of `i^* ⊣ i_*` (and `ℐ_d = 𝒜_d = 0` for `d < 0`),
is a quasi-coherent `𝒪_X`-module when `π` is quasi-compact (Stacks 03M9 and 084E).

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.etalePointReading_mul`: the reading of local sections of
  `f^*𝒜` on the charts of an étale scheme point `f` is multiplicative.
* `AlgebraicGeometry.Space.C1359Bridge.psiKernelPiece`: the pieces `ℐ_n`.
* `AlgebraicGeometry.Space.C1359Bridge.isQuasicoherentOnSite_psiKernelPiece`: `ℐ_n` is
  quasi-coherent.
* `AlgebraicGeometry.Space.C1359Bridge.mem_twistKerGradedIdeal_iff_mem_psiKernelPiece`: on the
  charts `W ⟶ U ⟶ X` of the atlas, `ℐ` has the sections of the graded ideal of Stacks 0801 of
  `Z ×_X U ⊆ Proj_U(𝒜|_U)`, for `ψ` the map of Stacks 084D.
* `AlgebraicGeometry.Space.C1359Bridge.psiKernelPiece_mul_mem_right_chart`: on those charts `ℐ`
  is stable under multiplication.

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)

namespace AlgebraicGeometry.Space.C1359Bridge

section Mul

variable (s : RelativeProjSituation.{u, u}) {T : BigFppfOver s.site s.base s.containsBase}
  (f : yoneda.obj T ⟶ s.space.1)
  (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) f).hom)

/-- The product of local sections of `f^*𝒜` over `W` is their product in the pullback of graded
algebras over the chart of `W`. -/
theorem relativeProjPoints_algebra_mul_app (i j : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece i, W))
    (b : Γ((s.relativeProjPoints.algebra T f).piece j, W)) :
    ((s.relativeProjPoints.algebra T f).mul i j).app W a b =
      ((etalePointAlgebra s.shrink.algebra T f).mul i j).app
        (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) a b :=
  rfl

/-- The product of homogeneous local sections of a sheaf of graded algebras. -/
def gradedMulApp {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (A : SheafOfModules.GradedAlgebra.{u, u} R) (i j : ℤ) (U : Cᵒᵖ)
    (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) : (A.piece (i + j)).val.obj U :=
  (A.mul i j).app U x y

/-- The product of local sections of `f^*𝒜` over `W`, read in the pullback of graded algebras of
the re-presented algebra over the chart of `W`. -/
theorem relativeProjPoints_algebra_mul_app_gradedMulApp (i j : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece i, W))
    (b : Γ((s.relativeProjPoints.algebra T f).piece j, W)) :
    @Eq (Γ((s.relativeProjPoints.algebra T f).piece (i + j), W))
      (((s.relativeProjPoints.algebra T f).mul i j).app W a b)
      (gradedMulApp (etalePointAlgebra s.shrink.algebra T f) i j
        (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) a b) :=
  relativeProjPoints_algebra_mul_app s f i j W a b

/-- The product of local sections of `f^*𝒜` over `W`, read in the pullback of graded algebras of
`AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebra`. -/
theorem relativeProjPoints_algebra_mul_app_small (i j : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece i, W))
    (b : Γ((s.relativeProjPoints.algebra T f).piece j, W)) :
    @Eq (Γ((s.relativeProjPoints.algebra T f).piece (i + j), W))
      (gradedMulApp (etalePointAlgebra s.shrink.algebra T f) i j
        (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) a b)
      (gradedMulApp (etalePointAlgebra s.smallAlgebra T f) i j
        (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) a b) :=
  rfl

/-- The sections of `f^*𝒜_n` over `W`, unfolded to the sections over the chart of `W` of the
pullback of graded algebras along the scheme point. -/
def etalePointSectionsUnfoldPull (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    ((etalePointAlgebra s.smallAlgebra T f).piece n).val.obj
      (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) :=
  s.etalePointSectionsUnfold f n W a

/-- The unfolding of the sections of `f^*𝒜` is multiplicative. -/
theorem etalePointSectionsUnfoldPull_gradedMulApp (i j : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece i, W))
    (b : Γ((s.relativeProjPoints.algebra T f).piece j, W)) :
    etalePointSectionsUnfoldPull s f (i + j) W
        (gradedMulApp (etalePointAlgebra s.smallAlgebra T f) i j
          (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) a b) =
      gradedMulApp (etalePointAlgebra s.smallAlgebra T f) i j
        (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W))
        (etalePointSectionsUnfoldPull s f i W a) (etalePointSectionsUnfoldPull s f j W b) :=
  rfl

/-- The re-presented algebra, as a sheaf of graded algebras over the structure sheaf of the small
étale ringed topos. -/
abbrev smallAlgebraTopos : SheafOfModules.GradedAlgebra.{u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.site s.base s.containsBase s.space).O) :=
  s.smallAlgebra

/-- The identification of the sections of `f^*𝒜_n` over `W` with those of `𝒜_n` over the chart
`W ⟶ T ⟶ X`, through the comparison of Stacks 03LW. -/
theorem etalePointSectionsEquiv_eq_iso (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (z : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointSectionsEquiv f hf n W z =
      s.smallAlgebraEquiv.equiv n (op ((smallEtalePostcomp s.site s.base s.containsBase
          (pointHom (X := s.space) f) hf).obj
          ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ)
        (((modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
          (pointHom (X := s.space) f) hf).hom.app (s.smallAlgebra.piece n)).val.app
            (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W))
            (etalePointSectionsUnfoldPull s f n W z)) :=
  rfl

/-- `AlgebraicGeometry.Space.C1359Bridge.etalePointSectionsEquiv_eq_iso`, with the comparison of
Stacks 03LW taken at the pieces of `AlgebraicGeometry.Space.C1359Bridge.smallAlgebraTopos`. -/
theorem etalePointSectionsEquiv_eq_iso_topos (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (z : Γ((s.relativeProjPoints.algebra T f).piece n, W)) :
    s.etalePointSectionsEquiv f hf n W z =
      s.smallAlgebraEquiv.equiv n (op ((smallEtalePostcomp s.site s.base s.containsBase
          (pointHom (X := s.space) f) hf).obj
          ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ)
        (((modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
          (pointHom (X := s.space) f) hf).hom.app ((smallAlgebraTopos s).piece n)).val.app
            (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W))
            (etalePointSectionsUnfoldPull s f n W z)) :=
  etalePointSectionsEquiv_eq_iso s f hf n W z

/-- `AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraEquiv_mul_app`, with the product
of the re-presented algebra taken over the structure sheaf of the small étale ringed topos. -/
theorem smallAlgebraEquiv_gradedMulApp (i j : ℤ)
    (U : (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ)
    (x : (s.smallAlgebra.piece i).val.obj U) (y : (s.smallAlgebra.piece j).val.obj U) :
    s.smallAlgebraEquiv.equiv (i + j) U
        (gradedMulApp (R := Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).O)
          s.smallAlgebra i j U x y) =
      (s.algebra.mul i j).app U (s.smallAlgebraEquiv.equiv i U x)
        (s.smallAlgebraEquiv.equiv j U y) :=
  s.smallAlgebraEquiv_mul_app i j U x y

/-- The comparison of Stacks 03LW followed by the comparison with `𝒜` carries products of local
sections of the pullback of the re-presented algebra to products in `𝒜`. -/
theorem smallAlgebraEquiv_modulePullbackIso_hom_mul
    (hrep : yoneda.relativelyRepresentable (pointHom (X := s.space) f).hom) (i j : ℤ)
    (V : SmallEtale s.site s.base s.containsBase (yoneda.obj T))
    (x : ((etalePointAlgebra s.smallAlgebra T f).piece i).val.obj (op V))
    (y : ((etalePointAlgebra s.smallAlgebra T f).piece j).val.obj (op V)) :
    s.smallAlgebraEquiv.equiv (i + j) (op ((smallEtalePostcomp s.site s.base s.containsBase
        (pointHom (X := s.space) f) hf).obj V) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ)
        (((modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
          (pointHom (X := s.space) f) hf).hom.app ((smallAlgebraTopos s).piece (i + j))).val.app
            (op V) (((etalePointAlgebra s.smallAlgebra T f).mul i j).app (op V) x y)) =
      (s.algebra.mul i j).app (op ((smallEtalePostcomp s.site s.base s.containsBase
          (pointHom (X := s.space) f) hf).obj V) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ)
        (s.smallAlgebraEquiv.equiv i (op ((smallEtalePostcomp s.site s.base s.containsBase
            (pointHom (X := s.space) f) hf).obj V) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ)
          (((modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
            (pointHom (X := s.space) f) hf).hom.app ((smallAlgebraTopos s).piece i)).val.app
              (op V) x))
        (s.smallAlgebraEquiv.equiv j (op ((smallEtalePostcomp s.site s.base s.containsBase
            (pointHom (X := s.space) f) hf).obj V) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ)
          (((modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
            (pointHom (X := s.space) f) hf).hom.app ((smallAlgebraTopos s).piece j)).val.app
              (op V) y)) :=
  (congrArg (s.smallAlgebraEquiv.equiv (i + j) (op ((smallEtalePostcomp s.site s.base s.containsBase
      (pointHom (X := s.space) f) hf).obj V) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ))
    (modulePullbackIso_hom_gradedPull_mul (smallAlgebraTopos s) (pointHom (X := s.space) f) hf hrep
      V i j x y)).trans
    (smallAlgebraEquiv_gradedMulApp s i j (op ((smallEtalePostcomp s.site s.base s.containsBase
          (pointHom (X := s.space) f) hf).obj V) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ) _ _)

/-- The product of `𝒜` over the chart `W ⟶ T ⟶ X`, with the chart spelled through the small étale
ringed topos. -/
theorem algebra_mul_app_etalePointChart (i j : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (x : (s.algebra.piece i).val.obj (op (s.etalePointChart f hf W)))
    (y : (s.algebra.piece j).val.obj (op (s.etalePointChart f hf W))) :
    (s.algebra.mul i j).app (op ((smallEtalePostcomp s.site s.base s.containsBase
        (pointHom (X := s.space) f) hf).obj
          ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ) x y =
      (s.algebra.mul i j).app (op (s.etalePointChart f hf W)) x y :=
  rfl

/-- **The reading of local sections on an étale chart is multiplicative**: the identification
of the sections of `f^*𝒜_n` over `W` with those of `𝒜_n` over the chart `W ⟶ T ⟶ X` carries
products to products. -/
theorem etalePointSectionsEquiv_mul
    (hrep : yoneda.relativelyRepresentable (pointHom (X := s.space) f).hom) (i j : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece i, W))
    (b : Γ((s.relativeProjPoints.algebra T f).piece j, W)) :
    s.etalePointSectionsEquiv f hf (i + j) W
        (((s.relativeProjPoints.algebra T f).mul i j).app W a b) =
      (s.algebra.mul i j).app (op (s.etalePointChart f hf W))
        (s.etalePointSectionsEquiv f hf i W a) (s.etalePointSectionsEquiv f hf j W b) := by
  have e0 := congrArg (s.etalePointSectionsEquiv f hf (i + j) W)
    ((relativeProjPoints_algebra_mul_app_gradedMulApp s f i j W a b).trans
      (relativeProjPoints_algebra_mul_app_small s f i j W a b))
  have e1 := etalePointSectionsEquiv_eq_iso s f hf (i + j) W
    (gradedMulApp (etalePointAlgebra s.smallAlgebra T f) i j
        (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) a b)
  have e2 := congrArg (fun y => s.smallAlgebraEquiv.equiv (i + j)
      (op ((smallEtalePostcomp s.site s.base s.containsBase (pointHom (X := s.space) f) hf).obj
          ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ)
      (((modulePullbackIsoEtaleModulePullback s.site s.base s.containsBase
        (pointHom (X := s.space) f) hf).hom.app (s.smallAlgebra.piece (i + j))).val.app
          (op ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) y))
    (etalePointSectionsUnfoldPull_gradedMulApp s f i j W a b)
  have h4 := smallAlgebraEquiv_modulePullbackIso_hom_mul s f hf hrep i j
    ((selfOpensFunctor s.site s.base s.containsBase T).obj W)
    (etalePointSectionsUnfoldPull s f i W a) (etalePointSectionsUnfoldPull s f j W b)
  have e3 := congrArg₂ (fun x y => (s.algebra.mul i j).app
      (op ((smallEtalePostcomp s.site s.base s.containsBase (pointHom (X := s.space) f) hf).obj
          ((selfOpensFunctor s.site s.base s.containsBase T).obj W)) :
          (smallEtaleRingedTopos s.site s.base s.containsBase s.space).Cᵒᵖ) x y)
    (etalePointSectionsEquiv_eq_iso_topos s f hf i W a).symm
    (etalePointSectionsEquiv_eq_iso_topos s f hf j W b).symm
  have e4 := algebra_mul_app_etalePointChart s f hf i j W (s.etalePointSectionsEquiv f hf i W a)
    (s.etalePointSectionsEquiv f hf j W b)
  exact e0.trans (e1.trans (e2.trans (h4.trans (e3.trans e4))))

/-- The reading of a situation is the identification of Stacks 03LW of the situation. -/
theorem etalePointSectionsEquiv_eq_etalePointReading (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) :
    s.etalePointSectionsEquiv f hf n W = s.etalePointReading f hf n W := by
  cases s
  rfl

/-- **The reading of local sections on an étale chart is multiplicative**, for the reading
`AlgebraicGeometry.Space.RelativeProjSituation.etalePointReading` of the situation itself. -/
theorem etalePointReading_mul
    (hrep : yoneda.relativelyRepresentable (pointHom (X := s.space) f).hom) (i j : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (a : Γ((s.relativeProjPoints.algebra T f).piece i, W))
    (b : Γ((s.relativeProjPoints.algebra T f).piece j, W)) :
    s.etalePointReading f hf (i + j) W (((s.relativeProjPoints.algebra T f).mul i j).app W a b) =
      (s.algebra.mul i j).app (op (s.etalePointChart f hf W))
        (s.etalePointReading f hf i W a) (s.etalePointReading f hf j W b) := by
  rw [← etalePointSectionsEquiv_eq_etalePointReading s f hf (i + j) W,
    ← etalePointSectionsEquiv_eq_etalePointReading s f hf i W,
    ← etalePointSectionsEquiv_eq_etalePointReading s f hf j W]
  exact etalePointSectionsEquiv_mul s f hf hrep i j W a b

end Mul

section Kernel

variable (s : RelativeProjSituation.{u, u})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (ψ : ∀ d : ℕ, (s.psiSourceQcoh (d : ℤ)).obj ⟶ (s.twistModule Px (d : ℤ)).obj)

/-- The target `π_*i_*i^*𝒪_P(d)` of the canonical map of Stacks 085L in degree `d`. -/
abbrev psiKernelTarget (d : ℕ) : Modules.{u, u} s.site s.base s.containsBase s.space.1 s.space.2 :=
  (modulePushforward s.site s.base s.containsBase (ObjectProperty.homMk s.relativeProjπ :
      (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space)).obj
    ((modulePushforward s.site s.base s.containsBase (Y :=
        (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) i).obj
      ((modulePullback s.site s.base s.containsBase (Y :=
          (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase)) i).obj
        (s.twistModule Px (d : ℤ)).obj))

/-- **The pieces `ℐ_n ⊆ 𝒜_n` of the graded ideal of Stacks 085L**: the kernel of the canonical
map `𝒜_n ⟶ π_*i_*i^*𝒪_P(n)` attached to `ψ_n` for `n ≥ 0`, and all of `𝒜_n = 0` for `n < 0`. -/
def psiKernelPiece : (n : ℤ) → (s.algebra.piece n).Submodule
  | Int.ofNat d => Stacks.SheafOfModules.kerSubmodule (psiKernelMap s Px i d (ψ d))
  | Int.negSucc k => Stacks.SheafOfModules.kerSubmodule
      (0 : s.algebra.piece (Int.negSucc k) ⟶ s.algebra.piece (Int.negSucc k))

/-- A local section of `𝒜_d`, `d ≥ 0`, lies in `ℐ_d` exactly when the canonical map kills it. -/
theorem mem_psiKernelPiece_iff (d : ℕ)
    (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (x : (s.algebra.piece (d : ℤ)).val.obj V) :
    x ∈ (psiKernelPiece s Px i ψ (d : ℤ)).obj V ↔ (psiKernelMap s Px i d (ψ d)).val.app V x = 0 :=
  Stacks.SheafOfModules.mem_kerSubmodule_obj (psiKernelMap s Px i d (ψ d)) V x

/-- Every local section of `𝒜_d`, `d < 0`, lies in `ℐ_d`. -/
theorem mem_psiKernelPiece_negSucc (k : ℕ)
    (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (x : (s.algebra.piece (Int.negSucc k)).val.obj V) :
    x ∈ (psiKernelPiece s Px i ψ (Int.negSucc k)).obj V :=
  (Stacks.SheafOfModules.mem_kerSubmodule_obj _ V x).2 rfl

/-- The target `π_*i_*i^*𝒪_P(d)` is quasi-coherent for `π` quasi-compact and `i` a closed
immersion. -/
theorem isQuasicoherentOnSite_psiKernelTarget
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) (d : ℕ) :
    (psiKernelTarget s Px i d).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePushforward_of_qcqs s.site s.base s.containsBase
    (ObjectProperty.homMk s.relativeProjπ :
        (⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :
      AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.space) hπ
    (isQuasiSeparated_of_isSeparated s.site s.base s.containsBase s.isSeparated_relativeProjπ) _
    (isQuasicoherentOnSite_modulePushforward_of_qcqs s.site s.base s.containsBase i
      (isQuasiCompact_of_isClosedImmersion s.site s.base s.containsBase i.hom Z.2 s.Proj.2 hi)
      (isQuasiSeparated_of_isSeparated s.site s.base s.containsBase
        (isSeparated_of_isClosedImmersion s.site s.base s.containsBase i.hom hi)) _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite s.site s.base s.containsBase
        i _ (s.isQuasicoherentOnSite_twistModule Px (d : ℤ))))

/-- A kernel of a morphism of quasi-coherent modules on the small étale site is quasi-coherent. -/
theorem isQuasicoherentOnSite_kerSubmodule {M N : SheafOfModules.{u}
      (structureRingSheaf s.site s.base s.containsBase s.space)} (φ : M ⟶ N)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) :
    (Stacks.SheafOfModules.kerSubmodule φ).toSheafOfModules.IsQuasicoherentOnSite :=
  let : CategoryTheory.ObjectProperty.IsClosedUnderKernels
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureRingSheaf s.site s.base s.containsBase s.space)) :=
    AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_smallEtale
      s.site s.base s.containsBase s.space.1 s.space.2
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Stacks.SheafOfModules.isLimitKernelForkKerSubmodule φ).conePointUniqueUpToIso
      (kernelIsKernel φ)).symm
    (CategoryTheory.ObjectProperty.prop_kernel _ φ hM hN)

/-- **`ℐ_n` is quasi-coherent** (Stacks 085L), for `π` quasi-compact and `i` a closed
immersion. -/
theorem isQuasicoherentOnSite_psiKernelPiece
    (hπ : IsQuasiCompact s.site s.base s.containsBase s.π.hom)
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom) :
    ∀ n : ℤ, (psiKernelPiece s Px i ψ n).toSheafOfModules.IsQuasicoherentOnSite
  | Int.ofNat d => isQuasicoherentOnSite_kerSubmodule s _ (s.isQuasicoherent (d : ℤ))
      (isQuasicoherentOnSite_psiKernelTarget s Px i hπ hi d)
  | Int.negSucc k => isQuasicoherentOnSite_kerSubmodule s _ (s.isQuasicoherent (Int.negSucc k))
      (s.isQuasicoherent (Int.negSucc k))

end Kernel

section Chart

variable (s : RelativeProjSituation.{u, u})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (ψ : ∀ d : ℕ, (s.psiSourceQcoh (d : ℤ)).obj ⟶ (s.twistModule Px (d : ℤ)).obj)
  (hψ : ∀ d : ℕ, (modulePullback s.site s.base s.containsBase (presentationAtlas
      (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))).map
      (ψ d) ≫ (s.twistModuleChartIso Px (d : ℤ)).hom = s.psiChartHomOfAdjoint Px d)

/-- A local section of `𝒜` in a negative degree vanishes. -/
theorem algebra_piece_eq_zero_of_neg {n : ℤ} (hn : n < 0)
    (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (x : (s.algebra.piece n).val.obj V) : x = 0 :=
  SheafOfModules.eq_zero_of_isZero (s.negative_isZero n hn) V x

include hψ in
/-- **The chart dictionary for `ℐ`**: at the atlas `u : U ⟶ X`, a local section `a` of
`(u^*𝒜)_n` over a Zariski open `W`, `n ≥ 0`, lies in the graded ideal of Stacks 0801 of
`Z ×_X U ⊆ Proj_U(u^*𝒜)` exactly when its reading on the chart `W ⟶ U ⟶ X` lies in `ℐ_n`. -/
theorem mem_twistKerGradedIdeal_iff_mem_psiKernelPiece
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
    [AlgebraicGeometry.QuasiCompact (relativeProj
      (s.relativeProjPoints.algebra Px.U Px.toSpace)).toBase] (n : ℕ)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) Px.toSpace).hom)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj Px.U).Opens)
    (a : Γ((s.relativeProjPoints.algebra Px.U Px.toSpace).piece (n : ℤ), W)) :
    a ∈ ((Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal
        (s.relativeProjPoints.algebra Px.U Px.toSpace)
        (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
        (RelativeProjSituation.chartClosedSubscheme i hi Px.U Px.toSpace)).piece
          (n : ℤ)).toSubmodule.obj (op W) ↔
      s.etalePointReading Px.toSpace hf (n : ℤ) W a ∈
        (psiKernelPiece s Px i ψ (n : ℤ)).obj (op (s.etalePointChart Px.toSpace hf W)) :=
  (mem_twistKerGradedIdeal_iff_psiKernelMap s Px i hi n (ψ n) (hψ n) hf W a).trans
    (mem_psiKernelPiece_iff s Px i ψ n (op (s.etalePointChart Px.toSpace hf W))
      (s.etalePointReading Px.toSpace hf (n : ℤ) W a)).symm

include hψ in
/-- **The chart dictionary for `ℐ`**, in every degree: at the atlas `u : U ⟶ X`, a local section
`a` of `(u^*𝒜)_n` over a Zariski open `W` lies in the graded ideal of Stacks 0801 of
`Z ×_X U ⊆ Proj_U(u^*𝒜)` exactly when its reading on the chart `W ⟶ U ⟶ X` lies in `ℐ_n`. -/
theorem mem_twistKerGradedIdeal_iff_mem_psiKernelPiece_int
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
    [AlgebraicGeometry.QuasiCompact (relativeProj
      (s.relativeProjPoints.algebra Px.U Px.toSpace)).toBase] (n : ℤ)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) Px.toSpace).hom)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj Px.U).Opens)
    (a : Γ((s.relativeProjPoints.algebra Px.U Px.toSpace).piece n, W)) :
    a ∈ ((Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal
        (s.relativeProjPoints.algebra Px.U Px.toSpace)
        (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
        (RelativeProjSituation.chartClosedSubscheme i hi Px.U Px.toSpace)).piece
          n).toSubmodule.obj (op W) ↔
      s.etalePointReading Px.toSpace hf n W a ∈
        (psiKernelPiece s Px i ψ n).obj (op (s.etalePointChart Px.toSpace hf W)) := by
  rcases lt_or_ge n 0 with hn | hn
  · have ha : a = 0 := Stacks.SheafOfModules.eq_zero_of_isZero
      ((s.relativeProjPoints.algebra Px.U Px.toSpace).negative_isZero n hn) (op W) a
    obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero hn
    refine ⟨fun _ => mem_psiKernelPiece_negSucc s Px i ψ k _ _, fun _ => ?_⟩
    rw [ha]
    exact Submodule.zero_mem _
  · obtain ⟨d, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact mem_twistKerGradedIdeal_iff_mem_psiKernelPiece s Px i ψ hψ hi d hf W a

include hψ in
/-- **`ℐ` is stable under right multiplication on the charts of the atlas**: on the chart
`W ⟶ U ⟶ X`, the product of a local section of `ℐ_p` with a local section of `𝒜_q` lies in
`ℐ_{p + q}`. -/
theorem psiKernelPiece_mul_mem_right_chart
    (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)
    [AlgebraicGeometry.QuasiCompact (relativeProj
      (s.relativeProjPoints.algebra Px.U Px.toSpace)).toBase]
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) Px.toSpace).hom)
    (hrep : yoneda.relativelyRepresentable (pointHom (X := s.space) Px.toSpace).hom)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj Px.U).Opens) (p q : ℤ)
    {x : (s.algebra.piece p).val.obj (op (s.etalePointChart Px.toSpace hf W))}
    (hx : x ∈ (psiKernelPiece s Px i ψ p).obj (op (s.etalePointChart Px.toSpace hf W)))
    (b : (s.algebra.piece q).val.obj (op (s.etalePointChart Px.toSpace hf W))) :
    (s.algebra.mul p q).app (op (s.etalePointChart Px.toSpace hf W)) x b ∈
      (psiKernelPiece s Px i ψ (p + q)).obj (op (s.etalePointChart Px.toSpace hf W)) := by
  obtain ⟨x', rfl⟩ := (s.etalePointReading Px.toSpace hf p W).surjective x
  obtain ⟨b', rfl⟩ := (s.etalePointReading Px.toSpace hf q W).surjective b
  rw [← etalePointReading_mul s Px.toSpace hf hrep p q W x' b']
  have hx' := (mem_twistKerGradedIdeal_iff_mem_psiKernelPiece_int s Px i ψ hψ hi p hf W x').2 hx
  exact (mem_twistKerGradedIdeal_iff_mem_psiKernelPiece_int s Px i ψ hψ hi (p + q) hf W _).1
    ((Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal
      (s.relativeProjPoints.algebra Px.U Px.toSpace)
      (Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra _)
      (RelativeProjSituation.chartClosedSubscheme i hi Px.U Px.toSpace)).mul_mem p q W hx' b')

end Chart


end AlgebraicGeometry.Space.C1359Bridge

end
