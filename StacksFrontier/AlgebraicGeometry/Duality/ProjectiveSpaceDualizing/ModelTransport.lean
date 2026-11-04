module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceDualizing.TwistSum
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeAffineBase
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartQcoh
public import StacksFrontier.CategoryTheory.Triangulated.Generators

/-!
# Carrying the twists of the `Proj` model of projective space to `ℙⁿ_S`

Over an affine base `S` with ring of global functions `A = Γ(S, ⊤)`, projective space has two
models in this library: the homogeneous spectrum `P = Proj A[T₀, …, Tₙ]`, on which the generator
`𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)` of [Stacks, Tag 0A9V] is stated, and the base change `X = ℙⁿ_S`, on
which the dualizing complex of [Stacks, Tag 0A9W] is computed. They are identified by the
isomorphism `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.projCompare`, which carries
the twists to the twists. This file transports along it:

* derived direct image along an isomorphism of schemes is an equivalence
  `D_QCoh(𝒪_P) ≌ D_QCoh(𝒪_X)`, compatible with the shift;
* along an affine morphism it carries a quasi-coherent module placed in a single degree to its
  direct image placed in the same degree;
* so the equivalence carries `⨁_{0 ≤ k ≤ n} 𝒪_P(-k)` to the object
  `Stacks.Duality.ProjectiveSpaceDualizing.twistGenerator` of `D_QCoh(𝒪_X)`;
* and a weak generator of a triangulated category is carried by an equivalence commuting with the
  shift to a weak generator.

## Main results

* `Stacks.Duality.ProjectiveSpaceDualizing.isWeakTriangulatedGenerator_of_equivalence`: weak
  generators ([Stacks, Tag 09SJ]) are transported along equivalences commuting with the shift.
* `Stacks.Duality.ProjectiveSpaceDualizing.derivedPushforwardSingleIsoOfIsAffineHom`:
  `Rf_*(ℱ[a]) ≅ (f_*ℱ)[a]` for `f` affine and `ℱ` quasi-coherent.
* `Stacks.Duality.ProjectiveSpaceDualizing.quasiCoherentDerivedPushforwardEquivOfIsIso`: derived
  direct image along an isomorphism of quasi-compact schemes is an equivalence of the
  quasi-coherent derived categories.
* `Stacks.Duality.ProjectiveSpaceDualizing.projCompareTwistGeneratorIso`: that equivalence, for
  the comparison `Proj A[T₀, …, Tₙ] ≅ ℙⁿ_S`, carries `⨁_{0 ≤ k ≤ n} 𝒪(-k)` to `twistGenerator`.

## References

* [Stacks Project, Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe w u

namespace Stacks.Duality.ProjectiveSpaceDualizing

/-! ### Weak generators along an equivalence -/

/-- **Weak generators are transported along an equivalence commuting with the shift.** If `G`
is a weak generator of `C` ([Stacks, Tag 09SJ]) and an equivalence `E : C ≌ D` commuting with the
shift carries `G` to `G'`, then `G'` is a weak generator of `D`. -/
theorem isWeakTriangulatedGenerator_of_equivalence {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ] (E : C ≌ D)
    [E.functor.CommShift ℤ] {G : C} {G' : D} (e : E.functor.obj G ≅ G')
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton G').IsWeakTriangulatedGenerator := by
  intro K hK
  have hz : IsZero (E.inverse.obj K) := by
    refine hG _ fun Y f hY => ?_
    obtain ⟨Z, a, eY, hZ⟩ := hY
    obtain rfl := (ObjectProperty.singleton_iff _ _).1 hZ
    have hY' : (ObjectProperty.singleton G').shiftClosure ℤ (E.functor.obj Y) :=
      ⟨G', a, E.functor.mapIso eY ≪≫ (E.functor.commShiftIso a).app G ≪≫
        (shiftFunctor D a).mapIso e, (ObjectProperty.singleton_iff _ _).2 rfl⟩
    have h0 := hK (E.functor.map f ≫ E.counitIso.hom.app K) hY'
    have h1 : E.functor.map f = 0 := by
      simpa using congrArg (· ≫ E.counitIso.inv.app K) h0
    exact E.functor.map_injective (h1.trans (E.functor.map_zero _ _).symm)
  exact (E.functor.map_isZero hz).of_iso (E.counitIso.app K).symm

/-! ### Derived direct image along an affine morphism and along an isomorphism -/

/-- **`Rf_*(ℱ[a]) ≅ (f_*ℱ)[a]` for an affine morphism `f` and a quasi-coherent module `ℱ`**: the
higher direct images of `ℱ` vanish ([Stacks, Tag 01XC]), so `Rf_*(ℱ[a])` has cohomology only in
degree `a`, where it is `R⁰f_*ℱ = f_*ℱ`. -/
def derivedPushforwardSingleIsoOfIsAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules] (F : X.Modules)
    [F.IsQuasicoherent] (a : ℤ) :
    (derivedPushforward f).obj ((DerivedCategory.singleFunctor _ a).obj F) ≅
      (DerivedCategory.singleFunctor Y.Modules a).obj ((Scheme.Modules.pushforward f).obj F) :=
  isoSingleOfConcentrated _ a _
    (fun q hq => isZero_homology_derivedPushforward_single f F a q fun k hk =>
      Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward f F k (by omega))
    ((Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso f a a 0
        (by simp)).app F ≪≫
      (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso f).app F)

section Equivalence

variable {P X : Scheme.{u}} (φ : P ⟶ X) [IsIso φ] [CompactSpace P] [CompactSpace X]

/-- `Rφ_* ⋙ Rψ_* ≅ 𝟭` on `D(𝒪_P)` when `φ ≫ ψ = 𝟙`. -/
def derivedPushforwardCompIsoIdOfEq {Q : Scheme.{u}} (φ : P ⟶ Q) (ψ : Q ⟶ P) (h : φ ≫ ψ = 𝟙 P) :
    derivedPushforward φ ⋙ derivedPushforward ψ ≅ 𝟭 (DerivedCategory P.Modules) :=
  derivedPushforwardCompIso φ ψ ≪≫
    eqToIso (congrArg (fun g : P ⟶ P => derivedPushforward g) h) ≪≫ derivedPushforwardIdIso P

/-- A natural isomorphism of functors on `D(𝒪)`, given objectwise on the quasi-coherent derived
categories, is a natural isomorphism of the functors on `D_QCoh`. -/
def quasiCoherentNatIso {Z Z' : Scheme.{u}}
    {F G : quasiCoherentDerivedCategory Z ⥤ quasiCoherentDerivedCategory Z'}
    (e : ∀ K, (F.obj K).obj ≅ (G.obj K).obj)
    (he : ∀ {K L} (g : K ⟶ L), (ObjectProperty.ι _).map (F.map g) ≫ (e L).hom =
      (e K).hom ≫ (ObjectProperty.ι _).map (G.map g)) : F ≅ G :=
  NatIso.ofComponents (fun K => ObjectProperty.isoMk _ (e K))
    fun g => (ObjectProperty.fullyFaithfulι _).map_injective (by simpa using he g)

/-- The composite of the derived direct images along `φ` and `ψ` with `φ ≫ ψ = 𝟙` is the identity
of `D_QCoh(𝒪_P)`. -/
def quasiCoherentDerivedPushforwardCompIsoIdOfEq {Q : Scheme.{u}} (φ : P ⟶ Q) (ψ : Q ⟶ P)
    [QuasiCompact φ] [QuasiSeparated φ] [CompactSpace Q] [QuasiCompact ψ] [QuasiSeparated ψ]
    (h : φ ≫ ψ = 𝟙 P) :
    quasiCoherentDerivedPushforward φ (isQuasicoherent_homology_derivedPushforward_of_qcqs φ) ⋙
      quasiCoherentDerivedPushforward ψ (isQuasicoherent_homology_derivedPushforward_of_qcqs ψ) ≅
        𝟭 (quasiCoherentDerivedCategory P) :=
  quasiCoherentNatIso (F := quasiCoherentDerivedPushforward φ _ ⋙
      quasiCoherentDerivedPushforward ψ _) (G := 𝟭 _)
    (fun K => (derivedPushforwardCompIsoIdOfEq φ ψ h).app K.obj)
    fun g => (derivedPushforwardCompIsoIdOfEq φ ψ h).hom.naturality ((ObjectProperty.ι _).map g)

/-- **Derived direct image along an isomorphism of quasi-compact schemes is an equivalence**
`D_QCoh(𝒪_P) ≌ D_QCoh(𝒪_X)`, with inverse derived direct image along the inverse. -/
def quasiCoherentDerivedPushforwardEquivOfIsIso :
    quasiCoherentDerivedCategory P ≌ quasiCoherentDerivedCategory X :=
  CategoryTheory.Equivalence.mk
    (quasiCoherentDerivedPushforward φ (isQuasicoherent_homology_derivedPushforward_of_qcqs φ))
    (quasiCoherentDerivedPushforward (inv φ)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (inv φ)))
    (quasiCoherentDerivedPushforwardCompIsoIdOfEq φ (inv φ) (IsIso.hom_inv_id φ)).symm
    (quasiCoherentDerivedPushforwardCompIsoIdOfEq (inv φ) φ (IsIso.inv_hom_id φ))

end Equivalence

/-! ### The comparison of the two models carries the twists to the twists -/

section ProjModel

open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage (projCompare
  nonempty_pushforward_twistingSheaf_iso)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (m : ℕ) (S : Scheme.{u}) [IsAffine S]

/-- **The comparison of the two models of projective space carries `⨁_{0 ≤ k ≤ n} 𝒪(-k)` to
`twistGenerator`.** Over an affine `S` with `A = Γ(S, ⊤)`, derived direct image along
`projCompare : Proj A[T₀, …, Tₙ] ≅ ℙⁿ_S` sends the direct sum of the twists `𝒪(-k)`, `0 ≤ k ≤ n`,
of the homogeneous-spectrum model, placed in degree zero, to the same direct sum on `ℙⁿ_S`: the
comparison is affine, so derived direct image of a quasi-coherent module placed in degree zero is
its direct image placed in degree zero, and the direct image of `𝒪(d)` is `𝒪(d)`
(`nonempty_pushforward_twistingSheaf_iso` in
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`). -/
def projCompareTwistGeneratorIso :
    (quasiCoherentDerivedPushforwardEquivOfIsIso
        (projCompare (m + 1) S)).functor.obj
      ⟨⨁ fun k : Fin (m + 2) =>
          (DerivedCategory.singleFunctor (AlgebraicGeometry.Proj
            (Stacks.ProjectiveCohomology.polyGrading ↥(Γ(S, ⊤)) (m + 1))).Modules 0).obj
            (ProjectiveSpectrum.Proj.twistingSheaf
              (Stacks.ProjectiveCohomology.polyGrading ↥(Γ(S, ⊤)) (m + 1)) (-(k : ℤ))),
        derivedCategoryB_biproduct_singleFunctor _ fun _k =>
          Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_twistingSheaf _ _⟩ ≅
      twistGenerator m S :=
  ObjectProperty.isoMk _ <|
    (derivedPushforward
        (projCompare (m + 1) S)).mapBiproduct _ ≪≫
      biproduct.mapIso fun k =>
        haveI := Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_twistingSheaf
          (Stacks.ProjectiveCohomology.polyGrading ↥(Γ(S, ⊤)) (m + 1)) (-(k : ℤ))
        derivedPushforwardSingleIsoOfIsAffineHom _ _ 0 ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            (nonempty_pushforward_twistingSheaf_iso (m + 1) S (-(k : ℤ))).some

end ProjModel

end Stacks.Duality.ProjectiveSpaceDualizing

end
