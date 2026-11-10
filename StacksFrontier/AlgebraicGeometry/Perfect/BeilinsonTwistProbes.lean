module

public import StacksFrontier.AlgebraicGeometry.Perfect.BeilinsonCoherentCharacterization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Associativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatSingleTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.FlatPullbackTensorSingle
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.InvertibleTwistDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.Extensions.ExtFromStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpaceDirectImage.TwistCohomology
public import StacksFrontier.CategoryTheory.Triangulated.ProbeKilling

/-!
# Twisting by `𝒪(d)` on `D(𝒪_{ℙⁿ_k})`, and the twists as probes

Let `k` be a field and `X = ℙⁿ_k`. This file supplies the input that the proof of
(4) ⟹ (1) of [Stacks, Tag 0FYB] draws from the geometry of `X`, in the shape that
`Stacks.Triangulated.ProbeKilling.mem_of_probes` consumes.

* Tensoring with `𝒪(d)[0]`, `K ↦ K ⊗^𝐋 𝒪(d)`, is an autoequivalence of `D(𝒪_X)`, with inverse
  tensoring with `𝒪(-d)[0]`: the associativity and unit constraints of the derived tensor
  product of [Stacks, Tag 06YU] and `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` ([Stacks, Tag 01MU]).
* The twist `𝒪(-a)[0]`, measured through `- ⊗^𝐋 𝒪(a)` from `𝒪_X[0]`, is a probe whose measured
  morphism spaces `Hom(𝒪_X[0], (K ⊗^𝐋 𝒪(a))[i]) = H^i(X, K ⊗^𝐋 𝒪(a))` are exactly the ones in
  condition (4) of [Stacks, Tag 0FYB].
* `Hom(𝒪_X[0], 𝒪(e)[0][i]) = H^i(X, 𝒪(e))` ([Stacks, Tag 01XT]) vanishes for `-n ≤ e ≤ -1` in
  every degree, and for `e = 0` outside degree `0`: this is the semi-orthogonality of
  `𝒪(-n), …, 𝒪` and the exceptionality of each twist.
* Every nonzero endomorphism of `𝒪_X[0]` is invertible, global functions on `ℙⁿ_k` being the
  field `k`.

## Main definitions

* `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.twistSingle`: `𝒪(d)` in degree
  zero.
* `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.tensorTwist`: `- ⊗^𝐋 𝒪(d)[0]`.
* `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.tensorTwistEquiv`: the
  autoequivalence it is.
* `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.twistProbe`: the probe of `𝒪(-a)`.

## References

* [Stacks Project, Tag 0FYB](https://stacks.math.columbia.edu/tag/0FYB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.Triangulated.ProbeKilling

namespace Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

universe u

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] opensSheafTensorAdditive opensSheafTensorObjAdditive
  opensHasMapBifunctorSheafTensor

variable (k : Type u) [Field k] (n : ℕ)

/-- The standard model of `D(𝒪_X)`, at the spelling of the ringed-site development of
[Stacks, Tag 06YU]. The type is `X.Modules` by `rfl`, but an instance found at one spelling does
not fire at the other. -/
local instance hasDerivedCategoryProjSiteModules :
    HasDerivedCategory (Stacks.DerivedTensor.RingedSite.Modules (projSpaceSite k n).O) :=
  HasDerivedCategory.standard _

/-- The same, at the spelling of the monoidal development of [Stacks, Tag 0FPT]. -/
local instance hasDerivedCategoryProjSiteMod :
    HasDerivedCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod (projSpaceSite k n).O) :=
  HasDerivedCategory.standard _

/-! ### The twists in degree zero -/

/-- The twist `𝒪(d)` of `ℙⁿ_k`, placed in cohomological degree zero. -/
abbrev twistSingle (d : ℤ) :
    DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules :=
  (DerivedCategory.singleFunctor _ 0).obj (twistOver n (Spec (CommRingCat.of k)) d)

/-- Each twist is flat, being invertible. -/
theorem isFlat_twistOver (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := (projSpaceSite k n).O)
      (twistOver n (Spec (CommRingCat.of k)) d) :=
  Stacks.AmpleNonvanishing.isFlat_of_isInvertibleModule _ _

/-- The single complex of a twist is K-flat. -/
theorem kFlat_single_twistOver (d : ℤ) :
    Stacks.SheafOfModules.KFlat (projSpaceSite k n).O
      ((CochainComplex.singleFunctor _ 0).obj (twistOver n (Spec (CommRingCat.of k)) d)) :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.kFlat_single _ _ (isFlat_twistOver k n d)

/-- **`𝒪(a)[0] ⊗^𝐋 𝒪(b)[0] ≅ 𝒪(a + b)[0]`.** Both factors are K-flat, so the derived tensor
product is the total tensor complex, which for two single complexes is the single complex of the
tensor product, and `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` is [Stacks, Tag 01MU]. -/
def twistSingleTensorIso (a b : ℤ) :
    ((projDerivedTensor k n).tensor.obj (twistSingle k n a)).obj (twistSingle k n b) ≅
      twistSingle k n (a + b) :=
  ((projDerivedTensor k n).tensor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _)).app _ ≪≫
    ((projDerivedTensor k n).tensor.obj _).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
    (projDerivedTensor k n).comparison _ _ (kFlat_single_twistOver k n a)
      (kFlat_single_twistOver k n b) ≪≫
    DerivedCategory.Q.mapIso (Stacks.Duality.tensorComplexSingleSingleIso _ _ _ 0) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (projectiveSpaceOverRing n (CommRingCat.of k)).Modules 0).app _).symm ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (ProjTwistTensorPow.twistOverMulIso n (Spec (CommRingCat.of k)) a b)

/-- **`𝒪(0)[0]` is the unit of the derived tensor product**, `𝒪_X[0]`. -/
def twistSingleZeroIso :
    twistSingle k n 0 ≅ Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
    (ProjTwistTensorPow.twistZeroIsoUnit n (Spec (CommRingCat.of k)))

/-- Equal degrees give isomorphic twists. -/
def twistSingleCongr {a b : ℤ} (h : a = b) : twistSingle k n a ≅ twistSingle k n b :=
  eqToIso (by rw [h])

/-! ### Tensoring with a twist -/

/-- **`K ↦ K ⊗^𝐋 𝒪(d)[0]`**, the derived tensor product of [Stacks, Tag 06YU] with the twist
`𝒪(d)` on the right. -/
abbrev tensorTwist (d : ℤ) :
    DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules ⥤
      DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules :=
  (projDerivedTensor k n).tensor.flip.obj (twistSingle k n d)

/-- Tensoring with a fixed object on the right commutes with the shifts: the `commShift_left`
datum of the derived tensor product, stated at the ringed site of `ℙⁿ_k` so that instance search
does not have to recover that site from its structure sheaf. -/
instance tensorTwist_commShift (d : ℤ) : (tensorTwist k n d).CommShift ℤ :=
  (projDerivedTensor k n).commShift_left (twistSingle k n d)

/-- Tensoring with a fixed object on the right is exact ([Stacks, Tag 06YU]). -/
instance tensorTwist_isTriangulated (d : ℤ) : (tensorTwist k n d).IsTriangulated :=
  (projDerivedTensor k n).exact_left (twistSingle k n d)

/-- **Twisting twice is twisting once**: `(K ⊗ 𝒪(a)) ⊗ 𝒪(b) ≅ K ⊗ 𝒪(a + b)`, naturally in `K`,
by the associativity constraint and `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`. -/
def tensorTwistCompIso (a b : ℤ) :
    tensorTwist k n a ⋙ tensorTwist k n b ≅ tensorTwist k n (a + b) :=
  NatIso.ofComponents
    (fun K => Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator
        (projSpaceSite k n).O (projDerivedTensor k n) K (twistSingle k n a) (twistSingle k n b) ≪≫
      ((projDerivedTensor k n).tensor.obj K).mapIso (twistSingleTensorIso k n a b))
    (fun {K K'} f => by
      have h1 := Stacks.SheafOfModules.DerivedMonoidal.derivedTensorAssociator_naturality_left
        (projSpaceSite k n).O (projDerivedTensor k n) f (twistSingle k n a) (twistSingle k n b)
      have h2 := ((projDerivedTensor k n).tensor.map f).naturality
        (twistSingleTensorIso k n a b).hom
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) h1).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) h2.symm).trans ?_
      exact (Category.assoc _ _ _).symm)

/-- **Twisting by `𝒪(0)` is the identity**, by the unit constraint. -/
def tensorTwistZeroIso : tensorTwist k n 0 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun K => ((projDerivedTensor k n).tensor.obj K).mapIso (twistSingleZeroIso k n) ≪≫
      Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso (projSpaceSite k n)
        (projDerivedTensor k n) K)
    (fun {K K'} f => by
      have h1 := ((projDerivedTensor k n).tensor.map f).naturality (twistSingleZeroIso k n).hom
      have h2 := Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality
        (projSpaceSite k n) (projDerivedTensor k n) f
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ _) h1.symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (_ ≫ ·) h2).trans ?_
      exact (Category.assoc _ _ _).symm)

/-- Equal degrees give isomorphic twisting functors. -/
def tensorTwistCongr {a b : ℤ} (h : a = b) : tensorTwist k n a ≅ tensorTwist k n b :=
  eqToIso (by rw [h])

/-- **Tensoring with `𝒪(d)[0]` is an autoequivalence of `D(𝒪_X)`**, with quasi-inverse tensoring
with `𝒪(-d)[0]`. -/
def tensorTwistEquiv (d : ℤ) :
    DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules ≌
      DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules :=
  CategoryTheory.Equivalence.mk (tensorTwist k n d) (tensorTwist k n (-d))
    ((tensorTwistZeroIso k n).symm ≪≫ tensorTwistCongr k n (by ring) ≪≫
      (tensorTwistCompIso k n d (-d)).symm)
    (tensorTwistCompIso k n (-d) d ≪≫ tensorTwistCongr k n (by ring) ≪≫ tensorTwistZeroIso k n)

/-! ### The twists as probes -/

/-- **The probe of `𝒪(-a)[0]`**: it is measured through `- ⊗^𝐋 𝒪(a)[0]` from `𝒪_X[0]`, which it
is carried to. -/
def twistProbe (a : ℤ) :
    Probe (DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) where
  P := twistSingle k n (-a)
  U := Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n)
  G := tensorTwist k n a
  ff := (tensorTwistEquiv k n a).fullyFaithfulFunctor
  ι := twistSingleTensorIso k n (-a) a ≪≫ twistSingleCongr k n (by ring) ≪≫ twistSingleZeroIso k n

end Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

end
