module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Linear
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ConvolutionPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.ProjectiveSpacePerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityPairingCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
public import StacksFrontier.AlgebraicGeometry.Perfect.BeilinsonCoherentCharacterization
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace

/-!
# A Fourier–Mukai transform carries condition (2) of [Stacks, Tag 0FYD] to finite total `Hom`

Let `k` be a field, let `X` and `Y` be schemes over `k` with `Y ⟶ Spec k` flat, proper and of
finite presentation, write `p : X ×_k Y ⟶ X` and `q : X ×_k Y ⟶ Y` for the projections, and let
`E'` be a perfect object of `D(𝒪_{X ×_k Y})`. Let `K ∈ D_QCoh(𝒪_X)` satisfy condition (2) of
[Stacks, Tag 0FYD]: `∑_i dim_k Ext^i_X(E, K) < ∞` for every perfect `E` on `X`. This file proves
that the Fourier–Mukai transform `M = Φ_{E'}(K) = Rq_*(Lp^*K ⊗^𝐋 E')` has finite total `Hom`
from every perfect object `A` of `D(𝒪_Y)`, and in particular from each member of the exceptional
sequence `𝒪(-m), …, 𝒪` when `Y = ℙᵐ_k`. That is the step of the proof of (2) ⇒ (1) of
[Stacks, Tag 0FYD] that passes from `X` to projective space.

## The computation

For `T ∈ D_QCoh(𝒪_X)` there is a `k`-linear bijection

`Hom_Y(A, Φ_{E'}(T)) ≅ Hom_X(E, T)`,  `E = (Rp_*(E' ⊗^𝐋 (Lq^*A)^∨))^∨`,

obtained as the composite of
* the adjunction `Lq^* ⊣ Rq_*` ([Stacks, Tag 079W]);
* `Hom(L, N) = Hom(𝒪, N ⊗^𝐋 L^∨)` for the perfect `L = Lq^*A` ([Stacks, Tags 0FPC, 08DQ]);
* the associativity and commutativity of `⊗^𝐋` ([Stacks, Tag 0FPB]), bringing
  `(Lp^*T ⊗ E') ⊗ (Lq^*A)^∨` to `(E' ⊗ (Lq^*A)^∨) ⊗ Lp^*T`;
* `Lp^*𝒪_X = 𝒪` and the adjunction `Lp^* ⊣ Rp_*`;
* the projection formula `Rp_*Q ⊗^𝐋 T ≅ Rp_*(Q ⊗^𝐋 Lp^*T)` ([Stacks, Tag 08EU]), which is where
  `T` has to have quasi-coherent cohomology;
* biduality `F ≅ F^∨∨` and `Hom(𝒪, T ⊗ F^∨∨) = Hom(F^∨, T)` for the perfect `F = Rp_*(Q)`
  ([Stacks, Tags 08DQ, 0FPC]).
Every step is `k`-linear: the adjunction bijections because `Rq_*`, `Rp_*` are, and the duality
bijections because `- ⊗^𝐋 L^∨` is (`AlgebraicGeometry.derivedPushforward_linear`,
`AlgebraicGeometry.derivedTensor_flip_obj_linear`). The object `E` is perfect: `Lq^*A` by
[Stacks, Tag 09UA], duals by [Stacks, Tag 08DQ], tensor products by [Stacks, Tag 09J5] and
`Rp_*` because `p` is a base change of `Y ⟶ Spec k` ([Stacks, Tag 0B91] (1)). Applied at
`T = K[i]` this gives `Hom(A, M[i]) ≅ Ext^i_X(E, K)`, and condition (2) at `E` finishes.

## Main results

* `Stacks.AlgebraicGeometry.FourierMukaiFiniteHom.homFourierMukaiLinearEquiv`: the bijection.
* `Stacks.AlgebraicGeometry.FourierMukaiFiniteHom.hasFiniteTotalHom_fourierMukai_of_isPerfect`:
  finite total `Hom` from any perfect `A`.
* `Stacks.AlgebraicGeometry.FourierMukaiFiniteHom.hasFiniteTotalHom_seqE_fourierMukai`: the case
  `Y = ℙᵐ_k`, `A = 𝒪(a - m)`, in exactly the shape of the hypothesis `hC` of
  `AlgebraicGeometry.CoherentConverse.derivedCategoryBBounded_of_fourierMukai`.

## Implementation notes

Everything is at the standard model of the derived categories, where the Fourier–Mukai functor
and the duality of perfect objects are stated. Two monoidal structures on `D(𝒪_W)` occur:
`Stacks.SheafOfModules.derivedMonoidalStructure`, in which the dual of a perfect object is an
exact pairing, and `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, whose tensor
product is the derived tensor product `tens W` of the Fourier–Mukai functor on the nose. The
duality bijection is proved in the abstract (`dualHomEquivOf`) for a monoidal category with its
tensor product read through an isomorphism with a bifunctor, and instantiated at the first
structure with `Stacks.SheafOfModules.derivedTensorCanonicalIso`; the associativity and
commutativity used are those of the second.

## References

* [Stacks Project, Tag 0FYD](https://stacks.math.columbia.edu/tag/0FYD)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory

universe u

namespace Stacks.AlgebraicGeometry.FourierMukaiFiniteHom

section Abstract

variable {D : Type*} [Category D] [MonoidalCategory D] {T : D ⥤ D ⥤ D}
  (τ : curriedTensor D ≅ T)

/-- `Hom(L, N) ≃ Hom(𝟙, N ⊗ L')` for an exact pairing `(L, L')`, with the tensor product read
through an isomorphism `τ` with a bifunctor `T`. -/
def dualHomEquivOf (L L' N : D) [ExactPairing L L'] : (L ⟶ N) ≃ (𝟙_ D ⟶ (T.obj N).obj L') :=
  ((λ_ L).symm.homFromEquiv).trans
    ((tensorRightHomEquiv (𝟙_ D) L L' N).trans ((τ.app N).app L').homToEquiv)

/-- `dualHomEquivOf` is natural in the target. -/
theorem dualHomEquivOf_comp {L L' N N' : D} [ExactPairing L L'] (f : L ⟶ N) (g : N ⟶ N') :
    dualHomEquivOf τ L L' N' (f ≫ g) = dualHomEquivOf τ L L' N f ≫ (T.map g).app L' := by
  have h1 : tensorRightHomEquiv (𝟙_ D) L L' N' ((λ_ L).hom ≫ f ≫ g) =
      tensorRightHomEquiv (𝟙_ D) L L' N ((λ_ L).hom ≫ f) ≫ g ▷ L' :=
    (congrArg _ (Category.assoc _ _ _).symm).trans (tensorRightHomEquiv_naturality _ _)
  have h2 : g ▷ L' ≫ ((τ.app N').app L').hom = ((τ.app N).app L').hom ≫ (T.map g).app L' :=
    NatTrans.naturality_app τ.hom L' g
  show tensorRightHomEquiv (𝟙_ D) L L' N' ((λ_ L).hom ≫ f ≫ g) ≫ ((τ.app N').app L').hom =
    (tensorRightHomEquiv (𝟙_ D) L L' N ((λ_ L).hom ≫ f) ≫ ((τ.app N).app L').hom) ≫
      (T.map g).app L'
  rw [h1, Category.assoc, h2, Category.assoc]

/-- `dualHomEquivOf` is postcomposition with a fixed morphism followed by `- ⊗ L'`. -/
theorem dualHomEquivOf_eq {L L' N : D} [ExactPairing L L'] (f : L ⟶ N) :
    dualHomEquivOf τ L L' N f = dualHomEquivOf τ L L' L (𝟙 L) ≫ (T.flip.obj L').map f := by
  simpa using dualHomEquivOf_comp τ (𝟙 L) f

/-- `dualHomEquivOf` is `k`-linear when `- ⊗ L'` is. -/
def dualHomLinearEquivOf (k : Type*) [Semiring k] [Preadditive D] [Linear k D]
    (L L' N : D) [ExactPairing L L'] [(T.flip.obj L').Additive] [(T.flip.obj L').Linear k] :
    (L ⟶ N) ≃ₗ[k] (𝟙_ D ⟶ (T.obj N).obj L') where
  toEquiv := dualHomEquivOf τ L L' N
  map_add' f g := by
    change dualHomEquivOf τ L L' N (f + g) =
      dualHomEquivOf τ L L' N f + dualHomEquivOf τ L L' N g
    rw [dualHomEquivOf_eq τ (f + g), dualHomEquivOf_eq τ f, dualHomEquivOf_eq τ g,
      Functor.map_add, Preadditive.comp_add]
  map_smul' r f := by
    change dualHomEquivOf τ L L' N (r • f) = r • dualHomEquivOf τ L L' N f
    rw [dualHomEquivOf_eq τ (r • f), dualHomEquivOf_eq τ f, Functor.map_smul, Linear.comp_smul]

end Abstract

section AdjunctionLinear

variable (k : Type*) [Semiring k] {C D : Type*} [Category C] [Category D] [Preadditive C]
  [Preadditive D] [Linear k C] [Linear k D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [G.Additive] [G.Linear k]

/-- The bijection of an adjunction is `k`-linear when the right adjoint is. -/
def adjHomLinearEquiv (A : C) (B : D) : (F.obj A ⟶ B) ≃ₗ[k] (A ⟶ G.obj B) where
  toEquiv := adj.homEquiv A B
  map_add' f g := by
    change adj.homEquiv A B (f + g) = adj.homEquiv A B f + adj.homEquiv A B g
    simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add]
  map_smul' r f := by
    change adj.homEquiv A B (r • f) = r • adj.homEquiv A B f
    simp only [Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul]

end AdjunctionLinear

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

open Stacks.Cohomology.PerfectComplexes (IsPerfect)

section Scheme

variable (W : Scheme.{u})

/-- The structure sheaf placed in degree zero, `𝒪_W[0]`. -/
noncomputable abbrev unitD : DerivedCategory W.Modules :=
  (DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf)

/-- The derived tensor product of [Stacks, Tag 06YU] on `D(𝒪_W)`, the one Fourier–Mukai functors
and the projection formula of [Stacks, Tag 08EU] are stated with. -/
noncomputable abbrev tens :
    DerivedCategory W.Modules ⥤ DerivedCategory W.Modules ⥤ DerivedCategory W.Modules :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor W.toRingedSpace.sheaf

/-- The dual `L^∨ = R𝓗om(L, 𝒪_W)` of [Stacks, Tag 08DQ]. -/
noncomputable abbrev dualD (L : DerivedCategory W.Modules) : DerivedCategory W.Modules :=
  Stacks.SheafOfModules.derivedDual W.sheaf L

/-- The monoidal structure of [Stacks, Tag 0FPT] on `D(𝒪_W)` in which the dual of a perfect
object is a left dual ([Stacks, Tag 0FPC]). -/
noncomputable abbrev monD : MonoidalCategory (DerivedCategory W.Modules) :=
  Stacks.SheafOfModules.derivedMonoidalStructure W.sheaf

/-- **[Stacks, Tag 0FPC]**: a perfect object and its dual form an exact pairing. -/
@[instance_reducible]
noncomputable def pairD (L : DerivedCategory W.Modules) (hL : IsPerfect (X := W.toRingedSpace) L) :
    letI := monD W
    ExactPairing L (dualD W L) :=
  Stacks.SheafOfModules.exactPairingDerivedDual W.sheaf L
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect W.toRingedSpace L hL)

/-- The tensor product of `monD W` is the derived tensor product `tens W`, up to the canonical
comparison of the two packagings of [Stacks, Tag 06YU]. -/
noncomputable def tensIso :
    letI := monD W
    curriedTensor (DerivedCategory W.Modules) ≅ tens W :=
  Stacks.SheafOfModules.derivedTensorCanonicalIso W.toRingedSpace

/-- `(P ⊗ E) ⊗ B ≅ (E ⊗ B) ⊗ P`, by the associativity and commutativity constraints of the
monoidal structure of [Stacks, Tag 0FPB] whose tensor product is `tens W` on the nose. -/
noncomputable def rotateIso (P E B : DerivedCategory W.Modules) :
    ((tens W).obj (((tens W).obj P).obj E)).obj B ≅
      ((tens W).obj (((tens W).obj E).obj B)).obj P :=
  letI : MonoidalCategory (DerivedCategory W.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal W.toRingedSpace.sheaf
  letI : SymmetricCategory (DerivedCategory W.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric W.toRingedSpace.sheaf
  α_ P E B ≪≫ β_ P (E ⊗ B)

/-- `F ⊗ T ≅ T ⊗ F`. -/
noncomputable def swapIso (F T : DerivedCategory W.Modules) :
    ((tens W).obj F).obj T ≅ ((tens W).obj T).obj F :=
  letI : MonoidalCategory (DerivedCategory W.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal W.toRingedSpace.sheaf
  letI : SymmetricCategory (DerivedCategory W.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric W.toRingedSpace.sheaf
  β_ F T

end Scheme

section Additive

/-- `L g^* ⊣ R g_*`, read between the derived categories of `Scheme.Modules`. -/
noncomputable abbrev dadj {W V : Scheme.{u}} (g : W ⟶ V) : dpull g ⊣ dpush g :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction g.toLRSHom.toShHom

/-- `- ⊗^𝐋 K` is additive, being exact ([Stacks, Tag 06YU]). -/
theorem tens_flip_additive (W : Scheme.{u}) (K : DerivedCategory W.Modules) :
    ((tens W).flip.obj K).Additive := by
  let : ((tens W).flip.obj K).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      W.toRingedSpace.sheaf).commShift_left K
  have : ((tens W).flip.obj K).IsTriangulated :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      W.toRingedSpace.sheaf).exact_left K
  infer_instance

/-- `Lf^*` is additive, being exact ([Stacks, Tag 06YJ]). -/
theorem derivedPullback_additive {W V : Scheme.{u}} (g : W ⟶ V) : (dpull g).Additive := by
  let : (dpull g).CommShift ℤ :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift (f := g.toLRSHom.toShHom)
  have : (dpull g).IsTriangulated :=
    Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated
      (f := g.toLRSHom.toShHom)
  infer_instance

/-- `Rf_*` is additive, being right adjoint to the additive `Lf^*`. -/
theorem derivedPushforward_additive {W V : Scheme.{u}} (g : W ⟶ V) : (dpush g).Additive := by
  have := derivedPullback_additive g
  exact (dadj g).right_adjoint_additive

end Additive

section OverField

variable {k : Type u} [Field k]

attribute [local instance] AlgebraicGeometry.modulesLinear

/-- `Hom(L, N) ≃ₗ[k] Hom(𝒪_W, N ⊗^𝐋 L^∨)` for a perfect `L` on a scheme over `k`. -/
noncomputable def dualHomLinearEquiv (W : Over (Spec (CommRingCat.of k)))
    (L N : DerivedCategory W.left.Modules) (hL : IsPerfect (X := W.left.toRingedSpace) L) :
    (L ⟶ N) ≃ₗ[k] (unitD W.left ⟶ ((tens W.left).obj N).obj (dualD W.left L)) :=
  letI := monD W.left
  letI := pairD W.left L hL
  haveI := tens_flip_additive W.left (dualD W.left L)
  haveI : ((tens W.left).flip.obj (dualD W.left L)).Linear k :=
    derivedTensor_flip_obj_linear k W (dualD W.left L)
  dualHomLinearEquivOf (tensIso W.left) k L (dualD W.left L) N

/-- The adjunction `Lf^* ⊣ Rf_*` along a morphism of schemes over `k`, as a `k`-linear
bijection. -/
noncomputable def pullPushLinearEquiv {W V : Over (Spec (CommRingCat.of k))} (g : W ⟶ V)
    (A : DerivedCategory V.left.Modules) (B : DerivedCategory W.left.Modules) :
    ((dpull g.left).obj A ⟶ B) ≃ₗ[k] (A ⟶ (dpush g.left).obj B) :=
  haveI : (dpush g.left).Linear k := derivedPushforward_linear k g
  haveI := derivedPushforward_additive g.left
  adjHomLinearEquiv k (dadj g.left) A B

end OverField

section Main

variable {k : Type u} [Field k]

attribute [local instance] AlgebraicGeometry.modulesLinear

variable (X Y : Over (Spec (CommRingCat.of k)))

/-- The first projection `X ×_k Y ⟶ X`, as a morphism over `k`. -/
noncomputable abbrev pk : overPullback k X Y ⟶ X := Over.homMk (pullback.fst X.hom Y.hom) rfl

/-- The second projection `X ×_k Y ⟶ Y`, as a morphism over `k`. -/
noncomputable abbrev qk : overPullback k X Y ⟶ Y :=
  Over.homMk (pullback.snd X.hom Y.hom) pullback.condition.symm

/-- `Lq^*A` on `X ×_k Y`. -/
noncomputable abbrev pulledA (A : DerivedCategory Y.left.Modules) :
    DerivedCategory (pullback X.hom Y.hom).Modules :=
  (dpull (pullback.snd X.hom Y.hom)).obj A

/-- `E' ⊗^𝐋 (Lq^*A)^∨` on `X ×_k Y`. -/
noncomputable abbrev kernelQ (E' : DerivedCategory (pullback X.hom Y.hom).Modules)
    (A : DerivedCategory Y.left.Modules) : DerivedCategory (pullback X.hom Y.hom).Modules :=
  ((tens _).obj E').obj (dualD _ (pulledA X Y A))

/-- `F = Rp_*(E' ⊗^𝐋 (Lq^*A)^∨)` on `X`. -/
noncomputable abbrev kernelF (E' : DerivedCategory (pullback X.hom Y.hom).Modules)
    (A : DerivedCategory Y.left.Modules) : DerivedCategory X.left.Modules :=
  (dpush (pullback.fst X.hom Y.hom)).obj (kernelQ X Y E' A)

/-- **The perfect object `E = F^∨ = (Rp_*(E' ⊗^𝐋 (Lq^*A)^∨))^∨` on `X`** that represents
`T ↦ Hom(A, Φ_{E'}(T))` on `D_QCoh(𝒪_X)`. -/
noncomputable abbrev kernelDual (E' : DerivedCategory (pullback X.hom Y.hom).Modules)
    (A : DerivedCategory Y.left.Modules) : DerivedCategory X.left.Modules :=
  dualD _ (kernelF X Y E' A)

variable {X Y}

section Perfect

variable [Flat Y.hom] [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom]
  {E' : DerivedCategory (pullback X.hom Y.hom).Modules}
  (hE' : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) E')
  {A : DerivedCategory Y.left.Modules} (hA : IsPerfect (X := Y.left.toRingedSpace) A)

omit [Flat Y.hom] [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom] in
include hA in
/-- `Lq^*A` is perfect ([Stacks, Tag 09UA]). -/
theorem isPerfect_pulledA :
    IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) (pulledA X Y A) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback _ A hA

omit [Flat Y.hom] [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom] in
include hA in
/-- `(Lq^*A)^∨` is perfect ([Stacks, Tag 08DQ]). -/
theorem isPerfect_dual_pulledA :
    IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) (dualD _ (pulledA X Y A)) :=
  Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace _ _ (isPerfect_pulledA hA)

omit [Flat Y.hom] [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom] in
include hE' hA in
/-- `E' ⊗^𝐋 (Lq^*A)^∨` is perfect ([Stacks, Tag 09J5]). -/
theorem isPerfect_kernelQ :
    IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) (kernelQ X Y E' A) :=
  isPerfect_dtenR _ _ hE' (isPerfect_dual_pulledA hA)

include hE' hA in
/-- `Rp_*(E' ⊗^𝐋 (Lq^*A)^∨)` is perfect ([Stacks, Tag 0B91] (1)): `p` is a base change of
`Y ⟶ Spec k`, hence flat, proper and of finite presentation. -/
theorem isPerfect_kernelF : IsPerfect (X := X.left.toRingedSpace) (kernelF X Y E' A) :=
  isPerfect_derivedPushforward_of_flat_of_isProper (pullback.fst X.hom Y.hom) _
    (isPerfect_kernelQ hE' hA)

include hE' hA in
/-- The representing object `kernelDual X Y E' A` is perfect ([Stacks, Tag 08DQ]). -/
theorem isPerfect_kernelDual : IsPerfect (X := X.left.toRingedSpace) (kernelDual X Y E' A) :=
  Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace _ _ (isPerfect_kernelF hE' hA)

/-- **`Hom(A, Φ_{E'}(T)) ≃ₗ[k] Hom(E, T)`** for `T` with quasi-coherent cohomology. -/
noncomputable def homFourierMukaiLinearEquiv (T : DerivedCategory X.left.Modules)
    (hT : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.left.Modules j).obj T).IsQuasicoherent) :
    (A ⟶ (fourierMukai X.hom Y.hom E').obj T) ≃ₗ[k] (kernelDual X Y E' A ⟶ T) :=
  let p := pullback.fst X.hom Y.hom
  let P := (dpull p).obj T
  let N := ((tens _).obj P).obj E'
  let V := ((tens _).obj (kernelQ X Y E' A)).obj P
  haveI : IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      p.toLRSHom.toShHom (kernelQ X Y E' A) T) :=
    Stacks.Cohomology.ProjectionFormulaQCoh.projectionFormulaMap_isIso_of_isQuasicoherent_homology
      p inferInstance inferInstance _ T
      (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ _ (isPerfect_kernelQ hE' hA))
      hT
  let uZ : (dpull p).obj (unitD X.left) ≅ unitD (pullback X.hom Y.hom) :=
    Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso p.toLRSHom.toShHom
  let ι : (dpush p).obj V ≅ ((tens X.left).obj T).obj (dualD _ (kernelDual X Y E' A)) :=
    (asIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      p.toLRSHom.toShHom (kernelQ X Y E' A) T)).symm ≪≫ swapIso _ _ T ≪≫
      ((tens X.left).obj T).mapIso (Stacks.SheafOfModules.derivedBidualIsoOfIsPerfectSpace
        X.left.toRingedSpace _ (isPerfect_kernelF hE' hA))
  (pullPushLinearEquiv (qk X Y) A N).symm ≪≫ₗ
    dualHomLinearEquiv (overPullback k X Y) (pulledA X Y A) N (isPerfect_pulledA hA) ≪≫ₗ
    Linear.homCongr k (Iso.refl _) (rotateIso _ P E' (dualD _ (pulledA X Y A))) ≪≫ₗ
    Linear.homCongr k uZ.symm (Iso.refl V) ≪≫ₗ
    pullPushLinearEquiv (pk X Y) (unitD X.left) V ≪≫ₗ
    Linear.homCongr k (Iso.refl _) ι ≪≫ₗ
    (dualHomLinearEquiv X (kernelDual X Y E' A) T (isPerfect_kernelDual hE' hA)).symm

end Perfect

/-- **Module C of the converse of [Stacks, Tag 0FYD].** Let `X`, `Y` be schemes over a field `k`
with `Y ⟶ Spec k` flat, proper and of finite presentation, let `E'` be a perfect object on
`X ×_k Y` and let `K ∈ D_QCoh(𝒪_X)` satisfy condition (2) of [Stacks, Tag 0FYD]:
`∑_i dim_k Ext^i_X(E, K) < ∞` for every perfect `E`. Then for every perfect `A` on `Y` the
Fourier–Mukai transform `Φ_{E'}(K) = Rq_*(Lp^*K ⊗^𝐋 E')` has finite total `Hom` from `A`:
`∑_i dim_k Hom(A, Φ_{E'}(K)[i]) < ∞`.

`Hom(A, Φ_{E'}(K)[i]) ≅ Ext^i_X(E, K)` with `E = (Rp_*(E' ⊗^𝐋 (Lq^*A)^∨))^∨`, which is perfect
([Stacks, Tags 09UA, 08DQ, 0B91]), through the adjunctions `Lq^* ⊣ Rq_*` and `Lp^* ⊣ Rp_*`, the
duality of perfect objects ([Stacks, Tags 0FPC, 08DQ]) and the projection formula
([Stacks, Tag 08EU]); every step is `k`-linear. -/
theorem hasFiniteTotalHom_fourierMukai_of_isPerfect
    [Flat Y.hom] [IsProper Y.hom] [LocallyOfFinitePresentation Y.hom]
    (E' : DerivedCategory (pullback X.hom Y.hom).Modules)
    (hE' : IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) E')
    (K : DerivedCategory X.left.Modules)
    (hK : DerivedCategoryB.derivedCategoryB (A := X.left.Modules)
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) K)
    (h2 : ∀ E : DerivedCategory X.left.Modules, IsPerfect (X := X.left.toRingedSpace) E →
      Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K)
    (A : DerivedCategory Y.left.Modules) (hA : IsPerfect (X := Y.left.toRingedSpace) A) :
    Pretriangulated.HasFiniteTotalHom k A ((fourierMukai X.hom Y.hom E').obj K) := by
  have hKs : ∀ j : ℤ, DerivedCategoryB.derivedCategoryB (A := X.left.Modules)
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) (K⟦j⟧) := by
    have := DerivedCategoryB.derivedCategoryB_isTriangulated (A := X.left.Modules)
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf)
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X.left)
    exact fun j => ObjectProperty.le_shift _ j K hK
  let e : ∀ j : ℤ, (A ⟶ ((fourierMukai X.hom Y.hom E').obj K)⟦j⟧) ≃ₗ[k]
      (kernelDual X Y E' A ⟶ K⟦j⟧) := fun j =>
    Linear.homCongr k (Iso.refl A)
        (((fourierMukai X.hom Y.hom E').commShiftIso j).app K).symm ≪≫ₗ
      homFourierMukaiLinearEquiv hE' hA (K⟦j⟧) (hKs j)
  obtain ⟨hfin, hset⟩ := h2 _ (isPerfect_kernelDual hE' hA)
  refine ⟨fun j => ?_, hset.subset fun j hj hs => ?_⟩
  · have : Module.Finite k (kernelDual X Y E' A ⟶ K⟦j⟧) := hfin j
    exact Module.Finite.equiv (e j).symm
  · have : Subsingleton (kernelDual X Y E' A ⟶ K⟦j⟧) := hs
    have : Nontrivial (A ⟶ ((fourierMukai X.hom Y.hom E').obj K)⟦j⟧) := hj
    exact not_subsingleton _ (e j).toEquiv.subsingleton

end Main

section ProjectiveSpace

open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjectiveSpacePerfect

attribute [local instance] MvPolynomial.gradedAlgebra AlgebraicGeometry.modulesLinear

variable {k : Type u} [Field k]

/-- `𝒪(d)` placed in degree zero is a perfect object of `D(𝒪_{ℙᵐ_k})`. -/
theorem isPerfect_twistE (m : ℕ) (d : ℤ) :
    IsPerfect.{u, u, u + 1}
      (X := (Stacks.AlgebraicGeometry.TwistEndomorphisms.projOver k m).left.toRingedSpace)
      (twistE k m d) := by
  let P := AlgebraicGeometry.Proj (polyGrading k m)
  let L := ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k m) d
  have hinv : Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      P.sheaf.obj P.ringCatSheaf.property L).mpr
      (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf (polyGrading k m)
        (Stacks.PicardUFD.degreeOneCover k m) d)
  exact AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree P L
    (@AlgebraicGeometry.VectorBundleKZero.isFiniteLocallyFree_of_isInvertible P L hinv)

/-- **Module C of the converse of [Stacks, Tag 0FYD], at the exceptional sequence of `ℙᵐ_k`.**
For `K ∈ D_QCoh(𝒪_X)` satisfying condition (2) of [Stacks, Tag 0FYD] and a perfect `E'` on
`X ×_k ℙᵐ_k`, the Fourier–Mukai transform `Rq_*(Lp^*K ⊗^𝐋 E')` has finite total `Hom` from each
of `𝒪(-m), …, 𝒪`. This is the hypothesis `hC` of
`AlgebraicGeometry.CoherentConverse.derivedCategoryBBounded_of_fourierMukai`. -/
theorem hasFiniteTotalHom_seqE_fourierMukai (X : Over (Spec (CommRingCat.of k)))
    (K : DerivedCategory X.left.Modules)
    (hK : DerivedCategoryB.derivedCategoryB (A := X.left.Modules)
      (SheafOfModules.isQuasicoherent X.left.ringCatSheaf) K)
    (h2 : ∀ E : DerivedCategory X.left.Modules, IsPerfect (X := X.left.toRingedSpace) E →
      Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.HasFiniteTotalExt k X E K)
    (m : ℕ) (E' : DerivedCategory (pullback X.hom (projToSpecCoeff k m)).Modules)
    (hE' : IsPerfect (X := (pullback X.hom (projToSpecCoeff k m)).toRingedSpace) E')
    (a : Fin (m + 1)) :
    Pretriangulated.HasFiniteTotalHom k (seqE k m a)
      ((fourierMukai X.hom (projToSpecCoeff k m) E').obj K) := by
  have : Smooth (Stacks.AlgebraicGeometry.TwistEndomorphisms.projOver k m).hom :=
    smooth_projToSpecCoeff k m
  have : IsProper (Stacks.AlgebraicGeometry.TwistEndomorphisms.projOver k m).hom :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k m
  exact hasFiniteTotalHom_fourierMukai_of_isPerfect
    (Y := Stacks.AlgebraicGeometry.TwistEndomorphisms.projOver k m) E' hE' K hK h2 _
    (isPerfect_twistE m _)

end ProjectiveSpace

end Stacks.AlgebraicGeometry.FourierMukaiFiniteHom

end
