module

public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.TensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Representative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence of the derived tensor product on a ringed space

Let `(X, 𝒪_X)` be a ringed space and let `K`, `L` be objects of `D(𝒪_X)`.  If `K` is
`n`-pseudo-coherent with `H^i(K) = 0` for `i > a` and `L` is `m`-pseudo-coherent with
`H^j(L) = 0` for `j > b`, then `K ⊗_{𝒪_X}^{𝐋} L` is `t`-pseudo-coherent for
`t = max (m + a, n + b)`; and if `K` and `L` are pseudo-coherent then so is
`K ⊗_{𝒪_X}^{𝐋} L`.  The derived tensor product is the one of Tag 06YU, instantiated on the site
of open subsets of `X`.

The argument is the source's.  Each factor is replaced by a K-flat representative, on which the
derived tensor product is the total tensor complex, so that complex represents
`K ⊗^{𝐋} L`; pseudo-coherence passes to those representatives by Tag 08CC part (2).  Over an
open on which both carry strictly perfect approximations — of the first in degree `n`, of the
second in degree `m` — the total tensor complex of the two models is strictly perfect (Tag 09J2)
and the derived tensor product of the two approximations is an approximation in degree `t`.  The
source asserts that last step as a consequence of "the spectral sequence of tors (details
omitted)"; it is proved here instead from right t-exactness of the derived tensor product, by
factoring `α ⊗^{𝐋} β` through `𝒫 ⊗^{𝐋} ℬ` and shifting the degree of each of the two legs by
the cohomological bound of the factor that stays fixed.  Tag 08CC part (1) assembles the local
approximations into `t`-pseudo-coherence.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedTensorProduct`: part (1), the
  quantitative statement.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedTensorProduct`: part (2), preservation
  of pseudo-coherence.

## Implementation notes

**The degree estimate is derived-categorical.**  The local step is
`AlgebraicGeometry.RingedSpace.exists_approximation_derivedTensor`, which needs no spectral
sequence: the cocone triangle of an approximation in degree `s` has third vertex in
`D^{≤ s - 1}`, tensoring with an object of `D^{≤ e}` keeps it in `D^{≤ s + e - 1}` by
`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct`, and reading that dictionary
backwards — `StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation` — returns an
approximation in degree `s + e`.  Exactness of the derived tensor product in each variable
separately, the `exact_left` and `exact_right` fields of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, is what makes the two legs available
without a symmetry constraint.  Since `t = max (m + a, n + b)` dominates both `m + a` and
`n + b`, and `t`-pseudo-coherence weakens as `t` grows, the two legs compose.

**Why part (2) is not part (1) at `t = q`.**  A pseudo-coherent object of `D(𝒪_X)` need not be
bounded above globally, so part (1) does not apply to it directly; the source restricts to an
open covering on which both factors are bounded above.  Here the bounds are produced on the
covering itself, in
`AlgebraicGeometry.RingedSpace.localApproximationData_of_isPseudoCoherentComplex`: a strictly
perfect approximation in degree `0` over an open has only finitely many nonzero terms, which
bounds the cohomology of the factor there, and the two thresholds are then chosen as
`n = min (q - b) a` and `m = min (q - a) b`, which makes `max (m + a, n + b) ≤ q`.

**The two spellings of the category of `𝒪_X`-modules.**  `StrictlyPerfect.OXMod X`, which strict
perfection, restriction to an open and pseudo-coherence are stated at, and
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf`, which the derived tensor product is stated
at, are the same category by
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.modules_eq_OXMod : rfl`, but unification
must unfold the semireducible `StrictlyPerfect.structureSheafOfRings` to see it and instance
search will not.  Every place where the two meet is cut into its own declaration —
`AlgebraicGeometry.RingedSpace.LocalApproximationData` and
`AlgebraicGeometry.RingedSpace.RestrictedIsLE` are the two predicates that exist only for that
reason — which is what keeps each declaration inside the default heartbeat budget; written as
one term the argument does not elaborate.

**The derived-category universe is fixed.**  `attribute [local instance]
HasDerivedCategory.standard` is used throughout, following
`StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback` and
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.RestrictionToAnOpen`: a single uniform
instance fires at both spellings of the category of modules, whereas a `HasDerivedCategory`
binder at either spelling does not.

**Relation to the existing reduction.**
`StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.TensorProduct` carries the same two
statements with the complex-level step
`Stacks.Cohomology.PseudoCoherentTensor.ComplexLevel` as a hypothesis.  That hypothesis is the
content of this tag, so nothing there carries the tag; the degenerate range of part (1), where
one pseudo-coherence threshold exceeds the cohomological bound of its own factor and the
estimate follows from right t-exactness alone, is reused from it as
`Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_derivedTensorProduct_of_lt`.

## References

* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Tag 09J2](https://stacks.math.columbia.edu/tag/09J2)
* [Stacks Project, Lemma 20.47.5 (Tag 09J3)](https://stacks.math.columbia.edu/tag/09J3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe v₁ u₁ w₁ u

/-! ### Approximations and isomorphisms of complexes -/

/-- **Pre- and post-composing an approximation with isomorphisms leaves it one.** -/
private theorem approximation_isoComp {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w₁} A] {W₁ W₂ Z₁ Z₂ : DerivedCategory A}
    (e₁ : W₁ ≅ W₂) (φ : W₂ ⟶ Z₁) (e₂ : Z₂ ≅ Z₁) (t : ℤ)
    (hiso : ∀ j : ℤ, t < j → IsIso ((DerivedCategory.homologyFunctor A j).map φ))
    (hepi : Epi ((DerivedCategory.homologyFunctor A t).map φ)) :
    (∀ j : ℤ, t < j →
        IsIso ((DerivedCategory.homologyFunctor A j).map (e₁.hom ≫ φ ≫ e₂.inv))) ∧
      Epi ((DerivedCategory.homologyFunctor A t).map (e₁.hom ≫ φ ≫ e₂.inv)) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have := hiso j hj
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  · have := hepi
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance

/-! ### Restricting an approximation to a smaller open -/

section Local

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- Restriction to an open subspace preserves a bound on the degrees of the nonzero terms. -/
private theorem isZero_restrictComplex_X (A : CochainComplex (KFlatDerivedPullback.Modules X) ℤ)
    (a : ℤ)
    (hA : A.IsStrictlyLE a) (W : Opens X.carrier) (j : ℤ) (hj : a < j) :
    IsZero ((restrictComplex A W).X j) := by
  have := hA
  exact (restrictModules X W).isZero_obj (A.isZero_of_isStrictlyLE a j hj)

/-- Restriction between opens preserves a bound on the degrees of the nonzero terms. -/
private theorem isZero_restrictModulesOfLE_X {U W : Opens X.carrier} (h : W ≤ U)
    (P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ) (c : ℤ)
    (hP : ∀ j : ℤ, c < j → IsZero (P.X j)) (j : ℤ) (hj : c < j) :
    IsZero ((((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X j) :=
  (restrictModulesOfLE X h).isZero_obj (hP j hj)

/-- **A strictly perfect approximation over `U` restricts to one over any smaller open `W`.**
Restriction to an open subspace is exact, so it preserves both cohomological conditions, and
`AlgebraicGeometry.RingedSpace.restrictComplexOfLEIso` identifies the two-step restriction of
the approximated complex with its one-step restriction. -/
private theorem exists_restricted_approximation {U W : Opens X.carrier} (h : W ≤ U)
    (A : CochainComplex (KFlatDerivedPullback.Modules X) ℤ) (s : ℤ)
    (P : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (α : P ⟶ restrictComplex A U)
    (hiso : ∀ j : ℤ, s < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α s)) :
    ∃ α' : (((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
        restrictComplex A W,
      (∀ j : ℤ, s < j → IsIso (HomologicalComplex.homologyMap α' j)) ∧
        Epi (HomologicalComplex.homologyMap α' s) := by
  refine ⟨((restrictModulesOfLE X h).mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫
    (restrictComplexOfLEIso X h A).hom, fun j hj => ?_, ?_⟩
  · exact isIso_homologyMap_comp _ _ j
      (isIso_homologyMap_mapHomologicalComplex (restrictModulesOfLE X h) α j (hiso j hj))
      inferInstance
  · refine epi_homologyMap_comp _ _ s
      (epi_homologyMap_mapHomologicalComplex (restrictModulesOfLE X h) α s hepi) ?_
    infer_instance

/-- The statement that `𝒜|_W` lies in `D^{≤ a}(𝒪_W)`, written in the spelling of the derived
tensor product rather than in the one restriction is stated at.  The two are the same category,
and elaborating that identification here rather than at each use keeps the declarations that
consume it inside the default heartbeat budget. -/
private abbrev RestrictedIsLE (A : CochainComplex (KFlatDerivedPullback.Modules X) ℤ)
    (W : Opens X.carrier) (a : ℤ) : Prop :=
  (DerivedCategory.Q.obj (restrictComplex A W :
    CochainComplex (Stacks.DerivedTensor.RingedSite.Modules
      (X.restrict W.isOpenEmbedding).sheaf) ℤ)).IsLE a

/-- A complex with no terms above `a` restricts to one whose class lies in `D^{≤ a}`. -/
private theorem restrictedIsLE_of_isStrictlyLE
    (A : CochainComplex (KFlatDerivedPullback.Modules X) ℤ) (a : ℤ) (hA : A.IsStrictlyLE a)
    (W : Opens X.carrier) : RestrictedIsLE X A W a := by
  have hz : CochainComplex.IsStrictlyLE (restrictComplex A W :
      CochainComplex (Stacks.DerivedTensor.RingedSite.Modules
        (X.restrict W.isOpenEmbedding).sheaf) ℤ) a :=
    (CochainComplex.isStrictlyLE_iff _ a).2 fun j hj => isZero_restrictComplex_X X A a hA W j hj
  have := hz
  exact (DerivedCategory.isLE_Q_obj_iff _ a).2 inferInstance

/-- A strictly perfect approximation of `𝒜|_W` in degree `s` whose source has no terms above `c`
puts `𝒜|_W` in `D^{≤ max s c}`. -/
private theorem restrictedIsLE_of_approximation
    (A : CochainComplex (KFlatDerivedPullback.Modules X) ℤ) (W : Opens X.carrier) (s c : ℤ)
    (P : CochainComplex (OXMod.{u, u} (X.restrict W.isOpenEmbedding)) ℤ)
    (hPz : ∀ j : ℤ, c < j → IsZero (P.X j)) (α : P ⟶ restrictComplex A W)
    (hiso : ∀ j : ℤ, s < j → IsIso (HomologicalComplex.homologyMap α j)) :
    RestrictedIsLE X A W (max s c) :=
  DerivedCategory.isLE_Q_obj_of_homologyMap_approximation s c hPz α hiso

end Local

/-! ### The derived-categorical core -/

section Core

attribute [local instance] HasDerivedCategory.standard

/-- **The derived-categorical heart of Tag 09J3 part (1).**  Let `α : 𝒫 ⟶ 𝒜` and `β : 𝒬 ⟶ ℬ` be
morphisms of complexes of `𝒪_Y`-modules with `𝒜` and `ℬ` having no terms above `a`, resp. `b`,
with `α` an approximation in degree `n ≤ a` and `β` one in degree `m`.  Then
`α ⊗^{𝐋} β : 𝒫 ⊗^{𝐋} 𝒬 ⟶ 𝒜 ⊗^{𝐋} ℬ` is an approximation in degree `t = max (m + a, n + b)`.

The morphism is factored as `𝒫 ⊗^{𝐋} 𝒬 ⟶ 𝒫 ⊗^{𝐋} ℬ ⟶ 𝒜 ⊗^{𝐋} ℬ`.  The first leg is `β`
tensored with `𝒫`, which lies in `D^{≤ a}(𝒪_Y)` because `α` is an isomorphism on cohomology
above `n ≤ a` and `𝒜` has no terms above `a`; the second is `α` tensored with `ℬ ∈ D^{≤ b}`.
Right t-exactness of the derived tensor product in each variable shifts the degree of each
approximation by the bound of the fixed factor, giving `m + a` and `n + b`; both are at most
`t`, so both legs are isomorphisms on cohomology above `t` and surjections in degree `t`, and
so is their composite. -/
private theorem exists_approximation_derivedTensor (Y : RingedSpace.{u, u})
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Y.sheaf)
    (P Q A B : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf) ℤ)
    (n m a b : ℤ) (hna : n ≤ a)
    (hQA : (DerivedCategory.Q.obj A).IsLE a) (hQB : (DerivedCategory.Q.obj B).IsLE b)
    (α : P ⟶ A)
    (hαiso : ∀ j : ℤ, n < j → IsIso (HomologicalComplex.homologyMap α j))
    (hαepi : Epi (HomologicalComplex.homologyMap α n))
    (β : Q ⟶ B)
    (hβiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hβepi : Epi (HomologicalComplex.homologyMap β m)) :
    ∃ γ : (T.tensor.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q) ⟶
        (T.tensor.obj (DerivedCategory.Q.obj A)).obj (DerivedCategory.Q.obj B),
      (∀ j : ℤ, max (m + a) (n + b) < j →
          IsIso ((DerivedCategory.homologyFunctor _ j).map γ)) ∧
        Epi ((DerivedCategory.homologyFunctor _ (max (m + a) (n + b))).map γ) := by
  have hQA' := hQA
  have hQB' := hQB
  have hQαiso : ∀ j : ℤ, n < j → IsIso ((DerivedCategory.homologyFunctor _ j).map
      (DerivedCategory.Q.map α)) := fun j hj =>
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ j) α).mpr (hαiso j hj)
  have hQαepi : Epi ((DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Q.map α)) :=
    (NatIso.epi_map_iff (DerivedCategory.homologyFunctorFactors _ n) α).mpr hαepi
  have hQβiso : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map
      (DerivedCategory.Q.map β)) := fun j hj =>
    (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ j) β).mpr (hβiso j hj)
  have hQβepi : Epi ((DerivedCategory.homologyFunctor _ m).map (DerivedCategory.Q.map β)) :=
    (NatIso.epi_map_iff (DerivedCategory.homologyFunctorFactors _ m) β).mpr hβepi
  have hQP : (DerivedCategory.Q.obj P).IsLE a := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    have := hQαiso j (by omega)
    exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj A) a j hj).of_iso
      (asIso ((DerivedCategory.homologyFunctor _ j).map (DerivedCategory.Q.map α)))
  let csP : (T.tensor.obj (DerivedCategory.Q.obj P)).CommShift ℤ :=
    T.commShift_right (DerivedCategory.Q.obj P)
  have exP : (T.tensor.obj (DerivedCategory.Q.obj P)).IsTriangulated :=
    T.exact_right (DerivedCategory.Q.obj P)
  let csB : (T.tensor.flip.obj (DerivedCategory.Q.obj B)).CommShift ℤ :=
    T.commShift_left (DerivedCategory.Q.obj B)
  have exB : (T.tensor.flip.obj (DerivedCategory.Q.obj B)).IsTriangulated :=
    T.exact_left (DerivedCategory.Q.obj B)
  have hleg1 := DerivedCategory.approximation_of_isLE_functor
    (T.tensor.obj (DerivedCategory.Q.obj P)) a
    (fun Z c hZ => by
      have := hZ
      have h := Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct Y.sheaf T
        (DerivedCategory.Q.obj P) Z a c
      exact DerivedCategory.TStructure.t.isLE_of_le _ (a + c) (c + a) (by omega))
    (DerivedCategory.Q.map β) m hQβiso hQβepi
  have hleg2 := DerivedCategory.approximation_of_isLE_functor
    (T.tensor.flip.obj (DerivedCategory.Q.obj B)) b
    (fun Z c hZ => by
      have := hZ
      exact Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct Y.sheaf T Z
        (DerivedCategory.Q.obj B) c b)
    (DerivedCategory.Q.map α) n hQαiso hQαepi
  refine ⟨(T.tensor.obj (DerivedCategory.Q.obj P)).map (DerivedCategory.Q.map β) ≫
    (T.tensor.flip.obj (DerivedCategory.Q.obj B)).map (DerivedCategory.Q.map α), ?_, ?_⟩
  · intro j hj
    have h1 := hleg1.1 j (by omega)
    have h2 := hleg2.1 j (by omega)
    rw [Functor.map_comp]
    infer_instance
  · have h1 := DerivedCategory.epi_homologyMap_of_le _ (m + a) (max (m + a) (n + b))
      (le_max_left _ _) hleg1.1 hleg1.2
    have h2 := DerivedCategory.epi_homologyMap_of_le _ (n + b) (max (m + a) (n + b))
      (le_max_right _ _) hleg2.1 hleg2.2
    rw [Functor.map_comp]
    infer_instance

end Core

/-! ### Tag 09J3 -/

section Main

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})


/-- The local data Tag 08CC part (1) consumes on an open `U`: a strictly perfect complex and a
morphism to `Tot(𝒜 ⊗_{𝒪_X} ℬ)|_U` in the derived category which is an isomorphism on cohomology
above `t` and a surjection in degree `t`.

Named, rather than written out at each of its three uses, because it is the one place where the
two spellings of the category of `𝒪_X`-modules meet: the restriction functor is stated at
`StrictlyPerfect.OXMod` and the total tensor complex at
`Stacks.DerivedTensor.RingedSite.Modules`, and the two are the same category by
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.modules_eq_OXMod : rfl` while unification
must unfold the semireducible `StrictlyPerfect.structureSheafOfRings` to see it.  Elaborating
that identification once here keeps every declaration below inside the default heartbeat
budget. -/
private abbrev LocalApproximationData
    (A B : CochainComplex (KFlatDerivedPullback.Modules X) ℤ) (t : ℤ) (U : Opens X.carrier) :
    Prop :=
  ∃ S : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules
      (X.restrict U.isOpenEmbedding).sheaf) ℤ,
    IsStrictlyPerfect S ∧
    ∃ δ : DerivedCategory.Q.obj S ⟶ DerivedCategory.Q.obj (restrictComplex
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj A).obj B) U),
      (∀ j : ℤ, t < j → IsIso ((DerivedCategory.homologyFunctor _ j).map δ)) ∧
        Epi ((DerivedCategory.homologyFunctor _ t).map δ)

/-- **The local step of Tag 09J3 part (1), on one open.**  Let `W` be an open contained in an
open `U` over which `𝒜` has a strictly perfect approximation in degree `n` and in an open `V`
over which `ℬ` has one in degree `m`, and suppose `𝒜|_W ∈ D^{≤ a}` and `ℬ|_W ∈ D^{≤ b}` with
`n ≤ a`.  Then `W` carries the local data of degree `t = max (m + a, n + b)`.

Both models restrict to `W`, where their total tensor complex is strictly perfect (Tag 09J2) and
hence K-flat, and `AlgebraicGeometry.RingedSpace.exists_approximation_derivedTensor` makes the
derived tensor product of the two restricted approximations an approximation in degree `t`.  Its
source is the class of the total tensor complex of the restricted models by the comparison of
Tag 06YU, and its target the class of `Tot(𝒜 ⊗ ℬ)|_W` by
`Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat`. -/
private theorem localApproximationData_of_approximations {U V W : Opens X.carrier}
    (hWU : W ≤ U) (hWV : W ≤ V)
    (A B : CochainComplex (KFlatDerivedPullback.Modules X) ℤ)
    (hAk : Stacks.SheafOfModules.KFlat.KFlat X.sheaf A)
    (hBk : Stacks.SheafOfModules.KFlat.KFlat X.sheaf B)
    (n m a b : ℤ) (hna : n ≤ a)
    (hA : RestrictedIsLE X A W a) (hB : RestrictedIsLE X B W b)
    (P₁ : CochainComplex (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP₁ : IsStrictlyPerfect P₁) (α : P₁ ⟶ restrictComplex A U)
    (hαiso : ∀ j : ℤ, n < j → IsIso (HomologicalComplex.homologyMap α j))
    (hαepi : Epi (HomologicalComplex.homologyMap α n))
    (P₂ : CochainComplex (OXMod.{u, u} (X.restrict V.isOpenEmbedding)) ℤ)
    (hP₂ : IsStrictlyPerfect P₂) (β : P₂ ⟶ restrictComplex B V)
    (hβiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hβepi : Epi (HomologicalComplex.homologyMap β m)) :
    LocalApproximationData X A B (max (m + a) (n + b)) W := by
  obtain ⟨α', hα'iso, hα'epi⟩ := exists_restricted_approximation X hWU A n P₁ α hαiso hαepi
  obtain ⟨β', hβ'iso, hβ'epi⟩ := exists_restricted_approximation X hWV B m P₂ β hβiso hβepi
  obtain ⟨γ, hγiso, hγepi⟩ := exists_approximation_derivedTensor
    (X.restrict W.isOpenEmbedding)
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      (X.restrict W.isOpenEmbedding).sheaf)
    _ _ _ _ n m a b hna hA hB α' hα'iso hα'epi β' hβ'iso hβ'epi
  obtain ⟨hδiso, hδepi⟩ := approximation_isoComp
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (X.restrict W.isOpenEmbedding).sheaf).comparison _ _
      (KFlatDerivedPullback.kFlat_of_isStrictlyPerfect _
        (isStrictlyPerfect_restrictModulesOfLE hWU hP₁))
      (KFlatDerivedPullback.kFlat_of_isStrictlyPerfect _
        (isStrictlyPerfect_restrictModulesOfLE hWV hP₂))).symm
    γ
    (Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat X W
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
        (X.restrict W.isOpenEmbedding).sheaf) A B hAk hBk)
    (max (m + a) (n + b)) hγiso hγepi
  refine ⟨_, ?_, _, hδiso, hδepi⟩
  exact isStrictlyPerfect_tensorComplex _ _ _
    (isStrictlyPerfect_restrictModulesOfLE hWU hP₁)
    (isStrictlyPerfect_restrictModulesOfLE hWV hP₂)

/-- The local data of degree `t` is in particular the local data of any degree `t ≤ q`. -/
private theorem LocalApproximationData.mono
    {A B : CochainComplex (KFlatDerivedPullback.Modules X) ℤ} {t q : ℤ} {W : Opens X.carrier}
    (h : LocalApproximationData X A B t W) (htq : t ≤ q) :
    LocalApproximationData X A B q W := by
  obtain ⟨S, hS, δ, hiso, hepi⟩ := h
  exact ⟨S, hS, δ, fun j hj => hiso j (by omega),
    DerivedCategory.epi_homologyMap_of_le δ t q htq hiso hepi⟩

/-- **The local step of Tag 09J3 part (1).**  Pseudo-coherence in degree `n` of `𝒜` and in
degree `m` of `ℬ` are local conditions, so every point lies in an open carrying a strictly
perfect approximation of each; on the intersection
`AlgebraicGeometry.RingedSpace.localApproximationData_of_approximations` applies, the bounds
on `𝒜|_W` and `ℬ|_W` coming from the bounds on the terms of `𝒜` and `ℬ`. -/
private theorem localApproximationData
    (A B : CochainComplex (KFlatDerivedPullback.Modules X) ℤ)
    (hAk : Stacks.SheafOfModules.KFlat.KFlat X.sheaf A)
    (hBk : Stacks.SheafOfModules.KFlat.KFlat X.sheaf B)
    (n m a b : ℤ) (hna : n ≤ a)
    (hALE : A.IsStrictlyLE a) (hBLE : B.IsStrictlyLE b)
    (hApc : IsPseudoCoherentComplexFrom (X := X) A n)
    (hBpc : IsPseudoCoherentComplexFrom (X := X) B m) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      LocalApproximationData X A B (max (m + a) (n + b)) U := by
  intro x
  obtain ⟨U, hxU, P₁, hP₁, α, hαiso, hαepi⟩ := hApc x
  obtain ⟨V, hxV, P₂, hP₂, β, hβiso, hβepi⟩ := hBpc x
  exact ⟨U ⊓ V, ⟨hxU, hxV⟩, localApproximationData_of_approximations X inf_le_left inf_le_right
    A B hAk hBk n m a b hna (restrictedIsLE_of_isStrictlyLE X A a hALE (U ⊓ V))
    (restrictedIsLE_of_isStrictlyLE X B b hBLE (U ⊓ V))
    P₁ hP₁ α hαiso hαepi P₂ hP₂ β hβiso hβepi⟩

/-- **The local step of Tag 09J3 part (2).**  For pseudo-coherent K-flat complexes `𝒜`, `ℬ` and
any integer `q`, every point lies in an open carrying the local data of degree `q`.

Neither factor is assumed bounded above, so the bounds are produced locally, which is the
source's reduction to an open covering.  A strictly perfect approximation of `𝒜` in degree `0`
over an open `U₀` has only finitely many nonzero terms, say none above `c`, so `𝒜|_{U₀}` lies in
`D^{≤ a}` for `a = max 0 c`; likewise `ℬ|_{V₀} ∈ D^{≤ b}`.  With those bounds in hand the
thresholds `n = min (q - b) a` and `m = min (q - a) b` give
`max (m + a, n + b) ≤ q` and `n ≤ a`, and approximations in those degrees exist over opens `U₁`,
`V₁`.  On the intersection of the four opens part (1)'s local step applies and
`AlgebraicGeometry.RingedSpace.LocalApproximationData.mono` raises its degree to `q`. -/
private theorem localApproximationData_of_isPseudoCoherentComplex
    (A B : CochainComplex (KFlatDerivedPullback.Modules X) ℤ)
    (hAk : Stacks.SheafOfModules.KFlat.KFlat X.sheaf A)
    (hBk : Stacks.SheafOfModules.KFlat.KFlat X.sheaf B)
    (hApc : IsPseudoCoherentComplex (X := X) A) (hBpc : IsPseudoCoherentComplex (X := X) B)
    (q : ℤ) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ LocalApproximationData X A B q U := by
  intro x
  obtain ⟨U₀, hxU₀, P₀, hP₀, α₀, hα₀iso, hα₀epi⟩ := hApc 0 x
  obtain ⟨V₀, hxV₀, Q₀, hQ₀, β₀, hβ₀iso, hβ₀epi⟩ := hBpc 0 x
  obtain ⟨c, hc⟩ := exists_isZero_X_of_lt hP₀
  obtain ⟨d, hd⟩ := exists_isZero_X_of_lt hQ₀
  obtain ⟨U₁, hxU₁, P₁, hP₁, α, hαiso, hαepi⟩ := hApc (min (q - max 0 d) (max 0 c)) x
  obtain ⟨V₁, hxV₁, P₂, hP₂, β, hβiso, hβepi⟩ := hBpc (min (q - max 0 c) (max 0 d)) x
  have hWU₀ : U₀ ⊓ U₁ ⊓ (V₀ ⊓ V₁) ≤ U₀ := le_trans inf_le_left inf_le_left
  have hWU₁ : U₀ ⊓ U₁ ⊓ (V₀ ⊓ V₁) ≤ U₁ := le_trans inf_le_left inf_le_right
  have hWV₀ : U₀ ⊓ U₁ ⊓ (V₀ ⊓ V₁) ≤ V₀ := le_trans inf_le_right inf_le_left
  have hWV₁ : U₀ ⊓ U₁ ⊓ (V₀ ⊓ V₁) ≤ V₁ := le_trans inf_le_right inf_le_right
  obtain ⟨α₀', hα₀'iso, -⟩ :=
    exists_restricted_approximation X hWU₀ A 0 P₀ α₀ hα₀iso hα₀epi
  obtain ⟨β₀', hβ₀'iso, -⟩ :=
    exists_restricted_approximation X hWV₀ B 0 Q₀ β₀ hβ₀iso hβ₀epi
  have hA : RestrictedIsLE X A (U₀ ⊓ U₁ ⊓ (V₀ ⊓ V₁)) (max 0 c) :=
    restrictedIsLE_of_approximation X A _ 0 c _
      (isZero_restrictModulesOfLE_X X hWU₀ P₀ c hc) α₀' hα₀'iso
  have hB : RestrictedIsLE X B (U₀ ⊓ U₁ ⊓ (V₀ ⊓ V₁)) (max 0 d) :=
    restrictedIsLE_of_approximation X B _ 0 d _
      (isZero_restrictModulesOfLE_X X hWV₀ Q₀ d hd) β₀' hβ₀'iso
  refine ⟨U₀ ⊓ U₁ ⊓ (V₀ ⊓ V₁), ⟨⟨hxU₀, hxU₁⟩, ⟨hxV₀, hxV₁⟩⟩,
    LocalApproximationData.mono X
      (localApproximationData_of_approximations X hWU₁ hWV₁ A B hAk hBk _ _ (max 0 c) (max 0 d)
        (min_le_right _ _) hA hB P₁ hP₁ α hαiso hαepi P₂ hP₂ β hβiso hβepi) ?_⟩
  have h1 : min (q - max 0 c) (max 0 d) + max 0 c ≤ q := by
    have := min_le_left (q - max 0 c) (max 0 d)
    omega
  have h2 : min (q - max 0 d) (max 0 c) + max 0 d ≤ q := by
    have := min_le_left (q - max 0 d) (max 0 c)
    omega
  exact max_le h1 h2

/-- **Tag 09J3, part (1).**  Let `(X, 𝒪_X)` be a ringed space and let `K`, `L` be objects of
`D(𝒪_X)`.  If `K` is `n`-pseudo-coherent with `H^i(K) = 0` for `i > a`, and `L` is
`m`-pseudo-coherent with `H^j(L) = 0` for `j > b`, then `K ⊗_{𝒪_X}^{𝐋} L` is
`t`-pseudo-coherent for `t = max (m + a, n + b)`.

If `a < n` then `t > a + b`, so the conclusion follows from right t-exactness of the derived
tensor product alone; that is
`Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_derivedTensorProduct_of_lt`.
Otherwise `n ≤ a`.  Both factors are replaced by K-flat representatives `𝒜`, `ℬ` with no terms
above their own bounds (Tag 06YQ through Tag 05T7); on those the derived tensor product is
`Tot(𝒜 ⊗_{𝒪_X} ℬ)` by the comparison of Tag 06YU, so that complex represents
`K ⊗^{𝐋} L` and is the one fed to Tag 08CC part (1).  Pseudo-coherence passes to `𝒜` and `ℬ` by
Tag 08CC part (2), and `AlgebraicGeometry.RingedSpace.localApproximationData` produces the
required local approximations in degree `t`. -/
@[stacks 09J3 "part (1)", sga "6 I 2.16" "special case"]
theorem isPseudoCoherentFrom_derivedTensorProduct
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf)
    (K L : DerivedCategory (KFlatDerivedPullback.Modules X)) (n m a b : ℤ)
    (hK : IsPseudoCoherentFrom (X := X) K n)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor (KFlatDerivedPullback.Modules X) i).obj K))
    (hL : IsPseudoCoherentFrom (X := X) L m)
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (KFlatDerivedPullback.Modules X) j).obj L)) :
    IsPseudoCoherentFrom (X := X) ((T.tensor.obj K).obj L) (max (m + a) (n + b)) := by
  rcases lt_or_ge a n with hna | hna
  · exact Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_derivedTensorProduct_of_lt
      X T K L n m a b hKa hLb (Or.inl hna)
  have hKLE : K.IsLE a := (DerivedCategory.isLE_iff K a).2 hKa
  have hLLE : L.IsLE b := (DerivedCategory.isLE_iff L b).2 hLb
  obtain ⟨A, hAk, hALE, ⟨eA⟩⟩ :=
    Stacks.DerivedTensor.RingedSite.exists_kFlat_isStrictlyLE_representative X.sheaf K a
  obtain ⟨B, hBk, hBLE, ⟨eB⟩⟩ :=
    Stacks.DerivedTensor.RingedSite.exists_kFlat_isStrictlyLE_representative X.sheaf L b
  have eG : DerivedCategory.Q.obj
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj A).obj B) ≅
      (T.tensor.obj K).obj L :=
    (T.comparison A B hAk hBk).symm ≪≫ (T.tensor.mapIso eA).app _ ≪≫
      (T.tensor.obj K).mapIso eB
  refine isPseudoCoherentFrom_of_local_derived_approximation
    ((T.tensor.obj K).obj L) (max (m + a) (n + b)) _ eG ?_
  exact localApproximationData X A B hAk hBk n m a b hna hALE hBLE
    (isPseudoCoherentComplexFrom_of_iso K n hK A eA)
    (isPseudoCoherentComplexFrom_of_iso L m hL B eB)

/-- **Tag 09J3, part (2).**  The derived tensor product of two pseudo-coherent objects of
`D(𝒪_X)` is pseudo-coherent.

Neither factor is assumed bounded above, so the representatives come from the unrestricted
K-flat resolutions of Tag 06YS rather than from a bounded one; `Tot(𝒜 ⊗_{𝒪_X} ℬ)` is then a
representative of `K ⊗^{𝐋} L`, and it suffices to see that it is `q`-pseudo-coherent as a
complex for every `q`.  By Tag 08CC that is `q`-pseudo-coherence of `K ⊗^{𝐋} L`, which
`AlgebraicGeometry.RingedSpace.localApproximationData_of_isPseudoCoherentComplex` supplies: the
cohomological bounds that part (1) needs are produced on an open covering, which is the source's
reduction to a covering on which both factors are bounded above. -/
@[stacks 09J3 "part (2)"]
theorem isPseudoCoherent_derivedTensorProduct
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf)
    (K L : DerivedCategory (KFlatDerivedPullback.Modules X))
    (hK : IsPseudoCoherent (X := X) K) (hL : IsPseudoCoherent (X := X) L) :
    IsPseudoCoherent (X := X) ((T.tensor.obj K).obj L) := by
  obtain ⟨P, ⟨eP⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  obtain ⟨P', ⟨eP'⟩⟩ : ∃ P', Nonempty (DerivedCategory.Q.obj P' ≅ L) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso L⟩⟩
  obtain ⟨A, f, hAk, -, hfq, -⟩ := KFlatDerivedPullback.exists_kFlatResolution X P
  obtain ⟨B, g, hBk, -, hgq, -⟩ := KFlatDerivedPullback.exists_kFlatResolution X P'
  have hf : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hfq
  have hg : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hgq
  have eA : DerivedCategory.Q.obj A ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ eP
  have eB : DerivedCategory.Q.obj B ≅ L := asIso (DerivedCategory.Q.map g) ≪≫ eP'
  have eG : DerivedCategory.Q.obj
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj A).obj B) ≅
      (T.tensor.obj K).obj L :=
    (T.comparison A B hAk hBk).symm ≪≫ (T.tensor.mapIso eA).app _ ≪≫
      (T.tensor.obj K).mapIso eB
  have hApc : IsPseudoCoherentComplex (X := X) A := fun q =>
    isPseudoCoherentComplexFrom_of_iso K q (hK.isPseudoCoherentFrom q) A eA
  have hBpc : IsPseudoCoherentComplex (X := X) B := fun q =>
    isPseudoCoherentComplexFrom_of_iso L q (hL.isPseudoCoherentFrom q) B eB
  refine ⟨_, fun q => isPseudoCoherentComplexFrom_of_iso ((T.tensor.obj K).obj L) q
    (isPseudoCoherentFrom_of_local_derived_approximation ((T.tensor.obj K).obj L) q _ eG
      (localApproximationData_of_isPseudoCoherentComplex X A B hAk hBk hApc hBpc q)) _ eG,
    ⟨eG⟩⟩

end Main

end AlgebraicGeometry.RingedSpace

end
