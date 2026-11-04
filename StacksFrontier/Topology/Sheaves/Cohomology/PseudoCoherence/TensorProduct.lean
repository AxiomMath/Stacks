module

public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.PullbackOfApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedCharacterization
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas

/-!
# Tensor products of pseudo-coherent complexes on a ringed space

Let `(X, 𝒪_X)` be a ringed space and let `K`, `L` be objects of `D(𝒪_X)`.
[Stacks, Tag 09J3](https://stacks.math.columbia.edu/tag/09J3) asserts

1. if `K` is `n`-pseudo-coherent with `H^i(K) = 0` for `i > a` and `L` is `m`-pseudo-coherent
   with `H^j(L) = 0` for `j > b`, then `K ⊗_{𝒪_X}^{𝐋} L` is `t`-pseudo-coherent for
   `t = max (m + a, n + b)`, and
2. if `K` and `L` are pseudo-coherent then so is `K ⊗_{𝒪_X}^{𝐋} L`.

The derived tensor product is the one of
[Stacks, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU), instantiated on the site
`Opens X` of the ringed space.

## Main results

* `Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_of_isLE`: an object of
  `D^{≤ t - 1}(𝒪_X)` is `t`-pseudo-coherent.
* `Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_derivedTensorProduct_of_lt`:
  part (1) in the range where one pseudo-coherence threshold exceeds the cohomological bound of
  its own factor.
* `Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_derivedTensorProduct` and
  `Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherent_derivedTensorProduct`: parts (1) and
  (2), assuming their complex-level form `Stacks.Cohomology.PseudoCoherentTensor.ComplexLevel`.
* `Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_canonicalDerivedTensorProduct` and
  `Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherent_canonicalDerivedTensorProduct`: the
  same for the canonical derived tensor product
  `Stacks.Cohomology.PseudoCoherentTensor.derivedTensorProduct`.

## Implementation notes

`Stacks.Cohomology.PseudoCoherentTensor.ComplexLevel` states parts (1) and (2) for the total
tensor complex of two K-flat complexes. The derived category is the one given by the local
instance `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
* [Stacks Project, Tag 09J3](https://stacks.math.columbia.edu/tag/09J3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect
open scoped ZeroObject

namespace Stacks.Cohomology.PseudoCoherentTensor

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-! ### The two spellings of pseudo-coherence -/

/-- The two families of complex-level pseudo-coherence predicates on a ringed space agree. -/
theorem isPseudoCoherentComplexFrom_families_iff
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) (m : ℤ) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom (X := X) E m ↔
      AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom (X := X) E m :=
  Iff.rfl

/-- The two families of derived-level pseudo-coherence predicates on a ringed space agree. -/
theorem isPseudoCoherentFrom_families_iff
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) (m : ℤ) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom (X := X) E m ↔
      AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X) E m :=
  Iff.rfl

/-! ### Pseudo-coherence from a cohomological bound -/

/-- An object of `D^{≤ t - 1}(𝒪_X)` is `t`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_isLE
    (E : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) (t : ℤ) (hE : E.IsLE (t - 1)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X) E t := by
  obtain ⟨P, ⟨eP⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ E) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso E⟩⟩
  have hPLE : P.IsLE (t - 1) :=
    (DerivedCategory.isLE_Q_obj_iff P (t - 1)).1
      (DerivedCategory.TStructure.t.isLE_of_iso eP.symm (t - 1))
  have hiso : IsIso (DerivedCategory.Q.map (P.ιTruncLE (t - 1))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  refine ⟨P.truncLE (t - 1), ?_, ⟨asIso (DerivedCategory.Q.map (P.ιTruncLE (t - 1))) ≪≫ eP⟩⟩
  intro x
  have hres : CochainComplex.IsStrictlyLE
      (AlgebraicGeometry.RingedSpace.restrictComplex (P.truncLE (t - 1)) ⊤) (t - 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (AlgebraicGeometry.RingedSpace.restrictModules X ⊤).isZero_obj
      ((P.truncLE (t - 1)).isZero_of_isStrictlyLE (t - 1) i hi)
  refine ⟨⊤, trivial, 0, StrictlyPerfect.isStrictlyPerfect_of_forall_isZero
    (fun i => (HomologicalComplex.eval _ _ i).isZero_obj (isZero_zero _)), 0, ?_, ?_⟩
  · intro j hj
    exact ⟨⟨0, ((HomologicalComplex.homologyFunctor _ _ j).isZero_obj
      (isZero_zero _)).eq_of_src _ _,
      (CochainComplex.isZero_of_isLE _ (t - 1) j (by lia)).eq_of_tgt _ _⟩⟩
  · have : IsIso (HomologicalComplex.homologyMap
        (0 : (0 : CochainComplex (StrictlyPerfect.OXMod.{u, u}
          (X.restrict (⊤ : Opens X.carrier).isOpenEmbedding)) ℤ) ⟶
          AlgebraicGeometry.RingedSpace.restrictComplex (P.truncLE (t - 1)) ⊤) t) :=
      ⟨⟨0, ((HomologicalComplex.homologyFunctor _ _ t).isZero_obj (isZero_zero _)).eq_of_src _ _,
        (CochainComplex.isZero_of_isLE _ (t - 1) t (by lia)).eq_of_tgt _ _⟩⟩
    infer_instance

/-! ### Tag 09J3 -/

/-- Part (1) of Tag 09J3 when `a < n` or `b < m`: if `H^i(K) = 0` for `i > a` and `H^j(L) = 0`
for `j > b`, then `K ⊗^𝐋 L` is `max (m + a, n + b)`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_derivedTensorProduct_of_lt
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf)
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) (n m a b
      : ℤ)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) i).obj K))
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) j).obj L))
    (hdeg : a < n ∨ b < m) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X)
      ((T.tensor.obj K).obj L) (max (m + a) (n + b)) := by
  have hKLE : K.IsLE a := (DerivedCategory.isLE_iff K a).2 hKa
  have hLLE : L.IsLE b := (DerivedCategory.isLE_iff L b).2 hLb
  have h₁ : ((T.tensor.obj K).obj L).IsLE (a + b) :=
    Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct X.sheaf T K L a b
  have h₂ : ((T.tensor.obj K).obj L).IsLE (max (m + a) (n + b) - 1) :=
    DerivedCategory.TStructure.t.isLE_of_le _ (a + b) _
      (by rcases hdeg with h | h <;> lia)
  exact isPseudoCoherentFrom_of_isLE X ((T.tensor.obj K).obj L) (max (m + a) (n + b)) h₂

/-- Tag 09J3 at the level of complexes: for K-flat complexes `P`, `Q` on a ringed space, the
total tensor complex satisfies the pseudo-coherence bounds of parts (1) and (2). -/
structure ComplexLevel : Prop where
  /-- Part (1) at the level of complexes. -/
  isPseudoCoherentComplexFrom_mapBifunctor :
    ∀ (Y : RingedSpace.{u, u}) (P Q : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) (n m a b : ℤ),
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y P →
        AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y Q →
      AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom (X := Y) P n →
      P.IsStrictlyLE a →
      AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom (X := Y) Q m →
      Q.IsStrictlyLE b →
      AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplexFrom (X := Y)
        (HomologicalComplex.mapBifunctor P Q (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
          (ComplexShape.up ℤ)) (max (m + a) (n + b))
  /-- Part (2) at the level of complexes. -/
  isPseudoCoherentComplex_mapBifunctor :
    ∀ (Y : RingedSpace.{u, u}) (P Q : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ),
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y P →
        AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y Q →
      AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplex (X := Y) P →
      AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplex (X := Y) Q →
      AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplex (X := Y)
        (HomologicalComplex.mapBifunctor P Q (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)
          (ComplexShape.up ℤ))

/-- Part (1) of Tag 09J3, assuming `ComplexLevel`: if `K` is `n`-pseudo-coherent with
`H^i(K) = 0` for `i > a` and `L` is `m`-pseudo-coherent with `H^j(L) = 0` for `j > b`, then
`K ⊗^𝐋 L` is `max (m + a, n + b)`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_derivedTensorProduct (h : ComplexLevel.{u})
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf)
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) (n m a b
      : ℤ)
    (hK : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X) K n)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) i).obj K))
    (hL : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X) L m)
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) j).obj L)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X)
      ((T.tensor.obj K).obj L) (max (m + a) (n + b)) := by
  have hKLE : K.IsLE a := (DerivedCategory.isLE_iff K a).2 hKa
  have hLLE : L.IsLE b := (DerivedCategory.isLE_iff L b).2 hLb
  obtain ⟨F, hFk, hFLE, ⟨eF⟩⟩ :=
    Stacks.DerivedTensor.RingedSite.exists_kFlat_isStrictlyLE_representative X.sheaf K a
  obtain ⟨G, hGk, hGLE, ⟨eG⟩⟩ :=
    Stacks.DerivedTensor.RingedSite.exists_kFlat_isStrictlyLE_representative X.sheaf L b
  have hFpc := Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso K n
    hK F eF
  have hGpc := Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso L m
    hL G eG
  exact ⟨_, h.isPseudoCoherentComplexFrom_mapBifunctor X F G n m a b hFk hGk hFpc hFLE hGpc hGLE,
    ⟨(Stacks.DerivedTensor.RingedSite.derivedTensorProductIso
      X.sheaf T hFk hGk eF eG).symm⟩⟩

/-- Part (2) of Tag 09J3, assuming `ComplexLevel`: if `K` and `L` are pseudo-coherent, then so
is `K ⊗^𝐋 L`. -/
theorem isPseudoCoherent_derivedTensorProduct (h : ComplexLevel.{u})
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf)
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hK : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X) K)
    (hL : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X) L) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X) ((T.tensor.obj K).obj L) := by
  obtain ⟨P, ⟨eP⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  obtain ⟨Q, ⟨eQ⟩⟩ : ∃ Q, Nonempty (DerivedCategory.Q.obj Q ≅ L) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso L⟩⟩
  obtain ⟨F, f, hFk, -, hfq, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution X P
  obtain ⟨G, g, hGk, -, hgq, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution X Q
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hfq
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hgq
  let eF : DerivedCategory.Q.obj F ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ eP
  let eG : DerivedCategory.Q.obj G ≅ L := asIso (DerivedCategory.Q.map g) ≪≫ eQ
  have hFpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplex (X := X) F := fun t =>
    Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso K t
      (AlgebraicGeometry.RingedSpace.IsPseudoCoherent.isPseudoCoherentFrom hK t) F eF
  have hGpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherentComplex (X := X) G := fun t =>
    Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso L t
      (AlgebraicGeometry.RingedSpace.IsPseudoCoherent.isPseudoCoherentFrom hL t) G eG
  exact ⟨_, h.isPseudoCoherentComplex_mapBifunctor X F G hFk hGk hFpc hGpc,
    ⟨(Stacks.DerivedTensor.RingedSite.derivedTensorProductIso
      X.sheaf T hFk hGk eF eG).symm⟩⟩

/-- The canonical derived tensor product of Tag 06YU on a ringed space. -/
abbrev derivedTensorProduct : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf :=
  Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf

/-- Part (1) of Tag 09J3 for the canonical derived tensor product, assuming `ComplexLevel`. -/
theorem isPseudoCoherentFrom_canonicalDerivedTensorProduct (h : ComplexLevel.{u})
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)) (n m a b
      : ℤ)
    (hK : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X) K n)
    (hKa : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) i).obj K))
    (hL : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X) L m)
    (hLb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) j).obj L)) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X)
      (((derivedTensorProduct X).tensor.obj K).obj L) (max (m + a) (n + b)) :=
  isPseudoCoherentFrom_derivedTensorProduct X h (derivedTensorProduct X) K L n m a b hK hKa hL hLb

/-- Part (2) of Tag 09J3 for the canonical derived tensor product, assuming `ComplexLevel`. -/
theorem isPseudoCoherent_canonicalDerivedTensorProduct (h : ComplexLevel.{u})
    (K L : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    (hK : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X) K)
    (hL : AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X) L) :
    AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X)
      (((derivedTensorProduct X).tensor.obj K).obj L) :=
  isPseudoCoherent_derivedTensorProduct X h (derivedTensorProduct X) K L hK hL

end Stacks.Cohomology.PseudoCoherentTensor

end
