module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDeltaBranchesDescent
public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.DeltaInvariantSeparableFieldChange
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.GeometricBranchesFieldChange
public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange

/-!
# Nodes and extension of the base field

Let `X` be a one-dimensional scheme locally of finite type over a field `k` — a locally
algebraic `k`-scheme of dimension one.  Whether a point of `X` is a closed point and a node does
not depend on the base field, in the following two senses.  First, for an extension `K / k` and
a point `y` of the base change `X_K` lying over `x`, the point `y` is a closed point and a node
of `X_K` over `K` exactly when `x` is one of `X` over `k`.  Second, if the base field `k'` of
`X` is itself a finite separable extension of a field `k`, then a point of `X` is a node over
`k'` exactly when it is a node for the composite `k`-scheme structure.

## Main results

* `Stacks.Curves.isNode_iff_of_fieldExtension` — being a closed point and a node is invariant
  under extension of the base field (Tag 0C56).
* `Stacks.Curves.isNode_iff_of_finiteSeparable_baseField` — being a node does not change when a
  finite separable subfield of the base field is used as the base field instead (Tag 0CD6).

## Implementation notes

The base change is the categorical pullback of the structure morphism along
`Spec K ⟶ Spec k`, viewed over `Spec K` through its second projection, and that a point lies
over another is recorded as an equality of its image under the first projection — the spellings
used by `Stacks.Curves.IsNode`.  Closedness of the point is part of `Stacks.Curves.IsNode`, so
the two closed-point conditions of the source are carried by the node predicates themselves
rather than stated separately.

For Tag 0C56 the source reduces to the case of algebraically closed fields, and so does the
proof here: the node condition over an arbitrary field is the condition that every point of the
base change to the algebraic closure be an ordinary double point
(`Stacks.Curves.isNode_iff_forall_isOrdinaryDoublePoint`), the two algebraic closures are
compared along `IsAlgClosed.lift`, and the two base changes are identified by
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`.  Over algebraically closed fields the node
condition is the numerical one of Tag 0C4D — reducedness of the local ring, delta invariant one
and two geometric branches, the separability clause being automatic over a perfect field — and
each of those three is invariant under extension of the base field.

That a closed point of the base change can map to a non-closed point of `X` is exactly the
subtlety the source points out.  It is ruled out by the node condition rather than assumed away:
a node has two geometric branches, geometric unibranchness is invariant under extension of the
base field (Tag 0C55), and a local ring of dimension zero is geometrically unibranch, so the
local ring at the image has dimension one and the image is closed.

Tag 0CD6 is deduced from Tag 0C56 together with the étale-locality of nodes (Tag 0C57).  The
graph of the structure morphism is a section of the first projection of
`X ×_{Spec k} Spec k'`, which is étale because `Spec k' ⟶ Spec k` is; a section of an étale
morphism is étale by `AlgebraicGeometry.Etale.of_comp`.

## References

* [Stacks Project, Tag 0C56](https://stacks.math.columbia.edu/tag/0C56)
* [Stacks Project, Tag 0CD6](https://stacks.math.columbia.edu/tag/0CD6)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C55](https://stacks.math.columbia.edu/tag/0C55)
* [Stacks Project, Tag 0C57](https://stacks.math.columbia.edu/tag/0C57)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.Curves

/-- Extension of the ground field does not change the dimension of a scheme locally of finite
type at a point. -/
private lemma topologicalKrullDimAt_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (y : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u})) :
    topologicalKrullDimAt
        (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}) y =
      topologicalKrullDimAt X
        ((pullback.fst f
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y) := by
  let Y := (pullback f
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})
  let g : Y ⟶ X :=
    pullback.fst f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let x := g.base y
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
  let : Algebra.FiniteType k Γ(X, U) := by
    show (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom).FiniteType
    exact (f.finiteType_appLE (isAffineOpen_top _) hU _).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let V : Y.Opens := g ⁻¹ᵁ U
  have hyV : y ∈ V := hxU
  obtain ⟨_, e, _hfst, _hsnd, hprime, _harrow⟩ :=
    affineBaseChangeLocalModel k K X f y U hU hxU
  let q : PrimeSpectrum (Γ(X, U) ⊗[k] K) := e.hom ⟨y, hyV⟩
  let : Algebra K (Γ(X, U) ⊗[k] K) := Algebra.TensorProduct.rightAlgebra
  calc
    topologicalKrullDimAt Y y = topologicalKrullDimAt (↥V) ⟨y, hyV⟩ :=
      Topology.IsOpenEmbedding.topologicalKrullDimAt_eq
        (IsOpen.isOpenEmbedding_subtypeVal V.2) ⟨y, hyV⟩
    _ = TopologicalSpace.localKrullDim (PrimeSpectrum (Γ(X, U) ⊗[k] K)) q := by
      rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim
        (PrimeSpectrum (Γ(X, U) ⊗[k] K)) q]
      exact topologicalKrullDimAt_eq_of_homeomorph e.hom.homeomorph ⟨y, hyV⟩
    _ = topologicalKrullDimAt X x := by
      rw [topologicalKrullDimAt_eq_affine_open x U hxU hU, ← hprime]
      exact (Algebra.IsPushout.localKrullDim_comap_eq k K Γ(X, U)
        (Γ(X, U) ⊗[k] K) q).symm

/-- The first projection of the base change of a scheme over a field along a field extension is
surjective. -/
private lemma surjective_base_baseChange_fst
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k)) :
    Function.Surjective (pullback.fst f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base := by
  have hg : Surjective (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    refine ⟨?_⟩
    intro z
    exact ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩
  have : Surjective (pullback.fst f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip hg
  exact (surjective_iff _).mp this

/-- The topological Krull dimension is unchanged by base change along a field extension. This is
`AlgebraicGeometry.topologicalKrullDim_baseChange` at the concrete pullback. -/
private lemma topologicalKrullDim_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f] :
    topologicalKrullDim
        (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}) = topologicalKrullDim X :=
  AlgebraicGeometry.topologicalKrullDim_baseChange k K
    (pullback.fst f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))) f
    (IsPullback.of_hasPullback _ _)

/-- A point of a scheme locally of finite type over a field lying over a closed point of the
base of a pullback square, and over a closed point of the new base, is itself closed. -/
private lemma isClosed_of_isPullback_of_isClosed
    {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {f' : X' ⟶ S'} {g' : X' ⟶ X} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (sq : IsPullback g' f' f g) (x' : X')
    (hxclosed : IsClosed ({g'.base x'} : Set X))
    (hbase : IsClosed ({f'.base x'} : Set S')) : IsClosed ({x'} : Set X') := by
  have hxFiber : IsClosed ({f.asFiber (g'.base x')} : Set (f.fiber (f.base (g'.base x')))) := by
    have h : IsClosed ({⟨g'.base x', by simp⟩} :
        Set (f.base ⁻¹' ({f.base (g'.base x')} : Set S))) := by
      convert hxclosed.preimage continuous_subtype_val using 1
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun hz => congrArg Subtype.val hz, fun hz => Subtype.ext hz⟩
    simpa [Scheme.Hom.asFiber] using
      (f.fiberHomeo (f.base (g'.base x'))).symm.isClosed_image.mpr h
  have hyFiber := AlgebraicGeometry.isClosed_asFiber_of_isPullback sq x' hxFiber
  have hfin := (AlgebraicGeometry.isClosed_asFiber_iff_finite_residueField f' x').mp hyFiber
  refine AlgebraicGeometry.isClosed_of_isAlgebraic_residueField f' x' ?_ hbase
  let := (f'.residueFieldMap x').hom.toAlgebra
  let : Module.Finite _ _ := hfin
  infer_instance

/-- A point of the base change of a scheme locally of finite type over a field along a field
extension is closed as soon as its image is. -/
theorem isClosed_singleton_baseChange_of_isClosed
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (y : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}))
    (hx : IsClosed ({(pullback.fst f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y} : Set X)) :
    IsClosed ({y} : Set
      (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u})) := by
  have : LocallyOfFiniteType (pullback.snd f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  exact isClosed_of_isPullback_of_isClosed (IsPullback.of_hasPullback _ _) y hx
    isClosed_singleton

/-- A local ring of Krull dimension zero is geometrically unibranch. -/
lemma isGeometricallyUnibranchRing_of_ringKrullDim_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] (hdim : ringKrullDim A = 0) :
    IsGeometricallyUnibranchRing A := by
  let : Ring.KrullDimLE 0 A := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mpr hdim
  have hnil : nilradical A = IsLocalRing.maximalIdeal A :=
    Ring.KrullDimLE.nilradical_eq_maximalIdeal A
  let R₀ := A ⧸ nilradical A
  let : (nilradical A).IsMaximal := by rw [hnil]; infer_instance
  let : Field R₀ := Ideal.Quotient.field (nilradical A)
  let C := integralClosure R₀ (FractionRing R₀)
  have hCsurj : Function.Surjective (algebraMap R₀ C) := by
    intro z
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral z.2
    exact ⟨r, Subtype.ext hr⟩
  let : IsLocalRing C := IsLocalRing.of_surjective' (algebraMap R₀ C) hCsurj
  let q : A →+* R₀ := Ideal.Quotient.mk _
  let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let F : A →+* C := (algebraMap R₀ C).comp q
  let : Algebra A C := F.toAlgebra
  let : IsLocalHom F := RingHom.isLocalHom_comp _ _
  unfold IsGeometricallyUnibranchRing
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hres : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)) := by
    intro z
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨r, rfl⟩ := hCsurj.comp Ideal.Quotient.mk_surjective z
    exact ⟨IsLocalRing.residue A r, IsLocalRing.ResidueField.algebraMap_residue r⟩
  exact ⟨Algebra.isIntegral_def.mpr fun z => by
      obtain ⟨r, rfl⟩ := hres z; exact isIntegral_algebraMap,
    fun z _ => hres z⟩

/-- A local ring of Krull dimension at most one which is not geometrically unibranch has Krull
dimension exactly one. -/
private lemma ringKrullDim_eq_one_of_not_isGeometricallyUnibranchRing
    (A : Type u) [CommRing A] [IsLocalRing A] (hle : ringKrullDim A ≤ 1)
    (hnot : ¬ IsGeometricallyUnibranchRing A) : ringKrullDim A = 1 := by
  have hnonneg : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  by_contra hne
  have hlt : ringKrullDim A < 1 := lt_of_le_of_ne hle hne
  have hzero : ringKrullDim A = 0 := by
    cases h : ringKrullDim A with
    | bot => exact absurd hnonneg (by simp [h])
    | coe d =>
        have hd : d < 1 := by simpa [h] using hlt
        simp [Order.lt_one_iff.mp hd]
  exact hnot (isGeometricallyUnibranchRing_of_ringKrullDim_eq_zero A hzero)

/-- A point of a one-dimensional scheme with two geometric branches has a local ring of
dimension one: a local ring of dimension zero is geometrically unibranch. -/
lemma ringKrullDim_stalk_eq_one_of_two_geometricBranches
    (Z : Scheme.{u}) (z : Z) (hZ : topologicalKrullDim Z = 1)
    (hbrZ : AlgebraicGeometry.numberOfGeometricBranches Z z = 2) :
    ringKrullDim (Z.presheaf.stalk z) = 1 := by
  refine ringKrullDim_eq_one_of_not_isGeometricallyUnibranchRing _
    (hZ ▸ ringKrullDim_stalk_le_topologicalKrullDim z) (fun huni => ?_)
  have h1 : AlgebraicGeometry.numberOfGeometricBranches Z z = 1 :=
    (AlgebraicGeometry.numberOfGeometricBranches_eq_one_iff Z z).mpr huni
  rw [hbrZ] at h1
  simp at h1

/-- A point at which a scheme of dimension at most `n` has local ring of dimension `n` is
closed. -/
private lemma isClosed_of_ringKrullDim_stalk_eq
    (X : Scheme.{u}) (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (x : X)
    (hdimx : ringKrullDim (X.presheaf.stalk x) = n) : IsClosed ({x} : Set X) := by
  have hbound (z : X) : Order.coheight z ≤ n := by
    have h := Order.coheight_le_krullDim z
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))] at h
    exact WithBot.coe_le_coe.mp (h.trans hdim)
  have hxco : Order.coheight x = n := by
    rw [ringKrullDim_stalk_eq_coheight] at hdimx
    exact WithBot.coe_inj.mp hdimx
  apply isClosed_of_closure_subset
  intro z hz
  have hzy : z ≤ x := specializes_iff_mem_closure.mpr hz
  refine Set.mem_singleton_iff.mpr ?_
  by_contra hne
  have hlt := Order.coheight_strictAnti (show z < x from ⟨hzy, fun hxz ↦
    hne ((hxz : Specializes z x).antisymm (hzy : Specializes x z)).eq⟩)
    (lt_of_le_of_lt (hbound x) (by simp : (n : ℕ∞) < ⊤))
  rw [hxco] at hlt
  exact (not_lt_of_ge (hbound z)) hlt

/-- A point with two geometric branches on a one-dimensional scheme is closed. -/
private lemma isClosed_of_two_geometricBranches
    (X : Scheme.{u}) (hdim : topologicalKrullDim X = 1) (x : X)
    (hbr : AlgebraicGeometry.numberOfGeometricBranches X x = 2) : IsClosed ({x} : Set X) :=
  isClosed_of_ringKrullDim_stalk_eq X 1 (by rw [hdim]; norm_num) x
    (by rw [ringKrullDim_stalk_eq_one_of_two_geometricBranches X x hdim hbr]; norm_num)

/-- **Over an algebraically closed field a closed point of a one-dimensional scheme locally of
finite type is a node exactly when its local ring is reduced with delta invariant one and two
geometric branches.**  Conditions (1) and (6) of Stacks Tag 0C4D, with the separability clause
dropped because it is automatic over a perfect field. -/
private lemma isNode_iff_isReduced_deltaInvariant_geometricBranches_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hdim : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    IsNode k X x ↔ (_root_.IsReduced (X.presheaf.stalk x) ∧
      Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
      AlgebraicGeometry.numberOfGeometricBranches X x = 2) := by
  let kToStalk : k →+* X.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  have h12 : IsNode k X x ↔ IsNodalAlgebra k (X.presheaf.stalk x) :=
    isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed k X x hx
  have h26 : IsNodalAlgebra k (X.presheaf.stalk x) ↔
      (Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            AlgebraicGeometry.numberOfGeometricBranches X x = 2) :=
    isNodalAlgebra_stalk_iff_deltaInvariant_eq_one_and_two_geometricBranches k X hdim x
  rw [h12, h26]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩,
    fun h => ⟨Algebra.isSeparableExtension_of_perfectField k (X.residueField x), h.1, h.2⟩⟩

/-- A flat morphism reflects reducedness of local rings. -/
private lemma isReduced_stalk_of_flat {X Y : Scheme.{u}} (p : Y ⟶ X) [Flat p] (y : Y)
    [_root_.IsReduced (Y.presheaf.stalk y)] :
    _root_.IsReduced (X.presheaf.stalk (p.base y)) := by
  algebraize [(p.stalkMap y).hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (p.base y)) (Y.presheaf.stalk y) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap p y) (p.toLRSHom.prop y)
  exact isReduced_of_injective (p.stalkMap y).hom
    ‹RingHom.FaithfullyFlat (p.stalkMap y).hom›.injective

/-- **Over algebraically closed fields, being a node is invariant under extension of the ground
field.**  Both sides are read off the numerical criterion of Stacks Tag 0C4D: reducedness, delta
invariant one and two geometric branches.  Each of the three is unchanged by the extension, and
the dimension of the local ring, hence closedness of the point, is forced by the two geometric
branches. -/
private lemma isNode_iff_baseChange_of_isAlgClosed
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X = 1)
    (y : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u})) :
    letI : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
    letI : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).Over (AlgebraicGeometry.Spec (.of K)) :=
      ⟨pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
    (IsNode k X ((pullback.fst f
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y) ↔
      IsNode K (pullback f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) y) := by
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback f g : Scheme.{u})
  let p : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
  let x := p.base y
  let : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
  let : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  have : LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k)) := by
    show LocallyOfFiniteType f; infer_instance
  have : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) := by
    show LocallyOfFiniteType q; infer_instance
  have : Flat g := Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) _)
  have hdimY : topologicalKrullDim Y = 1 := (topologicalKrullDim_baseChange k K X f).trans hdim
  have hbr : AlgebraicGeometry.numberOfGeometricBranches X x =
      AlgebraicGeometry.numberOfGeometricBranches Y y :=
    numberOfGeometricBranches_baseChange_fieldExtension k K X f x y rfl
  -- the normalization of a scheme over a perfect field has separable residue fields
  have hsep :
      (let Xnorm := normalizationSchemeOverField k f
       let ν := normalizationOverField k f
       ∀ x' : Xnorm, ν.base x' = x →
         let : Algebra k (Xnorm.residueField x') :=
           ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫
             Xnorm.Γevaluation x').hom.toAlgebra
         Algebra.IsSeparableExtension k (Xnorm.residueField x')) := by
    intro Xnorm ν x' _
    let : Algebra k (Xnorm.residueField x') :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (ν ≫ f).appTop ≫
        Xnorm.Γevaluation x').hom.toAlgebra
    exact Algebra.isSeparableExtension_of_perfectField k _
  constructor
  · intro hnode
    have hx : IsClosed ({x} : Set X) := hnode.isClosed
    have hy : IsClosed ({y} : Set Y) :=
      isClosed_singleton_baseChange_of_isClosed k K X f y hx
    obtain ⟨hred, hdelta, hbrX⟩ :=
      (isNode_iff_isReduced_deltaInvariant_geometricBranches_of_isAlgClosed k X hdim x hx).mp
        hnode
    have hbrY : AlgebraicGeometry.numberOfGeometricBranches Y y = 2 := hbr ▸ hbrX
    have : _root_.IsReduced (X.presheaf.stalk x) := hred
    have hredY : _root_.IsReduced (Y.presheaf.stalk y) :=
      isGeometricallyReducedAt_of_isReduced f x K y rfl
    have hdeltaEq := deltaInvariant_stalk_baseChange k K f x y rfl hred
      (ringKrullDim_stalk_eq_one_of_two_geometricBranches X x hdim hbrX) hsep
      (ringKrullDim_stalk_eq_one_of_two_geometricBranches Y y hdimY hbrY)
    exact (isNode_iff_isReduced_deltaInvariant_geometricBranches_of_isAlgClosed K Y hdimY y
      hy).mpr ⟨hredY, hdeltaEq ▸ hdelta, hbrY⟩
  · intro hnode
    have hy : IsClosed ({y} : Set Y) := hnode.isClosed
    obtain ⟨hredY, hdeltaY, hbrY⟩ :=
      (isNode_iff_isReduced_deltaInvariant_geometricBranches_of_isAlgClosed K Y hdimY y hy).mp
        hnode
    have hbrX : AlgebraicGeometry.numberOfGeometricBranches X x = 2 := hbr.trans hbrY
    have hdimA : ringKrullDim (X.presheaf.stalk x) = 1 :=
      ringKrullDim_stalk_eq_one_of_two_geometricBranches X x hdim hbrX
    have hx : IsClosed ({x} : Set X) := isClosed_of_two_geometricBranches X hdim x hbrX
    have : _root_.IsReduced (Y.presheaf.stalk y) := hredY
    have hredX : _root_.IsReduced (X.presheaf.stalk x) := isReduced_stalk_of_flat p y
    have hdeltaEq := deltaInvariant_stalk_baseChange k K f x y rfl hredX hdimA hsep
      (ringKrullDim_stalk_eq_one_of_two_geometricBranches Y y hdimY hbrY)
    exact (isNode_iff_isReduced_deltaInvariant_geometricBranches_of_isAlgClosed k X hdim x
      hx).mpr ⟨hredX, hdeltaEq.trans hdeltaY, hbrX⟩

/-- Over an algebraically closed field the node condition of Tag 0C47 and the
ordinary-double-point condition of Tag 0C1W agree: the base change to the algebraic closure is
then an isomorphism. -/
private lemma isNode_iff_isOrdinaryDoublePoint_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X) :
    IsNode k X x ↔ IsOrdinaryDoublePoint k X x := by
  let kToStalk : k →+* X.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  have hodp : IsOrdinaryDoublePoint k X x ↔
      IsClosed ({x} : Set X) ∧ IsNodalAlgebra k (X.presheaf.stalk x) :=
    isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk k X x
  constructor
  · intro h
    exact hodp.mpr ⟨h.isClosed,
      (isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed k X x h.isClosed).mp h⟩
  · intro h
    exact (isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed k X x h.isClosed).mpr
      (hodp.mp h).2

/-- The image of a node of the base change along a field extension is a closed point.  This is
the step of the source that rules out a closed point of `X_K` mapping to a non-closed point of
`X`: such an `x` would be a generic point, where `X` is geometrically unibranch, whereas a node
has two geometric branches and geometric unibranchness is invariant under extension of the
ground field. -/
private lemma isClosed_of_isNode_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X = 1) (x : X)
    (y : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}))
    (hy : (pullback.fst f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x)
    (hnode :
      letI : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).Over (AlgebraicGeometry.Spec (.of K)) :=
        ⟨pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
      IsNode K (pullback f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) y) :
    IsClosed ({x} : Set X) := by
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback f g : Scheme.{u})
  let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
  let : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  have : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) := by
    show LocallyOfFiniteType q; infer_instance
  have hdimY : topologicalKrullDim Y = 1 := (topologicalKrullDim_baseChange k K X f).trans hdim
  have hnode' : IsNode K Y y := hnode
  obtain ⟨-, -, hbrY⟩ :=
    isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode K Y
      hdimY y hnode'
  have hbrX : AlgebraicGeometry.numberOfGeometricBranches X x = 2 :=
    (numberOfGeometricBranches_baseChange_fieldExtension k K X f x y hy).trans hbrY
  exact isClosed_of_two_geometricBranches X hdim x hbrX

/-- **Stacks Project, Tag 0C56.**  Let `K / k` be an extension of fields and let `X` be a
one-dimensional scheme locally of finite type over `k`.  A point of the base change `X_K` is a
closed point and a node exactly when its image in `X` is.

Closedness of the point is part of `Stacks.Curves.IsNode`, so the two conditions of the source
are carried by the node predicates themselves rather than stated separately. -/
@[stacks 0C56]
theorem isNode_iff_of_fieldExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X = 1) (x : X)
    (y : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}))
    (hy : (pullback.fst f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y = x) :
    letI : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
    letI : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).Over (AlgebraicGeometry.Spec (.of K)) :=
      ⟨pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
    (IsNode k X x ↔
      IsNode K (pullback f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) y) := by
  let k' := AlgebraicClosure k
  let K' := AlgebraicClosure K
  let : Algebra k K' := ((algebraMap K K').comp (algebraMap k K)).toAlgebra
  let i : k' →ₐ[k] K' := IsAlgClosed.lift
  let : Algebra k' K' := i.toRingHom.toAlgebra
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let a : AlgebraicGeometry.Spec (.of k') ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let b : AlgebraicGeometry.Spec (.of K') ⟶ AlgebraicGeometry.Spec (.of K) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K K'))
  let c : AlgebraicGeometry.Spec (.of K') ⟶ AlgebraicGeometry.Spec (.of k') :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k' K'))
  have hbc : b ≫ g = c ≫ a := by
    show AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom i.toRingHom) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k k'))
    rw [← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
    congr 1
    ext t
    exact (i.commutes t).symm
  let Y := (pullback f g : Scheme.{u})
  let p : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
  let U := (pullback f a : Scheme.{u})
  let pU : U ⟶ X := pullback.fst f a
  let qU : U ⟶ AlgebraicGeometry.Spec (.of k') := pullback.snd f a
  let Z := (pullback q b : Scheme.{u})
  let pZ : Z ⟶ Y := pullback.fst q b
  let qZ : Z ⟶ AlgebraicGeometry.Spec (.of K') := pullback.snd q b
  let V := (pullback qU c : Scheme.{u})
  let pV : V ⟶ U := pullback.fst qU c
  let qV : V ⟶ AlgebraicGeometry.Spec (.of K') := pullback.snd qU c
  let e : Z ≅ V := pullbackLeftPullbackSndIso f g b ≪≫
    pullback.congrHom rfl hbc ≪≫ (pullbackLeftPullbackSndIso f a c).symm
  have he : e.hom ≫ qV = qZ := by
    simp [e, qV, qZ, qU, q, pullback.map, Category.assoc, pullback.lift_snd]
  have hep : e.hom ≫ pV ≫ pU = pZ ≫ p := by
    simp [e, pV, pU, pZ, p, qU, q, pullback.map, Category.assoc, pullback.lift_fst]
  let : X.Over (AlgebraicGeometry.Spec (.of k)) := ⟨f⟩
  let : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨q⟩
  let : U.Over (AlgebraicGeometry.Spec (.of k')) := ⟨qU⟩
  let : Z.Over (AlgebraicGeometry.Spec (.of K')) := ⟨qZ⟩
  let : V.Over (AlgebraicGeometry.Spec (.of K')) := ⟨qV⟩
  have : LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k)) := by
    show LocallyOfFiniteType f; infer_instance
  have hlftq : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
  have hlftqU : LocallyOfFiniteType qU :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f a))
  have : LocallyOfFiniteType (U ↘ AlgebraicGeometry.Spec (.of k')) := by
    show LocallyOfFiniteType qU; infer_instance
  have : LocallyOfFiniteType (Z ↘ AlgebraicGeometry.Spec (.of K')) := by
    show LocallyOfFiniteType qZ
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd q b))
  have : LocallyOfFiniteType (V ↘ AlgebraicGeometry.Spec (.of K')) := by
    show LocallyOfFiniteType qV
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd qU c))
  have hdimU : topologicalKrullDim U = 1 :=
    (topologicalKrullDim_baseChange k k' X f).trans hdim
  -- the ordinary-double-point condition transports between the two base changes
  have hbridge (z : Z) : IsOrdinaryDoublePoint K' Z z ↔
      IsOrdinaryDoublePoint k' U (pV.base (e.hom.base z)) := by
    have hZV : IsOrdinaryDoublePoint K' Z z ↔
        IsOrdinaryDoublePoint K' V (e.hom.base z) := by
      constructor
      · intro h
        refine isOrdinaryDoublePoint_of_isIso K' K' Z V e.inv (e.hom.base z) ?_
        have hzz : e.inv.base (e.hom.base z) = z := by
          rw [← Scheme.Hom.comp_apply, e.hom_inv_id]
          rfl
        rw [hzz]
        exact h
      · exact isOrdinaryDoublePoint_of_isIso K' K' V Z e.hom z
    have hUV : IsNode k' U (pV.base (e.hom.base z)) ↔ IsNode K' V (e.hom.base z) :=
      isNode_iff_baseChange_of_isAlgClosed k' K' U qU hdimU (e.hom.base z)
    rw [hZV, ← isNode_iff_isOrdinaryDoublePoint_of_isAlgClosed,
      ← isNode_iff_isOrdinaryDoublePoint_of_isAlgClosed]
    exact hUV.symm
  have hpoint (z : Z) (hz : pZ.base z = y) : pU.base (pV.base (e.hom.base z)) = x := by
    have hh := congrArg (fun m : Z ⟶ X => m.base z) hep
    change pU.base (pV.base (e.hom.base z)) = p.base (pZ.base z) at hh
    exact hh.trans ((congrArg p.base hz).trans hy)
  have hgeo (hxclosed : IsClosed ({x} : Set X)) :
      IsNode k X x ↔ ∀ u : U, pU.base u = x → IsOrdinaryDoublePoint k' U u :=
    isNode_iff_forall_isOrdinaryDoublePoint k X x hxclosed
  constructor
  · intro hx
    have hyclosed : IsClosed ({y} : Set Y) :=
      isClosed_singleton_baseChange_of_isClosed k K X f y (hy ▸ hx.isClosed)
    obtain ⟨z, hz⟩ := surjective_base_baseChange_fst K K' q y
    have hw := (hgeo hx.isClosed).mp hx (pV.base (e.hom.base z)) (hpoint z hz)
    exact ⟨hyclosed, z, hz, (hbridge z).mpr hw⟩
  · intro hyNode
    have hxclosed := isClosed_of_isNode_baseChange k K X f hdim x y hy hyNode
    obtain ⟨-, z, hz, hznode⟩ := hyNode
    exact ⟨hxclosed, pV.base (e.hom.base z), hpoint z hz, (hbridge z).mp hznode⟩

/-- The node condition depends on the structure morphism to the base field only through that
morphism, so equal structure morphisms give the same condition. -/
private lemma isNode_congr_structureMorphism {k : Type u} [Field k] {X : Scheme.{u}}
    (f₁ f₂ : X ⟶ AlgebraicGeometry.Spec (.of k)) (h : f₁ = f₂) (x : X) :
    @IsNode k _ X ⟨f₁⟩ x ↔ @IsNode k _ X ⟨f₂⟩ x := by
  subst h
  exact Iff.rfl

/-- **Stacks Project, Tag 0CD6.**  Let `k' / k` be a finite separable field extension and let `X`
be a one-dimensional scheme locally of finite type over `k'`.  A point of `X` is a node over `k'`
exactly when it is a node for the `k`-scheme structure obtained by composing with
`Spec k' ⟶ Spec k`.

The two conditions are joined through the base change `X ×_{Spec k} Spec k'`.  Its first
projection is étale, being a base change of the étale morphism `Spec k' ⟶ Spec k`, and the graph
of `f` is a section of that projection, hence itself étale.  Tag 0C56 identifies the node
condition over `k` with the one on the base change, and Tag 0C57 identifies the latter with the
node condition over `k'` on `X`. -/
@[stacks 0CD6, sga "7 XV 1.2.5" "ordinary case"]
theorem isNode_iff_of_finiteSeparable_baseField
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [Module.Finite k k']
    [Algebra.IsSeparable k k']
    (X : Scheme.{u}) (f : X ⟶ AlgebraicGeometry.Spec (.of k'))
    [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 1) (x : X) :
    letI : X.Over (AlgebraicGeometry.Spec (.of k')) := ⟨f⟩
    letI : X.Over (AlgebraicGeometry.Spec (.of k)) :=
      ⟨f ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k k'))⟩
    (IsNode k' X x ↔ IsNode k X x) := by
  let gk : AlgebraicGeometry.Spec (.of k') ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k k'))
  have halg : Algebra.Etale k k' :=
    ⟨Algebra.FormallyEtale.of_isSeparable k k',
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hgkEtale : Etale gk :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr halg)
  have hgkFinite : IsFinite gk := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hgkLft : LocallyOfFiniteType gk := inferInstance
  let fk : X ⟶ AlgebraicGeometry.Spec (.of k) := f ≫ gk
  have hfkLft : LocallyOfFiniteType fk := inferInstance
  let W := (pullback fk gk : Scheme.{u})
  let pW : W ⟶ X := pullback.fst fk gk
  let qW : W ⟶ AlgebraicGeometry.Spec (.of k') := pullback.snd fk gk
  let Δ : X ⟶ W := pullback.lift (𝟙 X) f (Category.id_comp fk)
  have hΔp : Δ ≫ pW = 𝟙 X := pullback.lift_fst _ _ _
  have hΔq : Δ ≫ qW = f := pullback.lift_snd _ _ _
  have hpEtale : Etale pW := inferInstanceAs (Etale (pullback.fst fk gk))
  have hΔEtale : Etale Δ := by
    have : Etale (Δ ≫ pW) := by rw [hΔp]; infer_instance
    exact Etale.of_comp Δ pW
  have hqLft : LocallyOfFiniteType qW :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd fk gk))
  have hdimW : topologicalKrullDim W = 1 :=
    (topologicalKrullDim_baseChange k k' X fk).trans hdim
  have hbase : pW.base (Δ.base x) = x := by
    have h := congrArg (fun m : X ⟶ X => m.base x) hΔp
    simpa using h
  have h1 : @IsNode k _ X ⟨fk⟩ x ↔ @IsNode k' _ W ⟨qW⟩ (Δ.base x) :=
    isNode_iff_of_fieldExtension k k' X fk hdim x (Δ.base x) hbase
  have h2 : @IsNode k' _ W ⟨qW⟩ (Δ.base x) ↔ @IsNode k' _ X ⟨Δ ≫ qW⟩ x :=
    isNode_iff_of_etale k' W X qW hdimW Δ x
  exact ((h1.trans h2).trans (isNode_congr_structureMorphism (Δ ≫ qW) f hΔq x)).symm

end Stacks.Curves

end
