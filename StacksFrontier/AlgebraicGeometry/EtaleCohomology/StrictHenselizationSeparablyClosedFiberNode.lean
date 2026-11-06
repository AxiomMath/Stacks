module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CommonLemmas
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.EtaleLocalRingBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.RingTheory.Henselian.NodeBranches
public import StacksFrontier.RingTheory.Henselian.Quotient
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange

/-!
# The node and the strict henselization at it

Let `k` be an algebraically closed field in which `2 ≠ 0`, and let `S` be the nodal cubic
`y² = x²(1 + x)` over `k`, with `s̄` the geometric point at the node. The strict henselization
`𝒪^{sh}_{S,s̄}` acquires the two branches `y = ± x √(1 + x)` of the node. This file sets up the
data of the counterexample to Stacks Tag 0EZV as stated: the branch `e = y - x √(1 + x)`, the
scheme `X = Spec(𝒪^{sh}_{S,s̄} / e)` mapping to `S`, and two points of `Spec 𝒪^{sh}_{S,s̄}` with
values in one algebraically closed field `K`, lying over the same point of `S`, of which the
first lies on the branch and the second does not.

## Main definitions

* `Stacks.EtaleCohomology.NodeCounterexample.nodeScheme`, `nodePoint`: the node and its
  geometric point.
* `Stacks.EtaleCohomology.NodeCounterexample.branch`: the branch `y - x √(1 + x)` in the strict
  henselization.

## References

* [Stacks Project, Tag 0EZV](https://stacks.math.columbia.edu/tag/0EZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite

universe u

namespace Stacks.EtaleCohomology.NodeCounterexample

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The nodal cubic `y² = x²(1 + x)`. -/
abbrev nodeScheme : Scheme.{u} := Spec (.of (StacksDraft.Node.ring k))

/-- The geometric point at the node, given by evaluation at `t = 1` on the normalization. -/
abbrev nodePoint : GeometricPoint (nodeScheme k) where
  residueField := k
  hom := Spec.map (CommRingCat.ofHom (StacksDraft.Node.eval k 1 : StacksDraft.Node.ring k →+* k))

/-- The geometric point at the node lies over the maximal ideal of the node. -/
theorem nodePoint_hom_closedPoint :
    ((nodePoint k).hom (closedPoint k)).asIdeal = StacksDraft.Node.maximalIdeal k := by
  show (PrimeSpectrum.comap _ (closedPoint k)).asIdeal = _
  rw [PrimeSpectrum.comap_asIdeal]
  show Ideal.comap _ (maximalIdeal k) = _
  rw [maximalIdeal_eq_bot]
  ext a
  simp [RingHom.mem_ker]

/-- The local ring of the node at the singular point. -/
abbrev nodeLocalRing : CommRingCat.{u} :=
  (nodeScheme k).presheaf.stalk ((nodePoint k).hom (closedPoint k))

/-- The local ring of the node at the singular point as an algebra over the coordinate ring. -/
instance : Algebra (StacksDraft.Node.ring k) (nodeLocalRing k) :=
  StructureSheaf.stalkAlgebra _ _

/-- The local ring of the node at the singular point is the localization at its maximal ideal. -/
instance : IsLocalization.AtPrime (nodeLocalRing k) (StacksDraft.Node.maximalIdeal k) := by
  have hloc := StructureSheaf.IsLocalization.to_stalk (StacksDraft.Node.ring k)
    ((nodePoint k).hom (closedPoint k))
  have key : ∀ (I J : Ideal (StacksDraft.Node.ring k)) [I.IsPrime] [J.IsPrime], I = J →
      IsLocalization.AtPrime (nodeLocalRing k) I → IsLocalization.AtPrime (nodeLocalRing k) J := by
    rintro I J _ _ rfl h
    exact h
  have : ((nodePoint k).hom (closedPoint k)).asIdeal.IsPrime :=
    PrimeSpectrum.isPrime (R := StacksDraft.Node.ring k) _
  exact key _ _ (nodePoint_hom_closedPoint k) hloc

/-! ### The strict henselization at a geometric point over the node -/

section Henselization

variable {k} (B : BigEtaleSite.{u}) (hS : B.Contains (nodeScheme k))
  (s : GeometricPoint (nodeScheme k))
  (hs : (s.hom (closedPoint s.residueField)).asIdeal = StacksDraft.Node.maximalIdeal k)

/-- The local ring of the node at the image of a geometric point. -/
abbrev localRingAt : CommRingCat.{u} :=
  (nodeScheme k).presheaf.stalk (s.hom (closedPoint s.residueField))

/-- The local ring of the node at the image of `s` as an algebra over the coordinate ring. -/
instance : Algebra (StacksDraft.Node.ring k) (localRingAt s) :=
  StructureSheaf.stalkAlgebra _ _

include hs in
/-- At a geometric point over the singular point, the local ring of the node is the localization
at the maximal ideal of the node. -/
theorem isLocalization_localRingAt :
    IsLocalization.AtPrime (localRingAt s) (StacksDraft.Node.maximalIdeal k) := by
  have hloc := StructureSheaf.IsLocalization.to_stalk (StacksDraft.Node.ring k)
    (s.hom (closedPoint s.residueField))
  have key : ∀ (I J : Ideal (StacksDraft.Node.ring k)) [I.IsPrime] [J.IsPrime], I = J →
      IsLocalization.AtPrime (localRingAt s) I → IsLocalization.AtPrime (localRingAt s) J := by
    rintro I J _ _ rfl h
    exact h
  have : (s.hom (closedPoint s.residueField)).asIdeal.IsPrime :=
    PrimeSpectrum.isPrime (R := StacksDraft.Node.ring k) _
  exact key _ _ hs hloc

/-- The étale local ring at `s`, the strict henselization of the node. -/
abbrev shRing : Type u := ↥(etaleLocalRing B (nodeScheme k) hS s)

/-- The strict henselization of the node at `s` is flat over the local ring. -/
instance : Module.Flat (localRingAt s) (shRing B hS s) := by
  let T := geometricHenselizationTower (nodeScheme k) s
  have : Module.Flat (localRingAt s) T.strictHenselization :=
    Module.Flat.trans _ T.henselization _
  exact Module.Flat.of_linearEquiv
    (etaleLocalRingAlgEquivStrictHenselization B (nodeScheme k) hS s).symm.toLinearEquiv

/-- The strict henselization of the node at `s` is faithfully flat over the local ring. -/
instance : Module.FaithfullyFlat (localRingAt s) (shRing B hS s) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The strict henselization of the node at `s` is ind-étale over the local ring. -/
theorem indEtale_shRing : StacksDraft.IndEtale (localRingAt s) (shRing B hS s) :=
  indEtale_etaleLocalRing B (nodeScheme k) hS s

/-- The strict henselizations of the node at `s̄` computed in two big étale sites are isomorphic
as algebras over the local ring: both are the strict henselization of that local ring. -/
def shRingEquiv (B' : BigEtaleSite.{u}) (hS' : B'.Contains (nodeScheme k)) :
    shRing B hS s ≃ₐ[localRingAt s] shRing B' hS' s :=
  (etaleLocalRingAlgEquivStrictHenselization B _ hS s).symm.trans
    (etaleLocalRingAlgEquivStrictHenselization B' _ hS' s)

/-- The isomorphism `shRingEquiv` commutes with the germ maps from the local ring. -/
theorem shRingEquiv_comp_fromLocalRing (B' : BigEtaleSite.{u})
    (hS' : B'.Contains (nodeScheme k)) :
    ((shRingEquiv B hS s B' hS' : shRing B hS s ≃+* shRing B' hS' s) : shRing B hS s →+* _).comp
        (structureSheafStalkFromLocalRing B _ hS s) =
      structureSheafStalkFromLocalRing B' _ hS' s :=
  RingHom.ext fun r => (shRingEquiv B hS s B' hS').commutes r

variable {B hS s}

/-- The coordinate `x` in the local ring of the node. -/
abbrev xO : localRingAt s := algebraMap (StacksDraft.Node.ring k) _ (StacksDraft.Node.x k)

/-- The coordinate `y` in the local ring of the node. -/
abbrev yO : localRingAt s := algebraMap (StacksDraft.Node.ring k) _ (StacksDraft.Node.y k)

/-- The equation `y² = x²(1 + x)` of the node, in its local ring. -/
theorem yO_sq : yO (s := s) ^ 2 = xO ^ 2 * (1 + xO) := by
  have := congrArg (algebraMap (StacksDraft.Node.ring k) (localRingAt s))
    (StacksDraft.Node.y_sq k)
  simpa only [map_pow, map_mul, map_add, map_one] using this

include hs in
/-- The coordinate `x` lies in the maximal ideal of the local ring at the singular point. -/
theorem xO_mem : xO (s := s) ∈ maximalIdeal (localRingAt s) := by
  have := isLocalization_localRingAt s hs
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (localRingAt s)
    (StacksDraft.Node.maximalIdeal k)]
  exact StacksDraft.Node.x_mem_maximalIdeal k

include hs in
/-- The local ring of the node at the singular point is a domain. -/
theorem isDomain_localRingAt : IsDomain (localRingAt s) :=
  have := isLocalization_localRingAt s hs
  StacksDraft.Node.isDomain_localization (k := k) _

include hs in
/-- If `2 ≠ 0` in `k`, the coordinate `y` does not lie in the ideal `(x)` of the local ring at
the singular point. -/
theorem yO_not_mem_span (h2 : (2 : k) ≠ 0) : yO (s := s) ∉ Ideal.span {xO (s := s)} :=
  have := isLocalization_localRingAt s hs
  StacksDraft.Node.y_not_mem_span_x _ h2

include hs in
/-- If `2 ≠ 0` in `k`, then `2` is a unit in the strict henselization at the singular point. -/
theorem isUnit_two (h2 : (2 : k) ≠ 0) : IsUnit (2 : shRing B hS s) := by
  have := isLocalization_localRingAt s hs
  have : IsUnit (2 : localRingAt s) := by
    have h : (2 : localRingAt s) = algebraMap (StacksDraft.Node.ring k) _ 2 :=
      (map_ofNat _ 2).symm
    rw [h, IsLocalization.AtPrime.isUnit_to_map_iff (localRingAt s)
      (StacksDraft.Node.maximalIdeal k)]
    intro hmem
    apply h2
    have : (StacksDraft.Node.eval k 1) 2 = 0 := hmem
    rwa [map_ofNat] at this
  simpa only [map_ofNat] using this.map (algebraMap (localRingAt s) (shRing B hS s))

include hs in
/-- A square root of `1 + x` congruent to `1` in the strict henselization. -/
theorem exists_sqrt (h2 : (2 : k) ≠ 0) :
    ∃ v : shRing B hS s, v ^ 2 = 1 + algebraMap _ _ (xO (s := s)) ∧
      v - 1 ∈ maximalIdeal (shRing B hS s) :=
  HenselianLocalRing.exists_sq_eq_one_add (isUnit_two hs h2)
    (map_nonunit (algebraMap (localRingAt s) (shRing B hS s)) _ (xO_mem hs))

end Henselization

/-! ### The branch -/

section Branch

variable {k} (B : BigEtaleSite.{u}) (hS : B.Contains (nodeScheme k))
  {s : GeometricPoint (nodeScheme k)}
  (hs : (s.hom (closedPoint s.residueField)).asIdeal = StacksDraft.Node.maximalIdeal k)
  (h2 : (2 : k) ≠ 0)

/-- The chosen square root of `1 + x` congruent to `1` in the strict henselization. -/
def sqrtOnePlusX : shRing B hS s := (exists_sqrt (B := B) (hS := hS) hs h2).choose

/-- The square of `sqrtOnePlusX` is `1 + x`. -/
theorem sqrtOnePlusX_sq : sqrtOnePlusX B hS hs h2 ^ 2 = 1 + algebraMap _ _ (xO (s := s)) :=
  (exists_sqrt (B := B) (hS := hS) hs h2).choose_spec.1

/-- `sqrtOnePlusX` is congruent to `1` modulo the maximal ideal. -/
theorem sqrtOnePlusX_sub_one_mem : sqrtOnePlusX B hS hs h2 - 1 ∈ maximalIdeal (shRing B hS s) :=
  (exists_sqrt (B := B) (hS := hS) hs h2).choose_spec.2

/-- **The branch** `y - x √(1 + x)` of the node in its strict henselization. -/
def branch : shRing B hS s :=
  algebraMap _ _ (yO (s := s)) - 1 * algebraMap _ _ (xO (s := s)) * sqrtOnePlusX B hS hs h2

/-- The branch is nonzero. -/
theorem branch_ne_zero : branch B hS hs h2 ≠ 0 :=
  have := isDomain_localRingAt hs
  StacksDraft.NodeBranches.branch_ne_zero _ _ (yO_not_mem_span hs h2) 1 (Or.inl rfl)

/-- The ideal generated by the branch meets the local ring of the node only in `0`. -/
theorem comap_span_branch :
    Ideal.comap (algebraMap (localRingAt s) (shRing B hS s)) (Ideal.span {branch B hS hs h2}) = ⊥ :=
  have := isDomain_localRingAt hs
  StacksDraft.NodeBranches.comap_span_branch _ _ yO_sq (yO_not_mem_span hs h2)
    (sqrtOnePlusX_sq B hS hs h2) 1 (Or.inl rfl)

/-- The branch lies in the maximal ideal of the strict henselization. -/
theorem branch_mem_maximalIdeal : branch B hS hs h2 ∈ maximalIdeal (shRing B hS s) := by
  have hx := map_nonunit (algebraMap (localRingAt s) (shRing B hS s)) _ (xO_mem hs)
  have hy : algebraMap (localRingAt s) (shRing B hS s) yO ∈ maximalIdeal (shRing B hS s) := by
    apply map_nonunit
    have := isLocalization_localRingAt s hs
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (localRingAt s)
      (StacksDraft.Node.maximalIdeal k)]
    exact StacksDraft.Node.y_mem_maximalIdeal k
  unfold branch
  exact Submodule.sub_mem _ hy (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ 1 hx))

/-- **Two `K`-points of the strict henselization over one point of the node**, the first on the
branch and the second off it. -/
theorem exists_two_points :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (κ τ : shRing B hS s →+* K),
      κ.comp (algebraMap (localRingAt s) (shRing B hS s)) =
          τ.comp (algebraMap (localRingAt s) (shRing B hS s)) ∧
        κ (branch B hS hs h2) = 0 ∧ τ (branch B hS hs h2) ≠ 0 := by
  have := isDomain_localRingAt hs
  obtain ⟨K, _, _, κ, τ, h, -, hκ, hτ⟩ := StacksDraft.NodeBranches.exists_two_points
    (indEtale_shRing B hS s) (branch_ne_zero B hS hs h2) (comap_span_branch B hS hs h2)
  exact ⟨K, inferInstance, inferInstance, κ, τ, h, hκ, hτ⟩

end Branch

/-! ### The étale local ring at a point with strictly henselian local ring -/

section StrictlyHenselianStalk

variable (B : BigEtaleSite.{u}) {X : Scheme.{u}} (hX : B.Contains X) (x : GeometricPoint X)

/-- The residue field map from the local ring to the étale local ring is surjective when the
residue field of the local ring is separably closed. -/
private theorem surjective_residueFieldMap_etaleLocalRing_aux
    [IsSepClosed (ResidueField (X.presheaf.stalk (x.hom (closedPoint x.residueField))))] :
    Function.Surjective (ResidueField.map (algebraMap
      ↥(X.presheaf.stalk (x.hom (closedPoint x.residueField))) ↥(etaleLocalRing B X hX x))) := by
  have := isSepClosure_residueField_etaleLocalRing B X hX x
  exact IsSepClosed.algebraMap_surjective _ _

/-- **At a point whose local ring is henselian with separably closed residue field, the étale
local ring is the local ring**: the germ map from the local ring to the étale local ring is
bijective. -/
theorem bijective_structureSheafStalkFromLocalRing
    [HenselianLocalRing (X.presheaf.stalk (x.hom (closedPoint x.residueField)))]
    [IsSepClosed (ResidueField (X.presheaf.stalk (x.hom (closedPoint x.residueField))))] :
    Function.Bijective (structureSheafStalkFromLocalRing B X hX x) := by
  set O := ↥(X.presheaf.stalk (x.hom (closedPoint x.residueField)))
  set A := ↥(etaleLocalRing B X hX x)
  have hind := indEtale_etaleLocalRing B X hX x
  have hres := surjective_residueFieldMap_etaleLocalRing_aux B hX x
  let χ : A →ₐ[O] O := HenselianLocalRing.indEtaleAlgHom hind hres
  have hχ : IsLocalHom χ := HenselianLocalRing.isLocalHom_indEtaleAlgHom hind hres
  have : IsLocalHom (Algebra.ofId O A : O →+* A) := isLocalHom_algebraMap_etaleLocalRing B X hX x
  have hcomp : (Algebra.ofId O A).comp χ = AlgHom.id O A :=
    (HenselianLocalRing.indEtaleAlgHom_unique (Sh := A) hind hres _
      ⟨(RingHom.isLocalHom_comp (Algebra.ofId O A : O →+* A) (χ : A →+* O)).map_nonunit⟩).trans
      (HenselianLocalRing.indEtaleAlgHom_unique (Sh := A) hind hres _ ⟨fun _ ha => ha⟩).symm
  exact ⟨Function.LeftInverse.injective (g := χ) fun r => χ.commutes r,
    fun a => ⟨χ a, AlgHom.congr_fun hcomp a⟩⟩

/-- At a point whose local ring has separably closed residue field, the étale local ring has the
same residue field. -/
theorem surjective_residueFieldMap_etaleLocalRing
    [IsSepClosed (ResidueField (X.presheaf.stalk (x.hom (closedPoint x.residueField))))] :
    Function.Surjective (ResidueField.map (algebraMap
      ↥(X.presheaf.stalk (x.hom (closedPoint x.residueField))) ↥(etaleLocalRing B X hX x))) :=
  surjective_residueFieldMap_etaleLocalRing_aux B hX x

end StrictlyHenselianStalk

/-! ### The branch as a scheme over the node -/

section BranchScheme

variable {k} (B : BigEtaleSite.{u}) (hS : B.Contains (nodeScheme k))
  (s : GeometricPoint (nodeScheme k))
  (hs : (s.hom (closedPoint s.residueField)).asIdeal = StacksDraft.Node.maximalIdeal k)
  (h2 : (2 : k) ≠ 0)

/-- The coordinate ring `𝒪^{sh}_{S,s̄} / (y - x √(1 + x))` of the branch. -/
abbrev branchRing : Type u := shRing B hS s ⧸ Ideal.span {branch B hS hs h2}

/-- The ideal generated by the branch is proper. -/
theorem span_branch_ne_top : Ideal.span {branch B hS hs h2} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  exact (mem_maximalIdeal _).mp (branch_mem_maximalIdeal B hS hs h2)

/-- The coordinate ring of the branch is a local ring. -/
instance : IsLocalRing (branchRing B hS s hs h2) :=
  haveI : Nontrivial (branchRing B hS s hs h2) :=
    Ideal.Quotient.nontrivial_iff.mpr (span_branch_ne_top B hS s hs h2)
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- The branch, as a scheme. -/
abbrev branchScheme : Scheme.{u} := Spec (.of (branchRing B hS s hs h2))

/-- The branch maps to the node through the strict henselization. -/
def branchToNode : branchScheme B hS s hs h2 ⟶ nodeScheme k :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ strictHenselizationToBase B _ hS s

/-- Evaluation of étale germs at `s̄` kills the branch. -/
theorem toGeometricField_branch :
    structureSheafStalkToGeometricField B _ hS s (branch B hS hs h2) = 0 := by
  have := structureSheafStalkToGeometricField_isLocalHom B _ hS s
  by_contra h
  exact (mem_maximalIdeal _).mp (branch_mem_maximalIdeal B hS hs h2)
    (isUnit_of_map_unit _ _ (isUnit_iff_ne_zero.mpr h))

/-- Evaluation of étale germs at `s̄`, on the branch. -/
def branchToGeometricField : branchRing B hS s hs h2 →+* s.residueField :=
  Ideal.Quotient.lift _ (structureSheafStalkToGeometricField B _ hS s) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, toGeometricField_branch, mul_zero]

/-- The geometric point of the branch over `s̄`. -/
abbrev branchPoint : GeometricPoint (branchScheme B hS s hs h2) where
  residueField := s.residueField
  hom := Spec.map (CommRingCat.ofHom (branchToGeometricField B hS s hs h2))

/-- The geometric point of the branch, followed by the closed immersion of the branch, is the
geometric point of the strict henselization. -/
theorem branchPoint_hom_comp :
    (branchPoint B hS s hs h2).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {branch B hS hs h2}))) =
      geometricPointToStrictHenselization B _ hS s := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The geometric point of the branch, followed by `branchToNode`, is `s̄`. -/
theorem branchPoint_hom_comp_branchToNode :
    (branchPoint B hS s hs h2).hom ≫ branchToNode B hS s hs h2 = s.hom := by
  rw [branchToNode, ← Category.assoc, branchPoint_hom_comp]
  exact geometricPointToStrictHenselization_comp B _ hS s

/-- The geometric point of the branch lies over `s̄`. -/
theorem branchPoint_map : (branchPoint B hS s hs h2).map (branchToNode B hS s hs h2) = s := by
  have h := branchPoint_hom_comp_branchToNode B hS s hs h2
  cases s
  simp only [GeometricPoint.map]
  congr

end BranchScheme

/-! ### Transport of homomorphisms out of étale local rings -/

section Transport

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- Transport along `e : s = t` of a homomorphism out of the étale local ring, composed with the
germ map at `t`, is the original homomorphism composed with the germ map at `s`, after the
identification of the local rings at `s` and `t`. -/
theorem etaleLocalRingHomCongr_comp_fromLocalRing {T : Type u} [CommRing T]
    {s t : GeometricPoint S} (e : s = t) (φ : ↥(etaleLocalRing B S hS s) →+* T) :
    (etaleLocalRingHomCongr B hS e φ).comp (structureSheafStalkFromLocalRing B S hS t) =
      (φ.comp (structureSheafStalkFromLocalRing B S hS s)).comp
        (S.presheaf.stalkCongr (.of_eq (by rw [e]))).hom.hom := by
  subst e
  simp [etaleLocalRingHomCongr]

/-- Transport along `e.symm` undoes transport along `e`. -/
theorem etaleLocalRingHomCongr_symm {T : Type u} [CommRing T]
    {s t : GeometricPoint S} (e : s = t) (φ : ↥(etaleLocalRing B S hS s) →+* T) :
    etaleLocalRingHomCongr B hS e.symm (etaleLocalRingHomCongr B hS e φ) = φ := by
  subst e
  rfl

/-- Transport along an equality of geometric points preserves surjectivity. -/
theorem surjective_etaleLocalRingHomCongr {T : Type u} [CommRing T]
    {s t : GeometricPoint S} (e : s = t) {φ : ↥(etaleLocalRing B S hS s) →+* T}
    (hφ : Function.Surjective φ) : Function.Surjective (etaleLocalRingHomCongr B hS e φ) := by
  subst e
  exact hφ

/-- An element killed by one homomorphism and not by another persists through transport along
an equality of geometric points. -/
theorem exists_etaleLocalRingHomCongr {T T' : Type u} [CommRing T] [CommRing T']
    {s t : GeometricPoint S} (e : s = t) {φ : ↥(etaleLocalRing B S hS s) →+* T}
    {φ' : ↥(etaleLocalRing B S hS s) →+* T'} (h : ∃ b, φ b = 0 ∧ φ' b ≠ 0) :
    ∃ b, etaleLocalRingHomCongr B hS e φ b = 0 ∧ etaleLocalRingHomCongr B hS e φ' b ≠ 0 := by
  subst e
  exact h

end Transport

/-! ### The étale local ring of the branch -/

section BranchLocalRing

variable {k} (B₀ : BigEtaleSite.{u}) (hS₀ : B₀.Contains (nodeScheme k))
  (s : GeometricPoint (nodeScheme k))
  (hs : (s.hom (closedPoint s.residueField)).asIdeal = StacksDraft.Node.maximalIdeal k)
  (h2 : (2 : k) ≠ 0)

/-- Evaluation of étale germs at `s̄` on the branch is a local homomorphism. -/
instance : IsLocalHom (branchToGeometricField B₀ hS₀ s hs h2) := by
  have := structureSheafStalkToGeometricField_isLocalHom B₀ _ hS₀ s
  refine ⟨fun a ha => ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (isUnit_of_map_unit (structureSheafStalkToGeometricField B₀ _ hS₀ s) r ha).map _

/-- The coordinate ring of the branch is a henselian local ring. -/
instance : HenselianLocalRing (branchRing B₀ hS₀ s hs h2) :=
  Stacks.Henselian.henselianLocalRing_quotient (span_branch_ne_top B₀ hS₀ s hs h2)

/-- The residue field of the coordinate ring of the branch is separably closed. -/
instance : IsSepClosed (ResidueField (branchRing B₀ hS₀ s hs h2)) := by
  have := etaleLocalRing_strictHenselian B₀ _ hS₀ s
  have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {branch B₀ hS₀ hs h2})) :=
    .of_surjective _ Ideal.Quotient.mk_surjective
  let φ := ResidueField.map (Ideal.Quotient.mk (Ideal.span {branch B₀ hS₀ hs h2}))
  refine IsSepClosed.of_ringEquiv (M := ResidueField (shRing B₀ hS₀ s))
    (RingEquiv.ofBijective φ ⟨φ.injective, fun c => ?_⟩).symm
  obtain ⟨r, rfl⟩ := (residue_surjective.comp Ideal.Quotient.mk_surjective) c
  exact ⟨residue _ r, ResidueField.map_residue _ r⟩

/-- The geometric point of the branch lies over the closed point of the branch. -/
theorem branchPoint_hom_closedPoint :
    (branchPoint B₀ hS₀ s hs h2).hom (closedPoint s.residueField) =
      closedPoint (branchRing B₀ hS₀ s hs h2) :=
  have : IsLocalHom (CommRingCat.ofHom (branchToGeometricField B₀ hS₀ s hs h2)).hom :=
    inferInstanceAs (IsLocalHom (branchToGeometricField B₀ hS₀ s hs h2))
  Spec_closedPoint (f := CommRingCat.ofHom (branchToGeometricField B₀ hS₀ s hs h2))

/-- The local ring of the branch at its geometric point is the coordinate ring of the branch. -/
def branchStalkIso :
    (branchScheme B₀ hS₀ s hs h2).presheaf.stalk
        ((branchPoint B₀ hS₀ s hs h2).hom (closedPoint s.residueField)) ≅
      CommRingCat.of (branchRing B₀ hS₀ s hs h2) :=
  (branchScheme B₀ hS₀ s hs h2).presheaf.stalkCongr
      (.of_eq (branchPoint_hom_closedPoint B₀ hS₀ s hs h2)) ≪≫
    stalkClosedPointIso (CommRingCat.of (branchRing B₀ hS₀ s hs h2))

/-- The local ring of the branch at its geometric point is henselian. -/
instance : HenselianLocalRing ((branchScheme B₀ hS₀ s hs h2).presheaf.stalk
    ((branchPoint B₀ hS₀ s hs h2).hom (closedPoint s.residueField))) :=
  HenselianLocalRing.of_ringEquiv (branchStalkIso B₀ hS₀ s hs h2).commRingCatIsoToRingEquiv.symm

/-- The local ring of the branch at its geometric point has separably closed residue field. -/
instance : IsSepClosed (ResidueField ((branchScheme B₀ hS₀ s hs h2).presheaf.stalk
    ((branchPoint B₀ hS₀ s hs h2).hom (closedPoint s.residueField)))) :=
  IsSepClosed.of_ringEquiv (ResidueField.mapEquiv
    (branchStalkIso B₀ hS₀ s hs h2).commRingCatIsoToRingEquiv)

variable (B : BigEtaleSite.{u}) (hS : B.Contains (nodeScheme k))
  (hX : B.Contains (branchScheme B₀ hS₀ s hs h2))

/-- The coordinate ring of the branch is the étale local ring of the branch at its geometric
point. -/
def branchEtaleLocalRingEquiv :
    branchRing B₀ hS₀ s hs h2 ≃+* ↥(etaleLocalRing B _ hX (branchPoint B₀ hS₀ s hs h2)) :=
  (branchStalkIso B₀ hS₀ s hs h2).commRingCatIsoToRingEquiv.symm.trans
    (RingEquiv.ofBijective _ (bijective_structureSheafStalkFromLocalRing B hX
      (branchPoint B₀ hS₀ s hs h2)))

end BranchLocalRing

/-! ### Transport of the strict henselization along an equality of geometric points -/

section TransportEquiv

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- The étale local rings at equal geometric points are isomorphic, compatibly with the germ maps
from the ordinary local rings. -/
theorem exists_etaleLocalRingEquiv_of_eq {s t : GeometricPoint S} (e : s = t) :
    ∃ τ : ↥(etaleLocalRing B S hS s) ≃+* ↥(etaleLocalRing B S hS t),
      ∀ r, τ (structureSheafStalkFromLocalRing B S hS s r) =
        structureSheafStalkFromLocalRing B S hS t
          ((S.presheaf.stalkCongr (.of_eq (by rw [e]))).hom r) := by
  subst e
  refine ⟨RingEquiv.refl _, fun r => ?_⟩
  simp only [RingEquiv.refl_apply, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl]
  rfl

end TransportEquiv

/-! ### The morphism of strict henselizations along the branch -/

section BranchMap

variable {k} (B₀ : BigEtaleSite.{u}) (hS₀ : B₀.Contains (nodeScheme k))
  (s : GeometricPoint (nodeScheme k))
  (hs : (s.hom (closedPoint s.residueField)).asIdeal = StacksDraft.Node.maximalIdeal k)
  (h2 : (2 : k) ≠ 0)

/-- The image of the geometric point of the branch. -/
abbrev branchImage : GeometricPoint (nodeScheme k) :=
  (branchPoint B₀ hS₀ s hs h2).map (branchToNode B₀ hS₀ s hs h2)

/-- The image of the geometric point of the branch lies over the maximal ideal of the node. -/
theorem branchImage_hs :
    ((branchImage B₀ hS₀ s hs h2).hom
        (closedPoint (branchImage B₀ hS₀ s hs h2).residueField)).asIdeal =
      StacksDraft.Node.maximalIdeal k := by
  have key : ∀ t : GeometricPoint (nodeScheme k), t = s →
      (t.hom (closedPoint t.residueField)).asIdeal = StacksDraft.Node.maximalIdeal k := by
    rintro t rfl
    exact hs
  exact key _ (branchPoint_map B₀ hS₀ s hs h2)

/-- `branchToNode` sends the point underlying the geometric point of the branch to the point
underlying `s̄`. -/
theorem branchToNode_branchPoint :
    (branchToNode B₀ hS₀ s hs h2) ((branchPoint B₀ hS₀ s hs h2).hom (closedPoint s.residueField)) =
      s.hom (closedPoint s.residueField) :=
  congrArg (fun g : (branchPoint B₀ hS₀ s hs h2).source ⟶ nodeScheme k =>
    g.base (closedPoint s.residueField)) (branchPoint_hom_comp_branchToNode B₀ hS₀ s hs h2)

/-- The ring map underlying the branch: the germ map of `s̄` followed by the quotient. -/
abbrev branchRingHom : (nodeScheme k).presheaf.stalk (s.hom (closedPoint s.residueField)) ⟶
    CommRingCat.of (branchRing B₀ hS₀ s hs h2) :=
  CommRingCat.ofHom ((Ideal.Quotient.mk (Ideal.span {branch B₀ hS₀ hs h2})).comp
    (structureSheafStalkFromLocalRing B₀ _ hS₀ s))

/-- The ring map underlying the branch is a local homomorphism. -/
instance : IsLocalHom (branchRingHom B₀ hS₀ s hs h2).hom := by
  have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {branch B₀ hS₀ hs h2})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (structureSheafStalkFromLocalRing B₀ _ hS₀ s) :=
    isLocalHom_algebraMap_etaleLocalRing B₀ _ hS₀ s
  exact RingHom.isLocalHom_comp _ _

/-- `branchToNode` is `Spec` of `branchRingHom` followed by the canonical morphism from the
spectrum of the local ring at `s̄`. -/
theorem branchToNode_eq :
    branchToNode B₀ hS₀ s hs h2 = Spec.map (branchRingHom B₀ hS₀ s hs h2) ≫
      (nodeScheme k).fromSpecStalk (s.hom (closedPoint s.residueField)) := by
  rw [branchToNode, strictHenselizationToBase, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- **The stalk computation along the branch**: the map of local rings of `branchToNode` at the
geometric point of the branch is the germ map of `s̄` followed by the quotient. -/
theorem stalkMap_branchToNode_comp_branchStalkIso :
    (branchToNode B₀ hS₀ s hs h2).stalkMap
        ((branchPoint B₀ hS₀ s hs h2).hom (closedPoint s.residueField)) ≫
      (branchStalkIso B₀ hS₀ s hs h2).hom =
    ((nodeScheme k).presheaf.stalkCongr (.of_eq (branchToNode_branchPoint B₀ hS₀ s hs h2))).hom ≫
      branchRingHom B₀ hS₀ s hs h2 := by
  have hx₀ := branchPoint_hom_closedPoint B₀ hS₀ s hs h2
  have hfc : (branchToNode B₀ hS₀ s hs h2) (closedPoint (branchRing B₀ hS₀ s hs h2)) =
      s.hom (closedPoint s.residueField) := by
    rw [← hx₀]; exact branchToNode_branchPoint B₀ hS₀ s hs h2
  have G : ((nodeScheme k).presheaf.stalkCongr (.of_eq hfc.symm)).hom ≫
      Scheme.stalkClosedPointTo (branchToNode B₀ hS₀ s hs h2) = branchRingHom B₀ hS₀ s hs h2 :=
    Scheme.stalkCongr_comp_stalkClosedPointTo_of_eq _ _ (branchToNode_eq B₀ hS₀ s hs h2) hfc
  have hcomp := Scheme.stalkMap_congr_point (branchToNode B₀ hS₀ s hs h2) hx₀
  simp only [branchStalkIso, Iso.trans_hom, ← Category.assoc]
  rw [hcomp, Category.assoc]
  show _ ≫ Scheme.stalkClosedPointTo (branchToNode B₀ hS₀ s hs h2) = _
  rw [← G, ← Category.assoc]
  congr 1
  simp only [TopCat.Presheaf.stalkCongr_hom]
  exact (TopCat.Presheaf.stalkSpecializes_comp _ _ _).symm

end BranchMap

section BranchMapIdentification

variable {k} (B₀ : BigEtaleSite.{u}) (hS₀ : B₀.Contains (nodeScheme k))
  (s : GeometricPoint (nodeScheme k))
  (hs : (s.hom (closedPoint s.residueField)).asIdeal = StacksDraft.Node.maximalIdeal k)
  (h2 : (2 : k) ≠ 0) (B : BigEtaleSite.{u}) (hS : B.Contains (nodeScheme k))
  (hX : B.Contains (branchScheme B₀ hS₀ s hs h2))

include hs in
/-- The residue field of the local ring of the node at the singular point, which is the base
field, is separably closed. -/
theorem isSepClosed_residueField_localRingAt :
    IsSepClosed (ResidueField (localRingAt s)) := by
  have := isLocalization_localRingAt s hs
  have : IsSepClosed k := IsSepClosed.of_isAlgClosed k
  have hsurj : Function.Surjective (StacksDraft.Node.eval k 1) :=
    fun a => ⟨algebraMap k _ a, AlgHom.commutes _ a⟩
  let e₁ := IsLocalization.AtPrime.equivQuotMaximalIdeal (StacksDraft.Node.maximalIdeal k)
    (localRingAt s)
  let e₂ := (Ideal.quotientKerAlgEquivOfSurjective hsurj).toRingEquiv
  exact IsSepClosed.of_ringEquiv (M := k) (N := ResidueField (localRingAt s))
    (e₁.toRingEquiv.symm.trans e₂)

/-- The homomorphism of strict henselizations along the branch, read at `s̄`. -/
def branchEtaleLocalRingHom :
    shRing B hS s →+* ↥(etaleLocalRing B _ hX (branchPoint B₀ hS₀ s hs h2)) :=
  etaleLocalRingHomCongr B hS (branchPoint_map B₀ hS₀ s hs h2)
    (etaleLocalRingHom B hX hS (branchToNode B₀ hS₀ s hs h2) (branchPoint B₀ hS₀ s hs h2))

/-- The homomorphism of strict henselizations along the branch is a local homomorphism. -/
instance : IsLocalHom (branchEtaleLocalRingHom B₀ hS₀ s hs h2 B hS hX) :=
  isLocalHom_etaleLocalRingHomCongr B hS _ _ inferInstance

/-- The homomorphism of strict henselizations along the branch, composed with the germ map of
the node, is the germ map followed by the quotient by the branch. -/
theorem branchEtaleLocalRingHom_comp_fromLocalRing :
    (branchEtaleLocalRingHom B₀ hS₀ s hs h2 B hS hX).comp
        (structureSheafStalkFromLocalRing B _ hS s) =
      (branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX).toRingHom.comp
        (branchRingHom B₀ hS₀ s hs h2).hom := by
  rw [branchEtaleLocalRingHom, etaleLocalRingHomCongr_comp_fromLocalRing,
    etaleLocalRingHom_comp_fromLocalRing]
  have hst := congrArg (fun φ => φ ≫ (branchStalkIso B₀ hS₀ s hs h2).inv)
    (stalkMap_branchToNode_comp_branchStalkIso B₀ hS₀ s hs h2)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hst
  rw [hst]
  have hsc : ∀ {x y : nodeScheme k} (h : Inseparable x y) (h' : Inseparable y x) r,
      ((nodeScheme k).presheaf.stalkCongr h').hom.hom
        (((nodeScheme k).presheaf.stalkCongr h).hom.hom r) = r := by
    intro x y h h' r
    simp only [TopCat.Presheaf.stalkCongr_hom]
    exact Scheme.stalkSpecializes_stalkSpecializes_apply _ _ r
  ext r
  exact congrArg (fun z => structureSheafStalkFromLocalRing B _ hX (branchPoint B₀ hS₀ s hs h2)
    ((branchStalkIso B₀ hS₀ s hs h2).inv.hom ((branchRingHom B₀ hS₀ s hs h2).hom z))) (hsc _ _ r)

/-- Two local homomorphisms out of an ind-étale local algebra with the same residue field into a
henselian local ring agree as soon as they agree on the base. -/
theorem eq_of_comp_algebraMap_eq {R Rh Sh : Type u} [CommRing R] [CommRing Rh] [CommRing Sh]
    [IsLocalRing R] [IsLocalRing Rh] [HenselianLocalRing Sh] [Algebra R Rh]
    [IsLocalHom (algebraMap R Rh)] (hind : StacksDraft.IndEtale R Rh)
    (hres : Function.Surjective (ResidueField.map (algebraMap R Rh)))
    (f g : Rh →+* Sh) (hf : IsLocalHom f) (hg : IsLocalHom g)
    (h : f.comp (algebraMap R Rh) = g.comp (algebraMap R Rh)) : f = g := by
  let : Algebra R Sh := (f.comp (algebraMap R Rh)).toAlgebra
  have : IsLocalHom (algebraMap R Sh) := RingHom.isLocalHom_comp f _
  let F : Rh →ₐ[R] Sh := { toRingHom := f, commutes' := fun _ => rfl }
  let G : Rh →ₐ[R] Sh := { toRingHom := g, commutes' := fun r => (RingHom.congr_fun h r).symm }
  exact congrArg AlgHom.toRingHom
    ((HenselianLocalRing.indEtaleAlgHom_unique hind hres F ⟨hf.map_nonunit⟩).trans
      (HenselianLocalRing.indEtaleAlgHom_unique hind hres G ⟨hg.map_nonunit⟩).symm)

/-- **The homomorphism of strict henselizations along the branch is the quotient by the
branch**, after the identification of the strict henselizations computed in the two sites, and
followed by the identification of the coordinate ring of the branch with its étale local ring. -/
theorem branchEtaleLocalRingHom_eq :
    branchEtaleLocalRingHom B₀ hS₀ s hs h2 B hS hX =
      ((branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX).toRingHom.comp
        (Ideal.Quotient.mk _)).comp
          ((shRingEquiv B hS s B₀ hS₀ : shRing B hS s ≃+* shRing B₀ hS₀ s) :
            shRing B hS s →+* shRing B₀ hS₀ s) := by
  have hcomp : IsLocalHom (((branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX).toRingHom.comp
      (Ideal.Quotient.mk (Ideal.span {branch B₀ hS₀ hs h2}))).comp
        ((shRingEquiv B hS s B₀ hS₀ : shRing B hS s ≃+* shRing B₀ hS₀ s) :
          shRing B hS s →+* shRing B₀ hS₀ s)) :=
    .of_surjective _ (((branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX).surjective.comp
      Ideal.Quotient.mk_surjective).comp (shRingEquiv B hS s B₀ hS₀).surjective)
  have : IsLocalHom (algebraMap (localRingAt s) (shRing B hS s)) :=
    isLocalHom_algebraMap_etaleLocalRing B _ hS s
  have : HenselianLocalRing ↥(etaleLocalRing B _ hX (branchPoint B₀ hS₀ s hs h2)) :=
    henselianLocalRing_etaleLocalRing B _ hX _
  refine eq_of_comp_algebraMap_eq (R := localRingAt s) (Rh := shRing B hS s)
    (Sh := ↥(etaleLocalRing B _ hX (branchPoint B₀ hS₀ s hs h2)))
    (indEtale_etaleLocalRing B _ hS s)
    (@surjective_residueFieldMap_etaleLocalRing B _ hS s
      (isSepClosed_residueField_localRingAt s hs)) _ _ inferInstance hcomp ?_
  rw [algebraMap_etaleLocalRing, branchEtaleLocalRingHom_comp_fromLocalRing, RingHom.comp_assoc,
    shRingEquiv_comp_fromLocalRing]
  rfl

end BranchMapIdentification

/-! ### The two points and the fibres of the branch over them -/

/-- The fibre of `Spec A ⟶ Spec R` over a point `Spec K ⟶ Spec R` is empty as soon as some element
of `R` vanishes in `A` but not in `K`. -/
theorem isEmpty_pullback_specMap {R A : CommRingCat.{u}} {K : Type u} [Field K] (ψ : R ⟶ A)
    (τ : R ⟶ CommRingCat.of K) (b : R) (hb0 : ψ b = 0) (hb : τ b ≠ 0) :
    IsEmpty ↥(pullback (Spec.map ψ) (Spec.map τ) : Scheme.{u}) := by
  refine ⟨fun p => ?_⟩
  have hpt := congrArg (fun g => g.base p) (pullback.condition (f := Spec.map ψ) (g := Spec.map τ))
  have h1 : b ∈ ((Spec.map ψ).base ((pullback.fst (Spec.map ψ) (Spec.map τ)).base p)).asIdeal := by
    rw [Spec.map_base]
    show ψ b ∈ ((pullback.fst (Spec.map ψ) (Spec.map τ)).base p).asIdeal
    rw [hb0]
    exact zero_mem _
  have h2 : b ∈ ((Spec.map τ).base ((pullback.snd (Spec.map ψ) (Spec.map τ)).base p)).asIdeal := by
    have : (Spec.map ψ).base ((pullback.fst (Spec.map ψ) (Spec.map τ)).base p) =
        (Spec.map τ).base ((pullback.snd (Spec.map ψ) (Spec.map τ)).base p) := hpt
    rw [← this]
    exact h1
  rw [Spec.map_base] at h2
  change τ b ∈ ((pullback.snd (Spec.map ψ) (Spec.map τ)).base p).asIdeal at h2
  have hprime : ((pullback.snd (Spec.map ψ) (Spec.map τ)).base p).asIdeal.IsPrime :=
    PrimeSpectrum.isPrime _
  rw [Ideal.eq_bot_of_prime ((pullback.snd (Spec.map ψ) (Spec.map τ)).base p).asIdeal,
    Ideal.mem_bot] at h2
  exact hb h2

section Points

variable {k} (B₀ : BigEtaleSite.{u}) (hS₀ : B₀.Contains (nodeScheme k))
  (s : GeometricPoint (nodeScheme k))
  (hs : (s.hom (closedPoint s.residueField)).asIdeal = StacksDraft.Node.maximalIdeal k)
  (h2 : (2 : k) ≠ 0) (B : BigEtaleSite.{u}) (hS : B.Contains (nodeScheme k))
  (hX : B.Contains (branchScheme B₀ hS₀ s hs h2))
  {K : Type u} [Field K] (κ τ : shRing B₀ hS₀ s →+* K)

/-- A point of the strict henselization at `s̄`, given in the site of the branch, read in the
site `B` at the image of the geometric point of the branch. -/
abbrev pointAtImage (φ : shRing B₀ hS₀ s →+* K) :
    Spec (.of K) ⟶ strictHenselization B _ hS (branchImage B₀ hS₀ s hs h2) :=
  Spec.map (CommRingCat.ofHom (etaleLocalRingHomCongr B hS (branchPoint_map B₀ hS₀ s hs h2).symm
    (φ.comp ((shRingEquiv B hS s B₀ hS₀ : shRing B hS s ≃+* shRing B₀ hS₀ s) :
      shRing B hS s →+* shRing B₀ hS₀ s))))

/-- The morphism of strict henselizations along the branch is `Spec` of
`branchEtaleLocalRingHom`, transported to the image of the geometric point of the branch. -/
theorem strictHenselizationSquareMap_branch :
    strictHenselizationSquareMap B hX hS (branchToNode B₀ hS₀ s hs h2)
        (branchPoint B₀ hS₀ s hs h2) =
      Spec.map (CommRingCat.ofHom (etaleLocalRingHomCongr B hS
        (branchPoint_map B₀ hS₀ s hs h2).symm
          (branchEtaleLocalRingHom B₀ hS₀ s hs h2 B hS hX))) := by
  rw [branchEtaleLocalRingHom, etaleLocalRingHomCongr_symm]
  rfl

/-- The morphism of strict henselizations along the branch is a monomorphism. -/
instance : Mono (strictHenselizationSquareMap B hX hS (branchToNode B₀ hS₀ s hs h2)
    (branchPoint B₀ hS₀ s hs h2)) := by
  rw [strictHenselizationSquareMap_branch]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (etaleLocalRingHomCongr B hS
      (branchPoint_map B₀ hS₀ s hs h2).symm
        (branchEtaleLocalRingHom B₀ hS₀ s hs h2 B hS hX)))) :=
    .spec_of_surjective _ <| surjective_etaleLocalRingHomCongr B hS _ <| by
      rw [branchEtaleLocalRingHom_eq]
      exact ((branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX).surjective.comp
        Ideal.Quotient.mk_surjective).comp (shRingEquiv B hS s B₀ hS₀).surjective
  infer_instance

/-- **The fibre of the branch over a point on the branch is the point itself.** -/
theorem isIso_pullback_snd_of_branch (hκ : κ (branch B₀ hS₀ hs h2) = 0) :
    IsIso (pullback.snd (strictHenselizationSquareMap B hX hS (branchToNode B₀ hS₀ s hs h2)
      (branchPoint B₀ hS₀ s hs h2)) (pointAtImage B₀ hS₀ s hs h2 B hS κ)) := by
  let κ' : branchRing B₀ hS₀ s hs h2 →+* K := Ideal.Quotient.lift _ κ fun a ha =>
    (Ideal.span_singleton_le_iff_mem _).2 (RingHom.mem_ker.2 hκ) ha
  let κbar := κ'.comp (branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX).symm.toRingHom
  have hfac : pointAtImage B₀ hS₀ s hs h2 B hS κ = Spec.map (CommRingCat.ofHom κbar) ≫
      strictHenselizationSquareMap B hX hS (branchToNode B₀ hS₀ s hs h2)
        (branchPoint B₀ hS₀ s hs h2) := by
    have hκ' : κ.comp ((shRingEquiv B hS s B₀ hS₀ : shRing B hS s ≃+* shRing B₀ hS₀ s) :
        shRing B hS s →+* shRing B₀ hS₀ s) =
        κbar.comp (((branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX).toRingHom.comp
          (Ideal.Quotient.mk _)).comp
            ((shRingEquiv B hS s B₀ hS₀ : shRing B hS s ≃+* shRing B₀ hS₀ s) :
              shRing B hS s →+* shRing B₀ hS₀ s)) := by
      ext r
      show κ _ = κ' ((branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX).symm
        ((branchEtaleLocalRingEquiv B₀ hS₀ s hs h2 B hX) (Ideal.Quotient.mk _ _)))
      rw [RingEquiv.symm_apply_apply]
      rfl
    rw [strictHenselizationSquareMap_branch, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← etaleLocalRingHomCongr_comp, branchEtaleLocalRingHom_eq, ← hκ']
  rw [hfac]
  exact pullback_snd_iso_of_right_factors_mono _ _

/-- **The fibre of the branch over a point off the branch is empty.** -/
theorem isEmpty_pullback_of_not_branch (hτ : τ (branch B₀ hS₀ hs h2) ≠ 0) :
    IsEmpty ↥(pullback (strictHenselizationSquareMap B hX hS (branchToNode B₀ hS₀ s hs h2)
      (branchPoint B₀ hS₀ s hs h2)) (pointAtImage B₀ hS₀ s hs h2 B hS τ) : Scheme.{u}) := by
  set ψ := ((shRingEquiv B hS s B₀ hS₀ : shRing B hS s ≃+* shRing B₀ hS₀ s) :
    shRing B hS s →+* shRing B₀ hS₀ s)
  obtain ⟨b, hb0, hb⟩ := exists_etaleLocalRingHomCongr B hS (branchPoint_map B₀ hS₀ s hs h2).symm
    (φ := branchEtaleLocalRingHom B₀ hS₀ s hs h2 B hS hX) (φ' := τ.comp ψ)
      ⟨(shRingEquiv B hS s B₀ hS₀).symm (branch B₀ hS₀ hs h2), by
        rw [branchEtaleLocalRingHom_eq]
        simp, by
        simpa [ψ] using hτ⟩
  rw [strictHenselizationSquareMap_branch]
  exact isEmpty_pullback_specMap _ _ b hb0 hb

/-- Two points of the strict henselization at `s̄` lying over the same point of the node still do
so when read in the site `B` at the image of the geometric point of the branch. -/
theorem pointAtImage_comp_toBase
    (h : κ.comp (structureSheafStalkFromLocalRing B₀ _ hS₀ s) =
      τ.comp (structureSheafStalkFromLocalRing B₀ _ hS₀ s)) :
    pointAtImage B₀ hS₀ s hs h2 B hS τ ≫
        strictHenselizationToBase B _ hS (branchImage B₀ hS₀ s hs h2) =
      pointAtImage B₀ hS₀ s hs h2 B hS κ ≫
        strictHenselizationToBase B _ hS (branchImage B₀ hS₀ s hs h2) := by
  have h' : (τ.comp ((shRingEquiv B hS s B₀ hS₀ : shRing B hS s ≃+* shRing B₀ hS₀ s) :
      shRing B hS s →+* shRing B₀ hS₀ s)).comp (structureSheafStalkFromLocalRing B _ hS s) =
      (κ.comp ((shRingEquiv B hS s B₀ hS₀ : shRing B hS s ≃+* shRing B₀ hS₀ s) :
      shRing B hS s →+* shRing B₀ hS₀ s)).comp (structureSheafStalkFromLocalRing B _ hS s) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, shRingEquiv_comp_fromLocalRing, h]
  simp only [pointAtImage, strictHenselizationToBase, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, etaleLocalRingHomCongr_comp_fromLocalRing, h']

end Points

end Stacks.EtaleCohomology.NodeCounterexample
