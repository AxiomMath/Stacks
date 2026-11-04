module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionLocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotientDirectSum.RegularLocusOpen
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.BranchBound
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationBranches
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus

/-!
# The singular points of a component of a nodal curve

Let `X` be a one-dimensional at-worst-nodal scheme locally of finite type over a perfect field
`k`, and let `Y ⊆ X` be a reduced equidimensional closed subcurve with `X'` the scheme-theoretic
closure of `X ∖ Y`. Off `X'` the curve `Y` agrees with `X`, so smoothness and nodes pass between
them there; at the points of `Y ∩ X'` the subcurve is smooth ([Stacks, Tag 0E38]). So every
singular point of `Y` is a node of `X` lying off `X'`.

## Main results

* `AlgebraicGeometry.smoothAt_comp_of_isClosedImmersion_of_mem_opens`: a closed immersion which
  is surjective over an open `V` preserves smoothness at points over `V`.
* `AlgebraicGeometry.isNode_of_isClosedImmersion_of_mem_opens`: it reflects nodes there.
* `AlgebraicGeometry.isNode_comp_of_isClosedImmersion_of_mem_opens`: it preserves nodes there.
* `AlgebraicGeometry.isNode_and_notMem_of_mem_singularLocus_subscheme`: a singular point of the
  subcurve is a node of `X` off `X'`.
* `AlgebraicGeometry.encard_normalizationFiber_eq_two_of_isNode`: over an algebraically closed
  field the normalization has two points over a node.
* `AlgebraicGeometry.finrank_globalSections_eq_natCard_of_isReduced`: a reduced scheme finite over
  an algebraically closed field has `dim_k Γ` points.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0E69](https://stacks.math.columbia.edu/tag/0E69)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.Curves
open Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum
  (isClosed_singleton_of_not_mem_regularLocus)

universe u

namespace AlgebraicGeometry

/-- A closed immersion that is surjective over an open `V` restricts to an isomorphism over `V`. -/
private theorem isIso_morphismRestrict_of_subset_range {X Y : Scheme.{u}} (ι : Y ⟶ X)
    [IsReduced X] [IsClosedImmersion ι] (V : X.Opens) (hV : (V : Set X) ⊆ Set.range ι.base) :
    IsIso (ι ∣_ V) := by
  have hsurj : Surjective (ι ∣_ V) := by
    constructor
    intro v
    obtain ⟨y', hy'⟩ := hV v.2
    exact ⟨⟨y', show ι.base y' ∈ V from hy' ▸ v.2⟩,
      Subtype.ext ((morphismRestrict_base_coe ι V _).trans hy')⟩
  exact isIso_of_isClosedImmersion_of_surjective (ι ∣_ V)

/-- The restriction of `ι` over `V` followed by `V.ι` acts on points as `ι`. -/
private theorem base_morphismRestrict_comp_ι {X Y : Scheme.{u}} (ι : Y ⟶ X) (V : X.Opens) (y : Y)
    (hyV : ι.base y ∈ V) : ((ι ∣_ V) ≫ V.ι).base ⟨y, hyV⟩ = ι.base y := by
  rw [morphismRestrict_ι]
  rfl

/-- **A closed immersion into a reduced scheme, surjective over an open `V`, preserves
smoothness at points over `V`.** Over `V` the closed immersion is an isomorphism. -/
theorem smoothAt_comp_of_isClosedImmersion_of_mem_opens {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsReduced X] (f : X ⟶ Spec (.of k)) (ι : Y ⟶ X) [IsClosedImmersion ι] (V : X.Opens)
    (hV : (V : Set X) ⊆ Set.range ι.base) (y : Y) (hyV : ι.base y ∈ V)
    (h : InfinitesimalLifting.SmoothAt f (ι.base y)) :
    InfinitesimalLifting.SmoothAt (ι ≫ f) y := by
  have := isIso_morphismRestrict_of_subset_range ι V hV
  have hcomm : (ι ⁻¹ᵁ V).ι ≫ (ι ≫ f) = ((ι ∣_ V) ≫ V.ι) ≫ f := by
    rw [morphismRestrict_ι, Category.assoc]
  have hab := base_morphismRestrict_comp_ι ι V y hyV
  rw [← hab] at h
  have h1 := InfinitesimalLifting.smoothAt_comp_of_etale ((ι ∣_ V) ≫ V.ι) f ⟨y, hyV⟩ h
  rw [← hcomm] at h1
  exact (InfinitesimalLifting.smoothAt_comp_iff_of_etale (ι ⁻¹ᵁ V).ι (ι ≫ f) ⟨y, hyV⟩).1 h1

/-- **A closed immersion into a reduced scheme, surjective over an open `V`, reflects nodes at
points over `V`.** -/
theorem isNode_of_isClosedImmersion_of_mem_opens {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsReduced X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 1)
    (ι : Y ⟶ X) [IsClosedImmersion ι] (hYdim : topologicalKrullDim Y = 1) (V : X.Opens)
    (hV : (V : Set X) ⊆ Set.range ι.base) (y : Y) (hyV : ι.base y ∈ V)
    (h : @IsNode k _ Y ⟨ι ≫ f⟩ y) : @IsNode k _ X ⟨f⟩ (ι.base y) := by
  have := isIso_morphismRestrict_of_subset_range ι V hV
  have hcomm : (ι ⁻¹ᵁ V).ι ≫ (ι ≫ f) = ((ι ∣_ V) ≫ V.ι) ≫ f := by
    rw [morphismRestrict_ι, Category.assoc]
  have hab := base_morphismRestrict_comp_ι ι V y hyV
  have h1 : @IsNode k _ _ ⟨(ι ⁻¹ᵁ V).ι ≫ (ι ≫ f)⟩ ⟨y, hyV⟩ :=
    (isNode_iff_of_etale k Y _ (ι ≫ f) hYdim (ι ⁻¹ᵁ V).ι ⟨y, hyV⟩).1 h
  have h2 : @IsNode k _ _ ⟨((ι ∣_ V) ≫ V.ι) ≫ f⟩ ⟨y, hyV⟩ := by
    rwa [← hcomm]
  rw [← hab]
  exact (isNode_iff_of_etale k X _ f hdim ((ι ∣_ V) ≫ V.ι) ⟨y, hyV⟩).2 h2

/-- The complement of a closed subscheme lies in the closure of its complement. -/
theorem compl_support_subset_support_complementaryCurveIdeal {X : Scheme.{u}} [IsReduced X]
    (I : X.IdealSheafData) :
    (I.support : Set X)ᶜ ⊆ ((complementaryCurveIdeal I).support : Set X) := by
  intro x hx
  have h := Scheme.Hom.support_ker_eq_closure_range (Scheme.Opens.ι I.support.compl)
  rw [Scheme.Opens.range_ι] at h
  rw [show ((complementaryCurveIdeal I).support : Set X) =
    closure ((I.support : Set X)ᶜ) from congrArg (fun T : Closeds X => (T : Set X)) h]
  exact subset_closure hx

/-- **A singular point of a reduced equidimensional subcurve of a nodal curve is a node of the
curve lying off the closure of the complement of the subcurve**, over a perfect field. At the
points of `Y ∩ X'` the subcurve is smooth ([Stacks, Tag 0E38]); off `X'` it agrees with `X`, so a
point where `X` is smooth is a smooth point of `Y`. -/
theorem isNode_and_notMem_of_mem_singularLocus_subscheme {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [IsReduced X] (hX_equidimensional : Equidimensional X)
    (hX_dimension : topologicalKrullDim X = 1) (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1) (y : I.subscheme)
    (hy : y ∈ singularLocus I.subscheme) :
    IsNode k X (I.subschemeι.base y) ∧
      I.subschemeι.base y ∉ ((complementaryCurveIdeal I).support : Set X) := by
  have hloc := smoothAt_locus_eq_regular_locus k (I.subschemeι ≫ (X ↘ Spec (.of k)))
  have hns : ¬ InfinitesimalLifting.SmoothAt (I.subschemeι ≫ (X ↘ Spec (.of k))) y := by
    intro h
    have h' : y ∈ {x | InfinitesimalLifting.SmoothAt (I.subschemeι ≫ (X ↘ Spec (.of k))) x} := h
    rw [hloc] at h'
    exact hy h'
  have hnot : I.subschemeι.base y ∉ ((complementaryCurveIdeal I).support : Set X) := fun h =>
    hns (smoothAt_of_mem_support_complementaryCurveIdeal hX_equidimensional hX_dimension
      hX_nodal I hY_equidimensional hY_dimension y h)
  refine ⟨?_, hnot⟩
  have hycl : IsClosed ({y} : Set I.subscheme) :=
    isClosed_singleton_of_not_mem_regularLocus _ hY_dimension.le y hy
  have hxcl : IsClosed ({I.subschemeι.base y} : Set X) := by
    simpa using I.subschemeι.isClosedEmbedding.isClosedMap _ hycl
  rcases hX_nodal _ hxcl with hsm | hnd
  · exfalso
    let V : X.Opens := ⟨((complementaryCurveIdeal I).support : Set X)ᶜ,
      (complementaryCurveIdeal I).support.isClosed.isOpen_compl⟩
    have hV : (V : Set X) ⊆ Set.range I.subschemeι.base := by
      intro x hx
      rw [I.range_subschemeι]
      by_contra hxI
      exact hx (compl_support_subset_support_complementaryCurveIdeal I hxI)
    exact hns (smoothAt_comp_of_isClosedImmersion_of_mem_opens _ I.subschemeι V hV y hnot hsm)
  · exact hnd

/-- **A closed immersion into a reduced scheme, surjective over an open `V`, preserves nodes at
points over `V`.** -/
theorem isNode_comp_of_isClosedImmersion_of_mem_opens {k : Type u} [Field k] {X Y : Scheme.{u}}
    [IsReduced X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 1)
    (ι : Y ⟶ X) [IsClosedImmersion ι] (hYdim : topologicalKrullDim Y = 1) (V : X.Opens)
    (hV : (V : Set X) ⊆ Set.range ι.base) (y : Y) (hyV : ι.base y ∈ V)
    (h : @IsNode k _ X ⟨f⟩ (ι.base y)) : @IsNode k _ Y ⟨ι ≫ f⟩ y := by
  have := isIso_morphismRestrict_of_subset_range ι V hV
  have hcomm : (ι ⁻¹ᵁ V).ι ≫ (ι ≫ f) = ((ι ∣_ V) ≫ V.ι) ≫ f := by
    rw [morphismRestrict_ι, Category.assoc]
  have hab := base_morphismRestrict_comp_ι ι V y hyV
  rw [← hab] at h
  have h1 : @IsNode k _ _ ⟨((ι ∣_ V) ≫ V.ι) ≫ f⟩ ⟨y, hyV⟩ :=
    (isNode_iff_of_etale k X _ f hdim ((ι ∣_ V) ≫ V.ι) ⟨y, hyV⟩).1 h
  have h2 : @IsNode k _ _ ⟨(ι ⁻¹ᵁ V).ι ≫ (ι ≫ f)⟩ ⟨y, hyV⟩ := by
    rwa [hcomm]
  exact (isNode_iff_of_etale k Y _ (ι ≫ f) hYdim (ι ⁻¹ᵁ V).ι ⟨y, hyV⟩).2 h2

/-- **Over an algebraically closed field the normalization has exactly two points over a node.**
The number of points of the normalization above a point is the number of branches there
([Stacks, Tag 0C1S]), which over a separably closed residue field is the number of geometric
branches, two at a node. -/
theorem encard_normalizationFiber_eq_two_of_isNode {k : Type u} [Field k] [IsAlgClosed k]
    {W : Scheme.{u}} [W.Over (Spec (.of k))] [LocallyOfFiniteType (W ↘ Spec (.of k))]
    (hdim : topologicalKrullDim W = 1)
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) (w : W)
    (hnode : IsNode k W w) :
    Set.encard {z : W.normalizationScheme hW | W.normalization hW z = w} = 2 := by
  rw [← numberOfBranches_eq_encard_normalizationFiber W hW w,
    numberOfBranches_eq_numberOfBranchesOfLocalRing]
  let : Algebra k (W.residueField w) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (W ↘ Spec (.of k)).appTop ≫ W.Γevaluation w).hom.toAlgebra
  have hbij := bijective_algebraMap_residueField_of_isClosed (W ↘ Spec (.of k)) w hnode.isClosed
  have : IsAlgClosed (IsLocalRing.ResidueField (W.presheaf.stalk w)) :=
    IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hbij)
  rw [numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed,
    ← numberOfGeometricBranches_eq_numberOfGeometricBranchesOfLocalRing]
  exact (isReduced_and_deltaInvariant_eq_one_and_numberOfGeometricBranches_eq_two_of_isNode
    k W hdim w hnode).2.2

/-- **A reduced scheme finite over an algebraically closed field has as many points as the
dimension of its ring of global sections.** Each stalk is a reduced Artinian local ring, hence a
field, finite over `k` and therefore equal to `k`. -/
theorem finrank_globalSections_eq_natCard_of_isReduced (k : Type u) [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsFinite g] [IsReduced Y] :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.finrank k Γ(Y, ⊤) = Nat.card Y := by
  classical
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have := finite_of_isFinite_over_field k g
  have : Fintype Y := Fintype.ofFinite Y
  rw [finrank_globalSections_eq_finsum_finrank_stalk k g, finsum_eq_sum_of_fintype]
  have hterm : ∀ y : Y,
      (let : Algebra k (Y.presheaf.stalk y) :=
        ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
          ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
      Module.finrank k (Y.presheaf.stalk y)) = 1 := fun y => by
    let : Algebra k (Y.presheaf.stalk y) :=
      ((Y.presheaf.germ ⊤ y (by simp)).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom).toAlgebra
    have : Module.Finite k (Y.presheaf.stalk y) := finite_stalk_of_isFinite_over_field k g y
    have : IsArtinianRing (Y.presheaf.stalk y) := IsArtinianRing.of_finite k _
    have : _root_.IsReduced (Y.presheaf.stalk y) := isReduced_stalk_of_isReduced Y y
    let : Field (Y.presheaf.stalk y) :=
      (IsArtinianRing.isField_of_isReduced_of_isLocalRing (Y.presheaf.stalk y)).toField
    have hbij : Function.Bijective (algebraMap k (Y.presheaf.stalk y)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    have e : k ≃ₐ[k] Y.presheaf.stalk y := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_univ, Nat.card_eq_fintype_card]

end AlgebraicGeometry

end
