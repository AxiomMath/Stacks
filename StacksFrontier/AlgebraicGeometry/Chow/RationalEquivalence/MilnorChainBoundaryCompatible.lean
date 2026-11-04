module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointClosureImmersionBoundary

/-!
# The degreewise localization sequence and the first differential of Stacks 0GU9

Stacks 0GUA asserts that the degreewise split short exact sequences of locally finite Milnor
K-chains attached to an open subscheme and its closed complement are compatible with the two
differentials of the complex of Stacks 0GU9. This file proves that compatibility for the *first*
differential, the tame-symbol boundary `K₂ ⟶ K₁`.

Both squares reduce to one point at a time. The coefficient of the boundary at a point `x'` is a
locally finite sum of local contributions over the points `x` of relative dimension `k + 2`, and
the contribution of `x` vanishes unless `x` specializes to `x'`. Restriction to an open subscheme
therefore loses nothing: a point specializing into the open subscheme lies in it, because the
intersection of the open subscheme with the closure of the point is a nonempty open subset of
that closure and so contains its generic point. What remains is that the local contributions
agree, which is
`Stacks.Chow.pointClosureMilnorBoundary_isOpenImmersion`.

## Main results

* `Stacks.Chow.milnorKTransport_pointwiseMilnorBoundaryTerm_comap` — the local contributions
  agree.
* `Stacks.Chow.milnorChainComap_pointwiseMilnorBoundary` — **Stacks 0GUA** for the first
  differential and the restriction map: restriction to the open subscheme commutes with the
  tame-symbol differential.
* `Stacks.Chow.pointwiseMilnorBoundary_milnorChainExtend` — **Stacks 0GUA** for the first
  differential and the extension-by-zero map from the closed complement.

## References

* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- A locally finite sum over the target of an injection whose terms vanish off its range is the
sum of the composed terms over the source. -/
theorem finsum_eq_finsum_of_injective {A B M : Type*} [AddCommMonoid M] (f : A → B)
    (hf : Function.Injective f) (g : B → M) (hg : ∀ b, b ∉ Set.range f → g b = 0) :
    (∑ᶠ b, g b) = ∑ᶠ a, g (f a) := by
  classical
  rw [← finsum_emb_domain' hf fun a ↦ g (f a)]
  refine finsum_congr fun b ↦ ?_
  split_ifs with hb
  · rw [hb.choose_spec]
  · exact hg b hb

variable (C : ChowSituation.{u}) {X U Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- **The local contributions to the first differential of Stacks 0GU9 agree on an open
subscheme.** The contribution of a point `w` of the open subscheme to the coefficient at a point
`u` of it is the contribution of its image to the coefficient at the image of `u`, transported
along the identification of the residue fields. -/
theorem milnorKTransport_pointwiseMilnorBoundaryTerm_comap (k : ℤ)
    (a : PointwiseKTwoGroup C p k) (w : pointsOfDimension C (j ≫ p) (k + 2))
    (u : pointsOfDimension C (j ≫ p) (k + 1)) :
    milnorKTransport
        (immersionResidueFieldEquiv j (bijective_residueFieldMap_openImmersion j) u.1 :
          _ →+* _) 1
        (pointwiseMilnorBoundaryTerm C p k a
          (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 2) w)
          (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 1) u)) =
      pointwiseMilnorBoundaryTerm C (j ≫ p) k
        (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) (k + 2) 2 a) w u := by
  by_cases hspec : (w.1 : U) ⤳ (u.1 : U)
  · have hspecX : (j.base w.1 : X) ⤳ (j.base u.1 : X) := hspec.map j.continuous
    have hdimU := ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one
      C (j ≫ p) hspec (by
        rw [(mem_pointsOfDimension C (j ≫ p)).mp w.2,
          (mem_pointsOfDimension C (j ≫ p)).mp u.2]
        ring)
    have hdimX := ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one
      C p hspecX (by
        rw [(mem_pointsOfDimension C p).mp
            (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 2) w).2,
          (mem_pointsOfDimension C p).mp
            (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 1) u).2]
        ring)
    rw [pointwiseMilnorBoundaryTerm_of_specializes C p k a
        (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 2) w)
        (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 1) u)
        hspecX hdimX,
      pointwiseMilnorBoundaryTerm_of_specializes C (j ≫ p) k
        (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) (k + 2) 2 a) w u hspec hdimU,
      milnorChainComap_apply]
    exact pointClosureMilnorBoundary_isOpenImmersion C p (j ≫ p) j
      (bijective_residueFieldMap_openImmersion j) w.1
      (specializes_iff_mem_closure.mp hspec) (specializes_iff_mem_closure.mp hspecX) hdimU hdimX
      (a.1 (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 2) w))
  · have hspecX : ¬ ((j.base w.1 : X) ⤳ (j.base u.1 : X)) := fun hcon ↦
      hspec (j.isOpenEmbedding.isInducing.specializes_iff.mp hcon)
    rw [pointwiseMilnorBoundaryTerm_of_not_specializes C p k a
        (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 2) w)
        (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 1) u) hspecX,
      pointwiseMilnorBoundaryTerm_of_not_specializes C (j ≫ p) k
        (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) (k + 2) 2 a) w u hspec, map_zero]

/-- **Stacks 0GUA for the first differential and the restriction map.** Restriction of locally
finite Milnor K-chains to an open subscheme commutes with the tame-symbol differential of
Stacks 0GU9: the square formed by the two differentials and the two restriction maps, in Milnor
degrees two and one, commutes. -/
@[stacks 0GUA "the compatibility of the restriction map of the degreewise localization sequence \
of the tag with the FIRST boundary map of the complex of Stacks 0GU9, the tame-symbol \
differential: for an open immersion j into a scheme locally of finite type over a Chow \
situation, restriction of locally finite Milnor K-chains to the open subscheme carries the \
tame-symbol differential in relative dimensions k + 2 and k + 1 to the tame-symbol differential \
of the open subscheme. The companion square for the extension-by-zero map from the closed \
complement is Stacks.Chow.pointwiseMilnorBoundary_milnorChainExtend. The two squares for the \
SECOND boundary map, the divisor differential of Stacks 0GU3, are \
Stacks.Chow.milnorChainComap_pointwiseDivisorDifferential and \
Stacks.Chow.pointwiseDivisorDifferential_milnorChainExtend; the six-term exact sequence the \
snake lemma yields from all four is Stacks.Chow.milnorChowLocalization_exact"]
theorem milnorChainComap_pointwiseMilnorBoundary (k : ℤ) :
    (pointwiseMilnorBoundary C (j ≫ p) k).comp
        (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) (k + 2) 2) =
      (milnorChainComap C p j (injective_base_of_isOpenImmersion j)
          (bijective_residueFieldMap_openImmersion j) (k + 1) 1).comp
        (pointwiseMilnorBoundary C p k) := by
  refine AddMonoidHom.ext fun a ↦ Subtype.ext (funext fun u ↦ ?_)
  show pointwiseMilnorBoundaryCoeff C (j ≫ p) k _ u =
    milnorKTransport
      (immersionResidueFieldEquiv j (bijective_residueFieldMap_openImmersion j) u.1 : _ →+* _) 1
      (pointwiseMilnorBoundaryCoeff C p k a
        (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 1) u))
  rw [pointwiseMilnorBoundaryCoeff, pointwiseMilnorBoundaryCoeff,
    AddMonoidHom.map_finsum_of_injective _
      (milnorKTransport_bijective
        (immersionResidueFieldEquiv j (bijective_residueFieldMap_openImmersion j) u.1) 1).1,
    finsum_eq_finsum_of_injective
      (immersionPoint C p j (bijective_residueFieldMap_openImmersion j) (k + 2))
      (immersionPoint_injective C p j (injective_base_of_isOpenImmersion j)
        (bijective_residueFieldMap_openImmersion j) (k + 2)) _ ?_]
  · exact (finsum_congr fun w ↦
      milnorKTransport_pointwiseMilnorBoundaryTerm_comap C p j k a w u).symm
  · intro x hx
    have hxrange : (x.1 : X) ∉ Set.range j.base := fun hcon ↦
      hx (exists_immersionPoint_eq C p j (bijective_residueFieldMap_openImmersion j) x hcon)
    rw [pointwiseMilnorBoundaryTerm_of_not_specializes C p k a x _
      (j.isOpenEmbedding.isOpen_range.not_specializes hxrange ⟨u.1, rfl⟩), map_zero]

/-! ### Extension by zero from the closed complement -/

omit [LocallyOfFiniteType p] in
/-- The coefficient of an extension by zero at the image of a point is the coefficient there,
transported backwards along the identification of the residue fields. -/
theorem milnorChainExtend_apply_immersionPoint {Z : Scheme.{u}} (f : Z ⟶ X)
    (hinj : Function.Injective f.base)
    (hbij : ∀ z : Z, Function.Bijective (f.residueFieldMap z).hom) (hqc : QuasiCompact f)
    (m : ℤ) (n : ℕ) (b : MilnorChainGroup C (f ≫ p) m n)
    (z : pointsOfDimension C (f ≫ p) m) :
    (milnorChainExtend C p f hinj hbij hqc m n b).1
        (immersionPoint C p f hbij m z) =
      milnorKTransport ((immersionResidueFieldEquiv f hbij z.1).symm : _ →+* _) n (b.1 z) := by
  rw [milnorChainExtend_apply, milnorChainExtendAtHom_of_eq C p f hinj hbij _ z rfl,
    milnorChainExtendHomOf_apply_rfl C p f hbij z]

variable (i : Y ⟶ X) [IsClosedImmersion i]

/-- **The local contributions to the first differential of Stacks 0GU9 agree on a closed
subscheme.** The contribution of a point of the closed subscheme to the coefficient at another
point of it is the contribution of its image to the coefficient at the image, transported along
the identification of the residue fields. -/
theorem milnorKTransport_pointwiseMilnorBoundaryTerm_extend (k : ℤ)
    (b : PointwiseKTwoGroup C (i ≫ p) k) (y' : pointsOfDimension C (i ≫ p) (k + 2))
    (y : pointsOfDimension C (i ≫ p) (k + 1)) :
    milnorKTransport
        (immersionResidueFieldEquiv i (bijective_residueFieldMap_closedImmersion i) y.1 :
          _ →+* _) 1
        (pointwiseMilnorBoundaryTerm C p k
          (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
            (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 2) 2 b)
          (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 2) y')
          (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 1) y)) =
      pointwiseMilnorBoundaryTerm C (i ≫ p) k b y' y := by
  by_cases hspec : (y'.1 : Y) ⤳ (y.1 : Y)
  · have hspecX : (i.base y'.1 : X) ⤳ (i.base y.1 : X) := hspec.map i.continuous
    have hdimY := ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one
      C (i ≫ p) hspec (by
        rw [(mem_pointsOfDimension C (i ≫ p)).mp y'.2,
          (mem_pointsOfDimension C (i ≫ p)).mp y.2]
        ring)
    have hdimX := ringKrullDim_pointClosureStalk_eq_one_of_relativeDimension_sub_eq_one
      C p hspecX (by
        rw [(mem_pointsOfDimension C p).mp
            (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 2) y').2,
          (mem_pointsOfDimension C p).mp
            (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 1) y).2]
        ring)
    rw [pointwiseMilnorBoundaryTerm_of_specializes C p k _
        (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 2) y')
        (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 1) y)
        hspecX hdimX,
      pointwiseMilnorBoundaryTerm_of_specializes C (i ≫ p) k b y' y hspec hdimY,
      pointClosureMilnorBoundary_isClosedImmersion C p (i ≫ p) i
        (bijective_residueFieldMap_closedImmersion i) y'.1
        (specializes_iff_mem_closure.mp hspec) (specializes_iff_mem_closure.mp hspecX)
        hdimY hdimX _,
      milnorChainExtend_apply_immersionPoint C p i (injective_base_of_isClosedImmersion i)
        (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 2) 2 b y',
      milnorKTransport_milnorKTransport_symm]
  · have hspecX : ¬ ((i.base y'.1 : X) ⤳ (i.base y.1 : X)) := fun hcon ↦
      hspec (i.isClosedEmbedding.isInducing.specializes_iff.mp hcon)
    rw [pointwiseMilnorBoundaryTerm_of_not_specializes C p k _
        (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 2) y')
        (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 1) y) hspecX,
      pointwiseMilnorBoundaryTerm_of_not_specializes C (i ≫ p) k b y' y hspec, map_zero]

/-- Off the closed subscheme the first differential of an extension by zero vanishes: a point of
the closed subscheme specializes only to points of it. -/
theorem pointwiseMilnorBoundaryCoeff_milnorChainExtend_of_notMem_range (k : ℤ)
    (b : PointwiseKTwoGroup C (i ≫ p) k) (x' : pointsOfDimension C p (k + 1))
    (hx' : (x'.1 : X) ∉ Set.range i.base) :
    pointwiseMilnorBoundaryCoeff C p k
      (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
        (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 2) 2 b) x' = 0 := by
  rw [pointwiseMilnorBoundaryCoeff, finsum_congr fun x ↦ ?_, finsum_zero]
  by_cases hx : (x.1 : X) ∈ Set.range i.base
  · exact pointwiseMilnorBoundaryTerm_of_not_specializes C p k _ x x'
      (i.isClosedEmbedding.isClosed_range.not_specializes hx hx')
  · refine pointwiseMilnorBoundaryTerm_of_eq_zero C p k _ ?_ x'
    rw [milnorChainExtend_apply,
      milnorChainExtendAtHom_of_notMem_range C p i
        (bijective_residueFieldMap_closedImmersion i) x hx, AddMonoidHom.zero_apply]

/-- **Stacks 0GUA for the first differential and the extension-by-zero map.** Extension by zero
of locally finite Milnor K-chains from a closed subscheme commutes with the tame-symbol
differential of Stacks 0GU9. -/
@[stacks 0GUA "the compatibility of the extension-by-zero map of the degreewise localization \
sequence of the tag with the FIRST boundary map of the complex of Stacks 0GU9, the tame-symbol \
differential: for a closed immersion i into a scheme locally of finite type over a Chow \
situation, extension by zero of locally finite Milnor K-chains from the closed subscheme \
carries its tame-symbol differential in relative dimensions k + 2 and k + 1 to the tame-symbol \
differential of the ambient scheme. The companion square for the restriction map to the open \
complement is Stacks.Chow.milnorChainComap_pointwiseMilnorBoundary. The two squares for the \
SECOND boundary map, the divisor differential of Stacks 0GU3, are \
Stacks.Chow.milnorChainComap_pointwiseDivisorDifferential and \
Stacks.Chow.pointwiseDivisorDifferential_milnorChainExtend; the six-term exact sequence the \
snake lemma yields from all four is Stacks.Chow.milnorChowLocalization_exact"]
theorem pointwiseMilnorBoundary_milnorChainExtend (k : ℤ) :
    (pointwiseMilnorBoundary C p k).comp
        (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 2) 2) =
      (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1).comp
        (pointwiseMilnorBoundary C (i ≫ p) k) := by
  refine AddMonoidHom.ext fun b ↦ Subtype.ext (funext fun x' ↦ ?_)
  by_cases hx' : (x'.1 : X) ∈ Set.range i.base
  · obtain ⟨y, rfl⟩ :=
      exists_immersionPoint_eq C p i (bijective_residueFieldMap_closedImmersion i) x' hx'
    show pointwiseMilnorBoundaryCoeff C p k _
        (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 1) y) =
      (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
        (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1
        (pointwiseMilnorBoundary C (i ≫ p) k b)).1
        (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 1) y)
    rw [milnorChainExtend_apply_immersionPoint C p i (injective_base_of_isClosedImmersion i)
      (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1 _ y]
    refine (milnorKTransport_bijective
      (immersionResidueFieldEquiv i (bijective_residueFieldMap_closedImmersion i) y.1) 1).1 ?_
    rw [milnorKTransport_milnorKTransport_symm, pointwiseMilnorBoundaryCoeff,
      AddMonoidHom.map_finsum_of_injective _
        (milnorKTransport_bijective
          (immersionResidueFieldEquiv i (bijective_residueFieldMap_closedImmersion i) y.1) 1).1,
      finsum_eq_finsum_of_injective
        (immersionPoint C p i (bijective_residueFieldMap_closedImmersion i) (k + 2))
        (immersionPoint_injective C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) (k + 2)) _ ?_]
    · exact finsum_congr fun y' ↦
        milnorKTransport_pointwiseMilnorBoundaryTerm_extend C p i k b y' y
    · intro x hx
      have hxrange : (x.1 : X) ∉ Set.range i.base := fun hcon ↦
        hx (exists_immersionPoint_eq C p i (bijective_residueFieldMap_closedImmersion i) x hcon)
      rw [pointwiseMilnorBoundaryTerm_of_eq_zero C p k _ ?_ _, map_zero]
      rw [milnorChainExtend_apply,
        milnorChainExtendAtHom_of_notMem_range C p i
          (bijective_residueFieldMap_closedImmersion i) x hxrange, AddMonoidHom.zero_apply]
  · show pointwiseMilnorBoundaryCoeff C p k
        (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
          (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 2) 2 b) x' =
      (milnorChainExtend C p i (injective_base_of_isClosedImmersion i)
        (bijective_residueFieldMap_closedImmersion i) inferInstance (k + 1) 1
        (pointwiseMilnorBoundary C (i ≫ p) k b)).1 x'
    rw [pointwiseMilnorBoundaryCoeff_milnorChainExtend_of_notMem_range C p i k b x' hx',
      milnorChainExtend_apply,
      milnorChainExtendAtHom_of_notMem_range C p i
        (bijective_residueFieldMap_closedImmersion i) x' hx', AddMonoidHom.zero_apply]

end Stacks.Chow

end
