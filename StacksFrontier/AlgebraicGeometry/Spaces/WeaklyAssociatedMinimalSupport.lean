module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections

/-!
# Germs, supports and weak association on an algebraic space

Let `X` be an algebraic space over `S`, let `F` be an `𝒪_X`-module and let `x̄` be a geometric
point of `X`. This file relates the three ways a point of `X` can be seen to carry a nonzero
piece of `F`: the germ of a section at `x̄`, the support of the underlying abelian sheaf, and
weak association of the maximal ideal of the étale local ring to the geometric stalk.

A germ vanishes exactly when the point of the chart carried by `x̄` lies in the largest open on
which the representing section vanishes, so a point lies in the support of `F` exactly when some
section over some small étale neighbourhood of some geometric point above it has a nonzero germ,
equivalently when some geometric stalk above it is nonzero. On the algebraic side, an element of
a geometric stalk which is nonzero and a power of which is killed by every non-unit of the étale
local ring witnesses weak association of the maximal ideal.

## Main results

* `AlgebraicGeometry.Space.geometricModuleStalkGerm_eq_zero_iff_mem_largestOpenZeroLocus`: the
  germ of a section vanishes exactly when the chart point lies in the largest open zero locus.
* `AlgebraicGeometry.Space.mem_supportOfSheaf_iff_exists_geometricModuleStalkGerm_ne_zero` and
  `AlgebraicGeometry.Space.mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk`: the support
  of the abelian sheaf underlying an `𝒪_X`-module, read on germs and on geometric stalks.
* `AlgebraicGeometry.Space.isUnit_etaleLocalRingGerm_of_mem_basicOpen`: a regular function which
  is invertible at the chart point has a germ which is a unit of the étale local ring.
* `AlgebraicGeometry.Space.exists_smallEtaleNeighborhoodHom_isAffine`: every small étale
  neighbourhood is refined by one whose chart is affine.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_forall_exists_pow_smul_eq_zero`: the
  algebraic criterion for weak association at a geometric point.

## Implementation notes

The support of Stacks 04KA is formed from the set-valued stalk of the underlying abelian sheaf,
whose vanishing criterion is `AlgebraicGeometry.Space.subsingleton_stalkSet_iff`, while the germ
map of `AlgebraicGeometry.Space.geometricModuleStalkGerm` lands in the geometric stalk, whose
vanishing criterion is `AlgebraicGeometry.Space.geometricModuleStalkGerm_eq_zero_iff`. Both
criteria say that the section dies on a refinement of the neighbourhood, so the two are compared
by the filtered-colimit description of the set-valued stalk alone, with no flatness or
quasi-coherence input.

The refinement of a neighbourhood used twice below is
`AlgebraicGeometry.Space.chartRefinement` along an open immersion of the chart's scheme: for the
unit criterion the open is the nonvanishing locus of the function, where the restriction of the
function is a unit already on the chart, and for the affine refinement it is an affine open
through the chosen lift.

Weak association is `IsWeaklyAssociatedPrime` of Stacks 0547, which asks for an element of the
module whose annihilator has the given prime as a *minimal* prime. For the maximal ideal of a
local ring the containment is automatic from the element being nonzero, and minimality is exactly
the hypothesis that every non-unit has a power annihilating the element: a prime below the
maximal ideal containing the annihilator then contains every non-unit.

## References

* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

attribute [local instance] pointTopology

/-! ### Germs and the support of the underlying abelian sheaf -/

/-- A germ of an `𝒪_X`-module at a geometric point vanishes exactly when the point of the chart
carried by that geometric point lies in the largest open on which the representing section
vanishes. -/
theorem geometricModuleStalkGerm_eq_zero_iff_mem_largestOpenZeroLocus
    (F : Modules.{u, m} B S hS X.1 X.2) (x : GeometricPoint B S hS X.1)
    (N : SmallEtaleNeighborhood x) (s : F.val.obj (op N.chart)) :
    geometricModuleStalkGerm B S hS X x F N s = 0 ↔
      (neighborhoodPoint B S hS X.1 N).image ∈
        (largestOpenZeroLocus B S hS X.1 ((SheafOfModules.toSheaf _).obj F) N.chart s).1 := by
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  refine (geometricModuleStalkGerm_eq_zero_iff B S hS X x F N s).trans
    (Iff.trans ?_ (germ_eq_zero_iff B S hS X.1 X.2 ((SheafOfModules.toSheaf _).obj F) N s))
  refine Iff.trans ?_ (Functor.ιColimitType_eq_iff_of_isFiltered'
    (F := SmallEtaleNeighborhood.sections (x := x)
      (((SheafOfModules.toSheaf _).obj F).obj ⋙ CategoryTheory.forget AddCommGrpCat.{m}))
    s (0 : F.val.obj (op N.chart))).symm
  constructor
  · rintro ⟨M, f, hf⟩
    refine ⟨op M, f.op, ?_⟩
    change F.val.map f.hom.op s = F.val.map f.hom.op 0
    simpa using hf
  · rintro ⟨M, f, hf⟩
    refine ⟨M.unop, f.unop, ?_⟩
    change F.val.map f.unop.hom.op s = F.val.map f.unop.hom.op 0 at hf
    simpa using hf

/-- **Stacks 04KA.** A point lies in the support of the abelian sheaf underlying an
`𝒪_X`-module exactly when, at some geometric point above it, some section over some small étale
neighbourhood has a nonzero germ. -/
theorem mem_supportOfSheaf_iff_exists_geometricModuleStalkGerm_ne_zero
    (F : Modules.{u, m} B S hS X.1 X.2) (x : points B S hS X.1) :
    x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ↔
      ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
        ∃ (N : SmallEtaleNeighborhood xbar) (s : F.val.obj (op N.chart)),
          geometricModuleStalkGerm B S hS X xbar F N s ≠ 0 := by
  rw [mem_supportOfSheaf_iff_exists]
  refine exists_congr fun xbar => and_congr_right fun _ => ?_
  constructor
  · intro hn
    by_contra hc
    push Not at hc
    exact hn ((subsingleton_stalkSet_iff B S hS X.1 X.2 ((SheafOfModules.toSheaf _).obj F)
      xbar).mpr fun N σ =>
        (geometricModuleStalkGerm_eq_zero_iff_mem_largestOpenZeroLocus B S hS X F xbar N σ).mp
          (hc N σ))
  · rintro ⟨N, s, hs⟩ hsub
    exact hs ((geometricModuleStalkGerm_eq_zero_iff_mem_largestOpenZeroLocus B S hS X F xbar N
      s).mpr ((subsingleton_stalkSet_iff B S hS X.1 X.2
        ((SheafOfModules.toSheaf _).obj F) xbar).mp hsub N s))

/-- **Stacks 04KA.** A point lies in the support of the abelian sheaf underlying an
`𝒪_X`-module exactly when the geometric stalk of the module at some geometric point above it is
nonzero. -/
theorem mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk
    (F : Modules.{u, m} B S hS X.1 X.2) (x : points B S hS X.1) :
    x ∈ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ↔
      ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
        Nontrivial (geometricModuleStalk B S hS X xbar F) :=
  (mem_supportOfSheaf_iff_exists_geometricModuleStalkGerm_ne_zero B S hS X F x).trans
    (exists_congr fun xbar => and_congr_right fun _ =>
      (nontrivial_geometricModuleStalk_iff B S hS X xbar F).symm)

/-! ### Units in the étale local ring -/

/-- The refinement of a small étale neighbourhood along an open immersion into its chart through
which the chart's geometric point lifts. -/
private noncomputable def openImmersionRefinement {x : GeometricPoint B S hS X.1}
    (N : SmallEtaleNeighborhood x) {W : Scheme.{u}} (j : W ⟶ chartScheme N.chart)
    [_root_.AlgebraicGeometry.IsOpenImmersion j] (q : (chartGeometricPoint N).source ⟶ W)
    (hq : q ≫ j = (chartGeometricPoint N).hom) : Over N :=
  chartRefinement N (Scheme.size_lt_of_isOpenImmersion j N.chart.obj.left.left.property) j
    inferInstance q hq

/-- **The restriction of a global regular function on a scheme to the open subscheme cut out by
its non-vanishing locus is a unit.**

The restriction along the inclusion of the basic open subscheme factors the restriction map of
the structure presheaf to that basic open, where the function is a unit by
`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`. -/
theorem isUnit_appTop_basicOpen (T : Scheme.{u}) (r : Γ(T, ⊤)) :
    IsUnit ((T.basicOpen r).ι.appTop r) := by
  let f : Γ(T, ⊤) ⟶ Γ(T, T.basicOpen r) := T.presheaf.map (homOfLE (T.basicOpen_le r)).op
  let g : Γ(T, T.basicOpen r) ⟶ Γ(T, (T.basicOpen r).ι ''ᵁ ⊤) :=
    T.presheaf.map (eqToHom (T.basicOpen r).ι_image_top).op
  have heq : f ≫ g = (T.basicOpen r).ι.appTop := by
    dsimp only [f, g]
    rw [← Functor.map_comp]
    rfl
  have ht : IsUnit ((f ≫ g) r) := (T.toRingedSpace.isUnit_res_basicOpen r).map g.hom
  rwa [heq] at ht

/-- A regular function on the chart of a small étale neighbourhood which does not vanish at the
point carried by the geometric point has a germ which is a unit of the étale local ring: the
chart may be shrunk to the nonvanishing locus of the function, where the function is a unit
already. -/
theorem isUnit_etaleLocalRingGerm_of_mem_basicOpen (x : GeometricPoint B S hS X.1)
    (N : SmallEtaleNeighborhood x) (a : Γ(chartScheme N.chart, ⊤))
    (ha : chartPoint B S hS X.1 N ∈ (chartScheme N.chart).basicOpen a) :
    IsUnit (etaleLocalRingGerm B S hS X.1 x (op N) a) := by
  let T := chartScheme N.chart
  let V := T.basicOpen a
  have hrange : Set.range (chartGeometricPoint N).hom ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint (chartGeometricPoint N).residueField)]
    exact ha
  let M := openImmersionRefinement B S hS X N V.ι
    (IsOpenImmersion.lift V.ι (chartGeometricPoint N).hom hrange)
    (IsOpenImmersion.lift_fac V.ι (chartGeometricPoint N).hom hrange)
  have heq : etaleLocalRingGerm B S hS X.1 x (op M.left) (V.ι.appTop a) =
      etaleLocalRingGerm B S hS X.1 x (op N) a :=
    DFunLike.congr_fun (spaceGerm_naturality (x := x) M.hom.op) a
  exact heq ▸ IsUnit.map (etaleLocalRingGerm B S hS X.1 x (op M.left))
    (isUnit_appTop_basicOpen T a)

/-! ### Affine refinements of a neighbourhood -/

/-- Every small étale neighbourhood of a geometric point is refined by one whose chart is an
affine scheme: the chosen lift factors through an affine open of the chart, which is again an
étale chart of the algebraic space. -/
theorem exists_smallEtaleNeighborhoodHom_isAffine (x : GeometricPoint B S hS X.1)
    (N : SmallEtaleNeighborhood x) :
    ∃ (M : SmallEtaleNeighborhood x) (_ : M ⟶ N), IsAffine (chartScheme M.chart) := by
  obtain ⟨R, j, hj, q, hq⟩ := exists_affine_point_refinement (chartGeometricPoint N)
    (chartGeometricPoint N).hom
  have : _root_.AlgebraicGeometry.IsOpenImmersion j := hj
  let M := openImmersionRefinement B S hS X N j q hq
  exact ⟨M.left, M.hom, inferInstanceAs (IsAffine (Spec R))⟩

/-! ### Weak association at a geometric point -/

/-- **Stacks 0CTX**, the algebraic criterion for weak association. A point of an algebraic space
is weakly associated to an `𝒪_X`-module as soon as, at some geometric point above it, the
geometric stalk has a nonzero element some power of each non-unit of the étale local ring
annihilates: the annihilator of that element lies in the maximal ideal because the ring is local,
and a prime below the maximal ideal containing the annihilator then contains every non-unit. -/
@[stacks 0CTX "weak association from a stalk element killed by powers of the non-units"]
theorem isWeaklyAssociatedPoint_of_forall_exists_pow_smul_eq_zero
    (F : Modules.{u, m} B S hS X.1 X.2) (x : points B S hS X.1)
    (xbar : GeometricPoint B S hS X.1) (hxbar : xbar.LiesOver x)
    (t : geometricModuleStalk B S hS X xbar F) (ht : t ≠ 0)
    (hpow : ∀ a : etaleLocalRing B S hS X.1 xbar, ¬ IsUnit a → ∃ n : ℕ, a ^ n • t = 0) :
    IsWeaklyAssociatedPoint B S hS X F x := by
  refine ⟨xbar, hxbar, ?_⟩
  let _ : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  refine ⟨t, ⟨inferInstance, fun a ha => ?_⟩, fun q hq _ a ha => ?_⟩
  · exact (IsLocalRing.mem_maximalIdeal a).mpr fun hu =>
      ht (hu.smul_eq_zero.mp ((Submodule.mem_annihilator_span_singleton t a).mp ha))
  · obtain ⟨n, hn⟩ := hpow a ((IsLocalRing.mem_maximalIdeal a).mp ha)
    exact hq.1.mem_of_pow_mem n
      (hq.2 ((Submodule.mem_annihilator_span_singleton t (a ^ n)).mpr hn))

end AlgebraicGeometry.Space

end
