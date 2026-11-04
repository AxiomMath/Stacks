module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.BaseChangeComponentDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Injective
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GeneralBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.CycleSupport
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a family of cycles under base change

Let `f : X ⟶ S` be locally of finite type, let `α` be a family of `r`-cycles on the fibres of
`X/S` and let `g : S' ⟶ S` be an arbitrary morphism of schemes. The support of the base change
`g^*α`, a family of `r`-cycles on the fibres of `X ×_S S' ⟶ S'`, is the inverse image of the
support of `α` along the projection `X ×_S S' ⟶ X`.

The fibre of `X ×_S S' ⟶ S'` over a point `t` of `S'` is the base change of the fibre of `f`
over `g t` along the residue field extension `κ(t)/κ(g t)`, so the fibrewise statement is the
compatibility of the support of a single cycle with a flat change of the base scheme, which is
proved first.

For a flat base change `B` of Chow situations one inclusion is formal: the coefficient of the
base change at a point is a multiple of the coefficient of the original cycle at its image, so
the support of the base change is contained in the inverse image of the support, which is
closed. The other inclusion is where the geometry enters. Let `w` be a point of `X ×_S S'` whose
image lies in the support of a cycle `z`, that is in the closure of some point `a` with
`z a ≠ 0`. Since the projection is flat it is generalizing, so the generalization `a` of the
image of `w` lifts to a generalization `v` of `w` over `a`. The point `v` need not carry a
nonzero coefficient, but it is a specialization of the image `y` of a generic point of the
scheme-theoretic inverse image of the reduced closure of `a`, and at such a point the
multiplicity entering the base change is the length of a nonzero module of finite length while
the relative dimension is the delta-dimension of a component of the base change of the reduced
closure of `a`. So the coefficient of the base change at `y` is a product of two nonzero
integers, and `w` lies in the closure of `y`.

The fibrewise statement is transported to the fibre of the base change through the canonical
isomorphism of the two fibres, which is a homeomorphism on points, and the topological support
of a function pulls back along a homeomorphism. Globally the support of a family is the union
over the base of the images of the supports of its members, so the two descriptions are matched
point by point: a point of `X ×_S S'` lies over the point `t` of `S'` it is sent to, its image
in `X` lies in the fibre over `g t`, and the canonical morphism of fibres is compatible with the
inclusions of the fibres into the total spaces.

## Main results

* `Stacks.Chow.tsupport_baseChangeCyclePullback` — the support of the base change of a cycle
  along a flat change of the base scheme is the inverse image of its support.
* `Stacks.Chow.tsupport_baseChangeFamily` — the fibrewise form of the compatibility.
* `Stacks.Chow.supportOfFamily_baseChangeFamily` — the support of a base-changed family of
  cycles is the inverse image of the support of the original family.

## Implementation notes

The reduced closure of a point is represented by the subscheme of its vanishing ideal sheaf and
its inverse image by the `comap` of that ideal sheaf, exactly as in the definition of the flat
pullback weight.

The nonvanishing statement proved here keeps track of the specialization relating the given
point of the base change to the point produced over the same image, which is what the inclusion
of supports needs; no surjectivity hypothesis on the base-change morphism is required, because
the point of the base change is supplied rather than constructed.

The support of a family of cycles is rarely closed in the total space, so the global statement
is an equality of subsets and not of closed subsets; the inverse image of the support of `α` is
nonetheless exactly the support of `g^*α`, with no closure taken.

A point `x` of `X ×_S S'` is viewed as a point of the fibre over its image in `S'` through
`AlgebraicGeometry.Scheme.Hom.asFiber`.

## References

* [Stacks Project, Tag 0H4V](https://stacks.math.columbia.edu/tag/0H4V)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVH](https://stacks.math.columbia.edu/tag/0FVH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The support of a cycle under a flat change of the base scheme -/

/-- In a flat base change of Chow situations, a point `w` of `X ×_S S'` lying over a point `x`
of `X` of relative dimension `k` is a specialization of a point of `X ×_S S'` lying over `x` at
which the weight entering a base-changed cycle is nonzero.

That point is the image of a generic point of the scheme-theoretic inverse image of the reduced
closure of `x`; its relative dimension is `k + c` because that inverse image is the base change
of the reduced closure of `x`, a scheme of delta-dimension `k`. -/
private theorem exists_flatPullbackWeight_ne_zero_specializes (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ)
    (x : X) (hx : relativeDimension B.base.dimensionFunction f x = k)
    (w : (pullback f B.g : Scheme.{u})) (hw : (pullback.fst f B.g).base w = x) :
    ∃ y : (pullback f B.g : Scheme.{u}), w ∈ closure ({y} : Set _) ∧
      flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g) (k + B.c) y ≠ 0 ∧
      (pullback.fst f B.g).base y = x := by
  classical
  set q : (pullback f B.g : Scheme.{u}) ⟶ X := pullback.fst f B.g
  set I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  have : IsIntegral I.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  obtain ⟨ξ, hspec, hξ⟩ := exists_comap_genericPoint_over q x w hw
  refine ⟨(I.comap q).subschemeι.base ξ.1, hspec, ?_, hξ⟩
  set Z : Scheme.{u} := pullback (I.subschemeι ≫ f) B.g
  set e : (I.comap q).subscheme ≅ Z := I.comapIso q ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso f B.g I.subschemeι with he
  set j : Z ⟶ (pullback f B.g : Scheme.{u}) := e.inv ≫ (I.comap q).subschemeι with hj
  have : IsClosedImmersion j := by
    rw [hj]
    infer_instance
  have hjsnd : j ≫ pullback.snd f B.g = pullback.snd (I.subschemeι ≫ f) B.g := by
    simp only [hj, he, Iso.trans_inv, Category.assoc,
      Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc, pullbackSymmetry_inv_comp_fst_assoc]
    exact pullbackRightPullbackFstIso_inv_snd_snd f B.g I.subschemeι
  have hdX : schemeDeltaDimension B.base (I.subschemeι ≫ f) = (k : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion,
      image_genericPoint_eq_of_range_eq_closure I.subschemeι x
        (range_subschemeι_vanishingIdeal_closure x), hx]
  set ζ : genericPoints Z := genericPointsIso e ξ
  have hdZ := deltaDimension_component_baseChange B (I.subschemeι ≫ f) k hdX
    (genericPoints.component ζ)
  rw [deltaDimension_eq_of_isGenericPoint _ _ _ ζ.1 (genericPoints.isGenericPoint ζ)] at hdZ
  have hjζ : j.base ζ.1 = (I.comap q).subschemeι.base ξ.1 := by
    have hinv : e.inv.base (e.hom.base ξ.1) = ξ.1 := by
      change ((e.hom ≫ e.inv) ξ.1) = ξ.1
      rw [Iso.hom_inv_id]
      rfl
    change (I.comap q).subschemeι.base (e.inv.base ζ.1) = _
    rw [show ζ.1 = e.hom.base ξ.1 from rfl, hinv]
  have hdim : relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g)
      ((I.comap q).subschemeι.base ξ.1) = k + B.c := by
    rwa [← hjζ, ← relativeDimension_comp_closedImmersion, hjsnd]
  exact flatPullbackWeight_ne_zero_of_genericPoint B.baseChange (pullback.snd f B.g) q (k + B.c)
    x ((I.comap q).subschemeι.base ξ.1) ξ rfl hξ hdim

/-- The support of the flat base change of a cycle is the inverse image of its support. -/
theorem tsupport_baseChangeCyclePullback (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (k : ℤ)
    (z : CycleGroup B.base f k) :
    tsupport (baseChangeCyclePullback B f k z).1 =
      pullback.fst f B.g ⁻¹' tsupport z.1 := by
  apply subset_antisymm
  · refine closure_minimal ?_ ((isClosed_tsupport _).preimage (pullback.fst f B.g).continuous)
    intro w hw
    rw [Function.mem_support, baseChangeCyclePullback_apply] at hw
    exact subset_closure (Function.mem_support.mpr (mul_ne_zero_iff.mp hw).1)
  · intro w hw
    have hlfs : LocallyFiniteSupport ⇑(z.1 : AlgebraicCycle X ℤ) :=
      Function.locallyFinsupp.locallyFiniteSupport z.1
    rw [Set.mem_preimage, tsupport_eq_biUnion_closure_singleton hlfs] at hw
    obtain ⟨a, ha, hclos⟩ := Set.mem_iUnion₂.mp hw
    have hza : z.1 a ≠ 0 := Function.mem_support.mp ha
    obtain ⟨v, hvw, hva⟩ := AlgebraicGeometry.Flat.generalizingMap (pullback.fst f B.g)
      (specializes_iff_mem_closure.mpr hclos)
    obtain ⟨y, hyv, hyweight, hyfst⟩ := exists_flatPullbackWeight_ne_zero_specializes B f k a
      ((mem_cyclesOfDimension_iff_forall_point B.base f k z.1).mp z.2 a hza) v hva
    have hysupport : y ∈ Function.support ⇑(baseChangeCyclePullback B f k z).1 := by
      rw [Function.mem_support, baseChangeCyclePullback_apply, hyfst]
      exact mul_ne_zero hza hyweight
    exact closure_mono (Set.singleton_subset_iff.mpr hysupport)
      (specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hyv).trans hvw))

/-! ### The support of a base-changed family of cycles -/

/-- The topological support of a function composed with a homeomorphism is the inverse image of
its topological support. -/
private theorem tsupport_comp_homeomorph {A C : Type*} [TopologicalSpace A]
    [TopologicalSpace C] (h : A ≃ₜ C) (c : C → ℤ) :
    tsupport (c ∘ h) = h ⁻¹' tsupport c := by
  change closure (Function.support (c ∘ h)) = h ⁻¹' closure (Function.support c)
  rw [show Function.support (c ∘ h) = h ⁻¹' Function.support c from rfl, h.preimage_closure]

/-- The fibrewise form: the support of the base-changed family on the fibre over `t` is the
inverse image of the support of the original family on the fibre over `g t`. -/
theorem tsupport_baseChangeFamily {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S') :
    tsupport (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) =
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t) ⁻¹'
        tsupport (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ) := by
  have hfun : ⇑(baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) =
      ⇑(baseChangeCyclePullback (residueFieldBaseChangeSituation g t)
            (f.fiberToSpecResidueField (g t)) (r : ℤ) (α (g t))).1 ∘
        Scheme.homeoOfIso (fibreBaseChangeIso f g t) := by
    funext x
    rw [baseChangeFamily_eq_baseChangeFiberCycle f g r α t]
    rfl
  rw [hfun, tsupport_comp_homeomorph, tsupport_baseChangeCyclePullback, ← Set.preimage_comp]
  exact congrArg (· ⁻¹' tsupport (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ))
    (funext fun x => fst_fibreBaseChangeIso_hom f g t x)

/-- **Stacks Project, Tag 0H4V, the base-change clause.** Taking the support of a family of
cycles on the fibres is compatible with base change: the support of `g^*α` is the inverse image
of the support of `α` along the projection `X ×_S S' ⟶ X`. -/
@[stacks 0H4V "base change"]
theorem supportOfFamily_baseChangeFamily {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) :
    supportOfFamily (pullback.snd f g) (baseChangeFamily f g r α) =
      pullback.fst f g ⁻¹' supportOfFamily f α := by
  have hmap : ∀ (t : S') (y : (pullback.snd f g).fiber t),
      f.fiberι (g t) (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
        pullback.condition t y) = pullback.fst f g ((pullback.snd f g).fiberι t y) := fun t y =>
    congrArg (fun m : (pullback.snd f g).fiber t ⟶ X => m y)
      (restrictedFiberMap_fiberι f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
  ext x
  simp only [Set.mem_preimage, mem_supportOfFamily]
  constructor
  · rintro ⟨t, y, hy, hyx⟩
    rw [tsupport_baseChangeFamily f g r α t] at hy
    exact ⟨g t, restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t y, hy, by rw [hmap, hyx]⟩
  · rintro ⟨s, y, hy, hyx⟩
    have hcond : f ((pullback.fst f g).base x) = g ((pullback.snd f g).base x) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun m : (pullback f g : Scheme.{u}) ⟶ S => m x)
          (pullback.condition (f := f) (g := g))
    obtain rfl : s = g ((pullback.snd f g).base x) := by
      rw [← hcond, ← hyx, Scheme.Hom.apply_fiberι]
    refine ⟨(pullback.snd f g).base x, (pullback.snd f g).asFiber x, ?_,
      Scheme.Hom.fiberι_asFiber _ _⟩
    rw [tsupport_baseChangeFamily f g r α ((pullback.snd f g).base x)]
    have hmy : restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
        ((pullback.snd f g).base x) ((pullback.snd f g).asFiber x) = y := by
      apply (f.fiberι (g ((pullback.snd f g).base x))).isEmbedding.injective
      rw [hmap, Scheme.Hom.fiberι_asFiber, ← hyx]
    exact Set.mem_preimage.mpr (hmy ▸ hy)

end Stacks.Chow

end
