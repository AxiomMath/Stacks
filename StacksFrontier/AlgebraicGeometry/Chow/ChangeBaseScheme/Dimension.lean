module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleRestriction
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.Meromorphic.RegularSectionExistence
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.BaseChangeComponentDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Delta-dimension and cycles under a change of the base scheme

Let `(S, δ)` and `(S', δ')` be two base situations for Chow homology joined by a flat morphism
`g : S' ⟶ S` whose dimension functions differ by a constant `c` on the generic points of the
fibres of `g` — the situation of Stacks 0FVG, here `Stacks.Chow.FlatBaseChangeSituation` — and
let `X` be locally of finite type over `S` with base change `X' = X ×_S S'`. This file proves
Stacks 0FVI: for a closed subscheme `Z ⊆ X` with `dim_δ(Z) ≤ k` the base change `Z' ⊆ X'` has
`dim_{δ'}(Z') ≤ k + c` and `g^*[Z]_k = [Z']_{k+c}`, and for a coherent sheaf `F` on `X` whose
support has delta-dimension at most `k` the base change `F'` is coherent with support of
delta-dimension at most `k + c` and `g^*[F]_k = [F']_{k+c}`. Here `g^*` is the base-change
homomorphism `Stacks.Chow.baseChangeCyclePullback` on cycle groups.

The argument reads Stacks 0FVH at one point at a time. A generic point `y'` of an irreducible
component of a base change `Y ×_S S'` lies in the base change of the reduced closure of its
image `y` in `Y`, and is a generic point of a component of that base change because it is
already maximal in `Y ×_S S'`; the reduced closure of `y` is integral of delta-dimension
`δ_Y(y)`, so Stacks 0FVH gives `δ'(y') = δ_Y(y) + c`. Taking the supremum over the components
bounds `dim_{δ'}(Y ×_S S')` by `dim_δ(Y) + c`. For a closed subscheme `Z ⊆ X` the two
descriptions `Z ×_X X'` and `Z ×_S S'` of the base change are identified by
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, which turns that supremum bound into a
bound on the relative dimension at every point of `Z ×_X X'`; the coherent case follows because
the support of the base change of a coherent sheaf is the inverse image of its support, so each
of its points already lies in the base change of the reduced support.

## Main results

* `Stacks.Chow.schemeDeltaDimension_baseChange_le` — the delta-dimension of a base change
  exceeds that of the original scheme by at most `c`.
* `Stacks.Chow.schemeDeltaDimension_baseChange_closedSubscheme_le` — **Stacks 0FVI, part (1),
  dimension bound**, the bound `dim_{δ'}(Z') ≤ k + c` for the base change of a closed subscheme.
* `Stacks.Chow.schemeDeltaDimension_baseChange_support_le` — **Stacks 0FVI, part (2), dimension
  bound**, the bound `dim_{δ'}(Supp F') ≤ k + c` for the base change of a coherent sheaf.
* `Stacks.Chow.baseChangeCyclePullback_cycleAssociatedToCoherentSheaf` — **Stacks 0FVI, part (2),
  cycle identity**, `g^*[F]_k = [F']_{k+c}`.
* `Stacks.Chow.baseChangeCyclePullback_cycleAssociatedToClosedSubscheme` — **Stacks 0FVI,
  part (1), cycle identity**, `g^*[Z]_k = [Z']_{k+c}`.
* `Stacks.Chow.pullbackPushforwardStructureSheafIso_of_flat` — the flat base change of the direct
  image of the structure sheaf of a closed subscheme is the direct image of the structure sheaf of
  its inverse image.
* `Stacks.Chow.cycleAssociatedToCoherentSheaf_eq_of_iso'` — isomorphic coherent sheaves have the
  same associated cycle.

## Implementation notes

The base change of `X` is the chosen categorical pullback `pullback f B.g`, with structure
morphism `CategoryTheory.Limits.pullback.snd` over the new base and projection
`CategoryTheory.Limits.pullback.fst` to `X`, exactly as in Stacks 0FVH. The base change of a
closed subscheme `i : Z ⟶ X` is presented as a closed subscheme of `X'`, namely
`pullback.snd i (pullback.fst f B.g)`, so that the two dimension bounds below are both bounds
for closed subschemes of one and the same scheme `X'`. The support of a coherent sheaf is
represented by the reduced closed subscheme `Stacks.Chow.reducedSupport` carried by it, and the
delta-dimension of a whole scheme is valued in `EInt`, hence the coercions.

### The cycle identities

The cycle identity of part (2) is read off one point `x'` of `X'` at a time. With `x = g(x')`,
`A = 𝒪_{X, x}`, `B = 𝒪_{X', x'}` and `M = F_x`, the coefficient of `g^*[F]_k` at `x'` is the
coefficient of `[F]_k` at `x` times the base-change multiplicity, that is

`length_A (M) * length_B (B / 𝔪_A B)`,

while the coefficient of `[F']_{k+c}` is `length_B (F'_{x'}) = length_B (B ⊗_A M)`. The two agree
by Stacks 02M1, here `AlgebraicGeometry.length_baseChange_eq_length_mul_length_quotient`; the
identification of the stalk of the base change with `B ⊗_A M` is Stacks 0098, and the two steps
are packaged as `Stacks.Chow.sheafMultiplicity_pullback`. The multiplicity formula applies
because `x'` is then forced to be the image of a generic point of a component of the inverse
image of the reduced closure of `x`, which is the base-change counterpart of Stacks 02QT proved
below.

Part (1) is deduced from part (2) as in the source: by Stacks 02QY the cycle of a closed
subscheme is the cycle of the direct image of its structure sheaf, and the base change of
`i_* 𝒪_Z` is `i'_* 𝒪_{Z'}` by flat base change for direct images in degree zero, Stacks 02KH,
which applies because a closed immersion is quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVH](https://stacks.math.columbia.edu/tag/0FVH)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
* [Stacks Project, Tag 02QY](https://stacks.math.columbia.edu/tag/02QY)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Relative dimension at an arbitrary point -/

/-- The relative dimension at every point of a scheme is at most its delta-dimension: this is
`Stacks.Chow.relativeDimension_le_of_schemeDeltaDimension_le` for the identity closed
immersion. -/
private theorem relativeDimension_le_of_schemeDeltaDimension_le_self (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] {k : ℤ}
    (hX : schemeDeltaDimension C f ≤ (k : EInt)) (x : X) :
    relativeDimension C.dimensionFunction f x ≤ k := by
  have h := relativeDimension_le_of_schemeDeltaDimension_le C f (𝟙 X)
    (k := k) (by simpa using hX) x
  simpa using h

/-! ### The delta-dimension of a base change -/

/-- A point lies on the reduced closure of itself, the support of `integralComponentAt`. -/
private theorem mem_support_integralComponentAt {X : Scheme.{u}} (x : X) :
    x ∈ ((integralComponentAt x).support : Set X) := by
  rw [coe_support_integralComponentAt]
  exact subset_closure rfl

/-- In the flat base-change situation of Stacks 0FVG, the relative dimension at a generic point
of an irreducible component of a base change `Y ×_S S'` exceeds by exactly `c` the relative
dimension of its image in `Y`.

The point lies in the base change of the reduced closure of its image, and is a generic point of
a component of that base change because it is already maximal in `Y ×_S S'`; the reduced closure
of the image is integral of delta-dimension the relative dimension of that image, so Stacks 0FVH
applies to it. -/
private theorem relativeDimension_baseChange_genericPoint (B : FlatBaseChangeSituation.{u})
    {Y : Scheme.{u}} (h : Y ⟶ B.base.S) [LocallyOfFiniteType h]
    (y' : (pullback h B.g : Scheme.{u}))
    (hy' : y' ∈ genericPoints (pullback h B.g : Scheme.{u})) :
    relativeDimension B.baseChange.dimensionFunction (pullback.snd h B.g) y' =
      relativeDimension B.base.dimensionFunction h ((pullback.fst h B.g) y') + B.c := by
  set p : (pullback h B.g : Scheme.{u}) ⟶ Y := pullback.fst h B.g with hp
  set y : Y := p y' with hy
  set I : Y.IdealSheafData := integralComponentAt y with hI
  have _ : IsIntegral I.subscheme := isIntegral_integralComponentAt y
  have hrange : y' ∈ Set.range (I.comap p).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rw [Scheme.IdealSheafData.support_comap]
    exact mem_support_integralComponentAt (p y')
  obtain ⟨w, hw⟩ := hrange
  have hwgen : w ∈ genericPoints (I.comap p).subscheme :=
    genericPoints_preimage_of_isClosedImmersion (I.comap p).subschemeι (by rw [hw]; exact hy')
  set Z : Scheme.{u} := pullback (I.subschemeι ≫ h) B.g with hZ
  set e : (I.comap p).subscheme ≅ Z := I.comapIso p ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso h B.g I.subschemeι with he
  set j : Z ⟶ (pullback h B.g : Scheme.{u}) := e.inv ≫ (I.comap p).subschemeι with hj
  have _ : IsClosedImmersion j := by rw [hj]; infer_instance
  have hjsnd : j ≫ pullback.snd h B.g = pullback.snd (I.subschemeι ≫ h) B.g := by
    simp only [hj, he, Iso.trans_inv, Category.assoc,
      Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc, pullbackSymmetry_inv_comp_fst_assoc]
    exact pullbackRightPullbackFstIso_inv_snd_snd h B.g I.subschemeι
  have hdY : schemeDeltaDimension B.base (I.subschemeι ≫ h) =
      ((relativeDimension B.base.dimensionFunction h y : ℤ) : EInt) :=
    schemeDeltaDimension_integralComponentAt B.base h y
  set ζ : genericPoints Z := genericPointsIso e ⟨w, hwgen⟩ with hζ
  have hdZ := deltaDimension_component_baseChange B (I.subschemeι ≫ h) _ hdY
    (genericPoints.component ζ)
  rw [deltaDimension_eq_of_isGenericPoint _ _ _ ζ.1 (genericPoints.isGenericPoint ζ)] at hdZ
  have hjζ : j ζ.1 = y' := by
    have hinv : e.inv (e.hom w) = w := by
      show ((e.hom ≫ e.inv) w) = w
      rw [Iso.hom_inv_id]
      rfl
    show (I.comap p).subschemeι (e.inv ζ.1) = y'
    rw [show ζ.1 = e.hom w from rfl, hinv]
    exact hw
  rw [← hjζ, ← relativeDimension_comp_closedImmersion, hjsnd]
  exact hdZ

/-- In the flat base-change situation of Stacks 0FVG, the delta-dimension of the base change
`Y ×_S S'` of a scheme locally of finite type over `S` exceeds that of `Y` by at most `c`: every
irreducible component of the base change contributes the relative dimension of its generic
point, which is the relative dimension of the image of that point plus `c`. -/
theorem schemeDeltaDimension_baseChange_le (B : FlatBaseChangeSituation.{u}) {Y : Scheme.{u}}
    (h : Y ⟶ B.base.S) [LocallyOfFiniteType h] {k : ℤ}
    (hY : schemeDeltaDimension B.base h ≤ (k : EInt)) :
    schemeDeltaDimension B.baseChange (pullback.snd h B.g) ≤ ((k + B.c : ℤ) : EInt) := by
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun W => WithBotTop.coe_le_coe.mpr ?_
  rw [deltaDimension_eq_of_isGenericPoint B.baseChange (pullback.snd h B.g) _
      (genericPoints.ofComponent W).1 (genericPoints.isGenericPoint_ofComponent W),
    relativeDimension_baseChange_genericPoint B h _ (genericPoints.ofComponent W).2]
  have hle := relativeDimension_le_of_schemeDeltaDimension_le_self B.base h hY
    ((pullback.fst h B.g) (genericPoints.ofComponent W).1)
  omega

/-- In the flat base-change situation of Stacks 0FVG, the relative dimension over the new base
of a point of `X ×_S S'` lying over a closed subscheme `i : Z ⟶ X` of delta-dimension at most
`k` is at most `k + c`.

The point comes from a point of `Z ×_X X'`, which is the base change `Z ×_S S'` of `Z`, and the
delta-dimension of that base change is at most `k + c`. -/
private theorem relativeDimension_baseChange_le_of_mem_range (B : FlatBaseChangeSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] {k : ℤ}
    (hZ : schemeDeltaDimension B.base (i ≫ f) ≤ (k : EInt))
    (x' : (pullback f B.g : Scheme.{u}))
    (hx' : (pullback.fst f B.g) x' ∈ Set.range i) :
    relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) x' ≤ k + B.c := by
  obtain ⟨w, hw⟩ : x' ∈ Set.range (pullback.snd i (pullback.fst f B.g)) := by
    rw [Scheme.Pullback.range_snd]
    exact hx'
  have hcomp : pullback.snd i (pullback.fst f B.g) ≫ pullback.snd f B.g =
      (pullbackRightPullbackFstIso f B.g i).hom ≫ pullback.snd (i ≫ f) B.g :=
    (pullbackRightPullbackFstIso_hom_snd f B.g i).symm
  have hpoint : relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) x' =
      relativeDimension B.baseChange.dimensionFunction (pullback.snd (i ≫ f) B.g)
        ((pullbackRightPullbackFstIso f B.g i).hom w) := by
    rw [← hw, ← relativeDimension_comp_closedImmersion B.baseChange.dimensionFunction
        (pullback.snd i (pullback.fst f B.g)) (pullback.snd f B.g) w, hcomp,
      relativeDimension_comp_closedImmersion]
  rw [hpoint]
  exact relativeDimension_le_of_schemeDeltaDimension_le_self B.baseChange
    (pullback.snd (i ≫ f) B.g) (schemeDeltaDimension_baseChange_le B (i ≫ f) hZ) _

/-! ### The dimension bounds of Stacks 0FVI -/

add_to_stacks 0FVI "part (2): coherence of the base change" AlgebraicGeometry.isCoherent_pullback

/-- **Stacks 0FVI, part (1), dimension bound.** In the flat base-change situation of Stacks
0FVG, the base change `Z' = Z ×_X X'` of a closed subscheme `Z ⊆ X` of delta-dimension at most
`k` is a closed subscheme of `X' = X ×_S S'` of delta-dimension at most `k + c`. -/
@[stacks 0FVI "part (1): dimension bound"]
theorem schemeDeltaDimension_baseChange_closedSubscheme_le (B : FlatBaseChangeSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] {k : ℤ}
    (hZ : schemeDeltaDimension B.base (i ≫ f) ≤ (k : EInt)) :
    schemeDeltaDimension B.baseChange
        (pullback.snd i (pullback.fst f B.g) ≫ pullback.snd f B.g) ≤ ((k + B.c : ℤ) : EInt) :=
  schemeDeltaDimension_le_of_forall_relativeDimension_le B.baseChange (pullback.snd f B.g)
    (pullback.snd i (pullback.fst f B.g)) fun w =>
      relativeDimension_baseChange_le_of_mem_range B f i hZ _
        ⟨pullback.fst i (pullback.fst f B.g) w,
          congrArg (fun m : pullback i (pullback.fst f B.g) ⟶ X => m w) pullback.condition⟩

/-- **Stacks 0FVI, part (2), dimension bound.** In the flat base-change situation of Stacks
0FVG, if a coherent sheaf on `X` has support of delta-dimension at most `k`, then the support of
its base change to `X' = X ×_S S'` has delta-dimension at most `k + c`.

Every point of the support of the base change lies over the support of the sheaf, so part (1)
for the reduced support bounds the relative dimension there. -/
@[stacks 0FVI "part (2): support dimension bound"]
theorem schemeDeltaDimension_baseChange_support_le (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsCoherent] {k : ℤ}
    (hFk : schemeDeltaDimension B.base ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian (pullback f B.g : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f B.g)
    letI : ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F).IsCoherent :=
      AlgebraicGeometry.isCoherent_pullback (pullback.fst f B.g) F
    schemeDeltaDimension B.baseChange
        ((reducedSupport ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F)).subschemeι ≫
          pullback.snd f B.g) ≤ ((k + B.c : ℤ) : EInt) := by
  have _ : IsLocallyNoetherian (pullback f B.g : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f B.g)
  have _ : ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback (pullback.fst f B.g) F
  have _ : F.IsFiniteType := isFiniteType_of_isCoherent F
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le B.baseChange
    (pullback.snd f B.g) _ fun w => ?_
  refine relativeDimension_baseChange_le_of_mem_range B f (reducedSupport F).subschemeι hFk _ ?_
  rw [Scheme.IdealSheafData.range_subschemeι, coe_support_reducedSupport]
  have hmem : (reducedSupport ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F)).subschemeι w
      ∈ SheafOfModules.supp ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F) := by
    rw [← coe_support_reducedSupport, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  rwa [Stacks.Modules.supp_pullback (pullback.fst f B.g) F] at hmem

/-! ### The cycle identities of Stacks 0FVI -/

/-- In the flat base-change situation of Stacks 0FVG, the relative dimension over the new base
of a point of `X ×_S S'` exceeds that of its image in `X` by at most `c`: the point lies over
the reduced closure of its image, an integral closed subscheme whose delta-dimension is exactly
that relative dimension. -/
private theorem relativeDimension_baseChange_le (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f]
    (x' : (pullback f B.g : Scheme.{u})) :
    relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) x' ≤
      relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g) x') + B.c := by
  have _ : IsIntegral (integralComponentAt ((pullback.fst f B.g) x')).subscheme :=
    isIntegral_integralComponentAt _
  refine relativeDimension_baseChange_le_of_mem_range B f
    (integralComponentAt ((pullback.fst f B.g) x')).subschemeι
    (le_of_eq (schemeDeltaDimension_integralComponentAt B.base f _)) x' ?_
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact mem_support_integralComponentAt _

/-- A point of a base change whose relative dimension over the new base is exactly that of its
image plus `c` is the image of a generic point of an irreducible component of the
scheme-theoretic inverse image of the reduced closure of that image.

No point of that inverse image has larger relative dimension: its image in `X` is a
specialization of the image of the given point, so has no larger relative dimension there, and
passing to the base change adds at most `c`. This is the base-change counterpart of Stacks 02QT,
which plays the same role for a flat morphism of fixed relative dimension over one base. -/
private theorem exists_genericPoints_comap_integralComponentAt_baseChange
    (B : FlatBaseChangeSituation.{u}) {X : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] (x' : (pullback f B.g : Scheme.{u}))
    (hdim : relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) x' =
      relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g) x') + B.c) :
    ∃ ξ : genericPoints ((integralComponentAt ((pullback.fst f B.g) x')).comap
        (pullback.fst f B.g)).subscheme,
      ((integralComponentAt ((pullback.fst f B.g) x')).comap
        (pullback.fst f B.g)).subschemeι.base ξ.1 = x' := by
  set q : (pullback f B.g : Scheme.{u}) ⟶ X := pullback.fst f B.g
  set x : X := q.base x'
  set I : X.IdealSheafData := integralComponentAt x
  have hsupp : (((I.comap q)).support : Set (pullback f B.g : Scheme.{u})) =
      q.base ⁻¹' (I.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hclosure : (I.support : Set X) = closure {x} := coe_support_integralComponentAt x
  have hxmem : x' ∈ ((I.comap q).support : Set (pullback f B.g : Scheme.{u})) := by
    rw [hsupp]
    exact mem_support_integralComponentAt _
  obtain ⟨ξ₀, hξ₀⟩ : ∃ z : (I.comap q).subscheme, (I.comap q).subschemeι.base z = x' := by
    rwa [← Scheme.IdealSheafData.range_subschemeι] at hxmem
  have hbound : ∀ z : (I.comap q).subscheme,
      relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g)
          ((I.comap q).subschemeι.base z) ≤
        relativeDimension B.base.dimensionFunction f x + B.c := by
    intro z
    have hmem : q.base ((I.comap q).subschemeι.base z) ∈ closure ({x} : Set X) := by
      rw [← hclosure, ← Set.mem_preimage, ← hsupp, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    have h1 : relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g)
          ((I.comap q).subschemeι.base z) ≤
        relativeDimension B.base.dimensionFunction f
          (q.base ((I.comap q).subschemeι.base z)) + B.c :=
      relativeDimension_baseChange_le B f ((I.comap q).subschemeι.base z)
    have h2 := relativeDimension_le_of_specializes B.base f
      (specializes_iff_mem_closure.mpr hmem)
    omega
  obtain ⟨W, hW⟩ := isGenericPoint_component_of_relativeDimension_eq B.baseChange
    (pullback.snd f B.g) (I.comap q).subschemeι
    (schemeDeltaDimension_le_of_forall_point B.baseChange (pullback.snd f B.g)
      (I.comap q).subschemeι hbound) ξ₀ (by rwa [hξ₀])
  refine ⟨⟨ξ₀, ?_⟩, hξ₀⟩
  simp only [genericPoints, Set.mem_ofPred_eq, hW.def]
  exact W.2

/-- **Stacks 0FVI, part (2), cycle identity.** In the flat base-change situation of Stacks 0FVG,
the base change of the cycle of a coherent sheaf `F` on `X` whose support has delta-dimension at
most `k` is the cycle of the base change of `F`:

`g^*[F]_k = [F']_{k + c}`.

The two sides are compared at one point `x'` of `X'` at a time. If `x'` has relative dimension
other than `k + c` both vanish, the left one because the base-change multiplicity is formed only
in that degree. If `x'` lies off the support of `F'` then its image lies off the support of `F`,
since the support of a pullback is the inverse image of the support, so the coefficient of
`[F]_k` already vanishes there. In the remaining case the relative dimension of the image is
forced to be exactly `k`, because it is at most `k` on the support of `F` while the relative
dimension of `x'` exceeds it by at most `c`; the two multiplicities are then
`length_A M * length_B (B / 𝔪_A B)` and `length_B (B ⊗_A M)` for `A = 𝒪_{X, x}`, `B = 𝒪_{X', x'}`
and `M = F_x`, equal by Stacks 02M1. -/
@[stacks 0FVI "part (2): cycle identity"]
theorem baseChangeCyclePullback_cycleAssociatedToCoherentSheaf (B : FlatBaseChangeSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent]
    (k : ℤ) (hFk : schemeDeltaDimension B.base ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    letI : IsLocallyNoetherian (pullback f B.g : Scheme.{u}) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f B.g)
    letI : ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F).IsCoherent :=
      AlgebraicGeometry.isCoherent_pullback (pullback.fst f B.g) F
    baseChangeCyclePullback B f k (cycleAssociatedToCoherentSheaf B.base f F k hFk) =
      cycleAssociatedToCoherentSheaf B.baseChange (pullback.snd f B.g)
        ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F) (k + B.c)
        (schemeDeltaDimension_baseChange_support_le B f F hFk) := by
  classical
  have _ : IsLocallyNoetherian (pullback f B.g : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f B.g)
  have _ : ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback (pullback.fst f B.g) F
  have _ : F.IsFiniteType := isFiniteType_of_isCoherent F
  have hsupp : SheafOfModules.supp ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F) =
      (pullback.fst f B.g).base ⁻¹' SheafOfModules.supp F :=
    Stacks.Modules.supp_pullback (pullback.fst f B.g) F
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x' => ?_)
  rw [baseChangeCyclePullback_apply]
  by_cases hrel : relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) x' =
      k + B.c
  · by_cases hx' : x' ∈ SheafOfModules.supp
        ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F)
    · have hfx : (pullback.fst f B.g).base x' ∈ SheafOfModules.supp F := by
        rwa [hsupp] at hx'
      have hle : relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g).base x') ≤ k :=
        relativeDimension_le_of_mem_supp B.base f F hFk hfx
      have hup := relativeDimension_baseChange_le B f x'
      have hrelX : relativeDimension B.base.dimensionFunction f
          ((pullback.fst f B.g).base x') = k := by omega
      have hdim' : relativeDimension B.baseChange.dimensionFunction (pullback.snd f B.g) x' =
          relativeDimension B.base.dimensionFunction f ((pullback.fst f B.g) x') + B.c := by
        omega
      rw [flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal B.baseChange
          (pullback.snd f B.g) (pullback.fst f B.g) (k + B.c) x'
          (exists_genericPoints_comap_integralComponentAt_baseChange B f x' hdim') hrel,
        cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq B.base f F k hFk hrelX,
        cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq B.baseChange
          (pullback.snd f B.g) ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F)
          (k + B.c) _ hrel]
      exact (sheafMultiplicity_pullback (pullback.fst f B.g) F x').symm
    · have hfx : (pullback.fst f B.g).base x' ∉ SheafOfModules.supp F := by
        rwa [hsupp] at hx'
      rw [cycleAssociatedToCoherentSheaf_apply B.base f F k hFk,
        cycleAssociatedToCoherentSheaf_apply B.baseChange (pullback.snd f B.g)
          ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F) (k + B.c) _]
      simp [hfx, hx']
  · have hw : flatPullbackWeight B.baseChange (pullback.snd f B.g) (pullback.fst f B.g)
        (k + B.c) x' = 0 := by
      unfold flatPullbackWeight closedSubschemeCycleCoeff
      split
      · rename_i h
        exact absurd (Classical.choose_spec h).2 hrel
      · rfl
    rw [hw, mul_zero]
    exact (cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne B.baseChange
      (pullback.snd f B.g) ((Scheme.Modules.pullback (pullback.fst f B.g)).obj F)
      (k + B.c) _ hrel).symm

/-- Isomorphic coherent sheaves have the same associated cycle: at a point whose relative
dimension is the prescribed one both coefficients are the multiplicity, and an isomorphism
induces an isomorphism of stalks hence preserves multiplicities; elsewhere both vanish.

Variant of `Stacks.Chow.cycleAssociatedToCoherentSheaf_eq_of_iso` with explicit modules and the
isomorphism last. -/
theorem cycleAssociatedToCoherentSheaf_eq_of_iso' (C : ChowSituation.{u})
    {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q] (F G : X.Modules) [F.IsCoherent]
    [G.IsCoherent] (k : ℤ)
    (hF : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ q) ≤ (k : EInt))
    (hG : schemeDeltaDimension C ((reducedSupport G).subschemeι ≫ q) ≤ (k : EInt)) (e : F ≅ G) :
    cycleAssociatedToCoherentSheaf C q F k hF = cycleAssociatedToCoherentSheaf C q G k hG := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  by_cases hx : relativeDimension C.dimensionFunction q x = k
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C q F k hF hx,
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C q G k hG hx]
    exact sheafMultiplicity_eq_of_iso e x
  · rw [cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C q F k hF hx,
      cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C q G k hG hx]

/-- **Flat base change for the direct image of the structure sheaf of a closed subscheme.** For a
closed immersion `i : Z ⟶ X` and a flat morphism `q : X' ⟶ X`, the inverse image along `q` of
`i_* 𝒪_Z` is the direct image of the structure sheaf of the inverse image `Z' = Z ×_X X'` of `Z`.

This is Stacks 02KH in degree zero — available because a closed immersion is quasi-compact and
quasi-separated — followed by the identification of the inverse image of a structure sheaf with
the structure sheaf, which holds because the inverse-image functor on opens is final.

Special case (`q` flat, the square `Z ×_X X'`) of
`Stacks.Chow.pullbackPushforwardStructureSheafIso`, which takes any cartesian square. -/
@[ega "III 4.3.4" "special case", sga "7 VII 1.3.8" "special case"]
noncomputable def pullbackPushforwardStructureSheafIso_of_flat {X X' Z : Scheme.{u}}
    (q : X' ⟶ X) [Flat q] (i : Z ⟶ X) [IsClosedImmersion i] :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) ≅
      (Scheme.Modules.pushforward (pullback.snd i q)).obj
        (Ample.unitModule (pullback i q : Scheme.{u})) :=
  have : IsIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (IsPullback.of_hasPullback i q).w).app (Ample.unitModule Z)) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat
      (IsPullback.of_hasPullback i q) (Ample.unitModule Z)
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (IsPullback.of_hasPullback i q).w).app (Ample.unitModule Z)) ≪≫
    (Scheme.Modules.pushforward (pullback.snd i q)).mapIso
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (pullback.fst i q))

/-- **Stacks 0FVI, part (1), cycle identity.** In the flat base-change situation of Stacks 0FVG,
the base change of the cycle of a closed subscheme `Z ⊆ X` of delta-dimension at most `k` is the
cycle of the base change `Z' = Z ×_X X'`:

`g^*[Z]_k = [Z']_{k + c}`.

By Stacks 02QY both cycles are cycles of coherent sheaves, namely of `i_* 𝒪_Z` and of
`i'_* 𝒪_{Z'}`, so part (2) reduces the claim to the flat base change of `i_* 𝒪_Z` being
`i'_* 𝒪_{Z'}`. -/
@[stacks 0FVI "part (1): cycle identity"]
theorem baseChangeCyclePullback_cycleAssociatedToClosedSubscheme (B : FlatBaseChangeSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ B.base.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] (k : ℤ)
    (hZ : schemeDeltaDimension B.base (i ≫ f) ≤ (k : EInt)) :
    baseChangeCyclePullback B f k (cycleAssociatedToClosedSubscheme B.base f i k) =
      cycleAssociatedToClosedSubscheme B.baseChange (pullback.snd f B.g)
        (pullback.snd i (pullback.fst f B.g)) (k + B.c) := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian (pullback f B.g : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f B.g)
  let _ : ((Scheme.Modules.pullback (pullback.fst f B.g)).obj
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback (pullback.fst f B.g)
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z))
  have hZ' := schemeDeltaDimension_baseChange_closedSubscheme_le B f i hZ
  rw [cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf B.base f i k hZ,
    cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf B.baseChange
      (pullback.snd f B.g) (pullback.snd i (pullback.fst f B.g)) (k + B.c) hZ',
    baseChangeCyclePullback_cycleAssociatedToCoherentSheaf B f
      ((Scheme.Modules.pushforward i).obj (Ample.unitModule Z)) k
      (schemeDeltaDimension_reducedSupport_pushforwardStructureSheaf_le B.base f i hZ)]
  exact cycleAssociatedToCoherentSheaf_eq_of_iso' B.baseChange (pullback.snd f B.g) _ _ (k + B.c)
    _ _ (pullbackPushforwardStructureSheafIso_of_flat (pullback.fst f B.g) i)

end Stacks.Chow

end
