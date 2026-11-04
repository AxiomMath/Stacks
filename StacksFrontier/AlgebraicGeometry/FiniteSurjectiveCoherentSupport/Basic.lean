module

public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FinitePushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Specialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent sheaves supported on an integral closed subscheme

Let `f : Y ⟶ X` be a finite surjective morphism with `X` locally Noetherian and let `i : Z ⟶ X`
be an integral closed subscheme with generic point `ξ`. This file constructs a coherent module
on `Y` whose direct image has support exactly `Z` and whose stalk at `ξ` is annihilated by the
maximal ideal of `𝒪_{X,ξ}`.

The construction is the one in the source: pick `ξ'` in the fibre of `f` over `ξ`, let `W` be the
reduced closed subscheme of `Y` supported on the closure of `{ξ'}`, and take `ℱ = j_* 𝒪_W` for
`j : W ⟶ Y` the inclusion. Writing `g = j ≫ f`, the direct image `f_* ℱ` *is* `g_* 𝒪_W`: the two
are definitionally equal, so no comparison isomorphism appears anywhere below.

## Main results

* `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.isZero_stalk_pushforward_of_notMem`:
  the stalk of a direct image of a sheaf of abelian groups vanishes at every point outside a
  closed set containing the range of the morphism. Only closedness of that set is used, not
  injectivity of the morphism.
* `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.supp_pushforward_subset`: the
  module-sheaf form of the same statement.
* `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.nontrivial_stalk_unit`: the stalk of
  the unit object of the category of sheaves of modules is nontrivial at every point.
* `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.range_eq_closure_genericPoint`: the
  range of a closed immersion with integral source is the closure of the image of the generic
  point.
* `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.subschemeι_genericPoint_closure`: the
  generic point of the reduced closed subscheme supported on the closure of `{x}` maps to `x`.
* `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.smul_maximalIdeal_stalk_eq_zero`: for
  a finite morphism out of an integral scheme whose fibre over the image of the generic point is
  a single point, the maximal ideal downstairs annihilates the stalk of the direct image of the
  structure sheaf there.
* `exists_isCoherent_of_pointClosure` is the construction with the point closure supplied as
  data, and `exists_isCoherent_supp_pushforward_eq_range` is the theorem, both in the namespace
  `Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport`.

## Implementation notes

Two places where the route taken here is shorter than the obvious one.

The image point `g ξ'` is *equal* to `ξ`, not merely inseparable from it, so the annihilation
statement is proved at `g ξ'` and transported by `subst`; the target point is a variable of
`smul_maximalIdeal_stalk_eq_zero` precisely so that this is available. Routing the same transport
through `TopCat.Presheaf.stalkCongr` instead would need the compatibility of
`TopCat.Presheaf.stalkSpecializes` with the scalar action on the stalk of a presheaf of modules,
which is not available in either tree.

The containment `supp (f_* ℱ) ⊆ Z` is proved from closedness of `Set.range i` alone. The source
argues instead that `f_* ℱ` is of the form `i_*(-)`, which needs the factorization of `g` through
the scheme-theoretic image of `i` — available as
`AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support` — and
then the stalk vanishing for the closed *embedding* `i`. The hypothesis actually consumed by
`ClosedImmersionSheaves.pushforwardStalkIsoOfEmptyPreimage` is only that the preimage of some
neighbourhood of the point is empty, so neither the factorization nor injectivity is needed.

Closedness of the support is likewise not needed: `Set.range i` is the closure of `{ξ}`, so the
reverse containment follows from stability of the support of a quasi-coherent module under
specialization, `AlgebraicGeometry.Scheme.Modules.stableUnderSpecialization_supp`.

## References

* [Stacks Project, Tag 01YO](https://stacks.math.columbia.edu/tag/01YO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport

/-! ### Stalks of a direct image away from the range -/

/-- The stalk of a direct image `p _* F` of a sheaf of abelian groups vanishes at every point
outside a closed set containing the range of `p`.

Only closedness of `K` is used: the complement of `K` is an open neighbourhood of `z` whose
preimage is empty, which is the whole input of
`ClosedImmersionSheaves.pushforwardStalkIsoOfEmptyPreimage`. In particular `p` need not be
injective, so this applies to a finite morphism and not only to a closed immersion. -/
@[ega "IV 21.9.1" "partial"]
lemma isZero_stalk_pushforward_of_notMem {T S : TopCat.{u}} (p : T ⟶ S)
    {F : T.Presheaf AddCommGrpCat.{u}} (hF : F.IsSheaf)
    {K : Set S} (hK : IsClosed K) (hrange : Set.range (ConcreteCategory.hom p) ⊆ K)
    {z : S} (hz : z ∉ K) :
    IsZero (TopCat.Presheaf.stalk (p _* F) z) := by
  let V : Opens S := ⟨Kᶜ, hK.isOpen_compl⟩
  have hV : (Opens.map p).obj V = ⊥ :=
    le_antisymm (fun w hw => hw (hrange (Set.mem_range_self w))) bot_le
  have hterm : IsTerminal (TopCat.Presheaf.stalk (p _* F) z) :=
    IsTerminal.ofIso (ClosedImmersionSheaves.isTerminalPushforwardObj p hF V hV)
      (ClosedImmersionSheaves.pushforwardStalkIsoOfEmptyPreimage p hF z V hz hV)
  exact IsZero.of_iso (isZero_zero AddCommGrpCat.{u})
    (hterm.uniqueUpToIso HasZeroObject.zeroIsTerminal)

/-- The support of a direct image of a sheaf of modules is contained in every closed set
containing the range of the morphism. -/
lemma supp_pushforward_subset {W X : Scheme.{u}} (g : W ⟶ X) (N : W.Modules)
    {K : Set X} (hK : IsClosed K) (hrange : Set.range g.base ⊆ K) :
    SheafOfModules.supp ((Scheme.Modules.pushforward g).obj N) ⊆ K := by
  rintro z ⟨a, ha⟩
  by_contra hzK
  exact ha ((AddCommGrpCat.subsingleton_of_isZero
    (isZero_stalk_pushforward_of_notMem g.base (Scheme.Modules.isSheaf N) hK hrange hzK)).elim a 0)

/-! ### The stalks of the structure sheaf as a sheaf of modules -/

/-- The stalk of the unit object of the category of sheaves of modules on a scheme is nontrivial
at every point: it is the stalk of the structure sheaf, which is a local ring.

The stalk is computed in `AddCommGrpCat` and the ring stalk in `CommRingCat`, so the two
forgetful functors have to be commuted past the defining filtered colimit. -/
lemma nontrivial_stalk_unit (W : Scheme.{u}) (x : W) :
    Nontrivial (TopCat.Presheaf.stalk (C := Ab.{u})
      (SheafOfModules.unit W.ringCatSheaf).val.presheaf x) := by
  let D₀ := (OpenNhds.inclusion x).op ⋙ W.presheaf
  let D := (OpenNhds.inclusion x).op ⋙ W.ringCatSheaf.obj
  let eCR := preservesColimitIso (forget₂ CommRingCat RingCat) D₀
  let eAb := preservesColimitIso (forget₂ RingCat AddCommGrpCat) D
  show Nontrivial ↑(colimit (D ⋙ forget₂ RingCat AddCommGrpCat))
  have h₀ : Nontrivial ((forget₂ CommRingCat RingCat).obj (colimit D₀)) := by
    show Nontrivial ↑(W.presheaf.stalk x)
    infer_instance
  have hD : Nontrivial ↑(colimit D) :=
    (ConcreteCategory.bijective_of_isIso eCR.hom).injective.nontrivial
  exact (ConcreteCategory.bijective_of_isIso eAb.hom).injective.nontrivial

/-- The generic point of an integral scheme lies in the support of the direct image of its
structure sheaf, provided the fibre of the morphism over its image is that point alone. -/
lemma mem_supp_pushforward_unit {W X : Scheme.{u}} (g : W ⟶ X) [IsFinite g] [IsIntegral W]
    (hfibre : g.base ⁻¹' ({g (genericPoint W)} : Set X) = {genericPoint W}) :
    g (genericPoint W) ∈ SheafOfModules.supp
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit W.ringCatSheaf)) := by
  have _ := nontrivial_stalk_unit W (genericPoint W)
  let _ : Module (W.presheaf.stalk (genericPoint W))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit W.ringCatSheaf).val.presheaf (genericPoint W)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := W.presheaf) (SheafOfModules.unit W.ringCatSheaf).val (genericPoint W)
  let _ : Module (X.presheaf.stalk (g (genericPoint W)))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit W.ringCatSheaf).val.presheaf (genericPoint W)) :=
    Module.compHom _ (g.stalkMap (genericPoint W)).hom
  obtain ⟨e⟩ := _root_.AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber
    g (genericPoint W) hfibre (SheafOfModules.unit W.ringCatSheaf)
  have := (ConcreteCategory.bijective_of_isIso e.hom).injective.nontrivial
  exact exists_ne 0

/-! ### A scalar that annihilates one side of an isomorphism annihilates the other -/

/-- If a ring element annihilates `M` and `M` is isomorphic to `N` in `ModuleCat R`, then it
annihilates `N`.

Every typeclass argument here is a variable, so the scalar actions in the statement are the ones
carried by `e` rather than ones instance search has to rediscover at the application site; that
is what makes this usable against an isomorphism whose module structures are supplied as inlined
`let`s. -/
lemma smul_eq_zero_of_moduleCatIso {R : Type u} [Ring R] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : ModuleCat.of R M ≅ ModuleCat.of R N) {a : R} (ha : ∀ m : M, a • m = 0) (n : N) :
    a • n = 0 := by
  apply (ConcreteCategory.bijective_of_isIso e.inv).1
  rw [e.inv.hom.map_smul, ha, e.inv.hom.map_zero]

/-! ### Generic points of closed subschemes -/

/-- Alias of `Stacks.AlgebraicGeometry.ComponentDegrees.range_eq_closure_genericPoint`. -/
alias range_eq_closure_genericPoint :=
  _root_.Stacks.AlgebraicGeometry.ComponentDegrees.range_eq_closure_genericPoint

/-- The generic point of the reduced closed subscheme supported on the closure of `{x}` maps to
`x`. -/
lemma subschemeι_genericPoint_closure {X : Scheme.{u}} (x : X) :
    (letI := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
     (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))).subschemeι
       (genericPoint (Scheme.IdealSheafData.vanishingIdeal
         (Closeds.closure ({x} : Set X))).subscheme) = x) := by
  let _ := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x
  set I : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) with hI
  have hsupport : (I.support : Set X) = closure ({x} : Set X) := by
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hclosure : closure ({I.subschemeι (genericPoint I.subscheme)} : Set X) =
      closure ({x} : Set X) := by
    rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, I.range_subschemeι, hsupport]
  exact isGenericPoint_closure.eq (hclosure ▸ isGenericPoint_closure)

/-! ### Annihilation of the generic stalk -/

/-- Let `g : W ⟶ X` be a finite morphism out of an integral scheme whose fibre over the image `q`
of the generic point `ξ'` of `W` is that single point. Then the maximal ideal of `𝒪_{X,q}`
annihilates the stalk of `g_* 𝒪_W` at `q`.

That stalk is the stalk of `𝒪_W` at `ξ'` by
`AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber`, and the latter is a
field, so the local homomorphism `𝒪_{X,q} ⟶ 𝒪_{W,ξ'}` kills the maximal ideal outright.

The target point `q` is a variable, with the identification `g ξ' = q` a hypothesis, so that
transport to another spelling of the point is a `subst` rather than a comparison of stalks along
`TopCat.Presheaf.stalkSpecializes`. -/
lemma smul_maximalIdeal_stalk_eq_zero {W X : Scheme.{u}} (g : W ⟶ X) [IsFinite g] [IsIntegral W]
    (hfibre : g.base ⁻¹' ({g (genericPoint W)} : Set X) = {genericPoint W})
    (q : X) (hq : g (genericPoint W) = q) :
    (letI : Module (X.presheaf.stalk q)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pushforward g).obj
            (SheafOfModules.unit W.ringCatSheaf)).val.presheaf q) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf)
        ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit W.ringCatSheaf)).val q
     ∀ a : X.presheaf.stalk q, a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk q) →
       ∀ s : TopCat.Presheaf.stalk (C := Ab.{u})
         ((Scheme.Modules.pushforward g).obj
           (SheafOfModules.unit W.ringCatSheaf)).val.presheaf q, a • s = 0) := by
  subst hq
  intro a ha s
  let _ : Module (X.presheaf.stalk (g (genericPoint W)))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pushforward g).obj
          (SheafOfModules.unit W.ringCatSheaf)).val.presheaf (g (genericPoint W))) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf)
      ((Scheme.Modules.pushforward g).obj (SheafOfModules.unit W.ringCatSheaf)).val
      (g (genericPoint W))
  let _ : Module (W.presheaf.stalk (genericPoint W))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit W.ringCatSheaf).val.presheaf (genericPoint W)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := W.presheaf) (SheafOfModules.unit W.ringCatSheaf).val (genericPoint W)
  let _ : Module (X.presheaf.stalk (g (genericPoint W)))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit W.ringCatSheaf).val.presheaf (genericPoint W)) :=
    Module.compHom _ (g.stalkMap (genericPoint W)).hom
  obtain ⟨e⟩ := _root_.AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber
    g (genericPoint W) hfibre (SheafOfModules.unit W.ringCatSheaf)
  have hkill : g.stalkMap (genericPoint W) a = 0 := by
    by_contra hne
    exact ((IsLocalRing.mem_maximalIdeal _).mp ha)
      (IsLocalHom.map_nonunit (f := (g.stalkMap (genericPoint W)).hom) a
        (isUnit_iff_ne_zero.mpr hne))
  have hsource : ∀ r : TopCat.Presheaf.stalk (C := Ab.{u})
      (SheafOfModules.unit W.ringCatSheaf).val.presheaf (genericPoint W), a • r = 0 := by
    intro r
    show (g.stalkMap (genericPoint W) a) • r = 0
    rw [hkill, zero_smul]
  exact smul_eq_zero_of_moduleCatIso e hsource s

/-! ### The theorem -/

/-- The fibre of a finite morphism out of an integral scheme over the image of the generic point
is that point alone. -/
private lemma preimage_singleton_genericPoint_eq {W X : Scheme.{u}} (g : W ⟶ X) [IsFinite g]
    [IsIntegral W] : g.base ⁻¹' ({g (genericPoint W)} : Set X) = {genericPoint W} := by
  have _ : DiscreteTopology (g.base ⁻¹' ({g (genericPoint W)} : Set X)) :=
    isDiscrete_iff_discreteTopology.mp (g.isDiscrete_preimage_singleton (g (genericPoint W)))
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun hz => ?_, fun h => by rw [h]⟩
  have hsp : (⟨genericPoint W, rfl⟩ : g.base ⁻¹' ({g (genericPoint W)} : Set X)) ⤳ ⟨z, hz⟩ :=
    (subtype_specializes_iff _ _).mpr (genericPoint_specializes z)
  exact (congrArg Subtype.val (specializes_iff_eq.mp hsp)).symm

/-- The construction behind [Stacks, Tag 01YO], with the closure of the chosen point of the fibre
supplied as an integral closed subscheme `j : W ⟶ Y` whose generic point lies over `ξ`. -/
theorem exists_isCoherent_of_pointClosure {X Y Z W : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (j : W ⟶ Y) [IsClosedImmersion j] [IsIntegral W]
    (hpoint : f (j (genericPoint W)) = i (genericPoint Z)) :
    ∃ F : Y.Modules, F.IsCoherent ∧
      SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) = Set.range i ∧
      (let G := (Scheme.Modules.pushforward f).obj F
       let x := i (genericPoint Z)
       letI : Module (X.presheaf.stalk x)
           (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
         PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
           (R := X.presheaf) G.val x
       ∀ a : X.presheaf.stalk x,
         a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
         ∀ s : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x, a • s = 0) := by
  classical
  have _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian j
  have hgpoint : (j ≫ f) (genericPoint W) = i (genericPoint Z) := hpoint
  -- the two ranges, as closures of the two generic points
  have hiclosure : Set.range i.base = closure ({i (genericPoint Z)} : Set X) :=
    range_eq_closure_genericPoint i
  have hrange : Set.range (j ≫ f).base ⊆ Set.range i.base := by
    rw [hiclosure]
    rintro z ⟨w, rfl⟩
    have hw : j w ∈ closure ({j (genericPoint W)} : Set Y) :=
      range_eq_closure_genericPoint j ▸ ⟨w, rfl⟩
    have hsp := (specializes_iff_mem_closure.mpr hw).map f.continuous
    rw [hpoint] at hsp
    exact specializes_iff_mem_closure.mp hsp
  have hfibre := preimage_singleton_genericPoint_eq (j ≫ f)
  refine ⟨(Scheme.Modules.pushforward j).obj (SheafOfModules.unit W.ringCatSheaf),
    FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite j _, ?_, fun a ha s => ?_⟩
  · show SheafOfModules.supp ((Scheme.Modules.pushforward (j ≫ f)).obj
      (SheafOfModules.unit W.ringCatSheaf)) = Set.range i.base
    refine Set.Subset.antisymm (supp_pushforward_subset (j ≫ f) _
      i.isClosedEmbedding.isClosed_range hrange) ?_
    have hxgen : IsGenericPoint (i (genericPoint Z)) (Set.range i.base) := hiclosure.symm
    have _ : ((Scheme.Modules.pushforward (j ≫ f)).obj
        (SheafOfModules.unit W.ringCatSheaf)).IsQuasicoherent :=
      AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom (j ≫ f) _
    intro z hz
    refine _root_.AlgebraicGeometry.Scheme.Modules.stableUnderSpecialization_supp X _
      (hxgen.specializes hz) ?_
    rw [← hgpoint]
    exact mem_supp_pushforward_unit (j ≫ f) hfibre
  · exact smul_maximalIdeal_stalk_eq_zero (j ≫ f) hfibre (i (genericPoint Z)) hgpoint a ha s

/-- **[Stacks, Tag 01YO].** Let `f : Y ⟶ X` be finite and surjective with `X` locally Noetherian
and let `i : Z ⟶ X` be an integral closed subscheme with generic point `ξ`. Then there is a
coherent module `ℱ` on `Y` whose direct image `f_* ℱ` has support exactly `Z` and whose stalk at
`ξ` is annihilated by the maximal ideal of `𝒪_{X,ξ}`. -/
@[stacks 01YO]
theorem exists_isCoherent_supp_pushforward_eq_range
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f]
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] :
    ∃ F : Y.Modules, F.IsCoherent ∧
      SheafOfModules.supp ((Scheme.Modules.pushforward f).obj F) = Set.range i ∧
      (let G := (Scheme.Modules.pushforward f).obj F
       let x := i (genericPoint Z)
       letI : Module (X.presheaf.stalk x)
           (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
         PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
           (R := X.presheaf) G.val x
       ∀ a : X.presheaf.stalk x,
         a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) →
         ∀ s : TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x, a • s = 0) := by
  obtain ⟨y, hy⟩ := (show Function.Surjective f.base from f.surjective) (i (genericPoint Z))
  let _ := Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure y
  exact exists_isCoherent_of_pointClosure f i
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set Y))).subschemeι
    (by rw [subschemeι_genericPoint_closure y, hy])

end Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport

end
