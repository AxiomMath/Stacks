module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingIdealSheafRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.DerivedIsomorphismLocality
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of ideals of derived completeness

Let `(𝒞, 𝒪)` be a ringed site and let `K ∈ D(𝒪)`. [Stacks, Tag 0998] asserts that the rule
sending an object `U` of `𝒞` to the set of sections `f ∈ 𝒪(U)` with `T(K|_U, f) = 0` is a sheaf
of ideals in `𝒪`. This file proves the locality of that condition and assembles the sheaf of
ideals.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedCompleteIdealSheaf`: **the sheaf of ideals of
  [Stacks, Tag 0998]**, whose sections over `U` are the sections `f` of `𝒪` with
  `T(K|_U, f) = 0`.

## Main results

* `CategoryTheory.GrothendieckTopology.coversTop_over_of_mem`: a covering sieve of `U` gives a
  family of objects of `𝒞/U` covering the final object of `𝒞/U`.
* `AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve`: **the condition
  `T(K|_U, f) = 0` is local on `U`.**
* `AlgebraicGeometry.RingedSite.mem_derivedCompleteIdealSheaf_iff`: the sections of the sheaf of
  ideals are exactly the sections satisfying that condition.

## Implementation notes

*The three steps.* The objectwise ideal
`AlgebraicGeometry.RingedSite.derivedCompleteIdealAt` and its stability under restriction
(`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.restrict`) make the rule a submodule
of the presheaf of modules underlying `𝒪`. What this file adds is the sheaf condition, and that
is assembled from three pieces.

1. `isDerivedCompleteAt_overFunctor_of_isDerivedCompleteAtSection` is the per-section form of
   the core of `AlgebraicGeometry.RingedSite.restrict_isDerivedComplete`: it carries
   `T(K|_{W.left}, g) = 0` across `CategoryTheory.Over.iteratedSliceEquiv` to the Milnor
   condition for the restriction of `K|_U` to the iterated slice `(𝒞/U)/W`. The transport
   functor is the iterated-slice equivalence of sheaves of modules
   `Stacks.SheafOfModules.InternalHom.sliceModulesEquiv`, which is additive, matches the two
   multiplication operators
   (`AlgebraicGeometry.RingedSite.sliceModulesEquiv_functor_map_terminalSectionToEnd`) and —
   being one half of an equivalence, hence a right adjoint — commutes with the countable
   products of the derived categories, so Grothendieck's AB4* is not needed.
2. `CategoryTheory.GrothendieckTopology.coversTop_over_of_mem` turns a covering sieve `S` of
   `U` into a family of objects of `𝒞/U` covering the final object `Over.mk (𝟙 U)` of `𝒞/U`,
   indexed by the arrows of `S`: the member attached to `a : V ⟶ U` is `Over.mk a`, and
   `Over.mk (a ≫ 𝟙 U) ⟶ Over.mk a` is the identity of `V`.
3. `Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` ([Stacks, Tag 08JJ], its
   locality step) reflects invertibility in `D(𝒪_U)` along such a family. Its input at the
   member `Over.mk a` is the invertibility of the *image* of the Milnor difference, not the
   Milnor difference of the image, so `isIso_map_oneSubSmulShift_of_isDerivedCompleteAt` below
   reads `AlgebraicGeometry.RingedSite.oneSubSmulShift_map_comp_piComparison` in the direction
   opposite to `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_map_of_smul_id`; the
   comparison of the countable products is invertible because derived restriction to a slice
   preserves them
   (`Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overFunctor`).

*The scalar at the iterated slice.* `Stacks.SheafOfModules.overFunctor_map_terminalSectionToEnd`
is the companion of `Stacks.SheafOfModules.overMap_map_terminalSectionToEnd` for the restriction
from a slice site to a slice of it: the compatible family of local sections which `f ∈ 𝒪(U)`
defines on `𝒞/U`, and the one which `f|_{W.left}` defines on `(𝒞/U)/W`, restrict `f` along the
same arrow of `𝒞`, by `Stacks.SheafOfModules.terminalSection_over_val` read on both sides and
`CategoryTheory.Over.w`.

*Universes.* The ringed site is a `RingedSite.{u, u, u}`, as in
`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.restrict` and for the same reason:
[Stacks, Tag 08FI] is available here as
`Stacks.Cohomology.Localization.isKInjective_over`, which pins objects, morphisms, the sheaf of
rings and the module sections to one universe, and the derived product preservation that the
locality step consumes is proved from it. It is also the generality in which [Stacks, Tag 099C] is
stated, which is the consumer of the sheaf of ideals.

*The linear structure.* `Stacks.SheafOfModules.centerLinear` is the tautological linear
structure over the centre, installed here at every depth of iterated slice;
`AlgebraicGeometry.RingedSite.overCatCenterLinear` is the same structure for one slice, and the
two agree by definition.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099C](https://stacks.math.columbia.edu/tag/099C)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u v w

namespace CategoryTheory.GrothendieckTopology

/-- **A covering sieve of `U` gives a family of objects of `C/U` covering the final object of
`C/U`.** The family is indexed by the arrows of the sieve, the member attached to `a : V ⟶ U`
being `Over.mk a`; the required arrow `Over.mk (a ≫ 𝟙 U) ⟶ Over.mk a` is the identity of `V`.

This is the shape in which the locality statements for the slice topology, such as
`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`, consume a covering of `U`. -/
@[sga "4½ Arcata 1.6.2"]
theorem coversTop_over_of_mem {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {U : C} (S : Sieve U) (hS : S ∈ J U) :
    (J.over U).CoversTop
      (fun i : Σ V : C, { a : V ⟶ U // S.arrows a } ↦ (Over.mk i.2.1 : Over U)) := by
  rw [coversTop_iff_of_isTerminal _ (Over.mk (𝟙 U)) Over.mkIdTerminal, J.mem_over_iff]
  refine J.superset_covering (fun Z a ha ↦ ?_) hS
  rw [Sieve.overEquiv_iff]
  exact ⟨⟨Z, a, ha⟩, ⟨Over.homMk (𝟙 Z) (by simp)⟩⟩

end CategoryTheory.GrothendieckTopology

namespace Stacks.SheafOfModules

/-- **The sheaves of modules over a sheaf of rings form a category linear over the centre of
itself**, by the tautological ring map. This is the linear structure the derived-completeness
predicate of [Stacks, Tag 0999] is stated at;
`AlgebraicGeometry.RingedSite.overCatCenterLinear` is the same structure for the restriction of
a structure sheaf to one slice site, and this form applies at every depth of iterated slice. -/
@[instance_reducible]
def centerLinear {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) :
    Linear (CatCenter (_root_.SheafOfModules.{w} R)) (_root_.SheafOfModules.{w} R) :=
  Linear.ofRingMorphism (RingHom.id _)

/-- **Restriction from a slice site to a slice of it matches the two multiplication operators
attached to a section.** For `W` an object of `C/U`, the compatible family of local sections of
`R.over U` which a section `f` of `R` over `U` defines on `C/U`, and the one which its
restriction `f|_{W.left}` defines on `(C/U)/W`, both restrict `f` along the arrow of `C`
underlying an object of `(C/U)/W`; so the restriction `SheafOfModules.overFunctor (R.over U) W`
carries multiplication by the first to multiplication by the second.

This is the companion of `Stacks.SheafOfModules.overMap_map_terminalSectionToEnd`, which is the
same statement for the restriction between two slices of `C` itself. -/
theorem overFunctor_map_terminalSectionToEnd {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [∀ T : Cᵒᵖ, IsMulCommutative (R.obj.obj T)] (U : C) (W : Over U)
    (f : R.obj.obj (op U)) (M : _root_.SheafOfModules.{w} (R.over U)) :
    (_root_.SheafOfModules.overFunctor.{w} (R.over U) W).map
        ((terminalSectionToEnd (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal f).asHom.app M) =
      (terminalSectionToEnd ((R.over U).over W) (Over.mk (𝟙 W)) Over.mkIdTerminal
            (R.obj.map W.hom.op f)).asHom.app
        ((_root_.SheafOfModules.overFunctor.{w} (R.over U) W).obj M) :=
  map_globalSectionToEnd (F := Over.forget W) (S := (R.over U).over W) (R := R.over U)
    (𝟙 ((R.over U).over W))
    (terminalSection (R.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal f)
    (terminalSection ((R.over U).over W) (Over.mk (𝟙 W)) Over.mkIdTerminal
      (R.obj.map W.hom.op f))
    (fun T ↦ by
      refine (terminalSection_over_val (R.over U) W (R.obj.map W.hom.op f) T).trans
        (Eq.trans ?_ (terminalSection_over_val R U f
          (op ((Over.forget W).obj (unop T)))).symm)
      change R.obj.map ((unop T).hom.left).op (R.obj.map W.hom.op f) =
        R.obj.map ((unop T).left.hom).op f
      rw [← RingCat.comp_apply, ← R.obj.map_comp, ← op_comp, Over.w])
    M

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

/-- **`T(G K, a) = 0` detects the invertibility of the image of the Milnor difference.** This is
`AlgebraicGeometry.RingedSite.oneSubSmulShift_map_comp_piComparison` read in the direction
opposite to `AlgebraicGeometry.RingedSite.isDerivedCompleteAt_map_of_smul_id`: that lemma
identifies `G (1 - a'·shift)` with `1 - a·shift` on `G K` through the comparison of the
countable products, which is invertible, so either invertibility gives the other. It is this
direction that a locality statement for the morphism `1 - a'·shift` consumes. -/
theorem isIso_map_oneSubSmulShift_of_isDerivedCompleteAt
    {A A' : Type*} [CommSemiring A] [CommSemiring A'] {D D' : Type*} [Category D] [Category D']
    [Preadditive D] [Preadditive D'] [Linear A D] [Linear A' D'] [HasProductsOfShape ℕ D]
    [HasProductsOfShape ℕ D'] (G : D' ⥤ D) [G.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) G] {L : D'} {a' : A'} {a : A}
    (hsmul : G.map (a' • 𝟙 L) = a • 𝟙 (G.obj L)) (h : IsDerivedCompleteAt (G.obj L) a) :
    IsIso (G.map (oneSubSmulShift L a')) := by
  rw [isDerivedCompleteAt_iff_isIso] at h
  have h1 : IsIso (piComparison G (fun _ : ℕ ↦ L) ≫ oneSubSmulShift (G.obj L) a) := by
    have := h
    infer_instance
  rw [← oneSubSmulShift_map_comp_piComparison G hsmul] at h1
  exact IsIso.of_isIso_comp_right _ (piComparison G (fun _ : ℕ ↦ L))

attribute [local instance] Stacks.SheafOfModules.centerLinear
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
  Stacks.Cohomology.Localization.hasProductsOfShape_nat_derivedCategory

/-- An exact functor carrying multiplication by `a` to multiplication by `b` on every object does
the same on the derived categories. -/
private theorem mapDerivedCategory_map_smul_id_of_map_app {A A' : Type*} [Category A]
    [Category A'] [Abelian A] [Abelian A'] [HasDerivedCategory A] [HasDerivedCategory A']
    (G : A' ⥤ A) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : CatCenter A') (b : CatCenter A) (h : ∀ M, G.map (a.app M) = b.app (G.obj M))
    (L : DerivedCategory A') :
    letI : Linear (CatCenter A') A' := Linear.ofRingMorphism (RingHom.id _)
    letI : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id _)
    G.mapDerivedCategory.map (a • 𝟙 L) = b • 𝟙 (G.mapDerivedCategory.obj L) := by
  let : Linear (CatCenter A') A' := Linear.ofRingMorphism (RingHom.id _)
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id _)
  exact Stacks.SheafOfModules.DerivedRestrictScalars.mapDerivedCategory_map_smul_id G a b
    (fun Z ↦ Stacks.SemilinearFunctor.map_smul_id_mapHomologicalComplex G a b
      (fun M ↦ (congrArg G.map (Category.comp_id (a.app M))).trans
        ((h M).trans (Category.comp_id (b.app (G.obj M))).symm))
      (ComplexShape.up ℤ) Z) L

variable (X : RingedSite.{u, u, u})
  (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))

/-- **The per-section form of the core of
`AlgebraicGeometry.RingedSite.restrict_isDerivedComplete`.** Let `U` be an object of `𝒞`, let
`W` be an object of `𝒞/U` and let `g` be a section of `𝒪` over `W.left`. If
`T(K|_{W.left}, g) = 0`, then the Milnor difference `1 - g·shift` is invertible on the countable
product of copies of the restriction of `K|_U` to the iterated slice `(𝒞/U)/W`.

The two statements live on different sites: the hypothesis on the slice `𝒞/W.left`, the
conclusion on `(𝒞/U)/W`. They are identified by `CategoryTheory.Over.iteratedSliceEquiv`; the
induced equivalence of categories of sheaves of modules is a pushforward, which is additive,
carries multiplication by `g` read on `𝒞/W.left` to multiplication by `g` read on `(𝒞/U)/W`,
and — being one half of an equivalence, hence a right adjoint — commutes with the countable
products of the derived categories. -/
theorem isDerivedCompleteAt_overFunctor_of_isDerivedCompleteAtSection
    (U : X.C) (W : Over U) (g : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op W.left))
    (hg : IsDerivedCompleteAtSection X K W.left g) :
    IsDerivedCompleteAt
      ((SheafOfModules.overFunctor.{u}
          (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) W).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K))
      (Stacks.SheafOfModules.terminalSectionToEnd
          ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W)
        (Over.mk (𝟙 W)) Over.mkIdTerminal g :
          CatCenter
            (SheafOfModules.{u}
              ((((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U).over W))) := by
  let E := Stacks.SheafOfModules.InternalHom.sliceModulesEquiv.{u, u, u, u} X U W
  let Φ := E.functor
  have : Φ.Additive :=
    inferInstanceAs (SheafOfModules.pushforward.{u}
      (F := (Over.iteratedSliceEquiv W).functor) (𝟙 _)).Additive
  have : E.inverse.Additive :=
    inferInstanceAs (SheafOfModules.pushforward.{u}
      (F := (Over.iteratedSliceEquiv W).inverse) (𝟙 _)).Additive
  have : Φ.IsEquivalence := inferInstanceAs E.functor.IsEquivalence
  have : E.inverse.IsEquivalence := inferInstanceAs E.inverse.IsEquivalence
  have : PreservesFiniteLimits Φ := inferInstance
  have : PreservesFiniteColimits Φ := inferInstance
  have : PreservesFiniteLimits E.inverse := inferInstance
  have : PreservesFiniteColimits E.inverse := inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ) Φ.mapDerivedCategory := by
    have adjD : E.inverse.mapDerivedCategory ⊣ Φ.mapDerivedCategory :=
      CategoryTheory.Adjunction.mapDerivedCategory E.symm.toAdjunction
    have := adjD.rightAdjoint_preservesLimits
    infer_instance
  let aL : CatCenter
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W.left)) :=
    Stacks.SheafOfModules.terminalSectionToEnd
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W.left)
      (Over.mk (𝟙 W.left)) Over.mkIdTerminal g
  let aW : CatCenter
      (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over W)) :=
    Stacks.SheafOfModules.terminalSectionToEnd
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over W)
      (Over.mk (𝟙 W)) Over.mkIdTerminal g
  have hsmulD := mapDerivedCategory_map_smul_id_of_map_app Φ aL aW
    (sliceModulesEquiv_functor_map_terminalSectionToEnd.{u, u} X U W g)
  let i₁ := Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.left) Φ
  let i₂ := Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) W)
  exact (isDerivedCompleteAt_iff_of_iso ((i₁.app K).symm ≪≫ i₂.app K) aW).mp
    (isDerivedCompleteAt_map_of_smul_id Φ.mapDerivedCategory (hsmulD _) hg)

/-- **The condition `T(K|_U, f) = 0` is local on `U`.** If `S` is a covering sieve of `U` and
`T(K|_V, f|_V) = 0` for every arrow `a : V ⟶ U` of `S`, then `T(K|_U, f) = 0`.

This is the sheaf condition of [Stacks, Tag 0998], whose verification the source omits. The
condition is the invertibility of the Milnor difference `1 - f·shift` on `D(𝒪_U)`;
invertibility there is local on `𝒞/U`
(`Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory`, the locality step of
[Stacks, Tag 08JJ]), the arrows of `S` give a family covering the final object of `𝒞/U`
(`CategoryTheory.GrothendieckTopology.coversTop_over_of_mem`), and at the member `Over.mk a` the
image of the Milnor difference is invertible because `T(K|_V, f|_V) = 0` transports to the
iterated slice. -/
theorem IsDerivedCompleteAtSection.of_sieve {U : X.C}
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))
    (S : Sieve U) (hS : S ∈ X.J U)
    (hf : ∀ {V : X.C} (a : V ⟶ U), S.arrows a →
      IsDerivedCompleteAtSection X K V
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map a.op f)) :
    IsDerivedCompleteAtSection X K U f := by
  have := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
    (J := X.J.over U)
  have := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
    (J := X.J.over U)
  have : ∀ W : Over U, HasSheafify ((X.J.over U).over W) AddCommGrpCat.{u} := fun W ↦
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, u, u}
      (J := (X.J.over U).over W)
  have : ∀ W : Over U,
      ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u} := fun W ↦
    Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
      (J := (X.J.over U).over W)
  have : ∀ W : Over U, PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) W).mapDerivedCategory := fun W ↦
    Stacks.Cohomology.Localization.preservesProducts_mapDerivedCategory_overFunctor
      (X.J.over U) ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) W
  change IsIso (oneSubSmulShift
    ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.obj K)
    (overTerminalRingHom X U f))
  refine Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory
    (X.J.coversTop_over_of_mem S hS) _ fun i ↦ ?_
  obtain ⟨V, a, ha⟩ := i
  let W : Over U := Over.mk a
  let G := SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) W
  let aU : CatCenter (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
    overTerminalRingHom X U f
  let aW : CatCenter
      (SheafOfModules.{u} (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over W)) :=
    Stacks.SheafOfModules.terminalSectionToEnd
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over W)
      (Over.mk (𝟙 W)) Over.mkIdTerminal
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a.op f)
  have hsmulD := mapDerivedCategory_map_smul_id_of_map_app G aU aW
    (Stacks.SheafOfModules.overFunctor_map_terminalSectionToEnd
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U W f)
  exact isIso_map_oneSubSmulShift_of_isDerivedCompleteAt G.mapDerivedCategory (hsmulD _)
    (isDerivedCompleteAt_overFunctor_of_isDerivedCompleteAtSection X K U W
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map a.op f) (hf a ha))

/-- **[Stacks, Tag 0998]: the sections `f` of `𝒪` with `T(K|_U, f) = 0` form a sheaf of ideals
in `𝒪`.** For a ringed site `(𝒞, 𝒪)` and `K ∈ D(𝒪)`, the rule sending an object `U` of `𝒞` to
`{f ∈ 𝒪(U) | T(K|_U, f) = 0}` is a sheaf of ideals: the value at each object is an ideal
(`AlgebraicGeometry.RingedSite.derivedCompleteIdealAt`), the values are stable under
restriction (`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.restrict`), and
membership is local (`AlgebraicGeometry.RingedSite.IsDerivedCompleteAtSection.of_sieve`). -/
@[stacks 0998]
def derivedCompleteIdealSheaf :
    SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) where
  obj V := derivedCompleteIdealAt X K V.unop
  map {V W} a := fun x hx ↦ (mem_derivedCompleteIdealAt_iff X K W.unop _).2
    (IsDerivedCompleteAtSection.restrict X K a.unop x
      ((mem_derivedCompleteIdealAt_iff X K V.unop x).1 hx))
  isSheaf {V} s hs := (mem_derivedCompleteIdealAt_iff X K V.unop s).2
    (IsDerivedCompleteAtSection.of_sieve X K s _ hs fun {Z} _ ha ↦
      (mem_derivedCompleteIdealAt_iff X K Z _).1 ha)

/-- The sections of the sheaf of ideals of [Stacks, Tag 0998] over `U` are the sections `f` of
`𝒪` with `T(K|_U, f) = 0`. -/
@[simp]
theorem mem_derivedCompleteIdealSheaf_iff (U : X.C)
    (f : ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U)) :
    f ∈ (derivedCompleteIdealSheaf X K).toSubmodule.obj (op U) ↔
      IsDerivedCompleteAtSection X K U f :=
  mem_derivedCompleteIdealAt_iff X K U f

/-- The sections of the sheaf of ideals of [Stacks, Tag 0998] over `U` are
`AlgebraicGeometry.RingedSite.derivedCompleteIdealAt`, by definition. -/
theorem derivedCompleteIdealSheaf_toSubmodule_obj (V : X.Cᵒᵖ) :
    (derivedCompleteIdealSheaf X K).toSubmodule.obj V = derivedCompleteIdealAt X K V.unop := rfl

end AlgebraicGeometry.RingedSite

end
