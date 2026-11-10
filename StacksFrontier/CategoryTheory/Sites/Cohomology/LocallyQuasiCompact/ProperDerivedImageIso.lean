module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.PullbackProperness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiCohomologyOverOpens
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiOverCoveringSieves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSheafToPresheafUnivLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperFibrewiseVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneFlasqueVanishing

/-!
# The derived clause of Stacks 0DCU: the derived Zariski base-change map of a proper morphism

Let `S` be a locally quasi-compact Zariski situation and `f : X ⟶ Y` a morphism of its site which
is proper in the sense of [Stacks, Tag 005O (5)]. This file proves the derived clause of
[Stacks, Tag 0DCU]: the derived base-change comparison
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.properDerivedImageComparison` is invertible.

The reduction `isIso_properDerivedImageComparison_of_locallyZero_cohomologyPresheaf` asks
only that, for every injective abelian sheaf `J` on the small Zariski site of `X`, every
`p > 0`, every object `W` of `LC_Zar/Y` and every class

`ξ ∈ H^p_{LC_Zar/X}(W ×_Y X, π_X^{-1} J)`,

there be a covering sieve of `W` all of whose members kill `ξ` by restriction. What is proved here
is that hypothesis, and it is assembled from four inputs:

* the local vanishing on a space, `Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber`, applied to
  the base change `f' : W ×_Y X ⟶ W.left` — which is again proper, by
  `isProperMap_pullback_fst` — and to the sheaf `h^{-1} J`, whose restriction to every fibre of
  `f'` is soft by `isSoft_restrictionFunctorUnivLE_fiber_snd_of_isFlasque`, `J` being flasque
  because it is injective;
* the comparison of the two cohomology theories at the *open subobjects* of `W ×_Y X`,
  `zariskiRightDerivedPresheafOverOpensIso`, which is natural in the open subset, as the
  transport of a statement about restriction maps requires;
* [Stacks, Tag 072W] with the coefficient universe freed,
  `Stacks.Cohomology.FreeYonedaUnivLE.rightDerivedObjIsoCohomologyPresheaf`, which identifies the
  right derived functors of `sheafToPresheaf` on a space with the `Ext`-theoretic cohomology
  presheaf that the local vanishing speaks about;
* the passage from the pointwise topology of `W.left` to the inductive Zariski topology of
  `LC_Zar/Y`, `equalizerSieve_mem_zariskiTopology_over_of_forall_exists_opens`.

## Main results

All in the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`.

* `map_eq_zero_of_opensOverHom_map_eq_zero`: a section of a presheaf on `LC_Zar/X` killed by the
  open immersion of `V ⊆ Z.left` is killed by every morphism into `Z` whose image lies in `V`.
* `exists_opens_map_eq_zero_of_isSoft_fiber`: **the local vanishing at an object of the big
  site** — around every point of the target of a proper `π` there is an open subset whose
  preimage, as an open subobject of `Over.mk q`, kills `ξ`.
* `equalizerSieve_mem_over_of_isProperMap`: the hypothesis of the reduction, verified.
* `properDerivedImageComparison_isIso`: **[Stacks, Tag 0DCU], the derived clause.**
* `properDerivedImageComparison_isIso_unconditional`: the same with the four sheafifications and
  the three enough-injectives inputs discharged rather than assumed, so that properness is the
  only hypothesis.

## Implementation notes

The coefficient universe is `max (u + 1) v` throughout, and the inputs on a space have to be read
there rather than at `v`: `Stacks.Topology.restrictionCohomologyPresheaf.{t}` is built on
`Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{max u t}`, so only a `t` that already absorbs the
universe of the space makes the two sides the same term — `freeYoneda.{t}` and
`freeYoneda.{max u t}` differ in their `ULift` level and are not definitionally equal. At
`t := max (u + 1) v` they agree on the nose.

`TopologicalSpace.Opens` is a partial order, so its morphisms are a subsingleton and the two
factorisations of one inclusion of opens that arise — `(Opens.map f').obj V ⟶ (Opens.map f').obj ⊤`
on one side and `(Opens.map f').obj V ⟶ ⊤` on the other — are identified by `Subsingleton.elim`,
with no rewriting under the opaque `Ext`-valued presheaves.

The identity that turns the restriction along `Over.map q` of an inclusion of opens into the open
immersion of the smaller open subobject is `CategoryTheory.Over.w` of that inclusion read in
`LC_Zar/T`; `Over.map` leaves the left component untouched, so `Over.OverMorphism.ext` closes it.

`HasExt` is an `abbrev` for a universally quantified statement, so
`Stacks.Topology.hasExt_sheafOpens` cannot be registered as an instance and is introduced by
`let` inside each proof, as in
`StacksFrontier/Topology/Sheaves/Cohomology/CompactSubset/ProperFibrewiseVanishing.lean`.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe t u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- **The degree-`p` cohomology presheaf of `π_X^{-1} J` on the localized Zariski site over `X`.**
This is the presheaf whose local vanishing the derived clause of [Stacks, Tag 0DCU] reduces to;
having a name for it is what lets it be supplied as an explicit argument, so that no higher-order
unification problem is posed by the shape `P.obj (op Z)` of a section. -/
abbrev zariskiInverseImageCohomologyPresheaf {X : S.category}
    [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
    (p : ℕ) (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
  ((sheafToPresheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
    ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)

/-- **A section killed by the open immersion of `V ⊆ Z.left` is killed by every morphism into `Z`
whose image lies in `V`.** Such a morphism factors through the open subobject cut out by `V`
(`exists_over_hom_opensToSlice_factor`), and a presheaf of abelian groups sends the resulting
composite to a map through zero. -/
theorem map_eq_zero_of_opensOverHom_map_eq_zero {X : S.category} {Z E : Over X}
    (P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{t}) (ξ : ToType (P.obj (op Z)))
    (κ : E ⟶ Z) (V : Opens Z.left.obj)
    (hκ : ∀ e : E.left.obj, (κ.left : E.left.obj → Z.left.obj) e ∈ V)
    (hV : P.map (opensOverHom S Z V).op ξ = 0) :
    P.map κ.op ξ = 0 := by
  obtain ⟨θ, hθ⟩ := exists_over_hom_opensToSlice_factor S κ V hκ
  have hcomp : P.map κ.op = P.map (opensOverHom S Z V).op ≫ P.map θ.op := by
    rw [← P.map_comp, ← op_comp, hθ]
  rw [hcomp, ConcreteCategory.comp_apply, hV, map_zero]

section LocalVanishing

variable {X : S.category} {T : S.category} (q : T ⟶ X) {U : S.category}
  (π : T ⟶ U)
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  (p : ℕ) (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})

/-- **The local vanishing of the higher cohomology of `π_X^{-1} J` at an object of the big site.**
Let `q : T ⟶ X` and `π : T ⟶ U` be morphisms of the site with `π` closed, with quasi-compact
fibres and with separated points, and suppose the restriction of `q^{-1} J` to every fibre of `π`
is soft. Then every class in `H^p_{LC_Zar/X}(Over.mk q, π_X^{-1} J)`, for `p > 0`, dies on the
open subobject cut out by `π^{-1} V` for some open neighbourhood `V` of any prescribed point
of `U`.

This is `Stacks.Topology.equalizerSieve_mem_of_isSoft_fiber` read through
`zariskiRightDerivedPresheafOverOpensIso` and the freed [Stacks, Tag 072W] bridge: those two
identify the cohomology presheaf of `q^{-1} J` on the space of `T` with the cohomology of
`π_X^{-1} J` at the open subobjects of `Over.mk q`, naturally in the open subset, which is what
transporting a statement about restriction maps requires. -/
theorem exists_opens_map_eq_zero_of_isSoft_fiber
    (hcl : IsClosedMap
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map π).hom : T.obj → U.obj))
    (hcpt : ∀ z : U.obj, IsCompact
      ((((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map π).hom :
        T.obj → U.obj) ⁻¹' ({z} : Set U.obj)))
    (hsep : IsSeparatedMap
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map π).hom : T.obj → U.obj))
    (hsoft : ∀ z : U.obj, IsSoft ((restrictionFunctorUnivLE.{max (u + 1) v}
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj T)
      ((((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map π).hom :
        T.obj → U.obj) ⁻¹' ({z} : Set U.obj))).obj
      ((inverseImageUnivLE.{max (u + 1) v}
        ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map q)).obj J)))
    (hp : 0 < p)
    (ξ : ToType ((((sheafToPresheaf (S.zariskiTopology.over X)
        AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)).obj (op (Over.mk q))))
    (z : U.obj) :
    ∃ V : Opens U.obj, z ∈ V ∧
      (((sheafToPresheaf (S.zariskiTopology.over X)
            AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)).map
        (opensOverHom S (Over.mk q)
          ((Opens.map ((S.qcSite.inclusion ⋙
            locallyQuasiCompactHausdorffToTop).map π)).obj V)).op ξ = 0 := by
  let _hextT : HasExt.{max (u + 1) v} (Sheaf (Opens.grothendieckTopology T.obj)
      AddCommGrpCat.{max (u + 1) v}) :=
    hasExt_sheafOpens.{max (u + 1) v} T.obj.obj
  let _hextT' : HasExt.{max (u + 1) v} (Sheaf (Opens.grothendieckTopology
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj T))
      AddCommGrpCat.{max (u + 1) v}) :=
    hasExt_sheafOpens.{max (u + 1) v} _
  let _hiT' : EnoughInjectives (Sheaf (Opens.grothendieckTopology
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj T))
      AddCommGrpCat.{max (u + 1) v}) :=
    Stacks.Topology.enoughInjectives_sheafOpens.{max (u + 1) v} _
  let _hiT : EnoughInjectives (Sheaf (Opens.grothendieckTopology T.obj)
      AddCommGrpCat.{max (u + 1) v}) :=
    enoughInjectives_sheafOpens_site.{u, w, v} S T
  let _hoT : EnoughInjectives (Sheaf (S.zariskiTopology.over T)
      AddCommGrpCat.{max (u + 1) v}) :=
    enoughInjectives_zariskiSliceSheaf.{u, w, v} S T
  let _hsT : HasSheafify (Opens.grothendieckTopology T.obj) AddCommGrpCat.{max (u + 1) v} :=
    hasSheafify_opens.{u, w, v} S T
  let πtop : (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj T ⟶
      (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj U :=
    (S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map π
  let G : Sheaf (Opens.grothendieckTopology T.obj) AddCommGrpCat.{max (u + 1) v} :=
    (inverseImageUnivLE.{max (u + 1) v}
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map q)).obj J
  let Dp : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
    ((sheafToPresheaf (S.zariskiTopology.over X)
      AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)
  let Pt : (Opens T.obj)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
    ((sheafToPresheaf (Opens.grothendieckTopology T.obj)
      AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj G
  let Pb : (Opens T.obj)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
    (S.opensToSlice T).1.op ⋙ (Over.map q).op ⋙ Dp
  let Pc : (Opens T.obj)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
    restrictionCohomologyPresheaf.{max (u + 1) v} T.obj.obj G p
  let Φ : Pt ≅ Pb := zariskiRightDerivedPresheafOverOpensIso.{u, w, v} S q p J
  let Ψ : Pt ≅ Pc :=
    Stacks.Cohomology.FreeYonedaUnivLE.rightDerivedObjIsoCohomologyPresheaf.{max (u + 1) v}
      (Opens.grothendieckTopology T.obj) G p
  -- the class `ξ`, read on the top open subobject and transported to the space of `T`
  let η : ToType (Pb.obj (op ((Opens.map πtop).obj ⊤))) :=
    Dp.map (opensOverHom S (Over.mk q) ((Opens.map πtop).obj ⊤)).op ξ
  let θ : ToType (Pt.obj (op ((Opens.map πtop).obj ⊤))) :=
    Φ.inv.app (op ((Opens.map πtop).obj ⊤)) η
  -- the local vanishing on the space of `U`
  obtain ⟨V, g, hg, hzV⟩ :=
    equalizerSieve_mem_of_isSoft_fiber.{max (u + 1) v, u} G πtop hcl hcpt hsep hsoft p hp ⊤
      (Ψ.hom.app (op ((Opens.map πtop).obj ⊤)) θ) z (by trivial)
  refine ⟨V, hzV, ?_⟩
  -- the inclusion of opens, pulled back along `π`
  have hPt : Pt.map ((Opens.map πtop).map g).op θ = 0 := by
    have hnat := ConcreteCategory.congr_hom (Ψ.inv.naturality ((Opens.map πtop).map g).op)
      (Ψ.hom.app (op ((Opens.map πtop).obj ⊤)) θ)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      Iso.hom_inv_id_app_apply] at hnat
    rw [← hnat]
    have hg0 : Pc.map ((Opens.map πtop).map g).op
        (Ψ.hom.app (op ((Opens.map πtop).obj ⊤)) θ) = 0 := by
      refine hg.trans ?_
      exact map_zero _
    rw [show Pc.map ((Opens.map πtop).map g).op
        (Ψ.hom.app (op ((Opens.map πtop).obj ⊤)) θ) = 0 from hg0, map_zero]
  have hPb : Pb.map ((Opens.map πtop).map g).op η = 0 := by
    have hnat := ConcreteCategory.congr_hom (Φ.hom.naturality ((Opens.map πtop).map g).op) θ
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
    have hη : Φ.hom.app (op ((Opens.map πtop).obj ⊤)) θ = η :=
      Iso.inv_hom_id_app_apply Φ _ η
    rw [hη] at hnat
    rw [← hnat, hPt, map_zero]
  -- the two factorisations of one inclusion of open subobjects
  have harr : (Over.map q).map ((S.opensToSlice T).1.map ((Opens.map πtop).map g)) ≫
      opensOverHom S (Over.mk q) ((Opens.map πtop).obj ⊤) =
      opensOverHom S (Over.mk q) ((Opens.map πtop).obj V) :=
    Over.OverMorphism.ext
      (by simp)
  rw [show opensOverHom S (Over.mk q) ((Opens.map πtop).obj V) = _ from harr.symm,
    op_comp, Dp.map_comp, ConcreteCategory.comp_apply]
  exact hPb

end LocalVanishing

section Clause

variable {X Y : S.category} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})] in
/-- **The local vanishing hypothesis of the derived clause of [Stacks, Tag 0DCU], verified.** For
`f : X ⟶ Y` proper, `J` an injective abelian sheaf on the small Zariski site of `X`, `p > 0` and
`W` an object of `LC_Zar/Y`, every class in `H^p_{LC_Zar/X}(W ×_Y X, π_X^{-1} J)` is killed by the
members of a Zariski covering sieve of `W`.

The base change `W ×_Y X ⟶ W.left` is proper by `isProperMap_pullback_fst`, and the restriction of
`h^{-1} J` to each of its fibres is soft by
`isSoft_restrictionFunctorUnivLE_fiber_snd_of_isFlasque`, `J` being flasque because it is
injective; so `exists_opens_map_eq_zero_of_isSoft_fiber` produces, around every point of `W.left`,
an open subset whose preimage kills the class as an open subobject of `W ×_Y X`. Pulling back the
open immersion of that open subset along `f` gives a morphism into `W ×_Y X` landing in the
preimage, which therefore also kills the class
(`map_eq_zero_of_opensOverHom_map_eq_zero`); and the resulting pointwise family is a Zariski
covering sieve by `equalizerSieve_mem_zariskiTopology_over_of_forall_exists_opens`. -/
theorem equalizerSieve_mem_over_of_isProperMap
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
    (hJ : Injective J) (p : ℕ) (hp : 0 < p) (W : Over Y)
    (ξ : ToType ((((Over.pullback f).op ⋙
        ((sheafToPresheaf (S.zariskiTopology.over X)
            AddCommGrpCat.{max (u + 1) v}).rightDerived p).obj
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J))).obj (op W))) :
    Presheaf.equalizerSieve (X := op W) ξ 0 ∈ (S.zariskiTopology.over Y) W := by
  let JT : ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X).Sheaf
      AddCommGrpCat.{max (u + 1) v} := J
  let _hinj : Injective JT := hJ
  let _hfl : TopCat.Sheaf.IsFlasque JT :=
    Stacks.Cohomology.CechOne.isFlasque_of_injective JT
  have _ht2X : T2Space
      ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj X) := by
    change T2Space X.obj
    infer_instance
  have _ht2T : T2Space ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).obj
      (Limits.pullback W.hom f)) := by
    change T2Space (Limits.pullback W.hom f).obj
    infer_instance
  have hproperX : _root_.IsProperMap
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f).hom :
        X.obj → Y.obj) :=
    isProperMap_site S f hf
  have hproper : _root_.IsProperMap
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map
        (Limits.pullback.fst W.hom f)).hom :
          (Limits.pullback W.hom f).obj → W.left.obj) :=
    isProperMap_pullback_fst S f W.hom hproperX
  refine equalizerSieve_mem_zariskiTopology_over_of_forall_exists_opens S
    (P := (Over.pullback f).op ⋙ zariskiInverseImageCohomologyPresheaf.{u, w, v} S p J)
    ξ 0 fun z => ?_
  obtain ⟨V, hzV, hzero⟩ :=
    exists_opens_map_eq_zero_of_isSoft_fiber S (Limits.pullback.snd W.hom f)
      (Limits.pullback.fst W.hom f) p J hproper.isClosedMap
      (fun _ => hproper.isCompact_preimage isCompact_singleton)
      (T2Space.isSeparatedMap _)
      (isSoft_restrictionFunctorUnivLE_fiber_snd_of_isFlasque.{max (u + 1) v} S f W.hom JT
        (fun _ => hproperX.isCompact_preimage isCompact_singleton) (T2Space.isSeparatedMap _))
      hp ξ z
  refine ⟨V, hzV, ?_⟩
  rw [map_zero]
  refine map_eq_zero_of_opensOverHom_map_eq_zero S
    (zariskiInverseImageCohomologyPresheaf.{u, w, v} S p J) ξ
    ((Over.pullback f).map (opensOverHom S W V))
    ((Opens.map ((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map
      (Limits.pullback.fst W.hom f))).obj V) (fun e => ?_) hzero
  have hfst := ConcreteCategory.congr_hom
    (over_pullback_map_left_fst S f (opensOverHom S W V)) e
  simp only [site_hom_comp_apply] at hfst
  change (Limits.pullback.fst W.hom f : (Limits.pullback W.hom f).obj → W.left.obj)
    ((((Over.pullback f).map (opensOverHom S W V)).left : _ → _) e) ∈ V
  rw [hfst]
  exact opensToSlice_hom_mem S V _

/-- **[Stacks, Tag 0DCU], the derived clause: the derived Zariski base-change map of a proper
morphism is an isomorphism.** For `f : X ⟶ Y` a proper morphism of the locally quasi-compact
Zariski site, the comparison
`π_Y^{-1} ∘ Rf_* ⟶ Rf_{Zar,*} ∘ π_X^{-1}` of `properDerivedImageComparison` is invertible.

This is `isIso_properDerivedImageComparison_of_locallyZero_cohomologyPresheaf` fed
`equalizerSieve_mem_over_of_isProperMap`. -/
@[stacks 0DCU "proper_derived_image"]
theorem properDerivedImageComparison_isIso
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj)) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) :=
  isIso_properDerivedImageComparison_of_locallyZero_cohomologyPresheaf.{u, w, v} S f hf
    fun J hJ p hp W ξ => equalizerSieve_mem_over_of_isProperMap S f hf J hJ p hp W ξ

omit [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})] in
/-- **[Stacks, Tag 0DCU], the derived clause, with properness as the only hypothesis.** For
`f : X ⟶ Y` a proper morphism of the locally quasi-compact Zariski site, the comparison
`π_Y^{-1} ∘ Rf_* ⟶ Rf_{Zar,*} ∘ π_X^{-1}` of `properDerivedImageComparison` is invertible.

The four sheafifications and the three enough-injectives inputs the derived functors are built
from are not assumed: all four sites are essentially small at this coefficient universe, so
`hasSheafify_opensSite`, `hasSheafify_zariskiSlice`, `enoughInjectives_spaceSheaf` and
`enoughInjectives_zariskiSliceSheaf` supply them. -/
@[stacks 0DCU "proper_derived_image, with the four sheafifications and the three \
enough-injectives inputs discharged rather than assumed"]
theorem properDerivedImageComparison_isIso_unconditional
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj)) :
    letI := hasSheafify_opensSite.{u, w, v} S X
    letI := hasSheafify_opensSite.{u, w, v} S Y
    letI := hasSheafify_zariskiSlice.{u, w, v} S X
    letI := hasSheafify_zariskiSlice.{u, w, v} S Y
    letI := enoughInjectives_spaceSheaf.{u, w, v} S X
    letI := enoughInjectives_spaceSheaf.{u, w, v} S Y
    letI := enoughInjectives_zariskiSliceSheaf.{u, w, v} S X
    IsIso (properDerivedImageComparison.{u, w, v} S f) :=
  let := hasSheafify_opensSite.{u, w, v} S X
  let := hasSheafify_opensSite.{u, w, v} S Y
  let := hasSheafify_zariskiSlice.{u, w, v} S X
  let := hasSheafify_zariskiSlice.{u, w, v} S Y
  let := enoughInjectives_spaceSheaf.{u, w, v} S X
  let := enoughInjectives_spaceSheaf.{u, w, v} S Y
  let := enoughInjectives_zariskiSliceSheaf.{u, w, v} S X
  properDerivedImageComparison_isIso.{u, w, v} S f hf

end Clause

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
