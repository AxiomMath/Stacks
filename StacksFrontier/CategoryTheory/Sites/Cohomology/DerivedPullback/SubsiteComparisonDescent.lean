module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FullyFaithfulSubsiteSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonCartesianCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Modules.CartesianLocalOnCover

/-!
# Descent of the cartesian comparison maps through a small subsite

Let `ε : (C_τ, O) ⟶ (C_τ', O)` be the comparison of a ringed site with its chaotic topology, so
that `Rε_*K` is the presheaf `U ↦ RΓ(U, K)`, and call `Rε_*K` cartesian along an arrow `U ⟶ V`
when the comparison map `RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is an isomorphism (Stacks 0GYV).
This file proves that this condition descends along a finite flat cover, in the generality in
which it is used for Stacks 0H0K, where the cover lives on the small étale site of an affine
scheme sitting inside a big site.

* On a ringed site `Sm` with fibre products, a terminal object `t` and a finite family
  `p i : t i ⟶ t` generating a covering sieve, whose restriction homomorphisms are flat and carry
  fibre products to pushouts, on whose slices `Sm/t i` cartesian presheaves of modules are
  sheaves and on which cartesian sheaves of modules are acyclic: if `Rε_*K` is cartesian along
  the arrows lying over the `t i`, it is cartesian along every arrow
  (`isCartesianPushforward_of_isIso_comparison_of_cover`). Over `t i`, Stacks 0D6G for `ε` and
  Stacks 0GZS on the slice make the cohomology sheaves of `K` cartesian over `t i`
  (`isUniversalArrow_homology_of_isIso_comparison`); being cartesian is local on a finite flat
  cover (`isCartesianPresheaf_of_cover`, from Stacks 03DX's descent step); and Stacks 0GZR with
  the acyclicity turns cartesian cohomology sheaves back into a cartesian `Rε_*K`.
* For a morphism of ringed sites `g : X ⟶ Sm` whose functor `u : Sm ⥤ X` is cocontinuous and
  whose structure map is invertible, `Rε_*(g_* L)` is cartesian along `b` exactly when `Rε_* L`
  is cartesian along `u(b)` (`isIso_comparison_pushforward_iff`), the derived sections of
  `g_* L` over `V` being those of `L` over `u V`.

Together: `isIso_comparison_map_of_cover`, if `Rε_*L` is cartesian along the images under `u` of
the arrows of `Sm` over the `t i`, it is cartesian along the image of every arrow of `Sm`.

## Main results

* `Stacks.Cohomology.SubsiteComparisonDescent.isUniversalArrow_homology_of_isIso_comparison`
* `Stacks.Cohomology.SubsiteComparisonDescent.isCartesianPresheaf_of_cover`
* `Stacks.Cohomology.SubsiteComparisonDescent.isCartesianPushforward_of_isIso_comparison_of_cover`
* `Stacks.Cohomology.SubsiteComparisonDescent.isIso_comparison_pushforward_iff`
* `Stacks.Cohomology.SubsiteComparisonDescent.isIso_comparison_map_of_cover`

## References

* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
* [Stacks Project, Tag 0GZR](https://stacks.math.columbia.edu/tag/0GZR)
* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0D6G](https://stacks.math.columbia.edu/tag/0D6G)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H0K](https://stacks.math.columbia.edu/tag/0H0K)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent (dInverseImage
  comparison_dInverseImage)
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars
open Stacks.Cohomology.FullyFaithfulSubsite
open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.TerminalBaseChange (CommSections)
open Stacks.PresheafOfModules (restrictionBaseChange isIso_restrictionBaseChange_of_cover)

namespace Stacks.Cohomology.SubsiteComparisonDescent

universe w m u v r

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-! ### Cohomology sheaves over a slice -/

section Slice

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  [HasSheafify J AddCommGrpCat.{max u v r w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}] [CommSections R.obj]
  (U : C) [HasSheafify (J.over U) AddCommGrpCat.{max u v r w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- **Cartesian comparison maps over a slice give cartesian cohomology sheaves over it.** Suppose
the restriction homomorphisms of `O` are flat and every cartesian presheaf of modules on `C/U`
is a sheaf. If the comparison maps of `Rε_*K` along all arrows of `C` lying over `U` are
isomorphisms, then the cohomology sheaves of `K` are cartesian along those arrows.

The comparison maps of `Rε_*K` along the arrows over `U` are the comparison maps of its
restriction to `C/U`, which is `Rε_{U*}(K|_U)` (Stacks 0D6G for `ε`); so `K|_U` lies in the
subcategory of Stacks 0GZS on `C/U`, its cohomology sheaves are cartesian there
(`isCartesianPresheaf_homology_of_isCartesianPushforward`), and they are the restrictions of
those of `K`. -/
theorem isUniversalArrow_homology_of_isIso_comparison
    (hflat : ∀ ⦃V W : Cᵒᵖ⦄ (a : W ⟶ V), RingHom.Flat (R.obj.map a).hom)
    (bc : BaseChangeData.{w} R.obj)
    (hsheaf : ∀ P : PresheafOfModules.{max u v r w} (overRingPresheaf R.obj U),
      IsCartesianPresheaf P → Presheaf.IsSheaf (J.over U) P.presheaf)
    (K : DerivedCategory (SheafOfModules.{max u v r w} R))
    (hK : ∀ ⦃A B : C⦄ (b : A ⟶ B) (_ : B ⟶ U),
      IsIso (comparison.{w} bc b.op ((derivedEpsilonPushforward.{w} R).obj K)))
    (n : ℤ) ⦃A B : C⦄ (b : A ⟶ B) (s : B ⟶ U) :
    (ModuleCat.restrictScalars.{max u v r w} (R.obj.map b.op).hom).IsUniversalArrow
      (((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) n).obj K).val.map
        b.op) := by
  have hO : ∀ (V : Cᵒᵖ) (x y : R.obj.obj V), x * y = y * x := CommSections.mul_comm
  let : CommSections (overRingSheaf R U).obj :=
    Stacks.ModulesOnACategory.TerminalMorphismOfSites.commSections_of_comm
      (overRingPresheaf R.obj U) (comm_overRingPresheaf R.obj U hO)
  let bcU := baseChangeDataOfComm.{r, v, max u v, w} (overRingPresheaf R.obj U)
    (comm_overRingPresheaf R.obj U hO)
  have hQC : IsQC.{w} bcU
      ((derivedRestriction.{w} R.obj U).obj ((derivedEpsilonPushforward.{w} R).obj K)) := by
    intro A' B' f
    rw [← comparison_derivedRestriction.{w} R.obj U bc bcU _ f]
    have : IsIso (comparison.{w} bc ((Over.forget U).op.map f)
        ((derivedEpsilonPushforward.{w} R).obj K)) := hK f.unop.left B'.unop.hom
    infer_instance
  have hICP : IsCartesianPushforward.{w} (overRingSheaf R U) bcU
      ((sheafRestriction.{w} R U).mapDerivedCategory.obj K) :=
    ObjectProperty.prop_of_iso (P := IsQC.{w} bcU)
      ((derivedRestrictionPushforwardIso.{w} R U).app K) hQC
  have hcart := isCartesianPresheaf_homology_of_isCartesianPushforward.{w} (overRingSheaf R U)
    (fun _ _ a => hflat ((Over.forget U).op.map a)) bcU hsheaf _ hICP n
  have hcart' : IsCartesianPresheaf ((sheafRestriction.{w} R U).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w} R) n).obj K)).val :=
    hcart.of_iso ((SheafOfModules.forget _).mapIso
      (((sheafRestriction.{w} R U).mapDerivedCategoryHomologyIso n).app K))
  exact hcart' (Over.homMk (U := Over.mk (b ≫ s)) (V := Over.mk s) b rfl).op

end Slice

/-! ### Cartesian presheaves glued along a finite flat cover of a terminal object -/

section Cover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- The pullback along `g : Y ⟶ X` of a covering family `gw i : W i ⟶ X` is a covering family
of `Y`. -/
private theorem ofArrows_pullback_fst_mem [HasPullbacks C] {X Y : C} (g : Y ⟶ X) {I : Type*}
    {W : I → C} (gw : ∀ i, W i ⟶ X) (hW : Sieve.ofArrows W gw ∈ J X) :
    Sieve.ofArrows (fun i => pullback g (gw i)) (fun i => pullback.fst g (gw i)) ∈ J Y := by
  refine GrothendieckTopology.superset_covering _ ?_ (J.pullback_stable g hW)
  rintro Z h ⟨Y'', g₁, g₂, ⟨i⟩, hgg⟩
  have hmem := (Sieve.ofArrows (fun i => pullback g (gw i))
      (fun i => pullback.fst g (gw i))).downward_closed
    (Sieve.ofArrows_mk (fun i => pullback g (gw i)) (fun i => pullback.fst g (gw i)) i)
    (pullback.lift h g₁ hgg.symm)
  rwa [pullback.lift_fst] at hmem

/-- **A sheaf of modules cartesian over the members of a finite flat cover is cartesian.** Let
`t` be a terminal object, `p i : t i ⟶ t` a finite family generating a covering sieve, and assume
that the restriction homomorphisms of `R` are flat and carry fibre products to pushouts. A sheaf
of modules `M` which is cartesian along every arrow whose target lies over some `t i` is
cartesian along every arrow.

An arrow `U ⟶ V` is handled by `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_cover`
at the covering `V ×_t t i ⟶ V`, whose members, and the members of whose double overlaps, lie
over the `t i`. -/
theorem isCartesianPresheaf_of_cover [HasPullbacks C]
    (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))
    (hM : Presieve.IsSheaf J (M.presheaf ⋙ forget AddCommGrpCat)) {t : C} (ht : IsTerminal t)
    {I : Type*} [Finite I] (ts : I → C) (p : ∀ i, ts i ⟶ t) (hcov : Sieve.ofArrows ts p ∈ J t)
    (hflat : ∀ ⦃U V : C⦄ (f : U ⟶ V), (R.map f.op).hom.Flat)
    (hpo : ∀ ⦃A B D : C⦄ (f : A ⟶ D) (h : B ⟶ D), IsPushout (R.map f.op) (R.map h.op)
      (R.map (pullback.fst f h).op) (R.map (pullback.snd f h).op))
    (hloc : ∀ (i : I) ⦃A B : C⦄ (b : A ⟶ B) (_ : B ⟶ ts i),
      IsIso (restrictionBaseChange M b.op)) :
    IsCartesianPresheaf M := by
  rw [isCartesianPresheaf_iff_isIso_restrictionBaseChange]
  intro X' Y' f
  let g : Y'.unop ⟶ X'.unop := f.unop
  let W : I → C := fun i => pullback (p i) (ht.from X'.unop)
  let gw : ∀ i, W i ⟶ X'.unop := fun i => pullback.snd (p i) (ht.from X'.unop)
  have hcoverV : Sieve.ofArrows W gw ∈ J X'.unop := by
    change Sieve.generate (Presieve.ofArrows W gw) ∈ J X'.unop
    rw [Presieve.ofArrows_pullback, Sieve.pullbackArrows_comm]
    exact J.pullback_stable _ hcov
  have hsfV : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows W gw) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hM _ hcoverV)
  have hsfU : Presieve.IsSheafFor (M.presheaf ⋙ forget AddCommGrpCat)
      (Presieve.ofArrows (fun i => pullback g (gw i)) (fun i => pullback.fst g (gw i))) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hM _ (ofArrows_pullback_fst_mem g gw hcoverV))
  exact isIso_restrictionBaseChange_of_cover M g W gw (hflat g) hsfV hsfU
    (fun i => hpo g (gw i)) (fun c => hpo g _)
    (fun i => hloc i (pullback.snd g (gw i)) (pullback.fst (p i) (ht.from X'.unop)))
    (fun c => hloc c.1 (pullback.snd g (pullback.fst (gw c.1) (gw c.2) ≫ gw c.1))
      (pullback.fst (gw c.1) (gw c.2) ≫ pullback.fst (p c.1) (ht.from X'.unop)))

end Cover

/-! ### Descent of the cartesian comparison maps along a finite flat cover -/

section Descent

/-- Sections of the ring sheaf of a ringed site, as a presheaf of rings, commute. -/
private theorem ringSheaf_obj_mul_comm {S : RingedSite.{u, v, r}} (V : S.Cᵒᵖ)
    (x y : (Stacks.SheafOfModules.Tensor.ringSheaf S.O).obj.obj V) : x * y = y * x :=
  mul_comm (show S.O.obj.obj V from x) (show S.O.obj.obj V from y)

variable (Sm : RingedSite.{u, v, r})
  [HasSheafify Sm.J AddCommGrpCat.{max u v r w}]
  [Sm.J.WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]
  [∀ U : Sm.C, HasSheafify (Sm.J.over U) AddCommGrpCat.{max u v r w}]
  [∀ U : Sm.C, (Sm.J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r w}]

/-- **The condition of Stacks 0GZS descends along a finite flat cover of a terminal object.**
Let `(C, O)` be a ringed site with fibre products and a terminal object `t`, whose restriction
homomorphisms are flat and carry fibre products to pushouts, and let `p i : t i ⟶ t` be a finite
family generating a covering sieve. Assume that every cartesian presheaf of modules on each
slice `C/t i` is a sheaf, and that every sheaf of modules with cartesian underlying presheaf has
vanishing higher cohomology over every object of `C`. If the comparison maps of `Rε_*K` are
isomorphisms along every arrow of `C` whose target lies over some `t i`, then `Rε_*K` has
cartesian derived sections: its comparison maps are isomorphisms along every arrow.

The cohomology sheaves of `K` are cartesian along the arrows over the `t i`
(`isUniversalArrow_homology_of_isIso_comparison`), hence along every arrow
(`isCartesianPresheaf_of_cover`), and Stacks 0GZR together with the acyclicity concludes
(`isCartesianPushforward_of_isCartesianPresheaf_homology`). -/
theorem isCartesianPushforward_of_isIso_comparison_of_cover [HasPullbacks Sm.C]
    (bc : BaseChangeData.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O).obj) {t : Sm.C}
    (ht : IsTerminal t) {I : Type*}
    [Finite I] (ts : I → Sm.C) (p : ∀ i, ts i ⟶ t) (hcov : Sieve.ofArrows ts p ∈ Sm.J t)
    (hflat : ∀ ⦃U V : Sm.C⦄ (f : U ⟶ V), (Sm.O.obj.map f.op).hom.Flat)
    (hpo : ∀ ⦃A B D : Sm.C⦄ (f : A ⟶ D) (h : B ⟶ D), IsPushout (Sm.O.obj.map f.op)
      (Sm.O.obj.map h.op) (Sm.O.obj.map (pullback.fst f h).op)
      (Sm.O.obj.map (pullback.snd f h).op))
    (hsheaf : ∀ (i : I) (P : PresheafOfModules.{max u v r w}
        (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O).obj (ts i))),
      IsCartesianPresheaf P → Presheaf.IsSheaf (Sm.J.over (ts i)) P.presheaf)
    (hacyc : ∀ F : SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O),
      IsCartesianPresheaf F.val → ∀ (U : Sm.C) (q : ℕ), 0 < q →
        IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O)
          (op U)).rightDerived q).obj F))
    (K : DerivedCategory
      (SheafOfModules.{max u v r w} (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O)))
    (hK : ∀ (i : I) ⦃A B : Sm.C⦄ (b : A ⟶ B) (_ : B ⟶ ts i),
      IsIso (comparison.{w} bc b.op
        ((derivedEpsilonPushforward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O)).obj K))) :
    IsCartesianPushforward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O) bc K := by
  let : CommSections (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O).obj :=
    ⟨ringSheaf_obj_mul_comm⟩
  have hflat' : ∀ ⦃V W : Sm.Cᵒᵖ⦄ (a : W ⟶ V),
      RingHom.Flat ((Stacks.SheafOfModules.Tensor.ringSheaf Sm.O).obj.map a).hom :=
    fun _ _ a => hflat a.unop
  have hcart : ∀ n : ℤ, IsCartesianPresheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w}
        (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O)) n).obj K).val := by
    intro n
    let F := (DerivedCategory.homologyFunctor (SheafOfModules.{max u v r w}
      (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O)) n).obj K
    have hM : Presieve.IsSheaf Sm.J (F.val.presheaf ⋙ forget AddCommGrpCat) := by
      rw [← isSheaf_iff_isSheaf_of_type]
      exact (Presheaf.isSheaf_iff_isSheaf_comp Sm.J F.val.presheaf (forget AddCommGrpCat)).mp
        F.isSheaf
    exact isCartesianPresheaf_of_cover.{max u v w} (R := Sm.O.obj) F.val hM ht ts p hcov hflat hpo
      fun i A B b s =>
        (Functor.isUniversalArrow_iff_isIso (ModuleCat.extendRestrictScalarsAdj _) _).1
        (isUniversalArrow_homology_of_isIso_comparison.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O) (ts i) hflat' bc (hsheaf i) K (hK i) n b s)
  exact fun _ _ a => isCartesianPushforward_of_isCartesianPresheaf_homology.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O) hflat' bc hacyc K hcart a

end Descent

/-! ### Comparison maps of a direct image along a cocontinuous morphism -/

section DirectImage

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [f.u.IsCocontinuous Y.J X.J] [IsIso f.fsharp]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [f.u.IsCocontinuous Y.J X.J] in
/-- The structure map `f^♯ : O_Y ⟶ u⁻¹ O_X` read on presheaves of rings is invertible when the
structure map of `f` is. -/
theorem isIso_fSharpPresheaf :
    IsIso (f.toRingedToposSiteHom.fSharpPresheaf :
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ⟶
        f.u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) := by
  unfold RingedToposSiteHom.fSharpPresheaf
  have : IsIso f.toRingedToposSiteHom.fSharp := ‹IsIso f.fsharp›
  have : IsIso f.toRingedToposSiteHom.fSharp.hom :=
    (inferInstance : IsIso ((sheafToPresheaf _ _).map f.toRingedToposSiteHom.fSharp))
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W =>
    (forget₂ CommRingCat RingCat).map_isIso (f.toRingedToposSiteHom.fSharp.hom.app W)

/-- **The comparison maps of a direct image along a cocontinuous morphism of ringed sites with
invertible structure map.** For `a : V ⟶ U` in `Yᵒᵖ`, the comparison map of `Rε_*(f_* L)` along
`a` is an isomorphism exactly when the comparison map of `Rε_* L` along `u(a)` is: the derived
sections of `f_* L` over `V` are those of `L` over `u V`, compatibly with restriction
(`Stacks.Cohomology.FullyFaithfulSubsite.derivedEpsilonPushforwardInverseImageIso`), up to a
restriction of scalars along the invertible `f^♯`. -/
theorem isIso_comparison_pushforward_iff
    (bcX : BaseChangeData.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    (bcY : BaseChangeData.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {U V : Y.Cᵒᵖ} (a : V ⟶ U) :
    IsIso (comparison.{u} bcY a
      ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        (f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.obj L))) ↔
      IsIso (comparison.{u} bcX (f.u.op.map a)
        ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L)) := by
  let bc' : BaseChangeData.{u} (f.u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
    baseChangeDataOfComm.{u, u, u, u} (f.u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      fun W => ringSheaf_obj_mul_comm (S := X) (f.u.op.obj W)
  refine (isIso_comparison_iff_of_iso bcY a
    ((derivedEpsilonPushforwardInverseImageIso f).app L)).trans ?_
  refine (@isIso_comparison_restrictScalars_iff _ _ (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj
    (f.u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
    f.toRingedToposSiteHom.fSharpPresheaf (isIso_fSharpPresheaf f) bcY bc' _ _ a _).trans ?_
  rw [← comparison_dInverseImage f.u (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj bcX bc' _ a]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

end DirectImage

/-! ### Descent of the comparison maps through a small subsite -/

section Subsite

variable {X Sm : RingedSite.{u, u, u}} (g : RingedSite.Hom X Sm)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Sm.J AddCommGrpCat.{u}] [Sm.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Sm.C, HasSheafify (Sm.J.over U) AddCommGrpCat.{u}]
  [∀ U : Sm.C, (Sm.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [g.u.IsCocontinuous Sm.J X.J] [IsIso g.fsharp]

/-- **Descent of the cartesian comparison maps through a small subsite.** Let
`g : (X, O_X) ⟶ (Sm, O_Sm)` be a morphism of ringed sites whose functor `u : Sm ⥤ X` is
cocontinuous and whose structure map is invertible (for instance the inclusion of the small
étale site of an affine scheme into a big one). Assume that `Sm` has fibre products and a
terminal object `t`, that its restriction homomorphisms are flat and carry fibre products to
pushouts, that `p i : t i ⟶ t` is a finite family generating a covering sieve, that cartesian
presheaves of modules on each slice `Sm/t i` are sheaves, and that sheaves of modules on `Sm`
with cartesian underlying presheaf have vanishing higher cohomology over every object.

Let `L ∈ D(O_X)` be such that the comparison map of `Rε_*L` along `u(b)` is an isomorphism for
every arrow `b` of `Sm` whose target lies over some `t i`. Then the comparison map of `Rε_*L`
along `u(b)` is an isomorphism for every arrow `b` of `Sm`; in particular along the `u(p i)`.

The comparison maps of `Rε_*L` along `u(b)` are those of `Rε_*(g_* L)` along `b`
(`isIso_comparison_pushforward_iff`), and the condition of Stacks 0GZS descends along the
cover on `Sm` (`isCartesianPushforward_of_isIso_comparison_of_cover`). -/
theorem isIso_comparison_map_of_cover [HasPullbacks Sm.C]
    (bc : BaseChangeData.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) {t : Sm.C}
    (ht : IsTerminal t) {I : Type*}
    [Finite I] (ts : I → Sm.C) (p : ∀ i, ts i ⟶ t) (hcov : Sieve.ofArrows ts p ∈ Sm.J t)
    (hflat : ∀ ⦃U V : Sm.C⦄ (f : U ⟶ V), (Sm.O.obj.map f.op).hom.Flat)
    (hpo : ∀ ⦃A B D : Sm.C⦄ (f : A ⟶ D) (h : B ⟶ D), IsPushout (Sm.O.obj.map f.op)
      (Sm.O.obj.map h.op) (Sm.O.obj.map (pullback.fst f h).op)
      (Sm.O.obj.map (pullback.snd f h).op))
    (hsheaf : ∀ (i : I)
        (P : PresheafOfModules.{u}
          (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O).obj (ts i))),
      IsCartesianPresheaf P → Presheaf.IsSheaf (Sm.J.over (ts i)) P.presheaf)
    (hacyc : ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O),
      IsCartesianPresheaf F.val → ∀ (U : Sm.C) (q : ℕ), 0 < q →
        IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O)
          (op U)).rightDerived q).obj F))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : ∀ (i : I) ⦃A B : Sm.C⦄ (b : A ⟶ B) (_ : B ⟶ ts i),
      IsIso (comparison.{u} bc (g.u.map b).op
        ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L)))
    ⦃A B : Sm.C⦄ (b : A ⟶ B) :
    IsIso (comparison.{u} bc (g.u.map b).op
      ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L)) := by
  let bcSm := baseChangeDataOfComm.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O).obj
    ringSheaf_obj_mul_comm
  have hK : IsCartesianPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Sm.O) bcSm
      (g.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.obj L) :=
    isCartesianPushforward_of_isIso_comparison_of_cover.{u, u, u, u} Sm bcSm ht ts p hcov hflat
    hpo hsheaf hacyc (g.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.obj L)
    (fun i A B b s => (isIso_comparison_pushforward_iff g bc bcSm L b.op).2 (hL i b s))
  exact (isIso_comparison_pushforward_iff g bc bcSm L b.op).1 (hK b.op)

end Subsite

end Stacks.Cohomology.SubsiteComparisonDescent

end
