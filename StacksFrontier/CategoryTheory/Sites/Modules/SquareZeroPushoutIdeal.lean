module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushout

/-!
# The ideal of the square-zero pushout, as a restriction datum

Let `(C, K)` be a site, let `π : R ⟶ B` be a locally surjective morphism of sheaves of
commutative rings on it, write `ℐ' = Ker π`, let `𝒢` be a sheaf of `R`-modules annihilated by
`ℐ'` and let `ψ : ℐ' ⟶ 𝒢` be a morphism of `R`-modules.
`StacksFrontier/CategoryTheory/Sites/Modules/SquareZeroPushout.lean` builds the square-zero pushout

`0 ⟶ 𝒢 ⟶ (R ⋉ 𝒢)/J ⟶ ℬ ⟶ 0`,  `J = {(g, -ψ g) : g ∈ ℐ'}`,

with its exactness. This file adds what is needed to read that extension as a square-zero
extension of `f⁻¹𝒪_S`-algebras in the sense of
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension`, whose identification of
the square-zero ideal with `𝒢` is a `Stacks.Sites.Conormal.IdealRestriction`: a *natural
`R`-linear family of maps out of the kernel ideal*, not merely an additive one.

Two things are therefore proved. First the comparison with `R`: the inclusion
`R ⟶ (R ⋉ 𝒢)/J`, `r ↦ [(r, 0)]`, lies over `ℬ` and carries a local section of `ℐ'` to the image
of its value under `ψ` — the relation `J` imposes. Second the identification of the ideal: the
inclusion `pushoutInr` of `𝒢` is injective with image exactly the kernel of the projection, so
it has a sectionwise inverse, and that inverse is a restriction datum.

The linearity of the inverse is the one non-formal point. It needs

`s · [(0, n)] = [(0, π(s) n)]`  for an *arbitrary* local section `s` of the pushout,

while `Stacks.Sites.SqZeroPushout.pushoutMk_mul_pushoutInr` gives it only for `s` in the image
of the quotient map `pushoutMk`. The quotient map is locally surjective — the objectwise
quotient map is surjective on sections and the unit of sheafification is locally surjective —
so the statement is local, and the pushout is a sheaf; `mul_pushoutInr_of_local_smul` does that
gluing.

## Main definitions

* `Stacks.Sites.SqZeroPushout.pushoutInl`: the inclusion `R ⟶ (R ⋉ 𝒢)/J`, `r ↦ [(r, 0)]`.
* `Stacks.Sites.SqZeroPushout.restrictAlong`: a sheaf of `ℬ`-modules read as a sheaf of
  `R`-modules through `π`, which is the shape the pushout consumes its ideal in.
* `Stacks.Sites.SqZeroPushout.idealSectionOf`: the local section of `𝒢` that a local section of
  the pushout killed by the projection comes from.
* `Stacks.Sites.SqZeroPushout.idealRestriction`: **the ideal of the pushout, as a restriction
  datum for its projection.**

## Main results

* `Stacks.Sites.SqZeroPushout.pushoutInl_comp_pushoutProj`: the inclusion of `R` lies over `ℬ`.
* `Stacks.Sites.SqZeroPushout.pushoutInl_app_kernel`: **the inclusion of `R` carries the kernel
  ideal `ℐ'` into `𝒢` by `ψ`**, which is the relation the graph ideal imposes and the reason the
  class of the resulting extension is the class of `ψ`.
* `Stacks.Sites.SqZeroPushout.isLocallySurjective_pushoutMk`: the quotient map onto the pushout
  is locally surjective.
* `Stacks.Sites.SqZeroPushout.mul_pushoutInr_of_local_smul` and
  `...mul_pushoutInr_restrictAlong`: **the ideal `𝒢` of the pushout is acted on through `ℬ`**,
  for an arbitrary local section of the pushout.
* `Stacks.Sites.SqZeroPushout.idealRestriction_app_pushoutInr`: the restriction datum inverts
  the inclusion of the ideal.

## Implementation notes

`mul_pushoutInr_of_local_smul` is stated with the action on the right-hand side supplied *locally*,
as a hypothesis quantified over the arrows of the site, rather than through a `ℬ`-module structure
on `𝒢`: `𝒢` is only an `R`-module in `Stacks.Sites.SqZeroPushout.PushoutData`, and a local section
of the pushout has no global lift to `R`. `mul_pushoutInr_restrictAlong` discharges that hypothesis
for `𝒢 = restrictAlong π G` with `G` a `ℬ`-module, which is the case the extension needs.

Scalars appear in two definitionally equal spellings, `↥(B.obj.obj X)` for the sections of a
sheaf of commutative rings and `↥((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj X)` for its
sections read as a sheaf of rings, and the module structure of `𝒢` is registered only for the
second; the statements below use `Stacks.Sites.Conormal.presentationScalar`, which carries that
spelling. `𝒢` is therefore declared over `Stacks.SheafOfModules.Tensor.ringSheaf B` rather than
over the `Stacks.Sheaves.Differentials.underlyingRingSheaf B` that the `Quotient` section's `𝒩`
uses: the two are definitionally equal, but neither unfolds to the other at the `.instances`
transparency at which instance search runs, so the `•` of `presentationScalar` is found only at
the spelling `Stacks.Sites.Conormal` itself uses.
For the same reason the restriction maps appear both as `G.val.map f` and as
`(modules (restrictAlong π G)).map f`, the latter wrapped in a `ModuleCat.restrictScalars`; the
proofs below ascribe types and compose with `Eq.trans` where a `rw` would have to match one of
the two spellings syntactically.

`Stacks.Deformation.InverseImageExtension.Data.pushoutMap` and its lemmas
`...pushoutMap_comp_pushoutProj`, `...pushoutMk_app_graphSection` and `...pushoutMap_app_kernel`
of `StacksFrontier/Deformation/RingedSpaceThickening/InverseImageExtensionComparison.lean` are the
same four statements as the first group here, specialized to that file's `Data`. They cannot be
reused: a `Data` carries a *second* square-zero extension together with an identification of its
ideal and a compatibility between the two actions, none of which is available when building
one extension out of `ψ`. The statements here depend on `π`, `𝒢` and `ψ` alone.

## References

* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
* [Stacks Project, Tag 0GPW](https://stacks.math.columbia.edu/tag/0GPW)
-/

@[expose] public section

open CategoryTheory PresheafOfModules Opposite
open Stacks.Sheaves.Differentials (sqZeroExtSheaf sqZeroExtSheafProj sqZeroExtSheafInl)
open Stacks.Sites.Conormal (kernelIdeal)

universe u

namespace Stacks.Sites.SqZeroPushout

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R B : Sheaf K CommRingCat.{u}} (π : R ⟶ B)
  (N : SheafOfModules.{u} (Stacks.Sheaves.Differentials.underlyingRingSheaf R))
  (ψ : PushoutData π N)

section Quotient

variable [HasWeakSheafify K CommRingCat.{u}]

/-- The inclusion `R ⟶ (R ⋉ 𝒢)/J` of the presented sheaf of rings into the pushout,
`r ↦ [(r, 0)]`. -/
noncomputable def pushoutInl : R ⟶ pushoutSheaf π N ψ :=
  sqZeroExtSheafInl R N ≫ pushoutMk π N ψ

/-- The inclusion of `R` into the pushout lies over `ℬ`. -/
theorem pushoutInl_comp_pushoutProj :
    pushoutInl π N ψ ≫ pushoutProj π N ψ = π := by
  have h : sqZeroExtSheafInl R N ≫ sqZeroExtSheafProj R N = 𝟙 R := by
    apply Sheaf.hom_ext
    refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun r => ?_))
    rfl
  change (sqZeroExtSheafInl R N ≫ pushoutMk π N ψ) ≫ pushoutProj π N ψ = π
  rw [Category.assoc, pushoutMk_comp_pushoutProj, ← Category.assoc, h, Category.id_comp]

/-- The inclusion of `R` into the pushout, on sections. -/
theorem pushoutInl_app (X : Cᵒᵖ) (r : ↥(R.obj.obj X)) :
    (pushoutInl π N ψ).hom.app X r =
      (pushoutMk π N ψ).hom.app X (sqZeroExtMk (M := modules N) r
        (0 : ↥((modules N).obj X))) :=
  rfl

/-- An antidiagonal section of the trivial square-zero extension dies in the pushout. -/
theorem pushoutMk_app_graphSection (X : Cᵒᵖ) (g : ↥(kernelIdeal π.hom X)) :
    (pushoutMk π N ψ).hom.app X (graphSection π N ψ X g) = 0 := by
  change ((toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ))).app X).hom
    (Ideal.Quotient.mk (Stacks.Sites.sectionIdeal (graphIdealSubsheaf π N ψ) X)
      (graphSection π N ψ X g)) = 0
  rw [show Ideal.Quotient.mk (Stacks.Sites.sectionIdeal (graphIdealSubsheaf π N ψ) X)
      (graphSection π N ψ X g) = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ⟨g, rfl⟩]
  exact map_zero _

/-- **The inclusion of `R` carries the kernel ideal `ℐ'` into `𝒢` by `ψ`.** This is exactly the
relation imposed by the graph ideal: `(g, 0)` and `(0, ψ g)` differ by the antidiagonal section
of `g`. -/
theorem pushoutInl_app_kernel (X : Cᵒᵖ) (g : ↥(kernelIdeal π.hom X)) :
    (pushoutInl π N ψ).hom.app X (g : ↥(R.obj.obj X)) =
      pushoutInr π N ψ X (ψ.app X g) := by
  have hsum : graphSection π N ψ X g + inrSection N X (ψ.app X g) =
      sqZeroExtMk (M := modules N) (g : ↥(R.obj.obj X)) (0 : ↥((modules N).obj X)) := by
    refine sqZeroExt_ext ?_ ?_
    · rw [sqZeroExtFst_add, graphSection_fst, inrSection_fst, add_zero, sqZeroExtFst_mk]
    · rw [sqZeroExtSnd_add, graphSection_snd, inrSection_snd, sqZeroExtSnd_mk, neg_add_cancel]
  refine (pushoutInl_app π N ψ X (g : ↥(R.obj.obj X))).trans ?_
  refine (congrArg (ConcreteCategory.hom ((pushoutMk π N ψ).hom.app X)) hsum.symm).trans ?_
  refine (map_add (ConcreteCategory.hom ((pushoutMk π N ψ).hom.app X))
    (graphSection π N ψ X g) (inrSection N X (ψ.app X g))).trans ?_
  exact (congrArg (fun z => z + (pushoutMk π N ψ).hom.app X (inrSection N X (ψ.app X g)))
    (pushoutMk_app_graphSection π N ψ X g)).trans (zero_add _)

variable [K.WEqualsLocallyBijective CommRingCat.{u}]

/-- **The quotient map onto the pushout is locally surjective**: the objectwise quotient map is
surjective on sections, and the unit of sheafification is locally surjective. -/
instance isLocallySurjective_pushoutMk :
    Presheaf.IsLocallySurjective K (pushoutMk π N ψ).hom := by
  have h₁ : Presheaf.IsLocallySurjective K
      (Stacks.Sites.toQuotientPresheaf (graphIdealSubsheaf π N ψ)) :=
    Presheaf.isLocallySurjective_of_surjective K _
      (fun X => Stacks.Sites.toQuotientPresheaf_app_surjective (graphIdealSubsheaf π N ψ) X)
  have h₂ : Presheaf.IsLocallySurjective K
      (toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ))) :=
    (K.W_toSheafify _).isLocallySurjective
  change Presheaf.IsLocallySurjective K
    (Stacks.Sites.toQuotientPresheaf (graphIdealSubsheaf π N ψ) ≫
      toSheafify K (Stacks.Sites.quotientPresheaf (graphIdealSubsheaf π N ψ)))
  infer_instance

/-- **The ideal `𝒢` of the pushout is acted on through `ℬ`.** For an arbitrary local section `s`
of the pushout, `s · [(0, n)] = [(0, m)]` as soon as `m` is, locally on the site, the action on
`n` of any local lift to `R` of the image of `s` in `ℬ`.

The hypothesis is stated locally and without a `ℬ`-module structure on `𝒢`, because `s` need not
lift to `R` globally: `pushoutMk` is only locally surjective. The proof glues
`pushoutMk_mul_pushoutInr`, which is the same statement for `s` in the image of `pushoutMk`. -/
theorem mul_pushoutInr_of_local_smul {X : Cᵒᵖ} (s : ↥((pushoutSheaf π N ψ).obj.obj X))
    (n m : ↥((modules N).obj X))
    (h : ∀ ⦃Y : C⦄ (f : Y ⟶ X.unop) (r : ↥(R.obj.obj (op Y))),
      (pushoutProj π N ψ).hom.app (op Y) (((pushoutSheaf π N ψ).obj.map f.op).hom s) =
          π.hom.app (op Y) r →
        r • ((modules N).map f.op n) = (modules N).map f.op m) :
    s * pushoutInr π N ψ X n = pushoutInr π N ψ X m := by
  refine eq_of_locally_eq (isSheaf_forgetCommRing (pushoutSheaf π N ψ))
    (Presheaf.imageSieve_mem K (pushoutMk π N ψ).hom s) _ _ fun Y f hf => ?_
  obtain ⟨w, hw⟩ := hf
  have hs : ((pushoutSheaf π N ψ).obj.map f.op).hom s =
      (pushoutMk π N ψ).hom.app (op Y) w := hw.symm
  have hproj : (pushoutProj π N ψ).hom.app (op Y)
      (((pushoutSheaf π N ψ).obj.map f.op).hom s) =
        π.hom.app (op Y) (sqZeroExtFst (M := modules N) w) := by
    rw [hs]
    exact congrArg (fun α : (sqZeroExtSheaf R N).obj ⟶ B.obj => α.app (op Y) w)
      (pushoutMk_comp_pushoutProj_hom π N ψ)
  have e1 : ((pushoutSheaf π N ψ).obj.map f.op).hom (pushoutInr π N ψ X n) =
      pushoutInr π N ψ (op Y) ((modules N).map f.op n) := pushoutInr_map π N ψ f.op n
  have e2 : ((pushoutSheaf π N ψ).obj.map f.op).hom (pushoutInr π N ψ X m) =
      pushoutInr π N ψ (op Y) ((modules N).map f.op m) := pushoutInr_map π N ψ f.op m
  refine (map_mul (ConcreteCategory.hom ((pushoutSheaf π N ψ).obj.map f.op)) s
    (pushoutInr π N ψ X n)).trans ?_
  rw [hs, e1]
  exact (pushoutMk_mul_pushoutInr π N ψ (op Y) w _).trans
    ((congrArg (pushoutInr π N ψ (op Y)) (h f _ hproj)).trans e2.symm)

end Quotient

section Ideal

open Stacks.Sites.Conormal (presentationRingHom presentationScalar)

variable (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- A sheaf of `ℬ`-modules read as a sheaf of `R`-modules through `π`, which is the shape in
which the square-zero pushout consumes its ideal. -/
noncomputable abbrev restrictAlong :
    SheafOfModules.{u} (Stacks.Sheaves.Differentials.underlyingRingSheaf R) :=
  (SheafOfModules.restrictScalars (presentationRingHom.{u, u, u} K π)).obj G

variable (c : PushoutData π (restrictAlong π G)) [HasWeakSheafify K CommRingCat.{u}]
  [K.WEqualsLocallyBijective CommRingCat.{u}]

/-- **The ideal of the pushout is acted on through `ℬ`**, for a `ℬ`-module read over `R`: there
the local hypothesis of `mul_pushoutInr_of_local_smul` is automatic, the `R`-action on `𝒢` being
the `ℬ`-action through `π`. -/
theorem mul_pushoutInr_restrictAlong (X : Cᵒᵖ)
    (r : ↥((pushoutSheaf π (restrictAlong π G) c).obj.obj X)) (n : ↥(G.val.obj X)) :
    r * pushoutInr π (restrictAlong π G) c X n =
      pushoutInr π (restrictAlong π G) c X
        (presentationScalar (pushoutProj π (restrictAlong π G) c) X r • n) := by
  refine mul_pushoutInr_of_local_smul π (restrictAlong π G) c r n _ ?_
  intro Y f r' hr'
  have h1 : ((G.val.map f.op).hom
        (presentationScalar (pushoutProj π (restrictAlong π G) c) X r • n) :
          ↥(G.val.obj (op Y))) =
      ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.map f.op)
          (presentationScalar (pushoutProj π (restrictAlong π G) c) X r) •
        ((G.val.map f.op).hom n : ↥(G.val.obj (op Y))) :=
    G.val.map_smul f.op _ _
  have h2 : ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.map f.op)
        (presentationScalar (pushoutProj π (restrictAlong π G) c) X r) =
      presentationScalar π (op Y) r' :=
    (NatTrans.naturality_apply (pushoutProj π (restrictAlong π G) c).hom f.op r).symm.trans hr'
  have h3 : ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.map f.op)
        (presentationScalar (pushoutProj π (restrictAlong π G) c) X r) •
        ((G.val.map f.op).hom n : ↥(G.val.obj (op Y))) =
      presentationScalar π (op Y) r' • ((G.val.map f.op).hom n : ↥(G.val.obj (op Y))) :=
    congrArg (fun b ↦ b • ((G.val.map f.op).hom n : ↥(G.val.obj (op Y)))) h2
  exact (h1.trans h3).symm

/-- The local section of `𝒢` that a local section of the pushout killed by the projection comes
from. It is unique by `pushoutInr_injective`. -/
noncomputable def idealSectionOf (X : Cᵒᵖ)
    (g : ↥(kernelIdeal (pushoutProj π (restrictAlong π G) c).hom X)) : ↥(G.val.obj X) :=
  ((pushoutProj_app_eq_zero_iff π (restrictAlong π G) c X g.1).1 g.2).choose

/-- The defining property of `idealSectionOf`. -/
theorem pushoutInr_idealSectionOf (X : Cᵒᵖ)
    (g : ↥(kernelIdeal (pushoutProj π (restrictAlong π G) c).hom X)) :
    pushoutInr π (restrictAlong π G) c X (idealSectionOf π G c X g) =
      (g : ↥((pushoutSheaf π (restrictAlong π G) c).obj.obj X)) :=
  ((pushoutProj_app_eq_zero_iff π (restrictAlong π G) c X g.1).1 g.2).choose_spec

/-- `idealSectionOf` is additive. -/
theorem idealSectionOf_add (X : Cᵒᵖ)
    (g g' : ↥(kernelIdeal (pushoutProj π (restrictAlong π G) c).hom X)) :
    idealSectionOf π G c X (g + g') =
      idealSectionOf π G c X g + idealSectionOf π G c X g' := by
  have hadd : ∀ a b : ↥(G.val.obj X),
      pushoutInr π (restrictAlong π G) c X (a + b) =
        pushoutInr π (restrictAlong π G) c X a + pushoutInr π (restrictAlong π G) c X b :=
    fun a b ↦ pushoutInr_add π (restrictAlong π G) c X a b
  refine pushoutInr_injective π (restrictAlong π G) c X ?_
  rw [pushoutInr_idealSectionOf, hadd, pushoutInr_idealSectionOf, pushoutInr_idealSectionOf]
  rfl

/-- `idealSectionOf` is linear over the pushout acting through `ℬ`. -/
theorem idealSectionOf_smul (X : Cᵒᵖ)
    (r : ↥((pushoutSheaf π (restrictAlong π G) c).obj.obj X))
    (g : ↥(kernelIdeal (pushoutProj π (restrictAlong π G) c).hom X)) :
    idealSectionOf π G c X (r • g) =
      presentationScalar (pushoutProj π (restrictAlong π G) c) X r •
        idealSectionOf π G c X g := by
  refine pushoutInr_injective π (restrictAlong π G) c X ?_
  rw [pushoutInr_idealSectionOf, ← mul_pushoutInr_restrictAlong π G c X r
    (idealSectionOf π G c X g), pushoutInr_idealSectionOf]
  rfl

/-- `idealSectionOf` commutes with the restriction maps. -/
theorem idealSectionOf_map {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (g : ↥(kernelIdeal (pushoutProj π (restrictAlong π G) c).hom X)) :
    idealSectionOf π G c Y
        ⟨((pushoutSheaf π (restrictAlong π G) c).obj.map f).hom
            (g : ↥((pushoutSheaf π (restrictAlong π G) c).obj.obj X)),
          Stacks.Sites.Conormal.map_kernel (pushoutProj π (restrictAlong π G) c).hom f g.2⟩ =
      G.val.map f (idealSectionOf π G c X g) := by
  have hmap : ∀ n : ↥(G.val.obj X),
      pushoutInr π (restrictAlong π G) c Y (G.val.map f n) =
        ((pushoutSheaf π (restrictAlong π G) c).obj.map f).hom
          (pushoutInr π (restrictAlong π G) c X n) :=
    fun n ↦ (pushoutInr_map π (restrictAlong π G) c f n).symm
  refine pushoutInr_injective π (restrictAlong π G) c Y ?_
  rw [pushoutInr_idealSectionOf, hmap, pushoutInr_idealSectionOf]

/-- **The ideal of the square-zero pushout, as a restriction datum for its projection.** The
identification of the ideal with `𝒢` is the inverse of the inclusion `pushoutInr`, which is
injective with image exactly the kernel of the projection. -/
noncomputable def idealRestriction :
    Stacks.Sites.Conormal.IdealRestriction.{u, u, u, u}
      (pushoutProj π (restrictAlong π G) c) G where
  app X := AddMonoidHom.mk' (idealSectionOf π G c X) (idealSectionOf_add π G c X)
  app_smul X r g := idealSectionOf_smul π G c X r g
  app_map f g := idealSectionOf_map π G c f g

/-- **The restriction datum of the pushout reads off the section of `𝒢` a local section of the
ideal comes from**: the hypothesis identifies the underlying section of the pushout, and the
conclusion names the section of `𝒢`. -/
theorem idealRestriction_app_eq_of_val (X : Cᵒᵖ)
    (g : ↥(kernelIdeal (pushoutProj π (restrictAlong π G) c).hom X)) (n : ↥(G.val.obj X))
    (h : (g : ↥((pushoutSheaf π (restrictAlong π G) c).obj.obj X)) =
      pushoutInr π (restrictAlong π G) c X n) :
    (idealRestriction π G c).app X g = n :=
  pushoutInr_injective π (restrictAlong π G) c X
    ((pushoutInr_idealSectionOf π G c X g).trans h)

/-- The restriction datum of the pushout inverts the inclusion of the ideal. -/
theorem idealRestriction_app_pushoutInr (X : Cᵒᵖ) (n : ↥(G.val.obj X)) :
    (idealRestriction π G c).app X
        ⟨pushoutInr π (restrictAlong π G) c X n,
          pushoutProj_pushoutInr π (restrictAlong π G) c X n⟩ = n :=
  idealRestriction_app_eq_of_val π G c X _ n rfl

end Ideal

end Stacks.Sites.SqZeroPushout

end
