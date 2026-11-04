module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition

/-!
# The square of small étale sites of a morphism of schemes, read through the inverse comparisons

`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` compares the two routes round the
square of small étale sites attached to a morphism `k : U' ⟶ U` of schemes of the big fppf site
over `S`: base change of étale charts along the represented morphism followed by the
identification of the small étale site of `yoneda.obj U'` with that of the scheme `U'`, against
that identification for `U` followed by base change of schemes.  Both composites are written with
the *functor* of the identification.

The direct image of modules that the derivation square of Stacks 05ZC and Stacks 05ZD needs is
written with the *inverse* of that identification instead — it is
`AlgebraicGeometry.Space.representedModuleRestriction`, the direct image along
`AlgebraicGeometry.Space.representedStructureMapInverse`, which is what
`AlgebraicGeometry.Space.schemeZariskiDerivationEquiv` produces.  This file supplies the
comparison of the two routes in that orientation.

The construction is the standard conjugation — whisker in the unit of the identification for
`U'`, the comparison, and the counit of the identification for `U` — so naturality comes for
free.  What a consumer needs in addition is that the *functor* of the identification carries it
back to the original comparison, which is
`AlgebraicGeometry.Space.functor_map_representedSmallEtaleBaseChangeInverseIso_hom`: the counit of
the identification is the identity
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_counit_app`) and the functor carries
the unit to an identity
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_functor_map_unit`), so only the
comparison survives.

With that comparison the two iterated direct images of modules round the square are identified,
`AlgebraicGeometry.Space.representedModulePushforwardInverseSquareIso`: it is
`SheafOfModules.pushforwardComp` at each end and `SheafOfModules.pushforwardCongr₂` in the middle,
and the one equation `pushforwardCongr₂` asks for — that the two routes carry the structure sheaf
of the scheme `U` to the structure sheaf of the small étale site of `yoneda.obj U'` by the same
map — is `AlgebraicGeometry.Space.representedStructureMapRing_inverse_square`.

Sections lemmas used by the same consumer are recorded here as well, each in the generality in
which it is cheap: the action of `SheafOfModules.pushforwardComp` on sections, which is the
identity, the composite round a square — whose middle factor is the action of
`SheafOfModules.pushforwardCongr₂` on sections, recorded in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents` — and the `.hom` half
of `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app`.

## Main definitions

* `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeInverseIso`: **the comparison of the two
  routes round the square of small étale sites, written with the inverse of the identification of
  the small étale site of a representable algebraic space with that of its scheme.**
* `AlgebraicGeometry.Space.representedModulePushforwardInverseSquareIso`: **the two routes round
  that square have the same iterated direct image of modules.**

## Main results

* `AlgebraicGeometry.Space.functor_map_representedSmallEtaleBaseChangeInverseIso_hom`: the functor
  of the identification carries it to
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, up to the counit for `U`.
* `AlgebraicGeometry.Space.functor_map_representedSmallEtaleBaseChangeInverseIso_inv_comp`: the
  same read as a cancellation, which is the form the compatibility of the two structure maps
  round the square needs.
* `AlgebraicGeometry.Space.representedStructureMapRing_inverse_square`: **the two routes round
  the square of small étale ringed sites carry the structure sheaf of the scheme `U` to the
  structure sheaf of the small étale site of `yoneda.obj U'` by the same map**, in the
  inverse-direction orientation.  This is the one equation the comparison of the direct images
  owed.
* `Stacks.SectionsComponents.pushforwardComp_hom_app_val_app` and
  `Stacks.SectionsComponents.pushforwardComp_inv_app_val_app`: contracting an iterated direct
  image of modules does nothing on sections.
* `Stacks.SectionsComponents.pushforwardSquare_hom_app_val_app`: the two together — the comparison
  of the two iterated direct images round a square of ringed sites is, on sections, restriction
  along the comparison of the two composite index functors.
* `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_hom_app_app`: the comparison of the
  two composite restrictions is restriction along the base change of an open, in the `.hom`
  direction.

## Implementation notes

`AlgebraicGeometry.Space.functor_map_representedSmallEtaleBaseChangeInverseIso_hom` is proved by
`show` followed by `simp only`, and **the `simp only` cannot be replaced by the corresponding `rw`
chain**: on this goal, a single `rw` of `CategoryTheory.Functor.map_comp` exhausts the
heartbeat budget while the `simp only` doing both of them costs a fraction of it.  The objects of
the two small étale sites have two definitionally but not reducibly equal spellings (see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean`), and `rw` has to
re-check the abstracted motive against them.

For the same reason **the counit of the identification for `U` is kept in the statement rather
than cancelled**, even though it is the identity.  Cancelling it needs
`CategoryTheory.Functor.map_id` to fire on
`(representedSchemeBaseChange B S hS k).map (𝟙 T)`, whose two sides are at
`(inverse ⋙ functor).obj T` and at `T`; that identification is definitional but not reducible, so
neither `simp only [CategoryTheory.Functor.map_id]` nor the corresponding `rw` applies — the
first reports "made no progress" with a type-correctness note and the second times out.  For the
same reason `CategoryTheory.Category.id_comp` has to be discharged by `exact` rather than by
`simp only`: after the unit has been rewritten to an identity, the identity is spelled at
`functor.obj W` while the morphism it precedes starts at
`functor.obj (inverse.obj (functor.obj W))`.

Three further heartbeat measurements, each of which cost real time:

* `AlgebraicGeometry.Space.representedStructureMapRing_inverse_square` cannot be proved by
  reducing its two sides to explicit composites.  `change`, and equally an `exact` of a term with
  the composite written out, times out: the component of
  `AlgebraicGeometry.Space.representedSchemeStructureMapRing` has its target spelled through
  `k.left` rather than through `BigFppfOver.toScheme`, so composing *that component* with a
  restriction map of the scheme's structure sheaf is not elaborable at all.  Composing with the
  whole `SheafOfModules.comparisonComp` instead is, because its type is written in the
  `represented…` spelling throughout.
* In the same proof the last rewrite is a `simp only`, not a `congrArg`: building a `congrArg`
  motive re-elaborates the composition it abstracts over, and that is what costs the budget.
  `CategoryTheory.Functor.map_id` must be given **both** arguments explicitly; with
  metavariables there the unifier walks into the two spellings of the object and times out.
* `Stacks.SectionsComponents.pushforwardSquare_hom_app_val_app` is stated for the composite
  *written out* rather than for a named isomorphism, and with every site and structure comparison
  a variable, because those are the only forms that can be checked.  Reading it at the concrete
  square — i.e. recording the sections action of
  `AlgebraicGeometry.Space.representedModulePushforwardInverseSquareIso` as a lemma of its own —
  times out at `whnf` whether the six arguments are left to unification or supplied explicitly,
  and so does giving the composite a name with the concrete type ascribed.

  **That reading is available by a different route; the route above fails for the following
  reason.**  It is not the shape of the statement and not the `eqToHom` inside
  `SheafOfModules.pushforwardCongr`: with the structure maps *and* the comparison of index
  functors left as variables the reading is `rfl` and cheap (that is Mathlib's
  `SheafOfModules.pushforwardNatTrans_app_val_app`); substituting the concrete structure maps
  keeps it cheap; substituting the concrete comparison
  `(AlgebraicGeometry.Space.representedSmallEtaleBaseChangeInverseIso …).inv` makes the same
  `rfl` exhaust the budget.  The target of `PresheafOfModules.map f` is a
  `ModuleCat.restrictScalars` along `f`, so deciding that the two sides of such a reading have
  the same type forces a weak-head-normalisation of that natural transformation, and it is the
  conjugate of Stacks 03G2 (4) by two tactic-built equivalences of sites.  The remedy is to wrap
  the comparison in a definition made `irreducible` after the one statement that needs its value,
  and to rebuild the middle factor as `SheafOfModules.pushforwardNatTrans` followed by
  `SheafOfModules.pushforwardCongr` rather than extracting it from the isomorphism; see
  `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePushforwardInverseSquareSections.lean`,
  where the reading is `AlgebraicGeometry.Space.representedSquareMiddle_app_val_app_apply`.

No Stacks tag is registered: the comparison of the two base changes is Stacks 03G2, part (4),
attributed where `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` is proved, and this
file only rewrites it in the other orientation.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The comparison of the two composite restrictions is restriction along the base change of an
open**, in the `.hom` direction.  Over an open `V` of `Y` it is the restriction map of `𝓕^a` along
the identification of the preimage open with the base change of `V`.

This is `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app` for the other
direction of the same isomorphism; the two spellings of its source and target agree by
unfolding. -/
public theorem restrictModuleBaseChangeIso_hom_app_app
    (M : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (V : Y.obj.Opens) :
    Scheme.Modules.Hom.app ((restrictModuleBaseChangeIso B a).hom.app M) V =
      M.val.presheaf.map ((baseChangeOpensIso B a).hom.app V).op :=
  rfl

end AlgebraicGeometry.SmallEtale

namespace Stacks.SectionsComponents

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w m

section PushforwardComp

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {F : C ⥤ D} {G : D ⥤ D'}
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} {R' : Sheaf K' RingCat.{w}}
  [F.IsContinuous J K] [G.IsContinuous K K'] [(F ⋙ G).IsContinuous J K']
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{w} K K').obj R')

omit [(F ⋙ G).IsContinuous J K'] in
/-- **Contracting an iterated direct image of modules does nothing on sections.**  Both sides
have the sections of `M` over the image of the object under the composite index functor. -/
public theorem pushforwardComp_hom_app_val_app (M : SheafOfModules.{m} R') (A : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{m} ψ ⋙ SheafOfModules.pushforward.{m} φ).obj M).val.obj A) :
    ((SheafOfModules.pushforwardComp.{m} φ ψ).hom.app M).val.app A x = x := rfl

/-- **Expanding a direct image of modules along a composite structure map does nothing on
sections.** -/
public theorem pushforwardComp_inv_app_val_app (M : SheafOfModules.{m} R') (A : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{m}
        (SheafOfModules.comparisonComp φ ψ)).obj M).val.obj A) :
    ((SheafOfModules.pushforwardComp.{m} φ ψ).inv.app M).val.app A x = x := rfl

end PushforwardComp

section PushforwardSquare

variable {A : Type u₁} [Category.{v₁} A] {B₁ : Type u₂} [Category.{v₂} B₁]
  {B₂ : Type u₃} [Category.{v₃} B₂] {E : Type u₄} [Category.{v₄} E]
  {J : GrothendieckTopology A} {K₁ : GrothendieckTopology B₁} {K₂ : GrothendieckTopology B₂}
  {L : GrothendieckTopology E} {F₁ : A ⥤ B₁} {G₁ : B₁ ⥤ E} {F₂ : A ⥤ B₂} {G₂ : B₂ ⥤ E}
  {R : Sheaf J RingCat.{w}} {R₁ : Sheaf K₁ RingCat.{w}} {R₂ : Sheaf K₂ RingCat.{w}}
  {R' : Sheaf L RingCat.{w}}
  [F₁.IsContinuous J K₁] [G₁.IsContinuous K₁ L] [(F₁ ⋙ G₁).IsContinuous J L]
  [F₂.IsContinuous J K₂] [G₂.IsContinuous K₂ L] [(F₂ ⋙ G₂).IsContinuous J L]
  (φ₁ : R ⟶ (F₁.sheafPushforwardContinuous RingCat.{w} J K₁).obj R₁)
  (ψ₁ : R₁ ⟶ (G₁.sheafPushforwardContinuous RingCat.{w} K₁ L).obj R')
  (φ₂ : R ⟶ (F₂.sheafPushforwardContinuous RingCat.{w} J K₂).obj R₂)
  (ψ₂ : R₂ ⟶ (G₂.sheafPushforwardContinuous RingCat.{w} K₂ L).obj R')
  (e : F₁ ⋙ G₁ ≅ F₂ ⋙ G₂)
  (h : SheafOfModules.comparisonComp φ₂ ψ₂ ≫
    (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{w} J L).app R' =
      SheafOfModules.comparisonComp φ₁ ψ₁)

/-- **The comparison of the two iterated direct images of modules round a square of ringed sites
is, on sections, the restriction map along the comparison of the two composite index functors.**
The comparison is `SheafOfModules.pushforwardComp` at each end with
`SheafOfModules.pushforwardCongr₂` in the middle; contracting and expanding an iterated direct
image does nothing on sections
(`Stacks.SectionsComponents.pushforwardComp_hom_app_val_app` and
`Stacks.SectionsComponents.pushforwardComp_inv_app_val_app`), so the only content is the middle
factor, `Stacks.SectionsComponents.pushforwardCongr₂_inv_app_val_app`.

Stated for the composite written out, and with the four sites and the four structure comparisons
variable, because that is the only form in which it can be checked: at a concrete square of small
étale sites the same `rfl` exhausts the heartbeat budget, and so does giving the composite a name
of its own and ascribing the concrete type to it. -/
public theorem pushforwardSquare_hom_app_val_app (M : SheafOfModules.{m} R') (X : Aᵒᵖ)
    (x : ((SheafOfModules.pushforward.{m} ψ₁ ⋙
      SheafOfModules.pushforward.{m} φ₁).obj M).val.obj X) :
    (((SheafOfModules.pushforwardComp.{m} φ₁ ψ₁ ≪≫
        (SheafOfModules.pushforwardCongr₂.{m}
          (SheafOfModules.comparisonComp φ₂ ψ₂) e h).symm ≪≫
        (SheafOfModules.pushforwardComp.{m} φ₂ ψ₂).symm).hom.app M).val.app X) x =
      M.val.map (e.inv.app X.unop).op x := rfl

end PushforwardSquare

end Stacks.SectionsComponents

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U' U : BigFppfOver B S hS} (k : U' ⟶ U)
  (hk : yoneda.relativelyRepresentable (yoneda.map k))

/-- **The comparison of the two routes round the square of small étale sites, written with the
inverse of the identification of the small étale site of a representable algebraic space with
that of its scheme.**  Reading an object of the small étale site of the scheme `U` on the small
étale site of `yoneda.obj U` and base changing its chart along the represented morphism is base
changing it along `k` as a scheme and reading the result on the small étale site of
`yoneda.obj U'`.

The conjugate of `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` by the two
identifications: the unit for `U'`, the comparison, and the counit for `U`. -/
def representedSmallEtaleBaseChangeInverseIso :
    (representedSmallEtaleEquivalence B S hS U).inverse ⋙
        smallBaseChange B S hS (representedSpaceMap B S hS k) hk ≅
      representedSchemeBaseChange B S hS k ⋙
        (representedSmallEtaleEquivalence B S hS U').inverse := by
  refine Iso.trans (Y := (representedSmallEtaleEquivalence B S hS U).inverse ⋙
      smallBaseChange B S hS (representedSpaceMap B S hS k) hk ⋙
      (representedSmallEtaleEquivalence B S hS U').functor ⋙
      (representedSmallEtaleEquivalence B S hS U').inverse)
    (Functor.isoWhiskerLeft ((representedSmallEtaleEquivalence B S hS U).inverse ⋙
      smallBaseChange B S hS (representedSpaceMap B S hS k) hk)
      (representedSmallEtaleEquivalence B S hS U').unitIso) ?_
  refine Iso.trans (Y := (representedSmallEtaleEquivalence B S hS U).inverse ⋙
      (representedSmallEtaleEquivalence B S hS U).functor ⋙
      representedSchemeBaseChange B S hS k ⋙
      (representedSmallEtaleEquivalence B S hS U').inverse)
    (Functor.isoWhiskerRight (Functor.isoWhiskerLeft
      (representedSmallEtaleEquivalence B S hS U).inverse
      (representedSmallEtaleBaseChangeIso B S hS k hk))
      (representedSmallEtaleEquivalence B S hS U').inverse) ?_
  exact Functor.isoWhiskerRight (representedSmallEtaleEquivalence B S hS U).counitIso
    (representedSchemeBaseChange B S hS k ⋙
      (representedSmallEtaleEquivalence B S hS U').inverse)

/-- Reading an object of the small étale site of the scheme `U` on the small étale site of
`yoneda.obj U` and base changing it is continuous. -/
instance isContinuous_representedInverse_comp_smallBaseChange :
    ((representedSmallEtaleEquivalence B S hS U).inverse ⋙
        smallBaseChange B S hS (representedSpaceMap B S hS k) hk).IsContinuous
      (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U')) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_representedSmallEtaleEquivalence_inverse B S hS U)
    (isContinuous_representedSmallBaseChange B S hS k hk)

/-- Base changing an object of the small étale site of the scheme `U` along `k` and reading the
result on the small étale site of `yoneda.obj U'` is continuous. -/
instance isContinuous_representedSchemeBaseChange_comp_representedInverse :
    (representedSchemeBaseChange B S hS k ⋙
        (representedSmallEtaleEquivalence B S hS U').inverse).IsContinuous
      (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U')) :=
  @Functor.isContinuous_comp _ _ _ _ _ _ _ _ _ _ _
    (isContinuous_representedSchemeBaseChange B S hS k)
    (isContinuous_representedSmallEtaleEquivalence_inverse B S hS U')

/-- **The functor of the identification carries the inverse-direction comparison back to
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`**, up to the counit of the
identification for `U`.  This is what pins the inverse-direction comparison: the functor carries
the unit for `U'` to an identity
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_functor_map_unit`) and is a retraction
of the inverse on morphisms
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_functor_map_inverse_map`), so of the
three whiskered factors only the comparison and the counit survive.

The counit is the identity by
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_counit_app`, but it is kept in the
statement rather than cancelled here; see the implementation notes. -/
theorem functor_map_representedSmallEtaleBaseChangeInverseIso_hom
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :
    (representedSmallEtaleEquivalence B S hS U').functor.map
        ((representedSmallEtaleBaseChangeInverseIso B S hS k hk).hom.app T) =
      (representedSmallEtaleBaseChangeIso B S hS k hk).hom.app
          ((representedSmallEtaleEquivalence B S hS U).inverse.obj T) ≫
        (representedSchemeBaseChange B S hS k).map
          ((representedSmallEtaleEquivalence B S hS U).counitIso.hom.app T) := by
  show (representedSmallEtaleEquivalence B S hS U').functor.map
      ((representedSmallEtaleEquivalence B S hS U').unitIso.hom.app
          ((smallBaseChange B S hS (representedSpaceMap B S hS k) hk).obj
            ((representedSmallEtaleEquivalence B S hS U).inverse.obj T)) ≫
        (representedSmallEtaleEquivalence B S hS U').inverse.map
          ((representedSmallEtaleBaseChangeIso B S hS k hk).hom.app
            ((representedSmallEtaleEquivalence B S hS U).inverse.obj T)) ≫
        (representedSmallEtaleEquivalence B S hS U').inverse.map
          ((representedSchemeBaseChange B S hS k).map
            ((representedSmallEtaleEquivalence B S hS U).counitIso.hom.app T))) = _
  simp only [Functor.map_comp, representedSmallEtaleEquivalence_functor_map_unit,
    representedSmallEtaleEquivalence_functor_map_inverse_map]
  exact Category.id_comp _

/-- **The inverse-direction comparison composed with the comparison is the identity**, after the
functor of the identification has been applied.  This is the form in which the compatibility of
the two structure maps round the square consumes
`AlgebraicGeometry.Space.functor_map_representedSmallEtaleBaseChangeInverseIso_hom`. -/
theorem functor_map_representedSmallEtaleBaseChangeInverseIso_inv_comp
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :
    (representedSmallEtaleEquivalence B S hS U').functor.map
          ((representedSmallEtaleBaseChangeInverseIso B S hS k hk).inv.app T) ≫
        (representedSmallEtaleBaseChangeIso B S hS k hk).hom.app
            ((representedSmallEtaleEquivalence B S hS U).inverse.obj T) ≫
          (representedSchemeBaseChange B S hS k).map
            ((representedSmallEtaleEquivalence B S hS U).counitIso.hom.app T) =
      𝟙 ((representedSmallEtaleEquivalence B S hS U').functor.obj
        ((representedSchemeBaseChange B S hS k ⋙
          (representedSmallEtaleEquivalence B S hS U').inverse).obj T)) := by
  refine Eq.trans (congrArg
    (fun m ↦ (representedSmallEtaleEquivalence B S hS U').functor.map
      ((representedSmallEtaleBaseChangeInverseIso B S hS k hk).inv.app T) ≫ m)
    (functor_map_representedSmallEtaleBaseChangeInverseIso_hom B S hS k hk T).symm) ?_
  refine Eq.trans
    (((representedSmallEtaleEquivalence B S hS U').functor.map_comp _ _).symm) ?_
  refine Eq.trans (congrArg (representedSmallEtaleEquivalence B S hS U').functor.map
    ((representedSmallEtaleBaseChangeInverseIso B S hS k hk).inv_hom_id_app T)) ?_
  exact CategoryTheory.Functor.map_id _ _

/-- **The comparison of the two base changes absorbs the counit of the identification for `U`.**
The counit is the identity (`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_counit_app`),
so base changing it along `k` is an identity.  It is kept in the statement of
`AlgebraicGeometry.Space.functor_map_representedSmallEtaleBaseChangeInverseIso_hom` because
`CategoryTheory.Functor.map_id` cannot be made to fire there, and this is where it is cancelled —
with both arguments of `CategoryTheory.Functor.map_id` supplied explicitly, which is what keeps
the unifier away from the two spellings of the object. -/
theorem representedSmallEtaleBaseChangeIso_hom_app_comp_counit
    (T : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :
    (representedSmallEtaleBaseChangeIso B S hS k hk).hom.app
          ((representedSmallEtaleEquivalence B S hS U).inverse.obj T) ≫
        (representedSchemeBaseChange B S hS k).map
          ((representedSmallEtaleEquivalence B S hS U).counitIso.hom.app T) =
      (representedSmallEtaleBaseChangeIso B S hS k hk).hom.app
        ((representedSmallEtaleEquivalence B S hS U).inverse.obj T) := by
  refine Eq.trans (congrArg (fun m ↦ (representedSmallEtaleBaseChangeIso B S hS k hk).hom.app
    ((representedSmallEtaleEquivalence B S hS U).inverse.obj T) ≫ m)
    (CategoryTheory.Functor.map_id (representedSchemeBaseChange B S hS k) T)) ?_
  exact Category.comp_id _

/-- The structure sheaf of the small étale site of `yoneda.obj V` acts on a morphism of that site
as the structure sheaf of the small étale site of the scheme `V` acts on its image under the
identification of the two sites.  The two sheaves of rings are the same sheaf — this is what
`AlgebraicGeometry.Space.representedEquivSharp` being the identity says — so the statement is a
reindexing of one restriction map and holds by unfolding.  It is stated with the morphism a
variable, which is what makes it affordable at a use site where that morphism is a large term. -/
theorem representedStructureRingSheaf_map_op
    (V : BigFppfOver B S hS) {W₁ W₂ : SmallEtale B S hS (yoneda.obj V)} (g : W₁ ⟶ W₂) :
    (representedStructureRingSheaf B S hS V).obj.map g.op =
      (representedSchemeStructureSheaf B S hS V).obj.map
        ((representedSmallEtaleEquivalence B S hS V).functor.map g).op := rfl

/-- **The two routes round the square of small étale ringed sites carry the structure sheaf of the
scheme `U` to the structure sheaf of the small étale site of `yoneda.obj U'` by the same map**, in
the orientation in which the identifications of the two sites are taken backwards.  This is the
hypothesis `SheafOfModules.pushforwardCongr₂` needs in order to compare the two iterated direct
images of modules round the square.

It is `AlgebraicGeometry.Space.representedStructureMapRing_square` read at the object
`inverse_U.obj T`.  The comparison of structure sheaves across the identification of the sites is
an identity in both directions, so the two `SheafOfModules.comparisonComp`s differ from the
forward square's only in which of the two identifications is written; the inverse-direction
comparison of the index functors is carried by the functor of the identification to the forward
one (`AlgebraicGeometry.Space.functor_map_representedSmallEtaleBaseChangeInverseIso_hom`) up to the
counit, which
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso_hom_app_comp_counit` absorbs. -/
theorem representedStructureMapRing_inverse_square :
    SheafOfModules.comparisonComp (representedSchemeStructureMapRing B S hS k)
          (representedStructureMapInverse B S hS U') ≫
        (Functor.sheafPushforwardContinuousNatTrans
          (representedSmallEtaleBaseChangeInverseIso B S hS k hk).hom RingCat.{u}
          (representedSchemeSmallEtaleTopology B S hS U)
          (SmallEtale.topology B S hS (yoneda.obj U'))).app
          (representedStructureRingSheaf B S hS U') =
      SheafOfModules.comparisonComp (representedStructureMapInverse B S hS U)
        (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk) := by
  ext : 2
  funext T
  have hJ' := Eq.trans
    (functor_map_representedSmallEtaleBaseChangeInverseIso_hom B S hS k hk T.unop)
    (representedSmallEtaleBaseChangeIso_hom_app_comp_counit B S hS k hk T.unop)
  refine Eq.trans (congrArg (fun m ↦ (SheafOfModules.comparisonComp
        (representedSchemeStructureMapRing B S hS k)
        (representedStructureMapInverse B S hS U')).hom.app T ≫ m)
    (representedStructureRingSheaf_map_op B S hS U'
      ((representedSmallEtaleBaseChangeInverseIso B S hS k hk).hom.app T.unop))) ?_
  simp only [hJ']
  exact congrArg (fun m ↦ m.hom.app
      (op ((representedSmallEtaleEquivalence B S hS U).inverse.obj T.unop)))
    (representedStructureMapRing_square B S hS k hk)

/-- **The two routes round the square of small étale ringed sites have the same direct image of
modules**, in the orientation in which the identifications of the two sites are taken backwards:
base changing the étale charts along the represented morphism and then reading the result on the
small étale site of the scheme `U` is reading a module on the small étale site of the scheme `U'`
and taking the direct image along the morphism of ringed sites of Stacks 070R (2) of the
underlying morphism of schemes.

Both sides are the direct image along one of the two composite routes —
`SheafOfModules.pushforwardComp` at each end — and the two routes agree by
`AlgebraicGeometry.Space.representedStructureMapRing_inverse_square`.  No adjoint-uniqueness
isomorphism occurs anywhere in it, and its action on sections is
`Stacks.SectionsComponents.pushforwardSquare_hom_app_val_app`, read at this data: restriction
along the component of
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeInverseIso`.  That reading has not been
recorded as a lemma of its own — see the implementation notes. -/
def representedModulePushforwardInverseSquareIso :
    smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS k) hk ⋙
        representedModuleRestriction B S hS U ≅
      representedModuleRestriction B S hS U' ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS k) :=
  SheafOfModules.pushforwardComp.{u} (representedStructureMapInverse B S hS U)
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS k) hk) ≪≫
    (SheafOfModules.pushforwardCongr₂.{u} (SheafOfModules.comparisonComp
        (representedSchemeStructureMapRing B S hS k) (representedStructureMapInverse B S hS U'))
        (representedSmallEtaleBaseChangeInverseIso B S hS k hk)
        (representedStructureMapRing_inverse_square B S hS k hk)).symm ≪≫
    (SheafOfModules.pushforwardComp.{u} (representedSchemeStructureMapRing B S hS k)
      (representedStructureMapInverse B S hS U')).symm

end AlgebraicGeometry.Space

end
