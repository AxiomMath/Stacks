module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.RingTheory.Module.Kaplansky

/-!
# Free global sections on an étale neighbourhood over the local ring of the base

Stacks 05KY asserts, for a morphism `f : X ⟶ S` locally of finite presentation and a
quasi-coherent module `F` of finite type on `X` which is flat over `S` at a point `x`, the
existence of an *elementary* étale neighbourhood `U` of `(S, f x)` together with a pointed affine
scheme `X'` over `Spec 𝒪_{U, u}` which is étale over `X ×_S Spec 𝒪_{U, u}`, on which the pullback
of `F` is of finite presentation and has *free* global sections over `𝒪_{U, u}`.

This file carries out the passage from the shape in which Stacks 05ID delivers its conclusion —
compatible elementary étale neighbourhoods `U` of `(S, f x)` and `Y` of `(X, x)`, both affine,
with a morphism `h : Y ⟶ U` over `f`, and projective global sections over `Γ(U, ⊤)` — to the
shape Stacks 05KY asserts, where the base has been replaced by the spectrum of the local ring
`𝒪_{U, u}`. The scheme `X'` is the base change `Y ×_U Spec 𝒪_{U, u}`, and every clause of
Stacks 05KY's conclusion except the projectivity of the global sections is derived here.

## Main definitions

* `AlgebraicGeometry.EtaleNeighborhood.liftBaseChange` is the comparison morphism
  `Y ⟶ X ×_S W` attached to an étale neighbourhood `Y` of `(X, x)` lying over an étale
  neighbourhood `W` of `(S, f x)`.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.etale_lift_fromSpecStalk`: the canonical morphism
  `Y ×_W Spec 𝒪_{W, w} ⟶ X ×_S Spec 𝒪_{W, w}` is étale.
* `AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections`: the conclusion of
  Stacks 05KY, from the single hypothesis `hID` recording the output of Stacks 05ID for a module
  of finite type, after base change to the local ring of the base neighbourhood.
  The unconditional Stacks 05KY is
  `AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections_of_isFiniteType`.

## Implementation notes

`AlgebraicGeometry.EtaleNeighborhood.liftBaseChange` is étale by étale cancellation
(`CategoryTheory.MorphismProperty.HasOfPostcompProperty`, available for `Etale` over `Etale`):
its composite with the first projection of `X ×_S U` is the étale structure morphism of `Y`, and
that first projection is étale as a base change of the structure morphism of `U`. Étaleness of
the morphism to `X ×_S Spec 𝒪_{U, u}` is then obtained by rewriting that morphism as a base
change of `liftBaseChange` along the two pasting isomorphisms
`CategoryTheory.Limits.pullbackRightPullbackFstIso` and
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`; no diagonal or separatedness argument is
needed, and the identification is checked clause by clause with
`CategoryTheory.Limits.pullback.hom_ext`.

The residue field clause uses that `AlgebraicGeometry.Scheme.fromSpecStalk` is surjective on
stalks, a property stable under base change, and that a morphism surjective on stalks induces an
isomorphism of residue fields. Note that the structure morphism of an elementary étale
neighbourhood does *not* induce an isomorphism of local rings, so this clause cannot be obtained
by identifying `𝒪_{U, u}` with `𝒪_{S, f x}`.

Local finite presentation of `h` is read off the factorization
`h = liftBaseChange ≫ (X ×_S W ⟶ W)`:
both factors are locally of finite presentation, the first because it is étale and the second
because it is a base change of `f`. This avoids the cancellation property for local finite
presentation, which is not available.

The one clause left as the hypothesis `hID` is projectivity of the global sections over
`𝒪_{U, u}`; it is the conclusion of Stacks 05ID (generalized from finitely presented to finite
type modules by Stacks 05I5) transported along the base change, and it is turned into freeness
here by Stacks 0593.

## References

* [Stacks Project, Tag 05KY](https://stacks.math.columbia.edu/tag/05KY)
* [Stacks Project, Tag 05ID](https://stacks.math.columbia.edu/tag/05ID)
* [Stacks Project, Tag 0593](https://stacks.math.columbia.edu/tag/0593)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

section Localize

namespace EtaleNeighborhood

variable {x : X} (W : EtaleNeighborhood S (f x)) (Y : EtaleNeighborhood X x)
  (h : Y.scheme ⟶ W.scheme) (hover : h ≫ W.toBase = Y.toBase ≫ f)

/-- The comparison morphism from an étale neighbourhood `Y` of `(X, x)` which lies over an étale
neighbourhood `W` of `(S, f x)` to the base change `X ×_S W`. -/
def liftBaseChange : Y.scheme ⟶ pullback f W.toBase :=
  pullback.lift Y.toBase h hover.symm

/-- The comparison morphism `liftBaseChange` composed with the first projection of `X ×_S W` is the
structure morphism of `Y`. -/
@[simp]
lemma liftBaseChange_fst : liftBaseChange f W Y h hover ≫ pullback.fst f W.toBase = Y.toBase :=
  pullback.lift_fst _ _ _

/-- The comparison morphism `liftBaseChange` composed with the second projection of `X ×_S W` is
`h`. -/
@[simp]
lemma liftBaseChange_snd : liftBaseChange f W Y h hover ≫ pullback.snd f W.toBase = h :=
  pullback.lift_snd _ _ _

/-- The comparison morphism to `X ×_S W` is étale. -/
instance : Etale (liftBaseChange f W Y h hover) := by
  refine MorphismProperty.HasOfPostcompProperty.of_postcomp
    (W' := @Etale) _ (pullback.fst f W.toBase) inferInstance ?_
  rw [liftBaseChange_fst]
  infer_instance

include hover in
/-- A morphism which factors through the comparison morphism to `X ×_S W` is locally of finite
presentation. -/
lemma locallyOfFinitePresentation_of_liftBaseChange [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation h := by
  rw [← liftBaseChange_snd f W Y h hover]
  exact MorphismProperty.comp_mem (@LocallyOfFinitePresentation) _ _ inferInstance inferInstance

include hover in
/-- **The étale clause of Stacks 05KY.** The canonical morphism from `Y ×_W Spec 𝒪_{W, w}` to
`X ×_S Spec 𝒪_{W, w}` is étale: it is a base change of the étale comparison morphism
`Y ⟶ X ×_S W`. -/
lemma etale_lift_fromSpecStalk
    (hcomm : (pullback.fst h (W.scheme.fromSpecStalk W.point) ≫ Y.toBase) ≫ f =
      pullback.snd h (W.scheme.fromSpecStalk W.point) ≫
        W.scheme.fromSpecStalk W.point ≫ W.toBase) :
    Etale (pullback.lift (pullback.fst h (W.scheme.fromSpecStalk W.point) ≫ Y.toBase)
      (pullback.snd h (W.scheme.fromSpecStalk W.point)) hcomm) := by
  have key : pullback.lift (pullback.fst h (W.scheme.fromSpecStalk W.point) ≫ Y.toBase)
        (pullback.snd h (W.scheme.fromSpecStalk W.point)) hcomm =
      (pullback.congrHom (liftBaseChange_snd f W Y h hover)
          (rfl : W.scheme.fromSpecStalk W.point = W.scheme.fromSpecStalk W.point)).inv ≫
        (pullbackRightPullbackFstIso (pullback.snd f W.toBase) (W.scheme.fromSpecStalk W.point)
          (liftBaseChange f W Y h hover)).inv ≫
        pullback.snd (liftBaseChange f W Y h hover)
          (pullback.fst (pullback.snd f W.toBase) (W.scheme.fromSpecStalk W.point)) ≫
        (pullbackLeftPullbackSndIso f W.toBase (W.scheme.fromSpecStalk W.point)).hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp [pullback.map]
    · rw [pullback.lift_snd]
      simp [pullback.map]
  rw [key]
  infer_instance

end EtaleNeighborhood

end Localize

/-- Stacks 0593 with the module structure as an explicit argument: the scalar action on the
global sections appearing in Stacks 05KY is a restriction of scalars which instance resolution
cannot find, so it has to be passed in rather than synthesized. -/
private theorem free_of_projective_module' (R : Type u) [CommRing R] [IsLocalRing R] (M : Type u)
    [AddCommGroup M] (inst : Module R M) (hM : @Module.Projective R _ M _ inst) :
    @Module.Free R M _ _ inst :=
  @Module.free_of_projective_of_isLocalRing R M _ _ inst _ hM

/-- The pullback of a sheaf of modules of finite presentation on a scheme is of finite
presentation; this is Stacks 01BQ transported from ringed spaces to schemes. -/
private theorem isFinitePresentation_schemePullback {A B : Scheme.{u}} (c : A ⟶ B)
    (M : B.Modules) (hM : M.IsFinitePresentation) :
    ((Scheme.Modules.pullback c).obj M).IsFinitePresentation :=
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ c.toLRSHom.toShHom M hM

/-- The conclusion of Stacks Tag 05KY, conditional on the hypothesis `hID`: a pointed affine
étale neighbourhood over the local ring of an elementary étale neighbourhood of the base, on which
the pullback of `F` is finitely presented with free global sections.

This is not Tag 05KY itself. The hypothesis `hID` is the conclusion of Stacks 05ID for a module of
finite type — which Stacks obtains by combining Stacks 05ID with Stacks 05I5 — with its
projectivity clause transported along the base change to the local ring of the base
neighbourhood, and the flatness hypothesis is not used. Everything else in the conclusion is
derived. The unconditional statement, Tag 05KY, is
`AlgebraicGeometry.exists_etale_neighborhood_with_free_globalSections_of_isFiniteType`. -/
theorem exists_etale_neighborhood_with_free_globalSections
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (_hflat : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hID : ∃ (W : EtaleNeighborhood S (f x)) (Y : EtaleNeighborhood X x)
      (h : Y.scheme ⟶ W.scheme) (_ : W.IsElementary) (_ : Y.IsElementary)
      (_ : h ≫ W.toBase = Y.toBase ≫ f) (_ : h Y.point = W.point)
      (_ : IsAffine Y.scheme) (_ : IsAffine W.scheme)
      (_ : ((Scheme.Modules.pullback Y.toBase).obj F).IsFinitePresentation),
      letI : Module (W.scheme.presheaf.stalk W.point)
          Γ((Scheme.Modules.pullback (pullback.fst h (W.scheme.fromSpecStalk W.point) ≫
            Y.toBase)).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (W.scheme.presheaf.stalk W.point))).inv ≫
            (pullback.snd h (W.scheme.fromSpecStalk W.point)).appTop).hom
      Module.Projective (W.scheme.presheaf.stalk W.point)
        Γ((Scheme.Modules.pullback (pullback.fst h (W.scheme.fromSpecStalk W.point) ≫
          Y.toBase)).obj F, ⊤)) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary)
      (X' : Scheme.{u}) (x' : X')
      (g : X' ⟶ X)
      (q : X' ⟶ Spec (.of (U.scheme.presheaf.stalk U.point)))
      (_ : g x' = x)
      (_ : q x' = IsLocalRing.closedPoint (U.scheme.presheaf.stalk U.point))
      (hcomm : g ≫ f = q ≫ U.scheme.fromSpecStalk U.point ≫ U.toBase)
      (_ : Etale (pullback.lift g q hcomm))
      (_ : IsIso (g.residueFieldMap x'))
      (_ : IsAffine X')
      (_ : FinitePresentation q)
      (_ : ((Scheme.Modules.pullback g).obj F).IsFinitePresentation),
      letI : Module (U.scheme.presheaf.stalk U.point)
          Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
        Module.compHom _
          ((Scheme.ΓSpecIso (.of (U.scheme.presheaf.stalk U.point))).inv ≫ q.appTop).hom
      Module.Free (U.scheme.presheaf.stalk U.point)
        Γ((Scheme.Modules.pullback g).obj F, ⊤) := by
  obtain ⟨W, Y, h, hWel, hYel, hover, hhY, hYaff, hWaff, hMfp, hproj⟩ := hID
  let _ := hYaff
  let _ := hWaff
  -- The spectrum of the local ring of `W` at its distinguished point, and `X' = Y ×_W Spec`.
  obtain ⟨x', hx'fst, hx'snd⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := h) (g := W.scheme.fromSpecStalk W.point) Y.point
    (IsLocalRing.closedPoint (W.scheme.presheaf.stalk W.point))
    (by rwa [Scheme.fromSpecStalk_closedPoint])
  -- the two structure morphisms of `X'`
  have hgx : (pullback.fst h (W.scheme.fromSpecStalk W.point) ≫ Y.toBase) x' = x := by
    rw [Scheme.Hom.comp_apply, hx'fst, Y.map_point]
  have hcomm : (pullback.fst h (W.scheme.fromSpecStalk W.point) ≫ Y.toBase) ≫ f =
      pullback.snd h (W.scheme.fromSpecStalk W.point) ≫
        W.scheme.fromSpecStalk W.point ≫ W.toBase := by
    rw [Category.assoc, ← hover, ← Category.assoc, pullback.condition, Category.assoc]
  -- the residue field clause
  have hsurj : SurjectiveOnStalks (pullback.fst h (W.scheme.fromSpecStalk W.point)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback h (W.scheme.fromSpecStalk W.point)).flip inferInstance
  have hres : IsIso ((pullback.fst h (W.scheme.fromSpecStalk W.point) ≫
      Y.toBase).residueFieldMap x') := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso'
      ((Y.toBase.isIso_residueFieldMap_congr hx'fst).mpr (Y.isElementary_iff.mp hYel))
      ((pullback.fst h (W.scheme.fromSpecStalk W.point)).isIso_residueFieldMap_of_surjectiveOnStalks
        x')
  -- finite presentation of the structure morphism to the spectrum of the local ring
  have hfp : FinitePresentation (pullback.snd h (W.scheme.fromSpecStalk W.point)) :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback h (W.scheme.fromSpecStalk W.point))
      (EtaleNeighborhood.locallyOfFinitePresentation_of_liftBaseChange f W Y h hover),
      inferInstance, inferInstance⟩
  -- finite presentation of the pulled back module
  have hMfp' : ((Scheme.Modules.pullback (pullback.fst h (W.scheme.fromSpecStalk W.point) ≫
      Y.toBase)).obj F).IsFinitePresentation := by
    refine (SheafOfModules.isFinitePresentation
      (pullback h (W.scheme.fromSpecStalk W.point)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.pullbackComp (pullback.fst h (W.scheme.fromSpecStalk W.point))
        Y.toBase).app F) ?_
    exact isFinitePresentation_schemePullback _ _ hMfp
  exact ⟨W, hWel, pullback h (W.scheme.fromSpecStalk W.point), x', _, _, hgx, hx'snd, hcomm,
    EtaleNeighborhood.etale_lift_fromSpecStalk f W Y h hover hcomm, hres, inferInstance, hfp, hMfp',
    free_of_projective_module' _ _ _ hproj⟩

end AlgebraicGeometry

end
