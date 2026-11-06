module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Comorphism
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Uniqueness
public import StacksCore.Tactic.StacksAttribute

/-!
# Differentials and the associated module on the small étale site

Let `f : X ⟶ Y` be a morphism of schemes and let `f_small : X_étale ⟶ Y_étale` be the induced
morphism of small étale sites (Descent, Remark 070R).  Stacks 04CS compares the small-étale
sheaf `(Ω_{X/Y})^a` associated to the quasi-coherent module `Ω_{X/Y}` with the module of
differentials `Ω_{X_étale/Y_étale}` of `f_small` in the sense of Stacks 04BN, and asserts that
the comparison is an isomorphism compatible with the universal derivations.

This module constructs the comparison map, in the direction in which the source's proof
produces it.  A `Y`-derivation `D` of `𝒪_{X_étale}` with values in a sheaf of
`𝒪_{X_étale}`-modules `𝓕` restricts to the small Zariski site of `X`, where it becomes an
ordinary `Y`-derivation of `𝒪_X` with values in the restriction `ε_* 𝓕`; the universal property
of `Ω_{X/Y}` turns that into a map `c' : Ω_{X/Y} ⟶ ε_* 𝓕`, and the adjunction `ε^* ⊣ ε_*` of
Stacks 03DU (4) — whose left adjoint is the associated-module functor — turns `c'` into a map
`c'' : (Ω_{X/Y})^a ⟶ 𝓕`.  At `𝓕 = Ω_{X_étale/Y_étale}` carrying its universal derivation this is
the map the source's proof calls `c''`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedRelativeDifferentials` is `(Ω_{X/Y})^a`, the
  small-étale sheaf of modules associated to `Ω_{X/Y}`.
* `AlgebraicGeometry.SmallEtale.pullbackSection` is a function on an open of `Y` pulled back to
  its preimage, read as a section of `𝒪_{X_étale}`; the hypothesis on a derivation below is
  that it annihilates these sections.
* `AlgebraicGeometry.SmallEtale.zariskiRestrictionData` and
  `AlgebraicGeometry.SmallEtale.zariskiRestriction` restrict a derivation of `𝒪_{X_étale}` to
  the small Zariski site of `X`, the second one carrying the vanishing condition over
  `f⁻¹𝒪_Y`.
* `AlgebraicGeometry.SmallEtale.differentialsComparison` is the comparison map
  `c'' : (Ω_{X/Y})^a ⟶ 𝓕`.

## Main results

* `AlgebraicGeometry.SmallEtale.differentialsComparison_adjunct`: the adjunct of the comparison
  map carries the universal derivation `d_{X/Y}` to the small Zariski restriction of `D`.
* `AlgebraicGeometry.SmallEtale.eq_differentialsComparison`: it is the only map with that
  property, so the comparison map is canonical.

## Implementation notes

The derivation on the small étale site is taken in the form Mathlib's
`PresheafOfModules.Derivation'` provides — a derivation of the structure sheaf of commutative
rings `𝒪_{X_étale}` relative to an unspecified presheaf of commutative rings — together with the
hypothesis `hD` that it annihilates every function pulled back from an open of `Y`.  That is the
only consequence of being a `Y_étale`-derivation which the construction uses, and it is weaker
than the vanishing condition over `f_small^{-1}𝒪_{Y_étale}`, so the comparison map is produced
for more derivations than the source needs.  Stating it this way avoids the inverse image
`f_small^{-1}𝒪_{Y_étale}` altogether.

The inverse image is *not* unavailable on this site for universe reasons, although the objects
of the small étale site lie one universe above the sections of its structure sheaf, so that the
left Kan extension presenting the inverse image is a colimit of a shape in `Type (u+1)` taken in
`CommRingCat.{u}`.  Inverse
images of sheaves of commutative rings along the morphisms of this site are available:
`AlgebraicGeometry.SmallEtale.relativeStructureSheaf` is `ε^{-1}f^{-1}𝒪_Y` with structure map
`AlgebraicGeometry.SmallEtale.relativeStructureMap`, on a site of exactly this universe shape,
and `AlgebraicGeometry.Space.inverseImageStructureSheaf` builds the genuine
`f_small^{-1}𝒪_{Y_étale}` on the small étale site of an algebraic space, whose universes are the
same.  What the formulation above avoids is therefore not an unavailable object but the
identification of the two bases.

**The invertibility clause of Stacks 04CS is proved.**  The canonical isomorphism
`(Ω_{X/Y})^a ≅ Ω_{X_étale/Y_étale}` is `AlgebraicGeometry.SmallEtale.differentialsIso` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDifferentialsIso.lean`, with
`AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom` for its compatibility with the
universal derivations and `AlgebraicGeometry.SmallEtale.isIso_universalDifferentialsComparison`
saying that the comparison map `c''` built below is the invertible one; both sides are exhibited
as corepresenting objects of the one functor of `Y_étale`-derivations.  No identification of
`f_small^{-1}𝒪_{Y_étale}` with `ε^{-1}f^{-1}𝒪_Y` is used: only the two *classes* of derivations
enter the universal properties, and the adjunction `f_small^{-1} ⊣ f_{small,*}` for sheaves of
sets compares them directly.  The spaces-level reading of the same clause, for a morphism of
schemes of a big fppf site, is `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeTransport.lean`, and it is what
made Stacks 04CV unconditional.

On the Zariski side the vanishing condition is over `f⁻¹𝒪_Y`, whose sections over an open of `X`
need not come from a single section of `𝒪_Y`;
`AlgebraicGeometry.SheafOfModules.ofComorphism` is what reduces it to the sections that do.

The identification of `Γ(X, W)` with the global functions of the open subscheme `W`, which is
what lets a derivation on the small étale site be read on the small Zariski site, is the
structure map `AlgebraicGeometry.SmallEtale.commRingStructureMap` of the morphism of ringed
sites `(X_étale, 𝒪) ⟶ (X_Zar, 𝒪_X)` of Stacks 070R; using it rather than
`AlgebraicGeometry.Scheme.Opens.topIso` directly supplies the naturality in `W` for free.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN), the module of
  differentials of a homomorphism of sheaves of rings on a site.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module
  on the small étale site and its right adjoint.
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R), the morphism of ringed
  sites `(X_étale, 𝒪) ⟶ (X_Zar, 𝒪_X)`.
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US), the sheaf of relative
  differentials of a morphism of schemes and its universal property.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)

/-- `(Ω_{X/Y})^a`, the sheaf of modules on the small étale site of `X` associated to the
quasi-coherent module `Ω_{X/Y}` of relative differentials by the associated-module functor of
Stacks 03DU (4). -/
public noncomputable abbrev associatedRelativeDifferentials :
    SheafOfModules.{u} (structureSheaf B X hX) :=
  (associatedModule B X hX).obj (Scheme.Hom.relativeDifferentials f)

/-- A function `b` on an open `W` of `Y`, pulled back to the preimage `f⁻¹W` and read as a
section of the structure sheaf of the small étale site of `X` over the object `f⁻¹W`.  An open
subscheme of `X` is étale over `X`, so `f⁻¹W` is such an object. -/
public noncomputable def pullbackSection (W : Y.Opens) (b : Γ(Y, W)) :
    (commRingStructureSheaf B X hX).obj.obj
      (op ((opensToSmallEtale B X hX).obj (f ⁻¹ᵁ W))) :=
  ((commRingStructureMap B X hX).hom.app (op (f ⁻¹ᵁ W))).hom ((f.app W).hom b)

variable {F : SheafOfModules.{u} (structureSheaf B X hX)}
  {R : (SmallEtale B X hX)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ (commRingStructureSheaf B X hX).obj}
  (D : PresheafOfModulesOfCommRing.Derivation'
    (R := (commRingStructureSheaf B X hX).obj) F.val ψ)

/-- The restriction of a derivation of `𝒪_{X_étale}` to the small Zariski site of `X`, as bare
derivation data: over an open `W` of `X` it is the derivation of the global functions of the
open subscheme `W`, read through the identification `Γ(X, W) ≅ Γ(W, 𝒪_W)` given by the structure
map of the morphism of ringed sites `(X_étale, 𝒪) ⟶ (X_Zar, 𝒪_X)`.

The vanishing condition recorded here is only the Leibniz rule, over the constant presheaf of
rings `ℤ`; the vanishing condition over `f⁻¹𝒪_Y` is
`AlgebraicGeometry.SmallEtale.zariskiRestriction`. -/
public noncomputable def zariskiRestrictionData :
    PresheafOfModulesOfCommRing.Derivation' ((restrictModule B X hX).obj F).val
      (SheafOfModules.constIntMap X.presheaf) where
  d {W} := (D.d (X := op ((opensToSmallEtale B X hX).obj W.unop))).comp
    ((commRingStructureMap B X hX).hom.app W).hom.toAddMonoidHom
  d_mul {W} a b :=
    Eq.trans (congrArg (D.d (X := op ((opensToSmallEtale B X hX).obj W.unop)))
      (map_mul ((commRingStructureMap B X hX).hom.app W).hom a b)) (D.d_mul _ _)
  d_map {W W'} g x := by
    refine Eq.trans (congrArg (D.d (X := op ((opensToSmallEtale B X hX).obj W'.unop))) ?_)
      (D.d_map ((opensToSmallEtale B X hX).map g.unop).op
        (((commRingStructureMap B X hX).hom.app W).hom x))
    exact congrArg (fun m : CommRingCat.Hom _ _ => m.hom x)
      ((commRingStructureMap B X hX).hom.naturality g)
  d_app {W} a := by
    refine SheafOfModules.constIntMap_app_eq_zero
      ((D.d (X := op ((opensToSmallEtale B X hX).obj W.unop))).comp
        ((commRingStructureMap B X hX).hom.app W).hom.toAddMonoidHom) ?_ a
    refine Eq.trans (congrArg (D.d (X := op ((opensToSmallEtale B X hX).obj W.unop)))
      (map_one ((commRingStructureMap B X hX).hom.app W).hom)) ?_
    exact D.d_one _

/-- The small Zariski restriction of a derivation is, on sections over an open `W` of `X`, the
derivation applied to the global functions of the open subscheme `W`. -/
public theorem zariskiRestrictionData_d {W : (X.Opens)ᵒᵖ} (a : Γ(X, W.unop)) :
    (zariskiRestrictionData B hX D).d a =
      D.d (X := op ((opensToSmallEtale B X hX).obj W.unop))
        (((commRingStructureMap B X hX).hom.app W).hom a) :=
  rfl

/-- The restriction to the small Zariski site of `X` of a derivation of `𝒪_{X_étale}` which
annihilates every function pulled back from an open of `Y`: an ordinary `Y`-derivation of `𝒪_X`
with values in the restriction `ε_* 𝓕` of `𝓕` along the inclusion of the small Zariski site of
`X` into its small étale site. -/
public noncomputable def zariskiRestriction
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    SheafOfModules.SheafDerivation (inverseImageStructureMap f)
      ((restrictModule B X hX).obj F) :=
  SheafOfModules.ofComorphism f (zariskiRestrictionData B hX D) (fun W b => hD W b)

/-- **Stacks 04CS**, the comparison map.  Let `D` be a derivation of `𝒪_{X_étale}` with values
in a sheaf of `𝒪_{X_étale}`-modules `𝓕` which annihilates every function pulled back from an
open of `Y`.  This is the morphism `c'' : (Ω_{X/Y})^a ⟶ 𝓕` of `𝒪_{X_étale}`-modules adjoint,
under the adjunction between the associated-module functor of Stacks 03DU (4) and restriction to
the small Zariski site, to the morphism `c' : Ω_{X/Y} ⟶ ε_* 𝓕` through which the small Zariski
restriction of `D` factors.

At `𝓕 = Ω_{X_étale/Y_étale}` and `D` its universal derivation this is the map the source's proof
calls `c''`. -/
@[stacks 04CS "the comparison map `c'' : (Ω_{X/Y})^a ⟶ 𝓕` of the source's proof, for a
  derivation of `𝒪_{X_étale}` annihilating the functions pulled back from `Y`"]
public noncomputable def differentialsComparison
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    associatedRelativeDifferentials B hX f ⟶ F :=
  ((associatedModuleAdjunction B X hX).homEquiv
      (Scheme.Hom.relativeDifferentials f) F).symm
    ((SheafOfModules.universalDerivation_isUniversal
      (inverseImageStructureMap f)).desc (zariskiRestriction B hX f D hD))

/-- The adjunct of a morphism `(Ω_{X/Y})^a ⟶ 𝓕` carries `d_{X/Y}` to the small Zariski restriction
of `D` exactly when the morphism is the comparison map. -/
private theorem postcomp_adjunct_eq_iff
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0)
    (g : associatedRelativeDifferentials B hX f ⟶ F) :
    (f.universalRelativeDerivation).postcomp
        ((((associatedModuleAdjunction B X hX).homEquiv
          (Scheme.Hom.relativeDifferentials f) F) g)).val =
      zariskiRestriction B hX f D hD ↔ g = differentialsComparison B hX f D hD := by
  have h := SheafOfModules.universalDerivation_isUniversal (inverseImageStructureMap f)
  exact ⟨fun hg => (Equiv.eq_symm_apply _).2 (h.desc_eq _ hg), fun hg => by
    rw [hg, differentialsComparison]
    erw [Equiv.apply_symm_apply]
    exact h.postcomp_desc _⟩

/-- **Stacks 04CS**, compatibility with the universal derivations on the small Zariski site.
The adjunct `c' : Ω_{X/Y} ⟶ ε_* 𝓕` of the comparison map carries the universal derivation
`d_{X/Y}` of `Ω_{X/Y}` to the small Zariski restriction of `D`. -/
@[stacks 04CS "compatibility of the comparison map with the universal derivation `d_{X/Y}` on
  the small Zariski site"]
public theorem differentialsComparison_adjunct
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) :
    (f.universalRelativeDerivation).postcomp
        ((((associatedModuleAdjunction B X hX).homEquiv
          (Scheme.Hom.relativeDifferentials f) F)
            (differentialsComparison B hX f D hD))).val =
      zariskiRestriction B hX f D hD := by
  exact (postcomp_adjunct_eq_iff B hX f D hD _).2 rfl

/-- **Stacks 04CS**, canonicity of the comparison map.  It is the only morphism
`(Ω_{X/Y})^a ⟶ 𝓕` whose adjunct carries the universal derivation `d_{X/Y}` to the small Zariski
restriction of `D`. -/
@[stacks 04CS "canonicity: the comparison map is the unique morphism whose adjunct carries
  `d_{X/Y}` to the small Zariski restriction of the derivation"]
public theorem eq_differentialsComparison
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0)
    (g : associatedRelativeDifferentials B hX f ⟶ F)
    (hg : (f.universalRelativeDerivation).postcomp
        ((((associatedModuleAdjunction B X hX).homEquiv
          (Scheme.Hom.relativeDifferentials f) F) g)).val =
      zariskiRestriction B hX f D hD) :
    g = differentialsComparison B hX f D hD := by
  exact (postcomp_adjunct_eq_iff B hX f D hD g).1 hg

section Naturality

variable {G : SheafOfModules.{u} (structureSheaf B X hX)}

/-- Postcomposing a derivation with a morphism of sheaves of modules preserves the vanishing on
the functions pulled back from `Y`. -/
public theorem postcomp_pullbackSection_eq_zero
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) (α : F ⟶ G)
    (W : Y.Opens) (b : Γ(Y, W)) :
    (D.postcomp α.val).d (pullbackSection B hX f W b) = 0 :=
  Eq.trans (PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply D α.val _)
    (Eq.trans (congrArg _ (hD W b)) (map_zero _))

/-- The small Zariski restriction of a derivation is natural in the coefficient sheaf. -/
public theorem zariskiRestriction_postcomp
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) (α : F ⟶ G) :
    (zariskiRestriction B hX f D hD).postcomp
        (((restrictModule B X hX).map α)).val =
      zariskiRestriction B hX f (D.postcomp α.val)
        (postcomp_pullbackSection_eq_zero B hX f D hD α) := by
  ext W a
  rfl

/-- **Stacks 04CS**, naturality of the comparison map in the coefficient sheaf: the comparison
map of a derivation postcomposed with `α : 𝓕 ⟶ 𝓖` is the comparison map of the derivation
followed by `α`.  So the comparison maps form a natural transformation out of `(Ω_{X/Y})^a`, and
in particular an isomorphism `(Ω_{X/Y})^a ≅ 𝓕` exhibited by one of them is canonical. -/
@[stacks 04CS "naturality of the comparison map in the coefficient sheaf of modules"]
public theorem differentialsComparison_postcomp
    (hD : ∀ (W : Y.Opens) (b : Γ(Y, W)), D.d (pullbackSection B hX f W b) = 0) (α : F ⟶ G) :
    differentialsComparison B hX f (D.postcomp α.val)
        (postcomp_pullbackSection_eq_zero B hX f D hD α) =
      differentialsComparison B hX f D hD ≫ α := by
  refine (eq_differentialsComparison B hX f (D.postcomp α.val)
    (postcomp_pullbackSection_eq_zero B hX f D hD α) _ ?_).symm
  refine Eq.trans (congrArg
    (fun g : Scheme.Hom.relativeDifferentials f ⟶ (restrictModule B X hX).obj G =>
      (f.universalRelativeDerivation).postcomp g.val)
    ((associatedModuleAdjunction B X hX).homEquiv_naturality_right
      (differentialsComparison B hX f D hD) α)) ?_
  refine Eq.trans (SheafOfModules.postcomp_comp_val _ _ _).symm ?_
  refine Eq.trans (congrArg (fun E => E.postcomp (((restrictModule B X hX).map α)).val)
    (differentialsComparison_adjunct B hX f D hD)) ?_
  exact zariskiRestriction_postcomp B hX f D hD α

end Naturality

end AlgebraicGeometry.SmallEtale

end
