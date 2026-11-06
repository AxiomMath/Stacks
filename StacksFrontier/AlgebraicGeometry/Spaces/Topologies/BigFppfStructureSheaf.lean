module

public import StacksFrontier.AlgebraicGeometry.Spaces.FppfMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfSite

/-!
# The structure sheaf on the big fppf site of an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `X` one of its objects.
The value at an algebraic space `U` over `S` of the structure presheaf of the big fppf site is
the ring `Γ(U, 𝒪_U)` of global regular functions on `U`, with pullback of regular functions as
its restriction maps. This file proves that the big fppf topology of algebraic spaces is
subcanonical, deduces that the presheaf of global regular functions is a sheaf for it, and
packages the result as a sheaf of rings on the big fppf site of `X`.

Subcanonicity is descent of morphisms of algebraic spaces along an fppf covering, which is the
fppf case of Stacks 04P2 and holds for an arbitrary algebraic space target; no representability
of the target and no input from Stacks 0APL is needed. The structure sheaf is then the presheaf
represented by the affine line over `S`, through the identification of global regular functions
on an algebraic space with its morphisms to the affine line.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.structurePresheaf` and
  `AlgebraicGeometry.BigFppfSpaceSite.structureSheaf`: the structure presheaf and the structure
  sheaf of rings on the big fppf site of an object `X` of `T`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isSheaf_yoneda` and
  `AlgebraicGeometry.BigFppfSpaceSite.topology_subcanonical`: the big fppf topology of algebraic
  spaces over `S` is subcanonical.
* `AlgebraicGeometry.BigFppfSpaceSite.globalFunctionsPresheaf_isSheaf` and
  `AlgebraicGeometry.BigFppfSpaceSite.structurePresheaf_isSheaf`: global regular functions
  satisfy fppf descent.

## Implementation notes

Nothing here carries a Stacks attribute: the statements proved are the fppf counterparts of the
big étale structure sheaf of Stacks 0DF9, a remark of Chapter 73. The declarations mirror
`AlgebraicGeometry.BigEtaleSpaceSite.globalFunctionsPresheaf_isSheaf` and its companions, and
reuse the affine-line description of global regular functions built there; only the descent
input differs, and the fppf one is stronger.

The four declarations `structurePresheaf_obj`, `structurePresheaf_map`, `structureSheaf_obj`
and `structureSheaf_map` are the rewriting interface a ringed-site comparison needs.

## References

* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 0DBW](https://stacks.math.columbia.edu/tag/0DBW)
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site of `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf :
    HasPullbacks ((BigFppfOver T.schemeSite S T.scheme_mem)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf
    {X Y Z : (BigFppfOver T.schemeSite S T.scheme_mem)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The big fppf topology is subcanonical -/

/-- A presheaf represented by an algebraic space satisfies the sheaf condition for an fppf
covering family of algebraic spaces. -/
private theorem isSheafFor_yoneda_of_fppfCovering
    {I : Type v} {Y : T.Spaces} (Xi : I → T.Spaces) (f : ∀ i, Xi i ⟶ Y)
    (hf : Space.IsFppfCovering T.schemeSite S T.scheme_mem
      (fun i => (Xi i).obj) (fun i => (f i).hom))
    (Z : T.Spaces) :
    Presieve.IsSheafFor (yoneda.obj Z) (Presieve.ofArrows Xi f) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact AlgebraicSpaces.existsUnique_desc_of_isFppfCovering T.schemeSite S T.scheme_mem f hf
    Z x fun i j W α β hαβ => hx i j W α β hαβ

/-- The big fppf topology of algebraic spaces over `S` is subcanonical: the presheaf
represented by an algebraic space is a sheaf. -/
theorem isSheaf_yoneda (Z : T.Spaces) : Presieve.IsSheaf T.topology (yoneda.obj Z) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y g R hR
  obtain ⟨E, rfl, hE⟩ := hR
  let P (i : E.I₀) := AlgebraicSpaces.fiberProduct T.schemeSite S T.scheme_mem g (E.f i)
  let p (i : E.I₀) : P i ⟶ Y := ObjectProperty.homMk (pullback.fst g.hom (E.f i).hom)
  let q (i : E.I₀) : P i ⟶ E.X i := ObjectProperty.homMk (pullback.snd g.hom (E.f i).hom)
  have hp (i : E.I₀) : IsPullback (p i) (q i) g (E.f i) :=
    AlgebraicSpaces.isPullback_fiberProduct T.schemeSite S T.scheme_mem g (E.f i)
  rw [← Sieve.ofArrows_eq_pullback_of_isPullback E.f hp]
  exact (Presieve.isSheafFor_iff_generate (Presieve.ofArrows P p)).1 <|
    isSheafFor_yoneda_of_fppfCovering T P p
      (Space.isFppfCovering_fibreProduct T.schemeSite S T.scheme_mem E.X E.f g hE.fppf) Z

/-- The big fppf topology of algebraic spaces over `S` is subcanonical. -/
instance topology_subcanonical : T.topology.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ (isSheaf_yoneda T)

/-! ### The structure sheaf -/

/-- The presheaf of global regular functions on algebraic spaces over `S` is a sheaf for the
big fppf topology: it is the presheaf represented by the affine line. -/
theorem globalFunctionsPresheaf_isSheaf :
    Presheaf.IsSheaf T.topology
      (Space.globalFunctionsPresheaf T.schemeSite S T.scheme_mem) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget T.topology
    (Space.globalFunctionsPresheaf T.schemeSite S T.scheme_mem) (forget CommRingCat.{u + 1})).2
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  apply (Presieve.isSheaf_iff_of_nat_equiv
    (P₂ := yoneda.obj (Space.affineLineSpace T.schemeSite S T.scheme_mem))
    (fun {U} => Space.globalFunctionsHomEquiv T.schemeSite S T.scheme_mem U)
    (fun {U V} f s =>
      Space.globalFunctionsHomEquiv_natural T.schemeSite S T.scheme_mem f s)).2
  exact isSheaf_yoneda T _

/-- The structure presheaf on the big fppf site of `X`: its value on an algebraic space `U`
over `X` is the ring of global regular functions on `U`. -/
noncomputable abbrev structurePresheaf (X : T.Spaces) :
    (BigFppfSpaceOver T X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (Over.forget X).op ⋙ Space.globalFunctionsPresheaf T.schemeSite S T.scheme_mem

/-- The value of the structure presheaf on `U ⟶ X` is the ring of global sections of the small
étale structure sheaf of `U`. -/
@[simp] theorem structurePresheaf_obj (X : T.Spaces) (U : (BigFppfSpaceOver T X)ᵒᵖ) :
    (structurePresheaf T X).obj U =
      CommRingCat.of (Space.globalFunctions' T.schemeSite S T.scheme_mem U.unop.left.obj) :=
  rfl

/-- Restriction on the big fppf site is pullback of global regular functions. -/
@[simp] theorem structurePresheaf_map (X : T.Spaces)
    {U V : (BigFppfSpaceOver T X)ᵒᵖ} (f : U ⟶ V) :
    (structurePresheaf T X).map f =
      CommRingCat.ofHom
        (Space.globalFunctionsMap T.schemeSite S T.scheme_mem f.unop.left) :=
  rfl

/-- Global regular functions satisfy fppf descent on the big fppf site of `X`. -/
theorem structurePresheaf_isSheaf (X : T.Spaces) :
    Presheaf.IsSheaf (BigFppfSpaceOver.topology T X) (structurePresheaf T X) :=
  (Over.forget X).op_comp_isSheaf_of_isSheaf
    (T.topology.over X) T.topology _ (globalFunctionsPresheaf_isSheaf T)

/-- The structure sheaf of rings on the big fppf site of `X`. -/
noncomputable def structureSheaf (X : T.Spaces) :
    Sheaf (BigFppfSpaceOver.topology T X) CommRingCat.{u + 1} :=
  ⟨structurePresheaf T X, structurePresheaf_isSheaf T X⟩

/-- The value of the structure sheaf on an object of the big fppf site. -/
@[simp] theorem structureSheaf_obj (X : T.Spaces) (U : (BigFppfSpaceOver T X)ᵒᵖ) :
    (structureSheaf T X).obj.obj U =
      CommRingCat.of (Space.globalFunctions' T.schemeSite S T.scheme_mem U.unop.left.obj) :=
  rfl

/-- The restriction maps of the structure sheaf. -/
@[simp] theorem structureSheaf_map (X : T.Spaces)
    {U V : (BigFppfSpaceOver T X)ᵒᵖ} (f : U ⟶ V) :
    (structureSheaf T X).obj.map f =
      CommRingCat.ofHom
        (Space.globalFunctionsMap T.schemeSite S T.scheme_mem f.unop.left) :=
  rfl

end AlgebraicGeometry.BigFppfSpaceSite

end
