module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AssociatedModuleOnCoarserTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcSmallEtaleSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallZariskiStructureSheaf

/-!
# The associated module `Fᵃ` on the small Zariski and small étale sites

[Stacks, Tag 03DU] (4) repeats clause (3) on the small sites `S_Zar` and `S_étale`, which
exist for the two coarsest of the five topologies: a quasi-coherent `𝒪_S`-module `F` gives the
sheaf of `𝒪`-modules `Fᵃ` whose sections over an object `T` of the small site are
`Γ(T, f^* F)`, where `f : T → S` is its structure morphism.  The base ring sheaf is the
structure sheaf of clause (2).

This file builds clause (4) on both small sites.  As in clause (3) the two inputs are already
in the tree and neither is a hypothesis here: [Stacks, Tag 03DT] in the unconditional form
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'`, and continuity of the presenting
functor of the small site for the localized fpqc topology.  No sheafification occurs, so the
sections of `Fᵃ` are literally the ones the source names.

## Main definitions

* `AlgebraicGeometry.SmallZariski.associatedModuleOfSections`: **clause (4) at `τ = Zariski`**,
  `Fᵃ` on `S_Zar`, as a sheaf of modules over `AlgebraicGeometry.SmallZariski.structureSheaf`.
* `AlgebraicGeometry.SmallEtale.associatedModuleOfSections`: **clause (4) at `τ = étale`**,
  `Fᵃ` on `S_étale`, as a sheaf of modules over
  `AlgebraicGeometry.SmallEtale.structureSheaf`.

## Main results

* `AlgebraicGeometry.SmallZariski.isContinuous_toOver`: the presenting functor of the small
  Zariski site is continuous for the localized fpqc topology.
* `AlgebraicGeometry.SmallZariski.isSheaf_associatedPresheaf` and
  `AlgebraicGeometry.SmallEtale.isSheaf_associatedPresheaf'`: the presheaf of pullback sections
  satisfies the sheaf condition on each small site, with no hypothesis.
* `AlgebraicGeometry.SmallZariski.associatedModuleOfSections_presheaf_obj` and its étale
  companion: the sections of `Fᵃ` over an object of the small site are the global sections of
  the pullback of `F`.

## Implementation notes

The construction is `Stacks.EtaleCohomology.associatedModuleOfIsContinuous`, as for the big
sites; only the presenting functor changes.  On the small étale site its continuity hypothesis
is the existing instance `AlgebraicGeometry.SmallEtale.isContinuous_toOver`.  On the small
Zariski site no continuity instance was available — the proof of
`AlgebraicGeometry.isSheaf_smallZariski_of_isSheaf_fpqc` goes through a `private` one — so
`AlgebraicGeometry.SmallZariski.isContinuous_toOver` turns that public restriction statement
back into the instance, which is sound because the statement is universe-polymorphic in the
coefficients: continuity is exactly the assertion that *every* sheaf of types restricts.

The continuity instance is introduced locally with `haveI` at each use rather than left to
instance search.  Search fails here even though the instance is stated at exactly the spelling
of the goal: the quasi-coherence argument of
`Stacks.EtaleCohomology.associatedModuleOfIsContinuous` is still pending when the continuity
argument is synthesized, and `maxSynthPendingDepth` is reached.  Supplying it as a local
instance is the shortest fix that does not rely on the elaborator's instance order.

`AlgebraicGeometry.SmallEtale.isSheaf_associatedPresheaf'` is the primed, hypothesis-free form
of `AlgebraicGeometry.SmallEtale.isSheaf_associatedPresheaf`, whose argument `hP` is the fpqc
sheaf condition for the presheaf of pullback sections read on types — that is [Stacks,
Tag 03DT], now available unconditionally, so the hypothesis is discharged rather than carried.

The name `AlgebraicGeometry.SmallEtale.associatedModule` is already taken, by the *pullback*
of sheaves of modules along the morphism of ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRingedSite.lean:408`).  That
is a different construction: [Stacks, Tag 03DU] (3) and (4) define `Fᵃ` by its sections, while
that one is the pullback.  Hence the `OfSections` suffix here, and hence both constructions
standing side by side rather than one replacing the other.

The identification of the two — [Stacks, Remark 03FH], which rests on [Stacks, Tag 070S] —
**is proved.**  For a quasi-coherent `F` it is
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAssociatedSections.lean:68`),
which is [Stacks, Tag 070S] (2) for an arbitrary big étale site: the pullback `Fᵃ` is the
sections sheaf `(g : T → S) ↦ Γ(T, g⁺F)` of [Stacks, Tag 03DS] on the small étale site.  The two
constructions therefore agree wherever both are defined; what the quasi-coherence hypothesis on
that identification leaves is only that the sections construction here is the one available for
a module which is not quasi-coherent.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presenting functor of the small Zariski site of `S` as a site of schemes over `S` is
continuous for the localized fpqc topology.  Continuity *is* the assertion that every sheaf of
types on the schemes over `S` restricts to a sheaf on the small Zariski site, which is
`AlgebraicGeometry.isSheaf_smallZariski_of_isSheaf_fpqc`. -/
public instance isContinuous_toOver :
    (inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion).IsContinuous
      (topology B S hS) (Scheme.fpqcTopology.{u}.over S) where
  op_comp_isSheaf_of_types P :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (isSheaf_smallZariski_of_isSheaf_fpqc B S hS P.obj P.property)

variable (F : S.Modules) [F.IsQuasicoherent]

/-- **The sheaf condition of [Stacks, Tag 03DU] (4) at `τ = Zariski`.**  The presheaf
`T ↦ Γ(T, f^* F)` of [Stacks, Tag 03DS] satisfies the sheaf condition on the small Zariski site
of `S`: it is an fpqc sheaf on all schemes over `S` by [Stacks, Tag 03DT], and the presenting
functor of the small Zariski site is continuous. -/
@[stacks 03DU "part (4) at τ = Zariski, the sheaf condition for `Fᵃ`"]
public theorem isSheaf_associatedPresheaf :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.associatedPresheaf S F
        (inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion)) :=
  have := isContinuous_toOver B S hS
  Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_isContinuous S F
    (inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion) (topology B S hS)

/-- **[Stacks, Tag 03DU] (4) at `τ = Zariski`.**  The associated module `Fᵃ` of a quasi-coherent
`𝒪_S`-module `F` on the small Zariski site `S_Zar`, as a sheaf of modules over the structure
sheaf of clause (2).  Its sections over an open `T ⊆ S` are the global sections of the pullback
of `F` to `T`, and no sheafification occurs. -/
@[stacks 03DU "part (4) at τ = Zariski"]
public noncomputable def associatedModuleOfSections :
    SheafOfModules.{u} (structureSheaf B S hS) :=
  haveI := isContinuous_toOver B S hS
  Stacks.EtaleCohomology.associatedModuleOfIsContinuous S F
    (inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion) (topology B S hS)

/-- The abelian presheaf underlying `Fᵃ` on the small Zariski site is the restriction of the
presheaf of pullback sections of [Stacks, Tag 03DS]. -/
@[simp]
public theorem associatedModuleOfSections_presheaf :
    (associatedModuleOfSections B S hS F).val.presheaf =
      Stacks.Sites.associatedPresheaf S F
        (inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion) :=
  rfl

/-- **The defining property of `Fᵃ` on `S_Zar`.**  Its sections over an object of the small
Zariski site are the global sections of the pullback of `F` to that open subscheme. -/
public theorem associatedModuleOfSections_presheaf_obj (T : (SmallZariski B S hS)ᵒᵖ) :
    (associatedModuleOfSections B S hS F).val.presheaf.obj T =
      AddCommGrpCat.of
        Γ((Scheme.Modules.pullback
          ((inclusion B S hS ⋙ Over.post (X := (⟨S, hS⟩ : B.Schemes)) B.inclusion).obj
            T.unop).hom).obj F, ⊤) :=
  rfl

end AlgebraicGeometry.SmallZariski

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : S.Modules) [F.IsQuasicoherent]

/-- **The sheaf condition of [Stacks, Tag 03DU] (4) at `τ = étale`, with no hypothesis.**
`AlgebraicGeometry.SmallEtale.isSheaf_associatedPresheaf` with its argument discharged: the fpqc
sheaf condition it asks for is [Stacks, Tag 03DT], which
`AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_fpqc'` proves unconditionally. -/
@[stacks 03DU "part (4) at τ = étale, the sheaf condition for `Fᵃ`"]
public theorem isSheaf_associatedPresheaf' :
    Presheaf.IsSheaf (topology B S hS)
      (Stacks.Sites.associatedPresheaf S F
        (inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion)) :=
  have := isContinuous_toOver B S hS
  Stacks.EtaleCohomology.isSheaf_associatedPresheaf_of_isContinuous S F
    (inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion) (topology B S hS)

/-- **[Stacks, Tag 03DU] (4) at `τ = étale`.**  The associated module `Fᵃ` of a quasi-coherent
`𝒪_S`-module `F` on the small étale site `S_étale`, as a sheaf of modules over the structure
sheaf of clause (2).  Its sections over an object `T` of the site are the global sections of the
pullback of `F` to `T`, and no sheafification occurs.

This is the construction [Stacks, Tag 03DU] (4) performs.  It is not
`AlgebraicGeometry.SmallEtale.associatedModule`, which is the pullback of sheaves of modules
along the morphism of ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)`; the two agree by
[Stacks, Remark 03FH], which for quasi-coherent `F` is
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheaf`. -/
@[stacks 03DU "part (4) at τ = étale"]
public noncomputable def associatedModuleOfSections :
    SheafOfModules.{u} (structureSheaf B S hS) :=
  haveI := isContinuous_toOver B S hS
  Stacks.EtaleCohomology.associatedModuleOfIsContinuous S F
    (inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion) (topology B S hS)

/-- The abelian presheaf underlying `Fᵃ` on the small étale site is the restriction of the
presheaf of pullback sections of [Stacks, Tag 03DS]. -/
@[simp]
public theorem associatedModuleOfSections_presheaf :
    (associatedModuleOfSections B S hS F).val.presheaf =
      Stacks.Sites.associatedPresheaf S F
        (inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion) :=
  rfl

/-- **The defining property of `Fᵃ` on `S_étale`.**  Its sections over an object of the small
étale site are the global sections of the pullback of `F` to it. -/
public theorem associatedModuleOfSections_presheaf_obj (T : (SmallEtale B S hS)ᵒᵖ) :
    (associatedModuleOfSections B S hS F).val.presheaf.obj T =
      AddCommGrpCat.of
        Γ((Scheme.Modules.pullback
          ((inclusion B S hS ⋙ Over.post (X := B.obj S hS) B.inclusion).obj T.unop).hom).obj
            F, ⊤) :=
  rfl

end AlgebraicGeometry.SmallEtale

end
