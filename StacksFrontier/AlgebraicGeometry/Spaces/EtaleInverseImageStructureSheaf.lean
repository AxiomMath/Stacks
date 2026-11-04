module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The inverse image of the structure sheaf along an étale morphism

Let `h : U ⟶ V` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  The first assertion of Stacks 03LV is that

`h⁻¹𝒪_V = 𝒪_U`,

that is, that the inverse-image form `h⁻¹𝒪_V ⟶ 𝒪_U` of the structure map of Stacks 03G8 is an
isomorphism.  This file proves it, and supplies the resulting isomorphism of sheaves of
commutative rings.

The route is uniqueness of left adjoints, twice.  Restriction of sheaves of sets along small
étale postcomposition with `h` is left adjoint to
`AlgebraicGeometry.Space.smallEtaleDirectImage` by
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`, and that direct image *is* the
direct image of the morphism of small étale topoi `AlgebraicGeometry.Space.smallToposMorphismTypeU`
on the nose, so restriction is also that morphism's inverse image — the content of Stacks 03LQ,
at the universe of the structure rings rather than at `Type (u + 1)`.  Under that identification
the structure map becomes the unit of the restriction adjunction
(`AlgebraicGeometry.Space.structureSharpSet_eq_unit`), whose adjunct is the comparison
isomorphism itself, and a morphism of sheaves of commutative rings that is invertible on
underlying sheaves of sets is invertible.

## Main definitions

* `AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso`: the inverse image of the
  morphism of small étale topoi of an étale morphism, at the universe of the structure rings, is
  restriction along small étale postcomposition.
* `AlgebraicGeometry.Space.etaleInverseImageStructureSheafIso`: the isomorphism
  `h⁻¹𝒪_V ≅ 𝒪_U` of sheaves of commutative rings.

## Main results

* `AlgebraicGeometry.Space.etaleInverseImageStructureSheafIso`: **Stacks 03LV**, the clause
  `h⁻¹𝒪_V = 𝒪_U` read as an isomorphism. That the inverse-image form of the structure map of an
  étale morphism is invertible at all is
  `AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale` of
  `StacksFrontier.AlgebraicGeometry.Spaces.EtaleStructureSheafInverseImage`, imported here.
* `AlgebraicGeometry.Space.etaleInverseImageStructureSheafIso_hom`: the forward map of that
  isomorphism is the inverse-image form of the structure map, so the isomorphism is canonical
  and not a second choice.

## Implementation notes

**What this does not supply.**  Stacks 03LV has three clauses: `h⁻¹𝒪_V = 𝒪_U`, then
`h^*G = h_{small}^{-1}G` for every `𝒪_V`-module `G` — which is the content of the abuse of
notation of Stacks' Equation 03LW, `G|_{U_étale} = h^*G = h_{small}^{-1}G` — and then exactness
of `h^*`.  Only the first is proved here.  The second does **not** follow from it by transport,
for the following reason: `AlgebraicGeometry.Space.modulePullback` is
`Stacks.Sheaves.RingedToposModules.pullbackModules`, whose first factor is
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctor` over
`Stacks.Sheaves.ToposPullback.pullbackRingSheaf` — and that sheaf of rings carries the ring
structure *transported* through the chosen finite products of the sheaf category, so
`pullbackRingSheaf (smallEtaleSetRestriction h hh) (Stacks.SheafOfModules.Tensor.ringSheaf V.O)`
is **not** `Stacks.SheafOfModules.Tensor.ringSheaf U.O`, not even definitionally.  Identifying the
two is a comparison of a transported ring structure with the direct one, and it is what Equation
03LW still owes; the isomorphism below is its structure-sheaf half, and
`Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans` and
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` are the tools it would be built
from.  The third clause is downstream of the second.

**Why the first declaration carries no attribute.**  Stacks 03LQ and the corresponding clause of
Stacks 03LP are already carried by
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` and
`AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso`, at `Type (u + 1)`.  The source
draws no distinction between universes — that distinction is an artefact of this development,
where the structure rings and hence `AlgebraicGeometry.Space.smallEtaleDirectImage` live at
`Type u` — so the restatement below is the same assertion at a second universe and not a
separate one, exactly as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleRestrictionAdjunction.lean` record for the
adjunction it is derived from.

**Elaboration.**  Two rewrites cannot be performed by `rw` against the library lemma and are
performed against an instantiated `have` instead.  `fSharpInverseImage_forget_homEquiv` carries
four `HasSheafCompose` instance arguments which instance search solves here at a spelling the
rewrite's pattern does not match, so it is instantiated at the morphism first; and the two
hom-set bijections in the goal are indexed by `forgetRing.obj 𝒪` on one side and by
`structureSetSheaf` on the other, which are equal by `rfl` but not syntactically, so
`Equiv.symm_apply_apply` is supplied as a term-mode equality whose type is written out in the
goal's own spelling.  No `set_option` appears in this file.

**Universes.**  Everything is at the universe `u` of the structure rings, which is the universe
at which `AlgebraicGeometry.Space.smallEtaleDirectImage`, and hence
`AlgebraicGeometry.Space.structureSharpSet`, exists.

## References

* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS}

/-- **Stacks 03LQ at the universe of the structure rings.**  For an étale morphism
`h : U ⟶ V` of algebraic spaces, the inverse image of the morphism of small étale topoi
`AlgebraicGeometry.Space.smallToposMorphismTypeU` is restriction of sheaves of sets along small
étale postcomposition with `h`:

`G|_{U_étale} = h_{small}^{-1}G`.

`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` is the same assertion for the
morphism of small étale topoi at `Type (u + 1)`.  This is the form that the structure sheaf and
the sheaves of modules see, since both live at the universe of the structure rings.

The direct image of `smallToposMorphismTypeU` is `AlgebraicGeometry.Space.smallEtaleDirectImage`
on the nose, and `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` exhibits small
étale restriction as another left adjoint of it, so the two agree by uniqueness of left
adjoints. -/
noncomputable def smallToposMorphismTypeU_inverseImageIso (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    (smallToposMorphismTypeU B S hS h).inverseImage ≅ smallEtaleSetRestriction B S hS h hh :=
  (smallToposMorphismTypeU B S hS h).adj.leftAdjointUniq
    (smallEtaleSetRestrictionAdjunction B S hS h hh)

/-- **Stacks 03LV, the clause `h⁻¹𝒪_V = 𝒪_U`, as an isomorphism.**  For an étale morphism
`h : U ⟶ V` of algebraic spaces, the inverse image of the structure sheaf of `V` along `h` is
the structure sheaf of `U`, as sheaves of commutative rings on the small étale site of `U`.

This is `AlgebraicGeometry.Space.isIso_fSharpInverseImage_of_isEtale` read as an
isomorphism; its forward
map is the structure map, by `etaleInverseImageStructureSheafIso_hom`, so no choice is made. -/
noncomputable def etaleInverseImageStructureSheafIso (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
        (smallEtaleRingedToposHom B S hS h).toToposHom).obj
        (smallEtaleRingedTopos B S hS V).O ≅
      (smallEtaleRingedTopos B S hS U).O :=
  haveI := isIso_fSharpInverseImage_of_isEtale B S hS h hh
  asIso (smallEtaleRingedToposHom B S hS h).fSharpInverseImage

/-- The forward map of `AlgebraicGeometry.Space.etaleInverseImageStructureSheafIso` is the
inverse-image form of the structure map of Stacks 03G8.  This is what makes that isomorphism the
canonical one of Stacks 03LV rather than an arbitrary one. -/
@[stacks 03LV "the canonical structure map"]
theorem etaleInverseImageStructureSheafIso_hom (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    (etaleInverseImageStructureSheafIso B S hS h hh).hom =
      (smallEtaleRingedToposHom B S hS h).fSharpInverseImage :=
  rfl

end AlgebraicGeometry.Space

end
