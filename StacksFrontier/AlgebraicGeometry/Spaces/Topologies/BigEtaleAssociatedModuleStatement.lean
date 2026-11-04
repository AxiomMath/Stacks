module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAssociatedModuleFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAssociatedModulePullbackEquivalence

/-!
# Stacks 0DGN: quasi-coherent modules on the big sites of an algebraic space

Let `S` be a scheme, `X` an algebraic space over `S` and `𝓕` a quasi-coherent `𝒪_X`-module.
Stacks 0DGN makes seven assertions about the rule `𝓕ᵃ : (f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)` of
`AlgebraicGeometry.Space.associatedPresheaf`.  This file records where each of them is proved and
registers the tag on the declarations stating clauses (2) to (7) and the a fortiori cases of
clause (1).

1. **The sheaf condition.**  `𝓕ᵃ` satisfies the sheaf condition for every fpqc covering of an
   object of `(Spaces/X)_étale`:
   `AlgebraicGeometry.Space.isSheafFor_associatedPresheaf_of_isFpqcCovering`, registered in
   `StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigEtaleAssociatedModuleFpqcSheaf.lean`.  A
   fortiori `𝓕ᵃ` is a sheaf on `(Spaces/X)_étale` and on `(Spaces/X)_fppf`:
   `AlgebraicGeometry.BigEtaleSpaceSite.isSheaf_associatedPresheaf` and
   `AlgebraicGeometry.BigFppfSpaceSite.isSheaf_associatedPresheaf`, read off here from clauses (2)
   and (3).
2. `𝓕ᵃ = π_X^*𝓕` on `(Spaces/X)_étale`:
   `AlgebraicGeometry.BigEtaleSpaceSite.associatedPresheafIsoPullback`.
3. `𝓕ᵃ = a_X^*𝓕` on `(Spaces/X)_fppf`:
   `AlgebraicGeometry.BigFppfSpaceSite.nonempty_associatedPresheaf_iso_pullback`.
4. `𝓕 ↦ 𝓕ᵃ = π_X^*𝓕` is an equivalence `QCoh(𝒪_X) ≌ QCoh((Spaces/X)_étale, 𝒪)`:
   `AlgebraicGeometry.BigEtaleSpaceSite.quasicoherentPullbackEquivalence`.
5. `𝓕 ↦ 𝓕ᵃ = a_X^*𝓕` is an equivalence `QCoh(𝒪_X) ≌ QCoh((Spaces/X)_fppf, 𝒪)`:
   `AlgebraicGeometry.BigFppfSpaceSite.quasicoherentPullbackEquivalence`.
6. `ε_{X,*}a_X^*𝓕 = π_X^*𝓕` and `a_{X,*}a_X^*𝓕 = 𝓕`:
   `AlgebraicGeometry.BigFppfSpaceSite.pushforward_pullback_of_quasicoherent`.
7. `R^iε_{X,*}(a_X^*𝓕) = 0` and `R^ia_{X,*}(a_X^*𝓕) = 0` for `i > 0`:
   `AlgebraicGeometry.BigFppfSpaceSite.isZero_rightDerived_pushforward_pullback_of_quasicoherent`.

## Implementation notes

`𝓕ᵃ` is formed for `𝒪_X`-modules on the small étale site of `X` (étale scheme charts), whose
sections lie in `Type u`.  Clauses (2) and (3) compare it with `π_X^*` and `a_X^*` of the same
module read on the spaces-étale site through the comparison `ι` of Stacks 03G1
(`AlgebraicGeometry.Space.toSpacesEtaleModules`), which is fully faithful.  Clauses (4) to (7)
are statements about `π_X^*`, `a_X^*` and their direct images, and are stated, as the comparison
morphisms are, for `𝒪_X`-modules on the spaces-étale site with sections in `Type (u + 1)`: the
quasi-coherent modules on the big sites need not have `u`-small sections, so the equivalences of
clauses (4) and (5) are between categories of that size.  By clauses (2) and (3) the functors of
those equivalences are the rule `𝓕 ↦ 𝓕ᵃ`.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The rule `𝓕ᵃ` is a sheaf on `(Spaces/X)_étale`** (the étale case of Stacks 0DGN,
clause (1)).  For a quasi-coherent `𝒪_X`-module `𝓕` on an algebraic space `X` of a big étale
site, the rule `𝓕ᵃ : (f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)` is a sheaf of
abelian groups on the big étale site of `X`: it is isomorphic to the underlying presheaf of the
sheaf of modules `π_X^*𝓕` (clause (2)). -/
@[stacks 0DGN "(1), a fortiori for étale coverings: 𝓕ᵃ is a sheaf on (Spaces/X)_étale, for \
𝓕 a quasi-coherent 𝒪_X-module; the fpqc sheaf condition is \
Space.isSheafFor_associatedPresheaf_of_isFpqcCovering"]
theorem BigEtaleSpaceSite.isSheaf_associatedPresheaf {S : Scheme.{u}} (T : BigEtaleSpaceSite S)
    (X : T.Spaces) (F : Space.Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2)
    [F.IsQuasicoherentOnSite] :
    Presheaf.IsSheaf (T.bigEtaleTopology X) (T.associatedPresheaf X F) :=
  (Presheaf.isSheaf_of_iso_iff (T.associatedPresheafIsoPullback X F)).2
    ((BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos
      |>.obj ((Space.toSpacesEtaleModules T.fppfSite S T.fppf_mem X).obj F)).isSheaf

/-- **The rule `𝓕ᵃ` is a sheaf on `(Spaces/X)_fppf`** (the fppf case of Stacks 0DGN,
clause (1)).  For a quasi-coherent `𝒪_X`-module `𝓕` on an algebraic space `X` of a big fppf
site, the rule `𝓕ᵃ : (f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)` is a sheaf of
abelian groups on the big fppf site of `X`: it is isomorphic to the underlying presheaf of the
sheaf of modules `a_X^*𝓕` (clause (3)). -/
@[stacks 0DGN "(1), a fortiori for fppf coverings: 𝓕ᵃ is a sheaf on (Spaces/X)_fppf, for \
𝓕 a quasi-coherent 𝒪_X-module; the fpqc sheaf condition is \
Space.isSheafFor_associatedPresheaf_of_isFpqcCovering"]
theorem BigFppfSpaceSite.isSheaf_associatedPresheaf {S : Scheme.{u}} (T : BigFppfSpaceSite S)
    (X : T.Spaces) (F : Space.Modules.{u, u} T.schemeSite S T.scheme_mem X.1 X.2)
    [F.IsQuasicoherentOnSite] :
    Presheaf.IsSheaf (BigFppfSpaceOver.topology T X) (Space.associatedPresheaf F) :=
  (Presheaf.isSheaf_of_iso_iff (T.nonempty_associatedPresheaf_iso_pullback X F).some).2
    ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj
      ((Space.toSpacesEtaleModules T.schemeSite S T.scheme_mem X).obj F)).isSheaf

add_to_stacks 0DGN "(2): 𝓕ᵃ ≅ π_X^*𝓕 on (Spaces/X)_étale, for 𝓕 a quasi-coherent \
𝒪_X-module read on the spaces-étale site through ι"
  BigEtaleSpaceSite.associatedPresheafIsoPullback

add_to_stacks 0DGN "(3): 𝓕ᵃ ≅ a_X^*𝓕 on (Spaces/X)_fppf, for 𝓕 a quasi-coherent \
𝒪_X-module read on the spaces-étale site through ι"
  BigFppfSpaceSite.nonempty_associatedPresheaf_iso_pullback

add_to_stacks 0DGN "(4): 𝓕 ↦ 𝓕ᵃ = π_X^*𝓕 is an equivalence between quasi-coherent \
𝒪_X-modules and quasi-coherent modules on ((Spaces/X)_étale, 𝒪), with quasi-inverse π_{X,*}"
  BigEtaleSpaceSite.quasicoherentPullbackEquivalence

add_to_stacks 0DGN "(5): 𝓕 ↦ 𝓕ᵃ = a_X^*𝓕 is an equivalence between quasi-coherent \
𝒪_X-modules and quasi-coherent modules on ((Spaces/X)_fppf, 𝒪), with quasi-inverse a_{X,*}"
  BigFppfSpaceSite.quasicoherentPullbackEquivalence

add_to_stacks 0DGN "(6): ε_{X,*}a_X^*𝓕 ≅ π_X^*𝓕 and 𝓕 ≅ a_{X,*}a_X^*𝓕 (the unit is an \
isomorphism) for 𝓕 a quasi-coherent 𝒪_X-module"
  BigFppfSpaceSite.pushforward_pullback_of_quasicoherent

add_to_stacks 0DGN "(7): R^i ε_{X,*}(a_X^*𝓕) = 0 and R^i a_{X,*}(a_X^*𝓕) = 0 for i > 0 and \
𝓕 a quasi-coherent 𝒪_X-module"
  BigFppfSpaceSite.isZero_rightDerived_pushforward_pullback_of_quasicoherent

end AlgebraicGeometry

end
