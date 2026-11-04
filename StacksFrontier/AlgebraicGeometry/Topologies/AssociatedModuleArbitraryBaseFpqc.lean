module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleArbitraryBase
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcCoveringSiteSheaves

/-!
# Descent, Lemma 0GN7 over an arbitrary base, on a site whose coverings are fpqc coverings

Let `C` be a site of schemes over `S`, presented by a precoverage `K` and a functor
`toOver : C ⥤ Over S`, whose covering families become fpqc covering families of schemes. On such a
site the presheaf of morphisms of pullbacks of two quasi-coherent modules and the associated
presheaf of a quasi-coherent module are sheaves, so Descent, Lemma 0GN7 holds over `S` without
assuming `S` affine.

## Main results

* `Stacks.Sites.isPrestackOver_of_mem_fpqcPrecoverage`: `Stacks.Sites.IsPrestackOver` holds on
  such a site.
* `Stacks.Sites.bijective_associatedModuleMap_of_mem_fpqcPrecoverage`: **Descent, Lemma 0GN7 over
  an arbitrary base on such a site** — the map `φ ↦ φᵃ` is bijective on morphisms of quasi-coherent
  modules.
* `Stacks.Sites.full_associatedModuleFunctor_of_mem_fpqcPrecoverage` and
  `Stacks.Sites.faithful_associatedModuleFunctor_of_mem_fpqcPrecoverage`: the same as fullness and
  faithfulness of `Stacks.Sites.associatedModuleFunctor`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

namespace Stacks.Sites

variable {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C] {S : Scheme.{u}}
  (K : Precoverage C) (toOver : C ⥤ Over S)
  [PreservesLimitsOfShape WalkingCospan (toOver ⋙ Over.forget S)]
  [K.HasPullbacks] [K.IsStableUnderBaseChange]

/-- **The descent property for morphisms of pullbacks of quasi-coherent modules holds on a site
of schemes over `S` whose coverings are fpqc coverings of schemes.** -/
public theorem isPrestackOver_of_mem_fpqcPrecoverage
    (hfpqc : ∀ ⦃T : C⦄ (R : Presieve T), R ∈ K T →
      Presieve.map (toOver ⋙ Over.forget S) R ∈
        Scheme.fpqcPrecoverage.{u} ((toOver ⋙ Over.forget S).obj T)) :
    IsPrestackOver S toOver K.toGrothendieck :=
  fun M N _ _ => isSheaf_presheafHom_toOver_of_mem_fpqcPrecoverage K toOver hfpqc M N

/-- On a site of schemes over `S` whose coverings are fpqc coverings of schemes, the map
`φ ↦ φᵃ` is bijective on morphisms of quasi-coherent modules on `S`, with **no affineness
assumption on `S`**, as soon as the arrows factoring through an object with affine underlying
scheme cover every object and the site contains an object `X₀` with invertible structure morphism
receiving a morphism from every object. -/
@[stacks 0GN7 "the lemma over a base that is NOT assumed affine, on a site of schemes over S \
presented by a precoverage K and a functor toOver : C -> Over S. The two registrations that stood \
before this one are at particular sites and neither covers this presentation: \
Stacks.Descent.fullyFaithfulAssociatedModuleQcoh' is the small site at a topology tau \
(StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleLocalBijectivity.lean:717) and Stacks.Descent.fullyFaithfulBaseAssociatedModuleQcoh is \
the big site (Sch/S)_tau (StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseFullyFaithful.lean:211); the abstract presentation has neither the \
objScheme/objRestrict apparatus of the second nor a functor out of S.Opens as the first uses, so \
neither transfers. WHAT IS REMOVED relative to the affine-base case \
Stacks.Sites.bijective_associatedModuleMap is exactly IsAffine S, and nothing else: both sheaf \
conditions of bijective_associatedModuleMap_of_isPrestack are discharged here, the presheaf of \
morphisms by isPrestackOver_of_mem_fpqcPrecoverage and the associated presheaf by \
isSheaf_associatedPresheaf_of_mem_fpqcPrecoverage, the latter being the SECOND assertion of \
Stacks 03OJ. CARRIED: hcover, that the arrows factoring through an object with affine underlying \
scheme cover every object. That is a real hypothesis and not a restatement of the conclusion, but \
it is NOT supplied by condition (2) of Stacks 03OJ -- condition (2) yields covering only at the \
class Stacks.Sites.OverAffineOpen, of objects whose structure morphism has image inside an affine \
open, and at that class the local half of this lemma is BLOCKED: the required agreement of two \
Gamma(T,O)-linear maps on all of Gamma(g^+M, top) needs \
AlgebraicGeometry.Scheme.Modules.span_range_pullbackSection_eq_top at W = top, which needs T \
affine, and that file's own documentation records that both of its affineness hypotheses are \
needed and that the statement is false for U affine and V arbitrary. So hcover at the AFFINE \
class is what this form asks for, and supplying it from Stacks 03OJ's conditions is the open \
problem that the third assertion of that tag now rests on. The full and faithful forms of this \
clause are full_ and faithful_associatedModuleFunctor_of_mem_fpqcPrecoverage below"]
public theorem bijective_associatedModuleMap_of_mem_fpqcPrecoverage
    (hfpqc : ∀ ⦃T : C⦄ (R : Presieve T), R ∈ K T →
      Presieve.map (toOver ⋙ Over.forget S) R ∈
        Scheme.fpqcPrecoverage.{u} ((toOver ⋙ Over.forget S).obj T))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ K.toGrothendieck X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀))
    (M N : S.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  bijective_associatedModuleMap_of_isPrestack S toOver K.toGrothendieck
    (isSheaf_presheafHom_toOver_of_mem_fpqcPrecoverage K toOver hfpqc M N)
    (isSheaf_associatedPresheaf_of_mem_fpqcPrecoverage K toOver hfpqc N) hcover X₀ hterm

/-- On a site of schemes over `S` whose coverings are fpqc coverings of schemes, the functor
`Stacks.Sites.associatedModuleFunctor S toOver` is faithful as soon as the arrows factoring
through an object with affine underlying scheme cover every object and the site contains an
object `X₀` with invertible structure morphism. -/
public theorem faithful_associatedModuleFunctor_of_mem_fpqcPrecoverage
    (hfpqc : ∀ ⦃T : C⦄ (R : Presieve T), R ∈ K T →
      Presieve.map (toOver ⋙ Over.forget S) R ∈
        Scheme.fpqcPrecoverage.{u} ((toOver ⋙ Over.forget S).obj T))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ K.toGrothendieck X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] :
    (associatedModuleFunctor S toOver).Faithful :=
  faithful_associatedModuleFunctor_of_isPrestack S toOver K.toGrothendieck
    (isPrestackOver_of_mem_fpqcPrecoverage K toOver hfpqc) hcover X₀

/-- On a site of schemes over `S` whose coverings are fpqc coverings of schemes, the functor
`Stacks.Sites.associatedModuleFunctor S toOver` is full as soon as the arrows factoring through an
object with affine underlying scheme cover every object and the site contains an object `X₀` with
invertible structure morphism receiving a morphism from every object. -/
public theorem full_associatedModuleFunctor_of_mem_fpqcPrecoverage
    (hfpqc : ∀ ⦃T : C⦄ (R : Presieve T), R ∈ K T →
      Presieve.map (toOver ⋙ Over.forget S) R ∈
        Scheme.fpqcPrecoverage.{u} ((toOver ⋙ Over.forget S).obj T))
    (hcover : ∀ X : C, Sieve.coverByImage
      (ObjectProperty.ι (fun Y : C ↦ IsAffine (toOver.obj Y).left)) X ∈ K.toGrothendieck X)
    (X₀ : C) [IsIso (toOver.obj X₀).hom] (hterm : ∀ X : C, Nonempty (X ⟶ X₀)) :
    (associatedModuleFunctor S toOver).Full :=
  full_associatedModuleFunctor_of_isPrestack S toOver K.toGrothendieck
    (isPrestackOver_of_mem_fpqcPrecoverage K toOver hfpqc)
    (fun M _ => isSheaf_associatedPresheaf_of_mem_fpqcPrecoverage K toOver hfpqc M)
    hcover X₀ hterm

end Stacks.Sites

end
