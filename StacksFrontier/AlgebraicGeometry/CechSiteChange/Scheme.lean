module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Affine
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Lattice

/-!
# The Čech complex of an affine open cover, transported from `Over X` to `X.Opens`

[Stacks, Tag 01XL] forms its Čech complexes over the site `Over X`, for the family
`Over.mk (T.f i)` attached to an affine open cover `T` of `X`.  [Stacks, Tag 02FU] — the statement
that such a complex is a resolution — is proved in this repository over the site of *open sets* of
the underlying space.  This file bridges the two sites, by instantiating the general change-of-site
isomorphism of `StacksDraft.AlgebraicGeometry.F3.CechSiteChange.Basic` at the functor

`opensOver X : X.Opens ⥤ Over X`,  `V ↦ Over.mk V.ι`.

The point is that this functor **preserves finite products**: the fibre product over `X` of
finitely many open subschemes is the intersection of the open sets.  Since every object in the
image has a monomorphism as structure morphism, both the factorisation and the uniqueness in the
universal property are instances of
`Stacks.AlgebraicGeometry.RelativeCechComplex.over_hom_unique`, so no pullback is ever computed.

## Main results

* `Stacks.CechSiteChange.opensOver`: the functor above.
* `Stacks.CechSiteChange.isLimitOpensOverMapCone` and
  `Stacks.CechSiteChange.preservesFiniteProducts_opensOver`: **`opensOver X` preserves finite
  products.**
* `Stacks.CechSiteChange.overMkIsoOpensOver`: an open immersion into `X` is isomorphic, as an
  object over `X`, to its open range.
* `Stacks.CechSiteChange.cechComplexFunctorAffineOpenCoverIso`: **the Čech complex over `Over X`
  of the family of an affine open cover is the Čech complex over `X.Opens` of the family of its
  ranges**, with coefficients restricted along `opensOver X`, naturally in the coefficient
  presheaf.

## Implementation notes

The product of a family `V : J → X.Opens` in `X.Opens` is its infimum, and the corresponding fan
is a limit because the morphisms of a lattice between a fixed pair of objects form a subsingleton.
Its image under `opensOver X` is a limit because of `over_hom_unique`; the lift is
`AlgebraicGeometry.IsOpenImmersion.lift` of the structure morphism of the vertex of the competing
fan, whose range lies in every `V j` by
`Stacks.AlgebraicGeometry.RelativeCechComplex.range_comp_subset` and therefore in the infimum.
Finiteness of the index type is used in exactly one place, `range_subset_iInf`: the underlying set
of an infimum of open sets is the intersection of the underlying sets only for a finite family
(in general it is its interior).

`overMkIsoOpensOver` is also built from `over_hom_unique`: the two objects have monomorphic
structure morphisms with the same range, so the two `IsOpenImmersion.lift`s are mutually inverse
with no computation.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace Stacks.CechSiteChange

open Stacks.AlgebraicGeometry.RelativeCechComplex

variable (X : Scheme.{u})

/-! ### Open subschemes as objects over `X` -/

/-- **The open sets of `X`, as objects over `X`.**  An open set `V` goes to the open immersion
`V.ι : V ⟶ X`, and an inclusion to the induced morphism of open subschemes.  Functoriality is
automatic: the structure morphisms are monomorphisms, so there is at most one morphism into
`Over.mk V.ι` from anywhere. -/
noncomputable def opensOver : X.Opens ⥤ Over X where
  obj V := Over.mk V.ι
  map h := Over.homMk (X.homOfLE (leOfHom h)) (X.homOfLE_ι _)
  map_id V := over_hom_unique (inferInstanceAs (Mono V.ι)) _ _
  map_comp {_ _ W} _ _ := over_hom_unique (inferInstanceAs (Mono W.ι)) _ _

/-- `opensOver X` sends an open set `V` to the open immersion `V.ι : V ⟶ X` over `X`. -/
@[simp]
theorem opensOver_obj (V : X.Opens) : (opensOver X).obj V = Over.mk V.ι := rfl

/-- The structure morphism of an object in the image of `opensOver` is a monomorphism. -/
theorem mono_opensOver_hom (V : X.Opens) : Mono ((opensOver X).obj V).hom :=
  inferInstanceAs (Mono V.ι)

/-- The structure morphism of an object in the image of `opensOver` is an open immersion. -/
theorem isOpenImmersion_opensOver_hom (V : X.Opens) :
    IsOpenImmersion ((opensOver X).obj V).hom :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-! ### `opensOver` preserves finite products -/

variable {J : Type*} (V : J → X.Opens)

/-- The infimum of a family of open sets, named so that the instance
`IsOpenImmersion (iInfOpens X V).ι` is found: `Scheme.Opens` is a `def`, and instance search does
not see through the `⨅` notation to it. -/
def iInfOpens : X.Opens := ⨅ j, V j

/-- The infimum is below every member of the family. -/
theorem iInfOpens_le (j : J) : iInfOpens X V ≤ V j := iInf_le V j

/-- The fan of a family of open sets with vertex their infimum. -/
def iInfFan : Fan V :=
  Fan.mk (iInfOpens X V) (fun j ↦ homOfLE (iInfOpens_le X V j))

/-- **The infimum is the product in the lattice of open sets.**  Both conditions of the universal
property are `Subsingleton.elim`, the lattice of open sets being a thin category. -/
def isLimitIInfFan : IsLimit (iInfFan X V) :=
  Fan.IsLimit.mk _ (fun s ↦ homOfLE (le_iInf fun j ↦ leOfHom (s.proj j)))
    (fun _ _ ↦ Subsingleton.elim _ _) (fun _ _ _ ↦ Subsingleton.elim _ _)

variable [Finite J]

/-- The structure morphism of the vertex of a fan over the image family has range inside every
member of the family, hence inside their infimum.  Finiteness of the index type enters here and
only here: the underlying set of an infimum of open sets is the intersection only for a finite
family. -/
theorem range_subset_iInf (s : Cone (Discrete.functor V ⋙ opensOver X)) :
    Set.range s.pt.hom ⊆ Set.range (iInfOpens X V).ι := by
  rw [Scheme.Opens.range_ι, iInfOpens, TopologicalSpace.Opens.coe_iInf]
  refine Set.subset_iInter fun j ↦ ?_
  rw [← Scheme.Opens.range_ι (V j)]
  exact range_comp_subset (s.π.app ⟨j⟩)

/-- The morphism from the vertex of a fan over the image family to the image of the infimum.  Both
the infimum and the target are written out — `iInfOpens` rather than `⨅`, and `Over.mk _.ι` rather
than `(opensOver X).obj _` — which is what makes the instance `IsOpenImmersion (iInfOpens X V).ι`
available.  `Scheme.Opens` is a `def`, so the instance is found when the expected type names the
open set and not otherwise. -/
noncomputable def opensOverFanLift (s : Cone (Discrete.functor V ⋙ opensOver X)) :
    s.pt ⟶ Over.mk (iInfOpens X V).ι :=
  Over.homMk (IsOpenImmersion.lift (iInfOpens X V).ι s.pt.hom (range_subset_iInf X V s))
    (IsOpenImmersion.lift_fac _ _ _)

/-- **`opensOver X` takes the infimum fan of a finite family of open sets to a product.**  The
lift is `opensOverFanLift`; both the factorisation and the uniqueness hold because every object
involved has a monomorphism as structure morphism. -/
noncomputable def isLimitOpensOverMapCone :
    IsLimit ((opensOver X).mapCone (iInfFan X V)) where
  lift := opensOverFanLift X V
  fac _ j := over_hom_unique (inferInstanceAs (Mono (V j.as).ι)) _ _
  uniq _ _ _ := over_hom_unique
    (A := Over.mk (iInfOpens X V).ι) (inferInstanceAs (Mono (iInfOpens X V).ι)) _ _

/-- `opensOver X` preserves the product of any finite family of open sets. -/
theorem preservesLimit_opensOver :
    PreservesLimit (Discrete.functor V) (opensOver X) :=
  preservesLimit_of_preserves_limit_cone (isLimitIInfFan X V) (isLimitOpensOverMapCone X V)

/-- **`opensOver X` preserves finite products** — the hypothesis of the change-of-site
isomorphism for Čech complexes. -/
instance preservesFiniteProducts_opensOver : PreservesFiniteProducts (opensOver X) where
  preserves n :=
    haveI : ∀ W : Fin n → X.Opens, PreservesLimit (Discrete.functor W) (opensOver X) :=
      fun W ↦ preservesLimit_opensOver X W
    preservesLimitsOfShape_of_discrete _

/-! ### An open immersion is its open range -/

variable {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- An open immersion factors through its open range. -/
noncomputable def toOpensRangeOver : Over.mk f ⟶ Over.mk f.opensRange.ι :=
  Over.homMk (IsOpenImmersion.lift f.opensRange.ι f
    (by rw [Scheme.Opens.range_ι]; exact subset_rfl)) (IsOpenImmersion.lift_fac _ _ _)

/-- The open range of an open immersion factors through it. -/
noncomputable def fromOpensRangeOver : Over.mk f.opensRange.ι ⟶ Over.mk f :=
  Over.homMk (IsOpenImmersion.lift f f.opensRange.ι
    (by rw [Scheme.Opens.range_ι]; exact subset_rfl)) (IsOpenImmersion.lift_fac _ _ _)

/-- **An open immersion into `X` is its open range, as an object over `X`.**  Both objects have a
monomorphism as structure morphism and the two structure morphisms have the same range, so the two
factorisations are mutually inverse by `over_hom_unique`. -/
noncomputable def overMkIsoOpensOver : Over.mk f ≅ Over.mk f.opensRange.ι where
  hom := toOpensRangeOver X f
  inv := fromOpensRangeOver X f
  hom_inv_id := over_hom_unique (A := Over.mk f) (inferInstanceAs (Mono f)) _ _
  inv_hom_id := over_hom_unique
    (A := Over.mk f.opensRange.ι) (inferInstanceAs (Mono f.opensRange.ι)) _ _

/-! ### The Čech complex of an affine open cover, over the site of open sets -/

variable {A : Type*} [Category* A] [HasProducts.{u} A] [Preadditive A]

/-- **The Čech complex of [Stacks, Tag 01XL] lives over the site of open sets.**  For an affine
open cover `T` of `X`, the Čech complex over `Over X` of the family `Over.mk (T.f i)` — the
complex of [Stacks, Tag 01XL] — is the Čech complex over `X.Opens` of the family of the open
ranges of the `T.f i`, with coefficients restricted along `opensOver X`, naturally in the
coefficient presheaf.

The restricted coefficient presheaf is `(opensOver X).op ⋙ P`, whose value at an open set `V` is
the value of `P` at `Over.mk V.ι`; for `P` the absolute Čech coefficient presheaf of
[Stacks, Tag 01XL] that value is `(V.ι)_* (V.ι)^* ℱ`. -/
noncomputable def cechComplexFunctorAffineOpenCoverIso (T : X.AffineOpenCover.{u, u}) :
    cechComplexFunctor (A := A) (fun i ↦ Over.mk (T.f i)) ≅
      (Functor.whiskeringLeft (X.Opens)ᵒᵖ (Over X)ᵒᵖ A).obj (opensOver X).op ⋙
        cechComplexFunctor (A := A) (fun i ↦ (T.f i).opensRange) :=
  cechComplexFunctorIsoOfFamilyIso (A := A) (fun i ↦ overMkIsoOpensOver X (T.f i)) ≪≫
    cechComplexFunctorSiteIso (A := A) (opensOver X) (fun i ↦ (T.f i).opensRange)

end Stacks.CechSiteChange
