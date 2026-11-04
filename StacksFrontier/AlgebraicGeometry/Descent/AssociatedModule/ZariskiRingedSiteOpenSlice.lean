module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSite
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization

/-!
# The slice of a scheme's Zariski ringed site at an open is that open's own Zariski ringed site

Let `X` be a scheme and `V` an open of `X`.  Two ringed sites are attached to `V`:

* `X.zariskiRingedSite.over V`, the localization of Stacks 04IX of the small Zariski ringed site
  of `X` at the object `V`.  Its underlying category is the slice `Over V` of the opens of `X`,
  its topology is the localized topology, and its structure sheaf is the restriction `𝒪_X|_V`,
  whose value at `W ⟶ V` is `𝒪_X(W)`.
* `V.toScheme.zariskiRingedSite`, the small Zariski ringed site of the open subscheme `V`.  Its
  underlying category is the opens of the subspace `V`, with the Zariski topology and the
  structure sheaf of the scheme `V`.

**These are the same ringed site**, and this file says so. The identification is needed because the
two sit on opposite sides of a join: the locality reduction for pseudo-coherence, Stacks 08FU part
(3) (`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`), reduces a statement
about `X` to statements about `X.zariskiRingedSite.over V`, whereas the affine-chart statements
that discharge those — `AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen` and the
vanishing results beside it — are about a *scheme* and an affine open of it, so on an affine `V`
they speak of `V.toScheme.zariskiRingedSite`.

## What is proved

The identification is given in the three layers a consumer needs, and each layer is *stated*
rather than left to a definitional unfolding.

* the **sites**: the two underlying categories are equivalent by Mathlib's
  `TopologicalSpace.Opens.overEquivalence`, and that equivalence is continuous in both
  directions, so the two topologies correspond; the inverse direction is a morphism of sites in
  the sense of Stacks 00X1 (`AlgebraicGeometry.Scheme.zariskiOver_isMorphismOfSites`);
* the **structure sheaf**: `AlgebraicGeometry.Scheme.zariskiOver_pushforward_O`, the direct image
  of `𝒪_X|_V` along that equivalence *is* `𝒪_V`, with `zariskiOver_pushforward_ringSheaf` the
  same for the sheaf of (not necessarily commutative) rings in which sheaves of modules are
  indexed.  Both are equalities, not merely isomorphisms, which is why the structure map of the
  resulting morphism of ringed sites is the identity;
* the **sheaves of modules**: no new construction, and this is the point of stating the second
  layer as an *equality* of sheaves of rings.  Mathlib's
  `AlgebraicGeometry.Scheme.Modules.overEquiv` is an equivalence
  `SheafOfModules (X.ringCatSheaf.over V) ≌ V.toScheme.Modules`, and
  `AlgebraicGeometry.Scheme.zariskiRingedSite_over_ringSheaf` and
  `zariskiRingedSite_toScheme_ringSheaf` say that its two sides *are* the categories of sheaves
  of modules of the two ringed sites, so that it can be used as such with no comparison and no
  second copy of it here.  Its unit compatibility is Mathlib's
  `TopologicalSpace.Opens.sheafOfModulesEquivOverUnit`, readable at the ringed sites for the same
  reason.

## Main definitions

* `AlgebraicGeometry.Scheme.zariskiOverRingedSiteHom`: **the identification**, as a morphism of
  ringed sites `X.zariskiRingedSite.over V ⟶ V.toScheme.zariskiRingedSite` in the sense of
  Stacks 03AD, whose underlying functor is an equivalence of the two sites and whose structure
  map is the identity.

## Main results

* `CategoryTheory.Functor.isMorphismOfSites_of_isEquivalence_sheafPushforwardContinuous`: a
  continuous functor whose direct image on sheaves of sets is an equivalence is a morphism of
  sites.
* `AlgebraicGeometry.Scheme.zariskiOver_pushforward_O` and
  `zariskiOver_pushforward_ringSheaf`: the structure sheaves agree.
* `AlgebraicGeometry.Scheme.zariskiOverRingedSiteHom_u_isEquivalence`: the underlying morphism of
  sites of the identification is an *equivalence* of sites, which is the sense in which the two
  ringed sites are the same and not merely related.
* `AlgebraicGeometry.Scheme.zariskiOver_coversTop`: the opens of the subspace `V`, read as opens
  of `X` lying over `V`, cover the final object of the localized site.  This is what the transfer
  statements of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnExactFunctor`
  ask of the site functor.
* `AlgebraicGeometry.Scheme.zariskiRingedSite_over_ringSheaf` and
  `zariskiRingedSite_toScheme_ringSheaf`: the two sheaves of rings in which sheaves of modules
  are indexed, in the spellings `CategoryTheory.Sheaf.over` and
  `TopologicalSpace.Opens.sheafRestrict` that Mathlib's identification of the two categories of
  sheaves of modules is stated at.
* `AlgebraicGeometry.Scheme.zariskiOver_isContinuous_symm_functor` and
  `zariskiOver_isContinuous_symm_inverse`: the same continuity, in the orientation that the
  transports of sheaves of modules along an equivalence of ringed sites ask for.

## Implementation notes

All three comparisons hold definitionally, and that is a fact about the *presentations* chosen
for the two sides rather than an accident: `TopologicalSpace.Opens.overEquivalence` presents an
open of the subspace `V` as its image in `X` together with the inclusion into `V`, the slice
projection sends `W ⟶ V` to `W`, and `AlgebraicGeometry.Scheme.Opens.toScheme` is
`AlgebraicGeometry.Scheme.restrict` along the open immersion, whose presheaf is the presheaf of
`X` precomposed with the open-image functor.  The three therefore agree on the nose.  They are
nevertheless recorded as declarations, because a consumer that has to *cross* between the two
spellings cannot do so by instance search: `AlgebraicGeometry.RingedSite.ringSheaf` does not
reduce at instance transparency, the same obstruction that forces
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mapDerivedCategory_of_hypotheses` to take its
typeclass hypotheses explicitly.

For the same reason the continuity of the two site functors is restated at the `RingedSite`
spellings of the two topologies. Mathlib's instances are stated at
`TopologicalSpace.Opens.grothendieckTopology` and `CategoryTheory.GrothendieckTopology.over`, and
instance search does not unfold `AlgebraicGeometry.RingedSite.J` of the localization of
`AlgebraicGeometry.Scheme.zariskiRingedSite` to reach them. Everything below is therefore phrased
with the site functors spelled `(TopologicalSpace.Opens.overEquivalence V).functor` and `.inverse`
and not through an abbreviation of them: instance search matches the head of a goal without
unfolding a local abbreviation, so an instance declared at an abbreviated spelling is not found at
the spelled-out one, nor conversely, and one spelling has to be chosen.

**No equivalence of module categories is constructed here.**  Mathlib's
`AlgebraicGeometry.Scheme.Modules.overEquiv`, which is
`TopologicalSpace.Opens.sheafOfModulesEquivOver` of the sheaf of rings of the scheme, already is
one, and it is used throughout this repository; stating a copy of it at the ringed sites would be
a second name for the same equivalence.  What a consumer needs instead is that its two sides are
the module categories of the two ringed sites, and that is the content of the two `ringSheaf`
equalities above.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace CategoryTheory.Functor

/-- **A continuous functor whose direct image on sheaves of sets is an equivalence is a morphism
of sites** in the sense of Stacks 00X1.  The induced functor `u_s` on sheaves of sets is the left
adjoint of that direct image, hence isomorphic to its inverse, hence itself an equivalence and in
particular exact. -/
theorem isMorphismOfSites_of_isEquivalence_sheafPushforwardContinuous {C : Type u}
    [SmallCategory C] {D : Type u} [SmallCategory D] (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [u.IsContinuous J K]
    [(u.sheafPushforwardContinuous (Type u) J K).IsEquivalence] :
    u.IsMorphismOfSites J K := by
  have e : u.sheafPullback (Type u) J K ≅ (u.sheafPushforwardContinuous (Type u) J K).inv :=
    (u.sheafAdjunctionContinuous (Type u) J K).leftAdjointUniq
      (u.sheafPushforwardContinuous (Type u) J K).asEquivalence.symm.toAdjunction
  have : PreservesLimitsOfSize.{u, u} (u.sheafPushforwardContinuous (Type u) J K).inv :=
    (u.sheafPushforwardContinuous (Type u)
      J K).asEquivalence.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (u.sheafPullback (Type u) J K) :=
    preservesFiniteLimits_of_natIso e.symm
  exact { isContinuous := inferInstance
          preservesFiniteLimits := inferInstance
          preservesFiniteColimits := preservesFiniteColimits_sheafPullback u J K }

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (V : X.Opens)

/-! ### The underlying sites

`(TopologicalSpace.Opens.overEquivalence V).functor` sends an open `W` of `X` lying over `V` to
the open `W` of the subspace `V`, and its inverse sends an open of the subspace `V` to its image
in `X`, which lies over `V`.  It is an equivalence of the underlying category of
`X.zariskiRingedSite.over V` with that of `V.toScheme.zariskiRingedSite`. -/

/-- The forward site functor is continuous, stated at the topologies of the two ringed sites. -/
instance zariskiOver_isContinuous_functor :
    (Opens.overEquivalence V).functor.IsContinuous (X.zariskiRingedSite.over V).J
      V.toScheme.zariskiRingedSite.J :=
  inferInstanceAs ((Opens.overEquivalence V).functor.IsContinuous
    ((Opens.grothendieckTopology ↥X).over V) (Opens.grothendieckTopology ↥V))

/-- The inverse site functor is continuous, stated at the topologies of the two ringed sites. -/
instance zariskiOver_isContinuous_inverse :
    (Opens.overEquivalence V).inverse.IsContinuous V.toScheme.zariskiRingedSite.J
      (X.zariskiRingedSite.over V).J :=
  inferInstanceAs ((Opens.overEquivalence V).inverse.IsContinuous
    (Opens.grothendieckTopology ↥V) ((Opens.grothendieckTopology ↥X).over V))

/-- The site equivalence read in the orientation `V.toScheme.zariskiRingedSite.C ≌
(X.zariskiRingedSite.over V).C`, which is the one the transports of sheaves of modules along an
equivalence of ringed sites —
`Stacks.SheafOfModules.reindexEquivalence`, `AlgebraicGeometry.RingedSite.modulesEquiv` and
`Stacks.SheafOfModules.InternalHom.siteEquivModulesOver` — ask for: continuity of the forward
functor.

This is `AlgebraicGeometry.Scheme.zariskiOver_isContinuous_inverse` at the spelling
`(TopologicalSpace.Opens.overEquivalence V).symm.functor`.  It is recorded as its own
declaration, rather than left to instance search at the use site, because at
`X.zariskiRingedSite.over V` — whose object universe is `max u u` and not syntactically `u` —
synthesis of this class inside those transports produces a stuck universe constraint and fails,
so the instance has to be *passed*. -/
instance zariskiOver_isContinuous_symm_functor :
    (Opens.overEquivalence V).symm.functor.IsContinuous V.toScheme.zariskiRingedSite.J
      (X.zariskiRingedSite.over V).J :=
  inferInstanceAs ((Opens.overEquivalence V).inverse.IsContinuous
    (Opens.grothendieckTopology ↥V) ((Opens.grothendieckTopology ↥X).over V))

/-- Continuity of the backward functor in the orientation of
`AlgebraicGeometry.Scheme.zariskiOver_isContinuous_symm_functor`. -/
instance zariskiOver_isContinuous_symm_inverse :
    (Opens.overEquivalence V).symm.inverse.IsContinuous (X.zariskiRingedSite.over V).J
      V.toScheme.zariskiRingedSite.J :=
  inferInstanceAs ((Opens.overEquivalence V).functor.IsContinuous
    ((Opens.grothendieckTopology ↥X).over V) (Opens.grothendieckTopology ↥V))

/-- The direct image of sheaves of sets along the inverse site functor is an equivalence, stated
at the topologies of the two ringed sites. -/
instance zariskiOver_isEquivalence_sheafPushforwardContinuous :
    ((Opens.overEquivalence V).inverse.sheafPushforwardContinuous (Type u)
      V.toScheme.zariskiRingedSite.J (X.zariskiRingedSite.over V).J).IsEquivalence :=
  inferInstanceAs (((Opens.overEquivalence V).inverse.sheafPushforwardContinuous (Type u)
    (Opens.grothendieckTopology ↥V) ((Opens.grothendieckTopology ↥X).over V)).IsEquivalence)

/-- **The inverse site functor is a morphism of sites** in the sense of Stacks 00X1: it is
continuous, and its direct image on sheaves of sets is an equivalence, being one half of an
equivalence of sites which is a dense subsite in both directions. -/
theorem zariskiOver_isMorphismOfSites :
    (Opens.overEquivalence V).inverse.IsMorphismOfSites V.toScheme.zariskiRingedSite.J
      (X.zariskiRingedSite.over V).J :=
  Functor.isMorphismOfSites_of_isEquivalence_sheafPushforwardContinuous _ _ _

/-- **The opens of the subspace `V`, read as opens of `X` lying over `V`, cover the final object
of the localized site.**  Every object of the slice is isomorphic to one of them, so the sieve of
arrows factoring through them is the whole of the maximal sieve.

This is the family of *all* objects of the source site, so nothing is transported and the
general transport of a covering family along an equivalence of sites,
`Stacks.SheafOfModules.SiteTransport.coversTop_functor_obj`, is not needed: it would have to be
fed the fact that every object of the source site covers itself, which is the argument below. -/
theorem zariskiOver_coversTop :
    (X.zariskiRingedSite.over V).J.CoversTop (Opens.overEquivalence V).inverse.obj := by
  intro U
  refine (X.zariskiRingedSite.over V).J.superset_covering ?_
    ((X.zariskiRingedSite.over V).J.top_mem U)
  intro T g _
  exact ⟨(Opens.overEquivalence V).functor.obj T, ⟨(Opens.overEquivalence V).unitIso.hom.app T⟩⟩

/-! ### The structure sheaves -/

/-- **The structure sheaves agree.**  The direct image along the site equivalence of the
restricted structure sheaf `𝒪_X|_V` of the localized ringed site *is* the structure sheaf `𝒪_V`
of the open subscheme: over an open `W` of the subspace `V`, both are `𝒪_X` evaluated at the
image of `W` in `X`. -/
theorem zariskiOver_pushforward_O :
    ((Opens.overEquivalence V).inverse.sheafPushforwardContinuous CommRingCat.{u}
        V.toScheme.zariskiRingedSite.J (X.zariskiRingedSite.over V).J).obj
      (X.zariskiRingedSite.over V).O = V.toScheme.zariskiRingedSite.O := rfl

/-- **The sheaves of rings in which sheaves of modules are indexed agree.**  This is
`AlgebraicGeometry.Scheme.zariskiOver_pushforward_O` with commutativity forgotten. -/
theorem zariskiOver_pushforward_ringSheaf :
    ((Opens.overEquivalence V).inverse.sheafPushforwardContinuous RingCat.{u}
        V.toScheme.zariskiRingedSite.J (X.zariskiRingedSite.over V).J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over V).O) =
        (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O) := rfl

/-- The sheaf of rings of the localized ringed site is the restriction of `X.ringCatSheaf` to the
slice over `V`, in the spelling `CategoryTheory.Sheaf.over` that Mathlib's transport of sheaves
of modules uses. -/
theorem zariskiRingedSite_over_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.zariskiRingedSite.over V).O) =
      X.ringCatSheaf.over V := rfl

/-- The sheaf of rings of the open subscheme `V` is the restriction of `X.ringCatSheaf` to `V`,
in the spelling `TopologicalSpace.Opens.sheafRestrict` that Mathlib's transport of sheaves of
modules uses. -/
theorem zariskiRingedSite_toScheme_ringSheaf :
    (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O) =
      V.sheafRestrict.obj X.ringCatSheaf := rfl

/-! ### The identification, as a morphism of ringed sites -/

/-- **The slice of a scheme's Zariski ringed site at an open is that open's own Zariski ringed
site**, as a morphism of ringed sites in the sense of Stacks 03AD: the underlying functor is the
equivalence of sites `(TopologicalSpace.Opens.overEquivalence V).inverse`, and the structure map
is the identity, the two structure sheaves being equal by
`AlgebraicGeometry.Scheme.zariskiOver_pushforward_O`. -/
noncomputable def zariskiOverRingedSiteHom :
    RingedSite.Hom (X.zariskiRingedSite.over V) V.toScheme.zariskiRingedSite where
  u := (Opens.overEquivalence V).inverse
  isMorphismOfSites := zariskiOver_isMorphismOfSites X V
  fsharp := 𝟙 _

/-- The underlying functor of the identification is the inverse of
`TopologicalSpace.Opens.overEquivalence V`. -/
@[simp]
theorem zariskiOverRingedSiteHom_u :
    (zariskiOverRingedSiteHom X V).u = (Opens.overEquivalence V).inverse := rfl

/-- **The structure map of the identification is the identity.** -/
@[simp]
theorem zariskiOverRingedSiteHom_fsharp :
    (zariskiOverRingedSiteHom X V).fsharp = 𝟙 _ := rfl

/-- **The underlying morphism of sites of the identification is an equivalence of sites.**  This
is the sense in which the two ringed sites are the same ringed site, and not merely related by a
morphism. -/
instance zariskiOverRingedSiteHom_u_isEquivalence :
    (zariskiOverRingedSiteHom X V).u.IsEquivalence :=
  inferInstanceAs (Opens.overEquivalence V).inverse.IsEquivalence

end AlgebraicGeometry.Scheme

end
