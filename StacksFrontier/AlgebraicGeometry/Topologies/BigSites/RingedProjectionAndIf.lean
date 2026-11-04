module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiRingedSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiToBig
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.CompositionGeneral
public import StacksCore.Tactic.StacksAttribute

/-!
# `π_S` as a morphism of ringed sites, and `i_f^{-1}𝒪 = 𝒪`

Two further clauses of Stacks 070R.

The first is the projection `π_S : (\Sch/S)_τ ⟶ S_τ` for `τ ∈ \{Zar, \etale\}`, one of the
generators of the change-of-topologies list of Topologies, Section 03FE — items (24) and (25) of
that list at `f = \mathrm{id}`, and a factor of items (16)–(24).  It is given by the continuous
functor in the opposite direction, the inclusion of the small site into the big one, and the
structure-sheaf homomorphism `π_S^♯` is the *identity*: the structure sheaf of either site is
`T ↦ Γ(T, 𝒪_T)`, and the inclusion is compatible with the underlying-scheme functors on the
nose, so restricting the big structure sheaf along it returns the small one.

The second is the clause of the remark about the morphism of topoi
`i_f : \mathrm{Sh}(T_τ) ⟶ \mathrm{Sh}((\Sch/S)_τ)` of Topologies, Lemmas 020Y and 021F: that it
becomes a morphism of ringed topoi, *because* `i_f^{-1}𝒪 = 𝒪`.  The inverse image of `i_f` is
restriction along the functor `V/T ↦ V/S` presenting it, by the inverse-image formula of those
two lemmas, and the identity `i_f^{-1}𝒪 = 𝒪` is then the statement that the two structure
sheaves are given by the same formula — which is what is proved here, for both topologies.

## Main definitions

* `AlgebraicGeometry.smallZariskiPiRingedSiteHom` and
  `AlgebraicGeometry.smallEtalePiRingedSiteHom`: `π_S` as a morphism of ringed sites.

## Main results

* `AlgebraicGeometry.smallZariskiInclusion_isMorphismOfSites_ringUniverse` and
  `AlgebraicGeometry.smallEtaleInclusion_isMorphismOfSites_ringUniverse`: the inclusion of the
  small site into the big one defines a morphism of sites at the universe of the structure
  rings.
* `AlgebraicGeometry.smallZariskiPiStructureSharp_eq_id` and
  `AlgebraicGeometry.smallEtalePiStructureSharp_eq_id`: `π_S^♯` is the identity.
* `AlgebraicGeometry.smallZariskiToBig_structureSheaf` and
  `AlgebraicGeometry.smallEtaleToBig_structureSheaf`: **`i_f^{-1}𝒪 = 𝒪`**, in the form
  "restricting the structure sheaf of the big `τ`-site over `S` along the functor presenting
  `i_f` returns the structure sheaf of the small `τ`-site of `T`".

## Implementation notes

The site conditions are at the universe of the sections of the structure sheaves, which is what
a morphism of ringed sites reads and which the `Type (u + 1)` statements
(`AlgebraicGeometry.smallEtaleInclusion_isMorphismOfSites`, Stacks 021G) do not give.  They come
from `isMorphismOfSites_of_essentiallySmall`, whose inputs are the continuity and left exactness
of the inclusions (Stacks 020Z and 021G) together with essential smallness of the two sites.

`i_f^{-1}𝒪 = 𝒪` is stated as an equality of sheaves of commutative rings and holds by `rfl`.
The reason is structural: the functor presenting `i_f` is `CategoryTheory.Over.map f` after the
small-site inclusion, and `Over.map` leaves the total space of an object untouched, so the
composite of that functor with the underlying-scheme functor of the big site over `S` *is* the
underlying-scheme functor of the small site of `T`. Both structure sheaves are global functions
on the underlying scheme, so restriction along the functor returns the other one with no
comparison map in between.

Only the identity `i_f^{-1}𝒪 = 𝒪` is stated here; the bundled morphisms of *ringed topoi*
`AlgebraicGeometry.smallZariskiToBigZariskiRingedToposHom` and
`AlgebraicGeometry.smallEtaleToBigEtaleRingedToposHom` use these two identities as their
structure maps.  They need `i_f` at the universe of the sections of the structure sheaves —
`AlgebraicGeometry.smallZariskiToBigZariskiMorphism` and
`AlgebraicGeometry.smallEtaleToBigEtaleMorphism` are geometric morphisms of the topoi of sheaves
of sets in `Type (u + 1)`, the universe of the objects of the sites, whereas an
`AlgebraicGeometry.RingedTopos` declares its underlying topos at the universe of the sections of
its structure sheaf — and supplying it there is the cocontinuous-functor analogue of
`isMorphismOfSites_of_essentiallySmall`, namely
`CategoryTheory.Functor.morphismOfTopoi_of_isCocontinuous`.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 020Y](https://stacks.math.columbia.edu/tag/020Y)
* [Stacks Project, Tag 020Z](https://stacks.math.columbia.edu/tag/020Z)
* [Stacks Project, Tag 021F](https://stacks.math.columbia.edu/tag/021F)
* [Stacks Project, Tag 021G](https://stacks.math.columbia.edu/tag/021G)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### The small Zariski site -/

section Zariski

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-- The inclusion of the small Zariski site of `S` into the big Zariski site over `S` defines a
morphism of sites for sheaves of sets valued in the universe of the sections of the structure
sheaves. -/
@[stacks 020Z "the morphism of sites, at the universe of the structure rings"]
public instance smallZariskiInclusion_isMorphismOfSites_ringUniverse :
    IsMorphismOfSites.{u} (SmallZariski.inclusion B S.1 S.property)
      (SmallZariski.topology B S.1 S.property) (BigZariskiOver.topology B S.1 S.property) :=
  have : EssentiallySmall.{u} (BigZariskiOver B S.1 S.property) :=
    essentiallySmall_overBase (τ := .zariski) B S.1 S.property
  have : RepresentablyFlat (SmallZariski.inclusion B S.1 S.property) :=
    flat_of_preservesFiniteLimits _
  isMorphismOfSites_of_essentiallySmall _ _ _

/-- The projection `π_S : (\Sch/S)_{Zar} ⟶ S_{Zar}` of Topologies, Lemma 020Z, as a morphism of
ringed sites

```
  (π_S, π_S^♯) : ((\Sch/S)_{Zar}, 𝒪) ⟶ (S_{Zar}, 𝒪).
```

Its structure map is the identity, by
`AlgebraicGeometry.smallZariskiPiStructureSharp_eq_id`. -/
@[stacks 070R "`π_S` on the Zariski sites, as a morphism of ringed sites"]
public noncomputable def smallZariskiPiRingedSiteHom :
    RingedSite.HomGeneral (bigSiteRingedSite (τ := .zariski) B S.1 S.property)
      (smallZariskiRingedSite B S.1 S.property) :=
  ChangeOfSites.ringedSiteHom (SmallZariski.topology B S.1 S.property)
    (BigZariskiOver.topology B S.1 S.property) (smallSiteInSchemesOver B S)
    (bigSiteToOver (τ := .zariski) B S.1 S.property)
    (SmallZariski.inclusion B S.1 S.property)
    (smallZariskiInclusion_isMorphismOfSites_ringUniverse B) (𝟙 _)
    (SmallZariski.structure_isSheaf B S.1 S.property)
    (bigSite_structure_isSheaf (τ := .zariski) B S.1 S.property)

/-- The continuous functor underlying `π_S` on the Zariski sites is the inclusion of the small
Zariski site of `S` into the big Zariski site over `S`. -/
@[simp]
public theorem smallZariskiPiRingedSiteHom_u :
    (smallZariskiPiRingedSiteHom B (S := S)).u = SmallZariski.inclusion B S.1 S.property := rfl

/-- **The structure map of `π_S` is the identity.**  Both structure sheaves are global functions
on the underlying scheme, and the inclusion of the small site into the big one is compatible
with the two underlying-scheme functors on the nose, so no comparison map intervenes. -/
@[stacks 070R "`π_S^♯` is the identity on the Zariski sites"]
public theorem smallZariskiPiStructureSharp_eq_id :
    (smallZariskiPiRingedSiteHom B (S := S)).fsharp = 𝟙 _ := rfl

/-- **`i_f^{-1}𝒪 = 𝒪` for the Zariski sites.**  Restricting the structure sheaf of the big
Zariski site over `S` along the functor `V/T ↦ V/S` which presents the morphism of topoi
`i_f : \mathrm{Sh}(T_{Zar}) ⟶ \mathrm{Sh}((\Sch/S)_{Zar})` of Topologies, Lemma 020Y returns the
structure sheaf of the small Zariski site of `T`.

By the inverse-image formula of that lemma the inverse image of `i_f` is that restriction, so
this is the identity `i_f^{-1}𝒪 = 𝒪` which the remark gives as the reason `i_f` becomes a
morphism of ringed topoi. -/
@[stacks 070R "the identity `i_f^{-1}𝒪 = 𝒪` for the big and small Zariski sites"]
public theorem smallZariskiToBig_structureSheaf :
    ((smallZariskiToBigZariskiFunctor B T S f).sheafPushforwardContinuous CommRingCat.{u}
          (SmallZariski.topology B T.1 T.property)
          (BigZariskiOver.topology B S.1 S.property)).obj
        (bigSiteRingedSite (τ := .zariski) B S.1 S.property).O =
      (smallZariskiRingedSite B T.1 T.property).O := rfl

end Zariski

/-! ### The small étale site -/

section Etale

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

/-- The inclusion of the small étale site of `S` into the big étale site over `S` preserves
finite limits: it preserves the terminal object and fibre products. -/
public instance preservesFiniteLimits_smallEtaleInclusion :
    PreservesFiniteLimits (SmallEtale.inclusion B S.obj S.property) :=
  have : PreservesLimitsOfShape (Discrete.{0} PEmpty)
      (SmallEtale.inclusion B S.obj S.property) :=
    preservesLimitsOfShape_pempty_of_preservesTerminal _
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- The inclusion of the small étale site of `S` into the big étale site over `S` defines a
morphism of sites for sheaves of sets valued in the universe of the sections of the structure
sheaves.

`AlgebraicGeometry.smallEtaleInclusion_isMorphismOfSites` is the same assertion for sheaves of
sets in `Type (u + 1)`, the universe of the objects of the sites; neither implies the other. -/
@[stacks 021G "the morphism of sites, at the universe of the structure rings"]
public instance smallEtaleInclusion_isMorphismOfSites_ringUniverse :
    IsMorphismOfSites.{u} (SmallEtale.inclusion B S.obj S.property)
      (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property) :=
  have : EssentiallySmall.{u} (BigEtaleOver B S.obj S.property) :=
    essentiallySmall_overBase (τ := .etale) B S.obj S.property
  have : RepresentablyFlat (SmallEtale.inclusion B S.obj S.property) :=
    flat_of_preservesFiniteLimits _
  isMorphismOfSites_of_essentiallySmall _ _ _

/-- The projection `π_S : (\Sch/S)_\etale ⟶ S_\etale` of Topologies, Lemma 021G, as a morphism
of ringed sites

```
  (π_S, π_S^♯) : ((\Sch/S)_\etale, 𝒪) ⟶ (S_\etale, 𝒪).
```

Its structure map is the identity, by
`AlgebraicGeometry.smallEtalePiStructureSharp_eq_id`. -/
@[stacks 070R "`π_S` on the étale sites, as a morphism of ringed sites"]
public noncomputable def smallEtalePiRingedSiteHom :
    RingedSite.HomGeneral (bigSiteRingedSite (τ := .etale) B S.obj S.property)
      (smallEtaleRingedSite B S.obj S.property) :=
  ChangeOfSites.ringedSiteHom (SmallEtale.topology B S.obj S.property)
    (BigEtaleOver.topology B S.obj S.property)
    (SmallEtale.inclusion B S.obj S.property ⋙ Over.post B.inclusion)
    (bigSiteToOver (τ := .etale) B S.obj S.property)
    (SmallEtale.inclusion B S.obj S.property)
    (smallEtaleInclusion_isMorphismOfSites_ringUniverse B) (𝟙 _)
    (SmallEtale.structure_isSheaf B S.obj S.property)
    (bigSite_structure_isSheaf (τ := .etale) B S.obj S.property)

/-- The continuous functor underlying `π_S` on the étale sites is the inclusion of the small
étale site of `S` into the big étale site over `S`. -/
@[simp]
public theorem smallEtalePiRingedSiteHom_u :
    (smallEtalePiRingedSiteHom B (S := S)).u = SmallEtale.inclusion B S.obj S.property := rfl

/-- **The structure map of `π_S` is the identity**, for the same reason as on the Zariski
sites. -/
@[stacks 070R "`π_S^♯` is the identity on the étale sites"]
public theorem smallEtalePiStructureSharp_eq_id :
    (smallEtalePiRingedSiteHom B (S := S)).fsharp = 𝟙 _ := rfl

/-- **`i_f^{-1}𝒪 = 𝒪` for the étale sites.**  Restricting the structure sheaf of the big étale
site over `S` along the functor `V/T ↦ V/S` which presents the morphism of topoi
`i_f : \mathrm{Sh}(T_\etale) ⟶ \mathrm{Sh}((\Sch/S)_\etale)` of Topologies, Lemma 021F returns
the structure sheaf of the small étale site of `T`. -/
@[stacks 070R "the identity `i_f^{-1}𝒪 = 𝒪` for the big and small étale sites"]
public theorem smallEtaleToBig_structureSheaf :
    ((smallEtaleToBigEtaleFunctor B T S f).sheafPushforwardContinuous CommRingCat.{u}
          (SmallEtale.topology B T.obj T.property)
          (BigEtaleOver.topology B S.obj S.property)).obj
        (bigSiteRingedSite (τ := .etale) B S.obj S.property).O =
      (smallEtaleRingedSite B T.obj T.property).O := rfl

end Etale

end AlgebraicGeometry

end
