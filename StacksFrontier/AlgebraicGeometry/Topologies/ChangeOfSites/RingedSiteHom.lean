module

public import StacksFrontier.AlgebraicGeometry.Descent.BigFppfRingedMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineRingedToposEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral
public import StacksCore.Tactic.StacksAttribute

/-!
# Change of topologies as a morphism of ringed sites

Stacks 070R says that every morphism of sites `f_sites` of the change-of-topologies list of
Topologies, Section 03FE becomes a morphism of *ringed* sites once both sites carry their sheaf
of global functions.  The content of that assertion is uniform in the two sites: each of those
morphisms of sites is given by the continuous functor `S'/S ↦ T ×_S S'/T`, and the
structure-sheaf homomorphism is always

```
  f_sites^♯ : 𝒪(S'/S) ⟶ f_{sites, *}𝒪(S'/S) = 𝒪(T ×_S S'/T),
```

the usual map `pr_{S'}^♯ : 𝒪(S') ⟶ 𝒪(T ×_S S')` on global functions.

This file states that once, for an arbitrary pair of sites of schemes presented as in
Stacks 03DU by functors `toOver : C ⥤ Over S` and `toOver' : D ⥤ Over T` recording the
structure morphism of each object.  Nothing here is particular to a topology: the five big and
two small sites of the list, and every composite of them, instantiate the same declarations.

## Main definitions

* `AlgebraicGeometry.ChangeOfSites.ringedSite`: a site of schemes over `S`, together with its
  sheaf of global functions, as a ringed site in the sense of Stacks 03AD.
* `AlgebraicGeometry.ChangeOfSites.structureSharp`: the structure-sheaf homomorphism
  `f_sites^♯` of a continuous functor between two such sites, given the projections
  `T ×_S S' ⟶ S'` of the underlying schemes.
* `AlgebraicGeometry.ChangeOfSites.structureSharpOfBaseChange`: the same for a functor
  exhibited as scheme-theoretic base change, where the projections are the ones of the fibre
  product.
* `AlgebraicGeometry.ChangeOfSites.ringedSiteHom` and
  `AlgebraicGeometry.ChangeOfSites.ringedSiteHomOfBaseChange`: the pair
  `(f_sites, f_sites^♯)` as a morphism of ringed sites.

## Main results

* `AlgebraicGeometry.ChangeOfSites.structureSharp_hom_app`: on an object `S'/S` the
  structure-sheaf homomorphism is the map on global functions induced by the projection.

## Implementation notes

The two sites are presented by `toOver`, not by a functor to `Scheme`, because that is what
determines the structure presheaf `Stacks.Sites.structurePresheaf`, and because the datum that
the continuous functor *is* base change is a compatibility of the two presentations over the
morphism `f : T ⟶ S` of base schemes.

Only the composites `toOver ⋙ Over.forget S` of the two presentations enter the
structure-sheaf homomorphism, so its input is the natural transformation of those composites
given by the projections; `structureSharpOfBaseChange` builds that transformation out of a
base-change identification and `CategoryTheory.Over.pullbackForget`.  Stating it this way
keeps the construction available for the morphisms of the list that are *not* literally a
slice pullback — the small sites, whose base-change functor agrees with the fibre product only
up to the canonical isomorphism of chosen pullbacks.

Structure sheaves are taken in `CommRingCat`, as `AlgebraicGeometry.RingedSite` requires;
`AlgebraicGeometry.commStructureSheaf` turns the ring-valued sheaf condition of Stacks 03DU
into the commutative-ring-valued one without reproving anything.

The bundled form is `AlgebraicGeometry.RingedSite.HomGeneral` rather than
`AlgebraicGeometry.RingedSite.Hom`: the sites of schemes have their objects one universe above
their morphisms, and `Hom` is typeable only when the two agree.  Its site condition is the
universe-general `IsMorphismOfSites` read at the universe of the sections of the structure
sheaves, which is the universe at which the underlying topos of a ringed topos is declared.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ChangeOfSites

variable {S T : Scheme.{u}} {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)}
  [Category.{u} D]

/-- A site of schemes over `S`, presented as in Stacks 03DU by a functor `toOver` recording the
structure morphism of each object, together with its sheaf of global functions, as a ringed site
in the sense of Stacks 03AD. -/
public noncomputable def ringedSite (S : Scheme.{u}) (J : GrothendieckTopology C)
    (toOver : C ⥤ Over S)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver)) :
    RingedSite.{u + 1, u, u} where
  C := C
  J := J
  O := commStructureSheaf S J toOver hJ

/-- The structure sheaf of `ringedSite S J toOver hJ` is the sheaf of global functions
`commStructureSheaf S J toOver hJ`. -/
@[simp]
public theorem ringedSite_O (S : Scheme.{u}) (J : GrothendieckTopology C) (toOver : C ⥤ Over S)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver)) :
    (ringedSite S J toOver hJ).O = commStructureSheaf S J toOver hJ := rfl

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (toOver : C ⥤ Over S)
  (toOver' : D ⥤ Over T) (F : C ⥤ D)

/-- **Stacks 070R.**  The structure-sheaf homomorphism `f_sites^♯ : 𝒪 ⟶ f_{sites, *}𝒪` of a
change-of-topologies morphism of sites.

Here `F` is the continuous functor representing `f_sites`, in the direction opposite to it, and
`p` is the family of projections `T ×_S S' ⟶ S'` of underlying schemes, natural in the object
`S'` of the target site.  The homomorphism is pullback of global functions along `p`. -/
@[stacks 070R "the structure-sheaf homomorphism `f_sites^♯` of a change-of-topologies morphism"]
public noncomputable def structureSharp [F.IsContinuous J K]
    (p : F ⋙ toOver' ⋙ Over.forget T ⟶ toOver ⋙ Over.forget S)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) :
    commStructureSheaf S J toOver hJ ⟶
      (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
        (commStructureSheaf T K toOver' hK) :=
  ⟨Functor.whiskerRight (NatTrans.op p) Scheme.Γ⟩

/-- On an object `S'/S` of the target site the structure-sheaf homomorphism is the map on
global functions induced by the projection `T ×_S S' ⟶ S'`. -/
@[simp]
public theorem structureSharp_hom_app [F.IsContinuous J K]
    (p : F ⋙ toOver' ⋙ Over.forget T ⟶ toOver ⋙ Over.forget S)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) (X : C) :
    (structureSharp J K toOver toOver' F p hJ hK).hom.app (op X) =
      Scheme.Γ.map (op (p.app X)) := rfl

/-- The projections of a functor between sites of schemes exhibited as scheme-theoretic base
change along `f : T ⟶ S`: at an object `S'/S` of the target site the projection is
`pr_{S'} : T ×_S S' ⟶ S'`. -/
public noncomputable def baseChangeProjections (f : T ⟶ S)
    (bc : F ⋙ toOver' ≅ toOver ⋙ Over.pullback f) :
    F ⋙ toOver' ⋙ Over.forget T ⟶ toOver ⋙ Over.forget S :=
  Functor.whiskerRight bc.hom (Over.forget T) ≫
    Functor.whiskerLeft toOver (Over.pullbackForget f)

/-- At an object `X` of the target site, the base-change projection is the comparison
isomorphism `bc` at `X` followed by the first projection of the fibre product. -/
@[simp]
public theorem baseChangeProjections_app (f : T ⟶ S)
    (bc : F ⋙ toOver' ≅ toOver ⋙ Over.pullback f) (X : C) :
    (baseChangeProjections toOver toOver' F f bc).app X =
      (bc.hom.app X).left ≫ pullback.fst (toOver.obj X).hom f := rfl

/-- **Stacks 070R.**  The structure-sheaf homomorphism of a change-of-topologies morphism of
sites whose continuous functor is exhibited as scheme-theoretic base change along
`f : T ⟶ S`: on an object `S'/S` it is the usual map
`pr_{S'}^♯ : 𝒪(S') ⟶ 𝒪(T ×_S S')`. -/
@[stacks 070R "`f_sites^♯` for a functor exhibited as base change along `f : T ⟶ S`"]
public noncomputable def structureSharpOfBaseChange [F.IsContinuous J K] (f : T ⟶ S)
    (bc : F ⋙ toOver' ≅ toOver ⋙ Over.pullback f)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) :
    commStructureSheaf S J toOver hJ ⟶
      (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
        (commStructureSheaf T K toOver' hK) :=
  structureSharp J K toOver toOver' F (baseChangeProjections toOver toOver' F f bc) hJ hK

/-- On an object `S'/S` of the target site the structure-sheaf homomorphism of a base-change
morphism of sites is the map on global functions induced by `pr_{S'} : T ×_S S' ⟶ S'`. -/
@[simp]
public theorem structureSharpOfBaseChange_hom_app [F.IsContinuous J K] (f : T ⟶ S)
    (bc : F ⋙ toOver' ≅ toOver ⋙ Over.pullback f)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) (X : C) :
    (structureSharpOfBaseChange J K toOver toOver' F f bc hJ hK).hom.app (op X) =
      Scheme.Γ.map (op ((bc.hom.app X).left ≫ pullback.fst (toOver.obj X).hom f)) := rfl

/-- **Stacks 070R.**  A change-of-topologies morphism of sites, together with its
structure-sheaf homomorphism, is a morphism of ringed sites

```
  (f_sites, f_sites^♯) : ((Sch/T)_τ, 𝒪_T) ⟶ ((Sch/S)_{τ'}, 𝒪_S)
```

in the sense of Stacks 03AD. -/
@[stacks 070R "a change-of-topologies morphism of sites is one of ringed sites"]
public noncomputable def ringedSiteHom (hF : IsMorphismOfSites.{u} F J K)
    (p : F ⋙ toOver' ⋙ Over.forget T ⟶ toOver ⋙ Over.forget S)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) :
    RingedSite.HomGeneral (ringedSite T K toOver' hK) (ringedSite S J toOver hJ) :=
  letI : F.IsContinuous J K := hF.toIsContinuous
  { u := F
    isMorphismOfSites := hF
    fsharp := structureSharp J K toOver toOver' F p hJ hK }

/-- The underlying functor of `ringedSiteHom` is `F`. -/
@[simp]
public theorem ringedSiteHom_u (hF : IsMorphismOfSites.{u} F J K)
    (p : F ⋙ toOver' ⋙ Over.forget T ⟶ toOver ⋙ Over.forget S)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) :
    (ringedSiteHom J K toOver toOver' F hF p hJ hK).u = F := rfl

/-- The structure-sheaf homomorphism of `ringedSiteHom` is `structureSharp`. -/
public theorem ringedSiteHom_fsharp (hF : IsMorphismOfSites.{u} F J K)
    (p : F ⋙ toOver' ⋙ Over.forget T ⟶ toOver ⋙ Over.forget S)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) :
    letI : F.IsContinuous J K := hF.toIsContinuous
    (ringedSiteHom J K toOver toOver' F hF p hJ hK).fsharp =
      structureSharp J K toOver toOver' F p hJ hK := rfl

/-- **Stacks 070R.**  The same, for a continuous functor exhibited as scheme-theoretic base
change along `f : T ⟶ S`, which is the form every morphism of the change-of-topologies list
takes. -/
@[stacks 070R "the morphism of ringed sites of a base-change morphism of sites"]
public noncomputable def ringedSiteHomOfBaseChange (hF : IsMorphismOfSites.{u} F J K)
    (f : T ⟶ S) (bc : F ⋙ toOver' ≅ toOver ⋙ Over.pullback f)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) :
    RingedSite.HomGeneral (ringedSite T K toOver' hK) (ringedSite S J toOver hJ) :=
  ringedSiteHom J K toOver toOver' F hF (baseChangeProjections toOver toOver' F f bc) hJ hK

/-- The underlying functor of `ringedSiteHomOfBaseChange` is `F`. -/
@[simp]
public theorem ringedSiteHomOfBaseChange_u (hF : IsMorphismOfSites.{u} F J K) (f : T ⟶ S)
    (bc : F ⋙ toOver' ≅ toOver ⋙ Over.pullback f)
    (hJ : Presheaf.IsSheaf J (Stacks.Sites.structurePresheaf S toOver))
    (hK : Presheaf.IsSheaf K (Stacks.Sites.structurePresheaf T toOver')) :
    (ringedSiteHomOfBaseChange J K toOver toOver' F hF f bc hJ hK).u = F := rfl

end AlgebraicGeometry.ChangeOfSites

end
