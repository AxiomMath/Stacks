module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHomOfRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedProjectionAndIf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiRingedSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiToBig
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.CocontinuousSmallModel
public import StacksCore.Tactic.StacksAttribute

/-!
# `i_f` as a morphism of ringed topoi

Stacks 070R: "Similarly, the morphism `i_f : \mathrm{Sh}(T_τ) ⟶ \mathrm{Sh}((\Sch/S)_τ)` for
`τ ∈ \{Zar, \etale\}`, see Topologies, Lemmas 020Y and 021F, becomes a morphism of ringed topoi
because `i_f^{-1}𝒪 = 𝒪`."

This file carries out both halves of that sentence, for both topologies.

`i_f` is presented by the functor `V/T ↦ V/S` from the small `τ`-site of `T` to the big
`τ`-site over `S`, which is cocontinuous (Stacks 020Y, 021F) *and* continuous.  The library's
morphism of topoi is at `Type (u + 1)`, the universe of the objects of the sites; a
`AlgebraicGeometry.RingedTopos` declares its topos at the universe of the sections of its
structure sheaf, which here is `u`.  `CategoryTheory.Functor.morphismOfTopoi_of_isCocontinuous`
supplies `i_f` there, and because that construction takes *restriction* as the inverse image —
which Stacks 00XR (1) identifies with the sheafified pullback — the identity `i_f^{-1}𝒪 = 𝒪`
becomes a comparison of sections which is the identity, and so the structure map of the
morphism of ringed topoi is an isomorphism.

## Main definitions

* `AlgebraicGeometry.smallZariskiToBigZariskiToposHom` and
  `AlgebraicGeometry.smallEtaleToBigEtaleToposHom`: **`i_f` at the universe of the structure
  rings**.
* `AlgebraicGeometry.smallZariskiToBigZariski_inverseImageStructureIso` and
  `AlgebraicGeometry.smallEtaleToBigEtale_inverseImageStructureIso`: **`i_f^{-1}𝒪 = 𝒪`** as an
  isomorphism of sheaves of commutative rings.
* `AlgebraicGeometry.smallZariskiToBigZariskiRingedToposHom` and
  `AlgebraicGeometry.smallEtaleToBigEtaleRingedToposHom`: **`i_f` as a morphism of ringed
  topoi.**

## Main results

* `AlgebraicGeometry.isIso_smallZariskiToBigZariskiRingedToposHom_fSharpInverseImage` and
  `AlgebraicGeometry.isIso_smallEtaleToBigEtaleRingedToposHom_fSharpInverseImage`: the structure
  map of `i_f` in inverse-image form is an isomorphism — the formal content of "because
  `i_f^{-1}𝒪 = 𝒪`".

## Implementation notes

The two topologies are two instantiations of one construction, not two constructions: all the
work is in `CategoryTheory.Functor.morphismOfTopoi_of_isCocontinuous`, in
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso` and in
`AlgebraicGeometry.RingedToposHom.ofInverseImageIso`, each of which is stated for an arbitrary
site.  They cannot be collapsed into a single `τ`-indexed statement because the small Zariski
and small étale sites of a scheme are different full subcategories of the big site over it —
the objects open over `S` and the objects étale over `S` — and the source treats them as two
cases for the same reason.

The structure sheaf of the big `τ`-site is taken in the uniform
`AlgebraicGeometry.bigSiteRingedSite` form of
`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/RingedBigSiteHom.lean`, so that the
identification of the restricted structure sheaf with the small one is the `rfl` recorded
as `AlgebraicGeometry.smallZariskiToBig_structureSheaf` and
`AlgebraicGeometry.smallEtaleToBig_structureSheaf`; those two theorems are what makes
`restrictionCommRingIso` land on the small structure sheaf with no intervening `eqToHom`.

The essential smallness of the big site localized at `S`, needed at the universe `u` for the
Kan extensions and for sheafification, is `AlgebraicGeometry.essentiallySmall_overBase`; it is a
lemma rather than an instance, so it is installed locally in each section.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 020Y](https://stacks.math.columbia.edu/tag/020Y)
* [Stacks Project, Tag 021F](https://stacks.math.columbia.edu/tag/021F)
* [Stacks Project, Tag 00XL](https://stacks.math.columbia.edu/tag/00XL)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry

/-! ### The small Zariski site inside the big Zariski site -/

section Zariski

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

private instance essentiallySmall_bigZariskiOver :
    EssentiallySmall.{u} (BigZariskiOver B S.1 S.property) :=
  essentiallySmall_overBase (τ := .zariski) B S.1 S.property

/-- **Stacks 020Y at the universe of the structure rings.**  The morphism of topoi
`i_f : \mathrm{Sh}(T_{Zar}) ⟶ \mathrm{Sh}((\Sch/S)_{Zar})` on sheaves of sets in `Type u`.

The library's `AlgebraicGeometry.smallZariskiToBigZariskiMorphism` is the same morphism for sheaves
of sets in `Type (u + 1)`, the universe of the objects of the sites; a ringed topos declares its
topos at the universe of the sections of its structure sheaf, so that one cannot carry a
morphism of ringed topoi. -/
@[stacks 020Y "the morphism of topoi, at the universe of the structure rings"]
public noncomputable def smallZariskiToBigZariskiToposHom :
    MorphismOfTopoi (Sheaf (SmallZariski.topology B T.1 T.property) (Type u))
      (Sheaf (BigZariskiOver.topology B S.1 S.property) (Type u)) :=
  Functor.morphismOfTopoi_of_isCocontinuous (smallZariskiToBigZariskiFunctor B T S f)
    (SmallZariski.topology B T.1 T.property) (BigZariskiOver.topology B S.1 S.property)

/-- The inverse image of `i_f` is restriction along `V/T ↦ V/S`, on the nose. -/
@[simp]
public theorem smallZariskiToBigZariskiToposHom_inverseImage :
    (smallZariskiToBigZariskiToposHom B f).inverseImage =
      (smallZariskiToBigZariskiFunctor B T S f).sheafPushforwardContinuous (Type u)
        (SmallZariski.topology B T.1 T.property)
        (BigZariskiOver.topology B S.1 S.property) := rfl

/-- **`i_f^{-1}𝒪 = 𝒪` for the Zariski sites**, as an isomorphism of sheaves of commutative
rings.  The inverse image of `i_f` is restriction, and restricting the structure sheaf of the
big Zariski site over `S` along `V/T ↦ V/S` returns the structure sheaf of the small Zariski
site of `T` — which is `AlgebraicGeometry.smallZariskiToBig_structureSheaf`, an equality by
`rfl`.  The comparison is the identity on sections. -/
@[stacks 070R "`i_f^{-1}𝒪 = 𝒪` for the Zariski sites, as an isomorphism of ring sheaves"]
public noncomputable def smallZariskiToBigZariski_inverseImageStructureIso :
    (inverseImageCommRingFunctor (smallZariskiToBigZariskiToposHom B f)).obj
        (bigSiteRingedSite (τ := .zariski) B S.1 S.property).O ≅
      (smallZariskiRingedSite B T.1 T.property).O :=
  restrictionCommRingIso (SmallZariski.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property) (smallZariskiToBigZariskiFunctor B T S f)
    (bigSiteRingedSite (τ := .zariski) B S.1 S.property).O

/-- **Stacks 070R for `i_f` on the Zariski sites.**  The morphism of topoi
`i_f : \mathrm{Sh}(T_{Zar}) ⟶ \mathrm{Sh}((\Sch/S)_{Zar})` of Topologies, Lemma 020Y, as a
morphism of ringed topoi

```
  (i_f, i_f^♯) : (\mathrm{Sh}(T_{Zar}), 𝒪) ⟶ (\mathrm{Sh}((\Sch/S)_{Zar}), 𝒪),
```

in the sense of Stacks 01D3.  Its structure map is the one determined by `i_f^{-1}𝒪 = 𝒪`. -/
@[stacks 070R "`i_f` on the Zariski sites, as a morphism of ringed topoi"]
public noncomputable def smallZariskiToBigZariskiRingedToposHom :
    RingedToposHom (smallZariskiRingedSite B T.1 T.property).toRingedTopos
      (bigSiteRingedSite (τ := .zariski) B S.1 S.property).toRingedTopos :=
  RingedToposHom.ofInverseImageIso
    (X := (smallZariskiRingedSite B T.1 T.property).toRingedTopos)
    (Y := (bigSiteRingedSite (τ := .zariski) B S.1 S.property).toRingedTopos)
    (smallZariskiToBigZariskiToposHom B f)
    (smallZariskiToBigZariski_inverseImageStructureIso B f)

/-- The underlying morphism of topoi of the ringed-topos morphism `i_f` on the Zariski sites is
`smallZariskiToBigZariskiToposHom`. -/
@[simp]
public theorem smallZariskiToBigZariskiRingedToposHom_toToposHom :
    (smallZariskiToBigZariskiRingedToposHom B f).toToposHom =
      smallZariskiToBigZariskiToposHom B f := rfl

/-- The structure map of `i_f` in inverse-image form is the comparison of `i_f^{-1}𝒪` with
`𝒪`. -/
public theorem smallZariskiToBigZariskiRingedToposHom_fSharpInverseImage :
    (smallZariskiToBigZariskiRingedToposHom B f).fSharpInverseImage =
      (smallZariskiToBigZariski_inverseImageStructureIso B f).hom :=
  RingedToposHom.ofInverseImageIso_fSharpInverseImage
    (X := (smallZariskiRingedSite B T.1 T.property).toRingedTopos)
    (Y := (bigSiteRingedSite (τ := .zariski) B S.1 S.property).toRingedTopos) _ _

/-- **The formal content of "because `i_f^{-1}𝒪 = 𝒪`":** the structure map of `i_f` in
inverse-image form is an isomorphism. -/
@[stacks 070R "`i_f` is a morphism of ringed topoi because `i_f^{-1}𝒪 = 𝒪`, Zariski case"]
public instance isIso_smallZariskiToBigZariskiRingedToposHom_fSharpInverseImage :
    IsIso (smallZariskiToBigZariskiRingedToposHom B f).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso
    (X := (smallZariskiRingedSite B T.1 T.property).toRingedTopos)
    (Y := (bigSiteRingedSite (τ := .zariski) B S.1 S.property).toRingedTopos) _ _

end Zariski

/-! ### The small étale site inside the big étale site -/

section Etale

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)

private instance essentiallySmall_bigEtaleOver :
    EssentiallySmall.{u} (BigEtaleOver B S.obj S.property) :=
  essentiallySmall_overBase (τ := .etale) B S.obj S.property

/-- **Stacks 021F at the universe of the structure rings.**  The morphism of topoi
`i_f : \mathrm{Sh}(T_\etale) ⟶ \mathrm{Sh}((\Sch/S)_\etale)` on sheaves of sets in `Type u`. -/
@[stacks 021F "the morphism of topoi, at the universe of the structure rings"]
public noncomputable def smallEtaleToBigEtaleToposHom :
    MorphismOfTopoi (Sheaf (SmallEtale.topology B T.obj T.property) (Type u))
      (Sheaf (BigEtaleOver.topology B S.obj S.property) (Type u)) :=
  Functor.morphismOfTopoi_of_isCocontinuous (smallEtaleToBigEtaleFunctor B T S f)
    (SmallEtale.topology B T.obj T.property) (BigEtaleOver.topology B S.obj S.property)

/-- The inverse image of `i_f` is restriction along `V/T ↦ V/S`, on the nose. -/
@[simp]
public theorem smallEtaleToBigEtaleToposHom_inverseImage :
    (smallEtaleToBigEtaleToposHom B f).inverseImage =
      (smallEtaleToBigEtaleFunctor B T S f).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property) := rfl

/-- **`i_f^{-1}𝒪 = 𝒪` for the étale sites**, as an isomorphism of sheaves of commutative rings.
The underlying equality of ring sheaves is
`AlgebraicGeometry.smallEtaleToBig_structureSheaf`, which holds by `rfl`. -/
@[stacks 070R "`i_f^{-1}𝒪 = 𝒪` for the étale sites, as an isomorphism of ring sheaves"]
public noncomputable def smallEtaleToBigEtale_inverseImageStructureIso :
    (inverseImageCommRingFunctor (smallEtaleToBigEtaleToposHom B f)).obj
        (bigSiteRingedSite (τ := .etale) B S.obj S.property).O ≅
      (smallEtaleRingedSite B T.obj T.property).O :=
  restrictionCommRingIso (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property) (smallEtaleToBigEtaleFunctor B T S f)
    (bigSiteRingedSite (τ := .etale) B S.obj S.property).O

/-- **Stacks 070R for `i_f` on the étale sites.**  The morphism of topoi
`i_f : \mathrm{Sh}(T_\etale) ⟶ \mathrm{Sh}((\Sch/S)_\etale)` of Topologies, Lemma 021F, as a
morphism of ringed topoi, in the sense of Stacks 01D3. -/
@[stacks 070R "`i_f` on the étale sites, as a morphism of ringed topoi"]
public noncomputable def smallEtaleToBigEtaleRingedToposHom :
    RingedToposHom (smallEtaleRingedSite B T.obj T.property).toRingedTopos
      (bigSiteRingedSite (τ := .etale) B S.obj S.property).toRingedTopos :=
  RingedToposHom.ofInverseImageIso
    (X := (smallEtaleRingedSite B T.obj T.property).toRingedTopos)
    (Y := (bigSiteRingedSite (τ := .etale) B S.obj S.property).toRingedTopos)
    (smallEtaleToBigEtaleToposHom B f)
    (smallEtaleToBigEtale_inverseImageStructureIso B f)

/-- The underlying morphism of topoi of the ringed-topos morphism `i_f` on the étale sites is
`smallEtaleToBigEtaleToposHom`. -/
@[simp]
public theorem smallEtaleToBigEtaleRingedToposHom_toToposHom :
    (smallEtaleToBigEtaleRingedToposHom B f).toToposHom =
      smallEtaleToBigEtaleToposHom B f := rfl

/-- The structure map of `i_f` in inverse-image form is the comparison of `i_f^{-1}𝒪` with
`𝒪`. -/
public theorem smallEtaleToBigEtaleRingedToposHom_fSharpInverseImage :
    (smallEtaleToBigEtaleRingedToposHom B f).fSharpInverseImage =
      (smallEtaleToBigEtale_inverseImageStructureIso B f).hom :=
  RingedToposHom.ofInverseImageIso_fSharpInverseImage
    (X := (smallEtaleRingedSite B T.obj T.property).toRingedTopos)
    (Y := (bigSiteRingedSite (τ := .etale) B S.obj S.property).toRingedTopos) _ _

/-- **The formal content of "because `i_f^{-1}𝒪 = 𝒪`":** the structure map of `i_f` in
inverse-image form is an isomorphism. -/
@[stacks 070R "`i_f` is a morphism of ringed topoi because `i_f^{-1}𝒪 = 𝒪`, étale case"]
public instance isIso_smallEtaleToBigEtaleRingedToposHom_fSharpInverseImage :
    IsIso (smallEtaleToBigEtaleRingedToposHom B f).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso
    (X := (smallEtaleRingedSite B T.obj T.property).toRingedTopos)
    (Y := (bigSiteRingedSite (τ := .etale) B S.obj S.property).toRingedTopos) _ _

end Etale

end AlgebraicGeometry

end
