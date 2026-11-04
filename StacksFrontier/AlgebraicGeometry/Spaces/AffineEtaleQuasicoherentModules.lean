module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCartesianModules

/-!
# Quasi-coherent modules on the affine étale site of an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `𝓕` be
a presheaf of `𝒪_F`-modules on the affine étale site `F_{affine, étale}` of Stacks 0H01.  This
file proves **Stacks 0H04**: the following three conditions on `𝓕` are equivalent.

1. For every morphism `U ⟶ U'` of `F_{affine, étale}` the base-change map
   `𝓕(U') ⊗_{𝒪_F(U')} 𝒪_F(U) ⟶ 𝓕(U)` is an isomorphism.
2. `𝓕` is a sheaf and is a quasi-coherent module on the ringed site
   `(F_{affine, étale}, 𝒪_F)` in the sense of Modules on Sites, Definition 03DL (6).
3. `𝓕` is a sheaf and corresponds to a quasi-coherent `𝒪_F`-module on the small étale site of
   `F` under the equivalence of ringed topoi of Stacks 0H03.

Conditions (2) and (3) are conditions on a *sheaf*, so each of them carries the sheaf condition
on `𝓕` as a conjunct, exactly as in the source: quasi-coherence is a condition on a sheaf of
modules, and the source's proof of (1) ⇒ (2) begins by proving that `𝓕` is a sheaf.

## Main definitions

* `AlgebraicGeometry.Space.affineEtaleStructureRingedSite` is the affine étale site of `F` with its
  structure sheaf, as a ringed site.
* `AlgebraicGeometry.Space.liftedSmallEtaleRingSheaf` is the sheaf of rings underlying the small
  étale structure sheaf of `F` at the universe of the charts, and
  `AlgebraicGeometry.Space.affineEtaleLiftedModuleRestriction` is restriction of sheaves of
  modules along the inclusion of the affine charts — the equivalence of Stacks 0H03 read on
  modules.

## Main results

* `AlgebraicGeometry.Space.affineEtaleLiftedModuleRestriction_comp_toSheaf`: that restriction of
  modules is, on underlying sheaves of abelian groups, the restriction functor of Stacks 0H03.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isIso_restrictionBaseChange`: **(1) ⇒ (2)**,
  a cartesian presheaf of modules on the affine étale site is a quasi-coherent sheaf.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleLiftedModuleRestriction_iff`:
  **(2) ⇔ (3)**, a sheaf of `𝒪_F`-modules on the small étale site is quasi-coherent exactly
  when its restriction to the affine charts is.
* `AlgebraicGeometry.Space.affineEtale_quasicoherent_tfae`: **Stacks 0H04**, the equivalence of
  the three conditions.

## Implementation notes

The structure sheaf used throughout is `AlgebraicGeometry.Space.affineEtaleStructureSheaf`, the
restriction to affine charts of the small étale structure sheaf with its rings of sections raised
to universe `u + 1`, the universe of the charts themselves.  That is the structure sheaf of the
two ringed topoi of Stacks 0H03, so clause (3) is literally read along that equivalence, and it
is the one over which the forward implication (2) ⇒ (1) is already available as
`AlgebraicGeometry.Space.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`.  The sections of
the modules therefore also live in universe `u + 1`: the Comparison Lemma for sheaves of modules
puts them in the universe of the structure rings, and the quasi-coherence criterion of
Stacks 0GZN, `Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso`, is stated
there too.

The base-change map of clause (1) is `Stacks.PresheafOfModules.restrictionBaseChange`, and the
base-change map of the quasi-coherence criterion is
`Stacks.SheafOfModules.canonicalMap`; the two are the same term, both being the adjoint
transpose of the same restriction map under `ModuleCat.extendRestrictScalarsAdj`, so (1) ⇒ (2)
needs no comparison between them.

Clause (2) ⇔ (3) is the clause 03DL (6) of Stacks 03DM along the dense subsite inclusion of
Stacks 04JS, `Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`.  Its size
hypotheses are all discharged by the universe arithmetic of the site: the objects of the affine
étale site and of the small étale site, and of each of their slices and comma categories, lie in
`Type (u + 1)` with morphisms in `Type u`, so `max` of the two is the module universe `u + 1`
and `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` applies with no appeal to
essential smallness.

## References

* [Stacks Project, Tag 0H04](https://stacks.math.columbia.edu/tag/0H04)
* [Stacks Project, Tag 0H03](https://stacks.math.columbia.edu/tag/0H03)
* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The affine étale site of `F` with the structure sheaf of Stacks 0H03, as a ringed site.

It differs from `AlgebraicGeometry.Space.affineEtaleRingedSite`, the restriction of the small
étale structure sheaf, in its universe of rings: its sheaf of rings is
`AlgebraicGeometry.Space.affineEtaleRingSheaf`, of the structure sheaf of Stacks 0H03. -/
noncomputable def affineEtaleStructureRingedSite : RingedSite.{u + 1, u, u + 1} where
  C := AffineEtale B S hS F
  J := AffineEtale.topology B S hS F
  O := affineEtaleStructureSheaf B S hS F hF

/-- The sheaf of rings of the affine étale ringed site is the one of
`AlgebraicGeometry.Space.affineEtaleRingSheaf`. -/
theorem ringSheaf_affineEtaleStructureRingedSite :
    Stacks.SheafOfModules.Tensor.ringSheaf (affineEtaleStructureRingedSite B S hS F hF).O =
      affineEtaleRingSheaf B S hS F hF :=
  rfl

/-- The base-change map of the affine étale ringed site is the base-change comparison of the
restriction map: both are the adjoint transpose of the restriction map of the module along the
morphism, under `ModuleCat.extendRestrictScalarsAdj`. -/
theorem canonicalMap_affineEtaleStructureRingedSite
    (M : PresheafOfModules.{u + 1}
      ((affineEtaleStructureSheaf B S hS F hF).obj ⋙ forget₂ CommRingCat RingCat))
    (h : Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf)
    {U V : AffineEtale B S hS F} (f : U ⟶ V) :
    Stacks.SheafOfModules.canonicalMap (affineEtaleStructureRingedSite B S hS F hF) ⟨M, h⟩ f =
      Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1} M f.op :=
  rfl

/-! ### Condition (1) implies condition (2) -/

/-- **Stacks 0H04, (1) ⇒ (2).**  A presheaf of `𝒪_F`-modules on the affine étale site of an
algebraic space all of whose base-change maps `𝓕(U') ⊗_{𝒪_F(U')} 𝒪_F(U) ⟶ 𝓕(U)` are
isomorphisms is a sheaf and is quasi-coherent on the ringed site
`(F_{affine, étale}, 𝒪_F)`.

The sheaf condition is `AlgebraicGeometry.Space.isSheaf_of_cartesian_affineEtale`: the coverings
of the affine étale site are finite flat coverings of affine schemes, so it is flat descent of
modules.  Quasi-coherence is the criterion of Stacks 0GZN in the form
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso`, whose hypothesis is the
assumption read through `AlgebraicGeometry.Space.canonicalMap_affineEtaleStructureRingedSite`. -/
theorem isQuasicoherentOnSite_of_isIso_restrictionBaseChange
    (M : PresheafOfModules.{u + 1}
      ((affineEtaleStructureSheaf B S hS F hF).obj ⋙ forget₂ CommRingCat RingCat))
    (hM : ∀ (U V : AffineEtale B S hS F) (f : U ⟶ V),
      IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1} M f.op)) :
    ∃ h : Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf,
      (⟨M, h⟩ : SheafOfModules.{u + 1}
        (affineEtaleRingSheaf B S hS F hF)).IsQuasicoherentOnSite := by
  have hs : Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf :=
    isSheaf_of_cartesian_affineEtale.{u, u + 1} B S hS F hF M
      (fun {X Y} f => hM Y.unop X.unop f.unop)
  exact ⟨hs, Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso
    (affineEtaleStructureRingedSite B S hS F hF) ⟨M, hs⟩ hM⟩

/-! ### The equivalence of Stacks 0H03 on modules -/

/-- The sheaf of rings underlying the small étale structure sheaf of `F`, with its rings of
sections at the universe of the charts.  This is the sheaf of rings of the ringed topos
`liftedSmallEtaleRingedTopos` of Stacks 0H03. -/
noncomputable abbrev liftedSmallEtaleRingSheaf :
    Sheaf (SmallEtale.topology B S hS F) RingCat.{u + 1} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (liftedStructureSheaf B S hS F).val

/-- **Restriction of sheaves of modules to the affine charts of `F`,** at the universe of the
charts: the equivalence of ringed topoi of Stacks 0H03 read on modules.  Its inverse image on
sheaves is restriction along the inclusion of the affine charts, which is a dense subsite
inclusion by Stacks 04JS, and its structure map is the identity because the affine étale
structure sheaf is *defined* as the restriction of the small étale one. -/
noncomputable def affineEtaleLiftedModuleRestriction :
    SheafOfModules.{u + 1} (liftedSmallEtaleRingSheaf B S hS F) ⥤
      SheafOfModules.{u + 1} (affineEtaleRingSheaf B S hS F hF) :=
  letI _hd := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  Stacks.DenseSubsiteModules.moduleRestriction
    (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F) (liftedSmallEtaleRingSheaf B S hS F)

/-- **Restriction of modules to the affine charts is the restriction functor of Stacks 0H03.**
On underlying sheaves of abelian groups,
`AlgebraicGeometry.Space.affineEtaleLiftedModuleRestriction` *is*
`AlgebraicGeometry.Space.affineEtaleRestriction`, the inverse image of the comparison morphism
of ringed topoi `AlgebraicGeometry.Space.affineEtaleToSmallEtale` of Stacks 0H03; so clause (3)
of Stacks 0H04 below is read along that equivalence and not along some other comparison. -/
theorem affineEtaleLiftedModuleRestriction_comp_toSheaf :
    affineEtaleLiftedModuleRestriction B S hS F hF ⋙
        SheafOfModules.toSheaf.{u + 1} (affineEtaleRingSheaf B S hS F hF) =
      SheafOfModules.toSheaf.{u + 1} (liftedSmallEtaleRingSheaf B S hS F) ⋙
        affineEtaleRestriction B S hS F hF AddCommGrpCat.{u + 1} :=
  rfl

/-- Sheaves of abelian groups at the universe of the charts admit sheafification on every slice
of the small étale site of `F`: the objects of such a slice lie in `Type (u + 1)` and its
morphisms in `Type u`, so `max` of the two is the universe of the sections. -/
theorem hasSheafify_smallEtale_over (V : SmallEtale B S hS F) :
    HasSheafify ((SmallEtale.topology B S hS F).over V) AddCommGrpCat.{u + 1} := by
  apply CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat

/-- Sheafification of sheaves of abelian groups at the universe of the charts inverts exactly
the locally bijective morphisms on every slice of the small étale site of `F`. -/
theorem wEqualsLocallyBijective_smallEtale_over (V : SmallEtale B S hS F) :
    ((SmallEtale.topology B S hS F).over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  apply CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- Sheaves of abelian groups at the universe of the charts admit sheafification on every slice
of the affine étale site of `F`. -/
theorem hasSheafify_affineEtale_over (U : AffineEtale B S hS F) :
    HasSheafify ((AffineEtale.topology B S hS F).over U) AddCommGrpCat.{u + 1} := by
  apply CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat

/-- Sheafification of sheaves of abelian groups at the universe of the charts inverts exactly
the locally bijective morphisms on every slice of the affine étale site of `F`. -/
theorem wEqualsLocallyBijective_affineEtale_over (U : AffineEtale B S hS F) :
    ((AffineEtale.topology B S hS F).over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} := by
  apply CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- **Stacks 0H04, (2) ⇔ (3).**  A sheaf of `𝒪_F`-modules on the small étale site of an
algebraic space is quasi-coherent exactly when its restriction to the affine étale charts is
quasi-coherent over the restricted structure sheaf.

This is the clause 03DL (6) of Stacks 03DM along the dense subsite inclusion of Stacks 04JS,
`Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`. -/
theorem isQuasicoherentOnSite_affineEtaleLiftedModuleRestriction_iff
    (G : SheafOfModules.{u + 1} (liftedSmallEtaleRingSheaf B S hS F)) :
    G.IsQuasicoherentOnSite ↔
      ((affineEtaleLiftedModuleRestriction B S hS F hF).obj G).IsQuasicoherentOnSite := by
  have _hd := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have _hc := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).1
  have _h1 := hasSheafify_smallEtale_over B S hS F
  have _h2 := wEqualsLocallyBijective_smallEtale_over B S hS F
  have _h3 := hasSheafify_affineEtale_over B S hS F
  have _h4 := wEqualsLocallyBijective_affineEtale_over B S hS F
  exact Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff
    (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F) (liftedSmallEtaleRingSheaf B S hS F) G

/-- **Restriction of sheaves of modules to the affine charts of `F` is an equivalence,** at the
universe of the charts: the Comparison Lemma for sheaves of modules along the dense subsite
inclusion of Stacks 04JS. -/
theorem isEquivalence_affineEtaleLiftedModuleRestriction :
    (affineEtaleLiftedModuleRestriction B S hS F hF).IsEquivalence := by
  have _hd := (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  have _he : ((AffineEtale.inclusion B S hS F).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)).IsEquivalence := by
    have _hl : ∀ X : (SmallEtale B S hS F)ᵒᵖ,
        HasLimitsOfShape (StructuredArrow X (AffineEtale.inclusion B S hS F).op)
          AddCommGrpCat.{u + 1} := fun _ => inferInstance
    infer_instance
  change (Stacks.DenseSubsiteModules.moduleRestriction
    (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F)
    (AffineEtale.inclusion B S hS F) (liftedSmallEtaleRingSheaf B S hS F)).IsEquivalence
  infer_instance

/-! ### The three conditions of Stacks 0H04 -/

/-- **Stacks 0H04.**  Let `F` be an algebraic space over a scheme `S` and let `𝓕` be a presheaf
of `𝒪_F`-modules on the affine étale site of `F`.  The following are equivalent:

1. for every morphism `U ⟶ U'` of `F_{affine, étale}` the base-change map
   `𝓕(U') ⊗_{𝒪_F(U')} 𝒪_F(U) ⟶ 𝓕(U)` is an isomorphism;
2. `𝓕` is a sheaf and is quasi-coherent on the ringed site `(F_{affine, étale}, 𝒪_F)` in the
   sense of Modules on Sites, Definition 03DL (6);
3. `𝓕` is a sheaf and corresponds, under the equivalence of Stacks 0H03, to a quasi-coherent
   `𝒪_F`-module on the small étale site of `F`.

Conditions (2) and (3) carry the sheaf condition as a conjunct, because quasi-coherence is a
condition on a sheaf of modules; the source's proof of (1) ⇒ (2) likewise begins by proving the
sheaf condition.

(1) ⇒ (2) is `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isIso_restrictionBaseChange`,
(2) ⇒ (1) is `AlgebraicGeometry.Space.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`, and
(2) ⇔ (3) is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_affineEtaleLiftedModuleRestriction_iff` together
with the essential surjectivity of restriction to the affine charts. -/
@[stacks 0H04 "the equivalence of (1), (2) and (3)"]
theorem affineEtale_quasicoherent_tfae
    (M : PresheafOfModules.{u + 1}
      ((affineEtaleStructureSheaf B S hS F hF).obj ⋙ forget₂ CommRingCat RingCat)) :
    List.TFAE
      [∀ (U V : AffineEtale B S hS F) (f : U ⟶ V),
          IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1} M f.op),
        ∃ h : Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf,
          (⟨M, h⟩ : SheafOfModules.{u + 1}
            (affineEtaleRingSheaf B S hS F hF)).IsQuasicoherentOnSite,
        ∃ h : Presheaf.IsSheaf (AffineEtale.topology B S hS F) M.presheaf,
          ∃ G : SheafOfModules.{u + 1} (liftedSmallEtaleRingSheaf B S hS F),
            G.IsQuasicoherentOnSite ∧
              Nonempty ((affineEtaleLiftedModuleRestriction B S hS F hF).obj G ≅ ⟨M, h⟩)] := by
  tfae_have 1 → 2 := isQuasicoherentOnSite_of_isIso_restrictionBaseChange B S hS F hF M
  tfae_have 2 → 1 := fun ⟨h, hq⟩ _ _ f =>
    isIso_restrictionBaseChange_of_isQuasicoherentOnSite.{u, u + 1} B S hS F hF ⟨M, h⟩ hq f
  tfae_have 2 → 3 := by
    rintro ⟨h, hq⟩
    have _he := isEquivalence_affineEtaleLiftedModuleRestriction B S hS F hF
    refine ⟨h, (affineEtaleLiftedModuleRestriction B S hS F hF).objPreimage ⟨M, h⟩, ?_,
      ⟨(affineEtaleLiftedModuleRestriction B S hS F hF).objObjPreimageIso ⟨M, h⟩⟩⟩
    exact (isQuasicoherentOnSite_affineEtaleLiftedModuleRestriction_iff B S hS F hF _).2
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((affineEtaleLiftedModuleRestriction B S hS F hF).objObjPreimageIso ⟨M, h⟩).symm hq)
  tfae_have 3 → 2 := fun ⟨h, G, hG, ⟨e⟩⟩ =>
    ⟨h, SheafOfModules.IsQuasicoherentOnSite.of_iso e
      ((isQuasicoherentOnSite_affineEtaleLiftedModuleRestriction_iff B S hS F hF G).1 hG)⟩
  tfae_finish

end AlgebraicGeometry.Space

end
