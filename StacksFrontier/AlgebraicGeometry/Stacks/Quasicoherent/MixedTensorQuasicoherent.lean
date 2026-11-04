module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorQuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FibredRingSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.MixedTensorRingULift
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# Quasi-coherence of the tensor product of modules with sections in independent universes

The tensor product of two quasi-coherent sheaves of modules on a ringed site is quasi-coherent
also when the sections of the two factors lie in two universes unrelated to each other and to
the site.  On a category fibred in groupoids over the big fppf category of schemes over a base
this is quasi-coherence of `AlgebraicGeometry.FibredSite.tensorSheafMixed`, the tensor product
whose universal property is Stacks 06WN(2).

The canonical theorem
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite` treats factors
whose sections lie in the universe of the coefficient rings. To keep the coefficient and
factor universes independent here, the proof transports the tensor product to one common
universe containing the site, rings and sections, then descends. It uses four existing
comparisons, none of which computes a sheafification:

* raising the universe of the *sections* of a sheaf of modules by an arbitrary amount preserves
  quasi-coherence, which is
  `SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`;
* raising the universe of the *coefficient rings* is an isomorphism of categories of sheaves of
  modules preserving quasi-coherence, which is
  `Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftUp` and its inverse
  `Stacks.Modules.isQuasicoherentOnSite_sheafRingULiftDown`;
* raising the universe of the coefficient rings commutes with the objectwise tensor product,
  which is `Stacks.Modules.tensorPresheafRingULiftDownIso`;
* lowering the universe of the coefficient rings, and raising the universe of the sections,
  commute with sheafification, which are `Stacks.Modules.sheafificationRingULiftDownIso` and
  `PresheafOfModules.sheafificationUliftObjIso`.

After the first two steps the two factors are sheaves of modules over the universe lift of the
coefficient rings with sections in the universe of those lifted rings, so the single-universe
theorem applies to them; the inverse of the second comparison and the last two carry the
conclusion back.

## Main results

* `Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift`: **on a ringed site whose
  sets of sections form a sheaf, the sheafification of the universe lift of the objectwise tensor
  product of two quasi-coherent sheaves of modules with sections in independent universes is
  quasi-coherent.**
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_tensorSheafMixed`: **the tensor product of
  two quasi-coherent sheaves of modules with sections in independent universes on an associated
  site of a category fibred in groupoids is quasi-coherent.**
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_toSiteModules_fppf`: a quasi-coherent
  module on the fppf site of the fibred category is quasi-coherent when read as a sheaf of
  modules for the inherited fppf topology.
* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_tensorSheafMixed_quasicoherent`: the
  tensor product of a pair of quasi-coherent modules with sections in independent universes,
  formed on the fppf site of the fibred category, is quasi-coherent.

## Implementation notes

The amount by which the sections of the first factor are raised is `max so sm r n`, with `so`
and `sm` the universes of the objects and the morphisms of the site, `r` that of the coefficient
rings and `n` that of the sections of the second factor, and symmetrically for the second
factor; both then have sections in `max so sm r m n`, which is the universe of the rings lifted
by `max m n`.  That is the regime of the single-universe theory.  The universe of the lifted
rings must contain the site, since a global presentation is indexed there, which is why the
rings are lifted into `max so sm r m n` rather than into `max r m n`.

The sheafification facts for abelian groups at `max so sm r m n` are produced inside the proof
from `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and its companion, which
apply because that universe contains the site; only the two facts at `max r m n`, the universe
of the sections of the mixed tensor product itself, are hypotheses, and on an associated site of
an essentially small fibred category they are supplied by
`AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology_above` and its companion, where
the universe of the sections need not contain the universe of the objects of the fibred
category.

Local bijectivity of the comparison of coefficient rings is supplied as a term throughout rather
than found by instance synthesis, which fails for the identity comparison once sheafification
instances at two different universes of sections are in scope.

Quasi-coherence of the two factors is taken as an explicit argument of the ringed-site statement
rather than as an instance.  The structure sheaf of an associated site of the fibred category is
the structure sheaf of a ringed site only up to unfolding the definition, and instance synthesis
does not see through that, while a term is checked against the expected type at the ordinary
transparency.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe so sm r u v m n

namespace Stacks.Modules

open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable {C : Type so} [Category.{sm} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **The tensor product of two quasi-coherent sheaves of modules with sections in independent
universes on a ringed site is quasi-coherent.**  The tensor product is the sheafification of the
universe lift of the objectwise tensor product, which is the shape in which it carries the
universal property of Stacks 06WN(2); its sections lie in the universe containing the
coefficient rings and the sections of the two factors.

The proof transports the pair into the regime in which the coefficient universe contains the
site and the sections, where
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite` applies:
the sections of each factor are raised so that both lie in one universe, the coefficient rings
are raised to that universe, and the three comparisons
`Stacks.Modules.tensorPresheafRingULiftDownIso`,
`Stacks.Modules.sheafificationRingULiftDownIso` and
`PresheafOfModules.sheafificationUliftObjIso` identify the tensor product formed there with the
universe lift of the sections of the one formed here.  No sheafification is computed.

The hypothesis on the sets of sections is what allows the universe of the coefficient rings to
be raised; it is not implied by the sheaf condition in `RingCat.{r}` when the site does not fit
inside `Type r`. -/
theorem isQuasicoherentOnSite_sheafificationTensorObjUlift
    (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
    (hset : Presheaf.IsSheaf J (structureRingPresheaf 𝒪 ⋙ forget RingCat.{r}))
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m n}]
    [HasWeakSheafify J AddCommGrpCat.{max r m n}]
    (F : SheafOfModules.{m} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (G : SheafOfModules.{n} (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
    (hF : F.IsQuasicoherentOnSite) (hG : G.IsQuasicoherentOnSite) :
    ((PresheafOfModules.sheafification.{max r m n}
      (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).obj
        ((PresheafOfModules.tensorObj (O := 𝒪) F.val G.val).uliftSections.{r})
      ).IsQuasicoherentOnSite := by
  have _ := SheafOfModules.isLocallyInjective_id_structure
    (R := SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)
  have _ := SheafOfModules.isLocallySurjective_id_structure
    (R := SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)
  have _ := hF
  have _ := hG
  have _ : (SheafOfModules.uliftForPresentation.{so, sm, r, m, max so sm r n} F
      ).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{so, sm, r, m, max so sm r n} hF
  have _ : (SheafOfModules.uliftForPresentation.{so, sm, r, n, max so sm r m} G
      ).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'.{so, sm, r, n, max so sm r m} hG
  have leftQuasicoherent := isQuasicoherentOnSite_sheafRingULiftUp.{so, sm, r, max m n} h𝒪 hset
    (SheafOfModules.uliftForPresentation.{so, sm, r, m, max so sm r n} F)
  have rightQuasicoherent := isQuasicoherentOnSite_sheafRingULiftUp.{so, sm, r, max m n} h𝒪 hset
    (SheafOfModules.uliftForPresentation.{so, sm, r, n, max so sm r m} G)
  have _ : HasSheafify J AddCommGrpCat.{max so sm r m n} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max so sm r m n, sm, so} J
  have _ : J.WEqualsLocallyBijective AddCommGrpCat.{max so sm r m n} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max so sm r m n,
      so, sm} J
  have _ := SheafOfModules.isLocallyInjective_id_structure
    (R := structureSheafRingULift.{so, sm, r, max m n} hset)
  have _ := SheafOfModules.isLocallySurjective_id_structure
    (R := structureSheafRingULift.{so, sm, r, max m n} hset)
  have tensorQuasicoherent :=
    @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite.{so, sm,
      max so sm r m n} C _ J _ _ _
    ⟨ringULift.{so, sm, r, max m n} 𝒪, Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ CommRingCat RingCat)
      (isSheaf_structureRingPresheaf_ringULift.{so, sm, r, max m n} 𝒪 hset)⟩
    ((sheafRingULiftUp.{so, sm, r, max m n, max so sm r m n} h𝒪 hset).obj
      (SheafOfModules.uliftForPresentation.{so, sm, r, m, max so sm r n} F))
    ((sheafRingULiftUp.{so, sm, r, max m n, max so sm r m n} h𝒪 hset).obj
      (SheafOfModules.uliftForPresentation.{so, sm, r, n, max so sm r m} G))
    leftQuasicoherent rightQuasicoherent
  have hD := @isQuasicoherentOnSite_sheafRingULiftDown.{so, sm, r, max m n} C _ J 𝒪 h𝒪 hset _
    tensorQuasicoherent
  have e₁ := sheafificationRingULiftDownIso.{so, sm, r, max so sm r m n, max m n} h𝒪 hset
    (tensorPresheafRingULift.{so, sm, r, 0, m, n} 𝒪 F.val G.val)
  have e₂ := (PresheafOfModules.sheafification.{max so sm r m n}
      (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)).mapIso
    (tensorPresheafRingULiftDownIso.{so, sm, r, 0, m, n} 𝒪 F.val G.val ≪≫
      (PresheafOfModules.uliftSectionsCompIso.{so, sm, r, max m n, r, max so sm}
        (PresheafOfModules.tensorObj (O := 𝒪) F.val G.val)).symm)
  have e₃ := PresheafOfModules.sheafificationUliftObjIso.{so, sm, r, max r m n, max so sm r}
    (𝟙 (SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj)
    ((PresheafOfModules.tensorObj (O := 𝒪) F.val G.val).uliftSections.{r})
  exact SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation.{so, sm, r, max r m n}
    (SheafOfModules.IsQuasicoherentOnSite.of_iso (e₁.symm ≪≫ e₂ ≪≫ e₃) hD)

end Stacks.Modules

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- A quasi-coherent module on the fppf site of a category fibred in groupoids is quasi-coherent
when read as a sheaf of modules for the inherited fppf topology: reading it there changes neither
the presheaf of sections nor the topology. -/
theorem isQuasicoherentOnSite_toSiteModules_fppf
    (F : quasicoherentModules.{u, v, u, m} B S hS p hp) :
    ((toSiteModules B S hS p hp .fppf).obj F).IsQuasicoherentOnSite :=
  F.property

variable [EssentiallySmall.{u} 𝒳]

/-- **The tensor product of two quasi-coherent sheaves of modules with sections in independent
universes on an associated site of a category fibred in groupoids is quasi-coherent.**  The
tensor product is `AlgebraicGeometry.FibredSite.tensorSheafMixed`, the object carrying the
universal property of Stacks 06WN(2); its sections lie in `max u m n`, with `u` the universe of
the coefficient rings, and the universe of the objects of the fibred category does not enter.

The sets of sections of the structure sheaf of an associated site form a sheaf, by
`AlgebraicGeometry.FibredSite.structureRingPresheaf_isSheafOfSets`, which is what allows the
universe of the coefficient rings to be raised; the sheafification facts for abelian groups with
sections above the universe of the coefficient rings come from
`AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology_above` and its companion. -/
theorem isQuasicoherentOnSite_tensorSheafMixed (τ : SiteKind)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ))
    (G : SheafOfModules.{n} (ringStructureSheafCore B S hS p hp τ))
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    (tensorSheafMixed B S hS p hp τ F G).IsQuasicoherentOnSite := by
  have _ := hasWeakSheafify_associatedTopology_above.{u, v, max m n} B S hS p τ
  have _ := wEqualsLocallyBijective_associatedTopology_above.{u, v, max m n} B S hS p τ
  exact Stacks.Modules.isQuasicoherentOnSite_sheafificationTensorObjUlift.{v, u, u, m, n}
    (𝒪 := (structureSheaf B S hS p hp τ).obj)
    (ringStructureSheafCore B S hS p hp τ).property
    (structureRingPresheaf_isSheafOfSets B S hS p hp τ) F G
    (inferInstance : F.IsQuasicoherentOnSite) (inferInstance : G.IsQuasicoherentOnSite)

/-- **The tensor product of a pair of quasi-coherent modules with sections in independent
universes, formed on the fppf site of a category fibred in groupoids, is quasi-coherent.**  This
is the object whose universal property is
`AlgebraicGeometry.FibredSite.existsUnique_hom_tensorSheafMixed_quasicoherent`, so the tensor
product of quasi-coherent modules is again a quasi-coherent module. -/
@[stacks 06WN "tensor_products", stacks 06WV "tensor_product"]
theorem isQuasicoherentOnSite_tensorSheafMixed_quasicoherent
    (F : quasicoherentModules.{u, v, u, m} B S hS p hp)
    (G : quasicoherentModules.{u, v, u, n} B S hS p hp) :
    (tensorSheafMixed B S hS p hp .fppf ((toSiteModules B S hS p hp .fppf).obj F)
      ((toSiteModules B S hS p hp .fppf).obj G)).IsQuasicoherentOnSite :=
  have _ := isQuasicoherentOnSite_toSiteModules_fppf B S hS p hp F
  have _ := isQuasicoherentOnSite_toSiteModules_fppf B S hS p hp G
  isQuasicoherentOnSite_tensorSheafMixed B S hS p hp .fppf _ _

end AlgebraicGeometry.FibredSite

end
