module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FibredTensorProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.MixedUniverseTensorProduct
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse

/-!
# Tensor products of module sheaves in independent universes on a fibred site

A category fibred in groupoids over the big fppf category of schemes over `S` carries five
associated topologies, all on the same category and all with the same coefficient sheaf of
rings.  This file forms the tensor product of two sheaves of modules on such a site whose
sections lie in two independent universes `m` and `n`, by sheafifying the universe lift of their
objectwise tensor product, and proves that the result is their tensor product in the category of
sheaves of modules for the site it is formed on, and for every finer one.  Its sections lie in
`max u m n`, with `u` the universe of the coefficient rings; the universe of the objects of the
fibred category does not enter.

## Main definitions

* `Stacks.Modules.toTensorSheafMixed` is the pure-tensor bilinear map from a pair of presheaves
  of modules on a ringed site into the sheafification of the universe lift of their objectwise
  tensor product.
* `AlgebraicGeometry.FibredSite.structureComparison` is the comparison of the ring presheaf
  underlying the commutative structure sheaf of an associated site with the coefficient sheaf of
  rings of that site.
* `AlgebraicGeometry.FibredSite.tensorSheafBifunctorMixed` is the tensor product of presheaves
  of modules with sections in independent universes on an associated site, as a bifunctor
  landing in sheaves of modules, and
  `AlgebraicGeometry.FibredSite.tensorSheafMixed` its value on a pair of sheaves of modules,
  with `AlgebraicGeometry.FibredSite.toTensorSheafMixed` the pure-tensor bilinear map into it.

## Main results

* `AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology_above`,
  `AlgebraicGeometry.FibredSite.wEqualsLocallyBijective_associatedTopology_above` and
  `AlgebraicGeometry.FibredSite.hasSheafCompose_associatedTopology_above`: the three
  sheafification facts for abelian groups on an associated site of an essentially small fibred
  category, at every universe of sections containing the universe of the coefficient rings.
* `Stacks.Modules.existsUnique_hom_toTensorSheafMixed`: on a ringed site, the sheafification of
  the universe lift of the objectwise tensor product of two presheaves of modules is their
  tensor product in the category of sheaves of modules for every topology finer than the one it
  is formed on.
* `AlgebraicGeometry.FibredSite.existsUnique_hom_tensorSheafMixed`,
  `AlgebraicGeometry.FibredSite.existsUnique_hom_tensorSheafMixed_sheaf` and
  `AlgebraicGeometry.FibredSite.existsUnique_hom_tensorSheafMixed_quasicoherent`: consequently
  the tensor product formed on any associated site of the fibred category is the tensor product
  in the category of sheaves of modules for that site and for every finer one, in particular for
  the inherited fppf topology, and in particular for a pair of quasi-coherent modules.

## Implementation notes

The whole construction rests on two facts about sheafification of abelian presheaves whose
sections lie above the universe of the coefficient rings but not above the universe of the
objects of the site.  These are not available by the plus construction, which colimits over the
covering sieves of the site and therefore cannot reach a universe that does not contain the site
objects; they are obtained instead by transporting to a small model, which is what
`CategoryTheory.hasWeakSheafify_addCommGrpCat_of_essentiallySmall` and its companions do.  The
hypothesis they need is essential smallness of the fibred category, which is exactly the
hypothesis already carried by the single-universe theory.

The three sheafification facts are stated at a universe of sections written `max u t` with `t`
a single parameter rather than at `max u m n`, so that the universes of the two factors do not
appear only inside one `max` expression; they are applied at `t := max m n`.

The coefficient sheaf of rings of an associated site and the ring presheaf underlying its
commutative structure sheaf are the same presheaf by construction but are built by different
routes, so `structureComparison` is the identity morphism between the two forms rather than a
rewrite of one into the other; its local bijectivity is what makes the sheafification of
presheaves of modules available on the site.
Local injectivity and local surjectivity of it are supplied as terms rather than found by
instance synthesis, which fails for them once the two sheafification instances are in scope.

The universal property is read off from
`Stacks.Modules.existsUnique_hom_ulift_of_le`: the sheafification unit of a presheaf of modules
is locally bijective on sections, and both local injectivity and local surjectivity pass to
finer topologies, while a sheaf for a finer topology is a sheaf for a coarser one.  So one
comparison serves every finer topology, which is the formal content of the agreement of the
tensor products computed on the five sites.

The factorization is tested against every sheaf of modules on the site, not only the
quasi-coherent ones, and the two factors are arbitrary sheaves of modules; the quasi-coherent
statement is the special case obtained by restricting a pair of quasi-coherent fppf modules to
the site.

## References

* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w m n t

namespace Stacks.Modules

open AlgebraicGeometry
open PresheafOfModules (tensorObj)

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}

section

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [HasWeakSheafify J AddCommGrpCat.{t}]

/-- The sheafification unit of a presheaf of modules is locally injective on sections.  This is
the library's instance, named so that it can be supplied as a term: in the presence of a
locally bijective comparison of coefficient rings, instance synthesis does not find it. -/
public theorem isLocallyInjective_toSheafify_sectionTypes (P : PresheafOfModules.{t} R₀) :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (CategoryTheory.toSheafify J P.presheaf)
        (forget AddCommGrpCat.{t})) :=
  inferInstance

/-- The sheafification unit of a presheaf of modules is locally surjective on sections.  This is
the library's instance, named so that it can be supplied as a term: in the presence of a
locally bijective comparison of coefficient rings, instance synthesis does not find it. -/
public theorem isLocallySurjective_toSheafify_sectionTypes (P : PresheafOfModules.{t} R₀) :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (CategoryTheory.toSheafify J P.presheaf)
        (forget AddCommGrpCat.{t})) :=
  inferInstance

end

variable {R : Cᵒᵖ ⥤ CommRingCat.{u}} {Rsh : Sheaf J RingCat.{u}}
  (α : R ⋙ forget₂ CommRingCat RingCat ⟶ Rsh.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

section

variable [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [HasWeakSheafify J AddCommGrpCat.{t}]

/-- On sections, the sheafification unit of a presheaf of modules is the sheafification unit of
its presheaf of abelian groups. -/
public theorem sectionTypesMap_sheafificationAdjunction_unit
    (P : PresheafOfModules.{t} (R ⋙ forget₂ CommRingCat RingCat)) :
    sectionTypesMap ((PresheafOfModules.sheafificationAdjunction α).unit.app P) =
      Functor.whiskerRight (CategoryTheory.toSheafify J P.presheaf) (forget AddCommGrpCat.{t}) :=
  rfl

end

section

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u m n}]
  [HasWeakSheafify J AddCommGrpCat.{max u m n}]
  (F : PresheafOfModules.{m} (R ⋙ forget₂ CommRingCat RingCat))
  (G : PresheafOfModules.{n} (R ⋙ forget₂ CommRingCat RingCat))

/-- The pure-tensor bilinear map from a pair of presheaves of modules with sections in
independent universes into the sheafification of the universe lift of their objectwise tensor
product: the sheafification unit, read as a bilinear map on sections.  The target of the
sheafification is the value of `Stacks.Modules.tensorSheafBifunctorMixed`, so its sections lie
in `max u m n`, with `u` the universe of the coefficient rings. -/
public noncomputable def toTensorSheafMixed :
    BilinearMap R F G
      ((PresheafOfModules.sheafification α ⋙ SheafOfModules.forget Rsh ⋙
        PresheafOfModules.restrictScalars α).obj ((tensorObj F G).uliftSections.{u})) :=
  BilinearMap.ofUliftTensorHom
    ((PresheafOfModules.sheafificationAdjunction α).unit.app ((tensorObj F G).uliftSections.{u}))

/-- The morphism out of the objectwise tensor product with raised sections associated with the
pure-tensor bilinear map is the sheafification unit itself. -/
public theorem uliftTensorHom_toTensorSheafMixed :
    (toTensorSheafMixed α F G).uliftTensorHom =
      (PresheafOfModules.sheafificationAdjunction α).unit.app ((tensorObj F G).uliftSections.{u}) :=
  BilinearMap.uliftHomEquiv.left_inv _

/-- The comparison of the objectwise tensor product with raised sections with its
sheafification is locally injective on sections. -/
public theorem isLocallyInjective_toTensorSheafMixed :
    Presheaf.IsLocallyInjective J (sectionTypesMap (toTensorSheafMixed α F G).uliftTensorHom) := by
  rw [uliftTensorHom_toTensorSheafMixed, sectionTypesMap_sheafificationAdjunction_unit]
  exact isLocallyInjective_toSheafify_sectionTypes _

/-- The comparison of the objectwise tensor product with raised sections with its
sheafification is locally surjective on sections. -/
public theorem isLocallySurjective_toTensorSheafMixed :
    Presheaf.IsLocallySurjective J (sectionTypesMap (toTensorSheafMixed α F G).uliftTensorHom) := by
  rw [uliftTensorHom_toTensorSheafMixed, sectionTypesMap_sheafificationAdjunction_unit]
  exact isLocallySurjective_toSheafify_sectionTypes _

/-- **Stacks 06WN(2).**  The sheafification of the universe lift of the objectwise tensor
product of two presheaves of modules is their tensor product in the category of sheaves of
modules for *every* topology finer than the one it is formed on: a bilinear map into a presheaf
of modules whose sections form a sheaf for the finer topology factors through the pure-tensor
map uniquely.  The two sources have sections in independent universes `m` and `n`, and the
tensor product has sections in `max u m n`, where `u` is the universe of the coefficient
rings. -/
public theorem existsUnique_hom_toTensorSheafMixed {K : GrothendieckTopology C} (hJK : J ≤ K)
    {H : PresheafOfModules.{max u m n} (R ⋙ forget₂ CommRingCat RingCat)}
    (hH : Presheaf.IsSheaf K (sectionTypes H)) (b : BilinearMap R F G H) :
    ∃! f : (PresheafOfModules.sheafification α ⋙ SheafOfModules.forget Rsh ⋙
        PresheafOfModules.restrictScalars α).obj ((tensorObj F G).uliftSections.{u}) ⟶ H,
      ∀ (U : Cᵒᵖ) (x : F.obj U) (y : G.obj U),
        f.app U ((toTensorSheafMixed α F G).app U x y) = b.app U x y :=
  existsUnique_hom_ulift_of_le hJK (toTensorSheafMixed α F G)
    (isLocallyInjective_toTensorSheafMixed α F G)
    (isLocallySurjective_toTensorSheafMixed α F G) hH b

end

end Stacks.Modules

namespace AlgebraicGeometry.FibredSite

open Stacks.Modules
open Stacks.SheafOfModules.TensorSheafification (structureRingPresheaf)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- The comparison of the ring presheaf underlying the commutative structure sheaf of an
associated site of the fibred category with the coefficient sheaf of rings of that site.  Both
are the ring presheaf obtained by restricting the global-functions presheaf of the big site
along the structure functor, so the comparison is the identity. -/
public noncomputable abbrev structureComparison (τ : SiteKind) :
    (structureSheaf B S hS p hp τ).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⟶
      (ringStructureSheafCore B S hS p hp τ).obj :=
  𝟙 _

/-- The comparison of coefficient rings on an associated site is locally injective. -/
public theorem isLocallyInjective_structureComparison (τ : SiteKind) :
    Presheaf.IsLocallyInjective (BigFppfOver.associatedTopology B S hS p τ)
      (structureComparison B S hS p hp τ) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h ↦ h

/-- The comparison of coefficient rings on an associated site is locally surjective. -/
public theorem isLocallySurjective_structureComparison (τ : SiteKind) :
    Presheaf.IsLocallySurjective (BigFppfOver.associatedTopology B S hS p τ)
      (structureComparison B S hS p hp τ) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ x ↦ ⟨x, rfl⟩

variable [EssentiallySmall.{u} 𝒳]

/-- An essentially `u`-small category is essentially `max u t`-small. -/
private theorem essentiallySmall_max (𝒳 : Type v) [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳] :
    EssentiallySmall.{max u t} 𝒳 :=
  essentiallySmall_lift.{t, u, v, u} 𝒳

/-- Sheafification into abelian groups with sections in any universe containing that of the
coefficient rings exists on each associated site of an essentially small category fibred in
groupoids over the big fppf category of schemes over `S`.  The universe of the sections need not
contain the universe of the objects of the fibred category. -/
public theorem hasWeakSheafify_associatedTopology_above (τ : SiteKind) :
    HasWeakSheafify (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{max u t} :=
  have := essentiallySmall_max.{u, v, t} 𝒳
  hasWeakSheafify_addCommGrpCat_of_essentiallySmall.{max u t, v, u} _

/-- Weak equivalences of presheaves of abelian groups with sections in any universe containing
that of the coefficient rings are the locally bijective maps, on each associated site of an
essentially small category fibred in groupoids.  The universe of the sections need not contain
the universe of the objects of the fibred category. -/
public theorem wEqualsLocallyBijective_associatedTopology_above (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS p τ).WEqualsLocallyBijective
      AddCommGrpCat.{max u t} :=
  have := essentiallySmall_max.{u, v, t} 𝒳
  wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall.{max u t, v, u} _

/-- The tensor product of presheaves of modules with sections in independent universes on an
associated site of the fibred category, as a bifunctor landing in sheaves of modules: the
sheafification, for the inherited topology, of the universe lift of the objectwise tensor
product.  The two sources have sections in independent universes `m` and `n` and the result has
sections in `max u m n`, where `u` is the universe of the coefficient rings. -/
public noncomputable def tensorSheafBifunctorMixed (τ : SiteKind) :
    PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ).obj ⥤
      PresheafOfModules.{n} (ringStructureSheafCore B S hS p hp τ).obj ⥤
        SheafOfModules.{max u m n} (ringStructureSheafCore B S hS p hp τ) :=
  have := isLocallyInjective_structureComparison B S hS p hp τ
  have := isLocallySurjective_structureComparison B S hS p hp τ
  have := hasWeakSheafify_associatedTopology_above.{u, v, max m n} B S hS p τ
  have := wEqualsLocallyBijective_associatedTopology_above.{u, v, max m n} B S hS p τ
  Stacks.Modules.tensorSheafBifunctorMixed (structureComparison B S hS p hp τ)

/-- The tensor product of two sheaves of modules with sections in independent universes on an
associated site of the fibred category: the sheafification, for the inherited topology, of the
universe lift of their objectwise tensor product. -/
public noncomputable def tensorSheafMixed (τ : SiteKind)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ))
    (G : SheafOfModules.{n} (ringStructureSheafCore B S hS p hp τ)) :
    SheafOfModules.{max u m n} (ringStructureSheafCore B S hS p hp τ) :=
  ((tensorSheafBifunctorMixed B S hS p hp τ).obj F.val).obj G.val

/-- The pure-tensor bilinear map of two sheaves of modules with sections in independent
universes on an associated site of the fibred category into their tensor product. -/
public noncomputable def toTensorSheafMixed (τ : SiteKind)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ))
    (G : SheafOfModules.{n} (ringStructureSheafCore B S hS p hp τ)) :
    Stacks.Modules.BilinearMap (structureSheaf B S hS p hp τ).obj F.val G.val
      (tensorSheafMixed B S hS p hp τ F G).val :=
  have := isLocallyInjective_structureComparison B S hS p hp τ
  have := isLocallySurjective_structureComparison B S hS p hp τ
  have := hasWeakSheafify_associatedTopology_above.{u, v, max m n} B S hS p τ
  have := wEqualsLocallyBijective_associatedTopology_above.{u, v, max m n} B S hS p τ
  Stacks.Modules.toTensorSheafMixed (structureComparison B S hS p hp τ) F.val G.val

/-- **Stacks 06WN(2).**  The tensor product of two sheaves of modules with sections in
independent universes, formed on any one of the five associated sites of the fibred category, is
already their tensor product in the category of sheaves of modules for *every* topology finer
than that one: every bilinear map into a presheaf of modules whose sections form a sheaf for the
finer topology factors through the pure-tensor map uniquely.  The coefficient ring presheaf is
the same for all five topologies, so the two sides of the factorization are stated over one and
the same presheaf of rings.  The sources have sections in `m` and `n` and the tensor product has
sections in `max u m n`, where `u` is the universe of the coefficient rings. -/
public theorem existsUnique_hom_tensorSheafMixed (τ : SiteKind)
    {K : GrothendieckTopology 𝒳} (hJK : BigFppfOver.associatedTopology B S hS p τ ≤ K)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ))
    (G : SheafOfModules.{n} (ringStructureSheafCore B S hS p hp τ))
    {H : PresheafOfModules.{max u m n}
      (structureRingPresheaf (structureSheaf B S hS p hp τ).obj)}
    (hH : Presheaf.IsSheaf K (Stacks.Modules.sectionTypes H))
    (b : Stacks.Modules.BilinearMap (structureSheaf B S hS p hp τ).obj F.val G.val H) :
    ∃! f : (tensorSheafMixed B S hS p hp τ F G).val ⟶ H,
      ∀ (U : 𝒳ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
        f.app U ((toTensorSheafMixed B S hS p hp τ F G).app U x y) = b.app U x y :=
  have := isLocallyInjective_structureComparison B S hS p hp τ
  have := isLocallySurjective_structureComparison B S hS p hp τ
  have := hasWeakSheafify_associatedTopology_above.{u, v, max m n} B S hS p τ
  have := wEqualsLocallyBijective_associatedTopology_above.{u, v, max m n} B S hS p τ
  Stacks.Modules.existsUnique_hom_toTensorSheafMixed (structureComparison B S hS p hp τ)
    F.val G.val hJK hH b

/-- The presheaf of sections of a sheaf of abelian groups on an associated site of an
essentially small category fibred in groupoids is a sheaf of sets, at any universe of sections
containing that of the coefficient rings. -/
public theorem hasSheafCompose_associatedTopology_above (τ : SiteKind) :
    (BigFppfOver.associatedTopology B S hS p τ).HasSheafCompose
      (forget AddCommGrpCat.{max u t}) :=
  have := essentiallySmall_max.{u, v, t} 𝒳
  hasSheafCompose_forget_addCommGrpCat_of_essentiallySmall.{max u t, v, u} _

/-- **Stacks 06WN(2).**  The tensor product of two sheaves of modules with sections in
independent universes, formed on an associated site of the fibred category, is their tensor
product in the category of sheaves of modules on that same site: every bilinear map into a sheaf
of modules there factors through the pure-tensor map uniquely, by a morphism of sheaves of
modules.  The sources have sections in `m` and `n` and the tensor product has sections in
`max u m n`, where `u` is the universe of the coefficient rings. -/
public theorem existsUnique_hom_tensorSheafMixed_sheaf (τ : SiteKind)
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ))
    (G : SheafOfModules.{n} (ringStructureSheafCore B S hS p hp τ))
    (H : SheafOfModules.{max u m n} (ringStructureSheafCore B S hS p hp τ))
    (b : Stacks.Modules.BilinearMap (structureSheaf B S hS p hp τ).obj F.val G.val H.val) :
    ∃! f : tensorSheafMixed B S hS p hp τ F G ⟶ H,
      ∀ (U : 𝒳ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
        f.val.app U ((toTensorSheafMixed B S hS p hp τ F G).app U x y) = b.app U x y := by
  have hH : Presheaf.IsSheaf (BigFppfOver.associatedTopology B S hS p τ)
      (Stacks.Modules.sectionTypes H.val) :=
    (hasSheafCompose_associatedTopology_above.{u, v, max m n} B S hS p τ).isSheaf _ H.isSheaf
  obtain ⟨g, hg, huniq⟩ :=
    existsUnique_hom_tensorSheafMixed B S hS p hp τ le_rfl F G hH b
  exact ⟨⟨g⟩, hg, fun f hf ↦ SheafOfModules.hom_ext (huniq f.val hf)⟩

/-- **Stacks 06WN(2).**  Restricted to a pair of quasi-coherent modules with sections in
independent universes, the tensor product formed on an associated site of the fibred category is
the tensor product in the ambient category of sheaves of modules on that site: every bilinear
map into a sheaf of modules there has a unique linear factorization through the pure-tensor map.
This is the universal property the source asserts of the common tensor product on the Zariski,
étale and fppf sites; it is proved here for all five associated sites, and the factorization is
tested against every sheaf of modules, not only the quasi-coherent ones. -/
@[stacks 06WN "tensor_products", stacks 06WV "tensor_product"]
public theorem existsUnique_hom_tensorSheafMixed_quasicoherent (τ : SiteKind)
    (F : quasicoherentModules.{u, v, u, m} B S hS p hp)
    (G : quasicoherentModules.{u, v, u, n} B S hS p hp)
    (H : SheafOfModules.{max u m n} (ringStructureSheafCore B S hS p hp τ))
    (b : Stacks.Modules.BilinearMap (structureSheaf B S hS p hp τ).obj
      F.obj.val G.obj.val H.val) :
    ∃! f : tensorSheafMixed B S hS p hp τ ((toSiteModules B S hS p hp τ).obj F)
        ((toSiteModules B S hS p hp τ).obj G) ⟶ H,
      ∀ (U : 𝒳ᵒᵖ) (x : F.obj.val.obj U) (y : G.obj.val.obj U),
        f.val.app U ((toTensorSheafMixed B S hS p hp τ
          ((toSiteModules B S hS p hp τ).obj F)
          ((toSiteModules B S hS p hp τ).obj G)).app U x y) = b.app U x y :=
  existsUnique_hom_tensorSheafMixed_sheaf B S hS p hp τ
    ((toSiteModules B S hS p hp τ).obj F) ((toSiteModules B S hS p hp τ).obj G) H b

end AlgebraicGeometry.FibredSite

end
