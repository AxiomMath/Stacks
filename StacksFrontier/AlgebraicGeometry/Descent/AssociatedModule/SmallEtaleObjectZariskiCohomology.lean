module

public import StacksFrontier.Algebra.Homology.RightDerivedEdgeComposition
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineAcyclic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleObjDerivation
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiQuasicoherentSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsUnit
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSectionTransfer
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedObjectRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.PushforwardCohomologyCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.LowDegreeSequence

/-!
# Étale cohomology over an object of the small étale site is Zariski cohomology

Let `S` be a scheme in a big étale site `B`, let `U` be an object of the small étale site of `S`,
with scheme `Y` and structure morphism `f : Y ⟶ S`, and let `H` be a quasi-coherent `𝒪`-module on
the small étale site of `S` — for instance `𝓕ᵃ` for a quasi-coherent `𝒪_S`-module `𝓕`.  This file
proves that the étale cohomology of `H` over `U` is the Zariski cohomology of `Y` with
coefficients in the restriction of `H` to the opens of `Y`,

  `Hᵖ(U, H) ≅ Hᵖ(Y, H|_{Y_Zar})`,

naturally in `U`, and that for `H = 𝓕ᵃ` the restriction is `f^*𝓕`.  This is
[Stacks, Tag 03P2] read at an arbitrary object of the small étale site rather than at the whole
scheme, together with its functoriality; it is the input that turns the presheaf
`V ↦ Hᵖ(X ×_Y V, 𝓕ᵃ)` of [Stacks, Tag 03Q8] into Zariski cohomology in the proof of
[Stacks, Tag 071N].

The opens of `Y` sit inside the small étale site of `S` through
`AlgebraicGeometry.SmallEtale.objOpensFunctor`, `W ↦ (W ↪ Y ⟶ S)`.  Restriction along it is
left exact and preserves injective abelian sheaves, and its higher direct images vanish on a
quasi-coherent `H`: they are the sheafifications of the cohomology over the objects `W`, which
vanishes over the affine opens `W`, and those cover.  The comparison is then the edge morphism
of the restriction followed by sections over `⊤`, which is invertible in every degree
(`Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso`), followed by the identification of `⊤`,
read in the small étale site of `S`, with `U`.

For a morphism `h : U₁ ⟶ U₂` the open `h⁻¹(V)` of `Y₁` maps to the open `V` of `Y₂` over `S`,
which gives an `h`-map from the restriction of an abelian sheaf to `Y₂` to the direct image of
its restriction to `Y₁`, and with it the pullback map of [Stacks, Tag 01FA] on Zariski
cohomology.  The comparison carries the restriction maps of étale cohomology to these pullback
maps; this is the pasting law of edge morphisms of
`StacksFrontier/Algebra/Homology/RightDerivedEdgeComposition.lean`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.objOpensFunctor`: the small Zariski site of the scheme of `U`
  inside the small étale site of `S`, and `AlgebraicGeometry.SmallEtale.objOpensPushforward` the
  restriction of abelian sheaves along it.
* `AlgebraicGeometry.SmallEtale.objOpensPushforwardMap` and
  `AlgebraicGeometry.SmallEtale.objOpensCohomologyMap`: the `h`-map and the pullback map on
  Zariski cohomology attached to a morphism `h` of the small étale site, for an arbitrary abelian
  sheaf.
* `AlgebraicGeometry.SmallEtale.rightDerivedSectionsObjOpensPushforwardIso`: the comparison
  `Hᵖ(Y, H|_{Y_Zar}) ≅ Hᵖ(U, H)` for a quasi-coherent `𝒪`-module `H`.
* `AlgebraicGeometry.SmallEtale.objOpensPushforwardAssociatedModuleIso`: `(𝓕ᵃ)|_{Y_Zar} ≅ f^*𝓕`
  on underlying abelian sheaves, built from the sections of pullbacks of Stacks 03DS.
* `AlgebraicGeometry.SmallEtale.objModuleMap` and
  `AlgebraicGeometry.SmallEtale.objPullbackCohomologyMap`: the `h`-map
  `f₂^*𝓕 ⟶ h_* f₁^*𝓕` (unit of `h^* ⊣ h_*` and `h^* f₂^* ≅ f₁^*`) and the pullback map
  `Hᵖ(Y₂, f₂^*𝓕) ⟶ Hᵖ(Y₁, f₁^*𝓕)` it induces.
* `AlgebraicGeometry.SmallEtale.objCohomologyAssociatedModuleIso`: **[Stacks, Tag 03P2] at an
  object of the small étale site**, `Hᵖ(Y, f^*𝓕) ≅ Hᵖ(U, 𝓕ᵃ)`.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_sheafSections_of_isAffine`: the higher
  cohomology of a quasi-coherent `𝒪`-module vanishes over affine objects, as right derived
  functors of sections of the underlying abelian sheaf.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_objOpensPushforward`: the higher direct
  images of the restriction to the small Zariski site of an object vanish.
* `AlgebraicGeometry.SmallEtale.rightDerivedSectionsObjOpensPushforwardIso_hom_naturality`: the
  comparison carries restriction maps to the pullback maps `objOpensCohomologyMap`.
* `AlgebraicGeometry.SmallEtale.objOpensPushforwardMap_app_comp_associatedModuleIso`: under
  `(𝓕ᵃ)|_{Y_i} ≅ f_i^*𝓕` the `h`-map of `𝓕ᵃ` is the `h`-map `objModuleMap` of `𝓕`.
* `AlgebraicGeometry.SmallEtale.objCohomologyAssociatedModuleIso_hom_naturality`: **the
  comparison of Tag 03P2 at objects is natural in the object**, restriction of étale cohomology
  corresponding to the pullback map `objPullbackCohomologyMap` of Zariski cohomology.

## Implementation notes

Cohomology on both sides is the right derived functor of sections of abelian sheaves, at the
morphism universe `u` of the small étale site, which is the cohomology the presheaf of
[Stacks, Tag 03Q8] (`Stacks.HigherDirectImage.preimageCohomologyPresheaf`) evaluates to.  The
vanishing over affine objects is read off the `Ext`-group statement of
`AlgebraicGeometry.SmallEtale.isZero_sheafH'_restrict_fpqcOverAssociatedSheaf`, whose `Ext`
universe is the object universe `u + 1`; the change of `Ext` universe is a bijection, so the
vanishing descends to `u`, where `Ext` and right derived sections agree.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Higher cohomology of a quasi-coherent module vanishes on affine objects -/

/-- **The higher cohomology of the abelian sheaf underlying a quasi-coherent `𝒪`-module on the
small étale site vanishes on affine objects**, in the form of the right derived functors of the
sections over the object. -/
public theorem isZero_rightDerived_sheafSections_of_isAffine
    (H : SheafOfModules.{u} (structureSheaf B S hS)) (hH : H.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS) (hV : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V)) (p : ℕ)
    (hp : 0 < p) :
    IsZero ((((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op V)).rightDerived
      p).obj ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H)) := by
  let : ((restrictModule B S hS).obj H).IsQuasicoherent :=
    isQuasicoherent_restrictModule B S hS H hH
  let : HasExt.{u + 1} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
    HasExt.standard _
  have h₁ : IsZero (Sheaf.H'.{u + 1}
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) p V) :=
    (isZero_sheafH'_restrict_fpqcOverAssociatedSheaf B S hS
      ((restrictModule B S hS).obj H) V hV p hp).of_iso
      (((Sheaf.cohomologyPresheafFunctor (topology B S hS) p).mapIso
        (toSheafIsoRestrictFpqcOverAssociatedSheaf B S hS H hH)).app (op V))
  let : HasExt.{u} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
    Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite _
  have h₂ : IsZero (Sheaf.H'.{u}
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) p V) := by
    rw [AddCommGrpCat.isZero_iff_subsingleton] at h₁ ⊢
    let e : ↑(Sheaf.H'.{u} ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) p V) ≃
        ↑(Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) p V) :=
      Abelian.Ext.chgUniv
    exact @Equiv.subsingleton _ _ e h₁
  exact h₂.of_iso (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u}
    (topology B S hS) _ p V).symm

variable (U : SmallEtale B S hS)

/-! ### The small Zariski site of an object, inside the small étale site -/

/-- The small Zariski site of the scheme `Y` of an object `U` of the small étale site of `S`,
inside the small étale site of `S`: an open `W` of `Y` goes to `W ↪ Y ⟶ S`. -/
public noncomputable abbrev objOpensFunctor : (objScheme B S hS U).Opens ⥤ SmallEtale B S hS :=
  objToSmallEtaleOver B S hS U ⋙ Over.forget U

/-- The small Zariski site of the scheme of `U` is continuous into the small étale site of
`S`. -/
public instance isContinuous_objOpensFunctor : (objOpensFunctor B S hS U).IsContinuous
    (Opens.grothendieckTopology ↥(objScheme B S hS U)) (topology B S hS) :=
  Functor.isContinuous_comp _ _ _ ((topology B S hS).over U) _

/-- Restriction of abelian sheaves on the small étale site of `S` to the small Zariski site of
the scheme of `U`. -/
public noncomputable abbrev objOpensPushforward :
    Sheaf (topology B S hS) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥(objScheme B S hS U)) AddCommGrpCat.{u} :=
  (objOpensFunctor B S hS U).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥(objScheme B S hS U)) (topology B S hS)

/-- Restriction to the small Zariski site of the scheme of `U` preserves injective abelian
sheaves: its left adjoint is exact, the opens having fibre products and equalizers which the
inclusion preserves. -/
public instance preservesInjectiveObjects_objOpensPushforward :
    (objOpensPushforward B S hS U).PreservesInjectiveObjects :=
  Stacks.Cohomology.BiggerSite.preservesInjectiveObjects_sheafPushforwardContinuous _ _ _

/-- The open `⊤` of the scheme of `U`, read in the small étale site of `S`, is `U` itself. -/
public noncomputable def objOpensFunctorTopIso : (objOpensFunctor B S hS U).obj ⊤ ≅ U :=
  (Over.forget U).mapIso
    ((isTerminalObjToSmallEtaleOverTop B hS U).uniqueUpToIso Over.mkIdTerminal)

/-- **The higher direct images of a quasi-coherent `𝒪`-module along the small Zariski site of an
object vanish.**  The affine opens of the scheme of `U` cover it, and over an affine open the
higher cohomology on the small étale site vanishes. -/
public theorem isZero_rightDerived_objOpensPushforward
    (H : SheafOfModules.{u} (structureSheaf B S hS)) (hH : H.IsQuasicoherentOnSite) (p : ℕ)
    (hp : 0 < p) :
    IsZero (((objOpensPushforward B S hS U).rightDerived p).obj
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H)) := by
  refine Stacks.Cohomology.HigherDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (objOpensFunctor B S hS U) p _ (fun V ↦ ?_)
  refine ⟨affineOpensPresieve (objScheme B S hS U) V,
    generate_affineOpensPresieve_mem (objScheme B S hS U) V, fun W g hg ↦ ?_⟩
  exact isZero_rightDerived_sheafSections_of_isAffine B S hS H hH
    ((objOpensFunctor B S hS U).obj W) (show IsAffineOpen W from hg) p hp

/-- Sections over `⊤` of the restriction of an abelian sheaf to the small Zariski site of the
scheme of `U` are its sections over `U`. -/
public def objOpensPushforwardSectionsIso :
    objOpensPushforward B S hS U ⋙
        (sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U)) AddCommGrpCat.{u}).obj
          (op ⊤) ≅
      (sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op U) :=
  Stacks.Cohomology.BiggerSite.sheafPushforwardContinuousCompSheafSectionsIso _ _
      (objOpensFunctor B S hS U) AddCommGrpCat.{u} ⊤ ≪≫
    (sheafSections (topology B S hS) AddCommGrpCat.{u}).mapIso
      (objOpensFunctorTopIso B S hS U).op.symm

/-- **Cohomology over an object of the small étale site is Zariski cohomology of the
restriction**, for a quasi-coherent `𝒪`-module: the `p`-th right derived functor of sections
over `U` of the abelian sheaf underlying `H` is the `p`-th Zariski cohomology of its restriction to
the scheme of `U`.  The comparison is the edge morphism of the restriction followed by sections,
invertible because the higher direct images of the restriction vanish. -/
public def rightDerivedSectionsObjOpensPushforwardIso
    (H : SheafOfModules.{u} (structureSheaf B S hS)) (hH : H.IsQuasicoherentOnSite) (p : ℕ) :
    (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U)) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived p).obj
        ((objOpensPushforward B S hS U).obj ((SheafOfModules.toSheaf _).obj H)) ≅
      (((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) :=
  Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso (objOpensPushforward B S hS U)
      ((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U)) AddCommGrpCat.{u}).obj
        (op ⊤)) ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) p
      (fun q hq _ ↦ isZero_rightDerived_objOpensPushforward B S hS U H hH q hq) ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (objOpensPushforwardSectionsIso B S hS U) p).app _

/-! ### The restriction of `𝓕ᵃ`, read through the sections of pullbacks -/

/-- An open `V` of the scheme `Y` of `U`, read as a scheme over `S` through `V ↪ Y ⟶ S`, with
its open immersion into `Y` as an arrow of schemes over `S`. -/
public abbrev objOpensOverHom (V : (objScheme B S hS U).Opens) :
    (toOver B S hS).obj ((objOpensFunctor B S hS U).obj V) ⟶ Over.mk (objHom B S hS U) :=
  Over.homMk V.ι rfl

/-- The arrow `objOpensOverHom` is an open immersion on underlying schemes. -/
public instance isOpenImmersion_objOpensOverHom_left (V : (objScheme B S hS U).Opens) :
    IsOpenImmersion (objOpensOverHom B S hS U V).left :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-- Sections of `(V ↪ Y ⟶ S)^*𝓕` over `V` are sections of `f^*𝓕` over `V`. -/
public noncomputable def objOpensSectionsMap (F : S.Modules) (V : (objScheme B S hS U).Opens) :
    Γ((Scheme.Modules.pullback ((toOver B S hS).obj ((objOpensFunctor B S hS U).obj V)).hom).obj F,
        (⊤ : V.toScheme.Opens)) ⟶ Γ((Scheme.Modules.pullback (objHom B S hS U)).obj F, V) :=
  Stacks.Sites.overSectionsMap F (Over.mk (objHom B S hS U)) (objOpensOverHom B S hS U V) ≫
    (((Scheme.Modules.pullback (objHom B S hS U)).obj F).presheaf.mapIso
      (eqToIso (Scheme.Opens.ι_image_top V).symm).op).hom

/-- The comparison of sections of pullbacks with sections of `f^*𝓕` is invertible. -/
public instance isIso_objOpensSectionsMap (F : S.Modules) (V : (objScheme B S hS U).Opens) :
    IsIso (objOpensSectionsMap B S hS U F V) :=
  IsIso.comp_isIso' (Stacks.Sites.isIso_overSectionsMap _ _ _) (Iso.isIso_hom _)

/-- An inclusion of opens of the scheme of `U`, read as an arrow of schemes over `S`, followed by
the open immersion of the larger open, is the open immersion of the smaller one. -/
public theorem toOver_map_objOpensFunctor_map_comp {V V' : (objScheme B S hS U).Opens}
    (i : V' ⟶ V) :
    (toOver B S hS).map ((objOpensFunctor B S hS U).map i) ≫ objOpensOverHom B S hS U V =
      objOpensOverHom B S hS U V' := by
  ext : 1
  exact Scheme.homOfLE_ι (objScheme B S hS U) (leOfHom i)

/-- **The comparison of sections of pullbacks with sections of `f^*𝓕` commutes with
restriction.** -/
public theorem pullbackSectionsMap_comp_objOpensSectionsMap (F : S.Modules)
    {V V' : (objScheme B S hS U).Opens} (i : V' ⟶ V) :
    pullbackSectionsMap F ((toOver B S hS).map ((objOpensFunctor B S hS U).map i)) ≫
        objOpensSectionsMap B S hS U F V' =
      objOpensSectionsMap B S hS U F V ≫
        ((Scheme.Modules.pullback (objHom B S hS U)).obj F).presheaf.map i.op := by
  have hk := toOver_map_objOpensFunctor_map_comp B S hS U i
  have : IsOpenImmersion ((toOver B S hS).map ((objOpensFunctor B S hS U).map i) ≫
      objOpensOverHom B S hS U V).left := by
    rw [hk]
    infer_instance
  have hle : ((toOver B S hS).map ((objOpensFunctor B S hS U).map i) ≫
      objOpensOverHom B S hS U V).left ''ᵁ ⊤ ≤ (objOpensOverHom B S hS U V).left ''ᵁ ⊤ :=
    Stacks.Sites.image_top_comp_le _ _
  have h := Stacks.Sites.pullbackSectionsMap_comp_overSectionsMap_comp F
    (Over.mk (objHom B S hS U)) (objOpensOverHom B S hS U V)
    ((toOver B S hS).map ((objOpensFunctor B S hS U).map i)) hle
  have key : ∀ (g' : (toOver B S hS).obj ((objOpensFunctor B S hS U).obj V') ⟶
      Over.mk (objHom B S hS U)) [IsOpenImmersion g'.left] (hg : g' = objOpensOverHom B S hS U V')
      (hA : V' = g'.left ''ᵁ ⊤),
      Stacks.Sites.overSectionsMap F (Over.mk (objHom B S hS U)) g' ≫
        ((Scheme.Modules.pullback (objHom B S hS U)).obj F).presheaf.map (eqToHom hA).op =
      objOpensSectionsMap B S hS U F V' := by
    rintro g' _ rfl hA
    rfl
  have hA : V' = ((toOver B S hS).map ((objOpensFunctor B S hS U).map i) ≫
      objOpensOverHom B S hS U V).left ''ᵁ ⊤ := by
    have hc : ⇑((toOver B S hS).map ((objOpensFunctor B S hS U).map i) ≫
        objOpensOverHom B S hS U V).left = ⇑(V'.ι) := by rw [hk]; rfl
    ext x
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.coe_opensRange, hc]
    exact (Iff.of_eq (congrArg (x ∈ ·) (Scheme.Opens.range_ι V'))).symm
  rw [← key _ hk hA, ← Category.assoc, h]
  simp only [objOpensSectionsMap, Category.assoc, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  exact congrArg (fun t => Stacks.Sites.overSectionsMap F (Over.mk (objHom B S hS U))
    (objOpensOverHom B S hS U V) ≫ t) (Stacks.Sites.presheaf_map_comp_eq₂ _ _ _ _ _)

/-- The inverse of `AlgebraicGeometry.SmallEtale.objOpensSectionsMap`: a section of `f^*𝓕` over
an open `V` pulls back to a global section of `(V ↪ Y)^*f^*𝓕 = (V ↪ Y ⟶ S)^*𝓕`. -/
public noncomputable def objOpensSectionsInv (F : S.Modules) (V : (objScheme B S hS U).Opens) :
    Γ((Scheme.Modules.pullback (objHom B S hS U)).obj F, V) ⟶
      Γ((Scheme.Modules.pullback
          ((toOver B S hS).obj ((objOpensFunctor B S hS U).obj V)).hom).obj F,
        (⊤ : V.toScheme.Opens)) :=
  pullbackSectionHom V.ι ((Scheme.Modules.pullback (objHom B S hS U)).obj F) V ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) ≫
    (Stacks.Sites.pullbackCompIso F V.ι (objHom B S hS U) _ rfl).hom.app ⊤

/-- `AlgebraicGeometry.SmallEtale.objOpensSectionsInv` is a right inverse of
`AlgebraicGeometry.SmallEtale.objOpensSectionsMap`: pulling a section back to the open subscheme
and restricting it back to the open is the identity. -/
public theorem objOpensSectionsInv_comp_objOpensSectionsMap (F : S.Modules)
    (V : (objScheme B S hS U).Opens) :
    objOpensSectionsInv B S hS U F V ≫ objOpensSectionsMap B S hS U F V = 𝟙 _ := by
  set M := (Scheme.Modules.pullback (objHom B S hS U)).obj F
  have hu := congrArg (fun t => Scheme.Modules.Hom.app t V)
    (Stacks.Sites.unit_restrictFunctorIsoPullback_inv V.ι M)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at hu
  ext s
  have hpc : ∀ x, ((Stacks.Sites.pullbackCompIso F V.ι (objHom B S hS U) _ rfl).inv.app ⊤)
      (((Stacks.Sites.pullbackCompIso F V.ι (objHom B S hS U) _ rfl).hom.app ⊤) x) = x := by
    intro x
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
    rfl
  have hn := ConcreteCategory.congr_hom
    (((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app M).mapPresheaf.naturality
      (homOfLE (Scheme.Opens.top_le_ι_preimage (U := V) (V := V) le_rfl)).op)
    ((((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).app V) s)
  have hu' := ConcreteCategory.congr_hom hu s
  change (M.presheaf.map _) (((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app M).app ⊤
    (((Stacks.Sites.pullbackCompIso F V.ι (objHom B S hS U) _ rfl).inv.app ⊤)
      (((Stacks.Sites.pullbackCompIso F V.ι (objHom B S hS U) _ rfl).hom.app ⊤)
        (((Scheme.Modules.pullback V.ι).obj M).presheaf.map _
          ((((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).app V) s))))) = s
  rw [hpc]
  simp only at hn
  refine (congrArg (ConcreteCategory.hom (M.presheaf.map (eqToIso _).op.hom)) hn).trans ?_
  change (M.presheaf.map _) ((M.presheaf.map _) (((Scheme.Modules.restrictFunctorIsoPullback
    V.ι).inv.app M).app (V.ι ⁻¹ᵁ V)
      ((((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).app V) s))) = s
  refine (congrArg (fun z => (ConcreteCategory.hom (M.presheaf.map (eqToIso
    (Scheme.Opens.ι_image_top V).symm).op.hom)) ((ConcreteCategory.hom (M.presheaf.map
      ((Scheme.Hom.opensFunctor V.ι).map (homOfLE (Scheme.Opens.top_le_ι_preimage (U := V)
        (V := V) le_rfl))).op)) z)) hu').trans ?_
  refine (congrArg (ConcreteCategory.hom (M.presheaf.map (eqToIso
    (Scheme.Opens.ι_image_top V).symm).op.hom))
    (Stacks.Sites.presheaf_map_apply_comp M _ _ (homOfLE (le_of_eq
      (Scheme.Opens.ι_image_top V))) s)).trans ?_
  refine (Stacks.Sites.presheaf_map_apply_comp M _ _ (𝟙 V) s).trans ?_
  rw [op_id, M.presheaf.map_id, ConcreteCategory.id_apply]

/-- `AlgebraicGeometry.SmallEtale.objOpensSectionsInv` is a left inverse of
`AlgebraicGeometry.SmallEtale.objOpensSectionsMap`, the latter being invertible. -/
public theorem objOpensSectionsMap_comp_objOpensSectionsInv (F : S.Modules)
    (V : (objScheme B S hS U).Opens) :
    objOpensSectionsMap B S hS U F V ≫ objOpensSectionsInv B S hS U F V = 𝟙 _ := by
  have : Mono (objOpensSectionsMap B S hS U F V) :=
    @IsIso.mono_of_iso _ _ _ _ _ (isIso_objOpensSectionsMap B S hS U F V)
  rw [← cancel_mono (objOpensSectionsMap B S hS U F V), Category.assoc,
    objOpensSectionsInv_comp_objOpensSectionsMap, Category.comp_id, Category.id_comp]

/-- Pasting two commuting squares: if `a ≫ b = d ≫ e` and `e ≫ c = f ≫ g`, then
`a ≫ b ≫ c = (d ≫ f) ≫ g`. -/
private theorem comp_comp_eq_of_comp_eq_of_comp_eq {C : Type*} [Category C] {A B X Y Z W : C}
    {a : A ⟶ B} {b : B ⟶ X} {c : X ⟶ Y} {d : A ⟶ Z} {e : Z ⟶ X} {f : Z ⟶ W} {g : W ⟶ Y}
    (h₁ : a ≫ b = d ≫ e) (h₂ : e ≫ c = f ≫ g) : a ≫ b ≫ c = (d ≫ f) ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- The identification of sections of `𝓕ᵃ` over the opens of the scheme of `U` with sections of
`f^*𝓕` commutes with restriction. -/
public theorem associatedModulePresheafIso_comp_objOpensSectionsMap_naturality (F : S.Modules)
    [F.IsQuasicoherent] {V V' : (objScheme B S hS U).Opens} (i : V' ⟶ V) :
    ((associatedModule B S hS).obj F).val.presheaf.map ((objOpensFunctor B S hS U).map i).op ≫
        (associatedModulePresheafIso B S hS F).hom.app (op ((objOpensFunctor B S hS U).obj V')) ≫
          objOpensSectionsMap B S hS U F V' =
      ((associatedModulePresheafIso B S hS F).hom.app (op ((objOpensFunctor B S hS U).obj V)) ≫
        objOpensSectionsMap B S hS U F V) ≫
          ((Scheme.Modules.pullback (objHom B S hS U)).obj F).presheaf.map i.op :=
  comp_comp_eq_of_comp_eq_of_comp_eq
    (associatedModulePresheafIso_hom_naturality B S hS F ((objOpensFunctor B S hS U).map i).op)
    (pullbackSectionsMap_comp_objOpensSectionsMap B S hS U F i)

/-- **The restriction of `𝓕ᵃ` to the small Zariski site of the scheme `Y` of `U` is the pullback
of `𝓕` along the structure morphism `f : Y ⟶ S` of `U`**, on underlying abelian sheaves:
`(𝓕ᵃ)|_{Y_Zar} ≅ f^*𝓕`.  Over an open `V` of `Y`, a section of `𝓕ᵃ` over `V ↪ Y ⟶ S` is a
section of the pullback of `𝓕` to `V` (Stacks 070S,
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso`), and that is a section of `f^*𝓕`
over `V` (`AlgebraicGeometry.SmallEtale.objOpensSectionsMap`). -/
public noncomputable def objOpensPushforwardAssociatedModuleIso (F : S.Modules)
    [F.IsQuasicoherent] :
    (objOpensPushforward B S hS U).obj
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj ((associatedModule B S hS).obj F)) ≅
      (SheafOfModules.toSheaf (objScheme B S hS U).ringCatSheaf).obj
        ((Scheme.Modules.pullback (objHom B S hS U)).obj F) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun V ↦ (associatedModulePresheafIso B S hS F).app
          (op ((objOpensFunctor B S hS U).obj V.unop)) ≪≫
        @asIso _ _ _ _ (objOpensSectionsMap B S hS U F V.unop)
          (isIso_objOpensSectionsMap B S hS U F V.unop))
      (fun {_ _} i ↦ associatedModulePresheafIso_comp_objOpensSectionsMap_naturality B S hS U F
        i.unop))

/-- **[Stacks, Tag 03P2] at an object of the small étale site**: for a quasi-coherent
`𝒪_S`-module `𝓕` and an object `U` of the small étale site of `S` with scheme `Y` and structure
morphism `f : Y ⟶ S`,

  `Hᵖ(Y, f^*𝓕) ≅ Hᵖ(U, 𝓕ᵃ)`,

Zariski cohomology of `Y` on the left and étale cohomology over `U` on the right, both as right
derived functors of sections of abelian sheaves. -/
public noncomputable def objCohomologyAssociatedModuleIso (F : S.Modules) [F.IsQuasicoherent]
    (p : ℕ) :
    (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U)) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived p).obj
        ((SheafOfModules.toSheaf (objScheme B S hS U).ringCatSheaf).obj
          ((Scheme.Modules.pullback (objHom B S hS U)).obj F)) ≅
      (((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op U)).rightDerived p).obj
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj ((associatedModule B S hS).obj F)) :=
  (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U)) AddCommGrpCat.{u}).obj
      (op ⊤)).rightDerived p).mapIso (objOpensPushforwardAssociatedModuleIso B S hS U F).symm ≪≫
    rightDerivedSectionsObjOpensPushforwardIso B S hS U _
      (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS F inferInstance) p

/-! ### Functoriality in the object -/

section Functoriality

variable {B S hS} {U₁ U₂ : SmallEtale B S hS} (h : U₁ ⟶ U₂)

/-- The morphism of schemes underlying a morphism of the small étale site. -/
public abbrev objMap : objScheme B S hS U₁ ⟶ objScheme B S hS U₂ := (toScheme B S hS).map h

/-- The range condition behind `objOpensMapHom`: the preimage of an open `V` under the morphism
of schemes underlying `h`, read over the scheme of `U₂`, has structure morphism with range in
`V`. -/
public theorem range_objOpensMap_le (V : (objScheme B S hS U₂).Opens) :
    Set.range ⇑(((localizationEquivalence B S hS U₂).inverse.obj ((Over.map h).obj
      ((objToSmallEtaleOver B S hS U₁).obj
        ((Opens.map (objMap h).base).obj V)))).obj.hom.hom) ⊆ (V : Set _) := by
  rintro x ⟨y, rfl⟩
  exact (show ↥((Opens.map (objMap h).base).obj V) from y).2

/-- The comparison `h⁻¹(V) ⟶ V` over `U₂`, for an open `V` of the scheme of `U₂`, read in the
localization of the small étale site at `U₂`. -/
public noncomputable def objOpensMapOverHom (V : (objScheme B S hS U₂).Opens) :
    (Over.map h).obj ((objToSmallEtaleOver B S hS U₁).obj ((Opens.map (objMap h).base).obj V)) ⟶
      (objToSmallEtaleOver B S hS U₂).obj V :=
  ((localizationEquivalence B S hS U₂).counitIso.app _).inv ≫
    (localizationEquivalence B S hS U₂).functor.map
      (homOfRangeLe B (objScheme B S hS U₂) (contains_objScheme B S hS U₂) V
        (range_objOpensMap_le h V))

/-- The comparison `h⁻¹(V) ⟶ V` over `U₂`, as a natural transformation of functors from the
small Zariski site of the scheme of `U₂` to the localization at `U₂`. -/
public noncomputable def objOpensMapOverNatTrans :
    Opens.map (objMap h).base ⋙ objToSmallEtaleOver B S hS U₁ ⋙ Over.map h ⟶
      objToSmallEtaleOver B S hS U₂ where
  app V := objOpensMapOverHom h V
  naturality _ V _ := Subsingleton.elim
    (h := subsingleton_hom_objToSmallEtaleOver B S hS U₂ _ V) _ _

/-- The comparison `h⁻¹(V) ⟶ V` in the small étale site of `S`, for an open `V` of the scheme of
`U₂`. -/
public noncomputable def objOpensMapNatTrans :
    Opens.map (objMap h).base ⋙ objOpensFunctor B S hS U₁ ⟶ objOpensFunctor B S hS U₂ :=
  Functor.whiskerRight (objOpensMapOverNatTrans h) (Over.forget U₂)

/-- Taking preimages under `h` and then including the small Zariski site of the scheme of `U₁`
is continuous into the small étale site of `S`. -/
public instance isContinuous_opensMap_comp_objOpensFunctor :
    (Opens.map (objMap h).base ⋙ objOpensFunctor B S hS U₁).IsContinuous
      (Opens.grothendieckTopology ↥(objScheme B S hS U₂)) (topology B S hS) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology ↥(objScheme B S hS U₁)) _

/-- **The `h`-map attached to a morphism `h : U₁ ⟶ U₂` of the small étale site.**  For an
abelian sheaf `E` on the small étale site of `S`, the restriction of `E` to the scheme of `U₂`
maps to the direct image along `h` of its restriction to the scheme of `U₁`: over an open `V`,
this is the restriction of sections of `E` along `h⁻¹(V) ⟶ V`. -/
public noncomputable def objOpensPushforwardMap :
    objOpensPushforward B S hS U₂ ⟶
      objOpensPushforward B S hS U₁ ⋙
        Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} (objMap h).base :=
  Functor.sheafPushforwardContinuousNatTrans (objOpensMapNatTrans h) AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥(objScheme B S hS U₂)) (topology B S hS)

/-- **The pullback map on Zariski cohomology attached to a morphism of the small étale site**,
`Hᵖ(Y₂, E|_{Y₂}) ⟶ Hᵖ(Y₁, E|_{Y₁})`: the map induced by the `h`-map `objOpensPushforwardMap`,
followed by the edge morphism `Hᵖ(Y₂, h_* -) ⟶ Hᵖ(Y₁, -)` of [Stacks, Tag 01FA]. -/
public noncomputable def objOpensCohomologyMap (E : Sheaf (topology B S hS) AddCommGrpCat.{u})
    (p : ℕ) :
    (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂)) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived p).obj ((objOpensPushforward B S hS U₂).obj E) ⟶
      (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₁)) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived p).obj ((objOpensPushforward B S hS U₁).obj E) :=
  (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂)) AddCommGrpCat.{u}).obj
      (op ⊤)).rightDerived p).map ((objOpensPushforwardMap h).app E) ≫
    (Stacks.Cohomology.LerayLowDegree.abelianEdgeMap.{u, 0} (objMap h).base p).app
      ((objOpensPushforward B S hS U₁).obj E)

/-- Under the identifications of `⊤` with the objects themselves, the comparison
`h⁻¹(⊤) ⟶ ⊤` is `h`.  Everything lives over `U₂`, where a morphism into the final object
`𝟙 U₂` is determined by its source. -/
public theorem comp_objOpensFunctorTopIso_inv :
    h ≫ (objOpensFunctorTopIso B S hS U₂).inv =
      (objOpensFunctorTopIso B S hS U₁).inv ≫ (objOpensMapNatTrans h).app ⊤ := by
  rw [← cancel_mono (objOpensFunctorTopIso B S hS U₂).hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  have key := Over.w ((Over.map h).map
      ((isTerminalObjToSmallEtaleOverTop B hS U₁).uniqueUpToIso Over.mkIdTerminal).inv ≫
    (objOpensMapOverNatTrans h).app ⊤ ≫
    ((isTerminalObjToSmallEtaleOverTop B hS U₂).uniqueUpToIso Over.mkIdTerminal).hom)
  simp only [Over.mk_hom, Over.map_obj_hom] at key
  exact key.symm

/-- The restriction of sections along `h`, read through the identifications of sections over `⊤`
of the restrictions with sections over the objects, is the `h`-map on sections over `⊤`. -/
public theorem objOpensPushforwardSectionsIso_hom_comp_map :
    (objOpensPushforwardSectionsIso B S hS U₂).hom ≫
        (sheafSections (topology B S hS) AddCommGrpCat.{u}).map h.op =
      (Functor.whiskerRight (objOpensPushforwardMap h)
          ((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂))
            AddCommGrpCat.{u}).obj (op ⊤)) ≫ (Functor.associator _ _ _).hom) ≫
        (objOpensPushforwardSectionsIso B S hS U₁).hom := by
  ext E : 2
  change E.obj.map _ ≫ E.obj.map _ = E.obj.map _ ≫ E.obj.map _
  exact (E.obj.map_comp _ _).symm.trans
    ((congrArg (fun k => E.obj.map k.op) (comp_objOpensFunctorTopIso_inv h)).trans
      (E.obj.map_comp _ _))

/-- **The comparison of étale cohomology over an object with Zariski cohomology of the
restriction is natural in the object.**  For a morphism `h : U₁ ⟶ U₂` of the small étale site,
the restriction map `Hᵖ(U₂, H) ⟶ Hᵖ(U₁, H)` of étale cohomology corresponds to the pullback map
`Hᵖ(Y₂, H|_{Y₂}) ⟶ Hᵖ(Y₁, H|_{Y₁})` of Zariski cohomology, `objOpensCohomologyMap`. -/
public theorem rightDerivedSectionsObjOpensPushforwardIso_hom_naturality
    (H : SheafOfModules.{u} (structureSheaf B S hS)) (hH : H.IsQuasicoherentOnSite) (p : ℕ) :
    (rightDerivedSectionsObjOpensPushforwardIso B S hS U₂ H hH p).hom ≫
        (NatTrans.rightDerived ((sheafSections (topology B S hS) AddCommGrpCat.{u}).map h.op)
          p).app ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) =
      objOpensCohomologyMap h ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) p ≫
        (rightDerivedSectionsObjOpensPushforwardIso B S hS U₁ H hH p).hom := by
  have hP := Stacks.Cohomology.RightDerivedEdge.edge_app_comp_rightDerived_whiskerRight
    (objOpensPushforward B S hS U₂) (objOpensPushforward B S hS U₁)
    (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} (objMap h).base)
    (objOpensPushforwardMap h)
    ((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂)) AddCommGrpCat.{u}).obj
      (op ⊤)) p ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H)
  have key := objOpensPushforwardSectionsIso_hom_comp_map (B := B) (S := S) (hS := hS) h
  simp only [rightDerivedSectionsObjOpensPushforwardIso, objOpensCohomologyMap, Iso.trans_hom,
    Iso.app_hom, Stacks.Cohomology.RightDerivedEdgeIso.edgeAppIso_hom, Category.assoc]
  change _ ≫ (NatTrans.rightDerived (objOpensPushforwardSectionsIso B S hS U₂).hom p).app _ ≫ _ =
    _ ≫ _ ≫ _ ≫ (NatTrans.rightDerived (objOpensPushforwardSectionsIso B S hS U₁).hom p).app _
  have step : NatTrans.rightDerived ((objOpensPushforwardSectionsIso B S hS U₂).hom ≫
      (sheafSections (topology B S hS) AddCommGrpCat.{u}).map h.op) p =
      NatTrans.rightDerived (Functor.whiskerRight (objOpensPushforwardMap h)
          ((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂))
            AddCommGrpCat.{u}).obj (op ⊤)) ≫ (Functor.associator _ _ _).hom) p ≫
        NatTrans.rightDerived (objOpensPushforwardSectionsIso B S hS U₁).hom p := by
    rw [key]
    exact NatTrans.rightDerived_comp _ _ p
  have h1 : (NatTrans.rightDerived (objOpensPushforwardSectionsIso B S hS U₂).hom p).app
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) ≫
      (NatTrans.rightDerived ((sheafSections (topology B S hS) AddCommGrpCat.{u}).map h.op) p).app
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) =
      (NatTrans.rightDerived (Functor.whiskerRight (objOpensPushforwardMap h)
          ((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂))
            AddCommGrpCat.{u}).obj (op ⊤)) ≫ (Functor.associator _ _ _).hom) p).app
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) ≫
      (NatTrans.rightDerived (objOpensPushforwardSectionsIso B S hS U₁).hom p).app
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) :=
    (NatTrans.congr_app (NatTrans.rightDerived_comp _ _ p)
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H)).symm.trans
      (NatTrans.congr_app step ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H))
  rw [h1]
  exact (Category.assoc _ _ _).symm.trans ((hP =≫ _).trans
    ((Category.assoc _ _ _).trans (congrArg (fun t => _ ≫ t) (Category.assoc _ _ _))))

/-- The morphism of schemes underlying `h` lies over `S`. -/
public theorem objMap_comp_objHom : objMap h ≫ objHom B S hS U₂ = objHom B S hS U₁ :=
  congrArg (fun k => k.hom) (Over.w h.hom)

/-- **The `h`-map of `𝓕`**, `f₂^*𝓕 ⟶ h_* f₁^*𝓕`: the unit of `h^* ⊣ h_*` followed by the
identification `h^* f₂^* 𝓕 ≅ f₁^*𝓕`. -/
public noncomputable def objModuleMap (F : S.Modules) :
    (Scheme.Modules.pullback (objHom B S hS U₂)).obj F ⟶
      (Scheme.Modules.pushforward (objMap h)).obj
        ((Scheme.Modules.pullback (objHom B S hS U₁)).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (objMap h)).unit.app _ ≫
    (Scheme.Modules.pushforward (objMap h)).map
      (Stacks.Sites.pullbackCompIso F (objMap h) (objHom B S hS U₂) (objHom B S hS U₁)
        (objMap_comp_objHom h)).hom

/-- The comparison `h⁻¹(V) ⟶ V`, on underlying schemes, commutes with the two open
immersions. -/
public theorem toScheme_map_objOpensMapNatTrans_app_comp (V : (objScheme B S hS U₂).Opens) :
    ((toOver B S hS).map ((objOpensMapNatTrans h).app V)).left ≫ V.ι =
      Scheme.Opens.ι ((Opens.map (objMap h).base).obj V) ≫ objMap h := by
  have hw := (toScheme B S hS).congr_map (Over.w (objOpensMapOverHom h V))
  simp only [Functor.map_comp, Over.map_obj_hom] at hw
  exact hw

/-- **The restriction maps of `𝓕ᵃ` along `h⁻¹(V) ⟶ V` are the `h`-map of `𝓕`**, read through
the transfer of sections of `f^*𝓕` to sections of pullbacks. -/
public theorem objOpensSectionsInv_comp_pullbackSectionsMap (F : S.Modules)
    (V : (objScheme B S hS U₂).Opens) :
    objOpensSectionsInv B S hS U₂ F V ≫
        pullbackSectionsMap F ((toOver B S hS).map ((objOpensMapNatTrans h).app V)) =
      (objModuleMap h F).app V ≫
        objOpensSectionsInv B S hS U₁ F ((Opens.map (objMap h).base).obj V) := by
  have hk := toScheme_map_objOpensMapNatTrans_app_comp h V
  have hm : (objModuleMap h F).app V =
      pullbackSectionHom (objMap h) ((Scheme.Modules.pullback (objHom B S hS U₂)).obj F) V
          ((Opens.map (objMap h).base).obj V) le_rfl ≫
        (Stacks.Sites.pullbackCompIso F (objMap h) (objHom B S hS U₂) (objHom B S hS U₁)
          (objMap_comp_objHom h)).hom.app ((Opens.map (objMap h).base).obj V) := by
    rw [pullbackSectionHom_preimage]
    rfl
  refine (congrArg (objOpensSectionsInv B S hS U₂ F V ≫ ·)
    (pullbackSectionsMap_eq_pullbackSectionHom F _ le_top)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (pullbackSectionHom_pullbackCompIso_comp F (objHom B S hS U₂) V.ι _ rfl
      _ _ (Over.w _) V ⊤ ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) le_top
      ((Category.assoc _ _ _).trans (Over.w _))).trans ?_
  refine (pullbackSectionHom_pullbackCompIso_congr F _ _ _ hk _ _
    ((Category.assoc _ _ _).trans (congrArg (Scheme.Opens.ι ((Opens.map (objMap h).base).obj V) ≫ ·)
      (objMap_comp_objHom h))) V ⊤ _
    (fun x _ => x.2)).trans ?_
  refine Eq.symm ((congrArg (· ≫ objOpensSectionsInv B S hS U₁ F
    ((Opens.map (objMap h).base).obj V)) hm).trans ?_)
  refine (Category.assoc _ _ _).trans ?_
  exact pullbackSectionHom_pullbackCompIso_comp F (objHom B S hS U₂) (objMap h) _
    (objMap_comp_objHom h) _ _ rfl V _ ⊤ le_rfl (Scheme.Opens.top_le_ι_preimage le_rfl) _

/-- `AlgebraicGeometry.SmallEtale.objOpensSectionsInv_comp_pullbackSectionsMap` read through the
comparison maps themselves. -/
public theorem pullbackSectionsMap_comp_objOpensSectionsMap_objMap (F : S.Modules)
    (V : (objScheme B S hS U₂).Opens) :
    pullbackSectionsMap F ((toOver B S hS).map ((objOpensMapNatTrans h).app V)) ≫
        objOpensSectionsMap B S hS U₁ F ((Opens.map (objMap h).base).obj V) =
      objOpensSectionsMap B S hS U₂ F V ≫ (objModuleMap h F).app V := by
  have hK := objOpensSectionsInv_comp_pullbackSectionsMap h F V
  have e₁ := objOpensSectionsMap_comp_objOpensSectionsInv B S hS U₂ F V
  have e₂ := objOpensSectionsInv_comp_objOpensSectionsMap B S hS U₁ F
    ((Opens.map (objMap h).base).obj V)
  exact ((Category.id_comp _).symm.trans (congrArg (· ≫ _) e₁.symm)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (objOpensSectionsMap B S hS U₂ F V ≫ ·)
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ objOpensSectionsMap B S hS U₁ F
          ((Opens.map (objMap h).base).obj V)) hK))).trans
        (congrArg (objOpensSectionsMap B S hS U₂ F V ≫ ·)
          ((Category.assoc _ _ _).trans ((congrArg ((objModuleMap h F).app V ≫ ·) e₂).trans
            (Category.comp_id _))))))

/-- **The `h`-map of `𝓕ᵃ` is the `h`-map of `𝓕`**: under the identifications
`(𝓕ᵃ)|_{Y_i} ≅ f_i^*𝓕`, the restriction of sections along `h⁻¹(V) ⟶ V` is the unit of
`h^* ⊣ h_*` followed by `h^* f₂^*𝓕 ≅ f₁^*𝓕`. -/
public theorem objOpensPushforwardMap_app_comp_associatedModuleIso (F : S.Modules)
    [F.IsQuasicoherent] :
    (objOpensPushforwardMap h).app
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj ((associatedModule B S hS).obj F)) ≫
      (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} (objMap h).base).map
        (objOpensPushforwardAssociatedModuleIso B S hS U₁ F).hom =
    (objOpensPushforwardAssociatedModuleIso B S hS U₂ F).hom ≫
      (SheafOfModules.toSheaf (objScheme B S hS U₂).ringCatSheaf).map (objModuleMap h F) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  change ((associatedModule B S hS).obj F).val.presheaf.map
      ((objOpensMapNatTrans h).app V.unop).op ≫
      (associatedModulePresheafIso B S hS F).hom.app
        (op ((objOpensFunctor B S hS U₁).obj ((Opens.map (objMap h).base).obj V.unop))) ≫
        objOpensSectionsMap B S hS U₁ F ((Opens.map (objMap h).base).obj V.unop) =
    ((associatedModulePresheafIso B S hS F).hom.app (op ((objOpensFunctor B S hS U₂).obj V.unop)) ≫
      objOpensSectionsMap B S hS U₂ F V.unop) ≫ (objModuleMap h F).app V.unop
  exact comp_comp_eq_of_comp_eq_of_comp_eq
    (associatedModulePresheafIso_hom_naturality B S hS F ((objOpensMapNatTrans h).app V.unop).op)
    (pullbackSectionsMap_comp_objOpensSectionsMap_objMap h F V.unop)

/-- **The pullback map on Zariski cohomology attached to a morphism of the small étale site**,
`Hᵖ(Y₂, f₂^*𝓕) ⟶ Hᵖ(Y₁, f₁^*𝓕)`: the map induced by the `h`-map
`AlgebraicGeometry.SmallEtale.objModuleMap` of `𝓕`, followed by the edge morphism
`Hᵖ(Y₂, h_* -) ⟶ Hᵖ(Y₁, -)`; this is the map of [Stacks, Tag 01FA]. -/
public noncomputable def objPullbackCohomologyMap (F : S.Modules) (p : ℕ) :
    (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂)) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived p).obj
        ((SheafOfModules.toSheaf (objScheme B S hS U₂).ringCatSheaf).obj
          ((Scheme.Modules.pullback (objHom B S hS U₂)).obj F)) ⟶
      (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₁)) AddCommGrpCat.{u}).obj
        (op ⊤)).rightDerived p).obj
        ((SheafOfModules.toSheaf (objScheme B S hS U₁).ringCatSheaf).obj
          ((Scheme.Modules.pullback (objHom B S hS U₁)).obj F)) :=
  (((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂)) AddCommGrpCat.{u}).obj
      (op ⊤)).rightDerived p).map
      ((SheafOfModules.toSheaf (objScheme B S hS U₂).ringCatSheaf).map (objModuleMap h F)) ≫
    (Stacks.Cohomology.LerayLowDegree.abelianEdgeMap.{u, 0} (objMap h).base p).app
      ((SheafOfModules.toSheaf (objScheme B S hS U₁).ringCatSheaf).obj
        ((Scheme.Modules.pullback (objHom B S hS U₁)).obj F))

/-- **[Stacks, Tag 03P2] at an object of the small étale site is natural in the object**: for a
morphism `h : U₁ ⟶ U₂` of the small étale site, the restriction map `Hᵖ(U₂, 𝓕ᵃ) ⟶ Hᵖ(U₁, 𝓕ᵃ)` of
étale cohomology corresponds to the pullback map `Hᵖ(Y₂, f₂^*𝓕) ⟶ Hᵖ(Y₁, f₁^*𝓕)` of Zariski
cohomology along the morphism of schemes underlying `h`. -/
public theorem objCohomologyAssociatedModuleIso_hom_naturality (F : S.Modules)
    [F.IsQuasicoherent] (p : ℕ) :
    (objCohomologyAssociatedModuleIso B S hS U₂ F p).hom ≫
        (NatTrans.rightDerived ((sheafSections (topology B S hS) AddCommGrpCat.{u}).map h.op)
          p).app ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj
            ((associatedModule B S hS).obj F)) =
      objPullbackCohomologyMap h F p ≫ (objCohomologyAssociatedModuleIso B S hS U₁ F p).hom := by
  have hG := objOpensPushforwardMap_app_comp_associatedModuleIso h F
  have hG' : (objOpensPushforwardAssociatedModuleIso B S hS U₂ F).inv ≫
      (objOpensPushforwardMap h).app
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj ((associatedModule B S hS).obj F)) =
      (SheafOfModules.toSheaf (objScheme B S hS U₂).ringCatSheaf).map (objModuleMap h F) ≫
        (Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u} (objMap h).base).map
          (objOpensPushforwardAssociatedModuleIso B S hS U₁ F).inv := by
    rw [Iso.inv_comp_eq]
    exact ((Iso.eq_comp_inv ((Stacks.Cohomology.LerayLowDegree.abelianPushforward.{u, u}
      (objMap h).base).mapIso (objOpensPushforwardAssociatedModuleIso B S hS U₁ F))).mpr hG).trans
      (Category.assoc _ _ _)
  have hN := rightDerivedSectionsObjOpensPushforwardIso_hom_naturality h _
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS F inferInstance) p
  have hE := (Stacks.Cohomology.LerayLowDegree.abelianEdgeMap.{u, 0} (objMap h).base p).naturality
    (objOpensPushforwardAssociatedModuleIso B S hS U₁ F).inv
  set R₂ := ((sheafSections (Opens.grothendieckTopology ↥(objScheme B S hS U₂))
    AddCommGrpCat.{u}).obj (op ⊤)).rightDerived p
  change (R₂.map (objOpensPushforwardAssociatedModuleIso B S hS U₂ F).inv ≫
      (rightDerivedSectionsObjOpensPushforwardIso B S hS U₂ _ _ p).hom) ≫ _ =
    (R₂.map ((SheafOfModules.toSheaf (objScheme B S hS U₂).ringCatSheaf).map (objModuleMap h F)) ≫
      _) ≫ _ ≫ (rightDerivedSectionsObjOpensPushforwardIso B S hS U₁ _ _ p).hom
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hN).trans ?_)
  change R₂.map _ ≫ (R₂.map _ ≫ _) ≫ _ = _
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (R₂.map_comp _ _).symm)))).trans ?_
  refine (congrArg (fun t => (R₂.map t ≫ _) ≫ _) hG').trans ?_
  refine (congrArg (fun t => (t ≫ _) ≫ _) (R₂.map_comp _ _)).trans ?_
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (R₂.map ((SheafOfModules.toSheaf (objScheme B S hS U₂).ringCatSheaf).map
    (objModuleMap h F)) ≫ ·) ?_
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hE)).trans (Category.assoc _ _ _)

end Functoriality

end AlgebraicGeometry.SmallEtale

end
