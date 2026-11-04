module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectAugmentationFunctorLeft
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfGuitart
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleUnitTopos
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictionOfUniv
public import StacksFrontier.CategoryTheory.Sites.Localization.SlicePostContinuous
public import StacksFrontier.CategoryTheory.Sites.Modules.RestrictionSquarePullbackMate
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomRingIso
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.OverSimplicialObjectTotalSite

/-!
# The unit of `h^* ⊣ h_*` on the components of a simplicial algebraic space

Let `U` be a simplicial object of a big fppf site of algebraic spaces with an augmentation
`a : U → X`, and `h : (Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total}) ⟶ (Sh(U_{spaces,étale}), 𝒪_U)`
the morphism of ringed topoi of Stacks 0DHC. Restricted to the component of degree `n`, the unit
`G ⟶ h_*h^*G` of an `𝒪_U`-module is the unit of the morphism of ringed sites
`((Spaces/U_n)_{fppf}, 𝒪) ⟶ ((U_n)_{spaces,étale}, 𝒪_{U_n})` at `G|_{U_n}` (Stacks 0DH0): the
degree square of `h` is Guitart exact.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.ringedSite`: the ringed site
  `(X_{spaces,étale}, 𝒪_X)` of a simplicial algebraic space.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfTotalRingedSite` and
  `.bigFppfTotalRingedSiteHom`: the ringed site `((Spaces/U)_{fppf,total}, 𝒪_{big,total})` and
  the morphism of ringed sites of `h`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.degreeRingedSiteHom`: the morphism of ringed
  sites of `h` in degree `n`, between the restrictions of the two ringed sites to degree `n`.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.bigFppfTotalRingedHom_eq_ringedToposHom`.
* `Space.SimplicialSpacesEtaleSite.isIso_restrictModules_map_bigFppfTotal_unit_iff`: the unit of
  `h` restricted to degree `n` is invertible exactly when the unit of the degree-`n` morphism is.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.isIso_degreeRingedSiteHom_unit_app_iff`: the
  unit of the degree-`n` morphism is that of `a_{U_n}` (Stacks 0DGM).
* `Space.SimplicialSpacesEtaleSite.isIso_of_forall_isIso_degreeRestrictModules_map`
  and `.isQuasicoherentOnSite_degreeRestrictModules_obj`: the restrictions to the degrees jointly
  reflect isomorphisms and preserve quasi-coherence.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.isIso_bigFppfTotalRingedHom_unit_app`: **the
  unit `G ⟶ h_*h^*G` is an isomorphism for a quasi-coherent `𝒪_U`-module `G`.**

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
* [Stacks Project, Tag 0DH0](https://stacks.math.columbia.edu/tag/0DH0)
* [Stacks Project, Tag 0DHC](https://stacks.math.columbia.edu/tag/0DHC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

section RingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The ringed site `(X_{spaces,étale}, 𝒪_X)` of a simplicial algebraic space; its ringed topos
is `ringedTopos X`. -/
abbrev ringedSite (X : SimplicialObject (AlgebraicSpaces B S hS)) :
    RingedSite.{u + 1, u + 1, u + 1} where
  C := SimplicialSpacesEtaleSite B S hS X
  J := topology X
  O := structureSheaf X

end RingedSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  (a : U ⟶ (SimplicialObject.const T.Spaces).obj X)

section Restriction

variable (n : SimplexCategory)

/-- The restriction of an `𝒪_X`-module to the spaces-étale site of `X_n`. -/
abbrev degreeRestrictModules :=
  (ringedSite U).restrictModulesAlongRestrictRestrictionSquarePullbackMate
    (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (degreeInclusion U n)

/-- **The restriction of a quasi-coherent `𝒪_X`-module to `X_n` is quasi-coherent**: the
inclusion of the spaces-étale site of `X_n` is continuous and cocontinuous (Stacks 03DM). -/
theorem isQuasicoherentOnSite_degreeRestrictModules_obj
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O))
    [hG : G.IsQuasicoherentOnSite] : ((degreeRestrictModules n).obj G).IsQuasicoherentOnSite := by
  have : ∀ V : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n)),
      (Over.post (X := V) (degreeInclusion U n)).IsContinuous
        ((SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))).over V)
        ((topology U).over ((degreeInclusion U n).obj V)) :=
    fun V ↦ Functor.isContinuous_overPost _ _ _ V
  exact Stacks.SheafOfModules.SiteTransport.isQuasicoherentOnSite_pushforward_ofUniv.{u + 1, u + 1,
    u + 1, u + 1, u + 1, u + 1} (J := topology U)
    (K := SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
    (R := Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).J)
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O)
    (degreeInclusion U n) (𝟙 _) (IsIso.id _) G hG

/-- **The restrictions to the degrees jointly reflect isomorphisms**: a morphism of
`𝒪_X`-modules is invertible as soon as its restriction to every `X_n` is, every object of
`X_{spaces,étale}` lying in a single degree. -/
theorem isIso_of_forall_isIso_degreeRestrictModules_map
    {G G' : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O)} (φ : G ⟶ G')
    (h : ∀ n, IsIso ((degreeRestrictModules (U := U) n).map φ)) : IsIso φ := by
  refine Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map φ ?_
  have hp : IsIso ((sheafToPresheaf _ _).map
      ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
        (ringedSite U).O)).map φ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    have h1 := h V.unop.degree
    have h2 : IsIso ((sheafToPresheaf _ _).map ((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
          (J := ((ringedSite U).restrictRestrictionSquarePullbackMate
            (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op V.unop.degree)))
            (degreeInclusion U V.unop.degree)).J)
          ((ringedSite U).restrictRestrictionSquarePullbackMate
            (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op V.unop.degree)))
            (degreeInclusion U V.unop.degree)).O)).map
        ((degreeRestrictModules (U := U) V.unop.degree).map φ))) := inferInstance
    rw [NatTrans.isIso_iff_isIso_app] at h2
    exact h2 (op V.unop.obj)
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

end Restriction

/-- The ringed site `((Spaces/U)_{fppf,total}, 𝒪_{big,total})`; its ringed topos is
`bigFppfTotalRingedTopos a`. -/
abbrev bigFppfTotalRingedSite : RingedSite.{u + 1, u + 1, u + 1} where
  C := Grothendieck (SimplicialOver.slices U)
  J := SimplicialOver.totalTopology T.topology U
  O := bigFppfTotalStructureSheaf a

/-- **The morphism of ringed sites of `h`** of Stacks 0DHC: the functor `u : V/U_n ↦ V/U_n`
with the identification `𝒪_U = u^p 𝒪_{big,total}` as structure map. -/
def bigFppfTotalRingedSiteHom : RingedSite.Hom (bigFppfTotalRingedSite a) (ringedSite U) where
  u := toBigFppfTotal U
  isMorphismOfSites := (toBigFppfTotal_isMorphismOfSites U).toSmallIsMorphismOfSites
  fsharp := (bigFppfTotalStructureIso a).hom

/-- The morphism of ringed topoi `h` is that of the morphism of ringed sites of `h`. -/
theorem bigFppfTotalRingedHom_eq_ringedToposHom :
    bigFppfTotalRingedHom a = (bigFppfTotalRingedSiteHom a).ringedToposHom :=
  rfl

section Degree

attribute [local instance] slicesι_isContinuous slicesι_isCocontinuous

variable (n : SimplexCategory)

/-- The structure map of the morphism of ringed sites of `h` in degree `n`: both rings assign to
`V/U_n` the ring `Γ(V, 𝒪_V)`, and the components are those of `bigFppfTotalStructureIso`. -/
def degreeStructureMap :
    ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O ⟶
      ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).sheafPushforwardContinuous
        CommRingCat.{u + 1} (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (BigFppfSpaceOver.topology T (U.obj (op n)))).obj
        ((bigFppfTotalRingedSite a).restrictRestrictionSquarePullbackMate
          (BigFppfSpaceOver.topology T (U.obj (op n)))
          (slicesι U n)).O where
  hom :=
    { app := fun V ↦
        (bigFppfTotalStructureIso a).hom.hom.app (op ((degreeInclusion U n).obj V.unop))
      naturality := fun V W g ↦ by
        have h :=
          (bigFppfTotalStructureIso a).hom.hom.naturality ((degreeInclusion U n).map g.unop).op
        refine h.trans ?_
        change _ ≫ (bigFppfTotalStructureSheaf a).obj.map
          ((toBigFppfTotal U).map ((degreeInclusion U n).map g.unop)).op = _
        rw [toBigFppfTotal_map_degreeInclusion]
        rfl }

/-- **The morphism of ringed sites of `h` in degree `n`**: the inclusion of `(U_n)_{spaces,étale}`
into `(Spaces/U_n)_{fppf}`, between the restrictions of the two ringed sites of `h` to the
components of degree `n`. -/
def degreeRingedSiteHom :
    RingedSite.Hom
      ((bigFppfTotalRingedSite a).restrictRestrictionSquarePullbackMate
        (BigFppfSpaceOver.topology T (U.obj (op n)))
        (slicesι U n))
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)) where
  u := SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))
  isMorphismOfSites := BigFppfSpaceSite.spacesEtaleInclusion_isMorphismOfSites T (U.obj (op n))
  fsharp := degreeStructureMap a n

/-- The degree square of `h`, spelled with the functors of the two morphisms of ringed sites. -/
def degreeHomSquare :
    TwoSquare (degreeRingedSiteHom a n).u (degreeInclusion U n) (slicesι U n)
      (bigFppfTotalRingedSiteHom a).u :=
  degreeTwoSquare U n

/-- The degree square of `h` is Guitart exact. -/
instance degreeHomSquare_guitartExact : (degreeHomSquare a n).GuitartExact :=
  degreeTwoSquare_guitartExact U n

/-- The natural transformation of the degree square of `h` is an isomorphism. -/
instance isIso_degreeHomSquare_natTrans : IsIso (degreeHomSquare a n).natTrans :=
  inferInstanceAs (IsIso (degreeInclusionCompToBigFppfTotalIso U n).inv)

/-- A presheaf on the total site maps the components of the degree square to identities. -/
theorem comp_map_degreeHomSquare_app {D : Type*} [Category* D]
    (P : (Grothendieck (SimplicialOver.slices U))ᵒᵖ ⥤ D)
    (V : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n))) {W : D}
    (x : W ⟶ P.obj (op ((slicesι U n).obj
      ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).obj V)))) :
    x ≫ P.map ((degreeHomSquare a n).natTrans.app V).op = x := by
  have key : ∀ k : (slicesι U n).obj
      ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).obj V) ⟶
        (slicesι U n).obj
          ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).obj V),
      k = 𝟙 _ → x ≫ P.map k.op = x := fun k hk ↦ by
    subst hk
    rw [op_id, P.map_id, Category.comp_id]
  exact key _ (degreeTwoSquare_app U n V)

/-- The structure map of the degree-`n` morphism of `h` at `V` is that of `h` at the image of `V`
in the total site. -/
theorem degreeRingedSiteHom_fsharp_app
    (V : (SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n)))ᵒᵖ) :
    (degreeRingedSiteHom a n).fsharp.hom.app V =
      (bigFppfTotalRingedSiteHom a).fsharp.hom.app ((degreeInclusion U n).op.obj V) :=
  rfl

/-- The structure maps of `h` and of its degree-`n` morphism agree through the degree square. -/
theorem degreeRingedSiteHom_fsharp_compat
    (V : (SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n)))ᵒᵖ) :
    (bigFppfTotalRingedSiteHom a).fsharp.hom.app ((degreeInclusion U n).op.obj V) ≫
        (bigFppfTotalRingedSite a).O.obj.map ((degreeHomSquare a n).natTrans.app V.unop).op =
      (degreeRingedSiteHom a n).fsharp.hom.app V := by
  rw [degreeRingedSiteHom_fsharp_app]
  exact comp_map_degreeHomSquare_app a n (bigFppfTotalRingedSite a).O.obj V.unop _

/-- **The unit of `h` in degree `n` (Stacks 0DH0).** The restriction to degree `n` of the unit
`G ⟶ h_*h^*G` is invertible exactly when the unit of the degree-`n` morphism of ringed sites at
`G|_{U_n}` is: the degree square of `h` is Guitart exact with invertible components. -/
theorem isIso_restrictModules_map_bigFppfTotal_unit_iff
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O)) :
    IsIso (((ringedSite U).restrictModulesAlongRestrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (degreeInclusion U n)).map
        ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (bigFppfTotalRingedSiteHom a).ringedToposHom).unit.app G)) ↔
      IsIso
        ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (degreeRingedSiteHom a n).ringedToposHom).unit.app
            (((ringedSite U).restrictModulesAlongRestrictRestrictionSquarePullbackMate
              (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
              (degreeInclusion U n)).obj G)) :=
  (bigFppfTotalRingedSiteHom a).isIso_restrictModules_map_unit_iff_restrictionSquarePullbackMate
    (BigFppfSpaceOver.topology T (U.obj (op n)))
    (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (slicesι U n)
    (degreeInclusion U n) (degreeRingedSiteHom a n) (degreeHomSquare a n)
    (degreeRingedSiteHom_fsharp_compat a n) G

/-- The restriction maps of `𝒪_{big,total}` along the component of degree `n` are those of the
big structure sheaf of `U_n`. -/
theorem bigFppfTotalStructureSheaf_map_slicesι {V W : Over (U.obj (op n))} (g : V ⟶ W) :
    (bigFppfTotalStructureSheaf a).obj.map ((slicesι U n).map g).op =
      (BigFppfSpaceSite.structureSheaf T (U.obj (op n))).obj.map g.op := by
  show (BigFppfSpaceSite.structureSheaf T X).obj.map
    ((SimplicialOver.augmentationFunctor U a).map ((slicesι U n).map g)).op = _
  rw [BigFppfSpaceSite.structureSheaf_map, BigFppfSpaceSite.structureSheaf_map]
  exact congrArg
    (fun k ↦ CommRingCat.ofHom (Space.globalFunctionsMap T.schemeSite S T.scheme_mem k))
    ((SimplicialOver.augmentationFunctor_map_left_overSimplicialObjectAugmentationFunctorLeft
      a _).trans (SimplicialOver.overMap_ι_map_fiber_left_simplicialSmallEtaleBigFppf U (op n) g))

/-- The restriction of `𝒪_{big,total}` to degree `n` is the big structure sheaf of `U_n`: both
assign to `V/U_n` the ring `Γ(V, 𝒪_V)`. -/
def degreeRingIso :
    ((slicesι U n).sheafPushforwardContinuous CommRingCat.{u + 1}
        (BigFppfSpaceOver.topology T (U.obj (op n)))
        (SimplicialOver.totalTopology T.topology U)).obj
        (bigFppfTotalStructureSheaf a) ≅
      BigFppfSpaceSite.structureSheaf T (U.obj (op n)) :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦
    (Category.comp_id _).trans ((bigFppfTotalStructureSheaf_map_slicesι a n g.unop).trans
      (Category.id_comp _).symm)))

/-- The structure map of `a_{U_n}` is that of the degree-`n` morphism of `h`, followed by the
identification of the rings. -/
theorem spacesEtaleRestrictionStructureIso_hom_eq :
    (BigFppfSpaceSite.spacesEtaleRestrictionStructureIso T (U.obj (op n))).hom =
      degreeStructureMap a n ≫
        ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem
          (U.obj (op n))).sheafPushforwardContinuous
          CommRingCat.{u + 1} (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
          (BigFppfSpaceOver.topology T (U.obj (op n)))).map (degreeRingIso a n).hom := by
  ext V x
  rfl

/-- **The unit of the degree-`n` morphism of `h` is that of `a_{U_n}`**: the two morphisms of
ringed sites have the same functor and their source rings are identified by `degreeRingIso`. -/
theorem isIso_degreeRingedSiteHom_unit_app_iff
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).J)
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O)) :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (degreeRingedSiteHom a n).ringedToposHom).unit.app G) ↔
      IsIso ((BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T
        (U.obj (op n))).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app G) := by
  have h1 := Adjunction.isIso_unit_app_iff_of_iso_right
    (RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (degreeRingedSiteHom a n).ringedToposHom)
    (degreeRingedSiteHom a n).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    (degreeRingedSiteHom a n).pushforwardToposIso G
  have h2 := RingedToposSiteHom.isIso_unit_app_iff_of_ringIso_ringedToposSiteHomRingIso
      (degreeRingIso a n)
      (Y := RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (degreeInclusion U n)))
      (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))) (degreeStructureMap a n)
      (BigFppfSpaceSite.spacesEtaleRestrictionStructureIso T (U.obj (op n))).hom
      (spacesEtaleRestrictionStructureIso_hom_eq a n) G
  exact h1.trans h2

/-- **Stacks 0DGN (6) in degree `n`**: the unit of the degree-`n` morphism of `h` is invertible at
a quasi-coherent module. -/
theorem isIso_degreeRingedSiteHom_unit_app
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).J)
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O)) [G.IsQuasicoherentOnSite] :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (degreeRingedSiteHom a n).ringedToposHom).unit.app G) :=
  (isIso_degreeRingedSiteHom_unit_app_iff a n G).mpr
    (@BigFppfSpaceSite.isIso_unit_app_of_isQuasicoherentOnSite _ _ _ G (by assumption))

end Degree

/-- **The unit of `h` is invertible on quasi-coherent modules** (Stacks 0DH0, 0DGN (6)): for a
quasi-coherent `𝒪_U`-module `G` the unit `G ⟶ h_*h^*G` is an isomorphism. In each degree `n` it
restricts to the unit of `a_{U_n}` at the quasi-coherent module `G|_{U_n}`. -/
theorem isIso_bigFppfTotalRingedHom_unit_app
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O))
    [G.IsQuasicoherentOnSite] :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (bigFppfTotalRingedHom a)).unit.app G) := by
  rw [bigFppfTotalRingedHom_eq_ringedToposHom]
  refine isIso_of_forall_isIso_degreeRestrictModules_map _ fun n ↦ ?_
  have := isQuasicoherentOnSite_degreeRestrictModules_obj n G
  exact (isIso_restrictModules_map_bigFppfTotal_unit_iff a n G).mpr
    (isIso_degreeRingedSiteHom_unit_app a n _)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
