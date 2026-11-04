module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RestrictScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesian
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Modules.CartesianQuasicoherent

/-!
# The counit of the associated-module adjunction of the small étale site

Let `S` be a scheme contained in a big étale site `B` and let `𝒢` be a sheaf of modules on the
small étale site of `S`.  Write `𝓕` for the restriction of `𝒢` along the inclusion of the small
Zariski site of `S`.  This file studies the counit `𝓕^a ⟶ 𝒢` of the associated-module adjunction
at `𝒢`, which is the candidate isomorphism exhibiting `𝒢` as an associated module.

When `𝓕` is quasi-coherent the counit is an isomorphism over every open of `S`: the unit of the
adjunction is an isomorphism at a quasi-coherent module by Stacks 0GN7, and the triangle identity
makes the restriction of the counit its inverse.  It is then an isomorphism outright: both `𝓕^a`
and `𝒢` are quasi-coherent on the site, hence cartesian between affine objects, so the
base-change square along a morphism from an affine object to an open of `S` propagates
bijectivity from the opens to the affine objects lying over them, and those cover.  This reduces
the essential surjectivity of `𝓕 ↦ 𝓕^a` to one statement about the right adjoint: that it carries
quasi-coherent modules on `S_étale` to quasi-coherent `𝒪_S`-modules.

## Main results

* `SheafOfModules.isIso_val_app_of_isIso` and `SheafOfModules.bijective_val_app_of_isIso`: an
  isomorphism of sheaves of modules is an isomorphism, and is bijective, on sections.
* `AlgebraicGeometry.SmallEtale.isIso_restrictModule_map_counit`: the restriction of the counit
  along the inclusion of the small Zariski site is an isomorphism.
* `AlgebraicGeometry.SmallEtale.bijective_counit_val_app_opensObj`: the counit is bijective on
  sections over every open of `S`.
* `AlgebraicGeometry.SmallEtale.bijective_counit_val_app_of_isAffine` and
  `AlgebraicGeometry.SmallEtale.bijective_counit_val_app_openSubObj`: the counit is bijective on
  sections over an affine object lying over an affine open of `S`.
* `AlgebraicGeometry.SmallEtale.isIso_counit`: **the counit is an isomorphism.**
* `AlgebraicGeometry.SmallEtale.essImage_associatedModuleQcoh_of_isQuasicoherent_restrictModule`
  and its global form
  `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule_of_isQuasicoherent_\
  restrictModule`: **Stacks 03DX (2) at `τ = étale`, essential surjectivity**, over
  quasi-coherence of the restriction alone.
* `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite_of_isQuasicoherent_\
  restrictModule` and
  `AlgebraicGeometry.SmallEtale.associatedModuleEquivalenceOfRestrictModule`: **the equivalence
  `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` of Stacks 03DX (2) at `τ = étale`**, over quasi-coherence of the
  restriction alone.
* `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`: that hypothesis is a theorem, and
  `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`,
  `AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'` and
  `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'` are the resulting unconditional
  forms.

## Implementation notes

Every statement up to `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` carries
quasi-coherence of `(restrictModule B S hS).obj 𝒢` as an explicit hypothesis, and none of those
is tagged: a hypothesis is part of a citation.  Discharging it is a statement about the Zariski
site of `S` with no reference to the étale site, namely that the base-change comparison of a
module is bijective on nested affine opens.  The two unconditional statements of clause (2) that
follow are registered against Tag 03DX by name at the end of the file.

Clause (2) of Stacks 03DX quantifies over `τ ∈ {Zariski, étale}`, and only `τ = étale` is treated
here and in the clause strings of the tree.  The reason is the counit argument below, not the
absence of a functor at `τ = Zariski`: that functor is
`AlgebraicGeometry.SmallZariski.associatedModule`, over
`AlgebraicGeometry.SmallZariski.structureSheaf`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u₁ v₁

namespace SheafOfModules

/-- An isomorphism of sheaves of modules is an isomorphism on sections over every object. -/
public theorem isIso_val_app_of_isIso {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (φ : M ⟶ N) (hφ : IsIso φ) (T : Cᵒᵖ) :
    IsIso (φ.val.app T) := by
  have := hφ
  exact (SheafOfModules.evaluation _ T).map_isIso φ

/-- An isomorphism of sheaves of modules is bijective on sections over every object. -/
public theorem bijective_val_app_of_isIso {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (φ : M ⟶ N) (hφ : IsIso φ) (T : Cᵒᵖ) :
    Function.Bijective (φ.val.app T) :=
  have := isIso_val_app_of_isIso φ hφ T
  ConcreteCategory.bijective_of_isIso _

end SheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The restriction of the counit to the small Zariski site is an isomorphism.**  If the
restriction `𝓕` of `𝒢` along the inclusion of the small Zariski site of `S` is quasi-coherent,
then the unit of the associated-module adjunction at `𝓕` is an isomorphism by Stacks 0GN7, and
the triangle identity exhibits the restriction of the counit at `𝒢` as its inverse. -/
public theorem isIso_restrictModule_map_counit
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) :
    IsIso ((restrictModule B S hS).map
      ((associatedModuleAdjunction B S hS).counit.app G)) := by
  have hu : IsIso ((associatedModuleAdjunction B S hS).unit.app
      ((restrictModule B S hS).obj G)) :=
    unitIsoOnQuasicoherent B S hS ⟨(restrictModule B S hS).obj G, h⟩
  have hcomp : IsIso ((associatedModuleAdjunction B S hS).unit.app
      ((restrictModule B S hS).obj G) ≫
      (restrictModule B S hS).map ((associatedModuleAdjunction B S hS).counit.app G)) := by
    rw [(associatedModuleAdjunction B S hS).right_triangle_components G]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((associatedModuleAdjunction B S hS).unit.app ((restrictModule B S hS).obj G)) _

/-- **The counit is bijective on sections over an open of `S`.**  Over the object of the small
étale site attached to an open `V` of `S` the counit is the section-wise inverse of the unit of
the adjunction, by `AlgebraicGeometry.SmallEtale.isIso_restrictModule_map_counit`. -/
public theorem bijective_counit_val_app_opensObj
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) (V : S.Opens) :
    Function.Bijective (((associatedModuleAdjunction B S hS).counit.app G).val.app
      (op ((opensToSmallEtale B S hS).obj V))) :=
  SheafOfModules.bijective_val_app_of_isIso
    ((restrictModule B S hS).map ((associatedModuleAdjunction B S hS).counit.app G))
    (isIso_restrictModule_map_counit B S hS G h) (op V)

/-- **The counit is bijective on sections over an affine object lying over an affine open.**
Both `𝓕^a` and `𝒢` are quasi-coherent on the small étale site, hence cartesian between affine
objects; the base-change square of
`Stacks.PresheafOfModules.restrictionBaseChange_naturality` along a morphism `T ⟶ V` therefore
has three bijective sides, the third being the counit over `V`. -/
public theorem bijective_counit_val_app_of_isAffine
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    {T : SmallEtale B S hS}
    (hT : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj T))
    {V : S.Opens} (hV : AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V)))
    (g : T ⟶ (opensToSmallEtale B S hS).obj V) :
    Function.Bijective
      (((associatedModuleAdjunction B S hS).counit.app G).val.app (op T)) := by
  classical
  set θ := (associatedModuleAdjunction B S hS).counit.app G with hθ
  have hqa : ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)
      ).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _ h
  have hG' := bijective_restrictionBaseChange_of_isQuasicoherentOnSite B S hS G hG hT hV g
  have hA' := bijective_restrictionBaseChange_of_isQuasicoherentOnSite B S hS
    ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)) hqa hT hV g
  have hV' : Function.Bijective (θ.val.app (op ((opensToSmallEtale B S hS).obj V))) :=
    bijective_counit_val_app_opensObj B S hS G h V
  have hVi : IsIso (θ.val.app (op ((opensToSmallEtale B S hS).obj V))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hV'
  have hE : Function.Bijective ((ModuleCat.extendScalars
      ((commStructurePresheaf B S hS).map g.op).hom).map
      (θ.val.app (op ((opensToSmallEtale B S hS).obj V)))) :=
    ConcreteCategory.bijective_of_isIso
      (f := ((ModuleCat.extendScalars ((commStructurePresheaf B S hS).map g.op).hom).mapIso
        (@asIso _ _ _ _ _ hVi)).hom)
  have hsq := Stacks.PresheafOfModules.restrictionBaseChange_naturality
    (R := commStructurePresheaf B S hS) θ.val g.op
  have hpt : ∀ x, Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS) G.val g.op
        ((ModuleCat.extendScalars ((commStructurePresheaf B S hS).map g.op).hom).map
          (θ.val.app (op ((opensToSmallEtale B S hS).obj V))) x) =
      θ.val.app (op T) (Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS)
        ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)).val g.op x) :=
    fun x => ConcreteCategory.congr_hom hsq x
  have hcomp : Function.Bijective (fun x => θ.val.app (op T)
      (Stacks.PresheafOfModules.restrictionBaseChange
        (R := commStructurePresheaf B S hS)
        ((associatedModule B S hS).obj ((restrictModule B S hS).obj G)).val g.op x)) := by
    refine (funext hpt : _ = _) ▸ ?_
    exact hG'.comp hE
  exact (hA'.of_comp_iff _).1 hcomp

/-- The affine opens of an object of the small étale site lying over an affine open `U` of `S`
map to the object attached to `U`. -/
public noncomputable def openSubHomOver (T : SmallEtale B S hS) {V : T.obj.left.obj.Opens}
    {U : S.Opens} (hVU : V ≤ T.obj.hom.hom ⁻¹ᵁ U) :
    openSubObj B S hS T V ⟶ (opensToSmallEtale B S hS).obj U :=
  homOfRangeLe B S hS U (by rintro z ⟨w, rfl⟩; exact hVU w.2)

/-- **The counit is bijective on sections over an affine open of an object lying over an affine
open of `S`.**  These are the members of
`AlgebraicGeometry.SmallEtale.affineSubordinateCover`. -/
public theorem bijective_counit_val_app_openSubObj
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G))
    (T : SmallEtale B S hS) {V : T.obj.left.obj.Opens} (hV : IsAffineOpen V)
    {U : S.Opens} (hU : IsAffineOpen U) (hVU : V ≤ T.obj.hom.hom ⁻¹ᵁ U) :
    Function.Bijective (((associatedModuleAdjunction B S hS).counit.app G).val.app
      (op (openSubObj B S hS T V))) :=
  bijective_counit_val_app_of_isAffine B S hS G hG h
    (T := openSubObj B S hS T V) hV (V := U) hU (openSubHomOver B S hS T hVU)

/-- **The counit is an isomorphism** whenever `𝒢` is quasi-coherent on the small étale site and
its restriction to the small Zariski site is quasi-coherent.  It is bijective over the affine
opens lying over affine opens of `S`, which cover every object, so it is locally bijective; both
source and target are sheaves. -/
public theorem isIso_counit
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) :
    IsIso ((associatedModuleAdjunction B S hS).counit.app G) := by
  set θ := (associatedModuleAdjunction B S hS).counit.app G with hθ
  have hbij : ∀ (T : SmallEtale B S hS) (i : (affineSubordinateCover B S hS T).I₀),
      Function.Bijective (((sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ)).app
        (op ((affineSubordinateCover B S hS T).X i))) := fun T i =>
    bijective_counit_val_app_openSubObj B S hS G hG h T i.down.1.2 i.down.2.1.2 i.down.2.2
  have hcov : ∀ (T : SmallEtale B S hS) (W : Sieve T),
      (∀ i, W ((affineSubordinateCover B S hS T).f i)) → W ∈ topology B S hS T :=
    fun T W hW => (topology B S hS).superset_covering
      (by rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]; exact hW)
      (mem_topology_sieve₀_affineSubordinateCover B S hS T)
  have hinj : Sheaf.IsLocallyInjective
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ) := by
    rw [← Sheaf.isLocallyInjective_sheafToPresheaf_map_iff]
    refine ⟨fun {T} x y hxy => hcov T.unop _ fun i => (hbij T.unop i).1 ?_⟩
    have hn := fun z => ConcreteCategory.congr_hom
      (((sheafToPresheaf (topology B S hS) AddCommGrpCat.{u}).map
        ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ)).naturality
        ((affineSubordinateCover B S hS T.unop).f i).op) z
    exact (hn x).trans ((congrArg _ hxy).trans (hn y).symm)
  have hsurj : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ) := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    exact ⟨fun {T} s => hcov T _ fun i => (hbij T i).2 _⟩
  have hiso := (Sheaf.isLocallyBijective_iff_isIso
    ((SheafOfModules.toSheaf (structureSheaf B S hS)).map θ)).1 ⟨hinj, hsurj⟩
  exact (isIso_iff_of_reflects_iso θ (SheafOfModules.toSheaf (structureSheaf B S hS))).1 hiso

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity at one module**, over
quasi-coherence of the restriction of `𝒢` to the small Zariski site: `𝒢` is the associated
module of that restriction, the isomorphism being the counit. -/
public theorem essImage_associatedModuleQcoh_of_isQuasicoherent_restrictModule
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (h : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G)) :
    (associatedModuleQcoh B S hS).essImage G :=
  ⟨⟨(restrictModule B S hS).obj G, h⟩,
    ⟨@asIso _ _ _ _ _ (isIso_counit B S hS G hG h)⟩⟩

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity**, over quasi-coherence of the
restriction to the small Zariski site of every quasi-coherent module on `S_étale`.  This is
`AlgebraicGeometry.SmallEtale.QuasicoherentIsEssImageAssociatedModule` reduced to that one
statement about the right adjoint. -/
public theorem quasicoherentIsEssImageAssociatedModule_of_isQuasicoherent_restrictModule
    (h : ∀ G : SheafOfModules.{u} (structureSheaf B S hS), G.IsQuasicoherentOnSite →
      SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) ((restrictModule B S hS).obj G)) :
    QuasicoherentIsEssImageAssociatedModule B S hS := fun G hG =>
  essImage_associatedModuleQcoh_of_isQuasicoherent_restrictModule B S hS G hG (h G hG)

/-- The functor `𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)`, over
quasi-coherence of the restriction alone. -/
public theorem isEquivalence_associatedModuleQcohOnSite_of_isQuasicoherent_restrictModule
    (h : ∀ G : SheafOfModules.{u} (structureSheaf B S hS), G.IsQuasicoherentOnSite →
      SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) ((restrictModule B S hS).obj G)) :
    (associatedModuleQcohOnSite B S hS).IsEquivalence :=
  isEquivalence_associatedModuleQcohOnSite B S hS
    (quasicoherentIsEssImageAssociatedModule_of_isQuasicoherent_restrictModule B S hS h)

/-- The equivalence of categories `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` with `𝓕 ↦ 𝓕^a` as its functor,
over quasi-coherence of the restriction alone. -/
public noncomputable def associatedModuleEquivalenceOfRestrictModule
    (h : ∀ G : SheafOfModules.{u} (structureSheaf B S hS), G.IsQuasicoherentOnSite →
      SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) ((restrictModule B S hS).obj G)) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  associatedModuleEquivalence B S hS
    (quasicoherentIsEssImageAssociatedModule_of_isQuasicoherent_restrictModule B S hS h)

/-! ### Quasi-coherence of the restriction, and the unconditional statements -/

/-- **The restriction of a quasi-coherent module on `S_étale` to the small Zariski site of `S` is
quasi-coherent.**  Its base-change comparison between nested affine opens is the comparison of
`𝒢` between the corresponding affine objects of the small étale site, which is bijective. -/
public theorem isQuasicoherent_restrictModule
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite) :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := by
  refine Stacks.AlgebraicGeometry.CartesianQuasicoherent.isQuasicoherent_of_bijective_restriction
    _ fun V V' hV hV' hle => bijective_restrictionBaseChange_restrictModule B S hS G hle ?_
  have aV : AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V)) := hV
  have aV' : AlgebraicGeometry.IsAffine
      ((toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V')) := hV'
  exact bijective_restrictionBaseChange_of_isQuasicoherentOnSite B S hS G hG aV' aV
    ((opensToSmallEtale B S hS).map (homOfLE hle))

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, with no hypothesis.**  Every
quasi-coherent `𝒪`-module on `S_étale` is isomorphic to `𝓕^a` for a quasi-coherent `𝒪_S`-module
`𝓕`, namely for its own restriction to the small Zariski site of `S`. -/
public theorem quasicoherentIsEssImageAssociatedModule :
    QuasicoherentIsEssImageAssociatedModule B S hS :=
  quasicoherentIsEssImageAssociatedModule_of_isQuasicoherent_restrictModule B S hS
    (isQuasicoherent_restrictModule B S hS)

/-- **`𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪)`, with no hypothesis.** -/
public theorem isEquivalence_associatedModuleQcohOnSite' :
    (associatedModuleQcohOnSite B S hS).IsEquivalence :=
  isEquivalence_associatedModuleQcohOnSite B S hS
    (quasicoherentIsEssImageAssociatedModule B S hS)

/-- **The equivalence of categories `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)`, with no hypothesis**, with
`𝓕 ↦ 𝓕^a` as its functor: `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence` with its
essential-surjectivity hypothesis discharged by
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`. -/
public noncomputable def associatedModuleEquivalence' :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory :=
  associatedModuleEquivalence B S hS (quasicoherentIsEssImageAssociatedModule B S hS)

/-! ### Tag registration for clause (2) at `τ = étale`

Clause (2) of Stacks 03DX at `τ = étale` is exactly the two unconditional statements above, so
each is registered against the tag by name rather than restated. `add_to_stacks` is a command,
not a declaration, so these are line comments: a `/-- -/` doc comment here is a parse error. -/

-- Essential surjectivity of the clause's functor.
add_to_stacks 03DX "clause (2) at τ = étale: essential surjectivity of 𝓕 ↦ 𝓕^a onto the \
quasi-coherent 𝒪-modules of the small étale site of S, with no hypothesis"
  quasicoherentIsEssImageAssociatedModule

-- The clause itself: that functor is an equivalence of categories.
add_to_stacks 03DX "clause (2) at τ = étale: 𝓕 ↦ 𝓕^a is an equivalence \
QCoh(𝒪_S) ⥤ QCoh(S_étale, 𝒪), with no hypothesis" isEquivalence_associatedModuleQcohOnSite'

end AlgebraicGeometry.SmallEtale

end
