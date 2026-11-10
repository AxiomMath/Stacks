module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafSubquotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSupportQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmodulePullbackChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuotientPointKernelZariski

/-!
# The chart restriction as the Zariski reading of the pullback, naturally in the module

Let `W` be an étale scheme chart of an algebraic space `X`, with scheme `T` and structure morphism
`w : T ⟶ X`. An `𝒪_X`-module `G` has two readings on the Zariski site of `T`: its restriction
`G|_W` to the chart (Stacks 03G6, `AlgebraicGeometry.Space.restrictToChart`), and the Zariski
reading of its pullback `w^*G` (Stacks 03LU), the direct image of `w^*G` along the inclusion of the
small Zariski site of `T` into its small étale site.

This file identifies the two readings naturally in `G`, so the identification is compatible with
morphisms of modules, in particular with the inclusion of a submodule.

Consequently, at an étale scheme point `f : T ⟶ X` of Situation 0849 the degree-`d` piece of `f^*𝒜`
is identified with `𝒜_d|_T` by an isomorphism carrying the Zariski image `𝒢` of `f^*ℱ ⟶ (f^*𝒜)_d`
into the image of `ℱ|_T ⟶ 𝒜_d|_T`, for every submodule `ℱ ⊆ 𝒜_d`, and clause (b) of Stacks 085N on
`X` follows from the chart statement for every chart submodule `ℱ' ≤ 𝒢`.

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingModulePullbackIsoRestrictToChartFunctor`: the Zariski
  reading of the pullback to an étale chart is the restriction to the chart, as functors of the
  module, and `AlgebraicGeometry.Space.zariskiReadingPointPullbackIsoRestrictToChartFunctor` its
  form at an étale scheme point.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointPieceChartIso`: the isomorphism
  `(f^*𝒜)_d ≅ 𝒜_d|_T` at an étale scheme point.

## Main results

* `AlgebraicGeometry.app_mem_localImage_of_natural_family_of_heq`: a natural identification carries
  the image submodule of `Pu φ` into the local image of `Rr i`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointPieceChartIso_hom_mem_imageSubmodule`: the
  isomorphism `(f^*𝒜)_d ≅ 𝒜_d|_T` carries `𝒢` into the image of `ℱ|_T ⟶ 𝒜_d|_T`.
* `AlgebraicGeometry.Space.RelativeProjSituation.disjoint_supportOfSheaf_cokernel_of_le`: clause
  (b) of Stacks 085N on `X` from a chart submodule `ℱ' ≤ 𝒢`.

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v₁ u₁ r m u

/-! ### Functoriality of the local image -/

namespace Stacks.SheafOfModules.ImageSubsheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
  {M N P : SheafOfModules.{m} R}

/-- A morphism `g` carries the local image of `f` into the local image of `f ≫ g`: where a section
is locally in the range of `f`, its image is locally in the range of `f ≫ g`. -/
theorem app_mem_imageSubmodule_comp (f : M ⟶ N) (g : N ⟶ P) {X : Cᵒᵖ} {a : N.val.obj X}
    (ha : a ∈ (imageSubmodule f).obj X) :
    g.val.app X a ∈ (imageSubmodule (f ≫ g)).obj X := by
  refine J.superset_covering (fun V h hh => ?_) ha
  rw [sieveOfSection_rangeSubmodule_apply] at hh ⊢
  obtain ⟨b, hb⟩ := hh
  exact ⟨b, (congrArg (g.val.app (op V)) hb).trans
    (PresheafOfModules.naturality_apply g.val h.op a)⟩

/-- The local image of `f ≫ g` lies in the local image of `g`. -/
theorem mem_imageSubmodule_of_mem_imageSubmodule_comp (f : M ⟶ N) (g : N ⟶ P) {X : Cᵒᵖ}
    {a : P.val.obj X} (ha : a ∈ (imageSubmodule (f ≫ g)).obj X) :
    a ∈ (imageSubmodule g).obj X := by
  refine J.superset_covering (fun V h hh => ?_) ha
  rw [sieveOfSection_rangeSubmodule_apply] at hh ⊢
  obtain ⟨b, hb⟩ := hh
  exact ⟨f.val.app (op V) b, hb⟩

/-- A commutative square carries local images into local images: if `f ≫ g = u ≫ r`, then `g`
carries the local image of `f` into the local image of `r`. -/
theorem app_mem_imageSubmodule_of_comp_eq {Q : SheafOfModules.{m} R} (f : M ⟶ N) (g : N ⟶ P)
    (u : M ⟶ Q) (r : Q ⟶ P) (h : f ≫ g = u ≫ r) {X : Cᵒᵖ} {a : N.val.obj X}
    (ha : a ∈ (imageSubmodule f).obj X) : g.val.app X a ∈ (imageSubmodule r).obj X := by
  exact mem_imageSubmodule_of_mem_imageSubmodule_comp u r (h ▸ app_mem_imageSubmodule_comp f g ha)

end Stacks.SheafOfModules.ImageSubsheaf

/-! ### The image submodule on a scheme lies in the local image -/

namespace AlgebraicGeometry

/-- On a scheme, the image submodule `AlgebraicGeometry.imageSubmodule p` of a morphism of modules
`p`, the sectionwise kernel of the cokernel of `p`, lies in its local image. -/
theorem mem_localImage_of_mem_imageSubmodule {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N)
    (U : X.Opens) {a : Γ(N, U)} (ha : a ∈ (imageSubmodule p).toSubmodule.obj (op U)) :
    a ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (R := X.ringCatSheaf) p).obj
      (op U) := by
  let q := toImageSubmodule p
  have : Epi (C := SheafOfModules.{u} X.ringCatSheaf) q := epi_toImageSubmodule p
  have : Abelian (SheafOfModules.{u} X.ringCatSheaf) := inferInstanceAs (Abelian X.Modules)
  have hiso := Stacks.SheafOfModules.ImageSubsheaf.isIso_imageSubmodule_ι (R := X.ringCatSheaf) q
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)).map
        (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (R := X.ringCatSheaf) q).ι)).2
    (⟨a, ha⟩ : ((imageSubmodule p).toSheafOfModules : X.Modules).val.obj (op U))
  have hb : (⟨a, ha⟩ : ((imageSubmodule p).toSheafOfModules : X.Modules).val.obj (op U)) ∈
      (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (R := X.ringCatSheaf) q).obj (op U) :=
    hy ▸ y.2
  have h := Stacks.SheafOfModules.ImageSubsheaf.app_mem_imageSubmodule_comp (R := X.ringCatSheaf)
    q (subι (imageSubmodule p)) hb
  have hfac : @CategoryStruct.comp (SheafOfModules.{u} X.ringCatSheaf) _ _ _ _ q
      (subι (imageSubmodule p)) = p :=
    toImageSubmodule_comp_subι p
  rwa [hfac] at h

/-- A commutative square carries the image submodule into the local image: on a scheme, if
`p ≫ g = u ≫ r`, then `g` carries the image submodule of `p` (the kernel of its cokernel) into the
local image of `r`. -/
theorem app_mem_localImage_of_comp_eq {X : Scheme.{u}} {M N : X.Modules}
    {P Q : SheafOfModules.{u} X.ringCatSheaf} (p : M ⟶ N)
    (g : (N : SheafOfModules.{u} X.ringCatSheaf) ⟶ P)
    (v : (M : SheafOfModules.{u} X.ringCatSheaf) ⟶ Q) (r : Q ⟶ P)
    (h : @CategoryStruct.comp (SheafOfModules.{u} X.ringCatSheaf) _ _ _ _ p g = v ≫ r)
    (U : X.Opens) {a : Γ(N, U)} (ha : a ∈ (imageSubmodule p).toSubmodule.obj (op U)) :
    g.val.app (op U) a ∈ (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule r).obj (op U) :=
  Stacks.SheafOfModules.ImageSubsheaf.app_mem_imageSubmodule_of_comp_eq p g v r h
    (mem_localImage_of_mem_imageSubmodule p U ha)

end AlgebraicGeometry

/-! ### A naturality square through an identification -/

namespace CategoryTheory

/-- A morphism heterogeneously equal to `ψ : X ⟶ Y'`, with target `Y = Y'`, becomes `ψ` after
composition with the `eqToHom` of that equality. -/
theorem comp_eqToHom_eq_of_heq_of_eq {C : Type*} [Category C] {X Y Y' : C} (h : Y = Y')
    (φ : X ⟶ Y) (ψ : X ⟶ Y') (hφ : HEq φ ψ) : φ ≫ eqToHom h = ψ := by
  subst h
  simpa using eq_of_heq hφ

/-- The composite identification `Nm = Pu Y ≅ Pu (Pl N) ≅ Rr N ≅ Rr G` determined by a family of
isomorphisms `α : Pu (Pl M) ≅ Rr M`, an equality `h : Y = Pl N`, an equality `hN : Pu Y = Nm` and
an isomorphism `j : N ≅ G`. -/
def Functor.isoOfFamilyOfEq {C D E : Type*} [Category C] [Category D] [Category E] (Pl : C ⥤ D)
    (Pu : D ⥤ E) (Rr : C ⥤ E) (α : ∀ M : C, Pu.obj (Pl.obj M) ≅ Rr.obj M) {N G : C} {Y : D}
    {Nm : E} (h : Y = Pl.obj N) (hN : Pu.obj Y = Nm) (j : N ≅ G) : Nm ≅ Rr.obj G :=
  eqToIso hN.symm ≪≫ Pu.mapIso (eqToIso h) ≪≫ α N ≪≫ Rr.mapIso j

/-- A naturality square through an identification: let `α : Pu (Pl M) ≅ Rr M` be a family of
isomorphisms, natural in `M`, `i : A ⟶ G` a morphism, `j : N ≅ G` an isomorphism and `φ : Pl A ⟶ Y`
a morphism which becomes `Pl (i ≫ j⁻¹)` once `Y` is identified with `Pl N` by `h`. Then `Pu φ`
followed by the composite identification `Pu Y ≅ Pu (Pl N) ≅ Rr N ≅ Rr G` is `α` at `A` followed by
`Rr i`. -/
theorem Functor.map_comp_mapIso_eqToIso_trans_trans_mapIso_hom {C D E : Type*} [Category C]
    [Category D] [Category E] (Pl : C ⥤ D) (Pu : D ⥤ E) (Rr : C ⥤ E)
    (α : ∀ M : C, Pu.obj (Pl.obj M) ≅ Rr.obj M)
    (hα : ∀ {M M' : C} (g : M ⟶ M'), Pu.map (Pl.map g) ≫ (α M').hom = (α M).hom ≫ Rr.map g)
    {A N G : C} {Y : D} (i : A ⟶ G) (j : N ≅ G) (h : Y = Pl.obj N) (φ : Pl.obj A ⟶ Y)
    (hφ : φ ≫ eqToHom h = Pl.map (i ≫ j.inv)) :
    Pu.map φ ≫ (Pu.mapIso (eqToIso h) ≪≫ α N ≪≫ Rr.mapIso j).hom = (α A).hom ≫ Rr.map i := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
  rw [← Category.assoc, ← Pu.map_comp, hφ, ← Category.assoc, hα, Category.assoc, ← Rr.map_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry

/-- In the situation of `CategoryTheory.Functor.map_comp_mapIso_eqToIso_trans_trans_mapIso_hom`,
with `Pu` and `Rr` landing in the modules on a scheme, a section of the image submodule of `Pu φ`
is carried by the composite identification `Pu Y ≅ Pu (Pl N) ≅ Rr N ≅ Rr G` into the local image of
`Rr i`. -/
theorem app_mem_localImage_of_natural_family {C D : Type*} [Category C] [Category D]
    {X : Scheme.{u}} (Pl : C ⥤ D) (Pu : D ⥤ SheafOfModules.{u} X.ringCatSheaf)
    (Rr : C ⥤ SheafOfModules.{u} X.ringCatSheaf) (α : ∀ M : C, Pu.obj (Pl.obj M) ≅ Rr.obj M)
    (hα : ∀ {M M' : C} (g : M ⟶ M'), Pu.map (Pl.map g) ≫ (α M').hom = (α M).hom ≫ Rr.map g)
    {A N G : C} {Y : D} (i : A ⟶ G) (j : N ≅ G) (h : Y = Pl.obj N) (φ : Pl.obj A ⟶ Y)
    (hφ : φ ≫ eqToHom h = Pl.map (i ≫ j.inv)) (U : X.Opens) {a : (Pu.obj Y).val.obj (op U)}
    (ha : a ∈ (imageSubmodule (M := Pu.obj (Pl.obj A)) (N := Pu.obj Y)
      (Pu.map φ)).toSubmodule.obj (op U)) :
    (Pu.mapIso (eqToIso h) ≪≫ α N ≪≫ Rr.mapIso j).hom.val.app (op U) a ∈
      (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (Rr.map i)).obj (op U) :=
  app_mem_localImage_of_comp_eq (Pu.map φ) _ (α A).hom (Rr.map i)
    (Functor.map_comp_mapIso_eqToIso_trans_trans_mapIso_hom Pl Pu Rr α hα i j h φ hφ) U ha

/-- `AlgebraicGeometry.app_mem_localImage_of_natural_family` for a module `Nm` equal to `Pu Y` and
a submodule `Sm ⊆ Nm` heterogeneously equal to the image submodule of `Pu φ`. -/
theorem app_mem_localImage_of_natural_family_of_heq {C D : Type*} [Category C] [Category D]
    {X : Scheme.{u}} (Pl : C ⥤ D) (Pu : D ⥤ SheafOfModules.{u} X.ringCatSheaf)
    (Rr : C ⥤ SheafOfModules.{u} X.ringCatSheaf) (α : ∀ M : C, Pu.obj (Pl.obj M) ≅ Rr.obj M)
    (hα : ∀ {M M' : C} (g : M ⟶ M'), Pu.map (Pl.map g) ≫ (α M').hom = (α M).hom ≫ Rr.map g)
    {A N G : C} {Y : D} (i : A ⟶ G) (j : N ≅ G) (h : Y = Pl.obj N) (φ : Pl.obj A ⟶ Y)
    (hφ : φ ≫ eqToHom h = Pl.map (i ≫ j.inv)) {Nm : SheafOfModules.{u} X.ringCatSheaf}
    (hN : Pu.obj Y = Nm) {Sm : Nm.Submodule}
    (hS : HEq Sm (imageSubmodule (M := Pu.obj (Pl.obj A)) (N := Pu.obj Y) (Pu.map φ)))
    (O : (X.Opens)ᵒᵖ) {a : Nm.val.obj O} (ha : a ∈ Sm.toSubmodule.obj O) :
    (Functor.isoOfFamilyOfEq Pl Pu Rr α h hN j).hom.val.app O a ∈
      (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule (Rr.map i)).obj O := by
  obtain ⟨U⟩ := O
  subst hN
  obtain rfl := eq_of_heq hS
  simpa only [Functor.isoOfFamilyOfEq, eqToIso_refl, Iso.refl_trans] using
    app_mem_localImage_of_natural_family Pl Pu Rr α hα i j h φ hφ U ha

end AlgebraicGeometry

/-! ### Raising the universe of the sections to the universe they live in -/

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- Raising the universe of the sections of sheaves of modules to the universe they already live in
is naturally isomorphic to the identity functor, with components
`SheafOfModules.uliftForPresentationSelfIso`. -/
def uliftForPresentationFunctorIsoId :
    uliftForPresentationFunctor.{u₁, v₁, r, m, m} (R := R) ≅ 𝟭 (SheafOfModules.{m} R) :=
  NatIso.ofComponents (fun M => uliftForPresentationSelfIso M)
    (fun _ => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => by ext; rfl))

end SheafOfModules

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The restriction to a chart scheme as a direct image, as functors -/

section Chart

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (A : SmallEtale B S hS F)
    [(openChartFunctor B S hS F A).IsContinuous
      (Opens.grothendieckTopology ↥(chartScheme A)) (SmallEtale.topology B S hS F)]

/-- The restriction to the scheme of an étale chart with continuous index functor is the direct
image along it, naturally in the module: the functor-level form of
`AlgebraicGeometry.Space.restrictToChartSchemeIsoPushforward`. -/
def restrictToChartSchemeFunctorIsoPushforward :
    restrictToChartSchemeFunctor.{u, u} B S hS F hF A ≅
      SheafOfModules.pushforward.{u} (K := SmallEtale.topology B S hS F)
        (chartSchemeRestrictionSheafHom B S hS hF A) := by
  let fg := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS F hF).O)
  let Pp := PresheafOfModules.pushforward.{u} (chartSchemeRestrictionRingHom B S hS F A)
  let sh := PresheafOfModules.sheafification.{u} (𝟙 (chartScheme A).ringCatSheaf.obj)
  let P := SheafOfModules.pushforward.{u} (K := SmallEtale.topology B S hS F)
    (chartSchemeRestrictionSheafHom B S hS hF A)
  let rs := PresheafOfModules.restrictScalars.{u} (𝟙 (chartScheme A).ringCatSheaf.obj)
  let κ : fg ⋙ Pp ≅ P ⋙ SheafOfModules.forget _ ⋙ rs :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by ext; rfl)
  exact Functor.isoWhiskerRight (SheafOfModules.uliftForPresentationFunctorIsoId
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      (fg ⋙ Pp ⋙ sh) ≪≫
    Functor.leftUnitor _ ≪≫ (Functor.associator fg Pp sh).symm ≪≫
    Functor.isoWhiskerRight κ sh ≪≫ Functor.associator P _ sh ≪≫
    Functor.isoWhiskerLeft P (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (chartScheme A).ringCatSheaf.obj)).counit) ≪≫
    Functor.rightUnitor P

end Chart

/-! ### The two readings of the chart restriction, as functors -/

section Readings

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- The two readings of the chart restriction are isomorphic as functors of the module: the
functor-level form of `AlgebraicGeometry.Space.restrictToChartIsoRestrictToChartScheme`. -/
def restrictToChartFunctorIsoRestrictToChartSchemeFunctor (U : SmallEtale B S hS X) :
    restrictToChartFunctor.{u, m} B S hS hX U ≅
      restrictToChartSchemeFunctor.{u, m} B S hS X hX U := by
  letI catSpaceModules : Category (PresheafOfModules.{max u m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)).obj) :=
    inferInstance
  letI catChartModules : Category (PresheafOfModules.{max u m}
      (etaleChartScheme B S hS U).ringCatSheaf.obj) := inferInstance
  letI : HasSheafify (Opens.grothendieckTopology (etaleChartScheme B S hS U))
      AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u m} _ _
  letI : (Opens.grothendieckTopology (etaleChartScheme B S hS U)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, max u m} _
  exact Functor.isoWhiskerLeft SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, m, u}
    (@Functor.isoWhiskerLeft _ _ _ catSpaceModules _ _ (SheafOfModules.forget _) _ _
      (@Functor.isoWhiskerRight _ catSpaceModules _ catChartModules _ _ _ _
        (Stacks.PresheafOfModules.pushforwardIsoOfIndexIso.{max u m}
          (eqToIso (chartOpens_eq_openChartFunctor B S hS U))
          (chartRestrictionRingHom_comp_whiskerRight B S hS hX U))
        (PresheafOfModules.sheafification.{max u m}
          (𝟙 (etaleChartScheme B S hS U).ringCatSheaf.obj))))

end Readings

/-! ### The Zariski reading on a represented space, as functors -/

section Represented

variable (U : BigFppfOver B S hS)

/-- The structure maps of the two direct images reading a module on the represented space of `U` on
the Zariski site of its scheme — along `AlgebraicGeometry.Space.selfOpensFunctor` and along the
index functor of the identity chart — are compatible with the identification
`AlgebraicGeometry.Space.selfOpensFunctorIso` of the two index functors. -/
theorem selfOpensStructureMap_comp_sheafPushforwardContinuousNatTrans :
    haveI := isContinuous_openChartFunctor_idEtaleChart B S hS U
    selfOpensStructureMap B S hS U ≫
        (Functor.sheafPushforwardContinuousNatTrans (selfOpensFunctorIso B S hS U).hom
          RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
          (SmallEtale.topology B S hS (yoneda.obj U))).app
          (representedStructureRingSheaf B S hS U) =
      chartSchemeRestrictionSheafHom B S hS
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (idEtaleChart B S hS U) := by
  have := isContinuous_openChartFunctor_idEtaleChart B S hS U
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun O => ?_)
  have h1 : (representedSmallEtaleEquivalence B S hS U).counit.app
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property O.unop) = 𝟙 _ :=
    @Subsingleton.elim _ (_root_.AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property _ O.unop)
      _ _
  have h2 : ((((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥((BigFppfOver.toScheme B S hS).obj U))
        (representedSchemeSmallEtaleTopology B S hS U)).map
        (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (representedSchemeStructureSheaf B S hS U))).hom.app O) = 𝟙 _ := by
    change (representedSchemeStructureSheaf B S hS U).obj.map
        ((representedSmallEtaleEquivalence B S hS U).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property O.unop)).op = 𝟙 _
    exact (congrArg (fun k => (representedSchemeStructureSheaf B S hS U).obj.map
          (Quiver.Hom.op k)) h1).trans
      ((congrArg (representedSchemeStructureSheaf B S hS U).obj.map op_id).trans
        ((representedSchemeStructureSheaf B S hS U).obj.map_id _))
  have h3 : ((Functor.sheafPushforwardContinuousNatTrans (selfOpensFunctorIso B S hS U).hom
        RingCat.{u} (Opens.grothendieckTopology ↥(chartScheme (idEtaleChart B S hS U)))
        (SmallEtale.topology B S hS (yoneda.obj U))).app
        (representedStructureRingSheaf B S hS U)).hom.app O = 𝟙 _ := by
    change (representedStructureRingSheaf B S hS U).obj.map
      (eqToHom (selfOpensFunctor_obj B S hS U O.unop).symm).op = 𝟙 _
    exact (congrArg (representedStructureRingSheaf B S hS U).obj.map (eqToHom_op _)).trans
      ((eqToHom_map (representedStructureRingSheaf B S hS U).obj _).trans rfl)
  change (_ ≫ _) ≫ _ = _
  rw [h2, h3]
  exact (Category.comp_id _).trans (Category.comp_id _)

/-- The Zariski reading of a module on the represented space of `U` is its restriction along the
identity chart, naturally in the module: the functor-level form of
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` composed with
`AlgebraicGeometry.Space.selfOpensPushforwardIso`. -/
def pushforwardSelfOpensIsoRestrictToChartSchemeFunctor :
    SheafOfModules.pushforward.{u} (K := SmallEtale.topology B S hS (yoneda.obj U))
        (selfOpensStructureMap B S hS U) ≅
      restrictToChartSchemeFunctor.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (idEtaleChart B S hS U) :=
  haveI := isContinuous_openChartFunctor_idEtaleChart B S hS U
  SheafOfModules.pushforwardCongr₂ (selfOpensStructureMap B S hS U)
      (ψ := chartSchemeRestrictionSheafHom B S hS
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (idEtaleChart B S hS U))
      (selfOpensFunctorIso B S hS U)
      (selfOpensStructureMap_comp_sheafPushforwardContinuousNatTrans B S hS U) ≪≫
    (restrictToChartSchemeFunctorIsoPushforward B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) (idEtaleChart B S hS U)).symm

end Represented

/-! ### The Zariski reading of the pullback to a chart -/

section Chart

variable (X : AlgebraicSpaces B S hS)

/-- The étale pullback to the space of a chart `W`, followed by the restriction along the identity
chart of that space, is the restriction along `W`, as functors of the module. -/
theorem etaleModulePullback_chartToSpace_comp_restrictToChartSchemeFunctor
    (W : SmallEtale B S hS X.1) :
    etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X W) (isEtale_chartToSpace B S hS X W) ⋙
        restrictToChartSchemeFunctor.{u, u} B S hS (chartSpace B S hS X W).1
          (chartSpace B S hS X W).2 (idEtaleChart B S hS (chartFppfObject B S hS X W)) =
      restrictToChartSchemeFunctor.{u, u} B S hS X.1 X.2 W :=
  etaleModulePullback_comp_restrictToChartSchemeFunctor B S hS (chartToSpace B S hS X W)
    (isEtale_chartToSpace B S hS X W) (idEtaleChart B S hS (chartFppfObject B S hS X W))

/-- The Zariski reading of the pullback of a module to an étale chart is its restriction to the
chart, naturally in the module: for an étale chart `W` of `X` with scheme `T` and structure
morphism `w`, the direct image of `w^*G` (Stacks 03LU) along the inclusion of the small Zariski
site of `T` is `G|_W` (Stacks 03G6), naturally in `G`. -/
@[irreducible]
def zariskiReadingModulePullbackIsoRestrictToChartFunctor (W : SmallEtale B S hS X.1) :
    modulePullback B S hS (chartToSpace B S hS X W) ⋙
        SheafOfModules.pushforward.{u}
          (K := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X W)))
          (selfOpensStructureMap B S hS (chartFppfObject B S hS X W)) ≅
      restrictToChartFunctor.{u, u} B S hS X.2 W :=
  Functor.isoWhiskerRight (modulePullbackIsoEtaleModulePullback B S hS
      (chartToSpace B S hS X W) (isEtale_chartToSpace B S hS X W)) _ ≪≫
    Functor.isoWhiskerLeft (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X W)
        (isEtale_chartToSpace B S hS X W))
      (pushforwardSelfOpensIsoRestrictToChartSchemeFunctor B S hS (chartFppfObject B S hS X W)) ≪≫
    eqToIso (etaleModulePullback_chartToSpace_comp_restrictToChartSchemeFunctor B S hS X W) ≪≫
    (restrictToChartFunctorIsoRestrictToChartSchemeFunctor B S hS X.2 W).symm

/-- `AlgebraicGeometry.Space.zariskiReadingModulePullbackIsoRestrictToChartFunctor` at the étale
chart of an étale scheme point `f : T ⟶ X`, with the pullback along the point and the Zariski
reading of the represented space of `T` spelled as in
`AlgebraicGeometry.Space.RelativeProjSituation.pointAlgebra`. -/
@[irreducible]
def zariskiReadingPointPullbackIsoRestrictToChartFunctor {T : BigFppfOver B S hS}
    {f : yoneda.obj T ⟶ X.1}
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    modulePullback B S hS (pointHom f) ⋙
        SheafOfModules.pushforward.{u} (K := SmallEtale.topology B S hS (yoneda.obj T))
          (selfOpensStructureMap B S hS T) ≅
      restrictToChartFunctor.{u, u} B S hS X.2 ⟨CostructuredArrow.mk f, hf⟩ :=
  zariskiReadingModulePullbackIsoRestrictToChartFunctor B S hS X ⟨CostructuredArrow.mk f, hf⟩

end Chart

/-! ### At a scheme point of Situation 0849 -/

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, u}) {T : BigFppfOver s.site s.base s.containsBase}
  (f : yoneda.obj T ⟶ s.space.1)

/-- The degree-`d` piece of the pullback `f^*𝒜` of the re-presented algebra (Stacks 084B (2)) to
the small étale site of a scheme point is the pullback of modules of its degree-`d` piece. -/
theorem etalePointAlgebra_shrink_piece_eq (d : ℤ) :
    (etalePointAlgebra s.shrink.algebra T f).piece d =
      (modulePullback s.site s.base s.containsBase (pointHom f)).obj (s.smallAlgebra.piece d) :=
  (congrArg (fun E₀ => E₀.piece d) (s.etalePointAlgebra_shrink_eq f)).trans rfl

/-- The pullback `f^*ℱ ⟶ (f^*𝒜)_d` of a submodule `ℱ ⊆ 𝒜_d` is, up to the identification of its
target with the pullback of modules of the re-presented piece, the pullback of
`ℱ ⟶ 𝒜_d ≅ (re-presented 𝒜)_d`. -/
theorem pointImageMap_heq {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) :
    HEq (s.pointImageMap f ℱ)
      ((modulePullback s.site s.base s.containsBase (pointHom f)).map
        (ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv)) :=
  cast_heq _ _

/-- `AlgebraicGeometry.Space.RelativeProjSituation.pointImageMap_heq` as an equation: the pullback
`f^*ℱ ⟶ (f^*𝒜)_d`, followed by the identification of its target with the pullback of modules of the
re-presented piece, is the pullback of `ℱ ⟶ 𝒜_d ≅ (re-presented 𝒜)_d`. -/
theorem pointImageMap_comp_eqToHom {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) :
    s.pointImageMap f ℱ ≫ eqToHom (s.etalePointAlgebra_shrink_piece_eq f d) =
      (modulePullback s.site s.base s.containsBase (pointHom f)).map
        (ℱ.ι ≫ (s.smallAlgebraPieceIso d).inv) :=
  comp_eqToHom_eq_of_heq_of_eq _ _ _ (s.pointImageMap_heq f ℱ)

/-- The Zariski reading of the represented space of a scheme point, spelled through `s.site`. -/
local notation "𝒵" => SheafOfModules.pushforward (K := SmallEtale.topology s.site s.base
  s.containsBase (yoneda.obj T)) (selfOpensStructureMap s.site s.base s.containsBase T)

/-- The degree-`d` piece of `f^*𝒜` for the re-presented algebra is the Zariski reading of the
degree-`d` piece of the pullback of the re-presented algebra to the small étale site. -/
theorem pointAlgebra_shrink_piece_eq (d : ℤ) :
    ((𝒵).obj ((etalePointAlgebra s.shrink.algebra T f).piece d) :
        SheafOfModules ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).ringCatSheaf) =
      (s.shrink.pointAlgebra T f).piece d :=
  rfl

variable {f}
  (hf : (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)

/-- The degree-`d` piece of `f^*𝒜` is the restriction `𝒜_d|_T` at an étale scheme point `f : T ⟶ X`
of Situation 0849: the Zariski reading of the degree-`d` piece of the pullback of the re-presented
algebra of Stacks 084B (2), whose pieces are pullbacks of modules
(`AlgebraicGeometry.Space.RelativeProjSituation.etalePointAlgebra_shrink_piece_eq`), identified
with the restriction by the natural isomorphism
`AlgebraicGeometry.Space.zariskiReadingPointPullbackIsoRestrictToChartFunctor`, followed by the
comparison of the re-presented algebra with `𝒜`
(`AlgebraicGeometry.Space.RelativeProjSituation.smallAlgebraPieceIso`). -/
abbrev pointPieceChartIso (d : ℤ) :
    @Iso (SheafOfModules.{u} (etaleChartScheme s.site s.base s.containsBase
        ⟨CostructuredArrow.mk f, hf⟩).ringCatSheaf) _ ((s.shrink.pointAlgebra T f).piece d)
      ((restrictToChartFunctor.{u, u} s.site s.base s.containsBase s.space.2
        ⟨CostructuredArrow.mk f, hf⟩).obj (s.algebra.piece d)) :=
  let Pu := 𝒵
  Functor.isoOfFamilyOfEq
    (E := SheafOfModules (etaleChartScheme s.site s.base s.containsBase
      ⟨CostructuredArrow.mk f, hf⟩).ringCatSheaf)
    (modulePullback s.site s.base s.containsBase (pointHom f)) Pu
    (restrictToChartFunctor.{u, u} s.site s.base s.containsBase s.space.2
      ⟨CostructuredArrow.mk f, hf⟩)
    (fun M => (zariskiReadingPointPullbackIsoRestrictToChartFunctor s.site s.base s.containsBase
      s.space hf).app M)
    (s.etalePointAlgebra_shrink_piece_eq f d) (s.pointAlgebra_shrink_piece_eq f d)
    (s.smallAlgebraPieceIso d)

/-- The Zariski image `𝒢` of `f^*ℱ` is, up to the two spellings of the Zariski reading, the image
submodule of the Zariski reading of `f^*ℱ ⟶ (f^*𝒜)_d`. -/
theorem pointZariskiImageSubmodule_heq {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) :
    HEq (s.pointZariskiImageSubmodule f ℱ)
      (AlgebraicGeometry.imageSubmodule ((𝒵).map (s.pointImageMap f ℱ))) :=
  HEq.rfl

/-- The chart compatibility of Stacks 085N (b): for a submodule `ℱ ⊆ 𝒜_d`, the isomorphism
`(f^*𝒜)_d ≅ 𝒜_d|_T` carries the Zariski image `𝒢 ⊆ (f^*𝒜)_d` of `f^*ℱ`
(`AlgebraicGeometry.Space.RelativeProjSituation.pointZariskiImageSubmodule`) into the image of
`ℱ|_T ⟶ 𝒜_d|_T`. -/
theorem pointPieceChartIso_hom_mem_imageSubmodule {d : ℤ} (ℱ : (s.algebra.piece d).Submodule)
    (O : (Opens (etaleChartScheme s.site s.base s.containsBase ⟨CostructuredArrow.mk f, hf⟩))ᵒᵖ)
    {a : (SheafOfModules.val (R := (etaleChartScheme s.site s.base s.containsBase
      ⟨CostructuredArrow.mk f, hf⟩).ringCatSheaf) ((s.shrink.pointAlgebra T f).piece d)).obj O}
    (ha : a ∈ (s.pointZariskiImageSubmodule f ℱ).toSubmodule.obj O) :
    (s.pointPieceChartIso hf d).hom.val.app O a ∈
      (Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule
        ((restrictToChartFunctor s.site s.base s.containsBase s.space.2
          ⟨CostructuredArrow.mk f, hf⟩).map ℱ.ι)).obj O := by
  let Pu := 𝒵
  have key := AlgebraicGeometry.app_mem_localImage_of_natural_family_of_heq
    (X := etaleChartScheme s.site s.base s.containsBase ⟨CostructuredArrow.mk f, hf⟩)
    (modulePullback s.site s.base s.containsBase (pointHom f)) Pu
    (restrictToChartFunctor.{u, u} s.site s.base s.containsBase s.space.2
      ⟨CostructuredArrow.mk f, hf⟩)
    (fun M => (zariskiReadingPointPullbackIsoRestrictToChartFunctor s.site s.base s.containsBase
      s.space hf).app M)
    (fun g => (zariskiReadingPointPullbackIsoRestrictToChartFunctor s.site s.base s.containsBase
      s.space hf).hom.naturality g) ℱ.ι
    (s.smallAlgebraPieceIso d) (s.etalePointAlgebra_shrink_piece_eq f d) (s.pointImageMap f ℱ)
    (s.pointImageMap_comp_eqToHom f ℱ) (s.pointAlgebra_shrink_piece_eq f d)
    (s.pointZariskiImageSubmodule_heq (f := f) ℱ) O (a := a)
  have t1 : s.pointPieceChartIso hf d = Functor.isoOfFamilyOfEq
      (E := SheafOfModules (etaleChartScheme s.site s.base s.containsBase
        ⟨CostructuredArrow.mk f, hf⟩).ringCatSheaf)
      (modulePullback s.site s.base s.containsBase (pointHom f)) Pu
      (restrictToChartFunctor.{u, u} s.site s.base s.containsBase s.space.2
        ⟨CostructuredArrow.mk f, hf⟩)
      (fun M => (zariskiReadingPointPullbackIsoRestrictToChartFunctor s.site s.base
        s.containsBase s.space hf).app M)
      (s.etalePointAlgebra_shrink_piece_eq f d) (s.pointAlgebra_shrink_piece_eq f d)
      (s.smallAlgebraPieceIso d) := rfl
  rw [t1]
  convert key ha using 2
  rfl

include hf in
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- Clause (b) of Stacks 085N on `X`, from a chart submodule below the image of `f^*ℱ`: let
`f : T ⟶ X` be an étale scheme point, `ℱ ⊆ 𝒜_d` quasi-coherent and `ℱ' ⊆ (f^*𝒜)_d` a submodule
contained in the Zariski image `𝒢` of `f^*ℱ`. If the support of `(f^*𝒜)_d/ℱ'` misses an open
`V ⊆ T` whose image covers `U`, then the support of `𝒜_d/ℱ` misses `U`. -/
theorem disjoint_supportOfSheaf_cokernel_of_le {d : ℤ} (ℱ : (s.algebra.piece d).Submodule)
    (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite)
    (ℱ' : ((s.shrink.pointAlgebra T f).piece d).Submodule)
    (hle : ℱ' ≤ s.pointZariskiImageSubmodule f ℱ)
    (V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (hV : (V : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) ∩
      (⟨(cokernel ℱ'.ι).val, (cokernel ℱ'.ι).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u}
          ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).toRingedSpace).supp = ∅)
    {U : Set (points s.site s.base s.containsBase s.space.1)}
    (hUV : U ⊆ (fun t ↦ pointsMap s.site s.base s.containsBase (yoneda.obj T) f
      ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t)) '' V) :
    Disjoint (supportOfSheaf s.site s.base s.containsBase s.space.1
      ((SheafOfModules.toSheaf (structureRingSheaf s.site s.base s.containsBase s.space)).obj
        (cokernel ℱ.ι))) U :=
  s.disjoint_supportOfSheaf_cokernel_of_point hf ℱ hℱ (s.pointPieceChartIso hf d) ℱ'
    (fun O _ ha => s.pointPieceChartIso_hom_mem_imageSubmodule hf ℱ O
      (PresheafOfModules.Submodule.le_iff.mp (SheafOfModules.Submodule.le_iff.mp hle) O ha))
    V hV hUV

end RelativeProjSituation

end AlgebraicGeometry.Space

end
