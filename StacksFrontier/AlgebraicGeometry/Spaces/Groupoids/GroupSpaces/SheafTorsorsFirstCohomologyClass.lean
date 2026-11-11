module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.ClassOverAnObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SliceTorsorActions
public import StacksFrontier.Deformation.Artin.FormalObject.NonEffectiveOfClasses
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackConstantData

/-!
# The class in `H¹` of an object of `𝒢/ℬ-Torsors`

Let `ℬ` be a presheaf on the big fppf site of `S`, let `𝒢` be a group object over `ℬ` and let
`A` be an abelian sheaf on the site. Suppose given, for every object `U` of the site and every
section `b` of `ℬ` over `U`, an identification of the sheaf of groups of sections of the acting
group `U ×_{b, ℬ} 𝒢` on the localized site `(Sch/U)_fppf` with the restriction `A|_U`, compatible
with base change along morphisms of the site over `ℬ`: the datum
`AlgebraicGeometry.Space.AbelianGroupData`. For the classifying stack of an abelian group scheme
`A` over `S`, with `ℬ = S`, this says that the points of `𝒢` are the points of `A`.

An object `T = (U, b, F)` of the category `𝒢/ℬ-Torsors` of Stacks 04UL then has a class in
`H¹(U, A)`: the sections of `F` over the localized site form a torsor under `A|_U`, and
`Stacks.Cohomology.Torsors.torsorClassOver` is its class. This file proves that the class is
natural along the morphisms of `𝒢/ℬ-Torsors`, which lie over morphisms of the site.

## Main definitions

* `AlgebraicGeometry.Space.AbelianGroupData`: the identification of the acting groups with `A`.
* `AlgebraicGeometry.Space.SheafTorsors.abelianTorsor`: the torsor under `A|_U` of the sections
  of an object of `𝒢/ℬ-Torsors` over `U`.
* `AlgebraicGeometry.Space.SheafTorsors.h1Class`: its class in `H¹(U, A)`.

## Main results

* `AlgebraicGeometry.Space.SheafTorsors.h1Class_map`: the class is natural along morphisms.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 04UL](https://stacks.math.columbia.edu/tag/04UL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory MonObj

universe w u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SheafTorsorsFirstCohomologyClass
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_SheafTorsorsFirstCohomologyClass
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  hasPullbacks_presheaf_SheafTorsorsFirstCohomologyClass.has_limit _

open Stacks.Cohomology.Torsors

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {ℬ : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-! ### Sectionwise equivariance -/

section Sections

variable {G : Grp (Over ℬ)}

/-- A morphism of torsors carries the lift of a pair of sections to the lift of the pair of
their images. -/
theorem SheafTorsors.smulSectionLift_comp_actionBaseChange {T T' : SheafTorsors G}
    (φ : T ⟶ T') {V : BigFppfOver 𝒞 S hS} (gs : T.group.left.obj (op V))
    (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s)
    (h' : T'.group.hom.app (op V) ((groupBaseChange φ.base φ.comp_sec).app (op V) gs) =
      T'.total.hom.app (op V) (φ.map.app (op V) s)) :
    smulSectionLift T.group T.total gs s h ≫
        actionBaseChange φ.base φ.comp_sec φ.map φ.isPullback.w.symm =
      smulSectionLift T'.group T'.total ((groupBaseChange φ.base φ.comp_sec).app (op V) gs)
        (φ.map.app (op V) s) h' := by
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ?_
    refine (whisker_eq _ (actionBaseChange_fst _ _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker (smulSectionLift_fst _ _ _ _ _) _).trans ?_
    refine (yonedaEquiv_symm_naturality_right _ _ _).trans ?_
    exact (smulSectionLift_fst T'.group T'.total _ _ h').symm
  · refine (Category.assoc _ _ _).trans ?_
    refine (whisker_eq _ (actionBaseChange_snd _ _ _ _)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (eq_whisker (smulSectionLift_snd _ _ _ _ _) _).trans ?_
    refine (yonedaEquiv_symm_naturality_right _ _ _).trans ?_
    exact (smulSectionLift_snd T'.group T'.total _ _ h').symm

/-- The base change of a section of the acting group lying over a section of the total space
lies over the image of that section. -/
theorem SheafTorsors.groupBaseChange_over {T T' : SheafTorsors G} (φ : T ⟶ T')
    {V : BigFppfOver 𝒞 S hS} (gs : T.group.left.obj (op V)) (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s) :
    T'.group.hom.app (op V) ((groupBaseChange φ.base φ.comp_sec).app (op V) gs) =
      T'.total.hom.app (op V) (φ.map.app (op V) s) := by
  have h1 : T'.group.hom.app (op V) ((groupBaseChange φ.base φ.comp_sec).app (op V) gs) =
      T.group.hom.app (op V) gs ≫ φ.base :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (groupBaseChange_snd φ.base φ.comp_sec)
      (op V)) gs
  have h2 : T.total.hom.app (op V) s ≫ φ.base =
      T'.total.hom.app (op V) (φ.map.app (op V) s) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app φ.isPullback.w.symm (op V)) s
  rw [h1, h, h2]

/-- **A morphism of torsors is equivariant on sections**: it carries the sectionwise action of
a section of the acting group to the sectionwise action of its base change. -/
theorem SheafTorsors.map_smulSection {T T' : SheafTorsors G} (φ : T ⟶ T')
    {V : BigFppfOver 𝒞 S hS} (gs : T.group.left.obj (op V)) (s : T.total.left.obj (op V))
    (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s) :
    φ.map.app (op V) (smulSection T.group T.total gs s h) =
      smulSection T'.group T'.total ((groupBaseChange φ.base φ.comp_sec).app (op V) gs)
        (φ.map.app (op V) s) (SheafTorsors.groupBaseChange_over φ gs s h) := by
  refine (yonedaEquiv_comp _ φ.map).symm.trans (congrArg yonedaEquiv ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ φ.smul_comp).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact eq_whisker (SheafTorsors.smulSectionLift_comp_actionBaseChange φ gs s h _) _

/-- **Equivariance of a morphism of total spaces is a condition on sections.** A morphism of
total spaces over a morphism `f` of the site which carries the sectionwise action of the acting
group of `T` to that of `T'` is equivariant in the sense of the morphisms of `𝒢/ℬ-Torsors`. -/
theorem SheafTorsors.smul_comp_of_sections {T T' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (hf : yoneda.map f ≫ T'.sec = T.sec) (gg : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = gg ≫ T'.total.hom)
    (hs : ∀ (V : BigFppfOver 𝒞 S hS) (gs : T.group.left.obj (op V))
      (s : T.total.left.obj (op V))
      (h : T.group.hom.app (op V) gs = T.total.hom.app (op V) s)
      (h' : T'.group.hom.app (op V) ((groupBaseChange f hf).app (op V) gs) =
        T'.total.hom.app (op V) (gg.app (op V) s)),
      gg.app (op V) (smulSection T.group T.total gs s h) =
        smulSection T'.group T'.total ((groupBaseChange f hf).app (op V) gs)
          (gg.app (op V) s) h') :
    (γ[T.group, T.total]).left ≫ gg =
      actionBaseChange f hf gg hg ≫ (γ[T'.group, T'.total]).left := by
  refine hom_ext_yoneda fun V p => ?_
  have h₀ : T.group.hom.app (op V)
        (yonedaEquiv (p ≫ pullback.fst T.group.hom T.total.hom)) =
      T.total.hom.app (op V)
        (yonedaEquiv (p ≫ pullback.snd T.group.hom T.total.hom)) := by
    rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.assoc, Category.assoc,
      pullback.condition]
  have hp : p = smulSectionLift T.group T.total
      (yonedaEquiv (p ≫ pullback.fst T.group.hom T.total.hom))
      (yonedaEquiv (p ≫ pullback.snd T.group.hom T.total.hom)) h₀ := by
    apply pullback.hom_ext
    · exact (Equiv.symm_apply_apply yonedaEquiv _).symm.trans
        (smulSectionLift_fst T.group T.total _ _ h₀).symm
    · exact (Equiv.symm_apply_apply yonedaEquiv _).symm.trans
        (smulSectionLift_snd T.group T.total _ _ h₀).symm
  have h₁ : T'.group.hom.app (op V) ((groupBaseChange f hf).app (op V)
        (yonedaEquiv (p ≫ pullback.fst T.group.hom T.total.hom))) =
      T'.total.hom.app (op V) (gg.app (op V)
        (yonedaEquiv (p ≫ pullback.snd T.group.hom T.total.hom))) := by
    have e1 : T'.group.hom.app (op V) ((groupBaseChange f hf).app (op V)
          (yonedaEquiv (p ≫ pullback.fst T.group.hom T.total.hom))) =
        T.group.hom.app (op V) (yonedaEquiv (p ≫ pullback.fst T.group.hom T.total.hom)) ≫ f :=
      ConcreteCategory.congr_hom (NatTrans.congr_app (groupBaseChange_snd f hf) (op V)) _
    have e2 : T.total.hom.app (op V) (yonedaEquiv (p ≫ pullback.snd T.group.hom T.total.hom)) ≫
        f = T'.total.hom.app (op V) (gg.app (op V)
          (yonedaEquiv (p ≫ pullback.snd T.group.hom T.total.hom))) :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hg (op V)) _
    exact e1.trans ((congrArg (· ≫ f) h₀).trans e2)
  have hl : smulSectionLift T.group T.total _ _ h₀ ≫ actionBaseChange f hf gg hg =
      smulSectionLift T'.group T'.total _ _ h₁ := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ?_
      refine (whisker_eq _ (actionBaseChange_fst _ _ _ _)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (eq_whisker (smulSectionLift_fst _ _ _ _ _) _).trans ?_
      refine (yonedaEquiv_symm_naturality_right _ _ _).trans ?_
      exact (smulSectionLift_fst T'.group T'.total _ _ h₁).symm
    · refine (Category.assoc _ _ _).trans ?_
      refine (whisker_eq _ (actionBaseChange_snd _ _ _ _)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (eq_whisker (smulSectionLift_snd _ _ _ _ _) _).trans ?_
      refine (yonedaEquiv_symm_naturality_right _ _ _).trans ?_
      exact (smulSectionLift_snd T'.group T'.total _ _ h₁).symm
  apply yonedaEquiv.injective
  rw [hp]
  refine Eq.trans (congrArg yonedaEquiv (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (yonedaEquiv_comp _ gg) ?_
  refine Eq.trans (hs V _ _ h₀ h₁) ?_
  refine Eq.trans ?_ (congrArg yonedaEquiv (Category.assoc _ _ _))
  exact congrArg yonedaEquiv (congrArg (· ≫ (γ[T'.group, T'.total]).left) hl.symm)

/-- **Cartesianness is a condition on sections.** A morphism of total spaces over `f` which over
every section `a` of the base is a bijection from the sections over `a` onto the sections over
`a ≫ f` makes the square of total spaces cartesian. -/
theorem SheafTorsors.isPullback_of_bijOn {T T' : SheafTorsors G} (f : T.base ⟶ T'.base)
    (gg : T.total.left ⟶ T'.total.left)
    (hg : T.total.hom ≫ yoneda.map f = gg ≫ T'.total.hom)
    (hbij : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (a : V.unop ⟶ T.base),
      Set.BijOn (gg.app V) {s : T.total.left.obj V | T.total.hom.app V s = a}
        {s' : T'.total.left.obj V | T'.total.hom.app V s' = a ≫ f}) :
    IsPullback gg T.total.hom T'.total.hom (yoneda.map f) := by
  have hw : gg ≫ T'.total.hom = T.total.hom ≫ yoneda.map f := hg.symm
  have hiso : IsIso (pullback.lift gg T.total.hom hw) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    rw [isIso_iff_bijective]
    have hpb := (IsPullback.of_hasPullback T'.total.hom (yoneda.map f)).map
      ((evaluation (BigFppfOver 𝒞 S hS)ᵒᵖ (Type u)).obj V)
    have hfst : ∀ x : T.total.left.obj V,
        (pullback.fst T'.total.hom (yoneda.map f)).app V
          ((pullback.lift gg T.total.hom hw).app V x) = gg.app V x := fun x =>
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (pullback.lift_fst gg T.total.hom hw) V) x
    have hsnd : ∀ x : T.total.left.obj V,
        (pullback.snd T'.total.hom (yoneda.map f)).app V
          ((pullback.lift gg T.total.hom hw).app V x) = T.total.hom.app V x := fun x =>
      ConcreteCategory.congr_hom
        (NatTrans.congr_app (pullback.lift_snd gg T.total.hom hw) V) x
    refine ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have h1 : T.total.hom.app V x = T.total.hom.app V y :=
        ((hsnd x).symm.trans (congrArg _ hxy)).trans (hsnd y)
      have h2 : gg.app V x = gg.app V y :=
        ((hfst x).symm.trans (congrArg _ hxy)).trans (hfst y)
      exact (hbij V (T.total.hom.app V x)).injOn rfl h1.symm h2
    · have hcz : T'.total.hom.app V ((pullback.fst T'.total.hom (yoneda.map f)).app V z) =
          (pullback.snd T'.total.hom (yoneda.map f)).app V z ≫ f :=
        ConcreteCategory.congr_hom (NatTrans.congr_app
          (pullback.condition (f := T'.total.hom) (g := yoneda.map f)) V) z
      obtain ⟨x, hx1, hx2⟩ := (hbij V
        ((pullback.snd T'.total.hom (yoneda.map f)).app V z)).surjOn hcz
      exact ⟨x, Types.ext_of_isPullback hpb ((hfst x).trans hx2) ((hsnd x).trans hx1)⟩
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso (pullback.lift gg T.total.hom hw))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end Sections

/-! ### The identification of the acting groups with an abelian sheaf -/

variable (G : Grp (Over ℬ)) (A : Sheaf (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u})

/-- The base change `U ×_{b, ℬ} 𝒢 ⟶ U' ×_{b', ℬ} 𝒢` of the acting group along a morphism
`f : U ⟶ U'` of the site with `b = b' ∘ f`. -/
def pullbackGroupMap {U U' : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ ℬ}
    {b' : yoneda.obj U' ⟶ ℬ} (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) :
    pullback G.X.hom b ⟶ pullback G.X.hom b' :=
  pullback.map _ _ _ _ (𝟙 G.X.left) (yoneda.map f) (𝟙 ℬ) (by simp) (by simp [hf])

/-- **The identification of the acting groups with an abelian sheaf.** For every object `U` of
the big fppf site and every section `b` of `ℬ` over `U`, an identification of the sheaf of
groups of sections of `U ×_{b, ℬ} 𝒢` on the localized site `(Sch/U)_fppf` with the restriction
`A|_U`, compatible with base change along morphisms of the site lying over `ℬ`. The test object
of the localized site at `U'` is given as `Over.mk a` for a morphism `a` equal to the composite,
so that the condition applies at the test objects which computations produce. -/
structure AbelianGroupData (hG : ∀ (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ ℬ),
      Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) (sheafPullbackGroup G U b).X.left) where
  /-- The identification of the sections of `U ×_{b, ℬ} 𝒢` with those of `A|_U`. -/
  equiv : ∀ (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ ℬ),
    SheafOfGroups.SectionEquiv (abelianSheafAsGroupSheaf (A.over U))
      (sliceSheafOfGroups (sheafPullbackGroup G U b).X (hG U b))
  /-- The identification is compatible with base change along a morphism over `ℬ`. -/
  equiv_baseChange : ∀ {U U' : BigFppfOver 𝒞 S hS} {b : yoneda.obj U ⟶ ℬ}
    {b' : yoneda.obj U' ⟶ ℬ} (f : U ⟶ U') (hf : yoneda.map f ≫ b' = b) (W : Over U)
    (a : W.left ⟶ U') (_ : a = W.hom ≫ f)
    (x : (abelianSheafAsGroupSheaf (A.over U)).presheaf.obj (op W)),
    ((equiv U' b').equiv (op (Over.mk a)) x).1 =
      (pullbackGroupMap G f hf).app (op W.left) ((equiv U b).equiv (op W) x).1

variable {G A} {hG : ∀ (U : BigFppfOver 𝒞 S hS) (b : yoneda.obj U ⟶ ℬ),
      Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) (sheafPullbackGroup G U b).X.left}
  (D : AbelianGroupData G A hG)

/-- **The torsor of sections of an object of `𝒢/ℬ-Torsors`.** For an object `(U, b, F)`, the
sections of `F` over the localized site `(Sch/U)_fppf` form a torsor under the sections of the
acting group (`AlgebraicGeometry.Space.slicePseudoTorsor`), read as a torsor under `A|_U`
through the identification `D`. -/
def SheafTorsors.abelianTorsor (T : SheafTorsors G) : AbelianTorsor (A.over T.base) :=
  ⟨(slicePseudoTorsor T.group T.total (hG T.base T.sec) T.isSheaf T.isPseudoTorsor).transport
      (D.equiv T.base T.sec),
    PseudoTorsor.transport_isTorsor _ _
      (isTorsor_slicePseudoTorsor_of_isLocallySurjective 𝒞 S hS T.group T.total
        (hG T.base T.sec) T.isSheaf T.isPseudoTorsor T.isLocallySurjective)⟩

/-- The sections of the torsor of an object are the sections of its total space lying over the
test object. -/
theorem SheafTorsors.abelianTorsor_presheaf (T : SheafTorsors G) :
    (T.abelianTorsor D).1.presheaf = sliceSection T.total :=
  rfl

/-- A section of `A` acts on the sections of the torsor of an object by the sectionwise action
of the section of the acting group it is identified with. -/
theorem SheafTorsors.abelianTorsor_act_fst (T : SheafTorsors G) (W : (Over T.base)ᵒᵖ)
    (x : (abelianSheafAsGroupSheaf (A.over T.base)).presheaf.obj W)
    (s : (sliceSection T.total).obj W) :
    ((T.abelianTorsor D).1.act W x s : (sliceSection T.total).obj W).1 =
      smulSection T.group T.total ((D.equiv T.base T.sec).equiv W x).1 s.1
        (((D.equiv T.base T.sec).equiv W x).2.trans s.2.symm) :=
  rfl

/-- The restriction along a morphism of `𝒢/ℬ-Torsors` of the sections of the torsor of its
target: a section of the source over `(V, a)` goes to its image, a section of the target over
`(V, a ≫ f)`. -/
def SheafTorsors.Hom.sliceMap {T T' : SheafTorsors G} (φ : T ⟶ T') (W : (Over T.base)ᵒᵖ)
    (s : (sliceSection T.total).obj W) :
    (sliceSection T'.total).obj (op ((Over.map φ.base).obj W.unop)) :=
  ⟨φ.map.app (op W.unop.left) s.1, by
    have h : T'.total.hom.app (op W.unop.left) (φ.map.app (op W.unop.left) s.1) =
        T.total.hom.app (op W.unop.left) s.1 ≫ φ.base :=
      ConcreteCategory.congr_hom (NatTrans.congr_app φ.isPullback.w (op W.unop.left)) s.1
    exact h.trans (congrArg (· ≫ φ.base) s.2)⟩

/-- The underlying section of the image of a section under `SheafTorsors.Hom.sliceMap`. -/
theorem SheafTorsors.Hom.sliceMap_val {T T' : SheafTorsors G} (φ : T ⟶ T') (W : (Over T.base)ᵒᵖ)
    (s : (sliceSection T.total).obj W) :
    (SheafTorsors.Hom.sliceMap φ W s).1 = φ.map.app (op W.unop.left) s.1 :=
  rfl

/-! ### The object of `𝒢/ℬ-Torsors` attached to a torsor under `A|_U` -/

section Globalization

variable {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ)
  (F : PseudoTorsor.{u} (abelianSheafAsGroupSheaf (A.over U)))

/-- The total space attached to a pseudo-torsor on the localized site: the coproduct presheaf
`V ↦ ∐_{a : V ⟶ U} F(V, a)` over the representable presheaf of `U`. -/
abbrev globalTotal : Over (yoneda.obj U) :=
  OverShriek.presheafFunctorToOver.obj F.presheaf

/-- The action on a section of the total space of a section of the acting group lying over the
same morphism to `U`: through the identification `D`, the section of the acting group is a
section of `A`, which acts on the second component. -/
def globalActPt {V : (BigFppfOver 𝒞 S hS)ᵒᵖ} (gs : (sheafPullbackGroup G U b).X.left.obj V)
    (p : (globalTotal F).left.obj V)
    (h : (sheafPullbackGroup G U b).X.hom.app V gs = p.1) : (globalTotal F).left.obj V :=
  ⟨p.1, F.act (op (Over.mk p.1)) ((D.equiv U b).symm.equiv (op (Over.mk p.1)) ⟨gs, h⟩) p.2⟩

/-- A point of the acting group, read at a section of its source lying over `a`, is the section
of the acting group attached to the corresponding point of the localized site. -/
theorem sliceSection_point_eq {Z : Over (yoneda.obj U)}
    (m : Z ⟶ (sheafPullbackGroup G U b).X) {V : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    (z : Z.left.obj V) (a : V.unop ⟶ U) (hz : Z.hom.app V z = a)
    (hm : (sheafPullbackGroup G U b).X.hom.app V (m.left.app V z) = a) :
    (⟨m.left.app V z, hm⟩ : (sliceSection (sheafPullbackGroup G U b).X).obj (op (Over.mk a))) =
      sliceSectionEquiv (sheafPullbackGroup G U b).X (Over.mk a)
        (Over.homMk (yonedaEquiv.symm z) (by
          apply yonedaEquiv.injective
          rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
          exact hz.trans (yonedaEquiv_yoneda_map a).symm) ≫ m) := by
  refine Subtype.ext ?_
  exact (congrArg (fun t => m.left.app V t) (Equiv.apply_symm_apply yonedaEquiv z).symm).trans
    (yonedaEquiv_comp _ _).symm

/-- The lying-over condition of a point of the acting group and a point of the total space
with the same source. -/
theorem globalPt_over {Z : Over (yoneda.obj U)} (m : Z ⟶ (sheafPullbackGroup G U b).X)
    (x : Z ⟶ globalTotal F) (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (z : Z.left.obj V) :
    (sheafPullbackGroup G U b).X.hom.app V (m.left.app V z) = (x.left.app V z).1 := by
  have e1 : (sheafPullbackGroup G U b).X.hom.app V (m.left.app V z) = Z.hom.app V z :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (Over.w m) V) z
  have e2 : (globalTotal F).hom.app V (x.left.app V z) = Z.hom.app V z :=
    ConcreteCategory.congr_hom (NatTrans.congr_app (Over.w x) V) z
  exact e1.trans e2.symm

/-- The action of the points of the acting group on the points of the total space. -/
def globalAct (Z : Over (yoneda.obj U)) (m : Z ⟶ (sheafPullbackGroup G U b).X)
    (x : Z ⟶ globalTotal F) : Z ⟶ globalTotal F :=
  Over.homMk
    { app V := ↾fun z => globalActPt D b F (m.left.app V z) (x.left.app V z)
        (globalPt_over b F m x V z)
      naturality V V' g := by
        ext z
        change globalActPt D b F (m.left.app V' (Z.left.map g z)) (x.left.app V' (Z.left.map g z))
            _ = (globalTotal F).left.map g (globalActPt D b F (m.left.app V z)
              (x.left.app V z) _)
        have hx : x.left.app V' (Z.left.map g z) = (globalTotal F).left.map g (x.left.app V z) :=
          NatTrans.naturality_apply x.left g z
        have hm : m.left.app V' (Z.left.map g z) =
            (sheafPullbackGroup G U b).X.left.map g (m.left.app V z) :=
          NatTrans.naturality_apply m.left g z
        have key : ∀ (gs₀ : (sheafPullbackGroup G U b).X.left.obj V)
            (p₀ : (globalTotal F).left.obj V)
            (h₀ : (sheafPullbackGroup G U b).X.hom.app V gs₀ = p₀.1)
            (gs : (sheafPullbackGroup G U b).X.left.obj V') (p : (globalTotal F).left.obj V')
            (hp : (sheafPullbackGroup G U b).X.hom.app V' gs = p.1)
            (_ : gs = (sheafPullbackGroup G U b).X.left.map g gs₀)
            (_ : p = (globalTotal F).left.map g p₀),
            globalActPt D b F gs p hp =
              (globalTotal F).left.map g (globalActPt D b F gs₀ p₀ h₀) := by
          intro gs₀ p₀ h₀ gs p hp hgs hpp
          subst hgs hpp
          obtain ⟨a, t⟩ := p₀
          change (⟨g.unop ≫ a, _⟩ : Σ φ : V'.unop ⟶ U, F.presheaf.obj (op (Over.mk φ))) =
            ⟨g.unop ≫ a, _⟩
          congr 1
          change F.act _ _ (F.presheaf.map (Over.homMk g.unop rfl :
              Over.mk (g.unop ≫ a) ⟶ Over.mk a).op t) =
            F.presheaf.map (Over.homMk g.unop rfl : Over.mk (g.unop ≫ a) ⟶ Over.mk a).op
              (F.act _ _ t)
          rw [F.naturality]
          congr 1
          exact (congrArg ((D.equiv U b).symm.equiv _) (Subtype.ext rfl)).trans
            ((D.equiv U b).symm.naturality
              (Over.homMk g.unop rfl : Over.mk (g.unop ≫ a) ⟶ Over.mk a).op ⟨gs₀, h₀⟩)
        exact key _ _ _ _ _ _ hm hx }
    (by
      ext V z
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (Over.w x) V) z)

/-- The points of the acting group lying over a section of the total space. -/
theorem globalAct_left_app {Z : Over (yoneda.obj U)} (m : Z ⟶ (sheafPullbackGroup G U b).X)
    (x : Z ⟶ globalTotal F) (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (z : Z.left.obj V) :
    (globalAct D b F Z m x).left.app V z =
      globalActPt D b F (m.left.app V z) (x.left.app V z) (globalPt_over b F m x V z) :=
  rfl

/-- The section of `A` attached to a point of the acting group at a section of its source. -/
theorem globalAct_section_eq {Z : Over (yoneda.obj U)} (m : Z ⟶ (sheafPullbackGroup G U b).X)
    (x : Z ⟶ globalTotal F) (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (z : Z.left.obj V) :
    (⟨m.left.app V z, globalPt_over b F m x V z⟩ :
        (sliceSection (sheafPullbackGroup G U b).X).obj (op (Over.mk (x.left.app V z).1))) =
      sliceSectionEquiv (sheafPullbackGroup G U b).X (Over.mk (x.left.app V z).1)
        (Over.homMk (yonedaEquiv.symm z) (by
          apply yonedaEquiv.injective
          have e2 : (globalTotal F).hom.app V (x.left.app V z) = Z.hom.app V z :=
            ConcreteCategory.congr_hom (NatTrans.congr_app (Over.w x) V) z
          rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
          exact e2.symm.trans (yonedaEquiv_yoneda_map _).symm) ≫ m) :=
  sliceSection_point_eq b m z _
    (ConcreteCategory.congr_hom (NatTrans.congr_app (Over.w x) V) z).symm _

/-- The group law of the sections of a group object over the localized site, read on points. -/
theorem sliceSectionEquiv_mul {X : Over (yoneda.obj U)} [GrpObj X]
    (hX : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) X.left) (W : Over U)
    (f g : sliceOver W ⟶ X) :
    (sliceSectionEquiv X W (f * g) : (sliceSheafOfGroups X hX).presheaf.obj (op W)) =
      Mul.mul (α := (sliceSheafOfGroups X hX).presheaf.obj (op W))
        (sliceSectionEquiv X W f) (sliceSectionEquiv X W g) :=
  ((sliceSheafOfGroups_mul X hX (op W) _ _).trans (by simp only [Equiv.symm_apply_apply]; rfl)).symm

/-- **The action of the acting group on the total space.** -/
abbrev globalModObj : ModObj (sheafPullbackGroup G U b).X (globalTotal F) :=
  ModObj.ofHomAction (globalAct D b F)
    (fun g m x => by
      apply Over.OverMorphism.ext
      ext V z
      rfl)
    (fun Z x => by
      apply Over.OverMorphism.ext
      ext V z
      change globalActPt D b F _ (x.left.app V z) _ = x.left.app V z
      have h1 := globalAct_section_eq b F (1 : Z ⟶ (sheafPullbackGroup G U b).X) x V z
      rw [MonObj.comp_one] at h1
      change (⟨(x.left.app V z).1, F.act _ ((D.equiv U b).symm.equiv _ _)
        (x.left.app V z).2⟩ : Σ φ : V.unop ⟶ U, F.presheaf.obj (op (Over.mk φ))) = _
      rw [h1, ← sliceSheafOfGroups_one _ (hG U b) (op (Over.mk _)),
        SheafOfGroups.SectionEquiv.map_one, F.one_act]
      rfl)
    (fun Z m n x => by
      apply Over.OverMorphism.ext
      ext V z
      change globalActPt D b F _ (x.left.app V z) _ =
        globalActPt D b F _ (globalActPt D b F _ (x.left.app V z) _) _
      have hm := globalAct_section_eq b F m x V z
      have hn := globalAct_section_eq b F n x V z
      have hmn := globalAct_section_eq b F (m * n) x V z
      rw [MonObj.comp_mul] at hmn
      have key : (D.equiv U b).symm.equiv (op (Over.mk (x.left.app V z).1))
          ⟨(m * n).left.app V z, globalPt_over b F (m * n) x V z⟩ =
          (D.equiv U b).symm.equiv (op (Over.mk (x.left.app V z).1))
            ⟨m.left.app V z, globalPt_over b F m x V z⟩ *
          (D.equiv U b).symm.equiv (op (Over.mk (x.left.app V z).1))
            ⟨n.left.app V z, globalPt_over b F n x V z⟩ := by
        refine (congrArg ((D.equiv U b).symm.equiv (op (Over.mk (x.left.app V z).1)))
          (hmn.trans ((sliceSectionEquiv_mul (hG U b) _ _ _).trans
            (congrArg₂ (Mul.mul (α := (sliceSheafOfGroups (sheafPullbackGroup G U b).X
              (hG U b)).presheaf.obj (op (Over.mk (x.left.app V z).1)))) hm.symm hn.symm)))).trans
          ((D.equiv U b).symm.map_mul _ _ _)
      refine congrArg (Sigma.mk (x.left.app V z).1) ?_
      exact (congrArg (fun c => F.act (op (Over.mk (x.left.app V z).1))
        c (x.left.app V z).2) key).trans (F.mul_act _ _ _ _))

/-- The sectionwise action is determined by its arguments. -/
theorem globalActPt_congr {V : (BigFppfOver 𝒞 S hS)ᵒᵖ}
    {gs gs' : (sheafPullbackGroup G U b).X.left.obj V} {p p' : (globalTotal F).left.obj V}
    (h : (sheafPullbackGroup G U b).X.hom.app V gs = p.1)
    (h' : (sheafPullbackGroup G U b).X.hom.app V gs' = p'.1) (hg : gs = gs') (hp : p = p') :
    globalActPt D b F gs p h = globalActPt D b F gs' p' h' := by
  subst hg hp
  rfl

/-- **The action on the localized site is the action of `A|_U` on `F`.** Through the
identification of `F` with the sections of the total space over the localized site
(`PseudoTorsor.sliceIsoObj`), the action of the acting group on those sections is the given
action of `A|_U` on `F`. -/
theorem globalTotal_sliceAction (W : Over U)
    (g : (abelianSheafAsGroupSheaf (A.over U)).presheaf.obj (op W))
    (t : F.presheaf.obj (op W)) :
    letI := globalModObj D b F
    sliceAction (sheafPullbackGroup G U b).X (globalTotal F) W
        ((D.equiv U b).equiv (op W) g)
        ((F.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)).hom.app (op W) t) =
      (F.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)).hom.app (op W)
        (F.act (op W) g t) := by
  let := globalModObj D b F
  apply Subtype.ext
  refine (sliceAction_fst _ _ _ _ _).trans ?_
  have hL := smulSectionLift_fst (sheafPullbackGroup G U b).X (globalTotal F)
    ((D.equiv U b).equiv (op W) g).1
    ((F.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)).hom.app (op W) t).1
    (((D.equiv U b).equiv (op W) g).2.trans
      ((F.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)).hom.app (op W) t).2.symm)
  have hR := smulSectionLift_snd (sheafPullbackGroup G U b).X (globalTotal F)
    ((D.equiv U b).equiv (op W) g).1
    ((F.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)).hom.app (op W) t).1
    (((D.equiv U b).equiv (op W) g).2.trans
      ((F.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)).hom.app (op W) t).2.symm)
  refine (yonedaEquiv_comp _ _).trans ?_
  refine (globalAct_left_app D b F _ _ _ _).trans ?_
  refine (globalActPt_congr D b F _ ((D.equiv U b).equiv (op W) g).2
    ((yonedaEquiv_comp _ _).symm.trans ((congrArg yonedaEquiv hL).trans
      (Equiv.apply_symm_apply _ _)))
    ((yonedaEquiv_comp _ _).symm.trans ((congrArg yonedaEquiv hR).trans
      (Equiv.apply_symm_apply _ _)))).trans ?_
  change (⟨W.hom, F.act (op (Over.mk W.hom)) ((D.equiv U b).symm.equiv (op (Over.mk W.hom))
      ((D.equiv U b).equiv (op W) g)) t⟩ :
      Σ φ : W.left ⟶ U, F.presheaf.obj (op (Over.mk φ))) = ⟨W.hom, F.act (op W) g t⟩
  exact congrArg (Sigma.mk W.hom) (congrArg (fun c => F.act (op W) c t)
    (((D.equiv U b).equiv (op W)).symm_apply_apply g))

/-- The action on the total space is a pseudo-torsor. -/
theorem globalTotal_isPseudoTorsor :
    letI := globalModObj D b F
    IsPseudoTorsor (sheafPullbackGroup G U b).X (globalTotal F) := by
  let := globalModObj D b F
  refine isPseudoTorsor_of_relativeSiteTorsorData 𝒞 S hS (sheafPullbackGroup G U b).X
    (globalTotal F) (abelianSheafAsGroupSheaf (A.over U)) F
    (NatIso.ofComponents (fun W => ((D.equiv U b).equiv W).toIso) (fun f => by
      ext g
      exact (D.equiv U b).naturality f g))
    (F.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)) ?_
  intro W g t
  exact (globalTotal_sliceAction D b F W g t).symm

/-- **The object of `𝒢/ℬ-Torsors` attached to a torsor under `A|_U`**: its total space is the
coproduct presheaf of the torsor over the representable presheaf of `U`, on which the acting
group acts through the identification `D`. -/
def SheafTorsors.ofAbelianTorsor (T : AbelianTorsor (A.over U)) : SheafTorsors G where
  base := U
  sec := b
  total := globalTotal T.1
  action := globalModObj D b T.1
  isTorsor := ⟨T.1.isSheaf_overYonedaObj (J := BigFppfOver.topology 𝒞 S hS)
      (isAlgebraicSpace_yoneda 𝒞 S hS U).isSheaf,
    globalTotal_isPseudoTorsor D b T.1,
    T.1.isLocallySurjective_overYonedaObj_hom (J := BigFppfOver.topology 𝒞 S hS) T.2⟩

/-- The torsor of sections of the object attached to a torsor `T` is isomorphic to `T`. -/
theorem SheafTorsors.ofAbelianTorsor_isIsomorphic (T : AbelianTorsor (A.over U)) :
    T.IsIsomorphic ((SheafTorsors.ofAbelianTorsor D b T).abelianTorsor D) :=
  ⟨⟨(T.1.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)).hom, fun W g t =>
      (globalTotal_sliceAction D b T.1 W.unop g t).symm⟩,
    inferInstanceAs (IsIso (T.1.sliceIsoObj (J := BigFppfOver.topology 𝒞 S hS)).hom)⟩

end Globalization

variable [HasSheafify (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u})]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u})]
  [(BigFppfOver.topology 𝒞 S hS).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u}]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasSheafify ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u}]
  [HasExt.{w} (Sheaf (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u})]
  [∀ U : BigFppfOver 𝒞 S hS,
    HasExt.{w} (Sheaf ((BigFppfOver.topology 𝒞 S hS).over U) AddCommGrpCat.{u})]
  [EnoughInjectives (Sheaf (BigFppfOver.topology 𝒞 S hS) AddCommGrpCat.{u})]
  [(BigFppfOver.topology 𝒞 S hS).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The restriction along a morphism of the sections of the torsor of its target is
equivariant. -/
theorem SheafTorsors.Hom.sliceMap_act {T T' : SheafTorsors G} (φ : T ⟶ T') (W : (Over T.base)ᵒᵖ)
    (x : (abelianSheafAsGroupSheaf (A.over T.base)).presheaf.obj W)
    (s : (sliceSection T.total).obj W) :
    SheafTorsors.Hom.sliceMap φ W ((T.abelianTorsor D).1.act W x s) =
      (T'.abelianTorsor D).1.act (op ((Over.map φ.base).obj W.unop)) x
        (SheafTorsors.Hom.sliceMap φ W s) :=
  Subtype.ext ((SheafTorsors.map_smulSection φ ((D.equiv T.base T.sec).equiv W x).1 s.1
    (((D.equiv T.base T.sec).equiv W x).2.trans s.2.symm)).trans
      (smulSection_congr (h' := (((D.equiv T'.base T'.sec).equiv
        (op ((Over.map φ.base).obj W.unop)) x).2.trans (SheafTorsors.Hom.sliceMap φ W s).2.symm))
        _ _ (D.equiv_baseChange φ.base φ.comp_sec W.unop _ rfl x).symm rfl))

/-- **The class of an object of `𝒢/ℬ-Torsors`** `(U, b, F)` in `H¹(U, A)`: the class of the
torsor of sections of `F` under `A|_U`. -/
def SheafTorsors.h1Class (T : SheafTorsors G) : Sheaf.H' A 1 T.base :=
  torsorClassOver (BigFppfOver.topology 𝒞 S hS) A (T.abelianTorsor D)

/-- **The class is natural along morphisms of `𝒢/ℬ-Torsors`.** The class of the source of a
morphism lying over `f` is the restriction along `f` of the class of its target. -/
theorem SheafTorsors.h1Class_map {T T' : SheafTorsors G} (φ : T ⟶ T') :
    T.h1Class D = (A.cohomologyPresheaf 1).map φ.base.op (T'.h1Class D) := by
  refine torsorClassOver_map (BigFppfOver.topology 𝒞 S hS) A φ.base (T'.abelianTorsor D)
    (T.abelianTorsor D) (SheafTorsors.Hom.sliceMap φ) ?_ ?_
  · intro W W' g s
    change (sliceSection T.total).obj W at s
    have h : φ.map.app (op W'.unop.left) (T.total.left.map g.unop.left.op s.1) =
        T'.total.left.map g.unop.left.op (φ.map.app (op W.unop.left) s.1) :=
      NatTrans.naturality_apply φ.map g.unop.left.op s.1
    exact Subtype.ext h
  · intro W a s
    exact SheafTorsors.Hom.sliceMap_act D φ W (Multiplicative.ofAdd a) s

/-- **Objects with the same class are related by a morphism.** Suppose that a section of `ℬ`
over an object of the site is unique. If the class of `T₁` is the restriction along an
isomorphism `e` of bases of the class of `T₂`, then there is a morphism `T₁ ⟶ T₂` lying over
`e`: the torsors of sections are isomorphic after restriction along `e` (Tag 03AJ), and such an
isomorphism is a morphism of total spaces over `e` which is cartesian and equivariant. -/
theorem SheafTorsors.exists_hom_of_h1Class_eq
    (hb : ∀ (U : BigFppfOver 𝒞 S hS) (b b' : yoneda.obj U ⟶ ℬ), b = b')
    {T₁ T₂ : SheafTorsors G} (e : T₁.base ≅ T₂.base)
    (h : T₁.h1Class D = (A.cohomologyPresheaf 1).map e.hom.op (T₂.h1Class D)) :
    ∃ φ : T₁ ⟶ T₂, φ.base = e.hom := by
  rw [SheafTorsors.h1Class, SheafTorsors.h1Class, ← torsorClassOver_restrict] at h
  obtain ⟨E, hE⟩ := (torsorClassOver_eq_iff _ A _ _).1 h
  have : IsIso E.hom := hE
  have hEb : ∀ W, Function.Bijective (E.hom.app W) := fun W =>
    (isIso_iff_bijective _).1 inferInstance
  have hf : yoneda.map e.hom ≫ T₂.sec = T₁.sec := hb _ _ _
  -- the value of `E` on a section, at any object it lies over
  let ev : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (a : V.unop ⟶ T₁.base)
      (s : T₁.total.left.obj V), T₁.total.hom.app V s = a → T₂.total.left.obj V :=
    fun V a s hs => (E.hom.app (op (Over.mk a)) ⟨s, hs⟩).1
  have hev : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (a : V.unop ⟶ T₁.base)
      (s : T₁.total.left.obj V) (hs : T₁.total.hom.app V s = a),
      ev V a s hs = ev V _ s rfl := by
    intro V a s hs
    subst hs
    rfl
  have hev_over : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (a : V.unop ⟶ T₁.base)
      (s : T₁.total.left.obj V) (hs : T₁.total.hom.app V s = a),
      T₂.total.hom.app V (ev V a s hs) = a ≫ e.hom :=
    fun V a s hs => (E.hom.app (op (Over.mk a)) ⟨s, hs⟩).2
  let gg : T₁.total.left ⟶ T₂.total.left :=
    { app V := ↾fun s => ev V _ s rfl
      naturality V V' g := by
        ext s
        have ha' : T₁.total.hom.app V' (T₁.total.left.map g s) =
            g.unop ≫ T₁.total.hom.app V s :=
          NatTrans.naturality_apply T₁.total.hom g s
        let k : (Over.mk (g.unop ≫ T₁.total.hom.app V s) : Over T₁.base) ⟶
            Over.mk (T₁.total.hom.app V s) := Over.homMk g.unop rfl
        change ev V' _ (T₁.total.left.map g s) rfl = T₂.total.left.map g (ev V _ s rfl)
        rw [← hev V' _ _ ha']
        exact congrArg Subtype.val (NatTrans.naturality_apply E.hom k.op ⟨s, rfl⟩) }
  have hgg : ∀ (V : (BigFppfOver 𝒞 S hS)ᵒᵖ) (s : T₁.total.left.obj V),
      gg.app V s = ev V _ s rfl := fun _ _ => rfl
  have hg : T₁.total.hom ≫ yoneda.map e.hom = gg ≫ T₂.total.hom := by
    ext V s
    exact (hev_over V _ s rfl).symm
  have hpb : IsPullback gg T₁.total.hom T₂.total.hom (yoneda.map e.hom) := by
    refine SheafTorsors.isPullback_of_bijOn e.hom gg hg fun V a => ⟨?_, ?_, ?_⟩
    · intro s hs
      change T₂.total.hom.app V (gg.app V s) = a ≫ e.hom
      rw [hgg, ← hev V a s hs]
      exact hev_over V a s hs
    · intro s hs s' hs' hss'
      change gg.app V s = gg.app V s' at hss'
      rw [hgg, hgg, ← hev V a s hs, ← hev V a s' hs'] at hss'
      exact congrArg Subtype.val ((hEb (op (Over.mk a))).1 (Subtype.ext hss'))
    · intro t ht
      obtain ⟨⟨s, hs⟩, hst⟩ := (hEb (op (Over.mk a))).2 ⟨t, ht⟩
      refine ⟨s, hs, ?_⟩
      rw [hgg, ← hev V a s hs]
      exact congrArg Subtype.val hst
  have hsc : (γ[T₁.group, T₁.total]).left ≫ gg =
      actionBaseChange e.hom hf gg hg ≫ (γ[T₂.group, T₂.total]).left := by
    refine SheafTorsors.smul_comp_of_sections e.hom hf gg hg fun V gs s h₀ h₁ => ?_
    set a := T₁.total.hom.app (op V) s
    let x := ((D.equiv T₁.base T₁.sec).equiv (op (Over.mk a))).symm ⟨gs, h₀⟩
    have hx : ((D.equiv T₁.base T₁.sec).equiv (op (Over.mk a)) x).1 = gs := by
      exact congrArg Subtype.val (Equiv.apply_symm_apply _ _)
    have hact := E.map_act (op (Over.mk a)) x ⟨s, rfl⟩
    have h1 : smulSection T₁.group T₁.total gs s h₀ =
        ((T₁.abelianTorsor D).1.act (op (Over.mk a)) x ⟨s, rfl⟩ :
          (sliceSection T₁.total).obj (op (Over.mk a))).1 :=
      (smulSection_congr _ _ hx.symm rfl).trans
        (SheafTorsors.abelianTorsor_act_fst D T₁ (op (Over.mk a)) x ⟨s, rfl⟩).symm
    rw [h1, hgg, ← hev (op V) a _ (((T₁.abelianTorsor D).1.act (op (Over.mk a)) x ⟨s, rfl⟩ :
      (sliceSection T₁.total).obj (op (Over.mk a))).2)]
    refine (congrArg Subtype.val hact).trans ?_
    refine (SheafTorsors.abelianTorsor_act_fst D T₂ (op ((Over.map e.hom).obj (Over.mk a))) x
      _).trans ?_
    refine smulSection_congr _ _ ?_ (hev (op V) a s rfl).symm
    exact (D.equiv_baseChange e.hom hf (Over.mk a) (a ≫ e.hom) rfl x).trans
      (congrArg _ hx)
  exact ⟨⟨e.hom, hf, gg, hpb, hsc⟩, rfl⟩


/-- The class of the object attached to a torsor `T` under `A|_U` is the class of `T`. -/
theorem SheafTorsors.h1Class_ofAbelianTorsor {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ)
    (T : AbelianTorsor (A.over U)) :
    (SheafTorsors.ofAbelianTorsor D b T).h1Class D =
      torsorClassOver (BigFppfOver.topology 𝒞 S hS) A T :=
  ((torsorClassOver_eq_iff (BigFppfOver.topology 𝒞 S hS) A T _).2
    (SheafTorsors.ofAbelianTorsor_isIsomorphic D b T)).symm

/-- Every class in `H¹(U, A)` is the class of an object of `𝒢/ℬ-Torsors` over `U`, as soon as
`ℬ` has a section over `U`. -/
theorem SheafTorsors.exists_h1Class_eq {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ ℬ)
    (c : Sheaf.H' A 1 U) :
    ∃ (T : SheafTorsors G) (e : T.base ≅ U),
      T.h1Class D = (A.cohomologyPresheaf 1).map e.hom.op c := by
  obtain ⟨T₀, hT₀⟩ := torsorClassOver_surjective (BigFppfOver.topology 𝒞 S hS) A U c
  have hc : (A.cohomologyPresheaf 1).map (Iso.refl U).hom.op c = c := by
    rw [Iso.refl_hom, op_id, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨SheafTorsors.ofAbelianTorsor D b T₀, Iso.refl U,
    (SheafTorsors.h1Class_ofAbelianTorsor D b T₀).trans (hT₀.trans hc.symm)⟩

/-- **The class in `H¹` is a classifying invariant of `𝒢/ℬ-Torsors`**, in the sense of
`Deformation.Artin.IsClassifyingInvariant`, when `ℬ` has exactly one section over every object of
the site (for instance when `ℬ` is the base): it is natural along morphisms, every class is the
class of an object, and two objects whose classes agree along an isomorphism of their bases are
related by a morphism over that isomorphism. -/
theorem SheafTorsors.isClassifyingInvariant_h1Class
    (b₀ : ∀ U : BigFppfOver 𝒞 S hS, yoneda.obj U ⟶ ℬ)
    (hb : ∀ (U : BigFppfOver 𝒞 S hS) (b b' : yoneda.obj U ⟶ ℬ), b = b') :
    Deformation.Artin.IsClassifyingInvariant (p := SheafTorsors.projection G)
      (A.cohomologyPresheaf 1 ⋙ forget AddCommGrpCat.{w})
      (fun T => (T.h1Class D : Sheaf.H' A 1 T.base)) where
  naturality φ := SheafTorsors.h1Class_map D φ
  surjective U c := SheafTorsors.exists_h1Class_eq D (b₀ U) c
  injective _ _ e h := SheafTorsors.exists_hom_of_h1Class_eq D hb e h

end AlgebraicGeometry.Space

end
