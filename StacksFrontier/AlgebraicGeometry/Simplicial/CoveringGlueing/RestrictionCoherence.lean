module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenSimplicialSystem
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexOpenNaturality

/-!
# Coherence of derived restriction along arrows of a ringed site

Let `(C, O_C)` be a ringed site. Restriction `E ↦ E|_{C/V}` along an arrow `V ⟶ U` of `C` acts on
the derived categories of modules of the slices, and restricting in two steps is restricting
along the composite, through the canonical comparison
`AlgebraicGeometry.RingedSite.derivedOverMapComp`. This file records that these comparisons
satisfy the coherence laws of a pseudofunctor: the associativity law and the unit law.

The proofs are by restriction along the localization of cochain complexes: each comparison is
induced, in the sense of `CategoryTheory.NatTrans.IsInducedBy`, by a transformation of functors
on cochain complexes whose components are the identity on sections
(`SheafOfModules.FixesSections`), and two such transformations agree.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedOverMapFactors`: derived restriction is induced by
  restriction of complexes.
* `AlgebraicGeometry.RingedSite.overMapIdIso` and `.derivedOverMapIdIso`: restriction along an
  identity is the identity functor.

## Main results

* `AlgebraicGeometry.RingedSite.derivedOverMapComp_hom_isInducedBy`: the comparison of derived
  restrictions is induced by the comparison of restrictions of sheaves of modules.
* `AlgebraicGeometry.RingedSite.isInducedBy_ext_of_fixesSections`: two transformations of
  derived functors induced by transformations whose components fix sections agree.
* `AlgebraicGeometry.RingedSite.derivedOverMapComp_assoc`: the associativity law.
* `AlgebraicGeometry.RingedSite.derivedOverMapComp_hom_app_derivedOverMapIdIso`: the unit law.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- Reduces a component of a transformation of functors on cochain complexes, built from
transformations of functors on sheaves of modules, to a composite of components of the latter. -/
macro "simp_fixesSections" : tactic => `(tactic| simp only [NatTrans.comp_app,
  HomologicalComplex.comp_f, Functor.whiskerRight_app, Functor.whiskerLeft_app,
  Functor.associator_inv_app, Functor.associator_hom_app, HomologicalComplex.id_f,
  NatIso.mapHomologicalComplex_inv_app_f, NatIso.mapHomologicalComplex_hom_app_f,
  Functor.mapHomologicalComplex_map_f, Category.comp_id, Category.id_comp,
  Functor.mapHomologicalComplexCompIso, Iso.symm_inv, Iso.symm_hom])

/-- An elementary morphism of sheaves of modules fixing sections, for `fixes_sections`. -/
syntax "fixes_sections_atom" : tactic

/-- Proves that a composite of morphisms of sheaves of modules built from comparisons which are
the identity on sections fixes sections. -/
macro "fixes_sections" : tactic => `(tactic| repeat' (first
  | with_reducible apply SheafOfModules.FixesSections.comp
  | fixes_sections_atom
  | exact fun _ _ => HEq.rfl))

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- Restriction of sheaves of modules along an arrow, for the ring sheaf of a ringed site. -/
abbrev overMapModules {U V : X.C} (f : V ⟶ U) :=
  SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f

/-- Restriction of sheaves of modules along an arrow is an additive functor. -/
instance overMapModules_additive {U V : X.C} (f : V ⟶ U) : (X.overMapModules f).Additive :=
  overMap_additive.{u} _ f

/-- Restriction of sheaves of modules along an arrow preserves finite limits. -/
instance overMapModules_preservesFiniteLimits {U V : X.C} (f : V ⟶ U) :
    PreservesFiniteLimits (X.overMapModules f) :=
  overMap_preservesFiniteLimits.{u} _ f

/-- Restriction of sheaves of modules along an arrow preserves finite colimits. -/
instance overMapModules_preservesFiniteColimits {U V : X.C} (f : V ⟶ U) :
    PreservesFiniteColimits (X.overMapModules f) :=
  overMap_preservesFiniteColimits.{u} _ f

/-- Derived restriction along an arrow is induced by restriction of complexes. -/
abbrev derivedOverMapFactors {U V : X.C} (f : V ⟶ U) :
    DerivedCategory.Q ⋙ derivedOverMap.{0} X f ≅
      (X.overMapModules f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (X.overMapModules f).mapDerivedCategoryFactors

/-- The comparison of restrictions of sheaves of modules along a composite, from the composite to
the two-step restriction. -/
abbrev overMapCompInv {U V W : X.C} {f : V ⟶ U} {g : W ⟶ V} {h : W ⟶ U} (e : g ≫ f = h) :
    X.overMapModules h ≅ X.overMapModules f ⋙ X.overMapModules g :=
  (overMapCompIsoOfEq.{0} X e).symm

/-- The components of the comparison `X.overMapCompInv e` are the identity on sections. -/
theorem overMapCompInv_hom_app_fixesSections {U V W : X.C} {f : V ⟶ U} {g : W ⟶ V} {h : W ⟶ U}
    (e : g ≫ f = h)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    SheafOfModules.FixesSections ((X.overMapCompInv e).hom.app M) :=
  SheafOfModules.FixesSections.inv ((overMapCompIsoOfEq.{0} X e).app M)
    (LocallyGiven.overMapCompIsoOfEq_hom_app_fixesSections e M)

/-- The components of the inverse of the comparison `X.overMapCompInv e` are the identity on
sections. -/
theorem overMapCompInv_inv_app_fixesSections {U V W : X.C} {f : V ⟶ U} {g : W ⟶ V} {h : W ⟶ U}
    (e : g ≫ f = h)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    SheafOfModules.FixesSections ((X.overMapCompInv e).inv.app M) :=
  LocallyGiven.overMapCompIsoOfEq_hom_app_fixesSections e M

/-- The components of the inverse of the comparison `overMapCompIsoOfEq X e`, from the composite
restriction to the two-step restriction, are the identity on sections. -/
theorem overMapCompIsoOfEq_inv_app_fixesSections {U V W : X.C} {f : V ⟶ U} {g : W ⟶ V}
    {h : W ⟶ U} (e : g ≫ f = h)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    SheafOfModules.FixesSections ((overMapCompIsoOfEq.{0} X e).inv.app M) :=
  SheafOfModules.FixesSections.inv ((overMapCompIsoOfEq.{0} X e).app M)
    (LocallyGiven.overMapCompIsoOfEq_hom_app_fixesSections e M)

/-- The restriction along an arrow of a morphism of sheaves of modules which is the identity on
sections is the identity on sections. -/
theorem overMapModules_map_fixesSections {U V : X.C} (f : V ⟶ U)
    {A B : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)} {φ : A ⟶ B}
    (hφ : SheafOfModules.FixesSections φ) :
    SheafOfModules.FixesSections ((X.overMapModules f).map φ) :=
  fun _ x => hφ _ x

macro_rules
  | `(tactic| fixes_sections_atom) =>
    `(tactic| with_reducible apply
      AlgebraicGeometry.RingedSite.overMapCompIsoOfEq_inv_app_fixesSections)
macro_rules
  | `(tactic| fixes_sections_atom) =>
    `(tactic| with_reducible apply
      AlgebraicGeometry.RingedSite.LocallyGiven.overMapCompIsoOfEq_hom_app_fixesSections)
macro_rules
  | `(tactic| fixes_sections_atom) =>
    `(tactic| with_reducible apply AlgebraicGeometry.RingedSite.overMapModules_map_fixesSections)

/-- **The comparison of derived restrictions along a composite is induced by the comparison of
restrictions of sheaves of modules.** -/
theorem derivedOverMapComp_hom_isInducedBy {U V W : X.C} {f : V ⟶ U} {g : W ⟶ V} {h : W ⟶ U}
    (e : g ≫ f = h) :
    NatTrans.IsInducedBy (X.derivedOverMapFactors h)
      (Functor.compFactorization (X.derivedOverMapFactors f) (X.derivedOverMapFactors g))
      (derivedOverMapComp.{0} X e).hom
      (Functor.mapHomologicalComplexCompIso (X.overMapCompInv e).symm
        (ComplexShape.up ℤ)).inv := by
  intro C
  simp only [Functor.compFactorization_hom_app]
  simp only [derivedOverMapComp, Iso.symm_hom, Localization.liftNatIso_inv,
    Localization.liftNatTrans_app, Localization.Lifting.iso, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, Category.assoc,
    Iso.symm_inv, Iso.symm_symm_eq]
  simp only [derivedOverMapFactors, derivedOverMap, Category.assoc]
  simp [← Functor.map_comp_assoc]

/-- **Two transformations of derived functors induced by transformations of functors on cochain
complexes whose components fix sections agree.** -/
theorem isInducedBy_ext_of_fixesSections {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasDerivedCategory 𝒜] {𝒟 : Type*} [Category 𝒟]
    {L₂ : CochainComplex (SheafOfModules.{u} R) ℤ ⥤ 𝒟}
    {F G : DerivedCategory 𝒜 ⥤ 𝒟}
    {F₀ G₀ : CochainComplex 𝒜 ℤ ⥤ CochainComplex (SheafOfModules.{u} R) ℤ}
    {ΦF : DerivedCategory.Q ⋙ F ≅ F₀ ⋙ L₂}
    {ΦG : DerivedCategory.Q ⋙ G ≅ G₀ ⋙ L₂} {γ γ' : F ⟶ G} {γ₀ γ₀' : F₀ ⟶ G₀}
    (h : NatTrans.IsInducedBy ΦF ΦG γ γ₀) (h' : NatTrans.IsInducedBy ΦF ΦG γ' γ₀')
    (hγ₀ : ∀ (K : CochainComplex 𝒜 ℤ) (p : ℤ), SheafOfModules.FixesSections ((γ₀.app K).f p))
    (hγ₀' : ∀ (K : CochainComplex 𝒜 ℤ) (p : ℤ),
      SheafOfModules.FixesSections ((γ₀'.app K).f p)) :
    γ = γ' :=
  NatTrans.IsInducedBy.ext_of_eq (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) h h'
    (NatTrans.ext (funext fun K => HomologicalComplex.hom_ext _ _ fun p =>
      SheafOfModules.FixesSections.ext (hγ₀ K p) (hγ₀' K p)))

/-- **Associativity of the comparisons of derived restrictions.** For arrows
`k : Z ⟶ W`, `h : W ⟶ V`, `g : V ⟶ U`, the two ways of comparing restriction along the composite
with restriction in three steps agree. -/
theorem derivedOverMapComp_assoc {U V W Z : X.C} (g : V ⟶ U) (h : W ⟶ V) (k : Z ⟶ W)
    {hg : W ⟶ U} (e₁ : h ≫ g = hg) {kh : Z ⟶ V} (e₂ : k ≫ h = kh) {khg : Z ⟶ U}
    (e₃ : k ≫ hg = khg) (e₄ : kh ≫ g = khg) (E : LocalDerivedCategory.{0} X U) :
    (derivedOverMapComp.{0} X e₃).hom.app E ≫
        (derivedOverMap.{0} X k).map ((derivedOverMapComp.{0} X e₁).hom.app E) =
      (derivedOverMapComp.{0} X e₄).hom.app E ≫
        (derivedOverMapComp.{0} X e₂).hom.app ((derivedOverMap.{0} X g).obj E) := by
  have hL := (X.derivedOverMapComp_hom_isInducedBy e₃).comp
    ((X.derivedOverMapComp_hom_isInducedBy e₁).whiskerRight (X.derivedOverMapFactors k))
  have hR := ((X.derivedOverMapComp_hom_isInducedBy e₄).comp
    (NatTrans.IsInducedBy.whiskerLeft (X.derivedOverMapFactors g)
      (X.derivedOverMapComp_hom_isInducedBy e₂))).comp
    (NatTrans.IsInducedBy.associator_inv (X.derivedOverMapFactors g) (X.derivedOverMapFactors h)
      (X.derivedOverMapFactors k))
  have := isInducedBy_ext_of_fixesSections hL hR
    (fun K p => by simp_fixesSections; fixes_sections)
    (fun K p => by simp_fixesSections; fixes_sections)
  simpa using NatTrans.congr_app this E

/-- The factorization of the identity functor of a derived category through the localization of
cochain complexes. -/
abbrev derivedIdFactorization (𝒜 : Type*) [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜] :
    DerivedCategory.Q ⋙ 𝟭 (DerivedCategory 𝒜) ≅ 𝟭 (CochainComplex 𝒜 ℤ) ⋙ DerivedCategory.Q :=
  Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- The right unitor of a functor `F` into a derived category is induced by the right unitor of a
functor `F₀` on cochain complexes inducing it, through the factorization `derivedIdFactorization`
of the identity. -/
theorem _root_.CategoryTheory.NatTrans.IsInducedBy.rightUnitor_hom {𝒜 : Type*} [Category 𝒜]
    [Abelian 𝒜] [HasDerivedCategory 𝒜] {D₁ C₁ : Type*} [Category D₁] [Category C₁]
    {L₁ : C₁ ⥤ D₁} {F : D₁ ⥤ DerivedCategory 𝒜} {F₀ : C₁ ⥤ CochainComplex 𝒜 ℤ}
    (ΦF : L₁ ⋙ F ≅ F₀ ⋙ DerivedCategory.Q) :
    NatTrans.IsInducedBy (Functor.compFactorization ΦF (derivedIdFactorization 𝒜)) ΦF
      (Functor.rightUnitor F).hom (Functor.rightUnitor F₀).hom := fun c => by
  simp [Functor.compFactorization_hom_app]

/-- Restriction of complexes of sheaves of modules along an identity arrow is the identity. -/
def overMapIdComplexIso (U : X.C) :
    (X.overMapModules (𝟙 U)).mapHomologicalComplex (ComplexShape.up ℤ) ≅ 𝟭 _ :=
  NatIso.mapHomologicalComplex (Stacks.SheafOfModules.overMapIdIso _ U) _ ≪≫
    Functor.mapHomologicalComplexIdIso _ _

/-- The components of the identification of restriction of sheaves of modules along an identity
arrow with the identity functor are the identity on sections. -/
theorem overMapIdIso_hom_app_fixesSections (U : X.C)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    SheafOfModules.FixesSections
      ((Stacks.SheafOfModules.overMapIdIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).hom.app
        M) := fun T x =>
  Stacks.SheafOfModules.heq_presheaf_map_of_left_eq_id (p := T.unop.hom)
    (q := T.unop.hom ≫ 𝟙 U) M.val.presheaf ((Over.mapId U).inv.app T.unop) rfl x

/-- **Derived restriction along an identity arrow is the identity functor.** -/
def derivedOverMapIdIso (U : X.C) : derivedOverMap.{0} X (𝟙 U) ≅ 𝟭 _ :=
  NatIso.liftAlong (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (X.derivedOverMapFactors (𝟙 U)) (derivedIdFactorization _) (X.overMapIdComplexIso U)

/-- The identification `X.derivedOverMapIdIso U` of derived restriction along `𝟙 U` with the
identity is induced by the identification `X.overMapIdComplexIso U` on cochain complexes. -/
theorem derivedOverMapIdIso_hom_isInducedBy (U : X.C) :
    NatTrans.IsInducedBy (X.derivedOverMapFactors (𝟙 U)) (derivedIdFactorization _)
      (X.derivedOverMapIdIso U).hom (X.overMapIdComplexIso U).hom :=
  NatTrans.isInducedBy_liftAlong _ _ _ _

/-- **The unit law for the comparisons of derived restrictions.** Restricting along `f` and then
along the identity, compared with restriction along `f` through the comparison of the composite
`𝟙 ≫ f = f`, is the identity. -/
theorem derivedOverMapComp_hom_app_derivedOverMapIdIso {U V : X.C} (f : V ⟶ U)
    (e : 𝟙 V ≫ f = f) (E : LocalDerivedCategory.{0} X U) :
    (derivedOverMapComp.{0} X e).hom.app E ≫
        (X.derivedOverMapIdIso V).hom.app ((derivedOverMap.{0} X f).obj E) = 𝟙 _ := by
  have hL := ((X.derivedOverMapComp_hom_isInducedBy e).comp
    (NatTrans.IsInducedBy.whiskerLeft (X.derivedOverMapFactors f)
      (X.derivedOverMapIdIso_hom_isInducedBy V))).comp
    (NatTrans.IsInducedBy.rightUnitor_hom (X.derivedOverMapFactors f))
  have := isInducedBy_ext_of_fixesSections hL NatTrans.IsInducedBy.id
    (fun K p => by
      simp_fixesSections
      simp only [overMapIdComplexIso, Iso.trans_hom, NatTrans.comp_app,
        HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
        Functor.mapHomologicalComplexIdIso, Functor.rightUnitor_hom_app]
      fixes_sections
      exact X.overMapIdIso_hom_app_fixesSections V _)
    (fun K p => fun _ _ => HEq.rfl)
  simpa using NatTrans.congr_app this E

end AlgebraicGeometry.RingedSite

end
