module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedImmersionConormalBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem

/-!
# The cocycle law of the base change of the Zariski reading

For a morphism `τ : T' ⟶ T` of test objects, the base-change map of the Zariski reading
`AlgebraicGeometry.Space.zariskiReadingPullbackHom τ : τ^*(R_T N) ⟶ R_{T'}(φ^* N)` is the mate of
the identification `R_T ∘ φ_* ⟶ τ_* ∘ R_{T'}` of sections of a direct image.  Mates of pasted
squares are pasted mates, so the base-change maps obey the cocycle law: along `τ₁ ≫ τ₂` the
base-change map is the base change along `τ₂` followed by the base change along `τ₁`, read
through the composition laws of inverse images of modules on schemes and on algebraic spaces
(Stacks 03LU).

The law is first proved for abstract adjunctions (`transposeComparison_comp`, with its unit
counterpart `transposeComparison_id`), then instantiated once.  The composite `τ` is kept free,
with an equation `τ₁ ≫ τ₂ = τ`, so that no two spellings of the morphisms of the composite are
compared inside a large term; the strict form is deduced at the end.

## Main results

* `CategoryTheory.Adjunction.transposeComparison_comp` and
  `CategoryTheory.Adjunction.transposeComparisonNatTrans_comp`: the cocycle law of transposed
  comparisons of right adjoints.
* `CategoryTheory.Adjunction.transposeComparison_id`: the unit law of transposed comparisons.
* `AlgebraicGeometry.Space.zariskiDirectImageNatTrans_comp`: the cocycle law of the
  identification of sections of a direct image over Zariski opens.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_whisker_comp_of_eq` and
  `AlgebraicGeometry.Space.zariskiReadingPullbackHom_comp_of_eq`: the cocycle law of the base
  change of the Zariski reading, for a composite given under another name.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_comp`: the cocycle law along `τ₁ ≫ τ₂`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Adjunction

section Cocycle

variable {ℰ ℰ' ℰ'' 𝒵 𝒵' 𝒵'' : Type*} [Category ℰ] [Category ℰ'] [Category ℰ''] [Category 𝒵]
  [Category 𝒵'] [Category 𝒵'']
  {φ₂u : ℰ ⥤ ℰ'} {φ₂l : ℰ' ⥤ ℰ} {φ₁u : ℰ' ⥤ ℰ''} {φ₁l : ℰ'' ⥤ ℰ'} {φu : ℰ ⥤ ℰ''}
  {φl : ℰ'' ⥤ ℰ} {τ₂u : 𝒵 ⥤ 𝒵'} {τ₂l : 𝒵' ⥤ 𝒵} {τ₁u : 𝒵' ⥤ 𝒵''} {τ₁l : 𝒵'' ⥤ 𝒵'}
  {τu : 𝒵 ⥤ 𝒵''} {τl : 𝒵'' ⥤ 𝒵} {Z : ℰ ⥤ 𝒵} {Z' : ℰ' ⥤ 𝒵'} {Z'' : ℰ'' ⥤ 𝒵''}
  (a₂ : φ₂u ⊣ φ₂l) (a₁ : φ₁u ⊣ φ₁l) (a : φu ⊣ φl) (b₂ : τ₂u ⊣ τ₂l) (b₁ : τ₁u ⊣ τ₁l)
  (b : τu ⊣ τl) (σ₂ : φ₂l ⋙ Z ⟶ Z' ⋙ τ₂l) (σ₁ : φ₁l ⋙ Z' ⟶ Z'' ⋙ τ₁l)
  (σ : φl ⋙ Z ⟶ Z'' ⋙ τl) (eφ : φ₂u ⋙ φ₁u ≅ φu) (rφ : φ₁l ⋙ φ₂l ≅ φl)
  (eτ : τu ⟶ τ₂u ⋙ τ₁u) (rτ : τ₁l ⋙ τ₂l ⟶ τl)

omit [Category ℰ] [Category ℰ'] [Category ℰ''] in
/-- The transpose of a transposed comparison is the Zariski reading of the unit followed by the
comparison. -/
theorem homEquiv_transposeComparison {ℰ ℰ' 𝒵 𝒵' : Type*} [Category ℰ] [Category ℰ']
    [Category 𝒵] [Category 𝒵'] {φu : ℰ ⥤ ℰ'} {φl : ℰ' ⥤ ℰ} {τu : 𝒵 ⥤ 𝒵'} {τl : 𝒵' ⥤ 𝒵}
    {Z : ℰ ⥤ 𝒵} {Z' : ℰ' ⥤ 𝒵'} (adjφ : φu ⊣ φl) (adjτ : τu ⊣ τl) (σ : φl ⋙ Z ⟶ Z' ⋙ τl)
    (N : ℰ) :
    adjτ.homEquiv _ _ (transposeComparison adjφ adjτ σ N) =
      Z.map (adjφ.unit.app N) ≫ σ.app (φu.obj N) :=
  Equiv.apply_symm_apply _ _

/-- The transpose along a composite adjunction of a morphism out of the composite left adjoint,
read through a comparison `eτ` of left adjoints whose conjugate is `rτ`. -/
theorem homEquiv_app_comp_eq_comp_homEquiv (hτ : conjugateEquiv (b₂.comp b₁) b eτ = rτ)
    {X : 𝒵} {Y : 𝒵''} (f : τ₁u.obj (τ₂u.obj X) ⟶ Y) :
    b.homEquiv _ _ (eτ.app X ≫ f) =
      b₂.homEquiv _ _ (b₁.homEquiv _ _ f) ≫ rτ.app Y := by
  have hc := unit_conjugateEquiv (b₂.comp b₁) b eτ X
  rw [hτ] at hc
  have hn := rτ.naturality f
  simp only [Functor.comp_map] at hn
  rw [homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hc, Category.assoc]
  simp only [Functor.comp_obj]
  rw [← hn, ← Category.assoc]
  congr 1
  rw [comp_unit_app, homEquiv_unit, homEquiv_unit, Functor.map_comp]
  simp only [Functor.comp_obj, Category.assoc]

/-- **The cocycle law of transposed comparisons**: for adjunctions composing up to comparisons
of left and of right adjoints, and comparisons `σ₂`, `σ₁`, `σ` compatible with the comparisons
of right adjoints, the transposed comparison of the composite is the pasting of the two
transposed comparisons, read through the comparisons of left adjoints. -/
theorem transposeComparison_comp
    (hφ : eφ = leftAdjointUniq ((a₂.comp a₁).ofNatIsoRight rφ) a)
    (hτ : conjugateEquiv (b₂.comp b₁) b eτ = rτ)
    (hσ : ∀ M, Z.map (rφ.hom.app M) ≫ σ.app M =
      σ₂.app (φ₁l.obj M) ≫ τ₂l.map (σ₁.app M) ≫ rτ.app (Z''.obj M))
    (N : ℰ) :
    eτ.app (Z.obj N) ≫ τ₁u.map (transposeComparison a₂ b₂ σ₂ N) ≫
        transposeComparison a₁ b₁ σ₁ (φ₂u.obj N) ≫ Z''.map (eφ.hom.app N) =
      transposeComparison a b σ N := by
  have hu := unit_comp_map_unit_comp_map_eq_unit a₂ a₁ a rφ eφ hφ N
  apply (b.homEquiv _ _).injective
  rw [homEquiv_app_comp_eq_comp_homEquiv b₂ b₁ b eτ rτ hτ, homEquiv_transposeComparison,
    homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_naturality_right,
    homEquiv_transposeComparison, homEquiv_transposeComparison]
  have h₁ := congrArg τ₂l.map (σ₁.naturality (eφ.hom.app N))
  have h₂ := σ₂.naturality (a₁.unit.app (φ₂u.obj N) ≫ φ₁l.map (eφ.hom.app N))
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.map_comp] at h₁ h₂
  rw [← hu]
  simp only [Functor.map_comp, Category.assoc]
  rw [hσ]
  simp only [Category.assoc] at h₂ ⊢
  rw [reassoc_of% h₂, reassoc_of% h₁]

/-- `CategoryTheory.Adjunction.transposeComparison_comp`, as an equation of natural
transformations. -/
theorem transposeComparisonNatTrans_comp
    (hφ : eφ = leftAdjointUniq ((a₂.comp a₁).ofNatIsoRight rφ) a)
    (hτ : conjugateEquiv (b₂.comp b₁) b eτ = rτ)
    (hσ : Functor.whiskerRight rφ.hom Z ≫ σ =
      Functor.whiskerLeft φ₁l σ₂ ≫ Functor.whiskerRight σ₁ τ₂l ≫ Functor.whiskerLeft Z'' rτ) :
    Functor.whiskerLeft Z eτ ≫ Functor.whiskerRight (transposeComparisonNatTrans a₂ b₂ σ₂) τ₁u ≫
        Functor.whiskerLeft φ₂u (transposeComparisonNatTrans a₁ b₁ σ₁) ≫
          Functor.whiskerRight eφ.hom Z'' =
      transposeComparisonNatTrans a b σ := by
  ext N
  have hσ' : ∀ M, Z.map (rφ.hom.app M) ≫ σ.app M =
      σ₂.app (φ₁l.obj M) ≫ τ₂l.map (σ₁.app M) ≫ rτ.app (Z''.obj M) := fun M => by
    simpa using congrArg (fun t => t.app M) hσ
  simpa using transposeComparison_comp a₂ a₁ a b₂ b₁ b σ₂ σ₁ σ eφ rφ eτ rτ hφ hτ hσ' N

end Cocycle

section Unit

variable {ℰ 𝒵 : Type*} [Category ℰ] [Category 𝒵] {φu : ℰ ⥤ ℰ} {φl : ℰ ⥤ ℰ} {τu : 𝒵 ⥤ 𝒵}
  {τl : 𝒵 ⥤ 𝒵} {Z : ℰ ⥤ 𝒵} (a : φu ⊣ φl) (b : τu ⊣ τl) (σ : φl ⋙ Z ⟶ Z ⋙ τl)
  (eφ : φu ⟶ 𝟭 ℰ) (rφ : 𝟭 ℰ ⟶ φl) (eτ : τu ⟶ 𝟭 𝒵) (rτ : 𝟭 𝒵 ⟶ τl)

/-- **The unit law of transposed comparisons**: for adjunctions whose left adjoints are
compared with the identity, and a comparison `σ` compatible with the conjugate comparisons of
right adjoints, the transposed comparison is the comparison of left adjoints. -/
theorem transposeComparison_id (hφ : conjugateEquiv .id a eφ = rφ)
    (hτ : conjugateEquiv .id b eτ = rτ) (hσ : ∀ M, Z.map (rφ.app M) ≫ σ.app M = rτ.app (Z.obj M))
    (N : ℰ) :
    transposeComparison a b σ N ≫ Z.map (eφ.app N) = eτ.app (Z.obj N) := by
  have hcφ := unit_conjugateEquiv Adjunction.id a eφ N
  have hcτ := unit_conjugateEquiv Adjunction.id b eτ (Z.obj N)
  rw [hφ] at hcφ
  rw [hτ] at hcτ
  simp only [Adjunction.id, Functor.id_obj, NatTrans.id_app, Category.id_comp] at hcφ hcτ
  apply (b.homEquiv _ _).injective
  rw [homEquiv_naturality_right, homEquiv_transposeComparison, homEquiv_unit, ← hcτ, ← hσ N,
    hcφ]
  have h := σ.naturality (eφ.app N)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h
  rw [Category.assoc, ← h, Functor.map_comp_assoc]

end Unit

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

section OfEq

variable {P' P X : AlgebraicSpaces B S hS} (φ : P' ⟶ P) (f : P ⟶ X) (g : P' ⟶ X)
  (h : φ ≫ f = g)

/-- The comparison of direct images of a composite, with the composite given under another
name. -/
def pushforwardModulesCompAtOfEq :
    (smallEtaleRingedToposHom B S hS φ).pushforwardModules ⋙
        (smallEtaleRingedToposHom B S hS f).pushforwardModules ≅
      (smallEtaleRingedToposHom B S hS g).pushforwardModules :=
  pushforwardModulesCompAt B S hS φ f ≪≫
    eqToIso (congrArg (fun k => (smallEtaleRingedToposHom B S hS k).pushforwardModules) h)

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_eq_leftAdjointUniq_etale`, with the composite
given under another name. -/
theorem modulePullbackCompIsoOfEq_eq_leftAdjointUniq :
    modulePullbackCompIsoOfEq B S hS φ f h =
      Adjunction.leftAdjointUniq (((etaleModuleAdjunction f).comp
          (etaleModuleAdjunction φ)).ofNatIsoRight (pushforwardModulesCompAtOfEq φ f g h))
        (etaleModuleAdjunction g) := by
  subst h
  simp only [modulePullbackCompIsoOfEq, pushforwardModulesCompAtOfEq, eqToIso_refl,
    Iso.trans_refl]
  exact modulePullbackCompIso_eq_leftAdjointUniq_etale φ f

end OfEq

section SchemeOfEq

variable {X X' X'' : Scheme.{u}} (f : X'' ⟶ X') (g : X' ⟶ X) (k : X'' ⟶ X) (h : f ≫ g = k)

/-- The composition law of inverse images of modules on schemes, with the composite given
under another name. -/
def schemePullbackCompOfEq :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback k :=
  Scheme.Modules.pullbackComp f g ≪≫ eqToIso (congrArg Scheme.Modules.pullback h)

/-- The composition law of direct images of modules on schemes, with the composite given under
another name. -/
def schemePushforwardCompOfEq :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pushforward g ≅ Scheme.Modules.pushforward k :=
  Scheme.Modules.pushforwardComp f g ≪≫ eqToIso (congrArg Scheme.Modules.pushforward h)

/-- The composition laws of inverse and of direct images of modules on schemes are conjugate,
with the composite given under another name. -/
theorem conjugateEquiv_schemePullbackCompOfEq_inv :
    conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction k) (schemePullbackCompOfEq f g k h).inv =
      (schemePushforwardCompOfEq f g k h).hom := by
  subst h
  simp only [schemePullbackCompOfEq, schemePushforwardCompOfEq, eqToIso_refl, Iso.trans_refl]
  exact Scheme.Modules.conjugateEquiv_pullbackComp_inv f g

end SchemeOfEq

section Comp

variable {T T' T'' : BigFppfOver B S hS} (τ₁ : T'' ⟶ T') (τ₂ : T' ⟶ T) (τ : T'' ⟶ T)
  (hτ : τ₁ ≫ τ₂ = τ)

include hτ in
/-- The morphisms of represented algebraic spaces of a composite of test objects compose. -/
theorem representedSpaceMap_comp_of_eq :
    representedSpaceMap B S hS τ₁ ≫ representedSpaceMap B S hS τ₂ = representedSpaceMap B S hS τ :=
  hτ ▸ ObjectProperty.hom_ext _ (yoneda.map_comp τ₁ τ₂).symm

include hτ in
/-- The morphisms of schemes of a composite of test objects compose. -/
theorem toScheme_map_comp_of_eq :
    (BigFppfOver.toScheme B S hS).map τ₁ ≫ (BigFppfOver.toScheme B S hS).map τ₂ =
      (BigFppfOver.toScheme B S hS).map τ :=
  hτ ▸ ((BigFppfOver.toScheme B S hS).map_comp τ₁ τ₂).symm

/-- **The cocycle law of the identification of sections of a direct image**: along a composite
of test objects it is the identification along the two factors, through the comparisons of
direct images of a composite. -/
theorem zariskiDirectImageNatTrans_comp
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (yonedaSpace B S hS T'')).O)) :
    (zariskiReadingFunctor T).map
        ((pushforwardModulesCompAt B S hS (representedSpaceMap B S hS τ₁)
          (representedSpaceMap B S hS τ₂)).hom.app M) ≫
        (zariskiDirectImageNatTrans (τ₁ ≫ τ₂)).app M =
      (zariskiDirectImageNatTrans τ₂).app ((testToposHom τ₁).pushforwardModules.obj M) ≫
        (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ₂)).map
          ((zariskiDirectImageNatTrans τ₁).app M) ≫
        (Scheme.Modules.pushforwardComp ((BigFppfOver.toScheme B S hS).map τ₁)
          ((BigFppfOver.toScheme B S hS).map τ₂)).hom.app
          ((zariskiReadingFunctor T'').obj M) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun O =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      directImageSelfOpensSection_pushforwardModulesCompAt τ₁ τ₂ O.unop M x))

/-- `AlgebraicGeometry.Space.zariskiDirectImageNatTrans_comp`, as an equation of natural
transformations. -/
theorem zariskiDirectImageNatTrans_whisker_comp :
    Functor.whiskerRight (pushforwardModulesCompAt B S hS (representedSpaceMap B S hS τ₁)
        (representedSpaceMap B S hS τ₂)).hom (zariskiReadingFunctor T) ≫
        zariskiDirectImageNatTrans (τ₁ ≫ τ₂) =
      Functor.whiskerLeft (testToposHom τ₁).pushforwardModules (zariskiDirectImageNatTrans τ₂) ≫
        Functor.whiskerRight (zariskiDirectImageNatTrans τ₁)
          (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ₂)) ≫
        Functor.whiskerLeft (zariskiReadingFunctor T'')
          (Scheme.Modules.pushforwardComp ((BigFppfOver.toScheme B S hS).map τ₁)
            ((BigFppfOver.toScheme B S hS).map τ₂)).hom :=
  NatTrans.ext (funext fun M => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun O =>
    ModuleCat.hom_ext (LinearMap.ext fun x =>
      directImageSelfOpensSection_pushforwardModulesCompAt τ₁ τ₂ O.unop M x)))

/-- `AlgebraicGeometry.Space.zariskiDirectImageNatTrans_comp_of_eq`, as an equation of natural
transformations. -/
theorem zariskiDirectImageNatTrans_whisker_comp_of_eq :
    Functor.whiskerRight (pushforwardModulesCompAtOfEq (representedSpaceMap B S hS τ₁)
        (representedSpaceMap B S hS τ₂) (representedSpaceMap B S hS τ)
        (representedSpaceMap_comp_of_eq τ₁ τ₂ τ hτ)).hom (zariskiReadingFunctor T) ≫
        zariskiDirectImageNatTrans τ =
      Functor.whiskerLeft (testToposHom τ₁).pushforwardModules (zariskiDirectImageNatTrans τ₂) ≫
        Functor.whiskerRight (zariskiDirectImageNatTrans τ₁)
          (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ₂)) ≫
        Functor.whiskerLeft (zariskiReadingFunctor T'')
          (schemePushforwardCompOfEq ((BigFppfOver.toScheme B S hS).map τ₁)
            ((BigFppfOver.toScheme B S hS).map τ₂) ((BigFppfOver.toScheme B S hS).map τ)
            (toScheme_map_comp_of_eq τ₁ τ₂ τ hτ)).hom := by
  subst hτ
  show Functor.whiskerRight (pushforwardModulesCompAtOfEq (representedSpaceMap B S hS τ₁)
        (representedSpaceMap B S hS τ₂)
        (representedSpaceMap B S hS τ₁ ≫ representedSpaceMap B S hS τ₂) rfl).hom
        (zariskiReadingFunctor T) ≫ zariskiDirectImageNatTrans (τ₁ ≫ τ₂) =
      Functor.whiskerLeft (testToposHom τ₁).pushforwardModules (zariskiDirectImageNatTrans τ₂) ≫
        Functor.whiskerRight (zariskiDirectImageNatTrans τ₁)
          (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map τ₂)) ≫
        Functor.whiskerLeft (zariskiReadingFunctor T'')
          (schemePushforwardCompOfEq ((BigFppfOver.toScheme B S hS).map τ₁)
            ((BigFppfOver.toScheme B S hS).map τ₂)
            ((BigFppfOver.toScheme B S hS).map τ₁ ≫ (BigFppfOver.toScheme B S hS).map τ₂) rfl).hom
  simp only [pushforwardModulesCompAtOfEq, schemePushforwardCompOfEq, eqToIso_refl,
    Iso.trans_refl]
  exact zariskiDirectImageNatTrans_whisker_comp τ₁ τ₂

/-- **The cocycle law of the base change of the Zariski reading** (Stacks 0B4I), as an equation
of natural transformations, for a morphism `τ` of test objects given as a composite `τ₁ ≫ τ₂`:
the base-change map along `τ` is the base change along `τ₂` followed by the base change along
`τ₁`, through the composition laws of inverse images of modules on schemes and on algebraic
spaces. -/
theorem zariskiReadingPullbackHom_whisker_comp_of_eq :
    Functor.whiskerLeft (zariskiReadingFunctor T)
        (schemePullbackCompOfEq ((BigFppfOver.toScheme B S hS).map τ₁)
          ((BigFppfOver.toScheme B S hS).map τ₂) ((BigFppfOver.toScheme B S hS).map τ)
          (toScheme_map_comp_of_eq τ₁ τ₂ τ hτ)).inv ≫
        Functor.whiskerRight (zariskiReadingPullbackHom τ₂)
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ₁)) ≫
        Functor.whiskerLeft (modulePullback B S hS (representedSpaceMap B S hS τ₂))
          (zariskiReadingPullbackHom τ₁) ≫
        Functor.whiskerRight (modulePullbackCompIsoOfEq B S hS (representedSpaceMap B S hS τ₁)
          (representedSpaceMap B S hS τ₂)
          (representedSpaceMap_comp_of_eq τ₁ τ₂ τ hτ)).hom (zariskiReadingFunctor T'') =
      zariskiReadingPullbackHom τ :=
  Adjunction.transposeComparisonNatTrans_comp
    (etaleModuleAdjunction (representedSpaceMap B S hS τ₂))
    (etaleModuleAdjunction (representedSpaceMap B S hS τ₁))
    (etaleModuleAdjunction (representedSpaceMap B S hS τ))
    (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map τ₂))
    (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map τ₁))
    (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map τ))
    (zariskiDirectImageNatTrans τ₂) (zariskiDirectImageNatTrans τ₁) (zariskiDirectImageNatTrans τ)
    (modulePullbackCompIsoOfEq B S hS (representedSpaceMap B S hS τ₁)
      (representedSpaceMap B S hS τ₂)
      (representedSpaceMap_comp_of_eq τ₁ τ₂ τ hτ))
    (pushforwardModulesCompAtOfEq (representedSpaceMap B S hS τ₁)
      (representedSpaceMap B S hS τ₂) (representedSpaceMap B S hS τ)
      (representedSpaceMap_comp_of_eq τ₁ τ₂ τ hτ))
    (schemePullbackCompOfEq ((BigFppfOver.toScheme B S hS).map τ₁)
      ((BigFppfOver.toScheme B S hS).map τ₂) ((BigFppfOver.toScheme B S hS).map τ)
      (toScheme_map_comp_of_eq τ₁ τ₂ τ hτ)).inv
    (schemePushforwardCompOfEq ((BigFppfOver.toScheme B S hS).map τ₁)
      ((BigFppfOver.toScheme B S hS).map τ₂) ((BigFppfOver.toScheme B S hS).map τ)
      (toScheme_map_comp_of_eq τ₁ τ₂ τ hτ)).hom
    (modulePullbackCompIsoOfEq_eq_leftAdjointUniq _ _ _ _)
    (conjugateEquiv_schemePullbackCompOfEq_inv _ _ _ _)
    (zariskiDirectImageNatTrans_whisker_comp_of_eq τ₁ τ₂ τ hτ)

/-- **The cocycle law of the base change of the Zariski reading** (Stacks 0B4I), for a
morphism `τ` of test objects given as a composite `τ₁ ≫ τ₂`. -/
theorem zariskiReadingPullbackHom_comp_of_eq
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (schemePullbackCompOfEq ((BigFppfOver.toScheme B S hS).map τ₁)
          ((BigFppfOver.toScheme B S hS).map τ₂) ((BigFppfOver.toScheme B S hS).map τ)
          (toScheme_map_comp_of_eq τ₁ τ₂ τ hτ)).inv.app ((zariskiReadingFunctor T).obj N) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ₁)).map
          ((zariskiReadingPullbackHom τ₂).app N) ≫
        (zariskiReadingPullbackHom τ₁).app
          ((modulePullback B S hS (representedSpaceMap B S hS τ₂)).obj N) ≫
        (zariskiReadingFunctor T'').map ((modulePullbackCompIsoOfEq B S hS
          (representedSpaceMap B S hS τ₁) (representedSpaceMap B S hS τ₂)
          (representedSpaceMap_comp_of_eq τ₁ τ₂ τ hτ)).hom.app N) =
      (zariskiReadingPullbackHom τ).app N := by
  exact congrArg (fun t => t.app N) (zariskiReadingPullbackHom_whisker_comp_of_eq τ₁ τ₂ τ hτ)

/-- **The cocycle law of the base change of the Zariski reading** (Stacks 0B4I): along a
composite `τ₁ ≫ τ₂` of test objects, the base-change map is the base change along `τ₂` followed
by the base change along `τ₁`, through the composition laws `Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Space.modulePullbackCompIso` of inverse images of modules. -/
theorem zariskiReadingPullbackHom_comp
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :
    (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τ₁)
          ((BigFppfOver.toScheme B S hS).map τ₂)).inv.app ((zariskiReadingFunctor T).obj N) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ₁)).map
          ((zariskiReadingPullbackHom τ₂).app N) ≫
        (zariskiReadingPullbackHom τ₁).app
          ((modulePullback B S hS (representedSpaceMap B S hS τ₂)).obj N) ≫
        (zariskiReadingFunctor T'').map ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS τ₁) (representedSpaceMap B S hS τ₂)).hom.app N) =
      (zariskiReadingPullbackHom (τ₁ ≫ τ₂)).app N := by
  have h : (schemePullbackCompOfEq ((BigFppfOver.toScheme B S hS).map τ₁)
          ((BigFppfOver.toScheme B S hS).map τ₂)
          ((BigFppfOver.toScheme B S hS).map τ₁ ≫ (BigFppfOver.toScheme B S hS).map τ₂)
          rfl).inv.app ((zariskiReadingFunctor T).obj N) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map τ₁)).map
          ((zariskiReadingPullbackHom τ₂).app N) ≫
        (zariskiReadingPullbackHom τ₁).app
          ((modulePullback B S hS (representedSpaceMap B S hS τ₂)).obj N) ≫
        (zariskiReadingFunctor T'').map ((modulePullbackCompIsoOfEq B S hS
          (representedSpaceMap B S hS τ₁) (representedSpaceMap B S hS τ₂) rfl).hom.app N) =
      (zariskiReadingPullbackHom (τ₁ ≫ τ₂)).app N :=
    zariskiReadingPullbackHom_comp_of_eq τ₁ τ₂ (τ₁ ≫ τ₂) rfl N
  simp only [schemePullbackCompOfEq, modulePullbackCompIsoOfEq, eqToIso_refl,
    Iso.trans_refl] at h
  exact h

end Comp

end AlgebraicGeometry.Space
