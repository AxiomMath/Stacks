module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.LocallySmallSheafification

/-!
# Restriction of étale sheaves of modules to small étale sites, at any section universe

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. The restriction
`F ↦ x^*F|_{U_ét}` of **Stacks 06WJ** of an étale sheaf of `𝒪_𝒳`-modules to the small étale site
of the scheme below an object `x` is exact, and commutes with sheafification. These facts are
proved in `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LocallyQuasicoherentAbelian.lean`
for modules whose sections live in the universe `u` of the schemes. The higher direct images
along a 1-morphism of algebraic stacks have sections in `u + 1`; this file proves the same facts
for sections in any universe `m` with `UnivLE.{u, m}`, by the same arguments.

The only universe-sensitive inputs are existence statements: sheafification of presheaves of
abelian groups with sections in `m` on the associated étale site of `𝒳` and on a small étale
site. Both sites have slices which are essentially small in `Type u` (**Stacks 06W0** for the
first), hence in `Type m`, and that is all the existence theorems ask for.

## Main results

* `AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology_univLE`: sheafification on the
  associated étale site of `𝒳` with sections in `m`.
* `AlgebraicGeometry.Stack.preservesFiniteLimits_restrictSheafToSmallEtale_univLE` and
  `AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictSheafToSmallEtale_univLE`: the
  restriction to a small étale site preserves finite limits and colimits.
* `AlgebraicGeometry.Stack.isIso_restrictSheafificationComparison_univLE`: restriction commutes
  with sheafification.

## References

* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m r j jv

namespace PresheafOfModules

variable {C : Type*} [Category C] {R R' : Cᵒᵖ ⥤ RingCat.{r}} (α : R ⟶ R')
variable {J : Type j} [Category.{jv} J] [HasColimitsOfShape J AddCommGrpCat.{m}]

/-- Change of scalars along a morphism of presheaves of rings preserves colimits of presheaves
of modules, the universe `m` of the sections being unrelated to the universe `r` of the rings.
After evaluation at an object it is the change of scalars of modules over a ring, which
preserves the colimits computed on underlying abelian groups. This is
`PresheafOfModules.preservesColimitsOfShape_restrictScalars_of_ringUniverse` with the two
universes separated. -/
noncomputable instance (priority := low) preservesColimitsOfShape_restrictScalars_univ :
    PreservesColimitsOfShape J (restrictScalars.{m} α) :=
  ⟨fun {K} => ⟨fun {_} hc => ⟨evaluationJointlyReflectsColimits (K ⋙ restrictScalars.{m} α) _
    fun X => isColimitOfPreserves (ModuleCat.restrictScalars.{m} (α.app X).hom)
      (isColimitOfPreserves (evaluation R' X) hc)⟩⟩⟩

variable {D : Type*} [Category D] (G : C ⥤ D) (T : Dᵒᵖ ⥤ RingCat.{r})

/-- Restriction of presheaves of modules along a functor preserves colimits, at any universe of
the sections: after evaluation it is a reindexing, and colimits of presheaves of modules are
computed objectwise. This is `PresheafOfModules.preservesColimitsOfShape_pushforward₀` with the
two universes separated. -/
noncomputable instance (priority := low) preservesColimitsOfShape_pushforward₀_univ :
    PreservesColimitsOfShape J (pushforward₀.{m} G T) :=
  ⟨fun {K} => ⟨fun {_} hc => ⟨evaluationJointlyReflectsColimits (K ⋙ pushforward₀.{m} G T) _
    fun X => isColimitOfPreserves (evaluation T (G.op.obj X)) hc⟩⟩⟩

end PresheafOfModules

namespace AlgebraicGeometry.SmallEtale

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T)

/-- Presheaves of abelian groups with sections in a universe `m` containing `u` on the small
étale site of a scheme admit a sheafification: the site is essentially small in `Type u`, hence
in `Type m`. -/
instance (priority := low) hasSheafify_addCommGrpCat_univLE [UnivLE.{u, m}] :
    HasSheafify (topology E T hT) AddCommGrpCat.{m} :=
  haveI : EssentiallySmall.{m} (SmallEtale E T hT) :=
    essentiallySmall_trans_univLE (inferInstance : EssentiallySmall.{u} (SmallEtale E T hT))
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{m} _

/-- On the small étale site of a scheme, sheafification of presheaves of abelian groups with
sections in a universe `m` containing `u` inverts exactly the locally bijective maps, by
transport from a small model of the site. -/
instance (priority := low) wEqualsLocallyBijective_addCommGrpCat_univLE [UnivLE.{u, m}] :
    (topology E T hT).WEqualsLocallyBijective AddCommGrpCat.{m} :=
  haveI : EssentiallySmall.{m} (SmallEtale E T hT) :=
    essentiallySmall_trans_univLE (inferInstance : EssentiallySmall.{u} (SmallEtale E T hT))
  haveI : ((equivSmallModel.{m} (SmallEtale E T hT)).inverse.inducedTopology
      (topology E T hT)).WEqualsLocallyBijective AddCommGrpCat.{m} := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall (topology E T hT)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [UnivLE.{u, m}]

/-- Every slice `𝒳/x` is essentially small in any universe `m` containing `u`. -/
private theorem essentiallySmall_over_univLE (hp : p.IsFiberedInGroupoids) :
    ∀ x : 𝒳, EssentiallySmall.{m} (Over x) := fun x =>
  essentiallySmall_trans_univLE (FibredSite.essentiallySmall_over B S hS p hp x)

include hp in
/-- Abelian presheaves on the associated étale site of `𝒳`, with sections in a universe `m`
containing the universe `u` of the schemes, have a sheafification: every slice `𝒳/x` is
essentially small in `Type u` by **Stacks 06W0**, hence in `Type m`. At `m = u` this is
`AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology`. -/
theorem hasSheafify_etaleAssociatedTopology_univLE :
    HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{m} :=
  have := essentiallySmall_over_univLE.{u, v, w, m} B S hS p hp
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall_over _

include hp in
/-- The weak equivalences of the sheafification of abelian presheaves on the associated étale
site of `𝒳`, with sections in a universe `m` containing `u`, are the locally bijective maps. At
`m = u` this is `AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology`. -/
theorem wEqualsLocallyBijective_etaleAssociatedTopology_univLE :
    (associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{m} :=
  have := essentiallySmall_over_univLE.{u, v, w, m} B S hS p hp
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over _

section Shape

variable {J : Type j} [Category.{jv} J] [HasColimitsOfShape J AddCommGrpCat.{m}]

/-- Restriction to the small étale site of the scheme below an object of `𝒳` preserves colimits
of presheaves of modules with sections in `m`: it is restriction along a functor followed by a
change of scalars, and both preserve colimits. This is
`AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictModuleToSmallEtaleFunctor` at section
universe `m`. -/
noncomputable instance preservesColimitsOfShape_restrictModuleToSmallEtaleFunctor_univLE (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    PreservesColimitsOfShape J
      (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x) := by
  have := isEquivalence_overPost B S hS p hp x
  unfold restrictModuleToSmallEtaleFunctor
  infer_instance

end Shape

section Limits

variable (K : Type j) [Category.{jv} K] [HasLimitsOfShape K (Type m)]

/-- Restriction of presheaves of modules to the small étale site preserves limits: it is
restriction along a functor, which is a reindexing after evaluation, followed by a change of
scalars, which changes nothing on sections. -/
instance preservesLimitsOfShape_restrictModuleToSmallEtaleFunctor_univLE (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    PreservesLimitsOfShape K
      (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x) := by
  refine ⟨fun {D} => ⟨fun {c} hc => ?_⟩⟩
  have hsmall : ∀ X, Small.{m} (((D ⋙
      restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x) ⋙
        PresheafOfModules.evaluation _ X) ⋙ forget _).sections := fun X =>
    (Types.hasLimit_iff_small_sections _).mp inferInstance
  have hsmall' : ∀ Y, Small.{m} ((D ⋙ PresheafOfModules.evaluation _ Y) ⋙ forget _).sections :=
    fun Y => (Types.hasLimit_iff_small_sections _).mp inferInstance
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X => ?_⟩
  have := isEquivalence_overPost B S hS p hp x
  let q := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  exact isLimitOfPreserves (ModuleCat.restrictScalars.{m}
    ((localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app X).hom)
      (isLimitOfPreserves (PresheafOfModules.evaluation
        (ringStructureSheafCore B S hS p hp τ hτ).obj (q.op.obj X)) hc)

/-- **The restriction of étale sheaves of modules to a small étale site preserves limits**, which
are computed on underlying presheaves of modules on both sides. -/
instance preservesLimitsOfShape_restrictSheafToSmallEtale_univLE (x : 𝒳)
    [PreservesLimitsOfShape K (SheafOfModules.forget.{m} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B)))] :
    PreservesLimitsOfShape K (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x) := by
  have : PreservesLimitsOfShape K (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x ⋙
      SheafOfModules.forget _) := by
    rw [restrictSheafToSmallEtale_comp_forget]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (SheafOfModules.forget _)

/-- The restriction of étale sheaves of modules to a small étale site is left exact. -/
instance preservesFiniteLimits_restrictSheafToSmallEtale_univLE (x : 𝒳) :
    PreservesFiniteLimits (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x) :=
  ⟨fun _ _ _ => inferInstance⟩

end Limits

section Colimits

variable [HasWeakSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{m}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Sheafification of presheaves of modules on the associated étale site of `𝒳`. -/
noncomputable abbrev etaleSheafificationUnivLE :
    PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj ⥤
      SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)) :=
  PresheafOfModules.sheafification.{m}
    (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)

/-- The sheafification adjunction of the associated étale site of `𝒳`. -/
noncomputable abbrev etaleSheafificationAdjunctionUnivLE :
    etaleSheafificationUnivLE B S hS p hp ⊣ SheafOfModules.forget _ :=
  PresheafOfModules.sheafificationAdjunction.{m}
    (𝟙 (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)

/-- Sheafification of presheaves of modules on the small étale site of the scheme below `x`. -/
noncomputable abbrev smallEtaleSheafificationUnivLE (x : 𝒳) :
    PresheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
      (contains_base B E h S hS p x)).obj ⥤
      SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)) :=
  PresheafOfModules.sheafification.{m}
    (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj)

/-- The sheafification adjunction of the small étale site of the scheme below `x`. -/
noncomputable abbrev smallEtaleSheafificationAdjunctionUnivLE (x : 𝒳) :
    smallEtaleSheafificationUnivLE B E h S hS p x ⊣ SheafOfModules.forget _ :=
  PresheafOfModules.sheafificationAdjunction.{m}
    (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj)

/-- The unit of the sheafification adjunction of the associated étale site of `𝒳`, with its
target written as the underlying presheaf of the sheafification. -/
noncomputable def etaleSheafificationUnitUnivLE
    (M : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    M ⟶ ((etaleSheafificationUnivLE B S hS p hp).obj M).val :=
  (etaleSheafificationAdjunctionUnivLE B S hS p hp).unit.app M

omit [UnivLE.{u, m}] in
/-- The unit of the sheafification adjunction of the associated étale site is natural. -/
theorem etaleSheafificationUnit_naturality_univLE
    {M N : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj} (f : M ⟶ N) :
    f ≫ etaleSheafificationUnitUnivLE B S hS p hp N =
      etaleSheafificationUnitUnivLE B S hS p hp M ≫
        ((etaleSheafificationUnivLE B S hS p hp).map f).val :=
  (etaleSheafificationAdjunctionUnivLE B S hS p hp).unit.naturality f

/-- The component at `M` of `restrictSheafificationComparisonUnivLE`: the transpose of the
restriction of the sheafification unit. -/
noncomputable def restrictSheafificationComparisonAppUnivLE (x : 𝒳)
    (M : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    (smallEtaleSheafificationUnivLE B E h S hS p x).obj
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) x).obj M) ⟶
      (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj
        ((etaleSheafificationUnivLE B S hS p hp).obj M) :=
  ((smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).homEquiv _
      ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj
        ((etaleSheafificationUnivLE B S hS p hp).obj M))).symm
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x).map (etaleSheafificationUnitUnivLE B S hS p hp M))

/-- The component of `restrictSheafificationComparisonUnivLE` is the isomorphism
`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso` of Stacks 06W1. -/
theorem isIso_restrictSheafificationComparisonApp_univLE (x : 𝒳)
    (M : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    IsIso (restrictSheafificationComparisonAppUnivLE B E h S hS p hp x M) := by
  let hx := isEquivalence_overPost B S hS p hp x
  let K := associatedTopology B S hS p (etaleTopology B)
  let J := SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)
  let q := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  obtain ⟨hqc, hqcc⟩ : q.IsContinuous J K ∧ q.IsCocontinuous J K :=
    isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x
  have e : restrictSheafificationComparisonAppUnivLE B E h S hS p hp x M =
      (Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso J K q
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x))
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))
        (localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B)).hom M).hom :=
    Adjunction.homEquiv_counit _ _ _ _
  rw [e]
  exact Iso.isIso_hom _

/-- The comparison between sheafifying and then restricting to the small étale site of the
scheme below `x`, and restricting and then sheafifying: the transpose, across the sheafification
adjunction of the small étale site, of the restriction of the sheafification unit. -/
noncomputable def restrictSheafificationComparisonUnivLE (x : 𝒳) :
    restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) x ⋙ smallEtaleSheafificationUnivLE B E h S hS p x ⟶
      etaleSheafificationUnivLE B S hS p hp ⋙
        restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x where
  app M := restrictSheafificationComparisonAppUnivLE B E h S hS p hp x M
  naturality {M N} f := by
    let G := restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) x
    let adjU := smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x
    let R := restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x
    let L := etaleSheafificationUnivLE B S hS p hp
    let η := etaleSheafificationUnitUnivLE B S hS p hp
    have h₁ := (adjU.homEquiv_naturality_left_symm (Y := R.obj (L.obj N)) (G.map f)
      (G.map (η N))).symm
    have h₂ := (adjU.homEquiv_naturality_right_symm (Y := R.obj (L.obj M))
      (Y' := R.obj (L.obj N)) (G.map (η M)) (R.map (L.map f)))
    have h₃ : G.map f ≫ (G.map (η N) : G.obj N ⟶ (SheafOfModules.forget _).obj (R.obj (L.obj N))) =
        (G.map (η M) : G.obj M ⟶ (SheafOfModules.forget _).obj (R.obj (L.obj M))) ≫
          (SheafOfModules.forget _).map (R.map (L.map f)) :=
      (G.map_comp f (η N)).symm.trans
        ((congrArg G.map (etaleSheafificationUnit_naturality_univLE B S hS p hp f)).trans
          (G.map_comp _ _))
    exact h₁.trans ((congrArg (adjU.homEquiv _ _).symm h₃).trans h₂)

/-- The comparison `restrictSheafificationComparisonUnivLE` is an isomorphism. -/
instance isIso_restrictSheafificationComparison_univLE (x : 𝒳) :
    IsIso (restrictSheafificationComparisonUnivLE B E h S hS p hp x) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (restrictSheafificationComparisonUnivLE B E h S hS p hp x)
    (isIso_restrictSheafificationComparisonApp_univLE B E h S hS p hp x)

end Colimits

/-- **The restriction of étale sheaves of modules to a small étale site preserves colimits.**
Sheafifying and then restricting is restricting and then sheafifying, by
`AlgebraicGeometry.Stack.restrictSheafificationComparison`, and restriction of presheaves of
modules and sheafification both preserve colimits; a diagram of sheaves is the sheafification of
its underlying diagram of presheaves. -/
instance preservesColimitsOfShape_restrictSheafToSmallEtale_univLE (x : 𝒳) (K : Type j)
    [Category.{jv} K] [HasColimitsOfShape K AddCommGrpCat.{m}] :
    PreservesColimitsOfShape K (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x) := by
  have := hasSheafify_etaleAssociatedTopology_univLE.{u, v, w, m} B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology_univLE.{u, v, w, m} B S hS p hp
  have : PreservesColimitsOfShape K
      (etaleSheafificationUnivLE B S hS p hp ⋙
        restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x) :=
    preservesColimitsOfShape_of_natIso
      (asIso (restrictSheafificationComparisonUnivLE B E h S hS p hp x))
  exact (etaleSheafificationAdjunctionUnivLE B S hS p hp).preservesColimitsOfShape_of_comp_reflector
    _ K

/-- The restriction of étale sheaves of modules to a small étale site is right exact. -/
instance preservesFiniteColimits_restrictSheafToSmallEtale_univLE (x : 𝒳) :
    PreservesFiniteColimits (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x) :=
  ⟨fun _ _ _ => inferInstance⟩

end AlgebraicGeometry.Stack

end


