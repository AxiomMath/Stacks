module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomToInjectiveSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveOfKInjectiveSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleLocalizationBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentImageCounterexample
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasicoherentRestrictionAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceInjectives
public import StacksFrontier.CategoryTheory.Functor.KanExtension.PointwiseExistence
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements

/-!
# Restriction of injective modules to a representing algebraic space

Let `𝒳` be an algebraic stack over a scheme `S` representable by an algebraic space `F`.
Restriction of abelian sheaves `𝓕 ↦ 𝓕|_{F_étale}` preserves injectives and K-injective complexes
(Stacks 075L, parts (1) and (2), `AlgebraicGeometry.Space.injective_restrictionAbSheafFunctor_obj`
and `AlgebraicGeometry.Space.isKInjective_restrictionAbSheafFunctor_obj`). Stacks 075L adds that
**the same does not hold for modules**. This file proves that: on every big fppf site, for the
algebraic stack `Spec ℤ` (`AlgebraicGeometry.Stack.specIntStack`), represented by the algebraic
space `h_{Spec ℤ}`, there is an injective `𝒪_𝒳`-module whose restriction
`AlgebraicGeometry.Space.moduleRestriction` to the small étale site is not an injective
`𝒪`-module, and a K-injective complex of `𝒪_𝒳`-modules whose degreewise restriction is not
K-injective.

## The argument

The source's argument (Stacks 0758) is followed. Let `α : 𝒪 ⟶ I` be a monomorphism into an
injective `𝒪_𝒳`-module. Multiplication by `2` on `𝒪|_{F_étale}` is a monomorphism, because
every étale chart `U ⟶ Spec ℤ` is flat, so that `2` is a nonzerodivisor on `Γ(U, 𝒪_U)`
(`AlgebraicGeometry.Space.eq_zero_of_add_self_eq_zero_of_flat`). If `I|_{F_étale}` were
injective, `α|_{F_étale}` would extend along it, so that `α(1) = 2s` for a global section `s` of
`I`. Restricting to the object `Spec 𝔽₂` of `𝒳`, which is *not* an étale chart, gives
`α(1) = 2 s|_{Spec 𝔽₂} = 0` there, while `α` is injective on sections and `1 ≠ 0` in `𝔽₂`.

For complexes, an injective module placed in degree `0` is K-injective, and an object placed in
degree `0` is injective as soon as the complex is K-injective
(`CochainComplex.injective_of_isKInjective_single`, through the vanishing of `Ext¹`).

## Main results

* `AlgebraicGeometry.Space.injective_restrictionAbSheafFunctor_obj_univ` and
  `AlgebraicGeometry.Space.isKInjective_restrictionAbSheafFunctor_obj_univ`: **Stacks 075L**,
  parts (1) and (2), for abelian sheaves in the universe of the schemes, with the size conditions
  of the general statements discharged.
* `AlgebraicGeometry.Space.not_injective_moduleRestriction_obj`: the general mechanism of the
  failure for modules.
* `AlgebraicGeometry.Space.exists_injective_not_injective_moduleRestriction` and
  `AlgebraicGeometry.Space.exists_isKInjective_not_isKInjective_moduleRestriction`: the two
  counterexamples on `Spec ℤ`.
* `AlgebraicGeometry.Space.restriction_modules_not_preserves_injectives`: **Stacks 075L**, the
  failure for modules of both parts.

## References

* [Stacks Project, Tag 075L](https://stacks.math.columbia.edu/tag/075L)
* [Stacks Project, Tag 0758](https://stacks.math.columbia.edu/tag/0758)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.AssociatedModuleNotExact (specInt contains_specInt)

universe v u w

namespace AlgebraicGeometry.Space

/-! ### Two is a nonzerodivisor on a flat scheme over an integral base -/

/-- **On a scheme flat over an integral scheme on which `2 ≠ 0`, a global function `s` with
`s + s = 0` vanishes.** Each germ of `s` is killed by `2` in a stalk that is flat over a domain
in which `2 ≠ 0`. -/
theorem eq_zero_of_add_self_eq_zero_of_flat {Z Y : Scheme.{u}} [IsIntegral Y]
    (h2 : (2 : Γ(Y, ⊤)) ≠ 0) (f : Z ⟶ Y) [Flat f] (s : Γ(Z, ⊤)) (hs : s + s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext Z.sheaf ⊤ s 0 fun x hx => ?_
  change Z.presheaf.germ ⊤ x hx s = Z.presheaf.germ ⊤ x hx 0
  rw [map_zero]
  set g := Z.presheaf.germ ⊤ x hx s
  have hg : g + g = 0 := by
    simp only [g]
    rw [← map_add, hs, map_zero]
  let φ := f.stalkMap x
  have hflat : φ.hom.Flat := Flat.stalkMap f x
  let := φ.hom.toAlgebra
  have : Module.Flat _ _ := hflat
  have h2' : (2 : Y.presheaf.stalk (f x)) ≠ 0 := by
    intro h
    exact h2 (germ_injective_of_isIntegral Y (f x) (U := ⊤) trivial (by
      rw [map_ofNat, map_zero]; exact h))
  have hreg := Module.Flat.isSMulRegular_of_isRegular (M := Z.presheaf.stalk x)
    (IsRegular.of_ne_zero h2')
  apply hreg
  change 2 • g = 2 • 0
  rw [smul_zero, Algebra.smul_def, map_ofNat, two_mul]
  exact hg

/-! ### Parts (1) and (2) with no size hypothesis -/

section Abelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Stacks 075L, part (1), with no size hypothesis.** For abelian sheaves with values in the
universe of the schemes, the sheafifications and Kan extensions that
`AlgebraicGeometry.Space.injective_restrictionAbSheafFunctor_obj` asks for exist: `𝒳` is
essentially small, being equivalent to the scheme charts of `F`, and so is the small étale site
of `F`. So the restriction of an injective abelian sheaf on `𝒳_étale` to `F_étale` is injective,
with no hypothesis beyond the source's. -/
@[stacks 075L "part (1), injective abelian sheaves, with no size hypothesis"]
theorem injective_restrictionAbSheafFunctor_obj_univ (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (I : Sheaf (BigFppfOver.associatedTopology B S hS p .etale) Ab.{u}) [Injective I] :
    Injective ((restrictionAbSheafFunctor.{u} B S hS F p hp e).obj I) := by
  have := essentiallySmall_of_equivalenceOver B S hS F p e
  have := locallySmall_of_equivalenceOver B S hS F p e
  have : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) Ab.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _
  have : HasSheafify (SmallEtale.topology B S hS F) Ab.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _
  have : ∀ G : (SmallEtale B S hS F)ᵒᵖ ⥤ Ab.{u},
      (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension G := fun G =>
    Functor.hasPointwiseLeftKanExtension_of_essentiallySmall_of_locallySmall.{u} _ _
  exact injective_restrictionAbSheafFunctor_obj B S hS F p hp e I

/-- **Stacks 075L, part (2), with no size hypothesis.** The degreewise restriction of a
K-injective complex of abelian sheaves on `𝒳_étale` to `F_étale` is K-injective, for sheaves with
values in the universe of the schemes. The abelian structures on the two categories of sheaves
are the ones given by sheafification, which exists on both sites because both are essentially
small (`AlgebraicGeometry.Space.essentiallySmall_of_equivalenceOver` for `𝒳`); the statement
introduces it from the presentation `e`. -/
@[stacks 075L "part (2), K-injective complexes, with no size hypothesis"]
theorem isKInjective_restrictionAbSheafFunctor_obj_univ (hp : p.IsFiberedInGroupoids)
    (e : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    letI := essentiallySmall_of_equivalenceOver B S hS F p e
    letI : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) Ab.{u} :=
      GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _
    letI : HasSheafify (SmallEtale.topology B S hS F) Ab.{u} :=
      GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _
    ∀ (I : CochainComplex
      (Sheaf (BigFppfOver.associatedTopology B S hS p .etale) Ab.{u}) ℤ) [I.IsKInjective],
    CochainComplex.IsKInjective
      (((restrictionAbSheafFunctor.{u} B S hS F p hp e).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  intro I _
  let := essentiallySmall_of_equivalenceOver B S hS F p e
  let : HasSheafify (BigFppfOver.associatedTopology B S hS p .etale) Ab.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _
  let : HasSheafify (SmallEtale.topology B S hS F) Ab.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _
  have := locallySmall_of_equivalenceOver B S hS F p e
  have : ∀ G : (SmallEtale B S hS F)ᵒᵖ ⥤ Ab.{u},
      (restrictionFunctor B S hS F p e).op.HasPointwiseLeftKanExtension G := fun G =>
    Functor.hasPointwiseLeftKanExtension_of_essentiallySmall_of_locallySmall.{u} _ _
  exact isKInjective_restrictionAbSheafFunctor_obj B S hS F p hp e I

end Abelian

/-! ### The general mechanism -/

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (e : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (X.1 ⋙ typeToCat)).p)

/-- Restriction of modules to the small étale site of the representing space is additive: on
sections it is evaluation at the image of a chart. -/
instance additive_moduleRestriction : (moduleRestriction B S hS X p hp e).Additive where
  map_add := rfl

/-- **A module containing `𝒪_𝒳` whose restriction is not injective.** Suppose that `2` is a
nonzerodivisor on the functions of every étale chart of `X`, and that some object `y` of `𝒳`
mapping to the image of a chart has a nonzero ring of functions in which `2 = 0`. Then for every
monomorphism `α : 𝒪_𝒳 ⟶ I`, the restriction `I|_{X_étale}` is not an injective `𝒪_X`-module. -/
theorem not_injective_moduleRestriction_obj
    (I : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .etale))
    (α : SheafOfModules.unit (FibredSite.ringStructureSheafCore B S hS p hp .etale) ⟶ I)
    [Mono α]
    (c₀ : SmallEtale B S hS X.1) (y : 𝒳) (g : y ⟶ (restrictionFunctor B S hS X.1 p e).obj c₀)
    (h2 : (2 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj y), ⊤)) = 0)
    (h1 : (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj y), ⊤)) ≠ 0)
    (hreg : ∀ (c : SmallEtale B S hS X.1)
      (s : Γ((BigFppfOver.toScheme B S hS).obj
        (p.obj ((restrictionFunctor B S hS X.1 p e).obj c)), ⊤)), s + s = 0 → s = 0) :
    ¬ Injective ((moduleRestriction B S hS X p hp e).obj I) := by
  intro hJ
  let M := moduleRestriction B S hS X p hp e
  let N := M.obj (SheafOfModules.unit (FibredSite.ringStructureSheafCore B S hS p hp .etale))
  let t : N ⟶ N := 𝟙 _ + 𝟙 _
  have ht : Mono t := by
    have : Mono ((SheafOfModules.forget _).map t) := by
      refine PresheafOfModules.mono_of_injective fun U s₁ s₂ h => ?_
      have h' : (s₁ - s₂) + (s₁ - s₂) = 0 := by
        have : s₁ + s₁ = s₂ + s₂ := h
        rw [sub_add_sub_comm, this, sub_self]
      exact sub_eq_zero.1 (hreg U.unop (s₁ - s₂) h')
    exact (SheafOfModules.forget _).mono_of_mono_map this
  let β := Injective.factorThru (M.map α) t
  have hβ : t ≫ β = M.map α := Injective.comp_factorThru _ _
  let x₀ := (restrictionFunctor B S hS X.1 p e).obj c₀
  let s : I.val.obj (op x₀) := β.val.app (op c₀) (1 : Γ((BigFppfOver.toScheme B S hS).obj
    (p.obj x₀), ⊤))
  have h3 : β.val.app (op c₀) (t.val.app (op c₀) (1 : Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj x₀), ⊤))) = α.val.app (op x₀) (1 : Γ((BigFppfOver.toScheme B S hS).obj
      (p.obj x₀), ⊤)) :=
    congrArg (fun φ : N ⟶ M.obj I => φ.val.app (op c₀)
      (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj x₀), ⊤))) hβ
  have key : α.val.app (op x₀) (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj x₀), ⊤)) =
      s + s := by
    rw [← h3]
    exact map_add _ _ _
  have hy : α.val.app (op y) (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj y), ⊤)) =
      α.val.app (op y) 0 := by
    have nat := PresheafOfModules.naturality_apply α.val g.op
      (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj x₀), ⊤))
    have h1' : (SheafOfModules.unit
        (FibredSite.ringStructureSheafCore B S hS p hp .etale)).val.map g.op
        (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj x₀), ⊤)) =
        (1 : Γ((BigFppfOver.toScheme B S hS).obj (p.obj y), ⊤)) :=
      map_one ((FibredSite.ringStructureSheafCore B S hS p hp .etale).obj.map g.op).hom
    have h2' : (2 : (FibredSite.ringStructureSheafCore B S hS p hp .etale).obj.obj (op y)) = 0 :=
      h2
    have hm : ∀ m : I.val.obj (op y), m + m = 0 := fun m => by
      rw [← two_smul ((FibredSite.ringStructureSheafCore B S hS p hp .etale).obj.obj (op y)) m,
        h2', zero_smul]
    rw [h1', key, map_add] at nat
    rw [nat, map_zero]
    exact hm _
  exact h1 (PresheafOfModules.injective_of_mono ((SheafOfModules.forget _).map α) (op y) hy)

end General

/-! ### The counterexample on `Spec ℤ` -/

section SpecInt

variable (B : BigFppfSite.{u})

/-- The algebraic space `h_{Spec ℤ}` over `Spec ℤ`, represented by the final object of the big
fppf site of `Spec ℤ`. -/
noncomputable abbrev specIntSpace : AlgebraicSpaces B specInt.{u} (contains_specInt B) :=
  ⟨yoneda.obj (Stack.specIntOver B), isAlgebraicSpace_yoneda B _ _ _⟩

/-- The algebraic stack `Spec ℤ` (`AlgebraicGeometry.Stack.specIntStack`) is represented by the
algebraic space `h_{Spec ℤ}`: its category is the slice over the final object, which is the
category of elements of the represented presheaf. -/
noncomputable abbrev specIntStackEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (Stack.specIntStack.{u, u} B).val.val.p
      (presheafOfCategories ((specIntSpace B).1 ⋙ typeToCat)).p :=
  PresheafOfCategories.sliceElementsEquivalenceOver (Stack.specIntOver B)

/-- The structure sheaf of the étale site of the algebraic stack `Spec ℤ`. -/
noncomputable abbrev specIntEtaleRingSheaf :=
  FibredSite.ringStructureSheafCore B specInt.{u} (contains_specInt B)
    (Stack.specIntStack.{u, u} B).val.val.p (Stack.specIntStack.{u, u} B).val.isFiberedInGroupoids
    .etale

/-- The restriction `𝓕 ↦ 𝓕|_{F_étale}` of `𝒪`-modules from the étale site of the algebraic stack
`Spec ℤ` to the small étale site of the algebraic space `F = h_{Spec ℤ}` representing it. -/
noncomputable abbrev specIntModuleRestriction :=
  moduleRestriction B specInt.{u} (contains_specInt B) (specIntSpace B)
    (Stack.specIntStack.{u, u} B).val.val.p (Stack.specIntStack.{u, u} B).val.isFiberedInGroupoids
    (specIntStackEquivalenceOver B)

/-- The restriction of modules from the algebraic stack `Spec ℤ` is additive. -/
instance additive_specIntModuleRestriction : (specIntModuleRestriction B).Additive :=
  additive_moduleRestriction B specInt.{u} (contains_specInt B) (specIntSpace B)
    (Stack.specIntStack.{u, u} B).val.val.p (Stack.specIntStack.{u, u} B).val.isFiberedInGroupoids
    (specIntStackEquivalenceOver B)

/-- The restriction of modules from the algebraic stack `Spec ℤ` preserves zero morphisms. -/
instance preservesZeroMorphisms_specIntModuleRestriction :
    (specIntModuleRestriction B).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- On an étale chart of `h_{Spec ℤ}`, `2` is a nonzerodivisor on the global functions: the chart
is an étale, hence flat, scheme over `Spec ℤ`. -/
theorem eq_zero_of_add_self_eq_zero_specIntChart
    (c : SmallEtale B specInt.{u} (contains_specInt B) (specIntSpace B).1)
    (s : Γ((BigFppfOver.toScheme B specInt.{u} (contains_specInt B)).obj c.obj.left, ⊤))
    (hs : s + s = 0) : s = 0 := by
  have h : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B specInt.{u} (contains_specInt B))).presheaf c.obj.hom :=
    c.property
  rw [← yoneda.map_preimage c.obj.hom] at h
  have het := (presheaf_yoneda_map_etale_iff B _ _ _).1 h
  have : Flat ((BigFppfOver.toScheme B specInt.{u} (contains_specInt B)).map
      (yoneda.preimage c.obj.hom)) := (Etale.iff_flat_and_formallyUnramified.1 het).1
  exact eq_zero_of_add_self_eq_zero_of_flat AssociatedModuleNotExact.two_ne_zero_gammaTop
    ((BigFppfOver.toScheme B specInt.{u} (contains_specInt B)).map (yoneda.preimage c.obj.hom))
    s hs

/-- Sheaves of `𝒪`-modules on the étale site of the algebraic stack `Spec ℤ` have enough
injectives, the stack being essentially small. -/
theorem enoughInjectives_specIntEtaleModules :
    EnoughInjectives (SheafOfModules.{u} (specIntEtaleRingSheaf B)) := by
  have : HasSheafify (BigFppfOver.associatedTopology B specInt.{u} (contains_specInt B)
      (Stack.specIntStack.{u, u} B).val.val.p .etale) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u} _
  have : (BigFppfOver.associatedTopology B specInt.{u} (contains_specInt B)
      (Stack.specIntStack.{u, u} B).val.val.p .etale).WEqualsLocallyBijective
        AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (specIntEtaleRingSheaf B)) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall.{u} _
  infer_instance

/-- **An injective `𝒪`-module on the algebraic stack `Spec ℤ` whose restriction to the small
étale site of the representing algebraic space is not injective.** -/
theorem exists_injective_not_injective_moduleRestriction :
    ∃ I : SheafOfModules.{u} (specIntEtaleRingSheaf B),
      Injective I ∧ ¬ Injective ((specIntModuleRestriction B).obj I) := by
  have := enoughInjectives_specIntEtaleModules B
  let O := SheafOfModules.unit (specIntEtaleRingSheaf B)
  refine ⟨Injective.under O, inferInstance, ?_⟩
  obtain ⟨h2, h1, -, -⟩ := Stack.specInt_sideConditions B
  exact not_injective_moduleRestriction_obj B specInt.{u} (contains_specInt B) (specIntSpace B)
    (Stack.specIntStack.{u, u} B).val.val.p (Stack.specIntStack.{u, u} B).val.isFiberedInGroupoids
    (specIntStackEquivalenceOver B) (Injective.under O) (Injective.ι O)
    ⟨CostructuredArrow.mk (𝟙 (yoneda.obj (Stack.specIntOver B))),
      isEtaleChart_id B _ _ (Stack.specIntOver B)⟩
    (Stack.specFTwoPt B) (Stack.specFTwoToTop B) h2 h1
    (fun c s hs => eq_zero_of_add_self_eq_zero_specIntChart B c s hs)

/-- **A K-injective complex of `𝒪`-modules on the algebraic stack `Spec ℤ` whose degreewise
restriction to the small étale site of the representing algebraic space is not K-injective.** It
is an injective module placed in degree `0`. -/
theorem exists_isKInjective_not_isKInjective_moduleRestriction :
    ∃ I : CochainComplex (SheafOfModules.{u} (specIntEtaleRingSheaf B)) ℤ,
      I.IsKInjective ∧ ¬ CochainComplex.IsKInjective
        (((specIntModuleRestriction B).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  obtain ⟨I, hI, hnot⟩ := exists_injective_not_injective_moduleRestriction B
  refine ⟨(CochainComplex.singleFunctor _ 0).obj I,
    CochainComplex.isKInjective_single_obj_of_injective I 0, fun h => hnot ?_⟩
  have e := (HomologicalComplex.singleMapHomologicalComplex (specIntModuleRestriction B)
    (ComplexShape.up ℤ) 0).app I
  have : ((CochainComplex.singleFunctor _ 0).obj
      ((specIntModuleRestriction B).obj I)).IsKInjective :=
    (CochainComplex.isKInjective_iff_of_iso e).1 h
  exact CochainComplex.injective_of_isKInjective_single _

end SpecInt

/-- **Stacks 075L, the failure for modules.** Restriction of abelian sheaves from an algebraic
stack representable by an algebraic space `F` to `F_étale` preserves injectives and K-injective
complexes (parts (1) and (2), `AlgebraicGeometry.Space.injective_restrictionAbSheafFunctor_obj`
and `AlgebraicGeometry.Space.isKInjective_restrictionAbSheafFunctor_obj`), but **the same does
not hold for modules**: on every big fppf site, the algebraic stack `Spec ℤ`, represented by the
algebraic space `h_{Spec ℤ}`, carries an injective `𝒪`-module `I` with `I|_{F_étale}` not an
injective `𝒪_F`-module, and a K-injective complex of `𝒪`-modules whose restriction is not
K-injective. -/
@[stacks 075L "the final sentence: the same does not hold for modules, for neither part"]
theorem restriction_modules_not_preserves_injectives (B : BigFppfSite.{u}) :
    (∃ I : SheafOfModules.{u} (specIntEtaleRingSheaf B),
      Injective I ∧ ¬ Injective ((specIntModuleRestriction B).obj I)) ∧
    ∃ I : CochainComplex (SheafOfModules.{u} (specIntEtaleRingSheaf B)) ℤ,
      I.IsKInjective ∧ ¬ CochainComplex.IsKInjective
        (((specIntModuleRestriction B).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  ⟨exists_injective_not_injective_moduleRestriction B,
    exists_isKInjective_not_isKInjective_moduleRestriction B⟩

end AlgebraicGeometry.Space

end
