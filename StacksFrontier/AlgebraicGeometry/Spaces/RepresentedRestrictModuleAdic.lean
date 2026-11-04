module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartRestrictionQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedCoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.RelativeSerreVanishing.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Restriction to the representing scheme, adic quotients and completion

Let `U` be an object of the big fppf site over `S` with underlying scheme `T`.  This file
constructs the restriction of modules **from the algebraic space `yoneda.obj U` to the scheme
`T`**, and shows that it carries coherent adic systems and completions on the space to coherent
adic systems and completions on the scheme.

The functor is `AlgebraicGeometry.Space.representedRestrictModule`, the composite of the inverse
of the identification of the two small étale sites with the restriction
`AlgebraicGeometry.SmallEtale.restrictModule` to the small Zariski site of `T`.  It is the right
adjoint of the transport `AlgebraicGeometry.Space.representedAssociate` of Descent,
Proposition 03DX (2), with unit and counit isomorphisms on the quasi-coherent modules, and its
sections over a Zariski open `O` of `T` are, on the nose, the sections of the module over the
chart `AlgebraicGeometry.Space.selfOpensFunctor` attaches to `O`.  In particular, over an affine
open both `(M|_T) / Ī ^ k (M|_T)` and `(M / 𝓘 ^ k M)|_T` are `M(V) / 𝓘(V) ^ k M(V)`.

The sheaf of ideals `Ī` on `T` is a parameter, tied to the sheaf of ideals `𝓘` on `yoneda.obj U` by
the single hypothesis `hIbar`: over every affine open `O` of `T`, `Ī(O)` generates `𝓘` on the
chart `O` cuts out, across the scalar isomorphism `AlgebraicGeometry.Space.selfOpensRingHom`.

## Main definitions

* `AlgebraicGeometry.Space.representedRestrictModule`: restriction `Modules(yoneda.obj U) ⥤
  T.Modules`, and `AlgebraicGeometry.Space.representedAssociateAdjunction` its adjunction with
  the associated module.
* `AlgebraicGeometry.Space.representedRestrictModuleQuotientHom`: the comparison
  `(M|_T) / Ī ^ k (M|_T) ⟶ (M / 𝓘 ^ k M)|_T`.
* `AlgebraicGeometry.Space.representedRestrictCoherent`: restriction on coherent modules,
  `Coh(yoneda.obj U) ⥤ Coh(𝒪_T)`, an equivalence for `T` locally Noetherian.
* `AlgebraicGeometry.Space.representedRestrictAdic`: termwise restriction of coherent adic
  systems, `Coh(yoneda.obj U, 𝓘) ⥤ Coh(T, Ī)`, fully faithful
  (`AlgebraicGeometry.Space.fullyFaithfulRepresentedRestrictAdic`).
* `AlgebraicGeometry.Space.representedRestrictCompletionIso`: **restriction commutes with
  completion**, `representedRestrictCoherent ⋙ completionFunctor T Ī ≅
  completionFunctor (yoneda.obj U) 𝓘 ⋙ representedRestrictAdic` (Stacks 0880 against Stacks 08B4).

## Main results

* `AlgebraicGeometry.Space.isIso_representedRestrictModuleQuotientHom`: the restriction of
  `M / 𝓘 ^ k M` is `(M|_T) / Ī ^ k (M|_T)` for quasi-coherent `M`.
* `AlgebraicGeometry.Space.fullyFaithfulRepresentedRestrictModuleQcoh`: restriction is fully
  faithful on the quasi-coherent modules.
* `AlgebraicGeometry.Space.isCoherentAdicSystem_comp_representedRestrictModule`: the termwise
  restriction of a coherent `𝓘`-adic system is a coherent `Ī`-adic system.
* `AlgebraicGeometry.Space.fullyFaithfulCompletionFunctorOfScheme`,
  `AlgebraicGeometry.Space.essSurj_completionFunctor_of_scheme` and
  `AlgebraicGeometry.Space.isEquivalence_completionFunctor_of_scheme`: **full faithfulness,
  essential surjectivity and the equivalence of the completion functor transfer from `T` to
  `yoneda.obj U`.**  With the scheme theorems Stacks 0883, 0885 and 088C these give Grothendieck
  existence for the algebraic space a proper (projective) scheme represents.

Two general lemmas of category theory are proved on the way, in `Stacks.CategoryTheory`:
`Stacks.CategoryTheory.fullyFaithfulιCompOfIsIsoCounit` (a right adjoint is fully faithful on the
objects where the counit is an isomorphism) and `Stacks.CategoryTheory.natTransPreimage` (natural
transformations lift along a functor fully faithful on a full subcategory).

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace Stacks.CategoryTheory

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}

/-- **A right adjoint is fully faithful on the objects at which the counit is an isomorphism.**
For an adjunction `L ⊣ R` and a full subcategory `P` of the target of `L` on whose objects the
counit is an isomorphism, the restriction of `R` to `P` is fully faithful: the preimage of
`f : R X ⟶ R Y` is `ε_X⁻¹ ≫ L f ≫ ε_Y`. -/
noncomputable def fullyFaithfulιCompOfIsIsoCounit (adj : L ⊣ R) (P : ObjectProperty D)
    (h : ∀ X, P X → IsIso (adj.counit.app X)) : (P.ι ⋙ R).FullyFaithful where
  preimage {X Y} f :=
    haveI := h X.obj X.property
    ObjectProperty.homMk (inv (adj.counit.app X.obj) ≫ L.map f ≫ adj.counit.app Y.obj)
  map_preimage {X Y} f := by
    have := h X.obj X.property
    simp only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom,
      Functor.map_comp, Functor.map_inv]
    have e : inv (R.map (adj.counit.app X.obj)) = adj.unit.app (R.obj X.obj) :=
      IsIso.inv_eq_of_inv_hom_id (adj.right_triangle_components X.obj)
    rw [e]
    exact (adj.unit_naturality_assoc (X := R.obj X.obj) (Y := R.obj Y.obj) f _).trans
      ((congrArg (f ≫ ·) (adj.right_triangle_components Y.obj)).trans (Category.comp_id f))
  preimage_map {X Y} g := by
    have := h X.obj X.property
    ext
    simp

section NatTransPreimage

variable {J : Type*} [Category J] {P : ObjectProperty D} {F : D ⥤ C}
  (hF : (P.ι ⋙ F).FullyFaithful)

/-- **Natural transformations lift along a functor fully faithful on a full subcategory.**  For
`F` fully faithful on `P` and two diagrams `X`, `Y` with values in `P`, a natural transformation
`X ⋙ F ⟶ Y ⋙ F` is the image of a unique `X ⟶ Y`, which this is. -/
def natTransPreimage {X Y : J ⥤ D} (hX : ∀ j, P (X.obj j)) (hY : ∀ j, P (Y.obj j))
    (τ : X ⋙ F ⟶ Y ⋙ F) : X ⟶ Y where
  app j := (hF.preimage (X := ⟨X.obj j, hX j⟩) (Y := ⟨Y.obj j, hY j⟩) (τ.app j)).hom
  naturality {i j} g := by
    have h := hF.map_injective (X := ⟨X.obj i, hX i⟩) (Y := ⟨Y.obj j, hY j⟩)
      (f := ObjectProperty.homMk (X.map g) ≫
        hF.preimage (X := ⟨X.obj j, hX j⟩) (Y := ⟨Y.obj j, hY j⟩) (τ.app j))
      (g := hF.preimage (X := ⟨X.obj i, hX i⟩) (Y := ⟨Y.obj i, hY i⟩) (τ.app i) ≫
        ObjectProperty.homMk (Y.map g)) (by
          simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]
          exact τ.naturality g)
    exact congrArg (fun k => k.hom) h

/-- `natTransPreimage` is a preimage. -/
theorem whiskerRight_natTransPreimage {X Y : J ⥤ D} (hX : ∀ j, P (X.obj j))
    (hY : ∀ j, P (Y.obj j)) (τ : X ⋙ F ⟶ Y ⋙ F) :
    Functor.whiskerRight (natTransPreimage hF hX hY τ) F = τ := by
  ext j
  exact hF.map_preimage (X := ⟨X.obj j, hX j⟩) (Y := ⟨Y.obj j, hY j⟩) (τ.app j)

/-- `natTransPreimage` is the only preimage. -/
theorem natTransPreimage_whiskerRight {X Y : J ⥤ D} (hX : ∀ j, P (X.obj j))
    (hY : ∀ j, P (Y.obj j)) (σ : X ⟶ Y) :
    natTransPreimage hF hX hY (Functor.whiskerRight σ F) = σ := by
  ext j
  exact congrArg (fun k => k.hom) (hF.preimage_map (X := ⟨X.obj j, hX j⟩) (Y := ⟨Y.obj j, hY j⟩)
    (ObjectProperty.homMk (σ.app j)))

end NatTransPreimage

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **Restriction of an `𝒪`-module on `yoneda.obj U` to the scheme `T` underlying `U`**: read the
module on the small étale site of `T` and restrict it along the inclusion of the small Zariski
site, `AlgebraicGeometry.SmallEtale.restrictModule`.  Its sections over a Zariski open `O` of `T`
are, on the nose, the sections of the module over the étale chart
`AlgebraicGeometry.Space.selfOpensFunctor` attaches to `O`.  It is the right adjoint of the
transport `AlgebraicGeometry.Space.representedAssociate` of Descent, Proposition 03DX (2)
(`AlgebraicGeometry.Space.representedAssociateAdjunction`). -/
noncomputable abbrev representedRestrictModule :
    Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      ((BigFppfOver.toScheme B S hS).obj U).Modules :=
  (representedSmallEtaleModuleEquivalence B S hS U).inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property

/-- The ring map `Γ(T, O) → 𝒪(selfOpensFunctor O)` along which
`AlgebraicGeometry.Space.representedRestrictModule` restricts scalars over a Zariski open `O`. -/
noncomputable def selfOpensRingHom (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    Γ((BigFppfOver.toScheme B S hS).obj U, O) →+*
      chartRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        ((selfOpensFunctor B S hS U).obj O) :=
  ((selfOpensStructureMap B S hS U).hom.app (op O)).hom

/-- The scalar map of the restriction over a Zariski open is an isomorphism of rings. -/
theorem bijective_selfOpensRingHom (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    Function.Bijective (selfOpensRingHom B S hS U O) :=
  (Stacks.SheafOfModules.bijective_reindexBackSharp_app
      (J' := SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U) (representedSchemeStructureSheaf B S hS U)
      _).comp
    (_root_.AlgebraicGeometry.SmallEtale.bijective_structureMap_hom_app
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property O)

/-- The scalar map of the restriction over a Zariski open, unfolded: the comparison
`Scheme.Opens.topIso` followed by the structure sheaf of the small étale site along a counit of
the identification of the two small étale sites. -/
theorem selfOpensRingHom_eq (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    selfOpensRingHom B S hS U O =
      ((representedSchemeStructureSheaf B S hS U).obj.map
          ((representedSmallEtaleEquivalence B S hS U).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property O)).op).hom.comp
        ((CategoryTheory.forget₂ CommRingCat RingCat.{u}).map (Scheme.Opens.topIso O).inv).hom :=
  rfl

/-- **The scalar map of the restriction over a Zariski open `O` is `Γ(T, O) ≅ Γ(O, ⊤)`**, the
inverse of `AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem selfOpensRingHom_eq_topIso (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    selfOpensRingHom B S hS U O = (Scheme.Opens.topIso O).inv.hom := by
  have h1 : (representedSmallEtaleEquivalence B S hS U).counit.app
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property O) = 𝟙 _ :=
    @Subsingleton.elim _ (_root_.AlgebraicGeometry.SmallEtale.subsingleton_hom_opensToSmallEtale
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
      U.left.property _ O) _ _
  rw [selfOpensRingHom_eq]
  simp only [h1]
  rfl

section Quotient

variable (𝓘 : (SheafOfModules.unit.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).O))).Submodule)
    (M : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (Ibar : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData)
    (hIbar : ∀ O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      Ideal.map (selfOpensRingHom B S hS U O.1) (Ibar.ideal O) =
        chartSectionIdeal B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
          ((selfOpensFunctor B S hS U).obj O.1))
    (k : ℕ)

include hIbar in
/-- If `𝓘 ^ k` annihilates a module `N` on `yoneda.obj U`, then `Ī ^ k` annihilates the sections
of its restriction over every affine open of `T`, `Ī` generating `𝓘` on the charts the affine opens
cut out (`hIbar`). -/
theorem pow_smul_top_representedRestrictModule_eq_bot
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : IsPowAnnihilated B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 k N)
    (O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    Ibar.ideal O ^ k • (⊤ : Submodule Γ((BigFppfOver.toScheme B S hS).obj U, O.1)
      Γ((representedRestrictModule B S hS U).obj N, O.1)) = ⊥ := by
  refine eq_bot_iff.mpr (Submodule.smul_le.mpr fun r hr y _ => ?_)
  have hr' : selfOpensRingHom B S hS U O.1 r ∈
      Ideal.map (selfOpensRingHom B S hS U O.1) (Ibar.ideal O ^ k) :=
    Ideal.mem_map_of_mem _ hr
  rw [Ideal.map_pow, hIbar O] at hr'
  rw [Submodule.mem_bot]
  exact hN ((selfOpensFunctor B S hS U).obj O.1) _ hr' y

include hIbar in
/-- **The restriction of `M / 𝓘 ^ k M` is annihilated by `Ī ^ k` over every affine open.** -/
theorem pow_smul_top_representedRestrictModule_idealPowerQuotient_eq_bot
    (O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    Ibar.ideal O ^ k • (⊤ : Submodule Γ((BigFppfOver.toScheme B S hS).obj U, O.1)
      Γ((representedRestrictModule B S hS U).obj
        (idealPowerQuotient B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 k M),
        O.1)) = ⊥ :=
  pow_smul_top_representedRestrictModule_eq_bot B S hS U 𝓘 Ibar hIbar k _
    (isPowAnnihilated_idealPowerQuotient B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      𝓘 k M) O

include hIbar in
/-- **Annihilation by `𝓘 ^ k` restricts to annihilation by `Ī ^ k`**: if `𝓘 ^ k N = 0`, then
`Ī ^ k (N|_T) = 0`. -/
theorem idealPowerMultiple_representedRestrictModule_eq_bot
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : idealPowerMultiple B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 k N = ⊥) :
    Stacks.Algebraization.idealPowerMultiple Ibar k ((representedRestrictModule B S hS U).obj N) =
      ⊥ :=
  (Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_smul_top _ _ _).2 fun O =>
    pow_smul_top_representedRestrictModule_eq_bot B S hS U 𝓘 Ibar hIbar k N
      ((idealPowerMultiple_eq_bot_iff B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
        k N).1 hN) O

/-- The zero morphism out of the sheaf of modules underlying a subsheaf on a scheme. -/
noncomputable local instance zeroHomOfSchemeSheafOfModules' {Y : Scheme.{u}}
    (A : SheafOfModules.{u} Y.ringCatSheaf) (N : Y.Modules) : Zero (A ⟶ N) :=
  HasZeroMorphisms.zero (C := Y.Modules) A N

include hIbar in
/-- `Ī ^ k`-power multiples of the restriction of `M` die in the restriction of `M / 𝓘 ^ k M`. -/
theorem idealPowerMultiple_ι_comp_representedRestrictModule_map_π :
    (Stacks.Algebraization.idealPowerMultiple Ibar k
        ((representedRestrictModule B S hS U).obj M)).ι ≫
      (representedRestrictModule B S hS U).map
        (cokernel.π (idealPowerMultiple B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          𝓘 k M).ι) = 0 :=
  ι_comp_eq_zero_of_le_kernelSubmodule _ _
    (Stacks.Coherent.idealPowerMultiple_le_kernelSubmodule Ibar k _ fun O =>
      pow_smul_top_representedRestrictModule_idealPowerQuotient_eq_bot B S hS U 𝓘 M Ibar hIbar k O)

/-- **The comparison of the two quotients**: `(M|_T) / Ī ^ k (M|_T) ⟶ (M / 𝓘 ^ k M)|_T`. -/
noncomputable def representedRestrictModuleQuotientHom :
    Stacks.Algebraization.idealPowerQuotient Ibar k ((representedRestrictModule B S hS U).obj M) ⟶
      (representedRestrictModule B S hS U).obj
        (idealPowerQuotient B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 k M) :=
  cokernel.desc _ _
    (idealPowerMultiple_ι_comp_representedRestrictModule_map_π B S hS U 𝓘 M Ibar hIbar k)

/-- The comparison of the quotients is compatible with the two projections. -/
theorem π_comp_representedRestrictModuleQuotientHom :
    cokernel.π (Stacks.Algebraization.idealPowerMultiple Ibar k
        ((representedRestrictModule B S hS U).obj M)).ι ≫
      representedRestrictModuleQuotientHom B S hS U 𝓘 M Ibar hIbar k =
      (representedRestrictModule B S hS U).map
        (cokernel.π (idealPowerMultiple B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          𝓘 k M).ι) :=
  cokernel.π_desc _ _ _

include hIbar in
/-- Over an affine open the comparison of the quotients is injective: both sides are
`M(V) / 𝓘(V) ^ k M(V)` for the affine chart `V` the open cuts out. -/
theorem injective_representedRestrictModuleQuotientHom_app
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules) (hM : M.IsQuasicoherentOnSite)
    (O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    Function.Injective
      ((representedRestrictModuleQuotientHom B S hS U 𝓘 M Ibar hIbar k).val.app (op O.1)) := by
  have hMc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) M hM
  have : ((representedRestrictModule B S hS U).obj M).IsQuasicoherent :=
    isQuasicoherent_restrictModule_representedSmallEtaleModuleInverse M hM
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  obtain ⟨x, rfl⟩ := @Stacks.Algebraization.surjective_app_of_epi_of_isAffineOpen _ _ _
    inferInstance (Stacks.Algebraization.isQuasicoherent_idealPowerQuotient Ibar k _)
    (cokernel.π (C := ((BigFppfOver.toScheme B S hS).obj U).Modules)
      (Stacks.Algebraization.idealPowerMultiple Ibar k
        ((representedRestrictModule B S hS U).obj M)).ι) inferInstance O z
  have h0 := congrArg (fun φ => φ.val.app (op O.1) x)
    (π_comp_representedRestrictModuleQuotientHom B S hS U 𝓘 M Ibar hIbar k)
  have h1 : (cokernel.π (idealPowerMultiple B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) 𝓘 k M).ι).val.app
      (op ((selfOpensFunctor B S hS U).obj O.1)) x = 0 :=
    h0.symm.trans hz
  have h2 : (x : M.val.obj (op ((selfOpensFunctor B S hS U).obj O.1))) ∈
      chartSectionIdeal B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
          ((selfOpensFunctor B S hS U).obj O.1) ^ k •
        (⊤ : Submodule (chartRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          ((selfOpensFunctor B S hS U).obj O.1))
          (M.val.obj (op ((selfOpensFunctor B S hS U).obj O.1)))) := by
    rw [← ker_val_app_idealPowerQuotient_π B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) 𝓘 hIcart M hMc k
      (V := (selfOpensFunctor B S hS U).obj O.1) O.2]
    exact h1
  have h3 : x ∈ Ibar.ideal O ^ k • (⊤ : Submodule Γ((BigFppfOver.toScheme B S hS).obj U, O.1)
      Γ((representedRestrictModule B S hS U).obj M, O.1)) := by
    refine Stacks.Submodule.mem_pow_smul_top_of_mem_map_pow_smul_top
      (R' := chartRing B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        ((selfOpensFunctor B S hS U).obj O.1))
      (M := Γ((representedRestrictModule B S hS U).obj M, O.1))
      (M' := M.val.obj (op ((selfOpensFunctor B S hS U).obj O.1)))
      (selfOpensRingHom B S hS U O.1)
      (bijective_selfOpensRingHom B S hS U O.1).2 (AddEquiv.refl _)
      (fun r y => rfl) (Ibar.ideal O) k ?_
    exact (hIbar O).symm ▸ h2
  rw [← Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine] at h3
  exact (Stacks.Algebraization.cokernel_π_app_eq_zero_iff _ _ _ _).2 h3

include hIbar in
/-- Over an affine open the comparison of the quotients is surjective. -/
theorem surjective_representedRestrictModuleQuotientHom_app
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules) (hM : M.IsQuasicoherentOnSite)
    (O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens) :
    Function.Surjective
      ((representedRestrictModuleQuotientHom B S hS U 𝓘 M Ibar hIbar k).val.app (op O.1)) := by
  have hMc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) M hM
  have : ((representedRestrictModule B S hS U).obj M).IsQuasicoherent :=
    isQuasicoherent_restrictModule_representedSmallEtaleModuleInverse M hM
  intro y
  obtain ⟨x, hx⟩ := surjective_val_app_idealPowerQuotient_π B S hS (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS U) 𝓘 hIcart M hMc k
    (V := (selfOpensFunctor B S hS U).obj O.1) O.2 y
  refine ⟨(cokernel.π (Stacks.Algebraization.idealPowerMultiple Ibar k
      ((representedRestrictModule B S hS U).obj M)).ι).val.app (op O.1) x, ?_⟩
  have h := congrArg (fun φ => φ.val.app (op O.1) x)
    (π_comp_representedRestrictModuleQuotientHom B S hS U 𝓘 M Ibar hIbar k)
  exact h.trans hx


include hIbar in
/-- **The restriction of `M / 𝓘 ^ k M` is `(M|_T) / Ī ^ k (M|_T)`**, for `M` quasi-coherent and
`𝓘` cartesian on affine charts: the comparison of the quotients is an isomorphism. -/
theorem isIso_representedRestrictModuleQuotientHom
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules) (hM : M.IsQuasicoherentOnSite) :
    IsIso (representedRestrictModuleQuotientHom B S hS U 𝓘 M Ibar hIbar k) :=
  Stacks.Algebraization.isIso_of_affine_sections_bijective _ fun O =>
    ⟨injective_representedRestrictModuleQuotientHom_app B S hS U 𝓘 M Ibar hIbar k hIcart hM O,
      surjective_representedRestrictModuleQuotientHom_app B S hS U 𝓘 M Ibar hIbar k hIcart hM O⟩

end Quotient


/-! ### The adjunction with the associated module -/

/-- The transport of an `𝒪_T`-module to `yoneda.obj U`: its associated module on the small étale
site of `T` (Stacks 03DU (4)), read on the small étale site of `yoneda.obj U`.  On the
quasi-coherent modules this is the functor of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`. -/
noncomputable abbrev representedAssociate :
    ((BigFppfOver.toScheme B S hS).obj U).Modules ⥤
      Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS U).functor

/-- The transport of `𝒪_T`-modules to `yoneda.obj U` is left adjoint to restriction to `T`. -/
noncomputable def representedAssociateAdjunction :
    representedAssociate B S hS U ⊣ representedRestrictModule B S hS U :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property).comp
    (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction

/-- **The counit is an isomorphism at a quasi-coherent module**: Descent, Proposition 03DX (2). -/
theorem isIso_representedAssociateAdjunction_counit_app
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) :
    IsIso ((representedAssociateAdjunction B S hS U).counit.app N) := by
  have h := _root_.AlgebraicGeometry.SmallEtale.isIso_counit (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj N)
    (isQuasicoherentOnSite_representedSmallEtaleModuleInverse N hN)
    (isQuasicoherent_restrictModule_representedSmallEtaleModuleInverse N hN)
  have key := Adjunction.comp_counit_app
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction N
  exact key ▸ @IsIso.comp_isIso _ _ _ _ _ _ _
    (Functor.map_isIso (F := (representedSmallEtaleModuleEquivalence B S hS U).functor) _)
    (Iso.isIso_hom ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app N))

/-- **The unit is an isomorphism at a quasi-coherent `𝒪_T`-module**: Stacks 0GN7. -/
theorem isIso_representedAssociateAdjunction_unit_app
    (G : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG : SheafOfModules.IsQuasicoherent G) :
    IsIso ((representedAssociateAdjunction B S hS U).unit.app G) := by
  have := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⟨G, hG⟩
  have key := Adjunction.comp_unit_app
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction G
  exact key ▸ inferInstance

/-! ### Full faithfulness on the quasi-coherent modules -/

/-- The quasi-coherent modules on the small étale site of `yoneda.obj U`, as a property of the
objects of `AlgebraicGeometry.Space.Modules`. -/
abbrev representedQuasicoherent :
    ObjectProperty (Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :=
  fun N => N.IsQuasicoherentOnSite

/-- **Restriction to the representing scheme is fully faithful on the quasi-coherent modules.** -/
noncomputable def fullyFaithfulRepresentedRestrictModuleQcoh :
    ((representedQuasicoherent B S hS U).ι ⋙ representedRestrictModule B S hS U).FullyFaithful :=
  Stacks.CategoryTheory.fullyFaithfulιCompOfIsIsoCounit (representedAssociateAdjunction B S hS U)
    _ fun N hN => isIso_representedAssociateAdjunction_counit_app B S hS U N hN

/-- **Restriction to the representing scheme undoes the associated module**: for a
quasi-coherent `𝒪_T`-module `G`, the restriction of `G^a` is `G`, by the inverse of the unit. -/
noncomputable def representedRestrictModuleAssociateIso
    (G : ((BigFppfOver.toScheme B S hS).obj U).Modules) (hG : SheafOfModules.IsQuasicoherent G) :
    (representedRestrictModule B S hS U).obj ((representedAssociate B S hS U).obj G) ≅ G :=
  haveI := isIso_representedAssociateAdjunction_unit_app B S hS U G hG
  (asIso ((representedAssociateAdjunction B S hS U).unit.app G)).symm

/-- **The restriction of a coherent module to the representing scheme is coherent**, for a
locally Noetherian representing scheme. -/
theorem isCoherent_representedRestrictModule
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (N : CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    ((representedRestrictModule B S hS U).obj N.obj).IsCoherent := by
  let E := representedQuasicoherentSchemeEquivalence B S hS U
  let Nq : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS U)).FullSubcategory :=
    ⟨N.obj, N.property.toIsQuasicoherentOnSite⟩
  let e : (E.functor.obj (E.inverse.obj Nq)).obj ≅ N.obj :=
    (ObjectProperty.ι _).mapIso (E.counitIso.app Nq)
  exact Stacks.AlgebraicGeometry.RelativeSerreVanishing.isCoherent_of_iso
    ((representedRestrictModuleAssociateIso B S hS U _ (E.inverse.obj Nq).property).symm ≪≫
      (representedRestrictModule B S hS U).mapIso e)
    ((isCoherent_representedQuasicoherentSchemeEquivalence_iff B S hS U _).1
      (isCoherent_of_iso B S hS (isAlgebraicSpace_yoneda B S hS U) e.symm N.property))

/-- **Restriction to the representing scheme, on coherent modules**: `Coh(yoneda.obj U) ⥤
Coh(𝒪_T)` for a locally Noetherian `T`. -/
noncomputable def representedRestrictCoherent
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      SheafOfModules.CoherentModules ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ representedRestrictModule B S hS U)
    fun N => isCoherent_representedRestrictModule B S hS U N

/-- The inclusion of the coherent modules on `yoneda.obj U` among its quasi-coherent ones. -/
noncomputable def representedCoherentToQuasicoherent :
    CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⥤
      (representedQuasicoherent B S hS U).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _) fun N => N.property.toIsQuasicoherentOnSite

/-- **Restriction to the representing scheme is fully faithful on coherent modules.** -/
noncomputable def fullyFaithfulRepresentedRestrictCoherent
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    (representedRestrictCoherent B S hS U).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful
    (G := ObjectProperty.ι (fun M : SheafOfModules.{u}
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf => M.IsCoherent))
    (((Functor.FullyFaithful.ofCompFaithful (G := (representedQuasicoherent B S hS U).ι)
        (ObjectProperty.fullyFaithfulι _)) :
        (representedCoherentToQuasicoherent B S hS U).FullyFaithful).comp
      (fullyFaithfulRepresentedRestrictModuleQcoh B S hS U))

/-- **Restriction to the representing scheme is essentially surjective on coherent modules**: a
coherent `𝒪_T`-module `G` is the restriction of `G^a`. -/
instance essSurj_representedRestrictCoherent
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    (representedRestrictCoherent B S hS U).EssSurj where
  mem_essImage G :=
    haveI : SheafOfModules.IsCoherent G.obj := G.property
    ⟨(representedCoherentSchemeFunctor B S hS U).obj G,
      ⟨ObjectProperty.isoMk _ (representedRestrictModuleAssociateIso B S hS U G.obj
        (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
          G.obj).1)⟩⟩

/-- Restriction to the representing scheme is an equivalence `Coh(yoneda.obj U) ≌ Coh(𝒪_T)`. -/
instance isEquivalence_representedRestrictCoherent
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    (representedRestrictCoherent B S hS U).IsEquivalence where
  faithful := (fullyFaithfulRepresentedRestrictCoherent B S hS U).faithful
  full := (fullyFaithfulRepresentedRestrictCoherent B S hS U).full

/-! ### Coherent adic systems -/

section Adic

variable (𝓘 : (SheafOfModules.unit.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U)).O))).Submodule)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (Ibar : ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData)
    (hIbar : ∀ O : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
      Ideal.map (selfOpensRingHom B S hS U O.1) (Ibar.ideal O) =
        chartSectionIdeal B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
          ((selfOpensFunctor B S hS U).obj O.1))

include hI hIbar in
/-- **The restriction to the representing scheme of a coherent `𝓘`-adic system is a coherent
`Ī`-adic system.** -/
theorem isCoherentAdicSystem_comp_representedRestrictModule
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (E : CoherentAdicSystems B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘) :
    Stacks.Coherent.IsCoherentAdicSystem Ibar (E.obj ⋙ representedRestrictModule B S hS U) := by
  obtain ⟨hcoh, hann, htr⟩ := E.property
  refine ⟨fun n => isCoherent_representedRestrictModule B S hS U ⟨E.obj.obj (op n), hcoh n⟩,
    fun n => idealPowerMultiple_representedRestrictModule_eq_bot B S hS U 𝓘 Ibar hIbar (n + 1) _
      (hann n), fun n => ?_⟩
  obtain ⟨e, he⟩ := htr n
  have := isIso_representedRestrictModuleQuotientHom B S hS U 𝓘 (E.obj.obj (op (n + 1))) Ibar
    hIbar (n + 1) (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) 𝓘.toSheafOfModules hI)
    (hcoh (n + 1)).toIsQuasicoherentOnSite
  refine ⟨asIso (representedRestrictModuleQuotientHom B S hS U 𝓘 (E.obj.obj (op (n + 1))) Ibar
    hIbar (n + 1)) ≪≫ (representedRestrictModule B S hS U).mapIso e, ?_⟩
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (fun g => g ≫ ((representedRestrictModule B S hS U).mapIso e).hom)
      (π_comp_representedRestrictModuleQuotientHom B S hS U 𝓘 (E.obj.obj (op (n + 1))) Ibar hIbar
        (n + 1))).trans
    (((representedRestrictModule B S hS U).map_comp _ _).symm.trans
      (congrArg (representedRestrictModule B S hS U).map he))

/-- **Restriction to the representing scheme, on coherent adic systems**:
`Coh(yoneda.obj U, 𝓘) ⥤ Coh(T, Ī)`, termwise restriction. -/
noncomputable def representedRestrictAdic
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    CoherentAdicSystems B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 ⥤
      Stacks.Coherent.CoherentAdicSystems Ibar :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (representedRestrictModule B S hS U))
    fun E => isCoherentAdicSystem_comp_representedRestrictModule B S hS U 𝓘 hI Ibar hIbar E

/-- The termwise restriction of a coherent adic system, as a functor, by `rfl`. -/
theorem representedRestrictAdic_obj_obj
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (E : CoherentAdicSystems B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘) :
    ((representedRestrictAdic B S hS U 𝓘 hI Ibar hIbar).obj E).obj =
      E.obj ⋙ representedRestrictModule B S hS U :=
  rfl

/-- **Restriction to the representing scheme is fully faithful on coherent adic systems.** -/
noncomputable def fullyFaithfulRepresentedRestrictAdic
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    (representedRestrictAdic B S hS U 𝓘 hI Ibar hIbar).FullyFaithful where
  preimage {E E'} f := ObjectProperty.homMk
    (Stacks.CategoryTheory.natTransPreimage (fullyFaithfulRepresentedRestrictModuleQcoh B S hS U)
      (fun n : ℕᵒᵖ => (E.property.1 n.unop).toIsQuasicoherentOnSite)
      (fun n : ℕᵒᵖ => (E'.property.1 n.unop).toIsQuasicoherentOnSite) f.hom)
  map_preimage {E E'} f := ObjectProperty.hom_ext _
    (Stacks.CategoryTheory.whiskerRight_natTransPreimage
      (fullyFaithfulRepresentedRestrictModuleQcoh B S hS U)
      (fun n : ℕᵒᵖ => (E.property.1 n.unop).toIsQuasicoherentOnSite)
      (fun n : ℕᵒᵖ => (E'.property.1 n.unop).toIsQuasicoherentOnSite) f.hom)
  preimage_map {E E'} f := ObjectProperty.hom_ext _
    (Stacks.CategoryTheory.natTransPreimage_whiskerRight
      (fullyFaithfulRepresentedRestrictModuleQcoh B S hS U)
      (fun n : ℕᵒᵖ => (E.property.1 n.unop).toIsQuasicoherentOnSite)
      (fun n : ℕᵒᵖ => (E'.property.1 n.unop).toIsQuasicoherentOnSite) f.hom)

/-! ### The completion functors -/

/-- The algebraic space represented by a locally Noetherian scheme is locally Noetherian. -/
instance fact_hasEtaleLocalProperty_yoneda_isLocallyNoetherian
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    Fact (HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
  ⟨hasEtaleLocalProperty_yoneda_isLocallyNoetherian B S hS U⟩

/-- The comparison of the `n`-th terms of the two completions: the `n`-th term of the scheme
completion of the restriction of `M` is the restriction of the `n`-th term of the completion of
`M` on `yoneda.obj U`. -/
noncomputable def representedRestrictCompletionApp
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (n : ℕ) :
    ((Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U) Ibar).obj
        ((representedRestrictCoherent B S hS U).obj M)).obj.obj (op n) ⟶
      (representedRestrictModule B S hS U).obj
        (((completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 hI).obj
          M).obj.obj (op n)) :=
  eqToHom (Stacks.Algebraization.completionFunctor_obj _ Ibar
      ((representedRestrictCoherent B S hS U).obj M) n) ≫
    representedRestrictModuleQuotientHom B S hS U 𝓘 M.obj Ibar hIbar (n + 1)

/-- The comparison of the terms of the two completions is an isomorphism. -/
theorem isIso_representedRestrictCompletionApp
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (n : ℕ) : IsIso (representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M n) := by
  have := isIso_representedRestrictModuleQuotientHom B S hS U 𝓘 M.obj Ibar hIbar (n + 1)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) 𝓘.toSheafOfModules hI)
    M.property.toIsQuasicoherentOnSite
  exact IsIso.comp_isIso' (Iso.isIso_hom (eqToIso (Stacks.Algebraization.completionFunctor_obj _
    Ibar ((representedRestrictCoherent B S hS U).obj M) n))) this

/-- **The scheme projection followed by the comparison is the restriction of the space
projection.** -/
theorem completionProjection_comp_representedRestrictCompletionApp
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (n : ℕ) :
    Stacks.Algebraization.completionProjection _ Ibar ((representedRestrictCoherent B S hS U).obj M)
        n ≫ representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M n =
      (representedRestrictModule B S hS U).map
        (cokernel.π (idealPowerMultiple B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
          𝓘 (n + 1) M.obj).ι) :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((eqToHom_trans_assoc _ _ _).trans
    ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)))).trans
      (π_comp_representedRestrictModuleQuotientHom B S hS U 𝓘 M.obj Ibar hIbar (n + 1)))

/-- The comparison of the terms of the two completions commutes with the transition maps. -/
theorem representedRestrictCompletionApp_naturality
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (n : ℕ) :
    ((Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U) Ibar).obj
        ((representedRestrictCoherent B S hS U).obj M)).obj.map (homOfLE (n.le_add_right 1)).op ≫
        representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M n =
      representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M (n + 1) ≫
        (representedRestrictModule B S hS U).map
          (((completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 hI).obj
            M).obj.map (homOfLE (n.le_add_right 1)).op) := by
  refine (@cancel_epi _ _ _ _ _ _ (Stacks.Algebraization.epi_completionProjection _ Ibar
    ((representedRestrictCoherent B S hS U).obj M) (n + 1)) _ _).1 ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (Stacks.Algebraization.completionProjection_transition _ Ibar _ n)).trans
    ((completionProjection_comp_representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M
        n).trans
    ((congrArg (representedRestrictModule B S hS U).map
        (π_comp_idealPowerQuotientMapOfLE B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U) 𝓘 (Nat.add_le_add_right (n.le_add_right 1) 1)
          M.obj).symm).trans
    (((representedRestrictModule B S hS U).map_comp _ _).trans
    ((congrArg (· ≫ _)
        (completionProjection_comp_representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M
          (n + 1)).symm).trans
      (Category.assoc _ _ _))))))

/-- **The completion of the restriction is the restriction of the completion**, as inverse
systems: `(M|_T)^∧ ≅ (M^∧)|_T`. -/
noncomputable def representedRestrictCompletionSystemIso
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    ((Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U) Ibar).obj
        ((representedRestrictCoherent B S hS U).obj M)).obj ≅
      ((completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 hI).obj
        M).obj ⋙ representedRestrictModule B S hS U :=
  let τ : ((Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U)
        Ibar).obj ((representedRestrictCoherent B S hS U).obj M)).obj ⟶
      ((completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
        hI).obj M).obj ⋙ representedRestrictModule B S hS U :=
    NatTrans.ofOpSequence (representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M)
      (representedRestrictCompletionApp_naturality B S hS U 𝓘 hI Ibar hIbar M)
  haveI : ∀ n : ℕᵒᵖ, IsIso (τ.app n) := fun n =>
    isIso_representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M n.unop
  haveI : IsIso τ := NatIso.isIso_of_isIso_app _
  asIso τ

/-- The components of `AlgebraicGeometry.Space.representedRestrictCompletionSystemIso`. -/
theorem representedRestrictCompletionSystemIso_hom_app
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (M : CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (n : ℕ) :
    (representedRestrictCompletionSystemIso B S hS U 𝓘 hI Ibar hIbar M).hom.app (op n) =
      representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M n :=
  rfl

/-- The comparison of the terms of the two completions is natural in the coherent module. -/
theorem representedRestrictCompletionApp_naturality_hom
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    {M M' : CoherentModules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
    (f : M ⟶ M') (n : ℕ) :
    ((Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U) Ibar).map
        ((representedRestrictCoherent B S hS U).map f)).hom.app (op n) ≫
        representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M' n =
      representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M n ≫
        (representedRestrictModule B S hS U).map
          (((completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
            hI).map f).hom.app (op n)) := by
  refine (@cancel_epi _ _ _ _ _ _ (Stacks.Algebraization.epi_completionProjection _ Ibar
    ((representedRestrictCoherent B S hS U).obj M) n) _ _).1 ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (Stacks.Algebraization.completionFunctor_map_quotient _ Ibar
      ((representedRestrictCoherent B S hS U).map f) n)).trans
    ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (completionProjection_comp_representedRestrictCompletionApp B S hS U 𝓘 hI
      Ibar hIbar M' n)).trans
    (((representedRestrictModule B S hS U).map_comp _ _).symm.trans
    ((congrArg (representedRestrictModule B S hS U).map
        (π_comp_idealPowerQuotientMapOfHom B S hS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B S hS U) 𝓘 (n + 1) f.hom).symm).trans
    (((representedRestrictModule B S hS U).map_comp _ _).trans
    ((congrArg (· ≫ _)
        (completionProjection_comp_representedRestrictCompletionApp B S hS U 𝓘 hI Ibar hIbar M
          n).symm).trans
      (Category.assoc _ _ _))))))))

/-- **Restriction to the representing scheme commutes with completion**:
`(M^∧)|_T ≅ (M|_T)^∧` naturally in the coherent module `M` on `yoneda.obj U`, where the
completion on the left is Stacks 08B4 along `𝓘` and on the right Stacks 0880 along `Ī`. -/
noncomputable def representedRestrictCompletionIso
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)] :
    representedRestrictCoherent B S hS U ⋙
        Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U) Ibar ≅
      completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 hI ⋙
        representedRestrictAdic B S hS U 𝓘 hI Ibar hIbar :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      (representedRestrictCompletionSystemIso B S hS U 𝓘 hI Ibar hIbar M))
    (fun f => ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n =>
      representedRestrictCompletionApp_naturality_hom B S hS U 𝓘 hI Ibar hIbar f n.unop)))

/-! ### Transfer of the scheme theorems to the represented algebraic space -/

/-- **Full faithfulness of completion transfers from the scheme to the algebraic space it
represents.**  If the completion functor `Coh(𝒪_T) ⥤ Coh(T, Ī)` of Stacks 0880 is fully faithful
(Stacks 0883 for `T` proper over a complete Noetherian ring), so is the completion functor
`Coh(yoneda.obj U) ⥤ Coh(yoneda.obj U, 𝓘)` of Stacks 08B4. -/
noncomputable def fullyFaithfulCompletionFunctorOfScheme
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    (h : (Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U)
      Ibar).FullyFaithful) :
    (completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
      hI).FullyFaithful :=
  haveI := (fullyFaithfulRepresentedRestrictAdic B S hS U 𝓘 hI Ibar hIbar).faithful
  Functor.FullyFaithful.ofCompFaithful (G := representedRestrictAdic B S hS U 𝓘 hI Ibar hIbar)
    (((fullyFaithfulRepresentedRestrictCoherent B S hS U).comp h).ofIso
      (representedRestrictCompletionIso B S hS U 𝓘 hI Ibar hIbar))

include hIbar in
/-- **Essential surjectivity of completion transfers from the scheme to the algebraic space it
represents.**  If every coherent `Ī`-adic system on `T` is the completion of a coherent module
(Stacks 0885, 088C), so is every coherent `𝓘`-adic system on `yoneda.obj U`. -/
theorem essSurj_completionFunctor_of_scheme
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    [(Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U) Ibar).EssSurj] :
    (completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘 hI).EssSurj where
  mem_essImage E := by
    let C := Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U) Ibar
    let R := representedRestrictAdic B S hS U 𝓘 hI Ibar hIbar
    let G := C.objPreimage (R.obj E)
    let M := (representedRestrictCoherent B S hS U).objPreimage G
    let e : R.obj ((completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
        hI).obj M) ≅ R.obj E :=
      (representedRestrictCompletionIso B S hS U 𝓘 hI Ibar hIbar).symm.app M ≪≫
        C.mapIso ((representedRestrictCoherent B S hS U).objObjPreimageIso G) ≪≫
        C.objObjPreimageIso (R.obj E)
    exact ⟨M, ⟨(fullyFaithfulRepresentedRestrictAdic B S hS U 𝓘 hI Ibar hIbar).preimageIso e⟩⟩

include hIbar in
/-- **Grothendieck existence transfers from the scheme to the algebraic space it represents**: if
the completion functor of Stacks 0880 on `T` along `Ī` is an equivalence (Stacks 0885 for `T`
projective, Stacks 088C for `T` proper, over a complete Noetherian ring), so is the completion
functor of Stacks 08B4 on `yoneda.obj U` along `𝓘`. -/
theorem isEquivalence_completionFunctor_of_scheme
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U)]
    [(Stacks.Algebraization.completionFunctor ((BigFppfOver.toScheme B S hS).obj U)
      Ibar).IsEquivalence] :
    (completionFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) 𝓘
      hI).IsEquivalence :=
  have := essSurj_completionFunctor_of_scheme B S hS U 𝓘 hI Ibar hIbar
  have hff := fullyFaithfulCompletionFunctorOfScheme B S hS U 𝓘 hI Ibar hIbar
    (Functor.FullyFaithful.ofFullyFaithful _)
  { faithful := hff.faithful, full := hff.full }

end Adic

end AlgebraicGeometry.Space

end
