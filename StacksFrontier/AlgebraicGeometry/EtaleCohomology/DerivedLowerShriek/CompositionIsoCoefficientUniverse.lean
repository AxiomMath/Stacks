module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.OpenImmersionDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.IndependenceCoefficientUniverse
import StacksCore.Tactic.StacksAttribute

/-!
# The composition of derived lower shrieks at every coefficient universe ([Stacks, Tag 0F7J])

-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u w

namespace Stacks.EtaleCohomology

attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

/-! ### Torsion objects of `D⁺`, at every coefficient universe -/

section Torsion

variable (Λ : Type w) [Ring Λ]

/-- Torsion sheaves of modules are closed under isomorphism, for `Λ` in any universe. -/
theorem IsTorsionEtaleModule.of_iso_univ {X : Scheme.{u}} {F G : EtaleModules.{u, w} Λ X}
    (e : F ≅ G) (hF : IsTorsionEtaleModule.{u, w} Λ X F) : IsTorsionEtaleModule.{u, w} Λ X G := by
  have : X.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{max (u + 1) w} Λ) :=
    wEqualsLocallyBijective_etaleModules.{u, w} Λ X
  exact IsLocallyTorsionModulePresheaf.of_isLocallySurjective
    ((sheafToPresheaf X.smallEtaleTopology _).map e.hom) inferInstance hF

/-- **`Rj_!` carries `D⁺_tors(U)` into `D⁺_tors(X)`**, for `Λ` in any universe: on cohomology
sheaves it is `j_!`, which preserves torsion sheaves. -/
theorem isTorsionPlus_etaleModuleDerivedExtensionByZero_obj_univ {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ U))
    (hK : isTorsionPlus.{u, w} Λ U K) :
    isTorsionPlus.{u, w} Λ X ((etaleModuleDerivedExtensionByZero.{u, w} Λ j).obj K) := fun q =>
  IsTorsionEtaleModule.of_iso_univ Λ (etaleModuleDerivedExtensionByZeroHomologyIsoUniv Λ j K q).symm
    (isTorsionEtaleModule_etaleModuleExtensionByZero_obj_univ Λ j _ (hK q))

end Torsion

/-! ### The open immersion case of [Stacks, Tag 0F7B] on `D⁺_tors`, at every coefficient
universe -/

section OpenBaseChange

variable (Λ : Type w) [Ring Λ]
  {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
  (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i)

include sq in
/-- **`Rf̄_* Rb_! K` vanishes over the closed complement of `Y`** for `K` in `D⁺_tors`: its
inverse image there is computed from the `c^{-1} R^p f̄_*(b_! H^q K)`, which vanish by proper base
change ([Stacks, Tag 095T]), the torsion sheaf `b_! H^q K` vanishing on everything lying over the
complement. -/
theorem isZero_etaleModuleDerivedInverseImagePlus_directImage_extensionByZero_univ
    (K : DerivedCategory.Plus (EtaleModules.{u, w} Λ P)) (hK : isTorsionPlus.{u, w} Λ P K) :
    IsZero ((etaleModuleDerivedInverseImagePlus.{u, w} Λ (openImmersionComplementι i)).obj
      ((etaleModuleDerivedDirectImage.{u, w} Λ fb).obj
        ((etaleModuleDerivedExtensionByZero.{u, w} Λ b).obj K))) := by
  refine isZero_etaleModuleDerivedInverseImagePlus_derivedDirectImage_of_rightDerived Λ fb
    (openImmersionComplementι i) _ fun q p => ?_
  refine IsZero.of_iso ?_ ((etaleModuleInverseImage.{u, w} Λ _).mapIso
    (((etaleModuleDirectImage.{u, w} Λ fb).rightDerived p).mapIso
      (etaleModuleDerivedExtensionByZeroHomologyIsoUniv Λ b K q)))
  refine isZero_etaleModuleInverseImage_rightDerived_directImage_of_isProper_univ Λ fb
    (openImmersionComplementι i) _ (fun V t ht => ?_)
    (isTorsionEtaleModule_etaleModuleExtensionByZero_obj_univ Λ b _ (hK q)) p
  exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ t b
    (disjoint_range_of_range_subset_preimage_openImmersionComplementι fb i b f' sq t ht) _

/-- **The open immersion case of [Stacks, Tag 0F7B]**, for `Λ` in any universe: for a cartesian
square `b ≫ f̄ = f' ≫ i` with `f̄` proper and `i` an open immersion,
`Rf̄_* ∘ Rb_! ≅ Ri_! ∘ Rf'_*` on `D⁺_tors(P_étale, Λ)`. -/
def etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProperUniv :
    (isTorsionPlus.{u, w} Λ P).ι ⋙ (etaleModuleDerivedExtensionByZero.{u, w} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, w} Λ fb) ≅
      (isTorsionPlus.{u, w} Λ P).ι ⋙ (etaleModuleDerivedDirectImage.{u, w} Λ f' ⋙
        etaleModuleDerivedExtensionByZero.{u, w} Λ i) :=
  let φ := Functor.whiskerLeft (isTorsionPlus.{u, w} Λ P).ι
    (etaleModuleDerivedExtensionByZeroDirectImageMap Λ fb i b f' sq)
  haveI : ∀ K, IsIso (φ.app K) := fun K =>
    isIso_etaleModuleDerivedExtensionByZeroDirectImageMap_app Λ fb i b f' sq K.obj
      (isZero_etaleModuleDerivedInverseImagePlus_directImage_extensionByZero_univ Λ fb i b f' sq
        K.obj K.property)
  haveI : IsIso φ := NatIso.isIso_of_isIso_app _
  (asIso φ).symm

end OpenBaseChange

section Composition

variable (Λ : Type w) [Ring Λ] {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- **`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` for the compactifications of the proof of [Stacks, Tag 0F7J]**,
on `D⁺_tors(X_étale, Λ)`, from the open immersion case `β` of [Stacks, Tag 0F7B]:
`Rf̄_* ∘ j'_! ≅ i_! ∘ Rf'_*` on `D⁺_tors(U_étale, Λ)`, and the preservation of torsion
cohomology by `j_!`. The chain is
`R(ḡ ∘ f̄)_* (j' ∘ j)_! ≅ Rḡ_* Rf̄_* j'_! j_! ≅ Rḡ_* i_! Rf'_* j_!`, the first isomorphism being
the composition of direct images and of extensions by zero. -/
def derivedLowerShriekCompOverIsoOfBaseChangeUniv
    (β : (isTorsionPlus.{u, w} Λ (CompactificationOf.restrictBase jg jX).space).ι ⋙
        (etaleModuleDerivedExtensionByZero.{u, w} Λ (CompactificationOf.restrictBaseι jg jX) ⋙
          etaleModuleDerivedDirectImage.{u, w} Λ jX.toBase) ≅
      (isTorsionPlus.{u, w} Λ (CompactificationOf.restrictBase jg jX).space).ι ⋙
        (etaleModuleDerivedDirectImage.{u, w} Λ (CompactificationOf.restrictBase jg jX).toBase ⋙
          etaleModuleDerivedExtensionByZero.{u, w} Λ jg.immersion))
    (hj : ∀ K, isTorsionPlus.{u, w} Λ X K →
      isTorsionPlus.{u, w} Λ (CompactificationOf.restrictBase jg jX).space
        ((etaleModuleDerivedExtensionByZero.{u, w} Λ
          (CompactificationOf.restrictBase jg jX).immersion).obj K)) :
    (isTorsionPlus.{u, w} Λ X).ι ⋙
        derivedLowerShriek.{u, w} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      (isTorsionPlus.{u, w} Λ X).ι ⋙
        derivedLowerShriek.{u, w} f (CompactificationOf.restrictBase jg jX) Λ ⋙
          derivedLowerShriek.{u, w} g jg Λ := by
  let a := (CompactificationOf.restrictBase jg jX).immersion
  let b := CompactificationOf.restrictBaseι jg jX
  -- `(b ∘ a)_! ≅ b_! ∘ a_!` and `R(ḡ ∘ f̄)_* ≅ Rḡ_* ∘ Rf̄_*`
  let e₁ : etaleModuleDerivedExtensionByZero.{u, w} Λ (a ≫ b) ≅
      etaleModuleDerivedExtensionByZero.{u, w} Λ a ⋙
        etaleModuleDerivedExtensionByZero.{u, w} Λ b :=
    (Functor.rightDerivedFunctorPlusCompIsoOfExact
      (etaleModuleExtensionByZero.{u, w} Λ a) (etaleModuleExtensionByZero.{u, w} Λ b)
      (etaleModuleExtensionByZero.{u, w} Λ (a ≫ b))
      (etaleModuleExtensionByZeroCompIso.{u, w} Λ a b).symm).symm
  let e₂ := etaleModuleDerivedDirectImageComp.{u, w} Λ jX.toBase jg.toBase
    (jX.toBase ≫ jg.toBase) rfl
  -- `j_!` carries `D⁺_tors(X)` into `D⁺_tors(U)`
  let L := ObjectProperty.lift
    (isTorsionPlus.{u, w} Λ (CompactificationOf.restrictBase jg jX).space)
    ((isTorsionPlus.{u, w} Λ X).ι ⋙ etaleModuleDerivedExtensionByZero.{u, w} Λ a)
    (fun K => hj K.obj K.property)
  let eL : L ⋙ (isTorsionPlus.{u, w} Λ (CompactificationOf.restrictBase jg jX).space).ι ≅
      (isTorsionPlus.{u, w} Λ X).ι ⋙ etaleModuleDerivedExtensionByZero.{u, w} Λ a :=
    ObjectProperty.liftCompιIso _ _ _
  let ιX := (isTorsionPlus.{u, w} Λ X).ι
  let ιU := (isTorsionPlus.{u, w} Λ (CompactificationOf.restrictBase jg jX).space).ι
  let Ra := etaleModuleDerivedExtensionByZero.{u, w} Λ a
  let Rb := etaleModuleDerivedExtensionByZero.{u, w} Λ b
  let Rfb := etaleModuleDerivedDirectImage.{u, w} Λ jX.toBase
  let Rgb := etaleModuleDerivedDirectImage.{u, w} Λ jg.toBase
  let Rf' := etaleModuleDerivedDirectImage.{u, w} Λ (CompactificationOf.restrictBase jg jX).toBase
  let Ri := etaleModuleDerivedExtensionByZero.{u, w} Λ jg.immersion
  let s₁ : ιX ⋙ derivedLowerShriek.{u, w} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      (ιX ⋙ Ra) ⋙ ((Rb ⋙ Rfb) ⋙ Rgb) :=
    Functor.isoWhiskerLeft ιX (Functor.isoWhiskerRight e₁ _ ≪≫ Functor.isoWhiskerLeft _ e₂)
  let s₂ : (ιX ⋙ Ra) ⋙ ((Rb ⋙ Rfb) ⋙ Rgb) ≅ (L ⋙ ιU) ⋙ ((Rb ⋙ Rfb) ⋙ Rgb) :=
    Functor.isoWhiskerRight eL.symm _
  let s₃ : (L ⋙ ιU) ⋙ ((Rb ⋙ Rfb) ⋙ Rgb) ≅ (L ⋙ ιU) ⋙ ((Rf' ⋙ Ri) ⋙ Rgb) :=
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight β Rgb)
  let s₄ : (L ⋙ ιU) ⋙ ((Rf' ⋙ Ri) ⋙ Rgb) ≅ (ιX ⋙ Ra) ⋙ ((Rf' ⋙ Ri) ⋙ Rgb) :=
    Functor.isoWhiskerRight eL _
  exact s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄

/-- **`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` through the compactifications of the proof of
[Stacks, Tag 0F7J]**, for `Λ` in any universe, on `D⁺_tors(X_étale, Λ)`: the assembly
`Stacks.EtaleCohomology.derivedLowerShriekCompOverIsoOfBaseChangeUniv` applied to the open
immersion case of [Stacks, Tag 0F7B]
(`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProperUniv`). -/
def derivedLowerShriekCompOverIsoUniv :
    (isTorsionPlus.{u, w} Λ X).ι ⋙
        derivedLowerShriek.{u, w} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      (isTorsionPlus.{u, w} Λ X).ι ⋙
        derivedLowerShriek.{u, w} f (CompactificationOf.restrictBase jg jX) Λ ⋙
          derivedLowerShriek.{u, w} g jg Λ :=
  derivedLowerShriekCompOverIsoOfBaseChangeUniv Λ jg jX
    (etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProperUniv Λ jX.toBase jg.immersion
      (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion))
    (fun K hK => isTorsionPlus_etaleModuleDerivedExtensionByZero_obj_univ Λ _ K hK)

end Composition

section CompositionIso

variable (Λ : Type w) [Ring Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks Project, Tag 0F7J**, for a coefficient ring `Λ` in any universe. Let `f : X ⟶ Y` and
`g : Y ⟶ Z` be separated morphisms of finite type of quasi-compact and quasi-separated schemes,
and let `Λ` be a ring. Then `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` as functors on `D⁺_tors(X_étale, Λ)`,
where `Rf_!`, `Rg_!` and `R(g ∘ f)_!` are computed through arbitrary compactifications `jf`, `jg`
and `j`.

Through a compactification `X ⟶ X̄` of `X` over `Ȳ` (Nagata's theorem, [Stacks, Tag 0F41]) the
isomorphism is `Stacks.EtaleCohomology.derivedLowerShriekCompOverIsoUniv`, which uses
[Stacks, Tag 0F7B] for the open immersion `Y ⟶ Ȳ`; it is transported to the given
compactifications by [Stacks, Tag 0F7I]
(`Stacks.EtaleCohomology.derivedLowerShriekCompactificationIsoUniv`). -/
@[stacks 0F7J "D⁺_tors(X_étale, Λ), Λ a ring in any universe"]
def derivedLowerShriekCompIsoUniv [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f]
    [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (jf : CompactificationOf (Over.mk f)) (jg : CompactificationOf (Over.mk g))
    (j : CompactificationOf (Over.mk (f ≫ g))) :
    (isTorsionPlus.{u, w} Λ X).ι ⋙ derivedLowerShriek.{u, w} (f ≫ g) j Λ ≅
      (isTorsionPlus.{u, w} Λ X).ι ⋙ derivedLowerShriek.{u, w} f jf Λ ⋙
        derivedLowerShriek.{u, w} g jg Λ :=
  haveI : QuasiCompact f := quasiCompact_of_compactSpace f
  haveI : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  let jX := (nonempty_compactificationOf_comp_immersion f g jg).some
  derivedLowerShriekCompactificationIsoUniv (f ≫ g) j (CompactificationOf.compOver jg jX) Λ ≪≫
    derivedLowerShriekCompOverIsoUniv Λ jg jX ≪≫
    Functor.isoWhiskerRight
      (derivedLowerShriekCompactificationIsoUniv f (CompactificationOf.restrictBase jg jX) jf Λ)
      (derivedLowerShriek.{u, w} g jg Λ)

end CompositionIso

end Stacks.EtaleCohomology

end
