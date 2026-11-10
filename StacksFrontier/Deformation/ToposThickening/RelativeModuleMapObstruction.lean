module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MultiplicationIdealProduct
public import StacksFrontier.Deformation.ToposThickening.ExtensionDifference
public import StacksFrontier.Deformation.ToposThickening.FlatLiftTorsors
public import StacksFrontier.Deformation.ToposThickening.IdealProductSequence
public import StacksFrontier.Deformation.ToposThickening.IdealProductTensorIso

/-!
# The relative obstruction to lifting a map of modules

Let `(f, f')` be a morphism of first order thickenings of ringed topoi

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_B) --t-->  (Sh(B'), O_{B'})
```

with square-zero ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`, and suppose the square
is strict. Let `ℱ'` and `𝒢'` be `O'`-modules flat over `O_{ℬ'}`, write `ℱ = i^*ℱ'` and
`𝒢 = i^*𝒢'`, and let `φ : ℱ ⟶ 𝒢` be an `O`-linear map. This file produces a class

```
  o(φ) ∈ Ext¹_O(ℱ, 𝒢 ⊗_O f^*𝒥)
```

whose vanishing is necessary and sufficient for `φ` to lift to an `O'`-linear map `ℱ' ⟶ 𝒢'`.
This is **Stacks 08MT**.

## Main definitions

* `Deformation.ToposThickening.idealTensorFunctor`: tensoring with the square-zero ideal of a
  first order thickening, as an endofunctor of the modules on the thickened topos.
* `Deformation.ToposThickening.idealAction`: the action `I ⊗_{O'} - ⟶ -` of the square-zero
  ideal, as a natural transformation. Its components are the multiplication maps of Stacks 08M4.
* `Deformation.ToposThickening.IsIdealActionMono`: the consequence of Stacks 08MQ that the proof
  consumes for `ℱ'`. See the scope section.

## Main results

* `Deformation.ToposThickening.unitIsCokernelIdealAction`: the unit `M ⟶ i_*i^*M` of the
  adjunction is a cokernel of the ideal action at `M`.
* `Deformation.ToposThickening.shortExact_map_pullbackModules`: a short exact sequence whose
  first term is a direct image and whose last term has injective ideal action stays short exact
  after `i^*`.
* `Deformation.ToposThickening.relativeModuleMapObstruction`: **Stacks 08MT**, in the general
  form that takes `Deformation.ToposThickening.IsIdealActionMono` as an explicit hypothesis. The
  tag registers on `Deformation.ToposThickening.relativeModuleMapObstructionClass_eq_zero_iff` in
  `StacksFrontier/Deformation/ToposThickening/IdealActionMono.lean`, where that hypothesis is
  supplied by `Deformation.ToposThickening.isIdealActionMono` and the class is a definition,
  `Deformation.ToposThickening.relativeModuleMapObstructionClass`. See the scope section.

## Implementation notes

The construction is the source's second proof, read without the extension-theoretic
bookkeeping. The defining sequence of `𝒢'`,

```
  0 ⟶ I·𝒢' ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0,
```

is `Deformation.ToposThickening.idealProductShortComplex_shortExact` of Stacks 08MP, with its
first term read through `Deformation.ToposThickening.idealProductModule` as the direct image of
an `O`-module. Pulling it back along the adjoint transpose `ℱ' ⟶ i_*𝒢` of `φ` gives a short
exact sequence of `O'`-modules whose retractions are exactly the maps `ℱ' ⟶ 𝒢'` lifting `φ`
(`Deformation.ToposThickening.pullback_retraction_iff` and
`Deformation.ToposThickening.nonempty_moduleMapLift_iff_exists_factorization`). Applying `i^*`
turns it into a short exact sequence of `O`-modules, and its Ext class — transported along the
isomorphism of the coefficient module supplied by Stacks 08MQ — is `o(φ)`. That an Ext class
vanishes exactly when the sequence is split is
`Deformation.ToposThickening.extClass_comp_mk₀_eq_zero_iff`, and that a retraction of the
pulled-back sequence descends to one before `i^*` is
`Deformation.ToposThickening.exists_retraction_map_iff`, the unit being invertible on a direct
image.

Exactness after `i^*` is the one place where flatness of `ℱ'` is used, and the only thing to
check is that the first map stays a monomorphism. The direct image of modules along a
thickening is fully faithful (Stacks 08M3), so that reduces to the monomorphy of
`I·𝒢' ⟶ P ⟶ i_*i^*P`, which is
`Deformation.ToposThickening.mono_comp_of_cokernel_action`: the ideal acts by zero on the direct
image `I·𝒢'`, it acts injectively on `ℱ'`, and the unit is a cokernel of its action. The ideal
action is the multiplication map of Stacks 08M4,
`Stacks.SheafOfModules.FlatSquareZero.multiplicationMap`, whose naturality is already recorded
there; that the unit is a cokernel of it is
`Stacks.SheafOfModules.FlatSquareZero.cokernelCofork_multiplicationMap_isColimit` applied to the
ideal-product sequence, the ideal product of Stacks 08MP being the image product of that file on
the nose.

The coefficient module is the source's `𝒢 ⊗_O f^*𝒥`, with `f^*𝒥` the `O`-module
`Deformation.ToposThickening.basePullbackIdeal`. Stacks 08MQ, and so
`Deformation.ToposThickening.IsIdealProductTensorIso`, identifies the ideal product with the
other order `f^*𝒥 ⊗_O 𝒢`, which is how
`Deformation.ToposThickening.moduleMapLift_torsor_of_isFlat` states Stacks 08MR; the two are
exchanged by the symmetry
`Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight` of the sheaf tensor product.
The Ext group is taken in the `O`-modules on `Sh(C)`, which is where the source takes it.

## Scope

Stacks 08MQ — the characterization of the `O'`-modules flat over `O_{ℬ'}` — is in the library:
it is `Deformation.ToposThickening.isFlat_iff_isIso_canonicalMap` in
`StacksFrontier/Deformation/ToposThickening/FlatLiftFlatnessEquivalence.lean`. Both consequences of
it that the proof below consumes are proved from it, and the tagged statement of Stacks 08MT,
`Deformation.ToposThickening.relativeModuleMapObstructionClass_eq_zero_iff`, assumes neither of
them.

* `Deformation.ToposThickening.IsIdealProductTensorIso` is 08MQ for `𝒢'`: for a strict square
  and `𝒢'` flat over `O_{ℬ'}`, the module `f^*𝒥 ⊗_O 𝒢` is the ideal product `I·𝒢'`. This is
  what puts the class in the Ext group the source names. `relativeModuleMapObstruction` below
  takes it from `Deformation.ToposThickening.isIdealProductTensorIso`, which proves it.
* `Deformation.ToposThickening.IsIdealActionMono` is 08MQ for `ℱ'`: under the same two
  hypotheses, the ideal action `I ⊗_{O'} ℱ' ⟶ ℱ'` is injective. This is the final assertion of
  08MQ, that the second factor `I ⊗_O ℱ ⟶ I·ℱ'` of its canonical map is an isomorphism, read
  through `Stacks.SheafOfModules.FlatSquareZero.multiplicationMapIsoIdealProduct`.
  `Deformation.ToposThickening.isIdealActionMono` proves it, in a module that imports this one,
  so it is supplied there — in
  `Deformation.ToposThickening.exists_relativeModuleMapObstruction` — rather than in the general
  form below, whose instance and data binders are otherwise identical.

Nothing below asserts the content of 08MQ, and nothing in the tagged statement of Stacks 08MT
assumes any of it.

## References

* [Stacks Project, Tag 08MT](https://stacks.math.columbia.edu/tag/08MT)
* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 08M4](https://stacks.math.columbia.edu/tag/08M4)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08M9](https://stacks.math.columbia.edu/tag/08M9)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w v' u' vS uS wS vS' uS' wS' e

namespace Deformation.ToposThickening

section Generic

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]

/-- A map of an adjunction's left adjoint is the image of a map exactly when the corresponding
square with the unit commutes. -/
theorem pullback_map_eq_iff_unit_comp
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {F G : A} (f : F ⟶ G) (g : L.obj F ⟶ L.obj G) :
    L.map f = g ↔ f ≫ adj.unit.app G = adj.unit.app F ≫ R.map g := by
  constructor
  · rintro rfl
    exact adj.unit.naturality f
  · intro h
    apply (adj.homEquiv F (L.obj G)).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact (adj.unit.naturality f).symm.trans h

/-- A map whose unit is invertible at its source has a retraction exactly when its image under
the left adjoint has one. -/
theorem exists_retraction_map_iff
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {K M : A} [IsIso (adj.unit.app K)] (f : K ⟶ M) :
    (∃ r : L.obj M ⟶ L.obj K, L.map f ≫ r = 𝟙 _) ↔ ∃ r : M ⟶ K, f ≫ r = 𝟙 _ := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨adj.unit.app M ≫ R.map r ≫ inv (adj.unit.app K), ?_⟩
    rw [← Category.assoc, ← adj.unit_naturality, Category.assoc, ← R.map_comp_assoc, hr, R.map_id,
      Category.id_comp, IsIso.hom_inv_id]
  · rintro ⟨r, hr⟩
    exact ⟨L.map r, by rw [← L.map_comp, hr, L.map_id]⟩

/-- A map admits a retraction exactly when it admits one up to a prescribed isomorphism of its
source. -/
theorem exists_comp_eq_iso_iff_exists_retraction {V M Z : B} (g : V ⟶ M) (ξ : V ≅ Z) :
    (∃ s : M ⟶ Z, g ≫ s = ξ.hom) ↔ ∃ r : M ⟶ V, g ≫ r = 𝟙 V := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s ≫ ξ.inv, by rw [← Category.assoc, hs, ξ.hom_inv_id]⟩
  · rintro ⟨r, hr⟩
    exact ⟨r ≫ ξ.hom, by rw [← Category.assoc, hr, Category.id_comp]⟩

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- Pulling a short exact sequence back along a map into its last term gives a short exact
sequence. -/
theorem pullback_shortExact {S : ShortComplex D} (hS : S.ShortExact) {F : D} (u : F ⟶ S.X₃) :
    (ShortComplex.mk
      (pullback.lift (f := u) (g := S.g) (0 : S.X₁ ⟶ F) S.f
        (by rw [zero_comp, S.zero]))
      (pullback.fst u S.g) (pullback.lift_fst _ _ _)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ inferInstance
  · apply (ShortComplex.exact_iff_exact_up_to_refinements _).2
    intro Z z hz
    dsimp only at z hz
    obtain ⟨y, hy⟩ := hS.exact.lift' (z ≫ pullback.snd u S.g) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hz, zero_comp])
    refine ⟨Z, 𝟙 Z, inferInstance, y, ?_⟩
    dsimp
    rw [Category.id_comp]
    exact pullback.hom_ext (by rwa [Category.assoc, pullback.lift_fst, comp_zero])
      (by rw [Category.assoc, pullback.lift_snd, hy])
  · exact mono_of_mono_fac (pullback.lift_snd _ _ _)

/-- The pulled back sequence splits exactly when the map it was pulled back along factors
through the middle term of the original sequence. -/
theorem pullback_retraction_iff {S : ShortComplex D} (hS : S.ShortExact) {F : D} (u : F ⟶ S.X₃) :
    (∃ r : pullback u S.g ⟶ S.X₁,
      pullback.lift (f := u) (g := S.g) (0 : S.X₁ ⟶ F) S.f
        (by rw [zero_comp, S.zero]) ≫ r = 𝟙 _) ↔
      ∃ t : F ⟶ S.X₂, t ≫ S.g = u := by
  have := hS.mono_f
  let l := pullback.lift (f := u) (g := S.g) (0 : S.X₁ ⟶ F) S.f
    (by rw [zero_comp, S.zero])
  let p := pullback.fst u S.g
  let s := pullback.snd u S.g
  have hP := pullback_shortExact hS u
  have : Epi p := hP.epi_g
  have hlp : l ≫ p = 0 := pullback.lift_fst _ _ _
  have hls : l ≫ s = S.f := pullback.lift_snd _ _ _
  have hps : p ≫ u = s ≫ S.g := pullback.condition
  constructor
  · rintro ⟨r, hr⟩
    change l ≫ r = 𝟙 _ at hr
    obtain ⟨t, ht⟩ := hP.exact.desc' (s - r ≫ S.f) (by
      change l ≫ (s - r ≫ S.f) = 0
      rw [Preadditive.comp_sub, hls, ← Category.assoc, hr, Category.id_comp, sub_self])
    change p ≫ t = s - r ≫ S.f at ht
    refine ⟨t, ?_⟩
    apply (cancel_epi p).1
    rw [← Category.assoc, ht, Preadditive.sub_comp, Category.assoc, S.zero,
      comp_zero, sub_zero, hps]
  · rintro ⟨t, ht⟩
    obtain ⟨r, hr⟩ := hS.exact.lift' (s - p ≫ t) (by
      rw [Preadditive.sub_comp, Category.assoc, ht, hps, sub_self])
    refine ⟨r, ?_⟩
    apply (cancel_mono S.f).1
    change (l ≫ r) ≫ S.f = _
    rw [Category.assoc, hr, Preadditive.comp_sub, hls, ← Category.assoc,
      hlp, zero_comp, sub_zero, Category.id_comp]

/-- Replacing the first term of a short exact sequence by an isomorphic object keeps it short
exact. -/
theorem shortExact_isoComp_f {S : ShortComplex D} (hS : S.ShortExact) {A : D} (e : A ≅ S.X₁) :
    (ShortComplex.mk (e.hom ≫ S.f) S.g
      (by rw [Category.assoc, S.zero, comp_zero])).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _)
      (by simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])) hS

/-- **The first term of a short exact sequence meets no multiple of the middle term.** Let `T`
be a right exact additive endofunctor with a map `a : T ⟶ 𝟭`, let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be
short exact, assume `a` vanishes at `X₁` and is a monomorphism at `X₃`, and let `q` be a
cokernel of `a` at `X₂`. Then `X₁ ⟶ X₂ ⟶ Q` is a monomorphism. -/
theorem mono_comp_of_cokernel_action
    (T : D ⥤ D) [T.Additive] [PreservesFiniteColimits T]
    (a : T ⟶ 𝟭 D) (S : ShortComplex D) (hS : S.ShortExact)
    [Mono (a.app S.X₃)] (ha : a.app S.X₁ = 0)
    {Q : D} (q : S.X₂ ⟶ Q) (hq : a.app S.X₂ ≫ q = 0)
    (hc : IsColimit (CokernelCofork.ofπ q hq)) : Mono (S.f ≫ q) := by
  have := hS.mono_f
  have := hS.epi_g
  have hT := hS.exact.map_of_epi_of_preservesCokernel T
    (inferInstance : Epi S.g) (inferInstance : PreservesColimit (parallelPair S.f 0) T)
  apply (Preadditive.mono_iff_cancel_zero _).2
  intro Z z hz
  obtain ⟨Z', p, hp, x, hx⟩ :=
    (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements hc (z ≫ S.f)).1
      (by simpa [Category.assoc] using hz)
  have hxg : x ≫ T.map S.g = 0 := by
    apply (cancel_mono (a.app S.X₃)).1
    rw [zero_comp, Category.assoc, a.naturality, ← Category.assoc, ← hx,
      Category.assoc, Category.assoc, Functor.id_map, S.zero, comp_zero, comp_zero]
  obtain ⟨Z'', p', hp', y, hy⟩ := hT.exact_up_to_refinements x hxg
  change p' ≫ x = y ≫ T.map S.f at hy
  apply (cancel_epi (p' ≫ p)).1
  apply (cancel_mono S.f).1
  rw [comp_zero, zero_comp, Category.assoc, Category.assoc, hx,
    ← Category.assoc p', hy, Category.assoc, a.naturality, ha, zero_comp, comp_zero]

end Generic

section IdealAction

open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.FlatSquareZero (multiplicationMap multiplicationMap_natural ringMap)

attribute [local instance] Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

/-- The square-zero ideal of a first order thickening, read as a sheaf of modules over the
thickened structure sheaf. -/
noncomputable abbrev idealOverThickened (hi : FirstOrderThickening i) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I

/-- Tensoring with the square-zero ideal of a first order thickening, as an endofunctor of the
sheaves of modules on the thickened topos. -/
noncomputable abbrev idealTensorFunctor (hi : FirstOrderThickening i) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj (idealOverThickened hi)

/-- **The action of the square-zero ideal**, as a natural transformation from tensoring with the
ideal to the identity: on local pure tensors it is multiplication of a section of the module by
the section of the structure sheaf underlying a section of the ideal. -/
noncomputable def idealAction (hi : FirstOrderThickening i) :
    idealTensorFunctor hi ⟶
      𝟭 (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) where
  app M := multiplicationMap i.fSharp hi.I M hi.incl
  naturality _ _ α := (multiplicationMap_natural i.fSharp hi.I hi.incl α).symm

/-- Tensoring with the square-zero ideal of a first order thickening preserves finite colimits. -/
instance preservesFiniteColimits_idealTensorFunctor (hi : FirstOrderThickening i) :
    PreservesFiniteColimits (idealTensorFunctor hi) := by
  have : PreservesColimitsOfSize.{0, 0} (idealTensorFunctor hi) :=
    preservesColimitsOfSize_shrink.{0, w, 0, w} _
  exact ⟨fun _ _ _ => inferInstance⟩

/-- Tensoring with the square-zero ideal of a first order thickening is an additive functor. -/
instance additive_idealTensorFunctor (hi : FirstOrderThickening i) :
    (idealTensorFunctor hi).Additive :=
  Stacks.SheafOfModules.FlatSquareZero.tensorLeft_additive Y.O (idealOverThickened hi)

section Cokernel

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] pullbackModules_additive

/-- **The unit of the adjunction kills the action of the square-zero ideal.** The action lands in
the ideal product, which the unit kills. -/
theorem idealAction_comp_unit (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (idealAction hi).app M ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app M = 0 :=
  Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_comp_eq_zero i.fSharp hi.I M hi.incl
    _ (idealProductSubmodule_unit_comp_zero hi M)

/-- **The unit of the adjunction is a cokernel of the action of the square-zero ideal.** It is a
cokernel of the inclusion of the ideal product by
`Deformation.ToposThickening.idealProductShortComplex_shortExact`, and a morphism out of `M`
kills that inclusion exactly when it kills the action. -/
noncomputable def unitIsCokernelIdealAction (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    IsColimit (CokernelCofork.ofπ
      (i.pullbackAdjPushforwardModulesViaComparison.unit.app M)
      (idealAction_comp_unit hi M)) :=
  letI := hi.abelian
  Stacks.SheafOfModules.FlatSquareZero.cokernelCofork_multiplicationMap_isColimit
    i.fSharp hi.I M hi.incl _ (idealProductSubmodule_unit_comp_zero hi M)
    (idealProductShortComplex_shortExact hi M).gIsCokernel (idealAction_comp_unit hi M)

/-- **The square-zero ideal acts by zero on a direct image.** The unit of the adjunction is a
monomorphism there and it kills the action. -/
theorem idealAction_app_eq_zero (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    [IsIso (i.pullbackAdjPushforwardModulesViaComparison.unit.app M)] :
    (idealAction hi).app M = 0 :=
  (cancel_mono (i.pullbackAdjPushforwardModulesViaComparison.unit.app M)).1
    ((idealAction_comp_unit hi M).trans zero_comp.symm)

/-- **A short exact sequence whose first term is a direct image and whose last term carries an
injective ideal action stays short exact after pullback.** The only thing to check is that the
pullback of the first map is still a monomorphism: by full faithfulness of the direct image that
is the monomorphy of `X₁ ⟶ X₂ ⟶ i_*i^*X₂`, which is
`Deformation.ToposThickening.mono_comp_of_cokernel_action` applied to the ideal action. -/
theorem shortExact_map_pullbackModules (hi : FirstOrderThickening i)
    (S : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hS : S.ShortExact)
    [IsIso (i.pullbackAdjPushforwardModulesViaComparison.unit.app S.X₁)]
    [Mono ((idealAction hi).app S.X₃)] :
    (S.map (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      i.toRingedToposModulesHom)).ShortExact := by
  let := hi.abelian
  let L := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    i.toRingedToposModulesHom
  let R := i.pushforwardModules
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let ff := (AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  let : R.Faithful := ff.faithful
  let := adj.leftAdjoint_preservesColimits
  let : Mono (S.f ≫ adj.unit.app S.X₂) :=
    mono_comp_of_cokernel_action (idealTensorFunctor hi) (idealAction hi) S hS
      (idealAction_app_eq_zero hi S.X₁) _
      (idealAction_comp_unit hi S.X₂) (unitIsCokernelIdealAction hi S.X₂)
  have hnat : adj.unit.app S.X₁ ≫ R.map (L.map S.f) = S.f ≫ adj.unit.app S.X₂ :=
    (adj.unit.naturality S.f).symm
  let : Mono (R.map (L.map S.f)) := by
    rw [← mono_comp_iff_of_isIso (adj.unit.app S.X₁), hnat]
    infer_instance
  let : Mono (L.map S.f) := R.mono_of_mono_map inferInstance
  have := hS.epi_g
  exact ShortComplex.ShortExact.mk'
    (hS.exact.map_of_epi_of_preservesCokernel L inferInstance inferInstance)
    (inferInstanceAs (Mono (L.map S.f))) (inferInstanceAs (Epi (L.map S.g)))

end Cokernel

end IdealAction

section Relative

open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify X'.J AddCommGrpCat.{w}]

/-- **The consequence of Stacks 08MQ that the proof of Stacks 08MT consumes for the source
module**, carried as a hypothesis: granting that the square is strict and that `ℱ'` is flat over
`O_{ℬ'}`, which are the hypotheses of 08MQ, the action `I ⊗_{O'} ℱ' ⟶ ℱ'` of the square-zero
ideal is injective. This is the final assertion of 08MQ, that the second factor
`I ⊗_O ℱ ⟶ I·ℱ'` of its canonical map is an isomorphism, read as the injectivity of the ideal
action. -/
def IsIdealActionMono (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) : Prop :=
  (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict →
    AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
            f'.fSharpInverseImage)).obj F') →
      Mono ((idealAction hi).app F')

/-- **Stacks 08MT.** Let `(f, f')` be a strict morphism of first order thickenings of ringed
topoi as in Situation 08M7, let `ℱ'` and `𝒢'` be `O'`-modules flat over `O_{ℬ'}`, set
`ℱ = i^*ℱ'` and `𝒢 = i^*𝒢'`, and let `φ : ℱ ⟶ 𝒢` be an `O`-linear map. There is an element
`o(φ)` of `Ext¹_O(ℱ, f^*𝒥 ⊗_O 𝒢)` whose vanishing is necessary and sufficient for `φ` to lift to
an `O'`-linear map `φ' : ℱ' ⟶ 𝒢'`.

The class is the Ext class of the sequence obtained by pulling the defining sequence
`0 ⟶ I·𝒢' ⟶ 𝒢' ⟶ i_*𝒢 ⟶ 0` of `𝒢'` back along the adjoint transpose of `φ` and then applying
`i^*`: a retraction of that sequence is exactly a lift of `φ`, and exactness after `i^*` is
where flatness of `ℱ'` enters. Stacks 08MQ enters twice and only through its final assertion,
once for `ℱ'` and once for `𝒢'`. The second of the two is supplied by
`Deformation.ToposThickening.isIdealProductTensorIso` and is not a hypothesis; the first is
carried as the hypothesis `Deformation.ToposThickening.IsIdealActionMono`, which is discharged
downstream by `Deformation.ToposThickening.exists_relativeModuleMapObstruction`.

The coefficient module `𝒢 ⊗_O f^*𝒥` is the source's, with `f^*𝒥` the `O`-module
`Deformation.ToposThickening.basePullbackIdeal`. -/
theorem relativeModuleMapObstruction (i : RingedToposHom X X') (t : RingedToposHom S S')
    (f : RingedToposHom X S) (f' : RingedToposHom X' S') (hi : FirstOrderThickening i)
    (ht : FirstOrderThickening t) (comm : f'.comp i = t.comp f)
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
    [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj G'))
    (hMQF : IsIdealActionMono i t f f' hi ht comm F')
    (φ : (pullbackModules i.toRingedToposModulesHom).obj F' ⟶
      (pullbackModules i.toRingedToposModulesHom).obj G') :
    ∃ o : Abelian.Ext.{e} ((pullbackModules i.toRingedToposModulesHom).obj F')
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
            (basePullbackIdeal t f ht)).obj
          ((pullbackModules i.toRingedToposModulesHom).obj G')) 1,
      o = 0 ↔ Nonempty (ModuleMapLift F' G' φ) := by
  let L := pullbackModules i.toRingedToposModulesHom
  let R := i.pushforwardModules
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  let ff := (ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  let : R.Faithful := ff.faithful
  let : R.Full := ff.full
  let Ki := (idealProductModule hi G').val
  let eG : R.obj Ki ≅ (idealProductSubmodule hi G').toSheafOfModules :=
    (idealProductModule hi G').property.some
  let κ := (isIdealProductTensorIso i t f f' hi ht comm G' hstrict hG).some
  -- the defining sequence `0 ⟶ I·𝒢' ⟶ 𝒢' ⟶ i_*i^*𝒢' ⟶ 0`, with its first term read as the
  -- direct image of the descended ideal product
  have hSq := shortExact_isoComp_f (idealProductShortComplex_shortExact hi G') eG
  let u := adj.homEquiv F' (L.obj G') φ
  have hP := pullback_shortExact hSq u
  let : IsIso (adj.unit.app (R.obj Ki)) :=
    adj.isIso_unit_app_iff_mem_essImage.2 (R.obj_mem_essImage Ki)
  let : Mono ((idealAction hi).app F') := hMQF hstrict hF
  have hLP := shortExact_map_pullbackModules hi _ hP
  let : IsIso (adj.counit.app Ki) := inferInstance
  let ν := (Stacks.SheafOfModules.FlatSquareZero.tensorLeftIsoTensorRight X.O
    (basePullbackIdeal t f ht)).app (L.obj G')
  let ξ : L.obj (R.obj Ki) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj
        (basePullbackIdeal t f ht)).obj (L.obj G') :=
    asIso (adj.counit.app Ki) ≪≫ κ.symm ≪≫ ν
  refine ⟨hLP.extClass.comp (Abelian.Ext.mk₀ ξ.hom) (add_zero 1), ?_⟩
  rw [extClass_comp_mk₀_eq_zero_iff hLP ξ.hom]
  exact (exists_comp_eq_iso_iff_exists_retraction _ ξ).trans
    ((exists_retraction_map_iff adj _).trans
      ((pullback_retraction_iff hSq u).trans
        (nonempty_moduleMapLift_iff_exists_factorization F' G' φ).symm))

end Relative

end Deformation.ToposThickening

end
