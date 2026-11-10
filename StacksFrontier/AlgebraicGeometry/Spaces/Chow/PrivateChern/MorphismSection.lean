module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleDual
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFactorizationInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemePullback

/-!
# The section of `𝒜^{-1} ⊗ ℳ` attached to a morphism `𝒜 ⟶ ℳ` out of an invertible module

Let `Z` be an algebraic space, `𝒜` an invertible `𝒪_Z`-module and `s : 𝒜 ⟶ ℳ` a morphism of
`𝒪_Z`-modules. Tensoring by `𝒜` is an equivalence, so `s` is the tensor product of `𝒜` with a
unique morphism `a : 𝒪_Z ⟶ 𝒜^{-1} ⊗ ℳ`, read through the cancellation `𝒜 ⊗ (𝒜^{-1} ⊗ ℳ) ≅ ℳ`:

  `(𝒜 ◁ a) ≫ cancel = ρ ≫ s`.

The morphism `a` is a global section `σ` of `𝒩 = 𝒜^{-1} ⊗ ℳ`, and `𝒜 ⊗ 𝒩 ≅ ℳ`; for `ℳ`
invertible, `𝒩` is invertible. On the projective bundle `π : 𝐏(ℰ) ⟶ X` of a module `ℰ` with an
invertible submodule `ℒ ⊆ ℰ`, applied to `π^*ℒ ⟶ π^*ℰ ⟶ 𝒪(1)`, this is the section of
`𝒪(1) ⊗ π^*ℒ^{-1}` of the proof of Stacks 0ES8.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.morphismSectionModule`: `𝒜^{-1} ⊗ ℳ`.
* `AlgebraicGeometry.Space.PrivateChern.morphismSectionHom`: the morphism `a : 𝒪_Z ⟶ 𝒜^{-1} ⊗ ℳ`.
* `AlgebraicGeometry.Space.PrivateChern.morphismSection`: the global section `σ`.
* `AlgebraicGeometry.Space.PrivateChern.morphismSectionTensorIso`: `𝒜 ⊗ (𝒜^{-1} ⊗ ℳ) ≅ ℳ`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.whiskerLeft_morphismSectionHom`:
  `(𝒜 ◁ a) ≫ cancel = ρ ≫ s`.
* `AlgebraicGeometry.Space.PrivateChern.isInvertibleModule_morphismSectionModule`: `𝒜^{-1} ⊗ ℳ`
  is invertible for invertible `ℳ`.
* `AlgebraicGeometry.Space.PrivateChern.modulePullback_map_morphismSectionHom_eq_zero_iff`: after
  the inverse image along any `g : T ⟶ Z`, `g^*a` vanishes exactly when `g^*s` does.
* `AlgebraicGeometry.Space.PrivateChern.exists_comp_eq_zeroScheme_morphismSection_iff`: a morphism
  `g : T ⟶ Z` factors through the zero scheme `Z(σ)` exactly when `g^*s = 0`, for `ℳ` invertible.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Z : AlgebraicSpaces B S hS}
  {A : Modules.{u, u} B S hS Z.1 Z.2} (hA : IsInvertibleModule Z A)
  (M : Modules.{u, u} B S hS Z.1 Z.2)

/-- **The module `𝒜^{-1} ⊗ ℳ`** for an invertible `𝒜`. -/
def morphismSectionModule : Modules.{u, u} B S hS Z.1 Z.2 :=
  hA.hasInverse.inv ⊗ M

/-- The cancellation `𝒜 ⊗ (𝒜^{-1} ⊗ ℳ) ≅ ℳ`. -/
def morphismSectionTensorIso : A ⊗ morphismSectionModule hA M ≅ M :=
  hA.hasInverse.tensorCancel M

/-- `𝒜^{-1} ⊗ ℳ` is invertible when `ℳ` is. -/
theorem isInvertibleModule_morphismSectionModule (hM : IsInvertibleModule Z M) :
    IsInvertibleModule Z (morphismSectionModule hA M) :=
  Stacks.SheafOfModules.isInvertible_of_hasInverse (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)
    (hA.hasInverse.hasInverseInv.tensor hM.hasInverse)

variable {M} (s : A ⟶ M)

/-- **The morphism `a : 𝒪_Z ⟶ 𝒜^{-1} ⊗ ℳ` attached to `s : 𝒜 ⟶ ℳ`**, the preimage of `s` under
tensoring by `𝒜`. -/
def morphismSectionHom : 𝟙_ (Modules.{u, u} B S hS Z.1 Z.2) ⟶ morphismSectionModule hA M :=
  (hA.hasInverse.exists_whiskerLeft_tensorCancel s).choose

/-- `(𝒜 ◁ a) ≫ cancel = ρ ≫ s`. -/
theorem whiskerLeft_morphismSectionHom :
    A ◁ morphismSectionHom hA s ≫ (morphismSectionTensorIso hA M).hom = (ρ_ A).hom ≫ s :=
  (hA.hasInverse.exists_whiskerLeft_tensorCancel s).choose_spec

/-- **The global section of `𝒜^{-1} ⊗ ℳ` attached to `s : 𝒜 ⟶ ℳ`.** -/
def morphismSection : (morphismSectionModule hA M).sections :=
  SheafOfModules.unitHomEquiv _ (morphismSectionHom hA s)

/-- **The inverse image of `a` vanishes exactly when that of `s` does**: for every morphism
`g : T ⟶ Z`, `g^*a = 0 ↔ g^*s = 0`, since `g^*` is monoidal and tensoring by the invertible
`g^*𝒜` is an equivalence. -/
theorem modulePullback_map_morphismSectionHom_eq_zero_iff {T : AlgebraicSpaces B S hS}
    (g : T ⟶ Z) :
    (modulePullback B S hS g).map (morphismSectionHom hA s) = 0 ↔
      (modulePullback B S hS g).map s = 0 := by
  let := modulePullbackMonoidal g
  have := preservesZeroMorphisms_modulePullback B S hS g
  set F := modulePullback B S hS g
  have hFA : HasInverse (F.obj A) := (modulePullbackInvertible g A hA).hasInverse
  have : (tensorLeft (F.obj A)).IsEquivalence := hFA.tensorLeftEquivalence.isEquivalence_functor
  have h1 : F.map (A ◁ morphismSectionHom hA s) =
      Functor.OplaxMonoidal.δ F A _ ≫ F.obj A ◁ F.map (morphismSectionHom hA s) ≫
        Functor.LaxMonoidal.μ F A _ :=
    Functor.Monoidal.map_whiskerLeft F A _
  have h2 : F.map (A ◁ morphismSectionHom hA s) ≫ F.map (morphismSectionTensorIso hA M).hom =
      F.map (ρ_ A).hom ≫ F.map s := by
    rw [← F.map_comp, ← F.map_comp, whiskerLeft_morphismSectionHom]
  constructor
  · intro h
    have h' : F.map (A ◁ morphismSectionHom hA s) = 0 := by
      rw [h1, h]
      change Functor.OplaxMonoidal.δ F A _ ≫
        (tensorLeft (F.obj A)).map (0 : F.obj (𝟙_ _) ⟶ F.obj (morphismSectionModule hA M)) ≫
          Functor.LaxMonoidal.μ F A _ = 0
      rw [Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
    rw [h', Limits.zero_comp] at h2
    have h5 := congrArg (fun k => F.map (ρ_ A).inv ≫ k) h2
    simp only [Limits.comp_zero] at h5
    rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp] at h5
    exact h5.symm
  · intro h
    rw [h, Limits.comp_zero] at h2
    have h3 : F.map (A ◁ morphismSectionHom hA s) = 0 := by
      have h6 := congrArg (fun k => k ≫ F.map (morphismSectionTensorIso hA M).inv) h2
      simp only [Limits.zero_comp, Category.assoc] at h6
      rwa [← F.map_comp, Iso.hom_inv_id, F.map_id, Category.comp_id] at h6
    rw [h1] at h3
    have h4 : (tensorLeft (F.obj A)).map (F.map (morphismSectionHom hA s)) = 0 := by
      change F.obj A ◁ F.map (morphismSectionHom hA s) = 0
      have := congrArg (fun k => Functor.LaxMonoidal.μ F A _ ≫ k ≫
        Functor.OplaxMonoidal.δ F A _) h3
      simpa only [Category.assoc, Functor.Monoidal.μ_δ, Functor.Monoidal.μ_δ_assoc,
        Category.comp_id, Limits.zero_comp, Limits.comp_zero] using this
    exact (Functor.map_eq_zero_iff (tensorLeft (F.obj A))).1 h4

/-- The morphism `𝒪_Z ⟶ 𝒜^{-1} ⊗ ℳ` corresponding to the global section `σ` is `a`. -/
theorem unitHomEquiv_symm_morphismSection :
    (SheafOfModules.unitHomEquiv _).symm (morphismSection hA s) = morphismSectionHom hA s :=
  (SheafOfModules.unitHomEquiv _).symm_apply_apply _

/-- The inverse image of `σ` vanishes exactly when that of `s` does. -/
theorem modulePullbackSections_morphismSection_eq_zero_iff {T : AlgebraicSpaces B S hS}
    (g : T ⟶ Z) :
    modulePullbackSections B S hS g _ (morphismSection hA s) = 0 ↔
      (modulePullback B S hS g).map s = 0 := by
  rw [← modulePullback_map_morphismSectionHom_eq_zero_iff hA s g]
  unfold modulePullbackSections
  rw [unitHomEquiv_symm_morphismSection]
  have h0 : ∀ {M' : Modules.{u, u} B S hS T.1 T.2},
      SheafOfModules.unitHomEquiv M' 0 = 0 := fun {M'} =>
    Subtype.ext (funext fun X => rfl)
  constructor
  · intro h
    have h' := (SheafOfModules.unitHomEquiv _).injective (h.trans h0.symm)
    have h'' := congrArg (fun k => (modulePullbackUnitIso B S hS g).hom ≫ k) h'
    simp only [Iso.hom_inv_id_assoc, Limits.comp_zero] at h''
    exact h''
  · intro h
    have h' : (modulePullbackUnitIso B S hS g).inv ≫
        (modulePullback B S hS g).map (morphismSectionHom hA s) = 0 := by
      convert Limits.comp_zero (f := (modulePullbackUnitIso B S hS g).inv) using 2
      exact h
    exact (congrArg (SheafOfModules.unitHomEquiv _) h').trans h0

/-- **A morphism factors through the zero scheme of `σ` exactly when the inverse image of `s`
vanishes**, for `ℳ` invertible. -/
theorem exists_comp_eq_zeroScheme_morphismSection_iff (hM : IsInvertibleModule Z M)
    {T : AlgebraicSpaces B S hS} (g : T ⟶ Z) :
    (∃ h : T ⟶ (⟨(zeroScheme B S hS Z (morphismSectionModule hA M)
        (morphismSection hA s)).1.toFunctor,
        (zeroScheme B S hS Z _ (morphismSection hA s)).2.1⟩ : AlgebraicSpaces B S hS),
      h ≫ ObjectProperty.homMk (zeroScheme B S hS Z _ (morphismSection hA s)).1.ι = g) ↔
      (modulePullback B S hS g).map s = 0 :=
  (modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme B S hS Z T _
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
      (isInvertibleModule_morphismSectionModule hA M hM)) _ g).symm.trans
    (modulePullbackSections_morphismSection_eq_zero_iff hA s g)

end AlgebraicGeometry.Space.PrivateChern

end
