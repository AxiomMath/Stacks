module

public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Descend

/-!
# Pushforward along an affine morphism is faithful on quasi-coherent modules

Let `f : X ⟶ Y` be an affine morphism of schemes. This file proves that pushforward along `f` is
faithful on quasi-coherent sheaves of modules, the faithfulness half of
[Stacks Project, Tag 01SB], and deduces that the counit of `pullback f ⊣ pushforward f` is an
epimorphism at every quasi-coherent module.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.hom_app_eq_of_opens_eq`: an equality of the actions of
  two morphisms of sheaves of modules on the sections over an open transports along an equality
  of opens.
* `Stacks.AlgebraicGeometry.ModuleLimits.affinePushforwardFaithful`: **pushforward along an
  affine morphism of schemes is faithful on quasi-coherent sheaves of modules.**
* `Stacks.AlgebraicGeometry.ModuleLimits.affineCounitEpi`: for an affine morphism, the counit of
  `pullback f ⊣ pushforward f` is an epimorphism at every quasi-coherent module.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_map`: a
  finitely presented module on the limit of a cofiltered diagram of quasi-compact
  quasi-separated schemes with affine transition morphisms is the pullback of a finitely
  presented module on some stage, given descent of morphisms ([Stacks Project, Tag 01ZR] (2)).
* `Stacks.AlgebraicGeometry.ModuleLimits.faithful_affineQuasicoherentPushforward`: the direct
  image over `f_* 𝒪_X`, restricted to quasi-coherent modules, is faithful.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- An equality of the actions of two morphisms of sheaves of modules on the sections over an
open transports along an equality of opens. -/
theorem hom_app_eq_of_opens_eq {X : Scheme.{u}} {F G : X.Modules} {χ χ' : F ⟶ G}
    {U V : X.Opens} (hUV : U = V) (h : χ.app V = χ'.app V) (a : Γ(F, U)) :
    χ.app U a = χ'.app U a := by
  subst hUV
  exact congrArg (fun k ↦ (ConcreteCategory.hom k) a) h

/-- **Pushforward along an affine morphism of schemes is faithful on quasi-coherent sheaves of
modules.** -/
theorem affinePushforwardFaithful : AffinePushforwardFaithful.{u} := by
  intro X Y f _ M N hM hN g h hgh
  let _ := hM
  let _ := hN
  let W : Y.affineOpens → X.Opens := fun V => f ⁻¹ᵁ V.1
  have hW : ∀ x : X, ∃ a, x ∈ W a := by
    intro x
    have hx : f.base x ∈ (⊤ : Y.Opens) := trivial
    rw [← AlgebraicGeometry.iSup_affineOpens_eq_top Y] at hx
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨V, hV⟩
  have hpush : ∀ V : Y.Opens, g.app (f ⁻¹ᵁ V) = h.app (f ⁻¹ᵁ V) := fun V ↦
    congrArg (fun k => Scheme.Modules.Hom.app k V) hgh
  refine hom_ext_of_restrict_cover W hW fun a ↦ ?_
  have hWa : IsAffineOpen (W a) := IsAffineHom.isAffine_preimage _ a.2
  have : IsAffine (W a).toScheme := hWa
  have hMq : (M.restrict (W a).ι).IsQuasicoherent := inferInstance
  have hNq : (N.restrict (W a).ι).IsQuasicoherent := inferInstance
  exact hom_ext_of_app_top fun m ↦
    hom_app_eq_of_opens_eq (Scheme.Opens.ι_image_top (W a)) (hpush a.1) m

/-- For an affine morphism of schemes, the counit of `pullback f ⊣ pushforward f` is an
epimorphism at every quasi-coherent module. -/
theorem affineCounitEpi : AffineCounitEpi.{u} :=
  affineCounitEpi_of_affinePushforwardFaithful affinePushforwardFaithful

/-! ### Finitely presented modules on a limit -/

section Residue

variable {I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition morphisms and `c` a limit cone on it. If morphisms between pullbacks of finitely
presented modules descend to some stage, compatibly through the canonical comparisons
`pullbackComp` and `pullbackCongr` (`hmap`, [Stacks Project, Tag 01ZR] (2)), then every finitely
presented module on `c.pt` is isomorphic to the pullback of a finitely presented module on some
stage ([Stacks Project, Tag 01ZR] (1)). -/
theorem exists_isFinitePresentation_pullback_iso_of_map
    [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hmap : ∀ (i : I) (F G : (D.obj i).Modules),
      F.IsFinitePresentation → G.IsFinitePresentation →
      ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj G,
      ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
        (Scheme.Modules.pullback (c.π.app j)).map φj ≫
            (pullbackComp (c.π.app j) (D.map e)).hom.app G ≫
            (pullbackCongr (c.w e)).hom.app G =
          (pullbackComp (c.π.app j) (D.map e)).hom.app F ≫
            (pullbackCongr (c.w e)).hom.app F ≫ φ)
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) :=
  exists_isFinitePresentation_pullback_iso_of_inputs D c hc affineCounitEpi hmap F

end Residue

/-! ### The restricted direct image is faithful -/

/-- For an affine morphism `f : X ⟶ S`, the direct image over `f_* 𝒪_X`, restricted to
quasi-coherent modules (`AffineQcohEquivalence.affineQuasicoherentPushforward f`), is faithful. -/
instance faithful_affineQuasicoherentPushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] :
    (AffineQcohEquivalence.affineQuasicoherentPushforward f).Faithful where
  map_injective {M N} g h hgh := by
    have h1 : ((AffineQcohEquivalence.affineQuasicoherentPushforward f).map g).hom
        = ((AffineQcohEquivalence.affineQuasicoherentPushforward f).map h).hom := by rw [hgh]
    exact CategoryTheory.ObjectProperty.hom_ext _
      (affinePushforwardFaithful.{u} f M.property N.property g.hom h.hom
        (congrArg (SheafOfModules.restrictScalars f.toRingCatSheafHom).map h1))

end Stacks.AlgebraicGeometry.ModuleLimits

end
