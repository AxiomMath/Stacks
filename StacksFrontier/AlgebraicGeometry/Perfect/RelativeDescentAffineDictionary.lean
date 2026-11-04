module

public import StacksFrontier.AlgebraicGeometry.Perfect.AffinePullbackComparisonCocycle
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard

/-!
# The affine dictionary of Stacks 0DI7 is natural

Over a spectrum, derived morphism sets between derived pullbacks of sheafified complexes are
identified with derived morphism sets over the ring through the affine comparison square of
Stacks 08DW and Stacks 06Z0. This file shows that these identifications commute with the maps
induced by further derived pullback and by further derived extension of scalars; the input is
the composition cocycle `AlgebraicGeometry.StandardModel.cmp_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.StandardModel

section Spec

variable {R₀ R R' : CommRingCat.{u}} (g : R₀ ⟶ R) (t : R ⟶ R')

/-- The affine comparison square of Stacks 08DW at an object, as an isomorphism. -/
def cmpIso (M : DerivedCategory (ModuleCat.{u} R₀)) :
    (dpb (Spec.map g)).obj ((tilde.functor R₀).mapDerivedCategory.obj M) ≅
      (tilde.functor R).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj M) :=
  (affinePullbackComparison R₀ R g).app M

/-- The forward morphism of `cmpIso g M` is `cmp g M`. -/
theorem cmpIso_hom (M : DerivedCategory (ModuleCat.{u} R₀)) : (cmpIso g M).hom = cmp g M := rfl

/-- The composition isomorphism of Stacks 0D5S along `Spec R' ⟶ Spec R ⟶ Spec R₀`, at an
object, for a ring map `g'` equal to `g ≫ t`. -/
def fcompIso (g' : R₀ ⟶ R') (ht : g ≫ t = g') (X : DerivedCategory (Spec R₀).Modules) :
    (dpb (Spec.map t)).obj ((dpb (Spec.map g)).obj X) ≅ (dpb (Spec.map g')).obj X :=
  (Stacks.DerivedPullback.schemeFactorIso (Spec.map t) (Spec.map g) (Spec.map g')
    (by rw [← ht, Spec.map_comp])).app X

/-- For `g' = g ≫ t`, the forward morphism of `fcompIso` is `fcomp g t X`. -/
theorem fcompIso_hom (X : DerivedCategory (Spec R₀).Modules) :
    (fcompIso g t (g ≫ t) rfl X).hom = fcomp g t X := rfl

/-- The composition isomorphism of derived extension of scalars at an object, for a ring map
`g'` equal to `g ≫ t`. -/
def extCompIso (g' : R₀ ⟶ R') (ht : g ≫ t = g') (M : DerivedCategory (ModuleCat.{u} R₀)) :
    (totalDerivedExtensionScalars.{u, u, u} t.hom).functor.obj
        ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj M) ≅
      (totalDerivedExtensionScalars.{u, u, u} g'.hom).functor.obj M :=
  (PseudoCoherence.derivedExtensionScalarsComp.{u, u} g.hom t.hom ≪≫
    PseudoCoherence.derivedExtensionScalarsCongr.{u, u} (congrArg CommRingCat.Hom.hom ht)).app M

/-- For `g' = g ≫ t`, the forward morphism of `extCompIso` is `extComp g t M`. -/
theorem extCompIso_hom (M : DerivedCategory (ModuleCat.{u} R₀)) :
    (extCompIso g t (g ≫ t) rfl M).hom = extComp g t M := by
  simp [extCompIso, extComp, PseudoCoherence.derivedExtensionScalarsCongr]

variable {X Y : DerivedCategory (Spec R₀).Modules} {𝕂 𝕃 : DerivedCategory (ModuleCat.{u} R₀)}
  (eX : X ≅ (tilde.functor R₀).mapDerivedCategory.obj 𝕂)
  (eY : Y ≅ (tilde.functor R₀).mapDerivedCategory.obj 𝕃)

/-- The derived pullback along `Spec g` of an object identified with a sheafification is the
sheafification of the derived extension of scalars. -/
def specStageIso {X : DerivedCategory (Spec R₀).Modules} {𝕂 : DerivedCategory (ModuleCat.{u} R₀)}
    (eX : X ≅ (tilde.functor R₀).mapDerivedCategory.obj 𝕂) :
    (dpb (Spec.map g)).obj X ≅
      (tilde.functor R).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj 𝕂) :=
  (dpb (Spec.map g)).mapIso eX ≪≫ cmpIso g 𝕂

/-- The identification of derived morphism sets over `Spec R` with derived morphism sets over
`R`. -/
def specStageHom :
    ((dpb (Spec.map g)).obj X ⟶ (dpb (Spec.map g)).obj Y) ≃
      ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj 𝕂 ⟶
        (totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj 𝕃) :=
  ((specStageIso g eX).homCongr (specStageIso g eY)).trans (homEquiv R _ _)

/-- The sheafification of `specStageHom g eX eY φ` is `φ` conjugated by `specStageIso g eX` and
`specStageIso g eY`. -/
theorem tilde_map_specStageHom (φ : (dpb (Spec.map g)).obj X ⟶ (dpb (Spec.map g)).obj Y) :
    (tilde.functor R).mapDerivedCategory.map (specStageHom g eX eY φ) =
      (specStageIso g eX).inv ≫ φ ≫ (specStageIso g eY).hom :=
  (mapDerivedCategoryFullyFaithful R).map_preimage _

/-- The composite of `specStageIso` with the composition isomorphism of Stacks 0D5S. -/
theorem specStageIso_comp :
    fcompIso g t (g ≫ t) rfl X ≪≫ specStageIso (g ≫ t) eX =
      (dpb (Spec.map t)).mapIso (specStageIso g eX) ≪≫
        cmpIso t ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj 𝕂) ≪≫
        (tilde.functor R').mapDerivedCategory.mapIso (extCompIso g t (g ≫ t) rfl 𝕂) := by
  refine Iso.ext ?_
  simp only [specStageIso, Iso.trans_hom, Functor.mapIso_hom, fcompIso_hom, cmpIso_hom,
    extCompIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% fcomp_naturality, cmp_comp]

/-- **The identification of `specStageHom` is natural along a further ring map.** The map on
derived morphism sets induced by derived pullback along `Spec t` corresponds to derived
extension of scalars along `t`, read through the composition isomorphism of derived extension
of scalars. -/
theorem specStageHom_transition (g' : R₀ ⟶ R') (ht : g ≫ t = g')
    (φ : (dpb (Spec.map g)).obj X ⟶ (dpb (Spec.map g)).obj Y) :
    specStageHom g' eX eY
        ((fcompIso g t g' ht X).homCongr (fcompIso g t g' ht Y) ((dpb (Spec.map t)).map φ)) =
      (extCompIso g t g' ht 𝕂).homCongr (extCompIso g t g' ht 𝕃)
        ((totalDerivedExtensionScalars.{u, u, u} t.hom).functor.map (specStageHom g eX eY φ)) := by
  subst ht
  apply (mapDerivedCategoryFullyFaithful R').map_injective
  have hX := specStageIso_comp g t eX
  have hY := specStageIso_comp g t eY
  have hn : (tilde.functor R').mapDerivedCategory.map
      ((totalDerivedExtensionScalars.{u, u, u} t.hom).functor.map (specStageHom g eX eY φ)) =
      (cmpIso t _).inv ≫ (dpb (Spec.map t)).map
        ((tilde.functor R).mapDerivedCategory.map (specStageHom g eX eY φ)) ≫
        (cmpIso t _).hom := by
    rw [Iso.eq_inv_comp, cmpIso_hom, cmpIso_hom, cmp_naturality]
  have e1 : (specStageIso (g ≫ t) eX).inv ≫
      ((fcompIso g t (g ≫ t) rfl X).inv ≫ (dpb (Spec.map t)).map φ ≫
        (fcompIso g t (g ≫ t) rfl Y).hom) ≫ (specStageIso (g ≫ t) eY).hom =
      (fcompIso g t (g ≫ t) rfl X ≪≫ specStageIso (g ≫ t) eX).inv ≫ (dpb (Spec.map t)).map φ ≫
        (fcompIso g t (g ≫ t) rfl Y ≪≫ specStageIso (g ≫ t) eY).hom := by
    simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [tilde_map_specStageHom, Iso.homCongr_apply, Iso.homCongr_apply, e1, hX, hY, Functor.map_comp,
    Functor.map_comp, hn, tilde_map_specStageHom]
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]

end Spec

section Schemes

variable {Z W W' : Scheme.{u}} {R₀ R R' : CommRingCat.{u}} (ε₀ : Z ≅ Spec R₀) (ε : W ≅ Spec R)
  (ε' : W' ≅ Spec R') (f : W ⟶ Z) (f' : W' ⟶ Z) (g : R₀ ⟶ R) (g' : R₀ ⟶ R')
  (h : ε.inv ≫ f = Spec.map g ≫ ε₀.inv) (h' : ε'.inv ≫ f' = Spec.map g' ≫ ε₀.inv)
  {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))}
  {𝕂 𝕃 : DerivedCategory (ModuleCat.{u} R₀)}
  (eK : (derivedPullback ε₀.inv.toLRSHom.toShHom).obj K ≅
    (tilde.functor R₀).mapDerivedCategory.obj 𝕂)
  (eL : (derivedPullback ε₀.inv.toLRSHom.toShHom).obj L ≅
    (tilde.functor R₀).mapDerivedCategory.obj 𝕃)

/-- **The affine dictionary at a stage.** For `f : W ⟶ Z` sitting over `Spec g` through the
isomorphisms `ε : W ≅ Spec R` and `ε₀ : Z ≅ Spec R₀`, and objects `K`, `L` of `D(𝒪_Z)` whose
transports to `Spec R₀` are the sheafifications of `𝕂`, `𝕃`, the derived morphism sets
`Hom(Lf^*K, Lf^*L)` are `Hom(R ⊗ᴸ 𝕂, R ⊗ᴸ 𝕃)`. -/
def stageDictionary :
    ((derivedPullback f.toLRSHom.toShHom).obj K ⟶ (derivedPullback f.toLRSHom.toShHom).obj L) ≃
      ((totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj 𝕂 ⟶
        (totalDerivedExtensionScalars.{u, u, u} g.hom).functor.obj 𝕃) :=
  (Equiv.ofBijective _ (Stacks.DerivedPullback.bijective_schemeFactorSquareHom ε.inv f (Spec.map g)
    ε₀.inv h ε.hom ε.inv_hom_id ε.hom_inv_id K L)).trans (specStageHom g eK eL)

/-- **The affine dictionary is natural.** A morphism `τ : W' ⟶ W` over `Z` whose transport to
spectra is `Spec t` for `t : R ⟶ R'` with `g ≫ t = g'` induces, on derived morphism sets, the map
which the dictionary identifies with derived extension of scalars along `t`. -/
theorem stageDictionary_naturality (τ : W' ⟶ W) (hτ : τ ≫ f = f') (t : R ⟶ R') (ht : g ≫ t = g')
    (hsr : Spec.map t ≫ ε.inv = ε'.inv ≫ τ)
    (φ : (derivedPullback f.toLRSHom.toShHom).obj K ⟶ (derivedPullback f.toLRSHom.toShHom).obj L) :
    stageDictionary ε₀ ε' f' g' h' eK eL (Stacks.DerivedPullback.schemeFactorHom τ f f' hτ K L φ) =
      (extCompIso g t g' ht 𝕂).homCongr (extCompIso g t g' ht 𝕃)
        ((totalDerivedExtensionScalars.{u, u, u} t.hom).functor.map
          (stageDictionary ε₀ ε f g h eK eL φ)) := by
  have hse : Spec.map t ≫ Spec.map g = Spec.map g' := by rw [← ht, Spec.map_comp]
  exact (congrArg (specStageHom g' eK eL)
    (Stacks.DerivedPullback.schemeFactorHom_schemeFactorSquareHom ε.inv f (Spec.map g) ε₀.inv
      (Spec.map t) τ ε'.inv f' (Spec.map g') h h' hse hτ hsr K L φ).symm).trans
    (specStageHom_transition g t eK eL g' ht _)

end Schemes

end AlgebraicGeometry.StandardModel

end
