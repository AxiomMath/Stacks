module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CechModulePairEquivalence
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasiCoherentModulesWithSection
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent modules on the simplicial scheme of a morphism with a section

Let `f : X ⟶ S` be a morphism of schemes and `(X/S)_•` the simplicial scheme of Stacks 024A.
This file proves Stacks 07TL: if `f` has a section, pullback is an equivalence between the
quasi-coherent `O_S`-modules and the quasi-coherent modules on the total Zariski site
`((X/S)_•)_Zar`; and the same holds, as the source's footnote says, if `f` has a section only
fpqc locally on `S`.

## Main definitions

* `AlgebraicGeometry.pullbackToSimplicialScheme`: the pullback of quasi-coherent `O_S`-modules to
  quasi-coherent modules on `((X/S)_•)_Zar`.

## Main results

* `AlgebraicGeometry.pullbackToSimplicialSchemeComponentIso`: the component in degree `n` of the
  pullback of `M` is the pullback of `M` along `(X/S)_n ⟶ S`, naturally in `M`.
* `AlgebraicGeometry.isEquivalence_pullbackToSimplicialScheme_of_section`: **Stacks 07TL.**
* `AlgebraicGeometry.isEquivalence_pullbackToSimplicialScheme_of_fpqcLocalSection`: **the
  footnote of Stacks 07TL.**

## Implementation notes

The pullback functor is the canonical descent functor of Stacks 023D for the one-element family
`{f}` (pullback along `f`, with its canonical descent datum) followed by the identification of
quasi-coherent descent data relative to `{f}` with quasi-coherent modules on `((X/S)_•)_Zar`
(`AlgebraicGeometry.SimplicialScheme.quasicoherentDescentDataEquivZariski`, which is Stacks 07TH
and 0D7M for `(X/S)_•`). That it is the pullback is
`AlgebraicGeometry.pullbackToSimplicialSchemeComponentIso`: a quasi-coherent module on
`((X/S)_•)_Zar` is determined by its components and transitions (Stacks 0D7M), and the component
in degree `n` is the pullback along the structure morphism. The equivalence with a section is
proved as in Stacks 0243 for the descent-data form
(`AlgebraicGeometry.isEquivalence_canonicalDescentFunctor_singleton_of_section`); the footnote's
form uses fpqc descent of quasi-coherent modules (Stacks 023R).

## References

* [Stacks Project, Tag 07TL](https://stacks.math.columbia.edu/tag/07TL)
* [Stacks Project, Tag 024A](https://stacks.math.columbia.edu/tag/024A)
* [Stacks Project, Tag 023R](https://stacks.math.columbia.edu/tag/023R)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry

open SimplicialScheme

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Pullback of quasi-coherent modules from `S` to the total Zariski site of `(X/S)_•`**: pull
back along `f` with the canonical descent datum relative to `{f}`, and read the quasi-coherent
descent datum as a quasi-coherent module on `((X/S)_•)_Zar`. Its component in degree `n` is the
pullback along `(X/S)_n ⟶ S` (`AlgebraicGeometry.pullbackToSimplicialSchemeComponentIso`). -/
def pullbackToSimplicialScheme :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      QuasicoherentZariskiModule (simplicialScheme f) :=
  canonicalDescentFunctor (PreZeroHypercover.singleton.{0} f).f ⋙
    (quasicoherentDescentDataEquivZariski f).functor

/-- The functor taking a pair to its module. -/
def pairModuleFunctor (Y : SimplicialObject Scheme.{u}) :
    (zariskiModuleFamily Y).Pair ⥤ (Y.obj (op ⦋0⦌)).Modules where
  obj A := A.obj
  map φ := φ.map

/-- The module of the pair of a quasi-coherent module on the total Zariski site is its component
in degree zero. -/
def quasicoherentToPairModuleIso (Y : SimplicialObject Scheme.{u}) :
    quasicoherentToPair Y ⋙ ObjectProperty.ι _ ⋙ pairModuleFunctor Y ≅
      ObjectProperty.ι _ ⋙ componentModule Y (op ⦋0⦌) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    simp only [Iso.refl_hom]
    rfl)

/-- The module of the pair of the descent datum of a quasi-coherent `O_S`-module `M` is
`pr^* f^* M`, for the vertex `pr : (X/S)_0 ⟶ X`. -/
def canonicalPairModuleIso :
    canonicalDescentFunctor (PreZeroHypercover.singleton.{0} f).f ⋙
        quasicoherentDescentDataToPair f ⋙ ObjectProperty.ι _ ⋙ pairModuleFunctor _ ≅
      ObjectProperty.ι _ ⋙ Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (proj f 0 0) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    simp only [Iso.refl_hom]
    rfl)

/-- **The component in degree zero of the pullback** of a quasi-coherent `O_S`-module `M` is
`pr^* f^* M`. -/
def pullbackToSimplicialSchemeComponentZeroIso :
    pullbackToSimplicialScheme f ⋙ ObjectProperty.ι _ ⋙ componentModule _ (op ⦋0⦌) ≅
      ObjectProperty.ι _ ⋙ Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (proj f 0 0) :=
  Functor.isoWhiskerLeft (canonicalDescentFunctor (PreZeroHypercover.singleton.{0} f).f ⋙
      quasicoherentDescentDataToPair f ⋙
        (quasicoherentEquivQuasicoherentPair (simplicialScheme f)).inverse)
      (quasicoherentToPairModuleIso (simplicialScheme f)).symm ≪≫
    Functor.isoWhiskerLeft (canonicalDescentFunctor (PreZeroHypercover.singleton.{0} f).f ⋙
        quasicoherentDescentDataToPair f)
      (Functor.isoWhiskerRight
        (quasicoherentEquivQuasicoherentPair (simplicialScheme f)).counitIso
        (ObjectProperty.ι _ ⋙ pairModuleFunctor _)) ≪≫
    canonicalPairModuleIso f

/-- A quasi-coherent module on the total Zariski site is cartesian. -/
theorem isCartesianModule_of_quasicoherent {Y : SimplicialObject Scheme.{u}}
    (N : QuasicoherentZariskiModule Y) : IsCartesianModule Y N.obj :=
  ((isQuasicoherentOnSite_iff_isCartesianModule_and_zero N.obj).1 N.property).1

/-- The transitions from degree zero of a quasi-coherent module on the total Zariski site, as a
natural isomorphism. -/
def componentTransitionIso (Y : SimplicialObject Scheme.{u}) (n : ℕ) :
    (ObjectProperty.ι _ ⋙ componentModule Y (op ⦋0⦌)) ⋙
        Scheme.Modules.pullback (Y.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op) ≅
      (ObjectProperty.ι (SheafOfModules.isQuasicoherentOnSite
        (Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos Y).O))) ⋙
          componentModule Y (op ⦋n⦌) :=
  NatIso.ofComponents
    (fun N => @asIso _ _ _ _
      (componentModuleTransition Y (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op N.obj)
      (isCartesianModule_of_quasicoherent N _))
    (fun g => componentModuleTransition_naturality _ g.hom)

/-- The vertex `0` of the degree-`n` part, followed by the structure morphism, is the structure
morphism of `(X/S)_n`. -/
theorem map_const_proj_comp (n : ℕ) :
    (simplicialScheme f).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op ≫ (proj f 0 0 ≫ f) =
      baseMap f n := by
  rw [← Category.assoc, map_proj, proj_comp]

/-- **The pullback is computed degreewise**: the component in degree `n` of the pullback of a
quasi-coherent `O_S`-module `M` to the total Zariski site of `(X/S)_•` is the pullback of `M`
along the structure morphism `(X/S)_n ⟶ S`, naturally in `M`. -/
@[stacks 07TL "the functor is pullback: its component in degree n is the pullback along \
the structure morphism (X/S)_n ⟶ S"]
def pullbackToSimplicialSchemeComponentIso (n : ℕ) :
    pullbackToSimplicialScheme f ⋙ ObjectProperty.ι _ ⋙ componentModule _ (op ⦋n⦌) ≅
      ObjectProperty.ι _ ⋙ Scheme.Modules.pullback (baseMap f n) :=
  Functor.isoWhiskerLeft (pullbackToSimplicialScheme f) (componentTransitionIso _ n).symm ≪≫
    Functor.isoWhiskerRight (pullbackToSimplicialSchemeComponentZeroIso f)
      (Scheme.Modules.pullback ((simplicialScheme f).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op)) ≪≫
    Functor.isoWhiskerLeft (ObjectProperty.ι _)
      (Functor.isoWhiskerRight (Scheme.Modules.pullbackComp (proj f 0 0) f)
          (Scheme.Modules.pullback
            ((simplicialScheme f).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op)) ≪≫
        Scheme.Modules.pullbackComp _ _ ≪≫ Scheme.Modules.pullbackCongr (map_const_proj_comp f n))

/-- Let `f : X ⟶ S` be a morphism of schemes with a section `σ`, and let `(X/S)_•` be the
simplicial scheme of Stacks 024A. Then pullback is an equivalence between the quasi-coherent
`O_S`-modules and the quasi-coherent modules on the total Zariski site `((X/S)_•)_Zar`. The
pullback functor is `AlgebraicGeometry.pullbackToSimplicialScheme`; its component in degree `n`
is the pullback along `(X/S)_n ⟶ S`
(`AlgebraicGeometry.pullbackToSimplicialSchemeComponentIso`). -/
@[stacks 07TL]
theorem isEquivalence_pullbackToSimplicialScheme_of_section (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    (pullbackToSimplicialScheme f).IsEquivalence := by
  have := isEquivalence_canonicalDescentFunctor_singleton_of_section f σ hσ
  unfold pullbackToSimplicialScheme
  infer_instance

/-- Pullback is an equivalence between the quasi-coherent `O_S`-modules and the quasi-coherent
modules on `((X/S)_•)_Zar` already when `f` has a section only fpqc locally on `S`: there is an
fpqc covering `{p_i : T_i ⟶ S}` and morphisms `s_i : T_i ⟶ X` with `s_i ≫ f = p_i`. -/
@[stacks 07TL "the footnote: it is enough that f have a section fpqc locally on S"]
theorem isEquivalence_pullbackToSimplicialScheme_of_fpqcLocalSection {I : Type*}
    {T : I → Scheme.{u}} (p : ∀ i, T i ⟶ S)
    (hp : Presieve.ofArrows T p ∈ Scheme.fpqcPrecoverage.{u} S)
    (s : ∀ i, T i ⟶ X) (hs : ∀ i, s i ≫ f = p i) :
    (pullbackToSimplicialScheme f).IsEquivalence := by
  have := isEquivalence_canonicalDescentFunctor_of_sieve_mem_fpqcTopology
    (sieve_ofArrows_singleton_mem_fpqcTopology_of_fpqcLocalSection f p hp s hs)
  unfold pullbackToSimplicialScheme
  infer_instance

/-- The equivalence of Stacks 07TL: quasi-coherent `O_S`-modules are the quasi-coherent modules on
`((X/S)_•)_Zar`, by pullback, when `f` has a section. -/
def quasicoherentEquivSimplicialSchemeOfSection (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      QuasicoherentZariskiModule (simplicialScheme f) :=
  have := isEquivalence_pullbackToSimplicialScheme_of_section f σ hσ
  (pullbackToSimplicialScheme f).asEquivalence

end AlgebraicGeometry
