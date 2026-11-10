module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkDiagram
public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPushStalkLocalRing
import all StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# The local rings of a cartesian square along a closed immersion

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion, and a point `w` of `Z'`.  The image point of `w` in `X` has two
presentations, `i (g w)` and `f (i' w)`.  This file records, at the presentation `f (i' w)` over
which the stalk of a pullback along `f` is computed, the two facts about the local rings of the
square that the stalks of Stacks 0E23 need.

## Main definitions

* `Stacks.Cohomology.ClosedImmersionBaseChange.pushforwardStalkIso`: the stalk of `i_* F` at a
  point equal to `i z` is the stalk of `F` at `z`, with scalars restricted.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.stalkCongr_transport`: a property of a pair of
  ring maps out of the stalk at a point passes to the stalk at an equal point.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_unit_app_restrictScalars_of_surjective`:
  along a surjective ring map the unit of extension and restriction of scalars is invertible at
  every restricted module.
* `Stacks.Cohomology.ClosedImmersionBaseChange.essImage_extendScalars_restrictScalars_stalk`:
  extending scalars from `𝒪_{X, f (i' w)}` to `𝒪_{X', i' w}` a module restricted from
  `𝒪_{Z, g w}` gives a module restricted from `𝒪_{Z', w}`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_comparison_restrictScalars_stalk`: under Tor
  independence, derived extension of scalars from `𝒪_{X, f (i' w)}` to `𝒪_{X', i' w}` is computed
  termwise on every complex restricted from a K-flat complex over `𝒪_{Z, g w}`.

## References

* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open scoped TensorProduct

noncomputable section

namespace Stacks.Cohomology.ClosedImmersionBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Transport between two equal points -/

section Transport

variable {Y : Scheme.{u}}

/-- **A property of ring maps out of a stalk passes to an equal point.**  For `h : a = b`, a
property of a pair of ring maps out of `𝒪_{Y,a}` whose second map factors through the comparison
`𝒪_{Y,a} ≅ 𝒪_{Y,b}` is a property of the pair out of `𝒪_{Y,b}` whose first map factors through
the inverse comparison. -/
theorem stalkCongr_transport {a b : Y} (h : a = b) {A B : CommRingCat.{u}}
    (P : ∀ c : Y, (Y.presheaf.stalk c ⟶ A) → (Y.presheaf.stalk c ⟶ B) → Prop)
    (ψ : Y.presheaf.stalk a ⟶ A) (φ : Y.presheaf.stalk b ⟶ B)
    (hP : P a ψ ((Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ φ)) :
    P b ((Y.presheaf.stalkCongr (Inseparable.of_eq h.symm)).hom ≫ ψ) φ := by
  subst h
  simpa only [stalkCongr_hom_eq_eqToHom, eqToHom_refl, Category.id_comp] using hP

end Transport

/-! ### Extension and restriction of scalars along a surjection -/

/-- **Along a surjective ring map, the unit of extension and restriction of scalars is invertible
at a restricted module.**  The unit `M ⟶ S ⊗_R M`, `m ↦ 1 ⊗ m`, is split by the counit, and it is
onto because every `s ⊗ m` is `ι r ⊗ m = 1 ⊗ r • m` for some `r`. -/
theorem isIso_unit_app_restrictScalars_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    (ι : R →+* S) (hι : Function.Surjective ι) (M : ModuleCat.{u} S) :
    IsIso ((ModuleCat.extendRestrictScalarsAdj ι).unit.app
      ((ModuleCat.restrictScalars ι).obj M)) := by
  have hmono : Mono ((ModuleCat.extendRestrictScalarsAdj ι).unit.app
      ((ModuleCat.restrictScalars ι).obj M)) :=
    (SplitMono.mk ((ModuleCat.restrictScalars ι).map
      ((ModuleCat.extendRestrictScalarsAdj ι).counit.app M))
      ((ModuleCat.extendRestrictScalarsAdj ι).right_triangle_components M)).mono
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(ModuleCat.mono_iff_injective _).1 hmono, fun x => ?_⟩
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    obtain ⟨r, rfl⟩ := hι s
    let : Module R S := Module.compHom S ι
    refine ⟨r • m, ?_⟩
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    congr 1
    exact mul_one (ι r)
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩

/-! ### The stalk of a pushforward along a closed immersion at a presented point -/

section Pushforward

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]

/-- **The stalk of a pushforward at a point equal to `i z`.**  For `h : a = i z`, the stalk of
`i_* F` at `a` is the stalk of `F` at `z` with scalars restricted along
`𝒪_{X,a} ≅ 𝒪_{X,i z} ⟶ 𝒪_{Z,z}`, naturally in `F`. -/
def pushforwardStalkIso {a : X} (z : Z) (h : a = i z) :
    Scheme.Modules.pushforward i ⋙ Stacks.ModuleSkyscraper.modulesStalkFunctor X a ≅
      Stacks.ModuleSkyscraper.modulesStalkFunctor Z z ⋙
        ModuleCat.restrictScalars.{u, u, u}
          ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ i.stalkMap z).hom :=
  have := isIso_pushStalkMap_of_isClosedImmersion i z
  Functor.isoWhiskerLeft (Scheme.Modules.pushforward i) (modulesStalkFunctorCongr h).symm ≪≫
    Functor.isoWhiskerRight (asIso (Stacks.ModuleSkyscraper.pushStalkMap i z))
      (ModuleCat.restrictScalars.{u, u, u} (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom) ≪≫
    Functor.isoWhiskerLeft (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z)
      (ModuleCat.restrictScalarsComp'.{u} (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom
        (i.stalkMap z).hom _ rfl).symm

end Pushforward

/-! ### The local rings of the square -/

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- The algebra structure on the target of a morphism of commutative rings. -/
private abbrev toAlgebraOfHom {A B : CommRingCat.{u}} (φ : A ⟶ B) : Algebra A B :=
  φ.hom.toAlgebra

/-- **The underived comparison of Stacks 065Z at the local rings is invertible.**  The four local
rings form a pushout square, so `𝒪_{X',i'w} ⊗_{𝒪_{X,i(gw)}} M ⟶ 𝒪_{Z',w} ⊗_{𝒪_{Z,gw}} M` is
bijective. -/
theorem isIso_stalkBaseChange_fst (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') (hpt : i (g w) = f (i' w)) :
    IsIso (derivedBaseChangeComparison.{u, u, u, u, u} (i.stalkMap (g w)).hom (ringRR' w hpt)
      (g.stalkMap w).hom (i'.stalkMap w).hom (stalkMap_ringHom_square sq w hpt)
      (Lg w hpt) (Lh w) (alphaG w hpt) (alphaH w)).1 := by
  let algRA := toAlgebraOfHom (i.stalkMap (g w))
  let algRR' :=
    toAlgebraOfHom ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w))
  let algRA' := toAlgebraOfHom
    ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w) ≫ i'.stalkMap w)
  let algAA' := toAlgebraOfHom (g.stalkMap w)
  let algR'A' := toAlgebraOfHom (i'.stalkMap w)
  have towerA : IsScalarTower (ToType (X.presheaf.stalk (i (g w))))
      (ToType (Z.presheaf.stalk (g w))) (ToType (Z'.presheaf.stalk w)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        ← Stacks.Cohomology.StalkPushout.stalkMap_comm_of_isPullback sq w hpt])
  have towerR' : IsScalarTower (ToType (X.presheaf.stalk (i (g w))))
      (ToType (X'.presheaf.stalk (i' w))) (ToType (Z'.presheaf.stalk w)) :=
    IsScalarTower.of_algebraMap_eq' (by
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Category.assoc])
  have hpush : Algebra.IsPushout (ToType (X.presheaf.stalk (i (g w))))
      (ToType (Z.presheaf.stalk (g w))) (ToType (X'.presheaf.stalk (i' w)))
      (ToType (Z'.presheaf.stalk w)) :=
    Stacks.Cohomology.StalkPushout.isPushout_stalkMap_toAlgebra_of_isPullback sq w hpt
  exact isIso_baseChange_of_isPushout.{u, u, u, u, u} _
    (derivedBaseChangeComparison_fst_app_tmul.{u, u, u, u, u} _ _ _ _ _ _ _ _ _)

/-- **Extension of scalars of a module restricted from `𝒪_{Z, g w}` is restricted from
`𝒪_{Z', w}`.**  Stated over the local ring `𝒪_{X, f (i' w)}`, the presentation of the image point
over which the stalk of a pullback along `f` is computed: for every `𝒪_{Z,gw}`-module `F₀`, the
module `𝒪_{X',i'w} ⊗_{𝒪_{X,f(i'w)}} F₀` is the restriction of an `𝒪_{Z',w}`-module along the germ
map of `i'`. -/
theorem essImage_extendScalars_restrictScalars_stalk (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') (hpt : i (g w) = f (i' w))
    (F₀ : ModuleCat.{u} (ToType (Z.presheaf.stalk (g w)))) :
    (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).essImage
      ((ModuleCat.extendScalars.{u, u, u} (f.stalkMap (i' w)).hom).obj
        ((ModuleCat.restrictScalars.{u, u, u}
          ((X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom ≫
            i.stalkMap (g w)).hom).obj F₀)) := by
  refine stalkCongr_transport hpt
    (fun c ψ φ => ∀ F₀ : ModuleCat.{u} (ToType (Z.presheaf.stalk (g w))),
      (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).essImage
        ((ModuleCat.extendScalars.{u, u, u} φ.hom).obj
          ((ModuleCat.restrictScalars.{u, u, u} ψ.hom).obj F₀)))
    (i.stalkMap (g w)) (f.stalkMap (i' w)) (fun F₁ => ?_) F₀
  have := isIso_stalkBaseChange_fst sq w hpt
  exact ⟨_, ⟨(@asIso _ _ _ _ _ (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ this F₁)).symm⟩⟩

/-- **Derived extension of scalars of a restricted K-flat complex is computed termwise.**  Under
Tor independence of `Z` and `X'` over `X`, derived extension of scalars along the germ map
`𝒪_{X, f (i' w)} ⟶ 𝒪_{X', i' w}` is computed by termwise extension of scalars on every complex
restricted from a K-flat complex of `𝒪_{Z, g w}`-modules. -/
theorem isIso_comparison_restrictScalars_stalk (_sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (w : Z') (hpt : i (g w) = f (i' w))
    (K : CochainComplex (ModuleCat.{u} (ToType (Z.presheaf.stalk (g w)))) ℤ)
    (hK : CochainComplex.KFlat K) :
    IsIso ((totalDerivedExtensionScalars.{u, u, u} (f.stalkMap (i' w)).hom).comparison.app
      (((ModuleCat.restrictScalars.{u, u, u}
          ((X.presheaf.stalkCongr (Inseparable.of_eq hpt.symm)).hom ≫
            i.stalkMap (g w)).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  refine stalkCongr_transport hpt
    (fun c ψ φ => ∀ K : CochainComplex (ModuleCat.{u} (ToType (Z.presheaf.stalk (g w)))) ℤ,
      CochainComplex.KFlat K →
        IsIso ((totalDerivedExtensionScalars.{u, u, u} φ.hom).comparison.app
          (((ModuleCat.restrictScalars.{u, u, u} ψ.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (i.stalkMap (g w)) (f.stalkMap (i' w)) (fun K₁ hK₁ => ?_) K hK
  let algRA := toAlgebraOfHom (i.stalkMap (g w))
  let algRR' :=
    toAlgebraOfHom ((X.presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ f.stalkMap (i' w))
  have hL : (Lg w hpt).IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ Lg w hpt ⟶ CochainComplex.extendScalarsLarge.{u, u, u}
          (algebraMap (ToType (X.presheaf.stalk (i (g w)))) (ToType (X'.presheaf.stalk (i' w)))) ⋙
            DerivedCategory.Q from alphaG w hpt)
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
    (totalDerivedExtensionScalars.{u, u, u} (ringRR' w hpt)).isLeftDerived
  exact isIso_extendScalarsCounit_app_restrict_of_torIndependent.{u, u, u, u}
    (torIndependent_stalkMap_of_torIndependent htor w hpt) (Lg w hpt) (alphaG w hpt) K₁ hK₁

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
