module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images of sheaves of modules along an integral morphism

For a ring `Λ` and an integral morphism of schemes `f : X ⟶ Y`, the direct image
`f_* : Mod(X_étale, Λ) ⥤ Mod(Y_étale, Λ)` is an exact functor, so `R^q f_* F = 0` for every sheaf
of `Λ`-modules `F` on `X_étale` and every `q > 0`. This is the case `n = 0` of [Stacks, Tag 095U],
which bounds the higher direct images along a proper morphism with fibres of dimension at most
`n`, here for every sheaf of `Λ`-modules rather than only the torsion abelian sheaves.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImage_preservesEpimorphisms_of_isIntegralHom`: the
  direct image of sheaves of `Λ`-modules along an integral morphism preserves epimorphisms.
* `Stacks.EtaleCohomology.etaleModuleDirectImage_exact_of_isIntegralHom`: that direct image is
  an exact functor.
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom`:
  `R^q f_* F = 0` for `q > 0`.
* `Stacks.EtaleCohomology.exists_isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom`:
  there is a degree above which every higher direct image vanishes.

## Implementation notes

Exactness is proved at module coefficients rather than transported from the abelian statement
`Stacks.EtaleCohomology.smallEtalePushforwardAb_exact_of_isIntegralHom`: that transport would need
the forgetful functor `ModuleCat Λ ⥤ AddCommGrpCat` to preserve injective objects, that is `Λ`
flat over `ℤ`, which fails for `Λ = ℤ/nℤ`.

## References

* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe t u r

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- The forgetful functor from modules to types preserves filtered colimits. -/
theorem forget_moduleCat_preservesFilteredColimits (Λ : Type r) [Ring Λ] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{t} Λ)) :=
  let : PreservesColimits (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{t, r, t, t} Λ
  comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{t} Λ) AddCommGrpCat.{t}) (CategoryTheory.forget AddCommGrpCat.{t})

attribute [local instance] forget_moduleCat_preservesFilteredColimits

/-- On a small site, sheafification of module-valued presheaves inverts exactly the locally
bijective morphisms. -/
theorem wEqualsLocallyBijective_moduleCat_smallSite (Λ : Type r) [Ring Λ] {D : Type t}
    [SmallCategory D] (K : GrothendieckTopology D) [UnivLE.{r, t}] :
    K.WEqualsLocallyBijective (ModuleCat.{t} Λ) :=
  inferInstance

/-- On the small étale site of a scheme, sheafification of module-valued presheaves inverts
exactly the locally bijective morphisms; equivalently, a morphism of sheaves of `Λ`-modules is
an epimorphism exactly when it is locally surjective. -/
instance wEqualsLocallyBijective_etaleModules (Λ : Type r) [Ring Λ] (X : Scheme.{u}) :
    X.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{max (u + 1) r} Λ) := by
  have : ((equivSmallModel.{max (u + 1) r} X.Etale).inverse.inducedTopology
      X.smallEtaleTopology).WEqualsLocallyBijective (ModuleCat.{max (u + 1) r} Λ) :=
    wEqualsLocallyBijective_moduleCat_smallSite Λ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, _, u + 1, _,
    max (u + 1) r} X.smallEtaleTopology

/-- For an integral morphism of schemes `f : X ⟶ Y`, the direct image
`f_* : Mod(X_étale, Λ) ⥤ Mod(Y_étale, Λ)` preserves epimorphisms. -/
theorem etaleModuleDirectImage_preservesEpimorphisms_of_isIntegralHom (Λ : Type r) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    (etaleModuleDirectImage.{u, r} Λ f).PreservesEpimorphisms := by
  have hset :
      ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) r))
        (smallEtaleTopology Y) (smallEtaleTopology X)).PreservesEpimorphisms :=
    smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom f
  constructor
  intro F G φ hφ
  have := (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max (u + 1) r} Λ) φ).2 hφ
  have hforget : Epi ((sheafCompose (smallEtaleTopology Y)
      (CategoryTheory.forget (ModuleCat.{max (u + 1) r} Λ))).map
      ((etaleModuleDirectImage.{u, r} Λ f).map φ)) :=
    hset.preserves ((sheafCompose (smallEtaleTopology X)
      (CategoryTheory.forget (ModuleCat.{max (u + 1) r} Λ))).map φ)
  have : Sheaf.IsLocallySurjective ((etaleModuleDirectImage.{u, r} Λ f).map φ) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget (smallEtaleTopology Y) _).2
      ((Sheaf.isLocallySurjective_iff_epi _).2 hforget)
  exact Sheaf.epi_of_isLocallySurjective _

/-- For an integral morphism of schemes `f : X ⟶ Y`, the direct image
`f_* : Mod(X_étale, Λ) ⥤ Mod(Y_étale, Λ)` is an exact functor. -/
theorem etaleModuleDirectImage_exact_of_isIntegralHom (Λ : Type r) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    exactFunctor (EtaleModules.{u, r} Λ X) (EtaleModules.{u, r} Λ Y)
      (etaleModuleDirectImage.{u, r} Λ f) := by
  have hfl : PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ f) := inferInstance
  have hepi := etaleModuleDirectImage_preservesEpimorphisms_of_isIntegralHom Λ f
  have hhom :=
    Functor.preservesHomology_of_preservesEpis_and_kernels (etaleModuleDirectImage.{u, r} Λ f)
  rw [exactFunctor_iff]
  exact ⟨hfl, Functor.preservesFiniteColimits_of_preservesHomology _⟩

/-- Let `Λ` be a ring and let `f : X ⟶ Y` be an integral morphism of schemes. Then the higher
direct images of every sheaf of `Λ`-modules `F` on the small étale site of `X` vanish:
`R^q f_* F = 0` for every `q > 2 · 0`. -/
@[stacks 095U "the case n = 0: for an integral morphism — a finite one, for instance, which is
what a proper morphism with zero-dimensional fibres is — R^q f_* F = 0 for every q > 0 and every
sheaf of Λ-modules F, with no torsion hypothesis. The general bound 2n is NOT proved: its
induction needs the curve case, Tag 03SC, which is not formalized here.",
  sga "4 VIII 5.6" "more general",
  sga "4 Vbis 4.3.4" "more general",
  sga "4 XII 5.3" "special case",
  sga "4 XIV 1.11" "partial",
  sga "4 XVII 4.3.1" "special case",
  sga "4 XVII 5.1.4" "special case",
  sga "4½ Arcata 2.3.6" "more general",
  sga "4½ Th_finitude 1.3" "special case"]
theorem isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom (Λ : Type r) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] (F : EtaleModules.{u, r} Λ X) (q : ℕ)
    (hq : 2 * 0 < q) :
    IsZero (((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).obj F) :=
  Functor.isZero_rightDerived_of_exactFunctor _
    (etaleModuleDirectImage_exact_of_isIntegralHom Λ f) F q (by omega)

/-- For an integral morphism of schemes `f : X ⟶ Y` there is a degree `d` such that
`R^q f_* F = 0` for every `q ≥ d` and every sheaf of `Λ`-modules `F` on the small étale site of
`X`. -/
theorem exists_isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom (Λ : Type r) [Ring Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, r} Λ X,
      IsZero (((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).obj F) :=
  ⟨1, fun q hq F ↦
    isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom Λ f F q (by omega)⟩

end Stacks.EtaleCohomology

end
