module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorNatTrans
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTensorPushforwardIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms

/-!
# The derived projection formula for a finite morphism of algebraic spaces

Let `S` be a scheme, `π : X ⟶ Y` a finite morphism of algebraic spaces over `S`, `𝒜` a sheaf of
rings on `X_étale`, `ℬ` a sheaf of rings on `Y_étale` and `φ : ℬ ⟶ π_*𝒜` a homomorphism of
sheaves of rings, with associated morphism of ringed topoi

`f = (π, φ) : (Sh(X_étale), 𝒜) ⟶ (Sh(Y_étale), ℬ)`.

**Stacks 0DK5** asserts that for `K ∈ D(ℬ)` and `M ∈ D(𝒜)`

`K ⊗^L_ℬ Rf_*M = Rf_*(Lf^*K ⊗^L_𝒜 M)`

in `D(ℬ)`.

The proof is the source's. By Stacks 0A4K (for modules: the direct image commutes with colimits,
`AlgebraicGeometry.Space.preservesColimitsOfSize_pushforwardModules_of_isFinite`), `f_*` is
exact, so `Rf_*` is computed by applying `f_*` to any representative complex. Represent `K` by
a K-flat complex `𝒦` with flat terms (Stacks 06YS); then `f^*𝒦` is K-flat with flat terms
(Stacks 0G7E) and represents `Lf^*K` (Stacks 06YY), so for any complex `ℳ` representing `M` the
two sides are represented by

`Tot(𝒦 ⊗_ℬ f_*ℳ)` and `f_*Tot(f^*𝒦 ⊗_𝒜 ℳ)`.

Since `f_*` commutes with direct sums these are identified termwise by the isomorphisms
`𝒦ⁿ ⊗_ℬ f_*ℳᵐ = f_*(f^*𝒦ⁿ ⊗_𝒜 ℳᵐ)` of Stacks 0DK4.

## Main definitions

* `AlgebraicGeometry.Space.tensorPushforwardBifunctorIso`: the isomorphism of Stacks 0DK4,
  `𝓖 ⊗_ℬ f_*𝓕 ≅ f_*(f^*𝓖 ⊗_𝒜 𝓕)`, as an isomorphism of bifunctors, for the curried tensor
  product of sheaves of modules and the direct image along the morphism of ringed topoi
  `AlgebraicGeometry.Space.ringedToposHomOfSharp`.
* `AlgebraicGeometry.Space.tensorBicomplexPushforwardIso`,
  `AlgebraicGeometry.Space.tensorComplexPushforwardIso`: its application to bicomplexes and the
  totalization `Tot(𝒦 ⊗_ℬ f_*ℳ) ≅ f_*Tot(f^*𝒦 ⊗_𝒜 ℳ)`, for arbitrary complexes `𝒦` and `ℳ`.
* `AlgebraicGeometry.Space.derivedPushforwardIsoMapDerivedCategory`: `Rf_*` is the functor induced
  on derived categories by the exact functor `f_*`;
  `AlgebraicGeometry.Space.derivedPushforwardObjQIso`
  and `AlgebraicGeometry.Space.derivedPullbackObjQIso` compute `Rf_*` on any complex and `Lf^*`
  on a K-flat complex with flat terms.
* `AlgebraicGeometry.Space.derivedTensorPushforwardIsoOfKFlat`: the isomorphism of Stacks 0DK5 on
  representatives.

## Main results

* `AlgebraicGeometry.Space.nonempty_derivedTensorPushforwardIso`: **Stacks 0DK5**.

## Implementation notes

The three derived functors are the ones of this repository at the generality of the small étale
ringed topos, whose site has its objects in `Type (u + 1)` and its sections in `Type u`: the
derived tensor product of Stacks 06YU at a site whose object universe is free
(`Stacks.SheafOfModules.derivedTensorProductFunctor`), the derived direct image of Stacks 07A5
and the derived pullback of Stacks 06YY for a morphism of ringed topoi in the two-field sense of
Stacks 01D3 (`Stacks.Cohomology.DerivedPushforward.derivedPushforward`,
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback`). The latter exists along every
morphism of ringed topoi, by Stacks 06YS and the exactness clause of Stacks 06YY
(`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`).

The source writes the conclusion as an equality in `D(ℬ)`, and its proof identifies the two
sides through the choice of representatives; accordingly the statement here is the existence of
an isomorphism. The isomorphism of total complexes from which it is built,
`AlgebraicGeometry.Space.tensorComplexPushforwardIso`, is canonical.

The canonical map `𝓖 ⊗_ℬ f_*𝓕 ⟶ f_*(f^*𝓖 ⊗_𝒜 𝓕)` is defined for the four-field morphism of
ringed topoi of the modules development, `AlgebraicGeometry.RingedToposHom.toModulesHom`, whose
direct image differs from `AlgebraicGeometry.RingedToposHom.pushforwardModules` — the one `Rf_*`
derives — by the identification `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`; the
two are reconciled in `AlgebraicGeometry.Space.tensorPushforwardBifunctorIso`. That the canonical
map is an isomorphism is proved for any four-field morphism with the same underlying morphism of
topoi as `f`, through the stalkwise criterion
`Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints` fed with
`AlgebraicGeometry.Space.exists_bijective_pushforwardFiberMap_of_isFinite` (Stacks 0DK3), which is
also how Stacks 0DK4 is proved.

## References

* [Stacks Project, Tag 0DK5](https://stacks.math.columbia.edu/tag/0DK5)
* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against the modules of the small étale site, whose objects lie
one universe above their sections; the abelian structure used here is the one at the pinned
universes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (π : X ⟶ Y)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}}
    (φ : ℬ ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS π)).obj 𝒜)

/-- The total tensor complex of two complexes of modules over a sheaf of rings on the small étale
site of an algebraic space exists. This is
`Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor` at the universes of this site; instance
search does not find it unaided, the abelian group universe of its hypotheses being determined
only through the module universes. Here `R` is any sheaf of commutative rings on the small étale
site; the case of the structure sheaf is the local instance
`AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_smallEtale` of `SmallEtaleDerivedTensor`. -/
instance hasMapBifunctor_sheafTensor_smallEtaleCommRingSheaf {Z : AlgebraicSpaces B S hS}
    (R : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u})
    (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} R) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u + 1, u, u, u, u} R K₁ K₂

/-- The derived pullback along `f = (π, φ)` exists: Stacks 06YS resolves by K-flat complexes
with flat terms, and degreewise pullback inverts quasi-isomorphisms between them. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_ringedToposHomOfSharp :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy
      (ringedToposHomOfSharp B S hS π φ)).HasLeftDerivedFunctor
      (Stacks.Cohomology.DerivedPullbackOfToposHom.quasiIsoTarget
        (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)) :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    (ringedToposHomOfSharp B S hS π φ)

variable {B S hS π}

/-- **Stacks 0DK4 for `f = (π, φ)`, at the four-field morphism of ringed topoi**: for `π`
finite the canonical map `𝓖 ⊗_ℬ f_*𝓕 ⟶ f_*(f^*𝓖 ⊗_𝒜 𝓕)` is an isomorphism. -/
theorem isIso_pushforwardTensorMap_ringedToposHomOfSharp (hπ : IsFinite B S hS π.hom)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ))
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜)) :
    IsIso (((Stacks.SheafOfModules.pushforwardTensorBifunctorNatTrans
      (ringedToposHomOfSharp B S hS π φ).toModulesHom).app G).app N) :=
  Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints
    (ringedToposHomOfSharp B S hS π φ).toModulesHom
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS Y.1 Y.2)
    (exists_bijective_pushforwardFiberMap_of_isFinite B S hS π hπ) G N

/-- For `π` finite, the canonical map of Stacks 0DK4 is an isomorphism of bifunctors. -/
theorem isIso_pushforwardTensorBifunctorNatTrans_ringedToposHomOfSharp
    (hπ : IsFinite B S hS π.hom) :
    IsIso (Stacks.SheafOfModules.pushforwardTensorBifunctorNatTrans
      (ringedToposHomOfSharp B S hS π φ).toModulesHom) := by
  have : ∀ G, IsIso ((Stacks.SheafOfModules.pushforwardTensorBifunctorNatTrans
      (ringedToposHomOfSharp B S hS π φ).toModulesHom).app G) := fun G =>
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N =>
      isIso_pushforwardTensorMap_ringedToposHomOfSharp φ hπ G N
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks 0DK4 as an isomorphism of bifunctors**: for `π` finite,
`(𝓖, 𝓕) ↦ 𝓖 ⊗_ℬ f_*𝓕` and `(𝓖, 𝓕) ↦ f_*(f^*𝓖 ⊗_𝒜 𝓕)` are isomorphic, through the canonical
map. -/
def tensorPushforwardBifunctorIso (hπ : IsFinite B S hS π.hom) :
    Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ ⋙
        (Functor.whiskeringLeft _ _ _).obj (ringedToposHomOfSharp B S hS π φ).pushforwardModules ≅
      (ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules ⋙
        Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜 ⋙
          (Functor.whiskeringRight _ _ _).obj
            (ringedToposHomOfSharp B S hS π φ).pushforwardModules :=
  haveI := isIso_pushforwardTensorBifunctorNatTrans_ringedToposHomOfSharp φ hπ
  Functor.isoWhiskerLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ)
      ((Functor.whiskeringLeft _ _ _).mapIso
        (ringedToposHomOfSharp B S hS π φ).toModulesPushforwardIso).symm ≪≫
    asIso (Stacks.SheafOfModules.pushforwardTensorBifunctorNatTrans
      (ringedToposHomOfSharp B S hS π φ).toModulesHom) ≪≫
    Functor.isoWhiskerLeft (ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules
      (Functor.isoWhiskerLeft (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜)
        ((Functor.whiskeringRight _ _ _).mapIso
          (ringedToposHomOfSharp B S hS π φ).toModulesPushforwardIso))

/-- The direct image of modules along `ringedToposHomOfSharp B S hS π φ` is additive. -/
instance : (ringedToposHomOfSharp B S hS π φ).pushforwardModules.Additive :=
  RingedToposHom.pushforwardModules_additive (ringedToposHomOfSharp B S hS π φ)

/-- The pullback of modules along `ringedToposHomOfSharp B S hS π φ` is additive. -/
instance : (ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (ringedToposHomOfSharp B S hS π φ)

/-- The bifunctor `(𝒦, ℳ) ↦ 𝒦 ⊗_ℬ f_*ℳ` preserves zero morphisms in its first variable. -/
instance : (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ ⋙
    (Functor.whiskeringLeft _ _ _).obj
    (ringedToposHomOfSharp B S hS π φ).pushforwardModules).PreservesZeroMorphisms where
  map_zero _ _ := NatTrans.ext (funext fun _ =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ).flip.obj _).map_zero _ _)

/-- For a fixed `ℬ`-module `G`, the functor `ℳ ↦ G ⊗_ℬ f_*ℳ` preserves zero morphisms. -/
instance (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ ⋙
      (Functor.whiskeringLeft _ _ _).obj
        (ringedToposHomOfSharp B S hS π φ).pushforwardModules).obj G).PreservesZeroMorphisms :=
  inferInstanceAs ((ringedToposHomOfSharp B S hS π φ).pushforwardModules ⋙
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ).obj G).PreservesZeroMorphisms

/-- The bifunctor `(𝒦, ℳ) ↦ f_*(f^*𝒦 ⊗_𝒜 ℳ)` preserves zero morphisms in its first variable. -/
instance : ((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules ⋙
    Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜 ⋙
    (Functor.whiskeringRight _ _ _).obj
      (ringedToposHomOfSharp B S hS π φ).pushforwardModules).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext N : 2
    simp only [Functor.comp_map, Functor.map_zero, Functor.whiskeringRight_obj_map,
      Functor.whiskerRight_app, NatTrans.app_zero]

/-- For a fixed `ℬ`-module `G`, the functor `ℳ ↦ f_*(f^*G ⊗_𝒜 ℳ)` preserves zero morphisms. -/
instance (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) :
    (((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules ⋙
      Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜 ⋙
      (Functor.whiskeringRight _ _ _).obj
        (ringedToposHomOfSharp B S hS π φ).pushforwardModules).obj G).PreservesZeroMorphisms :=
  inferInstanceAs ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜).obj
    ((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.obj G) ⋙
      (ringedToposHomOfSharp B S hS π φ).pushforwardModules).PreservesZeroMorphisms

/-- **Stacks 0DK4 on bicomplexes**: for `π` finite and complexes `𝒦` of `ℬ`-modules and `ℳ` of
`𝒜`-modules, the bicomplex `𝒦ᵖ ⊗_ℬ f_*ℳ^q` is isomorphic to the image under `f_*` of the
bicomplex `f^*𝒦ᵖ ⊗_𝒜 ℳ^q`, through the isomorphisms of Stacks 0DK4. -/
def tensorBicomplexPushforwardIso (hπ : IsFinite B S hS π.hom)
    (𝒦 : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) ℤ)
    (ℳ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜)) ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ℬ).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj 𝒦).obj
        (((ringedToposHomOfSharp B S hS π φ).pushforwardModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ℳ) ≅
      HomologicalComplex₂.TotalMap.mapBicomplex
        (ringedToposHomOfSharp B S hS π φ).pushforwardModules
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          𝒜).mapBifunctorHomologicalComplex
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
            (((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj 𝒦)).obj ℳ) :=
  HomologicalComplex.mapBifunctorHomologicalComplexNatIso 𝒦 ℳ
    (tensorPushforwardBifunctorIso φ hπ)

set_option maxHeartbeats 1000000 in
-- elaborating the total-complex isomorphisms over nested `mapHomologicalComplex` functors
/-- **Stacks 0DK4, totalized**: for `π` finite and complexes `𝒦` of `ℬ`-modules and `ℳ` of
`𝒜`-modules, `Tot(𝒦 ⊗_ℬ f_*ℳ) ≅ f_*Tot(f^*𝒦 ⊗_𝒜 ℳ)`. On the summand of bidegree `(p, q)`
it is the isomorphism `𝒦ᵖ ⊗_ℬ f_*ℳ^q ≅ f_*(f^*𝒦ᵖ ⊗_𝒜 ℳ^q)` of Stacks 0DK4; that `f_*` commutes
with the direct sums forming the total complex is
`AlgebraicGeometry.Space.preservesColimitsOfSize_pushforwardModules_of_isFinite`. -/
def tensorComplexPushforwardIso (hπ : IsFinite B S hS π.hom)
    (𝒦 : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) ℤ)
    (ℳ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex ℬ).obj 𝒦).obj
        (((ringedToposHomOfSharp B S hS π φ).pushforwardModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ℳ) ≅
      ((ringedToposHomOfSharp B S hS π φ).pushforwardModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex 𝒜).obj
          (((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj 𝒦)).obj ℳ) :=
  haveI := preservesColimitsOfSize_pushforwardModules_of_isFinite B S hS π hπ φ
  haveI := HomologicalComplex₂.hasTotal_of_iso (tensorBicomplexPushforwardIso φ hπ 𝒦 ℳ)
    (ComplexShape.up ℤ)
  HomologicalComplex₂.total.mapIso (tensorBicomplexPushforwardIso φ hπ 𝒦 ℳ) (ComplexShape.up ℤ) ≪≫
    HomologicalComplex₂.TotalMap.totalIso (c₁₂ := ComplexShape.up ℤ)
      (ringedToposHomOfSharp B S hS π φ).pushforwardModules
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        𝒜).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
          (((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj 𝒦)).obj ℳ)

/-- The sheaves of modules on the small étale site of an algebraic space over an arbitrary sheaf
of rings form a Grothendieck abelian category at the universe of the sections, the site being
essentially small; this is what makes `Rf_*` exist on the unbounded derived category. -/
theorem isGrothendieckAbelian_smallEtaleRingedToposOfRings_modules
    (𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜)) :=
  have : EssentiallySmall.{u} (smallEtaleRingedToposOfRings B S hS X 𝒜).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X.1)
    infer_instance
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

attribute [local instance] isGrothendieckAbelian_smallEtaleRingedToposOfRings_modules

/-- The direct image of modules along `ringedToposHomOfSharp B S hS π φ` preserves finite
limits. -/
instance : PreservesFiniteLimits (ringedToposHomOfSharp B S hS π φ).pushforwardModules :=
  RingedToposHom.pushforwardModules_preservesFiniteLimits (ringedToposHomOfSharp B S hS π φ)

/-- **`Rf_*` is the functor induced by the exact functor `f_*`** on derived categories, for `π`
finite: by Stacks 0A4K the direct image of modules is exact, and an exact functor is its own
total right derived functor. -/
def derivedPushforwardIsoMapDerivedCategory (hπ : IsFinite B S hS π.hom) :
    haveI := preservesColimitsOfSize_pushforwardModules_of_isFinite B S hS π hπ φ
    Stacks.Cohomology.DerivedPushforward.derivedPushforward
        (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
        (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
        (ringedToposHomOfSharp B S hS π φ) ≅
      (ringedToposHomOfSharp B S hS π φ).pushforwardModules.mapDerivedCategory :=
  haveI := preservesColimitsOfSize_pushforwardModules_of_isFinite B S hS π hπ φ
  (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived
    (ringedToposHomOfSharp B S hS π φ).pushforwardModules).symm

/-- For `π` finite, `Rf_*` of a complex is computed by applying `f_*` termwise. -/
def derivedPushforwardObjQIso (hπ : IsFinite B S hS π.hom)
    (ℳ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜)) ℤ) :
    (Stacks.Cohomology.DerivedPushforward.derivedPushforward
        (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
        (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
        (ringedToposHomOfSharp B S hS π φ)).obj (DerivedCategory.Q.obj ℳ) ≅
      DerivedCategory.Q.obj
        (((ringedToposHomOfSharp B S hS π φ).pushforwardModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ℳ) :=
  haveI := preservesColimitsOfSize_pushforwardModules_of_isFinite B S hS π hπ φ
  (derivedPushforwardIsoMapDerivedCategory φ hπ).app _ ≪≫
    (ringedToposHomOfSharp B S hS π φ).pushforwardModules.mapDerivedCategoryFactors.app ℳ

/-- **Stacks 06YY at a K-flat complex with flat terms**: `Lf^*` of such a complex is computed by
applying `f^*` termwise. -/
def derivedPullbackObjQIso
    (𝒦 : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) ℤ)
    (h𝒦 : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ) 𝒦)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := ℬ) (𝒦.X i)) :
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
        (ringedToposHomOfSharp B S hS π φ)).obj (DerivedCategory.Q.obj 𝒦) ≅
      DerivedCategory.Q.obj
        (((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj 𝒦) :=
  haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app
    (ringedToposHomOfSharp B S hS π φ)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedToposOfRings B S hS Y ℬ))
    (fun N => by
      obtain ⟨K, hK, t, ht⟩ :=
        Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
          (Y := smallEtaleRingedToposOfRings B S hS Y ℬ) N
      exact ⟨K, hK, t, ht⟩)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat
      (ringedToposHomOfSharp B S hS π φ))
    ((HomotopyCategory.quotient _ _).obj 𝒦) ⟨h𝒦, hflat⟩
  (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
      (ringedToposHomOfSharp B S hS π φ)).mapIso
      ((DerivedCategory.quotientCompQhIso _).app 𝒦).symm ≪≫
    asIso ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison
      (ringedToposHomOfSharp B S hS π φ)).app ((HomotopyCategory.quotient _ _).obj 𝒦)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- **Stacks 0G7E for `f = (π, φ)`**: the pullback of a K-flat complex of `ℬ`-modules with flat
terms is K-flat. -/
theorem isKFlat_pullbackModules_mapHomologicalComplex
    (𝒦 : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) ℤ)
    (h𝒦 : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ) 𝒦)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := ℬ) (𝒦.X i)) :
    Stacks.SheafOfModules.IsKFlat 𝒜
      (((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj 𝒦) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex
    (ringedToposHomOfSharp B S hS π φ) 𝒦 h𝒦 hflat

set_option maxHeartbeats 1000000 in
-- elaborating the K-flat comparison isomorphism through nested derived and complex functors
/-- For a K-flat complex `𝒦` of `ℬ`-modules with flat terms and any complex `ℳ` of `𝒜`-modules,
`Lf^*(Q𝒦) ⊗^L_𝒜 Qℳ` is represented by `Tot(f^*𝒦 ⊗_𝒜 ℳ)`: `Lf^*(Q𝒦) = Q(f^*𝒦)` by Stacks 06YY
and `f^*𝒦` is K-flat by Stacks 0G7E. -/
def derivedTensorPullbackObjQIso
    (𝒦 : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) ℤ)
    (h𝒦 : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ) 𝒦)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := ℬ) (𝒦.X i))
    (ℳ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜)) ℤ) :
    DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex 𝒜).obj
          (((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj 𝒦)).obj ℳ) ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleRingedToposOfRings B S hS X 𝒜).toRingedSite).obj
            ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
              (ringedToposHomOfSharp B S hS π φ)).obj (DerivedCategory.Q.obj 𝒦))).obj
          (DerivedCategory.Q.obj ℳ) :=
  ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (smallEtaleRingedToposOfRings B S hS X 𝒜).toRingedSite).comparisonLeft
          (((ringedToposHomOfSharp B S hS π φ).toModulesHom.pullbackModules.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj 𝒦) ℳ
          (isKFlat_pullbackModules_mapHomologicalComplex φ 𝒦 h𝒦 hflat)).symm ≪≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleRingedToposOfRings B S hS X 𝒜).toRingedSite).mapIso
            (derivedPullbackObjQIso φ 𝒦 h𝒦 hflat)).symm.app _

set_option maxHeartbeats 1000000 in
-- elaborating the composite of derived tensor-product and derived pushforward isomorphisms
/-- **Stacks 0DK5 on representatives**: for `π` finite, a K-flat complex `𝒦` of `ℬ`-modules with
flat terms and any complex `ℳ` of `𝒜`-modules,
`Q𝒦 ⊗^L_ℬ Rf_*(Qℳ) ≅ Rf_*(Lf^*(Q𝒦) ⊗^L_𝒜 Qℳ)`.

Both sides are represented by total complexes: the left by `Tot(𝒦 ⊗_ℬ f_*ℳ)`, `f_*` being
exact and `𝒦` K-flat, and the right by `f_*Tot(f^*𝒦 ⊗_𝒜 ℳ)`
(`AlgebraicGeometry.Space.derivedTensorPullbackObjQIso`); these are identified by
`AlgebraicGeometry.Space.tensorComplexPushforwardIso`. -/
def derivedTensorPushforwardIsoOfKFlat (hπ : IsFinite B S hS π.hom)
    (𝒦 : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) ℤ)
    (h𝒦 : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ) 𝒦)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := ℬ) (𝒦.X i))
    (ℳ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜)) ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedToposOfRings B S hS Y ℬ).toRingedSite).obj (DerivedCategory.Q.obj 𝒦)).obj
        ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
          (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
          (ringedToposHomOfSharp B S hS π φ)).obj (DerivedCategory.Q.obj ℳ)) ≅
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
          (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
          (ringedToposHomOfSharp B S hS π φ)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleRingedToposOfRings B S hS X 𝒜).toRingedSite).obj
            ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
              (ringedToposHomOfSharp B S hS π φ)).obj (DerivedCategory.Q.obj 𝒦))).obj
          (DerivedCategory.Q.obj ℳ)) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedToposOfRings B S hS Y ℬ).toRingedSite).obj
        (DerivedCategory.Q.obj 𝒦)).mapIso (derivedPushforwardObjQIso φ hπ ℳ) ≪≫
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (smallEtaleRingedToposOfRings B S hS Y ℬ).toRingedSite).comparisonLeft 𝒦 _ h𝒦 ≪≫
    DerivedCategory.Q.mapIso (tensorComplexPushforwardIso φ hπ 𝒦 ℳ) ≪≫
    (derivedPushforwardObjQIso φ hπ _).symm ≪≫
    (Stacks.Cohomology.DerivedPushforward.derivedPushforward
      (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
      (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
      (ringedToposHomOfSharp B S hS π φ)).mapIso
      (derivedTensorPullbackObjQIso φ 𝒦 h𝒦 hflat ℳ)

/-- **Stacks 06YS on `D(ℬ)`**: every object of `D(ℬ)` is represented by a K-flat complex with flat
terms. -/
theorem exists_kFlat_flat_iso
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ))) :
    ∃ 𝒦 : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ) 𝒦 ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := ℬ) (𝒦.X i)) ∧
      Nonempty (DerivedCategory.Q.obj 𝒦 ≅ K) := by
  obtain ⟨P, hP, t, ht⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
      (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
      ((HomotopyCategory.quotient _ _).obj (DerivedCategory.Q.objPreimage K))
  exact ⟨P.as, hP.1, hP.2, ⟨((DerivedCategory.quotientCompQhIso _).app P.as).symm ≪≫
    @asIso _ _ _ _ (DerivedCategory.Qh.map t)
      (Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) t ht) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

/-- **Stacks 0DK5 through representatives**: given a K-flat complex `𝒦` with flat terms and an
isomorphism `Q𝒦 ≅ K`, and a complex `ℳ` with `Qℳ ≅ M`, the isomorphism
`K ⊗^L_ℬ Rf_*M ≅ Rf_*(Lf^*K ⊗^L_𝒜 M)` transported from
`AlgebraicGeometry.Space.derivedTensorPushforwardIsoOfKFlat`. -/
def derivedTensorPushforwardIsoOfIso (hπ : IsFinite B S hS π.hom)
    (𝒦 : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)) ℤ)
    (h𝒦 : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ) 𝒦)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := ℬ) (𝒦.X i))
    (ℳ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜)) ℤ)
    {K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ))}
    {M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜))}
    (eK : DerivedCategory.Q.obj 𝒦 ≅ K) (eM : DerivedCategory.Q.obj ℳ ≅ M) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedToposOfRings B S hS Y ℬ).toRingedSite).obj K).obj
        ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
          (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
          (ringedToposHomOfSharp B S hS π φ)).obj M) ≅
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
          (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
          (ringedToposHomOfSharp B S hS π φ)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleRingedToposOfRings B S hS X 𝒜).toRingedSite).obj
            ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
              (ringedToposHomOfSharp B S hS π φ)).obj K)).obj M) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedToposOfRings B S hS Y ℬ).toRingedSite).mapIso eK.symm).app _ ≪≫
    ((Stacks.SheafOfModules.derivedTensorProductFunctor
      (smallEtaleRingedToposOfRings B S hS Y ℬ).toRingedSite).obj _).mapIso
      ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
        (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
        (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
        (ringedToposHomOfSharp B S hS π φ)).mapIso eM.symm) ≪≫
    derivedTensorPushforwardIsoOfKFlat φ hπ 𝒦 h𝒦 hflat ℳ ≪≫
    (Stacks.Cohomology.DerivedPushforward.derivedPushforward
      (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
      (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
      (ringedToposHomOfSharp B S hS π φ)).mapIso
      (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleRingedToposOfRings B S hS X 𝒜).toRingedSite).mapIso
          ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
            (ringedToposHomOfSharp B S hS π φ)).mapIso eK)).app _ ≪≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleRingedToposOfRings B S hS X 𝒜).toRingedSite).obj _).mapIso eM)

/-- **Stacks 0DK5.** Let `π : X ⟶ Y` be a finite morphism of algebraic spaces over `S`, `𝒜` a
sheaf of rings on `X_étale`, `ℬ` a sheaf of rings on `Y_étale` and `φ : ℬ ⟶ π_*𝒜` a homomorphism
of sheaves of rings, with associated morphism of ringed topoi
`f = (π, φ) : (Sh(X_étale), 𝒜) ⟶ (Sh(Y_étale), ℬ)`. Then for every `K ∈ D(ℬ)` and `M ∈ D(𝒜)`

`K ⊗^L_ℬ Rf_*M ≅ Rf_*(Lf^*K ⊗^L_𝒜 M)` in `D(ℬ)`.

`K` is represented by a K-flat complex with flat terms (Stacks 06YS) and `M` by any complex;
on such representatives the isomorphism is
`AlgebraicGeometry.Space.derivedTensorPushforwardIsoOfKFlat`. -/
@[stacks 0DK5]
theorem nonempty_derivedTensorPushforwardIso (hπ : IsFinite B S hS π.hom)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ℬ)))
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf 𝒜))) :
    Nonempty (((Stacks.SheafOfModules.derivedTensorProductFunctor
        (smallEtaleRingedToposOfRings B S hS Y ℬ).toRingedSite).obj K).obj
        ((Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
          (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
          (ringedToposHomOfSharp B S hS π φ)).obj M) ≅
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward
          (X := smallEtaleRingedToposOfRings B S hS X 𝒜)
          (Y := smallEtaleRingedToposOfRings B S hS Y ℬ)
          (ringedToposHomOfSharp B S hS π φ)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleRingedToposOfRings B S hS X 𝒜).toRingedSite).obj
            ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback
              (ringedToposHomOfSharp B S hS π φ)).obj K)).obj M)) := by
  obtain ⟨𝒦, h𝒦, hflat, ⟨eK⟩⟩ := exists_kFlat_flat_iso K
  exact ⟨derivedTensorPushforwardIsoOfIso φ hπ 𝒦 h𝒦 hflat _ eK
    (DerivedCategory.Q.objObjPreimageIso M)⟩

end AlgebraicGeometry.Space

end
