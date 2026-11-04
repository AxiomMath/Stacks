module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison

/-!
# Flat pullback of the Tor sheaves

Let `f : X ⟶ Y` be a flat morphism of schemes. Then

`f^*Tor_p^{𝒪_Y}(ℱ, 𝒢) ≅ Tor_p^{𝒪_X}(f^*ℱ, f^*𝒢)`

for all `𝒪_Y`-modules `ℱ` and `𝒢`.

## Main definitions

* `AlgebraicGeometry.TorFormula.pullbackTorSheafIso` — the isomorphism above.

## Implementation notes

The source of [Stacks, Tag 0B0Y] gets this from [Stacks, Tag 079U], the monoidality of derived
pullback, together with the exactness of `f^*` for flat `f`, which identifies `Lf^*ℱ` with
`f^*ℱ`. The proof here runs the same argument but entirely on K-flat representatives, so that
no derived pullback functor occurs and no comparison between the two models of `D(𝒪_X)` is
needed.

Choose K-flat complexes `A` and `B` of `𝒪_Y`-modules whose classes in `D(𝒪_Y)` are `ℱ` and `𝒢`
placed in degree `0`. Then:

* `ℱ ⊗ᴸ 𝒢 ≅ Q(Tot(A ⊗_{𝒪_Y} B))`, the `comparison` field of the derived tensor product;
* `f^*A` and `f^*B` are K-flat, which is [Stacks, Tag 06YC];
* `f^*` is exact, so it descends to `D(𝒪_Y) ⥤ D(𝒪_X)` and there `Q(f^*A)` is `f^*ℱ` placed in
  degree `0`, which gives `f^*ℱ ⊗ᴸ f^*𝒢 ≅ Q(Tot(f^*A ⊗_{𝒪_X} f^*B))` by the same comparison
  on `X`;
* `f^*Tot(A ⊗_{𝒪_Y} B) ≅ Tot(f^*A ⊗_{𝒪_X} f^*B)` degreewise, which is [Stacks, Tag 01CD]
  assembled on total complexes;
* an exact functor commutes with the cohomology of a complex, so `H^{-p}` of the right-hand
  side is `f^*H^{-p}(Tot(A ⊗_{𝒪_Y} B))`.

Exactness of `f^*` enters twice and in the same form both times: left exactness is flatness
(`AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat`) and right exactness holds
for every morphism (`AlgebraicGeometry.preservesFiniteColimits_modulesPullback`).

The pullback and tensor developments spell the structure sheaf of a ringed space differently,
so the local `implicit_reducible` attributes of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison` are
repeated here for the same reason they are needed there.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0B0Y](https://stacks.math.columbia.edu/tag/0B0Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TorFormula

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

/-- **The derived tensor product of two modules, computed on K-flat representatives.** If the
classes of the K-flat complexes `A` and `B` in `D(𝒪_Z)` are `ℱ` and `𝒢` placed in degree `0`,
then `ℱ ⊗ᴸ_{𝒪_Z} 𝒢 ≅ Q(Tot(A ⊗_{𝒪_Z} B))`. This is the `comparison` field of the derived
tensor product, transported along the two chosen isomorphisms. -/
def derivedTensorIsoQTotal (Z : Scheme.{u}) (F G : Z.Modules)
    (A B : Stacks.Duality.TensorComplex Z)
    (hA : Stacks.Duality.KFlatComplex A) (hB : Stacks.Duality.KFlatComplex B)
    (eA : (DerivedCategory.Q.obj A : DerivedCategory Z.Modules) ≅
      (DerivedCategory.singleFunctor Z.Modules 0).obj F)
    (eB : (DerivedCategory.Q.obj B : DerivedCategory Z.Modules) ≅
      (DerivedCategory.singleFunctor Z.Modules 0).obj G) :
    ((derivedTensor Z).obj
          ((DerivedCategory.singleFunctor Z.Modules 0).obj F)).obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj G) ≅
      (DerivedCategory.Q.obj (Stacks.Duality.totalTensorComplex A B) :
        DerivedCategory Z.Modules) :=
  (((derivedTensor Z).mapIso eA).app _).symm ≪≫
    ((derivedTensor Z).obj (DerivedCategory.Q.obj A)).mapIso eB.symm ≪≫
    (Stacks.Cohomology.TorAmplitude.derTensor Z.toRingedSpace).comparison A B hA hB

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The degreewise pullback of a complex of `𝒪_Y`-modules, as a complex of `𝒪_X`-modules. -/
abbrev pullbackComplexScheme (A : Stacks.Duality.TensorComplex Y) :
    Stacks.Duality.TensorComplex X :=
  ((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj A

/-- **[Stacks, Tag 06YC]: the degreewise pullback of a K-flat complex is K-flat.** -/
theorem kFlatComplex_pullbackComplexScheme (A : Stacks.Duality.TensorComplex Y)
    (hA : Stacks.Duality.KFlatComplex A) :
    Stacks.Duality.KFlatComplex (pullbackComplexScheme f A) :=
  Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional
    f.toLRSHom.toShHom A hA

/-- **[Stacks, Tag 01CD] on total complexes**: `f^*Tot(A ⊗_{𝒪_Y} B) ≅ Tot(f^*A ⊗_{𝒪_X} f^*B)`,
the degreewise comparison of pullback with the tensor product assembled over the total
complex. -/
def pullbackTotalTensorComplexIso (A B : Stacks.Duality.TensorComplex Y) :
    pullbackComplexScheme f (Stacks.Duality.totalTensorComplex A B) ≅
      Stacks.Duality.totalTensorComplex (pullbackComplexScheme f A)
        (pullbackComplexScheme f B) :=
  (Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso
    f.toLRSHom.toShHom).app (A, B)

section Exact

variable [PreservesFiniteLimits (Scheme.Modules.pullback f)]
  [PreservesFiniteColimits (Scheme.Modules.pullback f)]

/-- **The class of the pullback of a K-flat representative.** If the class of `A` in `D(𝒪_Y)` is
`ℱ` placed in degree `0`, then the class of `f^*A` is `f^*ℱ` placed in degree `0`: an exact
functor descends to derived categories, carrying the class of a complex to the class of the
degreewise image and a module in degree `0` to its image in degree `0`. -/
def qPullbackComplexIso (F : Y.Modules) (A : Stacks.Duality.TensorComplex Y)
    (eA : (DerivedCategory.Q.obj A : DerivedCategory Y.Modules) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj F) :
    (DerivedCategory.Q.obj (pullbackComplexScheme f A) : DerivedCategory X.Modules) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj
        ((Scheme.Modules.pullback f).obj F) :=
  (((Scheme.Modules.pullback f).mapDerivedCategoryFactors).app A).symm ≪≫
    ((Scheme.Modules.pullback f).mapDerivedCategory).mapIso eA ≪≫
    (((Scheme.Modules.pullback f).mapDerivedCategorySingleFunctor 0)).app F

/-- **`f^*Tor_p^{𝒪_Y}(ℱ, 𝒢) ≅ Tor_p^{𝒪_X}(f^*ℱ, f^*𝒢)`, computed on chosen K-flat
representatives** `A` of `ℱ` and `B` of `𝒢`, for a morphism of schemes `f : X ⟶ Y` along which
`f^*` is exact.

Upstairs the representatives are `f^*A` and `f^*B`, the total tensor complex of those is the
pullback of the total tensor complex of `A` and `B`, and an exact functor commutes with the
cohomology of a complex. -/
def pullbackTorSheafIsoOfKFlat (F G : Y.Modules) (p : ℕ)
    (A B : Stacks.Duality.TensorComplex Y)
    (hA : Stacks.Duality.KFlatComplex A) (hB : Stacks.Duality.KFlatComplex B)
    (eA : (DerivedCategory.Q.obj A : DerivedCategory Y.Modules) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj F)
    (eB : (DerivedCategory.Q.obj B : DerivedCategory Y.Modules) ≅
      (DerivedCategory.singleFunctor Y.Modules 0).obj G) :
    (Scheme.Modules.pullback f).obj (torSheaf Y F G p) ≅
      torSheaf X ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj G) p :=
  (Scheme.Modules.pullback f).mapIso
      ((DerivedCategory.homologyFunctor Y.Modules (-(p : ℤ))).mapIso
        (derivedTensorIsoQTotal Y F G A B hA hB eA eB)) ≪≫
    (((Scheme.Modules.pullback f).mapDerivedCategoryHomologyIso (-(p : ℤ))).app
      (DerivedCategory.Q.obj (Stacks.Duality.totalTensorComplex A B))).symm ≪≫
    (DerivedCategory.homologyFunctor X.Modules (-(p : ℤ))).mapIso
      ((((Scheme.Modules.pullback f).mapDerivedCategoryFactors).app
        (Stacks.Duality.totalTensorComplex A B)) ≪≫
      DerivedCategory.Q.mapIso (pullbackTotalTensorComplexIso f A B) ≪≫
      (derivedTensorIsoQTotal X ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj G) (pullbackComplexScheme f A)
        (pullbackComplexScheme f B) (kFlatComplex_pullbackComplexScheme f A hA)
        (kFlatComplex_pullbackComplexScheme f B hB)
        (qPullbackComplexIso f F A eA) (qPullbackComplexIso f G B eB)).symm)

/-- **`f^*Tor_p^{𝒪_Y}(ℱ, 𝒢) ≅ Tor_p^{𝒪_X}(f^*ℱ, f^*𝒢)` when `f^*` is exact**, for a morphism of
schemes `f : X ⟶ Y` and arbitrary `𝒪_Y`-modules `ℱ` and `𝒢`. K-flat representatives of `ℱ` and
`𝒢` exist by [Stacks, Tag 06YS]; the comparison at a chosen pair of them is
`pullbackTorSheafIsoOfKFlat`. -/
def pullbackTorSheafIsoOfExact (F G : Y.Modules) (p : ℕ) :
    (Scheme.Modules.pullback f).obj (torSheaf Y F G p) ≅
      torSheaf X ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj G) p :=
  pullbackTorSheafIsoOfKFlat f F G p
    (exists_kFlatComplex_iso Y
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)).choose
    (exists_kFlatComplex_iso Y
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)).choose
    (exists_kFlatComplex_iso Y
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)).choose_spec.1
    (exists_kFlatComplex_iso Y
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)).choose_spec.1
    (exists_kFlatComplex_iso Y
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)).choose_spec.2.some
    (exists_kFlatComplex_iso Y
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)).choose_spec.2.some

end Exact

/-- **The Tor sheaves commute with flat pullback**: for a flat morphism of schemes
`f : X ⟶ Y` and arbitrary `𝒪_Y`-modules `ℱ` and `𝒢`,

`f^*Tor_p^{𝒪_Y}(ℱ, 𝒢) ≅ Tor_p^{𝒪_X}(f^*ℱ, f^*𝒢)`.

This is the comparison the proof of [Stacks, Tag 0B0Y] needs. Flatness of `f` is exactly left
exactness of `f^*`; right exactness holds for every morphism. -/
def pullbackTorSheafIso [Flat f] (F G : Y.Modules) (p : ℕ) :
    (Scheme.Modules.pullback f).obj (torSheaf Y F G p) ≅
      torSheaf X ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj G) p :=
  haveI : PreservesFiniteLimits (Scheme.Modules.pullback f) :=
    preservesFiniteLimits_modulesPullback_of_flat f
  haveI : PreservesFiniteColimits (Scheme.Modules.pullback f) :=
    AlgebraicGeometry.preservesFiniteColimits_modulesPullback f
  pullbackTorSheafIsoOfExact f F G p

end AlgebraicGeometry.TorFormula

end
