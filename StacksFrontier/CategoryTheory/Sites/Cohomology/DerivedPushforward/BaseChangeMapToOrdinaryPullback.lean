module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOnRingedTopoi

/-!
# The base change map into the pushforward of an ordinary pullback

Let

```
                g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
        |  f'                |  f
        v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
                g
```

be a commutative diagram of ringed topoi.  The derived base change map of
[Stacks, Tag 07A7] is `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`, with the *derived* pullback
`L(g')^*` on the right.  Composing it with `Rf'_*` of the canonical comparison
`L(g')^* K ⟶ (g')^* K` of [Stacks, Tag 06YY] gives the map

`Lg^* Rf_* K ⟶ Rf'_* (g')^* K`

into the derived pushforward of the *ordinary* — degreewise — pullback.  That composition is
the construction [Stacks, Tag 07MS] prescribes, whose hint reads: compose the very general base
change map of Cohomology on Sites, Remark 07A7 with the canonical map
`Lf_{cris}^* ℱ' ⟶ f_{cris}^* ℱ' = ℱ`.

The comparison `L(g')^* ⟶ (g')^*` is a morphism of functors out of the *homotopy* category, so
the composite is taken at an object `M` of `K(𝒪_C)` rather than at an object of `D(𝒪_C)`; the
source of the map is then `Lg^* Rf_*` of the image of `M` in `D(𝒪_C)`.  For `M` a module in
degree zero this is the first displayed map of [Stacks, Tag 07MS], with its right hand side
`Rf'_*` of the ordinary pullback of that module.

## Main definitions

* `derivedBaseChangeMapToOrdinaryPullback` — the composite base change map
  `Lg^* Rf_* M ⟶ Rf'_* (g')^* M`.

## Main results

* `derivedBaseChangeMapToOrdinaryPullback_eq` — its defining factorization, through the base
  change map of [Stacks, Tag 07A7].
* `derivedBaseChangeMapToOrdinaryPullback_naturality` — it is natural in the object of the
  homotopy category.

## Implementation notes

*Why this is stated for a square of `AlgebraicGeometry.RingedToposSiteHom`.*  Both inputs are:
the base change map of [Stacks, Tag 07A7] is
`Stacks.Cohomology.DerivedBaseChangeOnTopoi.derivedBaseChangeMap`, and the comparison of
[Stacks, Tag 06YY] is
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison`; both are
stated for morphisms of ringed topoi presented by a morphism of the underlying sites, over
`AlgebraicGeometry.RingedTopos` with its three universes collapsed.  The collapse is inherited,
not chosen here; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/BaseChangeOnRingedTopoi.lean`.

*Why [Stacks, Tag 07MS] is not instantiated from this file.*  The tag instantiates the square at
`f := τ_{X'/S'}`, `g' := f_{cris}`, `f' := τ_{X/S}` and `g` the small Zariski morphism of
`S ⟶ S'`, with `τ` the structure morphism of [Stacks, Tag 07IM] and `f_{cris}` the morphism of
[Stacks, Tag 07IK].  Those four morphisms exist in this library, as
`Crystalline.GlobalCrystallineSituation.structureToposMorphism`,
`Crystalline.GlobalCrystallineSituation.crisMorphism` and
`StacksZariskiSite.opensMapMorphismOfTopoi`, but they are
`StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi` of topoi of sheaves of *sets* and not
morphisms of ringed topoi of the above shape (morphisms presented by continuous functors of
sites, at collapsed universes), and the instantiation *in this shape* is blocked at four
independent places:

1. the small crystalline site has its objects one universe above its morphisms —
   `Crystalline.GlobalCrystallineSituation.CrystallineThickening S : Type (u + 1)` with
   `Category.{u}` — so it is not a `AlgebraicGeometry.RingedTopos.{w, w, w}` for any `w`, which
   is the only shape the derived pullback and pushforward of this tree are available for;
2. the crystalline comparison `u_{X/S}` of [Stacks, Tag 07IL],
   `Crystalline.GlobalCrystallineSituation.zariskiToposMorphism`, has for its direct image the
   *cocontinuous* pushforward `Functor.sheafPushforwardCocontinuous` along the forgetful functor
   `Cris(X/S) ⥤ X_{Zar}`, whereas the direct image of a `RingedToposSiteHom` is restriction
   along a continuous functor in the opposite direction; so neither `τ_{X/S}` nor `f_{cris}`,
   which is a threefold composite mixing the two kinds, is of that shape;
3. no structure map `𝒪 ⟶ f_* 𝒪` is available for either `τ_{X/S}` or `f_{cris}`: the structure
   sheaf of the small crystalline site is
   `Crystalline.GlobalCrystallineSituation.SmallSite.commStructureSheaf`, and nothing compares it
   with the structure sheaf of another crystalline situation along `f_{cris}`, nor with
   `𝒪_S` along `τ_{X/S}`.  Even packaging the pair as an
   `AlgebraicGeometry.RingedToposHom`, the variant of [Stacks, Tag 01D3] built on a
   `MorphismOfTopoi` and the one whose universes are free enough, would first need that
   structure sheaf transported to `CommRingCat.{u + 1}`: the underlying topos of an
   `AlgebraicGeometry.RingedTopos` is its sheaves of sets at the universe of the sections of its
   structure sheaf, and the crystalline topos
   `Crystalline.GlobalCrystallineSituation.smallTopos` is `Sheaf _ (Type (u + 1))` while
   `commStructureSheaf` takes values in `CommRingCat.{u}`;
4. the base change map of [Stacks, Tag 07A7] consumes a strict equality of composites
   `g ∘ f' = f ∘ g'`, and the crystalline square commutes only up to canonical isomorphism: the
   two composite direct images are built from `sheafPushforwardCocontinuous` on one side and
   `sheafPushforwardContinuous` on the other, compared by
   `CategoryTheory.Functor.sheafPushforwardContinuousComp`, which is an isomorphism and not an
   equality.

All four are resolved for the two-field morphisms of ringed topoi of Stacks 01D3 (2), where
Stacks 07MS is constructed: see the closing section of this file.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.DerivedBaseChangeOnTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

section Square

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (g' : RingedToposSiteHom X' X)
  (f' : RingedToposSiteHom X' Y') (g : RingedToposSiteHom Y' Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f.comp g')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

/-- **The base change map into the pushforward of the ordinary pullback.**  For a commutative
square of ringed topoi and an object `M` of the homotopy category of `𝒪_C`-modules, the
composite of the derived base change map `Lg^* Rf_* M ⟶ Rf'_* L(g')^* M` of
[Stacks, Tag 07A7] with `Rf'_*` of the canonical comparison `L(g')^* M ⟶ (g')^* M` of
[Stacks, Tag 06YY].

This is the composition [Stacks, Tag 07MS] prescribes.  Its target is the derived pushforward of
the degreewise pullback of `M`, so for `M` a single module in degree zero it is
`Lg^* Rf_* ℱ' ⟶ Rf'_* ((g')^* ℱ')`, the pullback of `ℱ'` on the right being the ordinary
one. -/
def derivedBaseChangeMapToOrdinaryPullback (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (h : g.comp f' = f.comp g')
    (M : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (derivedPullback g).obj ((derivedPushforward f).obj (DerivedCategory.Qh.obj M)) ⟶
      (derivedPushforward f').obj ((pullbackOnHomotopy g').obj M) :=
  derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg h (DerivedCategory.Qh.obj M) ≫
    (derivedPushforward f').map ((derivedPullbackComparison g').app M)

/-- The defining factorization of the composite base change map: the base change map of
[Stacks, Tag 07A7], followed by the derived pushforward of the canonical comparison from the
derived to the degreewise pullback. -/
theorem derivedBaseChangeMapToOrdinaryPullback_eq (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (h : g.comp f' = f.comp g')
    (M : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    derivedBaseChangeMapToOrdinaryPullback f g' f' g hmosf hmosg' hmosf' hmosg h M =
      derivedBaseChangeMap f g' f' g hmosf hmosg' hmosf' hmosg h (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f').map ((derivedPullbackComparison g').app M) :=
  rfl

/-- **The composite base change map is natural** in the object of the homotopy category of
`𝒪_C`-modules: both of its factors are, the first by
`Stacks.Cohomology.DerivedBaseChangeOnTopoi.derivedBaseChangeMap_naturality` and the second
because the comparison of [Stacks, Tag 06YY] is a morphism of functors. -/
theorem derivedBaseChangeMapToOrdinaryPullback_naturality
    (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosg' : g'.u.IsMorphismOfSites X.J X'.J)
    (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J) (hmosg : g.u.IsMorphismOfSites Y.J Y'.J)
    (h : g.comp f' = f.comp g')
    {M N : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)} (e : M ⟶ N) :
    (derivedPullback g).map ((derivedPushforward f).map (DerivedCategory.Qh.map e)) ≫
        derivedBaseChangeMapToOrdinaryPullback f g' f' g hmosf hmosg' hmosf' hmosg h N =
      derivedBaseChangeMapToOrdinaryPullback f g' f' g hmosf hmosg' hmosf' hmosg h M ≫
        (derivedPushforward f').map ((pullbackOnHomotopy g').map e) := by
  have hnat := (derivedPullbackComparison g').naturality e
  rw [Functor.comp_map] at hnat
  rw [derivedBaseChangeMapToOrdinaryPullback_eq, derivedBaseChangeMapToOrdinaryPullback_eq,
    ← Category.assoc, derivedBaseChangeMap_naturality f g' f' g hmosf hmosg' hmosf' hmosg h
      (DerivedCategory.Qh.map e), Category.assoc, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, hnat]

/-- **The degreewise pullback of a module in degree zero.**  Degreewise pullback along `g'`
carries the complex with `ℱ'` in degree zero to the complex with the ordinary pullback
`(g')^* ℱ'` in degree zero, as objects of the homotopy category.

This is `HomologicalComplex.singleMapHomologicalComplex` for the additive functor `(g')^*`; what
makes it an isomorphism rather than an equality is that `(g')^*` takes the zero module to a zero
module only up to isomorphism. -/
def homotopyPullbackSingleIso
    (F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (g'.pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (0 : ℤ)).obj F') ≅
      (HomotopyCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) (0 : ℤ)).obj
        (g'.pullbackTopos.obj F') :=
  (g'.pullbackTopos.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) (0 : ℤ)).obj F') ≪≫
    (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O))
        (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex g'.pullbackTopos
        (ComplexShape.up ℤ) (0 : ℤ)).app F')

/-- **The base change map of [Stacks, Tag 07MS] at a module.**  For a commutative square of
ringed topoi and an `𝒪_C`-module `ℱ'`, the map

`Lg^* Rf_* ℱ' ⟶ Rf'_* ((g')^* ℱ')`

in `D(𝒪_{D'})`, both modules being read in degree zero and `(g')^* ℱ'` being the *ordinary*
pullback — "the pullback of `ℱ'`" in the language of the tag.

It is `derivedBaseChangeMapToOrdinaryPullback` at the complex with `ℱ'` in degree zero, with the
two ends transported along the comparison
`DerivedCategory.singleFunctorIsoCompQh` of the single functor into the derived category with the
single functor into the homotopy category, and the target further identified by
`homotopyPullbackSingleIso`. -/
def derivedBaseChangeMapOfModule (hmosf : f.u.IsMorphismOfSites Y.J X.J)
    (hmosg' : g'.u.IsMorphismOfSites X.J X'.J) (hmosf' : f'.u.IsMorphismOfSites Y'.J X'.J)
    (hmosg : g.u.IsMorphismOfSites Y.J Y'.J) (h : g.comp f' = f.comp g')
    (F' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (derivedPullback g).obj ((derivedPushforward f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (0 : ℤ)).obj F')) ⟶
      (derivedPushforward f').obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) (0 : ℤ)).obj
          (g'.pullbackTopos.obj F')) :=
  (derivedPullback g).map ((derivedPushforward f).map
      ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (0 : ℤ)).hom.app F')) ≫
    derivedBaseChangeMapToOrdinaryPullback f g' f' g hmosf hmosg' hmosf' hmosg h
      ((HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (0 : ℤ)).obj F') ≫
    (derivedPushforward f').map
      (DerivedCategory.Qh.map (homotopyPullbackSingleIso g' F').hom) ≫
    (derivedPushforward f').map
      ((DerivedCategory.singleFunctorIsoCompQh
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) (0 : ℤ)).inv.app
        (g'.pullbackTopos.obj F'))

end Square

end

end Stacks.Cohomology.DerivedBaseChangeOnTopoi

/-! ### Stacks 07MS

The construction above is for squares of morphisms of ringed topoi presented by continuous
functors of sites.  Stacks 07MS itself is registered on
`Crystalline.GlobalCrystallineSituation.SmallSite.crisSheafBaseChangeMap`
(`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapSheaf07MS.lean`), which carries
out the same composition — the base change map of Tag 07A7 followed by the comparison of
Tag 06YY — for the crystalline square of morphisms of ringed topoi in the two-field sense, where
the four obstructions listed in the implementation notes above do not arise: the universes of the
two-field ringed topoi are free, their morphisms are morphisms of topoi, the structure maps of
`τ_{X/S}` and `f_cris` are constructed, and the square is allowed to commute up to a
2-isomorphism.
-/

end
