module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialFlatResolution

/-!
# Derived extension of scalars along an augmentation is computed on a flat resolution

Let `C` be a site, let `A_•` be a simplicial sheaf of commutative rings on it and let
`ε : A_• ⟶ O` be an augmentation. Derived extension of scalars along `ε`,

`Lε^* = - ⊗^𝐋_{A_•} O : D(A_•) ⟶ D(π^{-1}O)`,

is `Stacks.SimplicialModules.derivedBaseChangeToProjectionRing`, the derived pullback of
[Stacks, Tag 06YY] along the change of coefficient rings `A_• ⟶ π^{-1}O` on `Δ × C`. On a
cochain complex `L^•` of simplicial `A_•`-modules which is bounded above and has flat terms,
`Lε^*(Q L^•)` is the image in `D(π^{-1}O)` of the degreewise extension of scalars
`L^• ⊗_{A_•} π^{-1}O`, naturally in `L^•`; and every object of `D(A_•)` bounded above is of that
form.

## Main definitions

* `Stacks.SimplicialModules.augmentationToposHom`: the augmentation read as a morphism of ringed
  topoi on `Δ × C`, the change of coefficient rings along `A_• ⟶ π^{-1}O`.
* `Stacks.SimplicialModules.augmentationBaseChangeComplex`: **`- ⊗_{A_•} π^{-1}O` on complexes**,
  degreewise extension of scalars along the augmentation.
* `Stacks.SimplicialModules.augmentationBaseChangeFlatIso`: **the representation.**
  `Lε^*(Q L^•) ≅ Q(L^• ⊗_{A_•} π^{-1}O)` for a bounded above `L^•` with flat terms.

## Main results

* `Stacks.SimplicialModules.augmentationBaseChangeComplex_eq_extendScalars`: the degreewise
  functor is extension of scalars along `ε`.
* `Stacks.SimplicialModules.augmentationBaseChangeFlatIso_hom_naturality`: **the representation
  is natural in the complex.**
* `Stacks.SimplicialModules.exists_flatRepresentative_derivedBaseChange_of_isLE`: an object of
  `D(A_•)` bounded above by `n` has a representative which is strictly bounded above by `n` and
  has flat terms, and on it the representation applies; so `Lε^*(K)` is `Q` of a degreewise
  extension of scalars.

## Implementation notes

The comparison is `Stacks.Sheaves.DerivedPullback.flatPullbackIso`, whose hypothesis is K-flat
with flat terms, applied through [Stacks, Tag 06YQ]
(`Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat`); the bounded above flat representative
is `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE`.

Naturality is in the complex, not in the object of `D(A_•)`: an object of `D(A_•)` has no
functorial bounded above flat representative, since `exists_flatRepresentative_of_isLE` is an
existence statement.

## References

* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3), the functor whose first
  factor `Lε^*` is.
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY), the derived pullback and
  its computation on a K-flat complex with flat terms.
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ), a bounded above complex
  of flat modules is K-flat.
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW), flat modules cover.
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), simplicial modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback
open Stacks.Sheaves.DerivedPullback.KFlatPullback

universe u

namespace Stacks.SimplicialModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A : SimplicialObject (Sheaf J CommRingCat.{u})} {O : Sheaf J CommRingCat.{u}}
  (ε : A ⟶ (Functor.const SimplexCategoryᵒᵖ).obj O)

/-- **The augmentation `ε : A_• ⟶ O` as a morphism of ringed topoi on `Δ × C`**: the change of
coefficient rings along `A_• ⟶ π^{-1}O`, whose underlying morphism of sites is the identity of
`Δ × C`. This is the morphism whose derived pullback is
`Stacks.SimplicialModules.derivedBaseChangeToProjectionRing`. -/
abbrev augmentationToposHom : RingedToposSiteHom
    (Stacks.Cohomology.ringedTopos (projectionTopology C J) (projectionCommRing J O))
    (Stacks.Cohomology.ringedTopos (projectionTopology C J) (simplicialCommRingSheaf J A)) :=
  RingedToposSiteHom.coefficientChange.{u, u, u} (projectionTopology C J)
    (augmentationCommRingMap J ε)

/-- **`- ⊗_{A_•} π^{-1}O` on complexes**: degreewise extension of scalars along the augmentation,
from cochain complexes of simplicial `A_•`-modules to cochain complexes of sheaves of
`π^{-1}O`-modules. -/
abbrev augmentationBaseChangeComplex :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.ringedTopos (projectionTopology C J)
          (simplicialCommRingSheaf J A)).O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (projectionRingSheaf J O)) ℤ :=
  pullbackComplex.{u} (augmentationToposHom J ε)

/-- **The degreewise functor is extension of scalars along the augmentation.** The pullback of
sheaves of modules along a change of coefficient rings is extension of scalars
(`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_coefficientChange`), so
`augmentationBaseChangeComplex` is `- ⊗_{A_•} π^{-1}O` applied in each degree. -/
theorem augmentationBaseChangeComplex_eq_extendScalars :
    augmentationBaseChangeComplex J ε =
      (Stacks.Sheaves.ModuleAdjunction.extendScalars.{u}
        ((augmentationToposHom J ε).fSharpRing)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  rfl

/-- **The representation of `Lε^*` on a bounded above complex with flat terms.** For a cochain
complex `L^•` of simplicial `A_•`-modules which vanishes in degrees `> n` and all of whose terms
are flat,

`Lε^*(Q L^•) ≅ Q(L^• ⊗_{A_•} π^{-1}O)`.

Such a complex is K-flat by [Stacks, Tag 06YQ], and on a K-flat complex with flat terms the
canonical comparison of [Stacks, Tag 06YY] is invertible. -/
def augmentationBaseChangeFlatIso
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.Cohomology.ringedTopos (projectionTopology C J) (simplicialCommRingSheaf J A)).O)) ℤ)
    (n : ℤ)
    (hLE : L.IsStrictlyLE n)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := simplicialCommRingSheaf J A) (L.X i)) :
    (derivedBaseChangeToProjectionRing J ε).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((augmentationBaseChangeComplex J ε).obj L) :=
  flatPullbackIso (augmentationToposHom J ε) (Functor.isMorphismOfSites_id _) L
    (Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat.{u, u, u} _ L ⟨n, hLE⟩ hflat) hflat

/-- **The representation is natural in the complex.** A map of cochain complexes of simplicial
`A_•`-modules, both vanishing in degrees `> n` and both with flat terms, gives a commuting square
between the derived extension of scalars of the two and the degreewise extension of scalars of
the two. -/
lemma augmentationBaseChangeFlatIso_hom_naturality
    {L L' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.Cohomology.ringedTopos (projectionTopology C J) (simplicialCommRingSheaf J A)).O)) ℤ}
    (n : ℤ)
    (hLE : L.IsStrictlyLE n) (hLE' : L'.IsStrictlyLE n)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := simplicialCommRingSheaf J A) (L.X i))
    (hflat' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := simplicialCommRingSheaf J A) (L'.X i)) (g : L ⟶ L') :
    (derivedBaseChangeToProjectionRing J ε).map (DerivedCategory.Q.map g) ≫
        (augmentationBaseChangeFlatIso J ε L' n hLE' hflat').hom =
      (augmentationBaseChangeFlatIso J ε L n hLE hflat).hom ≫
        DerivedCategory.Q.map ((augmentationBaseChangeComplex J ε).map g) :=
  flatPullbackIso_naturality (augmentationToposHom J ε) (Functor.isMorphismOfSites_id _) g _ _
    hflat hflat'

/-- **`Lε^*(K)` is `Q` of a degreewise extension of scalars, for every `K` in `D(A_•)` bounded
above.** An object of `D(A_•)` whose cohomology vanishes in degrees `> n` is represented by a
cochain complex `L^•` of simplicial `A_•`-modules vanishing in degrees `> n` with flat terms
(`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE`, which rests
on [Stacks, Tag 03EW]), and on such a complex `Lε^*` is computed degreewise, so

`Lε^*(K) ≅ Q(L^• ⊗_{A_•} π^{-1}O)`.

The isomorphism is only asserted to exist, and no naturality in `K` is claimed. -/
theorem exists_flatRepresentative_derivedBaseChange_of_isLE
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.Cohomology.ringedTopos (projectionTopology C J) (simplicialCommRingSheaf J A)).O)))
    (n : ℤ) (hK : K.IsLE n) :
    ∃ (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.ringedTopos (projectionTopology C J) (simplicialCommRingSheaf J A)).O))
        ℤ)
      (_ : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
        (O := simplicialCommRingSheaf J A) (L.X i)) (_ : L.IsStrictlyLE n),
      Nonempty ((derivedBaseChangeToProjectionRing J ε).obj K ≅
        DerivedCategory.Q.obj ((augmentationBaseChangeComplex J ε).obj L)) := by
  obtain ⟨L, hflat, hLLE, ⟨e⟩⟩ :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE
      (Stacks.Cohomology.ringedTopos (projectionTopology C J)
        (simplicialCommRingSheaf J A)).toRingedSite K n hK
  exact ⟨L, hflat, hLLE, ⟨(derivedBaseChangeToProjectionRing J ε).mapIso e.symm ≪≫
    augmentationBaseChangeFlatIso J ε L n hLLE hflat⟩⟩

end Stacks.SimplicialModules

end
