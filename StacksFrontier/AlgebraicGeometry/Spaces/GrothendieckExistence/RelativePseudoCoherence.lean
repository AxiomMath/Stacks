module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDefinition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.Homology.Perfect.Saturation

/-!
# Relative pseudo-coherence of the derived limit of Situation 0CX4

In Situation [Stacks, Tag 0CX4] let `K = R lim_{D_QCoh(𝒪_X)}(Fₙ) = DQ_X(R lim_{D(𝒪_X)} Fₙ)` be
the object of [Stacks, Tag 0CX5]. [Stacks, Tag 0CX7] says that `K` is pseudo-coherent relative to
`A`, in the sense of [Stacks, Tag 0CSY] for the structure morphism `X ⟶ Spec A`.

The source's proof chains three results: [Stacks, Tag 0CX6] (1), that `RΓ(X, K ⊗^𝐋 E)` is perfect
in `D(A)` for every perfect `E`; [Stacks, Tag 0CWH], that pseudo-coherence of `RΓ(X, E ⊗^𝐋 K)`
for every perfect `E` gives it for every pseudo-coherent `E`; and [Stacks, Tag 0CTT], that the
latter makes `K` pseudo-coherent relative to `A`.

## Main results

In the namespace `AlgebraicGeometry.Space`:

* `FlatSheafExistenceSituation.isLocallyOfFiniteType_structureMorphism`: the structure morphism
  `X ⟶ Spec A` is locally of finite type.
* `FlatSheafExistenceSituation.isRelativelyPseudoCoherent_of_perfect_sections`: `K` is
  pseudo-coherent relative to `A`, for any derived global sections functor `RΓ` to `D(R)` and any
  derived tensor product, given the three cited results at `K`.

## Implementation notes

`K` is read through `DQ_X` as in `derivedLimit_bounded_of_affineCase`: for every coherator
`DQ_X`, right adjoint to the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, and every derived limit `L` of the
tower `(iₙ,* Fₙ)` in `D(𝒪_X)`, `K = DQ_X(L)`.

The derived categories are the standard models, `D(𝒪_X)` being `spaceDerivedCategory` and
`D(R)` its counterpart for modules: the locally small models `ModuleCat.hasDerivedCategory` and
`SheafOfModules.hasDerivedCategory` are switched off here, since relative pseudo-coherence
(`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`) and the coherator of Lemma 0CX5 are
stated at the standard model.

## References

* [Stacks Project, Tag 0CX7](https://stacks.math.columbia.edu/tag/0CX7)
* [Stacks Project, Tag 0CX6](https://stacks.math.columbia.edu/tag/0CX6)
* [Stacks Project, Tag 0CWH](https://stacks.math.columbia.edu/tag/0CWH)
* [Stacks Project, Tag 0CTT](https://stacks.math.columbia.edu/tag/0CTT)
* [Stacks Project, Tag 0CSY](https://stacks.math.columbia.edu/tag/0CSY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- The structure morphism `X ⟶ Spec A` of Situation 0CX4 is locally of finite type. -/
theorem isLocallyOfFiniteType_structureMorphism :
    IsLocallyOfFiniteType D.B D.S D.containsLimitBase D.X.hom.hom :=
  isLocallyOfFiniteType_of_isLocallyOfFinitePresentation _ _ _ D.finitePresentation.1

attribute [local instance] HasDerivedCategory.standard

/-- The object `K = DQ_X(L)` of [Stacks, Tag 0CX5], for a coherator `DQ_X` and an object `L` of
`D(𝒪_X)`, as an object of `D_QCoh(𝒪_X)`. -/
abbrev coheratorObj
    (DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory)
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left) :
    QuasicoherentDerivedCategory.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 :=
  ⟨(DQ.obj L).obj, (DQ.obj L).property⟩

/-- **Relative pseudo-coherence from perfect sections.** Let `K` be an object of
`D_QCoh(𝒪_X)`, `RΓ : D(𝒪_X) ⥤ D(R)` a derived global sections functor and `⊗` a derived tensor
product on `D(𝒪_X)`. Suppose that `RΓ(E ⊗ K)` is perfect for every perfect `E` (as in
[Stacks, Tag 0CX6] (1)); that pseudo-coherence of `RΓ(E ⊗ K)` for perfect `E` implies it for
pseudo-coherent `E` (as in [Stacks, Tag 0CWH]); and that the latter makes `K` pseudo-coherent
relative to `A` (as in [Stacks, Tag 0CTT]). Then `K` is pseudo-coherent relative to `A`. -/
theorem isRelativelyPseudoCoherent_of_perfect_sections {R : Type u} [CommRing R]
    (Γ : DerivedCategory (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2) ⥤
      DerivedCategory (ModuleCat.{u} R))
    (T : DerivedCategory (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2) ⥤
      DerivedCategory (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2) ⥤
        DerivedCategory (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2))
    (K : QuasicoherentDerivedCategory.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2)
    (h0CX6 : ∀ E : DerivedCategory
        (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2),
      (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).IsPerfect
      E → StacksDraft.Perfect.IsPerfect (Γ.obj ((T.obj E).obj K.obj)))
    (h0CWH : (∀ E : DerivedCategory
        (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2),
      (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1
        D.X.left.2).IsPerfect E →
          StacksDraft.PseudoCoherence.IsPseudoCoherent (Γ.obj ((T.obj E).obj K.obj))) →
      ∀ E : DerivedCategory (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2),
      (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1
        D.X.left.2).IsPseudoCoherent E →
          StacksDraft.PseudoCoherence.IsPseudoCoherent (Γ.obj ((T.obj E).obj K.obj)))
    (h0CTT : (∀ E : DerivedCategory
        (Modules.{u, u} D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2),
      (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1
        D.X.left.2).IsPseudoCoherent E →
          StacksDraft.PseudoCoherence.IsPseudoCoherent (Γ.obj ((T.obj E).obj K.obj))) →
      IsRelativelyPseudoCoherent D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 D.X.hom.hom
        D.isLocallyOfFiniteType_structureMorphism K) :
    IsRelativelyPseudoCoherent D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 D.X.hom.hom
      D.isLocallyOfFiniteType_structureMorphism K :=
  h0CTT (h0CWH fun E hE => StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _ (h0CX6 E hE))

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
