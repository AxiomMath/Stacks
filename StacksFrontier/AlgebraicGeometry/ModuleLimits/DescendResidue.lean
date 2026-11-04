module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineFaithful
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.DescendUpToIso

/-!
# Finitely presented modules on a limit, from descent of morphisms up to isomorphism

Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine transition
morphisms and let `c` be a limit cone on it. This file proves that every finitely presented
module on `c.pt` is the pullback of a finitely presented module on some stage
([Stacks Project, Tag 01ZR] (1)), assuming only descent of morphisms
([Stacks Project, Tag 01ZR] (2)) in the form where the descended morphism agrees with the given
one through *some* pair of isomorphisms.

## Main results

* `exists_isFinitePresentation_pullback_iso_of_upToIso_map`, in the namespace
  `Stacks.AlgebraicGeometry.ModuleLimits`: Tag 01ZR (1) for a cofiltered system of
  quasi-compact and quasi-separated schemes with affine transition morphisms, from descent of
  morphisms up to an arbitrary identification.
* `exists_isFinitePresentation_pullback_iso_of_colim_and_upToIso_map`, in the same namespace: the
  same conclusion, with the presentation of quasi-coherent modules as directed colimits of
  finitely presented ones ([Stacks Project, Tag 01PK]) as an additional hypothesis.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {I : Type u} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- Let `D` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition morphisms and `c` a limit cone on it. If morphisms between pullbacks of finitely
presented modules descend to some stage, compatibly through *some* pair of isomorphisms (`hmap`,
a form of [Stacks Project, Tag 01ZR] (2)), then every finitely presented module on `c.pt` is
isomorphic to the pullback of a finitely presented module on some stage
([Stacks Project, Tag 01ZR] (1)). -/
theorem exists_isFinitePresentation_pullback_iso_of_upToIso_map
    [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hmap : ∀ (i : I) (F G : (D.obj i).Modules),
      F.IsFinitePresentation → G.IsFinitePresentation →
      ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj G,
      ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G)
        (iF : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj F) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj F)
        (iG : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj G) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj G),
        (Scheme.Modules.pullback (c.π.app j)).map φj ≫ iG.hom = iF.hom ≫ φ)
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) :=
  exists_isFinitePresentation_pullback_iso_of_upToIso_inputs D c hc affineCounitEpi hmap F

/-- The conclusion of `exists_isFinitePresentation_pullback_iso_of_upToIso_map`, under the
additional hypothesis `_hcolim` that every quasi-coherent module on a quasi-compact
quasi-separated scheme is a directed colimit of finitely presented ones
([Stacks Project, Tag 01PK]). The hypothesis `_hcolim` is not needed for the conclusion. -/
theorem exists_isFinitePresentation_pullback_iso_of_colim_and_upToIso_map
    [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (_hcolim : ∀ (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] (N : Z.Modules),
      N.IsQuasicoherent →
      ∃ (J : Type u) (_ : PartialOrder J) (_ : Nonempty J) (_ : IsDirected J (· ≤ ·))
        (E : J ⥤ Z.Modules) (φ : E ⟶ (Functor.const J).obj N),
        (∀ j, (E.obj j).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk N φ)))
    (hmap : ∀ (i : I) (F G : (D.obj i).Modules),
      F.IsFinitePresentation → G.IsFinitePresentation →
      ∀ φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
        (Scheme.Modules.pullback (c.π.app i)).obj G,
      ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G)
        (iF : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj F) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj F)
        (iG : (Scheme.Modules.pullback (c.π.app j)).obj
              ((Scheme.Modules.pullback (D.map e)).obj G) ≅
            (Scheme.Modules.pullback (c.π.app i)).obj G),
        (Scheme.Modules.pullback (c.π.app j)).map φj ≫ iG.hom = iF.hom ≫ φ)
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) :=
  exists_isFinitePresentation_pullback_iso_of_upToIso_map D c hc hmap F

end Stacks.AlgebraicGeometry.ModuleLimits

end
