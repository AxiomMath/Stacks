module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeSpecClosedImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.SymmetricSituation.PowerEpi

/-!
# A surjection of modules gives a closed immersion of vector bundles

Let `X` be a scheme and `f : ℱ ⟶ 𝒢` a surjection of quasi-coherent `𝒪_X`-modules. Then
`Sym(f) : Sym(ℱ) ⟶ Sym(𝒢)` is surjective, and so the induced morphism of vector bundles

`𝐕(f) : 𝐕(𝒢) = Spec_X(Sym(𝒢)) ⟶ 𝐕(ℱ) = Spec_X(Sym(ℱ))`

is a closed immersion over `X`; that statement is
`AlgebraicGeometry.Scheme.Modules.isClosedImmersion_vectorBundleMap_of_epi`, proved over affine
charts. This file keeps the sheaf-level route: the surjectivity of `Sym(f)` and the identification
of `𝐕(f)` with the morphism of relative spectra induced by `Sym(f)`.

Surjectivity of `Sym(f)` is checked degree by degree. In each degree `Symⁿ(f)` is an
epimorphism: this is the epimorphy half of [Stacks, Tag 01CJ], available for the symmetric
algebra built as the sheafification of the sectionwise symmetric powers, and transported to the
symmetric algebra `Sym(ℱ)` the vector bundle is built from along the canonical isomorphisms
between two symmetric algebras of the same module. Degreewise local surjectivity then gives local
surjectivity of the ungraded realization, and the relative spectrum of a locally surjective
morphism of quasi-coherent algebra sheaves is a closed immersion.

## Main results

* `AlgebraicGeometry.Scheme.Modules.epi_symmetricAlgebraUnitalHom_app`: **`Symⁿ(f)` is an
  epimorphism in every degree when `f` is.**
* `AlgebraicGeometry.Scheme.Modules.isLocallySurjective_symmetricAlgebraSheafMap`: `Sym(f)` is
  locally surjective as a morphism of algebra sheaves.
* `AlgebraicGeometry.Scheme.Modules.vectorBundleMap_eq_relativeSpecMapOfAlgebraHom`: `𝐕(f)` is
  the morphism of relative spectra induced by `Sym(f)`.

## Implementation notes

The degreewise epimorphy is proved for `SheafOfModules.symmetricDescHom` in
`StacksFrontier.AlgebraicGeometry.SymmetricSituation.PowerEpi`, which is a homomorphism between the
symmetric algebras `SheafOfModules.sheafifiedSymmetricAlgebra`, while
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraUnitalHom` is a homomorphism between the
symmetric algebras `AlgebraicGeometry.Scheme.Modules.symmetricAlgebra`. Both pairs are symmetric
algebras of the same modules, so the uniqueness clause of the universal property writes the
second homomorphism as the first one conjugated by the comparison homomorphisms, which are
isomorphisms in every degree (`SheafOfModules.GradedAlgebra.IsUniversal.pieceIso`).

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) {F G : SheafOfModules.{u} X.ringCatSheaf}

/-- **The degree-`n` symmetric power of an epimorphism of `𝒪_X`-modules is an epimorphism**, for
the symmetric algebras the vector bundles are built from. -/
theorem epi_symmetricAlgebraUnitalHom_app (f : F ⟶ G) [Epi f] (n : ℤ) :
    Epi ((symmetricAlgebraUnitalHom X f).app n) := by
  have hF := isSymmetricAlgebra_symmetricAlgebra X F
  have hG := isSymmetricAlgebra_symmetricAlgebra X G
  have hF' := SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
    (Opens.grothendieckTopology (X : TopCat)) F
  have hG' := SheafOfModules.isSymmetricAlgebra_sheafifiedSymmetricAlgebra
    (Opens.grothendieckTopology (X : TopCat)) G
  set a := hF.isUniversal.desc _ _ hF'.1
  set b := SheafOfModules.symmetricDescHom (Opens.grothendieckTopology (X : TopCat)) f
  set c := hG'.isUniversal.desc _ _ hG.1
  have h1 : symmetricAlgebraGen X F ≫ a.app 1 =
      SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology (X : TopCat)) F :=
    hF.isUniversal.desc_extends _ _ hF'.1
  have h2 := SheafOfModules.symmetricDescHom_gen (Opens.grothendieckTopology (X : TopCat)) f
  have h3 :
      SheafOfModules.sheafifiedSymmetricGenerator (Opens.grothendieckTopology (X : TopCat)) G ≫
        c.app 1 = symmetricAlgebraGen X G :=
    hG'.isUniversal.desc_extends _ _ hG.1
  have hgen : symmetricAlgebraGen X F ≫ (a.app 1 ≫ b.app 1) ≫ c.app 1 =
      f ≫ symmetricAlgebraGen X G :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ c.app 1) ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ b.app 1) h1).trans h2))).trans
        ((Category.assoc _ _ _).trans (congrArg (f ≫ ·) h3)))
  have key : symmetricAlgebraUnitalHom X f = (a.comp b).comp c :=
    (SheafOfModules.GradedAlgebra.IsUniversal.descComp_unique hF.isUniversal f _ _ hgen).symm
  rw [key]
  show Epi ((a.app n ≫ b.app n) ≫ c.app n)
  have ha : Epi (a.app n) := (hF.isUniversal.pieceIso hF'.isUniversal n).isIso_hom.epi_of_iso
  have hc : Epi (c.app n) := (hG'.isUniversal.pieceIso hG.isUniversal n).isIso_hom.epi_of_iso
  have hb : Epi (b.app n) :=
    @SheafOfModules.epi_symmetricDescHom_app _ _ (Opens.grothendieckTopology (X : TopCat)) _ _ _ _
      _ _ f (by assumption) n
  exact @epi_comp _ _ _ _ _ _ (@epi_comp _ _ _ _ _ _ ha _ hb) _ hc

/-- **`Sym(f)` is locally surjective when `f` is an epimorphism**, as a morphism of the algebra
sheaves whose relative spectra are the vector bundles: every homogeneous component is an
epimorphism, hence locally surjective, and local surjectivity passes to the ungraded
realization. -/
theorem isLocallySurjective_symmetricAlgebraSheafMap (f : F ⟶ G) [Epi f] :
    Sheaf.IsLocallySurjective (symmetricAlgebraSheafMap X f).right :=
  Stacks.RelativeSpec.isLocallySurjective_gradedAlgebraSheafMap X (symmetricAlgebraUnitalHom X f)
    (symmetricAlgebra_mul_comm X F) (symmetricAlgebra_mul_comm X G) fun n =>
      have := epi_symmetricAlgebraUnitalHom_app X f n
      Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi _

variable [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- **`𝐕(f)` is the morphism of relative spectra induced by `Sym(f)`**: the morphism over `X`
classified by `Sym(f)` under the universal property of the vector bundle is the one the
contravariant functoriality of the relative spectrum attaches to `Sym(f)`. -/
theorem vectorBundleMap_eq_relativeSpecMapOfAlgebraHom (f : F ⟶ G) :
    vectorBundleMap X f =
      relativeSpecMapOfAlgebraHom (symmetricAlgebraSheaf X F) (symmetricAlgebraSheaf X G)
        (symmetricAlgebraSheafMap X f) := by
  have := isAffineHom_vectorBundleOver X (F := F)
  exact eq_of_pushforwardAlgebraMap_eq ((pushforwardAlgebraMap_vectorBundleMap X f).trans
    (pushforwardAlgebraMap_relativeSpecMapOfAlgebraHom _ _ _).symm)

end AlgebraicGeometry.Scheme.Modules

end
