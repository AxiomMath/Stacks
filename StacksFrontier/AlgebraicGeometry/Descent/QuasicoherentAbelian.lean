module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent

/-!
# Colimits of quasi-coherent modules on an affine scheme

On the spectrum of a ring the associated-module functor `M ↦ M^~` is an equivalence onto the
quasi-coherent modules (`AlgebraicGeometry.tildeEquiv`) and it is a left adjoint, so it
preserves colimits.  Consequently a colimit of quasi-coherent modules on `Spec R` is
quasi-coherent, and so are coproducts and cokernels of quasi-coherent modules.

These are the affine cases of parts (1), (2) and the cokernel half of part (3) of
[Stacks, Tag 0GNB] and [Stacks, Tag 0GNC], which assert the same closure properties for
quasi-coherent modules on the small étale site, respectively the five big sites, of a scheme.

## Main results

* `Stacks.Descent.isQuasicoherent_colimit` states that a colimit of quasi-coherent modules on
  `Spec R` is quasi-coherent.
* `Stacks.Descent.isQuasicoherent_sigmaObj` states the same for a coproduct.
* `Stacks.Descent.isQuasicoherent_cokernel` states the same for a cokernel.

## Implementation notes

The diagram is lifted through the equivalence `AlgebraicGeometry.tildeEquiv`: a diagram of
quasi-coherent modules factors through the full subcategory of quasi-coherent modules, and
composing with the inverse of `tildeEquiv` produces a diagram of `R`-modules whose image under
`AlgebraicGeometry.tilde.functor` is isomorphic to the original diagram.  The colimit is then the
image of a colimit of `R`-modules, because `tilde.functor` is a left adjoint.

`isQuasicoherent_cokernel` is proved directly rather than as an instance of
`isQuasicoherent_colimit`, because `CategoryTheory.Limits.WalkingParallelPair` lives in `Type`
whereas `isQuasicoherent_colimit` is stated for diagrams indexed by a category in the scheme
universe.

The analogous statement for *kernels* is not proved here.  It is not a formal consequence of
`tildeEquiv` together with the adjunction: it amounts to exactness, rather than just right
exactness, of `tilde.functor`, i.e. to exactness of localization read off on the sections over
the basic opens.  Mathlib knows that localization commutes with kernels
(`LinearMap.toKerLocalized_isLocalizedModule`) but has no `PreservesFiniteLimits` instance for
`AlgebraicGeometry.tilde.functor`, so that route has to be built first.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Descent

variable {R : CommRingCat.{u}}

/-- The inverse of `AlgebraicGeometry.tildeEquiv` followed by the associated-module functor is
the inclusion of the quasi-coherent modules on `Spec R` into all modules. -/
noncomputable def tildeEquivInverseCompTilde :
    (tildeEquiv (R := R)).inverse ⋙ tilde.functor R ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) :=
  Functor.isoWhiskerRight (tildeEquiv (R := R)).counitIso (ObjectProperty.ι _)

/-- A module isomorphic to the associated module of an `R`-module is quasi-coherent. -/
private lemma isQuasicoherent_of_iso_tilde {M : (Spec R).Modules} {A : ModuleCat.{u} R}
    (e : (tilde.functor R).obj A ≅ M) : M.IsQuasicoherent :=
  isQuasicoherent_of_iso e inferInstance

/-- A colimit of quasi-coherent modules on an affine scheme is quasi-coherent.  This is the
affine case of parts (1) and (2) of Stacks 0GNB and 0GNC. -/
lemma isQuasicoherent_colimit {J : Type u} [SmallCategory J] (D : J ⥤ (Spec R).Modules)
    [∀ j, (D.obj j).IsQuasicoherent] : (colimit D).IsQuasicoherent := by
  let D' : J ⥤ (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
    ObjectProperty.lift _ D fun _ ↦ inferInstance
  let E : J ⥤ ModuleCat.{u} R := D' ⋙ (tildeEquiv (R := R)).inverse
  have e : E ⋙ tilde.functor R ≅ D :=
    Functor.isoWhiskerLeft D' tildeEquivInverseCompTilde
  exact isQuasicoherent_of_iso_tilde (preservesColimitIso (tilde.functor R) E ≪≫
    HasColimit.isoOfNatIso e)

/-- A coproduct of quasi-coherent modules on an affine scheme is quasi-coherent.  This is the
affine case of part (1) of Stacks 0GNB and 0GNC. -/
lemma isQuasicoherent_sigmaObj {ι : Type u} (M : ι → (Spec R).Modules)
    [∀ i, (M i).IsQuasicoherent] : (∐ M).IsQuasicoherent :=
  have (j : Discrete ι) : ((Discrete.functor M).obj j).IsQuasicoherent := inferInstanceAs
    (M j.as).IsQuasicoherent
  isQuasicoherent_colimit (Discrete.functor M)

/-- The cokernel of a morphism of quasi-coherent modules on an affine scheme is quasi-coherent.
This is the affine case of the cokernel half of part (3) of Stacks 0GNB and of part (3) of
Stacks 0GNC. -/
lemma isQuasicoherent_cokernel {M N : (Spec R).Modules} [hM : M.IsQuasicoherent]
    [hN : N.IsQuasicoherent] (f : M ⟶ N) : (cokernel f).IsQuasicoherent := by
  obtain ⟨A, ⟨eM⟩⟩ : (tilde.functor R).essImage M := by rw [essImage_tilde]; exact hM
  obtain ⟨B, ⟨eN⟩⟩ : (tilde.functor R).essImage N := by rw [essImage_tilde]; exact hN
  let g := (tilde.functor R).preimage (eM.hom ≫ f ≫ eN.inv)
  have hg : (tilde.functor R).map g = eM.hom ≫ f ≫ eN.inv := (tilde.functor R).map_preimage _
  have e : cokernel f ≅ cokernel ((tilde.functor R).map g) :=
    cokernel.mapIso _ _ eM.symm eN.symm (by rw [hg]; simp)
  exact isQuasicoherent_of_iso_tilde (PreservesCokernel.iso (tilde.functor R) g ≪≫ e.symm)

end Stacks.Descent

end
