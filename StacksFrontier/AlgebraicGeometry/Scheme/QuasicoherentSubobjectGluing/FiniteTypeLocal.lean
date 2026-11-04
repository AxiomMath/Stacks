module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local

/-!
# Being of finite type is local on a scheme

A module `M` on a scheme `X` whose restriction to every member of an open covering of `X` is of
finite type is itself of finite type. This is the finite type counterpart of
`Stacks.Modules.isQuasicoherent_of_restrict`.

Finite type is defined by the existence of a covering of the terminal object together with
finitely many generating sections over each member, so it is local by construction — but only in
the *slice* formulation, where the generators live on `M.over V` for `V` an object of the site.
The restriction `M.restrict V.ι` to an open subscheme is a different presentation of the same
object, and passing between the two is what this file supplies. In one direction that was already
available as `Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsOver`; the other direction,
`Stacks.AlgebraicGeometry.CoherentFinite.generatingSectionsOfOver`, is used here by transporting
generating sections along the equivalence `AlgebraicGeometry.Scheme.Modules.overEquiv` — which
preserves colimits and carries the structure sheaf to the structure sheaf — this time along its
functor rather than its inverse.

With both directions in hand the locality statement follows from the pointwise criterion
`Stacks.SheafOfModules.isFiniteType_iff_forall_isFiniteTypeAt`: a point of `X` lies in some member
`U` of the covering, finite type of `M.restrict U.ι` produces finitely many generating sections
over an open `V` of `U` containing it, and `AlgebraicGeometry.Scheme.Hom.isoImage` identifies `V`
with the open `U.ι ''ᵁ V` of `X`, over which those sections generate `M`.

## Main results

* `AlgebraicGeometry.isFiniteType_of_restrict` — being of finite type is local on the base.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Stacks.AlgebraicGeometry

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}}

/-- **Being of finite type is local on the base.** A module on a scheme whose restriction to
every member of an open covering is of finite type is of finite type.

This is the finite type counterpart of `Stacks.Modules.isQuasicoherent_of_restrict`. Note that
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_restrict_generatingSections` is a weaker
statement: it asks for finitely many generating sections *globally* over each member of the
covering, whereas finite type of a restriction only provides them locally. -/
theorem isFiniteType_of_restrict (M : X.Modules) {I : Type*} (U : I → X.Opens)
    (hU : iSup U = ⊤) (h : ∀ i, (M.restrict (U i).ι).IsFiniteType) :
    M.IsFiniteType := by
  apply Stacks.SheafOfModules.isFiniteType_of_forall_isFiniteTypeAt
  intro x
  have hx : x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  obtain ⟨V₀, hxV, σ, hσ⟩ := Stacks.SheafOfModules.isFiniteTypeAt_of_isFiniteType
    (M.restrict (U i).ι) (h i) (⟨x, hxi⟩ : (U i).toScheme)
  let V : (U i).toScheme.Opens := V₀
  -- the open of `X` cut out by `V`, and the identification of the two open subschemes
  let W : X.Opens := (U i).ι ''ᵁ V
  let φ : V.toScheme ≅ W.toScheme := (U i).ι.isoImage V
  have hcomp : V.ι ≫ (U i).ι = φ.hom ≫ W.ι := (Scheme.Hom.isoImage_hom_ι _ _).symm
  have heq : φ.inv ≫ (φ.hom ≫ W.ι) = W.ι := by rw [Iso.inv_hom_id_assoc]
  -- transport the generators from the slice presentation to `M.restrict W.ι`
  let τ₀ : ((M.restrict (U i).ι).restrict V.ι).GeneratingSections :=
    Stacks.AlgebraicGeometry.CoherentFinite.generatingSectionsOfOver V (M.restrict (U i).ι) σ
  let τ₁ : (M.restrict (V.ι ≫ (U i).ι)).GeneratingSections :=
    (GeneratingSections.equivOfIso
      ((Scheme.Modules.restrictFunctorComp V.ι (U i).ι).app M)).symm τ₀
  let τ₂ : (M.restrict (φ.hom ≫ W.ι)).GeneratingSections :=
    GeneratingSections.equivOfIso ((Scheme.Modules.restrictFunctorCongr hcomp).app M) τ₁
  let τ₃ : ((M.restrict (φ.hom ≫ W.ι)).restrict φ.inv).GeneratingSections :=
    CoherentTFAE.generatingSectionsRestrict φ.inv τ₂
  let τ₄ : (M.restrict W.ι).GeneratingSections :=
    (GeneratingSections.equivOfIso
      (((Scheme.Modules.restrictFunctorCongr heq).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorComp φ.inv (φ.hom ≫ W.ι)).app M)).symm τ₃
  exact ⟨W, ⟨⟨x, hxi⟩, hxV, rfl⟩, CoherentTFAE.generatingSectionsOver W M τ₄, ⟨hσ.finite⟩⟩

end AlgebraicGeometry

end
