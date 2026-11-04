module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeNormalBundleIso
public import StacksFrontier.AlgebraicGeometry.Constructions.SymmetricAlgebraSheafFunctorial
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.RegularToQuasiRegular
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalQuasiRegularCriterion

/-!
# The normal cone of a quasi-regular immersion is its normal bundle

Let `i : Z ⟶ X` be an immersion of schemes. The canonical morphism `C_ZX ⟶ N_ZX` from the normal
cone `C_ZX = Spec_Z(𝒞_{Z/X,*})` to the normal bundle `N_ZX = Spec_Z(Sym(𝒞_{Z/X}))` is the relative
spectrum of the canonical map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` of Stacks 0632. When `i` is
quasi-regular, and in particular when it is regular, that map is an isomorphism in every degree
(Divisors, Lemma 31.22.5, Stacks 063M), so `C_ZX ⟶ N_ZX` is an isomorphism: the normal cone of a
regular immersion is the vector bundle of its conormal sheaf. This is the identification
`𝒞_{Z/X,*} = Sym(𝒞_{Z/X})` that the proof of Stacks 0FBM uses.

## Main results

* `Stacks.Conormal.isIso_normalConeToNormalBundle_of_isIso` — if `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is
  an isomorphism in every degree, then `C_ZX ⟶ N_ZX` is an isomorphism, the induced map of
  algebra sheaves being one by `Stacks.Conormal.isIso_conormalSymmetricAlgebraSheafHom`.
* `Stacks.Conormal.isIso_normalConeToNormalBundle_of_isQuasiRegularImmersion` and
  `Stacks.Conormal.isIso_normalConeToNormalBundle_of_isRegularImmersion` — `C_ZX ⟶ N_ZX` is an
  isomorphism for a quasi-regular, resp. regular, immersion.

## References

* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Tag 0632](https://stacks.math.columbia.edu/tag/0632)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- **`C_ZX ⟶ N_ZX` is an isomorphism as soon as `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is an isomorphism
in every degree**: it is the relative spectrum of an isomorphism of algebra sheaves. -/
theorem isIso_normalConeToNormalBundle_of_isIso
    (h : ∀ n : ℤ, IsIso ((conormalSymmetricHom i).app n)) :
    IsIso (normalConeToNormalBundle i) := by
  have := isIso_conormalSymmetricAlgebraSheafHom i h
  exact Stacks.RelativeSpec.isIso_relativeSpectrumMapOfAlgebraIso (normalBundleSituation i)
    (conormalAlgebraSheaf i) (isQuasicoherent_conormalAlgebraSheaf i)
    (asIso (conormalSymmetricAlgebraSheafHom i))

/-- **The normal cone of a quasi-regular immersion is its normal bundle.** For a quasi-regular
immersion the map `Sym*(𝒞_{Z/X}) ⟶ 𝒞_{Z/X,*}` is an isomorphism in every degree (Stacks 063M), so
the canonical morphism `C_ZX ⟶ N_ZX` of Stacks 0637 is an isomorphism. -/
theorem isIso_normalConeToNormalBundle_of_isQuasiRegularImmersion
    (h : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion i) :
    IsIso (normalConeToNormalBundle i) :=
  isIso_normalConeToNormalBundle_of_isIso i ((isQuasiRegularImmersion_iff i).mp h).2.2

/-- **The normal cone of a regular immersion is its normal bundle**: a regular immersion is
quasi-regular (Stacks 063I). -/
theorem isIso_normalConeToNormalBundle_of_isRegularImmersion
    (h : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) :
    IsIso (normalConeToNormalBundle i) :=
  isIso_normalConeToNormalBundle_of_isQuasiRegularImmersion i
    (Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isRegularImmersion i h)

end Stacks.Conormal

end
