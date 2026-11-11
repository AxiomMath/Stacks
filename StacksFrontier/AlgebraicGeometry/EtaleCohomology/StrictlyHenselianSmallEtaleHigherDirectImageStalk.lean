module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleHigherDirectImageStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a higher direct image over a strictly henselian local base

Let `R` be a strictly henselian local ring, let `x : Spec Ω ⟶ Spec R` be a geometric point lying
over the closed point and let `f : X ⟶ Spec R` be an arbitrary morphism of schemes. For an
abelian sheaf `F` on the small étale site of `X` and any degree `n`, the stalk of `R^n f_* F` at
`x` is the étale cohomology group `H^n(X_étale, F)`.

This is [Stacks, Tag 03Q9] at a base that is already strictly henselian local at the point: the
strict henselisation `𝒪^{sh}_{Spec R, x}` is `R` itself, the base change
`X ×_{Spec R} Spec(𝒪^{sh}_{Spec R, x})` is `X`, the projection `p` is the identity and the
source's right hand side `H^n(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}F)` is `H^n(X_étale, F)`. The
source's hypothesis `f` quasi-compact and quasi-separated is not needed and is not assumed.

## Main results

* `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoCohomologyClosedPoint` — the stalk
  of `R^n f_* F` at such a point is `H^n(X_étale, F)`.

## Implementation notes

Nothing cohomological happens here. Over a strictly henselian local base the étale
neighbourhoods of a geometric point above the closed point have an **initial** object, namely the
final object of `(Spec R)_étale` with the point itself as its lift
(`Stacks.EtaleCohomology.isInitialPointSmallEtaleClosedPointElement`), so the filtered colimit of
`Stacks.EtaleCohomology.isColimitSmallEtaleHigherDirectImageStalkCocone` — the first step of the
source's proof, which holds over an arbitrary base — is attained at that one index. The hypothesis
`h03Q6` of `Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoOfIsColimit` is therefore
discharged, not carried, and [Stacks, Tag 03Q6] is not used: this is
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoCohomologyOfIsInitial` instantiated at
that initial neighbourhood. Over a base at which the neighbourhood category does not degenerate
`X ×_S Spec(𝒪^{sh}_{S,s})` is a proper limit of the `X ×_S V` and Tag 03Q6 is needed; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleHigherDirectImageStalk.lean`.

**Why this is not a second registration of the tag.** [Stacks, Tag 03Q9] is registered in this
model, over an arbitrary base and for `f` quasi-compact and quasi-separated, as
`AlgebraicGeometry.stalkHigherDirectImageIso` (with its complex and derived-category forms
`AlgebraicGeometry.stalkDerivedPushforwardHomologyIso` and
`AlgebraicGeometry.stalkDerivedPushforwardIso`). The statement below is the degenerate case of a
strictly henselian local base, where the right hand side is `H^n(X_étale, F)` itself and no
hypothesis on `f` is needed; it carries no tag of its own. The form over any base at which the
étale neighbourhoods of the geometric point have an initial object, of which a strictly henselian
local base is one case, is
`Stacks.EtaleCohomology.smallEtaleHigherDirectImageStalkIsoSectionsOfIsInitial`.

**The residue field.** The geometric point is taken with `IsAlgClosed Ω` rather than
`IsSepClosed Ω`: the initiality input routes through
`AlgebraicGeometry.exists_hom_of_strictlyHenselian`, whose point is an
`AlgebraicGeometry.GeometricPoint`, and that structure carries an algebraically closed residue
field in this library. Separable closedness is what the statement needs mathematically and is
what `Stacks.EtaleCohomology.smallEtaleStalkAb` asks for; the stronger hypothesis is inherited
from the available initiality lemma and is not used anywhere else below.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 03Q9] over a strictly henselian local base, in the
`AlgebraicGeometry.Scheme.Etale` model of the small étale site.** For `R` strictly henselian
local, `x : Spec Ω ⟶ Spec R` a geometric point lying over the closed point, `f : X ⟶ Spec R` an
arbitrary morphism of schemes, `F` an arbitrary abelian sheaf on `X_étale` and `n` an arbitrary
degree, the stalk of `R^n f_* F` at `x` is the étale cohomology group `H^n(X_étale, F)`.

Over such a base `𝒪^{sh}_{Spec R, x} = R`, so the source's right hand side
`H^n(X ×_S Spec(𝒪^{sh}_{S,s}), p^{-1}F)` is `H^n(X_étale, F)`; the source's hypothesis `f`
quasi-compact and quasi-separated is not needed. [Stacks, Tag 03Q6] is not used: the étale
neighbourhoods of `x` have an initial object, so the colimit of the first step of the source's
proof is attained there. -/
@[sga "4½ Arcata 2.3.3" "special case"]
def smallEtaleHigherDirectImageStalkIsoCohomologyClosedPoint
    {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [HasSheafify X.smallEtaleTopology Ab.{u + 1}]
    [HasSheafify (Spec (.of R)).smallEtaleTopology Ab.{u + 1}]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology Ab.{u + 1})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R))
    (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)
    (F : Sheaf X.smallEtaleTopology Ab.{u + 1}) (n : ℕ) :
    (smallEtaleStalkAb x).obj (((etaleAbelianDirectImage.{u, u + 1} f).rightDerived n).obj F) ≅
      ((Sheaf.Γ X.smallEtaleTopology Ab.{u + 1}).rightDerived n).obj F :=
  smallEtaleHigherDirectImageStalkIsoCohomologyOfIsInitial f x F n
    (isInitialPointSmallEtaleClosedPointElement x hx) (isTerminalEtaleMkId (Spec (.of R)))

end Stacks.EtaleCohomology

end
