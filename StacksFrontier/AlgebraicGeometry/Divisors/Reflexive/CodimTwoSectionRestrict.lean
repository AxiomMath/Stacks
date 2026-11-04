module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DivisorClassFaithful
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DepthCoherence.ReflexiveExtension
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OutsideImageDepth
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.StructureSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a reflexive module over a codimension-two open

Let `X` be a locally Noetherian normal scheme and let `V ⊆ X` be an open whose complement has
codimension at least two. A coherent reflexive `𝒪_X`-module has no sections and no relations
supported on that complement, so for *every* open `W ⊆ X` restriction

`Γ(W, ℱ) ⟶ Γ(V ∩ W, ℱ)`

is bijective. This is algebraic Hartogs extension ([Stacks, Tag 0E9I]) in the form the colimit
assertion of [Stacks, Tag 0EBN] needs: it is the step that carries an answer computed on `V` back
to `X`, both for the structure sheaf — where it compares `Γ(U ∩ W, 𝒪)` with `Γ(U ∩ V ∩ W, 𝒪)` —
and for the reflexive powers `ℱ^{[n]}`, where it compares `Γ(W, ℱ^{[n]})` with
`Γ(V ∩ W, ℱ^{[n]})`.

## Main results

* `AlgebraicGeometry.bijective_resF_inf_of_two_le_codimension`: **restriction to a
  codimension-two open is bijective on the sections of a coherent reflexive module**, over every
  open of the scheme.
* `AlgebraicGeometry.bijective_resF_inf_unit_of_two_le_codimension`: the structure-sheaf case,
  for which no reflexivity hypothesis has to be supplied.

## Implementation notes

Nothing is proved here that was not already available; what is new is the composite, which no
declaration previously stated. Its three links are
`Stacks.AlgebraicGeometry.PushforwardRegularity.bijective_resF_inf_of_isIso_unit`, which turns the
isomorphism `ℱ ≅ j_*(ℱ|_V)` into bijectivity of restriction over an arbitrary open;
`Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive`, which is that isomorphism for
a coherent reflexive module over an open whose complement carries depth at least two; and
`AlgebraicGeometry.two_le_depth_stalk_of_notMem_of_two_le_codimension`, which is where normality
enters — a normal local ring of dimension at least two has depth at least two, so the codimension
hypothesis of [Stacks, Tag 0AY6] (3) implies the depth hypothesis of [Stacks, Tag 0EBJ].

Integrality of `X` is not used, and is therefore not assumed, even though it is a standing
hypothesis of the section of the source this serves.

## References

* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace
open Stacks.AlgebraicGeometry.PushforwardRegularity (resF bijective_resF_inf_of_isIso_unit)
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive unitModule isReflexive_unit)

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] (V : X.Opens)

/-- **Restriction to an open whose complement has codimension at least two is bijective on the
sections of a coherent reflexive module**, over every open `W` of a locally Noetherian normal
scheme: a section of `ℱ` on `W` is determined by, and may be prescribed as, a section on
`V ∩ W`.

The codimension bound gives depth at least two off `V` because `X` is normal, the module is then
recovered from its restriction by Hartogs extension, and the unit of the adjunction is restriction
of sections. -/
@[ega "IV 19.9.8" "special case",
  ega "IV 21.13.4" "special case",
  sga "2 III 3.5" "(1) ⇒ (2), special case",
  sga "3 X 8.4" "extension of sections",
  sga "7 VIII 7.4" "more general"]
public theorem bijective_resF_inf_of_two_le_codimension
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (F : X.Modules) [_root_.SheafOfModules.IsCoherent F] (hF : IsReflexive F) (W : X.Opens) :
    Function.Bijective fun ξ : Γ(F, W) => resF F (inf_le_right : V ⊓ W ≤ W) ξ :=
  bijective_resF_inf_of_isIso_unit V F
    (Stacks.FundamentalGroup.DepthCoherence.isIso_unit_of_isReflexive V F hF
      (two_le_depth_stalk_of_notMem_of_two_le_codimension V hV)) W

/-- **The structure sheaf has the same sections over `W` as over `V ∩ W`**, for `V` an open of a
locally Noetherian normal scheme whose complement has codimension at least two. This is the
`ℱ = 𝒪_X` case of `AlgebraicGeometry.bijective_resF_inf_of_two_le_codimension`: the structure
sheaf is coherent on a locally Noetherian scheme and reflexive on any scheme, so neither
hypothesis has to be supplied. -/
public theorem bijective_resF_inf_unit_of_two_le_codimension
    (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (W : X.Opens) :
    Function.Bijective fun ξ : Γ(unitModule X, W) =>
      resF (unitModule X) (inf_le_right : V ⊓ W ≤ W) ξ :=
  have : _root_.SheafOfModules.IsCoherent (unitModule X) :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  bijective_resF_inf_of_two_le_codimension V hV (unitModule X) (isReflexive_unit X) W

end AlgebraicGeometry

end
