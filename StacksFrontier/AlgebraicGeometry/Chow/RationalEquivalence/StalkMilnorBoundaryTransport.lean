module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorKSymbolTransport
public import StacksFrontier.AlgebraicGeometry.Chow.StalkMilnorBoundary

/-!
# The tame-symbol boundary of Stacks 0GU9 transported along an isomorphism of stalks

`Stacks.Chow.stalkMilnorBoundary` is the local component of the first differential of the complex
of Stacks 0GU9: for a point `z` of an integral locally Noetherian scheme `W` whose local ring is
one-dimensional, and an identification `e` of the function field of `W` with a field `K`, it is
the tame symbol of that local ring read through `e`.

This file records that the boundary depends on nothing but the local ring, the field `K` and the
structure map between them: an isomorphism of local rings compatible with an isomorphism of the
two fields carries one boundary to the other. It is `Stacks.Chow.milnorKTwoTameSymbol_ringEquiv`
read at the two scheme-theoretic presentations, with both transports rewritten as the functorial
transport `milnorKTransport` of
`StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.MilnorKSymbolTransport`, which is the
transport the chain maps of the degreewise localization sequence of Stacks 0GUA move chains by.

## Main results

* `Stacks.Chow.stalkMilnorBoundary_ringEquiv` — the boundary transported along an isomorphism of
  stalks compatible with an isomorphism of the ambient fields.
* `Stacks.Chow.stalkMilnorBoundary_point_congr` — the boundary transported along an equality of
  points.

## References

* [Stacks Project, Tag 0GU9](https://stacks.math.columbia.edu/tag/0GU9)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The isomorphism of residue fields induced by an isomorphism of the stalks at two points of
two schemes. This is `IsLocalRing.ResidueField.mapEquiv`, stated at the scheme-theoretic residue
fields `Stacks.Scheme.residueField`, whose field structure is the same one. -/
def residueFieldEquivOfStalkEquiv {W W' : Scheme.{u}} {z : W} {w : W'}
    (ε : ↥(W.presheaf.stalk z) ≃+* ↥(W'.presheaf.stalk w)) :
    ↥(W.residueField z) ≃+* ↥(W'.residueField w) :=
  IsLocalRing.ResidueField.mapEquiv ε

/-- The induced isomorphism of residue fields carries the residue of a germ to the residue of its
image. -/
theorem residueFieldEquivOfStalkEquiv_residue {W W' : Scheme.{u}} {z : W} {w : W'}
    (ε : ↥(W.presheaf.stalk z) ≃+* ↥(W'.presheaf.stalk w)) (a : ↥(W.presheaf.stalk z)) :
    residueFieldEquivOfStalkEquiv ε (W.residue z a) = W'.residue w (ε a) := by
  change IsLocalRing.ResidueField.mapEquiv ε (IsLocalRing.residue _ a) =
    IsLocalRing.residue _ (ε a)
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

/-- **The local boundary of Stacks 0GU9 is transported by an isomorphism of stalks.** Let `z` be
a point of `W` and `w` a point of `W'`, both with one-dimensional local ring, let
`ε : 𝒪_{W, z} ≃+* 𝒪_{W', w}` be an isomorphism, and let `η : K ≃+* L` be an isomorphism of the
two fields identified with the function fields, compatible with `ε` on germs. Then the square
formed by the two boundary maps, the transport along `η` in degree two and the transport along
the induced isomorphism of residue fields in degree one, commutes. -/
theorem stalkMilnorBoundary_ringEquiv {W' W : Scheme.{u}} [IsIntegral W'] [IsIntegral W]
    [IsLocallyNoetherian W'] [IsLocallyNoetherian W] {K L : Type u} [Field K] [Field L]
    (eW : ↥W.functionField ≃+* K) (eW' : ↥W'.functionField ≃+* L) (z : W) (w : W')
    (ε : ↥(W.presheaf.stalk z) ≃+* ↥(W'.presheaf.stalk w)) (η : K ≃+* L)
    (hcompat : ∀ a : ↥(W.presheaf.stalk z),
      η (eW (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField a)) =
        eW' (algebraMap ↥(W'.presheaf.stalk w) ↥W'.functionField (ε a)))
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1)
    (hdim' : ringKrullDim (W'.presheaf.stalk w) = 1) (α : MilnorKTheory K 2) :
    milnorKTransport (residueFieldEquivOfStalkEquiv ε : _ →+* _) 1
        (stalkMilnorBoundary eW z hdim α) =
      stalkMilnorBoundary eW' w hdim' (milnorKTransport (η : K →+* L) 2 α) := by
  let := stalkAlgebraOfFunctionFieldEquiv eW z
  let := stalkAlgebraOfFunctionFieldEquiv eW' w
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv eW z
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv eW' w
  have key := milnorKTwoTameSymbol_ringEquiv (A := ↥(W.presheaf.stalk z))
    (B := ↥(W'.presheaf.stalk w)) (K := K) (L := L) ε η
    (fun a ↦ by
      rw [algebraMap_stalkAlgebraOfFunctionFieldEquiv eW z a,
        algebraMap_stalkAlgebraOfFunctionFieldEquiv eW' w (ε a)]
      exact hcompat a) hdim hdim' α
  refine Eq.trans
    (milnorKTransport_eq_milnorKOneRingEquiv (residueFieldEquivOfStalkEquiv ε) _) ?_
  refine Eq.trans ?_ (congrArg (stalkMilnorBoundary eW' w hdim')
    (milnorKTransport_eq_milnorKTwoRingEquiv η α).symm)
  exact key

/-- **The local boundary of Stacks 0GU9 transported along an equality of points.** Transport along
an equality is the identity once the equality is substituted, and the two dimension hypotheses are
then the same proposition. -/
theorem stalkMilnorBoundary_point_congr {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
    {K : Type u} [Field K] (e : ↥W.functionField ≃+* K) {z z' : W} (hzz : z = z')
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1)
    (hdim' : ringKrullDim (W.presheaf.stalk z') = 1) (α : MilnorKTheory K 2) :
    milnorKTransport
        ((W.residueFieldCongr hzz).commRingCatIsoToRingEquiv :
          ↥(W.residueField z) →+* ↥(W.residueField z')) 1
        (stalkMilnorBoundary e z hdim α) = stalkMilnorBoundary e z' hdim' α := by
  subst hzz
  exact milnorKTransport_id_apply 1 _

end Stacks.Chow

end
