module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Reduced

/-!
# Geometric properties are properties of the geometric fibres

Mathlib's `AlgebraicGeometry.geometrically P` asks that `X ×_S Spec K` satisfy `P` for every
field `K` over `S`. The Stacks project phrases such conditions through the *geometric fibres*
`X ×_S Spec k`, `Spec k ⟶ S` a geometric point, i.e. `k` algebraically closed
([Stacks, Tag 03PO]). The two agree as soon as `P` passes from the source to the target of a flat
surjective morphism: embed `K` in its algebraic closure `Ω`; the projection
`X ×_S Spec Ω ⟶ X ×_S Spec K` is a base change of `Spec Ω ⟶ Spec K`, hence flat and surjective.

## Main results

* `AlgebraicGeometry.geometrically_iff_forall_isAlgClosed`: the general statement.
* `AlgebraicGeometry.geometricallyIntegral_iff_forall_isAlgClosed`: a morphism is geometrically
  integral iff its geometric fibres are integral.
* `AlgebraicGeometry.geometricallyReduced_iff_forall_isAlgClosed`: likewise for reduced.
* `AlgebraicGeometry.geometricallyConnected_iff_forall_isAlgClosed`: likewise for connected.

Reducedness descends along flat surjective morphisms by `isReduced_of_flat_of_surjective`
([Stacks, Tag 06QM]); irreducibility and connectedness pass to the image of any continuous
surjection.

## References

* [Stacks Project, Tag 03PO](https://stacks.math.columbia.edu/tag/03PO)
* [Stacks Project, Tag 06QM](https://stacks.math.columbia.edu/tag/06QM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A geometric property is a property of the geometric fibres.** If `P` is invariant under
isomorphism and passes from the source to the target of flat surjective morphisms, then `f` is
geometrically `P` (`X ×_S Spec K` has `P` for every field `K` over `S`) if and only if
`X ×_S Spec k` has `P` for every algebraically closed field `k` and every `Spec k ⟶ S`. -/
theorem geometrically_iff_forall_isAlgClosed (P : ObjectProperty Scheme.{u})
    [P.IsClosedUnderIsomorphisms]
    (hP : ∀ ⦃Y Z : Scheme.{u}⦄ (p : Y ⟶ Z) [Flat p] [Surjective p], P Y → P Z)
    {X S : Scheme.{u}} (f : X ⟶ S) :
    geometrically P f ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S), P (pullback f s) := by
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  refine ⟨fun h k _ _ s ↦ h k s, fun h K _ y ↦ ?_⟩
  let g : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  have : Flat g := Flat.SpecMap_iff.2 (RingHom.Flat.of_isField (Field.toIsField K) _)
  exact hP (pullback.fst (pullback.snd f y) g) (P.prop_of_iso
    (pullbackLeftPullbackSndIso f y g).symm (h (AlgebraicClosure K) (g ≫ y)))

/-- **Geometric integrality is integrality of the geometric fibres.** A morphism `f : X ⟶ S`
is geometrically integral if and only if `X ×_S Spec k` is integral for every algebraically
closed field `k` and every `Spec k ⟶ S`, i.e. the geometric fibres of `f` are integral. -/
theorem geometricallyIntegral_iff_forall_isAlgClosed {X S : Scheme.{u}} (f : X ⟶ S) :
    GeometricallyIntegral f ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
        IsIntegral (pullback f s) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsIntegral ·) :=
    ⟨fun e h ↦ have := h; IsIntegral.of_isIso e.hom⟩
  rw [geometricallyIntegral_iff]
  refine geometrically_iff_forall_isAlgClosed _ (fun Y Z p _ _ (_ : IsIntegral Y) ↦ ?_) f
  have : IsReduced Z := isReduced_of_flat_of_surjective p
  have : IrreducibleSpace ↥Z := Function.Surjective.irreducibleSpace p.continuous p.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

/-- **Geometric reducedness is reducedness of the geometric fibres.** A morphism `f : X ⟶ S`
is geometrically reduced if and only if `X ×_S Spec k` is reduced for every algebraically
closed field `k` and every `Spec k ⟶ S`, i.e. the geometric fibres of `f` are reduced. -/
theorem geometricallyReduced_iff_forall_isAlgClosed {X S : Scheme.{u}} (f : X ⟶ S) :
    GeometricallyReduced f ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
        IsReduced (pullback f s) := by
  rw [geometricallyReduced_iff]
  exact geometrically_iff_forall_isAlgClosed _
    (fun Y Z p _ _ (_ : IsReduced Y) ↦ isReduced_of_flat_of_surjective p) f

/-- **Geometric connectedness is connectedness of the geometric fibres.** A morphism
`f : X ⟶ S` is geometrically connected if and only if `X ×_S Spec k` is connected (in
particular nonempty) for every algebraically closed field `k` and every `Spec k ⟶ S`, i.e. the
geometric fibres of `f` are connected. -/
theorem geometricallyConnected_iff_forall_isAlgClosed {X S : Scheme.{u}} (f : X ⟶ S) :
    GeometricallyConnected f ↔
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
        ConnectedSpace ↥(pullback f s) := by
  rw [geometricallyConnected_iff]
  exact geometrically_iff_forall_isAlgClosed _
    (fun Y Z p _ _ (_ : ConnectedSpace ↥Y) ↦
      Function.Surjective.connectedSpace p.surjective p.continuous) f

end AlgebraicGeometry

end
