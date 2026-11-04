module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.UnramifiedTranslation
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Unramified

/-!
# A group scheme is unramified exactly when its tangent spaces along the unit vanish

Let `G` be a group scheme over a base `S`, locally of finite type. Then `G` is unramified over
`S` if and only if, for every point `s` of `S`, the relative tangent space `T_{G/S, e(s)}` at the
point `e(s)` of the unit section vanishes.

This is the step of the proof of Stacks 0E6G which reads unramifiedness of the automorphism group
scheme of a curve off its tangent space at the identity. The source passes through
`Ω_{G/S} = f^* e^* Ω_{G/S}` (Stacks 047I) and the description of the tangent space as the dual of
the differentials (Stacks 0B2D); here the homogeneity is the translation argument
`AlgebraicGeometry.unramifiedAt_of_forall_unramifiedAt_unit`, applied to the structure morphism
of `G` read as the homomorphism to the trivial group scheme, and the pointwise step is
`AlgebraicGeometry.subsingleton_dottedTangentArrow_iff_unramifiedAt`.

## Main results

* `AlgebraicGeometry.unramified_iff_forall_subsingleton_dottedTangentArrow_unit`: **a group
  scheme locally of finite type is unramified exactly when its relative tangent spaces along the
  unit section vanish.**
* `AlgebraicGeometry.unramified_iff_forall_dualNumber_point_eq_unit`: over a field `k`, the same
  read through `κ(e) = k`: **a group scheme locally of finite type over `k` is unramified exactly
  when every `k[ε]`-point restricting to the identity on `Spec k` is the identity**, that is, when
  the kernel of `G(k[ε]) ⟶ G(k)` is trivial.

## References

* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 047I](https://stacks.math.columbia.edu/tag/047I)
* [Stacks Project, Tag 0B2D](https://stacks.math.columbia.edu/tag/0B2D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

/-- **A group scheme locally of finite type is unramified exactly when its relative tangent
spaces along the unit section vanish.** For a group scheme `G` over `S` whose structure morphism
is locally of finite type, `G ⟶ S` is unramified if and only if `T_{G/S, e(s)} = 0` for every
point `s` of `S`, where `e` is the unit section. -/
theorem unramified_iff_forall_subsingleton_dottedTangentArrow_unit [LocallyOfFiniteType G.hom] :
    Unramified G.hom ↔ ∀ s : S, Subsingleton (DottedTangentArrow G.hom ((η[G]).left s)) := by
  simp only [subsingleton_dottedTangentArrow_iff_unramifiedAt, unramified_iff]
  refine ⟨fun h s => h _, fun h x => ?_⟩
  have hleft : (toUnit G).left = G.hom := Over.toUnit_left
  have : LocallyOfFiniteType (toUnit G).left := by rw [hleft]; infer_instance
  have hmul : (fst G G * snd G G) ≫ toUnit G = (fst G G ≫ toUnit G) * (snd G G ≫ toUnit G) :=
    toUnit_unique _ _
  have := unramifiedAt_of_forall_unramifiedAt_unit (toUnit G) hmul
    (fun s => by rw [hleft]; exact h s) x
  rwa [hleft] at this

/-- **A group scheme locally of finite type over a field is unramified exactly when the kernel of
`G(k[ε]) ⟶ G(k)` is trivial.** For a group scheme `G` over `Spec k` whose structure morphism is
locally of finite type, `G` is unramified over `k` if and only if every morphism
`α : Spec k[ε] ⟶ G` over `k` whose restriction to `Spec k ⊂ Spec k[ε]` is the identity `e` of `G`
is the constant point `Spec k[ε] ⟶ Spec k ⟶ G` at `e`. These `α` are the tangent vectors of `G`
at `e`, the residue field at `e` being `k`. -/
theorem unramified_iff_forall_dualNumber_point_eq_unit {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] :
    Unramified G.hom ↔ ∀ α : Spec (.of (DualNumber k)) ⟶ G.left,
      α ≫ G.hom = dualNumberToBase k →
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ α = (η[G]).left →
          α = dualNumberToBase k ≫ (η[G]).left := by
  have hσ : (η[G]).left ≫ G.hom = 𝟙 (Spec (.of k)) := Over.w (η[G])
  have hι : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ dualNumberToBase k =
      𝟙 _ := by
    rw [dualNumberToBase, ← Spec.map_comp, ← Spec.map_id]
    congr 1
  have key : Subsingleton (DottedTangentArrow G.hom ((η[G]).left (closedPoint k))) ↔
      ∀ α : Spec (.of (DualNumber k)) ⟶ G.left, α ≫ G.hom = dualNumberToBase k →
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ α = (η[G]).left →
          α = dualNumberToBase k ≫ (η[G]).left := by
    rw [(dottedTangentArrowEquivDualNumberPoints G.hom (η[G]).left hσ).subsingleton_congr]
    refine ⟨fun h α h1 h2 => congrArg Subtype.val (@Subsingleton.elim _ h ⟨α, h1, h2⟩
      ⟨dualNumberToBase k ≫ (η[G]).left, by rw [Category.assoc, hσ, Category.comp_id],
        by rw [← Category.assoc, hι, Category.id_comp]⟩),
      fun h => ⟨fun a b => Subtype.ext ((h a.1 a.2.1 a.2.2).trans (h b.1 b.2.1 b.2.2).symm)⟩⟩
  rw [unramified_iff_forall_subsingleton_dottedTangentArrow_unit]
  refine ⟨fun h => key.mp (h _), fun h s => ?_⟩
  obtain rfl : s = closedPoint k := Subsingleton.elim _ _
  exact key.mpr h

end AlgebraicGeometry
