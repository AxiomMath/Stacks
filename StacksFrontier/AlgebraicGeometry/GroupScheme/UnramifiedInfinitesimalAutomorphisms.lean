module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.UnramifiedTangentIdentity
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsDerivations

/-!
# A group scheme of automorphisms is unramified exactly when there are no derivations

Let `k` be a field, `X` a scheme over `k` and `G` a group scheme locally of finite type over `k`.
Suppose the `k[ε]`-points of `G` restricting to the identity `e` over `Spec k` correspond to the
infinitesimal automorphisms of `X`: the self-maps of a first-order deformation `X'` of `X` over
`k[ε]` (for instance the trivial one `X ×_{Spec k} Spec k[ε]`) over the base and restricting to
the identity of `X`. This is what `G = Aut(X)` provides. Then `G` is unramified over `k` if and
only if `Der_k(𝒪_X, 𝒪_X) = 0`. This is the argument of Stacks 0E6G: `G` is unramified exactly when
its tangent space at `e` vanishes (Stacks 02G5, 047I, 0B2D), its tangent vectors are those
`k[ε]`-points, and the infinitesimal automorphisms of `X` are the `k`-derivations of `𝒪_X`
(Stacks 0DY9).

## Main results

* `AlgebraicGeometry.unramified_iff_subsingleton_derivations_of_equiv`: given a bijection between
  the `k[ε]`-points of `G` over `e` and the infinitesimal automorphisms of `X`, `G` is unramified
  over `k` exactly when `Der_k(𝒪_X, 𝒪_X)` vanishes.

## References

* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 047I](https://stacks.math.columbia.edu/tag/047I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

open Deformation Deformation.Examples

/-- **The tangent-space step of Stacks 0E6G.** Let `G` be a group scheme locally of finite type
over a field `k`, and `X` a scheme over `k` with a first-order deformation `P` over `k[ε]`. If the
`k[ε]`-points of `G` lying over the identity `e` correspond bijectively to the self-maps of the
total space of `P` over its base that restrict to the identity of `X`, then `G` is unramified over
`k` if and only if every `k`-derivation of `𝒪_X` into itself vanishes. -/
theorem unramified_iff_subsingleton_derivations_of_equiv {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {X : Over (Spec (.of k))} (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (coordinate : P.base ≃ₐ[Λ] DualNumber k)
    (φ : { α : Spec (.of (DualNumber k)) ⟶ G.left // α ≫ G.hom = dualNumberToBase k ∧
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ α = (η[G]).left } ≃
      { e : P.scheme ⟶ P.scheme // e ≫ P.toBase = P.toBase ∧ P.specialMap ≫ e = P.specialMap }) :
    Unramified G.hom ↔
      Subsingleton (schemeMorphismDerivations (Λ := Λ) (k := k) (𝟙 X.left) X.hom) := by
  have hσ : (η[G]).left ≫ G.hom = 𝟙 (Spec (.of k)) := Over.w (η[G])
  have hι : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ dualNumberToBase k =
      𝟙 _ := by
    rw [dualNumberToBase, ← Spec.map_comp, ← Spec.map_id]
    congr 1
  let α₀ : { α : Spec (.of (DualNumber k)) ⟶ G.left // α ≫ G.hom = dualNumberToBase k ∧
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ α = (η[G]).left } :=
    ⟨dualNumberToBase k ≫ (η[G]).left, by rw [Category.assoc, hσ, Category.comp_id],
      by rw [← Category.assoc, hι, Category.id_comp]⟩
  rw [unramified_iff_forall_dualNumber_point_eq_unit,
    ← (deformationSelfMapsEquivDerivations P coordinate).subsingleton_congr,
    ← φ.subsingleton_congr]
  exact ⟨fun h => ⟨fun a b => Subtype.ext <| (h a.1 a.2.1 a.2.2).trans (h b.1 b.2.1 b.2.2).symm⟩,
    fun h α h₁ h₂ => congrArg Subtype.val (@Subsingleton.elim _ h ⟨α, h₁, h₂⟩ α₀)⟩

end AlgebraicGeometry

end
