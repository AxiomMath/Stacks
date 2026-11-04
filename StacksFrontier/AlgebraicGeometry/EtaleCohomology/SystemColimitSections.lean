module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsAtQcqsObjects
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Basic
public import StacksFrontier.CategoryTheory.Limits.SystemColimitLift

/-!
# Sections of a colimit of a system of étale sheaves

Let `X` be a scheme, let `(G_i, T_{ij})` be a system of abelian sheaves on the small étale site
of `X` indexed by a directed set, satisfying the cocycle condition but not necessarily the
identity law, and let `𝓕` be its colimit. Then for every object `V` of the small étale site whose
underlying scheme is quasi-compact and quasi-separated, the sections `𝓕(V)` are the colimit of
the system of sections `G_i(V)`.

This is the degree zero case of Stacks 0739 on the small étale site, read for systems: the system
is a functor on the filtered category `CategoryTheory.Limits.SystemLift I`, and its colimit is
the colimit of the system (`CategoryTheory.Limits.SystemLift.isSystemColimit_iff`).

## Main results

* `Stacks.EtaleCohomology.isSystemColimit_sections_of_isSystemColimit`: the sections over an
  object with quasi-compact and quasi-separated underlying scheme of a colimit of a system of
  abelian sheaves are the colimit of the system of sections.

## References

* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

noncomputable section

variable {X : Scheme.{u}} {I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]

/-- **Sections of a colimit of a system of étale sheaves over a quasi-compact quasi-separated
object.** Let `X` be a scheme and let `ι_i : G_i ⟶ 𝓕` exhibit an abelian sheaf `𝓕` on the small
étale site of `X` as the colimit of a system `(G_i, T_{ij})` over a directed set satisfying the
cocycle condition. Then for every object `V` whose underlying scheme is quasi-compact and
quasi-separated the maps `ι_i(V) : G_i(V) ⟶ 𝓕(V)` exhibit `𝓕(V)` as the colimit of the system
`(G_i(V))`. -/
theorem isSystemColimit_sections_of_isSystemColimit
    {G : Iᵒᵖ → Sheaf X.smallEtaleTopology Ab.{u + 1}} {T : ∀ {i j : Iᵒᵖ}, (i ⟶ j) → (G j ⟶ G i)}
    (hT : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k), T (a ≫ b) = T b ≫ T a)
    {𝓕 : Sheaf X.smallEtaleTopology Ab.{u + 1}} {ι : ∀ i, G i ⟶ 𝓕}
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), T a ≫ ι i = ι j) (h : IsSystemColimit G T 𝓕 ι)
    (V : X.Etale) (hV : V ∈ qcqsEtaleObjects X) :
    IsSystemColimit
      (fun i => ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj (op V)).obj (G i))
      (fun a => ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj (op V)).map (T a))
      (((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj (op V)).obj 𝓕)
      (fun i => ((sheafSections X.smallEtaleTopology Ab.{u + 1}).obj (op V)).map (ι i)) := by
  obtain ⟨hc⟩ := (SystemLift.isSystemColimit_iff hT ι hι).mp h
  let S := (sheafSections X.smallEtaleTopology Ab.{u + 1}).obj (op V)
  refine IsSystemColimit.of_isColimit_mapCocone hT hι S ?_
  let F := SystemLift.functor G (fun a => T a) hT
  let e : AsSmall.{u + 1} (SystemLift I) ≌ SystemLift I := AsSmall.equiv.symm
  let F' := e.functor ⋙ F
  have : IsFiltered (AsSmall.{u + 1} (SystemLift I)) := IsFiltered.of_equivalence AsSmall.equiv
  have h₀ := isIso_colimit_post_rightDerived_sheafSections_of_qcqs.{0} 0 V hV F'
  have : IsIso (colimit.post F' S) :=
    Stacks.Cohomology.isIso_colimit_post_of_natIso F' _ _ (Functor.rightDerivedZeroIsoSelf S)
  have : PreservesColimit F' S := preservesColimit_of_isIso_post S F'
  exact (IsColimit.whiskerEquivalenceEquiv e).symm
    ((isColimitOfPreserves S (IsColimit.whiskerEquivalenceEquiv e hc)).ofIsoColimit
      S.mapCoconeWhisker)

end

end Stacks.EtaleCohomology
