module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.HasCompactification
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# A maximal compactifiable open subspace of a Noetherian algebraic space

Let `X` be a Noetherian algebraic space over `S` and `f : X ⟶ Y` a morphism of algebraic
spaces. The open subspaces of `X` correspond to the open subsets of the Noetherian topological
space `|X|`, and these satisfy the ascending chain condition. Hence if some open subspace
`U₀ ⊆ X` has a compactification over `Y`, there is an open subspace `U ⊇ U₀` with a
compactification over `Y` which is maximal among such: no strictly larger open subspace of `X`
has a compactification over `Y`. Since `U₀ ⊆ U`, density of `U₀` passes to `U`.

This is the Noetherian induction of the proof of Nagata's compactification theorem for
algebraic spaces: there one starts from a dense open affine `U₀`, and shows that a maximal `U`
must be all of `X`.

## Main results

* `AlgebraicGeometry.Space.exists_maximal_isOpenSubspace_hasCompactification`: a compactifiable
  open subspace is contained in a maximal one.

## References

* [Stacks Project, Tag 0F4D](https://stacks.math.columbia.edu/tag/0F4D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Noetherian induction for compactifiable open subspaces.** Let `X` be a Noetherian
algebraic space and `f : X ⟶ Y`. If an open subspace `U₀` of `X` has a compactification over
`Y`, then there is an open subspace `U ⊇ U₀` with a compactification over `Y` such that no open
subspace strictly containing `U` has one. -/
theorem exists_maximal_isOpenSubspace_hasCompactification (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hN : IsNoetherian B S hS hZ X) (f : X ⟶ Y) (U₀ : Subfunctor X)
    (hU₀ : IsOpenSubspace B S hS U₀) (hU₀f : HasCompactification B S hS (U₀.ι ≫ f)) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧ U₀ ≤ U ∧
      HasCompactification B S hS (U.ι ≫ f) ∧
      ∀ W : Subfunctor X, IsOpenSubspace B S hS W → U < W →
        ¬ HasCompactification B S hS (W.ι ≫ f) := by
  let := pointTopology B S hS X
  have : NoetherianSpace (points B S hS X) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X hX hN.1 hN.2.2
  let e := openSubspacesOrderIso B S hS X hX
  let s : Set (Opens (points B S hS X)) :=
    {V | ∃ W : {G : Subfunctor X // IsOpenSubspace B S hS G},
      e W = V ∧ U₀ ≤ W.1 ∧ HasCompactification B S hS (W.1.ι ≫ f)}
  obtain ⟨V, ⟨W, rfl, hW₀, hWf⟩, hmax⟩ := (wellFounded_gt (α := Opens (points B S hS X))).has_min
    s ⟨e ⟨U₀, hU₀⟩, ⟨U₀, hU₀⟩, rfl, le_rfl, hU₀f⟩
  exact ⟨W.1, W.2, hW₀, hWf, fun W' hW' hlt hW'f => hmax (e ⟨W', hW'⟩)
    ⟨⟨W', hW'⟩, rfl, hW₀.trans hlt.le, hW'f⟩ (e.strictMono (show W < ⟨W', hW'⟩ from hlt))⟩

end AlgebraicGeometry.Space

end
