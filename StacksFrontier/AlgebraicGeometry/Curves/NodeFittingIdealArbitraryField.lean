module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsDifferentials
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-!
# The Fitting ideal at a node over an arbitrary base field

Let `k` be a field, let `X` be a scheme locally of finite type over `k` and let `x` be a node of
`X`.  Then the first Fitting ideal of `Ω_{X/k}` generates the maximal ideal of `𝒪_{X,x}`, over an
arbitrary base field; equivalently, the local ring at `x` of the closed subscheme `Z ⊆ X` cut out
by that Fitting ideal is the residue field `κ(x)`.

This is the Fitting clause of the implication (1) ⟹ (4) of Stacks Tag 0C4D, and is the step "for
every point `x ∈ Z` the local ring `𝒪_{Z,x}` is equal to `κ(x)`" of the proof of the implication
(1) ⟹ (2) of Tag 0C4E.  Over an algebraically closed field it is
`Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_of_isNode_of_isAlgClosed`; what is proved here
is the general case, by descent along the base change to the algebraic closure.

## Main results

* `AlgebraicGeometry.stalk_fittingIdeal_relativeDifferentials_of_isPullback` — the stalk of the
  Fitting ideal sheaf of the relative differentials of a base change is the image of the stalk
  downstairs.
* `Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_of_isNode` — the Fitting clause of the
  implication (1) ⟹ (4) of Tag 0C4D over an arbitrary base field.

## Implementation notes

Formation of the Fitting ideal sheaf of the relative differentials commutes with base change
(Tag 0C3I, `AlgebraicGeometry.fittingIdeal_relativeDifferentials_comap`), and the stalk of an
inverse image ideal sheaf is the image of the stalk
(`AlgebraicGeometry.IdealSheafData.stalk_comap`).  Together they say that the stalk of the
Fitting ideal upstairs is `I · 𝒪_{X_{k̄},x̄}` for `I` the stalk downstairs.

By definition a node carries a point `x̄` of `X_{k̄}` above `x` which is an ordinary double point,
hence a closed point whose local ring is a nodal algebra, hence a node of `X_{k̄}` over the
algebraically closed field `k̄`.  There the Fitting clause is available, so
`I · 𝒪_{X_{k̄},x̄} = 𝔪_{x̄}`.  Since `I ≤ 𝔪_x` and the stalk map is local, this is squeezed
between `I · 𝒪_{X_{k̄},x̄}` and `𝔪_x · 𝒪_{X_{k̄},x̄}`, so those two agree; the stalk map is flat
— the base change is along the flat morphism `Spec k̄ ⟶ Spec k` — and local, hence faithfully
flat, and extension of ideals along a faithfully flat map is injective.

The hypothesis that the stalk of the Fitting ideal at `x` is proper is the one carried by the
algebraically closed case, and for the same reason: it is automatic at a node, but deriving it
there would need the node condition to obstruct smoothness, which is a different argument.  At
a point of `Z` it is free, by
`AlgebraicGeometry.IdealSheafData.stalk_le_maximalIdeal_subschemeι`.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **The stalk of the Fitting ideal sheaf of the relative differentials of a base change.**  In
a cartesian square with right edge `f : X ⟶ S` locally of finite type, left edge `f' : X' ⟶ S'`
and top edge `g' : X' ⟶ X`, the stalk at `x'` of the `r`-th Fitting ideal sheaf of `Ω_{X'/S'}` is
the ideal generated in `𝒪_{X',x'}` by the stalk at `g' x'` of the `r`-th Fitting ideal sheaf of
`Ω_{X/S}`.

This is Tag 0C3I read at a stalk. -/
theorem stalk_fittingIdeal_relativeDifferentials_of_isPullback {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (h : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (r : ℤ) (x' : X') :
    IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f') r) x' =
      Ideal.map (g'.stalkMap x').hom
        (IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f) r)
          (g'.base x')) := by
  rw [← fittingIdeal_relativeDifferentials_comap g' f' f g h r, IdealSheafData.stalk_comap]

end AlgebraicGeometry

namespace Stacks.Curves

/-- **The implication (1) ⟹ (4) of Stacks Tag 0C4D, Fitting clause, over an arbitrary base
field.**

Let `k` be a field, `X` a scheme locally of finite type over `k` and `x` a node of `X` at which
the stalk of the first Fitting ideal sheaf of `Ω_{X/k}` is a proper ideal.  Then that Fitting
ideal generates the maximal ideal of `𝒪_{X,x}`.

Equivalently the local ring at `x` of the closed subscheme cut out by the first Fitting ideal of
`Ω_{X/k}` is the residue field `κ(x)`, which is the step "for every point `x ∈ Z` the local ring
`𝒪_{Z,x}` is equal to `κ(x)`" of the proof of the implication (1) ⟹ (2) of Tag 0C4E.

The base field is arbitrary: the algebraically closed case
`Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_of_isNode_of_isAlgClosed` is applied at the
ordinary double point above `x` carried by the node condition, and the conclusion is brought down
by faithfully flat descent of ideals along `𝒪_{X,x} ⟶ 𝒪_{X_{k̄},x̄}`. -/
theorem stalk_fittingIdeal_eq_maximalIdeal_of_isNode
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X) (hnode : IsNode k X x)
    (hZ : IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials
        (X ↘ Spec (.of k))) (1 : ℤ)) x ≤ maximalIdeal (X.presheaf.stalk x)) :
    IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials
        (X ↘ Spec (.of k))) (1 : ℤ)) x = maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨-, xbar, hxbar, hodp⟩ := id hnode
  subst hxbar
  let f : X ⟶ Spec (.of k) := X ↘ Spec (.of k)
  let K := AlgebraicClosure k
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback f g : Scheme.{u})
  let F : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ Spec (.of K) := pullback.snd f g
  let instY : Y.Over (Spec (.of K)) := ⟨q⟩
  have hlft : LocallyOfFiniteType (Y ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
  let algB : Algebra K (Y.presheaf.stalk xbar) :=
    (((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ Spec (.of K)).appTop ≫
      Y.presheaf.germ ⊤ xbar trivial).hom).toAlgebra
  -- the point above `x` is a node of the base change
  have hxbarcl : IsClosed ({xbar} : Set Y) := hodp.1
  have hnodalB : IsNodalAlgebra K (Y.presheaf.stalk xbar) :=
    ((isOrdinaryDoublePoint_iff_isNodalAlgebra_stalk K Y xbar).mp hodp).2
  have hnodeY : IsNode K Y xbar :=
    (isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed K Y xbar hxbarcl).mpr hnodalB
  -- the stalk of the Fitting ideal upstairs is generated by the stalk downstairs
  have hsq : IsPullback F q f g := IsPullback.of_hasPullback f g
  have hq : (Y ↘ Spec (.of K)) = q := rfl
  have hbc := stalk_fittingIdeal_relativeDifferentials_of_isPullback F q f g hsq 1 xbar
  rw [← hq] at hbc
  -- the stalk map of the first projection is flat and local
  have hgflat : Flat g := (Flat.SpecMap_iff).2
    (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K))
  have hFflat : Flat F := inferInstanceAs (Flat (pullback.fst f g))
  have hlocal : IsLocalHom (F.stalkMap xbar).hom := F.toLRSHom.prop xbar
  -- the algebraically closed case at the ordinary double point above `x`
  have hfitbar := stalk_fittingIdeal_eq_maximalIdeal_of_isNode_of_isAlgClosed K Y xbar hxbarcl
    hnodeY
  rw [hbc] at hfitbar
  -- the two extensions agree, so faithfully flat descent gives the equality downstairs
  have hmapm : Ideal.map (F.stalkMap xbar).hom
      (maximalIdeal (X.presheaf.stalk (F.base xbar))) = maximalIdeal (Y.presheaf.stalk xbar) := by
    refine le_antisymm ?_ (hfitbar.ge.trans (Ideal.map_mono hZ))
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (IsLocalRing.maximalIdeal_comap (F.stalkMap xbar).hom).symm
  algebraize [(F.stalkMap xbar).hom]
  have : Module.FaithfullyFlat (X.presheaf.stalk (F.base xbar)) (Y.presheaf.stalk xbar) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap F xbar) hlocal
  exact Ideal.map_injective_of_faithfullyFlat (A := X.presheaf.stalk (F.base xbar))
    (B := Y.presheaf.stalk xbar) (hfitbar.trans hmapm.symm)

end Stacks.Curves

end
