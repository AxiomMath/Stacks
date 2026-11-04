module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Grassmannian
public import StacksFrontier.AlgebraicGeometry.Conormal.GrassmannianKZeroClass
public import StacksFrontier.AlgebraicGeometry.Conormal.SmoothRank
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex

/-!
# Embedding a smooth subscheme into `X × G(n - r, n)` with an extendable conormal class

This file carries out the geometric part of the proof of [Stacks, Tag 0FIR]. Let `i : Z ⟶ X` be
a closed immersion of smooth projective schemes over `k`, equidimensional of dimensions `e < d`,
and `r = d - e`. Choose an ample invertible module `L` on `X` and a surjection
`𝒪_Z^{⊕ n} ⟶ 𝒞_{Z/X} ⊗ L|_Z^{⊗ m}`; it is classified by `g : Z ⟶ G(n - r, n)`. Then
`h = (i, g) : Z ⟶ X × G(n - r, n)` is a closed immersion with `h ≫ pr₁ = i`, and the class of its
conormal sheaf in `K₀(Z)` is the pullback of a class of `K₀(X × G(n - r, n))`
(`Stacks.Conormal.exists_grassmannian_classOf_conormalSheaf`, which uses the conormal sequence of
[Stacks, Tag 067W]). Moreover `0 < n - r < n`, so that `G(n - r, n)` is in the range of
[Stacks, Tag 0FIQ].

When `d ≤ e` (so `e = d`, as `Z` is a closed subscheme) there is nothing to do: `𝒞_{Z/X}` is
finite locally free of rank `0`, hence zero, and its class is the pullback of `0`.

Here `K₀(Z)` is `K₀(Vect(Z))` (`AlgebraicGeometry.VectorBundleKZero`).

## Main results

All names below are in the namespace `Stacks.WeilCohomology.SmoothProjectiveScheme`.

* `isFiniteLocallyFreeOfRank_conormalSheaf`: `𝒞_{Z/X}` is finite locally free of rank `d - e`.
* `exists_pullbackRingHom_eq_classOf_conormalSheaf_of_le`: the case `d ≤ e`.
* `exists_grassmannian_embedding`: the case `e < d`.

## References

* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
* [Stacks Project, Tag 067W](https://stacks.math.columbia.edu/tag/067W)
* [Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- **The conormal sheaf of a closed immersion of smooth projective schemes has rank the
codimension.** For `i : Z ⟶ X` a closed immersion of smooth projective schemes over `k` of
relative dimensions `e` and `d`, `𝒞_{Z/X}` is finite locally free of rank `d - e`. -/
theorem isFiniteLocallyFreeOfRank_conormalSheaf
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] {e d : ℕ} (hZ : RelativeDimension Z.obj.hom e)
    (hX : RelativeDimension X.obj.hom d) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := Z.obj.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf i.hom.left : Z.obj.left.Modules)
      (d - e) := by
  have : Smooth (i.hom.left ≫ X.obj.hom) := by
    rw [Over.w i.hom]
    infer_instance
  have key : ∀ (q : Z.obj.left ⟶ Spec (.of k)) [LocallyOfFiniteType q], q = Z.obj.hom →
      RelativeDimension Z.obj.hom e → RelativeDimension q e := by
    rintro q _ rfl hq
    exact hq
  exact Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheaf_of_relativeDimension i.hom.left
    X.obj.hom d e hX (key _ (Over.w i.hom) hZ)

/-- **In codimension zero the conormal class extends.** For a closed immersion `i : Z ⟶ X` of
smooth projective schemes over `k` of relative dimensions `e` and `d ≤ e`, `𝒞_{Z/X}` is finite
locally free of rank `d - e = 0`, hence zero, so its class in `K₀(Z)` is the pullback of
`0 ∈ K₀(X)`. -/
theorem exists_pullbackRingHom_eq_classOf_conormalSheaf_of_le
    {Z X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : Z ⟶ X) [IsClosedImmersion i.hom.left] {e d : ℕ} (hZ : RelativeDimension Z.obj.hom e)
    (hX : RelativeDimension X.obj.hom d) (hde : d ≤ e) :
    ∃ β : VectorBundleKZero X.obj.left,
      pullbackRingHom i.hom.left β =
        classOf Z.obj.left (Stacks.Conormal.conormalSheaf i.hom.left) := by
  have h0 := isFiniteLocallyFreeOfRank_conormalSheaf i hZ hX
  rw [Nat.sub_eq_zero_of_le hde] at h0
  refine ⟨0, ?_⟩
  rw [map_zero, VectorBundleKZero.classOf_eq_zero_of_isZero
    (@Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero _ _ h0)]

/-- **The embedding `(i, g) : Z ⟶ X × G(n - r, n)` of the proof of Stacks 0FIR.** Let
`i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k` of relative dimensions
`e < d`. Then there are `0 < l < n` and a closed immersion `h : Z ⟶ X × G(l, n)` with
`h ≫ pr₁ = i` such that the class of `𝒞_{Z/X × G(l, n)}` in `K₀(Z)` is the pullback along `h` of
a class of `K₀(X × G(l, n))`. (Here `l = n - (d - e)`.) -/
theorem exists_grassmannian_embedding {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left] {e d : ℕ} (hZ : RelativeDimension Z.obj.hom e)
    (hX : RelativeDimension X.obj.hom d) (hed : e < d) :
    ∃ l n : ℕ, 0 < l ∧ l < n ∧
      ∃ h : Z ⟶ prod X (SmoothProjectiveScheme.grassmannian k l n),
        ∃ _ : IsClosedImmersion h.hom.left,
          h ≫ fst X (SmoothProjectiveScheme.grassmannian k l n) = i ∧
        ∃ β : VectorBundleKZero (prod X (SmoothProjectiveScheme.grassmannian k l n)).obj.left,
          pullbackRingHom h.hom.left β =
            classOf Z.obj.left (Stacks.Conormal.conormalSheaf h.hom.left) := by
  obtain ⟨L, hLinv, -, hL⟩ :=
    Stacks.Algebraization.exists_isRelativelyAmple_of_isProjective k X.obj.hom
      (SmoothProjectiveScheme.isProjective X)
  have := hLinv
  obtain ⟨m, hm, hrm, g, hg⟩ :=
    Stacks.Conormal.exists_grassmannian_classOf_conormalSheaf i.hom.left L hL (d - e)
      (hC := isFiniteLocallyFreeOfRank_conormalSheaf i hZ hX) (d - e + 1)
  set G := SmoothProjectiveScheme.grassmannian k (m - (d - e)) m
  let g' : Z.obj.left ⟶ G.obj.left :=
    pullback.lift (f := terminal.from (Spec (.of k)))
      (g := terminal.from (Grassmannian.scheme.{u} (m - (d - e)) m)) Z.obj.hom g
      (terminal.hom_ext _ _)
  have hg'G : g' ≫ G.obj.hom = Z.obj.hom := pullback.lift_fst _ _ _
  let τ : G.obj.left ⟶ Grassmannian.scheme.{u} (m - (d - e)) m :=
    pullback.snd (terminal.from (Spec (.of k)))
      (terminal.from (Grassmannian.scheme.{u} (m - (d - e)) m))
  have hg'q : g' ≫ τ = g := pullback.lift_snd _ _ _
  let hl : Z.obj.left ⟶ Limits.pullback X.obj.hom G.obj.hom :=
    pullback.lift i.hom.left g' (by rw [Over.w i.hom, hg'G])
  have hlfst : hl ≫ pullback.fst X.obj.hom G.obj.hom = i.hom.left := pullback.lift_fst _ _ _
  have hlsnd : hl ≫ pullback.snd X.obj.hom G.obj.hom = g' := pullback.lift_snd _ _ _
  let h : Z ⟶ prod X G := ObjectProperty.homMk (Over.homMk hl (by
    show hl ≫ pullback.fst X.obj.hom G.obj.hom ≫ X.obj.hom = Z.obj.hom
    rw [← Category.assoc, hlfst, Over.w i.hom]))
  have : IsClosedImmersion hl := by
    have : IsClosedImmersion (hl ≫ pullback.fst X.obj.hom G.obj.hom) := by
      rw [hlfst]
      infer_instance
    exact IsClosedImmersion.of_comp hl (pullback.fst X.obj.hom G.obj.hom)
  refine ⟨m - (d - e), m, by omega, by omega, h, (inferInstance : IsClosedImmersion hl),
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext hlfst), ?_⟩
  exact hg (Limits.pullback X.obj.hom G.obj.hom) (pullback.fst X.obj.hom G.obj.hom)
    (pullback.snd X.obj.hom G.obj.hom ≫ τ)
    hl hlfst (by rw [← Category.assoc, hlsnd, hg'q])

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
