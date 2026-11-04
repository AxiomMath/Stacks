module

public import StacksFrontier.AlgebraicGeometry.Divisors.ConstantGenericStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.ConstantOnIntegral
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.FiberChart
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericStalkComparison
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.PullbackDenominators

/-!
# The generic value of a meromorphic function pulled back along a flat morphism

The penultimate paragraph of [Stacks, Tag 0BD7] multiplies the meromorphic section `s` of the
first paragraph by the pullback `φ^*(q)` of a meromorphic function `q ∈ 𝒦_Y(A)`. On an integral
`X` the sheaf `𝒦_X` is the constant sheaf on `K(X)` ([Stacks, Tag 01X5] part (1)), so `φ^*(q)`
restricted to an open of `φ^{-1}(A)` is the constant section of one element of `K(X)`; and
`AlgebraicGeometry.meromorphicSectionSheafIsoConstant_smul` needs that element *named*, not
existentially quantified, because the paragraph identifies it with the ratio of two germs on the
base. This file names it.

The passage is forced by one equation. A section `q` of `𝒦_Y(A)` with `q g' = r'` for two
regular sections `g'`, `r'` of `𝒪_Y(A)` — the shape
`AlgebraicGeometry.exists_isAffineOpen_nhds_mul_toTotalQuotientSheaf_eq` produces — pulls back to
a section whose generic value `ρ` satisfies the same equation between the generic values of
`φ^#(g')` and `φ^#(r')`; and those are the images in `K(X)` of the germs of `g'` and `r'` at the
point of the base. When the germ of `g'` there is nonzero its image in `K(X)` is nonzero too, `φ`
being flat, so the equation determines `ρ`.

## Main results

* `AlgebraicGeometry.germ_genericPoint_appLE`: the germ at the generic point of `X` of a section
  pulled back from the base is the image in `K(X)` of its germ at any point of the open.
* `AlgebraicGeometry.germ_genericPoint_appLE_ne_zero`: hence that generic germ is nonzero as soon
  as the germ on the base is.
* `AlgebraicGeometry.restrict_ringSheafPullbackOfFlat_toTotalQuotientRingSheaf`: the pullback of
  meromorphic functions carries the image of a regular section to the image of its pullback.
* `AlgebraicGeometry.totalQuotientSheafIsoConstant_restrict_ringSheafPullbackOfFlat`: **the
  bridge** — the constant value of `φ^*(q)` on an open of `φ^{-1}(A)` is the element of `K(X)`
  named by the equation `ρ · (g' at the generic point) = (r' at the generic point)`.

## Implementation notes

The ring isomorphism `K(X) ≃+* 𝒪_{const}(W)` of
`AlgebraicGeometry.constantSheafOnSpaceSectionRingEquiv` is introduced by `obtain` together with
its defining equation, rather than used directly: the constant-section map is spelled
`toSheafify` in the statements that produce it, the isomorphism's codomain is spelled
`constantSheafOnSpace`, and a product of one of each fails to find its `HMul` instance although
the two types differ only by an unfolding. With the isomorphism named, every multiplication
happens on its codomain and `map_mul` and injectivity are available at once.

The generic point is a hypothesis `hξ : genericPoint X ∈ W` rather than being derived from a
point of `W`: on an integral scheme the two are interchangeable, and the germ at the generic
point has to be written down in the statements before any point of `W` is in scope.

No tag attribute: [Stacks, Tag 0BD7] makes no statement about one open of the base.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 01X5](https://stacks.math.columbia.edu/tag/01X5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Meromorphic

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A section pulled back from the base, read in the function field.** For `W ≤ φ^{-1}(A)` and
`x ∈ W`, the germ at the generic point of `X` of `φ^#(c)` is the image in `K(X)` of its germ at
`x`, which by `AlgebraicGeometry.germ_stalkMap_appLE` is the image of the germ of `c` at
`φ(x)`. -/
theorem germ_genericPoint_appLE [IrreducibleSpace X] {A : Y.Opens} {W : X.Opens}
    (e : W ≤ (f ⁻¹ᵁ A : X.Opens)) {x : X} (hx : x ∈ W) (hξ : genericPoint X ∈ W)
    (c : Γ(Y, A)) :
    X.presheaf.germ W (genericPoint X) hξ ((f.appLE A W e).hom c) =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((f.stalkMap x).hom (Y.presheaf.germ A (f x) (e hx) c)) := by
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hx ((f.appLE A W e).hom c)]
  exact congrArg _ (CategoryTheory.congr_fun (germ_stalkMap_appLE f A W e x hx) c).symm

/-- **A nonzero germ on the base stays nonzero in `K(X)`.** For a flat morphism of integral
schemes the map `𝒪_{Y, φ(x)} → K(X)` is injective
(`AlgebraicGeometry.injective_algebraMap_functionField_of_flat`), so the generic germ of the
pullback of a section with nonzero germ at `φ(x)` is nonzero. -/
theorem germ_genericPoint_appLE_ne_zero [Flat f] [IsIntegral X] [IsIntegral Y]
    {A : Y.Opens} {W : X.Opens} (e : W ≤ (f ⁻¹ᵁ A : X.Opens)) {x : X} (hx : x ∈ W)
    (hξ : genericPoint X ∈ W) {c : Γ(Y, A)} (hc : Y.presheaf.germ A (f x) (e hx) c ≠ 0) :
    X.presheaf.germ W (genericPoint X) hξ ((f.appLE A W e).hom c) ≠ 0 := by
  let : Algebra ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let : Algebra ↑(Y.presheaf.stalk (f x)) X.functionField :=
    ((algebraMap ↑(X.presheaf.stalk x) X.functionField).comp
      (algebraMap ↑(Y.presheaf.stalk (f x)) ↑(X.presheaf.stalk x))).toAlgebra
  rw [germ_genericPoint_appLE f e hx hξ c]
  intro h0
  exact hc (injective_algebraMap_functionField_of_flat f x (h0.trans (map_zero _).symm))

/-- **The pullback of meromorphic functions on a regular section.** The image in `𝒦_X` of the
pullback of `c ∈ 𝒪_Y(A)`, restricted to an open `W` of `φ^{-1}(A)`, is the image of
`φ^{\#}(c)` on `W`. This is
`Stacks.Meromorphic.Scheme.toTotalQuotientRingSheaf_comp_ringSheafPullbackOfFlat` read on
sections, followed by naturality of `AlgebraicGeometry.toTotalQuotientRingSheaf`. -/
theorem restrict_ringSheafPullbackOfFlat_toTotalQuotientRingSheaf [Flat f]
    {A : Y.Opens} {W : X.Opens} (e : W ≤ (f ⁻¹ᵁ A : X.Opens)) (c : Γ(Y, A)) :
    ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf).obj.map (homOfLE e).op).hom
        (((Scheme.ringSheafPullbackOfFlat f).hom.app (op A)).hom
          (((toTotalQuotientRingSheaf Y).hom.app (op A)).hom c))
      = ((toTotalQuotientRingSheaf X).hom.app (op W)).hom ((f.appLE A W e).hom c) := by
  have h1 := congrArg
    (fun m : Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y)
          Y.sheaf ⟶
        (Scheme.sheafPushforward f).obj
          (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.totalQuotientSheaf) =>
      (m.hom.app (op A)).hom c)
    (Scheme.toTotalQuotientRingSheaf_comp_ringSheafPullbackOfFlat f)
  have h2 := congrArg (fun z : (Stacks.Sheaves.Differentials.ringSheaf
      (J := Opens.grothendieckTopology X) X.totalQuotientSheaf).obj.obj
        (op ((f ⁻¹ᵁ A : X.Opens))) =>
    ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).obj.map (homOfLE e).op).hom z) h1
  refine h2.trans ?_
  exact (CategoryTheory.congr_fun
    ((toTotalQuotientRingSheaf X).hom.naturality (homOfLE e).op) ((f.app A).hom c)).symm

/-- **The generic value of a pulled-back meromorphic function.** If `q g' = r'` in `𝒦_Y(A)` with
`g'`, `r'` regular sections of `𝒪_Y(A)`, and `ρ ∈ K(X)` satisfies the same equation between the
generic values of `φ^{\#}(g')` and `φ^{\#}(r')`, then on an open `W` of `φ^{-1}(A)` the section
`φ^*(q)` of `𝒦_X` is the constant section of `ρ` — which is the form the scalar law
`AlgebraicGeometry.meromorphicSectionSheafIsoConstant_smul` asks for. -/
theorem totalQuotientSheafIsoConstant_restrict_ringSheafPullbackOfFlat [Flat f] [IsIntegral X]
    {A : Y.Opens} {W : X.Opens} (e : W ≤ (f ⁻¹ᵁ A : X.Opens)) (hξ : genericPoint X ∈ W)
    (q : (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y)
      Y.totalQuotientSheaf).obj.obj (op A)) (g' r' : Γ(Y, A))
    (hq : q * ((toTotalQuotientRingSheaf Y).hom.app (op A)).hom g'
      = ((toTotalQuotientRingSheaf Y).hom.app (op A)).hom r')
    (ρ : X.functionField)
    (hg : X.presheaf.germ W (genericPoint X) hξ ((f.appLE A W e).hom g') ≠ 0)
    (hρ : ρ * X.presheaf.germ W (genericPoint X) hξ ((f.appLE A W e).hom g')
      = X.presheaf.germ W (genericPoint X) hξ ((f.appLE A W e).hom r')) :
    ((totalQuotientSheafIsoConstant X).val.hom.hom.app (op W)).hom
        (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.totalQuotientSheaf).obj.map (homOfLE e).op).hom
            (((Scheme.ringSheafPullbackOfFlat f).hom.app (op A)).hom q))
      = ((toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op W)).hom ρ := by
  have hne : Nonempty W := ⟨⟨genericPoint X, hξ⟩⟩
  obtain ⟨ε, hε⟩ : ∃ ε : X.functionField ≃+*
      (constantSheafOnSpace (X : TopCat) CommRingCat.{u} X.functionField).obj.obj (op W),
      ∀ z, ε z = ((toSheafify (Opens.grothendieckTopology X)
        ((Functor.const (Opens X)ᵒᵖ).obj X.functionField)).app (op W)).hom z :=
    ⟨constantSheafOnSpaceSectionRingEquiv X X.functionField W hne, fun _ => rfl⟩
  have hT : ∀ c : Γ(Y, A),
      ((totalQuotientSheafIsoConstant X).val.hom.hom.app (op W)).hom
          (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.totalQuotientSheaf).obj.map (homOfLE e).op).hom
              (((Scheme.ringSheafPullbackOfFlat f).hom.app (op A)).hom
                (((toTotalQuotientRingSheaf Y).hom.app (op A)).hom c)))
        = ε (X.presheaf.germ W (genericPoint X) hξ ((f.appLE A W e).hom c)) := by
    intro c
    rw [restrict_ringSheafPullbackOfFlat_toTotalQuotientRingSheaf f e c, hε]
    exact (totalQuotientSheafIsoConstant X).property W ((f.appLE A W e).hom c) hξ
  have hkey := congrArg
    (fun z => ((totalQuotientSheafIsoConstant X).val.hom.hom.app (op W)).hom
      (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf).obj.map (homOfLE e).op).hom
          (((Scheme.ringSheafPullbackOfFlat f).hom.app (op A)).hom z))) hq
  erw [map_mul, map_mul, map_mul, hT, hT] at hkey
  rw [← hε, ← ε.symm_apply_eq]
  refine mul_right_cancel₀ hg (ε.injective ?_)
  rw [map_mul, ε.apply_symm_apply, hρ]
  exact hkey

end AlgebraicGeometry

end
