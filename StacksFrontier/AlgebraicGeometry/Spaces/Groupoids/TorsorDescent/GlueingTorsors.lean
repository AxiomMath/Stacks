module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorLocality

/-!
# Glueing fppf torsors along a covering of the base

Let `{Bᵢ ⟶ B}` be an fppf covering of an algebraic space `B` over a scheme `S`, let `G` be a
group algebraic space over `B` and let `Gᵢ` be its base changes. Stacks 04U1 asserts that a
descent datum consisting of an fppf `Gᵢ`-torsor `Xᵢ` over each `Bᵢ` together with equivariant
transition isomorphisms satisfying the cocycle condition over the triple overlaps is effective:
there is an fppf `G`-torsor `X` over `B` whose base change to `Bᵢ` is `Xᵢ`, recovering the
transition isomorphisms.

What is proved here is the part of that assertion which does not depend on the effectivity of
descent for algebraic spaces, namely that the glued object, once it is available, *is* an fppf
torsor: if `X` is an algebraic space over `B` carrying an action of `G` whose base change to
each `Bᵢ` is equivariantly isomorphic to `Xᵢ`, then `X` is an fppf `G`-torsor.

The production of `X` from the `Xᵢ` is not done here, so the transition isomorphisms and their
cocycle condition do not appear below: the hypothesis used instead is the identification of the
base changes of a given `X` with the `Xᵢ`. The whole of Stacks 04U1, for a covering of `S`, is
`AlgebraicGeometry.Space.exists_isFppfTorsor_of_descentDatum` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/TorsorDescent/GlueingTorsorsExistence.lean`,
which carries the tag.

## Main results

* `AlgebraicGeometry.isPseudoTorsor_of_modIso` and `AlgebraicGeometry.isPseudoTorsor_congr`: the
  pseudo-torsor condition of Stacks 04TW transports along an equivariant isomorphism of module
  objects in any cartesian monoidal category.
* `AlgebraicGeometry.Space.isTorsorFor_of_modIso` and
  `AlgebraicGeometry.Space.isFppfTorsor_of_modIso`: the conditions of Stacks 04TY transport
  along an equivariant isomorphism over the base, the trivializing family being unchanged.
* `AlgebraicGeometry.Space.isFppfTorsor_of_isFppfCovering_of_modIso`: the step of Stacks 04U1
  showing that the glued object is an fppf `G`-torsor.

## Implementation notes

The statement below takes the glued object as given. Producing it is the glueing of the
underlying torsors of sheaves, Stacks 04UM, followed by Stacks 04SK,
`AlgebraicGeometry.isAlgebraicSpace_of_isCovering`, for its algebraicity; that is done in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/TorsorDescent/GlueingTorsorsExistence.lean`.
Note that the algebraicity of the glued object is needed not only for the proof but to *state*
the conclusion: `IsFppfTorsor` takes a proof that the acted-on object is an algebraic space among
its arguments.

Fppf locality of the torsor conditions, which is the source's "these may be checked fppf
locally, and hence follow from the corresponding properties of the actions
`Gᵢ ×_{Bᵢ} Xᵢ → Xᵢ`", is `AlgebraicGeometry.Space.isFppfTorsor_of_isFppfCovering`, and the only
thing added here is the passage from the base changes of the action on `X` to the given actions
on the `Xᵢ` across the equivariant isomorphisms, which is the transport below.

The transport is stated for the pointwise form of the pseudo-torsor condition
(`CategoryTheory.ModObj.isIso_leftSMul_iff`): an equivariant isomorphism `e : X ≅ Y` carries the
unique group element taking one point of `X` to another to the unique group element taking the
images of those points to each other, because postcomposition with `e.hom` is injective and
commutes with the action. Only the equivariance of `e.hom` is used, the equivariance of `e.inv`
being Mathlib's instance for the inverse of an equivariant isomorphism; the `congr` form is then
the two directions of the transport. The trivializing family of
`AlgebraicGeometry.Space.IsTorsorFor` is carried over unchanged, a section of the base change of
`X` being composed with the base change of `e.hom`.

The base `B` is an arbitrary algebraic space over `S` rather than `S` itself, which is the case
`B = yoneda.obj (Over.mk (𝟙 _))` of the statement; this is a generalization, and is what
`AlgebraicGeometry.Space.isFppfTorsor_of_isFppfCovering` is stated for.

## References

* [Stacks Project, Tag 04U1](https://stacks.math.columbia.edu/tag/04U1)
* [Stacks Project, Tag 04TW](https://stacks.math.columbia.edu/tag/04TW)
* [Stacks Project, Tag 04TY](https://stacks.math.columbia.edu/tag/04TY)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 04TS](https://stacks.math.columbia.edu/tag/04TS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory CategoryTheory.MonObj

universe u v

namespace AlgebraicGeometry

/-! ### Transport of the pseudo-torsor condition along an equivariant isomorphism -/

/-- The inverse of an equivariant isomorphism, as `e.symm.hom`, is equivariant. -/
private theorem isModHom_symm_hom {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) [GrpObj G] {X Y : C} [ModObj G X] [ModObj G Y] (e : X ≅ Y) [IsModHom G e.hom] :
    IsModHom G e.symm.hom :=
  inferInstanceAs (IsModHom G e.inv)

/-- **The pseudo-torsor condition of Stacks 04TW transports along an equivariant isomorphism.**
If `G` acts on `X` and on `Y` in a cartesian monoidal category and `e : X ≅ Y` is `G`-equivariant,
then `Y` is a pseudo-torsor under `G` as soon as `X` is.

Read pointwise, by `CategoryTheory.ModObj.isIso_leftSMul_iff`: the unique group element taking
`x ≫ e.inv` to `y ≫ e.inv` is the unique one taking `x` to `y`, because postcomposition with the
isomorphism `e.hom` is injective and, by equivariance, commutes with the action. -/
theorem isPseudoTorsor_of_modIso {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) [GrpObj G] {X Y : C} [ModObj G X] [ModObj G Y] (e : X ≅ Y) [IsModHom G e.hom]
    (h : IsPseudoTorsor G X) : IsPseudoTorsor G Y := by
  have hpt := ModObj.isIso_leftSMul_iff.mp h
  refine ModObj.isIso_leftSMul_iff.mpr fun Z x y => ?_
  obtain ⟨m, hm, hmu⟩ := hpt Z (x ≫ e.inv) (y ≫ e.inv)
  have key : ∀ n : Z ⟶ G, (n • (x ≫ e.inv)) ≫ e.hom = n • x := by
    intro n
    rw [IsModHom.map_smul e.hom, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hiff : ∀ n : Z ⟶ G, n • (x ≫ e.inv) = y ≫ e.inv ↔ n • x = y := fun n => by
    rw [← cancel_mono e.hom, key n, Category.assoc, e.inv_hom_id, Category.comp_id]
  exact ⟨m, (hiff m).1 hm, fun n hn => hmu n ((hiff n).2 hn)⟩

/-- **The pseudo-torsor condition of Stacks 04TW is invariant under equivariant isomorphism.**
The two directions of `AlgebraicGeometry.isPseudoTorsor_of_modIso`, the second applied to the
inverse isomorphism, which is equivariant because `e.hom` is. -/
theorem isPseudoTorsor_congr {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (G : C) [GrpObj G] {X Y : C} [ModObj G X] [ModObj G Y] (e : X ≅ Y) [IsModHom G e.hom] :
    IsPseudoTorsor G X ↔ IsPseudoTorsor G Y :=
  ⟨isPseudoTorsor_of_modIso G e,
    have := isModHom_symm_hom G e
    isPseudoTorsor_of_modIso G e.symm⟩

namespace Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}

/-! ### Transport of local triviality along an equivariant isomorphism -/

variable (𝒞 S hS) in
/-- **The conditions of Stacks 04TY transport along an equivariant isomorphism over the base.**
A pseudo-torsor under `G` over `B` trivialized by a family satisfying `P` carries both properties
across an equivariant isomorphism `e : X ≅ Y` of objects over `B`: the pseudo-torsor condition by
`AlgebraicGeometry.isPseudoTorsor_of_modIso`, and the trivializing family unchanged, a section of
the base change of `X` to a member being composed with the base change of `e.hom`. -/
theorem isTorsorFor_of_modIso (hB : IsAlgebraicSpace 𝒞 S hS B) (G : Over B) [GrpObj G]
    {X Y : Over B} [ModObj G X] [ModObj G Y] (hG : IsAlgebraicSpace 𝒞 S hS G.left)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
    (P : ∀ (I : Type (u + 1)) (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u),
      (∀ i, Bᵢ i ⟶ B) → Prop)
    (e : X ≅ Y) [IsModHom G e.hom]
    (h : IsTorsorFor 𝒞 S hS B hB G X hG hX P) :
    IsTorsorFor 𝒞 S hS B hB G Y hG hY P := by
  obtain ⟨hp, I, Bᵢ, f, hBᵢ, hP, hsec⟩ := h
  exact ⟨isPseudoTorsor_of_modIso G e hp, I, Bᵢ, f, hBᵢ, hP,
    fun i => (hsec i).map fun s => s ≫ (Over.pullback (f i)).map e.hom⟩

variable (𝒞 S hS) in
/-- **Stacks 04TY**, part (2), transport along an equivariant isomorphism: an object over `B`
equivariantly isomorphic to an fppf `G`-torsor is an fppf `G`-torsor. This is the fppf case of
`AlgebraicGeometry.Space.isTorsorFor_of_modIso`. -/
theorem isFppfTorsor_of_modIso (hB : IsAlgebraicSpace 𝒞 S hS B) (G : Over B) [GrpObj G]
    {X Y : Over B} [ModObj G X] [ModObj G Y] (hG : IsAlgebraicSpace 𝒞 S hS G.left)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (hY : IsAlgebraicSpace 𝒞 S hS Y.left)
    (e : X ≅ Y) [IsModHom G e.hom]
    (h : IsFppfTorsor 𝒞 S hS B hB G X hG hX) :
    IsFppfTorsor 𝒞 S hS B hB G Y hG hY :=
  isTorsorFor_of_modIso 𝒞 S hS hB G hG hX hY
    (fun _ Bᵢ f => IsFppfCovering 𝒞 S hS Bᵢ f) e h

/-! ### Glueing fppf torsors along a covering of the base -/

variable (𝒞 S hS) in
/-- **The glued object of Stacks 04U1 is an fppf torsor.**

Let `{Bᵢ ⟶ B}` be an fppf covering of an algebraic space `B` over `S`, let `G` be a group
algebraic space over `B`, and suppose given for each `i` an fppf torsor `Xᵢ` over `Bᵢ` under the
base change of `G`. If `X` is an algebraic space over `B` carrying an action of `G` together
with, for each `i`, an isomorphism `e i` of the base change of `X` to `Bᵢ` with `Xᵢ` which is
equivariant for the base change of `G`, then `X` is an fppf `G`-torsor over `B`.

The base changes of the action on `X` are fppf torsors by transport along the `e i`
(`AlgebraicGeometry.Space.isFppfTorsor_of_modIso` applied to the inverse isomorphisms), and the
two conditions are fppf local on the base by
`AlgebraicGeometry.Space.isFppfTorsor_of_isFppfCovering`.

The existence of `X` from the transition isomorphisms of a descent datum, and so the whole of
Stacks 04U1, is `AlgebraicGeometry.Space.exists_isFppfTorsor_of_descentDatum`. -/
@[stacks 04U1 "the glued object is an fppf torsor; not its existence from the descent datum"]
theorem isFppfTorsor_of_isFppfCovering_of_modIso (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : Over B) [GrpObj G] (hG : IsAlgebraicSpace 𝒞 S hS G.left)
    (X : Over B) [ModObj G X] (hX : IsAlgebraicSpace 𝒞 S hS X.left)
    {I : Type (u + 1)} (Bᵢ : I → (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Bᵢ i ⟶ B)
    (hBᵢ : ∀ i, IsAlgebraicSpace 𝒞 S hS (Bᵢ i)) (hcov : IsFppfCovering 𝒞 S hS Bᵢ f)
    (Xᵢ : ∀ i, Over (Bᵢ i)) [∀ i, ModObj ((Over.pullback (f i)).obj G) (Xᵢ i)]
    (hXᵢ : ∀ i, IsAlgebraicSpace 𝒞 S hS (Xᵢ i).left)
    (e : ∀ i, (Over.pullback (f i)).obj X ≅ Xᵢ i)
    (he : ∀ i, IsModHom ((Over.pullback (f i)).obj G) (e i).hom)
    (htors : ∀ i, IsFppfTorsor 𝒞 S hS (Bᵢ i) (hBᵢ i) ((Over.pullback (f i)).obj G) (Xᵢ i)
      (isAlgebraicSpace_pullback 𝒞 S hS G.hom (f i) hG (hBᵢ i) hB) (hXᵢ i)) :
    IsFppfTorsor 𝒞 S hS B hB G X hG hX := by
  refine isFppfTorsor_of_isFppfCovering 𝒞 S hS hB G X hG hX Bᵢ f hBᵢ hcov fun i => ?_
  have := he i
  have := isModHom_symm_hom ((Over.pullback (f i)).obj G) (e i)
  exact isFppfTorsor_of_modIso 𝒞 S hS (hBᵢ i) ((Over.pullback (f i)).obj G)
    (isAlgebraicSpace_pullback 𝒞 S hS G.hom (f i) hG (hBᵢ i) hB) (hXᵢ i)
    (isAlgebraicSpace_pullback 𝒞 S hS X.hom (f i) hX (hBᵢ i) hB) (e i).symm (htors i)

end Space

end AlgebraicGeometry

end
