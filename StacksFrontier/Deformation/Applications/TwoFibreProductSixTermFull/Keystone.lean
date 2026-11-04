module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Applications.TwoFibreProductSelfExact

/-!
# The six-term sequence of a 2-fibre product, in one statement

Let `f : ℋ → ℱ` and `g : 𝒢 → ℱ` be `1`-morphisms of deformation categories over `𝒞_Λ` and let
`𝒲 = ℋ ×_ℱ 𝒢`. Part (2) of Tag 06L5 asserts a six-term exact sequence

`0 → Inf(𝒲) → Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ) → T𝒲 → Tℋ ⊕ T𝒢 → Tℱ`

of `k`-vector spaces. Its five maps and the exactness at four of its five spots are built one
spot at a time in
`StacksFrontier.Deformation.Applications.TwoFibreProductInfRow`,
`StacksFrontier.Deformation.Applications.TwoFibreProductBoundaryLinear`,
`StacksFrontier.Deformation.Applications.TwoFibreProductSelfExact` and
`StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact`. This file proves the
remaining spot, `Inf(ℱ)`, and assembles all five into the single statement
`Deformation.twoFibreProduct_sixTermExact`, which is the one to read part (2) off.

This is the first of three parts of
`StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull`: it contains the
reparametrization lemma, the three diagram chases, the bridge between the two models of
`Inf(ℱ)`, the comparison isomorphism of a fibre-product object, the two normalizations of the
square-zero extension compared, and the keystone at the re-based extension. The conjugation
relations and the vanishing of the class of the boundary quadruple are in
`StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull.BoundaryZero`, and the
six-term sequence itself is in
`StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull.SixTerm`.

## Main definitions

* `Deformation.infBoundaryLinearMap`: the boundary map `δ : Inf(ℱ) → T𝒲`, read on the model of
  `Inf(ℱ)` that the first three terms of the sequence use. The two models of `Inf(ℱ)` — the
  value of the canonical linear lift of the infinitesimal automorphisms, which is the source of
  `Deformation.boundaryLinearMap`, and the tangent space at the identity of the automorphism
  functor, which is the target of `Deformation.infLegDiff` — are *different types*, identified
  by `Deformation.tangentCarrierLinearEquiv` at the rank-one coordinate module; without that
  bridge the composite `Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ) → T𝒲` does not typecheck.

## Main results

* `Deformation.twoFibreProduct_sixTermExact`: **part (2) of Tag 06L5**, the six-term sequence
  with all five of its maps and the exactness at all five of its spots.
* `Deformation.exact_infLegDiff_infBoundaryLinearMap`: **part (2) of Tag 06L5, exactness at
  `Inf(ℱ)`**. The kernel of the boundary map is the image of the difference of the two outer
  legs, which is the source's "if `α` gives the trivial deformation
  `(k[ε], y'₀, z'₀, c' ∘ α ∘ b')` of `w₀`, then the isomorphism `w'₀ → δ(α)` produces a pair
  `(β, γ)` which is a preimage of `α`", with its converse.
* `Deformation.tangentClassAt_boundaryObject_eq_zero_iff`: the quadruple the boundary map
  produces is the trivial deformation of `w₀` exactly when the automorphism it twists by
  satisfies the boundary square for some pair of automorphisms of `y'₀` and of `z'₀`.
* `Deformation.boundaryCompare_comp_crossCompare_eq`: **the cocartesian-uniqueness
  identification at the re-based square-zero extension** — the comparison isomorphism carried
  by the chosen pushforward of `w₀` is the composite of the comparisons `b'` and `c'` of the
  boundary map, read through the comparisons of the two components with the chosen pushforwards
  of `y₀` and of `z₀`. This is the source's `w'₀ = (k[ε], y'₀, z'₀, c' ∘ b')` in the
  normalization in which the boundary map is built, i.e. the identification of the chosen
  pushforward of `w₀` with `Deformation.boundaryObject` at the identity automorphism.
* `Deformation.map_cross_comp_boundaryCompareFst`,
  `Deformation.map_cross_comp_boundaryCompareSnd`: **the transports of the comparisons across
  the two normalizations of the square-zero extension** — the comparisons of chosen
  pushforwards at the extension read as an algebra under the base are carried to `b'` and to
  `c'` by `Deformation.squareZeroCrossUnderIso`. The first, applied to the second leg, does the
  same there.
* `Deformation.transportAut_comp_boundaryCompareFst`,
  `Deformation.transportAut_comp_boundaryCompareSnd`: the conjugation relations the two outer
  legs satisfy, transported to the re-based extension along those comparisons.
* `Deformation.crossCompareFst`, `Deformation.crossCompareSnd`: the comparisons of the chosen
  pushforwards of `y₀` and of `z₀` with the two components of the chosen pushforward of `w₀`,
  at the re-based extension, with their defining properties and their verticality.

## Implementation notes

Four of the five exactness assertions are discharged from the per-spot theorems, not reproved:
`Deformation.injective_infProjPair`, `Deformation.exact_infProjPair_infLegDiff`,
`Deformation.exact_boundaryLinearMap_tangentProjPair` and
`Deformation.exact_tangentProjPair_tangentLegDiff`. Only the fourth needs an adjustment, because
it is stated for `Deformation.boundaryLinearMap` on its own model of `Inf(ℱ)`: precomposing the
first map of an exact pair with a surjection does not change its image
(`Deformation.exact_comp_of_surjective`), and the bridge is a linear equivalence.

Exactness at `Inf(ℱ)` is the spot that compares the *two normalizations* of the square-zero
extension: the boundary map and the comparisons `b'` and `c'` are built at the re-based
`Deformation.squareZeroCrossUnder`, while the `Inf`-row's maps are built at
`Deformation.dualNumbersUnder`. Three transports bridge them, one for each comparison of the
row: `Deformation.map_cross_comp_boundaryCompareFst` for the `ℋ`-leg, the same lemma applied to
`g` for the `𝒢`-leg, and `Deformation.map_cross_comp_boundaryCompareSnd` for the comparison of
Tag 06JV (2) between the pushforwards of `f(y₀)` and of `g(z₀)` — the `c` of
`Deformation.infLegDiff` — for which the coordinate arrows `Deformation.squareZeroCross` of the
two legs are identified across the equality of their bases
(`Deformation.eqToHom_comp_squareZeroCross`). Each of them turns a conjugation relation at the
dual numbers into one at the re-based extension by `Deformation.conj_of_map`, and the assembly
is then pure diagram algebra: an isomorphism between two `Deformation.boundaryObject`s is a
pair of automorphisms of `y'₀` and `z'₀` satisfying the comparison square
(`Deformation.tangentClassAt_boundaryObject_eq_zero_iff`), and that square says exactly that
the automorphism is the value of the difference of the two legs on the pair
(`Deformation.eq_comp_inv_iff_boundary_square`).

## References

* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 06L5](https://stacks.math.columbia.edu/tag/06L5)
-/

@[expose] public section

namespace Deformation

open CategoryTheory

/-! ### Exactness is unchanged by a surjective reparametrization -/

section Algebra
universe z z₁ z₂ z₃

/-- Precomposing the first map of an exact pair with a surjection preserves exactness: the
image is unchanged. -/
public theorem exact_comp_of_surjective {M : Type z} {N : Type z₁} {P : Type z₂} {Q : Type z₃}
    [Zero Q] {F₁ : N → P} {G₁ : P → Q} (h : Function.Exact F₁ G₁) {e : M → N}
    (he : Function.Surjective e) :
    Function.Exact (F₁ ∘ e) G₁ := by
  intro z
  refine (h z).trans ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨n, hn⟩ := hz
    obtain ⟨m, rfl⟩ := he n
    exact ⟨m, hn⟩
  · obtain ⟨m, hm⟩ := hz
    exact ⟨e m, hm⟩

end Algebra

/-! ### The three diagram chases of exactness at `Inf(ℱ)` -/

section Chase
open CategoryTheory.Functor
universe v₁ u₁ v₂ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
  {p : F ⥤ C} {x : F}

/-- **A conjugation square transported along the canonical arrow between two chosen
pushforwards.** Let `A'` be the transport of a fibre endomorphism `A` of the chosen pushforward
of `x` to `U` along an arrow `ψ : U ⟶ V`, let `D` and `Dd` be comparisons at `V` and at `U`
matched by `ψ` through `m`, and suppose `A` is conjugate to `θd` by `Dd` and that `m`
intertwines `θd` with `θ`. Then `A'` is conjugate to `θ` by `D`.

The canonical arrow between two chosen pushforwards is strongly cocartesian
(`Deformation.ChosenPushforwardsAt.map_cocartesian`), so it is enough that the two vertical
arrows agree after precomposition with it; there the chase is the four hypotheses in a row. This
is how a conjugation relation at the dual numbers is carried to the re-based square-zero
extension, where the boundary map is built. -/
public theorem conj_of_map (P : ChosenPushforwardsAt p x) {U V : Under (p.obj x)} (ψ : U ⟶ V)
    {Z Z' : F} {A : (P.obj U).1 ⟶ (P.obj U).1} {A' : (P.obj V).1 ⟶ (P.obj V).1}
    {D : (P.obj V).1 ⟶ Z} {Dd : (P.obj U).1 ⟶ Z'} {m : Z' ⟶ Z}
    {θ : Z ⟶ Z} {θd : Z' ⟶ Z'}
    (hA : P.map ψ ≫ A' = A ≫ P.map ψ) (hD : P.map ψ ≫ D = Dd ≫ m)
    (hAd : A ≫ Dd = Dd ≫ θd) (hm : m ≫ θ = θd ≫ m)
    (hl1 : p.IsHomLift (𝟙 V.right) (A' ≫ D)) (hl2 : p.IsHomLift (𝟙 V.right) (D ≫ θ)) :
    A' ≫ D = D ≫ θ := by
  refine @Functor.IsStronglyCocartesian.ext _ _ _ _ p _ _ _ _ ψ.right (P.map ψ)
    (P.map_cocartesian ψ) _ _ (𝟙 V.right) _ _ hl1 hl2 ?_
  rw [reassoc_of% hA, hD, reassoc_of% hAd, ← hm, reassoc_of% hD]

/-- A conjugation by an isomorphism, read in the other direction. This is
`Deformation.inv_comp_eq_of_conjugation` for an arbitrary isomorphism of an arbitrary
category. -/
public theorem inv_comp_eq_of_hom_conj {X Y : F} (e : X ≅ Y) {D : X ⟶ X} {A : Y ⟶ Y}
    (h : D ≫ e.hom = e.hom ≫ A) : e.inv ≫ D = A ≫ e.inv := by
  calc e.inv ≫ D = e.inv ≫ (D ≫ e.hom) ≫ e.inv := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = e.inv ≫ e.hom ≫ A ≫ e.inv := by rw [h, Category.assoc]
    _ = A ≫ e.inv := by rw [Iso.inv_hom_id_assoc]

/-- **The boundary square, solved for the automorphism it twists by.** Let `a₁` be conjugate to
`β` by `B` and `a₂` conjugate to `γ` by `Cc`. Then `α` is the composite of `a₁` with the inverse
of `a₂` exactly when the square

`β ≫ B⁻¹ ≫ Cc = B⁻¹ ≫ α ≫ Cc ≫ γ`

commutes. The right-hand side is the comparison square of an isomorphism between the quadruple
`(k[ε], y'₀, z'₀, c' ∘ α ∘ b')` the boundary map produces and the one at the identity
automorphism, with components `β` and `γ`; the left-hand side is the value of the map
`Inf(ℋ) ⊕ Inf(𝒢) → Inf(ℱ)` on the pair those components define, read as an automorphism of
`x'₀`. This is the whole of exactness at `Inf(ℱ)` once both sides are transported to one
normalization of the square-zero extension. -/
public theorem eq_comp_inv_iff_boundary_square {X Y Z : F} (B : X ≅ Y) (Cc : X ≅ Z)
    {α : X ⟶ X} (a₁ a₂ : X ≅ X) {β : Y ⟶ Y} {γ : Z ⟶ Z}
    (h1 : a₁.hom ≫ B.hom = B.hom ≫ β) (h2 : a₂.hom ≫ Cc.hom = Cc.hom ≫ γ) :
    α = a₁.hom ≫ a₂.inv ↔ β ≫ B.inv ≫ Cc.hom = B.inv ≫ α ≫ Cc.hom ≫ γ := by
  have hB := inv_comp_eq_of_hom_conj B h1
  have e1 : a₂.inv ≫ Cc.hom ≫ γ = Cc.hom := by rw [← h2, Iso.inv_hom_id_assoc]
  constructor
  · rintro rfl
    rw [Category.assoc, e1, reassoc_of% hB]
  · intro h
    have hcancel : B.inv ≫ a₁.hom ≫ Cc.hom = B.inv ≫ (α ≫ a₂.hom) ≫ Cc.hom := by
      rw [reassoc_of% hB, h, ← h2, Category.assoc]
    have k2 : a₁.hom = α ≫ a₂.hom :=
      (Iso.cancel_iso_hom_right _ _ Cc).mp ((Iso.cancel_iso_inv_left B _ _).mp hcancel)
    rw [k2, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Chase

/-! ### The bridge between the two models of `Inf(ℱ)` -/

section Bridge
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} {x : F}

/-- The identification of the value at the rank-one coordinate module of the canonical linear
lift of the infinitesimal automorphisms with the tangent space at the identity of the
automorphism functor is surjective, being a linear equivalence. -/
public theorem surjective_tangentCarrierLinearEquiv_symm (P : ChosenPushforwardsAt p x)
    (hp : SatisfiesRS p) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} P hp
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} P hp
    Function.Surjective (tangentCarrierLinearEquiv P hp).symm :=
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} P hp
  let := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} P hp
  (tangentCarrierLinearEquiv P hp).symm.surjective

/-- **The bridge, read on representatives.** A tangent vector of the automorphism functor,
carried to the value at the rank-one coordinate module of the canonical linear lift of the
infinitesimal automorphisms and then read as an infinitesimal automorphism, is the infinitesimal
automorphism that Tag 06JV attaches to it. Both identifications are the same transport along
`Deformation.infinitesimalAutomorphismLinearLift_carrier`, so the composite is the identity. -/
public theorem cast_tangentCarrierLinearEquiv_symm (P : ChosenPushforwardsAt p x)
    (hp : SatisfiesRS p) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} P hp
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} P hp
    ∀ t : localizedAutomorphismFunctorTangent.{u, v, w, u₁, v₁} P,
      cast (infinitesimalAutomorphismLinearLift_carrier P hp (FGModuleCat.of k (ULift.{v} k)))
        ((tangentCarrierLinearEquiv P hp).symm t) = localizedTangentEquivKernel P t := by
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} P hp
  let := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} P hp
  intro t
  unfold tangentCarrierLinearEquiv
  generalize naturalLocalizedTangentModule_spec P hp = hs
  obtain ⟨h1, h2⟩ := hs
  dsimp only
  exact cast_symm_cancel _ _

/-- The identification of Tag 06JV carries negation to inversion: it carries addition to
composition, and the zero tangent vector to the identity
(`Deformation.localizedTangentEquivKernel_eq_one`). -/
public theorem localizedTangentEquivKernel_neg (P : ChosenPushforwardsAt p x)
    (hp : SatisfiesRS p) :
    letI := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} P hp
    letI := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} P hp
    ∀ s : localizedAutomorphismFunctorTangent.{u, v, w, u₁, v₁} P,
      localizedTangentEquivKernel P (-s) = (localizedTangentEquivKernel P s)⁻¹ := by
  let := naturalLocalizedTangentAddCommGroup.{u, v, w, u₁, v₁} P hp
  let := naturalLocalizedTangentModule.{u, v, w, u₁, v₁} P hp
  obtain ⟨hadd, -⟩ := naturalLocalizedTangentModule_spec P hp
  intro s
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← hadd, add_neg_cancel, localizedTangentEquivKernel_eq_one P hp]

end Bridge

/-! ### The comparison isomorphism of a fibre-product object -/

section Vertical
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]

variable (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (f : H ⥤ F) (g : G ⥤ F)

/-- The comparison isomorphism carried by an object of the `2`-fibre product is vertical over
the base of its first component, which is the form the boundary map asks for. -/
public theorem isHomLift_fibreProduct_iso_hom
    (w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g) :
    pF.IsHomLift (𝟙 ((f ⋙ pF).obj w₀.x)) w₀.iso.hom := by
  rw [w₀.hx]
  exact w₀.vertical

end Vertical

/-! ### The two normalizations of the square-zero extension, compared -/

section Cross
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]
  {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

attribute [local implicit_reducible] squareZeroCrossUnder

/-- The comparison of the two normalizations of the square-zero extension depends on the base
object only up to the transport along an equality of base objects: both are the identity on
carriers. -/
public theorem eqToHom_comp_squareZeroCross {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (M : FGModuleCat.{max v w} k)
    (h : ((squareZeroAlgFunctor.{u, v, w} B).obj M).right =
      ((squareZeroAlgFunctor.{u, v, w} A).obj M).right) :
    eqToHom h ≫ squareZeroCross.{u, v, w} A M = squareZeroCross.{u, v, w} B M := by
  refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun t => ?_)
  show (squareZeroCross.{u, v, w} A M).hom ((eqToHom h).hom t) =
    (squareZeroCross.{u, v, w} B M).hom t
  rw [squareZeroCross_hom, squareZeroCross_hom]
  exact eq_of_heq (hom_eqToHom_apply_heq.{u, v, w} h t)

variable (f : H ⥤ F) {y₀ : H} (QH : ChosenPushforwardsAt (f ⋙ pF) y₀)
  (PF : ChosenPushforwardsAt pF (f.obj y₀)) (hcofF : IsCofiberedInGroupoids pF)
  (M : FGModuleCat.{max v w} k)

/-- **The comparison `b'` of the boundary map, read at the square-zero extension under the
base.** Transport along the comparison of the two normalizations carries a comparison of chosen
pushforwards at the extension read as an algebra under the base to
`Deformation.boundaryCompareFst`. Both sides lie over the coordinate arrow of that comparison,
and the chosen inclusion of `f(y₀)` is strongly cocartesian, so it is enough that they agree
after precomposition with it. -/
public theorem map_cross_comp_boundaryCompareFst
    (H₃ : (PF.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)).1 ≅
      f.obj (QH.obj (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)).1)
    (hi₃ : PF.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M) ≫ H₃.hom =
      f.map (QH.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)))
    (hl₃ : pF.IsHomLift (𝟙 (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M).right) H₃.hom) :
    PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom ≫
        (boundaryCompareFst.{u, v, w} f QH PF hcofF M).hom =
      H₃.hom ≫ f.map (QH.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom) := by
  have hL : pF.IsHomLift
      (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom.right
      (PF.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom ≫
        (boundaryCompareFst.{u, v, w} f QH PF hcofF M).hom) :=
    @IsHomLift.comp_lift_id_right' _ _ _ _ pF _ _ _ _ _ _ _
      (PF.map_isHomLift (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom)
      ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M) _
      (isHomLift_boundaryCompareFst.{u, v, w} f QH PF hcofF M).1
  have hR : pF.IsHomLift
      (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom.right
      (H₃.hom ≫
        f.map (QH.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom)) :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ pF _ _ _
      (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M).right H₃.hom hl₃ _ _ _ _
      (isHomLift_map_of_comp f
        (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom.right
        (QH.map (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom)
        (QH.map_isHomLift (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom))
  refine @Functor.IsStronglyCocartesian.ext _ _ _ _ pF _ _ _ _
    (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M).hom
    (PF.inclusion (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M))
    (PF.inclusion_cocartesian (squareZeroUnder.{u, v, w} (f ⋙ pF) y₀ M)) _ _
    (squareZeroCrossUnderIso.{u, v, w} ((f ⋙ pF).obj y₀) M).hom.right _ _ hL hR ?_
  rw [← Category.assoc, hi₃, ← f.map_comp]
  erw [QH.inclusion_map, ← Category.assoc, PF.inclusion_map]
  exact inclusion_comp_boundaryCompareFst_hom.{u, v, w} f QH PF hcofF M

end Cross

section Fibre
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]
  {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
  {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
  (PW : ChosenPushforwardsAt
    (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
  (M : FGModuleCat.{max v w} k)

attribute [local implicit_reducible] squareZeroCrossUnder

/-- A lift of an arrow `s` stays a lift of `s'` when `s'` is `s` precomposed with the transport
along an equality of the sources. -/
private theorem isHomLift_of_eqToHom_comp {E D : Type*} [Category E] [Category D] {p : E ⥤ D}
    {A A' B : D} {X Y : E} {φ : X ⟶ Y} {s : A ⟶ B} {s' : A' ⟶ B} (h : A' = A)
    (hs : eqToHom h ≫ s = s') (hφ : p.IsHomLift s φ) : p.IsHomLift s' φ := by
  subst h hs
  simpa using hφ

/-- The first component of the chosen inclusion of `w₀` into its pushforward to the re-based
square-zero extension lifts the structure arrow of the re-based extension over the base of
`w₀.x`, the two bases being equal. -/
public theorem isHomLift_inclusion_a :
    (f ⋙ pF).IsHomLift
      (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom
      (PW.inclusion
        (squareZeroCrossUnder.{u, v, w} w₀.base M)).a :=
  isHomLift_of_eqToHom_comp w₀.hx (eqToHom_comp_squareZeroCrossUnder_hom.{u, v, w} w₀.hx M)
    (TwoFibreProductOver.isHomLift_a
      (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M))
      (squareZeroCrossUnder.{u, v, w} w₀.base M).hom
      (PW.inclusion_cocartesian
        (squareZeroCrossUnder.{u, v, w} w₀.base M)).toIsHomLift)

/-- The second component, likewise. -/
public theorem isHomLift_inclusion_b :
    (g ⋙ pF).IsHomLift
      (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom
      (PW.inclusion
        (squareZeroCrossUnder.{u, v, w} w₀.base M)).b :=
  isHomLift_of_eqToHom_comp w₀.hy (eqToHom_comp_squareZeroCrossUnder_hom.{u, v, w} w₀.hy M)
    (TwoFibreProductOver.isHomLift_b
      (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M))
      (squareZeroCrossUnder.{u, v, w} w₀.base M).hom
      (PW.inclusion_cocartesian
        (squareZeroCrossUnder.{u, v, w} w₀.base M)).toIsHomLift)

variable (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x) (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
  (hcofH : IsCofiberedInGroupoids (f ⋙ pF)) (hcofG : IsCofiberedInGroupoids (g ⋙ pF))

/-- **The comparison of the chosen pushforward of `y₀` with the first component of the chosen
pushforward of `w₀`**, at the re-based square-zero extension. Both are codomains of strongly
cocartesian arrows out of `y₀` lifting the structure arrow of that extension. -/
public noncomputable def crossCompareFst :
    (QH.obj
        (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)).1 ≅
      (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.x :=
  letI := QH.inclusion_cocartesian
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids hcofH
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom
    (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).a
    (isHomLift_inclusion_a.{u, v, w} f g PW M)
  cocartesianCompare (f ⋙ pF)
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom
    (QH.inclusion
      (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M))
    (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).a

/-- The comparison is pinned by its composite with the chosen inclusion of `y₀`. -/
public theorem inclusion_comp_crossCompareFst_hom :
    QH.inclusion
          (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M) ≫
        (crossCompareFst.{u, v, w} f g PW M QH hcofH).hom =
      (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).a :=
  let := QH.inclusion_cocartesian
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hcofH
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom
    (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).a
    (isHomLift_inclusion_a.{u, v, w} f g PW M)
  comp_cocartesianCompare_hom (f ⋙ pF) _ _ _

/-- The comparison is vertical. -/
public theorem isHomLift_crossCompareFst :
    (f ⋙ pF).IsHomLift
      (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      (crossCompareFst.{u, v, w} f g PW M QH hcofH).hom :=
  let := QH.inclusion_cocartesian
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M)
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hcofH
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom
    (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).a
    (isHomLift_inclusion_a.{u, v, w} f g PW M)
  isHomLift_cocartesianCompare_hom (f ⋙ pF) _ _ _

/-- **The comparison of the chosen pushforward of `z₀` with the second component of the chosen
pushforward of `w₀`**, at the re-based square-zero extension. -/
public noncomputable def crossCompareSnd :
    (QG.obj
        (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)).1 ≅
      (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.y :=
  letI := QG.inclusion_cocartesian
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids hcofG
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom
    (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).b
    (isHomLift_inclusion_b.{u, v, w} f g PW M)
  cocartesianCompare (g ⋙ pF)
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom
    (QG.inclusion
      (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M))
    (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).b

/-- The comparison is pinned by its composite with the chosen inclusion of `z₀`. -/
public theorem inclusion_comp_crossCompareSnd_hom :
    QG.inclusion
          (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M) ≫
        (crossCompareSnd.{u, v, w} f g PW M QG hcofG).hom =
      (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).b :=
  let := QG.inclusion_cocartesian
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hcofG
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom
    (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).b
    (isHomLift_inclusion_b.{u, v, w} f g PW M)
  comp_cocartesianCompare_hom (g ⋙ pF) _ _ _

/-- The comparison is vertical. -/
public theorem isHomLift_crossCompareSnd :
    (g ⋙ pF).IsHomLift
      (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      (crossCompareSnd.{u, v, w} f g PW M QG hcofG).hom :=
  let := QG.inclusion_cocartesian
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M)
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hcofG
    (squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M).hom
    (PW.inclusion (squareZeroCrossUnder.{u, v, w} w₀.base M)).b
    (isHomLift_inclusion_b.{u, v, w} f g PW M)
  isHomLift_cocartesianCompare_hom (g ⋙ pF) _ _ _

end Fibre

/-! ### The keystone at the re-based square-zero extension -/

section Keystone2
open CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F]
  {pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : H ⥤ F) (g : G ⥤ F)
  {w₀ : TwoFibreProductOver (f ⋙ pF) (g ⋙ pF) pF f g}
  (PW : ChosenPushforwardsAt
    (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g) w₀)
  (QH : ChosenPushforwardsAt (f ⋙ pF) w₀.x) (QG : ChosenPushforwardsAt (g ⋙ pF) w₀.y)
  (PF : ChosenPushforwardsAt pF (f.obj w₀.x)) (M : FGModuleCat.{max v w} k)

attribute [local implicit_reducible] squareZeroCrossUnder

/-- **The cocartesian-uniqueness identification at the re-based square-zero extension.** The
comparison isomorphism carried by the chosen pushforward of `w₀` is the composite of the two
comparisons `b'` and `c'` of the boundary map, read through the comparisons of the two
components with the chosen pushforwards of `y₀` and of `z₀`. This is the source's
`w'₀ = (k[ε], y'₀, z'₀, c' ∘ b')` in the normalization in which the boundary map is built. -/
public theorem boundaryCompare_comp_crossCompare_eq
    (hcofF : IsCofiberedInGroupoids pF) (hcofH : IsCofiberedInGroupoids (f ⋙ pF))
    (hcofG : IsCofiberedInGroupoids (g ⋙ pF)) :
    (boundaryCompareFst.{u, v, w} f QH PF hcofF M).hom ≫
        f.map (crossCompareFst.{u, v, w} f g PW M QH hcofH).hom ≫
          (PW.obj
              (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.iso.hom =
      (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF
          M).hom ≫
        g.map (crossCompareSnd.{u, v, w} f g PW M QG hcofG).hom := by
  have hWb : (TwoFibreProductOver.structureFunctor (f ⋙ pF) (g ⋙ pF) pF f g).obj
      (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1 =
      (squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M :=
    (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).2
  have hLv : pF.IsHomLift
      (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      ((boundaryCompareFst.{u, v, w} f QH PF hcofF M).hom ≫
        f.map (crossCompareFst.{u, v, w} f g PW M QH hcofH).hom ≫
          (PW.obj
              (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.iso.hom) := by
    have h1 :=
      (isHomLift_boundaryCompareFst.{u, v, w} f QH PF hcofF M).1
    have h2 := isHomLift_map_of_comp f
      (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      (crossCompareFst.{u, v, w} f g PW M QH hcofH).hom
      (isHomLift_crossCompareFst.{u, v, w} f g PW M QH hcofH)
    have h3 := (PW.obj (squareZeroCrossUnder.{u, v, w} w₀.base M)).1.vertical
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ pF _ _ _ _ _ _ _ h1 _ _
      (@IsHomLift.comp_lift_id_right' _ _ _ _ pF _ _ _ _ _ _ _ h2 _ _ h3)
  have hRv : pF.IsHomLift (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      ((boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
          (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom ≫
        g.map (crossCompareSnd.{u, v, w} f g PW M QG hcofG).hom) := by
    have h1 := (isHomLift_boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
      (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).1
    have h2 := isHomLift_map_of_comp g
      (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M))
      (crossCompareSnd.{u, v, w} f g PW M QG hcofG).hom
      (isHomLift_crossCompareSnd.{u, v, w} f g PW M QG hcofG)
    exact @IsHomLift.comp_lift_id_right' _ _ _ _ pF _ _ _ _ _ _ _ h1 _ _ h2
  refine @Functor.IsStronglyCocartesian.ext _ _ _ _ pF _ _ _ _
    (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M).hom
    (PF.inclusion (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M))
    (PF.inclusion_cocartesian (squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M))
    _ _ (𝟙 ((squareZeroExtensionArtinian.{u, w, max v w} Λ k).obj M)) _ _ hLv hRv ?_
  set U := squareZeroCrossUnder.{u, v, w} ((f ⋙ pF).obj w₀.x) M with hU
  set V := squareZeroCrossUnder.{u, v, w} ((g ⋙ pF).obj w₀.y) M with hV
  set T := squareZeroCrossUnder.{u, v, w} w₀.base M with hT
  set bb := (boundaryCompareFst.{u, v, w} f QH PF hcofF M).hom with hbb
  set cc := (boundaryCompareSnd.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
    (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M).hom with hcc
  set u₁ := f.map (crossCompareFst.{u, v, w} f g PW M QH hcofH).hom with hu₁
  set u₂ := g.map (crossCompareSnd.{u, v, w} f g PW M QG hcofG).hom with hu₂
  set WI := (PW.obj T).1.iso.hom with hWI
  have hb : PF.inclusion U ≫ bb = f.map (QH.inclusion U) :=
    inclusion_comp_boundaryCompareFst_hom.{u, v, w} f QH PF hcofF M
  have hc : PF.inclusion U ≫ cc = w₀.iso.hom ≫ g.map (QG.inclusion V) :=
    inclusion_comp_boundaryCompareSnd_hom.{u, v, w} f g (w₀.hy.trans w₀.hx.symm)
      (isHomLift_fibreProduct_iso_hom.{u, v, w} pF f g w₀) QG PF hcofF M
  have hfst : QH.inclusion U ≫ (crossCompareFst.{u, v, w} f g PW M QH hcofH).hom =
      (PW.inclusion T).a :=
    inclusion_comp_crossCompareFst_hom.{u, v, w} f g PW M QH hcofH
  have hsnd : QG.inclusion V ≫ (crossCompareSnd.{u, v, w} f g PW M QG hcofG).hom =
      (PW.inclusion T).b :=
    inclusion_comp_crossCompareSnd_hom.{u, v, w} f g PW M QG hcofG
  have hL : PF.inclusion U ≫ bb ≫ u₁ ≫ WI = w₀.iso.hom ≫ g.map (PW.inclusion T).b := by
    rw [← Category.assoc, hb, hu₁, ← f.map_comp_assoc, hfst, (PW.inclusion T).w]
  have hR : PF.inclusion U ≫ cc ≫ u₂ = w₀.iso.hom ≫ g.map (PW.inclusion T).b := by
    rw [← Category.assoc, hc, Category.assoc, hu₂, ← g.map_comp, hsnd]
  exact hL.trans hR.symm

end Keystone2

end Deformation

end
