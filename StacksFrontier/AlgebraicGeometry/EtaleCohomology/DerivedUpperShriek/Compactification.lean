module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.ProjectionFormulaInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map `Rf_*RHom(K, L) ⟶ RHom(Rf_!K, Rf_!L)`

Let `f : X ⟶ Y` be a separated morphism of finite type between quasi-compact and
quasi-separated schemes and let `Λ` be a torsion coefficient ring. For `K`, `L` in
`D(X_étale, Λ)` there is a canonical map

`α : Rf_*RHom_Λ(K, L) ⟶ RHom_Λ(Rf_!K, Rf_!L)`,

functorial in `K` and in `L`. This is [Stacks, Tag 0GL7].

The construction is the one of the source. Choose a compactification, that is a factorisation
`f = f̄ ∘ j` with `j : X ⟶ X̄` an open immersion and `f̄ : X̄ ⟶ Y` proper, so that
`Rf_! = Rf̄_* ∘ j_!` and, by Leray, `Rf_* = Rf̄_* ∘ Rj_*`. Then:

* `β : Rj_*RHom_Λ(K, L) ⟶ RHom_Λ(j_!K, j_!L)` is the morphism whose adjunct under the
  tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(X̄_étale, Λ)` is
  `β' = j_!β''`, where `β''` is the evaluation `RHom_Λ(K, L) ⊗^L_Λ K ⟶ L` and the source of
  `β'` is identified with `j_!(RHom_Λ(K, L) ⊗^L_Λ K)` by [Stacks, Tag 0GL1] together with
  `j^{-1}Rj_* = id`;
* `γ : Rf̄_*RHom_Λ(j_!K, j_!L) ⟶ RHom_Λ(Rf̄_*j_!K, Rf̄_*j_!L)` is the canonical map of
  [Stacks, Tag 0B6D];
* `α = γ ∘ Rf̄_*β`.

## Main definitions

All in the namespace `Stacks.EtaleCohomology.DerivedUpperShriek`.

* `CompactificationData` — the three derived categories `D(X_étale, Λ)`, `D(X̄_étale, Λ)`,
  `D(Y_étale, Λ)` of a chosen compactification, each with its derived tensor product and its
  derived internal Hom tied together by the tensor–internal-Hom bijection of
  [Stacks, Tag 08J8], together with `j_!`, `Rj_*`, `Rf̄_*`, the extension-by-zero projection
  isomorphism of [Stacks, Tag 0GL1] and the relative cup product of [Stacks, Tag 0B6C].
* `CompactificationData.derivedLowerShriek` and `CompactificationData.derivedPushforward` —
  the composites `Rf_! = Rf̄_*j_!` and `Rf_* = Rf̄_*Rj_*`.
* `CompactificationData.openImmersionHomMap` — the map `β`.
* `CompactificationData.pushforwardHomMap` — the map `γ`, the canonical map of
  [Stacks, Tag 0B6D] in the present setting.
* `CompactificationData.lowerShriekHomMap` — **the map `α` of [Stacks, Tag 0GL7]**.

## Main results

* `CompactificationData.openImmersionHomMap_homEquiv` and
  `CompactificationData.pushforwardHomMap_homEquiv` — the adjunction identities that pin `β`
  and `γ`.
* `CompactificationData.lowerShriekHomMap_naturality_target` and
  `CompactificationData.lowerShriekHomMap_naturality_source` — `α` is covariant in `L` and
  contravariant in `K`, which is the functoriality the source asserts.
* `CompactificationData.openImmersionHomMap_naturality_target`,
  `...naturality_source`, `CompactificationData.pushforwardHomMap_naturality_target` and
  `...naturality_source` — the same for `β` and for `γ`.

## Implementation notes

*What is constructed and what is carried.* Of the inputs to the construction, none is a
morphism of the shape being constructed: `β`, `γ` and `α` all have bodies, and each of the two
adjuncts is pinned by an adjunction identity which is *proved*. What is carried as data is the
ambient structure the source's three cited results provide, in the shape in which the source
cites them.

The reason it is carried rather than used is that the development does not have `Rf_!` for a
separated finite-type morphism of quasi-compact quasi-separated schemes. Neither the Nagata
compactification of [Stacks, Tag 0F41] nor the derived lower shriek of [Stacks, Tag 0GJZ] is
present, and the derived pushforward and derived internal Hom that *are* present
(`Stacks.Cohomology.DerivedPushforward.derivedPushforward`,
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`) are stated for a ringed topos, not
for the small étale site with a coefficient ring. So the construction is made over the data a
compactification supplies, which is exactly the list of objects the source's seven-step recipe
mentions, and nothing more. Instantiating `CompactificationData` at the small étale site is
what [Stacks, Tag 0F41] and [Stacks, Tag 0GJZ] would supply.

*The tensor–internal-Hom bijection is carried as a `TensorHomAdjunction`.* This is the shape
already used by the development for [Stacks, Tag 0B6D], in
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi`: a family of bijections of
morphism groups indexed by all three objects together with its three naturality clauses. What
the development has unconditionally is the bijection of [Stacks, Tag 08J8] alone
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`); its naturality in the three objects is
the content of [Stacks, Tag 08J9] and is needed here because `α` is asserted to be
*functorial*. Carrying the bijection rather than an unconstrained bifunctor is what makes
`homU`, `homX`, `homY` the derived internal Homs and not arbitrary bifunctors: a right adjoint
of `− ⊗^L B` is determined up to canonical isomorphism.

*The projection isomorphism.* The source identifies the source of `β'`, namely
`Rj_*RHom_Λ(K, L) ⊗^L_Λ j_!K`, with `j_!(RHom_Λ(K, L) ⊗^L_Λ K)`. That identification is
[Stacks, Tag 0GL1], `M ⊗^L_Λ j_!B ≅ j_!(j^{-1}M ⊗^L_Λ B)`, composed with `j^{-1}Rj_* = id`,
which holds because `j` is an open immersion. The two are carried here as the single
isomorphism `projIso`, and as an isomorphism of *bifunctors* `(M, B) ↦ Rj_*M ⊗^L j_!B` and
`(M, B) ↦ j_!(M ⊗^L B)`, so that its naturality in both variables — which the functoriality of
`α` rests on — comes from `CategoryTheory.NatTrans.naturality` rather than from further
assumed equations. The underived form of [Stacks, Tag 0GL1] with extension by zero in the
right tensor slot is
`Stacks.Sites.InternalHomAndFlatness.extensionTensorBifunctorIso`, and the derived form with
it in the left slot is `Stacks.DerivedTensor.ExtensionByZero.derivedTensorExtensionIso`;
neither is available at the spelling of the small étale site with coefficients.

*The relative cup product* is carried for the same reason and in the same bifunctorial shape.
The development's relative cup product
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct` is [Stacks, Tag 0B6C]
for a morphism of ringed topoi; `cup` is its transcription as a natural transformation of
bifunctors on the derived categories of the compactification.

*Why `Rf_!` and `Rf_*` are composites rather than functors with Leray isomorphisms to them.*
The source writes "since `Rf_! = Rf̄_*j_!` and `Rf_* = Rf̄_*Rj_*` (by Leray)". Defining the two
functors as those composites makes the two identifications definitional and keeps the
statement of `α` the one of the source. The content of Leray in this setting — that the
composites are independent of the chosen compactification — is [Stacks, Tag 0F7I] and is a
separate result; it is not used in the construction of `α`, only in knowing that `α` does not
depend on the compactification, which the source does not assert here.

## References

* [Stacks Project, Tag 0GL7](https://stacks.math.columbia.edu/tag/0GL7)
* [Stacks Project, Tag 0B6D](https://stacks.math.columbia.edu/tag/0B6D)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0GL1](https://stacks.math.columbia.edu/tag/0GL1)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

namespace Stacks.EtaleCohomology.DerivedUpperShriek

universe v₁ u₁ v₂ u₂ v₃ u₃

/-- **The data of a compactification of a separated finite-type morphism**, as the construction
of the canonical map of [Stacks, Tag 0GL7] uses it.

`DU` stands for `D(X_étale, Λ)`, `DX` for `D(X̄_étale, Λ)` and `DY` for `D(Y_étale, Λ)`, where
`f = f̄ ∘ j` with `j : X ⟶ X̄` an open immersion and `f̄ : X̄ ⟶ Y` proper. Each of the three
carries its derived tensor product and its derived internal Hom, tied together by the
tensor–internal-Hom bijection of [Stacks, Tag 08J8]; `shriek` is `j_!`, `pushforwardJ` is
`Rj_*` and `pushforwardFbar` is `Rf̄_*`. The last two fields are the extension-by-zero
projection isomorphism of [Stacks, Tag 0GL1] — composed with `j^{-1}Rj_* = id` — and the
relative cup product of [Stacks, Tag 0B6C], each in bifunctorial form. -/
structure CompactificationData (DU : Type u₁) [Category.{v₁} DU] (DX : Type u₂)
    [Category.{v₂} DX] (DY : Type u₃) [Category.{v₃} DY] where
  /-- The derived tensor product `− ⊗^L_Λ −` on `D(X_étale, Λ)`. -/
  tensorU : DU ⥤ DU ⥤ DU
  /-- The derived internal Hom `RHom_Λ(−, −)` on `D(X_étale, Λ)`. -/
  homU : DUᵒᵖ ⥤ DU ⥤ DU
  /-- The tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(X_étale, Λ)`. -/
  adjU : TensorHomAdjunction tensorU homU
  /-- The derived tensor product `− ⊗^L_Λ −` on `D(X̄_étale, Λ)`. -/
  tensorX : DX ⥤ DX ⥤ DX
  /-- The derived internal Hom `RHom_Λ(−, −)` on `D(X̄_étale, Λ)`. -/
  homX : DXᵒᵖ ⥤ DX ⥤ DX
  /-- The tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(X̄_étale, Λ)`. -/
  adjX : TensorHomAdjunction tensorX homX
  /-- The derived tensor product `− ⊗^L_Λ −` on `D(Y_étale, Λ)`. -/
  tensorY : DY ⥤ DY ⥤ DY
  /-- The derived internal Hom `RHom_Λ(−, −)` on `D(Y_étale, Λ)`. -/
  homY : DYᵒᵖ ⥤ DY ⥤ DY
  /-- The tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(Y_étale, Λ)`. -/
  adjY : TensorHomAdjunction tensorY homY
  /-- Extension by zero `j_!` along the open immersion `j : X ⟶ X̄`. -/
  shriek : DU ⥤ DX
  /-- Derived direct image `Rj_*` along the open immersion `j : X ⟶ X̄`. -/
  pushforwardJ : DU ⥤ DX
  /-- Derived direct image `Rf̄_*` along the proper morphism `f̄ : X̄ ⟶ Y`. -/
  pushforwardFbar : DX ⥤ DY
  /-- The projection isomorphism `Rj_*M ⊗^L_Λ j_!B ≅ j_!(M ⊗^L_Λ B)`: [Stacks, Tag 0GL1]
  together with `j^{-1}Rj_* = id`, as an isomorphism of bifunctors. -/
  projIso : (pushforwardJ ⋙ tensorX) ⋙ (Functor.whiskeringLeft DU DX DX).obj shriek ≅
    tensorU ⋙ (Functor.whiskeringRight DU DU DX).obj shriek
  /-- The relative cup product `Rf̄_*A ⊗^L_Λ Rf̄_*B ⟶ Rf̄_*(A ⊗^L_Λ B)` of
  [Stacks, Tag 0B6C], as a natural transformation of bifunctors. -/
  cup : (pushforwardFbar ⋙ tensorY) ⋙ (Functor.whiskeringLeft DX DY DY).obj pushforwardFbar ⟶
    tensorX ⋙ (Functor.whiskeringRight DX DX DY).obj pushforwardFbar

/-- Naturality in the target of the adjunct of a morphism `π : P ⊗ A ⟶ M`. -/
private theorem comp_homEquiv_symm_target {C : Type*} [Category C] {T : C ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : TensorHomAdjunction T H) {P P' A M M' : C} (p : P ⟶ P')
    (m : M ⟶ M') (π : (T.obj P).obj A ⟶ M) (π' : (T.obj P').obj A ⟶ M')
    (h : (T.map p).app A ≫ π' = π ≫ m) :
    p ≫ (adj.homEquiv P' A M').symm π' = (adj.homEquiv P A M).symm π ≫ (H.obj (op A)).map m := by
  apply (adj.homEquiv P A M').injective
  rw [adj.homEquiv_naturality_source, adj.homEquiv_naturality_target, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, h]

/-- Naturality in the source of the adjunct of a morphism `π : P ⊗ A ⟶ M`. -/
private theorem comp_homEquiv_symm_source {C : Type*} [Category C] {T : C ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : TensorHomAdjunction T H) {P P' A A' M : C} (p : P ⟶ P')
    (a : A' ⟶ A) (π : (T.obj P).obj A ⟶ M) (π' : (T.obj P').obj A' ⟶ M)
    (h : (T.map p).app A' ≫ π' = (T.obj P).map a ≫ π) :
    p ≫ (adj.homEquiv P' A' M).symm π' = (adj.homEquiv P A M).symm π ≫ (H.map a.op).app M := by
  apply (adj.homEquiv P A' M).injective
  rw [adj.homEquiv_naturality_source, adj.homEquiv_naturality_middle, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, h]

namespace CompactificationData

variable {DU : Type u₁} [Category.{v₁} DU] {DX : Type u₂} [Category.{v₂} DX]
  {DY : Type u₃} [Category.{v₃} DY] (data : CompactificationData DU DX DY)

/-- `Rf_! = Rf̄_* ∘ j_!`, the derived lower shriek read off the chosen compactification. -/
abbrev derivedLowerShriek : DU ⥤ DY := data.shriek ⋙ data.pushforwardFbar

/-- `Rf_* = Rf̄_* ∘ Rj_*`, the derived direct image read off the chosen compactification by
Leray. -/
abbrev derivedPushforward : DU ⥤ DY := data.pushforwardJ ⋙ data.pushforwardFbar

/-! ### Naturality of the two carried bifunctorial inputs -/

/-- The projection isomorphism of [Stacks, Tag 0GL1] is natural in the object pushed forward. -/
theorem projIso_naturality_left {M M' : DU} (m : M ⟶ M') (B : DU) :
    (data.tensorX.map (data.pushforwardJ.map m)).app (data.shriek.obj B) ≫
        (data.projIso.hom.app M').app B =
      (data.projIso.hom.app M).app B ≫ data.shriek.map ((data.tensorU.map m).app B) :=
  congrArg (fun φ => NatTrans.app φ B) (data.projIso.hom.naturality m)

/-- The projection isomorphism of [Stacks, Tag 0GL1] is natural in the object extended by
zero. -/
theorem projIso_naturality_right (M : DU) {B B' : DU} (b : B ⟶ B') :
    (data.tensorX.obj (data.pushforwardJ.obj M)).map (data.shriek.map b) ≫
        (data.projIso.hom.app M).app B' =
      (data.projIso.hom.app M).app B ≫ data.shriek.map ((data.tensorU.obj M).map b) :=
  (data.projIso.hom.app M).naturality b

/-- The relative cup product of [Stacks, Tag 0B6C] is natural in its first variable. -/
theorem cup_naturality_left {A A' : DX} (a : A ⟶ A') (B : DX) :
    (data.tensorY.map (data.pushforwardFbar.map a)).app (data.pushforwardFbar.obj B) ≫
        (data.cup.app A').app B =
      (data.cup.app A).app B ≫ data.pushforwardFbar.map ((data.tensorX.map a).app B) :=
  congrArg (fun φ => NatTrans.app φ B) (data.cup.naturality a)

/-- The relative cup product of [Stacks, Tag 0B6C] is natural in its second variable. -/
theorem cup_naturality_right (A : DX) {B B' : DX} (b : B ⟶ B') :
    (data.tensorY.obj (data.pushforwardFbar.obj A)).map (data.pushforwardFbar.map b) ≫
        (data.cup.app A).app B' =
      (data.cup.app A).app B ≫ data.pushforwardFbar.map ((data.tensorX.obj A).map b) :=
  (data.cup.app A).naturality b

/-! ### The map `β` along the open immersion -/

/-- **The map `β` of [Stacks, Tag 0GL7]**, `Rj_*RHom_Λ(K, L) ⟶ RHom_Λ(j_!K, j_!L)`: the
morphism whose adjunct under the tensor–internal-Hom bijection on `D(X̄_étale, Λ)` is
`β' = j_!β''`, where `β''` is the evaluation `RHom_Λ(K, L) ⊗^L_Λ K ⟶ L` and the source of `β'`
is identified with `j_!(RHom_Λ(K, L) ⊗^L_Λ K)` by the projection isomorphism. -/
def openImmersionHomMap (K L : DU) :
    data.pushforwardJ.obj ((data.homU.obj (op K)).obj L) ⟶
      (data.homX.obj (op (data.shriek.obj K))).obj (data.shriek.obj L) :=
  (data.adjX.homEquiv (data.pushforwardJ.obj ((data.homU.obj (op K)).obj L))
      (data.shriek.obj K) (data.shriek.obj L)).symm
    ((data.projIso.hom.app ((data.homU.obj (op K)).obj L)).app K ≫
      data.shriek.map (data.adjU.evaluation K L))

/-- **The adjunction identity pinning `β`**: its adjunct under the tensor–internal-Hom
bijection on `D(X̄_étale, Λ)` is the projection isomorphism followed by `j_!` of the
evaluation. -/
theorem openImmersionHomMap_homEquiv (K L : DU) :
    data.adjX.homEquiv (data.pushforwardJ.obj ((data.homU.obj (op K)).obj L))
        (data.shriek.obj K) (data.shriek.obj L) (data.openImmersionHomMap K L) =
      (data.projIso.hom.app ((data.homU.obj (op K)).obj L)).app K ≫
        data.shriek.map (data.adjU.evaluation K L) :=
  (data.adjX.homEquiv _ _ _).apply_symm_apply _

/-- **`β` is covariant in the target `L`.** -/
theorem openImmersionHomMap_naturality_target (K : DU) {L L' : DU} (l : L ⟶ L') :
    data.pushforwardJ.map ((data.homU.obj (op K)).map l) ≫ data.openImmersionHomMap K L' =
      data.openImmersionHomMap K L ≫
        (data.homX.obj (op (data.shriek.obj K))).map (data.shriek.map l) := by
  refine comp_homEquiv_symm_target data.adjX _ _ _ _ ?_
  rw [reassoc_of% (data.projIso_naturality_left ((data.homU.obj (op K)).map l) K),
    ← Functor.map_comp, data.adjU.evaluation_naturality_target K l, Functor.map_comp,
    Category.assoc]

/-- **`β` is contravariant in the source `K`.** -/
theorem openImmersionHomMap_naturality_source {K K' : DU} (k : K' ⟶ K) (L : DU) :
    data.pushforwardJ.map ((data.homU.map k.op).app L) ≫ data.openImmersionHomMap K' L =
      data.openImmersionHomMap K L ≫
        (data.homX.map (data.shriek.map k).op).app (data.shriek.obj L) := by
  refine comp_homEquiv_symm_source data.adjX _ _ _ _ ?_
  rw [reassoc_of% (data.projIso_naturality_left ((data.homU.map k.op).app L) K'),
    ← Functor.map_comp, data.adjU.evaluation_naturality_source k L, Functor.map_comp,
    ← reassoc_of% (data.projIso_naturality_right ((data.homU.obj (op K)).obj L) k)]

/-! ### The map `γ` along the proper morphism -/

/-- **The map `γ` of [Stacks, Tag 0GL7]**,
`Rf̄_*RHom_Λ(A, B) ⟶ RHom_Λ(Rf̄_*A, Rf̄_*B)`: the canonical map of [Stacks, Tag 0B6D], the
morphism whose adjunct under the tensor–internal-Hom bijection on `D(Y_étale, Λ)` is the
relative cup product followed by `Rf̄_*` of the evaluation. -/
def pushforwardHomMap (A B : DX) :
    data.pushforwardFbar.obj ((data.homX.obj (op A)).obj B) ⟶
      (data.homY.obj (op (data.pushforwardFbar.obj A))).obj (data.pushforwardFbar.obj B) :=
  (data.adjY.homEquiv (data.pushforwardFbar.obj ((data.homX.obj (op A)).obj B))
      (data.pushforwardFbar.obj A) (data.pushforwardFbar.obj B)).symm
    ((data.cup.app ((data.homX.obj (op A)).obj B)).app A ≫
      data.pushforwardFbar.map (data.adjX.evaluation A B))

/-- **The adjunction identity pinning `γ`**: its adjunct under the tensor–internal-Hom
bijection on `D(Y_étale, Λ)` is the relative cup product followed by `Rf̄_*` of the
evaluation. -/
theorem pushforwardHomMap_homEquiv (A B : DX) :
    data.adjY.homEquiv (data.pushforwardFbar.obj ((data.homX.obj (op A)).obj B))
        (data.pushforwardFbar.obj A) (data.pushforwardFbar.obj B)
        (data.pushforwardHomMap A B) =
      (data.cup.app ((data.homX.obj (op A)).obj B)).app A ≫
        data.pushforwardFbar.map (data.adjX.evaluation A B) :=
  (data.adjY.homEquiv _ _ _).apply_symm_apply _

/-- **`γ` is covariant in the target `B`.** -/
theorem pushforwardHomMap_naturality_target (A : DX) {B B' : DX} (b : B ⟶ B') :
    data.pushforwardFbar.map ((data.homX.obj (op A)).map b) ≫ data.pushforwardHomMap A B' =
      data.pushforwardHomMap A B ≫
        (data.homY.obj (op (data.pushforwardFbar.obj A))).map
          (data.pushforwardFbar.map b) := by
  refine comp_homEquiv_symm_target data.adjY _ _ _ _ ?_
  rw [reassoc_of% (data.cup_naturality_left ((data.homX.obj (op A)).map b) A),
    ← Functor.map_comp, data.adjX.evaluation_naturality_target A b, Functor.map_comp,
    Category.assoc]

/-- **`γ` is contravariant in the source `A`.** -/
theorem pushforwardHomMap_naturality_source {A A' : DX} (a : A' ⟶ A) (B : DX) :
    data.pushforwardFbar.map ((data.homX.map a.op).app B) ≫ data.pushforwardHomMap A' B =
      data.pushforwardHomMap A B ≫
        (data.homY.map (data.pushforwardFbar.map a).op).app
          (data.pushforwardFbar.obj B) := by
  refine comp_homEquiv_symm_source data.adjY _ _ _ _ ?_
  rw [reassoc_of% (data.cup_naturality_left ((data.homX.map a.op).app B) A'),
    ← Functor.map_comp, data.adjX.evaluation_naturality_source a B, Functor.map_comp,
    ← reassoc_of% (data.cup_naturality_right ((data.homX.obj (op A)).obj B) a)]

/-! ### The map `α` -/

/-- **The canonical map `α` of [Stacks, Tag 0GL7]**,

`α : Rf_*RHom_Λ(K, L) ⟶ RHom_Λ(Rf_!K, Rf_!L)`,

for a chosen compactification `f = f̄ ∘ j`. It is `γ ∘ Rf̄_*β`, with `Rf_! = Rf̄_*j_!` and
`Rf_* = Rf̄_*Rj_*`. -/
@[stacks 0GL7 "the canonical map α, for a chosen compactification, at abstract compactification \
  data; its instance at the étale derived categories, which is the faithful registration of 0GL7, \
  is `Stacks.EtaleCohomology.etaleLowerShriekHomMap`"]
def lowerShriekHomMap (K L : DU) :
    data.derivedPushforward.obj ((data.homU.obj (op K)).obj L) ⟶
      (data.homY.obj (op (data.derivedLowerShriek.obj K))).obj
        (data.derivedLowerShriek.obj L) :=
  data.pushforwardFbar.map (data.openImmersionHomMap K L) ≫
    data.pushforwardHomMap (data.shriek.obj K) (data.shriek.obj L)

/-- **`α = γ ∘ Rf̄_*β`**, the factorisation along the chosen compactification by which the
canonical map of [Stacks, Tag 0GL7] is defined. -/
@[stacks 0GL7 "the factorisation α = γ ∘ Rf̄_*β, at abstract compactification data; at the étale \
  derived categories it is `Stacks.EtaleCohomology.etaleLowerShriekHomMap_eq`"]
theorem lowerShriekHomMap_eq (K L : DU) :
    data.lowerShriekHomMap K L =
      data.pushforwardFbar.map (data.openImmersionHomMap K L) ≫
        data.pushforwardHomMap (data.shriek.obj K) (data.shriek.obj L) :=
  rfl

/-- **The canonical map of [Stacks, Tag 0GL7] is covariant in `L`**, one half of the
functoriality the source asserts. -/
@[stacks 0GL7 "functoriality of α in L, at abstract compactification data; at the étale derived \
  categories it is `Stacks.EtaleCohomology.etaleLowerShriekHomMap_naturality_target`"]
theorem lowerShriekHomMap_naturality_target (K : DU) {L L' : DU} (l : L ⟶ L') :
    data.derivedPushforward.map ((data.homU.obj (op K)).map l) ≫
        data.lowerShriekHomMap K L' =
      data.lowerShriekHomMap K L ≫
        (data.homY.obj (op (data.derivedLowerShriek.obj K))).map
          (data.derivedLowerShriek.map l) := by
  have hβ := data.openImmersionHomMap_naturality_target K l
  have hγ := data.pushforwardHomMap_naturality_target (data.shriek.obj K) (data.shriek.map l)
  dsimp only [lowerShriekHomMap, Functor.comp_map, Functor.comp_obj]
  rw [← Functor.map_comp_assoc, hβ, Functor.map_comp, Category.assoc, hγ, Category.assoc]

/-- **The canonical map of [Stacks, Tag 0GL7] is contravariant in `K`**, the other half of the
functoriality the source asserts. -/
@[stacks 0GL7 "functoriality of α in K, at abstract compactification data; at the étale derived \
  categories it is `Stacks.EtaleCohomology.etaleLowerShriekHomMap_naturality_source`"]
theorem lowerShriekHomMap_naturality_source {K K' : DU} (k : K' ⟶ K) (L : DU) :
    data.derivedPushforward.map ((data.homU.map k.op).app L) ≫
        data.lowerShriekHomMap K' L =
      data.lowerShriekHomMap K L ≫
        (data.homY.map (data.derivedLowerShriek.map k).op).app
          (data.derivedLowerShriek.obj L) := by
  have hβ := data.openImmersionHomMap_naturality_source k L
  have hγ := data.pushforwardHomMap_naturality_source (data.shriek.map k) (data.shriek.obj L)
  dsimp only [lowerShriekHomMap, Functor.comp_map, Functor.comp_obj]
  rw [← Functor.map_comp_assoc, hβ, Functor.map_comp, Category.assoc, hγ, Category.assoc]

end CompactificationData

end Stacks.EtaleCohomology.DerivedUpperShriek

end
