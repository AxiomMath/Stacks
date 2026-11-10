module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleCoveringEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcAtlasReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcDescentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcUniformReading
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberPerMemberIsoDirect
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteDatumSheaf

/-!
# Transitivity of effective descent for quasi-coherent modules

Let `ρ : R ⟶ X` be a one-member surjective étale covering of an algebraic space, let
`(w i : W i ⟶ R)` be an fpqc covering of `R`, and let `D` be a descent datum for quasi-coherent
modules relative to the composites `(w i ≫ ρ : W i ⟶ X)`.  Suppose the base change of `D` to
`R` — `AlgebraicGeometry.Space.QuasiCoherentDescent.baseChangeDatum` — is effective, by
isomorphisms `ε i : D.F i ≅ (w i)^*N` of its component modules with the inverse images of an
`𝒪_R`-module `N`.  **Then `D` itself is effective.**

This is the transitivity of effective descent, and it is the last step of the effectivity clause
of Stacks 04W8.  The chain:

* the readings of `D` glue, along a two-leg covering of `R ×_X R`, into a pairwise isomorphism
  `ψ` of the two inverse images of `N` — `…exists_mapIso_eq_unreadIso_readN` — whose reading on
  every test space mapping to members of `(w i)` is the reading of `D`;
* that uniform reading makes the cocycle condition of `(N, ψ)` the composition law of the
  readings, `…readN_trans`, after a test space is covered by spaces mapping to members over all
  three of its morphisms to `R` — `…exists_isFpqcCovering_legTriple`;
* `(N, ψ)` is therefore a descent datum relative to the one-member family `{ρ}`, which is an
  étale covering, so it is effective by `…isEffective_of_isEtaleCovering`: there are a
  quasi-coherent `𝒪_X`-module `M` and an isomorphism `ν : N ≅ ρ^*M` carrying `ψ` to the
  canonical comparison of Stacks 04W5 of `M`;
* the components `ε i`, composed with `ν`, identify the component modules of `D` with the
  inverse images of `M`, and their compatibility with the pairwise isomorphisms of `D` is the
  uniform reading again, read on a covering of each pairwise fibre product.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.oneMemberDatum` is the descent datum `(N, ψ)`
  relative to `{ρ}`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.compModuleIso` is the identification of the
  component modules of `D` with the inverse images of `M`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_eq_readN`: the reading of `ψ` on a
  test space mapping to members of `(w i)` is the reading of `D`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readN_trans_mapIso_nu`: **the reading of `D`,
  conjugated by `ν`, is the canonical comparison of Stacks 04W5 of `M`.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_of_isEffective_baseChangeDatum`:
  **Transitivity of effective descent.**
* `AlgebraicGeometry.Space.QuasiCoherentDescent.isEffective_of_isFpqcCovering_comp`: the
  transitivity statement in the shape the reduction of the effectivity clause of Stacks 04W8
  consumes, with `N` and `ε` produced from the effectivity over `R` rather than assumed.

## Implementation notes

Every step is a declaration of its own and every statement is an equality of *isomorphisms*
until the last possible moment; the passages to morphisms are the three the interfaces ask for
(the pairwise condition of a morphism of descent data, and the two injectivity statements).

The pairwise condition of the last step cannot be read off the uniform reading at the pairwise
fibre product itself: the reading of `D.transition i j` on a test space is
`…transitionOn` at a morphism into that fibre product, and at the fibre product itself that
morphism is the identity, where the comparisons of Stacks 03LU do not cancel.  So the condition
is proved after pullback along a covering of the fibre product, where the morphism is a member
of the covering and the reading is available.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Components

variable {I : Type v} {X : AlgebraicSpaces B S hS} {Y : I → AlgebraicSpaces B S hS}
  {f : ∀ i, Y i ⟶ X}

/-- The component isomorphism of an isomorphism of descent data. -/
def DescentDatum.appIso {D E : DescentDatum B S hS Y f} (e : D ≅ E) (i : I) : D.F i ≅ E.F i where
  hom := e.hom.app i
  inv := e.inv.app i
  hom_inv_id := by
    simpa only [DescentDatum.comp_app, DescentDatum.id_app] using
      congrArg (fun a : D ⟶ D => a.app i) e.hom_inv_id
  inv_hom_id := by
    simpa only [DescentDatum.comp_app, DescentDatum.id_app] using
      congrArg (fun a : E ⟶ E => a.app i) e.inv_hom_id

/-- The forward morphism of `DescentDatum.appIso e i` is the component `e.hom.app i` of `e`. -/
@[simp]
theorem DescentDatum.appIso_hom {D E : DescentDatum B S hS Y f} (e : D ≅ E) (i : I) :
    (DescentDatum.appIso B S hS e i).hom = e.hom.app i :=
  rfl

/-- **The component isomorphisms of an isomorphism of descent data intertwine the two pairwise
isomorphisms**, as an equality of isomorphisms.  It is stated at variable descent data, so that a
consumer whose data are concrete instantiates it rather than projecting a structure field
underneath a composite. -/
theorem appIso_naturality {D E : DescentDatum B S hS Y f} (e : D ≅ E) (i j : I) :
    (modulePullback B S hS (pairFst B S hS Y f i j)).mapIso
          (DescentDatum.appIso B S hS e i) ≪≫ E.transition i j =
      D.transition i j ≪≫ (modulePullback B S hS (pairSnd B S hS Y f i j)).mapIso
        (DescentDatum.appIso B S hS e j) :=
  Iso.ext (by
    simpa only [Iso.trans_hom, Functor.mapIso_hom, DescentDatum.appIso_hom]
      using e.hom.naturality i j)

/-- The inverse image along a morphism into a pairwise fibre product of a pairwise isomorphism
of a descent datum, written through the reading of that isomorphism on the source. -/
theorem modulePullback_mapIso_transition (D : DescentDatum B S hS Y f)
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Y f i j) (vi : T ⟶ Y i)
    (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) :
    (modulePullback B S hS v).mapIso (D.transition i j) =
      (pullbackComparison B S hS v (pairFst B S hS Y f i j) vi hi (D.F i)).symm ≪≫
        transitionOn B S hS Y f D.F D.transition i j v vi vj hi hj ≪≫
        pullbackComparison B S hS v (pairSnd B S hS Y f i j) vj hj (D.F j) := by
  rw [transitionOn]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.symm_self_id, Iso.trans_refl]

end Components

section Transitivity

variable {I : Type v} {X R : AlgebraicSpaces B S hS} (W : I → AlgebraicSpaces B S hS)
  (w : ∀ i, W i ⟶ R) (ρ : R ⟶ X) (D : DescentDatum B S hS W (fun t => w t ≫ ρ))
  (N : Modules.{u, u} B S hS R.1 R.2)
  (ε : ∀ i, D.F i ≅ (modulePullback B S hS (w i)).obj N)
  (hcan : ∀ i j, (modulePullback B S hS (pairFst B S hS W w i j)).mapIso (ε i) ≪≫
      canonicalComparison (pairFst B S hS W w i j) (pairSnd B S hS W w i j) (w i) (w j)
        (pair_condition B S hS W w i j) N =
    baseChangeTransition B S hS W w ρ D i j ≪≫
      (modulePullback B S hS (pairSnd B S hS W w i j)).mapIso (ε j))
  (ψ : (modulePullback B S hS
      (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)).obj N ≅
    (modulePullback B S hS
      (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)).obj N)
  (hψ : ∀ (T : AlgebraicSpaces B S hS)
      (q : T ⟶ pair B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) (i j : I)
      (α : T ⟶ W i) (β : T ⟶ W j) (xx yy : T ⟶ R)
      (hqx : q ≫ pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = xx)
      (hqy : q ≫ pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = yy)
      (hax : α ≫ w i = xx) (hby : β ≫ w j = yy)
      (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
      (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
      (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β),
    (modulePullback B S hS q).mapIso ψ =
      unreadIso B S hS N
        (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)
        (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) q xx yy hqx hqy
        (readN B S hS W w ρ D N ε i j α β xx yy hax hby v hv₁ hv₂))

include hψ in
/-- **The reading of `ψ` on a test space mapping to members of the covering is the reading of
`D`.**  This is the uniform reading with the two comparisons of Stacks 03LU cancelled, which is
the form the pairwise isomorphisms of a descent datum relative to the one-member family `{ρ}` are
read in. -/
theorem transitionOn_eq_readN {T : AlgebraicSpaces B S hS}
    (q : T ⟶ pair B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) (i j : I)
    (α : T ⟶ W i) (β : T ⟶ W j) (xx yy : T ⟶ R)
    (hqx : q ≫ pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = xx)
    (hqy : q ≫ pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = yy)
    (hax : α ≫ w i = xx) (hby : β ≫ w j = yy)
    (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β) :
    transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) (fun _ => N) (fun _ _ => ψ)
        ⟨⟩ ⟨⟩ q xx yy hqx hqy =
      readN B S hS W w ρ D N ε i j α β xx yy hax hby v hv₁ hv₂ := by
  rw [transitionOn, hψ T q i j α β xx yy hqx hqy hax hby v hv₁ hv₂, unreadIso]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id, Iso.trans_refl]

include hψ in
/-- **One member of a covering of a test space identifies the two sides of the cocycle condition
of `(N, ψ)` there.**  On the member all three readings of `ψ` are readings of `D`, by
`…transitionOn_eq_readN`, and those compose by `…readN_trans`. -/
theorem transitionOn_trans_member {T : AlgebraicSpaces B S hS} (vi vj vk : T ⟶ R)
    (vij vjk vik : T ⟶ pair B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)
    (hij₀ : vij ≫ pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = vi)
    (hij₁ : vij ≫ pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = vj)
    (hjk₀ : vjk ≫ pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = vj)
    (hjk₁ : vjk ≫ pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = vk)
    (hik₀ : vik ≫ pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = vi)
    (hik₁ : vik ≫ pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ = vk)
    {P : AlgebraicSpaces B S hS} (cn : P ⟶ T) (i j k : I) (an : P ⟶ W i) (bn : P ⟶ W j)
    (dn : P ⟶ W k) (han : an ≫ w i = cn ≫ vi) (hbn : bn ≫ w j = cn ≫ vj)
    (hdn : dn ≫ w k = cn ≫ vk) :
    (modulePullback B S hS cn).mapIso
        (transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) (fun _ => N)
            (fun _ _ => ψ) ⟨⟩ ⟨⟩ vij vi vj hij₀ hij₁ ≪≫
          transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) (fun _ => N)
            (fun _ _ => ψ) ⟨⟩ ⟨⟩ vjk vj vk hjk₀ hjk₁) =
      (modulePullback B S hS cn).mapIso
        (transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) (fun _ => N)
          (fun _ _ => ψ) ⟨⟩ ⟨⟩ vik vi vk hik₀ hik₁) := by
  have key : ∀ (i j : I) (a : P ⟶ W i) (b : P ⟶ W j) u x y h₀ h₁
      (ha : a ≫ w i = cn ≫ x) (hb : b ≫ w j = cn ≫ y),
      ∃ v hv₁ hv₂,
        (modulePullback B S hS cn).mapIso
            (transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) (fun _ => N)
              (fun _ _ => ψ) ⟨⟩ ⟨⟩ u x y h₀ h₁) =
          (pullbackComparison B S hS cn x (a ≫ w i) ha.symm N).symm ≪≫
            readN B S hS W w ρ D N ε i j a b (a ≫ w i) (b ≫ w j) rfl rfl v hv₁ hv₂ ≪≫
            pullbackComparison B S hS cn y (b ≫ w j) hb.symm N := by
    intro i j a b u x y h₀ h₁ ha hb
    obtain ⟨v, hv₁, hv₂⟩ := exists_pairLeg B S hS W (fun t => w t ≫ ρ) i j a b
      (by rw [← Category.assoc, ← Category.assoc, ha, hb, Category.assoc, Category.assoc,
        ← h₀, ← h₁, Category.assoc, Category.assoc,
        pair_condition B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩])
    refine ⟨v, hv₁, hv₂, ?_⟩
    rw [modulePullback_mapIso_transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ)
      (fun _ => N) (fun _ _ => ψ) cn ⟨⟩ ⟨⟩ u x y h₀ h₁ (a ≫ w i) (b ≫ w j) ha.symm hb.symm
      (by rw [Category.assoc, h₀, ha]) (by rw [Category.assoc, h₁, hb]),
      transitionOn_eq_readN B S hS W w ρ D N ε ψ hψ (cn ≫ u) i j a b (a ≫ w i) (b ≫ w j)
        (by rw [Category.assoc, h₀, ha]) (by rw [Category.assoc, h₁, hb]) rfl rfl v hv₁ hv₂]
  obtain ⟨vij', hvij₁, hvij₂, e₁⟩ := key i j an bn vij vi vj hij₀ hij₁ han hbn
  obtain ⟨vjk', hvjk₁, hvjk₂, e₂⟩ := key j k bn dn vjk vj vk hjk₀ hjk₁ hbn hdn
  obtain ⟨vik', hvik₁, hvik₂, e₃⟩ := key i k an dn vik vi vk hik₀ hik₁ han hdn
  rw [Functor.mapIso_trans, e₁, e₂, e₃]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [Iso.subst_trans₂ (readN_trans B S hS W w ρ D N ε i j k an bn dn (an ≫ w i) (bn ≫ w j)
    (dn ≫ w k) rfl rfl rfl vij' hvij₁ hvij₂ vjk' hvjk₁ hvjk₂ vik' hvik₁ hvik₂)]

include hψ in
/-- **The cocycle condition of `(N, ψ)`.**  A test space with three morphisms to `R` agreeing
over `X` is covered, in the fpqc topology, by spaces mapping to members of `(w i)` over all
three, by `…exists_isFpqcCovering_legTriple`; there the two sides agree by
`…transitionOn_trans_member`, and the faithfulness half of Stacks 04W8 carries that back. -/
theorem transitionOn_trans (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    (i j k : PUnit.{v + 1}) (T : AlgebraicSpaces B S hS) (vi vj vk : T ⟶ R)
    (vij : T ⟶ pair B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) i j)
    (vjk : T ⟶ pair B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) j k)
    (vik : T ⟶ pair B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) i k)
    (hij₀ : vij ≫ pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) i j = vi)
    (hij₁ : vij ≫ pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) i j = vj)
    (hjk₀ : vjk ≫ pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) j k = vj)
    (hjk₁ : vjk ≫ pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) j k = vk)
    (hik₀ : vik ≫ pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) i k = vi)
    (hik₁ : vik ≫ pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) i k = vk) :
    transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) (fun _ => N) (fun _ _ => ψ)
          i j vij vi vj hij₀ hij₁ ≪≫
        transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) (fun _ => N)
          (fun _ _ => ψ) j k vjk vj vk hjk₀ hjk₁ =
      transitionOn B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) (fun _ => N)
        (fun _ _ => ψ) i k vik vi vk hik₀ hik₁ := by
  obtain rfl : i = PUnit.unit := rfl
  obtain rfl : j = PUnit.unit := rfl
  obtain rfl : k = PUnit.unit := rfl
  obtain ⟨K₃, Z₃, c₃, ι₃, κ₃, lam₃, a₃, b₃, d₃, hcov₃, ha₃, hb₃, hd₃⟩ :=
    exists_isFpqcCovering_legTriple B S hS W w hw vi vj vk
  refine Iso.ext (modulePullback_map_injective_of_isFpqcCovering B S hS
    (reprFpqcHomInjective B S hS) Z₃ c₃ hcov₃ _ _ fun n => ?_)
  simpa only [Functor.mapIso_hom] using congrArg Iso.hom
    (transitionOn_trans_member B S hS W w ρ D N ε ψ hψ vi vj vk vij vjk vik hij₀ hij₁
      hjk₀ hjk₁ hik₀ hik₁ (c₃ n) (ι₃ n) (κ₃ n) (lam₃ n) (a₃ n) (b₃ n) (d₃ n) (ha₃ n) (hb₃ n)
      (hd₃ n))

include hψ in
/-- **The descent datum `(N, ψ)` relative to the one-member family `{ρ}`.** -/
def oneMemberDatum (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    (hN : N.IsQuasicoherentOnSite) :
    DescentDatum B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) where
  F _ := N
  quasicoherent _ := hN
  transition _ _ := ψ
  cocycle := transitionOn_trans B S hS W w ρ D N ε ψ hψ hw

/-- Every component module of `oneMemberDatum` is `N`. -/
@[simp]
theorem oneMemberDatum_F (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    (hN : N.IsQuasicoherentOnSite) (i : PUnit.{v + 1}) :
    (oneMemberDatum B S hS W w ρ D N ε ψ hψ hw hN).F i = N :=
  rfl

/-- Every pairwise isomorphism of `oneMemberDatum` is `ψ`. -/
@[simp]
theorem oneMemberDatum_transition (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    (hN : N.IsQuasicoherentOnSite) (i j : PUnit.{v + 1}) :
    (oneMemberDatum B S hS W w ρ D N ε ψ hψ hw hN).transition i j = ψ :=
  rfl

include hψ in
/-- **The quasi-coherent `𝒪_X`-module and the identification of `N` with its inverse image.**
The descent datum `(N, ψ)` relative to the one-member étale covering `{ρ}` is effective by
`…isEffective_of_isEtaleCovering`; its component isomorphism is `ν` and the compatibility of
that isomorphism with the pairwise isomorphisms is the equation carried here. -/
theorem exists_module_and_nu (hw : IsFpqcCovering B S hS fun i => (w i).hom)
    (hN : N.IsQuasicoherentOnSite)
    (hρ : IsEtaleCovering B S hS (fun _ : PUnit.{v + 1} => R.1) (fun _ => ρ.hom)) :
    ∃ M : Modules.{u, u} B S hS X.1 X.2, M.IsQuasicoherentOnSite ∧
      ∃ (ν : N ≅ (modulePullback B S hS ρ).obj M),
      (modulePullback B S hS
            (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)).mapIso ν ≪≫
          canonicalComparison
            (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)
            (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) ρ ρ
            (pair_condition B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) M =
        ψ ≪≫ (modulePullback B S hS
          (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)).mapIso ν := by
  obtain ⟨M, hM, ⟨e⟩⟩ := isEffective_of_isEtaleCovering B S hS (fun _ : PUnit.{v + 1} => R)
    (fun _ => ρ) (fun _ => hρ.etale ⟨⟩) hρ
    (oneMemberDatum B S hS W w ρ D N ε ψ hψ hw hN)
  have hnat := appIso_naturality B S hS e ⟨⟩ ⟨⟩
  rw [canonicalDescentDatum_transition, oneMemberDatum_transition] at hnat
  exact ⟨M, hM, DescentDatum.appIso B S hS e ⟨⟩, hnat⟩

variable (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
  (ν : N ≅ (modulePullback B S hS ρ).obj M)
  (hν : (modulePullback B S hS
          (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)).mapIso ν ≪≫
      canonicalComparison
        (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)
        (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) ρ ρ
        (pair_condition B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) M =
    ψ ≪≫ (modulePullback B S hS
      (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)).mapIso ν)

include hψ hν in
/-- **The reading of `D` on a test space, conjugated by `ν`, is the canonical comparison of
Stacks 04W5 of `M`.**  The reading is the reading of `ψ` there, by the uniform reading, and `ψ`
is the canonical comparison conjugated by `ν`; the two comparisons of Stacks 03LU for the
morphism to `R ×_X R` cancel. -/
theorem readN_trans_mapIso_nu {T : AlgebraicSpaces B S hS} (i j : I) (α : T ⟶ W i)
    (β : T ⟶ W j) (xx yy : T ⟶ R) (hax : α ≫ w i = xx) (hby : β ≫ w j = yy)
    (hxy : xx ≫ ρ = yy ≫ ρ) (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β) :
    (modulePullback B S hS xx).mapIso ν ≪≫ canonicalComparison xx yy ρ ρ hxy M =
      readN B S hS W w ρ D N ε i j α β xx yy hax hby v hv₁ hv₂ ≪≫
        (modulePullback B S hS yy).mapIso ν := by
  obtain ⟨u, hu₁, hu₂⟩ :=
    exists_pairLeg B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩ xx yy hxy
  have key := congrArg (fun t => (modulePullback B S hS u).mapIso t) hν
  simp only [Functor.mapIso_trans] at key
  rw [modulePullback_mapIso_mapIso B S hS u
      (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) xx hu₁ ν,
    modulePullback_mapIso_canonicalComparison B S hS u
      (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)
      (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) ρ ρ
      (pair_condition B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) xx yy hu₁ hu₂
      hxy M,
    modulePullback_mapIso_mapIso B S hS u
      (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) yy hu₂ ν,
    hψ T u i j α β xx yy hu₁ hu₂ hax hby v hv₁ hv₂, unreadIso] at key
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc] at key
  exact Iso.eq_of_trans_eq_trans _ _ key

/-- **The identification of the component modules of `D` with the inverse images of `M`**: the
isomorphism `ε i` with `N` replaced by `ρ^*M` through `ν`, and the iterated inverse image along
`w i` and `ρ` identified with the inverse image along the composite.

Its target is the inverse image of `M` along the structure morphism and not the component module
of the canonical descent datum of Stacks 04W5: the two differ by one delta-iota step, and taken
inside the `CategoryTheory.Iso.trans` of the compatibility below that step stops every rewrite,
while taken in the argument of the effectivity criterion it is free. -/
def compModuleIso (i : I) :
    D.F i ≅ (modulePullback B S hS (w i ≫ ρ)).obj M :=
  ε i ≪≫ (modulePullback B S hS (w i)).mapIso ν ≪≫
    (pullbackComparison B S hS (w i) ρ (w i ≫ ρ) rfl M).symm

/-- `compModuleIso i` is the composite of `ε i`, the inverse image of `ν` along `w i`, and the
inverse of the comparison of the inverse images along `w i`, `ρ` and `w i ≫ ρ`. -/
@[simp]
theorem compModuleIso_eq (i : I) :
    compModuleIso B S hS W w ρ D N ε M ν i =
      ε i ≪≫ (modulePullback B S hS (w i)).mapIso ν ≪≫
        (pullbackComparison B S hS (w i) ρ (w i ≫ ρ) rfl M).symm :=
  rfl

include hψ hν in
/-- **The identifications of the component modules intertwine the pairwise isomorphisms of `D`
with the canonical comparisons of Stacks 04W5 of `M`**, read on a test space mapping to two
members of the covering.

This is `…readN_trans_mapIso_nu` with the comparisons of Stacks 03LU absorbed: on both sides the
canonical comparison of `M` is taken at the leg `(α ≫ w i) ≫ ρ`, which
`…canonicalComparison_eq_pullbackComparison` writes as the two comparisons for that leg. -/
theorem mapIso_compModuleIso_canonicalComparison {T : AlgebraicSpaces B S hS} (i j : I)
    (α : T ⟶ W i) (β : T ⟶ W j) (h : α ≫ (w i ≫ ρ) = β ≫ (w j ≫ ρ))
    (v : T ⟶ pair B S hS W (fun t => w t ≫ ρ) i j)
    (hv₁ : v ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j = α)
    (hv₂ : v ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j = β) :
    (modulePullback B S hS α).mapIso (compModuleIso B S hS W w ρ D N ε M ν i) ≪≫
        canonicalComparison α β (w i ≫ ρ) (w j ≫ ρ) h M =
      transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition i j v α β hv₁ hv₂ ≪≫
        (modulePullback B S hS β).mapIso (compModuleIso B S hS W w ρ D N ε M ν j) := by
  have hxy : (α ≫ w i) ≫ ρ = (β ≫ w j) ≫ ρ := by
    rw [Category.assoc, Category.assoc]
    exact h
  have hreadN : transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition i j v α β hv₁ hv₂ ≪≫
        (modulePullback B S hS β).mapIso (ε j) ≪≫
        (pullbackComparison B S hS β (w j) (β ≫ w j) rfl N).symm =
      (modulePullback B S hS α).mapIso (ε i) ≪≫
        (pullbackComparison B S hS α (w i) (α ≫ w i) rfl N).symm ≪≫
        readN B S hS W w ρ D N ε i j α β (α ≫ w i) (β ≫ w j) rfl rfl v hv₁ hv₂ := by
    rw [readN]
    simp only [Functor.mapIso_symm, Iso.self_symm_id_assoc,
      Iso.symm_self_id_assoc]
  simp only [compModuleIso_eq, Functor.mapIso_trans, Functor.mapIso_symm]
  rw [modulePullback_mapIso_mapIso B S hS α (w i) (α ≫ w i) rfl ν,
    modulePullback_mapIso_mapIso B S hS β (w j) (β ≫ w j) rfl ν,
    modulePullback_mapIso_pullbackComparison B S hS α (w i) ρ (w i ≫ ρ) rfl (α ≫ w i) rfl
      ((α ≫ w i) ≫ ρ) rfl (by rw [← Category.assoc]) M,
    modulePullback_mapIso_pullbackComparison B S hS β (w j) ρ (w j ≫ ρ) rfl (β ≫ w j) rfl
      ((α ≫ w i) ≫ ρ) hxy.symm (by rw [← Category.assoc]; exact hxy.symm) M,
    canonicalComparison_eq_pullbackComparison B S hS α β (w i ≫ ρ) (w j ≫ ρ) h
      ((α ≫ w i) ≫ ρ) (by rw [← Category.assoc])
      (by rw [← Category.assoc]; exact hxy.symm) M]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc,
    Iso.self_symm_id_assoc]
  rw [Iso.subst_trans₃ hreadN]
  simp only [Iso.trans_assoc]
  rw [Iso.subst_trans₂ (readN_trans_mapIso_nu B S hS W w ρ D N ε ψ hψ
    M ν hν i j α β (α ≫ w i) (β ≫ w j) rfl rfl hxy v hv₁ hv₂).symm]
  simp only [Iso.trans_assoc]
  rw [canonicalComparison_eq_pullbackComparison B S hS (α ≫ w i) (β ≫ w j) ρ ρ hxy
    ((α ≫ w i) ≫ ρ) rfl hxy.symm M]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

include hψ hν in
/-- **The compatibility of the identifications with the pairwise isomorphisms, after pullback
along one member of a covering of the pairwise fibre product.**

The reading of `D.transition i j` on a test space is `…transitionOn` at the morphism from that
space into the pairwise fibre product; at the fibre product itself that morphism is the identity,
which is why the compatibility is proved here, at a morphism `r` that is a member of a covering,
and carried back by the faithfulness half of Stacks 04W8. -/
theorem mapIso_compModuleIso_pair_member (i j : I) {P : AlgebraicSpaces B S hS}
    (r : P ⟶ pair B S hS W (fun t => w t ≫ ρ) i j) :
    (modulePullback B S hS r).mapIso
        ((modulePullback B S hS (pairFst B S hS W (fun t => w t ≫ ρ) i j)).mapIso
            (compModuleIso B S hS W w ρ D N ε M ν i) ≪≫
          canonicalComparison (pairFst B S hS W (fun t => w t ≫ ρ) i j)
            (pairSnd B S hS W (fun t => w t ≫ ρ) i j) (w i ≫ ρ) (w j ≫ ρ)
            (pair_condition B S hS W (fun t => w t ≫ ρ) i j) M) =
      (modulePullback B S hS r).mapIso
        (D.transition i j ≪≫ (modulePullback B S hS
          (pairSnd B S hS W (fun t => w t ≫ ρ) i j)).mapIso
            (compModuleIso B S hS W w ρ D N ε M ν j)) := by
  have h' : (r ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j) ≫ (w i ≫ ρ) =
      (r ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j) ≫ (w j ≫ ρ) := by
    rw [Category.assoc, pair_condition B S hS W (fun t => w t ≫ ρ) i j, ← Category.assoc]
  simp only [Functor.mapIso_trans]
  rw [modulePullback_mapIso_mapIso B S hS r (pairFst B S hS W (fun t => w t ≫ ρ) i j)
      (r ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j) rfl
      (compModuleIso B S hS W w ρ D N ε M ν i),
    modulePullback_mapIso_canonicalComparison B S hS r
      (pairFst B S hS W (fun t => w t ≫ ρ) i j) (pairSnd B S hS W (fun t => w t ≫ ρ) i j)
      (w i ≫ ρ) (w j ≫ ρ) (pair_condition B S hS W (fun t => w t ≫ ρ) i j)
      (r ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j)
      (r ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j) rfl rfl h' M,
    modulePullback_mapIso_transition B S hS D i j r
      (r ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j)
      (r ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j) rfl rfl,
    modulePullback_mapIso_mapIso B S hS r (pairSnd B S hS W (fun t => w t ≫ ρ) i j)
      (r ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j) rfl
      (compModuleIso B S hS W w ρ D N ε M ν j)]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [Iso.subst_trans₂ (mapIso_compModuleIso_canonicalComparison B S hS W w ρ D N ε ψ hψ M
    ν hν i j (r ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j)
    (r ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j) h' r rfl rfl)]
  simp only [Iso.trans_assoc]

include hψ hν in
/-- **The identifications of the component modules intertwine the pairwise isomorphisms of `D`
with the canonical comparisons of Stacks 04W5 of `M`.**  This is the compatibility the
effectivity of `D` is assembled from, and it is proved after pullback along a covering of the
pairwise fibre product — where the reading of `D.transition i j` is available — by
`…mapIso_compModuleIso_pair_member`, the faithfulness half of Stacks 04W8 carrying it back. -/
theorem mapIso_compModuleIso_pair (hw : IsFpqcCovering B S hS fun i => (w i).hom) (i j : I) :
    (modulePullback B S hS (pairFst B S hS W (fun t => w t ≫ ρ) i j)).mapIso
          (compModuleIso B S hS W w ρ D N ε M ν i) ≪≫
        canonicalComparison (pairFst B S hS W (fun t => w t ≫ ρ) i j)
          (pairSnd B S hS W (fun t => w t ≫ ρ) i j) (w i ≫ ρ) (w j ≫ ρ)
          (pair_condition B S hS W (fun t => w t ≫ ρ) i j) M =
      D.transition i j ≪≫ (modulePullback B S hS
        (pairSnd B S hS W (fun t => w t ≫ ρ) i j)).mapIso
          (compModuleIso B S hS W w ρ D N ε M ν j) := by
  obtain ⟨Z', c', a', hcov', ha'⟩ := exists_isFpqcCovering_leg B S hS W w hw
    (pairFst B S hS W (fun t => w t ≫ ρ) i j ≫ w i)
  refine Iso.ext (modulePullback_map_injective_of_isFpqcCovering B S hS
    (reprFpqcHomInjective B S hS) Z' c' hcov' _ _ fun n => ?_)
  simpa only [Functor.mapIso_hom, Iso.trans_hom] using congrArg Iso.hom
    (mapIso_compModuleIso_pair_member B S hS W w ρ D N ε ψ hψ M ν hν i j (c' n))

include hcan in
/-- **Transitivity of effective descent for quasi-coherent modules.**  A descent datum relative
to a family `(w i ≫ ρ : W i ⟶ X)` whose base change to `R` is the canonical descent datum of an
`𝒪_R`-module `N` is itself effective, `ρ` being a one-member surjective étale covering of `X`
and `(w i)` an fpqc covering of `R`.

The module is the one the descent datum `(N, ψ)` relative to `{ρ}` produces, the identification
of the component modules of `D` with its inverse images is `…compModuleIso` and their
compatibility with the pairwise isomorphisms is `…mapIso_compModuleIso_pair`; the three are
assembled by `…DescentDatum.isoMkOfTransitionEq`, which takes the compatibility at *named*
pairwise isomorphisms and as an equality of isomorphisms, so that the component modules of the
canonical descent datum are never identified with the inverse images underneath a composite. -/
theorem isEffective_of_isEffective_baseChangeDatum
    (hw : IsFpqcCovering B S hS fun i => (w i).hom) (hN : N.IsQuasicoherentOnSite)
    (hρ : IsEtaleCovering B S hS (fun _ : PUnit.{v + 1} => R.1) (fun _ => ρ.hom)) :
    IsEffective B S hS W (fun t => w t ≫ ρ) D := by
  obtain ⟨ψ, hψ⟩ := exists_mapIso_eq_unreadIso_readN B S hS W w ρ D N ε hcan
    (pairFst B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)
    (pairSnd B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩) hw hN
    (pair_condition B S hS (fun _ : PUnit.{v + 1} => R) (fun _ => ρ) ⟨⟩ ⟨⟩)
  obtain ⟨M, hM, ν, hν⟩ := exists_module_and_nu B S hS W w ρ D N ε ψ hψ hw hN hρ
  exact ⟨M, hM, ⟨DescentDatum.isoMkOfTransitionEq B S hS
    (fun i => compModuleIso B S hS W w ρ D N ε M ν i) D.transition
    (fun i j => canonicalComparison (pairFst B S hS W (fun t => w t ≫ ρ) i j)
      (pairSnd B S hS W (fun t => w t ≫ ρ) i j) (w i ≫ ρ) (w j ≫ ρ)
      (pair_condition B S hS W (fun t => w t ≫ ρ) i j) M)
    (fun i j => rfl)
    (canonicalDescentDatum_transition B S hS W (fun t => w t ≫ ρ) M hM)
    (mapIso_compModuleIso_pair B S hS W w ρ D N ε ψ hψ M ν hν hw)⟩⟩

end Transitivity

section Clause

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- **The transitivity statement in the shape the reduction of the effectivity clause of
Stacks 04W8 consumes**: for a one-member surjective étale covering `ρ` of `X` by a representable
algebraic space and an fpqc covering `(wj i)` of that space, every descent datum relative to the
composites is effective.

The base change of the datum to the representable space is effective by
`…isEffective_of_isFpqcCovering_representedBase`, which is the effectivity clause of Stacks 04W8
over a representable base; that is the hypothesis `…isEffective_of_isEffective_baseChangeDatum`
takes, its components `ε` and their compatibility being read off the isomorphism of descent data
by `…DescentDatum.appIso` and `…appIso_naturality`. -/
theorem isEffective_of_isFpqcCovering_comp {U : BigFppfOver B S hS}
    (ρ : representedAlgebraicSpace B S hS U ⟶ X)
    (hρ : IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj U) (fun _ => ρ.hom))
    (Wj : I → AlgebraicSpaces B S hS) (wj : ∀ i, Wj i ⟶ representedAlgebraicSpace B S hS U)
    (hcov : IsFpqcCovering B S hS fun i => (wj i).hom)
    (E : DescentDatum B S hS Wj (fun i => wj i ≫ ρ)) :
    IsEffective B S hS Wj (fun i => wj i ≫ ρ) E := by
  obtain ⟨N, hN, ⟨e⟩⟩ := isEffective_of_isFpqcCovering_representedBase B S hS Wj wj hcov
    (baseChangeDatum B S hS Wj wj ρ E)
  have hcan : ∀ i j, (modulePullback B S hS (pairFst B S hS Wj wj i j)).mapIso
          (DescentDatum.appIso B S hS e i) ≪≫
        canonicalComparison (pairFst B S hS Wj wj i j) (pairSnd B S hS Wj wj i j) (wj i) (wj j)
          (pair_condition B S hS Wj wj i j) N =
      baseChangeTransition B S hS Wj wj ρ E i j ≪≫
        (modulePullback B S hS (pairSnd B S hS Wj wj i j)).mapIso
          (DescentDatum.appIso B S hS e j) := by
    intro i j
    have h := appIso_naturality B S hS e i j
    rw [canonicalDescentDatum_transition, baseChangeDatum_transition] at h
    exact h
  have hρ' : IsEtaleCovering B S hS
      (fun _ : PUnit.{v + 1} => (representedAlgebraicSpace B S hS U).1) (fun _ => ρ.hom) :=
    IsEtaleCovering.reindex B S hS hρ (σ := fun _ : PUnit.{v + 1} => (() : Unit))
      fun _ => ⟨PUnit.unit, rfl⟩
  exact isEffective_of_isEffective_baseChangeDatum B S hS Wj wj ρ E N
    (DescentDatum.appIso B S hS e) hcan hcov hN hρ'

/-- **Every descent datum for quasi-coherent modules relative to an fpqc covering of an
algebraic space is effective** — the effectivity clause of Stacks 04W8, with no hypothesis
beyond the covering.

A scheme atlas of the target is a one-member surjective étale covering by a representable
algebraic space, so `…isEffective_of_isFpqcCovering_of_isEffective_comp` reduces the statement to
the transitivity of effective descent along it, which is
`…isEffective_of_isFpqcCovering_comp`. -/
theorem forall_isEffective_of_isFpqcCovering (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i => (f i).hom)
    (D : DescentDatum B S hS Xi f) : IsEffective B S hS Xi f D := by
  classical
  obtain ⟨U, a₀, hsurj, hetale⟩ := X.property.exists_atlas
  have hEtale : IsEtaleCovering B S hS (fun _ : Unit => yoneda.obj U) (fun _ => a₀) := by
    refine ⟨X.property, fun _ => isAlgebraicSpace_yoneda B S hS U,
      fun _ => (isEtale_iff_presheaf_of_yoneda B S hS a₀).2 hetale, ?_⟩
    rw [Set.iUnion_const, Set.range_eq_univ]
    exact (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U a₀).1 hsurj
  exact isEffective_of_isFpqcCovering_of_isEffective_comp B S hS f
    (ObjectProperty.homMk a₀ : representedAlgebraicSpace B S hS U ⟶ X) hEtale hf
    (fun Wj wj hc E => isEffective_of_isFpqcCovering_comp B S hS
      (ObjectProperty.homMk a₀ : representedAlgebraicSpace B S hS U ⟶ X) hEtale Wj wj hc E) D

/-- **Stacks 04W8: for an fpqc covering `(f i : X i ⟶ X)` of algebraic spaces, the canonical
descent functor from the quasi-coherent `𝒪_X`-modules to the descent data relative to the
covering is an equivalence.**

This is the tag, both of whose clauses the equivalence carries: *the functor is fully faithful*,
and *every descent datum on quasi-coherent sheaves for the family is effective* — which is
essential surjectivity by
`…essSurj_canonicalDescentFunctor'_iff_forall_isEffective`.  The full-faithfulness clause is
`…nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering` and the effectivity clause is
`…forall_isEffective_of_isFpqcCovering`; both are proved, and nothing is assumed beyond the
covering. -/
@[stacks 04W8]
theorem isEquivalence_canonicalDescentFunctor'_of_isFpqcCovering
    (Xi : I → AlgebraicSpaces B S hS) (f : ∀ i, Xi i ⟶ X)
    (hf : IsFpqcCovering B S hS fun i => (f i).hom) :
    (canonicalDescentFunctor' B S hS Xi f).IsEquivalence :=
  isEquivalence_canonicalDescentFunctor'_of_forall_isEffective B S hS Xi f hf
    (forall_isEffective_of_isFpqcCovering B S hS Xi f hf)

end Clause

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
