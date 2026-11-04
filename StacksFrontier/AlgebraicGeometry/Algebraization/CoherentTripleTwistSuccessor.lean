module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionMultiplication

/-!
# The successor comparison of the twists, and multiplication by a section through it

The induction step of [Stacks, Tag 0F27] compares the Euler characteristics of consecutive
twists, so every one of its constructions has to be moved one degree along. At the level of
modules that move is the identification

`(F ⊗ L^{⊗ n}) ⊗ L ≅ F ⊗ L^{⊗ (n + 1)}`,

the associativity constraint followed by the successor comparison of the tensor powers of
[Stacks, Tag 01CU]. This file builds it and proves the one compatibility its consumers need:
multiplication of the `n`-th twist by a global section of `L`, which
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` uses as the member of a morphism of
coherent triples, is multiplication of the whole module `F ⊗ L^{⊗ n}` by that section, read
through this identification.

## Main definitions

* `Stacks.Algebraization.tensorPowSchemeSuccIso`: the successor comparison
  `L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}` of [Stacks, Tag 01CU], at the scheme spelling.
* `Stacks.Algebraization.tensorModulesSuccIso`: **the successor identification
  `(F ⊗ L^{⊗ n}) ⊗ L ≅ F ⊗ L^{⊗ (n + 1)}`.**

## Main results

* `Stacks.Algebraization.whiskerLeft_mulSectionPowScheme`: **tensoring `F` with multiplication
  by a global section of `L` on the tensor powers is multiplication of `F ⊗ L^{⊗ n}` by that
  section, followed by the successor identification.** The left-hand side is the
  punctured-spectrum member of `Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`; the
  right-hand side is `(ρ_ _).inv ≫ _ ◁ σ`, which is the body of
  `Stacks.TensorSectionNonvanishing.mulRight`, whose monicity for a section nonvanishing near
  the associated points is `Stacks.SectionProduct.mono_mulRight_of_associatedPoints`.
* `Stacks.Algebraization.pullbackTensorPowSchemeIso_tensorPowSchemeSuccIso` and
  `Stacks.Algebraization.tensorPowSchemeCongr_tensorPowSchemeSuccIso`: the two comparisons of
  the integral tensor powers that `Stacks.Algebraization.IsInvertibleTriple.alphaPow` is built
  from each carry the successor comparison of [Stacks, Tag 01CU] to the successor comparison.
* `Stacks.Algebraization.alphaPow_tensorPowSchemeSuccIso`: **the identification of an invertible
  coherent triple is compatible with the successor comparison of the tensor powers**, which is
  the square making that comparison an isomorphism of coherent triples rather than of each
  member separately.
* `Stacks.Algebraization.pullbackTensorModulesIso_associator` and
  `Stacks.Algebraization.pullbackTensorModulesIso_whiskerLeft`: **[Stacks, Tag 01CD] is
  compatible with the associativity constraint of [Stacks, Tag 01CA] and natural in the second
  variable**, both at the scheme spelling the coherent triples use.
* `Stacks.Algebraization.pullbackTensorModulesIso_assoc_whiskerLeft`: their composite — **the
  inverse-image comparison carries the shape of `Stacks.Algebraization.tensorModulesSuccIso`,
  an associativity constraint followed by a left whiskering, to the same shape for the inverse
  images.**
* `Stacks.Algebraization.alpha_twistZ_eq_tensorHom` and
  `Stacks.Algebraization.alpha_tensorInvertible_eq_tensorHom`: the identifications of a twist and
  of a tensor product with an invertible triple, with the tensor product of the two
  identifications written in the monoidal `⊗ₘ` form rather than in the bifunctor form the `alpha`
  field is built with.

## Implementation notes

The successor square of `Stacks.Algebraization.IsInvertibleTriple.alphaPow` is assembled by
`Stacks.Algebraization.comp_eq_of_three_squares` out of the three squares of its three factors,
exactly as `Stacks.Algebraization.alphaPow_mulSectionPowScheme` is. The assembly is made in
`exact` position for the reason recorded below: the two routes around the square of a coherent
triple carry syntactically different `Category` instances on the same category, so `rw` refuses
to match a composite that mixes them even when the goal displays as the pattern. For the same
reason the three generic monoidal rearrangements below are applied with all of their arguments
given explicitly rather than left to `rw` to unify, and the one step that does move an inverse
across the inverse-image comparison is an `exact` of a `congrArg`.

The monoidal structure used is `Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor
product is `Stacks.RelativeVeryAmple.tensorModules` and whose unit is
`Stacks.Ample.unitModule` -- both on the nose, so the statements below are statements about the
tensor product sheaf of [Stacks, Tag 01CA] with no transport. It is installed as a `local
instance` at the `X.Modules` spelling, as in
`StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionPairing`: the structure is stated for
`SheafOfModules (structureSheaf X.presheaf _)`, which instance search does not recover from
`X.Modules`.

`Stacks.SheafOfModules.TensorPower.mulSectionPow`, which
`Stacks.Algebraization.mulSectionPowScheme` is, is *defined* as
`(ρ_ _).inv ≫ (_ ◁ σ) ≫ (tensorPowerSuccIso _).hom`; but it is defined against the structure as
named there, not against the local instance here, so the two spellings carry different
`Category` instances on the same category and no `simp` lemma about `≫` or `◁` fires across
them. The unfolding is therefore made by a `have … := rfl` *stated at the local instance*, the
idiom of `Stacks.Algebraization.CoherentTriple.puncturedClosedFibre_of_eq`; after it the whole
chase happens in one spelling. For the same reason the final step is an `exact` of a `congrArg`
rather than a `rw`: the section `σ` in the goal and the section in
`CategoryTheory.MonoidalCategory.associator_naturality_right` are typed through different
`Quiver` instances, which `rw` cannot match and `exact` accepts.

**What the associator coherence is for, and what the Lean proof had to route around.** The
successor identification of the twists is an isomorphism *of coherent triples*
`(T ⊗ L^{⊗ n}) ⊗ L ≅ T ⊗ L^{⊗ (n+1)}` only once its compatibility square commutes, and that
square is `Stacks.Algebraization.alphaPow_tensorPowSchemeSuccIso` pasted between two copies —
one at each of the two morphisms of the square of a coherent triple — of
`Stacks.Algebraization.pullbackTensorModulesIso_assoc_whiskerLeft`, with the pure monoidal
algebra supplied by `Stacks.Algebraization.assoc_whiskerLeft_tensorHom_of_succ_square`,
`Stacks.Algebraization.whiskerRight_tensorHom_comp_whiskerRight` and
`Stacks.Algebraization.comp_eq_of_outer_squares`. The two sides of the pasting reach the
monoidal structure on the modules of the punctured closed fibre by different routes —
`Stacks.Algebraization.CoherentTriple.alpha` spells that scheme as the source of
`AlgebraicGeometry.morphismRestrict`, while the statements written here spell it
`(Stacks.Algebraization.puncturedClosedFibre A f).toScheme` — so the goal and the lemma carry two
syntactically different instance terms for `Stacks.SheafOfModules.Strict.monoidalCategory` on one
category, and *comparing* them for defeq makes the elaborator unfold that structure, which is
`CategoryTheory.SymmetricCategory.ofFaithful` of an induced monoidal functor, descend into the
limits of the module pullback, and exhaust the heartbeat budget. Supplying all seventeen
morphisms of `comp_eq_of_outer_squares` explicitly does not avoid this, nor does pinning the
monoidal instance by `@`-application, nor inlining the square so the instances are read off the
goal rather than off a `have`, nor removing `Stacks.Algebraization.CoherentTriple.twistZ` from
the statement: every one of those still states an expected type for the assembly and then checks
the assembled term against it, and that check is exactly the expensive comparison.

The way out is to never write down that expected type at all.
`Stacks.Algebraization.alpha_twistZ_eq_tensorHom`, `alpha_twistZ_tensorModulesSuccIso_hs`,
`_hmid`, `_hw` and
`alpha_twistZ_tensorModulesSuccIso_aux` below are each stated with no ascribed type — the
`:=` of a `def`, not the `: … :=` of a `theorem` — so each is nothing but the natural output type
of the one application it performs, propagated from the one before it with no independent
re-elaboration to compare it against. The instance terms are never *decided* equal because they
are never compared in the first place: the only term that ever carries the `twistZ`-unfolded
statement is the public `Stacks.Algebraization.alpha_twistZ_tensorModulesSuccIso` itself, whose
single `exact alpha_twistZ_tensorModulesSuccIso_aux T hL n` gets a heartbeat budget of its own,
separate from the one spent assembling `aux`. Splitting the construction into several
declarations is what gives each stage its own budget; dropping the ascribed types on the
intermediate stages is what keeps any one of those budgets from being spent on a defeq check that
the final `exact` already has to do once, at the top.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

/-- The tensor product sheaf of [Stacks, Tag 01CA] as a monoidal structure on the
`𝒪_X`-modules of a scheme, with the structure sheaf as its unit, in the spelling in which the
tensor product is `Stacks.RelativeVeryAmple.tensorModules` on the nose. -/
local instance strictModulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.Strict.monoidalCategory X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)

/-! ### The successor comparison of the tensor powers -/

/-- **The successor comparison of the integer tensor powers of an invertible `𝒪_X`-module**,
`L^{⊗ n} ⊗ L ≅ L^{⊗ (n + 1)}`, at the scheme spelling of [Stacks, Tag 01CU] used by the twists
of a coherent triple. -/
public def tensorPowSchemeSuccIso (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) :
    tensorModules X (tensorPowScheme X L n) L ≅ tensorPowScheme X L (n + 1) :=
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n

/-! ### The successor identification of the twists -/

/-- **The successor identification of the twists of a module**,
`(F ⊗ L^{⊗ n}) ⊗ L ≅ F ⊗ L^{⊗ (n + 1)}`: the associativity constraint of the tensor product
sheaf followed by the successor comparison of the tensor powers, tensored into `F`. -/
public def tensorModulesSuccIso (X : Scheme.{u}) (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) :
    tensorModules X (tensorModules X F (tensorPowScheme X L n)) L ≅
      tensorModules X F (tensorPowScheme X L (n + 1)) :=
  α_ F (tensorPowScheme X L n) L ≪≫ whiskerLeftIso F (tensorPowSchemeSuccIso X L n)

/-! ### Multiplication by a section through the successor identification -/

/-- **Tensoring `F` with multiplication by a global section `σ` of `L` on the tensor powers is
multiplication of `F ⊗ L^{⊗ n}` by `σ`, read through the successor identification.**

The left-hand side is the punctured-spectrum member of
`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ`, the left-hand map of the short exact
sequence of the induction step of [Stacks, Tag 0F27]; the right-hand side is the body of
`Stacks.TensorSectionNonvanishing.mulRight`, multiplication of a single module by a global
section. This is the identification under which the monicity of multiplication by a section
nonvanishing near the associated points,
`Stacks.SectionProduct.mono_mulRight_of_associatedPoints`, applies to that map. -/
public theorem whiskerLeft_mulSectionPowScheme (X : Scheme.{u}) (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (σ : Stacks.Ample.unitModule X ⟶ L) (n : ℤ) :
    F ◁ mulSectionPowScheme X L σ n =
      ((ρ_ (tensorModules X F (tensorPowScheme X L n))).inv ≫
          tensorModules X F (tensorPowScheme X L n) ◁ σ) ≫
        (tensorModulesSuccIso X F L n).hom := by
  have hstruct : F ◁ (ρ_ (tensorPowScheme X L n)).inv =
      (ρ_ (F ⊗ tensorPowScheme X L n)).inv ≫
        (α_ F (tensorPowScheme X L n) (𝟙_ X.Modules)).hom := by
    monoidal
  have hms : mulSectionPowScheme X L σ n = (ρ_ (tensorPowScheme X L n)).inv ≫
      (tensorPowScheme X L n ◁ σ) ≫ (tensorPowSchemeSuccIso X L n).hom := rfl
  rw [hms]
  simp only [tensorModulesSuccIso, Iso.trans_hom, whiskerLeftIso_hom, whiskerLeft_comp,
    Category.assoc, hstruct]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun t => t ≫ F ◁ (tensorPowSchemeSuccIso X L n).hom)
    (associator_naturality_right F (tensorPowScheme X L n) σ).symm

/-! ### The successor comparison and the identification of an invertible triple -/

/-- **The inverse-image comparison of the integral tensor powers carries the successor comparison
to the successor comparison**, in every integer degree. This is
`Stacks.SheafOfModules.TensorPower.map_tensorPowerSuccIso_tensorPowerComparison` for the
tensorator of [Stacks, Tag 01CD]; the comparison used by the coherent triples *is* that
statement's `tensorPowerComparison`, by `rfl`. -/
@[reassoc]
public theorem pullbackTensorPowSchemeIso_tensorPowSchemeSuccIso {X S : Scheme.{u}} (g : X ⟶ S)
    (L : S.Modules) [Stacks.Ample.IsInvertibleModule S L]
    [Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback g).obj L)] (n : ℤ) :
    (Scheme.Modules.pullback g).map (tensorPowSchemeSuccIso S L n).hom ≫
        (pullbackTensorPowSchemeIso g L (n + 1)).hom =
      (pullbackTensorModulesIso g (tensorPowScheme S L n) L).hom ≫
        ((pullbackTensorPowSchemeIso g L n).hom ▷ (Scheme.Modules.pullback g).obj L) ≫
          (tensorPowSchemeSuccIso X ((Scheme.Modules.pullback g).obj L) n).hom := by
  let := isInvertible_of_isInvertibleModule S L
  let := isInvertible_of_isInvertibleModule X ((Scheme.Modules.pullback g).obj L)
  exact Stacks.SheafOfModules.TensorPower.map_tensorPowerSuccIso_tensorPowerComparison
    S.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf S)
    X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    (Scheme.Modules.pullback g) L
    (fun M N => pullbackTensorModulesIso g M N) (Scheme.Modules.pullbackUnitIso g) n

/-- **The comparison of the integral tensor powers of two isomorphic invertible modules carries
the successor comparison to the successor comparison**, in every integer degree. This is
`Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso_tensorPowerCongr` at the scheme
spelling. -/
@[reassoc]
public theorem tensorPowSchemeCongr_tensorPowSchemeSuccIso (X : Scheme.{u}) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (n : ℤ) :
    (tensorPowSchemeSuccIso X L n).hom ≫ (tensorPowSchemeCongr X e (n + 1)).hom =
      (tensorPowScheme X L n ◁ e.hom) ≫ ((tensorPowSchemeCongr X e n).hom ▷ L') ≫
        (tensorPowSchemeSuccIso X L' n).hom := by
  let := isInvertible_of_isInvertibleModule X L
  let := isInvertible_of_isInvertibleModule X L'
  exact Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso_tensorPowerCongr X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L L' e n

/-- The tensor product of two isomorphisms of `𝒪_X`-modules, read off the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, is their tensor product in the strict monoidal
structure. This is the bridge between the vocabulary the compatibility datum of a coherent triple
is written in and the vocabulary the tensor powers of [Stacks, Tag 01CU] are stated in.

Both sides are the sheafification of the objectwise tensor product of the two underlying
morphisms of presheaves: the left one by
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`, since
`Stacks.Algebraization.tensorModulesMap` is `CategoryTheory.Functor.uncurry` of that bifunctor at
a pair; the right one by `Stacks.SheafOfModules.tensorHom_eq_sheafify_map`. Routing it through
`Stacks.SheafOfModules.TensorPower.tensorSheafMapIso` instead does not work: that isomorphism is
`Functor.mapIso` of the sheafification at a `CategoryTheory.Iso.tensorIso`, while
`Stacks.RelativeVeryAmple.tensorModulesMapIso` is the composite of the bifunctor's two legs, and
the two are not definitionally equal. -/
public theorem tensorModulesMap_hom_eq_tensorHom (X : Scheme.{u}) {A A' B B' : X.Modules}
    (e : A ≅ A') (g : B ≅ B') :
    tensorModulesMap X e.hom g.hom = e.hom ⊗ₘ g.hom :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
      (R := ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩) e.hom g.hom).trans
    (Stacks.SheafOfModules.tensorHom_eq_sheafify_map X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) e.hom g.hom).symm

/-! ### Generic monoidal rearrangements -/

/-- A right whiskering, a left whiskering and two more right whiskerings in a row are the tensor
product of the composite of the three right-whiskered morphisms with the left-whiskered one. -/
public theorem whiskerRight_whiskerLeft_chain {M : Type*} [Category M] [MonoidalCategory M]
    {X₁ X₂ X₃ X₄ Y₁ Y₂ : M} (a : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (b : X₃ ⟶ X₄) (g : Y₁ ⟶ Y₂) :
    (a ▷ Y₁) ≫ (X₂ ◁ g) ≫ (c ▷ Y₂) ≫ (b ▷ Y₂) = (a ≫ c ≫ b) ⊗ₘ g :=
  calc (a ▷ Y₁) ≫ (X₂ ◁ g) ≫ (c ▷ Y₂) ≫ (b ▷ Y₂)
      = (a ⊗ₘ g) ≫ ((c ≫ b) ▷ Y₂) := by
        rw [MonoidalCategory.tensorHom_def, MonoidalCategory.comp_whiskerRight]
        simp only [Category.assoc]
    _ = (a ≫ c ≫ b) ⊗ₘ g := by
        rw [← MonoidalCategory.tensorHom_id (c ≫ b) Y₂,
          MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- Right whiskering an isomorphism and then its inverse cancels. -/
public theorem whiskerRight_inv_hom_comp {M : Type*} [Category M] [MonoidalCategory M]
    {X Y : M} (e : X ≅ Y) (Z : M) {W : M} (g : Y ⊗ Z ⟶ W) :
    (e.inv ▷ Z) ≫ (e.hom ▷ Z) ≫ g = g := by
  simp

/-- Left whiskering an isomorphism and then its inverse is the identity. -/
public theorem whiskerLeft_hom_inv_id {M : Type*} [Category M] [MonoidalCategory M] (X : M)
    {Y Z : M} (e : Y ≅ Z) : (X ◁ e.hom) ≫ (X ◁ e.inv) = 𝟙 (X ⊗ Y) := by
  simp

/-- Right whiskering an isomorphism's inverse and then the isomorphism cancels. -/
public theorem whiskerRight_hom_inv_comp {M : Type*} [Category M] [MonoidalCategory M]
    {X Y : M} (e : X ≅ Y) (Z : M) {W : M} (g : X ⊗ Z ⟶ W) :
    (e.hom ▷ Z) ≫ (e.inv ▷ Z) ≫ g = g := by
  simp

/-- One square, one cancelling pair and two factorisations paste to a commuting rectangle. This
is the rearrangement that reads the inverse-image comparison of a left whiskering through the
associator; it is stated for an abstract category because in `X.Modules` a rewrite along
`CategoryTheory.Category.assoc` does not fire, for the reason recorded in the implementation
notes of this file. -/
public theorem comp_eq_of_square_and_cancel {C : Type*} [Category C] {W Y Z T U U' P V : C}
    (m : W ⟶ Z) (a : W ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ T) (u : Y ⟶ U) (v : U ⟶ T) (t : U ⟶ U')
    (ti : U' ⟶ U) (p : W ⟶ P) (w : P ⟶ V) (al : V ⟶ U') (k : U' ⟶ T)
    (hm : m = a ≫ b) (hk : k = ti ≫ v) (h₁ : b ≫ c = u ≫ v)
    (h₂ : a ≫ u ≫ t = p ≫ w ≫ al) (ht : t ≫ ti = 𝟙 U) :
    m ≫ c = p ≫ w ≫ al ≫ k := by
  rw [hm, hk, Category.assoc, h₁, ← reassoc_of% h₂]
  simp [reassoc_of% ht]

/-- Right whiskering an isomorphism and then a tensor product of morphisms is the tensor product
conjugated by the isomorphism of the second factor, right-whiskered. This is the one remaining
tensor-product computation in the successor identification of the twists of a coherent triple:
the identification of a twist is itself a composite of two inverse-image comparisons with a
tensor product of morphisms between them. -/
public theorem whiskerRight_tensorHom_comp_whiskerRight {M : Type*} [Category M]
    [MonoidalCategory M] {Z₁ Z₂ Dk Dj Pk Pj : M} (l : Z₁ ⟶ Z₂) (p1 : Dk ≅ Pk) (j1 : Dj ≅ Pj)
    (q : Pk ⟶ Pj) (d : Dk ⟶ Dj) (hd : d = p1.hom ≫ q ≫ j1.inv) :
    (p1.hom ▷ Z₁) ≫ (q ⊗ₘ l) = (d ⊗ₘ l) ≫ (j1.hom ▷ Z₂) := by
  subst hd
  rw [← MonoidalCategory.tensorHom_id p1.hom Z₁, ← MonoidalCategory.tensorHom_id j1.hom Z₂,
    MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-- **The middle square of the successor identification of the twists**, as monoidal algebra.
Given that the successor comparison of the two tensor-power families is carried to itself by the
three identifications `An`, `ℓ`, `A1` of the factors — which is
`Stacks.Algebraization.alphaPow_tensorPowSchemeSuccIso` — the associativity constraint followed
by the left whiskering is carried by `a ⊗ₘ A1` to the same composite for the second family. -/
public theorem assoc_whiskerLeft_tensorHom_of_succ_square {M : Type*} [Category M]
    [MonoidalCategory M] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ Sk Sj Wk Wj : M} (a : X₁ ⟶ X₂) (An : Y₁ ⟶ Y₂)
    (l : Z₁ ⟶ Z₂) (A1 : Wk ⟶ Wj) (pk : Y₁ ⊗ Z₁ ⟶ Sk) (pj : Y₂ ⊗ Z₂ ⟶ Sj) (sk : Sk ⟶ Wk)
    (sj : Sj ⟶ Wj) (hs : pk ≫ sk ≫ A1 = (An ⊗ₘ l) ≫ pj ≫ sj) :
    (α_ X₁ Y₁ Z₁).hom ≫ (X₁ ◁ (pk ≫ sk)) ≫ (a ⊗ₘ A1) =
      ((a ⊗ₘ An) ⊗ₘ l) ≫ (α_ X₂ Y₂ Z₂).hom ≫ (X₂ ◁ (pj ≫ sj)) := by
  rw [reassoc_of% (MonoidalCategory.associator_naturality a An l)]
  congr 1
  rw [← MonoidalCategory.id_tensorHom X₁ (pk ≫ sk),
    ← MonoidalCategory.id_tensorHom X₂ (pj ≫ sj),
    MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id]
  simp only [Category.assoc, hs]

/-- **The inner half of the outer assembly**: the factorisation of one of the two inverse-image
comparisons, the middle square and the one remaining tensor-product computation paste to the
square with the second comparison still to come.

This half and `Stacks.Algebraization.comp_eq_of_outer_square` are the two stages of
`Stacks.Algebraization.comp_eq_of_outer_squares`, and they are stated separately because a
consumer that mixes two spellings of one scheme cannot afford the whole assembly in a single
declaration: the comparison that decides the two spellings' monoidal instances equal is paid
once per stage, and one heartbeat budget does not cover both. Stated for an abstract category,
for the reason recorded in the implementation notes of this file. -/
public theorem comp_eq_of_inner_squares {M : Type*} [Category M]
    {E Gk Ck Cj Dk Dj Vk Vj Uk Uj : M} (m : E ⟶ Gk) (p3 : Gk ⟶ Ck) (tA1 : Ck ⟶ Cj)
    (p4 : E ⟶ Dk) (tmid : Dk ⟶ Dj) (w : Dk ⟶ Vk) (ak : Vk ⟶ Uk) (uk : Uk ⟶ Ck)
    (w' : Dj ⟶ Vj) (aj : Vj ⟶ Uj) (uj : Uj ⟶ Cj) (tt : Vk ⟶ Vj)
    (hk : m ≫ p3 = p4 ≫ w ≫ ak ≫ uk)
    (hmid : ak ≫ uk ≫ tA1 = tt ≫ aj ≫ uj) (hw : w ≫ tt = tmid ≫ w') :
    m ≫ p3 ≫ tA1 = p4 ≫ tmid ≫ w' ≫ aj ≫ uj := by
  rw [reassoc_of% hk, hmid, reassoc_of% hw]

/-- **The outer half of the outer assembly**: the square produced by
`Stacks.Algebraization.comp_eq_of_inner_squares` and the factorisation of the second
inverse-image comparison paste to the whole rectangle. -/
public theorem comp_eq_of_outer_square {M : Type*} [Category M]
    {E Gk Ck Cj Gj Ej Dk Dj Vj Uj : M} (m : E ⟶ Gk) (p3 : Gk ⟶ Ck) (tA1 : Ck ⟶ Cj)
    (j3 : Gj ≅ Cj) (n' : Ej ⟶ Gj) (p4 : E ⟶ Dk) (tmid : Dk ⟶ Dj) (j4 : Ej ≅ Dj)
    (w' : Dj ⟶ Vj) (aj : Vj ⟶ Uj) (uj : Uj ⟶ Cj)
    (h : m ≫ p3 ≫ tA1 = p4 ≫ tmid ≫ w' ≫ aj ≫ uj)
    (hj : n' ≫ j3.hom = j4.hom ≫ w' ≫ aj ≫ uj) :
    m ≫ p3 ≫ tA1 ≫ j3.inv = (p4 ≫ tmid ≫ j4.inv) ≫ n' := by
  have hn : j4.inv ≫ n' = w' ≫ aj ≫ uj ≫ j3.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% hj]
    simp
  simp only [Category.assoc]
  rw [reassoc_of% h, ← hn]

/-- **The outer assembly of the successor identification of the twists.** The two
inverse-image comparisons of a twisted triple's identification are factored by
`Stacks.Algebraization.pullbackTensorModulesIso_assoc_whiskerLeft` on each side; `hmid` is the
middle square and `hw` the one remaining tensor-product computation. This is
`Stacks.Algebraization.comp_eq_of_inner_squares` followed by
`Stacks.Algebraization.comp_eq_of_outer_square`, in one declaration. -/
public theorem comp_eq_of_outer_squares {M : Type*} [Category M]
    {E Gk Ck Cj Gj Ej Dk Dj Vk Vj Uk Uj : M} (m : E ⟶ Gk) (p3 : Gk ⟶ Ck) (tA1 tA1' : Ck ⟶ Cj)
    (j3 : Gj ≅ Cj) (n' : Ej ⟶ Gj) (p4 : E ⟶ Dk) (tmid tmid' : Dk ⟶ Dj) (j4 : Ej ≅ Dj)
    (w : Dk ⟶ Vk) (ak : Vk ⟶ Uk) (uk : Uk ⟶ Ck) (w' : Dj ⟶ Vj) (aj : Vj ⟶ Uj) (uj : Uj ⟶ Cj)
    (tt : Vk ⟶ Vj) (hA : tA1 = tA1') (hM : tmid = tmid')
    (hk : m ≫ p3 = p4 ≫ w ≫ ak ≫ uk)
    (hj : n' ≫ j3.hom = j4.hom ≫ w' ≫ aj ≫ uj)
    (hmid : ak ≫ uk ≫ tA1' = tt ≫ aj ≫ uj) (hw : w ≫ tt = tmid' ≫ w') :
    m ≫ p3 ≫ tA1 ≫ j3.inv = (p4 ≫ tmid ≫ j4.inv) ≫ n' := by
  subst hA
  subst hM
  exact comp_eq_of_outer_square _ _ _ _ _ _ _ _ _ _ _
    (comp_eq_of_inner_squares _ _ _ _ _ _ _ _ _ _ _ _ hk hmid hw) hj

/-- **The identification of an invertible coherent triple is compatible with the successor
comparison of the tensor powers.** In degree `n` the identification `alphaPow n`, tensored with
the identification `λ` of the triple, is carried by the successor comparisons of the two members
to the identification in degree `n + 1`.

This is the square that makes the successor comparison of the twists an isomorphism *of coherent
triples* rather than of each member separately: it is exactly the compatibility condition the
`alpha` field of `Stacks.Algebraization.CoherentTriple` imposes. Its three factors are the three
factors of `alphaPow` — the inverse-image comparison of the tensor powers in each of the two
routes around the square of the triple, and the comparison of the tensor powers of the two
isomorphic modules in the middle — each of which carries the successor comparison by
`Stacks.Algebraization.pullbackTensorPowSchemeIso_tensorPowSchemeSuccIso` and
`Stacks.Algebraization.tensorPowSchemeCongr_tensorPowSchemeSuccIso`. -/
@[reassoc]
public theorem alphaPow_tensorPowSchemeSuccIso {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {L : CoherentTriple A f} (hL : IsInvertibleTriple L) (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map
        (tensorPowSchemeSuccIso (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n).hom ≫
        (hL.alphaPow (n + 1)).hom =
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) L.F).hom ≫
        ((hL.alphaPow n).hom ⊗ₘ L.alpha.hom) ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι
            (tensorPowScheme (closedFibre A f) L.F₀ n) L.F₀).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
            (tensorPowSchemeSuccIso (closedFibre A f) L.F₀ n).hom := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  have hA := pullbackTensorPowSchemeIso_tensorPowSchemeSuccIso
    (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)) L.F n
  have hC := tensorPowSchemeCongr_tensorPowSchemeSuccIso (puncturedClosedFibre A f).toScheme
    L.alpha n
  have hB := pullbackTensorPowSchemeIso_tensorPowSchemeSuccIso (puncturedClosedFibre A f).ι
    L.F₀ n
  have hchain := whiskerRight_whiskerLeft_chain
    (pullbackTensorPowSchemeIso (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)) L.F n).hom
    (tensorPowSchemeCongr (puncturedClosedFibre A f).toScheme L.alpha n).hom
    (pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ n).inv L.alpha.hom
  have h₂ : (((pullbackTensorPowSchemeIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A)) L.F n).hom ▷
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj L.F) ≫
        (tensorPowSchemeSuccIso (puncturedClosedFibre A f).toScheme
          ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).obj L.F) n).hom) ≫
      (tensorPowSchemeCongr (puncturedClosedFibre A f).toScheme L.alpha (n + 1)).hom =
      (((pullbackTensorPowSchemeIso (morphismRestrict (closedImmersion A f)
              (Stacks.Divisors.puncturedSpectrum A)) L.F n).hom ≫
            (tensorPowSchemeCongr (puncturedClosedFibre A f).toScheme L.alpha n).hom ≫
              (pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ n).inv) ⊗ₘ
          L.alpha.hom) ≫
        (((pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ n).hom ▷
            (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀) ≫
          (tensorPowSchemeSuccIso (puncturedClosedFibre A f).toScheme
            ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀) n).hom) := by
    rw [← hchain]
    simp only [Category.assoc]
    rw [whiskerRight_inv_hom_comp, hC]
  have hB'' : (tensorPowSchemeSuccIso (puncturedClosedFibre A f).toScheme
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀) n).hom ≫
      (pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ (n + 1)).inv =
      ((pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ n).inv ▷
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀) ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι
          (tensorPowScheme (closedFibre A f) L.F₀ n) L.F₀).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
            (tensorPowSchemeSuccIso (closedFibre A f) L.F₀ n).hom := by
    rw [← MonoidalCategory.whiskerRightIso_inv, Iso.eq_inv_comp,
      MonoidalCategory.whiskerRightIso_hom, ← Category.assoc, Iso.comp_inv_eq]
    exact ((Category.assoc _ _ _).trans
      ((congrArg (fun t => (pullbackTensorModulesIso (puncturedClosedFibre A f).ι
          (tensorPowScheme (closedFibre A f) L.F₀ n) L.F₀).inv ≫ t) hB).trans
        (Iso.inv_hom_id_assoc _ _))).symm
  have h₃ := (Category.assoc
      ((pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ n).hom ▷
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀)
      (tensorPowSchemeSuccIso (puncturedClosedFibre A f).toScheme
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀) n).hom
      (pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ (n + 1)).inv).trans
    ((congrArg (fun t => ((pullbackTensorPowSchemeIso (puncturedClosedFibre A f).ι L.F₀ n).hom ▷
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj L.F₀) ≫ t) hB'').trans
      (whiskerRight_hom_inv_comp _ _ _))
  unfold IsInvertibleTriple.alphaPow
  simp only [Iso.trans_hom, Iso.symm_hom]
  exact comp_eq_of_three_squares _ _ _ _ _ _ _ _ _ _ hA h₂ h₃


/-! ### The associator and the inverse-image comparison -/

/-- **[Stacks, Tag 01CD] is compatible with the associativity constraint of [Stacks, Tag 01CA]**,
at the scheme spelling: the comparison of the inverse image of a tensor product with the tensor
product of the inverse images carries the associator to the associator. This is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator`, whose monoidal structure
`Stacks.PullbackGradedAlgebra.monoidalCategory` is
`Stacks.SheafOfModules.Strict.monoidalCategory` by
`Stacks.PullbackGradedAlgebra.monoidalCategory_eq`. -/
@[reassoc]
public theorem pullbackTensorModulesIso_associator {X S : Scheme.{u}} (g : X ⟶ S)
    (A B D : S.Modules) :
    (Scheme.Modules.pullback g).map (α_ A B D).hom ≫
        (pullbackTensorModulesIso g A (tensorModules S B D)).hom ≫
          (((Scheme.Modules.pullback g).obj A : X.Modules) ◁
            (pullbackTensorModulesIso g B D).hom) =
      (pullbackTensorModulesIso g (tensorModules S A B) D).hom ≫
        (@MonoidalCategoryStruct.whiskerRight X.Modules _ _ _ _
            (pullbackTensorModulesIso g A B).hom
            ((Scheme.Modules.pullback g).obj D : X.Modules)) ≫
          (α_ ((Scheme.Modules.pullback g).obj A : X.Modules)
            ((Scheme.Modules.pullback g).obj B : X.Modules)
            ((Scheme.Modules.pullback g).obj D : X.Modules)).hom :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator g.toLRSHom.toShHom A B D

/-- **[Stacks, Tag 01CD] is natural in the second variable**, at the scheme spelling and in
whiskered form. This is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_naturality_right`. -/
@[reassoc]
public theorem pullbackTensorModulesIso_whiskerLeft {X S : Scheme.{u}} (g : X ⟶ S)
    (A : S.Modules) {B B' : S.Modules} (v : B ⟶ B') :
    (Scheme.Modules.pullback g).map (A ◁ v) ≫ (pullbackTensorModulesIso g A B').hom =
      (pullbackTensorModulesIso g A B).hom ≫
        ((Scheme.Modules.pullback g).obj A ◁ (Scheme.Modules.pullback g).map v) :=
  Stacks.PullbackTensorCoherence.pullbackTensorComparison_naturality_right g.toLRSHom.toShHom v

/-- **The inverse-image comparison carries the successor shape to the successor shape**: the
associativity constraint followed by a left whiskering, which is the shape of
`Stacks.Algebraization.tensorModulesSuccIso`, is carried by [Stacks, Tag 01CD] to the same shape
for the inverse images. This is the composite of
`Stacks.Algebraization.pullbackTensorModulesIso_associator` and
`Stacks.Algebraization.pullbackTensorModulesIso_whiskerLeft`. -/
public theorem pullbackTensorModulesIso_assoc_whiskerLeft {X S : Scheme.{u}} (g : X ⟶ S)
    (F M N : S.Modules) {Q : S.Modules} (e : tensorModules S M N ⟶ Q) :
    (Scheme.Modules.pullback g).map ((α_ F M N).hom ≫ F ◁ e) ≫
        (pullbackTensorModulesIso g F Q).hom =
      (pullbackTensorModulesIso g (tensorModules S F M) N).hom ≫
        (@MonoidalCategoryStruct.whiskerRight X.Modules _ _ _ _
          (pullbackTensorModulesIso g F M).hom
          ((Scheme.Modules.pullback g).obj N : X.Modules)) ≫
        (α_ ((Scheme.Modules.pullback g).obj F : X.Modules)
            ((Scheme.Modules.pullback g).obj M : X.Modules)
            ((Scheme.Modules.pullback g).obj N : X.Modules)).hom ≫
          ((Scheme.Modules.pullback g).obj F : X.Modules) ◁
            ((pullbackTensorModulesIso g M N).inv ≫ (Scheme.Modules.pullback g).map e) :=
  comp_eq_of_square_and_cancel _ _ _ _ _ _ _ _ _ _ _ _
    (CategoryTheory.Functor.map_comp _ _ _)
    (MonoidalCategory.whiskerLeft_comp _ _ _)
    (pullbackTensorModulesIso_whiskerLeft g F e)
    (pullbackTensorModulesIso_associator g F M N)
    (whiskerLeft_hom_inv_id _ _)

/-! ### The identifications of a twist and of a tensor product, in `⊗ₘ` form -/

/-- **The identification of the `n`-th twist of a coherent triple, with the tensor product of the
two identifications written in the monoidal `⊗ₘ` form** rather than in the bifunctor form the
`alpha` field of `Stacks.Algebraization.CoherentTriple.twistZ` is built with.

Stated in pure term mode with no ascribed type — the `:=` of a `def`, not the `: … :=` of a
`theorem` — so that the `rw`-vs-instance-mismatch fix it performs (a `congrArg`/`Eq.trans`
composite, not a `rw`) gets a heartbeat budget of its own instead of sharing one with everything
else its consumers need; the statement is written out as the ascription on `rfl`. -/
public noncomputable def alpha_twistZ_eq_tensorHom {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  (rfl : (T.twistZ L hL n).alpha.hom =
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).hom ≫
        tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom (hL.alphaPow n).hom ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀
          (tensorPowScheme (closedFibre A f) L.F₀ n)).inv).trans (congrArg
    (fun t => (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)) T.F
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).hom ≫
      t ≫
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀
        (tensorPowScheme (closedFibre A f) L.F₀ n)).inv)
    (tensorModulesMap_hom_eq_tensorHom (puncturedClosedFibre A f).toScheme T.alpha
      (hL.alphaPow n)))

/-- **The identification of the tensor product of a coherent triple with an invertible one, with
the tensor product of the two identifications written in the monoidal `⊗ₘ` form** rather than in
the bifunctor form the `alpha` field of
`Stacks.Algebraization.CoherentTriple.tensorInvertible` is built with. Stated in pure term mode
with no ascribed type, the idiom of `Stacks.Algebraization.alpha_twistZ_eq_tensorHom`. -/
public noncomputable def alpha_tensorInvertible_eq_tensorHom {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T Q : CoherentTriple A f) (hQ : IsInvertibleTriple Q) :=
  (rfl : (T.tensorInvertible Q hQ).alpha.hom =
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F Q.F).hom ≫
        tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom Q.alpha.hom ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ Q.F₀).inv).trans (congrArg
    (fun t => (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)) T.F Q.F).hom ≫
      t ≫
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ Q.F₀).inv)
    (tensorModulesMap_hom_eq_tensorHom (puncturedClosedFibre A f).toScheme T.alpha Q.alpha))

/-- The square identifying `(hL.alphaPow (n + 1)).hom` through the successor comparison of the
tensor powers, by naturality of `Stacks.Algebraization.alphaPow_tensorPowSchemeSuccIso`. Split
off for the same reason as `Stacks.Algebraization.alpha_twistZ_eq_tensorHom`. -/
private noncomputable def alpha_twistZ_tensorModulesSuccIso_hs {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {L : CoherentTriple A f} (hL : IsInvertibleTriple L) (n : ℤ) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  (congrArg
    (fun t => (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) L.F).inv ≫ t)
    (alphaPow_tensorPowSchemeSuccIso hL n)).trans (Iso.inv_hom_id_assoc _ _)

/-- The "middle" square of the outer pasting, built from `alpha_twistZ_tensorModulesSuccIso_hs`
by `Stacks.Algebraization.assoc_whiskerLeft_tensorHom_of_succ_square`. Split off so that this
application gets a fresh heartbeat budget, separate from the one that produced `hs`. -/
private noncomputable def alpha_twistZ_tensorModulesSuccIso_hmid {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  assoc_whiskerLeft_tensorHom_of_succ_square T.alpha.hom (hL.alphaPow n).hom
    L.alpha.hom (hL.alphaPow (n + 1)).hom
    (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) L.F).inv
    (pullbackTensorModulesIso (puncturedClosedFibre A f).ι
        (tensorPowScheme (closedFibre A f) L.F₀ n) L.F₀).inv
    ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).map
      (tensorPowSchemeSuccIso (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n).hom)
    ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
      (tensorPowSchemeSuccIso (closedFibre A f) L.F₀ n).hom)
    (alpha_twistZ_tensorModulesSuccIso_hs hL n)

/-- The "outer" square of the outer pasting, built from
`Stacks.Algebraization.alpha_twistZ_eq_tensorHom` by
`Stacks.Algebraization.whiskerRight_tensorHom_comp_whiskerRight`. Split off for the same reason as
`alpha_twistZ_tensorModulesSuccIso_hmid`. -/
private noncomputable def alpha_twistZ_tensorModulesSuccIso_hw {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  whiskerRight_tensorHom_comp_whiskerRight L.alpha.hom
    (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)) T.F
      (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
    (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀
      (tensorPowScheme (closedFibre A f) L.F₀ n))
    (T.alpha.hom ⊗ₘ (hL.alphaPow n).hom) ((T.twistZ L hL n).alpha.hom)
    (alpha_twistZ_eq_tensorHom T hL n)

/-- The outer assembly of `Stacks.Algebraization.alpha_twistZ_tensorModulesSuccIso`, with the
`(n + 1)`-st twist's identification already unfolded to its `⊗ₘ` form (`hn1` in that theorem).
Split off into its own declaration, and in turn built from `alpha_twistZ_tensorModulesSuccIso_hmid`
and `alpha_twistZ_tensorModulesSuccIso_hw` rather than inlining their construction, so that the
heavy unification of `Stacks.Algebraization.comp_eq_of_outer_squares`'s seventeen morphism
metavariables against `hk`, `hj`, `hmid`, `hw` gets a fresh heartbeat budget of its own, separate
from the budgets spent computing `hmid` and `hw` themselves. -/
private noncomputable def alpha_twistZ_tensorModulesSuccIso_aux {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  comp_eq_of_outer_squares _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl
    (pullbackTensorModulesIso_assoc_whiskerLeft (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A)) T.F
      (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n) L.F
      (tensorPowSchemeSuccIso (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n).hom)
    (pullbackTensorModulesIso_assoc_whiskerLeft (puncturedClosedFibre A f).ι T.F₀
      (tensorPowScheme (closedFibre A f) L.F₀ n) L.F₀
      (tensorPowSchemeSuccIso (closedFibre A f) L.F₀ n).hom)
    (alpha_twistZ_tensorModulesSuccIso_hmid T hL n) (alpha_twistZ_tensorModulesSuccIso_hw T hL n)

/-- **The successor comparison of the tensor powers carries the identification of the `n`-th
twist to the identification of the `(n + 1)`-st**, read through `tensorModulesSuccIso` on each
side. This is the compatibility square that makes `Stacks.Algebraization.tensorModulesSuccIso`
an isomorphism of coherent triples, pasted from
`Stacks.Algebraization.alphaPow_tensorPowSchemeSuccIso` between two copies of
`Stacks.Algebraization.pullbackTensorModulesIso_assoc_whiskerLeft`, by
`Stacks.Algebraization.comp_eq_of_outer_squares`; see the implementation notes of this file. -/
public theorem alpha_twistZ_tensorModulesSuccIso {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    letI := hL.invertible_F
    letI := hL.invertible_F₀
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).map
      (tensorModulesSuccIso (Stacks.Divisors.puncturedSpectrum A).toScheme T.F L.F n).hom ≫
      (T.twistZ L hL (n + 1)).alpha.hom =
    (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))
        (tensorModules (Stacks.Divisors.puncturedSpectrum A).toScheme T.F
          (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)) L.F).hom ≫
      ((T.twistZ L hL n).alpha.hom ⊗ₘ L.alpha.hom) ≫
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι
          (tensorModules (closedFibre A f) T.F₀
            (tensorPowScheme (closedFibre A f) L.F₀ n)) L.F₀).inv ≫
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
        (tensorModulesSuccIso (closedFibre A f) T.F₀ L.F₀ n).hom := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  rw [alpha_twistZ_eq_tensorHom T hL (n + 1)]
  exact alpha_twistZ_tensorModulesSuccIso_aux T hL n

/-! ### The successor identification as a morphism of coherent triples -/

/-- A factorisation of the left-hand side through four morphisms, together with a factorisation
of a fifth morphism through the first three of them, gives the two-step factorisation. Stated for
an abstract category so that the rewrites along `CategoryTheory.Category.assoc` fire; in
`X.Modules` they do not, for the reason recorded in the implementation notes of this file. -/
public theorem eq_comp_of_eq_comp_four {C : Type*} [Category C] {W X₁ X₂ X₃ Z : C}
    (m : W ⟶ Z) (a : W ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ Z) (e : W ⟶ X₃)
    (hm : m = a ≫ b ≫ c ≫ d) (he : e = a ≫ b ≫ c) : m = e ≫ d := by
  rw [hm, he, Category.assoc, Category.assoc]

/-- **The successor identification of the twists, as a morphism of coherent triples**
`(T ⊗ L^{⊗ n}) ⊗ L ⟶ T ⊗ L^{⊗ (n + 1)}`. Its two members are the successor identifications
`Stacks.Algebraization.tensorModulesSuccIso` of the two members, and its compatibility square is
`Stacks.Algebraization.alpha_twistZ_tensorModulesSuccIso` read against the `alpha` field of
`Stacks.Algebraization.CoherentTriple.tensorInvertible`.

Both members are isomorphisms, so this is an isomorphism of coherent triples in the sense the
consumers of such an identification use — `Stacks.Algebraization.CoherentTriple.ShortExact.compIso`
and `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom`, both of which ask for a
`Hom` with `IsIso` on each member. -/
public noncomputable def CoherentTriple.tensorInvertibleTwistZSuccHom {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    ((T.twistZ L hL n).tensorInvertible L hL).Hom (T.twistZ L hL (n + 1)) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  { onPunctured :=
      (tensorModulesSuccIso (Stacks.Divisors.puncturedSpectrum A).toScheme T.F L.F n).hom
    onClosedFibre := (tensorModulesSuccIso (closedFibre A f) T.F₀ L.F₀ n).hom
    compatible := eq_comp_of_eq_comp_four _ _ _ _ _ _
      (alpha_twistZ_tensorModulesSuccIso T hL n)
      (alpha_tensorInvertible_eq_tensorHom (T.twistZ L hL n) L hL) }

/-- The punctured-spectrum member of
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccHom` is the successor
identification of the punctured-spectrum members. -/
public theorem CoherentTriple.tensorInvertibleTwistZSuccHom_onPunctured {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    letI := hL.invertible_F
    (T.tensorInvertibleTwistZSuccHom hL n).onPunctured =
      (tensorModulesSuccIso (Stacks.Divisors.puncturedSpectrum A).toScheme T.F L.F n).hom :=
  rfl

/-- The closed-fibre member of
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccHom` is the successor
identification of the closed-fibre members. -/
public theorem CoherentTriple.tensorInvertibleTwistZSuccHom_onClosedFibre {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    letI := hL.invertible_F₀
    (T.tensorInvertibleTwistZSuccHom hL n).onClosedFibre =
      (tensorModulesSuccIso (closedFibre A f) T.F₀ L.F₀ n).hom :=
  rfl

/-- **Both members of the successor identification of the twists are isomorphisms**, so
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccHom` is an isomorphism of
coherent triples. -/
public theorem CoherentTriple.isIso_tensorInvertibleTwistZSuccHom {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) {L : CoherentTriple A f}
    (hL : IsInvertibleTriple L) (n : ℤ) :
    IsIso (T.tensorInvertibleTwistZSuccHom hL n).onPunctured ∧
      IsIso (T.tensorInvertibleTwistZSuccHom hL n).onClosedFibre := by
  let := hL.invertible_F
  let := hL.invertible_F₀
  refine ⟨?_, ?_⟩
  · rw [CoherentTriple.tensorInvertibleTwistZSuccHom_onPunctured]
    exact Iso.isIso_hom _
  · rw [CoherentTriple.tensorInvertibleTwistZSuccHom_onClosedFibre]
    exact Iso.isIso_hom _

end Stacks.Algebraization

end
