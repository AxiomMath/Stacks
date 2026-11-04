module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechLocalCohomology
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClass
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.GlobalEquationsComplexData

/-!
# The fraction class map of Stacks 0G7Q

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global functions with `c ≥ 1`, let `Z` be
their common zero locus and let `ℱ` be a quasi-coherent `𝒪_X`-module.  A local section `s` of
`ℱ` has a fraction `s / (f₁ ⋯ f_c)`: the product of the equations is invertible on the
intersection of their principal opens, so the restriction of `s` there is divisible by it, and
the result is a section of the top term `ℱ_{1 … c}` of the extended alternating Čech complex
`ℱ^•` of [Stacks, Tag 0G7I].  Its class in the degree-`c` cohomology sheaf of `ℱ^•` — the
cokernel of `⨁ᵢ ℱ_{1 … î … c} ⟶ ℱ_{1 … c}` — only depends on `s` modulo the image of
`(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`, because multiplying `s` by `f_i` makes the fraction the image under
the last Čech differential of the cochain supported on the `i`-th face.  So the fraction class
descends to the quotient `ℱ/(f₁, …, f_c)ℱ` and, through the identification
`i_* 𝓗ᶜ_Z(ℱ) ≅ Hᶜ(ℱ^•)` of [Stacks, Tag 0G7M], gives a map
`ℱ/(f₁, …, f_c)ℱ ⟶ i_* 𝓗ᶜ_Z(ℱ)`.  Its transpose under the adjunction between inverse image and
direct image along the inclusion of `Z` is the canonical map

`c_{f₁, …, f_c} : i^{-1}(ℱ/(f₁, …, f_c)ℱ) ⟶ 𝓗ᶜ_Z(ℱ)`.

Multiplication by a global function on a module is also set up here, as the natural endomorphism
of the identity functor it is, together with its invertibility on the direct images occurring in
the Čech complex.

## Main definitions

* `Stacks.Perfect.FractionClass.smulHom`: multiplication by a global function on a module.
* `Stacks.Perfect.FractionClass.fracTerm`: the fraction `s / (f₁ ⋯ f_c)`, with values in the top
  term of the extended alternating Čech complex.
* `Stacks.Perfect.FractionClass.classMap`: its class in the degree-`c` cohomology sheaf.
* `Stacks.Perfect.FractionClass.equationsMap` and
  `Stacks.Perfect.FractionClass.equationsQuotient`: the map `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ` and its
  cokernel `ℱ/(f₁, …, f_c)ℱ`.
* `Stacks.Perfect.FractionClass.quotientClassMap`: the fraction class on the quotient.
* `Stacks.Perfect.FractionClass.pushforwardFractionClass`: the map
  `ℱ/(f₁, …, f_c)ℱ ⟶ i_* 𝓗ᶜ_Z(ℱ)`.
* `Stacks.Perfect.FractionClass.fractionClass`: the map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q].

## Main results

* `Stacks.Perfect.FractionClass.smulHom_comp_classMap`: multiplying the numerator by one of the
  equations kills the fraction class.
* `Stacks.Perfect.FractionClass.cokernelπ_comp_quotientClassMap`: the map on the quotient sends
  the class of a section to the class of its fraction.
* `Stacks.Perfect.FractionClass.homEquiv_fractionClass`: `c_{f₁, …, f_c}` is the transpose of
  that map.
* `Stacks.Perfect.FractionClass.cplxHomologyZeroIso` and
  `Stacks.Perfect.FractionClass.isIso_quotientClassMap`: for the **empty** family of equations
  the degree-zero cohomology sheaf of the complex is `ℱ` itself and the map out of the quotient
  is that identification.

## Implementation notes

Multiplication by a global function is built as a natural endomorphism of the identity functor,
so that it commutes with every morphism of modules; that single naturality statement replaces all
the sectionwise bookkeeping in the computations below.  On a direct image it is the direct image
of multiplication by the pullback of the function, which is invertible as soon as the function is
invertible on the open one restricts to; hence multiplication by the product of the equations of
an increasing tuple is invertible on the direct image belonging to that tuple.

The division by the product of the equations is characterized by the morphism identity saying
that multiplying it back by that product is the canonical restriction; no section-level unfolding
occurs.  The identity making the fraction class well defined is then proved by cancelling the
invertible multiplication by the product of the equations other than the one multiplied in.

There are two constructions of the extended alternating Čech complex in this repository and they
are isomorphic by [Stacks, Tag 0G7I]; the fraction is built on
`Stacks.Perfect.ExtendedAlternatingCech.cplx`, whose terms, differentials and canonical
restrictions are available as named maps, and transported along that isomorphism to the
construction on which [Stacks, Tag 0G7M] identifies the cohomology sheaves with the local
cohomology sheaves.

The top term of the complex has one summand, indexed by the tuple of all the equations, and the
term after it vanishes: there is no increasing `(c+1)`-tuple of indices in `Fin c`.  So the
degree-`c` cycles are the whole top term and the fraction class is the composite of the induced
map to the cycles with the projection onto homology; the vanishing after multiplication by an
equation is then the statement that a boundary has zero class.

The number of equations is written `c = n + 1`, which is what makes the top term a product over
a one-element index type.  The descent through the equations is proved separately for one
equation, where the preceding term of the complex is the coefficient module itself, and for at
least two, where it is a product over the faces.

## References

* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G7K](https://stacks.math.columbia.edu/tag/0G7K)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0AEF](https://stacks.math.columbia.edu/tag/0AEF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.FractionClass

/-! ### Multiplication by a global function -/

variable {X : Scheme.{u}}

/-- The restriction of a global function to an open, as a scalar acting on the sections of a
module over that open. -/
public def resTop (r : Γ(X, ⊤)) (U : (Opens ↥X)ᵒᵖ) : X.ringCatSheaf.obj.obj U :=
  X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op r

/-- Restricting a global function further is restricting it once. -/
public theorem ringCatSheaf_map_resTop (r : Γ(X, ⊤)) {U V : (Opens ↥X)ᵒᵖ} (g : U ⟶ V) :
    X.ringCatSheaf.obj.map g (resTop r U) = resTop r V := by
  have h : X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ X.presheaf.map g =
      X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op := by
    rw [← Functor.map_comp]; congr 1
  exact congrArg (fun φ : X.presheaf.obj (op ⊤) ⟶ X.presheaf.obj V =>
    ConcreteCategory.hom φ r) h

/-- Multiplication by a global function `r ∈ Γ(X, 𝒪_X)`, as a natural endomorphism of the
identity functor on `𝒪_X`-modules: on sections over an open it is multiplication by the
restriction of `r` to that open. -/
public def globalSmul (r : Γ(X, ⊤)) : 𝟭 X.Modules ⟶ 𝟭 X.Modules where
  app N := show N ⟶ N from
    { val :=
      { app U := ModuleCat.ofHom
          { toFun := fun x => resTop r U • x
            map_add' := fun x y => smul_add _ _ _
            map_smul' := by
              intro a x
              let _ : CommRing (X.ringCatSheaf.obj.obj U) :=
                inferInstanceAs (CommRing (X.presheaf.obj U))
              exact smul_comm _ _ _ }
        naturality := by
          intro U V g
          ext x
          exact ((N.val.map_smul g (resTop r U) x).trans
            (congrArg (fun a => a • N.val.map g x) (ringCatSheaf_map_resTop r g))).symm } }
  naturality := by
    intro N P g
    ext U x
    exact ((g.val.app (op U)).hom.map_smul _ _).symm

/-- Multiplication by a global function `r ∈ Γ(X, 𝒪_X)` on an `𝒪_X`-module. -/
public def smulHom (r : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M := (globalSmul r).app M

/-- On sections over an open `V`, multiplication by `r` is multiplication by the restriction of
`r` to `V`. -/
public theorem smulHom_app_apply (r : Γ(X, ⊤)) (M : X.Modules) (V : X.Opens) (x : Γ(M, V)) :
    (smulHom r M).app V x = (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r) • x := rfl

/-- Multiplication by a global function commutes with every morphism of modules. -/
public theorem smulHom_naturality (r : Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    smulHom r M ≫ φ = φ ≫ smulHom r N := ((globalSmul r).naturality φ).symm

/-- Two morphisms of modules agree when they agree on every section over every open. -/
private theorem hom_ext_apply {M N : X.Modules} {φ ψ : M ⟶ N}
    (h : ∀ (V : X.Opens) (x : Γ(M, V)), φ.app V x = ψ.app V x) : φ = ψ :=
  Scheme.Modules.hom_ext _ _ fun V => AddCommGrpCat.hom_ext (AddMonoidHom.ext (h V))

/-- Multiplication by a product of two global functions is the composite of the two
multiplications. -/
public theorem smulHom_mul (r s : Γ(X, ⊤)) (M : X.Modules) :
    smulHom (r * s) M = smulHom r M ≫ smulHom s M := by
  refine hom_ext_apply fun V x => ?_
  rw [Scheme.Modules.Hom.comp_app]
  show (smulHom (r * s) M).app V x = (smulHom s M).app V ((smulHom r M).app V x)
  rw [smulHom_app_apply, smulHom_app_apply, smulHom_app_apply, map_mul, smul_smul, mul_comm]

/-- Multiplication by the unit global function is the identity. -/
public theorem smulHom_one (M : X.Modules) : smulHom (1 : Γ(X, ⊤)) M = 𝟙 M := by
  refine hom_ext_apply fun V x => ?_
  rw [smulHom_app_apply, map_one, one_smul]
  rfl

/-- Multiplication by an invertible global function is invertible. -/
public theorem isIso_smulHom {r : Γ(X, ⊤)} (hr : IsUnit r) (M : X.Modules) :
    IsIso (smulHom r M) := by
  obtain ⟨v, hv⟩ := hr.exists_right_inv
  refine ⟨smulHom v M, ?_, ?_⟩
  · rw [← smulHom_mul, hv, smulHom_one]
  · rw [← smulHom_mul, mul_comm, hv, smulHom_one]

/-- Multiplication by a global function on a direct image is the direct image of multiplication
by the pullback of that function. -/
public theorem smulHom_pushforward {Y : Scheme.{u}} (g : Y ⟶ X) (N : Y.Modules) (r : Γ(X, ⊤)) :
    smulHom r ((Scheme.Modules.pushforward g).obj N) =
      (Scheme.Modules.pushforward g).map (smulHom (g.appTop r) N) := by
  refine hom_ext_apply fun V x => ?_
  have h2 := congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(Y, g ⁻¹ᵁ V) => ConcreteCategory.hom φ r)
    (g.naturality (U' := (⊤ : X.Opens)) (U := V) (homOfLE (le_top : V ≤ ⊤)).op)
  simp only [ConcreteCategory.comp_apply] at h2
  have h3 : ConcreteCategory.hom (Scheme.Hom.app g V)
        (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r) =
      Y.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ V ≤ ⊤)).op (g.appTop r) := by
    rw [h2]; congr 1
  exact congrArg (fun a : Γ(Y, g ⁻¹ᵁ V) => a • (show Γ(N, g ⁻¹ᵁ V) from x)) h3

/-- A global function invertible on an open restricts to an invertible section there. -/
private theorem isUnit_res {V : X.Opens} (r : Γ(X, ⊤)) (hV : V ≤ X.basicOpen r) :
    IsUnit (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r) := by
  have hunit : IsUnit ((X.presheaf.map
      (homOfLE (show X.basicOpen r ≤ ⊤ from le_top)).op) r) :=
    X.toRingedSpace.isUnit_res_basicOpen r
  have hmap := hunit.map (X.presheaf.map (homOfLE hV).op).hom
  convert hmap using 1
  simp [← X.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]

/-- A global function invertible on an open pulls back to an invertible global function on that
open. -/
private theorem isUnit_appTop_ι {U : X.Opens} (r : Γ(X, ⊤)) (h : U ≤ X.basicOpen r) :
    IsUnit (U.ι.appTop r) := by
  rw [Scheme.Opens.ι_appTop]
  exact isUnit_res r (le_trans (le_of_eq U.ι_image_top) h)

/-! ### Multiplication by the equations on the terms of the Čech complex -/

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)

/-- The principal intersection of an increasing tuple is contained in each of the principal
opens it is made of. -/
private theorem equationsOpen_le_basicOpen {p : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p)
    (k : Fin (p + 1)) : equationsOpen f p s ≤ X.basicOpen (f (s.1 k)) := iInf_le _ k

/-- Multiplication by a global function which is invertible on the principal intersection of an
increasing tuple is invertible on the corresponding direct image. -/
private theorem isIso_smulHom_restrictedModule {p : ℕ}
    (s : CechCochains.OrdIndex (I := Fin c) p) (r : Γ(X, ⊤))
    (h : IsUnit ((equationsOpen f p s).ι.appTop r)) :
    IsIso (smulHom r (restrictedModule f F p s)) := by
  rw [show restrictedModule f F p s =
    (Scheme.Modules.pushforward (equationsOpen f p s).ι).obj
      ((Scheme.Modules.pullback (equationsOpen f p s).ι).obj F) from rfl, smulHom_pushforward]
  have := isIso_smulHom h ((Scheme.Modules.pullback (equationsOpen f p s).ι).obj F)
  infer_instance

/-- Multiplication by a product of equations each of which is invertible on the principal
intersection of an increasing tuple is invertible on the corresponding direct image. -/
private theorem isIso_smulHom_prodComp {p m : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p)
    (g : Fin m → Fin c) (h : ∀ k, equationsOpen f p s ≤ X.basicOpen (f (g k))) :
    IsIso (smulHom (∏ k, f (g k)) (restrictedModule f F p s)) := by
  refine isIso_smulHom_restrictedModule f F s _ ?_
  rw [map_prod, IsUnit.prod_univ_iff]
  intro k
  exact isUnit_appTop_ι (f (g k)) (h k)

/-! ### The top increasing tuple -/

/-- The increasing tuple consisting of all the indices. -/
private def topIndex (n : ℕ) : CechCochains.OrdIndex (I := Fin (n + 1)) n := ⟨id, strictMono_id⟩

/-- There is only one increasing `(n+1)`-tuple of indices in `Fin (n+1)`. -/
private theorem topIndex_unique {n : ℕ} (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    t = topIndex n := by
  apply Subtype.ext
  apply t.2.eq_of_range_eq (strictMono_id : StrictMono (id : Fin (n + 1) → Fin (n + 1)))
  have hcard : (Set.range t.1).ncard = n + 1 := by
    rw [Set.ncard_eq_toFinset_card]
    simp [Finset.card_image_of_injective, t.2.injective]
  have heq : Set.range t.1 = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [hcard, Set.ncard_univ]
    simp
  simpa [topIndex] using heq

/-- The principal intersection of the top tuple is contained in every principal open. -/
private theorem topIndex_le_basicOpen {n : ℕ} (g : Fin (n + 1) → Γ(X, ⊤))
    (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) (j : Fin (n + 1)) :
    equationsOpen g n t ≤ X.basicOpen (g j) := by
  rw [topIndex_unique t]
  exact iInf_le (fun k => X.basicOpen (g ((topIndex n).1 k))) j

/-! ### Restriction of the augmentation -/

/-- Restricting a section to a principal intersection and then to a smaller one is restricting
it to the smaller one. -/
private theorem augR_comp_canR {p q : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p)
    (t : CechCochains.OrdIndex (I := Fin c) q) (h : equationsOpen f q t ≤ equationsOpen f p s) :
    augR f F p s ≫ canR f F s t h = augR f F q t := by
  refine hom_ext_apply fun V x => ?_
  refine (restrictedModuleSection_bijective f F q t V).1 ?_
  rw [comp_app_apply, canR_section, augR_section, augR_section, restr_eq]
  exact collapse2 F _ _ _ x

/-- Multiplication by the product of the equations of an increasing tuple is invertible on the
corresponding direct image. -/
private theorem isIso_smulHom_prodAt {p : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p) :
    IsIso (smulHom (∏ k, f (s.1 k)) (restrictedModule f F p s)) :=
  isIso_smulHom_prodComp f F s s.1 (equationsOpen_le_basicOpen f s)

/-- Division of a section by the product of the equations of an increasing tuple, with values in
the corresponding direct image, where that product is invertible. -/
private def divFactor {p : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p) :
    F ⟶ restrictedModule f F p s :=
  haveI := isIso_smulHom_prodAt f F s
  augR f F p s ≫ inv (smulHom (∏ k, f (s.1 k)) (restrictedModule f F p s))

/-- Multiplying the fraction with the equations of a tuple as denominator by that product gives
back the restriction of the numerator. -/
private theorem divFactor_comp_smulHom {p : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p) :
    divFactor f F s ≫ smulHom (∏ k, f (s.1 k)) (restrictedModule f F p s) = augR f F p s := by
  have := isIso_smulHom_prodAt f F s
  show (augR f F p s ≫ inv (smulHom (∏ k, f (s.1 k)) (restrictedModule f F p s))) ≫ _ = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **Enlarging the denominator.** Multiplying the fraction with the equations of a tuple `t` as
denominator by an equation `r` whose product with the equations of a smaller tuple `s` is the
product for `t` gives the restriction of the fraction belonging to `s`. -/
private theorem smulHom_comp_divFactor {p q : ℕ} (s : CechCochains.OrdIndex (I := Fin c) p)
    (t : CechCochains.OrdIndex (I := Fin c) q) (h : equationsOpen f q t ≤ equationsOpen f p s)
    (r : Γ(X, ⊤)) (hiso : IsIso (smulHom (∏ k, f (s.1 k)) (restrictedModule f F q t)))
    (hmul : r * (∏ k, f (s.1 k)) = ∏ k, f (t.1 k)) :
    smulHom r F ≫ divFactor f F t = divFactor f F s ≫ canR f F s t h := by
  have := hiso
  rw [← cancel_mono (smulHom (∏ k, f (s.1 k)) (restrictedModule f F q t))]
  calc (smulHom r F ≫ divFactor f F t) ≫ smulHom (∏ k, f (s.1 k)) (restrictedModule f F q t)
      = smulHom r F ≫ (smulHom (∏ k, f (s.1 k)) F ≫ divFactor f F t) := by
        rw [Category.assoc, ← smulHom_naturality (∏ k, f (s.1 k)) (divFactor f F t)]
    _ = smulHom (∏ k, f (t.1 k)) F ≫ divFactor f F t := by
        rw [← Category.assoc, ← smulHom_mul, hmul]
    _ = augR f F q t := by
        rw [smulHom_naturality (∏ k, f (t.1 k)) (divFactor f F t), divFactor_comp_smulHom]
    _ = augR f F p s ≫ canR f F s t h := (augR_comp_canR f F s t h).symm
    _ = (divFactor f F s ≫ canR f F s t h) ≫
          smulHom (∏ k, f (s.1 k)) (restrictedModule f F q t) := by
        rw [Category.assoc, ← smulHom_naturality (∏ k, f (s.1 k)) (canR f F s t h),
          ← Category.assoc, divFactor_comp_smulHom]

/-! ### The fraction with the equations as denominator -/

section Fraction

variable {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) (F : X.Modules)

/-- Multiplication by the product of all the equations is invertible on the top Čech term. -/
public theorem isIso_smulHom_equationsProd
    (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    IsIso (smulHom (∏ i, f i) (restrictedModule f F n t)) := by
  have h := isIso_smulHom_prodComp f F t id (topIndex_le_basicOpen f t)
  exact h

/-- The fraction `s / (f₁ ⋯ f_c)`, as a map to the summand of the top Čech term belonging to an
increasing tuple: restrict the section and divide by the product of the equations, which is
invertible there. -/
public def fracFactor (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    F ⟶ restrictedModule f F n t :=
  haveI := isIso_smulHom_equationsProd f F t
  augR f F n t ≫ inv (smulHom (∏ i, f i) (restrictedModule f F n t))

/-- Multiplying the fraction `s / (f₁ ⋯ f_c)` by the product of the equations gives back the
restriction of `s`. -/
public theorem fracFactor_comp_smulHom (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    fracFactor f F t ≫ smulHom (∏ i, f i) (restrictedModule f F n t) = augR f F n t := by
  have := isIso_smulHom_equationsProd f F t
  show (augR f F n t ≫ inv (smulHom (∏ i, f i) (restrictedModule f F n t))) ≫ _ = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **The fraction map.** The section `s / (f₁ ⋯ f_c)` of the top term of the extended
alternating Čech complex of `f₁, …, f_c`, as a map from the coefficient module. -/
public def fracTerm : F ⟶ prodTerm f F n := Pi.lift (fracFactor f F)

/-- The components of the fraction map are the fractions in the summands. -/
public theorem fracTerm_comp_π (t : CechCochains.OrdIndex (I := Fin (n + 1)) n) :
    fracTerm f F ≫
        Pi.π (fun u : CechCochains.OrdIndex (I := Fin (n + 1)) n => restrictedModule f F n u) t =
      fracFactor f F t :=
  Pi.lift_π _ t

/-! ### The fraction class in degree-`c` cohomology -/

/-- The fraction with all the equations as denominator is the fraction with the equations of the
top tuple as denominator. -/
private theorem fracFactor_topIndex :
    fracFactor f F (topIndex n) = divFactor f F (topIndex n) := rfl

/-- The increasing tuple of all the indices but one. -/
private def faceIndex {m : ℕ} (j : Fin (m + 2)) : CechCochains.OrdIndex (I := Fin (m + 2)) m :=
  ⟨(topIndex (m + 1)).1 ∘ j.succAbove, CechCochains.strictMono_omit (topIndex (m + 1)).2 j⟩

private theorem faceIndex_injective {m : ℕ} {j k : Fin (m + 2)}
    (h : faceIndex j = faceIndex k) : j = k :=
  Fin.succAbove_left_injective (congrArg Subtype.val h)

private alias sign_smul_sign := AlgebraicGeometry.ExtendedAlternatingCech.sign_smul_sign

/-- **Multiplying the fraction by an equation gives a boundary**, in the presence of at least two
equations: the product of the remaining equations divides the numerator on the principal
intersection omitting that equation, and the resulting cochain is carried to the fraction by the
last Čech differential. -/
private theorem exists_descent_succ {m : ℕ} (g : Fin (m + 2) → Γ(X, ⊤)) (G : X.Modules)
    (i : Fin (m + 2)) :
    ∃ W : G ⟶ prodTerm g G m,
      smulHom (g i) G ≫ fracTerm g G = W ≫ difSucc g G m := by
  classical
  refine ⟨Pi.lift fun s => (if faceIndex i = s then ((-1 : ℤ) ^ (i : ℕ)) else 0) •
    divFactor g G s, ?_⟩
  refine Limits.Pi.hom_ext _ _ fun t => ?_
  obtain rfl := topIndex_unique t
  have hsum : difSucc g G m ≫
        Pi.π (fun u : CechCochains.OrdIndex (I := Fin (m + 2)) (m + 1) =>
          restrictedModule g G (m + 1) u) (topIndex (m + 1)) =
      ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (Pi.π (fun u : CechCochains.OrdIndex (I := Fin (m + 2)) m => restrictedModule g G m u)
            (faceIndex j) ≫
          canR g G (faceIndex j) (topIndex (m + 1)) (omitLe g (topIndex (m + 1)) j)) :=
    Pi.lift_π _ _
  have hterm : ∀ j : Fin (m + 2),
      (Pi.lift fun s => (if faceIndex i = s then ((-1 : ℤ) ^ (i : ℕ)) else 0) •
          divFactor g G s) ≫ (((-1 : ℤ) ^ (j : ℕ)) •
        (Pi.π (fun u : CechCochains.OrdIndex (I := Fin (m + 2)) m => restrictedModule g G m u)
            (faceIndex j) ≫
          canR g G (faceIndex j) (topIndex (m + 1)) (omitLe g (topIndex (m + 1)) j))) =
      ((-1 : ℤ) ^ (j : ℕ)) • ((if faceIndex i = faceIndex j then ((-1 : ℤ) ^ (i : ℕ)) else 0) •
        (divFactor g G (faceIndex j) ≫
          canR g G (faceIndex j) (topIndex (m + 1)) (omitLe g (topIndex (m + 1)) j))) := by
    intro j
    rw [Preadditive.comp_zsmul, ← Category.assoc, Pi.lift_π, Preadditive.zsmul_comp]
  rw [Category.assoc, fracTerm_comp_π, Category.assoc, hsum, Preadditive.comp_sum]
  simp only [hterm]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i) ?_, ite_eq_left rfl, sign_smul_sign,
    fracFactor_topIndex]
  · refine smulHom_comp_divFactor g G (faceIndex i) (topIndex (m + 1))
      (omitLe g (topIndex (m + 1)) i) (g i) ?_ ?_
    · exact isIso_smulHom_prodComp g G (topIndex (m + 1)) (faceIndex i).1
        (fun k => topIndex_le_basicOpen g (topIndex (m + 1)) _)
    · exact (Fin.prod_univ_succAbove g i).symm
  · intro j _ hj
    rw [ite_eq_right (fun hcontra => hj (faceIndex_injective hcontra).symm), zero_smul,
      smul_zero]

/-- **Multiplying the fraction by an equation gives a boundary.** -/
private theorem exists_descent (i : Fin (n + 1)) :
    ∃ W : F ⟶ (cplx f F).X n, smulHom (f i) F ≫ fracTerm f F = W ≫ (cplx f F).d n (n + 1) := by
  cases n with
  | zero =>
      have hi : f i = ∏ j, f j := by
        rw [Fin.prod_univ_one]
        exact congrArg f (Subsingleton.elim (α := Fin 1) i 0)
      have key : smulHom (f i) F ≫ fracTerm f F = difZero f F := by
        refine Limits.Pi.hom_ext _ _ fun t => ?_
        rw [Category.assoc, fracTerm_comp_π,
          show difZero f F ≫ Pi.π _ t = augR f F 0 t from Pi.lift_π _ t,
          ← fracFactor_comp_smulHom f F t, hi]
        exact smulHom_naturality _ _
      exact ⟨𝟙 F, key.trans (((Category.id_comp (difZero f F)).symm).trans
        (congrArg (fun δ : (cplx f F).X 0 ⟶ (cplx f F).X 1 => 𝟙 F ≫ δ)
          (cplx_d_zero f F).symm))⟩
  | succ m =>
      obtain ⟨W, hW⟩ := exists_descent_succ f F i
      exact ⟨W, by rw [cplx_d_succ]; exact hW⟩

end Fraction

/-! ### The class of the fraction and the quotient by the equations -/

section Class

/-- **The fraction `s / (f₁ ⋯ f_c)` in the top term of the extended alternating Čech complex**,
for an arbitrary number `c` of equations. For `c = 0` the denominator is the empty product `1`,
the top term is the degree-zero term `ℱ`, and the fraction is the section itself. -/
public def fracTermTop {m : ℕ} (g : Fin m → Γ(X, ⊤)) (G : X.Modules) : G ⟶ (cplx g G).X m :=
  match m, g with
  | 0, _ => 𝟙 G
  | _ + 1, h => fracTerm h G

/-- With at least one equation the fraction in the top term is the fraction with the product of
all the equations as denominator. -/
public theorem fracTermTop_succ {m : ℕ} (g : Fin (m + 1) → Γ(X, ⊤)) (G : X.Modules) :
    fracTermTop g G = fracTerm g G :=
  rfl

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)

/-- There is no increasing `(c+1)`-tuple of indices in `Fin c`, so the differential out of the
top term of the extended alternating Čech complex vanishes. This holds for every number `c` of
equations, including `c = 0`, where the top term is the degree-zero term `ℱ` and the
differential out of it is the empty product of restrictions. -/
public theorem d_top_eq_zero : (cplx f F).d c (c + 1) = 0 := by
  have hcontra : ∀ _t : CechCochains.OrdIndex (I := Fin c) c, False := by
    intro t
    have h := Fintype.card_le_of_injective t.1 t.2.injective
    simp only [Fintype.card_fin] at h
    omega
  cases c with
  | zero =>
      rw [cplx_d_zero]
      exact Limits.Pi.hom_ext _ _ fun t => (hcontra t).elim
  | succ m =>
      rw [cplx_d_succ]
      exact Limits.Pi.hom_ext _ _ fun t => (hcontra t).elim

/-- The fraction `s / (f₁ ⋯ f_c)` as a cycle in the top degree of the extended alternating Čech
complex: the differential out of the top degree vanishes. -/
public def fracCycle : F ⟶ (cplx f F).cycles c :=
  (cplx f F).liftCycles' (i := c) (fracTermTop f F) (c + 1) rfl
    (by rw [d_top_eq_zero]; exact comp_zero)

/-- The cycle of the fraction is the fraction. -/
public theorem fracCycle_comp_iCycles :
    fracCycle f F ≫ (cplx f F).iCycles c = fracTermTop f F :=
  (cplx f F).liftCycles_i (i := c) (fracTermTop f F) (c + 1)
    ((ComplexShape.up ℕ).next_eq' rfl) (by rw [d_top_eq_zero]; exact comp_zero)

/-- **The fraction class.** The class of the fraction `s / (f₁ ⋯ f_c)` in the degree-`c`
cohomology sheaf of the extended alternating Čech complex of the equations, which is the cokernel
of the last Čech differential. -/
public def classMap : F ⟶ (cplx f F).homology c :=
  fracCycle f F ≫ (cplx f F).homologyπ c

/-- **The fraction class only depends on the numerator modulo the equations.** Multiplying the
numerator by one of the equations kills the class of the fraction, because the result is the image
of a cochain under the last Čech differential. An equation to multiply by is itself a witness
that there is at least one, which is what the descent of the product needs. -/
@[stacks 0G7Q "the class of the fraction depends only on the numerator modulo the equations"]
public theorem smulHom_comp_classMap (j : Fin c) :
    smulHom (f j) F ≫ classMap f F = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, c = n + 1 := ⟨c - 1, by have := j.isLt; omega⟩
  obtain ⟨W, hW⟩ := exists_descent f F j
  have key : smulHom (f j) F ≫ fracCycle f F =
      (cplx f F).liftCycles' (i := n + 1) (W ≫ (cplx f F).d n (n + 1)) (n + 2) rfl
        (by rw [Category.assoc, HomologicalComplex.d_comp_d, comp_zero]) := by
    rw [← cancel_mono ((cplx f F).iCycles (n + 1)), Category.assoc, fracCycle_comp_iCycles,
      HomologicalComplex.liftCycles_i, fracTermTop_succ]
    exact hW
  show smulHom (f j) F ≫ (fracCycle f F ≫ (cplx f F).homologyπ (n + 1)) = 0
  rw [← Category.assoc, key]
  exact (cplx f F).liftCycles_homologyπ_eq_zero_of_boundary _ (n + 2)
    ((ComplexShape.up ℕ).next_eq' rfl) W rfl

/-- The map `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ` given by multiplication by the equations on the
summands. -/
public def equationsMap : (∐ fun _ : Fin c => F) ⟶ F :=
  Sigma.desc fun i => smulHom (f i) F

/-- The quotient `ℱ / (f₁, …, f_c)ℱ` of the coefficient module by the submodule generated by the
equations. -/
public def equationsQuotient : X.Modules := cokernel (equationsMap f F)

/-- The fraction class kills the image of `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ`. -/
public theorem equationsMap_comp_classMap : equationsMap f F ≫ classMap f F = 0 := by
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [comp_zero, ← Category.assoc, equationsMap, Limits.Sigma.ι_desc]
  exact smulHom_comp_classMap f F i

/-- **The fraction class of a residue class.** The map `ℱ/(f₁, …, f_c)ℱ ⟶ Hᶜ(ℱ^•)` sending the
class of a local section `s` to the class of the fraction `s / (f₁ ⋯ f_c)` in the cokernel of the
last Čech differential. -/
public def quotientClassMap : equationsQuotient f F ⟶ (cplx f F).homology c :=
  cokernel.desc (equationsMap f F) (classMap f F) (equationsMap_comp_classMap f F)

/-- The map out of the quotient sends the class of a section to the class of its fraction. -/
@[stacks 0G7Q "the value on the class of a local section is the class of its fraction"]
public theorem cokernelπ_comp_quotientClassMap :
    cokernel.π (equationsMap f F) ≫ quotientClassMap f F = classMap f F :=
  cokernel.π_desc _ _ _

/-! ### The fraction class of an empty family of equations -/

/-- **With no equations the degree-zero cohomology sheaf of the extended alternating Čech complex
is the coefficient module itself.**  The complex has nothing below degree zero and, by
`d_top_eq_zero` at `c = 0`, nothing leaving degree zero either — the degree-one term is a product
over the increasing `1`-tuples in `Fin 0`, of which there are none. -/
public def cplxHomologyZeroIso {g : Fin 0 → Γ(X, ⊤)} (G : X.Modules) :
    (cplx g G).homology 0 ≅ G :=
  CochainComplex.homologyZeroIso (cplx g G) (d_top_eq_zero g G)

/-- **With no equations the fraction class is the canonical identification.**  The denominator is
the empty product `1`, so the fraction is the section itself: `fracTermTop` at `c = 0` is the
identity, hence the cycle it defines is the section and its class is the inverse of
`cplxHomologyZeroIso`. -/
public theorem classMap_comp_cplxHomologyZeroIso_hom {g : Fin 0 → Γ(X, ⊤)} (G : X.Modules) :
    classMap g G ≫ (cplxHomologyZeroIso G).hom = 𝟙 G := by
  rw [classMap, Category.assoc]
  refine Eq.trans (congrArg (fun φ => fracCycle g G ≫ φ)
    (CochainComplex.homologyπ_comp_homologyZeroIso_hom (cplx g G) (d_top_eq_zero g G))) ?_
  exact fracCycle_comp_iCycles g G

/-- `classMap_comp_cplxHomologyZeroIso_hom` read as an identification of the two maps. -/
public theorem classMap_eq_cplxHomologyZeroIso_inv {g : Fin 0 → Γ(X, ⊤)} (G : X.Modules) :
    classMap g G = (cplxHomologyZeroIso G).inv :=
  (Iso.comp_hom_eq_id _).mp (classMap_comp_cplxHomologyZeroIso_hom G)

/-- **With no equations the fraction class is an isomorphism.** -/
public instance isIso_classMap {g : Fin 0 → Γ(X, ⊤)} (G : X.Modules) : IsIso (classMap g G) := by
  rw [classMap_eq_cplxHomologyZeroIso_inv]
  infer_instance

/-- **With no equations the map `(f₁, …, f_c) : ℱ^{⊕c} ⟶ ℱ` vanishes**, its source being an
empty coproduct. -/
public theorem equationsMap_eq_zero {g : Fin 0 → Γ(X, ⊤)} (G : X.Modules) :
    equationsMap g G = 0 :=
  Limits.Sigma.hom_ext _ _ fun i => i.elim0

/-- **With no equations the quotient by the equations is the module itself**, the projection onto
it being an isomorphism because the map quotiented by is zero. -/
public instance isIso_cokernelπ_equationsMap {g : Fin 0 → Γ(X, ⊤)} (G : X.Modules) :
    IsIso (cokernel.π (equationsMap g G)) := by
  rw [equationsMap_eq_zero]
  infer_instance

/-- **With no equations the map of [Stacks, Tag 0G7Q] out of the quotient is an isomorphism**: it
is the canonical identification of `ℱ` with the degree-zero cohomology sheaf of its extended
alternating Čech complex.  Both of its factors are isomorphisms — the projection onto the
quotient by an empty family of equations, and the fraction class with an empty denominator. -/
public theorem isIso_quotientClassMap {g : Fin 0 → Γ(X, ⊤)} (G : X.Modules) :
    IsIso (quotientClassMap g G) :=
  have : IsIso (cokernel.π (equationsMap g G) ≫ quotientClassMap g G) := by
    rw [cokernelπ_comp_quotientClassMap]
    infer_instance
  IsIso.of_isIso_comp_left (cokernel.π (equationsMap g G)) (quotientClassMap g G)

end Class

/-! ### The fraction class with values in the local cohomology sheaf -/

section LocalCohomology

attribute [local instance] HasDerivedCategory.standard

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) (F : X.Modules)

/-- The fraction class in the degree-`c` cohomology sheaf of the extended alternating Čech
complex, transported to the construction
`AlgebraicGeometry.ExtendedAlternatingCech.data` of that complex. -/
public def quotientClassMapData :
    equationsQuotient f F ⟶
      (AlgebraicGeometry.ExtendedAlternatingCech.data f F).complex.homology c :=
  quotientClassMap f F ≫
    HomologicalComplex.homologyMap (Stacks.Perfect.CechComparison.complexIso f F).inv c

/-- **Stacks Project, Tag 0G7Q**, before transposing along the adjunction: the canonical map
`ℱ/(f₁, …, f_c)ℱ ⟶ i_* 𝓗ᶜ_Z(ℱ)` sending the class of a local section `s` to the class of the
fraction `s / (f₁ ⋯ f_c)`, where the degree-`c` local cohomology sheaf on the common zero locus
`Z` of the equations is identified with the cokernel of the last Čech differential. -/
public def pushforwardFractionClass [F.IsQuasicoherent] :
    equationsQuotient f F ⟶
      (modulePushforward (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).obj
        (localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
          (isClosed_equationsClosedSet f) (c : ℤ)
          ((DerivedCategory.singleFunctor X.Modules 0).obj F)) :=
  quotientClassMapData f F ≫
    (Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso f F c).inv

/-- **Stacks Project, Tag 0G7Q.** The canonical map
`c_{f₁, …, f_c} : i^{-1}(ℱ/(f₁, …, f_c)ℱ) ⟶ 𝓗ᶜ_Z(ℱ)`
of `𝒪_X|_Z`-modules on the common zero locus `Z` of `f₁, …, f_c`, for a quasi-coherent
`𝒪_X`-module `ℱ`: it is the transpose, under the adjunction between inverse image and direct
image along the inclusion of `Z`, of the map carrying the class of a local section `s` of `ℱ` to
the class of the fraction `s / (f₁ ⋯ f_c)` in the degree-`c` cohomology sheaf of the extended
alternating Čech complex of the equations, which is the direct image of `𝓗ᶜ_Z(ℱ)`. -/
@[stacks 0G7Q "the canonical map c_{f_1, …, f_c}"]
public def fractionClass [F.IsQuasicoherent] :
    (modulePullback (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f))).obj
        (equationsQuotient f F) ⟶
      localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
        (isClosed_equationsClosedSet f) (c : ℤ)
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) :=
  (homEquiv (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)) _
    (equationsQuotient f F)).symm (pushforwardFractionClass f F)

/-- The fraction class of a residue class, read in the cohomology sheaf of the construction
`AlgebraicGeometry.ExtendedAlternatingCech.data`: the class of a local section `s` goes to the
class of the fraction `s / (f₁ ⋯ f_c)`. -/
public theorem cokernelπ_comp_quotientClassMapData :
    cokernel.π (equationsMap f F) ≫ quotientClassMapData f F =
      classMap f F ≫ HomologicalComplex.homologyMap
        (Stacks.Perfect.CechComparison.complexIso f F).inv c :=
  cokernel.π_desc_assoc _ _ _ _

/-- **Stacks Project, Tag 0G7Q.** The map to the direct image of the local cohomology sheaf is
the fraction class followed by the two identifications: the comparison of the two constructions
of the extended alternating Čech complex, and the identification of the degree-`c` cohomology
sheaf of that complex with the direct image of `𝓗ᶜ_Z(ℱ)`. -/
@[stacks 0G7Q "the fraction class followed by the identifications"]
public theorem pushforwardFractionClass_eq [F.IsQuasicoherent] :
    pushforwardFractionClass f F =
      (quotientClassMap f F ≫ HomologicalComplex.homologyMap
          (Stacks.Perfect.CechComparison.complexIso f F).inv c) ≫
        (Stacks.Perfect.CechLocalCohomology.pushforwardLocalCohomologyIso f F c).inv := rfl

/-- **Stacks Project, Tag 0G7Q.** The map `c_{f₁, …, f_c}` is the transpose of the map from the
quotient `ℱ/(f₁, …, f_c)ℱ` to the direct image of the degree-`c` local cohomology sheaf. -/
@[stacks 0G7Q "c_{f_1, …, f_c} is the transpose of the fraction class"]
public theorem homEquiv_fractionClass [F.IsQuasicoherent] :
    homEquiv (closedSubsetInclusion X.toRingedSpace (equationsClosedSet f)) _
        (equationsQuotient f F) (fractionClass f F) =
      pushforwardFractionClass f F :=
  Equiv.apply_symm_apply _ _

end LocalCohomology

end Stacks.Perfect.FractionClass

end
