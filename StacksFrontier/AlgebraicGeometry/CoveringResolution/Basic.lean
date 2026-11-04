module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CoveringResolution

/-!
# The product coordinates of the Čech resolution (towards Tag 02FU)

`StacksDraft.Ch20.Sec25.Tag02FU` builds the augmented Čech complex
`Stacks.CechTotalComplex.CoveringResolution.coveringComplex` of an open covering `U` of a ringed
  space `(X, R)` with values in
the direct images of the restrictions of a sheaf of modules, and discharges the `complex` and
`hasHomology` fields of `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`. This file
  supplies the four
*coordinate* fields, which identify the sections of the degree-`p` term with the product
`Stacks.CechTotalComplex.CoveringResolution.cechSections` of the sections of `F` over the multiple
  intersections, and names the
differential and the restrictions in those coordinates.

## Main definitions

* `coordFactor X R F V W` is the factor of a Čech term indexed by the open set `W`: the
  sections over `V ⊓ W` of the enlargement of `F`, with scalars restricted from `R(V)`.
  `coordFactorMap` is restriction along a shrinking of `W`, and `coordFactorIso` is the
  isomorphism between the factors of two *equal* index open sets, which is what mediates
  between the two indexings of the intersections (`Stacks.CategoryTheory.CechComplex.inter`
  and `Stacks.CechTotalComplex.CoveringResolution.cechIntersection`).
* `coordπ X R U F p V s` is the `s`-th coordinate of the sections over `V` of the degree-`p`
  term, and `coordFan`/`coordFanIsLimit` exhibit those sections as the product of the
  factors.
* `termIso X R U F p V` is the resulting linear identification of the sections of the
  degree-`p` term with `Stacks.CechTotalComplex.CoveringResolution.cechSections X R U F p V`.
* `coveringResolutionOfAugmentation` assembles a term of
  `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution` from
  an augmentation with its degree-zero formula and the quasi-isomorphism property; every
  other field is supplied here.

## Main results

The four coordinate fields of `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`, in
  the statements of that structure:

* `termIso_restriction`: the coordinates commute with restriction to a smaller open set;
* `termIso_naturality`: a morphism of sheaves of modules acts coordinatewise;
* `differential_field`: Equation 01EE — the differential is, in these coordinates, the
  alternating sum of the restrictions along the face inclusions;
* and `termIso` itself, characterized by `termIso_hom_apply` and `termIso_down`: its `s`-th
  coordinate is the `s`-th Čech projection, followed by the restriction that passes from
  `inter U s` to the structure's `cechIntersection X U p s`.

That characterization is what makes `termIso` more than data: `coordFanIsLimit` says the
coordinates are jointly a product cone, and `termIso_hom_apply` pins each coordinate to the
Čech projection, so no other identification satisfies these statements.

## Implementation notes

The two indexings of a multiple intersection are *propositionally* but not definitionally
equal: `Stacks.CategoryTheory.CechComplex.inter U s` is a categorical product in `Opens X`,
whose `HasLimit` instance goes through `Classical.choice`, while
`Stacks.CechTotalComplex.CoveringResolution.cechIntersection X U p s` is the infimum
  `⨅ k, U (s k)`. They are identified by
`Stacks.CechTotalComplex.CoveringResolution.inter_eq_cechIntersection`. Rather than transport along
  that equality with
`eqToHom`, the factors indexed by the two open sets are identified by the *restriction maps*
both ways (`coordFactorIso`), which have the computational advantage of acting on sections as
`F.val.map` of an inclusion of open sets; every coherence then reduces to `Subsingleton.elim`
in the thin category `Opens X`.

`coordFactor` and `coordPt` are `@[reducible]` on purpose. The Čech machinery states its
degreewise description as a `Fan` over the family `fun s ↦ P.obj (op (inter U s))`, and
matching a `Discrete.functor` applied to an object against a named abbreviation of that
family happens at reducible transparency, so a semireducible definition there fails to
elaborate.

## What is not proved here

Three fields of `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution` remain, and they
  are exactly the hypotheses of
`coveringResolutionOfAugmentation`:

* `augmentation` and `augmentation_f_zero`.
  `Stacks.CechTotalComplex.CoveringResolution.coveringAugmentation` is a map out of
  `Stacks.CechTotalComplex.CoveringResolution.infPushforward X R F (⊤_ (Opens X))`; what the structure
    asks for is a natural
  transformation out of `Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift X R ⋙
    HomologicalComplex.single _ _ 0`,
  so what is owed is an isomorphism between those two sheaves of modules, natural in `F`,
  resting on `Stacks.CategoryTheory.CechComplex.terminal_eq_top`.
* `quasiIso`, the mathematical core. Nothing in this file bears on it, and what the usual
  proof needs is in two halves, of which Mathlib supplies one.

  The half that exists: the augmented Čech object of a *split* covering is contractible.
  `CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech` produces an
  `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy` on
  `U.cech.augmentOfIsTerminal` as soon as there is a morphism `T ⟶ U.obj i₀` from the
  terminal object — which for `Opens X` says `⊤ ≤ U i₀`, i.e. that one member of the covering
  is the whole space. `ExtraDegeneracy.homotopyEquiv` then makes the augmentation a homotopy
  equivalence, hence a quasi-isomorphism. Note that this is stated for the alternating *face*
  map complex of a simplicial object, whereas the Čech cochain complex is the alternating
  *coface* map complex of the cosimplicial object obtained by applying the coefficient
  presheaf; since `ExtraDegeneracy.map` transports only along a covariant functor, using it
  here means passing through the opposite category.

  The half that is missing: a covering is split only after restricting to one of its own
  members, so the argument gives exactness of the augmented complex over each `V ≤ U i₀`, and
  concluding exactness of the complex of sheaves needs a *locality* criterion — a complex of
  sheaves of modules that is exact on a family of open sets covering `X` is exact. In
  the pinned Mathlib there is no `IsLocallyExact`, `isLocallyExact` or
  `locallyExact` anywhere in it, and the one exactness-is-local statement it has,
  `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` in `Mathlib.Topology.Sheaves.Abelian`, is
  about `Sheaf C X` in the `TopCat.Presheaf` sense rather than about `SheafOfModules R` on
  `Opens.grothendieckTopology X`. That criterion is therefore the single missing input, and it
  is a statement about sheaf categories rather than about Čech complexes.

## References

* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
* [Stacks Project, Equation 01EE](https://stacks.math.columbia.edu/tag/01EE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open Stacks.CategoryTheory.CechComplex

universe u v w t uC vC uR vM

namespace Stacks.AlgebraicGeometry.CoveringResolution

open Stacks.CechTotalComplex.CoveringResolution

/-! ### Generalities on sheaves of modules -/

/-- Evaluation on an object of the site is an additive functor on sheaves of modules. -/
instance evaluationAdditive {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{uR}} (Y : Cᵒᵖ) : (SheafOfModules.evaluation.{vM} S Y).Additive where
  map_add := rfl

/-- Evaluation on an object of the site is taking the component of the underlying morphism of
presheaves of modules. -/
theorem evaluation_map_app {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{uR}} (Y : Cᵒᵖ) {M N : SheafOfModules.{vM} S} (m : M ⟶ N) :
    (SheafOfModules.evaluation.{vM} S Y).map m = m.val.app Y := rfl

/-- Composition of morphisms of modules, on an element. -/
theorem moduleCat_comp_apply {S : Type uR} [Ring S] {M N P : ModuleCat.{vM} S} (f : M ⟶ N)
    (g : N ⟶ P) (m : M) : (f ≫ g) m = g (f m) := rfl

/-- An integer multiple of a morphism of modules, on an element. -/
theorem moduleCat_zsmul_apply {S : Type uR} [Ring S] {M N : ModuleCat.{vM} S} (n : ℤ)
    (f : M ⟶ N) (m : M) : (n • f) m = n • f m := rfl

/-- A finite sum of morphisms of modules, on an element. -/
theorem moduleCat_sum_apply {S : Type uR} [Ring S] {M N : ModuleCat.{vM} S} {α : Type*}
    (f : α → (M ⟶ N)) (c : Finset α) (m : M) :
    (∑ j ∈ c, f j) m = ∑ j ∈ c, f j m := by
  simp [ModuleCat.hom_sum, LinearMap.sum_apply]

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
variable {ι : Type t} (U : ι → Opens X)

/-! ### The factors of a Čech term -/

/-- The factor of a Čech term indexed by the open set `W`, as a module over the sections of
`R` on `V`: the sections over `V ⊓ W` of the enlargement of `F`, with scalars restricted
along `R(V) ⟶ R(V ⊓ W)`. This is one factor of
  `Stacks.CechTotalComplex.CoveringResolution.cechSections`. -/
@[reducible] noncomputable def coordFactor (F : SheafOfModules.{w} R) (V W : Opens X) :
    ModuleCat.{max u v w t} (R.obj.obj (op V)) :=
  (SheafOfModules.evaluation.{max u v w t} R (op V)).obj
    ((infPushforwardOpens.{u, v, w, t} X R F).obj (op W))

/-- The sections over `V` of the degree-`p` term of the covering complex. -/
@[reducible] noncomputable def coordPt (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) :
    ModuleCat.{max u v w t} (R.obj.obj (op V)) :=
  (SheafOfModules.evaluation.{max u v w t} R (op V)).obj
    (((cechComplexFunctor U).obj (infPushforwardOpens.{u, v, w, t} X R F)).X p)

/-- Restriction between factors along a shrinking of the index open set. -/
noncomputable def coordFactorMap (F : SheafOfModules.{w} R) (V : Opens X) {W W' : Opens X}
    (h : W ≤ W') : coordFactor.{u, v, w, t} X R F V W' ⟶ coordFactor.{u, v, w, t} X R F V W :=
  (infPushforwardRestriction.{u, v, w, t} X R F h).app (op V)

/-- `coordFactorMap` is the Čech diagram applied to the inclusion of open sets. -/
theorem coordFactorMap_eq (F : SheafOfModules.{w} R) (V : Opens X) {W W' : Opens X}
    (h : W ≤ W') : coordFactorMap.{u, v, w, t} X R F V h =
      ((infPushforwardOpens.{u, v, w, t} X R F).map (homOfLE h).op).val.app (op V) := rfl

/-- `coordFactorMap` is restriction of sections of `F`. -/
theorem coordFactorMap_apply (F : SheafOfModules.{w} R) (V : Opens X) {W W' : Opens X}
    (h : W ≤ W') (x : coordFactor.{u, v, w, t} X R F V W') :
    coordFactorMap.{u, v, w, t} X R F V h x =
      ULift.up (F.val.map (homOfLE (inf_le_inf_left V h)).op x.down) := rfl

/-- Restriction along the identity inclusion is the identity. -/
theorem coordFactorMap_refl (F : SheafOfModules.{w} R) (V W : Opens X) :
    coordFactorMap.{u, v, w, t} X R F V (le_refl W) = 𝟙 _ :=
  congrArg (fun f => PresheafOfModules.Hom.app f (op V))
    (infPushforwardRestriction_refl.{u, v, w, t} X R F W)

/-- Restrictions between factors compose. -/
theorem coordFactorMap_trans (F : SheafOfModules.{w} R) (V : Opens X) {W W' W'' : Opens X}
    (h : W ≤ W') (h' : W' ≤ W'') :
    coordFactorMap.{u, v, w, t} X R F V h' ≫ coordFactorMap.{u, v, w, t} X R F V h =
      coordFactorMap.{u, v, w, t} X R F V (h.trans h') :=
  congrArg (fun f => PresheafOfModules.Hom.app f (op V))
    (infPushforwardRestriction_trans.{u, v, w, t} X R F h h')

/-- Factors indexed by *equal* open sets are isomorphic, by restriction both ways. This is
what mediates between the two indexings of the multiple intersections. -/
noncomputable def coordFactorIso (F : SheafOfModules.{w} R) (V : Opens X) {W W' : Opens X}
    (h : W = W') : coordFactor.{u, v, w, t} X R F V W' ≅ coordFactor.{u, v, w, t} X R F V W where
  hom := coordFactorMap.{u, v, w, t} X R F V h.le
  inv := coordFactorMap.{u, v, w, t} X R F V h.ge
  hom_inv_id := (coordFactorMap_trans.{u, v, w, t} X R F V h.ge h.le).trans
    (coordFactorMap_refl.{u, v, w, t} X R F V W')
  inv_hom_id := (coordFactorMap_trans.{u, v, w, t} X R F V h.le h.ge).trans
    (coordFactorMap_refl.{u, v, w, t} X R F V W)

/-- Two restrictions between the same pair of factors agree, because `Opens X` is thin. -/
theorem restrOpens_eq (F : SheafOfModules.{w} R) (V : Opens X) {W W' : Opens X}
    (g g' : (op W : (Opens X)ᵒᵖ) ⟶ op W') :
    ((infPushforwardOpens.{u, v, w, t} X R F).map g).val.app (op V) =
      ((infPushforwardOpens.{u, v, w, t} X R F).map g').val.app (op V) :=
  congrArg (fun m => (SheafOfModules.Hom.val m).app (op V))
    (congrArg (infPushforwardOpens.{u, v, w, t} X R F).map (Subsingleton.elim g g'))

/-- Restrictions between factors compose, in the Čech-diagram spelling. -/
theorem restrOpens_comp (F : SheafOfModules.{w} R) (V : Opens X) {W₁ W₂ W₃ : Opens X}
    (g₁ : (op W₁ : (Opens X)ᵒᵖ) ⟶ op W₂) (g₂ : (op W₂ : (Opens X)ᵒᵖ) ⟶ op W₃) :
    ((infPushforwardOpens.{u, v, w, t} X R F).map g₁).val.app (op V) ≫
        ((infPushforwardOpens.{u, v, w, t} X R F).map g₂).val.app (op V) =
      ((infPushforwardOpens.{u, v, w, t} X R F).map (g₁ ≫ g₂)).val.app (op V) :=
  congrArg (fun m => (SheafOfModules.Hom.val m).app (op V))
    ((infPushforwardOpens.{u, v, w, t} X R F).map_comp g₁ g₂).symm

/-- Any two composites of restrictions between the same pair of factors agree. -/
theorem restrOpens_eq_comp (F : SheafOfModules.{w} R) (V : Opens X) {W₁ W₂ W₃ W₄ : Opens X}
    (g₁ : (op W₁ : (Opens X)ᵒᵖ) ⟶ op W₂) (g₂ : (op W₂ : (Opens X)ᵒᵖ) ⟶ op W₄)
    (g₃ : (op W₁ : (Opens X)ᵒᵖ) ⟶ op W₃) (g₄ : (op W₃ : (Opens X)ᵒᵖ) ⟶ op W₄) :
    ((infPushforwardOpens.{u, v, w, t} X R F).map g₁).val.app (op V) ≫
        ((infPushforwardOpens.{u, v, w, t} X R F).map g₂).val.app (op V) =
      ((infPushforwardOpens.{u, v, w, t} X R F).map g₃).val.app (op V) ≫
        ((infPushforwardOpens.{u, v, w, t} X R F).map g₄).val.app (op V) :=
  ((restrOpens_comp.{u, v, w, t} X R F V g₁ g₂).trans
      (restrOpens_eq.{u, v, w, t} X R F V (g₁ ≫ g₂) (g₃ ≫ g₄))).trans
    (restrOpens_comp.{u, v, w, t} X R F V g₃ g₄).symm

/-- Restriction in the open set on which sections are taken, on one factor. -/
theorem coordFactor_map_apply (F : SheafOfModules.{w} R) (W₀ : Opens X) {V W : Opens X}
    (h : W ≤ V) (y : coordFactor.{u, v, w, t} X R F V W₀) :
    ((infPushforwardOpens.{u, v, w, t} X R F).obj (op W₀)).val.map (homOfLE h).op y =
      ULift.up (F.val.map (homOfLE (inf_le_inf_right W₀ h)).op y.down) := rfl

/-! ### The product coordinates of a Čech term -/

/-- The `s`-th coordinate of the sections over `V` of the degree-`p` term: the `s`-th Čech
projection, followed by the restriction from `inter U s` to `cechIntersection X U p s`. -/
noncomputable def coordπ (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X)
    (s : Fin (p + 1) → ι) :
    coordPt.{u, v, w, t} X R U F p V ⟶
      coordFactor.{u, v, w, t} X R F V (cechIntersection X U p s) :=
  (SheafOfModules.evaluation.{max u v w t} R (op V)).map
      (π U (infPushforwardOpens.{u, v, w, t} X R F) p s) ≫
    (coordFactorIso.{u, v, w, t} X R F V (inter_eq_cechIntersection X U p s).symm).hom

/-- `coordπ` unfolded: the Čech projection followed by `coordFactorMap`. -/
theorem coordπ_eq (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) (s : Fin (p + 1) → ι) :
    coordπ.{u, v, w, t} X R U F p V s =
      (SheafOfModules.evaluation.{max u v w t} R (op V)).map
          (π U (infPushforwardOpens.{u, v, w, t} X R F) p s) ≫
        coordFactorMap.{u, v, w, t} X R F V (inter_eq_cechIntersection X U p s).ge := rfl

/-- `coordπ`, elementwise. -/
theorem coordπ_apply (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) (s : Fin (p + 1) → ι)
    (x : coordPt.{u, v, w, t} X R U F p V) :
    coordπ.{u, v, w, t} X R U F p V s x =
      ULift.up (F.val.map
        (homOfLE (inf_le_inf_left V (inter_eq_cechIntersection X U p s).ge)).op
          (((π U (infPushforwardOpens.{u, v, w, t} X R F) p s).val.app (op V) x).down)) := rfl

/-- The fan exhibiting the sections over `V` of the degree-`p` term as the product of the
factors indexed by the `(p+1)`-tuples of members of the covering. -/
noncomputable def coordFan (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) :
    Fan (fun s : Fin (p + 1) → ι =>
      coordFactor.{u, v, w, t} X R F V (cechIntersection X U p s)) :=
  (Cone.postcompose (Discrete.natIso (fun j => coordFactorIso.{u, v, w, t} X R F V
      (inter_eq_cechIntersection X U p j.as).symm)).hom).obj
    (Fan.mk (coordPt.{u, v, w, t} X R U F p V)
      (fun s => (SheafOfModules.evaluation.{max u v w t} R (op V)).map
        (π U (infPushforwardOpens.{u, v, w, t} X R F) p s)))

/-- The vertex of `coordFan` is the sections of the degree-`p` term. -/
theorem coordFan_pt (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) :
    (coordFan.{u, v, w, t} X R U F p V).pt = coordPt.{u, v, w, t} X R U F p V := rfl

/-- The projections of `coordFan` are the coordinates `coordπ`. -/
theorem coordFan_π (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) (s : Fin (p + 1) → ι) :
    (coordFan.{u, v, w, t} X R U F p V).π.app ⟨s⟩ = coordπ.{u, v, w, t} X R U F p V s := rfl

/-- **The sections over `V` of the degree-`p` term are the product of the factors**, with
`coordπ` as the projections. This is what the evaluation functor preserving limits buys. -/
noncomputable def coordFanIsLimit (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) :
    IsLimit (coordFan.{u, v, w, t} X R U F p V) :=
  (IsLimit.postcomposeHomEquiv _ _).symm
    (isLimitFanMkObjOfIsLimit (SheafOfModules.evaluation.{max u v w t} R (op V)) _
      (π U (infPushforwardOpens.{u, v, w, t} X R F) p) (isLimitFan U _ p))

/-- **The `termIso` field of `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`.** The
  sections over `V` of the
degree-`p` term of the covering complex, identified with the product
`Stacks.CechTotalComplex.CoveringResolution.cechSections X R U F p V` of the sections of `F` over
  the intersections
`V ⊓ cechIntersection X U p s`. -/
noncomputable def termIso (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) :
    (((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.obj (op V) ≅
      cechSections.{u, v, w, t} X R U F p V :=
  IsLimit.conePointUniqueUpToIso (coordFanIsLimit.{u, v, w, t} X R U F p V)
    (ModuleCat.productConeIsLimit.{v, t, max u v w t}
      (fun s : Fin (p + 1) → ι => coordFactor.{u, v, w, t} X R F V (cechIntersection X U p s)))

/-- **`termIso` is the Čech projections.** Its `s`-th coordinate is `coordπ`, so no other
identification satisfies the statements below. -/
theorem termIso_hom_apply (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X)
    (x : (((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.obj (op V))
    (s : Fin (p + 1) → ι) :
    (termIso.{u, v, w, t} X R U F p V).hom x s = coordπ.{u, v, w, t} X R U F p V s x :=
  ConcreteCategory.congr_hom
    (IsLimit.conePointUniqueUpToIso_hom_comp (coordFanIsLimit.{u, v, w, t} X R U F p V)
      (ModuleCat.productConeIsLimit.{v, t, max u v w t} _) ⟨s⟩) x

/-- A coordinate of `termIso` as an element of `ULift`, in terms of the Čech projection. -/
private theorem termIso_hom_eq (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X)
    (x : (((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.obj (op V))
    (s : Fin (p + 1) → ι) :
    (termIso.{u, v, w, t} X R U F p V).hom x s =
      ULift.up (F.val.map
        (homOfLE (inf_le_inf_left V (inter_eq_cechIntersection X U p s).ge)).op
          (((π U (infPushforwardOpens.{u, v, w, t} X R F) p s).val.app (op V) x).down)) :=
  (termIso_hom_apply.{u, v, w, t} X R U F p V x s).trans
    (coordπ_apply.{u, v, w, t} X R U F p V s x)

/-- The coordinates of `termIso`, as sections of `F` on the multiple intersections. -/
theorem termIso_down (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X)
    (x : (((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.obj (op V))
    (s : Fin (p + 1) → ι) :
    ((termIso.{u, v, w, t} X R U F p V).hom x s).down =
      F.val.map (homOfLE (inf_le_inf_left V (inter_eq_cechIntersection X U p s).ge)).op
        (((π U (infPushforwardOpens.{u, v, w, t} X R F) p s).val.app (op V) x).down) :=
  congrArg ULift.down (termIso_hom_eq.{u, v, w, t} X R U F p V x s)

/-! ### The coordinate fields of the covering-resolution structure -/

/-- **The `termIso_restriction` field of
  `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`.** The product
coordinates commute with restriction to a smaller open set. -/
theorem termIso_restriction (F : SheafOfModules.{w} R) (p : ℕ) {V W : Opens X} (h : W ≤ V)
    (x : (((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.obj (op V))
    (s : Fin (p + 1) → ι) :
    (termIso.{u, v, w, t} X R U F p W).hom
        ((((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.map (homOfLE h).op x) s =
      ULift.up (F.val.map (homOfLE (inf_le_inf_right (cechIntersection X U p s) h)).op
        (((termIso.{u, v, w, t} X R U F p V).hom x s).down)) := by
  refine (termIso_hom_eq.{u, v, w, t} X R U F p W _ s).trans (congrArg ULift.up ?_)
  have hL : ((π U (infPushforwardOpens.{u, v, w, t} X R F) p s).val.app (op W)
        ((((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.map (homOfLE h).op x)).down =
      F.val.map (homOfLE (inf_le_inf_right (inter U s) h)).op
        (((π U (infPushforwardOpens.{u, v, w, t} X R F) p s).val.app (op V) x).down) :=
    congrArg ULift.down (PresheafOfModules.naturality_apply
      (π U (infPushforwardOpens.{u, v, w, t} X R F) p s).val (homOfLE h).op x)
  have key : ∀ a : F.val.obj (op (V ⊓ inter U s)),
      F.val.map (homOfLE (inf_le_inf_left W (inter_eq_cechIntersection X U p s).ge)).op
          (F.val.map (homOfLE (inf_le_inf_right (inter U s) h)).op a) =
        F.val.map (homOfLE (inf_le_inf_right (cechIntersection X U p s) h)).op
          (F.val.map (homOfLE (inf_le_inf_left V
            (inter_eq_cechIntersection X U p s).ge)).op a) := fun a => by
    rw [← F.val.map_comp_apply, ← F.val.map_comp_apply]
    exact F.val.congr_map_apply (Subsingleton.elim _ _) _
  rw [hL, termIso_down.{u, v, w, t} X R U F p V x s]
  exact key _

/-- The Čech projections are natural in the coefficient presheaf. -/
theorem map_f_comp_π {P Q : (Opens X)ᵒᵖ ⥤ SheafOfModules.{max u v w t} R} (ψ : P ⟶ Q) (n : ℕ)
    (y : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).map ψ).f n ≫ π U Q n y =
      π U P n y ≫ ψ.app (op (inter U y)) :=
  Pi.map_π (fun x : Fin (n + 1) → ι => ψ.app (op (inter U x))) y

/-- **The `termIso_naturality` field of
  `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`.** A morphism of
sheaves of modules acts on the product by its maps on sections. -/
theorem termIso_naturality {F G : SheafOfModules.{w} R} (φ : F ⟶ G) (p : ℕ) (V : Opens X)
    (x : (((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.obj (op V))
    (s : Fin (p + 1) → ι) :
    (termIso.{u, v, w, t} X R U G p V).hom
        ((((coveringComplex.{u, v, w, t} X R U).map φ).f p).val.app (op V) x) s =
      ULift.up (φ.val.app (op (V ⊓ cechIntersection X U p s))
        (((termIso.{u, v, w, t} X R U F p V).hom x s).down)) := by
  refine (termIso_hom_eq.{u, v, w, t} X R U G p V _ s).trans (congrArg ULift.up ?_)
  have hL : ((π U (infPushforwardOpens.{u, v, w, t} X R G) p s).val.app (op V)
        ((((coveringComplex.{u, v, w, t} X R U).map φ).f p).val.app (op V) x)).down =
      φ.val.app (op (V ⊓ inter U s))
        (((π U (infPushforwardOpens.{u, v, w, t} X R F) p s).val.app (op V) x).down) :=
    congrArg ULift.down (ConcreteCategory.congr_hom
      (congrArg (fun m => (SheafOfModules.Hom.val m).app (op V))
        (map_f_comp_π.{u, v, w, t} X R U ((cechDiagram.{u, v, w, t} X R).map φ) p s)) x)
  rw [hL, termIso_down.{u, v, w, t} X R U F p V x s]
  exact (PresheafOfModules.naturality_apply φ.val
    (homOfLE (inf_le_inf_left V (inter_eq_cechIntersection X U p s).ge)).op _).symm

/-- The degree `p+1` intersection is contained in the degree `p` intersection with the `j`-th
index omitted. This is the inequality underlying
  `Stacks.CechTotalComplex.CoveringResolution.cechFaceInclusion`. -/
theorem cechIntersection_le_succAbove (p : ℕ) (s : Fin (p + 2) → ι) (j : Fin (p + 2)) :
    cechIntersection X U (p + 1) s ≤ cechIntersection X U p (s ∘ j.succAbove) :=
  le_iInf fun k => iInf_le (fun a => U (s a)) (j.succAbove k)

/-- **Equation 01EE in the product coordinates, as an identity of morphisms.** -/
theorem coordπ_d (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X) (s : Fin (p + 2) → ι) :
    (SheafOfModules.evaluation.{max u v w t} R (op V)).map
          (((cechComplexFunctor U).obj
            (infPushforwardOpens.{u, v, w, t} X R F)).d p (p + 1)) ≫
        coordπ.{u, v, w, t} X R U F (p + 1) V s =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (coordπ.{u, v, w, t} X R U F p V (s ∘ j.succAbove) ≫
          coordFactorMap.{u, v, w, t} X R F V (cechIntersection_le_succAbove X U p s j)) := by
  rw [coordπ_eq, ← Category.assoc, ← Functor.map_comp,
    d_comp_π U (infPushforwardOpens.{u, v, w, t} X R F) p s, Functor.map_sum,
    Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Functor.map_zsmul, Preadditive.zsmul_comp, Functor.map_comp, Category.assoc, coordπ_eq,
    Category.assoc]
  refine congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) •
    ((SheafOfModules.evaluation.{max u v w t} R (op V)).map
      (π U (infPushforwardOpens.{u, v, w, t} X R F) p (s ∘ j.succAbove)) ≫ z)) ?_
  rw [coordFactorMap_eq, coordFactorMap_eq, coordFactorMap_eq, evaluation_map_app]
  exact restrOpens_eq_comp.{u, v, w, t} X R F V _ _ _ _

/-- **Equation 01EE in the product coordinates, elementwise.** -/
theorem coordπ_d_apply (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X)
    (s : Fin (p + 2) → ι) (x : coordPt.{u, v, w, t} X R U F p V) :
    coordπ.{u, v, w, t} X R U F (p + 1) V s
        ((SheafOfModules.evaluation.{max u v w t} R (op V)).map
          (((cechComplexFunctor U).obj
            (infPushforwardOpens.{u, v, w, t} X R F)).d p (p + 1)) x) =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        coordFactorMap.{u, v, w, t} X R F V (cechIntersection_le_succAbove X U p s j)
          (coordπ.{u, v, w, t} X R U F p V (s ∘ j.succAbove) x) := by
  have h := ConcreteCategory.congr_hom (coordπ_d.{u, v, w, t} X R U F p V s) x
  simpa only [moduleCat_comp_apply, moduleCat_sum_apply, moduleCat_zsmul_apply] using h

/-- **The `differential` field of
  `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`.** Equation 01EE: in the
product coordinates the differential is the alternating sum of the restrictions along the
face inclusions. -/
theorem differential_field (F : SheafOfModules.{w} R) (p : ℕ) (V : Opens X)
    (x : (((coveringComplex.{u, v, w, t} X R U).obj F).X p).val.obj (op V))
    (s : Fin (p + 2) → ι) :
    (termIso.{u, v, w, t} X R U F (p + 1) V).hom
        ((((coveringComplex.{u, v, w, t} X R U).obj F).d p (p + 1)).val.app (op V) x) s =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        ULift.up (F.val.map (cechFaceInclusion X U p s j V).op
          (((termIso.{u, v, w, t} X R U F p V).hom x (s ∘ j.succAbove)).down)) := by
  refine (termIso_hom_apply.{u, v, w, t} X R U F (p + 1) V _ s).trans ?_
  refine (coordπ_d_apply.{u, v, w, t} X R U F p V s x).trans ?_
  exact Finset.sum_congr rfl fun j _ => by rw [termIso_hom_apply]; rfl

/-! ### Assembling the covering-resolution structure -/

/-- **Six of the nine fields of `Stacks.CechTotalComplex.CoveringResolution.CoveringResolution`,
  discharged.** The `complex`
field is `Stacks.CechTotalComplex.CoveringResolution.coveringComplex`, the four coordinate fields
  are the theorems above, and
`hasHomology` is `Stacks.CechTotalComplex.CoveringResolution.hasHomology_of_enlarged`. What is left
  as a hypothesis is exactly
the augmentation — as a natural transformation out of the single complex, together with its
degree-zero formula — and the quasi-isomorphism property. -/
noncomputable def coveringResolutionOfAugmentation
    (aug : moduleUniverseLift.{u, v, w, t} X R ⋙
        HomologicalComplex.single (SheafOfModules.{max u v w t} R) (ComplexShape.up ℕ) 0 ⟶
      coveringComplex.{u, v, w, t} X R U)
    (haug : ∀ (F : SheafOfModules.{w} R) (V : Opens X)
      (x : (((moduleUniverseLift.{u, v, w, t} X R ⋙ HomologicalComplex.single
        (SheafOfModules.{max u v w t} R) (ComplexShape.up ℕ) 0).obj F).X 0).val.obj (op V))
      (s : Fin 1 → ι),
      (termIso.{u, v, w, t} X R U F 0 V).hom (((aug.app F).f 0).val.app (op V) x) s =
        ULift.up (F.val.map (homOfLE inf_le_left :
          V ⊓ cechIntersection X U 0 s ⟶ V).op
          (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            ((moduleUniverseLift.{u, v, w, t} X R).obj F)).hom.val.app (op V) x).down)))
    (hqi : ∀ F : SheafOfModules.{w} R,
      haveI : ∀ q : ℕ, ((coveringComplex.{u, v, w, t} X R U).obj F).HasHomology q :=
        fun q => hasHomology_of_enlarged.{u, v, max w t} X R _ q
      QuasiIso (aug.app F)) :
    CoveringResolution.{u, v, w, t} X R U where
  complex := coveringComplex.{u, v, w, t} X R U
  augmentation := aug
  termIso := termIso.{u, v, w, t} X R U
  termIso_restriction := termIso_restriction.{u, v, w, t} X R U
  termIso_naturality := termIso_naturality.{u, v, w, t} X R U
  differential := differential_field.{u, v, w, t} X R U
  augmentation_f_zero := haug
  hasHomology _F q := hasHomology_of_enlarged.{u, v, max w t} X R _ q
  quasiIso := hqi

end Stacks.AlgebraicGeometry.CoveringResolution
