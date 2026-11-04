module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.ZeroSchemeSliceUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspaceGeneralPullback

/-!
# An étale chart of the base change of a zero locus is the zero scheme of the pulled-back functions

Let `g : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site, let `f₁, …, f_r ∈ Γ(Y, 𝒪_Y)` and let `V(f₁, …, f_r) ⊆ Y` be the closed subspace they cut
out, `AlgebraicGeometry.Space.vanishingSubfunctor`.  This file identifies an étale chart of
`g⁻¹ V(f₁, …, f_r)` with a **scheme-theoretic zero scheme**: if `W` is an affine étale chart of
`X` which maps over `g` to an étale chart `U` of `Y` by a morphism `p` of the site, then the
chart of the inverse image obtained by base changing `W` along the closed immersion is, over
`W`, the closed subscheme

`V(p^*f₁|_U, …, p^*f_r|_U) ⊆ W`

cut out by the pullbacks along `p` of the values of the functions on `U`; and the closed
immersion it carries into `W` is unramified over the spectrum of a field as soon as the germs of
those pullbacks generate the maximal ideal, the vanishing hypothesis of the criterion of
**Stacks 02GF** being discharged by the identification itself.

This is the residue of the chart construction of **Stacks 06N3** named in the implementation
notes of `StacksFrontier/AlgebraicGeometry/Stacks/ChartShrinkingOpenSubspace.lean`: with the fibre
`F = U ×_𝒳 Spec k` and the **Stacks 06MD** slice `V(f₁, …, f_r)` of `U`, the fibre of the slice
over `Spec k` is `g⁻¹ V(f₁, …, f_r) ⊆ F` for `g : F ⟶ U` the projection of **Stacks 04SW**, and
an étale chart of it is the zero scheme of the pulled-back slicing sequence inside an affine
étale chart of `F`.  The two compatibilities this needs of
`AlgebraicGeometry.Space.vanishingSubfunctor` divide as follows.  Base change is proved with no
hypothesis on `g`: `AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage`
says `V(g^*f₁, …, g^*f_r) = g⁻¹ V(f₁, …, f_r)`, and
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_chartBaseChange` carries that to the
algebraic space representing the 2-fibre product of the zero-locus stack, so the fibre of the
slice *is* `V(g^*f₁, …, g^*f_r)`.  Passage to an étale chart is what this file adds: the
functions `g^*f_i` read on the chart `W` are the pullbacks `p^*f_i|_U` by
`AlgebraicGeometry.Space.globalFunctionsMap_val_of_factor`, and the chart of the closed subspace
is the zero scheme they cut out.

## Main results

* `AlgebraicGeometry.Space.appTop_chartBaseChangeHom_eq_zero_of_mem_definingIdealAt` and
  `AlgebraicGeometry.Space.stalkMap_germ_chartBaseChangeHom_eq_zero_of_mem_definingIdealAt`: a
  global regular function on an étale chart `W` of `X` lying in the defining ideal of a closed
  subspace `Z ⊆ X` pulls back to zero on the chart `Z ×_X W`, globally and in the local ring at
  any point of it — the vanishing hypothesis of the criterion of **Stacks 02GF**, with no
  hypothesis on the chart.
* `AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_comp_over_field`: **the criterion of
  Stacks 02GF at an étale chart of a closed subspace**, with the vanishing hypothesis
  discharged: for functions in the defining ideal whose germs generate the maximal ideal at a
  point and a finite separable residue field extension, the composite `Z ×_X W ⟶ W ⟶ Spec k` is
  unramified there.
* `AlgebraicGeometry.Space.exists_iso_zeroScheme_chartBaseChange_of_definingIdealAt_eq`: the
  chart `Z ×_X W` of an affine étale chart **is** the closed subscheme of `W` cut out by any
  ideal equal to the defining ideal of `Z` at `W`.
* `AlgebraicGeometry.Space.mem_definingIdealAt_vanishingSubspace`: for `Z = V(c₁, …, c_r)` the
  values of the functions lie in that ideal.
* `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList`:
  **passage to an étale chart, at the base change of a zero locus.** The defining ideal of
  `V(g^*f₁, …, g^*f_r)` at an affine étale chart `W` of `X` lying over an étale chart `U` of `Y`
  is the ideal of the pullbacks `p^*f₁|_U, …, p^*f_r|_U`.  Affineness of `U` is not needed.
* `AlgebraicGeometry.Space.exists_iso_zeroScheme_chartBaseChange_globalFunctionsMap`: hence
  **the étale chart of the base change of the zero locus is the zero scheme
  `V(p^*f₁|_U, …, p^*f_r|_U)`** inside the affine étale chart `W`.
* `AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field`
  and `AlgebraicGeometry.Space.unramifiedAt_of_eq_chartBaseChangeHom_globalFunctionsMap_comp`:
  that chart is unramified over `Spec k` at a point where the germs of the pullbacks generate
  the maximal ideal — the second with the composite supplied as a morphism of its own, so that a
  consumer whose morphism carries the `AlgebraicGeometry.LocallyOfFiniteType` instance can hand
  it over and substitute.

## Implementation notes

The chart of the closed subspace is `AlgebraicGeometry.Space.chartBaseChangeHom`, the base change
of the closed immersion along the chart taken through the representability datum the immersion
carries, so no fibre product of presheaves is formed and the source of the closed immersion is a
scheme of the site on the nose.  That is what lets the statements below phrase the slice as the
zero scheme **definitionally**, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/CohenMacaulaySlice/ZeroSchemeSliceUnramified.lean`
require: no hypothesis of the form `Z = V(c)` with `Z` a scheme occurs, and the point of the
slice is a point of the source of `AlgebraicGeometry.Space.chartBaseChangeHom` rather than a
point transported along an isomorphism.

For the same reason the criterion of **Stacks 02GF** is applied in the form
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field`, which
takes an arbitrary preimmersion, rather than in the form
`Stacks.AlgebraicGeometry.unramifiedAt_subschemeι_comp_of_ofList_germ_eq_maximalIdeal_over_field`,
which is stated at `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`: the two differ by the
isomorphism of
`AlgebraicGeometry.Space.exists_iso_zeroScheme_chartBaseChange_of_definingIdealAt_eq`, and
transporting unramifiedness across it would be exactly the dependent transport that design rule
forbids.  The isomorphism is still recorded, since "the chart *is* the zero scheme" is what the
source asserts; it is the membership statement, not the isomorphism, that the unramifiedness
statements use, and membership needs no affineness at all.

The vanishing is read off `AlgebraicGeometry.Space.definingIdealAt_eq_ker`, which identifies the
defining ideal of a closed subspace at a chart with the kernel of pullback of global regular
functions along exactly that closed immersion and holds with no hypothesis.  Affineness of the
chart of `X` enters only through
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq'`, where the defining ideal of
`V(c₁, …, c_r)` is identified with the ideal generated by the values.  Affineness of the chart
of `Y` is never used: the only thing read off the chart `U` upstairs is the value of a global
function on it, and `AlgebraicGeometry.Space.globalFunctionsMap_val_of_factor` computes the
pullback of that value with no hypothesis on either chart.  So the étale chart of `Y` through
which the slicing sequence is read may be the identity chart of a representing object, which is
how `AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`
delivers the sequence of **Stacks 06N3**.

The ideal is written `Ideal.ofList (List.ofFn _)`, the form in which the scheme-level slicing
lemma **Stacks 06LI** and the criterion of **Stacks 02GF** both phrase it.

No `@[stacks]` attribute is claimed: this is a step of the proof of **Stacks 06N3**, which is no
tag of its own, and whose registration sits on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Section 06LV](https://stacks.math.columbia.edu/tag/06LV)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The functions of the defining ideal pull back to zero on the chart -/

/-- **A global regular function on an étale chart lying in the defining ideal of a closed
subspace pulls back to zero on the chart of that subspace**, with no hypothesis on the chart.
The defining ideal is the kernel of pullback of global regular functions along the base changed
closed immersion, `AlgebraicGeometry.Space.definingIdealAt_eq_ker`. -/
theorem appTop_chartBaseChangeHom_eq_zero_of_mem_definingIdealAt
    (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    {s : Γ(chartScheme W, ⊤)} (hs : s ∈ definingIdealAt B S hS X Z (op W)) :
    (chartBaseChangeHom B S hS X Z W).appTop s = 0 := by
  change (chartBaseChangeHom B S hS X Z W).appTop.hom s = 0
  rw [definingIdealAt_eq_ker B S hS X Z W] at hs
  exact RingHom.mem_ker.mp hs

/-- **The germ of such a function pulls back to zero in the local ring at any point of the chart
of the subspace.**  This is the vanishing hypothesis of the criterion of **Stacks 02GF** at that
chart: the function pulls back to zero globally by
`AlgebraicGeometry.Space.appTop_chartBaseChangeHom_eq_zero_of_mem_definingIdealAt`, and the stalk
map carries the germ of a function to the germ of its pullback. -/
theorem stalkMap_germ_chartBaseChangeHom_eq_zero_of_mem_definingIdealAt
    (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    (z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom))
    {s : Γ(chartScheme W, ⊤)} (hs : s ∈ definingIdealAt B S hS X Z (op W)) :
    ((chartBaseChangeHom B S hS X Z W).stalkMap z).hom
        ((chartScheme W).presheaf.germ ⊤
          (chartBaseChangeHom B S hS X Z W z) trivial s) = 0 := by
  rw [← _root_.Stacks.AlgebraicGeometry.germ_appTop_eq_stalkMap_germ
      (chartBaseChangeHom B S hS X Z W) z s,
    appTop_chartBaseChangeHom_eq_zero_of_mem_definingIdealAt B S hS Z W hs]
  exact map_zero _

/-! ### Unramifiedness of the chart over the spectrum of a field -/

/-- **The criterion of Stacks 02GF at an étale chart of a closed subspace, with the vanishing
hypothesis discharged.**  Let `Z ⊆ X` be a closed subspace, let `W` be an étale chart of `X`
with a morphism of schemes `π : W ⟶ Spec k`, and let `z` be a point of the chart `Z ×_X W`.  If
`s₁, …, s_r` are global regular functions on `W` lying in the defining ideal of `Z` at `W` whose
germs generate the maximal ideal of `𝒪_{W, w}`, `w` the image of `z`, and if `κ(w)` is finite
separable over the residue field of `Spec k`, then the composite `Z ×_X W ⟶ W ⟶ Spec k` is
unramified at `z`.

This is `Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field`
fed with `AlgebraicGeometry.Space.stalkMap_germ_chartBaseChangeHom_eq_zero_of_mem_definingIdealAt`:
functions in the defining ideal pull back to zero on the chart of the subspace, so the
generation of `𝔪_w` by their germs is by itself enough.  The preimmersion the criterion asks for
is the base changed closed immersion itself, so no point and no morphism is transported. -/
theorem unramifiedAt_chartBaseChangeHom_comp_over_field {k : Type u} [Field k]
    (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    (π : chartScheme W ⟶ Spec (.of k))
    [LocallyOfFiniteType (chartBaseChangeHom B S hS X Z W ≫ π)]
    (z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom))
    {r : ℕ} (s : Fin r → Γ(chartScheme W, ⊤))
    (hs : ∀ i, s i ∈ definingIdealAt B S hS X Z (op W))
    (hgen : Ideal.ofList (List.ofFn fun i => (chartScheme W).presheaf.germ ⊤
          (chartBaseChangeHom B S hS X Z W z) trivial (s i)) =
      maximalIdeal ((chartScheme W).presheaf.stalk (chartBaseChangeHom B S hS X Z W z)))
    (hsep : letI := (π.residueFieldMap (chartBaseChangeHom B S hS X Z W z)).hom.toAlgebra
      Module.Finite ((Spec (.of k)).residueField (π (chartBaseChangeHom B S hS X Z W z)))
          ((chartScheme W).residueField (chartBaseChangeHom B S hS X Z W z)) ∧
        Algebra.IsSeparable
          ((Spec (.of k)).residueField (π (chartBaseChangeHom B S hS X Z W z)))
          ((chartScheme W).residueField (chartBaseChangeHom B S hS X Z W z))) :
    UnramifiedAt (chartBaseChangeHom B S hS X Z W ≫ π) z :=
  _root_.Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field
    (chartBaseChangeHom B S hS X Z W) π z
    (fun i => (chartScheme W).presheaf.germ ⊤
      (chartBaseChangeHom B S hS X Z W z) trivial (s i))
    (fun i => stalkMap_germ_chartBaseChangeHom_eq_zero_of_mem_definingIdealAt B S hS Z W z
      (hs i))
    hgen hsep

/-! ### The chart of a closed subspace as a scheme-theoretic zero scheme -/

/-- **The base change of a closed subspace along an affine étale chart is the closed subscheme
cut out by any ideal equal to the defining ideal at that chart.**  The ideal is taken as a
parameter together with the equality, rather than being the defining ideal itself, so that a
consumer which knows it under another name — the ideal of a slicing sequence — gets the
identification onto that name with no transport of a dependent type. -/
theorem exists_iso_zeroScheme_chartBaseChange_of_definingIdealAt_eq
    (Z : ClosedSubspaces B S hS X.1) (W : SmallEtale B S hS X.1)
    (hW : IsAffine (chartScheme W)) (I : Ideal Γ(chartScheme W, ⊤))
    (hI : definingIdealAt B S hS X Z (op W) = I) :
    ∃ e : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom) ≅
        (Scheme.IdealSheafData.ofIdealTop I).subscheme,
      e.hom ≫ (Scheme.IdealSheafData.ofIdealTop I).subschemeι =
        chartBaseChangeHom B S hS X Z W := by
  subst hI
  exact exists_iso_subscheme_ofIdealTop_definingIdealAt B S hS X Z W hW

/-! ### The zero locus of a family of global functions -/

/-- **The value of one of the functions cutting out `V(c₁, …, c_r)` on an affine étale chart lies
in the defining ideal of `V(c₁, …, c_r)` at that chart.**  The defining ideal there is the ideal
generated by all of the values, `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq'`. -/
theorem mem_definingIdealAt_vanishingSubspace {r : ℕ}
    (c : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS X)).sections)
    (W : SmallEtale B S hS X.1) (hW : IsAffine (chartScheme W)) (i : Fin r) :
    unitSectionValue B S hS X (c i) (op W) ∈
      definingIdealAt B S hS X (vanishingSubspace B S hS X c) (op W) := by
  rw [definingIdealAt_vanishingSubspace_eq' B S hS X c W hW]
  exact Ideal.subset_span (Set.mem_range_self i)

/-- **Passage to an étale chart, at the base change of a zero locus.**  Let `g : X ⟶ Y` be a
morphism of algebraic spaces over `S` — with no hypothesis whatever — let
`f₁, …, f_r ∈ Γ(Y, 𝒪_Y)`, let `U` be an étale chart of `Y`, let `W` be an **affine** étale chart
of `X` and let `p : W ⟶ U` be a morphism of the site over `g`.  Then the defining ideal of
`V(g^*f₁, …, g^*f_r)` at `W` is the ideal generated by the pullbacks along `p` of the values of
the functions on `U`:

`definingIdealAt V(g^*f₁, …, g^*f_r) W = (p^*f₁|_U, …, p^*f_r|_U)`.

The two inputs are `AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_eq'`, which
identifies the defining ideal with the ideal of the restricted functions and is where affineness
of `W` enters, and `AlgebraicGeometry.Space.globalFunctionsMap_val_of_factor`, which names each
restricted function as the pullback along `p` with no hypothesis on either chart. -/
theorem definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList (g : X ⟶ Y) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Y)).sections)
    (U : SmallEtale B S hS Y.1) (W : SmallEtale B S hS X.1) (p : W.1.left ⟶ U.1.left)
    (hp : yoneda.map p ≫ U.1.hom = W.1.hom ≫ g.hom) (hW : IsAffine (chartScheme W)) :
    definingIdealAt B S hS X
        (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) (op W) =
      (Ideal.ofList (List.ofFn fun i =>
        ((BigFppfOver.toScheme B S hS).map p).appTop.hom ((f i).eval (op U))) :
          Ideal Γ(chartScheme W, ⊤)) := by
  rw [definingIdealAt_vanishingSubspace_eq' B S hS X
    (fun i => globalFunctionsMap B S hS g (f i)) W hW]
  refine Eq.trans ?_ (Ideal.ofList_ofFn _).symm
  exact congrArg Ideal.span (congrArg Set.range
    (funext fun i => globalFunctionsMap_val_of_factor B S hS g (f i) U W p hp))

/-- **An étale chart of the base change of `V(f₁, …, f_r)` along an arbitrary morphism of
algebraic spaces is the zero scheme of the pulled-back functions.**  In the situation of
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList`, the
base change along `W` of `V(g^*f₁, …, g^*f_r) = g⁻¹ V(f₁, …, f_r)` is, as a closed subscheme of
`W`, the scheme-theoretic zero scheme

`V(p^*f₁|_U, …, p^*f_r|_U) ⊆ W`.

This is the identification the chart construction of **Stacks 06N3** needs of the fibre of the
**Stacks 06MD** slice: the closed subspace being base changed is the fibre of the slice, by
`AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage` and
`AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_chartBaseChange`, and the chart of it is
the zero scheme of the pulled-back slicing sequence. -/
theorem exists_iso_zeroScheme_chartBaseChange_globalFunctionsMap (g : X ⟶ Y) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Y)).sections)
    (U : SmallEtale B S hS Y.1) (W : SmallEtale B S hS X.1) (p : W.1.left ⟶ U.1.left)
    (hp : yoneda.map p ≫ U.1.hom = W.1.hom ≫ g.hom) (hW : IsAffine (chartScheme W)) :
    ∃ e : (BigFppfOver.toScheme B S hS).obj
          ((vanishingSubspace B S hS X fun i =>
            globalFunctionsMap B S hS g (f i)).2.2.rep.pullback W.1.hom) ≅
        (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn fun i =>
          ((BigFppfOver.toScheme B S hS).map p).appTop.hom ((f i).eval (op U))))).subscheme,
      e.hom ≫ (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn fun i =>
            ((BigFppfOver.toScheme B S hS).map p).appTop.hom
              ((f i).eval (op U))))).subschemeι =
        chartBaseChangeHom B S hS X
          (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W :=
  exists_iso_zeroScheme_chartBaseChange_of_definingIdealAt_eq B S hS
    (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W hW _
    (definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList B S hS g f U W p hp hW)

/-- **The pullback along `p` of the value of one of the functions lies in the defining ideal of
the base changed zero locus at `W`.**  This is
`AlgebraicGeometry.Space.definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList` read at
one member of the family. -/
theorem appTop_mem_definingIdealAt_vanishingSubspace_globalFunctionsMap (g : X ⟶ Y) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Y)).sections)
    (U : SmallEtale B S hS Y.1) (W : SmallEtale B S hS X.1) (p : W.1.left ⟶ U.1.left)
    (hp : yoneda.map p ≫ U.1.hom = W.1.hom ≫ g.hom) (hW : IsAffine (chartScheme W))
    (i : Fin r) :
    ((BigFppfOver.toScheme B S hS).map p).appTop.hom ((f i).eval (op U)) ∈
      definingIdealAt B S hS X
        (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) (op W) := by
  rw [definingIdealAt_vanishingSubspace_globalFunctionsMap_eq_ofList B S hS g f U W p hp hW]
  exact Ideal.subset_span (List.mem_ofFn.mpr ⟨i, rfl⟩)

/-- **An étale chart of the base change of `V(f₁, …, f_r)` is unramified over the spectrum of a
field at a point where the germs of the pulled-back functions generate the maximal ideal.**  This
is `AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_comp_over_field` at the pullbacks
`p^*f₁|_U, …, p^*f_r|_U`, whose membership in the defining ideal is
`AlgebraicGeometry.Space.appTop_mem_definingIdealAt_vanishingSubspace_globalFunctionsMap`.

It is the shape the chart construction of **Stacks 06N3** uses the criterion of **Stacks 02GF**
in: the generating sequence is produced on the chart `U` of the algebraic space being sliced, by
`AlgebraicGeometry.Space.exists_representedUnitSection_isRegular_etaleLocalRing_of_isAffine`,
whose germ clause is exactly the hypothesis `hgen` below, and what has to be unramified over
`Spec k` is the slice read on the chart `W` of the fibre. -/
theorem unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field
    {k : Type u} [Field k] (g : X ⟶ Y) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Y)).sections)
    (U : SmallEtale B S hS Y.1) (W : SmallEtale B S hS X.1) (p : W.1.left ⟶ U.1.left)
    (hp : yoneda.map p ≫ U.1.hom = W.1.hom ≫ g.hom) (hW : IsAffine (chartScheme W))
    (π : chartScheme W ⟶ Spec (.of k))
    [LocallyOfFiniteType (chartBaseChangeHom B S hS X
      (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W ≫ π)]
    (z : (BigFppfOver.toScheme B S hS).obj
      ((vanishingSubspace B S hS X fun i =>
        globalFunctionsMap B S hS g (f i)).2.2.rep.pullback W.1.hom))
    (hgen : Ideal.ofList (List.ofFn fun i => (chartScheme W).presheaf.germ ⊤
          (chartBaseChangeHom B S hS X
            (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W z) trivial
          (((BigFppfOver.toScheme B S hS).map p).appTop.hom ((f i).eval (op U)))) =
      maximalIdeal ((chartScheme W).presheaf.stalk
        (chartBaseChangeHom B S hS X
          (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W z)))
    (hsep : letI := (π.residueFieldMap (chartBaseChangeHom B S hS X
          (vanishingSubspace B S hS X fun i =>
            globalFunctionsMap B S hS g (f i)) W z)).hom.toAlgebra
      Module.Finite ((Spec (.of k)).residueField
          (π (chartBaseChangeHom B S hS X
            (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W z)))
          ((chartScheme W).residueField
            (chartBaseChangeHom B S hS X
              (vanishingSubspace B S hS X fun i =>
                globalFunctionsMap B S hS g (f i)) W z)) ∧
        Algebra.IsSeparable ((Spec (.of k)).residueField
            (π (chartBaseChangeHom B S hS X
              (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W z)))
            ((chartScheme W).residueField
              (chartBaseChangeHom B S hS X
                (vanishingSubspace B S hS X fun i =>
                  globalFunctionsMap B S hS g (f i)) W z))) :
    UnramifiedAt (chartBaseChangeHom B S hS X
      (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W ≫ π) z :=
  unramifiedAt_chartBaseChangeHom_comp_over_field B S hS
    (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W π z
    (fun i => ((BigFppfOver.toScheme B S hS).map p).appTop.hom ((f i).eval (op U)))
    (fun i => appTop_mem_definingIdealAt_vanishingSubspace_globalFunctionsMap B S hS g f U W p
      hp hW i)
    hgen hsep

/-- **The same with the composite supplied as a morphism of its own.**  The structure morphism
over `Spec k` of an étale chart of the fibre of the slice arrives, in the chart construction of
**Stacks 06N3**, as a morphism of the big fppf site carrying its own
`AlgebraicGeometry.LocallyOfFiniteType` instance; this is
`AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field` with
that morphism taken as a parameter together with its factorisation through the chart, which is
substituted. -/
theorem unramifiedAt_of_eq_chartBaseChangeHom_globalFunctionsMap_comp
    {k : Type u} [Field k] (g : X ⟶ Y) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (structureRingSheaf B S hS Y)).sections)
    (U : SmallEtale B S hS Y.1) (W : SmallEtale B S hS X.1) (p : W.1.left ⟶ U.1.left)
    (hp : yoneda.map p ≫ U.1.hom = W.1.hom ≫ g.hom) (hW : IsAffine (chartScheme W))
    (π : chartScheme W ⟶ Spec (.of k))
    (ψ : (BigFppfOver.toScheme B S hS).obj
        ((vanishingSubspace B S hS X fun i =>
          globalFunctionsMap B S hS g (f i)).2.2.rep.pullback W.1.hom) ⟶ Spec (.of k))
    [LocallyOfFiniteType ψ]
    (hψ : ψ = chartBaseChangeHom B S hS X
      (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W ≫ π)
    (z : (BigFppfOver.toScheme B S hS).obj
      ((vanishingSubspace B S hS X fun i =>
        globalFunctionsMap B S hS g (f i)).2.2.rep.pullback W.1.hom))
    (hgen : Ideal.ofList (List.ofFn fun i => (chartScheme W).presheaf.germ ⊤
          (chartBaseChangeHom B S hS X
            (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W z) trivial
          (((BigFppfOver.toScheme B S hS).map p).appTop.hom ((f i).eval (op U)))) =
      maximalIdeal ((chartScheme W).presheaf.stalk
        (chartBaseChangeHom B S hS X
          (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W z)))
    (hsep : letI := (π.residueFieldMap (chartBaseChangeHom B S hS X
          (vanishingSubspace B S hS X fun i =>
            globalFunctionsMap B S hS g (f i)) W z)).hom.toAlgebra
      Module.Finite ((Spec (.of k)).residueField
          (π (chartBaseChangeHom B S hS X
            (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W z)))
          ((chartScheme W).residueField
            (chartBaseChangeHom B S hS X
              (vanishingSubspace B S hS X fun i =>
                globalFunctionsMap B S hS g (f i)) W z)) ∧
        Algebra.IsSeparable ((Spec (.of k)).residueField
            (π (chartBaseChangeHom B S hS X
              (vanishingSubspace B S hS X fun i => globalFunctionsMap B S hS g (f i)) W z)))
            ((chartScheme W).residueField
              (chartBaseChangeHom B S hS X
                (vanishingSubspace B S hS X fun i =>
                  globalFunctionsMap B S hS g (f i)) W z))) :
    UnramifiedAt ψ z := by
  subst hψ
  exact unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field B S hS g f U W p hp
    hW π z hgen hsep

end AlgebraicGeometry.Space

end
