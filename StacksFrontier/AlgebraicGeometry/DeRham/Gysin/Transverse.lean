module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapCommutesWithDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Globalisation

/-!
# Base change of the Gysin map along a transverse cartesian square

Let

```
Z' → X' → S'
↓h   ↓g    ↓
Z  → X  → S
```

be a commutative diagram of schemes in which `Z → X` and `Z' → X'` are closed immersions of
finite presentation with conormal sheaf locally free of rank `c`, so that each carries the
canonical Gysin map `γ^p` of [Stacks, Tag 0G86]. Assume moreover that the left square is
cartesian and that `h^*𝒞_{Z/X} → 𝒞_{Z'/X'}` is an isomorphism. **Tag 0G89 is the assertion that
the square**

```
h^*Ω^p_{Z/S} ----γ^p----→ 𝒪_{X'}|_{Z'} ⊗ h^{-1}ℋ^c_Z(Ω^{p+c}_{X/S})
    ↓                                   ↓
Ω^p_{Z'/S'} ----γ^p----→ ℋ^c_{Z'}(Ω^{p+c}_{X'/S'})
```

**commutes**, the left vertical arrow being functoriality of modules of differentials and the
right one the canonical map of Cohomology, Remark [Stacks, Tag 0G78]. That is
`Stacks.Gysin.GysinBaseChange.gysinHom_baseChange`.

As in `StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Globalisation` both Gysin maps are read on the
ambient schemes — the source as `i_*Ω^p_{Z/S}`, the target as the direct image of the local
cohomology sheaf — so the square above becomes a statement about the sections over an open `V`
of `X` and the sections over `g⁻¹V` of `X'`. A morphism of sheaves being its family of maps on
sections, that is the same statement.

## Main definitions

* `Stacks.Gysin.subschemeFormBaseChange`: **the left vertical arrow**, pullback of relative
  differential forms along `h`, read on the sections of the direct images. It is the canonical
  map of [Stacks, Tag 01UV] in exterior degree `p`, transported along the identification
  `i'⁻¹(g⁻¹V) = h⁻¹(i⁻¹V)` that the commuting left square provides.
* `Stacks.Gysin.GysinBaseChange`: the base-change data of the square — the right vertical arrow,
  the correspondence of equation charts that the cartesian hypothesis provides, the
  compatibility of the class maps `c_{f₁, …, f_c}` with base change, and local liftability of
  forms. It does not assert Gysin commutativity.

## Main results

* `Stacks.Gysin.relativeDifferentialFormsPullback_comp`: **pulling back a relative differential
  form is functorial**, on local sections. This is
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_comp` read through the unit of the
  pullback adjunction, and it is what identifies the two ways around the outer square of the
  diagram.
* `Stacks.Gysin.relativeDifferentialFormsPullback_equationsWedgeOn` and
  `relativeDifferentialFormsPullback_gysinWedgeOn`: **the equation wedge pulls back to the
  equation wedge of the pulled-back equations**, `d f₁ ∧ ⋯ ∧ d f_c ↦ d f'₁ ∧ ⋯ ∧ d f'_c` for
  `f'_j = g^♯ f_j`. This is the sentence the source proof ends on, and it is the mathematical
  content of the lemma.
* `Stacks.Gysin.subschemeFormBaseChange_subschemeFormPullback`: restriction of an ambient form to
  the closed subscheme commutes with base change — the two ways around the outer square.
* `Stacks.Gysin.GysinBaseChange.gysinHom_baseChange_subschemeFormPullback`: the commutativity on
  a form lifted to the ambient scheme over an equation chart, which is where the computation
  happens.
* `Stacks.Gysin.GysinBaseChange.gysinHom_baseChange`: **Tag 0G89**, the commutativity of the
  Gysin square.

## Implementation notes

**What is proved and what is assumed.** The square is proved to commute. Four things are carried
as fields of `GysinBaseChange`, each the content of a tag this library does not have.

* `GysinBaseChange.tgt` and `tgt_res`: the right vertical arrow, the base-change map on the
  degree-`c` local cohomology of the ambient forms. The source builds it from Cohomology,
  Remark [Stacks, Tag 0G78] followed by the derived-to-underived comparison and functoriality of
  differentials, descended to degree `c` using the vanishing of local cohomology above degree `c`
  ([Stacks, Tag 0G7N]). The library has the derived map — `supportedPullbackMap` of
  `StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/SupportedSectionsDerivedPullback.lean`
  — and the vanishing, but not the descent to a map of degree-`c` sheaves, which is what the
  Gysin square's arrow is.
* `GysinBaseChange.tgt_cls`: **the base-change square for the class maps `c_{f₁, …, f_c}`**,
  which is Derived Categories of Schemes, Remark [Stacks, Tag 0G7U]. The `@[stacks 0G7U]`
  declarations in
  `StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/EquationsBaseChange.lean`
  are the cartesian square of the closed subschemes cut out by the equations and their
  pullbacks, not that compatibility of the class maps.
* `GysinBaseChange.chart`, `chart_ambient`, `chart_equations`: the equation charts of `Z' → X'`
  obtained by pulling back those of `Z → X`. This is where hypotheses (2) and (3) of the
  statement — the left square cartesian and the conormal comparison an isomorphism — enter: they
  are what makes `f'_j = g^♯ f_j` cut out `Z'` with locally free conormal sheaf of the *same*
  rank `c`, so that the pulled-back family is a chart of a `GysinChartData` for `i'`. Nothing in
  this library derives `c` equations from a rank-`c` conormal sheaf, which is the same gap
  `Globalisation.lean` records for `GysinChartData.ambient`.
* `GysinBaseChange.lift`: local surjectivity of restriction of relative `p`-forms to the closed
  subscheme, on a covering refining the equation charts. This is
  `Stacks.Gysin.ChartComparison.lift` of `Globalisation.lean`, over a covering rather than a
  single open; the library has exactness of the conormal sequence at its right term only
  ([Stacks, Tag 01UZ]).

**No field asserts anything about the Gysin maps.** The two Gysin maps are
`GysinChartData.gysinHom` of the two chart data, and what is proved about them is the
commutativity of the square. The fields speak only about the arrows of the square and about the
inputs of Tag 0G86 on the primed side.

**Why the statement is read on sections.** `GysinChartData.gysinHom` is a morphism of sheaves of
`𝒪_X`-modules and the comparison of the two targets is a map `Γ(T, V) → Γ(T', g⁻¹V)`, i.e. a
morphism `T ⟶ g_*T'`, which is the adjoint shape of the right vertical arrow of the source. The
commutativity is then the equation on sections proved here. Nothing is lost: a morphism of
sheaves of modules is its family of maps on sections.

**The two ways around the outer square.** `subschemeFormBaseChange` composes the restriction to
`Z` with the pullback along `h`; the primed side composes the pullback along `g` with the
restriction to `Z'`. Both are the canonical map of the outer square `Z' → X` over `S' → S`,
because `h ≫ i = i' ≫ g`, and `relativeDifferentialFormsPullback_comp` is what says so. The two
opens `h⁻¹(i⁻¹V)` and `i'⁻¹(g⁻¹V)` are *equal* but not definitionally so, and the identification
is carried by the restriction map along that equality rather than by `eqToHom`, which keeps every
statement below a statement about sections.

## References

* [Stacks Project, Tag 0G89](https://stacks.math.columbia.edu/tag/0G89)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7N](https://stacks.math.columbia.edu/tag/0G7N)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.Tag01VSPullbackTensor

universe u

namespace Stacks.Gysin

/-! ### Restriction along the identity, and naturality of the structure-sheaf map -/

/-- Restricting a local section of a sheaf of modules along the identity inclusion of its open
does nothing. -/
theorem presheaf_map_le_refl {Y : Scheme.{u}} (F : Y.Modules) (V : Y.Opens) (z : Γ(F, V)) :
    F.presheaf.map (homOfLE (le_refl V)).op z = z := by
  rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from rfl, F.presheaf.map_id]
  rfl

/-- Restricting a local section of the structure sheaf along the identity inclusion of its open
does nothing. -/
theorem structurePresheaf_map_le_refl {Y : Scheme.{u}} (V : Y.Opens) (z : Γ(Y, V)) :
    (Y.presheaf.map (homOfLE (le_refl V)).op).hom z = z := by
  rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from rfl, Y.presheaf.map_id]
  rfl

/-- **The structure-sheaf map of a morphism commutes with restriction.** This is the naturality
of `AlgebraicGeometry.Scheme.Hom.app`, with the inclusion of preimages spelled by `homOfLE`. -/
theorem app_structurePresheaf_map {X X' : Scheme.{u}} (g : X' ⟶ X) {U V : X.Opens} (hV : V ≤ U)
    (e : Γ(X, U)) :
    (g.app V).hom ((X.presheaf.map (homOfLE hV).op).hom e)
      = (X'.presheaf.map
          (homOfLE (show g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U from fun _ hz => hV hz)).op).hom ((g.app U).hom e) := by
  have h := congrArg (fun φ : Γ(X, U) ⟶ Γ(X', g ⁻¹ᵁ V) => ConcreteCategory.hom φ e)
    (g.naturality (homOfLE hV).op).symm
  simp only [ConcreteCategory.comp_apply] at h
  refine Eq.trans h.symm ?_
  exact congrArg (fun m : (g ⁻¹ᵁ V) ⟶ (g ⁻¹ᵁ U) =>
    (X'.presheaf.map m.op).hom ((g.app U).hom e)) (Subsingleton.elim _ _)

/-! ### Functoriality of the pullback of relative differential forms, on sections -/

/-- **The unit of the module pullback is natural in the module.** The pullback of a morphism,
evaluated on the unit image of a section, is the unit image of the value of the morphism. -/
theorem modulesPullbackUnit_pullback_map {X Y : Scheme.{u}} (g : X ⟶ Y) {F G : Y.Modules}
    (φ : F ⟶ G) (U : Y.Opens) (s : Γ(F, U)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback g).map φ) (g ⁻¹ᵁ U)
        (modulesPullbackUnit g F U s)
      = modulesPullbackUnit g G U (Scheme.Modules.Hom.app φ U s) := by
  have h2 := congrArg (fun ψ : F ⟶ (Scheme.Modules.pushforward g).obj
      ((Scheme.Modules.pullback g).obj G) =>
    ConcreteCategory.hom (Scheme.Modules.Hom.app ψ U) s)
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, Functor.id_map,
    Functor.comp_map] at h2
  exact h2.symm

/-- **Pulling back a relative differential form is functorial**, on local sections: for two
horizontally composable commutative squares the pullback along the composite is the pullback
along the right-hand edge followed by the pullback along the left-hand one. This is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_comp` read through the unit of the
pullback adjunction. -/
theorem relativeDifferentialFormsPullback_comp {X X' X'' S S' S'' : Scheme.{u}}
    (f : X' ⟶ X) (f' : X'' ⟶ X') (π : X ⟶ S) (π' : X' ⟶ S') (π'' : X'' ⟶ S'')
    (t : S' ⟶ S) (t' : S'' ⟶ S') (t'' : S'' ⟶ S)
    (h₁ : f ≫ π = π' ≫ t) (h₂ : f' ≫ π' = π'' ≫ t')
    (h₃ : (f' ≫ f) ≫ π = π'' ≫ t'') (n : ℤ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms π n, U)) :
    relativeDifferentialFormsPullback (f' ≫ f) π π'' t'' h₃ n U ω
      = relativeDifferentialFormsPullback f' π' π'' t' h₂ n (f ⁻¹ᵁ U)
          (relativeDifferentialFormsPullback f π π' t h₁ n U ω) := by
  refine Eq.trans (congrArg (fun φ => ConcreteCategory.hom
      (Scheme.Modules.Hom.app φ ((f' ≫ f) ⁻¹ᵁ U))
      (modulesPullbackUnit (f' ≫ f) (relativeDifferentialForms π n) U ω))
    (relativeDifferentialFormsMap_comp f f' π π' π'' t t' t'' h₁ h₂ h₃ n)) ?_
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [modulesPullbackUnit_pullbackComp_inv f' f (relativeDifferentialForms π n) U ω]
  exact congrArg (fun z => ConcreteCategory.hom (Scheme.Modules.Hom.app
      (relativeDifferentialFormsMap f' π' π'' t' h₂ n) (f' ⁻¹ᵁ f ⁻¹ᵁ U)) z)
    (modulesPullbackUnit_pullback_map f' (relativeDifferentialFormsMap f π π' t h₁ n) (f ⁻¹ᵁ U)
      (modulesPullbackUnit f (relativeDifferentialForms π n) U ω))

/-- **The pullback of a relative differential form depends only on the morphism**, not on which
of two equal morphisms it is spelled by: the two preimage opens are then equal and the pullbacks
agree after restriction along that equality. -/
theorem relativeDifferentialFormsPullback_congrMor {X W S S'' : Scheme.{u}} {k k' : W ⟶ X}
    (hk : k = k') (π : X ⟶ S) (π'' : W ⟶ S'') (t : S'' ⟶ S)
    (h₁ : k ≫ π = π'' ≫ t) (h₂ : k' ≫ π = π'' ≫ t) (n : ℤ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π n, V)) :
    (relativeDifferentialForms π'' n).presheaf.map
        (homOfLE (le_of_eq (show k' ⁻¹ᵁ V = k ⁻¹ᵁ V by rw [hk]))).op
        (relativeDifferentialFormsPullback k π π'' t h₁ n V ω)
      = relativeDifferentialFormsPullback k' π π'' t h₂ n V ω := by
  subst hk
  exact presheaf_map_le_refl _ _ _

/-! ### The pullback of the equation wedge -/

section Wedge

variable {X X' S S' : Scheme.{u}} (g : X' ⟶ X) (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)
  (hcomm : g ≫ π = π' ≫ t)

/-- **The pullback of an exact one-form is the exact one-form of the pullback**, in the spelling
`AlgebraicGeometry.Scheme.Hom.exactOneForm` that the equation wedge uses. This is
[Stacks, Tag 01UV] on sections. -/
theorem relativeDifferentialFormsPullback_exactOneForm (V : X.Opens) (b : Γ(X, V)) :
    relativeDifferentialFormsPullback g π π' t hcomm 1 V (exactOneForm π (op V) b)
      = exactOneForm π' (op (g ⁻¹ᵁ V)) ((g.app V).hom b) :=
  relativeDifferentialFormsPullback_exactOne g π π' t hcomm V b

/-- **The pullback of an ordered wedge of exact one-forms is the ordered wedge of the exact
one-forms of the pulled-back functions.** Pulling back is multiplicative and unital, so this is
the previous lemma spread over the recursion defining the ordered product. -/
theorem relativeDifferentialFormsPullback_prodDegOne (V : X.Opens) :
    ∀ (c : ℕ) (b : Fin c → Γ(X, V)),
    relativeDifferentialFormsPullback g π π' t hcomm (c : ℤ) V
        ((relativeDifferentialFormsAlgebra π).prodDegOne (op V) c
          fun j => exactOneForm π (op V) (b j))
      = (relativeDifferentialFormsAlgebra π').prodDegOne (op (g ⁻¹ᵁ V)) c
          fun j => exactOneForm π' (op (g ⁻¹ᵁ V)) ((g.app V).hom (b j)) := by
  intro c
  induction c with
  | zero => intro _; exact relativeDifferentialFormsPullback_one g π π' t hcomm V
  | succ n ih =>
      intro b
      refine Eq.trans (relativeDifferentialFormsPullback_mul g π π' t hcomm (n : ℤ) 1 V
        ((relativeDifferentialFormsAlgebra π).prodDegOne (op V) n
          fun i => exactOneForm π (op V) (b i.castSucc))
        (exactOneForm π (op V) (b (Fin.last n)))) ?_
      exact congrArg₂ (fun x y => ((relativeDifferentialFormsAlgebra π').mul (n : ℤ) 1).app
          (op (g ⁻¹ᵁ V)) x y)
        (ih fun j => b j.castSucc)
        (relativeDifferentialFormsPullback_exactOneForm g π π' t hcomm V (b (Fin.last n)))

/-- **The equation wedge pulls back to the equation wedge of the pulled-back equations**:
`d f₁ ∧ ⋯ ∧ d f_c` goes to `d f'₁ ∧ ⋯ ∧ d f'_c` for `f'_j = g^♯ f_j`. This is the sentence the
proof of [Stacks, Tag 0G89] ends on. -/
theorem relativeDifferentialFormsPullback_equationsWedgeOn {V : X.Opens} {c : ℕ}
    (f : Fin c → Γ(X, V)) :
    relativeDifferentialFormsPullback g π π' t hcomm (c : ℤ) V
        (equationsWedgeOn π f (le_refl V))
      = equationsWedgeOn π' (fun j => (g.app V).hom (f j)) (le_refl (g ⁻¹ᵁ V)) := by
  change relativeDifferentialFormsPullback g π π' t hcomm (c : ℤ) V
      ((relativeDifferentialFormsAlgebra π).prodDegOne (op V) c
        fun j => exactOneForm π (op V)
          ((X.presheaf.map (homOfLE (le_refl V)).op).hom (f j)))
    = (relativeDifferentialFormsAlgebra π').prodDegOne (op (g ⁻¹ᵁ V)) c
        fun j => exactOneForm π' (op (g ⁻¹ᵁ V))
          ((X'.presheaf.map (homOfLE (le_refl (g ⁻¹ᵁ V))).op).hom ((g.app V).hom (f j)))
  simp only [structurePresheaf_map_le_refl]
  exact relativeDifferentialFormsPullback_prodDegOne g π π' t hcomm V c f

/-- **Wedging with the equation wedge commutes with base change.** The pullback of
`ω ∧ d f₁ ∧ ⋯ ∧ d f_c` is `g^*ω ∧ d f'₁ ∧ ⋯ ∧ d f'_c`. -/
theorem relativeDifferentialFormsPullback_gysinWedgeOn {V : X.Opens} {c : ℕ}
    (f : Fin c → Γ(X, V)) (p : ℤ) (ω : Γ(relativeDifferentialForms π p, V)) :
    relativeDifferentialFormsPullback g π π' t hcomm (p + (c : ℤ)) V
        (gysinWedgeOn π f p (le_refl V) ω)
      = gysinWedgeOn π' (fun j => (g.app V).hom (f j)) p (le_refl (g ⁻¹ᵁ V))
          (relativeDifferentialFormsPullback g π π' t hcomm p V ω) :=
  (relativeDifferentialFormsPullback_mul g π π' t hcomm p (c : ℤ) V ω
    (equationsWedgeOn π f (le_refl V))).trans
    (congrArg (((relativeDifferentialFormsAlgebra π').mul p (c : ℤ)).app (op (g ⁻¹ᵁ V))
        (relativeDifferentialFormsPullback g π π' t hcomm p V ω))
      (relativeDifferentialFormsPullback_equationsWedgeOn g π π' t hcomm f))

end Wedge

/-! ### The left vertical arrow of the Gysin square -/

section BaseChange

variable {Z X S Z' X' S' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (h : Z' ⟶ Z) (g : X' ⟶ X)
  (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)

/-- The outer square of a transverse diagram commutes. -/
theorem outer_comm {i : Z ⟶ X} {i' : Z' ⟶ X'} {h : Z' ⟶ Z} {g : X' ⟶ X} {π : X ⟶ S}
    {π' : X' ⟶ S'} {t : S' ⟶ S} (left_comm : h ≫ i = i' ≫ g) (right_comm : g ≫ π = π' ≫ t) :
    h ≫ (i ≫ π) = (i' ≫ π') ≫ t := by
  rw [← Category.assoc, left_comm, Category.assoc, right_comm, ← Category.assoc]

/-- The two preimages of an open of the ambient scheme on the primed closed subscheme agree:
`i'⁻¹(g⁻¹V) = h⁻¹(i⁻¹V)`, because the left square commutes. -/
theorem preimage_eq_of_left_comm (left_comm : h ≫ i = i' ≫ g) (V : X.Opens) :
    i' ⁻¹ᵁ (g ⁻¹ᵁ V) = h ⁻¹ᵁ (i ⁻¹ᵁ V) := by
  change (i' ≫ g) ⁻¹ᵁ V = (h ≫ i) ⁻¹ᵁ V
  rw [left_comm]

/-- **The left vertical arrow of the Gysin square**: functoriality of modules of differentials.
A relative `p`-form on `Z` over `i⁻¹V` is pulled back along `h` to a relative `p`-form on `Z'`
over `h⁻¹(i⁻¹V)`, which is the open `i'⁻¹(g⁻¹V)` by `preimage_eq_of_left_comm`; reading both
through the direct images, this is a map
`Γ(i_*Ω^p_{Z/S}, V) → Γ(i'_*Ω^p_{Z'/S'}, g⁻¹V)`. -/
def subschemeFormBaseChange (left_comm : h ≫ i = i' ≫ g) (right_comm : g ≫ π = π' ≫ t) (n : ℤ)
    (V : X.Opens) (x : Γ(pushforwardRelativeForms i π n, V)) :
    Γ(pushforwardRelativeForms i' π' n, g ⁻¹ᵁ V) :=
  (relativeDifferentialForms (i' ≫ π') n).presheaf.map
    (homOfLE (le_of_eq (preimage_eq_of_left_comm i i' h g left_comm V))).op
    (relativeDifferentialFormsPullback h (i ≫ π) (i' ≫ π') t (outer_comm left_comm right_comm) n
      (i ⁻¹ᵁ V) x)

/-- **The left vertical arrow commutes with restriction**, which is what lets the commutativity
of the Gysin square be checked locally. -/
theorem subschemeFormBaseChange_res (left_comm : h ≫ i = i' ≫ g) (right_comm : g ≫ π = π' ≫ t)
    (n : ℤ) {V V₀ : X.Opens} (hV₀ : V₀ ≤ V) (x : Γ(pushforwardRelativeForms i π n, V)) :
    (pushforwardRelativeForms i' π' n).presheaf.map
        (homOfLE (show g ⁻¹ᵁ V₀ ≤ g ⁻¹ᵁ V from fun _ hz => hV₀ hz)).op
        (subschemeFormBaseChange i i' h g π π' t left_comm right_comm n V x)
      = subschemeFormBaseChange i i' h g π π' t left_comm right_comm n V₀
          ((pushforwardRelativeForms i π n).presheaf.map (homOfLE hV₀).op x) := by
  refine Eq.trans (presheaf_map_map (relativeDifferentialForms (i' ≫ π') n) _ _
    (homOfLE (show i' ⁻¹ᵁ (g ⁻¹ᵁ V₀) ≤ h ⁻¹ᵁ (i ⁻¹ᵁ V) from
      le_of_eq_of_le (preimage_eq_of_left_comm i i' h g left_comm V₀)
        (fun _ hz => hV₀ hz))) _) ?_
  refine Eq.trans ?_ (congrArg
    ((relativeDifferentialForms (i' ≫ π') n).presheaf.map
      (homOfLE (le_of_eq (preimage_eq_of_left_comm i i' h g left_comm V₀))).op)
    (relativeDifferentialFormsPullback_map h (i ≫ π) (i' ≫ π') t
      (outer_comm left_comm right_comm) n (i.preimage_mono hV₀)
      x).symm)
  exact (presheaf_map_map (relativeDifferentialForms (i' ≫ π') n) _ _ _ _).symm

/-- **Restriction of an ambient form to the closed subscheme commutes with base change.** Both
ways around the outer square `Z' → X` are the canonical map of that square on relative
differential forms, by `relativeDifferentialFormsPullback_comp`, and the two spellings
`h ≫ i` and `i' ≫ g` of its upper edge are equal. -/
theorem subschemeFormBaseChange_subschemeFormPullback (left_comm : h ≫ i = i' ≫ g)
    (right_comm : g ≫ π = π' ≫ t) (n : ℤ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π n, V)) :
    subschemeFormBaseChange i i' h g π π' t left_comm right_comm n V
        (subschemeFormPullback i π n V ω)
      = subschemeFormPullback i' π' n (g ⁻¹ᵁ V)
          (relativeDifferentialFormsPullback g π π' t right_comm n V ω) := by
  have hhi : h ≫ (i ≫ π) = (i' ≫ π') ≫ t := outer_comm left_comm right_comm
  have hcomp : (h ≫ i) ≫ π = (i' ≫ π') ≫ t := by
    rw [Category.assoc]; exact hhi
  have hcomp' : (i' ≫ g) ≫ π = (i' ≫ π') ≫ t := by rw [← left_comm]; exact hcomp
  have hleft : relativeDifferentialFormsPullback h (i ≫ π) (i' ≫ π') t hhi n (i ⁻¹ᵁ V)
      (subschemeFormPullback i π n V ω)
      = relativeDifferentialFormsPullback (h ≫ i) π (i' ≫ π') t hcomp n V ω :=
    (relativeDifferentialFormsPullback_comp i h π (i ≫ π) (i' ≫ π') (𝟙 S) t t
      (Category.comp_id (i ≫ π)).symm hhi hcomp n V ω).symm
  have hright : relativeDifferentialFormsPullback i' π' (i' ≫ π') (𝟙 S')
      (Category.comp_id (i' ≫ π')).symm n (g ⁻¹ᵁ V)
      (relativeDifferentialFormsPullback g π π' t right_comm n V ω)
      = relativeDifferentialFormsPullback (i' ≫ g) π (i' ≫ π') t hcomp' n V ω :=
    (relativeDifferentialFormsPullback_comp g i' π π' (i' ≫ π') t (𝟙 S') t right_comm
      (Category.comp_id (i' ≫ π')).symm hcomp' n V ω).symm
  refine Eq.trans (congrArg
    ((relativeDifferentialForms (i' ≫ π') n).presheaf.map
      (homOfLE (le_of_eq (preimage_eq_of_left_comm i i' h g left_comm V))).op) hleft) ?_
  exact Eq.trans (relativeDifferentialFormsPullback_congrMor left_comm π (i' ≫ π') t
    hcomp hcomp' n V ω) hright.symm

end BaseChange

/-! ### The base-change data of a transverse cartesian square -/

/-- **The base-change data of a transverse cartesian square**, for the Gysin maps of
[Stacks, Tag 0G86] attached to two `GysinChartData`. The module docstring says which field
stands for which result of the Stacks project and why each is an input rather than a
consequence. No field says anything about the Gysin maps: the commutativity of the square is
`GysinBaseChange.gysinHom_baseChange`. -/
structure GysinBaseChange {Z X S Z' X' S' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    (h : Z' ⟶ Z) (g : X' ⟶ X) (π : X ⟶ S) (π' : X' ⟶ S') (t : S' ⟶ S)
    (left_comm : h ≫ i = i' ≫ g) (right_comm : g ≫ π = π' ≫ t) {c p : ℕ}
    (D : GysinChartData i π c p) (D' : GysinChartData i' π' c p) where
  /-- **The right vertical arrow of the Gysin square**: base change on the degree-`c` local
  cohomology of the ambient relative forms, on sections. Its construction is Cohomology,
  Remark [Stacks, Tag 0G78] descended to degree `c` using the vanishing of
  [Stacks, Tag 0G7N]. -/
  tgt : (V : X.Opens) → Γ(D.target, V) → Γ(D'.target, g ⁻¹ᵁ V)
  /-- It commutes with restriction, being a map of sheaves. -/
  tgt_res : ∀ (V V₀ : X.Opens) (hV₀ : V₀ ≤ V) (y : Γ(D.target, V)),
    tgt V₀ (D.target.presheaf.map (homOfLE hV₀).op y)
      = D'.target.presheaf.map
          (homOfLE (show g ⁻¹ᵁ V₀ ≤ g ⁻¹ᵁ V from fun _ hz => hV₀ hz)).op (tgt V y)
  /-- The equation chart of `i'` obtained by pulling back an equation chart of `i`. That the
  pulled-back equations again cut out a closed immersion of finite presentation with conormal
  sheaf locally free of rank `c` is hypotheses (2) and (3) of the statement. -/
  chart : D.Chart → D'.Chart
  /-- Its open contains the preimage of the open of the chart it comes from. -/
  chart_ambient : ∀ a, g ⁻¹ᵁ D.ambient a ≤ D'.ambient (chart a)
  /-- **Its equations are the pullbacks `f'_j = g^♯ f_j`.** -/
  chart_equations : ∀ (a : D.Chart) (j : Fin c),
    (X'.presheaf.map (homOfLE (chart_ambient a)).op).hom (D'.equations (chart a) j)
      = (g.app (D.ambient a)).hom (D.equations a j)
  /-- **Derived Categories of Schemes, Remark [Stacks, Tag 0G7U]**: the class maps
  `c_{f₁, …, f_c}` and `c_{f'₁, …, f'_c}` fit into a commutative square with the base-change map
  on the targets and the canonical map on the ambient relative forms. -/
  tgt_cls : ∀ (a : D.Chart) (V : X.Opens) (hV : V ≤ D.ambient a)
    (y : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V)),
    tgt V (D.cls a V hV y)
      = D'.cls (chart a) (g ⁻¹ᵁ V)
          (le_trans (show g ⁻¹ᵁ V ≤ g ⁻¹ᵁ D.ambient a from fun _ hz => hV hz) (chart_ambient a))
          (relativeDifferentialFormsPullback g π π' t right_comm ((p : ℤ) + (c : ℤ)) V y)
  /-- **Local liftability of relative `p`-forms**: every section of `i_*Ω^p_{Z/S}` over an open
  of `X` is, on a covering of that open by opens each inside an equation chart, the restriction
  of an ambient relative `p`-form. -/
  lift : ∀ (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
    ∃ (J : Type u) (V₀ : J → X.Opens) (hle : ∀ k, V₀ k ≤ V) (a : J → D.Chart),
      (∀ k, V₀ k ≤ D.ambient (a k)) ∧ (V ≤ ⨆ k, V₀ k) ∧
        ∀ k, ∃ ω, subschemeFormPullback i π (p : ℤ) (V₀ k) ω =
          (pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE (hle k)).op x

namespace GysinBaseChange

variable {Z X S Z' X' S' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'} {h : Z' ⟶ Z} {g : X' ⟶ X}
  {π : X ⟶ S} {π' : X' ⟶ S'} {t : S' ⟶ S} {left_comm : h ≫ i = i' ≫ g}
  {right_comm : g ≫ π = π' ≫ t} {c p : ℕ} {D : GysinChartData i π c p}
  {D' : GysinChartData i' π' c p} (B : GysinBaseChange i i' h g π π' t left_comm right_comm D D')

/-- The equations of the pulled-back chart, restricted to the preimage of an open of the chart
they come from, are the pullbacks of the restricted equations. This is `chart_equations` spread
over a smaller open by naturality of the structure-sheaf map. -/
theorem chart_equations_res (a : D.Chart) {V : X.Opens} (hV : V ≤ D.ambient a) (j : Fin c) :
    (X'.presheaf.map (homOfLE (le_trans
          (show g ⁻¹ᵁ V ≤ g ⁻¹ᵁ D.ambient a from fun _ hz => hV hz)
          (B.chart_ambient a))).op).hom (D'.equations (B.chart a) j)
      = (g.app V).hom ((X.presheaf.map (homOfLE hV).op).hom (D.equations a j)) := by
  rw [app_structurePresheaf_map g hV, ← B.chart_equations a j, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  rfl

/-- **The Gysin square commutes on a form lifted to the ambient scheme over an equation chart.**
This is the computation of [Stacks, Tag 0G89]: on the restriction `ω̃|_Z` of an ambient `p`-form
both Gysin maps are given by the Gysin formula of [Stacks, Tag 0G83], the class maps are
compatible with base change by [Stacks, Tag 0G7U], and the equation wedge pulls back to the
equation wedge of the pulled-back equations. -/
theorem gysinHom_baseChange_subschemeFormPullback (a : D.Chart) (V : X.Opens)
    (hV : V ≤ D.ambient a) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    B.tgt V (D.gysinHom.app V (subschemeFormPullback i π (p : ℤ) V ω))
      = D'.gysinHom.app (g ⁻¹ᵁ V) (subschemeFormBaseChange i i' h g π π' t left_comm right_comm
          (p : ℤ) V (subschemeFormPullback i π (p : ℤ) V ω)) := by
  have hV' : g ⁻¹ᵁ V ≤ D'.ambient (B.chart a) :=
    (g.preimage_mono hV).trans (B.chart_ambient a)
  rw [D.gysinHom_app_subschemeFormPullback a V hV ω, B.tgt_cls a V hV _,
    subschemeFormBaseChange_subschemeFormPullback i i' h g π π' t left_comm right_comm
      (p : ℤ) V ω,
    D'.gysinHom_app_subschemeFormPullback (B.chart a) (g ⁻¹ᵁ V) hV' _]
  refine congrArg (D'.cls (B.chart a) (g ⁻¹ᵁ V) hV') ?_
  rw [← gysinWedgeOn_restrict π (D.equations a) (p : ℤ) hV ω,
    relativeDifferentialFormsPullback_gysinWedgeOn g π π' t right_comm
      (fun j => (X.presheaf.map (homOfLE hV).op).hom (D.equations a j)) (p : ℤ) ω,
    ← gysinWedgeOn_restrict π' (D'.equations (B.chart a)) (p : ℤ) hV'
      (relativeDifferentialFormsPullback g π π' t right_comm (p : ℤ) V ω)]
  exact congrArg
    (fun z : Fin c → Γ(X', g ⁻¹ᵁ V) => gysinWedgeOn π' z (p : ℤ) (le_refl (g ⁻¹ᵁ V))
      (relativeDifferentialFormsPullback g π π' t right_comm (p : ℤ) V ω))
    (funext fun j => (B.chart_equations_res a hV j).symm)

/-- **Stacks Project, Tag 0G89.** For a transverse cartesian square the Gysin maps of
[Stacks, Tag 0G86] on the two closed immersions fit into a commutative square: the base-change
map on the targets applied to `γ^p` agrees with `γ^p` applied to the pullback of relative
differential forms.

The commutativity is checked locally, which is what the source does: on a covering of the open by
opens inside an equation chart over which the form lifts to the ambient scheme, it is
`gysinHom_baseChange_subschemeFormPullback`; the target is a sheaf, so it holds over the open
itself. -/
@[stacks 0G89 "the Gysin square of a transverse cartesian square commutes, for the Gysin maps \
GysinChartData.gysinHom of Stacks 0G86; granted the right vertical arrow of Stacks 0G78 \
descended to degree c by the vanishing of Stacks 0G7N as the hypothesis B.tgt with B.tgt_res, \
the class-map base-change square of Stacks 0G7U as the hypothesis B.tgt_cls, hypotheses (2) and \
(3) of the statement -- the left square cartesian and the conormal comparison of Stacks 01R4 an \
isomorphism -- as the chart correspondence B.chart with B.chart_ambient and B.chart_equations, \
and the local liftability of relative forms coming from the conormal sequence of Stacks 01UZ as \
the hypothesis B.lift; none of these four is proved in this library"]
theorem gysinHom_baseChange (V : X.Opens) (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    B.tgt V (D.gysinHom.app V x)
      = D'.gysinHom.app (g ⁻¹ᵁ V) (subschemeFormBaseChange i i' h g π π' t left_comm right_comm
          (p : ℤ) V x) := by
  obtain ⟨J, V₀, hle, a, ha, hcov, hlift⟩ := B.lift V x
  have hcovg : g ⁻¹ᵁ V ≤ ⨆ k, g ⁻¹ᵁ V₀ k := by
    intro z hz
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (hcov hz)
    exact Opens.mem_iSup.mpr ⟨k, hk⟩
  have key : ∀ k : J, D'.target.presheaf.map
        (homOfLE (g.preimage_mono (hle k))).op
        (B.tgt V (D.gysinHom.app V x))
      = D'.target.presheaf.map
        (homOfLE (g.preimage_mono (hle k))).op
        (D'.gysinHom.app (g ⁻¹ᵁ V) (subschemeFormBaseChange i i' h g π π' t left_comm
          right_comm (p : ℤ) V x)) := by
    intro k
    obtain ⟨ω, hω⟩ := hlift k
    rw [← B.tgt_res V (V₀ k) (hle k) (D.gysinHom.app V x),
      ← homApp_presheaf_map D.gysinHom (homOfLE (hle k)) x,
      ← homApp_presheaf_map D'.gysinHom (homOfLE (g.preimage_mono (hle k))) _,
      subschemeFormBaseChange_res i i' h g π π' t left_comm right_comm (p : ℤ) (hle k) x, ← hω]
    exact B.gysinHom_baseChange_subschemeFormPullback (a k) (V₀ k) (ha k) ω
  exact TopCat.Sheaf.eq_of_locally_eq'
    (F := (⟨D'.target.presheaf, D'.target.isSheaf⟩ : TopCat.Sheaf Ab.{u} X'))
    (fun k => g ⁻¹ᵁ V₀ k) (g ⁻¹ᵁ V) (fun k => homOfLE (fun _ hz => hle k hz)) hcovg _ _ key

end GysinBaseChange

end Stacks.Gysin

end
