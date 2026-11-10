module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDifferenceDerivation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFirstOrder
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The difference of two infinitesimal deformations of a map, globally

Let `S` be a scheme, let `i : X ⟶ X'` and `j : Y ⟶ Y'` be first-order thickenings over `S`, and
let `(a, a')` and `(b, b')` be two morphisms of thickenings `(X ⊂ X') ⟶ (Y ⊂ Y')` over `S`.
[Stacks Project, Tag 04FG] says that if `a = b` and the two induced maps
`a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4] agree, then `(a')^♯ - (b')^♯` factors as
```
𝒪_{Y'} ⟶ 𝒪_Y --D--> a_*𝒞_{X/X'} ⟶ a_*𝒪_{X'}
```
with `D` an `𝒪_S`-derivation. This file proves that statement for **arbitrary** `X'` and `Y'`.
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivation.lean` proves it on global
sections when `X'` and `Y'` are affine; this file glues that computation along the affine opens
of `Y'`.

## The shape of the statement

Every sheaf in the factorization is read on sections, as in
`Stacks.Thickenings.mapDifferenceDerivation`. For an open `V ⊆ Y'`:

* `𝒪_{Y'}` over `V` is `Γ(Y', V)`;
* `𝒪_Y` over `V` is `Γ(Y, j ⁻¹ᵁ V)`, the sections of `j_*𝒪_Y`;
* `a_*𝒪_{X'}` over `V` is `Γ(X', a' ⁻¹ᵁ V)` — the underlying continuous maps of `a'` and `b'`
  agree by `Stacks.Thickenings.preimage_eq_of_comm`, so this is also where `(b')^♯` lands and the
  two comorphisms may be subtracted;
* `a_*𝒞_{X/X'}` over `V` is the subgroup of `Γ(X', a' ⁻¹ᵁ V)` killed by `i.app (a' ⁻¹ᵁ V)`, the
  defining ideal of `i`, which for a first-order thickening *is* the conormal sheaf — that
  identification is `Stacks.Thickenings.firstOrderConormalIso` and the inclusion into `𝒪_{X'}` is
  `Stacks.Thickenings.firstOrderConormalSheafι`.

The map `D` is `Stacks.Thickenings.mapDifferenceSheaf`. Note that `𝒪_{Y'} ⟶ 𝒪_Y` is **not**
surjective on sections over a general open, so `D` cannot be defined by descending the difference
along it; it is constructed by gluing, which is the content of
`Stacks.Thickenings.existsUnique_descendAlongIdeal`.

## Main definitions

* `Stacks.Thickenings.AgreeOnIdeal`: hypothesis (2) of the source, on sections. The two
  comorphisms agree on the defining ideal of `j`. For a first-order thickening the defining ideal
  is the conormal sheaf and the induced map of [Stacks Project, Tag 01R4] is the restriction of
  the ambient comorphism (`Stacks.Thickenings.conormalMap_apply` is the affine form of this), so
  this is exactly the hypothesis that the two maps `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` coincide.
* `Stacks.Thickenings.mapDifferenceSheaf`: the derivation `D`, as a map
  `Γ(Y, j ⁻¹ᵁ V) → Γ(X', a' ⁻¹ᵁ V)` for every open `V` of `Y'`.
* `Stacks.Thickenings.conormalSmul`: the action of `𝒪_Y` on `a_*𝒞_{X/X'}`, needed to state the
  Leibniz rule. A section of `𝒪_{Y'}` acts on the conormal sheaf through `a'`, and the action
  kills the defining ideal of `j` because the conormal sheaf is square-zero, so the action
  descends to `𝒪_Y`; it too is constructed by gluing.

## Main results

* `Stacks.Thickenings.existsUnique_descendAlongIdeal`: the gluing principle. A rule `F` assigning
  to a section of `𝒪_{Y'}` over `W` a section of `a'_*𝒪_{X'}` over `W`, additive, natural in `W`
  and killing the defining ideal of `j`, descends uniquely to a rule on sections of `𝒪_Y`.
* `Stacks.Thickenings.mapDifferenceSheaf_app`: **the factorization of [Stacks Project, Tag 04FG]**.
  On a section `x` of `𝒪_{Y'}` over `V` the composite `D ∘ j^♯` is `(a')^♯ x - (b')^♯ x`.
* `Stacks.Thickenings.app_mapDifferenceSheaf`: `D` takes values in `a_*𝒞_{X/X'}`, i.e. the
  factorization passes through the conormal sheaf and not merely through `a_*𝒪_{X'}`.
* `Stacks.Thickenings.mapDifferenceSheaf_add`, `Stacks.Thickenings.mapDifferenceSheaf_mul`,
  `Stacks.Thickenings.mapDifferenceSheaf_appLE_base`: `D` is additive, satisfies the Leibniz rule
  for `Stacks.Thickenings.conormalSmul`, and kills the sections pulled back from `S`. That is,
  `D` is an `𝒪_S`-derivation.
* `Stacks.Thickenings.mapDifferenceSheaf_map`: `D` is a map of sheaves, i.e. commutes with
  restriction.
* `Stacks.Thickenings.agreeOnIdeal_of_affine`: hypothesis (2) need only be checked on the affine
  opens of `Y'`, so `Stacks.Thickenings.AgreeOnIdeal` is a local condition.

## Implementation notes

The construction is the one the source indicates, carried out on sections. Over an **affine** open
`W` of `Y'` the comorphism `j.app W` is surjective (`AlgebraicGeometry.Scheme.Hom.app_surjective`),
so a section `s` of `𝒪_Y` over `j ⁻¹ᵁ W` lifts to `x ∈ Γ(Y', W)` and the difference
`(a')^♯ x - (b')^♯ x` is available there. Two lifts differ by a section of the defining ideal of
`j`, which hypothesis (2) kills, so the local values do not depend on the lift and glue. The
affine opens of `Y'` form a basis, so this determines `D` on every open — and the uniqueness half
of `Stacks.Thickenings.existsUnique_descendAlongIdeal` is what every property of `D` below is
proved with: to prove an identity between sections of `a'_*𝒪_{X'}` built from `D` it suffices to
check it on an affine open after choosing lifts.

Nothing here needs `X'` to be affine. The one place where affineness of the ambient scheme was
used in the global-sections proof is the square-zero property of the defining ideal of `i`, and
`Stacks.Thickenings.ker_app_sq_eq_bot` supplies that over an arbitrary open.

`𝒪_S`-linearity of `D` is stated as `Stacks.Thickenings.mapDifferenceSheaf_appLE_base`: `D` kills
every section of `𝒪_Y` pulled back from `𝒪_S` along `j ≫ q`. Together with the Leibniz rule this
is `𝒪_S`-linearity, the form in which a derivation over a base is usually axiomatised; it is the
sheaf form of `map_smul'` in `Stacks.Thickenings.mapDifferenceLinearMap`.

## Partial coverage

Hypothesis (2) is carried in the sectionwise form `Stacks.Thickenings.AgreeOnIdeal`, and the
identification of that form with the equality of the two morphisms
`Stacks.Thickenings.firstOrderThickeningConormalSheafMap` of sheaves of modules is **not**
formalised here. The two are the same condition: for a first-order thickening the quotient map
`ℐ ⟶ i_* 𝒞_{X/X'}` of [Stacks Project, Tag 01R3] part (1) is an isomorphism
(`Stacks.Thickenings.isIso_unit_app_idealSheaf`), so a morphism of conormal sheaves induced by a
square of thickenings is determined by, and determines, the restriction of the ambient comorphism
to the defining ideal — which on sections is what `AgreeOnIdeal` asserts and what
`Stacks.Thickenings.conormalMap_apply` says in the affine case. What is proved about the form
carried here is that it is local, `Stacks.Thickenings.agreeOnIdeal_of_affine`: it is a condition
on a basis of opens of `Y'`, hence a condition on sheaves and not a stronger pointwise one.

The derivation is not packaged as a `Derivation` or as a
`AlgebraicGeometry.SheafOfModules.SheafDerivation`: its three laws are stated separately, over
each open, together with the module action `Stacks.Thickenings.conormalSmul` the Leibniz rule
needs. Bundling them would require the `𝒪_Y`-module structure on `a_*𝒞_{X/X'}` as an instance,
which `conormalSmul` supplies the action for but whose module axioms are not checked here.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Thickenings

variable {S X X' Y Y' : Scheme.{u}}

/-! ### Notation for restriction -/

/-- The restriction of a section of the structure sheaf of a scheme to a smaller open, as a
function. The statements below restrict sections constantly and
`Z.presheaf.map (homOfLE h).op` spelled out makes them unreadable. -/
abbrev resOpen {Z : Scheme.{u}} {U U' : Z.Opens} (h : U' ≤ U) (x : Γ(Z, U)) : Γ(Z, U') :=
  (Z.presheaf.map (CategoryTheory.homOfLE h).op).hom x

/-- Restricting twice is restricting once, to the smaller open. -/
theorem resOpen_resOpen {Z : Scheme.{u}} {U U' U'' : Z.Opens} (h : U' ≤ U) (h' : U'' ≤ U')
    (x : Γ(Z, U)) : resOpen h' (resOpen h x) = resOpen (h'.trans h) x := by
  rw [resOpen, resOpen, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of a section to the same open is the identity. -/
theorem resOpen_self {Z : Scheme.{u}} {U : Z.Opens} (h : U ≤ U) (x : Γ(Z, U)) :
    resOpen h x = x := by
  rw [resOpen, show (CategoryTheory.homOfLE h).op = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Sections over the preimage of an open are determined on the preimages of affine opens.**
The affine opens contained in `V` cover `V`, so their preimages under any morphism cover the
preimage of `V`. This is the locality principle every proof below is written with. -/
theorem section_ext_preimage {Z : Scheme.{u}} (f : Z ⟶ Y') {V : Y'.Opens} {t₁ t₂ : Γ(Z, f ⁻¹ᵁ V)}
    (h : ∀ (W : Y'.Opens) (hW : W ≤ V), IsAffineOpen W →
      resOpen (f.preimage_mono hW) t₁ = resOpen (f.preimage_mono hW) t₂) : t₁ = t₂ := by
  refine TopCat.Presheaf.IsSheaf.section_ext (F := Z.presheaf) Z.sheaf.property
    (U := op (f ⁻¹ᵁ V)) ?_
  intro z hz
  have hfz : f.base z ∈ V := hz
  obtain ⟨W₀, haff, hzW₀, hsub₀⟩ := exists_isAffineOpen_mem_and_subset hfz
  exact ⟨f ⁻¹ᵁ W₀, f.preimage_mono hsub₀, hzW₀, h W₀ hsub₀ haff⟩

/-- Restriction sends the zero section to zero. -/
theorem resOpen_zero {Z : Scheme.{u}} {U U' : Z.Opens} (h : U' ≤ U) :
    resOpen h (0 : Γ(Z, U)) = 0 := map_zero _

/-- Restriction of sections is additive. -/
theorem resOpen_add {Z : Scheme.{u}} {U U' : Z.Opens} (h : U' ≤ U) (x y : Γ(Z, U)) :
    resOpen h (x + y) = resOpen h x + resOpen h y := map_add _ _ _

/-- Restriction of sections is multiplicative. -/
theorem resOpen_mul {Z : Scheme.{u}} {U U' : Z.Opens} (h : U' ≤ U) (x y : Γ(Z, U)) :
    resOpen h (x * y) = resOpen h x * resOpen h y := map_mul _ _ _

/-- Restriction of sections commutes with the comorphism of a morphism of schemes. -/
theorem app_resOpen {Z Z' : Scheme.{u}} (f : Z ⟶ Z') {V V' : Z'.Opens} (h : V' ≤ V)
    (x : Γ(Z', V)) :
    (f.app V').hom (resOpen h x) = resOpen (f.preimage_mono h) ((f.app V).hom x) := by
  have h2 := congr($(f.naturality (CategoryTheory.homOfLE h).op).hom x)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h2
  exact h2

/-- The comorphism on an open lying over `V` is the comorphism over `V` followed by
restriction. -/
theorem appLE_eq_resOpen_app {Z Z' : Scheme.{u}} (f : Z ⟶ Z') {V : Z'.Opens} {U : Z.Opens}
    (hU : U ≤ f ⁻¹ᵁ V) (y : Γ(Z', V)) :
    (f.appLE V U hU).hom y = resOpen hU ((f.app V).hom y) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply]

/-- Two morphisms of schemes that are equal have the same comorphism, read on sections after
restriction to a common open. The two sides are not syntactically comparable before the equality
is substituted, because the open an unrestricted comorphism lands on depends on the morphism. -/
theorem resOpen_app_congr {Z Z' : Scheme.{u}} {g g' : Z ⟶ Z'} (h : g = g') {V : Z'.Opens}
    {W : Z.Opens} (hg : W ≤ g ⁻¹ᵁ V) (hg' : W ≤ g' ⁻¹ᵁ V) (y : Γ(Z', V)) :
    resOpen hg ((g.app V).hom y) = resOpen hg' ((g'.app V).hom y) := by
  subst h
  rfl

/-! ### The difference of the two comorphisms -/

variable {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'} {p : X' ⟶ S} {q : Y' ⟶ S}

/-- **The comorphism of a composite, on sections over an open lying over `V`.** Applying the
comorphism of `i` to the restriction along `f` of a section over `V` is the restriction of the
comorphism of `i ≫ f`. -/
theorem app_appLE (i : X ⟶ X') (f : X' ⟶ Y') {V : Y'.Opens} {U : X'.Opens} (hU : U ≤ f ⁻¹ᵁ V)
    (y : Γ(Y', V)) (hc : i ⁻¹ᵁ U ≤ (i ≫ f) ⁻¹ᵁ V) :
    (i.app U).hom ((f.appLE V U hU).hom y) = resOpen hc (((i ≫ f).app V).hom y) := by
  rw [appLE_eq_resOpen_app, app_resOpen i hU ((f.app V).hom y)]
  rfl

/-- **Hypothesis (2) of [Stacks Project, Tag 04FG], on sections.** The two comorphisms
`(a')^♯` and `(b')^♯` agree on the defining ideal of `j : Y ⟶ Y'`.

For a first-order thickening the defining ideal *is* the conormal sheaf — that is
`Stacks.Thickenings.firstOrderConormalIso` — and the map `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of
[Stacks Project, Tag 01R4] induced by a morphism of thickenings is, on sections, the restriction
of the ambient comorphism to the defining ideal; `Stacks.Thickenings.conormalMap_apply` is that
statement on global sections over an affine. So this is exactly the hypothesis of the source that
the two induced maps of conormal sheaves coincide. -/
def AgreeOnIdeal (j : Y ⟶ Y') (a' b' : X' ⟶ Y') : Prop :=
  ∀ (V : Y'.Opens) (U : X'.Opens) (hUa : U ≤ a' ⁻¹ᵁ V) (hUb : U ≤ b' ⁻¹ᵁ V) (y : Γ(Y', V)),
    (j.app V).hom y = 0 → (a'.appLE V U hUa).hom y = (b'.appLE V U hUb).hom y

/-- **The difference of the two comorphisms over an open.** For an open `V` of `Y'` and an open
`U` of `X'` lying over `V` for both `a'` and `b'`, this is `(a')^♯ x - (b')^♯ x`. -/
def mapDifferenceLE {V : Y'.Opens} {U : X'.Opens} (hUa : U ≤ a' ⁻¹ᵁ V) (hUb : U ≤ b' ⁻¹ᵁ V)
    (x : Γ(Y', V)) : Γ(X', U) :=
  (a'.appLE V U hUa).hom x - (b'.appLE V U hUb).hom x

/-- The difference of the two comorphisms is additive. -/
theorem mapDifferenceLE_add {V : Y'.Opens} {U : X'.Opens} (hUa : U ≤ a' ⁻¹ᵁ V)
    (hUb : U ≤ b' ⁻¹ᵁ V) (x y : Γ(Y', V)) :
    mapDifferenceLE hUa hUb (x + y) = mapDifferenceLE hUa hUb x + mapDifferenceLE hUa hUb y := by
  simp only [mapDifferenceLE, map_add]
  ring

/-- The difference of the two comorphisms commutes with subtraction. -/
theorem mapDifferenceLE_sub {V : Y'.Opens} {U : X'.Opens} (hUa : U ≤ a' ⁻¹ᵁ V)
    (hUb : U ≤ b' ⁻¹ᵁ V) (x y : Γ(Y', V)) :
    mapDifferenceLE hUa hUb (x - y) = mapDifferenceLE hUa hUb x - mapDifferenceLE hUa hUb y := by
  simp only [mapDifferenceLE, map_sub]
  ring

/-- The difference of the two comorphisms is a section of the defining ideal of `i`: both
comorphisms reduce to `a^♯ ∘ j^♯`. This is the first assertion of [Stacks Project, Tag 04FG],
over an arbitrary open. -/
theorem app_mapDifferenceLE (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) {V : Y'.Opens}
    {U : X'.Opens} (hUa : U ≤ a' ⁻¹ᵁ V) (hUb : U ≤ b' ⁻¹ᵁ V) (x : Γ(Y', V)) :
    (i.app U).hom (mapDifferenceLE hUa hUb x) = 0 := by
  have hca : i ⁻¹ᵁ U ≤ (i ≫ a') ⁻¹ᵁ V := i.preimage_mono hUa
  have hcb : i ⁻¹ᵁ U ≤ (i ≫ b') ⁻¹ᵁ V := i.preimage_mono hUb
  rw [mapDifferenceLE, map_sub, app_appLE i a' hUa x hca, app_appLE i b' hUb x hcb,
    resOpen_app_congr (comm_a.trans comm_b.symm) hca hcb x, sub_self]

/-- The difference of the two comorphisms commutes with restriction. -/
theorem mapDifferenceLE_resOpen {V : Y'.Opens} {U U' : X'.Opens} (hUa : U ≤ a' ⁻¹ᵁ V)
    (hUb : U ≤ b' ⁻¹ᵁ V) (h : U' ≤ U) (x : Γ(Y', V)) :
    resOpen h (mapDifferenceLE hUa hUb x) = mapDifferenceLE (h.trans hUa) (h.trans hUb) x := by
  have ha := congr($(a'.appLE_map hUa (CategoryTheory.homOfLE h).op).hom x)
  have hb := congr($(b'.appLE_map hUb (CategoryTheory.homOfLE h).op).hom x)
  simp only [CommRingCat.comp_apply] at ha hb
  simp only [mapDifferenceLE, resOpen, map_sub]
  rw [ha, hb]

/-- The difference of the two comorphisms commutes with restriction in the target open. -/
theorem mapDifferenceLE_map {V V' : Y'.Opens} {U : X'.Opens} (hV : V' ≤ V)
    (hUa : U ≤ a' ⁻¹ᵁ V') (hUb : U ≤ b' ⁻¹ᵁ V') (x : Γ(Y', V)) :
    mapDifferenceLE hUa hUb (resOpen hV x)
      = mapDifferenceLE (hUa.trans (a'.preimage_mono hV)) (hUb.trans (b'.preimage_mono hV)) x := by
  have ha := congr($(a'.map_appLE hUa (CategoryTheory.homOfLE hV).op).hom x)
  have hb := congr($(b'.map_appLE hUb (CategoryTheory.homOfLE hV).op).hom x)
  simp only [CommRingCat.comp_apply] at ha hb
  simp only [mapDifferenceLE, resOpen]
  rw [ha, hb]

/-! ### The gluing principle -/

/-- If `x` lifts `s` over `W`, its restriction to a smaller `W₀` lifts the restriction of `s`. -/
private theorem app_resOpen_eq_of_lift {j : Y ⟶ Y'} {V W W₀ : Y'.Opens} {s : Γ(Y, j ⁻¹ᵁ V)}
    {x : Γ(Y', W)} (hW : W ≤ V) (hW₀ : W₀ ≤ W)
    (hx : (j.app W).hom x = resOpen (j.preimage_mono hW) s) :
    (j.app W₀).hom (resOpen hW₀ x) = resOpen (j.preimage_mono (hW₀.trans hW)) s := by
  rw [app_resOpen j hW₀ x, hx, resOpen_resOpen]

/-- **A rule on sections of `𝒪_{Y'}` that kills the defining ideal of `j` descends to a rule on
sections of `𝒪_Y`.** This is the gluing step the proof of [Stacks Project, Tag 04FG] needs, and
it is the only place the affine opens of `Y'` are used.

The comorphism `𝒪_{Y'} ⟶ j_*𝒪_Y` is surjective on sections over an **affine** open, so a section
`s` of `𝒪_Y` over `j ⁻¹ᵁ V` lifts locally; a rule `F` as in the hypotheses takes the same value on
two lifts, since they differ by a section of the defining ideal of `j`, and the values glue. The
resulting section of `a'_*𝒪_{X'}` over `V` is characterised by its values on **every** open
`W ≤ V` carrying a lift, not only on the affine ones.

The hypotheses on `F` are: naturality in the open, additivity, and vanishing on the defining
ideal of `j`. Additivity is what turns "two lifts differ by a section of the ideal" into "`F`
takes the same value on them". -/
theorem existsUnique_descendAlongIdeal (hj : AlgebraicGeometry.IsClosedImmersion j)
    (V : Y'.Opens) (F : ∀ W : Y'.Opens, W ≤ V → Γ(Y', W) → Γ(X', a' ⁻¹ᵁ W))
    (hnat : ∀ (W W' : Y'.Opens) (hW : W ≤ V) (h : W' ≤ W) (x : Γ(Y', W)),
      resOpen (a'.preimage_mono h) (F W hW x) = F W' (h.trans hW) (resOpen h x))
    (hadd : ∀ (W : Y'.Opens) (hW : W ≤ V) (x y : Γ(Y', W)),
      F W hW (x + y) = F W hW x + F W hW y)
    (hker : ∀ (W : Y'.Opens) (hW : W ≤ V) (x : Γ(Y', W)), (j.app W).hom x = 0 → F W hW x = 0)
    (s : Γ(Y, j ⁻¹ᵁ V)) :
    ∃! t : Γ(X', a' ⁻¹ᵁ V), ∀ (W : Y'.Opens) (hW : W ≤ V) (x : Γ(Y', W)),
      (j.app W).hom x = resOpen (j.preimage_mono hW) s →
        resOpen (a'.preimage_mono hW) t = F W hW x := by
  let := hj
  -- `F` is a group homomorphism on each open, hence constant on the fibres of `j.app`.
  have hsub : ∀ (W : Y'.Opens) (hW : W ≤ V) (x y : Γ(Y', W)),
      F W hW (x - y) = F W hW x - F W hW y := fun W hW =>
    map_sub (AddMonoidHom.mk' (F W hW) (hadd W hW))
  have hcongr : ∀ (W : Y'.Opens) (hW : W ≤ V) (x y : Γ(Y', W)),
      (j.app W).hom x = (j.app W).hom y → F W hW x = F W hW y := by
    intro W hW x y h
    have h0 : F W hW (x - y) = 0 := hker W hW _ (by rw [map_sub, h, sub_self])
    rw [hsub] at h0
    exact sub_eq_zero.mp h0
  -- Over an affine open of `V` a lift of `s` exists; choose one.
  have hlift : ∀ W : {W : Y'.Opens // W ≤ V ∧ IsAffineOpen W},
      ∃ x : Γ(Y', W.1), (j.app W.1).hom x = resOpen (j.preimage_mono W.2.1) s :=
    fun W => Scheme.Hom.app_surjective j W.1 W.2.2 _
  choose lift hlift using hlift
  -- The values on the chosen lifts are compatible, so they glue.
  have hcompat : TopCat.Presheaf.IsCompatible X'.presheaf
      (fun W : {W : Y'.Opens // W ≤ V ∧ IsAffineOpen W} => a' ⁻¹ᵁ W.1)
      (fun W => F W.1 W.2.1 (lift W)) := by
    intro W₁ W₂
    have e₁ := hnat W₁.1 (W₁.1 ⊓ W₂.1) W₁.2.1 inf_le_left (lift W₁)
    have e₂ := hnat W₂.1 (W₁.1 ⊓ W₂.1) W₂.2.1 inf_le_right (lift W₂)
    have hval : F (W₁.1 ⊓ W₂.1) (inf_le_left.trans W₁.2.1)
          (resOpen (inf_le_left : W₁.1 ⊓ W₂.1 ≤ W₁.1) (lift W₁))
        = F (W₁.1 ⊓ W₂.1) (inf_le_left.trans W₁.2.1)
          (resOpen (inf_le_right : W₁.1 ⊓ W₂.1 ≤ W₂.1) (lift W₂)) := by
      refine hcongr _ _ _ _ ?_
      rw [app_resOpen j inf_le_left (lift W₁), app_resOpen j inf_le_right (lift W₂),
        hlift W₁, hlift W₂, resOpen_resOpen, resOpen_resOpen]
    exact e₁.trans (hval.trans e₂.symm)
  have hcover : a' ⁻¹ᵁ V ≤
      ⨆ W : {W : Y'.Opens // W ≤ V ∧ IsAffineOpen W}, a' ⁻¹ᵁ (W.1 : Y'.Opens) := by
    have h1 : V ≤ ⨆ W : {W : Y'.Opens // W ≤ V ∧ IsAffineOpen W}, (W.1 : Y'.Opens) := by
      intro z hz
      obtain ⟨W, haff, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset hz
      exact Opens.mem_iSup.mpr ⟨⟨W, hWV, haff⟩, hzW⟩
    calc a' ⁻¹ᵁ V ≤ a' ⁻¹ᵁ (⨆ W : {W : Y'.Opens // W ≤ V ∧ IsAffineOpen W}, (W.1 : Y'.Opens)) :=
          a'.preimage_mono h1
      _ = _ := Scheme.Hom.preimage_iSup _ _
  obtain ⟨t, ht⟩ := TopCat.Sheaf.existsUnique_gluing' X'.sheaf
    (fun W : {W : Y'.Opens // W ≤ V ∧ IsAffineOpen W} => a' ⁻¹ᵁ W.1) (a' ⁻¹ᵁ V)
    (fun W => CategoryTheory.homOfLE (a'.preimage_mono W.2.1)) hcover
    (fun W => F W.1 W.2.1 (lift W)) hcompat
  -- The glued section has the stated property on every open, not only on the affine ones.
  have hgen : ∀ (W : Y'.Opens) (hW : W ≤ V) (x : Γ(Y', W)),
      (j.app W).hom x = resOpen (j.preimage_mono hW) s →
        resOpen (a'.preimage_mono hW) t = F W hW x := by
    intro W hW x hx
    refine section_ext_preimage a' (V := W) ?_
    intro W₀ hW₀W haff
    have hA : resOpen (a'.preimage_mono hW₀W) (resOpen (a'.preimage_mono hW) t)
        = F W₀ (hW₀W.trans hW) (lift ⟨W₀, hW₀W.trans hW, haff⟩) :=
      (resOpen_resOpen _ _ t).trans (ht.1 ⟨W₀, hW₀W.trans hW, haff⟩)
    have hB : resOpen (a'.preimage_mono hW₀W) (F W hW x)
        = F W₀ (hW₀W.trans hW) (resOpen hW₀W x) := hnat W W₀ hW hW₀W x
    have hC : F W₀ (hW₀W.trans hW) (lift ⟨W₀, hW₀W.trans hW, haff⟩)
        = F W₀ (hW₀W.trans hW) (resOpen hW₀W x) := by
      refine hcongr _ _ _ _ ?_
      rw [hlift ⟨W₀, hW₀W.trans hW, haff⟩, app_resOpen_eq_of_lift hW hW₀W hx]
    exact hA.trans (hC.trans hB.symm)
  refine ⟨t, hgen, fun t' ht' => ?_⟩
  refine section_ext_preimage a' (V := V) ?_
  intro W₀ hW₀V haff
  exact (ht' W₀ hW₀V (lift ⟨W₀, hW₀V, haff⟩) (hlift ⟨W₀, hW₀V, haff⟩)).trans
    (hgen W₀ hW₀V (lift ⟨W₀, hW₀V, haff⟩) (hlift ⟨W₀, hW₀V, haff⟩)).symm

/-! ### The derivation of [Stacks Project, Tag 04FG] -/

/-- A section of `𝒪_Y` over `j ⁻¹ᵁ W` lifts to `Γ(Y', W)` when `W` is affine: a closed immersion
is surjective on sections over an affine open. -/
theorem exists_lift (hj : IsFirstOrderThickening j) {V : Y'.Opens} (s : Γ(Y, j ⁻¹ᵁ V))
    {W : Y'.Opens} (hW : W ≤ V) (haff : IsAffineOpen W) :
    ∃ x : Γ(Y', W), (j.app W).hom x = resOpen (j.preimage_mono hW) s :=
  have := hj.1
  Scheme.Hom.app_surjective j W haff _

/-- A first-order thickening is surjective on points. -/
theorem surjective_base (hi : IsFirstOrderThickening i) : Function.Surjective i.base :=
  hi.isThickening.2

/-- **Hypothesis (1) of the source makes the two comorphisms comparable.** Since `a'` and `b'`
agree after precomposition with the thickening `i`, which is surjective on points, they have the
same underlying continuous map, so an open of `X'` lying over `V` for `a'` lies over `V` for
`b'`. This is `Stacks.Thickenings.preimage_eq_of_comm` with the two halves of
`IsFirstOrderThickening` split off. -/
theorem preimage_le_preimage (hi : IsFirstOrderThickening i) (comm_a : i ≫ a' = a ≫ j)
    (comm_b : i ≫ b' = a ≫ j) (V : Y'.Opens) : a' ⁻¹ᵁ V ≤ b' ⁻¹ᵁ V :=
  have := hi.1
  (preimage_eq_of_comm hi.2 comm_a comm_b V).ge

/-- **Hypothesis (2) makes the difference depend only on the image of the section in `𝒪_Y`.**
Two sections of `𝒪_{Y'}` with the same image under `j^♯` have the same difference. -/
theorem mapDifferenceLE_congr (hC : AgreeOnIdeal j a' b') {W : Y'.Opens} {U : X'.Opens}
    (hUa : U ≤ a' ⁻¹ᵁ W) (hUb : U ≤ b' ⁻¹ᵁ W) (x y : Γ(Y', W))
    (h : (j.app W).hom x = (j.app W).hom y) :
    mapDifferenceLE hUa hUb x = mapDifferenceLE hUa hUb y := by
  have h0 : mapDifferenceLE hUa hUb (x - y) = 0 := by
    rw [mapDifferenceLE, hC W U hUa hUb (x - y) (by rw [map_sub, h, sub_self]), sub_self]
  rw [mapDifferenceLE_sub] at h0
  exact sub_eq_zero.mp h0

/-- **Hypothesis (2) need only be checked on the affine opens of `Y'`.** `AgreeOnIdeal` is
therefore a local condition — a condition on a basis of opens — and not a stronger one than the
equality of the two induced maps of conormal sheaves that the source assumes. -/
theorem agreeOnIdeal_of_affine (hi : IsFirstOrderThickening i) (comm_a : i ≫ a' = a ≫ j)
    (comm_b : i ≫ b' = a ≫ j)
    (h : ∀ (W : Y'.Opens), IsAffineOpen W → ∀ y : Γ(Y', W), (j.app W).hom y = 0 →
      (a'.app W).hom y
        = (b'.appLE W (a' ⁻¹ᵁ W) (preimage_le_preimage hi comm_a comm_b W)).hom y) :
    AgreeOnIdeal j a' b' := by
  intro V U hUa hUb y hy
  have key : (a'.app V).hom y
      = (b'.appLE V (a' ⁻¹ᵁ V) (preimage_le_preimage hi comm_a comm_b V)).hom y := by
    refine section_ext_preimage a' (V := V) ?_
    intro W hW haff
    have hy' : (j.app W).hom (resOpen hW y) = 0 := by
      rw [app_resOpen j hW y, hy, resOpen_zero]
    have hL : resOpen (a'.preimage_mono hW) ((a'.app V).hom y) = (a'.app W).hom (resOpen hW y) :=
      (app_resOpen a' hW y).symm
    have hR : resOpen (a'.preimage_mono hW)
          ((b'.appLE V (a' ⁻¹ᵁ V) (preimage_le_preimage hi comm_a comm_b V)).hom y)
        = (b'.appLE W (a' ⁻¹ᵁ W)
            (preimage_le_preimage hi comm_a comm_b W)).hom (resOpen hW y) := by
      rw [appLE_eq_resOpen_app, appLE_eq_resOpen_app, resOpen_resOpen, app_resOpen b' hW y,
        resOpen_resOpen]
    rw [hL, hR]
    exact h W haff (resOpen hW y) hy'
  rw [appLE_eq_resOpen_app, key, appLE_eq_resOpen_app, appLE_eq_resOpen_app, resOpen_resOpen]

/-- **The difference of the two comorphisms descends to the sections of `𝒪_Y`.** For every open
`V` of `Y'` and every section `s` of `𝒪_Y` over `j ⁻¹ᵁ V` there is exactly one section of
`a_*𝒪_{X'}` over `V` whose restriction to `a' ⁻¹ᵁ W`, for every `W ≤ V` carrying a lift `x` of
`s`, is `(a')^♯ x - (b')^♯ x`.

This is [Stacks Project, Tag 04FG] stripped of its algebraic structure: it is the existence and
uniqueness of the map `D` in the factorization. -/
theorem existsUnique_mapDifferenceSheaf (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (hC : AgreeOnIdeal j a' b') (V : Y'.Opens) (s : Γ(Y, j ⁻¹ᵁ V)) :
    ∃! t : Γ(X', a' ⁻¹ᵁ V), ∀ (W : Y'.Opens) (hW : W ≤ V) (x : Γ(Y', W)),
      (j.app W).hom x = resOpen (j.preimage_mono hW) s →
        resOpen (a'.preimage_mono hW) t
          = mapDifferenceLE (le_refl (a' ⁻¹ᵁ W)) (preimage_le_preimage hi comm_a comm_b W) x := by
  refine existsUnique_descendAlongIdeal hj.1 V
    (fun W _ x =>
      mapDifferenceLE (le_refl (a' ⁻¹ᵁ W)) (preimage_le_preimage hi comm_a comm_b W) x)
    (fun W W' _ h x => ?_) (fun W _ x y => mapDifferenceLE_add _ _ x y) (fun W _ x hx => ?_) s
  · rw [mapDifferenceLE_resOpen, mapDifferenceLE_map]
  · rw [mapDifferenceLE,
      hC W (a' ⁻¹ᵁ W) (le_refl (a' ⁻¹ᵁ W)) (preimage_le_preimage hi comm_a comm_b W) x hx,
      sub_self]

/-- **The derivation `D` of [Stacks Project, Tag 04FG].** For an open `V` of `Y'` this is the map
`Γ(Y, j ⁻¹ᵁ V) → Γ(X', a' ⁻¹ᵁ V)`, that is `𝒪_Y ⟶ a_*𝒞_{X/X'}` on sections over `V`, through
which `(a')^♯ - (b')^♯` factors. It is characterised by
`Stacks.Thickenings.mapDifferenceSheaf_spec`. -/
@[stacks 04FG "the derivation D"]
noncomputable def mapDifferenceSheaf (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (hC : AgreeOnIdeal j a' b') (V : Y'.Opens) (s : Γ(Y, j ⁻¹ᵁ V)) : Γ(X', a' ⁻¹ᵁ V) :=
  (existsUnique_mapDifferenceSheaf hi hj comm_a comm_b hC V s).choose

/-- **The characterising property of `Stacks.Thickenings.mapDifferenceSheaf`.** On an open `W`
carrying a lift `x` of `s` the value of `D` restricts to `(a')^♯ x - (b')^♯ x`. -/
theorem mapDifferenceSheaf_spec (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (hC : AgreeOnIdeal j a' b')
    (V : Y'.Opens) (s : Γ(Y, j ⁻¹ᵁ V)) (W : Y'.Opens) (hW : W ≤ V) (x : Γ(Y', W))
    (hx : (j.app W).hom x = resOpen (j.preimage_mono hW) s) :
    resOpen (a'.preimage_mono hW) (mapDifferenceSheaf hi hj comm_a comm_b hC V s)
      = mapDifferenceLE (le_refl (a' ⁻¹ᵁ W)) (preimage_le_preimage hi comm_a comm_b W) x :=
  (existsUnique_mapDifferenceSheaf hi hj comm_a comm_b hC V s).choose_spec.1 W hW x hx

/-- `Stacks.Thickenings.mapDifferenceSheaf` is the only section with that property. -/
theorem eq_mapDifferenceSheaf (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (hC : AgreeOnIdeal j a' b')
    (V : Y'.Opens) (s : Γ(Y, j ⁻¹ᵁ V)) (t : Γ(X', a' ⁻¹ᵁ V))
    (ht : ∀ (W : Y'.Opens) (hW : W ≤ V) (x : Γ(Y', W)),
      (j.app W).hom x = resOpen (j.preimage_mono hW) s →
        resOpen (a'.preimage_mono hW) t
          = mapDifferenceLE (le_refl (a' ⁻¹ᵁ W)) (preimage_le_preimage hi comm_a comm_b W) x) :
    t = mapDifferenceSheaf hi hj comm_a comm_b hC V s :=
  (existsUnique_mapDifferenceSheaf hi hj comm_a comm_b hC V s).choose_spec.2 t ht

/-- **Checking the characterising property on affine opens is enough.** This is the form of
uniqueness every algebraic property of `D` is proved with: on an affine open a lift of any
section of `𝒪_Y` can be chosen, which is what makes the computation possible. -/
theorem eq_mapDifferenceSheaf_of_affine (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (hC : AgreeOnIdeal j a' b') (V : Y'.Opens) (s : Γ(Y, j ⁻¹ᵁ V)) (t : Γ(X', a' ⁻¹ᵁ V))
    (ht : ∀ (W : Y'.Opens) (hW : W ≤ V), IsAffineOpen W → ∀ x : Γ(Y', W),
      (j.app W).hom x = resOpen (j.preimage_mono hW) s →
        resOpen (a'.preimage_mono hW) t
          = mapDifferenceLE (le_refl (a' ⁻¹ᵁ W)) (preimage_le_preimage hi comm_a comm_b W) x) :
    t = mapDifferenceSheaf hi hj comm_a comm_b hC V s := by
  refine eq_mapDifferenceSheaf hi hj comm_a comm_b hC V s t fun W hW x hx => ?_
  refine section_ext_preimage a' (V := W) ?_
  intro W₀ hW₀W haff
  have hA := ht W₀ (hW₀W.trans hW) haff (resOpen hW₀W x) (app_resOpen_eq_of_lift hW hW₀W hx)
  rw [resOpen_resOpen, hA, mapDifferenceLE_resOpen, mapDifferenceLE_map]

/-- **The factorization of [Stacks Project, Tag 04FG].** The difference of the two comorphisms on
`Γ(Y', V)` is the composite of `j^♯ : 𝒪_{Y'} ⟶ 𝒪_Y` with the derivation `D`. -/
@[stacks 04FG "the factorization"]
theorem mapDifferenceSheaf_app (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (hC : AgreeOnIdeal j a' b')
    (V : Y'.Opens) (x : Γ(Y', V)) :
    mapDifferenceSheaf hi hj comm_a comm_b hC V ((j.app V).hom x)
      = mapDifferenceLE (le_refl (a' ⁻¹ᵁ V)) (preimage_le_preimage hi comm_a comm_b V) x := by
  have h := mapDifferenceSheaf_spec hi hj comm_a comm_b hC V ((j.app V).hom x) V le_rfl x
    (by rw [resOpen_self])
  rwa [resOpen_self] at h

/-- **The derivation takes values in the conormal sheaf.** The value of `D` is killed by the
comorphism of `i`, i.e. it is a section of the defining ideal of `X ⊂ X'`, which for a first-order
thickening is `𝒞_{X/X'}`. This is what makes the factorization of
`Stacks.Thickenings.mapDifferenceSheaf_app` pass through `a_*𝒞_{X/X'}` and not merely through
`a_*𝒪_{X'}`. -/
@[stacks 04FG "the factorization passes through the conormal sheaf"]
theorem app_mapDifferenceSheaf (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (hC : AgreeOnIdeal j a' b')
    (V : Y'.Opens) (s : Γ(Y, j ⁻¹ᵁ V)) :
    (i.app (a' ⁻¹ᵁ V)).hom (mapDifferenceSheaf hi hj comm_a comm_b hC V s) = 0 := by
  refine section_ext_preimage (i ≫ a') (V := V) ?_
  intro W hW haff
  obtain ⟨x, hx⟩ := exists_lift hj s hW haff
  have h1 : resOpen ((i ≫ a').preimage_mono hW)
        ((i.app (a' ⁻¹ᵁ V)).hom (mapDifferenceSheaf hi hj comm_a comm_b hC V s))
      = (i.app (a' ⁻¹ᵁ W)).hom
        (resOpen (a'.preimage_mono hW) (mapDifferenceSheaf hi hj comm_a comm_b hC V s)) :=
    (app_resOpen i (a'.preimage_mono hW) _).symm
  rw [h1, mapDifferenceSheaf_spec hi hj comm_a comm_b hC V s W hW x hx,
    app_mapDifferenceLE comm_a comm_b]
  exact (map_zero (X.presheaf.map (CategoryTheory.homOfLE
    ((i ≫ a').preimage_mono hW)).op).hom).symm

/-- **`D` is a map of sheaves**: it commutes with restriction. -/
@[stacks 04FG "D is a map of sheaves"]
theorem mapDifferenceSheaf_map (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (hC : AgreeOnIdeal j a' b')
    {V V' : Y'.Opens} (hV : V' ≤ V) (s : Γ(Y, j ⁻¹ᵁ V)) :
    resOpen (a'.preimage_mono hV) (mapDifferenceSheaf hi hj comm_a comm_b hC V s)
      = mapDifferenceSheaf hi hj comm_a comm_b hC V' (resOpen (j.preimage_mono hV) s) := by
  refine eq_mapDifferenceSheaf hi hj comm_a comm_b hC V' _ _ fun W hW x hx => ?_
  rw [resOpen_resOpen]
  refine mapDifferenceSheaf_spec hi hj comm_a comm_b hC V s W (hW.trans hV) x ?_
  rw [hx, resOpen_resOpen]

/-- **`D` is additive.** -/
@[stacks 04FG "D is additive"]
theorem mapDifferenceSheaf_add (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (hC : AgreeOnIdeal j a' b')
    (V : Y'.Opens) (s t : Γ(Y, j ⁻¹ᵁ V)) :
    mapDifferenceSheaf hi hj comm_a comm_b hC V (s + t)
      = mapDifferenceSheaf hi hj comm_a comm_b hC V s
        + mapDifferenceSheaf hi hj comm_a comm_b hC V t := by
  refine (eq_mapDifferenceSheaf_of_affine hi hj comm_a comm_b hC V (s + t) _
    fun W hW haff x hx => ?_).symm
  obtain ⟨u, hu⟩ := exists_lift hj s hW haff
  obtain ⟨v, hv⟩ := exists_lift hj t hW haff
  have hlift : (j.app W).hom (u + v) = resOpen (j.preimage_mono hW) (s + t) := by
    rw [map_add, hu, hv, resOpen_add]
  rw [resOpen_add, mapDifferenceSheaf_spec hi hj comm_a comm_b hC V s W hW u hu,
    mapDifferenceSheaf_spec hi hj comm_a comm_b hC V t W hW v hv,
    mapDifferenceLE_congr hC _ _ x (u + v) (hx.trans hlift.symm), mapDifferenceLE_add]

/-- **`D` kills the sections pulled back from the base.** This is `𝒪_S`-linearity: a section of
`𝒪_S` over an open `Z` of `S` pulls back to a section of `𝒪_Y` over `j ⁻¹ᵁ V` for `V ≤ q ⁻¹ᵁ Z`,
and `D` vanishes on it, because the two lifts `a'` and `b'` are morphisms over `S` and therefore
agree on sections coming from `S`. -/
@[stacks 04FG "D is 𝒪_S-linear"]
theorem mapDifferenceSheaf_appLE_base (hi : IsFirstOrderThickening i)
    (hj : IsFirstOrderThickening j) (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (hC : AgreeOnIdeal j a' b') (ha' : a' ≫ q = p) (hb' : b' ≫ q = p) {Z : S.Opens}
    {V : Y'.Opens} (hV : V ≤ q ⁻¹ᵁ Z) (hjV : j ⁻¹ᵁ V ≤ (j ≫ q) ⁻¹ᵁ Z) (r : Γ(S, Z)) :
    mapDifferenceSheaf hi hj comm_a comm_b hC V
        (((j ≫ q).appLE Z (j ⁻¹ᵁ V) hjV).hom r) = 0 := by
  refine (eq_mapDifferenceSheaf_of_affine hi hj comm_a comm_b hC V _ 0
    fun W hW _ x hx => ?_).symm
  have hWZ : W ≤ q ⁻¹ᵁ Z := hW.trans hV
  have hy : (j.app W).hom ((q.appLE Z W hWZ).hom r)
      = resOpen (j.preimage_mono hW) (((j ≫ q).appLE Z (j ⁻¹ᵁ V) hjV).hom r) := by
    have h1 := congr($(Scheme.Hom.appLE_comp_appLE j q Z W (j ⁻¹ᵁ W) hWZ
      (le_refl (j ⁻¹ᵁ W))).hom r)
    have h2 := congr($((j ≫ q).appLE_map hjV (CategoryTheory.homOfLE
      (j.preimage_mono hW)).op).hom r)
    rw [CommRingCat.comp_apply, Scheme.Hom.appLE_eq_app] at h1
    rw [CommRingCat.comp_apply] at h2
    rw [h1, ← h2]
  have hzero : mapDifferenceLE (le_refl (a' ⁻¹ᵁ W))
      (preimage_le_preimage hi comm_a comm_b W) ((q.appLE Z W hWZ).hom r) = 0 := by
    have hA := congr($(Scheme.Hom.appLE_comp_appLE a' q Z W (a' ⁻¹ᵁ W) hWZ
      (le_refl (a' ⁻¹ᵁ W))).hom r)
    have hB := congr($(Scheme.Hom.appLE_comp_appLE b' q Z W (a' ⁻¹ᵁ W) hWZ
      (preimage_le_preimage hi comm_a comm_b W)).hom r)
    rw [CommRingCat.comp_apply] at hA hB
    have hpa : a' ⁻¹ᵁ W ≤ p ⁻¹ᵁ Z := by
      rw [← ha']
      exact a'.preimage_mono hWZ
    rw [mapDifferenceLE, hA, hB, appLE_congr_hom ha' _ _ _ hpa,
      appLE_congr_hom hb' _ _ _ hpa, sub_self]
  rw [resOpen_zero,
    mapDifferenceLE_congr hC _ _ x ((q.appLE Z W hWZ).hom r) (hx.trans hy.symm), hzero]

/-! ### The action of `𝒪_Y` on the conormal sheaf, and the Leibniz rule -/

/-- A section of `𝒪_{Y'}` killed by `j^♯` pulls back to a section of the defining ideal of `i`:
its image under `(a')^♯` is killed by `i^♯`, because `i ≫ a' = a ≫ j`. -/
theorem app_app_eq_zero_of_comm (comm_a : i ≫ a' = a ≫ j) {W : Y'.Opens} {x : Γ(Y', W)}
    (hx : (j.app W).hom x = 0) : (i.app (a' ⁻¹ᵁ W)).hom ((a'.app W).hom x) = 0 := by
  have hg : (i ≫ a') ⁻¹ᵁ W ≤ (i ≫ a') ⁻¹ᵁ W := le_rfl
  have hg' : (i ≫ a') ⁻¹ᵁ W ≤ (a ≫ j) ⁻¹ᵁ W :=
    le_of_eq (congrArg (fun f : X ⟶ Y' => f ⁻¹ᵁ W) comm_a)
  have h := resOpen_app_congr comm_a hg hg' x
  have h0 : ((a ≫ j).app W).hom x = 0 := by
    change (a.app (j ⁻¹ᵁ W)).hom ((j.app W).hom x) = 0
    rw [hx, map_zero]
  rw [h0, resOpen_zero, resOpen_self] at h
  exact h

/-- **The action of a section of `𝒪_{Y'}` on the conormal sheaf descends to `𝒪_Y`.** A section
`c` of the defining ideal of `i` over `a' ⁻¹ᵁ V` is multiplied by the pullback of a section of
`𝒪_{Y'}` along `a'`; a section killed by `j^♯` acts as zero, because its pullback lies in the
defining ideal of `i` and that ideal is square-zero. So the action descends along `j^♯`, and the
descended action is again determined by gluing.

This is the `𝒪_Y`-module structure on `a_*𝒞_{X/X'}` that the Leibniz rule of
[Stacks Project, Tag 04FG] is stated for; it is the sheaf form of
`Stacks.Thickenings.conormalModuleAlong`. -/
theorem existsUnique_conormalSmul (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (V : Y'.Opens) (c : Γ(X', a' ⁻¹ᵁ V))
    (hc : (i.app (a' ⁻¹ᵁ V)).hom c = 0) (s : Γ(Y, j ⁻¹ᵁ V)) :
    ∃! t : Γ(X', a' ⁻¹ᵁ V), ∀ (W : Y'.Opens) (hW : W ≤ V) (x : Γ(Y', W)),
      (j.app W).hom x = resOpen (j.preimage_mono hW) s →
        resOpen (a'.preimage_mono hW) t
          = (a'.app W).hom x * resOpen (a'.preimage_mono hW) c := by
  refine existsUnique_descendAlongIdeal hj.1 V
    (fun W hW x => (a'.app W).hom x * resOpen (a'.preimage_mono hW) c)
    (fun W W' hW h x => ?_) (fun W hW x y => ?_) (fun W hW x hx => ?_) s
  · rw [resOpen_mul, app_resOpen a' h x, resOpen_resOpen]
  · rw [map_add]
    ring
  · refine mul_eq_zero_of_app_eq_zero hi (a' ⁻¹ᵁ W) _ _ (app_app_eq_zero_of_comm comm_a hx) ?_
    rw [app_resOpen i (a'.preimage_mono hW) c, hc, resOpen_zero]

/-- **The action of `𝒪_Y` on `a_*𝒞_{X/X'}`.** See
`Stacks.Thickenings.existsUnique_conormalSmul`. -/
noncomputable def conormalSmul (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (V : Y'.Opens) (c : Γ(X', a' ⁻¹ᵁ V))
    (hc : (i.app (a' ⁻¹ᵁ V)).hom c = 0) (s : Γ(Y, j ⁻¹ᵁ V)) : Γ(X', a' ⁻¹ᵁ V) :=
  (existsUnique_conormalSmul hi hj comm_a V c hc s).choose

/-- The characterising property of `Stacks.Thickenings.conormalSmul`: on an open carrying a lift
of `s` the action is multiplication by the pullback of that lift. -/
theorem conormalSmul_spec (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (V : Y'.Opens) (c : Γ(X', a' ⁻¹ᵁ V))
    (hc : (i.app (a' ⁻¹ᵁ V)).hom c = 0) (s : Γ(Y, j ⁻¹ᵁ V)) (W : Y'.Opens) (hW : W ≤ V)
    (x : Γ(Y', W)) (hx : (j.app W).hom x = resOpen (j.preimage_mono hW) s) :
    resOpen (a'.preimage_mono hW) (conormalSmul hi hj comm_a V c hc s)
      = (a'.app W).hom x * resOpen (a'.preimage_mono hW) c :=
  (existsUnique_conormalSmul hi hj comm_a V c hc s).choose_spec.1 W hW x hx

/-- **The Leibniz rule for `D`.** This is the last clause of [Stacks Project, Tag 04FG]: together
with `Stacks.Thickenings.mapDifferenceSheaf_add` and
`Stacks.Thickenings.mapDifferenceSheaf_appLE_base` it says that `D` is an `𝒪_S`-derivation of
`𝒪_Y` with values in `a_*𝒞_{X/X'}`.

The proof is the computation of the affine case, read on an affine open of `Y'` after lifting the
two sections: the difference of the two comorphisms on a product is
`Δ(u)·(a')^♯ v + (b')^♯ u·Δ(v)`, and this agrees with `(a')^♯ u·Δ(v) + (a')^♯ v·Δ(u)` because the
two differences lie in the defining ideal of `i`, whose square vanishes. -/
@[stacks 04FG "the Leibniz rule for D"]
theorem mapDifferenceSheaf_mul (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j) (hC : AgreeOnIdeal j a' b')
    (V : Y'.Opens) (s t : Γ(Y, j ⁻¹ᵁ V)) :
    mapDifferenceSheaf hi hj comm_a comm_b hC V (s * t)
      = conormalSmul hi hj comm_a V (mapDifferenceSheaf hi hj comm_a comm_b hC V t)
            (app_mapDifferenceSheaf hi hj comm_a comm_b hC V t) s
        + conormalSmul hi hj comm_a V (mapDifferenceSheaf hi hj comm_a comm_b hC V s)
            (app_mapDifferenceSheaf hi hj comm_a comm_b hC V s) t := by
  refine (eq_mapDifferenceSheaf_of_affine hi hj comm_a comm_b hC V (s * t) _
    fun W hW haff x hx => ?_).symm
  obtain ⟨u, hu⟩ := exists_lift hj s hW haff
  obtain ⟨v, hv⟩ := exists_lift hj t hW haff
  have hlift : (j.app W).hom (u * v) = resOpen (j.preimage_mono hW) (s * t) := by
    rw [map_mul, hu, hv, resOpen_mul]
  -- the two values of `D`, restricted to `W`
  have hDs := mapDifferenceSheaf_spec hi hj comm_a comm_b hC V s W hW u hu
  have hDt := mapDifferenceSheaf_spec hi hj comm_a comm_b hC V t W hW v hv
  -- the two differences lie in the square-zero defining ideal of `i`
  have hz : mapDifferenceLE (le_refl (a' ⁻¹ᵁ W)) (preimage_le_preimage hi comm_a comm_b W) u
      * mapDifferenceLE (le_refl (a' ⁻¹ᵁ W)) (preimage_le_preimage hi comm_a comm_b W) v = 0 :=
    mul_eq_zero_of_app_eq_zero hi (a' ⁻¹ᵁ W) _ _ (app_mapDifferenceLE comm_a comm_b _ _ u)
      (app_mapDifferenceLE comm_a comm_b _ _ v)
  rw [resOpen_add, conormalSmul_spec hi hj comm_a V _ _ s W hW u hu,
    conormalSmul_spec hi hj comm_a V _ _ t W hW v hv, hDs, hDt,
    mapDifferenceLE_congr hC _ _ x (u * v) (hx.trans hlift.symm)]
  have ha : (a'.app W).hom u
      = (a'.appLE W (a' ⁻¹ᵁ W) (le_refl (a' ⁻¹ᵁ W))).hom u := by
    rw [Scheme.Hom.appLE_eq_app]
  have hb : (a'.app W).hom v
      = (a'.appLE W (a' ⁻¹ᵁ W) (le_refl (a' ⁻¹ᵁ W))).hom v := by
    rw [Scheme.Hom.appLE_eq_app]
  simp only [mapDifferenceLE, map_mul, ha, hb] at hz ⊢
  linear_combination hz

end Stacks.Thickenings

end
