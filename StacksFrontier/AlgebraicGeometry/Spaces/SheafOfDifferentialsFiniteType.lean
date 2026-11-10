module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteFromGeneratingSections
public import Mathlib.RingTheory.Kaehler.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of differentials of a morphism locally of finite type is of finite type

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Stacks 05ZE asserts that
`Ω_{X/Y}` is a finite type `𝒪_X`-module when `f` is locally of finite type.

The proof here is not the source's.  The source reduces to the scheme case, Morphisms,
Lemma 01V2, by the étale localization of Stacks 04CU; that route needs the identification of
`Ω_{X/Y}|_{U_étale}` with the *Zariski* sheaf of differentials of a morphism of schemes, which
is the final sentence of Stacks 04CU and is not available in this development.  Instead the
finite generation is read off the construction of `Ω_{X/Y}` as the sheafification of the
presheaf of sectionwise Kähler differentials of `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`:

* a Leibniz additive map on `𝒪_X(W)` which kills the image of `𝒪_X(V)` under restriction along
  an arrow `W ⟶ V` of the small étale site is zero as soon as `Ω_{𝒪_X(W)/𝒪_X(V)}` vanishes,
  because it is then an `𝒪_X(V)`-derivation; applied to the universal derivation composed with
  the projection onto a quotient this says that `d_{X/Y}` of *every* section over `W` lies in
  the `𝒪_X(W)`-span of the `d_{X/Y}` of the restrictions of the sections over `V`
  (`AlgebraicGeometry.Space.universalDerivation_mem_span_restrict_of_subsingleton`), and
  `Ω_{𝒪_X(W)/𝒪_X(V)}` does vanish when both charts are affine, which is Algebra, Lemma 00UU
  (`AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_chartRing_of_affineChart`);
* if `𝒪_X(V)` is generated as an `(f⁻¹𝒪_Y)(V)`-algebra by finitely many sections `y₁, …, yₙ`
  then an `Algebra.adjoin` induction cuts that span down to the span of `d_{X/Y}(yᵢ|_W)`, since
  `d_{X/Y}` kills the image of `f⁻¹𝒪_Y` and satisfies the Leibniz rule
  (`AlgebraicGeometry.Space.universalDerivation_restrict_mem_span_of_adjoin`);
* a section of `Ω_{X/Y}` over any object is, on a covering sieve, the image of a sectionwise
  Kähler differential, because the unit of sheafification is locally surjective, and a
  sectionwise Kähler differential is an `𝒪_X`-combination of `d_{X/Y}` of sections
  (`AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation`).

Together these say that on each affine member of a covering the sections `d_{X/Y}(yᵢ)` generate
`Ω_{X/Y}` locally, which is exactly the hypothesis of
`Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_sections`, and hence
`SheafOfModules.IsFiniteTypeOnSite`.

## The chart-algebra condition

`AlgebraicGeometry.Space.HasFiniteTypeAffineChartAlgebras` is the sheaf-theoretic content of
"`f` is locally of finite type": every object of the small étale site of `X` has a covering
family whose members have affine underlying scheme and over each of which the ring of sections
`𝒪_X(V)` is generated as an `(f⁻¹𝒪_Y)(V)`-algebra by finitely many sections.  This development
defines `AlgebraicGeometry.Space.IsLocallyOfFiniteType` (Stacks 03XF(1)) by transporting
`AlgebraicGeometry.LocallyOfFiniteType` across étale scheme charts, and the passage from that
definition to this condition is Stacks 03XF(1) applied to a square of *affine* étale charts
together with the chart description of `f⁻¹𝒪_Y`.  It is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsFiniteTypeChartBridge.lean`
(`AlgebraicGeometry.Space.hasFiniteTypeAffineChartAlgebras_of_isLocallyOfFiniteType`), which is
downstream of this file because it consumes
`AlgebraicGeometry.Space.exists_adjoin_inverseImage_of_square`; the statement of Stacks 05ZE at
the source's hypothesis and with nothing else assumed is there too
(`Space.isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_unconditional`).

Unramifiedness of the transition maps of the small étale site — Algebra, Lemma 00UU — is carried
by the first group of statements below as
`AlgebraicGeometry.Space.HasUnramifiedChartTransitions`, which is **false** as stated; the
second group does not carry it, because Lemma 00UU is proved for the arrows those proofs
restrict along.  See the implementation notes.

## Main results

* `AlgebraicGeometry.Space.universalDerivation_mem_span_restrict_of_subsingleton`: when the
  transition map `W ⟶ V` has vanishing module of differentials, `d_{X/Y}` of any section over
  `W` lies in any submodule containing `d_{X/Y}` of the restrictions from `V`.
* `AlgebraicGeometry.Space.universalDerivation_restrict_mem_span_of_adjoin`: the
  `Algebra.adjoin` induction.
* `AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation`: every section of
  `Ω_{X/Y}` is locally an `𝒪_X`-combination of universal differentials.
* `AlgebraicGeometry.Space.span_le_span_universalDerivation_restrict`: **the étale-local
  reduction step**, shared with Stacks 05ZF — over a chart whose transition map has vanishing
  module of differentials, every universal differential is a combination of the
  `d_{X/Y}(yᵢ|_·)`.
* `AlgebraicGeometry.Space.hasFiniteGlobalGenerators_sheafOfDifferentials_over` and
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials`,
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType`:
  **the generators half and Stacks 05ZE** carrying
  `AlgebraicGeometry.Space.HasUnramifiedChartTransitions` and the sieve form of the
  chart-algebra condition, as the source's statement is carried here.
* `AlgebraicGeometry.Space.hasFiniteGlobalGenerators_sheafOfDifferentials_over_of_isAffine`:
  **the generators half** — on a chart with affine underlying scheme, `Ω_{X/Y}` is generated by
  the finitely many sections `d_{X/Y}(yᵢ)` in the sense of Stacks 03DE(5), with no
  unramifiedness hypothesis.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_sheafOfDifferentials_of_affineChartAlgebras`: the
  finite type of `Ω_{X/Y}` from the chart-algebra condition on a covering by affine charts, with
  no unramifiedness hypothesis.  Composed with
  `AlgebraicGeometry.Space.hasFiniteTypeAffineChartAlgebras_of_isLocallyOfFiniteType` it gives
  Stacks 05ZE at the source's hypothesis and with nothing else assumed; that composite is
  `Space.isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_unconditional`,
  in `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsFiniteTypeChartBridge.lean`.
* `AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation_restrict`: **the generators
  half of Stacks 04CV** — `Ω_{X/Y}|_V` is locally generated by the universal differentials of
  the sections of `𝒪_X` over `V`, from `hunram` alone.  Quasi-coherence needs in
  addition the relations half of Descent, Proposition 03DX(2), which this development carries as
  a hypothesis (`hrel` of
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_of_rel`) and does
  not prove; no 04CV attribute is claimed here.

## Implementation notes

**Why Algebra, Lemma 00UU is proved rather than assumed, and what that cost.**
`AlgebraicGeometry.Space.HasUnramifiedChartTransitions` asserts `Ω[𝒪_X(W)⁄𝒪_X(V)] = 0` for
*every* arrow `W ⟶ V` of the small étale site, and that is false: the objects of
`AlgebraicGeometry.Space.SmallEtale` are étale charts with arbitrary underlying scheme, so for
`X = P¹_k` over `S = Spec k`, `V` the identity chart and `W` the open immersion `A¹ ↪ P¹` — both
étale charts, the arrow between them an open immersion — one has `𝒪_X(V) = k`,
`𝒪_X(W) = k[t]`, and `Ω[k[t]⁄k]` is free of rank one.  Lemma 00UU applies to an arrow between
*affine* charts, where the restriction map is an étale ring map
(`AlgebraicGeometry.Space.etale_chartRestrict_of_affineChart`), and
`AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_chartRing_of_affineChart` is the whole
of it.

Using it therefore means never restricting along an arrow out of a non-affine chart, and two
places needed changing.  The chart `V` of the generators half is required to be affine, so the
carried hypothesis quantifies over a covering *family* of affine charts rather than over all
arrows of a covering sieve.  And the covering sieve witnessing local generation inside
`AlgebraicGeometry.Space.hasFiniteGlobalGenerators_sheafOfDifferentials_over_of_isAffine` can no
longer be the transport of the sieve of
`AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation`, whose arrows have arbitrary
source; it is instead `Stacks.Sheaves.LocalGeneration.spanSieve`, the sieve of *all* arrows at
which the conclusion already holds, which covers by
`CategoryTheory.GrothendieckTopology.transitive` applied to the affine refinement
`AlgebraicGeometry.Space.SmallEtale.exists_affine_ofArrows_over`.

**How `HasFiniteTypeAffineChartAlgebras` is derived from
`AlgebraicGeometry.Space.IsLocallyOfFiniteType`.**  Two inputs, both available.  The covering of
every object of the small étale site of `X` by affine charts each admitting a morphism to an
affine étale chart of `Y` commuting with `f` is Stacks 03G2 in the form
`AlgebraicGeometry.Space.exists_affine_chartDiagram_ofArrows`; it is what makes the chart
condition of Stacks 03XF(1) applicable, and with both charts affine that gives a finite type ring
map `𝒪_Y(W) ⟶ 𝒪_X(V)`.  The chart-level comparison `𝒪_Y(W) ⟶ (f⁻¹𝒪_Y)(V)` attached to such a
square is the unit of the inverse-image adjunction read through the chart correspondence of
Stacks 03G8, whose composite with `f♯` is that ring map; that is
`AlgebraicGeometry.Space.structureSharpInverseImage_chartDiagramInverseImageSection`.  Both, and
the assembly, are in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsFiniteTypeChartBridge.lean`.

`attribute [local instance_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite` is in force
from the generators half onwards: `AlgebraicGeometry.Space.smallEtaleRingedSite` is a plain
definition, so instance search does not unfold its `C` field, and without it `Over V` has no
`Category` instance at the spelling in which the statements about the slice are written.

`Stacks.KaehlerDifferential.mem_of_subsingleton_kaehlerDifferential` is stated for a bare
`AddMonoidHom` with the Leibniz rule rather than for a `Derivation`: the universal derivation of
`Ω_{X/Y}` is a `PresheafOfModules.Derivation'`, whose `d` field is an `AddMonoidHom` over the
*sections of `f⁻¹𝒪_Y`*, and the ring over which it must be seen as a derivation in order to
apply the vanishing of `Ω_{𝒪_X(W)/𝒪_X(V)}` is `𝒪_X(V)`, a different ring.  The derivation over
`𝒪_X(V)` is built inside that lemma, on the quotient by the submodule.

## References

* [Stacks Project, Tag 05ZE](https://stacks.math.columbia.edu/tag/05ZE)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal derivation.
* [Stacks Project, Tag 01V2](https://stacks.math.columbia.edu/tag/01V2), the scheme case, which
  the source reduces to.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale localization
  the source's reduction uses.
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF), locally of finite type
  for morphisms of algebraic spaces.
* [Stacks Project, Tag 00UU](https://stacks.math.columbia.edu/tag/00UU), unramified ring maps;
  brought to the transition maps between affine charts of this site in
  `StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsEtale`.
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL), part (5), finite type
  modules on a site.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace Stacks.KaehlerDifferential

/-- **A Leibniz additive map killing a subring with vanishing differentials is trapped in any
submodule containing its values on that subring.**

Let `A ⟶ C` be a ring map with `Ω[C⁄A] = 0`, let `M` be a `C`-module and let `D : C →+ M`
satisfy the Leibniz rule.  If a `C`-submodule `N` of `M` contains `D (algebraMap A C a)` for
every `a`, then it contains `D c` for every `c`.

Composing `D` with the projection `M ⟶ M ⧸ N` gives an `A`-derivation which kills the image of
`A`, hence is `A`-linear for the `A`-module structure on `M ⧸ N` obtained by restricting
scalars, so it is an `A`-derivation of `C`; it therefore factors through `Ω[C⁄A] = 0`. -/
theorem mem_of_subsingleton_kaehlerDifferential
    {A : Type u} {C : Type v} [CommRing A] [CommRing C] [Algebra A C]
    [Subsingleton (_root_.KaehlerDifferential A C)]
    {M : Type*} [AddCommGroup M] [Module C M] (D : C →+ M)
    (hleib : ∀ a b : C, D (a * b) = a • D b + b • D a)
    (N : Submodule C M) (hN : ∀ a : A, D (algebraMap A C a) ∈ N) (c : C) :
    D c ∈ N := by
  let _i : Module A (M ⧸ N) := Module.compHom _ (algebraMap A C)
  have _t : IsScalarTower A C (M ⧸ N) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hq : ∀ a : A, N.mkQ (D (algebraMap A C a)) = 0 :=
    fun a => (Submodule.Quotient.mk_eq_zero N).2 (hN a)
  let D' : Derivation A C (M ⧸ N) :=
    { toFun := fun c => N.mkQ (D c)
      map_add' := fun x y => by
        change N.mkQ (D (x + y)) = N.mkQ (D x) + N.mkQ (D y)
        rw [map_add, map_add]
      map_smul' := fun a x => by
        change N.mkQ (D (a • x)) = a • N.mkQ (D x)
        rw [Algebra.smul_def, hleib, map_add, map_smul, map_smul, hq a, smul_zero,
          add_zero]
        rfl
      map_one_eq_zero' := by
        change N.mkQ (D 1) = 0
        rw [show (1 : C) = algebraMap A C 1 from (map_one _).symm]
        exact hq 1
      leibniz' := fun x y => by
        change N.mkQ (D (x * y)) = x • N.mkQ (D y) + y • N.mkQ (D x)
        rw [hleib, map_add, map_smul, map_smul] }
  have key : D'.liftKaehlerDifferential (_root_.KaehlerDifferential.D A C c) = D' c :=
    DFunLike.congr_fun D'.liftKaehlerDifferential_comp c
  have hzero : (_root_.KaehlerDifferential.D A C) c = 0 := Subsingleton.elim _ _
  have hD' : D' c = 0 := by rw [← key, hzero, map_zero]
  exact (Submodule.Quotient.mk_eq_zero N).1 hD'

/-- Membership in a submodule transported along an equality of elements, with the submodule an
explicit argument.  Taking it explicitly fixes the ambient module before the equality is
elaborated, which is what makes this usable by `exact` where `rewrite` cannot form a motive: the
sections of `Ω_{X/Y}` carry two definitionally equal but syntactically different spellings, one
through the presheaf of abelian groups and one through the presheaf of modules. -/
theorem submodule_mem_of_eq_of_mem {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) {a b : M} (h : a = b) (hb : b ∈ N) : a ∈ N := h ▸ hb

end Stacks.KaehlerDifferential

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The two rings of sections at an object of the small étale site -/

/-- The ring `(f⁻¹𝒪_Y)(U)` of sections of the inverse image of the structure sheaf of the target
over an étale chart `U` of `X`. -/
noncomputable abbrev inverseImageStructureRing (f : X ⟶ Y) (U : SmallEtale B S hS X.1) : Type u :=
  (inverseImageStructureSheaf B S hS f).obj.obj (op U)

/-- The `(f⁻¹𝒪_Y)(U)`-algebra structure on `𝒪_X(U)` given by the structure map
`f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`.  Not an instance: it depends on `f`. -/
@[instance_reducible]
noncomputable def sharpAlgebra (f : X ⟶ Y) (U : SmallEtale B S hS X.1) :
    Algebra (inverseImageStructureRing B S hS f U) (chartRing B S hS X.1 X.2 U) :=
  (((structureSharpInverseImage B S hS f).hom.app (op U)).hom).toAlgebra

theorem sharpAlgebra_algebraMap (f : X ⟶ Y) (U : SmallEtale B S hS X.1) :
    letI := sharpAlgebra B S hS f U
    (algebraMap (inverseImageStructureRing B S hS f U) (chartRing B S hS X.1 X.2 U)) =
      ((structureSharpInverseImage B S hS f).hom.app (op U)).hom := rfl

/-! ### The chart-algebra conditions -/

/-- **Étale-local finite generation of `𝒪_X` as an `f⁻¹𝒪_Y`-algebra.**  On a covering sieve of
every object of the small étale site of `X`, the ring of sections `𝒪_X(V)` is generated as an
`(f⁻¹𝒪_Y)(V)`-algebra by finitely many sections.

This is the sheaf-theoretic content of "`f` is locally of finite type", asked at *every* arrow of
one covering sieve rather than on a covering family; the family form,
`AlgebraicGeometry.Space.HasFiniteTypeAffineChartAlgebras`, is the one Stacks 05ZE uses and the
one proved from `AlgebraicGeometry.Space.IsLocallyOfFiniteType`.  The sieve form is used only by
the finite-presentation refinement of Stacks 05ZF. -/
def HasFiniteTypeChartAlgebras (f : X ⟶ Y) : Prop :=
  ∀ U : SmallEtale B S hS X.1, ∃ T : Sieve U, T ∈ (SmallEtale.topology B S hS X.1) U ∧
    ∀ ⦃V : SmallEtale B S hS X.1⦄ (g : V ⟶ U), T.arrows g →
      ∃ (n : ℕ) (y : Fin n → chartRing B S hS X.1 X.2 V),
        letI := sharpAlgebra B S hS f V
        ∀ z : chartRing B S hS X.1 X.2 V,
          z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)

/-- **Unramifiedness of the transition maps of the small étale site.**  For every arrow
`g : W ⟶ V` of the small étale site of `X` the module of differentials of the restriction ring
map `𝒪_X(V) ⟶ 𝒪_X(W)` vanishes.

This is "an étale ring map is unramified", Algebra, Lemma 00UU, for the ring map of sections of
an arrow of the small étale site; it mentions neither `f` nor `Ω_{X/Y}`. -/
def HasUnramifiedChartTransitions (X : AlgebraicSpaces B S hS) : Prop :=
  ∀ ⦃V W : SmallEtale B S hS X.1⦄ (g : W ⟶ V),
    letI := chartAlgebra (hF := X.2) g
    Subsingleton (KaehlerDifferential (chartRing B S hS X.1 X.2 V)
      (chartRing B S hS X.1 X.2 W))

/-! ### The universal derivation on restrictions -/

/-- **With unramified transitions, the universal differentials of the sections over `W` are
trapped by those of the restrictions from `V`.**

If a submodule `N` of `Ω_{X/Y}(W)` contains `d_{X/Y}(z|_W)` for every section `z` of `𝒪_X` over
`V`, then it contains `d_{X/Y}(c)` for every section `c` over `W`.  This is
`Stacks.KaehlerDifferential.mem_of_subsingleton_kaehlerDifferential` for the restriction ring
map `𝒪_X(V) ⟶ 𝒪_X(W)`, whose module of differentials vanishes by `hunram`. -/
theorem universalDerivation_mem_span_restrict_of_subsingleton (f : X ⟶ Y)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (hg : letI := chartAlgebra (hF := X.2) g
      Subsingleton (KaehlerDifferential (chartRing B S hS X.1 X.2 V)
        (chartRing B S hS X.1 X.2 W)))
    (N : Submodule (chartRing B S hS X.1 X.2 W)
      ((sheafOfDifferentials B S hS f).val.obj (op W)))
    (hN : ∀ z : chartRing B S hS X.1 X.2 V,
      (universalDerivation B S hS f).d (chartRestrict g z) ∈ N)
    (c : chartRing B S hS X.1 X.2 W) :
    (universalDerivation B S hS f).d c ∈ N := by
  let _ := chartAlgebra (hF := X.2) g
  have _ : Subsingleton (KaehlerDifferential (chartRing B S hS X.1 X.2 V)
      (chartRing B S hS X.1 X.2 W)) := hg
  have hN' : ∀ a : chartRing B S hS X.1 X.2 V,
      (universalDerivation B S hS f).d
        (algebraMap (chartRing B S hS X.1 X.2 V) (chartRing B S hS X.1 X.2 W) a) ∈ N := hN
  exact Stacks.KaehlerDifferential.mem_of_subsingleton_kaehlerDifferential
    (A := chartRing B S hS X.1 X.2 V) (C := chartRing B S hS X.1 X.2 W)
    (universalDerivation B S hS f).d (fun a b => (universalDerivation B S hS f).d_mul a b)
    N hN' c

/-- `AlgebraicGeometry.Space.universalDerivation_mem_span_restrict_of_subsingleton` fed with the
hypothesis `AlgebraicGeometry.Space.HasUnramifiedChartTransitions`. -/
theorem universalDerivation_mem_span_restrict (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (N : Submodule (chartRing B S hS X.1 X.2 W)
      ((sheafOfDifferentials B S hS f).val.obj (op W)))
    (hN : ∀ z : chartRing B S hS X.1 X.2 V,
      (universalDerivation B S hS f).d (chartRestrict g z) ∈ N)
    (c : chartRing B S hS X.1 X.2 W) :
    (universalDerivation B S hS f).d c ∈ N :=
  universalDerivation_mem_span_restrict_of_subsingleton B S hS f g (hunram g) N hN c

/-- **The `Algebra.adjoin` induction.**  If `z` lies in the `(f⁻¹𝒪_Y)(V)`-subalgebra of `𝒪_X(V)`
generated by `y₁, …, yₙ`, then `d_{X/Y}(z|_W)` lies in the `𝒪_X(W)`-span of the
`d_{X/Y}(yᵢ|_W)`.

The generators are in the span by definition; the universal derivation kills the image of
`f⁻¹𝒪_Y`, and restriction commutes with `f♯`, so it kills the restriction of a scalar; and the
span is closed under the sum and the Leibniz rule. -/
theorem universalDerivation_restrict_mem_span_of_adjoin (f : X ⟶ Y)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V) {n : ℕ}
    (y : Fin n → chartRing B S hS X.1 X.2 V) (z : chartRing B S hS X.1 X.2 V)
    (hz : letI := sharpAlgebra B S hS f V
      z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)) :
    (universalDerivation B S hS f).d (chartRestrict g z) ∈
      Submodule.span (chartRing B S hS X.1 X.2 W)
        (Set.range fun i : Fin n =>
          (universalDerivation B S hS f).d (chartRestrict g (y i))) := by
  let _ := sharpAlgebra B S hS f V
  set N := Submodule.span (chartRing B S hS X.1 X.2 W)
    (Set.range fun i : Fin n =>
      (universalDerivation B S hS f).d (chartRestrict g (y i))) with hNdef
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  | algebraMap a =>
    have hnat := (structureSharpInverseImage B S hS f).hom.naturality g.op
    have hres : chartRestrict (hF := X.2) g
        (((structureSharpInverseImage B S hS f).hom.app (op V)).hom a) =
        ((structureSharpInverseImage B S hS f).hom.app (op W)).hom
          (((inverseImageStructureSheaf B S hS f).obj.map g.op).hom a) :=
      (congrArg (fun φ : _ ⟶ _ => (CommRingCat.Hom.hom φ) a) hnat).symm
    refine Stacks.KaehlerDifferential.submodule_mem_of_eq_of_mem N ?_ (Submodule.zero_mem N)
    exact (congrArg (fun t => (universalDerivation B S hS f).d t) hres).trans
      ((universalDerivation B S hS f).d_app _)
  | add x w _ _ hx hw =>
    refine Stacks.KaehlerDifferential.submodule_mem_of_eq_of_mem N ?_ (Submodule.add_mem N hx hw)
    have hr : chartRestrict (hF := X.2) g (x + w) =
        chartRestrict (hF := X.2) g x + chartRestrict (hF := X.2) g w := map_add _ _ _
    exact (congrArg (fun t => (universalDerivation B S hS f).d t) hr).trans
      ((universalDerivation B S hS f).d.map_add _ _)
  | mul x w _ _ hx hw =>
    refine Stacks.KaehlerDifferential.submodule_mem_of_eq_of_mem N ?_
      (Submodule.add_mem N
        (Submodule.smul_mem N (chartRestrict (hF := X.2) g x) hw)
        (Submodule.smul_mem N (chartRestrict (hF := X.2) g w) hx))
    have hr : chartRestrict (hF := X.2) g (x * w) =
        chartRestrict (hF := X.2) g x * chartRestrict (hF := X.2) g w := map_mul _ _ _
    exact (congrArg (fun t => (universalDerivation B S hS f).d t) hr).trans
      ((universalDerivation B S hS f).d_mul _ _)


/-- The span of all universal differentials over `W` lies in the span of the `d_{X/Y}(yᵢ|_W)`. -/
private theorem span_universalDerivation_le_span_restrict (f : X ⟶ Y)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (hg : letI := chartAlgebra (hF := X.2) g
      Subsingleton (KaehlerDifferential (chartRing B S hS X.1 X.2 V)
        (chartRing B S hS X.1 X.2 W)))
    {n : ℕ} (y : Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)) :
    (Submodule.span (chartRing B S hS X.1 X.2 W)
        (Set.range fun c : chartRing B S hS X.1 X.2 W =>
          (universalDerivation B S hS f).d c) :
        Submodule (chartRing B S hS X.1 X.2 W)
          ((sheafOfDifferentials B S hS f).val.obj (op W))) ≤
      Submodule.span (chartRing B S hS X.1 X.2 W)
        (Set.range fun i : Fin n => (universalDerivation B S hS f).d
          (chartRestrict (hF := X.2) g (y i))) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, rfl⟩
  exact universalDerivation_mem_span_restrict_of_subsingleton B S hS f g hg _
    (fun z => universalDerivation_restrict_mem_span_of_adjoin B S hS f g y z (hy z)) c

/-! ### Sections of the sheaf of differentials are locally universal differentials -/

/-- The unit of sheafification at the presheaf of sectionwise Kähler differentials of `f♯`.  The
universal derivation `d_{X/Y}` is by construction this morphism composed with the sectionwise
Kähler differential. -/
noncomputable def differentialsSheafifyUnit (f : X ⟶ Y) :
    PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        (structureSharpInverseImage B S hS f).hom ⟶
      (PresheafOfModules.restrictScalars
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O)).obj)).obj
        ((SheafOfModules.forget
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).obj
          (sheafOfDifferentials B S hS f)) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).obj)).unit.app _

/-- The universal derivation is the sectionwise Kähler differential followed by the unit of
sheafification, which is how `AlgebraicGeometry.Space.universalDerivation` is defined. -/
theorem differentialsSheafifyUnit_app_d (f : X ⟶ Y) (U : SmallEtale B S hS X.1)
    (c : chartRing B S hS X.1 X.2 U) :
    ((differentialsSheafifyUnit B S hS f).app (op U)).hom
        (CommRingCat.KaehlerDifferential.d
          (f := (structureSharpInverseImage B S hS f).hom.app (op U)) c) =
      (universalDerivation B S hS f).d c := rfl

/-- The underlying morphism of presheaves of abelian groups of
`AlgebraicGeometry.Space.differentialsSheafifyUnit` is the unit of sheafification of presheaves
of abelian groups, which is locally surjective. -/
theorem toPresheaf_differentialsSheafifyUnit (f : X ⟶ Y) :
    (PresheafOfModules.toPresheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj).map
        (differentialsSheafifyUnit B S hS f) =
      CategoryTheory.toSheafify (smallEtaleRingedSite B S hS X.1 X.2).J
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
          (structureSharpInverseImage B S hS f).hom).presheaf :=
  PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _

/-- **Every section of `Ω_{X/Y}` is, on a covering sieve, an `𝒪_X`-combination of universal
differentials.**

`Ω_{X/Y}` is the sheafification of the presheaf of sectionwise Kähler differentials of `f♯`, and
the unit of sheafification is locally surjective, so on a covering sieve of any object the given
section is the image of a sectionwise Kähler differential; those are spanned by the Kähler
differentials of sections of `𝒪_X` (`KaehlerDifferential.span_range_derivation`), whose images
under the unit are the universal differentials. -/
theorem exists_sieve_mem_span_universalDerivation (f : X ⟶ Y) (W : SmallEtale B S hS X.1)
    (x : (sheafOfDifferentials B S hS f).val.obj (op W)) :
    ∃ T : Sieve W, T ∈ (smallEtaleRingedSite B S hS X.1 X.2).J W ∧
      ∀ ⦃Bo : SmallEtale B S hS X.1⦄ (g : Bo ⟶ W), T.arrows g →
        ((sheafOfDifferentials B S hS f).val.map g.op) x ∈
          (Submodule.span (chartRing B S hS X.1 X.2 Bo)
            (Set.range fun c : chartRing B S hS X.1 X.2 Bo =>
              (universalDerivation B S hS f).d c) :
            Submodule (chartRing B S hS X.1 X.2 Bo)
              ((sheafOfDifferentials B S hS f).val.obj (op Bo))) := by
  have hls := ((smallEtaleRingedSite B S hS X.1 X.2).J.W_toSheafify (A := AddCommGrpCat.{u})
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
      (structureSharpInverseImage B S hS f).hom).presheaf).isLocallySurjective
  refine ⟨Presheaf.imageSieve (CategoryTheory.toSheafify
    (smallEtaleRingedSite B S hS X.1 X.2).J
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
        (structureSharpInverseImage B S hS f).hom).presheaf) x, hls.imageSieve_mem x, ?_⟩
  rintro Bo g ⟨t, ht⟩
  let _ : Algebra (inverseImageStructureRing B S hS f Bo)
      ((smallEtaleRingedTopos B S hS X).O.obj.obj (op Bo)) :=
    (((structureSharpInverseImage B S hS f).hom.app (op Bo)).hom).toAlgebra
  set Nc := (Submodule.span (chartRing B S hS X.1 X.2 Bo)
    (Set.range fun c : chartRing B S hS X.1 X.2 Bo =>
      (universalDerivation B S hS f).d c) :
      Submodule (chartRing B S hS X.1 X.2 Bo)
        ((sheafOfDifferentials B S hS f).val.obj (op Bo))) with hNc
  have htop : Submodule.span ((smallEtaleRingedTopos B S hS X).O.obj.obj (op Bo))
      (Set.range fun b : (smallEtaleRingedTopos B S hS X).O.obj.obj (op Bo) =>
        CommRingCat.KaehlerDifferential.d
          (f := (structureSharpInverseImage B S hS f).hom.app (op Bo)) b) = ⊤ :=
    KaehlerDifferential.span_range_derivation (inverseImageStructureRing B S hS f Bo)
      ((smallEtaleRingedTopos B S hS X).O.obj.obj (op Bo))
  have himg : ∀ y ∈ Submodule.span ((smallEtaleRingedTopos B S hS X).O.obj.obj (op Bo))
        (Set.range fun b : (smallEtaleRingedTopos B S hS X).O.obj.obj (op Bo) =>
          CommRingCat.KaehlerDifferential.d
            (f := (structureSharpInverseImage B S hS f).hom.app (op Bo)) b),
      ((differentialsSheafifyUnit B S hS f).app (op Bo)).hom y ∈ Nc := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, rfl⟩ := hz
      exact Submodule.subset_span ⟨b, differentialsSheafifyUnit_app_d B S hS f Bo b⟩
    | zero =>
      exact Stacks.KaehlerDifferential.submodule_mem_of_eq_of_mem Nc
        (map_zero ((differentialsSheafifyUnit B S hS f).app (op Bo)).hom)
        (Submodule.zero_mem Nc)
    | add a b _ _ ha hb =>
      exact Stacks.KaehlerDifferential.submodule_mem_of_eq_of_mem Nc
        (map_add ((differentialsSheafifyUnit B S hS f).app (op Bo)).hom a b)
        (Submodule.add_mem Nc ha hb)
    | smul r a _ ha =>
      exact Stacks.KaehlerDifferential.submodule_mem_of_eq_of_mem Nc
        (map_smul ((differentialsSheafifyUnit B S hS f).app (op Bo)).hom r a)
        (Submodule.smul_mem Nc r ha)
  exact Stacks.KaehlerDifferential.submodule_mem_of_eq_of_mem Nc ht.symm
    (himg t (htop.ge Submodule.mem_top))


/-! ### The generators half of Stacks 04CV -/

/-- **With unramified transitions, the universal differentials of the sections over `W` lie in
the span of the restrictions of those of the sections over `V`.**  This is
`AlgebraicGeometry.Space.universalDerivation_mem_span_restrict` with the span itself as the
trapping submodule. -/
theorem universalDerivation_mem_span_restrict_range (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V) (c : chartRing B S hS X.1 X.2 W) :
    (universalDerivation B S hS f).d c ∈
      Submodule.span (chartRing B S hS X.1 X.2 W)
        (Set.range fun z : chartRing B S hS X.1 X.2 V =>
          (universalDerivation B S hS f).d (chartRestrict (hF := X.2) g z)) :=
  universalDerivation_mem_span_restrict B S hS f hunram g
    (Submodule.span (chartRing B S hS X.1 X.2 W)
      (Set.range fun z : chartRing B S hS X.1 X.2 V =>
        (universalDerivation B S hS f).d (chartRestrict (hF := X.2) g z)))
    (fun z => Submodule.subset_span ⟨z, rfl⟩) c

/-- **The span of all universal differentials over `W` is inside the span of the restrictions of
the `d_{X/Y}(yᵢ)`**, whenever the transition map `W ⟶ V` has vanishing module of differentials
and the `yᵢ` generate `𝒪_X(V)` as an `(f⁻¹𝒪_Y)(V)`-algebra.

This is the étale-local reduction step shared by the finite type and the finite presentation of
`Ω_{X/Y}`: `AlgebraicGeometry.Space.universalDerivation_mem_span_restrict_of_subsingleton` fed
with the `Algebra.adjoin` induction
`AlgebraicGeometry.Space.universalDerivation_restrict_mem_span_of_adjoin`. -/
theorem span_le_span_universalDerivation_restrict (f : X ⟶ Y)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (hg : letI := chartAlgebra (hF := X.2) g
      Subsingleton (KaehlerDifferential (chartRing B S hS X.1 X.2 V)
        (chartRing B S hS X.1 X.2 W)))
    {n : ℕ} (y : Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)) :
    (Submodule.span (chartRing B S hS X.1 X.2 W)
        (Set.range fun c : chartRing B S hS X.1 X.2 W =>
          (universalDerivation B S hS f).d c) :
        Submodule (chartRing B S hS X.1 X.2 W)
          ((sheafOfDifferentials B S hS f).val.obj (op W))) ≤
      Submodule.span (chartRing B S hS X.1 X.2 W)
        (Set.range fun i : Fin n => (universalDerivation B S hS f).d
          (chartRestrict (hF := X.2) g (y i))) :=
  span_universalDerivation_le_span_restrict B S hS f g hg y hy

/-- **The generators half of Stacks 04CV.**  With unramified transitions, every section of
`Ω_{X/Y}` over an object `W` of the small étale site which lies over a chart `V` is, on a
covering sieve of `W`, an `𝒪_X`-combination of the restrictions of the universal differentials
`d_{X/Y}(z)` of the sections `z` of `𝒪_X` over `V`.

Equivalently: the morphism to `Ω_{X/Y}|_V` from the free `𝒪_X|_V`-module on the sections of
`𝒪_X` over `V` which sends a section to its universal differential is locally surjective, hence
an epimorphism.  Quasi-coherence of `Ω_{X/Y}` needs in addition the *relations* half — that the
kernel of that morphism is itself generated by global sections on a covering — which is the
hypothesis `hrel` of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts_of_rel` and is not
proved anywhere in this development.  No 04CV attribute is therefore claimed. -/
theorem exists_sieve_mem_span_universalDerivation_restrict (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    {V W : SmallEtale B S hS X.1} (g : W ⟶ V)
    (x : (sheafOfDifferentials B S hS f).val.obj (op W)) :
    ∃ T : Sieve W, T ∈ (smallEtaleRingedSite B S hS X.1 X.2).J W ∧
      ∀ ⦃Bo : SmallEtale B S hS X.1⦄ (h : Bo ⟶ W), T.arrows h →
        ((sheafOfDifferentials B S hS f).val.map h.op) x ∈
          (Submodule.span (chartRing B S hS X.1 X.2 Bo)
            (Set.range fun z : chartRing B S hS X.1 X.2 V =>
              (universalDerivation B S hS f).d
                (chartRestrict (hF := X.2) (h ≫ g) z)) :
            Submodule (chartRing B S hS X.1 X.2 Bo)
              ((sheafOfDifferentials B S hS f).val.obj (op Bo))) := by
  obtain ⟨T, hT, hTspec⟩ := exists_sieve_mem_span_universalDerivation B S hS f W x
  refine ⟨T, hT, fun Bo h hh => ?_⟩
  have hle : (Submodule.span (chartRing B S hS X.1 X.2 Bo)
        (Set.range fun c : chartRing B S hS X.1 X.2 Bo =>
          (universalDerivation B S hS f).d c) :
        Submodule (chartRing B S hS X.1 X.2 Bo)
          ((sheafOfDifferentials B S hS f).val.obj (op Bo))) ≤
      Submodule.span (chartRing B S hS X.1 X.2 Bo)
        (Set.range fun z : chartRing B S hS X.1 X.2 V =>
          (universalDerivation B S hS f).d (chartRestrict (hF := X.2) (h ≫ g) z)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, rfl⟩
    exact universalDerivation_mem_span_restrict_range B S hS f hunram (h ≫ g) c
  exact hle (hTspec h hh)

/-! ### Finite generation on a covering, and Stacks 05ZE -/

/-- **The generators half.**  If `𝒪_X(V)` is generated as an `(f⁻¹𝒪_Y)(V)`-algebra by
`y₁, …, yₙ` and the transition maps of the small étale site are unramified, then the `n`
sections `d_{X/Y}(yᵢ)` generate `Ω_{X/Y}` on the slice at `V` in the sense of Stacks 03DE(5).

A section of `Ω_{X/Y}` over an object of the slice is locally an `𝒪_X`-combination of universal
differentials by `AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation`; each
universal differential lies in the span of the `d_{X/Y}(yᵢ|_·)` by
`AlgebraicGeometry.Space.universalDerivation_mem_span_restrict` fed with
`AlgebraicGeometry.Space.universalDerivation_restrict_mem_span_of_adjoin`; and a covering sieve
of the slice is the transport of a covering sieve of the base by
`CategoryTheory.Sieve.overEquiv`. -/
theorem hasFiniteGlobalGenerators_sheafOfDifferentials_over (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C) {n : ℕ}
    (y : Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)) :
    ((sheafOfDifferentials B S hS f).over V).HasFiniteGlobalGenerators := by
  refine Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_sections
    ((sheafOfDifferentials B S hS f).over V)
    (fun i => Stacks.SheafOfModules.mkOver (M := sheafOfDifferentials B S hS f) (V := V)
      ((universalDerivation B S hS f).d (y i))) ?_
  intro V' x
  obtain ⟨T₀, hT₀, hT₀spec⟩ := exists_sieve_mem_span_universalDerivation B S hS f V'.left x
  refine ⟨(Sieve.overEquiv V').symm T₀,
    (smallEtaleRingedSite B S hS X.1 X.2).J.overEquiv_symm_mem_over V' T₀ hT₀, ?_⟩
  intro Bo g hg
  have h1 := hT₀spec g.left ((Sieve.overEquiv_symm_iff T₀ g).1 hg)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (span_universalDerivation_le_span_restrict B S hS f Bo.hom (hunram Bo.hom) y hy h1)
  refine ⟨c, Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hc⟩
  exact congrArg
    (fun w : (sheafOfDifferentials B S hS f).val.obj (op Bo.left) => c i • w)
    (((universalDerivation B S hS f).d_map Bo.hom.op (y i)).symm)

/-- **Stacks 05ZE**, with the two carried hypotheses in place of "`f` is locally of finite
type".  If `𝒪_X` is étale-locally generated as an `f⁻¹𝒪_Y`-algebra by finitely many sections and
the transition maps of the small étale site of `X` are unramified, then `Ω_{X/Y}` is a finite
type `𝒪_X`-module.

The covering of each object is the one `hft` supplies, presented as the family of all its arrows
indexed by their sources, and on each member the finitely many generators are
`AlgebraicGeometry.Space.hasFiniteGlobalGenerators_sheafOfDifferentials_over`. -/
@[stacks 05ZE "finite type of Ω_{X/Y}, from étale-local finite generation of 𝒪_X over f⁻¹𝒪_Y
  and unramifiedness of the transition maps of the small étale site; the gap to the source's
  hypothesis is the bridge from 03XF(1) to the algebra statement, and 00UU for the sections of
  an arrow of the small étale site"]
theorem isFiniteTypeOnSite_sheafOfDifferentials (f : X ⟶ Y)
    (hunram : HasUnramifiedChartTransitions B S hS X)
    (hft : HasFiniteTypeChartAlgebras B S hS f) :
    (sheafOfDifferentials B S hS f).IsFiniteTypeOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨T, hT, hTspec⟩ := hft U
  refine ⟨Σ V : (smallEtaleRingedSite B S hS X.1 X.2).C, {g : V ⟶ U // T.arrows g}, fun i => i.1,
    fun i => i.2.1, ?_, fun i => ?_⟩
  · refine (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering (fun Z g hg => ?_) hT
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Z, g, hg⟩, 𝟙 Z, (Category.id_comp g).symm⟩
  · obtain ⟨n, y, hy⟩ := hTspec i.2.1 i.2.2
    exact hasFiniteGlobalGenerators_sheafOfDifferentials_over B S hS f hunram i.1 y hy

/-- **Stacks 05ZE.**  If `f : X ⟶ Y` is a morphism of algebraic spaces over `S` which is locally
of finite type, then `Ω_{X/Y}` is a finite type `𝒪_X`-module.

The two inputs not proved in this development are carried universally quantified: the bridge
from `AlgebraicGeometry.Space.IsLocallyOfFiniteType` (Stacks 03XF(1), defined through étale
scheme charts) to the statement that `𝒪_X` is étale-locally a finite type `f⁻¹𝒪_Y`-algebra, and
the unramifiedness of the transition maps of a small étale site, which is Algebra, Lemma 00UU
for the ring map of sections of an arrow of that site. -/
@[stacks 05ZE "the source's statement, carrying the bridge from 03XF(1) to étale-local finite
  generation of 𝒪_X over f⁻¹𝒪_Y as `hft` and unramifiedness of the transition maps of a small
  étale site (00UU) as `hunram`, both quantified over all algebraic spaces over `S`"]
theorem isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType
    (hunram : ∀ X' : AlgebraicSpaces B S hS, HasUnramifiedChartTransitions B S hS X')
    (hft : ∀ (X' Y' : AlgebraicSpaces B S hS) (g : X' ⟶ Y'),
      IsLocallyOfFiniteType B S hS g.hom → HasFiniteTypeChartAlgebras B S hS g)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    (sheafOfDifferentials B S hS f).IsFiniteTypeOnSite :=
  isFiniteTypeOnSite_sheafOfDifferentials B S hS f (hunram X) (hft X Y f hf)

/-! ### The same with Algebra, Lemma 00UU proved rather than assumed -/

attribute [local instance_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The generators half at an affine chart, with no unramifiedness hypothesis.**  If the
scheme underlying the étale chart `V` is affine and `𝒪_X(V)` is generated as an
`(f⁻¹𝒪_Y)(V)`-algebra by `y₁, …, yₙ`, then the `n` sections `d_{X/Y}(yᵢ)` generate `Ω_{X/Y}` on
the slice at `V` in the sense of Stacks 03DE(5).

This is `AlgebraicGeometry.Space.hasFiniteGlobalGenerators_sheafOfDifferentials_over` with
Algebra, Lemma 00UU supplied rather than assumed.  Lemma 00UU is available only for arrows
between *affine* charts
(`AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_chartRing_of_affineChart`), so the
covering sieve witnessing the local generation is taken to be
`Stacks.Sheaves.LocalGeneration.spanSieve`, the sieve of **all** arrows along which the
restriction of the given section is already a combination of the generators; being a sieve is
part of that definition.  It covers by `CategoryTheory.GrothendieckTopology.transitive`: the
sieve of `AlgebraicGeometry.Space.exists_sieve_mem_span_universalDerivation` covers, and
refining each of its arrows by the affine charts of
`AlgebraicGeometry.Space.SmallEtale.exists_affine_ofArrows_over` lands inside the span sieve,
because over an affine chart
`AlgebraicGeometry.Space.span_le_span_universalDerivation_restrict` applies. -/
theorem hasFiniteGlobalGenerators_sheafOfDifferentials_over_of_isAffine (f : X ⟶ Y)
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    {n : ℕ} (y : Fin n → chartRing B S hS X.1 X.2 V)
    (hy : letI := sharpAlgebra B S hS f V
      ∀ z : chartRing B S hS X.1 X.2 V,
        z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f V) (Set.range y)) :
    ((sheafOfDifferentials B S hS f).over V).HasFiniteGlobalGenerators := by
  set σ : Fin n → ((sheafOfDifferentials B S hS f).over V).sections := fun i =>
    Stacks.SheafOfModules.mkOver (M := sheafOfDifferentials B S hS f) (V := V)
      ((universalDerivation B S hS f).d (y i)) with hσ
  refine Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_sections
    ((sheafOfDifferentials B S hS f).over V) σ ?_
  intro V' x
  refine ⟨Stacks.Sheaves.LocalGeneration.spanSieve ((sheafOfDifferentials B S hS f).over V)
    (fun i => (σ i).val (op V')) x, ?_, ?_⟩
  · obtain ⟨T₀, hT₀, hT₀spec⟩ := exists_sieve_mem_span_universalDerivation B S hS f V'.left x
    refine ((smallEtaleRingedSite B S hS X.1 X.2).J.over V).transitive
      ((smallEtaleRingedSite B S hS X.1 X.2).J.overEquiv_symm_mem_over V' T₀ hT₀) _ ?_
    intro Z g hg
    obtain ⟨I, A, a, hAaff, hAcov⟩ := SmallEtale.exists_affine_ofArrows_over B S hS X.1 V Z
    refine ((smallEtaleRingedSite B S hS X.1 X.2).J.over V).superset_covering ?_ hAcov
    refine (Sieve.generate_le_iff _ _).2 ?_
    rintro Z' h ⟨j⟩
    change (Stacks.Sheaves.LocalGeneration.spanSieve ((sheafOfDifferentials B S hS f).over V)
      (fun i => (σ i).val (op V')) x).arrows (a j ≫ g)
    obtain ⟨k, hk⟩ : ∃ k : A j ⟶ V', k = a j ≫ g := ⟨_, rfl⟩
    rw [← hk]
    have hmem : T₀.arrows (Over.Hom.left k) := by
      rw [hk]
      exact T₀.downward_closed ((Sieve.overEquiv_symm_iff T₀ g).1 hg) (Over.Hom.left (a j))
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun
      (chartRing B S hS X.1 X.2 (A j).left)).1
      (span_le_span_universalDerivation_restrict B S hS f (A j).hom
        (subsingleton_kaehlerDifferential_chartRing_of_affineChart B S hS (hF := X.2) (A j).hom
          hV (hAaff j))
        y hy (hT₀spec (Over.Hom.left k) hmem))
    exact ⟨c, Eq.trans (Finset.sum_congr rfl fun i _ => congrArg
      (fun w : (sheafOfDifferentials B S hS f).val.obj (op (A j).left) => c i • w)
      (((σ i).property k.op).trans
        (((universalDerivation B S hS f).d_map (A j).hom.op (y i)).symm))) hc⟩
  · intro Bo g hg
    obtain ⟨c, hc⟩ := hg
    exact ⟨c, Eq.trans (Finset.sum_congr rfl fun i _ =>
      congrArg (fun w => c i • w) (((σ i).property g.op).symm)) hc⟩

/-- **Étale-local finite generation of `𝒪_X` as an `f⁻¹𝒪_Y`-algebra, on a covering by affine
charts.**  Every object of the small étale site of `X` carries a covering family whose members
have affine underlying scheme and over each of which the ring of sections `𝒪_X(V)` is generated
as an `(f⁻¹𝒪_Y)(V)`-algebra by finitely many sections.

This is the sheaf-theoretic content of "`f` is locally of finite type".  It asks for the
generation only on a covering *family* of charts with affine underlying scheme, which is where
the chart condition of Stacks 03XF(1) delivers it — the chart morphism of a commuting square of
*affine* étale charts is a finite type morphism of affine schemes, hence a finite type ring map
on global sections — and it is also exactly where Algebra, Lemma 00UU is available for the
transition maps.  It holds for every morphism locally of finite type, by
`AlgebraicGeometry.Space.hasFiniteTypeAffineChartAlgebras_of_isLocallyOfFiniteType`; see the
module notes. -/
def HasFiniteTypeAffineChartAlgebras (f : X ⟶ Y) : Prop :=
  ∀ U : SmallEtale B S hS X.1,
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B S hS X.1) (a : ∀ i, V i ⟶ U),
      Sieve.ofArrows V a ∈ (SmallEtale.topology B S hS X.1) U ∧
        ∀ i, IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj (V i)) ∧
          ∃ (n : ℕ) (y : Fin n → chartRing B S hS X.1 X.2 (V i)),
            letI := sharpAlgebra B S hS f (V i)
            ∀ z : chartRing B S hS X.1 X.2 (V i),
              z ∈ Algebra.adjoin (inverseImageStructureRing B S hS f (V i)) (Set.range y)

/-- **Finite type of `Ω_{X/Y}` from the étale-local finite generation of `𝒪_X` over `f⁻¹𝒪_Y`.**
If every object of the small étale site of `X` has a covering by affine charts over which `𝒪_X`
is generated as an `f⁻¹𝒪_Y`-algebra by finitely many sections, then `Ω_{X/Y}` is a finite type
`𝒪_X`-module.

The covering of each object is the one `hft` supplies, and on each of its members the finitely
many generators are
`AlgebraicGeometry.Space.hasFiniteGlobalGenerators_sheafOfDifferentials_over_of_isAffine`.
Unramifiedness of the transition maps — Algebra, Lemma 00UU — is *proved*, not assumed:
affineness of the members is what makes
`AlgebraicGeometry.Space.subsingleton_kaehlerDifferential_chartRing_of_affineChart` apply.

This is the engine of Stacks 05ZE with no unramifiedness hypothesis; at the source's own
hypothesis `AlgebraicGeometry.Space.IsLocallyOfFiniteType`, and with nothing else assumed, the
statement is
`Space.isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_unconditional`,
in `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsFiniteTypeChartBridge.lean`. -/
@[stacks 05ZE "finite type of Ω_{X/Y} from étale-local finite generation of 𝒪_X over f⁻¹𝒪_Y on a
  covering by affine charts, which is what 03XF(1) delivers; unramifiedness of the transition
  maps of the small étale site (00UU) is proved, not assumed.  The source's own hypothesis is
  taken in `isFiniteTypeOnSite_sheafOfDifferentials_of_isLocallyOfFiniteType_unconditional`"]
theorem isFiniteTypeOnSite_sheafOfDifferentials_of_affineChartAlgebras (f : X ⟶ Y)
    (hft : HasFiniteTypeAffineChartAlgebras B S hS f) :
    (sheafOfDifferentials B S hS f).IsFiniteTypeOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, a, hcov, hV⟩ := hft U
  refine ⟨I, V, a, hcov, fun i => ?_⟩
  obtain ⟨haff, n, y, hy⟩ := hV i
  exact hasFiniteGlobalGenerators_sheafOfDifferentials_over_of_isAffine B S hS f (V i) haff y hy

end AlgebraicGeometry.Space

end
