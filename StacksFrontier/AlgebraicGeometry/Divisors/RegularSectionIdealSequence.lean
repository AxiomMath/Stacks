module

public import StacksFrontier.Algebra.Homology.ShortComplex.ShortExactTransport
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniPullbackTrivialization

/-!
# Stacks Tag 0C6K: the ideal sequence of a regular section

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `s` a regular global section of `L`
([Stacks, Tag 01WY]) and `i : Z(s) ⟶ X` the inclusion of its zero scheme ([Stacks, Tag 02OQ]).
Then

`0 ⟶ L^{⊗ -1} ⟶ 𝒪_X ⟶ i_* 𝒪_{Z(s)} ⟶ 0`

is short exact, the first map being multiplication by `s` — an element of `L^{⊗ -1}` paired
against `s` lands in `L^{⊗ -1} ⊗ L = 𝒪_X` — and the second restriction to the zero scheme. In
the decomposition of [Stacks, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K) this is the
label `regular_section_ideal_sequence`: the second of the two sequences the remark writes down
for a regular section of an invertible sheaf.

## Main definitions

* `AlgebraicGeometry.inverseTensorPower`: `L^{⊗ -1}`, ascribed to `X.Modules`.
* `AlgebraicGeometry.inverseTensorPowerIsoUnit`: the canonical trivialization
  `L^{⊗ -1} ⊗ L ≅ 𝒪_X`.

## Main results

* `AlgebraicGeometry.unitToPushforwardObjUnit_eq_unit_comp_pullback`: restriction to a closed
  subscheme, read through a trivialization of its source. This is the one commuting square the
  transport needs.
* `AlgebraicGeometry.shortExact_zeroScheme_ideal_of_tensorIsoUnit`: the sequence for an
  arbitrary tensor inverse of `L`, that is, for an invertible `M` equipped with a
  trivialization `θ : M ⊗ L ≅ 𝒪_X`. The map `M ⟶ 𝒪_X` is multiplication by `s` read through
  `θ`.
* `AlgebraicGeometry.shortExact_zeroScheme_ideal_of_isRegularSection`: **Stacks Tag 0C6K, the
  label `regular_section_ideal_sequence`**, the previous statement at `M = L^{⊗ -1}` with its
  canonical trivialization, which is the tag's own sequence.

## Where it comes from

The twisted regular-section sequence of this same tag,
`AlgebraicGeometry.shortExact_zeroScheme_twist_of_isRegularSection`, already gives

`0 ⟶ M ⟶ M ⊗ L ⟶ i_* i^* (M ⊗ L) ⟶ 0`

for every invertible `M`. Taking `M` to be a tensor inverse of `L` turns the middle term into
`𝒪_X`, and the only work left is to see that the last term then becomes `i_* 𝒪_{Z(s)}` *with the
restriction map the sequence needs*. Two facts do that, and both are in the library:

* the unit of `i^* ⊣ i_*` is natural, so transporting the middle term along `θ` replaces the
  unit at `M ⊗ L` by the unit at `𝒪_X` composed with `i_* i^*(θ)`;
* `𝒪_X` pulls back to `𝒪_{Z(s)}` (`Stacks.Divisors.unitComparison`, an isomorphism), and the
  adjoint of that comparison *is* the restriction map
  `SheafOfModules.unitToPushforwardObjUnit`
  (`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`).

Composing the two gives the one commuting square that
`Stacks.ShortComplex.shortExact_transport₂₃` asks for, and short exactness transports.

## Implementation notes

The monoidal structure is `Stacks.SheafOfModules.sheafTensorMonoidal`, re-exported at a scheme
by `AlgebraicGeometry.schemeModulesMonoidal`, which is the one the twisted sequence is stated
for; so `⊗`, `◁` and `ρ_` below mean the tensor product sheaf of [Stacks, Tag 01CA] and nothing
has to be compared.

`L^{⊗ -1}` is `Stacks.SheafOfModules.Invertible.tensorPower` at `-1`, whose type is indexed by
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj _` rather than by
`X.ringCatSheaf`. The two are the same, but instance search is syntactic, so the tensor power is
ascribed to `X.Modules` wherever the monoidal notation has to find its structure. The same holds
of the two invertibility predicates, crossed once through
`Stacks.InvertibleBridge`. No transparency option is involved.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

attribute [local instance] AlgebraicGeometry.schemeModulesMonoidal

namespace AlgebraicGeometry

/-- **Restriction to a closed subscheme, read through a trivialization of the source.** For
`i : Z ⟶ X` a morphism of schemes, `A` an `𝒪_X`-module and `θ : A ≅ 𝒪_X`, the restriction map
`𝒪_X ⟶ i_* 𝒪_Z` precomposed with `θ` is the unit of `i^* ⊣ i_*` at `A` followed by the
pushforward of `i^*(θ)` and of the comparison `i^* 𝒪_X ≅ 𝒪_Z`.

Two facts: the unit is natural, and the adjoint transpose of the comparison
`Stacks.Divisors.unitComparison` *is* the restriction map
(`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`). -/
theorem unitToPushforwardObjUnit_eq_unit_comp_pullback {X Z : Scheme.{u}} (i : Z ⟶ X)
    (A : X.Modules) (θ : A ≅ SheafOfModules.unit X.ringCatSheaf) :
    θ.hom ≫ SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
        (Scheme.Modules.pushforward i).map
          ((Scheme.Modules.pullback i).map θ.hom ≫ Stacks.Divisors.unitComparison i) :=
  have hn : θ.hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (SheafOfModules.unit X.ringCatSheaf) =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map θ.hom) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.naturality θ.hom
  have hadj : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward i).map (Stacks.Divisors.unitComparison i) =
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      i.toRingCatSheafHom
  ((congrArg (fun k => (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A ≫ k)
      (Functor.map_comp (Scheme.Modules.pushforward i) ((Scheme.Modules.pullback i).map θ.hom)
        (Stacks.Divisors.unitComparison i))).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (Scheme.Modules.pushforward i).map
            (Stacks.Divisors.unitComparison i)) hn.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (fun k => θ.hom ≫ k) hadj))))).symm

variable (X : Scheme.{u}) (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **[Stacks, Tag 0C6K], the ideal sequence of a regular section, for an arbitrary tensor
inverse of `L`.** Let `s` be a regular global section of the invertible module `L` and let `M`
be an invertible module trivializing `L`, i.e. equipped with `θ : M ⊗ L ≅ 𝒪_X`. Then

`0 ⟶ M ⟶ 𝒪_X ⟶ i_* 𝒪_{Z(s)} ⟶ 0`

is short exact, the first map being multiplication by `s` read through `θ` and the second the
restriction to the zero scheme of `s`. -/
theorem shortExact_zeroScheme_ideal_of_tensorIsoUnit (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    (θ : M ⊗ L ≅ SheafOfModules.unit X.ringCatSheaf) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let u : M ⟶ SheafOfModules.unit X.ringCatSheaf :=
      ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) ≫ θ.hom
    let q : SheafOfModules.unit X.ringCatSheaf ⟶
        (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf) :=
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
    ∃ h : u ≫ q = 0, (ShortComplex.mk u q h).ShortExact := by
  obtain ⟨h0, hse⟩ := shortExact_zeroScheme_twist_of_isRegularSection X L s hs M
  exact Stacks.ShortComplex.shortExact_transport₂₃ hse θ
    ((Scheme.Modules.pushforward (zeroScheme X L (s.eval (op ⊤))).subschemeι).mapIso
      ((Scheme.Modules.pullback (zeroScheme X L (s.eval (op ⊤))).subschemeι).mapIso θ ≪≫
        asIso (Stacks.Divisors.unitComparison
          (zeroScheme X L (s.eval (op ⊤))).subschemeι)))
    (unitToPushforwardObjUnit_eq_unit_comp_pullback
      (zeroScheme X L (s.eval (op ⊤))).subschemeι (M ⊗ L) θ)


/-- `L^{⊗ -1}`, the inverse first tensor power of an invertible module, ascribed to `X.Modules`.

The tensor power of [Stacks, Tag 01CU] is stated for a sheaf of modules over a general site,
and its type names the sheaf of rings as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj _` rather than as
`X.ringCatSheaf`. The two are the same, but the monoidal structure of this file is registered
on `X.Modules`, and instance search is syntactic; so the ascription is made once, here. -/
abbrev inverseTensorPower : X.Modules :=
  Stacks.SheafOfModules.Invertible.tensorPower X.sheaf.obj X.ringCatSheaf.property L (-1)

/-- **The canonical trivialization `L^{⊗ -1} ⊗ L ≅ 𝒪_X`** of an invertible module against its
inverse first tensor power: one more application of the right-tensor autoequivalence sends
`L^{⊗ -1}` to `L^{⊗ 0}`, which is the structure sheaf. -/
def inverseTensorPowerIsoUnit :
    inverseTensorPower X L ⊗ L ≅ SheafOfModules.unit X.ringCatSheaf :=
  have hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  Stacks.SheafOfModules.Invertible.tensorPowerSuccIso X.sheaf.obj X.ringCatSheaf.property L (-1) ≪≫
    Stacks.SheafOfModules.Invertible.tensorPowerReindex X.sheaf.obj X.ringCatSheaf.property L
      (show (-1 : ℤ) + 1 = 0 by ring)

/-- `L^{⊗ -1}` is invertible, in the spelling the twisted sequence takes its module factor. -/
theorem isInvertible_inverseTensorPower :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (inverseTensorPower X L) :=
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (inverseTensorPower X L) :=
    Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.sheaf.obj
      X.ringCatSheaf.property L (-1)
  Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible

/-- **Stacks Tag 0C6K, the label `regular_section_ideal_sequence`.** For an invertible module
`L` on a scheme `X` and a regular global section `s` of `L` ([Stacks, Tag 01WY]), the sequence

`0 ⟶ L^{⊗ -1} ⟶ 𝒪_X ⟶ i_* 𝒪_{Z(s)} ⟶ 0`

is short exact, where `i` is the inclusion of the zero scheme of `s`, the first map is
multiplication by `s` through the canonical trivialization `L^{⊗ -1} ⊗ L ≅ 𝒪_X` and the second
is restriction to the zero scheme. -/
@[stacks 0C6K "regular_section_ideal_sequence"]
theorem shortExact_zeroScheme_ideal_of_isRegularSection (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let Linv : X.Modules := inverseTensorPower X L
    let u : Linv ⟶ SheafOfModules.unit X.ringCatSheaf :=
      ((ρ_ Linv).inv ≫ Linv ◁ L.unitHomEquiv.symm s) ≫ (inverseTensorPowerIsoUnit X L).hom
    let q : SheafOfModules.unit X.ringCatSheaf ⟶
        (Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (zeroScheme X L (s.eval (op ⊤))).subscheme.ringCatSheaf) :=
      SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom
    ∃ h : u ≫ q = 0, (ShortComplex.mk u q h).ShortExact :=
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (inverseTensorPower X L) := isInvertible_inverseTensorPower X L
  shortExact_zeroScheme_ideal_of_tensorIsoUnit X L s hs (inverseTensorPower X L)
    (inverseTensorPowerIsoUnit X L)

end AlgebraicGeometry

end
