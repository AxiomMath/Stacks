module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.FunctionFieldShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.Codimension
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.CategoryTheory.Abelian.ShortExactReflectFaithful
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient presentation of a principal divisor on an integral scheme

Let `(S, δ)` be a base situation with a dimension function, let `X` be integral and locally of
finite type over `S` with `dim_δ(X) = k + 1`, and let `g` be a nonzero rational function on `X`
with ideal of denominators `I`. The two short exact sequences of Stacks 02P0,

`0 ⟶ I ⟶ 𝒪_X ⟶ 𝒪_X/I ⟶ 0`   and   `0 ⟶ I ⟶^{g} 𝒪_X ⟶ 𝒪_X/gI ⟶ 0`,

share their first and their second term, both quotients are coherent with support of
delta-dimension at most `k`, and at each point the difference of the multiplicities of the two
quotients is the order of vanishing of `g`. This file assembles that data into the presentation
which the proof of [Stacks, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS) feeds to
`Stacks.Chow.cycleDimensionLayerWideHom_eq_zero_of_shortExact`.

## Main definitions

* `Stacks.Chow.denominatorQuotientUnit` and `Stacks.Chow.denominatorSectionQuotientUnit` —
  `𝒪_X/I` and `𝒪_X/sI`.
* `Stacks.Chow.shortComplexDimLE` — a short complex of modules whose three terms are given as
  objects of `Coh_{≤b}(X)`, read as a short complex of `Coh_{≤b}(X)`.
* `Stacks.Chow.structureSheafDimLE` and `Stacks.Chow.denominatorIdealDimLE` — `𝒪_X` and `I`, as
  objects of `Coh_{≤k+1}(X)`.
* `Stacks.Chow.denominatorQuotientUnitDimLE` and
  `Stacks.Chow.denominatorSectionQuotientUnitDimLE` — the two quotients, as objects of
  `Coh_{≤k}(X)`.
* `Stacks.Chow.denominatorShortComplexUnit` and `Stacks.Chow.denominatorSectionShortComplexUnit`
  — the two sequences above, as short complexes of `Coh_{≤k+1}(X)`.

## Main results

* `Stacks.Chow.isCoherent_denominatorIdeal_unitModule` — the ideal of denominators of a
  meromorphic section of `𝒪_X` is coherent.
* `Stacks.Chow.isCoherent_denominatorQuotientUnit` and
  `Stacks.Chow.isCoherent_denominatorSectionQuotientUnit` — Stacks 02SW part (2) for `L = 𝒪_X`:
  both quotients are coherent.
* `Stacks.Chow.schemeDeltaDimension_denominatorQuotientUnit_le` and
  `Stacks.Chow.schemeDeltaDimension_denominatorSectionQuotientUnit_le` — both quotients are
  supported in delta-dimension at most `k`.
* `Stacks.Chow.shortExact_shortComplexDimLE` — a short complex of `Coh_{≤b}(X)` is short exact as
  soon as the underlying short complex of `𝒪_X`-modules is.
* `Stacks.Chow.shortExact_denominatorShortComplexUnit` and
  `Stacks.Chow.shortExact_denominatorSectionShortComplexUnit` — Stacks 02SW part (1) for
  `L = 𝒪_X`, in the dimension layer.
* `Stacks.Chow.dimensionLayerCycle_denominatorQuotientUnit_sub_apply` and
  `Stacks.Chow.dimensionLayerCycle_denominatorQuotientUnit_sub_eq` — the cycle identity
  `[𝒪_X/gI]_k − [𝒪_X/I]_k = div(g)` on an integral `X` of delta-dimension `k + 1`, pointwise and
  as an identity of cycles.

## Implementation notes

Coherence of the two quotients does **not** follow from
`Stacks.Chow.isCoherent_denominatorQuotient`, the general form of Stacks 02SW part (2): that is
stated for the cokernel of `I F ⟶ F`, and at `F = 𝒪_X` the product `I · 𝒪_X` is the image of the
action `I ⊗ 𝒪_X ⟶ 𝒪_X`, which is not the term `I` that the two sequences of this file are built
from. Both quotients are therefore proved coherent directly: the ideal of denominators is
quasi-coherent by Stacks 02P0 and a submodule of the coherent `𝒪_X`, hence coherent by
Stacks 01Y1, and a cokernel of a morphism of coherent modules is coherent by Stacks 01Y0. The
dimension bounds, by contrast, are free: the supports of these very two cokernels are the two
halves of `AlgebraicGeometry.denominatorBadLocus`, so
`Stacks.Chow.relativeDimension_le_of_mem_denominatorBadLocus` applies with no containment left to
prove.

The two quotients are given names rather than written as cokernels inside the statements that
mention them. `Stacks.Chow.reducedSupport` takes a module of the declared type
`AlgebraicGeometry.Scheme.Modules`, whose categorical instances are copies of the ones on
`CategoryTheory.SheafOfModules`; a `cokernel` elaborated against that expected type therefore
carries a different `HasCokernel` instance from the same cokernel elaborated in the
`SheafOfModules` reading, and although the two terms agree by `rfl`, the coherence instance
proved for one is not found by instance search for the other. A definition at a fixed declared
type removes that: the term `Stacks.Chow.denominatorQuotientUnit X s` is opaque to instance
search and matches syntactically wherever it appears.

Both the lifting of a short complex into `Coh_{≤b}(X)` and the reflection of short exactness are
stated over abstract data: `Stacks.Chow.shortComplexDimLE` takes the three objects and the two
morphisms as arguments, and `CategoryTheory.ShortComplex.shortExact_of_shortExact_map` is proved
for a bare faithful exact functor. At a concrete denominator morphism, inside a structure
instance, the homology-preservation instances are searched before the goal is unified with the
morphism and the search runs on the large terms.

The predicate carried by an object of `Stacks.Chow.CoherentModulesDimLE` mentions
`Stacks.Chow.reducedSupport`, which takes coherence of the module as an instance argument;
coherence is a `Prop`, so by proof irrelevance the bound may be proved with any proof of it.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample (unitModule)

universe u

namespace Stacks.Chow

/-! ### Preliminaries -/

/-- A monomorphism of modules on a scheme, read in `AlgebraicGeometry.Scheme.Modules`. The
categorical instances on that definition are copies of the ones on
`CategoryTheory.SheafOfModules`, so the two readings of `Mono f` are not interchangeable by
instance search. -/
private theorem mono_modules {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B)
    (hf : @Mono (_root_.SheafOfModules.{u} X.ringCatSheaf) (inferInstance) A B f) : Mono f :=
  ⟨fun _ _ hcomp => hf.right_cancellation _ _ hcomp⟩

/-- The relative dimension at every point of a scheme is bounded by the delta-dimension of the
scheme: this is `Stacks.Chow.relativeDimension_le_of_schemeDeltaDimension_le` for the identity
closed immersion. -/
private theorem relativeDimension_le_of_le (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] {b : ℤ}
    (hX : schemeDeltaDimension C p ≤ (b : EInt)) (x : X) :
    relativeDimension C.dimensionFunction p x ≤ b := by
  simpa using relativeDimension_le_of_schemeDeltaDimension_le C p (𝟙 X) (k := b)
    (by simpa using hX) x

/-- The support of a coherent module has delta-dimension at most that of the scheme itself:
every point of the scheme has relative dimension at most that bound. -/
theorem schemeDeltaDimension_reducedSupport_le_of_le (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (F : X.Modules) [F.IsCoherent] {b : ℤ}
    (hX : schemeDeltaDimension C p ≤ (b : EInt)) :
    schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ p) ≤ (b : EInt) :=
  schemeDeltaDimension_reducedSupport_le C p F fun x _ => relativeDimension_le_of_le C p hX x

/-! ### The two denominator quotients of the structure sheaf -/

/-- The quotient `𝒪_X/I` of the structure sheaf by the ideal of denominators of a meromorphic
section of `𝒪_X`: the third term of the first sequence of Stacks 02SW part (1) for `L = 𝒪_X`. -/
def denominatorQuotientUnit (X : Scheme.{u}) (s : MeromorphicSection X.sheaf (unitModule X)) :
    _root_.SheafOfModules.{u} X.ringCatSheaf :=
  cokernel (denominatorIdealι X (unitModule X) s)

/-- The quotient `𝒪_X/sI` of the structure sheaf by the image of the ideal of denominators of a
meromorphic section `s` of `𝒪_X` under multiplication by `s`: the third term of the second
sequence of Stacks 02SW part (1) for `L = 𝒪_X`. -/
def denominatorSectionQuotientUnit (X : Scheme.{u})
    (s : MeromorphicSection X.sheaf (unitModule X)) :
    _root_.SheafOfModules.{u} X.ringCatSheaf :=
  cokernel (denominatorIdealMul X (unitModule X) s)

/-- **The ideal of denominators of a meromorphic section of `𝒪_X` is coherent.** It is
quasi-coherent by Stacks 02P0 and a submodule of the coherent module `𝒪_X`. -/
@[ega "IV 20.2.14" "special case"]
theorem isCoherent_denominatorIdeal_unitModule (X : Scheme.{u}) [IsLocallyNoetherian X]
    (s : MeromorphicSection X.sheaf (unitModule X)) :
    (denominatorIdeal X (unitModule X) s).IsCoherent := by
  have : (denominatorIdeal X (unitModule X) s).IsQuasicoherent :=
    denominatorIdeal_isQuasicoherent X (unitModule X) s (isInvertible_unitModule X)
  have := mono_modules _ (mono_denominatorIdealι_unitModule X s)
  exact Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_mono
    (denominatorIdealι X (unitModule X) s)

/-- The cokernel of any morphism from the ideal of denominators of a meromorphic section of `𝒪_X`
to `𝒪_X` is coherent. -/
private theorem isCoherent_cokernel_denominator (X : Scheme.{u}) [IsLocallyNoetherian X]
    (s : MeromorphicSection X.sheaf (unitModule X))
    (f : denominatorIdeal X (unitModule X) s ⟶ unitModule X) : (cokernel f).IsCoherent :=
  have := isCoherent_denominatorIdeal_unitModule X s
  have : (unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  AlgebraicGeometry.isCoherent_cokernel f

/-- **Stacks 02SW part (2) for `L = 𝒪_X`, first quotient.** The quotient of `𝒪_X` by the ideal of
denominators of a meromorphic section of `𝒪_X` is coherent. -/
theorem isCoherent_denominatorQuotientUnit (X : Scheme.{u}) [IsLocallyNoetherian X]
    (s : MeromorphicSection X.sheaf (unitModule X)) :
    (denominatorQuotientUnit X s).IsCoherent :=
  isCoherent_cokernel_denominator X s _

/-- **Stacks 02SW part (2) for `L = 𝒪_X`, second quotient.** The quotient of `𝒪_X` by the image
of the ideal of denominators of a meromorphic section `s` of `𝒪_X` under multiplication by `s` is
coherent. -/
theorem isCoherent_denominatorSectionQuotientUnit (X : Scheme.{u}) [IsLocallyNoetherian X]
    (s : MeromorphicSection X.sheaf (unitModule X)) :
    (denominatorSectionQuotientUnit X s).IsCoherent :=
  isCoherent_cokernel_denominator X s _

/-- A coherent module supported in the exceptional locus of a regular meromorphic section of
`𝒪_X` has support of delta-dimension at most `k`, if `dim_δ(X) ≤ k + 1`. -/
private theorem schemeDeltaDimension_reducedSupport_le_of_badLocus (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) (F : X.Modules) [F.IsCoherent]
    (hF : ∀ x ∈ SheafOfModules.supp F, x ∈ denominatorBadLocus X (unitModule X) s) :
    schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ p) ≤ (k : EInt) :=
  schemeDeltaDimension_reducedSupport_le C p F fun x hx =>
    relativeDimension_le_of_mem_denominatorBadLocus C p (unitModule X) s
      (isInvertible_unitModule X) hs hdim (hF x hx)

/-- **Stacks 02SW part (2) for `L = 𝒪_X`, first quotient.** If `dim_δ(X) ≤ k + 1`, the quotient
`𝒪_X/I` by the ideal of denominators of a regular meromorphic section of `𝒪_X` is supported in
delta-dimension at most `k`: its support is one half of the closed nowhere dense exceptional
subset of Stacks 02P2. -/
theorem schemeDeltaDimension_denominatorQuotientUnit_le (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsLocallyNoetherian X]
    (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) :
    schemeDeltaDimension C ((@reducedSupport X (denominatorQuotientUnit X s)
        (isCoherent_denominatorQuotientUnit X s)).subschemeι ≫ p) ≤ (k : EInt) := by
  have := isCoherent_denominatorQuotientUnit X s
  exact schemeDeltaDimension_reducedSupport_le_of_badLocus C p s hs hdim _ fun x hx =>
    Or.inl (by rwa [SheafOfModules.supp_eq_moduleSheaf_supp])

/-- **Stacks 02SW part (2) for `L = 𝒪_X`, second quotient.** If `dim_δ(X) ≤ k + 1`, the quotient
`𝒪_X/sI` is supported in delta-dimension at most `k`: its support is the other half of the closed
nowhere dense exceptional subset of Stacks 02P2. -/
theorem schemeDeltaDimension_denominatorSectionQuotientUnit_le (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsLocallyNoetherian X]
    (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) :
    schemeDeltaDimension C ((@reducedSupport X (denominatorSectionQuotientUnit X s)
        (isCoherent_denominatorSectionQuotientUnit X s)).subschemeι ≫ p) ≤ (k : EInt) := by
  have := isCoherent_denominatorSectionQuotientUnit X s
  exact schemeDeltaDimension_reducedSupport_le_of_badLocus C p s hs hdim _ fun x hx =>
    Or.inr (by rwa [SheafOfModules.supp_eq_moduleSheaf_supp])

/-! ### Short complexes of a dimension layer -/

/-- A short complex of `𝒪_X`-modules whose three terms are given as objects of `Coh_{≤b}(X)`,
read as a short complex of `Coh_{≤b}(X)`. -/
def shortComplexDimLE (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (b : ℤ) (A B Q : CoherentModulesDimLE C p b)
    (f : A.obj.obj ⟶ B.obj.obj) (g : B.obj.obj ⟶ Q.obj.obj) (w : f ≫ g = 0) :
    ShortComplex (CoherentModulesDimLE C p b) where
  X₁ := A
  X₂ := B
  X₃ := Q
  f := ObjectProperty.homMk (ObjectProperty.homMk f)
  g := ObjectProperty.homMk (ObjectProperty.homMk g)
  zero := ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ w)

/-- **The inclusion of a dimension layer reflects short exactness.** A short complex of
`Coh_{≤b}(X)` assembled by `Stacks.Chow.shortComplexDimLE` is short exact as soon as the
underlying short complex of `𝒪_X`-modules is. The two inclusions
`Coh_{≤b}(X) ⟶ Coh(𝒪_X) ⟶ Mod(𝒪_X)` are faithful and exact, being inclusions of weak Serre
subcategories, so each of them reflects short exactness. -/
theorem shortExact_shortComplexDimLE (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (b : ℤ) (A B Q : CoherentModulesDimLE C p b)
    (f : A.obj.obj ⟶ B.obj.obj) (g : B.obj.obj ⟶ Q.obj.obj) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) :
    (shortComplexDimLE C p b A B Q f g w).ShortExact :=
  ShortComplex.shortExact_of_shortExact_map (coherentModulesDimLE C p b).ι
    (ShortComplex.shortExact_of_shortExact_map
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι hS)

/-! ### The four objects of the presentation -/

/-- `𝒪_X` as an object of `Coh_{≤b}(X)`, for a scheme of delta-dimension at most `b` over the
base of a Chow situation. -/
def structureSheafDimLE (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {b : ℤ} (hdim : schemeDeltaDimension C p ≤ (b : EInt)) :
    CoherentModulesDimLE C p b :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hcoh : (unitModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  ⟨⟨unitModule X, AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hcoh⟩,
    schemeDeltaDimension_reducedSupport_le_of_le C p (unitModule X) hdim⟩

/-- The ideal of denominators of a meromorphic section of `𝒪_X`, as an object of `Coh_{≤b}(X)`
for a scheme of delta-dimension at most `b` over the base of a Chow situation. -/
def denominatorIdealDimLE (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (s : MeromorphicSection X.sheaf (unitModule X)) {b : ℤ}
    (hdim : schemeDeltaDimension C p ≤ (b : EInt)) :
    CoherentModulesDimLE C p b :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hcoh := isCoherent_denominatorIdeal_unitModule X s
  ⟨⟨denominatorIdeal X (unitModule X) s,
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent hcoh⟩,
    schemeDeltaDimension_reducedSupport_le_of_le C p (denominatorIdeal X (unitModule X) s) hdim⟩

/-- `𝒪_X/I` as an object of `Coh_{≤k}(X)`, where `I` is the ideal of denominators of a regular
meromorphic section of `𝒪_X` on a scheme of delta-dimension at most `k + 1`. -/
def denominatorQuotientUnitDimLE (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) :
    CoherentModulesDimLE C p k :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  ⟨⟨denominatorQuotientUnit X s,
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
        (isCoherent_denominatorQuotientUnit X s)⟩,
    schemeDeltaDimension_denominatorQuotientUnit_le C p s hs hdim⟩

/-- `𝒪_X/sI` as an object of `Coh_{≤k}(X)`, where `I` is the ideal of denominators of a regular
meromorphic section `s` of `𝒪_X` on a scheme of delta-dimension at most `k + 1`. -/
def denominatorSectionQuotientUnitDimLE (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) :
    CoherentModulesDimLE C p k :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  ⟨⟨denominatorSectionQuotientUnit X s,
      AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
        (isCoherent_denominatorSectionQuotientUnit X s)⟩,
    schemeDeltaDimension_denominatorSectionQuotientUnit_le C p s hs hdim⟩

/-! ### The two sequences in the dimension layer -/

/-- **Stacks 02SW part (1) for `L = 𝒪_X`, first sequence, in the dimension layer.** The short
complex `0 ⟶ I ⟶ 𝒪_X ⟶ 𝒪_X/I ⟶ 0` of `Coh_{≤k+1}(X)`, with its third term the image of
`𝒪_X/I ∈ Coh_{≤k}(X)` under the inclusion of dimension layers. -/
def denominatorShortComplexUnit (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) :
    ShortComplex (CoherentModulesDimLE C p (k + 1)) :=
  shortComplexDimLE C p (k + 1) (denominatorIdealDimLE C p s hdim) (structureSheafDimLE C p hdim)
    ((dimensionLayerInclusion C p k).obj (denominatorQuotientUnitDimLE C p s hs hdim))
    (denominatorIdealι X (unitModule X) s)
    (cokernel.π (denominatorIdealι X (unitModule X) s)) (cokernel.condition _)

/-- **Stacks 02SW part (1) for `L = 𝒪_X`, second sequence, in the dimension layer.** The short
complex `0 ⟶ I ⟶^{s} 𝒪_X ⟶ 𝒪_X/sI ⟶ 0` of `Coh_{≤k+1}(X)`, with its third term the image of
`𝒪_X/sI ∈ Coh_{≤k}(X)` under the inclusion of dimension layers. -/
def denominatorSectionShortComplexUnit (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) :
    ShortComplex (CoherentModulesDimLE C p (k + 1)) :=
  shortComplexDimLE C p (k + 1) (denominatorIdealDimLE C p s hdim) (structureSheafDimLE C p hdim)
    ((dimensionLayerInclusion C p k).obj (denominatorSectionQuotientUnitDimLE C p s hs hdim))
    (denominatorIdealMul X (unitModule X) s)
    (cokernel.π (denominatorIdealMul X (unitModule X) s)) (cokernel.condition _)

/-- **Stacks 02SW part (1) for `L = 𝒪_X`, first sequence.** The inclusion of the ideal of
denominators into `𝒪_X` sits in a short exact sequence of `Coh_{≤k+1}(X)` with its cokernel. -/
theorem shortExact_denominatorShortComplexUnit (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) :
    (denominatorShortComplexUnit C p s hs hdim).ShortExact :=
  shortExact_shortComplexDimLE C p (k + 1) _ _ _ _ _ _
    (AlgebraicGeometry.shortExact_denominatorIdealι X s)

/-- **Stacks 02SW part (1) for `L = 𝒪_X`, second sequence.** Multiplication by a regular
meromorphic section of `𝒪_X` embeds its ideal of denominators into `𝒪_X` and sits in a short
exact sequence of `Coh_{≤k+1}(X)` with its cokernel. -/
theorem shortExact_denominatorSectionShortComplexUnit (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X]
    (s : MeromorphicSection X.sheaf (unitModule X))
    (hs : IsRegularMeromorphicSection X.sheaf (unitModule X) s) {k : ℤ}
    (hdim : schemeDeltaDimension C p ≤ ((k + 1 : ℤ) : EInt)) :
    (denominatorSectionShortComplexUnit C p s hs hdim).ShortExact :=
  shortExact_shortComplexDimLE C p (k + 1) _ _ _ _ _ _
    (AlgebraicGeometry.shortExact_denominatorIdealMul X s hs)

/-! ### The coefficients of the two quotient cycles -/

/-- At a point whose closure does not have delta-dimension `k`, the coefficient of the cycle of an
object of `Coh_{≤k}(X)` vanishes. -/
theorem dimensionLayerCycle_apply_of_relativeDimension_ne (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (Q : CoherentModulesDimLE C p k) {x : X}
    (hx : relativeDimension C.dimensionFunction p x ≠ k) :
    (dimensionLayerCycle C p k Q : AlgebraicCycle X ℤ) x = 0 :=
  have : _root_.SheafOfModules.IsCoherent Q.obj.obj :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent Q.obj.property
  cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C p Q.obj.obj k Q.property hx

/-- **The coefficient identity of the proof of Stacks 0FDS.** On an integral scheme of
delta-dimension `k + 1` over the base of a Chow situation, the coefficient at a point `x` of the
difference of the cycles of `𝒪_X/gI` and of `𝒪_X/I` is the order of vanishing of `g` at `x`.

At a point of relative dimension `k` — equivalently, by Stacks 02RK, a point of codimension one —
both coefficients are multiplicities and the identity is
`AlgebraicGeometry.sheafMultiplicity_denominator_sub_eq_ord`. At any other point both
coefficients vanish, and so does the order of vanishing. -/
theorem dimensionLayerCycle_denominatorQuotientUnit_sub_apply (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X]
    [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt)) (g : X.functionFieldˣ) (x : X) :
    (dimensionLayerCycle C p k (denominatorSectionQuotientUnitDimLE C p
          (AlgebraicGeometry.meromorphicSectionOfFunctionField X g)
          (AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField X g)
          hdim.le) : AlgebraicCycle X ℤ) x -
        (dimensionLayerCycle C p k (denominatorQuotientUnitDimLE C p
          (AlgebraicGeometry.meromorphicSectionOfFunctionField X g)
          (AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField X g)
          hdim.le) : AlgebraicCycle X ℤ) x =
      X.ord (g : X.functionField) x := by
  have hiff := relativeDimension_eq_sub_one_iff_coheight_eq_one C p hdim x
  simp only [add_sub_cancel_right] at hiff
  by_cases hx : relativeDimension C.dimensionFunction p x = k
  · rw [dimensionLayerCycle_apply_of_relativeDimension_eq C p k _ hx,
      dimensionLayerCycle_apply_of_relativeDimension_eq C p k _ hx]
    exact AlgebraicGeometry.sheafMultiplicity_denominator_sub_eq_ord g (hiff.mp hx)
  · rw [dimensionLayerCycle_apply_of_relativeDimension_ne C p k _ hx,
      dimensionLayerCycle_apply_of_relativeDimension_ne C p k _ hx,
      X.ord_eq_zero_of_coheight_neq_one (fun h => hx (hiff.mpr h)) (g : X.functionField),
      sub_zero]

/-! ### The cycle identity -/

/-- **The cycle identity of the proof of Stacks 0FDS.** On an integral scheme `X` of
delta-dimension `k + 1` over the base of a Chow situation, the difference of the `k`-cycles of
`𝒪_X/gI` and of `𝒪_X/I` is the principal divisor of `g`: any `k`-cycle whose coefficient at every
point is the order of vanishing of `g` there equals that difference.

This is the orientation that the distance function of Stacks 02MG gives — additivity along
`𝒪_X ⊇ I, gI` reads `d(𝒪_X, gI) − d(𝒪_X, I) = d(I, gI) = ord(g)`; the source states the difference
the other way round. -/
theorem dimensionLayerCycle_denominatorQuotientUnit_sub_eq (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X]
    [IsLocallyNoetherian X] {k : ℤ}
    (hdim : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt)) (g : X.functionFieldˣ)
    {c : CycleGroup C p k}
    (hc : ∀ x : X, (c : AlgebraicCycle X ℤ) x = X.ord (g : X.functionField) x) :
    dimensionLayerCycle C p k (denominatorSectionQuotientUnitDimLE C p
          (AlgebraicGeometry.meromorphicSectionOfFunctionField X g)
          (AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField X g)
          hdim.le) -
        dimensionLayerCycle C p k (denominatorQuotientUnitDimLE C p
          (AlgebraicGeometry.meromorphicSectionOfFunctionField X g)
          (AlgebraicGeometry.isRegularMeromorphicSection_meromorphicSectionOfFunctionField X g)
          hdim.le) = c := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x => ?_)
  rw [hc x]
  exact dimensionLayerCycle_denominatorQuotientUnit_sub_apply C p hdim g x

end Stacks.Chow

end
