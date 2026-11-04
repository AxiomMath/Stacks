module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineOpenTensorSections
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChart

/-!
# The degreewise piece comparison of the relative twist, over an affine open

In the setting of Tag 02NB — `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible
`𝒪_S`-module, `ℬ_d = 𝒜_d ⊗_{𝒪_S} ℒ^{⊗ d}` its twist — this file proves that over an **affine
open** `V` of the base the sections of `ℬ_d` are the tensor product of the sections:

$$\Gamma(V, \mathcal{B}_d) \;\cong\; \Gamma(V, \mathcal{A}_d)
\otimes_{\Gamma(S,V)} \Gamma(V, \mathcal{L}^{\otimes d}).$$

This is the affine tensor-sections isomorphism of
`Stacks.AlgebraicGeometry.AffineOpenTensorSections.gammaTensorEquiv` applied at the pair
`(𝒜_d, ℒ^{⊗ d})`, and it is available because the twist's homogeneous piece **is** that tensor
product: `Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist` has
`piece d = tensorSheaf (𝒜.piece d) (ℒ^{⊗ d})`, which is definitionally the monoidal product the
isomorphism is stated for. No comparison of tensor-product spellings is needed.

## Why this is the shape the twisting data wants

`Stacks.GradedRing.InvertibleTwist` — the hypothesis the whole absolute Tag 02NC development is
parameterised by — has exactly three fields: a
family of linear equivalences `piece d : 𝒜_d ⊗_R 𝓛_d ≃ₗ[R] ℬ_d`, its multiplicativity
`piece_mul`, and its unitality `piece_one`. Over an affine open `V`, with `R = Γ(S, V)`, **all
three are proved below** — `twistPieceSectionsEquiv`, `gammaTmul_mul`, `gammaTmul_one`. What
remains between that and an `InvertibleTwist` term is the substrate, not the mathematics; see
"What is not proved here".

## The chart comparison is the canonical map

`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt`, the degree-`d` comparison attached
to a section `x` of `ℒ` over `V`, is *definitionally* the canonical pure-tensor map applied to
`a ⊗ x^d`: `psiPieceAt_eq_gammaTmul` holds by `rfl`. So `psiPieceAt` factors through the
isomorphism as "tensor with `x^d`, then compare", which is `psiPieceAt_eq_equiv`, and its
bijectivity is equivalent to that of tensoring with `x^d` on sections —
`bijective_psiPieceAt_iff`. That reduces a question about a sheaf comparison to a question about
a single element of a module over `Γ(S, V)`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistPieceSectionsEquiv`: **the degreewise
  piece isomorphism** `Γ(V, 𝒜_d) ⊗_{Γ(S,V)} Γ(V, ℒ^{⊗ d}) ≃ Γ(V, ℬ_d)` over an affine open.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt_eq_gammaTmul`: the chart
  comparison is the canonical pure-tensor map, by `rfl`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt_eq_equiv`: it is the piece
  isomorphism precomposed with tensoring by `x^d`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.bijective_psiPieceAt_iff`: **the chart
  comparison in degree `d` is bijective exactly when tensoring with `x^d` is**, over an affine
  open.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.gammaTmul_mul`: **the canonical map is
  multiplicative**, which is the `piece_mul` field of `Stacks.GradedRing.InvertibleTwist` in the
  relative setting.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.gammaTmul_one`: **the unit of the twist is
  the pure tensor of the two units**, which is the `piece_one` field.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.span_twistPieceSections_eq_top`: the pure
  tensors span the sections of `ℬ_d` over an affine open.

## Quasi-coherence

Both factors are quasi-coherent with no hypothesis beyond invertibility of `ℒ`, so every
statement below is unconditional. `𝒜.piece d` is quasi-coherent by the `isQuasicoherent` field of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`, which is an instance. The
tensor power is handled by `isQuasicoherent_tpMod`: the power of an invertible module is again
invertible, and an invertible module on a scheme is finite locally free of rank one. The
invertibility has to be passed to that lemma by hand, because instance search does not cross
from the `S.ringCatSheaf.property` spelling of the structure sheaf to the
`structureSheafRing S.toRingedSpace` one — which is the same manoeuvre the `isQuasicoherent`
field of `Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist` makes for this very term.

## What is not proved here

**No `InvertibleTwist` term is constructed.** The three fields' mathematical content is proved;
what is missing is one object, and it is named precisely below rather than gestured at.

*Not missing: the `Submodule` substrate.* `InvertibleTwist` wants `Submodule R`-valued gradings
while `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.grading` is
`AddSubgroup`-valued, but the refinement exists and is already applied to this very grading:
`Stacks.GradedRing.toSubmodules` promotes an `AddSubgroup`-valued graded ring over an algebra to
a `Submodule R`-valued one, `Stacks.GradedRing.instGradedRingToSubmodules` is the
`GradedAlgebra` instance it carries, and
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.gradingEquiv` is the composite at
`𝒜.grading V`, over the algebra `sectionRingAlgebra` induced by `strHom`. So `𝒜` and `ℬ` present
no obstacle.

*Not missing: invertibility of the sections.* `Stacks.Discriminant`
`.isInvertible_iff_forall_module_invertible` says an invertible module on a scheme is exactly a
quasi-coherent one whose sections over every affine open are an invertible module over the
functions there, so `Module.Invertible Γ(S, V) Γ(ℒ, V)` is available — which is the hypothesis
`Stacks.GradedRing.InvertibleTwist.exists_dual_notMem` and the chart cover
`iSup_mapDomain_twistHomOf_eq_top` need in their `Module.Invertible R ↥(𝓛 1)` slot.

*Missing: the tensor-power ring.* `InvertibleTwist` needs a single commutative ring `T` over
`Γ(S, V)` carrying the tensor powers as a `Submodule Γ(S,V)`-valued family `𝓛` satisfying
`Stacks.GradedRing.IsTensorPowerFamily`. Both classes are inhabited:
`Stacks.GradedRing.identityTwist` is an `InvertibleTwist`, and
`Stacks.GradedRing.isTensorPowerFamily_span_pow`,
`Stacks.GradedRing.Polynomial.isTensorPowerFamily_span_X_pow` and
`Stacks.GradedRing.isTensorPowerFamily_one` are terms of `IsTensorPowerFamily`. What is still
missing is a term for *this* family, the tensor powers of `ℒ` over an affine open.
Three commutative rings `⨁_n Γ(ℒ^{⊗ n})` do exist
(`Stacks.SheafOfModules.sectionRing`, `Stacks.GradedSections.sectionRing`, and the
`Hom`-spelling of `Stacks.Divisors.InvertibleSections`), each with an `AddSubgroup`-valued
grading that `toSubmodules` would promote, but all three are taken over global sections rather
than over an affine open, and none carries an `Algebra Γ(S, V)` structure.

Of the four `IsTensorPowerFamily` fields, `algebraMap_injective` and `degree_zero` are routine
once that structure map is in place, and the other two need **no transport at all** of
`gammaTensorEquiv` across the coherent multiplication `ℒ^{⊗ i} ⊗ ℒ^{⊗ j} ≅ ℒ^{⊗ (i + j)}`:
`Stacks.GradedRing.isTensorPowerFamily_of_invertible` supplies both fields from invertibility of
the members alone, because `Submodule.mulMap'` is surjective onto the product submodule for free
and a surjection between invertible modules is bijective. Invertibility of the members is
available by `Stacks.Discriminant.isInvertible_iff_forall_module_invertible`, as recorded above.

Nor is any of this what stands between this file and the chart-level statement of the tag. That
statement is proved, without an `InvertibleTwist` term, in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChartIso`: the
degreewise bijectivity of `bijective_psiPieceAt` is carried to the homogeneous components of the
graded ring of sections and fed to `Stacks.AlgebraicGeometry.RelativeProjChain`'s
`isIso_mapHom_of_eventually_bijective`, giving `Proj ℬ(V) ≅ Proj 𝒜(V)` over every open of the
base carrying a trivializing section. The degreewise half of the canonicity of that isomorphism
is `StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeCanonical`, and the
glueing over the base is `ProjInvertibleTwistRelativeGluing.lean`.

Nothing here carries a `stacks` attribute: these are statements over one chart.

## References

* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory PresheafOfModules
open scoped AlgebraicGeometry TensorProduct
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

open Stacks.AlgebraicGeometry.AffineOpenTensorSections

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf Stacks.Algebraization.sectionsSMulCommClassΓ
  Stacks.Algebraization.sectionsModuleΓPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafPresheaf
  Stacks.Algebraization.sectionsModuleΓSheafVal

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]

/-- The `d`-th tensor power of the twisting module, retyped as an object of
`AlgebraicGeometry.Scheme.Modules`. The two spellings are the same type; the ascription is what
lets the affine tensor-sections isomorphism be applied to it. -/
abbrev tpMod (d : ℤ) : S.Modules := tp L d

/-- **Every tensor power of the twisting module is quasi-coherent.** The power is again
invertible by `Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower`, and an invertible
module on a scheme is finite locally free of rank one, hence quasi-coherent.

The invertibility is passed as an explicit argument rather than found: instance search does not
cross from the `S.ringCatSheaf.property` spelling of the structure sheaf to the
`structureSheafRing S.toRingedSpace` one. This is the argument the `isQuasicoherent` field of
`Stacks.AlgebraicGeometry.GradedAlgebraTwist.twist` already makes for the same term. -/
instance isQuasicoherent_tpMod (d : ℤ) : (tpMod L d).IsQuasicoherent :=
  have hinv : Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property
      (tpMod L d) :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower S.sheaf.obj
      S.ringCatSheaf.property L d
  @Stacks.SheafOfModules.Scheme.isQuasicoherent_of_isInvertible S _ hinv

/-- The `d`-th power of a local section of the twisting module over an open, at the `Γ(·, ·)`
spelling of the sections. The two spellings are the same type; the ascription is what lets the
pure tensor `a ⊗ x^d` be elaborated with no expected type to guide it. -/
abbrev powSecAtMod (V : S.Opens) (x : (tp L 1).val.obj (op V)) (d : ℕ) :
    Γ(tpMod L (d : ℤ), V) := powSecAt L (op V) x d

variable (𝒜 : SheafGradedAlgebra S)

/-- The homogeneous piece of the twist **is** the monoidal product of the piece of `𝒜` with the
tensor power of `ℒ`. Both sides are `tensorSheaf (𝒜.piece d) (ℒ^{⊗ d})`; the two spellings of the
tensor product of sheaves of modules are definitionally equal. -/
theorem twist_piece_eq (d : ℤ) :
    tensorMod (𝒜.piece d) (tpMod L d) = (twist 𝒜 L).piece d := rfl

variable {V : S.Opens}

/-- **The degreewise piece isomorphism of the relative twist over an affine open**:

`Γ(V, 𝒜_d) ⊗_{Γ(S,V)} Γ(V, ℒ^{⊗ d}) ≃ Γ(V, ℬ_d)`

for `V` an affine open of the base. This is the affine tensor-sections isomorphism at the pair
`(𝒜_d, ℒ^{⊗ d})`, read through `twist_piece_eq`, and it is the first field of
`Stacks.GradedRing.InvertibleTwist` in the setting of Tag 02NB. -/
def twistPieceSectionsEquiv (hV : IsAffineOpen V) (d : ℤ) :
    (Γ(𝒜.piece d, V) ⊗[Γ(S, V)] Γ(tpMod L d, V)) ≃ₗ[Γ(S, V)] Γ((twist 𝒜 L).piece d, V) :=
  gammaTensorEquiv hV (𝒜.piece d) (tpMod L d)

/-- The piece isomorphism carries a pure tensor of sections to the pure tensor local section. -/
theorem twistPieceSectionsEquiv_tmul (hV : IsAffineOpen V) (d : ℤ)
    (a : Γ(𝒜.piece d, V)) (b : Γ(tpMod L d, V)) :
    twistPieceSectionsEquiv L 𝒜 hV d (a ⊗ₜ[Γ(S, V)] b) =
      gammaTmul (𝒜.piece d) (tpMod L d) V a b :=
  rfl

/-- **The chart-level comparison is the canonical pure-tensor map.** The degree-`d` comparison
attached to a section `x` of `ℒ` over `V` sends `a` to the canonical image of `a ⊗ x^d`; the two
are the same term.

This is what identifies `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt` with the
data the twisting structure of Tag 02NB asks for. -/
theorem psiPieceAt_eq_gammaTmul (V : S.Opens) (x : (tp L 1).val.obj (op V)) (d : ℕ)
    (a : 𝒜.sectionPieces V d) :
    psiPieceAt L 𝒜 V x d a =
      gammaTmul (𝒜.piece (d : ℤ)) (tpMod L d) V a (powSecAtMod L V x d) :=
  rfl

/-- **The chart comparison factors through the piece isomorphism**: it is tensoring with `x^d`,
followed by the isomorphism. -/
theorem psiPieceAt_eq_equiv (hV : IsAffineOpen V) (x : (tp L 1).val.obj (op V)) (d : ℕ)
    (a : 𝒜.sectionPieces V d) :
    psiPieceAt L 𝒜 V x d a =
      twistPieceSectionsEquiv L 𝒜 hV (d : ℤ)
        (a ⊗ₜ[Γ(S, V)] powSecAtMod L V x d) :=
  rfl

/-- **Over an affine open the chart comparison in degree `d` is bijective exactly when tensoring
with `x^d` is.** The comparison is that tensoring followed by the piece isomorphism, so the two
bijectivity statements differ by a bijection.

This reduces the degreewise invertibility that the absolute machinery of Tag 01MY consumes to a
statement about a single element of the `Γ(S, V)`-module of sections of `ℒ^{⊗ d}`, with no sheaf
comparison left in it. `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.bijective_psiPieceAt`
gives the same conclusion from a trivializing isomorphism of sheaves instead. -/
theorem bijective_psiPieceAt_iff (hV : IsAffineOpen V) (x : (tp L 1).val.obj (op V)) (d : ℕ) :
    Function.Bijective (psiPieceAt L 𝒜 V x d) ↔
      Function.Bijective (fun a : Γ(𝒜.piece (d : ℤ), V) =>
        a ⊗ₜ[Γ(S, V)] powSecAtMod L V x d) :=
  EquivLike.comp_bijective (fun a : Γ(𝒜.piece (d : ℤ), V) => a ⊗ₜ[Γ(S, V)] powSecAtMod L V x d)
    (twistPieceSectionsEquiv L 𝒜 hV (d : ℤ))

/-- **The canonical map is multiplicative**: the product in the twist of two pure tensors is the
pure tensor of the two products, that of `𝒜` and that of the tensor powers of `ℒ`.

This is the `piece_mul` field of `Stacks.GradedRing.InvertibleTwist`, in the relative setting and
over an arbitrary open. Unlike
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiPieceAt_mul` the two second factors are
independent — neither is tied to a power of a section of `ℒ` — which is what the field asks for.

No heterogeneous equality appears: both sides are sections of the piece in degree `i + j`, and
the degree is the same spelling on both sides, so the `pieceReindex` bookkeeping that genuinely
distinct spellings of a degree would need is not in play. -/
theorem gammaTmul_mul (i j : ℤ) (V : S.Opens)
    (a : Γ(𝒜.piece i, V)) (l : Γ(tpMod L i, V))
    (b : Γ(𝒜.piece j, V)) (m : Γ(tpMod L j, V)) :
    ((twist 𝒜 L).mul i j).app V
        (gammaTmul (𝒜.piece i) (tpMod L i) V a l)
        (gammaTmul (𝒜.piece j) (tpMod L j) V b m) =
      gammaTmul (𝒜.piece (i + j)) (tpMod L (i + j)) V
        ((𝒜.mul i j).app V a b) ((lmul L i j).app (op V) l m) := by
  refine Eq.trans (mulSection_pure S.sheaf.obj S.ringCatSheaf.property 𝒜.piece
    (mulHom 𝒜) L i j (op V) a l b m) ?_
  refine congrArg₂ (fun s t => gammaTmul (𝒜.piece (i + j)) (tpMod L (i + j)) V s t)
    (mulA_eq 𝒜 i j (op V) a b) ?_
  exact coherentMulIso_app_eq_mulBilinear S.sheaf.obj S.ringCatSheaf.property L i j (op V) l m

/-- **The unit of the twist is the pure tensor of the two units**: the canonical map carries
`1 ⊗ 1` to `1`, in degree `0` and over an arbitrary open.

This is the `piece_one` field of `Stacks.GradedRing.InvertibleTwist`, in the relative setting. It
is `psiPieceAt_one` read through `psiPieceAt_eq_gammaTmul`, at the zero section of `ℒ`: the
degree-`0` power of a section is the unit section whichever section it is, so the choice is
immaterial. -/
theorem gammaTmul_one (V : S.Opens) :
    gammaTmul (𝒜.piece 0) (tpMod L 0) V (𝒜.one V)
        ((Stacks.SheafOfModules.TensorPower.oneSection S.sheaf.obj S.ringCatSheaf.property
          L).eval (op V)) =
      (twist 𝒜 L).one V :=
  psiPieceAt_one L 𝒜 V 0

/-- **The pure tensors of sections span the sections of the twist in each degree**, over an
affine open of the base. This is the surjective half of the piece isomorphism. -/
theorem span_twistPieceSections_eq_top (hV : IsAffineOpen V) (d : ℤ) :
    Submodule.span Γ(S, V)
        (Set.range fun p : Γ(𝒜.piece d, V) × Γ(tpMod L d, V) =>
          gammaTmul (𝒜.piece d) (tpMod L d) V p.1 p.2) = ⊤ :=
  span_gammaTmul_eq_top hV (𝒜.piece d) (tpMod L d)

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
