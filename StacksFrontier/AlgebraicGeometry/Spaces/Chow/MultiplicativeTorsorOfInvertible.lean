module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged

/-!
# The multiplicative torsor of an invertible sheaf on a good algebraic space

In Situation 0EDT let `X/B` be good and let `ℒ` be an invertible `𝒪_X`-module.  The small étale
site of `X` is locally ringed, so `ℒ` is trivial on an étale covering of `X`, its Laurent algebra
`⨁_{n ∈ ℤ} ℒ^{⊗ n}` is quasi-coherent, and the multiplicative torsor
`q : T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n}) ⟶ X` needs no hypothesis on `ℒ` beyond
invertibility.  Two properties of `q` come with its construction: `q` is affine, and forming it
commutes with arbitrary base change.

The quasi-coherence of the Laurent algebra is proved here and is unconditional.  The two
statements about `q`, however, are made under the parameters `E` and `C` that
`AlgebraicGeometry.Space.relativeSpec` carries, and `E` is **empty** over any site one of whose
algebraic spaces has an affine étale chart with a nonzero ring of functions, so over such a site
they assert nothing; see the implementation notes below.  `T`, `q` and the affineness of `q`
without any parameter are in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorSpectrum`.

## Main definitions

* `AlgebraicGeometry.Space.multiplicativeTorsorBaseChange`: the relative spectrum over `Y` of
  the pullback `g^*(⨁_{n ∈ ℤ} ℒ^{⊗ n})` along `g : Y ⟶ X`, and
  `AlgebraicGeometry.Space.multiplicativeTorsorBaseChangeProjection` its projection to `T`.

## Main results

* `AlgebraicGeometry.Space.isLocallyTrivial_of_isInvertibleSheaf`: **an invertible `𝒪_X`-module is
  trivial on an étale covering of `X`.**
* `AlgebraicGeometry.Space.isQuasicoherent_laurentAlgebraSheaf`: **the Laurent algebra sheaf of an
  invertible `𝒪_X`-module is quasi-coherent.**
* `AlgebraicGeometry.Space.isAffineHom_multiplicativeTorsorProjection`: `q` is affine — but under
  the parameter `E` below, which is empty over any nondegenerate site, so the statement asserts
  nothing there.  For `q` affine under the hypotheses of Situation 0EDT alone, see
  `AlgebraicGeometry.Space.isAffineHom_multiplicativeTorsorSpectrumProjection`.
* `AlgebraicGeometry.Space.isPullback_multiplicativeTorsorBaseChange`: the base change of `q`
  along `g : Y ⟶ X` is cartesian, with corner `\underline{Spec}_Y(g^*(⨁_{n ∈ ℤ} ℒ^{⊗ n}))` —
  again under `E`, and under `C`, so again vacuous over any nondegenerate site.

## Implementation notes

Local triviality comes from
`Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_locallyEitherUnit`, the converse clause of
Tag 0B8Q, together with `AlgebraicGeometry.Space.locallyEitherUnit_structureSheaf'`, the
local-unit conjunct of Tag 04KH for the small étale site.  Of the two forms of that converse it
is the one leaving the universe of the sections free that applies, the small étale site of an
algebraic space having its objects one universe above its morphisms and its sections.

The base change of `T` is stated with `\underline{Spec}_Y(g^*(⨁_{n ∈ ℤ} ℒ^{⊗ n}))` itself as the
corner of the cartesian square rather than the abstract base change supplied by Tag 081V:
`AlgebraicGeometry.Space.relativeSpecBaseChangeAffineIso` identifies the two and
`CategoryTheory.IsPullback.of_iso'` transports the square across it.

**The parameters `E` and `C` empty the statements that carry them.**  `T` and `q` are formed here
through `AlgebraicGeometry.Space.relativeSpec`, which takes an inhabitant `E` of
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence` — Tag 081V with the tag's unrestricted
target — and `C` a base-change clause for that `E`.  Over any site one of whose algebraic spaces
has an affine étale chart with a nonzero ring of functions, `E` is empty, by
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`: an
affine morphism has fewer than `B.cutoff` sections over a chart (Tag 03G8) while a quasi-coherent
algebra is under no such bound, so no anti-equivalence can identify the two.  So over any such
site the two theorems below that take `E` assert nothing, and nothing that takes `E` constructs
`T` or `q` from the hypotheses of Situation 0EDT.  Carrying `E` is not forced: Tag 081W holds for
every quasi-coherent algebra with no parameter at all, over the enlargement of the site that
Tag 03FO supplies (`AlgebraicGeometry.Space.relativeSpectrum`), and inside the site itself for
every algebra satisfying the size condition of the corrected Tag 081V
(`AlgebraicGeometry.Space.boundedRelativeSpec`).  `T`, `q` and the affineness of `q` are formed
both of those ways, with no parameter and under the hypotheses of Situation 0EDT alone, in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorSpectrum`.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-! ### Local triviality and quasi-coherence -/

include hL in
/-- An invertible `𝒪_X`-module on an algebraic space `X` is trivial on an étale covering of `X`. -/
theorem isLocallyTrivial_of_isInvertibleSheaf :
    Stacks.SheafOfModules.Invertible.IsLocallyTrivial
      (R := tensorStructureSheaf D p hp) L :=
  have : Stacks.SheafOfModules.IsInvertible (structureSheaf' D.site D.base D.base_mem X).obj
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  Stacks.SheafOfModules.Invertible.isLocallyTrivial_of_locallyEitherUnit
    (structureSheaf' D.site D.base D.base_mem X)
    (isSheaf_tensorStructureRingPresheaf D p hp) L
    (locallyEitherUnit_structureSheaf' D.site D.base D.base_mem X)

/-- The Laurent algebra sheaf `⨁_{n ∈ ℤ} ℒ^{⊗ n}` of an invertible `𝒪_X`-module `ℒ` is
quasi-coherent. -/
@[stacks 0EQG "the quasi-coherence of ⨁_{n ∈ ℤ} L^{⊗n} that clause (1) presupposes in forming
T = Spec_X(⨁_{n ∈ ℤ} L^{⊗n}): in Situation 0EDT with X/B good, the Laurent algebra of an
invertible O_X-module is a quasi-coherent O_X-algebra, with no hypothesis on L beyond
invertibility -- triviality of L on an etale covering is DISCHARGED here from local ringedness of
the small etale site, not assumed.  Nothing about the morphism q is covered by this
declaration"]
theorem isQuasicoherent_laurentAlgebraSheaf :
    AlgebraSheaf.IsQuasicoherent (laurentAlgebraSheaf D p hp L hL) :=
  isQuasicoherent_laurentAlgebraSheaf_of_isLocallyTrivial D p hp L hL
    (isLocallyTrivial_of_isInvertibleSheaf D p hp L hL)

/-! ### The torsor and its projection -/

variable (E : AffineAlgebraAntiEquivalence D.site D.base D.base_mem)

/-- The projection `q : T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n}) ⟶ X` of the multiplicative
torsor of an invertible `𝒪_X`-module is an affine morphism of algebraic spaces.

**This statement is vacuous over any nondegenerate site**, since the parameter `E` it takes is
empty there; see the implementation notes above.  The assertion under the hypotheses of
Situation 0EDT alone is
`AlgebraicGeometry.Space.isAffineHom_multiplicativeTorsorSpectrumProjection`. -/
@[stacks 0EQG "clause (1), the affineness part -- BUT VACUOUS AS STATED, and registered here only
because the base file carries this line.  The statement takes a parameter
E : AffineAlgebraAntiEquivalence, this development's rendering of Stacks 081V with the tag's
unrestricted target, and that type is EMPTY over any site one of whose algebraic spaces has an
affine etale chart with a nonzero ring of functions
(not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart).  Over such a site this
theorem asserts nothing: quasi-coherence of the Laurent algebra, which IS discharged by
isQuasicoherent_laurentAlgebraSheaf, is discharged into a statement with no content.  THE
REGISTRATION THAT CARRIES THIS CLAUSE is
isAffineHom_multiplicativeTorsorSpectrumProjection (MultiplicativeTorsorSpectrum), which takes no
parameter at all; isAffineHom_boundedMultiplicativeTorsorProjection gives it inside the site of X
under the size condition of the corrected 081V, which E implies.  Read this line as covering
nothing"]
theorem isAffineHom_multiplicativeTorsorProjection :
    IsAffineHom D.site D.base D.base_mem (multiplicativeTorsorProjection D p hp L hL E
      (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)).hom :=
  (multiplicativeTorsor D p hp L hL E
    (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)).property

/-! ### Base change -/

variable (C : BaseChangeCompatibility D.site D.base D.base_mem E)
    {Y : AlgebraicSpaces D.site D.base D.base_mem} (g : Y ⟶ ⟨X, hp.1⟩)

/-- The relative spectrum over `Y` of the pullback `g^*(⨁_{n ∈ ℤ} ℒ^{⊗ n})` of the Laurent
algebra of `ℒ` along `g : Y ⟶ X`, as an algebraic space affine over `Y`. -/
def multiplicativeTorsorBaseChange : AffineOver D.site D.base D.base_mem Y :=
  relativeSpec D.site D.base D.base_mem E
    ((qcAlgebraPullback D.site D.base D.base_mem E C g).obj
      (laurentQuasicoherentAlgebra D p hp L hL (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)))

/-- The projection `\underline{Spec}_Y(g^*(⨁_{n ∈ ℤ} ℒ^{⊗ n})) ⟶ T` of the base change of the
multiplicative torsor of `ℒ` along `g : Y ⟶ X`. -/
def multiplicativeTorsorBaseChangeProjection :
    (multiplicativeTorsorBaseChange D p hp L hL E C g).obj.left ⟶
      multiplicativeTorsorSpace D p hp L hL E
        (isQuasicoherent_laurentAlgebraSheaf D p hp L hL) :=
  ((ObjectProperty.ι _ ⋙ Over.forget Y).mapIso
        (relativeSpecBaseChangeAffineIso D.site D.base D.base_mem E C g
          (laurentQuasicoherentAlgebra D p hp L hL
            (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)))).hom ≫
    C.affineBaseChange_projection g (multiplicativeTorsor D p hp L hL E
      (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))

/-- The base change of `q : T ⟶ X` along `g : Y ⟶ X` is cartesian, with corner
`\underline{Spec}_Y(g^*(⨁_{n ∈ ℤ} ℒ^{⊗ n}))`: forming the multiplicative torsor commutes with
arbitrary base change.

**This statement is vacuous over any nondegenerate site**, since the parameters `E` and `C` it
takes are empty there; see the implementation notes above. -/
@[stacks 0EQG "clause (3) for q: the base change of q along an arbitrary g : Y ⟶ X is cartesian
and Y ×_X T is the relative spectrum over Y of g^*(⨁_n L^{⊗n}), the latter being the corner of
the cartesian square as stated.
VACUOUS AS STATED: it takes the parameters E : AffineAlgebraAntiEquivalence and C its
base-change clause, and E is EMPTY over any site one of whose algebraic spaces has an affine
etale chart with a nonzero ring of functions
(not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart).  Over such a site this
theorem asserts nothing.  In particular, although Stacks 08AI at q -- the input the construction
of alpha : q^*L ≅ O_T consumes -- is genuinely discharged from X/B good and L invertible by
affineDirectImageEquivalence_multiplicativeTorsorProjection, that discharge is itself stated
under E and so is equally vacuous; it should not be read as evidence that this clause is in
better shape than it is.  Two further pieces of the source's clause (3) lie outside this
statement in any case: alpha itself, whose construction needs in addition the degree-shift
isomorphism of the Laurent algebra over itself, ⨁_n L^{⊗(n+1)} ≅ ⨁_n L^{⊗n}, which is clause
(2)'s own content and which this tree does not have (only the per-degree powSuccIso); and the
identification of g^*(⨁_n L^{⊗n}) with ⨁_n (g^*L)^{⊗n}.  No parameter-free counterpart of this
base-change square has been formed: MultiplicativeTorsorSpectrum supplies T, q and the
affineness of q without parameters, not the base change"]
theorem isPullback_multiplicativeTorsorBaseChange :
    IsPullback (multiplicativeTorsorBaseChangeProjection D p hp L hL E C g)
      (multiplicativeTorsorBaseChange D p hp L hL E C g).obj.hom
      (multiplicativeTorsorProjection D p hp L hL E
        (isQuasicoherent_laurentAlgebraSheaf D p hp L hL)) g := by
  refine (C.affineBaseChange_isPullback g (multiplicativeTorsor D p hp L hL E
      (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))).of_iso'
    ((ObjectProperty.ι _ ⋙ Over.forget Y).mapIso
      (relativeSpecBaseChangeAffineIso D.site D.base D.base_mem E C g
        (laurentQuasicoherentAlgebra D p hp L hL
          (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact Over.w (relativeSpecBaseChangeAffineIso D.site D.base D.base_mem E C g
      (laurentQuasicoherentAlgebra D p hp L hL
        (isQuasicoherent_laurentAlgebraSheaf D p hp L hL))).hom.hom
  · simp
  · simp

end AlgebraicGeometry.Space

end
