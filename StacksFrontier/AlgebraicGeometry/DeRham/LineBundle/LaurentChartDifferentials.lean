module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.LaurentChartForms
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSectionsAffineOpen

/-!
# The relative `1`-forms of a Laurent chart

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module, and let
`L^⋆ ⟶ X` be the complement of the zero section of the line bundle. Over an affine open `U` of
`X` carrying a Laurent chart and mapping into an affine open `V` of `S`, the functions on the
inverse image of `U` in `L^⋆` are the Laurent polynomial algebra `Γ(X, U)[T;T⁻¹]` over
`Γ(S, V)`, by `Stacks.LineBundle.Situation.LaurentChart.sectionsAlgEquiv`.

This file computes the relative `1`-forms of `L^⋆` over `S` on that affine open: they are the
Kähler differentials of the Laurent polynomial algebra,

`Ω[Γ(X, U)[T;T⁻¹]⁄Γ(S, V)] ≅ Γ(Ω¹_{L^⋆/S}, π⁻¹U)`.

Three identifications compose to it. The algebra comparison of a chart is transported across by
Tag 01UT, which identifies the sections of the sheaf of relative differentials over an affine
open with the Kähler differentials of its ring of functions; the transport itself is
`Stacks.KaehlerDifferential.algEquivCongr`, the passage of a module of Kähler differentials
along an isomorphism of algebras; and the sheaf of relative differentials is identified with the
relative `1`-forms, the degree-one piece of the exterior algebra being the module itself.

The result is the affine local input of the residue sequence of Tag 0FUF: that sequence is
proved over a cover of `X` by affine opens carrying a chart, and over such an open the forms of
`L^⋆` are the forms of a Laurent polynomial algebra, where the residue is the ring-level
computation of `StacksFrontier.RingTheory.DeRham.LaurentResidue`.

## Main definitions

* `Stacks.KaehlerDifferential.algEquivCongr`: **transport of Kähler differentials along an
  isomorphism of algebras.** For `e : A ≃ₐ[R] B` the module `Ω[A⁄R]` is carried onto `Ω[B⁄R]`,
  linearly over `A` acting on the target through `e`. Stated for an arbitrary isomorphism of
  algebras rather than for the chart comparison alone, the comparisons of Tags 0FUH and 0FUI
  wanting the same transport.
* `Stacks.LineBundle.Situation.cotangentFormsOneIso`: **`Ω_{L^⋆/S} ≅ Ω¹_{L^⋆/S}`**, the sheaf of
  relative differentials of `L^⋆` over `S` read as the sheaf of relative `1`-forms.
* `Stacks.LineBundle.Situation.LaurentChart.cotangentEquiv`: **the relative differentials of
  `L^⋆` over an affine open carrying a chart**, `Ω[Γ(X, U)[T;T⁻¹]⁄Γ(S, V)] ≅ Γ(Ω_{L^⋆/S},
  π⁻¹U)`.
* `Stacks.LineBundle.Situation.LaurentChart.formsOneEquiv`: the same identification landing in
  the relative `1`-forms, `Ω[Γ(X, U)[T;T⁻¹]⁄Γ(S, V)] ≅ Γ(Ω¹_{L^⋆/S}, π⁻¹U)`.

## Main results

* `Stacks.KaehlerDifferential.algEquivCongr_D`: the transport carries `d a` to `d (e a)`, which
  pins it down, the differentials generating.
* `Stacks.LineBundle.Situation.app_cotangentSheafIso_inv_universalD` and
  `Stacks.LineBundle.Situation.sections_cotangentFormsOneIso_universalD`: the identification of
  the differentials with the `1`-forms **carries the universal differential of a function on
  `L^⋆` to its relative de Rham differential** as a `1`-form.
* `Stacks.LineBundle.Situation.LaurentChart.cotangentEquiv_D` and
  `Stacks.LineBundle.Situation.LaurentChart.formsOneEquiv_D`: **the identification carries the
  Kähler differential of a Laurent polynomial to the de Rham differential of the function it
  names**, which is what makes it an identification of de Rham forms and not merely of modules.

## Implementation notes

The target of the transport of Kähler differentials carries the scalars of the source through
the isomorphism, by `Module.compHom`, rather than the transport being stated as a semilinear
equivalence. That is the shape of
`AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv`, which this wraps, and it is
also what composes: each of the three identifications is linear over the ring that the previous
one has already transported, so the composites are assembled from the underlying additive
equivalences with the scalar law supplied by hand.

Each of the three steps crosses two spellings of one object that are equal by `rfl` but not at
reducible transparency — the sections of a morphism of sheaves of modules written with
`AlgebraicGeometry.Scheme.Modules.Hom.app` against the same thing written with `.val.app`, and
the Kähler differential of a derivation written with
`PresheafOfModulesOfCommRing.Derivation'.app` against
`PresheafOfModulesOfCommRing.Derivation.d`. A term-level `congrArg` crosses them; a `rw` cannot, its
motive being elaborated at reducible transparency. Every proof here is therefore a chain of
`congrArg` rather than a `rw`.

**What the global sequence of Tag 0FUF still needs.** The affine local side of that sequence is
complete: the ring-level sequence `0 → Ω^•_{A/R} → Ω^•_{A[T;T⁻¹]/R,0} → Ω^•_{A/R}[-1] → 0` is
short exact by `LaurentDeRham.shortExact_residueShortComplex`, and its residue is independent of
the coordinate by `LaurentDeRham.eq_of_mapExteriorPower_add_wedgeLeft_dlogUnit`, which is what
would let local residue maps be glued. The affine-open description of the degree-`n` part is
also available, as `Stacks.LineBundle.Situation.homogeneousSheafSubmodule_eq` together with
`Stacks.LineBundle.Situation.homogeneousSheafSubmodule_obj`. What is not available anywhere
below is the *sheaf-level middle complex*, and it is not a transport of any of these:

* **The differential.** `Stacks.LineBundle.Situation.laurentFormsPushforward` is a sheaf of
  `𝒪_X`-modules, and the de Rham differential is not `𝒪_X`-linear — already in degree zero the
  Leibniz rule gives `d(b b') = b d b' + b' d b`. So the middle term of the sequence is a
  complex of `f^{-1}𝒪_S`-modules, the restriction of scalars of the pushforward along
  `f^{-1}𝒪_S ⟶ 𝒪_X`, and no morphism of sheaves of modules
  `Ω^p_{L^⋆/S} ⟶ Ω^{p+1}_{L^⋆/S}` on `X` is constructed. The one piece of it that exists,
  `Stacks.LineBundle.Situation.gradedD`, is sectionwise and goes from functions to `1`-forms
  only. A pushforward of a de Rham complex is assembled elsewhere in the library, for modules
  on a ringed space in `Stacks.DeRhamPullback.deRhamPushforwardChain` and for abelian sheaves in
  `AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap`, and the total space has
  `Stacks.LineBundle.Situation.deRhamPushforward`; what is absent is the one for
  `AlgebraicGeometry.Scheme.Modules.pushforward`, the functor
  `Stacks.LineBundle.Situation.laurentFormsPushforward` is built from.

  **The abelian reading of that differential, however, costs nothing here, and this is worth
  knowing, since the `𝒪_X`-linear one cannot exist, for the Leibniz reason
  just given.** Two facts hold, each checkable by a standalone `example`. First,
  the generic bounded-below abelian pushforward of a de Rham complex,
  `AlgebraicGeometry.Scheme.Hom.deRhamPushforwardPlus`, instantiates at this situation with no
  new argument: `deRhamPushforwardPlus D.laurentSpectrumToBase D.laurentToBase` elaborates as a
  `CochainComplex.Plus` of abelian sheaves on `X`. Second, its degree-`p` term *is* the abelian
  sheaf underlying `laurentFormsPushforward p`, **by `rfl`**: pushing forward the `𝒪`-module and
  then forgetting to abelian sheaves agrees on the nose with forgetting and then pushing forward,
  because both are sections over the inverse image. So a differential
  `Ω^p_{L^⋆/S} ⟶ Ω^{p+1}_{L^⋆/S}` on the ambient of the middle term is already available at the
  abelian level, and the first bullet's absence is specifically the `𝒪_X`-module packaging. What
  this does *not* give is the subcomplex: see the next bullet.
* **Stability of the degree-`n` part under the differential**, which cannot be stated before
  the differential is. The statement to transport is the ring-level one,
  `KaehlerDifferential.deRhamDifferential_maps_gradedDifferentialFormComponent`, which says for
  an arbitrary grading of the algebra that the differential carries the degree-`g` part of
  `Ω^p` into the degree-`g` part of `Ω^{p+1}`. Turning the resulting stable family of
  sub-sheaves into a subcomplex has `Stacks.SheafOfModules.Submodule.restrictHom` for its
  degreewise step; there is no general "subcomplex from a stable family of sub-sheaves", only
  the one written out for torsion in `Stacks.IdealPowerTorsion.torsionComplex`.

  With the abelian differential in hand the stability statement *can* now be made, and its
  obstruction is a mismatch in the direction the two
  relevant wedge recursions run. The de Rham rule available on the differential is the
  `generator` field of `AlgebraicGeometry.SheafOfModules.DeRhamDifferential`, which computes
  `d (b • ω)` only for `ω` satisfying `AlgebraicGeometry.SheafOfModules.IsExactWedge`, and that
  predicate recurses on the **left** — `ω = d b ∧ η`. The homogeneity predicate
  `Stacks.LineBundle.Situation.IsHomogeneousLaurentForm` recurses on the **right** —
  `ω = η ∧ d a`. So applying the rule to a homogeneous form first asks that a right-recursive
  wedge be rewritten as a scalar multiple of a left-recursive one, and the degree-zero case of
  even that needs the unit laws of `Stacks.LineBundle.Situation.laurentFormsAlgebra` relating
  `1 ∧ d a` to `d a ∧ 1`. The ring-level statement to transport afterwards is unchanged,
  `KaehlerDifferential.deRhamDifferential_maps_gradedDifferentialFormComponent`, and the
  degree-zero homogeneity of the unit that the base case also needs is
  `Stacks.LineBundle.Situation.isHomogeneousLaurentForm_gradedOne`.
* **The two arrows**, the pullback `Ω^•_{X/S} ⟶ Ω^•_{L^⋆/S,0}` along the projection and the
  residue `Ω^•_{L^⋆/S,0} ⟶ Ω^•_{X/S}[-1]`, as morphisms of complexes of sheaves. Gluing the
  residue from its local formulas needs a morphism of sheaves of modules built from local data,
  and the construction available,
  `Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_cover`, is stated for sheaves of
  `𝒪_X`-modules, which by the previous point is the wrong category here.
  `Stacks.SheafOfModules.ComplexGlue.mkHomOfLocallyComm` does not help with this: it takes the
  degreewise morphisms as given and glues only their commutation with the differential.
* **The degreewise affine comparison for every `p`.** The identification proved in this file is
  `p = 1`, while the ring-level sequence lives on `⋀^p Ω[Γ(X, U)[T;T⁻¹]⁄Γ(S, V)]`, so what is
  owed is the exterior power of this identification together with a matching of the sections of
  the degree-zero part over `U` with `LaurentDeRham.weightComponent`.

One further mismatch is worth recording, since it is not visible from the statement of the
gluing lemma. `Stacks.SheafOfModules.ComplexGlue.shortExact_of_degreewise_isAffineOpen` asks for
exactness of the sections over *every* affine open of `X`, whereas a Laurent chart is available
only over an affine open that trivializes `L` and maps into an affine open of `S`. Such opens
cover `X`, by `Stacks.LineBundle.Situation.exists_trivializing_affineOpen_over_affine`, and so
are a basis once one knows they can be found inside an arbitrary open, but a basis is still not
all affine opens: either the local input has to be obtained over an arbitrary affine open or
that lemma needs a version over a basis.

## References

* [Stacks Project, Tag 0FUF](https://stacks.math.columbia.edu/tag/0FUF), the residue sequence
  this is the affine local input of
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT), the differentials of an
  affine open
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9), the grading of the de
  Rham complex of a graded algebra
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.KaehlerDifferential

/-- **Transport of Kähler differentials along an isomorphism of algebras.** An isomorphism
`e : A ≃ₐ[R] B` of `R`-algebras carries the module of Kähler differentials of `A` over `R` onto
that of `B` over `R`, linearly over `A` acting on the target through `e`.

This is `AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv` at the square whose base
side is the identity of `R`: a pair of ring isomorphisms commuting with the algebra maps, here
`e` itself and `RingEquiv.refl R`, the commuting square being `AlgEquiv.commutes`. -/
def algEquivCongr {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (e : A ≃ₐ[R] B) :
    letI : Algebra A B := e.toRingEquiv.toRingHom.toAlgebra
    letI : Module A (Ω[B⁄R]) := Module.compHom _ e.toRingEquiv.toRingHom
    Ω[A⁄R] ≃ₗ[A] Ω[B⁄R] :=
  AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv (RingEquiv.refl R)
    e.toRingEquiv e.commutes

/-- **The transport carries universal differentials to universal differentials**: `d a` goes to
`d (e a)`. Since the differentials generate `Ω[A⁄R]` as an `A`-module this pins the transport
down. -/
theorem algEquivCongr_D {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (e : A ≃ₐ[R] B) (a : A) :
    letI : Algebra A B := e.toRingEquiv.toRingHom.toAlgebra
    letI : Module A (Ω[B⁄R]) := Module.compHom _ e.toRingEquiv.toRingHom
    algEquivCongr e (_root_.KaehlerDifferential.D R A a)
      = _root_.KaehlerDifferential.D R B (e a) :=
  AlgebraicGeometry.SheafOfModules.kaehlerDifferentialRingEquiv_D (RingEquiv.refl R)
    e.toRingEquiv e.commutes a

end Stacks.KaehlerDifferential

namespace Stacks.LineBundle

/-! ### The relative differentials of `L^⋆` as relative `1`-forms -/

/-- **`Ω_{L^⋆/S} ≅ Ω¹_{L^⋆/S}`**: the sheaf of relative differentials of the complement of the
zero section over the base is its sheaf of relative `1`-forms.

Two identifications compose to it: the two sheaves of relative differentials of a morphism of
schemes agree (`AlgebraicGeometry.Scheme.Hom.cotangentSheafIso`), and the degree-one piece of
the exterior algebra of a sheaf of modules is that sheaf itself, by its degree-one generator. -/
def Situation.cotangentFormsOneIso (D : Situation.{u}) :
    Stacks.Smooth.cotangentSheaf D.laurentToBase ≅ D.laurentForms 1 :=
  (AlgebraicGeometry.Scheme.Hom.cotangentSheafIso D.laurentToBase).symm ≪≫
    (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras D.laurentToBase).exteriorGeneratorIso

/-- **Passing from the corepresenting sheaf of differentials to the sheafified one carries the
universal differential to the universal relative derivation**, read on sections over an open of
`L^⋆`. This is the sections-level form of
`AlgebraicGeometry.Scheme.Hom.universalDerivation_postcomp_cotangentSheafIso_inv`. -/
theorem Situation.app_cotangentSheafIso_inv_universalD (D : Situation.{u})
    (W : D.laurentSpectrum.Opens) (b : Γ(D.laurentSpectrum, W)) :
    Scheme.Modules.Hom.app
        (AlgebraicGeometry.Scheme.Hom.cotangentSheafIso D.laurentToBase).inv W
        (Stacks.Smooth.universalD D.laurentToBase W b) =
      ((AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation D.laurentToBase).app
        (op W)).d b :=
  congrArg (fun d => PresheafOfModulesOfCommRing.Derivation.d d b)
    (AlgebraicGeometry.Scheme.Hom.universalDerivation_postcomp_cotangentSheafIso_inv
      D.laurentToBase)

/-- **The identification of the relative differentials of `L^⋆` with its relative `1`-forms
carries the universal differential of a local function to its de Rham differential**, the
`1`-form `Stacks.LineBundle.Situation.laurentDifferential`. This is what makes
`Stacks.LineBundle.Situation.cotangentFormsOneIso` an identification of de Rham forms. -/
theorem Situation.sections_cotangentFormsOneIso_universalD (D : Situation.{u})
    (W : D.laurentSpectrum.Opens) (b : Γ(D.laurentSpectrum, W)) :
    AlgebraicGeometry.sectionsLinearEquivOfIso D.cotangentFormsOneIso W
        (Stacks.Smooth.universalD D.laurentToBase W b) =
      D.laurentDifferential W b :=
  (congrArg
        (Scheme.Modules.Hom.app
          (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras
            D.laurentToBase).exteriorGeneratorIso.hom W)
        (D.app_cotangentSheafIso_inv_universalD W b)).trans
    (congrArg
      (fun φ => Scheme.Modules.Hom.app φ W
        (((AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation D.laurentToBase).app
          (op W)).d b))
      (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorGeneratorIso_hom
        (AlgebraicGeometry.Scheme.Hom.deRhamAlgebras D.laurentToBase)))

namespace Situation.LaurentChart

variable {D : Situation.{u}} {U : D.X.affineOpens} (ch : D.LaurentChart U.1) {V : D.S.Opens}
  (hV : IsAffineOpen V) (hUV : U.1 ≤ D.f ⁻¹ᵁ V)

/-- **The relative differentials of `L^⋆` over an affine open carrying a Laurent chart**: for
`U` an affine open of `X` carrying a chart and mapping into an affine open `V` of `S`,

`Ω[Γ(X, U)[T;T⁻¹]⁄Γ(S, V)] ≅ Γ(Ω_{L^⋆/S}, π⁻¹U)`,

linearly over `Γ(X, U)[T;T⁻¹]` acting on the sections through the comparison of the chart.

The inverse image of `U` in `L^⋆` is affine and lies over `V`, so Tag 01UT identifies the
sections of `Ω_{L^⋆/S}` over it with the Kähler differentials of its ring of functions; the
chart comparison identifies that ring with `Γ(X, U)[T;T⁻¹]` as a `Γ(S, V)`-algebra, and
`Stacks.KaehlerDifferential.algEquivCongr` transports the differentials along it. -/
def cotangentEquiv :
    letI := Stacks.Smooth.algebraAppLE D.f hUV
    letI := Stacks.Smooth.algebraAppLE D.laurentToBase
      (D.laurentPreimage_le_laurentToBase_preimage hUV)
    letI : Module (LaurentPolynomial Γ(D.X, U.1))
        Γ(Stacks.Smooth.cotangentSheaf D.laurentToBase, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
      Module.compHom _ (ch.sectionsAlgEquiv hUV).toRingEquiv.toRingHom
    Ω[LaurentPolynomial Γ(D.X, U.1)⁄Γ(D.S, V)] ≃ₗ[LaurentPolynomial Γ(D.X, U.1)]
      Γ(Stacks.Smooth.cotangentSheaf D.laurentToBase, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
  letI := Stacks.Smooth.algebraAppLE D.f hUV
  letI := Stacks.Smooth.algebraAppLE D.laurentToBase
    (D.laurentPreimage_le_laurentToBase_preimage hUV)
  letI : Module (LaurentPolynomial Γ(D.X, U.1))
      Ω[Γ(D.laurentSpectrum, D.laurentSpectrumToBase ⁻¹ᵁ U.1)⁄Γ(D.S, V)] :=
    Module.compHom _ (ch.sectionsAlgEquiv hUV).toRingEquiv.toRingHom
  letI : Module (LaurentPolynomial Γ(D.X, U.1))
      Γ(Stacks.Smooth.cotangentSheaf D.laurentToBase, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
    Module.compHom _ (ch.sectionsAlgEquiv hUV).toRingEquiv.toRingHom
  let e₁ := Stacks.KaehlerDifferential.algEquivCongr (ch.sectionsAlgEquiv hUV)
  let e₂ := Stacks.Smooth.cotangentSectionsEquiv D.laurentToBase
    (D.isAffineOpen_laurentPreimage U.2) hV
    (D.laurentPreimage_le_laurentToBase_preimage hUV)
  { (e₁.toAddEquiv.trans e₂.toAddEquiv) with
    map_smul' := fun a x =>
      (congrArg e₂ (e₁.map_smul a x)).trans
        (e₂.map_smul ((ch.sectionsAlgEquiv hUV) a) (e₁ x)) }

/-- **The identification carries the Kähler differential of a Laurent polynomial to the
universal differential of the function it names.** Since the Kähler differentials `d q` generate
the source this pins the identification down. -/
theorem cotangentEquiv_D (q : LaurentPolynomial Γ(D.X, U.1)) :
    letI := Stacks.Smooth.algebraAppLE D.f hUV
    letI := Stacks.Smooth.algebraAppLE D.laurentToBase
      (D.laurentPreimage_le_laurentToBase_preimage hUV)
    letI : Module (LaurentPolynomial Γ(D.X, U.1))
        Γ(Stacks.Smooth.cotangentSheaf D.laurentToBase, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
      Module.compHom _ (ch.sectionsAlgEquiv hUV).toRingEquiv.toRingHom
    cotangentEquiv ch hV hUV
        (_root_.KaehlerDifferential.D Γ(D.S, V) (LaurentPolynomial Γ(D.X, U.1)) q) =
      Stacks.Smooth.universalD D.laurentToBase (D.laurentSpectrumToBase ⁻¹ᵁ U.1)
        ((ch.sectionsAlgEquiv hUV) q) :=
  let := Stacks.Smooth.algebraAppLE D.f hUV
  let := Stacks.Smooth.algebraAppLE D.laurentToBase
    (D.laurentPreimage_le_laurentToBase_preimage hUV)
  (congrArg
        (Stacks.Smooth.cotangentSectionsEquiv D.laurentToBase
          (D.isAffineOpen_laurentPreimage U.2) hV
          (D.laurentPreimage_le_laurentToBase_preimage hUV))
        (Stacks.KaehlerDifferential.algEquivCongr_D (ch.sectionsAlgEquiv hUV) q)).trans
    (Stacks.Smooth.cotangentSectionsEquiv_D D.laurentToBase
      (D.isAffineOpen_laurentPreimage U.2) hV
      (D.laurentPreimage_le_laurentToBase_preimage hUV) ((ch.sectionsAlgEquiv hUV) q))

/-- **The relative `1`-forms of `L^⋆` over an affine open carrying a Laurent chart**: for `U` an
affine open of `X` carrying a chart and mapping into an affine open `V` of `S`,

`Ω[Γ(X, U)[T;T⁻¹]⁄Γ(S, V)] ≅ Γ(Ω¹_{L^⋆/S}, π⁻¹U)`,

linearly over `Γ(X, U)[T;T⁻¹]` acting on the sections through the comparison of the chart. This
is `Stacks.LineBundle.Situation.LaurentChart.cotangentEquiv` read into the relative `1`-forms,
the shape in which the de Rham complex of `L^⋆` is graded and in which the residue sequence of
Tag 0FUF is stated. -/
def formsOneEquiv :
    letI := Stacks.Smooth.algebraAppLE D.f hUV
    letI := Stacks.Smooth.algebraAppLE D.laurentToBase
      (D.laurentPreimage_le_laurentToBase_preimage hUV)
    letI : Module (LaurentPolynomial Γ(D.X, U.1))
        Γ(D.laurentForms 1, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
      Module.compHom _ (ch.sectionsAlgEquiv hUV).toRingEquiv.toRingHom
    Ω[LaurentPolynomial Γ(D.X, U.1)⁄Γ(D.S, V)] ≃ₗ[LaurentPolynomial Γ(D.X, U.1)]
      Γ(D.laurentForms 1, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
  letI := Stacks.Smooth.algebraAppLE D.f hUV
  letI := Stacks.Smooth.algebraAppLE D.laurentToBase
    (D.laurentPreimage_le_laurentToBase_preimage hUV)
  letI : Module (LaurentPolynomial Γ(D.X, U.1))
      Γ(Stacks.Smooth.cotangentSheaf D.laurentToBase, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
    Module.compHom _ (ch.sectionsAlgEquiv hUV).toRingEquiv.toRingHom
  letI : Module (LaurentPolynomial Γ(D.X, U.1))
      Γ(D.laurentForms 1, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
    Module.compHom _ (ch.sectionsAlgEquiv hUV).toRingEquiv.toRingHom
  let e := cotangentEquiv ch hV hUV
  let e' := AlgebraicGeometry.sectionsLinearEquivOfIso D.cotangentFormsOneIso
    (D.laurentSpectrumToBase ⁻¹ᵁ U.1)
  { (e.toAddEquiv.trans e'.toAddEquiv) with
    map_smul' := fun a x =>
      (congrArg e' (e.map_smul a x)).trans
        (e'.map_smul ((ch.sectionsAlgEquiv hUV) a) (e x)) }

/-- **The identification carries the Kähler differential of a Laurent polynomial to the relative
de Rham differential of the function it names**, as a `1`-form on `L^⋆`. Since the Kähler
differentials `d q` generate the source this pins the identification down, and it is what makes
`Stacks.LineBundle.Situation.LaurentChart.formsOneEquiv` an identification of de Rham forms
rather than merely of modules. -/
theorem formsOneEquiv_D (q : LaurentPolynomial Γ(D.X, U.1)) :
    letI := Stacks.Smooth.algebraAppLE D.f hUV
    letI := Stacks.Smooth.algebraAppLE D.laurentToBase
      (D.laurentPreimage_le_laurentToBase_preimage hUV)
    letI : Module (LaurentPolynomial Γ(D.X, U.1))
        Γ(D.laurentForms 1, D.laurentSpectrumToBase ⁻¹ᵁ U.1) :=
      Module.compHom _ (ch.sectionsAlgEquiv hUV).toRingEquiv.toRingHom
    formsOneEquiv ch hV hUV
        (_root_.KaehlerDifferential.D Γ(D.S, V) (LaurentPolynomial Γ(D.X, U.1)) q) =
      D.laurentDifferential (D.laurentSpectrumToBase ⁻¹ᵁ U.1) ((ch.sectionsAlgEquiv hUV) q) :=
  let := Stacks.Smooth.algebraAppLE D.f hUV
  let := Stacks.Smooth.algebraAppLE D.laurentToBase
    (D.laurentPreimage_le_laurentToBase_preimage hUV)
  (congrArg
        (AlgebraicGeometry.sectionsLinearEquivOfIso D.cotangentFormsOneIso
          (D.laurentSpectrumToBase ⁻¹ᵁ U.1))
        (cotangentEquiv_D ch hV hUV q)).trans
    (D.sections_cotangentFormsOneIso_universalD (D.laurentSpectrumToBase ⁻¹ᵁ U.1)
      ((ch.sectionsAlgEquiv hUV) q))

end Situation.LaurentChart

end Stacks.LineBundle

end
