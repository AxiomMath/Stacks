module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicBaseChangeSquares
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AffineSpecTransport

/-!
# The second paragraph of Stacks 088B across an isomorphism of the base

Let `g : Y₂ ⟶ Y` be an **isomorphism** of Noetherian schemes, let `𝒦 ⊆ 𝒪_Y` be a quasi-coherent
sheaf of ideals, let `f : X ⟶ Y` and `f₂ : X₂ ⟶ Y₂` be proper, and let `g' : X₂ ⟶ X` be an
isomorphism with `g' ≫ f = f₂ ≫ g`. This file carries the whole of the second paragraph of the
proof of [Stacks, Tag 088B] across such a square: the two comparisons `ι` and `θ` of the direct
images, the base change `β'` of `β`, **both** squares `hδ` and `hγ`, and the descent of the
resulting morphism, so that the characterization

`Stacks.Coherent.IsDirectImageCharacterized`

of the source's `α` **transports along an isomorphism of the base**.

## Why this is what was missing

`CompletionProper/C1018Assembly.lean` measures the one structural gap between the two halves of
the route to [Stacks, Tag 088C], `hDev` and [Stacks, Tag 088E]:

* `CompletionProper/AdicBaseChangeSituation.lean` and
  `CompletionProper/AdicBaseChangeSquares.lean` prove the second paragraph of Stacks 088B for a
  proper morphism `π : X' ⟶ Spec B` — over `Spec B` **itself**;
* the glueing of the first paragraph consumes, over an affine open `V` of a general base, a
  solution for `π ∣_ V : π ⁻¹ V ⟶ V`, and `V` is only *isomorphic* to `Spec Γ(X, V)`
  (`AlgebraicGeometry.IsAffineOpen.isoSpec`), so `π ∣_ V` does not instantiate `π`.

Its docstring records that nothing in the tree transports
`Stacks.Coherent.IsDirectImageCharacterized` along an isomorphism of the base, and that one of the
two sides has to travel. This file supplies that transport, in the direction the route needs: from
the situation over `Y₂` — which in the intended application is `Spec Γ(X, V)`, where
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_adicBaseChangeGamma`
proves Stacks 088B outright — to the situation over `Y`, which is the affine open `V`.

## The one new ingredient

Everything here is an instance of machinery that `CompletionProper/BaseChangeMateIdentity.lean`
and `CompletionProper/AdicBaseChangeSquares.lean` already state for an *arbitrary* commuting
square — `Stacks.Algebraization.completedComparison_comp_directImageQuotientComparison` and
`Stacks.Algebraization.directImageComparison_square_of_factorizations` — except for one thing
those applications get from Cohomology of Schemes 02KH and this one cannot:

**the invertibility of the degree-zero base-change comparison.**
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine` asks for a
square whose two bases are *literally* `Spec` of a ring, and an affine open `V` of a scheme is
not; `…isIso_pushforwardBaseChange_of_isAffineHom` asks for an affine `f`, and `π ∣_ V` is proper.
`Stacks.Algebraization.isIso_pushforwardBaseChange_of_isIso` supplies it instead from the two
horizontal morphisms being isomorphisms, with **no** flatness, quasi-coherence, affineness or
cartesianness hypothesis: the comparison is the adjoint transpose of
`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChangeUnit`, which is the unit of
`(g')^* ⊣ (g')_*` followed by three structural isomorphisms, and for `g'` an isomorphism that
unit is invertible because `AlgebraicGeometry.Scheme.Modules.pullback g'` is an equivalence
(`AlgebraicGeometry.Scheme.Modules.isEquivalence_pullback_of_isIso`); the transpose of an
isomorphism along `g^* ⊣ g_*` is then an isomorphism because for `g` an isomorphism the counit of
that adjunction is one.

## Main definitions

* `Stacks.Algebraization.isoSquarePushforwardIso` — the degree-zero base change of the square as
  an isomorphism `g^*(f_*𝓕) ≅ (f₂)_*((g')^*𝓕)`, and
  `…isoSquareProperPushforwardIso` the same read in `Coh`.
* `Stacks.Algebraization.isoSquareCompletedComparison` — **the comparison `ι`**,
  `((f₂)_*((g')^*𝓕)) ^∧ ⟶ g^*((f_*𝓕) ^∧)`, the completion of the base change followed by
  Stacks 0887 (`Stacks.Coherent.completionPullbackIso`).
* `Stacks.Algebraization.isoSquareAlgebraizationIso` — **the base change `β'` of `β`**, `β`
  pulled back along `g'` and read through `Stacks.Modules.pullbackSquareIso`, Stacks 0887 and the
  transport `…comap_comap_of_isoSquare` of the two ideal sheaves on `X₂`.

## Main results

* `Stacks.Algebraization.isIso_pushforwardBaseChange_of_isIso` and
  `…isIso_pushforwardBaseChangeUnit_of_isIso` — the new ingredient above.
* `Stacks.Algebraization.isoSquareCompletedComparison_directImageQuotientComparison` — **the
  square `hδ`**: `ι` and `θ` carry the comparison `δ` of
  `Stacks.Coherent.directImageQuotientComparison` over `Y₂` to the pullback along `g` of the one
  over `Y`.
* `Stacks.Algebraization.isoSquareDirectImageComparison_square` — **the square `hγ`**: they carry
  the `γ_n` of `Stacks.Coherent.directImageComparison` over `Y₂` built from `β'` to the pullback
  along `g` of the `γ_n` built from `β`.
* `Stacks.Algebraization.coherentAdicPullback_isEquivalence_of_isIso` and
  `…existsUnique_systemHom_of_isIso` — pullback along an isomorphism is an equivalence on
  coherent adic systems, so a morphism of the pulled-back systems descends uniquely.
* `Stacks.Algebraization.exists_isDirectImageCharacterized_of_isoSquare` — **the transport.**
  Given a morphism `α₂` over `Y₂` characterized in the source's sense for `f₂`, `(g')^*𝓕` and the
  base change `β'` of `β`, there is a morphism `α` over `Y` characterized for `f`, `𝓕` and `β`,
  whose pullback along `g` is `α₂ ≫ ι`. Nothing is assumed of `Y`, `Y₂` beyond being Noetherian:
  neither is required to be affine, let alone a spectrum.

## Implementation notes

**`θ` is a binder, and must be.** The comparison `θ_n` of the two direct images of the levels is
carried in `hδ`, in `hγ` and in the transport as a binder constrained by its factorization

`θ_n = (f₂)_*(levelIso_n)⁻¹ ≫ (base change at the level)⁻¹`   (`hθ`),

which is the discipline `CompletionProper/AdicBaseChangeSquares.lean` records as what keeps these
declarations inside the kernel's reduction budget. Here it is not a precaution but a measurement:
a `def` naming that composite elaborates, and the `rfl` identifying it with its own body is
`(kernel) deterministic timeout` — the transport `…comap_comap_of_isoSquare` of the two ideal
sheaves on `X₂` is not definitional, so unfolding such a definition against a respelling of its
body is exactly the comparison the kernel cannot make. With `θ` and `hθ` as binders the same
content is inside the budget, and `hθ` is discharged by `rfl` at the point of use, where both
sides are the one literal composite and no definition has to be unfolded.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, so the ambient category of
`CategoryTheory.Category.assoc` is named explicitly with `(obj := _)` and the composites are
assembled in term mode out of `congrArg`, as elsewhere in this subtree.

No `stacks` attribute is attached: nothing here is a statement of the source. Stacks 088B is
registered on `Stacks.Coherent.directImageComparison`,
`…isKernelCokernelAnnihilatedByPower_directImageComparison_iff` and
`…exists_isDirectImageCharacterized_isKernelCokernel_of_affineLocalSolutions`, and the part of
02KH this file uses is registered on
`Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine`.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Coherent Stacks.AlgebraicGeometry.FlatBaseChange

/-! ### The degree-zero base change of a square whose horizontal morphisms are isomorphisms -/

section IsoComparison

variable {X X₂ Y Y₂ : Scheme.{u}} {f : X ⟶ Y} {g : Y₂ ⟶ Y} {f₂ : X₂ ⟶ Y₂} {g' : X₂ ⟶ X}

/-- **The adjoint form of the degree-zero base-change comparison is an isomorphism as soon as the
upper horizontal morphism of the square is.**

`Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChangeUnit` is the direct image along `f`
of the unit of `(g')^* ⊣ (g')_*` followed by three structural isomorphisms of pushforwards, so it
is invertible as soon as that unit is — which it is for `g'` an isomorphism, pullback along an
isomorphism being an equivalence
(`AlgebraicGeometry.Scheme.Modules.isEquivalence_pullback_of_isIso`) and the unit of an adjunction
whose left adjoint is an equivalence being invertible. Neither `g` nor the square enters. -/
public theorem isIso_pushforwardBaseChangeUnit_of_isIso [IsIso g'] (w : g' ≫ f = f₂ ≫ g)
    (M : X.Modules) : IsIso (pushforwardBaseChangeUnit w M) := by
  have : IsIso (Scheme.Modules.pullbackPushforwardAdjunction g').unit := inferInstance
  unfold pushforwardBaseChangeUnit
  infer_instance

/-- **The degree-zero base-change comparison of a square whose two horizontal morphisms are
isomorphisms is an isomorphism**, for an arbitrary sheaf of modules and with no flatness,
quasi-coherence or cartesianness hypothesis. -/
public theorem isIso_pushforwardBaseChange_of_isIso [IsIso g] [IsIso g']
    (w : g' ≫ f = f₂ ≫ g) (M : X.Modules) : IsIso (pushforwardBaseChange w M) := by
  have := isIso_pushforwardBaseChangeUnit_of_isIso w M
  unfold pushforwardBaseChange
  rw [Adjunction.homEquiv_counit]
  infer_instance

end IsoComparison

/-! ### The situation of a base change along an isomorphism -/

section IsoSquare

variable {X X₂ Y Y₂ : Scheme.{u}} [IsNoetherian X] [IsNoetherian X₂] [IsNoetherian Y]
  [IsNoetherian Y₂] (f : X ⟶ Y) [IsProper f] (g : Y₂ ⟶ Y) [IsIso g] (f₂ : X₂ ⟶ Y₂)
  [IsProper f₂] (g' : X₂ ⟶ X) [IsIso g'] (w : g' ≫ f = f₂ ≫ g) (K : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

include w

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian X₂]
  [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Y₂] [IsProper f] [IsIso g]
  [IsProper f₂] [IsIso g'] in
/-- **The two routes from `𝒦 ⊆ 𝒪_Y` to an ideal sheaf on `X₂` agree.** The inverse image of
`𝒦 𝒪_{Y₂}` along `f₂` is the inverse image of `ℐ = f^{-1}𝒦 𝒪_X` along `g'`, both being the
inverse image of `𝒦` along the two equal composites of the square. -/
public theorem comap_comap_of_isoSquare :
    (K.comap g).comap f₂ = (K.comap f).comap g' := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, w]

/-- **The degree-zero base change of the square, as an isomorphism** `g^*(f_*𝓕) ≅ (f₂)_*((g')^*𝓕)`.

Unlike Cohomology of Schemes 02KH over an affine base, this needs neither flatness nor
quasi-coherence nor cartesianness: the two horizontal morphisms being isomorphisms is enough, by
`Stacks.Algebraization.isIso_pushforwardBaseChange_of_isIso`. -/
public def isoSquarePushforwardIso (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M) ≅
      (Scheme.Modules.pushforward f₂).obj ((Scheme.Modules.pullback g').obj M) :=
  haveI := isIso_pushforwardBaseChange_of_isIso w M
  asIso (pushforwardBaseChange w M)

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian X₂]
  [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Y₂] [IsProper f]
  [IsProper f₂] in
/-- The isomorphism of the degree-zero base change is the canonical comparison. -/
public theorem isoSquarePushforwardIso_hom (M : X.Modules) :
    (isoSquarePushforwardIso f g f₂ g' w M).hom = pushforwardBaseChange w M :=
  rfl

/-- **The identification of `(f₂)_*((g')^*𝓕)` with `g^*(f_*𝓕)` as coherent modules**, i.e.
`Stacks.Algebraization.isoSquarePushforwardIso` at `𝓕` itself read in `Coh(𝒪_{Y₂})`. -/
public def isoSquareProperPushforwardIso :
    properPushforwardCoherent f₂ ((pullbackCoherentModules g').obj F) ≅
      (pullbackCoherentModules g).obj (properPushforwardCoherent f F) :=
  ObjectProperty.isoMk _ (isoSquarePushforwardIso f g f₂ g' w F.obj).symm

/-- **The comparison `ι` of the two completed direct images, at a base change along an
isomorphism**:

`((f₂)_*((g')^*𝓕)) ^∧ ⟶ g^*((f_*𝓕) ^∧)`.

It is assembled from two isomorphisms, exactly as
`Stacks.Algebraization.adicBaseChangeCompletedComparison` is: the identification
`Stacks.Algebraization.isoSquareProperPushforwardIso` of the two direct images, completed along
`𝒦 𝒪_{Y₂}`, and the identification `(g^*𝒜) ^∧ ≅ g^*(𝒜 ^∧)` of completion with pullback
(`Stacks.Coherent.completionPullbackIso`, [Stacks, Tag 0887]). In particular it is itself an
isomorphism, which is what the annihilation half of Stacks 088B asks of `ι`. -/
public def isoSquareCompletedComparison :
    ((completionFunctor Y₂ (K.comap g)).obj
        (properPushforwardCoherent f₂ ((pullbackCoherentModules g').obj F))).obj ⟶
      ((coherentAdicPullback g K).obj
        ((completionFunctor Y K).obj (properPushforwardCoherent f F))).obj :=
  (((completionFunctor Y₂ (K.comap g)).map
      (isoSquareProperPushforwardIso f g f₂ g' w F).hom) ≫
    (completionPullbackIso g K (properPushforwardCoherent f F)).hom).hom

omit [AlgebraicGeometry.IsNoetherian X] in
/-- **The normalization of the comparison `ι` of the two completed direct images.** Composing the
`n`-th component of `ι` with the projection of `(f₂)_*((g')^*𝓕)` onto the `n`-th term of its
completion gives the inverse of the degree-zero base change followed by the pullback along `g` of
the projection of `f_*𝓕` onto the `n`-th term of *its* completion.

The projection is an epimorphism (`Stacks.Algebraization.epi_completionProjection`), so this
determines `ι`. It is the two normalizations `ι` is assembled from:
`Stacks.Algebraization.completionFunctor_map_quotient` and
`Stacks.Coherent.completionProjection_completionPullbackComparison`. -/
public theorem completionProjection_isoSquareCompletedComparison (n : ℕ) :
    completionProjection Y₂ (K.comap g)
          (properPushforwardCoherent f₂ ((pullbackCoherentModules g').obj F)) n ≫
        (isoSquareCompletedComparison f g f₂ g' w K F).app (op n) =
      (isoSquarePushforwardIso f g f₂ g' w F.obj).inv ≫
        (Scheme.Modules.pullback g).map
          (completionProjection Y K (properPushforwardCoherent f F) n) := by
  have h1 := completionFunctor_map_quotient Y₂ (K.comap g)
    (isoSquareProperPushforwardIso f g f₂ g' w F).hom n
  have h2 := completionProjection_completionPullbackComparison g K
    (properPushforwardCoherent f F) (op n)
  refine Eq.trans ?_ (congrArg
    (fun k => (isoSquareProperPushforwardIso f g f₂ g' w F).hom.hom ≫ k) h2)
  refine Eq.trans ?_ (Category.assoc (obj := Y₂.Modules) _ _ _)
  refine Eq.trans ?_ (congrArg (fun k => k ≫
    (completionPullbackComparison g K (properPushforwardCoherent f F)).hom.app (op n)) h1)
  exact (Category.assoc (obj := Y₂.Modules) _ _ _).symm

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
  [AlgebraicGeometry.IsNoetherian Y₂] [IsProper f] [IsIso g] [IsProper f₂] [IsIso g'] in
/-- **The normalization of the identification of the levels.** The quotient projection of
`(g')^*𝓕` followed by the inverse of the identification of the levels is the pullback along `g'`
of the quotient projection of `𝓕`; this is
`Stacks.Algebraization.π_comp_pullbackIdealPowerQuotientIsoOfEq_inv` at `g'`. -/
public theorem π_comp_isoSquareIdealPowerQuotientIso_inv (n : ℕ) :
    cokernel.π (C := X₂.Modules)
          (idealPowerMultiple ((K.comap g).comap f₂) (n + 1)
            ((pullbackCoherentModules g').obj F).obj).ι ≫
        (pullbackIdealPowerQuotientIsoOfEq g' (K.comap f)
          (comap_comap_of_isoSquare f g f₂ g' w K).symm (n + 1) F.obj).inv =
      (Scheme.Modules.pullback g').map
        (cokernel.π (C := X.Modules) (idealPowerMultiple (K.comap f) (n + 1) F.obj).ι) :=
  π_comp_pullbackIdealPowerQuotientIsoOfEq_inv g' (K.comap f)
    (comap_comap_of_isoSquare f g f₂ g' w K).symm (n + 1) F.obj

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian X₂]
  [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.IsNoetherian Y₂] [IsProper f]
  [IsProper f₂] in
/-- **The degree-zero base change along an isomorphism is natural in the module, on the
inverses.** For `t : 𝓕 ⟶ 𝓔`, the inverse of the base change at `𝓕` followed by the pullback along
`g` of the direct image of `t` is the direct image along `f₂` of the pullback along `g'` of `t`,
followed by the inverse of the base change at `𝓔`.

This is `Stacks.AlgebraicGeometry.FlatBaseChange.pushforwardBaseChange_naturality` read on the
inverses. At the quotient projection of `𝓕` it is the agreement of the two morphisms computed for
the two sides of `hδ`. -/
public theorem isoSquarePushforwardIso_inv_naturality {E : X.Modules} (t : F.obj ⟶ E) :
    (isoSquarePushforwardIso f g f₂ g' w F.obj).inv ≫
        (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map t) =
      (Scheme.Modules.pushforward f₂).map ((Scheme.Modules.pullback g').map t) ≫
        (isoSquarePushforwardIso f g f₂ g' w E).inv :=
  have hnat : (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map t) ≫
        (isoSquarePushforwardIso f g f₂ g' w E).hom =
      (isoSquarePushforwardIso f g f₂ g' w F.obj).hom ≫
        (Scheme.Modules.pushforward f₂).map ((Scheme.Modules.pullback g').map t) :=
    pushforwardBaseChange_naturality w t
  (Iso.inv_comp_eq _).2
    (((Iso.eq_comp_inv _).2 hnat).trans (Category.assoc (obj := Y₂.Modules) _ _ _))

/-- **The square `hδ`, at a base change along an isomorphism.** The comparisons `ι` and `θ`
carry the comparison `δ` of `Stacks.Coherent.directImageQuotientComparison` over `Y₂` to the
pullback along `g` of the one over `Y`.

This is `Stacks.Algebraization.completedComparison_comp_directImageQuotientComparison` — which is
stated for an arbitrary commuting square and arbitrary `ι`, `θ` — at the normalization
`…completionProjection_isoSquareCompletedComparison` of `ι`, the factorization `hθ` of `θ`, the
normalization `…π_comp_isoSquareIdealPowerQuotientIso_inv` of the identification of the levels,
and the naturality `…isoSquarePushforwardIso_inv_naturality` of the degree-zero base change at
the quotient projection of `𝓕`.

`θ` is a binder constrained by its factorization `hθ`; see the implementation notes for why it
cannot be a definition here. -/
public theorem isoSquareCompletedComparison_directImageQuotientComparison (n : ℕ)
    {θ : (Scheme.Modules.pushforward f₂).obj
        (idealPowerQuotient ((K.comap g).comap f₂) (n + 1)
          ((pullbackCoherentModules g').obj F).obj) ⟶
      (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj
          (idealPowerQuotient (K.comap f) (n + 1) F.obj))}
    (hθ : θ = (Scheme.Modules.pushforward f₂).map
          (pullbackIdealPowerQuotientIsoOfEq g' (K.comap f)
            (comap_comap_of_isoSquare f g f₂ g' w K).symm (n + 1) F.obj).inv ≫
        (isoSquarePushforwardIso f g f₂ g' w
          (idealPowerQuotient (K.comap f) (n + 1) F.obj)).inv)
    :
    (isoSquareCompletedComparison f g f₂ g' w K F).app (op n) ≫
          (Scheme.Modules.pullback g).map
            (eqToHom (completionFunctor_obj Y K (properPushforwardCoherent f F) n) ≫
              directImageQuotientComparison f K (n + 1) F.obj) =
        (eqToHom (completionFunctor_obj Y₂ (K.comap g)
              (properPushforwardCoherent f₂ ((pullbackCoherentModules g').obj F)) n) ≫
            directImageQuotientComparison f₂ (K.comap g) (n + 1)
              ((pullbackCoherentModules g').obj F).obj) ≫ θ :=
  completedComparison_comp_directImageQuotientComparison f g f₂ K F
    ((pullbackCoherentModules g').obj F) n
    (completionProjection_isoSquareCompletedComparison f g f₂ g' w K F n) hθ
    (π_comp_isoSquareIdealPowerQuotientIso_inv f g f₂ g' w K F n)
    (isoSquarePushforwardIso_inv_naturality f g f₂ g' w F
      (cokernel.π (C := X.Modules) (idealPowerMultiple (K.comap f) (n + 1) F.obj).ι))

/-! ### The base change of `β` along an isomorphism, and the square `hγ` -/

variable (G : CoherentAdicSystems K)
  (β : (coherentAdicPullback f K).obj G ≅ (completionFunctor X (K.comap f)).obj F)

/-- **The base change of `β` along the isomorphism.** Given `β : f^*(𝒢_n) ≅ 𝓕 ^∧` over `Y`, the
corresponding isomorphism

`(f₂)^*(g^*(𝒢_n)) ≅ ((g')^*𝓕) ^∧`

over `Y₂`. It is `β` pulled back along `g'` and read through three identifications, exactly as
`Stacks.Algebraization.adicBaseChangeAlgebraizationIso` is: the composition isomorphism
`(f₂)^*g^* ≅ (g')^*f^*` of `Stacks.Modules.pullbackSquareIso` whiskered with the diagram of
`(𝒢_n)`, then `Stacks.Coherent.completionPullbackIso` at `g'` ([Stacks, Tag 0887]), then
`Stacks.Algebraization.completionFunctorObjCongr` at the transport
`…comap_comap_of_isoSquare` of the two ideal sheaves on `X₂`.

`β'` has to be constructed from `β` and cannot be a binder: the square `hγ` below is false for a
`β'` unrelated to `β`. -/
public def isoSquareAlgebraizationIso :
    (coherentAdicPullback f₂ (K.comap g)).obj ((coherentAdicPullback g K).obj G) ≅
      (completionFunctor X₂ ((K.comap g).comap f₂)).obj
        ((pullbackCoherentModules g').obj F) :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft G.obj (Stacks.Modules.pullbackSquareIso f f₂ g g' w) ≪≫
      Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso β) (Scheme.Modules.pullback g') ≪≫
        (ObjectProperty.ι _).mapIso (completionPullbackIso g' (K.comap f) F).symm ≪≫
          completionFunctorObjCongr (comap_comap_of_isoSquare f g f₂ g' w K).symm
            ((pullbackCoherentModules g').obj F))

omit [IsProper f] [IsIso g] [IsProper f₂] [IsIso g'] in
/-- **The components of the base change of `β`, as an equality of natural transformations.**
`rfl`, stated separately because in a functor category the level `n` of a composite of natural
isomorphisms is not reachable by `CategoryTheory.NatTrans.comp_app` with its arguments left to
unification; the equality of the transformations has to be named first. -/
public theorem isoSquareAlgebraizationIso_hom_hom :
    (isoSquareAlgebraizationIso f g f₂ g' w K F G β).hom.hom =
      (Functor.isoWhiskerLeft G.obj (Stacks.Modules.pullbackSquareIso f f₂ g g' w) ≪≫
          Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso β)
            (Scheme.Modules.pullback g') ≪≫
            (ObjectProperty.ι _).mapIso (completionPullbackIso g' (K.comap f) F).symm ≪≫
              completionFunctorObjCongr (comap_comap_of_isoSquare f g f₂ g' w K).symm
                ((pullbackCoherentModules g').obj F)).hom :=
  rfl

omit [IsProper f] [IsIso g] [IsProper f₂] [IsIso g'] in
/-- **The components of the base change of `β`, read at the level `n`.** This is
`Stacks.Algebraization.isoSquareAlgebraizationIso_hom_hom` at `op n`, and it is the factorization
of `β'_n` that the unit half of `hγ` consumes. -/
public theorem isoSquareAlgebraizationIso_hom_hom_app (n : ℕ) :
    (isoSquareAlgebraizationIso f g f₂ g' w K F G β).hom.hom.app (op n) =
      (Functor.isoWhiskerLeft G.obj
          (Stacks.Modules.pullbackSquareIso f f₂ g g' w)).hom.app (op n) ≫
        (Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso β)
              (Scheme.Modules.pullback g') ≪≫
            (ObjectProperty.ι _).mapIso (completionPullbackIso g' (K.comap f) F).symm ≪≫
              completionFunctorObjCongr (comap_comap_of_isoSquare f g f₂ g' w K).symm
                ((pullbackCoherentModules g').obj F)).hom.app (op n) :=
  congr_app (isoSquareAlgebraizationIso_hom_hom f g f₂ g' w K F G β) (op n)

omit [AlgebraicGeometry.IsNoetherian Y₂] [IsProper f] [IsIso g] [IsProper f₂] [IsIso g'] in
/-- **The tail of the base change of `β` at level `n`.** The last three factors of `β'` split
off the pullback along `g'` of `β_n`; `rfl`. -/
public theorem isoSquareAlgebraizationIso_tail_app (n : ℕ) :
    (Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso β)
            (Scheme.Modules.pullback g') ≪≫
          (ObjectProperty.ι _).mapIso (completionPullbackIso g' (K.comap f) F).symm ≪≫
            completionFunctorObjCongr (comap_comap_of_isoSquare f g f₂ g' w K).symm
              ((pullbackCoherentModules g').obj F)).hom.app (op n) =
      (Scheme.Modules.pullback g').map (β.hom.hom.app (op n)) ≫
        ((ObjectProperty.ι _).mapIso (completionPullbackIso g' (K.comap f) F).symm ≪≫
            completionFunctorObjCongr (comap_comap_of_isoSquare f g f₂ g' w K).symm
              ((pullbackCoherentModules g').obj F)).hom.app (op n) :=
  rfl

omit [IsProper f] [IsProper f₂] in
/-- **The square `hγ`, at a base change along an isomorphism.** The comparisons `ι` and the
binder `θ` of `hθ`
carry the map `γ_n` of `Stacks.Coherent.directImageComparison` over `Y₂`, built from the base
change `Stacks.Algebraization.isoSquareAlgebraizationIso` of `β`, to the pullback along `g` of
the `γ_n` built from `β`.

Both `γ`'s are the unit of the adjunction followed by a direct image of a component of `β`, resp.
of `β'` (`Stacks.Coherent.directImageComparison_app`), so this is
`Stacks.Algebraization.directImageComparison_square_of_factorizations` — stated for an arbitrary
commuting square — read through that description on each side. Its eight hypotheses are: the mate
identity `Stacks.Algebraization.unit_comp_pushforwardBaseChange`, the two factorizations
`…isoSquareAlgebraizationIso_hom_hom_app` and `…isoSquareAlgebraizationIso_tail_app` of `β'_n`,
the level identification `…completionPullbackIso_inv_app_comp` at `g'`, the two readings of the
transports of the terms of the two completions as direct images (`CategoryTheory.eqToHom_map`),
the factorization `hθ` of `θ`, and the invertibility of the degree-zero base change at the level.

Unlike the corresponding square at the base change along `Spec B ^∧ ⟶ Spec B`, this is one
declaration and not ten: the schemes here are variables, so the kernel never has to reduce the
category structure of a concrete fibre product. -/
public theorem isoSquareDirectImageComparison_square (n : ℕ)
    {θ : (Scheme.Modules.pushforward f₂).obj
        (idealPowerQuotient ((K.comap g).comap f₂) (n + 1)
          ((pullbackCoherentModules g').obj F).obj) ⟶
      (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj
          (idealPowerQuotient (K.comap f) (n + 1) F.obj))}
    (hθ : θ = (Scheme.Modules.pushforward f₂).map
          (pullbackIdealPowerQuotientIsoOfEq g' (K.comap f)
            (comap_comap_of_isoSquare f g f₂ g' w K).symm (n + 1) F.obj).inv ≫
        (isoSquarePushforwardIso f g f₂ g' w
          (idealPowerQuotient (K.comap f) (n + 1) F.obj)).inv)
    :
    (directImageComparison f₂ (K.comap g) ((coherentAdicPullback g K).obj G)
            ((pullbackCoherentModules g').obj F)
            (isoSquareAlgebraizationIso f g f₂ g' w K F G β)).app (op n) ≫
        eqToHom (pushforward_completion_obj f₂ (K.comap g)
          ((pullbackCoherentModules g').obj F) n) ≫ θ =
      (Scheme.Modules.pullback g).map
        ((directImageComparison f K G F β).app (op n) ≫
          eqToHom (pushforward_completion_obj f K F n)) := by
  have : F.obj.IsCoherent := F.property
  have : F.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : (idealPowerQuotient (K.comap f) (n + 1) F.obj).IsCoherent :=
    (coherentAnnihilatedBy_idealPowerQuotient (K.comap f) n F.obj F.property).1
  have : (idealPowerQuotient (K.comap f) (n + 1) F.obj).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  refine Eq.trans (congrArg (fun k => k ≫
      (eqToHom (pushforward_completion_obj f₂ (K.comap g)
          ((pullbackCoherentModules g').obj F) n) ≫ θ))
    (directImageComparison_app f₂ (K.comap g) ((coherentAdicPullback g K).obj G)
      ((pullbackCoherentModules g').obj F)
      (isoSquareAlgebraizationIso f g f₂ g' w K F G β) (op n))) ?_
  refine Eq.trans ?_ (congrArg (Scheme.Modules.pullback g).map
    (congrArg (fun k => k ≫ eqToHom (pushforward_completion_obj f K F n))
      (directImageComparison_app f K G F β (op n)).symm))
  exact directImageComparison_square_of_factorizations f f₂ g g' w (G.obj.obj (op n))
    (unit_comp_pushforwardBaseChange f f₂ g g' w (G.obj.obj (op n)))
    (isoSquareAlgebraizationIso_hom_hom_app f g f₂ g' w K F G β n)
    (isoSquareAlgebraizationIso_tail_app f g f₂ g' w K F G β n)
    (completionPullbackIso_inv_app_comp g' (K.comap f)
      (comap_comap_of_isoSquare f g f₂ g' w K).symm F n)
    (eqToHom_map (Scheme.Modules.pushforward f)
      (completionFunctor_obj X (K.comap f) F n)).symm
    (eqToHom_map (Scheme.Modules.pushforward f₂)
      (completionFunctor_obj X₂ ((K.comap g).comap f₂)
        ((pullbackCoherentModules g').obj F) n)).symm hθ
    (Iso.hom_inv_id (isoSquarePushforwardIso f g f₂ g' w
      (idealPowerQuotient (K.comap f) (n + 1) F.obj)))

end IsoSquare

/-! ### Descent along an isomorphism of the base -/

section IsoDescent

open Stacks.Coherent

variable {Y Y₂ : Scheme.{u}} [IsNoetherian Y] [IsNoetherian Y₂] (g : Y₂ ⟶ Y) [IsIso g]
  (K : Y.IdealSheafData)

/-- **Pullback along an isomorphism is an equivalence on coherent adic systems.** [Stacks, Tag
0EHQ] at a morphism which is trivially flat and trivially an isomorphism over `V(𝒦)`. -/
public theorem coherentAdicPullback_isEquivalence_of_isIso :
    (coherentAdicPullback g K).IsEquivalence :=
  coherentAdicPullback_isEquivalence _ _

/-- **A morphism of coherent adic systems descends along an isomorphism of the base, uniquely.**
Every morphism of the pullbacks along `g` of two objects of `Coh(Y, 𝒦)` is the pullback of a
unique morphism between them. -/
public theorem existsUnique_systemHom_of_isIso (G H : CoherentAdicSystems K)
    (b : (coherentAdicPullback g K).obj G ⟶ (coherentAdicPullback g K).obj H) :
    ∃! a : G.obj ⟶ H.obj, ∀ n : ℕᵒᵖ,
      (Scheme.Modules.pullback g).map (a.app n) = b.hom.app n := by
  have := coherentAdicPullback_isEquivalence_of_isIso g K
  obtain ⟨a₀, ha₀⟩ := (coherentAdicPullback g K).map_surjective b
  subst ha₀
  refine ⟨a₀.hom, fun _ => rfl, fun y hy => ?_⟩
  have h1 : (coherentAdicPullback g K).map (ObjectProperty.homMk y) =
      (coherentAdicPullback g K).map a₀ :=
    ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => hy n))
  exact congrArg (fun z : G ⟶ H => z.hom)
    ((coherentAdicPullback g K).map_injective h1)

end IsoDescent

/-! ### The transport of the characterization of Stacks 088B along an isomorphism of the base -/

section Transport

variable {X X₂ Y Y₂ : Scheme.{u}} [IsNoetherian X] [IsNoetherian X₂] [IsNoetherian Y]
  [IsNoetherian Y₂] (f : X ⟶ Y) [IsProper f] (g : Y₂ ⟶ Y) [IsIso g] (f₂ : X₂ ⟶ Y₂)
  [IsProper f₂] (g' : X₂ ⟶ X) [IsIso g'] (w : g' ≫ f = f₂ ≫ g) (K : Y.IdealSheafData)
  (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
  (G : CoherentAdicSystems K)
  (β : (coherentAdicPullback f K).obj G ≅ (completionFunctor X (K.comap f)).obj F)

include w

/-- **The transport of `Stacks.Coherent.IsDirectImageCharacterized` along an isomorphism of the
base.** Let `g : Y₂ ⟶ Y` be an isomorphism of Noetherian schemes, `𝒦 ⊆ 𝒪_Y` quasi-coherent,
`f : X ⟶ Y` and `f₂ : X₂ ⟶ Y₂` proper, `g' : X₂ ⟶ X` an isomorphism with `g' ≫ f = f₂ ≫ g`, `𝓕` a
coherent `𝒪_X`-module, `(𝒢_n)` an object of `Coh(Y, 𝒦)` and `β : f^*(𝒢_n) ≅ 𝓕 ^∧`. A morphism

`α₂ : g^*(𝒢_n) ⟶ ((f₂)_*((g')^*𝓕)) ^∧`

characterized in the source's sense for `f₂`, `(g')^*𝓕` and the base change `β'` of `β`
(`Stacks.Algebraization.isoSquareAlgebraizationIso`) yields a morphism

`α : (𝒢_n) ⟶ ((f_*𝓕) ^∧)`

characterized in the source's sense for `f`, `𝓕` and `β` — and the second clause pins `α` down:
its pullback along `g` is `α₂ ≫ ι`.

**This is the transport whose absence `CompletionProper/C1018Assembly.lean` records as the one
structural gap of the 088E route.** The two squares `hδ` and `hγ` move the characterizing equation
across `ι` and `θ`, after which the equation holds after pullback along `g`; pullback along an
isomorphism is faithful, so the equation holds on the nose, and the descent of `α₂ ≫ ι` itself is
`Stacks.Algebraization.existsUnique_systemHom_of_isIso`.

Nothing is assumed of `Y` or `Y₂` beyond being Noetherian — neither has to be affine, let alone a
spectrum — which is exactly what the affine open `V` of a general base needs. -/
public theorem exists_isDirectImageCharacterized_of_isoSquare
    {θ : ∀ n : ℕ, (Scheme.Modules.pushforward f₂).obj
        (idealPowerQuotient ((K.comap g).comap f₂) (n + 1)
          ((pullbackCoherentModules g').obj F).obj) ⟶
      (Scheme.Modules.pullback g).obj
        ((Scheme.Modules.pushforward f).obj
          (idealPowerQuotient (K.comap f) (n + 1) F.obj))}
    (hθ : ∀ n : ℕ, θ n = (Scheme.Modules.pushforward f₂).map
          (pullbackIdealPowerQuotientIsoOfEq g' (K.comap f)
            (comap_comap_of_isoSquare f g f₂ g' w K).symm (n + 1) F.obj).inv ≫
        (isoSquarePushforwardIso f g f₂ g' w
          (idealPowerQuotient (K.comap f) (n + 1) F.obj)).inv)
    (α₂ : ((coherentAdicPullback g K).obj G).obj ⟶
      ((completionFunctor Y₂ (K.comap g)).obj
        (properPushforwardCoherent f₂ ((pullbackCoherentModules g').obj F))).obj)
    (hα₂ : IsDirectImageCharacterized f₂ (K.comap g) ((coherentAdicPullback g K).obj G)
      ((pullbackCoherentModules g').obj F)
      (isoSquareAlgebraizationIso f g f₂ g' w K F G β) α₂) :
    ∃ α : G.obj ⟶ ((completionFunctor Y K).obj (properPushforwardCoherent f F)).obj,
      IsDirectImageCharacterized f K G F β α ∧
        ∀ n : ℕᵒᵖ, (Scheme.Modules.pullback g).map (α.app n) =
          (α₂ ≫ isoSquareCompletedComparison f g f₂ g' w K F).app n := by
  have := coherentAdicPullback_isEquivalence_of_isIso g K
  have hψ : ∀ n : ℕ,
      (α₂ ≫ isoSquareCompletedComparison f g f₂ g' w K F).app (op n) ≫
          (Scheme.Modules.pullback g).map
            (eqToHom (completionFunctor_obj Y K (properPushforwardCoherent f F) n) ≫
              directImageQuotientComparison f K (n + 1) F.obj) =
        (Scheme.Modules.pullback g).map
          ((directImageComparison f K G F β).app (op n) ≫
            eqToHom (pushforward_completion_obj f K F n)) := by
    intro n
    rw [NatTrans.comp_app]
    exact (Category.assoc (obj := Y₂.Modules) _ _ _).trans
      ((congrArg (fun z => α₂.app (op n) ≫ z)
          (isoSquareCompletedComparison_directImageQuotientComparison f g f₂ g' w K F n
            (hθ n))).trans
        ((Category.assoc (obj := Y₂.Modules) _ _ _).symm.trans
          ((congrArg (fun z => z ≫ θ n) (hα₂ n)).trans
            ((Category.assoc (obj := Y₂.Modules) _ _ _).trans
              (isoSquareDirectImageComparison_square f g f₂ g' w K F G β n (hθ n))))))
  obtain ⟨α, hα, -⟩ := existsUnique_systemHom_of_isIso g K G
    ((completionFunctor Y K).obj (properPushforwardCoherent f F))
    (ObjectProperty.homMk (α₂ ≫ isoSquareCompletedComparison f g f₂ g' w K F))
  refine ⟨α, fun n => ?_, hα⟩
  refine (Scheme.Modules.pullback g).map_injective ?_
  rw [Functor.map_comp, hα (op n)]
  exact hψ n

end Transport

end Stacks.Algebraization

end
