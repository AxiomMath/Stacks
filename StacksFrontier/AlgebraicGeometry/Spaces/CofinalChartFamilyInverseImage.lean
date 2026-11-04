module

public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartFamilySurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.JointlyLocallyInhabitedSurjective

/-!
# The inverse images of the charts of a cover are jointly surjective onto the final sheaf

Let `X` and `Y` be algebraic spaces over a scheme `S` in a big fppf site, let
`g : Sh(X_étale) ⟶ Sh(Y_étale)` be a morphism of topoi — for instance the one underlying a
morphism `ψ` of their small étale ringed topoi — and let `V i` be étale charts of `Y` covering
the final object of the small étale site of `Y`.  Writing `h_{V i}` for the sheaf on `Y_étale`
represented by `V i`, this file proves

* `∐ᵢ g⁻¹h_{V i} ⟶ *` is a surjection of sheaves on `X_étale`
  (`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf`),
  and
* the charts of `X` over which some `g⁻¹h_{V i}` has a section are cofinal among the affine
  étale charts of `X`
  (`AlgebraicGeometry.Space.isCofinalChartFamily_inverseImage_smallEtaleChartSheaf`),

which is the hypothesis `AlgebraicGeometry.Space.IsCofinalChartFamily` of the two gluing
statements of `StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartGluing.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/CofinalChartTwoIsoGluing.lean`.  Both are recorded here
with that hypothesis discharged, so that step 5 and step 6 of the proof of
[Stacks Project, Tag 04KL] need only a covering family of étale charts of `Y`.

That is item (d) of what Stacks 04KL owes: "a chart and a section from the surjectivity of
`∐ᵢ g⁻¹h_{V i} ⟶ *`".

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleChartSheaf` — the sheaf on the small étale site of an
  algebraic space represented by an étale chart, `h_V`.  It is a sheaf because that topology is
  subcanonical (`AlgebraicGeometry.Space.smallEtaleTopology_subcanonical`).

## Main results

* `AlgebraicGeometry.Space.jointlyLocallyInhabited_smallEtaleChartSheaf` — the representable
  sheaves of a covering family of étale charts are jointly locally inhabited.
* `AlgebraicGeometry.Space.jointlyLocallyInhabited_inverseImage_smallEtaleChartSheaf` — so are
  their inverse images under a morphism of topoi.
* `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf` —
  **the surjectivity `∐ᵢ g⁻¹h_{V i} ⟶ *`**, for any family of morphisms into any terminal sheaf;
  `…_finalSheaf_…` is the same with the final sheaf spelled out as the constant sheaf `PUnit`,
  and `…_ringedToposHom` reads it off a morphism of small étale ringed topoi.
* `AlgebraicGeometry.Space.isCofinalChartFamily_inverseImage_smallEtaleChartSheaf` — the
  cofinality, **with no coproduct**, and `…_ringedToposHom` for a morphism of ringed topoi.
* `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_coversTop` and
  `AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_coversTop` — the two gluing
  statements with their cofinality hypothesis discharged.
* `AlgebraicGeometry.Space.SmallEtale.exists_coversTop_punit` — every algebraic space has a
  single étale chart covering the final object of its small étale site, at index universe `u`.
  With `AlgebraicGeometry.Space.hasSomeChartSection_id_smallEtaleChartSheaf` this is what shows
  the statements above are not vacuous.

## Implementation notes

### Which form a consumer should use, and the universe constraint that decides it

`AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc` takes
`[HasCoproduct G]`, and for `Type u`-valued sheaves that is a constraint on the index universe,
not a formality: on the small étale site of an algebraic space, whose objects are a
`Type (u + 1)` and whose sheaves are of `Type u`, `HasColimitsOfShape (Discrete I) (Type u)`
holds for `I : Type u` and **fails** for `I : Type (u + 1)`.  So a cover indexed by the affine
étale charts themselves — as
`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts` produces it — has no coproduct of
inverse images at all.

The cofinality statements here therefore go through
`AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection`, whose hypothesis is a
covering sieve rather than a surjection, and whose index type is unconstrained; the coproduct
form is recorded beside them for the consumer that wants it and has a small enough index type.
The passage between the two is
`Stacks.Topos.isLocallySurjective_sigmaDesc_iff_of_isTerminal`: the two conditions are
equivalent whenever the coproduct exists.

Of the two coproduct consumers, the one targeted is
`AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc` rather than
`…_of_isLocallySurjective_finalSheaf`, because the surjectivity proved here holds for *any*
family of morphisms into *any* terminal sheaf — terminality is the only property of the target
used — so the general form costs a caller nothing and subsumes the final-sheaf spelling through
`CategoryTheory.Sheaf.isTerminalTerminal`.  The final-sheaf form is given as a corollary all the
same.

### Why no colimit and no sheafification appear in the transport

The step that moves the covering from `Y_étale` to `X_étale` is
`Stacks.Topos.jointlyLocallyInhabited_inverseImage`, which forms no colimit indexed by the
family: it transports the *subsheaf of the terminal sheaf* cut out by the covering condition
along the adjunction `g⁻¹ ⊣ g_*`.  The route through "a left adjoint preserves the coproduct and
the epimorphism" would need the coproduct to exist on both sides, which is exactly what the
universe constraint above denies in general.

### The morphism of topoi is arbitrary

Nothing below uses the structure sheaves, so the statements are made for an arbitrary
`MorphismOfTopoi` between the two topoi of sheaves of sets, with the forms for a
`AlgebraicGeometry.RingedToposHom` as corollaries through its `toToposHom` field.  That is also
what makes the non-vacuity witness cheap: for the identity morphism of topoi the inverse image
is the identity functor, so the chart `V i` itself carries a section of `h_{V i}`.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The sheaf represented by an étale chart -/

/-- **The sheaf `h_V` on the small étale site of an algebraic space `X` represented by an étale
chart `V`.**  The presheaf `CategoryTheory.yoneda.obj V` is a sheaf because the small étale
topology of an algebraic space is subcanonical,
`AlgebraicGeometry.Space.smallEtaleTopology_subcanonical`.

The subcanonicality is used only inside this definition, so no statement about `h_V` has to
carry it as an instance argument. -/
noncomputable def smallEtaleChartSheaf (X : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS X.1) : Sheaf (SmallEtale.topology B S hS X.1) (Type u) :=
  letI := smallEtaleTopology_subcanonical B S hS X
  (SmallEtale.topology B S hS X.1).yoneda.obj V

/-- The underlying presheaf of `AlgebraicGeometry.Space.smallEtaleChartSheaf` is the represented
presheaf, so its sections over an étale chart `W` are the morphisms `W ⟶ V` of the small étale
site. -/
theorem smallEtaleChartSheaf_obj (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1) :
    (smallEtaleChartSheaf B S hS X V).obj = yoneda.obj V :=
  rfl

/-! ### Coproducts of `Type u`-valued sheaves on the small étale site

Instance search for a coproduct in this sheaf category does not terminate inside the heartbeat
budget: `CategoryTheory.hasColimitsEssentiallySmallSite` fires on every colimit goal in a sheaf
category and the small étale site is essentially small, so the search walks into the model.  The
answer is recorded once here, for the index universe at which it exists.  The precedent is
`CategoryTheory.Sheaf.hasColimit_discrete_sheafifiedYoneda` of
`StacksFrontier/CategoryTheory/Sites/QuasiCompact/CoveringSetFromCoversTop.lean`. -/

/-- **Coproducts of `Type u`-valued sheaves on the small étale site, over an index type in
`Type u`.**  The colimit is the sheafification of the colimit of presheaves, which exists
because the site admits sheafification with `Type u` coefficients
(`AlgebraicGeometry.Space.SmallEtale.instHasSheafify`).

The index universe cannot be raised: `HasColimitsOfShape (Discrete I) (Type u)` fails for
`I : Type (u + 1)`, so there is no coproduct of a family of `Type u`-valued sheaves indexed by
the objects of the site themselves. -/
noncomputable instance hasColimitsOfShape_discrete_smallEtale
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) {I : Type u} :
    HasColimitsOfShape (Discrete I) (Sheaf (SmallEtale.topology B S hS F) (Type u)) :=
  ⟨fun _ => HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
    Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

/-! ### A covering family of étale charts, and what it gives on the source -/

variable {X Y : AlgebraicSpaces B S hS} {I : Type w'}

/-- **The representable sheaves of a covering family of étale charts are jointly locally
inhabited**: every étale chart of `Y` is covered by charts admitting a morphism to one of the
`V i`.  The two conditions are the same sieves being covering; see
`Stacks.Topos.jointlyLocallyInhabited_yoneda_iff_coversTop`. -/
theorem jointlyLocallyInhabited_smallEtaleChartSheaf (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V) :
    Stacks.Topos.JointlyLocallyInhabited (SmallEtale.topology B S hS Y.1)
      fun i => smallEtaleChartSheaf B S hS Y (V i) :=
  hV

/-- **The inverse images `g⁻¹h_{V i}` of a covering family of étale charts of `Y` are jointly
locally inhabited on the small étale site of `X`**: every étale chart of `X` is covered by
charts over which some `g⁻¹h_{V i}` has a section.

This is `Stacks.Topos.jointlyLocallyInhabited_inverseImage` — the transport of joint local
inhabitedness along a morphism of topoi, which forms no coproduct over the index type — applied
to `AlgebraicGeometry.Space.jointlyLocallyInhabited_smallEtaleChartSheaf`. -/
theorem jointlyLocallyInhabited_inverseImage_smallEtaleChartSheaf
    (g : MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS X.1) (Type u))
      (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))
    (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V) :
    Stacks.Topos.JointlyLocallyInhabited (SmallEtale.topology B S hS X.1)
      fun i => g.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i)) :=
  Stacks.Topos.jointlyLocallyInhabited_inverseImage g _ hV

/-! ### The surjectivity onto the final sheaf -/

/-- **`∐ᵢ g⁻¹h_{V i} ⟶ *` is a surjection of sheaves on the small étale site of `X`**, for `V i`
a family of étale charts of `Y` covering the final object of the small étale site of `Y` and `g`
a morphism of topoi `Sh(X_étale) ⟶ Sh(Y_étale)`.

The target is an arbitrary terminal sheaf and the morphisms into it are arbitrary, because
terminality of the target is the only thing the argument uses: over a chart carrying a section
of some `g⁻¹h_{V i}` the coprojection produces a section of the coproduct, and that it is a
preimage of the prescribed section of the target is automatic.

This is the hypothesis `hc` of
`AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_sigmaDesc`.  A consumer
that does not want to produce a coproduct should use
`AlgebraicGeometry.Space.isCofinalChartFamily_inverseImage_smallEtaleChartSheaf` instead, which
reaches the same conclusion with no colimit and no constraint on the index universe. -/
theorem isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf
    (g : MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS X.1) (Type u))
      (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))
    (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    [HasCoproduct fun i => g.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))]
    {Z : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (hZ : IsTerminal Z)
    (c : ∀ i, g.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i)) ⟶ Z) :
    Sheaf.IsLocallySurjective (Sigma.desc c) :=
  Stacks.Topos.isLocallySurjective_sigmaDesc_of_jointlyLocallyInhabited _ hZ c
    (jointlyLocallyInhabited_inverseImage_smallEtaleChartSheaf B S hS g V hV)

/-- `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf`
with the final sheaf of the small étale site spelled out as the constant sheaf `PUnit`, which is
the shape `AlgebraicGeometry.Space.isCofinalChartFamily_of_isLocallySurjective_finalSheaf`
consumes. -/
theorem isLocallySurjective_sigmaDesc_finalSheaf_inverseImage_smallEtaleChartSheaf
    (g : MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS X.1) (Type u))
      (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))
    (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    [HasCoproduct fun i => g.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))]
    (c : ∀ i, g.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i)) ⟶
      Sheaf.terminal (SmallEtale.topology B S hS X.1) Types.isTerminalPUnit) :
    Sheaf.IsLocallySurjective (Sigma.desc c) :=
  isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf B S hS g V hV
    (Sheaf.isTerminalTerminal _ Types.isTerminalPUnit) c

/-- **`∐ᵢ ψ⁻¹h_{V i} ⟶ *` is a surjection of sheaves**, for `ψ` a morphism of the small étale
ringed topoi of `X` and `Y`.  This is
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf` at the
morphism of topoi underlying `ψ`; it is the form the proof of [Stacks Project, Tag 04KL]
produces, where `ψ` is the `(g, g^♯)` being recovered. -/
theorem isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf_ringedToposHom
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    [HasCoproduct fun i =>
      ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))]
    {Z : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (hZ : IsTerminal Z)
    (c : ∀ i, ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i)) ⟶ Z) :
    Sheaf.IsLocallySurjective (Sigma.desc c) :=
  isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf B S hS ψ.toToposHom V hV hZ c

/-! ### The cofinality, without a coproduct -/

/-- **The charts of `X` over which some `g⁻¹h_{V i}` has a section are cofinal among the affine
étale charts of `X`.**  This is the conclusion item (d) of [Stacks Project, Tag 04KL] needs, and
it carries no coproduct: the hypothesis of
`AlgebraicGeometry.Space.isCofinalChartFamily_hasSomeChartSection` is the covering sieve
produced by
`AlgebraicGeometry.Space.jointlyLocallyInhabited_inverseImage_smallEtaleChartSheaf`, which is
`Stacks.Topos.inhabitedSieve` and whose membership condition is
`AlgebraicGeometry.Space.SmallEtale.HasSomeSection` on the nose.

So the index type of the cover is unconstrained here, unlike in
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf`. -/
theorem isCofinalChartFamily_inverseImage_smallEtaleChartSheaf
    (g : MorphismOfTopoi (Sheaf (SmallEtale.topology B S hS X.1) (Type u))
      (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))
    (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V) :
    IsCofinalChartFamily B S hS (F := X.1) (HasSomeChartSection B S hS X.1
      fun i => g.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))) :=
  isCofinalChartFamily_hasSomeChartSection B S hS X.1 _ fun W =>
    ⟨_, jointlyLocallyInhabited_inverseImage_smallEtaleChartSheaf B S hS g V hV W,
      fun _ _ hh => hh⟩

/-- `AlgebraicGeometry.Space.isCofinalChartFamily_inverseImage_smallEtaleChartSheaf` for the
morphism of topoi underlying a morphism `ψ` of small étale ringed topoi. -/
theorem isCofinalChartFamily_inverseImage_smallEtaleChartSheaf_ringedToposHom
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V) :
    IsCofinalChartFamily B S hS (F := X.1) (HasSomeChartSection B S hS X.1
      fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))) :=
  isCofinalChartFamily_inverseImage_smallEtaleChartSheaf B S hS ψ.toToposHom V hV

/-! ### The two gluing statements with their cofinality hypothesis discharged -/

/-- **A family of morphisms to `Y`, given on the charts of `X` carrying a section of some
`ψ⁻¹h_{V i}` and compatible up to 2-isomorphism, glues to a morphism `X ⟶ Y`.**

This is `AlgebraicGeometry.Space.exists_hom_of_chartHoms_twoIso_of_cofinal` — step 5 of the
proof of [Stacks Project, Tag 04KL] — with its cofinality hypothesis discharged by
`AlgebraicGeometry.Space.isCofinalChartFamily_inverseImage_smallEtaleChartSheaf_ringedToposHom`,
so that the only datum about the cover is that the `V i` cover the final object of the small
étale site of `Y`. -/
theorem exists_hom_of_chartHoms_twoIso_of_coversTop
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    (k : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
      ∀ b : yoneda.obj T ⟶ X.1, IsEtale B S hS b →
        HasSomeChartSection B S hS X.1
          (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))) T b →
        (yoneda.obj T ⟶ Y.1))
    (hk : ∀ (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (hU : IsAffineOver B S hS U) (r : T ⟶ U) (b : yoneda.obj U ⟶ X.1)
      (hb : IsEtale B S hS b) (hrb : IsEtale B S hS (yoneda.map r ≫ b))
      (hPb : HasSomeChartSection B S hS X.1
        (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))) U b)
      (hPrb : HasSomeChartSection B S hS X.1
        (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))) T
        (yoneda.map r ≫ b)),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS
          (ObjectProperty.homMk (yoneda.map r ≫ k U hU b hb hPb) :
            (schemeSpace T : AlgebraicSpaces B S hS) ⟶ Y))
        (smallEtaleRingedToposHom B S hS
          (ObjectProperty.homMk (k T hT (yoneda.map r ≫ b) hrb hPrb) :
            (schemeSpace T : AlgebraicSpaces B S hS) ⟶ Y))))
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ X.1) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : X.1 ⟶ Y.1, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (r : T ⟶ U)
      (hrb : IsEtale B S hS (yoneda.map r ≫ b))
      (hPrb : HasSomeChartSection B S hS X.1
        (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))) T
        (yoneda.map r ≫ b)),
      yoneda.map r ≫ b ≫ l = k T hT (yoneda.map r ≫ b) hrb hPrb :=
  exists_hom_of_chartHoms_twoIso_of_cofinal B S hS X.property.isSheaf
    (isCofinalChartFamily_inverseImage_smallEtaleChartSheaf_ringedToposHom B S hS ψ V hV)
    k hk U b hb hsurj

/-- **Chartwise 2-isomorphisms over the charts of `X` carrying a section of some `ψ⁻¹h_{V i}`
glue to a global one.**

This is `AlgebraicGeometry.Space.inducesSmallEtaleRingedToposHom_of_cofinal` — step 6 of the
proof of [Stacks Project, Tag 04KL] — with its cofinality hypothesis discharged by
`AlgebraicGeometry.Space.isCofinalChartFamily_inverseImage_smallEtaleChartSheaf_ringedToposHom`.
Its conclusion is the predicate `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` demands. -/
theorem inducesSmallEtaleRingedToposHom_of_coversTop
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (l : X ⟶ Y) (V : I → SmallEtale B S hS Y.1)
    (hV : (SmallEtale.topology B S hS Y.1).CoversTop V)
    (ht : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
      ∀ b : yoneda.obj T ⟶ X.1, IsEtale B S hS b →
        HasSomeChartSection B S hS X.1
          (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (V i))) T b →
        InducesSmallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b ≫ l)
          (smallEtaleComp B S hS ψ
            (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) :
    InducesSmallEtaleRingedToposHom B S hS l ψ :=
  inducesSmallEtaleRingedToposHom_of_cofinal B S hS ψ l _
    (isCofinalChartFamily_inverseImage_smallEtaleChartSheaf_ringedToposHom B S hS ψ V hV) ht

/-! ### Nothing above is vacuous -/

/-- **Every algebraic space has a single étale chart covering the final object of its small étale
site, with the one-element index type in `Type u`.**  The chart is the scheme atlas of
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`, which is surjective and étale, so
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective` applies;
`CategoryTheory.GrothendieckTopology.coversTop_punit` then moves the one-element family down to
the index universe at which the coproduct of the inverse images exists.

So the hypothesis `hV` of every statement above is satisfiable for every algebraic space, with
no quasi-compactness and at an index type small enough for
`AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_inverseImage_smallEtaleChartSheaf`. -/
theorem SmallEtale.exists_coversTop_punit (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    ∃ U : SmallEtale B S hS F,
      (SmallEtale.topology B S hS F).CoversTop fun _ : PUnit.{u + 1} => U := by
  obtain ⟨U, a, hasurj, haet⟩ := hF.exists_atlas
  refine ⟨⟨CostructuredArrow.mk a, haet⟩, GrothendieckTopology.coversTop_punit
    (SmallEtale.coversTop_of_isSurjective B S hS F hF _ ?_)⟩
  exact (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).1 hasurj

/-- **The selected class of charts is not empty.**  For the identity morphism of topoi the
inverse image is the identity functor, so the chart `V i` itself carries a section of
`h_{V i}` — the identity — and is therefore selected by
`AlgebraicGeometry.Space.HasSomeChartSection`.

Together with `AlgebraicGeometry.Space.SmallEtale.exists_coversTop_punit` this shows that the
statements above have non-empty content: the covering families they ask for exist, and the class
of charts they select is inhabited rather than the empty class, which would make
`AlgebraicGeometry.Space.IsCofinalChartFamily` hold for degenerate reasons. -/
theorem hasSomeChartSection_id_smallEtaleChartSheaf (V : I → SmallEtale B S hS X.1) (i : I) :
    HasSomeChartSection B S hS X.1
      (fun j => (MorphismOfTopoi.id
          (Sheaf (SmallEtale.topology B S hS X.1) (Type u))).inverseImage.obj
        (smallEtaleChartSheaf B S hS X (V j)))
      ((SmallEtale.toOver B S hS X.1).obj (V i)) (V i).1.hom :=
  hasSomeChartSection_of_hasSomeSection B S hS X.1 ⟨i, ⟨𝟙 (V i)⟩⟩

end AlgebraicGeometry.Space

end
