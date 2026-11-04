module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionExt
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartBaseFunction
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.CompositionOfLocallyRingedMorphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.TwoIsoAndRightCancellation

/-!
# Transporting the functions pulled back from the base along a morphism of ringed topoi

Let `X`, `Y` be algebraic spaces over a scheme `S` of a big fppf site `B` and let
`(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of their small étale ringed
topoi.  A regular function `r` on `S` is a global regular function on `Y`
(`AlgebraicGeometry.Space.baseGlobalFunction`) and `g` transports it to a regular function on
every étale chart of `X` (`AlgebraicGeometry.Space.baseFunctionTransport`).  This file proves
that the transported function is again the function pulled back from the base **as soon as `g`
is 2-compatible with a pair of morphisms to a third algebraic space**, which is the hypothesis
of [Stacks Project, Tag 04KL] over a base.

Three statements carry it, and they are the three the reduction of
`StacksFrontier/AlgebraicGeometry/Spaces/RecoveringMorphisms/ChartBaseFunction.lean` asks for:

* for `g` the morphism of ringed topoi of a morphism `f : X ⟶ Y` of algebraic spaces over `S`,
  the transport of `r` is the function pulled back from the base
  (`AlgebraicGeometry.Space.baseFunctionTransport_smallEtaleRingedToposHom`).  The content is
  Stacks 03G8, the chartwise formula for the structure homomorphism: in direct-image form the
  structure map sends a regular function on an étale chart `V` of `Y` to its pullback along the
  vertical morphism of schemes of a chart diagram over `f`, and that morphism is a morphism of
  the big fppf category over `S`, hence a morphism over `S`;
* the transport is invariant under a 2-isomorphism
  (`AlgebraicGeometry.Space.baseFunctionTransport_eq_of_twoIso`), because a 2-isomorphism
  carries the inverse-image form of one structure map to that of the other
  (`AlgebraicGeometry.RingedToposHom.TwoIso.fSharpSet_eq`);
* the transport along a composite is the transport along the second factor of the transport
  along the first (`AlgebraicGeometry.Space.baseFunctionTransport_comp`), because the
  inverse-image form of the structure map of a composite is the inverse image of one followed
  by the other (`AlgebraicGeometry.RingedToposHom.fSharpSet_comp`).

Put together they give the main result below: for `pP : P ⟶ A`, `pQ : Q ⟶ A` and a `ψ` whose
composite with `pQ` is 2-isomorphic to `pP`, the transport of a function on the base along `ψ`
is the function pulled back from the base.  The three statements are *all* that is needed: no
affineness of anything and no local ringedness of `ψ`.

The 2-compatibility is not removable, and the counterexample is the one recorded in the
docstring of `AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`: for `S = P = Q = Spec ℚ(i)`,
the `σ`-twist `ψ` of the identity fixes every ring of sections but transports `i` to `σ(i) = -i`,
so the conclusion fails for it — as it must, since that `ψ` admits no 2-isomorphism to the
identity.

## Main results

* `AlgebraicGeometry.Space.baseFunctionTransport_smallEtaleRingedToposHom`: a morphism of
  algebraic spaces over `S` transports the functions pulled back from the base to themselves.
* `AlgebraicGeometry.Space.baseFunctionTransport_eq_of_twoIso`: the transport is invariant
  under a 2-isomorphism.
* `AlgebraicGeometry.Space.baseFunctionTransport_comp`: the transport along a composite.
* `AlgebraicGeometry.Space.baseFunctionTransport_eq_of_twoCompatible`: **a morphism of the small
  étale ringed topoi which is 2-compatible with a pair of structure morphisms transports the
  functions pulled back from the base to themselves.**

## Implementation notes

The transport is read off the *inverse-image* form `g⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map, which
is the form the 2-isomorphism and the composition lemmas are stated in, while the chartwise
formula of Stacks 03G8 is in direct-image form.  The two are adjunct, so the first statement is
proved by transposing: `AlgebraicGeometry.Space.baseGlobalFunction_comp_structureSharpSet` is
the direct-image form of it, and there the sections of the direct image over a chart `V` of `Y`
are tested by their chart projections
(`AlgebraicGeometry.Space.hom_ext_directImageChartProjection`), where the formula applies.  The
transposed statement is an equality of two morphisms *out of the terminal sheaf* and the second
of them is not named: its chart projections are computed from naturality alone, so it is taken
as an argument.

The inverse image of the terminal sheaf has exactly one section over every chart
(`AlgebraicGeometry.Space.uniqueInverseImageTerminal`), which is what makes the transport a
function of `g` and `r` alone and what discharges every comparison of sections of it below.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] smallEtaleTopology_subcanonical

variable {X Y Z : AlgebraicSpaces B S hS}

/-! ### A morphism of algebraic spaces transports the functions of the base to themselves -/

/-- **Two morphisms into the direct image of a sheaf of sets agree as soon as the chart
projections of all their values agree.**  This is
`AlgebraicGeometry.Space.directImageChartProjection_ext` read for morphisms rather than for
sections. -/
theorem hom_ext_directImageChartProjection (f : X ⟶ Y)
    {A : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)}
    {F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    {m m' : A ⟶ (smallEtaleDirectImage B S hS f).obj F}
    (h : ∀ (V : SmallEtale B S hS Y.1) (x : A.obj.obj (op V))
      (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op),
      (directImageChartProjection B S hS f V j).app F (m.hom.app (op V) x) =
        (directImageChartProjection B S hS f V j).app F (m'.hom.app (op V) x)) :
    m = m' :=
  Sheaf.hom_ext_sections fun V x ↦ by
    obtain ⟨V⟩ := V
    exact directImageChartProjection_ext B S hS f V F fun j ↦ h V x j

/-- **The chart of an arrow into the cartesian base change is a chart over the base**: its
structure morphism to the base factors, through the chartwise morphism of the arrow, that of the
chart of the target.  This is
`AlgebraicGeometry.Space.chartToBase_comp_chartDiagram` at the diagram of charts the arrow
determines. -/
theorem chartBaseChangeMap_comp_chartToBase (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (BigFppfOver.toScheme B S hS).map (chartBaseChangeMap B S hS f V j) ≫
        chartToBase B S hS Y V =
      chartToBase B S hS X j.right.unop :=
  chartToBase_comp_chartDiagram B S hS f
    (chartDiagramOfBaseChangeArrow B S hS f j.right.unop V j.hom.unop)

/-- **The direct-image form of the transport of a function pulled back from the base.**  The
global function `r` determines on `Y`, followed by the direct-image form of the structure map of
a morphism `f : X ⟶ Y` of algebraic spaces over `S`, is the global function `r` determines on
`X`, read through *any* morphism from the terminal sheaf to the direct image of the terminal
sheaf.

The second morphism is arbitrary because it is only ever evaluated: over an étale chart `V` of
`Y` both sides are tested by their chart projections, and the chart projections of the
right-hand side are, by naturality, the values of the global function of `X` — whatever section
of the direct image of the terminal sheaf they are taken at.  Those of the left-hand side are
the chartwise pullbacks of `r`, by Stacks 03G8, and the two agree because the chartwise
morphisms are morphisms over the base. -/
theorem baseGlobalFunction_comp_structureSharpSet (f : X ⟶ Y) (r : Γ(S, ⊤))
    (ι : (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶
      (smallEtaleDirectImage B S hS f).obj
        (⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u))) :
    baseGlobalFunction Y r ≫ structureSharpSet B S hS f =
      ι ≫ (smallEtaleDirectImage B S hS f).map (baseGlobalFunction X r) := by
  refine hom_ext_directImageChartProjection f fun V x j ↦ ?_
  have hL : (directImageChartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        ((baseGlobalFunction Y r ≫ structureSharpSet B S hS f).hom.app (op V) x) =
      chartPullback B S hS f V j ((chartToBase B S hS Y V).appTop.hom r) := by
    show (directImageChartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        ((structureSharpSet B S hS f).hom.app (op V)
          ((baseGlobalFunction Y r).hom.app (op V) x)) = _
    rw [baseGlobalFunction_app]
    exact directImageChartProjection_structureSharpSet B S hS f V j _
  have hR : (directImageChartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        ((ι ≫ (smallEtaleDirectImage B S hS f).map (baseGlobalFunction X r)).hom.app (op V) x) =
      (chartToBase B S hS X j.right.unop).appTop.hom r := by
    refine Eq.trans (directImageChartProjection_map B S hS f V j
      (baseGlobalFunction X r) (ι.hom.app (op V) x)) ?_
    exact baseGlobalFunction_app X r j.right.unop _
  have h := congrArg (fun k : chartScheme j.right.unop ⟶ S => k.appTop.hom r)
    (chartBaseChangeMap_comp_chartToBase f V j)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  exact hL.trans (h.trans hR.symm)

/-- **The transport of a function pulled back from the base along the morphism of ringed topoi of
a morphism of algebraic spaces over `S` is the function pulled back from the base**, in
inverse-image form: the inverse image of the global function `r` determines on `Y`, followed by
the inverse-image form of the structure map, is the global function `r` determines on `X`, read
through the unique morphism to the terminal sheaf.

This is `AlgebraicGeometry.Space.baseGlobalFunction_comp_structureSharpSet` transposed along the
adjunction of Stacks 03G8. -/
theorem baseGlobalFunction_transport_smallEtaleRingedToposHom (f : X ⟶ Y) (r : Γ(S, ⊤)) :
    (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
          (baseGlobalFunction Y r) ≫
        (smallEtaleRingedToposHom B S hS f).fSharpSet =
      terminal.from _ ≫ baseGlobalFunction X r := by
  have hleft : (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.map
        (baseGlobalFunction Y r) ≫
        (smallEtaleRingedToposHom B S hS f).fSharpSet =
      ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv _ _).symm
        (baseGlobalFunction Y r ≫ RingedToposHom.forgetFSharp
          (smallEtaleRingedToposHom B S hS f)) :=
    (Adjunction.homEquiv_naturality_left_symm _ _ _).symm
  have hff : RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f) =
      structureSharpSet B S hS f := forgetRing_map_fSharp B S hS f
  rw [hleft, Equiv.symm_apply_eq, Adjunction.homEquiv_naturality_right, hff]
  exact baseGlobalFunction_comp_structureSharpSet f r _

/-- The value over a chart of a global function pulled back from the base, read through any
morphism to the terminal sheaf, is `r` pulled back along the structure morphism of the chart. -/
theorem comp_baseGlobalFunction_app {T : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (k : T ⟶ (⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u))) (r : Γ(S, ⊤))
    (U : SmallEtale B S hS X.1) (t : T.obj.obj (op U)) :
    (k ≫ baseGlobalFunction X r).hom.app (op U) t = (chartToBase B S hS X U).appTop.hom r :=
  baseGlobalFunction_app X r U (k.hom.app (op U) t)

/-- If the inverse-image form of the structure map applied to the function pulled back from the
base factors through some `k` followed by `m`, then the transport is `k ≫ m` read at the default
section. -/
private theorem baseFunctionTransport_eq_comp_app
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    {W : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (k : g.toToposHom.inverseImage.obj (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶ W)
    (m : W ⟶ setO X) (r : Γ(S, ⊤))
    (h : g.toToposHom.inverseImage.map (baseGlobalFunction Y r) ≫ g.fSharpSet = k ≫ m)
    (U : SmallEtale B S hS X.1) :
    baseFunctionTransport g r U = (k ≫ m).hom.app (op U) default :=
  congrArg (fun m : _ ⟶ setO X ↦ m.hom.app (op U) default) h

/-- **A morphism of algebraic spaces over `S` transports the functions pulled back from the base
to themselves**: over every étale chart `U` of `X` the transported function is `r` pulled back
along the structure morphism of `U` to the base. -/
theorem baseFunctionTransport_smallEtaleRingedToposHom (f : X ⟶ Y) (r : Γ(S, ⊤))
    (U : SmallEtale B S hS X.1) :
    baseFunctionTransport (smallEtaleRingedToposHom B S hS f) r U =
      (chartToBase B S hS X U).appTop.hom r := by
  exact (baseFunctionTransport_eq_comp_app _ _ _ r
    (baseGlobalFunction_transport_smallEtaleRingedToposHom f r) U).trans
    (comp_baseGlobalFunction_app _ r U default)

/-! ### The transport under a 2-isomorphism and under composition -/

variable (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

/-- The transport of a function pulled back from the base, read after any morphism into the
inverse image of the terminal sheaf, is the transport itself: that inverse image has a single
section over every chart. -/
theorem comp_inverseImageTerminal_app
    {T : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (k : T ⟶ g.toToposHom.inverseImage.obj
      (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)))
    (m : g.toToposHom.inverseImage.obj
      (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶ setO X)
    (U : SmallEtale B S hS X.1) (t : T.obj.obj (op U)) :
    (k ≫ m).hom.app (op U) t = m.hom.app (op U) default :=
  congrArg (m.hom.app (op U)) (Subsingleton.elim _ _)

/-- **The transport of a function pulled back from the base is invariant under a
2-isomorphism.**  A 2-isomorphism of morphisms of ringed topoi is an isomorphism of their direct
images, and the conjugate isomorphism of their inverse images carries the inverse-image form of
one structure map to that of the other
(`AlgebraicGeometry.RingedToposHom.TwoIso.fSharpSet_eq`); the inverse image of the terminal
sheaf has a single section over every chart, so the isomorphism does not move the section the
transport is read at. -/
theorem baseFunctionTransport_eq_of_twoIso
    {g' : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
    (t : RingedToposHom.TwoIso (A := smallEtaleRingedTopos B S hS X)
      (B := smallEtaleRingedTopos B S hS Y) g g') (r : Γ(S, ⊤))
    (U : SmallEtale B S hS X.1) :
    baseFunctionTransport g r U = baseFunctionTransport g' r U := by
  have hnat := t.symm.inverseImageIso.hom.naturality (baseGlobalFunction Y r)
  have hkey : g.toToposHom.inverseImage.map (baseGlobalFunction Y r) ≫ g.fSharpSet =
      t.symm.inverseImageIso.hom.app (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ≫
        (g'.toToposHom.inverseImage.map (baseGlobalFunction Y r) ≫ g'.fSharpSet) := by
    rw [t.fSharpSet_eq, ← Category.assoc]
    exact (congrArg (fun m ↦ m ≫ g'.fSharpSet) hnat).trans (Category.assoc _ _ _)
  exact (baseFunctionTransport_eq_comp_app g _ _ r hkey U).trans
    (comp_inverseImageTerminal_app g' _ _ U default)

section Comp

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **The transport of a function pulled back from the base along a composite**, when the first
factor transports it to the function pulled back from the base: then the composite transports it
to whatever the second factor does.

The inverse-image form of the structure map of a composite is the inverse image along the second
factor of that of the first, followed by that of the second
(`AlgebraicGeometry.RingedToposHom.fSharpSet_comp`), so the transport along the composite is the
transport along the second factor of the transport along the first. -/
theorem baseFunctionTransport_comp
    (χ : RingedToposHom (smallEtaleRingedTopos B S hS Y) (smallEtaleRingedTopos B S hS Z))
    (r : Γ(S, ⊤))
    (hχ : χ.toToposHom.inverseImage.map (baseGlobalFunction Z r) ≫ χ.fSharpSet =
      terminal.from _ ≫ baseGlobalFunction Y r)
    (U : SmallEtale B S hS X.1) :
    baseFunctionTransport (RingedToposHom.comp
        (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (Z := smallEtaleRingedTopos B S hS Z) χ g) r U =
      baseFunctionTransport g r U := by
  refine (baseFunctionTransport_eq_comp_app
    (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
      (Z := smallEtaleRingedTopos B S hS Z) χ g) (g.toToposHom.inverseImage.map (terminal.from _))
    (g.toToposHom.inverseImage.map (baseGlobalFunction Y r) ≫ g.fSharpSet) r ?_ U).trans
    (comp_inverseImageTerminal_app g _ _ U default)
  rw [RingedToposHom.fSharpSet_comp χ g]
  show g.toToposHom.inverseImage.map (χ.toToposHom.inverseImage.map
        (baseGlobalFunction Z r)) ≫
      g.toToposHom.inverseImage.map χ.fSharpSet ≫ g.fSharpSet = _
  rw [← Category.assoc, ← Functor.map_comp, hχ, Functor.map_comp, Category.assoc]

end Comp

/-! ### The transport under the 2-compatibility of Stacks 04KL over a base -/

/-- **A morphism of the small étale ringed topoi which is 2-compatible with a pair of structure
morphisms to a third algebraic space transports the functions pulled back from the base to
themselves.**

This is the hypothesis which the reduction of
`AlgebraicGeometry.Space.chartSchemeHom_comp_inclusion_map_of_baseFunctionTransport` asks of
`ψ`, and it is derived here from the 2-compatibility of
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` and nothing else: the composite
`p_Q ∘ ψ` transports `r` to what `ψ` does, because `p_Q` transports it to the function pulled
back from the base, and it transports `r` to the function pulled back from the base, because it
is 2-isomorphic to `p_P`, which does. -/
theorem baseFunctionTransport_eq_of_twoCompatible {A P Q : AlgebraicSpaces B S hS}
    (pP : P ⟶ A) (pQ : Q ⟶ A)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS P) (smallEtaleRingedTopos B S hS Q))
    (t : RingedToposHom.TwoIso (A := smallEtaleRingedTopos B S hS P)
      (B := smallEtaleRingedTopos B S hS A)
      (RingedToposHom.comp (X := smallEtaleRingedTopos B S hS P)
        (Y := smallEtaleRingedTopos B S hS Q) (Z := smallEtaleRingedTopos B S hS A)
        (smallEtaleRingedToposHom B S hS pQ) ψ)
      (smallEtaleRingedToposHom B S hS pP))
    (r : Γ(S, ⊤)) (U : SmallEtale B S hS P.1) :
    baseFunctionTransport ψ r U = (chartToBase B S hS P U).appTop.hom r := by
  have h1 := baseFunctionTransport_comp ψ (smallEtaleRingedToposHom B S hS pQ) r
    (baseGlobalFunction_transport_smallEtaleRingedToposHom pQ r) U
  have h2 := baseFunctionTransport_eq_of_twoIso _ t r U
  have h3 := baseFunctionTransport_smallEtaleRingedToposHom pP r U
  exact h1.symm.trans (h2.trans h3)

end AlgebraicGeometry.Space

end
