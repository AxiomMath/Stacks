module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport

/-!
# The Veronese family of a chart-wise class, computed

Let `S` be a scheme, `A` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `V` an open of
`S` and `d ≥ 1`. `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Fd.chartClass` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport` reads a quadruple
for `A` over a morphism factoring as `g_V ≫ V.ι : T ⟶ V ⟶ S` as a point of `F_d(T)` for the
restriction `A|_V`, and `Fd.chartClass_mk` unfolds it: the class of a quadruple `P` goes to the
class of `P` base-changed along `V.ι` ([Stacks, Tag 01NT]) and then transported along
`...RelativeProjQcohSheaf.unitalHomInverse` of `restrictPullbackUnitalHom`.

That docstring records a measurement: the transport is along the **inverse** of an adjoint
transpose of the unit of the restriction adjunction, so the value of the transported `ψ` on a
global section is not available by unfolding, and the computation of
`...RelativeProjQcohSheaf.veroneseSections` for a chart-wise class was recorded as not done.

**This file does that computation.** It is available after all, and the route does not go through
the inverse at all: `chartTwisting_sectionHom` below says that the transported `ψ`, read on
sections over the preimage `V.ι ⁻¹ᵁ W` of an open `W` of `S` **at the unit image of a section of
`A` over `W`**, is the original `ψ` transposed over `W`. In that shape only the *forward* maps
occur, and the three bricks that prove it are
`Stacks.RingedSpace.pullbackUnit_naturality`,
`Stacks.PullbackCompMonoidal.comparison_pullbackUnit` and
`Stacks.RingedSpace.transposeApp_pullbackUnit`; the inverse is discharged once, by
`...RelativeProjQcohSheaf.val_app_roundtrip`, in
`unitalHomInverse_restrictPullbackUnitalHom_app`.

The sections of `A|_V` over `⊤` *are* the sections of `A` over `V.ι ''ᵁ ⊤`, so taking `W` to be
that image open turns the general statement into a formula for the transported `ψ`'s
`Twisting.globalSectionHom` (`chartTwisting_globalSectionHom`), hence for the Veronese family
(`veroneseSections_chartTwisting`). The one identification needed on the way is
`restrictUnit_image_top`: the unit of the restriction adjunction at the open `V.ι ''ᵁ ⊤` is, after
the identification `V.ι ⁻¹ᵁ (V.ι ''ᵁ ⊤) = ⊤`, the identity.

## Main definitions

* `...RelativeProjQcohSheaf.Twisting.baseUnit` and `...RelativeProjQcohSheaf.restrictUnit`: the
  pullback-unit image of a local section of `A`, typed at the **base-changed** algebra of
  [Stacks, Tag 01NT], and the restriction-adjunction unit image of one, typed at the
  **restriction** of `...RelativeProjBridge.SheafGradedAlgebra.restrict`. See the implementation
  notes for why these two wrappers exist.

## Main results

* `...RelativeProjQcohSheaf.Twisting.algebraTransport_sectionHom`,
  `...Twisting.baseChangeUp_sectionHom` and `...Twisting.sectionHom_restrict`: the transposed map
  of a quadruple on sections, read across a unital homomorphism of the algebra, across the base
  change of [Stacks, Tag 01NT], and along a restriction of the open.
* `...RelativeProjQcohSheaf.unitalHomInverse_restrictPullbackUnitalHom_app`: **the inverse
  comparison of the two spellings of the restriction, on a unit image** — the one place the
  inverse is touched.
* `...RelativeProjQcohSheaf.chartTwisting_sectionHom`: **the transported `ψ` of a chart-wise
  class, on sections.**
* `...RelativeProjQcohSheaf.chartTwisting_globalSectionHom`: **the same on global sections of the
  chart's algebra**, which is the value the Veronese family is built from.
* `...RelativeProjQcohSheaf.veroneseSections_chartTwisting`: **the Veronese family of a chart-wise
  class.**

## What this does not do, and where that is done

It does **not** itself discharge the hypothesis `hψU` of
`...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_comp_projInclusionMap`, which asks that the
Veronese families of the chart-wise classes at two affine opens `Z ≤ U` be related by
`...ProjChartGradedClassifying.comapVeronese`. That is
`...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassComap`, and the two transports it
adds to the formula above are: the comparison of the *base morphisms* `g_Z ≫ Z.ι` and
`g_U ≫ U.ι` — two factorizations of one `g : T ⟶ S` — and the heterogeneous transport of the
grading from `(A.restrict V.ι).grading ⊤` to `A.grading V`. Neither is what an earlier note here
predicted. The first is *not* a transport along
`...RelativeProjQcohSheaf.Twisting.globalSectionHom_congrBase`: the comparison of the two charts
happens over the image opens `Z.ι ''ᵁ ⊤` and `U.ι ''ᵁ ⊤`, which are not `⊤` in `S`, so global
sections do not reach it, and what does is `...ChartClassComap.Twisting.sectionHom_heq`, on
sections over an arbitrary open. The second is not assembled from
`...SheafGradedAlgebra.restrict_ι_grading_top` but from
`...ChartClassComap.veroneseSections_toFun_heq`, which carries every instance as an argument.

The *computational* half of the comparison is here: `sectionHom_resPiece` says the transposed map
commutes with the restriction of the graded ring of sections, which is what `comapVeronese` of
`...RelativeProjBridge.SheafGradedAlgebra.res` acts by.

## Implementation notes

**Why `Twisting.baseUnit` and `restrictUnit` exist.** `(baseAlgebra g A).piece m` is
`(pullbackFunctor g).obj (A.piece m)` by `rfl`, and the sections of the pushforward of `A|_X` over
`W` are the sections of `A|_X` over `f ⁻¹ᵁ W` by `rfl` — but neither `rfl` holds at the
`implicit` transparency `rw` checks its motives at, so a goal stating either in the unwrapped
spelling is reported as not type-correct and no rewrite fires in it. Naming the two unit images
once, each at the type the consumer expects, keeps every goal below type-correct. Where a
statement still mixes the spellings — `Twisting.baseChangeUp_sectionHom`, whose own definition
`Twisting.baseChangeUpApp` only typechecks after `baseAlgebra` is unfolded — the proof is written
in term mode, where the defeq is checked at default transparency.

**The open `V.ι ⁻¹ᵁ (V.ι ''ᵁ ⊤) = ⊤` is an argument, not a rewrite.**
`restrictUnit_image_top` takes the equality as a hypothesis, so that a caller passing its own
proof gets a syntactic match; the version that proved it internally could not be rewritten with,
the equality's two sides being spelled `V.ι ⁻¹ᵁ _` on one side and
`(opensMap (ringedSpaceHom V.ι)).obj _` on the other. Those two are definitionally equal and are
*not* syntactically equal, which is also why `top_le_preimage_image_top` needs a `show ... from
rfl` to change spelling before rewriting.

**The restriction morphisms on the test scheme are arguments too.** `(g_V ≫ V.ι) ⁻¹ᵁ (V.ι ''ᵁ ⊤)`
and `⊤` are equal opens of `T`, so all the restriction maps between their sections agree by
`Subsingleton.elim` — the category of opens is thin. Rather than fix one, the statements take the
morphism as an argument; `top_le_preimage_image_top` supplies one.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

namespace Twisting

variable {T X : Scheme.{u}} {f : T ⟶ X}
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The transposed map of a quadruple read across a unital homomorphism of the algebra, on
sections.** For `Φ : 𝒜 ⟶ ℬ` a unital homomorphism of sheaves of graded algebras on the base and
`χ` a map `ψ` for `ℬ`, the degree-`i` component of
`...RelativeProjQcohSheaf.Twisting.algebraTransport` evaluated on a section `a` of `𝒜_{id}` over
an open `W` is the component of `χ` evaluated on the image of `a` under `Φ`.

The whole content is the naturality `Stacks.RingedSpace.pullbackUnit_naturality` of the unit of
`f^* ⊣ f_*` in the sheaf of modules: the transport precomposes `χ` with the pullback of `Φ`, and
on a unit image the pullback of `Φ` is `Φ` on sections. -/
theorem algebraTransport_sectionHom (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : Twisting f B d L) (i : ℤ) (W : (Opens X.toRingedSpace.carrier)ᵒᵖ)
    (a : (A.piece (i * d)).val.obj W) :
    (Twisting.algebraTransport Φ χ).sectionHom i W a =
      χ.sectionHom i W ((Φ.app (i * d)).val.app W a) := by
  rw [sectionHom_apply, sectionHom_apply, algebraTransport_app,
    SheafOfModules.comp_val_app_apply, pullbackUnit_naturality]

/-- **The transposed map of a quadruple commutes with a restriction of the open.** Restricting a
section of `𝒜_{id}` from `W` to a smaller open and then transposing is transposing over `W` and
then restricting the resulting section of `L^{⊗ i}` along the preimage.

This is the naturality of `ψ`'s degree-`i` component as a morphism of sheaves of modules together
with the naturality `Stacks.RingedSpace.pullbackUnit_restrict` of the unit in the open. -/
theorem sectionHom_restrict (χ : Twisting f A d L) (i : ℤ)
    {W W' : (Opens X.toRingedSpace.carrier)ᵒᵖ} (h : W ⟶ W')
    (a : (A.piece (i * d)).val.obj W) :
    χ.sectionHom i W' ((A.piece (i * d)).val.restrictₛₗ h a)
      = ((laurent L).piece i).val.restrictₛₗ ((opensMap (ringedSpaceHom f)).op.map h)
          (χ.sectionHom i W a) := by
  rw [sectionHom_apply, sectionHom_apply, ← pullbackUnit_restrict]
  exact PresheafOfModules.restrictₛₗ_naturality_apply (χ.app i).val
    ((opensMap (ringedSpaceHom f)).op.map h) _

section BaseChange

variable {S S' T : Scheme.{u}} (g : S' ⟶ S) (f' : T ⟶ S')
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The pullback-unit image of a local section of `𝒜`, typed at the base-changed algebra of
[Stacks, Tag 01NT].** The pieces of `...RelativeProjQcohSheaf.baseAlgebra` are the inverse images
of the pieces by `rfl`, but not by a `rfl` the `implicit` transparency sees; naming the image at
the type a map `ψ` for the base-changed algebra consumes is what keeps the goals below
type-correct. See the implementation notes. -/
def baseUnit (m : ℤ) (W : (Opens S.toRingedSpace.carrier)ᵒᵖ)
    (a : (A.piece m).val.obj W) :
    ((baseAlgebra g A).piece m).val.obj ((opensMap (ringedSpaceHom g)).op.obj W) :=
  pullbackUnit (ringedSpaceHom g) (A.piece m) W a

/-- `Twisting.baseUnit` is the pullback-unit image, by definition. -/
theorem baseUnit_eq (m : ℤ) (W : (Opens S.toRingedSpace.carrier)ᵒᵖ)
    (a : (A.piece m).val.obj W) :
    baseUnit g A m W a = pullbackUnit (ringedSpaceHom g) (A.piece m) W a := rfl

/-- **The transposed map of a base-changed quadruple, on sections.** For `g : S' ⟶ S` and
`f' : T ⟶ S'`, the map `ψ` of [Stacks, Tag 01NT]'s `Twisting.baseChangeUp` of a map `χ` for the
base-changed situation, transposed over an open `W` of `S`, is `χ` transposed over the preimage
`g ⁻¹ᵁ W` at the pullback-unit image of the section.

The input is the unit coherence `Stacks.PullbackCompMonoidal.comparison_pullbackUnit` of the
contraction of an iterated pullback: the unit for `g ≫ f'` is the unit for `f'` of the unit for
`g`, read across the contraction. -/
theorem baseChangeUp_sectionHom (χ : Twisting f' (baseAlgebra g A) d L) (i : ℤ)
    (W : (Opens S.toRingedSpace.carrier)ᵒᵖ) (a : (A.piece (i * d)).val.obj W) :
    (χ.baseChangeUp g f' A d).sectionHom i W a =
      χ.sectionHom i ((opensMap (ringedSpaceHom g)).op.obj W)
        (baseUnit g A (i * d) W a) :=
  congrArg
    (fun z : ((pullbackFunctor (ringedSpaceHom f')).obj
        ((baseAlgebra g A).piece (i * d))).val.obj
          ((opensMap (ringedSpaceHom f')).op.obj ((opensMap (ringedSpaceHom g)).op.obj W)) =>
      (χ.app i).val.app
        ((opensMap (ringedSpaceHom f')).op.obj ((opensMap (ringedSpaceHom g)).op.obj W)) z)
    (Stacks.PullbackCompMonoidal.comparison_pullbackUnit (ringedSpaceHom g) (ringedSpaceHom f')
      (A.piece (i * d)) W a)

/-- The two base-change constructions of [Stacks, Tag 01NT] on maps `ψ` are inverse, in the
direction that recovers a map over the composite. This is
`...RelativeProjQcohSheaf.Twisting.baseChangeEquiv` read as an equation, so that it can be
rewritten with. -/
theorem baseChangeUp_baseChangeDown (ψ : Twisting (f' ≫ g) A d L) :
    (ψ.baseChangeDown g f' A d).baseChangeUp g f' A d = ψ :=
  (Twisting.baseChangeEquiv g f' A d).apply_symm_apply ψ

end BaseChange

end Twisting

/-- Two successive restrictions of a section agree with any single restriction between the same
objects, the category of opens being thin. -/
private theorem restrictₛₗ_restrictₛₗ_apply_of_subsingleton {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat} (M : PresheafOfModules R) {X Y Z : Cᵒᵖ} [Subsingleton (X ⟶ Z)]
    (g₁ : X ⟶ Y) (g₂ : Y ⟶ Z) (h : X ⟶ Z) (a : M.obj X) :
    M.restrictₛₗ g₂ (M.restrictₛₗ g₁ a) = M.restrictₛₗ h a := by
  rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.restrictₛₗ_apply,
    PresheafOfModules.restrictₛₗ_apply, ← PresheafOfModules.map_comp_apply,
    Subsingleton.elim (g₁ ≫ g₂) h]

section Restrict

variable {S X : Scheme.{u}} (A : SheafGradedAlgebra S) (f : X ⟶ S) [IsOpenImmersion f]

/-- **The restriction-adjunction unit image of a local section of `𝒜`, typed at the restriction
of `...RelativeProjBridge.SheafGradedAlgebra.restrict`.** Concretely it is the section of `𝒜`
over `f ''ᵁ (f ⁻¹ᵁ W)` obtained by restricting a section over `W`, read as a section of `A|_X`
over `f ⁻¹ᵁ W`. As with `Twisting.baseUnit`, the point of the wrapper is the type: see the
implementation notes. -/
def restrictUnit (n : ℤ) (W : Opens S.toRingedSpace.carrier)
    (a : ((situationAlgebra A).piece n).val.obj (op W)) :
    ((situationAlgebra (A.restrict f)).piece n).val.obj
      (op ((opensMap (ringedSpaceHom f)).obj W)) :=
  ((restrictUnitalHom A f).app n).val.app (op W) a

/-- `restrictUnit` is the unit image of `...RelativeProjQcohSheaf.restrictUnitalHom`, by
definition. -/
theorem restrictUnit_eq (n : ℤ) (W : Opens S.toRingedSpace.carrier)
    (a : ((situationAlgebra A).piece n).val.obj (op W)) :
    restrictUnit A f n W a = ((restrictUnitalHom A f).app n).val.app (op W) a := rfl

/-- **The comparison of the two spellings of the restriction, on a pullback-unit image.** The
degree-`n` component of `...RelativeProjQcohSheaf.restrictPullbackUnitalHom` carries the
pullback-unit image of a section of `𝒜` over `W` to its restriction-adjunction unit image.

This is the defining property of an adjoint transpose,
`Stacks.RingedSpace.transposeApp_pullbackUnit`, for the homomorphism
`...RelativeProjQcohSheaf.restrictUnitalHom` whose transpose the comparison is. -/
theorem restrictPullbackUnitalHom_app_baseUnit (n : ℤ) (W : Opens S.toRingedSpace.carrier)
    (a : ((situationAlgebra A).piece n).val.obj (op W)) :
    ((restrictPullbackUnitalHom A f).app n).val.app
        ((opensMap (ringedSpaceHom f)).op.obj (op W))
        (Twisting.baseUnit f (situationAlgebra A) n (op W) a)
      = restrictUnit A f n W a :=
  Stacks.RingedSpace.transposeApp_pullbackUnit (ringedSpaceHom f) (restrictUnitalHom A f) n W a

/-- **The inverse comparison of the two spellings of the restriction, on a unit image.** The
degree-`n` component of `...RelativeProjQcohSheaf.unitalHomInverse` of the comparison carries the
restriction-adjunction unit image of a section of `𝒜` over `W` back to its pullback-unit image.

This is the only statement in the file about the inverse, and it needs no description of it: the
forward component carries the pullback-unit image to the restriction-adjunction unit image
(`restrictPullbackUnitalHom_app_baseUnit`), and `...RelativeProjQcohSheaf.val_app_roundtrip`
cancels the two. -/
theorem unitalHomInverse_restrictPullbackUnitalHom_app (n : ℤ)
    (W : Opens S.toRingedSpace.carrier)
    (a : ((situationAlgebra A).piece n).val.obj (op W)) :
    ((unitalHomInverse (restrictPullbackUnitalHom A f)
          (isIso_restrictPullbackUnitalHom_app_forall A f)).app n).val.app
        ((opensMap (ringedSpaceHom f)).op.obj (op W))
        (restrictUnit A f n W a)
      = Twisting.baseUnit f (situationAlgebra A) n (op W) a := by
  rw [← restrictPullbackUnitalHom_app_baseUnit A f n W a, unitalHomInverse_app]
  exact val_app_roundtrip ((restrictPullbackUnitalHom A f).app n)
    (@inv _ _ _ _ ((restrictPullbackUnitalHom A f).app n)
      (isIso_restrictPullbackUnitalHom_app_forall A f n))
    (@CategoryTheory.IsIso.hom_inv_id _ _ _ _ ((restrictPullbackUnitalHom A f).app n)
      (isIso_restrictPullbackUnitalHom_app_forall A f n)) _ _

/-- **The restriction-adjunction unit commutes with a restriction of the open**, the naturality
of `...RelativeProjQcohSheaf.restrictUnitalHom` in the open read on sections. -/
theorem restrictUnit_restrict (n : ℤ) {W W₂ : Opens S.toRingedSpace.carrier}
    (h : (op W : (Opens S.toRingedSpace.carrier)ᵒᵖ) ⟶ op W₂)
    (a : ((situationAlgebra A).piece n).val.obj (op W)) :
    ((situationAlgebra (A.restrict f)).piece n).val.restrictₛₗ
        ((opensMap (ringedSpaceHom f)).op.map h) (restrictUnit A f n W a)
      = restrictUnit A f n W₂ (((situationAlgebra A).piece n).val.restrictₛₗ h a) :=
  (PresheafOfModules.restrictₛₗ_naturality_apply ((restrictUnitalHom A f).app n).val h a).symm

/-- **At the image of `⊤` the restriction-adjunction unit is the identity.** The sections of
`A|_X` over `⊤` are the sections of `𝒜` over `f ''ᵁ ⊤`; this says that reading a section of `𝒜`
over `f ''ᵁ ⊤` as a global section of `A|_X`, carrying it through the unit, and restoring the open
by `f ⁻¹ᵁ (f ''ᵁ ⊤) = ⊤` returns it unchanged.

Both maps involved are restriction maps of `𝒜` between its sections over `f ''ᵁ ⊤` and over
`f ''ᵁ (f ⁻¹ᵁ (f ''ᵁ ⊤))`, so their composite is a morphism of `(Opens S)ᵒᵖ` from `f ''ᵁ ⊤` to
itself, and the category of opens is thin. The equality of opens is an argument rather than a
rewrite; see the implementation notes. -/
theorem restrictUnit_image_top (n : ℤ)
    (hpre : (opensMap (ringedSpaceHom f)).obj (f ''ᵁ (⊤ : Opens X.toRingedSpace.carrier))
      = (⊤ : Opens X.toRingedSpace.carrier))
    (a : ((situationAlgebra A).piece n).val.obj
      (op (f ''ᵁ (⊤ : Opens X.toRingedSpace.carrier)))) :
    ((situationAlgebra (A.restrict f)).piece n).val.restrictₛₗ (eqToHom (congrArg op hpre))
        (restrictUnit A f n (f ''ᵁ (⊤ : Opens X.toRingedSpace.carrier)) a) = a := by
  exact (restrictₛₗ_restrictₛₗ_apply_of_subsingleton ((situationAlgebra A).piece n).val
    (homOfLE (f.image_preimage_le (f ''ᵁ (⊤ : Opens X.toRingedSpace.carrier)))).op
    (homOfLE (f.image_mono
      (le_of_eq (f.preimage_image_eq (⊤ : Opens X.toRingedSpace.carrier)).symm))).op
    (𝟙 _) a).trans (by rw [PresheafOfModules.restrictₛₗ_apply]; simp)

end Restrict

/-- The preimage of the image of `⊤` under an open immersion `V.ι` is `⊤`. -/
private theorem preimage_image_top_eq {S : Scheme.{u}} (V : S.Opens) :
    (opensMap (ringedSpaceHom V.ι)).obj (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier))
      = (⊤ : Opens V.toScheme.toRingedSpace.carrier) :=
  V.ι.preimage_image_eq _

section Chart

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (V : S.Opens) {k : ℤ} {T : Scheme.{u}}
  (gV : T ⟶ V.toScheme)
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- **The transported `ψ` of a chart-wise class, on sections — the computation
`...RelativeProjQcohSheaf.Fd.chartClass_mk` is the unfolding of.** For a quadruple for `𝒜` over
`g_V ≫ V.ι : T ⟶ V ⟶ S`, the map `ψ` of the chart-wise class — `ψ` base-changed along `V.ι` by
[Stacks, Tag 01NT] and then transported along the inverse comparison of the two spellings of the
restriction — transposed over the preimage `V.ι ⁻¹ᵁ W`, at the restriction-adjunction unit image
of a section `a` of `𝒜_{nd}` over an open `W` of `S`, is the **original** `ψ` transposed over `W`
at `a`.

In this shape the inverse comparison is the only inverse that occurs and
`unitalHomInverse_restrictPullbackUnitalHom_app` removes it; what is left is the transport across
the unital homomorphism (`Twisting.algebraTransport_sectionHom`) and the base change
(`Twisting.baseChangeUp_sectionHom`), each of which is one naturality of the pullback unit. -/
theorem chartTwisting_sectionHom (ψ : Twisting (gV ≫ V.ι) (situationAlgebra A) k L) (n : ℤ)
    (W : Opens S.toRingedSpace.carrier)
    (a : ((situationAlgebra A).piece (n * k)).val.obj (op W)) :
    (Twisting.algebraTransport
          (unitalHomInverse (restrictPullbackUnitalHom A V.ι)
            (isIso_restrictPullbackUnitalHom_app_forall A V.ι))
          (ψ.baseChangeDown V.ι gV (situationAlgebra A) k)).sectionHom n
        (op ((opensMap (ringedSpaceHom V.ι)).obj W))
        (restrictUnit A V.ι (n * k) W a)
      = ψ.sectionHom n (op W) a :=
  (Twisting.algebraTransport_sectionHom _ (ψ.baseChangeDown V.ι gV (situationAlgebra A) k) n
        (op ((opensMap (ringedSpaceHom V.ι)).obj W)) (restrictUnit A V.ι (n * k) W a)).trans
    ((congrArg
          (fun z : ((baseAlgebra V.ι (situationAlgebra A)).piece (n * k)).val.obj
              (op ((opensMap (ringedSpaceHom V.ι)).obj W)) =>
            (ψ.baseChangeDown V.ι gV (situationAlgebra A) k).sectionHom n
              (op ((opensMap (ringedSpaceHom V.ι)).obj W)) z)
          (unitalHomInverse_restrictPullbackUnitalHom_app A V.ι (n * k) W a)).trans
      ((Twisting.baseChangeUp_sectionHom V.ι gV (situationAlgebra A) k
            (ψ.baseChangeDown V.ι gV (situationAlgebra A) k) n (op W) a).symm.trans
        (congrArg
          (fun χ : Twisting (gV ≫ V.ι) (situationAlgebra A) k L => χ.sectionHom n (op W) a)
          (Twisting.baseChangeUp_baseChangeDown V.ι gV (situationAlgebra A) k ψ))))

/-- **The transported `ψ` of a chart-wise class, on global sections of the chart's algebra.** A
global section of `(A|_V)_{nd}` *is* a section of `𝒜_{nd}` over `V.ι ''ᵁ ⊤`, and this says the
chart-wise map `ψ` sends it to the original `ψ` transposed over that open, read across the
identification of the two opens `(g_V ≫ V.ι) ⁻¹ᵁ (V.ι ''ᵁ ⊤) = ⊤` of `T`.

This is `chartTwisting_sectionHom` at `W = V.ι ''ᵁ ⊤`, where `restrictUnit_image_top` makes the
unit image disappear, composed with the restriction `Twisting.globalSectionHom` carries. The
restriction morphism on `T` is an argument: all choices agree, the category of opens being thin,
and `top_le_preimage_image_top` supplies one. -/
theorem chartTwisting_globalSectionHom (ψ : Twisting (gV ≫ V.ι) (situationAlgebra A) k L) (n : ℤ)
    (a : ((situationAlgebra (A.restrict V.ι)).piece (n * k)).val.obj
      (op (⊤ : Opens V.toScheme.toRingedSpace.carrier)))
    (e : (op ((opensMap (ringedSpaceHom (gV ≫ V.ι))).obj
            (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)))
          : (Opens T.toRingedSpace.carrier)ᵒᵖ) ⟶ op (⊤ : Opens T.toRingedSpace.carrier)) :
    (Twisting.algebraTransport
          (unitalHomInverse (restrictPullbackUnitalHom A V.ι)
            (isIso_restrictPullbackUnitalHom_app_forall A V.ι))
          (ψ.baseChangeDown V.ι gV (situationAlgebra A) k)).globalSectionHom n a
      = ((laurent L).piece n).val.restrictₛₗ e
          (ψ.sectionHom n (op (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier))) a) := by
  have hpre := preimage_image_top_eq V
  have h1 := Twisting.sectionHom_restrict
    (Twisting.algebraTransport
      (unitalHomInverse (restrictPullbackUnitalHom A V.ι)
        (isIso_restrictPullbackUnitalHom_app_forall A V.ι))
      (ψ.baseChangeDown V.ι gV (situationAlgebra A) k)) n
    (eqToHom (congrArg op hpre))
    (restrictUnit A V.ι (n * k) (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)) a)
  rw [restrictUnit_image_top A V.ι (n * k) hpre a,
    chartTwisting_sectionHom A V gV ψ n
      (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)) a] at h1
  rw [Twisting.globalSectionHom_apply, h1]
  exact (restrictₛₗ_restrictₛₗ_apply_of_subsingleton ((laurent L).piece n).val _ _ e _)

end Chart

section Veronese

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (V : S.Opens) {k : ℕ} {T : Scheme.{u}}
  (gV : T ⟶ V.toScheme) {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-- **The Veronese family of a chart-wise class.** The datum `ψ` of a triple of Section 01N4
attached to the chart-wise class of a quadruple for `𝒜` evaluates, on a homogeneous element of
degree `nd` of the graded ring of global sections of `A|_V`, to the original quadruple's
transposed map over the open `V.ι ''ᵁ ⊤`, read through the comparison `L ^⊗ n ≅ L^{⊗ n}` of
[Stacks, Tag 01CU] and the identification of the two opens of `T`. -/
theorem veroneseSections_chartTwisting
    (ψ : Twisting (gV ≫ V.ι) (situationAlgebra A) (k : ℤ) L) (n : ℕ)
    (a : (A.restrict V.ι).grading (⊤ : V.toScheme.Opens) (n * k))
    (e : (op ((opensMap (ringedSpaceHom (gV ≫ V.ι))).obj
            (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)))
          : (Opens T.toRingedSpace.carrier)ᵒᵖ) ⟶ op (⊤ : Opens T.toRingedSpace.carrier)) :
    (veroneseSections (Twisting.algebraTransport
          (unitalHomInverse (restrictPullbackUnitalHom A V.ι)
            (isIso_restrictPullbackUnitalHom_app_forall A V.ι))
          (ψ.baseChangeDown V.ι gV (situationAlgebra A) (k : ℤ)))).toFun n a
      = (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L n).inv.app ⊤
          (((laurent L).piece (n : ℤ)).val.restrictₛₗ e
            (ψ.sectionHom (n : ℤ)
              (op (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)))
              ((a : (A.restrict V.ι).sectionRing (⊤ : V.toScheme.Opens)) (n * k)))) :=
  congrArg (fun z => (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L n).inv.app ⊤ z)
    (chartTwisting_globalSectionHom A V gV ψ (n : ℤ)
      ((a : (A.restrict V.ι).sectionRing (⊤ : V.toScheme.Opens)) (n * k)) e)

/-- **The test scheme is contained in the preimage of the image of `⊤`.** An equality in fact:
`g_V ≫ V.ι` factors through `V`, so the preimage of `V.ι ''ᵁ ⊤` is all of `T`. This supplies the
restriction morphism that `chartTwisting_globalSectionHom` and
`veroneseSections_chartTwisting` take as an argument. -/
theorem top_le_preimage_image_top :
    (⊤ : Opens T.toRingedSpace.carrier) ≤
      (opensMap (ringedSpaceHom (gV ≫ V.ι))).obj
        (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)) := by
  have hpre := preimage_image_top_eq V
  refine le_of_eq ?_
  rw [show (opensMap (ringedSpaceHom (gV ≫ V.ι))).obj
        (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier))
      = (opensMap (ringedSpaceHom gV)).obj
        ((opensMap (ringedSpaceHom V.ι)).obj
          (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier))) from rfl, hpre]
  exact (Twisting.preimage_top gV).symm

/-- **The transposed map of a quadruple commutes with the restriction of the graded ring of
sections.** `...RelativeProjBridge.SheafGradedAlgebra.resPiece` is the restriction map of `𝒜` on
homogeneous sections, so this is `Twisting.sectionHom_restrict` read on the graded ring of
[Stacks, Tag 01NN].

It is the computational half of the comparison of two charts: the graded ring homomorphism that
`...ProjChartGradedClassifying.comapVeronese` pulls a Veronese family back along, in the
hypothesis of `...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_comp_projInclusionMap`, is
`...SheafGradedAlgebra.res`, which acts degreewise by `resPiece`. -/
theorem sectionHom_resPiece {g : T ⟶ S} (ψ : Twisting g (situationAlgebra A) (k : ℤ) L) (n : ℕ)
    {W W' : S.Opens} (h : W' ≤ W) (a : A.sectionPieces W (n * k)) :
    ψ.sectionHom (n : ℤ) (op W') (A.resPiece h (n * k) a)
      = ((laurent L).piece (n : ℤ)).val.restrictₛₗ
          ((opensMap (ringedSpaceHom g)).op.map (homOfLE h).op)
          (ψ.sectionHom (n : ℤ) (op W) a) :=
  Twisting.sectionHom_restrict ψ (n : ℤ) (homOfLE h).op a

end Veronese

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
