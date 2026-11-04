module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectObjectsTransitionBridge

/-!
# Carrying the inductive hypotheses of Stacks 09RJ between two stages

`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean` is the
elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ.  It is run
at a stage of the system and needs the two inductive hypotheses `αU`, `αV` **at that stage**, while
the comparison isomorphism Stacks 09RI produces is found at a stage of its own choosing.  This is
the source's "after increasing `i` we can find an isomorphism": the inductive hypotheses have to be
carried to the stage the comparison was found at, and because
`AlgebraicGeometry.Space.edsBridgeFst` is *built from* `αU`, carrying `αU` changes it and the
change has to be shown to cancel.

`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectObjectsTransitionBridge.lean` has the
geometry and the algebra of that move: the composition comparisons
`AlgebraicGeometry.Space.edsTransitionOpenComp` and `…edsTransitionEtaleComp` that carry a
hypothesis from one stage to another, the stage-independent square isomorphisms
`…edsTransitionOpenSquare` and `…edsTransitionEtaleSquare` over the projection `s`, the pasting
coherences `…edsTransitionOpenSquare_prism` and `…edsTransitionEtaleSquare_prism`, and the
cancellation algebra.  What it could not state is the pasting coherence **in the spelling the
bridge's definitions are written in**.

**This file performs that respelling and runs the cancellation.**  The move is then immediate: `α`
and `β` factor through the stage-independent square isomorphism over `s` with everything
stage-dependent collected into one factor, the factorisation does not see which stage that factor
came from, and the square step becomes available with its inductive hypotheses at one stage and its
comparison at another.

## The respelling, and what made it expensive

`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism` and the bridge's definitions
write the same five morphisms two ways: the prism writes the components `e.hom.app M` of the
natural isomorphisms, the bridge writes the isomorphisms `(e.app M).hom` at the objects, and
`CategoryTheory.Iso.app_hom` identifies them.  Thirteen crossings between the two spellings are
already in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectObjectsTransitionBridge.lean`, and
assembling the respelling from them by `AlgebraicGeometry.Space.eq_comp₃_comp₂_congr` does not pass
the kernel: it takes **2,460,000** heartbeats over the open subspace and
**2,455,478** over the étale algebraic space, both ending in `(kernel) deterministic timeout`.

The cost is **not** the mismatch of object spellings, `CategoryTheory.Functor.comp_obj`.  Each such
crossing, taken in isolation, costs about 1,000 heartbeats, whether it is one
`…comp_obj`, two, or one together with the unfolding of an abbreviation; and a congruence lemma
whose nine functors are free variables, so that every `…comp_obj` is discharged once at the free
level and by instantiation afterwards, changes the total by nothing (**2,455,236**).  Measuring one
factor at a time locates the whole cost in two of the five: **2,387,223** for the composition
comparison of the intersections, **610,418** for the square isomorphism of the face over `q'`, and
about 3,000 each for the other three.

What those two have in common is that `…squareIso_prism`, instantiated, writes their object
argument **out** — `(smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq pb p q hq)).obj
Ab` — where the crossings of the bridge write the abbreviation
`AlgebraicGeometry.Space.edsBridgeOpenObj` for it.  So the kernel is asked to compare two
components of one natural transformation whose object arguments differ by one unfolding of an
abbreviation, and on these objects it does not take the cheap route: the comparison of
`e.hom.app (edsBridgeOpenObj hsq pb p q hq Ab)` with `e.hom.app ((…).obj Ab)` alone costs
**609,649** and does not finish.  **The same two crossings stated with the object written out as
the prism writes it cost 40,664 and 35,875**, and with them the respelling passes the kernel at
**46,032** and **46,034**.  That is the whole content of the first two sections below: not new
mathematics, but the five crossings written at one spelling of the object.

## Main results

* `AlgebraicGeometry.Space.edsTransitionOpenSquare_prism_bridged` and
  `…edsTransitionEtaleSquare_prism_bridged`: **the pasting coherence in the spelling of the
  bridge.**
* `AlgebraicGeometry.Space.edsBridgeFst_eq` and `…edsBridgeSnd_eq`: **`α` and `β` factor through
  the stage-independent square isomorphism over `s`**, with all the stage-dependence in the single
  factor `AlgebraicGeometry.Space.edsTransitionOpenComp`, respectively `…edsTransitionEtaleComp`.
* `AlgebraicGeometry.Space.edsBridgeFst_edsTransitionOpenComp` and
  `…edsBridgeSnd_edsTransitionEtaleComp`: **the invariance.**  `α` built at one stage from an
  inductive hypothesis carried there from another is the `α` of the other stage.
* `AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom_of_stage`:
  **the square step with its inductive hypotheses at one stage and its comparison at another.**
  Given `αU`, `αV` at a stage `(p₁, q₁, q₁')` and the comparison `c` with the hom-level equation of
  Stacks 09RI at a stage `(p₂, q₂, q₂')`, there is a **perfect** object `F` of `D(𝒪_{W₂})`
  restricting to the two objects and with `Lq₂'^*F ≅ E`.

## The hypotheses carried, and why each is an input rather than part of the conclusion

*`hsq`, `pb`, `p₁`, `p₂`, `p'`, `q₁`, `q₂`, `q₁'`, `q₂'`, `hq₁`, `hq₂`, `hq₁'`, `hq₂'`, `s`,
`hs₁`, `hs₂`, `hsp`: the geometry of Situation 09RH at the square, at two stages.*  In this
parametrisation a stage is a triple `(p, q, q')` factoring the *fixed* projection
`s : W' ⟶ W_b`, and the base stage `p_b`, the limit `p'`, the projection `s` and the two descended
objects are the same at both.  So the move needs **no morphism between the two stages** and no
comparison of the two factorisations: both restrictions of `A_b` are compared with its single
restriction along `s`, by the composition comparison of the pseudofunctoriality datum.  In
particular the two stages need not be comparable in the index.

*`Ab`, `Bb`, `E`, `αU`, `αV`, `hA`, `hBo`, `c`: the inductive hypotheses of Stacks 08GP and the
output of Stacks 09RI.*  Unchanged from
`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom`, except that
`αU` and `αV` are taken at the first stage and `c`, `hA`, `hBo` at the second; see "The hypotheses
carried" in the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean`.

No `Prop` binder stands in for missing mathematics, and no coherence of the pseudofunctoriality
datum is assumed: the one coherence used,
`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism`, is a theorem about the
fields of `AlgebraicGeometry.Space.DerivedPullbackComposition`, whose associativity coherence
`iso_assoc` is a field of the structure.

## What is not here

*The induction of Stacks 08GP and the affine base case.*  Running the induction needs, besides the
square step in the form below, the base change of Situation 09RH along an arbitrary quasi-compact
quasi-separated algebraic space étale over `X₀`, the colimit statement of Stacks 09RI for the
resulting system of intersections, and the transport of the affine base case to the chart; none is
assumed below.

*Stacks 09RI.*  Nothing below mentions a system, a colimit or a
`AlgebraicGeometry.Space.DescentSituation.RingModel`; the pair `(c, hfac)` is an argument.

## Implementation notes

Every crossing between the two spellings is its own declaration, with its natural isomorphism and
its object written out, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssSurjSquareStepBridged.lean`, and
**with the object argument spelled as
`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism` spells it** — written out
rather than as the bridge's abbreviation — which is what makes the respelling affordable; see
"The respelling, and what made it expensive".

The assembly is `AlgebraicGeometry.Space.eq_comp₃_comp₂_congr_prism`, whose six categories, nine
functors and one object are free variables, so that no composite of comparisons of total left
derived functors is traversed and each mismatch of object spellings is discharged once, at the free
level.  The variable blocks are scoped as tightly as the declarations allow, because a `variable`
block is elaborated once per declaration that draws on it and this one is expensive: holding `E`,
`αU` and `αV` in it costs about 13,400 heartbeats a declaration, which is why `αU` and `αV` are
binders of the declarations that use them rather than variables, and why the crossings and the
pasting coherences are in a section that does not see them.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 75.10.8 (Tag 08HB)](https://stacks.math.columbia.edu/tag/08HB)
* [Stacks Project, Lemma 75.9.1 (Tag 08GN)](https://stacks.math.columbia.edu/tag/08GN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

/-! ### The assembly, at free functors

The one declaration of this section is about free isomorphisms of free functors between free
categories.  Both spellings of each of the five objects of the pasting coherence are written out in
its statement, so that the mismatches of object spellings are discharged here, once, where the
functors are variables, and by instantiation afterwards.  See "Implementation notes". -/

/-- **Rewriting all five factors of an equation between a threefold and a twofold composite, at
the two spellings of each object.**  The five equations come **before** the equation being
rewritten, so that the conclusion is in their spelling; and each object is written both as a
composite of derived pullbacks applied to an object and as the composite functor applied to it, so
that the hypotheses may be stated in either spelling and the equation rewritten in the other. -/
theorem eq_comp₃_comp₂_congr_prism
    {A Pk Un Pn U V : Type*} [Category A] [Category Pk] [Category Un] [Category Pn]
      [Category U] [Category V]
    (tU : A ⥤ Un) (fstb : A ⥤ Pk) (tP : Pk ⥤ Pn) (fstp : Un ⥤ Pn)
    (rP : Pn ⥤ V) (sP : Pk ⥤ V) (rU : Un ⥤ U) (sU : A ⥤ U) (fstp' : U ⥤ V) (M : A)
    {f₁ : rP.obj (fstp.obj (tU.obj M)) ⟶ rP.obj (tP.obj (fstb.obj M))}
    {f₁' : rP.obj ((tU ⋙ fstp).obj M) ⟶ rP.obj ((fstb ⋙ tP).obj M)}
    {f₂ f₂' : (tP ⋙ rP).obj (fstb.obj M) ⟶ sP.obj (fstb.obj M)}
    {f₃ : sP.obj (fstb.obj M) ⟶ fstp'.obj (sU.obj M)}
    {f₃' : (fstb ⋙ sP).obj M ⟶ (sU ⋙ fstp').obj M}
    {g₁ : rP.obj (fstp.obj (tU.obj M)) ⟶ fstp'.obj (rU.obj (tU.obj M))}
    {g₁' : (fstp ⋙ rP).obj (tU.obj M) ⟶ (rU ⋙ fstp').obj (tU.obj M)}
    {g₂ : fstp'.obj (rU.obj (tU.obj M)) ⟶ fstp'.obj (sU.obj M)}
    {g₂' : fstp'.obj ((tU ⋙ rU).obj M) ⟶ fstp'.obj (sU.obj M)}
    (h₁ : f₁ = f₁') (h₂ : f₂ = f₂') (h₃ : f₃ = f₃') (h₄ : g₁ = g₁') (h₅ : g₂ = g₂')
    (h : f₁' ≫ f₂' ≫ f₃' = g₁' ≫ g₂') :
    f₁ ≫ f₂ ≫ f₃ = g₁ ≫ g₂ := by
  rw [h₁, h₂, h₃, h₄, h₅]
  exact h

section OneStage

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {Wb W W' : AlgebraicSpaces B S hS} (pb : Wb ⟶ W₀) (p : W ⟶ W₀) (p' : W' ⟶ W₀)
  (q : W ⟶ Wb) (q' : W' ⟶ W) (hq : q ≫ pb = p) (hq' : q' ≫ p = p')
  (s : W' ⟶ Wb) (hs : s = q' ≫ q) (hsp : s ≫ pb = p')
  (Ab : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsOpen B S hS (edsPreimage hsq pb)))))
  (Bb : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsEtale B S hS (edsPreimage hsq pb)))))

/-! ### The two crossings that have to be restated at the prism's spelling of the object -/

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeInterComp` at the object over the open
subspace, with that object written out as
`AlgebraicGeometry.Space.DerivedPullbackComposition.squareIso_prism` writes it rather than as
`AlgebraicGeometry.Space.edsBridgeInterOpenObj`. -/
theorem edsBridgeInterComp_hom_eq_open_obj :
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
        (edsBridgeInterOpenObj hsq pb Ab)).hom =
      ((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
          (edsPreimageInterMap hsq pb p' s hsp)
          (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app
        ((smallEtaleDerivedModulePullback B S hS
          (edsFst B S hS (edsPreimage hsq pb))).obj Ab) :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p' s hsp)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s hs hsp))
    ((smallEtaleDerivedModulePullback B S hS
      (edsFst B S hS (edsPreimage hsq pb))).obj Ab)

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeInterComp` at the object over the étale
algebraic space, with that object written out as the prism writes it. -/
theorem edsBridgeInterComp_hom_eq_etale_obj :
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
        (edsBridgeInterEtaleObj hsq pb Bb)).hom =
      ((DerivedPullbackComposition.canonical B S hS).iso
          (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
          (edsPreimageInterMap hsq pb p' s hsp)
          (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s
            hs hsp)).hom.app
        ((smallEtaleDerivedModulePullback B S hS
          (edsSnd B S hS (edsPreimage hsq pb))).obj Bb) :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).iso
    (edsPreimageInterMap hsq p p' q' hq') (edsPreimageInterMap hsq pb p q hq)
    (edsPreimageInterMap hsq pb p' s hsp)
    (edsPreimageInterMap_comp_edsPreimageInterMap hsq pb p p' q q' hq hq' s hs hsp))
    ((smallEtaleDerivedModulePullback B S hS
      (edsSnd B S hS (edsPreimage hsq pb))).obj Bb)

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeOpenSquare'`, with its object written out
as the prism writes it rather than as `AlgebraicGeometry.Space.edsBridgeOpenObj`. -/
theorem edsBridgeOpenSquare'_hom_obj :
    (edsBridgeOpenSquare' hsq pb p p' q q' hq hq' Ab).hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq p p' q' hq')
          (edsPreimageInterMap hsq p p' q' hq') (edsFst B S hS (edsPreimage hsq p))
          (edsFst_comp_edsPreimageOpenMap hsq p p' q' hq')).hom.app
        ((smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq pb p q hq)).obj Ab) :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq p p' q' hq')
    (edsPreimageInterMap hsq p p' q' hq') (edsFst B S hS (edsPreimage hsq p))
    (edsFst_comp_edsPreimageOpenMap hsq p p' q' hq'))
    ((smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq pb p q hq)).obj Ab)

/-- The crossing for `AlgebraicGeometry.Space.edsBridgeEtaleSquare'`, with its object written out
as the prism writes it. -/
theorem edsBridgeEtaleSquare'_hom_obj :
    (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb).hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q' hq')
          (edsPreimageInterMap hsq p p' q' hq') (edsSnd B S hS (edsPreimage hsq p))
          (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq')).hom.app
        ((smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq pb p q hq)).obj Bb) :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q' hq')
    (edsPreimageInterMap hsq p p' q' hq') (edsSnd B S hS (edsPreimage hsq p))
    (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq'))
    ((smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq pb p q hq)).obj Bb)

/-! ### The pasting coherence, in the spelling of the bridge -/

/-- **The two faces of the cube over `q` and over `q'` through the open subspace paste to the face
over `s`**, with every factor written as the bridge's definitions write it.  This is
`AlgebraicGeometry.Space.edsTransitionOpenSquare_prism` crossed into that spelling, and it is the
hypothesis `AlgebraicGeometry.Space.edsTransitionConj₄` takes. -/
theorem edsTransitionOpenSquare_prism_bridged :
    ((smallEtaleDerivedModulePullback B S hS
          (edsPreimageInterMap hsq p p' q' hq')).mapIso
        (edsBridgeOpenSquare hsq pb p q hq Ab)).inv ≫
      ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
        (edsBridgeInterOpenObj hsq pb Ab)).hom ≫
      (edsTransitionOpenSquare hsq pb p' s hsp Ab).hom =
    (edsBridgeOpenSquare' hsq pb p p' q q' hq hq' Ab).hom ≫
      ((smallEtaleDerivedModulePullback B S hS
        (edsFst B S hS (edsPreimage hsq p'))).mapIso
          (edsTransitionOpenComp hsq pb p p' q q' hq hq' s hs hsp Ab)).hom :=
  eq_comp₃_comp₂_congr_prism
    (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq pb p q hq))
    (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq pb)))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq))
    (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p)))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq'))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p' s hsp))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p p' q' hq'))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq pb p' s hsp))
    (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p')))
    Ab
    (edsBridgeOpenSquare_mapIso_inv_eq hsq pb p p' q q' hq hq' Ab)
    (edsBridgeInterComp_hom_eq_open_obj hsq pb p p' q q' hq hq' s hs hsp Ab)
    (edsTransitionOpenSquare_hom_eq hsq pb p' s hsp Ab)
    (edsBridgeOpenSquare'_hom_obj hsq pb p p' q q' hq hq' Ab)
    (edsTransitionOpenComp_mapIso_hom_eq hsq pb p p' q q' hq hq' s hs hsp Ab)
    (edsTransitionOpenSquare_prism hsq pb p p' q q' hq hq' s hs hsp Ab)

/-- **The two faces of the cube over `q` and over `q'` through the étale algebraic space paste to
the face over `s`**, with every factor written as the bridge's definitions write it.  This is the
hypothesis `AlgebraicGeometry.Space.edsTransitionConj₅` takes. -/
theorem edsTransitionEtaleSquare_prism_bridged :
    ((smallEtaleDerivedModulePullback B S hS
          (edsPreimageInterMap hsq p p' q' hq')).mapIso
        (edsBridgeEtaleSquare hsq pb p q hq Bb)).inv ≫
      ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
        (edsBridgeInterEtaleObj hsq pb Bb)).hom ≫
      (edsTransitionEtaleSquare hsq pb p' s hsp Bb).hom =
    (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb).hom ≫
      ((smallEtaleDerivedModulePullback B S hS
        (edsSnd B S hS (edsPreimage hsq p'))).mapIso
          (edsTransitionEtaleComp hsq pb p p' q q' hq hq' s hs hsp Bb)).hom :=
  eq_comp₃_comp₂_congr_prism
    (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq pb p q hq))
    (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq pb)))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq))
    (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p)))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq p p' q' hq'))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p' s hsp))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p p' q' hq'))
    (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq pb p' s hsp))
    (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p')))
    Bb
    (edsBridgeEtaleSquare_mapIso_inv_eq hsq pb p p' q q' hq hq' Bb)
    (edsBridgeInterComp_hom_eq_etale_obj hsq pb p p' q q' hq hq' s hs hsp Bb)
    (edsTransitionEtaleSquare_hom_eq hsq pb p' s hsp Bb)
    (edsBridgeEtaleSquare'_hom_obj hsq pb p p' q q' hq hq' Bb)
    (edsTransitionEtaleComp_mapIso_hom_eq hsq pb p p' q q' hq hq' s hs hsp Bb)
    (edsTransitionEtaleSquare_prism hsq pb p p' q q' hq hq' s hs hsp Bb)

/-! ### The factorisation of `α` and of `β` -/

variable (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))

/-- **`α` factors through the stage-independent square isomorphism over `s`**, with all its
dependence on the stage in the one factor
`AlgebraicGeometry.Space.edsTransitionOpenComp`.  This is
`AlgebraicGeometry.Space.edsTransitionConj₄` at the pasting coherence. -/
theorem edsBridgeFst_eq
    (αU : (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p p' q' hq')).obj
        (edsBridgeOpenObj hsq pb p q hq Ab) ≅
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS (edsPreimage hsq p'))).obj E) :
    edsBridgeFst hsq pb p p' q q' hq hq' s hs hsp Ab E αU =
      edsTransitionOpenSquare hsq pb p' s hsp Ab ≪≫
        ((smallEtaleDerivedModulePullback B S hS
          (edsFst B S hS (edsPreimage hsq p'))).mapIso
            (edsTransitionOpenComp hsq pb p p' q q' hq hq' s hs hsp Ab)).symm ≪≫
        (smallEtaleDerivedModulePullback B S hS
          (edsFst B S hS (edsPreimage hsq p'))).mapIso αU :=
  edsTransitionConj₄
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
      (edsBridgeInterOpenObj hsq pb Ab))
    ((smallEtaleDerivedModulePullback B S hS
      (edsPreimageInterMap hsq p p' q' hq')).mapIso (edsBridgeOpenSquare hsq pb p q hq Ab))
    (edsBridgeOpenSquare' hsq pb p p' q q' hq hq' Ab)
    ((smallEtaleDerivedModulePullback B S hS
      (edsFst B S hS (edsPreimage hsq p'))).mapIso αU)
    (edsTransitionOpenSquare hsq pb p' s hsp Ab)
    ((smallEtaleDerivedModulePullback B S hS
      (edsFst B S hS (edsPreimage hsq p'))).mapIso
        (edsTransitionOpenComp hsq pb p p' q q' hq hq' s hs hsp Ab))
    (edsTransitionOpenSquare_prism_bridged hsq pb p p' q q' hq hq' s hs hsp Ab)

/-- **`β` factors through the stage-independent square isomorphism over `s`**, with all its
dependence on the stage in the one factor
`AlgebraicGeometry.Space.edsTransitionEtaleComp`. -/
theorem edsBridgeSnd_eq
    (αV : (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p p' q' hq')).obj
        (edsBridgeEtaleObj hsq pb p q hq Bb) ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS (edsPreimage hsq p'))).obj E) :
    edsBridgeSnd hsq pb p p' q q' hq hq' s hs hsp Bb E αV =
      edsTransitionEtaleSquare hsq pb p' s hsp Bb ≪≫
        ((smallEtaleDerivedModulePullback B S hS
          (edsSnd B S hS (edsPreimage hsq p'))).mapIso
            (edsTransitionEtaleComp hsq pb p p' q q' hq hq' s hs hsp Bb)).symm ≪≫
        (smallEtaleDerivedModulePullback B S hS
          (edsSnd B S hS (edsPreimage hsq p'))).mapIso αV ≪≫
        (edsBridgeCartesianSquare hsq p' E).symm :=
  edsTransitionConj₅
    ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
      (edsBridgeInterEtaleObj hsq pb Bb))
    ((smallEtaleDerivedModulePullback B S hS
      (edsPreimageInterMap hsq p p' q' hq')).mapIso (edsBridgeEtaleSquare hsq pb p q hq Bb))
    (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb)
    ((smallEtaleDerivedModulePullback B S hS
      (edsSnd B S hS (edsPreimage hsq p'))).mapIso αV)
    (edsBridgeCartesianSquare hsq p' E).symm
    (edsTransitionEtaleSquare hsq pb p' s hsp Bb)
    ((smallEtaleDerivedModulePullback B S hS
      (edsSnd B S hS (edsPreimage hsq p'))).mapIso
        (edsTransitionEtaleComp hsq pb p p' q q' hq hq' s hs hsp Bb))
    (edsTransitionEtaleSquare_prism_bridged hsq pb p p' q q' hq hq' s hs hsp Bb)

end OneStage

/-! ### The invariance, and the square step with its data at two stages -/

section TwoStages

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {Wb W₁ W₂ W' : AlgebraicSpaces B S hS} (pb : Wb ⟶ W₀) (p₁ : W₁ ⟶ W₀) (p₂ : W₂ ⟶ W₀)
  (p' : W' ⟶ W₀) (q₁ : W₁ ⟶ Wb) (q₂ : W₂ ⟶ Wb) (q₁' : W' ⟶ W₁) (q₂' : W' ⟶ W₂)
  (hq₁ : q₁ ≫ pb = p₁) (hq₂ : q₂ ≫ pb = p₂) (hq₁' : q₁' ≫ p₁ = p') (hq₂' : q₂' ≫ p₂ = p')
  (s : W' ⟶ Wb) (hs₁ : s = q₁' ≫ q₁) (hs₂ : s = q₂' ≫ q₂) (hsp : s ≫ pb = p')
  (Ab : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsOpen B S hS (edsPreimage hsq pb)))))
  (Bb : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsEtale B S hS (edsPreimage hsq pb)))))
  (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))

/-- **The invariance of `α` under the move between stages, over the open subspace.**  The
inductive hypothesis at the second stage carried to the first by the two composition comparisons
builds the same `α` as the inductive hypothesis at the first: the two copies of the carried
comparison cancel against the one `AlgebraicGeometry.Space.edsBridgeFst` is built from. -/
theorem edsBridgeFst_edsTransitionOpenComp
    (αU : (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p₁ p' q₁' hq₁')).obj
        (edsBridgeOpenObj hsq pb p₁ q₁ hq₁ Ab) ≅
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS (edsPreimage hsq p'))).obj E) :
    edsBridgeFst hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Ab E
        (edsTransitionOpenComp hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Ab ≪≫
          (edsTransitionOpenComp hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Ab).symm ≪≫ αU) =
      edsBridgeFst hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Ab E αU :=
  (edsBridgeFst_eq hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Ab E _).trans
    ((edsTransitionNormalise₄
      (smallEtaleDerivedModulePullback B S hS (edsFst B S hS (edsPreimage hsq p')))
      (edsTransitionOpenSquare hsq pb p' s hsp Ab)
      (edsTransitionOpenComp hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Ab)
      (edsTransitionOpenComp hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Ab) αU).trans
      (edsBridgeFst_eq hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Ab E αU).symm)

/-- **The invariance of `β` under the move between stages, over the étale algebraic space.** -/
theorem edsBridgeSnd_edsTransitionEtaleComp
    (αV : (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p₁ p' q₁' hq₁')).obj
        (edsBridgeEtaleObj hsq pb p₁ q₁ hq₁ Bb) ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS (edsPreimage hsq p'))).obj E) :
    edsBridgeSnd hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Bb E
        (edsTransitionEtaleComp hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Bb ≪≫
          (edsTransitionEtaleComp hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Bb).symm ≪≫ αV) =
      edsBridgeSnd hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Bb E αV :=
  (edsBridgeSnd_eq hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Bb E _).trans
    ((edsTransitionNormalise₅
      (smallEtaleDerivedModulePullback B S hS (edsSnd B S hS (edsPreimage hsq p')))
      (edsTransitionEtaleSquare hsq pb p' s hsp Bb)
      (edsTransitionEtaleComp hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Bb)
      (edsTransitionEtaleComp hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Bb) αV
      (edsBridgeCartesianSquare hsq p' E).symm).trans
      (edsBridgeSnd_eq hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Bb E αV).symm)

/-- **The elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ,
with its inductive hypotheses at one stage and its comparison isomorphism at another.**

This is the source's "after increasing `i` we can find an isomorphism".  In the geometry of
Situation 09RH at an elementary distinguished square over `W₀` — a base stage `W_b`, two later
stages `W₁`, `W₂` and the limit `W'`, the triples `(p₁, q₁, q₁')` and `(p₂, q₂, q₂')` both
factoring the projection `s : W' ⟶ W_b` — let `A_b` and `Bo_b` be the objects descended over the
open subspace and over the étale algebraic space of the square at the base stage, let `αU`, `αV`
record that their restrictions **to the first stage** descend the two restrictions of `E`, let
their derived pullbacks **to the second stage** be perfect (`hA`, `hBo`), and let `c` be a
comparison isomorphism at the second stage whose image under the hom-level map of Stacks 09RI is
the comparison of the `α` and `β` built at the *first* stage (`hfac`).  Then there is a
**perfect** object `F` of `D(𝒪_{W₂})` with `F|_U ≅ A_b|_U`, `F|_V ≅ Bo_b|_V` and `Lq₂'^*F ≅ E`.

This is `AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom` with its
inductive hypotheses carried from the first stage to the second by
`AlgebraicGeometry.Space.edsTransitionOpenComp` and `…edsTransitionEtaleComp`, the change of
`AlgebraicGeometry.Space.edsBridgeFst` and `…edsBridgeSnd` cancelled by the two invariance lemmas
above, and `hfac` rewritten by `AlgebraicGeometry.Space.edsTransitionCompInvCongr`. -/
theorem exists_glue_isPerfect_derivedPullback_iso_of_factorHom_of_stage
    (c : (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p₂ q₂ hq₂)).obj
        (edsBridgeInterOpenObj hsq pb Ab) ≅
      (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p₂ q₂ hq₂)).obj
        (edsBridgeInterEtaleObj hsq pb Bb))
    (αU : (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p₁ p' q₁' hq₁')).obj
        (edsBridgeOpenObj hsq pb p₁ q₁ hq₁ Ab) ≅
      (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS (edsPreimage hsq p'))).obj E)
    (αV : (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p₁ p' q₁' hq₁')).obj
        (edsBridgeEtaleObj hsq pb p₁ q₁ hq₁ Bb) ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS (edsPreimage hsq p'))).obj E)
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS (edsPreimage hsq p₂)).1
      (edsOpen B S hS (edsPreimage hsq p₂)).2).IsPerfect (edsBridgeOpenObj hsq pb p₂ q₂ hq₂ Ab))
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS (edsPreimage hsq p₂)).1
      (edsEtale B S hS (edsPreimage hsq p₂)).2).IsPerfect (edsBridgeEtaleObj hsq pb p₂ q₂ hq₂ Bb))
    (hfac : ((edsBridgeInterComp hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp).app
            (edsBridgeInterOpenObj hsq pb Ab)).inv ≫
          (smallEtaleDerivedModulePullback B S hS
            (edsPreimageInterMap hsq p₂ p' q₂' hq₂')).map c.hom ≫
          ((edsBridgeInterComp hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp).app
            (edsBridgeInterEtaleObj hsq pb Bb)).hom =
      (edsBridgeFst hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Ab E αU).hom ≫
        (edsBridgeSnd hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Bb E αV).inv) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W₂)))
      (_ : (smallEtaleDerivedModulePullback B S hS
        (edsOpenHom B S hS (edsPreimage hsq p₂))).obj F ≅ edsBridgeOpenObj hsq pb p₂ q₂ hq₂ Ab)
      (_ : (smallEtaleDerivedModulePullback B S hS
        (edsEtaleHom B S hS (edsPreimage hsq p₂))).obj F ≅ edsBridgeEtaleObj hsq pb p₂ q₂ hq₂ Bb),
      (smallEtaleRingedSite B S hS W₂.1 W₂.2).IsPerfect F ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS q₂').obj F ≅ E) :=
  exists_glue_isPerfect_derivedPullback_iso_of_factorHom hsq pb p₂ p' q₂ q₂' hq₂ hq₂' Ab Bb E
    s hs₂ hsp c
    (edsTransitionOpenComp hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Ab ≪≫
      (edsTransitionOpenComp hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Ab).symm ≪≫ αU)
    (edsTransitionEtaleComp hsq pb p₂ p' q₂ q₂' hq₂ hq₂' s hs₂ hsp Bb ≪≫
      (edsTransitionEtaleComp hsq pb p₁ p' q₁ q₁' hq₁ hq₁' s hs₁ hsp Bb).symm ≪≫ αV)
    hA hBo
    (hfac.trans (edsTransitionCompInvCongr
      (edsBridgeFst_edsTransitionOpenComp hsq pb p₁ p₂ p' q₁ q₂ q₁' q₂' hq₁ hq₂ hq₁' hq₂' s
        hs₁ hs₂ hsp Ab E αU)
      (edsBridgeSnd_edsTransitionEtaleComp hsq pb p₁ p₂ p' q₁ q₂ q₁' q₂' hq₁ hq₂ hq₁' hq₂' s
        hs₁ hs₂ hsp Bb E αV)).symm)

end TwoStages

end AlgebraicGeometry.Space

end
