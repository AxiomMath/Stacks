module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectDescentBridgeOverlap

/-!
# The elementary-distinguished-square step of Stacks 09RJ, from the hom-level equation of 09RI

`AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage` is the
elementary-distinguished-square step of the essential surjectivity half of Stacks 09RJ, and
`AlgebraicGeometry.Space.hc_edsBridgeComparison_of_factorHom` produces that step's hypothesis
`hc` from the hom-level equation of Stacks 09RI.  The two are written in two spellings of the
same five morphisms: the step writes the components `e.hom.app M` of the five square
isomorphisms of the cube of Stacks 08GN, the bridge writes the isomorphisms `(e.app M).hom` at
the objects.  `CategoryTheory.Iso.app_hom` and `…Iso.app_inv` identify them.  This file
identifies the two spellings and composes the two statements.

## Main results

* `AlgebraicGeometry.Space.edsBridgeOpenSquare'_hom`,
  `…edsBridgeCartesianSquare_hom`, `…edsBridgeEtaleSquare'_inv`: the three respellings, one per
  factor that needs one.
* `AlgebraicGeometry.Space.exists_glue_isPerfect_derivedPullback_iso_of_factorHom`: **the square
  step with its comparison isomorphism produced by Stacks 09RI** — given the objects `A_b`,
  `Bo_b` at a base stage, the isomorphisms `αU`, `αV` at the two members of the square over the
  limit, a comparison `c` at the stage `W` of the step and the hom-level equation `hfac` for it,
  there is a **perfect** object `F` of `D(𝒪_W)` restricting to the two objects and with
  `Lq'^*F ≅ E`.
* `CategoryTheory.eq_comp₅_congr₃`: rewriting the first, third and fifth factors of a fivefold
  composite.

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

namespace CategoryTheory

/-- **Rewriting the first, third and fifth factors of a fivefold composite.** -/
theorem eq_comp₅_congr₃ {T : Type*} [Category* T] {a b c d e f : T}
    {t : a ⟶ f} {f₁ : a ⟶ b} {m₁ : b ⟶ c} {f₂ : c ⟶ d} {m₂ : d ⟶ e} {f₃ : e ⟶ f}
    (h : t = f₁ ≫ m₁ ≫ f₂ ≫ m₂ ≫ f₃)
    {f₁' : a ⟶ b} {f₂' : c ⟶ d} {f₃' : e ⟶ f}
    (h₁ : f₁ = f₁') (h₂ : f₂ = f₂') (h₃ : f₃ = f₃') :
    t = f₁' ≫ m₁ ≫ f₂' ≫ m₂ ≫ f₃' := by
  rwa [← h₁, ← h₂, ← h₃]

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {W₀ : AlgebraicSpaces B S hS} {V₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {U₀ : Subfunctor W₀.1} {f₀ : V₀ ⟶ W₀.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W₀.2 U₀ f₀)
  {Wb W W' : AlgebraicSpaces B S hS} (pb : Wb ⟶ W₀) (p : W ⟶ W₀) (p' : W' ⟶ W₀)
  (q : W ⟶ Wb) (q' : W' ⟶ W) (hq : q ≫ pb = p) (hq' : q' ≫ p = p')
  (Ab : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsOpen B S hS (edsPreimage hsq pb)))))
  (Bb : DerivedCategory (SheafOfModules.{u}
    (ringedToposStructureRingSheaf B S hS (edsEtale B S hS (edsPreimage hsq pb)))))
  (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W')))

/-! ### The three respellings -/

/-- The square isomorphism of the face of the cube over `q'` through the open subspace, at the
object, is the component of that square isomorphism. -/
theorem edsBridgeOpenSquare'_hom :
    (edsBridgeOpenSquare' hsq pb p p' q q' hq hq' Ab).hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq p p' q' hq')
          (edsPreimageInterMap hsq p p' q' hq') (edsFst B S hS (edsPreimage hsq p))
          (edsFst_comp_edsPreimageOpenMap hsq p p' q' hq')).hom.app
        (edsBridgeOpenObj hsq pb p q hq Ab) :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsFst B S hS (edsPreimage hsq p')) (edsPreimageOpenMap hsq p p' q' hq')
    (edsPreimageInterMap hsq p p' q' hq') (edsFst B S hS (edsPreimage hsq p))
    (edsFst_comp_edsPreimageOpenMap hsq p p' q' hq')) (edsBridgeOpenObj hsq pb p q hq Ab)

/-- The square isomorphism of the cartesian square of the square over `W'`, at `E`, is the
component of that square isomorphism. -/
theorem edsBridgeCartesianSquare_hom :
    (edsBridgeCartesianSquare hsq p' E).hom =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
        (edsSnd B S hS (edsPreimage hsq p')) (edsEtaleHom B S hS (edsPreimage hsq p'))
        (edsFst B S hS (edsPreimage hsq p')) (edsOpenHom B S hS (edsPreimage hsq p'))
        (isPullback_edsInter B S hS (edsPreimage hsq p')).flip.w).hom.app E :=
  Iso.app_hom ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p')) (edsEtaleHom B S hS (edsPreimage hsq p'))
    (edsFst B S hS (edsPreimage hsq p')) (edsOpenHom B S hS (edsPreimage hsq p'))
    (isPullback_edsInter B S hS (edsPreimage hsq p')).flip.w) E

/-- The inverse of the square isomorphism of the face of the cube over `q'` through the étale
algebraic space, at the object, is the component of that square isomorphism's inverse. -/
theorem edsBridgeEtaleSquare'_inv :
    (edsBridgeEtaleSquare' hsq pb p p' q q' hq hq' Bb).inv =
      ((DerivedPullbackComposition.canonical B S hS).squareIso
          (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q' hq')
          (edsPreimageInterMap hsq p p' q' hq') (edsSnd B S hS (edsPreimage hsq p))
          (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq')).inv.app
        (edsBridgeEtaleObj hsq pb p q hq Bb) :=
  Iso.app_inv ((DerivedPullbackComposition.canonical B S hS).squareIso
    (edsSnd B S hS (edsPreimage hsq p')) (edsPreimageEtaleMap hsq p p' q' hq')
    (edsPreimageInterMap hsq p p' q' hq') (edsSnd B S hS (edsPreimage hsq p))
    (edsSnd_comp_edsPreimageEtaleMap hsq p p' q' hq')) (edsBridgeEtaleObj hsq pb p q hq Bb)

/-! ### The square step with the comparison isomorphism of Stacks 09RI -/

variable (s : W' ⟶ Wb) (hs : s = q' ≫ q) (hsp : s ≫ pb = p')
  (c : (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq)).obj
      (edsBridgeInterOpenObj hsq pb Ab) ≅
    (smallEtaleDerivedModulePullback B S hS (edsPreimageInterMap hsq pb p q hq)).obj
      (edsBridgeInterEtaleObj hsq pb Bb))
  (αU : (smallEtaleDerivedModulePullback B S hS (edsPreimageOpenMap hsq p p' q' hq')).obj
      (edsBridgeOpenObj hsq pb p q hq Ab) ≅
    (smallEtaleDerivedModulePullback B S hS (edsOpenHom B S hS (edsPreimage hsq p'))).obj E)
  (αV : (smallEtaleDerivedModulePullback B S hS (edsPreimageEtaleMap hsq p p' q' hq')).obj
      (edsBridgeEtaleObj hsq pb p q hq Bb) ≅
    (smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS (edsPreimage hsq p'))).obj E)

include hs in
/-- **The elementary-distinguished-square step of the essential surjectivity half of
Stacks 09RJ, with its comparison isomorphism and its compatibility supplied by Stacks 09RI.**

In the geometry of Situation 09RH at an elementary distinguished square over `W₀` — a base stage
`W_b`, a later stage `W` and the limit `W'`, with `q : W ⟶ W_b`, `q' : W' ⟶ W` and the composite
projection `s : W' ⟶ W_b` — let `A_b` and `Bo_b` be the objects descended over the open subspace
and over the étale algebraic space of the square at the base stage, let their derived pullbacks
to the stage `W` be **perfect** (`hA`, `hBo`) and descend the two restrictions of `E` (`αU`,
`αV`), and let `c` be a comparison isomorphism at the stage `W` between their restrictions to
the intersection whose image under the hom-level map of Stacks 09RI is the comparison of `αU`
and `αV` (`hfac`).  Then there is a **perfect** object `F` of `D(𝒪_W)` with `F|_U ≅ A_b|_U`,
`F|_V ≅ Bo_b|_V` and `Lq'^*F ≅ E`. -/
theorem exists_glue_isPerfect_derivedPullback_iso_of_factorHom
    (hA : (smallEtaleRingedSite B S hS (edsOpen B S hS (edsPreimage hsq p)).1
      (edsOpen B S hS (edsPreimage hsq p)).2).IsPerfect (edsBridgeOpenObj hsq pb p q hq Ab))
    (hBo : (smallEtaleRingedSite B S hS (edsEtale B S hS (edsPreimage hsq p)).1
      (edsEtale B S hS (edsPreimage hsq p)).2).IsPerfect (edsBridgeEtaleObj hsq pb p q hq Bb))
    (hfac : ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
            (edsBridgeInterOpenObj hsq pb Ab)).inv ≫
          (smallEtaleDerivedModulePullback B S hS
            (edsPreimageInterMap hsq p p' q' hq')).map c.hom ≫
          ((edsBridgeInterComp hsq pb p p' q q' hq hq' s hs hsp).app
            (edsBridgeInterEtaleObj hsq pb Bb)).hom =
      (edsBridgeFst hsq pb p p' q q' hq hq' s hs hsp Ab E αU).hom ≫
        (edsBridgeSnd hsq pb p p' q q' hq hq' s hs hsp Bb E αV).inv) :
    ∃ (F : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)))
      (_ : (smallEtaleDerivedModulePullback B S hS
        (edsOpenHom B S hS (edsPreimage hsq p))).obj F ≅ edsBridgeOpenObj hsq pb p q hq Ab)
      (_ : (smallEtaleDerivedModulePullback B S hS
        (edsEtaleHom B S hS (edsPreimage hsq p))).obj F ≅ edsBridgeEtaleObj hsq pb p q hq Bb),
      (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect F ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS q').obj F ≅ E) :=
  have hc := hc_edsBridgeComparison_of_factorHom hsq pb p p' q q' hq hq' s hs hsp Ab Bb E c αU αV
    hfac
  exists_glue_isPerfect_derivedPullback_iso_of_edsPreimage hsq p p' q' hq' E
    (edsBridgeOpenObj hsq pb p q hq Ab) (edsBridgeEtaleObj hsq pb p q hq Bb) hA hBo αU αV
    (edsBridgeComparison hsq pb p q hq Ab Bb c)
    (eq_comp₅_congr₃ hc (edsBridgeOpenSquare'_hom hsq pb p p' q q' hq hq' Ab)
      (edsBridgeCartesianSquare_hom hsq p' E)
      (edsBridgeEtaleSquare'_inv hsq pb p p' q q' hq hq' Bb))

end AlgebraicGeometry.Space

end
