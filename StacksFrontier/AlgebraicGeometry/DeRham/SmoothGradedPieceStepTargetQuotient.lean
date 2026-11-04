module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepAssembly
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceTargetDegreewise
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite

/-!
# The target complex of Section 0FMK read into the quotient by the next step

`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` identifies the degree-`n` term of the `k`-th
graded piece of the filtration of `Ω^•_{X/S}` with the degree-`n` term of
`f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`, for `f` smooth and `n = k + 1 + m`. A
*differential* cannot be carried along that identification as it stands: the differential of a
graded piece is the differential of the step read modulo the next step, so it can only be checked
through the projection `CategoryTheory.FilteredObject.grMapπ`, which above the cut is merely an
epimorphism.

**This file reads the target side of that identification into the quotient
`Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`**, where the comparison of Section 0FMK is a *monomorphism*
(`AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsPullbackGradedQuotientHom`), and computes
the composite: it is the inclusion of the step `F^kΩ^n_{X/S}` into `Ω^n_{X/S}` followed by the
projection onto the quotient. That is the shape the wedge product and the Leibniz rule
`AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_cokernelπ_prodWedgeHomOfEq` are written in,
and a square above the cut may be checked after composing with the monomorphism.

It is the analogue above the cut of
`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom`, which does the same thing in
the degree of the cut; there the projection onto the graded piece is itself invertible and no
monomorphism is needed.

## Main definitions

* `Stacks.DeRhamSmooth.gradedTargetXToStepQuotient`: **the degree-`n` term of the target complex,
  read into `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`** — the degreewise comparison, the crossing of
  [Stacks, Tag 08DE] and Section 0FMK's comparison into the quotient.

## Main results

* `Stacks.CategoryTheory.isoTrans₄_hom_comp_inv₃_comp`: **cancelling a four-fold chain of
  isomorphisms against the inverses of its last three factors**, at generic objects.
* `Stacks.CategoryTheory.mono_map_of_mono`: a functor preserving monomorphisms carries one to one,
  with the monomorphy explicit.
* `Stacks.DeRhamSmooth.mono_gradedTargetXToStepQuotient`: **that reading is a monomorphism**, so a
  square above the cut may be checked after it.
* `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient`: the three inverted
  factors of the degreewise comparison cancel against it, leaving
  `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` and the inclusion of the sheaf-level graded
  piece.
* `Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient`: **the
  graded-piece side of the square above the cut, computed** — the projection followed by the
  comparison and the reading is the inclusion of the step followed by the quotient projection.

## Implementation notes

**The cancellation is a kernel problem as much as an elaboration problem**, and
`Stacks.CategoryTheory.isoTrans₄_hom_comp_inv₃_comp` is what solves it: every reassociation is
discharged once, by the elaborator, against a signature over an abstract category where the
objects are variables and there is nothing to unfold. This is the device of
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepAssembly`, whose implementation notes
record why: at these binders a directly written chain of `Eq.trans` under `whisker_eq` *elaborates*
and is then rejected by the kernel with a deterministic timeout.

**Nothing is rewritten.** `rw` and `simp` are refused at these binders — the goals are reported as
not type-correct at `implicit` transparency — so the one `CategoryTheory.Functor.map_comp` that
splits the last factor is applied as a term, in
`Stacks.DeRhamSmooth.gradedTargetXToStepQuotient_eq`.

**Monomorphy and invertibility are handed in, never searched for.** Two definitionally equal
category instances are in scope at these binders, and instance search finds neither `Mono q` for a
`q` whose monomorphy is in context nor `IsIso e.hom` for an honest isomorphism `e`. Both are
supplied through lemmas taking them as explicit hypotheses.

**The restriction of scalars appears under two spellings.**
`RingedSpaceModuleAdjunction.pushforward (Stacks.DeRhamDirectImage.toInverseImageBase (f ≫ g))`
is the one `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` is written with and
`SheafOfModules.restrictScalars (AlgebraicGeometry.SheafOfModules.underlyingRingHom)` the one the
assembly is written with; they agree by definition, and the statements below use whichever spelling
their own factors carry rather than transporting between them.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

universe u

namespace Stacks.CategoryTheory

variable {C : Type*} [_root_.CategoryTheory.Category C]

/-- **Cancelling a four-fold chain of isomorphisms against the inverses of its last three
factors.** For `e = e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄` and any `ρ` out of the target of `e₁`,

`e.hom ≫ e₄.inv ≫ e₃.inv ≫ e₂.inv ≫ ρ  =  e₁.hom ≫ ρ`.

This is the shape in which the degreewise comparison of [Stacks, Section 0FMK] meets the reading
of its own last three factors back into the quotient `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`: the comparison
is a right-nested `≪≫` whose last three factors are inverses, and the morphism into the quotient
is built from the three `hom`s in the opposite order, so all three cancel and only the first
factor survives.

Stated over an abstract category, which is the whole point: every reassociation is done here,
where the objects are variables, and not at the binders of the de Rham complex, where `rw` and
`simp` do not fire at all and where the *kernel* cannot afford the reassociation either. See the
implementation notes of `StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepAssembly`.

Costs 200 heartbeats against the default budget of 200,000. -/
theorem isoTrans₄_hom_comp_inv₃_comp {W X₀ Y₀ Z₀ T₀ U : C} (e₁ : W ≅ X₀) (e₂ : X₀ ≅ Y₀)
    (e₃ : Y₀ ≅ Z₀) (e₄ : Z₀ ≅ T₀) (ρ : X₀ ⟶ U) :
    (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄).hom ≫ e₄.inv ≫ e₃.inv ≫ e₂.inv ≫ ρ = e₁.hom ≫ ρ := by
  simp

/-- **A functor preserving monomorphisms carries a monomorphism to one**, with the monomorphy of
the argument an explicit hypothesis rather than an instance.

`CategoryTheory.Functor.map_mono` takes it as an instance, and at the binders of the de Rham
complex that is not enough: two definitionally equal category instances are in scope and instance
search does not find `Mono q` even for a `q` whose monomorphy is in context. This is the same
device, and for the same reason, as `Stacks.CategoryTheory.mono_comp_of_isIso` and
`Stacks.CategoryTheory.mono_comp_of_mono`.

Costs 70 heartbeats against the default budget of 200,000. -/
theorem mono_map_of_mono {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {D₁ : Type*}
    [_root_.CategoryTheory.Category D₁] (U : C₁ ⥤ D₁) [U.PreservesMonomorphisms] {P Q : C₁}
    (q : P ⟶ Q) (hq : Mono q) : Mono (U.map q) :=
  have := hq
  U.map_mono q

end Stacks.CategoryTheory

namespace Stacks.DeRhamSmooth

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The degree-`n` term of the target complex of [Stacks, Section 0FMK], read into the quotient
`Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`**, for `n = k + 1 + j` and `f` smooth: the degreewise comparison
`Stacks.DeRhamSmooth.gradedTargetXIso` of that term with
`f^{-1}Ω^k_{Y/S} ⊗_{f^{-1}𝒪_Y} Ω^{j+1}_{X/Y}`, the crossing
`Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso` back to the tensor product over
`𝒪_X`, and then
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom`, which is Section
0FMK's comparison followed by the inclusion of the graded piece into that quotient.

**This is the monomorphism a square above the cut may be checked after**
(`Stacks.DeRhamSmooth.mono_gradedTargetXToStepQuotient`), and it is the one that turns the graded
piece's side of the square into the inclusion of the step followed by a quotient projection
(`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient`) — the shape
the wedge product and the Leibniz rule are written in. It is the analogue above the cut of the
cancellation `Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom` performs in the
degree of the cut, where the projection onto the graded piece is itself invertible and no
monomorphism is needed.

The three factors are the last three of
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`, in the opposite order and inverted, which is
exactly why they cancel against it.

Costs 4,668 heartbeats against the default budget of 200,000. -/
def gradedTargetXToStepQuotient [Smooth f] (k j : ℕ) :
    (gradedTargetComplex f g k).X ((k + 1 + j : ℕ) : ℤ) ⟶
      (pushforward (toInverseImageBase (f ≫ g))).obj
        (cokernel (_root_.SheafOfModules.prodWedgeHom
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
          (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) :=
  (gradedTargetXIso f g k (j + 1) (k + 1 + j) (by omega)).hom ≫
    (gradedSourceMixedTensorCoefficientIso f g k
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j + 1 : ℕ) : ℤ))).hom ≫
      (pushforward (toInverseImageBase (f ≫ g))).map
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom f g k j)

/-- `Stacks.DeRhamSmooth.gradedTargetXToStepQuotient` with its last factor split in two along the
definition of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedQuotientHom` — Section 0FMK's
comparison, and the inclusion of the graded piece into the quotient — so that the comparison
stands alone and can be cancelled against the one inside
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX`.

One `CategoryTheory.Functor.map_comp`, applied as a term: at these binders `rw` does not fire.

Costs 12,836 heartbeats against the default budget of 200,000. -/
theorem gradedTargetXToStepQuotient_eq [Smooth f] (k j : ℕ) :
    gradedTargetXToStepQuotient f g k j =
      (gradedTargetXIso f g k (j + 1) (k + 1 + j) (by omega)).hom ≫
        (gradedSourceMixedTensorCoefficientIso f g k
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j + 1 : ℕ) : ℤ))).hom ≫
          ((pushforward (toInverseImageBase (f ≫ g))).map
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison
                f g k j) ≫
            (pushforward (toInverseImageBase (f ≫ g))).map
              (imageSubobject (_root_.SheafOfModules.exteriorGradedHom
                (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
                  (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
                (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
                  (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
                (Scheme.Hom.relativeDifferentialsShortComplex f g).f k j)).arrow) :=
  congrArg ((gradedTargetXIso f g k (j + 1) (k + 1 + j) (by omega)).hom ≫ ·)
    (congrArg ((gradedSourceMixedTensorCoefficientIso f g k
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j + 1 : ℕ) : ℤ))).hom ≫ ·)
      ((pushforward (toInverseImageBase (f ≫ g))).map_comp _ _))

/-- **The degreewise comparison of [Stacks, Section 0FMK] above the cut, read into the quotient
`Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`, is the comparison with the sheaf-level graded piece followed by that
piece's inclusion.** All three of the last factors of
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` — the pushforward of the inverse of Section
0FMK's comparison, the crossing of [Stacks, Tag 08DE] and the degreewise comparison of the target
complex — cancel against the three factors of
`Stacks.DeRhamSmooth.gradedTargetXToStepQuotient`, leaving
`Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` and the inclusion of `gr^kΩ^n_{X/S}` into the
quotient.

The cancellation itself happens at generic objects, in
`Stacks.CategoryTheory.isoTrans₄_hom_comp_inv₃_comp`; what is done here is only to split the last
factor and to name the four isomorphisms. Smoothness of `f` enters once, as the invertibility of
Section 0FMK's comparison
(`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsPullbackGradedComparison`), which is the
only hypothesis of `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX` as well.

Costs 66,211 heartbeats against the default budget of 200,000. -/
theorem gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient [Smooth f] (k j : ℕ) :
    (gradedPieceXIsoGradedTargetX f g k j).hom ≫ gradedTargetXToStepQuotient f g k j =
      (gradedPieceXIsoExteriorGraded f g k j).hom ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
          (imageSubobject (_root_.SheafOfModules.exteriorGradedHom
            (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
            (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
              (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
            (Scheme.Hom.relativeDifferentialsShortComplex f g).f k j)).arrow := by
  have := AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsPullbackGradedComparison
    f g k j
  exact (whisker_eq _ (gradedTargetXToStepQuotient_eq f g k j)).trans <|
    Stacks.CategoryTheory.isoTrans₄_hom_comp_inv₃_comp
    (gradedPieceXIsoExteriorGraded f g k j)
    ((pushforward (toInverseImageBase (f ≫ g))).mapIso
      (asIso (AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison
        f g k j)).symm)
    (gradedSourceMixedTensorCoefficientIso f g k
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j + 1 : ℕ) : ℤ))).symm
    (gradedTargetXIso f g k (j + 1) (k + 1 + j) (by omega)).symm
    ((pushforward (toInverseImageBase (f ≫ g))).map
      (imageSubobject (_root_.SheafOfModules.exteriorGradedHom
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
        (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
        (Scheme.Hom.relativeDifferentialsShortComplex f g).f k j)).arrow)

/-- **The reading of the target complex into the quotient `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}` is a
monomorphism**, so a square above the cut may be checked after composing with it. Two of its three
factors are isomorphisms and the third is the pushforward of
`AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsPullbackGradedQuotientHom`, restriction of
scalars preserving monomorphisms.

Every monomorphy and invertibility is handed in explicitly rather than left to instance search,
which at these binders does not find them; see
`Stacks.CategoryTheory.mono_map_of_mono`.

Costs 6,322 heartbeats against the default budget of 200,000. -/
theorem mono_gradedTargetXToStepQuotient [Smooth f] (k j : ℕ) :
    Mono (gradedTargetXToStepQuotient f g k j) :=
  Stacks.CategoryTheory.mono_comp_of_isIso _ _
    (Iso.isIso_hom (gradedTargetXIso f g k (j + 1) (k + 1 + j) (by omega)))
    (Stacks.CategoryTheory.mono_comp_of_isIso _ _
      (Iso.isIso_hom (gradedSourceMixedTensorCoefficientIso f g k
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((j + 1 : ℕ) : ℤ))))
      (Stacks.CategoryTheory.mono_map_of_mono (pushforward (toInverseImageBase (f ≫ g))) _
        (AlgebraicGeometry.Scheme.Hom.mono_relativeDifferentialsPullbackGradedQuotientHom
          f g k j)))

/-- **The square of [Stacks, Section 0FMK] above the cut, with its graded-piece side computed.**
The projection onto the degree-`n` term of the `k`-th graded piece, followed by the degreewise
comparison and the reading into the quotient `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`, is the inclusion of the
`k`-th step `F^kΩ^n_{X/S}` into `Ω^n_{X/S}` followed by that quotient's projection, `n = k+1+j`.

This is `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient` composed with
the assembly
`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoExteriorGraded_hom_comp_arrow`, and what it achieves
is the same thing above the cut that
`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom` achieves at the cut: **no
graded piece, no image subobject and no cokernel of an inclusion of steps survives on the right**,
only the comparison of the two presentations of the step, the inclusion of the step and the
projection onto the quotient by the next step.

Costs 72,619 heartbeats against the default budget of 200,000. -/
theorem grMapπ_f_gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient [Smooth f] (k j : ℕ) :
    (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
          (deRhamSmoothFiltration f g)).f ((k + 1 + j : ℕ) : ℤ) ≫
        (gradedPieceXIsoGradedTargetX f g k j).hom ≫ gradedTargetXToStepQuotient f g k j =
      stepXToExteriorFiltration f g k j ≫
        (_root_.SheafOfModules.restrictScalars.{u}
              (AlgebraicGeometry.SheafOfModules.underlyingRingHom
                (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map
            (Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + j) k).arrow ≫
          (_root_.SheafOfModules.restrictScalars.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHom
              (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map
            (cokernel.π (_root_.SheafOfModules.prodWedgeHom
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
                (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
                (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
                (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
              (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) j)) := by
  exact (whisker_eq _ (gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient f g k j)).trans
    (grMapπ_f_gradedPieceXIsoExteriorGraded_hom_comp_arrow f g k j)

end Stacks.DeRhamSmooth

end
