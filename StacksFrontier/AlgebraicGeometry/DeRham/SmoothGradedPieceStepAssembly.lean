module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepProjection
import StacksFrontier.AlgebraicGeometry.SheafifyMono.RestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor

/-!
# The degreewise comparison of Section 0FMK, read on the projection onto the graded piece

`Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` identifies the degree-`n` term of the `k`-th
graded piece of the filtration of `Ω^•_{X/S}` with the sheaf-level graded piece `gr^kΩ^n_{X/S}`,
`n = k + 1 + m`, as a composite of seven isomorphisms. Each of the seven comes with its own
compatibility with the quotient projection out of the numerator; **this file assembles the
seven into one statement about the whole composite**:

`π ≫ (gr^kΩ^•_{X/S})^n ≅ gr^kΩ^n_{X/S} ⊆ Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`
  `=  (F^kΩ^•_{X/S})^n ⟶ F^kΩ^n_{X/S} ⟶ Ω^n_{X/S} ⟶ Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`.

That is the bridge a *differential* has to be carried along. The differential of a graded piece
is the differential of the step read modulo the next step, so nothing about it can be checked
except through the projection `CategoryTheory.FilteredObject.grMapπ`, which is an epimorphism
degreewise; and the right-hand side above carries no graded piece and no image subobject at all
— only the inclusion of the step `F^kΩ^n_{X/S}` into `Ω^n_{X/S}` and the projection onto the
quotient by the next step, which is the shape the wedge product and the Leibniz rule are
written in.

## Main results

* `Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoExteriorGraded_hom_comp_arrow`: the degreewise
  comparison of Section 0FMK, read on the projection onto the graded piece and into the quotient
  `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`, is the inclusion of the step followed by that quotient's
  projection. Nothing is assumed of `f`.
* `Stacks.CategoryTheory.comp_isoTrans_hom_comp`, its merging form
  `Stacks.CategoryTheory.comp_isoTrans_hom_comp_merge` and its leading form
  `Stacks.CategoryTheory.comp_isoTrans_hom_comp_head`: **one step of such an assembly, at
  generic objects** — a compatibility with a projection for `e₁` and one for `e₂ ≫ r` give one
  for `(e₁ ≪≫ e₂) ≫ r`.
* `Stacks.CategoryTheory.map_comp_mapIso_hom_comp_map`: the same across a functor, which is what
  the seventh step of the chain needs, it being `CategoryTheory.Functor.mapIso` of a composite.
* `Stacks.GradedPieceImage.mapSubobjectsObjIso_hom_eq`: the two factors the fifth and sixth
  steps leave behind are the one identification
  `Stacks.GradedPieceImage.mapSubobjectsObjIso` that
  `Stacks.DeRhamSmooth.stepXToExteriorFiltration` is written with.

## Implementation notes

**The assembly is a kernel problem, not an elaboration problem**, and the four generic lemmas
above are what solves it. Written directly — the seven compatibilities chained by `Eq.trans`
under towers of `CategoryTheory.whisker_eq`, with one `CategoryTheory.Category.assoc` peel and
one `@[reassoc]` lemma per step — the proof *elaborates completely*, all seven steps firing with
no error, and the **kernel** then rejects the term with a deterministic timeout; halving the
size of the proof term does not change that, so it is defeq on the whole term and not its size.
`#count_heartbeats` cannot see this at all, since it runs at `maxHeartbeats 0`, which lifts the
kernel's deadline too: only a full build checks it.

What the generic lemmas change is *where the work happens*. Every reassociation and every
identification of two spellings of an intermediate object is discharged once, by the elaborator,
against a signature over an abstract category, where the objects are variables and there is
nothing to unfold. The kernel is then left with seven applications of named constants whose
types it already has, and it checks them in seconds. This is the same device as
`Stacks.GradedPieceImage.cokernelEpiCompIsoImageInQuotient`, whose docstring records naming a
three-fold composite to make one compatibility affordable — applied here against the kernel
rather than against the elaborator.

The accumulated prefix is collapsed as the assembly proceeds rather than afterwards: the merging
form takes the equation identifying `a₁ ≫ a₂` with a named morphism, so the fifth step hands in
`Stacks.GradedPieceImage.mapSubobjectsObjIso_hom_eq` and every other step hands in `rfl`, and
what comes out is `Stacks.DeRhamSmooth.stepXToExteriorFiltration` on the nose, with no
reassociation of the prefix left to do.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

universe u

namespace Stacks.CategoryTheory

variable {C : Type*} [_root_.CategoryTheory.Category C]

/-- **One step of the assembly of a chain of isomorphisms, read on a projection.** If `e₁`
carries `p` to `a₁ ≫ q₁` and `e₂` followed by `r` carries `q₁` to `a₂ ≫ q₂`, then `e₁ ≪≫ e₂`
followed by `r` carries `p` to `a₁ ≫ a₂ ≫ q₂`.

Stated over an abstract category, which is the whole point: all of the reassociation is done
here, where the objects are variables, and not at the binders of the de Rham complex, where the
*kernel* cannot afford it. See the implementation notes of this file.

Costs 295 heartbeats against the default budget of 200,000. -/
theorem comp_isoTrans_hom_comp {W X₀ Y₀ Z₀ T A B : C} {p : W ⟶ X₀} {e₁ : X₀ ≅ Y₀}
    {e₂ : Y₀ ≅ Z₀} {r : Z₀ ⟶ T} {a₁ : W ⟶ A} {q₁ : A ⟶ Y₀} {a₂ : A ⟶ B} {q₂ : B ⟶ T}
    (h₁ : p ≫ e₁.hom = a₁ ≫ q₁) (h₂ : q₁ ≫ e₂.hom ≫ r = a₂ ≫ q₂) :
    p ≫ (e₁ ≪≫ e₂).hom ≫ r = a₁ ≫ a₂ ≫ q₂ := by
  rw [Iso.trans_hom, Category.assoc, ← Category.assoc p, h₁, Category.assoc, h₂]

/-- `Stacks.CategoryTheory.comp_isoTrans_hom_comp` with the two accumulated prefixes merged into
one named morphism `a`, supplied by an equation `a₁ ≫ a₂ = a`.

This is what keeps the prefix of a long chain from growing: at each step the prefix accumulated
so far is replaced by the single morphism it is equal to, so the conclusion of the last step is
already written in terms of the named composite rather than as a nest of factors needing
reassociation. Where there is no name to collapse to, the equation is `rfl`.

Costs 252 heartbeats against the default budget of 200,000. -/
theorem comp_isoTrans_hom_comp_merge {W X₀ Y₀ Z₀ T A B : C} {p : W ⟶ X₀} {e₁ : X₀ ≅ Y₀}
    {e₂ : Y₀ ≅ Z₀} {r : Z₀ ⟶ T} {a₁ : W ⟶ A} {q₁ : A ⟶ Y₀} {a₂ : A ⟶ B} {q₂ : B ⟶ T}
    {a : W ⟶ B} (h₁ : p ≫ e₁.hom = a₁ ≫ q₁) (h₂ : q₁ ≫ e₂.hom ≫ r = a₂ ≫ q₂)
    (ha : a₁ ≫ a₂ = a) :
    p ≫ (e₁ ≪≫ e₂).hom ≫ r = a ≫ q₂ :=
  (comp_isoTrans_hom_comp h₁ h₂).trans (by rw [← ha, Category.assoc])

/-- `Stacks.CategoryTheory.comp_isoTrans_hom_comp` for the leading step of a chain, where the
compatibility has no prefix: `e₁` carries `p` to `q₁` outright. This is the shape the projection
onto a graded piece of a filtered complex meets its first identification in
(`CategoryTheory.Limits.PreservesCokernel.π_iso_hom`), the graded piece being
*defined* as that cokernel, so that nothing separates the two projections.

Costs 239 heartbeats against the default budget of 200,000. -/
theorem comp_isoTrans_hom_comp_head {W X₀ Y₀ Z₀ T B : C} {p : W ⟶ X₀} {e₁ : X₀ ≅ Y₀}
    {e₂ : Y₀ ≅ Z₀} {r : Z₀ ⟶ T} {q₁ : W ⟶ Y₀} {a₂ : W ⟶ B} {q₂ : B ⟶ T}
    (h₁ : p ≫ e₁.hom = q₁) (h₂ : q₁ ≫ e₂.hom ≫ r = a₂ ≫ q₂) :
    p ≫ (e₁ ≪≫ e₂).hom ≫ r = a₂ ≫ q₂ := by
  rw [Iso.trans_hom, Category.assoc, ← Category.assoc p, h₁, h₂]

/-- **A compatibility with a projection, carried along a functor.** For `U` a functor and
`c ≫ e.hom ≫ r = a ≫ q` in the source, the image of that equation is a compatibility of
`CategoryTheory.Functor.mapIso U e` with `U.map c`.

A chain of identifications of graded pieces ends in a change of rings, and the identification
after it is the image under restriction of scalars of an identification of sheaves of modules
over the larger ring; so the last step of such a chain is a `CategoryTheory.Functor.mapIso`, and
this is how its compatibility is reached from the compatibility of what it is the image of.

Costs 247 heartbeats against the default budget of 200,000. -/
theorem map_comp_mapIso_hom_comp_map {D : Type*} [_root_.CategoryTheory.Category D] (U : C ⥤ D)
    {W X₀ Y₀ Z₀ A : C} {c : W ⟶ X₀} {e : X₀ ≅ Y₀} {r : Y₀ ⟶ Z₀} {a : W ⟶ A} {q : A ⟶ Z₀}
    (h : c ≫ e.hom ≫ r = a ≫ q) :
    U.map c ≫ (U.mapIso e).hom ≫ U.map r = U.map a ≫ U.map q := by
  rw [Functor.mapIso_hom, ← U.map_comp, ← U.map_comp, h, U.map_comp]

end Stacks.CategoryTheory

namespace Stacks.GradedPieceImage

/-- **`Stacks.GradedPieceImage.mapSubobjectsObjIso` is the inclusion of the transported subobject
in the subobject presented by the image of its inclusion, followed by the identification of that
subobject with its underlying object.** The two factors are what the transport of a subquotient
along a functor leaves behind — the first from the change of description of the transported
subobject, the second from the exactness of the functor — and this says they compose to the one
identification `Stacks.DeRhamSmooth.stepXToExteriorFiltration` is written with.

The monomorphy of `U.map P.arrow` is supplied here, from `U` preserving monomorphisms, and not
by instance search: at the binders of the de Rham complex it is not found, which is the reason
`Stacks.GradedPieceImage.mapSubobjectsObjIso` exists at all.

Costs 316 heartbeats against the default budget of 200,000. -/
theorem mapSubobjectsObjIso_hom_eq {C₁ : Type*} [Category* C₁] {D₁ : Type*} [Category* D₁]
    (U : C₁ ⥤ D₁) [U.PreservesMonomorphisms] {Z : C₁} (P : Subobject Z) :
    Subobject.ofLE ((mapSubobjects U Z).obj P) (Subobject.mk (U.map P.arrow))
          (mapSubobjects_obj U P).le ≫
        (@Subobject.underlyingIso _ _ _ _ (U.map P.arrow) (U.map_mono P.arrow)).hom =
      (mapSubobjectsObjIso U P).hom := by
  have := U.map_mono P.arrow
  simp [mapSubobjectsObjIso]

end Stacks.GradedPieceImage

namespace Stacks.DeRhamSmooth

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The degreewise comparison of [Stacks, Section 0FMK], read on the projection onto the
graded piece and into the quotient `Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}`**, for `n = k + 1 + m`:

`π ≫ ((gr^kΩ^•_{X/S})^n ≅ gr^kΩ^n_{X/S} ⊆ Ω^n_{X/S}/F^{k+1}Ω^n_{X/S})`
  `=  ((F^kΩ^•_{X/S})^n ⟶ F^kΩ^n_{X/S}) ≫ (F^kΩ^n_{X/S} ⟶ Ω^n_{X/S}) ≫ π`.

This is the assembly of the seven per-step compatibilities of
`Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` with the projection, and the point of it is
what is *not* on the right-hand side: no graded piece, no image subobject and no cokernel of an
inclusion of steps survive, only the comparison of the two presentations of the step
(`Stacks.DeRhamSmooth.stepXToExteriorFiltration`), the inclusion of the step into `Ω^n_{X/S}`
and the projection onto the quotient by the next step. That is the shape the wedge product is
written in, so it is the shape in which the Leibniz rule
`AlgebraicGeometry.SheafOfModules.summandOfEq_d` can be compared against a square on the step.

Nothing is assumed of `f`, and in particular not smoothness: both sides are defined for every
morphism, each of the seven steps is an identification of two models of one quotient, and the
projection is the projection of a filtered complex onto a graded piece.

Costs 142,313 heartbeats against the default budget of 200,000. -/
theorem grMapπ_f_gradedPieceXIsoExteriorGraded_hom_comp_arrow (k m : ℕ) :
    (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
          (deRhamSmoothFiltration f g)).f ((k + 1 + m : ℕ) : ℤ) ≫
        (gradedPieceXIsoExteriorGraded f g k m).hom ≫
          (_root_.SheafOfModules.restrictScalars.{u}
            (AlgebraicGeometry.SheafOfModules.underlyingRingHom
              (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map
            (imageSubobject (_root_.SheafOfModules.exteriorGradedHom
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
                (Scheme.Hom.relativeDifferentialsShortComplex f g).X₁)
              (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
                (Scheme.Hom.relativeDifferentialsShortComplex f g).X₂)
              (Scheme.Hom.relativeDifferentialsShortComplex f g).f k m)).arrow =
      stepXToExteriorFiltration f g k m ≫
        (_root_.SheafOfModules.restrictScalars.{u}
              (AlgebraicGeometry.SheafOfModules.underlyingRingHom
                (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))).map
            (Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) k).arrow ≫
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
              (Scheme.Hom.relativeDifferentialsShortComplex f g).f (𝟙 _) (k + 1) m)) := by
  have hle : Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) (k + 1) ≤
      Scheme.Hom.relativeDifferentialsExteriorFiltration f g (k + 1 + m) k :=
    _root_.SheafOfModules.exteriorImageFiltration_antitone _ _ _ (k + 1 + m) (Nat.le_succ k)
  have hle2 := AlgebraicGeometry.SheafOfModules.exteriorPowerSubobjectRestriction_monotone
    (Scheme.Hom.deRhamAlgebras (f ≫ g)) (k + 1 + m) hle
  set E := ((AlgebraicGeometry.SheafOfModules.deRhamComplex
      (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras (f ≫ g)))).extendXIso
    ComplexShape.embeddingUpNat (i := k + 1 + m) (i' := ((k + 1 + m : ℕ) : ℤ)) rfl) with hE
  have hle3 := leOfHom ((_root_.CategoryTheory.Subobject.map E.inv).map
        (homOfLE hle2))
  have := Stacks.GradedPieceImage.mono_iso_inv E
  have h1 := grMapπ_f_gradedPieceXIsoCokernelStep_hom f g k m
  have h2 := Stacks.GradedPieceImage.π_cokernelIsoCokernelOfLEMk_hom _
    (((deRhamSmoothFiltration f g).filtration.ι.app (op (k : ℤ))).f ((k + 1 + m : ℕ) : ℤ))
    (((deRhamSmoothFiltration f g).filtration.ι.app (op ((k + 1 : ℕ) : ℤ))).f
      ((k + 1 + m : ℕ) : ℤ))
    (by
      have hd := (deRhamSmoothFiltration f g).filtration.diagram_map_comp_ι_app
        (homOfLE (Int.le_add_one le_rfl) : (k : ℤ) ⟶ (k : ℤ) + 1).op
      have hd2 := HomologicalComplex.congr_hom hd ((k + 1 + m : ℕ) : ℤ)
      rw [HomologicalComplex.comp_f] at hd2
      exact hd2)
  have hW := mk_ι_app_f_eq f g (k + 1) (k + 1 + m) (by omega)
  have hN := mk_ι_app_f_eq f g k (k + 1 + m) (by omega)
  have h3 := Stacks.GradedPieceImage.π_cokernelOfLEIsoOfEq'_hom
    (le_trans hW.le (le_trans hle3 hN.ge)) hle3 hW hN
  have h4 := Abelian.Subobject.π_cokernelOfLEMapIso_hom E.inv hle2
  have h5 := Stacks.GradedPieceImage.π_cokernelOfLEIsoOfEq'_hom hle2
    (Stacks.GradedPieceImage.mk_map_arrow_le _ _ _ hle)
    (Stacks.GradedPieceImage.mapSubobjects_obj _ _)
    (Stacks.GradedPieceImage.mapSubobjects_obj _ _)
  have h6 := Stacks.GradedPieceImage.π_cokernelOfLEFunctorMapIso_hom
    (_root_.SheafOfModules.restrictScalars.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g)))) _ _ hle
  have h7 := Stacks.CategoryTheory.map_comp_mapIso_hom_comp_map
    (_root_.SheafOfModules.restrictScalars.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g))))
    (_root_.SheafOfModules.π_cokernelOfLEIsoExteriorGraded_hom_comp_arrow_of_eq _ _ _ _ _ hle
      (relativeDifferentialsExteriorFiltration_succ_eq f g k m)
      (relativeDifferentialsExteriorFiltration_eq f g k m))
  exact Stacks.CategoryTheory.comp_isoTrans_hom_comp_head h1
    (Stacks.CategoryTheory.comp_isoTrans_hom_comp_merge h2
      (Stacks.CategoryTheory.comp_isoTrans_hom_comp_merge h3
        (Stacks.CategoryTheory.comp_isoTrans_hom_comp_merge h4
          (Stacks.CategoryTheory.comp_isoTrans_hom_comp_merge h5
            (Stacks.CategoryTheory.comp_isoTrans_hom_comp h6 h7)
            (@Stacks.GradedPieceImage.mapSubobjectsObjIso_hom_eq _ _ _ _
              (_root_.SheafOfModules.restrictScalars.{u}
                (AlgebraicGeometry.SheafOfModules.underlyingRingHom
                  (φ := AlgebraicGeometry.inverseImageStructureMap (f ≫ g))))
              (Stacks.SheafifyMono.restrictScalars_preservesMonomorphisms _) _ _))
          rfl)
        rfl)
      rfl)

end Stacks.DeRhamSmooth

end
