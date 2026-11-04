module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTriple
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Restricting an affine chart to a smaller affine open

Let `(X, D, M)` be a triple as in Situation 0F8S and let `(U, A, f, M^•)` be an affine chart for
it, as in `StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTriple`.  This file *builds*
an affine chart over any affine open `V ⊆ U`: the chart `(V, B, f|_V, M^• ⊗_A B)`, where
`B = Γ(X, V)` and the base change is along the restriction map `A ⟶ B`.  Taking `V = D(g)` a
standard open of `U` gives the chart used to compare two charts on the overlap of their domains.

This is one of the two constructors of
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart` in the library; the other is
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullback` of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback`, which is tag 0F8T for a
general `h`.  Every other statement about charts consumes one.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.restrict`: the chart
  `(V, Γ(X, V), f|_V, M^• ⊗_A Γ(X, V))` over an affine open `V ⊆ U`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.restrictBasicOpen`: the same over a
  standard open `D(g) ⊆ U`, which is the form in which charts are compared on overlaps.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.restrictRepresentsIso`: the
  isomorphism in `D(𝒪_V)` identifying `E|_V` with the sheaf of modules of `M^• ⊗_A Γ(X, V)`,
  which is the `represents` field of the restricted chart.

## Main results

* `AlgebraicGeometry.isOpenImmersion_SpecMap_presheaf_map`: the restriction map between the
  coordinate rings of two nested affine opens induces an open immersion of spectra.
* `AlgebraicGeometry.IsAffineOpen.isRegular_presheaf_map_of_le`: a nonzerodivisor on an affine
  open stays a nonzerodivisor on a smaller affine open, the restriction being flat.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.restrict_determinantalIdeal`: the
  determinantal ideals of the restricted chart are the extensions of those of the original
  chart, which is Stacks tag 0GSU read on charts.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart`
  `.isPrincipal_restrict_determinantalIdeal`: hence principality of the determinantal ideals is
  inherited by the restricted chart.

## How `represents` is proved

The `represents` field of a chart says: some complex `E` of `𝒪_X`-modules represents `M`, and
`E|_U` is isomorphic in `D(𝒪_U)` to the complex of `𝒪_U`-modules obtained from `M^•` by the
`tilde` equivalence on `Spec A` transported along `U ≅ Spec A`.  For the restricted chart the
same `E` is used, and the second isomorphism is produced in three moves.

* Restricting to `V` is restricting to `U` and then along `j : V ⟶ U`
  (`AlgebraicGeometry.Scheme.homOfLE`), by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` and
  `AlgebraicGeometry.Scheme.homOfLE_ι`.
* Restriction along an open immersion is exact — it is additive, preserves finite limits by
  `AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits` and finite colimits
  by left adjointness — so it induces a functor on derived categories,
  `CategoryTheory.Functor.mapDerivedCategory`, and
  `CategoryTheory.Functor.mapDerivedCategoryFactors` says that functor computes the restriction
  of a complex.  This is what transports the chart's isomorphism from `D(𝒪_U)` to `D(𝒪_V)`;
  it is an isomorphism in the derived category, not a quasi-isomorphism of complexes, so it
  cannot be restricted by hand.
* On the other side, `j` followed by `U ≅ Spec A` is `V ≅ Spec B` followed by `Spec (A ⟶ B)`
  (`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map`), and the restriction of `M^~`
  along `Spec (A ⟶ B)` is the sheaf associated to `B ⊗_A M^•`, which is the affine dictionary
  `Stacks.AffineTilde.restrictTildeComplexIso`.  Finally
  `Stacks.Eta.DeterminantalIdeal.baseChangeCochainIso` identifies `B ⊗_A M^•` with the complex
  of the base-changed bounded complex `M^• ⊗_A B`, whose differentials are the entrywise images
  of those of `M^•`.

## Why the `@[stacks 0F8T]` attribute is qualified

Tag 0F8T, part (1), is stated for an arbitrary morphism `h : Y ⟶ X` for which `h⁻¹D` is defined:
an affine open `V ⊆ Y` with `h(V) ⊆ U` carries a chart for the pulled-back triple
`(Y, h⁻¹D, Lh^*M)`.  What is proved here is the case `h = 𝟙 X`, i.e. that a chart restricts to
any smaller affine open of its own domain.  The attribute therefore records exactly the case
that is proved.

The general case is `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullback` of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback`, which also carries the
tag.  Its `represents` field is the analogue, for a general `h`, of `restrictRepresentsIso`
below: restriction along the open immersion `V ⟶ Y` is derived pullback along it, so the
composition formula of Tag 0D5S reduces the restriction of `Lh^*M` to the derived pullback of
`M|_U` along `h|_V : V ⟶ U`, and then along `Spec (A ⟶ B)`; there the derived pullback is the
degreewise one, because `M̃^•` is K-flat, which is what replaces `B ⊗ᴸ_A M^•` by the termwise
base change `B ⊗_A M^•`.

Part (2) of the tag is `Stacks.map_idealI_eq_idealI_baseChange`, carried as `@[stacks 0GSU]` in
`StacksFrontier.LinearAlgebra.Matrix.BoundedComplex`; it is used here to compute the determinantal
ideals of the restricted chart.

## References

* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0GSU](https://stacks.math.columbia.edu/tag/0GSU)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect

attribute [local instance] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry

/-- The restriction map `Γ(X, U) ⟶ Γ(X, V)` between the coordinate rings of two nested affine
opens of a scheme induces an open immersion `Spec Γ(X, V) ⟶ Spec Γ(X, U)`.

Indeed `Spec` of the restriction map is the inclusion `V ⟶ U` of open subschemes conjugated by
the two canonical isomorphisms `U ≅ Spec Γ(X, U)` and `V ≅ Spec Γ(X, V)`, by
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map`. -/
theorem isOpenImmersion_SpecMap_presheaf_map {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hle : V ≤ U) :
    IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE hle).op)) := by
  have hsq : hV.isoSpec.hom ≫ Spec.map (X.presheaf.map (homOfLE hle).op) =
      X.homOfLE hle ≫ hU.isoSpec.hom :=
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ hle
  rw [show Spec.map (X.presheaf.map (homOfLE hle).op) =
      hV.isoSpec.inv ≫ X.homOfLE hle ≫ hU.isoSpec.hom from (Iso.eq_inv_comp _).2 hsq]
  infer_instance

/-- A section which is a nonzerodivisor on an affine open restricts to a nonzerodivisor on a
smaller affine open.

The restriction map `Γ(X, U) ⟶ Γ(X, V)` is flat, being the ring map of an open immersion of
spectra by `AlgebraicGeometry.isOpenImmersion_SpecMap_presheaf_map`, and multiplication by a
nonzerodivisor is injective on a flat module by
`Module.Flat.isSMulRegular_of_nonZeroDivisors`. -/
theorem IsAffineOpen.isRegular_presheaf_map_of_le {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hle : V ≤ U) {f : Γ(X, U)} (hf : IsRegular f) :
    IsRegular ((X.presheaf.map (homOfLE hle).op) f) := by
  have hoi : IsOpenImmersion (Spec.map (X.presheaf.map (homOfLE hle).op)) :=
    isOpenImmersion_SpecMap_presheaf_map hU hV hle
  let := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  have : Module.Flat ↑Γ(X, U) ↑Γ(X, V) := AlgebraicGeometry.Flat.SpecMap_iff.1 inferInstance
  have hsm : IsSMulRegular ↑Γ(X, V) f :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (isRegular_iff_mem_nonZeroDivisors.1 hf)
  have key : ∀ z : ↑Γ(X, V), (X.presheaf.map (homOfLE hle).op) f * z = 0 → z = 0 := by
    intro z hz
    have hz' : f • z = f • (0 : ↑Γ(X, V)) := by rw [smul_zero, Algebra.smul_def]; exact hz
    exact hsm hz'
  exact isRegular_iff_mem_nonZeroDivisors.2
    (mem_nonZeroDivisors_iff.2 ⟨key, fun z hz => key z (by rw [mul_comm]; exact hz)⟩)

namespace ComplexAndDivisorSituation.AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- The isomorphism in `D(𝒪_V)` that makes `M^• ⊗_A Γ(X, V)` represent the restriction of `M`
to an affine open `V ⊆ U`, given the chart's own isomorphism over `U`.

The restriction of `E` to `V` is its restriction to `U` restricted along `j : V ⟶ U`; the
chart's isomorphism is carried along `j` by the functor that the exact functor
`AlgebraicGeometry.Scheme.Modules.restrictFunctor j` induces on derived categories; and on the
other side the affine dictionary `Stacks.AffineTilde.restrictTildeComplexIso` together with
`Stacks.Eta.DeterminantalIdeal.baseChangeCochainIso` turns the restriction of `\widetilde{M^•}`
into the sheaf of modules of the base-changed bounded complex. -/
def restrictRepresentsIso (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens))
    (E : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ)
    (e : DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor (C.U : S.X.Opens).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E) ≅
      DerivedCategory.Q.obj
        (((tilde.functor Γ(S.X, C.U) ⋙
          Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C.complex.toCochainComplex)) :
    DerivedCategory.Q.obj
        (((Scheme.Modules.restrictFunctor (V : S.X.Opens).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E) ≅
      DerivedCategory.Q.obj
        (((tilde.functor Γ(S.X, (V : S.X.Opens)) ⋙
          Scheme.Modules.restrictFunctor V.2.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (C.complex.baseChange
            (S.X.presheaf.map (homOfLE hle).op).hom).toCochainComplex) := by
  have hV : IsAffineOpen (V : S.X.Opens) := V.2
  have hsq : hV.isoSpec.hom ≫ Spec.map (S.X.presheaf.map (homOfLE hle).op) =
      S.X.homOfLE hle ≫ C.U.2.isoSpec.hom :=
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ hle
  have hoi : IsOpenImmersion (Spec.map (S.X.presheaf.map (homOfLE hle).op)) :=
    isOpenImmersion_SpecMap_presheaf_map C.U.2 hV hle
  -- restriction to `V` factors through restriction to the chart
  have a₁ : (((Scheme.Modules.restrictFunctor (V : S.X.Opens).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E) ≅
      ((Scheme.Modules.restrictFunctor (S.X.homOfLE hle)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor (C.U : S.X.Opens).ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E) :=
    ((Functor.mapHomologicalComplexCompIso
      ((Scheme.Modules.restrictFunctorComp (S.X.homOfLE hle) (C.U : S.X.Opens).ι).symm ≪≫
        Scheme.Modules.restrictFunctorCongr (S.X.homOfLE_ι hle))
      (ComplexShape.up ℤ)).app E).symm
  -- the chart's tilde complex, with the two functors applied one at a time
  have a₂ : (((tilde.functor Γ(S.X, C.U) ⋙
          Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C.complex.toCochainComplex) ≅
      ((Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((tilde.functor Γ(S.X, C.U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C.complex.toCochainComplex) :=
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor Γ(S.X, C.U) ⋙
        Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom))
      (ComplexShape.up ℤ)).app C.complex.toCochainComplex).symm
  -- restricting along `U ≅ Spec A` and then to `V` is restricting along `Spec (A ⟶ B)`
  have a₃ : ∀ Y : CochainComplex (OXMod.{u, u} (Spec Γ(S.X, C.U)).toRingedSpace) ℤ,
      ((Scheme.Modules.restrictFunctor (S.X.homOfLE hle)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor C.U.2.isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Y) ≅
      ((Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor
          (Spec.map (S.X.presheaf.map (homOfLE hle).op))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Y) := fun Y =>
    (Functor.mapHomologicalComplexCompIso
        ((Scheme.Modules.restrictFunctorComp (S.X.homOfLE hle) C.U.2.isoSpec.hom).symm ≪≫
          Scheme.Modules.restrictFunctorCongr hsq.symm ≪≫
          Scheme.Modules.restrictFunctorComp hV.isoSpec.hom
            (Spec.map (S.X.presheaf.map (homOfLE hle).op)))
        (ComplexShape.up ℤ)).app Y ≪≫
      ((Functor.mapHomologicalComplexCompIso
        (Iso.refl (Scheme.Modules.restrictFunctor
            (Spec.map (S.X.presheaf.map (homOfLE hle).op)) ⋙
          Scheme.Modules.restrictFunctor hV.isoSpec.hom))
        (ComplexShape.up ℤ)).app Y).symm
  -- the affine dictionary, and base change of the bounded complex
  have a₄ : ((Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.restrictFunctor
          (Spec.map (S.X.presheaf.map (homOfLE hle).op))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((tilde.functor Γ(S.X, C.U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C.complex.toCochainComplex)) ≅
      (((tilde.functor Γ(S.X, (V : S.X.Opens)) ⋙
          Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (C.complex.baseChange
            (S.X.presheaf.map (homOfLE hle).op).hom).toCochainComplex) :=
    ((Scheme.Modules.restrictFunctor hV.isoSpec.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).mapIso
      (Stacks.AffineTilde.restrictTildeComplexIso (S.X.presheaf.map (homOfLE hle).op)
          C.complex.toCochainComplex ≪≫
        ((tilde.functor Γ(S.X, (V : S.X.Opens))).mapHomologicalComplex
          (ComplexShape.up ℤ)).mapIso
          (Stacks.Eta.DeterminantalIdeal.baseChangeCochainIso
            (S.X.presheaf.map (homOfLE hle).op).hom C.complex)) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (tilde.functor Γ(S.X, (V : S.X.Opens)) ⋙
          Scheme.Modules.restrictFunctor hV.isoSpec.hom))
        (ComplexShape.up ℤ)).app _
  -- restriction along `j` is exact, hence descends to the derived categories
  have step : ∀ K L : CochainComplex (OXMod.{u, u} (C.U : S.X.Opens).toScheme.toRingedSpace) ℤ,
      (DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) →
      (DerivedCategory.Q.obj
          (((Scheme.Modules.restrictFunctor (S.X.homOfLE hle)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≅
        DerivedCategory.Q.obj
          (((Scheme.Modules.restrictFunctor (S.X.homOfLE hle)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L)) := fun K L i =>
    ((Scheme.Modules.restrictFunctor (S.X.homOfLE hle)).mapDerivedCategoryFactors.app K).symm ≪≫
      (Scheme.Modules.restrictFunctor (S.X.homOfLE hle)).mapDerivedCategory.mapIso i ≪≫
      (Scheme.Modules.restrictFunctor (S.X.homOfLE hle)).mapDerivedCategoryFactors.app L
  exact DerivedCategory.Q.mapIso a₁ ≪≫ step _ _ (e ≪≫ DerivedCategory.Q.mapIso a₂) ≪≫
    DerivedCategory.Q.mapIso (a₃ _ ≪≫ a₄)

/-- **Stacks tag 0F8T, part (1), for the inclusion of an affine open into a chart.**  An affine
chart `(U, A, f, M^•)` for a triple `(X, D, M)` as in Situation 0F8S restricts to an affine chart
over any affine open `V ⊆ U`: its equation is the restriction `f|_V`, and its bounded complex of
finite free modules is the base change `M^• ⊗_A Γ(X, V)`, i.e. the complex whose differentials
are the entrywise images of those of `M^•` under `A ⟶ Γ(X, V)`.

That `f|_V` is again a nonzerodivisor is
`AlgebraicGeometry.IsAffineOpen.isRegular_presheaf_map_of_le`, the restriction between affine
opens being flat; that it cuts out `D ∩ V` is
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`; and that `M^• ⊗_A Γ(X, V)` represents the
restriction of `M` is `restrictRepresentsIso`. -/
@[stacks 0F8T "part (1) in the case `h = 𝟙 X`: the restriction of an affine chart to a smaller \
affine open `V ⊆ U` is an affine chart, with representing complex `M^• ⊗_A Γ(X, V)`.  The case \
of a general `h` is AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pullback in \
StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback, which carries the tag too."]
def restrict (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) : AffineChart S where
  U := V
  f := (S.X.presheaf.map (homOfLE hle).op) C.f
  regular := IsAffineOpen.isRegular_presheaf_map_of_le C.U.2 V.2 hle C.regular
  divisor_ideal := by
    rw [← S.D.map_ideal hle, C.divisor_ideal, Ideal.map_span, Set.image_singleton]
    rfl
  complex := C.complex.baseChange (S.X.presheaf.map (homOfLE hle).op).hom
  represents := by
    obtain ⟨E, hE, ⟨e⟩⟩ := C.represents
    exact ⟨E, hE, ⟨C.restrictRepresentsIso V hle E e⟩⟩

/-- The domain of the restriction of a chart to an affine open `V ⊆ U` is `V`. -/
@[simp]
theorem restrict_U (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) : (C.restrict V hle).U = V :=
  rfl

/-- The equation of the restriction of a chart to `V ⊆ U` is the image of `f` in `Γ(X, V)`. -/
@[simp]
theorem restrict_f (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) :
    (C.restrict V hle).f = (S.X.presheaf.map (homOfLE hle).op) C.f :=
  rfl

/-- The complex of the restriction of a chart to `V ⊆ U` is `M^• ⊗_A Γ(X, V)`. -/
@[simp]
theorem restrict_complex (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) :
    (C.restrict V hle).complex =
      C.complex.baseChange (S.X.presheaf.map (homOfLE hle).op).hom :=
  rfl

/-- **The determinantal ideals of a restricted chart.**  The ideal `I_i(M^•, f)` of the chart
restricted to an affine open `V ⊆ U` is the extension of `I_i(M^•, f)` along `Γ(X, U) ⟶ Γ(X, V)`.
This is Stacks tag 0GSU — part (2) of tag 0F8T — read on charts. -/
@[simp]
theorem restrict_determinantalIdeal (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) (i : ℤ) :
    (C.restrict V hle).determinantalIdeal i =
      Ideal.map (S.X.presheaf.map (homOfLE hle).op).hom (C.determinantalIdeal i) :=
  (map_idealI_eq_idealI_baseChange _ _ _ _).symm

/-- Principality of the determinantal ideals of a chart is inherited by its restriction to a
smaller affine open: an extension of a principal ideal is principal, generated by the image of a
generator. -/
theorem isPrincipal_restrict_determinantalIdeal (C : AffineChart S) (V : S.X.affineOpens)
    (hle : (V : S.X.Opens) ≤ (C.U : S.X.Opens)) {i : ℤ}
    (h : (C.determinantalIdeal i).IsPrincipal) :
    ((C.restrict V hle).determinantalIdeal i).IsPrincipal := by
  obtain ⟨a, ha⟩ := h
  refine ⟨(S.X.presheaf.map (homOfLE hle).op) a, ?_⟩
  rw [C.restrict_determinantalIdeal V hle i, ha, Ideal.map_span, Set.image_singleton]
  rfl

/-- The restriction of an affine chart to a standard open `D(g) ⊆ U`, the form in which two
charts are compared on the overlap of their domains: a point of the overlap lies in a standard
open of each chart, and both restrict to the same open. -/
def restrictBasicOpen (C : AffineChart S) (g : Γ(S.X, C.U)) : AffineChart S :=
  C.restrict (S.X.affineBasicOpen g) (S.X.basicOpen_le g)

/-- The domain of the restriction of a chart to `D(g)` is the affine open `D(g)`. -/
@[simp]
theorem restrictBasicOpen_U (C : AffineChart S) (g : Γ(S.X, C.U)) :
    (C.restrictBasicOpen g).U = S.X.affineBasicOpen g :=
  rfl

/-- The equation of the restriction of a chart to `D(g)` is the image of `f` in
`Γ(X, D(g))`. -/
@[simp]
theorem restrictBasicOpen_f (C : AffineChart S) (g : Γ(S.X, C.U)) :
    (C.restrictBasicOpen g).f =
      (S.X.presheaf.map (homOfLE (S.X.basicOpen_le g)).op) C.f :=
  rfl

/-- The complex of the restriction of a chart to `D(g)` is `M^• ⊗_A Γ(X, D(g))`. -/
@[simp]
theorem restrictBasicOpen_complex (C : AffineChart S) (g : Γ(S.X, C.U)) :
    (C.restrictBasicOpen g).complex =
      C.complex.baseChange (S.X.presheaf.map (homOfLE (S.X.basicOpen_le g)).op).hom :=
  rfl

/-- The determinantal ideals of the restriction of a chart to a standard open `D(g)` are the
extensions of those of the chart to `Γ(X, D(g))`. -/
theorem restrictBasicOpen_determinantalIdeal (C : AffineChart S) (g : Γ(S.X, C.U)) (i : ℤ) :
    (C.restrictBasicOpen g).determinantalIdeal i =
      Ideal.map (S.X.presheaf.map (homOfLE (S.X.basicOpen_le g)).op).hom
        (C.determinantalIdeal i) :=
  C.restrict_determinantalIdeal _ _ i

end ComplexAndDivisorSituation.AffineChart

end AlgebraicGeometry

end
