module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.Limits.AbsoluteNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep
public import StacksFrontier.AlgebraicGeometry.Limits.StageTransfer
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Immersion

/-!
# Descending an ample sheaf and a quasi-compact open to one common stage

The Stacks proof of [Stacks, Tag 0E21] writes a scheme `X` carrying an ample invertible sheaf `L`
as a limit `X = lim Xᵢ` of schemes of finite type over `ℤ` with affine transition morphisms
([Stacks, Tag 01ZA]) and then descends three things to a finite stage: the open `W`
([Stacks, Tag 01Z4] (1)), the sheaf `L` ([Stacks, Tag 0B8W] (2)) and the *ampleness* of `L`
([Stacks, Tag 09MT]). The three descents land at three different stages, and the argument needs
them at one.

This file performs that refinement, and then runs the whole of [Stacks, Tag 0E21] through it,
ending at the tag itself: the limit presentation is supplied by absolute Noetherian approximation,
whose single-affine step
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.isOneAffineOpenStep` is proved in this
repository, so no hypothesis beyond ampleness is left.

## Main results

* `exists_isAmple_pullback_iso_preimage_eq_of_isLimit`, in the namespace
  `AlgebraicGeometry.Scheme.Modules`: the common-stage refinement.
* `exists_affine_nonvanishingOpen_factorsThrough_of_isLimit`: [Stacks, Tag 0E21] for the limit of
  a cofiltered system of quasi-compact quasi-separated schemes of finite type over `ℤ`.
* `exists_affine_nonvanishingOpen_factorsThrough_of_isOneAffineOpenStep`: [Stacks, Tag 0E21] with
  no finiteness hypothesis on the scheme at all, granted the single-affine step of Noetherian
  approximation.
* `exists_affine_nonvanishingOpen_factorsThrough`: **[Stacks, Tag 0E21]**, unconditionally.

## Implementation notes

**The order of the three descents is forced, and only one order works.** Tag 09MT must be applied
*last*. It produces ampleness at *some* stage below the one it is given, and ampleness does not
then descend further: nothing lets a sheaf ample at a stage be recognised as ample at an earlier
one. So the sheaf and the open are descended first, refined to a common index by cofilteredness,
and only then is ampleness obtained — at a stage over that common index, to which the sheaf and
the open transport by pullback and preimage.

The composite "Tag 0B8W (2) then Tag 09MT" already existed in this repository, *specialised*:
`AlgebraicGeometry.FieldExtensionDescent.exists_isAmple_baseChangeDiagram_obj` runs it on the
diagram of base changes of a scheme to the finitely generated subalgebras of a field extension,
for [Stacks, Tag 0BDC]. That form cannot serve here for two independent reasons — it is tied to
that one diagram, and its conclusion keeps only the *existence* of an ample sheaf at a stage,
dropping the isomorphism `L ≅ p^* M`, which is exactly the datum Tag 0E21 needs in order to
carry its conclusion back to the limit. The statement below is the general diagram, with the
isomorphism and the open retained; the specialised one is a candidate to be rederived from it
once the two can be put in import order.

The comparison of an iterated pullback with the pullback along a composite is
`AlgebraicGeometry.Scheme.Modules.pullbackCompObjIso`, which already packages Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` at the object level, with the equation oriented
as a diagram's `CategoryTheory.Functor.map_comp` delivers it. Only *module* isomorphisms are
transported, never sections of tensor powers, so no coherence property of
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` is needed.

Tag 01Z4 (1) descends only a *quasi-compact* open, while the tag quantifies over an arbitrary
one. The source's reduction is its own first sentence, "since `Spec A` is quasi-compact we may
replace `W` by a quasi-compact open still containing the image", and that is
`AlgebraicGeometry.exists_compactOpen_covering_range`. The conclusion transfers back because it
asserts a containment `X_s ⊆ W`, which only gets stronger when `W` is shrunk, together with a
factorisation of `Spec A ⟶ W` through `X_s`, which is an equation between morphisms into the
ambient scheme and so does not change when `W` does.

The two invertibility hypotheses differ in spelling between the tags — Tag 0B8W (2) states it
through `AlgebraicGeometry.Scheme.sheaf` and `AlgebraicGeometry.Scheme.ringCatSheaf`, Tag 09MT
and `AlgebraicGeometry.Scheme.Modules.IsAmple` through
`AlgebraicGeometry.Scheme.toRingedSpace` and
  `structureSheafRing` — and the two are
the same proposition by definition. They are converted by binding the instance under a declared
type, not left to instance search, which does not see through the two spellings.

The `@[stacks 0E21]` attribute is attached to `exists_affine_nonvanishingOpen_factorsThrough`, the
last theorem below, which carries exactly the hypotheses of the tag: a scheme, an ample
invertible sheaf on it, an open, and a family of points of that open parametrised by an integral
algebra over a field. The intermediate form
`exists_affine_nonvanishingOpen_factorsThrough_of_isOneAffineOpenStep` takes the single-affine
step of Noetherian approximation as a hypothesis and is kept beside it; that hypothesis is
discharged by `AlgebraicGeometry.Scheme.FiniteTypeApproximation.isOneAffineOpenStep`, which this
repository proves, so nothing is assumed.

## References

* [Stacks Project, Tag 0E21](https://stacks.math.columbia.edu/tag/0E21)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe v u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- **An ample invertible sheaf and a quasi-compact open on a limit come from one common stage.**

Let `c` be a limit cone on a cofiltered diagram `D` of quasi-compact quasi-separated schemes with
affine transition morphisms, let `L` be an ample invertible sheaf on the limit and let `W` be a
quasi-compact open of the limit. Then there is a stage `j` carrying an *ample* invertible sheaf
`M` and an open `V` with `L ≅ p^* M` and `W = p⁻¹ V`, where `p = c.π.app j`.

This is the refinement step of the Stacks proof of [Stacks, Tag 0E21]. The sheaf comes from
[Stacks, Tag 0B8W] (2) and the open from [Stacks, Tag 01Z4] (1), at two unrelated stages; they
are brought together by cofilteredness; and [Stacks, Tag 09MT] is applied *last*, because it
yields ampleness at one stage and ampleness does not descend from there to any earlier one. -/
theorem exists_isAmple_pullback_iso_preimage_eq_of_isLimit
    (L : c.pt.Modules)
    [hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible c.pt.toRingedSpace.presheaf
      (structureSheafRing c.pt.toRingedSpace).property L]
    (hL : IsAmple c.pt L)
    (W : c.pt.Opens) (hW : IsCompact (W : Set c.pt)) :
    ∃ (j : I) (M : (D.obj j).Modules),
      ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj j).toRingedSpace.presheaf
        (structureSheafRing (D.obj j).toRingedSpace).property M,
      ∃ V : (D.obj j).Opens,
        IsAmple (D.obj j) M ∧ W = c.π.app j ⁻¹ᵁ V ∧
          Nonempty (L ≅ (Scheme.Modules.pullback (c.π.app j)).obj M) := by
  -- the invertibility of `L` in the spelling Tag 0B8W (2) states
  have hLsheaf : AlgebraicGeometry.SheafOfModules.IsInvertible c.pt.sheaf.obj
      c.pt.ringCatSheaf.property L := hLinv
  -- Tag 0B8W (2): the sheaf comes from a stage
  obtain ⟨i₀, L₀, hL₀, ⟨e₀⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit
      D c hc L hLsheaf
  have hL₀' : AlgebraicGeometry.SheafOfModules.IsInvertible (D.obj i₀).toRingedSpace.presheaf
      (structureSheafRing (D.obj i₀).toRingedSpace).property L₀ := hL₀
  -- Tag 01Z4 (1): the quasi-compact open comes from a stage
  obtain ⟨i₁, V₁, -, hV₁⟩ := exists_preimage_eq D c hc W hW
  -- one index below both
  obtain ⟨j, g₀, g₁, -⟩ := IsCofilteredOrEmpty.cone_objs i₀ i₁
  have e₁ : L ≅ (Scheme.Modules.pullback (c.π.app j)).obj
      ((Scheme.Modules.pullback (D.map g₀)).obj L₀) :=
    e₀ ≪≫ (pullbackCompObjIso (c.π.app j) (D.map g₀) (c.π.app i₀) (c.w g₀).symm L₀).symm
  -- Tag 09MT, applied last
  obtain ⟨j', g, hamp⟩ :=
    Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs D c hc j
      ((Scheme.Modules.pullback (D.map g₀)).obj L₀) (isAmple_of_iso e₁ hL)
  refine ⟨j', _, inferInstance, D.map g ⁻¹ᵁ D.map g₁ ⁻¹ᵁ V₁, hamp, ?_, ⟨?_⟩⟩
  · rw [← hV₁, ← c.w g₁, ← c.w g, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
  · exact e₁ ≪≫ (pullbackCompObjIso (c.π.app j') (D.map g) (c.π.app j) (c.w g).symm _).symm

include hc in
/-- **[Stacks, Tag 0E21] at a limit of schemes of finite type over `ℤ`.**

Let `c` be a limit cone on a cofiltered diagram of quasi-compact quasi-separated schemes of
finite type over `ℤ` with affine transition morphisms, let `L` be an ample invertible sheaf on
the limit, let `W` be open in the limit and let `Spec A ⟶ W` be a family of points of `W`
parametrised by an integral algebra over a field. Then some positive tensor power of `L` has a
global section `s` with `X_s` affine, `X_s ⊆ W`, and `Spec A ⟶ W` factoring through `X_s`.

This is the Stacks proof of the tag with the limit presentation taken as a hypothesis: `W` is
shrunk to a quasi-compact open (`AlgebraicGeometry.exists_compactOpen_covering_range`), the sheaf,
the open and the ampleness are descended to one stage
(`exists_isAmple_pullback_iso_preimage_eq_of_isLimit`), the tag is applied there, and its
conclusion is carried back along the projection
(`exists_affine_nonvanishingOpen_factorsThrough_of_pullback`). -/
theorem exists_affine_nonvanishingOpen_factorsThrough_of_isLimit
    (k : Type v) (A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.IsIntegral k A]
    (hFT : ∀ i : I, LocallyOfFiniteType (terminal.from (D.obj i)))
    (L : c.pt.Modules)
    [hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible c.pt.toRingedSpace.presheaf
      (structureSheafRing c.pt.toRingedSpace).property L]
    (hL : IsAmple c.pt L)
    (W : c.pt.Opens) (f : Spec (CommRingCat.of A) ⟶ (W : Scheme.{u})) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (tensorPower c.pt.toRingedSpace.presheaf
        (structureSheafRing c.pt.toRingedSpace).property L (n : ℤ)).sections,
      ∃ U : c.pt.Opens,
        U = nonvanishingOpen
          (tensorPower c.pt.toRingedSpace.presheaf
            (structureSheafRing c.pt.toRingedSpace).property L (n : ℤ)) s ∧
        IsAffineOpen U ∧ U ≤ W ∧
        ∃ g : Spec (CommRingCat.of A) ⟶ (U : Scheme.{u}), g ≫ U.ι = f ≫ W.ι := by
  -- replace `W` by a quasi-compact open still containing the image of `Spec A`
  have hrange : Set.range (f ≫ W.ι).base ⊆ (W : Set c.pt) := by
    rintro _ ⟨y, rfl⟩
    exact (f.base y).property
  obtain ⟨W', hW'c, hW'W, hW'r⟩ := exists_compactOpen_covering_range (f ≫ W.ι) hrange
  obtain ⟨f', hf'⟩ := exists_factorsThrough_of_range_subset W' (f ≫ W.ι) hW'r
  -- descend the sheaf, the open and the ampleness to one stage
  obtain ⟨j, M, hMinv, V, hamp, hWV, ⟨e⟩⟩ :=
    exists_isAmple_pullback_iso_preimage_eq_of_isLimit D c hc L hL W' hW'c
  have : IsAffineHom (c.π.app j) := isAffineHom_π_app D c hc j
  have : LocallyOfFiniteType (terminal.from (D.obj j)) := hFT j
  obtain ⟨n, hn, s, U, hU, haff, hUW', g, hg⟩ :=
    exists_affine_nonvanishingOpen_factorsThrough_of_pullback (X := c.pt) k A
      (c.π.app j) M hamp L e V W' hWV f'
  exact ⟨n, hn, s, U, hU, haff, hUW'.trans hW'W, g, hg.trans hf'⟩

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- **[Stacks, Tag 0E21], granted the single-affine step of Noetherian approximation.**

Let `L` be an ample invertible sheaf on a scheme `X`, let `W ⊆ X` be open and let
`Spec A ⟶ W` be a family of points of `W` parametrised by an integral algebra over a field. Then
some positive tensor power of `L` has a global section `s` whose nonvanishing open `X_s` is
affine, is contained in `W`, and is such that `Spec A ⟶ W` factors through `X_s`.

The only hypothesis here that the tag does not carry is
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`: no finiteness assumption
on `X` is left, the quasi-compactness and quasi-separatedness that absolute Noetherian
approximation needs coming from ampleness itself
(`AlgebraicGeometry.Scheme.Modules.IsAmple.compactSpace` and
`AlgebraicGeometry.Scheme.Modules.quasiSeparatedSpace_of_isAmple`, the latter being
[Stacks, Tag 01PY] for the affine nonvanishing cover that ampleness provides).

The finite-presentation hypothesis of
`AlgebraicGeometry.Scheme.Modules.exists_affine_nonvanishingOpen_containing_range` is *eliminated*
and not discharged: a scheme carrying an ample invertible sheaf need not be of finite presentation
over `ℤ`, since the spectrum of any non-finitely-generated ring is affine and therefore carries
one. What removes it is the limit argument — the stages of absolute Noetherian approximation are
of finite type over `ℤ`, hence of finite presentation
(`AlgebraicGeometry.locallyOfFinitePresentation_terminal_from`), and the
conclusion is transferred back to `X` along the projection. -/
theorem exists_affine_nonvanishingOpen_factorsThrough_of_isOneAffineOpenStep
    (hstep : Scheme.FiniteTypeApproximation.IsOneAffineOpenStep.{u})
    (k : Type v) (A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.IsIntegral k A]
    (X : Scheme.{u}) (L : X.Modules)
    [hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : IsAmple X L)
    (W : X.Opens) (f : Spec (CommRingCat.of A) ⟶ (W : Scheme.{u})) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      ∃ U : X.Opens,
        U = nonvanishingOpen
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
        IsAffineOpen U ∧ U ≤ W ∧
        ∃ g : Spec (CommRingCat.of A) ⟶ (U : Scheme.{u}), g ≫ U.ι = f ≫ W.ι := by
  have : CompactSpace X := hL.compactSpace
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_isAmple X L hL
  obtain ⟨J, hpre, hne, hdir, Q, hQ, hQFT⟩ :=
    Scheme.FiniteTypeApproximation.exists_limitNoetherianSituation_of_isOneAffineOpenStep hstep X
  subst hQ
  have hnoeth : ∀ i : Jᵒᵖ, IsNoetherian (Q.system.obj i) := fun i ↦ Q.noetherian i.unop
  have : ∀ i : Jᵒᵖ, CompactSpace (Q.system.obj i) := fun i ↦ inferInstance
  have : ∀ i : Jᵒᵖ, QuasiSeparatedSpace (Q.system.obj i) := fun i ↦ inferInstance
  have hFT : ∀ i : Jᵒᵖ, LocallyOfFiniteType (terminal.from (Q.system.obj i)) :=
    fun i ↦ hQFT i.unop
  have : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (Q.system.map g) := fun g ↦
    Q.transition_affine g
  exact exists_affine_nonvanishingOpen_factorsThrough_of_isLimit Q.system Q.limitCone Q.isLimit
    k A hFT L hL W f

/-- **[Stacks, Tag 0E21].**

Let `L` be an ample invertible sheaf on a scheme `X`, let `W ⊆ X` be open and let
`Spec A ⟶ W` be a family of points of `W` parametrised by an integral algebra `A` over a field
`k`. Then there is an `n > 0` and a global section `s` of `L ^ ⊗ n` whose nonvanishing open `X_s`
is affine, is contained in `W`, and is such that `Spec A ⟶ W` factors through `X_s`.

This is `exists_affine_nonvanishingOpen_factorsThrough_of_isOneAffineOpenStep` with its one
remaining hypothesis discharged by
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.isOneAffineOpenStep`, the single-affine step of
Noetherian approximation relative to a quasi-compact open ([Stacks, Tag 07RN]). -/
@[stacks 0E21]
theorem exists_affine_nonvanishingOpen_factorsThrough
    (k : Type v) (A : Type u) [Field k] [CommRing A] [Algebra k A] [Algebra.IsIntegral k A]
    (X : Scheme.{u}) (L : X.Modules)
    [hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : IsAmple X L)
    (W : X.Opens) (f : Spec (CommRingCat.of A) ⟶ (W : Scheme.{u})) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
      ∃ U : X.Opens,
        U = nonvanishingOpen
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ∧
        IsAffineOpen U ∧ U ≤ W ∧
        ∃ g : Spec (CommRingCat.of A) ⟶ (U : Scheme.{u}), g ≫ U.ι = f ≫ W.ι :=
  exists_affine_nonvanishingOpen_factorsThrough_of_isOneAffineOpenStep
    Scheme.FiniteTypeApproximation.isOneAffineOpenStep.{u} k A X L hL W f

end AlgebraicGeometry.Scheme.Modules

end
