module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.FibreFlatnessSpecialization
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteTypeII.ModuleFlatLocus
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.FinitePushforward
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeFinitePresentation.LocalOnSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.WeaklyAssociatedLocallyFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeFinitePresentation.FinitePresentation
public import StacksFrontier.Algebra.Module.FinitePresentation.Transport
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.FlatnessTransfer

/-!
# The relative flat locus of a module of finite type over a morphism of finite type

Let `f : X ⟶ S` be a morphism of schemes locally of finite *type* and let `F` be a quasi-coherent
`𝒪_X`-module of finite type. If the weakly associated points of `S` are locally finite, the locus
where `F` is flat over `S` is still open; on it `F` is flat over `S` and finitely presented
*relative* to `S` in the sense of `AlgebraicGeometry.IsFinitelyPresentedRelative`. These are the
three assertions of Stacks 05IQ, the finite type version of Stacks 05IK.

## Main results

* `AlgebraicGeometry.isOpen_flatLocus_of_locallyOfFiniteType` is the openness assertion of
  Stacks 05IQ.
* `AlgebraicGeometry.isFlatOver_flatLocus_of_locallyOfFiniteType` is its flatness assertion and
  `AlgebraicGeometry.isFinitelyPresentedRelative_flatLocus` its relative-finite-presentation
  assertion. The latter is read off from the stronger statement for a module that is flat over
  the base everywhere, `AlgebraicGeometry.isFinitelyPresentedRelative_of_isFlatOver`.

## Implementation notes

Everything here rests on `Stacks.Flatness.ExistsAwayFlatFinitePresentationOfFlatAtPrime`, the
affine content of Stacks 05IK, which is the theorem
`Stacks.Flatness.existsAwayFlatFinitePresentationOfFlatAtPrime`; it reaches the statements below
through Stacks 05IK in
`StacksFrontier/AlgebraicGeometry/Flatness/FiniteTypeII/ModuleFlatLocus.lean`.

The argument of the source is the embedding into affine space. The question is local on `X` and
`S`, so one may assume both affine; then `f` factors as a closed immersion `i : X ⟶ X'` followed
by a morphism `p : X' ⟶ S` locally of finite presentation
(`AlgebraicGeometry.exists_finitePresentation_closedImmersion`), and `i` is finite. The
pushforward `i_*F` is quasi-coherent and of finite type, and Stacks 05IK applies to it over `p`.
Since `i` is a closed immersion its fibres are singletons, so the stalk of `i_*F` at `i x` is
isomorphic to the stalk of `F` at `x`
(`AlgebraicGeometry.stalk_isomorphic_pushforward_pushforward_of_finite_singleton_fiber`), which
transports relative flatness between the two sides. Openness of the flat locus of `F` is then
openness of the flat locus of `i_*F` pulled back along `i`.

For the relative-finite-presentation assertion the same factorisation is used in the case where
`F` is flat over `S` at *every* point of `X`, which is the case the flat locus reduces to. Then
`i_*F` is flat over `S` at every point of `X'`: at a point of the image this is the stalk
comparison again, and off the image the stalk of `i_*F` vanishes, because the inverse image of
an open disjoint from the closed set `i(X)` is empty and a module of sections over the empty
open is trivial. So Stacks 05IK makes `i_*F` a module of finite presentation on all of `X'`,
Stacks 09T8 turns that into finite presentation relative to `S`, and Stacks 09T9 carries it
across the finite morphism `i` to `F`. The affine case globalises because relative finite
presentation is a condition on affine charts
(`AlgebraicGeometry.isFinitelyPresentedRelative_of_resLE`): the chart `f.resLE V W` of a
morphism of schemes at affine opens `W ≤ f ⁻¹ᵁ V` is a morphism of affine schemes, and a module
flat over `S` everywhere restricts to one flat over `V` everywhere.

One bookkeeping lemma is needed that the finite presentation case did not need. Relative
flatness at a point is unchanged by *post*composition with an open immersion of the target
(`flatOverAt_comp_open_iff`), because the stalk map of an open immersion is an isomorphism and
flatness over a ring is transported along a ring isomorphism compatible with the action
(`flat_iff_of_ringEquiv`). It is what identifies relative flatness over an affine open of the
base with relative flatness over the base itself.

## References

* [Stacks Project, Tag 05IQ](https://stacks.math.columbia.edu/tag/05IQ)
* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
* [Stacks Project, Tag 09T8](https://stacks.math.columbia.edu/tag/09T8)
* [Stacks Project, Tag 09T9](https://stacks.math.columbia.edu/tag/09T9)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry

noncomputable section

/-- Flatness over `S` transfers to flatness over `R` along a ring isomorphism `e : R ≃+* S`
through which the two actions on `M` agree. -/
private theorem flat_of_ringEquiv {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    (e : R ≃+* S) [Module S M] [Module R M] (hsmul : ∀ (r : R) (m : M), e r • m = r • m)
    [Module.Flat S M] : Module.Flat R M := by
  let _ : Algebra R S := e.toRingHom.toAlgebra
  have _ : Module.Flat R S :=
    (RingHom.flat_algebraMap_iff (R := R) (S := S)).mp (RingHom.Flat.of_bijective e.bijective)
  have _ : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul hsmul
  exact Module.Flat.trans R S M

/-- **Flatness over a ring transported along a ring isomorphism.** If `e : R ≃+* S` and the two
actions on `M` agree through `e`, then `M` is flat over `R` exactly when it is flat over `S`. -/
private theorem flat_iff_of_ringEquiv {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M]
    (e : R ≃+* S) [Module S M] [Module R M] (hsmul : ∀ (r : R) (m : M), e r • m = r • m) :
    Module.Flat R M ↔ Module.Flat S M := by
  have h' (s : S) (m : M) : e.symm s • m = s • m := by
    simpa using (hsmul (e.symm s) m).symm
  exact ⟨fun _ => flat_of_ringEquiv e.symm h', fun _ => flat_of_ringEquiv e hsmul⟩

/-- Relative flatness at a point is unchanged by composing the morphism with an open immersion
of the target. -/
private theorem flatOverAt_comp_open_iff {X Y S : Scheme.{u}} (f : X ⟶ Y) (j : Y ⟶ S)
    [IsOpenImmersion j] (F : X.Modules) (x : X) :
    IsFlatOverAt (f ≫ j).toLRSHom.toShHom F x ↔ IsFlatOverAt f.toLRSHom.toShHom F x := by
  let R := S.presheaf.stalk (j (f x))
  let A := Y.presheaf.stalk (f x)
  let M := TopCat.Presheaf.stalk F.val.presheaf x
  let e : R ≃+* A := (asIso (j.stalkMap (f x))).commRingCatIsoToRingEquiv
  let _ : Module (X.presheaf.stalk x) M := AlgebraicGeometry.Scheme.Modules.moduleStalk F x
  let _ : Module A M := Module.compHom _ (f.stalkMap x).hom
  let _ : Module R M := Module.compHom _ ((f ≫ j).stalkMap x).hom
  have hsmul (r : R) (m : M) : e r • m = r • m := by
    change (f.stalkMap x).hom ((j.stalkMap (f x)).hom r) • m = ((f ≫ j).stalkMap x).hom r • m
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  change Module.Flat R M ↔ Module.Flat A M
  exact flat_iff_of_ringEquiv e hsmul

/-- Restricting a quasi-coherent module of finite type along an open immersion keeps both
properties. -/
private theorem restrict_isQuasicoherent_and_isFiniteType {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    (F.restrict j).IsQuasicoherent ∧ (F.restrict j).IsFiniteType :=
  ⟨Scheme.Modules.isQuasicoherent_restrictFunctor j F,
    Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_restrict j F⟩

/-- Relative flatness at a point is unchanged by passing to the pushforward along a closed
immersion `i` over which `f` factors as `i ≫ p`. -/
private theorem isFlatOverAt_pushforward_iff_of_isClosedImmersion {X Y S : Scheme.{u}}
    (i : X ⟶ Y) (p : Y ⟶ S) (f : X ⟶ S) (hcomp : i ≫ p = f) [IsClosedImmersion i]
    (F : X.Modules) [F.IsQuasicoherent] (x : X) :
    IsFlatOverAt f.toLRSHom.toShHom F x ↔
      IsFlatOverAt p.toLRSHom.toShHom ((Scheme.Modules.pushforward i).obj F) (i x) :=
  isFlatOverAt_pushforward_iff i p f hcomp F x (by
    rw [← Set.image_singleton, Set.preimage_image_eq _ i.isClosedEmbedding.injective])

/-- **The affine case of the openness assertion.** -/
private theorem isOpen_flatLocus_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite) :
    IsOpen (flatLocus f F) := by
  obtain ⟨X', p, i, hp, hi, hcomp⟩ := exists_finitePresentation_closedImmersion f
  have _ : LocallyOfFinitePresentation p := hp.1
  let F' := (Scheme.Modules.pushforward i).obj F
  have _ : F'.IsFiniteType := (isFiniteType_iff_pushforward_isFiniteType i F).mp inferInstance
  convert (isOpen_flatLocus p F' hS).preimage i.continuous using 1
  ext x
  exact isFlatOverAt_pushforward_iff_of_isClosedImmersion i p f hcomp F x

/-- **Stacks Project, Tag 05IQ (openness).** The locus where a quasi-coherent module of finite
type is flat over the target of a morphism locally of finite type is open, provided the weakly
associated points of the target are locally finite. -/
@[stacks 05IQ "openness of the relative flat locus", sga "3 VIB 13.1" "(i) U open"]
theorem isOpen_flatLocus_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite) :
    IsOpen (flatLocus f F) := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW (W.2.preimage f.continuous)
  let jX : Spec Γ(X, V) ⟶ X := hV.fromSpec
  let jS : Spec Γ(S, W) ⟶ S := hW.fromSpec
  let φ : Γ(S, W) ⟶ Γ(X, V) := f.appLE W V hVW
  let g : Spec Γ(X, V) ⟶ Spec Γ(S, W) := Spec.map φ
  have _ : IsOpenImmersion jX := hV.isOpenImmersion_fromSpec
  have _ : IsOpenImmersion jS := hW.isOpenImmersion_fromSpec
  let G := F.restrict jX
  have _ : LocallyOfFiniteType g :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (f.finiteType_appLE hW hV hVW)
  obtain ⟨_, _⟩ := restrict_isQuasicoherent_and_isFiniteType jX F
  have heq : flatLocus g G = jX ⁻¹' flatLocus f F := by
    ext y
    calc IsFlatOverAt g.toLRSHom.toShHom G y ↔
        IsFlatOverAt (g ≫ jS).toLRSHom.toShHom G y := (flatOverAt_comp_open_iff g jS G y).symm
      _ ↔ IsFlatOverAt (jX ≫ f).toLRSHom.toShHom G y := by
        rw [IsAffineOpen.SpecMap_appLE_fromSpec f hW hV hVW]
      _ ↔ IsFlatOverAt f.toLRSHom.toShHom F (jX y) := isFlatOverAt_restrict_iff jX f F y
  refine ⟨jX '' (flatLocus g G), Set.image_subset_iff.mpr heq.subset, ?_, ?_⟩
  · exact jX.isOpenEmbedding.isOpenMap _ (heq ▸ isOpen_flatLocus_of_isAffine g G
      (exists_finite_schemeWeaklyAssociatedPoints_inter_of_isOpenImmersion jS hS))
  · obtain ⟨y, rfl⟩ : x ∈ Set.range jX := by simpa only [jX, hV.range_fromSpec] using hxV
    exact ⟨y, heq.symm ▸ Set.mem_preimage.mpr hx, rfl⟩

/-- The sections of a sheaf of modules over an empty open subset are trivial, the structure
sheaf being the zero ring there. -/
private theorem subsingleton_sections_of_eq_bot {X : Scheme.{u}} (M : X.Modules) {V : X.Opens}
    (hV : V = ⊥) : Subsingleton Γ(M, V) := by
  subst hV
  exact Module.subsingleton Γ(X, ⊥) _

/-- The stalk of a direct image at a point outside the closed image of the morphism is
trivial: every germ is the germ of a section over an open disjoint from the image, whose
inverse image is empty. -/
private theorem subsingleton_stalk_pushforward {X Y : Scheme.{u}} (i : X ⟶ Y)
    (hi : IsClosed (Set.range i.base)) (F : X.Modules) {y : Y} (hy : y ∉ Set.range i.base) :
    Subsingleton (((Scheme.Modules.pushforward i).obj F).presheaf.stalk y) := by
  let F' := (Scheme.Modules.pushforward i).obj F
  let Z : Y.Opens := ⟨(Set.range i.base)ᶜ, hi.isOpen_compl⟩
  refine subsingleton_of_forall_eq (0 : F'.presheaf.stalk y) fun t => ?_
  obtain ⟨U, hyU, s, rfl⟩ := F'.presheaf.exists_germ_eq t
  have hbot : i ⁻¹ᵁ (U ⊓ Z) = ⊥ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact hx.2 ⟨x, rfl⟩
  have hsub : Subsingleton Γ(F', U ⊓ Z) := subsingleton_sections_of_eq_bot F hbot
  rw [← F'.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ Z ≤ U)) y ⟨hyU, hy⟩ s,
    Subsingleton.elim (F'.presheaf.map (homOfLE (inf_le_left : U ⊓ Z ≤ U)).op s) 0, map_zero]

/-- A quasi-coherent module of finite presentation on the open subscheme `⊤` comes from one on
the whole scheme: the inclusion of `⊤` is a one-element Zariski, hence fpqc, covering. -/
theorem isFinitePresentation_of_restrict_top {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (hF : (F.restrict (⊤ : X.Opens).ι).IsFinitePresentation) :
    F.IsFinitePresentation := by
  let 𝒰open : X.Cover.{u} (Scheme.precoverage @IsOpenImmersion) :=
    Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ => (⊤ : X.Opens).toScheme)
      (fun _ => (⊤ : X.Opens).ι)
      (fun x => ⟨PUnit.unit, ⟨x, trivial⟩, rfl⟩) (fun _ => inferInstance)
  let 𝒰 : X.Cover.{u} Scheme.fpqcPrecoverage :=
    { __ := 𝒰open.toPreZeroHypercover
      mem₀ := Scheme.zariskiPrecoverage_le_fpqcPrecoverage X 𝒰open.mem₀ }
  exact isFinitePresentation_of_pullback_fpqcCover F 𝒰 fun _ =>
    (SheafOfModules.isFinitePresentation (⊤ : X.Opens).toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (⊤ : X.Opens).ι).app F) hF

/-- **The affine case of the relative finite presentation assertion.** -/
private theorem isFinitelyPresentedRelative_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite)
    (hflat : ∀ x : X, IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsFinitelyPresentedRelative f F := by
  obtain ⟨X', p, i, hp, hi, hcomp⟩ := exists_finitePresentation_closedImmersion f
  have _ : LocallyOfFinitePresentation p := hp.1
  let F' := (Scheme.Modules.pushforward i).obj F
  have _ : F'.IsFiniteType := (isFiniteType_iff_pushforward_isFiniteType i F).mp inferInstance
  have hflat' : ∀ x' : X', IsFlatOverAt p.toLRSHom.toShHom F' x' := by
    intro x'
    by_cases hx' : x' ∈ Set.range i.base
    · obtain ⟨x, rfl⟩ := hx'
      exact (isFlatOverAt_pushforward_iff_of_isClosedImmersion i p f hcomp F x).mp (hflat x)
    · exact isFlatOverAt_of_subsingleton_stalk p F' x'
        (subsingleton_stalk_pushforward i hi.isClosedEmbedding.isClosed_range F hx')
  exact (isFinitelyPresentedRelative_pushforward_iff i f p hcomp F).mp
    ((isFinitelyPresentedRelative_iff_isFinitePresentation p F').mpr
      (isFinitePresentation_of_restrict_top F'
        (isFinitePresentation_restrict_of_subset_flatLocus p F' hS ⊤ fun x _ => hflat' x)))

/-- A quasi-coherent module of finite type that is flat over the base at every point of the
source of a morphism locally of finite type is finitely presented relative to the base,
provided the weakly associated points of the target are locally finite. This is the content of
Stacks 05IQ: the flat locus is the open subscheme on which the hypothesis holds. -/
theorem isFinitelyPresentedRelative_of_isFlatOver
    {Y S : Scheme.{u}} (g : Y ⟶ S) [LocallyOfFiniteType g]
    (G : Y.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite)
    (hflat : ∀ y : Y, IsFlatOverAt g.toLRSHom.toShHom G y) :
    IsFinitelyPresentedRelative g G := by
  refine isFinitelyPresentedRelative_of_resLE g G fun V hV W hW hWV => ?_
  have _ : IsAffine W.toScheme := hW
  have _ : IsAffine V.toScheme := hV
  obtain ⟨_, _⟩ := restrict_isQuasicoherent_and_isFiniteType W.ι G
  refine isFinitelyPresentedRelative_of_isAffine (g.resLE V W hWV) (G.restrict W.ι)
    (exists_finite_schemeWeaklyAssociatedPoints_inter_of_isOpenImmersion V.ι hS) fun w => ?_
  rw [← flatOverAt_comp_open_iff (g.resLE V W hWV) V.ι (G.restrict W.ι) w,
    Scheme.Hom.resLE_comp_ι]
  exact (isFlatOverAt_restrict_iff W.ι g G w).mpr (hflat (W.ι w))

/-- **Stacks Project, Tag 05IQ (flatness on the flat locus).** The restriction of the module to
its relative flat locus is flat over the base. -/
@[stacks 05IQ "flatness over the base on the flat locus"]
theorem isFlatOver_flatLocus_of_locallyOfFiniteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite) :
    letI U : X.Opens := ⟨flatLocus f F, isOpen_flatLocus_of_locallyOfFiniteType f F hS⟩
    IsFlatOver (U.ι ≫ f).toLRSHom.toShHom (F.restrict U.ι) :=
  isFlatOver_restrict_of_subset_flatLocus f F _ Set.Subset.rfl

/-- **Stacks Project, Tag 05IQ (relative finite presentation on the flat locus).** The
restriction of the module to its relative flat locus is finitely presented relative to the
base. -/
@[stacks 05IQ "relative finite presentation on the flat locus"]
theorem isFinitelyPresentedRelative_flatLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (hS : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧
      (schemeWeaklyAssociatedPoints S ∩ (W : Set S)).Finite) :
    letI U : X.Opens := ⟨flatLocus f F, isOpen_flatLocus_of_locallyOfFiniteType f F hS⟩
    IsFinitelyPresentedRelative (U.ι ≫ f) (F.restrict U.ι) := by
  set U : X.Opens := ⟨flatLocus f F, isOpen_flatLocus_of_locallyOfFiniteType f F hS⟩
  obtain ⟨_, _⟩ := restrict_isQuasicoherent_and_isFiniteType U.ι F
  exact isFinitelyPresentedRelative_of_isFlatOver (U.ι ≫ f) (F.restrict U.ι) hS
    fun y => (isFlatOverAt_restrict_iff U.ι f F y).mpr y.2

end

end AlgebraicGeometry
