module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentHomDescentZariskiLeaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentZariskiSchemeHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentZariskiTorTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectFullyFaithfulStages
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentedDerivedPullbackComparisonConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.ShiftAndVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands

/-!
# Stacks 0DKV from the comparison of derived pullbacks under `ε^*`

The proof of Stacks 0DKV reduces the conclusion for `(K₀, L₀)` to affine situations by
`AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_canonical_of_restrict_affine`:
for an étale `g : U₀ ⟶ X₀` with `U₀` affine whose composite to `Y₀` factors as `t ≫ w` through
an étale `w : V ⟶ Y₀` from an affine `V`, the conclusion for `(Lg^*K₀[n], Lg^*L₀)` in the
situation restricted along `g`.  This file proves that leaf, and with it Stacks 0DKV, from the
coherent identification of the small étale and Zariski derived pullbacks under `ε^*`,
`Φ : AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison B S hS canonical`.  That datum
is `AlgebraicGeometry.Space.representedDerivedPullbackComparisonCanonical`, built from the
underived compatibility of `h^*ε^* ≅ ε^*r^*` with the compositors on homotopy categories,
`AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence` (internal, pending), which is the
only hypothesis left.

On the leaf, `U₀` and `V` are read through spectra `Spec A ≅ U₀` and `Spec R ≅ V` with
`t : Spec A ⟶ Spec R` the morphism of an `R`-algebra.  The pullbacks of `K₀` and `L₀` to the
model are `ε^*K''` and `ε^*L''` for `K'', L'' ∈ D_QCoh(𝒪_{Spec A})` (Stacks 071Q, 08F4), `ε^*` is
bijective on their derived homomorphisms (Stacks 071Q, 08DW), and the Zariski form of the
conclusion is the case of schemes, Stacks 0DI7, whose hypotheses are: `K''` pseudo-coherent
(Stacks 08H4 for the pullback, 08HE for `ε^*`), `L''` with quasi-coherent cohomology, flatness and
finite presentation of `t` (Stacks 03ML, 03XP), and the Tor hypothesis, read off the Tor clause of
`L₀` (`RelativeDescentSituation.zariskiModelHomDescent_of_hasLocallyFiniteTorDimensionAlong`).

Nothing here is registered.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherentObject_shift`: shifts of pseudo-coherent objects of
  `D(𝒪_X)` are pseudo-coherent.
* `AlgebraicGeometry.Space.isPseudoCoherent_of_zariskiEtaleDerived_iso`: if `ε^*E₀` is a pullback
  of a pseudo-coherent object, then `E₀` is pseudo-coherent on the underlying scheme.
* `AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_restrict_of_specModel`: the leaf on
  given Spec models.
* `AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_restrict_of_comparison`:
  the leaf, in the form of the reduction.
* `AlgebraicGeometry.Space.RelativeDescentSituation.homDescentOfPseudoCoherent_of_comparison`:
  Stacks 0DKV (`h0DKV`) from `Φ`.
* `AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectFullyFaithful_of_comparison`:
  clauses (4) and (5) of Stacks 0DKW from `Φ`.
* `RelativeDescentSituation.homDescentOfPseudoCoherent_of_homotopyPullbackCoherence`
  and `relativelyPerfectFullyFaithful_of_homotopyPullbackCoherence`: the same from
  `AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence` alone.

## Implementation notes

The leaf is proved for an arbitrary pseudofunctoriality datum `P` and comparison datum `Φ`; the
canonical datum `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` is substituted
only in the last step, as in `RelativeDescentHomDescentZariski.lean`.  The index type lives in
universe `u`, that of Stacks 0DI7.

## References

* [Stacks Project, Tag 0DKV](https://stacks.math.columbia.edu/tag/0DKV)
* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Pseudo-coherence on the affine model -/

section PseudoCoherence

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The shifts of a pseudo-coherent object of `D(𝒪_X)` are pseudo-coherent**: `E[n]` is
`(m - n)`-pseudo-coherent when `E` is `m`-pseudo-coherent (Stacks 08FV), and pseudo-coherence is
`m`-pseudo-coherence for every `m` (Stacks 08FU (2)). -/
theorem isPseudoCoherentObject_shift {X : AlgebraicSpaces B S hS} (E : derivedModules B S hS X)
    (hE : IsPseudoCoherentObject E) (n : ℤ) : IsPseudoCoherentObject (E⟦n⟧) := by
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m => ?_
  have h := (RingedSite.isPseudoCoherentFrom_shift_iff _ (m + n) n E).2
    ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ E).1 hE (m + n))
  rwa [add_sub_cancel_right] at h

/-- **Pseudo-coherence on the scheme underlying an object of the site, from a pullback.**  If
`ε^*E₀ ≅ Lf^*E` for a morphism `f : h_U ⟶ X` of algebraic spaces and a pseudo-coherent
`E ∈ D(𝒪_X)`, then `E₀` is pseudo-coherent on the scheme underlying `U`: `Lf^*E` is
pseudo-coherent (Stacks 08H4), and pseudo-coherence descends along `ε^*` (Stacks 08HE). -/
theorem isPseudoCoherent_of_zariskiEtaleDerived_iso {X : AlgebraicSpaces B S hS}
    (U : BigFppfOver B S hS)
    (f : (schemeSpace U : AlgebraicSpaces B S hS) ⟶ X)
    (E : derivedModules B S hS X) (hE : IsPseudoCoherentObject E)
    (E₀ : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace)))
    (a : (zariskiEtaleDerived B S hS U).obj E₀ ≅ (smallEtaleDerivedModulePullback B S hS f).obj E) :
    RingedSpace.IsPseudoCoherent (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) E₀ := by
  obtain ⟨P, hP, ⟨e⟩⟩ := isPseudoCoherent_smallEtaleDerivedModulePullback f E hE
  exact isPseudoCoherent_of_representedDerivedAssociatedModule B S hS U E₀ ⟨P, hP, ⟨e ≪≫ a.symm⟩⟩

end PseudoCoherence

/-! ### The leaf -/

namespace RelativeDescentSituation

section Leaf

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 6000] preadditive_smallEtaleModules_model

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance] isDirected_laterIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : RelativeDescentSituation B S hS hZ I}

/-- **The affine leaf of Stacks 0DKV on given Spec models**, from a comparison datum `Φ`.  Let
`g : U₀ ⟶ X₀` and `w : V ⟶ Y₀` be étale with `t ≫ w = g ≫ p₀`, read through
`e₀ : h_{Spec A} ≅ U₀` and `e_V : h_{Spec R} ≅ V` with `t` the morphism of an `R`-algebra `A`.
For `K` pseudo-coherent on `U₀` and `L₀ ∈ D_QCoh(𝒪_{X₀})` locally of finite Tor dimension over
`Y₀`, the conclusion of the tag holds for `(K, Lg^*L₀)` in the situation restricted along `g`. -/
theorem homDescent_restrict_of_specModel
    {P : DerivedPullbackComposition B S hS} (Φ : RepresentedDerivedPullbackComparison B S hS P)
    (hD : D.IsSchemeLimit) {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU₀ : IsAlgebraicSpace B S hS U₀) (g : U₀ ⟶ D.X₀)
    (hg : IsEtale B S hS g) (hgflat : IsFlat B S hS g) (hgfp : IsFinitePresentation B S hS g)
    {V : AlgebraicSpaces B S hS} (w : V ⟶ D.initialTarget) (t : U₀ ⟶ V.1)
    (hw : IsEtale B S hS w.hom) (ht : t ≫ w.hom = g ≫ D.p₀)
    {R : Type u} [CommRing R] {hR : B.Contains (Spec (CommRingCat.of R))}
    {gR : B.obj hR ⟶ B.obj hS} {A : Type u} [CommRing A] [Algebra R A]
    {hA : B.Contains (Spec (CommRingCat.of A))} {gA : B.obj hA ⟶ B.obj hS}
    (wA : (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap R A))) :
      B.obj hA ⟶ B.obj hR) ≫ gR = gA)
    (e₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specAffineFppf hA gA)) ≅ U₀)
    (eV : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (specAffineFppf hR gR)) ≅ V.1)
    (ht' : yoneda.map (specFppfOverMap B S hS hR gR hA gA wA) ≫ eV.hom = e₀.hom ≫ t)
    (K : (D.restrict hU₀ g hgflat hgfp).InitialDerived) (hK : IsPseudoCoherentObject K)
    (L₀ : D.InitialDerived) (hL₀ : IsInQuasicoherentDerived D.initialSource L₀)
    (hL₀tor : HasLocallyFiniteTorDimensionAlong D.initialStructure L₀) :
    (D.restrict hU₀ g hgflat hgfp).HomDescent P K
      ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀ g hgflat hgfp)).obj L₀) := by
  let Rep := (D.restrict hU₀ g hgflat hgfp).affineBaseChangeRepresentation (specAffineFppf hA gA)
    (e₀.hom ≫ (D.restrict hU₀ g hgflat hgfp).p₀) hD.1
  refine homDescent_of_zariskiModelHomDescent_of_quasicoherent (e₀ := e₀) Φ Rep K _
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS _ _ K hK)
    (derivedQuasicoherent_smallEtaleDerivedModulePullback B S hS _ L₀ hL₀)
    fun K'' L'' _ hL'' a b => ?_
  exact zariskiModelHomDescent_of_hasLocallyFiniteTorDimensionAlong hD hU₀ g hg hgflat hgfp w t
    hw ht wA e₀ eV ht' Rep K'' L'' (isPseudoCoherent_of_zariskiEtaleDerived_iso _
      (modelInitialHom (D := D.restrict hU₀ g hgflat hgfp) e₀) K hK K'' a) hL'' L₀ hL₀tor b

/-- **The affine leaf of Stacks 0DKV**, in the form consumed by the reduction
`AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_canonical_of_restrict_affine`,
from a comparison datum `Φ`, for `K₀` pseudo-coherent and `L₀ ∈ D_QCoh(𝒪_{X₀})` locally of
finite Tor dimension over `Y₀`.  The affine `U₀` and `V` are spectra
(`AlgebraicGeometry.Space.exists_specFppfOver_iso_of_isAffineSpace`) and `t` is the morphism of
a ring map (`AlgebraicGeometry.Space.exists_algebra_specFppfOverMap_eq`); the shifts of
`Lg^*K₀` are pseudo-coherent (Stacks 08H4, 08FV). -/
theorem shiftedHomDescent_restrict_of_comparison
    {P : DerivedPullbackComposition B S hS} (Φ : RepresentedDerivedPullbackComparison B S hS P)
    (hD : D.IsSchemeLimit) (K₀ L₀ : D.InitialDerived) (hK₀ : IsPseudoCoherentObject K₀)
    (hL₀ : IsInQuasicoherentDerived D.initialSource L₀)
    (hL₀tor : HasLocallyFiniteTorDimensionAlong D.initialStructure L₀)
    {U₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU₀ : IsAffineSpace B S hS U₀)
    (g : U₀ ⟶ D.X₀) (hg : IsEtale B S hS g)
    {V : AlgebraicSpaces B S hS} (w : V ⟶ D.initialTarget) (t : U₀ ⟶ V.1)
    (hV : IsAffineSpace B S hS V.1) (hw : IsEtale B S hS w.hom) (ht : t ≫ w.hom = g ≫ D.p₀) :
    (D.restrict hU₀.isAlgebraicSpace g (D.isFlat_of_isEtale_affine hg)
        (D.isFinitePresentation_of_isEtale_affine hU₀ hg)).ShiftedHomDescent P
      ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀.isAlgebraicSpace g
        (D.isFlat_of_isEtale_affine hg) (D.isFinitePresentation_of_isEtale_affine hU₀ hg))).obj K₀)
      ((smallEtaleDerivedModulePullback B S hS (D.restrictInitial hU₀.isAlgebraicSpace g
        (D.isFlat_of_isEtale_affine hg)
        (D.isFinitePresentation_of_isEtale_affine hU₀ hg))).obj L₀) := by
  intro n
  obtain ⟨A, _, hA, gA, ⟨e₀⟩⟩ := exists_specFppfOver_iso_of_isAffineSpace hU₀
  obtain ⟨R, _, hR, gR, ⟨eV⟩⟩ := exists_specFppfOver_iso_of_isAffineSpace hV
  obtain ⟨_, wA, htt⟩ := exists_algebra_specFppfOverMap_eq
    (yoneda.preimage (e₀.hom ≫ t ≫ eV.inv))
  have ht' : yoneda.map (specFppfOverMap B S hS hR gR hA gA wA) ≫ eV.hom = e₀.hom ≫ t := by
    rw [htt, Functor.map_preimage, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  exact homDescent_restrict_of_specModel Φ hD hU₀.isAlgebraicSpace g hg _ _ w t hw ht wA
    e₀ eV ht' _ (isPseudoCoherentObject_shift _
      (isPseudoCoherent_smallEtaleDerivedModulePullback _ K₀ hK₀) n) L₀ hL₀ hL₀tor

end Leaf

/-! ### Stacks 0DKV and the full faithfulness in Stacks 0DKW -/

section Assembly

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

variable (I) in
/-- **Stacks 0DKV from the comparison of derived pullbacks under `ε^*`**: the hom-descent output
`h0DKV` consumed by
`RelativeDescentSituation.relativelyPerfectFullyFaithful_of_homDescentOfPseudoCoherent`,
for index types in universe `u` (that of Stacks 0DI7), from
`Φ : AlgebraicGeometry.Space.RepresentedDerivedPullbackComparison B S hS canonical`, the coherent
comparison of the small étale and Zariski derived pullbacks under `ε^*` (it is
`AlgebraicGeometry.Space.representedDerivedPullbackComparisonCanonical` of the pending
`AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence`).

The reduction to affine situations
(`AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_canonical_of_restrict_affine`)
is fed with the leaf
`AlgebraicGeometry.Space.RelativeDescentSituation.shiftedHomDescent_restrict_of_comparison` at
the canonical datum, and read at the shift `0`. -/
theorem homDescentOfPseudoCoherent_of_comparison
    (Φ : RepresentedDerivedPullbackComparison B S hS
      (DerivedPullbackComposition.canonical B S hS)) :
    HomDescentOfPseudoCoherent B S hS hZ I := fun D hD K₀ L₀ hK₀ hL₀ hL₀tor =>
  homDescent_of_iso (DerivedPullbackComposition.canonical B S hS)
    ((shiftFunctorZero D.InitialDerived ℤ).app K₀)
    (D.shiftedHomDescent_canonical_of_restrict_affine K₀ L₀
      (fun {_} hU₀ g hg {_} w t hV hw ht => shiftedHomDescent_restrict_of_comparison Φ hD
        K₀ L₀ hK₀ hL₀ hL₀tor hU₀ g hg w t hV hw ht) 0)

/-- **Fullness and faithfulness in Stacks 0DKW (clauses (4) and (5)) from the comparison of
derived pullbacks under `ε^*`**: the comparison datum `Φ` at the canonical pseudofunctoriality
datum gives Stacks 0DKV
(`AlgebraicGeometry.Space.RelativeDescentSituation.homDescentOfPseudoCoherent_of_comparison`),
which gives clauses (4) and (5) of Stacks 0DKW. -/
theorem relativelyPerfectFullyFaithful_of_comparison
    (D : RelativeDescentSituation B S hS hZ I)
    (Φ : RepresentedDerivedPullbackComparison B S hS
      (DerivedPullbackComposition.canonical B S hS)) :
    D.RelativelyPerfectFullyFaithful :=
  D.relativelyPerfectFullyFaithful_of_homDescentOfPseudoCoherent
    (homDescentOfPseudoCoherent_of_comparison I Φ)

variable (I) in
/-- **Stacks 0DKV from the underived compatibility of `h^*ε^* ≅ ε^*r^*` with the compositors**
(`hcoh : AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence B S hS`, internal,
pending): the hom-descent output `h0DKV`, for index types in universe `u`, with the comparison
datum `AlgebraicGeometry.Space.representedDerivedPullbackComparisonCanonical hcoh`. -/
theorem homDescentOfPseudoCoherent_of_homotopyPullbackCoherence
    (hcoh : RepresentedHomotopyPullbackCoherence B S hS) :
    HomDescentOfPseudoCoherent B S hS hZ I :=
  homDescentOfPseudoCoherent_of_comparison I (representedDerivedPullbackComparisonCanonical hcoh)

/-- **Fullness and faithfulness in Stacks 0DKW (clauses (4) and (5)) from the underived
compatibility of `h^*ε^* ≅ ε^*r^*` with the compositors**
(`hcoh : AlgebraicGeometry.Space.RepresentedHomotopyPullbackCoherence B S hS`, internal,
pending), through
`RelativeDescentSituation.homDescentOfPseudoCoherent_of_homotopyPullbackCoherence`. -/
theorem relativelyPerfectFullyFaithful_of_homotopyPullbackCoherence
    (D : RelativeDescentSituation B S hS hZ I)
    (hcoh : RepresentedHomotopyPullbackCoherence B S hS) :
    D.RelativelyPerfectFullyFaithful :=
  D.relativelyPerfectFullyFaithful_of_comparison
    (representedDerivedPullbackComparisonCanonical hcoh)

end Assembly

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
