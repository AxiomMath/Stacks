module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Homology.PseudoCoherent.Local
public import StacksFrontier.RingTheory.PseudoCoherentMap.Locality
public import StacksFrontier.RingTheory.PseudoCoherentMap.Quotient
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization
public import StacksFrontier.RingTheory.Syntomic.Morphisms
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public noncomputable section

/-!
# Descent of pseudo-coherence along a faithfully flat syntomic ring map

Let `R → A → A'` be ring maps with `A → A'` syntomic and faithfully flat. If `R → A'` is
pseudo-coherent, then so is `R → A`. This is the whole algebraic content of Tag 0698, the
statement that pseudo-coherence of morphisms of schemes is local on the source for the syntomic
topology.

The argument follows the source. Finite type of `R → A` descends along the faithfully flat map
`A → A'` (Tag 0367), so `A` is a quotient `P ⧸ I` of a polynomial ring `P = R[x_1, …, x_n]`, and
pseudo-coherence of `R → P ⧸ I` is pseudo-coherence of `I` as a `P`-module (Tag 0697). Faithfully
flat descent of pseudo-coherence (Tag 068R) takes place over `P` and not over `R`, so `A'` has to
be lifted to a flat `P`-algebra of finite presentation: Tag 00T0 produces, for each member `g` of
a family of elements generating the unit ideal of `A'`, a relative global complete intersection
`T` over `P` together with an isomorphism `T ⧸ I T ≅ A'_g` of `P`-algebras. Such a `T` is
syntomic over `P` (Tag 00SW), hence flat and of finite presentation, so `Spec T → Spec P` is open
(Tag 01UA); as `Spec A' → Spec A` is surjective and the `Spec A'_g` cover `Spec A'`, the images
of these maps cover the closed subset `V(I)` of `Spec P`. Over a standard open `D(f)` contained
in one of them the map `P_f → T_f` is faithfully flat, so Tag 068R descends pseudo-coherence of
`I T_f` as a `T_f`-module to that of `I P_f` as a `P_f`-module, which by Tag 0697 is
pseudo-coherence of `R → P_f ⧸ I P_f`, that is of `R → (P ⧸ I)_f`. The elements `f` obtained this
way cover `Spec (P ⧸ I)`, and pseudo-coherence of a ring map is local on the target.

## Main definitions

* `StacksDraft.PseudoCoherence.extendScalarsIdealIso`: the base change of an ideal along a flat
  ring map is the ideal it generates.
* `Stacks.PseudoCoherent.quotientMapAwayAlgEquiv`: `P_f ⧸ I P_f` is the localization of `P ⧸ I`
  away from the image of `f`.

## Main results

* `StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_extendScalars_of_faithfullyFlat`:
  **Tag 068R for modules**, pseudo-coherence of a module descends along a faithfully flat ring
  map.
* `Algebra.PseudoCoherent.of_syntomic_faithfullyFlat`: the descent of pseudo-coherence of a ring
  map along a syntomic faithfully flat ring map.

## Implementation notes

*The two helpers about extension of scalars are stated for a bare ring homomorphism.*
`ModuleCat.extendScalars f` builds its tensor product from the algebra structure
`RingHom.toAlgebra f`, which is only propositionally equal to an ambient `Algebra` instance, so
stating `StacksDraft.PseudoCoherence.extendScalarsIdealIso` for a homomorphism and introducing
that algebra structure inside the proof keeps the two descriptions of the carrier syntactically
equal. Tags 066C and 068R are already phrased for a bare homomorphism, so nothing is lost.

*The covering family is taken in `P ⧸ I` rather than in `P`.* The source replaces `X'` by the
disjoint union of the pieces supplied by Tag 00T0 and works with a single lift, which on the
algebra side is a finite product of the `T`. Instead, the set of elements of `P ⧸ I` whose away
localization is pseudo-coherent over `R` is shown to generate the unit ideal, by exhibiting for
each prime of `P ⧸ I` one element of the set outside it; the lifts are then used one at a time
and no product has to be formed.

## References

* [The Stacks Project, Lemma 37.60.13 (0698)](https://stacks.math.columbia.edu/tag/0698)
* [The Stacks Project, Lemma 15.83.14 (0697)](https://stacks.math.columbia.edu/tag/0697)
* [The Stacks Project, Tag 068R](https://stacks.math.columbia.edu/tag/068R)
* [The Stacks Project, Tag 066C](https://stacks.math.columbia.edu/tag/066C)
* [The Stacks Project, Tag 00T0](https://stacks.math.columbia.edu/tag/00T0)
* [The Stacks Project, Lemma 10.136.13 (00SW)](https://stacks.math.columbia.edu/tag/00SW)
* [The Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [The Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
-/

open CategoryTheory TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.PseudoCoherence

/-- Extension of scalars along a flat ring map `f : P → T` carries an ideal `I` of `P` to the
ideal `I T` it generates: the base change `T ⊗_P I` maps onto `I T` always, and injectively
because `T` is flat over `P`. -/
def extendScalarsIdealIso {P T : Type u} [CommRing P] [CommRing T] (f : P →+* T)
    (hf : f.Flat) (I : Ideal P) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of P I) ≅ ModuleCat.of T (I.map f) := by
  letI : Algebra P T := f.toAlgebra
  have hflat : Module.Flat P T := hf
  let l : I →ₗ[P] T := (Algebra.linearMap P T) ∘ₗ I.subtype
  let φ : TensorProduct P T I →ₗ[T] T := LinearMap.liftBaseChange T l
  have hfun : (φ : TensorProduct P T I → T) =
      (TensorProduct.rid P T) ∘ (LinearMap.lTensor T I.subtype) := by
    funext z
    induction z with
    | zero => simp
    | tmul t x => simp [φ, l, Algebra.smul_def, mul_comm]
    | add a b ha hb =>
      simp only [map_add, Function.comp_apply] at *
      rw [ha, hb]
  have hinj : Function.Injective φ := by
    rw [hfun]
    exact (TensorProduct.rid P T).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hrange : LinearMap.range φ = I.map f := by
    rw [show φ = LinearMap.liftBaseChange T l from rfl, LinearMap.range_liftBaseChange]
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro y ⟨x, rfl⟩
      exact Ideal.mem_map_of_mem _ x.2
    · rw [Ideal.map, Ideal.span_le]
      rintro y ⟨x, hx, rfl⟩
      exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  exact (LinearEquiv.ofInjective φ hinj ≪≫ₗ LinearEquiv.ofEq _ _ hrange).toModuleIso

/-- **Stacks 068R for modules.** Pseudo-coherence of a module descends along a faithfully flat
ring map: if the base change `T ⊗_P M` is a pseudo-coherent `T`-module, then `M` is a
pseudo-coherent `P`-module.

This is the complex-level Stacks 068R,
`isPseudoCoherentFrom_and_isPseudoCoherent_of_faithfullyFlat_baseChange`, applied to the complex
concentrated in degree zero with value `M`, whose image in the derived category is the object
tested by `IsModulePseudoCoherent` and whose termwise base change is the complex concentrated in
degree zero with value `T ⊗_P M`. -/
@[sga "6 III 1.10" "clause b), special case"]
theorem isModulePseudoCoherent_of_extendScalars_of_faithfullyFlat
    {P T : Type u} [CommRing P] [CommRing T] (f : P →+* T) (hf : f.FaithfullyFlat)
    (M : ModuleCat.{u} P)
    (h : IsModulePseudoCoherent (R := T) ((ModuleCat.extendScalars.{u, u, u} f).obj M)) :
    IsModulePseudoCoherent (R := P) M := by
  set K := (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M
  have e1 : (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M ≅
      DerivedCategory.Q.obj K :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} P) 0).app M
  have e2 : DerivedCategory.Q.obj
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} T) 0).obj
        ((ModuleCat.extendScalars.{u, u, u} f).obj M) :=
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.extendScalars.{u, u, u} f) (ComplexShape.up ℤ) 0).app M) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} T) 0).app _).symm
  exact IsPseudoCoherent.ofIso
    ((isPseudoCoherentFrom_and_isPseudoCoherent_of_faithfullyFlat_baseChange.{u, u, u}
      f hf K 0).2 (IsPseudoCoherent.ofIso h e2.symm)) e1.symm

/-- Pseudo-coherence of a module depends only on its isomorphism class. -/
theorem IsModulePseudoCoherent.ofIso {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : IsModulePseudoCoherent (R := R) M) : IsModulePseudoCoherent (R := R) N :=
  IsPseudoCoherent.ofIso hM ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso e)

end StacksDraft.PseudoCoherence

namespace Stacks.PseudoCoherent

/-- Localization away from an element commutes with passing to a quotient: for an ideal `I` of
`P` and `f : P`, the quotient of `P_f` by `I P_f` is the localization of `P ⧸ I` away from the
image of `f`.

Both sides are localizations of `P ⧸ I` at the image of the powers of `f`: the left one because
`P_f ⧸ I P_f` is the base change `(P ⧸ I) ⊗_P P_f`, which localizes `P ⧸ I` at the image of the
localizing submonoid. -/
def quotientMapAwayAlgEquiv {P : Type u} [CommRing P] (I : Ideal P) (f : P)
    (Pf : Type u) [CommRing Pf] [Algebra P Pf] [IsLocalization.Away f Pf] :
    (Pf ⧸ I.map (algebraMap P Pf)) ≃ₐ[P ⧸ I]
      Localization.Away (Ideal.Quotient.mk I f) := by
  have hsub : Algebra.algebraMapSubmonoid (P ⧸ I) (Submonoid.powers f) =
      Submonoid.powers (Ideal.Quotient.mk I f) := Submonoid.map_powers _ f
  have h1 : IsLocalization (Algebra.algebraMapSubmonoid (P ⧸ I) (Submonoid.powers f))
      (TensorProduct P (P ⧸ I) Pf) := IsLocalization.tensor Pf (Submonoid.powers f)
  have h2 : IsLocalization (Submonoid.powers (Ideal.Quotient.mk I f))
      (Pf ⧸ I.map (algebraMap P Pf)) := by
    rw [← hsub]
    exact IsLocalization.isLocalization_of_algEquiv _
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Pf I).symm
  exact IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I f)) _ _

/-- If `R → P → S` and `R → S → B` are scalar towers along with `P → S → B`, then so is
`R → P → B`. -/
private theorem isScalarTower_of_tower_of_tower {R P S B : Type*} [CommSemiring R]
    [CommSemiring P] [CommSemiring S] [CommSemiring B] [Algebra R P] [Algebra P S] [Algebra R S]
    [Algebra S B] [Algebra P B] [Algebra R B] [IsScalarTower R P S] [IsScalarTower P S B]
    [IsScalarTower R S B] : IsScalarTower R P B :=
  IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S B, IsScalarTower.algebraMap_apply R P S,
      IsScalarTower.algebraMap_apply P S B]

/-- The localizing base change of `R → P ⧸ I` is pseudo-coherent whenever the standard open
`D(f)` of `Spec P` lies in the image of a flat finitely presented `P`-algebra `T` for which
`R → T ⧸ I T` is pseudo-coherent.

This is the whole localized step of Stacks 0698: Stacks 0697 turns `R → T ⧸ I T` into
pseudo-coherence of `I T` as a `T`-module, Stacks 066C localizes that away from `f`, the map
`P_f → T_f` is faithfully flat because `D(f)` lies in the image of `Spec T → Spec P`, so Stacks
068R descends pseudo-coherence to `I P_f` as a `P_f`-module, and Stacks 0697 read backwards
returns `R → P_f ⧸ I P_f`, which is the localization of `P ⧸ I` away from the image of `f`. -/
private theorem _root_.Algebra.PseudoCoherent.localizationAway_quotient
    {R P T : Type u} [CommRing R] [CommRing P] [CommRing T]
    [Algebra R P] [Algebra P T] [Algebra R T] [IsScalarTower R P T]
    [Module.Flat R P] [Algebra.FinitePresentation R P]
    [Module.Flat P T] [Algebra.FinitePresentation P T]
    (I : Ideal P) (f : P)
    (hopen : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum P)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap P T)))
    (hT : Algebra.PseudoCoherent R (T ⧸ I.map (algebraMap P T))) :
    Algebra.PseudoCoherent R (Localization.Away (Ideal.Quotient.mk I f)) := by
  have hflatRT : Module.Flat R T := Module.Flat.trans R P T
  have hfpRT : Algebra.FinitePresentation R T := Algebra.FinitePresentation.trans R P T
  -- `I T` is a pseudo-coherent `T`-module.
  have hIT : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := T)
      (I.map (algebraMap P T)) :=
    (Algebra.pseudoCoherent_quotient_iff_isModulePseudoCoherent
      (I.map (algebraMap P T))).mp hT
  let Pf := Localization.Away f
  let Tf := Localization.Away (algebraMap P T f)
  have hfpPPf : Algebra.FinitePresentation P Pf := IsLocalization.Away.finitePresentation f
  have hflatPTf : Module.Flat P Tf := Module.Flat.trans P T Tf
  let : Algebra Pf Tf := (IsLocalization.Away.map Pf Tf (algebraMap P T) f).toAlgebra
  have htw : IsScalarTower P Pf Tf := IsScalarTower.of_algebraMap_eq fun x => by
    show _ = IsLocalization.Away.map Pf Tf (algebraMap P T) f (algebraMap P Pf x)
    rw [IsLocalization.Away.map, IsLocalization.map_eq]
    exact IsScalarTower.algebraMap_apply P T Tf x
  have hflatPfTf : Module.Flat Pf Tf :=
    (Module.flat_iff_of_isLocalization Pf (Submonoid.powers f) Tf).mpr hflatPTf
  -- `P_f → T_f` is faithfully flat, because `D(f)` lies in the image of `Spec T → Spec P`.
  have hff : (algebraMap Pf Tf).FaithfullyFlat := by
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨RingHom.flat_algebraMap_iff.mpr hflatPfTf, fun p => ?_⟩
    have hmem : PrimeSpectrum.comap (algebraMap P Pf) p ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum P)) := by
      rw [← PrimeSpectrum.localization_away_comap_range Pf f]
      exact ⟨p, rfl⟩
    have hq : f ∉ (PrimeSpectrum.comap (algebraMap P Pf) p).asIdeal := hmem
    obtain ⟨q, hqeq⟩ := hopen hmem
    obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap T Tf)) := by
      rw [PrimeSpectrum.localization_away_comap_range Tf (algebraMap P T f)]
      exact fun hmem' => hq (by rw [← hqeq]; exact Ideal.mem_comap.mpr hmem')
    refine ⟨q', ?_⟩
    apply PrimeSpectrum.localization_comap_injective Pf (Submonoid.powers f)
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq P Pf Tf,
      IsScalarTower.algebraMap_eq P T Tf, PrimeSpectrum.comap_comp_apply, hq', hqeq]
  -- The two descriptions of `I T_f` as an ideal.
  have hmapeq : (I.map (algebraMap P T)).map (algebraMap T Tf) =
      (I.map (algebraMap P Pf)).map (algebraMap Pf Tf) := by
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq P T Tf,
      ← IsScalarTower.algebraMap_eq P Pf Tf]
  -- Localize away from `f` and descend along `P_f → T_f`.
  have hITf : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := Tf)
      ((I.map (algebraMap P T)).map (algebraMap T Tf)) :=
    StacksDraft.PseudoCoherence.IsModulePseudoCoherent.ofIso
      (StacksDraft.PseudoCoherence.extendScalarsIdealIso (algebraMap T Tf)
        (RingHom.flat_algebraMap_iff.mpr inferInstance) (I.map (algebraMap P T)))
      ((StacksDraft.PseudoCoherence.extensionScalars_preserves_pseudoCoherent
        (algebraMap T Tf) (RingHom.flat_algebraMap_iff.mpr inferInstance)
        (ModuleCat.of T (I.map (algebraMap P T)))).2 hIT)
  rw [hmapeq] at hITf
  have hIPf : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := Pf)
      (I.map (algebraMap P Pf)) :=
    StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_extendScalars_of_faithfullyFlat
      (algebraMap Pf Tf) hff (ModuleCat.of Pf (I.map (algebraMap P Pf)))
      (StacksDraft.PseudoCoherence.IsModulePseudoCoherent.ofIso
        (StacksDraft.PseudoCoherence.extendScalarsIdealIso (algebraMap Pf Tf)
          (RingHom.flat_algebraMap_iff.mpr hflatPfTf) (I.map (algebraMap P Pf))).symm hITf)
  -- Back to a ring map, and identify the quotient with a localization of `P ⧸ I`.
  have hflatRPf : Module.Flat R Pf := Module.Flat.trans R P Pf
  have hfpRPf : Algebra.FinitePresentation R Pf := Algebra.FinitePresentation.trans R P Pf
  have hquot : Algebra.PseudoCoherent R (Pf ⧸ I.map (algebraMap P Pf)) :=
    (Algebra.pseudoCoherent_quotient_iff_isModulePseudoCoherent
      (I.map (algebraMap P Pf))).mpr hIPf
  have htwR : IsScalarTower R (P ⧸ I) (Pf ⧸ I.map (algebraMap P Pf)) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R P (P ⧸ I)]
      show _ = Ideal.Quotient.mk _ (algebraMap P Pf (algebraMap R P r))
      rw [← IsScalarTower.algebraMap_apply R P Pf]
      rfl
  refine hquot.equiv
    (AlgEquiv.ofRingEquiv (f := (quotientMapAwayAlgEquiv I f Pf).toRingEquiv) fun r => ?_)
  rw [IsScalarTower.algebraMap_apply R (P ⧸ I) (Pf ⧸ I.map (algebraMap P Pf)),
    IsScalarTower.algebraMap_apply R (P ⧸ I) (Localization.Away (Ideal.Quotient.mk I f))]
  exact (quotientMapAwayAlgEquiv I f Pf).commutes _

/-- **The ring-level content of Stacks 0698.** Let `R → A → A'` be ring maps with `A → A'`
syntomic and faithfully flat. If `R → A'` is pseudo-coherent, then so is `R → A`.

Finite type of `R → A` descends by Stacks 0367, so `A = P ⧸ I` for a polynomial ring
`P = R[x_1, …, x_n]` and an ideal `I`. Stacks 00T0 lifts `A'` syntomic over `P ⧸ I` to a family
of relative global complete intersections `T` over `P` with `T ⧸ I T` a localization of `A'`,
one for each member of a family of elements generating the unit ideal of `A'`. Each such `T` is
flat and of finite presentation over `P`, so `Spec T → Spec P` is open (Stacks 01UA), and
surjectivity of `Spec A' → Spec A` makes those images cover `V(I)`. On a standard open `D(f)`
inside one of them the localized step applies and gives pseudo-coherence of `R → (P ⧸ I)_f`; the
`f` obtained this way cover `Spec (P ⧸ I)`, so the locality of pseudo-coherence on the target
assembles them into `R → P ⧸ I`. -/
@[ega "IV 17.7.5" "special case"]
theorem _root_.Algebra.PseudoCoherent.of_syntomic_faithfullyFlat
    {R A : Type u} (A' : Type u) [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [Algebra.Syntomic A A'] [Module.FaithfullyFlat A A']
    [h : Algebra.PseudoCoherent R A'] : Algebra.PseudoCoherent R A := by
  classical
  have hffAA' : (algebraMap A A').FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have hfpAA' : (algebraMap A A').FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr inferInstance
  -- `R → A` is of finite type, by descent along the faithfully flat `A → A'`.
  have hftA : Algebra.FiniteType R A := by
    have hc : ((algebraMap A A').comp (algebraMap R A)).FiniteType := by
      rw [← IsScalarTower.algebraMap_eq R A A']
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    exact RingHom.finiteType_algebraMap.mp
      (RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation hc hffAA' hfpAA')
  obtain ⟨n, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hftA
  let P := MvPolynomial (Fin n) R
  let I : Ideal P := RingHom.ker π
  let e : (P ⧸ I) ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective hπ
  suffices hPI : Algebra.PseudoCoherent R (P ⧸ I) from hPI.equiv e
  -- Regard `A` and `A'` as algebras over `P ⧸ I` and over `P`.
  let : Algebra (P ⧸ I) A := e.toRingEquiv.toRingHom.toAlgebra
  let : Algebra (P ⧸ I) A' := ((algebraMap A A').comp e.toRingEquiv.toRingHom).toAlgebra
  have : IsScalarTower (P ⧸ I) A A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R (P ⧸ I) A' := by
    refine IsScalarTower.of_algebraMap_eq (R := R) (S := P ⧸ I) (A := A') fun r => ?_
    show algebraMap R A' r = algebraMap A A' (e (algebraMap R (P ⧸ I) r))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply R A A']
  let : Algebra P A' := ((algebraMap (P ⧸ I) A').comp (algebraMap P (P ⧸ I))).toAlgebra
  have : IsScalarTower P (P ⧸ I) A' :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := P ⧸ I) (A := A') fun _ => rfl
  have htwRPA' : IsScalarTower R P A' := by
    exact isScalarTower_of_tower_of_tower (S := P ⧸ I)
  -- `A'` is syntomic over `P ⧸ I`, since `P ⧸ I ≃ A`.
  have : Algebra.Smooth (P ⧸ I) A := Algebra.Smooth.of_equiv
    (show (P ⧸ I) ≃ₐ[P ⧸ I] A from { e.toRingEquiv with commutes' := fun _ => rfl })
  have : Algebra.Syntomic (P ⧸ I) A := Algebra.Smooth.syntomic _ _
  have : Algebra.Syntomic (P ⧸ I) A' := Algebra.Syntomic.comp (P ⧸ I) A A'
  obtain ⟨s, hs, hgs⟩ :=
    Algebra.Syntomic.exists_span_eq_top_algEquiv_quotient (R := P) I (S := A')
  -- The elements of `P ⧸ I` whose away localization is pseudo-coherent over `R`.
  let G : Set (P ⧸ I) := {a | Algebra.PseudoCoherent R (Localization.Away a)}
  have hGtop : Ideal.span G = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hGm⟩ := Ideal.exists_le_maximal _ hne
    let q : PrimeSpectrum (P ⧸ I) := ⟨m, hm.isPrime⟩
    -- `Spec A' → Spec (P ⧸ I)` is surjective.
    have hffPIA' : (algebraMap (P ⧸ I) A').FaithfullyFlat :=
      RingHom.FaithfullyFlat.stableUnderComposition e.toRingEquiv.toRingHom (algebraMap A A')
        (RingHom.FaithfullyFlat.of_bijective e.bijective) hffAA'
    obtain ⟨p', hp'⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hffPIA').2 q
    -- One of the generators of the unit ideal of `A'` avoids `p'`.
    obtain ⟨g, hgmem, hgnot⟩ : ∃ g ∈ s, g ∉ p'.asIdeal := by
      by_contra hc
      refine p'.isPrime.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr fun x hx => ?_))
      exact not_not.mp fun hn => hc ⟨x, hx, hn⟩
    obtain ⟨T, instT, instPT, hgci, ⟨ε⟩⟩ := hgs g hgmem
    have : Algebra.Syntomic P T := Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection P T
    let : Algebra R T := ((algebraMap P T).comp (algebraMap R P)).toAlgebra
    have : IsScalarTower R P T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    -- `Spec T → Spec P` is open, and its image contains the point `q`.
    have hU : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap P T))) := by
      rw [← Set.image_univ]
      exact primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation P T _ isOpen_univ
    obtain ⟨pg, hpg⟩ : p' ∈ Set.range
        (PrimeSpectrum.comap (algebraMap A' (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hgnot
    have hkey : PrimeSpectrum.comap (algebraMap P (P ⧸ I)) q ∈
        Set.range (PrimeSpectrum.comap (algebraMap P T)) := by
      refine ⟨PrimeSpectrum.comap (algebraMap T (T ⧸ I.map (algebraMap P T)))
        (PrimeSpectrum.comap ε.toRingEquiv.toRingHom pg), ?_⟩
      rw [← PrimeSpectrum.comap_comp_apply,
        ← IsScalarTower.algebraMap_eq P T (T ⧸ I.map (algebraMap P T)),
        ← PrimeSpectrum.comap_comp_apply,
        show ε.toRingEquiv.toRingHom.comp (algebraMap P (T ⧸ I.map (algebraMap P T))) =
          algebraMap P (Localization.Away g) from RingHom.ext ε.commutes,
        IsScalarTower.algebraMap_eq P A' (Localization.Away g),
        PrimeSpectrum.comap_comp_apply, hpg, IsScalarTower.algebraMap_eq P (P ⧸ I) A',
        PrimeSpectrum.comap_comp_apply, hp']
    -- Shrink to a standard open `D(f)` inside that image.
    obtain ⟨V, hVb, hmemV, hVU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hkey hU
    obtain ⟨f, rfl⟩ := hVb
    -- `R → T ⧸ I T` is pseudo-coherent, being `R → A'_g` up to an isomorphism over `P`.
    have : IsScalarTower R P (Localization.Away g) :=
      isScalarTower_of_tower_of_tower (S := A')
    have : IsScalarTower R P (T ⧸ I.map (algebraMap P T)) :=
      isScalarTower_of_tower_of_tower (S := T)
    have hTq : Algebra.PseudoCoherent R (T ⧸ I.map (algebraMap P T)) := by
      refine Algebra.PseudoCoherent.equiv
        (h.trans (Algebra.PseudoCoherent.of_isLocalizationAway (Localization.Away g) g))
        (AlgEquiv.ofRingEquiv (f := ε.toRingEquiv.symm) fun r => ?_)
      rw [IsScalarTower.algebraMap_apply R P (Localization.Away g),
        IsScalarTower.algebraMap_apply R P (T ⧸ I.map (algebraMap P T))]
      exact ε.symm.commutes _
    -- The localized step, and the contradiction with maximality of `m`.
    have hpc : Algebra.PseudoCoherent R (Localization.Away (Ideal.Quotient.mk I f)) :=
      Algebra.PseudoCoherent.localizationAway_quotient I f hVU hTq
    exact hmemV (Ideal.mem_comap.mpr (hGm (Ideal.subset_span hpc)))
  obtain ⟨t, hts, ht1⟩ := Submodule.mem_span_finite_of_mem_span
    (show (1 : P ⧸ I) ∈ Ideal.span G from hGtop ▸ Submodule.mem_top)
  refine Algebra.PseudoCoherent.of_span_eq_top_target
    (fun a : ((t : Set (P ⧸ I))) => (a : P ⧸ I)) ?_ fun a => hts a.2
  rwa [Ideal.eq_top_iff_one, Subtype.range_coe]

end Stacks.PseudoCoherent

end
