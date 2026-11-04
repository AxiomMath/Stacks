module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.TrivialityExample
public import StacksFrontier.AlgebraicGeometry.Modules.FreeMapIsoLocus
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs

/-!
# The generic fibre and the rank of global sections

Let `A` be a local domain and `f : X ⟶ Spec A` universally closed. A finite locally free module
`E` which is free of rank `r'` on the generic fibre `X_η` and free of rank `r` on a thickening
`Xₙ`, `n ≥ 1`, has `r = r'` as soon as `X_η` is nonempty: a point of `X_η` specializes, since `f`
is closed, to a point of the special fibre, and both lie in one open trivializing `E`. Hence
`E|_{X_η} ≅ 𝒪_X^r|_{X_η}` in every case.

By flat base change in degree zero along `Spec κ(η) ⟶ Spec A`, `Γ(X_η, F|_{X_η})` is
`κ(η) ⊗ Γ(X, F)`, so two quasi-coherent modules with isomorphic restrictions to `X_η` have global
sections of the same rank.

## Main results

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `eq_of_iso_free`: on a nonempty scheme the rank of a free module of finite rank is determined.
* `rank_genericFibre_eq`: `r = r'` when the generic fibre is nonempty.
* `nonempty_genericFibreRestrict_iso_free`: `E|_{X_η} ≅ 𝒪_X^r|_{X_η}`.
* `finrank_cohomologyOver_zero_eq_of_genericFibre_iso`: **equal ranks of global sections.**

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

/-! ### The rank of a free module -/

/-- **On a nonempty scheme the rank of a free module of finite rank is determined**, read on
global sections, which form a free module over the nonzero ring `Γ(T, ⊤)`. -/
theorem eq_of_iso_free {T : Scheme.{u}} [Nonempty T] {a b : ℕ}
    (e : (SheafOfModules.free.{u} (R := T.ringCatSheaf) (ULift.{u} (Fin a))) ≅
      SheafOfModules.free.{u} (R := T.ringCatSheaf) (ULift.{u} (Fin b))) : a = b := by
  obtain ⟨t⟩ := ‹Nonempty T›
  have : Nontrivial Γ(T, ⊤) := RingHom.domain_nontrivial (T.presheaf.Γgerm t).hom
  let L := ((moduleGlobalSectionsFreeIso T a).symm ≪≫ (moduleGlobalSections T).mapIso e ≪≫
    moduleGlobalSectionsFreeIso T b).toLinearEquiv
  simpa using L.finrank_eq

/-- A module free of rank `a` after pullback along `h` is free of rank `a` after pullback along
`g ≫ h`. -/
def pullbackCompIsoFree {T Y X : Scheme.{u}} (g : T ⟶ Y) (h : Y ⟶ X) {E : X.Modules} {a : ℕ}
    (e : (Scheme.Modules.pullback h).obj E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin a))) :
    (Scheme.Modules.pullback (g ≫ h)).obj E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin a)) :=
  (Scheme.Modules.pullbackComp g h).symm.app E ≪≫ (Scheme.Modules.pullback g).mapIso e ≪≫
    Scheme.Modules.pullbackFreeIso g _

/-- **Two trivializations seen from a common nonempty scheme have the same rank.** -/
theorem eq_of_pullback_iso_free {T Y₁ Y₂ X : Scheme.{u}} [Nonempty T] {E : X.Modules}
    (g₁ : T ⟶ Y₁) (h₁ : Y₁ ⟶ X) (g₂ : T ⟶ Y₂) (h₂ : Y₂ ⟶ X) (hw : g₁ ≫ h₁ = g₂ ≫ h₂) {a b : ℕ}
    (e₁ : (Scheme.Modules.pullback h₁).obj E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin a)))
    (e₂ : (Scheme.Modules.pullback h₂).obj E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin b))) :
    a = b :=
  eq_of_iso_free ((pullbackCompIsoFree g₁ h₁ e₁).symm ≪≫ eqToIso (by rw [hw]) ≪≫
    pullbackCompIsoFree g₂ h₂ e₂)

/-- A trivialization of `E` over an open `V`, read as a pullback along the inclusion of `V`. -/
def pullbackOpenIsoFree {X : Scheme.{u}} {E : X.Modules} (V : X.Opens) {I : Type u} [Finite I]
    (e : E.restrict V.ι ≅ SheafOfModules.free.{u} I) :
    (Scheme.Modules.pullback V.ι).obj E ≅
      SheafOfModules.free.{u} (ULift.{u} (Fin (Nat.card I))) :=
  (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm.app E ≪≫ e ≪≫
    (SheafOfModules.freeFunctor (R := (V : Scheme.{u}).ringCatSheaf)).mapIso
      ((Finite.equivFin I).trans Equiv.ulift.symm).toIso

/-- A morphism from the spectrum of a residue field whose point lies in `V` factors through `V`;
the two trivializations then have the same rank. -/
theorem eq_card_of_residueField {Y X : Scheme.{u}} (h : Y ⟶ X) (y : Y) {E : X.Modules} {a : ℕ}
    (e₁ : (Scheme.Modules.pullback h).obj E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin a)))
    (V : X.Opens) (hyV : h y ∈ V) {I : Type u} [Finite I]
    (e₂ : E.restrict V.ι ≅ SheafOfModules.free.{u} I) : a = Nat.card I := by
  have hrange : Set.range (Y.fromSpecResidueField y ≫ h) ⊆ Set.range V.ι := by
    rintro _ ⟨s, rfl⟩
    rwa [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply, Scheme.Opens.range_ι]
  exact eq_of_pullback_iso_free (Y.fromSpecResidueField y) h
    (IsOpenImmersion.lift V.ι _ hrange) V.ι (IsOpenImmersion.lift_fac _ _ hrange).symm e₁
    (pullbackOpenIsoFree V e₂)

/-! ### The ranks on the generic fibre and on a thickening agree -/

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A))

omit [IsDomain A] in
/-- The closed point of `Spec (A ⧸ 𝔪ⁿ)` lies over the closed point of `Spec A`, for `n ≥ 1`. -/
theorem exists_thickening_point {n : ℕ} (hn : 1 ≤ n) :
    ∃ w : Spec (CommRingCat.of (A ⧸ IsLocalRing.maximalIdeal A ^ n)),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n))) w =
        IsLocalRing.closedPoint A := by
  have hne : IsLocalRing.maximalIdeal A ^ n ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (top_le_iff.1 (h ▸ Ideal.pow_le_self (by omega)))
  have : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ n) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (A ⧸ IsLocalRing.maximalIdeal A ^ n)
  refine ⟨⟨M, hM.isPrime⟩, ?_⟩
  have hmax : (M.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n))).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

/-- **The rank on the generic fibre is the rank on a thickening.** Let `f` be universally closed
over a local domain, `E` finite locally free, free of rank `r'` on the generic fibre and of rank
`r` on the thickening `Xₙ`, `n ≥ 1`. If the generic fibre is nonempty, `r = r'`. -/
theorem rank_genericFibre_eq [UniversallyClosed f] (E : X.Modules) (hE : E.IsFiniteLocallyFree)
    {r r' n : ℕ} (hn : 1 ≤ n)
    (eη : genericFibreRestrict A f E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r')))
    (en : thickeningRestrict A f n E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r)))
    (z : genericFibre A f) : r' = r := by
  set η := genericPoint (Spec (CommRingCat.of A))
  set x := f.fiberι η z
  have hcl := f.isClosedMap _ (isClosed_closure (s := ({x} : Set X)))
  obtain ⟨y, hy, hfy⟩ : IsLocalRing.closedPoint A ∈ f '' closure {x} :=
    (IsLocalRing.specializes_closedPoint (f x)).mem_closed hcl ⟨x, subset_closure rfl, rfl⟩
  obtain ⟨V, hyV, I, hI, ⟨eV⟩⟩ := hE y
  have hxV : x ∈ V := (specializes_iff_mem_closure.2 hy).mem_open V.isOpen hyV
  have h₁ : r' = Nat.card I := eq_card_of_residueField (f.fiberι η) z eη V hxV eV
  obtain ⟨w, hw⟩ := exists_thickening_point A hn
  obtain ⟨y', hy'₁, -⟩ := Scheme.Pullback.exists_preimage_pullback y w (hfy.trans hw.symm)
  have h₂ : r = Nat.card I := eq_card_of_residueField _ y' en V (by rwa [hy'₁]) eV
  exact h₁.trans h₂.symm

/-- **`E|_{X_η} ≅ 𝒪_X^r|_{X_η}`** for `E` as in `rank_genericFibre_eq`: if the generic fibre is
empty both sides are zero, and else the two ranks agree. -/
theorem nonempty_genericFibreRestrict_iso_free [UniversallyClosed f] (E : X.Modules)
    (hE : E.IsFiniteLocallyFree) {r r' n : ℕ} (hn : 1 ≤ n)
    (eη : genericFibreRestrict A f E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r')))
    (en : thickeningRestrict A f n E ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) :
    Nonempty (genericFibreRestrict A f E ≅
      genericFibreRestrict A f (SheafOfModules.free.{u} (ULift.{u} (Fin r)))) := by
  by_cases h : Nonempty (genericFibre A f)
  · obtain ⟨z⟩ := h
    obtain rfl := rank_genericFibre_eq A f E hE hn eη en z
    exact ⟨eη ≪≫ (Scheme.Modules.pullbackFreeIso _ _).symm⟩
  · have : IsEmpty (genericFibre A f) := not_nonempty_iff.1 h
    have hz : ∀ M : (genericFibre A f).Modules, IsZero M := fun M =>
      (Scheme.Modules.isZero_iff_supp_eq_empty M).2 (Set.eq_empty_of_isEmpty _)
    exact ⟨(hz _).iso (hz _)⟩

/-! ### Global sections over the generic fibre -/

open Stacks.AlgebraicGeometry.SectionsBaseChange in
omit [IsLocalRing A] in
/-- The ring map `Γ(Spec A, ⊤) ⟶ Γ(Spec κ(η), ⊤)` at the generic point of a domain is
injective: it is the germ at the generic point, which is injective on an integral scheme,
followed by the residue map of a field and isomorphisms. -/
theorem injective_appTop_fromSpecResidueField_genericPoint :
    Function.Injective ((Spec (CommRingCat.of A)).fromSpecResidueField
      (genericPoint (Spec (CommRingCat.of A)))).appTop := by
  have key : ∀ {Y : Scheme.{u}} {U V : Y.Opens} (h : U ≤ V), V ≤ U →
      Function.Injective (Y.presheaf.map (homOfLE h).op) := fun {Y U V} h h' => by
    have : IsIso (homOfLE h).op :=
      ⟨⟨(homOfLE h').op, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    exact (ConcreteCategory.bijective_of_isIso _).1
  have h1 : Function.Injective ((Spec (CommRingCat.of A)).presheaf.germ ⊤
      (genericPoint (Spec (CommRingCat.of A))) trivial) :=
    germ_injective_of_isIntegral _ (U := ⊤) _ trivial
  have h2 : Function.Injective ((Spec (CommRingCat.of A)).residue
      (genericPoint (Spec (CommRingCat.of A)))) := by
    have : IsField ((Spec (CommRingCat.of A)).presheaf.stalk
        (genericPoint (Spec (CommRingCat.of A)))) :=
      Field.toIsField (Spec (CommRingCat.of A)).functionField
    exact RingHom.injective _
  unfold Scheme.fromSpecResidueField
  rw [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, ← Category.comp_id
    (Scheme.Hom.appTop (Spec.map _)), ← Iso.hom_inv_id (Scheme.ΓSpecIso _),
    ← Category.assoc (Scheme.Hom.appTop (Spec.map _)), Scheme.ΓSpecIso_naturality]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1.comp
    (h2.comp ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1.comp
      ((key _ (by simp)).comp
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).1.comp h1))))

open Stacks.AlgebraicGeometry.SectionsBaseChange in
omit [IsLocalRing A] in
/-- **Isomorphic restrictions to the generic fibre give global sections of equal rank**, over
`Γ(Spec A, ⊤)`: by flat base change in degree zero, `κ(η) ⊗ Γ(X, F) ≅ Γ(X_η, F|_{X_η})`, and the
rank of a module over the domain `Γ(Spec A, ⊤)` is the dimension of its base change to a field
containing it. -/
theorem finrank_sections_eq_of_genericFibre_iso [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (e : genericFibreRestrict A f F ≅ genericFibreRestrict A f G) :
    letI := baseModule f F ⊤
    letI := baseModule f G ⊤
    Module.finrank Γ(Spec (CommRingCat.of A), ⊤) Γ(F, ⊤) =
      Module.finrank Γ(Spec (CommRingCat.of A), ⊤) Γ(G, ⊤) := by
  have H : IsPullback (f.fiberι (genericPoint (Spec (CommRingCat.of A))))
      (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of A)))) f
      ((Spec (CommRingCat.of A)).fromSpecResidueField (genericPoint (Spec (CommRingCat.of A)))) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨eF, -⟩ := exists_linearEquiv_sections_baseChange H F
  obtain ⟨eG, -⟩ := exists_linearEquiv_sections_baseChange H G
  let := baseAlgebra ((Spec (CommRingCat.of A)).fromSpecResidueField
    (genericPoint (Spec (CommRingCat.of A))))
  let := baseModule f F ⊤
  let := baseModule f G ⊤
  let := baseModule (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of A))))
    (genericFibreRestrict A f F) ⊤
  let := baseModule (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of A))))
    (genericFibreRestrict A f G) ⊤
  let Ξ : Γ(genericFibreRestrict A f F, ⊤) ≃ₗ[Γ(Spec ((Spec (CommRingCat.of A)).residueField
      (genericPoint (Spec (CommRingCat.of A)))), ⊤)] Γ(genericFibreRestrict A f G, ⊤) :=
    { toFun := e.hom.app ⊤
      invFun := e.inv.app ⊤
      map_add' := map_add _
      map_smul' := fun c y => Scheme.Modules.Hom.app_smul e.hom
        ((Scheme.Hom.appLE (f.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of A))))
          ⊤ ⊤ (le_preimage_top _ ⊤)).hom c) y
      left_inv := fun y => congrArg (fun φ => (φ.app ⊤) y) e.hom_inv_id
      right_inv := fun y => congrArg (fun φ => (φ.app ⊤) y) e.inv_hom_id }
  have : FaithfulSMul Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec ((Spec (CommRingCat.of A)).residueField
      (genericPoint (Spec (CommRingCat.of A)))), ⊤) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    show Function.Injective (Scheme.Hom.appLE _ ⊤ ⊤ _)
    rw [Stacks.AffineAlgebraEquivalence.appLE_top_top]
    exact injective_appTop_fromSpecResidueField_genericPoint A
  have : NoZeroDivisors Γ(Spec ((Spec (CommRingCat.of A)).residueField
      (genericPoint (Spec (CommRingCat.of A)))), ⊤) :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).1.noZeroDivisors _
      (map_zero _) (map_mul _)
  have hF := (TensorProduct.isBaseChange Γ(Spec (CommRingCat.of A), ⊤) Γ(F, ⊤)
    Γ(Spec ((Spec (CommRingCat.of A)).residueField (genericPoint (Spec (CommRingCat.of A)))),
      ⊤)).finrank_eq
  have hG := (TensorProduct.isBaseChange Γ(Spec (CommRingCat.of A), ⊤) Γ(G, ⊤)
    Γ(Spec ((Spec (CommRingCat.of A)).residueField (genericPoint (Spec (CommRingCat.of A)))),
      ⊤)).finrank_eq
  rw [← hF, ← hG]
  exact (eF.trans (Ξ.trans eG.symm)).finrank_eq

open Stacks.AlgebraicGeometry.SectionsBaseChange in
omit [IsDomain A] [IsLocalRing A] in
/-- The rank of `H⁰(X, F)` over `A` is the rank of `Γ(X, F)` over `Γ(Spec A, ⊤)`: in degree zero
the right derived functor of global sections is global sections, and the two scalar rings are
identified by `Γ(Spec A, ⊤) ≅ A`. -/
theorem finrank_cohomologyOver_zero (F : X.Modules) :
    letI := baseModule f F ⊤
    Module.finrank A (cohomologyOver A f 0 F) =
      Module.finrank Γ(Spec (CommRingCat.of A), ⊤) Γ(F, ⊤) := by
  let := baseModule f F ⊤
  let j := ((moduleGlobalSections X).rightDerivedZeroIsoSelf.app F).toLinearEquiv
  let jA : cohomologyOver A f 0 F ≃+ Γ(F, ⊤) := j.toAddEquiv
  exact congrArg Cardinal.toNat <|
    rank_eq_of_equiv_equiv (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom jA
      (ConcreteCategory.bijective_of_isIso _) fun a m =>
        (LinearEquiv.map_smul j (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom a)
          (show ((moduleGlobalSections X).rightDerived 0).obj F from m)).trans
          (congrArg (· • j m) (congrArg
            (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))
            (Stacks.AffineAlgebraEquivalence.appLE_top_top f (le_preimage_top f ⊤))).symm)

omit [IsLocalRing A] in
/-- **Isomorphic restrictions to the generic fibre give `H⁰` of equal rank over `A`.** -/
theorem finrank_cohomologyOver_zero_eq_of_genericFibre_iso [CompactSpace X]
    [QuasiSeparatedSpace X] {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (e : genericFibreRestrict A f F ≅ genericFibreRestrict A f G) :
    Module.finrank A (cohomologyOver A f 0 F) = Module.finrank A (cohomologyOver A f 0 G) := by
  rw [finrank_cohomologyOver_zero, finrank_cohomologyOver_zero]
  exact finrank_sections_eq_of_genericFibre_iso A f e

end Stacks.AlgebraicGeometry.FreenessOverDVR
