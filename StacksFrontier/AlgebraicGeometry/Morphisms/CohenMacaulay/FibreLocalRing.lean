module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohen-Macaulayness of a fibre at a point, read in the local ring

The Cohen-Macaulay condition on the fibre of a morphism of schemes at a point is local on the
stalk, so it is invariant under an isomorphism of stalks, under restriction along an open
immersion of the source or of the target, and under an isomorphism of arrows. For an affine
morphism the condition matches the Cohen-Macaulay locus of the corresponding fibre ring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The scheme-theoretic fibre of a morphism of affine schemes over a prime of the base is the
spectrum of the fibre algebra `κ(p) ⊗_R T`. -/
@[ega "II 1.5.4" "special case"]
noncomputable def affineFiberSchemeIso
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] (p : PrimeSpectrum R) :
    (Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber p ≅
      Spec (.of (p.asIdeal.Fiber T)) := by
  refine Limits.pullbackSymmetry _ _ ≪≫ ?_ ≪≫ pullbackSpecIso R p.asIdeal.ResidueField T
  refine Limits.pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p).symm rfl ≪≫ ?_
  refine asIso <| Limits.pullback.map _ _ _ _
    (Spec.map <| (Scheme.Spec.residueFieldIso (.of R) p).inv) (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The prime of the fibre algebra corresponding to a prime `q` of `T`. -/
noncomputable def affineFiberPoint
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    PrimeSpectrum ((PrimeSpectrum.comap (algebraMap R T) q).asIdeal.Fiber T) :=
  (affineFiberSchemeIso (R := R) (T := T)
    (PrimeSpectrum.comap (algebraMap R T) q)).hom.base
      ((Spec.map (CommRingCat.ofHom (algebraMap R T))).asFiber q)

/-- The local ring of the fibre at the point coming from `q` is the localization of the fibre
algebra at the corresponding prime. -/
noncomputable def affineFiberStalkRingEquiv
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R T))
    let z := f.asFiber q
    (f.fiber (f q)).presheaf.stalk z ≃+*
      Localization.AtPrime (affineFiberPoint (R := R) q).asIdeal := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R T) q
  let f : Spec (.of T) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R T))
  let e := affineFiberSchemeIso (R := R) (T := T) p
  have : IsIso (e.hom.stalkMap (f.asFiber q)) :=
    (isIso_iff_isIso_stalkMap e.hom).mp inferInstance |>.2 _
  dsimp [f, affineFiberPoint, p]
  exact (asIso (e.hom.stalkMap (f.asFiber q))).commRingCatIsoToRingEquiv.symm.trans
    (Spec.stalkIso (.of (p.asIdeal.Fiber T))
      (e.hom.base (f.asFiber q))).commRingCatIsoToRingEquiv

/-- The prime of the fibre algebra attached to `q` contracts back to `q`. -/
theorem affineFiberPoint_comap
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    (affineFiberPoint (R := R) q).asIdeal.comap
      (Algebra.TensorProduct.includeRight : T →ₐ[R]
        ((PrimeSpectrum.comap (algebraMap R T) q).asIdeal.Fiber T)).toRingHom = q.asIdeal := by
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R T) q
  let f : Spec (.of T) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R T))
  let e := affineFiberSchemeIso (R := R) (T := T) p
  have hproj : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : T →ₐ[R] p.asIdeal.Fiber T).toRingHom) =
      f.fiberι (f q) := by
    dsimp [e, affineFiberSchemeIso, Iso.trans]
    simp only [Category.assoc, pullbackSpecIso_hom_snd,
      Limits.pullback.congrHom_hom, Limits.pullback.map, Limits.pullback.lift_snd]
    simp only [Limits.pullback.lift_snd, Category.comp_id]
    show (Limits.pullbackSymmetry f ((Spec (.of R)).fromSpecResidueField p)).hom ≫
      Limits.pullback.snd ((Spec (.of R)).fromSpecResidueField p) f =
        Limits.pullback.fst f ((Spec (.of R)).fromSpecResidueField p)
    exact Limits.pullbackSymmetry_hom_comp_snd f _
  show (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight :
    T →ₐ[R] p.asIdeal.Fiber T).toRingHom (e.hom.base (f.asFiber q))).asIdeal = q.asIdeal
  have hq : (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : T →ₐ[R] p.asIdeal.Fiber T).toRingHom)).base
        (e.hom.base (f.asFiber q)) = (f.fiberι (f q)).base (f.asFiber q) :=
    congrArg (fun k : Scheme.Hom _ _ => k.base (f.asFiber q)) hproj
  exact congrArg PrimeSpectrum.asIdeal (hq.trans (Scheme.Hom.fiberι_asFiber f q))

/-- The fibre ring `S_q/pS_q` at a prime `q`, computed from any model `Y` of `S_q`. -/
noncomputable def affineFiberRingEquiv (R : Type*) {S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] (Y : Type*) [CommRing Y]
    [Algebra S Y] [IsLocalization.AtPrime Y q] [Algebra R Y] [IsScalarTower R S Y] :
    (Y ⧸ (q.under R).map (algebraMap R Y)) ≃ₐ[R]
      Localization.AtPrime (q.map (Ideal.Quotient.mk
        ((q.under R).map (algebraMap R S)))) := by
  have hLies : (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))).LiesOver q :=
    ⟨.trans (by simp [← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
      (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm⟩
  have hsub := Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
    (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))) q Ideal.Quotient.mk_surjective
  set I := (q.under R).map (algebraMap R S)
  refine (Ideal.quotientEquivAlgOfEq R (J := I.map (algebraMap S Y))
    (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq])).trans ?_
  have : IsLocalization (q.map (Ideal.Quotient.mk I)).primeCompl
      (Y ⧸ I.map (algebraMap S Y)) := hsub ▸ inferInstance
  have : IsScalarTower R (S ⧸ I) (Y ⧸ I.map (algebraMap S Y)) :=
    .of_algebraMap_eq fun r => by
      change Ideal.Quotient.mk _ (algebraMap R Y r) =
        Ideal.Quotient.mk _ (algebraMap S Y (algebraMap R S r))
      rw [IsScalarTower.algebraMap_apply R S Y r]
  exact (IsLocalization.algEquiv (q.map (Ideal.Quotient.mk I)).primeCompl _
    (Localization.AtPrime (q.map (Ideal.Quotient.mk I)))).restrictScalars R

/-- Transport of a quotient of a localization at a prime along an equality of primes. -/
noncomputable def quotientLocalizationAtPrimeCongr {A : Type*} [CommRing A]
    {I J : Ideal A} [I.IsPrime] [J.IsPrime] (h : I = J) {R : Type*} [CommRing R]
    [Algebra R A] (p : Ideal R) :
    (Localization.AtPrime I ⧸ p.map (algebraMap R (Localization.AtPrime I))) ≃ₐ[R]
      (Localization.AtPrime J ⧸ p.map (algebraMap R (Localization.AtPrime J))) := by
  subst h
  exact AlgEquiv.refl

/-- The localization of the fibre algebra at the prime attached to `q` is the fibre ring of
`T_q` over `R`. -/
noncomputable def affineFiberPointRingEquiv
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    Localization.AtPrime (affineFiberPoint (R := R) (T := T) q).asIdeal ≃ₐ[R]
      Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
        ((q.asIdeal.under R).map (algebraMap R T)))) := by
  let p := (PrimeSpectrum.comap (algebraMap R T) q).asIdeal
  let qbar := affineFiberPoint (R := R) (T := T) q
  let r := qbar.asIdeal.comap
    (Algebra.TensorProduct.includeRight : T →ₐ[R] p.Fiber T).toRingHom
  let _ : qbar.asIdeal.IsPrime := qbar.isPrime
  let _ : r.IsPrime := Ideal.IsPrime.comap _
  have hr : r = q.asIdeal := affineFiberPoint_comap (R := R) (T := T) q
  let e₂ : (Localization.AtPrime r ⧸ (p.map (algebraMap R T)).map
      (algebraMap T (Localization.AtPrime r))) ≃ₐ[R]
      (Localization.AtPrime r ⧸ p.map (algebraMap R (Localization.AtPrime r))) :=
    Ideal.quotientEquivAlgOfEq R
      (I := (p.map (algebraMap R T)).map (algebraMap T (Localization.AtPrime r)))
      (J := p.map (algebraMap R (Localization.AtPrime r)))
      (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq])
  exact (Ideal.Fiber.algEquivAux₂ p qbar.asIdeal).trans (e₂.trans
    ((quotientLocalizationAtPrimeCongr hr p).trans
      (affineFiberRingEquiv R q.asIdeal (Localization.AtPrime q.asIdeal))))

/-- Maximal Cohen–Macaulayness of the localized fibre algebra is the ring-theoretic
Cohen–Macaulayness of the fibre ring. -/
theorem affineFiberPoint_cm_iff_ring_locus
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (hf : ∀ y : Spec (.of R), IsLocallyNoetherian
      ((Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber y)) (q : PrimeSpectrum T) :
    Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (affineFiberPoint (R := R) (T := T) q).asIdeal)
        (Localization.AtPrime (affineFiberPoint (R := R) (T := T) q).asIdeal) ↔
      Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
          ((q.asIdeal.under R).map (algebraMap R T)))))
        (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
          ((q.asIdeal.under R).map (algebraMap R T))))) := by
  let A := (((Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber
    ((Spec.map (CommRingCat.ofHom (algebraMap R T))) q)).presheaf.stalk
      ((Spec.map (CommRingCat.ofHom (algebraMap R T))).asFiber q))
  let B := Localization.AtPrime (affineFiberPoint (R := R) (T := T) q).asIdeal
  let C := Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
    ((q.asIdeal.under R).map (algebraMap R T))))
  let eAB : A ≃+* B := affineFiberStalkRingEquiv (R := R) (T := T) q
  let eBC : B ≃+* C := affineFiberPointRingEquiv (R := R) (T := T) q
  let _ : IsLocallyNoetherian ((Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber
      ((Spec.map (CommRingCat.ofHom (algebraMap R T))) q)) := hf _
  let _ : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A eAB
  let _ : IsNoetherianRing C := isNoetherianRing_of_ringEquiv B eBC
  let _ : IsLocalRing B := eAB.isLocalRing
  let _ : IsLocalRing C := eBC.isLocalRing
  exact Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv eBC

/-- Cohen–Macaulayness of the fibre local ring at `q` is maximal Cohen–Macaulayness of the
localized fibre algebra. -/
theorem affineFiber_cm_iff
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (hf : ∀ y : Spec (.of R), IsLocallyNoetherian
      ((Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber y)) (q : PrimeSpectrum T) :
    IsCohenMacaulayLocalRing
      (((Spec.map (CommRingCat.ofHom (algebraMap R T))).fiber
        ((Spec.map (CommRingCat.ofHom (algebraMap R T))) q)).presheaf.stalk
          ((Spec.map (CommRingCat.ofHom (algebraMap R T))).asFiber q)) ↔
      Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (affineFiberPoint (R := R) (T := T) q).asIdeal)
        (Localization.AtPrime (affineFiberPoint (R := R) (T := T) q).asIdeal) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R T))
  let _ : IsLocallyNoetherian (f.fiber (f q)) := hf (f q)
  let A := (f.fiber (f q)).presheaf.stalk (f.asFiber q)
  let B := Localization.AtPrime (affineFiberPoint (R := R) (T := T) q).asIdeal
  let e : A ≃+* B := affineFiberStalkRingEquiv (R := R) (T := T) q
  let _ : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e
  let _ : IsLocalRing B := e.isLocalRing
  show IsCohenMacaulayLocalRing A ↔ Module.IsMaximalCohenMacaulay B B
  exact (isCohenMacaulayLocalRing_iff_of_ringEquiv e).trans
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay B)

/-- Cohen–Macaulayness of a stalk transports along a morphism which is an isomorphism on
stalks. -/
theorem localCM_iff_of_isIso_stalkMap {A B : Scheme.{u}} (k : A ⟶ B) (z : A)
    [IsIso (k.stalkMap z)] (hA : IsLocallyNoetherian A) (hB : IsLocallyNoetherian B) :
    IsCohenMacaulayLocalRing (A.presheaf.stalk z) ↔
      IsCohenMacaulayLocalRing (B.presheaf.stalk (k z)) := by
  let e : A.presheaf.stalk z ≃+* B.presheaf.stalk (k z) :=
    (asIso (k.stalkMap z)).commRingCatIsoToRingEquiv.symm
  let _ : IsNoetherianRing (B.presheaf.stalk (k z)) := isNoetherianRing_of_ringEquiv _ e
  let _ : IsLocalRing (B.presheaf.stalk (k z)) := e.isLocalRing
  exact isCohenMacaulayLocalRing_iff_of_ringEquiv e

/-- Cohen–Macaulayness of a stalk transports along an equality of points. -/
theorem localCM_iff_of_point_eq {A : Scheme.{u}} (z w : A) (h : z = w)
    [IsNoetherianRing (A.presheaf.stalk z)] [IsNoetherianRing (A.presheaf.stalk w)]
    [IsLocalRing (A.presheaf.stalk z)] [IsLocalRing (A.presheaf.stalk w)] :
    IsCohenMacaulayLocalRing (A.presheaf.stalk z) ↔
      IsCohenMacaulayLocalRing (A.presheaf.stalk w) := by
  cases h
  rfl

/-- Cohen–Macaulayness of stalks transports along a morphism of schemes which is an open
immersion or an isomorphism, as soon as it maps the first point to the second. -/
private theorem localCM_iff_of_apply_eq {A B : Scheme.{u}} (k : A ⟶ B) (z : A) (w : B)
    (h : k z = w) [IsOpenImmersion k] (hA : IsLocallyNoetherian A) (hB : IsLocallyNoetherian B)
    [IsNoetherianRing (B.presheaf.stalk w)] [IsLocalRing (B.presheaf.stalk w)]
    [IsNoetherianRing (A.presheaf.stalk z)] [IsLocalRing (A.presheaf.stalk z)] :
    IsCohenMacaulayLocalRing (A.presheaf.stalk z) ↔
      IsCohenMacaulayLocalRing (B.presheaf.stalk w) := by
  have : IsIso (k.stalkMap z) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 _
  exact (localCM_iff_of_isIso_stalkMap k z hA hB).trans
    (localCM_iff_of_point_eq (A := B) (k z) w h)

/-- Restricting the source along an open immersion does not change the fibre local ring. -/
theorem localFiberCM_iff_sourceOpenImmersion {X X' S : Scheme.{u}}
    (i : X' ⟶ X) [IsOpenImmersion i] (f : X ⟶ S) (x : X')
    (hf : IsLocallyNoetherian (f.fiber (f (i x))))
    (hg : IsLocallyNoetherian ((i ≫ f).fiber (f (i x))))
    [IsNoetherianRing ((f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x)))]
    [IsNoetherianRing (((i ≫ f).fiber (f (i x))).presheaf.stalk ((i ≫ f).asFiber x))]
    [IsLocalRing ((f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x)))]
    [IsLocalRing (((i ≫ f).fiber (f (i x))).presheaf.stalk ((i ≫ f).asFiber x))] :
    IsCohenMacaulayLocalRing
      ((f.fiber (f (i x))).presheaf.stalk (f.asFiber (i x))) ↔
    IsCohenMacaulayLocalRing
      (((i ≫ f).fiber (f (i x))).presheaf.stalk ((i ≫ f).asFiber x)) := by
  let h := i ≫ f
  let e : h.fiber (f (i x)) ≅
      Limits.pullback i (Limits.pullback.fst f (S.fromSpecResidueField (f (i x)))) :=
    (Limits.pullbackRightPullbackFstIso f
      (S.fromSpecResidueField (f (i x))) i).symm
  let k : h.fiber (f (i x)) ⟶ f.fiber (f (i x)) :=
    e.hom ≫ Limits.pullback.snd i
      (Limits.pullback.fst f (S.fromSpecResidueField (f (i x))))
  have hk : IsOpenImmersion k := by
    have : IsOpenImmersion (Limits.pullback.snd i
        (Limits.pullback.fst f (S.fromSpecResidueField (f (i x))))) :=
      MorphismProperty.pullback_snd (P := @IsOpenImmersion) i
        (Limits.pullback.fst f (S.fromSpecResidueField (f (i x)))) inferInstance
    exact IsOpenImmersion.comp e.hom
      (Limits.pullback.snd i
        (Limits.pullback.fst f (S.fromSpecResidueField (f (i x)))))
  have hkpt : k (h.asFiber x) = f.asFiber (i x) := by
    apply (f.fiberι (f (i x))).isEmbedding.injective
    have hcomp : k ≫ f.fiberι (f (i x)) = h.fiberι (f (i x)) ≫ i := by
      show ((Limits.pullbackRightPullbackFstIso f
        (S.fromSpecResidueField (f (i x))) i).inv ≫
        Limits.pullback.snd i (Limits.pullback.fst f
          (S.fromSpecResidueField (f (i x)))) ≫
        Limits.pullback.fst f (S.fromSpecResidueField (f (i x)))) =
          Limits.pullback.fst (i ≫ f) (S.fromSpecResidueField (f (i x))) ≫ i
      exact Limits.pullbackRightPullbackFstIso_inv_snd_fst f
        (S.fromSpecResidueField (f (i x))) i
    have hv := congrArg (fun m : h.fiber (f (i x)) ⟶ X => m (h.asFiber x)) hcomp
    change (f.fiberι (f (i x))) (k (h.asFiber x)) =
      i ((h.fiberι (f (i x))) (h.asFiber x)) at hv
    have hr : h.fiberι (f (i x)) (h.asFiber x) = x :=
      Scheme.Hom.fiberι_asFiber h x
    rw [hr] at hv
    simpa only [Scheme.Hom.fiberι_asFiber] using hv
  exact (localCM_iff_of_apply_eq k (h.asFiber x) _ hkpt hg hf).symm

/-- Enlarging the target along an open immersion does not change the fibre local ring. -/
theorem localFiberCM_iff_openTarget {X S T : Scheme.{u}} (i : T ⟶ S)
    [IsOpenImmersion i] (f : X ⟶ T) (_y : T) (x : X)
    (hf : IsLocallyNoetherian (f.fiber (f x)))
    (hh : IsLocallyNoetherian ((f ≫ i).fiber (i (f x))))
    [IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
    [IsNoetherianRing (((f ≫ i).fiber (i (f x))).presheaf.stalk ((f ≫ i).asFiber x))]
    [IsLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
    [IsLocalRing (((f ≫ i).fiber (i (f x))).presheaf.stalk ((f ≫ i).asFiber x))] :
    IsCohenMacaulayLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ↔
      IsCohenMacaulayLocalRing
        (((f ≫ i).fiber (i (f x))).presheaf.stalk ((f ≫ i).asFiber x)) := by
  let h := f ≫ i
  let K := S.residueField (i (f x))
  let K' := T.residueField (f x)
  let inner := i.fiber (i (f x))
  let p := Limits.pullback.snd i (S.fromSpecResidueField (i (f x)))
  have : IsOpenImmersion p :=
    MorphismProperty.pullback_snd (P := @IsOpenImmersion) i
      (S.fromSpecResidueField (i (f x))) inferInstance
  have hpSurj : Function.Surjective p.base := fun _ => ⟨i.asFiber (f x), Subsingleton.elim _ _⟩
  have : Epi p.base := TopCat.epi_iff_surjective p.base |>.mpr hpSurj
  have hpIso : IsIso p := IsOpenImmersion.isIso p
  obtain ⟨pInv, hpInv₁, hpInv₂⟩ := hpIso.out
  let ePoint : inner ≅ Spec K := ⟨p, pInv, hpInv₁, hpInv₂⟩
  let rmap := i.residueFieldMap (f x)
  have : IsIso rmap := by infer_instance
  let eRing : K ≅ K' := asIso rmap
  let eField : Spec K ≅ Spec K' := asIso (Spec.map eRing.inv)
  let eInner : inner ≅ Spec K' := ePoint ≪≫ eField
  have heInner : eInner.hom ≫ T.fromSpecResidueField (f x) =
      Limits.pullback.fst i (S.fromSpecResidueField (i (f x))) := by
    apply (cancel_mono i).1
    show (ePoint.hom ≫ eField.hom) ≫ T.fromSpecResidueField (f x) ≫ i =
      Limits.pullback.fst i (S.fromSpecResidueField (i (f x))) ≫ i
    show (p ≫ Spec.map eRing.inv) ≫ T.fromSpecResidueField (f x) ≫ i =
      Limits.pullback.fst i (S.fromSpecResidueField (i (f x))) ≫ i
    calc
      _ = p ≫ Spec.map eRing.inv ≫ Spec.map rmap ≫
          S.fromSpecResidueField (i (f x)) := by
        rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
        simp only [Category.assoc, rmap]
      _ = p ≫ S.fromSpecResidueField (i (f x)) := by
        have hc : Spec.map eRing.inv ≫ Spec.map rmap = 𝟙 (Spec K) := by
          rw [← Spec.map_comp]
          simp [eRing, K]
        rw [← Category.assoc (Spec.map eRing.inv), hc, Category.id_comp]
      _ = Limits.pullback.fst i (S.fromSpecResidueField (i (f x))) ≫ i :=
        Limits.pullback.condition.symm
  let eAssoc := (Limits.pullbackRightPullbackFstIso i
    (S.fromSpecResidueField (i (f x))) f).symm
  let m := Limits.pullback.map f (Limits.pullback.fst i
      (S.fromSpecResidueField (i (f x)))) f (T.fromSpecResidueField (f x))
    (𝟙 X) eInner.hom (𝟙 T) (by simp) heInner.symm
  have : IsIso eInner.hom := Iso.isIso_hom eInner
  have : IsIso m := by
    dsimp [m]
    exact @Limits.pullback.map_isIso Scheme _ X inner X (Spec K') T T
      f (Limits.pullback.fst i (S.fromSpecResidueField (i (f x)))) _
      f (T.fromSpecResidueField (f x)) _ (𝟙 X) eInner.hom (𝟙 T)
      (by simp) heInner.symm (by infer_instance) (Iso.isIso_hom eInner) (by infer_instance)
  let eChange := asIso m
  let e : h.fiber (i (f x)) ≅ f.fiber (f x) := eAssoc.trans eChange
  have heComp : e.hom ≫ f.fiberι (f x) = h.fiberι (i (f x)) := by
    show e.hom ≫ Limits.pullback.fst f (T.fromSpecResidueField (f x)) =
      Limits.pullback.fst (f ≫ i) (S.fromSpecResidueField (i (f x)))
    show eAssoc.hom ≫ eChange.hom ≫
      Limits.pullback.fst f (T.fromSpecResidueField (f x)) =
        Limits.pullback.fst (f ≫ i) (S.fromSpecResidueField (i (f x)))
    calc
      _ = eAssoc.hom ≫ (m ≫ Limits.pullback.fst f (T.fromSpecResidueField (f x))) := by
        show (eAssoc.hom ≫ m) ≫
          Limits.pullback.fst f (T.fromSpecResidueField (f x)) = _
        rfl
      _ = eAssoc.hom ≫ Limits.pullback.fst f
          (Limits.pullback.fst i (S.fromSpecResidueField (i (f x)))) := by
        simp [m, Limits.pullback.map, Limits.pullback.lift_fst]
      _ = Limits.pullback.fst (f ≫ i) (S.fromSpecResidueField (i (f x))) :=
        Limits.pullbackRightPullbackFstIso_inv_fst i
          (S.fromSpecResidueField (i (f x))) f
  have hpt : e.hom (h.asFiber x) = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    have hv := congrArg (fun m : h.fiber (i (f x)) ⟶ X => m (h.asFiber x)) heComp
    change (f.fiberι (f x)) (e.hom (h.asFiber x)) =
      (h.fiberι (i (f x))) (h.asFiber x) at hv
    have hr : h.fiberι (i (f x)) (h.asFiber x) = x := by
      have hxy : (f ≫ i) x = i (f x) := Scheme.Hom.comp_apply f i x
      cases hxy
      exact Scheme.Hom.fiberι_asFiber (f ≫ i) x
    rw [hr] at hv
    exact hv.trans (by simp only [Scheme.Hom.fiberι_asFiber])
  exact (localCM_iff_of_apply_eq e.hom (h.asFiber x) _ hpt hh hf).symm

/-- An isomorphism of arrows identifies the fibre local rings at corresponding points. -/
theorem localFiberCM_iff_arrowIso {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (g : X' ⟶ S') (e : Arrow.mk f ≅ Arrow.mk g)
    (hf : ∀ y : S, IsLocallyNoetherian (f.fiber y))
    (hg : ∀ y : S', IsLocallyNoetherian (g.fiber y)) (x : X)
    (hcomp : IsLocallyNoetherian
      ((e.hom.left ≫ g).fiber (g (e.hom.left x))))
    [IsNoetherianRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
    [IsNoetherianRing ((g.fiber (g (e.hom.left x))).presheaf.stalk
      (g.asFiber (e.hom.left x)))]
    [IsLocalRing ((f.fiber (f x)).presheaf.stalk (f.asFiber x))]
    [IsLocalRing ((g.fiber (g (e.hom.left x))).presheaf.stalk
      (g.asFiber (e.hom.left x)))]
    [IsNoetherianRing
      (((f ≫ e.hom.right).fiber (e.hom.right (f x))).presheaf.stalk
        ((f ≫ e.hom.right).asFiber x))]
    [IsNoetherianRing
      (((e.hom.left ≫ g).fiber (g (e.hom.left x))).presheaf.stalk
        ((e.hom.left ≫ g).asFiber x))]
    [IsLocalRing
      (((f ≫ e.hom.right).fiber (e.hom.right (f x))).presheaf.stalk
        ((f ≫ e.hom.right).asFiber x))]
    [IsLocalRing
      (((e.hom.left ≫ g).fiber (g (e.hom.left x))).presheaf.stalk
        ((e.hom.left ≫ g).asFiber x))] :
    IsCohenMacaulayLocalRing
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) ↔
    IsCohenMacaulayLocalRing
      ((g.fiber (g (e.hom.left x))).presheaf.stalk (g.asFiber (e.hom.left x))) := by
  let i := e.hom.left
  let j := e.hom.right
  have hcomm : i ≫ g = f ≫ j := e.hom.w
  have hpt : g (i x) = j (f x) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k : X ⟶ S' => k x) hcomm
  let _ : IsLocallyNoetherian (f.fiber (f x)) := hf _
  let _ : IsLocallyNoetherian (g.fiber (g (i x))) := hg _
  have hh : IsLocallyNoetherian ((f ≫ j).fiber (j (f x))) := by
    rw [← hcomm, ← hpt]
    exact hcomp
  have h₂' : IsCohenMacaulayLocalRing
      (((i ≫ g).fiber (g (i x))).presheaf.stalk ((i ≫ g).asFiber x)) ↔
      IsCohenMacaulayLocalRing
        (((f ≫ j).fiber (j (f x))).presheaf.stalk ((f ≫ j).asFiber x)) := by
    let D := {z : (X ⟶ S') × S' // z.1 x = z.2 ∧
      IsLocallyNoetherian (z.1.fiber z.2)}
    let a : D := ⟨(i ≫ g, g (i x)), ⟨Scheme.Hom.comp_apply i g x, hcomp⟩⟩
    let b : D := ⟨(f ≫ j, j (f x)), ⟨Scheme.Hom.comp_apply f j x, hh⟩⟩
    have hab : a = b := Subtype.ext (Prod.ext hcomm hpt)
    let P : D → Prop := fun d => by
      let : IsLocallyNoetherian (d.1.1.fiber d.1.2) := d.2.2
      exact IsCohenMacaulayLocalRing
        ((d.1.1.fiber d.1.2).presheaf.stalk (d.2.1 ▸ d.1.1.asFiber x))
    simpa only [a, b, D, P] using Iff.of_eq (congrArg P hab)
  exact (localFiberCM_iff_openTarget j f (f x) x (hf _) hh).trans
    (h₂'.symm.trans (localFiberCM_iff_sourceOpenImmersion i g x (hg _) hcomp).symm)

/-- The stalk of a locally Noetherian scheme is a Noetherian ring. -/
theorem noetherianStalk_of_locallyNoetherian {Y : Scheme.{u}} (y : Y)
    (h : IsLocallyNoetherian Y) : IsNoetherianRing (Y.presheaf.stalk y) :=
  inferInstance

end AlgebraicGeometry

end
