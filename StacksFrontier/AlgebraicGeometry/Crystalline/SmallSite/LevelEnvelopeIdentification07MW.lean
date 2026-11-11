module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineObjectCompletedFormsComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTaylorFirstOrder
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRingDividedPowers
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineOverAffineSubsite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelSectionsSheafifyIso

/-!
# The levels of the system of [Stacks, Tag 07JN] are the envelopes when `p` is nilpotent

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine and `p` nilpotent on
`X`, and let `E(n)` be the (uncompleted) divided power envelope of the `(n+1)`-fold tensor power
of the presentation of the system, `T(n)_e` the levels of the system of [Stacks, Tag 07JN].
The reduction `E(n) → Γ(T(n)_e, 𝒪)` (`...SmallSite.envLevelMap`) is a divided power morphism of
`Γ(S, ⊤)`-algebras; this module packages it as such and shows that, **as soon as
`p^{N+e} = 0` in `E(n)`** (which holds for every large `e` when `p` is nilpotent in `Γ(S, ⊤)`),
it is an isomorphism of divided power rings: it is bijective and its inverse is a divided power
morphism.  These are the inputs `θ₀`, `θ₁` of the comparison of forms
`Crystalline.GlobalCrystallineSituation.formsHom`.

The level objects are also recorded as objects of the affine-over-affine subsite.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.levelAffineObject` — `T(n)_e` as an object of
  the affine-over-affine subsite (over the affine open `⊤` of `S`).
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelEnvelopeAlgHom` — the reduction
  `E(n) → Γ(T(n)_e, 𝒪)` as a morphism of `Γ(S, ⊤)`-algebras.
* `Crystalline.GlobalCrystallineSituation.SmallSite.levelEnvelopeAlgHomInv` — its inverse, when
  `p^{N+e} = 0` in `E(n)`.

## Main results

* `Crystalline.isDPMorphism_ringEquivOfBijective_symm` — the inverse of a bijective divided power
  morphism carrying the ideal onto the ideal is a divided power morphism.
* `...SmallSite.bijective_envLevelMap_of_pow_eq_zero`,
  `...SmallSite.isDPMorphism_levelEnvelopeAlgHomInv`.

## What is and is not proved

Everything stated is proved.  The hypothesis `p^{N+e} = 0` in `E(n)` is explicit; nothing is
claimed for smaller `e`.  No tag attribute is placed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite DividedPowers Simplicial
open scoped AlgebraicGeometry

universe u

namespace Crystalline

/-- **The inverse of a bijective divided power morphism which carries the divided power ideal
onto the divided power ideal is a divided power morphism.** -/
theorem isDPMorphism_ringEquivOfBijective_symm {B C : Type*} [CommRing B] [CommRing C]
    {J : Ideal B} {L : Ideal C} {δ : DividedPowers J} {ε : DividedPowers L} {f : B →+* C}
    (hf : Function.Bijective f) (hdp : IsDPMorphism δ ε f) (hL : L ≤ J.map f) :
    IsDPMorphism ε δ (RingEquiv.ofBijective f hf).symm.toRingHom := by
  have key : ∀ y ∈ L, ∃ x ∈ J, f x = y := fun y hy ↦
    (Ideal.mem_map_iff_of_surjective f hf.2).1 (hL hy)
  have hsymm : ∀ x, (RingEquiv.ofBijective f hf).symm.toRingHom (f x) = x := fun x ↦
    (RingEquiv.ofBijective f hf).symm_apply_apply x
  refine ⟨Ideal.map_le_iff_le_comap.2 fun y hy ↦ ?_, fun {n} y hy ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := key y hy
    exact Ideal.mem_comap.2 ((hsymm x).symm ▸ hx)
  · obtain ⟨x, hx, rfl⟩ := key y hy
    rw [hsymm, hdp.2 x hx, hsymm]

/-- **The ring map `Ê → C` of a divided power morphism `θ : E → C` is a divided power morphism**
for the completed divided powers, when `p` is nilpotent in `E`: the inverse of
`E → Ê` is one, `E → Ê` carrying the divided power ideal onto the completed one. -/
theorem isDPMorphism_completedFormsRingHom (p : ℕ) {A : Type u} [CommRing A] {E : Type u}
    [CommRing E] [Algebra A E] {J : Ideal E} (h : DividedPowers J)
    (hpJ : IsNilpotent (Ideal.Quotient.mk J (p : E))) (hE : ∃ k, (p : E) ^ k = 0)
    {C : Type*} [CommRing C] [Algebra A C] {K : Ideal C} {hK : DividedPowers K}
    (θ : E →ₐ[A] C) (hθ : IsDPMorphism h hK θ.toRingHom) :
    IsDPMorphism (completionDividedPowers p h hpJ) hK (completedFormsRingHom p hE θ) := by
  have hof := (completionDPMorphism J h p hpJ).isDPMorphism
  have hb : Function.Bijective (algebraMap E (AdicCompletion (pAdicIdeal (A := E) p) E)) :=
    (pAdicOfRingEquiv p hE).bijective
  have hsymm := isDPMorphism_ringEquivOfBijective_symm hb hof fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hb.2 x
    have h0 : completionToQuotient J p hpJ (algebraMap E _ y) = 0 := hx
    rw [completionToQuotient_algebraMap] at h0
    exact Ideal.mem_map_of_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  exact hθ.comp _ hsymm

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))

/-- **The level `T(n)_e` as an object of the affine-over-affine subsite**: its ambient scheme is
affine and lies over the affine open `⊤` of `S`. -/
def levelAffineObject (n e : ℕ) : AffineOverAffineCrystallineThickening S :=
  ⟨levelObj hp n e, isAffine_wholeSpaceSystem_target hp n e, ⊤, isAffineOpen_top _, le_rfl⟩

/-- The underlying object of `levelAffineObject` is the level `T(n)_e`. -/
@[simp]
theorem levelAffineObject_obj (n e : ℕ) : (levelAffineObject hp n e).obj = levelObj hp n e :=
  rfl

/-- The envelope `E(n)` as an algebra over `Γ(S, ⊤)`, in the spelling of the base ring used by
`Crystalline.GlobalCrystallineSituation.formsHom`. -/
abbrev wsEnvelopeTopAlgebra (n : ℕ) :
    Algebra (Γ(S.S.scheme, ⊤) : Type u) (wsEnvelope hp n) :=
  tensorPowerEnvelopeAlgebraInstance (affineSituation S hp) (wholeSpacePresentation S hp) n

attribute [local instance] crysTopAlgebra wsEnvelopeTopAlgebra

/-- **The reduction `E(n) → Γ(T(n)_e, 𝒪)` as a morphism of `Γ(S, ⊤)`-algebras.** -/
def levelEnvelopeAlgHom (n e : ℕ) :
    wsEnvelope hp n →ₐ[(Γ(S.S.scheme, ⊤) : Type u)]
      Γ((levelObj hp n e).obj.thickening.target.scheme, ⊤) :=
  { envLevelMap hp n e with
    commutes' := fun a ↦ by
      refine Eq.trans ?_ ((wholeSpaceEnvelopeRingLevelEquiv hp n e).symm_apply_apply _)
      refine congrArg (wholeSpaceEnvelopeRingLevelEquiv hp n e).symm ?_
      exact (wholeSpaceEnvelopeRingLevelEquiv_crysBaseAppLE hp n e a).symm }

/-- The underlying map of `levelEnvelopeAlgHom` is the reduction `envLevelMap`. -/
theorem levelEnvelopeAlgHom_apply (n e : ℕ) (x : wsEnvelope hp n) :
    levelEnvelopeAlgHom hp n e x = envLevelMap hp n e x :=
  rfl

/-- The reduction is a divided power morphism. -/
theorem isDPMorphism_levelEnvelopeAlgHom (n e : ℕ) :
    IsDPMorphism (wsEnvelope hp n).dividedPowers (crysDividedPowers S (levelObj hp n e).obj)
      (levelEnvelopeAlgHom hp n e).toRingHom :=
  isDPMorphism_envLevelMap hp n e

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- `p` is nilpotent in the envelope once it is nilpotent in `Γ(S, ⊤)`. -/
theorem exists_pow_eq_zero_wsEnvelope (hA : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (n : ℕ) :
    ∃ k, (S.p : wsEnvelope hp n) ^ k = 0 := by
  obtain ⟨k, hk⟩ := hA
  refine ⟨k, ?_⟩
  have h := congrArg (algebraMap (Γ(S.S.scheme, ⊤) : Type u) (wsEnvelope hp n)) hk
  rwa [map_pow, map_natCast, map_zero] at h

variable {hp} in
/-- **The reduction `E(n) → Γ(T(n)_e, 𝒪)` is bijective once `p^{N+e} = 0` in `E(n)`.** -/
theorem bijective_envLevelMap_of_pow_eq_zero {n e : ℕ}
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      wsEnvelope hp n) = 0) :
    Function.Bijective (envLevelMap hp n e) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, surjective_envLevelMap hp n e⟩
  obtain ⟨z, rfl⟩ := exists_eq_mul_of_envLevelMap_eq_zero hp n e hx
  rw [hpe, zero_mul]

variable {hp} in
/-- **The inverse of the reduction is a divided power morphism** once `p^{N+e} = 0` in `E(n)`: the
reduction carries the divided power ideal of `E(n)` onto that of `Γ(T(n)_e, 𝒪)`. -/
theorem isDPMorphism_envLevelMap_symm {n e : ℕ}
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      wsEnvelope hp n) = 0) :
    IsDPMorphism (crysDividedPowers S (levelObj hp n e).obj) (wsEnvelope hp n).dividedPowers
      (RingEquiv.ofBijective (envLevelMap hp n e)
        (bijective_envLevelMap_of_pow_eq_zero hpe)).symm.toRingHom := by
  refine isDPMorphism_ringEquivOfBijective_symm _ (isDPMorphism_envLevelMap hp n e)
    fun y hy ↦ ?_
  have hz := (isDPMorphism_wholeSpaceEnvelopeRingLevelEquiv hp n e).1 (Ideal.mem_map_of_mem _ hy)
  obtain ⟨x, hx⟩ := surjective_mk_algebraMap (R := wsEnvelope hp n) S.p
    (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)
    (wholeSpaceEnvelopeRingLevelEquiv hp n e y)
  have hz' : Ideal.Quotient.mk _ (wsCompletionMap hp n x) ∈
      (wholeSpaceEnvelopeDPRing hp n).ideal.map (Ideal.Quotient.mk (DividedPowers.pAdicIdeal
        (A := ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) (affineSituation S hp).p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e))) := by
    have hx' : Ideal.Quotient.mk (DividedPowers.pAdicIdeal
        (A := ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) (affineSituation S hp).p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) (wsCompletionMap hp n x) =
        wholeSpaceEnvelopeRingLevelEquiv hp n e y := hx
    rw [hx']
    exact hz
  obtain ⟨w, hw, hwx⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk
    (DividedPowers.pAdicIdeal (A := ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u))
      (affineSituation S hp).p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)))
    Ideal.Quotient.mk_surjective).1 hz'
  have hmem : wsCompletionMap hp n x ∈ (wholeSpaceEnvelopeDPRing hp n).ideal := by
    have hd : wsCompletionMap hp n x - w ∈ DividedPowers.pAdicIdeal
        (A := ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) (affineSituation S hp).p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) :=
      Ideal.Quotient.eq.1 hwx.symm
    have hsplit : wsCompletionMap hp n x = (wsCompletionMap hp n x - w) + w :=
      (sub_add_cancel _ _).symm
    rw [hsplit]
    exact Ideal.add_mem _ ((isPAdicLevel_wholeSpaceEnvelopeDPRing hp n e).1 hd) hw
  have hxJ : x ∈ (wsEnvelope hp n).ideal := by
    have h0 := RingHom.mem_ker.1 hmem
    exact Ideal.Quotient.eq_zero_iff_mem.1
      ((DividedPowers.completionToQuotient_algebraMap _ _ _ x).symm.trans h0)
  have hxy : envLevelMap hp n e x = y := by
    change (wholeSpaceEnvelopeRingLevelEquiv hp n e).symm
      (Ideal.Quotient.mk _ (wsCompletionMap hp n x)) = y
    rw [show Ideal.Quotient.mk _ (wsCompletionMap hp n x) =
      wholeSpaceEnvelopeRingLevelEquiv hp n e y from hx]
    exact (wholeSpaceEnvelopeRingLevelEquiv hp n e).symm_apply_apply y
  exact hxy ▸ Ideal.mem_map_of_mem _ hxJ

variable {hp} in
/-- **The inverse of the reduction `E(n) → Γ(T(n)_e, 𝒪)`**, as a morphism of `Γ(S, ⊤)`-algebras,
once `p^{N+e} = 0` in `E(n)`. -/
def levelEnvelopeAlgHomInv {n e : ℕ}
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      wsEnvelope hp n) = 0) :
    Γ((levelObj hp n e).obj.thickening.target.scheme, ⊤) →ₐ[(Γ(S.S.scheme, ⊤) : Type u)]
      wsEnvelope hp n :=
  (AlgEquiv.ofBijective (levelEnvelopeAlgHom hp n e)
    (bijective_envLevelMap_of_pow_eq_zero hpe)).symm.toAlgHom

variable {hp} in
/-- The inverse is a left inverse. -/
theorem levelEnvelopeAlgHomInv_comp {n e : ℕ}
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      wsEnvelope hp n) = 0) :
    (levelEnvelopeAlgHomInv hpe).comp (levelEnvelopeAlgHom hp n e) = AlgHom.id _ _ :=
  AlgHom.ext fun x ↦ (AlgEquiv.ofBijective (levelEnvelopeAlgHom hp n e)
    (bijective_envLevelMap_of_pow_eq_zero hpe)).symm_apply_apply x

variable {hp} in
/-- The inverse is a right inverse. -/
theorem comp_levelEnvelopeAlgHomInv {n e : ℕ}
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      wsEnvelope hp n) = 0) :
    (levelEnvelopeAlgHom hp n e).comp (levelEnvelopeAlgHomInv hpe) = AlgHom.id _ _ :=
  AlgHom.ext fun x ↦ (AlgEquiv.ofBijective (levelEnvelopeAlgHom hp n e)
    (bijective_envLevelMap_of_pow_eq_zero hpe)).apply_symm_apply x

variable {hp} in
/-- The inverse is a divided power morphism. -/
theorem isDPMorphism_levelEnvelopeAlgHomInv {n e : ℕ}
    (hpe : ((S.p ^ (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) : ℕ) :
      wsEnvelope hp n) = 0) :
    IsDPMorphism (crysDividedPowers S (levelObj hp n e).obj) (wsEnvelope hp n).dividedPowers
      (levelEnvelopeAlgHomInv hpe).toRingHom :=
  isDPMorphism_envLevelMap_symm hpe

end Crystalline.GlobalCrystallineSituation.SmallSite

end
