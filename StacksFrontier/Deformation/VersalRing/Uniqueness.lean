module

public import StacksFrontier.Deformation.CofiberedPresentation.Prorepresentable
public import StacksFrontier.Deformation.CofiberedPresentation.Smooth
public import StacksFrontier.Deformation.FormalObject.AssociatedMorphismMap
public import StacksFrontier.Deformation.FormalObject.ProrepresentableMorphism
public import StacksFrontier.Deformation.RimSchlessingerCategory.Prorepresentable
public import StacksFrontier.Deformation.Smooth.PowerSeries
public import StacksFrontier.Deformation.Smooth.Versal
public import StacksFrontier.Deformation.VersalRing
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTranslation

/-!
# Uniqueness of versal rings

Let `ℱ` be a deformation category over `𝒞_Λ` whose tangent space and infinitesimal automorphisms
are finite-dimensional over `k`.  A versal formal object `ξ` of `ℱ` lying over `R` does not
determine a map out of `R`: if `η` is a formal object lying over `S`, there may be many maps
`R → S` pushing `ξ` forward to `η`.  The assertion proved here is that any two of them are
formally homotopic, so that `R` is determined by `ℱ` up to formal homotopy.

The argument is the one of the source.  Versality of `ξ` says exactly that the morphism
`ξ : U → ℱ` associated with it is smooth, where `U = R|_{𝒞_Λ}` is the restricted representable
functor of `R`; so the groupoid in functors `(U, R₁, s, t, c)` that Tag 06KY builds from it is
smooth, and it is prorepresentable by Tag 06L7.  Prorepresentability makes the arrow functor
`R₁` the restricted representable functor of a complete local algebra `B`, under which the
source and target projections become maps `s, t : R → B` and the identity arrows become a
common section `B → R` of both.  Smoothness of `s` makes `B` a power series ring over `R`, and
translating the coordinates by the section turns `t` into a map `h : R → R[[x₁, …, x_r]]` which
is the identity on constant coefficients.  Finally an isomorphism `f_*ξ ≅ η ≅ g_*ξ` is a
compatible family of arrows of the groupoid over `S`, hence a map `k : B → S` with `f = k ∘ s`
and `g = k ∘ t`; the triple `(r, h, k)` is a formal homotopy.

## Main definitions

* `Deformation.HasPowerSeriesCoordinates`: two maps out of `R` exhibit the target as a power
  series ring over `R` in which the second map is the identity on constant coefficients.
* `Deformation.presentationPoint`: the point of a presentation's arrow functor determined by an
  object of the two-fibre product `U ×_ℱ U`.

## Main results

* `Deformation.formallyHomotopic_of_isVersal`: **Stacks 0DQD**, two maps out of the base of a
  versal formal object that push it forward to the same formal object are formally homotopic.
* `Deformation.formallyHomotopic_of_powerSeriesArrow`: a formal homotopy read off from a map out
  of a power series ring.
* `Deformation.exists_representingArrowFunctor`: the arrow functor of a prorepresentable
  groupoid in functors is a restricted representable functor.
* `Deformation.exists_centered_coordinates`: coordinates on a power series ring can be
  translated so that the constant coefficient computes a prescribed augmentation.

## Implementation notes

### The hypotheses

The source states the two finiteness hypotheses as `dim_k Tℱ < ∞` and `dim_k Inf(ℱ) < ∞`.  The
first is `FiniteDimensional k (tangentModuleAt 𝓕 hp M)` at the rank-one module `M`, and the
second is finite-dimensionality of the value of `Deformation.infinitesimalAutomorphismLinearLift`
there, read at an arbitrary object of `ℱ` lying over the residue field and an arbitrary choice of
pushforwards; that is the form in which Tag 06L7 consumes it.  The tangent-space hypothesis is
not used: the source needs it to produce a versal formal object, which here is given.  It is
retained because the source states it.

`Λ` is Noetherian and `k` is finite over it throughout the chapter, so those are standing
assumptions of `𝒞_Λ` rather than additional hypotheses; Tag 06L7 requires them.

### Isomorphisms of pushforwards

The source's hypothesis `f_*ξ ≅ η` appears as `∃ a : ξ ⟶ η, a.base = f`, a morphism of formal
objects lying over `f`.  The completion of a category cofibered in groupoids is again cofibered
in groupoids, so a morphism over `f` is a cocartesian lift of `f`, which is to say an
isomorphism from the pushforward of `ξ` along `f` to `η`.

### Universes

The hom-set universe of `ℱ` is at most that of `𝒞_Λ`: the base category is written
`ArtinianLocalAlgCat.{u, max v v₃ w, w}` with `v₃` the hom-set universe of `ℱ`, which is the
convention of `StacksFrontier.Deformation.CofiberedPresentation.Prorepresentable` and is forced by
the prorepresentability criterion used there.  Every universe is a free variable.

### Maps out of the representing algebra

A map `B ⟶ S` is a compatible family of maps `B → S/m_S^{n+1}`, which is
`Deformation.representableSectionEquiv`.  That equivalence, rather than the isomorphism of
functors `Deformation.coyonedaIsoAdicCompletion` which it underlies, is what the proof uses: the
two have the same content, but comparing an adic section with a value of the completion functor
unfolds that functor, whereas the equivalence is applied to an argument directly.

## References

* [Stacks Project, Tag 0DQD](https://stacks.math.columbia.edu/tag/0DQD)
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite

universe u v w u₃ v₃ uC vC

namespace Deformation
variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The canonical points of a restricted representable functor -/

/-- Transporting the quotient homomorphism onto the `(n + 1)`-st adic truncation of `S` along
the transition map to the `n`-th gives the quotient homomorphism onto the `n`-th.  So the
quotient homomorphisms are a point of the restricted representable functor of `S` at every
level, compatible along the truncation tower. -/
lemma restrictedCoyoneda_map_quotientProjection (S : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    (restrictedCoyoneda S).map (AdicTruncation.transition S n) (quotientProjection S (n + 1)) =
      quotientProjection S n := by
  simpa only [representableSectionMap, Category.id_comp] using
    (representableSectionMap S S (𝟙 S)).compatible n

/-- The `n`-th value of the adic section attached to a morphism `f : R ⟶ S` is the image of the
quotient homomorphism onto the `n`-th adic truncation of `S` under precomposition with `f`. -/
lemma representableSectionMap_value {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (n : ℕ) :
    (representableSectionMap R S f).value n =
      (restrictedCoyonedaMap f).app (AdicTruncation.obj S n) (quotientProjection S n) := rfl

/-! ### Power series helpers -/

/-- A ring homomorphism out of a multivariable formal power series ring which kills every
variable factors through the constant coefficient.  The induction splits off one variable at a
time with `MvPowerSeries.finSuccEquiv`, writing a one-variable series as its constant term plus
a multiple of the variable. -/
private lemma hom_eq_constantCoeff {R S : Type*} [CommRing R] [CommRing S]
    (n : ℕ) (h : MvPowerSeries (Fin n) R →+* S)
    (hX : ∀ i, h (MvPowerSeries.X i) = 0) (f : MvPowerSeries (Fin n) R) :
    h f = h (MvPowerSeries.C (MvPowerSeries.constantCoeff f)) := by
  induction n with
  | zero =>
    congr 1
    apply (MvPowerSeries.isEmptyEquiv (Fin 0) R).injective
    simp [MvPowerSeries.isEmptyEquiv]
  | succ n ih =>
    let e := MvPowerSeries.finSuccEquiv R n
    let h' := h.comp e.symm.toRingHom
    have hx : h' PowerSeries.X = 0 := by
      change h (e.symm PowerSeries.X) = 0
      rw [← MvPowerSeries.finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply]
      exact hX 0
    have hc (i : Fin n) : (h'.comp PowerSeries.C) (MvPowerSeries.X i) = 0 := by
      change h (e.symm (PowerSeries.C (MvPowerSeries.X i))) = 0
      rw [← MvPowerSeries.finSuccEquiv_X_succ, AlgEquiv.symm_apply_apply]
      exact hX i.succ
    have hcc : MvPowerSeries.constantCoeff (PowerSeries.constantCoeff (e f)) =
        MvPowerSeries.constantCoeff f := by
      simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff,
        ← PowerSeries.coeff_zero_eq_constantCoeff]
      simpa only [Finsupp.cons_zero_zero] using
        (MvPowerSeries.coeff_coeff_finSuccEquiv f (k := 0) (x := 0))
    calc
      h f = h' (e f) := by simp [h']
      _ = h' (PowerSeries.C (PowerSeries.constantCoeff (e f))) := by
        conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (e f)]
        rw [map_add, map_mul, hx, zero_mul, zero_add]
      _ = h' (PowerSeries.C (MvPowerSeries.C (MvPowerSeries.constantCoeff f))) := by
        simpa only [RingHom.comp_apply, hcc] using
          ih (h'.comp PowerSeries.C) hc (PowerSeries.constantCoeff (e f))
      _ = h (MvPowerSeries.C (MvPowerSeries.constantCoeff f)) := by
        change h (e.symm _) = _
        rw [← MvPowerSeries.finSuccEquiv_C, AlgEquiv.symm_apply_apply]

/-- **Coordinates on a power series ring can be centred at an augmentation.**  Let `A` be an
algebra over a complete local ring `R` which is isomorphic to a power series ring over `R`, and
let `ε : A → R` be an `R`-algebra map.  Then the isomorphism can be chosen so that the constant
coefficient of the image of `a` is `ε a` for every `a`.

The images of the variables under `ε` lie in the maximal ideal of `R`: a unit among them would,
through the inverse of that unit, make `1` the image of a non-unit.  Translating the variables by
those elements is an automorphism of the power series ring because `R` is adically complete, and
after the translation `ε` is the constant coefficient, since the two agree on the variables and
on the constants. -/
lemma exists_centered_coordinates {R A : Type*}
    [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [IsAdicComplete (maximalIdeal R) R]
    (ε : A →ₐ[R] R) (n : ℕ) (e : A ≃ₐ[R] MvPowerSeries (Fin n) R) :
    ∃ e' : A ≃ₐ[R] MvPowerSeries (Fin n) R,
      ∀ x, MvPowerSeries.constantCoeff (e' x) = ε x := by
  let q := ε.comp e.symm.toAlgHom
  let d (i : Fin n) : R := q (MvPowerSeries.X i)
  have hd : ∀ i, d i ∈ maximalIdeal R := by
    intro i
    rw [mem_maximalIdeal]
    rintro ⟨a, ha⟩
    have hunit : IsUnit (1 - MvPowerSeries.C (↑(a⁻¹) : R) *
        (MvPowerSeries.X i : MvPowerSeries (Fin n) R)) := by
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    have heq : q (MvPowerSeries.C (↑(a⁻¹) : R)) * d i = 1 := by
      rw [show q (MvPowerSeries.C (↑(a⁻¹) : R)) = ↑(a⁻¹) from q.commutes _, ← ha]
      exact a.inv_mul
    have hz := hunit.map q.toMonoidHom
    change IsUnit (q (1 - MvPowerSeries.C (↑(a⁻¹) : R) * MvPowerSeries.X i)) at hz
    simp only [map_sub, map_one, map_mul] at hz
    change IsUnit (1 - q (MvPowerSeries.C (↑(a⁻¹) : R)) * d i) at hz
    rw [heq, sub_self] at hz
    exact not_isUnit_zero hz
  have hnd : ∀ i, (-d) i ∈ maximalIdeal R := fun i => (maximalIdeal R).neg_mem (hd i)
  let shift := ShiftConstr.shiftAlgHom (maximalIdeal R) d hd
  let negShift := ShiftConstr.shiftAlgHom (maximalIdeal R) (-d) hnd
  let a := AlgEquiv.ofBijective shift (ShiftConstr.shiftAlgHom_bijective _ _ _)
  have hq (f : MvPowerSeries (Fin n) R) :
      q (negShift f) = MvPowerSeries.constantCoeff f := by
    have hx (i : Fin n) : (q.comp negShift) (MvPowerSeries.X i) = 0 := by
      change q (negShift (MvPowerSeries.X i)) = 0
      rw [ShiftConstr.shiftAlgHom_X, map_add]
      change d i + q (MvPowerSeries.C (-d i)) = 0
      rw [show q (MvPowerSeries.C (-d i)) = -d i from q.commutes _]
      exact add_neg_cancel _
    exact (hom_eq_constantCoeff n (q.comp negShift).toRingHom hx f).trans
      ((q.comp negShift).commutes _)
  refine ⟨e.trans a, fun x => ?_⟩
  have hc := DFunLike.congr_fun
    (ShiftConstr.shiftAlgHom_comp_eq_id (maximalIdeal R) (-d) d hnd hd (by simp)) (e x)
  have hh := hq (shift (e x))
  change q (negShift (shift (e x))) = _ at hh
  rw [show negShift (shift (e x)) = e x from hc] at hh
  exact hh.symm.trans (congrArg ε (e.symm_apply_apply x))

/-! ### From a represented smooth arrow space to a formal homotopy -/

/-- Two morphisms `s, t : R ⟶ A` of complete local `Λ`-algebras have power series coordinates
when, regarding `A` as an `R`-algebra through `s`, it is isomorphic to a multivariable formal
power series ring over `R` in which `t` becomes the identity after taking constant coefficients.
This is the data `(r, h)` of a formal homotopy, before a lift to the target is given. -/
def HasPowerSeriesCoordinates {R A : CompleteLocalAlgCat.{u, v, w} Λ k}
    (s t : R ⟶ A) : Prop :=
  let : Algebra R A := s.hom.toRingHom.toAlgebra
  ∃ n, ∃ e : A ≃ₐ[R] MvPowerSeries (Fin n) R,
    ∀ a, MvPowerSeries.constantCoeff (e (t.hom a)) = a

/-- **A map out of a power series ring gives a formal homotopy.**  If `s, t : R ⟶ A` have power
series coordinates and `arrow : A ⟶ S` composes with `s` to `f` and with `t` to `g`, then `f` and
`g` are formally homotopic: the coordinates turn `t` into the map `h : R → R[[x₁, …, x_r]]` of the
definition, which is the identity on constant coefficients, and `arrow` into the lift out of the
power series ring; the two specialisations are then `f` and `g`. -/
theorem formallyHomotopic_of_powerSeriesArrow
    {R A S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (s t : R ⟶ A) (hps : HasPowerSeriesCoordinates s t) (arrow : A ⟶ S) (f g : R ⟶ S)
    (hf : s ≫ arrow = f) (hg : t ≫ arrow = g) :
    CompleteLocalAlgCat.FormallyHomotopic f g := by
  let : Algebra R A := s.hom.toRingHom.toAlgebra
  obtain ⟨n, e, hconst⟩ := hps
  let h : R →ₐ[Λ] MvPowerSeries (Fin n) R :=
    (e.toAlgHom.restrictScalars Λ).comp t.hom
  let l : MvPowerSeries (Fin n) R →ₐ[Λ] S :=
    arrow.hom.comp (e.symm.toAlgHom.restrictScalars Λ)
  have hlocal : IsLocalHom h.toRingHom := by
    let : IsLocalHom t.hom.toRingHom := t.isLocal
    let : IsLocalHom e.toRingEquiv.toRingHom := isLocalHom_toRingHom e.toRingEquiv
    exact RingHom.isLocalHom_comp e.toRingEquiv.toRingHom t.hom.toRingHom
  have llocal : IsLocalHom l.toRingHom := by
    let : IsLocalHom arrow.hom.toRingHom := arrow.isLocal
    let : IsLocalHom e.symm.toRingEquiv.toRingHom := isLocalHom_toRingHom e.symm.toRingEquiv
    exact RingHom.isLocalHom_comp arrow.hom.toRingHom e.symm.toRingEquiv.toRingHom
  refine ⟨n, h, l, hlocal, llocal, hconst, ?_, ?_⟩
  · intro a
    rw [← hf]
    change (s ≫ arrow).hom a = l (MvPowerSeries.C a)
    dsimp [l]
    rw [← show e (s.hom a) = MvPowerSeries.C a from e.commutes a, AlgEquiv.symm_apply_apply]
  · intro a
    rw [← hg]
    dsimp [l, h]
    rw [AlgEquiv.symm_apply_apply]

/-- **A common section centres power series coordinates.**  If `s` exhibits `B` as a power series
ring over `R` and `σ : B ⟶ R` is a section of both `s` and `t`, then `s` and `t` have power series
coordinates: the coordinates of `s` are translated so that the constant coefficient is `σ`. -/
private theorem hasPowerSeriesCoordinates_of_section {R B : CompleteLocalAlgCat.{u, v, w} Λ k}
    {s t : R ⟶ B} (hs : IsPowerSeriesOver s) (σ : B ⟶ R) (hsσ : s ≫ σ = 𝟙 R)
    (htσ : t ≫ σ = 𝟙 R) : HasPowerSeriesCoordinates s t := by
  let : Algebra R B := s.hom.toRingHom.toAlgebra
  let ε : B →ₐ[R] R :=
    { __ := σ.hom.toRingHom
      commutes' r := congrArg (fun q : R ⟶ R => q.hom r) hsσ }
  obtain ⟨n, ⟨e₀⟩⟩ := hs
  obtain ⟨e₁, he₁⟩ := exists_centered_coordinates ε n e₀
  refine ⟨n, e₁, fun r => ?_⟩
  rw [he₁]
  exact congrArg (fun q : R ⟶ R => q.hom r) htσ

/-! ### Representability of the arrow functor -/

section

/-- The comparison of arrow functors induced by an isomorphism of groupoids in functors. -/
def groupoidArrowsIso {C : Type uC} [Category.{vC, uC} C]
    {G H : GroupoidInFunctors C} (e : G ≅ H) : G.arrows ≅ H.arrows where
  hom := e.hom.mapArrows
  inv := e.inv.mapArrows
  hom_inv_id := by
    have h := congrArg (fun f : GroupoidInFunctors.Hom G G => f.mapArrows) e.hom_inv_id
    change e.hom.mapArrows ≫ e.inv.mapArrows = 𝟙 G.arrows at h
    exact h
  inv_hom_id := by
    have h := congrArg (fun f : GroupoidInFunctors.Hom H H => f.mapArrows) e.inv_hom_id
    change e.inv.mapArrows ≫ e.hom.mapArrows = 𝟙 H.arrows at h
    exact h

end

/-- **The arrow functor of a prorepresentable groupoid in functors is a restricted
representable functor.** Prorepresentability provides a representable groupoid in functors on
complete local algebras whose restriction it is, and the arrow functor of a representable
groupoid is a universe-lifted covariant representable functor; the lift is into a universe the
values already lie in, so it can be removed. -/
lemma exists_representingArrowFunctor
    (G : GroupoidInFunctors.{_, v, v} (ArtinianLocalAlgCat.{u, v, w} Λ k))
    (hG : GroupoidInFunctors.IsProrepresentable.{u, v, w, v} G) :
    ∃ B : CompleteLocalAlgCat.{u, v, w} Λ k, Nonempty (G.arrows ≅ restrictedCoyoneda B) := by
  obtain ⟨H, ⟨P, ⟨eHP⟩⟩, ⟨eGH⟩⟩ := hG
  refine ⟨P.arrows, ⟨groupoidArrowsIso eGH ≪≫ ?_⟩⟩
  exact Functor.isoWhiskerLeft artinianToComplete
    (groupoidArrowsIso eHP ≪≫ (CategoryTheory.uliftCoyonedaIsoCoyoneda.{v}).app (op P.arrows))

section
universe a b

/-- A natural transformation into a universe-lifted functor, with the lift removed. -/
def natTransDown {F U : ArtinianLocalAlgCat.{u, max a b, w} Λ k ⥤ Type (max a b)}
    (α : F ⟶ U ⋙ uliftFunctor.{a, max a b}) : F ⟶ U where
  app T := TypeCat.ofHom fun x => (α.app T x).down
  naturality T S f := by
    apply TypeCat.homEquiv.injective
    funext x
    change (α.app S (F.map f x)).down = U.map f ((α.app T x).down)
    exact congrArg ULift.down (NatTrans.naturality_apply α f x)

/-- **Smoothness transports to the representing functor.** A projection out of the arrow
functor is smooth as a morphism of categories of elements if and only if its transport along a
representing isomorphism is, both being the elementwise lifting condition. -/
theorem smooth_of_representing_iso
    {B : CompleteLocalAlgCat.{u, max a b, w} Λ k}
    {G U : ArtinianLocalAlgCat.{u, max a b, w} Λ k ⥤ Type (max a b)}
    (e : restrictedCoyoneda B ≅ G) (π : G ⟶ U ⋙ uliftFunctor.{a, max a b})
    (hπ : IsSmooth (elementsBasedFunctor π)) :
    IsSmooth (elementsBasedFunctor (natTransDown (e.hom ≫ π))) := by
  apply (isSmooth_elementsBasedFunctor_iff _).2
  intro B₀ A₀ q hq xA yB hxy
  have hrel : π.app A₀ (e.hom.app A₀ xA) = ULift.up (U.map q yB) := by
    apply ULift.ext
    exact hxy
  obtain ⟨zB, hzmap, hzπ⟩ := (isSmooth_elementsBasedFunctor_iff π).1 hπ q hq
    (e.hom.app A₀ xA) (ULift.up yB) hrel
  refine ⟨e.inv.app B₀ zB, ?_, ?_⟩
  · rw [← NatTrans.naturality_apply e.inv q zB, hzmap]
    exact (e.app A₀).hom_inv_id_apply xA
  · change (π.app B₀ (e.hom.app B₀ (e.inv.app B₀ zB))).down = yB
    have hid : e.hom.app B₀ (e.inv.app B₀ zB) = zB := (e.app B₀).inv_hom_id_apply zB
    rw [hid]
    exact ULift.up_injective hzπ

end

/-- The image of an adic section under a natural transformation. -/
noncomputable def adicSectionMapNat {F G : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
    (α : F ⟶ G) (S : CompleteLocalAlgCat.{u, v, w} Λ k) (x : AdicSection F S) :
    AdicSection G S where
  value n := α.app (AdicTruncation.obj S n) (x.value n)
  compatible n := by
    calc
      G.map (AdicTruncation.transition S n)
          (α.app (AdicTruncation.obj S (n + 1)) (x.value (n + 1))) =
          α.app (AdicTruncation.obj S n)
            (F.map (AdicTruncation.transition S n) (x.value (n + 1))) :=
              (NatTrans.naturality_apply α (AdicTruncation.transition S n) _).symm
      _ = α.app (AdicTruncation.obj S n) (x.value n) := congrArg _ (x.compatible n)

/-- **Maps out of a representing algebra.**  Let `e` identify `A` with the restricted
representable functor of `B`, and let `σ` be a compatible family of points of `A` over `S`, so
that `σ` corresponds to a map `B ⟶ S`.  If `m : R ⟶ B` corresponds to a projection `ψ` of `A`
and the projections of `σ` are the points of a map `z : R ⟶ S`, then `m` followed by the map
of `σ` is `z`. -/
private theorem comp_representableSectionEquiv_symm
    {R B S : CompleteLocalAlgCat.{u, max v v₃ w, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k ⥤ Type (max v v₃ w)}
    (e : restrictedCoyoneda B ≅ A) (σ : AdicSection A S)
    (ψ : A ⟶ restrictedCoyoneda R ⋙ uliftFunctor.{v₃, max v v₃ w}) (m : R ⟶ B) (z : R ⟶ S)
    (hm : restrictedCoyonedaMap m = natTransDown.{u, w, v₃, max v w} (e.hom ≫ ψ))
    (hz : ∀ n, (ψ.app (AdicTruncation.obj S n) (σ.value n)).down =
      (restrictedCoyonedaMap z).app (AdicTruncation.obj S n) (quotientProjection S n)) :
    m ≫ (representableSectionEquiv B S).symm (adicSectionMapNat e.inv S σ) = z := by
  let arrow := (representableSectionEquiv B S).symm (adicSectionMapNat e.inv S σ)
  have harrow : representableSectionMap B S arrow = adicSectionMapNat e.inv S σ :=
    (representableSectionEquiv B S).apply_symm_apply _
  have hval (n : ℕ) : (restrictedCoyonedaMap arrow).app (AdicTruncation.obj S n)
      (quotientProjection S n) = e.inv.app (AdicTruncation.obj S n) (σ.value n) :=
    (representableSectionMap_value arrow n).symm.trans
      (congrArg (fun q : AdicSection (restrictedCoyoneda B) S => q.value n) harrow)
  have hcancel (n : ℕ) : e.hom.app (AdicTruncation.obj S n)
      (e.inv.app (AdicTruncation.obj S n) (σ.value n)) = σ.value n :=
    (e.app (AdicTruncation.obj S n)).inv_hom_id_apply (σ.value n)
  apply (representableSectionEquiv R S).injective
  apply AdicSection.ext
  intro n
  change (restrictedCoyonedaMap m).app (AdicTruncation.obj S n)
    ((restrictedCoyonedaMap arrow).app (AdicTruncation.obj S n) (quotientProjection S n)) = _
  rw [hval, hm]
  change (ψ.app (AdicTruncation.obj S n)
    (e.hom.app (AdicTruncation.obj S n) (e.inv.app (AdicTruncation.obj S n) (σ.value n)))).down = _
  rw [hcancel]
  exact hz n

/-! ### Points of the arrow functor coming from the two-fibre product -/

section PresentationPoints
universe uU uF2 vF2

variable {C : Type uC} [Category.{vC} C] {F : Type uF2} [Category.{vF2} F]
  {p : F ⥤ C} {U : C ⥤ Type uU} {f : U.Elements ⥤ F}
  {hOver : f ⋙ p = Functor.Elements.π U}

/-- A transport cancels against its inverse in the middle of a composite. -/
private lemma eqToHom_cancel_mid {A : Type*} [Category A] {X Y Z W V : A}
    (h : X = Y) (h' : Z = W) (g : Y ⟶ Z) (c : W ⟶ V) :
    eqToHom h.symm ≫ (eqToHom h ≫ g ≫ eqToHom h') ≫ c = g ≫ eqToHom h' ≫ c := by
  subst h h'
  simp

/-- The point of a presentation's arrow functor determined by an object of the two-fibre product
`U ×_ℱ U`.  The equivalence of the arrow functor's category of elements with the two-fibre
product produces an object of the former whose base is only propositionally equal to the base of
the given object; the counit of the equivalence transports the point along that identification. -/
noncomputable def presentationPoint (P : PresentationGroupoid p U f hOver)
    (q : TwoFibreProductOver (Functor.Elements.π U) (Functor.Elements.π U) p f f) :
    P.arrows.obj q.base :=
  let E := P.fibreProductEquivalence
  let j := E.inverse.obj q
  let h := Functor.congr_obj P.fibreProductOverBase j
  P.arrows.map (eqToHom h.symm ≫ (E.counitIso.hom.app q).hbase) j.2

/-- The points attached to objects of the two-fibre product are compatible with its morphisms:
transporting the point of the source along the base map of a morphism gives the point of the
target. -/
lemma presentationPoint_naturality (P : PresentationGroupoid p U f hOver)
    {q r : TwoFibreProductOver (Functor.Elements.π U) (Functor.Elements.π U) p f f}
    (a : q ⟶ r) :
    P.arrows.map a.hbase (presentationPoint P q) = presentationPoint P r := by
  let E := P.fibreProductEquivalence
  let j := E.inverse.map a
  have hj := j.2
  have hn := congrArg TwoFibreProductOver.Hom.hbase (E.counitIso.hom.naturality a)
  have ho := Functor.congr_hom P.fibreProductOverBase j
  dsimp only [Functor.comp_map, Functor.Elements.π_map] at ho
  change (E.functor.map j).hbase = _ at ho
  change (E.functor.map j).hbase ≫ (E.counitIso.hom.app r).hbase =
    (E.counitIso.hom.app q).hbase ≫ a.hbase at hn
  let hq : (E.functor.obj (E.inverse.obj q)).base = (E.inverse.obj q).1 :=
    Functor.congr_obj P.fibreProductOverBase _
  let hr : (E.functor.obj (E.inverse.obj r)).base = (E.inverse.obj r).1 :=
    Functor.congr_obj P.fibreProductOverBase _
  let kq : (E.inverse.obj q).1 ⟶ q.base := eqToHom hq.symm ≫ (E.counitIso.hom.app q).hbase
  let kr : (E.inverse.obj r).1 ⟶ r.base := eqToHom hr.symm ≫ (E.counitIso.hom.app r).hbase
  have hk : kq ≫ a.hbase = j.1 ≫ kr := by
    dsimp [kq, kr]
    rw [Category.assoc, ← hn, ho]
    apply eqToHom_cancel_mid (A := C)
  change P.arrows.map a.hbase (P.arrows.map kq (E.inverse.obj q).2) =
    P.arrows.map kr (E.inverse.obj r).2
  calc
    _ = P.arrows.map (kq ≫ a.hbase) (E.inverse.obj q).2 :=
      (Functor.map_comp_apply _ _ _ _).symm
    _ = P.arrows.map (j.1 ≫ kr) (E.inverse.obj q).2 := congrArg (fun l => P.arrows.map l _) hk
    _ = P.arrows.map kr (P.arrows.map j.1 (E.inverse.obj q).2) :=
      Functor.map_comp_apply _ _ _ _
    _ = _ := congrArg (P.arrows.map kr) hj

/-- A projection of an arrow functor to `U`, evaluated at a transported point, is the transport of
the value of the projection at the original point, provided the transports of the two points of
`U` involved are compatible. -/
private lemma projection_map_eq {A : C ⥤ Type (max vF2 uU)}
    (N : A ⟶ U ⋙ uliftFunctor.{vF2, uU}) {j : A.Elements} {T B V : C} (kk : j.1 ⟶ T)
    (ι : V ⟶ j.1) (b : V ⟶ B) (h : B ⟶ T) (y : U.obj V)
    (hs : U.map ι y = (N.app j.1 j.2).down) (hk : ι ≫ kk = b ≫ h) :
    (N.app T (A.map kk j.2)).down = U.map h (U.map b y) := by
  have hn := NatTrans.naturality_apply N kk j.2
  change N.app T (A.map kk j.2) = _ at hn
  rw [hn, ← Functor.map_comp_apply, ← hk, Functor.map_comp_apply, hs]
  rfl

/-- The source of the point attached to an object of the two-fibre product is the second of the
two elements of `U` that object consists of. -/
lemma presentationPoint_source (P : PresentationGroupoid p U f hOver)
    (q : TwoFibreProductOver (Functor.Elements.π U) (Functor.Elements.π U) p f f) :
    (P.source.app q.base (presentationPoint P q)).down = U.map (eqToHom q.hy) q.y.2 := by
  let E := P.fibreProductEquivalence
  let j := E.inverse.obj q
  let c := E.counitIso.hom.app q
  let h := Functor.congr_obj P.fibreProductOverBase j
  let kk := eqToHom h.symm ≫ c.hbase
  have hsv := P.sourceProjectionIso_vertical j
  change (P.sourceProjectionIso.hom.app j).1 = _ at hsv
  have := c.hb
  have hfac := IsHomLift.fac' (Functor.Elements.π U) c.hbase c.b
  change c.b.1 = _ at hfac
  have hk : (P.sourceProjectionIso.hom.app j).1 ≫ kk = c.b.1 ≫ eqToHom q.hy := by
    rw [hsv, hfac]
    dsimp [kk]
    simp only [← Category.assoc]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact eqToHom_trans_assoc _ _ _
  exact (projection_map_eq P.source kk _ c.b.1 (eqToHom q.hy) (E.functor.obj j).y.2
    (P.sourceProjectionIso.hom.app j).2 hk).trans (congrArg (U.map (eqToHom q.hy)) c.b.2)

/-- The target of the point attached to an object of the two-fibre product is the first of the
two elements of `U` that object consists of. -/
lemma presentationPoint_target (P : PresentationGroupoid p U f hOver)
    (q : TwoFibreProductOver (Functor.Elements.π U) (Functor.Elements.π U) p f f) :
    (P.target.app q.base (presentationPoint P q)).down = U.map (eqToHom q.hx) q.x.2 := by
  let E := P.fibreProductEquivalence
  let j := E.inverse.obj q
  let c := E.counitIso.hom.app q
  let h := Functor.congr_obj P.fibreProductOverBase j
  let kk := eqToHom h.symm ≫ c.hbase
  have hsv := P.targetProjectionIso_vertical j
  change (P.targetProjectionIso.hom.app j).1 = _ at hsv
  have := c.ha
  have hfac := IsHomLift.fac' (Functor.Elements.π U) c.hbase c.a
  change c.a.1 = _ at hfac
  have hk : (P.targetProjectionIso.hom.app j).1 ≫ kk = c.a.1 ≫ eqToHom q.hx := by
    rw [hsv, hfac]
    dsimp [kk]
    simp only [← Category.assoc]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact eqToHom_trans_assoc _ _ _
  exact (projection_map_eq P.target kk _ c.a.1 (eqToHom q.hx) (E.functor.obj j).x.2
    (P.targetProjectionIso.hom.app j).2 hk).trans (congrArg (U.map (eqToHom q.hx)) c.a.2)

end PresentationPoints

/-! ### Maps out of the representing algebra of a presentation -/

section RepresentingAlgebra

variable {F : Type u₃} [Category.{v₃} F]

/-- **The source and target of a smooth presentation have power series coordinates.**  Let `P` be
a smooth presentation of `U = R|_{𝒞_Λ}` whose arrow functor is represented by `B`, and let
`s, t : R ⟶ B` correspond to its source and target.  Then `s` exhibits `B` as a power series ring
over `R`, the identity arrows give a common section of `s` and `t`, and so `s` and `t` have power
series coordinates. -/
private theorem hasPowerSeriesCoordinates_of_presentation
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k}
    {R B : CompleteLocalAlgCat.{u, max v v₃ w, w} Λ k} {f : (restrictedCoyoneda R).Elements ⥤ F}
    {hOver : f ⋙ p = Functor.Elements.π (restrictedCoyoneda R)}
    (P : PresentationGroupoid p (restrictedCoyoneda R) f hOver)
    (hP : GroupoidInFunctors.IsSmooth P.toGroupoidInFunctors)
    (e : restrictedCoyoneda B ≅ P.toGroupoidInFunctors.arrows) {s t : R ⟶ B}
    (hs : restrictedCoyonedaMap s =
      natTransDown.{u, w, v₃, max v w} (e.hom ≫ P.toGroupoidInFunctors.source))
    (ht : restrictedCoyonedaMap t =
      natTransDown.{u, w, v₃, max v w} (e.hom ≫ P.toGroupoidInFunctors.target)) :
    HasPowerSeriesCoordinates s t := by
  let G := P.toGroupoidInFunctors
  have h := smooth_of_representing_iso.{u, w, v₃, max v w} e G.source hP.1
  rw [← hs] at h
  let identitySection : AdicSection G.arrows R :=
    { value n := G.identity (AdicTruncation.obj R n) (ULift.up (quotientProjection R n))
      compatible n :=
        (evalMap_identity G (AdicTruncation.transition R n) _).trans <|
          congrArg (G.identity (AdicTruncation.obj R n))
            (congrArg ULift.up (restrictedCoyoneda_map_quotientProjection R n)) }
  exact hasPowerSeriesCoordinates_of_section
    ((restrictedRepresentableMap_isSmooth_iff_isPowerSeriesOver s).mp h) _
    (comp_representableSectionEquiv_symm e identitySection G.source s (𝟙 R)
      hs fun n => by
        let T := AdicTruncation.obj R n
        let x : G.Evaluation T := ULift.up (quotientProjection R n)
        let : Groupoid (G.Evaluation T) := G.evaluationGroupoid T
        exact congrArg ULift.down (G.evaluationArrowEquiv T x x (𝟙 x)).2.1)
    (comp_representableSectionEquiv_symm e identitySection G.target t (𝟙 R)
      ht fun n => by
        let T := AdicTruncation.obj R n
        let x : G.Evaluation T := ULift.up (quotientProjection R n)
        let : Groupoid (G.Evaluation T) := G.evaluationGroupoid T
        exact congrArg ULift.down (G.evaluationArrowEquiv T x x (𝟙 x)).2.2)

/-- The object of the two-fibre product `U ×_ℱ U` over the `n`-th adic truncation of `η.base`
given by two isomorphisms `f_*ξ ≅ η ≅ g_*ξ` of associated morphisms. -/
private noncomputable def twoFibreProductObjOfIsos {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) {ξ η : FormalObject p} (pushforwards : ChosenPushforwards p)
    {a b : ξ ⟶ η}
    (τa : BasedFunctor.comp (restrictedRepresentableMap a.base)
      (associatedMorphism hp ξ pushforwards).toBasedFunctor ≅
        (associatedMorphism hp η pushforwards).toBasedFunctor)
    (τb : BasedFunctor.comp (restrictedRepresentableMap b.base)
      (associatedMorphism hp ξ pushforwards).toBasedFunctor ≅
        (associatedMorphism hp η pushforwards).toBasedFunctor) (n : ℕ) :
    TwoFibreProductOver (Functor.Elements.π (restrictedCoyoneda ξ.base))
      (Functor.Elements.π (restrictedCoyoneda ξ.base)) p
      (associatedMorphism hp ξ pushforwards).toBasedFunctor.toFunctor
      (associatedMorphism hp ξ pushforwards).toBasedFunctor.toFunctor := by
  let α : (restrictedCoyoneda η.base).Elements :=
    Functor.elementsMk _ (AdicTruncation.obj η.base n) (quotientProjection η.base n)
  let ib := ((BasedNatTrans.forgetful _ _).mapIso τb).app α
  let ia := ((BasedNatTrans.forgetful _ _).mapIso τa).app α
  refine ⟨AdicTruncation.obj η.base n, (restrictedRepresentableMap b.base).toFunctor.obj α,
    (restrictedRepresentableMap a.base).toFunctor.obj α, rfl, rfl, ib ≪≫ ia.symm, ?_⟩
  have hbb : p.IsHomLift (𝟙 (AdicTruncation.obj η.base n)) (τb.hom.toNatTrans.app α) :=
    τb.hom.isHomLift rfl
  have haa : p.IsHomLift (𝟙 (AdicTruncation.obj η.base n)) (τa.inv.toNatTrans.app α) :=
    τa.inv.isHomLift rfl
  let := hbb
  let := haa
  change p.IsHomLift (𝟙 (AdicTruncation.obj η.base n)) (ib.hom ≫ ia.symm.hom)
  exact IsHomLift.comp p (𝟙 (AdicTruncation.obj η.base n))
    (𝟙 (AdicTruncation.obj η.base n)) (τb.hom.toNatTrans.app α) (τa.inv.toNatTrans.app α)

/-- **Two maps pushing `ξ` forward to `η` give a compatible family of arrows.**  Two morphisms
`a, b : ξ ⟶ η` of formal objects give, through the isomorphisms `f_*ξ ≅ η ≅ g_*ξ`, a compatible
family over `η.base` of arrows of the presentation attached to `ξ`, whose sources are the points
of `a.base` and whose targets are the points of `b.base`. -/
private theorem exists_adicSection_presentationGroupoid
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k) (hp : IsCofiberedInGroupoids p)
    {ξ η : FormalObject p} (pushforwards : ChosenPushforwards p) (a b : ξ ⟶ η) :
    let X := (associatedMorphism hp ξ pushforwards).toBasedFunctor
    let P := presentationGroupoid p (restrictedCoyoneda ξ.base) X.toFunctor X.w hp
    ∃ σ : AdicSection P.arrows η.base,
      (∀ n, (P.source.app (AdicTruncation.obj η.base n) (σ.value n)).down =
        (restrictedCoyonedaMap a.base).app (AdicTruncation.obj η.base n)
          (quotientProjection η.base n)) ∧
      ∀ n, (P.target.app (AdicTruncation.obj η.base n) (σ.value n)).down =
        (restrictedCoyonedaMap b.base).app (AdicTruncation.obj η.base n)
          (quotientProjection η.base n) := by
  intro X P
  obtain ⟨τa, -⟩ := associatedMorphism_map hp a pushforwards
  obtain ⟨τb, -⟩ := associatedMorphism_map hp b pushforwards
  let U := restrictedCoyoneda ξ.base
  let α : ∀ n : ℕ, (restrictedCoyoneda η.base).Elements :=
    fun n => Functor.elementsMk _ (AdicTruncation.obj η.base n) (quotientProjection η.base n)
  let αstep : ∀ n : ℕ, α (n + 1) ⟶ α n := fun n =>
    Functor.Elements.homMk (AdicTruncation.transition η.base n)
      (restrictedCoyoneda_map_quotientProjection η.base n)
  let fa := restrictedRepresentableMap a.base
  let fb := restrictedRepresentableMap b.base
  let Y := (associatedMorphism hp η pushforwards).toBasedFunctor.toFunctor
  let Q := twoFibreProductObjOfIsos hp pushforwards τa τb
  let : Category.{max v v₃ w}
      (TwoFibreProductOver (Functor.Elements.π U) (Functor.Elements.π U) p X.toFunctor
        X.toFunctor) :=
    CategoryTheory.TwoFibreProductOver.instCategory (p𝒳 := Functor.Elements.π U)
      (p𝒴 := Functor.Elements.π U) (p𝒮 := p) (F := X.toFunctor) (G := X.toFunctor)
  have hQstep (n : ℕ) : ∃ φ : Q (n + 1) ⟶ Q n, φ.hbase = AdicTruncation.transition η.base n := by
    have hstep : (restrictedRepresentable η.base).p.IsHomLift
        (AdicTruncation.transition η.base n) (αstep n) :=
      IsHomLift.of_fac' _ _ _ rfl rfl (by rfl)
    let := hstep
    refine ⟨⟨AdicTruncation.transition η.base n, fb.toFunctor.map (αstep n),
      fa.toFunctor.map (αstep n),
      BasedFunctor.preserves_isHomLift fb (AdicTruncation.transition η.base n) (αstep n),
      BasedFunctor.preserves_isHomLift fa (AdicTruncation.transition η.base n) (αstep n), ?_⟩,
      rfl⟩
    have hbn : X.toFunctor.map (fb.toFunctor.map (αstep n)) ≫ τb.hom.app (α n) =
        τb.hom.app (α (n + 1)) ≫ Y.map (αstep n) := τb.hom.toNatTrans.naturality (αstep n)
    have han : Y.map (αstep n) ≫ τa.inv.app (α n) =
        τa.inv.app (α (n + 1)) ≫ X.toFunctor.map (fa.toFunctor.map (αstep n)) :=
      τa.inv.toNatTrans.naturality (αstep n)
    change X.toFunctor.map (fb.toFunctor.map (αstep n)) ≫
        (τb.hom.app (α n) ≫ τa.inv.app (α n)) =
      (τb.hom.app (α (n + 1)) ≫ τa.inv.app (α (n + 1))) ≫
        X.toFunctor.map (fa.toFunctor.map (αstep n))
    exact (Category.assoc _ _ _).symm.trans <| (hbn =≫ τa.inv.app (α n)).trans <|
      (Category.assoc _ _ _).trans <|
        (congrArg (τb.hom.app (α (n + 1)) ≫ ·) han).trans (Category.assoc _ _ _).symm
  refine ⟨{ value n := presentationPoint P (Q n), compatible n := ?_ }, fun n => ?_, fun n => ?_⟩
  · obtain ⟨φ, hφ⟩ := hQstep n
    have h := presentationPoint_naturality P φ
    rwa [hφ] at h
  · refine (presentationPoint_source P (Q n)).trans ?_
    exact congrArg (fun l : U.obj (AdicTruncation.obj η.base n) ⟶
      U.obj (AdicTruncation.obj η.base n) => l ((Q n).y.2)) (U.map_id _)
  · refine (presentationPoint_target P (Q n)).trans ?_
    exact congrArg (fun l : U.obj (AdicTruncation.obj η.base n) ⟶
      U.obj (AdicTruncation.obj η.base n) => l ((Q n).x.2)) (U.map_id _)

end RepresentingAlgebra

/-! ### Stacks 0DQD -/

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] {F : Type u₃} [Category.{v₃} F]

/-- **Stacks Project, Tag 0DQD.**  Let `ℱ` be a deformation category over `𝒞_Λ` whose tangent
space and infinitesimal automorphisms are finite-dimensional over `k`.  Let `ξ` be a versal
formal object lying over `R`, and let `η` be a formal object lying over `S`.  Then any two maps
`f, g : R → S` with `f_*ξ ≅ η ≅ g_*ξ` are formally homotopic. -/
@[stacks 0DQD]
theorem formallyHomotopic_of_isVersal
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k)
    (hp : IsDeformationCategory.{u, max v v₃, w} p)
    (_hT : FiniteDimensional k
      ↥(tangentModuleAt.{u, max v v₃, w} (BasedCategory.ofFunctor p) hp
        (FGModuleCat.of k (ULift.{max v v₃} k))))
    (hInf : ∀ (x : F) (P : ChosenPushforwardsAt p x),
      p.obj x = residueFieldObject.{u, max v v₃, w} Λ k →
      FiniteDimensional k
        ↥((infinitesimalAutomorphismLinearLift.{u, max v v₃, w} P hp.satisfiesRS).functor.obj
          (FGModuleCat.of k (ULift.{max v v₃} k))))
    (ξ η : FormalObject p) (hξ : IsVersal hp.predeformation.cofibered ξ)
    (f g : ξ.base ⟶ η.base)
    (hf : ∃ a : ξ ⟶ η, a.base = f) (hg : ∃ a : ξ ⟶ η, a.base = g) :
    CompleteLocalAlgCat.FormallyHomotopic f g := by
  let pushforwards := chosenPushforwardsOfCofibered p hp.predeformation.cofibered
  let associated := associatedMorphism hp.predeformation.cofibered ξ pushforwards
  have hassociated : IsSmooth associated.toBasedFunctor := hξ pushforwards
  let U := restrictedCoyoneda ξ.base
  let presentation := presentationGroupoid p U associated.toBasedFunctor.toFunctor
    associated.toBasedFunctor.w hp.predeformation.cofibered
  let G := presentation.toGroupoidInFunctors
  have hGsmooth : GroupoidInFunctors.IsSmooth G :=
    isSmooth_presentationGroupoid p U associated.toBasedFunctor hp.predeformation.cofibered
      hassociated
  have hU : IsProrepresentable U := ⟨ξ.base, ⟨Iso.refl _⟩⟩
  let y₀ : U.Elements :=
    U.elementsMk (residueFieldObject.{u, max v v₃, w} Λ k) (residuePoint ξ.base)
  let PF := chosenPushforwardsAtOfCofibered hp.predeformation.cofibered
    (associated.toBasedFunctor.toFunctor.obj y₀)
  have hGprorepresentable : GroupoidInFunctors.IsProrepresentable G :=
    isProrepresentable_presentationGroupoid.{u, v, w, u₃, v₃} p U
      associated.toBasedFunctor.toFunctor associated.toBasedFunctor.w hU hp PF
      (hInf _ PF (Functor.congr_obj associated.toBasedFunctor.w y₀))
  obtain ⟨B, ⟨eArrow⟩⟩ := exists_representingArrowFunctor G hGprorepresentable
  let e : restrictedCoyoneda B ≅ G.arrows := eArrow.symm
  obtain ⟨s, hs⟩ := (restrictedCoyonedaMap_bijective ξ.base B).2
    (natTransDown.{u, w, v₃, max v w} (e.hom ≫ G.source))
  obtain ⟨t, ht⟩ := (restrictedCoyonedaMap_bijective ξ.base B).2
    (natTransDown.{u, w, v₃, max v w} (e.hom ≫ G.target))
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  obtain ⟨σ, hσs, hσt⟩ :=
    exists_adicSection_presentationGroupoid.{u, v, w, u₃, v₃} p hp.predeformation.cofibered
      pushforwards a b
  exact formallyHomotopic_of_powerSeriesArrow s t
    (hasPowerSeriesCoordinates_of_presentation.{u, v, w, u₃, v₃} presentation hGsmooth e hs ht)
    _ a.base b.base
    (comp_representableSectionEquiv_symm e σ G.source s a.base hs hσs)
    (comp_representableSectionEquiv_symm e σ G.target t b.base ht hσt)

end

end Deformation
