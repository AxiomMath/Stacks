module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Etale.PushoutLiftSquareZero

/-!
# Lifting an approximation across a nilpotent ideal

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal and let `J ⊆ A` be a nilpotent ideal.
Write `A₀ = A ⧸ J` and, for a finite type `A`-algebra `C`, write `C₀ = C ⧸ JC`.  Given a finite
type `A₀`-algebra `B₀` sitting in a commutative diagram

```
C  --->  C₀  =  C ⧸ JC
          ^
          |
         B₀
          ^
          |
A  --->  A₀  =  A ⧸ J
```

such that `Spec C → Spec A` is étale over `Spec A \ V(I)`, such that `Spec B₀ → Spec A₀` is étale
over `Spec A₀ \ V(I A₀)`, and such that `B₀ → C₀` is étale and induces an isomorphism
`B₀ ⧸ I B₀ = C₀ ⧸ I C₀`, the diagram can be filled in: there is a finite type `A`-algebra `B`
with `B ⧸ JB = B₀`, with `B → C` étale, and with `Spec B → Spec A` étale over `Spec A \ V(I)`.

The commutativity of the diagram is expressed by scalar tower hypotheses, and "étale over
`Spec A \ V(I)`" pointwise: `Algebra.IsEtaleAt` at every prime `q` of `C` with `I ⊄ q ∩ A`.

## Main results

* `Stacks.Etale.bijective_quotientMap_of_comp_surjective`: if `π ∘ φ : R → Q` is surjective with
  kernel `J` and `ker π = J·S`, then `R ⧸ J → S ⧸ J·S` is bijective.
* `Stacks.Etale.bijective_algebraMap_of_formallyEtale_of_bijective_quotientMap`: a formally étale
  algebra which is an isomorphism modulo a nilpotent ideal of the base is an isomorphism.
* `Stacks.Etale.exists_finiteType_etale_lift_of_isNilpotent`: the diagram can be filled in when
  the ideal `I B₀` is nilpotent.
* `Stacks.Etale.exists_finiteType_etale_lift_of_eq_top`: the diagram can be filled in when
  `I B₀ = B₀`.
* `Stacks.Etale.bijective_quotientMap_of_thickening`: isomorphisms modulo `I` lift across a
  nilpotent thickening of an étale map.
* `Stacks.Etale.exists_etale_lift_of_sq_eq_bot`, `Stacks.Etale.exists_etale_lift_of_sq_eq_bot'`:
  the lift when `J ^ 2 = 0`, with étaleness away from `V(I)` stated on the localizations at
  elements of `I`.
* `Stacks.Etale.exists_etale_lift_of_pow_eq_bot`: the lift when `J ^ (n + 1) = 0`, with arbitrary
  models of the reductions.

## References

* [Stacks Project, Tag 0ALT](https://stacks.math.columbia.edu/tag/0ALT)
-/

@[expose] public section

universe u

namespace Stacks.Etale

/-- An ideal whose image in the quotient by a nilpotent ideal is the unit ideal is itself the
unit ideal. -/
private theorem eq_top_of_map_mk_eq_top {R : Type*} [CommRing R] {K X : Ideal R}
    (hK : IsNilpotent K) (h : X.map (Ideal.Quotient.mk K) = ⊤) : X = ⊤ := by
  obtain ⟨n, hn⟩ := hK
  have h1 : (1 : R) ∈ X ⊔ K := Ideal.mem_quotient_iff_mem_sup.mp (by rw [h]; trivial)
  obtain ⟨x, hx, k, hk, hxk⟩ := Submodule.mem_sup.mp h1
  have hknil : IsNilpotent k := ⟨n, by simpa [hn] using Ideal.pow_mem_pow hk n⟩
  exact Ideal.eq_top_of_isUnit_mem _ hx (eq_sub_of_add_eq hxk ▸ hknil.isUnit_one_sub)

/-- The extension of a nilpotent ideal along an algebra map is nilpotent. -/
private theorem isNilpotent_map_algebraMap {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {J : Ideal R} (hJ : IsNilpotent J) : IsNilpotent (J.map (algebraMap R S)) := by
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩

/-- If `A → Q` factors through `B` and `C` compatibly with `Q → B → C`, then `A → B → C` is a
scalar tower. -/
private theorem isScalarTower_of_isScalarTower_quotient (A Q B C : Type*) [CommRing A]
    [CommRing Q] [CommRing B] [CommRing C] [Algebra A Q] [Algebra A B] [Algebra A C] [Algebra Q B]
    [Algebra Q C] [Algebra B C] [IsScalarTower A Q B] [IsScalarTower A Q C]
    [IsScalarTower Q B C] : IsScalarTower A B C :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A Q C, IsScalarTower.algebraMap_apply A Q B,
      IsScalarTower.algebraMap_apply Q B C]

/-- A finitely presented algebra which is étale at every prime not containing `I`, and in which
`I` extends to the unit ideal, is étale. -/
private theorem etale_of_map_eq_top {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (I : Ideal R) (htop : I.map (algebraMap R S) = ⊤)
    (h : ∀ q : Ideal S, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap R S) →
      Algebra.IsEtaleAt R q) : Algebra.Etale R S := by
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  refine Set.eq_univ_of_forall fun q => h q.asIdeal q.isPrime fun hle => ?_
  have h1 := Ideal.map_le_iff_le_comap.mpr hle
  rw [htop, top_le_iff] at h1
  exact q.isPrime.ne_top h1

/-- Let `φ : R →+* S` and `π : S →+* Q`, and suppose the composite `π ∘ φ` is surjective with
kernel `J`, while the kernel of `π` is the ideal `J·S` generated by the image of `J`. Then
`R ⧸ J → S ⧸ J·S` is bijective. -/
theorem bijective_quotientMap_of_comp_surjective
    {R S Q : Type*} [CommRing R] [CommRing S] [CommRing Q]
    (φ : R →+* S) (π : S →+* Q) (hq : Function.Surjective (π.comp φ))
    (J : Ideal R) (hJ : RingHom.ker (π.comp φ) = J)
    (hK : RingHom.ker π = J.map φ) :
    Function.Bijective (Ideal.quotientMap (J.map φ) φ Ideal.le_comap_map) := by
  constructor
  · intro x y hxy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq] at hxy
    rwa [Ideal.Quotient.eq, ← hJ, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
      map_sub, ← RingHom.mem_ker, hK]
  · intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, hr⟩ := hq (π s)
    refine ⟨Ideal.Quotient.mk J r, ?_⟩
    rwa [Ideal.quotientMap_mk, Ideal.Quotient.eq, ← hK, RingHom.mem_ker, map_sub, sub_eq_zero]

/-- A formally étale algebra `S` over `R` which is an isomorphism modulo a nilpotent ideal
`a ⊆ R` is an isomorphism. -/
theorem bijective_algebraMap_of_formallyEtale_of_bijective_quotientMap
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyEtale R S]
    (a : Ideal R) (ha : IsNilpotent a)
    (h : Function.Bijective
      (Ideal.quotientMap (a.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    Function.Bijective (algebraMap R S) := by
  classical
  have hb : IsNilpotent (a.map (algebraMap R S)) := isNilpotent_map_algebraMap ha
  let φ : (R ⧸ a) ≃+* (S ⧸ a.map (algebraMap R S)) := RingEquiv.ofBijective _ h
  have hφ : ∀ r : R, φ (Ideal.Quotient.mk a r) =
      Ideal.Quotient.mk (a.map (algebraMap R S)) (algebraMap R S r) := fun r => by
    simp [φ, Ideal.quotientMap_mk]
  let g₀ : S →ₐ[R] R ⧸ a :=
    { (φ.symm : (S ⧸ a.map (algebraMap R S)) →+* (R ⧸ a)).comp
        (Ideal.Quotient.mk (a.map (algebraMap R S))) with
      commutes' := by
        intro r
        show φ.symm (Ideal.Quotient.mk (a.map (algebraMap R S)) (algebraMap R S r)) = _
        rw [← hφ r, φ.symm_apply_apply]
        rfl }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift (R := R) (A := S) a ha g₀
  have h1 : ∀ r : R, g (algebraMap R S r) = r := fun r => by simp
  have h2 : (Algebra.ofId R S).comp g = AlgHom.id R S := by
    refine Algebra.FormallyUnramified.ext (a.map (algebraMap R S)) hb fun s => ?_
    have e1 : Ideal.Quotient.mk a (g s) =
        φ.symm (Ideal.Quotient.mk (a.map (algebraMap R S)) s) := AlgHom.congr_fun hg s
    show Ideal.Quotient.mk (a.map (algebraMap R S)) (algebraMap R S (g s)) = _
    rw [← hφ (g s), e1, φ.apply_symm_apply]
    rfl
  exact ⟨Function.LeftInverse.injective h1, fun s => ⟨g s, AlgHom.congr_fun h2 s⟩⟩

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `J ⊆ A` a nilpotent ideal, and consider a
commutative diagram of finite type ring maps

```
C  --->  C ⧸ JC
          ^
         B₀
          ^
A  --->  A ⧸ J
```

such that `Spec C → Spec A` is étale over `Spec A \ V(I)`, such that `Spec B₀ → Spec (A ⧸ J)` is
étale over `Spec (A ⧸ J) \ V(I (A ⧸ J))`, and such that `B₀ → C ⧸ JC` is étale and induces an
isomorphism `B₀ ⧸ I B₀ = (C ⧸ JC) ⧸ I (C ⧸ JC)`.  Then the diagram can be filled in: there are a
finite type `A`-algebra `B`, an `A`-algebra map `B → C` which is étale, and an isomorphism
`B ⧸ JB ≅ B₀` compatible with the maps to `C ⧸ JC`, such that `Spec B → Spec A` is étale over
`Spec A \ V(I)`.

This takes the extra hypothesis `hnil` that `I B₀` is nilpotent, equivalently that the open set
`Spec B₀ \ V(I B₀)` is empty. -/
@[stacks 0ALT "extra hypothesis: the ideal I·B₀ is nilpotent, equivalently the open set \
Spec(B₀) minus V(I·B₀) along which the source glues is empty; the conclusion is delivered in \
full"]
theorem exists_finiteType_etale_lift_of_isNilpotent
    (A C B₀ : Type u) [CommRing A] [CommRing C] [CommRing B₀]
    [IsNoetherianRing A] [Algebra A C] [Algebra.FiniteType A C]
    (I J : Ideal A) (_hJ : IsNilpotent J)
    [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
    [Algebra.FiniteType (A ⧸ J) B₀]
    [Algebra (A ⧸ J) (C ⧸ J.map (algebraMap A C))]
    [IsScalarTower A (A ⧸ J) (C ⧸ J.map (algebraMap A C))]
    [Algebra B₀ (C ⧸ J.map (algebraMap A C))]
    [IsScalarTower (A ⧸ J) B₀ (C ⧸ J.map (algebraMap A C))]
    [Algebra.Etale B₀ (C ⧸ J.map (algebraMap A C))]
    (hC : ∀ q : Ideal C, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A C) →
      Algebra.IsEtaleAt A q)
    (_hB₀ : ∀ q : Ideal B₀, ∀ _ : q.IsPrime,
      ¬ I.map (Ideal.Quotient.mk J) ≤ q.comap (algebraMap (A ⧸ J) B₀) →
        Algebra.IsEtaleAt (A ⧸ J) q)
    (hmod : Function.Bijective (Ideal.quotientMap
      (((I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) B₀)).map
        (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (hnil : IsNilpotent ((I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) B₀))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B)
      (_ : Algebra B C) (_ : IsScalarTower A B C) (_ : Algebra.Etale B C)
      (e : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A] B₀),
      (∀ q : Ideal B, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A B) →
        Algebra.IsEtaleAt A q) ∧
      ∀ b : B, algebraMap B₀ (C ⧸ J.map (algebraMap A C))
            (e (Ideal.Quotient.mk (J.map (algebraMap A B)) b)) =
          Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap B C b) := by
  classical
  have htower : IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C)) :=
    isScalarTower_of_isScalarTower_quotient A (A ⧸ J) B₀ _
  have hbij : Function.Bijective (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) :=
    bijective_algebraMap_of_formallyEtale_of_bijective_quotientMap _ hnil hmod
  let φ : B₀ ≃+* (C ⧸ J.map (algebraMap A C)) := RingEquiv.ofBijective _ hbij
  have hφ : ∀ b : B₀, φ b = algebraMap B₀ (C ⧸ J.map (algebraMap A C)) b := fun _ => rfl
  let e : (C ⧸ J.map (algebraMap A C)) ≃ₐ[A] B₀ :=
    AlgEquiv.ofRingEquiv (f := φ.symm) fun a => by
      rw [RingEquiv.symm_apply_eq, hφ]
      exact IsScalarTower.algebraMap_apply A B₀ (C ⧸ J.map (algebraMap A C)) a
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, e, hC, fun b => ?_⟩
  show algebraMap B₀ (C ⧸ J.map (algebraMap A C)) (φ.symm _) = _
  rw [← hφ, φ.apply_symm_apply]
  rfl

/-- The data and the conclusion are those of `exists_finiteType_etale_lift_of_isNilpotent`, with
the extra hypothesis `htop` that `I B₀` is the unit ideal, equivalently that the closed set
`V(I B₀) ⊆ Spec B₀` is empty, in place of `hnil`. -/
@[stacks 0ALT "extra hypothesis: I·B₀ is the unit ideal of B₀, equivalently the closed set \
V(I·B₀) in Spec(B₀) along which the source glues is empty; the conclusion is delivered in full"]
theorem exists_finiteType_etale_lift_of_eq_top
    (A C B₀ : Type u) [CommRing A] [CommRing C] [CommRing B₀]
    [IsNoetherianRing A] [Algebra A C] [Algebra.FiniteType A C]
    (I J : Ideal A) (hJ : IsNilpotent J)
    [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
    [Algebra.FiniteType (A ⧸ J) B₀]
    [Algebra (A ⧸ J) (C ⧸ J.map (algebraMap A C))]
    [IsScalarTower A (A ⧸ J) (C ⧸ J.map (algebraMap A C))]
    [Algebra B₀ (C ⧸ J.map (algebraMap A C))]
    [IsScalarTower (A ⧸ J) B₀ (C ⧸ J.map (algebraMap A C))]
    [Algebra.Etale B₀ (C ⧸ J.map (algebraMap A C))]
    (hC : ∀ q : Ideal C, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A C) →
      Algebra.IsEtaleAt A q)
    (hB₀ : ∀ q : Ideal B₀, ∀ _ : q.IsPrime,
      ¬ I.map (Ideal.Quotient.mk J) ≤ q.comap (algebraMap (A ⧸ J) B₀) →
        Algebra.IsEtaleAt (A ⧸ J) q)
    (_hmod : Function.Bijective (Ideal.quotientMap
      (((I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) B₀)).map
        (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map))
    (htop : (I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) B₀) = ⊤) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B)
      (_ : Algebra B C) (_ : IsScalarTower A B C) (_ : Algebra.Etale B C)
      (e : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A] B₀),
      (∀ q : Ideal B, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A B) →
        Algebra.IsEtaleAt A q) ∧
      ∀ b : B, algebraMap B₀ (C ⧸ J.map (algebraMap A C))
            (e (Ideal.Quotient.mk (J.map (algebraMap A B)) b)) =
          Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap B C b) := by
  classical
  have hJC : IsNilpotent (J.map (algebraMap A C)) := isNilpotent_map_algebraMap hJ
  have htower : IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C)) :=
    isScalarTower_of_isScalarTower_quotient A (A ⧸ J) B₀ _
  have : Algebra.FinitePresentation (A ⧸ J) B₀ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hEtB₀ : Algebra.Etale (A ⧸ J) B₀ := etale_of_map_eq_top _ htop hB₀
  have htopC₀ : I.map (algebraMap A (C ⧸ J.map (algebraMap A C))) = ⊤ := by
    rw [IsScalarTower.algebraMap_eq A (A ⧸ J) (C ⧸ J.map (algebraMap A C)), ← Ideal.map_map,
      Ideal.Quotient.algebraMap_eq,
      IsScalarTower.algebraMap_eq (A ⧸ J) B₀ (C ⧸ J.map (algebraMap A C)), ← Ideal.map_map,
      htop, Ideal.map_top]
  have hICtop : I.map (algebraMap A C) = ⊤ := by
    refine eq_top_of_map_mk_eq_top hJC ?_
    rw [Ideal.map_map, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq A C (C ⧸ J.map (algebraMap A C))]
    exact htopC₀
  have : Algebra.FinitePresentation A C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hEtC : Algebra.Etale A C := etale_of_map_eq_top _ hICtop hC
  have hsurj : Function.Surjective (algebraMap A (A ⧸ J)) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  obtain ⟨B, _, _, hEtB, ψ, hψ, hker⟩ := etale_lift_along_surjection A (A ⧸ J) B₀ hsurj
  have := hEtB
  have hkerJ : RingHom.ker (ψ : B →+* B₀) = J.map (algebraMap A B) := by
    rw [hker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift (R := A) (A := B)
    (J.map (algebraMap A C)) hJC
    ((IsScalarTower.toAlgHom A B₀ (C ⧸ J.map (algebraMap A C))).comp ψ)
  let : Algebra B C := g.toRingHom.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  have : Algebra.Etale B C := Algebra.Etale.of_restrictScalars A B C
  let e : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A] B₀ :=
    (Ideal.quotientEquivAlgOfEq A hkerJ.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hψ)
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, e, ?_, ?_⟩
  · exact fun _ _ _ => inferInstance
  · exact fun b => (AlgHom.congr_fun hg b).symm

/-! ### Lifts across square-zero and nilpotent ideals -/

section General

variable {A : Type u} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
  {T T₀ S S₀ : Type u} [CommRing T] [CommRing T₀] [CommRing S] [CommRing S₀]
  [Algebra A T] [Algebra A T₀] [Algebra A S] [Algebra A S₀]
  [Algebra T S] [IsScalarTower A T S] [Algebra T₀ S₀] [IsScalarTower A T₀ S₀]

include hJ in
/-- Let `J` be a nilpotent ideal and `T → S` étale, reducing to `T₀ → S₀` along surjections with
kernels `JT` and `JS`. If `T₀ ⧸ I T₀ → S₀ ⧸ I S₀` is bijective, so is `T ⧸ I T → S ⧸ I S`. -/
theorem bijective_quotientMap_of_thickening [Algebra.Etale T S]
    (π : T →ₐ[A] T₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : T →+* T₀) = J.map (algebraMap A T))
    (πS : S →ₐ[A] S₀) (hπS : Function.Surjective πS)
    (hkerS : RingHom.ker (πS : S →+* S₀) = J.map (algebraMap A S))
    (hcomp : ∀ t, πS (algebraMap T S t) = algebraMap T₀ S₀ (π t)) (I : Ideal A)
    (hmod : Function.Bijective (Ideal.quotientMap
      ((I.map (algebraMap A T₀)).map (algebraMap T₀ S₀)) (algebraMap T₀ S₀) Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap
      ((I.map (algebraMap A T)).map (algebraMap T S)) (algebraMap T S) Ideal.le_comap_map) := by
  generalize hIT : I.map (algebraMap A T) = IT
  set IS := IT.map (algebraMap T S) with hIS'
  have hIS : IS = I.map (algebraMap A S) := by
    rw [hIS', ← hIT, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : Algebra.Etale (T ⧸ IT) (S ⧸ IS) :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S IT).symm
  have hIS₀ : (I.map (algebraMap A T₀)).map (algebraMap T₀ S₀) = I.map (algebraMap A S₀) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hnil : IsNilpotent (J.map (algebraMap A (T ⧸ IT))) := isNilpotent_map_algebraMap hJ
  have hJS : (J.map (algebraMap A (T ⧸ IT))).map (algebraMap (T ⧸ IT) (S ⧸ IS)) =
      (J.map (algebraMap A S)).map (Ideal.Quotient.mk IS) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext a
    show Ideal.Quotient.mk IS (algebraMap T S (algebraMap A T a)) =
      Ideal.Quotient.mk IS (algebraMap A S a)
    rw [IsScalarTower.algebraMap_apply A T S]
  have hJT :
      J.map (algebraMap A (T ⧸ IT)) = (J.map (algebraMap A T)).map (Ideal.Quotient.mk IT) := by
    rw [Ideal.map_map]
    rfl
  have hmemS : ∀ u : S, Ideal.Quotient.mk IS u ∈
      (J.map (algebraMap A (T ⧸ IT))).map (algebraMap (T ⧸ IT) (S ⧸ IS)) ↔
      u ∈ J.map (algebraMap A S) ⊔ IS := by
    intro u
    rw [hJS, Ideal.mem_quotient_iff_mem_sup]
  have hmemT : ∀ t : T, Ideal.Quotient.mk IT t ∈ J.map (algebraMap A (T ⧸ IT)) ↔
      t ∈ J.map (algebraMap A T) ⊔ IT := by
    intro t
    rw [hJT, Ideal.mem_quotient_iff_mem_sup]
  have hle : J.map (algebraMap A S) ⊔ IS ≤ (I.map (algebraMap A S₀)).comap πS := by
    refine sup_le ?_ ?_
    · rw [← hkerS]
      intro z hz
      have hz' : πS z = 0 := hz
      rw [Ideal.mem_comap, hz']
      exact zero_mem _
    · rw [hIS, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Ideal.mem_comap]
      rw [AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ ha
  have hITle : IT = I.map (algebraMap A T) := hIT.symm
  refine bijective_algebraMap_of_formallyEtale_of_bijective_quotientMap _ hnil ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x'
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, hmemT]
    change Ideal.Quotient.mk IS (algebraMap T S t) ∈ _ at hx
    have h1 := hle ((hmemS _).mp hx)
    rw [Ideal.mem_comap, hcomp, ← hIS₀] at h1
    have h3 : Ideal.Quotient.mk (I.map (algebraMap A T₀)) (π t) = 0 :=
      hmod.1 (by rwa [map_zero, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem])
    rw [Ideal.Quotient.eq_zero_iff_mem] at h3
    rw [hITle, sup_comm]
    exact SquareZero.mem_sup_of_map_mem J π hπ hker I h3
  · intro y
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y'
    obtain ⟨x₀, hx₀⟩ := hmod.2 (Ideal.Quotient.mk _ (πS u))
    obtain ⟨t₀, rfl⟩ := Ideal.Quotient.mk_surjective x₀
    obtain ⟨t, rfl⟩ := hπ t₀
    refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk IT t), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx₀
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    show Ideal.Quotient.mk IS (algebraMap T S t) - Ideal.Quotient.mk IS u ∈ _
    rw [← map_sub, hmemS]
    rw [← hcomp, ← map_sub, hIS₀] at hx₀
    rw [hIS, sup_comm]
    exact SquareZero.mem_sup_of_map_mem J πS hπS hkerS I hx₀

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `J ⊆ A` an ideal with `J ^ 2 = 0`. Let `C`
be a finite type `A`-algebra and `B₀` a finite type `A ⧸ J`-algebra with an étale map
`B₀ → C ⧸ JC` inducing a bijection modulo `I`, where `C` and `B₀` are étale over `A` and `A ⧸ J`
after inverting any element of `I`. Then there is a finite type `A`-algebra `B` with an étale map
`B → C` and a surjection `B → B₀` with kernel `JB` compatible with the maps to `C ⧸ JC`, such
that `B` is étale over `A` after inverting any element of `I` and `B → C` is bijective modulo
`I`. -/
theorem exists_etale_lift_of_sq_eq_bot
    (A C B₀ : Type u) [CommRing A] [CommRing C] [CommRing B₀]
    [IsNoetherianRing A] [Algebra A C] [Algebra.FiniteType A C]
    (I J : Ideal A) (hJ : J ^ 2 = ⊥)
    [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀] [Algebra.FiniteType A B₀]
    [Algebra B₀ (C ⧸ J.map (algebraMap A C))] [IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C))]
    [Algebra.Etale B₀ (C ⧸ J.map (algebraMap A C))]
    (hC : ∀ a ∈ I, Algebra.Etale A (Localization.Away (algebraMap A C a)))
    (hB₀ : ∀ a ∈ I, Algebra.Etale (A ⧸ J) (Localization.Away (algebraMap A B₀ a)))
    (hmod : Function.Bijective (Ideal.quotientMap
      ((I.map (algebraMap A B₀)).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B)
      (_ : Algebra B C) (_ : IsScalarTower A B C) (_ : Algebra.Etale B C) (πB : B →ₐ[A] B₀),
      Function.Surjective πB ∧ RingHom.ker (πB : B →+* B₀) = J.map (algebraMap A B) ∧
      (∀ b, algebraMap B₀ (C ⧸ J.map (algebraMap A C)) (πB b) =
        Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap B C b)) ∧
      (∀ a ∈ I, Algebra.Etale A (Localization.Away (algebraMap A B a))) ∧
      Function.Bijective (Ideal.quotientMap ((I.map (algebraMap A B)).map (algebraMap B C))
        (algebraMap B C) Ideal.le_comap_map) := by
  classical
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  have hfI : ∀ k, f k ∈ I := fun k ↦ hf ▸ Submodule.subset_span (Set.mem_range_self k)
  have hprod : ∀ s : Finset (Fin r), s.Nonempty → SquareZero.prodGen f s ∈ I := by
    rintro s ⟨k, hk⟩
    rw [SquareZero.prodGen, ← Finset.mul_prod_erase s f hk]
    exact Ideal.mul_mem_right _ _ (hfI k)
  have σ : SquareZero.Setup J f B₀ := ⟨hJ, fun s hs ↦ by
    have h := hB₀ _ (hprod s hs)
    rwa [IsScalarTower.algebraMap_apply A (A ⧸ J) B₀, Ideal.Quotient.algebraMap_eq] at h⟩
  have hflat : Module.Flat B₀ (C ⧸ J.map (algebraMap A C)) := inferInstance
  have hspan : Ideal.span (Set.range (SquareZero.genB J f B₀)) = I.map (algebraMap A B₀) := by
    rw [← hf]
    show Ideal.span _ = Ideal.map _ (Ideal.span _)
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    ext k
    simp [SquareZero.genB, IsScalarTower.algebraMap_apply A (A ⧸ J) B₀]
  have hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (SquareZero.genB J f B₀))).map
        (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map) := by
    rw [hspan]; exact hmod
  have hEtC : ∀ s : Finset (Fin r), s.Nonempty → Algebra.Etale A (SquareZero.locC f C s) :=
    fun s hs ↦ hC _ (hprod s hs)
  let B := SquareZero.glueRing C σ
  let : Algebra B C := (SquareZero.glueToC σ).toRingHom.toAlgebra
  have : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq fun a ↦ ((SquareZero.glueToC σ).commutes a).symm
  have : Algebra.Etale B C := SquareZero.etale_glueRing C σ hflat hq hEtC fun _ ↦ rfl
  let πB := SquareZero.glueReduction σ hflat hq
  have hπB : Function.Surjective πB := fun b ↦
    SquareZero.exists_lift_to_glueRing C σ hflat hq hEtC b
  have hker : RingHom.ker (πB : B →+* B₀) = J.map (algebraMap A B) :=
    SquareZero.ker_glueReduction C σ hflat hq hEtC
  have : Algebra.FiniteType A B := SquareZero.finiteType_of_thickening J hJ πB hπB hker
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hcomp : ∀ b, algebraMap B₀ (C ⧸ J.map (algebraMap A C)) (πB b) =
      Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap B C b) := fun b ↦
    SquareZero.algebraMap_glueReduction C σ hflat hq b
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, πB, hπB, hker, hcomp, fun a ha ↦ ?_, ?_⟩
  · refine (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := A)).mp fun q hqa ↦ ?_
    exact SquareZero.isEtaleAt_glueRing C σ hflat hq hEtC hf.ge q.asIdeal fun hle ↦ hqa (hle ha)
  · exact bijective_quotientMap_of_thickening J ⟨2, by rw [hJ, Ideal.zero_eq_bot]⟩ πB hπB hker
      (Ideal.Quotient.mkₐ A (J.map (algebraMap A C))) (Ideal.Quotient.mkₐ_surjective A _)
      (by rw [Ideal.Quotient.mkₐ_ker]) (fun b ↦ (hcomp b).symm) I hmod

/-- `exists_etale_lift_of_sq_eq_bot` with arbitrary models `A₀` of `A ⧸ J` and `C₀` of
`C ⧸ JC`. -/
theorem exists_etale_lift_of_sq_eq_bot'
    (A C B₀ A₀ C₀ : Type u) [CommRing A] [CommRing C] [CommRing B₀] [CommRing A₀] [CommRing C₀]
    [IsNoetherianRing A] [Algebra A C] [Algebra.FiniteType A C]
    (I J : Ideal A) (hJ : J ^ 2 = ⊥)
    [Algebra A A₀] (hA₀ : Function.Surjective (algebraMap A A₀))
    (hkerA₀ : RingHom.ker (algebraMap A A₀) = J)
    [Algebra A₀ B₀] [Algebra A B₀] [IsScalarTower A A₀ B₀] [Algebra.FiniteType A B₀]
    [Algebra A C₀] [Algebra B₀ C₀] [IsScalarTower A B₀ C₀] [Algebra.Etale B₀ C₀]
    (πC : C →ₐ[A] C₀) (hπC : Function.Surjective πC)
    (hkerC : RingHom.ker (πC : C →+* C₀) = J.map (algebraMap A C))
    (hC : ∀ a ∈ I, Algebra.Etale A (Localization.Away (algebraMap A C a)))
    (hB₀ : ∀ a ∈ I, Algebra.Etale A₀ (Localization.Away (algebraMap A B₀ a)))
    (hmod : Function.Bijective (Ideal.quotientMap ((I.map (algebraMap A B₀)).map (algebraMap B₀ C₀))
      (algebraMap B₀ C₀) Ideal.le_comap_map)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B)
      (_ : Algebra B C) (_ : IsScalarTower A B C) (_ : Algebra.Etale B C) (πB : B →ₐ[A] B₀),
      Function.Surjective πB ∧ RingHom.ker (πB : B →+* B₀) = J.map (algebraMap A B) ∧
      (∀ b, algebraMap B₀ C₀ (πB b) = πC (algebraMap B C b)) ∧
      (∀ a ∈ I, Algebra.Etale A (Localization.Away (algebraMap A B a))) ∧
      Function.Bijective (Ideal.quotientMap ((I.map (algebraMap A B)).map (algebraMap B C))
        (algebraMap B C) Ideal.le_comap_map) := by
  let eA : (A ⧸ J) ≃+* A₀ :=
    (Ideal.quotEquivOfEq hkerA₀.symm).trans (RingHom.quotientKerEquivOfSurjective hA₀)
  have heA : ∀ a, eA (Ideal.Quotient.mk J a) = algebraMap A A₀ a := fun a ↦ rfl
  let : Algebra (A ⧸ J) A₀ := (eA : A ⧸ J →+* A₀).toAlgebra
  let : Algebra (A ⧸ J) B₀ := ((algebraMap A₀ B₀).comp (algebraMap (A ⧸ J) A₀)).toAlgebra
  have : IsScalarTower (A ⧸ J) A₀ B₀ := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (A ⧸ J) B₀ := .of_algebraMap_eq fun a ↦ by
    show algebraMap A B₀ a = algebraMap A₀ B₀ (eA (Ideal.Quotient.mk J a))
    rw [heA, ← IsScalarTower.algebraMap_apply]
  have : Algebra.Etale (A ⧸ J) A₀ := .of_equiv (AlgEquiv.ofRingEquiv (f := eA) fun _ ↦ rfl)
  have hB₀' : ∀ a ∈ I, Algebra.Etale (A ⧸ J) (Localization.Away (algebraMap A B₀ a)) := by
    intro a ha
    have := hB₀ a ha
    have : IsScalarTower (A ⧸ J) A₀ (Localization.Away (algebraMap A B₀ a)) :=
      .of_algebraMap_eq fun x ↦ by
        rw [IsScalarTower.algebraMap_apply (A ⧸ J) B₀ (Localization.Away (algebraMap A B₀ a)),
          IsScalarTower.algebraMap_apply A₀ B₀ (Localization.Away (algebraMap A B₀ a))]
        rfl
    exact .comp (A ⧸ J) A₀ _
  let eC : (C ⧸ J.map (algebraMap A C)) ≃ₐ[A] C₀ :=
    (Ideal.quotientEquivAlgOfEq A hkerC.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπC)
  have heC : ∀ c, eC (Ideal.Quotient.mk _ c) = πC c := fun c ↦ rfl
  let : Algebra B₀ (C ⧸ J.map (algebraMap A C)) :=
    ((eC.symm : C₀ →+* C ⧸ J.map (algebraMap A C)).comp (algebraMap B₀ C₀)).toAlgebra
  have hB₀C : ∀ b, algebraMap B₀ (C ⧸ J.map (algebraMap A C)) b = eC.symm (algebraMap B₀ C₀ b) :=
    fun _ ↦ rfl
  have : IsScalarTower A B₀ (C ⧸ J.map (algebraMap A C)) := .of_algebraMap_eq fun a ↦ by
    rw [hB₀C, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  let eC' : C₀ ≃ₐ[B₀] (C ⧸ J.map (algebraMap A C)) :=
    AlgEquiv.ofRingEquiv (f := eC.symm.toRingEquiv) fun _ ↦ rfl
  have : Algebra.Etale B₀ (C ⧸ J.map (algebraMap A C)) := .of_equiv eC'
  have hmod' : Function.Bijective (Ideal.quotientMap
      ((I.map (algebraMap A B₀)).map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map) := by
    set IB := I.map (algebraMap A B₀)
    have hIC : (IB.map (algebraMap B₀ C₀)).map (eC'.toRingEquiv : C₀ →+* _) =
        IB.map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) := by
      rw [Ideal.map_map]
      rfl
    let Φ := Ideal.quotientEquiv (IB.map (algebraMap B₀ C₀))
      (IB.map (algebraMap B₀ (C ⧸ J.map (algebraMap A C)))) eC'.toRingEquiv hIC.symm
    have hΦ : ⇑(Ideal.quotientMap (IB.map (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
        (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map) =
        Φ ∘ ⇑(Ideal.quotientMap (IB.map (algebraMap B₀ C₀)) (algebraMap B₀ C₀)
          Ideal.le_comap_map) := by
      funext x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    rw [hΦ]
    exact Φ.bijective.comp hmod
  obtain ⟨B, _, _, _, _, _, _, πB, hπB, hker, hcomp, hEt, hmodB⟩ :=
    exists_etale_lift_of_sq_eq_bot A C B₀ I J hJ hC hB₀' hmod'
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, πB, hπB, hker, fun b ↦ ?_, hEt, hmodB⟩
  have h := congrArg eC (hcomp b)
  rwa [hB₀C, AlgEquiv.apply_symm_apply, heC] at h

/-- `exists_etale_lift_of_sq_eq_bot'` for an ideal `J` with `J ^ (n + 1) = 0` in place of
`J ^ 2 = 0`. -/
theorem exists_etale_lift_of_pow_eq_bot (n : ℕ)
    (A C B₀ A₀ C₀ : Type u) [CommRing A] [CommRing C] [CommRing B₀] [CommRing A₀] [CommRing C₀]
    [IsNoetherianRing A] [Algebra A C] [Algebra.FiniteType A C]
    (I J : Ideal A) (hJ : J ^ (n + 1) = ⊥)
    [Algebra A A₀] (hA₀ : Function.Surjective (algebraMap A A₀))
    (hkerA₀ : RingHom.ker (algebraMap A A₀) = J)
    [Algebra A₀ B₀] [Algebra A B₀] [IsScalarTower A A₀ B₀] [Algebra.FiniteType A B₀]
    [Algebra A C₀] [Algebra B₀ C₀] [IsScalarTower A B₀ C₀] [Algebra.Etale B₀ C₀]
    (πC : C →ₐ[A] C₀) (hπC : Function.Surjective πC)
    (hkerC : RingHom.ker (πC : C →+* C₀) = J.map (algebraMap A C))
    (hC : ∀ a ∈ I, Algebra.Etale A (Localization.Away (algebraMap A C a)))
    (hB₀ : ∀ a ∈ I, Algebra.Etale A₀ (Localization.Away (algebraMap A B₀ a)))
    (hmod : Function.Bijective (Ideal.quotientMap ((I.map (algebraMap A B₀)).map (algebraMap B₀ C₀))
      (algebraMap B₀ C₀) Ideal.le_comap_map)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B)
      (_ : Algebra B C) (_ : IsScalarTower A B C) (_ : Algebra.Etale B C) (πB : B →ₐ[A] B₀),
      Function.Surjective πB ∧ RingHom.ker (πB : B →+* B₀) = J.map (algebraMap A B) ∧
      (∀ b, algebraMap B₀ C₀ (πB b) = πC (algebraMap B C b)) ∧
      (∀ a ∈ I, Algebra.Etale A (Localization.Away (algebraMap A B a))) ∧
      Function.Bijective (Ideal.quotientMap ((I.map (algebraMap A B)).map (algebraMap B C))
        (algebraMap B C) Ideal.le_comap_map) := by
  induction n generalizing A C B₀ A₀ C₀ with
  | zero =>
    have hJ2 : J ^ 2 = ⊥ := by
      rw [zero_add, pow_one] at hJ
      rw [hJ, pow_two, Ideal.bot_mul]
    exact exists_etale_lift_of_sq_eq_bot' A C B₀ A₀ C₀ I J hJ2 hA₀ hkerA₀ πC hπC hkerC hC hB₀ hmod
  | succ n ih =>
    classical
    set K := J ^ (n + 1) with hK
    have hKJ : K ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero n)
    have hK2 : K ^ 2 = ⊥ := by
      rw [hK, ← pow_mul, eq_bot_iff, ← hJ]
      exact Ideal.pow_le_pow_right (by omega)
    let A' := A ⧸ K
    let J' : Ideal A' := J.map (Ideal.Quotient.mk K)
    let I' : Ideal A' := I.map (Ideal.Quotient.mk K)
    have hJ' : J' ^ (n + 1) = ⊥ := by
      show (J.map (Ideal.Quotient.mk K)) ^ (n + 1) = ⊥
      rw [← Ideal.map_pow, ← hK, Ideal.map_quotient_self]
    let C' := C ⧸ K.map (algebraMap A C)
    have : Algebra.FiniteType A C' :=
      .of_surjective (Ideal.Quotient.mkₐ A _) (Ideal.Quotient.mkₐ_surjective A _)
    have : Algebra.FiniteType A' C' := .of_restrictScalars_finiteType A A' C'
    have hKA₀ : K ≤ RingHom.ker (algebraMap A A₀) := by rw [hkerA₀]; exact hKJ
    let : Algebra A' A₀ := (Ideal.Quotient.lift K (algebraMap A A₀) hKA₀).toAlgebra
    have : IsScalarTower A A' A₀ := .of_algebraMap_eq fun _ ↦ rfl
    have hA'₀ : Function.Surjective (algebraMap A' A₀) :=
      Ideal.Quotient.lift_surjective_of_surjective _ _ hA₀
    have hkerA'₀ : RingHom.ker (algebraMap A' A₀) = J' := by
      show RingHom.ker (Ideal.Quotient.lift K (algebraMap A A₀) hKA₀) = _
      rw [Ideal.ker_quotient_lift, hkerA₀]
    let : Algebra A' B₀ := ((algebraMap A₀ B₀).comp (algebraMap A' A₀)).toAlgebra
    have : IsScalarTower A' A₀ B₀ := .of_algebraMap_eq fun _ ↦ rfl
    have hA'B₀ : ∀ a, algebraMap A' B₀ (Ideal.Quotient.mk K a) = algebraMap A B₀ a := fun a ↦ by
      show algebraMap A₀ B₀ (algebraMap A A₀ a) = _
      rw [← IsScalarTower.algebraMap_apply]
    have : IsScalarTower A A' B₀ := .of_algebraMap_eq fun a ↦ (hA'B₀ a).symm
    have : Algebra.FiniteType A' B₀ := .of_restrictScalars_finiteType A A' B₀
    let : Algebra A' C₀ := ((algebraMap B₀ C₀).comp (algebraMap A' B₀)).toAlgebra
    have : IsScalarTower A' B₀ C₀ := .of_algebraMap_eq fun _ ↦ rfl
    have hKC : K.map (algebraMap A C) ≤ RingHom.ker (πC : C →+* C₀) := by
      rw [hkerC]; exact Ideal.map_mono hKJ
    let πC'₀ : C' →+* C₀ := Ideal.Quotient.lift _ (πC : C →+* C₀) hKC
    let πC' : C' →ₐ[A'] C₀ :=
      { πC'₀ with
        commutes' := fun a ↦ by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
          show πC (algebraMap A C a) = algebraMap B₀ C₀ (algebraMap A' B₀ (Ideal.Quotient.mk K a))
          rw [AlgHom.commutes, hA'B₀, ← IsScalarTower.algebraMap_apply] }
    have hπC' : Function.Surjective πC' :=
      Ideal.Quotient.lift_surjective_of_surjective _ _ hπC
    have hkerC' : RingHom.ker (πC' : C' →+* C₀) = J'.map (algebraMap A' C') := by
      show RingHom.ker πC'₀ = _
      rw [Ideal.ker_quotient_lift, hkerC, Ideal.map_map, Ideal.map_map]
      rfl
    have hC' : ∀ a ∈ I', Algebra.Etale A' (Localization.Away (algebraMap A' C' a)) := by
      intro a ha
      obtain ⟨a₀, ha₀, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ha
      have := hC a₀ ha₀
      exact SquareZero.etale_localizationAway_quotient K (algebraMap A C a₀)
    have hB₀' : ∀ a ∈ I', Algebra.Etale A₀ (Localization.Away (algebraMap A' B₀ a)) := by
      intro a ha
      obtain ⟨a₀, ha₀, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp ha
      rw [hA'B₀]
      exact hB₀ a₀ ha₀
    have hIB : I'.map (algebraMap A' B₀) = I.map (algebraMap A B₀) := by
      show (I.map (Ideal.Quotient.mk K)).map _ = _
      rw [Ideal.map_map]
      congr 1
      ext a
      exact hA'B₀ a
    have hmod' : Function.Bijective (Ideal.quotientMap
        ((I'.map (algebraMap A' B₀)).map (algebraMap B₀ C₀)) (algebraMap B₀ C₀)
          Ideal.le_comap_map) := by
      rw [hIB]; exact hmod
    obtain ⟨B', _, _, _, _, _, _, πB', hπB', hkerB', hcompB', hEtB', hmodB'⟩ :=
      ih A' C' B₀ A₀ C₀ I' J' hJ' hA'₀ hkerA'₀ πC' hπC' hkerC' hC' hB₀' hmod'
    let : Algebra A B' := ((algebraMap A' B').comp (algebraMap A A')).toAlgebra
    have : IsScalarTower A A' B' := .of_algebraMap_eq fun _ ↦ rfl
    have : Algebra.FiniteType A A' :=
      .of_surjective (Ideal.Quotient.mkₐ A K) (Ideal.Quotient.mkₐ_surjective A K)
    have : Algebra.FiniteType A B' := .trans (S := A') inferInstance inferInstance
    have : IsScalarTower A B' C' := .of_algebraMap_eq fun a ↦ by
      rw [IsScalarTower.algebraMap_apply A A' C', IsScalarTower.algebraMap_apply A' B' C']
      rfl
    have hA'surj : Function.Surjective (algebraMap A A') := by
      rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective
    have hkerA' : RingHom.ker (algebraMap A A') = K := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    have hB'I : ∀ a ∈ I, Algebra.Etale A' (Localization.Away (algebraMap A B' a)) := fun a ha ↦
      hEtB' _ (Ideal.mem_map_of_mem _ ha)
    have hIB' : I'.map (algebraMap A' B') = I.map (algebraMap A B') := by
      show (I.map (Ideal.Quotient.mk K)).map _ = _
      rw [Ideal.map_map, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    have hmodB'' : Function.Bijective (Ideal.quotientMap
        ((I.map (algebraMap A B')).map (algebraMap B' C')) (algebraMap B' C')
          Ideal.le_comap_map) := by
      rw [← hIB']; exact hmodB'
    obtain ⟨B, _, _, _, _, _, _, πB, hπB, hkerB, hcompB, hEtB, hmodB⟩ :=
      exists_etale_lift_of_sq_eq_bot' A C B' A' C' I K hK2 hA'surj hkerA'
        (Ideal.Quotient.mkₐ A _) (Ideal.Quotient.mkₐ_surjective A _)
        (by rw [Ideal.Quotient.mkₐ_ker]) hC hB'I hmodB''
    refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, (πB'.restrictScalars A).comp πB, hπB'.comp hπB, ?_, fun b ↦ ?_, hEtB, hmodB⟩
    · have h1 : RingHom.ker (πB'.restrictScalars A : B' →+* B₀) = J.map (algebraMap A B') := by
        show RingHom.ker (πB' : B' →+* B₀) = _
        rw [hkerB', Ideal.map_map, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
      have h2 : J.map (algebraMap A B') = (J.map (algebraMap A B)).map (πB : B →+* B') := by
        rw [Ideal.map_map]
        congr 1
        ext a
        exact (πB.commutes a).symm
      show RingHom.ker ((πB'.restrictScalars A : B' →+* B₀).comp (πB : B →+* B')) = _
      rw [← RingHom.comap_ker, h1, h2, Ideal.comap_map_of_surjective (πB : B →+* B') hπB,
        ← RingHom.ker_eq_comap_bot, hkerB]
      exact sup_eq_left.mpr (Ideal.map_mono hKJ)
    · show algebraMap B₀ C₀ (πB' (πB b)) = πC (algebraMap B C b)
      rw [hcompB', hcompB]
      rfl

end General

end Stacks.Etale

end
