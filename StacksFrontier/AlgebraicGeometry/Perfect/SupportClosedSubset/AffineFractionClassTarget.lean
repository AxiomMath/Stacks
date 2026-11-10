module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AffineFractionClassComparison

/-!
# The target comparison of the affine description of the fraction class map

Let `A` be a commutative ring, let `f₁, …, f_c ∈ A` be a finite nonempty family and let `M` be an
`A`-module.  `StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AffineFractionClass\
StacksFrontier/AlgebraicGeometry/Perfect/PerfectApproximation/Comparison.lean` reduces clause 3 of
Tag 0G7R to the existence of a **target comparison**: an
`A`-linear map

`M_{f₁⋯f_c}/im(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c}) ⟶ Γ(Spec A, Coker(lastDif))`

carrying the class of the fraction `s/(f₁⋯f_c)` to the class of the sheaf-theoretic fraction.
This file builds that map, which is `affineTargetComparison_exists` below.

## Main definitions

* `Stacks.Perfect.AffineFractionClass.awayLift`: for a set `s` of indices and an open `V` on
  which `∏_{j ∈ s} f j` is invertible, the canonical map `M_{∏_{j ∈ s} f j} ⟶ Γ(V, M~)`.  This is
  Mathlib's localization instance `AlgebraicGeometry.tilde.toOpen` read through
  `LocalizedModule.lift`.
* `Stacks.Perfect.AffineFractionClass.atIndexL`: a section of `M~` over one principal-open
  intersection, viewed as the cochain supported in that component.
* `Stacks.Perfect.AffineFractionClass.topTransfer`: the resulting map from the top Čech term
  `⨁_{#t = c} M_{∏_{i ∈ t} f i}` to `Γ(Spec A, ℱ_{1…c})`.
* `Stacks.Perfect.AffineFractionClass.targetComparison`: **the target comparison**, the map
  `topTransfer` induces on the cokernel of the last algebraic Čech differential.

## Main results

* `Stacks.Perfect.AffineFractionClass.exists_lastDif_preimage`: the image under `topTransfer` of
  a fraction whose denominator omits an index is a boundary for the last differential of the
  sheaf-level extended alternating Čech complex, already on global sections.  This is what makes
  `topTransfer` descend to the cokernel.
* `Stacks.Perfect.AffineFractionClass.targetComparison_mk`: the target comparison carries the
  class of `s/(f₁⋯f_c)` to the class of the sheaf-theoretic fraction.
* `Stacks.Perfect.AffineFractionClass.affineTargetComparison_exists`: **the target comparison
  exists**, i.e. the hypothesis `τ` of
  `Stacks.Perfect.AffineFractionClass.supportedFraction_eq_of_targetComparison` is satisfiable.
* `Stacks.Perfect.AffineFractionClass.supportedFraction_eq_targetComparison`: consequently, the
  global sections of Tag 0G7Q's map, read through the source comparison and through the target
  comparison, are `Cech.supportedFraction` — clause 3 of Tag 0G7R except that the target
  comparison is not shown *here* to be an isomorphism.  The source one is
  `Stacks.Perfect.AffineFractionClass.bijective_affineSourceComparison`; the target one is
  `Stacks.Perfect.AffineFractionClass.bijective_targetComparison`.

## Implementation notes

The open on which everything happens is `W = ⋂ᵢ D(fᵢ)`, written as the principal-open intersection
`CechCochains.inter (fun i => ⊤ ⊓ (Spec A).basicOpen (specFun f i)) (topIndex d).1` belonging to
the unique full tuple.  It is never identified with `PrimeSpectrum.basicOpen (∏ i, f i)`: all that
is needed is the inequality `W ≤ PrimeSpectrum.basicOpen (f i)` for each `i`, which gives
`W ≤ PrimeSpectrum.basicOpen (∏_{j ∈ s} f j)` for *every* `s`, hence invertibility of every
denominator occurring in the complex, by
`AlgebraicGeometry.Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen`.  The maps out of the
localizations are then `LocalizedModule.lift`s of `AlgebraicGeometry.tilde.toOpen`, and they are
compared with one another by the uniqueness of such lifts, so no fraction is ever manipulated.

Čech indices are kept abstract: a subtype element `t : {s : Finset (Fin c) // s.card = c}` is
never replaced by `⟨Finset.univ, _⟩` inside a type, because the crossing between
`(⟨Finset.univ, h⟩ : _).1` and `Finset.univ` under `Cech.cechMod` is extremely expensive.  The one
place where the index must be concrete, `targetComparison_mk`, goes through
`topTransfer_lof_of_card`, which takes the underlying `Finset` and its cardinality as separate
arguments.

Two spellings of the same type occur throughout, `Γ(F, V)` and
`(modulesSpecToSheaf.obj F).presheaf.obj (.op V)`; they are definitionally equal but `rw` rejects
the crossing.  Hence `resL` and `toOpenL`, which are the restriction maps and
`AlgebraicGeometry.tilde.toOpen` stated at the `Γ` spelling, and hence the use of `Eq.trans` and
`exact` rather than `rw` wherever the boundary is crossed.

**What is proved elsewhere.**  Bijectivity of the target comparison, i.e.

```lean
Function.Bijective (targetComparison f M)
```

is right exactness of `Γ(Spec A, -)` on these modules; it is proved in
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AffineFractionClassBijective.lean`,
as `Stacks.Perfect.AffineFractionClass.bijective_targetComparison`, from quasi-coherence of the
Čech terms and the exactness of `M ↦ M~`.  What is established *here* is the normalisation on
fractions, which is what
`Stacks.Perfect.AffineFractionClass.supportedFraction_eq_of_targetComparison` consumes.

No Stacks tag attribute for Tag 0G7R is placed in this file: as in
`AffineFractionClassComparison.lean`, what is below is a step of the proof of clause 3, not the
clause itself.  The clause is
`Stacks.Perfect.AffineFractionClass.supportedFraction_eq_conj`, in
`AffineFractionClassBijective.lean`.

## References

* [Stacks Project, Tag 0G7R](https://stacks.math.columbia.edu/tag/0G7R)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Perfect.SupportedFraction Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AffineFractionClass

variable {R : CommRingCat.{u}} {d : ℕ}


/-- restriction as an `R`-linear map -/
public def resL (F : (Spec R).Modules) {V V' : (Spec R).Opens} (h : V' ≤ V) :
    Γ(F, V) →ₗ[R] Γ(F, V') :=
  ((modulesSpecToSheaf.obj F).presheaf.map (homOfLE h).op).hom

/-- `resL` is the restriction map of the presheaf. -/
public theorem resL_apply (F : (Spec R).Modules) {V V' : (Spec R).Opens} (h : V' ≤ V)
    (x : Γ(F, V)) : resL F h x = F.presheaf.map (homOfLE h).op x := rfl

/-- `tilde.toOpen`, stated at the `Γ` spelling of its target -/
public def toOpenL (M : ModuleCat.{u} R) (V : (Spec R).Opens) : (M : Type u) →ₗ[R] Γ(tilde M, V) :=
  (tilde.toOpen M V).hom

/-- An open on which every member of a finite family of ring elements is invertible lies in the
principal open of their product. -/
public theorem le_basicOpen_prod {V : (Spec R).Opens} (f : Fin (d + 1) → R)
    (s : Finset (Fin (d + 1))) (h : ∀ j ∈ s, V ≤ PrimeSpectrum.basicOpen (f j)) :
    V ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, PrimeSpectrum.basicOpen_one]; exact le_top
  | cons a s ha ih =>
      rw [Finset.prod_cons, PrimeSpectrum.basicOpen_mul]
      exact le_inf (h a (by simp)) (ih fun j hj => h j (by simp [hj]))

/-- Every power of `∏_{j ∈ s} f j` acts invertibly on the sections of `M~` over an open contained
in the principal open of that product. -/
public theorem awayUnit (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : Finset (Fin (d + 1)))
    {V : (Spec R).Opens} (hV : V ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j))
    (x : Cech.cechSub f s) :
    IsUnit ((algebraMap R (Module.End R Γ(tilde M, V))) (x : R)) := by
  obtain ⟨_, n, rfl⟩ := x
  simpa only [map_pow] using
    (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := tilde M) _ hV).pow n

/-- the comparison map out of a localized module -/
public def awayLift (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : Finset (Fin (d + 1)))
    {V : (Spec R).Opens} (hV : V ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j)) :
    Cech.cechMod f (M : Type u) s →ₗ[R] Γ(tilde M, V) :=
  LocalizedModule.lift _ (toOpenL M V) (awayUnit f M s hV)

/-- `awayLift` extends the canonical map `M ⟶ Γ(V, M~)`. -/
public theorem awayLift_mk (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : Finset (Fin (d + 1)))
    {V : (Spec R).Opens} (hV : V ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j)) (m : M) :
    awayLift f M s hV (LocalizedModule.mkLinearMap (Cech.cechSub f s) (M : Type u) m) =
      toOpenL M V m :=
  LinearMap.congr_fun (LocalizedModule.lift_comp _ _ (awayUnit f M s hV)) m


/-- `awayLift` is the only `R`-linear extension of the canonical map `M ⟶ Γ(V, M~)`. -/
public theorem awayLift_unique (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin (d + 1))) {V : (Spec R).Opens}
    (hV : V ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j))
    (g : Cech.cechMod f (M : Type u) s →ₗ[R] Γ(tilde M, V))
    (hg : ∀ m : M, g (LocalizedModule.mkLinearMap (Cech.cechSub f s) (M : Type u) m) =
      toOpenL M V m) :
    awayLift f M s hV = g :=
  LocalizedModule.lift_unique _ _ (awayUnit f M s hV) g (LinearMap.ext hg)

/-- The canonical maps from `M` to the sections of `M~` are compatible with restriction. -/
public theorem resL_toOpen (M : ModuleCat.{u} R) {V V' : (Spec R).Opens} (h : V' ≤ V) (m : M) :
    resL (tilde M) h (toOpenL M V m) = toOpenL M V' m := rfl

/-- Restricting the value of `awayLift` to a smaller open is the value of `awayLift` there. -/
public theorem resL_awayLift (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin (d + 1))) {V V' : (Spec R).Opens}
    (hV : V ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j))
    (hV' : V' ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j)) (h : V' ≤ V)
    (x : Cech.cechMod f (M : Type u) s) :
    resL (tilde M) h (awayLift f M s hV x) = awayLift f M s hV' x :=
  LinearMap.congr_fun
    (awayLift_unique f M s hV' ((resL (tilde M) h).comp (awayLift f M s hV))
      (fun m => by rw [LinearMap.comp_apply, awayLift_mk, resL_toOpen])).symm x

/-- Enlarging the set of inverted equations before applying `awayLift` changes nothing: both maps
extend the same map out of `M`. -/
public theorem awayLift_cechι (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    {s t : Finset (Fin (d + 1))} (hst : s ⊆ t) {V : (Spec R).Opens}
    (hs : V ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j))
    (ht : V ≤ PrimeSpectrum.basicOpen (∏ j ∈ t, f j))
    (x : Cech.cechMod f (M : Type u) s) :
    awayLift f M t ht (Cech.cechι f (M : Type u) hst x) = awayLift f M s hs x :=
  LinearMap.congr_fun
    (awayLift_unique f M s hs ((awayLift f M t ht).comp (Cech.cechι f (M : Type u) hst))
      (fun m => by
        rw [LinearMap.comp_apply, Cech.cechι_mk, awayLift_mk])).symm x


/-- A principal-open intersection is contained in the principal open of each equation it
inverts. -/
public theorem inter_le_basicOpen (f : Fin (d + 1) → R) {p : ℕ}
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) (i : Fin (d + 1)) (k : Fin (p + 1))
    (hk : q.1 k = i) :
    CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1 ≤
      PrimeSpectrum.basicOpen (f i) := by
  have h1 : CechCochains.inter
      (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1 ≤
      (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f (q.1 k)) := iInf_le _ k
  rw [hk] at h1
  refine h1.trans (inf_le_right.trans (le_of_eq ?_))
  exact AlgebraicGeometry.basicOpen_eq_of_affine (f i)

/-- A principal-open intersection is contained in the principal open of any product of equations
it inverts. -/
public theorem inter_le_basicOpen_prod (f : Fin (d + 1) → R) {p : ℕ}
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) (s : Finset (Fin (d + 1)))
    (hs : ∀ j ∈ s, ∃ k, q.1 k = j) :
    CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1 ≤
      PrimeSpectrum.basicOpen (∏ j ∈ s, f j) :=
  le_basicOpen_prod f s fun j hj => by
    obtain ⟨k, hk⟩ := hs j hj
    exact inter_le_basicOpen f q j k hk

/-- The intersection of all the principal opens inverts every product of equations. -/
public theorem interTop_le (f : Fin (d + 1) → R) (s : Finset (Fin (d + 1))) :
    CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) (topIndex d).1 ≤
      PrimeSpectrum.basicOpen (∏ j ∈ s, f j) :=
  inter_le_basicOpen_prod f (topIndex d) s fun j _ => ⟨j, rfl⟩

/-- The principal-open intersection of the tuple omitting `i` inverts the product of all the
equations except `f i`. -/
public theorem interFace_le {e : ℕ} (f : Fin (e + 2) → R) (i : Fin (e + 2)) :
    CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
          (faceIndex e i).1 ≤
      PrimeSpectrum.basicOpen (∏ j ∈ Finset.univ.erase i, f j) :=
  inter_le_basicOpen_prod f (faceIndex e i) _ fun _ hj =>
    Fin.exists_succAbove_eq (Finset.ne_of_mem_erase hj)


/-- Equal index tuples have equal principal-open intersections. -/
public theorem interEqLe (f : Fin (d + 1) → R) {p : ℕ}
    (q q₀ : CechCochains.OrdIndex (I := Fin (d + 1)) p) (h : q = q₀) :
    CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1 ≤
      CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q₀.1 :=
  le_of_eq (by rw [h])

/-- The sectionwise identification of a positive-degree term with the ordered Čech cochains is
`R`-linear componentwise. -/
public theorem secIso_smulR (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ)
    (r : R) (x : Γ(prodTerm (specFun f) (tilde M) p, ⊤))
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    secIso (specFun f) (tilde M) p ⊤ (r • x) q =
      r • secIso (specFun f) (tilde M) p ⊤ x q := by
  have key : ∀ {F : (Spec R).Modules} {W : (Spec R).Opens} (y : Γ(F, W)) (h : W ≤ ⊤),
      r • y = (Spec R).presheaf.map (homOfLE h).op ((Scheme.ΓSpecIso R).inv r) • y := by
    intro F W y h
    rw [Scheme.Modules.smul_Spec_def]
    congr 2
  rw [key x le_top, secIso_smul, key (secIso (specFun f) (tilde M) p ⊤ x q) le_top,
    ringMap_collapse (homOfLE (show (⊤ : (Spec R).Opens) ≤ ⊤ from le_top))
      (homOfLE (interLe (specFun f) p q ⊤))
      (homOfLE (show CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q.1 ≤ ⊤
          from le_top))]


/-- The component of the section belonging to an ordered Čech cochain is that cochain's
component. -/
public theorem secIso_symm_apply (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ)
    (cc : CechCochains.OrdCochain
      (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
      (Scheme.Modules.presheaf (tilde M)) p)
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    secIso (specFun f) (tilde M) p ⊤ ((secIso (specFun f) (tilde M) p ⊤).symm cc) q = cc q :=
  congrFun ((secIso (specFun f) (tilde M) p ⊤).apply_symm_apply cc) q

/-- the cochain whose only nonzero component is the given section -/
public def atIndexCochain (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ)
    (q₀ : CechCochains.OrdIndex (I := Fin (d + 1)) p)
    (y : Γ(tilde M, CechCochains.inter
      (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q₀.1)) :
    CechCochains.OrdCochain (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
      (Scheme.Modules.presheaf (tilde M)) p :=
  fun q => if h : q = q₀ then resL (tilde M) (interEqLe f q q₀ h) y else 0

/-- The components of `atIndexCochain`. -/
public theorem atIndexCochain_apply (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ)
    (q₀ : CechCochains.OrdIndex (I := Fin (d + 1)) p)
    (y : Γ(tilde M, CechCochains.inter
      (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q₀.1))
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    atIndexCochain f M p q₀ y q =
      if h : q = q₀ then resL (tilde M) (interEqLe f q q₀ h) y else 0 := rfl

/-- a section over one principal intersection, put in that component -/
public def atIndexL (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ)
    (q₀ : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    Γ(tilde M, CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q₀.1) →ₗ[R]
      Γ(prodTerm (specFun f) (tilde M) p, ⊤) where
  toFun y := (secIso (specFun f) (tilde M) p ⊤).symm (atIndexCochain f M p q₀ y)
  map_add' y z := by
    refine (secIso (specFun f) (tilde M) p ⊤).injective (funext fun q => ?_)
    rw [map_add, CechCochains.OrdCochain.add_apply, secIso_symm_apply, secIso_symm_apply,
      secIso_symm_apply, atIndexCochain_apply, atIndexCochain_apply, atIndexCochain_apply]
    by_cases hq : q = q₀
    · simp only [dite_eq_left hq]; exact map_add _ _ _
    · simp only [dite_eq_right hq]; exact (add_zero 0).symm
  map_smul' r y := by
    refine (secIso (specFun f) (tilde M) p ⊤).injective (funext fun q => ?_)
    rw [RingHom.id_apply, secIso_smulR, secIso_symm_apply, secIso_symm_apply,
      atIndexCochain_apply, atIndexCochain_apply]
    by_cases hq : q = q₀
    · simp only [dite_eq_left hq]; exact map_smul _ _ _
    · simp only [dite_eq_right hq]; exact (smul_zero r).symm

/-- The components of `atIndexL`. -/
public theorem secIso_atIndexL (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (p : ℕ)
    (q₀ : CechCochains.OrdIndex (I := Fin (d + 1)) p)
    (y : Γ(tilde M, CechCochains.inter
      (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) q₀.1))
    (q : CechCochains.OrdIndex (I := Fin (d + 1)) p) :
    secIso (specFun f) (tilde M) p ⊤ (atIndexL f M p q₀ y) q =
      if h : q = q₀ then resL (tilde M) (interEqLe f q q₀ h) y else 0 :=
  secIso_symm_apply f M p (atIndexCochain f M p q₀ y) q

/-- the comparison on the top Čech term -/
public def topTransfer (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    Cech.cechTerm f (M : Type u) (d + 1) →ₗ[R] Γ(prodTerm (specFun f) (tilde M) d, ⊤) :=
  DirectSum.toModule R _ _ fun t =>
    (atIndexL f M d (topIndex d)).comp (awayLift f M t.1 (interTop_le f t.1))

/-- `topTransfer` on a single summand of the top Čech term. -/
public theorem topTransfer_lof (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (t : {w : Finset (Fin (d + 1)) // w.card = d + 1}) (x : Cech.cechMod f (M : Type u) t.1) :
    topTransfer f M
        (DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
          (fun w => Cech.cechMod f (M : Type u) w.1) t x) =
      atIndexL f M d (topIndex d) (awayLift f M t.1 (interTop_le f t.1) x) :=
  DirectSum.toModule_lof
    (M := fun w : {w : Finset (Fin (d + 1)) // w.card = d + 1} => Cech.cechMod f (M : Type u) w.1)
    R t x

/-- For a single equation, a fraction whose denominator is empty is the image under the
augmentation of the section it comes from. -/
public theorem lastDif_preimage_zero (f : Fin 1 → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin 1))
    (htop : (⊤ : (Spec R).Opens) ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j))
    (x : Cech.cechMod f (M : Type u) s) :
    (difZero (specFun f) (tilde M)).app ⊤ (awayLift f M s htop x) =
      atIndexL f M 0 (topIndex 0) (awayLift f M s (interTop_le f s) x) := by
  refine (secIso (specFun f) (tilde M) 0 ⊤).injective (funext fun q => ?_)
  obtain rfl := topIndex_unique q
  rw [secIso_difZero, secIso_atIndexL, dite_eq_left rfl]
  exact (resL_awayLift f M s htop (interTop_le f s) _ x).trans
    (resL_awayLift f M s (interTop_le f s) (interTop_le f s) _ x).symm

/-- For at least two equations, a fraction whose denominator omits the equation `f i` is the image
under the last differential of the cochain supported, with the Čech sign of `i`, in the `i`-th
face. -/
public theorem lastDif_preimage_succ {e : ℕ} (f : Fin (e + 2) → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin (e + 2))) (i : Fin (e + 2))
    (hface : CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) (faceIndex e i).1 ≤
      PrimeSpectrum.basicOpen (∏ j ∈ s, f j))
    (x : Cech.cechMod f (M : Type u) s) :
    (difSucc (specFun f) (tilde M) e).app ⊤
        (atIndexL f M e (faceIndex e i)
          (((-1 : ℤ) ^ (i : ℕ)) • awayLift f M s hface x)) =
      atIndexL f M (e + 1) (topIndex (e + 1)) (awayLift f M s (interTop_le f s) x) := by
  refine (secIso (specFun f) (tilde M) (e + 1) ⊤).injective (funext fun t => ?_)
  obtain rfl := topIndex_unique t
  have hidx : ∀ j : Fin (e + 2),
      (⟨(topIndex (e + 1)).1 ∘ j.succAbove,
        CechCochains.strictMono_omit (topIndex (e + 1)).2 j⟩ :
          CechCochains.OrdIndex (I := Fin (e + 2)) e) = faceIndex e j := fun _ => rfl
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin (e + 2))), j ≠ i →
      ((-1 : ℤ) ^ (j : ℕ)) • CechCochains.restr (Scheme.Modules.presheaf (tilde M))
          (CechCochains.inter_le_omit
            (fun k => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f k))
            (topIndex (e + 1)).1 j)
          (secIso (specFun f) (tilde M) e ⊤
            (atIndexL f M e (faceIndex e i)
              (((-1 : ℤ) ^ (i : ℕ)) • awayLift f M s hface x))
            ⟨(topIndex (e + 1)).1 ∘ j.succAbove,
              CechCochains.strictMono_omit (topIndex (e + 1)).2 j⟩) = 0 := by
    intro j _ hj
    rw [secIso_atIndexL, dite_eq_right fun h => hj (faceIndex_injective ((hidx j).symm.trans h)),
      map_zero, smul_zero]
  rw [secIso_difSucc, ordD_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hzero,
    secIso_atIndexL, dite_eq_left (hidx i), map_zsmul, map_zsmul, sign_smul_sign, restr_eq,
    secIso_atIndexL, dite_eq_left rfl]
  exact ((congrArg (fun z => resL (tilde M)
      (CechCochains.inter_le_omit
        (fun k => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f k))
        (topIndex (e + 1)).1 i) z)
      (resL_awayLift f M s hface hface _ x)).trans
    (resL_awayLift f M s hface (interTop_le f s) _ x)).trans
      (resL_awayLift f M s (interTop_le f s) (interTop_le f s) _ x).symm


/-- the projection to the cokernel on global sections -/
public def piL (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    Γ(prodTerm (specFun f) (tilde M) d, ⊤) →ₗ[R]
      moduleSpecΓFunctor.obj (cokernel (lastDif (specFun f) (tilde M))) :=
  (moduleSpecΓFunctor.map (cokernel.π (lastDif (specFun f) (tilde M)))).hom

/-- `piL` is the projection to the cokernel, on global sections. -/
public theorem piL_apply (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (y : Γ(prodTerm (specFun f) (tilde M) d, ⊤)) :
    piL f M y = (cokernel.π (lastDif (specFun f) (tilde M))).app ⊤ y := rfl

/-- The projection to the cokernel kills the image of the last differential. -/
public theorem piL_lastDif (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (w : Γ(term (specFun f) (tilde M) d, ⊤)) :
    piL f M ((lastDif (specFun f) (tilde M)).app ⊤ w) = 0 :=
  congrArg
    (fun φ : term (specFun f) (tilde M) d ⟶ cokernel (lastDif (specFun f) (tilde M)) =>
      φ.app ⊤ w)
    (cokernel.condition (lastDif (specFun f) (tilde M)))

/-- **The descent condition.**  The image under `topTransfer` of a fraction whose denominator
omits an index is, already on global sections, the image of a section under the last differential
of the sheaf-level extended alternating Čech complex. -/
public theorem exists_lastDif_preimage (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin (d + 1))) (hs : s.card = d) (x : Cech.cechMod f (M : Type u) s) :
    ∃ w : Γ(term (specFun f) (tilde M) d, ⊤),
      (lastDif (specFun f) (tilde M)).app ⊤ w =
        atIndexL f M d (topIndex d) (awayLift f M s (interTop_le f s) x) := by
  classical
  cases d with
  | zero =>
      have hprod : (∏ j ∈ s, f j) = 1 := by rw [Finset.card_eq_zero.mp hs]; simp
      have htop : (⊤ : (Spec R).Opens) ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j) := by
        rw [hprod, PrimeSpectrum.basicOpen_one]
        exact le_rfl
      exact ⟨awayLift f M s htop x, lastDif_preimage_zero f M s htop x⟩
  | succ e =>
      have hcompl : sᶜ.card = 1 := by
        rw [Finset.card_compl, hs]
        simp
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
      have hsi : s = Finset.univ.erase i := by
        rw [← Finset.compl_singleton, ← hi, compl_compl]
      have hface : CechCochains.inter
          (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
            (faceIndex e i).1 ≤ PrimeSpectrum.basicOpen (∏ j ∈ s, f j) := by
        rw [hsi]; exact interFace_le f i
      exact ⟨atIndexL f M e (faceIndex e i) (((-1 : ℤ) ^ (i : ℕ)) • awayLift f M s hface x),
        lastDif_preimage_succ f M s i hface x⟩

/-- A fraction whose denominator omits an index has zero class in the cokernel. -/
public theorem piL_atIndexL_eq_zero (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s : Finset (Fin (d + 1))) (hs : s.card = d) (x : Cech.cechMod f (M : Type u) s) :
    piL f M (atIndexL f M d (topIndex d) (awayLift f M s (interTop_le f s) x)) = 0 := by
  obtain ⟨w, hw⟩ := exists_lastDif_preimage f M s hs x
  rw [← hw]
  exact piL_lastDif f M w


/-- `topTransfer` on a single summand, with the index presented as a `Finset` together with its
cardinality. -/
public theorem topTransfer_lof_of_card (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (T : Finset (Fin (d + 1))) (hT : T.card = d + 1) (x : Cech.cechMod f (M : Type u) T) :
    topTransfer f M
        (DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
          (fun w => Cech.cechMod f (M : Type u) w.1) ⟨T, hT⟩ x) =
      atIndexL f M d (topIndex d) (awayLift f M T (interTop_le f T) x) :=
  topTransfer_lof f M ⟨T, hT⟩ x

/-- A fraction pushed into the top Čech term from a smaller set of inverted equations has zero
class in the cokernel. -/
public theorem piL_topTransfer_lof_cechι (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s T : Finset (Fin (d + 1))) (hs : s.card = d) (hT : T.card = d + 1) (h : s ⊆ T)
    (y : Cech.cechMod f (M : Type u) s) :
    piL f M (topTransfer f M
        (DirectSum.lof R {w : Finset (Fin (d + 1)) // w.card = d + 1}
          (fun w => Cech.cechMod f (M : Type u) w.1) ⟨T, hT⟩
          (Cech.cechι f (M : Type u) h y))) = 0 := by
  rw [topTransfer_lof_of_card f M T hT, awayLift_cechι f M h (interTop_le f s) (interTop_le f T) y,
    piL_atIndexL_eq_zero f M s hs]

/-- **The boundaries die.**  The composite of `topTransfer` with the projection to the cokernel
kills the image of the last algebraic Čech differential. -/
public theorem piL_topTransfer_cechD (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (z : Cech.cechTerm f (M : Type u) d) :
    piL f M (topTransfer f M (Cech.cechD f (M : Type u) d z)) = 0 := by
  classical
  have key : (piL f M).comp ((topTransfer f M).comp (Cech.cechD f (M : Type u) d)) = 0 := by
    refine DirectSum.linearMap_ext R fun t => LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply]
    rw [Cech.cechD_lof, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_zsmul, map_zsmul,
      piL_topTransfer_lof_cechι f M t.1 (insert i.1 t.1) t.2 _ (Finset.subset_insert i.1 t.1) y,
      smul_zero]
  exact LinearMap.congr_fun key z


/-- The product of the global functions belonging to the full tuple is the global function of the
product. -/
public theorem prod_specFun_topIndex (f : Fin (d + 1) → R) :
    (∏ k, specFun f ((topIndex d).1 k)) = (Scheme.ΓSpecIso R).inv (∏ i, f i) := by
  simp only [specFun, topIndex, id]
  exact (map_prod _ f Finset.univ).symm

/-- On `⋂ᵢ D(fᵢ)`, the fraction `m/(f₁⋯f_c)` of the top Čech term is the sheaf-theoretic
fraction. -/
public theorem awayLift_univ_eq_fraction (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (m : M) :
    awayLift f M Finset.univ (interTop_le f Finset.univ)
        (LocalizedModule.mk m ⟨∏ i, f i, Submonoid.mem_powers _⟩) =
      Ring.inverse ((Spec R).presheaf.map (homOfLE (show CechCochains.inter
          (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) (topIndex d).1 ≤ ⊤
            from le_top)).op (∏ k, specFun f ((topIndex d).1 k))) •
        toOpenL M (CechCochains.inter
          (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
          (topIndex d).1) m := by
  have hunit := isUnit_prodEquations (specFun f) (⊤ : (Spec R).Opens) d (topIndex d)
  refine Scheme.Modules.isSMulRegular_of_le_basicOpen (M := tilde M)
    (f := ∏ i, f i) (interTop_le f Finset.univ) ?_
  have hL : (∏ i, f i) • awayLift f M Finset.univ (interTop_le f Finset.univ)
        (LocalizedModule.mk m ⟨∏ i, f i, Submonoid.mem_powers _⟩) =
      toOpenL M (CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
        (topIndex d).1) m := by
    rw [← map_smul, LocalizedModule.smul'_mk,
      show ((∏ i, f i) • m : (M : Type u)) =
        (⟨∏ i, f i, Submonoid.mem_powers _⟩ : Cech.cechSub f Finset.univ) • m from rfl,
      LocalizedModule.mk_cancel, ← LocalizedModule.mkLinearMap_apply, awayLift_mk]
  have hR : (∏ i, f i) •
        (Ring.inverse ((Spec R).presheaf.map (homOfLE (show CechCochains.inter
            (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) (topIndex d).1 ≤ ⊤
              from le_top)).op (∏ k, specFun f ((topIndex d).1 k))) •
          toOpenL M (CechCochains.inter
            (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
            (topIndex d).1) m) =
      toOpenL M (CechCochains.inter
        (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
        (topIndex d).1) m := by
    rw [Scheme.Modules.smul_Spec_def,
      show (Spec R).presheaf.map (CechCochains.inter
          (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j))
          (topIndex d).1).leTop.op ((Scheme.ΓSpecIso R).inv (∏ i, f i)) =
        (Spec R).presheaf.map (homOfLE (show CechCochains.inter
            (fun j => (⊤ : (Spec R).Opens) ⊓ (Spec R).basicOpen (specFun f j)) (topIndex d).1 ≤ ⊤
              from le_top)).op (∏ k, specFun f ((topIndex d).1 k)) from by
          rw [prod_specFun_topIndex]
          congr 2]
    exact smul_ringInverse_smul hunit _
  exact hL.trans hR.symm


/-- `topTransfer` carries the fraction `m/(f₁⋯f_c)` to the sheaf-theoretic fraction. -/
public theorem atIndexL_awayLift_univ (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (m : M) :
    atIndexL f M d (topIndex d)
        (awayLift f M Finset.univ (interTop_le f Finset.univ)
          (LocalizedModule.mk m ⟨∏ i, f i, Submonoid.mem_powers _⟩)) =
      (fractionHom (specFun f) (tilde M) d).app ⊤ (toOpenL M ⊤ m) := by
  refine (secIso (specFun f) (tilde M) d ⊤).injective (funext fun q => ?_)
  obtain rfl := topIndex_unique q
  rw [secIso_atIndexL, dite_eq_left rfl, fractionHom_secIso, fractionCochain_apply,
    resL_awayLift f M Finset.univ (interTop_le f Finset.univ) (interTop_le f Finset.univ) _ _,
    awayLift_univ_eq_fraction]
  rfl

/-- **The target comparison.** -/
public def targetComparison (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    (Cech.cechTerm f (M : Type u) (d + 1) ⧸
        LinearMap.range (Cech.cechD f (M : Type u) d)) →ₗ[R]
      moduleSpecΓFunctor.obj (cokernel (lastDif (specFun f) (tilde M))) :=
  Submodule.liftQ _ ((piL f M).comp (topTransfer f M)) (by
    rintro _ ⟨z, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    exact piL_topTransfer_cechD f M z)

/-- **The normalisation on fractions.**  The target comparison carries the class of the fraction
`s/(f₁⋯f_c)` to the class of the sheaf-theoretic fraction. -/
public theorem targetComparison_mk (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (m : M) :
    targetComparison f M (Submodule.Quotient.mk (Cech.topFraction f (M : Type u) m)) =
      (cokernel.π (lastDif (specFun f) (tilde M))).app ⊤
        ((fractionHom (specFun f) (tilde M) d).app ⊤ ((tilde.isoTop M).hom m)) := by
  change piL f M (topTransfer f M (Cech.topFraction f (M : Type u) m)) = _
  rw [Cech.topFraction_apply, topTransfer_lof_of_card f M Finset.univ (Finset.card_fin _),
    atIndexL_awayLift_univ]
  rfl

/-- **The target comparison exists.**  There is an `R`-linear map from the cokernel of the last
algebraic Čech differential to the global sections of `Coker(lastDif)` carrying the class of the
fraction `s/(f₁⋯f_c)` to the class of the sheaf-theoretic fraction.  This discharges the
hypothesis `τ` of `supportedFraction_eq_of_targetComparison`, and with it all of clause 3 of
Tag 0G7R except the bijectivity of `τ`, which is
`Stacks.Perfect.AffineFractionClass.bijective_targetComparison`. -/
public theorem affineTargetComparison_exists (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    ∃ τ : (Cech.cechTerm f (M : Type u) (d + 1) ⧸
             LinearMap.range (Cech.cechD f (M : Type u) d)) →ₗ[R]
           moduleSpecΓFunctor.obj (cokernel (lastDif (specFun f) (tilde M))),
      ∀ s : M, τ (Submodule.Quotient.mk (Cech.topFraction f (M : Type u) s)) =
        (cokernel.π (lastDif (specFun f) (tilde M))).app ⊤
          ((fractionHom (specFun f) (tilde M) d).app ⊤ ((tilde.isoTop M).hom s)) :=
  ⟨targetComparison f M, targetComparison_mk f M⟩

/-- **Clause 3 of Tag 0G7R, with the target comparison supplied.**  The global sections of
Tag 0G7Q's map `supportedFractionClass`, read through the source comparison on the left and
through the target comparison on the right, are the map `Cech.supportedFraction` of Tag 0G7R.

What separates this from the whole of clause 3 is that the target comparison is not shown *here*
to be an isomorphism; the source one is, by
`Stacks.Perfect.AffineFractionClass.bijective_affineSourceComparison`, so the left-hand side may
equivalently be read through `affineSourceEquiv`.  The target one is
`Stacks.Perfect.AffineFractionClass.bijective_targetComparison`, and the resulting clause is
`Stacks.Perfect.AffineFractionClass.supportedFraction_eq_conj`. -/
public theorem supportedFraction_eq_targetComparison (f : Fin (d + 1) → R)
    (M : ModuleCat.{u} R) :
    (moduleSpecΓFunctor.map (supportedFractionClass (specFun f) (tilde M))).hom ∘ₗ
        affineSourceComparison f M =
      targetComparison f M ∘ₗ Cech.supportedFraction f (M : Type u) :=
  supportedFraction_eq_of_targetComparison f M (targetComparison f M) (targetComparison_mk f M)

end Stacks.Perfect.AffineFractionClass

end
