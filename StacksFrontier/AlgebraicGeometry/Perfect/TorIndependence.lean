module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Data.List.TFAE
public import Mathlib.Order.CompletePartialOrder
public import StacksFrontier.Homology.Tor.Independence
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Homology.Tor.Presentation
import StacksFrontier.RingTheory.Tor.Balancing

/-!
# Tor independence of schemes over a base

Two schemes over a common base are Tor independent when, at every pair of points having the
same image in the base, their local rings have vanishing higher Tor over the corresponding local
ring of the base. This can be checked affine-locally: it holds if and only if the rings of
sections over every compatible triple of affine opens are Tor independent, and equivalently that
ring-theoretic condition may be checked on chosen affine open coverings of the base and of the
two inverse images.

## Main definitions

* `Algebra.TorIndependent` says that all positive-degree Tor modules of two algebras over a
  commutative ring vanish.
* `AlgebraicGeometry.TorIndependent` says that two scheme morphisms to a common base have
  Tor-independent local rings at points with the same image.

## Main results

* `Algebra.torIndependent_iff` characterizes algebraic Tor independence by positive-degree Tor
  vanishing.
* `Algebra.TorIndependent.isZero` extracts any one of these vanishing statements.
* `AlgebraicGeometry.torIndependent_iff` characterizes Tor independence of schemes stalkwise.
* `AlgebraicGeometry.TorIndependent.at_stalks` extracts Tor independence for a pair of points
  over the same point of the base.
* `AlgebraicGeometry.torIndependent_tfae` gives the three equivalent criteria for Tor
  independence.
* `AlgebraicGeometry.torIndependent_of_flat_left` and
  `AlgebraicGeometry.torIndependent_of_flat_right` deduce Tor independence from flatness of
  either one of the two morphisms.

## Implementation notes

An equality between the images of two points transports the second stalk map to the local ring
at the image of the first point, so both stalks are modules over literally the same ring before
their Tor modules are formed.

Containment of the image of an open in a base open is expressed as containment in its inverse
image. The two algebra structures on rings of sections are induced by `Scheme.Hom.appLE`. Open
coverings are represented by indexed families whose supremum is the open being covered.

## References

* [Stacks Project, Tag 0660](https://stacks.math.columbia.edu/tag/0660)
* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 0FXV](https://stacks.math.columbia.edu/tag/0FXV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Algebra

/-- Two commutative algebras over `R` are Tor independent if their Tor modules
in every positive degree vanish. -/
def TorIndependent (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] : Prop :=
  ∀ p : ℕ, 0 < p →
    IsZero (((Tor (ModuleCat.{u} R) p).obj (ModuleCat.of R A)).obj (ModuleCat.of R B))

/-- Algebraic Tor independence is precisely vanishing of every positive-degree
Tor module. -/
theorem torIndependent_iff (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    TorIndependent R A B ↔
      ∀ p : ℕ, 0 < p →
        IsZero (((Tor (ModuleCat.{u} R) p).obj (ModuleCat.of R A)).obj (ModuleCat.of R B)) :=
  Iff.rfl

/-- A chosen positive-degree Tor module vanishes for Tor-independent algebras. -/
theorem TorIndependent.isZero {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (h : TorIndependent R A B) (p : ℕ) (hp : 0 < p) :
    IsZero (((Tor (ModuleCat.{u} R) p).obj (ModuleCat.of R A)).obj (ModuleCat.of R B)) := h p hp

end Algebra

namespace AlgebraicGeometry

/-- Two schemes over a common base are Tor independent if their local rings at
every pair of points with the same image are Tor independent over the local
ring of the base. -/
@[stacks 08IA, sga "6 III 1.5", sga "5 III 6.2"]
def TorIndependent {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) : Prop :=
  ∀ (x : X) (y : Y) (h : f.base x = g.base y),
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
      (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
    Algebra.TorIndependent (S.presheaf.stalk (f.base x))
      (X.presheaf.stalk x) (Y.presheaf.stalk y)

/-- Tor independence of schemes is equivalent to Tor independence of the
local rings at every pair of points lying over the same base point. -/
theorem torIndependent_iff {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    TorIndependent f g ↔
      ∀ (x : X) (y : Y) (h : f.base x = g.base y),
        letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
          (f.stalkMap x).hom.toAlgebra
        letI : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
          (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
        Algebra.TorIndependent (S.presheaf.stalk (f.base x))
          (X.presheaf.stalk x) (Y.presheaf.stalk y) := Iff.rfl

/-- Tor-independent schemes have Tor-independent local rings at every pair of
points lying over the same point of the base. -/
theorem TorIndependent.at_stalks {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (H : TorIndependent f g) (x : X) (y : Y) (h : f.base x = g.base y) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
      (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
    Algebra.TorIndependent (S.presheaf.stalk (f.base x))
      (X.presheaf.stalk x) (Y.presheaf.stalk y) := H x y h

private lemma torIndependent_iff_ringTheory
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    Algebra.TorIndependent R A B ↔
      RingTheory.TorIndependence.TorIndependent R A B :=
  (RingTheory.TorIndependence.torIndependent_iff_isZero_tor R A B).symm

/-- Tor independence transports along compatible ring isomorphisms of the base and of the two
algebras. -/
public lemma torIndependent_congr
    (R A B R' A' B' : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']
    (eR : R ≃+* R') (eA : A ≃+* A') (eB : B ≃+* B')
    (hA : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r))
    (hB : ∀ r, eB (algebraMap R B r) = algebraMap R' B' (eR r)) :
    RingTheory.TorIndependence.TorIndependent R A B ↔
      RingTheory.TorIndependence.TorIndependent R' A' B' := by
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor,
    RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  let F := ModuleCat.restrictScalars eR.toRingHom
  have iso : ∀ (C C' : Type u) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R' C']
      (e : C ≃+* C') (h : ∀ r, e (algebraMap R C r) = algebraMap R' C' (eR r)),
      ModuleCat.of R C ≅ F.obj (ModuleCat.of R' C') := fun C C' _ _ _ _ e h ↦
    LinearEquiv.toModuleIso (show C ≃ₗ[R] (F.obj (ModuleCat.of R' C')) from
      { toFun := e
        invFun := e.symm
        left_inv := e.left_inv
        right_inv := e.right_inv
        map_add' := e.map_add
        map_smul' := fun r a ↦ by
          show e (r • a) = (eR r) • e a
          rw [Algebra.smul_def, Algebra.smul_def, e.map_mul, h] })
  let iA := iso A A' eA hA
  let iB := iso B B' eB hB
  refine ⟨fun hzero i hi ↦ ?_, fun hzero i hi ↦ ?_⟩
  · apply (RingTheory.TorIndependence.isZero_tor_restrict_iff eR
      (ModuleCat.of R' A') (ModuleCat.of R' B') i).mp
    rw [← (((CategoryTheory.Tor (ModuleCat R) i).mapIso iA).app
      (F.obj (ModuleCat.of R' B'))).isZero_iff,
      ← (((CategoryTheory.Tor (ModuleCat R) i).obj (ModuleCat.of R A)).mapIso iB).isZero_iff]
    exact hzero i hi
  · rw [(((CategoryTheory.Tor (ModuleCat R) i).obj (ModuleCat.of R A)).mapIso iB).isZero_iff,
      (((CategoryTheory.Tor (ModuleCat R) i).mapIso iA).app
        (F.obj (ModuleCat.of R' B'))).isZero_iff]
    exact (RingTheory.TorIndependence.isZero_tor_restrict_iff eR
      (ModuleCat.of R' A') (ModuleCat.of R' B') i).mpr (hzero i hi)

private lemma torIndependent_arrowIso
    (R A B R' A' B' : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [CommRing R'] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']
    (f : R →+* A) (g : R →+* B)
    (f' : R' →+* A') (g' : R' →+* B')
    (iA : Arrow.mk (CommRingCat.ofHom f) ≅ Arrow.mk (CommRingCat.ofHom f'))
    (iB : Arrow.mk (CommRingCat.ofHom g) ≅ Arrow.mk (CommRingCat.ofHom g'))
    (hbase : iA.hom.left = iB.hom.left)
    (hf : f = algebraMap R A) (hg : g = algebraMap R B)
    (hf' : f' = algebraMap R' A') (hg' : g' = algebraMap R' B') :
    RingTheory.TorIndependence.TorIndependent R A B ↔
      RingTheory.TorIndependence.TorIndependent R' A' B' := by
  let eR : R ≃+* R' := (asIso iA.hom.left).commRingCatIsoToRingEquiv
  let eA : A ≃+* A' := (asIso iA.hom.right).commRingCatIsoToRingEquiv
  let eB : B ≃+* B' := (asIso iB.hom.right).commRingCatIsoToRingEquiv
  have hA : ∀ r, eA (algebraMap R A r) = algebraMap R' A' (eR r) := by
    intro r
    show iA.hom.right.hom (algebraMap R A r) =
      algebraMap R' A' (iA.hom.left.hom r)
    simpa [hf, hf'] using (DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp iA.hom.w) r).symm
  have hB : ∀ r, eB (algebraMap R B r) = algebraMap R' B' (eR r) := by
    intro r
    have hh := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp iB.hom.w) r
    rw [← hbase] at hh
    show iB.hom.right.hom (algebraMap R B r) =
      algebraMap R' B' (iA.hom.left.hom r)
    simpa [hg, hg'] using hh.symm
  exact torIndependent_congr R A B R' A' B' eR eA eB hA hB

private lemma stalk_eqToHom_algebraMap
    {T : Scheme.{u}} (W : T.Opens) (x y : T) (hx : x ∈ W) (hy : y ∈ W)
    (hxy : x = y) (a : Γ(T, W)) :
    letI : Algebra Γ(T, W) (T.presheaf.stalk x) :=
      T.presheaf.algebra_section_stalk ⟨x, hx⟩
    letI : Algebra Γ(T, W) (T.presheaf.stalk y) :=
      T.presheaf.algebra_section_stalk ⟨y, hy⟩
    (eqToHom (congrArg (fun z ↦ T.presheaf.stalk z) hxy)).hom
      (algebraMap Γ(T, W) (T.presheaf.stalk x) a) =
    algebraMap Γ(T, W) (T.presheaf.stalk y) a := by
  cases hxy
  rfl

private lemma torIndependent_atPrime_congr
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (r₁ r₂ : PrimeSpectrum R) (p₁ p₂ : PrimeSpectrum A)
    (q₁ q₂ : PrimeSpectrum B)
    (hr : r₁ = r₂) (hp : p₁ = p₂) (hq : q₁ = q₂)
    (h₁A : r₁.asIdeal = p₁.asIdeal.comap (algebraMap R A))
    (h₁B : r₁.asIdeal = q₁.asIdeal.comap (algebraMap R B))
    (h₂A : r₂.asIdeal = p₂.asIdeal.comap (algebraMap R A))
    (h₂B : r₂.asIdeal = q₂.asIdeal.comap (algebraMap R B)) :
    letI : p₁.asIdeal.LiesOver r₁.asIdeal := ⟨h₁A⟩
    letI : q₁.asIdeal.LiesOver r₁.asIdeal := ⟨h₁B⟩
    letI : Algebra (Localization.AtPrime r₁.asIdeal) (Localization.AtPrime p₁.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver r₁.asIdeal p₁.asIdeal
    letI : Algebra (Localization.AtPrime r₁.asIdeal) (Localization.AtPrime q₁.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver r₁.asIdeal q₁.asIdeal
    RingTheory.TorIndependence.TorIndependent (Localization.AtPrime r₁.asIdeal)
      (Localization.AtPrime p₁.asIdeal) (Localization.AtPrime q₁.asIdeal) ↔
    letI : p₂.asIdeal.LiesOver r₂.asIdeal := ⟨h₂A⟩
    letI : q₂.asIdeal.LiesOver r₂.asIdeal := ⟨h₂B⟩
    letI : Algebra (Localization.AtPrime r₂.asIdeal) (Localization.AtPrime p₂.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver r₂.asIdeal p₂.asIdeal
    letI : Algebra (Localization.AtPrime r₂.asIdeal) (Localization.AtPrime q₂.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver r₂.asIdeal q₂.asIdeal
    RingTheory.TorIndependence.TorIndependent (Localization.AtPrime r₂.asIdeal)
      (Localization.AtPrime p₂.asIdeal) (Localization.AtPrime q₂.asIdeal) := by
  cases hr
  cases hp
  cases hq
  rfl

/-- The prime of a section ring at a point is the preimage of the prime at a point above it. -/
private lemma primeIdealOf_eq_comap_appLE {S X : Scheme.{u}} (f : X ⟶ S) (W : S.Opens)
    (hW : IsAffineOpen W) (U : X.Opens) (hU : IsAffineOpen U) (hUW : U ≤ f ⁻¹ᵁ W)
    {x : X} (hx : x ∈ U) :
    (hW.primeIdealOf ⟨f.base x, hUW hx⟩).asIdeal =
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.comap (f.appLE W U hUW).hom :=
  (congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE W hW U hU hUW hx)).symm

private lemma torIndependent_at_affine_points_iff
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (U : X.Opens) (hU : IsAffineOpen U)
    (V : Y.Opens) (hV : IsAffineOpen V)
    (W : S.Opens) (hW : IsAffineOpen W)
    (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W)
    (x : X) (hx : x ∈ U) (y : Y) (hy : y ∈ V)
    (hxy : f.base x = g.base y) :
    letI : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
    letI : Algebra Γ(S, W) Γ(Y, V) := (g.appLE W V hVW).hom.toAlgebra
    let r := (hW.primeIdealOf ⟨f.base x, hUW hx⟩).asIdeal
    let _rG := (hW.primeIdealOf ⟨g.base y, hVW hy⟩).asIdeal
    let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    let q := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
    letI : p.LiesOver r := ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE
      W hW U hU hUW hx).1).symm⟩
    letI : q.LiesOver r := ⟨
      (congrArg (fun z : W ↦ (hW.primeIdealOf z).asIdeal)
        (Subtype.ext hxy)).trans
        (congr($(IsAffineOpen.comap_primeIdealOf_appLE W hW V hV hVW hy).1).symm)⟩
    letI : Algebra (Localization.AtPrime r) (Localization.AtPrime p) :=
      Localization.AtPrime.algebraOfLiesOver r p
    letI : Algebra (Localization.AtPrime r) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver r q
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    letI : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
      (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hxy) ≫ g.stalkMap y).hom.toAlgebra
    Algebra.TorIndependent
        (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) (Y.presheaf.stalk y) ↔
      RingTheory.TorIndependence.TorIndependent
        (Localization.AtPrime r) (Localization.AtPrime p) (Localization.AtPrime q) := by
  let : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  let : Algebra Γ(S, W) Γ(Y, V) := (g.appLE W V hVW).hom.toAlgebra
  have hr : (hW.primeIdealOf ⟨f.base x, hUW hx⟩).asIdeal =
      (hW.primeIdealOf ⟨g.base y, hVW hy⟩).asIdeal :=
    congrArg (fun z : W ↦ (hW.primeIdealOf z).asIdeal) (Subtype.ext hxy)
  let r := (hW.primeIdealOf ⟨f.base x, hUW hx⟩).asIdeal
  let rG := (hW.primeIdealOf ⟨g.base y, hVW hy⟩).asIdeal
  let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  let : r.IsPrime := (hW.primeIdealOf ⟨f.base x, hUW hx⟩).isPrime
  let : rG.IsPrime := (hW.primeIdealOf ⟨g.base y, hVW hy⟩).isPrime
  let : p.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let : q.IsPrime := (hV.primeIdealOf ⟨y, hy⟩).isPrime
  have hpOver : r = Ideal.comap (f.appLE W U hUW).hom p :=
    primeIdealOf_eq_comap_appLE f W hW U hU hUW hx
  let : p.LiesOver r := ⟨hpOver⟩
  have hGOver : rG = Ideal.comap (g.appLE W V hVW).hom q :=
    primeIdealOf_eq_comap_appLE g W hW V hV hVW hy
  have hqOver : r = Ideal.comap (g.appLE W V hVW).hom q := hr.trans hGOver
  let : q.LiesOver r := ⟨hqOver⟩
  let : Algebra (Localization.AtPrime r) (Localization.AtPrime p) :=
    Localization.AtPrime.algebraOfLiesOver r p
  let : Algebra (Localization.AtPrime r) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver r q
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hxy) ≫ g.stalkMap y).hom.toAlgebra
  let iA := IsAffineOpen.arrowStalkMapIso f W hW U hU hUW hx
  let eS : S.presheaf.stalk (f.base x) ≅ S.presheaf.stalk (g.base y) :=
    asIso (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hxy))
  let iBraw := IsAffineOpen.arrowStalkMapIso g W hW V hV hVW hy
  have hprimeCompl : r.primeCompl = rG.primeCompl := by
    ext a
    show a ∉ (hW.primeIdealOf ⟨f.base x, hUW hx⟩).asIdeal ↔
      a ∉ (hW.primeIdealOf ⟨g.base y, hVW hy⟩).asIdeal
    rw [hr]
  let : IsLocalization r.primeCompl (Localization.AtPrime rG) := by
    exact hprimeCompl.symm ▸
      (inferInstance : IsLocalization rG.primeCompl (Localization.AtPrime rG))
  have hmapPrimeComplSymm :
      Submonoid.map (RingEquiv.refl Γ(S, W)).toMonoidHom rG.primeCompl =
        r.primeCompl := by
    simpa using hprimeCompl.symm
  let eLocEquiv : Localization.AtPrime rG ≃+* Localization.AtPrime r :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime rG)
      (Localization.AtPrime r) (RingEquiv.refl Γ(S, W)) hmapPrimeComplSymm
  let eLoc : CommRingCat.of (Localization.AtPrime rG) ≅
      CommRingCat.of (Localization.AtPrime r) :=
    eLocEquiv.toCommRingCatIso
  have hLocAlgMap (a : Γ(S, W)) :
      eLoc.hom (algebraMap Γ(S, W) (Localization.AtPrime rG) a) =
        algebraMap Γ(S, W) (Localization.AtPrime r) a := by
    show IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime rG)
      (Localization.AtPrime r) (RingEquiv.refl Γ(S, W)) hmapPrimeComplSymm _ = _
    rw [IsLocalization.ringEquivOfRingEquiv_eq]
    simp
  have hLocMap : eLoc.hom ≫ CommRingCat.ofHom
      (Localization.localRingHom r q (g.appLE W V hVW).hom hqOver) =
      CommRingCat.ofHom
        (Localization.localRingHom rG q (g.appLE W V hVW).hom hGOver) := by
    apply CommRingCat.hom_ext_iff.mpr
    apply IsLocalization.ringHom_ext rG.primeCompl
    ext a
    show Localization.localRingHom r q (g.appLE W V hVW).hom hqOver
        (eLoc.hom (algebraMap Γ(S, W) (Localization.AtPrime rG) a)) =
      _
    rw [hLocAlgMap]
    simp [Localization.localRingHom_to_map]
  let iB₀ : Arrow.mk (g.stalkMap y) ≅ Arrow.mk (CommRingCat.ofHom
      (Localization.localRingHom r q (g.appLE W V hVW).hom hqOver)) :=
    Arrow.isoMk' _ _ (asIso iBraw.hom.left ≪≫ eLoc)
      (asIso iBraw.hom.right) (by
        show iBraw.hom.left ≫ eLoc.hom ≫ CommRingCat.ofHom
            (Localization.localRingHom r q (g.appLE W V hVW).hom hqOver) =
          (g.stalkMap y) ≫ iBraw.hom.right
        calc
          _ = iBraw.hom.left ≫ (eLoc.hom ≫ CommRingCat.ofHom
              (Localization.localRingHom r q (g.appLE W V hVW).hom hqOver)) := by
            rfl
          _ = iBraw.hom.left ≫ CommRingCat.ofHom
              (Localization.localRingHom rG q (g.appLE W V hVW).hom hGOver) := by
            rw [hLocMap]
          _ = _ := iBraw.hom.w)
  let iB : Arrow.mk ((eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hxy) ≫
      g.stalkMap y)) ≅ Arrow.mk (CommRingCat.ofHom
        (Localization.localRingHom r q (g.appLE W V hVW).hom hqOver)) :=
    Arrow.isoMk' _ _ (eS ≪≫ asIso iB₀.hom.left) (asIso iB₀.hom.right) (by
      calc
        _ = eS.hom ≫ (iB₀.hom.left ≫
            CommRingCat.ofHom (Localization.localRingHom r q
              (g.appLE W V hVW).hom hqOver)) := by simp [Category.assoc]
        _ = eS.hom ≫ (g.stalkMap y ≫ iB₀.hom.right) := by
          congr 1
          exact iB₀.hom.w
        _ = (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hxy) ≫
              g.stalkMap y) ≫ iB₀.hom.right := by simp [eS, Category.assoc])
  have hbase : iA.hom.left = iB.hom.left := by
    let : Algebra Γ(S, W) (S.presheaf.stalk (f.base x)) :=
      S.presheaf.algebra_section_stalk ⟨f.base x, hUW hx⟩
    let : IsLocalization r.primeCompl (S.presheaf.stalk (f.base x)) :=
      hW.isLocalization_stalk ⟨f.base x, hUW hx⟩
    let : Algebra Γ(S, W) (S.presheaf.stalk (g.base y)) :=
      S.presheaf.algebra_section_stalk ⟨g.base y, hVW hy⟩
    let : IsLocalization rG.primeCompl (S.presheaf.stalk (g.base y)) :=
      hW.isLocalization_stalk ⟨g.base y, hVW hy⟩
    have hmaps :
        (iA.hom.left.hom : S.presheaf.stalk (f.base x) →+* Localization.AtPrime r) =
        (iB.hom.left.hom : S.presheaf.stalk (f.base x) →+* Localization.AtPrime r) := by
      apply IsLocalization.ringHom_ext (R := Γ(S, W)) (M := r.primeCompl)
        (S := S.presheaf.stalk (f.base x))
      ext a
      have htransport := stalk_eqToHom_algebraMap W (f.base x) (g.base y)
        (hUW hx) (hVW hy) hxy a
      simp only [RingHom.comp_apply]
      simp only [Arrow.mk_left, IsAffineOpen.arrowStalkMapIso, hr, Arrow.isoMk_hom_left,
        RingEquiv.toCommRingCatIso_hom, AlgEquiv.toRingEquiv_toRingHom,
        ConcreteCategory.hom_ofHom, RingHom.coe_coe, AlgEquiv.commutes, Arrow.isoMk_hom_right,
        Arrow.mk_right, Iso.trans_hom, asIso_hom, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply, htransport, iA, iB, eS, iB₀, iBraw]
      rw [hLocAlgMap]
    exact CommRingCat.hom_ext_iff.mpr hmaps
  rw [torIndependent_iff_ringTheory]
  exact torIndependent_arrowIso _ _ _ _ _ _ (f.stalkMap x).hom
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hxy) ≫ g.stalkMap y).hom
    (Localization.localRingHom r p (f.appLE W U hUW).hom hpOver)
    (Localization.localRingHom r q (g.appLE W V hVW).hom hqOver)
    iA iB hbase rfl rfl rfl rfl

/-- Tor independence of two schemes over a base can be checked on every
compatible triple of affine opens, or on affine open coverings of the base and
of the two inverse images. -/
@[stacks 0FXV, sga "6 III 1.5" "affine/local criterion"]
theorem torIndependent_tfae {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    List.TFAE [
      TorIndependent f g,
      ∀ (U : X.Opens) (_ : IsAffineOpen U)
        (V : Y.Opens) (_ : IsAffineOpen V)
        (W : S.Opens) (_ : IsAffineOpen W)
        (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W),
        letI : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
        letI : Algebra Γ(S, W) Γ(Y, V) := (g.appLE W V hVW).hom.toAlgebra
        Algebra.TorIndependent Γ(S, W) Γ(X, U) Γ(Y, V),
      ∃ (I : Type u) (W : I → S.Opens),
        ((⨆ i, W i) = ⊤) ∧
          ((∀ i, IsAffineOpen (W i)) ∧
            ∀ i, ∃ (J : Type u) (U : J → X.Opens)
              (hU : (⨆ j, U j) = f ⁻¹ᵁ W i),
              (∀ j, IsAffineOpen (U j)) ∧
                ∃ (K : Type u) (V : K → Y.Opens)
                  (hV : (⨆ k, V k) = g ⁻¹ᵁ W i),
                  (∀ k, IsAffineOpen (V k)) ∧
                    ∀ j k,
                      let hUW : U j ≤ f ⁻¹ᵁ W i := (le_iSup U j).trans hU.le
                      let hVW : V k ≤ g ⁻¹ᵁ W i := (le_iSup V k).trans hV.le
                      letI : Algebra Γ(S, W i) Γ(X, U j) :=
                        (f.appLE (W i) (U j) hUW).hom.toAlgebra
                      letI : Algebra Γ(S, W i) Γ(Y, V k) :=
                        (g.appLE (W i) (V k) hVW).hom.toAlgebra
                      Algebra.TorIndependent
                        Γ(S, W i) Γ(X, U j) Γ(Y, V k))] := by
  tfae_have 1 → 2 := by
    intro h U hU V hV W hW hUW hVW
    let : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
    let : Algebra Γ(S, W) Γ(Y, V) := (g.appLE W V hVW).hom.toAlgebra
    have hlocal : ∀ (r : PrimeSpectrum Γ(S, W))
        (p : PrimeSpectrum Γ(X, U)) (q : PrimeSpectrum Γ(Y, V))
        (hp : r.asIdeal = p.asIdeal.comap (algebraMap Γ(S, W) Γ(X, U)))
        (hq : r.asIdeal = q.asIdeal.comap (algebraMap Γ(S, W) Γ(Y, V))),
        let : p.asIdeal.LiesOver r.asIdeal := ⟨hp⟩
        let : q.asIdeal.LiesOver r.asIdeal := ⟨hq⟩
        let : Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime p.asIdeal) :=
          Localization.AtPrime.algebraOfLiesOver r.asIdeal p.asIdeal
        let : Algebra (Localization.AtPrime r.asIdeal) (Localization.AtPrime q.asIdeal) :=
          Localization.AtPrime.algebraOfLiesOver r.asIdeal q.asIdeal
        RingTheory.TorIndependence.TorIndependent (Localization.AtPrime r.asIdeal)
          (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) := by
      intro r p q hp hq
      let x : X := (hU.isoSpec.inv.base p).1
      let y : Y := (hV.isoSpec.inv.base q).1
      have hx : x ∈ U := (hU.isoSpec.inv.base p).2
      have hy : y ∈ V := (hV.isoSpec.inv.base q).2
      have hpU : hU.primeIdealOf ⟨x, hx⟩ = p :=
        congrArg (fun k : Scheme.Hom (Spec Γ(X, U)) (Spec Γ(X, U)) ↦ k.base p)
          hU.isoSpec.inv_hom_id
      have hqV : hV.primeIdealOf ⟨y, hy⟩ = q :=
        congrArg (fun k : Scheme.Hom (Spec Γ(Y, V)) (Spec Γ(Y, V)) ↦ k.base q)
          hV.isoSpec.inv_hom_id
      have hbaseX : (hW.primeIdealOf ⟨f.base x, hUW hx⟩).asIdeal = r.asIdeal := by
        rw [primeIdealOf_eq_comap_appLE f W hW U hU hUW hx, hpU]
        exact hp.symm
      have hbaseY : (hW.primeIdealOf ⟨g.base y, hVW hy⟩).asIdeal = r.asIdeal := by
        rw [primeIdealOf_eq_comap_appLE g W hW V hV hVW hy, hqV]
        exact hq.symm
      have hprime : hW.primeIdealOf ⟨f.base x, hUW hx⟩ = hW.primeIdealOf ⟨g.base y, hVW hy⟩ :=
        PrimeSpectrum.ext (hbaseX.trans hbaseY.symm)
      have hpoint : f.base x = g.base y := by
        simpa only [IsAffineOpen.fromSpec_primeIdealOf] using congrArg hW.fromSpec.base hprime
      let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
        (f.stalkMap x).hom.toAlgebra
      let : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
        (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) hpoint) ≫ g.stalkMap y).hom.toAlgebra
      have hloc := (torIndependent_at_affine_points_iff f g U hU V hV W hW
        hUW hVW x hx y hy hpoint).mp (h.at_stalks x y hpoint)
      let r₁ := hW.primeIdealOf ⟨f.base x, hUW hx⟩
      let p₁ := hU.primeIdealOf ⟨x, hx⟩
      let q₁ := hV.primeIdealOf ⟨y, hy⟩
      have hrEq : r₁ = r := PrimeSpectrum.ext hbaseX
      have h₁A : r₁.asIdeal = p₁.asIdeal.comap (algebraMap Γ(S, W) Γ(X, U)) := by
        simpa only [r₁, p₁, hrEq, hpU] using hp
      have h₁B : r₁.asIdeal = q₁.asIdeal.comap (algebraMap Γ(S, W) Γ(Y, V)) := by
        simpa only [r₁, q₁, hrEq, hqV] using hq
      exact (torIndependent_atPrime_congr r₁ r p₁ p q₁ q hrEq hpU hqV
        h₁A h₁B hp hq).mp hloc
    exact (torIndependent_iff_ringTheory Γ(S, W) Γ(X, U) Γ(Y, V)).mpr
      (((RingTheory.TorIndependence.torIndependent_localizations_tfae
        Γ(S, W) Γ(X, U) Γ(Y, V)).out 2 1).mp hlocal)
  tfae_have 2 → 3 := by
    intro h
    let I := S.affineOpens
    refine ⟨I, fun i ↦ i.1, ?_, fun i ↦ i.2, fun i ↦ ?_⟩
    · simpa [I] using iSup_affineOpens_eq_top S
    let J := {U : X.affineOpens // (U : X.Opens) ≤ f ⁻¹ᵁ (i : S.Opens)}
    let K := {V : Y.affineOpens // (V : Y.Opens) ≤ g ⁻¹ᵁ (i : S.Opens)}
    refine ⟨J, fun j ↦ j.1.1, le_antisymm (iSup_le fun j ↦ j.2) fun x hx ↦ ?_, fun j ↦ j.1.2,
      K, fun k ↦ k.1.1, le_antisymm (iSup_le fun k ↦ k.2) fun y hy ↦ ?_, fun k ↦ k.1.2,
      fun j k ↦ h _ j.1.2 _ k.1.2 i.1 i.2 j.2 k.2⟩
    · obtain ⟨U, hU, hxU, hsub⟩ := exists_isAffineOpen_mem_and_subset hx
      exact le_iSup (fun j : J ↦ (j.1 : X.Opens)) ⟨⟨U, hU⟩, hsub⟩ hxU
    · obtain ⟨V, hV, hyV, hsub⟩ := exists_isAffineOpen_mem_and_subset hy
      exact le_iSup (fun k : K ↦ (k.1 : Y.Opens)) ⟨⟨V, hV⟩, hsub⟩ hyV
  tfae_have 3 → 1 := by
    intro h x y hxy
    obtain ⟨I, W, hcover, hWaff, hdata⟩ := h
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show f.base x ∈ ⨆ i, W i by simp [hcover])
    obtain ⟨J, U, hUcover, hUaff, K, V, hVcover, hVaff, htor⟩ := hdata i
    have hxInv : x ∈ f ⁻¹ᵁ W i := hi
    have hyInv : y ∈ g ⁻¹ᵁ W i := by
      show g.base y ∈ W i
      rw [← hxy]
      exact hi
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ j, U j by rwa [hUcover])
    obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show y ∈ ⨆ k, V k by rwa [hVcover])
    let hUW : U j ≤ f ⁻¹ᵁ W i := (le_iSup U j).trans hUcover.le
    let hVW : V k ≤ g ⁻¹ᵁ W i := (le_iSup V k).trans hVcover.le
    let : Algebra Γ(S, W i) Γ(X, U j) :=
      (f.appLE (W i) (U j) hUW).hom.toAlgebra
    let : Algebra Γ(S, W i) Γ(Y, V k) :=
      (g.appLE (W i) (V k) hVW).hom.toAlgebra
    have htorRing : RingTheory.TorIndependence.TorIndependent
        Γ(S, W i) Γ(X, U j) Γ(Y, V k) :=
      (torIndependent_iff_ringTheory _ _ _).mp (htor j k)
    let zf : W i := ⟨f.base x, hxInv⟩
    let zg : W i := ⟨g.base y, hyInv⟩
    let r := (hWaff i).primeIdealOf zf
    let r' := (hWaff i).primeIdealOf zg
    let p := (hUaff j).primeIdealOf ⟨x, hj⟩
    let q := (hVaff k).primeIdealOf ⟨y, hk⟩
    have hr : r.asIdeal = r'.asIdeal :=
      congrArg (fun z : W i ↦ ((hWaff i).primeIdealOf z).asIdeal) (Subtype.ext hxy)
    have hp : r.asIdeal = p.asIdeal.comap (algebraMap Γ(S, W i) Γ(X, U j)) :=
      primeIdealOf_eq_comap_appLE f (W i) (hWaff i) (U j) (hUaff j) hUW hj
    have hq : r.asIdeal = q.asIdeal.comap (algebraMap Γ(S, W i) Γ(Y, V k)) :=
      hr.trans (primeIdealOf_eq_comap_appLE g (W i) (hWaff i) (V k) (hVaff k) hVW hk)
    have hcriterion := ((RingTheory.TorIndependence.torIndependent_localizations_tfae
      Γ(S, W i) Γ(X, U j) Γ(Y, V k)).out 1 2).mp htorRing
    exact (torIndependent_at_affine_points_iff f g (U j) (hUaff j)
      (V k) (hVaff k) (W i) (hWaff i) hUW hVW x hj y hk hxy).mpr (hcriterion r p q hp hq)
  tfae_finish

/-! ### Tor independence from flatness -/

/-- Precomposing a flat ring homomorphism with an equality of its source is flat. -/
private lemma flat_eqToHom_comp {A B R : CommRingCat.{u}} (h : A = B) (φ : B ⟶ R)
    (hφ : φ.hom.Flat) : (eqToHom h ≫ φ).hom.Flat := by
  cases h
  simpa using hφ

/-- Tor independence of algebras is symmetric, by the balancing of Tor. -/
private lemma torIndependent_symm_aux {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (hAB : Algebra.TorIndependent R A B) :
    Algebra.TorIndependent R B A := by
  intro p hp
  obtain ⟨e⟩ := tor_symm_canonically_iso R p
  exact (hAB p hp).of_iso ((e.app (ModuleCat.of R B)).app (ModuleCat.of R A))

/-- A flat algebra is Tor independent from every other algebra over the same ring. -/
private lemma torIndependent_of_flat_aux {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Flat R A] : Algebra.TorIndependent R A B := by
  intro p hp
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  exact isZero_Tor_succ_of_flat (ModuleCat.of R A) (ModuleCat.of R B) k

/-- A flat morphism is Tor independent from every other morphism to its target: the stalk of `X`
at `x` is a flat module over the stalk of `S` at `f x`, and tensoring with a flat module preserves
the exactness of a projective resolution, so `Torᵢ` against it vanishes in positive degrees. -/
theorem torIndependent_of_flat_left {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Flat f] :
    TorIndependent f g := by
  intro x y h
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
  have hflat : Module.Flat (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  exact torIndependent_of_flat_aux

/-- Every morphism is Tor independent from a flat morphism to the same target: the vanishing of
`Torᵢ` is symmetric in the two arguments by the balancing of Tor, which reduces this to
`AlgebraicGeometry.torIndependent_of_flat_left`. -/
theorem torIndependent_of_flat_right {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Flat g] :
    TorIndependent f g := by
  intro x y h
  let : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ g.stalkMap y).hom.toAlgebra
  have hflat : Module.Flat (S.presheaf.stalk (f.base x)) (Y.presheaf.stalk y) :=
    flat_eqToHom_comp (congrArg (fun z ↦ S.presheaf.stalk z) h) (g.stalkMap y)
      (Flat.stalkMap g y)
  exact torIndependent_symm_aux torIndependent_of_flat_aux

/-- **Tor independence of algebras is symmetric**, by the balancing of Tor
([Stacks, Tag 00M3]). -/
theorem _root_.Algebra.TorIndependent.symm {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (hAB : Algebra.TorIndependent R A B) :
    Algebra.TorIndependent R B A := torIndependent_symm_aux hAB

/-- **Tor independence of schemes is symmetric.** On a compatible triple of affine opens the
condition is Tor independence of two algebras over a common ring, which is symmetric by the
balancing of Tor ([Stacks, Tag 00M3]); the affine criterion of [Stacks, Tag 0FXV] transfers that
to the two morphisms. -/
theorem TorIndependent.symm {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (H : TorIndependent f g) : TorIndependent g f := by
  have H2 := ((torIndependent_tfae f g).out 1 2).mp H
  refine ((torIndependent_tfae g f).out 1 2).mpr fun V hV U hU W hW hVW hUW ↦ ?_
  let : Algebra Γ(S, W) Γ(Y, V) := (g.appLE W V hVW).hom.toAlgebra
  let : Algebra Γ(S, W) Γ(X, U) := (f.appLE W U hUW).hom.toAlgebra
  exact (H2 U hU V hV W hW hUW hVW).symm

end AlgebraicGeometry
