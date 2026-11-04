module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Canonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RefinementCanonical

/-!
# Pasting canonical comparisons of inverse images along adjacent squares

Let

```text
  P --a--> Q --a'--> R
  |        |         |
  eP       eQ        eR
  v        v         v
  X --b--> Y --b'--> W
```

be two commutative squares of algebraic spaces and `M` a module on `W`. The canonical comparison
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison` of the outer square is the
composite of the canonical comparisons of the two squares, the right one pulled back along `a`,
read through the comparisons of iterated inverse images of Stacks 03LU. This is the pasting law
of the comparisons, the horizontal companion of
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_trans`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_trans_eqToIso`: changing the
  second leg along an equality of morphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_paste`: the pasting law.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/Canonical.lean`, everything
is an equation of isomorphisms, never of their underlying morphisms, and it is reached through
`AlgebraicGeometry.Space.QuasiCoherentDescent.pair_coherence` and
`AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_factorRight`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Changing the second leg of a canonical comparison along an equality of morphisms composes
the comparison with the transport of the inverse image along that equality. -/
theorem canonicalComparison_trans_eqToIso {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    {b b' : P ⟶ R} (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) (hb : b = b')
    (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison a b fi fj h M ≪≫
        eqToIso (congrArg (fun q : P ⟶ R =>
          (modulePullback B S hS q).obj ((modulePullback B S hS fj).obj M)) hb) =
      canonicalComparison a b' fi fj (hb ▸ h) M := by
  subst hb
  simp

/-- **The pasting law of canonical comparisons.** For two commutative squares
`a ≫ eQ = eP ≫ b` and `a' ≫ eR = eQ ≫ b'` side by side and a module `M` on the bottom right
corner, the canonical comparison of the right square pulled back along `a`, followed by the
canonical comparison of the left square at `b'^* M`, is the canonical comparison of the outer
square followed by the comparison of iterated inverse images along `b` and `b'`. -/
theorem canonicalComparison_paste {P Q R X Y W : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    (a' : Q ⟶ R) (eP : P ⟶ X) (eQ : Q ⟶ Y) (eR : R ⟶ W) (b : X ⟶ Y) (b' : Y ⟶ W)
    (h : a ≫ eQ = eP ≫ b) (h' : a' ≫ eR = eQ ≫ b')
    (hp : (a ≫ a') ≫ eR = eP ≫ b ≫ b') (M : Modules.{u, u} B S hS W.1 W.2) :
    pullbackComparison B S hS a a' (a ≫ a') rfl ((modulePullback B S hS eR).obj M) ≪≫
        (modulePullback B S hS a).mapIso (canonicalComparison a' eQ eR b' h' M) ≪≫
        canonicalComparison a eP eQ b h ((modulePullback B S hS b').obj M) =
      canonicalComparison (a ≫ a') eP eR (b ≫ b') hp M ≪≫
        (modulePullback B S hS eP).mapIso
          (pullbackComparison B S hS b b' (b ≫ b') rfl M) := by
  have hpair := pair_coherence B S hS a a' eQ eR b' h' M
  have hright := canonicalComparison_factorRight B S hS (a ≫ a') eR eP b b' (b ≫ b') rfl hp
    (by rw [hp, Category.assoc]) M
  have hleft : canonicalComparison (a ≫ a') (a ≫ eQ) eR b'
      (by rw [Category.assoc, Category.assoc, h']) M ≪≫
        eqToIso (congrArg (fun q : P ⟶ Y =>
          (modulePullback B S hS q).obj ((modulePullback B S hS b').obj M)) h) =
      canonicalComparison (a ≫ a') (eP ≫ b) eR b' (by rw [hp, Category.assoc]) M :=
    canonicalComparison_trans_eqToIso (a ≫ a') eR b' _ h M
  rw [hright, ← hleft, ← hpair]
  rw [canonicalComparison_eq a eP eQ b h, canonicalComparison_eq]
  simp only [Iso.trans_assoc, Functor.mapIso_symm, pullbackComparison_rfl, Iso.symm_symm_eq]
  rw [Iso.self_symm_id, Iso.trans_refl]

/-- **Changing the outer legs of a canonical comparison along equalities of morphisms**
transports it along the induced identifications of the iterated inverse images. -/
theorem canonicalComparison_congr {A P Q R : AlgebraicSpaces B S hS} {a a' : P ⟶ Q}
    (b : P ⟶ R) (fi : Q ⟶ A) {fj fj' : R ⟶ A} (ha : a = a') (hfj : fj = fj')
    (h : a ≫ fi = b ≫ fj) (h' : a' ≫ fi = b ≫ fj') (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison a b fi fj h M =
      eqToIso (congrArg (fun q : P ⟶ Q =>
          (modulePullback B S hS q).obj ((modulePullback B S hS fi).obj M)) ha) ≪≫
        canonicalComparison a' b fi fj' h' M ≪≫
        (modulePullback B S hS b).mapIso (eqToIso (congrArg (fun q : R ⟶ A =>
          (modulePullback B S hS q).obj M) hfj.symm)) := by
  subst ha
  subst hfj
  simp

/-- A comparison of an inverse image with an iterated inverse image along a factorization
`v = g ≫ p`, for an arbitrary proof of the factorization, is the transport along it followed by
the comparison at the composite itself. -/
theorem pullbackComparison_eq_eqToIso {A P T : AlgebraicSpaces B S hS} (g : T ⟶ P)
    (p : P ⟶ A) {v : T ⟶ A} (hv : g ≫ p = v) (M : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS g p v hv M =
      eqToIso (congrArg (fun q : T ⟶ A => (modulePullback B S hS q).obj M) hv.symm) ≪≫
        pullbackComparison B S hS g p (g ≫ p) rfl M := by
  subst hv
  simp

/-- `AlgebraicGeometry.Space.modulePullbackTriangle` at a module is the comparison of the inverse
image with the iterated inverse image. -/
theorem modulePullbackTriangle_app {A P T : AlgebraicSpaces B S hS} {g : T ⟶ P} {p : P ⟶ A}
    {v : T ⟶ A} (hv : g ≫ p = v) (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullbackTriangle B S hS hv).app M = pullbackComparison B S hS g p v hv M := by
  subst hv
  rw [pullbackComparison_rfl]
  ext
  simp [modulePullbackTriangle]

/-- Transporting the inverse image of a module along an equality of morphisms is natural in the
module. -/
theorem eqToIso_modulePullback_naturality {A P : AlgebraicSpaces B S hS} {p q : P ⟶ A}
    (hpq : p = q) {M N : Modules.{u, u} B S hS A.1 A.2} (φ : M ≅ N) :
    (modulePullback B S hS p).mapIso φ ≪≫
        eqToIso (congrArg (fun r : P ⟶ A => (modulePullback B S hS r).obj N) hpq) =
      eqToIso (congrArg (fun r : P ⟶ A => (modulePullback B S hS r).obj M) hpq) ≪≫
        (modulePullback B S hS q).mapIso φ := by
  subst hpq
  simp

/-- **The canonical comparison is natural in the module**, as an equation of isomorphisms. -/
theorem canonicalComparison_naturality_iso {A P Q R : AlgebraicSpaces B S hS} (a : P ⟶ Q)
    (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    {M N : Modules.{u, u} B S hS A.1 A.2} (φ : M ≅ N) :
    (modulePullback B S hS a).mapIso ((modulePullback B S hS fi).mapIso φ) ≪≫
        canonicalComparison a b fi fj h N =
      canonicalComparison a b fi fj h M ≪≫
        (modulePullback B S hS b).mapIso ((modulePullback B S hS fj).mapIso φ) := by
  have e1 := modulePullbackCompIso_mapIso B S hS a fi φ
  have e2 := modulePullbackCompIso_mapIso B S hS b fj φ
  have e3 := eqToIso_modulePullback_naturality h φ
  rw [canonicalComparison_eq, canonicalComparison_eq, ← Iso.trans_assoc, e1, Iso.trans_assoc,
    ← Iso.trans_assoc _ (eqToIso _), e3]
  have e2' : (modulePullback B S hS (b ≫ fj)).mapIso φ ≪≫
        ((modulePullbackCompIso B S hS b fj).app N).symm =
      ((modulePullbackCompIso B S hS b fj).app M).symm ≪≫
        (modulePullback B S hS b).mapIso ((modulePullback B S hS fj).mapIso φ) := by
    have := congrArg (fun i => ((modulePullbackCompIso B S hS b fj).app M).symm ≪≫ i ≪≫
      ((modulePullbackCompIso B S hS b fj).app N).symm) e2
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl, Iso.symm_self_id_assoc]
      using this.symm
  simp only [Iso.trans_assoc, e2']

/-- **The cocycle of the comparisons along two adjacent squares, with transition isomorphisms.**
Let `a ≫ eC = eA ≫ bg` and `a' ≫ eD = eC ≫ bh` be adjacent commutative squares, and let
`φn : bh^* LD ≅ LC` and `φm : bg^* LC ≅ LA` be isomorphisms of modules. The comparison
`a^* eC^* LC ≅ eA^* LA` of the left square followed by `φm`, preceded by the inverse image along
`a` of the comparison of the right square followed by `φn`, is the comparison of the outer square
followed by the composite transition `bgh^* LD ≅ bg^* bh^* LD ≅ bg^* LC ≅ LA`. The composites `v`,
`w` and `bgh` are arbitrary morphisms equal to the composites, so that the statement can be
instantiated at morphisms which are only propositionally composites. -/
theorem canonicalComparison_cocycle {PA PC PD XA XC XD : AlgebraicSpaces B S hS}
    (a : PA ⟶ PC) (a' : PC ⟶ PD) {v w : PA ⟶ PD} (hv : a ≫ a' = v) (hvw : v = w)
    (eA : PA ⟶ XA) (eC : PC ⟶ XC) (eD : PD ⟶ XD) (bg : XA ⟶ XC) (bh : XC ⟶ XD)
    {bgh : XA ⟶ XD} (hgh : bg ≫ bh = bgh) (hm : a ≫ eC = eA ≫ bg) (hn : a' ≫ eD = eC ≫ bh)
    (hw : w ≫ eD = eA ≫ bgh) {LA : Modules.{u, u} B S hS XA.1 XA.2}
    {LC : Modules.{u, u} B S hS XC.1 XC.2} (LD : Modules.{u, u} B S hS XD.1 XD.2)
    (φn : (modulePullback B S hS bh).obj LD ≅ LC) (φm : (modulePullback B S hS bg).obj LC ≅ LA) :
    pullbackComparison B S hS a a' v hv ((modulePullback B S hS eD).obj LD) ≪≫
        (modulePullback B S hS a).mapIso
          (canonicalComparison a' eC eD bh hn LD ≪≫ (modulePullback B S hS eC).mapIso φn) ≪≫
        canonicalComparison a eA eC bg hm LC ≪≫ (modulePullback B S hS eA).mapIso φm =
      eqToIso (congrArg (fun q : PA ⟶ PD =>
          (modulePullback B S hS q).obj ((modulePullback B S hS eD).obj LD)) hvw) ≪≫
        canonicalComparison w eA eD bgh hw LD ≪≫
        (modulePullback B S hS eA).mapIso
          (pullbackComparison B S hS bg bh bgh hgh LD ≪≫
            (modulePullback B S hS bg).mapIso φn ≪≫ φm) := by
  subst hv hvw hgh
  have hnat := canonicalComparison_naturality_iso a eA eC bg hm φn
  have hpaste := canonicalComparison_paste a a' eA eC eD bg bh hm hn hw LD
  simp only [Functor.mapIso_trans, Iso.trans_assoc, eqToIso_refl, Iso.refl_trans]
  rw [← Iso.trans_assoc ((modulePullback B S hS a).mapIso
      ((modulePullback B S hS eC).mapIso φn)), hnat]
  simp only [← Iso.trans_assoc] at hpaste ⊢
  rw [hpaste]

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
