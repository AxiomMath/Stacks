module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# The coherences behind the canonical descent datum of a quasi-coherent module

Let `X` be an algebraic space over `S`, let `(f i : Y i ⟶ X)` be a family of algebraic spaces
over it and let `M` be a quasi-coherent `𝒪_X`-module.  The inverse images `(f i)^*M` carry a
descent datum relative to the family whose pairwise isomorphism is the canonical comparison of
the two inverse images of `M` to `Y i ×_X Y j`; this is the canonical descent datum
`(M|_{Y i}, can)` of Stacks 04W5.  This file proves the coherences that datum rests on; the
datum itself, the trivial descent datum and effectivity are in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/CanonicalDatum.lean`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_canonicalComparison`: read on a
  test space, the pairwise isomorphism of the canonical descent datum is again the canonical
  comparison of the two inverse images.  This is what makes the cocycle condition hold.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.canonicalComparison_trans`: the canonical
  comparisons of three inverse images of one module compose.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_comp`: a pairwise isomorphism of
  an arbitrary descent datum, read on a test space and then pulled back further, is the same
  isomorphism read on the second test space.

## Implementation notes

Everything here is unconditional.  The one input is
`AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`, the associativity coherence of the
comparison of inverse images of Stacks 03LU, which enters through
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_mapIso_compIso` and is supplied by
`AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`.

Quasi-coherence of the inverse images, Stacks 03GA, is *not* used here.  It is needed only to
form the descent datum, and that is why the datum lives in its own module: Stacks 03GA for an
arbitrary morphism carries the affine chart diagram machinery, and the statements below are
used by files that have no business importing it.

Every statement below is an equality of *isomorphisms*, never of their underlying morphisms:
the comparison of inverse images transports along an equality of morphisms of algebraic spaces,
and the kernel does not finish checking a proof that projects such an isomorphism to its
components.  The two lemmas in `CategoryTheory.Iso` substitute a composite of two or three
isomorphisms inside a longer composite, and
`AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullbackCompIso_mapIso` reads naturality of
the comparison between isomorphisms; together they are what replaces `CategoryTheory.Iso.ext`
here.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Iso

universe v u

variable {C : Type u} [Category.{v} C]

/-- Replacing the first two factors of a composite of three isomorphisms by an isomorphism they
compose to. -/
theorem subst_trans₂ {W X Y Z : C} {e₁ : W ≅ X} {e₂ : X ≅ Y} {g : W ≅ Y} (h : e₁ ≪≫ e₂ = g)
    (e : Y ≅ Z) : e₁ ≪≫ e₂ ≪≫ e = g ≪≫ e := by
  rw [← h, Iso.trans_assoc]

/-- Replacing the first three factors of a composite of four isomorphisms by an isomorphism
they compose to. -/
theorem subst_trans₃ {W X Y Z V : C} {e₁ : W ≅ X} {e₂ : X ≅ Y} {e₃ : Y ≅ Z} {g : W ≅ Z}
    (h : e₁ ≪≫ e₂ ≪≫ e₃ = g) (e : Z ≅ V) : e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e = g ≪≫ e := by
  rw [← h]
  simp only [Iso.trans_assoc]

end CategoryTheory.Iso

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- The two projections of the pairwise fibre product `Y i ×_X Y j` have equal composites to
`X`. -/
theorem pair_condition (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (i j : I) :
    pairFst B S hS Y f i j ≫ f i = pairSnd B S hS Y f i j ≫ f j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (f i) (f j)).w

/-- The canonical comparisons of the inverse images of a module along three morphisms with equal
composites to its base compose: the comparison from the first to the second followed by the one
from the second to the third is the one from the first to the third. -/
theorem canonicalComparison_trans {A P Q R T : AlgebraicSpaces B S hS}
    (a : P ⟶ Q) (b : P ⟶ R) (c : P ⟶ T) (fi : Q ⟶ A) (fj : R ⟶ A) (fk : T ⟶ A)
    (h : a ≫ fi = b ≫ fj) (h' : b ≫ fj = c ≫ fk) (M : Modules.{u, u} B S hS A.1 A.2) :
    canonicalComparison a b fi fj h M ≪≫ canonicalComparison b c fj fk h' M =
      canonicalComparison a c fi fk (h.trans h') M := by
  rw [canonicalComparison_eq, canonicalComparison_eq, canonicalComparison_eq]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [Iso.subst_trans₂ (eqToIso_trans _ _)]

/-- The canonical comparison of two inverse images of a module, pulled back along a further
morphism `v` and read through the comparisons of iterated inverse images, is the canonical
comparison for the two composites with `v`. -/
theorem pair_coherence
    {A P Q R T : AlgebraicSpaces B S hS} (v : T ⟶ P) (a : P ⟶ Q) (b : P ⟶ R)
    (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj) (M : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS v a (v ≫ a) rfl ((modulePullback B S hS fi).obj M) ≪≫
        (modulePullback B S hS v).mapIso (canonicalComparison a b fi fj h M) ≪≫
        (pullbackComparison B S hS v b (v ≫ b) rfl
          ((modulePullback B S hS fj).obj M)).symm =
      canonicalComparison (v ≫ a) (v ≫ b) fi fj
        (by rw [Category.assoc, Category.assoc, h]) M := by
  rw [canonicalComparison_eq, canonicalComparison_eq, pullbackComparison_rfl,
    pullbackComparison_rfl, Iso.symm_symm_eq]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm,
    modulePullback_mapIso_compIso (modulePullbackCompIsoAssoc B S hS),
    Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.symm_self_id, Iso.trans_refl]
  rw [Iso.subst_trans₃ (modulePullbackCompIso_eqToIso v h M)]

/-- The inverse image along `w` of the comparison of an inverse image along `v` with the
iterated inverse image along a factorization `v = g ≫ p`, read through the comparisons for
`w`. -/
theorem mapIso_pullbackComparison
    {A P T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T) (v : T ⟶ P) (p : P ⟶ A)
    (N : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS w).mapIso (pullbackComparison B S hS v p (v ≫ p) rfl N) =
      (modulePullbackCompIso B S hS w (v ≫ p)).app N ≪≫
        pullbackComparison B S hS (w ≫ v) p ((w ≫ v) ≫ p) rfl N ≪≫
        ((modulePullbackCompIso B S hS w v).app ((modulePullback B S hS p).obj N)).symm := by
  rw [pullbackComparison_rfl, pullbackComparison_rfl, Functor.mapIso_symm,
    modulePullback_mapIso_compIso (modulePullbackCompIsoAssoc B S hS) w v p N]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]

/-- Naturality of the comparison of iterated inverse images of Stacks 03LU in the module. -/
theorem modulePullbackCompIso_mapIso {P T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T) (v : T ⟶ P)
    {N N' : Modules.{u, u} B S hS P.1 P.2} (φ : N ≅ N') :
    (modulePullback B S hS w).mapIso ((modulePullback B S hS v).mapIso φ) ≪≫
        (modulePullbackCompIso B S hS w v).app N' =
      (modulePullbackCompIso B S hS w v).app N ≪≫
        (modulePullback B S hS (w ≫ v)).mapIso φ :=
  Iso.ext ((modulePullbackCompIso B S hS w v).hom.naturality φ.hom)

/-- A pairwise isomorphism of a descent datum, read on a test space `T` and then pulled back
along a morphism `w` into `T`, is that isomorphism read on the source of `w`. -/
theorem transitionOn_comp
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j))
    {T T' : AlgebraicSpaces B S hS} (w : T' ⟶ T) (i j : I) (v : T ⟶ pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) :
    (modulePullback B S hS w).mapIso (transitionOn B S hS Y f F φ i j v vi vj hi hj) =
      (modulePullbackCompIso B S hS w vi).app (F i) ≪≫
        transitionOn B S hS Y f F φ i j (w ≫ v) (w ≫ vi) (w ≫ vj)
          (by rw [← hi, Category.assoc]) (by rw [← hj, Category.assoc]) ≪≫
        ((modulePullbackCompIso B S hS w vj).app (F j)).symm := by
  subst hi
  subst hj
  rw [transitionOn, transitionOn]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm,
    mapIso_pullbackComparison B S hS w v, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc]
  rw [Iso.subst_trans₂ (modulePullbackCompIso_mapIso B S hS w v (φ i j))]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  rfl

/-- Read on a test space `T` mapping compatibly to `Y i` and `Y j`, the pairwise isomorphism
built from the canonical comparison is the canonical comparison of the two inverse images of
`M` along the two morphisms out of `T`. -/
theorem transitionOn_canonicalComparison
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2)
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) :
    transitionOn B S hS Y f (fun t => (modulePullback B S hS (f t)).obj M)
        (fun s t => canonicalComparison (pairFst B S hS Y f s t) (pairSnd B S hS Y f s t)
          (f s) (f t) (pair_condition B S hS Y f s t) M) i j v vi vj hi hj =
      canonicalComparison vi vj (f i) (f j)
        (by rw [← hi, ← hj, Category.assoc, Category.assoc,
          pair_condition B S hS Y f i j]) M := by
  subst hi
  subst hj
  exact pair_coherence B S hS v _ _ (f i) (f j) _ M

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
