module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RefinementCanonical

/-!
# Readings of a quasi-coherent descent datum against a factorization of its family

Let `(f i : Y i ⟶ X)` be a family of algebraic spaces over `X` and suppose each `f i` factors as
`w i ≫ ρ` through one morphism `ρ : R ⟶ X`.  A descent datum for quasi-coherent modules relative
to `(f i)` then restricts to a descent datum relative to `(w i : Y i ⟶ R)`: the pairwise fibre
product `Y i ×_R Y j` maps to `Y i ×_X Y j` over the two projections, and the pairwise
isomorphism of the given datum read on it — `AlgebraicGeometry.Space.QuasiCoherentDescent`
`.transitionOn` — is the pairwise isomorphism of the restriction.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.pairOver` is the morphism
  `Y i ×_R Y j ⟶ Y i ×_X Y j` of pairwise fibre products.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.baseChangeTransition` and
  `…baseChangeDatum`: **the descent datum relative to `(w i : Y i ⟶ R)` restricted from a
  descent datum relative to `(w i ≫ ρ)`.**

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.modulePullback_mapIso_mapIso`,
  `…modulePullback_mapIso_pullbackComparison`, `…modulePullback_mapIso_canonicalComparison` and
  `…modulePullback_mapIso_transitionOn`: the inverse image along a further morphism of each of
  the comparisons of Stacks 03LU and 04W5, **with the legs of the result supplied as named
  morphisms** together with the equations identifying them with the composites.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_baseChangeTransition`: read on a
  test space, the pairwise isomorphism of the restricted datum is the pairwise isomorphism of
  the given datum read on that space.  This is what makes the cocycle condition of the
  restriction follow from that of the given datum.

## Implementation notes

Each of the four readings is stated with the legs of the result as *named* morphisms `x`, `y`
together with equations `q ≫ vi = x`, rather than as the composites themselves, following
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison`, which carries the transport
along such an equation inside itself.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The inverse images of the comparisons, with the legs of the result named -/

/-- The inverse image along `q` of the inverse image along `v` of an isomorphism of modules is
the inverse image along `x = q ≫ v` of that isomorphism, read through the comparison of
iterated inverse images of Stacks 03LU. -/
theorem modulePullback_mapIso_mapIso {P T T' : AlgebraicSpaces B S hS} (q : T' ⟶ T)
    (v : T ⟶ P) (x : T' ⟶ P) (hx : q ≫ v = x)
    {M M' : Modules.{u, u} B S hS P.1 P.2} (φ : M ≅ M') :
    (modulePullback B S hS q).mapIso ((modulePullback B S hS v).mapIso φ) =
      (pullbackComparison B S hS q v x hx M).symm ≪≫
        (modulePullback B S hS x).mapIso φ ≪≫
        pullbackComparison B S hS q v x hx M' := by
  subst hx
  simp only [pullbackComparison_rfl, Iso.symm_symm_eq]
  rw [← Iso.trans_assoc, ← modulePullbackCompIso_mapIso B S hS q v φ, Iso.trans_assoc,
    Iso.self_symm_id, Iso.trans_refl]

/-- The inverse image along `q` of the comparison of an inverse image with an iterated inverse
image is the comparison for the composites, read through two further comparisons. -/
theorem modulePullback_mapIso_pullbackComparison {A P T T' : AlgebraicSpaces B S hS}
    (q : T' ⟶ T) (a : T ⟶ P) (p : P ⟶ A) (x : T ⟶ A) (hx : a ≫ p = x)
    (a' : T' ⟶ P) (ha' : q ≫ a = a') (x' : T' ⟶ A) (hax : a' ≫ p = x')
    (hx' : q ≫ x = x') (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS q).mapIso (pullbackComparison B S hS a p x hx M) =
      (pullbackComparison B S hS q x x' hx' M).symm ≪≫
        pullbackComparison B S hS a' p x' hax M ≪≫
        pullbackComparison B S hS q a a' ha' ((modulePullback B S hS p).obj M) := by
  subst hx
  subst ha'
  subst hax
  rw [mapIso_pullbackComparison B S hS q a p M,
    show pullbackComparison B S hS q (a ≫ p) ((q ≫ a) ≫ p) hx' M =
      pullbackComparison B S hS q (a ≫ p) (q ≫ (a ≫ p)) rfl M from rfl]
  simp only [pullbackComparison_rfl, Iso.symm_symm_eq]

/-- The inverse image along `q` of the canonical comparison of two inverse images of Stacks 04W5
is the canonical comparison for the composites, read through the comparisons of iterated inverse
images on either side. -/
theorem modulePullback_mapIso_canonicalComparison {A P Q R T : AlgebraicSpaces B S hS}
    (q : T ⟶ P) (a : P ⟶ Q) (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A) (h : a ≫ fi = b ≫ fj)
    (x : T ⟶ Q) (y : T ⟶ R) (hx : q ≫ a = x) (hy : q ≫ b = y)
    (h' : x ≫ fi = y ≫ fj) (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS q).mapIso (canonicalComparison a b fi fj h M) =
      (pullbackComparison B S hS q a x hx ((modulePullback B S hS fi).obj M)).symm ≪≫
        canonicalComparison x y fi fj h' M ≪≫
        pullbackComparison B S hS q b y hy ((modulePullback B S hS fj).obj M) := by
  subst hx
  subst hy
  rw [← pair_coherence B S hS q a b fi fj h M]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id, Iso.trans_refl]

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- The inverse image along `q` of a pairwise isomorphism of a descent datum read on a test
space is that isomorphism read on the source of `q`, through the comparisons of iterated
inverse images on either side. -/
theorem modulePullback_mapIso_transitionOn (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j))
    {T T' : AlgebraicSpaces B S hS} (q : T' ⟶ T) (i j : I) (v : T ⟶ pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) (x : T' ⟶ Y i) (y : T' ⟶ Y j)
    (hx : q ≫ vi = x) (hy : q ≫ vj = y)
    (hi' : (q ≫ v) ≫ pairFst B S hS Y f i j = x)
    (hj' : (q ≫ v) ≫ pairSnd B S hS Y f i j = y) :
    (modulePullback B S hS q).mapIso (transitionOn B S hS Y f F φ i j v vi vj hi hj) =
      (pullbackComparison B S hS q vi x hx (F i)).symm ≪≫
        transitionOn B S hS Y f F φ i j (q ≫ v) x y hi' hj' ≪≫
        pullbackComparison B S hS q vj y hy (F j) := by
  subst hx
  subst hy
  rw [transitionOn_comp B S hS Y f F φ q i j v vi vj hi hj]
  simp only [pullbackComparison_rfl, Iso.symm_symm_eq]

/-! ### The base change of a descent datum along a factorization of its family -/

section BaseChange

variable {R : AlgebraicSpaces B S hS} (W : I → AlgebraicSpaces B S hS) (w : ∀ i, W i ⟶ R)
  (ρ : R ⟶ X)

/-- The two projections of `W i ×_R W j` have equal composites to `X` through `ρ`. -/
theorem pairOver_condition (i j : I) :
    pairFst B S hS W w i j ≫ (w i ≫ ρ) = pairSnd B S hS W w i j ≫ (w j ≫ ρ) := by
  rw [← Category.assoc, ← Category.assoc, pair_condition B S hS W w i j]

/-- The morphism `W i ×_R W j ⟶ W i ×_X W j` of pairwise fibre products attached to a
factorization `w i ≫ ρ` of the structure morphisms. -/
def pairOver (i j : I) :
    pair B S hS W w i j ⟶ pair B S hS W (fun t => w t ≫ ρ) i j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (w i ≫ ρ) (w j ≫ ρ)).lift
    (pairFst B S hS W w i j) (pairSnd B S hS W w i j) (pairOver_condition B S hS W w ρ i j)

/-- The morphism `W i ×_R W j ⟶ W i ×_X W j` is compatible with the first projections. -/
@[simp]
theorem pairOver_fst (i j : I) :
    pairOver B S hS W w ρ i j ≫ pairFst B S hS W (fun t => w t ≫ ρ) i j =
      pairFst B S hS W w i j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (w i ≫ ρ) (w j ≫ ρ)).lift_fst _ _ _

/-- The morphism `W i ×_R W j ⟶ W i ×_X W j` is compatible with the second projections. -/
@[simp]
theorem pairOver_snd (i j : I) :
    pairOver B S hS W w ρ i j ≫ pairSnd B S hS W (fun t => w t ≫ ρ) i j =
      pairSnd B S hS W w i j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (w i ≫ ρ) (w j ≫ ρ)).lift_snd _ _ _

/-- The pairwise isomorphism of the base change of a descent datum along a factorization of its
family: the given pairwise isomorphism read on `W i ×_R W j`. -/
def baseChangeTransition (D : DescentDatum B S hS W (fun t => w t ≫ ρ)) (i j : I) :
    (modulePullback B S hS (pairFst B S hS W w i j)).obj (D.F i) ≅
      (modulePullback B S hS (pairSnd B S hS W w i j)).obj (D.F j) :=
  transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition i j
    (pairOver B S hS W w ρ i j) (pairFst B S hS W w i j) (pairSnd B S hS W w i j)
    (pairOver_fst B S hS W w ρ i j) (pairOver_snd B S hS W w ρ i j)

/-- **Read on a test space, the pairwise isomorphism of the base change is the pairwise
isomorphism of the given datum read on that space.** -/
theorem transitionOn_baseChangeTransition (D : DescentDatum B S hS W (fun t => w t ≫ ρ))
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS W w i j)
    (vi : T ⟶ W i) (vj : T ⟶ W j) (hi : v ≫ pairFst B S hS W w i j = vi)
    (hj : v ≫ pairSnd B S hS W w i j = vj) :
    transitionOn B S hS W w D.F (baseChangeTransition B S hS W w ρ D) i j v vi vj hi hj =
      transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition i j
        (v ≫ pairOver B S hS W w ρ i j) vi vj
        (by rw [Category.assoc, pairOver_fst, hi]) (by rw [Category.assoc, pairOver_snd, hj]) := by
  subst hi
  subst hj
  rw [transitionOn, baseChangeTransition,
    modulePullback_mapIso_transitionOn B S hS W (fun t => w t ≫ ρ) D.F D.transition v i j
      (pairOver B S hS W w ρ i j) (pairFst B S hS W w i j) (pairSnd B S hS W w i j)
      (pairOver_fst B S hS W w ρ i j) (pairOver_snd B S hS W w ρ i j)
      (v ≫ pairFst B S hS W w i j) (v ≫ pairSnd B S hS W w i j) rfl rfl
      (by simp) (by simp)]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.trans_refl]

/-- **The base change of a descent datum along a factorization of its family**: a descent datum
for quasi-coherent modules relative to `(w i ≫ ρ : W i ⟶ X)` is a descent datum relative to
`(w i : W i ⟶ R)`, with the same component modules and with the pairwise isomorphisms read on
the pairwise fibre products over `R`. -/
def baseChangeDatum (D : DescentDatum B S hS W (fun t => w t ≫ ρ)) :
    DescentDatum B S hS W w where
  F := D.F
  quasicoherent := D.quasicoherent
  transition := baseChangeTransition B S hS W w ρ D
  cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ := by
    rw [transitionOn_baseChangeTransition B S hS W w ρ D i j vij vi vj hij₀ hij₁,
      transitionOn_baseChangeTransition B S hS W w ρ D j k vjk vj vk hjk₀ hjk₁,
      transitionOn_baseChangeTransition B S hS W w ρ D i k vik vi vk hik₀ hik₁]
    exact D.cocycle i j k T vi vj vk _ _ _ _ _ _ _ _ _

/-- The base change of a descent datum has the same component modules. -/
@[simp]
theorem baseChangeDatum_F (D : DescentDatum B S hS W (fun t => w t ≫ ρ)) (i : I) :
    (baseChangeDatum B S hS W w ρ D).F i = D.F i :=
  rfl

/-- The pairwise isomorphisms of the base change of a descent datum are the given pairwise
isomorphisms read on the pairwise fibre products over `R`. -/
@[simp]
theorem baseChangeDatum_transition (D : DescentDatum B S hS W (fun t => w t ≫ ρ)) (i j : I) :
    (baseChangeDatum B S hS W w ρ D).transition i j = baseChangeTransition B S hS W w ρ D i j :=
  rfl

end BaseChange

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
