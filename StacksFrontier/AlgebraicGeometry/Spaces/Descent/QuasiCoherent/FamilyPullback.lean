module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Canonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksFrontier.CategoryTheory.Sites.Hypercover.ZeroOver

/-!
# Pullback of quasi-coherent descent data along a morphism of families

Let `𝒰 = {U i ⟶ U}` and `𝒱 = {V j ⟶ V}` be families of morphisms of algebraic spaces with
fixed target and let `Φ = (g, s₀, h₀) : 𝒰 ⟶ 𝒱` be a morphism of such families in the sense of
Stacks 00VT, that is a morphism `g : U ⟶ V` of the targets, a map `s₀` of index sets and
morphisms `h₀ i : U i ⟶ V (s₀ i)` over `g`.  A descent datum `(F j, φ j j')` for quasi-coherent
modules relative to `𝒱` pulls back to the descent datum `((h₀ i)^*F (s₀ i), (h₀ i × h₀ i')^*φ)`
relative to `𝒰`, functorially in the datum, and two morphisms of families with the same `g`
give naturally isomorphic pullbacks.  This is Stacks 04W4.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.familyPairMap` is the morphism
  `U i ×_U U i' ⟶ V (s₀ i) ×_V V (s₀' i')` of pairwise fibre products induced by two morphisms
  of families, and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.comparisonPairMap` the morphism
  `U i ⟶ V (s₀ i) ×_V V (s₀' i)` induced by two morphisms of families over the same `g`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackTransition` is the pairwise isomorphism
  of the pulled-back descent datum.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackDatum` is **Stacks 04W4, part (1)**, the
  pulled-back descent datum, and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackFunctor` is **part (2)**, the functor it
  defines on the categories of descent data.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackCompare` is **part (3)**, the
  comparison isomorphism of the components of the two pulled-back data attached to two
  morphisms of families with the same morphism of targets.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison_naturality` and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_naturality`: the comparison of
  iterated inverse images, and a pairwise isomorphism read on a test space, are natural in the
  module and in the descent datum.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_pullbackTransition`: read on a test
  space, the pairwise isomorphism of the pulled-back datum is the pairwise isomorphism of the
  original datum read on that space through `h₀`.  This is what makes the cocycle condition of
  the pulled-back datum follow from that of the original.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackCompare_naturality` and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackCompare_datum_naturality` are the two
  halves of **part (3)** that `pullbackCompare` needs: its components commute with the pairwise
  isomorphisms of the two pulled-back data, and they are natural in the descent datum.

## Implementation notes

The morphism of families is `CategoryTheory.PreZeroHypercover.HomOver` of Stacks 00VT (1), and
a family of morphisms with fixed target is Mathlib's `CategoryTheory.PreZeroHypercover`, whose
fields are exactly the family `(Y i ⟶ X)` that
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum` is indexed by.

Everything below is unconditional.  Two inputs are used, and both are theorems of this
development: `AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, the associativity coherence
of the comparison of inverse images of Stacks 03LU, which enters through
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_pullbackTransition`, and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, which
is Stacks 03GA for an arbitrary morphism of algebraic spaces and which enters through the
quasi-coherence field of the pulled-back datum.

The source's notation `(g_i × g_{i'})^*φ` is read here as: pull `φ` back along the induced
morphism `familyPairMap` of pairwise fibre products, and transport through the comparisons of
iterated inverse images on either side.  Equivalently, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn_pullbackTransition`, it is the
pairwise isomorphism of the original datum read on `U i ×_U U i'` along the two composites with
the `h₀`.

Part (3) is proved by two applications of the cocycle condition of the original datum on the
test space `U i ×_U U i'`, which carries four morphisms to members of `𝒱` — the two `h₀` of
each of the two morphisms of families, composed with the two projections.  The morphism
`familyPairMap` is therefore defined for a *pair* of morphisms of families, so that the mixed
fibre product `V (s₀ i) ×_V V (s₀' i')` needed there is an instance of it.

Part (3) is recorded as the family of component isomorphisms `pullbackCompare` together with
the two compatibilities that make it an isomorphism of descent data natural in the datum, and
not as an `Iso` in `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.category`.  The
reason is `pullbackCompare` itself, and not the spelling of the field.

The compatibility field of a
`AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` out of `pullbackDatum` does ask
the kernel to reconcile `(pullbackDatum ...).F i` with `(modulePullback (h₀ i)).obj (D.F (s₀ i))`,
and those are definitionally equal by `pullbackDatum_F`.  That reconciliation is cheap:
`pullbackHom` below is a bare structure instance carrying exactly the same obligation, with its
below is a bare structure instance carrying exactly the same obligation, with its `naturality` field
discharged by `pullbackTransition_naturality` stated in the unfolded spelling, and the kernel closes
it in milliseconds.  So neither the mixed spelling nor the inverse-image functor is the obstruction.

What differs is the morphism in the `app` field.  `pullbackHom` supplies
`(modulePullback (h₀ i)).map (a.app (s₀ i))`, and every residual obligation is congruence on
syntactically identical subterms.  `pullbackCompare` instead comes from `comparisonPairMap`, which
is an `AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct ... |>.lift`, and whose reduct is
`CategoryTheory.Limits.getLimitCone`.  The elaborator declines to unfold that — it is not exposed —
so elaboration stays fast, but the kernel has no such protection and descends into the fibre-product
construction on the big fppf site.  Parameterising the statement does not help, because the
obligation is the closing `exact`, not the shape of the binders; and `rw` cannot replace it, since
there is no syntactic match.  Parts (1) and (2) contain `familyPairMap`, which is also a `lift`, and
check fine precisely because no obligation there needs the kernel to look inside it.

The three statements below carry exactly the data of the isomorphism of part (3) and never ask the
kernel to enter a `lift`.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W4](https://stacks.math.columbia.edu/tag/04W4)
* [Stacks Project, Tag 00VT](https://stacks.math.columbia.edu/tag/00VT)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v v'

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Naturality

/-- The comparison of an inverse image with an iterated inverse image along a factorization is
natural in the module. -/
theorem pullbackComparison_naturality {A P T : AlgebraicSpaces B S hS} (w : T ⟶ P) (p : P ⟶ A)
    (x : T ⟶ A) (hx : w ≫ p = x) {M N : Modules.{u, u} B S hS A.1 A.2} (a : M ⟶ N) :
    (modulePullback B S hS x).map a ≫ (pullbackComparison B S hS w p x hx N).hom =
      (pullbackComparison B S hS w p x hx M).hom ≫
        (modulePullback B S hS w).map ((modulePullback B S hS p).map a) := by
  subst hx
  simp only [pullbackComparison_rfl, Iso.symm_hom, Iso.app_inv]
  exact (modulePullbackCompIso B S hS w p).inv.naturality a

/-- The inverse of the comparison of an inverse image with an iterated inverse image along a
factorization is natural in the module. -/
theorem pullbackComparison_inv_naturality {A P T : AlgebraicSpaces B S hS} (w : T ⟶ P)
    (p : P ⟶ A) (x : T ⟶ A) (hx : w ≫ p = x) {M N : Modules.{u, u} B S hS A.1 A.2} (a : M ⟶ N) :
    (modulePullback B S hS w).map ((modulePullback B S hS p).map a) ≫
        (pullbackComparison B S hS w p x hx N).inv =
      (pullbackComparison B S hS w p x hx M).inv ≫ (modulePullback B S hS x).map a := by
  rw [Iso.comp_inv_eq, Category.assoc, pullbackComparison_naturality B S hS w p x hx a,
    Iso.inv_hom_id_assoc]

variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- A pairwise isomorphism of a descent datum, read on a test space, is natural in the descent
datum. -/
theorem transitionOn_naturality (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    {D E : DescentDatum B S hS Y f} (a : DescentDatum.Hom B S hS D E)
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) :
    (modulePullback B S hS vi).map (a.app i) ≫
        (transitionOn B S hS Y f E.F E.transition i j v vi vj hi hj).hom =
      (transitionOn B S hS Y f D.F D.transition i j v vi vj hi hj).hom ≫
        (modulePullback B S hS vj).map (a.app j) := by
  subst hi
  subst hj
  simp only [transitionOn, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, pullbackComparison_naturality, Category.assoc]
  congr 1
  rw [← Category.assoc, ← Functor.map_comp, a.naturality, Functor.map_comp, Category.assoc,
    pullbackComparison_inv_naturality]

end Naturality

section Family

variable {U V : AlgebraicSpaces B S hS} {𝒰 : PreZeroHypercover.{v} U}
  {𝒱 : PreZeroHypercover.{v'} V} {g : U ⟶ V}

/-- The two legs `U i ×_U U i' ⟶ V (s₀ i)` and `U i ×_U U i' ⟶ V (s₀' i')` built from two
morphisms of families have equal composites to `V`. -/
theorem familyPairMap_condition (Φ Ψ : 𝒰.HomOver 𝒱 g) (i j : 𝒰.I₀) :
    (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) ≫ 𝒱.f (Φ.s₀ i) =
      (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Ψ.h₀ j) ≫ 𝒱.f (Ψ.s₀ j) := by
  rw [Category.assoc, Category.assoc, Φ.w₀, Ψ.w₀, ← Category.assoc, ← Category.assoc,
    pair_condition B S hS 𝒰.X 𝒰.f i j]

/-- The morphism `U i ×_U U i' ⟶ V (s₀ i) ×_V V (s₀' i')` of pairwise fibre products whose two
projections are the two projections of the source followed by `h₀ i` and `h₀' i'`. -/
def familyPairMap (Φ Ψ : 𝒰.HomOver 𝒱 g) (i j : 𝒰.I₀) :
    pair B S hS 𝒰.X 𝒰.f i j ⟶ pair B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Ψ.s₀ j) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒱.f (Φ.s₀ i)) (𝒱.f (Ψ.s₀ j))).lift
    (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Ψ.h₀ j)
    (familyPairMap_condition B S hS Φ Ψ i j)

@[simp]
theorem familyPairMap_fst (Φ Ψ : 𝒰.HomOver 𝒱 g) (i j : 𝒰.I₀) :
    familyPairMap B S hS Φ Ψ i j ≫ pairFst B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Ψ.s₀ j) =
      pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒱.f (Φ.s₀ i)) (𝒱.f (Ψ.s₀ j))).lift_fst _ _ _

@[simp]
theorem familyPairMap_snd (Φ Ψ : 𝒰.HomOver 𝒱 g) (i j : 𝒰.I₀) :
    familyPairMap B S hS Φ Ψ i j ≫ pairSnd B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Ψ.s₀ j) =
      pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Ψ.h₀ j :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒱.f (Φ.s₀ i)) (𝒱.f (Ψ.s₀ j))).lift_snd _ _ _

/-- The morphism `U i ⟶ V (s₀ i) ×_V V (s₀' i)` determined by two morphisms of families over
the same morphism of targets. -/
def comparisonPairMap (Φ Ψ : 𝒰.HomOver 𝒱 g) (i : 𝒰.I₀) :
    𝒰.X i ⟶ pair B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Ψ.s₀ i) :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒱.f (Φ.s₀ i)) (𝒱.f (Ψ.s₀ i))).lift
    (Φ.h₀ i) (Ψ.h₀ i) (by rw [Φ.w₀, Ψ.w₀])

@[simp]
theorem comparisonPairMap_fst (Φ Ψ : 𝒰.HomOver 𝒱 g) (i : 𝒰.I₀) :
    comparisonPairMap B S hS Φ Ψ i ≫ pairFst B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Ψ.s₀ i) = Φ.h₀ i :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒱.f (Φ.s₀ i)) (𝒱.f (Ψ.s₀ i))).lift_fst _ _ _

@[simp]
theorem comparisonPairMap_snd (Φ Ψ : 𝒰.HomOver 𝒱 g) (i : 𝒰.I₀) :
    comparisonPairMap B S hS Φ Ψ i ≫ pairSnd B S hS 𝒱.X 𝒱.f (Φ.s₀ i) (Ψ.s₀ i) = Ψ.h₀ i :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS (𝒱.f (Φ.s₀ i)) (𝒱.f (Ψ.s₀ i))).lift_snd _ _ _

/-- The pairwise isomorphism of the pulled-back descent datum: the pairwise isomorphism of the
given datum, pulled back along the induced morphism of pairwise fibre products and read through
the comparisons of iterated inverse images on either side. -/
def pullbackTransition (Φ : 𝒰.HomOver 𝒱 g) (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).obj
        ((modulePullback B S hS (Φ.h₀ i)).obj (D.F (Φ.s₀ i))) ≅
      (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).obj
        ((modulePullback B S hS (Φ.h₀ j)).obj (D.F (Φ.s₀ j))) :=
  (pullbackComparison B S hS (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ i)
      (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) rfl (D.F (Φ.s₀ i))).symm ≪≫
    transitionOn B S hS 𝒱.X 𝒱.f D.F D.transition (Φ.s₀ i) (Φ.s₀ j)
      (familyPairMap B S hS Φ Φ i j) _ _ (familyPairMap_fst B S hS Φ Φ i j)
      (familyPairMap_snd B S hS Φ Φ i j) ≪≫
    pullbackComparison B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ j)
      (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) rfl (D.F (Φ.s₀ j))

/-- **The key coherence of Stacks 04W4, part (1).**  Read on a test space `T` mapping compatibly
to `U i` and `U i'`, the pairwise isomorphism of the pulled-back datum is the pairwise
isomorphism of the original datum read on `T` along the two composites with the `h₀`. -/
theorem transitionOn_pullbackTransition
    (Φ : 𝒰.HomOver 𝒱 g) (D : DescentDatum B S hS 𝒱.X 𝒱.f) {T : AlgebraicSpaces B S hS}
    (i j : 𝒰.I₀) (v : T ⟶ pair B S hS 𝒰.X 𝒰.f i j) (vi : T ⟶ 𝒰.X i) (vj : T ⟶ 𝒰.X j)
    (hi : v ≫ pairFst B S hS 𝒰.X 𝒰.f i j = vi)
    (hj : v ≫ pairSnd B S hS 𝒰.X 𝒰.f i j = vj) :
    transitionOn B S hS 𝒰.X 𝒰.f
        (fun t => (modulePullback B S hS (Φ.h₀ t)).obj (D.F (Φ.s₀ t)))
        (pullbackTransition B S hS Φ D) i j v vi vj hi hj =
      (pullbackComparison B S hS vi (Φ.h₀ i) (vi ≫ Φ.h₀ i) rfl (D.F (Φ.s₀ i))).symm ≪≫
        transitionOn B S hS 𝒱.X 𝒱.f D.F D.transition (Φ.s₀ i) (Φ.s₀ j)
          (v ≫ familyPairMap B S hS Φ Φ i j) (vi ≫ Φ.h₀ i) (vj ≫ Φ.h₀ j)
          (by rw [Category.assoc, familyPairMap_fst, ← hi, Category.assoc])
          (by rw [Category.assoc, familyPairMap_snd, ← hj, Category.assoc]) ≪≫
        pullbackComparison B S hS vj (Φ.h₀ j) (vj ≫ Φ.h₀ j) rfl (D.F (Φ.s₀ j)) := by
  have hassoc : ModulePullbackCompIsoAssoc B S hS := modulePullbackCompIsoAssoc B S hS
  subst hi
  subst hj
  rw [transitionOn, pullbackTransition]
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, transitionOn_comp B S hS,
    modulePullback_mapIso_compIso hassoc, Iso.trans_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, pullbackComparison_rfl, Iso.symm_self_id_assoc, Iso.symm_self_id,
    Iso.trans_refl]
  rfl

/-- The pulled-back pairwise isomorphisms are natural in the descent datum. -/
theorem pullbackTransition_naturality (Φ : 𝒰.HomOver 𝒱 g)
    {D E : DescentDatum B S hS 𝒱.X 𝒱.f} (a : D ⟶ E) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).map
          ((modulePullback B S hS (Φ.h₀ i)).map (a.app (Φ.s₀ i))) ≫
        (pullbackTransition B S hS Φ E i j).hom =
      (pullbackTransition B S hS Φ D i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).map
          ((modulePullback B S hS (Φ.h₀ j)).map (a.app (Φ.s₀ j))) := by
  have h1 := pullbackComparison_inv_naturality B S hS (pairFst B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ i)
    (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) rfl (a.app (Φ.s₀ i))
  have h2 := transitionOn_naturality B S hS 𝒱.X 𝒱.f a (Φ.s₀ i) (Φ.s₀ j)
    (familyPairMap B S hS Φ Φ i j) (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i)
    (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) (familyPairMap_fst B S hS Φ Φ i j)
    (familyPairMap_snd B S hS Φ Φ i j)
  have h3 := pullbackComparison_naturality B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j) (Φ.h₀ j)
    (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j) rfl (a.app (Φ.s₀ j))
  simp only [pullbackTransition, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    reassoc_of% h1, reassoc_of% h2, h3]

/-- The component modules of the pulled-back datum are quasi-coherent. -/
theorem isQuasicoherentOnSite_pullbackModule (Φ : 𝒰.HomOver 𝒱 g)
    (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i : 𝒰.I₀) :
    ((modulePullback B S hS (Φ.h₀ i)).obj (D.F (Φ.s₀ i))).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (Φ.h₀ i)
    (D.F (Φ.s₀ i)) (D.quasicoherent (Φ.s₀ i))

/-- The cocycle condition for the pulled-back pairwise isomorphisms, deduced from the cocycle
condition of the given datum read on the same test space along the `h₀`. -/
theorem pullbackTransition_cocycle
    (Φ : 𝒰.HomOver 𝒱 g) (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i j k : 𝒰.I₀)
    (T : AlgebraicSpaces B S hS) (vi : T ⟶ 𝒰.X i) (vj : T ⟶ 𝒰.X j) (vk : T ⟶ 𝒰.X k)
    (vij : T ⟶ pair B S hS 𝒰.X 𝒰.f i j) (vjk : T ⟶ pair B S hS 𝒰.X 𝒰.f j k)
    (vik : T ⟶ pair B S hS 𝒰.X 𝒰.f i k)
    (hij₀ : vij ≫ pairFst B S hS 𝒰.X 𝒰.f i j = vi)
    (hij₁ : vij ≫ pairSnd B S hS 𝒰.X 𝒰.f i j = vj)
    (hjk₀ : vjk ≫ pairFst B S hS 𝒰.X 𝒰.f j k = vj)
    (hjk₁ : vjk ≫ pairSnd B S hS 𝒰.X 𝒰.f j k = vk)
    (hik₀ : vik ≫ pairFst B S hS 𝒰.X 𝒰.f i k = vi)
    (hik₁ : vik ≫ pairSnd B S hS 𝒰.X 𝒰.f i k = vk) :
    transitionOn B S hS 𝒰.X 𝒰.f
          (fun t => (modulePullback B S hS (Φ.h₀ t)).obj (D.F (Φ.s₀ t)))
          (pullbackTransition B S hS Φ D) i j vij vi vj hij₀ hij₁ ≪≫
        transitionOn B S hS 𝒰.X 𝒰.f
          (fun t => (modulePullback B S hS (Φ.h₀ t)).obj (D.F (Φ.s₀ t)))
          (pullbackTransition B S hS Φ D) j k vjk vj vk hjk₀ hjk₁ =
      transitionOn B S hS 𝒰.X 𝒰.f
        (fun t => (modulePullback B S hS (Φ.h₀ t)).obj (D.F (Φ.s₀ t)))
        (pullbackTransition B S hS Φ D) i k vik vi vk hik₀ hik₁ := by
  rw [transitionOn_pullbackTransition B S hS Φ D i j vij vi vj hij₀ hij₁,
    transitionOn_pullbackTransition B S hS Φ D j k vjk vj vk hjk₀ hjk₁,
    transitionOn_pullbackTransition B S hS Φ D i k vik vi vk hik₀ hik₁]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [Iso.subst_trans₂ (D.cocycle (Φ.s₀ i) (Φ.s₀ j) (Φ.s₀ k) T (vi ≫ Φ.h₀ i) (vj ≫ Φ.h₀ j)
    (vk ≫ Φ.h₀ k) (vij ≫ familyPairMap B S hS Φ Φ i j) (vjk ≫ familyPairMap B S hS Φ Φ j k)
    (vik ≫ familyPairMap B S hS Φ Φ i k) _ _ _ _ _ _)]

/-- **Stacks 04W4, part (1).**  The pullback of a descent datum for quasi-coherent modules along
a morphism of families of morphisms with fixed target: the inverse images `(h₀ i)^*F (s₀ i)`,
with the pairwise isomorphisms of the given datum pulled back to the pairwise fibre products of
the source family. -/
@[stacks 04W4 "part (1)"]
def pullbackDatum (Φ : 𝒰.HomOver 𝒱 g)
    (D : DescentDatum B S hS 𝒱.X 𝒱.f) : DescentDatum B S hS 𝒰.X 𝒰.f where
  F i := (modulePullback B S hS (Φ.h₀ i)).obj (D.F (Φ.s₀ i))
  quasicoherent i := isQuasicoherentOnSite_pullbackModule B S hS Φ D i
  transition i j := pullbackTransition B S hS Φ D i j
  cocycle := pullbackTransition_cocycle B S hS Φ D

@[simp]
theorem pullbackDatum_F (Φ : 𝒰.HomOver 𝒱 g)
    (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i : 𝒰.I₀) :
    (pullbackDatum B S hS Φ D).F i =
      (modulePullback B S hS (Φ.h₀ i)).obj (D.F (Φ.s₀ i)) :=
  rfl

@[simp]
theorem pullbackDatum_transition (Φ : 𝒰.HomOver 𝒱 g)
    (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i j : 𝒰.I₀) :
    (pullbackDatum B S hS Φ D).transition i j = pullbackTransition B S hS Φ D i j :=
  rfl

/-- **Stacks 04W4, part (2).**  The action of pullback on a morphism of descent data: the
inverse images of its components. -/
def pullbackHom (Φ : 𝒰.HomOver 𝒱 g)
    {D E : DescentDatum B S hS 𝒱.X 𝒱.f} (a : D ⟶ E) :
    pullbackDatum B S hS Φ D ⟶ pullbackDatum B S hS Φ E where
  app i := (modulePullback B S hS (Φ.h₀ i)).map (a.app (Φ.s₀ i))
  naturality i j := pullbackTransition_naturality B S hS Φ a i j

@[simp]
theorem pullbackHom_app (Φ : 𝒰.HomOver 𝒱 g)
    {D E : DescentDatum B S hS 𝒱.X 𝒱.f} (a : D ⟶ E) (i : 𝒰.I₀) :
    (pullbackHom B S hS Φ a).app i =
      (modulePullback B S hS (Φ.h₀ i)).map (a.app (Φ.s₀ i)) :=
  rfl

/-- **Stacks 04W4, part (2).**  Pullback of descent data along a morphism of families of
morphisms with fixed target is a functor on the categories of descent data of Stacks 04W3. -/
@[stacks 04W4 "part (2)"]
def pullbackFunctor (Φ : 𝒰.HomOver 𝒱 g) :
    DescentDatum B S hS 𝒱.X 𝒱.f ⥤ DescentDatum B S hS 𝒰.X 𝒰.f where
  obj D := pullbackDatum B S hS Φ D
  map a := pullbackHom B S hS Φ a
  map_id D := DescentDatum.Hom.ext fun i =>
    (modulePullback B S hS (Φ.h₀ i)).map_id (D.F (Φ.s₀ i))
  map_comp a b := DescentDatum.Hom.ext fun i =>
    (modulePullback B S hS (Φ.h₀ i)).map_comp (a.app (Φ.s₀ i)) (b.app (Φ.s₀ i))

/-- **Stacks 04W4, part (3).**  For two morphisms of families with the same morphism of
targets, the pairwise isomorphism of the given datum read on `U i` along `h₀ i` and `h₀' i` is
an isomorphism of the `i`-th components of the two pulled-back data. -/
@[stacks 04W4 "part (3), the comparison isomorphism"]
def pullbackCompare (Φ Ψ : 𝒰.HomOver 𝒱 g) (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i : 𝒰.I₀) :
    (modulePullback B S hS (Φ.h₀ i)).obj (D.F (Φ.s₀ i)) ≅
      (modulePullback B S hS (Ψ.h₀ i)).obj (D.F (Ψ.s₀ i)) :=
  transitionOn B S hS 𝒱.X 𝒱.f D.F D.transition (Φ.s₀ i) (Ψ.s₀ i)
    (comparisonPairMap B S hS Φ Ψ i) (Φ.h₀ i) (Ψ.h₀ i)
    (comparisonPairMap_fst B S hS Φ Ψ i) (comparisonPairMap_snd B S hS Φ Ψ i)

/-- **Stacks 04W4, part (3).**  The components of `pullbackCompare` commute with the pairwise
isomorphisms of the two pulled-back data, so that they constitute a morphism of descent data:
two applications of the cocycle condition of the given datum on the test space `U i ×_U U j`,
which carries four morphisms to members of `𝒱`. -/
@[stacks 04W4 "part (3), compatibility of the comparison with the pairwise isomorphisms"]
theorem pullbackCompare_naturality
    (Φ Ψ : 𝒰.HomOver 𝒱 g) (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).mapIso
          (pullbackCompare B S hS Φ Ψ D i) ≪≫ pullbackTransition B S hS Ψ D i j =
      pullbackTransition B S hS Φ D i j ≪≫
        (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).mapIso
          (pullbackCompare B S hS Φ Ψ D j) := by
  have hassoc : ModulePullbackCompIsoAssoc B S hS := modulePullbackCompIsoAssoc B S hS
  have hmid := D.cocycle (Φ.s₀ i) (Ψ.s₀ i) (Ψ.s₀ j) (pair B S hS 𝒰.X 𝒰.f i j)
    (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Ψ.h₀ i)
    (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Ψ.h₀ j)
    (pairFst B S hS 𝒰.X 𝒰.f i j ≫ comparisonPairMap B S hS Φ Ψ i)
    (familyPairMap B S hS Ψ Ψ i j) (familyPairMap B S hS Φ Ψ i j)
    (by simp) (by simp) (familyPairMap_fst B S hS Ψ Ψ i j)
    (familyPairMap_snd B S hS Ψ Ψ i j) (familyPairMap_fst B S hS Φ Ψ i j)
    (familyPairMap_snd B S hS Φ Ψ i j)
  have hmid' := D.cocycle (Φ.s₀ i) (Φ.s₀ j) (Ψ.s₀ j) (pair B S hS 𝒰.X 𝒰.f i j)
    (pairFst B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ i) (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Φ.h₀ j)
    (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ Ψ.h₀ j)
    (familyPairMap B S hS Φ Φ i j)
    (pairSnd B S hS 𝒰.X 𝒰.f i j ≫ comparisonPairMap B S hS Φ Ψ j)
    (familyPairMap B S hS Φ Ψ i j)
    (familyPairMap_fst B S hS Φ Φ i j) (familyPairMap_snd B S hS Φ Φ i j)
    (by simp) (by simp) (familyPairMap_fst B S hS Φ Ψ i j)
    (familyPairMap_snd B S hS Φ Ψ i j)
  rw [pullbackCompare, pullbackCompare, pullbackTransition, pullbackTransition,
    transitionOn_comp B S hS, transitionOn_comp B S hS, pullbackComparison_rfl,
    pullbackComparison_rfl, pullbackComparison_rfl, pullbackComparison_rfl]
  simp only [Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [Iso.subst_trans₂ hmid, Iso.subst_trans₂ hmid']

/-- `pullbackCompare_naturality` on underlying morphisms. -/
theorem pullbackCompare_hom_naturality
    (Φ Ψ : 𝒰.HomOver 𝒱 g) (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i j : 𝒰.I₀) :
    (modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).map
          (pullbackCompare B S hS Φ Ψ D i).hom ≫ (pullbackTransition B S hS Ψ D i j).hom =
      (pullbackTransition B S hS Φ D i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).map
          (pullbackCompare B S hS Φ Ψ D j).hom := by
  have h := congrArg Iso.hom (pullbackCompare_naturality B S hS Φ Ψ D i j)
  simpa only [Iso.trans_hom, Functor.mapIso_hom] using h

/-- The inverse components of `pullbackCompare` commute with the pairwise isomorphisms of the
two pulled-back data. -/
theorem pullbackCompare_inv_naturality
    (Φ Ψ : 𝒰.HomOver 𝒱 g) (D : DescentDatum B S hS 𝒱.X 𝒱.f) (i j : 𝒰.I₀) :
    ((modulePullback B S hS (pairFst B S hS 𝒰.X 𝒰.f i j)).mapIso
          (pullbackCompare B S hS Φ Ψ D i)).inv ≫
        (pullbackTransition B S hS Φ D i j).hom =
      (pullbackTransition B S hS Ψ D i j).hom ≫
        ((modulePullback B S hS (pairSnd B S hS 𝒰.X 𝒰.f i j)).mapIso
          (pullbackCompare B S hS Φ Ψ D j)).inv := by
  have h := congrArg Iso.hom (pullbackCompare_naturality B S hS Φ Ψ D i j)
  simp only [Iso.trans_hom] at h
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Stacks 04W4, part (3).**  The comparison is natural in the descent datum: it commutes
with the components of the pulled-back morphisms, which are the components of
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackHom`. -/
@[stacks 04W4 "part (3), naturality of the comparison in the descent datum"]
theorem pullbackCompare_datum_naturality (Φ Ψ : 𝒰.HomOver 𝒱 g)
    {D E : DescentDatum B S hS 𝒱.X 𝒱.f} (a : D ⟶ E) (i : 𝒰.I₀) :
    (modulePullback B S hS (Φ.h₀ i)).map (a.app (Φ.s₀ i)) ≫
        (pullbackCompare B S hS Φ Ψ E i).hom =
      (pullbackCompare B S hS Φ Ψ D i).hom ≫
        (modulePullback B S hS (Ψ.h₀ i)).map (a.app (Ψ.s₀ i)) :=
  transitionOn_naturality B S hS 𝒱.X 𝒱.f a (Φ.s₀ i) (Ψ.s₀ i)
    (comparisonPairMap B S hS Φ Ψ i) (Φ.h₀ i) (Ψ.h₀ i)
    (comparisonPairMap_fst B S hS Φ Ψ i) (comparisonPairMap_snd B S hS Φ Ψ i)

end Family

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
