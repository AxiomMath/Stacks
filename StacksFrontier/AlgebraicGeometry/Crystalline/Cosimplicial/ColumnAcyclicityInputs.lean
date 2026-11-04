module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedFormsShapeNatural
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedForms

/-!
# The inputs of `hcolumns`: the two shapes of the forms, cosimplicially, and [Stacks, Tag 07LA]
at `M(•)`

`...SmallSite.computes07LG_of_doubleComplex` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFromDoubleComplex.lean` proves
[Stacks, Proposition 60.21.3, Tag 07LG] from the double complex `K^{a,b}` and five carried
inputs.  One of them, `hcolumns`, is the acyclicity of the columns `K^{a,•}` for `a > 0`, and it
is [Stacks, Lemma 60.19.1, Tag 07LA] — which is proved, as
`Crystalline.id_completedTensorCompletedForms_homotopic_zero`, **in a different shape**: the
`Ω^i_{D(n)}` of that lemma is the `p`-adic completion of the `i`-th exterior power, formed over
the *completed* ring `D̂(n)`, of the *completed* differentials `Ω̂_{D(n)}`, whereas
`Crystalline.CosimplicialDPAlgebra.forms` — and therefore the columns of
`Crystalline.CosimplicialCompletedPair.doubleComplex`, and the target complex of
[Stacks, Tag 07LG] — is the completion of the exterior power, formed over the *uncompleted*
carrier, of the *uncompleted* differentials.

This module supplies the two things that identification needed, and instantiates
[Stacks, Tag 07LA] at the cosimplicial module `M(•)` of an arbitrary
`Crystalline.CosimplicialCompletedModule`.

## What is proved

* **The comparison of the two shapes is a map of cosimplicial modules.**
  `Crystalline.completedFormsShapeEquiv` compares the two shapes in a *single* degree.  Here it
  is instantiated at a `Crystalline.CosimplicialDPAlgebra` —
  `Crystalline.CosimplicialDPAlgebra.formsShapeEquiv` — and
  `Crystalline.CosimplicialDPAlgebra.formsShapeEquiv_formsMap` proves that it commutes with the
  cosimplicial transition maps, the uncompleted shape moving by
  `Crystalline.CosimplicialDPAlgebra.formsMap` and the completed shape by the newly formed
  `Crystalline.CosimplicialDPAlgebra.formsShapeMap`.  That is
  `Crystalline.completedFormsShapeEquiv_natural_of_completedMap` with its hypotheses discharged:
  `hΦ` is `Crystalline.mapDifferentialFormsOfDPMorphism_ιMulti`, `hΦc` is
  `ExteriorAlgebra.powMapₛₗ_ιMulti`, `hσc` is `Crystalline.adicCompletionRingMap_of` and `hψc` is
  `Crystalline.CosimplicialDPAlgebra.completedDifferentialsMap_of`.  The `p`-adic ideal of a
  completion is the image of the `p`-adic ideal of its base
  (`Crystalline.pAdicIdeal_map_algebraMap_adicCompletion`), and
  `Crystalline.adicCompletionIdealCongr` moves between the two spellings; it commutes with the
  completion of a semilinear map by `Crystalline.adicCompletionIdealCongr_mapₛₗ`.

* **The transition map of a degreewise exterior power is `ExteriorAlgebra.powMapₛₗ` of the
  transition map.**  `Crystalline.exteriorPowerFunctor_restrictₛₗ`, for every cosimplicial ring
  and every cosimplicial module over it.  This is the other input recorded under
  `hcolumns` in the module documentation of `Crystalline/Computes07LGFromDoubleComplex.lean`.

* **[Stacks, Tag 07LA] at `M(•)`.**  For a `Crystalline.CosimplicialCompletedModule` over
  `Crystalline.envelopeDPAlgebra` — the module half of the double complex of
  [Stacks, Tag 07LG], with no connection needed — `M(•)` is a cosimplicial module over the
  cosimplicial ring `Crystalline.cosimplicialEnvelopeRing`
  (`Crystalline.columnModule`; the two descriptions of `D(*)` agree on the nose, rings and
  transition maps alike), and
  `Crystalline.homotopic_id_columnTargetModule_zero` is [Stacks, Tag 07LA] read at it: for
  `a > 0` the identity of `M(•) ⊗̂_{D(•)} Ω^a_{D(•)}`, in the shape of that lemma, is homotopic to
  zero.

## Where `hcolumns` is finished

`hcolumns` itself is discharged one module later, in
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/ColumnAcyclicity.lean`: the degreewise
identification

`K^{a,b} = M(b) ⊗̂_{D̂(b)} Ω^a_{D(b)}  ≅  (M(•) ⊗̂_{D(•)} Ω^a_{D(•)})_b`

of `Crystalline.CosimplicialCompletedModule.column` with `Crystalline.columnTargetModule` is
`Crystalline.columnTargetIso` there, and
`Crystalline.isZero_homology_alternatingCofaceMapComplex_of_homotopic_id_zero` together with
`Crystalline.isZero_homology_alternatingCofaceMapComplex_of_iso` finish from
`Crystalline.homotopic_id_columnTargetModule_zero` below.

The obstruction that identification has to route around is a *spelling* one, and it is sharp.
The two sides name the same ring and the same module by different terms: the column uses
`Crystalline.CosimplicialDPAlgebra.completedRing`, i.e.
`AdicCompletion (pAdicIdeal p) (E.carrier b)` with the `CommRing` instance Mathlib's
`AdicCompletion` carries, while [Stacks, Tag 07LA] uses
`(Crystalline.cosimplicialEnvelopeRing s f hf).obj ⦋b⦌`, i.e. a `CommRingCat.of` whose instance
arrives through the bundled category.  The two are definitionally equal, and Lean checks it
cheaply for the rings themselves and for the differentials — but **not** inside an exterior
power: unifying `⋀[R]^a N` with `⋀[R']^a N'` for `R`, `R'` and `N`, `N'` two such spellings
exhausts the heartbeat limit, because it forces the unifier through the `TensorAlgebra` and
`CliffordAlgebra` quotients underlying `ExteriorAlgebra` (whose `ringCon` is sealed) in order to
reconcile the two `Module` instances.  So the identification cannot be written as a type
ascription in either spelling; it has to be routed through
`Crystalline.ExteriorPowerFunctor.componentIso`, whose naturality is the `transition_mk` field —
which is to say, through the general `Crystalline.exteriorPowerFunctor_restrictₛₗ` above, stated
as it is here in **one** spelling throughout, with the passage between spellings performed once,
on the rings and the differentials only, where it is affordable.

No `@[stacks 07LG]` and no `@[stacks 07LA]` attribute is placed: [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`, and [Stacks, Tag 07LA] carries its tag where it is
proved, in `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedForms.lean`; the
statement below is that lemma read at one cosimplicial module, not a second proof of it.

## Main definitions

* `Crystalline.adicCompletionIdealCongr` — an equality of ideals identifies the two adic
  completions.
* `Crystalline.CosimplicialDPAlgebra.completedDifferentials` and `...completedDifferentialsMap` —
  the completed differentials `Ω̂_{D(b)}` of a cosimplicial degree and their transition map.
* `Crystalline.CosimplicialDPAlgebra.formsShape` and `...formsShapeMap` — **the forms in the
  shape of [Stacks, Tag 07LA]**, and their transition map as `ExteriorAlgebra.powMapₛₗ` of the
  transition of the completed differentials.
* `Crystalline.CosimplicialDPAlgebra.formsShapeEquiv` — **the comparison of the two shapes**, in
  positive exterior degree, linear over `D̂(b)`.
* `Crystalline.columnModule` — `M(•)` as a cosimplicial module over `D(*)`.
* `Crystalline.columnFormsModule` and `Crystalline.columnTargetModule` — the forms and the whole
  of `M(•) ⊗̂_{D(•)} Ω^a_{D(•)}` in the shape of [Stacks, Tag 07LA].

## Main results

* `Crystalline.CosimplicialDPAlgebra.formsShapeEquiv_formsMap` — **the comparison of the two
  shapes is natural in the cosimplicial direction.**
* `Crystalline.exteriorPowerFunctor_restrictₛₗ` — **the transition map of a degreewise exterior
  power is `ExteriorAlgebra.powMapₛₗ` of the transition map.**
* `Crystalline.homotopic_id_columnTargetModule_zero` — **[Stacks, Tag 07LA] at `M(•)`.**

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers Opposite
open scoped TensorProduct

universe u v w

namespace Crystalline

/-! ### Transport of an adic completion along an equality of ideals -/

section IdealCongr

variable {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J)
  (M : Type*) [AddCommGroup M] [Module R M]

/-- An equality of ideals identifies the two adic completions, `R`-linearly. -/
def adicCompletionIdealCongr : AdicCompletion I M ≃ₗ[R] AdicCompletion J M := by
  subst h; exact LinearEquiv.refl _ _

/-- `adicCompletionIdealCongr` sends the image of `x` in the `I`-adic completion to its image in
the `J`-adic completion. -/
theorem adicCompletionIdealCongr_of (x : M) :
    adicCompletionIdealCongr h M (AdicCompletion.of I M x) = AdicCompletion.of J M x := by
  subst h; rfl

/-- The transport along an equality of ideals commutes with the completion of a semilinear
map. -/
theorem adicCompletionIdealCongr_mapₛₗ {R' : Type*} [CommRing R'] {I' J' : Ideal R'}
    (h' : I' = J') {σ : R →+* R'} {P Q : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R' Q] (g : P →ₛₗ[σ] Q) (hle : I.map σ ≤ I')
    (hle' : J.map σ ≤ J') (x : AdicCompletion I P) :
    adicCompletionIdealCongr h' Q (adicCompletionMapₛₗ g hle x) =
      adicCompletionMapₛₗ g hle' (adicCompletionIdealCongr h P x) := by
  subst h; subst h'; rfl

end IdealCongr

/-- The `p`-adic ideal of a `p`-adic completion is the image of the `p`-adic ideal of the
base. -/
theorem pAdicIdeal_map_algebraMap_adicCompletion (p : ℕ) (R : Type*) [CommRing R] :
    (pAdicIdeal (A := R) p).map
        (algebraMap R (AdicCompletion (pAdicIdeal (A := R) p) R)) =
      pAdicIdeal (A := AdicCompletion (pAdicIdeal (A := R) p) R) p := by
  simp [pAdicIdeal, Ideal.map_span, Set.image_singleton]

/-- The `p`-adic ideal is finitely generated. -/
theorem pAdicIdeal_fg_commRing (p : ℕ) (R : Type*) [CommRing R] : (pAdicIdeal (A := R) p).FG :=
  ⟨{(p : R)}, by simp [pAdicIdeal]⟩

/-! ### The transition map of a degreewise exterior power -/

/-- **The transition map of `⋀^a K_*` is `ExteriorAlgebra.powMapₛₗ` of the transition map of
`K_*`.**

Both are semilinear maps out of an exterior power, so by `ExteriorAlgebra.powMapₛₗ_ext` it is
enough that they agree on a wedge `ω₁ ∧ ⋯ ∧ ω_a`, where the left-hand side is the `transition_mk`
field of `Crystalline.ExteriorPowerFunctor` and the right-hand side is
`ExteriorAlgebra.powMapₛₗ_ιMulti`.

This is the step the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/Computes07LGFromDoubleComplex.lean` records as
outstanding under `hcolumns` — "the `ExteriorAlgebra.powMapₛₗ` of
`Crystalline.completedEnvelopeDifferentialsMap` on the completed side has still to be formed" —
and it is proved here for every cosimplicial ring and every cosimplicial module over it, hence in
particular at `Crystalline.cosimplicialEnvelopeDifferentials`, whose transition map **is**
`Crystalline.completedEnvelopeDifferentialsMap`. -/
theorem exteriorPowerFunctor_restrictₛₗ {A : CosimplicialObject CommRingCat.{u}}
    (K : CosimplicialModule A) (a : ℕ) {n m : SimplexCategory} (φ : n ⟶ m) :
    ((exteriorPowerFunctor A a).functor.obj K).restrictₛₗ φ.op.op =
      ExteriorAlgebra.powMapₛₗ a ((cosimplicialRingPresheaf A).map φ.op.op).hom
        (K.restrictₛₗ φ.op.op) :=
  ExteriorAlgebra.powMapₛₗ_ext fun v =>
    ((exteriorPowerFunctor A a).transition_mk K φ v).trans
      (ExteriorAlgebra.powMapₛₗ_ιMulti a ((cosimplicialRingPresheaf A).map φ.op.op).hom
        (K.restrictₛₗ φ.op.op) v).symm

/-! ### The two shapes of the forms of a cosimplicial divided power algebra -/

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-- **The transition map of the uncompleted divided power differentials** of a cosimplicial
family, semilinear over the transition of the carriers. -/
def differentialsMap {m n : SimplexCategory} (φ : m ⟶ n) :
    dividedPowerDifferentials (A := A) (E.dividedPowers m.len) →ₛₗ[(E.map φ).toRingHom]
      dividedPowerDifferentials (A := A) (E.dividedPowers n.len) :=
  mapDifferentialsOfDPMorphismₛₗ (A := A) (E.ideal m.len) (E.dividedPowers m.len)
    (E.dividedPowers n.len) (E.map φ) (E.map_isDPMorphism φ)

/-- **The completed differentials `Ω̂_{D(b)}`** of a cosimplicial degree: the `p`-adic completion
of the module of divided power differentials, which is the degree-one piece of the shape
[Stacks, Lemma 60.19.1, Tag 07LA] is stated in. -/
abbrev completedDifferentials (b : ℕ) : Type v :=
  AdicCompletion (pAdicIdeal (A := E.carrier b) p)
    (dividedPowerDifferentials (A := A) (E.dividedPowers b))

/-- **The transition map `Ω̂_{D(m)} → Ω̂_{D(n)}` of the completed differentials**, semilinear over
the transition map of the completed rings. -/
def completedDifferentialsMap {m n : SimplexCategory} (φ : m ⟶ n) :
    E.completedDifferentials p m.len →ₛₗ[E.completedRingMap p φ]
      E.completedDifferentials p n.len where
  toFun := adicCompletionMapₛₗ (E.differentialsMap φ) (map_pAdicIdeal_le p (E.map φ).toRingHom)
  map_add' := map_add _
  map_smul' := adicCompletionMapₛₗ_smul _ _

/-- On the image of an uncompleted differential, the transition map of the completed differentials
is the image of the transition map of the uncompleted ones. -/
theorem completedDifferentialsMap_of {m n : SimplexCategory} (φ : m ⟶ n)
    (y : dividedPowerDifferentials (A := A) (E.dividedPowers m.len)) :
    E.completedDifferentialsMap p φ (AdicCompletion.of _ _ y) =
      AdicCompletion.of _ _ (mapDifferentialsOfDPMorphism (A := A) (E.ideal m.len)
        (E.dividedPowers m.len) (E.dividedPowers n.len) (E.map φ) (E.map_isDPMorphism φ) y) :=
  adicCompletionMapₛₗ_of (E.differentialsMap φ) (map_pAdicIdeal_le p (E.map φ).toRingHom) y

/-- **The transition map of the forms is the completion of the comparison of the uncompleted
forms.**  This is the definition of `Crystalline.CosimplicialDPAlgebra.formsMap` unfolded one
step, in the shape `Crystalline.completedFormsShapeEquiv_natural_of_completedMap` consumes. -/
theorem formsMap_eq {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) (x : E.forms p a m.len) :
    E.formsMap p φ a x =
      adicCompletionMapₛₗ
        (mapDifferentialFormsOfDPMorphism (A := A) (E.ideal m.len) (E.dividedPowers m.len)
          (E.dividedPowers n.len) (E.map φ) (E.map_isDPMorphism φ) a)
        (map_pAdicIdeal_le p (E.map φ).toRingHom) x := rfl

/-- **The forms in the shape of [Stacks, Lemma 60.19.1, Tag 07LA]**: the `p`-adic completion of
the `a`-th exterior power, taken over the *completed* ring `D̂(b)`, of the *completed*
differentials `Ω̂_{D(b)}`. -/
abbrev formsShape (a b : ℕ) : Type v :=
  AdicCompletion (pAdicIdeal (A := E.completedRing p b) p)
    ↥(⋀[E.completedRing p b]^a (E.completedDifferentials p b))

/-- **The transition map of the forms in the shape of [Stacks, Tag 07LA]**: the completion of the
`a`-th exterior power of the transition of the completed differentials. -/
def formsShapeMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) :
    E.formsShape p a m.len →ₛₗ[E.completedRingMap p φ] E.formsShape p a n.len :=
  adicCompletionMapₛₗ
    (ExteriorAlgebra.powMapₛₗ a (E.completedRingMap p φ) (E.completedDifferentialsMap p φ))
    (map_pAdicIdeal_le p (E.completedRingMap p φ))

/-- **The two shapes of the forms agree**, in positive exterior degree, `D̂(b)`-linearly.  This is
`Crystalline.completedFormsShapeLinearEquiv` with the `p`-adic ideal of the completion written in
the shape the cosimplicial constructions use. -/
def formsShapeEquiv (a b : ℕ) (ha : 0 < a) :
    E.forms p a b ≃ₗ[E.completedRing p b] E.formsShape p a b :=
  (completedFormsShapeLinearEquiv (pAdicIdeal_fg_commRing p (E.carrier b)) a ha).trans
    (adicCompletionIdealCongr (pAdicIdeal_map_algebraMap_adicCompletion p (E.carrier b))
      ↥(⋀[E.completedRing p b]^a (E.completedDifferentials p b)))

/-- `formsShapeEquiv` unfolded: `Crystalline.completedFormsShapeEquiv` followed by the transport
along the equality of `p`-adic ideals. -/
theorem formsShapeEquiv_apply (a b : ℕ) (ha : 0 < a) (x : E.forms p a b) :
    E.formsShapeEquiv p a b ha x =
      adicCompletionIdealCongr (pAdicIdeal_map_algebraMap_adicCompletion p (E.carrier b))
        ↥(⋀[E.completedRing p b]^a (E.completedDifferentials p b))
        (completedFormsShapeEquiv (pAdicIdeal_fg_commRing p (E.carrier b)) a ha x) := rfl

/-- **The comparison of the two shapes is natural in the cosimplicial direction.**

This is `Crystalline.completedFormsShapeEquiv_natural_powMapₛₗ`: the transition of the
uncompleted shape is the completion of `ExteriorAlgebra.powMapₛₗ` of the map of the uncompleted
differentials, and the transition of the completed shape is the completion of
`ExteriorAlgebra.powMapₛₗ` of the completion of that same map. -/
theorem formsShapeEquiv_formsMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) (ha : 0 < a)
    (x : E.forms p a m.len) :
    E.formsShapeMap p φ a (E.formsShapeEquiv p a m.len ha x) =
      E.formsShapeEquiv p a n.len ha (E.formsMap p φ a x) := by
  have hsigma : ∀ r : E.carrier m.len,
      E.completedRingMap p φ (algebraMap (E.carrier m.len) (E.completedRing p m.len) r) =
        algebraMap (E.carrier n.len) (E.completedRing p n.len) ((E.map φ).toRingHom r) :=
    fun r => adicCompletionRingMap_of (E.map φ).toRingHom
      (map_pAdicIdeal_le p (E.map φ).toRingHom) r
  have hnat := completedFormsShapeEquiv_natural_of_completedMap
    (pAdicIdeal_fg_commRing p (E.carrier m.len)) (pAdicIdeal_fg_commRing p (E.carrier n.len)) ha
    (map_pAdicIdeal_le p (E.map φ).toRingHom) hsigma
    (Φ := mapDifferentialFormsOfDPMorphism (A := A) (E.ideal m.len) (E.dividedPowers m.len)
      (E.dividedPowers n.len) (E.map φ) (E.map_isDPMorphism φ) a)
    (ψ := mapDifferentialsOfDPMorphism (A := A) (E.ideal m.len) (E.dividedPowers m.len)
      (E.dividedPowers n.len) (E.map φ) (E.map_isDPMorphism φ))
    (Φc := ExteriorAlgebra.powMapₛₗ a (E.completedRingMap p φ) (E.completedDifferentialsMap p φ))
    (mapDifferentialFormsOfDPMorphism_ιMulti (A := A) (E.ideal m.len) (E.dividedPowers m.len)
      (E.dividedPowers n.len) (E.map φ) (E.map_isDPMorphism φ) a)
    (E.completedDifferentialsMap p φ) (fun y => E.completedDifferentialsMap_of p φ y)
    (ExteriorAlgebra.powMapₛₗ_ιMulti a (E.completedRingMap p φ)
      (E.completedDifferentialsMap p φ)) x
  exact (adicCompletionIdealCongr_mapₛₗ
    (pAdicIdeal_map_algebraMap_adicCompletion p (E.carrier m.len))
    (pAdicIdeal_map_algebraMap_adicCompletion p (E.carrier n.len))
    (ExteriorAlgebra.powMapₛₗ a (E.completedRingMap p φ) (E.completedDifferentialsMap p φ))
    (map_map_adicCompletion_le (map_pAdicIdeal_le p (E.map φ).toRingHom) hsigma)
    (map_pAdicIdeal_le p (E.completedRingMap p φ))
    (completedFormsShapeEquiv (pAdicIdeal_fg_commRing p (E.carrier m.len)) a ha x)).symm.trans
    (congrArg _ hnat)

end CosimplicialDPAlgebra

/-! ### The columns of the double complex, at the actual cosimplicial envelope -/

section Column

open AlgebraicTopology Simplicial

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)
  (W : CosimplicialCompletedModule.{u, max u w, max u w} (envelopeDPAlgebra s f) s.p)

/-- **The cosimplicial module `M(•)` as semilinear data over the cosimplicial ring `D(*)`** of
`Crystalline.cosimplicialEnvelopeRing`.  The two rings agree: the completed ring of the
cosimplicial divided power algebra `Crystalline.envelopeDPAlgebra` in degree `b` is the
`p`-adically completed envelope `D(b)`, and the two transition maps are the same completion of
the same reindexing morphism. -/
def columnSemilinearModule :
    SemilinearCosimplicialModule.{max u w, max u w} (cosimplicialEnvelopeRing s f hf) where
  obj n := W.carrier n.len
  addCommGroup _n := inferInstance
  module n := inferInstanceAs
    (Module ((envelopeDPAlgebra s f).completedRing s.p n.len) (W.carrier n.len))
  map φ := W.map φ
  map_id_apply n x := W.map_id_apply n x
  map_comp_apply φ ψ x := W.map_comp_apply φ ψ x

/-- `M(•)` as a cosimplicial module over `D(*)`, which is what [Stacks, Tag 07LA] quantifies
over. -/
def columnModule : CosimplicialModule (cosimplicialEnvelopeRing s f hf) :=
  (columnSemilinearModule s f hf W).toCosimplicialModule

/-- **The forms of [Stacks, Tag 07LA] as a cosimplicial module**: the degreewise `p`-adic
completion of the `a`-th exterior power of the completed differentials `Ω̂_{D(*)}`. -/
def columnFormsModule (a : ℕ) : CosimplicialModule (cosimplicialEnvelopeRing s f hf) :=
  (pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).completion
    ((exteriorPowerFunctor (cosimplicialEnvelopeRing s f hf) a).functor.obj
      (cosimplicialEnvelopeDifferentials s f hf))

/-- **The cosimplicial module [Stacks, Tag 07LA] proves null homotopic**:
`M(•) ⊗̂_{D(•)} Ω^a_{D(•)}` in the shape of that lemma. -/
def columnTargetModule (a : ℕ) : CosimplicialModule (cosimplicialEnvelopeRing s f hf) :=
  (pAdicCosimplicialIdeal (cosimplicialEnvelopeRing s f hf) s.p).completion
    (MonoidalCategory.tensorObj (columnModule s f hf W) (columnFormsModule s f hf a))

/-- **[Stacks, Lemma 60.19.1, Tag 07LA] at `M(•)`**: the identity of
`M(•) ⊗̂_{D(•)} Ω^a_{D(•)}` is homotopic to zero for `a > 0`. -/
theorem homotopic_id_columnTargetModule_zero (a : ℕ) (ha : 0 < a) :
    Homotopic (𝟙 (columnTargetModule s f hf W a)) 0 :=
  cosimplicialEnvelope_completedForms_homotopic_zero s f hf (columnModule s f hf W) (i := a) ha

end Column

end Crystalline

end
