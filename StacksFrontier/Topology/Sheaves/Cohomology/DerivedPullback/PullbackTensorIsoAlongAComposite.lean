module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorOnModels

/-!
# The pullback-tensor comparison along a composite

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` is the comparison of
Stacks 079U,

`Lf^*(K ⊗^L_{𝒪_Y} L) ≅ Lf^*K ⊗^L_{𝒪_X} Lf^*L`.

This file assembles what the composition law for that comparison is proved from: the abstract
diagram chase, and the identification of the comparison on K-flat representatives in the
inverse-free form that chase consumes.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.tensorComparison_comp_of_models`: **the abstract
  assembly lemma.**  For functors `Pg : CZ ⥤ CY`, `Pf : CY ⥤ CX`, `Ph : CZ ⥤ CX` with a
  comparison `c : Pg ⋙ Pf ⟶ Ph`, bifunctors `TZ, TY, TX` and comparisons
  `tg : TZ ⋙ Pg ⟶ Pg.prod Pg ⋙ TY` and likewise `tf`, `th`, the identity
  `c ≫ th = Pf(tg) ≫ tf ≫ TX(c, c)` holds at a pair of objects as soon as a *model* for that
  pair satisfies the nine identities listed there.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_comp_rightComparison`:
  at a pair of K-flat complexes, Stacks 079U followed by the right comparison is the left
  comparison.  This is the keystone
  `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_of_kFlat` with the
  inverse that `Stacks.Cohomology.DerivedPullbackTensor.modelComparison` carries cancelled.
* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_comp_derivedToTensor`:
  the same identity written out — Stacks 079U, then the derived pullback of each tensor factor
  and the canonical map to the ordinary total tensor complex on `X`, is the canonical map on
  `Y`, then the derived pullback of a complex, then the comparison of total complexes of
  Stacks 01CD.  This is the shape the abstract chase consumes, and no inverse is left in it.
* `Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedToTensorNatTrans_app`,
  `Stacks.Cohomology.DerivedPullbackTensor.mono_derivedTensor_map_derivedPullbackNatTrans_app`
  and
  `Stacks.Cohomology.DerivedPullbackTensor.mono_derivedToTensorNatTrans_app_pullbackComplex`:
  the two monomorphisms the abstract chase cancels, at a pair of K-flat complexes.

## Implementation notes

*Why this is not already available.*  Nothing in the tree states any compatibility of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso` with composition of
morphisms of ringed spaces; the comparison is constructed for one morphism at a time by
descending `Stacks.Cohomology.DerivedPullbackTensor.modelComparison` along the localization of
pairs of K-flat objects, and `CategoryTheory.Localization.liftNatIso` records nothing about how
two such descents interact.

*Why the chase is carried out abstractly.*  `tensorComparison_comp_of_models` states the chase
for arbitrary categories, bifunctors, functors and transformations of the right shapes.  The
concrete functors are derived functors on derived categories of sheaves of modules, where `rw`
has to unfold reducible abbreviations in order to build a rewrite motive and the resulting
motive is not type-correct at `implicit` transparency; at the abstract statement every term is
small and the chase is seven rewrites.

*Where the inverses go.*  `Stacks.Cohomology.DerivedPullbackTensor.modelComparison` is
`asIso (leftComparison …) ≪≫ (asIso (rightComparison …)).symm`, so the keystone
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_of_kFlat` presents the
component of Stacks 079U with an inverse in it, and a chase fed those components directly would
carry inverses on both sides of the identity it is proving.  The two results above remove them
once and for all: postcomposing the component with the right comparison cancels that inverse
(`trans_symm_hom_comp`), and postcomposing further with the comparison of total complexes
cancels the inverse the right comparison itself ends with (`comp_eq_of_comp_inv`).  Both
cancellations are abstract lemmas applied by unification through `exact`, so no rewrite motive
is ever abstracted out of the concrete terms, and both are stated at exactly the bracketing the
unfolded comparisons carry: composition is associative only up to a propositional equality, so
a cancellation lemma whose brackets differ from the goal's is not applicable by unification at
all.

*What is not here: the composition law itself.*  Instantiating
`tensorComparison_comp_of_models` at `f` and `g`, at a pair `(QK, QL)` of K-flat
representatives, is a single `exact` whose fourteen arguments are: the two monomorphisms above;
the three instances of `derivedPullbackTensorIso_hom_app_comp_derivedToTensor`, at `g`, at `f`
(for the degreewise pullbacks `g^*K`, `g^*L`, which are K-flat by
`Stacks.SheafOfModules.KFlatPullback.kFlat_modulePullback_unconditional`) and at `f ≫ g`; three
instances of `derivedPullbackCompIsoCanonical_hom_app_comp_derivedPullbackNatTrans` in this
namespace, at `K`, at `L` and at the total tensor complex; naturality of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackNatTrans` along the comparison of total
complexes for `g`; naturality of
`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans` along the composition law for
pullback of complexes; and
`Stacks.PullbackTensorComposition.pullbackTensorComplexNatIso_comp` carried along
`DerivedCategory.Q`.  Descending from there to arbitrary objects of `D(𝒪_Z)` is
`Stacks.Cohomology.DerivedPullbackTensor.natTrans_ext_of_kFlat`, applied to the two sides read
as transformations `TZ ⋙ Pg ⋙ Pf ⟶ Ph.prod Ph ⋙ TX`.

That `exact` elaborates, but not within the heartbeat budget this library is held to, and no
splitting of it helps.  Merely *instantiating* the three model identities costs upwards of two
hundred thousand heartbeats on its own: each of their statements mentions
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair` and
`Stacks.Cohomology.DerivedPullbackTensor.pullbackTensorComplexNatIso`, and every mention of
either costs some twenty thousand in instance synthesis alone.  Splitting the chase into halves
does not help either, because an intermediate statement naming the model has to mention the
same terms.  What is needed is a presentation of the models in a vocabulary whose terms are
cheap to elaborate — `derivedPullbackTensorIso_hom_app_comp_rightComparison` is one such
statement, and a chase phrased against `Stacks.Cohomology.DerivedPullbackTensor.leftComparison`
and `Stacks.Cohomology.DerivedPullbackTensor.rightComparison` throughout would be another —
not more of the chase.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules.KFlatPullback (kFlat_modulePullback_unconditional)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedPullbackTensor

universe u

/-! ### The two cancellations, and the abstract chase -/

/-- Postcomposing `asIso l ≪≫ (asIso r).symm` with `r` returns `l`.  Stated abstractly and
applied by unification: in the concrete goal below `r` is a component of a transformation of
derived functors, and a rewrite motive abstracting it is not type-correct at `implicit`
transparency. -/
private lemma trans_symm_hom_comp {C : Type*} [Category C] {V W Z : C} (l : V ⟶ Z) (r : W ⟶ Z)
    [IsIso l] [IsIso r] : (asIso l ≪≫ (asIso r).symm).hom ≫ r = l := by
  change (l ≫ inv r) ≫ r = l
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- Cancelling an isomorphism against its inverse at the end of a composite of four factors,
and reassociating the other side.  Stated at exactly the two bracketings the concrete terms
carry, since composition is associative only up to a propositional equality and a cancellation
whose brackets differ from the goal's is not applicable by unification. -/
lemma comp_eq_of_comp_inv {C : Type*} [Category C] {V W Z₁ Z₂ Z₃ Z₄ : C}
    (p : V ⟶ W) (q : W ⟶ Z₁) (r : Z₁ ⟶ Z₂) (i : Z₂ ⟶ Z₃) (h : Z₃ ⟶ Z₂)
    (l₁ : V ⟶ Z₄) (l₂ : Z₄ ⟶ Z₃)
    (hih : i ≫ h = 𝟙 Z₂) (hkey : p ≫ q ≫ r ≫ i = l₁ ≫ l₂) :
    p ≫ q ≫ r = l₁ ≫ l₂ ≫ h := by
  have hcancel : (p ≫ q ≫ r ≫ i) ≫ h = p ≫ q ≫ r := by
    rw [Category.assoc, Category.assoc, Category.assoc, hih, Category.comp_id]
  rw [← hcancel, hkey, Category.assoc]

/-- **The abstract assembly lemma: a comparison of a tensor product with the tensor product of
the images is compatible with composition as soon as the three models are.**

Three categories `CZ, CY, CX` with bifunctors `TZ, TY, TX` on them; functors `Pg : CZ ⥤ CY`,
`Pf : CY ⥤ CX`, `Ph : CZ ⥤ CX` with a comparison `c : Pg ⋙ Pf ⟶ Ph`; and comparisons
`tg, tf, th` of each of the three with the tensor products, of the shape
`TZ ⋙ Pg ⟶ Pg.prod Pg ⋙ TY`.

Fix two objects `A, B` of `CZ`.  A *model* for the pair consists of an object `MZ` with a map
`s : TZ.obj (A, B) ⟶ MZ`; resolutions `a, b` of `A, B` along `Pg`, `a', b'` along `Pf` and
`a'', b''` along `Ph`, with comparisons `κ, κ'` between the last two; resolutions `m, m₀, m''`
of `MZ`, with comparison `κM`; transports `β, β₀, β', β''`; and maps `cmpY, cmpX, cmpX'` out of
the three tensor products, with comparison `κT`.  The identities asked for are: the composition
law for the resolutions at `A`, at `B` and at `MZ` (`hA`, `hB`, `hM`); naturality of the
resolution along `Pf` at the transport `β` (`hν`); naturality of `cmp` at `κ, κ'` (`hcmp`); the
model identity for each of `tg`, `tf`, `th` (`hg`, `hf`, `hh`); and the composition law for the
transports (`hβ`).

Then `c` carries `th` to `tg`, followed by `tf`, followed by `c` in each tensor factor.

Both sides become maps into the model for `th` after postcomposition with
`TX.map (a'' ×ₘ b'') ≫ cmpX'`, which is a monomorphism, so the identity is proved by cancelling
it.  After that `hh` replaces the left side by the model; `hcmp`, naturality of `tf` and `hf`
replace the right side by the model for `f`, and `hg` by the model for `g`; and `hν`, naturality
of `c`, `hM` and `hβ` identify the two. -/
theorem tensorComparison_comp_of_models
    {CZ CY CX : Type*} [Category CZ] [Category CY] [Category CX]
    {TZ : CZ × CZ ⥤ CZ} {TY : CY × CY ⥤ CY} {TX : CX × CX ⥤ CX}
    {Pg : CZ ⥤ CY} {Pf : CY ⥤ CX} {Ph : CZ ⥤ CX}
    (c : Pg ⋙ Pf ⟶ Ph)
    (tg : TZ ⋙ Pg ⟶ Pg.prod Pg ⋙ TY) (tf : TY ⋙ Pf ⟶ Pf.prod Pf ⋙ TX)
    (th : TZ ⋙ Ph ⟶ Ph.prod Ph ⋙ TX)
    (A B : CZ)
    {A₁ B₁ : CY} {A₂ B₂ A₃ B₃ : CX}
    {a : Pg.obj A ⟶ A₁} {b : Pg.obj B ⟶ B₁}
    {a' : Pf.obj A₁ ⟶ A₂} {b' : Pf.obj B₁ ⟶ B₂}
    {a'' : Ph.obj A ⟶ A₃} {b'' : Ph.obj B ⟶ B₃}
    {κ : A₂ ⟶ A₃} {κ' : B₂ ⟶ B₃}
    {MZ : CZ} {MY MY' : CY} {MX MX' MX₀ NX NX' : CX}
    {s : TZ.obj (A, B) ⟶ MZ}
    {m : Pg.obj MZ ⟶ MY} {β : MY ⟶ MY'} {cmpY : TY.obj (A₁, B₁) ⟶ MY'}
    {m' : Pf.obj MY' ⟶ MX} {β' : MX ⟶ MX'} {cmpX : TX.obj (A₂, B₂) ⟶ MX'}
    {m₀ : Pf.obj MY ⟶ MX₀} {β₀ : MX₀ ⟶ MX}
    {m'' : Ph.obj MZ ⟶ NX} {β'' : NX ⟶ NX'} {cmpX' : TX.obj (A₃, B₃) ⟶ NX'}
    {κM : MX₀ ⟶ NX} {κT : MX' ⟶ NX'}
    (hmono : Mono (TX.map (a'' ×ₘ b''))) (hmono' : Mono cmpX')
    (hA : c.app A ≫ a'' = Pf.map a ≫ a' ≫ κ)
    (hB : c.app B ≫ b'' = Pf.map b ≫ b' ≫ κ')
    (hM : c.app MZ ≫ m'' = Pf.map m ≫ m₀ ≫ κM)
    (hν : Pf.map β ≫ m' = m₀ ≫ β₀)
    (hcmp : TX.map (κ ×ₘ κ') ≫ cmpX' = cmpX ≫ κT)
    (hg : tg.app (A, B) ≫ TY.map (a ×ₘ b) ≫ cmpY = Pg.map s ≫ m ≫ β)
    (hf : tf.app (A₁, B₁) ≫ TX.map (a' ×ₘ b') ≫ cmpX = Pf.map cmpY ≫ m' ≫ β')
    (hh : th.app (A, B) ≫ TX.map (a'' ×ₘ b'') ≫ cmpX' = Ph.map s ≫ m'' ≫ β'')
    (hβ : κM ≫ β'' = β₀ ≫ β' ≫ κT) :
    c.app (TZ.obj (A, B)) ≫ th.app (A, B) =
      Pf.map (tg.app (A, B)) ≫ tf.app (Pg.obj A, Pg.obj B) ≫
        TX.map (c.app A ×ₘ c.app B) := by
  have htf := tf.naturality (a ×ₘ b)
  change Pf.map (TY.map (a ×ₘ b)) ≫ _ = _ ≫ TX.map (Pf.map a ×ₘ Pf.map b) at htf
  have hpair : (c.app A ×ₘ c.app B) ≫ (a'' ×ₘ b'') =
      (Pf.map a ×ₘ Pf.map b) ≫ (a' ×ₘ b') ≫ (κ ×ₘ κ') := by
    ext
    · exact hA
    · exact hB
  apply (cancel_mono (TX.map (a'' ×ₘ b''))).1
  apply (cancel_mono cmpX').1
  simp only [Category.assoc]
  rw [hh, ← TX.map_comp_assoc, hpair]
  simp only [TX.map_comp, Category.assoc]
  rw [hcmp, ← reassoc_of% htf, reassoc_of% hf]
  simp only [← Pf.map_comp_assoc]
  rw [hg]
  simp only [Pf.map_comp, Category.assoc]
  rw [reassoc_of% hν, ← c.naturality_assoc]
  simp only [Functor.comp_map]
  rw [reassoc_of% hM]
  simp only [hβ]

/-! ### The K-flat model identity, with the inverses cancelled -/

attribute [local instance] HasDerivedCategory.standard

-- `structureSheafRing` is `@[instance_reducible]`, so it unfolds at `implicit`
-- transparency already, but its reduct stops at an explicit-constructor projection while
-- `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`; these two Mathlib
-- definitions are the gap between them.
--
-- The four names added to the list seat that gap at both ends rather than at one.  `X.sheaf`
-- has type `TopCat.Sheaf CommRingCat X.carrier` while `Tensor.ringSheaf` asks for a
-- `CategoryTheory.Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat`, and the pullback
-- development types the same modules over `structureSheafRing X`.  These are the same data, but
-- they meet only once `TopCat.Sheaf`, `TopCat.Presheaf.IsSheaf`, `structureSheafRing` and
-- `Tensor.ringSheaf` unfold, and `implicit` transparency -- which instance search and `rw`'s
-- motive both run at -- unfolds none of them.  Without them, every statement naming
-- the derived tensor product of `X` is reported as "not type-correct under the `implicit`
-- transparency level", and the synthesis of `Mono` below fails.
attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf
  TopCat.Sheaf TopCat.Presheaf.IsSheaf structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf

section Models

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **On a pair of K-flat complexes the canonical map to the ordinary total tensor complex is
invertible**: there it is the K-flat comparison of Stacks 06YU. -/
theorem isIso_derivedToTensorNatTrans_app (W : RingedSpace.{u, u})
    [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules W) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat W K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat W L) :
    IsIso ((derivedToTensorNatTrans W).app (K, L)) := by
  have h : (derivedToTensorNatTrans W).app (K, L) =
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.sheaf).toTensor K L :=
    rfl
  rw [h, (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    W.sheaf).toTensor_eq_comparison K L hK hL]
  exact Iso.isIso_hom _

/-- **Stacks 079U on K-flat representatives, against the right comparison.**  At a pair of
K-flat cochain complexes `K, L` of `𝒪_Y`-modules the comparison

`Lf^*(QK ⊗^L_{𝒪_Y} QL) ≅ Lf^*(QK) ⊗^L_{𝒪_X} Lf^*(QL)`

followed by `Stacks.Cohomology.DerivedPullbackTensor.rightComparison` is
`Stacks.Cohomology.DerivedPullbackTensor.leftComparison`.

`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_hom_app_of_kFlat` identifies
the component with `Stacks.Cohomology.DerivedPullbackTensor.modelComparison`, which is the left
comparison against the inverse of the right one, and postcomposing with the right comparison
cancels that inverse. -/
theorem derivedPullbackTensorIso_hom_app_comp_rightComparison
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (rightComparison f).app (K, L) =
      (leftComparison f).app (K, L) := by
  have hl := isIso_leftComparison_app f K L hK hL
  have hr := isIso_rightComparison_app f K L hK hL
  rw [derivedPullbackTensorIso_hom_app_of_kFlat f K L hK hL]
  exact trans_symm_hom_comp ((leftComparison f).app (K, L)) ((rightComparison f).app (K, L))

/-- **Stacks 079U on K-flat representatives, as an identity between the two canonical maps into
the ordinary total tensor complex.**  For K-flat cochain complexes `K, L` of `𝒪_Y`-modules the
comparison

`Lf^*(QK ⊗^L_{𝒪_Y} QL) ≅ Lf^*(QK) ⊗^L_{𝒪_X} Lf^*(QL)`,

followed by the derived pullback of each tensor factor and the canonical map to the ordinary
total tensor complex on `X`, is the canonical map to the ordinary total tensor complex on `Y`,
then the derived pullback of a complex, then the comparison of total complexes of Stacks 01CD.

This is `derivedPullbackTensorIso_hom_app_comp_rightComparison` with the right comparison
written out: postcomposing with the comparison of total complexes cancels the inverse that the
right comparison ends with.  No inverse survives, which is what makes this the form a
composition law can be chased with. -/
theorem derivedPullbackTensorIso_hom_app_comp_derivedToTensor
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Y L) :
    (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) ≫
          (derivedToTensorNatTrans X).app
            ((pullbackComplex f).obj K, (pullbackComplex f).obj L) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((derivedToTensorNatTrans Y).app (K, L)) ≫
        (derivedPullbackNatTrans f).app
            ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj (K, L)) ≫
          DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (K, L)) := by
  have hih : DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app (K, L)) ≫
      DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).hom.app (K, L)) = 𝟙 _ :=
    (DerivedCategory.Q.mapIso ((pullbackTensorComplexNatIso f).app (K, L))).inv_hom_id
  have hkey : (derivedPullbackTensorIso f).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
            ((derivedPullbackNatTrans f).app K ×ₘ (derivedPullbackNatTrans f).app L) ≫
          (derivedToTensorNatTrans X).app
              ((pullbackComplex f).obj K, (pullbackComplex f).obj L) ≫
            DerivedCategory.Q.map ((pullbackTensorComplexNatIso f).inv.app (K, L)) =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).map
          ((derivedToTensorNatTrans Y).app (K, L)) ≫
        (derivedPullbackNatTrans f).app
          ((totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf)).obj (K, L)) :=
    derivedPullbackTensorIso_hom_app_comp_rightComparison f K L hK hL
  exact comp_eq_of_comp_inv _ _ _ _ _ _ _ hih hkey

end Models

/-! ### The two monomorphisms the chase cancels -/

section Composite

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived tensor product of the two comparisons `L(f ≫ g)^*(QK) ⟶ Q((f ≫ g)^*K)` is a
monomorphism at a pair of K-flat complexes**, being there the derived tensor product of two
isomorphisms.  This is the first of the two monomorphisms
`tensorComparison_comp_of_models` cancels. -/
theorem mono_derivedTensor_map_derivedPullbackNatTrans_app
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    Mono ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)).map
      ((derivedPullbackNatTrans (f ≫ g)).app K ×ₘ
        (derivedPullbackNatTrans (f ≫ g)).app L)) := by
  have hiK := isIso_derivedPullbackNatTrans_app (f ≫ g) K hK
  have hiL := isIso_derivedPullbackNatTrans_app (f ≫ g) L hL
  have hprod : IsIso ((derivedPullbackNatTrans (f ≫ g)).app K ×ₘ
      (derivedPullbackNatTrans (f ≫ g)).app L) := by
    rw [isIso_prod_iff]
    exact ⟨hiK, hiL⟩
  infer_instance

/-- **The canonical map into the ordinary total tensor complex on `X` is a monomorphism at the
degreewise pullbacks of a pair of K-flat complexes**: those pullbacks are K-flat by Stacks 06YC,
and there the canonical map is the K-flat comparison of Stacks 06YU.  This is the second of the
two monomorphisms `tensorComparison_comp_of_models` cancels. -/
theorem mono_derivedToTensorNatTrans_app_pullbackComplex
    (K L : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)
    (hK : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z K)
    (hL : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.KFlat Z L) :
    Mono ((derivedToTensorNatTrans X).app
      ((pullbackComplex (f ≫ g)).obj K, (pullbackComplex (f ≫ g)).obj L)) := by
  have := isIso_derivedToTensorNatTrans_app X ((pullbackComplex (f ≫ g)).obj K)
    ((pullbackComplex (f ≫ g)).obj L)
    (kFlat_modulePullback_unconditional (f ≫ g) K hK)
    (kFlat_modulePullback_unconditional (f ≫ g) L hL)
  infer_instance

end Composite

end Stacks.Cohomology.DerivedPullbackTensor

end
