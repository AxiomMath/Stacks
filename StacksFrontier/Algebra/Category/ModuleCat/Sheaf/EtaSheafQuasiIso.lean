module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# The décalage of an invertible ideal preserves quasi-isomorphisms

In Situation 0GT4 — a ringed space `(X, O_X)` together with a sheaf of ideals `ι : I ⟶ O_X`
which is invertible and a subsheaf — let `F` and `G` be cochain complexes of `I`-torsion-free
`O_X`-modules.  A map of complexes `a : F ⟶ G` induces a map `η_I a : η_I F ⟶ η_I G` of their
décalages, and this file proves Tag 0F8P: if `a` is a quasi-isomorphism then so is `η_I a`.

## Main definitions

* `etaMap`: the map `η_I F ⟶ η_I G` induced by a map of complexes `F ⟶ G`.  In degree `n` it is
  the map of fibre products whose two components are `I^{⊗ n} ⊗ a^n` and `I^{⊗ (n+1)} ⊗ a^{n+1}`.

## Main results

* `quasiIso_etaMap` (Tag 0F8P): `η_I` carries a quasi-isomorphism of complexes of
  `I`-torsion-free `O_X`-modules to a quasi-isomorphism.
* `etaMap_fst`, `etaMap_snd` pin the induced map down: on the two projections of the fibre
  product `(η_I F)^n` it is the twisted map `a^n` in degree `n` and the twisted map `a^{n+1}`
  in degree `n + 1`.

## Implementation notes

The hypothesis that `a` is a quasi-isomorphism is the one the word "too" in the source
statement presupposes; without it the conclusion is false, since the zero map from the zero
complex to a complex with nonvanishing cohomology is a map of `I`-torsion-free complexes whose
décalage has nonvanishing cohomology in the target.

The argument is the one of the source — the comparison of Tag 0F8N is compatible with maps of
complexes — carried out through the public characterizations of that comparison rather than
through its construction.  Naturality is established one layer at a time: on cocycle sheaves
(`etaCyclesIso_natural`), where both sides are maps into the fibre product `(η_I F)^n` and are
therefore determined by their two projections, and then on cohomology sheaves
(`etaHomologyMap_natural`), where the twisted projection to cohomology is an epimorphism.  The
conclusion does not use the isomorphism of Tag 0F8N itself: what is needed is that the map
`I^{⊗ n} ⊗ H^n(F) ⟶ H^n(η_I F)` is an epimorphism whose kernel is the twisted `I`-torsion, so
that an isomorphism `H^n(F) ≅ H^n(G)` descends to the two cohomology sheaves of the décalages
in both directions, and the two descents are mutually inverse by cancelling those epimorphisms.

Naturality of the ideal-power inclusion `I^{⊗ (n+1)} ⊗ M ⟶ I^{⊗ n} ⊗ M` in `M`, and the
naturality of the right unitor it rests on, are proved here from the public tensor-power
calculus; `EtaSheaf.lean` has both but privately.

As in `EtaSheaf.lean` and `EtaSheafCohomology.lean` the hypotheses are `Mono ι` together with
invertibility of `I`, that is condition (2) of Tag 0GT3 rather than condition (1) demanded by
Situation 0GT4.  This is formally weaker, hence the statements are formally stronger, and it is
the generalization sanctioned by the footnote to Situation 0GT4.

Two spellings of the structure sheaf of rings meet here, as in `EtaSheafCohomology.lean`, so a
composite that mixes `(η_I F).X n` with the projections of the fibre product defining it is
type-correct only at `default` transparency and no rewrite can act on it.  The naturality of
the cocycle comparison is therefore assembled as a chain of ground equations.

### Where Tag 0GTA is

Tag 0GTA states that in Situation 0GT4, for `M` in `D(O_X)` and `x ∈ X` with `O_{X,x}` nonzero,
if `H^i(M)_x` is finite free over `O_{X,x}` then `H^i(Lη_I M)_x` is finite free of the same
rank.  It is formalized, but not here: in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafStalk.lean`,
`Stacks.IdealTorsion.Eta.isFiniteFreeStalkOfRank_homology_derivedEtaOfRegular` states it under
the hypotheses of Situation 0GT4 themselves and
`Stacks.IdealTorsion.Eta.isFiniteFreeStalkOfRank_homology_leta` for the décalage built from
given termwise `I`-torsion-free resolutions, while the clause "of the same rank" — the
uniqueness of the common rank over a nonzero stalk, which is the only use of the hypothesis
`O_{X,x} ≠ 0` — is `Stacks.IdealTorsion.Eta.rank_homology_derivedEtaOfRegular_eq` under the
hypotheses of Situation 0GT4 themselves and
`Stacks.IdealTorsion.Eta.rank_homology_derivedEta_eq` in the generality of the former pair.
The functor `Lη_I` those
statements speak about is `Stacks.IdealTorsion.Eta.derivedEta`, with its Situation 0GT4 form
`Stacks.IdealTorsion.Eta.derivedEtaOfRegular`, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafDerived.lean`; those carry Tag 0F8Q.

The complex-level content on which they rest is also in `EtaSheafStalk.lean`: the stalk form of
Tag 0F8N (`Stacks.IdealTorsion.Eta.etaCohomologyStalkEquiv`), the rank predicate at the
`ringStalk X x` spelling used by `EtaSheaf.lean` together with the uniqueness of the rank over a
nonzero stalk (`Stacks.IdealTorsion.Eta.IsFiniteFreeStalkOfRank` and its `rank_eq`), and the
conclusion that `H^i(F)_x` finite free of rank `r` forces `H^i(η_I F)_x` finite free of rank `r`
(`Stacks.IdealTorsion.Eta.isFiniteFreeStalkOfRank_etaHomology_of_homology`).

## References

* [Stacks Project, Tag 0F8P](https://stacks.math.columbia.edu/tag/0F8P)
* [Stacks Project, Tag 0F8N](https://stacks.math.columbia.edu/tag/0F8N)
* [Stacks Project, Tag 0GT4](https://stacks.math.columbia.edu/tag/0GT4)
* [Stacks Project, Tag 0GT3](https://stacks.math.columbia.edu/tag/0GT3)
* [Stacks Project, Tag 0GTA](https://stacks.math.columbia.edu/tag/0GTA)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

open Stacks.SheafOfModules.Invertible ( tensorRightFunctor_isEquivalence
  tensorPowerEquivalence powSuccIso powSuccIso_natural
  tensorProductRightUnitor)

universe u v w

namespace Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ





/-- The induced map on the degree-`n` term. -/
noncomputable def etaTermMap (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G) (n : ℤ) :
    etaTerm X I ι F n ⟶ etaTerm X I ι G n :=
  pullback.lift
    (pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1))) ≫ idealPowerMap X I n (a.f n))
    (pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
        (idealPowerIncl X I ι n (F.X (n + 1))) ≫
      idealPowerMap X I (n + 1) (a.f (n + 1)))
    (by
      simp only [Category.assoc]
      rw [← idealPowerMap_comp, a.comm, idealPowerMap_comp, pullback.condition_assoc,
        idealPowerIncl_natural])


/-- On the first projection of the defining fibre product, the induced map on the degree-`n`
décalage term is the twisted map in the same degree.  This is
`Stacks.IdealTorsion.Eta.etaMap_fst` at the `etaTerm` spelling, in which every object in sight is
a fibre product. -/
public lemma etaTermMap_pullbackFst (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G) (n : ℤ) :
    etaTermMap X I ι a n ≫
        pullback.fst (idealPowerMap X I n (G.d n (n + 1)))
          (idealPowerIncl X I ι n (G.X (n + 1))) =
      pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
          (idealPowerIncl X I ι n (F.X (n + 1))) ≫ idealPowerMap X I n (a.f n) :=
  pullback.lift_fst _ _ _

/-- On the second projection of the defining fibre product, the induced map on the degree-`n`
décalage term is the twisted map in the next degree.  This is
`Stacks.IdealTorsion.Eta.etaMap_snd` at the `etaTerm` spelling. -/
public lemma etaTermMap_pullbackSnd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G) (n : ℤ) :
    etaTermMap X I ι a n ≫
        pullback.snd (idealPowerMap X I n (G.d n (n + 1)))
          (idealPowerIncl X I ι n (G.X (n + 1))) =
      pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
          (idealPowerIncl X I ι n (F.X (n + 1))) ≫
        idealPowerMap X I (n + 1) (a.f (n + 1)) :=
  pullback.lift_snd _ _ _

private alias etaTermMap_fst := etaTermMap_pullbackFst

private alias etaTermMap_snd := etaTermMap_pullbackSnd

private lemma etaTermMap_comm (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ) :
    etaTermMap X I ι a n ≫ (etaDifferentialData X I ι G hG).d n =
      (etaDifferentialData X I ι F hF).d n ≫ etaTermMap X I ι a (n + 1) := by
  set L := etaTermMap X I ι a n ≫ (etaDifferentialData X I ι G hG).d n with hL
  set R := (etaDifferentialData X I ι F hF).d n ≫ etaTermMap X I ι a (n + 1) with hR
  have hfst : L ≫ pullback.fst (idealPowerMap X I (n + 1) (G.d (n + 1) (n + 1 + 1)))
          (idealPowerIncl X I ι (n + 1) (G.X (n + 1 + 1))) =
      R ≫ pullback.fst (idealPowerMap X I (n + 1) (G.d (n + 1) (n + 1 + 1)))
          (idealPowerIncl X I ι (n + 1) (G.X (n + 1 + 1))) := by
    rw [hL, hR, Category.assoc, Category.assoc,
      (etaDifferentialData X I ι G hG).d_fst n, etaTermMap_snd, etaTermMap_fst,
      ← Category.assoc, (etaDifferentialData X I ι F hF).d_fst n]
  apply pullback.hom_ext
  · exact hfst
  · have _hm : Mono (idealPowerIncl X I ι (n + 1) (G.X (n + 1 + 1))) :=
      idealPowerIncl_mono X I ι (G.X (n + 1 + 1)) (hG _) (n + 1)
    apply (cancel_mono (idealPowerIncl X I ι (n + 1) (G.X (n + 1 + 1)))).mp
    have hc : pullback.snd (idealPowerMap X I (n + 1) (G.d (n + 1) (n + 1 + 1)))
            (idealPowerIncl X I ι (n + 1) (G.X (n + 1 + 1))) ≫
          idealPowerIncl X I ι (n + 1) (G.X (n + 1 + 1)) =
        pullback.fst (idealPowerMap X I (n + 1) (G.d (n + 1) (n + 1 + 1)))
            (idealPowerIncl X I ι (n + 1) (G.X (n + 1 + 1))) ≫
          idealPowerMap X I (n + 1) (G.d (n + 1) (n + 1 + 1)) :=
      pullback.condition.symm
    rw [Category.assoc, Category.assoc, hc, ← Category.assoc, ← Category.assoc, hfst,
      Category.assoc, Category.assoc, pullback.condition]
    simp only [hR, Category.assoc]

/-- **The induced map.**  A map of complexes of `I`-torsion-free `O_X`-modules induces a map of
their décalages. -/
public noncomputable def etaMap (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) :
    etaObj X I ι F hF ⟶ etaObj X I ι G hG where
  f n := etaTermMap X I ι a n
  comm' n m h := by
    obtain rfl : n + 1 = m := h
    rw [etaObj_d_eq, etaObj_d_eq]
    exact etaTermMap_comm X I ι a hF hG n

private lemma etaMap_f (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ) :
    (etaMap X I ι a hF hG).f n = etaTermMap X I ι a n := rfl


/-- The first projection of the fibre product defining the degree-`n` décalage term. -/
public noncomputable abbrev etaFst (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaTerm X I ι F n ⟶ idealPowerTerm X I n (F.X n) :=
  pullback.fst (idealPowerMap X I n (F.d n (n + 1)))
    (idealPowerIncl X I ι n (F.X (n + 1)))

/-- The second projection of the fibre product defining the degree-`n` décalage term. -/
public noncomputable abbrev etaSnd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaTerm X I ι F n ⟶ idealPowerTerm X I (n + 1) (F.X (n + 1)) :=
  pullback.snd (idealPowerMap X I n (F.d n (n + 1)))
    (idealPowerIncl X I ι n (F.X (n + 1)))

/-- On the first projection, the induced map is the twisted map in the same degree. -/
public theorem etaMap_fst (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ) :
    (etaMap X I ι a hF hG).f n ≫ etaFst X I ι G n =
      etaFst X I ι F n ≫ idealPowerMap X I n (a.f n) :=
  etaTermMap_fst X I ι a n

/-- On the second projection, the induced map is the twisted map in the next degree. -/
public theorem etaMap_snd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ) :
    (etaMap X I ι a hF hG).f n ≫ etaSnd X I ι G n =
      etaSnd X I ι F n ≫ idealPowerMap X I (n + 1) (a.f (n + 1)) :=
  etaTermMap_snd X I ι a n

/-- A naturality square for a map into a fibre product, checked after one projection. -/
private lemma comp_proj_eq_of_comp_eq {C : Type*} [Category C] {S S' T T' U V P Q : C}
    (e : S ⟶ T) (iF : T ⟶ U) (f : U ⟶ V) (pG : V ⟶ P) (pF : U ⟶ Q) (k : Q ⟶ P)
    (h : S ⟶ S') (e' : S' ⟶ T') (iG : T' ⟶ V) (u : S ⟶ Q) (v : S' ⟶ P)
    (hp : f ≫ pG = pF ≫ k) (hu : e ≫ iF ≫ pF = u) (hv : e' ≫ iG ≫ pG = v)
    (huv : u ≫ k = h ≫ v) : e ≫ (iF ≫ f) ≫ pG = h ≫ (e' ≫ iG) ≫ pG := by
  simp only [Category.assoc] at *
  rw [hp, reassoc_of% hu, huv, hv]

/-- The naturality square of `etaCyclesIso_natural`, after the first projection of the defining
fibre product. -/
private lemma etaCyclesIso_natural_fst (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ) :
    (etaCyclesIso X I ι F hF n).hom ≫
        ((etaObj X I ι F hF).iCycles n ≫ (etaMap X I ι a hF hG).f n) ≫ etaFst X I ι G n =
      idealPowerMap X I n (HomologicalComplex.cyclesMap a n) ≫
        ((etaCyclesIso X I ι G hG n).hom ≫ (etaObj X I ι G hG).iCycles n) ≫
          etaFst X I ι G n :=
  comp_proj_eq_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ (etaMap_fst X I ι a hF hG n)
    (etaCyclesIso_hom_fst X I ι F hF n) (etaCyclesIso_hom_fst X I ι G hG n)
    (by rw [← idealPowerMap_comp, ← idealPowerMap_comp, ← HomologicalComplex.cyclesMap_i])

/-- The naturality square of `etaCyclesIso_natural`, after the second projection of the defining
fibre product. -/
private lemma etaCyclesIso_natural_snd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ) :
    (etaCyclesIso X I ι F hF n).hom ≫
        ((etaObj X I ι F hF).iCycles n ≫ (etaMap X I ι a hF hG).f n) ≫ etaSnd X I ι G n =
      idealPowerMap X I n (HomologicalComplex.cyclesMap a n) ≫
        ((etaCyclesIso X I ι G hG n).hom ≫ (etaObj X I ι G hG).iCycles n) ≫
          etaSnd X I ι G n :=
  comp_proj_eq_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ (etaMap_snd X I ι a hF hG n)
    (etaCyclesIso_hom_snd X I ι F hF n) (etaCyclesIso_hom_snd X I ι G hG n)
    (by rw [zero_comp, comp_zero])

/-- The comparison of cocycle sheaves of Tag 0F8N is natural in the complex. -/
private lemma etaCyclesIso_natural (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ) :
    (etaCyclesIso X I ι F hF n).hom ≫
        HomologicalComplex.cyclesMap (etaMap X I ι a hF hG) n =
      idealPowerMap X I n (HomologicalComplex.cyclesMap a n) ≫
        (etaCyclesIso X I ι G hG n).hom := by
  apply (cancel_mono ((etaObj X I ι G hG).iCycles n)).mp
  have hL : ((etaCyclesIso X I ι F hF n).hom ≫
        HomologicalComplex.cyclesMap (etaMap X I ι a hF hG) n) ≫
        (etaObj X I ι G hG).iCycles n =
      (etaCyclesIso X I ι F hF n).hom ≫
        ((etaObj X I ι F hF).iCycles n ≫ (etaMap X I ι a hF hG).f n) :=
    (Category.assoc _ _ _).trans
      (congrArg ((etaCyclesIso X I ι F hF n).hom ≫ ·)
        (HomologicalComplex.cyclesMap_i (etaMap X I ι a hF hG) n))
  have hR : (idealPowerMap X I n (HomologicalComplex.cyclesMap a n) ≫
        (etaCyclesIso X I ι G hG n).hom) ≫ (etaObj X I ι G hG).iCycles n =
      idealPowerMap X I n (HomologicalComplex.cyclesMap a n) ≫
        ((etaCyclesIso X I ι G hG n).hom ≫ (etaObj X I ι G hG).iCycles n) :=
    Category.assoc _ _ _
  refine hL.trans (Eq.trans ?_ hR.symm)
  apply pullback.hom_ext
  · exact etaCyclesIso_natural_fst X I ι a hF hG n
  · exact etaCyclesIso_natural_snd X I ι a hF hG n

private lemma etaHomologyMap_natural (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ) :
    etaHomologyMap X I ι F hF n ≫
        HomologicalComplex.homologyMap (etaMap X I ι a hF hG) n =
      idealPowerMap X I n (HomologicalComplex.homologyMap a n) ≫
        etaHomologyMap X I ι G hG n := by
  have _he : Epi (idealPowerMap X I n (F.homologyπ n)) :=
    @Functor.map_epi _ _ _ _ (tensorPowerEquivalence X.sheaf.obj (Oₓ).property I n).functor
      inferInstance _ _ (F.homologyπ n) (HomologicalComplex.instEpiHomologyπ F n)
  apply (cancel_epi (idealPowerMap X I n (F.homologyπ n))).mp
  rw [← Category.assoc, etaHomologyMap_cycles, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc, etaCyclesIso_natural,
    Category.assoc, ← etaHomologyMap_cycles, ← Category.assoc, ← idealPowerMap_comp,
    ← Category.assoc, ← idealPowerMap_comp, HomologicalComplex.homologyπ_naturality]

private lemma etaHomologyMap_desc (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (n : ℤ)
    {T : SheafOfModules.{u} Oₓ} (t : idealPowerTerm X I n (G.homology n) ⟶ T)
    (ht : idealPowerMap X I n (idealPowerAnnihilatorSubsheaf X ι (G.homology n) 1).ι ≫ t = 0) :
    ∃ s : (etaObj X I ι G hG).homology n ⟶ T, etaHomologyMap X I ι G hG n ≫ s = t := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, (sub_add_cancel n 1).symm⟩
  let E := (tensorPowerEquivalence X.sheaf.obj (Oₓ).property I (m + 1)).functor
  let Ann := idealPowerAnnihilatorSubsheaf X ι (G.homology (m + 1)) 1
  let i := idealPowerMap X I (m + 1) Ann.ι
  let f := etaHomologyMap X I ι G hG (m + 1)
  have hc {B : SheafOfModules.{u} Oₓ}
      (b : B ⟶ idealPowerTerm X I (m + 1) (G.homology (m + 1))) :
      b ≫ f = 0 ↔ b ≫ idealPowerIncl X I ι m (G.homology (m + 1)) = 0 :=
    etaHomologyMap_comp_eq_zero_iff X I ι G hG m b
  have hi : i ≫ f = 0 :=
    (hc i).mpr (idealPowerAnnihilator_incl_zero X I ι (G.homology (m + 1)) m)
  have _hm : Mono i :=
    @Functor.map_mono _ _ _ _ E inferInstance _ _ Ann.ι
      (SheafOfModules.Submodule.instMonoι Ann)
  let hk : IsLimit (KernelFork.ofι i hi) := by
    refine KernelFork.IsLimit.ofι' _ _ ?_
    intro B b hb
    exact KernelFork.IsLimit.lift'
      (idealPowerAnnihilatorIsKernel X I ι (G.homology (m + 1)) m) b ((hc b).mp hb)
  have hS : (ShortComplex.mk i f hi).Exact := ShortComplex.exact_of_f_is_kernel _ hk
  have _hepi : Epi f := etaHomologyMap_epi X I ι G hG (m + 1)
  exact ⟨_, (CokernelCofork.IsColimit.desc' hS.gIsCokernel t ht).2⟩


private lemma etaHomologyMap_descAlong (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) (m : ℤ)
    (ψ : G.homology (m + 1) ⟶ F.homology (m + 1)) :
    ∃ s : (etaObj X I ι G hG).homology (m + 1) ⟶ (etaObj X I ι F hF).homology (m + 1),
      etaHomologyMap X I ι G hG (m + 1) ≫ s =
        idealPowerMap X I (m + 1) ψ ≫ etaHomologyMap X I ι F hF (m + 1) := by
  refine etaHomologyMap_desc X I ι G hG (m + 1) _ ?_
  let annihilator := idealPowerAnnihilatorSubsheaf X ι (G.homology (m + 1)) 1
  have mappedComposition := idealPowerMap_comp X I (m + 1) annihilator.ι ψ
  have intoInclusionZero : idealPowerMap X I (m + 1) (annihilator.ι ≫ ψ) ≫
      idealPowerIncl X I ι m (F.homology (m + 1)) = 0 :=
    (congrArg (fun morphism => morphism ≫ idealPowerIncl X I ι m (F.homology (m + 1)))
      mappedComposition).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (idealPowerMap X I (m + 1) annihilator.ι ≫ ·)
            (idealPowerIncl_natural X I ι m ψ).symm).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun morphism => morphism ≫ idealPowerMap X I m ψ)
                  (idealPowerAnnihilator_incl_zero X I ι (G.homology (m + 1)) m)).trans
                    zero_comp))))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun morphism => morphism ≫ etaHomologyMap X I ι F hF (m + 1))
      mappedComposition.symm).trans
        ((etaHomologyMap_comp_eq_zero_iff X I ι F hF m _).mpr intoInclusionZero))

/-- **Stacks Project, Tag 0F8P.**  In Situation 0GT4, if a map `a : F ⟶ G` of complexes of
`I`-torsion-free `O_X`-modules is a quasi-isomorphism, then so is the induced map
`η_I a : η_I F ⟶ η_I G` of décalages. -/
@[stacks 0F8P]
public theorem quasiIso_etaMap (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n))
    (ha : QuasiIso a) :
    QuasiIso (etaMap X I ι a hF hG) := by
  refine ⟨fun n => ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, (sub_add_cancel n 1).symm⟩
  have hiso : IsIso (HomologicalComplex.homologyMap a (m + 1)) :=
    (quasiIsoAt_iff_isIso_homologyMap a (m + 1)).mp (ha.quasiIsoAt (m + 1))
  have _heF : Epi (etaHomologyMap X I ι F hF (m + 1)) :=
    etaHomologyMap_epi X I ι F hF (m + 1)
  have _heG : Epi (etaHomologyMap X I ι G hG (m + 1)) :=
    etaHomologyMap_epi X I ι G hG (m + 1)
  obtain ⟨s, hs⟩ := etaHomologyMap_descAlong X I ι F G hF hG m
    (inv (HomologicalComplex.homologyMap a (m + 1)))
  have hnat := etaHomologyMap_natural X I ι a hF hG (m + 1)
  refine ⟨s, ?_, ?_⟩
  · apply (cancel_epi (etaHomologyMap X I ι F hF (m + 1))).mp
    rw [← Category.assoc, hnat, Category.assoc, hs, ← Category.assoc, ← idealPowerMap_comp,
      IsIso.hom_inv_id, idealPowerMap_id, Category.id_comp, Category.comp_id]
  · apply (cancel_epi (etaHomologyMap X I ι G hG (m + 1))).mp
    rw [← Category.assoc, hs, Category.assoc, hnat, ← Category.assoc, ← idealPowerMap_comp,
      IsIso.inv_hom_id, idealPowerMap_id, Category.id_comp, Category.comp_id]

end Stacks.IdealTorsion.Eta

end
