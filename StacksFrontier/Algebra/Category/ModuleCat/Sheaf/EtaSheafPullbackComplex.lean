module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackTerm
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafQuasiIso

/-!
# The comparison of décalages under a pullback, as a map of complexes

Let `f : X ⟶ Y` be a morphism of ringed spaces, let `I ⊆ 𝒪_Y` be an invertible ideal sheaf and
let `F^•` be a cochain complex of `I`-torsion-free `𝒪_Y`-modules whose termwise pullback is a
complex of `f^*I`-torsion-free `𝒪_X`-modules.  This file assembles the degreewise comparison of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheafPullbackTerm.lean` into a map of complexes

`f^*(η_I F^•) ⟶ η_{f^*I}(f^* F^•)`

and shows that it is an isomorphism when `f` is flat.

## Main definitions

* `Stacks.IdealTorsion.Eta.pullbackEtaTermMap`: the canonical comparison on the degree-`n` term.
  No flatness is assumed: pullback carries the cone defining `η_I F^•` in degree `n` to a cone on
  the pulled-back cospan, and the canonical map to the limit is the comparison.
* `Stacks.IdealTorsion.Eta.pullbackEtaMap`: the same as a morphism of cochain complexes.

## Main results

* `Stacks.IdealTorsion.Eta.etaDifferentialData_d_comp_etaSnd` and
  `Stacks.IdealTorsion.Eta.etaObj_d_comp_etaSnd`: the differential of `η_I F^•` kills the second
  projection in the next degree.  Together with
  `Stacks.IdealTorsion.Eta.EtaDifferentialData.d_fst` this pins the differential down.
* `Stacks.IdealTorsion.Eta.pullbackEtaTermIso_hom_eq`: for flat `f`, the degreewise comparison
  isomorphism `Stacks.IdealTorsion.Eta.pullbackEtaTermIso` has the canonical comparison as its
  underlying map; so the latter is an isomorphism, which is
  `Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap`.
* `Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap`: **for flat `f` the comparison of complexes is
  an isomorphism.**
* `Stacks.IdealTorsion.Eta.pullbackEtaTermMap_natural` and
  `Stacks.IdealTorsion.Eta.pullbackEtaMap_natural`: **the comparison is natural in the
  complex**, with no flatness hypothesis.  This is what lets the comparison at an arbitrary
  complex be read off the comparison at a complex along which it is understood: precomposing
  with the pullback of `η_I` of a map of complexes is the same as postcomposing with
  `η_{f^*I}` of the pullback of that map.

## Implementation notes

Everything is proved through the two projections of the defining fibre products: the degree-`n`
term of `η_I F^•` is a fibre product, the differential is characterized by
`Stacks.IdealTorsion.Eta.EtaDifferentialData.d_fst` together with the vanishing
`etaDifferentialData_d_comp_etaSnd`, and the comparison is a
`CategoryTheory.Limits.pullback.lift`.  Each square below is therefore an application of
`CategoryTheory.Limits.pullback.hom_ext`.

That vanishing is not a field of `EtaDifferentialData`; it is recovered from `d_fst` by
cancelling the monomorphism `idealPowerIncl`, which is a monomorphism precisely because the terms
of `F^•` are `I`-torsion-free.

As in the files this one builds on, the projection `(η_I F^•).X n` does not unfold to the fibre
product `etaTerm` at `instances` transparency, so a tactic proof phrased at the `η_I F^•`
spelling breaks.  Every square is therefore proved one degree at a time in a statement written
purely through `etaDifferentialData` and `etaTerm`, and crossed to `η_I F^•` by
`Stacks.IdealTorsion.Eta.etaObj_d_eq`.

The pullback functor is typed over a different spelling of the structure sheaf of rings than the
décalage files, so composites mixing the two carry different `Category` instance terms and `rw`
cannot match `Category.assoc` in them.  The squares are therefore assembled by `Eq.trans`, and the
fibre-product lemmas are applied in the category of the décalage files, named explicitly.

The hypothesis that the termwise pullback of `F^•` is a complex of `f^*I`-torsion-free modules is
taken as an argument rather than derived: `η` of a complex takes torsion-freeness of its terms as
data, so both décalages below need their own.  Likewise `Mono (pullbackIdealIncl f I ι)`, in the
category of the décalage files, is an instance argument; for flat `f` it is supplied by
`Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl`.  Flatness of `f` is *not* needed for the
comparison map itself, only for its invertibility.
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)

universe u

namespace Stacks.IdealTorsion.Eta

/-! ### The second projection of the differential of a décalage -/

section Differential

variable (X : RingedSpace.{u})

/-- The differential of the décalage kills the second projection in the next degree.

The second projection is a section of the next ideal power, and the twisted differential kills it
by `Stacks.IdealTorsion.Eta.etaTerm_snd_comp_d_eq_zero`; the claim follows by cancelling the
monomorphism `idealPowerIncl`, which is one because the terms of `F^•` are `I`-torsion-free.

This is stated at the `etaTerm` spelling, where every object is a fibre product; see
`Stacks.IdealTorsion.Eta.etaObj_d_comp_etaSnd` for the same statement about `η_I F^•`. -/
theorem etaDifferentialData_d_comp_etaSnd
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaDifferentialData X I ι F hF).d n ≫ etaSnd X I ι F (n + 1) = 0 := by
  have hmono : Mono (idealPowerIncl X I ι (n + 1) (F.X (n + 1 + 1))) :=
    idealPowerIncl_mono X I ι (F.X (n + 1 + 1)) (hF _) (n + 1)
  have := hmono
  apply (cancel_mono (idealPowerIncl X I ι (n + 1) (F.X (n + 1 + 1)))).mp
  rw [zero_comp, Category.assoc, ← pullback.condition, ← Category.assoc,
    (etaDifferentialData X I ι F hF).d_fst n]
  exact etaTerm_snd_comp_d_eq_zero X I ι F n
    (idealPowerIncl_mono X I ι (F.X (n + 1 + 1)) (hF _) n)

/-- The differential of `η_I F^•` composed with the second projection in the next degree
vanishes. -/
theorem etaObj_d_comp_etaSnd
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaObj X I ι F hF).d n (n + 1) ≫ etaSnd X I ι F (n + 1) = 0 := by
  rw [etaObj_d_eq]
  exact etaDifferentialData_d_comp_etaSnd X I ι F hF n

end Differential

/-! ### The canonical comparison on a term -/

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The two projections of the pulled-back fibre product, composed with the interchange of the
pullback with the ideal powers, form a cone on the cospan defining `η_{f^*I}(f^* F^•)` in degree
`n`.

The square for the twisted differential is
`Stacks.IdealTorsion.Eta.pullbackIdealPowerIso_natural` and the square for the inclusion of
consecutive ideal powers is `Stacks.IdealTorsion.Eta.map_idealPowerIncl`; between them sits the
pullback of the defining condition of the fibre product on `Y`. -/
theorem pullbackEtaTerm_cone_condition
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    ((pullbackFunctor f).map (etaFst Y I ι F n) ≫
          (pullbackIdealPowerIso f I n (F.X n)).hom) ≫
        idealPowerMap X ((pullbackFunctor f).obj I) n
          ((pullbackFunctor f).map (F.d n (n + 1))) =
      ((pullbackFunctor f).map (etaSnd Y I ι F n) ≫
          (pullbackIdealPowerIso f I (n + 1) (F.X (n + 1))).hom) ≫
        idealPowerIncl X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) n
          ((pullbackFunctor f).obj (F.X (n + 1))) := by
  -- The composites mix the category instance of the pullback functor's spelling of the structure
  -- sheaf with that of the décalage files, so `rw` cannot match `Category.assoc`; the chain is
  -- assembled by `Eq.trans`, where each step is a `default`-transparency unification.
  refine (Category.assoc _ _ _).trans <|
    (congrArg (fun k => (pullbackFunctor f).map (etaFst Y I ι F n) ≫ k)
      (pullbackIdealPowerIso_natural f I n (F.d n (n + 1))).symm).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (fun k => k ≫ (pullbackIdealPowerIso f I n (F.X (n + 1))).hom)
      (((pullbackFunctor f).map_comp _ _).symm.trans <|
        (congrArg (pullbackFunctor f).map pullback.condition).trans
          ((pullbackFunctor f).map_comp _ _))).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (fun k => (pullbackFunctor f).map (etaSnd Y I ι F n) ≫ k)
      (map_idealPowerIncl f I ι n (F.X (n + 1)))).trans (Category.assoc _ _ _).symm

/-- **The canonical comparison of décalages on a term.**  The pullback of the degree-`n` fibre
product defining `η_I F^•` maps canonically to the degree-`n` fibre product defining
`η_{f^*I}(f^* F^•)`: the pullback of the defining cone is a cone on the pulled-back cospan, after
the interchange of the pullback with the ideal powers.

No flatness is assumed.  Flatness of `f` is what makes this map an isomorphism, by
`Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap`. -/
noncomputable def pullbackEtaTermMap
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    (pullbackFunctor f).obj (etaTerm Y I ι F n) ⟶
      etaTerm X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) n :=
  pullback.lift (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    ((pullbackFunctor f).map (etaFst Y I ι F n) ≫ (pullbackIdealPowerIso f I n (F.X n)).hom)
    ((pullbackFunctor f).map (etaSnd Y I ι F n) ≫
      (pullbackIdealPowerIso f I (n + 1) (F.X (n + 1))).hom)
    (pullbackEtaTerm_cone_condition f I ι F n)

/-- The first projection of the canonical comparison on a term. -/
theorem pullbackEtaTermMap_fst
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    pullbackEtaTermMap f I ι F n ≫
        etaFst X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) n =
      (pullbackFunctor f).map (etaFst Y I ι F n) ≫ (pullbackIdealPowerIso f I n (F.X n)).hom :=
  pullback.lift_fst (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) _ _ _

/-- The second projection of the canonical comparison on a term. -/
theorem pullbackEtaTermMap_snd
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    pullbackEtaTermMap f I ι F n ≫
        etaSnd X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) n =
      (pullbackFunctor f).map (etaSnd Y I ι F n) ≫
        (pullbackIdealPowerIso f I (n + 1) (F.X (n + 1))).hom :=
  pullback.lift_snd (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) _ _ _

/-- For a flat morphism the degreewise comparison isomorphism
`Stacks.IdealTorsion.Eta.pullbackEtaTermIso` is the canonical comparison map: both are maps into
a fibre product, and their two projections agree. -/
theorem pullbackEtaTermIso_hom_eq (hf : AlgebraicGeometry.IsFlat f)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    (pullbackEtaTermIso f hf I ι F n).hom = pullbackEtaTermMap f I ι F n :=
  pullback.hom_ext (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    ((pullbackEtaTermIso_hom_fst f hf I ι F n).trans (pullbackEtaTermMap_fst f I ι F n).symm)
    ((pullbackEtaTermIso_hom_snd f hf I ι F n).trans (pullbackEtaTermMap_snd f I ι F n).symm)

/-- **For a flat morphism the canonical comparison of décalages on a term is an
isomorphism.** -/
theorem isIso_pullbackEtaTermMap (hf : AlgebraicGeometry.IsFlat f)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
    (n : ℤ) :
    IsIso (pullbackEtaTermMap f I ι F n) := by
  rw [← pullbackEtaTermIso_hom_eq f hf I ι F n]
  exact (pullbackEtaTermIso f hf I ι F n).isIso_hom

/-! ### The canonical comparison as a map of complexes -/

section Complex

variable (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) [Mono ι]
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
    (pullbackIdealIncl f I ι)]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ)
  (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
  (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι) ((pullbackComplex f F).X n))

/-- The canonical comparison on terms commutes with the differentials of the two décalages.

Checked on the two projections of the target fibre product: on the first the square becomes the
pullback of `Stacks.IdealTorsion.Eta.EtaDifferentialData.d_fst`, and on the second both sides
vanish by `Stacks.IdealTorsion.Eta.etaDifferentialData_d_comp_etaSnd`, on `Y` before pulling back
and on `X` after.

Stated at the `etaTerm` spelling, so that every object in sight is a fibre product. -/
theorem pullbackEtaTermMap_comm (n : ℤ) :
    pullbackEtaTermMap f I ι F n ≫
        (etaDifferentialData X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (pullbackComplex f F) hF').d n =
      (pullbackFunctor f).map ((etaDifferentialData Y I ι F hF).d n) ≫
        pullbackEtaTermMap f I ι F (n + 1) := by
  -- The composites mix the category instance of the pullback functor's spelling of the structure
  -- sheaf with that of the décalage files, so `rw` cannot match them; each square is assembled
  -- by `Eq.trans`, whose steps are `default`-transparency unifications.
  refine pullback.hom_ext
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ?_ ?_
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (fun k => pullbackEtaTermMap f I ι F n ≫ k)
        ((etaDifferentialData X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (pullbackComplex f F) hF').d_fst n)).trans <|
      (pullbackEtaTermMap_snd f I ι F n).trans <|
      (congrArg (fun k => k ≫ (pullbackIdealPowerIso f I (n + 1) (F.X (n + 1))).hom)
        ((congrArg (pullbackFunctor f).map ((etaDifferentialData Y I ι F hF).d_fst n).symm).trans
          ((pullbackFunctor f).map_comp _ _))).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg (fun k => (pullbackFunctor f).map ((etaDifferentialData Y I ι F hF).d n) ≫ k)
        (pullbackEtaTermMap_fst f I ι F (n + 1)).symm).trans (Category.assoc _ _ _).symm
  · have hR : ((pullbackFunctor f).map ((etaDifferentialData Y I ι F hF).d n) ≫
          pullbackEtaTermMap f I ι F (n + 1)) ≫
        etaSnd X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F)
          (n + 1) = 0 :=
      (Category.assoc _ _ _).trans <|
        (congrArg (fun k => (pullbackFunctor f).map ((etaDifferentialData Y I ι F hF).d n) ≫ k)
          (pullbackEtaTermMap_snd f I ι F (n + 1))).trans <|
        (Category.assoc _ _ _).symm.trans <|
        (congrArg (fun k => k ≫ (pullbackIdealPowerIso f I (n + 1 + 1) (F.X (n + 1 + 1))).hom)
          (((pullbackFunctor f).map_comp _ _).symm.trans <|
            (congrArg (pullbackFunctor f).map
              (etaDifferentialData_d_comp_etaSnd Y I ι F hF n)).trans
              ((pullbackFunctor f).map_zero _ _))).trans zero_comp
    exact ((Category.assoc _ _ _).trans <|
      (congrArg (fun k => pullbackEtaTermMap f I ι F n ≫ k)
        (etaDifferentialData_d_comp_etaSnd X ((pullbackFunctor f).obj I)
          (pullbackIdealIncl f I ι) (pullbackComplex f F) hF' n)).trans comp_zero).trans hR.symm

/-- **The canonical comparison of décalages under a pullback, as a map of cochain complexes**:
`f^*(η_I F^•) ⟶ η_{f^*I}(f^* F^•)`.

The degree-`n` component is `Stacks.IdealTorsion.Eta.pullbackEtaTermMap` and the commutation with
the differentials is `Stacks.IdealTorsion.Eta.pullbackEtaTermMap_comm`.

No flatness is assumed; see `Stacks.IdealTorsion.Eta.isIso_pullbackEtaMap`. -/
noncomputable def pullbackEtaMap :
    pullbackComplex f (etaObj Y I ι F hF) ⟶
      etaObj X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι) (pullbackComplex f F) hF' where
  f n := pullbackEtaTermMap f I ι F n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have hX : (etaObj X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
        (pullbackComplex f F) hF').d i (i + 1) =
          (etaDifferentialData X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
            (pullbackComplex f F) hF').d i := by
      simp only [etaObj, CochainComplex.of_d]
    exact (congrArg (fun k => pullbackEtaTermMap f I ι F i ≫ k) hX).trans <|
      (pullbackEtaTermMap_comm f I ι F hF hF' i).trans
      (congrArg (fun k => (pullbackFunctor f).map k ≫ pullbackEtaTermMap f I ι F (i + 1))
        (etaObj_d_eq Y I ι F hF i).symm)

/-- The degree-`n` component of the comparison of complexes is the comparison on the term. -/
theorem pullbackEtaMap_f (n : ℤ) :
    (pullbackEtaMap f I ι F hF hF').f n = pullbackEtaTermMap f I ι F n :=
  rfl

/-- **For a flat morphism the comparison of décalages is an isomorphism of complexes**:
`f^*(η_I F^•) ≅ η_{f^*I}(f^* F^•)`.

A map of complexes is invertible as soon as it is invertible in every degree, which is
`Stacks.IdealTorsion.Eta.isIso_pullbackEtaTermMap`. -/
theorem isIso_pullbackEtaMap (hf : AlgebraicGeometry.IsFlat f) :
    IsIso (pullbackEtaMap f I ι F hF hF') := by
  have h : ∀ n : ℤ, IsIso ((pullbackEtaMap f I ι F hF hF').f n) := fun n => by
    rw [pullbackEtaMap_f]
    exact isIso_pullbackEtaTermMap f hf I ι F n
  have := h
  exact HomologicalComplex.Hom.isIso_of_components _

end Complex

/-! ### Naturality in the complex -/

section Naturality

variable (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  (ι : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
  [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).property I]
  {F G : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) ℤ} (a : F ⟶ G)

/-- A square of comparison maps over a functor `Φ` commutes once it does on a projection: the
square upstairs, the comparisons of both ends, the square downstairs and the naturality of the
interchange `e` of `Φ` with the target of the projection are all that is used. -/
private theorem map_comp_comparison_comp_eq {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D)
    {A B P Q : C} {A' B' P' Q' : D} {u : A ⟶ B} {p : A ⟶ P} {q : B ⟶ Q} {m : P ⟶ Q}
    {e : Φ.obj P ≅ P'} {e' : Φ.obj Q ≅ Q'} {m' : P' ⟶ Q'} {TF : Φ.obj A ⟶ A'}
    {TG : Φ.obj B ⟶ B'} {v : A' ⟶ B'} {p' : A' ⟶ P'} {q' : B' ⟶ Q'}
    (hu : u ≫ q = p ≫ m) (hTF : TF ≫ p' = Φ.map p ≫ e.hom) (hTG : TG ≫ q' = Φ.map q ≫ e'.hom)
    (hv : v ≫ q' = p' ≫ m') (hm : Φ.map m ≫ e'.hom = e.hom ≫ m') :
    (Φ.map u ≫ TG) ≫ q' = (TF ≫ v) ≫ q' := by
  rw [Category.assoc, hTG, ← Φ.map_comp_assoc, hu, Φ.map_comp_assoc, hm, Category.assoc TF,
    hv, ← Category.assoc TF, hTF, Category.assoc]

/-- **The comparison on a term is natural in the complex.**  Both sides are maps into the fibre
product defining `η_{f^*I}(f^*G^•)` in degree `n`, so they agree as soon as their two projections
do; on each projection the square is the pullback of
`Stacks.IdealTorsion.Eta.etaTermMap_pullbackFst`, respectively
`Stacks.IdealTorsion.Eta.etaTermMap_pullbackSnd`, followed by the naturality
`Stacks.IdealTorsion.Eta.pullbackIdealPowerIso_natural` of the interchange of the pullback with
the ideal powers.

Stated at the `etaTerm` spelling, so that every object in sight is a fibre product; see
`Stacks.IdealTorsion.Eta.pullbackEtaMap_natural` for the statement about the maps of
complexes. -/
theorem pullbackEtaTermMap_natural (n : ℤ) :
    (pullbackFunctor f).map (etaTermMap Y I ι a n) ≫ pullbackEtaTermMap f I ι G n =
      pullbackEtaTermMap f I ι F n ≫
        etaTermMap X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) n := by
  -- As in `Stacks.IdealTorsion.Eta.pullbackEtaTermMap_comm`, the composites mix the category
  -- instance of the pullback functor's spelling of the structure sheaf with that of the décalage
  -- files, so `rw` cannot match them; each projection is assembled by `Eq.trans`, whose steps are
  -- `default`-transparency unifications.
  refine pullback.hom_ext
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ?_ ?_
  · exact map_comp_comparison_comp_eq (pullbackFunctor f)
      (etaTermMap_pullbackFst Y I ι a n) (pullbackEtaTermMap_fst f I ι F n)
      (pullbackEtaTermMap_fst f I ι G n)
      (etaTermMap_pullbackFst X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
        (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) n)
      (pullbackIdealPowerIso_natural f I n (a.f n))
  · exact map_comp_comparison_comp_eq (pullbackFunctor f)
      (etaTermMap_pullbackSnd Y I ι a n) (pullbackEtaTermMap_snd f I ι F n)
      (pullbackEtaTermMap_snd f I ι G n)
      (etaTermMap_pullbackSnd X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
        (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) n)
      (pullbackIdealPowerIso_natural f I (n + 1) (a.f (n + 1)))

/-- **The comparison of décalages under a pullback is natural in the complex**: for a map
`a : F^• ⟶ G^•` of complexes of `I`-torsion-free `𝒪_Y`-modules whose termwise pullbacks are
complexes of `f^*I`-torsion-free `𝒪_X`-modules, the square

`f^*(η_I F^•) ⟶ f^*(η_I G^•) ⟶ η_{f^*I}(f^*G^•)`,
`f^*(η_I F^•) ⟶ η_{f^*I}(f^*F^•) ⟶ η_{f^*I}(f^*G^•)`

commutes.  Degreewise this is
`Stacks.IdealTorsion.Eta.pullbackEtaTermMap_natural`.

No flatness is assumed.  This is what lets the comparison at an arbitrary complex be computed
from the comparison at a complex along which it is understood: composing with the décalage of a
quasi-isomorphism on one side is the same as pulling that quasi-isomorphism back on the
other. -/
theorem pullbackEtaMap_natural [Mono ι]
    [Mono (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf))
      (pullbackIdealIncl f I ι)]
    (hF : ∀ n : ℤ, IsIdealTorsionFree Y ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree Y ι (G.X n))
    (hF' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f F).X n))
    (hG' : ∀ n : ℤ, IsIdealTorsionFree X (pullbackIdealIncl f I ι)
      ((pullbackComplex f G).X n)) :
    ((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (etaMap Y I ι a hF hG) ≫
        pullbackEtaMap f I ι G hG hG' =
      pullbackEtaMap f I ι F hF hF' ≫
        etaMap X ((pullbackFunctor f).obj I) (pullbackIdealIncl f I ι)
          (((pullbackFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map a) hF' hG' :=
  HomologicalComplex.hom_ext _ _ fun n => pullbackEtaTermMap_natural f I ι a n

end Naturality

end Stacks.IdealTorsion.Eta

end
