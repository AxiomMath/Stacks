module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafPullbackInclInt

/-!
# Transport of the décalage along a compatible isomorphism of ideal sheaves

Let `Z` be a ringed space and let `I, J ⊆ 𝒪_Z` be two invertible ideal sheaves, given by their
inclusions `ι : I ⟶ 𝒪_Z` and `κ : J ⟶ 𝒪_Z`.  Suppose `e : I ≅ J` is *compatible* with those
inclusions, in the sense that `e.hom ≫ κ = ι`: the two ideals are the same subsheaf of `𝒪_Z`,
presented twice.  Then the two décalages agree, and this file produces the identification at
every level of the construction:

* on the invertible ideal powers `I^{⊗ n} ⊗ M`;
* on the degreewise terms `η_I F^•` of the chain-level décalage;
* on the complex `η_I F^•` itself;
* and on the derived décalage `Lη_I` of [Stacks, Tag 0F8Q], at an object of `D(𝒪_Z)` represented
  by a complex of `I`-torsion-free modules.

The décalage is indexed by an inclusion `I ⟶ 𝒪_Z` rather than by the subsheaf it cuts out, so
two presentations of one ideal have to be compared explicitly.  In [Stacks, Tag 0F9X], for
instance, the pullback comparison `Stacks.IdealTorsion.Eta.pullbackDerivedEtaMap` lands in
`Lη_{h^*I_D}` while the statement concerns `Lη_{I_E}` with `E = h^{-1}D`, and the two ideals are
identified by a compatible isomorphism.

## Main definitions

* `Stacks.IdealTorsion.Eta.IdealCongr.powerIso`: **`I^{⊗ n} ⊗ M ≅ J^{⊗ n} ⊗ M` for every
  `n : ℤ`**, obtained from `e` by `Stacks.Equivalence.powIntertwineObj` along the *identity*
  functor.
* `Stacks.IdealTorsion.Eta.IdealCongr.etaTermMap` and
  `Stacks.IdealTorsion.Eta.IdealCongr.etaTermIso`: the comparison on the degree-`n` term of the
  décalage, and the fact that it is invertible.
* `Stacks.IdealTorsion.Eta.IdealCongr.etaIso`: **`η_I F^• ≅ η_J F^•`** as cochain complexes.
* `Stacks.IdealTorsion.Eta.IdealCongr.derivedEtaIso`: **`Lη_I [F^•] ≅ Lη_J [F^•]`** in
  `D(𝒪_Z)`.

## Main results

* `Stacks.IdealTorsion.Eta.IdealCongr.idealPowerAnnihilatorSubsheaf_eq` and
  `Stacks.IdealTorsion.Eta.IdealCongr.isIdealTorsionFree_congr`: **torsion-freeness does not
  distinguish the two presentations.**  The annihilator subsheaf is a supremum over a family of
  submodule subsheaves cut out by a condition on the sections of the ideal, and a compatible
  isomorphism matches those families; so the two suprema, hence the two torsion-freeness
  conditions, agree.
* `Stacks.IdealTorsion.Eta.IdealCongr.powerIso_natural` and
  `Stacks.IdealTorsion.Eta.IdealCongr.powerIso_idealPowerIncl`: the two squares that identify
  the cospans defining the two degreewise terms.

## Implementation notes

**No flatness, and no choice.**  Every comparison below is an isomorphism outright: the
transport is along an isomorphism of ideals on one and the same space, so none of the
exactness that the *pullback* comparison needs is in play.  In particular
`Stacks.IdealTorsion.Eta.IdealCongr.etaTermMap` is invertible with no hypothesis, where its
pullback counterpart `Stacks.IdealTorsion.Eta.pullbackEtaTermMap` needs `f` to be flat.

**The identity functor as the intertwiner.**  The passage from the degree-`1` comparison
`M ⊗ I ≅ M ⊗ J` to every integer degree is `Stacks.Equivalence.powIntertwineObj`, applied with
`R = 𝟭`; the two autoequivalences are `- ⊗ I` and `- ⊗ J`, which are genuinely different, so
this is not a degenerate instance.  `Stacks.SheafOfModules.TensorPower.tensorPowerCongr`
transports the tensor *powers* of the ideal itself in the same way; here the powers *act on a
module*, and the transport is compatible with `Stacks.IdealTorsion.Eta.idealPowerMap` and with
`Stacks.IdealTorsion.Eta.idealPowerIncl`.

The degree-`1` comparison is the curried tensor functor at `M` applied to `e`:
`((Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf).obj M).mapIso e`. Its naturality is the
naturality square of the bifunctor's map, and compatibility with the ideal inclusion follows
from the same functor's composition law.

**Torsion-freeness is transported rather than assumed.**  Both décalages ask for the terms of
`F^•` to be torsion-free, each for its own ideal, so the complex-level comparison takes both
hypotheses.  They are equivalent, by
`Stacks.IdealTorsion.Eta.IdealCongr.isIdealTorsionFree_congr`, and since they are propositions
the décalage does not depend on which proof is supplied.

## References

* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Invertible (
  tensorProductRightUnitor)

universe u

namespace Stacks.IdealTorsion.Eta.IdealCongr

variable (Z : RingedSpace.{u})

/-! ### Torsion-freeness depends only on the ideal, not on its presentation -/

/-- The section map of an ideal inclusion which factors through another one is the second one
precomputed with the factoring morphism.  This is the composition law for a morphism of sheaves
of modules read off on sections. -/
theorem idealSection_comp
    {I J : SheafOfModules.{u} (structureSheafRing Z)}
    (κ : J ⟶ SheafOfModules.unit
      (structureSheafRing Z))
    (g : I ⟶ J) (U : (TopologicalSpace.Opens Z)ᵒᵖ) (a : I.val.obj U) :
    Stacks.IdealTorsion.idealSection Z (g ≫ κ) U a =
      Stacks.IdealTorsion.idealSection Z κ U ((g.val.app U).hom a) :=
  rfl

/-- **The defining family of the `κ`-annihilator is contained in that of the `ι`-annihilator**
whenever `ι` factors as `g ≫ κ`.  A product of sections of `I` is a product of sections of `J`,
namely of their images under `g`, so a submodule subsheaf killed by every product of `n` sections
of `J` is killed by every product of `n` sections of `I`. -/
theorem annihilatorFamily_subset
    {I J : SheafOfModules.{u} (structureSheafRing Z)}
    (ι : I ⟶ SheafOfModules.unit
      (structureSheafRing Z))
    (κ : J ⟶ SheafOfModules.unit
      (structureSheafRing Z))
    (g : I ⟶ J) (hg : g ≫ κ = ι)
    (F : SheafOfModules.{u} (structureSheafRing Z))
    (n : ℕ) :
    { N : F.Submodule | ∀ (U : (TopologicalSpace.Opens Z)ᵒᵖ) (s : F.val.obj U),
        s ∈ N.toSubmodule.obj U →
          ∀ (V : TopologicalSpace.Opens Z) (hVU : V ≤ Opposite.unop U)
            (b : Fin n → J.val.obj (Opposite.op V)),
            (∏ k, Stacks.IdealTorsion.idealSection Z κ (Opposite.op V) (b k)) •
              (F.val.map (homOfLE hVU).op).hom s = 0 } ⊆
      { N : F.Submodule | ∀ (U : (TopologicalSpace.Opens Z)ᵒᵖ) (s : F.val.obj U),
        s ∈ N.toSubmodule.obj U →
          ∀ (V : TopologicalSpace.Opens Z) (hVU : V ≤ Opposite.unop U)
            (a : Fin n → I.val.obj (Opposite.op V)),
            (∏ k, Stacks.IdealTorsion.idealSection Z ι (Opposite.op V) (a k)) •
              (F.val.map (homOfLE hVU).op).hom s = 0 } := by
  subst hg
  intro N h U s hs V hVU a
  simpa only [idealSection_comp] using
    h U s hs V hVU (fun k => (g.val.app (Opposite.op V)).hom (a k))

/-- **A compatible isomorphism of ideals gives the same annihilator subsheaves.**  Each of the
two defining families contains the other, by `annihilatorFamily_subset` applied to `e.hom` and to
`e.inv`, so the two suprema coincide. -/
theorem idealPowerAnnihilatorSubsheaf_eq
    {I J : SheafOfModules.{u} (structureSheafRing Z)}
    (ι : I ⟶ SheafOfModules.unit
      (structureSheafRing Z))
    (κ : J ⟶ SheafOfModules.unit
      (structureSheafRing Z))
    (e : I ≅ J) (he : e.hom ≫ κ = ι)
    (F : SheafOfModules.{u} (structureSheafRing Z))
    (n : ℕ) :
    Stacks.IdealTorsion.idealPowerAnnihilatorSubsheaf Z ι F n =
      Stacks.IdealTorsion.idealPowerAnnihilatorSubsheaf Z κ F n := by
  have he2 : e.inv ≫ ι = κ := by rw [← he, Iso.inv_hom_id_assoc]
  let _ : CompleteLattice F.Submodule := SheafOfModules.Submodule.instCompleteLattice
  change sSup _ = sSup _
  rw [Set.Subset.antisymm (annihilatorFamily_subset Z κ ι e.inv he2 F n)
    (annihilatorFamily_subset Z ι κ e.hom he F n)]

/-- **Torsion-freeness is the same condition for two compatible presentations of one ideal.** -/
theorem isIdealTorsionFree_congr
    {I J : SheafOfModules.{u} (structureSheafRing Z)}
    (ι : I ⟶ SheafOfModules.unit
      (structureSheafRing Z))
    (κ : J ⟶ SheafOfModules.unit
      (structureSheafRing Z))
    (e : I ≅ J) (he : e.hom ≫ κ = ι)
    (F : SheafOfModules.{u} (structureSheafRing Z)) :
    Stacks.IdealTorsion.IsIdealTorsionFree Z ι F ↔
      Stacks.IdealTorsion.IsIdealTorsionFree Z κ F := by
  simp only [Stacks.IdealTorsion.IsIdealTorsionFree,
    idealPowerAnnihilatorSubsheaf_eq Z ι κ e he F 1]

/-! ### The transported ideal powers -/

variable (I J : SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))

variable [invertibleSource : Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))).property I]
  [invertibleTarget : Stacks.SheafOfModules.IsInvertible Z.sheaf.obj
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))).property J]

/-- **The degree-`1` comparison `M ⊗ I ≅ M ⊗ J`**, the native tensor functor at `M` applied
to the isomorphism of ideals. -/
def tensorIso (e : I ≅ J) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj I).obj M ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf
          Z.IsSheaf)).flip.obj J).obj M :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).obj M).mapIso e

/-- **The transported invertible ideal powers**: `I^{⊗ n} ⊗ M ≅ J^{⊗ n} ⊗ M`, for every integer
`n`.  The degree-`1` comparison `tensorIso` is transported to every integer iterate of the two
tensoring autoequivalences by `Stacks.Equivalence.powIntertwineObj`, along the identity
functor. -/
def powerIso (e : I ≅ J) (n : ℤ) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))) :
    idealPowerTerm Z I n M ≅ idealPowerTerm Z J n M :=
  Stacks.Equivalence.powIntertwineObj
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj I)
      (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Z.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).property I))
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj J)
      (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Z.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).property J))
    (𝟭 _) (fun P => tensorIso Z I J e P) n M

/-- In degree `0` the transport is the identity: the zeroth ideal power is the module itself. -/
theorem powerIso_zero (e : I ≅ J) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))) :
    powerIso Z I J e 0 M = Iso.refl M :=
  rfl

/-- In degree `1` the transport is the degree-`1` comparison, so it involves no choice beyond the
functoriality of the tensor product in the ideal. -/
theorem powerIso_one (e : I ≅ J) (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
    (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))) :
    powerIso Z I J e 1 M = tensorIso Z I J e M :=
  rfl

/-- **The transport is natural in the module**, in every integer degree.  The degree-`1` case is
the functoriality of the tensor product bifunctor on the two factorizations of `(b, e.hom)`, and
`Stacks.Equivalence.powIntertwineObj_naturality` supplies every other degree. -/
theorem powerIso_natural (e : I ≅ J) (n : ℤ)
    {M N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))} (a : M ⟶ N) :
    idealPowerMap Z I n a ≫ (powerIso Z I J e n N).hom =
      (powerIso Z I J e n M).hom ≫ idealPowerMap Z J n a := by
  refine Stacks.Equivalence.powIntertwineObj_naturality
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj I)
      (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Z.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).property I))
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj J)
      (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Z.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).property J))
    (𝟭 _) (fun P => tensorIso Z I J e P) (fun {P Q} b => ?_) n a
  let tensor := Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)
  exact ((tensor.map b).naturality e.hom).symm

/-- **The transport respects the inclusion of consecutive ideal powers**, in every integer
degree.

This is `Stacks.Equivalence.powIntertwineObj_incl` at the two tensoring autoequivalences, the
identity functor, the degree-`1` comparison, and `Stacks.IdealTorsion.Eta.idealInclNatTrans` for
`ι` and for `κ` as the two natural transformations to the identity.  Its hypothesis, the
degree-`0` case, is the functoriality of the tensor product bifunctor together with
`e.hom ≫ κ = ι`. -/
theorem powerIso_idealPowerIncl
    (ι : I ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    (κ : J ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
    (e : I ≅ J) (he : e.hom ≫ κ = ι) (n : ℤ)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))) :
    idealPowerIncl Z I ι n M ≫ (powerIso Z I J e n M).hom =
      (powerIso Z I J e (n + 1) M).hom ≫ idealPowerIncl Z J κ n M := by
  rw [idealPowerIncl_eq_powSuccIso_inv_comp Z I ι n M,
    idealPowerIncl_eq_powSuccIso_inv_comp Z J κ n M]
  refine Stacks.Equivalence.powIntertwineObj_incl
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj I)
      (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Z.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).property I))
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).flip.obj J)
      (Stacks.SheafOfModules.Invertible.tensorRightFunctor_isEquivalence Z.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).property J))
    (𝟭 _) (fun P => tensorIso Z I J e P)
    (idealInclNatTrans Z I ι) (idealInclNatTrans Z J κ) (fun P => ?_) n M
  rw [idealInclNatTrans_app, idealInclNatTrans_app, idealPowerIncl_zero_eq_core,
    idealPowerIncl_zero_eq_core]
  let tensor := Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)
  let rightUnitor := (tensorProductRightUnitor Z.sheaf.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)).property P).hom
  change ((tensor.map (𝟙 P)).app I ≫ (tensor.obj P).map ι) ≫ rightUnitor =
    (tensor.obj P).map e.hom ≫
      ((tensor.map (𝟙 P)).app J ≫ (tensor.obj P).map κ) ≫ rightUnitor
  simp only [tensor.map_id, NatTrans.id_app, Category.id_comp]
  rw [← he, Functor.map_comp]
  exact Category.assoc _ _ _

/-! ### The degreewise terms of the décalage -/

variable (ι : I ⟶ SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
  (κ : J ⟶ SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf))))
  (e : I ≅ J) (he : e.hom ≫ κ = ι)
  (F : CochainComplex (SheafOfModules.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (CategoryTheory.ObjectProperty.FullSubcategory.mk Z.presheaf Z.IsSheaf)))) ℤ)

include he in
/-- The two projections of the degree-`n` fibre product, composed with the transport of the ideal
powers, form a cone on the cospan defining the degree-`n` term of `η_J F^•`.

The square for the twisted differential is `powerIso_natural` and the square for the inclusion of
consecutive ideal powers is `powerIso_idealPowerIncl`; between them sits the defining condition
of the fibre product for `η_I F^•`. -/
theorem etaTerm_cone_condition (n : ℤ) :
    (etaFst Z I ι F n ≫ (powerIso Z I J e n (F.X n)).hom) ≫
        idealPowerMap Z J n (F.d n (n + 1)) =
      (etaSnd Z I ι F n ≫ (powerIso Z I J e (n + 1) (F.X (n + 1))).hom) ≫
        idealPowerIncl Z J κ n (F.X (n + 1)) := by
  rw [Category.assoc, ← powerIso_natural Z I J e n (F.d n (n + 1)), ← Category.assoc,
    pullback.condition, Category.assoc, powerIso_idealPowerIncl Z I J ι κ e he n (F.X (n + 1)),
    Category.assoc]

include he in
/-- **The comparison of décalages on a term, for a compatible isomorphism of ideals.** -/
def etaTermMap (n : ℤ) : etaTerm Z I ι F n ⟶ etaTerm Z J κ F n :=
  pullback.lift (etaFst Z I ι F n ≫ (powerIso Z I J e n (F.X n)).hom)
    (etaSnd Z I ι F n ≫ (powerIso Z I J e (n + 1) (F.X (n + 1))).hom)
    (etaTerm_cone_condition Z I J ι κ e he F n)

/-- The first projection of the comparison on a term. -/
theorem etaTermMap_fst (n : ℤ) :
    etaTermMap Z I J ι κ e he F n ≫ etaFst Z J κ F n =
      etaFst Z I ι F n ≫ (powerIso Z I J e n (F.X n)).hom :=
  pullback.lift_fst _ _ _

/-- The second projection of the comparison on a term. -/
theorem etaTermMap_snd (n : ℤ) :
    etaTermMap Z I J ι κ e he F n ≫ etaSnd Z J κ F n =
      etaSnd Z I ι F n ≫ (powerIso Z I J e (n + 1) (F.X (n + 1))).hom :=
  pullback.lift_snd _ _ _

include he in
/-- **The comparison of décalages on a term is an isomorphism**, with no hypothesis: the two
cospans defining the fibre products are isomorphic, by `powerIso_natural` and
`powerIso_idealPowerIncl`. -/
def etaTermIso (n : ℤ) : etaTerm Z I ι F n ≅ etaTerm Z J κ F n :=
  asIso (pullback.map _ _ (idealPowerMap Z J n (F.d n (n + 1)))
    (idealPowerIncl Z J κ n (F.X (n + 1)))
    (powerIso Z I J e n (F.X n)).hom
    (powerIso Z I J e (n + 1) (F.X (n + 1))).hom
    (powerIso Z I J e n (F.X (n + 1))).hom
    (powerIso_natural Z I J e n (F.d n (n + 1)))
    (powerIso_idealPowerIncl Z I J ι κ e he n (F.X (n + 1))))

/-- The isomorphism of terms is the canonical comparison map: both are maps into a fibre product
and their two projections agree. -/
theorem etaTermIso_hom_eq (n : ℤ) :
    (etaTermIso Z I J ι κ e he F n).hom = etaTermMap Z I J ι κ e he F n := by
  refine pullback.hom_ext ?_ ?_
  · rw [etaTermMap_fst, etaTermIso, asIso_hom, pullback.lift_fst]
  · rw [etaTermMap_snd, etaTermIso, asIso_hom, pullback.lift_snd]

/-- **The comparison of décalages on a term is an isomorphism.** -/
theorem isIso_etaTermMap (n : ℤ) : IsIso (etaTermMap Z I J ι κ e he F n) := by
  rw [← etaTermIso_hom_eq Z I J ι κ e he F n]
  exact (etaTermIso Z I J ι κ e he F n).isIso_hom

/-! ### The décalage as a complex, and in the derived category -/

variable [monoSource : Mono ι] [monoTarget : Mono κ]
  (hF : ∀ n : ℤ, IsIdealTorsionFree Z ι (F.X n))
  (hF' : ∀ n : ℤ, IsIdealTorsionFree Z κ (F.X n))

/-- The comparison on terms commutes with the differentials of the two décalages. -/
theorem etaTermMap_comm (n : ℤ) :
    etaTermMap Z I J ι κ e he F n ≫ (etaDifferentialData Z J κ F hF').d n =
      (etaDifferentialData Z I ι F hF).d n ≫ etaTermMap Z I J ι κ e he F (n + 1) := by
  let sourceData := etaDifferentialData Z I ι F hF
  let targetData := etaDifferentialData Z J κ F hF'
  have sourceZero : sourceData.d n ≫
      pullback.snd (idealPowerMap Z I (n + 1) (F.d (n + 1) ((n + 1) + 1)))
        (idealPowerIncl Z I ι (n + 1) (F.X ((n + 1) + 1))) = 0 := by
    rw [← sourceData.d_fst (n + 1), ← Category.assoc, sourceData.d_comp_d, zero_comp]
  have targetZero : targetData.d n ≫
      pullback.snd (idealPowerMap Z J (n + 1) (F.d (n + 1) ((n + 1) + 1)))
        (idealPowerIncl Z J κ (n + 1) (F.X ((n + 1) + 1))) = 0 := by
    rw [← targetData.d_fst (n + 1), ← Category.assoc, targetData.d_comp_d, zero_comp]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, (etaDifferentialData Z J κ F hF').d_fst n, etaTermMap_snd,
      Category.assoc, etaTermMap_fst, ← Category.assoc, (etaDifferentialData Z I ι F hF).d_fst n]
  · rw [Category.assoc, targetZero, comp_zero,
      Category.assoc, etaTermMap_snd, ← Category.assoc,
      sourceZero, zero_comp]

include he in
/-- **The comparison of décalages as a map of cochain complexes**: `η_I F^• ⟶ η_J F^•`, for a
compatible isomorphism `I ≅ J` of ideal sheaves. -/
def etaMap : etaObj Z I ι F hF ⟶ etaObj Z J κ F hF' where
  f n := etaTermMap Z I J ι κ e he F n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    simpa only [etaObj, CochainComplex.of_d] using etaTermMap_comm Z I J ι κ e he F hF hF' i

/-- The degree-`n` component of the comparison of complexes is the comparison on the term. -/
theorem etaMap_f (n : ℤ) : (etaMap Z I J ι κ e he F hF hF').f n = etaTermMap Z I J ι κ e he F n :=
  rfl

include he in
/-- **`η_I F^• ≅ η_J F^•` for a compatible isomorphism of ideal sheaves**, with no hypothesis
beyond the compatibility: a map of complexes invertible in every degree is invertible. -/
def etaIso : etaObj Z I ι F hF ≅ etaObj Z J κ F hF' :=
  have (n : ℤ) : IsIso ((etaMap Z I J ι κ e he F hF hF').f n) :=
    isIso_etaTermMap Z I J ι κ e he F n
  have := HomologicalComplex.Hom.isIso_of_components (etaMap Z I J ι κ e he F hF hF')
  asIso (etaMap Z I J ι κ e he F hF hF')

/-- The underlying map of the isomorphism of complexes is the canonical comparison. -/
theorem etaIso_hom : (etaIso Z I J ι κ e he F hF hF').hom = etaMap Z I J ι κ e he F hF hF' :=
  rfl

/-! ### The derived décalage -/

attribute [local instance] HasDerivedCategory.standard

include he in
/-- **`Lη_I [F^•] ≅ Lη_J [F^•]` for a compatible isomorphism of ideal sheaves.**

At an object of `D(𝒪_Z)` represented by a complex `F^•` of torsion-free modules both derived
décalages are the class of the corresponding chain-level décalage, by
`Stacks.IdealTorsion.Eta.derivedEta_iso` — the morphism clause of [Stacks, Tag 0F8Q], a natural
isomorphism — and the two chain-level décalages are identified by
`Stacks.IdealTorsion.Eta.IdealCongr.etaIso`. -/
def derivedEtaIso (hres : HasTorsionFreeResolutions Z ι) (hres' : HasTorsionFreeResolutions Z κ) :
    (@derivedEta Z I ι monoSource invertibleSource hres).obj (DerivedCategory.Q.obj F) ≅
      (@derivedEta Z J κ monoTarget invertibleTarget hres').obj (DerivedCategory.Q.obj F) :=
  (@derivedEta_iso Z I ι monoSource invertibleSource hres).app
      (HomologicalComplex.liftObjectProperty (torsionFreeProperty Z ι) F hF) ≪≫
    DerivedCategory.Q.mapIso (etaIso Z I J ι κ e he F hF hF') ≪≫
    ((@derivedEta_iso Z J κ monoTarget invertibleTarget hres').app
      (HomologicalComplex.liftObjectProperty (torsionFreeProperty Z κ) F hF')).symm

end Stacks.IdealTorsion.Eta.IdealCongr

end
