module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafIdealInclSucc
public import StacksFrontier.CategoryTheory.Equivalence.PowObjIsoSelfNaturality

/-!
# The décalage by an ideal whose inclusion is invertible

Let `X` be a ringed space, let `I` be an invertible sheaf of `O_X`-modules and let `ι : I ⟶ O_X`
exhibit it as an ideal sheaf.  When `ι` is an *isomorphism* — the ideal is the unit ideal, up to
the identification `ι` provides — the Berthelot–Ogus décalage `η_I` does nothing: this file
produces an isomorphism of functors `η_I ≅ id` on complexes of `I`-torsion-free modules, and
descends it to `Lη_I ≅ id` on the derived category.

The geometric case is the one that matters: the ideal sheaf of an effective Cartier divisor
restricted to the complement of its support is the unit ideal, so the derived décalage attached
to a divisor is trivial away from that divisor.

## Main definitions

* `Stacks.IdealTorsion.Eta.idealUntwist`: for invertible `ι`, the isomorphism
  `I^{⊗ n} ⊗ M ≅ M` untwisting the `n`-th ideal power, for every integer `n`.
* `Stacks.IdealTorsion.Eta.etaObjIsoSelf`: the décalage of a complex of `I`-torsion-free modules
  is that complex.
* `Stacks.IdealTorsion.Eta.etaFunctorIsoSelf`: the same as an isomorphism of functors.
* `Stacks.IdealTorsion.Eta.derivedEtaIsoId`: **`Lη_I` is the identity functor of `D(O_X)`.**

## Main results

* `Stacks.IdealTorsion.Eta.isIso_idealPowerIncl_of_isIso`: when `ι` is invertible, so is every
  inclusion of consecutive ideal powers.
* `Stacks.IdealTorsion.Eta.idealUntwist_naturality` and
  `Stacks.IdealTorsion.Eta.idealPowerIncl_comp_idealUntwist`: the untwisting isomorphisms are
  natural in the module and form a compatible system along the inclusions.

## Implementation notes

The untwisting isomorphism is `Stacks.Equivalence.powObjIsoSelf` of
`StacksFrontier.CategoryTheory.Equivalence.PowObjIsoSelf`, applied to the autoequivalence "tensor
on the right by `I`" and to the family of isomorphisms `I ⊗ M ≅ M` the degree-`0` inclusion
provides.  Its two properties come from
`StacksFrontier.CategoryTheory.Equivalence.PowObjIsoSelfNaturality`; the only input they ask for is
the naturality of that degree-`0` family, which is proved here directly from the naturality of
the right unit constraint and the interchange law of the tensor product bifunctor.

The naturality of the right unit constraint is re-proved here rather than imported: the copies
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf` and in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafQuasiIso` are private to those modules.
The proof is the unitor square of the presheaf monoidal structure pushed forward by
sheafification, inserted into the naturality of the sheafification counit; every step is a term
rather than a rewrite, since the two spellings of the counit's source are unified only at
`default` transparency.

The degreewise term of `η_I F^•` is a fibre product one of whose legs is the inclusion of
consecutive ideal powers.  That leg being invertible, the other projection is invertible too,
and composing it with the untwisting isomorphism gives the degreewise comparison; the
compatibility of the differentials is then exactly the defining equation of the differential of
the décalage together with the two properties of the untwisting system.

The passage to the derived category is `CategoryTheory.Localization.liftNatIso` against
`Stacks.IdealTorsion.Eta.isLocalization_torsionFreeToDerived`: both `Lη_I` and the identity lift
the same functor to `D(O_X)` out of complexes of `I`-torsion-free modules, so they agree.

## References

* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 0GT4](https://stacks.math.columbia.edu/tag/0GT4)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

/- The same locally-unfoldable links as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheafDerived`: without them instance search
does not see through the spelling `structureSheaf X.sheaf` of the structure sheaf of rings. -/
attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.SheafOfModules.Invertible ( tensorRightFunctor_isEquivalence
  tensorPowerEquivalence   tensorProductRightUnitor)

universe u v w

namespace Stacks.IdealTorsion.Eta

/-! ### The inclusion in degree zero -/

variable (X : RingedSpace.{u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf
  (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf))
local notation "𝒪" => SheafOfModules.unit Oₓ

/-- **The degree-`0` inclusion of ideal powers is natural in the module.** It is the ideal
inclusion tensored into the module followed by the right unit constraint, so its naturality is
the interchange law of the tensor product bifunctor followed by the naturality of that
constraint. -/
theorem idealPowerIncl_zero_naturality (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {M N : SheafOfModules.{u} Oₓ} (f : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I).map f ≫
        idealPowerIncl X I ι 0 N =
      idealPowerIncl X I ι 0 M ≫ f := by
  let T := (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
    (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)))
  have hswapExplicit : T.map (X := (M, I)) (Y := (M, 𝒪)) (𝟙 _, ι) ≫
      T.map (X := (M, 𝒪)) (Y := (N, 𝒪)) (f, 𝟙 _) =
    T.map (X := (M, I)) (Y := (N, I)) (f, 𝟙 _) ≫
      T.map (X := (N, I)) (Y := (N, 𝒪)) (𝟙 _, ι) := by
    rw [← T.map_comp, ← T.map_comp]
    congr 1
  let cM : T.obj (M, I) ⟶ T.obj (M, 𝒪) := T.map (X := (M, I)) (Y := (M, 𝒪)) (𝟙 _, ι)
  let cN : T.obj (N, I) ⟶ T.obj (N, 𝒪) := T.map (X := (N, I)) (Y := (N, 𝒪)) (𝟙 _, ι)
  let s : T.obj (M, I) ⟶ T.obj (N, I) := T.map (X := (M, I)) (Y := (N, I)) (f, 𝟙 _)
  let t : T.obj (M, 𝒪) ⟶ T.obj (N, 𝒪) := T.map (X := (M, 𝒪)) (Y := (N, 𝒪)) (f, 𝟙 _)
  let rM := tensorProductRightUnitor X.sheaf.obj (Oₓ).property M
  let rN := tensorProductRightUnitor X.sheaf.obj (Oₓ).property N
  have hswap : cM ≫ t = s ≫ cN := hswapExplicit
  have hun : t ≫ rN.hom = rM.hom ≫ f :=
    tensorProductRightUnitor_naturality X.sheaf.obj (Oₓ).property f
  have hL : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I).map f ≫
      idealPowerIncl X I ι 0 N = s ≫ cN ≫ rN.hom :=
    (congrArg (fun morphism => ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I).map f ≫
          morphism)
      (idealPowerIncl_zero_eq_core X I ι N)).trans
        (congrArg (fun morphism => morphism ≫ cN ≫ rN.hom)
          ((congrArg (fun morphism =>
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
              (CategoryTheory.ObjectProperty.FullSubcategory.mk
                X.presheaf X.IsSheaf)).flip.obj I).map f ≫
              morphism)
            (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
              (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).obj N).map_id
              I)).trans
              (Category.comp_id _)).symm)
  have hR : idealPowerIncl X I ι 0 M ≫ f = (cM ≫ rM.hom) ≫ f :=
    congrArg (fun k => k ≫ f) (idealPowerIncl_zero_eq_core X I ι M)
  -- The objects of these composites carry two spellings of the ring sheaf, so every step is
  -- written as a term: `rw` and `simp` match below `default` transparency and do not fire.
  refine hL.trans (Eq.trans ?_ hR.symm)
  calc s ≫ cN ≫ rN.hom = (s ≫ cN) ≫ rN.hom := (Category.assoc _ _ _).symm
    _ = (cM ≫ t) ≫ rN.hom := congrArg (fun k => k ≫ rN.hom) hswap.symm
    _ = cM ≫ t ≫ rN.hom := Category.assoc _ _ _
    _ = cM ≫ rM.hom ≫ f := congrArg (cM ≫ ·) hun
    _ = (cM ≫ rM.hom) ≫ f := (Category.assoc _ _ _).symm

/-! ### Invertibility of the inclusions -/

/-- When the ideal inclusion is invertible, so is the part of the inclusion of consecutive ideal
powers that follows the successor comparison: it is the ideal inclusion tensored into a module,
which is an isomorphism because the bifunctor preserves them, followed by the right unit
constraint. -/
theorem isIso_idealPowerInclCore_of_isIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    IsIso (idealPowerInclCore X I ι n M) := by
  have hpair : IsIso (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
        (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)))).map
      (X := (idealPowerTerm X I n M, I)) (Y := (idealPowerTerm X I n M, 𝒪)) (𝟙 _, ι)) := by
    have : IsIso ((𝟙 (idealPowerTerm X I n M), ι) :
        (idealPowerTerm X I n M, I) ⟶ (idealPowerTerm X I n M, 𝒪)) :=
      (CategoryTheory.isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
    infer_instance
  rw [idealPowerInclCore]
  exact IsIso.comp_isIso' hpair (Iso.isIso_hom _)

/-- **When the ideal inclusion is invertible, so is every inclusion of consecutive ideal
powers.** -/
theorem isIso_idealPowerIncl_of_isIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    IsIso (idealPowerIncl X I ι n M) := by
  rw [idealPowerIncl_eq_core]
  exact IsIso.comp_isIso' (Iso.isIso_inv _) (isIso_idealPowerInclCore_of_isIso X I ι n M)

/-! ### Untwisting the ideal powers -/

/-- The degree-`0` inclusion of ideal powers, read as an isomorphism `I ⊗ M ≅ M`. -/
def idealPowerInclIso (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) :
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk
            X.presheaf X.IsSheaf)).property I)).functor.obj M ≅
      M :=
  @asIso _ _ _ _ (idealPowerIncl X I ι 0 M) (isIso_idealPowerIncl_of_isIso X I ι 0 M)

/-- The forward map of `idealPowerInclIso` is the degree-`0` inclusion `idealPowerIncl`. -/
@[simp] theorem idealPowerInclIso_hom (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) :
    (idealPowerInclIso X I ι M).hom = idealPowerIncl X I ι 0 M := rfl

/-- **Untwisting the `n`-th ideal power.** When the ideal inclusion is invertible, so is each
inclusion of consecutive ideal powers, and composing them identifies `I^{⊗ n} ⊗ M` with `M` in
every integer degree. -/
def idealUntwist (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    idealPowerTerm X I n M ≅ M :=
  Stacks.Equivalence.powObjIsoSelf
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).property I))
    (idealPowerInclIso X I ι) n M

/-- **The untwisting isomorphisms are natural in the module.** -/
theorem idealUntwist_naturality (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (n : ℤ) {M N : SheafOfModules.{u} Oₓ} (f : M ⟶ N) :
    idealPowerMap X I n f ≫ (idealUntwist X I ι n N).hom =
      (idealUntwist X I ι n M).hom ≫ f :=
  Stacks.Equivalence.powObjIsoSelf_naturality
    (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).property I))
    (idealPowerInclIso X I ι)
    (fun {_ _} g => idealPowerIncl_zero_naturality X I ι g) n f

/-- **The untwisting isomorphisms form a compatible system along the inclusions**: untwisting
the `(n + 1)`-st ideal power is including it into the `n`-th and untwisting that. -/
theorem idealPowerIncl_comp_idealUntwist (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    idealPowerIncl X I ι n M ≫ (idealUntwist X I ι n M).hom =
      (idealUntwist X I ι (n + 1) M).hom :=
  (congrArg (fun k => k ≫ (idealUntwist X I ι n M).hom)
      (idealPowerIncl_eq_powSuccIso_inv_comp X I ι n M)).trans
    (Stacks.Equivalence.powObjIsoSelf_succIso
      (@Functor.asEquivalence _ _ _ _
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
          (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).flip.obj I)
      (tensorRightFunctor_isEquivalence X.sheaf.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (CategoryTheory.ObjectProperty.FullSubcategory.mk X.presheaf X.IsSheaf)).property I))
      (idealPowerInclIso X I ι) n M)

/-! ### The décalage of a complex is that complex -/

/-- Untwisting after the image of `f` under the `n`-th ideal power is `f` after untwisting. -/
private theorem comp_idealPowerMap_comp_idealUntwist (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [IsIso ι] [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I] (n : ℤ)
    {A : SheafOfModules.{u} Oₓ} {M N : SheafOfModules.{u} Oₓ} {h : A ⟶ idealPowerTerm X I n M}
    (f : M ⟶ N) :
    (h ≫ idealPowerMap X I n f) ≫ (idealUntwist X I ι n N).hom =
      (h ≫ (idealUntwist X I ι n M).hom) ≫ f := by
  rw [Category.assoc, Category.assoc, idealUntwist_naturality]

/-- The differential of `η_I F^•` followed by the first projection in the next degree is the
second projection. -/
theorem etaObj_d_fst_eq_etaSnd (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaObj X I ι F hF).d n (n + 1) ≫ etaFst X I ι F (n + 1) = etaSnd X I ι F n := by
  have hd : (etaObj X I ι F hF).d n (n + 1) = (etaDifferentialData X I ι F hF).d n := by
    simp only [etaObj, CochainComplex.of_d]
  rw [hd]
  exact (etaDifferentialData X I ι F hF).d_fst n

/-- The degree-`n` term of the décalage is the degree-`n` term of the complex: one leg of the
defining fibre product is the inclusion of consecutive ideal powers, which is invertible, so the
other projection is invertible too, and the twist it lands in is untwisted by
`Stacks.IdealTorsion.Eta.idealUntwist`. -/
def etaTermIsoSelf (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι] [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    etaTerm X I ι F n ≅ F.X n :=
  haveI : IsIso (idealPowerIncl X I ι n (F.X (n + 1))) :=
    isIso_idealPowerIncl_of_isIso X I ι n (F.X (n + 1))
  asIso (etaFst X I ι F n) ≪≫ idealUntwist X I ι n (F.X n)

/-- The forward map of `etaTermIsoSelf` is the first projection `etaFst` followed by the
untwisting isomorphism `idealUntwist`. -/
theorem etaTermIsoSelf_hom (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι] [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ) (n : ℤ) :
    (etaTermIsoSelf X I ι F n).hom =
      etaFst X I ι F n ≫ (idealUntwist X I ι n (F.X n)).hom := rfl

/-- The degreewise identifications are compatible with the differentials: this is the defining
equation of the differential of the décalage together with the two properties of the untwisting
system. -/
theorem etaTermIsoSelf_comm (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι] [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaTermIsoSelf X I ι F n).hom ≫ F.d n (n + 1) =
      (etaObj X I ι F hF).d n (n + 1) ≫ (etaTermIsoSelf X I ι F (n + 1)).hom := by
  have hcond : etaFst X I ι F n ≫ idealPowerMap X I n (F.d n (n + 1)) =
      etaSnd X I ι F n ≫ idealPowerIncl X I ι n (F.X (n + 1)) := pullback.condition
  have main : (etaFst X I ι F n ≫ (idealUntwist X I ι n (F.X n)).hom) ≫ F.d n (n + 1) =
      etaSnd X I ι F n ≫ (idealUntwist X I ι (n + 1) (F.X (n + 1))).hom :=
    calc (etaFst X I ι F n ≫ (idealUntwist X I ι n (F.X n)).hom) ≫ F.d n (n + 1)
        = (etaFst X I ι F n ≫ idealPowerMap X I n (F.d n (n + 1))) ≫
            (idealUntwist X I ι n (F.X (n + 1))).hom :=
          (comp_idealPowerMap_comp_idealUntwist X I ι n _).symm
      _ = (etaSnd X I ι F n ≫ idealPowerIncl X I ι n (F.X (n + 1))) ≫
            (idealUntwist X I ι n (F.X (n + 1))).hom :=
          congrArg (fun k => k ≫ (idealUntwist X I ι n (F.X (n + 1))).hom) hcond
      _ = etaSnd X I ι F n ≫ (idealUntwist X I ι (n + 1) (F.X (n + 1))).hom := by
          rw [Category.assoc, idealPowerIncl_comp_idealUntwist]
  exact main.trans
    ((congrArg (fun k => k ≫ (idealUntwist X I ι (n + 1) (F.X (n + 1))).hom)
        (etaObj_d_fst_eq_etaSnd X I ι F hF n)).symm.trans
      (Category.assoc _ _ _))

/-- **The décalage by an ideal whose inclusion is invertible does nothing.** -/
def etaObjIsoSelf (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι] [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) :
    etaObj X I ι F hF ≅ F :=
  HomologicalComplex.Hom.isoOfComponents (fun n => etaTermIsoSelf X I ι F n)
    (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact etaTermIsoSelf_comm X I ι F hF i)

/-- In each degree `n`, the forward map of `etaObjIsoSelf` is that of `etaTermIsoSelf`. -/
theorem etaObjIsoSelf_hom_f (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι] [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (F : CochainComplex (SheafOfModules.{u} Oₓ) ℤ)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n)) (n : ℤ) :
    (etaObjIsoSelf X I ι F hF).hom.f n = (etaTermIsoSelf X I ι F n).hom := rfl

/-- The identification of the décalage with the complex is natural in the complex. -/
theorem etaMap_comp_etaObjIsoSelf (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι] [IsIso ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    {F G : CochainComplex (SheafOfModules.{u} Oₓ) ℤ} (a : F ⟶ G)
    (hF : ∀ n : ℤ, IsIdealTorsionFree X ι (F.X n))
    (hG : ∀ n : ℤ, IsIdealTorsionFree X ι (G.X n)) :
    etaMap X I ι a hF hG ≫ (etaObjIsoSelf X I ι G hG).hom =
      (etaObjIsoSelf X I ι F hF).hom ≫ a := by
  apply HomologicalComplex.hom_ext
  intro n
  -- As above, the composite of the induced map with the projection is type-correct only at
  -- `default` transparency, so the two outer steps are terms rather than rewrites.
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (idealUntwist X I ι n (G.X n)).hom)
      (etaMap_fst X I ι a hF hG n)).trans
      (comp_idealPowerMap_comp_idealUntwist X I ι n _))

/-- **The décalage functor by an ideal whose inclusion is invertible is the inclusion of
complexes of `I`-torsion-free modules**, that is, the identity up to that inclusion. -/
def etaFunctorIsoSelf (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [monoIncl : Mono ι] [isoIncl : IsIso ι]
    [invertibleIdeal : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    : @etaFunctor X I ι monoIncl invertibleIdeal ≅ torsionFreeComplex X ι :=
  NatIso.ofComponents
    (fun F => @etaObjIsoSelf X I ι monoIncl isoIncl invertibleIdeal
      ((torsionFreeComplex X ι).obj F)
      (torsionFreeComplex_torsionFree X ι F))
    (fun {_ _} a => @etaMap_comp_etaObjIsoSelf X I ι monoIncl isoIncl invertibleIdeal _ _
      ((torsionFreeComplex X ι).map a) _ _)

/-! ### The derived décalage -/

attribute [local instance] HasDerivedCategory.standard

/-- **The derived décalage by an ideal whose inclusion is invertible is the identity functor of
`D(O_X)`.**  Both it and the identity lift the passage from complexes of `I`-torsion-free
modules to `D(O_X)`, which is a localization, so they agree. -/
def derivedEtaIsoId (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [monoIncl : Mono ι] [isoIncl : IsIso ι]
    [invertibleIdeal : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (hres : HasTorsionFreeResolutions X ι) :
    @derivedEta X I ι monoIncl invertibleIdeal hres ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} Oₓ)) :=
  letI := isLocalization_torsionFreeToDerived X ι hres
  letI : Localization.Lifting (torsionFreeToDerived X ι) (torsionFreeQuasiIso X ι)
      (@etaFunctor X I ι monoIncl invertibleIdeal ⋙ DerivedCategory.Q)
      (@derivedEta X I ι monoIncl invertibleIdeal hres) :=
    ⟨@derivedEta_iso X I ι monoIncl invertibleIdeal hres⟩
  Localization.liftNatIso (torsionFreeToDerived X ι) (torsionFreeQuasiIso X ι)
    (@etaFunctor X I ι monoIncl invertibleIdeal ⋙ DerivedCategory.Q) (torsionFreeToDerived X ι)
    (@derivedEta X I ι monoIncl invertibleIdeal hres) (𝟭 _)
    (Functor.isoWhiskerRight (@etaFunctorIsoSelf X I ι monoIncl isoIncl invertibleIdeal)
      DerivedCategory.Q)

end Stacks.IdealTorsion.Eta

end
