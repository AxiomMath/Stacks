module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorBraiding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoCompositionModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoOfIso

/-!
# The comparison of Stacks 07A4 along isomorphic morphisms of ringed topoi

Let `φ, ψ : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be morphisms of ringed topoi presented by continuous
functors of sites which are morphisms of sites, and let `e : ψ.u ≅ φ.u` be an isomorphism of the
underlying functors carrying the structure map of `φ` to that of `ψ`. The derived pullbacks are
then isomorphic,
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackIsoOfIso : Lφ^* ≅ Lψ^*`.
This file proves that this isomorphism is compatible with the comparisons

`Lφ^*(K ⊗^L L) ≅ Lφ^*K ⊗^L Lφ^*L`, `Lψ^*(K ⊗^L L) ≅ Lψ^*K ⊗^L Lψ^*L`

of [Stacks, Tag 07A4] (`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`).

## Main definitions

* `Stacks.Sheaves.DerivedPullback.pullbackComplexIsoOfIso` — `φ^* ≅ ψ^*` read degreewise on
  cochain complexes.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackComplexIsoOfIso_comp_pullbackToposTensorTotalIso` —
  the comparison `f^*Tot(K ⊗ L) ≅ Tot(f^*K ⊗ f^*L)` of [Stacks, Tag 03EL] is compatible with
  `φ^* ≅ ψ^*`, for arbitrary complexes.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackIsoOfIso_hom_app_comp_pullbackComparisonQ` —
  the comparison `Lf^*(QM) ⟶ Q(f^*M)` of [Stacks, Tag 06YY] is compatible with the two
  isomorphisms.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_isoOfIso` and
  `DerivedPullback.derivedPullbackIsoOfIso_hom_app_comp_derivedPullbackTensorIso_hom_app`
  — **the comparison of Stacks 07A4 is compatible with `Lφ^* ≅ Lψ^*`**, as an identity of
  natural transformations and at a pair of objects.

## Implementation notes

On a pair of K-flat complexes with flat terms every comparison in sight is computed by an
ordinary total tensor complex (Stacks 0FPH at a pair of models,
`Stacks.Sheaves.DerivedPullback.toTensor_square_of_kFlat`), and the identity becomes the
compatibility of the degreewise comparisons of Stacks 03EL with `φ^* ≅ ψ^*`, which is
`Stacks.Sheaves.DerivedPullback.pullbackToposIsoOfIso_hom_app_comp_pullbackToposTensorMap`. It
descends to the whole derived category along the localization of pairs of models
(`Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat`).

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **A transformation between two functors carrying tensor comparisons, checked on models.**
Let `c : P ⟶ P'` be a transformation between two functors with comparisons
`t : T_Y ⋙ P ⟶ P.prod P ⋙ T_X` and `t'` for `P'`. Suppose that at `(A, B)` both comparisons are
computed by models: there are maps `a, b` (for `P`) and `a'', b''` (for `P'`) to objects on which
the tensor products are compared with a model `T_X(A₂, B₂) ⟶ M_X'` by `cmpX`, and similarly for
`P'`, and `c` is carried by the maps `κ` to the models. Then `c` is compatible with the two
comparisons at `(A, B)`, as soon as the two maps on the models are compatible (`hβ`) and the
second set of maps is jointly monomorphic. -/
theorem _root_.CategoryTheory.tensorComparison_natTrans_of_models
    {CY CX : Type*} [Category CY] [Category CX]
    {TY : CY × CY ⥤ CY} {TX : CX × CX ⥤ CX} {Pg Ph : CY ⥤ CX} (c : Pg ⟶ Ph)
    (tg : TY ⋙ Pg ⟶ Pg.prod Pg ⋙ TX) (th : TY ⋙ Ph ⟶ Ph.prod Ph ⋙ TX) (A B : CY)
    {A₂ B₂ A₃ B₃ : CX} {a : Pg.obj A ⟶ A₂} {b : Pg.obj B ⟶ B₂}
    {a'' : Ph.obj A ⟶ A₃} {b'' : Ph.obj B ⟶ B₃} {κ : A₂ ⟶ A₃} {κ' : B₂ ⟶ B₃}
    {MZ : CY} {MX MX' NX NX' : CX} {s : TY.obj (A, B) ⟶ MZ}
    {m : Pg.obj MZ ⟶ MX} {β : MX ⟶ MX'} {cmpX : TX.obj (A₂, B₂) ⟶ MX'}
    {m'' : Ph.obj MZ ⟶ NX} {β'' : NX ⟶ NX'} {cmpX' : TX.obj (A₃, B₃) ⟶ NX'}
    {κM : MX ⟶ NX} {κT : MX' ⟶ NX'}
    (hmono : Mono (TX.map (a'' ×ₘ b''))) (hmono' : Mono cmpX')
    (hA : c.app A ≫ a'' = a ≫ κ) (hB : c.app B ≫ b'' = b ≫ κ')
    (hM : c.app MZ ≫ m'' = m ≫ κM)
    (hcmp : TX.map (κ ×ₘ κ') ≫ cmpX' = cmpX ≫ κT)
    (hg : tg.app (A, B) ≫ TX.map (a ×ₘ b) ≫ cmpX = Pg.map s ≫ m ≫ β)
    (hh : th.app (A, B) ≫ TX.map (a'' ×ₘ b'') ≫ cmpX' = Ph.map s ≫ m'' ≫ β'')
    (hβ : κM ≫ β'' = β ≫ κT) :
    c.app (TY.obj (A, B)) ≫ th.app (A, B) = tg.app (A, B) ≫ TX.map (c.app A ×ₘ c.app B) := by
  have hpair : (c.app A ×ₘ c.app B) ≫ (a'' ×ₘ b'') = (a ×ₘ b) ≫ (κ ×ₘ κ') := by
    ext
    exacts [hA, hB]
  apply (cancel_mono (TX.map (a'' ×ₘ b''))).1
  apply (cancel_mono cmpX').1
  simp only [Category.assoc]
  rw [hh, ← TX.map_comp_assoc, hpair, TX.map_comp_assoc, hcmp, reassoc_of% hg,
    ← c.naturality_assoc, reassoc_of% hM, hβ]

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {φ ψ : RingedToposSiteHom X Y} {e : ψ.u ≅ φ.u}
  (he : RingedToposSiteHom.FSharpCompatible φ ψ e)

/-- **`φ^* ≅ ψ^*` read degreewise on cochain complexes.** -/
abbrev pullbackComplexIsoOfIso : pullbackComplex φ ≅ pullbackComplex ψ :=
  NatIso.mapHomologicalComplex (RingedToposSiteHom.pullbackToposIsoOfIso he) (ComplexShape.up ℤ)

section Complexes

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (hmosφ : φ.u.IsMorphismOfSites Y.J X.J) (hmosψ : ψ.u.IsMorphismOfSites Y.J X.J)

/-- The inverse comparison of total tensor complexes on a summand, through the inverse of the
degreewise comparison. -/
private theorem ι_pullbackToposTensorTotalIso_inv (f : RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)
          p q n hpq ≫
        (pullbackToposTensorTotalIso f hmos K L).inv.f n =
      (pullbackToposTensorMapDegIso f hmos K L p q).inv ≫
        f.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)
            p q n hpq) := by
  rw [Iso.eq_inv_comp, pullbackToposTensorMapDegIso_hom,
    ← reassoc_of% (ι_pullbackToposTensorTotalIso_hom f hmos K L p q n hpq),
    ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  exact Category.comp_id _

/-- **The comparison of total tensor complexes of Stacks 03EL is compatible with `φ^* ≅ ψ^*`**,
for arbitrary cochain complexes `K`, `L` of `𝒪_D`-modules. It is checked on the summands of
`Tot(φ^*K ⊗ φ^*L)`, where it is the module-level compatibility
`pullbackToposIsoOfIso_hom_app_comp_pullbackToposTensorMap`. -/
theorem pullbackComplexIsoOfIso_comp_pullbackToposTensorTotalIso
    (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplexIsoOfIso he).hom.app (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≫
        (pullbackToposTensorTotalIso ψ hmosψ K L).hom =
      (pullbackToposTensorTotalIso φ hmosφ K L).hom ≫
        HomologicalComplex.mapBifunctorMap ((pullbackComplexIsoOfIso he).hom.app K)
          ((pullbackComplexIsoOfIso he).hom.app L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) := by
  rw [← Iso.inv_comp_eq]
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  simp only [HomologicalComplex.comp_f]
  rw [reassoc_of% (ι_pullbackToposTensorTotalIso_inv φ hmosφ K L p q n hpq),
    HomologicalComplex.ι_mapBifunctorMap]
  have hnat' : φ.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)
          p q n hpq) ≫
      ((pullbackComplexIsoOfIso he).hom.app (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))).f n =
      (RingedToposSiteHom.pullbackToposIsoOfIso he).hom.app _ ≫
        ψ.pullbackTopos.map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)
            p q n hpq) :=
    (RingedToposSiteHom.pullbackToposIsoOfIso he).hom.naturality
      (HomologicalComplex.ιMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)
          p q n hpq)
  rw [reassoc_of% hnat', ι_pullbackToposTensorTotalIso_hom ψ hmosψ K L p q n hpq,
    pullbackToposTensorMapDeg_eq ψ hmosψ,
    reassoc_of% (pullbackToposIsoOfIso_hom_app_comp_pullbackToposTensorMap he hmosφ hmosψ
      (K.X p) (L.X q)),
    ← pullbackToposTensorMapDeg_eq φ hmosφ, ← pullbackToposTensorMapDegIso_hom,
    Iso.inv_hom_id_assoc]
  rfl

end Complexes

section Comparison

variable [(pullbackOnHomotopy φ).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ψ).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The comparison `Lf^*(QM) ⟶ Q(f^*M)` of Stacks 06YY is compatible with `Lφ^* ≅ Lψ^*`**,
read against `φ^* ≅ ψ^*` on complexes: this is the defining property of the isomorphism of total
left derived functors induced by `φ^* ≅ ψ^*`. -/
theorem derivedPullbackIsoOfIso_hom_app_comp_pullbackComparisonQ
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullbackIsoOfIso he).hom.app (DerivedCategory.Q.obj M) ≫ pullbackComparisonQ ψ M =
      pullbackComparisonQ φ M ≫ DerivedCategory.Q.map ((pullbackComplexIsoOfIso he).hom.app M) := by
  have hfac := Functor.leftDerivedNatTrans_app (derivedPullback φ) (derivedPullback ψ)
    (derivedPullbackComparison φ) (derivedPullbackComparison ψ)
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))
    (pullbackOnHomotopyIsoOfIso he).hom ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M)
  have hq := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ((pullbackComplexIsoOfIso he).hom.app M)
  have hn := (derivedPullbackIsoOfIso he).hom.naturality
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app M)
  dsimp only [pullbackComparisonQ]
  rw [← Category.assoc, ← hn, Category.assoc, Category.assoc]
  refine congrArg ((derivedPullback φ).map _ ≫ ·) ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hfac).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hq).trans (Category.assoc _ _ _).symm)))

end Comparison

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [(pullbackOnHomotopy φ).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy ψ).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmosφ : φ.u.IsMorphismOfSites Y.J X.J) (hmosψ : ψ.u.IsMorphismOfSites Y.J X.J)

/-- **The comparison of Stacks 07A4 is compatible with `Lφ^* ≅ Lψ^*`, at a pair of K-flat
complexes with flat terms.** There every comparison is computed by an ordinary total tensor
complex (Stacks 0FPH, `toTensor_square_of_kFlat`), and the identity is the compatibility of the
comparison of total tensor complexes of Stacks 03EL with `φ^* ≅ ψ^*`
(`pullbackComplexIsoOfIso_comp_pullbackToposTensorTotalIso`). -/
theorem derivedPullbackTensorIso_isoOfIso_app_of_kFlat
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackIsoOfIso he).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O)).obj
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
        (derivedPullbackTensorIso ψ hmosψ).hom.app
            (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (derivedPullbackTensorIso φ hmosφ).hom.app
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
          ((derivedPullbackIsoOfIso he).hom.app (DerivedCategory.Q.obj K) ×ₘ
            (derivedPullbackIsoOfIso he).hom.app (DerivedCategory.Q.obj L)) := by
  have htot : DerivedCategory.Q.map ((pullbackComplexIsoOfIso he).hom.app
        (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj L)) ≫
      DerivedCategory.Q.map (pullbackTensorComplexIso ψ hmosψ K L).hom =
      DerivedCategory.Q.map (pullbackTensorComplexIso φ hmosφ K L).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((pullbackComplexIsoOfIso he).hom.app K) ((pullbackComplexIsoOfIso he).hom.app L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
      (pullbackComplexIsoOfIso_comp_pullbackToposTensorTotalIso he hmosφ hmosψ K L)).trans
        (DerivedCategory.Q.map_comp _ _))
  have h := CategoryTheory.tensorComparison_natTrans_of_models
    (derivedPullbackIsoOfIso he).hom
    (derivedPullbackTensorIso φ hmosφ).hom (derivedPullbackTensorIso ψ hmosψ).hom
    (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
    (mono_derivedTensorMap_pullbackComparisonQ ψ hmosψ K L hK hL hflatK hflatL)
    (mono_toTensor_pullbackComplex ψ hmosψ K L hK hL hflatK hflatL)
    (derivedPullbackIsoOfIso_hom_app_comp_pullbackComparisonQ he K)
    (derivedPullbackIsoOfIso_hom_app_comp_pullbackComparisonQ he L)
    (derivedPullbackIsoOfIso_hom_app_comp_pullbackComparisonQ he
      (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj L))
    (toTensor_naturality_prod X ((pullbackComplexIsoOfIso he).hom.app K)
      ((pullbackComplexIsoOfIso he).hom.app L))
    ((toTensor_square_of_kFlat φ hmosφ K L hK hL hflatK hflatL).symm : _)
    ((toTensor_square_of_kFlat ψ hmosψ K L hK hL hflatK hflatL).symm : _)
    htot
  exact h

/-- **The comparison of Stacks 07A4 is compatible with `Lφ^* ≅ Lψ^*`**, as an identity of
natural transformations on `D(𝒪_D) × D(𝒪_D)`: the isomorphism `Lφ^* ≅ Lψ^*` at `K ⊗^L L`,
followed by the comparison for `ψ`, is the comparison for `φ` followed by `Lφ^* ≅ Lψ^*` in each
tensor factor. -/
theorem derivedPullbackTensorIso_isoOfIso :
    Functor.whiskerLeft
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
          (derivedPullbackIsoOfIso he).hom ≫
        (derivedPullbackTensorIso ψ hmosψ).hom =
      (derivedPullbackTensorIso φ hmosφ).hom ≫
        Functor.whiskerRight
          (NatTrans.prod (derivedPullbackIsoOfIso he).hom (derivedPullbackIsoOfIso he).hom)
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) :=
  natTrans_ext_of_flatKFlat Y _ _ fun K L hK hL hflatK hflatL =>
    derivedPullbackTensorIso_isoOfIso_app_of_kFlat he hmosφ hmosψ K L hK hL hflatK hflatL

/-- **The comparison of Stacks 07A4 is compatible with `Lφ^* ≅ Lψ^*`, at a pair of objects.** -/
theorem derivedPullbackIsoOfIso_hom_app_comp_derivedPullbackTensorIso_hom_app
    (P Q : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackIsoOfIso he).hom.app
          ((Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O)).obj (P, Q)) ≫
        (derivedPullbackTensorIso ψ hmosψ).hom.app (P, Q) =
      (derivedPullbackTensorIso φ hmosφ).hom.app (P, Q) ≫
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
          ((derivedPullbackIsoOfIso he).hom.app P ×ₘ (derivedPullbackIsoOfIso he).hom.app Q) :=
  NatTrans.congr_app (derivedPullbackTensorIso_isoOfIso he hmosφ hmosψ) (P, Q)

end Tensor

end Stacks.Sheaves.DerivedPullback

end
