module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeMonoidalChainLevel
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangePrefixExists
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTransposeCovariantSlot
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeUnitChainPrefix
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TransportedMonoidalTailPosition
public import StacksFrontier.Homology.HomComplex.RingEquivTransport
public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionTransport
public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTransposePin

/-!
# Chain-level and scalar-lift comparisons for derived base change

Let `f : R → A` be a ring homomorphism. This file collects the chain-level and presentation
lemmas used to identify the monoidality isomorphism of [stacks 068I] with the lax monoidal
structure map of derived base change.

## Main results

* `StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry_Phi_postcomp` -- uncurrying the
  chain-level currying `Φ ≫ postcomp g` of a chain map `g` out of a total tensor complex gives `g`
  back.
* `Stacks.DerivedHom.BaseChangeIso.uncurry_unit_comp_curry_comp_changeOfRingsMap` -- the
  [stacks 0E1W] side of the keystone at the chain map presenting a curried morphism.
* `Stacks.DerivedHom.BaseChange.scalarEquivalence_inverse_map_tensor_scalarLift` -- the scalar
  lift of the K-flat presentation of a derived tensor product.
* `Stacks.DerivedHom.BaseChange.unitIso_comp_inverse_map_chain_comp_scalarRestrictionIso_inv` --
  the scalar-restriction comparison `δ` at a class, inverted, against its chain value.

## References

* [Stacks Project, Tag 0A62](https://stacks.math.columbia.edu/tag/0A62)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace StacksDraft.DerivedHom.DerivedInternalHom.Model

open CochainComplex HomComplex HomologicalComplex

universe u

variable {R : Type u} [CommRing R]

/-- **Uncurrying the chain-level currying.**  The chain map
`Φ_{K,L} ≫ postcomp g : K ⟶ Hom^•(L, M)` of [stacks 0A62] uncurries to `g`: on the generator
`x ⊗ y` of the summand `K^p ⊗ L^q` both sides are `g (x ⊗ y)`. -/
public lemma uncurry_Phi_postcomp {K L M : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : K ⊗ L ⟶ M) :
    uncurry (Stacks.HomComplex.TensorHomMap.Phi R K L ≫
      Stacks.HomComplex.TensorHomMap.postcomp R L (K ⊗ L) M g) = g := by
  ext n : 1
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a b
  change (uncurry (Stacks.HomComplex.TensorHomMap.Phi R K L ≫
      Stacks.HomComplex.TensorHomMap.postcomp R L (K ⊗ L) M g)).f n
        ((ιTensorObj K L p q n hpq).hom (a ⊗ₜ[R] b)) =
    g.f n ((ιTensorObj K L p q n hpq).hom (a ⊗ₜ[R] b))
  rw [uncurry_apply, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    Stacks.HomComplex.TensorHomMap.Phi_f_apply, postcomp_apply,
    Stacks.HomComplex.TensorHomMap.Phiv_v]
  rfl

end StacksDraft.DerivedHom.DerivedInternalHom.Model

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

universe u₁ u₂ u₃

/-- **Splitting a tensored pair off an inverse transpose.**  The inverse transpose of
`(a ⊗ᴸ b) ≫ c` is `a`, then the inverse transpose of `c`, then the internal Hom of `b` in the
contravariant slot. -/
public theorem homEquiv_symm_tensor_map_mkHom {B : Type u₁} [CommRing B]
    [HasDerivedCategory.{u₃} (ModuleCat.{u₂} B)] (d : DerivedHomAdjunction.{u₁, u₂, u₃} B)
    {X X' Y Y' M : DerivedCategory (ModuleCat.{u₂} B)} (a : X ⟶ X') (b : Y ⟶ Y')
    (c : d.tensor.obj (X', Y') ⟶ M) :
    (d.homEquiv X Y M).symm (d.tensor.map (CategoryTheory.Prod.mkHom a b) ≫ c) =
      a ≫ (d.homEquiv X' Y' M).symm c ≫
        d.hom.map ((b.op, 𝟙 M) : ((Opposite.op Y', M) : (DerivedCategory (ModuleCat.{u₂} B))ᵒᵖ ×
          DerivedCategory (ModuleCat.{u₂} B)) ⟶ (Opposite.op Y, M)) := by
  have hsplit : d.tensor.map (CategoryTheory.Prod.mkHom a b) =
      d.tensor.map ((a, 𝟙 Y) : (X, Y) ⟶ (X', Y)) ≫
        d.tensor.map ((𝟙 X', b) : (X', Y) ⟶ (X', Y')) := by
    rw [← d.tensor.map_comp]
    exact congrArg d.tensor.map (Prod.ext (Category.comp_id a).symm (Category.id_comp b).symm)
  apply (d.homEquiv X Y M).injective
  rw [AddEquiv.apply_symm_apply, d.homEquiv_naturality_left, d.homEquiv_symm_comp_hom_map,
    AddEquiv.apply_symm_apply, hsplit, Category.assoc, Category.comp_id]

/-- `StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_tensor_map_mkHom` followed by an
arbitrary morphism. -/
public theorem homEquiv_symm_tensor_map_mkHom_assoc {B : Type u₁} [CommRing B]
    [HasDerivedCategory.{u₃} (ModuleCat.{u₂} B)] (d : DerivedHomAdjunction.{u₁, u₂, u₃} B)
    {X X' Y Y' M : DerivedCategory (ModuleCat.{u₂} B)} (a : X ⟶ X') (b : Y ⟶ Y')
    (c : d.tensor.obj (X', Y') ⟶ M) {Z : DerivedCategory (ModuleCat.{u₂} B)}
    (z : d.hom.obj (Opposite.op Y, M) ⟶ Z) :
    (d.homEquiv X Y M).symm (d.tensor.map (CategoryTheory.Prod.mkHom a b) ≫ c) ≫ z =
      a ≫ (d.homEquiv X' Y' M).symm c ≫
        d.hom.map ((b.op, 𝟙 M) : ((Opposite.op Y', M) : (DerivedCategory (ModuleCat.{u₂} B))ᵒᵖ ×
          DerivedCategory (ModuleCat.{u₂} B)) ⟶ (Opposite.op Y, M)) ≫ z := by
  rw [homEquiv_symm_tensor_map_mkHom]
  simp only [Category.assoc]

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Stacks.DerivedHom.BaseChangeIso

open StacksDraft.DerivedHom

universe u

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The [stacks 0E1W] side at a curried chain map.**  If the chain map
`w : K ⟶ Hom_A(A ⊗_R P, J)|_R` is the degreewise unit followed by the restriction of the
chain-level currying `Φ ≫ postcomp g` of a chain map `g : (A ⊗ K) ⊗ (A ⊗ P) ⟶ J`, then the
uncurrying of `w` followed by the chain-level map of [stacks 0E1W] is the degreewise unit at
`K ⊗ P`, then the restriction of the inverse monoidality comparison of [stacks 068I] followed by
`g`, then `q`. -/
public theorem uncurry_unit_comp_curry_comp_changeOfRingsMap
    (K P : CochainComplex (ModuleCat.{u} R) ℤ)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (g : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj K ⊗
        (CochainComplex.extendScalarsLarge.{u, u, u} f).obj P ⟶ J) :
    DerivedInternalHom.Model.uncurry
        ((((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
            (Stacks.HomComplex.TensorHomMap.Phi A _ _ ≫
              Stacks.HomComplex.TensorHomMap.postcomp A _ _ J g)) ≫
            Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f P J I q) =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app (K ⊗ P) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          ((CochainComplex.ExtendScalars.extendScalarsMonoidalIso f K P).inv ≫ g) ≫ q := by
  refine (congrArg DerivedInternalHom.Model.uncurry (Category.assoc _ _ _)).trans ?_
  refine (uncurry_unit_comp_restrictScalars_map_comp_changeOfRingsMap f K P J I q _).trans ?_
  exact congrArg (fun z => ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app (K ⊗ P) ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} f).map
          ((CochainComplex.ExtendScalars.extendScalarsMonoidalIso f K P).inv ≫ z) ≫ q)
    (DerivedInternalHom.Model.uncurry_Phi_postcomp g)

end Stacks.DerivedHom.BaseChangeIso

namespace Stacks.DerivedHom.BaseChange

open StacksDraft.DerivedHom

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- **Cancelling a presentation against its transport.**  Abstract form of the identification of
two scalar-lift presentations: if `Gd (κ⁻¹) ≫ c = s ≫ v` and `v ≫ u = 𝟙`, then
`Gd ((a ≪≫ κ)⁻¹) ≫ Gd a ≫ c ≫ u = s`. -/
public theorem transport_presentation_cancel {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (Gd : 𝒞 ⥤ 𝒟) {T Y X : 𝒞} {A L : 𝒟} (a : T ≅ Y) (κ : Y ≅ X) (c : Gd.obj Y ⟶ A)
    (u : A ⟶ L) (s : Gd.obj X ⟶ L) (v : L ⟶ A) (hnat : Gd.map κ.inv ≫ c = s ≫ v)
    (htri : v ≫ u = 𝟙 L) :
    Gd.map (a ≪≫ κ).inv ≫ Gd.map a.hom ≫ c ≫ u = s := by
  simp only [Iso.trans_inv, Functor.map_comp, Category.assoc]
  rw [← Gd.map_comp_assoc a.inv a.hom, Iso.inv_hom_id, Gd.map_id, Category.id_comp,
    reassoc_of% hnat, htri, Category.comp_id]

/-- **The two scalar-lift presentations of a class are adjoint to each other.**  The presentation
`CochainComplex.DerivedTensor.scalarEquivalenceQObjIso` of the class of `X` as the image of the
class of its lift, pushed forward by the scalar lift and followed by the inverse unit of
`StacksDraft.DerivedHom.derivedScalarEquivalence`, is the scalar-lift presentation
`Stacks.DerivedHom.BaseChange.scalarLiftQObjIso` of `X`. -/
public theorem scalarEquivalence_map_scalarEquivalenceQObjIso_inv_comp_unitIso_inv
    (B : Type u) [CommRing B] (X : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v} B).functor.map
        (CochainComplex.DerivedTensor.scalarEquivalenceQObjIso.{u, v} B X).inv ≫
      (derivedScalarEquivalence.{u, v, max u v + 1} B).unitIso.inv.app
        (DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X)) =
      (scalarLiftQObjIso.{u, v} B X).hom := by
  rw [_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_unitIso,
    Iso.symm_inv,
    ← Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_symm_counit_app,
    Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_symm_counit_app_Q]
  let e₀ := uliftModuleEquivalence.{u, max u v, v} B
  let G := e₀.inverse
  let X' := ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X)
  have hc : (ScalarTransportedInternalHom.uliftComplexEquivalence.{u, v} B).counitIso.inv.app X =
      (NatIso.mapHomologicalComplex e₀.counitIso (ComplexShape.up ℤ)).inv.app X := rfl
  have htri : (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ScalarTransportedInternalHom.uliftComplexEquivalence.{u, v} B).counitIso.inv.app X) ≫
      (ScalarTransportedInternalHom.uliftComplexEquivalence.{u, v} B).unitIso.inv.app X' = 𝟙 _ :=
    (ScalarTransportedInternalHom.uliftComplexEquivalence.{u, v} B).inverse_counitInv_comp X
  have hnat := G.mapDerivedCategoryFactors.hom.naturality
    ((ScalarTransportedInternalHom.uliftComplexEquivalence.{u, v} B).counitIso.inv.app X)
  have htri' : DerivedCategory.Q.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ScalarTransportedInternalHom.uliftComplexEquivalence.{u, v} B).counitIso.inv.app X)) ≫
      DerivedCategory.Q.map
        ((ScalarTransportedInternalHom.uliftComplexEquivalence.{u, v} B).unitIso.inv.app X') =
        𝟙 _ := by
    rw [← DerivedCategory.Q.map_comp, htri, DerivedCategory.Q.map_id]
  exact transport_presentation_cancel
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v} B).functor
    ((e₀.functor.mapDerivedCategoryFactors).app X')
    (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex e₀.counitIso (ComplexShape.up ℤ)).app X))
    _ _ _ _ hnat htri'

/-- Abstract folding of a covariant internal-Hom map through an equivalence. -/
public theorem fold_covariant_through_equivalence {𝒜 𝒜' : Type*} [Category 𝒜] [Category 𝒜']
    (S : 𝒜 ≌ 𝒜') (HA : 𝒜'ᵒᵖ × 𝒜' ⥤ 𝒜') {Y M : 𝒜} {Z₃ N Q₀ : 𝒜'} {T₀ : 𝒜}
    (a : Z₃ ⟶ S.functor.obj Y) (χ : S.functor.obj M ⟶ N)
    (hc : HA.obj (Opposite.op Z₃, N) ⟶ Q₀) (v : S.inverse.obj Q₀ ⟶ T₀) :
    S.inverse.map (HA.map ((a.op, χ) : ((Opposite.op (S.functor.obj Y), S.functor.obj M) :
        𝒜'ᵒᵖ × 𝒜') ⟶ (Opposite.op Z₃, N)) ≫ hc) ≫ v =
      S.inverse.map (HA.map (((S.functor.map (𝟙 Y)).op,
          S.functor.map (S.unitIso.hom.app M ≫ S.inverse.map χ)) :
        ((Opposite.op (S.functor.obj Y), S.functor.obj M) : 𝒜'ᵒᵖ × 𝒜') ⟶
          (Opposite.op (S.functor.obj Y), S.functor.obj (S.inverse.obj N)))) ≫
        S.inverse.map (HA.map ((a.op, S.counitIso.hom.app N) :
          ((Opposite.op (S.functor.obj Y), S.functor.obj (S.inverse.obj N)) : 𝒜'ᵒᵖ × 𝒜') ⟶
            (Opposite.op Z₃, N)) ≫ hc) ≫ v := by
  rw [← Category.assoc, ← S.inverse.map_comp, ← Category.assoc, ← HA.map_comp]
  congr 4
  refine Prod.ext ?_ ?_
  · simp
  · simp only [prod_comp, Functor.map_comp, Category.assoc, Equivalence.counit_naturality,
      Equivalence.functor_unit_comp_assoc]

/-- Abstract assembly of the model-level tail of the transposed K-flat tensor presentation. -/
public theorem transpose_model_tail_assembly {𝒜 𝒜' : Type*} [Category 𝒜] [Category 𝒜']
    (S : 𝒜 ≌ 𝒜') (Du : 𝟭 𝒜' ≅ S.inverse ⋙ S.functor) (hDu : Du = S.counitIso.symm)
    (HA : 𝒜'ᵒᵖ × 𝒜' ⥤ 𝒜') {QP QP' T₀ : 𝒜} {W₀ Hm L₀ J₀ X₀ Hx : 𝒜'}
    (s0 : QP ⟶ S.inverse.obj W₀) (m1 : W₀ ⟶ Hm) (hi : HA.obj (Opposite.op L₀, J₀) ≅ Hm)
    (s1 : QP' ⟶ S.inverse.obj L₀) (a : X₀ ⟶ S.functor.obj QP')
    (hx : HA.obj (Opposite.op X₀, J₀) ≅ Hx) (sif : S.inverse.obj Hx ⟶ T₀) (pre : Hm ⟶ Hx)
    (lq : X₀ ⟶ L₀) (qid : J₀ ⟶ J₀) (out : QP ⟶ T₀)
    (H3 : a ≫ S.functor.map s1 ≫ Du.inv.app L₀ = lq) (hqid : qid = 𝟙 J₀)
    (H5 : HA.map ((lq.op, qid) : ((Opposite.op L₀, J₀) : 𝒜'ᵒᵖ × 𝒜') ⟶ (Opposite.op X₀, J₀)) ≫
      hx.hom = hi.hom ≫ pre)
    (H8 : s0 ≫ S.inverse.map (m1 ≫ pre) ≫ sif = out) :
    s0 ≫ (S.inverse.map m1 ≫ (S.inverse.map hi.inv ≫ S.inverse.map (HA.map
        (((Du.inv.app L₀).op, Du.hom.app J₀) : ((Opposite.op L₀, J₀) : 𝒜'ᵒᵖ × 𝒜') ⟶
          (Opposite.op (S.functor.obj (S.inverse.obj L₀)),
            S.functor.obj (S.inverse.obj J₀)))))) ≫
      S.inverse.map (HA.map (((S.functor.map s1).op, S.functor.map (𝟙 (S.inverse.obj J₀))) :
        ((Opposite.op (S.functor.obj (S.inverse.obj L₀)), S.functor.obj (S.inverse.obj J₀)) :
          𝒜'ᵒᵖ × 𝒜') ⟶ (Opposite.op (S.functor.obj QP'), S.functor.obj (S.inverse.obj J₀)))) ≫
        S.inverse.map (HA.map ((a.op, S.counitIso.hom.app J₀) :
          ((Opposite.op (S.functor.obj QP'), S.functor.obj (S.inverse.obj J₀)) : 𝒜'ᵒᵖ × 𝒜') ⟶
            (Opposite.op X₀, J₀)) ≫ hx.hom) ≫ sif = out := by
  subst hDu hqid
  have hcomb : HA.map ((((S.counitIso.symm).inv.app L₀).op, (S.counitIso.symm).hom.app J₀) :
        ((Opposite.op L₀, J₀) : 𝒜'ᵒᵖ × 𝒜') ⟶
          (Opposite.op (S.functor.obj (S.inverse.obj L₀)), S.functor.obj (S.inverse.obj J₀))) ≫
      HA.map (((S.functor.map s1).op, S.functor.map (𝟙 (S.inverse.obj J₀))) :
        ((Opposite.op (S.functor.obj (S.inverse.obj L₀)), S.functor.obj (S.inverse.obj J₀)) :
          𝒜'ᵒᵖ × 𝒜') ⟶ (Opposite.op (S.functor.obj QP'), S.functor.obj (S.inverse.obj J₀))) ≫
        HA.map ((a.op, S.counitIso.hom.app J₀) :
          ((Opposite.op (S.functor.obj QP'), S.functor.obj (S.inverse.obj J₀)) : 𝒜'ᵒᵖ × 𝒜') ⟶
            (Opposite.op X₀, J₀)) =
      HA.map ((lq.op, 𝟙 J₀) : ((Opposite.op L₀, J₀) : 𝒜'ᵒᵖ × 𝒜') ⟶ (Opposite.op X₀, J₀)) := by
    rw [← HA.map_comp, ← HA.map_comp, ← H3]
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · simp
  have hS : S.inverse.map hi.inv ≫ S.inverse.map (HA.map
        ((((S.counitIso.symm).inv.app L₀).op, (S.counitIso.symm).hom.app J₀) :
          ((Opposite.op L₀, J₀) : 𝒜'ᵒᵖ × 𝒜') ⟶
            (Opposite.op (S.functor.obj (S.inverse.obj L₀)), S.functor.obj (S.inverse.obj J₀)))) ≫
      S.inverse.map (HA.map (((S.functor.map s1).op, S.functor.map (𝟙 (S.inverse.obj J₀))) :
        ((Opposite.op (S.functor.obj (S.inverse.obj L₀)), S.functor.obj (S.inverse.obj J₀)) :
          𝒜'ᵒᵖ × 𝒜') ⟶ (Opposite.op (S.functor.obj QP'), S.functor.obj (S.inverse.obj J₀)))) ≫
        S.inverse.map (HA.map ((a.op, S.counitIso.hom.app J₀) :
          ((Opposite.op (S.functor.obj QP'), S.functor.obj (S.inverse.obj J₀)) : 𝒜'ᵒᵖ × 𝒜') ⟶
            (Opposite.op X₀, J₀)) ≫ hx.hom) = S.inverse.map pre := by
    simp only [← S.inverse.map_comp]
    rw [reassoc_of% hcomb, H5, Iso.inv_hom_id_assoc]
  rw [← H8, S.inverse.map_comp m1 pre, ← hS]
  simp only [Category.assoc]

/-- Abstract: a presentation followed by a transported localized map and the factorization. -/
public theorem presentation_comp_map_comp_factors {𝒞 𝒟 𝒜 𝒜' : Type*} [Category 𝒞]
    [Category 𝒟] [Category 𝒜] [Category 𝒜'] (Qf : 𝒞 ⥤ 𝒜) (Qf' : 𝒟 ⥤ 𝒜') (Si : 𝒜' ⥤ 𝒜)
    (G : 𝒟 ⥤ 𝒞) (SIF : Qf' ⋙ Si ≅ G ⋙ Qf) {P : 𝒞} {X₀ Y₀ : 𝒟} (κi : P ⟶ G.obj X₀)
    (g : X₀ ⟶ Y₀) (s0 : Qf.obj P ⟶ Si.obj (Qf'.obj X₀)) (hs : s0 ≫ SIF.hom.app X₀ = Qf.map κi) :
    s0 ≫ Si.map (Qf'.map g) ≫ SIF.hom.app Y₀ = Qf.map (κi ≫ G.map g) := by
  have h := SIF.hom.naturality g
  simp only [Functor.comp_map] at h
  rw [h, ← Category.assoc, hs, Qf.map_comp]

/-- Abstract form of the covariant step of the transposed K-flat tensor presentation. -/
public theorem presentation_covariant_step {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (Ei : 𝒟 ⥤ 𝒞) {A₀ A₁ QX QN : 𝒞} {B₁ B₂ B₃ B₄ W₀ : 𝒟} (t₁ : A₀ ⟶ A₁)
    (t₂ : A₁ ⟶ Ei.obj B₁) (r : B₁ ⟶ B₂) (σX : Ei.obj B₂ ⟶ QX) (qe : QX ⟶ QN)
    (le : B₂ ⟶ B₃) (σN : Ei.obj B₃ ⟶ QN) (u : QN ⟶ Ei.obj W₀) (s : W₀ ⟶ B₃) (qn : B₃ ⟶ B₄)
    (hnat : σX ≫ qe = Ei.map le ≫ σN) (h2 : σN ≫ u ≫ Ei.map s = 𝟙 _) (rle : B₁ ⟶ B₄)
    (hrle : rle = r ≫ le ≫ qn) :
    ((t₁ ≫ t₂ ≫ (Ei.map r ≫ σX)) ≫ qe) ≫ u ≫ Ei.map (s ≫ qn) =
      t₁ ≫ t₂ ≫ Ei.map rle := by
  subst hrle
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% h2]

/-- Abstract form of the lifted-unit identity. -/
public theorem lifted_unit_generic {𝒞 𝒟 𝒜 : Type*} [Category 𝒞] [Category 𝒟] [Category 𝒜]
    (Lf : 𝒜 ⥤ 𝒟) (Rs : 𝒞 ⥤ 𝒟) (G : 𝒞 ⥤ 𝒜) {X : 𝒜} {E1 E2 Z : 𝒞}
    (η' : Lf.obj X ⟶ Rs.obj E1) (lam : E1 ≅ E2) (t : E1 ⟶ Z) (κ : X ⟶ G.obj E2)
    (src : Lf.obj (G.obj E2) ⟶ Rs.obj E2) (srcZ : Lf.obj (G.obj Z) ⟶ Rs.obj Z)
    (hunit : η' ≫ Rs.map lam.hom = Lf.map κ ≫ src)
    (hnat : src ≫ Rs.map (lam.inv ≫ t) = Lf.map (G.map (lam.inv ≫ t)) ≫ srcZ) :
    Lf.map (κ ≫ G.map (lam.inv ≫ t)) ≫ srcZ = η' ≫ Rs.map t := by
  have h1 : η' ≫ Rs.map t = (η' ≫ Rs.map lam.hom) ≫ Rs.map (lam.inv ≫ t) := by
    rw [Category.assoc, ← Rs.map_comp, Iso.hom_inv_id_assoc]
  rw [h1, hunit, Category.assoc, hnat, ← Category.assoc, ← Lf.map_comp]

/-- Abstract: the localization of an exact functor's image depends only on the localization. -/
public theorem map_congr_of_factors {𝒞 𝒟 𝒞' 𝒟' : Type*} [Category 𝒞] [Category 𝒟]
    [Category 𝒞'] [Category 𝒟'] (Q₁ : 𝒞 ⥤ 𝒞') (Q₂ : 𝒟 ⥤ 𝒟') (G : 𝒞 ⥤ 𝒟) (Gd : 𝒞' ⥤ 𝒟')
    (fac : Q₁ ⋙ Gd ≅ G ⋙ Q₂) {X Y : 𝒞} (x y : X ⟶ Y) (h : Q₁.map x = Q₁.map y) :
    Q₂.map (G.map x) = Q₂.map (G.map y) := by
  have hx := fac.hom.naturality x
  have hy := fac.hom.naturality y
  simp only [Functor.comp_map] at hx hy
  rw [← cancel_epi (fac.hom.app X), ← hx, ← hy, h]

/-- Abstract: three isomorphisms cancelled against their inverses. -/
public theorem three_iso_cancel {𝒞 : Type*} [Category 𝒞] {W X Y Z V : 𝒞} (a : Z ≅ W)
    (b : Y ≅ Z) (c : X ≅ Y) (n : W ⟶ V) :
    (a.inv ≫ b.inv ≫ c.inv) ≫ c.hom ≫ b.hom ≫ a.hom ≫ n = n := by
  simp

/-- Abstract: replacing a middle factor with one of the same localization. -/
public theorem map_comp_congr_middle {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (Q : 𝒞 ⥤ 𝒟)
    {A B C D E : 𝒞} (a : A ⟶ B) (b : B ⟶ C) (x y : C ⟶ D) (q : D ⟶ E)
    (h : Q.map x = Q.map y) : Q.map (a ≫ b ≫ x ≫ q) = Q.map (a ≫ b ≫ y ≫ q) := by
  simp only [Functor.map_comp, h]

/-- Abstract: inserting an isomorphism and its inverse in front of an equation. -/
public theorem eq_inv_hom_comp_of_eq {𝒞 : Type*} [Category 𝒞] {X Y Z : 𝒞} (i : X ≅ Y)
    {a b : Y ⟶ Z} (h : a = b) : a = i.inv ≫ i.hom ≫ b := by
  rw [Iso.inv_hom_id_assoc, h]

/-- Abstract cancellation for the valued fourth factor of [stacks 0E1W]. -/
public theorem inv_comp_map_comp_eFv_cancel {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟]
    [Category ℰ] (TB : 𝒞 ⥤ 𝒟) (Sf : ℰ ⥤ 𝒟) {X Y : 𝒞} {Z W : 𝒟} {P P' : ℰ}
    (α : TB.obj Y ⟶ Z) (hα : IsIso α) (ex : X ≅ Y) (q : Z ⟶ W) (s : W ⟶ Sf.obj P')
    (c : P ⟶ P') (hc : IsIso c) :
    @CategoryTheory.inv _ _ _ _ α hα ≫ TB.map ex.inv ≫
        (((TB.map ex.hom ≫ (α ≫ q)) ≫ s) ≫ Sf.map (@CategoryTheory.inv _ _ _ _ c hc)) ≫
          Sf.map c = q ≫ s := by
  simp only [Category.assoc, ← Sf.map_comp, IsIso.inv_hom_id, Sf.map_id, Category.comp_id,
    ← TB.map_comp_assoc, Iso.inv_hom_id, TB.map_id, Category.id_comp, IsIso.inv_hom_id_assoc]

/-- Abstract cancellation of a mapped isomorphism against the head of a composite. -/
public theorem map_inv_comp_map_hom_cancel {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (Sf : 𝒞 ⥤ 𝒟) {X Y : 𝒞} {Z W : 𝒟} (i : X ≅ Y) (s : Sf.obj Y ⟶ Z) (q : Z ⟶ W) :
    Sf.map i.inv ≫ ((Sf.map i.hom ≫ s) ≫ q) = s ≫ q := by
  simp only [← Category.assoc, ← Sf.map_comp, Iso.inv_hom_id, Sf.map_id, Category.id_comp]

/-- Abstract combination of transported internal-Hom maps into one. -/
public theorem hom_transport_combine {𝒜 𝒜' : Type*} [Category 𝒜] [Category 𝒜']
    (Si : 𝒜' ⥤ 𝒜) (Sf : 𝒜 ⥤ 𝒜') (HA : 𝒜'ᵒᵖ × 𝒜' ⥤ 𝒜')
    {Y₁ Y₂ M₁ M₂ : 𝒜} {Z₁ Z₂ Z₃ N : 𝒜'} {Q₀ : 𝒜'} {T₀ : 𝒜}
    (l : Y₂ ⟶ Y₁) (g : M₁ ⟶ M₂) (e₁ : Z₁ ⟶ Sf.obj Y₂) (e₂ : Z₂ ⟶ Z₁) (y : Sf.obj M₂ ⟶ N)
    (e₃ : Z₃ ⟶ Z₂) (hc : HA.obj (Opposite.op Z₃, N) ⟶ Q₀) (v : Si.obj Q₀ ⟶ T₀)
    (a : Z₃ ⟶ Sf.obj Y₁) (χ : Sf.obj M₁ ⟶ N)
    (ha : e₃ ≫ e₂ ≫ e₁ ≫ Sf.map l = a) (hχ : Sf.map g ≫ y = χ) :
    Si.map (HA.map (((Sf.map l).op, Sf.map (𝟙 M₁)) :
          ((Opposite.op (Sf.obj Y₁), Sf.obj M₁) : 𝒜'ᵒᵖ × 𝒜') ⟶
            (Opposite.op (Sf.obj Y₂), Sf.obj M₁))) ≫
      Si.map (HA.map (((Sf.map (𝟙 Y₂)).op, Sf.map g) :
          ((Opposite.op (Sf.obj Y₂), Sf.obj M₁) : 𝒜'ᵒᵖ × 𝒜') ⟶
            (Opposite.op (Sf.obj Y₂), Sf.obj M₂))) ≫
        Si.map (HA.map (CategoryTheory.Prod.mkHom e₁.op (𝟙 (Sf.obj M₂))) ≫
          HA.map (CategoryTheory.Prod.mkHom e₂.op y) ≫
            (HA.map (((e₃.op, 𝟙 N)) : ((Opposite.op Z₂, N) : 𝒜'ᵒᵖ × 𝒜') ⟶ (Opposite.op Z₃, N)) ≫
              hc)) ≫ v =
      Si.map (HA.map ((a.op, χ) : ((Opposite.op (Sf.obj Y₁), Sf.obj M₁) : 𝒜'ᵒᵖ × 𝒜') ⟶
        (Opposite.op Z₃, N)) ≫ hc) ≫ v := by
  subst ha hχ
  simp only [← Si.map_comp_assoc, ← HA.map_comp_assoc]
  congr 3
  refine congrArg HA.map (Prod.ext ?_ ?_)
  · simp
  · simp

/-- Abstract triangle identity for a presentation `σ : E⁻¹ Y ≅ X` of an object. -/
public theorem equivalence_presentation_unit_counit {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (E : 𝒞 ≌ 𝒟) {X : 𝒞} {Y : 𝒟} (σ : E.inverse.obj Y ≅ X) :
    σ.hom ≫ E.unitIso.hom.app X ≫ E.inverse.map (E.functor.map σ.inv ≫ E.counitIso.hom.app Y) =
      𝟙 _ := by
  have hu : E.unitIso.hom.app X ≫ E.inverse.map (E.functor.map σ.inv) =
      σ.inv ≫ E.unitIso.hom.app (E.inverse.obj Y) := (E.unitIso.hom.naturality σ.inv).symm
  rw [E.inverse.map_comp, reassoc_of% hu, Iso.hom_inv_id_assoc]
  exact E.unit_inverse_comp Y

/-- Abstract glue: cancel a presentation `d` against its transported value. -/
public theorem cancel_presentation_glue {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (Ei : 𝒟 ⥤ 𝒞) {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : 𝒟} {W₀ T Z : 𝒞} (d : Ei.obj X₀ ≅ W₀)
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (r : X₂ ⟶ X₃) (s₁ : X₃ ⟶ X₄) (qc : X₂ ⟶ X₄)
    (x₁ : X₄ ⟶ X₅) (x₂ : X₅ ⟶ X₆) (u : W₀ ⟶ T) (σ' : T ⟶ Ei.obj X₃) (z : Ei.obj X₆ ⟶ Z)
    (hq : qc = r ≫ s₁) (hC : Ei.map (a ≫ b ≫ r) = d.hom ≫ u ≫ σ') :
    d.inv ≫ Ei.map (a ≫ b ≫ qc ≫ x₁ ≫ x₂) ≫ z = u ≫ σ' ≫ Ei.map (s₁ ≫ x₁ ≫ x₂) ≫ z := by
  subst hq
  have h : Ei.map (a ≫ b ≫ (r ≫ s₁) ≫ x₁ ≫ x₂) =
      Ei.map (a ≫ b ≫ r) ≫ Ei.map (s₁ ≫ x₁ ≫ x₂) := by
    simp only [Functor.map_comp, Category.assoc]
  rw [h, hC]
  simp

/-- Abstract cancellation `a ≫ (U b ≫ U c) ≫ d = 𝟙` from `b ≫ c = 𝟙` and `a ≫ d = 𝟙`. -/
public theorem cancel_four_of_map {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (U : 𝒞 ⥤ 𝒟)
    {X Y : 𝒞} {W : 𝒟} (a : W ⟶ U.obj X) (b : X ⟶ Y) (c : Y ⟶ X) (d : U.obj X ⟶ W)
    (hbc : b ≫ c = 𝟙 X) (had : a ≫ d = 𝟙 W) : (a ≫ U.map b) ≫ U.map c ≫ d = 𝟙 W := by
  rw [Category.assoc, ← U.map_comp_assoc, hbc, U.map_id, Category.id_comp, had]

/-- Abstract form of the transport of `δ` against its chain value: if `λ` is the transpose of
`ψi ≫ dh` across `E` then the unit, `E⁻¹ λ` and `di = dh⁻¹` compose to `ψi`. -/
public theorem unit_inverse_map_transpose_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (E : 𝒞 ≌ 𝒟) {z' P : 𝒞} {Vq : 𝒟} (ψi : z' ⟶ P) (dh : P ⟶ E.inverse.obj Vq)
    (di : E.inverse.obj Vq ⟶ P) (hd : dh ≫ di = 𝟙 P) (lam : E.functor.obj z' ⟶ Vq)
    (hlam : lam = E.functor.map (ψi ≫ dh) ≫ E.counitIso.hom.app Vq) :
    E.unitIso.hom.app z' ≫ E.inverse.map lam ≫ di = ψi := by
  subst hlam
  have hu : E.unitIso.hom.app z' ≫ E.inverse.map (E.functor.map (ψi ≫ dh)) =
      (ψi ≫ dh) ≫ E.unitIso.hom.app (E.inverse.obj Vq) := (E.unitIso.hom.naturality _).symm
  have ht : E.unitIso.hom.app (E.inverse.obj Vq) ≫ E.inverse.map (E.counitIso.hom.app Vq) =
      𝟙 _ := E.unit_inverse_comp Vq
  rw [E.inverse.map_comp, Category.assoc, reassoc_of% hu]
  simp only [reassoc_of% ht, hd, Category.comp_id]

/-- Abstract solution of a transposed equation for its first factor. -/
public theorem solve_transpose_of_key {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (Ef : 𝒞 ⥤ 𝒟)
    {z' P P₁ : 𝒞} {T₁ Vq Vq' M : 𝒟} (ψi : z' ⟶ P) (ψ₁ : P ⟶ P₁) (ψ₂ : P₁ ⟶ z')
    (hψ : ψi ≫ ψ₁ ≫ ψ₂ = 𝟙 z') (x₁ : Ef.obj z' ⟶ Vq') (x₂ : Vq' ⟶ Vq) (fh : Vq ≅ M)
    (s : Ef.obj z' ⟶ T₁) (r : T₁ ⟶ M)
    (key : x₁ ≫ x₂ ≫ fh.hom = Ef.map (ψi ≫ ψ₁ ≫ ψ₂) ≫ s ≫ r) :
    s ≫ r ≫ fh.inv = x₁ ≫ x₂ := by
  rw [hψ, Ef.map_id, Category.id_comp] at key
  rw [← Category.assoc, ← key]
  simp

/-- Abstract form of the naturality step of the transported unit chain. -/
public theorem unit_chain_naturality_step {𝒞 𝒜 : Type*} [Category 𝒞] [Category 𝒜]
    (U : 𝒜 ⥤ 𝒞) {n₀ z' Y₀ : 𝒞} {y y₁ y₂ : 𝒜} (qφ : n₀ ⟶ z') (qη : n₀ ⟶ Y₀)
    (qr : Y₀ ⟶ z') (fi' : z' ⟶ U.obj y₁) (fu : Y₀ ⟶ U.obj y) (k₁ : y ⟶ y₁) (k₂ : y₁ ⟶ y₂)
    (hφ : qφ = qη ≫ qr) (hn : qr ≫ fi' = fu ≫ U.map k₁) :
    qφ ≫ fi' ≫ U.map k₂ = qη ≫ fu ≫ U.map (k₁ ≫ k₂) := by
  subst hφ
  rw [U.map_comp, Category.assoc, reassoc_of% hn]

/-- Abstract form of the scalar-lift unit cancellation. -/
public theorem scalarLift_unit_cancel {𝒜 𝒜' : Type*} [Category 𝒜] [Category 𝒜'] (S : 𝒜 ≌ 𝒜')
    {y : 𝒜} {zz : 𝒜'} {W : 𝒜} (sl : S.functor.obj y ≅ zz) (sif : S.inverse.obj zz ≅ W)
    (c : y ⟶ W) (h : S.unitIso.hom.app y ≫ S.inverse.map sl.hom ≫ sif.hom = c) :
    (c ≫ sif.inv) ≫ S.inverse.map sl.inv ≫ S.unitIso.inv.app y = 𝟙 y := by
  subst h
  simp

/-- Abstract assembly of the transported unit chain. -/
public theorem transported_unit_chain_assembly {𝒞 𝒟 𝒜 𝒜' : Type*} [Category 𝒞] [Category 𝒟]
    [Category 𝒜] [Category 𝒜'] (E : 𝒞 ≌ 𝒟) (U : 𝒜 ⥤ 𝒞) (Sf : 𝒜 ⥤ 𝒜') (Si : 𝒜' ⥤ 𝒜)
    (V : 𝒜' ⥤ 𝒟) (δinv : V ⋙ E.inverse ⟶ Si ⋙ U) {n₀ z' : 𝒞} {L₁ L₂ M₁ : 𝒟} {y : 𝒜}
    {zz : 𝒜'} {Y₀ : 𝒞} (a : E.functor.obj n₀ ⟶ L₁) (qlφ : L₁ ⟶ L₂) (qs : L₂ ⟶ M₁)
    (fi : M₁ ⟶ V.obj zz) (w : zz ⟶ Sf.obj y) (ν : Si.obj (Sf.obj y) ⟶ y)
    (qφ : n₀ ⟶ z') (a' : E.functor.obj z' ⟶ L₂) (ψi : z' ⟶ U.obj (Si.obj zz))
    (qη : n₀ ⟶ Y₀) (fu : Y₀ ⟶ U.obj y) (κ : y ⟶ Si.obj zz) (qL : L₁ ⟶ M₁)
    (hq : qL = qlφ ≫ qs)
    (H1 : a ≫ qlφ = E.functor.map qφ ≫ a')
    (H2 : E.unitIso.hom.app z' ≫ E.inverse.map (a' ≫ qs ≫ fi) ≫ δinv.app zz = ψi)
    (H3 : qφ ≫ ψi = qη ≫ fu ≫ U.map κ) (H4 : κ ≫ Si.map w ≫ ν = 𝟙 y) :
    E.unitIso.hom.app n₀ ≫ E.inverse.map a ≫ E.inverse.map (qL ≫ fi ≫ V.map w) ≫
        δinv.app (Sf.obj y) ≫ U.map ν = qη ≫ fu := by
  subst hq
  rw [Category.assoc]
  have hδ : E.inverse.map (V.map w) ≫ δinv.app (Sf.obj y) = δinv.app zz ≫ U.map (Si.map w) :=
    δinv.naturality w
  have hu : E.unitIso.hom.app n₀ ≫ E.inverse.map (E.functor.map qφ) =
      qφ ≫ E.unitIso.hom.app z' := (E.unitIso.hom.naturality qφ).symm
  have H4' : U.map κ ≫ U.map (Si.map w) ≫ U.map ν = 𝟙 _ := by
    rw [← U.map_comp, ← U.map_comp, H4, U.map_id]
  have hsplit : E.inverse.map a ≫ E.inverse.map (qlφ ≫ qs ≫ fi ≫ V.map w) =
      E.inverse.map (E.functor.map qφ) ≫ E.inverse.map (a' ≫ qs ≫ fi) ≫
        E.inverse.map (V.map w) := by
    rw [← E.inverse.map_comp, ← E.inverse.map_comp, ← E.inverse.map_comp]
    congr 1
    simp only [← Category.assoc, H1]
  rw [reassoc_of% hsplit, reassoc_of% hu, reassoc_of% hδ]
  have H2' : E.unitIso.hom.app z' ≫ E.inverse.map (a' ≫ qs ≫ fi) ≫ δinv.app zz ≫
      U.map (Si.map w) ≫ U.map ν = ψi ≫ U.map (Si.map w) ≫ U.map ν := by
    rw [← H2]
    simp only [Category.assoc]
  rw [H2', reassoc_of% H3, H4', Category.comp_id]

/-- Abstract assembly of a transported composite against a presentation and its inverse. -/
public theorem map_comp_eq_comp_of_presentation {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (Ei : 𝒟 ⥤ 𝒞) {X₁ X₂ X₃ X₄ X₅ : 𝒟} {W : 𝒞} (m₁ : X₁ ⟶ X₂) (m₂ : X₂ ⟶ X₃) (p : X₁ ⟶ X₃)
    (t : X₃ ⟶ X₄) (r : X₄ ⟶ X₅) (σ : Ei.obj X₅ ⟶ W) (ρ : W ⟶ Ei.obj X₅)
    (h1 : m₁ ≫ m₂ = p) (h2 : σ ≫ ρ = 𝟙 _) :
    Ei.map (p ≫ t ≫ r) = (Ei.map m₁ ≫ (Ei.map m₂ ≫ Ei.map t) ≫ (Ei.map r ≫ σ)) ≫ ρ := by
  subst h1
  simp only [Functor.map_comp, Category.assoc, h2, Category.comp_id]

/-- The presentation of the class of `X` by its lift, then the unit and the inverse of the scalar
lift presentation, compose to the identity. -/
private theorem scalarEquivalenceQObjIso_hom_comp_unitIso_comp_scalarLiftQObjIso
    (B : Type u) [CommRing B] (X : CochainComplex (ModuleCat.{max u v} B) ℤ) :
    (CochainComplex.DerivedTensor.scalarEquivalenceQObjIso.{u, v} B X).hom ≫
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v}
        B).unitIso.hom.app (DerivedCategory.Q.obj X) ≫
        (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v}
          B).inverse.map (scalarLiftQObjIso.{u, v} B X).hom = 𝟙 _ := by
  have hcounit : (derivedScalarEquivalence.{u, v, max u v + 1} B).unitIso.inv.app
        (DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X)) =
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v}
        B).counitIso.hom.app (DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X)) := by
    rw [_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_unitIso]
    rfl
  rw [← scalarEquivalence_map_scalarEquivalenceQObjIso_inv_comp_unitIso_inv.{u, v} B X, hcounit]
  exact equivalence_presentation_unit_counit
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v} B)
    (CochainComplex.DerivedTensor.scalarEquivalenceQObjIso.{u, v} B X)

/-- **The K-flat presentation of a derived tensor product, transported into the scalar-lift
world.**  The scalar lift of `CochainComplex.DerivedTensor.derivedTensor_comparison` is the
fixed-universe tensor of the two scalar-lift presentations, followed by the K-flat tensor model
over the lifted ring and the comparison of the lifted total tensor complex with the lift of the
total tensor complex. -/
public theorem scalarEquivalence_inverse_map_tensor_scalarLift
    (B : Type u) [CommRing B] (K L : CochainComplex (ModuleCat.{max u v} B) ℤ)
    (hL : CochainComplex.DerivedTensor.IsKFlat.{u, v} L) :
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v} B
    E.inverse.map ((DerivedInternalHom.Model.adjunction (ULift.{v} B)).tensor.map
          (((scalarLiftQObjIso.{u, v} B K).hom, (scalarLiftQObjIso.{u, v} B L).hom) :
            ((E.functor.obj (DerivedCategory.Q.obj K), E.functor.obj (DerivedCategory.Q.obj L)) :
              DerivedCategory (ModuleCat.{max u v} (ULift.{v} B)) ×
                DerivedCategory (ModuleCat.{max u v} (ULift.{v} B))) ⟶
            (DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max u v}
                (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K),
              DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max u v}
                (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj L))) ≫
        ((DerivedInternalHom.Model.adjunction (ULift.{v} B)).tensorIso
            (((ModuleCat.restrictScalars.{max u v}
              (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)
            (((ModuleCat.restrictScalars.{max u v}
              (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj L)
            (kFlat_scalarLift.{u, v} B L hL)).hom ≫
          DerivedCategory.Q.map (CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso
            (ULift.ringEquiv : ULift.{v} B ≃+* B) K L).hom) =
      (CochainComplex.DerivedTensor.derivedTensor_comparison.{u, v} B K L hL).hom ≫
        E.unitIso.hom.app (DerivedCategory.Q.obj (CochainComplex.DerivedTensor.tensorComplex K L)) ≫
          E.inverse.map (scalarLiftQObjIso.{u, v} B
            (CochainComplex.DerivedTensor.tensorComplex K L)).hom := by
  intro E
  let D := derivedScalarEquivalence.{u, v, max u v + 1} B
  let TR := (DerivedInternalHom.Model.adjunction (ULift.{v} B)).tensor
  let lift := (ModuleCat.restrictScalars.{max u v}
    (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)
  let N := CochainComplex.DerivedTensor.tensorComplex K L
  have hiK := scalarEquivalence_map_scalarEquivalenceQObjIso_inv_comp_unitIso_inv.{u, v} B K
  have hiL := scalarEquivalence_map_scalarEquivalenceQObjIso_inv_comp_unitIso_inv.{u, v} B L
  have h1 : TR.map ((E.functor.map (CochainComplex.DerivedTensor.scalarEquivalenceQObjIso.{u, v}
          B K).inv, E.functor.map (CochainComplex.DerivedTensor.scalarEquivalenceQObjIso.{u, v}
          B L).inv) : (E.functor.obj (DerivedCategory.Q.obj K),
            E.functor.obj (DerivedCategory.Q.obj L)) ⟶
            (E.functor.obj (E.inverse.obj (DerivedCategory.Q.obj (lift.obj K))),
              E.functor.obj (E.inverse.obj (DerivedCategory.Q.obj (lift.obj L))))) ≫
        TR.map ((D.unitIso.inv.app (DerivedCategory.Q.obj (lift.obj K)),
          D.unitIso.inv.app (DerivedCategory.Q.obj (lift.obj L))) :
            (E.functor.obj (E.inverse.obj (DerivedCategory.Q.obj (lift.obj K))),
              E.functor.obj (E.inverse.obj (DerivedCategory.Q.obj (lift.obj L)))) ⟶
            (DerivedCategory.Q.obj (lift.obj K), DerivedCategory.Q.obj (lift.obj L))) =
      TR.map (((scalarLiftQObjIso.{u, v} B K).hom, (scalarLiftQObjIso.{u, v} B L).hom) :
        (E.functor.obj (DerivedCategory.Q.obj K), E.functor.obj (DerivedCategory.Q.obj L)) ⟶
          (DerivedCategory.Q.obj (lift.obj K), DerivedCategory.Q.obj (lift.obj L))) := by
    rw [← TR.map_comp]
    exact congrArg TR.map (Prod.ext hiK hiL)
  have h2 := scalarEquivalenceQObjIso_hom_comp_unitIso_comp_scalarLiftQObjIso.{u, v} B N
  exact map_comp_eq_comp_of_presentation E.inverse _ _ _ _ _ _ _ h1 h2

/-- **The transposed K-flat tensor presentation followed by the model internal Hom is a localized
chain map.**  Over a ring `B`, the inverse transpose of [stacks 0A63] of the K-flat presentation
of `Q P ⊗ᴸ Q P'` followed by a chain map `e`, read into the model internal Hom over the lift of
`B` through a contravariant chain map `lam` and a covariant chain map `n` into a K-injective
complex, is the localization of the chain-level currying of `rSTCI ≫ lift e ≫ n` followed by
precomposition with `lam`, pushed down along the scalar lift. -/
public theorem homEquiv_symm_derivedTensor_comparison_comp_model (B : Type u) [CommRing B]
    (P P' N' : CochainComplex (ModuleCat.{max u v} B) ℤ)
    (hP' : CochainComplex.DerivedTensor.IsKFlat.{u, v} P')
    (e : CochainComplex.DerivedTensor.tensorComplex P P' ⟶ N')
    (X J : CochainComplex (ModuleCat.{max u v} (ULift.{v} B)) ℤ) [J.IsKInjective]
    (lam : X ⟶ ((ModuleCat.restrictScalars.{max u v}
        (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P')
    (n : ((ModuleCat.restrictScalars.{max u v}
        (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N' ⟶ J) :
    let S := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, v} B
    let HA := DerivedInternalHom.Model.hom (ULift.{v} B)
    let dB := derivedHomAdjunctionOverRing.{u, v, max u v + 1} B
    let lift := (ModuleCat.restrictScalars.{max u v}
        (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)
    (dB.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj P')
          (DerivedCategory.Q.obj N')).symm
        ((CochainComplex.DerivedTensor.derivedTensor_comparison.{u, v} B P P' hP').hom ≫
          DerivedCategory.Q.map e) ≫
      S.inverse.map (HA.map ((DerivedCategory.Q.map lam ≫ (scalarLiftQObjIso.{u, v} B P').inv).op,
          (scalarLiftQObjIso.{u, v} B N').hom ≫ DerivedCategory.Q.map n) ≫
        (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.Model.homComplexIso X J).hom) ≫
        (scalarEquivalenceInverseFactors.{u, v} B).hom.app
          (CochainComplex.HomComplexR (ULift.{v} B) X J) =
      DerivedCategory.Q.map (scalarLiftCounitInv.{u, v} B P ≫
        ((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).symm.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} B) (lift.obj P) (lift.obj P') ≫
            Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} B) (lift.obj P') _ J
              ((CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso
                (ULift.ringEquiv : ULift.{v} B ≃+* B) P P').hom ≫ lift.map e ≫ n) ≫
            Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} B) X (lift.obj P') J lam)) := by
  intro S HA dB lift
  let D := derivedScalarEquivalence.{u, v, max u v + 1} B
  let sEQ := CochainComplex.DerivedTensor.scalarEquivalenceQObjIso.{u, v} B
  let h := (CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso
    (ULift.ringEquiv : ULift.{v} B ≃+* B) P P').hom ≫ lift.map e ≫ n
  have hP'₀ : CochainComplex.KFlat (lift.obj P') := kFlat_scalarLift.{u, v} B P' hP'
  have hk : ((CochainComplex.DerivedTensor.derivedTensor_comparison.{u, v} B P P' hP').hom ≫
      DerivedCategory.Q.map e) ≫ S.unitIso.hom.app (DerivedCategory.Q.obj N') ≫
        S.inverse.map ((scalarLiftQObjIso.{u, v} B N').hom ≫ DerivedCategory.Q.map n) =
      dB.tensor.map (CategoryTheory.Prod.mkHom (sEQ P).inv (sEQ P').inv) ≫
        (derivedTensorModelIso.{u, v, max u v + 1} B (lift.obj P) (lift.obj P') hP'₀).hom ≫
          S.inverse.map (DerivedCategory.Q.map h) := by
    have h2N := scalarEquivalenceQObjIso_hom_comp_unitIso_comp_scalarLiftQObjIso.{u, v} B N'
    have hQh : DerivedCategory.Q.map h = DerivedCategory.Q.map
          (CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso
            (ULift.ringEquiv : ULift.{v} B ≃+* B) P P').hom ≫
        DerivedCategory.Q.map (lift.map e) ≫ DerivedCategory.Q.map n := by
      simp only [h, Functor.map_comp]
    exact presentation_covariant_step S.inverse _ _ _ _ _ _ _ _ _ _
      (CochainComplex.DerivedTensor.scalarEquivalenceQObjIso_naturality.{u, v} B e).symm h2N _ hQh
  refine (congrArg (fun z => (dB.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj P')
          (DerivedCategory.Q.obj N')).symm
        ((CochainComplex.DerivedTensor.derivedTensor_comparison.{u, v} B P P' hP').hom ≫
          DerivedCategory.Q.map e) ≫ z)
    (fold_covariant_through_equivalence S HA
      (DerivedCategory.Q.map lam ≫ (scalarLiftQObjIso.{u, v} B P').inv)
      ((scalarLiftQObjIso.{u, v} B N').hom ≫ DerivedCategory.Q.map n)
      (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.Model.homComplexIso X J).hom
      ((scalarEquivalenceInverseFactors.{u, v} B).hom.app
          (CochainComplex.HomComplexR (ULift.{v} B) X J)))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_naturality_right dB
      (S.unitIso.hom.app (DerivedCategory.Q.obj N') ≫
        S.inverse.map ((scalarLiftQObjIso.{u, v} B N').hom ≫ DerivedCategory.Q.map n))
      ((CochainComplex.DerivedTensor.derivedTensor_comparison.{u, v} B P P' hP').hom ≫
          DerivedCategory.Q.map e)).symm)).trans ?_
  rw [hk]
  refine (StacksDraft.DerivedHom.DerivedHomAdjunction.homEquiv_symm_tensor_map_mkHom_assoc dB
    (sEQ P).inv (sEQ P').inv _ _).trans ?_
  have hd : (dB.homEquiv (D.functor.obj (DerivedCategory.Q.obj (lift.obj P)))
        (D.functor.obj (DerivedCategory.Q.obj (lift.obj P')))
        (D.functor.obj (DerivedCategory.Q.obj J))).symm
        ((derivedTensorModelIso.{u, v, max u v + 1} B (lift.obj P) (lift.obj P') hP'₀).hom ≫
          D.functor.map (DerivedCategory.Q.map h)) =
      D.functor.map (DerivedCategory.Q.map
          (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} B) (lift.obj P) (lift.obj P') ≫
            Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} B) (lift.obj P') _ J h)) ≫
        (derivedHomModelIso.{u, v, max u v + 1} B (lift.obj P') J).inv :=
    StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_homEquiv_symm_apply (lift.obj P)
      (lift.obj P') J hP'₀ h
  refine (congrArg (fun z => (sEQ P).inv ≫ z) (congrArg (· ≫ _) hd)).trans ?_
  have hi3 := scalarEquivalence_map_scalarEquivalenceQObjIso_inv_comp_unitIso_inv.{u, v} B P'
  have H3 : (DerivedCategory.Q.map lam ≫ (scalarLiftQObjIso.{u, v} B P').inv) ≫
      S.functor.map (sEQ P').inv ≫ D.unitIso.inv.app (DerivedCategory.Q.obj (lift.obj P')) =
      DerivedCategory.Q.map lam := by
    rw [hi3, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have H5 := (derivedHomAdjunctionULift.{u, v, max u v + 1} (R := B)).homIso_naturality lam (𝟙 J)
  have hpost : Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} B) X (lift.obj P') J lam ≫
      Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} B) X J J (𝟙 J) =
      Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} B) X (lift.obj P') J lam := by
    rw [DerivedInternalHom.Model.postcomp_id, Category.comp_id]
  have H8 : (sEQ P).inv ≫ S.inverse.map (DerivedCategory.Q.map
        (Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} B) (lift.obj P) (lift.obj P') ≫
          Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} B) (lift.obj P') _ J h) ≫
        DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} B) X
          (lift.obj P') J lam ≫
          Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} B) X J J (𝟙 J))) ≫
      (scalarEquivalenceInverseFactors.{u, v} B).hom.app
          (CochainComplex.HomComplexR (ULift.{v} B) X J) =
      DerivedCategory.Q.map (scalarLiftCounitInv.{u, v} B P ≫
        ((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).symm.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((Stacks.HomComplex.TensorHomMap.Phi (ULift.{v} B) (lift.obj P) (lift.obj P') ≫
            Stacks.HomComplex.TensorHomMap.postcomp (ULift.{v} B) (lift.obj P') _ J h) ≫
            Stacks.HomComplex.TensorHomMap.precomp (ULift.{v} B) X (lift.obj P') J lam)) := by
    rw [hpost, ← DerivedCategory.Q.map_comp]
    have h2P := scalarEquivalenceQObjIso_hom_comp_unitIso_comp_scalarLiftQObjIso.{u, v} B P
    have hs : (sEQ P).inv ≫ (scalarEquivalenceInverseFactors.{u, v} B).hom.app (lift.obj P) =
        DerivedCategory.Q.map (scalarLiftCounitInv.{u, v} B P) := by
      rw [Iso.inv_ext h2P]
      exact (Category.assoc _ _ _).trans (scalarEquivalence_unitIso_hom_app_Q_comp.{u, v} B P)
    exact presentation_comp_map_comp_factors DerivedCategory.Q DerivedCategory.Q S.inverse
      ((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).symm.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ))
      (scalarEquivalenceInverseFactors.{u, v} B) (scalarLiftCounitInv.{u, v} B P) _ _ hs
  refine (transpose_model_tail_assembly S D.unitIso
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_unitIso.{u, v,
      max u v + 1} B) HA (sEQ P).inv _ ((derivedHomAdjunctionULift.{u, v, max u v + 1}
        (R := B)).homIso (lift.obj P') J) (sEQ P').inv _
    (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.Model.homComplexIso X J) _ _ _ _ _ H3
    (DerivedCategory.Q.map_id J) H5 H8)

section Delta

universe uR uA uM

attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- **The scalar-restriction comparison `δ` at a class, transposed and inverted.**  At the class
of a cochain complex `Z` of modules over the lift of `A`, the unit of the scalar lift over `R`,
then the scalar lift's inverse of the chain value
`Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison`, then the inverse component of
`δ`, is the inverse factorization of derived restriction along `f` followed by the restriction of
the inverse factorization of the scalar lift over `A`. -/
public theorem unitIso_comp_inverse_map_chain_comp_scalarRestrictionIso_inv
    (Z : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    let E := _root_.Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max uR uA uM} R
    let Z' := ((ModuleCat.restrictScalars.{max uR uA uM} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z)
    E.unitIso.hom.app (DerivedCategory.Q.obj Z') ≫
        E.inverse.map ((scalarLiftQObjIso.{uR, max uR uA uM} R Z').hom ≫
          DerivedCategory.Q.map (scalarRestrictionChainComparison.{uR, uA, uM} f Z) ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.inv.app Z) ≫
          (scalarRestrictionIso.{uR, uA, uM} f).inv.app (DerivedCategory.Q.obj Z) =
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
          ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).inv.app Z) := by
  intro f' E Z'
  let U := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
  let ψi := (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z) ≫
        U.map ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).inv.app Z)
  have key := scalarRestrictionIso_hom_app_Q_comp_counit.{uR, uA, uM} f Z
    (DerivedCategory.Q.obj Z') ψi
  have hψ : ψi ≫ U.map ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app Z) ≫
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z) = 𝟙 _ :=
    cancel_four_of_map U _ _ _ _ (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)
  have hlam := solve_transpose_of_key E.functor ψi _ _ hψ _ _
    ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app Z) _ _ key
  exact unit_inverse_map_transpose_comp E ψi
    ((scalarRestrictionIso.{uR, uA, uM} f).hom.app (DerivedCategory.Q.obj Z))
    ((scalarRestrictionIso.{uR, uA, uM} f).inv.app (DerivedCategory.Q.obj Z))
    ((scalarRestrictionIso.{uR, uA, uM} f).hom_inv_id_app _) _ hlam

/-- **`Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison` is natural.**  It is the
identity on underlying elements. -/
public theorem scalarRestrictionChainComparison_naturality
    {Z₁ Z₂ : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ}
    (g : Z₁ ⟶ Z₂) :
    scalarRestrictionChainComparison.{uR, uA, uM} f Z₁ ≫
        ((ModuleCat.restrictScalars.{max uR uA uM}
          (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g =
      ((ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((ModuleCat.restrictScalars.{max uR uA uM} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
            (((ModuleCat.restrictScalars.{max uR uA uM}
              (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).map g)) ≫
        scalarRestrictionChainComparison.{uR, uA, uM} f Z₂ := by
  ext n x
  rfl

end Delta

end Stacks.DerivedHom.BaseChange

end
