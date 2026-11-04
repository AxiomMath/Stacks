module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.DerivedInternalHom
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso

/-!
# Change of rings on Hom complexes

The scalar-transported derived internal Hom
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom` in an independently chosen module universe:
scalars are lifted along `ULift.ringEquiv`, the canonical K-flat/K-injective construction of
`StacksDraft.DerivedHom` is applied, and scalars are restricted back, through the transport
`Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence`.

For a ring map `f : R → A`, the change-of-rings comparison of Hom complexes
`Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` (scalar adjunction followed by a map to
an injective representative), and its quasi-isomorphism on K-flat and K-injective representatives
`Stacks.DerivedHom.BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat`.
-/

open StacksDraft.DerivedHom.Construction (KInjectiveObjects Q_map_surjective_of_isKInjective
    postcomp_bijective postcomp_quasiIso_of_homotopyEquivalence precomp_bijective
    precomp_quasiIso_of_homotopyEquivalence)

section ScalarTransportedHom

open CategoryTheory

namespace Stacks.DerivedHom.ScalarTransportedInternalHom

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- The derived equivalence induced by the canonical isomorphism `ULift.{v} R ≃+* R`.
The original ring, ambient module size, and derived-morphism size are independent. -/
@[expose]
public noncomputable def scalarEquivalence (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] :
    DerivedCategory (ModuleCat.{max u v} R) ≌
      DerivedCategory (ModuleCat.{max u v} (ULift.{v} R)) := by
  let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ULift.ringEquiv : ULift.{v} R ≃+* R)
  let ec := e.mapHomologicalComplex (ComplexShape.up ℤ)
  refine Localization.equivalence DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} (ULift.{v} R)) (ComplexShape.up ℤ))
    (e.functor.mapHomologicalComplex _ ⋙ DerivedCategory.Q) e.functor.mapDerivedCategory
    (e.inverse.mapHomologicalComplex _ ⋙ DerivedCategory.Q) e.inverse.mapDerivedCategory ?_ ?_
  · exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e.inverse.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.unitIso.symm _ ≪≫ Functor.leftUnitor _
  · exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ e.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ec.counitIso _ ≪≫ Functor.leftUnitor _

/-- The scalar-lifting derived equivalence `scalarEquivalence R` has an additive functor. -/
instance (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] :
    (scalarEquivalence R).functor.Additive := by
  change (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).mapDerivedCategory.Additive
  infer_instance

/-- The scalar-lifting derived equivalence `scalarEquivalence R` has an additive inverse. -/
instance (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] :
    (scalarEquivalence R).inverse.Additive := by
  change (ModuleCat.restrictScalars
    (ULift.ringEquiv : ULift.{v} R ≃+* R).symm.toRingHom).mapDerivedCategory.Additive
  infer_instance

/-- The derived internal-Hom bifunctor in an independently chosen universe of modules.
Lift scalars to the common universe, apply the fixed K-injective construction, then restrict
scalars back to `R`. -/
@[expose]
public noncomputable def hom (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)] :
    (DerivedCategory (ModuleCat.{max u v} R))ᵒᵖ ×
      DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R) :=
  Functor.prod (scalarEquivalence R).functor.op (scalarEquivalence R).functor ⋙
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := ULift.{v} R)).hom ⋙
      (scalarEquivalence R).inverse

/-- A K-injective target computes derived internal Hom by the ordinary Hom complex. -/
public noncomputable abbrev Model.homComplexIso {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{u} R)] (L I : CochainComplex (ModuleCat.{u} R) ℤ)
    [I.IsKInjective] :
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom R).obj
        (Opposite.op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR R L I) :=
  (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).homIso L I

end Stacks.DerivedHom.ScalarTransportedInternalHom

end ScalarTransportedHom

section DerivedHomChangeOfRings

open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChange

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

open CochainComplex HomComplex

section Complexes

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    (f : R →+* A)

/-- Restricting the coefficients of a homogeneous map is linear over the smaller ring. -/
private noncomputable def restrictCochainLinearMap
    (K L : CochainComplex (ModuleCat.{uM} A) ℤ) (n : ℤ) :
    (ModuleCat.restrictScalars f).obj (ModuleCat.of A (Cochain K L n)) →ₗ[R]
      Cochain (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj K)
        (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj L) n where
  toFun z := z.map (ModuleCat.restrictScalars f)
  map_add' z w := Cochain.map_add z w _
  map_smul' r z := by
    apply Cochain.ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of scalars on Hom complexes commutes with the Hom differential. -/
private noncomputable def homComplexRestrictScalarsMap
    (K L : CochainComplex (ModuleCat.{uM} A) ℤ) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
        (HomComplexR A K L) ⟶
      HomComplexR R
        (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj K)
        (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj L) where
  f n := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars f).obj ((HomComplexR A K L).X n))
    (restrictCochainLinearMap f K L n)
  comm' n m _ := ModuleCat.hom_ext (LinearMap.ext fun z ↦ δ_map n m z (ModuleCat.restrictScalars f))

set_option backward.isDefEq.respectTransparency false in
/-- The restriction comparison is natural in both complex variables. -/
private theorem homComplexRestrictScalarsMap_naturality
    {K K' L L' : CochainComplex (ModuleCat.{uM} A) ℤ}
    (a : K' ⟶ K) (b : L ⟶ L') :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map
        (Stacks.HomComplex.TensorHomMap.precomp A K' K L a ≫ Stacks.HomComplex.TensorHomMap.postcomp
          A K' L L' b) ≫
      homComplexRestrictScalarsMap f K' L' =
    homComplexRestrictScalarsMap f K L ≫
      (Stacks.HomComplex.TensorHomMap.precomp R _ _ _
          (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map a) ≫
        Stacks.HomComplex.TensorHomMap.postcomp R _ _ _
          (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).map b)) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  show (((Cochain.ofHom a).comp z (zero_add n)).comp
      (Cochain.ofHom b) (add_zero n)).map (ModuleCat.restrictScalars f) = _
  simp only [Cochain.map_comp, Cochain.map_ofHom]
  rfl

end Complexes

section ScalarAdjunction

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    (f : R →+* A)

/-- The scalar-extension unit on complexes is the degreewise scalar-extension unit. -/
private noncomputable def extendScalarsComplexUnit
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ) :
    K ⟶ (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj
      ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) where
  f n := (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).unit.app (K.X n)
  comm' n m _ :=
    ((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).unit.naturality (K.d n m)).symm

/-- The Hom-complex adjunction map, before taking any resolutions. -/
private noncomputable def homComplexExtendRestrictScalarsMap
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (J : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ) :
    (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj
        (HomComplexR A ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) J) ⟶
      HomComplexR R K ((CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj J) :=
  homComplexRestrictScalarsMap f _ _ ≫
    Stacks.HomComplex.TensorHomMap.precomp R K _ _ (extendScalarsComplexUnit.{uR, uA, uM} f K)

/-- In every degree, the comparison is precisely the scalar adjunction. -/
private theorem homComplexExtendRestrictScalarsMap_f_apply
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (J : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (n : ℤ) (z : Cochain ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) J n)
    (p q : ℤ) (hpq : p + n = q) :
    (((homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K J).f n) z).v p q hpq =
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).homEquiv
        (K.X p) (J.X q) (z.v p q hpq) := by
  show ((Cochain.ofHom (extendScalarsComplexUnit.{uR, uA, uM} f K)).comp
    (z.map (ModuleCat.restrictScalars f)) (zero_add n)).v p q hpq = _
  erw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.map_v]
  rfl

/-- The Hom-complex comparison is a bijection in every degree. -/
private theorem homComplexExtendRestrictScalarsMap_bijective
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (J : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ) (n : ℤ) :
    Function.Bijective ((homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K J).f n) := by
  constructor
  · intro z w h
    apply Cochain.ext
    intro p q hpq
    apply ((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).homEquiv
      (K.X p) (J.X q)).injective
    rw [← homComplexExtendRestrictScalarsMap_f_apply.{uR, uA, uM} f K J n z p q hpq,
      ← homComplexExtendRestrictScalarsMap_f_apply.{uR, uA, uM} f K J n w p q hpq, h]
  · intro z
    change Cochain K ((CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj J) n at z
    refine ⟨Cochain.mk (fun p q hpq =>
      ((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).homEquiv (K.X p) (J.X q)).symm
        (z.v p q hpq)), ?_⟩
    apply Cochain.ext
    intro p q hpq
    rw [homComplexExtendRestrictScalarsMap_f_apply]
    exact Equiv.apply_symm_apply _ _

/-- The degreewise scalar adjunction is an isomorphism of Hom complexes. -/
private theorem isIso_homComplexExtendRestrictScalarsMap
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (J : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ) :
    IsIso (homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K J) := by
  have (n : ℤ) : IsIso ((homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K J).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (homComplexExtendRestrictScalarsMap_bijective.{uR, uA, uM} f K J n)
  exact HomologicalComplex.Hom.isIso_of_components _

set_option backward.isDefEq.respectTransparency false in
/-- Scalar adjunction on Hom complexes is natural in both arguments. -/
private theorem homComplexExtendRestrictScalarsMap_naturality
    {K K' : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ}
    {J J' : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ}
    (a : K' ⟶ K) (b : J ⟶ J') :
    (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).map
        (Stacks.HomComplex.TensorHomMap.precomp A _ _ _
            ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).map a) ≫
          Stacks.HomComplex.TensorHomMap.postcomp A _ _ _ b) ≫
      homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K' J' =
    homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K J ≫
      (Stacks.HomComplex.TensorHomMap.precomp R _ _ _ a ≫ Stacks.HomComplex.TensorHomMap.postcomp R
        _ _ _
        ((CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).map b)) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change Cochain ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) J n at z
  show ((homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K' J').f n)
      (((Cochain.ofHom ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).map a)).comp z
        (zero_add n)).comp (Cochain.ofHom b) (add_zero n)) =
    ((Cochain.ofHom a).comp
      (((homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K J).f n) z)
        (zero_add n)).comp
      (Cochain.ofHom ((CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).map b)) (add_zero n)
  apply Cochain.ext
  intro p q hpq
  rw [homComplexExtendRestrictScalarsMap_f_apply,
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v,
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, homComplexExtendRestrictScalarsMap_f_apply]
  show (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).homEquiv _ _
      ((ModuleCat.extendScalars f).map (a.f p) ≫ z.v p q hpq ≫ b.f q) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact (Category.assoc _ _ _).symm

/-- The comparison on representatives is scalar adjunction followed by the chosen
map to an injective representative over the smaller ring. -/
public noncomputable def homComplexChangeOfRingsMap
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (J : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (I : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj J ⟶ I) :
    (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj
        (HomComplexR A ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) J) ⟶
      HomComplexR R K I :=
  homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K J ≫
    Stacks.HomComplex.TensorHomMap.postcomp R K _ I q

/-- The comparison on representatives has the degreewise formula of scalar adjunction
and postcomposition. -/
public theorem homComplexChangeOfRingsMap_f_apply
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (J : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (I : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj J ⟶ I)
    (n : ℤ) (z : Cochain ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) J n)
    (p r : ℤ) (hpr : p + n = r) :
    (((homComplexChangeOfRingsMap.{uR, uA, uM} f K J I q).f n) z).v p r hpr =
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).homEquiv
        (K.X p) (J.X r) (z.v p r hpr) ≫ q.f r := by
  show ((((homComplexExtendRestrictScalarsMap.{uR, uA, uM} f K J).f n) z).comp
    (Cochain.ofHom q) (add_zero n)).v p r hpr = _
  erw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rw [homComplexExtendRestrictScalarsMap_f_apply]
  rfl

end ScalarAdjunction

section HomComplexBifunctors

universe u

/-- Scalar adjunction is an isomorphism of the two ordinary Hom-complex bifunctors. -/
private noncomputable def homComplexExtendRestrictScalarsNatIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    Functor.prod (CochainComplex.extendScalarsLarge.{u, u, u} f).op
        (𝟭 (CochainComplex (ModuleCat.{u} A) ℤ)) ⋙
        StacksDraft.DerivedHom.Model.homComplexFunctor A ⋙
          CochainComplex.restrictScalarsLarge.{u, u, u} f ≅
      Functor.prod (𝟭 (CochainComplex (ModuleCat.{u} R) ℤ)ᵒᵖ)
        (CochainComplex.restrictScalarsLarge.{u, u, u} f) ⋙
        StacksDraft.DerivedHom.Model.homComplexFunctor R := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · exact @asIso _ _ _ _ (homComplexExtendRestrictScalarsMap.{u, u, u} f X.1.unop X.2)
      (isIso_homComplexExtendRestrictScalarsMap.{u, u, u} f X.1.unop X.2)
  · intro X Y g
    exact homComplexExtendRestrictScalarsMap_naturality.{u, u, u} f g.1.unop g.2

end HomComplexBifunctors

/-- An additive adjunction acts degreewise on cochain complexes. -/
private def mapCochainAdjunction
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G) :
    F.mapHomologicalComplex (.up ℤ) ⊣ G.mapHomologicalComplex (.up ℤ) where
  unit :=
    { app := fun K =>
        { f := fun n => adj.unit.app (K.X n)
          comm' := fun n m _ => (adj.unit.naturality (K.d n m)).symm }
      naturality := fun {X Y} g => by
        ext n
        exact adj.unit.naturality (g.f n) }
  counit :=
    { app := fun K =>
        { f := fun n => adj.counit.app (K.X n)
          comm' := fun n m _ => (adj.counit.naturality (K.d n m)).symm }
      naturality := fun {X Y} g => by
        ext n
        exact adj.counit.naturality (g.f n) }
  left_triangle_components K := by
    ext n
    exact adj.left_triangle_components (K.X n)
  right_triangle_components K := by
    ext n
    exact adj.right_triangle_components (K.X n)

/-- With an exact right-hand comparison, the derived adjunction can be normalized by
its original unit. Preservation of the relevant Kan extensions follows from the adjointness
of the derived functors. -/
private noncomputable def derivedAdjunctionWithUnitComparison
    {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂]
    {E : C₁ ⥤ C₂} {U : C₂ ⥤ C₁} (adj : E ⊣ U)
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    {E' : D₁ ⥤ D₂} {U' : D₂ ⥤ D₁}
    (α : L₁ ⋙ E' ⟶ E ⋙ L₂) (β : L₂ ⋙ U' ≅ U ⋙ L₁)
    [E'.IsLeftDerivedFunctor α W₁] [E'.IsLeftAdjoint] [U'.IsRightAdjoint] :
    {a : E' ⊣ U' // ∀ X : C₁,
      a.unit.app (L₁.obj X) ≫ U'.map (α.app X) =
        L₁.map (adj.unit.app X) ≫ β.inv.app (E.obj X)} := by
  letI := Functor.isRightDerivedFunctor_of_inverts W₂ U' β
  exact ⟨adj.derived W₁ W₂ α β.inv, fun X => adj.derivedη_fac_app W₁ α β.inv X⟩

private theorem isIso_leftDerivedCounit_app_of_comp
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {Q : C ⥤ D} {Q' : C' ⥤ D'} (W' : MorphismProperty C') [Q'.IsLocalization W']
    {E N : C ⥤ C'} {T : C' ⥤ C'} (eT : T ≅ 𝟭 C')
    {F B : D ⥤ D'} {G : D' ⥤ D'}
    (αF : Q ⋙ F ⟶ N ⋙ Q') (αB : Q ⋙ B ⟶ E ⋙ Q')
    (αG : Q' ⋙ G ⟶ T ⋙ Q') [G.IsLeftDerivedFunctor αG W']
    (eN : N ≅ E ⋙ T) (eF : F ≅ B ⋙ G)
    (h : Functor.whiskerLeft Q eF.hom ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight αB G ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft E αG ≫
        (Functor.associator _ _ _).inv =
      αF ≫ Functor.whiskerRight eN.hom Q')
    (K : C) [IsIso (αF.app K)] : IsIso (αB.app K) := by
  let e₀ : Q' ⋙ 𝟭 D' ≅ T ⋙ Q' :=
    Functor.rightUnitor Q' ≪≫ (Functor.leftUnitor Q').symm ≪≫
      Functor.isoWhiskerRight eT.symm Q'
  have : (𝟭 D').IsLeftDerivedFunctor e₀.hom W' :=
    Functor.isLeftDerivedFunctor_of_inverts W' _ e₀
  let eG : G ≅ 𝟭 D' := Functor.leftDerivedUnique (𝟭 D') G αG e₀.hom W'
  have : G.ReflectsIsomorphisms := reflectsIsomorphisms_of_iso eG.symm
  have : IsIso αG := by
    have hG : αG = Functor.whiskerLeft Q' eG.hom ≫ e₀.hom := by
      simp [eG]
    rw [hG]
    infer_instance
  have hK := congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hK
  have hB : G.map (αB.app K) = eF.inv.app (Q.obj K) ≫ αF.app K ≫
      Q'.map (eN.hom.app K) ≫ inv (αG.app (E.obj K)) := by
    rw [← Category.assoc (αF.app K), ← hK]
    simp
  have : IsIso (G.map (αB.app K)) := by
    rw [hB]
    infer_instance
  exact isIso_of_reflects_iso (αB.app K) G

open CategoryTheory.MonoidalCategory in
/-- If `α : Q ⋙ L ⟶ extendScalarsLarge f ⋙ Q` exhibits `L` as the left derived functor of
extension of scalars along `f`, then `α.app K` is an isomorphism for every K-flat complex `K`. -/
public theorem isIso_extendScalarsCounit_app_of_kFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
    (L : DerivedCategory (ModuleCat.{max uM uR uA} R) ⥤
      DerivedCategory (ModuleCat.{max uM uR uA} A))
    (α : DerivedCategory.Q ⋙ L ⟶
      CochainComplex.extendScalarsLarge.{uM, uR, uA} f ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max uM uR uA} R) (ComplexShape.up ℤ))]
    (K : CochainComplex (ModuleCat.{max uM uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uM uA} K) : IsIso (α.app K) := by
  let : MonoidalCategoryStruct (ModuleCat.{max uM uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max uM uA}
  let : MonoidalCategory (ModuleCat.{max uM uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max uM uA}
  let : MonoidalCategoryStruct (ModuleCat.{max uM uR uA} A) :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max uM uR}
  let : MonoidalCategory (ModuleCat.{max uM uR uA} A) :=
    ModuleCat.liftedModuleMonoidal.{uA, max uM uR}
  obtain ⟨N, _, eN, F, B, G, cF, _, αF, αB, αG, hF, hB, hG, hflat, eF, hfac⟩ :=
    CochainComplex.DerivedTensor.exists_derived_tensor_change_of_rings.{uR, uA, uM} f
      (HomologicalComplex.tensorUnit (ModuleCat.{max uM uR uA} A) (ComplexShape.up ℤ))
  have := hB
  have := hG
  have : IsIso (αF.app K) := hflat K hK
  have : IsIso (αB.app K) := isIso_leftDerivedCounit_app_of_comp
    (HomologicalComplex.quasiIso (ModuleCat.{max uM uR uA} A) (ComplexShape.up ℤ))
    (trightCochainTensorUnitIso _) αF αB αG eN eF hfac K
  let e : L ≅ B := Functor.leftDerivedUnique B L α αB
    (HomologicalComplex.quasiIso (ModuleCat.{max uM uR uA} R) (ComplexShape.up ℤ))
  have he : e.hom.app (DerivedCategory.Q.obj K) ≫ αB.app K = α.app K := by
    simp [e]
  rw [← he]
  infer_instance

/-- A normalized derived adjunction sends the localized ordinary transpose to its derived
transpose. This formula holds before imposing any acyclicity condition on the source. -/
private theorem derivedAdjunction_homEquiv_map
    {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂]
    {E : C₁ ⥤ C₂} {U : C₂ ⥤ C₁} (adj : E ⊣ U)
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    {E' : D₁ ⥤ D₂} {U' : D₂ ⥤ D₁}
    (α : L₁ ⋙ E' ⟶ E ⋙ L₂) (β : L₂ ⋙ U' ≅ U ⋙ L₁)
    (a : E' ⊣ U')
    (ha : ∀ X, a.unit.app (L₁.obj X) ≫ U'.map (α.app X) =
      L₁.map (adj.unit.app X) ≫ β.inv.app (E.obj X))
    {X : C₁} {Y : C₂} (g : E.obj X ⟶ Y) :
    a.homEquiv _ _ (α.app X ≫ L₂.map g) ≫ β.hom.app Y =
      L₁.map (adj.homEquiv X Y g) := by
  rw [Adjunction.homEquiv_unit, U'.map_comp, ← Category.assoc, ha]
  simp only [Category.assoc]
  erw [← β.inv.naturality_assoc g]
  simp only [Functor.comp_map, Iso.inv_hom_id_app, Category.comp_id]
  rw [← L₁.map_comp]
  rfl

/-- A representative which computes a derived left adjoint gives the expected bijection
on derived morphisms, including a subsequent isomorphism of target representatives. -/
private theorem derivedAdjunction_bijective_on_representatives
    {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂]
    {E : C₁ ⥤ C₂} {U : C₂ ⥤ C₁} (_adj : E ⊣ U)
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
    {E' : D₁ ⥤ D₂} {U' : D₂ ⥤ D₁}
    (α : L₁ ⋙ E' ⟶ E ⋙ L₂) (β : L₂ ⋙ U' ≅ U ⋙ L₁)
    (a : E' ⊣ U') (X : C₁) (Y : C₂) (I : C₁)
    (q : U.obj Y ⟶ I) [IsIso (α.app X)] [IsIso (L₁.map q)] :
    Function.Bijective (fun g : L₂.obj (E.obj X) ⟶ L₂.obj Y =>
      a.homEquiv _ _ (α.app X ≫ g) ≫ β.hom.app Y ≫ L₁.map q) := by
  let e := (Iso.homCongr (asIso (α.app X)).symm (Iso.refl (L₂.obj Y))).trans
    ((a.homEquiv _ _).trans
      (Iso.homCongr (Iso.refl _) ((β.app Y) ≪≫ asIso (L₁.map q))))
  have he : (fun g : L₂.obj (E.obj X) ⟶ L₂.obj Y =>
      a.homEquiv _ _ (α.app X ≫ g) ≫ β.hom.app Y ≫ L₁.map q) = e := by
    funext g
    simp [e, Iso.homCongr_apply]
  rw [he]
  exact e.bijective

section HomComplexCohomology

universe v u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D]
    {K L : CochainComplex C ℤ} {K' L' : CochainComplex D ℤ}

/-- A morphism of Hom complexes sends cocycles to cocycles. -/
private def homComplexCocycleMap (g : HomComplex K L ⟶ HomComplex K' L') (n : ℤ) :
    Cocycle K L n →+ Cocycle K' L' n where
  toFun z := Cocycle.mk ((g.f n) (z : Cochain K L n)) (n + 1) rfl (by
    change (g.f n ≫ (HomComplex K' L').d n (n + 1)) (z : Cochain K L n) = 0
    rw [g.comm]
    change (g.f (n + 1)) (δ n (n + 1) (z : Cochain K L n)) = 0
    rw [Cocycle.δ_eq_zero]
    exact (g.f (n + 1)).hom.map_zero)
  map_zero' := by apply Cocycle.ext; exact map_zero (g.f n).hom
  map_add' x y := by apply Cocycle.ext; exact map_add (g.f n).hom _ _

/-- Morphisms of Hom complexes preserve coboundaries. -/
private theorem homComplexCocycleMap_mem_coboundaries
    (g : HomComplex K L ⟶ HomComplex K' L') (n : ℤ)
    (z : Cocycle K L n) (hz : z ∈ coboundaries K L n) :
    homComplexCocycleMap g n z ∈ coboundaries K' L' n := by
  obtain ⟨m, hm, w, hw⟩ := hz
  refine ⟨m, hm, (g.f m) w, ?_⟩
  show ((g.f m) ≫ (HomComplex K' L').d m n) w = _
  rw [g.comm]
  show (g.f n) (δ m n w) = (g.f n) (z : Cochain K L n)
  rw [hw]

/-- The induced additive map on the quotient of cocycles by coboundaries. -/
private def homComplexCohomologyMap (g : HomComplex K L ⟶ HomComplex K' L') (n : ℤ) :
    CohomologyClass K L n →+ CohomologyClass K' L' n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K' L' n).comp (homComplexCocycleMap g n)) (by
      intro z hz
      exact (CohomologyClass.mk_eq_zero_iff _).2
        (homComplexCocycleMap_mem_coboundaries g n z hz))

/-- The concrete quotient map computes the map on homology. -/
private noncomputable def homComplexLeftHomologyMapData
    (g : HomComplex K L ⟶ HomComplex K' L') (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) n).map g)
      (HomComplex.leftHomologyData K L n) (HomComplex.leftHomologyData K' L' n) where
  φK := AddCommGrpCat.ofHom (homComplexCocycleMap g n)
  φH := AddCommGrpCat.ofHom (homComplexCohomologyMap g n)
  commi := by ext z; rfl
  commf' := by
    ext z
    exact Cocycle.ext (ConcreteCategory.congr_hom (g.comm _ _) z).symm
  commπ := by ext z; rfl

/-- Bijectivity on cocycles modulo coboundaries detects quasi-isomorphisms of Hom complexes. -/
private theorem quasiIso_homComplex_iff (g : HomComplex K L ⟶ HomComplex K' L') :
    QuasiIso g ↔ ∀ n : ℤ, Function.Bijective (homComplexCohomologyMap g n) := by
  rw [quasiIso_iff]
  refine forall_congr' fun n => ?_
  rw [quasiIsoAt_iff, (homComplexLeftHomologyMapData g n).quasiIso_iff]
  exact ConcreteCategory.isIso_iff_bijective _

end HomComplexCohomology

section DerivedHomComplexCohomology

universe v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- Morphisms into a K-injective complex are unchanged by localization. -/
private noncomputable def homotopyToDerivedEquiv
    (K I : CochainComplex C ℤ) [I.IsKInjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj I) ≃
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj I) :=
  (Equiv.ofBijective DerivedCategory.Qh.map (IsKInjective.Qh_map_bijective _ I)).trans
    (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
      ((DerivedCategory.quotientCompQhIso C).app I))

private theorem homotopyToDerivedEquiv_map
    {K I : CochainComplex C ℤ} [I.IsKInjective] (g : K ⟶ I) :
    homotopyToDerivedEquiv K I ((HomotopyCategory.quotient C (.up ℤ)).map g) =
      DerivedCategory.Q.map g := by
  show (DerivedCategory.quotientCompQhIso C).inv.app K ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map g) ≫
    (DerivedCategory.quotientCompQhIso C).hom.app I = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  simp

/-- Cohomology classes of a Hom complex with K-injective target are derived morphisms. -/
private noncomputable def homComplexCohomologyDerivedEquiv
    (K I : CochainComplex C ℤ) [I.IsKInjective] (n : ℤ) :
    CohomologyClass K I n ≃ (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj (I⟦n⟧)) :=
  CohomologyClass.homAddEquiv.toEquiv.trans (homotopyToDerivedEquiv K (I⟦n⟧))

private theorem homComplexCohomologyDerivedEquiv_mk
    {K I : CochainComplex C ℤ} [I.IsKInjective] {n : ℤ} (z : Cocycle K I n) :
    homComplexCohomologyDerivedEquiv K I n (CohomologyClass.mk z) =
      DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) :=
  homotopyToDerivedEquiv_map _

end DerivedHomComplexCohomology

section ChangeOfRingsCohomology

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    (f : R →+* A)
    (K : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (J : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (I : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj J ⟶ I)

/-- The underlying abelian-group map of the change-of-rings comparison. -/
private noncomputable def homComplexChangeOfRingsAbMap :
    HomComplex ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) J ⟶ HomComplex K I :=
  ((forget₂ (ModuleCat.{max uR uA uM} R) Ab).mapHomologicalComplex (.up ℤ)).map
    (homComplexChangeOfRingsMap.{uR, uA, uM} f K J I q)

/-- The comparison agrees with scalar adjunction on shifted chain maps. -/
private theorem homComplexChangeOfRingsAbMap_homShift
    (n : ℤ) (z : Cocycle ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) J n) :
    Cocycle.equivHomShift.symm
        (homComplexCocycleMap (homComplexChangeOfRingsAbMap.{uR, uA, uM} f K J I q) n z) =
      (mapCochainAdjunction (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f)).homEquiv
        K (J⟦n⟧) (Cocycle.equivHomShift.symm z) ≫
      ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapCochainComplexShiftIso n).hom.app J ≫
        q⟦n⟧' := by
  ext p : 1
  simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    Cocycle.rightShift_coe, HomologicalComplex.comp_f]
  rw [Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p + n) rfl]
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso_refl,
    Iso.refl_inv, Category.comp_id]
  show (((homComplexChangeOfRingsMap.{uR, uA, uM} f K J I q).f n)
    (z : Cochain _ _ n)).v p (p + n) rfl = _
  rw [homComplexChangeOfRingsMap_f_apply]
  simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
    Functor.mapCochainComplexShiftIso_hom_app_f]
  rfl

/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance :
    (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint

/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance :
    (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
/-- The source comparison is a quasi-isomorphism: in every degree, its map on cohomology
is the derived extension--restriction adjunction. -/
private theorem quasiIso_homComplexChangeOfRingsMap
    [J.IsKInjective] [I.IsKInjective] [QuasiIso q]
    (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (α : DerivedCategory.Q ⋙ F ⟶
      CochainComplex.extendScalarsLarge.{uM, uR, uA} f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (.up ℤ))]
    (a : F ⊣ (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory)
    (ha : ∀ X, a.unit.app (DerivedCategory.Q.obj X) ≫
      (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map (α.app X) =
      DerivedCategory.Q.map
        ((mapCochainAdjunction
          (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f)).unit.app X) ≫
        (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors.inv.app
          ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj X))
    (hK : K.KFlat) :
    QuasiIso (homComplexChangeOfRingsMap.{uR, uA, uM} f K J I q) := by
  have : IsIso (α.app K) := isIso_extendScalarsCounit_app_of_kFlat f F α K hK
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{max uR uA uM} R) Ab)).1
  show QuasiIso (homComplexChangeOfRingsAbMap.{uR, uA, uM} f K J I q)
  rw [quasiIso_homComplex_iff]
  intro n
  let β := (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors
  let qn : (CochainComplex.restrictScalarsLarge.{uM, uR, uA} f).obj (J⟦n⟧) ⟶ I⟦n⟧ :=
    ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapCochainComplexShiftIso n).hom.app J ≫
      q⟦n⟧'
  have : QuasiIso qn := by dsimp only [qn]; infer_instance
  let e₁ := homComplexCohomologyDerivedEquiv
    ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) J n
  let e₂ := homComplexCohomologyDerivedEquiv K I n
  let dmap := fun g : DerivedCategory.Q.obj
      ((CochainComplex.extendScalarsLarge.{uM, uR, uA} f).obj K) ⟶ DerivedCategory.Q.obj (J⟦n⟧) =>
    a.homEquiv _ _ (α.app K ≫ g) ≫ β.hom.app (J⟦n⟧) ≫ DerivedCategory.Q.map qn
  have hb : Function.Bijective dmap :=
    derivedAdjunction_bijective_on_representatives
      (mapCochainAdjunction (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f))
      α β a K (J⟦n⟧) (I⟦n⟧) qn
  have hc : e₂ ∘ homComplexCohomologyMap
      (homComplexChangeOfRingsAbMap.{uR, uA, uM} f K J I q) n = dmap ∘ e₁ := by
    funext z
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective z
    show homComplexCohomologyDerivedEquiv K I n
        (CohomologyClass.mk (homComplexCocycleMap
          (homComplexChangeOfRingsAbMap.{uR, uA, uM} f K J I q) n z)) = _
    rw [homComplexCohomologyDerivedEquiv_mk,
      homComplexChangeOfRingsAbMap_homShift]
    show DerivedCategory.Q.map
      ((mapCochainAdjunction
        (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f)).homEquiv _ _
          (Cocycle.equivHomShift.symm z) ≫ qn) = _
    rw [Functor.map_comp]
    dsimp only [Function.comp_apply, dmap, e₁]
    rw [homComplexCohomologyDerivedEquiv_mk, ← Category.assoc,
      derivedAdjunction_homEquiv_map _ α β a ha (Cocycle.equivHomShift.symm z)]
    rfl
  apply (e₂.bijective.of_comp_iff' _).1
  rw [hc]
  exact hb.comp e₁.bijective

set_option backward.isDefEq.respectTransparency false in
/-- K-flat and K-injective representatives make the canonical change-of-rings map a
quasi-isomorphism, independently of the chosen total derived extension functor. -/
public theorem quasiIso_homComplexChangeOfRingsMap_of_kFlat
    [J.IsKInjective] [I.IsKInjective] [QuasiIso q]
    (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (α : DerivedCategory.Q ⋙ F ⟶
      CochainComplex.extendScalarsLarge.{uM, uR, uA} f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (.up ℤ))]
    (hK : K.KFlat) :
    QuasiIso (homComplexChangeOfRingsMap.{uR, uA, uM} f K J I q) := by
  let : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
    f F α
  let := a.isLeftAdjoint
  let := a.isRightAdjoint
  let b := derivedAdjunctionWithUnitComparison
    (mapCochainAdjunction (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f))
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (.up ℤ))
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} A) (.up ℤ))
    α (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategoryFactors
  exact quasiIso_homComplexChangeOfRingsMap f K J I q F α b.1 b.2 hK

end ChangeOfRingsCohomology

end Stacks.DerivedHom.BaseChange

end DerivedHomChangeOfRings
