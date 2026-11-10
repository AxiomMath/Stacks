module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ResolvedProjectionFormula
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareLift
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeMorEqLax
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.TensorSquareComplex
public import StacksFrontier.Homology.Tor.BaseChangeTensorScalarLift
import all StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionComponent
import all StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.Tensor
import StacksFrontier.Homology.HomComplex.RHom.BaseChange
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelRestrictScalars
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.Invertibility

/-!
# The resolved projection formula is the projection formula

Let `f : R → A` be a ring map, `F` a model of derived extension of scalars along `f`, and
`p : P ⟶ A[0]` a K-flat resolution of the algebra.  The projection formula
`F ⋙ U ≅ (- ⊗ᴸ_R A)` exists in two forms: `Dualizing.derivedExtendRestrictScalarsTensorIso`,
built by transport through the universe lifts of the two rings, and
`Dualizing.resolvedProjectionFormula`, built from chain-level isomorphisms at K-flat complexes.
This file proves that they are equal.

## Main definitions

* `Dualizing.TransportChainIdentity`: the identity of the two chain isomorphisms
  `(A ⊗_R K)|_R ≅ Tot(A[0] ⊗ K)` over the lifted base ring, for every complex `K`.

## Main results

* `Dualizing.derivedExtendRestrictScalarsTensorIso_eq_resolvedProjectionFormula`: the two
  projection formulas are equal.
* `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_eq`: they agree at the class of
  every K-flat complex.
* `Dualizing.transportChainIdentity`: `Dualizing.TransportChainIdentity` holds.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor MonoidalCategory
open scoped ChangeOfRings TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe v uR uA

namespace StacksDraft.DerivedHom.DerivedHomData

universe u w

variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)] (d : DerivedHomData S)

/-- **The inverse symmetry against a resolution of the second variable.**  For K-flat `K` and `P`
and a chain map `q : P ⟶ B`, tensoring `q` into the second variable, the inverse symmetry and the
K-flat comparison at `(B, K)` is the K-flat comparison at `(K, P)` followed by the inverse signed
interchange and `q` tensored into the first variable. -/
theorem tensor_map_comp_tensorSwap_inv_comp_tensorIso_hom
    (K P B : CochainComplex (ModuleCat.{u} S) ℤ) (hK : K.KFlat) (hP : P.KFlat) (q : P ⟶ B) :
    d.tensor.map ((𝟙 (DerivedCategory.Q.obj K), DerivedCategory.Q.map q) :
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj B)) ≫
      (d.tensorSwap (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj K)).inv ≫
        (d.tensorIso B K hK).hom =
      (d.tensorIso K P hP).hom ≫
        DerivedCategory.Q.map ((Model.complexSwap S P K).inv ≫ (q ▷ K)) := by
  have h1 := d.tensorSwap_naturality (DerivedCategory.Q.map q) (𝟙 (DerivedCategory.Q.obj K))
  have h2 := d.tensorIso_naturality q (𝟙 K) hK hK
  have h3 : (d.tensorSwap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)).hom ≫
      (d.tensorIso K P hP).hom =
      (d.tensorIso P K hK).hom ≫ DerivedCategory.Q.map (Model.complexSwap S P K).hom :=
    d.tensorSwap_comparison P K hP hK
  rw [DerivedCategory.Q.map_id] at h2
  have h1' : d.tensor.map ((𝟙 (DerivedCategory.Q.obj K), DerivedCategory.Q.map q) :
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj B)) ≫
      (d.tensorSwap (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj K)).inv =
      (d.tensorSwap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)).inv ≫
        d.tensor.map ((DerivedCategory.Q.map q, 𝟙 (DerivedCategory.Q.obj K)) :
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj K) ⟶
            (DerivedCategory.Q.obj B, DerivedCategory.Q.obj K)) := by
    exact (CommSq.vert_inv (g := d.tensorSwap _ _) (h := d.tensorSwap _ _) ⟨h1⟩).w
  have h3' : (d.tensorSwap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)).inv ≫
      (d.tensorIso P K hK).hom =
      (d.tensorIso K P hP).hom ≫ DerivedCategory.Q.map (Model.complexSwap S P K).inv := by
    exact (CommSq.horiz_inv (f := d.tensorSwap _ _) (i := DerivedCategory.Q.mapIso
      (Model.complexSwap S P K)) ⟨h3⟩).w
  rw [reassoc_of% h1', h2, reassoc_of% h3', DerivedCategory.Q.map_comp]
  rfl

end StacksDraft.DerivedHom.DerivedHomData

namespace Stacks.DerivedHom.BaseChange

universe u w

/-- The unit of an equivalence followed by a presentation of the image, natural in the source. -/
theorem unit_comp_inverse_map_naturality {C D : Type*} [Category* C] [Category* D] (E : C ≌ D)
    {X Y : C} (a : X ⟶ Y) {X' Y' : D} (ψX : E.functor.obj X ⟶ X') (ψY : E.functor.obj Y ⟶ Y')
    (b : X' ⟶ Y') (h : E.functor.map a ≫ ψY = ψX ≫ b) :
    a ≫ E.unitIso.hom.app Y ≫ E.inverse.map ψY =
      (E.unitIso.hom.app X ≫ E.inverse.map ψX) ≫ E.inverse.map b := by
  have h1 : a ≫ E.unitIso.hom.app Y = E.unitIso.hom.app X ≫ E.inverse.map (E.functor.map a) :=
    E.unitIso.hom.naturality a
  rw [reassoc_of% h1, ← E.inverse.map_comp, h, E.inverse.map_comp, Category.assoc]

/-- **The scalar-lift unit at the class of a complex.**  The unit of the scalar-lift equivalence
at the class of `X`, followed by the inverse of the lift applied to the scalar-lift presentation of
that class. -/
def scalarLiftUnit (B : Type u) [CommRing B] (X : CochainComplex (ModuleCat.{max u w} B) ℤ) :
    DerivedCategory.Q.obj X ⟶
      (ScalarTransportedInternalHom.scalarEquivalence.{u, w} B).inverse.obj
        (DerivedCategory.Q.obj (((ModuleCat.restrictScalars.{max u w}
          (ULift.ringEquiv : ULift.{w} B ≃+* B).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X)) :=
  (ScalarTransportedInternalHom.scalarEquivalence.{u, w} B).unitIso.hom.app
      (DerivedCategory.Q.obj X) ≫
    (ScalarTransportedInternalHom.scalarEquivalence.{u, w} B).inverse.map
      (scalarLiftQObjIso.{u, w} B X).hom

/-- `Stacks.DerivedHom.BaseChange.scalarLiftUnit` is natural in the complex. -/
theorem scalarLiftUnit_naturality (B : Type u) [CommRing B]
    {X Y : CochainComplex (ModuleCat.{max u w} B) ℤ} (g : X ⟶ Y) :
    DerivedCategory.Q.map g ≫ scalarLiftUnit.{u, w} B Y =
      scalarLiftUnit.{u, w} B X ≫
        (ScalarTransportedInternalHom.scalarEquivalence.{u, w} B).inverse.map
          (DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max u w}
            (ULift.ringEquiv : ULift.{w} B ≃+* B).toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).map g)) :=
  unit_comp_inverse_map_naturality
    (ScalarTransportedInternalHom.scalarEquivalence.{u, w} B) (DerivedCategory.Q.map g) _ _ _
    ((ModuleCat.restrictScalars.{max u w}
      (ULift.ringEquiv : ULift.{w} B ≃+* B).toRingHom).mapDerivedCategoryFactors.hom.naturality g)

end Stacks.DerivedHom.BaseChange

namespace Dualizing

attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- The universe lift of the algebra, as a module over the lifted base ring: restriction of
scalars along `ULift.ringEquiv` of `Dualizing.algebraModule` is the lifted algebra restricted
along the lifted ring map. -/
def algebraLiftIso :
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    (ModuleCat.restrictScalars.{max v uR uA}
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).obj (algebraModule.{v} f) ≅
      (ModuleCat.restrictScalars f').obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)) :=
  (show (((ModuleCat.restrictScalars.{max v uR uA}
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).obj (algebraModule.{v} f) :
          ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) : Type _) ≃ₗ[ULift.{max v uR uA} R]
      (((ModuleCat.restrictScalars ((ULift.ringEquiv.symm.toRingHom.comp f).comp
          ULift.ringEquiv.toRingHom : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A)).obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)) :
          ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) : Type _) from
    { toFun x := ULift.up x.down
      invFun x := ULift.up x.down
      left_inv x := by cases x; rfl
      right_inv x := by cases x; rfl
      map_add' x y := rfl
      map_smul' r x := rfl }).toModuleIso

/-- The universe lift of the algebra complex, as a complex over the lifted base ring: the
lifted algebra placed in degree zero. -/
def algebraLiftChain :
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    ((ModuleCat.restrictScalars.{max v uR uA}
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (algebraComplex.{v} f) ⟶
      (CochainComplex.singleFunctor (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
        ((ModuleCat.restrictScalars f').obj
          (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A))) :=
  ((ModuleCat.restrictScalars.{max v uR uA}
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapCochainComplexSingleFunctor
          0).hom.app (algebraModule.{v} f) ≫
    (CochainComplex.singleFunctor (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).map
      (algebraLiftIso.{v} f).hom

/-- **The lift of the algebra, computed.**  `Dualizing.derivedAlgebraSingleLiftIso` is the
scalar-lift factorization at the algebra complex followed by the class of
`Dualizing.algebraLiftChain`. -/
theorem derivedAlgebraSingleLiftIso_hom_eq :
    (derivedAlgebraSingleLiftIso.{uR, uA, max v uA} f).hom =
      ((ModuleCat.restrictScalars.{max v uR uA}
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapDerivedCategoryFactors.app
          (algebraComplex.{v} f)).hom ≫
        DerivedCategory.Q.map (algebraLiftChain.{v} f) := by
  let e := ModuleCat.restrictScalars.{max v uR uA}
    (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom
  have h := (Iso.inv_comp_eq (e.mapDerivedCategoryFactors.app
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (algebraModule.{v} f)))).1
    (e.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app
      (algebraModule.{v} f))
  refine (congrArg (· ≫ (DerivedCategory.singleFunctor _ 0).map (algebraLiftIso.{v} f).hom)
    h).trans ?_
  simp only [Category.assoc, algebraLiftChain, Functor.map_comp]
  rfl

section Clean

variable (F : DerivedCategory (ModuleCat.{max v uR uA} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA} R) (ComplexShape.up ℤ))]
  (P : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (hP : CochainComplex.KFlat.{uR, max v uR uA} P)
  (p : P ⟶ algebraComplex.{v} f) [QuasiIso p]

/-- For a bifunctor `G`, a pair map in the second variable, an inverse symmetry and a map in the
transported first variable regroup as a pair map followed by the symmetry against the second
variable. -/
theorem bifunctor_swap_regroup {𝒟 : Type*} [Category* 𝒟] (G : 𝒟 × 𝒟 ⥤ 𝒟)
    {X Y Y' B X' Y'' Z : 𝒟} (u : X ⟶ X) (hu : u = 𝟙 X) (a : Y ⟶ Y') (ih : Y' ⟶ B)
    (sw1 : G.obj (B, X) ≅ G.obj (X, B)) (ψK : X ⟶ X') (sw2 : G.obj (B, X') ≅ G.obj (X', B))
    (t : G.obj (B, X') ⟶ Z) (ψP : Y ⟶ Y'') (q : Y'' ⟶ B) (hq : a ≫ ih = ψP ≫ q)
    (hsw : G.map ((𝟙 B, ψK) : (B, X) ⟶ (B, X')) ≫ sw2.hom =
      sw1.hom ≫ G.map ((ψK, 𝟙 B) : (X, B) ⟶ (X', B)))
    (rest : G.obj (X', Y'') ⟶ Z)
    (hC : G.map ((𝟙 X', q) : (X', Y'') ⟶ (X', B)) ≫ sw2.inv ≫ t = rest) :
    G.map ((u, a) : (X, Y) ⟶ (X, Y')) ≫ G.map ((𝟙 X, ih) : (X, Y') ⟶ (X, B)) ≫ sw1.inv ≫
        G.map ((𝟙 B, ψK) : (B, X) ⟶ (B, X')) ≫ t =
      G.map ((ψK, ψP) : (X, Y) ⟶ (X', Y'')) ≫ rest := by
  subst hu
  have hsw' : sw1.inv ≫ G.map ((𝟙 B, ψK) : (B, X) ⟶ (B, X')) =
      G.map ((ψK, 𝟙 B) : (X, B) ⟶ (X', B)) ≫ sw2.inv := by
    exact (CommSq.vert_inv (g := sw1) (h := sw2) ⟨hsw⟩).w.symm
  have hpair : G.map ((𝟙 X, a) : (X, Y) ⟶ (X, Y')) ≫ G.map ((𝟙 X, ih) : (X, Y') ⟶ (X, B)) ≫
      G.map ((ψK, 𝟙 B) : (X, B) ⟶ (X', B)) =
      G.map ((ψK, ψP) : (X, Y) ⟶ (X', Y'')) ≫ G.map ((𝟙 X', q) : (X', Y'') ⟶ (X', B)) := by
    rw [← G.map_comp, ← G.map_comp, ← G.map_comp]
    congr 1
    ext
    · simp
    · simp [hq]
  rw [reassoc_of% hsw', ← hC, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  rw [Category.assoc (G.map _) (G.map _), hpair, Category.assoc, Category.assoc]

/-- A composite of images under a functor, with identities removed, is the image of the
composite. -/
theorem map_comp_id_comp_map_clean {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Ei : 𝒟 ⥤ 𝒞)
    {X₀ X Y V U T : 𝒟} (a₀ : X₀ ⟶ X) (a : X ⟶ Y) (b : Y ⟶ V) (c : V ⟶ U) (d : U ⟶ T) :
    Ei.map a₀ ≫ 𝟙 (Ei.obj X) ≫ Ei.map ((a ≫ 𝟙 Y) ≫ b) ≫ Ei.map c ≫ Ei.map d =
      Ei.map (a₀ ≫ a ≫ b ≫ c ≫ d) := by
  simp

/-- Solving a presented composite for the inverse of the presentation. -/
theorem inv_comp_eq_of_presentation {𝒦 𝒟 𝒞 : Type*} [Category* 𝒦] [Category* 𝒟] [Category* 𝒞]
    (Qf : 𝒦 ⥤ 𝒟) (Ei : 𝒟 ⥤ 𝒞) {M M' : 𝒟} {B : 𝒞} {Y Y' Z : 𝒦}
    (d : Ei.obj M ≅ B) (u : B ⟶ Ei.obj (Qf.obj Y')) (m₁ : M ⟶ M') (m₂ : M' ⟶ Qf.obj Y)
    (r : Y ≅ Y') (x : Y ⟶ Z) (T : Ei.obj M ⟶ Ei.obj (Qf.obj Z))
    (h₁ : Ei.map (m₁ ≫ m₂ ≫ Qf.map r.hom) = d.hom ≫ u)
    (h₂ : T = Ei.map (m₁ ≫ m₂ ≫ Qf.map x)) :
    d.inv ≫ T = u ≫ Ei.map (Qf.map (r.inv ≫ x)) := by
  rw [h₂, Iso.inv_comp_eq, ← reassoc_of% h₁, ← Ei.map_comp]
  congr 1
  simp only [Category.assoc, ← Qf.map_comp, Iso.hom_inv_id_assoc]

/-- Conjugating a commutative square of isomorphisms. -/
theorem comp_inv_eq_inv_comp_of_square {𝒞 : Type*} [Category* 𝒞] {X Y X' Y' : 𝒞}
    (a : X ⟶ X') (b : Y ⟶ Y') (r : X ≅ Y) (r' : X' ≅ Y') (h : a ≫ r'.hom = r.hom ≫ b) :
    b ≫ r'.inv = r.inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- Three squares pasted. -/
theorem comp_three_squares {𝒞 : Type*} [Category* 𝒞] {X₀ X₁ X₂ Y₁ Y₂ Z W : 𝒞}
    (x : X₀ ⟶ X₁) (a : X₁ ⟶ X₂) (b : X₀ ⟶ Y₁) (c : Y₁ ⟶ X₂) (d : X₂ ⟶ Z) (e : Y₁ ⟶ Y₂)
    (g : Y₂ ⟶ Z) (k : Z ⟶ W) (m : Y₂ ⟶ W)
    (h₁ : x ≫ a = b ≫ c) (h₂ : c ≫ d = e ≫ g) (h₃ : g ≫ k = m) :
    x ≫ a ≫ d ≫ k = b ≫ e ≫ m := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- An inverse against a natural presentation. -/
theorem inv_comp_eq_of_natural {𝒞 : Type*} [Category* 𝒞] {A B C C' D : 𝒞} (k : A ≅ B)
    (s : A ⟶ B) (hk : k.hom = s) (uX : A ⟶ C) (uY : B ⟶ C') (t : C ⟶ C')
    (ht : s ≫ uY = uX ≫ t) (eX : C ⟶ D) (eY : C' ⟶ D) (he : t ≫ eY = eX) :
    k.inv ≫ uX ≫ eX = uY ≫ eY := by
  rw [Iso.inv_comp_eq, ← he, ← reassoc_of% ht, hk]

/-- **A transport prefix, solved.** Given an equivalence `S`, an isomorphism
`δ : S.inverse ⋙ U ≅ V ⋙ Ei` and a presentation `hE` of `S.functor.map c`, the composite of the
unit of `S`, `ei`, `δ` and the images of `bψ` and `al` is `U.map c` followed by the unit, `δ` and
the image of `sl.hom ≫ ql.inv`. -/
theorem transport_prefix_generic {C D C' D' : Type*} [Category* C] [Category* D] [Category* C']
    [Category* D'] (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C') (Ei : C' ⥤ C)
    (δ : S.inverse ⋙ U ≅ V ⋙ Ei) {Y₀ Y₁ : D} {B₀ B₁ W Z : D'} (c : Y₀ ⟶ Y₁)
    (eh : B₀ ⟶ S.functor.obj Y₀) (ei : S.functor.obj Y₀ ⟶ B₀) (hei : ei ≫ eh = 𝟙 _)
    (bψ : B₀ ⟶ B₁) (al : B₁ ⟶ W) (ql : W ≅ Z)
    (sl : S.functor.obj Y₁ ≅ Z)
    (hE : eh ≫ S.functor.map c = (bψ ≫ al ≫ ql.hom) ≫ sl.inv) :
    𝟙 (U.obj Y₀) ≫ U.map (S.unitIso.hom.app Y₀) ≫ U.map (S.inverse.map ei) ≫
        δ.hom.app B₀ ≫ Ei.map (V.map bψ) ≫ Ei.map (V.map al) =
      U.map c ≫ U.map (S.unitIso.hom.app Y₁) ≫ δ.hom.app (S.functor.obj Y₁) ≫
        Ei.map (V.map (sl.hom ≫ ql.inv)) := by
  have h0 : S.functor.map c = ei ≫ (bψ ≫ al ≫ ql.hom) ≫ sl.inv := by
    rw [← hE, ← Category.assoc, hei, Category.id_comp]
  have h1 : ei ≫ bψ ≫ al = S.functor.map c ≫ sl.hom ≫ ql.inv := by
    rw [h0]
    simp
  have n1 := δ.hom.naturality ei
  have n2 := δ.hom.naturality (S.functor.map c)
  have n3 := S.unitIso.hom.naturality c
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at n1 n2 n3
  rw [Category.id_comp, reassoc_of% n1, ← Ei.map_comp, ← Ei.map_comp, ← V.map_comp,
    ← V.map_comp, h1, V.map_comp, Ei.map_comp, reassoc_of% n2.symm, ← U.map_comp_assoc,
    ← U.map_comp_assoc, n3]

/-- Six commutative squares pasted. -/
theorem paste_prefix_tail {𝒞 : Type*} [Category* 𝒞]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ Q₁ Q₂ Q₃ Q₄ Q₅ Q₆ Q₇ Q₈ : 𝒞}
    (u : P₀ ⟶ P₁) (δh : P₁ ⟶ P₂) (e₁ : P₂ ⟶ P₃) (e₂ : P₃ ⟶ P₄) (e₃ : P₄ ⟶ P₅) (k : P₅ ⟶ P₆)
    (uψ : P₁ ⟶ Q₁) (δh' : Q₁ ⟶ P₃) (q₁ : P₀ ⟶ Q₂) (sif : Q₂ ⟶ Q₁) (ufh : Q₂ ⟶ Q₃)
    (eu : Q₃ ⟶ Q₄) (eψ : Q₄ ⟶ Q₅) (esr : Q₅ ⟶ Q₆) (efi : Q₆ ⟶ P₃) (ufY : P₀ ⟶ Q₇)
    (qr : Q₇ ⟶ Q₃) (N : Q₇ ⟶ Q₈) (el : Q₈ ⟶ Q₅) (er : Q₆ ⟶ P₅)
    (F₁ : δh ≫ e₁ = uψ ≫ δh') (F₂ : u ≫ uψ = q₁ ≫ sif)
    (F₃ : sif ≫ δh' = ufh ≫ eu ≫ eψ ≫ esr ≫ efi) (F₄ : q₁ ≫ ufh = ufY ≫ qr)
    (F₅ : qr ≫ eu ≫ eψ = N ≫ el) (F₆ : efi ≫ e₂ ≫ e₃ = er)
    (e₁₂ : P₂ ⟶ P₄) (he : e₁₂ = e₁ ≫ e₂) (ch : Q₈ ⟶ P₆) (hch : ch = el ≫ esr ≫ er ≫ k) :
    u ≫ δh ≫ e₁₂ ≫ e₃ ≫ k = ufY ≫ N ≫ ch := by
  rw [he, hch, Category.assoc, reassoc_of% F₁, reassoc_of% F₂, reassoc_of% F₃, reassoc_of% F₄,
    reassoc_of% F₅, reassoc_of% F₆]

/-- A presentation of a composite with an isomorphism, pushed forward and solved. -/
theorem map_comp_eq_of_comp_hom {𝒜 𝒞 : Type*} [Category* 𝒜] [Category* 𝒞] (U : 𝒜 ⥤ 𝒞)
    {X Y Z W : 𝒜} (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ≅ W) (d : X ⟶ W) (h : a ≫ b ≫ c.hom = d) :
    U.map a ≫ U.map b = U.map d ≫ U.map c.inv := by
  rw [← h, ← U.map_comp, ← U.map_comp]
  simp

/-- An iso-equation solved for the forward component of `δ`. -/
theorem solve_delta {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Ei : 𝒟 ⥤ 𝒞)
    {X₀ X₁ Y : 𝒞} {M₀ M₁ M₂ M₃ : 𝒟} (x : X₁ ⟶ Ei.obj M₀) (a : M₀ ⟶ M₁) (b : M₁ ⟶ M₂)
    (c : M₂ ⟶ M₃) (δ : Y ≅ Ei.obj M₃) (d : X₀ ≅ X₁) (si : X₀ ⟶ Y)
    (h : x ≫ Ei.map (a ≫ b ≫ c) ≫ δ.inv = d.inv ≫ si) :
    si ≫ δ.hom = d.hom ≫ x ≫ Ei.map a ≫ Ei.map b ≫ Ei.map c := by
  have h' : si = d.hom ≫ x ≫ Ei.map (a ≫ b ≫ c) ≫ δ.inv := by
    rw [h, Iso.hom_inv_id_assoc]
  rw [h']
  simp

/-- A naturality square of an isomorphism, pushed forward and solved. -/
theorem map_natural_solve {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Ei : 𝒟 ⥤ 𝒞)
    {A B A' B' : 𝒟} (vl : A ⟶ A') (fh : A ≅ B) (fh' : A' ≅ B') (ql : B ⟶ B')
    (h : vl ≫ fh'.hom = fh.hom ≫ ql) :
    Ei.map fh.inv ≫ Ei.map vl ≫ Ei.map fh'.hom = Ei.map ql := by
  rw [← Ei.map_comp, ← Ei.map_comp, h, Iso.inv_hom_id_assoc]

/-- Four chain maps localized and pushed forward. -/
theorem map_map_comp_four {𝒦 𝒟 𝒞 : Type*} [Category* 𝒦] [Category* 𝒟] [Category* 𝒞]
    (Qf : 𝒦 ⥤ 𝒟) (Ei : 𝒟 ⥤ 𝒞) {X₀ X₁ X₂ X₃ X₄ : 𝒦} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) :
    Ei.map (Qf.map (a ≫ b ≫ c ≫ d)) =
      Ei.map (Qf.map a) ≫ Ei.map (Qf.map b) ≫ Ei.map (Qf.map c) ≫ Ei.map (Qf.map d) := by
  simp

/-- Two morphisms `lib` and `R` agree once their composites with the isomorphism `LT` are related
by the given chain of commutative squares. -/
theorem final_assembly {𝒞 : Type*} [Category* 𝒞]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ Z₁ : 𝒞}
    (lib R : X₀ ⟶ X₁) (LT : X₁ ⟶ X₂) [IsIso LT] (pre : X₀ ⟶ X₃) (x : X₃ ⟶ X₄) (y : X₄ ⟶ X₂)
    (c : X₀ ⟶ X₅) (a : X₅ ⟶ X₆) (b : X₆ ⟶ X₇) (e : X₇ ⟶ X₃) (ufac : X₅ ⟶ Y₁) (slY : Y₁ ⟶ Y₂)
    (tq : Y₂ ⟶ X₂) (el : Y₂ ⟶ Z₁) (ed : Z₁ ⟶ X₂) (qe : Y₁ ⟶ Y₃) (ki : Y₃ ⟶ Y₄) (di : Y₄ ⟶ Y₅)
    (t : Y₅ ⟶ X₁) (slP : Y₄ ⟶ Y₆) (eP : Y₆ ⟶ X₂) (slA : Y₃ ⟶ Z₁)
    (hpair : lib ≫ LT = pre ≫ x ≫ y) (hL1 : pre = c ≫ a ≫ b ≫ e)
    (htv : a ≫ b ≫ e ≫ x ≫ y = ufac ≫ slY ≫ tq) (hL4 : tq = el ≫ ed)
    (hR : R = c ≫ ufac ≫ qe ≫ ki ≫ di ≫ t) (hL3 : di ≫ t ≫ LT = slP ≫ eP)
    (hL5 : ki ≫ slP ≫ eP = slA ≫ ed) (hnat : qe ≫ slA = slY ≫ el) :
    lib = R := by
  refine (cancel_mono LT).1 ?_
  rw [hpair, hL1, hR]
  simp only [Category.assoc]
  rw [htv, hL4, hL3, hL5, reassoc_of% hnat]

/-- Four summand inclusions pushed through four maps. -/
theorem chain_tail {𝒞 : Type*} [Category* 𝒞] {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : 𝒞}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (m : X₀ ⟶ Y₁) (ι₁ : Y₁ ⟶ X₁)
    (ri : Y₁ ⟶ Y₂) (ι₂ : Y₂ ⟶ X₂) (β : Y₂ ⟶ Y₃) (ι₃ : Y₃ ⟶ X₃) (w : Y₃ ⟶ Y₄) (ι₄ : Y₄ ⟶ X₄)
    (ha : a = m ≫ ι₁) (hb : ι₁ ≫ b = ri ≫ ι₂) (hc : ι₂ ≫ c = β ≫ ι₃) (hd : ι₃ ≫ d = w ≫ ι₄) :
    a ≫ b ≫ c ≫ d = m ≫ ri ≫ β ≫ w ≫ ι₄ := by
  rw [ha, Category.assoc, reassoc_of% hb, reassoc_of% hc, hd]

/-- A summand formula for an isomorphism, inverted. -/
theorem summand_inv {𝒞 : Type*} [Category* 𝒞] {Y₁ Y₂ X₁ X₂ : 𝒞} (ι₁ : Y₁ ⟶ X₁) (ι₂ : Y₂ ⟶ X₂)
    (rh : X₂ ⟶ X₁) (ri : X₁ ⟶ X₂) (hr : rh ≫ ri = 𝟙 X₂) (M : Y₂ ≅ Y₁)
    (h : ι₂ ≫ rh = M.hom ≫ ι₁) : ι₁ ≫ ri = M.inv ≫ ι₂ := by
  rw [Iso.eq_inv_comp, ← reassoc_of% h, hr, Category.comp_id]

/-- The degreewise components of a fourfold composite, for any instance of zero morphisms. -/
theorem comp4_f_of_zero {𝒞 : Type*} [Category* 𝒞] {_ : Limits.HasZeroMorphisms 𝒞}
    {X₀ X₁ X₂ X₃ X₄ : CochainComplex 𝒞 ℤ} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (i : ℤ) :
    (a ≫ b ≫ c ≫ d).f i = a.f i ≫ b.f i ≫ c.f i ≫ d.f i :=
  rfl

/-- Replacing the last factor of a fourfold composite. -/
theorem comp_last_congr {𝒞 : Type*} [Category* 𝒞] {X₀ X₁ X₂ X₃ X₄ : 𝒞} (a : X₀ ⟶ X₁)
    (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d d' : X₃ ⟶ X₄) (h : d = d') :
    a ≫ b ≫ c ≫ d = a ≫ b ≫ c ≫ d' := by
  rw [h]

/-- Two fourfold composites followed by one inclusion. -/
theorem comp_four_incl {𝒞 : Type*} [Category* 𝒞] {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ X₅ : 𝒞}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (a' : X₀ ⟶ Y₁) (b' : Y₁ ⟶ Y₂)
    (c' : Y₂ ⟶ Y₃) (d' : Y₃ ⟶ X₄) (ι : X₄ ⟶ X₅)
    (h : a ≫ b ≫ c ≫ d = a' ≫ b' ≫ c' ≫ d') :
    a ≫ b ≫ c ≫ d ≫ ι = a' ≫ b' ≫ c' ≫ d' ≫ ι := by
  simp only [← Category.assoc] at h ⊢
  rw [h]

/-- A composite of four morphisms of modules on an element, computed one step at a time. -/
theorem ModuleCat_hom_comp₄_eq {T : Type*} [Ring T] {X₀ X₁ X₂ X₃ X₄ : ModuleCat T}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄}
    {y : X₀} {w₂ : X₂} {w₃ : X₃} {w₄ : X₄}
    (h₂ : f₁.hom (f₀.hom y) = w₂) (h₃ : f₂.hom w₂ = w₃) (h₄ : f₃.hom w₃ = w₄) :
    (f₀ ≫ f₁ ≫ f₂ ≫ f₃).hom y = w₄ := by
  subst h₂ h₃ h₄
  rfl

/-- **The resolved tensor with the algebra, read through the scalar lift.**  Tensoring the
inverse resolution of the algebra into the second variable of the derived tensor product of
[stacks 0A63], followed by the transport tail of the independent-universe projection formula, is
the scalar lift of the K-flat comparison of the lifted model at the lifts of `K` and `P`, followed
by the inverse signed interchange and the lifted resolution tensored into the first variable. -/
theorem tensor_map_algebraResolutionIso_inv_comp_liftTransportTail
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    let G := DerivedInternalHom.Model.adjunction (ULift.{max v uR uA} R)
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
        ((𝟙 (DerivedCategory.Q.obj K), (algebraResolutionIso.{v} f P p).inv) :
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
            (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, v} f)) ≫
      liftTransportTail.{v, uR, uA} f K hK =
    E.inverse.map (G.tensor.map
        (((Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max v uR uA} R K).hom,
          (Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max v uR uA} R P).hom) :
          (E.functor.obj (DerivedCategory.Q.obj K), E.functor.obj (DerivedCategory.Q.obj P)) ⟶
            (DerivedCategory.Q.obj (lift.obj K), DerivedCategory.Q.obj (lift.obj P))) ≫
      (G.tensorIso (lift.obj K) (lift.obj P)
        (kFlat_restrictScalars_uliftRingEquiv.{uR, max v uR uA} P hP)).hom ≫
      DerivedCategory.Q.map ((Model.complexSwap (ULift.{max v uR uA} R) (lift.obj P)
          (lift.obj K)).inv ≫ ((lift.map p ≫ algebraLiftChain.{v} f) ▷ lift.obj K))) := by
  intro E G lift
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let Bc := (CochainComplex.singleFunctor
    (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
    ((ModuleCat.restrictScalars f').obj
      (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
  have ha : (algebraResolutionIso.{v} f P p).inv = DerivedCategory.Q.map p := by
    simp only [algebraResolutionIso]
    exact Category.comp_id _
  have hq : E.functor.map (algebraResolutionIso.{v} f P p).inv ≫
      (derivedAlgebraSingleLiftIso.{uR, uA, max v uA} f).hom =
      (Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max v uR uA} R P).hom ≫
        DerivedCategory.Q.map (lift.map p ≫ algebraLiftChain.{v} f) := by
    rw [ha, derivedAlgebraSingleLiftIso_hom_eq, DerivedCategory.Q.map_comp]
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ DerivedCategory.Q.map
      (algebraLiftChain.{v} f)) ?_).trans (Category.assoc _ _ _))
    exact NatTrans.naturality (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapDerivedCategoryFactors.hom p
  have hsw := G.tensorSwap_naturality (𝟙 (DerivedCategory.Q.obj Bc))
    (Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max v uR uA} R K).hom
  have hC := DerivedHomData.tensor_map_comp_tensorSwap_inv_comp_tensorIso_hom G (lift.obj K)
    (lift.obj P) Bc (kFlat_restrictScalars_uliftRingEquiv.{uR, max v uA} K hK)
    (kFlat_restrictScalars_uliftRingEquiv.{uR, max v uR uA} P hP)
    (lift.map p ≫ algebraLiftChain.{v} f)
  refine (?_ : _ = E.inverse.map
      (G.tensor.map ((E.functor.map (𝟙 (DerivedCategory.Q.obj K)),
          E.functor.map (algebraResolutionIso.{v} f P p).inv) :
          (E.functor.obj (DerivedCategory.Q.obj K), E.functor.obj (DerivedCategory.Q.obj P)) ⟶
            (E.functor.obj (DerivedCategory.Q.obj K),
              E.functor.obj (derivedAlgebraSingle.{uR, uA, v} f))) ≫
        G.tensor.map ((𝟙 (E.functor.obj (DerivedCategory.Q.obj K)),
          (derivedAlgebraSingleLiftIso.{uR, uA, max v uA} f).hom) :
          (E.functor.obj (DerivedCategory.Q.obj K),
              E.functor.obj (derivedAlgebraSingle.{uR, uA, v} f)) ⟶
            (E.functor.obj (DerivedCategory.Q.obj K), DerivedCategory.Q.obj Bc)) ≫
        (G.tensorSwap (DerivedCategory.Q.obj Bc) (E.functor.obj (DerivedCategory.Q.obj K))).inv ≫
        G.tensor.map ((𝟙 (DerivedCategory.Q.obj Bc),
          (Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uR, max v uR uA} R K).hom) :
          (DerivedCategory.Q.obj Bc, E.functor.obj (DerivedCategory.Q.obj K)) ⟶
            (DerivedCategory.Q.obj Bc, DerivedCategory.Q.obj (lift.obj K))) ≫
        (G.tensorIso Bc (lift.obj K)
          (kFlat_restrictScalars_uliftRingEquiv.{uR, max v uA} K hK)).hom)).trans ?_
  · refine Eq.trans ?_ (map_comp_id_comp_map_clean E.inverse _ _ _ _ _)
    rfl
  · exact congrArg E.inverse.map (bifunctor_swap_regroup G.tensor _ (E.functor.map_id _) _ _
      (G.tensorSwap _ _) _ (G.tensorSwap _ _) _ _ _ hq hsw _ hC)

/-- **The resolved tail, read through the scalar lift.**  The inverse K-flat comparison of
[stacks 0A63] at `(K, P)`, the inverse resolution of the algebra in the second variable and the
transport tail of the independent-universe projection formula compose to the scalar-lift unit at
`K ⊗ P` followed by the lift of a chain map: the inverse comparison of total tensor products with
restriction of scalars, the inverse signed interchange, and the lifted resolution tensored into
the first variable. -/
theorem derivedTensor_comparison_inv_comp_tensor_map_comp_liftTransportTail
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    (derivedTensor_comparison.{uR, max v uR uA} R K P hP).inv ≫
      (derivedHomAdjunctionOverRing.{uR, max v uR uA, max v uR uA + 1} R).tensor.map
        ((𝟙 (DerivedCategory.Q.obj K), (algebraResolutionIso.{v} f P p).inv) :
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ⟶
            (DerivedCategory.Q.obj K, derivedAlgebraSingle.{uR, uA, v} f)) ≫
      liftTransportTail.{v, uR, uA} f K hK =
    Stacks.DerivedHom.BaseChange.scalarLiftUnit.{uR, max v uR uA} R
        (tensorComplex.{uR, max v uR uA} K P) ≫
      E.inverse.map (DerivedCategory.Q.map
        ((restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            K P).inv ≫
          (Model.complexSwap (ULift.{max v uR uA} R) (lift.obj P) (lift.obj K)).inv ≫
            ((lift.map p ≫ algebraLiftChain.{v} f) ▷ lift.obj K))) := by
  intro E lift
  exact inv_comp_eq_of_presentation DerivedCategory.Q E.inverse _ _ _ _ _ _ _
    (Stacks.DerivedHom.BaseChange.scalarEquivalence_inverse_map_tensor_scalarLift.{uR,
      max v uR uA} R K P hP)
    (tensor_map_algebraResolutionIso_inv_comp_liftTransportTail.{v} f P hP p K hK)

omit [QuasiIso p] in
/-- **The resolution of the algebra, carried through the lifted chain-level tail.** -/
theorem lift_map_tensor_resolution_comp_chainTail
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    lift.map (HomologicalComplex.mapBifunctorMap (𝟙 K) p (moduleTensor.{uR, max v uR uA} R)
        (ComplexShape.up ℤ)) ≫
      (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
          K (algebraComplex.{v} f)).inv ≫
        (Model.complexSwap (ULift.{max v uR uA} R) (lift.obj (algebraComplex.{v} f))
          (lift.obj K)).inv ≫ (algebraLiftChain.{v} f ▷ lift.obj K) =
    (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R) K P).inv ≫
      (Model.complexSwap (ULift.{max v uR uA} R) (lift.obj P) (lift.obj K)).inv ≫
        ((lift.map p ≫ algebraLiftChain.{v} f) ▷ lift.obj K) := by
  intro lift
  have h1 : HomologicalComplex.mapBifunctorMap (lift.map (𝟙 K)) (lift.map p)
        (moduleTensor (ULift.{max v uR uA} R)) (ComplexShape.up ℤ) ≫
      (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
          K (algebraComplex.{v} f)).hom =
      (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R) K P).hom ≫
        lift.map (HomologicalComplex.mapBifunctorMap (𝟙 K) p
          (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ)) :=
    restrictScalarsTensorComplexIso_naturality
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R) (𝟙 K) p
  rw [CategoryTheory.Functor.map_id] at h1
  let := CochainComplex.Koszul.koszulSymmetric (ULift.{max v uR uA} R)
  exact comp_three_squares _ _ _ _ _ _ _ _ _
    (comp_inv_eq_inv_comp_of_square _ _ _ _ h1)
    (BraidedCategory.braiding_inv_naturality_right (lift.obj K) (lift.map p))
    (MonoidalCategory.comp_whiskerRight _ _ _).symm

/-- **The resolution of the algebra removed from the resolved tail.** -/
theorem kFlatTensorResolutionIso_inv_comp_scalarLiftUnit
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    (kFlatTensorResolutionIso.{v} f P p K hK).inv ≫
      Stacks.DerivedHom.BaseChange.scalarLiftUnit.{uR, max v uR uA} R
        (tensorComplex.{uR, max v uR uA} K P) ≫
      E.inverse.map (DerivedCategory.Q.map
        ((restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            K P).inv ≫
          (Model.complexSwap (ULift.{max v uR uA} R) (lift.obj P) (lift.obj K)).inv ≫
            ((lift.map p ≫ algebraLiftChain.{v} f) ▷ lift.obj K))) =
    Stacks.DerivedHom.BaseChange.scalarLiftUnit.{uR, max v uR uA} R
        (tensorComplex.{uR, max v uR uA} K (algebraComplex.{v} f)) ≫
      E.inverse.map (DerivedCategory.Q.map
        ((restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            K (algebraComplex.{v} f)).inv ≫
          (Model.complexSwap (ULift.{max v uR uA} R) (lift.obj (algebraComplex.{v} f))
            (lift.obj K)).inv ≫ (algebraLiftChain.{v} f ▷ lift.obj K))) := by
  intro E lift
  refine inv_comp_eq_of_natural _ _ (kFlatTensorResolutionIso_hom.{v} f P p K hK) _ _ _
    (Stacks.DerivedHom.BaseChange.scalarLiftUnit_naturality.{uR, max v uR uA} R _) _ _ ?_
  rw [← E.inverse.map_comp, ← DerivedCategory.Q.map_comp]
  exact congrArg (fun z => E.inverse.map (DerivedCategory.Q.map z))
    (lift_map_tensor_resolution_comp_chainTail.{v} f P p K)

/-- **The transport prefix at a K-flat complex, computed.**  The six-factor transport prefix of
the independent-universe projection formula at a K-flat `K` is the comparison of `F` at `K`,
followed by the unit of the scalar lift over `A`, the restriction comparison
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso`, and the scalar-lift presentation of
`A ⊗_R K` read back through the explicit comparison of [stacks 0E1W]. -/
theorem liftTransportPrefix_eq (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
    let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max v uR uA} A
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let U := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategory
    let YP := ((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    liftTransportPrefix.{v, uR, uA} f F comparison K =
      U.map (comparison.app K) ≫ U.map (S.unitIso.hom.app (DerivedCategory.Q.obj YP)) ≫
        (Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f).hom.app
          (S.functor.obj (DerivedCategory.Q.obj YP)) ≫
        E.inverse.map (V.map ((Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA, max v uR uA}
            A YP).hom ≫
          DerivedCategory.Q.map (extendScalarsLiftChainIso.{uR, uA, v} f K).inv)) := by
  intro E S f' U V YP
  have hE :=
    Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app_comp_comparison_eq.{uR,
      uA, v} f F comparison K (extendScalarsLiftChainIso.{uR, uA, v} f K).hom
      (Stacks.DerivedHom.BaseChange.scalarLiftExtendUnitChain_eq.{uR, uA, v} f K)
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{max v uR uA,
    max v uR uA, max v uR uA} f'
      (HomologicalComplex.zero :
        CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} A)) ℤ)
  let a := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, v}
    f F comparison
  let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{
    max v uR uA, max v uR uA, max v uR uA} _ _ _ _ f' _ _ T.B T.alphaB T.isLeftDerivedB
  let eF : E.functor ⋙ T.B ≅ F ⋙ S.functor :=
    (E.toAdjunction.comp a').leftAdjointUniq ((a.comp S.toAdjunction).ofNatIsoRight
      (Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f))
  refine Eq.trans ?_ (transport_prefix_generic S U V E.inverse
    (Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f) (comparison.app K)
    (eF.hom.app (DerivedCategory.Q.obj K)) (eF.inv.app (DerivedCategory.Q.obj K))
    (eF.inv_hom_id_app (DerivedCategory.Q.obj K)) _ _
    (DerivedCategory.Q.mapIso (extendScalarsLiftChainIso.{uR, uA, v} f K))
    (Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA, max v uR uA} A YP) hE)
  rfl

/-- The chain map carried by the transport part of the independent-universe projection formula:
the scalar-lift counit over `A`, the restriction comparison, the explicit comparison of
[stacks 0E1W] and the chain-level projection formula over the lifted ring. -/
def transportChain (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :=
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let lift := (ModuleCat.restrictScalars.{max v uR uA}
    (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let restr := (ModuleCat.restrictScalars.{max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let YP := ((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let liftA := (ModuleCat.restrictScalars.{max v uR uA}
    (ULift.ringEquiv : ULift.{max v uR uA} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let c₁ := lift.map (restr.map
      (Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max v uR uA} A YP))
  let c₂ := Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison.{uR, uA, v} f
    (liftA.obj YP)
  let c₃ := ((ModuleCat.restrictScalars.{max v uR uA} f').mapHomologicalComplex
    (ComplexShape.up ℤ)).map (extendScalarsLiftChainIso.{uR, uA, v} f K).inv
  let c₄ := (extendRestrictScalarsComplexIso f').hom.app (lift.obj K)
  c₁ ≫ c₂ ≫ c₃ ≫ c₄

/-- The transport part of the independent-universe projection formula followed by the
chain-level projection formula over the lifted ring, as one morphism. -/
def transportValue (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :=
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max v uR uA} A
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let U := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory
  let V := (ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategory
  let YP := ((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let lift := (ModuleCat.restrictScalars.{max v uR uA}
    (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  U.map (S.unitIso.hom.app (DerivedCategory.Q.obj YP)) ≫
    (Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f).hom.app
      (S.functor.obj (DerivedCategory.Q.obj YP)) ≫
    E.inverse.map (V.map ((Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA, max v uR uA}
        A YP).hom ≫ DerivedCategory.Q.map (extendScalarsLiftChainIso.{uR, uA, v} f K).inv)) ≫
    E.inverse.map ((ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategoryFactors.app
      ((CochainComplex.extendScalarsLarge f').obj (lift.obj K))).hom ≫
    E.inverse.map (DerivedCategory.Q.map
      ((extendRestrictScalarsComplexIso f').hom.app (lift.obj K)))

/-- The same morphism, read as a factorization, a scalar-lift unit and a lifted chain map. -/
def transportChainValue (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :=
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let restr := (ModuleCat.restrictScalars.{max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let YP := ((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategoryFactors.hom.app YP ≫
    Stacks.DerivedHom.BaseChange.scalarLiftUnit.{uR, max v uR uA} R (restr.obj YP) ≫
    E.inverse.map (DerivedCategory.Q.map (transportChain.{v} f K))

/-- `Dualizing.transportValue` is the scalar-lift factorization, the scalar-lift unit and the lift
of the chain map `Dualizing.transportChain`. -/
theorem transportValue_eq (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) :
    transportValue.{v} f K = transportChainValue.{v} f K := by
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR, max v uR uA} R
  let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uA, max v uR uA} A
  let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let U := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategory
  let YP := ((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let liftA := (ModuleCat.restrictScalars.{max v uR uA}
    (ULift.ringEquiv : ULift.{max v uR uA} A ≃+* A).toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)
  let restr := (ModuleCat.restrictScalars.{max v uR uA} f).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let ψ := Stacks.DerivedHom.BaseChange.scalarLiftQObjIso.{uA, max v uR uA} A YP
  have F1 := ((Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f).hom.naturality
    ψ.hom).symm
  have F2 := map_comp_eq_of_comp_hom U _ _
    ((Stacks.DerivedHom.BaseChange.scalarEquivalenceInverseFactors.{uA, max v uR uA} A).app
      (liftA.obj YP)) _
    (Stacks.DerivedHom.BaseChange.scalarEquivalence_unitIso_hom_app_Q_comp.{uA, max v uR uA} A YP)
  have F3 := solve_delta E.inverse _ _ _ _
    ((Stacks.DerivedHom.BaseChange.scalarRestrictionIso.{uR, uA, v} f).app
      (DerivedCategory.Q.obj (liftA.obj YP)))
    ((ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategoryFactors.app _) _
    (Stacks.DerivedHom.BaseChange.unitIso_comp_inverse_map_chain_comp_scalarRestrictionIso_inv.{uR,
      uA, v} f (liftA.obj YP))
  have F4 := (ModuleCat.restrictScalars.{max v uR uA} f).mapDerivedCategoryFactors.hom.naturality
    (Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max v uR uA} A YP)
  have F5 := Stacks.DerivedHom.BaseChange.scalarLiftUnit_naturality.{uR, max v uR uA} R
    (restr.map (Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max v uR uA} A YP))
  have F6 := map_natural_solve E.inverse _
    ((ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategoryFactors.app _)
    ((ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategoryFactors.app _) _
    ((ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategoryFactors.hom.naturality
      (extendScalarsLiftChainIso.{uR, uA, v} f K).inv)
  let V := (ModuleCat.restrictScalars.{max v uR uA} f').mapDerivedCategory
  exact paste_prefix_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 F2 F3 F4 F5 F6 _
    ((congrArg E.inverse.map (V.map_comp _ _)).trans (E.inverse.map_comp _ _)) _
    (map_map_comp_four DerivedCategory.Q E.inverse _ _ _ _)

set_option linter.checkUnivs false in
/-- The summand inclusions of the total tensor complex over the lifted ring are those of the
monoidal tensor product of complexes. -/
theorem ιMapBifunctor_moduleTensor_lift_eq
    (K L : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ) (p q n : ℤ)
    (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor K L (moduleTensor.{max v uR uA, uR} (ULift.{max v uR uA} R))
        (ComplexShape.up ℤ) p q n h =
      HomologicalComplex.ιTensorObj K L p q n h :=
  rfl

set_option linter.checkUnivs false in
/-- A fourfold composite of chain maps over the lifted ring in degree `n`, computed on the
summand of bidegree `(n, 0)` through four summand inclusions. -/
theorem lifted_tail_f {X₀ X₁ : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ}
    (Kt At Bt : CochainComplex (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) ℤ)
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ tensorComplex.{max v uR uA, uR} Kt At) (c : Kt ⊗ At ⟶ At ⊗ Kt)
    (d : At ⊗ Kt ⟶ Bt ⊗ Kt) (n : ℤ) {Y₁ Y₄ : ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)}
    (m : X₀.X n ⟶ Y₁) (ι₁ : Y₁ ⟶ X₁.X n)
    (ri : Y₁ ⟶ ModuleCat.of (ULift.{max v uR uA} R) (TensorProduct (ULift.{max v uR uA} R)
      (Kt.X n) (At.X 0)))
    (β : Kt.X n ⊗ At.X 0 ⟶ At.X 0 ⊗ Kt.X n) (w : At.X 0 ⊗ Kt.X n ⟶ Y₄)
    (ι₄ : Y₄ ⟶ (Bt ⊗ Kt).X n)
    (ha : a.f n = m ≫ ι₁)
    (hb : ι₁ ≫ b.f n = ri ≫ HomologicalComplex.ιMapBifunctor Kt At
      (moduleTensor.{max v uR uA, uR} (ULift.{max v uR uA} R)) (ComplexShape.up ℤ) n 0 n
        (add_zero n))
    (hc : HomologicalComplex.ιTensorObj Kt At n 0 n (add_zero n) ≫ c.f n =
      β ≫ HomologicalComplex.ιTensorObj At Kt 0 n n (zero_add n))
    (hd : HomologicalComplex.ιTensorObj At Kt 0 n n (zero_add n) ≫ d.f n = w ≫ ι₄) :
    (a ≫ b ≫ c ≫ d).f n = m ≫ ri ≫ β ≫ w ≫ ι₄ := by
  have hc' : HomologicalComplex.ιMapBifunctor Kt At
      (moduleTensor.{max v uR uA, uR} (ULift.{max v uR uA} R)) (ComplexShape.up ℤ) n 0 n
        (add_zero n) ≫ c.f n =
      β ≫ HomologicalComplex.ιTensorObj At Kt 0 n n (zero_add n) := hc
  have hs : (a ≫ b ≫ c ≫ d).f n = a.f n ≫ b.f n ≫ c.f n ≫ d.f n := rfl
  exact hs.trans (chain_tail _ _ _ _ _ _ _ _ _ _ _ _ ha hb hc' hd)

/-- The inverse comparison of total tensor products with restriction of scalars, on the summand of
bidegree `(n, 0)`. -/
theorem tail_h2 (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ) :
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    (ModuleCat.restrictScalars.{max v uR uA}
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).map
      (HomologicalComplex.ιMapBifunctor K (algebraComplex.{v} f)
        (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ) n 0 n (add_zero n)) ≫
      (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            K (algebraComplex.{v} f)).inv.f n =
      (restrictScalarsTensorIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            (K.X n) ((algebraComplex.{v} f).X 0)).inv ≫
        HomologicalComplex.ιMapBifunctor (lift.obj K) (lift.obj (algebraComplex.{v} f))
          (moduleTensor.{max v uR uA, uR} (ULift.{max v uR uA} R)) (ComplexShape.up ℤ) n 0 n
            (add_zero n) := by
  intro lift
  exact summand_inv _ _ _ _ (by
      rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]) _
    (CochainComplex.DerivedTensor.ι_restrictScalarsTensorComplexIso_hom
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R) K (algebraComplex.{v} f) n 0 n (add_zero n))

/-- The inverse signed interchange on the summand of bidegree `(n, 0)`: the Koszul sign is one. -/
theorem tail_h3 (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ) :
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    HomologicalComplex.ιTensorObj (lift.obj K) (lift.obj (algebraComplex.{v} f)) n 0 n
        (add_zero n) ≫
      (Model.complexSwap (ULift.{max v uR uA} R) (lift.obj (algebraComplex.{v} f))
        (lift.obj K)).inv.f n =
      (β_ ((lift.obj K).X n) ((lift.obj (algebraComplex.{v} f)).X 0)).hom ≫
        HomologicalComplex.ιTensorObj (lift.obj (algebraComplex.{v} f)) (lift.obj K) 0 n n
          (zero_add n) := by
  intro lift
  have h3 := CochainComplex.Koszul.koszulSymmetric_braiding_ιTensorObj (ULift.{max v uR uA} R)
    (lift.obj K) (lift.obj (algebraComplex.{v} f)) n 0 n (add_zero n)
  rw [mul_zero, Int.negOnePow_zero, one_smul] at h3
  have hc : (Model.complexSwap (ULift.{max v uR uA} R) (lift.obj (algebraComplex.{v} f))
      (lift.obj K)).inv =
      ((CochainComplex.Koszul.koszulSymmetric (ULift.{max v uR uA} R)).toBraidedCategory.braiding
        (lift.obj K) (lift.obj (algebraComplex.{v} f))).hom := by
    let := CochainComplex.Koszul.koszulSymmetric (ULift.{max v uR uA} R)
    exact (SymmetricCategory.braiding_swap_eq_inv_braiding _ _).symm
  rwa [hc]

/-- The lifted algebra chain map tensored into the first variable, on the summand of bidegree
`(0, n)`. -/
theorem tail_h4 (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ) :
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let Bc := (CochainComplex.singleFunctor
      (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
      ((ModuleCat.restrictScalars f').obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
    HomologicalComplex.ιTensorObj (lift.obj (algebraComplex.{v} f)) (lift.obj K) 0 n n
        (zero_add n) ≫ (algebraLiftChain.{v} f ▷ lift.obj K).f n =
      ((algebraLiftChain.{v} f).f 0 ▷ (lift.obj K).X n) ≫
        HomologicalComplex.ιTensorObj Bc (lift.obj K) 0 n n (zero_add n) := by
  intro lift f' Bc
  have h4 := HomologicalComplex.ι_mapBifunctorMap (algebraLiftChain.{v} f) (𝟙 (lift.obj K))
    (curriedTensor _) (ComplexShape.up ℤ) 0 n n (zero_add n)
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id] at h4
  exact h4

/-- **The resolved chain-level tail in one degree.** -/
theorem resolvedChainTail_f (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ) :
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let Bc := (CochainComplex.singleFunctor
      (ModuleCat.{max v uR uA} (ULift.{max v uR uA} R)) 0).obj
      ((ModuleCat.restrictScalars f').obj
        (ModuleCat.of (ULift.{max v uR uA} A) (ULift.{max v uR uA} A)))
    (lift.map (extendRestrictComplexIso.{v} f K).hom ≫
        (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            K (algebraComplex.{v} f)).inv ≫
          (Model.complexSwap (ULift.{max v uR uA} R) (lift.obj (algebraComplex.{v} f))
            (lift.obj K)).inv ≫ (algebraLiftChain.{v} f ▷ lift.obj K)).f n =
      (ModuleCat.restrictScalars.{max v uR uA}
          (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).map
          ((extendRestrictFlipIso.{v} f).hom.app (K.X n) ≫
            ((moduleTensor.{uR, max v uR uA} R).obj (K.X n)).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (algebraModule.{v} f)).inv) ≫
        (restrictScalarsTensorIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            (K.X n) ((algebraComplex.{v} f).X 0)).inv ≫
        (β_ ((lift.obj K).X n) ((lift.obj (algebraComplex.{v} f)).X 0)).hom ≫
        ((algebraLiftChain.{v} f).f 0 ▷ (lift.obj K).X n) ≫
        HomologicalComplex.ιTensorObj Bc (lift.obj K) 0 n n (zero_add n) := by
  intro lift f' Bc
  have h1 : (lift.map (extendRestrictComplexIso.{v} f K).hom).f n =
      (ModuleCat.restrictScalars.{max v uR uA}
          (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).map
          ((extendRestrictFlipIso.{v} f).hom.app (K.X n) ≫
            ((moduleTensor.{uR, max v uR uA} R).obj (K.X n)).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (algebraModule.{v} f)).inv) ≫
        (ModuleCat.restrictScalars.{max v uR uA}
          (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).map
            (HomologicalComplex.ιMapBifunctor K (algebraComplex.{v} f)
              (moduleTensor.{uR, max v uR uA} R) (ComplexShape.up ℤ) n 0 n (add_zero n)) :=
    Eq.trans rfl ((congrArg (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).map
        (Category.assoc _ _ _).symm).trans (Functor.map_comp _ _ _))
  exact lifted_tail_f.{v, uR, uA} _ _ _ _ _ _ _ n _ _ _ _ _ _ h1 (tail_h2.{v} f K n)
    (tail_h3.{v} f K n) (tail_h4.{v} f K n)

/-- **The resolved tail on a pure tensor.** -/
theorem resolvedTail_tmul (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ)
    (a : A) (m : K.X n) :
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := f.toAlgebra
    ((ModuleCat.restrictScalars.{max v uR uA}
          (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).map
          ((extendRestrictFlipIso.{v} f).hom.app (K.X n) ≫
            ((moduleTensor.{uR, max v uR uA} R).obj (K.X n)).map
              (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
                (algebraModule.{v} f)).inv) ≫
        (restrictScalarsTensorIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            (K.X n) ((algebraComplex.{v} f).X 0)).inv ≫
        (β_ ((lift.obj K).X n) ((lift.obj (algebraComplex.{v} f)).X 0)).hom ≫
        ((algebraLiftChain.{v} f).f 0 ▷ (lift.obj K).X n)).hom (a ⊗ₜ[R] m) =
      (ULift.up a : ULift.{max v uR uA} A) ⊗ₜ m := by
  intro lift
  simp only [ModuleCat.hom_comp, algebraLiftChain, HomologicalComplex.comp_f,
    Functor.mapCochainComplexSingleFunctor]
  rfl

/-- The inverse comparison of [stacks 0E1W] on a pure tensor. -/
theorem extendScalarsLiftNatIso_inv_app_tmul (M : ModuleCat.{max v uR uA} R) (a : A) (m : M) :
    ((extendScalarsLiftNatIso.{uR, uA, v} f).inv.app M).hom (a ⊗ₜ[R, f] m) =
      ((ULift.up a : ULift.{max uR uA v} A) ⊗ₜ[ULift.{max uR uA v} R,
        liftRingHom.{uR, uA, v} f] m) := by
  have h0 : ((extendScalarsLiftNatIso.{uR, uA, v} f).hom.app M).hom
      ((ULift.up a : ULift.{max uR uA v} A) ⊗ₜ[ULift.{max uR uA v} R,
        liftRingHom.{uR, uA, v} f] m) = a ⊗ₜ[R, f] m :=
    extendScalarsLiftNatIso_hom_app_tmul.{uR, uA, v} f M _ m
  have h1 := congrArg (fun φ => ModuleCat.Hom.hom φ
    ((ULift.up a : ULift.{max uR uA v} A) ⊗ₜ[ULift.{max uR uA v} R,
      liftRingHom.{uR, uA, v} f] m)) ((extendScalarsLiftNatIso.{uR, uA, v} f).hom_inv_id_app M)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h1
  exact (congrArg (ModuleCat.Hom.hom ((extendScalarsLiftNatIso.{uR, uA, v} f).inv.app M))
    h0.symm).trans h1

/-- **The transport tail on a pure tensor.** -/
theorem transportTail_tmul (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (n : ℤ)
    (a : A) (m : K.X n) :
    let f' : ULift.{max v uR uA} R →+* ULift.{max v uR uA} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    let lift := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    let restr := (ModuleCat.restrictScalars.{max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ)
    let YP := ((ModuleCat.extendScalars.{uR, uA, max v uR uA} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    let liftA := (ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} A ≃+* A).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)
    letI := f.toAlgebra
    ((lift.map (restr.map
        (Stacks.DerivedHom.BaseChange.scalarLiftCounitInv.{uA, max v uR uA} A YP))).f n ≫
      (Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison.{uR, uA, v} f
        (liftA.obj YP)).f n ≫
      (((ModuleCat.restrictScalars.{max v uR uA} f').mapHomologicalComplex
        (ComplexShape.up ℤ)).map (extendScalarsLiftChainIso.{uR, uA, v} f K).inv).f n ≫
      (extendRestrictScalarsModuleIso f').hom.app ((lift.obj K).X n)).hom (a ⊗ₜ[R] m) =
      (ULift.up a : ULift.{max v uR uA} A) ⊗ₜ m := by
  intro f' lift restr YP liftA
  refine ModuleCat_hom_comp₄_eq (w₂ := a ⊗ₜ[R, f] m)
    (w₃ := ((ULift.up a : ULift.{max uR uA v} A) ⊗ₜ[ULift.{max uR uA v} R,
        liftRingHom.{uR, uA, v} f] m)) ?_ ?_ ?_
  · rfl
  · exact extendScalarsLiftNatIso_inv_app_tmul.{v} f (K.X n) a m
  · exact extendRestrictScalarsModuleIso_hom_app_apply f' _ _

/-- **The chain-level identity.** The chain map
`Dualizing.transportChain` carried by the transport part of the independent-universe projection
formula is the scalar lift of the chain-level projection formula
`Dualizing.extendRestrictComplexIso`, followed by the inverse comparison of total tensor products
with restriction of scalars, the inverse signed interchange and the lifted algebra tensored into
the first variable. -/
def TransportChainIdentity : Prop :=
  ∀ K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ,
    transportChain.{v} f K =
      ((ModuleCat.restrictScalars.{max v uR uA}
        (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (extendRestrictComplexIso.{v} f K).hom ≫
        (restrictScalarsTensorComplexIso (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R)
            K (algebraComplex.{v} f)).inv ≫
          (Model.complexSwap (ULift.{max v uR uA} R)
            (((ModuleCat.restrictScalars.{max v uR uA}
              (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj (algebraComplex.{v} f))
            (((ModuleCat.restrictScalars.{max v uR uA}
              (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)).inv ≫
            (algebraLiftChain.{v} f ▷
              ((ModuleCat.restrictScalars.{max v uR uA}
                (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj K)

/-- **`Dualizing.TransportChainIdentity` holds.** -/
theorem transportChainIdentity : TransportChainIdentity.{v} f := by
  intro K
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [resolvedChainTail_f.{v} f K n]
  have h := extendRestrictScalarsComplexIso_hom_app_f
    ((ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom :
      ULift.{max v uR uA} R →+* ULift.{max v uR uA} A)
    (((ModuleCat.restrictScalars.{max v uR uA}
      (ULift.ringEquiv : ULift.{max v uR uA} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) n
  dsimp only [transportChain]
  refine (comp4_f_of_zero _ _ _ _ n).trans ?_
  refine (comp_last_congr _ _ _ _ _ h).trans ?_
  refine comp_four_incl _ _ _ _ _ _ _ _ _ ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    refine (LinearMap.map_add _ x y).trans ?_
    refine Eq.trans ?_ (LinearMap.map_add _ x y).symm
    exact congrArg₂ (· + ·) hx hy
  | tmul a m =>
    exact (transportTail_tmul.{v} f K n a m).trans (resolvedTail_tmul.{v} f K n a m).symm

/-- **The two projection formulas agree on K-flat complexes**, given
`Dualizing.TransportChainIdentity`. -/
theorem derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_eq_of_transportChainIdentity
    (hchain : TransportChainIdentity.{v} f) (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).hom.app
        (DerivedCategory.Q.obj K) =
      (resolvedProjectionComponent.{v} f F comparison P hP p K hK).hom := by
  have : IsIso (liftTransportTail.{v, uR, uA} f K hK) :=
    Iso.isIso_hom ((liftFlipConjugate.{v, uR, uA} f).app (DerivedCategory.Q.obj K) ≪≫
      (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
        max v uR uA} R).inverse.mapIso ((liftCoeffIso.{v, uR, uA} f).symm.app _) ≪≫
      (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
        max v uR uA} R).inverse.mapIso (liftTensorPsi.{v, uR, uA} f K) ≪≫
      (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
        max v uR uA} R).inverse.mapIso (liftKFlatTensorIso.{v, uR, uA} f K hK))
  have hpair := derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_chainPairing.{v, uR, uA}
    f F comparison K hK
  have hL1 := liftTransportPrefix_eq.{v} f F comparison K
  have htv := transportValue_eq.{v} f K
  let Ei := (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,
      max v uR uA} R).inverse
  have hL4 := (congrArg (fun z => Ei.map (DerivedCategory.Q.map z))
    (hchain K)).trans
      ((congrArg Ei.map (DerivedCategory.Q.map_comp _ _)).trans (Ei.map_comp _ _))
  have hL3 := derivedTensor_comparison_inv_comp_tensor_map_comp_liftTransportTail.{v} f P hP p K hK
  have hL5 := kFlatTensorResolutionIso_inv_comp_scalarLiftUnit.{v} f P p K hK
  have hnat := Stacks.DerivedHom.BaseChange.scalarLiftUnit_naturality.{uR, max v uR uA} R
    (extendRestrictComplexIso.{v} f K).hom
  exact final_assembly (LT := liftTransportTail.{v, uR, uA} f K hK)
    (qe := DerivedCategory.Q.map (extendRestrictComplexIso.{v} f K).hom)
    (slA := Stacks.DerivedHom.BaseChange.scalarLiftUnit.{uR, max v uR uA} R
      (tensorComplex.{uR, max v uR uA} K (algebraComplex.{v} f)))
    (hpair := hpair) (hL1 := hL1) (htv := htv) (hL4 := hL4)
    (hR := resolvedProjectionComponent_hom.{v} f F comparison P hP p K hK) (hL3 := hL3)
    (hL5 := hL5) (hnat := hnat)

/-- **The two projection formulas are equal**, given `Dualizing.TransportChainIdentity`. -/
theorem derivedExtendRestrictScalarsTensorIso_eq_resolvedProjectionFormula_of_transportChainIdentity
    (hchain : TransportChainIdentity.{v} f) :
    derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison =
      resolvedProjectionFormula.{v} f F comparison P hP p := by
  refine Iso.ext (NatTrans.ext (funext fun X => ?_))
  obtain ⟨L, s, hL, -, hs, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{uR, max v uA}
    (DerivedCategory.Q.objPreimage X)
  have := hs
  let e : X ≅ DerivedCategory.Q.obj L :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫ (asIso (DerivedCategory.Q.map s)).symm
  rw [Stacks.DerivedHom.BaseChange.natTrans_app_eq_of_iso _ e,
    Stacks.DerivedHom.BaseChange.natTrans_app_eq_of_iso
      (resolvedProjectionFormula.{v} f F comparison P hP p).hom e,
    derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_eq_of_transportChainIdentity.{v} f F
      comparison P hP p hchain L hL,
    resolvedProjectionFormula_hom_app.{v} f F comparison P hP p L hL]

/-- **The two projection formulas agree on K-flat complexes.** -/
theorem derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_eq
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uR uA} K) :
    (derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison).hom.app
        (DerivedCategory.Q.obj K) =
      (resolvedProjectionComponent.{v} f F comparison P hP p K hK).hom :=
  derivedExtendRestrictScalarsTensorIso_hom_app_q_obj_eq_of_transportChainIdentity.{v} f F
    comparison P hP p (transportChainIdentity.{v} f) K hK

/-- **The resolved projection formula is the projection formula.**  The isomorphism
`F ⋙ U ≅ (- ⊗ᴸ_R A)` built by transport through the universe lifts,
`Dualizing.derivedExtendRestrictScalarsTensorIso`, is the one built from chain-level
isomorphisms at K-flat complexes and any K-flat resolution `p` of the algebra,
`Dualizing.resolvedProjectionFormula`. -/
theorem derivedExtendRestrictScalarsTensorIso_eq_resolvedProjectionFormula :
    derivedExtendRestrictScalarsTensorIso.{uR, uA, v} f F comparison =
      resolvedProjectionFormula.{v} f F comparison P hP p :=
  derivedExtendRestrictScalarsTensorIso_eq_resolvedProjectionFormula_of_transportChainIdentity.{v}
    f F comparison P hP p (transportChainIdentity.{v} f)

end Clean

end Dualizing
