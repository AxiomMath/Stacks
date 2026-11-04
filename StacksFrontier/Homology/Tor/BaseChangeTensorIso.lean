module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensor

@[expose] public noncomputable section

/-!
# Derived tensor products and base change

Let `f : R →+* A` be a homomorphism of commutative rings. Derived extension of scalars along `f`
is monoidal for the derived tensor products of `R` and of `A`: for complexes `K, L` of
`R`-modules there is a canonical isomorphism

`(K ⊗ᴸ_R A) ⊗ᴸ_A (L ⊗ᴸ_R A) ≅ (K ⊗ᴸ_R L) ⊗ᴸ_R A`

in `D(A)`, natural in `K` and `L`. On K-flat representatives it is induced by the ordinary
base-change isomorphism `(A ⊗_R K) ⊗_A (A ⊗_R L) ≅ A ⊗_R (K ⊗_R L)` of total complexes, summand
by summand.

The file also records the consequences of flatness: if `f` is flat then degreewise extension of
scalars is exact, so derived extension of scalars commutes with homology; specialized to a
localization `R → R_S` this identifies `Hⁱ(K ⊗ᴸ_R R_S)` with `Hⁱ(K)_S`, and for `S` the powers
of a single element with the localization away from that element.

Ring and module universes are independent throughout.

## Main definitions

* `CochainComplex.DerivedTensor.extensionOfScalarsCochain`: degreewise extension of scalars on
  complexes, in a common module universe.
* `CochainComplex.DerivedTensor.IsTensorBaseChangeIso`: the property of an isomorphism of total
  complexes of being the ordinary tensor base-change isomorphism on every homogeneous summand.
* `CochainComplex.DerivedTensor.DerivedExtensionScalarsTensorIso`: the derived base-change
  isomorphism together with the diagram identifying it on K-flat representatives.
* `CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso`: its construction.
* `CochainComplex.DerivedTensor.extensionScalars`: extension of scalars on modules in a common
  universe.
* `CochainComplex.DerivedTensor.localizedModuleFunctor`: localization of modules at a submonoid,
  as a functor.
* `CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso`: for a flat `f`, derived
  extension of scalars commutes with each homology functor.
* `CochainComplex.DerivedTensor.derivedExtensionScalarsAwayHomologyIso`: the identification
  `Hⁱ(K ⊗ᴸ_R R_g) ≅ (Hⁱ K)_g` for the localization away from an element `g`.

## Main results

* `CochainComplex.DerivedTensor.extensionScalars_preservesHomology`: extension of scalars along
  a flat ring homomorphism preserves homology.

## Implementation notes

The derived isomorphism is obtained by comparing the two derived bifunctors on the K-flat
models: the K-flat complexes resolve every object of the homotopy category, so the pairs of
K-flat models localize to pairs of objects of the derived category, and a natural isomorphism on
the models descends. The prescribed value on K-flat representatives is the degreewise tensor
base-change isomorphism, which on the antidiagonal summand `K^p ⊗ L^q` is the inverse of
`TensorProduct.AlgebraTensorModule.distribBaseChange`.

Extension of scalars preserves K-flatness, which is the chain-level projection formula of
`CochainComplex.KFlat.ScalarBaseChange`.

## References

* [The Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.LeftDerivedByResolutions

namespace CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

section Interface

universe u uR uA v

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]

/-- Termwise extension of scalars on cochain complexes, in a common module universe containing
both rings. -/
public noncomputable def extensionOfScalarsCochain (f : R →+* A) :
    CochainComplex (ModuleCat.{max uR uA v} R) ℤ ⥤
      CochainComplex (ModuleCat.{max uR uA v} A) ℤ := by
  letI : (ModuleCat.extendScalars.{uR, uA, max uR uA v} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA v, uR, uA} f).isLeftAdjoint
  exact (ModuleCat.extendScalars.{uR, uA, max uR uA v} f).mapHomologicalComplex
      (ComplexShape.up ℤ)

/-- A chain isomorphism is the standard tensor base-change isomorphism if, on every homogeneous
summand, it is the inverse of `AlgebraTensorModule.distribBaseChange`. -/
public def IsTensorBaseChangeIso (f : R →+* A)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (e : tensorComplex.{uA, max uR v} (extensionOfScalarsCochain f |>.obj K)
        (extensionOfScalarsCochain f |>.obj L) ≅
      (extensionOfScalarsCochain f).obj
        (tensorComplex.{uR, max uA v} K L)) : Prop :=
  letI := f.toAlgebra
  ∀ (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιMapBifunctor
          ((extensionOfScalarsCochain f).obj K) ((extensionOfScalarsCochain f).obj L)
          (moduleTensor.{uA, max uR v} A) (ComplexShape.up ℤ) p q n h ≫
        e.hom.f n =
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        R A (K.X p) (L.X q)).symm.toModuleIso.hom ≫
        (ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map
          (HomologicalComplex.ιMapBifunctor K L
            (moduleTensor.{uR, max uA v} R)
            (ComplexShape.up ℤ) p q n h)

/-- The canonical derived tensor base-change isomorphism, together with the diagram identifying
each K-flat component with the standard total-complex tensor base-change isomorphism. -/
public structure DerivedExtensionScalarsTensorIso (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f) where
  /-- The identification, natural in both derived complexes. -/
  iso : (D.functor.prod D.functor ⋙ Functor.uncurry.obj T_A.tensor) ≅
    (Functor.uncurry.obj T_R.tensor ⋙ D.functor)
  /-- On K-flat representatives the component is induced by standard tensor base change. -/
  comparison (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
      (hK : K.KFlat) (hL : L.KFlat) :
    ∃ (hFK : ((extensionOfScalarsCochain f).obj K).KFlat)
      (hFL : ((extensionOfScalarsCochain f).obj L).KFlat)
      (e : tensorComplex.{uA, max uR v} ((extensionOfScalarsCochain f).obj K)
          ((extensionOfScalarsCochain f).obj L) ≅
        (extensionOfScalarsCochain f).obj
          (tensorComplex.{uR, max uA v} K L)),
      IsTensorBaseChangeIso f K L e ∧
        (T_A.tensor.map (D.comparison.app K)).app (D.functor.obj (DerivedCategory.Q.obj L)) ≫
              (T_A.tensor.obj (DerivedCategory.Q.obj ((extensionOfScalarsCochain f).obj K))).map
                (D.comparison.app L) ≫
              (T_A.comparison _ _ hFK hFL).hom ≫ DerivedCategory.Q.map e.hom =
            iso.hom.app (X := (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
              D.functor.map (T_R.comparison K L hK hL).hom ≫
              D.comparison.app (tensorComplex.{uR, max uA v} K L)

end Interface

section Construction

universe uR uA v

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]

/-- In each degree, the total tensor complex of two base-changed complexes is isomorphic to the
base change of the total tensor complex, summand by summand via
`TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
private noncomputable def tensorComplexExtendScalarsXIso (f : R →+* A)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ) (n : ℤ) :
    (tensorComplex.{uA, max uR v} (extensionOfScalarsCochain f |>.obj K)
        (extensionOfScalarsCochain f |>.obj L)).X n ≅
      ((extensionOfScalarsCochain f).obj
        (tensorComplex.{uR, max uA v} K L)).X n := by
  letI := f.toAlgebra
  letI : (ModuleCat.extendScalars.{uR, uA, max uR uA v} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA v, uR, uA} f).isLeftAdjoint
  let F := ModuleCat.extendScalars.{uR, uA, max uR uA v} f
  let X := (((moduleTensor.{uR, max uA v} R).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L
  have hc := isColimitCofanMkObjOfIsColimit (G := F) (P := X.toGradedObject.mapObj
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
    (f := X.toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
    (fun x => X.toGradedObject.ιMapObj _ x.1 n x.2) (X.toGradedObject.isColimitCofanMapObj
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
  exact
  { hom := HomologicalComplex.mapBifunctorDesc (fun p q h =>
      (TensorProduct.AlgebraTensorModule.distribBaseChange
        R A (K.X p) (L.X q)).symm.toModuleIso.hom ≫
        F.map (HomologicalComplex.ιMapBifunctor K L
            (moduleTensor.{uR, max uA v} R) (ComplexShape.up ℤ) p q n h))
    inv := Cofan.IsColimit.desc hc (fun x => (TensorProduct.AlgebraTensorModule.distribBaseChange
        R A (K.X x.1.1) (L.X x.1.2)).toModuleIso.hom ≫ HomologicalComplex.ιMapBifunctor
          ((extensionOfScalarsCochain f).obj K) ((extensionOfScalarsCochain f).obj L)
          (moduleTensor.{uA, max uR v} A) (ComplexShape.up ℤ) x.1.1 x.1.2 n x.2)
    hom_inv_id := by
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      erw [HomologicalComplex.ι_mapBifunctorDesc_assoc, Category.assoc]
      erw [Cofan.IsColimit.fac hc _ ⟨⟨p, q⟩, h⟩]
      dsimp only
      rw [Category.comp_id]
      ext x
      exact congrArg _ ((TensorProduct.AlgebraTensorModule.distribBaseChange
        R A (K.X p) (L.X q)).apply_symm_apply x)
    inv_hom_id := by
      apply Cofan.IsColimit.hom_ext hc
      rintro ⟨⟨p, q⟩, h⟩
      erw [Cofan.IsColimit.fac_assoc hc _ ⟨⟨p, q⟩, h⟩]
      dsimp only [Cofan.mk_ι_app, Cofan.inj]
      erw [Category.comp_id, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
      ext x
      exact congrArg (F.map (X.toGradedObject.ιMapObj _ (p, q) n h)).hom
        ((TensorProduct.AlgebraTensorModule.distribBaseChange
        R A (K.X p) (L.X q)).symm_apply_apply (1 ⊗ₜ[R] x)) }
set_option backward.isDefEq.respectTransparency false

/-- The degreewise base-change comparison, read on the antidiagonal summand `K^p ⊗ L^q`. -/
private lemma ι_tensorComplexExtendScalarsXIso_hom (f : R →+* A)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    letI := f.toAlgebra
    HomologicalComplex.ιMapBifunctor
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L)
        (moduleTensor.{uA, max uR v} A) (.up ℤ) p q n h ≫
      (tensorComplexExtendScalarsXIso f K L n).hom =
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A (K.X p) (L.X q)).symm.toModuleIso.hom ≫
      (ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map
        (HomologicalComplex.ιMapBifunctor K L
          (moduleTensor.{uR, max uA v} R) (.up ℤ) p q n h) := by
  simp only [tensorComplexExtendScalarsXIso, HomologicalComplex.ι_mapBifunctorDesc]

/-- The inverse of `distribBaseChange` is natural in both module variables. -/
private lemma distribBaseChange_symm_naturality (f : R →+* A)
    {M M' N N' : ModuleCat.{max uR uA v} R} (a : M ⟶ M') (b : N ⟶ N') :
    letI := f.toAlgebra
    ((moduleTensor.{uA, max uR v} A).map
        ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map a)).app
        ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj N) ≫
      ((moduleTensor.{uA, max uR v} A).obj
        ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj M')).map
        ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map b) ≫
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M' N').symm.toModuleIso.hom =
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toModuleIso.hom ≫
      (ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map
        (((moduleTensor.{uR, max uA v} R).map a).app N ≫
          ((moduleTensor.{uR, max uA v} R).obj M').map b) := by
  let := f.toAlgebra
  let F := ModuleCat.extendScalars.{uR, uA, max uR uA v} f
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change TensorProduct R A M at x
  change TensorProduct R A N at y
  show (TensorProduct.AlgebraTensorModule.distribBaseChange R A M' N').symm
      ((F.map a).hom x ⊗ₜ[A] (F.map b).hom y) =
    (F.map (((moduleTensor.{uR, max uA v} R).map a).app N ≫
      ((moduleTensor.{uR, max uA v} R).obj M').map b)).hom
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm (x ⊗ₜ[A] y))
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.zero_tmul]
  | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
  | tmul r x =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero]
    | add y y' hy hy' => simp only [map_add, TensorProduct.tmul_add, hy, hy']
    | tmul s y =>
      show (TensorProduct.AlgebraTensorModule.distribBaseChange R A M' N').symm
          ((r ⊗ₜ[R] a.hom x) ⊗ₜ[A] (s ⊗ₜ[R] b.hom y)) = _
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
      rfl

/-- The inverse of `distribBaseChange` is natural in the first module variable. -/
private lemma distribBaseChange_symm_naturality_left (f : R →+* A)
    {M M' : ModuleCat.{max uR uA v} R} (a : M ⟶ M') (N : ModuleCat.{max uR uA v} R) :
    letI := f.toAlgebra
    ((moduleTensor.{uA, max uR v} A).map
      ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map a)).app
      ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj N) ≫
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M' N).symm.toModuleIso.hom =
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toModuleIso.hom ≫
      (ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map
        (((moduleTensor.{uR, max uA v} R).map a).app N) := by
  let := f.toAlgebra
  have hn := distribBaseChange_symm_naturality f a (𝟙 N)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id] at hn
  exact hn

/-- The inverse of `distribBaseChange` is natural in the second module variable. -/
private lemma distribBaseChange_symm_naturality_right (f : R →+* A)
    (M : ModuleCat.{max uR uA v} R) {N N' : ModuleCat.{max uR uA v} R} (b : N ⟶ N') :
    letI := f.toAlgebra
    ((moduleTensor.{uA, max uR v} A).obj
      ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj M)).map
      ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map b) ≫
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N').symm.toModuleIso.hom =
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toModuleIso.hom ≫
      (ModuleCat.extendScalars.{uR, uA, max uR uA v} f).map
        (((moduleTensor.{uR, max uA v} R).obj M).map b) := by
  let := f.toAlgebra
  have hn := distribBaseChange_symm_naturality f (𝟙 M) b
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at hn
  exact hn

/-- The degreewise base-change comparisons commute with the total differentials: on each
summand the two Koszul-signed partial differentials match on both sides. -/
private lemma tensorComplexExtendScalarsXIso_comm (f : R →+* A)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensorComplexExtendScalarsXIso f K L i).hom ≫
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj
          (tensorComplex.{uR, max uA v} K L)).d i j =
      (tensorComplex.{uA, max uR v} ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
          ((extensionOfScalarsCochain.{uR, uA, v} f).obj L)).d i j ≫
        (tensorComplexExtendScalarsXIso f K L j).hom := by
  let := f.toAlgebra
  let F := ModuleCat.extendScalars.{uR, uA, max uR uA v} f
  let : F.IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA v, uR, uA} f).isLeftAdjoint
  have : F.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _
    (by change PreservesFiniteColimits F; infer_instance)
  show (tensorComplexExtendScalarsXIso f K L i).hom ≫
      F.map (tensorComplex.{uR, max uA v} K L |>.d i j) = _
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hp : p + 1 + q = j := by change i + 1 = j at hij; change p + q = i at h; omega
  have hq : p + (q + 1) = j := by omega
  rw [← Category.assoc, ι_tensorComplexExtendScalarsXIso_hom, Category.assoc,
    ← F.map_comp]
  simp only [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
    Preadditive.add_comp, CategoryTheory.Functor.map_add]
  congr 1
  · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q j hp,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q j hp]
    simp only [CategoryTheory.Functor.map_units_smul, Linear.comp_units_smul,
      Linear.units_smul_comp,
      CategoryTheory.Functor.map_comp, Category.assoc,
      ι_tensorComplexExtendScalarsXIso_hom]
    erw [reassoc_of% distribBaseChange_symm_naturality_left f (K.d p (p + 1)) (L.X q)]
  · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) j hq,
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl) j hq]
    simp only [CategoryTheory.Functor.map_units_smul, Linear.comp_units_smul,
      Linear.units_smul_comp,
      CategoryTheory.Functor.map_comp, Category.assoc,
      ι_tensorComplexExtendScalarsXIso_hom]
    erw [reassoc_of% distribBaseChange_symm_naturality_right f (K.X p) (L.d q (q + 1))]

/-- The tensor base-change isomorphism of total complexes:
`(A ⊗_R K) ⊗_A (A ⊗_R L) ≅ A ⊗_R (K ⊗_R L)`. -/
private noncomputable def tensorComplexExtendScalarsIso (f : R →+* A)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ) :
    tensorComplex.{uA, max uR v} ((extensionOfScalarsCochain.{uR, uA, v} f).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} f).obj (tensorComplex.{uR, max uA v} K L) :=
  HomologicalComplex.Hom.isoOfComponents (tensorComplexExtendScalarsXIso f K L)
    (tensorComplexExtendScalarsXIso_comm f K L)

/-- The comparison of total complexes is the standard tensor base-change isomorphism on every
homogeneous summand. -/
private lemma tensorComplexExtendScalarsIso_normalized (f : R →+* A)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ) :
    IsTensorBaseChangeIso f K L (tensorComplexExtendScalarsIso f K L) :=
  ι_tensorComplexExtendScalarsXIso_hom f K L

/-- The tensor base-change isomorphism of total complexes is natural in both complexes. -/
private lemma tensorComplexExtendScalarsIso_naturality (f : R →+* A)
    {K K' L L' : CochainComplex (ModuleCat.{max uR uA v} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    HomologicalComplex.mapBifunctorMap
        ((extensionOfScalarsCochain.{uR, uA, v} f).map a)
        ((extensionOfScalarsCochain.{uR, uA, v} f).map b)
        (moduleTensor.{uA, max uR v} A) (.up ℤ) ≫
        (tensorComplexExtendScalarsIso f K' L').hom =
      (tensorComplexExtendScalarsIso f K L).hom ≫
        (extensionOfScalarsCochain.{uR, uA, v} f).map
          (HomologicalComplex.mapBifunctorMap a b
            (moduleTensor.{uR, max uA v} R) (.up ℤ)) := by
  let := f.toAlgebra
  let F := ModuleCat.extendScalars.{uR, uA, max uR uA v} f
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  show HomologicalComplex.ιMapBifunctor
      ((extensionOfScalarsCochain f).obj K) ((extensionOfScalarsCochain f).obj L)
      (moduleTensor.{uA, max uR v} A) (.up ℤ) p q n h ≫
      (HomologicalComplex.mapBifunctorMap
        ((extensionOfScalarsCochain f).map a) ((extensionOfScalarsCochain f).map b)
        (moduleTensor.{uA, max uR v} A) (.up ℤ)).f n ≫
      (tensorComplexExtendScalarsXIso f K' L' n).hom =
    HomologicalComplex.ιMapBifunctor
      ((extensionOfScalarsCochain f).obj K) ((extensionOfScalarsCochain f).obj L)
      (moduleTensor.{uA, max uR v} A) (.up ℤ) p q n h ≫
      (tensorComplexExtendScalarsXIso f K L n).hom ≫
      F.map ((HomologicalComplex.mapBifunctorMap a b
        (moduleTensor.{uR, max uA v} R) (.up ℤ)).f n)
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc,
    ι_tensorComplexExtendScalarsXIso_hom,
    reassoc_of% ι_tensorComplexExtendScalarsXIso_hom]
  simp (failIfUnchanged := false) only [Category.assoc]
  rw [← F.map_comp, HomologicalComplex.ι_mapBifunctorMap]
  let c₁ := ((moduleTensor.{uR, max uA v} R).map (a.f p)).app (L.X q)
  let c₂ := ((moduleTensor.{uR, max uA v} R).obj (K'.X p)).map (b.f q)
  let ι := HomologicalComplex.ιMapBifunctor K' L'
    (moduleTensor.{uR, max uA v} R) (.up ℤ) p q n h
  rw [← Category.assoc c₁ c₂ ι, F.map_comp (c₁ ≫ c₂) ι]
  exact (reassoc_of% distribBaseChange_symm_naturality f (a.f p) (b.f q)) _

/- The projection formula below is proved at the level of complexes, so K-flat
preservation does not depend on a derived base-change comparison. -/

/-- Extension of scalars carries K-flat complexes of `R`-modules to K-flat complexes of
`A`-modules. -/
private lemma isKFlat_extendScalars (f : R →+* A)
    (K : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uA v} K) :
    CochainComplex.KFlat.{uA, max uR v} ((extensionOfScalarsCochain.{uR, uA, v} f).obj K) :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uA, v} f K hK

open CategoryTheory.MonoidalCategory in
/-- The total tensor product of two K-flat complexes is K-flat, by associativity of the tensor
product of complexes. -/
lemma isKFlat_tensor
    (K L : CochainComplex (ModuleCat.{max uR v} R) ℤ)
    (hK : K.KFlat) (hL : L.KFlat) :
    (tensorComplex.{uR, v} K L).KFlat := by
  let : MonoidalCategoryStruct (ModuleCat.{max uR v} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, v}
  let : MonoidalCategory (ModuleCat.{max uR v} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, v}
  let : MonoidalPreadditive (ModuleCat.{max uR v} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, v}
  let : MonoidalClosed (ModuleCat.{max uR v} R) :=
    ModuleCat.liftedModuleMonoidalClosed.{uR, v}
  intro M hM
  have hflip : ∀ N : ModuleCat.{max v uR} R,
      PreservesColimits ((curriedTensor (ModuleCat.{max v uR} R)).flip.obj N) := fun N =>
    preservesColimits_of_natIso (NatIso.ofComponents
      (fun P => (TensorProduct.comm R N P).toModuleIso)
      (by intro P P' p; apply ModuleCat.hom_ext; apply TensorProduct.ext'; intro x n; rfl) :
        MonoidalCategory.tensorLeft N ≅ (curriedTensor (ModuleCat.{max v uR} R)).flip.obj N)
  let : ∀ M : ModuleCat.{max v uR} R, PreservesColimitsOfSize.{0,0}
      ((curriedTensor (ModuleCat.{max v uR} R)).flip.obj M) := fun M =>
    have := hflip M
    preservesSmallestColimits_of_preservesColimits _
  let : ∀ M : ModuleCat.{max v uR} R, PreservesColimitsOfSize.{0,0}
      ((curriedTensor (ModuleCat.{max v uR} R)).obj M) := fun M =>
    preservesSmallestColimits_of_preservesColimits _
  let : HomologicalComplex.HasGoodTensor₁₂ M K L := fun i j => by infer_instance
  let : HomologicalComplex.HasGoodTensor₂₃ M K L := fun i j => by infer_instance
  exact HomologicalComplex.Acyclic.of_iso (HomologicalComplex.associator M K L)
    (hL _ (hK M hM))
/-- The K-flat objects of the homotopy category, the resolving class for derived tensoring. -/
private abbrev kFlatModels (R : Type uR) [CommRing R] :
    ObjectProperty (HomotopyCategory (ModuleCat.{max uR v} R) (.up ℤ)) :=
  fun K => CochainComplex.KFlat K.as
/-- Localization restricted to the K-flat objects of the homotopy category. -/
private abbrev kFlatQ (R : Type uR) [CommRing R] :=
  (kFlatModels.{uR, v} R).ι ⋙ DerivedCategory.Qh
/-- The quasi-isomorphisms between K-flat objects of the homotopy category. -/
private abbrev kFlatW (R : Type uR) [CommRing R] :=
  (HomotopyCategory.quasiIso (ModuleCat.{max uR v} R) (.up ℤ)).inverseImage
    (kFlatModels.{uR, v} R).ι
/-- The K-flat objects localize to the whole derived category: they resolve every object, so
their inclusion is a localized equivalence. -/
private lemma kFlatQ_isLocalization (R : Type uR) [CommRing R] :
    (kFlatQ.{uR, v} R).IsLocalization (kFlatW.{uR, v} R) := by
  let W := HomotopyCategory.quasiIso (ModuleCat.{max uR v} R) (.up ℤ)
  let P := kFlatModels.{uR, v} R
  have : (inclusionLocalizerMorphism W P).HasLeftResolutions := fun X => by
    obtain ⟨K, s, hK, _, hs, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution X.as
    exact ⟨{
      X₁ := ⟨(HomotopyCategory.quotient _ _).obj K, hK⟩
      w := (HomotopyCategory.quotient _ _).map s
      hw := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs }⟩
  have := isLocalizedEquivalence_inclusionLocalizerMorphism W P
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (inclusionLocalizerMorphism W P) DerivedCategory.Qh

/-- Base change both arguments, then tensor over `A`, as a functor of pairs of complexes. -/
private abbrev baseChangedTensorFunctor (f : R →+* A)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f) :=
  D.functor.prod D.functor ⋙ CategoryTheory.Functor.uncurry.obj T_A.tensor

/-- Tensor over `R`, then base change, as a functor of pairs of complexes. -/
private abbrev tensorBaseChangeFunctor (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f) :=
  CategoryTheory.Functor.uncurry.obj T_R.tensor ⋙ D.functor

/-- On a pair of K-flat models, base changing and then tensoring over `A` is computed by the
ordinary total tensor product of the base-changed complexes. -/
private def tensorBaseChangeModelLeftIso (f : R →+* A)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uA v} K)
    (hL : CochainComplex.KFlat.{uR, max uA v} L) :
    (baseChangedTensorFunctor f T_A D).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, v} f).obj
        (tensorComplex.{uR, max uA v} K L)) := by
  have := D.comparison_isIso_of_kFlat K hK
  have := D.comparison_isIso_of_kFlat L hL
  exact (CategoryTheory.Functor.uncurry.obj T_A.tensor).mapIso
      ((asIso (D.comparison.app K)).prod (asIso (D.comparison.app L))) ≪≫
    T_A.comparison _ _ (isKFlat_extendScalars f K hK) (isKFlat_extendScalars f L hL) ≪≫
    DerivedCategory.Q.mapIso (tensorComplexExtendScalarsIso f K L)

/-- On a pair of K-flat models, tensoring over `R` and then base changing is computed by the
base change of the ordinary total tensor product. -/
private def tensorBaseChangeModelRightIso (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uA v} K)
    (hL : CochainComplex.KFlat.{uR, max uA v} L) :
    (tensorBaseChangeFunctor f T_R D).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj ((extensionOfScalarsCochain.{uR, uA, v} f).obj
        (tensorComplex.{uR, max uA v} K L)) := by
  have := D.comparison_isIso_of_kFlat _ (isKFlat_tensor K L hK hL)
  exact D.functor.mapIso (T_R.comparison K L hK hL) ≪≫ asIso (D.comparison.app _)

/-- The comparison of the two constructions on a pair of K-flat models, obtained from the
tensor base-change isomorphism of total complexes. -/
private def tensorBaseChangeModelIso (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uA v} K)
    (hL : CochainComplex.KFlat.{uR, max uA v} L) :
    (baseChangedTensorFunctor f T_A D).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (tensorBaseChangeFunctor f T_R D).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  tensorBaseChangeModelLeftIso f T_A D K L hK hL ≪≫
    (tensorBaseChangeModelRightIso f T_R D K L hK hL).symm

/-- The right-hand model comparison is natural in the pair of K-flat models. -/
private lemma tensorBaseChangeModelRightIso_naturality (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f)
    {K K' L L' : CochainComplex (ModuleCat.{max uR uA v} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (hK : CochainComplex.KFlat.{uR, max uA v} K)
    (hK' : CochainComplex.KFlat.{uR, max uA v} K')
    (hL : CochainComplex.KFlat.{uR, max uA v} L)
    (hL' : CochainComplex.KFlat.{uR, max uA v} L') :
    (tensorBaseChangeFunctor f T_R D).map
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) ≫
        (tensorBaseChangeModelRightIso f T_R D K' L' hK' hL').hom =
      (tensorBaseChangeModelRightIso f T_R D K L hK hL).hom ≫
        DerivedCategory.Q.map ((extensionOfScalarsCochain.{uR, uA, v} f).map
          (HomologicalComplex.mapBifunctorMap a b
            (moduleTensor.{uR, max uA v} R) (.up ℤ))) := by
  let t := HomologicalComplex.mapBifunctorMap a b
    (moduleTensor.{uR, max uA v} R) (.up ℤ)
  have ht : (CategoryTheory.Functor.uncurry.obj T_R.tensor).map
      (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) ≫
      (T_R.comparison K' L' hK' hL').hom =
    (T_R.comparison K L hK hL).hom ≫ DerivedCategory.Q.map t := by
    simpa only [CategoryTheory.Functor.uncurry_obj_map, Category.assoc] using
      T_R.comparison_naturality a b hK hK' hL hL'
  have hd : D.functor.map (DerivedCategory.Q.map t) ≫ D.comparison.app _ =
      D.comparison.app _ ≫ DerivedCategory.Q.map
        ((extensionOfScalarsCochain.{uR, uA, v} f).map t) := D.comparison.naturality t
  show D.functor.map ((CategoryTheory.Functor.uncurry.obj T_R.tensor).map
      (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b))) ≫
      (D.functor.map (T_R.comparison K' L' hK' hL').hom ≫ D.comparison.app _) =
    (D.functor.map (T_R.comparison K L hK hL).hom ≫ D.comparison.app _) ≫
      DerivedCategory.Q.map ((extensionOfScalarsCochain.{uR, uA, v} f).map t)
  rw [← D.functor.map_comp_assoc, ht, D.functor.map_comp_assoc]
  simpa only [Category.assoc] using
    congrArg (fun z => D.functor.map (T_R.comparison K L hK hL).hom ≫ z) hd

/-- The left-hand model comparison is natural in the pair of K-flat models. -/
private lemma tensorBaseChangeModelLeftIso_naturality (f : R →+* A)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f)
    {K K' L L' : CochainComplex (ModuleCat.{max uR uA v} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (hK : CochainComplex.KFlat.{uR, max uA v} K)
    (hK' : CochainComplex.KFlat.{uR, max uA v} K')
    (hL : CochainComplex.KFlat.{uR, max uA v} L)
    (hL' : CochainComplex.KFlat.{uR, max uA v} L') :
    (baseChangedTensorFunctor f T_A D).map
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) ≫
        (tensorBaseChangeModelLeftIso f T_A D K' L' hK' hL').hom =
      (tensorBaseChangeModelLeftIso f T_A D K L hK hL).hom ≫
        DerivedCategory.Q.map ((extensionOfScalarsCochain.{uR, uA, v} f).map
          (HomologicalComplex.mapBifunctorMap a b
            (moduleTensor.{uR, max uA v} R) (.up ℤ))) := by
  let E := extensionOfScalarsCochain.{uR, uA, v} f
  let U := CategoryTheory.Functor.uncurry.obj T_A.tensor
  let t := HomologicalComplex.mapBifunctorMap a b
    (moduleTensor.{uR, max uA v} R) (.up ℤ)
  let α := CategoryTheory.Prod.mkHom (D.functor.map (DerivedCategory.Q.map a))
    (D.functor.map (DerivedCategory.Q.map b))
  let β := CategoryTheory.Prod.mkHom (DerivedCategory.Q.map (E.map a))
    (DerivedCategory.Q.map (E.map b))
  let δ (P Q : CochainComplex (ModuleCat.{max uR uA v} R) ℤ) :=
    CategoryTheory.Prod.mkHom (D.comparison.app P) (D.comparison.app Q)
  have hd : α ≫ δ K' L' = δ K L ≫ β :=
    Prod.ext (D.comparison.naturality a) (D.comparison.naturality b)
  let c := T_A.comparison (E.obj K) (E.obj L)
    (isKFlat_extendScalars f K hK) (isKFlat_extendScalars f L hL)
  let c' := T_A.comparison (E.obj K') (E.obj L')
    (isKFlat_extendScalars f K' hK') (isKFlat_extendScalars f L' hL')
  let t' := HomologicalComplex.mapBifunctorMap (E.map a) (E.map b)
    (moduleTensor.{uA, max uR v} A) (.up ℤ)
  have ht : U.map β ≫ c'.hom = c.hom ≫ DerivedCategory.Q.map t' := by
    simpa only [U, β, c, c', t', CategoryTheory.Functor.uncurry_obj_map,
      CategoryTheory.Prod.mkHom, Category.assoc] using
      T_A.comparison_naturality (E.map a) (E.map b)
        (isKFlat_extendScalars f K hK) (isKFlat_extendScalars f K' hK')
        (isKFlat_extendScalars f L hL) (isKFlat_extendScalars f L' hL')
  have he : DerivedCategory.Q.map t' ≫
      DerivedCategory.Q.map (tensorComplexExtendScalarsIso f K' L').hom =
    DerivedCategory.Q.map (tensorComplexExtendScalarsIso f K L).hom ≫
      DerivedCategory.Q.map (E.map t) := by
    rw [← DerivedCategory.Q.map_comp, tensorComplexExtendScalarsIso_naturality f a b,
      DerivedCategory.Q.map_comp]
  show U.map α ≫ (U.map (δ K' L') ≫ c'.hom ≫
      DerivedCategory.Q.map (tensorComplexExtendScalarsIso f K' L').hom) =
    (U.map (δ K L) ≫ c.hom ≫
      DerivedCategory.Q.map (tensorComplexExtendScalarsIso f K L).hom) ≫
      DerivedCategory.Q.map (E.map t)
  rw [← U.map_comp_assoc, hd, U.map_comp_assoc, reassoc_of% ht, he]
  simp only [Category.assoc]

/-- Pairs of K-flat objects of the homotopy category. -/
private abbrev kFlatModelPairs (R : Type uR) [CommRing R] :=
  (kFlatModels.{uR, v} R).FullSubcategory × (kFlatModels.{uR, v} R).FullSubcategory

/-- Localization on pairs of K-flat objects. -/
private abbrev kFlatModelPairsQ (R : Type uR) [CommRing R] :=
  (kFlatQ.{uR, v} R).prod (kFlatQ.{uR, v} R)

/-- Pairs of quasi-isomorphisms between K-flat objects. -/
private abbrev kFlatModelPairsW (R : Type uR) [CommRing R] :=
  (kFlatW.{uR, v} R).prod (kFlatW.{uR, v} R)

/-- Pairs of K-flat objects localize to pairs of objects of the derived category. -/
private lemma kFlatModelPairsQ_isLocalization (R : Type uR) [CommRing R] :
    (kFlatModelPairsQ.{uR, v} R).IsLocalization (kFlatModelPairsW.{uR, v} R) := by
  have := kFlatQ_isLocalization.{uR, v} R
  infer_instance

/-- A pair of K-flat objects is isomorphic to the pair of localizations of its two complexes. -/
private def kFlatModelPairsIso {R : Type uR} [CommRing R] (X : kFlatModelPairs.{uR, v} R) :
    (kFlatModelPairsQ.{uR, v} R).obj X ≅
      (DerivedCategory.Q.obj X.1.obj.as, DerivedCategory.Q.obj X.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso (ModuleCat.{max uR v} R)).app X.1.obj.as).prod
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max uR v} R)).app X.2.obj.as)

/-- That identification of pairs is natural. -/
private lemma kFlatModelPairsIso_naturality {R : Type uR} [CommRing R]
    {X Y : kFlatModelPairs.{uR, v} R} (g : X ⟶ Y) :
    (kFlatModelPairsQ.{uR, v} R).map g ≫ (kFlatModelPairsIso Y).hom =
      (kFlatModelPairsIso X).hom ≫
        CategoryTheory.Prod.mkHom (DerivedCategory.Q.map g.1.hom.out)
          (DerivedCategory.Q.map g.2.hom.out) := by
  have key : ∀ {X Y : (kFlatModels.{uR, v} R).FullSubcategory} (g : X ⟶ Y),
      DerivedCategory.Qh.map g.hom ≫
          (DerivedCategory.quotientCompQhIso _).hom.app Y.obj.as =
        (DerivedCategory.quotientCompQhIso _).hom.app X.obj.as ≫
          DerivedCategory.Q.map g.hom.out := fun g => by
    simpa only [CategoryTheory.Functor.comp_map, HomotopyCategory.quotient_map_out] using
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max uR v} R)).hom.naturality g.hom.out
  exact Prod.ext (key g.1) (key g.2)

universe v₁ v₂ u₁ u₂
/-- Naturality of a transformation transported along isomorphisms of the two functors. -/
private lemma naturality_transport {C : Type u₁} {E : Type u₂}
    [Category.{v₁} C] [Category.{v₂} E]
    (F G : C ⥤ E) {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y')
    (a : F.obj X' ≅ G.obj X') (b : F.obj Y' ≅ G.obj Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (hf : f ≫ eY.hom = eX.hom ≫ g)
    (hg : F.map g ≫ b.hom = a.hom ≫ G.map g) :
    F.map f ≫ (F.mapIso eY ≪≫ b ≪≫ (G.mapIso eY).symm).hom =
      (F.mapIso eX ≪≫ a ≪≫ (G.mapIso eX).symm).hom ≫ G.map f := by
  have hgi : eX.inv ≫ f = g ≫ eY.inv := by
    apply (cancel_mono eY.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hf, Iso.inv_hom_id_assoc]
  dsimp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, CategoryTheory.Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hf, F.map_comp_assoc, reassoc_of% hg]
  rw [← G.map_comp, ← G.map_comp, hgi]

/-- The comparison on pairs of K-flat models is natural, hence descends to the localization. -/
private lemma tensorBaseChangeModelIso_naturality (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f)
    {K K' L L' : CochainComplex (ModuleCat.{max uR uA v} R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (hK : CochainComplex.KFlat.{uR, max uA v} K)
    (hK' : CochainComplex.KFlat.{uR, max uA v} K')
    (hL : CochainComplex.KFlat.{uR, max uA v} L)
    (hL' : CochainComplex.KFlat.{uR, max uA v} L') :
    (baseChangedTensorFunctor f T_A D).map
        (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) ≫
        (tensorBaseChangeModelIso f T_R T_A D K' L' hK' hL').hom =
      (tensorBaseChangeModelIso f T_R T_A D K L hK hL).hom ≫
        (tensorBaseChangeFunctor f T_R D).map
          (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) := by
  apply (cancel_mono (tensorBaseChangeModelRightIso f T_R D K' L' hK' hL').hom).1
  dsimp only [tensorBaseChangeModelIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tensorBaseChangeModelRightIso_naturality f T_R D a b hK hK' hL hL',
    Iso.inv_hom_id_assoc]
  exact tensorBaseChangeModelLeftIso_naturality f T_A D a b hK hK' hL hL'

/-- The comparison of the two constructions, as an isomorphism of functors on pairs of K-flat
models. -/
private def tensorBaseChangeModelsIso (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f) :
    kFlatModelPairsQ.{uR, max uA v} R ⋙ baseChangedTensorFunctor f T_A D ≅
      kFlatModelPairsQ.{uR, max uA v} R ⋙ tensorBaseChangeFunctor f T_R D :=
  NatIso.ofComponents (fun X =>
    (baseChangedTensorFunctor f T_A D).mapIso (kFlatModelPairsIso X) ≪≫
      tensorBaseChangeModelIso f T_R T_A D X.1.obj.as X.2.obj.as
        X.1.property X.2.property ≪≫
      ((tensorBaseChangeFunctor f T_R D).mapIso (kFlatModelPairsIso X)).symm) (by
    intro X Y g
    exact naturality_transport (baseChangedTensorFunctor f T_A D)
      (tensorBaseChangeFunctor f T_R D) (kFlatModelPairsIso X) (kFlatModelPairsIso Y)
      (tensorBaseChangeModelIso f T_R T_A D X.1.obj.as X.2.obj.as X.1.property X.2.property)
      (tensorBaseChangeModelIso f T_R T_A D Y.1.obj.as Y.2.obj.as Y.1.property Y.2.property)
      ((kFlatModelPairsQ.{uR, max uA v} R).map g) _ (kFlatModelPairsIso_naturality g)
      (tensorBaseChangeModelIso_naturality f T_R T_A D g.1.hom.out g.2.hom.out
        X.1.property Y.1.property X.2.property Y.2.property))

/-- The derived base-change isomorphism, obtained by descending the comparison on pairs of
K-flat models through the localization. -/
private def tensorBaseChangeNatIso (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f) :
    baseChangedTensorFunctor f T_A D ≅ tensorBaseChangeFunctor f T_R D := by
  haveI := kFlatModelPairsQ_isLocalization.{uR, max uA v} R
  exact Localization.liftNatIso (kFlatModelPairsQ.{uR, max uA v} R)
    (kFlatModelPairsW.{uR, max uA v} R) _ _ _ _ (tensorBaseChangeModelsIso f T_R T_A D)

/-- The component of a transformation transported along isomorphisms of the two functors. -/
private lemma natTrans_app_of_transport {C : Type u₁} {E : Type u₂}
    [Category.{v₁} C] [Category.{v₂} E]
    (F G : C ⥤ E) (τ : F ⟶ G) {X Y : C} (e : X ≅ Y)
    (a : F.obj Y ⟶ G.obj Y)
    (h : τ.app X = F.map e.hom ≫ a ≫ G.map e.inv) : τ.app Y = a := by
  apply (cancel_epi (F.map e.hom)).1
  rw [τ.naturality, h]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The derived base-change isomorphism evaluated at a pair of K-flat representatives is the
model comparison. -/
private lemma tensorBaseChangeNatIso_hom_app (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f)
    (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max uA v} K)
    (hL : CochainComplex.KFlat.{uR, max uA v} L) :
    (tensorBaseChangeNatIso f T_R T_A D).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (tensorBaseChangeModelIso f T_R T_A D K L hK hL).hom := by
  have := kFlatModelPairsQ_isLocalization.{uR, max uA v} R
  let X : kFlatModelPairs.{uR, max uA v} R :=
    (⟨(HomotopyCategory.quotient _ _).obj K, hK⟩,
      ⟨(HomotopyCategory.quotient _ _).obj L, hL⟩)
  apply natTrans_app_of_transport _ _ _ (kFlatModelPairsIso X)
  show (Localization.liftNatTrans _ _ _ _ _ _
      (tensorBaseChangeModelsIso f T_R T_A D).hom).app
      ((kFlatModelPairsQ.{uR, max uA v} R).obj X) = _
  rw [Localization.liftNatTrans_app]
  show 𝟙 _ ≫ ((baseChangedTensorFunctor f T_A D).mapIso (kFlatModelPairsIso X) ≪≫
      tensorBaseChangeModelIso f T_R T_A D K L hK hL ≪≫
      ((tensorBaseChangeFunctor f T_R D).mapIso (kFlatModelPairsIso X)).symm).hom ≫
      𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv]

/-- Scalar extension commutes naturally with derived tensor products, with its prescribed
comparison on K-flat complexes. -/
private noncomputable def derivedExtensionScalarsTensorIsoOfKFlatModels (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f) :
    DerivedExtensionScalarsTensorIso f T_R T_A D := by
  refine { iso := tensorBaseChangeNatIso f T_R T_A D, comparison := ?_ }
  intro K L hK hL
  refine ⟨isKFlat_extendScalars f K hK, isKFlat_extendScalars f L hL,
    tensorComplexExtendScalarsIso f K L,
    tensorComplexExtendScalarsIso_normalized f K L, ?_⟩
  rw [tensorBaseChangeNatIso_hom_app f T_R T_A D K L hK hL]
  have he : (tensorBaseChangeModelLeftIso f T_A D K L hK hL).hom =
      (tensorBaseChangeModelIso f T_R T_A D K L hK hL).hom ≫
        (tensorBaseChangeModelRightIso f T_R D K L hK hL).hom := by
    simp only [tensorBaseChangeModelIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [tensorBaseChangeModelLeftIso, tensorBaseChangeModelRightIso,
    Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.prod_hom, asIso_hom,
    CategoryTheory.Functor.uncurry_obj_map, CategoryTheory.Prod.mkHom,
    Category.assoc, baseChangedTensorFunctor, CategoryTheory.Functor.comp_obj,
    CategoryTheory.Functor.prod_obj, extensionOfScalarsCochain,
    CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral,
    CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex] using he

end Construction

section Consequences

universe u uR uA v

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]

/-- The canonical base-change isomorphism
`(K ⊗ᴸ[R] A) ⊗ᴸ[A] (L ⊗ᴸ[R] A) ≅ (K ⊗ᴸ[R] L) ⊗ᴸ[R] A` in `D(A)`, natural in
`K, L ∈ D(R)` and represented on K-flat complexes by standard tensor base change. -/
@[stacks 068I, no_expose]
public noncomputable def derivedExtensionScalarsTensorIso (f : R →+* A)
    (T_R : DerivedTensorProductGeneral.{uR, max uA v} R)
    (T_A : DerivedTensorProductGeneral.{uA, max uR v} A)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.{uR, v, uA} f) :
    DerivedExtensionScalarsTensorIso f T_R T_A D :=
  derivedExtensionScalarsTensorIsoOfKFlatModels f T_R T_A D


/-- Extension of scalars in a common module universe containing both rings. -/
public abbrev extensionScalars (f : R →+* A) :
    ModuleCat.{max uR uA v} R ⥤ ModuleCat.{max uR uA v} A :=
  ModuleCat.extendScalars f

public noncomputable instance (f : R →+* A) :
    (extensionScalars.{uR, uA, v} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uA} f).isLeftAdjoint

public instance (f : R →+* A) : (extensionScalars.{uR, uA, v} f).Additive :=
  CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _ (by
    change PreservesFiniteColimits _
    infer_instance)

/-- Extension along a flat ring homomorphism preserves homology in any module universe. -/
public lemma extensionScalars_preservesHomology (f : R →+* A) (hf : f.Flat) :
    (extensionScalars.{uR, uA, v} f).PreservesHomology := by
  let := f.toAlgebra
  have : Module.Flat R A := hf
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact A hS

/-- Flat extension of scalars commutes with homology, naturally in the derived object.
This is obtained from the comparison of `totalDerivedExtensionScalars`: flatness makes
termwise extension exact, so its total left derived comparison is an isomorphism. In
particular, this construction does not use the tagged tensor comparison of Equation 068I. -/
public noncomputable def derivedExtensionScalarsHomologyIso
    (f : R →+* A) (hf : f.Flat) (i : ℤ) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, v} f).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max uR uA v} A) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max uR uA v} R) i ⋙
        ModuleCat.extendScalars f := by
  let F := extensionScalars.{uR, uA, v} f
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, v} f
  haveI : F.PreservesHomology := extensionScalars_preservesHomology f hf
  haveI : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  haveI : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{max uR uA v} R) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
      infer_instance)
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max uR uA v} A) (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{max uR uA v} R) (ComplexShape.up ℤ) i ⋙ F :=
    NatIso.ofComponents (fun K ↦ (K.sc i).mapHomologyIso F) (fun φ ↦
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) i).map φ) F)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA v} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (D.functor ⋙ DerivedCategory.homologyFunctor _ i))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor _ i ⋙ F)) _ _
    (Functor.isoWhiskerRight (asIso D.comparison) (DerivedCategory.homologyFunctor _ i) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors _ i) ≪≫ e ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors _ i).symm F)

/-- Localization as an endofunctor of modules, with the literal `LocalizedModule` carrier.
For `S = Submonoid.powers f`, its objects are the `LocalizedModule.Away f` of Tag 0H84. -/
public noncomputable def localizedModuleFunctor (S : Submonoid R) :
    ModuleCat.{max uR v} R ⥤ ModuleCat.{max uR v} R where
  obj M := ModuleCat.of R (LocalizedModule S M)
  map {M N} g := ModuleCat.ofHom (IsLocalizedModule.map S
    (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N) g.hom)
  map_id M := ModuleCat.hom_ext (IsLocalizedModule.map_id S _)
  map_comp {M N P} g h := by
    apply ModuleCat.hom_ext
    apply IsLocalizedModule.linearMap_ext S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S P)
    ext x
    change IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S P) (h.hom.comp g.hom) (LocalizedModule.mkLinearMap S M x) =
      IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N)
        (LocalizedModule.mkLinearMap S P) h.hom
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
          (LocalizedModule.mkLinearMap S N) g.hom (LocalizedModule.mkLinearMap S M x))
    simp only [IsLocalizedModule.map_apply, LinearMap.comp_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Extension to a localization, restricted back to the original ring, has the canonical
localized-module carrier. The scalar action is normalized to that of the ring homomorphism
so that the comparison agrees with `ModuleCat.extendScalars`. -/
public noncomputable def extensionScalarsLocalizedModuleIso (S : Submonoid R) [a : Algebra R A]
    [IsLocalization S A] (M : ModuleCat.{max uR uA v} R) :
    ((ModuleCat.extendScalars (algebraMap R A)) ⋙
      ModuleCat.restrictScalars (algebraMap R A)).obj M ≅
        ModuleCat.of R (LocalizedModule S M) := by
  have hloc : IsLocalization S A := inferInstance
  letI aRA : Algebra R A := (algebraMap R A).toAlgebra
  haveI : IsLocalization S A := by
    have ha : aRA = a := @toAlgebra_algebraMap R A _ _ a
    rwa [ha]
  exact (IsLocalizedModule.linearEquiv S (TensorProduct.mk R A M 1)
    (LocalizedModule.mkLinearMap S M)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- The extension/localization comparison is natural in the module. -/
@[ega "0 1.5.4" "first identification"]
public noncomputable def extensionScalarsLocalizedModuleNatIso (S : Submonoid R) [a : Algebra R A]
    [IsLocalization S A] :
    ModuleCat.extendScalars.{uR, uA, max uR uA v} (algebraMap R A) ⋙
      ModuleCat.restrictScalars (algebraMap R A) ≅
        localizedModuleFunctor.{uR, max uA v} S := by
  refine NatIso.ofComponents (extensionScalarsLocalizedModuleIso S) ?_
  intro M N g
  have hloc : IsLocalization S A := inferInstance
  let aRA : Algebra R A := (algebraMap R A).toAlgebra
  have : IsLocalization S A := by
    have ha : aRA = a := @toAlgebra_algebraMap R A _ _ a
    rwa [ha]
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.linearMap_ext S (TensorProduct.mk R A M 1)
    (LocalizedModule.mkLinearMap S N)
  ext x
  change (IsLocalizedModule.linearEquiv S (TensorProduct.mk R A N 1)
      (LocalizedModule.mkLinearMap S N)) (TensorProduct.mk R A N 1 (g.hom x)) =
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) g.hom
      ((IsLocalizedModule.linearEquiv S (TensorProduct.mk R A M 1)
        (LocalizedModule.mkLinearMap S M)) (TensorProduct.mk R A M 1 x))
  rw [IsLocalizedModule.linearEquiv_apply, IsLocalizedModule.linearEquiv_apply,
    IsLocalizedModule.map_apply]

/-- For any localization of a commutative ring, homology after total derived extension of
scalars is the localization of homology, naturally in the derived object. Restriction of
scalars expresses both sides as modules over the original ring. -/
public noncomputable def derivedExtensionScalarsLocalizationHomologyIso
    (S : Submonoid R) [Algebra R A] [IsLocalization S A] (i : ℤ) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, v}
        (algebraMap R A)).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max uR uA v} A) i ⋙
        ModuleCat.restrictScalars (algebraMap R A) ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max uR uA v} R) i ⋙
        localizedModuleFunctor.{uR, max uA v} S :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedExtensionScalarsHomologyIso.{uR, uA, v} (algebraMap R A)
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A S)) i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (extensionScalarsLocalizedModuleNatIso.{uR, uA, v} (A := A) S)

/-- The natural identification `Hⁱ(N ⊗ᴸ[R] R_f) ≅ (Hⁱ(N))_f` used in the proof of Tag 0H85.
The right side uses the literal `LocalizedModule.Away f` carrier from Tag 0H84. -/
public noncomputable def derivedExtensionScalarsAwayHomologyIso (f : R) (i : ℤ) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uR, v}
      (algebraMap R (Localization.Away f))).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max uR v} (Localization.Away f)) i ⋙
        ModuleCat.restrictScalars (algebraMap R (Localization.Away f)) ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max uR v} R) i ⋙
        localizedModuleFunctor.{uR, v} (Submonoid.powers f) :=
  derivedExtensionScalarsLocalizationHomologyIso (Submonoid.powers f) i
end Consequences

end CochainComplex.DerivedTensor

end
