module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TensorConstantModule
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverModules
public import StacksFrontier.Homology.TorAmplitude.FlatRepresentative

/-!
# The Čech complex of `N ⊗_A M` on objects with affine ambient scheme

Fix a global crystalline situation `(p, (S, I, γ), X)`, write `A = Γ(S, 𝒪_S)`, let `N` be a
quasi-coherent sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)` and `M` an `A`-module.  For a finite
family `D` of objects of `CRIS(X/S)` with chosen products `D_x = D_{x_0} × ⋯ × D_{x_n}` whose
ambient schemes are affine, the Čech complex of `Stacks.CechSite.FinalCover` of the sheaf
`N ⊗_A M` of `StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TensorConstantModule` is the
termwise tensor product with `M` of the Čech complex of `N`:

`Č(D, N ⊗_A M) ≅ Č(D, N) ⊗_A M`.

Its terms are the products `∏_x (N ⊗_A M)(D_x) = ∏_x N(D_x) ⊗_A M`, the sections of `N ⊗_A M`
over an object with affine ambient scheme being `N(T) ⊗_A M`, naturally; and a finite product
commutes with `- ⊗_A M`.

## Main definitions

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.TensorConstant`.

* `cechTensorConstantModuleIso` — **`Č(D, N ⊗_A M) ≅ Č(D, N) ⊗_A M`**, as complexes of
  `A`-modules (the Čech complexes being taken of the universe lifts to the module universe
  `u + 1`, as `Stacks.CechSite.FinalCover.cechFunctor` requires), with
  `cechTensorConstantModuleHomologyIso` the resulting isomorphism of cohomology.
* `cechIntTensorConstantModuleIso` — the same for the integer-graded Čech complex
  `Stacks.CechSite.FinalCover.cechIntFunctor`, in the form
  `StacksDraft.TorAmplitude.tensorComplex (Č(D, N)) M`, with
  `cechIntTensorConstantModuleHomologyIso` on cohomology.
* `cechTensorRestrictIso` — the identification, on the objects with affine ambient scheme, of the
  presheaf of `A`-modules of sections of `N ⊗_A M` with `T ↦ N(T) ⊗_A M`.
* `cochainComplexIsoOfRestrictIso` and `cochainComplexCompIso` — the two generalities used: the
  cochain complex of a presheaf on a simplicial formal coproduct depends only on the presheaf over
  the objects that occur, and commutes with an additive functor preserving the products that
  occur.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.TensorConstant

/-! ### Two generalities on the cochain complex of a simplicial formal coproduct -/

section Generalities

variable {C : Type*} [Category* C] {𝒜 : Type*} [Category* 𝒜] [HasProducts.{w} 𝒜]
  (E : SimplicialObject (FormalCoproduct.{w} C))

/-- The extension of a presheaf to formal coproducts is natural, along a morphism of formal
coproducts all of whose objects satisfy `Pr`, for an isomorphism of the restrictions of two
presheaves to `Pr`; the extension is written out. -/
theorem lift_comp_piMap (Pr : ObjectProperty C)
    {P Q : Cᵒᵖ ⥤ 𝒜} (e : Pr.ι.op ⋙ P ≅ Pr.ι.op ⋙ Q) {X Y : FormalCoproduct.{w} C}
    (hX : ∀ i, Pr (X.obj i)) (hY : ∀ j, Pr (Y.obj j)) (g : X ⟶ Y) :
    (Pi.lift fun i ↦ Pi.π (fun j ↦ P.obj (op (Y.obj j))) (g.f i) ≫ P.map (g.φ i).op) ≫
        Limits.Pi.map (f := fun i ↦ P.obj (op (X.obj i))) (g := fun i ↦ Q.obj (op (X.obj i)))
          (fun i ↦ (e.app (op ⟨X.obj i, hX i⟩)).hom) =
      Limits.Pi.map (f := fun j ↦ P.obj (op (Y.obj j))) (g := fun j ↦ Q.obj (op (Y.obj j)))
          (fun j ↦ (e.app (op ⟨Y.obj j, hY j⟩)).hom) ≫
        Pi.lift fun i ↦ Pi.π (fun j ↦ Q.obj (op (Y.obj j))) (g.f i) ≫ Q.map (g.φ i).op := by
  refine Pi.hom_ext _ _ fun i ↦ ?_
  simp only [Category.assoc, Pi.map_π, Pi.lift_π, Pi.lift_π_assoc, Pi.map_π_assoc]
  exact congrArg (fun t ↦ Pi.π (fun j ↦ P.obj (op (Y.obj j))) (g.f i) ≫ t)
    (e.hom.naturality (ObjectProperty.homMk (X := ⟨_, hX i⟩) (Y := ⟨_, hY (g.f i)⟩)
      (g.φ i)).op)

/-- The isomorphism of products of the values of two presheaves at the objects of a formal
coproduct, all satisfying `Pr`, induced by an isomorphism of their restrictions to `Pr`. -/
def piMapIsoOfRestrictIso (Pr : ObjectProperty C)
    {P Q : Cᵒᵖ ⥤ 𝒜} (e : Pr.ι.op ⋙ P ≅ Pr.ι.op ⋙ Q) {X : FormalCoproduct.{w} C}
    (hX : ∀ i, Pr (X.obj i)) :
    (∏ᶜ fun i ↦ P.obj (op (X.obj i))) ≅ ∏ᶜ fun i ↦ Q.obj (op (X.obj i)) where
  hom := Limits.Pi.map (f := fun i ↦ P.obj (op (X.obj i))) (g := fun i ↦ Q.obj (op (X.obj i)))
    fun i ↦ (e.app (op ⟨X.obj i, hX i⟩)).hom
  inv := Limits.Pi.map (f := fun i ↦ Q.obj (op (X.obj i))) (g := fun i ↦ P.obj (op (X.obj i)))
    fun i ↦ (e.app (op ⟨X.obj i, hX i⟩)).inv
  hom_inv_id := Pi.hom_ext _ _ fun i ↦ by simp
  inv_hom_id := Pi.hom_ext _ _ fun i ↦ by simp

/-- **The cosimplicial object of a presheaf on a simplicial formal coproduct only depends on the
presheaf over the objects that occur**: if all the objects of the formal coproducts `E_n` satisfy
`Pr`, an isomorphism between the restrictions of two presheaves to `Pr` induces an isomorphism of
their cosimplicial objects. -/
def cosimplicialIsoOfRestrictIso (Pr : ObjectProperty C)
    (hE : ∀ (n : SimplexCategoryᵒᵖ) (i : (E.obj n).I), Pr ((E.obj n).obj i))
    {P Q : Cᵒᵖ ⥤ 𝒜} (e : Pr.ι.op ⋙ P ≅ Pr.ι.op ⋙ Q) :
    (FormalCoproduct.cosimplicialObjectFunctor E).obj P ≅
      (FormalCoproduct.cosimplicialObjectFunctor E).obj Q :=
  NatIso.ofComponents (fun n ↦ piMapIsoOfRestrictIso Pr e (X := E.obj (op n)) (hE (op n)))
    fun {n m} f ↦
    lift_comp_piMap Pr e (hE (op m)) (hE (op n)) (E.map f.op)

/-- `cosimplicialIsoOfRestrictIso` on the cochain complexes. -/
def cochainComplexIsoOfRestrictIso [Preadditive 𝒜] (Pr : ObjectProperty C)
    (hE : ∀ (n : SimplexCategoryᵒᵖ) (i : (E.obj n).I), Pr ((E.obj n).obj i))
    {P Q : Cᵒᵖ ⥤ 𝒜} (e : Pr.ι.op ⋙ P ≅ Pr.ι.op ⋙ Q) :
    (FormalCoproduct.cochainComplexFunctor E).obj P ≅
      (FormalCoproduct.cochainComplexFunctor E).obj Q :=
  (AlgebraicTopology.alternatingCofaceMapComplex 𝒜).mapIso (cosimplicialIsoOfRestrictIso E Pr hE e)

variable {𝒜' : Type*} [Category* 𝒜'] [HasProducts.{w} 𝒜'] (F : 𝒜 ⥤ 𝒜')

/-- The extension of a presheaf to formal coproducts commutes with a functor `F`, through the
comparison maps of products; the extensions are written out. -/
theorem map_lift_comp_piComparison (P : Cᵒᵖ ⥤ 𝒜)
    {X Y : FormalCoproduct.{w} C} (g : X ⟶ Y) :
    F.map (Pi.lift fun i ↦ Pi.π (fun j ↦ P.obj (op (Y.obj j))) (g.f i) ≫ P.map (g.φ i).op) ≫
        piComparison F (fun i ↦ P.obj (op (X.obj i))) =
      piComparison F (fun j ↦ P.obj (op (Y.obj j))) ≫
        Pi.lift fun i ↦ Pi.π (fun j ↦ F.obj (P.obj (op (Y.obj j)))) (g.f i) ≫
          F.map (P.map (g.φ i).op) := by
  refine Pi.hom_ext _ _ fun i ↦ ?_
  simp only [Category.assoc, piComparison_comp_π, Pi.lift_π, piComparison_comp_π_assoc,
    ← Functor.map_comp]

/-- **A functor preserving the products that occur commutes with the cosimplicial object of a
presheaf on a simplicial formal coproduct.** -/
def cosimplicialCompIso
    (hF : ∀ n : SimplexCategory, PreservesLimitsOfShape (Discrete (E.obj (op n)).I) F)
    (P : Cᵒᵖ ⥤ 𝒜) :
    (FormalCoproduct.cosimplicialObjectFunctor E).obj P ⋙ F ≅
      (FormalCoproduct.cosimplicialObjectFunctor E).obj (P ⋙ F) :=
  NatIso.ofComponents (fun n ↦
      haveI : PreservesLimit (Discrete.functor fun i ↦ P.obj (op ((E.obj (op n)).obj i))) F :=
        (hF n).preservesLimit
      PreservesProduct.iso F fun i ↦ P.obj (op ((E.obj (op n)).obj i)))
    fun {_ _} f ↦ map_lift_comp_piComparison F P (E.map f.op)

/-- An additive functor commutes with the alternating coface map complex. -/
def mapAlternatingCofaceMapComplexIso [Preadditive 𝒜] [Preadditive 𝒜'] [F.Additive]
    (X : CosimplicialObject 𝒜) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex 𝒜).obj X) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex 𝒜').obj (X ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j hij ↦ by
    subst hij
    simp [AlgebraicTopology.alternatingCofaceMapComplex,
      AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      Functor.map_sum]
    rfl

/-- **An additive functor preserving the products that occur commutes with the cochain complex of
a presheaf on a simplicial formal coproduct.** -/
def cochainComplexCompIso [Preadditive 𝒜] [Preadditive 𝒜'] [F.Additive]
    (hF : ∀ n : SimplexCategory, PreservesLimitsOfShape (Discrete (E.obj (op n)).I) F)
    (P : Cᵒᵖ ⥤ 𝒜) :
    (FormalCoproduct.cochainComplexFunctor E).obj (P ⋙ F) ≅
      (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((FormalCoproduct.cochainComplexFunctor E).obj P) :=
  (AlgebraicTopology.alternatingCofaceMapComplex 𝒜').mapIso (cosimplicialCompIso E F hF P).symm ≪≫
    (mapAlternatingCofaceMapComplexIso F _).symm

end Generalities

/-! ### The Čech complex of `N ⊗_A M` -/

section Cech

open Stacks.CechSite.FinalCover

variable {S : GlobalCrystallineSituation.{u}}
  (N : SheafOfModules.{u} (crystallineStructureSheaf S)) [N.IsQuasicoherentOnSite]
  (M : ModuleCat.{u} (BaseRing S))

/-- The sheaves of `𝒪_{X/S}`-modules at the module universe `u + 1` as presheaves of `A`-modules,
`Stacks.CechSite.FinalCover.basePresheaf` at the ring map `SmallSite.bigBaseRingHom`. -/
abbrev bigBasePresheaf (S : GlobalCrystallineSituation.{u}) :=
  basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (SmallSite.bigBaseRingHom S)

/-- The ring maps `A ⟶ Γ(T, 𝒪_T)` through which the Čech complexes of
`Stacks.CechSite.FinalCover` read the sections of a sheaf of `𝒪_{X/S}`-modules as `A`-modules are
the structure maps `baseMap`. -/
theorem ringCone_bigBaseRingHom (T : (Thickening S)ᵒᵖ) (a : BaseRing S) :
    ringCone (crystallineStructureSheaf S) (SmallSite.bigBaseRingHom S) T a = baseMap T.unop a :=
  rfl

/-- The sections of the universe lift of a sheaf of `𝒪_{X/S}`-modules over an object, as an
`A`-module through `SmallSite.bigBaseRingHom`, are its sections there. -/
def uliftBaseSectionsEquiv (G : SheafOfModules.{u} (crystallineStructureSheaf S))
    (T : Thickening S) :
    (((bigBasePresheaf S).obj
      ((SmallSite.bigModuleULift S).obj G)).obj (op T) : Type (u + 1)) ≃ₗ[BaseRing S]
        BaseSections G.val T where
  toFun x := x.down
  invFun x := ULift.up x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The identification of the values of `N ⊗_A M` with `N(T) ⊗_A M`, read on the universe
lifts as `A`-modules, at an object with affine ambient scheme.** -/
def cechTensorSectionsEquiv (B : BigAffineThickening S) :
    (((bigBasePresheaf S).obj
      ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M))).obj (op B.obj) :
        Type (u + 1)) ≃ₗ[BaseRing S]
      ((StacksDraft.TorAmplitude.tensorRightMixed M).obj
        (((bigBasePresheaf S).obj
          ((SmallSite.bigModuleULift S).obj N)).obj (op B.obj)) : Type (u + 1)) :=
  (uliftBaseSectionsEquiv _ B.obj).trans
    ((tensorConstantModuleBaseSectionsIso N M B.obj).toLinearEquiv.trans
      (TensorProduct.congr (uliftBaseSectionsEquiv N B.obj).symm (LinearEquiv.refl _ _)))

omit [N.IsQuasicoherentOnSite] in
/-- The universe lift of the map `N(T) ⊗_A M ⟶ N(T') ⊗_A M`. -/
theorem uliftTensor_tensorRestrict {T T' : Thickening S} (g : T' ⟶ T)
    (z : TensorSections N.val M T) :
    TensorProduct.congr (uliftBaseSectionsEquiv N T').symm (LinearEquiv.refl _ _)
        (tensorRestrict N.val M g z) =
      ((StacksDraft.TorAmplitude.tensorRightMixed M).map
        (((bigBasePresheaf S).obj ((SmallSite.bigModuleULift S).obj N)).map g.op)).hom
        (TensorProduct.congr (uliftBaseSectionsEquiv N T).symm (LinearEquiv.refl _ _) z) := by
  have h : (TensorProduct.congr (uliftBaseSectionsEquiv N T').symm
        (LinearEquiv.refl (BaseRing S) M)).toLinearMap.comp (tensorRestrict N.val M g) =
      ((StacksDraft.TorAmplitude.tensorRightMixed M).map
        (((bigBasePresheaf S).obj ((SmallSite.bigModuleULift S).obj N)).map g.op)).hom.comp
        (TensorProduct.congr (uliftBaseSectionsEquiv N T).symm
          (LinearEquiv.refl (BaseRing S) M)).toLinearMap :=
    TensorProduct.ext' fun _ _ ↦ rfl
  exact LinearMap.congr_fun h z

/-- `cechTensorSectionsEquiv` is natural in the objects with affine ambient scheme. -/
theorem cechTensorSectionsEquiv_naturality {B B' : BigAffineThickening S} (k : B' ⟶ B)
    (x : (((bigBasePresheaf S).obj
        ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M))).obj (op B.obj) :
          Type (u + 1))) :
    cechTensorSectionsEquiv N M B'
        ((((bigBasePresheaf S).obj
          ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M))).map k.hom.op).hom x) =
      ((StacksDraft.TorAmplitude.tensorRightMixed M).map
        (((bigBasePresheaf S).obj
          ((SmallSite.bigModuleULift S).obj N)).map k.hom.op)).hom
        (cechTensorSectionsEquiv N M B x) :=
  (congrArg (TensorProduct.congr (uliftBaseSectionsEquiv N B'.obj).symm (LinearEquiv.refl _ _))
    (tensorConstantModuleSectionsEquiv_restrict N M k.hom x.down)).trans
      (uliftTensor_tensorRestrict N M k.hom _)

/-- **The values of `N ⊗_A M` and of `T ↦ N(T) ⊗_A M` agree on the objects with affine ambient
scheme**, as presheaves of `A`-modules on `CRIS_aff(X/S)` read on the universe lifts. -/
def cechTensorRestrictIso :
    (IsAffineAmbient S).ι.op ⋙
        (bigBasePresheaf S).obj
          ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M)) ≅
      (IsAffineAmbient S).ι.op ⋙
        ((bigBasePresheaf S).obj
          ((SmallSite.bigModuleULift S).obj N) ⋙ StacksDraft.TorAmplitude.tensorRightMixed M) :=
  NatIso.ofComponents (fun B ↦ (cechTensorSectionsEquiv N M B.unop).toModuleIso) fun {B B'} k ↦ by
    ext x
    exact cechTensorSectionsEquiv_naturality N M k.unop x

variable {ι : Type} (D : ι → Thickening S)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]

/-- **The Čech complex of `N ⊗_A M` on a finite family of objects whose products have affine
ambient schemes is the termwise tensor product of the Čech complex of `N` with `M`**:

`Č(D, N ⊗_A M) ≅ Č(D, N) ⊗_A M`,

as complexes of `A`-modules, both sides read on the universe lifts to the module universe
`u + 1` of `Stacks.CechSite.FinalCover.cechFunctor`.  On the objects with affine ambient scheme
the sections of `N ⊗_A M` are `N(T) ⊗_A M`, naturally (`cechTensorRestrictIso`), the Čech terms
are finite products of such sections, and `- ⊗_A M` commutes with finite products. -/
def cechTensorConstantModuleIso [Finite ι]
    (hD : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsAffine (inter D x).thickening.target.scheme) :
    (cechFunctor.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (SmallSite.bigBaseRingHom S)
        D).obj ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M)) ≅
      ((StacksDraft.TorAmplitude.tensorRightMixed M).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
        ((cechFunctor.{0, u, u + 1, u, u} (crystallineStructureSheaf S)
          (SmallSite.bigBaseRingHom S) D).obj ((SmallSite.bigModuleULift S).obj N)) :=
  cochainComplexIsoOfRestrictIso (simplicialObject D) (IsAffineAmbient S)
      (fun n x ↦ hD _ x) (cechTensorRestrictIso N M) ≪≫
    cochainComplexCompIso (simplicialObject D)
      (StacksDraft.TorAmplitude.tensorRightMixed M :
        ModuleCat.{u + 1} (BaseRing S) ⥤ ModuleCat.{u + 1} (BaseRing S))
      (fun n ↦ by
        have : Finite ((simplicialObject D).obj (op n)).I := by
          change Finite (Fin (n.len + 1) → ι)
          infer_instance
        infer_instance) _

/-- **The cohomology of the Čech complex of `N ⊗_A M` is that of `Č(D, N) ⊗_A M`.** -/
def cechTensorConstantModuleHomologyIso [Finite ι]
    (hD : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsAffine (inter D x).thickening.target.scheme)
    (q : ℕ) :
    ((cechFunctor.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (SmallSite.bigBaseRingHom S)
        D).obj ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M))).homology q ≅
      (((StacksDraft.TorAmplitude.tensorRightMixed M).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
        ((cechFunctor.{0, u, u + 1, u, u} (crystallineStructureSheaf S)
          (SmallSite.bigBaseRingHom S) D).obj ((SmallSite.bigModuleULift S).obj N))).homology q :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso (cechTensorConstantModuleIso N M D hD)

/-- **The integer-graded Čech complex of `N ⊗_A M` is the termwise tensor product of that of `N`
with `M`**: `cechTensorConstantModuleIso` extended by zero to integer degrees, in the form of
`StacksDraft.TorAmplitude.tensorComplex`. -/
def cechIntTensorConstantModuleIso [Finite ι]
    (hD : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsAffine (inter D x).thickening.target.scheme) :
    (cechIntFunctor.{0, u, u + 1, u, u} (crystallineStructureSheaf S)
        (SmallSite.bigBaseRingHom S) D).obj
        ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M)) ≅
      StacksDraft.TorAmplitude.tensorComplex
        ((cechIntFunctor.{0, u, u + 1, u, u} (crystallineStructureSheaf S)
          (SmallSite.bigBaseRingHom S) D).obj ((SmallSite.bigModuleULift S).obj N)) M :=
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso (cechTensorConstantModuleIso N M D hD) ≪≫
    HomologicalComplex.mapHomologicalComplexExtendIso
      (StacksDraft.TorAmplitude.tensorRightMixed M :
        ModuleCat.{u + 1} (BaseRing S) ⥤ ModuleCat.{u + 1} (BaseRing S)) _
      ComplexShape.embeddingUpNat

/-- **The cohomology of the integer-graded Čech complex of `N ⊗_A M` is that of
`tensorComplex (Č(D, N)) M`.** -/
def cechIntTensorConstantModuleHomologyIso [Finite ι]
    (hD : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsAffine (inter D x).thickening.target.scheme)
    (q : ℤ) :
    ((cechIntFunctor.{0, u, u + 1, u, u} (crystallineStructureSheaf S)
        (SmallSite.bigBaseRingHom S) D).obj
        ((SmallSite.bigModuleULift S).obj (tensorConstantModule N M))).homology q ≅
      (StacksDraft.TorAmplitude.tensorComplex
        ((cechIntFunctor.{0, u, u + 1, u, u} (crystallineStructureSheaf S)
          (SmallSite.bigBaseRingHom S) D).obj ((SmallSite.bigModuleULift S).obj N)) M).homology q :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso (cechIntTensorConstantModuleIso N M D hD)

end Cech

end Crystalline.GlobalCrystallineSituation.TensorConstant

end
