module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# Mayer–Vietoris for an elementary distinguished square of algebraic spaces

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S`, let `P = U ×_X V` be its intersection and write `j_U`, `j_V` and `j_P` for the
three étale morphisms to `X`, `(-)|_Y` for restriction of modules along an étale morphism and
`j_{Y!}` for its left adjoint, extension by zero.  Stacks 08GV says that a sheaf of
`𝒪_X`-modules `F` sits in a short exact sequence

`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`

and that an object `E` of the unbounded derived category `D(𝒪_X)` sits in a distinguished
triangle

`j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V ⟶ E ⟶ (j_{P!}E|_P)[1]`.

The second part is deduced from the first exactly as in the source: the three functors
`j_{Y!}((-)|_Y)` are exact, so each is computed on `D(𝒪_X)` by applying it termwise to a
cochain complex representing `E`; the short exact sequences of part (1) at the terms of that
complex assemble to a short exact sequence of complexes, and the distinguished triangle is
the one attached to it.

## Main definitions

* `AlgebraicGeometry.Space.edsOpen`, `AlgebraicGeometry.Space.edsEtale` and
  `AlgebraicGeometry.Space.edsInter` are the open subspace, the étale algebraic space and the
  intersection `U ×_X V` of an elementary distinguished square, and
  `AlgebraicGeometry.Space.edsOpenHom`, `AlgebraicGeometry.Space.edsEtaleHom`,
  `AlgebraicGeometry.Space.edsFst`, `AlgebraicGeometry.Space.edsSnd` and
  `AlgebraicGeometry.Space.edsInterHom` are the morphisms between them.
* `CategoryTheory.Functor.biprodIsoOfAdditive` is the comparison identifying the image of a
  binary biproduct under an additive functor with the biproduct of the images.

## Main results

* `CategoryTheory.mem_distTriang_biprod_of_natural_shortExact`: for exact functors
  `Φ_P, Φ_U, Φ_V, Ψ` between abelian categories and natural transformations
  `Φ_P ⟶ Φ_U`, `Φ_P ⟶ Φ_V`, `Φ_U ⟶ Ψ`, `Φ_V ⟶ Ψ` whose Mayer–Vietoris short complex is
  short exact at every object, the derived transformations form a distinguished triangle at
  every object of the derived category.  This is the homological content of the passage from
  part (1) to part (2) of Stacks 08GV.
* `CategoryTheory.mem_distTriang_biprod_of_natural_shortExact_id`: the same when `Ψ` is the
  identity functor, so that the third term of the triangle is the object itself.
* `AlgebraicGeometry.Space.isEtale_edsOpenHom`,
  `AlgebraicGeometry.Space.isEtale_edsEtaleHom`, `AlgebraicGeometry.Space.isEtale_edsFst`,
  `AlgebraicGeometry.Space.isEtale_edsSnd` and
  `AlgebraicGeometry.Space.isEtale_edsInterHom`: the five morphisms of an elementary
  distinguished square and of its intersection are étale.
* `AlgebraicGeometry.Space.mem_distTriang_mayerVietoris`: the derived triangle of a
  Mayer–Vietoris short exact sequence of extensions by zero, read for an elementary
  distinguished square.

## Implementation notes

Restriction of modules along an étale morphism is
`AlgebraicGeometry.Space.etaleModulePullback`, the reading of Stacks 03LV of the inverse
image of modules as restriction of sections along postcomposition of étale charts, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero`.  Extension by zero is
not constructed here but enters as data: a functor together with an adjunction exhibiting it
as a left adjoint of restriction, which pins both the functor and the counit
`j_{Y!}(F|_Y) ⟶ F` up to a unique compatible isomorphism.  Its exactness — Stacks 03DJ — is
therefore also data: it is carried by the instance arguments `PreservesFiniteLimits`,
`PreservesFiniteColimits` and `Functor.Additive` on the three extension functors, and it is
what makes the derived functors of the three composites available at all.

The two maps out of the intersection are *not* constructed either: they are arbitrary natural
transformations `a` and `b`, and the short exactness of the resulting short complex enters as
the hypothesis `hMV`.  The deduction below is the source's own and uses nothing about the maps
beyond that exactness, which is why it is formulated at this generality; for the maps of the
square it is supplied by
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`, and the two clauses of Stacks 08GV
together are
`AlgebraicGeometry.Space.mayerVietoris_shortExact_and_mem_distTriang`.

The third term of the triangle is the object `E` itself rather than the value at `E` of the
derived functor of the identity: `CategoryTheory.Functor.mapDerivedCategoryIdIso` performs that
identification, and the second morphism of the triangle is composed with it.

The intersection is the fibre product of Stacks 02X2 and its morphism to `X` is the composite
through `U`; étaleness of the two projections is Stacks 03FU, étaleness of the composite is
Stacks 03FT, and étaleness of the open immersion is the comparison of Stacks 02YU with the
étale-chart definition.

## References

* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe w₁ w₂ v₁ v₂ u₁ u₂ u

namespace CategoryTheory

section Biprod

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D]

/-- An additive functor carries a binary biproduct to a binary biproduct: the comparison
built from the images of the two projections is inverse to the one built from the images of
the two inclusions. -/
noncomputable def Functor.biprodIsoOfAdditive (F : C ⥤ D) [F.Additive] (A B : C)
    [HasBinaryBiproduct A B] [HasBinaryBiproduct (F.obj A) (F.obj B)] :
    F.obj (A ⊞ B) ≅ F.obj A ⊞ F.obj B where
  hom := biprod.lift (F.map biprod.fst) (F.map biprod.snd)
  inv := biprod.desc (F.map biprod.inl) (F.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, assoc, biprod.lift_fst,
        biprod.lift_snd, ← F.map_comp, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst,
        biprod.inr_snd, comp_id, Functor.map_zero, CategoryTheory.Functor.map_id]

/-- The image under an additive functor of a map into a biproduct, read through the biproduct
comparison, is the map into the biproduct of the images of the two components. -/
@[reassoc]
theorem Functor.biprodIsoOfAdditive_hom_map_lift (F : C ⥤ D) [F.Additive] (A B : C)
    [HasBinaryBiproduct A B] [HasBinaryBiproduct (F.obj A) (F.obj B)] {X : C} (f : X ⟶ A)
    (g : X ⟶ B) :
    F.map (biprod.lift f g) ≫ (F.biprodIsoOfAdditive A B).hom =
      biprod.lift (F.map f) (F.map g) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;>
    simp only [Functor.biprodIsoOfAdditive, assoc, biprod.lift_fst, biprod.lift_snd,
      ← F.map_comp]

/-- The image under an additive functor of a map out of a biproduct, read through the
biproduct comparison, is the map out of the biproduct of the images of the two components. -/
@[reassoc]
theorem Functor.biprodIsoOfAdditive_inv_map_desc (F : C ⥤ D) [F.Additive] (A B : C)
    [HasBinaryBiproduct A B] [HasBinaryBiproduct (F.obj A) (F.obj B)] {X : C} (f : A ⟶ X)
    (g : B ⟶ X) :
    (F.biprodIsoOfAdditive A B).inv ≫ F.map (biprod.desc f g) =
      biprod.desc (F.map f) (F.map g) := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;>
    simp only [Functor.biprodIsoOfAdditive, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.inl_desc, biprod.inr_desc, ← F.map_comp]

end Biprod

section Derived

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]

/-- The functor induced on unbounded derived categories by the identity functor lifts, through
the localization, the identity on cochain complexes. -/
noncomputable instance Localization.liftingMapDerivedCategoryId :
    Localization.Lifting (DerivedCategory.Q (C := C₁))
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      ((𝟭 C₁).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (𝟭 (DerivedCategory C₁)) :=
  ⟨Iso.refl _⟩

variable {ΦP ΦU ΦV Ψ : C₁ ⥤ C₂}
  [ΦP.Additive] [PreservesFiniteLimits ΦP] [PreservesFiniteColimits ΦP]
  [ΦU.Additive] [PreservesFiniteLimits ΦU] [PreservesFiniteColimits ΦU]
  [ΦV.Additive] [PreservesFiniteLimits ΦV] [PreservesFiniteColimits ΦV]

/-- Let `Φ_P, Φ_U, Φ_V, Ψ : C₁ ⥤ C₂` be exact functors of abelian categories and let
`a : Φ_P ⟶ Φ_U`, `b : Φ_P ⟶ Φ_V`, `c_U : Φ_U ⟶ Ψ` and `c_V : Φ_V ⟶ Ψ` be natural
transformations such that

`0 ⟶ Φ_P M ⟶ Φ_U M ⊕ Φ_V M ⟶ Ψ M ⟶ 0`

is short exact for every object `M`, the maps being `(a, -b)` and `c_U + c_V`.  Then the
derived transformations fit, at every object `E` of the derived category of `C₁`, into a
distinguished triangle

`Φ_P E ⟶ Φ_U E ⊕ Φ_V E ⟶ Ψ E ⟶ (Φ_P E)[1]`

in the derived category of `C₂`. -/
theorem mem_distTriang_biprod_of_natural_shortExact [Ψ.Additive] [PreservesFiniteLimits Ψ]
    [PreservesFiniteColimits Ψ] (a : ΦP ⟶ ΦU) (b : ΦP ⟶ ΦV) (cU : ΦU ⟶ Ψ) (cV : ΦV ⟶ Ψ)
    (hzero : ∀ M, biprod.lift (a.app M) (-(b.app M)) ≫
      biprod.desc (cU.app M) (cV.app M) = 0)
    (hex : ∀ M, (ShortComplex.mk (biprod.lift (a.app M) (-(b.app M)))
      (biprod.desc (cU.app M) (cV.app M)) (hzero M)).ShortExact)
    (E : DerivedCategory C₁) :
    ∃ δ, Triangle.mk
        (biprod.lift ((NatTrans.mapDerivedCategory a).app E)
          (-((NatTrans.mapDerivedCategory b).app E)))
        (biprod.desc ((NatTrans.mapDerivedCategory cU).app E)
          ((NatTrans.mapDerivedCategory cV).app E)) δ ∈
      distTriang (DerivedCategory C₂) := by
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  let a' := (NatTrans.mapHomologicalComplex a (ComplexShape.up ℤ)).app K
  let b' := (NatTrans.mapHomologicalComplex b (ComplexShape.up ℤ)).app K
  let cU' := (NatTrans.mapHomologicalComplex cU (ComplexShape.up ℤ)).app K
  let cV' := (NatTrans.mapHomologicalComplex cV (ComplexShape.up ℤ)).app K
  let AU := (ΦU.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let AV := (ΦV.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let ev : ℤ → (CochainComplex C₂ ℤ ⥤ C₂) :=
    fun n => HomologicalComplex.eval C₂ (ComplexShape.up ℤ) n
  have e1 : ∀ n : ℤ, (ev n).map (biprod.lift a' (-b')) =
      biprod.lift (a.app (K.X n)) (-(b.app (K.X n))) ≫
        ((ev n).biprodIsoOfAdditive AU AV).inv := by
    intro n
    rw [Iso.eq_comp_inv, Functor.biprodIsoOfAdditive_hom_map_lift, (ev n).map_neg]
    rfl
  have e2 : ∀ n : ℤ, ((ev n).biprodIsoOfAdditive AU AV).inv ≫
      (ev n).map (biprod.desc cU' cV') =
      biprod.desc (cU.app (K.X n)) (cV.app (K.X n)) := fun n =>
    Functor.biprodIsoOfAdditive_inv_map_desc _ _ _ _ _
  have hz' : biprod.lift a' (-b') ≫ biprod.desc cU' cV' = 0 := by
    ext n
    show (ev n).map (biprod.lift a' (-b') ≫ biprod.desc cU' cV') = 0
    rw [(ev n).map_comp, e1 n, assoc, e2 n, hzero (K.X n)]
  have hS : (ShortComplex.mk _ _ hz').ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n => ?_)
    refine ShortComplex.shortExact_of_iso ?_ (hex (K.X n))
    refine ShortComplex.isoMk (Iso.refl _) ((ev n).biprodIsoOfAdditive AU AV).symm
      (Iso.refl _) ?_ ?_
    · simp only [Iso.refl_hom, id_comp, Iso.symm_hom]
      exact e1 n
    · simp only [Iso.refl_hom, comp_id, Iso.symm_hom]
      exact e2 n
  let iso : ∀ (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F],
      F.mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj K) :=
    fun F _ _ _ => F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app K
  have kk : ∀ {F G : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F]
      [PreservesFiniteColimits F] [G.Additive] [PreservesFiniteLimits G]
      [PreservesFiniteColimits G] (τ : F ⟶ G),
      (NatTrans.mapDerivedCategory τ).app E ≫ (iso G).hom =
        (iso F).hom ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := by
    intro F G _ _ _ _ _ _ τ
    have hn := (NatTrans.mapDerivedCategory τ).naturality e.inv
    have hq : (NatTrans.mapDerivedCategory τ).app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategoryFactors.hom.app K =
        F.mapDerivedCategoryFactors.hom.app K ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) := by
      rw [NatTrans.mapDerivedCategory_app_Q]
      simp
    simp only [iso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, assoc]
    rw [← hq, ← assoc, ← assoc, hn]
  have comm1 : biprod.lift ((NatTrans.mapDerivedCategory a).app E)
        (-((NatTrans.mapDerivedCategory b).app E)) ≫
      (biprod.mapIso (iso ΦU) (iso ΦV) ≪≫
        (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm).hom =
      (iso ΦP).hom ≫ DerivedCategory.Q.map (biprod.lift a' (-b')) := by
    rw [Iso.trans_hom, Iso.symm_hom, ← assoc, Iso.comp_inv_eq, assoc,
      Functor.biprodIsoOfAdditive_hom_map_lift, biprod.mapIso_hom]
    refine biprod.hom_ext _ _ ?_ ?_
    · simp only [assoc, biprod.map_fst, biprod.lift_fst_assoc]
      refine (kk a).trans ?_
      congr 1
      exact (biprod.lift_fst _ _).symm
    · simp only [assoc, biprod.map_snd, biprod.lift_snd_assoc, Functor.map_neg,
        Preadditive.neg_comp]
      rw [kk b, ← Preadditive.comp_neg]
      congr 1
      exact (biprod.lift_snd _ _).symm
  have comm2 : biprod.desc ((NatTrans.mapDerivedCategory cU).app E)
        ((NatTrans.mapDerivedCategory cV).app E) ≫ (iso Ψ).hom =
      (biprod.mapIso (iso ΦU) (iso ΦV) ≪≫
          (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm).hom ≫
        DerivedCategory.Q.map (biprod.desc cU' cV') := by
    simp only [Iso.trans_hom, Iso.symm_hom, assoc,
      Functor.biprodIsoOfAdditive_inv_map_desc, biprod.mapIso_hom]
    refine biprod.hom_ext' _ _ ?_ ?_
    · simp only [biprod.inl_desc_assoc, biprod.inl_desc, biprod.inl_map_assoc, kk cU]
      rfl
    · simp only [biprod.inr_desc_assoc, biprod.inr_desc, biprod.inr_map_assoc, kk cV]
      rfl
  have comm3 : ((iso Ψ).hom ≫ DerivedCategory.triangleOfSESδ hS ≫
        (shiftFunctor (DerivedCategory C₂) (1 : ℤ)).map (iso ΦP).inv) ≫
      (shiftFunctor (DerivedCategory C₂) (1 : ℤ)).map (iso ΦP).hom =
      (iso Ψ).hom ≫ DerivedCategory.triangleOfSESδ hS := by
    rw [assoc, assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      comp_id]
  exact ⟨_, isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ (iso ΦP) (biprod.mapIso (iso ΦU) (iso ΦV) ≪≫
      (DerivedCategory.Q.biprodIsoOfAdditive AU AV).symm) (iso Ψ) comm1 comm2 comm3)⟩

/-- The Mayer–Vietoris distinguished triangle of
`CategoryTheory.mem_distTriang_biprod_of_natural_shortExact` when the third functor is the
identity, so that the third term of the triangle is the object itself. -/
theorem mem_distTriang_biprod_of_natural_shortExact_id {ΨP ΨU ΨV : C₁ ⥤ C₁}
    [ΨP.Additive] [PreservesFiniteLimits ΨP] [PreservesFiniteColimits ΨP]
    [ΨU.Additive] [PreservesFiniteLimits ΨU] [PreservesFiniteColimits ΨU]
    [ΨV.Additive] [PreservesFiniteLimits ΨV] [PreservesFiniteColimits ΨV]
    (a : ΨP ⟶ ΨU) (b : ΨP ⟶ ΨV) (cU : ΨU ⟶ 𝟭 C₁) (cV : ΨV ⟶ 𝟭 C₁)
    (hzero : ∀ M, biprod.lift (a.app M) (-(b.app M)) ≫
      biprod.desc (cU.app M) (cV.app M) = 0)
    (hex : ∀ M, (ShortComplex.mk (biprod.lift (a.app M) (-(b.app M)))
      (biprod.desc (cU.app M) (cV.app M)) (hzero M)).ShortExact)
    (E : DerivedCategory C₁) :
    ∃ δ, Triangle.mk
        (biprod.lift ((NatTrans.mapDerivedCategory a).app E)
          (-((NatTrans.mapDerivedCategory b).app E)))
        (biprod.desc ((NatTrans.mapDerivedCategory cU).app E)
            ((NatTrans.mapDerivedCategory cV).app E) ≫
          (Functor.mapDerivedCategoryIdIso C₁).hom.app E) δ ∈
      distTriang (DerivedCategory C₁) := by
  obtain ⟨δ, hδ⟩ := mem_distTriang_biprod_of_natural_shortExact a b cU cV hzero hex E
  refine ⟨(Functor.mapDerivedCategoryIdIso C₁).inv.app E ≫ δ, ?_⟩
  refine isomorphic_distinguished _ hδ _ (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((Functor.mapDerivedCategoryIdIso C₁).app E).symm ?_ ?_ ?_)
  · simp
  · simp
  · simp

end Derived

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- The open subspace of an elementary distinguished square, as an algebraic space over the
base scheme. -/
def edsOpen : AlgebraicSpaces B S hS := ⟨Uo.toFunctor, hsq.isOpenSubspace.1⟩

/-- The étale algebraic space of an elementary distinguished square. -/
def edsEtale : AlgebraicSpaces B S hS := ⟨V, hsq.isAlgebraicSpace⟩

/-- The open immersion `j_U : U ⟶ X` of an elementary distinguished square. -/
def edsOpenHom : edsOpen B S hS hsq ⟶ W := ObjectProperty.homMk Uo.ι

/-- The étale morphism `j_V : V ⟶ X` of an elementary distinguished square. -/
def edsEtaleHom : edsEtale B S hS hsq ⟶ W := ObjectProperty.homMk fV

/-- The intersection `U ×_X V` of an elementary distinguished square, as the fibre product of
Stacks 02X2. -/
def edsInter : AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS (edsOpenHom B S hS hsq) (edsEtaleHom B S hS hsq)

/-- The first projection `U ×_X V ⟶ U` of an elementary distinguished square. -/
def edsFst : edsInter B S hS hsq ⟶ edsOpen B S hS hsq :=
  ObjectProperty.homMk (pullback.fst (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom)

/-- The second projection `U ×_X V ⟶ V` of an elementary distinguished square. -/
def edsSnd : edsInter B S hS hsq ⟶ edsEtale B S hS hsq :=
  ObjectProperty.homMk (pullback.snd (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom)

/-- The étale morphism `j_{U ×_X V} : U ×_X V ⟶ X` of an elementary distinguished square,
taken as the composite through the open subspace. -/
def edsInterHom : edsInter B S hS hsq ⟶ W := edsFst B S hS hsq ≫ edsOpenHom B S hS hsq

/-- The intersection of an elementary distinguished square is the fibre product of the open
subspace and the étale algebraic space over the ambient space. -/
theorem isPullback_edsInter :
    IsPullback (edsFst B S hS hsq) (edsSnd B S hS hsq) (edsOpenHom B S hS hsq)
      (edsEtaleHom B S hS hsq) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The open immersion of an elementary distinguished square is étale. -/
theorem isEtale_edsOpenHom : IsEtale B S hS (edsOpenHom B S hS hsq).hom :=
  isEtale_of_isOpenImmersion B S hS hsq.isOpenSubspace.2

/-- The étale morphism of an elementary distinguished square is étale. -/
theorem isEtale_edsEtaleHom : IsEtale B S hS (edsEtaleHom B S hS hsq).hom :=
  hsq.isEtale

/-- **Stacks 03FU** for an elementary distinguished square: the first projection of the
intersection is étale, being a base change of the étale morphism. -/
theorem isEtale_edsFst : IsEtale B S hS (edsFst B S hS hsq).hom :=
  isEtale_of_isPullback B S hS (edsSnd B S hS hsq) (edsFst B S hS hsq)
    (edsEtaleHom B S hS hsq) (edsOpenHom B S hS hsq) (isPullback_edsInter B S hS hsq).flip
    (isEtale_edsEtaleHom B S hS hsq)

/-- **Stacks 03FU** for an elementary distinguished square: the second projection of the
intersection is étale, being a base change of the open immersion. -/
theorem isEtale_edsSnd : IsEtale B S hS (edsSnd B S hS hsq).hom :=
  isEtale_of_isPullback B S hS (edsFst B S hS hsq) (edsSnd B S hS hsq)
    (edsOpenHom B S hS hsq) (edsEtaleHom B S hS hsq) (isPullback_edsInter B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq)

/-- **Stacks 03FT** for an elementary distinguished square: the morphism from the intersection
to the ambient algebraic space is étale. -/
theorem isEtale_edsInterHom : IsEtale B S hS (edsInterHom B S hS hsq).hom :=
  isEtale_comp B S hS (isEtale_edsFst B S hS hsq) (isEtale_edsOpenHom B S hS hsq)

end Square

section Triangle

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
  [HasSheafify (smallEtaleRingedSite B S hS W.1 W.2).J AddCommGrpCat.{u}]
  [(smallEtaleRingedSite B S hS W.1 W.2).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {shriekU : Modules.{u, u} B S hS (edsOpen B S hS hsq).1 (edsOpen B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekV : Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  {shriekP : Modules.{u, u} B S hS (edsInter B S hS hsq).1 (edsInter B S hS hsq).2 ⥤
    Modules.{u, u} B S hS W.1 W.2}
  (adjU : shriekU ⊣ etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
    (isEtale_edsOpenHom B S hS hsq))
  (adjV : shriekV ⊣ etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
    (isEtale_edsEtaleHom B S hS hsq))
  (adjP : shriekP ⊣ etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
    (isEtale_edsInterHom B S hS hsq))
  [shriekU.Additive] [PreservesFiniteLimits shriekU] [PreservesFiniteColimits shriekU]
  [shriekV.Additive] [PreservesFiniteLimits shriekV] [PreservesFiniteColimits shriekV]
  [shriekP.Additive] [PreservesFiniteLimits shriekP] [PreservesFiniteColimits shriekP]

/-- **The derived triangle of a Mayer–Vietoris short exact sequence of extensions by zero.**
Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` and let `P = U ×_X V`.  Write `(-)|_Y` for restriction of modules along an étale
morphism `j_Y : Y ⟶ X` and `j_{Y!}` for a left adjoint of it, extension by zero, with counit
`j_{Y!}(F|_Y) ⟶ F`.  Let `a : j_{P!}((-)|_P) ⟶ j_{U!}((-)|_U)` and
`b : j_{P!}((-)|_P) ⟶ j_{V!}((-)|_V)` be natural transformations for which

`0 ⟶ j_{P!}F|_P ⟶ j_{U!}F|_U ⊕ j_{V!}F|_V ⟶ F ⟶ 0`,

with maps `(a, -b)` and the sum of the two counits, is short exact for every sheaf of
`𝒪_X`-modules `F`.  Then every object `E` of the unbounded derived category `D(𝒪_X)` sits in a
distinguished triangle

`j_{P!}E|_P ⟶ j_{U!}E|_U ⊕ j_{V!}E|_V ⟶ E ⟶ (j_{P!}E|_P)[1]`,

whose first two maps are the derived transformations of `(a, -b)` and of the two counits.

For the comparisons of the square the short exactness holds, by
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`; Stacks 08GV itself is
`AlgebraicGeometry.Space.mayerVietoris_shortExact_and_mem_distTriang`. -/
theorem mem_distTriang_mayerVietoris
    (a : etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
        etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
          (isEtale_edsOpenHom B S hS hsq) ⋙ shriekU)
    (b : etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
          (isEtale_edsInterHom B S hS hsq) ⋙ shriekP ⟶
        etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
          (isEtale_edsEtaleHom B S hS hsq) ⋙ shriekV)
    (hzero : ∀ F, biprod.lift (a.app F) (-(b.app F)) ≫
      biprod.desc (adjU.counit.app F) (adjV.counit.app F) = 0)
    (hMV : ∀ F, (ShortComplex.mk (biprod.lift (a.app F) (-(b.app F)))
      (biprod.desc (adjU.counit.app F) (adjV.counit.app F)) (hzero F)).ShortExact)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    ∃ δ, Triangle.mk
        (biprod.lift ((NatTrans.mapDerivedCategory a).app E)
          (-((NatTrans.mapDerivedCategory b).app E)))
        (biprod.desc ((NatTrans.mapDerivedCategory adjU.counit).app E)
            ((NatTrans.mapDerivedCategory adjV.counit).app E) ≫
          (Functor.mapDerivedCategoryIdIso
            (Modules.{u, u} B S hS W.1 W.2)).hom.app E) δ ∈
      distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :=
  mem_distTriang_biprod_of_natural_shortExact_id a b adjU.counit adjV.counit hzero hMV E

end Triangle

end AlgebraicGeometry.Space

end
