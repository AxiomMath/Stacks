module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Glueing.HomSheafLocalization

/-!
# Push-pull along the localization at a semi-representable object

Let `(C, J)` be a small site and `K = {U i}` a semi-representable object of `C`. Restricting a
sheaf to the localized sites `C / U i` and pushing it forward again, one component at a time, is
the internal hom out of the sheafification of the semi-representable presheaf `F(K)` attached
to `K`:
`∏ i, j_{i,*} j_i^{-1} F ≅ SheafHom(F(K)^#, F)`, naturally in `F`.

The proof is the source's. Both sides are right adjoints: the right-hand side to
`G ↦ F(K)^# × G` by Stacks 0BWQ, and the left-hand side to the coproduct of the functors
`G ↦ U i^# × G` by Stacks 0D7X one component at a time. Sheafification preserves the coproduct
defining `F(K)`, and the product of right adjoints is right adjoint to the coproduct of the left
adjoints, so the two left adjoints agree and the right adjoints are canonically isomorphic.

## Main results

* `CategoryTheory.SemiRepresentable.localizationPushforwardPullbackNatIsoSheafHom`: the
  push-pull/internal-hom identification.

## Implementation notes

The source identifies sheaves on `C / K` with families of sheaves on the sites `C / U i`.
Accordingly, its object `j_* j^{-1} F` appears here as the product of the componentwise objects
`j_{i,*} j_i^{-1} F`, and the source's equality of sheaves is a categorical isomorphism, natural
in the sheaf.

## References

* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D7X](https://stacks.math.columbia.edu/tag/0D7X)
* [Stacks Project, Tag 0BWQ](https://stacks.math.columbia.edu/tag/0BWQ)
-/

@[expose] public section

namespace CategoryTheory.SemiRepresentable

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.OverShriek

universe u v w

variable {C : Type u} [SmallCategory C]

/-- A morphism out of a coproduct is a family of morphisms out of its summands. -/
noncomputable def coproductHomFamilyEquiv {I : Type u} {D : Type w}
    [Category.{v, w} D] (F : I → D) [HasCoproduct F] (Y : D) :
    (∐ F ⟶ Y) ≃ (∀ i, F i ⟶ Y) where
  toFun g i := Sigma.ι F i ≫ g
  invFun g := Sigma.desc g
  left_inv g := by ext i; simp
  right_inv g := by funext i; simp

/-- A morphism into a product is a family of morphisms into its factors. -/
noncomputable def productHomFamilyEquiv {I : Type u} {D : Type w}
    [Category.{v, w} D] (F : I → D) [HasProduct F] (X : D) :
    (X ⟶ ∏ᶜ F) ≃ (∀ i, X ⟶ F i) where
  toFun g i := g ≫ Pi.π F i
  invFun g := Pi.lift g
  left_inv g := by ext i; simp
  right_inv g := by funext i; simp

/-- The morphism out of a coproduct determined by a family restricts to each member of the family
on the corresponding summand. -/
@[simp] lemma coproductHomFamilyEquiv_symm_ι {I : Type u} {D : Type w}
    [Category.{v, w} D] (F : I → D) [HasCoproduct F] (Y : D)
    (g : ∀ i, F i ⟶ Y) (i : I) :
    Sigma.ι F i ≫ (coproductHomFamilyEquiv F Y).symm g = g i := Sigma.ι_desc _ _

/-- The morphism into a product determined by a family composes with each projection to the
corresponding member of the family. -/
@[simp] lemma productHomFamilyEquiv_symm_π {I : Type u} {D : Type w}
    [Category.{v, w} D] (F : I → D) [HasProduct F] (X : D)
    (g : ∀ i, X ⟶ F i) (i : I) :
    (productHomFamilyEquiv F X).symm g ≫ Pi.π F i = g i := Pi.lift_π _ _

/-- The `i`-th member of the family attached to a morphism into a product is its composite with
the `i`-th projection. -/
@[simp] lemma productHomFamilyEquiv_π {I : Type u} {D : Type w}
    [Category.{v, w} D] (F : I → D) [HasProduct F] (X : D)
    (g : X ⟶ ∏ᶜ F) (i : I) :
    productHomFamilyEquiv F X g i = g ≫ Pi.π F i := rfl

/-- The `i`-th member of the family attached to a morphism out of a coproduct is its restriction
to the `i`-th summand. -/
@[simp] lemma coproductHomFamilyEquiv_ι {I : Type u} {D : Type w}
    [Category.{v, w} D] (F : I → D) [HasCoproduct F] (Y : D)
    (g : ∐ F ⟶ Y) (i : I) :
    coproductHomFamilyEquiv F Y g i = Sigma.ι F i ≫ g := rfl

/-- The product of the internal-hom functors out of a family of sheaves is right adjoint to the
coproduct of the product functors with its members. -/
@[sga "3 I 1.7.3" "special case"]
noncomputable def localizationProductSheafHomAdjunction
    (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C)
    (G : K.I → Sheaf J (Type u)) :
    (Functor.pi' (fun i ↦ prod.functor.obj (G i)) ⋙ Sigma.functor K.I) ⊣
      (Functor.pi' (fun i ↦ SheafHomAdj.sheafHomFunctor (G i)) ⋙ Pi.functor K.I) := by
  let L : Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
    Functor.pi' (fun i ↦ prod.functor.obj (G i)) ⋙ Sigma.functor K.I
  let R : Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
    Functor.pi' (fun i ↦ SheafHomAdj.sheafHomFunctor (G i)) ⋙ Pi.functor K.I
  exact Adjunction.mkOfHomEquiv
    { homEquiv := fun X F =>
        (coproductHomFamilyEquiv (fun i ↦ (prod.functor.obj (G i)).obj X) F).trans
          ((Equiv.piCongrRight (fun i ↦
              (SheafHomAdj.prodSheafHomAdjunction (G i)).homEquiv X F)).trans
            (productHomFamilyEquiv
              (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F) X).symm)
      homEquiv_naturality_left_symm := by
        intro X' X F f g
        change X ⟶ ∏ᶜ (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F) at g
        apply Cofan.IsColimit.hom_ext (coproductIsCoproduct _)
        intro i
        change Sigma.ι (fun i ↦ (prod.functor.obj (G i)).obj X') i ≫
            ((coproductHomFamilyEquiv (fun i ↦ (prod.functor.obj (G i)).obj X') F).trans
              ((Equiv.piCongrRight (fun i ↦
                  (SheafHomAdj.prodSheafHomAdjunction (G i)).homEquiv X' F)).trans
                (productHomFamilyEquiv
                  (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F) X').symm)).symm (f ≫ g) =
          Sigma.ι (fun i ↦ (prod.functor.obj (G i)).obj X') i ≫
            Limits.Sigma.map (fun i ↦ (prod.functor.obj (G i)).map f) ≫
              ((coproductHomFamilyEquiv (fun i ↦ (prod.functor.obj (G i)).obj X) F).trans
              ((Equiv.piCongrRight (fun i ↦
                  (SheafHomAdj.prodSheafHomAdjunction (G i)).homEquiv X F)).trans
                  (productHomFamilyEquiv
                    (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F) X).symm)).symm g
        simp only [← Category.assoc, Limits.Sigma.ι_map]
        simp only [Category.assoc, coproductHomFamilyEquiv_symm_ι,
          Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.piCongrRight_symm_apply,
          Pi.map_apply, productHomFamilyEquiv_π]
        exact (SheafHomAdj.prodSheafHomAdjunction (G i)).homEquiv_naturality_left_symm f
          (g ≫ Pi.π (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F) i)
      homEquiv_naturality_right := by
        intro X F F' f g
        change (∐ (fun i ↦ (prod.functor.obj (G i)).obj X) ⟶ F) at f
        apply Pi.hom_ext _ _
        intro i
        change ((coproductHomFamilyEquiv (fun i ↦ (prod.functor.obj (G i)).obj X) F').trans
              ((Equiv.piCongrRight (fun i ↦
                  (SheafHomAdj.prodSheafHomAdjunction (G i)).homEquiv X F')).trans
                (productHomFamilyEquiv
                  (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F') X).symm)) (f ≫ g) ≫
            Pi.π (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F') i =
          (((coproductHomFamilyEquiv (fun i ↦ (prod.functor.obj (G i)).obj X) F).trans
              ((Equiv.piCongrRight (fun i ↦
                  (SheafHomAdj.prodSheafHomAdjunction (G i)).homEquiv X F)).trans
                (productHomFamilyEquiv
                  (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F) X).symm)) f) ≫
            Limits.Pi.map (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).map g) ≫
              Pi.π (fun i ↦ (SheafHomAdj.sheafHomFunctor (G i)).obj F') i
        simp only [Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply,
          coproductHomFamilyEquiv_ι, productHomFamilyEquiv_symm_π, Limits.Pi.map_π]
        have hproj :
            (productHomFamilyEquiv
              (fun j ↦ (SheafHomAdj.sheafHomFunctor (G j)).obj F) X).symm
              ((Equiv.piCongrRight (fun j ↦
                (SheafHomAdj.prodSheafHomAdjunction (G j)).homEquiv X F))
                ((coproductHomFamilyEquiv
                  (fun j ↦ (prod.functor.obj (G j)).obj X) F) f)) ≫
              Pi.π (fun j ↦ (SheafHomAdj.sheafHomFunctor (G j)).obj F) i =
              Pi.map (fun j ↦ (SheafHomAdj.prodSheafHomAdjunction (G j)).homEquiv X F)
              ((coproductHomFamilyEquiv
                (fun j ↦ (prod.functor.obj (G j)).obj X) F) f) i := by
          simp only [productHomFamilyEquiv_symm_π, Equiv.piCongrRight_apply, Pi.map_apply]
        calc
          _ = ((Equiv.piCongrRight (fun j ↦
                (SheafHomAdj.prodSheafHomAdjunction (G j)).homEquiv X F)
                ((coproductHomFamilyEquiv
                  (fun j ↦ (prod.functor.obj (G j)).obj X) F) f)) i) ≫
                (SheafHomAdj.sheafHomFunctor (G i)).map g := by
              simpa [Equiv.piCongrRight_apply, Pi.map_apply,
                coproductHomFamilyEquiv_ι, Category.assoc] using
                (SheafHomAdj.prodSheafHomAdjunction (G i)).homEquiv_naturality_right
                  (Sigma.ι (fun j ↦ (prod.functor.obj (G j)).obj X) i ≫ f) g
          _ = _ := by
            exact congrArg (fun h => h ≫ (SheafHomAdj.sheafHomFunctor (G i)).map g)
              hproj.symm }

/-- Sheafification turns the semi-representable presheaf attached to `K` into the coproduct of
the sheafified representables of its components. -/
noncomputable def sheafifiedFormalCoproductIso
    (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) :
    (presheafToSheaf J (Type u)).obj ((FormalCoproduct.yoneda (C := C)).obj K) ≅
      ∐ (fun i : K.I =>
        (presheafToSheaf J (Type u)).obj ((yoneda (C := C)).obj (K.obj i))) := by
  let : PreservesColimits (presheafToSheaf J (Type u)) :=
    (sheafificationAdjunction J (Type u)).leftAdjoint_preservesColimits
  exact PreservesCoproduct.iso (presheafToSheaf J (Type u))
    (fun i : K.I => (yoneda (C := C)).obj (K.obj i))

/-- The binary product is symmetric, read as an isomorphism between the two ways of forming it
with the product functor. -/
noncomputable def productFunctorSwap {D : Type w} [Category.{v, w} D]
    [HasBinaryProducts D] (X Y : D) :
    (prod.functor.obj X).obj Y ≅ (prod.functor.obj Y).obj X := by
  simpa [prod.functor] using Limits.prod.braiding X Y

/-- The coproduct of the products of a family with a fixed object is the product of the
coproduct with that object. -/
noncomputable def coproductOfProductsIso {I : Type u}
    (J : GrothendieckTopology C) (G : I → Sheaf J (Type u)) (X : Sheaf J (Type u)) :
    (∐ (fun i ↦ (prod.functor.obj (G i)).obj X)) ≅
      (prod.functor.obj (∐ G)).obj X := by
  let : PreservesColimitsOfShape (Discrete I) (prod.functor.obj X) :=
    (SheafHomAdj.prodSheafHomAdjunction X).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  exact Sigma.mapIso (fun i ↦ productFunctorSwap (G i) X) ≪≫
    (PreservesCoproduct.iso (prod.functor.obj X) G).symm ≪≫
      productFunctorSwap X (∐ G)

/-- `coproductOfProductsIso` carries the `i`-th coproduct injection to the product of the `i`-th
injection with the identity. -/
lemma coproductOfProductsIso_ι_hom {I : Type u}
    (J : GrothendieckTopology C) (G : I → Sheaf J (Type u))
    (X : Sheaf J (Type u)) (i : I) :
    Sigma.ι (fun j ↦ (prod.functor.obj (G j)).obj X) i ≫
        (coproductOfProductsIso J G X).hom =
      (prod.functor.map (Sigma.ι G i)).app X := by
  let : PreservesColimitsOfShape (Discrete I) (prod.functor.obj X) :=
    (SheafHomAdj.prodSheafHomAdjunction X).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  show Sigma.ι (fun j ↦ (prod.functor.obj (G j)).obj X) i ≫
      (Sigma.mapIso (fun j ↦ productFunctorSwap (G j) X)).hom ≫
        (PreservesCoproduct.iso (prod.functor.obj X) G).symm.hom ≫
        (productFunctorSwap X (∐ G)).hom = _
  simp only [← Category.assoc, Sigma.ι_mapIso_hom]
  simp only [Category.assoc, Iso.symm_hom, PreservesCoproduct.inv_hom,
    ι_comp_sigmaComparison]
  apply Limits.prod.hom_ext <;> simp [productFunctorSwap, prod.functor]

/-- `coproductOfProductsIso`, naturally in the fixed object. -/
noncomputable def coproductOfProductsNatIso {I : Type u}
    (J : GrothendieckTopology C) (G : I → Sheaf J (Type u)) :
    (Functor.pi' (fun i ↦ prod.functor.obj (G i)) ⋙ Sigma.functor I) ≅
      prod.functor.obj (∐ G) := by
  refine NatIso.ofComponents (fun X ↦ coproductOfProductsIso J G X) ?_
  intro X Y f
  apply IsColimit.hom_ext (coproductIsCoproduct
    (fun i ↦ (prod.functor.obj (G i)).obj X))
  intro i
  change Sigma.ι (fun j ↦ (prod.functor.obj (G j)).obj X) i.as ≫
      Limits.Sigma.map (fun j ↦ (prod.functor.obj (G j)).map f) ≫
        (coproductOfProductsIso J G Y).hom =
    Sigma.ι (fun j ↦ (prod.functor.obj (G j)).obj X) i.as ≫
      (coproductOfProductsIso J G X).hom ≫ (prod.functor.obj (∐ G)).map f
  simp only [← Category.assoc, Limits.Sigma.ι_map]
  rw [Category.assoc, coproductOfProductsIso_ι_hom, coproductOfProductsIso_ι_hom]
  exact (prod.functor.map (Sigma.ι G i.as)).naturality f

/-- **Stacks 0D86.** For a semi-representable object `K = {U i}`, the product of the
localization push-pull functors `j_{i,*} j_i^{-1}` is naturally isomorphic to
`SheafHom(F(K)^#, -)`. This is the source's `j_* j^{-1} F = SheafHom(F(K)^#, F)` under the
product description of sheaves on `C / K`, naturally in `F`. -/
@[stacks 0D86]
noncomputable def localizationPushforwardPullbackNatIsoSheafHom
    (J : GrothendieckTopology C) (K : FormalCoproduct.{u} C) :
    (Functor.pi' (fun i : K.I =>
        localizationPullback (K.obj i) J ⋙ localizationPushforward (K.obj i) J) ⋙
        Pi.functor K.I) ≅
      CategoryTheory.SheafHomAdj.sheafHomFunctor
        ((presheafToSheaf J (Type u)).obj ((FormalCoproduct.yoneda (C := C)).obj K)) := by
  let G : K.I → Sheaf J (Type u) := fun i ↦
    (presheafToSheaf J (Type u)).obj ((yoneda (C := C)).obj (K.obj i))
  let L : Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
    Functor.pi' (fun i ↦ (prod.functor.obj (G i))) ⋙ Sigma.functor K.I
  let R : Sheaf J (Type u) ⥤ Sheaf J (Type u) :=
    Functor.pi' (fun i ↦ SheafHomAdj.sheafHomFunctor (G i)) ⋙ Pi.functor K.I
  let adj : L ⊣ R := localizationProductSheafHomAdjunction J K G
  let Gtot : Sheaf J (Type u) :=
    (presheafToSheaf J (Type u)).obj ((FormalCoproduct.yoneda (C := C)).obj K)
  let GcopIso : (∐ G) ≅ Gtot := (sheafifiedFormalCoproductIso J K).symm
  let leftIso : L ≅ prod.functor.obj Gtot :=
    coproductOfProductsNatIso J G ≪≫ NatIso.ofComponents
      (fun X ↦ (show (prod.functor.obj (∐ G)).obj X ≅ (prod.functor.obj Gtot).obj X from
        Limits.prod.mapIso GcopIso (Iso.refl X))) (by
        intro X Y f
        exact Limits.prod.map_swap f GcopIso.hom)
  let adjTot : L ⊣ SheafHomAdj.sheafHomFunctor Gtot :=
    (SheafHomAdj.prodSheafHomAdjunction Gtot).ofNatIsoLeft leftIso.symm
  let e : R ≅ SheafHomAdj.sheafHomFunctor Gtot :=
    Adjunction.rightAdjointUniq adj adjTot
  let A : K.I → (Sheaf J (Type u) ⥤ Sheaf J (Type u)) := fun i ↦
    localizationPullback (K.obj i) J ⋙ localizationPushforward (K.obj i) J
  let B : K.I → (Sheaf J (Type u) ⥤ Sheaf J (Type u)) := fun i ↦
    SheafHomAdj.sheafHomFunctor (G i)
  let isoFamily : Functor.pi' A ≅ Functor.pi' B :=
    NatIso.pi' (fun i ↦ (OverShriek.sheafHomYonedaSheafifyNatIso (K.obj i) J).symm)
  let isoLoc : (Functor.pi' A ⋙ Pi.functor K.I) ≅ R :=
    Functor.isoWhiskerRight isoFamily (Pi.functor K.I)
  exact isoLoc ≪≫ e

end CategoryTheory.SemiRepresentable

end
