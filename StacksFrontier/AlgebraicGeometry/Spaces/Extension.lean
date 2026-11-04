module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ExtensionEvaluation

/-!
# Extension of algebraic spaces along a change of base scheme (Stacks 03I4 (2), (3))

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `j` be the corresponding localization
functor from the big fppf site of `S` to that of `S'`. Stacks 03I4 part (2) says that the extension
`j_!` carries the representable sheaf of a scheme `U` over `S` to the representable sheaf of
`U` viewed over `S'`, and part (3) says that `j_!` carries algebraic spaces over `S` to algebraic
spaces over `S'`.

## Main results

* `AlgebraicGeometry.isAlgebraicSpace_extend`: **Stacks 03I4 (3)**, the extension of an algebraic
  space is an algebraic space.

## Implementation notes

The extension functor is taken to be an arbitrary left adjoint `L` of restriction along
`CategoryTheory.Over.map g`, since adjoints are unique up to canonical isomorphism.

The source deduces part (3) from the characterisation of an algebraic space as the quotient of an
étale equivalence relation (Stacks 0262 and Theorem 02WW): a presentation `F = U/R` extends to the
presentation `j_!F = j(U)/j(R)`. Here the three defining conditions of
`AlgebraicGeometry.IsAlgebraicSpace` are verified for `j_!F` directly instead, which needs neither
of those two results:

* the sheaf condition is the sheaf condition of `L.obj F`;
* for the diagonal and for the atlas, the common input is that every section of `j_!F` over a
  scheme `V` over `S'` factors through the extension of a representable: by the evaluation formula
  `AlgebraicGeometry.isIso_relocalizeOfRestricted` it is a pair of a factorization `V → S` of the
  structure morphism of `V` and a section of `F` over `V` viewed over `S`
  (`extendedSection_factorization`). Representability of the diagonal and surjectivity and
  étaleness of the extended atlas are then each obtained from the corresponding property of `F` by
  the same base-change argument (`extended_presheaf_property`), using that `L` preserves fibre
  products.

That `L` preserves fibre products is the source's appeal to Sites 04BB, and it is proved here from
the evaluation formula as well: `L` is isomorphic to the composite of the forgetful functor to
presheaves with `CategoryTheory.OverShriek.relocalizePresheafFunctor g`
(`relocalizeSheafModelIso`), and the latter is an equivalence followed by `Over.map (yoneda.map g)`
followed by an equivalence, so it preserves all connected limits.

Part (2) is `relocalizedYonedaIso`, the identification of
`OverShriek.relocalizePresheafFunctor g |>.obj (yoneda.obj U)` with the representable presheaf of
`(Over.map g).obj U`, transported to `L` as `extendedRepresentableIso`. It is not tagged
separately: the tag of this file is on part (3).

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace AlgebraicGeometry

/-- `CategoryTheory.Over.map f` preserves all connected limits: it does so after composing with
the forgetful functor to the base, which reflects them. -/
private theorem overMap_preservesConnectedLimits
    {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y)
    {K : Type w} [Category.{w'} K] [IsConnected K] :
    PreservesLimitsOfShape K (Over.map f) := by
  have _ : PreservesLimitsOfShape K ((Over.map f) ⋙ Over.forget Y) := by
    rw [Over.mapForget_eq]
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves (Over.map f) (Over.forget Y)

/-- The presheaf-level extension `CategoryTheory.OverShriek.relocalizePresheafFunctor g` preserves
all connected limits: under the equivalences of Stacks 00Y1 identifying presheaves on a slice with
presheaves over a representable, it is `CategoryTheory.Over.map (yoneda.map g)`.

In particular it preserves fibre products, which is what every base-change argument about the
lower-shriek extension of Stacks 03I5 part (2) rests on. -/
theorem relocalizePresheaf_preservesConnectedLimits
    {C : Type u} [Category.{v} C] {V U : C} (g : V ⟶ U)
    {K : Type w} [Category.{w'} K] [IsConnected K] :
    PreservesLimitsOfShape K (OverShriek.relocalizePresheafFunctor g) := by
  let E₁ := OverShriek.presheafEquivalence (U := V)
  let E₂ := OverShriek.presheafEquivalence (U := U)
  let M := Over.map (yoneda.map g)
  have _ : PreservesLimitsOfShape K E₁.functor := inferInstance
  have _ : PreservesLimitsOfShape K E₂.inverse := inferInstance
  have _ : PreservesLimitsOfShape K M :=
    overMap_preservesConnectedLimits (f := yoneda.map g)
  show PreservesLimitsOfShape K (E₁.functor ⋙ M ⋙ E₂.inverse)
  infer_instance

/-- The presheaf-level extension of a sheaf on the big fppf site of `S` is already a sheaf on the
big fppf site of `S'`, by `AlgebraicGeometry.isIso_relocalizeOfRestricted`, so
`CategoryTheory.OverShriek.relocalizePresheafFunctor g` restricts to a functor on sheaves. This is
the model of the extension functor through which its exactness properties are read off. -/
private noncomputable def relocalizeSheafModel
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S')) :
    Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u) := by
  let J := B.topology.over S
  let P := OverShriek.relocalizePresheafFunctor g
  refine ObjectProperty.lift _ (sheafToPresheaf J (Type u) ⋙ P) ?_
  intro F
  have hIso : IsIso (OverShriek.relocalizeOfRestricted g (adj.unit.app F).hom) :=
    isIso_relocalizeOfRestricted B S S' g adj F
  let e : P.obj F.obj ≅ (L.obj F).obj :=
    asIso (OverShriek.relocalizeOfRestricted g (adj.unit.app F).hom)
  exact (Presheaf.isSheaf_of_iso_iff e).2 (L.obj F).property

/-- Any left adjoint of restriction along `CategoryTheory.Over.map g` is isomorphic to
`AlgebraicGeometry.relocalizeSheafModel`, the presheaf-level extension read as a functor on
sheaves. -/
private noncomputable def relocalizeSheafModelIso
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S')) :
    relocalizeSheafModel B S S' g adj ≅ L := by
  let β (F : Sheaf (B.topology.over S) (Type u)) :
      F.obj ⟶ (OverShriek.relocalizeRestrict g).obj ((L.obj F).obj) := (adj.unit.app F).hom
  refine NatIso.ofComponents (fun F => ?_) ?_
  · have hα : IsIso (OverShriek.relocalizeOfRestricted g (β F)) :=
      isIso_relocalizeOfRestricted B S S' g adj F
    exact ObjectProperty.isoMk _ (@asIso _ _ _ _ _ hα)
  · intro F F' f
    apply Sheaf.hom_ext
    dsimp [relocalizeSheafModel, ObjectProperty.isoMk]
    let A := OverShriek.relocalizeAdjunction g
    apply (A.homEquiv F.obj (L.obj F').obj).injective
    rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
    change _ ≫ OverShriek.relocalizeToRestricted g (OverShriek.relocalizeOfRestricted g (β F')) =
      OverShriek.relocalizeToRestricted g (OverShriek.relocalizeOfRestricted g (β F)) ≫ _
    rw [OverShriek.relocalizeToRestricted_relocalizeOfRestricted,
      OverShriek.relocalizeToRestricted_relocalizeOfRestricted]
    exact congrArg (fun k => k.hom) (adj.unit.naturality f)

/-- The component at `X` of the inverse of `AlgebraicGeometry.relocalizeSheafModelIso`, as an
isomorphism of presheaves from the extended sheaf to the presheaf-level extension. -/
private noncomputable def extendedPresheafIso
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S'))
    (X : Sheaf (B.topology.over S) (Type u)) :
    (L.obj X).obj ≅ (OverShriek.relocalizePresheafFunctor g).obj X.obj := by
  simpa [relocalizeSheafModel] using
    (asIso ((relocalizeSheafModelIso B S S' g adj).app X).inv.hom)

/-- `AlgebraicGeometry.extendedPresheafIso` is natural in the sheaf. -/
private theorem extendedPresheafIso_naturality
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S'))
    {X Y : Sheaf (B.topology.over S) (Type u)} (q : X ⟶ Y) :
    (extendedPresheafIso B S S' g adj X).hom ≫
        (OverShriek.relocalizePresheafFunctor g).map q.hom =
      (L.map q).hom ≫ (extendedPresheafIso B S S' g adj Y).hom :=
  (congrArg (fun f => f.hom) ((relocalizeSheafModelIso B S S' g adj).inv.naturality q)).symm

/-- `AlgebraicGeometry.relocalizeSheafModel` preserves fibre products: the forgetful functor to
presheaves reflects them, and the composite is the presheaf-level extension. -/
private theorem relocalizeSheafModel_preservesConnectedLimits
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S')) :
    PreservesLimitsOfShape WalkingCospan (relocalizeSheafModel B S S' g adj) := by
  let R := relocalizeSheafModel B S S' g adj
  let J := B.topology.over S
  let J' := B.topology.over S'
  let P := OverShriek.relocalizePresheafFunctor g
  have _ : PreservesLimitsOfShape WalkingCospan (sheafToPresheaf J (Type u)) := inferInstance
  have _ : PreservesLimitsOfShape WalkingCospan P :=
    relocalizePresheaf_preservesConnectedLimits g
  have _ : PreservesLimitsOfShape WalkingCospan (R ⋙ sheafToPresheaf J' (Type u)) := by
    show PreservesLimitsOfShape WalkingCospan (sheafToPresheaf J (Type u) ⋙ P)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves R (sheafToPresheaf J' (Type u))

/-- **The extension functor preserves fibre products.** This is the source's appeal to Sites 04BB;
it holds for any left adjoint of restriction along `CategoryTheory.Over.map g`, being true for the
presheaf-level model. -/
private theorem leftAdjoint_preservesConnectedLimits
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S')) :
    PreservesLimitsOfShape WalkingCospan L := by
  have _ : PreservesLimitsOfShape WalkingCospan (relocalizeSheafModel B S S' g adj) :=
    relocalizeSheafModel_preservesConnectedLimits B S S' g adj
  exact Limits.preservesLimitsOfShape_of_natIso (relocalizeSheafModelIso B S S' g adj)

/-- The representable presheaf of a scheme over `S` is a sheaf on the big fppf site of `S`, the big
fppf topology being subcanonical. -/
private theorem bigFppfOver_isSheaf_yoneda
    (B : BigFppfSite.{u}) (S : B.Schemes) (hS := S.property)
    (U : BigFppfOver B (B.inclusion.obj S) hS) :
    Presheaf.IsSheaf (BigFppfOver.topology B (B.inclusion.obj S) hS) (yoneda.obj U) := by
  have _ : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  have _ : (BigFppfOver.topology B (B.inclusion.obj S) hS).Subcanonical := by
    show (B.topology.over (B.obj hS)).Subcanonical
    infer_instance
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := _) (yoneda.obj U))

/-- **Stacks 03I4 (2), presheaf level.** The presheaf-level extension of the representable presheaf
of a scheme `U` over `S` is represented by `U` viewed over `S'`: a section over `W` is a
factorization of the structure morphism of `W` through `S` together with a morphism `W ⟶ U` over
it, which is the same thing as a morphism `W ⟶ U` over `S'`. -/
noncomputable def relocalizedYonedaRepresentableBy
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    (U : BigFppfOver B (B.inclusion.obj S) S.property) :
    ((OverShriek.relocalizePresheafFunctor g).obj (yoneda.obj U)).RepresentableBy
      (Over.mk (U.hom ≫ g)) := by
  refine ⟨?_, ?_⟩
  · intro W
    refine
      { toFun := fun k => ⟨⟨k.left ≫ U.hom, Over.homMk k.left rfl⟩, by
          change k.left ≫ U.hom ≫ g = W.hom
          simpa [Category.assoc] using k.w⟩
        invFun := fun x => Over.homMk x.1.2.left (by
          calc
            x.1.2.left ≫ U.hom ≫ g = x.1.1 ≫ g :=
              congrArg (fun t => t ≫ g) x.1.2.w
            _ = W.hom := x.2)
        left_inv := fun k => by ext; rfl
        right_inv := by
          rintro ⟨⟨ψ, k⟩, hψ⟩
          let kHom : Over.mk ψ ⟶ U := k
          apply Subtype.ext
          apply Sigma.ext
          · simp
          · dsimp
            let kInv : Over.mk ψ ⟶ U := Over.homMk kHom.left kHom.w
            let kL' : (Over.mk ψ).left ⟶ U.left := Over.Hom.left kInv
            let k' : Over.mk (kL' ≫ U.hom) ⟶ U := Over.homMk kL' rfl
            have hidx : kL' ≫ U.hom = ψ := by simp [kL']
            have hObj : Over.mk (kL' ≫ U.hom) = Over.mk ψ := congrArg Over.mk hidx
            have hleft : (eqToHom hObj.symm).left = 𝟙 ((Over.mk ψ).left) := by
              rw [Over.eqToHom_left]
              rfl
            have hk : eqToHom hObj.symm ≫ k' = kHom := by
              apply Over.OverMorphism.ext
              rw [Over.comp_left, hleft, Category.id_comp]
              change kL' = Over.Hom.left kHom
              rfl
            simpa [Over.homMk, k', kL', kInv, kHom] using
              (eqToHom_comp_heq k' hObj.symm).symm.trans (heq_of_eq hk) }
  · intro W W' f k
    rfl

/-- **Stacks 03I4 (2), presheaf level**, as an isomorphism of presheaves: the lower-shriek
extension of the representable presheaf of a scheme `U` over `S` is the representable presheaf of
`U` viewed over `S'`. -/
noncomputable def relocalizedYonedaIso
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    (U : BigFppfOver B (B.inclusion.obj S) S.property) :
    (OverShriek.relocalizePresheafFunctor g).obj (yoneda.obj U) ≅
      yoneda.obj ((Over.map g).obj U) :=
  (Functor.representableByEquiv (relocalizedYonedaRepresentableBy B S S' g U)).symm

/-- `AlgebraicGeometry.relocalizedYonedaIso` is natural in `U`. -/
theorem relocalizedYonedaIso_naturality
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {U V : BigFppfOver B (B.inclusion.obj S) S.property} (k : U ⟶ V) :
    (OverShriek.relocalizePresheafFunctor g).map (yoneda.map k) ≫
        (relocalizedYonedaIso B S S' g V).hom =
      (relocalizedYonedaIso B S S' g U).hom ≫ yoneda.map ((Over.map g).map k) := by
  ext W x
  rcases x with ⟨⟨ψ, f⟩, hψ⟩
  rfl

/-- **Stacks 03I4 (2).** The extension of the representable sheaf of a scheme `U` over `S` is the
representable sheaf of `U` viewed over `S'`. -/
private noncomputable def extendedRepresentableIso
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S'))
    (U : BigFppfOver B (B.inclusion.obj S) S.property)
    (hU : Presheaf.IsSheaf (B.topology.over S) (yoneda.obj U)) :
    (L.obj (⟨yoneda.obj U, hU⟩ : Sheaf (B.topology.over S) (Type u))).obj ≅
      yoneda.obj ((Over.map g).obj U) := by
  exact extendedPresheafIso B S S' g adj ⟨yoneda.obj U, hU⟩ ≪≫ relocalizedYonedaIso B S S' g U

/-- `AlgebraicGeometry.extendedRepresentableIso` is natural in `U`. -/
private theorem extendedRepresentableIso_naturality
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S'))
    {U V : BigFppfOver B (B.inclusion.obj S) S.property}
    (hU : Presheaf.IsSheaf (B.topology.over S) (yoneda.obj U))
    (hV : Presheaf.IsSheaf (B.topology.over S) (yoneda.obj V))
    (k : U ⟶ V) :
    (extendedRepresentableIso B S S' g adj U hU).hom ≫ yoneda.map ((Over.map g).map k) =
      (L.map (ObjectProperty.homMk (yoneda.map k) :
        (⟨yoneda.obj U, hU⟩ : Sheaf (B.topology.over S) (Type u)) ⟶
        ⟨yoneda.obj V, hV⟩)).hom ≫
        (extendedRepresentableIso B S S' g adj V hV).hom := by
  let XU : Sheaf (B.topology.over S) (Type u) := ⟨yoneda.obj U, hU⟩
  let XV : Sheaf (B.topology.over S) (Type u) := ⟨yoneda.obj V, hV⟩
  let q : XU ⟶ XV := ObjectProperty.homMk (yoneda.map k)
  have hη : (extendedPresheafIso B S S' g adj XU).hom ≫
      (OverShriek.relocalizePresheafFunctor g).map (yoneda.map k) =
      (L.map q).hom ≫ (extendedPresheafIso B S S' g adj XV).hom :=
    extendedPresheafIso_naturality B S S' g adj q
  have hγ := relocalizedYonedaIso_naturality B S S' g k
  show (extendedPresheafIso B S S' g adj XU).hom ≫ (relocalizedYonedaIso B S S' g U).hom ≫
      yoneda.map ((Over.map g).map k) =
    (L.map q).hom ≫ (extendedPresheafIso B S S' g adj XV).hom ≫
      (relocalizedYonedaIso B S S' g V).hom
  rw [← hγ, reassoc_of% hη]

/-- **Every section of an extended sheaf comes from a section of the original one.** A morphism
`yoneda.obj V ⟶ L.obj F` from the representable sheaf of a scheme `V` over `S'` factors as the
extension of a morphism `yoneda.obj V₀ ⟶ F`, where `V₀` is `V` together with a factorization of its
structure morphism through `S`, and `V` is the image of `V₀` over `S'`. This is the content of the
evaluation formula `AlgebraicGeometry.isIso_relocalizeOfRestricted` in the form used below. -/
private theorem extendedSection_factorization
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S'))
    (F : (BigFppfOver B (B.inclusion.obj S) S.property)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (B.topology.over S) F)
    (V : BigFppfOver B (B.inclusion.obj S') S'.property)
    (e : yoneda.obj V ⟶ (L.obj (⟨F, hF⟩ : Sheaf (B.topology.over S) (Type u))).obj) :
    ∃ (V₀ : BigFppfOver B (B.inclusion.obj S) S.property)
      (eV : (Over.map g).obj V₀ ≅ V) (e₀ : yoneda.obj V₀ ⟶ F),
      e = yoneda.map eV.inv ≫
        (extendedRepresentableIso B S S' g adj V₀
          (bigFppfOver_isSheaf_yoneda B S S.property V₀)).inv ≫
        (L.map (ObjectProperty.homMk e₀ :
          (⟨yoneda.obj V₀, bigFppfOver_isSheaf_yoneda B S S.property V₀⟩ :
              Sheaf (B.topology.over S) (Type u)) ⟶ ⟨F, hF⟩)).hom := by
  classical
  let X : Sheaf (B.topology.over S) (Type u) := ⟨F, hF⟩
  let η := relocalizeSheafModelIso B S S' g adj
  let h := e ≫ (η.app X).inv.hom
  let x := yonedaEquiv h
  change (OverShriek.fiber (𝟙 (yoneda.obj S'))
      (OverShriek.presheafToYoneda F ≫ yoneda.map g)).obj (Opposite.op V) at x
  have hx : yonedaEquiv h = x := rfl
  rcases x with ⟨⟨ψ, s⟩, hψ⟩
  have hxval := congrArg Subtype.val hx
  have hψ' : ψ ≫ g = V.hom := by
    change ψ ≫ g = V.hom at hψ
    exact hψ
  let V₀ : BigFppfOver B (B.inclusion.obj S) S.property := Over.mk ψ
  let eV : (Over.map g).obj V₀ ≅ V :=
    Over.isoMk (Iso.refl _) (by simpa [V₀] using hψ'.symm)
  let e₀ : yoneda.obj V₀ ⟶ F := yonedaEquiv.symm s
  refine ⟨V₀, eV, e₀, ?_⟩
  apply (cancel_mono (η.app X).inv.hom).1
  apply yonedaEquiv.injective
  let U₀ : Sheaf (B.topology.over S) (Type u) :=
    ⟨yoneda.obj V₀, bigFppfOver_isSheaf_yoneda B S S.property V₀⟩
  let q₀ : U₀ ⟶ X := ObjectProperty.homMk e₀
  let ρ := relocalizedYonedaIso B S S' g V₀
  let M := relocalizeSheafModel B S S' g adj
  let θ := extendedPresheafIso B S S' g adj U₀
  have hα : (extendedRepresentableIso B S S' g adj V₀ U₀.property).inv = ρ.inv ≫ θ.inv := by
    show (θ ≪≫ ρ).inv = ρ.inv ≫ θ.inv
    rw [Iso.trans_inv]
  have hComp : θ.inv ≫ (L.map q₀).hom ≫ (η.app X).inv.hom =
      (M.map q₀).hom :=
    (Iso.inv_comp_eq _).2 (extendedPresheafIso_naturality B S S' g adj q₀).symm
  let κ := relocalizedYonedaRepresentableBy B S S' g V₀
  let s₀ : (yoneda.obj V₀).obj (Opposite.op V₀) := 𝟙 V₀
  have hψ₀ : V₀.hom ≫ g = V.hom := by
    show ψ ≫ g = V.hom
    exact hψ'
  have heVleft : Over.Hom.left eV.inv = 𝟙 V.left := by
    have hh := congrArg Over.Hom.left eV.inv_hom_id
    simpa [eV, Over.isoMk] using hh
  have hρ : ρ.inv.app (Opposite.op V) eV.inv = ⟨⟨ψ, s₀⟩, hψ₀⟩ := by
    show κ.homEquiv eV.inv = ⟨⟨ψ, s₀⟩, hψ₀⟩
    apply Subtype.ext
    apply Sigma.ext
    · dsimp [κ, relocalizedYonedaRepresentableBy]
      show Over.Hom.left eV.inv ≫ V₀.hom = ψ
      rw [heVleft]
      simp [V₀]
    · dsimp [κ, relocalizedYonedaRepresentableBy]
      apply heq_of_eq
      apply Over.OverMorphism.ext
      exact heVleft
  rw [hα]
  simp only [Category.assoc]
  show yonedaEquiv h =
    yonedaEquiv (yoneda.map eV.inv ≫ ρ.inv ≫ θ.inv ≫ (L.map q₀).hom ≫ (η.app X).inv.hom)
  rw [hComp]
  apply Subtype.ext
  rw [hxval]
  rw [yonedaEquiv_apply]
  have hEval :
      ((yoneda.map eV.inv ≫ ρ.inv ≫ (M.map q₀).hom).app (Opposite.op V)) (𝟙 V) =
        ((M.map q₀).hom).app (Opposite.op V) (ρ.inv.app (Opposite.op V) eV.inv) :=
    rfl
  rw [hEval, hρ]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    show s = e₀.app (Opposite.op V₀) s₀
    simp [e₀, s₀]

/-- Étaleness of morphisms of schemes is invariant under pre- and post-composition with
isomorphisms.

This is not registered as a global instance: it is made a local instance in each module that
needs it, as here. -/
theorem etale_scheme_respectsIso : MorphismProperty.RespectsIso (@Etale.{u}) :=
  MorphismProperty.RespectsIso.mk _ (fun e f hf => by
    have _ : Etale f := hf
    infer_instance) (fun e f hf => by
    have _ : Etale f := hf
    infer_instance)

attribute [local instance] etale_scheme_respectsIso

/-- **A property of a morphism from a representable presheaf survives extension.** If
`q : h_U ⟶ F` has a property `Q` of morphisms of schemes after every representable base change,
then so does the extended morphism `h_{j(U)} ⟶ j_!F`. Every section of `j_!F` factors as the
extension of a section of `F` (`extendedSection_factorization`), the base change of the extended
`q` along it is the extension of the base change of `q` because the extension functor preserves
fibre products, and that base change is a morphism of schemes over `S'` with the same underlying
morphism of schemes. -/
private theorem extended_presheaf_property
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous
      (Type u) (B.topology.over S) (B.topology.over S'))
    (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (F : (BigFppfOver B (B.inclusion.obj S) S.property)ᵒᵖ ⥤ Type u)
    (hF : Presheaf.IsSheaf (B.topology.over S) F)
    (U : BigFppfOver B (B.inclusion.obj S) S.property)
    (hU : Presheaf.IsSheaf (B.topology.over S) (yoneda.obj U))
    (q : yoneda.obj U ⟶ F)
    (hq : (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B (B.inclusion.obj S) S.property)).presheaf q) :
    (MorphismProperty.inverseImage Q
      (BigFppfOver.toScheme B (B.inclusion.obj S') S'.property)).presheaf
      ((extendedRepresentableIso B S S' g adj U hU).inv ≫
        (L.map (ObjectProperty.homMk q :
          (⟨yoneda.obj U, hU⟩ : Sheaf (B.topology.over S) (Type u)) ⟶ ⟨F, hF⟩)).hom) := by
  classical
  let J := B.topology.over S
  let J' := BigFppfOver.topology B (B.inclusion.obj S') S'.property
  let T := BigFppfOver.toScheme B (B.inclusion.obj S) S.property
  let T' := BigFppfOver.toScheme B (B.inclusion.obj S') S'.property
  let F' := Over.map g
  let Q₀ := MorphismProperty.inverseImage Q T
  let Q₁ := MorphismProperty.inverseImage Q T'
  let X : Sheaf J (Type u) := ⟨F, hF⟩
  let U₀ : Sheaf J (Type u) := ⟨yoneda.obj U, hU⟩
  let q₀ : U₀ ⟶ X := ObjectProperty.homMk q
  let q₁ : yoneda.obj ((Over.map g).obj U) ⟶ (L.obj X).obj :=
    (extendedRepresentableIso B S S' g adj U hU).inv ≫ (L.map q₀).hom
  have _ : Q₁.RespectsIso := inferInstance
  show Q₁.presheaf q₁
  refine MorphismProperty.relative.of_exists (F := yoneda) (f := q₁) ?_
  · intro V e
    obtain ⟨V₀, eV, e₀, he⟩ := extendedSection_factorization B S S' g adj F hF V e
    let W₀ := hq.1.pullback e₀
    let p₀ : W₀ ⟶ U := yoneda.preimage (hq.1.fst e₀)
    have hp₀ : yoneda.map p₀ = hq.1.fst e₀ := yoneda.map_preimage _
    let r₀ := hq.1.snd e₀
    have hpull₀ := hq.1.isPullback e₀
    have hQr₀ : Q₀ r₀ := hq.2 e₀ (hq.1.fst e₀) r₀ hpull₀
    have hW : Presheaf.IsSheaf J (yoneda.obj W₀) :=
      bigFppfOver_isSheaf_yoneda B S S.property W₀
    have hV₀ : Presheaf.IsSheaf J (yoneda.obj V₀) :=
      bigFppfOver_isSheaf_yoneda B S S.property V₀
    let W₀F : Sheaf J (Type u) := ⟨yoneda.obj W₀, hW⟩
    let V₀F : Sheaf J (Type u) := ⟨yoneda.obj V₀, hV₀⟩
    let p₀F : W₀F ⟶ U₀ := ObjectProperty.homMk (yoneda.map p₀)
    let r₀F : W₀F ⟶ V₀F := ObjectProperty.homMk (yoneda.map r₀)
    let e₀F : V₀F ⟶ X := ObjectProperty.homMk e₀
    have hpull₀F : IsPullback p₀F r₀F q₀ e₀F := by
      apply IsPullback.of_map_of_faithful (sheafToPresheaf J (Type u))
      simpa [p₀F, r₀F, q₀, e₀F, hp₀] using hpull₀
    have _ : PreservesLimitsOfShape WalkingCospan L :=
      leftAdjoint_preservesConnectedLimits B S S' g adj
    have hpullL := hpull₀F.map L
    have hW' : Presheaf.IsSheaf J' (yoneda.obj (F'.obj W₀)) :=
      bigFppfOver_isSheaf_yoneda B S' S'.property (F'.obj W₀)
    have hU' : Presheaf.IsSheaf J' (yoneda.obj (F'.obj U)) :=
      bigFppfOver_isSheaf_yoneda B S' S'.property (F'.obj U)
    have hV' : Presheaf.IsSheaf J' (yoneda.obj V) :=
      bigFppfOver_isSheaf_yoneda B S' S'.property V
    have hV₀' : Presheaf.IsSheaf J' (yoneda.obj (F'.obj V₀)) :=
      bigFppfOver_isSheaf_yoneda B S' S'.property (F'.obj V₀)
    let W₁ : Sheaf J' (Type u) := ⟨yoneda.obj (F'.obj W₀), hW'⟩
    let U₁ : Sheaf J' (Type u) := ⟨yoneda.obj (F'.obj U), hU'⟩
    let V₁ : Sheaf J' (Type u) := ⟨yoneda.obj V, hV'⟩
    let V₀₁ : Sheaf J' (Type u) := ⟨yoneda.obj (F'.obj V₀), hV₀'⟩
    let αW := extendedRepresentableIso B S S' g adj W₀ hW
    let αU := extendedRepresentableIso B S S' g adj U hU
    let αV := extendedRepresentableIso B S S' g adj V₀ hV₀
    let βW : L.obj W₀F ≅ W₁ := ObjectProperty.isoMk _ αW
    let βU : L.obj U₀ ≅ U₁ := ObjectProperty.isoMk _ αU
    let βV : L.obj V₀F ≅ V₀₁ := ObjectProperty.isoMk _ αV
    let δ : V₀₁ ≅ V₁ := ObjectProperty.isoMk _ (yoneda.mapIso eV)
    let q₁ : U₁ ⟶ L.obj X := ObjectProperty.homMk (αU.inv ≫ (L.map q₀).hom)
    let e₁ : V₁ ⟶ L.obj X :=
      ObjectProperty.homMk (yoneda.map eV.inv ≫ αV.inv ≫ (L.map e₀F).hom)
    let p₁ : W₁ ⟶ U₁ := ObjectProperty.homMk (yoneda.map (F'.map p₀))
    let r₁ : W₁ ⟶ V₁ := ObjectProperty.homMk (yoneda.map (F'.map r₀ ≫ eV.hom))
    have hnatP := extendedRepresentableIso_naturality B S S' g adj hW hU p₀
    have hnatR := extendedRepresentableIso_naturality B S S' g adj hW hV₀ r₀
    have hpull₁ : IsPullback p₁ r₁ q₁ e₁ := by
      apply hpullL.of_iso βW βU (βV ≪≫ δ) (Iso.refl _)
      · apply Sheaf.hom_ext
        exact hnatP.symm
      · apply Sheaf.hom_ext
        simpa [βW, βV, δ, αW, αV, r₀F, r₁, ObjectProperty.homMk,
          Category.assoc, Functor.map_comp] using
          congrArg (fun k => k ≫ yoneda.map eV.hom) hnatR.symm
      · apply Sheaf.hom_ext
        simp [q₁, βU]
      · apply Sheaf.hom_ext
        simp [e₁, δ, βV, Category.assoc]
    have hQr₁ : Q₁ (F'.map r₀ ≫ eV.hom) := by
      have hbase : Q₁ (F'.map r₀) := by
        show Q (T.map r₀)
        exact hQr₀
      exact MorphismProperty.RespectsIso.postcomp Q (T'.map eV.hom)
        (T'.map (F'.map r₀)) (by simpa [Q₁, T'] using hbase)
    refine ⟨F'.obj W₀, yoneda.map (F'.map p₀), F'.map r₀ ≫ eV.hom, ?_, ?_⟩
    · convert hpull₁.map (sheafToPresheaf J' (Type u)) using 1 <;> try rfl
      simpa [e₁, αV, e₀F, ObjectProperty.homMk] using he
    · exact hQr₁

/-- **Stacks 03I4 (3).** Extension along a morphism `g : S ⟶ S'` of a big fppf site carries
algebraic spaces over `S` to algebraic spaces over `S'`. -/
@[stacks 03I4 "extension_algebraic_space"]
theorem isAlgebraicSpace_extend
    (B : BigFppfSite.{u}) (S S' : B.Schemes) (g : S ⟶ S')
    {L : Sheaf (B.topology.over S) (Type u) ⥤
      Sheaf (B.topology.over S') (Type u)}
    (adj : L ⊣ (Over.map g).sheafPushforwardContinuous (Type u)
      (B.topology.over S) (B.topology.over S'))
    (F : (BigFppfOver B (B.inclusion.obj S) S.property)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (B.inclusion.obj S) S.property F) :
    IsAlgebraicSpace B (B.inclusion.obj S') S'.property
      (L.obj (⟨F, hF.isSheaf⟩ : Sheaf (B.topology.over S) (Type u))).obj := by
  classical
  let J := B.topology.over S
  let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  refine ⟨(L.obj FF).property, ?_, ?_⟩
  · let _ : HasBinaryProducts (BigFppfOver B (B.inclusion.obj S) S.property) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    let _ : HasBinaryProducts (BigFppfOver B (B.inclusion.obj S') S'.property) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    apply Functor.relativelyRepresentable.diag_of_map_from_obj
    intro V e
    obtain ⟨V₀, eV, e₀, he⟩ := extendedSection_factorization B S S' g adj F hF.isSheaf V e
    have he₀ : yoneda.relativelyRepresentable e₀ :=
      Functor.relativelyRepresentable.of_diag hF.diagonal_representable e₀
    have hprop : (MorphismProperty.inverseImage (⊤ : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (B.inclusion.obj S) S.property)).presheaf e₀ :=
      ⟨he₀, fun _ _ _ _ _ _ => trivial⟩
    have hext := extended_presheaf_property B S S' g adj
      (⊤ : MorphismProperty Scheme.{u}) F hF.isSheaf V₀
      (bigFppfOver_isSheaf_yoneda B S S.property V₀) e₀ hprop
    rw [he]
    exact MorphismProperty.RespectsIso.precomp yoneda.relativelyRepresentable
      (yoneda.map eV.inv) _ hext.1
  · obtain ⟨U, q, hqSurj, hqEtale⟩ := hF.exists_atlas
    have hU : Presheaf.IsSheaf J (yoneda.obj U) := bigFppfOver_isSheaf_yoneda B S S.property U
    let U₀ : Sheaf J (Type u) := ⟨yoneda.obj U, hU⟩
    let α := extendedRepresentableIso B S S' g adj U hU
    let f : yoneda.obj ((Over.map g).obj U) ⟶ (L.obj FF).obj :=
      α.inv ≫ (L.map (ObjectProperty.homMk q : U₀ ⟶ FF)).hom
    exact ⟨(Over.map g).obj U, f,
      extended_presheaf_property B S S' g adj
        (@Surjective.{u} : MorphismProperty Scheme.{u}) F hF.isSheaf U hU q hqSurj,
      extended_presheaf_property B S S' g adj
        (@Etale.{u} : MorphismProperty Scheme.{u}) F hF.isSheaf U hU q hqEtale⟩

end AlgebraicGeometry

end
