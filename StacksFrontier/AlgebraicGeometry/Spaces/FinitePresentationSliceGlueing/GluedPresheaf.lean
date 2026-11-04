module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subterminal
public import StacksFrontier.AlgebraicGeometry.Full.Square
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraicityOnBaseCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueing.SubterminalRestriction

/-!
# The glued presheaf of a two-element covering by subterminal objects

Given a presheaf `A` over the representable presheaf of a subterminal `U`, a presheaf `B` over
that of a subterminal `W`, and an isomorphism of their base changes to `V`, this file constructs
the glued presheaf `CategoryTheory.SubterminalGlueing.gluedPresheaf`, whose sections over `X` are
the compatible pairs of sections of `A` over `U ⨯ X` and of `B` over `W ⨯ X`. It proves that it
is a sheaf when `A` and `B` are, that it is functorial and symmetric in the glueing datum, and,
over a terminal object, identifies its two restrictions with the two presheaves glued,
compatibly over `V` and naturally in the glueing datum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-! ### Glueing two presheaves along a subterminal intersection -/

namespace SubterminalGlueing

variable [HasBinaryProducts C] {U W V : C} {iU : V ⟶ U} {iW : V ⟶ W}
  (hU : IsSubterminal U) (hW : IsSubterminal W) (hV : IsSubterminal V)
  {A A' : Over (yoneda.obj U : Cᵒᵖ ⥤ Type v)} {Bb Bb' : Over (yoneda.obj W : Cᵒᵖ ⥤ Type v)}
  (φ : (Over.pullback (yoneda.map iU)).obj A ≅ (Over.pullback (yoneda.map iW)).obj Bb)
  (φ' : (Over.pullback (yoneda.map iU)).obj A' ≅ (Over.pullback (yoneda.map iW)).obj Bb')

/-- The identification over `V` of the two presheaves being glued: an isomorphism of their base
changes to `V` is, by `CategoryTheory.prodRestrictPullbackIso`, an isomorphism of their
restrictions along `V ⨯ -`. -/
noncomputable def glueingRestrictIso :
    (prod.functor.obj V).op ⋙ A.left ≅ (prod.functor.obj V).op ⋙ Bb.left :=
  (prodRestrictPullbackIso iU hU hV A).symm ≪≫
    Functor.isoWhiskerLeft (prod.functor.obj V).op ((Over.forget _).mapIso φ) ≪≫
      prodRestrictPullbackIso iW hW hV Bb

/-- The restriction of the second presheaf to `V`, read inside the restriction of the first one
through `CategoryTheory.SubterminalGlueing.glueingRestrictIso`. -/
noncomputable def glueingLegRight :
    (prod.functor.obj W).op ⋙ Bb.left ⟶ (prod.functor.obj V).op ⋙ A.left :=
  prodRestrictMap iW Bb.left ≫ (glueingRestrictIso hU hW hV φ).inv

/-- **The glued presheaf.** Its sections over `X` are the pairs of a section of `A` over `U ⨯ X`
and a section of `B` over `W ⨯ X` whose restrictions to `V ⨯ X` agree under the given
identification. -/
noncomputable def gluedPresheaf : Cᵒᵖ ⥤ Type v where
  obj X := Types.PullbackObj ((prodRestrictMap iU A.left).app X)
    ((glueingLegRight hU hW hV φ).app X)
  map {X Y} g := ↾fun p => ⟨⟨((prod.functor.obj U).op ⋙ A.left).map g p.1.1,
      ((prod.functor.obj W).op ⋙ Bb.left).map g p.1.2⟩, by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, p.2]⟩
  map_id X := by
    ext p
    · exact ((prod.functor.obj U).op ⋙ A.left).map_id_apply X _
    · exact ((prod.functor.obj W).op ⋙ Bb.left).map_id_apply X _
  map_comp f g := by
    ext p
    · exact ((prod.functor.obj U).op ⋙ A.left).map_comp_apply f g _
    · exact ((prod.functor.obj W).op ⋙ Bb.left).map_comp_apply f g _

/-- The first component of a restricted section of the glued presheaf. -/
@[simp]
theorem gluedPresheaf_map_val_fst {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (p : (gluedPresheaf hU hW hV φ).obj X) :
    ((gluedPresheaf hU hW hV φ).map g p).1.1 =
      ((prod.functor.obj U).op ⋙ A.left).map g p.1.1 :=
  rfl

/-- The second component of a restricted section of the glued presheaf. -/
@[simp]
theorem gluedPresheaf_map_val_snd {X Y : Cᵒᵖ} (g : X ⟶ Y)
    (p : (gluedPresheaf hU hW hV φ).obj X) :
    ((gluedPresheaf hU hW hV φ).map g p).1.2 =
      ((prod.functor.obj W).op ⋙ Bb.left).map g p.1.2 :=
  rfl

/-- The projection from the glued presheaf to the restriction of the first presheaf. -/
noncomputable def gluedPresheafFst :
    gluedPresheaf hU hW hV φ ⟶ (prod.functor.obj U).op ⋙ A.left where
  app _ := ↾fun p => p.1.1
  naturality _ _ _ := rfl

/-- The projection from the glued presheaf to the restriction of the second presheaf. -/
noncomputable def gluedPresheafSnd :
    gluedPresheaf hU hW hV φ ⟶ (prod.functor.obj W).op ⋙ Bb.left where
  app _ := ↾fun p => p.1.2
  naturality _ _ _ := rfl

/-- The two projections from the glued presheaf agree over `V`. -/
theorem gluedPresheaf_condition :
    gluedPresheafFst hU hW hV φ ≫ prodRestrictMap iU A.left =
      gluedPresheafSnd hU hW hV φ ≫ glueingLegRight hU hW hV φ := by
  ext X p
  exact p.2

/-- The glued presheaf, with its two projections, is a fibre product of the restrictions of the
two given presheaves above the restriction to `V` of the first one. -/
noncomputable def isLimitGluedPresheafCone :
    IsLimit (PullbackCone.mk (gluedPresheafFst hU hW hV φ) (gluedPresheafSnd hU hW hV φ)
      (gluedPresheaf_condition hU hW hV φ)) :=
  PullbackCone.IsLimit.mk _
    (fun s =>
      { app X := ↾fun x => ⟨⟨s.fst.app X x, s.snd.app X x⟩,
          ConcreteCategory.congr_hom (NatTrans.congr_app s.condition X) x⟩
        naturality X Y g := by
          ext x
          refine Subtype.ext (Prod.ext ?_ ?_)
          · exact NatTrans.naturality_apply s.fst g x
          · exact NatTrans.naturality_apply s.snd g x })
    (fun _ => rfl) (fun _ => rfl)
    (fun s m h₁ h₂ => by
      ext X x
      refine Subtype.ext (Prod.ext ?_ ?_)
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₁ X) x
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app h₂ X) x)

/-- **The glued presheaf is a sheaf** as soon as the two given presheaves are. It is a fibre
product of their restrictions along the products with `U`, `W` and `V`, each of which is a sheaf
by `CategoryTheory.Presheaf.isSheaf_prod_functor_op_comp`, and sheaves are closed under limits
computed in presheaves. -/
theorem isSheaf_gluedPresheaf (J : GrothendieckTopology C) (hA : Presheaf.IsSheaf J A.left)
    (hB : Presheaf.IsSheaf J Bb.left) :
    Presheaf.IsSheaf J (gluedPresheaf hU hW hV φ) :=
  ObjectProperty.prop_of_isLimit _ (isLimitGluedPresheafCone hU hW hV φ) (by
    rintro (_ | (_ | _))
    · exact Presheaf.isSheaf_prod_functor_op_comp J V hA
    · exact Presheaf.isSheaf_prod_functor_op_comp J U hA
    · exact Presheaf.isSheaf_prod_functor_op_comp J W hB)

/-! #### Functoriality in the glueing datum -/

variable {a : A ⟶ A'} {b : Bb ⟶ Bb'}

/-- A morphism of glueing data is compatible with the identifications over `V`. -/
theorem glueingRestrictIso_hom_naturality
    (h : (Over.pullback (yoneda.map iU)).map a ≫ φ'.hom =
      φ.hom ≫ (Over.pullback (yoneda.map iW)).map b) :
    Functor.whiskerLeft (prod.functor.obj V).op a.left ≫ (glueingRestrictIso hU hW hV φ').hom =
      (glueingRestrictIso hU hW hV φ).hom ≫
        Functor.whiskerLeft (prod.functor.obj V).op b.left := by
  have h1 := prodRestrictPullbackIso_naturality iU hU hV a
  have h2 := prodRestrictPullbackIso_naturality iW hW hV b
  have h1' : Functor.whiskerLeft (prod.functor.obj V).op a.left ≫
        (prodRestrictPullbackIso iU hU hV A').inv =
      (prodRestrictPullbackIso iU hU hV A).inv ≫ Functor.whiskerLeft (prod.functor.obj V).op
        ((Over.pullback (yoneda.map iU)).map a).left := by
    rw [Iso.comp_inv_eq, Category.assoc, h1, Iso.inv_hom_id_assoc]
  have key : Functor.whiskerLeft (prod.functor.obj V).op
          ((Over.pullback (yoneda.map iU)).map a).left ≫
        Functor.whiskerLeft (prod.functor.obj V).op φ'.hom.left ≫
          (prodRestrictPullbackIso iW hW hV Bb').hom =
      Functor.whiskerLeft (prod.functor.obj V).op φ.hom.left ≫
        (prodRestrictPullbackIso iW hW hV Bb).hom ≫
          Functor.whiskerLeft (prod.functor.obj V).op b.left := by
    rw [← h2, ← Category.assoc, ← Category.assoc, ← Functor.whiskerLeft_comp,
      ← Functor.whiskerLeft_comp, ← Over.comp_left, ← Over.comp_left, h]
  dsimp only [glueingRestrictIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.mapIso_hom, Over.forget_map]
  rw [← Category.assoc, h1', Category.assoc, Category.assoc, Category.assoc, key]

/-- The inverse form of `CategoryTheory.SubterminalGlueing.glueingRestrictIso_hom_naturality`. -/
theorem glueingRestrictIso_inv_naturality
    (h : (Over.pullback (yoneda.map iU)).map a ≫ φ'.hom =
      φ.hom ≫ (Over.pullback (yoneda.map iW)).map b) :
    (glueingRestrictIso hU hW hV φ).inv ≫
        Functor.whiskerLeft (prod.functor.obj V).op a.left =
      Functor.whiskerLeft (prod.functor.obj V).op b.left ≫
        (glueingRestrictIso hU hW hV φ').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc,
    ← glueingRestrictIso_hom_naturality hU hW hV φ φ' h]
  simp

/-- A morphism of glueing data is compatible with the right legs of the glued presheaves. -/
theorem glueingLegRight_naturality
    (h : (Over.pullback (yoneda.map iU)).map a ≫ φ'.hom =
      φ.hom ≫ (Over.pullback (yoneda.map iW)).map b) :
    Functor.whiskerLeft (prod.functor.obj W).op b.left ≫ glueingLegRight hU hW hV φ' =
      glueingLegRight hU hW hV φ ≫
        Functor.whiskerLeft (prod.functor.obj V).op a.left := by
  dsimp only [glueingLegRight]
  rw [← Category.assoc, prodRestrictMap_naturality, Category.assoc, Category.assoc,
    glueingRestrictIso_inv_naturality hU hW hV φ φ' h]

/-- **The glued presheaf is functorial in the glueing datum.** A pair of morphisms of the two
given presheaves whose base changes to `V` commute with the two identifications induces a
morphism of the glued presheaves, taking a compatible pair of sections to the pair of their
images. -/
noncomputable def gluedPresheafMap
    (h : (Over.pullback (yoneda.map iU)).map a ≫ φ'.hom =
      φ.hom ≫ (Over.pullback (yoneda.map iW)).map b) :
    gluedPresheaf hU hW hV φ ⟶ gluedPresheaf hU hW hV φ' where
  app X := ↾fun p => ⟨⟨(Functor.whiskerLeft (prod.functor.obj U).op a.left).app X p.1.1,
      (Functor.whiskerLeft (prod.functor.obj W).op b.left).app X p.1.2⟩, by
    refine (ConcreteCategory.congr_hom
      (NatTrans.congr_app (prodRestrictMap_naturality iU a.left) X) p.1.1).trans ?_
    refine (congrArg
      (fun y => (Functor.whiskerLeft (prod.functor.obj V).op a.left).app X y) p.2).trans ?_
    exact (ConcreteCategory.congr_hom
      (NatTrans.congr_app (glueingLegRight_naturality hU hW hV φ φ' h) X) p.1.2).symm⟩
  naturality X Y g := by
    ext x
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact NatTrans.naturality_apply
        (Functor.whiskerLeft (prod.functor.obj U).op a.left) g x.1.1
    · exact NatTrans.naturality_apply
        (Functor.whiskerLeft (prod.functor.obj W).op b.left) g x.1.2

/-! #### The restriction of the glued presheaf to `U` -/

/-- Where the comparison `V ⨯ X ⟶ W ⨯ X` is invertible, so is the right leg of the glued
presheaf: it is the restriction along that comparison followed by an isomorphism. -/
theorem bijective_glueingLegRight_app (X : Cᵒᵖ)
    (h : IsIso (prod.map iW (𝟙 X.unop) : V ⨯ X.unop ⟶ W ⨯ X.unop)) :
    Function.Bijective ((glueingLegRight hU hW hV φ).app X) := by
  have := h
  have h1 : Function.Bijective (Bb.left.map (prod.map iW (𝟙 X.unop)).op) :=
    (isIso_iff_bijective _).1 inferInstance
  have h3 : Function.Bijective ((glueingRestrictIso hU hW hV φ).inv.app X) :=
    (isIso_iff_bijective _).1 inferInstance
  exact h3.comp h1

/-- Where the comparison `V ⨯ X ⟶ W ⨯ X` is invertible, the first projection from the glued
presheaf is bijective on sections over `X`: the second component of a compatible pair is then
determined by the first. -/
theorem bijective_gluedPresheafFst_app (X : Cᵒᵖ)
    (h : IsIso (prod.map iW (𝟙 X.unop) : V ⨯ X.unop ⟶ W ⨯ X.unop)) :
    Function.Bijective ((gluedPresheafFst hU hW hV φ).app X) :=
  Limits.Types.bijective_pullbackObj_fst _ (bijective_glueingLegRight_app hU hW hV φ X h)

/-! #### Symmetry of the glueing construction -/

/-- The identification over `V` is reversed by swapping the two presheaves glued. -/
theorem glueingRestrictIso_symm :
    glueingRestrictIso hW hU hV φ.symm = (glueingRestrictIso hU hW hV φ).symm := by
  refine Iso.ext ?_
  dsimp only [glueingRestrictIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Iso.trans_assoc]
  simp

/-- Swapping the two components of a compatible pair exchanges the two glued presheaves. -/
noncomputable def gluedPresheafSymmHom :
    gluedPresheaf hU hW hV φ ⟶ gluedPresheaf hW hU hV φ.symm where
  app X := ↾fun p => ⟨⟨p.1.2, p.1.1⟩, by
    have h2 := p.2
    simp only [glueingLegRight, NatTrans.comp_app, types_comp_apply] at h2 ⊢
    rw [glueingRestrictIso_symm, Iso.symm_inv, h2]
    simp⟩
  naturality _ _ _ := rfl

/-- **The glueing construction is symmetric in its two arguments.** -/
noncomputable def gluedPresheafSymmIso :
    gluedPresheaf hU hW hV φ ≅ gluedPresheaf hW hU hV φ.symm where
  hom := gluedPresheafSymmHom hU hW hV φ
  inv := gluedPresheafSymmHom hW hU hV φ.symm
  hom_inv_id := by ext X p; rfl
  inv_hom_id := by ext X p; rfl

section Restriction

variable {Z : C} (hZ : IsTerminal Z)

/-- The structure morphism of the glued presheaf to the representable presheaf of the terminal
object. -/
noncomputable def gluedToTerminal : gluedPresheaf hU hW hV φ ⟶ yoneda.obj Z :=
  (hZ.isTerminalObj yoneda Z).from (gluedPresheaf hU hW hV φ)

/-- The glued presheaf, as an object over the representable presheaf of the terminal object. -/
noncomputable def gluedOver : Over (yoneda.obj Z : Cᵒᵖ ⥤ Type v) :=
  Over.mk (gluedToTerminal hU hW hV φ hZ)

/-- The comparison from the restriction to `U` of the glued presheaf to the first of the two
presheaves glued: a section of the glued presheaf over an object `X` lying over `U` has a first
component over `U ⨯ X`, and the graph of `X ⟶ U` carries it back to a section over `X`. -/
noncomputable def gluedRestrictLeftHom (jU : U ⟶ Z) :
    pullback (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU) ⟶ A.left where
  app X := ↾fun z => A.left.map (prod.lift
      ((pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z) (𝟙 X.unop)).op
    (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z).1.1)
  naturality X Y h := ConcreteCategory.hom_ext _ _ fun z => by
    have hs := NatTrans.naturality_apply
      (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)) h z
    have hf := NatTrans.naturality_apply
      (pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)) h z
    have hmor : prod.lift (h.unop ≫
          (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z)
          (𝟙 Y.unop) ≫ prod.map (𝟙 U) h.unop =
        h.unop ≫ prod.lift
          ((pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z) (𝟙 X.unop) := by
      refine prod.hom_ext ?_ ?_ <;> simp
    have key : A.left.map (prod.map (𝟙 U) h.unop).op ≫
          A.left.map (prod.lift (h.unop ≫
            (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z)
            (𝟙 Y.unop)).op =
        A.left.map (prod.lift
            ((pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z)
            (𝟙 X.unop)).op ≫ A.left.map h := by
      rw [← A.left.map_comp, ← A.left.map_comp, ← op_comp, hmor, op_comp, Quiver.Hom.op_unop]
    simp only [types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, hs, hf,
      yoneda_obj_map, gluedPresheaf_map_val_fst, prod.functor_obj_map,
      Functor.comp_map, Functor.op_map]
    exact ConcreteCategory.congr_hom key _

/-- The comparison of `CategoryTheory.SubterminalGlueing.gluedRestrictLeftHom`, as a morphism
of presheaves over the representable presheaf of `U`. -/
noncomputable def gluedRestrictLeft (jU : U ⟶ Z) :
    (Over.pullback (yoneda.map jU)).obj (gluedOver hU hW hV φ hZ) ⟶ A :=
  Over.homMk (gluedRestrictLeftHom hU hW hV φ hZ jU) (by ext X z; exact hU _ _)

/-- The comparison is bijective on sections over every object: over an object not lying over `U`
both sides are empty, and over an object lying over `U` it is a composite of three bijections —
the first projection from the base change, the first projection from the glued presheaf, and
restriction along the graph of `X ⟶ U`. -/
theorem bijective_gluedRestrictLeftHom_app {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) (X : Cᵒᵖ) :
    Function.Bijective ((gluedRestrictLeftHom hU hW hV φ hZ jU).app X) := by
  by_cases hne : Nonempty (X.unop ⟶ U)
  · obtain ⟨p⟩ := hne
    have hb1 : Function.Bijective
        ((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X) :=
      bijective_pullback_fst_app jU (isSubterminal_of_isTerminal hZ) hU
        (Over.mk (gluedToTerminal hU hW hV φ hZ)) p
    have hb2 : Function.Bijective ((gluedPresheafFst hU hW hV φ).app X) :=
      bijective_gluedPresheafFst_app hU hW hV φ X (isIso_prod_map_of_hom hZ hU hVp p)
    have hiso : IsIso (prod.lift p (𝟙 X.unop)) := isIso_prod_lift_id_of_hom hU p
    have hb3 : Function.Bijective (A.left.map (prod.lift p (𝟙 X.unop)).op) :=
      (isIso_iff_bijective _).1 inferInstance
    have hfun : ∀ z, (gluedRestrictLeftHom hU hW hV φ hZ jU).app X z =
        A.left.map (prod.lift p (𝟙 X.unop)).op ((gluedPresheafFst hU hW hV φ).app X
          ((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z)) := fun z =>
      congrArg (fun q : X.unop ⟶ U => A.left.map (prod.lift q (𝟙 X.unop)).op
        ((gluedPresheafFst hU hW hV φ).app X
          ((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z))) (hU _ p)
    refine ⟨fun x y hxy => hb1.injective (hb2.injective (hb3.injective ?_)), fun a => ?_⟩
    · rw [← hfun, ← hfun]
      exact hxy
    · obtain ⟨w, hw⟩ := hb3.surjective a
      obtain ⟨s, hs⟩ := hb2.surjective w
      obtain ⟨z, hz⟩ := hb1.surjective s
      exact ⟨z, by rw [hfun, hz, hs, hw]⟩
  · exact ⟨fun x _ _ => absurd ⟨(pullback.snd (gluedToTerminal hU hW hV φ hZ)
      (yoneda.map jU)).app X x⟩ hne, fun y => absurd ⟨A.hom.app X y⟩ hne⟩

/-- **The restriction to `U` of the glued presheaf is the first of the two presheaves glued.**
This is the identification over `U` of the comparison between the algebraic spaces over the base
and the glueing data. -/
noncomputable def gluedRestrictLeftIso {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (Over.pullback (yoneda.map jU)).obj (gluedOver hU hW hV φ hZ) ≅ A :=
  haveI : ∀ X : Cᵒᵖ, IsIso ((gluedRestrictLeftHom hU hW hV φ hZ jU).app X) := fun X =>
    (isIso_iff_bijective _).2 (bijective_gluedRestrictLeftHom_app hU hW hV φ hZ hVp X)
  haveI := NatIso.isIso_of_isIso_app (gluedRestrictLeftHom hU hW hV φ hZ jU)
  haveI : IsIso ((Over.forget (yoneda.obj U)).map (gluedRestrictLeft hU hW hV φ hZ jU)) :=
    inferInstanceAs (IsIso (gluedRestrictLeftHom hU hW hV φ hZ jU))
  haveI : IsIso (gluedRestrictLeft hU hW hV φ hZ jU) :=
    isIso_of_reflects_iso _ (Over.forget (yoneda.obj U))
  asIso (gluedRestrictLeft hU hW hV φ hZ jU)

/-- The symmetry of the glueing construction, read over the representable presheaf of the
terminal object. -/
noncomputable def gluedOverSymmIso :
    gluedOver hU hW hV φ hZ ≅ gluedOver hW hU hV φ.symm hZ :=
  Over.isoMk (gluedPresheafSymmIso hU hW hV φ) ((hZ.isTerminalObj yoneda Z).hom_ext _ _)

/-- **The restriction to `W` of the glued presheaf is the second of the two presheaves glued.**
This is `CategoryTheory.SubterminalGlueing.gluedRestrictLeftIso` with the two arguments of the
glueing construction exchanged. -/
noncomputable def gluedRestrictRightIso {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (Over.pullback (yoneda.map jW)).obj (gluedOver hU hW hV φ hZ) ≅ Bb :=
  (Over.pullback (yoneda.map jW)).mapIso (gluedOverSymmIso hU hW hV φ hZ) ≪≫
    gluedRestrictLeftIso hW hU hV φ.symm hZ hVp.flip

/-- `CategoryTheory.SubterminalGlueing.gluedRestrictLeftIso` read as a product: over a terminal
object the restriction of the glued presheaf to `U` is the product with the representable
presheaf of `U`. -/
noncomputable def prodGluedRestrictLeftIso {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (yoneda.obj U : Cᵒᵖ ⥤ Type v) ⨯ gluedPresheaf hU hW hV φ ≅ A.left :=
  prodIsoPullbackOfIsTerminal hZ jU (gluedToTerminal hU hW hV φ hZ) ≪≫
    (Over.forget (yoneda.obj U)).mapIso (gluedRestrictLeftIso hU hW hV φ hZ hVp)

/-- `CategoryTheory.SubterminalGlueing.gluedRestrictRightIso` read as a product. -/
noncomputable def prodGluedRestrictRightIso {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (yoneda.obj W : Cᵒᵖ ⥤ Type v) ⨯ gluedPresheaf hU hW hV φ ≅ Bb.left :=
  prodIsoPullbackOfIsTerminal hZ jW (gluedToTerminal hU hW hV φ hZ) ≪≫
    (Over.forget (yoneda.obj W)).mapIso (gluedRestrictRightIso hU hW hV φ hZ hVp)

/-- **The structure morphism of the first presheaf glued is a base change of the structure
morphism of the glued presheaf** along the Yoneda image of `jU`. -/
theorem isPullback_gluedRestrictLeft {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    IsPullback ((gluedRestrictLeftIso hU hW hV φ hZ hVp).inv.left ≫
        pullback.fst (gluedOver hU hW hV φ hZ).hom (yoneda.map jU))
      A.hom (gluedOver hU hW hV φ hZ).hom (yoneda.map jU) :=
  IsPullback.of_iso_pullback
    ⟨by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (gluedRestrictLeftIso hU hW hV φ hZ hVp).inv.left ≫
            pullback.snd (gluedOver hU hW hV φ hZ).hom (yoneda.map jU) = A.hom from
          Over.w _]⟩
    ((Over.forget (yoneda.obj U)).mapIso (gluedRestrictLeftIso hU hW hV φ hZ hVp)).symm
    rfl (Over.w (gluedRestrictLeftIso hU hW hV φ hZ hVp).inv)

/-- **The structure morphism of the second presheaf glued is a base change of the structure
morphism of the glued presheaf** along the Yoneda image of `jW`. -/
theorem isPullback_gluedRestrictRight {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    IsPullback ((gluedRestrictRightIso hU hW hV φ hZ hVp).inv.left ≫
        pullback.fst (gluedOver hU hW hV φ hZ).hom (yoneda.map jW))
      Bb.hom (gluedOver hU hW hV φ hZ).hom (yoneda.map jW) :=
  IsPullback.of_iso_pullback
    ⟨by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        show (gluedRestrictRightIso hU hW hV φ hZ hVp).inv.left ≫
            pullback.snd (gluedOver hU hW hV φ hZ).hom (yoneda.map jW) = Bb.hom from
          Over.w _]⟩
    ((Over.forget (yoneda.obj W)).mapIso (gluedRestrictRightIso hU hW hV φ hZ hVp)).symm
    rfl (Over.w (gluedRestrictRightIso hU hW hV φ hZ hVp).inv)

/-! #### The two restrictions agree over `V` -/

/-- `CategoryTheory.SubterminalGlueing.gluedRestrictLeftIso` is the comparison
`CategoryTheory.SubterminalGlueing.gluedRestrictLeftHom`, read in the slice over the
representable presheaf of `U`. -/
@[simp]
theorem gluedRestrictLeftIso_hom_left {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) :
    (gluedRestrictLeftIso hU hW hV φ hZ hVp).hom.left = gluedRestrictLeftHom hU hW hV φ hZ jU :=
  rfl

/-- The structure morphism of the glued presheaf over the representable presheaf of the terminal
object. -/
@[simp]
theorem gluedOver_hom : (gluedOver hU hW hV φ hZ).hom = gluedToTerminal hU hW hV φ hZ :=
  rfl

/-- The comparison from the restriction to `U` of the glued presheaf, read on sections: it reads
off the first component of the compatible pair and carries it back along the graph. -/
theorem gluedRestrictLeftHom_app_apply (jU : U ⟶ Z) (X : Cᵒᵖ)
    (z : (pullback (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).obj X) :
    (gluedRestrictLeftHom hU hW hV φ hZ jU).app X z =
      A.left.map (prod.lift
          ((pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z)
          (𝟙 X.unop)).op
        (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z).1.1) :=
  rfl

/-- Base change along `j` of a morphism of `Over F`, read on sections of the base change: it acts
by the morphism on the first projection and leaves the second projection unchanged. -/
private theorem pullback_map_fst_snd_apply {D : Type u} [Category.{v} D]
    {F E : Dᵒᵖ ⥤ Type v} (j : E ⟶ F) {G H : Over F}
    (f : G ⟶ H) (X : Dᵒᵖ) (z : (pullback G.hom j).obj X) :
    (pullback.fst H.hom j).app X (((Over.pullback j).map f).left.app X z) =
        f.left.app X ((pullback.fst G.hom j).app X z) ∧
      (pullback.snd H.hom j).app X (((Over.pullback j).map f).left.app X z) =
        (pullback.snd G.hom j).app X z :=
  ⟨ConcreteCategory.congr_hom (NatTrans.congr_app (Over.pullback_map_left_comp_fst j f) X) z,
    ConcreteCategory.congr_hom (NatTrans.congr_app (Over.w ((Over.pullback j).map f)) X) z⟩

/-- The comparison from the restriction to `W` of the glued presheaf, read on sections: it reads
off the second component of the compatible pair and carries it back along the graph. -/
theorem gluedRestrictRightIso_hom_left_app {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW) (X : Cᵒᵖ)
    (z : (pullback (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW)).obj X) :
    (gluedRestrictRightIso hU hW hV φ hZ hVp).hom.left.app X z =
      Bb.left.map (prod.lift
          ((pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW)).app X z)
          (𝟙 X.unop)).op
        (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW)).app X z).1.2) := by
  obtain ⟨hfst, hsnd⟩ := pullback_map_fst_snd_apply (yoneda.map jW)
    (gluedOverSymmIso hU hW hV φ hZ).hom X z
  refine Eq.trans (gluedRestrictLeftHom_app_apply hW hU hV φ.symm hZ jW X
    (((Over.pullback (yoneda.map jW)).map
      (gluedOverSymmIso hU hW hV φ hZ).hom).left.app X z)) ?_
  erw [hfst, hsnd]
  rfl

/-- The identification over `V` of the two presheaves glued, read through the base changes: it
takes the first projection of a section of the base change of `A` to the first projection of its
image under the given identification. -/
theorem glueingRestrictIso_hom_app_apply (T : C)
    (z : (pullback A.hom (yoneda.map iU)).obj (op (V ⨯ T))) :
    (glueingRestrictIso hU hW hV φ).hom.app (op T)
        ((pullback.fst A.hom (yoneda.map iU)).app (op (V ⨯ T)) z) =
      (pullback.fst Bb.hom (yoneda.map iW)).app (op (V ⨯ T))
        (φ.hom.left.app (op (V ⨯ T)) z) := by
  have hinv : (prodRestrictPullbackIso iU hU hV A).inv.app (op T)
      ((pullback.fst A.hom (yoneda.map iU)).app (op (V ⨯ T)) z) = z :=
    ConcreteCategory.congr_hom
      ((prodRestrictPullbackIso iU hU hV A).hom_inv_id_app (op T)) z
  have hcomp : (glueingRestrictIso hU hW hV φ).hom.app (op T)
        ((pullback.fst A.hom (yoneda.map iU)).app (op (V ⨯ T)) z) =
      (pullback.fst Bb.hom (yoneda.map iW)).app (op (V ⨯ T))
        (φ.hom.left.app (op (V ⨯ T))
          ((prodRestrictPullbackIso iU hU hV A).inv.app (op T)
            ((pullback.fst A.hom (yoneda.map iU)).app (op (V ⨯ T)) z))) := rfl
  rw [hcomp, hinv]

/-- **Two sections matching under the identification over `V` stay matched over an object lying
over `V`.** The image under `φ` of a lift of the restriction of the first along the graph of
`T ⟶ U` is, through the first projection, the corresponding restriction of the second. -/
theorem pullback_fst_app_hom_left {T : C} (p : T ⟶ V) (a : A.left.obj (op (U ⨯ T)))
    (b : Bb.left.obj (op (W ⨯ T)))
    (hab : A.left.map (prod.map iU (𝟙 T)).op a =
      (glueingRestrictIso hU hW hV φ).inv.app (op T) (Bb.left.map (prod.map iW (𝟙 T)).op b))
    (z : (pullback A.hom (yoneda.map iU)).obj (op T))
    (hz : (pullback.fst A.hom (yoneda.map iU)).app (op T) z =
      A.left.map (prod.lift (p ≫ iU) (𝟙 T)).op a) :
    (pullback.fst Bb.hom (yoneda.map iW)).app (op T) (φ.hom.left.app (op T) z) =
      Bb.left.map (prod.lift (p ≫ iW) (𝟙 T)).op b := by
  obtain ⟨y, hy⟩ := (bijective_pullback_fst_app iU hU hV A
    (prod.fst : V ⨯ T ⟶ V)).surjective (A.left.map (prod.map iU (𝟙 T)).op a)
  have hlU : prod.lift p (𝟙 T) ≫ prod.map iU (𝟙 T) = prod.lift (p ≫ iU) (𝟙 T) := by simp
  have hlW : prod.lift p (𝟙 T) ≫ prod.map iW (𝟙 T) = prod.lift (p ≫ iW) (𝟙 T) := by simp
  have hnatA : (pullback.fst A.hom (yoneda.map iU)).app (op T)
        ((pullback A.hom (yoneda.map iU)).map (prod.lift p (𝟙 T)).op y) =
      A.left.map (prod.lift p (𝟙 T)).op
        ((pullback.fst A.hom (yoneda.map iU)).app (op (V ⨯ T)) y) :=
    NatTrans.naturality_apply (pullback.fst A.hom (yoneda.map iU)) (prod.lift p (𝟙 T)).op y
  have hzy : z = (pullback A.hom (yoneda.map iU)).map (prod.lift p (𝟙 T)).op y := by
    refine (bijective_pullback_fst_app iU hU hV A p).injective ?_
    rw [hz, hnatA, hy]
    simp only [← Functor.map_comp_apply, ← op_comp, hlU]
  have hnatφ : φ.hom.left.app (op T)
        ((pullback A.hom (yoneda.map iU)).map (prod.lift p (𝟙 T)).op y) =
      (pullback Bb.hom (yoneda.map iW)).map (prod.lift p (𝟙 T)).op
        (φ.hom.left.app (op (V ⨯ T)) y) :=
    NatTrans.naturality_apply φ.hom.left (prod.lift p (𝟙 T)).op y
  have hnatB : (pullback.fst Bb.hom (yoneda.map iW)).app (op T)
        ((pullback Bb.hom (yoneda.map iW)).map (prod.lift p (𝟙 T)).op
          (φ.hom.left.app (op (V ⨯ T)) y)) =
      Bb.left.map (prod.lift p (𝟙 T)).op
        ((pullback.fst Bb.hom (yoneda.map iW)).app (op (V ⨯ T))
          (φ.hom.left.app (op (V ⨯ T)) y)) :=
    NatTrans.naturality_apply (pullback.fst Bb.hom (yoneda.map iW)) (prod.lift p (𝟙 T)).op _
  have hcond : (glueingRestrictIso hU hW hV φ).hom.app (op T)
      (A.left.map (prod.map iU (𝟙 T)).op a) = Bb.left.map (prod.map iW (𝟙 T)).op b := by
    rw [hab]
    exact ConcreteCategory.congr_hom
      ((glueingRestrictIso hU hW hV φ).inv_hom_id_app (op T)) _
  rw [hzy, hnatφ, hnatB, ← glueingRestrictIso_hom_app_apply hU hW hV φ T y, hy, hcond]
  simp only [← Functor.map_comp_apply, ← op_comp, hlW]

/-- **The two comparison isomorphisms of the restrictions of the glued presheaf are compatible
over `V`.** Base changed to `V`, the comparison over `U` followed by the given identification is
the comparison isomorphism of the square followed by the comparison over `W`. -/
theorem gluedRestrict_comm {jU : U ⟶ Z} {jW : W ⟶ Z} (hVp : IsPullback iU iW jU jW) :
    (Over.pullback (yoneda.map iU)).map (gluedRestrictLeftIso hU hW hV φ hZ hVp).hom ≫ φ.hom =
      (Over.pullbackSquareObjIso (yoneda_map_comm hVp.w) (gluedOver hU hW hV φ hZ)).hom ≫
        (Over.pullback (yoneda.map iW)).map (gluedRestrictRightIso hU hW hV φ hZ hVp).hom := by
  refine Over.hom_ext_pullback_fst (yoneda.map iW) (NatTrans.ext (funext fun X =>
    ConcreteCategory.hom_ext _ _ fun r => ?_))
  have hfstU := (pullback_map_fst_snd_apply (yoneda.map iU)
    (gluedRestrictLeftIso hU hW hV φ hZ hVp).hom X r).1
  have hfstW := (pullback_map_fst_snd_apply (yoneda.map iW)
    (gluedRestrictRightIso hU hW hV φ hZ hVp).hom X
    ((Over.pullbackSquareObjIso (yoneda_map_comm hVp.w) (gluedOver hU hW hV φ hZ)).hom.left.app X
      r)).1
  have hsqf : (pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW)).app X
        ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW))
            (yoneda.map iW)).app X
          ((Over.pullbackSquareObjIso (yoneda_map_comm hVp.w)
            (gluedOver hU hW hV φ hZ)).hom.left.app X r)) =
      (pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X
        ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
          (yoneda.map iU)).app X r) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (Over.pullbackSquareObjIso_hom_left_fst (yoneda_map_comm hVp.w)
        (gluedOver hU hW hV φ hZ)) X) r
  have hright : (pullback.fst Bb.hom (yoneda.map iW)).app X
        (((Over.pullback (yoneda.map iW)).map
            (gluedRestrictRightIso hU hW hV φ hZ hVp).hom).left.app X
          ((Over.pullbackSquareObjIso (yoneda_map_comm hVp.w)
            (gluedOver hU hW hV φ hZ)).hom.left.app X r)) =
      Bb.left.map (prod.lift
          ((pullback.snd (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
            (yoneda.map iU)).app X r ≫ iW) (𝟙 X.unop)).op
        (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X
          ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
            (yoneda.map iU)).app X r)).1.2) := by
    erw [hfstW, gluedRestrictRightIso_hom_left_app, hsqf]
    exact congrArg (fun q => Bb.left.map (prod.lift q (𝟙 X.unop)).op
      (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X
        ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
          (yoneda.map iU)).app X r)).1.2)) (hW _ _)
  have hz : (pullback.fst A.hom (yoneda.map iU)).app X
        (((Over.pullback (yoneda.map iU)).map
          (gluedRestrictLeftIso hU hW hV φ hZ hVp).hom).left.app X r) =
      A.left.map (prod.lift
          ((pullback.snd (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
            (yoneda.map iU)).app X r ≫ iU) (𝟙 X.unop)).op
        (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X
          ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
            (yoneda.map iU)).app X r)).1.1) := by
    erw [hfstU, gluedRestrictLeftHom_app_apply]
    exact congrArg (fun q => A.left.map (prod.lift q (𝟙 X.unop)).op
      (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X
        ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
          (yoneda.map iU)).app X r)).1.1)) (hU _ _)
  exact (pullback_fst_app_hom_left hU hW hV φ
    ((pullback.snd (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
      (yoneda.map iU)).app X r)
    (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X
      ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
        (yoneda.map iU)).app X r)).1.1)
    (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X
      ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
        (yoneda.map iU)).app X r)).1.2)
    (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X
      ((pullback.fst (pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU))
        (yoneda.map iU)).app X r)).2) _ hz).trans hright.symm

/-! #### Naturality of the two restrictions -/

/-- The morphism of glued presheaves over the representable presheaf of the terminal object
induced by a morphism of glueing data: the compatibility is automatic, that presheaf being
terminal. -/
noncomputable def gluedOverMap
    (h : (Over.pullback (yoneda.map iU)).map a ≫ φ'.hom =
      φ.hom ≫ (Over.pullback (yoneda.map iW)).map b) :
    gluedOver hU hW hV φ hZ ⟶ gluedOver hU hW hV φ' hZ :=
  Over.homMk (gluedPresheafMap hU hW hV φ φ' h) ((hZ.isTerminalObj yoneda Z).hom_ext _ _)

/-- **The comparison of the restriction to `U` is natural in the glueing datum.** -/
theorem gluedRestrictLeftIso_naturality {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW)
    (h : (Over.pullback (yoneda.map iU)).map a ≫ φ'.hom =
      φ.hom ≫ (Over.pullback (yoneda.map iW)).map b) :
    (Over.pullback (yoneda.map jU)).map (gluedOverMap hU hW hV φ φ' hZ h) ≫
        (gluedRestrictLeftIso hU hW hV φ' hZ hVp).hom =
      (gluedRestrictLeftIso hU hW hV φ hZ hVp).hom ≫ a := by
  refine Over.OverMorphism.ext (NatTrans.ext (funext fun X =>
    ConcreteCategory.hom_ext _ _ fun z => ?_))
  obtain ⟨hfst, hsnd⟩ := pullback_map_fst_snd_apply (yoneda.map jU)
    (gluedOverMap hU hW hV φ φ' hZ h) X z
  refine Eq.trans (gluedRestrictLeftHom_app_apply hU hW hV φ' hZ jU X
    (((Over.pullback (yoneda.map jU)).map
      (gluedOverMap hU hW hV φ φ' hZ h)).left.app X z)) ?_
  erw [hfst, hsnd]
  exact (NatTrans.naturality_apply a.left
    (prod.lift ((pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jU)).app X z)
      (𝟙 X.unop)).op _).symm

/-- **The comparison of the restriction to `W` is natural in the glueing datum.** -/
theorem gluedRestrictRightIso_naturality {jU : U ⟶ Z} {jW : W ⟶ Z}
    (hVp : IsPullback iU iW jU jW)
    (h : (Over.pullback (yoneda.map iU)).map a ≫ φ'.hom =
      φ.hom ≫ (Over.pullback (yoneda.map iW)).map b) :
    (Over.pullback (yoneda.map jW)).map (gluedOverMap hU hW hV φ φ' hZ h) ≫
        (gluedRestrictRightIso hU hW hV φ' hZ hVp).hom =
      (gluedRestrictRightIso hU hW hV φ hZ hVp).hom ≫ b := by
  refine Over.OverMorphism.ext (NatTrans.ext (funext fun X =>
    ConcreteCategory.hom_ext _ _ fun z => ?_))
  obtain ⟨hfst, hsnd⟩ := pullback_map_fst_snd_apply (yoneda.map jW)
    (gluedOverMap hU hW hV φ φ' hZ h) X z
  have hR : ((gluedRestrictRightIso hU hW hV φ hZ hVp).hom ≫ b).left.app X z =
      b.left.app X (Bb.left.map (prod.lift
          ((pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW)).app X z)
          (𝟙 X.unop)).op
        (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW)).app X z).1.2)) :=
    congrArg (fun y => b.left.app X y)
      (gluedRestrictRightIso_hom_left_app hU hW hV φ hZ hVp X z)
  refine Eq.trans (gluedRestrictRightIso_hom_left_app hU hW hV φ' hZ hVp X
    (((Over.pullback (yoneda.map jW)).map
      (gluedOverMap hU hW hV φ φ' hZ h)).left.app X z)) ?_
  erw [hfst, hsnd, hR]
  exact (NatTrans.naturality_apply b.left
    (prod.lift ((pullback.snd (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW)).app X z)
      (𝟙 X.unop)).op
    (((pullback.fst (gluedToTerminal hU hW hV φ hZ) (yoneda.map jW)).app X z).1.2)).symm

end Restriction

end SubterminalGlueing

end CategoryTheory

end
