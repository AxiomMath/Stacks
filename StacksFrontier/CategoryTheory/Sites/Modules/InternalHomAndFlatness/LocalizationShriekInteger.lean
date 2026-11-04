module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.AbelianLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Localization.AbelianShriekTensor

/-!
# Lower shriek of the constant integer sheaf on a localized topos

Let `F` be a sheaf of sets on a site `C` and let `j : Sh(C)/F ⟶ Sh(C)` be the localization
morphism, presented by the site of elements `C/F`, whose objects are pairs `(U, s)` with
`s ∈ F(U)`, with the topology induced from `J`. Then `j_! ℤ` is the free abelian sheaf `Z_F^#`
on `F`.

## Main definitions

* `Stacks.Sites.Localization.sectionsOfElementsEquiv`: morphisms from the terminal presheaf on
  the site of elements of `F` to a restriction are morphisms out of `F`.
* `Stacks.Sites.Localization.constantIntegerSectionsEquiv`: morphisms from the constant abelian
  presheaf `ℤ` are sections of the underlying presheaf of sets.
* `Stacks.Sites.Localization.shriekConstantIntegerHomEquiv`: the resulting bijection between
  morphisms out of `j_! ℤ` and morphisms out of `Z_F^#`.

## Main results

* `Stacks.Sites.Localization.localizationShriek_constantInteger_iso_freeAbSheaf`: the
  identification `j_! ℤ ≅ Z_F^#`.

## References

* [Stacks Project, Tag 0EYY](https://stacks.math.columbia.edu/tag/0EYY)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791), the presentation of the
  localization by the site of elements.
* [Stacks Project, Tag 03AC](https://stacks.math.columbia.edu/tag/03AC), the free abelian sheaf.
* [Stacks Project, Tag 04BG](https://stacks.math.columbia.edu/tag/04BG), lower shriek.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe w u

namespace Stacks.Sites.Localization

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

attribute [local instance] localizationProjection_isContinuous

/-- The canonical section of the terminal presheaf of sets over an object. -/
noncomputable def terminalSection (D : Type u) [SmallCategory D] (X : Dᵒᵖ) :
    (⊤_ (Dᵒᵖ ⥤ Type u)).obj X :=
  (terminal.from ((Functor.const Dᵒᵖ).obj (PUnit : Type u))).app X PUnit.unit

/-- The terminal presheaf of sets has exactly one section over each object. -/
theorem terminalPresheaf_subsingleton {D : Type u} [SmallCategory D] (X : Dᵒᵖ) :
    Subsingleton ((⊤_ (Dᵒᵖ ⥤ Type u)).obj X) :=
  have ht : IsTerminal ((⊤_ (Dᵒᵖ ⥤ Type u)).obj X) :=
    IsTerminal.isTerminalObj ((evaluation Dᵒᵖ (Type u)).obj X) _ terminalIsTerminal
  (Types.isTerminalEquivUnique _ ht).instSubsingleton

section Elements

variable (F G : Cᵒᵖ ⥤ Type u)

/-- The value at a section `x` of `F` over `U` of the morphism of presheaves of sets attached to
a morphism from the terminal presheaf on the site of elements of `F`. -/
noncomputable def elementSectionValue
    (s : (⊤_ ((CostructuredArrow yoneda F)ᵒᵖ ⥤ Type u)) ⟶
      (((Functor.whiskeringLeft (CostructuredArrow yoneda F)ᵒᵖ Cᵒᵖ (Type u)).obj
        (CostructuredArrow.proj yoneda F).op).obj G)) {U : Cᵒᵖ} (x : F.obj U) : G.obj U :=
  (s.app (op (CostructuredArrow.mk (yonedaEquiv.symm x))))
    (terminalSection (CostructuredArrow yoneda F) (op (CostructuredArrow.mk (yonedaEquiv.symm x))))

/-- Morphisms from the terminal presheaf of sets on the site of elements of `F` to the restriction
of `G` are morphisms `F ⟶ G`. -/
noncomputable def sectionsOfElementsEquiv :
    ((⊤_ ((CostructuredArrow yoneda F)ᵒᵖ ⥤ Type u)) ⟶
      (((Functor.whiskeringLeft (CostructuredArrow yoneda F)ᵒᵖ Cᵒᵖ (Type u)).obj
        (CostructuredArrow.proj yoneda F).op).obj G)) ≃ (F ⟶ G) := by
  classical
  refine Equiv.mk ?toFun ?invFun ?left_inv ?right_inv
  · intro s
    let app : ∀ U, F.obj U ⟶ G.obj U := fun U ↦ ↾(fun x ↦ elementSectionValue F G s x)
    refine { app := app, naturality := ?_ }
    intro U V f
    ext x
    dsimp [elementSectionValue]
    let X := CostructuredArrow.mk (yonedaEquiv.symm x)
    let Y := CostructuredArrow.mk (yonedaEquiv.symm (F.map f x))
    have hw : yoneda.map f.unop ≫ X.hom = Y.hom :=
      yonedaEquiv_symm_naturality_left f.unop F x
    let h : Y ⟶ X := CostructuredArrow.homMk f.unop hw
    have hs := NatTrans.naturality_apply s h.op
      (terminalSection (CostructuredArrow yoneda F) (op X))
    have := terminalPresheaf_subsingleton (op Y : (CostructuredArrow yoneda F)ᵒᵖ)
    have ht : ((⊤_ ((CostructuredArrow yoneda F)ᵒᵖ ⥤ Type u)).map h.op)
        (terminalSection (CostructuredArrow yoneda F) (op X)) =
          terminalSection (CostructuredArrow yoneda F) (op Y) := Subsingleton.elim _ _
    rw [ht] at hs
    simpa [elementSectionValue, app, X, Y, h] using hs
  · intro f
    let app : ∀ X, (⊤_ ((CostructuredArrow yoneda F)ᵒᵖ ⥤ Type u)).obj X ⟶
        ((((Functor.whiskeringLeft (CostructuredArrow yoneda F)ᵒᵖ Cᵒᵖ (Type u)).obj
          (CostructuredArrow.proj yoneda F).op).obj G).obj X) :=
      fun X ↦ ↾(fun _ ↦ f.app (op X.unop.left) (yonedaEquiv X.unop.hom))
    refine { app := app, naturality := ?_ }
    intro X Y g
    ext x
    dsimp
    have hnat := NatTrans.naturality_apply f g.unop.left.op (yonedaEquiv X.unop.hom)
    have hsec := yonedaEquiv_naturality X.unop.hom g.unop.left
    rw [CostructuredArrow.w g.unop] at hsec
    simp [app, ← hsec]
  · intro s
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    dsimp
    let Z := CostructuredArrow.mk (yonedaEquiv.symm (yonedaEquiv X.unop.hom))
    have hw : yoneda.map (𝟙 X.unop.left) ≫ X.unop.hom = Z.hom := by simp [Z]
    let h : Z ⟶ X.unop := CostructuredArrow.homMk (𝟙 _) hw
    have hs := NatTrans.naturality_apply s h.op (terminalSection _ X)
    have hZ : terminalSection _ (op Z) =
        ((⊤_ ((CostructuredArrow yoneda F)ᵒᵖ ⥤ Type u)).map h.op) (terminalSection _ X) :=
      @Subsingleton.elim _
        (terminalPresheaf_subsingleton (D := CostructuredArrow yoneda F) (op Z)) _ _
    obtain rfl : terminalSection _ X = x := @Subsingleton.elim _
      (terminalPresheaf_subsingleton (D := CostructuredArrow yoneda F) X) _ _
    calc
      (s.app (op Z)) (terminalSection _ (op Z)) = (s.app (op Z))
          (((⊤_ ((CostructuredArrow yoneda F)ᵒᵖ ⥤ Type u)).map h.op) (terminalSection _ X)) :=
            congrArg (s.app (op Z)) hZ
      _ = ((((Functor.whiskeringLeft (CostructuredArrow yoneda F)ᵒᵖ Cᵒᵖ (Type u)).obj
            (CostructuredArrow.proj yoneda F).op).obj G).map h.op)
            ((s.app X) (terminalSection _ X)) := by simp [h, Z]
      _ = (s.app X) (terminalSection _ X) := by
            change G.map (𝟙 X.unop.left).op ((s.app X) (terminalSection _ X)) = _
            simp
  · intro f
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    dsimp
    simp [elementSectionValue, CostructuredArrow.hom, Equiv.apply_symm_apply]

/-- `sectionsOfElementsEquiv` is natural in the target presheaf of sets. -/
theorem sectionsOfElementsEquiv_natural {G' : Cᵒᵖ ⥤ Type u} (q : G ⟶ G')
    (s : (⊤_ ((CostructuredArrow yoneda F)ᵒᵖ ⥤ Type u)) ⟶
      (((Functor.whiskeringLeft (CostructuredArrow yoneda F)ᵒᵖ Cᵒᵖ (Type u)).obj
        (CostructuredArrow.proj yoneda F).op).obj G)) :
    sectionsOfElementsEquiv F G' (s ≫
      (((Functor.whiskeringLeft (CostructuredArrow yoneda F)ᵒᵖ Cᵒᵖ (Type u)).obj
        (CostructuredArrow.proj yoneda F).op).map q)) =
      sectionsOfElementsEquiv F G s ≫ q := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end Elements

section ConstantInteger

variable {D : Type u} [SmallCategory D]

/-- Morphisms from the constant abelian presheaf `ℤ` to an abelian presheaf `G` are sections of
the underlying presheaf of sets of `G` over the terminal presheaf. -/
noncomputable def constantIntegerSectionsEquiv (G : Dᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ G) ≃
      (⊤_ (Dᵒᵖ ⥤ Type u) ⟶ G ⋙ forget AddCommGrpCat.{u}) := by
  classical
  let E := AddCommGrpCat.coyonedaObjIsoForget
  refine Equiv.mk ?_ ?_ ?_ ?_
  · intro α
    let app : ∀ X, (⊤_ (Dᵒᵖ ⥤ Type u)).obj X ⟶ (G ⋙ forget AddCommGrpCat).obj X :=
      fun X ↦ ↾(fun _ ↦ (E.hom.app (G.obj X)) (α.app X))
    refine { app := app, naturality := ?_ }
    intro X Y f
    ext x
    have hα : α.app X ≫ G.map f = α.app Y := by
      simpa using (NatTrans.naturality α f).symm
    have hval : (E.hom.app (G.obj Y)) (α.app Y) =
        (forget AddCommGrpCat).map (G.map f) ((E.hom.app (G.obj X)) (α.app X)) := by
      rw [← hα]
      exact congrArg (fun k ↦ k (α.app X)) (E.hom.naturality (G.map f))
    change app Y (((⊤_ (Dᵒᵖ ⥤ Type u)).map f) x) = (G ⋙ forget AddCommGrpCat).map f (app X x)
    simpa [app] using hval
  · intro s
    let app : ∀ X, ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ))).obj X ⟶ G.obj X :=
      fun X ↦ (E.inv.app (G.obj X)) (s.app X (terminalSection D X))
    refine { app := app, naturality := ?_ }
    intro X Y f
    have hsec : (s.app Y) (terminalSection D Y) =
        (G ⋙ forget AddCommGrpCat).map f ((s.app X) (terminalSection D X)) := by
      have hs := NatTrans.naturality_apply s f (terminalSection D X)
      have ht : ((⊤_ (Dᵒᵖ ⥤ Type u)).map f) (terminalSection D X) = terminalSection D Y :=
        @Subsingleton.elim _ (terminalPresheaf_subsingleton (D := D) Y) _ _
      rwa [ht] at hs
    have hE' := congrArg (fun k ↦ k (app X)) (E.hom.naturality (G.map f))
    have hinj : Function.Injective (E.hom.app (G.obj Y)) := fun a b hab ↦ by
      simpa using congrArg (E.inv.app (G.obj Y)) hab
    apply hinj
    calc
      (E.hom.app (G.obj Y)) (app Y) = (s.app Y) (terminalSection D Y) := by simp [app]
      _ = (G ⋙ forget AddCommGrpCat).map f ((s.app X) (terminalSection D X)) := hsec
      _ = (E.hom.app (G.obj Y)) (app X ≫ G.map f) := by simpa [app] using hE'.symm
  · intro α
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro z
    simp [E]
  · intro s
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    calc
      ((E.hom.app (G.obj X)) ((E.inv.app (G.obj X)) (s.app X (terminalSection D X)))) =
          (s.app X) (terminalSection D X) := by simp [E]
      _ = (s.app X) x := congrArg (s.app X)
        (@Subsingleton.elim _ (terminalPresheaf_subsingleton X) (terminalSection D X) x)

/-- `constantIntegerSectionsEquiv` is natural in the abelian presheaf. -/
theorem constantIntegerSectionsEquiv_natural {G G' : Dᵒᵖ ⥤ AddCommGrpCat.{u}} (q : G ⟶ G')
    (α : (Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ G) :
    constantIntegerSectionsEquiv G' (α ≫ q) = constantIntegerSectionsEquiv G α ≫
      Functor.whiskerRight q (forget AddCommGrpCat.{u}) := by
  apply NatTrans.ext
  funext X
  apply ConcreteCategory.hom_ext
  intro x
  dsimp [constantIntegerSectionsEquiv]
  show (AddCommGrpCat.coyonedaObjIsoForget.hom.app (G'.obj X)) (α.app X ≫ q.app X) = _
  simpa using congrArg (fun k ↦ k (α.app X))
    (AddCommGrpCat.coyonedaObjIsoForget.hom.naturality (q.app X))

end ConstantInteger

/-- An object is determined by the functor it corepresents: a family of bijections
`(A ⟶ X) ≃ (B ⟶ X)` natural in `X` gives `A ≅ B`. -/
noncomputable def isoOfCorepresentingEquiv {D : Type w} [Category.{u} D] (A B : D)
    (e : ∀ X : D, (A ⟶ X) ≃ (B ⟶ X))
    (hnat : ∀ {X Y : D} (q : X ⟶ Y) (f : A ⟶ X), e Y (f ≫ q) = e X f ≫ q) : A ≅ B := by
  let h : A ⟶ B := (e B).symm (𝟙 B)
  let g : B ⟶ A := e A (𝟙 A)
  refine ⟨h, g, ?_, ?_⟩
  · apply (e A).injective
    rw [hnat g h]
    simp [h, g]
  · rw [← hnat h (𝟙 A)]
    simp [h]

/-- Morphisms out of the constant sheaf `ℤ` on the site of elements of `F` are morphisms out of
the sheafification of the constant presheaf `ℤ`. -/
noncomputable def constantSheafPresentationEquiv (F : Sheaf J (Type u))
    (G : Sheaf (localizationTopology J F) AddCommGrpCat.{u}) :
    ((constantSheaf (localizationTopology J F) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ G) ≃
      ((presheafToSheaf (localizationTopology J F) AddCommGrpCat.{u}).obj
        ((Functor.const (CostructuredArrow yoneda F.obj)ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ G) :=
  Equiv.refl _

/-- `constantSheafPresentationEquiv` commutes with postcomposition. -/
theorem constantSheafPresentationEquiv_natural (F : Sheaf J (Type u))
    {G G' : Sheaf (localizationTopology J F) AddCommGrpCat.{u}} (q : G ⟶ G')
    (f : (constantSheaf (localizationTopology J F) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ G) :
    constantSheafPresentationEquiv J F G' (f ≫ q) =
      constantSheafPresentationEquiv J F G f ≫ q :=
  rfl

/-- The underlying presheaf of sets of the inverse image of `H` along the projection from the
site of elements of `F` is the restriction of the underlying presheaf of sets of `H`, as a
bijection on morphisms from the terminal presheaf. -/
noncomputable def restrictedUnderlyingEquiv (F : Sheaf J (Type u))
    (H : Sheaf J AddCommGrpCat.{u}) :
    ((⊤_ ((CostructuredArrow yoneda F.obj)ᵒᵖ ⥤ Type u)) ⟶
        ((sheafToPresheaf (localizationTopology J F) AddCommGrpCat.{u}).obj
          ((Stacks.Sites.abelianInverseImage (localizationProjection J F)
            (localizationTopology J F) J).obj H)) ⋙ forget AddCommGrpCat.{u}) ≃
      ((⊤_ ((CostructuredArrow yoneda F.obj)ᵒᵖ ⥤ Type u)) ⟶
        (((Functor.whiskeringLeft (CostructuredArrow yoneda F.obj)ᵒᵖ Cᵒᵖ (Type u)).obj
          (CostructuredArrow.proj yoneda F.obj).op).obj
            (H.obj ⋙ forget AddCommGrpCat.{u}))) :=
  Equiv.refl _

/-- `restrictedUnderlyingEquiv` carries the restriction of a morphism of abelian sheaves to the
restriction of its underlying morphism of presheaves of sets. -/
theorem restrictedUnderlyingEquiv_natural (F : Sheaf J (Type u))
    {H H' : Sheaf J AddCommGrpCat.{u}} (q : H ⟶ H')
    (s : (⊤_ ((CostructuredArrow yoneda F.obj)ᵒᵖ ⥤ Type u)) ⟶
        ((sheafToPresheaf (localizationTopology J F) AddCommGrpCat.{u}).obj
          ((Stacks.Sites.abelianInverseImage (localizationProjection J F)
            (localizationTopology J F) J).obj H)) ⋙ forget AddCommGrpCat.{u}) :
    restrictedUnderlyingEquiv J F H'
        (s ≫ Functor.whiskerRight
          ((sheafToPresheaf (localizationTopology J F) AddCommGrpCat.{u}).map
            ((Stacks.Sites.abelianInverseImage (localizationProjection J F)
              (localizationTopology J F) J).map q)) (forget AddCommGrpCat.{u})) =
      restrictedUnderlyingEquiv J F H s ≫
        (((Functor.whiskeringLeft (CostructuredArrow yoneda F.obj)ᵒᵖ Cᵒᵖ (Type u)).obj
          (CostructuredArrow.proj yoneda F.obj).op).map
            (Functor.whiskerRight ((sheafToPresheaf J AddCommGrpCat.{u}).map q)
              (forget AddCommGrpCat.{u}))) :=
  rfl

/-- The chain of bijections identifying maps out of `j_! ℤ` with maps out of the free abelian
sheaf on `F`. -/
noncomputable def shriekConstantIntegerHomEquiv (F : Sheaf J (Type u))
    (H : Sheaf J AddCommGrpCat.{u}) :
    ((Stacks.Sites.abelianShriek (localizationProjection J F) (localizationTopology J F) J).obj
        ((constantSheaf (localizationTopology J F) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ H) ≃
      ((Presheaf.freeAbelianSheaf J).obj F.obj ⟶ H) :=
  ((Stacks.Sites.abelianShriekAdjunction (localizationProjection J F)
        (localizationTopology J F) J).homEquiv _ H).trans
    ((constantSheafPresentationEquiv J F _).trans
    (((sheafificationAdjunction (localizationTopology J F) AddCommGrpCat.{u}).homEquiv _ _).trans
      ((constantIntegerSectionsEquiv _).trans
        ((restrictedUnderlyingEquiv J F H).trans
          ((sectionsOfElementsEquiv F.obj (H.obj ⋙ forget AddCommGrpCat.{u})).trans
            ((Presheaf.freeAbelianSheafAdj J).homEquiv F.obj H).symm)))))

/-- `shriekConstantIntegerHomEquiv` is natural in the target abelian sheaf. -/
theorem shriekConstantIntegerHomEquiv_natural (F : Sheaf J (Type u))
    {H H' : Sheaf J AddCommGrpCat.{u}} (q : H ⟶ H')
    (f : (Stacks.Sites.abelianShriek (localizationProjection J F)
        (localizationTopology J F) J).obj
      ((constantSheaf (localizationTopology J F) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ H) :
    shriekConstantIntegerHomEquiv J F H' (f ≫ q) =
      shriekConstantIntegerHomEquiv J F H f ≫ q := by
  let j := localizationProjection J F
  let K := localizationTopology J F
  let adj := Stacks.Sites.abelianShriekAdjunction j K J
  simp only [shriekConstantIntegerHomEquiv, Equiv.trans_apply]
  apply ((Presheaf.freeAbelianSheafAdj J).homEquiv F.obj H').injective
  rw [Adjunction.homEquiv_naturality_right (Presheaf.freeAbelianSheafAdj J)]
  simp only [Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right adj f q, constantSheafPresentationEquiv_natural,
    Adjunction.homEquiv_naturality_right, constantIntegerSectionsEquiv_natural,
    restrictedUnderlyingEquiv_natural]
  exact sectionsOfElementsEquiv_natural F.obj _ _ _

/-- For the localization morphism `j : Sh(C)/F ⟶ Sh(C)`, presented by the site of elements
`C/F`, the abelian sheaf `j_! ℤ` is the free abelian sheaf `Z_F^#` on `F`. -/
@[stacks 0EYY "j_shriek_int"]
noncomputable def localizationShriek_constantInteger_iso_freeAbSheaf (F : Sheaf J (Type u)) :
    (Stacks.Sites.abelianShriek (localizationProjection J F)
          (localizationTopology J F) J).obj
        ((constantSheaf (localizationTopology J F) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (Presheaf.freeAbelianSheaf J).obj ((sheafToPresheaf J (Type u)).obj F) :=
  isoOfCorepresentingEquiv _ _ (shriekConstantIntegerHomEquiv J F)
    (fun q f => shriekConstantIntegerHomEquiv_natural J F q f)

add_to_stacks 0EYY "j_!(j⁻¹ H) = j_! ℤ ⊗ H, for a site of arbitrary size: sheafification, \
the monoidality of the two sheafification localizers and the left Kan extensions along \
C/F ⥤ C are instance hypotheses here, and every one of them holds at the hypotheses of \
the source -- see jShriekPullbackIsoShriekUnitTensor" jShriekPullbackIsoTensor

end Stacks.Sites.Localization
