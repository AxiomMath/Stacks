module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedSubschemeSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections

/-!
# Comparisons of étale global sections are unique, and pass to abelian coefficients

For a morphism of schemes `c : T ⟶ Z`, several natural transformations
`Γ(Z, -) ⟶ Γ(T, c^{-1} -)` of global-sections functors on sheaves of sets appear in this library,
built in different ways (from the unit of the inverse-image adjunction, from the unit of the left
Kan extension and the sheafification map, or from a limit description of global sections). This
file shows that there is only one: global sections of a sheaf of sets are morphisms out of the
terminal sheaf, the terminal sheaf is the constant sheaf on a point, and inverse image carries it
to the terminal sheaf of `T`, whose global sections are a single point. So any statement that one
of them is an isomorphism is a statement about each of them.

The invertibility, on global sections, of the unit of the inverse-image/direct-image adjunction is
then transported from sheaves of sets to abelian sheaves, using that composing with the
forgetful functor of abelian groups commutes with inverse image compatibly with the units
(`Stacks.EtaleCohomology.coefficientPullbackComparison_unit`).

## Main results

* `Stacks.EtaleCohomology.natTrans_Γ_ext` — two transformations `Γ_J ⟶ F ⋙ Γ_K` agree as soon as
  `Γ_K (F P)` is a subsingleton for the constant sheaf `P` on a point.
* `Stacks.EtaleCohomology.eq_smallEtaleGlobalSectionsComparison` — every natural transformation
  `Γ(Z, -) ⟶ Γ(T, c^{-1} -)` on sheaves of sets is
  `Stacks.EtaleCohomology.smallEtaleGlobalSectionsComparison c`.
* `Stacks.EtaleCohomology.isIso_Γ_map_etaleAbelianUnit_of_isIso` — if some such transformation is
  an isomorphism, the unit of the abelian inverse-image/direct-image adjunction along `c` is
  bijective on global sections, for every abelian sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u v₁ v₂ u₁ u₂

namespace Stacks.EtaleCohomology

section Generic

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- The constant presheaf on a point is a terminal presheaf. -/
def isTerminal_const_punit :
    IsTerminal ((Functor.const Cᵒᵖ).obj (PUnit.{w + 1} : Type w)) :=
  IsTerminal.ofUniqueHom (fun _ ↦ { app := fun _ ↦ TypeCat.ofHom fun _ ↦ PUnit.unit })
    (fun _ _ ↦ by ext; rfl)

/-- The constant sheaf on a point is a terminal sheaf: sheafification is left exact. -/
def isTerminal_constantSheaf_punit [HasSheafify J (Type w)] :
    IsTerminal ((constantSheaf J (Type w)).obj PUnit.{w + 1}) :=
  IsTerminal.isTerminalObj (presheafToSheaf J (Type w)) _ (isTerminal_const_punit.{w})

/-- A terminal object of the category of types has at most one element. -/
lemma subsingleton_of_isTerminal_type {X : Type w} (hX : IsTerminal X) : Subsingleton X :=
  ⟨fun a b ↦ by
    have h := hX.hom_ext (TypeCat.ofHom fun _ : PUnit.{w + 1} ↦ a)
      (TypeCat.ofHom fun _ : PUnit.{w + 1} ↦ b)
    exact congrArg (fun m : PUnit.{w + 1} ⟶ X ↦ m PUnit.unit) h⟩

/-- **Natural transformations out of global sections of sheaves of sets are determined by their
value at the constant sheaf on a point.** Every global section of a sheaf `G` is the image of the
canonical global section of the constant sheaf `P` on a point under a morphism `P ⟶ G`; so two
transformations `Γ_J ⟶ F ⋙ Γ_K` agree everywhere once `Γ_K (F P)` has at most one element. -/
theorem natTrans_Γ_ext [HasSheafify J (Type w)] [HasGlobalSectionsFunctor J (Type w)]
    [HasWeakSheafify K (Type w)] [HasGlobalSectionsFunctor K (Type w)]
    (F : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    (hP : Subsingleton ((Sheaf.Γ K (Type w)).obj (F.obj ((constantSheaf J (Type w)).obj PUnit))))
    (α β : Sheaf.Γ J (Type w) ⟶ F ⋙ Sheaf.Γ K (Type w)) : α = β := by
  ext G x
  set P := (constantSheaf J (Type w)).obj PUnit.{w + 1}
  let xh : P ⟶ G := Sheaf.ΓObjEquivHom J G PUnit x
  set pt := (Sheaf.ΓObjEquivHom J P PUnit).symm (𝟙 P)
  have hx : x = (Sheaf.Γ J (Type w)).map xh pt := by
    have h := Sheaf.ΓObjEquivHom_naturality_symm J xh (𝟙 P)
    rw [Category.id_comp] at h
    rw [← h]
    exact ((Sheaf.ΓObjEquivHom J G PUnit).symm_apply_apply x).symm
  have hα := ConcreteCategory.congr_hom (α.naturality xh) pt
  have hβ := ConcreteCategory.congr_hom (β.naturality xh) pt
  simp only [ConcreteCategory.comp_apply] at hα hβ
  show α.app G x = β.app G x
  rw [hx, hα, hβ, Subsingleton.elim (α.app P pt) (β.app P pt)]

end Generic

section SmallEtale

variable {T Z : Scheme.{u}} (c : T ⟶ Z)

/-- Inverse image of sheaves of sets along `c` carries the constant sheaf on a point to a sheaf
whose global sections have at most one element: composed with the constant sheaf functor it is a
left adjoint of global sections on `T`, hence the constant sheaf functor of `T`. -/
lemma subsingleton_Γ_smallEtaleInverseImage_constantSheaf :
    Subsingleton ((Sheaf.Γ (Scheme.smallEtaleTopology T) (Type (max (u + 1) v₁))).obj
      ((smallEtaleInverseImage.{u, v₁} c).obj
        ((constantSheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v₁))).obj PUnit))) := by
  let e : constantSheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v₁)) ⋙
      smallEtaleInverseImage.{u, v₁} c ≅
        constantSheaf (Scheme.smallEtaleTopology T) (Type (max (u + 1) v₁)) :=
    Adjunction.leftAdjointUniq (Adjunction.ofNatIsoRight
        ((constantSheafΓAdj (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v₁))).comp
          (smallEtaleInverseImageAdjunction.{u, v₁} c))
        (smallEtalePushforwardGammaIso.{u, v₁} c))
      (constantSheafΓAdj (Scheme.smallEtaleTopology T) (Type (max (u + 1) v₁)))
  have hT : IsTerminal ((smallEtaleInverseImage.{u, v₁} c).obj
      ((constantSheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v₁))).obj PUnit)) :=
    (isTerminal_constantSheaf_punit.{max (u + 1) v₁} (Scheme.smallEtaleTopology T)).ofIso
      (e.app PUnit).symm
  exact subsingleton_of_isTerminal_type
    (IsTerminal.isTerminalObj (Sheaf.Γ (Scheme.smallEtaleTopology T) (Type (max (u + 1) v₁)))
      _ hT)

/-- **There is only one comparison of étale global sections along `c`.** Every natural
transformation `Γ(Z, -) ⟶ Γ(T, c^{-1} -)` of functors on sheaves of sets is
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsComparison c`, the map induced by the unit of the
inverse-image/direct-image adjunction. -/
theorem eq_smallEtaleGlobalSectionsComparison
    (α : Sheaf.Γ (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v₁)) ⟶
      smallEtaleInverseImage.{u, v₁} c ⋙
        Sheaf.Γ (Scheme.smallEtaleTopology T) (Type (max (u + 1) v₁))) :
    α = smallEtaleGlobalSectionsComparison.{u, v₁} c :=
  natTrans_Γ_ext _ _ _ (subsingleton_Γ_smallEtaleInverseImage_constantSheaf.{u, v₁} c) _ _

/-- If some comparison `Γ(Z, -) ⟶ Γ(T, c^{-1} -)` of étale global sections of sheaves of sets is
an isomorphism, then the unit of the inverse-image/direct-image adjunction along `c` is bijective
on sections over the terminal object of `Z_étale`, for every sheaf of sets. -/
theorem isIso_unit_app_terminal_of_isIso
    (α : Sheaf.Γ (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v₁)) ⟶
      smallEtaleInverseImage.{u, v₁} c ⋙
        Sheaf.Γ (Scheme.smallEtaleTopology T) (Type (max (u + 1) v₁))) [IsIso α]
    (F : Sheaf (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v₁))) :
    IsIso (((smallEtaleInverseImageAdjunction.{u, v₁} c).unit.app F).hom.app
      (op (terminal Z.Etale))) := by
  rw [eq_smallEtaleGlobalSectionsComparison.{u, v₁} c α] at *
  have h : IsIso ((smallEtaleGlobalSectionsComparison.{u, v₁} c).app F) := inferInstance
  rw [smallEtaleGlobalSectionsComparison, Stacks.Sites.globalSectionsPullbackComparison_app,
    Stacks.Sites.sectionsPullbackComparison_app] at h
  let g := (isTerminalSmallEtaleBaseChangeObjTerminal c).from (terminal T.Etale)
  have : IsIso g :=
    isIso_of_isTerminal terminalIsTerminal (isTerminalSmallEtaleBaseChangeObjTerminal c) g
  have : IsIso g.op := inferInstance
  let a := (Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology Z) (Type (max (u + 1) v₁))
    terminalIsTerminal).hom.app F
  let b := (Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology T) (Type (max (u + 1) v₁))
    terminalIsTerminal).inv.app ((smallEtaleInverseImage.{u, v₁} c).obj F)
  let m := ((smallEtaleInverseImageAdjunction.{u, v₁} c).unit.app F).hom.app
    (op (terminal Z.Etale))
  let n := ((smallEtaleInverseImage.{u, v₁} c).obj F).obj.map g.op
  have hn : IsIso n := Functor.map_isIso ((smallEtaleInverseImage.{u, v₁} c).obj F).obj g.op
  have : IsIso a := (Iso.app (Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology Z)
    (Type (max (u + 1) v₁)) terminalIsTerminal) F).isIso_hom
  have : IsIso b := (Iso.app (Sheaf.ΓNatIsoSheafSections (Scheme.smallEtaleTopology T)
    (Type (max (u + 1) v₁)) terminalIsTerminal)
      ((smallEtaleInverseImage.{u, v₁} c).obj F)).isIso_inv
  change IsIso (a ≫ (m ≫ n) ≫ b) at h
  have h₁ : IsIso ((m ≫ n) ≫ b) := IsIso.of_isIso_comp_left a _
  have h₂ : IsIso (m ≫ n) := IsIso.of_isIso_comp_right _ b
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ m n hn h₂

/-- **Transport of the unit to abelian coefficients.** For an abelian sheaf `G` on `Z_étale`, if
the unit of the inverse-image/direct-image adjunction for sheaves of sets is bijective over the
terminal object at the underlying sheaf of sets of `G`, then so is the unit for abelian sheaves at
`G`: composing with the forgetful functor carries the abelian unit to the set unit followed by an
isomorphism (`Stacks.EtaleCohomology.coefficientPullbackComparison_unit`). -/
theorem isIso_etaleAbelianUnit_app_terminal
    (G : Sheaf (Scheme.smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (h : IsIso (((smallEtaleInverseImageAdjunction.{u, 0} c).unit.app
      ((sheafCompose (Scheme.smallEtaleTopology Z) (forget AddCommGrpCat.{u + 1})).obj G)).hom.app
        (op (terminal Z.Etale)))) :
    IsIso (((etaleAbelianInverseImageDirectImageAdj.{u, 0} c).unit.app G).hom.app
      (op (terminal Z.Etale))) := by
  let φ := coefficientPullbackComparison (smallEtaleBaseChange c) (Scheme.smallEtaleTopology Z)
    (Scheme.smallEtaleTopology T) (forget AddCommGrpCat.{u + 1}) G
  have key := congrArg (fun m ↦ m.hom.app (op (terminal Z.Etale)))
    (coefficientPullbackComparison_unit (smallEtaleBaseChange c) (Scheme.smallEtaleTopology Z)
      (Scheme.smallEtaleTopology T) (forget AddCommGrpCat.{u + 1}) G)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at key
  have : IsIso φ := by
    have := NatIso.isIso_app_of_isIso (coefficientPullbackTwoSquare (smallEtaleBaseChange c)
      (Scheme.smallEtaleTopology Z) (Scheme.smallEtaleTopology T)
      (forget AddCommGrpCat.{u + 1})).natTrans G
    rwa [coefficientPullbackTwoSquare_app] at this
  have : IsIso φ.hom :=
    (inferInstance : IsIso ((sheafToPresheaf (Scheme.smallEtaleTopology T) (Type (u + 1))).map φ))
  have hφ : IsIso (φ.hom.app (op ((smallEtaleBaseChange c).obj (terminal Z.Etale)))) :=
    inferInstance
  have hf : IsIso ((forget AddCommGrpCat.{u + 1}).map
      (((etaleAbelianInverseImageDirectImageAdj.{u, 0} c).unit.app G).hom.app
        (op (terminal Z.Etale)))) := by
    have h₂ : IsIso
        ((((smallEtaleInverseImageAdjunction.{u, 0} c).unit.app
          ((sheafCompose (Scheme.smallEtaleTopology Z)
            (forget AddCommGrpCat.{u + 1})).obj G)).hom.app
            (op (terminal Z.Etale))) ≫
          φ.hom.app (op ((smallEtaleBaseChange c).obj (terminal Z.Etale)))) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _ h hφ
    have key' : (forget AddCommGrpCat.{u + 1}).map
        (((etaleAbelianInverseImageDirectImageAdj.{u, 0} c).unit.app G).hom.app
          (op (terminal Z.Etale))) =
        (((smallEtaleInverseImageAdjunction.{u, 0} c).unit.app
          ((sheafCompose (Scheme.smallEtaleTopology Z)
            (forget AddCommGrpCat.{u + 1})).obj G)).hom.app
            (op (terminal Z.Etale))) ≫
          φ.hom.app (op ((smallEtaleBaseChange c).obj (terminal Z.Etale))) := by
      refine Eq.trans ?_ key.symm
      exact (Category.comp_id _).symm
    rw [key']
    exact h₂
  exact isIso_of_reflects_iso _ (forget AddCommGrpCat.{u + 1})

end SmallEtale

end Stacks.EtaleCohomology

end
