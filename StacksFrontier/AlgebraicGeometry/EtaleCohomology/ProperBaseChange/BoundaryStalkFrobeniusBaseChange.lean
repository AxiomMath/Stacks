module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryStalkFrobeniusPullback
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryInertiaInvariantsLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChange

/-!
# The specialization map of `j_* F` on germs: the base change step of Tag 03Q9

Let `j : U ⟶ S`, `s` a geometric point of `S`, `π : Spec 𝒪^{sh}_{S,s} ⟶ S` the strict
henselization and `U ×_S Spec 𝒪^{sh} ≅ Spec K`. The identification of the stalk `(j_* F)_s` with
the sections of `F` over `Spec K` (Stacks 03Q9 in degree zero,
`Stacks.EtaleCohomology.directImageStalkIsoFieldSections`) is computed here on germs: the germ of
`τ ∈ F(U ×_S V)` at a lift `x` of `s` goes to the pull-back of `τ`, restricted along the section
of `U ×_S V` induced by a section of `V ×_S Spec 𝒪^{sh}` through `x`; through the germ at a
geometric point `t̄` of `Spec K` this is the germ of `τ` at the corresponding lift of `t̄`. This is
the step of the Frobenius equivariance of `H⁰_loc` (Weil II 1.8) in which the Frobenius moves
the lift `x` to `a ≫ x`.

## Main results

* `AlgebraicGeometry.smallEtaleSetBaseChange_unit_app` — the base change map of a square,
  transposed (the mate relation), and
  `AlgebraicGeometry.smallEtaleSetBaseChangeTwoCell_app_hom_app` — the square two-cell on sections.
* `AlgebraicGeometry.toPresheafFiber_stalkIsoStrictHenselizationGamma_hom` — the germ formula for
  `F_s ≅ Γ(Spec 𝒪^{sh}, π⁻¹ F)`.
* `AlgebraicGeometry.toPresheafFiber_directImageStalk_baseChange` — the germ formula through the
  base change map of Tag 03Q9.
* `AlgebraicGeometry.fieldSections_toPresheafFiber` — the field step `Γ(T, fst⁻¹ F) ≅ Γ(Spec K,
  g⁻¹ F)` followed by the germ at `t̄` and Tag 03Q1.

## Implementation notes

The kernel times out on instances of generic lemmas at `pullback j (strictHenselizationToBase …)`
made inside a tactic `have`; the base change step is therefore proved for an arbitrary
`π : SH' ⟶ S` (`AlgebraicGeometry.baseChange_sections_of_eq`) and instantiated once, by a term,
with all implicit objects given. Composite natural transformations containing an `eqToIso` are
unfolded through separate `rfl` lemmas combined with `congrArg₂`.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme

universe v u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-- The two-cell `e_* ⋙ g_* ⟶ h_* ⋙ f_*` of a commutative square `e ≫ g = h ≫ f` whose mate is the
base change map `Stacks.EtaleCohomology.smallEtaleSetBaseChange`. -/
def smallEtaleSetBaseChangeTwoCell {Y T X' S' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X')
    (g : T ⟶ S') (f : X' ⟶ S') (w : e ≫ g = h ≫ f) :
    TwoSquare
      ((Stacks.EtaleCohomology.smallEtaleBaseChange e).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology T) (smallEtaleTopology Y))
      ((Stacks.EtaleCohomology.smallEtaleBaseChange h).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology X') (smallEtaleTopology Y))
      ((Stacks.EtaleCohomology.smallEtaleBaseChange g).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology T))
      ((Stacks.EtaleCohomology.smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology X')) :=
  TwoSquare.mk _ _ _ _ <| (smallEtalePushforwardCompIso.{u, v} e g).hom ≫
    (eqToIso (congrArg (fun k : Y ⟶ S' ↦
      (Stacks.EtaleCohomology.smallEtaleBaseChange k).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology Y)) w)).hom ≫
    (smallEtalePushforwardCompIso.{u, v} h f).inv

/-- The mate of the base change map of a square is the square two-cell. -/
theorem mateEquiv_smallEtaleSetBaseChange {Y T X' S' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X')
    (g : T ⟶ S') (f : X' ⟶ S') (w : e ≫ g = h ≫ f) :
    mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
        (smallEtaleInverseImageAdjunction.{u, v} f) (smallEtaleSetBaseChange.{u, v} e h g f w) =
      smallEtaleSetBaseChangeTwoCell.{v, u} e h g f w := by
  unfold smallEtaleSetBaseChange
  exact Equiv.apply_symm_apply _ _

/-- **The base change map of a square, transposed** (the mate relation): `g_*` of the unit of
`e⁻¹ ⊣ e_*` followed by the square two-cell is the unit of `f⁻¹ ⊣ f_*` followed by `f_*` of the
base change map. -/
theorem smallEtaleSetBaseChange_unit_app {Y T X' S' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X')
    (g : T ⟶ S') (f : X' ⟶ S') (w : e ≫ g = h ≫ f)
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) (V : S'.Etale) :
    ((smallEtaleInverseImageAdjunction.{u, v} f).unit.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange g).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology T)).obj F)).hom.app
          (op V) ≫
      ((smallEtaleSetBaseChange.{u, v} e h g f w).app F).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)) =
    ((smallEtaleInverseImageAdjunction.{u, v} e).unit.app F).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)) ≫
      ((smallEtaleSetBaseChangeTwoCell.{v, u} e h g f w).app
        ((smallEtaleInverseImage.{u, v} e).obj F)).hom.app (op V) := by
  have hm := unit_mateEquiv (smallEtaleInverseImageAdjunction.{u, v} e)
    (smallEtaleInverseImageAdjunction.{u, v} f) (smallEtaleSetBaseChange.{u, v} e h g f w) F
  rw [mateEquiv_smallEtaleSetBaseChange] at hm
  exact (congrArg (fun m => m.hom.app (op V)) hm).symm

/-- Direct image along equal morphisms, on sections: transport is restriction along the
identification of the two base changes. -/
theorem smallEtalePushforward_eqToHom_app_hom_app {Y S' : Scheme.{u}} {k k' : Y ⟶ S'} (w : k = k')
    (X : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S'.Etale) :
    ((eqToHom (congrArg (fun k : Y ⟶ S' ↦
      (Stacks.EtaleCohomology.smallEtaleBaseChange k).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology Y)) w)).app X).hom.app
        (op V) =
      X.obj.map (eqToHom (congrArg (fun k : Y ⟶ S' ↦
        (Stacks.EtaleCohomology.smallEtaleBaseChange k).obj V) w.symm)).op := by
  subst w
  exact (X.obj.map_id _).symm

/-- The composition isomorphism of direct images, on sections. -/
theorem smallEtalePushforwardCompIso_hom_app_hom_app {Y T S' : Scheme.{u}} (e : Y ⟶ T) (g : T ⟶ S')
    (X : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S'.Etale) :
    ((smallEtalePushforwardCompIso.{u, v} e g).hom.app X).hom.app (op V) =
      X.obj.map ((smallEtaleBaseChangeComp e g).hom.app V).op := rfl

/-- The inverse composition isomorphism of direct images, on sections. -/
theorem smallEtalePushforwardCompIso_inv_app_hom_app {Y T S' : Scheme.{u}} (e : Y ⟶ T) (g : T ⟶ S')
    (X : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S'.Etale) :
    ((smallEtalePushforwardCompIso.{u, v} e g).inv.app X).hom.app (op V) =
      X.obj.map ((smallEtaleBaseChangeComp e g).inv.app V).op := rfl

/-- `smallEtaleSetBaseChangeTwoCell` as a composite of natural transformations. -/
theorem smallEtaleSetBaseChangeTwoCell_natTrans {Y T X' S' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X')
    (g : T ⟶ S') (f : X' ⟶ S') (w : e ≫ g = h ≫ f) :
    smallEtaleSetBaseChangeTwoCell.{v, u} e h g f w =
      (smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        (eqToIso (congrArg (fun k : Y ⟶ S' ↦
          (Stacks.EtaleCohomology.smallEtaleBaseChange k).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology Y)) w)).hom ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv := rfl

/-- The components of the composite defining `smallEtaleSetBaseChangeTwoCell`. -/
theorem smallEtaleSetBaseChangeTwoCellComp_app {Y T X' S' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X')
    (g : T ⟶ S') (f : X' ⟶ S') (w : e ≫ g = h ≫ f)
    (X : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    ((smallEtalePushforwardCompIso.{u, v} e g).hom ≫
        (eqToIso (congrArg (fun k : Y ⟶ S' ↦
          (Stacks.EtaleCohomology.smallEtaleBaseChange k).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology Y)) w)).hom ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv).app X =
      (smallEtalePushforwardCompIso.{u, v} e g).hom.app X ≫
        (eqToHom (congrArg (fun k : Y ⟶ S' ↦
          (Stacks.EtaleCohomology.smallEtaleBaseChange k).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology Y)) w)).app X ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv.app X := rfl

/-- The components of `smallEtaleSetBaseChangeTwoCell`. -/
theorem smallEtaleSetBaseChangeTwoCell_app {Y T X' S' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X')
    (g : T ⟶ S') (f : X' ⟶ S') (w : e ≫ g = h ≫ f)
    (X : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) :
    (smallEtaleSetBaseChangeTwoCell.{v, u} e h g f w).app X =
      (smallEtalePushforwardCompIso.{u, v} e g).hom.app X ≫
        (eqToHom (congrArg (fun k : Y ⟶ S' ↦
          (Stacks.EtaleCohomology.smallEtaleBaseChange k).sheafPushforwardContinuous
            (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology Y)) w)).app X ≫
        (smallEtalePushforwardCompIso.{u, v} h f).inv.app X :=
  (congrArg (fun α => NatTrans.app α X)
    (smallEtaleSetBaseChangeTwoCell_natTrans.{v, u} e h g f w)).trans
    (smallEtaleSetBaseChangeTwoCellComp_app.{v, u} e h g f w X)

/-- **The square two-cell on sections** is restriction along the identifications
`e^* g^* V ≅ (e ≫ g)^* V = (h ≫ f)^* V ≅ h^* f^* V`. -/
theorem smallEtaleSetBaseChangeTwoCell_app_hom_app {Y T X' S' : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X')
    (g : T ⟶ S') (f : X' ⟶ S') (w : e ≫ g = h ≫ f)
    (X : Sheaf (smallEtaleTopology Y) (Type (max (u + 1) v))) (V : S'.Etale) :
    ((smallEtaleSetBaseChangeTwoCell.{v, u} e h g f w).app X).hom.app (op V) =
      X.obj.map ((smallEtaleBaseChangeComp e g).hom.app V).op ≫
        X.obj.map (eqToHom (congrArg (fun k : Y ⟶ S' ↦
          (Stacks.EtaleCohomology.smallEtaleBaseChange k).obj V) w.symm)).op ≫
        X.obj.map ((smallEtaleBaseChangeComp h f).inv.app V).op := by
  rw [smallEtaleSetBaseChangeTwoCell_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, NatTrans.comp_app]
  exact congrArg₂ (· ≫ ·) (smallEtalePushforwardCompIso_hom_app_hom_app.{v, u} e g X V)
    (congrArg₂ (· ≫ ·) (smallEtalePushforward_eqToHom_app_hom_app.{v, u} w X V)
      (smallEtalePushforwardCompIso_inv_app_hom_app.{v, u} h f X V))

/-- Six restriction maps of a presheaf compose to the restriction along the composite. -/
theorem map_op_comp₆ {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (P : 𝒞ᵒᵖ ⥤ 𝒟)
    {W₀ W₁ W₂ W₃ W₄ W₅ W₆ : 𝒞} (a₁ : W₁ ⟶ W₀) (a₂ : W₂ ⟶ W₁) (a₃ : W₃ ⟶ W₂) (a₄ : W₄ ⟶ W₃)
    (a₅ : W₅ ⟶ W₄) (a₆ : W₆ ⟶ W₅) (φ : W₆ ⟶ W₀) (h : a₆ ≫ a₅ ≫ a₄ ≫ a₃ ≫ a₂ ≫ a₁ = φ) :
    P.map a₁.op ≫ P.map a₂.op ≫ P.map a₃.op ≫ P.map a₄.op ≫ P.map a₅.op ≫ P.map a₆.op =
      P.map φ.op := by
  subst h
  simp only [op_comp, Functor.map_comp, Category.assoc]

/-- **Direct image along an isomorphism is inverse image along its inverse, on sections over a
final object**: through `smallEtalePushforwardIsoInverseImageOfIso`, a section `ζ` over a final
object `W`, restricted to `e^*(e⁻¹)^* W`, becomes the pull-back of `ζ` along `e⁻¹`. -/
theorem smallEtalePushforwardIsoInverseImageOfIso_hom_app_unit {P Q : Scheme.{u}} (e : P ≅ Q)
    (X : Sheaf (smallEtaleTopology P) (Type (max (u + 1) v))) {W : P.Etale} (hW : IsTerminal W)
    (φ : (Stacks.EtaleCohomology.smallEtaleBaseChange e.hom).obj
      ((Stacks.EtaleCohomology.smallEtaleBaseChange e.inv).obj W) ⟶ W) :
    X.obj.map φ.op ≫ ((smallEtalePushforwardIsoInverseImageOfIso.{u, v} e).hom.app X).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange e.inv).obj W)) =
      ((smallEtaleInverseImageAdjunction.{u, v} e.inv).unit.app X).hom.app (op W) := by
  let E : Sheaf (smallEtaleTopology P) (Type (max (u + 1) v)) ≌
      Sheaf (smallEtaleTopology Q) (Type (max (u + 1) v)) :=
    CategoryTheory.Equivalence.mk
      ((Stacks.EtaleCohomology.smallEtaleBaseChange e.hom).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology Q) (smallEtaleTopology P))
      ((Stacks.EtaleCohomology.smallEtaleBaseChange e.inv).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology P) (smallEtaleTopology Q))
      ((Functor.sheafPushforwardContinuousId'
          (Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf _ e.hom_inv_id)
          (Type (max (u + 1) v)) (smallEtaleTopology P)).symm ≪≫
        (smallEtalePushforwardCompIso.{u, v} e.hom e.inv).symm)
      (smallEtalePushforwardCompIso.{u, v} e.inv e.hom ≪≫
        Functor.sheafPushforwardContinuousId'
          (Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf _ e.inv_hom_id)
          (Type (max (u + 1) v)) (smallEtaleTopology Q))
  have h := congrArg (fun m => m.hom.app (op W))
    (Adjunction.unit_leftAdjointUniq_hom_app E.toAdjunction
      (smallEtaleInverseImageAdjunction.{u, v} e.inv) X)
  have hu : (E.toAdjunction.unit.app X).hom.app (op W) = X.obj.map φ.op := by
    change ((Equivalence.adjointifyη
      ((Functor.sheafPushforwardContinuousId'
          (Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf _ e.hom_inv_id)
          (Type (max (u + 1) v)) (smallEtaleTopology P)).symm ≪≫
        (smallEtalePushforwardCompIso.{u, v} e.hom e.inv).symm)
      (smallEtalePushforwardCompIso.{u, v} e.inv e.hom ≪≫
        Functor.sheafPushforwardContinuousId'
          (Stacks.EtaleCohomology.smallEtaleBaseChangeIdOf _ e.inv_hom_id)
          (Type (max (u + 1) v)) (smallEtaleTopology Q))).hom.app X).hom.app (op W) = _
    simp only [Functor.id_obj, Functor.comp_obj, Equivalence.adjointifyη, Trans.trans,
      Iso.trans_assoc, Iso.trans_symm, Functor.isoWhiskerRight_trans, Functor.isoWhiskerLeft_trans,
      Iso.symm_symm_eq, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_map, Functor.leftUnitor_hom_app, Category.comp_id,
      ← Functor.map_comp, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuousId'_inv_app_hom_app,
      smallEtalePushforwardCompIso_inv_app_hom_app, Functor.sheafPushforwardContinuous_map_hom_app,
      Functor.sheafPushforwardContinuous_obj_obj_map, Quiver.Hom.unop_op,
      smallEtalePushforwardCompIso_hom_app_hom_app,
      Functor.sheafPushforwardContinuousId'_hom_app_hom_app]
    exact map_op_comp₆ X.obj _ _ _ _ _ _ _ (hW.hom_ext _ _)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  rwa [hu] at h

/-- Two restriction maps of a presheaf compose to the restriction along the composite. -/
theorem map_op_comp₂ {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (P : 𝒞ᵒᵖ ⥤ 𝒟)
    {W₀ W₁ W₂ : 𝒞} (a₁ : W₁ ⟶ W₀) (a₂ : W₂ ⟶ W₁) (φ : W₂ ⟶ W₀) (h : a₂ ≫ a₁ = φ) :
    P.map φ.op = P.map a₁.op ≫ P.map a₂.op := by
  subst h
  simp only [op_comp, Functor.map_comp]

/-- The inverse of `Γ(S', g_* X) ≅ Γ(T, X)` on the sections over a final object `W` of `T`: they
are restricted to `g^* S'` and read as sections of `g_* X` over `S'`. -/
theorem ΓNatIsoSheafSections_inv_app_smallEtalePushforwardGammaIso_inv_app {T S' : Scheme.{u}}
    (g : T ⟶ S') (X : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) {W : T.Etale}
    (hW : IsTerminal W) :
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (max (u + 1) v)) hW).inv.app X ≫
      (smallEtalePushforwardGammaIso.{u, v} g).inv.app X =
    X.obj.map ((hW.from _ :
      (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 S')) ⟶ W)).op ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology S') (Type (max (u + 1) v))
        (isTerminalEtaleMkId S')).inv.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange g).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology T)).obj X) := by
  have h : (smallEtalePushforwardGammaIso.{u, v} g).inv.app X =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (max (u + 1) v))
        (isTerminalSmallEtaleBaseChangeObj g (isTerminalEtaleMkId S'))).hom.app X ≫ 𝟙 _ ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology S') (Type (max (u + 1) v))
        (isTerminalEtaleMkId S')).inv.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange g).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology T)).obj X) := rfl
  have hR : (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (max (u + 1) v))
      hW).inv.app X ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (max (u + 1) v))
        (isTerminalSmallEtaleBaseChangeObj g (isTerminalEtaleMkId S'))).hom.app X =
      X.obj.map ((hW.from _ :
        (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj (Scheme.Etale.mk (𝟙 S')) ⟶ W)).op := by
    have e1 : X.ΓRes (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
        (Scheme.Etale.mk (𝟙 S')))) =
        (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (max (u + 1) v)) hW).hom.app X ≫
          X.obj.map ((hW.from _ : (Stacks.EtaleCohomology.smallEtaleBaseChange g).obj
            (Scheme.Etale.mk (𝟙 S')) ⟶ W)).op := by
      rw [Sheaf.ΓNatIsoSheafSections_hom_app_general]
      exact (Sheaf.ΓRes_map X _).symm
    rw [Sheaf.ΓNatIsoSheafSections_hom_app_general
      (isTerminalSmallEtaleBaseChangeObj g (isTerminalEtaleMkId S')), e1]
    exact Iso.inv_hom_id_app_assoc _ _ _
  rw [h, ← Category.assoc, hR]
  exact congrArg (_ ≫ ·) (Category.id_comp _)

section GlobalGerm

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- The lift `s ≫ m ≫ pr₁` of `s ≫ i` lies over `X`. -/
theorem pointLiftOfSection_w {Z X : Scheme.{u}} (i : Z ⟶ X) (s : Spec (.of Ω) ⟶ Z) (W : X.Etale)
    (m : Scheme.Etale.mk (𝟙 Z) ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange i).obj W) :
    (s ≫ m.left ≫ pullback.fst W.hom i) ≫ W.hom = s ≫ i := by
  have hw : m.left ≫ pullback.snd W.hom i = 𝟙 _ := CategoryTheory.Over.w m.hom
  refine (Category.assoc _ _ _).trans (congrArg (s ≫ ·) ?_)
  exact (Category.assoc _ _ _).trans ((congrArg (m.left ≫ ·) pullback.condition).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ i) hw).trans (Category.id_comp i))))

/-- A section `m` of `Z ×_X W ⟶ Z` through a lift `x` of `s ≫ i` to `W` sends `s` to the
lift of `s` to `Z ×_X W` induced by `x`. -/
private theorem comp_left_eq_pointSmallEtaleBaseChangeFiberIso_hom_app_left {Z X : Scheme.{u}}
    (i : Z ⟶ X) (s : Spec (.of Ω) ⟶ Z) (W : X.Etale) (x : (pointSmallEtale (s ≫ i)).fiber.obj W)
    (m : Scheme.Etale.mk (𝟙 Z) ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange i).obj W)
    (hm : s ≫ m.left ≫ pullback.fst W.hom i = x.left) :
    s ≫ m.left = ((pointSmallEtaleBaseChangeFiberIso i s).hom.app W x).left := by
  have hw : m.left ≫ pullback.snd W.hom i = 𝟙 _ := CategoryTheory.Over.w m.hom
  exact pullback.hom_ext
    ((Category.assoc _ _ _).trans
      (hm.trans (pointSmallEtaleBaseChangeFiberIso_hom_app_left_fst i s W x).symm))
    ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) hw).trans ((Category.comp_id _).trans
      (pointSmallEtaleBaseChangeFiberIso_hom_app_left_snd i s W x).symm)))

/-- The lift of `s ≫ i` to `W` given by a section `m` of `Z ×_X W ⟶ Z`. -/
def pointLiftOfSection {Z X : Scheme.{u}} (i : Z ⟶ X) (s : Spec (.of Ω) ⟶ Z) (W : X.Etale)
    (m : Scheme.Etale.mk (𝟙 Z) ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange i).obj W) :
    (pointSmallEtale (s ≫ i)).fiber.obj W :=
  CategoryTheory.Over.homMk (s ≫ m.left ≫ pullback.fst W.hom i) (pointLiftOfSection_w i s W m)

/-- **The germ of a restricted pull-back** (Stacks 03Q1 for global sections): the germ at `s`
of the pull-back `i^* τ` restricted along a section `m` of `Z ×_X W ⟶ Z` is, under
`(i⁻¹ F)_s ≅ F_{s ≫ i}`, the germ of `τ` at the lift `s ≫ m ≫ pr₁` of `s ≫ i` to `W`. -/
theorem unit_map_toPresheafFiber_smallEtaleInverseImageStalkIso_hom {Z X : Scheme.{u}} (i : Z ⟶ X)
    (s : Spec (.of Ω) ⟶ Z) (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v)))
    (W : X.Etale)
    (m : Scheme.Etale.mk (𝟙 Z) ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange i).obj W) :
    ((smallEtaleInverseImageAdjunction.{u, v} i).unit.app F).hom.app (op W) ≫
        ((smallEtaleInverseImage.{u, v} i).obj F).obj.map m.op ≫
        (pointSmallEtale s).toPresheafFiber _ (pointSmallEtaleIdElementOf s)
          ((smallEtaleInverseImage.{u, v} i).obj F).obj ≫
        (smallEtaleInverseImageStalkIso.{v, u} i s).hom.app F =
      (pointSmallEtale (s ≫ i)).toPresheafFiber W (pointLiftOfSection i s W m) F.obj := by
  have hpt : (pointSmallEtale s).fiber.map m (pointSmallEtaleIdElementOf s) =
      (pointSmallEtaleBaseChangeFiberIso i s).hom.app W (pointLiftOfSection i s W m) :=
    CategoryTheory.Over.OverMorphism.ext
      (comp_left_eq_pointSmallEtaleBaseChangeFiberIso_hom_app_left i s W _ m rfl)
  have h1 := (pointSmallEtale s).toPresheafFiber_w m (pointSmallEtaleIdElementOf s)
    ((smallEtaleInverseImage.{u, v} i).obj F).obj
  rw [hpt] at h1
  exact (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1))).trans
    (smallEtaleInverseImageStalkIso_hom_germ_unit.{v, u} i s F W (pointLiftOfSection i s W m))

end GlobalGerm

/-- `smallEtalePushforwardIsoInverseImageOfIso` on sections over any final object: a section
`ζ` over a final object `T` of `P`, restricted to `e^* W'` for a final `W'`, becomes the pull-back
of `ζ` along `e⁻¹`, restricted along `W' ⟶ (e⁻¹)^* T`. -/
theorem smallEtalePushforwardIsoInverseImageOfIso_hom_app_unit' {P Q : Scheme.{u}} (e : P ≅ Q)
    (X : Sheaf (smallEtaleTopology P) (Type (max (u + 1) v))) {T : P.Etale} (hT : IsTerminal T)
    {W' : Q.Etale} (fr : (Stacks.EtaleCohomology.smallEtaleBaseChange e.hom).obj W' ⟶ T)
    (ρ : W' ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange e.inv).obj T) :
    X.obj.map fr.op ≫ ((smallEtalePushforwardIsoInverseImageOfIso.{u, v} e).hom.app X).hom.app
        (op W') =
      ((smallEtaleInverseImageAdjunction.{u, v} e.inv).unit.app X).hom.app (op T) ≫
        ((smallEtaleInverseImage.{u, v} e.inv).obj X).obj.map ρ.op := by
  let φ : (Stacks.EtaleCohomology.smallEtaleBaseChange e.hom).obj
      ((Stacks.EtaleCohomology.smallEtaleBaseChange e.inv).obj T) ⟶ T := hT.from _
  rw [map_op_comp₂ X.obj φ ((Stacks.EtaleCohomology.smallEtaleBaseChange e.hom).map ρ) fr
    (hT.hom_ext _ _)]
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (((smallEtalePushforwardIsoInverseImageOfIso.{u, v} e).hom.app X).hom.naturality
      ρ.op)).trans ?_)
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    (smallEtalePushforwardIsoInverseImageOfIso_hom_app_unit.{v, u} e X hT φ))

/-- Naturality of `Γ(Z, -) ≅ sections over the final object`, for a morphism of sheaves. -/
private theorem ΓNatIsoSheafSections_inv_app_comp_map {Z : Scheme.{u}}
    {A B : Sheaf (smallEtaleTopology Z) (Type (max (u + 1) v))} (f : A ⟶ B) :
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) (Type (max (u + 1) v))
        (isTerminalEtaleMkId Z)).inv.app A ≫
      (Sheaf.Γ (smallEtaleTopology Z) (Type (max (u + 1) v))).map f =
    f.hom.app (op (Scheme.Etale.mk (𝟙 Z))) ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) (Type (max (u + 1) v))
        (isTerminalEtaleMkId Z)).inv.app B :=
  ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) (Type (max (u + 1) v))
    (isTerminalEtaleMkId Z)).inv.naturality f).symm

private theorem chain_field {𝒞 : Type*} [Category* 𝒞]
    {a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b4 b5 b6 b7 : 𝒞}
    (Γi : a1 ⟶ a2) (γinv : a2 ⟶ a3) (Γι : a3 ⟶ a4) (Γc : a4 ⟶ a5) (Γh : a5 ⟶ a6)
    (germK : a6 ⟶ a7) (Qg : a7 ⟶ a8) (Xfrom : a1 ⟶ b1) (ΓKi : b1 ⟶ a3) (ιapp : b1 ⟶ b2)
    (ΓKi2 : b2 ⟶ a4) (compapp : b2 ⟶ a6) (ΓKi3 : a6 ⟶ a5) (unitW : a1 ⟶ b4) (Lρ : b4 ⟶ b2)
    (germK' : b2 ⟶ b5) (Pcomp : b5 ⟶ a7) (Qe : b5 ⟶ b6) (germW : a1 ⟶ b6) (Qf : b6 ⟶ b7)
    (E : b7 ⟶ a8)
    (h1 : Γi ≫ γinv = Xfrom ≫ ΓKi) (h2 : ΓKi ≫ Γι = ιapp ≫ ΓKi2) (h3 : ΓKi2 ≫ Γc = compapp ≫ ΓKi3)
    (h4 : ΓKi3 ≫ Γh = 𝟙 _) (h5 : Xfrom ≫ ιapp = unitW ≫ Lρ)
    (h6 : compapp ≫ germK = germK' ≫ Pcomp) (h7 : unitW ≫ Lρ ≫ germK' ≫ Qe = germW)
    (h8 : Pcomp ≫ Qg = Qe ≫ Qf ≫ E) :
    Γi ≫ γinv ≫ Γι ≫ Γc ≫ Γh ≫ germK ≫ Qg = germW ≫ Qf ≫ E := by
  subst h7
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, reassoc_of% h4,
    reassoc_of% h5, reassoc_of% h6, h8]
  simp only [Category.assoc]

private theorem comp_eq_of_inv_inv_comp {𝒞 : Type*} [Category* 𝒞] {x y z d a : 𝒞}
    (A : x ≅ y) (B : z ≅ x) (M : z ⟶ d) (H : d ⟶ a) (E' : y ⟶ a)
    (h : A.inv ≫ B.inv ≫ M ≫ H = E') : M ≫ H = B.hom ≫ A.hom ≫ E' := by
  subst h
  simp

/-- **The field step of the specialization map on sections** (generic form): through
`Γ(T, X) ≅ Γ(Spec K, e_* X) ≅ Γ(Spec K, g⁻¹ F)` (`g = e⁻¹ ≫ fst`), then the germ at `t` and
`(g⁻¹ F)_t ≅ F_{t ≫ g}`, a section of `X = fst⁻¹ F` over a final object `W` of `T` goes to its
germ at `t ≫ e⁻¹`, read through `(fst⁻¹ F)_{t ≫ e⁻¹} ≅ F_{t ≫ e⁻¹ ≫ fst}`. -/
theorem fieldSections_toPresheafFiber {U T : Scheme.{u}} (fst : T ⟶ U)
    (F : Sheaf (smallEtaleTopology U) (Type (u + 1))) {K : Type u} [Field K]
    (e : T ≅ Spec (.of K)) (g : Spec (.of K) ⟶ U) (hg : g = e.inv ≫ fst) {Ω' : Type u}
    [Field Ω'] [IsSepClosed Ω'] (t : Spec (.of Ω') ⟶ Spec (.of K)) {W : T.Etale}
    (hW : IsTerminal W) :
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (u + 1)) hW).inv.app
        ((smallEtaleInverseImage.{u, 0} fst).obj F) ≫
      (smallEtalePushforwardGammaIso.{u, 0} e.hom).inv.app
        ((smallEtaleInverseImage.{u, 0} fst).obj F) ≫
      (Sheaf.Γ (smallEtaleTopology (Spec (.of K))) (Type (u + 1))).map
        ((Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, 0} fst)
          (smallEtalePushforwardIsoInverseImageOfIso.{u, 0} e) ≪≫
          smallEtaleInverseImageComp.{u, 0} e.inv fst ≪≫
          eqToIso (congrArg (fun k => smallEtaleInverseImage.{u, 0} k) hg.symm)).hom.app F) ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of K))) (Type (u + 1))
        (isTerminalEtaleMkId _)).hom.app ((smallEtaleInverseImage.{u, 0} g).obj F) ≫
      (pointSmallEtale t).toPresheafFiber _ (pointSmallEtaleIdElementOf t)
        ((smallEtaleInverseImage.{u, 0} g).obj F).obj ≫
      (smallEtaleInverseImageStalkIso.{0, u} g t).hom.app F =
    (pointSmallEtale (t ≫ e.inv)).toPresheafFiber W
        (pointLiftOfSection e.inv t W ((isTerminalSmallEtaleBaseChangeObj e.inv hW).from _))
        ((smallEtaleInverseImage.{u, 0} fst).obj F).obj ≫
      (smallEtaleInverseImageStalkIso.{0, u} fst (t ≫ e.inv)).hom.app F ≫
      eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj F.obj)
        (show (t ≫ e.inv) ≫ fst = t ≫ g by rw [hg, Category.assoc])) := by
  subst hg
  let X := (smallEtaleInverseImage.{u, 0} fst).obj F
  let ι := (smallEtalePushforwardIsoInverseImageOfIso.{u, 0} e).hom.app X
  let cm := (smallEtaleInverseImageComp.{u, 0} e.inv fst).hom.app F
  let ρ := (isTerminalSmallEtaleBaseChangeObj e.inv hW).from (Scheme.Etale.mk (𝟙 (Spec (.of K))))
  let ΓNK := Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of K))) (Type (u + 1))
    (isTerminalEtaleMkId (Spec (.of K)))
  have hFI : (Sheaf.Γ (smallEtaleTopology (Spec (.of K))) (Type (u + 1))).map
      ((Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, 0} fst)
        (smallEtalePushforwardIsoInverseImageOfIso.{u, 0} e) ≪≫
        smallEtaleInverseImageComp.{u, 0} e.inv fst ≪≫
        eqToIso (congrArg (fun k => smallEtaleInverseImage.{u, 0} k)
          (rfl : e.inv ≫ fst = _).symm)).hom.app F) =
      (Sheaf.Γ (smallEtaleTopology (Spec (.of K))) (Type (u + 1))).map ι ≫
        (Sheaf.Γ (smallEtaleTopology (Spec (.of K))) (Type (u + 1))).map cm := by
    simp [ι, cm, X]
  have h1 := ΓNatIsoSheafSections_inv_app_smallEtalePushforwardGammaIso_inv_app.{0, u} e.hom X hW
  have h2 := ΓNatIsoSheafSections_inv_app_comp_map.{0, u} ι
  have h3 := ΓNatIsoSheafSections_inv_app_comp_map.{0, u} cm
  have h4 := ΓNK.inv_hom_id_app ((smallEtaleInverseImage.{u, 0} (e.inv ≫ fst)).obj F)
  have h5 := smallEtalePushforwardIsoInverseImageOfIso_hom_app_unit'.{0, u} e X hW
    (hW.from _) ρ
  have h6 := ((pointSmallEtale t).toPresheafFiber_naturality cm.hom _
    (pointSmallEtaleIdElementOf t)).symm
  have h7 := unit_map_toPresheafFiber_smallEtaleInverseImageStalkIso_hom.{0, u} e.inv t X W ρ
  have h8 := comp_eq_of_inv_inv_comp ((smallEtaleInverseImageStalkIso.{0, u} fst (t ≫ e.inv)).app F)
    ((smallEtaleInverseImageStalkIso.{0, u} e.inv t).app X) _ _ _
    (smallEtaleInverseImageStalkIso_comp.{0, u} e.inv fst t F)
  rw [hFI, Category.assoc]
  exact chain_field _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8

section ClosedPointGerm

variable {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R] {Ω' : Type u} [Field Ω']
  [IsAlgClosed Ω']

/-- **The germ at a closed geometric point of a strictly henselian local scheme is the restriction
along a section**: the identification of the stalk at `y` with global sections sends the germ of
a section `ζ` over an étale `W` at a lift `w` of `y` to the restriction of `ζ` along any section
`σ` of `W` through `w`. -/
theorem toPresheafFiber_sheafFiberClosedPointIsoGamma_hom (y : Spec (.of Ω') ⟶ Spec (.of R))
    (hy : y (default : Spec (.of Ω')) = IsLocalRing.closedPoint R)
    (H : Sheaf (smallEtaleTopology (Spec (.of R))) (Type (max (u + 1) v)))
    (W : (Spec (.of R)).Etale) (w : (pointSmallEtale y).fiber.obj W)
    (σ : Scheme.Etale.mk (𝟙 (Spec (.of R))) ⟶ W) (hσ : y ≫ σ.left = w.left) :
    (pointSmallEtale y).toPresheafFiber W w H.obj ≫
        (sheafFiberClosedPointIsoGamma.{u, v} y hy).hom.app H =
      H.obj.map σ.op ≫ (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R)))
        (Type (max (u + 1) v)) (isTerminalEtaleMkId (Spec (.of R)))).inv.app H := by
  have hw : (pointSmallEtale y).fiber.map σ (pointSmallEtaleClosedPointElement y) = w :=
    CategoryTheory.Over.OverMorphism.ext hσ
  have hg := (pointSmallEtale y).toPresheafFiber_w σ (pointSmallEtaleClosedPointElement y) H.obj
  rw [hw] at hg
  have hI := (presheafFiberClosedPointIsoSections.{u, v} y hy).hom_inv_id_app H.obj
  have key : (pointSmallEtale y).toPresheafFiber _ (pointSmallEtaleClosedPointElement y) H.obj ≫
      (sheafFiberClosedPointIsoGamma.{u, v} y hy).hom.app H =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R)))
        (Type (max (u + 1) v)) (isTerminalEtaleMkId (Spec (.of R)))).inv.app H := by
    change (pointSmallEtale y).toPresheafFiber _ (pointSmallEtaleClosedPointElement y) H.obj ≫
        (presheafFiberClosedPointIsoSections.{u, v} y hy).inv.app H.obj ≫ _ = _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hI).trans (Category.id_comp _))
  exact (congrArg (· ≫ _) hg.symm).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) key))

end ClosedPointGerm

section StrictHenselization

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- **The germ formula for the stalk as sections over the strict henselization**: the
identification `F_s ≅ Γ(Spec 𝒪^{sh}_{S,s}, π⁻¹ F)` sends the germ of a section `τ` over an
étale `V` at a lift `x` of `s` to the pull-back `π^* τ`, restricted along a section `σ` of
`V ×_S Spec 𝒪^{sh}` through the lift of `x`. -/
theorem toPresheafFiber_stalkIsoStrictHenselizationGamma_hom
    (G : Sheaf (smallEtaleTopology S) (Type (u + 1))) (V : S.Etale)
    (x : (pointSmallEtale s.hom).fiber.obj V)
    (σ : Scheme.Etale.mk (𝟙 (strictHenselization B S hS s)) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange (strictHenselizationToBase B S hS s)).obj V)
    (hσ : geometricPointToStrictHenselization B S hS s ≫ σ.left ≫
      pullback.fst V.hom (strictHenselizationToBase B S hS s) = x.left) :
    (pointSmallEtale s.hom).toPresheafFiber V x G.obj ≫
        (stalkIsoStrictHenselizationGamma B S hS s).hom.app G =
      ((smallEtaleInverseImageAdjunction.{u, 0} (strictHenselizationToBase B S hS s)).unit.app
          G).hom.app (op V) ≫
        ((smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B S hS s)).obj G).obj.map
          σ.op ≫
        (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (strictHenselization B S hS s))
          (Type (u + 1)) (isTerminalEtaleMkId _)).inv.app
          ((smallEtaleInverseImage.{u, 0} (strictHenselizationToBase B S hS s)).obj G) := by
  let π := strictHenselizationToBase B S hS s
  let pt := geometricPointToStrictHenselization B S hS s
  have hpt := geometricPointToStrictHenselization_base_default B S hS s
  have e0 : s.hom = pt ≫ π := (geometricPointToStrictHenselization_comp B S hS s).symm
  have hSt : (stalkIsoStrictHenselizationGamma B S hS s).hom.app G =
      eqToHom (congrArg (fun k => (pointSmallEtale k).presheafFiber.obj G.obj) e0) ≫
        (smallEtaleInverseImageStalkIso.{0, u} π pt).inv.app G ≫
        (sheafFiberClosedPointIsoGamma.{u, 0} pt hpt).hom.app
          ((smallEtaleInverseImage.{u, 0} π).obj G) := by
    simp only [stalkIsoStrictHenselizationGamma, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app]
    rfl
  let x' : (pointSmallEtale (pt ≫ π)).fiber.obj V :=
    CategoryTheory.Over.homMk x.left (by rw [← e0]; exact CategoryTheory.Over.w x)
  have h1 := toPresheafFiber_comp_eqToHom.{0, u} e0 V x G.obj
  have h2 := toPresheafFiber_smallEtaleInverseImageStalkIso_inv.{0, u} π pt G V x'
  have hσ' : pt ≫ σ.left = ((pointSmallEtaleBaseChangeFiberIso π pt).hom.app V x').left :=
    comp_left_eq_pointSmallEtaleBaseChangeFiberIso_hom_app_left π pt V x' σ hσ
  have h3 := toPresheafFiber_sheafFiberClosedPointIsoGamma_hom.{0, u} pt hpt
    ((smallEtaleInverseImage.{u, 0} π).obj G) _ _ σ hσ'
  rw [hSt]
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans ?_)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h3)

private theorem chain_partA {𝒞 : Type*} [Category* 𝒞] {a b c d e f k l m n o o' : 𝒞}
    (G : a ⟶ b) (St : b ⟶ c) (Γc : c ⟶ d) (γ : d ⟶ e) (Uπ : a ⟶ f) (Mσ : f ⟶ k) (Γi1 : k ⟶ c)
    (Ct : k ⟶ l) (Γi2 : l ⟶ d) (Cv : f ⟶ m) (Nσ : m ⟶ l) (Uf : a ⟶ n) (Sq : n ⟶ m)
    (A1 : n ⟶ o) (A2 : o ⟶ o') (A3 : o' ⟶ m) (ΓT : l ⟶ e)
    (h1 : G ≫ St = Uπ ≫ Mσ ≫ Γi1) (h2 : Γi1 ≫ Γc = Ct ≫ Γi2) (h3 : Mσ ≫ Ct = Cv ≫ Nσ)
    (h4 : Uπ ≫ Cv = Uf ≫ Sq) (h5 : Sq = A1 ≫ A2 ≫ A3) (h7 : Γi2 ≫ γ = ΓT) :
    G ≫ St ≫ Γc ≫ γ = Uf ≫ A1 ≫ A2 ≫ A3 ≫ Nσ ≫ ΓT := by
  rw [← Category.assoc G St, h1]
  simp only [Category.assoc]
  rw [reassoc_of% h2, reassoc_of% h3, reassoc_of% h4, h5, h7]
  simp only [Category.assoc]

/-- The identification of sections of a direct image with sections of the sheaf, at the two
final objects. -/
theorem ΓNatIsoSheafSections_inv_app_smallEtalePushforwardGammaIso_hom_app {T S' : Scheme.{u}}
    (g : T ⟶ S') (X : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology S') (Type (max (u + 1) v))
        (isTerminalEtaleMkId S')).inv.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange g).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology T)).obj X) ≫
      (smallEtalePushforwardGammaIso.{u, v} g).hom.app X =
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (max (u + 1) v))
      (isTerminalSmallEtaleBaseChangeObj g (isTerminalEtaleMkId S'))).inv.app X := by
  have h : (smallEtalePushforwardGammaIso.{u, v} g).hom.app X =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology S') (Type (max (u + 1) v))
        (isTerminalEtaleMkId S')).hom.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange g).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology S') (smallEtaleTopology T)).obj X) ≫ 𝟙 _ ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) (Type (max (u + 1) v))
        (isTerminalSmallEtaleBaseChangeObj g (isTerminalEtaleMkId S'))).inv.app X := rfl
  rw [h]
  exact (Iso.inv_hom_id_app_assoc _ _ _).trans (Category.id_comp _)

variable {U : Scheme.{u}} (j : U ⟶ S)

/-- **The base change map of Tag 03Q9 on pulled-back sections**, for an arbitrary
`π : SH' ⟶ S`: if `St` sends `ζ` to the pull-back `π^* τ` restricted along a section `σ` of
`V ×_S SH'`, then `St` followed by the base change map and `Γ(SH', snd_* -) = Γ(U ×_S SH', -)`
sends `ζ` to `fst^* τ` restricted along the induced section of `U ×_S V` over `U ×_S SH'`. -/
theorem baseChange_sections_of_eq {SH' : Scheme.{u}} (π : SH' ⟶ S)
    (F : Sheaf (smallEtaleTopology U) (Type (u + 1))) (V : S.Etale) {A : Type (u + 1)}
    (ζ : (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F).obj.obj (op V) ⟶ A)
    (St : A ⟶ (smallEtaleInverseImage.{u, 0} π ⋙
      Sheaf.Γ (smallEtaleTopology SH') (Type (u + 1))).obj
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F))
    (σ : Scheme.Etale.mk (𝟙 SH') ⟶ (Stacks.EtaleCohomology.smallEtaleBaseChange π).obj V)
    (h1 : ζ ≫ St = ((smallEtaleInverseImageAdjunction.{u, 0} π).unit.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F)).hom.app (op V) ≫
      ((smallEtaleInverseImage.{u, 0} π).obj
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F)).obj.map σ.op ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology SH') (Type (u + 1))
        (isTerminalEtaleMkId SH')).inv.app ((smallEtaleInverseImage.{u, 0} π).obj
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F))) :
    ζ ≫ St ≫
      (Sheaf.Γ (smallEtaleTopology SH') (Type (u + 1))).map
        ((smallEtaleSetBaseChange.{u, 0} (pullback.fst j π) (pullback.snd j π) j π
          pullback.condition).app F) ≫
      (smallEtalePushforwardGammaIso.{u, 0} (pullback.snd j π)).hom.app
        ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F) =
    ((smallEtaleInverseImageAdjunction.{u, 0} (pullback.fst j π)).unit.app F).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange j).obj V)) ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F).obj.map
        ((smallEtaleBaseChangeComp (pullback.fst j π) j).hom.app V).op ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F).obj.map
        (eqToHom (congrArg (fun k : pullback j π ⟶ S ↦
          (Stacks.EtaleCohomology.smallEtaleBaseChange k).obj V) pullback.condition.symm)).op ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F).obj.map
        ((smallEtaleBaseChangeComp (pullback.snd j π) π).inv.app V).op ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F).obj.map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange (pullback.snd j π)).map σ).op ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (pullback j π)) (Type (u + 1))
        (isTerminalSmallEtaleBaseChangeObj (pullback.snd j π) (isTerminalEtaleMkId SH'))).inv.app
        ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F) := by
  let c := (smallEtaleSetBaseChange.{u, 0} (pullback.fst j π) (pullback.snd j π) j π
    pullback.condition).app F
  have h2 := ΓNatIsoSheafSections_inv_app_comp_map.{0, u} c
  have h3 : ((smallEtaleInverseImage.{u, 0} π).obj
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F)).obj.map σ.op ≫
      c.hom.app (op (Scheme.Etale.mk (𝟙 SH'))) =
      c.hom.app (op ((Stacks.EtaleCohomology.smallEtaleBaseChange π).obj V)) ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F).obj.map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange (pullback.snd j π)).map σ).op :=
    c.hom.naturality σ.op
  have h4 := smallEtaleSetBaseChange_unit_app.{0, u} (pullback.fst j π) (pullback.snd j π) j π
    pullback.condition F V
  have h5 := smallEtaleSetBaseChangeTwoCell_app_hom_app.{0, u} (pullback.fst j π) (pullback.snd j π)
    j π pullback.condition ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F) V
  have h7 := ΓNatIsoSheafSections_inv_app_smallEtalePushforwardGammaIso_hom_app.{0, u}
    (pullback.snd j π) ((smallEtaleInverseImage.{u, 0} (pullback.fst j π)).obj F)
  exact chain_partA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h7

/-- **The base change of Tag 03Q9 on the germ of a section** (first half of the germ formula of
the specialization map): the stalk at `s` of `j_* F`, read as sections of `fst⁻¹ F` over
`U ×_S Spec 𝒪^{sh}`, sends the germ of `τ ∈ F(U ×_S V)` at a lift `x` of `s` to the pull-back
`fst^* τ`, restricted along the section of `U ×_S V` over `U ×_S Spec 𝒪^{sh}` induced by a section
`σ` of `V ×_S Spec 𝒪^{sh}` through `x`. -/
theorem toPresheafFiber_directImageStalk_baseChange
    (F : Sheaf (smallEtaleTopology U) (Type (u + 1))) (V : S.Etale)
    (x : (pointSmallEtale s.hom).fiber.obj V)
    (σ : Scheme.Etale.mk (𝟙 (strictHenselization B S hS s)) ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange (strictHenselizationToBase B S hS s)).obj V)
    (hσ : geometricPointToStrictHenselization B S hS s ≫ σ.left ≫
      pullback.fst V.hom (strictHenselizationToBase B S hS s) = x.left) :
    (pointSmallEtale s.hom).toPresheafFiber V x
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F).obj ≫
      (stalkIsoStrictHenselizationGamma B S hS s).hom.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F) ≫
      (Sheaf.Γ (smallEtaleTopology (strictHenselization B S hS s)) (Type (u + 1))).map
        ((smallEtaleSetBaseChange.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))
          (pullback.snd j (strictHenselizationToBase B S hS s)) j
          (strictHenselizationToBase B S hS s) pullback.condition).app F) ≫
      (smallEtalePushforwardGammaIso.{u, 0}
        (pullback.snd j (strictHenselizationToBase B S hS s))).hom.app
        ((smallEtaleInverseImage.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))).obj
          F) =
    ((smallEtaleInverseImageAdjunction.{u, 0}
        (pullback.fst j (strictHenselizationToBase B S hS s))).unit.app F).hom.app
        (op ((Stacks.EtaleCohomology.smallEtaleBaseChange j).obj V)) ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))).obj
          F).obj.map
        ((smallEtaleBaseChangeComp (pullback.fst j (strictHenselizationToBase B S hS s)) j).hom.app
          V).op ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))).obj
          F).obj.map
        (eqToHom (congrArg (fun k : pullback j (strictHenselizationToBase B S hS s) ⟶ S ↦
          (Stacks.EtaleCohomology.smallEtaleBaseChange k).obj V) pullback.condition.symm)).op ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))).obj
          F).obj.map
        ((smallEtaleBaseChangeComp (pullback.snd j (strictHenselizationToBase B S hS s))
          (strictHenselizationToBase B S hS s)).inv.app V).op ≫
      ((smallEtaleInverseImage.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))).obj
          F).obj.map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange
          (pullback.snd j (strictHenselizationToBase B S hS s))).map σ).op ≫
      (Sheaf.ΓNatIsoSheafSections
        (smallEtaleTopology (pullback j (strictHenselizationToBase B S hS s)))
        (Type (u + 1)) (isTerminalSmallEtaleBaseChangeObj
          (pullback.snd j (strictHenselizationToBase B S hS s))
          (isTerminalEtaleMkId (strictHenselization B S hS s)))).inv.app
        ((smallEtaleInverseImage.{u, 0} (pullback.fst j (strictHenselizationToBase B S hS s))).obj
          F) :=
  baseChange_sections_of_eq S j (strictHenselizationToBase B S hS s) F V
    (A := (pointSmallEtale s.hom).sheafFiber.obj
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F))
    ((pointSmallEtale s.hom).toPresheafFiber V x
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F).obj)
    ((stalkIsoStrictHenselizationGamma B S hS s).hom.app
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F)) σ
    (toPresheafFiber_stalkIsoStrictHenselizationGamma_hom B S hS s
        (((Stacks.EtaleCohomology.smallEtaleBaseChange j).sheafPushforwardContinuous (Type (u + 1))
          (smallEtaleTopology S) (smallEtaleTopology U)).obj F) V x σ hσ)

end StrictHenselization

end AlgebraicGeometry

end
