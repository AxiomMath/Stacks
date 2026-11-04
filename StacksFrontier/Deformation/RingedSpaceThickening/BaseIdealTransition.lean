module

public import StacksFrontier.Deformation.RingedSpaceThickening.FlatThickeningBoundary
public import StacksFrontier.Deformation.RingedSpaceThickening.ModulePullbackTranspose
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical maps `f^* 𝒥 ⟶ i^* ℐ` along a cube of thickenings

For a commutative cube formed by two morphisms of first order thickenings `(f, f'₂)` and
`(f, f'₃)` of ringed spaces and morphisms of thickenings `h : X'₂ ⟶ X'₃` of `X` and
`g : S'₂ ⟶ S'₃` of `S` with `h ≫ f'₃ = f'₂ ≫ g`, the canonical maps `f^* 𝒥ₖ ⟶ iₖ^* ℐₖ` of
**Stacks 08KZ** commute with the maps `𝒥₃ ⟶ 𝒥₂` and `ℐ₃ ⟶ ℐ₂` induced by `g^♯` and `h^♯`
(`baseToSourceIdeal_comp_thickeningIdealMap`). Both composites are compared after transposing
along `f` and `t₃`, where they become the inclusion `𝒥₃ ⊆ 𝒪_{S'₃}` followed by the
structure-sheaf map of `f'₂ ≫ g = h ≫ f'₃`. The chosen ideal maps of a sequence of first order
thickenings in the sense of **Stacks 08LE** are identified with the induced maps
(`FirstOrderThickeningSequence.thickeningIdealMap_eq_idealMap₃₂` and
`FirstOrderThickeningSequence.thickeningIdealMap_eq_idealMap₂₁`).

This is the compatibility of the coefficient sequence `f^* 𝒥ₖ ⊗ ℱ` of **Stacks 08VT** with the
sequence `ℐₖ ⊗ ℱ` of **Stacks 08LF**.

## References

* [Stacks Project, Tag 08VT](https://stacks.math.columbia.edu/tag/08VT)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
* [Stacks Project, Tag 08LE](https://stacks.math.columbia.edu/tag/08LE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

section IdealMaps

variable {X X₁ X₂ : RingedSpace.{u, u}}

/-- **The map `ℐ₂ ⟶ ℐ₁` of a morphism of first order thickenings is the restriction of `h^♯`**,
in transposed form: the transpose `ℐ₂ ⟶ (i₂)_* i₁^* ℐ₁ = h_* (i₁)_* i₁^* ℐ₁ ≅ h_* ℐ₁` of
`thickeningIdealMap`, followed by the inclusion `h_* ℐ₁ ⊆ h_* 𝒪_{X'₁}`, is the inclusion
`ℐ₂ ⊆ 𝒪_{X'₂}` followed by `h^♯`. -/
theorem homEquiv_thickeningIdealMap_comp (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂) (h : X₁ ⟶ X₂)
    (comm : i₁ ≫ h = i₂) (hi₁ : IsFirstOrderThickening i₁) :
    haveI := isIso_unit_app_idealSheaf i₁ hi₁
    (modulePullbackPushforwardAdjunction i₂).homEquiv _ _ (thickeningIdealMap i₁ i₂ h comm) ≫
        eqToHom (congrArg (fun k : X ⟶ X₂ => (modulePushforward k).obj (idealSheafPullback i₁))
          comm.symm) ≫
        (modulePushforward h).map (inv ((modulePullbackPushforwardAdjunction i₁).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf i₁)) ≫ idealSheafι i₁) =
      idealSheafι i₂ ≫ structureSheafModuleHom h := by
  have := isIso_unit_app_idealSheaf i₁ hi₁
  subst comm
  have e1 : (modulePullbackPushforwardAdjunction (i₁ ≫ h)).homEquiv _ _
      (thickeningIdealMap i₁ (i₁ ≫ h) h rfl) =
      (modulePullbackPushforwardAdjunction h).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf (i₁ ≫ h)) ≫
        (modulePushforward h).map (Stacks.ClosedImmersion.idealSheafMap
            (comp_eq_id_comp (rfl : i₁ ≫ h = i₁ ≫ h)) ≫
          (modulePullbackPushforwardAdjunction i₁).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i₁)) := by
    rw [thickeningIdealMap_eq, homEquiv_modulePullbackComp_hom, Adjunction.homEquiv_unit,
      Adjunction.homEquiv_unit]
    congr 2
    exact ((modulePullbackPushforwardAdjunction i₁).unit.naturality _).symm
  have e2 : ((modulePullbackPushforwardAdjunction h).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf (i₁ ≫ h)) ≫
        (modulePushforward h).map (Stacks.ClosedImmersion.idealSheafMap
            (comp_eq_id_comp (rfl : i₁ ≫ h = i₁ ≫ h)) ≫
          (modulePullbackPushforwardAdjunction i₁).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i₁))) ≫
        (modulePushforward h).map (inv ((modulePullbackPushforwardAdjunction i₁).unit.app
          (AlgebraicGeometry.SheafOfModules.idealSheaf i₁)) ≫ idealSheafι i₁) =
      idealSheafι (i₁ ≫ h) ≫ structureSheafModuleHom h := by
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι
      (comp_eq_id_comp (rfl : i₁ ≫ h = i₁ ≫ h)))
    refine congrArg (fun z => _ ≫ z) ((Functor.map_comp _ _ _).symm.trans ?_)
    exact congrArg (fun z => (modulePushforward h).map z)
      ((Category.assoc _ _ _).trans (congrArg (fun z => _ ≫ z) (IsIso.hom_inv_id_assoc _ _)))
  refine Eq.trans ?_ e2
  rw [← e1]
  exact congrArg (fun z => _ ≫ z) (Category.id_comp _)

/-- The comparison `i^* (f')^* 𝒥 ≅ f^* t^* 𝒥` of a morphism of thickenings is the pullback
comparison of its square. -/
theorem reducedPullbackComparison_eq (D : MorphismOfThickenings.{u}) :
    D.reducedPullbackComparison =
      (modulePullbackSquareIso D.f D.f' D.i D.t D.comm).app D.idealJ := by
  ext1
  simp only [MorphismOfThickenings.reducedPullbackComparison, modulePullbackSquareIso,
    modulePullbackCompUniq_eq_modulePullbackComp, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    NatTrans.comp_app, modulePullbackCongr, eqToIso.hom, eqToHom_app]

/-- **The canonical map `f^* 𝒥 ⟶ i^* ℐ` in transposed form.** Transposing
`f^* t^* 𝒥 ⟶ i^* ℐ ⟶ 𝒬` along `f` and `t` is transposing `(f')^* 𝒥 ⟶ ℐ` followed by the
transpose of `i^* ℐ ⟶ 𝒬`, read through `(f')_* i_* ≅ t_* f_*`. -/
theorem homEquiv_baseToSourceIdeal_comp (D : MorphismOfThickenings.{u})
    {Q : SheafOfModules.{u} (structureSheafRing D.X)}
    (ψ : (modulePullback D.i).obj D.idealI ⟶ Q) :
    (modulePullbackPushforwardAdjunction D.t).homEquiv _ _
        ((modulePullbackPushforwardAdjunction D.f).homEquiv _ _
          (D.baseToSourceIdeal ≫ ψ)) =
    (modulePullbackPushforwardAdjunction D.f').homEquiv _ _
        (D.idealMap.1 ≫ (modulePullbackPushforwardAdjunction D.i).homEquiv _ _ ψ) ≫
      (modulePushforwardSquareIso D.f D.f' D.i D.t D.comm).hom.app Q := by
  rw [MorphismOfThickenings.baseToSourceIdeal, reducedPullbackComparison_eq, Iso.app_inv,
    Category.assoc, homEquiv_modulePullbackSquareIso_inv,
    Adjunction.homEquiv_naturality_left]

/-- A structure-sheaf map read through an equality of morphisms. -/
theorem structureSheafModuleHom_comp_eqToHom {Y Z : RingedSpace.{u, u}} {k₁ k₂ : Y ⟶ Z}
    (e : k₁ = k₂) :
    structureSheafModuleHom k₁ ≫ eqToHom (congrArg (fun k : Y ⟶ Z =>
      (modulePushforward k).obj (SheafOfModules.unit (structureSheafRing Y))) e) =
      structureSheafModuleHom k₂ := by
  subst e
  simp

/-- The structure-sheaf map of a composite, through the comparison `b_* a_* ≅ (a ≫ b)_*`. -/
theorem structureSheafModuleHom_comp_modulePushforwardComp {A B C : RingedSpace.{u, u}}
    (a : A ⟶ B) (b : B ⟶ C) :
    structureSheafModuleHom b ≫ (modulePushforward b).map (structureSheafModuleHom a) ≫
        (modulePushforwardComp a b).hom.app (SheafOfModules.unit (structureSheafRing A)) =
      structureSheafModuleHom (a ≫ b) := by
  rw [modulePushforwardComp_hom_app]
  exact (Category.comp_id _).trans (structureSheafModuleHom_comp a b).symm

end IdealMaps

section Cube

variable {X S X₂ S₂ X₃ S₃ : RingedSpace.{u, u}}

/-- **The transition maps of the coefficient modules commute with the canonical maps
`f^* 𝒥ₖ ⟶ i_k^* ℐₖ`.** For a commutative cube formed by two morphisms of first order thickenings
`(f, f₂)` and `(f, f₃)` and morphisms `h : X'₂ ⟶ X'₃`, `g : S'₂ ⟶ S'₃` of thickenings of `X` and
of `S` with `h ≫ f₃ = f₂ ≫ g`, the square

    f^* 𝒥₃ ⟶ i₃^* ℐ₃
      ↓          ↓
    f^* 𝒥₂ ⟶ i₂^* ℐ₂

commutes, the vertical maps being induced by `g^♯` and `h^♯`. Both composites are checked after
transposing along `f` and `t₃` and mapping into `𝒪_{X'₂}`, where they become `𝒥₃ ⊆ 𝒪_{S'₃}`
followed by the structure-sheaf map of `f₂ ≫ g = h ≫ f₃`. -/
theorem baseToSourceIdeal_comp_thickeningIdealMap (i₂ : X ⟶ X₂) (t₂ : S ⟶ S₂) (f : X ⟶ S)
    (f₂ : X₂ ⟶ S₂) (i₃ : X ⟶ X₃) (t₃ : S ⟶ S₃) (f₃ : X₃ ⟶ S₃) (h : X₂ ⟶ X₃) (g : S₂ ⟶ S₃)
    (hi₂ : IsFirstOrderThickening i₂) (ht₂ : IsFirstOrderThickening t₂)
    (hi₃ : IsThickening i₃) (ht₃ : IsThickening t₃)
    (r₂ : i₂ ≫ f₂ = f ≫ t₂) (r₃ : i₃ ≫ f₃ = f ≫ t₃) (hcomm : i₂ ≫ h = i₃)
    (gcomm : t₂ ≫ g = t₃) (c : h ≫ f₃ = f₂ ≫ g) :
    (modulePullback f).map (thickeningIdealMap t₂ t₃ g gcomm) ≫
        (MorphismOfThickenings.mk X X₂ S S₂ i₂ t₂ f f₂ hi₂.1 ht₂.1 r₂).baseToSourceIdeal =
      (MorphismOfThickenings.mk X X₃ S S₃ i₃ t₃ f f₃ hi₃ ht₃ r₃).baseToSourceIdeal ≫
        thickeningIdealMap i₂ i₃ h hcomm := by
  subst hcomm gcomm
  have := isIso_unit_app_idealSheaf i₂ hi₂
  let D₂ := MorphismOfThickenings.mk X X₂ S S₂ i₂ t₂ f f₂ hi₂.1 ht₂.1 r₂
  let D₃ := MorphismOfThickenings.mk X X₃ S S₃ (i₂ ≫ h) (t₂ ≫ g) f f₃ hi₃ ht₃ r₃
  let Q := (modulePullback i₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf i₂)
  let X0 : (modulePushforward i₂).obj Q ⟶ SheafOfModules.unit (structureSheafRing X₂) :=
    inv ((modulePullbackPushforwardAdjunction i₂).unit.app
      (AlgebraicGeometry.SheafOfModules.idealSheaf i₂)) ≫ idealSheafι i₂
  let X1 : (modulePushforward (i₂ ≫ h)).obj Q ⟶
      (modulePushforward h).obj (SheafOfModules.unit (structureSheafRing X₂)) :=
    (modulePushforwardComp i₂ h).inv.app Q ≫ (modulePushforward h).map X0
  let M := (modulePushforwardSquareIso f f₃ (i₂ ≫ h) (t₂ ≫ g) r₃).inv.app Q ≫
    (modulePushforward f₃).map X1
  let THX : (modulePullback (i₂ ≫ h)).obj (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h))
      ⟶ Q :=
    (modulePullbackComp i₂ h).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf (i₂ ≫ h)) ≫
      (modulePullback i₂).map (Stacks.ClosedImmersion.idealSheafMap
        (comp_eq_id_comp (rfl : i₂ ≫ h = i₂ ≫ h)))
  let THS : (modulePullback (t₂ ≫ g)).obj (AlgebraicGeometry.SheafOfModules.idealSheaf (t₂ ≫ g))
      ⟶ (modulePullback t₂).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t₂) :=
    (modulePullbackComp t₂ g).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf (t₂ ≫ g)) ≫
      (modulePullback t₂).map (Stacks.ClosedImmersion.idealSheafMap
        (comp_eq_id_comp (rfl : t₂ ≫ g = t₂ ≫ g)))
  have hL : (modulePullbackPushforwardAdjunction (t₂ ≫ g)).homEquiv _ _
      ((modulePullbackPushforwardAdjunction f).homEquiv _ _ (D₃.baseToSourceIdeal ≫ THX)) ≫ M =
      Stacks.ClosedImmersion.idealSheafι (t₂ ≫ g) ≫ structureSheafModuleHom f₃ ≫
        (modulePushforward f₃).map (structureSheafModuleHom h) := by
    have hT : (modulePullbackPushforwardAdjunction (i₂ ≫ h)).homEquiv _ _ THX ≫ X1 =
        idealSheafι (i₂ ≫ h) ≫ structureSheafModuleHom h := by
      have := homEquiv_thickeningIdealMap_comp i₂ (i₂ ≫ h) h rfl hi₂
      rwa [thickeningIdealMap_eq] at this
    rw [homEquiv_baseToSourceIdeal_comp D₃, Category.assoc]
    change _ ≫ (modulePushforwardSquareIso D₃.f D₃.f' D₃.i D₃.t D₃.comm).hom.app Q ≫
      (modulePushforwardSquareIso D₃.f D₃.f' D₃.i D₃.t D₃.comm).inv.app Q ≫ _ = _
    rw [Iso.hom_inv_id_app_assoc, ← Adjunction.homEquiv_naturality_right, Category.assoc]
    change ((modulePullbackPushforwardAdjunction f₃).homEquiv _ _)
      (D₃.idealMap.1 ≫ (modulePullbackPushforwardAdjunction (i₂ ≫ h)).homEquiv _ _ THX ≫ X1) = _
    rw [hT]
    exact (congrArg _ (Category.assoc _ _ _).symm).trans
      ((Adjunction.homEquiv_naturality_right _ _ _).trans
        ((congrArg (· ≫ _) (MorphismOfThickenings.homEquiv_idealMap_comp_idealι D₃)).trans
          (Category.assoc _ _ _)))
  have hτ : (modulePushforward g).map
        ((modulePushforwardSquareIso f f₂ i₂ t₂ r₂).hom.app Q) ≫
      (modulePushforwardComp t₂ g).hom.app ((modulePushforward f).obj Q) ≫
      (modulePushforwardSquareIso f f₃ (i₂ ≫ h) (t₂ ≫ g) r₃).inv.app Q ≫
      (modulePushforward f₃).map ((modulePushforwardComp i₂ h).inv.app Q) =
      (modulePushforwardComp f₂ g).hom.app ((modulePushforward i₂).obj Q) ≫
        eqToHom (congrArg (fun k : X₂ ⟶ S₃ => (modulePushforward k).obj
          ((modulePushforward i₂).obj Q)) c.symm) ≫
        (modulePushforwardComp h f₃).inv.app ((modulePushforward i₂).obj Q) := by
    have hsq : ∀ {a b c' d : RingedSpace.{u, u}} (a₁ : a ⟶ b) (b₁ : b ⟶ d) (c₁ : a ⟶ c')
        (d₁ : c' ⟶ d) (e : a₁ ≫ b₁ = c₁ ≫ d₁) (N : SheafOfModules.{u} (structureSheafRing a)),
        IsSectionIdentity ((modulePushforwardSquareIso c₁ b₁ a₁ d₁ e).hom.app N) := by
      intro a b c' d a₁ b₁ c₁ d₁ e N
      rw [modulePushforwardSquareIso_hom_app]
      exact isSectionIdentity_comp (isSectionIdentity_modulePushforwardComp_hom _ _ _)
        (isSectionIdentity_comp (isSectionIdentity_eqToHom _)
          (isSectionIdentity_modulePushforwardComp_inv _ _ _))
    refine eq_of_isSectionIdentity ?_ ?_
    · exact isSectionIdentity_comp (isSectionIdentity_modulePushforward g (hsq _ _ _ _ r₂ _))
        (isSectionIdentity_comp (isSectionIdentity_modulePushforwardComp_hom _ _ _)
          (isSectionIdentity_comp (isSectionIdentity_inv
            ((modulePushforwardSquareIso f f₃ (i₂ ≫ h) (t₂ ≫ g) r₃).app Q) (hsq _ _ _ _ r₃ _))
            (isSectionIdentity_modulePushforward f₃
              (isSectionIdentity_modulePushforwardComp_inv _ _ _))))
    · exact isSectionIdentity_comp (isSectionIdentity_modulePushforwardComp_hom _ _ _)
        (isSectionIdentity_comp (isSectionIdentity_eqToHom _)
          (isSectionIdentity_modulePushforwardComp_inv _ _ _))
  have hb2 : (modulePullbackPushforwardAdjunction t₂).homEquiv _ _
      ((modulePullbackPushforwardAdjunction f).homEquiv _ _ D₂.baseToSourceIdeal) =
      (modulePullbackPushforwardAdjunction f₂).homEquiv _ _
          (D₂.idealMap.1 ≫ (modulePullbackPushforwardAdjunction i₂).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i₂)) ≫
        (modulePushforwardSquareIso f f₂ i₂ t₂ r₂).hom.app Q := by
    have := homEquiv_baseToSourceIdeal_comp D₂ (𝟙 _)
    rwa [Category.comp_id, Adjunction.homEquiv_id] at this
  have hR : (modulePullbackPushforwardAdjunction (t₂ ≫ g)).homEquiv _ _
      ((modulePullbackPushforwardAdjunction f).homEquiv _ _
        ((modulePullback f).map THS ≫ D₂.baseToSourceIdeal)) ≫ M =
      Stacks.ClosedImmersion.idealSheafι (t₂ ≫ g) ≫ structureSheafModuleHom f₃ ≫
        (modulePushforward f₃).map (structureSheafModuleHom h) := by
    rw [Adjunction.homEquiv_naturality_left, Category.assoc, homEquiv_modulePullbackComp_hom',
      Adjunction.homEquiv_naturality_left, hb2, ← Category.assoc,
      Adjunction.homEquiv_naturality_right, Category.assoc, Category.assoc]
    have hX1 : (modulePushforward f₃).map X1 =
        (modulePushforward f₃).map ((modulePushforwardComp i₂ h).inv.app Q) ≫
          (modulePushforward f₃).map ((modulePushforward h).map X0) := Functor.map_comp _ _ _
    rw [Functor.map_comp, Category.assoc, hX1]
    simp only [Category.assoc]
    rw [reassoc_of% hτ, modulePushforwardComp_eqToHom_naturality f₂ g h f₃ c.symm X0]
    have hu : (modulePullbackPushforwardAdjunction f₂).homEquiv _ _
          (D₂.idealMap.1 ≫ (modulePullbackPushforwardAdjunction i₂).unit.app
            (AlgebraicGeometry.SheafOfModules.idealSheaf i₂)) ≫ (modulePushforward f₂).map X0 =
        Stacks.ClosedImmersion.idealSheafι t₂ ≫ structureSheafModuleHom f₂ := by
      rw [← Adjunction.homEquiv_naturality_right, Category.assoc, IsIso.hom_inv_id_assoc]
      exact MorphismOfThickenings.homEquiv_idealMap_comp_idealι D₂
    have hg : (modulePullbackPushforwardAdjunction g).homEquiv
          (AlgebraicGeometry.SheafOfModules.idealSheaf (t₂ ≫ g))
          (AlgebraicGeometry.SheafOfModules.idealSheaf t₂)
          (Stacks.ClosedImmersion.idealSheafMap (comp_eq_id_comp (rfl : t₂ ≫ g = t₂ ≫ g))) ≫
        (modulePushforward g).map (Stacks.ClosedImmersion.idealSheafι t₂) =
        Stacks.ClosedImmersion.idealSheafι (t₂ ≫ g) ≫ structureSheafModuleHom g :=
      (Adjunction.homEquiv_naturality_right _ _ _).symm.trans
        ((Adjunction.homEquiv_unit _ _ _ _).trans
          (Stacks.ClosedImmersion.unit_comp_pushforward_idealSheafMap_comp_ι
            (comp_eq_id_comp (rfl : t₂ ≫ g = t₂ ≫ g))))
    have hfin : structureSheafModuleHom g ≫ (modulePushforward g).map (structureSheafModuleHom f₂) ≫
        (modulePushforwardComp f₂ g).hom.app (SheafOfModules.unit (structureSheafRing X₂)) ≫
        eqToHom (congrArg (fun k : X₂ ⟶ S₃ => (modulePushforward k).obj
          (SheafOfModules.unit (structureSheafRing X₂))) c.symm) ≫
        (modulePushforwardComp h f₃).inv.app (SheafOfModules.unit (structureSheafRing X₂)) =
        structureSheafModuleHom f₃ ≫ (modulePushforward f₃).map (structureSheafModuleHom h) := by
      rw [reassoc_of% structureSheafModuleHom_comp_modulePushforwardComp f₂ g,
        reassoc_of% structureSheafModuleHom_comp_eqToHom c.symm,
        ← structureSheafModuleHom_comp_modulePushforwardComp h f₃, Category.assoc,
        Category.assoc, Iso.hom_inv_id_app]
      exact congrArg (fun z => structureSheafModuleHom f₃ ≫ z) (Category.comp_id _)
    rw [← Functor.map_comp_assoc, hu, Functor.map_comp, Category.assoc, reassoc_of% hg, hfin]
  have hpm : ∀ {A B : RingedSpace.{u, u}} (k : A ⟶ B)
      {P P' : SheafOfModules.{u} (structureSheafRing A)} (φ : P ⟶ P'), Mono φ →
        Mono ((modulePushforward k).map φ) := by
    intro A B k P P' φ hφ
    have : (SheafOfModules.pushforward (structureSheafHom k)).IsRightAdjoint :=
      modulePushforward_isRightAdjoint k
    exact (modulePushforward k).map_mono φ
  have hX0 : Mono X0 := mono_comp _ _
  have hM : Mono M := by
    have := hpm h X0 hX0
    have : Mono X1 := mono_comp _ _
    have := hpm f₃ X1 inferInstance
    exact mono_comp _ _
  have key : (modulePullback f).map THS ≫ D₂.baseToSourceIdeal = D₃.baseToSourceIdeal ≫ THX := by
    apply ((modulePullbackPushforwardAdjunction f).homEquiv _ _).injective
    apply ((modulePullbackPushforwardAdjunction (t₂ ≫ g)).homEquiv _ _).injective
    exact (cancel_mono M).1 (hR.trans hL.symm)
  exact (congrArg (fun z => (modulePullback f).map z ≫ D₂.baseToSourceIdeal)
    (thickeningIdealMap_eq t₂ g)).trans
    (key.trans (congrArg (fun z => D₃.baseToSourceIdeal ≫ z) (thickeningIdealMap_eq i₂ h).symm))

end Cube

section Sequence

/-- `thickeningIdealMap_eq` for a morphism `h` with `i₁ ≫ h = i₂` not definitionally. -/
theorem thickeningIdealMap_eq' {X X₁ X₂ : RingedSpace.{u, u}} (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂)
    (h : X₁ ⟶ X₂) (comm : i₁ ≫ h = i₂) :
    thickeningIdealMap i₁ i₂ h comm =
      eqToHom (congrArg (fun k : X ⟶ X₂ => (modulePullback k).obj
          (AlgebraicGeometry.SheafOfModules.idealSheaf i₂)) comm.symm) ≫
        (modulePullbackComp i₁ h).hom.app (AlgebraicGeometry.SheafOfModules.idealSheaf i₂) ≫
        (modulePullback i₁).map (Stacks.ClosedImmersion.idealSheafMap (comp_eq_id_comp comm)) := by
  subst comm
  rw [eqToHom_refl, Category.id_comp]
  exact thickeningIdealMap_eq i₁ h

/-- The ideal-sheaf map of a square is the canonical ideal map of **Stacks 08KZ** of the same
square: both are the kernel lift of the same map into the structure sheaf. -/
theorem idealSheafMap_eq_idealMap (D : MorphismOfThickenings.{u}) (e : D.i ≫ D.f' = D.f ≫ D.t) :
    Stacks.ClosedImmersion.idealSheafMap e = D.idealMap.1 := rfl

namespace FirstOrderThickeningSequence

variable (S : FirstOrderThickeningSequence.{u})

attribute [local implicit_reducible] square₁₂ square₂₃

/-- **The chosen map `ℐ₂ ⟶ ℐ₁` is the map induced by `f₁₂`.** -/
theorem thickeningIdealMap_eq_idealMap₂₁ (h : S.HasInducedIdealMaps) :
    thickeningIdealMap S.i₁ S.i₂ S.f₁₂ S.comm₁₂ = S.idealMap₂₁ := by
  have hp := MorphismOfThickenings.pullback_idealMap_eq S.square₁₂ S.firstOrder₁ S.firstOrder₂ _
    S.idealComparison₂ S.idealMap₂₁ h.1
  have hk : S.idealMap₂₁ = S.idealComparison₂.hom ≫ S.square₁₂.reducedPullbackComparison.inv ≫
      (modulePullback S.i₁).map S.square₁₂.idealMap.1 := by
    change _ = _ ≫ _ ≫ (modulePullback S.square₁₂.i).map S.square₁₂.idealMap.1
    rw [hp, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [hk, thickeningIdealMap_eq', idealSheafMap_eq_idealMap S.square₁₂]
  simp only [idealComparison₂, MorphismOfThickenings.reducedPullbackComparison, square₁₂,
    MorphismOfThickenings.idealJ,
    modulePullbackCompUniq_eq_modulePullbackComp, Iso.trans_hom, Iso.trans_inv, Iso.app_hom,
    Iso.app_inv, Iso.symm_inv, eqToIso.hom, eqToIso.inv, Category.assoc, Iso.hom_inv_id_app_assoc,
    eqToHom_trans_assoc]
  rfl

/-- **The chosen map `ℐ₃ ⟶ ℐ₂` is the map induced by `f₂₃`.** -/
theorem thickeningIdealMap_eq_idealMap₃₂ (h : S.HasInducedIdealMaps) :
    thickeningIdealMap S.i₂ S.i₃ S.f₂₃ S.comm₂₃ = S.idealMap₃₂ := by
  have hp := MorphismOfThickenings.pullback_idealMap_eq S.square₂₃ S.firstOrder₂ S.firstOrder₃ _
    S.idealComparison₃ S.idealMap₃₂ h.2
  have hk : S.idealMap₃₂ = S.idealComparison₃.hom ≫ S.square₂₃.reducedPullbackComparison.inv ≫
      (modulePullback S.i₂).map S.square₂₃.idealMap.1 := by
    change _ = _ ≫ _ ≫ (modulePullback S.square₂₃.i).map S.square₂₃.idealMap.1
    rw [hp, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  rw [hk, thickeningIdealMap_eq', idealSheafMap_eq_idealMap S.square₂₃]
  simp only [idealComparison₃, MorphismOfThickenings.reducedPullbackComparison, square₂₃,
    MorphismOfThickenings.idealJ,
    modulePullbackCompUniq_eq_modulePullbackComp, Iso.trans_hom, Iso.trans_inv, Iso.app_hom,
    Iso.app_inv, Iso.symm_inv, eqToIso.hom, eqToIso.inv, Category.assoc, Iso.hom_inv_id_app_assoc,
    eqToHom_trans_assoc]
  rfl

end FirstOrderThickeningSequence

end Sequence

end AlgebraicGeometry.RingedSpaceThickening
