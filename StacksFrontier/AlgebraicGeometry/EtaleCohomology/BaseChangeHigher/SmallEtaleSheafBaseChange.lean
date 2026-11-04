module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity

/-!
# Inverse images and base change maps of étale sheaves with arbitrary coefficients

Let `A` be a category of coefficients for which the direct image `f_*` of sheaves on the small
étale sites along every morphism of schemes `f` has a left adjoint, the inverse image `f⁻¹`; this
holds for sheaves of sets and for abelian sheaves. This file sets up, for such coefficients, the
formalism of the base change map: for a commutative square of schemes

```
X' ←-h-  Y
|f'      |e
S  ←-g-  T
```

the base change map `f'⁻¹ g_* ⟶ h_* e⁻¹` is the mate, under the two inverse-image/direct-image
adjunctions, of the identification `g_* e_* ≅ f'_* h_*` of the two composite direct images. For
two horizontally composable commutative squares, the base change map of the outer rectangle is
the composite of the base change maps of the two squares, read through the comparisons of the
inverse images along the composites ([Stacks, Tag 0E47] for the underived maps).

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleSheafPullback`: the inverse image `f⁻¹` with coefficients
  in `A`, the left adjoint of `f_*`.
* `Stacks.EtaleCohomology.smallEtaleSheafPullbackComp'`: the comparison
  `f⁻¹ g⁻¹ ≅ (fg)⁻¹` of inverse images along a named composite.
* `Stacks.EtaleCohomology.smallEtaleSheafBaseChange`: the base change map `f'⁻¹ g_* ⟶ h_* e⁻¹`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSheafPullbackCompApp_assoc`: the comparisons of inverse
  images along composites are associative.
* `Stacks.EtaleCohomology.smallEtaleSheafBaseChange_app_eq`: the base change map is adjoint to
  the direct image of the unit followed by the identification of composite direct images.
* `Stacks.EtaleCohomology.smallEtaleSheafBaseChange_paste_app`: the pasting law.

## Implementation notes

The inverse image is Mathlib's `CategoryTheory.Functor.sheafPullback`, the abstract left adjoint
of the direct image, and the comparisons along composites are the comparisons of left adjoints
`CategoryTheory.Adjunction.leftAdjointCompIso` of the comparisons of direct images, so that the
inverse image along a transition of an inverse system of schemes and its comparisons are those of
`Stacks.EtaleCohomology.EtaleSheafSystem`. The comparisons along composites are taken along a
named composite `fg` with an equation `fg = f ≫ g`, which keeps every identity between such
comparisons an identity between morphisms of the same shape.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' u

namespace Stacks.EtaleCohomology

variable (A : Type w) [Category.{w'} A]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (smallEtalePushforward f A).IsRightAdjoint]

/-! ### The inverse image and its comparisons along composites -/

/-- **The inverse image `f⁻¹`** along a morphism of schemes `f : X ⟶ Y`, for sheaves on the small
étale sites with coefficients in `A`: the left adjoint of the direct image `f_*`. -/
abbrev smallEtaleSheafPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology Y) A ⥤ Sheaf (smallEtaleTopology X) A :=
  (smallEtaleBaseChange f).sheafPullback A (smallEtaleTopology Y) (smallEtaleTopology X)

/-- The inverse-image/direct-image adjunction `f⁻¹ ⊣ f_*` on the small étale sites. -/
def smallEtaleSheafAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleSheafPullback A f ⊣ smallEtalePushforward f A :=
  Functor.sheafAdjunctionContinuous (smallEtaleBaseChange f) A (smallEtaleTopology Y)
    (smallEtaleTopology X)

/-- The inverse image along a named composite `fg = f ≫ g` is the composite of the inverse images:
the comparison of left adjoints of `Stacks.EtaleCohomology.smallEtalePushforwardComp'`. -/
def smallEtaleSheafPullbackComp' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    smallEtaleSheafPullback A g ⋙ smallEtaleSheafPullback A f ≅ smallEtaleSheafPullback A fg :=
  Adjunction.leftAdjointCompIso (smallEtaleSheafAdjunction A g) (smallEtaleSheafAdjunction A f)
    (smallEtaleSheafAdjunction A fg) (smallEtalePushforwardComp' f g fg hfg A)

/-- The component at a sheaf `M` of the comparison of inverse images along a named composite,
with its source written as the iterated inverse image `f⁻¹(g⁻¹M)`. -/
def smallEtaleSheafPullbackCompApp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (M : Sheaf (smallEtaleTopology Z) A) :
    (smallEtaleSheafPullback A f).obj ((smallEtaleSheafPullback A g).obj M) ≅
      (smallEtaleSheafPullback A fg).obj M :=
  (smallEtaleSheafPullbackComp' A f g fg hfg).app M

/-- The components of the comparison `f⁻¹ g⁻¹ ≅ (fg)⁻¹` are natural in the sheaf. -/
theorem smallEtaleSheafPullbackCompApp_hom_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) {M N : Sheaf (smallEtaleTopology Z) A}
    (φ : M ⟶ N) :
    (smallEtaleSheafPullback A f).map ((smallEtaleSheafPullback A g).map φ) ≫
        (smallEtaleSheafPullbackCompApp A f g fg hfg N).hom =
      (smallEtaleSheafPullbackCompApp A f g fg hfg M).hom ≫
        (smallEtaleSheafPullback A fg).map φ :=
  (smallEtaleSheafPullbackComp' A f g fg hfg).hom.naturality φ

/-- The inverses of the components of the comparison `f⁻¹ g⁻¹ ≅ (fg)⁻¹` are natural in the
sheaf. -/
theorem smallEtaleSheafPullbackCompApp_inv_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) {M N : Sheaf (smallEtaleTopology Z) A}
    (φ : M ⟶ N) :
    (smallEtaleSheafPullback A fg).map φ ≫ (smallEtaleSheafPullbackCompApp A f g fg hfg N).inv =
      (smallEtaleSheafPullbackCompApp A f g fg hfg M).inv ≫
        (smallEtaleSheafPullback A f).map ((smallEtaleSheafPullback A g).map φ) :=
  (smallEtaleSheafPullbackComp' A f g fg hfg).inv.naturality φ

/-- **The associativity pentagon of the comparisons of inverse images**, the left adjoint form of
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc`. -/
theorem smallEtaleSheafPullbackComp'_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) :
    Functor.isoWhiskerLeft (smallEtaleSheafPullback A h)
          (smallEtaleSheafPullbackComp' A f g fg hfg) ≪≫
        smallEtaleSheafPullbackComp' A fg h fgh h₁ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtaleSheafPullbackComp' A g h gh hgh)
          (smallEtaleSheafPullback A f) ≪≫
          smallEtaleSheafPullbackComp' A f gh fgh h₂ :=
  Adjunction.leftAdjointCompIso_assoc (smallEtaleSheafAdjunction A h)
    (smallEtaleSheafAdjunction A g) (smallEtaleSheafAdjunction A f)
    (smallEtaleSheafAdjunction A gh) (smallEtaleSheafAdjunction A fg)
    (smallEtaleSheafAdjunction A fgh) (smallEtalePushforwardComp' g h gh hgh A)
    (smallEtalePushforwardComp' f g fg hfg A) (smallEtalePushforwardComp' fg h fgh h₁ A)
    (smallEtalePushforwardComp' f gh fgh h₂ A)
    (by
      refine Iso.ext (NatTrans.ext (funext fun F => ?_))
      have := congrArg (fun z : _ ≅ _ => NatTrans.app z.hom F)
        (smallEtalePushforwardComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂ A)
      simpa using this.symm)

/-- The associativity pentagon, on components with iterated inverse images as sources. -/
theorem smallEtaleSheafPullbackCompApp_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) (M : Sheaf (smallEtaleTopology Z) A) :
    (smallEtaleSheafPullbackCompApp A f g fg hfg ((smallEtaleSheafPullback A h).obj M)).hom ≫
        (smallEtaleSheafPullbackCompApp A fg h fgh h₁ M).hom =
      (smallEtaleSheafPullback A f).map (smallEtaleSheafPullbackCompApp A g h gh hgh M).hom ≫
        (smallEtaleSheafPullbackCompApp A f gh fgh h₂ M).hom := by
  have h0 := congrArg (fun z : _ ≅ _ => NatTrans.app z.hom M)
    (smallEtaleSheafPullbackComp'_assoc A f g h fg hfg gh hgh fgh h₁ h₂)
  show (smallEtaleSheafPullbackComp' A f g fg hfg).hom.app ((smallEtaleSheafPullback A h).obj M) ≫
      (smallEtaleSheafPullbackComp' A fg h fgh h₁).hom.app M =
    (smallEtaleSheafPullback A f).map ((smallEtaleSheafPullbackComp' A g h gh hgh).hom.app M) ≫
      (smallEtaleSheafPullbackComp' A f gh fgh h₂).hom.app M
  simpa using h0

/-- The comparison of inverse images, transposed: the comparison of direct images. -/
theorem conjugateEquiv_smallEtaleSheafPullbackComp'_inv {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    conjugateEquiv ((smallEtaleSheafAdjunction A g).comp (smallEtaleSheafAdjunction A f))
        (smallEtaleSheafAdjunction A fg) (smallEtaleSheafPullbackComp' A f g fg hfg).inv =
      (smallEtalePushforwardComp' f g fg hfg A).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

/-- The comparison of inverse images, transposed, in the other direction. -/
theorem conjugateEquiv_smallEtaleSheafPullbackComp'_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    conjugateEquiv (smallEtaleSheafAdjunction A fg)
        ((smallEtaleSheafAdjunction A g).comp (smallEtaleSheafAdjunction A f))
        (smallEtaleSheafPullbackComp' A f g fg hfg).hom =
      (smallEtalePushforwardComp' f g fg hfg A).inv := by
  have h : conjugateIsoEquiv ((smallEtaleSheafAdjunction A g).comp (smallEtaleSheafAdjunction A f))
      (smallEtaleSheafAdjunction A fg) (smallEtaleSheafPullbackComp' A f g fg hfg).symm =
      smallEtalePushforwardComp' f g fg hfg A :=
    Iso.ext (conjugateEquiv_smallEtaleSheafPullbackComp'_inv A f g fg hfg)
  exact congrArg Iso.inv h

/-- **The unit of a composite of inverse-image/direct-image adjunctions.** The unit of
`(fg)⁻¹ ⊣ (fg)_*` is the unit of `g⁻¹ ⊣ g_*` followed by the direct image of the unit of
`f⁻¹ ⊣ f_*`, the comparison of direct images and the comparison of inverse images. -/
theorem smallEtaleSheafAdjunction_unit_app_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (H : Sheaf (smallEtaleTopology Z) A) :
    (smallEtaleSheafAdjunction A fg).unit.app H =
      (smallEtaleSheafAdjunction A g).unit.app H ≫
        (smallEtalePushforward g A).map
          ((smallEtaleSheafAdjunction A f).unit.app ((smallEtaleSheafPullback A g).obj H)) ≫
          (smallEtalePushforwardComp' f g fg hfg A).hom.app _ ≫
            (smallEtalePushforward fg A).map
              (smallEtaleSheafPullbackCompApp A f g fg hfg H).hom := by
  have h := unit_conjugateEquiv
    ((smallEtaleSheafAdjunction A g).comp (smallEtaleSheafAdjunction A f))
    (smallEtaleSheafAdjunction A fg) (smallEtaleSheafPullbackComp' A f g fg hfg).inv H
  rw [conjugateEquiv_smallEtaleSheafPullbackComp'_inv, Adjunction.comp_unit_app] at h
  rw [← cancel_mono ((smallEtalePushforward fg A).map
    (smallEtaleSheafPullbackCompApp A f g fg hfg H).inv)]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.comp_id]
  exact h.symm.trans (Category.assoc _ _ _)

/-! ### The base change map -/

section Square

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The identification `g_* e_* ≅ f'_* h_*` of the two composite direct images around the
commutative square `h ≫ f' = e ≫ g`, through the common diagonal `h ≫ f'`. -/
def smallEtaleSheafSquarePushforwardComp :
    smallEtalePushforward e A ⋙ smallEtalePushforward g A ≅
      smallEtalePushforward h A ⋙ smallEtalePushforward f' A :=
  smallEtalePushforwardComp' e g (h ≫ f') w A ≪≫
    (smallEtalePushforwardComp' h f' (h ≫ f') rfl A).symm

/-- **The base change map `f'⁻¹ g_* ⟶ h_* e⁻¹`** of a commutative square `h ≫ f' = e ≫ g` of
schemes, for sheaves with coefficients in `A`: the mate of the identification of the two
composite direct images under the adjunctions `e⁻¹ ⊣ e_*` and `f'⁻¹ ⊣ f'_*`. -/
def smallEtaleSheafBaseChange :
    smallEtalePushforward g A ⋙ smallEtaleSheafPullback A f' ⟶
      smallEtaleSheafPullback A e ⋙ smallEtalePushforward h A :=
  (mateEquiv (smallEtaleSheafAdjunction A e) (smallEtaleSheafAdjunction A f')).symm
    (TwoSquare.mk _ _ _ _ (smallEtaleSheafSquarePushforwardComp A f' g h e w).hom)

/-- The mate of the base change map is the identification of the two composite direct images. -/
theorem mateEquiv_smallEtaleSheafBaseChange :
    mateEquiv (smallEtaleSheafAdjunction A e) (smallEtaleSheafAdjunction A f')
        (TwoSquare.mk _ _ _ _ (smallEtaleSheafBaseChange A f' g h e w)) =
      TwoSquare.mk _ _ _ _ (smallEtaleSheafSquarePushforwardComp A f' g h e w).hom :=
  Equiv.apply_symm_apply _ _

/-- **The base change map is adjoint to the direct image of the unit** followed by the
identification of the two composite direct images. -/
theorem smallEtaleSheafBaseChange_app_eq (F : Sheaf (smallEtaleTopology T) A) :
    (smallEtaleSheafBaseChange A f' g h e w).app F =
      ((smallEtaleSheafAdjunction A f').homEquiv _ _).symm
        ((smallEtalePushforward g A).map ((smallEtaleSheafAdjunction A e).unit.app F) ≫
          (smallEtaleSheafSquarePushforwardComp A f' g h e w).hom.app
            ((smallEtaleSheafPullback A e).obj F)) := by
  rw [Equiv.eq_symm_apply, Adjunction.homEquiv_unit]
  exact (unit_mateEquiv_symm (smallEtaleSheafAdjunction A e) (smallEtaleSheafAdjunction A f')
    (TwoSquare.mk _ _ _ _ (smallEtaleSheafSquarePushforwardComp A f' g h e w).hom) F).symm

/-- The base change map is natural in the sheaf. -/
theorem smallEtaleSheafBaseChange_naturality {F G : Sheaf (smallEtaleTopology T) A}
    (φ : F ⟶ G) :
    (smallEtaleSheafPullback A f').map ((smallEtalePushforward g A).map φ) ≫
        (smallEtaleSheafBaseChange A f' g h e w).app G =
      (smallEtaleSheafBaseChange A f' g h e w).app F ≫
        (smallEtalePushforward h A).map ((smallEtaleSheafPullback A e).map φ) :=
  (smallEtaleSheafBaseChange A f' g h e w).naturality φ

/-- **The adjoint of a base change map followed by a direct image.** For a map
`ι : e⁻¹B ⟶ C`, the map adjoint to the base change map followed by `h_* ι` is the direct image
along `g` of the adjoint of `ι`, followed by the identification of the composite direct
images. -/
theorem smallEtaleSheafAdjunction_homEquiv_baseChange {B : Sheaf (smallEtaleTopology T) A}
    {C : Sheaf (smallEtaleTopology Y) A} (ι : (smallEtaleSheafPullback A e).obj B ⟶ C) :
    (smallEtaleSheafAdjunction A f').homEquiv _ _
        ((smallEtaleSheafBaseChange A f' g h e w).app B ≫ (smallEtalePushforward h A).map ι) =
      (smallEtalePushforward g A).map ((smallEtaleSheafAdjunction A e).homEquiv _ _ ι) ≫
        (smallEtaleSheafSquarePushforwardComp A f' g h e w).hom.app C := by
  rw [Adjunction.homEquiv_naturality_right, smallEtaleSheafBaseChange_app_eq]
  simp only [Functor.id_obj, Functor.comp_obj, Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc]
  congr 1
  exact ((smallEtaleSheafSquarePushforwardComp A f' g h e w).hom.naturality ι).symm

end Square

/-! ### The pasting law -/

section Paste

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
  (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁)

/-- A functor applied to an inverse and then to the forward component of a natural isomorphism
cancels. -/
private theorem map_inv_app_hom_app_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    (F : D ⥤ E) {G H : C ⥤ D} (e : G ≅ H) (X : C) {Z : E} (k : F.obj (H.obj X) ⟶ Z) :
    F.map (e.inv.app X) ≫ F.map (e.hom.app X) ≫ k = k := by
  simp [← Functor.map_comp_assoc]

omit [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (smallEtalePushforward f A).IsRightAdjoint] in
/-- The associativity pentagon of the comparisons of direct images, evaluated at a sheaf. -/
private theorem pushforwardComp'_assoc_app {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) (F : Sheaf (smallEtaleTopology T) A) :
    (smallEtalePushforward h A).map ((smallEtalePushforwardComp' f g fg hfg A).hom.app F) ≫
        (smallEtalePushforwardComp' fg h fgh h₁ A).hom.app F =
      (smallEtalePushforwardComp' g h gh hgh A).hom.app ((smallEtalePushforward f A).obj F) ≫
        (smallEtalePushforwardComp' f gh fgh h₂ A).hom.app F := by
  have h0 := congrArg (fun z : _ ≅ _ => NatTrans.app z.hom F)
    (smallEtalePushforwardComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂ A)
  simpa using h0

omit [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (smallEtalePushforward f A).IsRightAdjoint] in
/-- **The pasting of the identifications of composite direct images.** -/
theorem smallEtaleSheafSquarePushforwardComp_paste_app
    (𝓖 : Sheaf (smallEtaleTopology X₂) A) :
    (smallEtaleSheafSquarePushforwardComp A (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
          (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)).hom.app 𝓖 =
      (smallEtalePushforward g₀ A).map
          ((smallEtalePushforwardComp' v₂ v₁ (v₂ ≫ v₁) rfl A).inv.app 𝓖) ≫
        (smallEtaleSheafSquarePushforwardComp A u₁ g₀ g₁ v₁ w₁).hom.app
            ((smallEtalePushforward v₂ A).obj 𝓖) ≫
          (smallEtalePushforward u₁ A).map
              ((smallEtaleSheafSquarePushforwardComp A u₂ g₁ g₂ v₂ w₂).hom.app 𝓖) ≫
            (smallEtalePushforwardComp' u₂ u₁ (u₂ ≫ u₁) rfl A).hom.app
              ((smallEtalePushforward g₂ A).obj 𝓖) := by
  have hL : g₂ ≫ u₂ ≫ u₁ = v₂ ≫ g₁ ≫ u₁ := by rw [← Category.assoc, w₂, Category.assoc]
  have hM : g₂ ≫ u₂ ≫ u₁ = (g₂ ≫ u₂) ≫ u₁ := (Category.assoc _ _ _).symm
  have hw₀ := smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂
  have hP₁ := pushforwardComp'_assoc_app A v₂ v₁ g₀ (v₂ ≫ v₁) rfl (g₁ ≫ u₁) w₁
    (g₂ ≫ u₂ ≫ u₁) hw₀ hL 𝓖
  have hP₂ := pushforwardComp'_assoc_app A v₂ g₁ u₁ (g₂ ≫ u₂) w₂ (g₁ ≫ u₁) rfl
    (g₂ ≫ u₂ ≫ u₁) hM hL 𝓖
  have hP₃ := pushforwardComp'_assoc_app A g₂ u₂ u₁ (g₂ ≫ u₂) rfl (u₂ ≫ u₁) rfl
    (g₂ ≫ u₂ ≫ u₁) hM rfl 𝓖
  simp only [smallEtaleSheafSquarePushforwardComp, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← cancel_mono ((smallEtalePushforwardComp' g₂ (u₂ ≫ u₁) (g₂ ≫ u₂ ≫ u₁) rfl A).hom.app 𝓖)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← hP₃, map_inv_app_hom_app_assoc, hP₂, Iso.inv_hom_id_app_assoc, ← hP₁,
    map_inv_app_hom_app_assoc]

include w₁ w₂ in
/-- **The pasting law for the base change map**, as an identity of `2`-squares. -/
theorem smallEtaleSheafBaseChange_paste :
    TwoSquare.mk _ _ _ _
        (smallEtaleSheafBaseChange A (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
          (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)) =
      ((TwoSquare.vComp (TwoSquare.mk _ _ _ _ (smallEtaleSheafBaseChange A u₁ g₀ g₁ v₁ w₁))
            (TwoSquare.mk _ _ _ _ (smallEtaleSheafBaseChange A u₂ g₁ g₂ v₂ w₂))).whiskerLeft
          (smallEtaleSheafPullbackComp' A v₂ v₁ (v₂ ≫ v₁) rfl).hom).whiskerRight
        (smallEtaleSheafPullbackComp' A u₂ u₁ (u₂ ≫ u₁) rfl).inv := by
  apply (mateEquiv (smallEtaleSheafAdjunction A (v₂ ≫ v₁))
    (smallEtaleSheafAdjunction A (u₂ ≫ u₁))).injective
  rw [mateEquiv_conjugateEquiv_vcomp (smallEtaleSheafAdjunction A (v₂ ≫ v₁))
      ((smallEtaleSheafAdjunction A u₁).comp (smallEtaleSheafAdjunction A u₂))
      (smallEtaleSheafAdjunction A (u₂ ≫ u₁)),
    conjugateEquiv_mateEquiv_vcomp (smallEtaleSheafAdjunction A (v₂ ≫ v₁))
      ((smallEtaleSheafAdjunction A v₁).comp (smallEtaleSheafAdjunction A v₂))
      ((smallEtaleSheafAdjunction A u₁).comp (smallEtaleSheafAdjunction A u₂)),
    mateEquiv_hcomp (smallEtaleSheafAdjunction A v₁) (smallEtaleSheafAdjunction A u₁)
      (smallEtaleSheafAdjunction A v₂) (smallEtaleSheafAdjunction A u₂),
    conjugateEquiv_smallEtaleSheafPullbackComp'_hom,
    conjugateEquiv_smallEtaleSheafPullbackComp'_inv,
    mateEquiv_smallEtaleSheafBaseChange, mateEquiv_smallEtaleSheafBaseChange,
    mateEquiv_smallEtaleSheafBaseChange]
  refine TwoSquare.ext _ _ fun 𝓖 => ?_
  simpa using smallEtaleSheafSquarePushforwardComp_paste_app A g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ 𝓖

include w₁ w₂ in
/-- **The pasting law, evaluated at a sheaf.** -/
theorem smallEtaleSheafBaseChange_paste_app (F : Sheaf (smallEtaleTopology X₀) A) :
    (smallEtaleSheafBaseChange A (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
          (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)).app F =
      (smallEtaleSheafPullbackComp' A u₂ u₁ (u₂ ≫ u₁) rfl).inv.app
          ((smallEtalePushforward g₀ A).obj F) ≫
        (smallEtaleSheafPullback A u₂).map ((smallEtaleSheafBaseChange A u₁ g₀ g₁ v₁ w₁).app F) ≫
          (smallEtaleSheafBaseChange A u₂ g₁ g₂ v₂ w₂).app ((smallEtaleSheafPullback A v₁).obj F) ≫
            (smallEtalePushforward g₂ A).map
              ((smallEtaleSheafPullbackComp' A v₂ v₁ (v₂ ≫ v₁) rfl).hom.app F) := by
  have h := congr_app (smallEtaleSheafBaseChange_paste A g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) F
  simpa using h

/-- **The pasting law with the composites named.** For composites `u = u₂ ≫ u₁` and
`v = v₂ ≫ v₁` given with their equations, the base change map of the outer rectangle is the
composite of the base change maps of the two squares, read through the comparisons of inverse
images along the named composites. -/
theorem smallEtaleSheafBaseChange_paste_app_named (u : S₂ ⟶ S₀) (hu : u = u₂ ≫ u₁)
    (v : X₂ ⟶ X₀) (hv : v = v₂ ≫ v₁) (w : g₂ ≫ u = v ≫ g₀)
    (F : Sheaf (smallEtaleTopology X₀) A) :
    (smallEtaleSheafBaseChange A u g₀ g₂ v w).app F =
      (smallEtaleSheafPullbackCompApp A u₂ u₁ u hu ((smallEtalePushforward g₀ A).obj F)).inv ≫
        (smallEtaleSheafPullback A u₂).map ((smallEtaleSheafBaseChange A u₁ g₀ g₁ v₁ w₁).app F) ≫
          (smallEtaleSheafBaseChange A u₂ g₁ g₂ v₂ w₂).app ((smallEtaleSheafPullback A v₁).obj F) ≫
            (smallEtalePushforward g₂ A).map
              (smallEtaleSheafPullbackCompApp A v₂ v₁ v hv F).hom := by
  subst hu hv
  exact smallEtaleSheafBaseChange_paste_app A g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ F

end Paste

/-! ### Base change of a pushed-forward adjoint -/

section Cube

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (γ₀ : X₀ ⟶ S₀) (γ₁ : X₁ ⟶ S₁) (γ₂ : X₂ ⟶ S₂)
  (φ : X₁ ⟶ X₀) (χ : S₁ ⟶ S₀) (φ' : X₂ ⟶ X₁) (χ' : S₂ ⟶ S₁) (φ'' : X₂ ⟶ X₀) (χ'' : S₂ ⟶ S₀)
  (hφ : φ'' = φ' ≫ φ) (hχ : χ'' = χ' ≫ χ) (w₁ : γ₁ ≫ χ = φ ≫ γ₀) (w₂ : γ₂ ≫ χ' = φ' ≫ γ₁)
  (w₃ : γ₂ ≫ χ'' = φ'' ≫ γ₀)
  {M : Sheaf (smallEtaleTopology X₁) A} {N : Sheaf (smallEtaleTopology X₂) A}
  (ι : (smallEtaleSheafPullback A φ').obj M ⟶ N)

include hφ hχ in
/-- **Base change of a pushed-forward adjoint.** Consider two commutative squares
`γ₁ ≫ χ = φ ≫ γ₀` and `γ₂ ≫ χ' = φ' ≫ γ₁` with composite `γ₂ ≫ χ'' = φ'' ≫ γ₀`, where
`φ'' = φ' ≫ φ` and `χ'' = χ' ≫ χ`, and let `ι : φ'⁻¹M ⟶ N`. The direct image along `γ₀` of the
map `φ_* M ⟶ φ''_* N` given by the adjoint of `ι` corresponds, through the identifications of
composite direct images of the squares, to the map `χ_* γ₁_* M ⟶ χ''_* γ₂_* N` given by the
adjoint of the base change map of the square `γ₂ ≫ χ' = φ' ≫ γ₁` followed by `γ₂_* ι`. -/
theorem smallEtalePushforward_map_comp_smallEtaleSheafSquarePushforwardComp :
    (smallEtalePushforward γ₀ A).map
          ((smallEtalePushforward φ A).map ((smallEtaleSheafAdjunction A φ').homEquiv _ _ ι) ≫
            (smallEtalePushforwardComp' φ' φ φ'' hφ A).hom.app N) ≫
        (smallEtaleSheafSquarePushforwardComp A χ'' γ₀ γ₂ φ'' w₃).hom.app N =
      (smallEtaleSheafSquarePushforwardComp A χ γ₀ γ₁ φ w₁).hom.app M ≫
        (smallEtalePushforward χ A).map ((smallEtaleSheafAdjunction A χ').homEquiv _ _
            ((smallEtaleSheafBaseChange A χ' γ₁ γ₂ φ' w₂).app M ≫
              (smallEtalePushforward γ₂ A).map ι)) ≫
          (smallEtalePushforwardComp' χ' χ χ'' hχ A).hom.app
            ((smallEtalePushforward γ₂ A).obj N) := by
  subst hφ hχ
  have hP := smallEtaleSheafSquarePushforwardComp_paste_app A γ₀ γ₁ γ₂ χ χ' φ φ' w₁ w₂ N
  have hn : (smallEtalePushforward γ₀ A).map
        ((smallEtalePushforward φ A).map ((smallEtaleSheafAdjunction A φ').homEquiv _ _ ι)) ≫
        (smallEtaleSheafSquarePushforwardComp A χ γ₀ γ₁ φ w₁).hom.app
          ((smallEtalePushforward φ' A).obj N) =
      (smallEtaleSheafSquarePushforwardComp A χ γ₀ γ₁ φ w₁).hom.app M ≫
        (smallEtalePushforward χ A).map
          ((smallEtalePushforward γ₁ A).map ((smallEtaleSheafAdjunction A φ').homEquiv _ _ ι)) :=
    (smallEtaleSheafSquarePushforwardComp A χ γ₀ γ₁ φ w₁).hom.naturality
      ((smallEtaleSheafAdjunction A φ').homEquiv _ _ ι)
  rw [smallEtaleSheafAdjunction_homEquiv_baseChange, hP]
  simp [reassoc_of% hn]

end Cube

end Stacks.EtaleCohomology

end
