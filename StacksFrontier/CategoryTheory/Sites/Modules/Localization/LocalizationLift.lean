module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationLeftExactExtension

/-!
# Morphisms of ringed topoi into a localization

Let `X` be a ringed topos, `G` a sheaf of sets on it and `j_G : (Sh(C)/G, O_G) ⟶ (Sh(C), O)` the
localization morphism. Two morphisms of ringed topoi `a, b : T ⟶ (Sh(C)/G, O_G)` are
2-isomorphic as soon as `j_G ∘ a` and `j_G ∘ b` are, by a 2-isomorphism carrying the pulled back
tautological section `a⁻¹(τ)` to `b⁻¹(τ)`: a morphism into a localization is its composite with the
localization morphism together with a section of the pulled back sheaf.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIso`: the isomorphism of inverse images
  conjugate to a 2-isomorphism of ringed topoi.
* `AlgebraicGeometry.RingedTopos.localizationTwoIso`: the 2-isomorphism `a ≅ b` of morphisms into
  a localization.

## Main results

* `AlgebraicGeometry.RingedToposHom.TwoIso.inverseImageIso_fSharpInverseImage`: the conjugate of
  a 2-isomorphism is compatible with the inverse-image form of the structure maps.
* `AlgebraicGeometry.RingedTopos.localizationEquivalence_map_tautologicalSection`: under the
  identification of a localization with a slice topos, the tautological section is the diagonal.
* `AlgebraicGeometry.RingedTopos.localizedToposMorphism_map_tautologicalSection`: the localized
  morphism of Stacks 04IF preserves the tautological section.
* `AlgebraicGeometry.RingedToposHom.relocalized_map_tautologicalSection`: the morphism of
  Stacks 04J8 pulls the tautological section of `G` back to `s`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe v₁ u₁ w₁ v₂ u₂ w₂ v₃ u₃ w₃ v₄ u₄ w₄

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- The isomorphism of inverse images `q⁻¹ ≅ p⁻¹` conjugate to a 2-isomorphism `p ≅ q` of
morphisms of ringed topoi. -/
noncomputable def inverseImageIso {p q : RingedToposHom A B} (s : TwoIso p q) :
    q.toToposHom.inverseImage ≅ p.toToposHom.inverseImage :=
  (conjugateIsoEquiv p.toToposHom.adj q.toToposHom.adj).symm s.e

/-- Taking the conjugate isomorphism of inverse images undoes
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`. -/
@[simp]
theorem inverseImageIso_ofInverseImageIso {p q : RingedToposHom A B}
    (α : q.toToposHom.inverseImage ≅ p.toToposHom.inverseImage)
    (h : α.hom.app (B.forgetRing.obj B.O) ≫ A.forgetRing.map p.fSharpInverseImage =
      A.forgetRing.map q.fSharpInverseImage) :
    (ofInverseImageIso α h).inverseImageIso = α :=
  (conjugateIsoEquiv p.toToposHom.adj q.toToposHom.adj).symm_apply_apply α

/-- **The conjugate of a 2-isomorphism of ringed topoi is compatible with the structure maps in
inverse-image form.** This is the converse of
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso`. -/
theorem inverseImageIso_fSharpInverseImage {p q : RingedToposHom A B} (s : TwoIso p q) :
    s.inverseImageIso.hom.app (B.forgetRing.obj B.O) ≫ A.forgetRing.map p.fSharpInverseImage =
      A.forgetRing.map q.fSharpInverseImage := by
  apply (q.toToposHom.adj.homEquiv _ _).injective
  exact (Stacks.CategoryTheory.homEquiv_conjugate p.toToposHom.adj q.toToposHom.adj s.e.hom
    (A.forgetRing.map p.fSharpInverseImage)).trans (((congrArg (· ≫ s.e.hom.app
      (A.forgetRing.obj A.O)) (forgetFSharp_eq_homEquiv p).symm).trans s.commutes).trans
        (forgetFSharp_eq_homEquiv q))

/-- The conjugate of a vertical composite is the composite of the conjugates. -/
theorem inverseImageIso_trans {p q r : RingedToposHom A B} (s : TwoIso p q) (t : TwoIso q r) :
    (s.trans t).inverseImageIso = t.inverseImageIso ≪≫ s.inverseImageIso := by
  ext1
  exact (conjugateEquiv_symm_comp p.toToposHom.adj q.toToposHom.adj r.toToposHom.adj
    s.e.hom t.e.hom).symm

/-- The conjugate of the inverse is the inverse of the conjugate. -/
theorem inverseImageIso_symm {p q : RingedToposHom A B} (s : TwoIso p q) :
    s.symm.inverseImageIso = s.inverseImageIso.symm := by
  ext1
  show (conjugateEquiv q.toToposHom.adj p.toToposHom.adj).symm s.e.inv = s.inverseImageIso.inv
  rw [← Iso.hom_comp_eq_id]
  show (conjugateEquiv p.toToposHom.adj q.toToposHom.adj).symm s.e.hom ≫
    (conjugateEquiv q.toToposHom.adj p.toToposHom.adj).symm s.e.inv = 𝟙 _
  rw [conjugateEquiv_symm_comp, Iso.inv_hom_id, conjugateEquiv_symm_id]

section Whiskering

variable {C : RingedTopos.{v₃, u₃, w₃}} {D : RingedTopos.{v₄, u₄, w₄}}
  [C.J.HasSheafCompose (forget RingCat.{w₃})]
  [D.J.HasSheafCompose (forget RingCat.{w₄})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w₄} RingCat.{w₄})]

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The conjugate of a 2-isomorphism whiskered on the right by `g` is the conjugate whiskered on
the left by the inverse image of `g`. -/
theorem inverseImageIso_whiskerRight {f₁ f₂ : RingedToposHom A B} (s : TwoIso f₁ f₂)
    (g : RingedToposHom B C) :
    (s.whiskerRight g).inverseImageIso =
      Functor.isoWhiskerLeft g.toToposHom.inverseImage s.inverseImageIso := by
  ext1
  apply (conjugateEquiv (g.comp f₁).toToposHom.adj (g.comp f₂).toToposHom.adj).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine Eq.symm ((conjugateEquiv_whiskerLeft f₁.toToposHom.adj f₂.toToposHom.adj
    g.toToposHom.adj s.inverseImageIso.hom).trans ?_)
  show Functor.whiskerRight ((conjugateEquiv f₁.toToposHom.adj f₂.toToposHom.adj)
    ((conjugateEquiv f₁.toToposHom.adj f₂.toToposHom.adj).symm s.e.hom))
      g.toToposHom.pushforward = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The conjugate of a 2-isomorphism whiskered on the left by `f` is the conjugate whiskered on
the right by the inverse image of `f`. -/
theorem inverseImageIso_whiskerLeft (f : RingedToposHom A B) {g₁ g₂ : RingedToposHom B C}
    (s : TwoIso g₁ g₂) :
    (s.whiskerLeft f).inverseImageIso =
      Functor.isoWhiskerRight s.inverseImageIso f.toToposHom.inverseImage := by
  ext1
  apply (conjugateEquiv (g₁.comp f).toToposHom.adj (g₂.comp f).toToposHom.adj).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  refine Eq.symm ((conjugateEquiv_whiskerRight g₁.toToposHom.adj g₂.toToposHom.adj
    f.toToposHom.adj s.inverseImageIso.hom).trans ?_)
  show Functor.whiskerLeft f.toToposHom.pushforward ((conjugateEquiv g₁.toToposHom.adj
    g₂.toToposHom.adj) ((conjugateEquiv g₁.toToposHom.adj g₂.toToposHom.adj).symm s.e.hom)) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The conjugate of the reassociation 2-isomorphism is the reassociation of the inverse
images. -/
theorem inverseImageIso_associator (f : RingedToposHom A B) (g : RingedToposHom B C)
    (h : RingedToposHom C D) :
    (associator f g h).inverseImageIso =
      Functor.associator h.toToposHom.inverseImage g.toToposHom.inverseImage
        f.toToposHom.inverseImage := by
  ext1
  apply (conjugateEquiv (h.comp (g.comp f)).toToposHom.adj
    ((h.comp g).comp f).toToposHom.adj).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  exact (conjugateEquiv_associator_hom h.toToposHom.adj g.toToposHom.adj f.toToposHom.adj).symm

end Whiskering

end AlgebraicGeometry.RingedToposHom.TwoIso

namespace MorphismOfTopoi

open CartesianMonoidalCategory

universe v' v'' u' u''

variable {E : Type u'} [Category.{v'} E] {D : Type u''} [Category.{v''} D]
  (f : MorphismOfTopoi E D) (G : D) [HasPullbacks D]
  [CartesianMonoidalCategory E] [CartesianMonoidalCategory D]

/-- **The inverse image of a diagonal is a diagonal.** The diagonal `G ⟶ G × G`, as a morphism in
the slice over `G` from its terminal object, is carried by the slice-level morphism of Stacks 04H1
to the diagonal of `f⁻¹G`, read through the comparison `f⁻¹(G × G) ≅ f⁻¹G × f⁻¹G`. -/
theorem over_map_diagonal :
    (f.over G).inverseImage.map
        (Over.homMk (lift (𝟙 G) (𝟙 G)) (lift_snd _ _) : Over.mk (𝟙 G) ⟶ (toOver G).obj G) ≫
      (f.inverseImageCompToOverIso G).inv.app G =
      Over.mkIdTerminal.from _ ≫
        (Over.homMk (lift (𝟙 (f.inverseImage.obj G)) (𝟙 (f.inverseImage.obj G))) (lift_snd _ _) :
          Over.mk (𝟙 (f.inverseImage.obj G)) ⟶ (toOver (f.inverseImage.obj G)).obj
            (f.inverseImage.obj G)) := by
  have := f.preservesFiniteLimits
  let _ : f.inverseImage.Monoidal := Functor.Monoidal.ofChosenFiniteProducts f.inverseImage
  ext1
  simp only [Over.comp_left, Over.mkIdTerminal_from_left, MorphismOfTopoi.inverseImageCompToOverIso,
    NatIso.ofComponents_inv_app]
  have key : ∀ (p : MonoidalCategory.tensorObj G G ⟶ G)
      (q : MonoidalCategory.tensorObj (f.inverseImage.obj G) (f.inverseImage.obj G) ⟶
        f.inverseImage.obj G), lift (𝟙 G) (𝟙 G) ≫ p = 𝟙 G →
      lift (𝟙 (f.inverseImage.obj G)) (𝟙 (f.inverseImage.obj G)) ≫ q = 𝟙 _ →
      (Functor.Monoidal.μIso f.inverseImage G G).inv ≫ q = f.inverseImage.map p →
      f.inverseImage.map (lift (𝟙 G) (𝟙 G)) ≫ (Functor.Monoidal.μIso f.inverseImage G G).inv ≫ q =
        f.inverseImage.map (𝟙 G) ≫
          (lift (𝟙 (f.inverseImage.obj G)) (𝟙 (f.inverseImage.obj G)) ≫ q) := by
    intro p q hp hq hμ
    rw [hμ, ← Functor.map_comp, hp, hq, Category.comp_id]
  refine hom_ext _ _ ?_ ?_
  · refine (Category.assoc _ _ _).trans ((key _ _ (lift_fst _ _) (lift_fst _ _) ?_).trans
      (Category.assoc _ _ _).symm)
    rw [Iso.inv_comp_eq]
    exact (Functor.Monoidal.μ_fst f.inverseImage G G).symm
  · refine (Category.assoc _ _ _).trans ((key _ _ (lift_snd _ _) (lift_snd _ _) ?_).trans
      (Category.assoc _ _ _).symm)
    rw [Iso.inv_comp_eq]
    exact (Functor.Monoidal.μ_snd f.inverseImage G G).symm

end MorphismOfTopoi

namespace AlgebraicGeometry.RingedTopos

open RingedToposHom

universe v u w

variable {X : RingedTopos.{v, u, v}} [EssentiallySmall.{v} X.C] {G : X.Topos}
  {W : RingedTopos.{v, w, v}}

/-- The tautological section `τ : * ⟶ j⁻¹G` of the localization of `X` at `G`, as a morphism in
the localized topos. Its value at `(U, s)` is `s`. -/
noncomputable abbrev tautologicalSection (X : RingedTopos.{v, u, v}) [EssentiallySmall.{v} X.C]
    (G : X.Topos) :
    CategoryTheory.Stacks.Topos.Localized.terminalFiber X.J G ⟶
      (X.localizationMorphism G).toToposHom.inverseImage.obj G :=
  CategoryTheory.Stacks.Topos.Localized.tautologicalSection X.J G

/-- The tautological section's source is terminal. -/
noncomputable abbrev isTerminalTautologicalSource (X : RingedTopos.{v, u, v}) (G : X.Topos) :
    IsTerminal (CategoryTheory.Stacks.Topos.Localized.terminalFiber X.J G) :=
  CategoryTheory.Stacks.Topos.Localized.isTerminalTerminalFiber X.J G

/-- The diagonal `F ⟶ F × F`, as a morphism over `F` from the terminal object `𝟙 F` of the slice
topos to the product `F × F ⟶ F` that the inverse image of the localization sends `F` to. -/
noncomputable def diagonalOver {X : RingedTopos.{v, u, v}} (F : X.Topos) :
    Over.mk (𝟙 F) ⟶ (toOver F).obj F :=
  Over.homMk (CartesianMonoidalCategory.lift (𝟙 F) (𝟙 F))
    (CartesianMonoidalCategory.lift_snd _ _)

/-- **The tautological section is the diagonal.** Under the identification of the localization of
`X` at `F` with the slice topos `Sh(C)/F` (Stacks 04IE), the tautological section `τ : * ⟶ j⁻¹F`
is the diagonal of `F`. -/
theorem localizationEquivalence_map_tautologicalSection (X : RingedTopos.{v, u, v})
    [EssentiallySmall.{v} X.C] (F : X.Topos) :
    (localizationEquivalence X F).functor.map (tautologicalSection X F) ≫
        (localizationInverseImageIso X F).hom.app F =
      Over.mkIdTerminal.from _ ≫ diagonalOver F := by
  let e := (CategoryTheory.Stacks.Topos.Localized.fiberFunctor F.obj X.J F.property).asEquivalence
  let adj := CategoryTheory.Stacks.Topos.Localized.forgetAdjunction F.obj X.J F.property
  have h0 : adj.homEquiv (Over.mk (𝟙 F)) F (𝟙 F) =
      e.toAdjunction.homEquiv (Over.mk (𝟙 F)) _
        (CategoryTheory.Stacks.Topos.Localized.homEquivFiberSheaf F.obj X.J F.property
          (Over.mk (𝟙 F)) F (𝟙 F)) := by
    simp only [adj, CategoryTheory.Stacks.Topos.Localized.forgetAdjunction,
      Adjunction.mkOfHomEquiv_homEquiv, CategoryTheory.Stacks.Topos.Localized.homEquivShriek]
    rfl
  have h1 : adj.unit.app (Over.mk (𝟙 F)) =
      e.unit.app (Over.mk (𝟙 F)) ≫ e.inverse.map (tautologicalSection X F) :=
    (adj.homEquiv_id (Over.mk (𝟙 F))).symm.trans (h0.trans
      ((Adjunction.homEquiv_unit e.toAdjunction (Over.mk (𝟙 F)) _ _).trans
        (congrArg (e.unit.app (Over.mk (𝟙 F)) ≫ e.inverse.map ·)
          ((congrArg ((CategoryTheory.Stacks.Topos.Localized.fiberInclusion X.J F).app
              (Over.mk (𝟙 F)) ≫ ·)
            ((CategoryTheory.Stacks.Topos.Localized.restrictionFunctor F.obj X.J).map_id F)).trans
            (Category.comp_id _)))))
  have h2 : adj.unit.app (Over.mk (𝟙 F)) ≫ (localizationInverseImageIso X F).hom.app F =
      diagonalOver F :=
    Adjunction.unit_rightAdjointUniq_hom_app adj (forgetAdjToOver F) (Over.mk (𝟙 F))
  have h3 : e.unitInv.app (Over.mk (𝟙 F)) ≫ adj.unit.app (Over.mk (𝟙 F)) =
      (localizationEquivalence X F).functor.map (tautologicalSection X F) :=
    (congrArg (e.unitInv.app (Over.mk (𝟙 F)) ≫ ·) h1).trans
      (e.unitIso.inv_hom_id_app_assoc (Over.mk (𝟙 F)) _)
  exact (congrArg (· ≫ (localizationInverseImageIso X F).hom.app F) h3.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (e.unitInv.app (Over.mk (𝟙 F)) ≫ ·) h2).trans
      (congrArg (· ≫ diagonalOver F) (Over.mkIdTerminal.hom_ext _ _))))

/-- The diagonal of `F`, carried back from the slice topos, is the tautological section. This is
`localizationEquivalence_map_tautologicalSection` solved for the diagonal. -/
theorem diagonalOver_comp_localizationInverseImageIso_inv (X : RingedTopos.{v, u, v})
    [EssentiallySmall.{v} X.C] (F : X.Topos) :
    diagonalOver F ≫ (localizationInverseImageIso X F).inv.app F =
      ((isTerminalTautologicalSource X F).isTerminalObj
          (localizationEquivalence X F).functor).from _ ≫
        (localizationEquivalence X F).functor.map (tautologicalSection X F) := by
  let T := ((isTerminalTautologicalSource X F).isTerminalObj
    (localizationEquivalence X F).functor).from (Over.mk (𝟙 F))
  have hT : T ≫ Over.mkIdTerminal.from _ = 𝟙 _ := Over.mkIdTerminal.hom_ext _ _
  calc diagonalOver F ≫ (localizationInverseImageIso X F).inv.app F
      = (T ≫ Over.mkIdTerminal.from _) ≫ diagonalOver F ≫
          (localizationInverseImageIso X F).inv.app F := by rw [hT, Category.id_comp]
    _ = T ≫ (Over.mkIdTerminal.from _ ≫ diagonalOver F) ≫
          (localizationInverseImageIso X F).inv.app F := by simp only [Category.assoc]
    _ = T ≫ ((localizationEquivalence X F).functor.map (tautologicalSection X F) ≫
          (localizationInverseImageIso X F).hom.app F) ≫
          (localizationInverseImageIso X F).inv.app F := by
        rw [localizationEquivalence_map_tautologicalSection]
    _ = T ≫ (localizationEquivalence X F).functor.map (tautologicalSection X F) := by
        simp only [Category.assoc, Iso.hom_inv_id_app]
        exact congrArg (T ≫ ·) (Category.comp_id _)

/-- `MorphismOfTopoi.over_map_diagonal` for the diagonal of a sheaf on a ringed topos. -/
theorem over_map_diagonalOver {X Y : RingedTopos.{v, u, v}} (f : MorphismOfTopoi X.Topos Y.Topos)
    (G : Y.Topos) :
    (f.over G).inverseImage.map (diagonalOver G) ≫ (f.inverseImageCompToOverIso G).inv.app G =
      Over.mkIdTerminal.from _ ≫ diagonalOver (f.inverseImage.obj G) :=
  f.over_map_diagonal G

/-- The tautological section of `G`, carried to the slice topos, pulled back along `f` and
carried back to the localization at `f⁻¹G`, is the tautological section of `f⁻¹G`. -/
theorem over_map_tautologicalSection {X Y : RingedTopos.{v, u, v}}
    [EssentiallySmall.{v} X.C] [EssentiallySmall.{v} Y.C] (f : RingedToposHom X Y)
    (G : Y.Topos) :
    (f.toToposHom.over G).inverseImage.map ((localizationEquivalence Y G).functor.map
          (tautologicalSection Y G) ≫ (localizationInverseImageIso Y G).hom.app G) ≫
        (f.toToposHom.inverseImageCompToOverIso G).inv.app G ≫
          (localizationInverseImageIso X (f.toToposHom.inverseImage.obj G)).inv.app
            (f.toToposHom.inverseImage.obj G) =
      ((f.toToposHom.over G).inverseImage.map (Over.mkIdTerminal.from _) ≫
          Over.mkIdTerminal.from _ ≫
          ((isTerminalTautologicalSource X (f.toToposHom.inverseImage.obj G)).isTerminalObj
            (localizationEquivalence X (f.toToposHom.inverseImage.obj G)).functor).from _) ≫
        (localizationEquivalence X (f.toToposHom.inverseImage.obj G)).functor.map
          (tautologicalSection X (f.toToposHom.inverseImage.obj G)) := by
  rw [localizationEquivalence_map_tautologicalSection, Functor.map_comp, Category.assoc,
    ← Category.assoc ((f.toToposHom.over G).inverseImage.map (diagonalOver G)),
    over_map_diagonalOver f.toToposHom G]
  rw [Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·)
    (diagonalOver_comp_localizationInverseImageIso_inv X (f.toToposHom.inverseImage.obj G)))

/-- **The localized morphism of Stacks 04IF preserves the tautological section.** For a morphism of
ringed topoi `f` and a sheaf `G` on its target, the inverse image of `τ_G` under the localized
morphism `f'` is, through the inverse-image square of Stacks 04IF, the tautological section of the
localization at `f⁻¹G`. -/
theorem localizedToposMorphism_map_tautologicalSection {X Y : RingedTopos.{v, u, v}}
    [EssentiallySmall.{v} X.C] [EssentiallySmall.{v} Y.C] (f : RingedToposHom X Y)
    (G : Y.Topos) :
    (RingedToposHom.localizedToposMorphism f G).inverseImage.map (tautologicalSection Y G) ≫
        (f.inverseImageCompLocalizationIso G).inv.app G =
      (isTerminalTautologicalSource X (f.toToposHom.inverseImage.obj G)).from _ ≫
        tautologicalSection X (f.toToposHom.inverseImage.obj G) := by
  let F' := f.toToposHom.inverseImage.obj G
  let eX := localizationEquivalence X F'
  let c := (f.toToposHom.over G).inverseImage.map (Over.mkIdTerminal.from
      ((localizationEquivalence Y G).functor.obj
        (CategoryTheory.Stacks.Topos.Localized.terminalFiber Y.J G))) ≫
    Over.mkIdTerminal.from _ ≫
    ((isTerminalTautologicalSource X F').isTerminalObj eX.functor).from _
  have h1 : (RingedToposHom.localizedToposMorphism f G).inverseImage.map
        (tautologicalSection Y G) ≫ (f.inverseImageCompLocalizationIso G).inv.app G =
      eX.inverse.map ((f.toToposHom.over G).inverseImage.map
          ((localizationEquivalence Y G).functor.map (tautologicalSection Y G) ≫
            (localizationInverseImageIso Y G).hom.app G) ≫
        (f.toToposHom.inverseImageCompToOverIso G).inv.app G ≫
          (localizationInverseImageIso X F').inv.app F') ≫
        eX.unitIso.inv.app ((X.localizationMorphism F').toToposHom.inverseImage.obj F') := by
    rw [f.inverseImageCompLocalizationIso_inv_app G]
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have h2 : eX.inverse.map (c ≫ eX.functor.map (tautologicalSection X F')) ≫
        eX.unitIso.inv.app ((X.localizationMorphism F').toToposHom.inverseImage.obj F') =
      (eX.inverse.map c ≫ eX.unitIso.inv.app _) ≫ tautologicalSection X F' := by
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    exact congrArg (eX.inverse.map c ≫ ·) (eX.unitIso.inv.naturality (tautologicalSection X F'))
  refine h1.trans ((congrArg (fun x ↦ eX.inverse.map x ≫ eX.unitIso.inv.app
    ((X.localizationMorphism F').toToposHom.inverseImage.obj F'))
    (over_map_tautologicalSection f G)).trans (h2.trans ?_))
  exact congrArg (· ≫ tautologicalSection X F') ((isTerminalTautologicalSource X F').hom_ext _ _)

attribute [local instance] isContinuous_elementPostcomp isCocontinuous_elementPostcomp
  hasPointwiseRightKanExtension_of_essentiallySmall

/-- **The relocalization along `s : F ⟶ K` pulls the tautological section of `K` back to `s`.** The
inverse image along the relocalization morphism of Stacks 04J4 of the tautological section of the
localization at `K` is the tautological section of the localization at `F` followed by `j_F⁻¹(s)`:
both send a section `t` of `F` over `U` to `s(t)`. -/
theorem relocalizationMorphismOfTopoi_map_tautologicalSection (X : RingedTopos.{v, u, v})
    [EssentiallySmall.{v} X.C] {F K : X.Topos} (s : F ⟶ K) :
    (X.relocalizationMorphismOfTopoi s).inverseImage.map (tautologicalSection X K) =
      (isTerminalTautologicalSource X F).from _ ≫ tautologicalSection X F ≫
        (X.localizationMorphism F).toToposHom.inverseImage.map s := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U ↦ ?_))
  ext p
  have h1 : p.val = yonedaEquiv (U.unop.hom ≫ s.hom) := p.app_val
  have h2 : (((isTerminalTautologicalSource X F).from
      ((X.relocalizationMorphismOfTopoi s).inverseImage.obj
        (CategoryTheory.Stacks.Topos.Localized.terminalFiber X.J K))).hom.app U p).val =
      yonedaEquiv U.unop.hom :=
    (((isTerminalTautologicalSource X F).from
      ((X.relocalizationMorphismOfTopoi s).inverseImage.obj
        (CategoryTheory.Stacks.Topos.Localized.terminalFiber X.J K))).hom.app U p).app_val
  show p.val = s.hom.app _ (((isTerminalTautologicalSource X F).from _).hom.app U p).val
  rw [h1, h2]
  exact yonedaEquiv_comp U.unop.hom s.hom

/-- **The morphism `(f_s, f_s♯)` of Stacks 04J8 pulls the tautological section of `G` back to
`s`.** Its inverse image sends the tautological section of the localization at `G` to the
tautological section of the localization at `F` followed by `j_F⁻¹(s)` and the comparison
`j_F⁻¹ f⁻¹ ≅ f_s⁻¹ j_G⁻¹` of the localization square. -/
theorem _root_.AlgebraicGeometry.RingedToposHom.relocalized_map_tautologicalSection
    {X Y : RingedTopos.{v, u, v}} [EssentiallySmall.{v} X.C] [EssentiallySmall.{v} Y.C]
    (f : RingedToposHom X Y) {G : Y.Topos} {F : X.Topos}
    (s : F ⟶ f.toToposHom.inverseImage.obj G) :
    (f.relocalized s).toToposHom.inverseImage.map (tautologicalSection Y G) =
      ((isTerminalTautologicalSource X F).from _ ≫ tautologicalSection X F ≫
          (X.localizationMorphism F).toToposHom.inverseImage.map s) ≫
        (X.relocalizationMorphismOfTopoi s).inverseImage.map
          ((f.inverseImageCompLocalizationIso G).hom.app G) := by
  have h1 : (RingedToposHom.localizedToposMorphism f G).inverseImage.map
        (tautologicalSection Y G) =
      ((isTerminalTautologicalSource X (f.toToposHom.inverseImage.obj G)).from _ ≫
        tautologicalSection X (f.toToposHom.inverseImage.obj G)) ≫
        (f.inverseImageCompLocalizationIso G).hom.app G := by
    rw [← localizedToposMorphism_map_tautologicalSection, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  show (X.relocalizationMorphismOfTopoi s).inverseImage.map
    ((RingedToposHom.localizedToposMorphism f G).inverseImage.map (tautologicalSection Y G)) = _
  rw [h1, Functor.map_comp, Functor.map_comp, relocalizationMorphismOfTopoi_map_tautologicalSection]
  exact congrArg (· ≫ _) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((isTerminalTautologicalSource X F).hom_ext _ _)))

variable (a b : AlgebraicGeometry.RingedToposHom W (X.localizedRingedTopos G))
  (ε : TwoIso (A := W) (B := X)
    (comp (X := W) (Y := X.localizedRingedTopos G) (Z := X) (X.localizationMorphism G) a)
    (comp (X := W) (Y := X.localizedRingedTopos G) (Z := X) (X.localizationMorphism G) b))

/-- The condition under which a 2-isomorphism `ε : j_G ∘ a ≅ j_G ∘ b` comes from a 2-isomorphism
`a ≅ b`: its conjugate carries `b⁻¹(τ)` to `a⁻¹(τ)`, for `τ` the tautological section. -/
def CarriesTautologicalSection : Prop :=
  b.toToposHom.inverseImage.map (tautologicalSection X G) ≫ ε.inverseImageIso.hom.app G =
    ((isTerminalTautologicalSource X G).isTerminalObj a.toToposHom.inverseImage).from _ ≫
      a.toToposHom.inverseImage.map (tautologicalSection X G)

variable {a b ε}

/-- The isomorphism of inverse images `b⁻¹ ≅ a⁻¹` extending the conjugate of `ε`. -/
noncomputable def localizationLiftInverseImageIso (hε : CarriesTautologicalSection a b ε) :
    b.toToposHom.inverseImage ≅ a.toToposHom.inverseImage :=
  haveI := b.toToposHom.preservesFiniteLimits
  haveI := a.toToposHom.preservesFiniteLimits
  CategoryTheory.Stacks.Topos.Localized.extendIso X.J G b.toToposHom.inverseImage
    a.toToposHom.inverseImage ε.inverseImageIso hε

/-- At the underlying sheaf of sets of the structure sheaf of the localization,
`localizationLiftInverseImageIso` is the conjugate of `ε` at the structure sheaf of `X`. -/
theorem localizationLiftInverseImageIso_hom_app_forget (hε : CarriesTautologicalSection a b ε) :
    (localizationLiftInverseImageIso hε).hom.app
        ((X.localizedRingedTopos G).forgetRing.obj (X.localizedRingedTopos G).O) =
      ε.inverseImageIso.hom.app (X.forgetRing.obj X.O) :=
  have := b.toToposHom.preservesFiniteLimits
  have := a.toToposHom.preservesFiniteLimits
  CategoryTheory.Stacks.Topos.Localized.extendIso_hom_app_restriction X.J G
    b.toToposHom.inverseImage a.toToposHom.inverseImage ε.inverseImageIso hε (X.forgetRing.obj X.O)

/-- The structure map of a morphism into a localization, on underlying sheaves of sets and in
inverse-image form, is the structure map of its composite with the localization morphism. -/
theorem forgetRing_fSharpInverseImage_comp_localizationMorphism
    (c : RingedToposHom W (X.localizedRingedTopos G)) :
    W.forgetRing.map (comp (X := W) (Y := X.localizedRingedTopos G) (Z := X)
      (X.localizationMorphism G) c).fSharpInverseImage =
      W.forgetRing.map c.fSharpInverseImage :=
  (comp_fSharpInverseImage_forget (X := W) (Y := X.localizedRingedTopos G) (Z := X)
    (X.localizationMorphism G) c).trans
    ((congrArg (· ≫ W.forgetRing.map c.fSharpInverseImage)
      ((congrArg c.toToposHom.inverseImage.map
        (forgetRing_localizationMorphism_fSharpInverseImage X G)).trans
          (c.toToposHom.inverseImage.map_id _))).trans (Category.id_comp _))

/-- A 2-isomorphism of ringed topoi `j_G ∘ c ≅ p` for a morphism `c` into a localization, read off
an isomorphism of inverse images compatible with the structure map of `c`: the structure map of
the localization morphism is the identity on underlying sheaves of sets. -/
noncomputable def compLocalizationMorphismTwoIsoOfInverseImageIso
    (c : RingedToposHom W (X.localizedRingedTopos G)) (p : RingedToposHom W X)
    (α : p.toToposHom.inverseImage ≅
      (X.localizationMorphism G).toToposHom.inverseImage ⋙ c.toToposHom.inverseImage)
    (h : α.hom.app (X.forgetRing.obj X.O) ≫ W.forgetRing.map c.fSharpInverseImage =
      W.forgetRing.map p.fSharpInverseImage) :
    TwoIso (A := W) (B := X)
      (comp (X := W) (Y := X.localizedRingedTopos G) (Z := X) (X.localizationMorphism G) c) p :=
  TwoIso.ofInverseImageIso (A := W) (B := X)
    (p := comp (X := W) (Y := X.localizedRingedTopos G) (Z := X) (X.localizationMorphism G) c)
    (q := p) α
    ((congrArg (α.hom.app (X.forgetRing.obj X.O) ≫ ·)
      (forgetRing_fSharpInverseImage_comp_localizationMorphism c)).trans h)

/-- The conjugate of `compLocalizationMorphismTwoIsoOfInverseImageIso` is the given isomorphism. -/
theorem compLocalizationMorphismTwoIsoOfInverseImageIso_inverseImageIso
    (c : RingedToposHom W (X.localizedRingedTopos G)) (p : RingedToposHom W X)
    (α : p.toToposHom.inverseImage ≅
      (X.localizationMorphism G).toToposHom.inverseImage ⋙ c.toToposHom.inverseImage)
    (h : α.hom.app (X.forgetRing.obj X.O) ≫ W.forgetRing.map c.fSharpInverseImage =
      W.forgetRing.map p.fSharpInverseImage) :
    (compLocalizationMorphismTwoIsoOfInverseImageIso c p α h).inverseImageIso = α :=
  (conjugateIsoEquiv (comp (X := W) (Y := X.localizedRingedTopos G) (Z := X)
    (X.localizationMorphism G) c).toToposHom.adj p.toToposHom.adj).symm_apply_apply α

/-- **Morphisms into a localization are determined by their composite with the localization
morphism and the pulled back tautological section.** A 2-isomorphism `ε : j_G ∘ a ≅ j_G ∘ b`
carrying `b⁻¹(τ)` to `a⁻¹(τ)` comes from a 2-isomorphism `a ≅ b`. -/
noncomputable def localizationTwoIso (hε : CarriesTautologicalSection a b ε) :
    TwoIso (A := W) (B := X.localizedRingedTopos G) a b :=
  TwoIso.ofInverseImageIso (A := W) (B := X.localizedRingedTopos G) (p := a) (q := b)
    (localizationLiftInverseImageIso hε) (by
    refine (congrArg (· ≫ W.forgetRing.map a.fSharpInverseImage)
      (localizationLiftInverseImageIso_hom_app_forget hε)).trans ?_
    refine (congrArg (ε.inverseImageIso.hom.app (X.forgetRing.obj X.O) ≫ ·)
      (forgetRing_fSharpInverseImage_comp_localizationMorphism a).symm).trans ?_
    exact (RingedToposHom.TwoIso.inverseImageIso_fSharpInverseImage ε).trans
      (forgetRing_fSharpInverseImage_comp_localizationMorphism b))

end AlgebraicGeometry.RingedTopos

end
