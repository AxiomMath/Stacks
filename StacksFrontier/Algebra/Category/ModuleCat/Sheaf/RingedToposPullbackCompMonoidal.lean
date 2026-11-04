module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardCompMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardIsoSections
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCompTransfer
public import StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence
public import StacksFrontier.CategoryTheory.Monoidal.ConjugateOplax
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex

/-!
# The pullback along a composite of morphisms of ringed topoi is monoidal

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and `g : (Sh(D), O_D) ⟶ (Sh(E), O_E)` be morphisms of
ringed topoi and `c : (g ∘ f)^* ≅ g^* ⋙ f^*` the compositor of pullbacks. The comparison
`δ_h : h^*(A ⊗ B) ≅ h^*A ⊗ h^*B` of pullback with tensor product is compatible with `c`:

`f^*(δ_g) ≫ δ_f ≫ (c⁻¹ ⊗ c⁻¹) = c⁻¹ ≫ δ_{g ∘ f}`.

## Main results

* `conjugateEquiv_pullbackModulesCompIso_hom_eq_pushforwardModulesCompIsoToModulesHom`:
  the conjugate of the compositor under the pullback-pushforward adjunctions is the comparison
  of direct images `Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso`.
* `AlgebraicGeometry.RingedToposHom.pullbackTensorIso_hom_app_comp`: the compatibility of the
  tensor comparison of pullbacks with the compositor.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace Stacks.CategoryTheory

variable {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]

/-- The conjugate of a transformation into a composite of left adjoints, after the right adjoints
of the three adjunctions are changed along isomorphisms. -/
theorem conjugateEquiv_comp_ofNatIsoRight {F : C₀ ⥤ C₁} {G G' : C₁ ⥤ C₀} {H : C₁ ⥤ C₂}
    {I I' : C₂ ⥤ C₁} {L : C₀ ⥤ C₂} {R R' : C₂ ⥤ C₀} (a : F ⊣ G) (b : H ⊣ I) (c : L ⊣ R)
    (j : G ≅ G') (i : I ≅ I') (k : R ≅ R') (α : L ⟶ F ⋙ H) :
    conjugateEquiv ((a.ofNatIsoRight j).comp (b.ofNatIsoRight i)) (c.ofNatIsoRight k) α =
      (Functor.isoWhiskerLeft I' j).inv ≫ (Functor.isoWhiskerRight i G).inv ≫
        conjugateEquiv (a.comp b) c α ≫ k.hom := by
  rw [Adjunction.comp_ofNatIsoRight_left, Adjunction.comp_ofNatIsoRight_right,
    conjugateEquiv_ofNatIsoRight_right, conjugateEquiv_ofNatIsoRight_left,
    conjugateEquiv_ofNatIsoRight_left]
  simp only [Category.assoc]

end Stacks.CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

universe w v u v' u' v'' u''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}} {Z : RingedTopos.{v'', u'', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse identification of the two direct images of sheaves of modules is the identity on
underlying sheaves of sets. -/
lemma moduleSheafFunctor_map_toModulesPushforwardIso_inv_app_eq_id
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
      (f.toModulesPushforwardIso.inv.app M) =
      𝟙 (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M)) := rfl

/-- The comparison of direct images of sheaves of modules along the composite `g ∘ f`, attached
to the identification of the underlying direct images on the nose. -/
abbrev pushforwardModulesCompIsoToModulesHom :
    Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom ⋙
        Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom ≅
      Stacks.Sheaves.RingedToposModules.pushforwardModules (g.comp f).toModulesHom :=
  Stacks.Sheaves.RingedToposModules.pushforwardModulesCompIso f.toModulesHom g.toModulesHom
    (g.comp f).toModulesHom (Iso.refl _)
    ((Category.comp_id _).trans (comp_fSharpRing_underlying g f).symm)

/-- The underlying sheaf of the double direct image of a sheaf of modules. -/
private abbrev pushforwardCompObj
    (M : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :=
  g.toToposHom.pushforward.obj
    (f.toToposHom.pushforward.obj
      (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M))

omit [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The conjugate of the compositor of pullbacks under the pullback-pushforward adjunctions is
the comparison of direct images along the composite. -/
theorem conjugateEquiv_pullbackModulesCompIso_hom_eq_pushforwardModulesCompIsoToModulesHom :
    conjugateEquiv
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom))
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules (g.comp f).toModulesHom)
        (pullbackModulesCompIso f g).hom =
      (pushforwardModulesCompIsoToModulesHom f g).hom := by
  have h := (conjugateEquiv_pullbackModulesCompIso_hom f g).symm.trans
    (Stacks.CategoryTheory.conjugateEquiv_comp_ofNatIsoRight
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom)
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom)
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules (g.comp f).toModulesHom)
      g.toModulesPushforwardIso f.toModulesPushforwardIso (g.comp f).toModulesPushforwardIso
      (pullbackModulesCompIso f g).hom)
  rw [← cancel_mono (g.comp f).toModulesPushforwardIso.hom,
    ← cancel_epi (Functor.isoWhiskerRight f.toModulesPushforwardIso
      (Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom)).inv,
    ← cancel_epi (Functor.isoWhiskerLeft (pushforwardModules f) g.toModulesPushforwardIso).inv,
    ← h]
  refine NatTrans.ext (funext fun M ↦ ?_)
  refine Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor ?_
  have hP : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
      ((pushforwardModulesCompIso f g).inv.app M) = 𝟙 (pushforwardCompObj f g M) := rfl
  have hW : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
      ((Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom).map
        (f.toModulesPushforwardIso.inv.app M)) = 𝟙 (pushforwardCompObj f g M) := by
    rw [Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_pushforwardModules_map,
      moduleSheafFunctor_map_toModulesPushforwardIso_inv_app_eq_id]
    exact CategoryTheory.Functor.map_id g.toToposHom.pushforward
      (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) M))
  have hQ : (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
      ((pushforwardModulesCompIsoToModulesHom f g).hom.app M) = 𝟙 (pushforwardCompObj f g M) := rfl
  simp only [NatTrans.comp_app, Functor.map_comp, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app, hP, hW, hQ,
    moduleSheafFunctor_map_toModulesPushforwardIso_inv_app_eq_id,
    moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id]
  exact Sheaf.hom_ext_sections fun _ _ ↦ rfl

section Monoidal

/-- Replacing the last factor of a composite of four morphisms. -/
private lemma comp₃_congr {C : Type*} [Category C] {P Q R S T : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {t t' : S ⟶ T} (h : t = t') :
    a ≫ b ≫ c ≫ t = a ≫ b ≫ c ≫ t' := by
  rw [h]

/-- Moving an isomorphism across an identity of composites. -/
private lemma eq_comp_of_comp_eq_comp_of_hom_inv {C : Type*} [Category C] {P Q R S T : C}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {d : P ⟶ T} {e : T ⟶ S} {e' : S ⟶ T}
    (h : a ≫ b ≫ c = d ≫ e) (he : e ≫ e' = 𝟙 _) : d = a ≫ b ≫ c ≫ e' := by
  rw [reassoc_of% h, he, Category.comp_id]

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
  Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal

instance isMonoidal_conjugateEquiv_pullbackModulesCompIso_hom :
    NatTrans.IsMonoidal (conjugateEquiv
        ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
          (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom))
        (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules (g.comp f).toModulesHom)
        (pullbackModulesCompIso f g).hom) := by
  rw [conjugateEquiv_pullbackModulesCompIso_hom_eq_pushforwardModulesCompIsoToModulesHom]
  exact Stacks.Sheaves.RingedToposModules.isMonoidal_pushforwardModulesCompIso_hom _ _ _ _ _

/-- The tensor comparison of pullbacks is compatible with the compositor, at the monoidal
spelling: the compositor `(g ∘ f)^* ⟶ g^* ⋙ f^*` carries the comparison for `g ∘ f` to the composite
comparison `f^*(δ_g) ≫ δ_f`. -/
theorem pullbackModulesCompIso_hom_app_tensor_comp_δ
    (A B : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (pullbackModulesCompIso f g).hom.app (A ⊗ B) ≫
        f.toModulesHom.pullbackModules.map
          (Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison g.toModulesHom A B) ≫
        Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison f.toModulesHom
          (g.toModulesHom.pullbackModules.obj A) (g.toModulesHom.pullbackModules.obj B) =
      Stacks.SheafOfModules.RingedToposPullback.pullbackTensorComparison (g.comp f).toModulesHom
          A B ≫
        ((pullbackModulesCompIso f g).hom.app A ⊗ₘ (pullbackModulesCompIso f g).hom.app B) := by
  have h := Adjunction.app_tensor_comp_δ_of_isMonoidal_conjugateEquiv
    ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).comp
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom))
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules (g.comp f).toModulesHom)
    (pullbackModulesCompIso f g).hom A B
  rwa [Functor.OplaxMonoidal.comp_δ] at h

/-- The tensor comparison of pullbacks is compatible with the compositor: the comparison for
`g ∘ f` is the compositor, then `f^*` of the comparison for `g`, then the comparison for `f`,
then the inverse compositor in each tensor factor. -/
theorem pullbackTensorIso_hom_app_comp
    (A B : _root_.SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    (Stacks.SheafOfModules.pullbackTensorIso (g.comp f).toModulesHom).hom.app (A, B) =
      (pullbackModulesCompIso f g).hom.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)).obj (A, B)) ≫
        f.toModulesHom.pullbackModules.map
          ((Stacks.SheafOfModules.pullbackTensorIso g.toModulesHom).hom.app (A, B)) ≫
        (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).hom.app
          (g.toModulesHom.pullbackModules.obj A, g.toModulesHom.pullbackModules.obj B) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            ((pullbackModulesCompIso f g).inv.app A)).app
            (f.toModulesHom.pullbackModules.obj (g.toModulesHom.pullbackModules.obj B)) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            ((g.comp f).toModulesHom.pullbackModules.obj A)).map
            ((pullbackModulesCompIso f g).inv.app B) := by
  have h := pullbackModulesCompIso_hom_app_tensor_comp_δ f g A B
  have hinv : ((pullbackModulesCompIso f g).hom.app A ⊗ₘ (pullbackModulesCompIso f g).hom.app B) ≫
      ((pullbackModulesCompIso f g).inv.app A ⊗ₘ (pullbackModulesCompIso f g).inv.app B) = 𝟙 _ := by
    rw [tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app, tensorHom_id,
      id_whiskerRight]
  exact (eq_comp_of_comp_eq_comp_of_hom_inv h hinv).trans (comp₃_congr
    (Stacks.SheafOfModules.Strict.tensorHom_eq_tensorSheafBifunctor_map X.O _ _))

end Monoidal

end AlgebraicGeometry.RingedToposHom

end
