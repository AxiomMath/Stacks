module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# Pulling back étale cohomology classes along a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes, `F` an abelian sheaf on the small étale site of `Y`,
`G` an abelian sheaf on the small étale site of `X`, and `φ : f⁻¹F ⟶ G` a map of sheaves. Then
there is a canonical map

`H^p(Y, F) ⟶ H^p(X, f⁻¹F) ⟶ H^p(X, G)`

on étale cohomology. Étale cohomology is Mathlib's `CategoryTheory.Sheaf.H`, the `Ext`-group out
of the constant sheaf `ℤ`; the first arrow is the action of the exact functor `f⁻¹` on `Ext`,
followed by the identification of `f⁻¹` of the constant sheaf with the constant sheaf, and the
second is composition with `φ`.

This file constructs that map and proves the two compatibilities that make it the transition map
of a system of cohomology groups: pulling back along a composite is the composite of the pull
backs, and pulling back along an identity is the identity.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleConstantAdj`: the constant sheaf functor is left adjoint to
  sections over the final object `X ⟶ X` of the small étale site.
* `Stacks.EtaleCohomology.smallEtalePullbackAbConstantIso`: `f⁻¹` carries the constant sheaf to
  the constant sheaf, by the comparison of left adjoints induced by the canonical identification
  of the global sections of `f_*G` with those of `G`.
* `Stacks.EtaleCohomology.etaleCohomologyPullback`: the map `H^p(Y, F) ⟶ H^p(X, G)` attached to
  `f` and `φ : f⁻¹F ⟶ G`.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbConstantIso_comp`: the identifications of the
  inverse images of the constant sheaf are compatible with the comparison
  `(fg)⁻¹ ≅ f⁻¹ ∘ g⁻¹` of `Stacks.EtaleCohomology.smallEtalePullbackAbComp'`.
* `Stacks.EtaleCohomology.etaleCohomologyPullback_comp`: pulling back along `f` and then along
  `g` is pulling back along the composite, with the composite map of sheaves.

## Implementation notes

The identification `f⁻¹ℤ ≅ ℤ` is `CategoryTheory.Adjunction.leftAdjointCompIso` of the three
adjunctions `ℤ ⊣ Γ(Y, -)`, `f⁻¹ ⊣ f_*` and `ℤ ⊣ Γ(X, -)` at the isomorphism
`Γ(Y, f_* -) ≅ Γ(X, -)`, which restricts sections along the unique isomorphism between the final
object `X ⟶ X` and the base change of the final object of the small étale site of `Y`. With this
choice the compatibility with composition is an instance of
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`: the corresponding compatibility of the
right adjoints says that two restrictions of sections along morphisms into a final object agree,
which holds because any two morphisms into a final object are equal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Abelian sheaves on a small étale site have all `Ext`-groups at the coefficient universe: the
category is Grothendieck abelian, the site being essentially small. -/
instance smallEtaleAbSheaf_hasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (smallEtaleTopology X) Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.Etale := inferInstance
  have : IsGrothendieckAbelian.{u + 1} (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall.{u + 1} (smallEtaleTopology X) Ab.{u + 1}
  exact hasExt_of_enoughInjectives _

/-! ### The final object and the constant sheaf -/

section Final

variable (X : Scheme.{u})

/-- The constant sheaf functor is left adjoint to sections over the final object `X ⟶ X` of the
small étale site. -/
def smallEtaleConstantAdj :
    constantSheaf (smallEtaleTopology X) Ab.{u + 1} ⊣
      (sheafSections (smallEtaleTopology X) Ab.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 X))) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  constantSheafAdj _ _ (MorphismProperty.Over.mkIdTerminal _ _)

end Final

/-! ### The inverse image of the constant sheaf -/

section Constant

variable {X Y Z : Scheme.{u}}

/-- Base change carries the final object `Y ⟶ Y` to a final object. -/
def smallEtaleBaseChangeFinalIsTerminal (f : X ⟶ Y) :
    IsTerminal ((smallEtaleBaseChange f).obj (Scheme.Etale.mk (𝟙 Y))) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  (MorphismProperty.Over.mkIdTerminal _ _).isTerminalObj (smallEtaleBaseChange f) _

/-- The global sections of a direct image are the global sections: restriction along the unique
isomorphism between the final object of `X.Etale` and the base change of the final object of
`Y.Etale`. -/
def smallEtalePushforwardAbΓIso (f : X ⟶ Y) :
    smallEtalePushforwardAb f ⋙
        (sheafSections (smallEtaleTopology Y) Ab.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 Y))) ≅
      (sheafSections (smallEtaleTopology X) Ab.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 X))) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  (sheafSections (smallEtaleTopology X) Ab.{u + 1}).mapIso
    ((show IsTerminal (Scheme.Etale.mk (𝟙 X)) from
      MorphismProperty.Over.mkIdTerminal _ _).uniqueUpToIso
        (smallEtaleBaseChangeFinalIsTerminal f)).op

/-- The value of `smallEtalePushforwardAbΓIso` is restriction along a morphism from the final
object. -/
lemma smallEtalePushforwardAbΓIso_hom_app (f : X ⟶ Y) (G : Sheaf (smallEtaleTopology X) Ab) :
    (smallEtalePushforwardAbΓIso f).hom.app G =
      G.obj.map ((smallEtaleBaseChangeFinalIsTerminal f).from (Scheme.Etale.mk (𝟙 X))).op := by
  dsimp [smallEtalePushforwardAbΓIso]
  congr 2

/-- **The inverse image of the constant sheaf is the constant sheaf**, as a natural isomorphism
of functors of the coefficient group. -/
def smallEtalePullbackAbConstantIso (f : X ⟶ Y) :
    constantSheaf (smallEtaleTopology Y) Ab.{u + 1} ⋙ smallEtalePullbackAb f ≅
      constantSheaf (smallEtaleTopology X) Ab.{u + 1} :=
  Adjunction.leftAdjointCompIso (smallEtaleConstantAdj Y) (smallEtaleAdjunctionAb f)
    (smallEtaleConstantAdj X) (smallEtalePushforwardAbΓIso f)

/-- The global sections of the composite of two direct images are compatible with the
identifications `Γ(Y, f_* -) ≅ Γ(X, -)`: both sides restrict sections along a morphism from the
final object to a final object. -/
lemma smallEtalePushforwardAbΓIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    Functor.isoWhiskerLeft (smallEtalePushforwardAb f) (smallEtalePushforwardAbΓIso g) ≪≫
        smallEtalePushforwardAbΓIso f =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtalePushforwardAbComp' f g fg hfg)
          ((sheafSections (smallEtaleTopology Z) Ab.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 Z)))) ≪≫
          smallEtalePushforwardAbΓIso fg := by
  refine Iso.ext (NatTrans.ext (funext fun G => ?_))
  have hT : IsTerminal ((smallEtaleBaseChange f).obj ((smallEtaleBaseChange g).obj
      (Scheme.Etale.mk (𝟙 Z)))) :=
    (smallEtaleBaseChangeFinalIsTerminal g).isTerminalObj (smallEtaleBaseChange f) _
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, smallEtalePushforwardAbΓIso_hom_app,
    Category.id_comp]
  change G.obj.map _ ≫ G.obj.map _ =
    ((smallEtalePushforwardAbComp' f g fg hfg).hom.app G).hom.app _ ≫ G.obj.map _
  rw [smallEtalePushforwardAbComp'_hom_app_hom_app]
  refine (G.obj.map_comp _ _).symm.trans (Eq.trans ?_ (G.obj.map_comp _ _))
  congr 1
  exact Quiver.Hom.unop_inj (hT.hom_ext _ _)

/-- **The identifications of the inverse images of the constant sheaf are compatible with
composition**: along `fg = f ≫ g`, the identification `(fg)⁻¹ℤ ≅ ℤ` is the identification
`f⁻¹(g⁻¹ℤ) ≅ f⁻¹ℤ ≅ ℤ`, read through the comparison
`Stacks.EtaleCohomology.smallEtalePullbackAbComp'`. -/
lemma smallEtalePullbackAbConstantIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    Functor.isoWhiskerLeft _ (smallEtalePullbackAbComp' f g fg hfg) ≪≫
        smallEtalePullbackAbConstantIso fg =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtalePullbackAbConstantIso g) (smallEtalePullbackAb f) ≪≫
          smallEtalePullbackAbConstantIso f := by
  rw [smallEtalePullbackAbComp'_eq_leftAdjointCompIso]
  exact Adjunction.leftAdjointCompIso_assoc (smallEtaleConstantAdj Z) (smallEtaleAdjunctionAb g)
    (smallEtaleAdjunctionAb f) (smallEtaleConstantAdj Y) (smallEtaleAdjunctionAb fg)
    (smallEtaleConstantAdj X) (smallEtalePushforwardAbΓIso g)
    (smallEtalePushforwardAbComp' f g fg hfg) (smallEtalePushforwardAbΓIso fg)
    (smallEtalePushforwardAbΓIso f) (smallEtalePushforwardAbΓIso_comp f g fg hfg)

/-- The component form of `smallEtalePullbackAbConstantIso_comp`, on the inverses. -/
lemma smallEtalePullbackAbConstantIso_comp_inv_app (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (A : Ab.{u + 1}) :
    (smallEtalePullbackAbConstantIso fg).inv.app A =
      (smallEtalePullbackAbConstantIso f).inv.app A ≫
        (smallEtalePullbackAb f).map ((smallEtalePullbackAbConstantIso g).inv.app A) ≫
          (smallEtalePullbackAbComp' f g fg hfg).hom.app _ := by
  have h := congrArg (fun e => e.inv.app A) (smallEtalePullbackAbConstantIso_comp f g fg hfg)
  simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Iso.symm_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id] at h
  rw [← Category.assoc, ← h]
  simp

end Constant

/-! ### The pull back map on étale cohomology -/

section Pullback

variable {X Y Z : Scheme.{u}}

/-- **The pull back map on étale cohomology.** For `f : X ⟶ Y` and a map of sheaves
`φ : f⁻¹F ⟶ G`, the map `H^p(Y, F) ⟶ H^p(X, G)`: apply the exact functor `f⁻¹` to an `Ext`
class out of `ℤ`, identify `f⁻¹ℤ` with `ℤ`, and compose with `φ`. -/
def etaleCohomologyPullback (f : X ⟶ Y) {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : (smallEtalePullbackAb f).obj F ⟶ G)
    (p : ℕ) : Sheaf.H.{u + 1} F p →+ Sheaf.H.{u + 1} G p where
  toFun x := (Ext.mk₀ ((smallEtalePullbackAbConstantIso f).inv.app
      (AddCommGrpCat.of (ULift ℤ)))).comp
    ((x.mapExactFunctor (smallEtalePullbackAb f)).comp (Ext.mk₀ φ) (add_zero p)) (zero_add p)
  map_zero' := by simp
  map_add' x y := by simp [Ext.comp_add, Ext.add_comp]

/-- The value of `etaleCohomologyPullback f φ p` on a class `x`: the image of `x` under `f⁻¹`,
composed with `Ext.mk₀ φ` and preceded by the inverse of `f⁻¹ℤ ≅ ℤ`. -/
lemma etaleCohomologyPullback_apply (f : X ⟶ Y) {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : (smallEtalePullbackAb f).obj F ⟶ G)
    (p : ℕ) (x : Sheaf.H.{u + 1} F p) :
    etaleCohomologyPullback f φ p x =
      (Ext.mk₀ ((smallEtalePullbackAbConstantIso f).inv.app
        (AddCommGrpCat.of (ULift ℤ)))).comp
        ((x.mapExactFunctor (smallEtalePullbackAb f)).comp (Ext.mk₀ φ) (add_zero p))
        (zero_add p) := rfl

/-- Pulling back is natural in the target sheaf. -/
lemma etaleCohomologyPullback_comp_mk₀ (f : X ⟶ Y)
    {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {G G' : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb f).obj F ⟶ G) (ψ : G ⟶ G') (p : ℕ) (x : Sheaf.H.{u + 1} F p) :
    (etaleCohomologyPullback f φ p x).comp (Ext.mk₀ ψ) (add_zero p) =
      etaleCohomologyPullback f (φ ≫ ψ) p x := by
  simp only [etaleCohomologyPullback_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]

/-- **Pulling back along a composite.** Pulling back along `f` with `φ : f⁻¹F ⟶ G` and then
along `g` with `ψ : g⁻¹G ⟶ K` is pulling back along `gf = g ≫ f` with the composite
`(gf)⁻¹F ≅ g⁻¹f⁻¹F ⟶ g⁻¹G ⟶ K`. -/
lemma etaleCohomologyPullback_comp (g : X ⟶ Y) (f : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = g ≫ f)
    {F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}} {G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    {K : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : (smallEtalePullbackAb f).obj F ⟶ G)
    (ψ : (smallEtalePullbackAb g).obj G ⟶ K) (p : ℕ) (x : Sheaf.H.{u + 1} F p) :
    etaleCohomologyPullback g ψ p (etaleCohomologyPullback f φ p x) =
      etaleCohomologyPullback gf ((smallEtalePullbackAbComp' g f gf hgf).inv.app F ≫
        (smallEtalePullbackAb g).map φ ≫ ψ) p x := by
  have hcomp := Stacks.ExtFunctorial.mapExactFunctor_comp_functor (smallEtalePullbackAb f)
    (smallEtalePullbackAb g)
    ((constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) p x
  have hnat := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor
    (smallEtalePullbackAbComp' g f gf hgf).hom
    ((constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) p x
  have hc := smallEtalePullbackAbConstantIso_comp_inv_app g f gf hgf (AddCommGrpCat.of (ULift ℤ))
  have hx : x.mapExactFunctor (smallEtalePullbackAb f ⋙ smallEtalePullbackAb g) =
      (Ext.mk₀ ((smallEtalePullbackAbComp' g f gf hgf).hom.app
        ((constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))))).comp
        ((x.mapExactFunctor (smallEtalePullbackAb gf)).comp
          (Ext.mk₀ ((smallEtalePullbackAbComp' g f gf hgf).inv.app F)) (add_zero p))
        (zero_add p) := by
    rw [← Ext.comp_assoc_of_third_deg_zero, hnat, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app, Ext.comp_mk₀_id]
  simp only [etaleCohomologyPullback_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rw [hcomp, hx, hc]
  simp only [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀_assoc, Category.assoc]

/-- **Pulling back in degree zero.** On a morphism `x : ℤ ⟶ F` read as a class of degree zero,
pulling back is `f⁻¹ℤ ≅ ℤ` followed by `f⁻¹x` and `φ`. -/
lemma etaleCohomologyPullback_mk₀ (f : X ⟶ Y) {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : (smallEtalePullbackAb f).obj F ⟶ G)
    (x : (constantSheaf (smallEtaleTopology Y) Ab.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)) ⟶ F) :
    etaleCohomologyPullback f φ 0 (Ext.mk₀ x) =
      Ext.mk₀ ((smallEtalePullbackAbConstantIso f).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
        (smallEtalePullbackAb f).map x ≫ φ) := by
  rw [etaleCohomologyPullback_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]

/-- **Pulling back is natural in the source sheaf.** -/
lemma etaleCohomologyPullback_mk₀_comp (f : X ⟶ Y) {F F' : Sheaf (smallEtaleTopology Y) Ab.{u + 1}}
    {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (g : F' ⟶ F)
    (φ : (smallEtalePullbackAb f).obj F ⟶ G) (p : ℕ) (x : Sheaf.H.{u + 1} F' p) :
    etaleCohomologyPullback f φ p (x.comp (Ext.mk₀ g) (add_zero p)) =
      etaleCohomologyPullback f ((smallEtalePullbackAb f).map g ≫ φ) p x := by
  simp only [etaleCohomologyPullback_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

/-- **Pulling back commutes with the connecting maps.** Let `S` be a short exact sequence of
abelian sheaves on `Y`, `S'` one on `X`, and `ψ : f⁻¹S ⟶ S'` a morphism of short complexes. Then
pulling back along `f` with the components of `ψ` carries the connecting map of `S` to the
connecting map of `S'`. -/
lemma etaleCohomologyPullback_comp_extClass (f : X ⟶ Y)
    {S : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1})} (hS : S.ShortExact)
    {S' : ShortComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1})} (hS' : S'.ShortExact)
    (ψ₁ : (smallEtalePullbackAb f).obj S.X₁ ⟶ S'.X₁)
    (ψ₂ : (smallEtalePullbackAb f).obj S.X₂ ⟶ S'.X₂)
    (ψ₃ : (smallEtalePullbackAb f).obj S.X₃ ⟶ S'.X₃)
    (h₁₂ : (smallEtalePullbackAb f).map S.f ≫ ψ₂ = ψ₁ ≫ S'.f)
    (h₂₃ : (smallEtalePullbackAb f).map S.g ≫ ψ₃ = ψ₂ ≫ S'.g) (p : ℕ)
    (x : Sheaf.H.{u + 1} S.X₃ p) :
    (etaleCohomologyPullback f ψ₃ p x).comp hS'.extClass rfl =
      etaleCohomologyPullback f ψ₁ (p + 1) (x.comp hS.extClass rfl) := by
  have hS₁ : (S.map (smallEtalePullbackAb f)).ShortExact := hS.map_of_exact _
  have hn : hS₁.extClass.comp (Ext.mk₀ ψ₁) (add_zero 1) =
      (Ext.mk₀ ψ₃).comp hS'.extClass (zero_add 1) := hS₁.extClass_naturality hS'
    { τ₁ := ψ₁, τ₂ := ψ₂, τ₃ := ψ₃, comm₁₂ := h₁₂.symm, comm₂₃ := h₂₃.symm }
  rw [etaleCohomologyPullback_apply, etaleCohomologyPullback_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass _ hS, Ext.comp_assoc_of_third_deg_zero, hn,
    ← Ext.comp_assoc_of_second_deg_zero]
  exact Ext.comp_assoc _ _ _ (zero_add p) rfl (by omega)

end Pullback

end Stacks.EtaleCohomology

end
