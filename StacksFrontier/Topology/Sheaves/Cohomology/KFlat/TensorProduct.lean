module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Homology.BifunctorAssociator
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Localization.Trifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedSymmetry
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# The tensor product of complexes with a K-flat complex is K-flat

Let `R` be a sheaf of commutative rings on a site. If `K` and `L` are K-flat complexes of
`R`-modules then the total tensor product `Tot(K ⊗_R L)` is K-flat.

The proof transports the associativity of the objectwise tensor product of presheaves of
modules through sheafification, using the localization-theoretic associator, and then applies
the mapping-bifunctor associator for complexes.

## Main results

* `Stacks.SheafOfModules.kFlat_tensorComplex`: K-flatness of the total tensor product.

## Implementation notes

Every object here is spelled over `(Stacks.SheafOfModules.Tensor.ringSheaf R).obj`, the structure
presheaf used by `PresheafOfModules.sheafification` and `SheafOfModules.forget`, rather than over
`AlgebraicGeometry.SheafOfModules.ringPresheaf R.obj`. The two are definitionally but not
reducibly equal, so a rewrite whose pattern mixes them does not fire; the boundary is crossed
only in term position, where a single definitional check settles it. Sheafification, its
adjunction and unit, and the canonical `PresheafOfModules.tensorBifunctor` and `Tensor.sheafTensor`
bifunctors are used directly, without file-local spelling wrappers.

## References

* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] PresheafOfModules.tensorBifunctor CategoryTheory.sheafCompose

/-! ### Sheafification and tensor bifunctors -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{w})
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **Tag 05NB**, cited at this file's spelling: tensoring preserves local isomorphisms. -/
lemma W_presheafTensorRightMod
    {A B : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    (h : J.W ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf R).obj).map f))
      :
    J.W ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf R).obj).map
      (((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).flip.obj X).map f)) :=
  Stacks.SheafOfModules.TensorColimits.TensorLocalization.W_whiskerRight R.obj f X h

/-! ### Symmetry of the objectwise tensor product -/

section TensorComm

/-- Tensoring on the left and on the right agree by the canonical presheaf symmetry. -/
noncomputable def tensorCommIso
    (F : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).obj F ≅
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).flip.obj F :=
  NatIso.ofComponents
    (fun module => Stacks.SheafOfModules.TensorRaised.presheafTensorSwapIso.{u, v, w, w}
      (O := R.obj) F module)
    (fun morphism =>
      Stacks.SheafOfModules.TensorRaised.presheafTensorSwap_naturality.{u, v, w, w}
        (O := R.obj) (𝟙 F) morphism)

end TensorComm

/-! ### What sheafification inverts -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Sheafification inverts exactly the local isomorphisms. -/
lemma sheafifyMod_map_isIso_iff_W
    {P Q : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj} (f : P ⟶ Q) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map f) ↔
      J.W ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf R).obj).map f) :=
        by
  show MorphismProperty.isomorphisms _
    ((PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)).map f) ↔
      _
  show ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj))) f ↔ _
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Sheafification inverts a local isomorphism tensored on the left with a fixed presheaf. -/
lemma sheafifyMod_inverts_presheafTensorLeft
    (F : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    {P Q : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj} (f : P ⟶ Q)
    (hf : IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map f)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
      (((PresheafOfModules.tensorBifunctor (R).obj).obj F).map f)) := by
  have he : ((PresheafOfModules.tensorBifunctor (R).obj).obj F).map f =
      (tensorCommIso R F).hom.app P ≫
        ((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).flip.obj F).map f ≫
        (tensorCommIso R F).inv.app Q :=
    ((Iso.eq_comp_inv ((tensorCommIso R F).app Q)).2
      ((tensorCommIso R F).hom.naturality f)).trans (Category.assoc _ _ _)
  replace hf := (sheafifyMod_map_isIso_iff_W R f).mp hf
  refine (sheafifyMod_map_isIso_iff_W R
    (((PresheafOfModules.tensorBifunctor (R).obj).obj F).map f)).mpr ?_
  let forgetModules := PresheafOfModules.toPresheaf (Tensor.ringSheaf R).obj
  have expandRight := forgetModules.map_comp
    (((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).flip.obj F).map f)
    ((tensorCommIso R F).inv.app Q)
  have expandAll := (forgetModules.map_comp ((tensorCommIso R F).hom.app P)
    (((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).flip.obj F).map f ≫
      (tensorCommIso R F).inv.app Q)).trans
    (congrArg (fun morphism => forgetModules.map ((tensorCommIso R F).hom.app P) ≫ morphism)
      expandRight)
  have : IsIso (forgetModules.map ((tensorCommIso R F).hom.app P)) :=
    Iso.isIso_hom (forgetModules.mapIso ((tensorCommIso R F).app P))
  have : IsIso (forgetModules.map ((tensorCommIso R F).inv.app Q)) :=
    Iso.isIso_inv (forgetModules.mapIso ((tensorCommIso R F).app Q))
  exact (congrArg (fun morphism => J.W morphism)
    ((congrArg (fun morphism => forgetModules.map morphism) he).trans expandAll)).mpr
      (J.W.comp_mem _ _ (MorphismProperty.of_isIso _ _)
        (J.W.comp_mem _ _ (W_presheafTensorRightMod R f F hf) (MorphismProperty.of_isIso _ _)))

/-! ### The two-variable tensor product of morphisms -/

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The two-variable tensor splits into its two one-variable parts. -/
lemma tensorHomMod_factor
    {G G' F F' : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj}
    (φ : G ⟶ G') (ψ : F ⟶ F') :
    PresheafOfModules.tensorHom (O := R.obj) φ ψ =
      PresheafOfModules.tensorHom (O := R.obj) φ (𝟙 F) ≫
        PresheafOfModules.tensorHom (O := R.obj) (𝟙 G') ψ :=
  (congrArg₂ (fun u v => PresheafOfModules.tensorHom (O := R.obj) u v)
      (Category.comp_id φ).symm (Category.id_comp ψ).symm).trans
    (PresheafOfModules.tensorHom_comp (O := R.obj) φ (𝟙 F) (𝟙 G') ψ).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **Tag 05NB** for `PresheafOfModules.tensorHom`. -/
lemma W_tensorHomMod_id_right
    {A B : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj} (f : A ⟶ B)
    (X : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    (h : J.W ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf R).obj).map f))
      :
    J.W ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf R).obj).map
      (PresheafOfModules.tensorHom (O := R.obj) f (𝟙 X))) :=
  Stacks.SheafOfModules.TensorColimits.TensorLocalization.W_whiskerRight R.obj f X h

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Sheafification inverts a local isomorphism tensored on the left. -/
lemma sheafifyMod_inverts_tensorHomMod_id_left
    (G : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)
    {F F' : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj} (ψ : F ⟶ F')
    (h : IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map ψ)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
      (PresheafOfModules.tensorHom (O := R.obj) (𝟙 G) ψ)) :=
  sheafifyMod_inverts_presheafTensorLeft R G ψ h

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Sheafification inverts the tensor product of two local isomorphisms. -/
lemma sheafifyMod_map_tensorHomMod_isIso
    {P P' Q Q' : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj}
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map f))
    (hg : IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map g)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
      (PresheafOfModules.tensorHom (O := R.obj) f g)) := by
  have h1 : IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
      (PresheafOfModules.tensorHom (O := R.obj) f (𝟙 Q))) :=
    (sheafifyMod_map_isIso_iff_W R _).mpr
      (W_tensorHomMod_id_right R f Q ((sheafifyMod_map_isIso_iff_W R f).mp hf))
  have h2 : IsIso ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
      (PresheafOfModules.tensorHom (O := R.obj) (𝟙 P') g)) :=
    sheafifyMod_inverts_tensorHomMod_id_left R P' g hg
  have hcomp := (congrArg
      (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
      (tensorHomMod_factor R f g)).trans
    ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map_comp _ _)
  exact hcomp.symm ▸ ((@asIso _ _ _ _ _ h1) ≪≫ (@asIso _ _ _ _ _ h2)).isIso_hom

/-- Two factorizations of a two-variable tensor product of composites agree when the factors do. -/
private theorem tensorHom_comp_eq_tensorHom_comp {D : Type*} [Category D]
    {O : Dᵒᵖ ⥤ CommRingCat.{w}}
    {P₁ P₂ P₃ P₂' Q₁ Q₂ Q₃ Q₂' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
    {f : P₁ ⟶ P₂} {g : P₂ ⟶ P₃} {f' : P₁ ⟶ P₂'} {g' : P₂' ⟶ P₃}
    {u : Q₁ ⟶ Q₂} {v : Q₂ ⟶ Q₃} {u' : Q₁ ⟶ Q₂'} {v' : Q₂' ⟶ Q₃}
    (hfg : f ≫ g = f' ≫ g') (huv : u ≫ v = u' ≫ v') :
    PresheafOfModules.tensorHom f u ≫ PresheafOfModules.tensorHom g v =
      PresheafOfModules.tensorHom f' u' ≫ PresheafOfModules.tensorHom g' v' :=
  (PresheafOfModules.tensorHom_comp f u g v).trans
    ((congrArg₂ (fun a b => PresheafOfModules.tensorHom a b) hfg huv).trans
      (PresheafOfModules.tensorHom_comp f' u' g' v').symm)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Naturality of the two-variable tensor in its right argument. -/
lemma tensorHomMod_naturality_right
    {P Q Q' : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj}
    (ηP : P ⟶ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
      ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj P))
    (ηQ : Q ⟶ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
      ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj Q))
    (ηQ' : Q' ⟶ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
      ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj Q'))
    (g : Q ⟶ Q')
    (hη : ηQ ≫ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map
        ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map g) = g ≫ ηQ') :
    PresheafOfModules.tensorHom (O := R.obj) ηP ηQ ≫ PresheafOfModules.tensorHom (O := R.obj)
        (𝟙 ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
          ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj P)))
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map
          ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map g)) =
      PresheafOfModules.tensorHom (O := R.obj) (𝟙 P) g ≫
        PresheafOfModules.tensorHom (O := R.obj) ηP ηQ' :=
  tensorHom_comp_eq_tensorHom_comp ((Category.comp_id ηP).trans (Category.id_comp ηP).symm) hη

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Naturality of the two-variable tensor in its left argument. -/
lemma tensorHomMod_naturality_left
    {P P' Q : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj}
    (ηP : P ⟶ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
      ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj P))
    (ηP' : P' ⟶ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
      ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj P'))
    (ηQ : Q ⟶ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
      ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj Q))
    (f : P ⟶ P')
    (hη : ηP ≫ (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map
        ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map f) = f ≫ ηP') :
    PresheafOfModules.tensorHom (O := R.obj) ηP ηQ ≫ PresheafOfModules.tensorHom (O := R.obj)
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map
          ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map f))
        (𝟙 ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
          ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj Q))) =
      PresheafOfModules.tensorHom (O := R.obj) f (𝟙 Q) ≫
        PresheafOfModules.tensorHom (O := R.obj) ηP' ηQ :=
  tensorHom_comp_eq_tensorHom_comp hη ((Category.comp_id ηQ).trans (Category.id_comp ηQ).symm)

/-! ### Comparing the sheafified presheaf tensor product with the sheaf tensor product -/

/-- Sheafifying the objectwise tensor product of two presheaves gives the tensor product of
their sheafifications. -/
noncomputable def sheafTensorSheafifyIso
    (P Q : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj
        (((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).obj P).obj Q) ≅
      ((Tensor.sheafTensor.{u, v, w, w, w} R).obj
        ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj P)).obj
          ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj Q) :=
  @asIso _ _ _ _
    ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
      (PresheafOfModules.tensorHom (O := R.obj)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app P)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app Q)))
    (PresheafOfModules.isIso_sheafification_tensor_units.{v, u, w, w, w}
      (Osharp := R) J (𝟙 R.obj) P Q)

/-- The comparison isomorphism is sheafification applied to the tensor of the two units. -/
lemma sheafTensorSheafifyIso_hom
    (P Q : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    (sheafTensorSheafifyIso R P Q).hom =
      (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
        (PresheafOfModules.tensorHom (O := R.obj)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app P)
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app Q)) :=
  rfl

/-- The comparison isomorphism, natural in the second variable. -/
noncomputable def sheafTensorSheafifyNatIso
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    (show PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
        PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj from
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj).obj P) ⋙
        PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj) ≅
      PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj) ⋙
        (Tensor.sheafTensor.{u, v, w, w, w} R).obj
          ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj P) :=
  NatIso.ofComponents (fun Q => sheafTensorSheafifyIso R P Q) (by
    intro Q Q' g
    have hbase := tensorHomMod_naturality_right R
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app P)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app Q)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app Q') g
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Tensor.ringSheaf R).obj)).unit.naturality g).symm)
    change (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
        (PresheafOfModules.tensorHom (O := R.obj) (𝟙 P) g) ≫ (sheafTensorSheafifyIso R P Q').hom =
      (sheafTensorSheafifyIso R P Q).hom ≫
        (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
          (PresheafOfModules.tensorHom (O := R.obj)
            (𝟙 ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
              ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj P)))
            ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map
              ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map g)))
    rw [sheafTensorSheafifyIso_hom, sheafTensorSheafifyIso_hom]
    exact ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map_comp _ _).symm.trans
      ((congrArg
        (fun k => (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map k)
        hbase.symm).trans
        ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map_comp _ _)))

/-! ### The localization lifting -/

/-- The comparison isomorphism is natural in the first variable too. -/
lemma sheafTensorSheafifyIso_naturality_left
    {P P' : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj}
    (f : P ⟶ P') (Q : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :
    (sheafTensorSheafifyIso R P Q).hom ≫
        ((Tensor.sheafTensor.{u, v, w, w, w} R).map
          ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map f)).app
            ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj Q) =
      (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
        (PresheafOfModules.tensorHom (O := R.obj) f (𝟙 Q)) ≫
          (sheafTensorSheafifyIso R P' Q).hom := by
  have hbase := tensorHomMod_naturality_left R
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app P)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app P')
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (Tensor.ringSheaf R).obj)).unit.app Q) f
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Tensor.ringSheaf R).obj)).unit.naturality f).symm)
  rw [sheafTensorSheafifyIso_hom, sheafTensorSheafifyIso_hom, Tensor.sheafTensor_map_app]
  exact ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map_comp _ _).symm.trans
    ((congrArg
      (fun k => (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map k)
      hbase).trans ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map_comp _ _))

/-- The local isomorphisms of presheaves of modules. -/
abbrev sheafificationW :=
  J.W.inverseImage (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)

/-- The sheaf tensor product is the localization of the objectwise tensor product. -/
@[instance_reducible]
noncomputable def sheafTensorLifting₂ :
    CategoryTheory.Localization.Lifting₂
      (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj))
      (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj))
      (sheafificationW R) (sheafificationW R)
      ((show PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
            PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj ⥤
              PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj from
          PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj) ⋙
        (Functor.whiskeringRight _ _ _).obj
          (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)))
      (Tensor.sheafTensor.{u, v, w, w, w} R) where
  iso := NatIso.ofComponents (fun P => (sheafTensorSheafifyNatIso R P).symm) (by
    intro P P' f
    apply NatTrans.ext
    funext Q
    change ((Tensor.sheafTensor.{u, v, w, w, w} R).map
        ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map f)).app
          ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).obj Q) ≫
        (sheafTensorSheafifyIso R P' Q).inv =
      (sheafTensorSheafifyIso R P Q).inv ≫
        (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map
          (PresheafOfModules.tensorHom (O := R.obj) f (𝟙 Q))
    rw [← cancel_epi (sheafTensorSheafifyIso R P Q).hom, ← Category.assoc,
      sheafTensorSheafifyIso_naturality_left, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc])

/-! ### The associator -/

/-- Associativity of the objectwise tensor product, as an isomorphism of trifunctors. This is
the monoidal associator of `PresheafOfModules`, curried; the monoidal structure is the one
`Tag 05NB`'s module provides at this file's spelling of the structure presheaf. -/
noncomputable def presheafTensorAssocNatIso :
    CategoryTheory.bifunctorComp₁₂
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj)
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj) ≅
      CategoryTheory.bifunctorComp₂₃
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj)
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj) :=
  CategoryTheory.MonoidalCategory.curriedAssociatorNatIso
    (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj)

/-- The associator for the tensor product of sheaves of modules, obtained by transporting the
objectwise associator through sheafification. -/
noncomputable def sheafTensorAssociatorAux :
    CategoryTheory.bifunctorComp₁₂
        (Tensor.sheafTensor.{u, v, w, w, w} R) (Tensor.sheafTensor.{u, v, w, w, w} R) ≅
      CategoryTheory.bifunctorComp₂₃
        (Tensor.sheafTensor.{u, v, w, w, w} R) (Tensor.sheafTensor.{u, v, w, w, w} R) := by
  letI : Presheaf.IsLocallyInjective J (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
    inferInstance
  letI : Presheaf.IsLocallySurjective J (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf R).obj) :=
    inferInstance
  letI : (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).IsLocalization
      (sheafificationW R) := inferInstance
  letI := sheafTensorLifting₂ R
  exact CategoryTheory.Localization.associator
    (L₁ := PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj))
    (L₂ := PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj))
    (L₃ := PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj))
    (L₁₂ := PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj))
    (L₂₃ := PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj))
    (L := PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj))
    (W₁ := sheafificationW R) (W₂ := sheafificationW R) (W₃ := sheafificationW R)
    (W₁₂ := sheafificationW R) (W₂₃ := sheafificationW R)
    (F₁₂ := PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj)
    (G := PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj)
    (F := PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj)
    (G₂₃ := PresheafOfModules.tensorBifunctor.{v, u, w, w, w} R.obj)
    (iso := presheafTensorAssocNatIso R)
    (F₁₂' := Tensor.sheafTensor.{u, v, w, w, w} R) (G' := Tensor.sheafTensor.{u, v, w, w, w} R)
    (F' := Tensor.sheafTensor.{u, v, w, w, w} R) (G₂₃' := Tensor.sheafTensor.{u, v, w, w, w} R)

/-- **The associator for the tensor product of sheaves of modules**, at Tag 06YM's spelling. -/
noncomputable def sheafTensorAssociator :
    CategoryTheory.bifunctorComp₁₂ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) ≅
      CategoryTheory.bifunctorComp₂₃ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) :=
  sheafTensorAssociatorAux R

/-! ### Colimit preservation in each variable -/

/-- Tensoring on the left and tensoring on the right agree, after sheafification. -/
noncomputable def sheafTensorMod_flipIso
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor (J := J) (R)).obj P ≅
      (Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj P :=
  NatIso.ofComponents
    (fun Q => (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).mapIso
      ((tensorCommIso R ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj
        P)).app
        ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj Q)))
    (by
      intro Q Q' f
      have h := congrArg
        (fun k => (PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map k)
        ((tensorCommIso R
          ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).obj P)).hom.naturality
          ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf R)).map f))
      exact
        ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map_comp _ _).symm.trans
        (h.trans ((PresheafOfModules.sheafification (𝟙 (Tensor.ringSheaf R).obj)).map_comp _ _)))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Tag 05NB.** Tensoring with a fixed sheaf of modules on the left preserves colimits. -/
@[ega "0 4.1.5" "partial, tensor product"]
theorem sheafTensorMod_obj_preservesColimits
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{0, w} ((Tensor.sheafTensor.{u, v, w, w, w} R).obj P) :=
  -- The sheaf-condition composition omitted from this statement is supplied here from the
  -- unconditional fact: `forget₂ CommRingCat RingCat` preserves limits of every size.
  have := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits J R P

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **Tag 05NB.** Tensoring with a fixed sheaf of modules on the right preserves colimits. -/
@[ega "0 4.1.5" "partial, tensor product"]
theorem sheafTensorMod_flip_obj_preservesColimits
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{0, w} ((Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj P) := by
  have := sheafTensorMod_obj_preservesColimits R P
  exact preservesColimits_of_natIso (sheafTensorMod_flipIso R P)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Tensoring on the left preserves colimits indexed in the smallest universe. -/
@[ega "0 4.1.5" "partial, tensor product"]
theorem sheafTensor_obj_preservesSmallestColimits
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{0, 0}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj P) := by
  have : PreservesColimitsOfSize.{0, w}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj P) :=
    sheafTensorMod_obj_preservesColimits R P
  exact preservesSmallestColimits_of_preservesColimits _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Tensoring on the right preserves colimits indexed in the smallest universe. -/
theorem sheafTensor_flip_obj_preservesSmallestColimits
    (P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    PreservesColimitsOfSize.{0, 0}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj P) := by
  have : PreservesColimitsOfSize.{0, w}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).flip.obj P) :=
    sheafTensorMod_flip_obj_preservesColimits R P
  exact preservesSmallestColimits_of_preservesColimits _

/-! ### K-flatness of the total tensor product -/

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) (ComplexShape.up ℤ)]

/-- **Stacks 079R.** The total tensor product of two K-flat complexes of sheaves of modules is
K-flat. -/
@[stacks 079R]
theorem kFlat_tensorComplex
    {K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (hK : Stacks.SheafOfModules.IsKFlat R K) (hL : Stacks.SheafOfModules.IsKFlat R L) :
    Stacks.SheafOfModules.IsKFlat R (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj K).obj L)
      := by
  intro F hF i
  let _ := sheafTensor_obj_preservesSmallestColimits R
  let _ := sheafTensor_flip_obj_preservesSmallestColimits R
  let _ : HomologicalComplex.HasGoodTrifunctor₁₂Obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) F K L
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) := fun i j => by infer_instance
  let _ : HomologicalComplex.HasGoodTrifunctor₂₃Obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} R) F K L
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) := fun i j => by infer_instance
  let e := HomologicalComplex.mapBifunctorAssociator (sheafTensorAssociator R)
    F K L (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  exact ((hL _ (hK F hF)) i).of_iso e

end Stacks.SheafOfModules
