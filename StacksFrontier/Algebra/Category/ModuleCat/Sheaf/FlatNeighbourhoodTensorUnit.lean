module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
import StacksCore.Tactic.StacksAttribute

/-!
# Flat neighbourhood isomorphisms for sheaves of modules

Let `O ⟶ O'` be a flat morphism of sheaves of commutative rings on a site.  If it
is an isomorphism modulo an ideal sheaf `I`, extension of scalars along this morphism
does not change an `O`-module annihilated by a power of `I`.

## Main definitions

* `Stacks.Sheaves.FlatNeighbourhood.restrictedOne` is the unit section of `O'`, read as a section
  of the
  restriction of scalars of `O'` along `O ⟶ O'`.
* `Stacks.Sheaves.FlatNeighbourhood.tensorUnitSection` is the section `x ⊗ 1` of `F ⊗_O O'`.
* `Stacks.Sheaves.FlatNeighbourhood.tensorUnitMap` is the canonical map `F ⟶ F ⊗_O O'`, specified
  by its value on sections before sheafification.
* `Stacks.Sheaves.FlatNeighbourhood.tensorUnitMap_naturality` records its naturality in `F`.

## Main results

* `Stacks.Sheaves.FlatNeighbourhood.isIso_tensorUnitMap_of_pow_smul_eq_zero` says that the
  canonical
  extension-of-scalars map is an isomorphism under the neighbourhood hypotheses.

## Implementation notes

An ideal sheaf is represented by a monomorphism into the rank-one module `O`; since
`O` is commutative, an `O`-submodule of `O` is precisely an ideal.  Quotient sheaves
are categorical cokernels.  Thus the map on quotients is specified by its commuting
square with the two cokernel projections.  The condition `I ^ n F = 0` is written
sectionwise: every product of `n` sections of `I` annihilates every section of `F`.
The tensor-unit map is packaged with its formula `x ↦ x ⊗ 1` followed by the
sheafification unit; in particular it is not an arbitrary morphism.  The module
universe agrees with the ring universe because the available rank-one sheaf
module and tensor endofunctor are at that universe.

Restriction of scalars along an identity, and the forgetful functor from sheaves of
modules, are semireducible, so `(SheafOfModules.forget R ⋙ restrictScalars (𝟙 R.obj)).obj F`
and `F.val` agree definitionally but not at the transparency level at which `rw`, `simp`
and instance search check that a term is type-correct.  Every statement here is therefore
phrased with `F.val`, and the identification is carried by the result type of a
definition — `restrictedOne`, `tensorUnitSection`, `sheafificationValHom`,
`sheafificationValIso` and `tensorUnitHom` — rather than crossed by a rewrite.  The one
place where the unit and counit of `PresheafOfModules.sheafificationAdjunction` are used
at their own phrasing is inside the proofs of `sheafificationValHom_unit` and
`sheafification_map_presheafTensorUnit`, where a type ascription does the crossing.

## References

* [Stacks Project, Tag 0GLY](https://stacks.math.columbia.edu/tag/0GLY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe v u w

open AlgebraicGeometry.SheafOfModules

attribute [local instance_reducible] CategoryTheory.sheafCompose PresheafOfModules.unit

namespace Stacks.Sheaves.FlatNeighbourhood

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]

noncomputable local instance isIso_associatedRingMap_id (O : Sheaf J CommRingCat.{w}) :
    IsIso (associatedRingMap J (𝟙 O.obj)) := by
  rw [show associatedRingMap J (𝟙 O.obj) =
    𝟙 (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) from rfl]
  exact IsIso.id _

noncomputable abbrev RingModule (O : Sheaf J CommRingCat.{w}) :=
  SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)

noncomputable abbrev RestrictedRingModule {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O') :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)).obj
      (RingModule O')

/-- The unit section of `O'`, read as a section of the restriction of scalars of the
rank-one `O'`-module along `f`.  The identification is carried by the result type, so that
terms mentioning it stay type-correct without unfolding `SheafOfModules.restrictScalars`. -/
noncomputable def restrictedOne {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O') (X : Cᵒᵖ) :
    (RestrictedRingModule f).val.obj X :=
  (1 : O'.obj.obj X)

private noncomputable def presheafRingMap {O O' : Sheaf J CommRingCat.{w}}
    (f : O ⟶ O') :
    PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⟶ (RestrictedRingModule f).val :=
  (PresheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk (fun X => (1 : O'.obj.obj X))
      (fun {_ _} g => (O'.obj.map g).hom.map_one))

private noncomputable def presheafTensorUnit {O O' : Sheaf J CommRingCat.{w}}
    (f : O ⟶ O') (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    P ⟶ MonoidalCategoryStruct.tensorObj P (RestrictedRingModule f).val :=
  (MonoidalCategory.rightUnitor P).inv ≫
    MonoidalCategory.whiskerLeft P (presheafRingMap f)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private lemma presheafTensorUnit_apply {O O' : Sheaf J CommRingCat.{w}}
    (f : O ⟶ O') (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (X : Cᵒᵖ) (x : P.obj X) :
    (presheafTensorUnit f P).app X x =
      x ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X] restrictedOne f X := by
  change x ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X]
    ((1 : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X) • restrictedOne f X) = _
  rw [one_smul]

private lemma isIso_sheafification_tensorHom
    (O : Sheaf J CommRingCat.{w})
    {P P' Q Q' : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
    (a : P ⟶ P') (b : Q ⟶ Q')
    (ha : IsIso ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map a))
    (hb : IsIso ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map b)) :
    IsIso ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map
        (PresheafOfModules.Monoidal.tensorHom a b)) := by
  let S := _root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)
  let T := Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O)
  let e := _root_.PresheafOfModules.sheafificationTensorIso J (𝟙 O.obj)
  have : IsIso (S.map a) := ha
  have : IsIso (S.map b) := hb
  have : IsIso (Prod.mkHom (S.map a) (S.map b)) :=
    (isIso_prod_iff _ _).mpr ⟨ha, hb⟩
  have h : T.map (Prod.mkHom (S.map a) (S.map b)) ≫ (e.app (P', Q')).hom =
      (e.app (P, Q)).hom ≫ S.map (PresheafOfModules.Monoidal.tensorHom a b) :=
    (e.hom.naturality (show (P, Q) ⟶ (P', Q') from (a, b))).trans
      (congrArg (fun morphism ↦ (e.app (P, Q)).hom ≫ S.map morphism)
        (PresheafOfModules.tensorBifunctor_uncurry_map (O := O.obj) a b))
  have heq : S.map (PresheafOfModules.Monoidal.tensorHom a b) =
      (e.app (P, Q)).inv ≫ T.map
        (Prod.mkHom (S.map a) (S.map b)) ≫
          (e.app (P', Q')).hom := by
    apply (cancel_epi (e.app (P, Q)).hom).1
    exact h.symm.trans ((e.app (P, Q)).hom_inv_id_assoc _).symm
  change IsIso (S.map (PresheafOfModules.Monoidal.tensorHom a b))
  rw [heq]
  exact ((e.app (P, Q)).symm ≪≫
    T.mapIso (Iso.prod (@asIso _ _ _ _ (S.map a) ha)
      (@asIso _ _ _ _ (S.map b) hb)) ≪≫
    e.app (P', Q')).isIso_hom

section

open MonoidalCategory

variable {A : Type*} [Category A] [MonoidalCategory A]

private lemma tensorUnit_naturality {B P Q : A} (a : 𝟙_ A ⟶ B) (g : P ⟶ Q) :
    g ≫ (ρ_ Q).inv ≫ Q ◁ a = (ρ_ P).inv ≫ P ◁ a ≫ g ▷ B := by
  rw [rightUnitor_inv_naturality_assoc, whisker_exchange]

private lemma tensorUnit_tensor (B P Q : A) (a : 𝟙_ A ⟶ B) :
    (ρ_ (P ⊗ Q)).inv ≫ (P ⊗ Q) ◁ a =
      P ◁ ((ρ_ Q).inv ≫ Q ◁ a) ≫ (α_ P Q B).inv := by
  simp only [rightUnitor_tensor_inv, Category.assoc, whiskerLeft_comp]
  rw [associator_inv_naturality_right]

private lemma isIso_map_tensorUnit_of_tensor_ideal_eq_zero
    [HasZeroMorphisms A] [HasCokernels A]
    {D : Type*} [Category D] (L : A ⥤ D)
    (hL : ∀ {X Y : A} (g : X ⟶ Y) (P : A),
      IsIso (L.map g) → IsIso (L.map (P ◁ g)))
    {I B : A} (i : I ⟶ 𝟙_ A) (a : 𝟙_ A ⟶ B) (P : A)
    [(tensorLeft P).PreservesZeroMorphisms]
    [PreservesColimit (parallelPair i 0) (tensorLeft P)]
    (hP : P ◁ i = 0)
    (hQ : IsIso (L.map ((ρ_ (cokernel i)).inv ≫ (cokernel i) ◁ a))) :
    IsIso (L.map ((ρ_ P).inv ≫ P ◁ a)) := by
  let Q := cokernel i
  let g : P ⟶ P ⊗ Q := (ρ_ P).inv ≫ P ◁ cokernel.π i
  have : IsIso (P ◁ cokernel.π i) := by
    let e := PreservesCokernel.iso (tensorLeft P) i
    have : IsIso (cokernel.π ((tensorLeft P).map i)) := cokernel.π_of_zero hP
    have heq : P ◁ cokernel.π i = cokernel.π ((tensorLeft P).map i) ≫ e.inv := by
      apply (cancel_mono e.hom).1
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
      exact PreservesCokernel.π_iso_hom (tensorLeft P) i
    rw [heq]
    infer_instance
  have : IsIso g := by dsimp [g]; infer_instance
  have : IsIso (L.map ((ρ_ (P ⊗ Q)).inv ≫ (P ⊗ Q) ◁ a)) := by
    rw [tensorUnit_tensor, L.map_comp]
    have := hL ((ρ_ Q).inv ≫ Q ◁ a) P hQ
    infer_instance
  have : IsIso (L.map ((ρ_ P).inv ≫ P ◁ a) ≫ L.map (g ▷ B)) := by
    rw [← L.map_comp, Category.assoc, ← tensorUnit_naturality, L.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (L.map (g ▷ B))

end

private lemma isIso_sheafification_tensorUnit_of_annihilated
    (O : Sheaf J CommRingCat.{w})
    {I B : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
    (i : I ⟶ PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (a : PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⟶ B)
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (hP : ∀ X (x : P.obj X) (y : I.obj X), (i.app X y) • x = 0)
    (hQ : IsIso ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map
        ((MonoidalCategory.rightUnitor (cokernel i)).inv ≫
          MonoidalCategory.whiskerLeft (cokernel i) a))) :
    IsIso ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map
        ((MonoidalCategory.rightUnitor P).inv ≫ MonoidalCategory.whiskerLeft P a)) := by
  let S := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)
  let L := MonoidalCategory.tensorLeft P
  let : PreservesFiniteColimits L :=
    PreservesColimitsOfSize.preservesFiniteColimits L
  have : L.PreservesZeroMorphisms := by
    constructor
    intro X Y
    ext U : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    change x ⊗ₜ[O.obj.obj U] (0 : Y.obj U) = 0
    simp only [TensorProduct.tmul_zero]
  exact isIso_map_tensorUnit_of_tensor_ideal_eq_zero S (by
    intro X Y g M hg
    exact isIso_sheafification_tensorHom O (𝟙 M) g (by infer_instance) hg) i a P (by
    apply (cancel_mono (MonoidalCategory.rightUnitor P).hom).1
    rw [zero_comp]
    ext X : 1
    let : CommRing ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X) :=
      inferInstanceAs (CommRing (O.obj.obj X))
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    exact hP X x y) hQ

/-- The section `x ⊗ 1` of `F ⊗_O O'`: the elementary tensor, followed by the unit of the
sheafification adjunction.  The identification of the sheafified tensor product with the
value of the right tensor functor is carried by the result type. -/
noncomputable def tensorUnitSection {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (X : Cᵒᵖ) (x : F.val.obj X) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
        (RestrictedRingModule f)).obj F).val.obj X :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
      (MonoidalCategoryStruct.tensorObj F.val
        (RestrictedRingModule f).val)).app X
    (x ⊗ₜ[O.obj.obj X] restrictedOne f X)

/-- The canonical extension-of-scalars morphism `F ⟶ F ⊗_O O'`, with its
sectionwise tensor-with-one formula before sheafification. -/
noncomputable def tensorUnitMap {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    { t : F ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
        (RestrictedRingModule f)).obj F //
      ∀ (X : Cᵒᵖ) (x : F.val.obj X),
        t.val.app X x = tensorUnitSection f F X x } := by
  classical
  let R := Stacks.SheafOfModules.Tensor.ringSheaf O
  let R' := Stacks.SheafOfModules.Tensor.ringSheaf O'
  let rf : R ⟶ R' := (sheafCompose J (forget₂ CommRingCat RingCat)).map f
  let α : PresheafOfModules.unit R.obj ⟶ (RestrictedRingModule f).val :=
    PresheafOfModules.homMk
      { app := fun X => AddCommGrpCat.ofHom (rf.hom.app X).hom.toAddMonoidHom
        naturality := by
          intro X Y g
          apply AddCommGrpCat.hom_ext
          ext r
          change (rf.hom.app Y).hom ((R.obj.map g) r) =
            (R'.obj.map g) ((rf.hom.app X).hom r)
          exact NatTrans.naturality_apply rf.hom g r }
      (by
        intro X r m
        let m' : R.obj.obj X := m
        change (rf.hom.app X).hom (r • m') =
          (rf.hom.app X).hom r • (rf.hom.app X).hom m'
        simpa only [smul_eq_mul] using map_mul (rf.hom.app X).hom r m')
  letI : MonoidalCategory (PresheafOfModules R.obj) :=
    PresheafOfModules.monoidalCategory
  let c : F.val ⟶ MonoidalCategoryStruct.tensorObj F.val
      (RestrictedRingModule f).val :=
    (MonoidalCategoryStruct.rightUnitor F.val).inv ≫
      MonoidalCategoryStruct.tensorHom (𝟙 F.val) α
  let sh := PresheafOfModules.sheafification (R := R) (𝟙 R.obj)
  let τ := (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
    (MonoidalCategoryStruct.tensorObj F.val (RestrictedRingModule f).val)
  let t : F ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
      (RestrictedRingModule f)).obj F :=
    (SheafOfModules.fullyFaithfulForget R).preimage (c ≫ τ)
  refine ⟨t, ?_⟩
  intro X x
  let : CommRing (R.obj.obj X) := inferInstanceAs (CommRing (O.obj.obj X))
  let : Module (R.obj.obj X) (R'.obj.obj X) :=
    ((RestrictedRingModule f).val.obj X).isModule
  let αX := α.app X
  change (c ≫ τ).app X x = _
  apply congrArg (τ.app X)
  change MonoidalCategoryStruct.tensorUnit (ModuleCat (R.obj.obj X)) ⟶ _ at αX
  change (MonoidalCategoryStruct.tensorHom (𝟙 (F.val.obj X)) αX).hom
    ((MonoidalCategoryStruct.rightUnitor (F.val.obj X)).inv.hom x) = _
  rw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  change x ⊗ₜ[R.obj.obj X] (rf.hom.app X).hom 1 = _
  rw [(rf.hom.app X).hom.map_one]
  rfl

noncomputable section
/-- Tensoring with one commutes with morphisms of sheaves of modules. -/
lemma tensorUnitMap_naturality {O O' : Sheaf J CommRingCat.{w}}
    (f : O ⟶ O') {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (φ : F ⟶ G) :
    φ ≫ (tensorUnitMap f G).val =
      (tensorUnitMap f F).val ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
            (RestrictedRingModule f)).map φ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  let : CommRing (O.obj.obj X) := inferInstance
  let : Module (O.obj.obj X) (F.val.obj X) :=
    Module.compHom (R := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X)
      (S := O.obj.obj X) (F.val.obj X) (RingHom.id (O.obj.obj X))
  let : Module (O.obj.obj X) (G.val.obj X) :=
    Module.compHom (R := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X)
      (S := O.obj.obj X) (G.val.obj X) (RingHom.id (O.obj.obj X))
  let : Module (O.obj.obj X) ((RestrictedRingModule f).val.obj X) :=
    Module.compHom (R := (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X)
      (S := O.obj.obj X) ((RestrictedRingModule f).val.obj X)
      (RingHom.id (O.obj.obj X))
  let : Module (O.obj.obj X) (O'.obj.obj X) :=
    inferInstanceAs (Module (O.obj.obj X) ((RestrictedRingModule f).val.obj X))
  apply ModuleCat.hom_ext
  ext x
  change ((tensorUnitMap f G).val.val.app X) ((φ.val.app X) x) =
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
        (RestrictedRingModule f)).map φ).val.app X
      (((tensorUnitMap f F).val.val.app X) x)
  rw [(tensorUnitMap f G).property X (φ.val.app X x),
    (tensorUnitMap f F).property X x]
  let P : PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
      PresheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O).obj :=
    PresheafOfModules.tensorRight
      (O := O.obj) (RestrictedRingModule f).val
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit
  let Sh := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  have hNat := η.naturality (P.map φ.val)
  have hNatX := congrArg (fun ψ => ψ.app X (x ⊗ₜ[O.obj.obj X] (1 : O'.obj.obj X))) hNat
  change (η.app (P.obj G.val)).app X
      ((P.map φ.val).app X (x ⊗ₜ[O.obj.obj X] (1 : O'.obj.obj X))) =
    (Sh.map (P.map φ.val)).val.app X
      ((η.app (P.obj F.val)).app X (x ⊗ₜ[O.obj.obj X] (1 : O'.obj.obj X))) at hNatX
  convert hNatX using 1
  rfl

end

/-- The counit of the sheafification adjunction at `F`, with the source written as the
sheafification of `F.val` rather than as the sheafification of a restriction of scalars
along an identity. -/
private noncomputable def sheafificationValHom {O : Sheaf J CommRingCat.{w}}
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).obj F.val ⟶ F :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit.app F

private instance isIso_sheafificationValHom {O : Sheaf J CommRingCat.{w}}
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsIso (sheafificationValHom F) :=
  NatIso.isIso_app_of_isIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit F

/-- A sheaf of modules is the sheafification of its underlying presheaf of modules. -/
private noncomputable def sheafificationValIso {O : Sheaf J CommRingCat.{w}}
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).obj F.val ≅ F :=
  asIso (sheafificationValHom F)

/-- `tensorUnitMap`, with the sheafification of the presheaf tensor product as its target. -/
private noncomputable abbrev tensorUnitHom {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    F ⟶ (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).obj
      (MonoidalCategoryStruct.tensorObj F.val (RestrictedRingModule f).val) :=
  (tensorUnitMap f F).val

/-- The sheafification adjunction's hom-equivalence is precomposition with the unit. -/
private lemma sheafificationHomEquiv_app {O : Sheaf J CommRingCat.{w}}
    {P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
    {G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (g : (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).obj P ⟶ G)
    (X : Cᵒᵖ) (x : P.obj X) :
    (PresheafOfModules.sheafificationHomEquiv
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) g).app X x =
      g.val.app X (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app P).app X x) := rfl

/-- The counit undoes the unit on sections. -/
private lemma sheafificationValHom_unit {O : Sheaf J CommRingCat.{w}}
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (X : Cᵒᵖ) (x : F.val.obj X) :
    (sheafificationValHom F).val.app X
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app F.val).app X x) = x := by
  have h : ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app F.val ≫
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        PresheafOfModules.restrictScalars
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).map (sheafificationValHom F)) = 𝟙 F.val :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).right_triangle_components F
  exact congrArg (fun k => (ConcreteCategory.hom (k.app X)) x) h

private lemma sheafification_map_presheafTensorUnit
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map
      (presheafTensorUnit f F.val) =
    (sheafificationValIso F).hom ≫ tensorUnitHom f F := by
  apply (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).injective
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  ext x
  rw [sheafificationHomEquiv_app, sheafificationHomEquiv_app]
  change ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map
      (presheafTensorUnit f F.val)).val.app X _ =
    (tensorUnitHom f F).val.app X ((sheafificationValHom F).val.app X _)
  rw [sheafificationValHom_unit]
  refine Eq.trans ?_ ((tensorUnitMap f F).property X x).symm
  refine Eq.trans (congrArg (fun k => (ConcreteCategory.hom (k.app X)) x)
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.naturality
        (presheafTensorUnit f F.val))).symm ?_
  change ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (MonoidalCategoryStruct.tensorObj F.val (RestrictedRingModule f).val)).app X
      ((presheafTensorUnit f F.val).app X x) = _
  rw [presheafTensorUnit_apply]
  exact rfl

private lemma isIso_tensorUnitMap_iff_sheafification_map
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    IsIso (tensorUnitMap f F).val ↔
      IsIso ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 _)).map (presheafTensorUnit f F.val)) := by
  rw [sheafification_map_presheafTensorUnit]
  exact (isIso_comp_left_iff (sheafificationValIso F).hom (tensorUnitHom f F)).symm

private lemma isIso_sheafification_tensorUnit_iff
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    let S := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)
    IsIso (S.map (presheafTensorUnit f P)) ↔
      IsIso (tensorUnitMap f (S.obj P)).val := by
  intro S
  rw [isIso_tensorUnitMap_iff_sheafification_map]
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  have hη : IsIso (S.map (adj.unit.app P)) :=
    IsIso.of_isIso_fac_right (adj.left_triangle_components P)
  let η : P ⟶ ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (𝟙 _)).obj P).val := adj.unit.app P
  have : IsIso (S.map η) := hη
  have : IsIso (S.map (MonoidalCategory.whiskerRight η (RestrictedRingModule f).val)) :=
    isIso_sheafification_tensorHom O η (𝟙 _) hη
      (S.mapIso (Iso.refl (RestrictedRingModule f).val)).isIso_hom
  have h := congrArg S.map (tensorUnit_naturality (presheafRingMap f) η)
  change S.map (η ≫ presheafTensorUnit f (S.obj P).val) =
    S.map (presheafTensorUnit f P ≫
      MonoidalCategory.whiskerRight η (RestrictedRingModule f).val) at h
  simp only [CategoryTheory.Functor.map_comp] at h
  rw [← isIso_comp_right_iff (S.map (presheafTensorUnit f P))
    (S.map (MonoidalCategory.whiskerRight η (RestrictedRingModule f).val)), ← h,
    isIso_comp_left_iff]

private lemma isIso_tensorUnitMap_of_iso
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (e : F ≅ G)
    (hG : IsIso (tensorUnitMap f G).val) : IsIso (tensorUnitMap f F).val := by
  exact IsIso.of_isIso_fac_right (tensorUnitMap_naturality f e.hom).symm

private lemma isIso_sheafification_presheafCokernel_tensorUnit
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (i : F ⟶ G)
    (hQ : IsIso (tensorUnitMap f (cokernel i)).val) :
    IsIso ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
      (𝟙 _)).map (presheafTensorUnit f (cokernel i.val))) := by
  let S := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)
  have hcomm : S.map i.val ≫ (sheafificationValIso G).hom =
      (sheafificationValIso F).hom ≫ i :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit.naturality i
  let e : S.obj (cokernel i.val) ≅ cokernel i :=
    PreservesCokernel.iso S i.val ≪≫
      cokernel.mapIso (S.map i.val) i (sheafificationValIso F) (sheafificationValIso G) hcomm
  exact (isIso_sheafification_tensorUnit_iff f (cokernel i.val)).mpr
    (isIso_tensorUnitMap_of_iso f e hQ)

private lemma isIso_tensorUnitMap_cokernel_of_quotient_iso
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (hf : IsFlatMap f)
    {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (i : I ⟶ RingModule O) [Mono i]
    (hquot : ∃ q : cokernel i ⟶
        cokernel (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
            (RestrictedRingModule f)).map i),
      IsIso q ∧ cokernel.π i ≫ q = (tensorUnitMap f (RingModule O)).val ≫
        cokernel.π (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
            (RestrictedRingModule f)).map i)) :
    IsIso (tensorUnitMap f (cokernel i)).val := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
      (RestrictedRingModule f)
  let : PreservesFiniteColimits T := (exactFunctor_iff T).mp hf |>.2
  obtain ⟨q, hq, hqπ⟩ := hquot
  let e : T.obj (cokernel i) ≅ cokernel (T.map i) := PreservesCokernel.iso T i
  let q' : cokernel i ⟶ T.obj (cokernel i) := q ≫ e.inv
  have hcmp : cokernel.π (T.map i) ≫ e.inv = T.map (cokernel.π i) := by
    apply (cancel_mono e.hom).1
    simp [e, PreservesCokernel.π_iso_hom]
  have hπ : cokernel.π i ≫ q' = cokernel.π i ≫ (tensorUnitMap f (cokernel i)).val := by
    dsimp [q']
    calc
      cokernel.π i ≫ q ≫ e.inv =
          (cokernel.π i ≫ q) ≫ e.inv := by simp [Category.assoc]
      _ = ((tensorUnitMap f (RingModule O)).val ≫
          cokernel.π (T.map i)) ≫ e.inv := by rw [hqπ]
      _ = (tensorUnitMap f (RingModule O)).val ≫ T.map (cokernel.π i) := by
        rw [Category.assoc, hcmp]
      _ = cokernel.π i ≫ (tensorUnitMap f (cokernel i)).val :=
        (tensorUnitMap_naturality f (cokernel.π i)).symm
  have hq' : IsIso q' := by dsimp [q']; infer_instance
  have hepi : Epi (cokernel.π i) := by infer_instance
  have heq : q' = (tensorUnitMap f (cokernel i)).val := (cancel_epi _).1 hπ
  rw [← heq]
  exact hq'

private lemma isIso_tensorUnitMap_of_sections_eq_zero
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (hf : IsFlatMap f)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∀ (X : Cᵒᵖ) (x : F.val.obj X), x = 0) :
    IsIso (tensorUnitMap f F).val := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
      (RestrictedRingModule f)
  have hFzero : IsZero F := by
    rw [IsZero.iff_id_eq_zero]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    ext x
    simp [hF X x]
  have hTzero : IsZero (T.obj F) := by
    let : PreservesFiniteColimits T := (exactFunctor_iff T).mp hf |>.2
    let : PreservesFiniteLimits T := (exactFunctor_iff T).mp hf |>.1
    exact T.map_isZero hFzero
  exact hFzero.isIso hTzero _

private lemma isIso_tensorUnitMap_of_shortExact
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (hf : IsFlatMap f)
    {A B D : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (u : A ⟶ B) (v : B ⟶ D) (huv : u ≫ v = 0)
    (hS : (ShortComplex.mk u v huv).ShortExact)
    (hA : IsIso (tensorUnitMap f A).val)
    (hD : IsIso (tensorUnitMap f D).val) :
    IsIso (tensorUnitMap f B).val := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
      (RestrictedRingModule f)
  let : PreservesFiniteLimits T := (exactFunctor_iff T).mp hf |>.1
  let : PreservesFiniteColimits T := (exactFunctor_iff T).mp hf |>.2
  let : T.PreservesZeroMorphisms := inferInstance
  let S₁ := ShortComplex.mk u v huv
  let S₂ := S₁.map T
  let hS₂ : S₂.ShortExact := by
    change (S₁.map T).ShortExact
    exact hS.map_of_exact T
  let η : ShortComplex.Hom S₁ S₂ :=
    { τ₁ := (tensorUnitMap f A).val
      τ₂ := (tensorUnitMap f B).val
      τ₃ := (tensorUnitMap f D).val
      comm₁₂ := (tensorUnitMap_naturality f u).symm
      comm₂₃ := (tensorUnitMap_naturality f v).symm }
  let : IsIso η.τ₁ := by simpa [η, S₁, S₂] using hA
  let : IsIso η.τ₃ := by simpa [η, S₁, S₂] using hD
  have hb := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ η hS hS₂
  simpa [η, S₁, S₂] using hb

section

open MonoidalCategory

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]


private noncomputable abbrev idealAction
    {O : Sheaf J CommRingCat.{w}}
    {I : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
    (i : I ⟶ PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    P ⊗ I ⟶ P :=
  P ◁ i ≫ (ρ_ P).hom

private lemma idealAction_tmul
    {O : Sheaf J CommRingCat.{w}}
    {I : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
    (i : I ⟶ PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (X : Cᵒᵖ) (x : P.obj X) (y : I.obj X) :
    (idealAction i P).app X (x ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X] y) =
      (i.app X y) • x := rfl

private lemma idealAction_cokernel_smul_eq_zero
    {O : Sheaf J CommRingCat.{w}}
    {I : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
    (i : I ⟶ PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (X : Cᵒᵖ) (x : (cokernel (idealAction i P)).obj X) (y : I.obj X) :
    (i.app X y) • x = 0 := by
  obtain ⟨x, rfl⟩ := PresheafOfModules.surjective_of_epi
    (cokernel.π (idealAction i P)) X x
  rw [← map_smul]
  rw [← idealAction_tmul i P X x y]
  exact congrArg (fun g => g.app X (x ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X] y))
    (cokernel.condition (idealAction i P))

private lemma idealAction_image_smul_eq_zero
    {O : Sheaf J CommRingCat.{w}}
    {I : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
    (i : I ⟶ PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (X : Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X)
    (hr : ∀ (x : P.obj X) (y : I.obj X), r • ((i.app X y) • x) = 0)
    (x : (Abelian.image (idealAction i P)).obj X) : r • x = 0 := by
  apply PresheafOfModules.injective_of_mono (Abelian.image.ι (idealAction i P)) X
  rw [map_smul, map_zero]
  obtain ⟨z, rfl⟩ := PresheafOfModules.surjective_of_epi
    (Abelian.factorThruImage (idealAction i P)) X x
  have hfac := congrArg (fun g => g.app X z) (Abelian.image.fac (idealAction i P))
  change (Abelian.image.ι (idealAction i P)).app X
      ((Abelian.factorThruImage (idealAction i P)).app X z) =
    (idealAction i P).app X z at hfac
  rw [hfac]
  clear hfac
  let φ : P.obj X ⊗[(Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X] I.obj X →ₗ[
      (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X] P.obj X :=
    ModuleCat.Hom.hom ((idealAction i P).app X)
  have key : ∀ t, r • φ t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]
    | tmul x y => exact hr x y
    | add t t' ht ht' => rw [map_add, smul_add, ht, ht', add_zero]
  exact key z

end
private lemma isIso_sheafification_tensorUnit_of_pow_smul_eq_zero
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (hf : IsFlatMap f)
    {I : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj}
    (i : I ⟶ PresheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (hQ : IsIso ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map
        (presheafTensorUnit f (cokernel i))))
    (n : ℕ) (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    (hP : ∀ (X : Cᵒᵖ) (a : Fin n → I.obj X) (x : P.obj X),
      (∏ k, (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X from i.app X (a k))) • x = 0) :
    IsIso ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)).map (presheafTensorUnit f P)) := by
  induction n generalizing P with
  | zero =>
      apply isIso_sheafification_tensorUnit_of_annihilated O i (presheafRingMap f) P _ hQ
      intro X x y
      have hx : x = 0 := by simpa using hP X (fun k => Fin.elim0 k) x
      rw [hx, smul_zero]
  | succ n ih =>
      let μ := idealAction i P
      let S := PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (𝟙 _)
      have hA : IsIso (S.map (presheafTensorUnit f (Abelian.image μ))) := by
        apply ih
        intro X a x
        apply idealAction_image_smul_eq_zero i P X _ _ x
        intro z y
        have h := hP X (Fin.cons y a) z
        rw [Fin.prod_univ_succ] at h
        simp only [Fin.cons_zero, Fin.cons_succ] at h
        rw [mul_comm, mul_smul] at h
        exact h
      have hD : IsIso (S.map (presheafTensorUnit f (cokernel μ))) :=
        isIso_sheafification_tensorUnit_of_annihilated O i (presheafRingMap f)
          (cokernel μ) (idealAction_cokernel_smul_eq_zero i P) hQ
      let E := ShortComplex.mk (Abelian.image.ι μ) (cokernel.π μ)
        (kernel.condition (cokernel.π μ))
      have hE : E.ShortExact := { exact := ShortComplex.exact_kernel _ }
      apply (isIso_sheafification_tensorUnit_iff f P).mpr
      exact isIso_tensorUnitMap_of_shortExact f hf
        (S.map (Abelian.image.ι μ)) (S.map (cokernel.π μ)) (E.map S).zero
        (hE.map_of_exact S)
        ((isIso_sheafification_tensorUnit_iff f (Abelian.image μ)).mp hA)
        ((isIso_sheafification_tensorUnit_iff f (cokernel μ)).mp hD)

/-- **Stacks Project, Tag 0GLY.** If a flat map of ring sheaves is an
isomorphism modulo an ideal `I`, then extension of scalars is an isomorphism on
every module annihilated by a power of `I`. -/
@[stacks 0GLY]
lemma isIso_tensorUnitMap_of_pow_smul_eq_zero
    {O O' : Sheaf J CommRingCat.{w}} (f : O ⟶ O')
    (hf : IsFlatMap f)
    {I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (i : I ⟶ RingModule O) [Mono i]
    (hquot : ∃ q : cokernel i ⟶
        cokernel (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
            (RestrictedRingModule f)).map i),
      IsIso q ∧ cokernel.π i ≫ q = (tensorUnitMap f (RingModule O)).val ≫
        cokernel.π (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj
            (RestrictedRingModule f)).map i))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : ∃ n : ℕ, ∀ (X : Cᵒᵖ) (a : Fin n → I.val.obj X) (x : F.val.obj X),
      ((F.val.obj X).smul
        (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X from
          (Finset.univ.prod (fun k ↦ show O.obj.obj X from (i.val.app X) (a k)) :
            O.obj.obj X))).hom x = 0) :
    IsIso (tensorUnitMap f F).val := by
  obtain ⟨n, hn⟩ := hF
  apply (isIso_tensorUnitMap_iff_sheafification_map f F).mpr
  exact isIso_sheafification_tensorUnit_of_pow_smul_eq_zero f hf i.val
    (isIso_sheafification_presheafCokernel_tensorUnit f i
      (isIso_tensorUnitMap_cokernel_of_quotient_iso f hf i hquot)) n F.val hn

end Stacks.Sheaves.FlatNeighbourhood

end
