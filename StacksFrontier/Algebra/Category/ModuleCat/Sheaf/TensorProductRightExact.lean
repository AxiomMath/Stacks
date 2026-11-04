module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRaisedSymmetry

public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLocallyFree
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensor products of sheaves of modules are right exact, and preserve global presentations

Let `O` be a sheaf of commutative rings on a site `(C, J)` and let `R` be the underlying sheaf
of rings.  The tensor product of two sheaves of `R`-modules is the sheafification of the
objectwise tensor product of the underlying presheaves of modules
(`Stacks.SheafOfModules.Tensor.sheafTensor`, Stacks 0GMW).  This file proves that
this bifunctor preserves all colimits in each variable, and deduces the statement about global
presentations: if `F` and `G` are each a cokernel of a map between coproducts of copies of the
structure sheaf (Stacks 03DE(6)), then so is `F ⊗ G`.

The colimit statement is the mathematical engine; the presentation statement is the global
half of the assertion of Stacks 0GNC that a tensor product of quasi-coherent modules is
quasi-coherent.

## Main definitions

* `Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight` and
  `Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft` are the two partial applications
  `F ⊗ -` and `- ⊗ G` of the tensor product of sheaves of modules.
* `Stacks.SheafOfModules.TensorLocalProperties.sheafifyTensorRightIso` and
  `Stacks.SheafOfModules.TensorLocalProperties.sheafifyTensorLeftIso` compare these functors,
  precomposed with sheafification, with the objectwise tensor product followed by
  sheafification.

## Main results

* `CategoryTheory.Limits.preservesZeroMorphisms_of_isIso_counit`: if `L ⊣ ι` with the counit an
  isomorphism, then a functor out of the target of `L` preserves zero morphisms as soon as its
  composite with `L` does.  The colimit version of this is Mathlib's
  `CategoryTheory.Adjunction.preservesColimitsOfSize_iff`, which is used rather than reproved.
* `Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight` and
  `Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafLeft`: the tensor
  product of sheaves of modules preserves colimits in each variable.  In particular it is
  right exact.
* `Stacks.SheafOfModules.TensorLocalProperties.freeModel_isFree`: the sheafification of a
  coproduct of copies of the unit presheaf of modules is a coproduct of copies of the unit
  sheaf of modules.
* `Stacks.SheafOfModules.TensorLocalProperties.exists_isColimitCofan_tensorSheaf`: a tensor
  product of two coproducts of copies of the structure sheaf is a coproduct of copies of the
  structure sheaf, indexed by the product of the two index types.
* `Stacks.SheafOfModules.TensorLocalProperties.exists_presentation_tensorSheaf`: a tensor
  product of two globally presented sheaves of modules is globally presented.

## Implementation notes

Colimit preservation cannot be read off from the definition of the tensor product: the
sheafification functor `L` preserves colimits, being a left adjoint, and the objectwise tensor
product `P ⊗ -` on presheaves of modules preserves colimits, but the forgetful functor from
sheaves to presheaves that sits between them does not.  What repairs this is Stacks 0GMW:
`_root_.PresheafOfModules.sheafificationTensorIso` identifies `L P ⊗ L Q` with
`L (P ⊗ Q)`, so `L ⋙ (F ⊗ -)` is isomorphic to `(F.val ⊗ -) ⋙ L`, which does preserve
colimits.  `CategoryTheory.Adjunction.preservesColimitsOfSize_iff` then transfers that back
to `F ⊗ -` itself, using that the right adjoint of sheafification is fully faithful, i.e. that
sheaves of modules form a reflective subcategory of presheaves of modules.

The passage from presentations of `F` and of `G` to a presentation of `F ⊗ G` uses right
exactness twice.  Writing `F = coker (aF : QF ⟶ PF)` and `G = coker (aG : QG ⟶ PG)`, the map
`PF ⊗ PG ⟶ PF ⊗ G` is a cokernel of `PF ⊗ QG ⟶ PF ⊗ PG` and the map `PF ⊗ G ⟶ F ⊗ G` is a
cokernel of `QF ⊗ G ⟶ PF ⊗ G`; the two are composed by
`CategoryTheory.Limits.isColimitCokernelCoforkCompOfLift`, whose lifting hypothesis is
discharged here by `aF ⊗ 𝟙`, both composites in question being `aF ⊗ aG`.  This is the step
that the analogous argument for a cokernel of a single morphism cannot perform, since there a
lift of the generators of the source along the presentation of the target is extra
information.

The module universe and the universe of the structure sheaf agree throughout, because that is
the generality in which `Stacks.SheafOfModules.Tensor.sheafTensor` and the
monoidal structure on presheaves of modules are available.  Consequently the conclusion is
stated as an explicit cokernel-of-coproducts datum rather than as
`SheafOfModules.HasGlobalPresentation`, which asks for that datum after the universe lift
`SheafOfModules.uliftForPresentation`.

**Relation to the other tensor products of sheaves of modules in this library.**  There are
three parallel constructions of the sheafified tensor product here, none of them bridged to the
others: `Stacks.SheafOfModules.Tensor.sheafTensor` of
`StacksFrontier.CategoryTheory.Sites.Modules.Tensor`, which is the one used by this file and by
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isLocallyFreeOnSite`;
`Stacks.SheafOfModules.Tensor.sheafTensor` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor`, which keeps the module and
ring universes independent; and `Stacks.SheafOfModules.Tensor.sheafTensor` of
  `StacksDraft.Ch17.Sec16.Tag05NA`.
For the third of these both statements proved here are already available in stronger or
different form: colimit preservation is
`Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits` (Stacks 05NB, at
independent universes) and the tensored presentation is
`Stacks.SheafOfModules.TensorPresentations.exact_tensorSheaf_presentations_on_site`, stated as
exactness of a three-term complex and so requiring that the category of sheaves of modules be
abelian.  Neither transfers to `Stacks.SheafOfModules.Tensor.sheafTensor` without a comparison
isomorphism between
the constructions, which does not exist yet; and the cofan-and-cofork form proved here, unlike
the exactness form, needs no abelian structure, which is what the global-presentation predicate
`SheafOfModules.HasGlobalPresentation` is phrased to avoid.

## References

* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules

universe u v w

namespace CategoryTheory.Limits

/-- Let `L ⊣ ι` be an adjunction whose counit is an isomorphism.  A functor out of the target
of `L` preserves zero morphisms as soon as `L` and the composite `L ⋙ Φ` do: every morphism in
the target is conjugate, by the counit, to the image under `L` of a morphism upstairs.

This is the zero-morphism companion of Mathlib's
`CategoryTheory.Adjunction.preservesColimitsOfSize_iff`. -/
lemma preservesZeroMorphisms_of_isIso_counit
    {A B D : Type*} [Category A] [Category B] [Category D]
    [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms D]
    {L : A ⥤ B} {ι : B ⥤ A} (adj : L ⊣ ι) [IsIso adj.counit]
    (Φ : B ⥤ D) [L.PreservesZeroMorphisms] [(L ⋙ Φ).PreservesZeroMorphisms] :
    Φ.PreservesZeroMorphisms where
  map_zero X Y := by
    have h1 : (0 : X ⟶ Y) =
        (asIso (adj.counit.app X)).inv ≫ L.map (0 : ι.obj X ⟶ ι.obj Y) ≫
          (asIso (adj.counit.app Y)).hom := by
      rw [L.map_zero]; simp
    have h2 : Φ.map (L.map (0 : ι.obj X ⟶ ι.obj Y)) = 0 := (L ⋙ Φ).map_zero _ _
    rw [h1, Φ.map_comp, Φ.map_comp, h2, zero_comp, comp_zero]

end CategoryTheory.Limits

namespace Stacks.SheafOfModules.TensorLocalProperties

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The identity of a sheaf of commutative rings is a locally injective map to its own
associated sheaf of rings. -/
instance isLocallyInjective_associatedRingMap_id (O : Sheaf J CommRingCat.{w}) :
    Presheaf.IsLocallyInjective J (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj)) := by
  change Presheaf.IsLocallyInjective J (𝟙 (O.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

/-- The identity of a sheaf of commutative rings is a locally surjective map to its own
associated sheaf of rings. -/
instance isLocallySurjective_associatedRingMap_id (O : Sheaf J CommRingCat.{w}) :
    Presheaf.IsLocallySurjective J (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj)) := by
  change Presheaf.IsLocallySurjective J (𝟙 (O.obj ⋙ forget₂ CommRingCat RingCat))
  infer_instance

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The sheafification of a coproduct of `B` copies of the unit presheaf of modules is a
coproduct of `B` copies of the unit sheaf of modules: the sheafification unit is locally
bijective, and a coproduct of copies of the unit is carried across a locally bijective map into
a sheaf. -/
theorem freeModel_isFree (R : Sheaf J RingCat.{w}) (B : Type w) :
    ∃ ι : B → (SheafOfModules.unit R ⟶ freeModel R B),
      Nonempty (IsColimit (Cofan.mk (freeModel R B) ι)) := by
  have hi : PresheafOfModules.IsLocallyInjective J
      (sheafificationUnit (R := R) (∐ fun _ : B => PresheafOfModules.unit R.obj)) :=
    inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J
      (∐ fun _ : B => PresheafOfModules.unit R.obj).presheaf))
  have hs : PresheafOfModules.IsLocallySurjective J
      (sheafificationUnit (R := R) (∐ fun _ : B => PresheafOfModules.unit R.obj)) :=
    inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J
      (∐ fun _ : B => PresheafOfModules.unit R.obj).presheaf))
  exact ⟨_, ⟨isColimit_of_locallyBijective (hinj := hi) (hsurj := hs)
    (M := freeModel R B)
    (fun b => Sigma.ι (fun _ : B => PresheafOfModules.unit R.obj) b)
    (coproductIsCoproduct _) (sheafificationUnit _)⟩⟩

variable (J) (O : Sheaf J CommRingCat.{w})

/-- Sheafification of presheaves of modules along the identity of the structure sheaf is a left
adjoint, so it preserves colimits and zero morphisms. -/
noncomputable instance isLeftAdjoint_moduleSheafification :
    (_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).IsLeftAdjoint :=
  ⟨_, ⟨PresheafOfModules.sheafificationAdjunction.{w, v, w, u}
    (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj))⟩⟩

/-- The tensor product `F ⊗ -` of sheaves of modules with a fixed left factor. -/
@[ega "0 4.1.5" "partial"]
noncomputable def tensorSheafRight (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
    O)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj F

/-- The tensor product `- ⊗ G` of sheaves of modules with a fixed right factor. -/
@[ega "0 4.1.5" "partial"]
noncomputable def tensorSheafLeft (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
    O)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).flip.obj G

/-- Tensoring with a sheaf `F` presented as the associated sheaf of a presheaf of modules `P`,
after sheafification, is the objectwise tensor product with `P` followed by sheafification.
This is the form in which Stacks 0GMW makes the tensor product of sheaves of modules a functor
that preserves colimits. -/
noncomputable def sheafifyTensorRightIso
    (P : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    {F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (ε : (_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj P ≅ F) :
    _root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj) ⋙ tensorSheafRight J O F ≅
      tensorLeft P ⋙ _root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj) :=
  NatIso.ofComponents
    (fun Q => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).mapIso ε.symm).app
        ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj Q) ≪≫
      (_root_.PresheafOfModules.sheafificationTensorIso J (𝟙 O.obj)).app (P, Q))
    (fun {Q Q'} f => by
      have hnat := (_root_.PresheafOfModules.sheafificationTensorIso J (𝟙 O.obj)).hom.naturality
        (show ((P, Q) : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ×
            PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) ⟶ (P, Q') from
          (𝟙 P, f))
      change (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map
          ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map (𝟙 P))).app _ ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj
              ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj P)).map
                ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map f)) ≫ _ =
        _ ≫ (_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map
          (((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O.obj).map (𝟙 P)).app Q ≫
            ((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O.obj).obj P).map f) at hnat
      rw [(_root_.PresheafOfModules.moduleSheafification.{v, u, w, w} J (𝟙 O.obj)).map_id P,
        (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O.obj).map_id P, NatTrans.id_app,
        Category.id_comp] at hnat
      have hnat' := (congrArg (· ≫
          (_root_.PresheafOfModules.sheafificationTensorIso J (𝟙 O.obj)).hom.app (P, Q'))
        ((congrArg (fun φ => NatTrans.app φ
            ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj Q) ≫
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj
                ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj P)).map
                  ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map f))
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map_id
            ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj P))).trans
          (Category.id_comp _))).symm.trans hnat
      change ((Stacks.SheafOfModules.Tensor.sheafTensor O).obj F).map
          ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map f) ≫
            (((Stacks.SheafOfModules.Tensor.sheafTensor O).map ε.inv).app _ ≫ _) =
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).map ε.inv).app _ ≫ _) ≫ _
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _)
          (((Stacks.SheafOfModules.Tensor.sheafTensor O).map ε.inv).naturality
            ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map f))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor O).map ε.inv).app _ ≫ ·)
            hnat').trans (Category.assoc _ _ _).symm))))

/-- The mirror image of `sheafifyTensorRightIso` for a fixed right factor. -/
noncomputable def sheafifyTensorLeftIso
    (P : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}))
    {G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (ε : (_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj P ≅ G) :
    _root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj) ⋙ tensorSheafLeft J O G ≅
      tensorRight P ⋙ _root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj) :=
  NatIso.ofComponents
    (fun Q => ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj
        ((_root_.PresheafOfModules.moduleSheafification J (𝟙
        O.obj)).obj Q)).mapIso ε.symm ≪≫
      (_root_.PresheafOfModules.sheafificationTensorIso J (𝟙 O.obj)).app (Q, P))
    (fun {Q Q'} f => by
      have hnat := (_root_.PresheafOfModules.sheafificationTensorIso J (𝟙 O.obj)).hom.naturality
        (show ((Q, P) : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ×
            PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) ⟶ (Q', P) from
          (f, 𝟙 P))
      change (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map
          ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map f)).app _ ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj
              ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj Q')).map
                ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map (𝟙 P))) ≫ _ =
        _ ≫ (_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map
          (((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O.obj).map f).app P ≫
            ((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O.obj).obj Q').map (𝟙 P)) at hnat
      rw [(_root_.PresheafOfModules.moduleSheafification.{v, u, w, w} J (𝟙 O.obj)).map_id P,
        ((PresheafOfModules.tensorBifunctor.{v, u, w, w, w} O.obj).obj Q').map_id P,
        Category.comp_id] at hnat
      have hnat' := (congrArg (· ≫
          (_root_.PresheafOfModules.sheafificationTensorIso J (𝟙 O.obj)).hom.app (Q', P))
        ((congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map
            ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map f)).app
              ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj P) ≫ ·)
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj
            ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj Q')).map_id
              ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj P))).trans
          (Category.comp_id _))).symm.trans hnat
      change ((Stacks.SheafOfModules.Tensor.sheafTensor O).map
          ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map f)).app G ≫
            (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj _).map ε.inv ≫ _) =
        (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj _).map ε.inv ≫ _) ≫ _
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _)
          (((Stacks.SheafOfModules.Tensor.sheafTensor O).map
            ((_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map f)).naturality
              ε.inv).symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj _).map ε.inv ≫ ·)
            hnat').trans (Category.assoc _ _ _).symm))))

/-- The sheafification unit of a module sheaf, read as an isomorphism from the sheafification
of its underlying presheaf of modules. -/
noncomputable def counitIsoOfSheaf
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj)).obj
      ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        PresheafOfModules.restrictScalars (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj))).obj F) ≅
            F :=
  (asIso (PresheafOfModules.sheafificationAdjunction.{w, v, w, u}
    (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj))).counit).app F

/-- **The tensor product of sheaves of modules is right exact in its second variable**, and
indeed preserves all colimits there. -/
@[ega "0 4.1.5" "partial, tensor product"]
noncomputable instance preservesColimits_tensorSheafRight
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesColimitsOfSize.{w, w} (tensorSheafRight J O F) :=
  Stacks.SheafOfModules.TensorColimits.tensorLeft_preservesColimits J O F

/-- **The tensor product of sheaves of modules is right exact in its first variable**, and
indeed preserves all colimits there. -/
@[ega "0 4.1.5" "partial, tensor product"]
noncomputable instance preservesColimits_tensorSheafLeft
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesColimitsOfSize.{w, w} (tensorSheafLeft J O G) :=
  Stacks.SheafOfModules.TensorRaised.tensorRightRaised_preservesColimits.{u, v, w, w} O G

/-- The objectwise tensor product with a presheaf of modules preserves zero morphisms. -/
noncomputable instance preservesZeroMorphisms_tensorLeft
    (P : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    (tensorLeft P).PreservesZeroMorphisms := by
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
    preservesColimitsOfSize_shrink.{0, w, 0, w} _
  infer_instance

/-- The objectwise tensor product with a presheaf of modules preserves zero morphisms. -/
noncomputable instance preservesZeroMorphisms_tensorRight
    (P : PresheafOfModules.{w} (O.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    (tensorRight P).PreservesZeroMorphisms := by
  have : PreservesColimitsOfSize.{0, 0} (tensorRight P) :=
    preservesColimitsOfSize_shrink.{0, w, 0, w} _
  infer_instance

/-- Tensoring sheaves of modules with a fixed left factor preserves zero morphisms. -/
noncomputable instance preservesZeroMorphisms_tensorSheafRight
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (tensorSheafRight J O F).PreservesZeroMorphisms := by
  have h : (_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj) ⋙ tensorSheafRight J O
      F).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso
      (F₁ := tensorLeft ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
          PresheafOfModules.restrictScalars
            (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj))).obj F) ⋙
        _root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj))
      (sheafifyTensorRightIso J O _ (counitIsoOfSheaf J O F)).symm
  exact preservesZeroMorphisms_of_isIso_counit
    (PresheafOfModules.sheafificationAdjunction.{w, v, w, u}
    (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj))) _

/-- Tensoring sheaves of modules with a fixed right factor preserves zero morphisms. -/
noncomputable instance preservesZeroMorphisms_tensorSheafLeft
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (tensorSheafLeft J O G).PreservesZeroMorphisms := by
  have h : (_root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj) ⋙ tensorSheafLeft J O
      G).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_iso
      (F₁ := tensorRight ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
          PresheafOfModules.restrictScalars
            (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj))).obj G) ⋙
        _root_.PresheafOfModules.moduleSheafification J (𝟙 O.obj))
      (sheafifyTensorLeftIso J O _ (counitIsoOfSheaf J O G)).symm
  exact preservesZeroMorphisms_of_isIso_counit
    (PresheafOfModules.sheafificationAdjunction.{w, v, w, u}
    (CategoryTheory.Sheaf.toRingCatMap J (𝟙 O.obj))) _

/-- Tensoring with a fixed left factor preserves the colimit of a parallel pair, which is the
shape of a cokernel. -/
noncomputable instance preservesColimit_parallelPair_tensorSheafRight
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {X Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) (tensorSheafRight J O F) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorSheafRight J O F) :=
    preservesColimitsOfSize_shrink.{0, w, 0, w} _
  infer_instance

/-- Tensoring with a fixed right factor preserves the colimit of a parallel pair, which is the
shape of a cokernel. -/
noncomputable instance preservesColimit_parallelPair_tensorSheafLeft
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {X Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (f g : X ⟶ Y) :
    PreservesColimit (parallelPair f g) (tensorSheafLeft J O G) := by
  have : PreservesColimitsOfSize.{0, 0} (tensorSheafLeft J O G) :=
    preservesColimitsOfSize_shrink.{0, w, 0, w} _
  infer_instance

/-- The tensor product of two coproducts of copies of the structure sheaf is a coproduct of
copies of the structure sheaf, indexed by the product of the two index types. -/
theorem exists_isColimitCofan_tensorSheaf {I K : Type w}
    {X Y : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {ι : I → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶ X)}
    {κ : K → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶ Y)}
    (hX : IsColimit (Cofan.mk X ι)) (hY : IsColimit (Cofan.mk Y κ)) :
    ∃ μ : I × K → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj X).obj Y),
      Nonempty (IsColimit (Cofan.mk (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          O).obj X).obj Y) μ))
          := by
  obtain ⟨ιI, hI⟩ := freeModel_isFree (Stacks.SheafOfModules.Tensor.ringSheaf O) I
  obtain ⟨κK, hK⟩ := freeModel_isFree (Stacks.SheafOfModules.Tensor.ringSheaf O) K
  obtain ⟨μ0, hμ0⟩ := freeModel_isFree (Stacks.SheafOfModules.Tensor.ringSheaf O) (I × K)
  let e : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj X).obj Y ≅
      freeModel (Stacks.SheafOfModules.Tensor.ringSheaf O) (I × K) :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).mapIso
        (hX.coconePointUniqueUpToIso hI.some)).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj _).mapIso
        (hY.coconePointUniqueUpToIso hK.some)) ≪≫
      freeModel_tensorIso O I K
  exact ⟨fun p => μ0 p ≫ e.inv, ⟨hμ0.some.ofIsoColimit (Cofan.ext e.symm (fun b => rfl))⟩⟩

/-- **Tensor products of globally presented sheaves of modules.**  If `F` and `G` are each the
cokernel of a map between coproducts of copies of the structure sheaf, in the sense of
Stacks 03DE(6), then so is their tensor product: it is the cokernel of a map
`(PF ⊗ QG) ⊞ (QF ⊗ PG) ⟶ PF ⊗ PG`, with index types `IF × IG` and `(IF × KG) ⊕ (KF × IG)`. -/
theorem exists_presentation_tensorSheaf
    {F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {IF KF IG KG : Type w}
    {PF QF PG QG : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    {ιF : IF → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶ PF)}
    {κF : KF → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶ QF)}
    {ιG : IG → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶ PG)}
    {κG : KG → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶ QG)}
    (hPF : IsColimit (Cofan.mk PF ιF)) (hQF : IsColimit (Cofan.mk QF κF))
    (hPG : IsColimit (Cofan.mk PG ιG)) (hQG : IsColimit (Cofan.mk QG κG))
    {aF : QF ⟶ PF} {bF : PF ⟶ F} (habF : aF ≫ bF = 0)
    (hbF : IsColimit (CokernelCofork.ofπ bF habF))
    {aG : QG ⟶ PG} {bG : PG ⟶ G} (habG : aG ≫ bG = 0)
    (hbG : IsColimit (CokernelCofork.ofπ bG habG)) :
    ∃ (I K : Type w) (P Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ι : I → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶ P))
      (κ : K → (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O) ⟶ Q)),
      Nonempty (IsColimit (Cofan.mk P ι)) ∧ Nonempty (IsColimit (Cofan.mk Q κ)) ∧
        ∃ (a : Q ⟶ P) (b : P ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj
            F).obj G)
          (hab : a ≫ b = 0), Nonempty (IsColimit (CokernelCofork.ofπ b hab)) := by
  have hb := isColimitCoforkMapOfIsColimit' (tensorSheafRight J O PF) habG hbG
  have hpi := isColimitCoforkMapOfIsColimit' (tensorSheafLeft J O G) habF hbF
  have hpepi : Epi ((tensorSheafRight J O QF).map bG) :=
    Cofork.IsColimit.epi (isColimitCoforkMapOfIsColimit' (tensorSheafRight J O QF) habG hbG)
  have hl : (tensorSheafLeft J O PG).map aF ≫ (tensorSheafRight J O PF).map bG =
      (tensorSheafRight J O QF).map bG ≫ (tensorSheafLeft J O G).map aF :=
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map aF).naturality
      bG).symm
  have hmain := @isColimitCokernelCoforkCompOfLift _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpepi _ _ _ hb _
    hpi hl
  obtain ⟨μP, hμP⟩ := exists_isColimitCofan_tensorSheaf J O hPF hPG
  obtain ⟨μ1, hμ1⟩ := exists_isColimitCofan_tensorSheaf J O hPF hQG
  obtain ⟨μ2, hμ2⟩ := exists_isColimitCofan_tensorSheaf J O hQF hPG
  exact ⟨IF × IG, (IF × KG) ⊕ (KF × IG), _, _, μP, _, hμP,
    ⟨_root_.SheafOfModules.isColimitCofanSumOfBinaryCofan hμ1.some hμ2.some
      (bc := BinaryCofan.mk coprod.inl coprod.inr) (coprodIsCoprod _ _)⟩, _, _, _, ⟨hmain⟩⟩

end Stacks.SheafOfModules.TensorLocalProperties

end
