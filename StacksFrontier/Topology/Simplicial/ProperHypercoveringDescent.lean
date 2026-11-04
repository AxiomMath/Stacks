module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.FiniteLimits
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismProperty
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact
public import StacksFrontier.Topology.Maps.Proper
public import StacksFrontier.Topology.Simplicial.Augmentation

/-!
# Proper hypercoverings of locally compact spaces and cartesian sheaves

Let `U` be a simplicial object of the category `LC` of Hausdorff locally quasi-compact spaces
and let `a : U ⟶ X` be an augmentation. This file sets up the objects in terms of which
Stacks 0DAG is stated: proper surjections, the inverse and direct images of sheaves of sets and
of abelian sheaves along the morphism of topoi `a : Sh(U_Zar) ⟶ Sh(X)` of Tag 09W4, and
cartesian sheaves on `U_Zar`. It proves the inclusion of Stacks 0DAG which needs no hypothesis on
the augmentation: every sheaf in the essential image of `a^{-1}` is cartesian.

## Main definitions

* `Stacks.Topology.Simplicial.ProperHypercovering.properSurjective`: the morphism property
  of proper surjections of locally quasi-compact Hausdorff spaces.
* `Stacks.Topology.Simplicial.ProperHypercovering.cartesianTransition` and
  `.IsCartesian`, `.IsCartesianAb`: the canonical inverse-image transitions of a sheaf on
  the simplicial-open site, and cartesianness as their invertibility.

## Main results

* `Stacks.Topology.Simplicial.ProperHypercovering.isCartesian_inverseImage` and
  `.isCartesian_of_mem_essImage`, with their abelian counterparts: every sheaf in the
  essential image of `a^{-1}` is cartesian.

## Implementation notes

Cartesianness on `U_Zar` is expressed by the invertibility of the adjoint of every
transition map of the sheaf system of Tag 09VM, which is the description of cartesian
sheaves on the simplicial-open site. For an abelian sheaf it is cartesianness of the
underlying sheaf of sets, exactly as in Tag 07TF.

The abelian inverse and direct images are the canonical ones attached to the morphism of
topoi of Tag 09W4, namely `CategoryTheory.Sites.abelianInverseImage` and
`Stacks.Topos.AbelianPushforward.abelianPushforward`.

Stacks 0DAG itself is
`Stacks.Topology.Simplicial.ProperHypercovering.inverseImage_fullyFaithful_of_isHypercovering`
and its abelian counterpart, in
`StacksFrontier/Topology/Simplicial/ProperHypercoveringFullyFaithful.lean`.

## References

* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u


namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.Simplicial

/-- A proper surjection of Hausdorff locally quasi-compact spaces. -/
def properSurjective : MorphismProperty LocallyQuasiCompactHausdorff.{u} :=
  fun _ _ f => StacksDraft.Topology.IsProperMap.{u, u, u} (f : _ → _) ∧
    Function.Surjective (f : _ → _)

variable (Y : SimplicialObject LocallyQuasiCompactHausdorff.{u})
  (X : LocallyQuasiCompactHausdorff.{u})
  (a : Y ⟶ (SimplicialObject.const LocallyQuasiCompactHausdorff).obj X)

/-- The underlying simplicial topological space of a simplicial locally quasi-compact
Hausdorff space. -/
abbrev U : SimplicialObject TopCat.{u} := Y ⋙ locallyQuasiCompactHausdorffToTop

/-- The underlying augmentation of topological spaces. -/
abbrev topologicalAugmentation :
    U Y ⟶ (SimplicialObject.const TopCat).obj (locallyQuasiCompactHausdorffToTop.obj X) :=
  Functor.whiskerRight a locallyQuasiCompactHausdorffToTop

/-- The morphism of topoi `a : Sh(U_Zar) ⟶ Sh(X)` of Tag 09W4 attached to the
augmentation. -/
abbrev augmentationTopoi :
    MorphismOfTopoi (Sheaf (SimplicialOpen.grothendieckTopology (U Y)) (Type u))
      (TopCat.Sheaf (Type u) (locallyQuasiCompactHausdorffToTop.obj X)) :=
  (augmentationMorphism (U Y) (locallyQuasiCompactHausdorffToTop.obj X)
    (topologicalAugmentation Y X a)).toMorphismOfTopoi

/-- Inverse image `a^{-1} : Sh(X) ⥤ Sh(U_Zar)` of sheaves of sets. -/
abbrev inverseImage := (augmentationTopoi Y X a).inverseImage

/-- Direct image `a_* : Sh(U_Zar) ⥤ Sh(X)` of sheaves of sets. -/
abbrev directImage := (augmentationTopoi Y X a).pushforward

/-- Inverse image `a^{-1} : Ab(X) ⥤ Ab(U_Zar)` of sheaves of abelian groups. -/
abbrev abelianInverseImage := Sites.abelianInverseImage (augmentationTopoi Y X a)

/-- Direct image `a_* : Ab(U_Zar) ⥤ Ab(X)` of sheaves of abelian groups. -/
abbrev abelianDirectImage :=
  Stacks.Topos.AbelianPushforward.abelianPushforward
    (SimplicialOpen.grothendieckTopology (U Y)) (augmentationTopoi Y X a)

/-- The adjunction `a^{-1} ⊣ a_*` on sheaves of abelian groups. -/
abbrev abelianAdjunction : abelianInverseImage Y X a ⊣ abelianDirectImage Y X a :=
  Stacks.Topos.AbelianPushforward.abelianInverseImageAdjPushforward
    (SimplicialOpen.grothendieckTopology (U Y)) (augmentationTopoi Y X a)

section Cartesian

open Stacks.Topology.Simplicial.Augmentation

variable (Z : SimplicialObject TopCat.{u})

/-- The transition map of a simplicial sheaf system, read as a map out of a pullback: the
adjoint of `Stacks.Topology.Simplicial.Augmentation.systemTransition`. -/
def systemCartesianTransition (S : SimplicialSheafSystem Z (Type u))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (pb (Z.map φ)).obj (S.component m) ⟶ S.component n :=
  ((adj (Z.map φ)).homEquiv _ _).symm (systemTransition Z S φ)

/-- A morphism of simplicial sheaf systems commutes with the direct-image form of the
transition maps. -/
lemma systemTransition_naturality {S T : SimplicialSheafSystem Z (Type u)} (σ : S ⟶ T)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    systemTransition Z S φ ≫ (pf (Z.map φ)).map (σ.componentHom n) =
      σ.componentHom m ≫ systemTransition Z T φ :=
  Sheaf.hom_ext (NatTrans.ext (funext fun V => σ.naturality φ V))

/-- A morphism of simplicial sheaf systems commutes with the inverse-image form of the
transition maps. -/
lemma systemCartesianTransition_naturality {S T : SimplicialSheafSystem Z (Type u)}
    (σ : S ⟶ T) {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (pb (Z.map φ)).map (σ.componentHom m) ≫ systemCartesianTransition Z T φ =
      systemCartesianTransition Z S φ ≫ σ.componentHom n := by
  rw [systemCartesianTransition, systemCartesianTransition,
    ← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    systemTransition_naturality]

/-- The components of an isomorphism of simplicial sheaf systems are isomorphisms. -/
instance isIso_componentHom {S T : SimplicialSheafSystem Z (Type u)} (σ : S ≅ T)
    (n : SimplexCategoryᵒᵖ) : IsIso (σ.hom.componentHom n) :=
  ⟨σ.inv.componentHom n,
    congrArg (fun t : S ⟶ S => t.componentHom n) σ.hom_inv_id,
    congrArg (fun t : T ⟶ T => t.componentHom n) σ.inv_hom_id⟩

/-- Invertibility of the inverse-image transitions only depends on the isomorphism class of
the system. -/
lemma isIso_systemCartesianTransition_of_iso {S T : SimplicialSheafSystem Z (Type u)}
    (σ : S ≅ T) {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (h : IsIso (systemCartesianTransition Z T φ)) :
    IsIso (systemCartesianTransition Z S φ) := by
  have heq : systemCartesianTransition Z S φ =
      (pb (Z.map φ)).map (σ.hom.componentHom m) ≫ systemCartesianTransition Z T φ ≫
        inv (σ.hom.componentHom n) := by
    rw [← Category.assoc, systemCartesianTransition_naturality, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

/-- The canonical inverse-image transition of a sheaf of sets on the simplicial-open site of
a simplicial topological space: the adjoint of the transition map of the associated sheaf
system of Tag 09VM. -/
def cartesianTransition (G : Sheaf (SimplicialOpen.grothendieckTopology Z) (Type u))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (TopCat.Sheaf.pullback (Type u) (Z.map φ)).obj (componentSheaf Z G m) ⟶
      componentSheaf Z G n :=
  systemCartesianTransition Z
    ((sheafEquivalenceSimplicialSheafSystem Z (Type u)).toEquivalence.functor.obj G) φ

end Cartesian

/-- **Stacks 07TF for the simplicial-open site.** A sheaf of sets on `Z_Zar` is *cartesian*
when all of its canonical inverse-image transitions are isomorphisms. -/
def IsCartesian (Z : SimplicialObject TopCat.{u})
    (G : Sheaf (SimplicialOpen.grothendieckTopology Z) (Type u)) : Prop :=
  ∀ ⦃n m : SimplexCategoryᵒᵖ⦄ (φ : n ⟶ m), IsIso (cartesianTransition Z G φ)

section InverseImageCartesian

open Stacks.Topology.Simplicial.Augmentation

/-- Two pullbacks in succession and the pullback along the composite are both left adjoint
to the same direct image, so the adjoint of the canonical comparison between them is an
isomorphism. -/
lemma isIso_homEquiv_symm_pullTransition {B C W : TopCat.{u}}
    (f : B ⟶ C) (b : B ⟶ W) (c : C ⟶ W) (h : f ≫ c = b) (F : sh W) :
    IsIso (((adj f).homEquiv _ _).symm (pullTransition f b c h F)) := by
  subst h
  have key : ((adj f).homEquiv _ _).symm (pullTransition f (f ≫ c) c rfl F) =
      (Adjunction.leftAdjointUniq ((adj c).comp (adj f))
        (show pb (f ≫ c) ⊣ pf f ⋙ pf c from adj (f ≫ c))).hom.app F := by
    apply (((adj c).comp (adj f)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [Adjunction.comp_homEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [pullTransition, Equiv.apply_symm_apply]
    exact Category.comp_id _
  rw [key]
  infer_instance

/-- The inverse-image transitions of a system of degreewise pullbacks along an augmentation
are isomorphisms. -/
lemma isIso_systemCartesianTransition_pullbackSystem (Z : SimplicialObject TopCat.{u})
    (W : TopCat.{u}) (α : Z ⟶ (SimplicialObject.const TopCat).obj W) (F : sh W)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    IsIso (systemCartesianTransition Z (pullbackSystem Z W α F) φ) :=
  isIso_homEquiv_symm_pullTransition (Z.map φ) (α.app n) (α.app m)
    (augmentation_w Z W α φ) F

/-- Cartesianness only depends on the isomorphism class of the sheaf. -/
lemma isCartesian_of_iso (Z : SimplicialObject TopCat.{u})
    {G G' : Sheaf (SimplicialOpen.grothendieckTopology Z) (Type u)} (e : G ≅ G')
    (h : IsCartesian Z G') : IsCartesian Z G := by
  intro n m φ
  exact isIso_systemCartesianTransition_of_iso Z
    ((sheafEquivalenceSimplicialSheafSystem Z (Type u)).toEquivalence.functor.mapIso e) φ (h φ)

/-- **Stacks 09W4 (1).** The inverse image of a sheaf of sets along the augmentation is
cartesian: in degree `n` it is the pullback along `a_n`, and the transition attached to
`φ : [n] ⟶ [m]` is the canonical comparison between `U(φ)^{-1}a_m^{-1}F` and `a_n^{-1}F`. -/
lemma isCartesian_inverseImage (F : TopCat.Sheaf (Type u)
    (locallyQuasiCompactHausdorffToTop.obj X)) :
    IsCartesian (U Y) ((inverseImage Y X a).obj F) := by
  intro n m φ
  exact isIso_systemCartesianTransition_of_iso (U Y)
    ((sheafEquivalenceSimplicialSheafSystem (U Y) (Type u)).toEquivalence.counitIso.app
      ((pullbackSystemFunctor (U Y) (locallyQuasiCompactHausdorffToTop.obj X)
        (topologicalAugmentation Y X a)).obj F)) φ
    (isIso_systemCartesianTransition_pullbackSystem (U Y)
      (locallyQuasiCompactHausdorffToTop.obj X) (topologicalAugmentation Y X a) F φ)

/-- Every sheaf of sets in the essential image of `a^{-1}` is cartesian. This is the
inclusion of Tag 0DAG which needs no hypothesis on the augmentation. -/
lemma isCartesian_of_mem_essImage {G : Sheaf (SimplicialOpen.grothendieckTopology (U Y))
    (Type u)} (hG : (inverseImage Y X a).essImage G) : IsCartesian (U Y) G := by
  obtain ⟨F, ⟨e⟩⟩ := hG
  exact isCartesian_of_iso (U Y) e.symm (isCartesian_inverseImage Y X a F)

end InverseImageCartesian

/-- **Stacks 07TF for the simplicial-open site.** A sheaf of abelian groups on `Z_Zar` is
*cartesian* when its underlying sheaf of sets is. -/
def IsCartesianAb (Z : SimplicialObject TopCat.{u})
    (G : Sheaf (SimplicialOpen.grothendieckTopology Z) AddCommGrpCat.{u}) : Prop :=
  IsCartesian Z ((sheafCompose (SimplicialOpen.grothendieckTopology Z)
    (forget AddCommGrpCat.{u})).obj G)

/-- Cartesianness of an abelian sheaf only depends on its isomorphism class. -/
lemma isCartesianAb_of_iso (Z : SimplicialObject TopCat.{u})
    {G G' : Sheaf (SimplicialOpen.grothendieckTopology Z) AddCommGrpCat.{u}} (e : G ≅ G')
    (h : IsCartesianAb Z G') : IsCartesianAb Z G :=
  isCartesian_of_iso Z ((sheafCompose (SimplicialOpen.grothendieckTopology Z)
    (forget AddCommGrpCat.{u})).mapIso e) h

/-- **Stacks 09W4 (1), abelian coefficients.** The inverse image of a sheaf of abelian
groups along the augmentation is cartesian: the underlying sheaf of sets of `a^{-1}F` is
`a^{-1}` of the underlying sheaf of sets of `F`. -/
lemma isCartesianAb_abelianInverseImage (F : Sheaf (Opens.grothendieckTopology
    (locallyQuasiCompactHausdorffToTop.obj X)) AddCommGrpCat.{u}) :
    IsCartesianAb (U Y) ((abelianInverseImage Y X a).obj F) :=
  isCartesian_inverseImage Y X a
    ((sheafCompose (Opens.grothendieckTopology
      (locallyQuasiCompactHausdorffToTop.obj X)) (forget AddCommGrpCat.{u})).obj F)

/-- Every sheaf of abelian groups in the essential image of `a^{-1}` is cartesian. -/
lemma isCartesianAb_of_mem_essImage {G : Sheaf (SimplicialOpen.grothendieckTopology (U Y))
    AddCommGrpCat.{u}} (hG : (abelianInverseImage Y X a).essImage G) :
    IsCartesianAb (U Y) G := by
  obtain ⟨F, ⟨e⟩⟩ := hG
  exact isCartesianAb_of_iso (U Y) e.symm (isCartesianAb_abelianInverseImage Y X a F)

end Stacks.Topology.Simplicial.ProperHypercovering

end
