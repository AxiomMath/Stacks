module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageExact
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SurjectiveMorphismStalkDescent

/-!
# The level zero of the torsion-free model commutes with inverse image

For a morphism `f : X ⟶ Y` of a big étale site, an ℓ-adic sheaf `G` on `Y` and `N : ℕ`, the
level zero `ℓᴺ (f⁻¹G)_N` of the torsion-free model of `f⁻¹ G` is the inverse image of the level
zero `ℓᴺ G_N` of the torsion-free model of `G`. On underlying abelian sheaves both are the image
of multiplication by `ℓᴺ` on `f⁻¹ G_N`. Inverse image is exact, so it preserves images. It
commutes with forgetting the module structure
(`CategoryTheory.Functor.sheafPullbackSheafComposeIso`, the comma categories of small étale base
change being filtered).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.levelPullbackForgetIso`: inverse image commutes with
  forgetting the `ℤ/ℓⁿ⁺¹`-module structure.
* `Stacks.EtaleCohomology.LAdicSheaf.torsionFreeModelInverseImageLevelZeroIso`:
  `(ℓᴺ f⁻¹G)₀ ≅ f⁻¹ (ℓᴺ G)₀`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {ℓ : ℕ}

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

attribute [local instance] underlyingLevelFunctor_additive
  underlyingLevelFunctor_preservesMonomorphisms underlyingLevelFunctor_isLeftAdjoint
  underlyingLevelFunctor_preservesKernels underlyingLevelFunctor_full

variable [Fact ℓ.Prime]

namespace LAdicSheaf

variable {X Y : B.Scheme} (f : X ⟶ Y)

/-- **Inverse image commutes with forgetting the `ℤ/ℓⁿ⁺¹`-module structure.** -/
def levelPullbackForgetIso (n : ℕ) (S : FiniteLevelSheaf.{u, u + 1} B Y ℓ n) :
    (underlyingLevelFunctor B X ℓ n).obj
        ((SmallEtale.LAdicSheaf.levelPullback (ℓ := ℓ) f n).obj S) ≅
      (smallEtaleAbelianPullbackFunctor B f).obj ((underlyingLevelFunctor B Y ℓ n).obj S) := by
  let Φ := smallEtaleBaseChange B f
  let _ : ∀ P : (SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      Φ.op.HasPointwiseLeftKanExtension P := fun _ Z => by
    let _ := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow Φ.op Z) AddCommGrpCat.{u + 1}
    infer_instance
  let _ : ∀ P : (SmallEtale B Y.obj Y.property)ᵒᵖ ⥤ ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))),
      Φ.op.HasPointwiseLeftKanExtension P := fun _ Z => by
    let _ := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow Φ.op Z) (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    infer_instance
  let _ : (SmallEtale.topology B X.obj X.property).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}) :=
    ModuleSheaf.preservesSheafification_forget₂.{u + 1} _ _
  exact (Φ.sheafPullbackSheafComposeIso (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    (forget₂ (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) AddCommGrpCat.{u + 1}) S).symm

/-- The image of a morphism factored as an epimorphism followed by a monomorphism is the middle
object. -/
def abelianImageIsoOfFac {C : Type*} [Category* C] [Abelian C] {A B I : C} (g : A ⟶ B)
    (e : A ⟶ I) (m : I ⟶ B) (he : Epi e) (hm : Mono m) (h : e ≫ m = g) : Abelian.image g ≅ I :=
  haveI : StrongEpi e := strongEpi_of_epi e
  Abelian.imageIsoImage g ≪≫ (image.isoStrongEpiMono e m h).symm

variable [IsNoetherian X.1] [IsNoetherian Y.1]

/-- **`(ℓᴺ f⁻¹G)₀ ≅ f⁻¹ (ℓᴺ G)₀`.** On underlying abelian sheaves both sides are the image of
multiplication by `ℓᴺ` on `f⁻¹ G_N`: inverse image commutes with forgetting the module structure,
and it is exact, so it carries the epi-mono factorisation of `ℓᴺ` on `G_N` to one on `f⁻¹ G_N`. -/
def torsionFreeModelInverseImageLevelZeroIso (G : LAdicSheaf.{u, u + 1} B Y ℓ) (N : ℕ) :
    (torsionFreeModel (SmallEtale.LAdicSheaf.inverseImage f G) N).level 0 ≅
      (SmallEtale.LAdicSheaf.inverseImage f (torsionFreeModel G N)).level 0 := by
  let A := (underlyingLevelFunctor B Y ℓ (N + 0)).obj (G.level (N + 0))
  let c := levelPullbackForgetIso f (N + 0) (G.level (N + 0))
  let P := smallEtaleAbelianPullbackFunctor B f
  let g := (ℓ ^ N) • 𝟙 A
  have : PreservesFiniteLimits P :=
    preservesFiniteLimits_smallEtaleSheafPullback_addCommGrp.{u + 1, u} B f
  have : PreservesFiniteColimits P :=
    preservesFiniteColimits_smallEtaleSheafPullback_addCommGrp.{u + 1, u} B f
  have : P.Additive := additive_smallEtaleSheafPullback_addCommGrp.{u + 1, u} B f
  have he : Epi (c.hom ≫ P.map (Abelian.factorThruImage g)) := epi_comp _ _
  have hm : Mono (P.map (Abelian.image.ι g) ≫ c.inv) := mono_comp _ _
  have hfac : (c.hom ≫ P.map (Abelian.factorThruImage g)) ≫ (P.map (Abelian.image.ι g) ≫ c.inv) =
      (ℓ ^ N) •
        𝟙 (underlyingLAdicLevel B X ℓ (SmallEtale.LAdicSheaf.inverseImage f G) (N + 0)) := by
    rw [Category.assoc, ← Category.assoc (P.map _), ← P.map_comp, Abelian.image.fac,
      Functor.map_nsmul, CategoryTheory.Functor.map_id, Preadditive.nsmul_comp,
      Category.id_comp, Preadditive.comp_nsmul, Iso.hom_inv_id]
    rfl
  exact (underlyingLevelFunctor B X ℓ 0).preimageIso
    (torsionFreeModelLevelIso (SmallEtale.LAdicSheaf.inverseImage f G) N 0 ≪≫
      abelianImageIsoOfFac _ _ _ he hm hfac ≪≫
      P.mapIso (torsionFreeModelLevelIso G N 0).symm ≪≫
      (levelPullbackForgetIso f 0 (torsionFreeModelLevel G N 0)).symm)

end LAdicSheaf

end Stacks.EtaleCohomology
