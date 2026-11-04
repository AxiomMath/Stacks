module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllCover
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ModuleFiltrationTransport

/-!
# Induction along the filtration of Tag 0A3R

Tag 0A3R gives, for a finite type locally constant sheaf `M` of `F_ℓ`-vector spaces, a finite
filtration of a pullback of `M` with successive quotients `Z/ℓZ`. This file turns such a
filtration (a `RelSeries` of `Stacks.EtaleCohomology.ConstantRankOneStep`) into an induction
principle for the underlying abelian sheaf: every class of abelian sheaves which contains the zero
sheaves and the constant sheaf `Z/ℓZ`, and is closed under isomorphisms and extensions, contains
the abelian sheaf underlying `M`.

## Main results

* `Stacks.EtaleCohomology.forget₂_mem_of_relSeries_constantRankOneStep`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} {X : Scheme.{u}}

/-- The abelian sheaf underlying a sheaf of `F_ℓ`-modules. -/
abbrev forgetZModSheaf (X : Scheme.{u}) (ℓ : ℕ) :
    Sheaf (smallEtaleTopology X) (ModuleCat.{u + 1} (ZMod ℓ)) ⥤
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  sheafCompose (smallEtaleTopology X) (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1})

/-- The forgetful functor from `ZMod ℓ`-modules to abelian groups is a left adjoint. -/
instance isLeftAdjoint_forget₂_zmod :
    (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
  have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod ℓ))).IsLeftAdjoint :=
    ⟨_, ⟨ModuleCat.restrictCoextendScalarsAdj.{u + 1} (Int.castRingHom (ZMod ℓ))⟩⟩
  change (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod ℓ)) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  infer_instance

/-- The forgetful functor from `ZMod ℓ`-modules to abelian groups is a right adjoint. -/
instance isRightAdjoint_forget₂_zmod :
    (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).IsRightAdjoint := by
  have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod ℓ))).IsRightAdjoint :=
    ⟨_, ⟨ModuleCat.extendRestrictScalarsAdj.{u + 1} (Int.castRingHom (ZMod ℓ))⟩⟩
  change (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom (ZMod ℓ)) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsRightAdjoint
  infer_instance

/-- The forgetful functor from `ZMod ℓ`-modules to abelian groups preserves finite limits. -/
instance : PreservesFiniteLimits (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) :=
  inferInstance

/-- Passing to the underlying abelian sheaf preserves finite limits. -/
instance : PreservesFiniteLimits (forgetZModSheaf X ℓ) := by
  have : PreservesFiniteLimits (forgetZModSheaf X ℓ ⋙
      sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) := by
    change PreservesFiniteLimits
      (sheafToPresheaf (smallEtaleTopology X) (ModuleCat.{u + 1} (ZMod ℓ)) ⋙
        (Functor.whiskeringRight X.Etaleᵒᵖ (ModuleCat.{u + 1} (ZMod ℓ))
          AddCommGrpCat.{u + 1}).obj
        (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})

/-- Passing to the underlying abelian sheaf preserves finite colimits. -/
instance : PreservesFiniteColimits (forgetZModSheaf X ℓ) :=
  ⟨fun K _ _ => preservesColimitsOfShape_sheafCompose _ _ K⟩

/-- Passing to the underlying abelian sheaf preserves zero morphisms. -/
instance : (forgetZModSheaf X ℓ).PreservesZeroMorphisms := inferInstance

/-- Passing to the underlying abelian sheaf is an additive functor. -/
instance : (forgetZModSheaf X ℓ).Additive := Functor.additive_of_preserves_binary_products _

/-- A sheaf of `F_ℓ`-modules is killed by `ℓ` as an abelian sheaf. -/
theorem nsmul_id_forgetZModSheaf_eq_zero
    (M : Sheaf (smallEtaleTopology X) (ModuleCat.{u + 1} (ZMod ℓ))) :
    ℓ • 𝟙 ((forgetZModSheaf X ℓ).obj M) = 0 := by
  have key : ∀ (N : ModuleCat.{u + 1} (ZMod ℓ)) (y : N), ℓ • y = 0 := by
    intro N y
    rw [← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_self, zero_smul]
  ext U x
  exact key (M.obj.obj U) x

/-- **Induction along a filtration with quotients `Z/ℓZ`.** Let `S` be a filtration of a sheaf
`M` of `F_ℓ`-modules whose first term is zero, whose last term is `M`, and whose successive
quotients are `Z/ℓZ`. Then every property `P` of abelian sheaves which holds for zero sheaves and
for `Z/ℓZ`, and is stable under isomorphisms and extensions, holds for the abelian sheaf underlying
`M`. -/
theorem forget₂_mem_of_relSeries_constantRankOneStep
    (M : Sheaf (smallEtaleTopology X) (ModuleCat.{u + 1} (ZMod ℓ)))
    (S : RelSeries (ConstantRankOneStep.{u + 1, u} ℓ M))
    (hhead : IsZero (Subobject.underlying.obj S.head)) (hlast : IsIso S.last.arrow)
    (P : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} → Prop)
    (h0 : ∀ H, IsZero H → P H) (hiso : ∀ H H', (H ≅ H') → P H → P H')
    (hext : ∀ T : ShortComplex (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
      T.ShortExact → P T.X₁ → P T.X₃ → P T.X₂)
    (hL : P ((forgetZModSheaf X ℓ).obj (constantZMod.{u + 1, u} ℓ X))) :
    P ((forgetZModSheaf X ℓ).obj M) := by
  have key : ∀ i : Fin (S.length + 1),
      P ((forgetZModSheaf X ℓ).obj (Subobject.underlying.obj (S i))) := by
    intro i
    induction i using Fin.induction with
    | zero => exact h0 _ ((forgetZModSheaf X ℓ).map_isZero hhead)
    | succ i ih =>
      obtain ⟨hle, ⟨e⟩⟩ := S.step i
      let T := ShortComplex.mk ((S i.castSucc).ofLE (S i.succ) hle)
        (cokernel.π ((S i.castSucc).ofLE (S i.succ) hle)) (cokernel.condition _)
      have hT : T.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
      exact hext _ (hT.map_of_exact (forgetZModSheaf X ℓ)) ih
        (hiso _ _ ((forgetZModSheaf X ℓ).mapIso e).symm hL)
  exact hiso _ _ ((forgetZModSheaf X ℓ).mapIso (asIso S.last.arrow)) (key (Fin.last _))

/-- The abelian sheaf underlying the constant sheaf `Z/ℓZ` of `F_ℓ`-modules is the constant
abelian sheaf `Z/ℓZ`. -/
def forgetZModSheafConstantIso (X : Scheme.{u}) (ℓ : ℕ) :
    (forgetZModSheaf X ℓ).obj (constantZMod.{u + 1, u} ℓ X) ≅
      (constantSheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) :=
  (constantCommuteCompose (smallEtaleTopology X)
    (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1})).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))

/-- Pointwise left Kan extensions along `(smallEtaleBaseChange g).op` exist in any category with
colimits of size `u + 1`. -/
private theorem hasPointwiseLeftKanExtension_op_smallEtaleBaseChange {V U : Scheme.{u}}
    (g : V ⟶ U) (C : Type*) [Category.{u + 1} C] [HasColimitsOfSize.{u + 1, u + 1} C]
    (P : (U.Etale)ᵒᵖ ⥤ C) : (smallEtaleBaseChange g).op.HasPointwiseLeftKanExtension P :=
  fun Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow (smallEtaleBaseChange g).op Y) C
    infer_instance

/-- Inverse image of sheaves of `F_ℓ`-modules commutes with forgetting the module structure. -/
theorem nonempty_forgetZMod_pullback_iso {V U : Scheme.{u}} (g : V ⟶ U)
    (M : Sheaf (smallEtaleTopology U) (ModuleCat.{u + 1} (ZMod ℓ))) :
    Nonempty ((forgetZModSheaf V ℓ).obj ((smallEtalePullbackZMod.{u + 1, u} ℓ g).obj M) ≅
      (etaleAbelianInverseImage.{u, u + 1} g).obj ((forgetZModSheaf U ℓ).obj M)) := by
  let Φ := Stacks.EtaleCohomology.smallEtaleBaseChange g
  let _ := fun P => hasPointwiseLeftKanExtension_op_smallEtaleBaseChange g
    (ModuleCat.{u + 1} (ZMod ℓ)) P
  let _ := fun P => hasPointwiseLeftKanExtension_op_smallEtaleBaseChange g
    AddCommGrpCat.{u + 1} P
  let e₁ := Φ.sheafPullbackSheafComposeIso (ModuleCat.{u + 1} (ZMod ℓ)) (smallEtaleTopology U)
    (smallEtaleTopology V) (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}) M
  let e₂ := (Adjunction.leftAdjointUniq (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} g)
    (Φ.sheafAdjunctionContinuous AddCommGrpCat.{u + 1} (smallEtaleTopology U)
      (smallEtaleTopology V))).app ((forgetZModSheaf U ℓ).obj M)
  exact ⟨e₁.symm ≪≫ e₂.symm⟩

end Stacks.EtaleCohomology

end
