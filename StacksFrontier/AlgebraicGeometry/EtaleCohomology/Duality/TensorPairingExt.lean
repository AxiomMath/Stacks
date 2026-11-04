module

public import StacksFrontier.CategoryTheory.Sites.Point.ExactPairingOfFibers
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.GeometricFibres
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit

/-!
# Duality of `Ext` along a fibrewise perfect pairing of étale sheaves

Let `Y` be a scheme, `N ≥ 1`, and let `μ : F ⊗ G ⟶ ℤ/N` be a pairing of sheaves of
`ℤ/N`-modules on the small étale site of `Y`, where `G` is locally constant of finite type with
flat geometric fibres and `μ` is perfect on every geometric fibre: `F_s̄ → Hom(G_s̄, ℤ/N)` is
bijective. Then `μ` is the evaluation of an exact pairing between `G` and `F`
(`Stacks.EtaleCohomology.exactPairingOfFiberPerfect`, from
`Stacks.SheafDuality.exactPairingOfPerfect` at the residue geometric points), so `- ⊗ G` is left
adjoint to the exact functor `- ⊗ F`, and the adjunction gives
`Ext^i(ℤ/N, F) ≅ Ext^i(G, ℤ/N)` for every `i`. Read through `Ext^i(ℤ/N, -) = Hⁱ(Y, -)` this is
the map underlying the cup product pairing `Hⁱ(Y, F) × Ext^j(ℤ/N, G) → Ext^{i+j}(ℤ/N, ℤ/N)` of
`Stacks.ExtCup.cup`: `Stacks.ExtCup.cup μ a b = b ∘ Θ_μ(a)`. This is the coefficient duality
step of the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exactPairingOfFiberPerfect`: the exact pairing, with evaluation `μ`
  (`Stacks.EtaleCohomology.exactPairingOfFiberPerfect_evaluation`).
* `Stacks.EtaleCohomology.bijective_tensorPairingExt`: `a ↦ (a ⊗ G) ∘ μ ∘ λ⁻¹` is bijective.

## Implementation notes

No local constancy of `F` is assumed: it follows from the perfectness of `μ`, `F` being the dual
of `G`. Flatness of the fibres of `G` cannot be dropped: over `ℤ/4`, `G = F = ℤ/2` with
`(x, y) ↦ 2xy` is perfect on fibres while `G` has no dual.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory AlgebraicGeometry
  Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory moduleCat_hasLimitsOfSize
  etaleModules_AB5OfSize etaleModules_preservesFilteredColimits_forget
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

/-- Sheafification of presheaves of `ℤ/N`-modules on the slices of the small étale site, at the
coefficient universe `u + 1`: `Stacks.ConstantSheaf.hasSheafify_moduleCat` with its universes
fixed, which instance search cannot do itself. -/
local instance hasWeakSheafify_smallEtale_over_zmod (Y : Scheme.{u}) (N : ℕ) (V : Y.Etale) :
    HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} (ZMod N)) :=
  haveI := Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1}
    (Y.smallEtaleTopology.over V) (ZMod N)
  inferInstance

variable {Y : Scheme.{u}} {N : ℕ} [NeZero N]
  [(Y.smallEtaleTopology.W (A := ModuleCat.{u + 1} (ZMod N))).IsMonoidal]

/-- **A pairing of étale sheaves of `ℤ/N`-modules which is perfect on geometric fibres is an exact
pairing**, for `G` locally constant of finite type with flat fibres: `μ : F ⊗ G ⟶ ℤ/N` is the
evaluation of a duality between `G` and `F`, whose coevaluation `ℤ/N ⟶ G ⊗ F` is glued from the
canonical elements of the fibres. -/
@[instance_reducible]
def exactPairingOfFiberPerfect (F G : EtaleModules.{u, 0} (ZMod N) Y)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) Y.smallEtaleTopology G)
    (hGflat : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Module.Flat (ZMod N)
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod N))).obj G))
    (μ : F ⊗ G ⟶ unitSheaf (X := Y) N)
    (hμ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} (ZMod N)))
        F G ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod N))).map μ).hom)) :
    ExactPairing G F := by
  haveI : ∀ V : Y.Etale,
      (Y.smallEtaleTopology.over V).WEqualsLocallyBijective (ModuleCat.{u + 1} (ZMod N)) :=
    fun V => Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, u + 1, 0} _ (ZMod N)
  refine Stacks.SheafDuality.exactPairingOfPerfect
    (isConservativeFamilyOfPoints_residueGeometricPoints.{u, 0} Y)
    (μ : F ⊗ G ⟶ 𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) hG ?_ ?_
  · rintro ⟨_, ⟨y⟩⟩
    exact hGflat _ (residueGeometricPoint Y y)
  · rintro ⟨_, ⟨y⟩⟩
    have h := Function.Bijective.comp (LinearEquiv.congrRight (Stacks.SheafDuality.unitEquiv
      ((Scheme.pointSmallEtale (residueGeometricPoint Y y)).ulift.{u + 1}).sheafFiber)).bijective
        (hμ _ (residueGeometricPoint Y y))
    convert h using 1
    funext b
    ext g
    rfl

/-- The evaluation of `exactPairingOfFiberPerfect` is the given pairing. -/
theorem exactPairingOfFiberPerfect_evaluation (F G : EtaleModules.{u, 0} (ZMod N) Y)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) Y.smallEtaleTopology G)
    (hGflat : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Module.Flat (ZMod N)
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod N))).obj G))
    (μ : F ⊗ G ⟶ unitSheaf (X := Y) N)
    (hμ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} (ZMod N)))
        F G ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod N))).map μ).hom)) :
    letI := exactPairingOfFiberPerfect F G hG hGflat μ hμ
    ε_ G F = μ :=
  rfl

/-- **Duality of `Ext` along a fibrewise perfect pairing.** Let `μ : F ⊗ G ⟶ ℤ/N` be a pairing
of étale sheaves of `ℤ/N`-modules on `Y`, with `G` locally constant of finite type with flat
fibres, which is perfect on every geometric fibre. Then for every `i` the map
`Ext^i(ℤ/N, F) → Ext^i(G, ℤ/N)`, `a ↦ μ ∘ (a ⊗ G) ∘ λ⁻¹`, is bijective.

The pairing is the evaluation of an exact pairing (`exactPairingOfFiberPerfect`), so `- ⊗ G` is
left adjoint to the exact functor `- ⊗ F`, and the map is the adjunction isomorphism
`Ext^i(ℤ/N, ℤ/N ⊗ F) ≅ Ext^i(ℤ/N ⊗ G, ℤ/N)` of `Stacks.ExtAdjunction.extMap_bijective` composed
with the unitors. -/
theorem bijective_tensorPairingExt (F G : EtaleModules.{u, 0} (ZMod N) Y)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) Y.smallEtaleTopology G)
    (hGflat : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Module.Flat (ZMod N)
        ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod N))).obj G))
    [(MonoidalCategory.tensorRight G).Additive]
    [PreservesFiniteLimits (MonoidalCategory.tensorRight G)]
    [PreservesFiniteColimits (MonoidalCategory.tensorRight G)]
    (μ : F ⊗ G ⟶ unitSheaf (X := Y) N)
    (hμ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} (ZMod N)))
        F G ≫
        (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
          (A := ModuleCat.{u + 1} (ZMod N))).map μ).hom))
    (i : ℕ) :
    Function.Bijective (fun a : Ext (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) F i =>
      (Ext.mk₀ (λ_ G).inv).comp
        ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ)
        (add_zero i)) (zero_add i)) := by
  let := exactPairingOfFiberPerfect F G hG hGflat μ hμ
  let adj := tensorRightAdjunction G F
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight F) :=
    have : PreservesLimitsOfSize.{0, 0} (MonoidalCategory.tensorRight F) :=
      adj.rightAdjoint_preservesLimits
    PreservesLimitsOfSize.preservesFiniteLimits _
  have : PreservesColimitsOfSize.{u, u + 1} (MonoidalCategory.tensorRight F) :=
    Sheaf.preservesColimitsOfSize_tensorRight_moduleCat.{u + 1, u, u + 1, 0} F
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight F) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : (MonoidalCategory.tensorRight F).Additive :=
    Functor.additive_of_preserves_binary_products _
  let φ : F ⟶ (MonoidalCategory.tensorRight F).obj (unitSheaf (X := Y) N) := (λ_ F).inv
  have : IsIso φ := inferInstanceAs (IsIso (λ_ F).inv)
  have hcounit : (MonoidalCategory.tensorRight G).map φ ≫
      adj.counit.app (unitSheaf (X := Y) N) = μ := by
    show (λ_ F).inv ▷ G ≫ (𝟙 _ ▷ G ≫ (α_ _ _ _).hom ≫ _ ◁ μ ≫ (ρ_ _).hom) = μ
    simp only [id_whiskerRight, Category.id_comp]
    monoidal
  have key : ∀ a : Ext (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) F i,
      (a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ) (add_zero i) =
        Stacks.ExtAdjunction.extMap adj (𝟙_ _) (unitSheaf (X := Y) N) i
          (a.comp (Ext.mk₀ φ) (add_zero i)) := by
    intro a
    rw [Stacks.ExtAdjunction.extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hcounit]
  have hΘ : (fun a : Ext (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y)) F i =>
      (Ext.mk₀ (λ_ G).inv).comp
        ((a.mapExactFunctor (MonoidalCategory.tensorRight G)).comp (Ext.mk₀ μ)
        (add_zero i)) (zero_add i)) =
      ((Ext.mk₀ (λ_ G).inv).precomp (unitSheaf (X := Y) N) (zero_add i)) ∘
        (Stacks.ExtAdjunction.extMap adj (𝟙_ _) (unitSheaf (X := Y) N) i) ∘
          ((Ext.mk₀ φ).postcomp (𝟙_ _) (add_zero i)) := by
    funext a
    simp only [Function.comp_apply, Stacks.ExtAdjunction.precomp_apply,
      Stacks.ExtAdjunction.postcomp_apply, key]
  rw [hΘ]
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ i).comp
    ((Stacks.ExtAdjunction.extMap_bijective adj _ _ i).comp
      (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso _ i))

end Stacks.EtaleCohomology
