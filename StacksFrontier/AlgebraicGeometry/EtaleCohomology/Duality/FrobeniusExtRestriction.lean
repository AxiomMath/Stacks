module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExtTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantTwistedFrobeniusFix
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CupProductRestriction

/-!
# The canonical Frobenius on `Hⁱ(Y_k̄, Λ)` is restriction along `π̄`

Let `k` be a finite field, `Y` a scheme over `k`, `k̄` an extension of `k`, `pr : Y_k̄ ⟶ Y` the
projection and `π̄ = π_Y × id` the base change of the geometric Frobenius. The canonical geometric
Frobenius `π_Y^*` of `Hⁱ(Y_k̄, Λ) = Ext^i(Λ, pr^{-1} Λ_Y)` is
`b ↦ θ(b ∘ τ)` (`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt_canonical_apply`),
with `τ : pr^{-1} Λ_Y ⟶ π̄_* pr^{-1} Λ_Y` the base change of the Frobenius descent isomorphism of
[Stacks, Tag 03SR] and `θ` the `Ext` map of the adjunction `π̄^{-1} ⊣ π̄_*`.

Transported to the constant sheaf `Λ_{Y_k̄} ≅ pr^{-1} Λ_Y`, the twist `τ` is the canonical map
`Λ ⟶ π̄_* Λ` adjoint to `π̄^{-1} Λ ≅ Λ`: both fix the constant section, and maps out of a constant
sheaf are determined by it
(`transportedConstantTwist_frobeniusBaseChangeTwist_eq_constantSelfMapTwist`). Hence, read on
`Ext^i(Λ_{Y_k̄}, Λ_{Y_k̄})`, the canonical Frobenius is the restriction
`Stacks.EtaleCohomology.constantExtRestriction Λ π̄ i` along `π̄`
(`Stacks.EtaleCohomology.adjunctionExtMap_frobeniusBaseChangeTwist_constant`), the map which
commutes with cup products. This identifies `π_X^*` with the pullback along `π̄`, as in the
Frobenius equivariance of the Weil pairing of [Tag 03V8].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  etaleModuleInverseImageSheafPullbackMonoidal etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The class of morphisms inverted by sheafification of étale `Λ`-modules on `S` is compatible
with the monoidal structure. -/
local instance (S : Scheme.{u}) : (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

/-- **The Frobenius base change twist of the constant sheaf is the canonical map.** Transported
to `Λ_{Y_k̄}` along `pr^{-1} Λ_Y ≅ Λ_{Y_k̄}`, the base change `τ` of the Frobenius descent
isomorphism is the map `Λ_{Y_k̄} ⟶ π̄_* Λ_{Y_k̄}` adjoint to `π̄^{-1} Λ ≅ Λ`: both fix the constant
section. -/
theorem transportedConstantTwist_frobeniusBaseChangeTwist_eq_constantSelfMapTwist
    (M : ModuleCat.{u + 1} Λ) :
    transportedConstantTwist.{u, 0} Λ M (fieldBaseChangeProj Y kbar)
        (geometricFrobeniusBaseChange Y kbar p q hcard)
        ((frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app
          (etaleModuleConstantSheaf Λ M Y.left)) =
      constantSelfMapTwist Λ M (geometricFrobeniusBaseChange Y kbar p q hcard) := by
  obtain ⟨ρ, hρ⟩ := exists_pulledBackConstantSection_comp_frobeniusBaseChangeTwist Λ M Y kbar p q
    hcard
  apply constantSheaf_hom_ext
  rw [constantSheafSection_comp_transportedConstantTwist Λ M _ _ _ ρ hρ,
    constantSheafSection_comp_constantSelfMapTwist]

/-- **The adjoint of the transported Frobenius twist of the constant sheaf is the canonical
identification** `π̄^{-1} Λ_{Y_k̄} ≅ Λ_{Y_k̄}`. -/
theorem inverseImage_frobeniusBaseChangeTwist_constant_comp_counit :
    (etaleModuleInverseImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).map
        ((inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ (ModuleCat.of Λ (ULift.{u + 1} Λ))
            (fieldBaseChangeProj Y kbar)).inv ≫
          (frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.left.smallEtaleTopology)) ≫
      (etaleModuleInverseImageAdj.{u, 0} Λ
            (geometricFrobeniusBaseChange Y kbar p q hcard)).counit.app
          ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.left.smallEtaleTopology)) ≫
        (inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ (ModuleCat.of Λ (ULift.{u + 1} Λ))
          (fieldBaseChangeProj Y kbar)).hom =
      (constantInverseImageIso Λ (geometricFrobeniusBaseChange Y kbar p q hcard)).inv := by
  set π := geometricFrobeniusBaseChange Y kbar p q hcard
  set M := ModuleCat.of Λ (ULift.{u + 1} Λ)
  set e := inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ M (fieldBaseChangeProj Y kbar)
  set adj := etaleModuleInverseImageAdj.{u, 0} Λ π
  have hcounit := adj.counit.naturality e.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hcounit
  have htw :=
    transportedConstantTwist_frobeniusBaseChangeTwist_eq_constantSelfMapTwist Λ Y kbar p q hcard M
  rw [← hcounit, ← Category.assoc, ← Functor.map_comp, Category.assoc, ← Adjunction.homEquiv_counit]
  show (adj.homEquiv _ _).symm (transportedConstantTwist.{u, 0} Λ M (fieldBaseChangeProj Y kbar) π
    ((frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app
      (etaleModuleConstantSheaf Λ M Y.left))) = _
  rw [htw, constantSelfMapTwist, Equiv.symm_apply_apply]
  rfl

/-- **The canonical Frobenius on `Hⁱ(Y_k̄, Λ)` is restriction along `π̄`.** Read on
`Ext^i(Λ_{Y_k̄}, Λ_{Y_k̄})` through `pr^{-1} Λ_Y ≅ Λ_{Y_k̄}`, the endomorphism `b ↦ θ(b ∘ τ)` of
`Ext^i(Λ_{Y_k̄}, pr^{-1} Λ_Y)` — the canonical geometric Frobenius
(`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt_canonical_apply`) — is
`Stacks.EtaleCohomology.constantExtRestriction Λ π̄ i`. -/
theorem adjunctionExtMap_frobeniusBaseChangeTwist_constant {i : ℕ}
    (b : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange Y kbar).smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange Y kbar).smallEtaleTopology) i) :
    (Stacks.ExtCup.adjunctionExtMap
        (etaleModuleInverseImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleInverseImageAdj.{u, 0} Λ (geometricFrobeniusBaseChange Y kbar p q hcard))
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj Y kbar)).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.left.smallEtaleTopology))
        ((b.comp (Ext.mk₀ (inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ
            (ModuleCat.of Λ (ULift.{u + 1} Λ)) (fieldBaseChangeProj Y kbar)).inv) (add_zero i)).comp
          (Ext.mk₀ ((frobeniusBaseChangeTwist.{u, 0} Λ Y kbar p q hcard).app
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.left.smallEtaleTopology)))
          (add_zero i))).comp
      (Ext.mk₀ (inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ (ModuleCat.of Λ (ULift.{u + 1} Λ))
        (fieldBaseChangeProj Y kbar)).hom) (add_zero i) =
      constantExtRestriction Λ (geometricFrobeniusBaseChange Y kbar p q hcard) i b := by
  rw [adjunctionExtMap_eq_etaleModuleExtRestriction Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard),
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, etaleModuleExtRestriction_comp_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, constantExtRestriction_eq]
  refine (Ext.comp_assoc_of_third_deg_zero _ _ _ (add_zero i)).trans ?_
  rw [Ext.mk₀_comp_mk₀, Category.assoc, inverseImage_frobeniusBaseChangeTwist_constant_comp_counit]
  rfl

section CompactSupport

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))

/-- **The canonical Frobenius on `Hⁱ_c(X_k̄, K)` is restriction along `π̄`**, when `j_! K` is the
constant sheaf on the compactification `X̄` (for instance `X` proper, `j = id` and `K = Λ_X`). Read
on `Ext^i(Λ_{X̄_k̄}, Λ_{X̄_k̄})` through `Hⁱ_c(X_k̄, K) ≅ Ext^i(Λ, (j_! K)|_{X̄_k̄})` and
`(j_! K)|_{X̄_k̄} ≅ Λ_{X̄}|_{X̄_k̄} ≅ Λ_{X̄_k̄}`, the canonical geometric Frobenius
`Stacks.EtaleCohomology.canonicalCompactSupportFrobeniusGroup` is
`Stacks.EtaleCohomology.constantExtRestriction Λ π̄ i`. -/
theorem compactSupportFrobeniusSingleIsoExt_canonical_constant (K : EtaleModules.{u, 0} Λ X)
    (γ : (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (Over.mk j.toBase).left.smallEtaleTopology) {i : ℕ}
    (b : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) i) :
    (((compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).hom).hom
        (((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          (canonicalCompactSupportFrobeniusGroup.{u, 0} Λ f j kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj K) i)).hom
          (((compactSupportFrobeniusSingleIsoExt Λ f j kbar K i).inv).hom
            (b.comp (Ext.mk₀ ((inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ
                (ModuleCat.of Λ (ULift.{u + 1} Λ))
                (fieldBaseChangeProj (Over.mk j.toBase) kbar)).inv ≫
              (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
                γ.inv)) (add_zero i))))).comp
      (Ext.mk₀ ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map
          γ.hom ≫ (inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ
            (ModuleCat.of Λ (ULift.{u + 1} Λ)) (fieldBaseChangeProj (Over.mk j.toBase) kbar)).hom))
        (add_zero i) =
      constantExtRestriction Λ (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard) i
        b := by
  rw [compactSupportFrobeniusSingleIsoExt_canonical_apply]
  have hnat :=
    (frobeniusBaseChangeTwist.{u, 0} Λ (Over.mk j.toBase) kbar p q hcard).naturality γ.inv
  dsimp only [Functor.comp_map] at hnat
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc, hnat,
    ← Category.assoc, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    adjunctionExtMap_eq_etaleModuleExtRestriction Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard),
    etaleModuleExtRestriction_comp_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  have hc := (etaleModuleInverseImageAdj.{u, 0} Λ
    (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)).counit.naturality
      ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map γ.inv)
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [← Category.assoc, hc, Category.assoc, ← Category.assoc
    ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).map γ.inv),
    ← Functor.map_comp, Iso.inv_hom_id]
  have h2 :=
    adjunctionExtMap_frobeniusBaseChangeTwist_constant Λ (Over.mk j.toBase) kbar p q hcard b
  rw [adjunctionExtMap_eq_etaleModuleExtRestriction Λ
      (geometricFrobeniusBaseChange (Over.mk j.toBase) kbar p q hcard)] at h2
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, etaleModuleExtRestriction_comp_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀] at h2 ⊢
  refine Eq.trans ?_ h2
  refine Eq.symm ((Ext.comp_assoc_of_third_deg_zero _ _ _ (add_zero i)).trans ?_)
  rw [Ext.mk₀_comp_mk₀, Category.assoc]
  rfl

end CompactSupport

end Stacks.EtaleCohomology

end
