module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PointClassNonzero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CompactSupportTopExcision
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison

/-!
# The class of a point is nonzero once it is nonzero on a dense open

Let `W` be of finite type over a separably closed field `k`, with a compactification `j : W → X̄`,
let `U ⊆ W` be an open whose closed complement `Z` has dimension at most `e`, and let `x : P → W`
be a closed point of `W` lying in `U`. The class of `x` in `H^{2e+2}_c(W)`
(`Stacks.EtaleCohomology.PointClassNonzeroAt`, through an open `N ∋ x` of `W`) is nonzero as
soon as the class of `x` in `H^{2e+2}_c(U)`, through the compactification `U → W → X̄`, is
(`Stacks.EtaleCohomology.pointClassNonzeroAt_of_restrictOpen`): the extension by zero
`H^{2e+2}_c(U) → H^{2e+2}_c(W)` is injective, the complement having cohomological dimension at
most `2e` (`Stacks.EtaleCohomology.bijective_ext_extensionByZero_counit_of_closed`), it carries
the class of `x` in `U` to the class of `x` in `W`, and the skyscraper sheaves `(N → X̄)_! x_* Λ`
and `(U → X̄)_! x_* Λ` are both the direct image of `Λ` along the closed point of `X̄`
(Tag 0GJ1 for the cartesian squares of `x` in `N` and in `U`).

This is the excision step of the class of a point through an elementary fibration, in the proof
of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImageExtensionByZeroIsoOfComp`.
* `Stacks.EtaleCohomology.pointClassNonzeroAt_of_restrictOpen`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

-- `Stacks.EtaleCohomology.PointClassNonzeroAt` reads `ZMod ℓ` as a ring through `ZMod.commRing`;
-- the field structure would give a second, only definitionally equal, path.
attribute [-instance] ZMod.instField

/-- **`n_! ∘ i_* ≅ x_*`** for a closed immersion `x = i ≫ n` through an open immersion `n`: the
square of `i`, `𝟙`, `n`, `x` is cartesian, `n` being a monomorphism (Tag 0GJ1). -/
def etaleModuleDirectImageExtensionByZeroIsoOfComp (Λ : Type) [Ring Λ] {P N W : Scheme.{u}}
    (i : P ⟶ N) (n : N ⟶ W) [IsOpenImmersion n] (x : P ⟶ W) [IsClosedImmersion x]
    (h : i ≫ n = x) :
    etaleModuleDirectImage.{u, 0} Λ i ⋙ etaleModuleExtensionByZero.{u, 0} Λ n ≅
      etaleModuleDirectImage.{u, 0} Λ x :=
  etaleModuleExtensionByZeroDirectImageIso.{u, 0} Λ i (𝟙 P) n x
      (IsPullback.of_vert_isIso_mono ⟨by rw [h, Category.id_comp]⟩) ≪≫
    Functor.isoWhiskerRight (etaleModuleExtensionByZeroIdIso Λ P) _ ≪≫ Functor.leftUnitor _

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [IsSepClosed k] {W : Scheme.{u}}
  (f : W ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  (jc : CompactificationOf (Over.mk f))

/-- **The class of a point is nonzero once it is nonzero on an open with small complement.** Let
`U ⊆ W` be open with closed complement `Z` of dimension at most `e`, and `x : P → W` a closed
immersion through an open `n : N → W` (as `i : P → N`) and through `U` (as `p : P → U`). If the
class of `p` in `H^{2e+2}_c(U)` is nonzero, through the compactification `U → W → X̄`, so is the
class of `i` in `H^{2e+2}_c(W)`. -/
theorem pointClassNonzeroAt_of_restrictOpen [TopologicalSpace.NoetherianSpace jc.space]
    (U : W.Opens) {Z : Scheme.{u}} (iZ : Z ⟶ W) [IsClosedImmersion iZ]
    (hiU : Set.range U.ι.base = (Set.range iZ.base)ᶜ) (e : ℕ)
    (hd : topologicalKrullDim Z ≤ e) {N P : Scheme.{u}} (n : N ⟶ W) [IsOpenImmersion n]
    (i : P ⟶ N) (p : P ⟶ U.toScheme) (x : P ⟶ W) [IsClosedImmersion x] (hi : i ≫ n = x)
    (hp : p ≫ U.ι = x)
    (h : PointClassNonzeroAt ℓ (e + 1) (U.ι ≫ f) (jc.restrictOpen U.ι) (𝟙 U.toScheme) p) :
    PointClassNonzeroAt ℓ (e + 1) f jc n i := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨γU, zU, hU⟩ := h
  let jW := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion
  -- the two skyscraper sheaves at `x`
  let M := unitSheaf (X := P) ℓ
  let εW : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj M) ≅
      jW.obj ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) x).obj M) :=
    (etaleModuleExtensionByZeroCompIso (ZMod ℓ) n jc.immersion).app _ ≪≫
      jW.mapIso ((etaleModuleDirectImageExtensionByZeroIsoOfComp (ZMod ℓ) i n x hi).app M)
  let εU : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
        (𝟙 U.toScheme ≫ (jc.restrictOpen U.ι).immersion)).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) p).obj M) ≅
      jW.obj ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) x).obj M) :=
    (etaleModuleExtensionByZeroCompIso (ZMod ℓ) (𝟙 U.toScheme)
        (jc.restrictOpen U.ι).immersion).app _ ≪≫
      (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (jc.restrictOpen U.ι).immersion).mapIso
        ((etaleModuleExtensionByZeroIdIso (ZMod ℓ) U.toScheme).app _) ≪≫
      (etaleModuleExtensionByZeroCompIso (ZMod ℓ) U.ι jc.immersion).app _ ≪≫
      jW.mapIso ((etaleModuleDirectImageExtensionByZeroIsoOfComp (ZMod ℓ) p U.ι x hp).app M)
  -- the extension by zero `H^{2e+2}_c(U) → H^{2e+2}_c(W)`
  let eU : unitSheaf (X := U.toScheme) ℓ ≅
      (etaleModuleRestriction.{u, 0} (ZMod ℓ) U.ι).obj (unitSheaf (X := W) ℓ) :=
    ((etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) U.ι).app
        (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))).symm ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod ℓ) U.ι).app (unitSheaf (X := W) ℓ)
  let eT : (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (U.ι ≫ jc.immersion)).obj
        (unitSheaf (X := U.toScheme) ℓ) ≅
      jW.obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) U.ι).obj
          (unitSheaf (X := W) ℓ)) :=
    (etaleModuleExtensionByZeroCompIso (ZMod ℓ) U.ι jc.immersion).app _ ≪≫
      jW.mapIso ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) U.ι).mapIso eU)
  let μ := eT.hom ≫ jW.map ((etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) U.ι).counit.app
    (unitSheaf (X := W) ℓ))
  have hbij := bijective_ext_extensionByZero_counit_of_closed jc U iZ hiU e hd
    (unitSheaf (X := W) ℓ) (2 * (e + 1)) (by omega)
  have hinj : Function.Injective (fun y : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (U.ι ≫ jc.immersion)).obj
        (unitSheaf (X := U.toScheme) ℓ)) (2 * (e + 1)) =>
      y.comp (Ext.mk₀ μ) (add_zero _)) := by
    intro y₁ y₂ hy
    apply (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso eT.hom (2 * (e + 1))).1
    apply hbij.1
    simp only [μ] at hy
    show (y₁.comp (Ext.mk₀ eT.hom) (add_zero _)).comp (Ext.mk₀ _) (add_zero _) =
      (y₂.comp (Ext.mk₀ eT.hom) (add_zero _)).comp (Ext.mk₀ _) (add_zero _)
    rwa [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  -- the class on `W`
  let γ' : Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)).obj
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) i).obj M))
      (jW.obj (unitSheaf (X := W) ℓ)) (2 * (e + 1)) :=
    (Ext.mk₀ (εW.hom ≫ εU.inv)).comp ((Stacks.ExtAdjunction.extMap
      (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ)
        (𝟙 U.toScheme ≫ (jc.restrictOpen U.ι).immersion)) _ _ (2 * (e + 1)) γU).comp
          (Ext.mk₀ μ) (add_zero _)) (zero_add _)
  obtain ⟨γ₀, hγ₀⟩ := (Stacks.ExtAdjunction.extMap_bijective
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) (n ≫ jc.immersion)) _
    (jW.obj (unitSheaf (X := W) ℓ)) (2 * (e + 1))).2 γ'
  refine ⟨γ₀, zU.comp (Ext.mk₀ (εU.hom ≫ εW.inv)) (add_zero 0), ?_⟩
  rw [hγ₀]
  have gen : ∀ {X₀ X₁ X₂ X₃ X₄ : EtaleModules.{u, 0} (ZMod ℓ) jc.space} {q : ℕ}
      (z : Ext X₀ X₁ 0) (E : Ext X₁ X₃ q) (μ' : X₃ ⟶ X₄) (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₁),
      a ≫ b = 𝟙 _ → (z.comp E (zero_add q)).comp (Ext.mk₀ μ') (add_zero q) =
        (z.comp (Ext.mk₀ a) (add_zero 0)).comp ((Ext.mk₀ b).comp (E.comp (Ext.mk₀ μ')
          (add_zero q)) (zero_add q)) (zero_add q) := by
    intro X₀ X₁ X₂ X₃ X₄ q z E μ' a b hab
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀_assoc, hab, Ext.mk₀_id_comp]
  have hab : ∀ {A B C : EtaleModules.{u, 0} (ZMod ℓ) jc.space} (α : A ≅ B) (β : C ≅ B),
      (α.hom ≫ β.inv) ≫ β.hom ≫ α.inv = 𝟙 _ := by
    intros; simp
  intro h0
  apply hU
  apply hinj
  refine (gen zU _ μ (εU.hom ≫ εW.inv) (εW.hom ≫ εU.inv)
    (hab εU εW)).trans ?_
  exact h0.trans (Ext.zero_comp _ _ _ _ _).symm

end Stacks.EtaleCohomology

end
