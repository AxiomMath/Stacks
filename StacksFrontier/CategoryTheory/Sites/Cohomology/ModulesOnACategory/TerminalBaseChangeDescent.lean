module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCechSheafCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangePresheaf

/-!
# Faithfully flat descent for the base change presheaf of a module

Let `C` be a category with a terminal object `X`, let `O` be a presheaf of rings on `C` with
commutative section rings, and let `M` be an `O(X)`-module. The presheaf of modules
`P_M : U ↦ O(U) ⊗_{O(X)} M` of `Stacks.TerminalBaseChange.baseChangePresheaf` has restriction
maps which are base changes: along `g : W ⟶ T` the sections over `W` are
`O(W) ⊗_{O(T)} P_M(T)`. Consequently `P_M` satisfies the sheaf condition for a finite family
`{Y i ⟶ T}` as soon as the product of the rings `O(Y i)` is faithfully flat over `O(T)` and the
rings of chosen objects `Pb i j` over pairs of members are the tensor products of the rings of
the members: this is degree-zero exactness of the Amitsur complex (Stacks 023M).

## Main results

* `Stacks.TerminalBaseChange.exists_baseChangePresheaf_restrictionEquiv`: the restriction maps of
  `P_M` are base changes.
* `Stacks.TerminalBaseChange.isSheafFor_baseChangePresheaf_ofArrows`: the sheaf condition for
  such a family.
-/

@[expose] public section

universe t v u r

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace Stacks.TerminalBaseChange

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r}) [CommSections O]
  {X : C} (hX : IsTerminal X) (M : ModuleCat.{max t r} (O.obj (op X)))

/-- **The restriction maps of the base change presheaf are base changes.** Along `g : W ⟶ T` the
sections over `W` are the base change of the sections over `T` along `O(T) → O(W)`, compatibly
with restriction. -/
theorem exists_baseChangePresheaf_restrictionEquiv {T W : C} (g : W ⟶ T) :
    letI := (O.map g.op).hom.toAlgebra
    ∃ e : O.obj (op W) ⊗[O.obj (op T)] ((baseChangePresheaf.{t} O hX).obj M).obj (op T)
        ≃ₗ[O.obj (op W)] ((baseChangePresheaf.{t} O hX).obj M).obj (op W),
      ∀ n, e ((1 : O.obj (op W)) ⊗ₜ[O.obj (op T)] n) =
        ((baseChangePresheaf.{t} O hX).obj M).map g.op n := by
  let : Algebra (O.obj (op T)) (O.obj (op W)) := (O.map g.op).hom.toAlgebra
  let : Algebra ((constRing O X).obj (op T)) ((commPresheaf O).obj (op T)) :=
    ((theta O hX).app (op T)).hom.toAlgebra
  let : Algebra ((constRing O X).obj (op T)) ((commPresheaf O).obj (op W)) :=
    ((theta O hX).app (op W)).hom.toAlgebra
  let : Algebra ((commPresheaf O).obj (op T)) ((commPresheaf O).obj (op W)) :=
    (O.map g.op).hom.toAlgebra
  have : IsScalarTower ((constRing O X).obj (op T)) ((commPresheaf O).obj (op T))
      ((commPresheaf O).obj (op W)) :=
    IsScalarTower.of_algebraMap_eq fun s => (rho_comp_apply O hX g.op s).symm
  refine ⟨TensorProduct.AlgebraTensorModule.cancelBaseChange ((constRing O X).obj (op T))
    ((commPresheaf O).obj (op T)) ((commPresheaf O).obj (op W)) ((commPresheaf O).obj (op W))
    ((constModObj.{t} O X M).obj (op T)), fun n => ?_⟩
  induction n using TensorProduct.induction_on with
  | zero =>
    exact (congrArg _ (TensorProduct.tmul_zero _ _)).trans ((map_zero _).trans (map_zero _).symm)
  | tmul s m =>
    refine Eq.trans (b := (((show (commPresheaf O).obj (op W) from (O.map g.op).hom s) * 1)
        ⊗ₜ[(constRing O X).obj (op T)] m :
      (commPresheaf O).obj (op W) ⊗[(constRing O X).obj (op T)]
        ((constModObj.{t} O X M).obj (op T)))) ?_ ?_
    · exact TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul ..
    · refine Eq.trans ?_ (Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul (theta O hX)
        (constModObj.{t} O X M) g.op s m).symm
      rw [mul_one]
      rfl
  | add x y hx hy =>
    exact (congrArg _ (TensorProduct.tmul_add _ _ _)).trans
      ((map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm))

/-- **The sheaf condition for the base change presheaf along a finite faithfully flat family.**
Let `{g i : Y i ⟶ T}` be a finite family and `Pb i j` objects over the pairs of members whose ring
is the tensor product of the rings of the two members over `O(T)`. If the product of the rings
`O(Y i)` is faithfully flat over `O(T)`, then `U ↦ O(U) ⊗_{O(X)} M` satisfies the sheaf condition
for the family: this is degree-zero exactness of the Amitsur complex (Stacks 023M), through
`PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀`. -/
theorem isSheafFor_baseChangePresheaf_ofArrows {T : C} {ι : Type*} [Finite ι] {Y : ι → C}
    (g : ∀ i, Y i ⟶ T) {Pb : ι → ι → C} (pr₁ : ∀ i j, Pb i j ⟶ Y i)
    (pr₂ : ∀ i j, Pb i j ⟶ Y j) (hpr : ∀ i j, pr₁ i j ≫ g i = pr₂ i j ≫ g j)
    (hff : letI : ∀ i, Algebra (O.obj (op T)) (O.obj (op (Y i))) :=
        fun i => (O.map (g i).op).hom.toAlgebra
      Module.FaithfullyFlat (O.obj (op T)) (∀ i, O.obj (op (Y i))))
    (hpush : ∀ i j, IsPushout (CommRingCat.ofHom (O.map (g i).op).hom)
      (CommRingCat.ofHom (O.map (g j).op).hom) (CommRingCat.ofHom (O.map (pr₁ i j).op).hom)
      (CommRingCat.ofHom (O.map (pr₂ i j).op).hom)) :
    Presieve.IsSheafFor (((baseChangePresheaf.{t} O hX).obj M).presheaf ⋙
      CategoryTheory.forget AddCommGrpCat.{max t r}) (Presieve.ofArrows Y g) := by
  classical
  let N := (baseChangePresheaf.{t} O hX).obj M
  let _ : ∀ i, Algebra (O.obj (op T)) (O.obj (op (Y i))) :=
    fun i => (O.map (g i).op).hom.toAlgebra
  have hem : ∀ i, ∃ e : O.obj (op (Y i)) ⊗[O.obj (op T)] N.obj (op T) ≃ₗ[O.obj (op (Y i))]
      N.obj (op (Y i)), ∀ n, e ((1 : O.obj (op (Y i))) ⊗ₜ[O.obj (op T)] n) = N.map (g i).op n :=
    fun i => exists_baseChangePresheaf_restrictionEquiv O hX M (g i)
  choose em hem using hem
  have hpairf : ∀ i j, ∃ F : (O.obj (op (Y i)) ⊗[O.obj (op T)] O.obj (op (Y j))) ⊗[O.obj (op T)]
      N.obj (op T) →+ N.obj (op (Pb i j)),
      Function.Injective F ∧
        (∀ (b : O.obj (op (Y i))) (n), N.restrictₛₗ (pr₁ i j).op (em i (b ⊗ₜ n)) =
            F ((b ⊗ₜ[O.obj (op T)] (1 : O.obj (op (Y j)))) ⊗ₜ n)) ∧
          ∀ (b : O.obj (op (Y j))) (n), N.restrictₛₗ (pr₂ i j).op (em j (b ⊗ₜ n)) =
            F (((1 : O.obj (op (Y i))) ⊗ₜ[O.obj (op T)] b) ⊗ₜ n) := fun i j => by
    let _ : Algebra (O.obj (op (Y i))) (O.obj (op (Pb i j))) :=
      (O.map (pr₁ i j).op).hom.toAlgebra
    let _ : Algebra (O.obj (op (Y j))) (O.obj (op (Pb i j))) :=
      (O.map (pr₂ i j).op).hom.toAlgebra
    let _ : Algebra (O.obj (op T)) (O.obj (op (Pb i j))) :=
      (O.map (pr₁ i j ≫ g i).op).hom.toAlgebra
    have tw : ∀ {A : C} (a : A ⟶ T) (p : Pb i j ⟶ A), p ≫ a = pr₁ i j ≫ g i → ∀ c,
        (O.map (pr₁ i j ≫ g i).op).hom c = (O.map p.op).hom ((O.map a.op).hom c) :=
      fun a p h c => by simp [← h]
    have t₁ : IsScalarTower (O.obj (op T)) (O.obj (op (Y i))) (O.obj (op (Pb i j))) :=
      IsScalarTower.of_algebraMap_eq (tw _ _ rfl)
    have t₂ : IsScalarTower (O.obj (op T)) (O.obj (op (Y j))) (O.obj (op (Pb i j))) :=
      IsScalarTower.of_algebraMap_eq (tw _ _ (hpr i j).symm)
    have hpo : Algebra.IsPushout (O.obj (op T)) (O.obj (op (Y i))) (O.obj (op (Y j)))
        (O.obj (op (Pb i j))) :=
      CommRingCat.isPushout_iff_isPushout.1 (hpush i j)
    obtain ⟨eP, heP⟩ := exists_baseChangePresheaf_restrictionEquiv O hX M (pr₁ i j ≫ g i)
    exact PresheafOfModules.exists_pairBaseChange (N := N) (g i) (g j) (pr₁ i j) (pr₂ i j)
      (hpr i j) (O.obj (op T)) (O.obj (op (Y i))) (O.obj (op (Y j))) (O.obj (op (Pb i j)))
      (em i) (hem i) (em j) (hem j) eP heP
      (fun b u => N.map_smul (pr₁ i j).op b u) (fun b u => N.map_smul (pr₂ i j).op b u)
  choose F hFinj hnat₁ hnat₂ using hpairf
  obtain ⟨eW, eV, hbijW, honeW, hinjV, hd₀⟩ :=
    PresheafOfModules.exists_amitsurDiff₀_data (N := N) g pr₁ pr₂ (O.obj (op T))
      (fun i => O.obj (op (Y i))) (fun i => (em i).toAddEquiv) hem F hFinj hnat₁ hnat₂
  have : Module.FaithfullyFlat (O.obj (op T)) (∀ i, O.obj (op (Y i))) := hff
  exact PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀ g (O.obj (op T))
    (∀ i, O.obj (op (Y i))) Pb pr₁ pr₂ hpr eW hbijW honeW eV hinjV hd₀

end Stacks.TerminalBaseChange

end
