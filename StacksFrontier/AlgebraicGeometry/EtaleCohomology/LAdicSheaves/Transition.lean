module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Additive

/-!
# The transition maps of an ℓ-adic sheaf

The transition map `Fₙ₊₁ ⟶ Fₙ` of an ℓ-adic sheaf is an epimorphism, and it exhibits the level
`Fₙ` as the quotient `Fₙ₊₁/ℓⁿ⁺¹Fₙ₊₁`. Multiplication by `ℓ` on `Fₙ₊₁` therefore factors through
it, by a Verschiebung map `Fₙ ⟶ Fₙ₊₁` whose composites with the transition map in either order
are multiplication by `ℓ`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.verschiebung`: the factorization of multiplication by `ℓ`
  through the transition map.

## Main results

* `Stacks.EtaleCohomology.restrictScalarsFunctor_full` and
  `.restrictScalarsFunctor_isLeftAdjoint`: restriction of scalars along the quotient of
  consecutive coefficient rings is full, and is a left adjoint as well as a right one.
* `Stacks.EtaleCohomology.scalarAdjunction_unit_isCokernel`: the unit of the scalar
  reduction/restriction adjunction at a level `n + 1` sheaf is its quotient by `ℓⁿ⁺¹`.
* `Stacks.EtaleCohomology.LAdicSheaf.transition_epi` and `.transition_isCokernel`: the
  transition map is an epimorphism exhibiting `Fₙ` as `Fₙ₊₁/ℓⁿ⁺¹Fₙ₊₁`.
* `Stacks.EtaleCohomology.LAdicSheaf.transition_verschiebung` and `.verschiebung_transition`:
  both composites of the transition map and the Verschiebung are multiplication by `ℓ`.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u u₁ u₂ u₃ v₁ v₂ v₃

namespace Stacks.EtaleCohomology

section Annihilated

/-- For a morphism `f` of sheaves of modules, `r • f` sends a section `x` to `r • f x`. -/
public theorem sheaf_nsmul_app
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {R : Type u₂} [Ring R] {P Q : Sheaf J (ModuleCat.{u₃} R)}
    (f : P ⟶ Q) (r : ℕ) (U : Cᵒᵖ) (x : P.obj.obj U) :
    ((r • f).hom.app U).hom x = r • (f.hom.app U).hom x := by
  change ((((sheafToPresheaf J (ModuleCat.{u₃} R)).map (r • f)).app U).hom x) = _
  rw [Functor.map_nsmul]
  rfl

/-- A sheaf of `ℤ/mℤ`-modules is annihilated by `m`. -/
public theorem zmodSheaf_nsmul_id
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (m : ℕ)
    (P : Sheaf J (ModuleCat.{u₂} (ZMod m))) : m • (𝟙 P) = 0 := by
  ext U x
  rw [sheaf_nsmul_app]
  exact ZModModule.char_nsmul_eq_zero m x

/-- The cokernel of multiplication by `r` on an object is annihilated by `r`. -/
public theorem cokernel_nsmul_id
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    (M : C) (r : ℕ) [HasCokernel (r • (𝟙 M))] :
    r • (𝟙 (cokernel (r • (𝟙 M)))) = 0 := by
  apply (cancel_epi (cokernel.π (r • (𝟙 M)))).1
  simpa only [Preadditive.comp_nsmul, Category.comp_id, comp_zero,
    Preadditive.nsmul_comp, Category.id_comp] using cokernel.condition (r • (𝟙 M))

/-- If `r` kills every section of the target of `f`, then `r • 𝟙 P` is killed by `f`. -/
private theorem nsmul_id_comp_eq_zero
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Type u₂} [Ring R] {P Q : Sheaf J (ModuleCat.{u₃} R)}
    (f : P ⟶ Q) (r : ℕ) (h : ∀ U (x : Q.obj.obj U), r • x = 0) : (r • (𝟙 P)) ≫ f = 0 := by
  rw [Preadditive.nsmul_comp, Category.id_comp]
  ext U x
  rw [sheaf_nsmul_app]
  exact h U _

/-- A presheaf of `ℤ/mℤ`-modules annihilated by `n`, read as a presheaf of
`ℤ/nℤ`-modules. -/
public def annihilatedModulePresheaf
    {C : Type u₁} [Category.{v₁} C] (n m : ℕ)
    (P : Cᵒᵖ ⥤ ModuleCat.{u₂} (ZMod m)) (h : ∀ U (x : P.obj U), n • x = 0) :
    Cᵒᵖ ⥤ ModuleCat.{u₂} (ZMod n) := by
  let (U : Cᵒᵖ) : Module (ZMod n) (P.obj U) := AddCommGroup.zmodModule (h U)
  exact {
    obj U := ModuleCat.of (ZMod n) (P.obj U)
    map i := ModuleCat.ofHom ((P.map i).hom.toAddMonoidHom.toZModLinearMap n)
    map_id U := by ext x; exact ConcreteCategory.congr_hom (P.map_id U) x
    map_comp i j := by ext x; exact ConcreteCategory.congr_hom (P.map_comp i j) x }

/-- A sheaf of `ℤ/mℤ`-modules annihilated by `n`, read as a sheaf of `ℤ/nℤ`-modules. -/
public def annihilatedModuleSheaf
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (n m : ℕ)
    (P : Sheaf J (ModuleCat.{max u₁ v₁ u₂} (ZMod m)))
    (h : ∀ U (x : P.obj.obj U), n • x = 0) :
    Sheaf J (ModuleCat.{max u₁ v₁ u₂} (ZMod n)) where
  obj := annihilatedModulePresheaf n m P.obj h
  property := by
    apply Presheaf.isSheaf_of_isSheaf_comp J _
      (forget₂ (ModuleCat.{max u₁ v₁ u₂} (ZMod n)) AddCommGrpCat)
    change Presheaf.IsSheaf J (P.obj ⋙ forget₂ (ModuleCat (ZMod m)) AddCommGrpCat)
    exact Presheaf.isSheaf_comp_of_isSheaf J P.obj _ P.property

/-- An additive equivalence of `ℤ/nℤ`-modules is a linear one. -/
public def zmodModuleIsoOfAddEquiv (n : ℕ)
    (M N : ModuleCat.{u₁} (ZMod n)) (e : M ≃+ N) : M ≅ N :=
  LinearEquiv.toModuleIso { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }

/-- Restricting the scalars of an annihilated sheaf back along a quotient of coefficient rings
returns the sheaf itself. -/
public def annihilatedModuleSheafIso
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) (n m : ℕ)
    (P : Sheaf J (ModuleCat.{max u₁ v₁ u₂} (ZMod m)))
    (h : ∀ U (x : P.obj.obj U), n • x = 0) (f : ZMod m →+* ZMod n) :
    (sheafCompose J (ModuleCat.restrictScalars.{max u₁ v₁ u₂, 0, 0} f)).obj
        (annihilatedModuleSheaf.{u₁, u₂, v₁} J n m P h) ≅ P where
  hom := ⟨{
    app U := (zmodModuleIsoOfAddEquiv m
      ((ModuleCat.restrictScalars f).obj
        ((annihilatedModuleSheaf.{u₁, u₂, v₁} J n m P h).obj.obj U))
      (P.obj.obj U) (AddEquiv.refl _)).hom
    naturality {U V} i := by ext x; rfl }⟩
  inv := ⟨{
    app U := (zmodModuleIsoOfAddEquiv m
      ((ModuleCat.restrictScalars f).obj
        ((annihilatedModuleSheaf.{u₁, u₂, v₁} J n m P h).obj.obj U))
      (P.obj.obj U) (AddEquiv.refl _)).inv
    naturality {U V} i := by ext x; rfl }⟩
  hom_inv_id := by ext U x; rfl
  inv_hom_id := by ext U x; rfl

/-- Restriction of scalars along a surjective ring homomorphism is full. -/
public theorem restrictScalars_full_of_surjective
    {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{u₃} f).Full where
  map_surjective {M N} g := by
    refine ⟨ModuleCat.ofHom { g.hom.toAddMonoidHom with map_smul' := ?_ }, ?_⟩
    · intro s x
      obtain ⟨r, rfl⟩ := hf s
      exact g.hom.map_smul r x
    · rfl

/-- Composing with a left adjoint is a left adjoint on sheaves. -/
public theorem sheafCompose_isLeftAdjoint
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    (F : D ⥤ E) [J.HasSheafCompose F] [HasWeakSheafify J E]
    [F.IsLeftAdjoint] : (sheafCompose J F).IsLeftAdjoint := by
  let R := sheafCompose J F
  let e : Sheaf.composeAndSheafify J F ≅ R :=
    Functor.associator R (sheafToPresheaf J E) (presheafToSheaf J E) ≪≫
      Functor.isoWhiskerLeft R (asIso (sheafificationAdjunction J E).counit) ≪≫
      Functor.rightUnitor R
  exact Functor.isLeftAdjoint_of_iso e

/-- Two maps out of `R.obj (L.obj M)` agree once they do after the unit, when `R` is full. -/
public theorem adjunction_unit_hom_ext
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Full]
    (M : C) (N : D) (f g : R.obj (L.obj M) ⟶ R.obj N)
    (h : adj.unit.app M ≫ f = adj.unit.app M ≫ g) : f = g := by
  have hh : R.preimage f = R.preimage g := by
    apply (adj.homEquiv M N).injective
    simpa only [adj.homEquiv_unit, Functor.map_preimage] using h
  simpa only [Functor.map_preimage] using congrArg R.map hh

end Annihilated

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- Restriction of scalars along the quotient of consecutive coefficient rings is full. -/
public instance restrictScalarsFunctor_full (n : ℕ) :
    (restrictScalarsFunctor B X ℓ n).Full := by
  let := restrictScalars_full_of_surjective (finiteLevelRingHom ℓ n)
    (ZMod.ringHom_surjective _)
  infer_instance

/-- Restriction of scalars along the quotient of consecutive coefficient rings is a left adjoint
as well as a right one, coextension of scalars being its right adjoint. -/
public instance restrictScalarsFunctor_isLeftAdjoint (n : ℕ) :
    (restrictScalarsFunctor B X ℓ n).IsLeftAdjoint := by
  have : (ModuleCat.restrictScalars.{u + 1, 0, 0} (finiteLevelRingHom ℓ n)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj (finiteLevelRingHom ℓ n)).isLeftAdjoint
  exact sheafCompose_isLeftAdjoint _ _

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The unit of the scalar reduction/restriction adjunction kills `ℓⁿ⁺¹`. -/
public theorem scalarAdjunction_unit_condition (n : ℕ)
    (M : FiniteLevelSheaf B X ℓ (n + 1)) :
    ((ℓ ^ (n + 1)) • (𝟙 M)) ≫ (scalarAdjunction B X ℓ n).unit.app M = 0 := by
  exact nsmul_id_comp_eq_zero _ _ fun U x => ZModModule.char_nsmul_eq_zero (ℓ ^ (n + 1))
    (show (((scalarReductionFunctor B X ℓ n).obj M).obj.obj U) from x)

/-- The unit of the scalar reduction/restriction adjunction at a level `n + 1` sheaf `M`
exhibits the restriction of its reduction as the quotient `M/ℓⁿ⁺¹M`. -/
public def scalarAdjunction_unit_isCokernel (n : ℕ)
    (M : FiniteLevelSheaf B X ℓ (n + 1)) :
    IsColimit (CokernelCofork.ofπ ((scalarAdjunction B X ℓ n).unit.app M)
      (scalarAdjunction_unit_condition B X ℓ n M)) := by
  let r := ℓ ^ (n + 1)
  let J := SmallEtale.topology B X.1 X.property
  let Q := cokernel (r • (𝟙 M))
  have hQ : ∀ U (x : Q.obj.obj U), r • x = 0 := by
    intro U x
    have h := congrArg (fun g : Q ⟶ Q => (g.hom.app U).hom x) (cokernel_nsmul_id M r)
    rwa [sheaf_nsmul_app] at h
  let Q₀ := annihilatedModuleSheaf.{u + 1, u + 1, u} J r (ℓ ^ (n + 2)) Q hQ
  let e : (restrictScalarsFunctor B X ℓ n).obj Q₀ ≅ Q :=
    annihilatedModuleSheafIso.{u + 1, u + 1, u} J r (ℓ ^ (n + 2)) Q hQ (finiteLevelRingHom ℓ n)
  let q : M ⟶ (restrictScalarsFunctor B X ℓ n).obj Q₀ := cokernel.π (r • (𝟙 M)) ≫ e.inv
  let adj := scalarAdjunction B X ℓ n
  let d : (restrictScalarsFunctor B X ℓ n).obj ((scalarReductionFunctor B X ℓ n).obj M) ⟶ Q :=
    (restrictScalarsFunctor B X ℓ n).map ((adj.homEquiv M Q₀).symm q) ≫ e.hom
  have hd : adj.unit.app M ≫ d = cokernel.π (r • (𝟙 M)) := by
    have hq : adj.unit.app M ≫
        (restrictScalarsFunctor B X ℓ n).map ((adj.homEquiv M Q₀).symm q) = q :=
      (adj.homEquiv_unit M Q₀ _).symm.trans ((adj.homEquiv M Q₀).apply_symm_apply q)
    change adj.unit.app M ≫ (_ ≫ e.hom) = _
    rw [← Category.assoc, hq]
    simp [q]
  let β : Q ⟶ (restrictScalarsFunctor B X ℓ n).obj ((scalarReductionFunctor B X ℓ n).obj M) :=
    cokernel.desc (r • (𝟙 M)) (adj.unit.app M) (scalarAdjunction_unit_condition B X ℓ n M)
  have hβ : cokernel.π (r • (𝟙 M)) ≫ β = adj.unit.app M := cokernel.π_desc _ _ _
  have hdb : d ≫ β = 𝟙 _ := by
    apply adjunction_unit_hom_ext adj M ((scalarReductionFunctor B X ℓ n).obj M)
    rw [← Category.assoc, hd, hβ]
    exact (Category.comp_id _).symm
  have : Epi β := epi_of_epi_fac hdb
  have : Epi (adj.unit.app M) := by rw [← hβ]; infer_instance
  apply CokernelCofork.IsColimit.ofπ' _ (scalarAdjunction_unit_condition B X ℓ n M)
  intro H h wh
  exact ⟨d ≫ cokernel.desc (r • (𝟙 M)) h wh, by rw [← Category.assoc, hd, cokernel.π_desc]⟩

omit [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] in
/-- The unit of the scalar reduction/restriction adjunction is an epimorphism. -/
public theorem scalarAdjunction_unit_epi (n : ℕ) (M : FiniteLevelSheaf B X ℓ (n + 1)) :
    Epi ((scalarAdjunction B X ℓ n).unit.app M) :=
  Cofork.IsColimit.epi (scalarAdjunction_unit_isCokernel B X ℓ n M)

variable [Fact ℓ.Prime] [IsNoetherian X.1]

namespace LAdicSheaf

variable {B X ℓ}

/-- The transition map of an ℓ-adic sheaf is an epimorphism. -/
public theorem transition_epi (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    Epi (F.transition n) := by
  let adj := scalarAdjunction B X ℓ n
  let r := FiniteLevelSheaf.scalarReductionMap B X ℓ n (F.level (n + 1)) (F.level n)
    (F.transition n)
  have : IsIso r := F.reduction_isIso n
  have := scalarAdjunction_unit_epi B X ℓ n (F.level (n + 1))
  have ht : F.transition n =
      adj.unit.app (F.level (n + 1)) ≫ (restrictScalarsFunctor B X ℓ n).map r :=
    (FiniteLevelSheaf.scalarReductionMap_comp B X ℓ n _ _ _).symm.trans (adj.homEquiv_unit _ _ r)
  rw [ht]
  infer_instance

/-- The transition map of an ℓ-adic sheaf kills `ℓⁿ⁺¹`. -/
public theorem transition_condition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    ((ℓ ^ (n + 1)) • (𝟙 (F.level (n + 1)))) ≫ F.transition n = 0 := by
  exact nsmul_id_comp_eq_zero _ _ fun U x => ZModModule.char_nsmul_eq_zero (ℓ ^ (n + 1))
    (show (F.level n).obj.obj U from x)

/-- The transition map of an ℓ-adic sheaf exhibits `Fₙ` as the quotient `Fₙ₊₁/ℓⁿ⁺¹Fₙ₊₁`. -/
public def transition_isCokernel (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ (F.transition n) (transition_condition F n)) := by
  let r := FiniteLevelSheaf.scalarReductionMap B X ℓ n (F.level (n + 1)) (F.level n)
    (F.transition n)
  have : IsIso r := F.reduction_isIso n
  refine IsColimit.ofIsoColimit (scalarAdjunction_unit_isCokernel B X ℓ n (F.level (n + 1)))
    (Cofork.ext ((restrictScalarsFunctor B X ℓ n).mapIso (asIso r)) ?_)
  exact ((scalarAdjunction B X ℓ n).homEquiv_unit _ _ r).symm.trans
    (FiniteLevelSheaf.scalarReductionMap_comp B X ℓ n _ _ _)

/-- Multiplication by `ℓ` on a level of an ℓ-adic sheaf kills `ℓⁿ⁺¹`. -/
public theorem verschiebung_condition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    ((ℓ ^ (n + 1)) • (𝟙 (F.level (n + 1)))) ≫ (ℓ • (𝟙 (F.level (n + 1)))) = 0 := by
  rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.comp_id, smul_smul, ← pow_succ]
  exact zmodSheaf_nsmul_id _ _ _

/-- The Verschiebung of an ℓ-adic sheaf: multiplication by `ℓ` on `Fₙ₊₁` kills `ℓⁿ⁺¹`, so it
factors through the transition map. -/
public def verschiebung (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    (restrictScalarsFunctor B X ℓ n).obj (F.level n) ⟶ F.level (n + 1) :=
  (CokernelCofork.IsColimit.desc' (transition_isCokernel F n) (ℓ • (𝟙 (F.level (n + 1))))
    (verschiebung_condition F n)).1

/-- The transition map followed by the Verschiebung is multiplication by `ℓ`. -/
public theorem transition_verschiebung (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    F.transition n ≫ verschiebung F n = ℓ • (𝟙 (F.level (n + 1))) :=
  (CokernelCofork.IsColimit.desc' (transition_isCokernel F n) (ℓ • (𝟙 (F.level (n + 1))))
    (verschiebung_condition F n)).2

/-- The Verschiebung followed by the transition map is multiplication by `ℓ`. -/
public theorem verschiebung_transition (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    verschiebung F n ≫ F.transition n =
      ℓ • (𝟙 ((restrictScalarsFunctor B X ℓ n).obj (F.level n))) := by
  have := transition_epi F n
  apply (cancel_epi (F.transition n)).1
  rw [← Category.assoc, transition_verschiebung, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp, Category.comp_id]

end LAdicSheaf

end Stacks.EtaleCohomology

end
