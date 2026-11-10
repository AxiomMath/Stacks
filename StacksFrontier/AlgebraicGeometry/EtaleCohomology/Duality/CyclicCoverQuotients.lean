module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CyclicCoverFiltration

/-!
# The first two quotients of the free sheaf on the torsor of an extension

Let `Λ = ℤ/ℓ` with `ℓ` prime, `0 → Λ_X --i--> E --ε--> Λ_X → 0` an extension on the small étale
site of `X`, `P = ε⁻¹(1)` its torsor with translation `τ`, and `s = Λ[τ] - 1` on the free sheaf
`Λ[P]` (`Stacks.EtaleCohomology.ExtensionTorsor.shift`). The inclusion `P ⊂ E` extends to
`φ : Λ[P] → E`, and `ε̃ = ε ∘ φ` sends every generator `[p]` to `1`. Since `τ p = i(1) + p`,
`φ ∘ s = i ∘ ε̃`. Then `ε̃` identifies `coker s` with `Λ_X`, and `φ` identifies `coker s²`
with `E`.

## Main definitions

* `Stacks.EtaleCohomology.ExtensionTorsor.generator`: the generator `[p]` of `Λ[P]`.
* `Stacks.EtaleCohomology.ExtensionTorsor.extensionMap`: `φ : Λ[P] → E`.
* `Stacks.EtaleCohomology.ExtensionTorsor.augmentation`: `ε̃ : Λ[P] → Λ_X`.

## Main results

* `Stacks.EtaleCohomology.ExtensionTorsor.shift_comp_extensionMap`: `φ ∘ s = i ∘ ε̃`.
* `Stacks.EtaleCohomology.ExtensionTorsor.cokernelShiftIso`: `coker s ≅ Λ_X`.
* `Stacks.EtaleCohomology.ExtensionTorsor.cokernelShiftSqIso`: `coker s² ≅ E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.ExtensionTorsor

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : EtaleModules.{u, 0} (ZMod ℓ) X}
  (i : unitSheaf ℓ ⟶ E) (ε : E ⟶ unitSheaf ℓ) (w : i ≫ ε = 0)

section Generators

/-- The inclusion of the torsor into the underlying sheaf of sets of `E`. -/
def torsorIncl : torsor i ε w ⟶
    (sheafCompose X.smallEtaleTopology (forget (ModuleCat.{u + 1} (ZMod ℓ)))).obj E :=
  ⟨{ app := fun _ => TypeCat.ofHom fun p => p.1
     naturality := fun _ _ _ => rfl }⟩

/-- The generator `[p]` of `Λ[P]` attached to a section `p` of the torsor. -/
def generator {V : X.Etale} (p : (torsor i ε w).obj.obj (op V)) :
    (freeTorsor (i := i) (ε := ε) (w := w)).obj.obj (op V) :=
  ((etaleModuleFreeAdj (ZMod ℓ) X).unit.app (torsor i ε w)).hom.app (op V) p

variable {i ε w}

/-- A map out of `Λ[P]` evaluated on a generator is its adjoint evaluated on the section. -/
theorem apply_generator {M : EtaleModules.{u, 0} (ZMod ℓ) X}
    (φ : freeTorsor (i := i) (ε := ε) (w := w) ⟶ M) {V : X.Etale}
    (p : (torsor i ε w).obj.obj (op V)) :
    φ.hom.app (op V) (generator i ε w p) =
      (((etaleModuleFreeAdj (ZMod ℓ) X).homEquiv _ _ φ).hom.app (op V) p) := by
  rw [Adjunction.homEquiv_unit]
  rfl

/-- **Maps out of `Λ[P]` are determined by their values on the generators.** -/
theorem hom_ext_generator {M : EtaleModules.{u, 0} (ZMod ℓ) X}
    {φ ψ : freeTorsor (i := i) (ε := ε) (w := w) ⟶ M}
    (h : ∀ (V : X.Etale) (p : (torsor i ε w).obj.obj (op V)),
      φ.hom.app (op V) (generator i ε w p) = ψ.hom.app (op V) (generator i ε w p)) : φ = ψ := by
  apply ((etaleModuleFreeAdj (ZMod ℓ) X).homEquiv _ _).injective
  apply Sheaf.hom_ext
  ext V p
  exact (apply_generator φ (V := V.unop) p).symm.trans
    ((h V.unop p).trans (apply_generator ψ (V := V.unop) p))

/-- `Λ[f]` sends the generator `[p]` to `[f p]`. -/
theorem map_generator (f : torsor i ε w ⟶ torsor i ε w) {V : X.Etale}
    (p : (torsor i ε w).obj.obj (op V)) :
    ((etaleModuleFree (ZMod ℓ) X).map f).hom.app (op V) (generator i ε w p) =
      generator i ε w (f.hom.app (op V) p) := by
  rw [apply_generator, ← Category.comp_id ((etaleModuleFree (ZMod ℓ) X).map f),
    Adjunction.homEquiv_naturality_left]
  rfl

variable (i ε w)

/-- **The map `φ : Λ[P] → E`** extending the inclusion `P ⊂ E`. -/
def extensionMap : freeTorsor (i := i) (ε := ε) (w := w) ⟶ E :=
  ((etaleModuleFreeAdj (ZMod ℓ) X).homEquiv _ _).symm (torsorIncl i ε w)

/-- **The augmentation `ε̃ = ε ∘ φ : Λ[P] → Λ_X`.** -/
def augmentation : freeTorsor (i := i) (ε := ε) (w := w) ⟶ unitSheaf ℓ :=
  extensionMap i ε w ≫ ε

variable {i ε w}

/-- **`φ [p] = p`.** -/
theorem extensionMap_generator {V : X.Etale} (p : (torsor i ε w).obj.obj (op V)) :
    (extensionMap i ε w).hom.app (op V) (generator i ε w p) = p.1 := by
  rw [apply_generator, extensionMap, Equiv.apply_symm_apply]
  rfl

/-- **`ε̃ [p] = 1`.** -/
theorem augmentation_generator {V : X.Etale} (p : (torsor i ε w).obj.obj (op V)) :
    (augmentation i ε w).hom.app (op V) (generator i ε w p) = oneSection ℓ V := by
  change ε.hom.app (op V) ((extensionMap i ε w).hom.app (op V) (generator i ε w p)) = _
  rw [extensionMap_generator]
  exact torsor_spec i ε w p

end Generators

variable {i ε w} (hS : (ShortComplex.mk i ε w).ShortExact)

/-- **`s [p] = [τ p] - [p]`.** -/
theorem shift_generator {V : X.Etale} (p : (torsor i ε w).obj.obj (op V)) :
    (shift hS).asHom.hom.app (op V) (generator i ε w p) =
      generator i ε w ((translation hS).asHom.hom.app (op V) p) - generator i ε w p := by
  rw [← map_generator]
  rfl

/-- **`φ ∘ s = i ∘ ε̃`**: `φ(s [p]) = (i(1) + p) - p = i(1) = i(ε̃ [p])`. -/
theorem shift_comp_extensionMap :
    (shift hS).asHom ≫ extensionMap i ε w = augmentation i ε w ≫ i := by
  refine hom_ext_generator fun V p => ?_
  change (extensionMap i ε w).hom.app (op V) ((shift hS).asHom.hom.app (op V) (generator i ε w p)) =
    i.hom.app (op V) ((augmentation i ε w).hom.app (op V) (generator i ε w p))
  rw [shift_generator, map_sub, extensionMap_generator, extensionMap_generator,
    augmentation_generator, translation_app]
  exact add_sub_cancel_right (i.hom.app (op V) (oneSection ℓ V)) (p.1 : E.obj.obj (op V))

/-- `ε̃ ∘ s = 0`. -/
theorem shift_comp_augmentation : (shift hS).asHom ≫ augmentation i ε w = 0 := by
  rw [augmentation, ← Category.assoc, shift_comp_extensionMap, Category.assoc, w,
    Limits.comp_zero]

/-- `φ ∘ s² = 0`. -/
theorem shift_sq_comp_extensionMap : (shift hS ^ 2).asHom ≫ extensionMap i ε w = 0 := by
  rw [pow_two, End.mul_asHom, Category.assoc, shift_comp_extensionMap, ← Category.assoc,
    shift_comp_augmentation, Limits.zero_comp]

/-- If `a ∘ s = 0`, the kernel of `s` is a line, `a` is nonzero and its target is a line, then `a`
is onto and `ker a = im s`. -/
theorem ker_eq_range_of_finrank_ker_eq_one {K M L : Type*} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [AddCommGroup L] [Module K L] (s : M →ₗ[K] M) (a : M →ₗ[K] L)
    (has : a ∘ₗ s = 0) (hs : Module.finrank K (LinearMap.ker s) = 1)
    (hL : Module.finrank K L = 1) (ha : a ≠ 0) :
    LinearMap.ker a = LinearMap.range s ∧ LinearMap.range a = ⊤ := by
  have : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  have hrs := LinearMap.finrank_range_add_finrank_ker s
  have hra := LinearMap.finrank_range_add_finrank_ker a
  have htop : LinearMap.range a = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 : Module.finrank K (LinearMap.range a) ≤ 1 := hL ▸ Submodule.finrank_le _
    have h2 : 0 < Module.finrank K (LinearMap.range a) := Nat.pos_of_ne_zero fun h =>
      ha (LinearMap.range_eq_bot.1 (Submodule.finrank_eq_zero.1 h))
    omega
  refine ⟨(Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm, htop⟩
  · rintro _ ⟨x, rfl⟩
    exact LinearMap.congr_fun has x
  · rw [htop, finrank_top] at hra
    omega

/-- The map `coker s → Λ_X` induced by `ε̃`. -/
def cokernelShiftDesc : cokernel (shift hS).asHom ⟶ unitSheaf ℓ :=
  cokernel.desc _ (augmentation i ε w) (shift_comp_augmentation hS)

/-- The map `coker s² → E` induced by `φ`. -/
def cokernelShiftSqDesc : cokernel (shift hS ^ 2).asHom ⟶ E :=
  cokernel.desc _ (extensionMap i ε w) (shift_sq_comp_extensionMap hS)

section Fibre

/-- `ModuleCat.{u + 1} (ZMod ℓ)` has colimits indexed by categories in `Type (u + 1)`. -/
local instance : HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} (ZMod ℓ)

/-- `ModuleCat.{u + 1} (ZMod ℓ)` has limits indexed by categories in `Type (u + 1)`. -/
local instance : HasLimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
  ModuleCat.instHasLimitsOfSize.{u + 1, u + 1, 0}

/-- The forgetful functor on `ModuleCat.{u + 1} (ZMod ℓ)` preserves filtered colimits. -/
local instance : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
    (forget (ModuleCat.{u + 1, 0} (ZMod ℓ))) :=
  comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1})
    (forget AddCommGrpCat.{u + 1})

variable (Φ : X.smallEtaleTopology.Point.{u + 1})

/-- The fibre of `Λ_X` is a line. -/
theorem finrank_sheafFiber_unitSheaf :
    Module.finrank (ZMod ℓ) ((Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).obj
      (unitSheaf ℓ)) = 1 := by
  refine ((fiberUnitIso (ℓ := ℓ) Φ).toLinearEquiv.finrank_eq).trans ?_
  change Module.finrank (ZMod ℓ) (ULift (ZMod ℓ)) = 1
  rw [ULift.moduleEquiv.finrank_eq, Module.finrank_self]

include hS in
/-- **`ε̃` is nonzero on every fibre.** -/
theorem sheafFiber_map_augmentation_ne_zero :
    (Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map (augmentation i ε w) ≠ 0 := by
  obtain ⟨t⟩ := nonempty_presheafFiber_torsor hS Φ
  obtain ⟨V, y, p, -⟩ :=
    Φ.toPresheafFiber_jointly_surjective (A := Type (u + 1)) (P := (torsor i ε w).obj) t
  intro h
  have h1 := ConcreteCategory.congr_hom
    (Φ.toPresheafFiber_naturality (A := ModuleCat.{u + 1} (ZMod ℓ)) (augmentation i ε w).hom V y)
    (generator i ε w p)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, augmentation_generator] at h1
  have h2 : Φ.presheafFiber.map (augmentation i ε w).hom = 0 := h
  rw [h2] at h1
  have h3 := fiberUnitIso_toPresheafFiber_oneSection (ℓ := ℓ) Φ y
  rw [← h1] at h3
  have h4 := congrArg ULift.down h3
  simp at h4

/-- **On every fibre, `coker s → Λ_X` is bijective.** -/
theorem bijective_sheafFiber_map_cokernelShiftDesc :
    Function.Bijective
      ((Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map (cokernelShiftDesc hS)) := by
  have := finiteDimensional_sheafFiber_freeTorsor hS Φ
  set F := Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))
  obtain ⟨hker, htop⟩ := ker_eq_range_of_finrank_ker_eq_one (F.map (shift hS).asHom).hom
    (F.map (augmentation i ε w)).hom (by
      rw [← ModuleCat.hom_comp, ← Functor.map_comp, shift_comp_augmentation, Functor.map_zero]
      rfl)
    (finrank_ker_sheafFiber_map_shift hS Φ) (finrank_sheafFiber_unitSheaf Φ) (fun h =>
      sheafFiber_map_augmentation_ne_zero hS Φ (ModuleCat.hom_ext h))
  have hfac : F.map (cokernel.π (shift hS).asHom) ≫ F.map (cokernelShiftDesc hS) =
      F.map (augmentation i ε w) := by
    rw [← Functor.map_comp, cokernelShiftDesc, cokernel.π_desc]
  have hπ : Function.Surjective (F.map (cokernel.π (shift hS).asHom)) := by
    rw [← ModuleCat.epi_iff_surjective]
    infer_instance
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨x, rfl⟩ := hπ y
    have hx : x ∈ LinearMap.ker (F.map (augmentation i ε w)).hom := by
      rwa [LinearMap.mem_ker, ← hfac, ModuleCat.comp_apply]
    rw [hker] at hx
    obtain ⟨z, rfl⟩ := hx
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, cokernel.condition, Functor.map_zero]
    rfl
  · intro y
    obtain ⟨x, hx⟩ : y ∈ LinearMap.range (F.map (augmentation i ε w)).hom := htop ▸ trivial
    exact ⟨F.map (cokernel.π (shift hS).asHom) x, by rwa [← ModuleCat.comp_apply, hfac]⟩

end Fibre

/-- **`ε̃` identifies `coker s` with `Λ_X`.** -/
theorem isIso_cokernelShiftDesc : IsIso (cokernelShiftDesc hS) := by
  have : GrothendieckTopology.HasEnoughPoints.{u + 1} X.smallEtaleTopology :=
    Scheme.hasEnoughPoints_smallEtaleTopology.{0, u} X
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty X.smallEtaleTopology
  have : HasColimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1, 0} (ZMod ℓ)) :=
    ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} (ZMod ℓ)
  have : PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{u + 1, 0} (ZMod ℓ))) :=
    etaleModules_preservesFilteredColimits_forget.{u} (ZMod ℓ)
  have : ∀ q : P.FullSubcategory, IsIso
      ((q.obj.sheafFiber (A := ModuleCat.{u + 1} (ZMod ℓ))).map (cokernelShiftDesc hS)) :=
    fun q => (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_sheafFiber_map_cokernelShiftDesc hS q.obj)
  exact (hP.jointlyReflectIsomorphisms (ModuleCat.{u + 1} (ZMod ℓ))).isIso _

/-- **`coker s ≅ Λ_X`**, via the augmentation. -/
def cokernelShiftIso : cokernel (shift hS).asHom ≅ unitSheaf ℓ :=
  haveI := isIso_cokernelShiftDesc hS
  asIso (cokernelShiftDesc hS)

/-- The morphism from `0 → coker s → coker s² → coker s → 0` to the extension, given by `ε̃`,
`φ` and `ε̃`. -/
def cokernelPowShortComplexHom :
    Stacks.Abelian.cokernelPowShortComplex (shift hS) 1 ⟶ ShortComplex.mk i ε w where
  τ₁ := cokernelShiftDesc hS
  τ₂ := cokernelShiftSqDesc hS
  τ₃ := (cokernelIsoOfEq (congrArg End.asHom (pow_one (shift hS)))).hom ≫ cokernelShiftDesc hS
  comm₁₂ := by
    change cokernelShiftDesc hS ≫ i =
      Stacks.Abelian.cokernelPowι (shift hS) 1 ≫ cokernelShiftSqDesc hS
    rw [← cancel_epi (cokernel.π (shift hS).asHom), ← Category.assoc, cokernelShiftDesc,
      cokernel.π_desc, Stacks.Abelian.π_cokernelPowι_assoc, pow_one, cokernelShiftSqDesc,
      cokernel.π_desc, shift_comp_extensionMap]
  comm₂₃ := by
    change cokernelShiftSqDesc hS ≫ ε = Stacks.Abelian.cokernelPowq (shift hS) 1 ≫
      (cokernelIsoOfEq (congrArg End.asHom (pow_one (shift hS)))).hom ≫ cokernelShiftDesc hS
    rw [← cancel_epi (cokernel.π (shift hS ^ 2).asHom), ← Category.assoc, cokernelShiftSqDesc,
      cokernel.π_desc]
    change extensionMap i ε w ≫ ε = cokernel.π (shift hS ^ (1 + 1)).asHom ≫
      Stacks.Abelian.cokernelPowq (shift hS) 1 ≫
        (cokernelIsoOfEq (congrArg End.asHom (pow_one (shift hS)))).hom ≫ cokernelShiftDesc hS
    rw [Stacks.Abelian.π_cokernelPowq_assoc, π_comp_cokernelIsoOfEq_hom_assoc, cokernelShiftDesc,
      cokernel.π_desc]
    rfl

/-- **`φ` identifies `coker s²` with `E`.** -/
theorem isIso_cokernelShiftSqDesc : IsIso (cokernelShiftSqDesc hS) := by
  have : IsIso (cokernelPowShortComplexHom hS).τ₁ := isIso_cokernelShiftDesc hS
  have : IsIso (cokernelPowShortComplexHom hS).τ₃ :=
    Iso.isIso_hom (cokernelIsoOfEq (congrArg End.asHom (pow_one (shift hS))) ≪≫ cokernelShiftIso hS)
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ (cokernelPowShortComplexHom hS)
    (cokernelPowShortComplex_shift_shortExact hS (Fact.out : ℓ.Prime).one_lt) hS

/-- **`coker s² ≅ E`**, via `φ`. -/
def cokernelShiftSqIso : cokernel (shift hS ^ 2).asHom ≅ E :=
  haveI := isIso_cokernelShiftSqDesc hS
  asIso (cokernelShiftSqDesc hS)

end Stacks.EtaleCohomology.ExtensionTorsor

end
