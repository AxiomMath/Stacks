module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LevelDichotomyBasePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PurityComplexBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules

/-!
# Short exact sequences from stable submodules of the monodromy

Let `X` be a scheme, `j : V ⟶ X` an open immersion with `V` connected, `v̄` a geometric point of
`V`, `Λ` a finite commutative ring and `G` a sheaf of `Λ`-modules on `X_étale` whose restriction
`j⁻¹G` is locally constant of finite type. A `π₁(V, v̄)`-stable submodule `W` of the monodromy
module `M = (j⁻¹G)_v̄` (Tag 0DV5) gives a short exact sequence `0 ⟶ A ⟶ G ⟶ Q ⟶ 0` on `X`: with
`Q_V` the lisse sheaf of `M / W` and `b : j⁻¹G ⟶ Q_V` the quotient map, `Q` is the image of the
adjoint `G ⟶ j_* Q_V` of `b` and `A` its kernel
(`Stacks.EtaleCohomology.exists_shortExact_of_monodromy_submodule`). Then `j⁻¹A` and `j⁻¹Q` are
locally constant of finite type, `Q` has no sections supported off `V`, an integer killing `A`
kills `W`, and an integer killing `Q` maps `M` into `W`. Moreover a subsheaf of a constructible
sheaf on a Noetherian scheme is constructible
(`Stacks.EtaleCohomology.isConstructibleEtaleModule_of_mono_small`).

## Main definitions

* `Stacks.EtaleCohomology.finiteTypeContinuousModuleQuotient`: the quotient of a finite
  continuous module by a stable submodule.
* `Stacks.EtaleCohomology.finiteTypeContinuousModuleQuotientπ`: the projection onto it.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_mono_small`: a subsheaf of a
  constructible sheaf on a Noetherian scheme is constructible.
* `Stacks.EtaleCohomology.exists_shortExact_of_monodromy_submodule`: the short exact sequence
  attached to a stable submodule of the monodromy.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.GroupCohomology

universe u v w

namespace Stacks.EtaleCohomology

section Module

variable {Λ : Type} [CommRing Λ] [Finite Λ] {H : Type v} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H]

/-- **The quotient of a finite continuous module by a stable submodule.** -/
def finiteTypeContinuousModuleQuotient (P : FiniteTypeContinuousModule.{0, v, w} Λ H)
    (W : Submodule Λ P.obj.obj.obj.V) (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).hom x ∈ W) :
    FiniteTypeContinuousModule.{0, v, w} Λ H :=
  haveI : Finite (ToType P.obj.obj.obj.V) := (moduleCat_isFG_iff_finite Λ _).mp P.property
  haveI : Finite (P.obj.obj.obj.V ⧸ W) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective W)
  ⟨ofRepresentation (R := Λ) (M := P.obj.obj.obj.V ⧸ W)
      { toFun := fun h ↦ W.mapQ W (P.obj.obj.obj.ρ h).hom (fun x hx ↦ hW h x hx)
        map_one' := by
          ext x
          change Submodule.Quotient.mk ((P.obj.obj.obj.ρ 1).hom x) = Submodule.Quotient.mk x
          rw [map_one]
          rfl
        map_mul' := fun g g' ↦ by
          ext x
          change Submodule.Quotient.mk ((P.obj.obj.obj.ρ (g * g')).hom x) =
            Submodule.Quotient.mk ((P.obj.obj.obj.ρ g).hom ((P.obj.obj.obj.ρ g').hom x))
          rw [map_mul]
          rfl }
      ((isContinuous_actionOfRepresentation_iff _).2 fun z ↦ by
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective W z
        have hst := isOpen_stabilizer Λ H P.obj y
        rw [isOpen_iff_mem_nhds]
        intro g hg
        have hmem : (fun s ↦ g⁻¹ * s) ⁻¹'
            {s : H | (P.obj.obj.obj.ρ s).hom y = y} ∈ nhds g :=
          (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
            (hst.mem_nhds (by
              change (P.obj.obj.obj.ρ (g⁻¹ * g)).hom y = y
              rw [inv_mul_cancel, map_one]
              rfl))
        filter_upwards [hmem] with s hs
        have hs' : (P.obj.obj.obj.ρ (g⁻¹ * s)).hom y = y := hs
        have hsg : (P.obj.obj.obj.ρ s).hom y = (P.obj.obj.obj.ρ g).hom y := by
          rw [show s = g * (g⁻¹ * s) by group, map_mul]
          change (P.obj.obj.obj.ρ g).hom ((P.obj.obj.obj.ρ (g⁻¹ * s)).hom y) = _
          rw [hs']
        change Submodule.Quotient.mk ((P.obj.obj.obj.ρ s).hom y) = Submodule.Quotient.mk y
        rw [hsg]
        exact hg),
    (ModuleCat.isFG_iff _).2
      (show Module.Finite Λ (P.obj.obj.obj.V ⧸ W) from Module.Finite.of_finite)⟩

/-- The projection onto `Stacks.EtaleCohomology.finiteTypeContinuousModuleQuotient`. -/
def finiteTypeContinuousModuleQuotientπ (P : FiniteTypeContinuousModule.{0, v, w} Λ H)
    (W : Submodule Λ P.obj.obj.obj.V) (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).hom x ∈ W) :
    P ⟶ finiteTypeContinuousModuleQuotient P W hW :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    ⟨ModuleCat.ofHom W.mkQ, fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)⟩))

/-- The projection `finiteTypeContinuousModuleQuotientπ P W hW` sends `x` to its class mod `W`. -/
theorem finiteTypeContinuousModuleQuotientπ_apply (P : FiniteTypeContinuousModule.{0, v, w} Λ H)
    (W : Submodule Λ P.obj.obj.obj.V) (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).hom x ∈ W)
    (x : P.obj.obj.obj.V) :
    (finiteTypeContinuousModuleQuotientπ P W hW).hom.hom.hom.hom.hom x =
      Submodule.Quotient.mk x := rfl

/-- The inclusion of a stable submodule composed with the projection onto the quotient vanishes. -/
private theorem finiteTypeContinuousModuleOfStableι_comp_quotientπ
    (P : FiniteTypeContinuousModule.{0, v, w} Λ H) (W : Submodule Λ P.obj.obj.obj.V)
    (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).hom x ∈ W) :
    finiteTypeContinuousModuleOfStableι P W hW ≫ finiteTypeContinuousModuleQuotientπ P W hW =
      0 := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  refine Action.hom_ext _ _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
  exact (Submodule.Quotient.mk_eq_zero W).2 x.2

omit [Finite Λ] [IsTopologicalGroup H] in
/-- An integer killing a map of finite-type continuous modules kills the underlying linear map. -/
private theorem nsmul_hom_apply_eq_zero_of_nsmul_eq_zero
    {P P' : FiniteTypeContinuousModule.{0, v, w} Λ H} (f : P ⟶ P') (e : ℕ) (h : e • f = 0)
    (x : P.obj.obj.obj.V) : e • f.hom.hom.hom.hom.hom x = 0 := by
  let Uf : FiniteTypeContinuousModule.{0, v, w} Λ H ⥤ ModuleCat.{w} Λ :=
    finiteTypeContinuousModuleι Λ H ⋙ Stacks.Injectives.continuousModuleUnderlying Λ H
  have : (finiteTypeContinuousModuleι.{0, v, w} Λ H).Additive := ⟨fun {_ _ _ _} ↦ rfl⟩
  have := additive_continuousModuleToModuleCat.{0, v, w} Λ H
  have : Uf.Additive := inferInstance
  have h3 := congrArg Uf.map h
  rw [Functor.map_nsmul, Functor.map_zero] at h3
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h3) x

/-- An integer killing the inclusion of a stable submodule kills the submodule. -/
theorem nsmul_eq_zero_of_nsmul_finiteTypeContinuousModuleOfStableι
    (P : FiniteTypeContinuousModule.{0, v, w} Λ H) (W : Submodule Λ P.obj.obj.obj.V)
    (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).hom x ∈ W) (e : ℕ)
    (h : e • finiteTypeContinuousModuleOfStableι P W hW = 0) : ∀ x ∈ W, e • x = 0 :=
  fun x hx ↦ nsmul_hom_apply_eq_zero_of_nsmul_eq_zero _ e h ⟨x, hx⟩

/-- An integer killing the projection onto the quotient by a stable submodule maps everything into
the submodule. -/
theorem nsmul_mem_of_nsmul_finiteTypeContinuousModuleQuotientπ
    (P : FiniteTypeContinuousModule.{0, v, w} Λ H) (W : Submodule Λ P.obj.obj.obj.V)
    (hW : ∀ h, ∀ x ∈ W, (P.obj.obj.obj.ρ h).hom x ∈ W) (e : ℕ)
    (h : e • finiteTypeContinuousModuleQuotientπ P W hW = 0) : ∀ x, e • x ∈ W :=
  fun x ↦ (Submodule.Quotient.mk_eq_zero W).1 (nsmul_hom_apply_eq_zero_of_nsmul_eq_zero _ e h x)

end Module

section Equivalence

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]

/-- If `e • (E⁻¹ f ≫ η⁻¹)` vanishes for an additive inverse `E⁻¹` of an equivalence, so does
`e • f`. -/
theorem nsmul_eq_zero_of_nsmul_inverse_map_comp_unitInv (E : C ≌ D) [E.inverse.Additive]
    {Y : D} {X : C} (f : Y ⟶ E.functor.obj X) (e : ℕ)
    (h : e • (E.inverse.map f ≫ E.unitInv.app X) = 0) : e • f = 0 := by
  apply E.inverse.map_injective
  rw [Functor.map_nsmul, Functor.map_zero]
  have h1 : E.inverse.map f = (E.inverse.map f ≫ E.unitInv.app X) ≫ E.unit.app X := by
    change E.inverse.map f = (E.inverse.map f ≫ E.unitIso.inv.app X) ≫ E.unitIso.hom.app X
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  rw [h1, ← Preadditive.nsmul_comp, h, zero_comp]

/-- If `e • (η ≫ E⁻¹ f)` vanishes for an additive inverse `E⁻¹` of an equivalence, so does
`e • f`. -/
theorem nsmul_eq_zero_of_nsmul_unit_comp_inverse_map (E : C ≌ D) [E.inverse.Additive]
    {X : C} {Y : D} (f : E.functor.obj X ⟶ Y) (e : ℕ)
    (h : e • (E.unit.app X ≫ E.inverse.map f) = 0) : e • f = 0 := by
  apply E.inverse.map_injective
  rw [Functor.map_nsmul, Functor.map_zero]
  have h1 : E.inverse.map f = E.unitInv.app X ≫ E.unit.app X ≫ E.inverse.map f := by
    change E.inverse.map f = E.unitIso.inv.app X ≫ E.unitIso.hom.app X ≫ E.inverse.map f
    rw [Iso.inv_hom_id_app_assoc]
  rw [h1, ← Preadditive.comp_nsmul, h, comp_zero]

/-- The image of the adjoint `adj.homEquiv A B b` under `F` followed by the counit is `b`. -/
private theorem map_homEquiv_comp_counit {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive]
    {A : C} {B : D}
    (b : F.obj A ⟶ B) : F.map (adj.homEquiv A B b) ≫ adj.counit.app B = b := by
  simpa only [Equiv.symm_apply_apply] using (adj.homEquiv_counit (g := adj.homEquiv A B b)).symm

/-- If `e` kills the adjoint `adj.homEquiv A B b` of `b`, for an additive left adjoint, it kills
`b`. -/
theorem nsmul_eq_zero_of_nsmul_homEquiv {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive]
    {A : C} {B : D} (b : F.obj A ⟶ B) (e : ℕ) (h : e • adj.homEquiv A B b = 0) : e • b = 0 := by
  rw [← map_homEquiv_comp_counit adj b, ← Preadditive.nsmul_comp, ← Functor.map_nsmul, h,
    Functor.map_zero, zero_comp]

/-- If `e` kills the kernel of `f` and `g ≫ L.map f = 0` for an additive functor `L` preserving
the kernel of `f`, then `e` kills `g`. -/
private theorem nsmul_eq_zero_of_comp_map_eq_zero (L : C ⥤ D) [L.Additive] {X Y : C} (f : X ⟶ Y)
    [HasKernel f] [HasKernel (L.map f)] [PreservesLimit (parallelPair f 0) L] {Z : D}
    (g : Z ⟶ L.obj X) (hg : g ≫ L.map f = 0) (e : ℕ) (he : e • 𝟙 (kernel f) = 0) : e • g = 0 := by
  have hk : (kernel.lift (L.map f) g hg ≫ (PreservesKernel.iso L f).inv) ≫ L.map (kernel.ι f) =
      g := by
    simp only [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]
  rw [← hk, ← Preadditive.comp_nsmul, ← Functor.map_nsmul, ← Category.id_comp (kernel.ι f),
    ← Preadditive.nsmul_comp, he, zero_comp, Functor.map_zero, comp_zero]

omit [Preadditive C] [Preadditive D] in
/-- An object with a monomorphism into `G.obj Y`, for a right adjoint `G`, has a monic unit. -/
private theorem mono_unit_app_of_mono_to_obj {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {Q : C} {Y : D}
    (ι : Q ⟶ G.obj Y) [Mono ι] : Mono (adj.unit.app Q) := by
  have h1 : ι ≫ adj.unit.app (G.obj Y) = adj.unit.app Q ≫ (F ⋙ G).map ι :=
    adj.unit.naturality ι
  have : IsSplitMono (adj.unit.app (G.obj Y)) :=
    IsSplitMono.mk' ⟨G.map (adj.counit.app Y), adj.right_triangle_components Y⟩
  have hc : Mono (ι ≫ adj.unit.app (G.obj Y)) := inferInstance
  rw [h1] at hc
  exact mono_of_mono _ ((F ⋙ G).map ι)

end Equivalence

section LocallyConstant

/-- A finite-type locally constant module sheaf is locally constant with finite values. -/
private theorem isLocallyConstantWith_finite_of_isFiniteTypeLocallyConstant {R : Type*} [Ring R]
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)] {F : Sheaf J (ModuleCat.{w} R)}
    (h : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J F) :
    Stacks.ConstantSheaf.IsLocallyConstantWith R J (fun E => Module.Finite R E) F := fun U ↦ by
  obtain ⟨I, V, f, hc, ht⟩ := h U
  exact ⟨I, V, f, hc, fun i ↦ by
    obtain ⟨E, hE, he⟩ := ht i
    exact ⟨E, (ModuleCat.isFG_iff _).1 hE, he⟩⟩

end LocallyConstant

section Constructible

variable {Λ : Type} [CommRing Λ] [IsNoetherianRing Λ]

/-- **A subsheaf of a constructible sheaf is constructible.** On a Noetherian scheme a subsheaf of
a constructible sheaf of `Λ`-modules is constructible, for a Noetherian coefficient ring
`Λ : Type` ([Stacks, Tag 09BH] (3)). -/
theorem isConstructibleEtaleModule_of_mono_small {X : Scheme.{u}} [IsNoetherian X]
    {G F : EtaleModules.{u, 0} Λ X} (i : G ⟶ F) [Mono i]
    (hF : IsConstructibleEtaleModule Λ F) : IsConstructibleEtaleModule Λ G := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have : IsNoetherian (B.obj X hX).obj := ‹IsNoetherian X›
  have : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} Λ) :=
    ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0}
  have : HasSheafify (SmallEtale.topology B X hX) (ModuleCat.{u + 1} Λ) :=
    Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1} _ Λ
  have : Mono ((etaleModuleToBoundedSite.{u, 0} Λ B hX).map i) :=
    (etaleModuleToBoundedSite.{u, 0} Λ B hX).map_mono i
  exact isConstructibleModuleSheaf_of_mono' B Λ (B.obj X hX)
    ((etaleModuleToBoundedSite.{u, 0} Λ B hX).map i) hF

end Constructible

section Sheaf

attribute [local instance] moduleCat_hasLimitsOfSize etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable {Λ : Type} [CommRing Λ] [Finite Λ]

/-- **A map from `j⁻¹G` to a locally constant sheaf gives a short exact sequence on `X`.** Let
`j : V ⟶ X` be an open immersion, `G` a sheaf on `X` with `j⁻¹G` locally constant of finite type,
and `b : j⁻¹G ⟶ Q_V` a map to a locally constant sheaf of finite type. With `Q` the image of the
adjoint `G ⟶ j_* Q_V` of `b` and `A` its kernel, `0 ⟶ A ⟶ G ⟶ Q ⟶ 0` is short exact, `j⁻¹A` and
`j⁻¹Q` are locally constant with finite values, `Q ⟶ j_* j⁻¹ Q` is a monomorphism, an integer
killing `A` kills every map whose composite with `b` vanishes, and an integer killing `Q` kills
`b`. -/
private theorem exists_shortExact_of_inverseImage_hom {X V : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j]
    (G : EtaleModules.{u, 0} Λ X) {QV : EtaleModules.{u, 0} Λ V}
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ V.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ j).obj G))
    (hQV : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ V.smallEtaleTopology QV)
    (b : (etaleModuleInverseImage.{u, 0} Λ j).obj G ⟶ QV) :
    ∃ (A Q : EtaleModules.{u, 0} Λ X) (α : A ⟶ G) (β : G ⟶ Q) (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact ∧
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
        (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ j).obj A) ∧
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
        (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ j).obj Q) ∧
      Mono ((etaleModuleInverseImageAdj.{u, 0} Λ j).unit.app Q) ∧
      (∀ e : ℕ, e • 𝟙 A = 0 → ∀ {Z : EtaleModules.{u, 0} Λ V}
        (g : Z ⟶ (etaleModuleInverseImage.{u, 0} Λ j).obj G), g ≫ b = 0 → e • g = 0) ∧
      (∀ e : ℕ, e • 𝟙 Q = 0 → e • b = 0) := by
  let L := etaleModuleInverseImage.{u, 0} Λ j
  let adj := etaleModuleInverseImageAdj.{u, 0} Λ j
  have := etaleModuleInverseImage_preservesFiniteLimits.{u, 0} Λ j
  have : L.Additive := inferInstance
  have : IsIso (adj.counit.app QV) := inferInstance
  have : Mono (adj.counit.app QV) := IsIso.mono_of_iso _
  have hiso : ∀ {F F' : EtaleModules.{u, 0} Λ V} (_ : F ≅ F'),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ V.smallEtaleTopology F →
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ V.smallEtaleTopology F' :=
    fun e h ↦
      (Stacks.ConstantSheaf.isClosedUnderIsomorphisms_isFiniteTypeLocallyConstantModuleSheaf.{u,
        u + 1, u + 1, 0} V.smallEtaleTopology Λ).of_iso e h
  let β₀ : G ⟶ (etaleModuleDirectImage.{u, 0} Λ j).obj QV := (adj.homEquiv _ _) b
  have hRQV : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ V.smallEtaleTopology
      (L.obj ((etaleModuleDirectImage.{u, 0} Λ j).obj QV)) :=
    hiso (asIso (adj.counit.app QV)).symm hQV
  let ι' := Abelian.image.ι β₀
  let β := Abelian.factorThruImage β₀
  have hfac : β ≫ ι' = β₀ := Abelian.image.fac β₀
  have hw : kernel.ι β₀ ≫ β = 0 := by
    rw [← cancel_mono ι', Category.assoc, hfac, kernel.condition, zero_comp]
  refine ⟨kernel β₀, Abelian.image β₀, kernel.ι β₀, β, hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨ShortComplex.exact_of_f_is_kernel _
      (isKernelOfComp ι' β₀ (kernelIsKernel β₀) hw hfac)⟩
  · exact isLocallyConstantWith_finite_of_isFiniteTypeLocallyConstant
      (hiso (PreservesKernel.iso L β₀).symm
        (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0} _ Λ
          (L.map β₀) hG hRQV))
  · have hC : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ V.smallEtaleTopology
        (L.obj (cokernel β₀)) :=
      hiso (PreservesCokernel.iso L β₀).symm
        (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_cokernel.{u, u + 1, 0, 0} _ Λ
          (L.map β₀) hG hRQV)
    exact isLocallyConstantWith_finite_of_isFiniteTypeLocallyConstant
      (hiso (PreservesKernel.iso L (cokernel.π β₀)).symm
        (Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0} _ Λ
          (L.map (cokernel.π β₀)) hRQV hC))
  · have : Mono ι' := equalizer.ι_mono
    exact mono_unit_app_of_mono_to_obj adj ι'
  · intro e he Z g hg
    have hβ₀ : L.map β₀ ≫ adj.counit.app QV = b := map_homEquiv_comp_counit adj b
    have hk : g ≫ L.map β₀ = 0 := by
      rw [← cancel_mono (adj.counit.app QV), Category.assoc, hβ₀, hg, zero_comp]
    exact nsmul_eq_zero_of_comp_map_eq_zero L β₀ g hk e he
  · intro e he
    refine nsmul_eq_zero_of_nsmul_homEquiv adj b e ?_
    change e • β₀ = 0
    rw [← hfac, ← Preadditive.nsmul_comp, ← Category.comp_id β, ← Preadditive.comp_nsmul, he,
      comp_zero, zero_comp]

/-- **A stable submodule of the monodromy gives a short exact sequence on `X`.** Let
`j : V ⟶ X` be an open immersion with `V` connected, `v̄` a geometric point of `V`, `G` a sheaf of
`Λ`-modules on `X` with `j⁻¹G` locally constant of finite type, and `W` a `π₁(V, v̄)`-stable
submodule of the monodromy module `M` of `j⁻¹G` at `v̄`. Then there is a short exact sequence
`0 ⟶ A ⟶ G ⟶ Q ⟶ 0` with `j⁻¹A`, `j⁻¹Q` locally constant with finite values, `Q ⟶ j_* j⁻¹ Q`
a monomorphism, such that every `e : ℕ` killing `A` kills `W` and every `e` killing `Q` maps `M`
into `W`. -/
theorem exists_shortExact_of_monodromy_submodule (B : BigEtaleSite.{u}) {X : Scheme.{u}}
    (VB : B.Scheme) [ConnectedSpace VB.1] (jV : VB.1 ⟶ X) [IsOpenImmersion jV]
    (v : GeometricPoint VB.1) (G : EtaleModules.{u, 0} Λ X)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ VB.1.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} Λ jV).obj G))
    (W : Submodule Λ ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v
      Λ).functor.obj ⟨_, hG⟩).obj.obj.obj.V)
    (hW : ∀ h, ∀ x ∈ W, (((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v
      Λ).functor.obj ⟨_, hG⟩).obj.obj.obj.ρ h).hom x ∈ W) :
    ∃ (A Q : EtaleModules.{u, 0} Λ X) (α : A ⟶ G) (β : G ⟶ Q) (w : α ≫ β = 0),
      (ShortComplex.mk α β w).ShortExact ∧
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ VB.1.smallEtaleTopology
        (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj A) ∧
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ VB.1.smallEtaleTopology
        (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj Q) ∧
      Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app Q) ∧
      (∀ e : ℕ, e • 𝟙 A = 0 → e • finiteTypeContinuousModuleOfStableι
        ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v Λ).functor.obj ⟨_, hG⟩)
        W hW = 0) ∧
      (∀ e : ℕ, e • 𝟙 Q = 0 → e • finiteTypeContinuousModuleQuotientπ
        ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v Λ).functor.obj ⟨_, hG⟩)
        W hW = 0) := by
  generalize finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B VB v Λ = EV at W hW ⊢
  let Xs : ObjectProperty.FullSubcategory
      (fun F : EtaleModules.{u, 0} Λ VB.1 =>
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ VB.1.smallEtaleTopology F) :=
    ⟨(etaleModuleInverseImage.{u, 0} Λ jV).obj G, hG⟩
  have : EV.inverse.Additive := (additive_of_equivalence_finiteTypeContinuousModule EV).1
  let π := finiteTypeContinuousModuleQuotientπ (EV.functor.obj Xs) W hW
  let ι := finiteTypeContinuousModuleOfStableι (EV.functor.obj Xs) W hW
  have hιπ : ι ≫ π = 0 := finiteTypeContinuousModuleOfStableι_comp_quotientπ _ W hW
  let bV : Xs ⟶ EV.inverse.obj (finiteTypeContinuousModuleQuotient (EV.functor.obj Xs) W hW) :=
    EV.unit.app Xs ≫ EV.inverse.map π
  obtain ⟨Qs, ⟨eQs⟩⟩ : ∃ Qs : ObjectProperty.FullSubcategory
      (fun F : EtaleModules.{u, 0} Λ VB.1 =>
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ VB.1.smallEtaleTopology F),
      Nonempty (EV.inverse.obj (finiteTypeContinuousModuleQuotient (EV.functor.obj Xs) W hW) ≅
        Qs) :=
    ⟨_, ⟨Iso.refl _⟩⟩
  let bW : Xs ⟶ Qs := bV ≫ eQs.hom
  obtain ⟨A, Q, α, β, w, hex, hA, hQ, hmono, hAe, hQe⟩ :=
    exists_shortExact_of_inverseImage_hom jV G hG Qs.property bW.hom
  refine ⟨A, Q, α, β, w, hex, hA, hQ, hmono, fun e he ↦ ?_, fun e he ↦ ?_⟩
  · let g' : EV.inverse.obj (finiteTypeContinuousModuleOfStable (EV.functor.obj Xs) W hW) ⟶ Xs :=
      EV.inverse.map ι ≫ EV.unitInv.app Xs
    have hg'bW : g' ≫ bW = 0 := by
      change (EV.inverse.map ι ≫ EV.unitIso.inv.app Xs) ≫ (EV.unitIso.hom.app Xs ≫
        EV.inverse.map π) ≫ eQs.hom = 0
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
      rw [← Functor.map_comp_assoc, hιπ, Functor.map_zero, zero_comp]
    have heg : e • g' = 0 := by
      apply ObjectProperty.hom_ext
      change e • g'.hom = 0
      exact hAe e he g'.hom (congrArg (fun φ : EV.inverse.obj
        (finiteTypeContinuousModuleOfStable (EV.functor.obj Xs) W hW) ⟶ Qs ↦ φ.hom) hg'bW)
    exact nsmul_eq_zero_of_nsmul_inverse_map_comp_unitInv EV ι e heg
  · have hb0 : e • bV = 0 := by
      rw [← cancel_mono eQs.hom, Preadditive.nsmul_comp, zero_comp]
      exact ObjectProperty.hom_ext _ (hQe e he)
    exact nsmul_eq_zero_of_nsmul_unit_comp_inverse_map EV π e hb0

end Sheaf

end Stacks.EtaleCohomology

end
