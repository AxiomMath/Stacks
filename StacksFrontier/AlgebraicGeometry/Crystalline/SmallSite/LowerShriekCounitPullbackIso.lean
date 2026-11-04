module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineBaseChangeAlong
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductLocal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseQuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekCrystalBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionCohomologyULift
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechLocal07Q9

/-!
# The pullback of the counit of `i_! ⊣ i^{-1}` at a quasi-coherent module is invertible

Let `(f, g) : (S, X) ⟶ (S', X')` be a morphism of global crystalline situations, with no
hypothesis on `g`, and let `N` be a quasi-coherent sheaf of `𝒪_{X'/S'}`-modules on the big
crystalline site `CRIS(X'/S')`, lifted to the module universe `u + 1` by `bigModuleULift`.  The
counit `ε : i_! i^{-1} N ⟶ N` of the module-level adjunction `i_! ⊣ i^{-1}` of
[Stacks, Tag 07IJ] is in general not an isomorphism on `CRIS(X'/S')`, but this file proves that
its pullback `f_cris^*` along `Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')`
(`...SmallSite.crisModulePullback`) is one.  This identifies the general inverse image
`crisModuleInverseImage` of `i^{-1} N` with `i^{-1}` of the big-site pullback of `N`, which is
the comparison used for arrow 2 of the proof of [Stacks, Tag 07N5].

## The proof

The pullback of `ε` evaluated at an object `A` of `Cris(X/S)` is `ε` at the image `u(A)` of `A`
in `CRIS(X'/S')`, so it suffices that `ε` be bijective on sections over `u(A)` for `A` running
through a covering of every object of `Cris(X/S)`.

* **Every object is covered by good ones** (`exists_restrictOpen_hom_ι`).  Around each point of
  the ambient scheme of `A` there is an affine open `W` such that `u(A|_W)` maps into affine opens
  `V' ⊆ S'` and `W' ⊆ X'`.  Read in the restricted situation `(S'|_{V'}, W')`, which is affine, it
  admits a morphism to an object of the small site with affine ambient scheme, by
  [Stacks, Tag 07HP] (`exists_hom_to_specWholeSpaceThickening`); extending back gives a morphism
  `τ : u(A|_W) ⟶ i C` with `C` in `Cris(X'/S')` (`exists_hom_ι_of_range_subset`).
* **`ε` is bijective over the source of such a `τ`** (`bijective_lowerShriekCounitULift_app`).
  Both sides are base changes of the sections over `C`: the sections of `i_! i^{-1} N` are
  `Γ(𝒪) ⊗ N(C)` by `bijective_lowerShriekBaseChange`, the crystal `i^{-1} N` being locally
  quasi-coherent, and the sections of `N` are `Γ(𝒪) ⊗ N(C)` by
  `bijective_extensionSectionsMapAlong`.  By the triangle identity of the adjunction, `ε` takes
  `t · τ^*(η s)` to `t · τ^* s`, so it is the identity of `Γ(𝒪) ⊗ N(C)` read through these two
  bijections.
* **A morphism of sheaves of modules that is bijective over a covering of every object is an
  isomorphism** (`isIso_of_forall_exists_presieve_bijective`): it is locally injective and
  locally surjective.

## Main results

* `...SmallSite.isIso_crisModulePullback_map_moduleLowerShriekAdjunction_counit` — the pullback
  of the counit of `i_! ⊣ i^{-1}` at the universe lift of a quasi-coherent module is an
  isomorphism.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07HP](https://stacks.math.columbia.edu/tag/07HP)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section Generic

universe v₁ v u₁ w

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{v})]

/-- **A morphism of sheaves of modules which is bijective on the sections over the members of a
covering family of every object is an isomorphism.**  It is locally injective and locally
surjective, hence an isomorphism of the underlying abelian sheaves, hence bijective on every group
of sections. -/
theorem isIso_of_forall_exists_presieve_bijective {M M' : SheafOfModules.{v} R} (φ : M ⟶ M')
    (h : ∀ U : C, ∃ T : Presieve U, Sieve.generate T ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), T f → Function.Bijective (φ.val.app (op V))) :
    IsIso φ := by
  have hψ : IsIso ((SheafOfModules.toSheaf R).map φ) := by
    refine (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨⟨fun {X} x y hxy ↦ ?_⟩, ⟨fun {U} s ↦ ?_⟩⟩
    · obtain ⟨T, hT, hb⟩ := h X.unop
      refine J.superset_covering ((Sieve.generate_le_iff _ _).2 fun V f hf ↦ ?_) hT
      exact (hb f hf).1 <| (PresheafOfModules.naturality_apply φ.val f.op x).trans
        ((congrArg _ hxy).trans (PresheafOfModules.naturality_apply φ.val f.op y).symm)
    · obtain ⟨T, hT, hb⟩ := h U
      refine J.superset_covering ((Sieve.generate_le_iff _ _).2 fun V f hf ↦ ?_) hT
      exact (hb f hf).2 (M'.val.map f.op s)
  have hb : ∀ X : Cᵒᵖ, IsIso (φ.val.app X) := fun X ↦ (ConcreteCategory.isIso_iff_bijective _).2
    (ConcreteCategory.bijective_of_isIso (((SheafOfModules.toSheaf R).map φ).hom.app X))
  have : IsIso ((SheafOfModules.forget R).map φ) :=
    PresheafOfModules.isIso_of_forall_isIso_app φ.val hb
  exact isIso_of_reflects_iso φ (SheafOfModules.forget R)

end Generic

variable {S : GlobalCrystallineSituation.{u}}

/-- **An object of `CRIS(X/S)` with affine ambient scheme lying over affine opens `V ⊆ S` and
`W ⊆ X` maps to an object of `Cris(X/S)` with affine ambient scheme.**  Read in the restricted
situation `(S|_V, W)` the object admits a morphism to the spectrum of a finite level of a divided
power envelope, [Stacks, Tag 07HP]; that spectrum is an object of the small site, and extending
back to `(S, X)` gives the morphism. -/
theorem exists_hom_ι_of_range_subset (B : Thickening S) [IsAffine B.thickening.target.scheme]
    {V : S.S.scheme.Opens} {W : S.X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hVW : W ≤ sourceToBase S ⁻¹ᵁ V) (hB : Set.range B.toBase.hom.base ⊆ V)
    (hX : Set.range B.toX.base ⊆ W) :
    ∃ C : CrystallineThickening S, IsAffine C.obj.thickening.target.scheme ∧
      Nonempty (B ⟶ (CrystallineThickening.ι S).obj C) := by
  have := isAffine_restrictX07Q9 S hW hVW
  have := isAffine_restrictS07Q9 S hV hVW
  let B' := localObject S V W hVW B hB hX
  have : IsAffine B'.thickening.source :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine B.thickening.immersion).1
  obtain ⟨T, hT, ⟨φ⟩⟩ := exists_hom_to_specWholeSpaceThickening
    (isNilpotent_prime_openSituation07Q9 S hW hVW) B'
  refine ⟨(smallExtend S V W hVW).obj ((wholeι _).obj (specWholeSpaceThickening _ T hT)), ?_,
    ⟨(extendLocalObjectIso S V W hVW B hB hX).inv ≫ (extend S V W hVW).map φ⟩⟩
  show IsAffine (Spec _)
  infer_instance

section Counit

variable (N₀ : SheafOfModules.{u} (crystallineStructureSheaf S))

/-- **The counit `i_! i^{-1} N ⟶ N` of `i_! ⊣ i^{-1}`** at the universe lift `N` of a sheaf
`N₀` of `𝒪_{X/S}`-modules on `CRIS(X/S)`. -/
abbrev lowerShriekCounitULift :
    (moduleLowerShriek S).obj ((crisRestrictModules.{u + 1} S).obj ((bigModuleULift S).obj N₀)) ⟶
      (bigModuleULift S).obj N₀ :=
  (moduleLowerShriekAdjunction S).counit.app ((bigModuleULift S).obj N₀)

/-- **The triangle identity on sections**: the counit at `i C` sends the unit of a section over
`C` back to that section. -/
theorem lowerShriekCounitULift_unitAt (C : CrystallineThickening S)
    (a : ((moduleULift S).obj (restrictSheafOfModules N₀)).val.obj (op C)) :
    (lowerShriekCounitULift N₀).val.app (op ((CrystallineThickening.ι S).obj C))
      (lowerShriekUnitAt ((moduleULift S).obj (restrictSheafOfModules N₀)) C a) = a :=
  congrArg (fun φ ↦ (φ.val.app (op C)).hom a)
    ((moduleLowerShriekAdjunction S).right_triangle_components ((bigModuleULift S).obj N₀))

/-- **The counit on `t · τ^*(η s)`**: for `τ : B ⟶ i C` it is `t · τ^* s`, the counit being
linear, natural and a left inverse of the unit. -/
theorem lowerShriekCounitULift_smul_restrict {B : Thickening S} {C : CrystallineThickening S}
    (τ : B ⟶ (CrystallineThickening.ι S).obj C) (c : crysSheafRing S B)
    (s : (restrictSheafOfModules N₀).val.obj (op C)) :
    (lowerShriekCounitULift N₀).val.app (op B)
        (c • lowerShriekRestrict ((moduleULift S).obj (restrictSheafOfModules N₀)) τ
          (upSection (restrictSheafOfModules N₀) s)) =
      ULift.up (c • moduleSiteRestrict N₀ τ s) := by
  have h := PresheafOfModules.naturality_apply (lowerShriekCounitULift N₀).val τ.op
    (lowerShriekUnitAt ((moduleULift S).obj (restrictSheafOfModules N₀)) C
      (upSection (restrictSheafOfModules N₀) s))
  refine (((lowerShriekCounitULift N₀).val.app (op B)).hom.map_smul c _).trans ?_
  refine congrArg (c • ·) (h.trans ?_)
  exact congrArg _ (lowerShriekCounitULift_unitAt N₀ C (upSection (restrictSheafOfModules N₀) s))

variable {B : Thickening S} {C : CrystallineThickening S}
  (τ : B ⟶ (CrystallineThickening.ι S).obj C)

/-- The biadditive datum of `bigTensorToLowerShriekTensor`. -/
def bigTensorToLowerShriekTensorAux :
    ringAlong τ →+ (N₀.val.obj (op ((CrystallineThickening.ι S).obj C)) →+
      (ModuleCat.extendScalars (tauRing τ).hom).obj
        (sectionsOver (restrictSheafOfModules N₀) C)) :=
  AddMonoidHom.mk'
    (fun t ↦ AddMonoidHom.mk'
      (fun s ↦ Stacks.PullbackModel.tmul (tauRing τ).hom
        (show Γ(B.thickening.target.scheme, ⊤) from siteRingAlong τ t) s)
      (fun _ _ ↦ TensorProduct.tmul_add _ _ _))
    (fun _ _ ↦ AddMonoidHom.ext fun _ ↦ TensorProduct.add_tmul _ _ _)

/-- **The change of spelling from the source of the big-site base change of sections of `N₀`
along `τ` to the source of the base change of sections of `i_!`**: `t ⊗ s ↦ t ⊗ s`. -/
def bigTensorToLowerShriekTensor :
    ringAlong τ ⊗[crysSheafRing S ((CrystallineThickening.ι S).obj C)]
        N₀.val.obj (op ((CrystallineThickening.ι S).obj C)) →+
      (ModuleCat.extendScalars (tauRing τ).hom).obj
        (sectionsOver (restrictSheafOfModules N₀) C) :=
  TensorProduct.liftAddHom (bigTensorToLowerShriekTensorAux N₀ τ) fun b t s ↦
    TensorProduct.smul_tmul (R := (crisCommRing S).obj (op ((CrystallineThickening.ι S).obj C)))
      (M := (ModuleCat.restrictScalars (tauRing τ).hom).obj
        (ModuleCat.of Γ(B.thickening.target.scheme, ⊤) Γ(B.thickening.target.scheme, ⊤)))
      (N := sectionsOver (restrictSheafOfModules N₀) C)
      (show (crisCommRing S).obj (op ((CrystallineThickening.ι S).obj C)) from b)
      (show Γ(B.thickening.target.scheme, ⊤) from siteRingAlong τ t) s

/-- `bigTensorToLowerShriekTensor` on a pure tensor. -/
theorem bigTensorToLowerShriekTensor_tmul (t : ringAlong τ)
    (s : N₀.val.obj (op ((CrystallineThickening.ι S).obj C))) :
    bigTensorToLowerShriekTensor N₀ τ (t ⊗ₜ s) =
      Stacks.PullbackModel.tmul (tauRing τ).hom
        (show Γ(B.thickening.target.scheme, ⊤) from siteRingAlong τ t) s :=
  rfl

/-- `bigTensorToLowerShriekTensor` is surjective: both sides are generated by pure tensors. -/
theorem surjective_bigTensorToLowerShriekTensor :
    Function.Surjective (bigTensorToLowerShriekTensor N₀ τ) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul t s => exact ⟨ringAlongSection τ t ⊗ₜ s, rfl⟩
  | add z z' hz hz' =>
    obtain ⟨w, rfl⟩ := hz
    obtain ⟨w', rfl⟩ := hz'
    exact ⟨w + w', map_add _ _ _⟩

/-- **The counit read through the two base changes of sections is the identity**: followed by
the counit, the base change of sections of `i_! i^{-1} N` is the big-site base change of sections
of `N₀`, lifted to the universe `u + 1`. -/
theorem lowerShriekCounitULift_lowerShriekBaseChange
    (w : ringAlong τ ⊗[crysSheafRing S ((CrystallineThickening.ι S).obj C)]
        N₀.val.obj (op ((CrystallineThickening.ι S).obj C))) :
    (lowerShriekCounitULift N₀).val.app (op B) (lowerShriekBaseChange (restrictSheafOfModules N₀) τ
        (bigTensorToLowerShriekTensor N₀ τ w)) =
      ULift.up (extensionSectionsMapAlong N₀ τ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact map_zero ((lowerShriekCounitULift N₀).val.app (op B)).hom
  | tmul t s =>
    exact (lowerShriekCounitULift_smul_restrict N₀ τ (siteRingAlong τ t) s).trans
      (congrArg ULift.up (extensionSectionsMapAlong_tmul N₀ τ t s).symm)
  | add w w' hw hw' =>
    simp only [map_add]
    exact (map_add ((lowerShriekCounitULift N₀).val.app (op B)).hom _ _).trans
      (by rw [hw, hw']; rfl)

include τ in
/-- **The counit `i_! i^{-1} N ⟶ N` is bijective on the sections over an object `B` of `CRIS(X/S)`
with affine ambient scheme which maps to an object `C` of `Cris(X/S)` with affine ambient scheme**,
for `N` the universe lift of a quasi-coherent sheaf of modules: both sides are the base change of
the sections over `C`. -/
theorem bijective_lowerShriekCounitULift_app (hN₀ : N₀.IsQuasicoherentOnSite)
    [IsAffine C.obj.thickening.target.scheme] [IsAffine B.thickening.target.scheme] :
    Function.Bijective ((lowerShriekCounitULift N₀).val.app (op B)) := by
  have hlqc := GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite N₀ hN₀
  have hcrys := GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite N₀ hN₀
  have : (ambientSchemeModules N₀ ((CrystallineThickening.ι S).obj C)).IsQuasicoherent :=
    GlobalCrystallineSituation.isQuasicoherent_ambientModuleRestriction hlqc _
  have : IsAffine ((CrystallineThickening.ι S).obj C).thickening.target.scheme :=
    ‹IsAffine C.obj.thickening.target.scheme›
  have hE := bijective_extensionSectionsMapAlong N₀ τ hcrys
  have hL := bijective_lowerShriekBaseChange (restrictSheafOfModules N₀) τ
    (isLocallyQuasiCoherent_restrictSheafOfModules hlqc)
    (isSheafCrystal_restrictSheafOfModules hcrys)
  refine ⟨(injective_iff_map_eq_zero ((lowerShriekCounitULift N₀).val.app (op B)).hom).2
    fun y hy ↦ ?_, fun n ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := hL.2 y
    obtain ⟨w, rfl⟩ := surjective_bigTensorToLowerShriekTensor N₀ τ z
    have h2 : extensionSectionsMapAlong N₀ τ w = extensionSectionsMapAlong N₀ τ 0 :=
      (congrArg ULift.down ((lowerShriekCounitULift_lowerShriekBaseChange N₀ τ w).symm.trans
        hy)).trans (map_zero _).symm
    rw [hE.1 h2]
    exact (congrArg _ (map_zero _)).trans (map_zero _)
  · obtain ⟨w, hw⟩ := hE.2 n.down
    exact ⟨lowerShriekBaseChange (restrictSheafOfModules N₀) τ
      (bigTensorToLowerShriekTensor N₀ τ w),
      (lowerShriekCounitULift_lowerShriekBaseChange N₀ τ w).trans (congrArg ULift.up hw)⟩

end Counit

/-- The image of the ambient scheme of a restriction `A|_W` in a base `S'` lies in an open `V`
as soon as `W` maps into `V`. -/
theorem range_restrictOpen_toBase_comp_subset {S' : GlobalCrystallineSituation.{u}}
    (a : Thickening S) (W : a.thickening.target.scheme.Opens) (g : S.S ⟶ S'.S)
    {V : S'.S.scheme.Opens} (h : W ≤ (a.toBase ≫ g).hom ⁻¹ᵁ V) :
    Set.range ((a.restrictOpen W).toBase ≫ g).hom.base ⊆ V := by
  rintro _ ⟨z, rfl⟩
  exact h z.2

/-- The image of the thickened scheme of a restriction `A|_W` in a scheme `X'` lies in an open
`V` as soon as every point of the thickened scheme over `W` maps into `V`. -/
theorem range_restrictOpen_toX_comp_subset {S' : GlobalCrystallineSituation.{u}}
    (a : Thickening S) (W : a.thickening.target.scheme.Opens) (g : S.X ⟶ S'.X)
    {V : S'.X.Opens}
    (h : ∀ y, a.thickening.immersion.base y ∈ W → (a.toX ≫ g).base y ∈ V) :
    Set.range ((a.restrictOpen W).toX ≫ g).base ⊆ V := by
  rintro _ ⟨z, rfl⟩
  exact h z.1 z.2

variable {S' : GlobalCrystallineSituation.{u}} (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **Every point of the ambient scheme of an object `A` of `CRIS(X/S)` has an affine open
neighbourhood `W` such that the image of `A|_W` under change of base maps to an object of
`Cris(X'/S')` with affine ambient scheme.**  Choose affine opens `V' ⊆ S'` and `W' ⊆ X'` around
the images of the point, and `W` inside the open of the points over `V'` whose fibre in the
thickened scheme maps into `W'`; then `exists_hom_ι_of_range_subset` applies. -/
theorem exists_restrictOpen_hom_ι (a : Thickening S) (x : a.thickening.target.scheme) :
    ∃ W : a.thickening.target.scheme.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ C : CrystallineThickening S', IsAffine C.obj.thickening.target.scheme ∧
        Nonempty ((changeBase S S' fS fX hf).obj (a.restrictOpen W) ⟶
          (CrystallineThickening.ι S').obj C) := by
  set β := (a.toBase ≫ fS).hom
  set γ := a.toX ≫ fX
  set i := a.thickening.immersion
  have hover : i ≫ β = γ ≫ sourceToBase S' := ((changeBase S S' fS fX hf).obj a).over_base
  obtain ⟨V', hV', hxV', -⟩ :=
    exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (β.base x))
  obtain ⟨W', hW', hW'V', hyW'⟩ : ∃ W' : S'.X.Opens, IsAffineOpen W' ∧
      W' ≤ sourceToBase S' ⁻¹ᵁ V' ∧ ∀ y, i.base y = x → γ.base y ∈ W' := by
    by_cases hx : ∃ y, i.base y = x
    · obtain ⟨y, rfl⟩ := hx
      have hy : γ.base y ∈ sourceToBase S' ⁻¹ᵁ V' := by
        show (γ ≫ sourceToBase S').base y ∈ V'
        rw [← hover]
        exact hxV'
      obtain ⟨W', hW', hyW', hsub⟩ := exists_isAffineOpen_mem_and_subset hy
      refine ⟨W', hW', hsub, fun y' hy' ↦ ?_⟩
      rwa [i.isClosedEmbedding.injective hy']
    · exact ⟨⊥, isAffineOpen_bot _, bot_le, fun y hy ↦ absurd ⟨y, hy⟩ hx⟩
  have hZ : IsClosed (i.base '' ((γ ⁻¹ᵁ W' : a.thickening.source.Opens) : Set _)ᶜ) :=
    i.isClosedEmbedding.isClosedMap _ (γ ⁻¹ᵁ W').isOpen.isClosed_compl
  let O : a.thickening.target.scheme.Opens := β ⁻¹ᵁ V' ⊓ ⟨_, hZ.isOpen_compl⟩
  have hxO : x ∈ O := by
    refine ⟨hxV', ?_⟩
    rintro ⟨y, hy, rfl⟩
    exact hy (hyW' y rfl)
  obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset hxO
  have htoX : ∀ y, i.base y ∈ W → γ.base y ∈ W' := fun y hy ↦ by
    by_contra hne
    exact (hWO hy).2 ⟨y, hne, rfl⟩
  have : IsAffine ((changeBase S S' fS fX hf).obj (a.restrictOpen W)).thickening.target.scheme :=
    hW
  exact ⟨W, hW, hxW, exists_hom_ι_of_range_subset
    ((changeBase S S' fS fX hf).obj (a.restrictOpen W)) hV' hW' hW'V'
    (range_restrictOpen_toBase_comp_subset a W fS fun _ hz ↦ (hWO hz).1)
    (range_restrictOpen_toX_comp_subset a W fX htoX)⟩

/-- **The pullback `f_cris^*` of the counit `i_! i^{-1} N ⟶ N` of `i_! ⊣ i^{-1}` is an
isomorphism** for `N` the universe lift of a quasi-coherent sheaf of `𝒪_{X'/S'}`-modules on
`CRIS(X'/S')`, for every morphism of global crystalline situations `(f, g)` — no hypothesis on
`g`.  The pullback evaluated at an object `A` of `Cris(X/S)` is the counit at the image of `A`,
which is bijective over the restrictions of `A` to an affine open cover, by
`exists_restrictOpen_hom_ι` and `bijective_lowerShriekCounitULift_app`. -/
theorem isIso_crisModulePullback_map_moduleLowerShriekAdjunction_counit
    (N₀ : SheafOfModules.{u} (crystallineStructureSheaf S')) (hN₀ : N₀.IsQuasicoherentOnSite) :
    IsIso ((crisModulePullback.{u + 1} fS fX hf).map
      ((moduleLowerShriekAdjunction S').counit.app ((bigModuleULift S').obj N₀))) := by
  apply isIso_of_forall_exists_presieve_bijective
  intro A
  choose W hW hxW C hC hτ using exists_restrictOpen_hom_ι fS fX hf A.obj
  refine ⟨(A.restrictOpenCover fun x : ULift.{u + 1} A.obj.thickening.target.scheme ↦
    W x.down).presieve₀, generate_mem_smallTopology_of_mem_restrictCoverage S
      ⟨_, _, fun x ↦ ⟨⟨x⟩, hxW x⟩, rfl⟩, ?_⟩
  rintro V f ⟨x⟩
  exact @bijective_lowerShriekCounitULift_app S' N₀ _ _ (hτ x.down).some hN₀ (hC x.down) (hW x.down)

end Crystalline.GlobalCrystallineSituation.SmallSite
