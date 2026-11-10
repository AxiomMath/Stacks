module

public import StacksFrontier.RingTheory.Dualizing.DualExtAnnihilator
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExtDetection
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantSystem
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated

/-!
# Local duality for kernels of local cohomology, and images of Ext

Let `(B, 𝔪)` be a Noetherian local ring with a normalized dualizing complex `ω'`, let
`0 → N → P → Q → 0` be a short exact sequence of `B`-modules with `Q` finite and let `a : N ⟶ N'`
be a map into a finite module. For a complex `ω` with `ω⟦j⟧ ≅ ω'⟦-i⟧`, the kernel of
`H^i_{V(𝔪)}(N → P)` is contained in the kernel of `H^i_{V(𝔪)}(a)` exactly when the image of the
map induced by `a` on `H^j(RHom_B(−, ω))` is contained in the image of the map induced by `N → P`.

## Main results

* `Dualizing.LocalDuality.ker_le_ker_localCohomologyModuleFunctor_iff_forall_exists_comp_eq` —
  the kernel containment on local cohomology holds exactly when every morphism out
  of the auxiliary module, precomposed with `a`, factors through `f`.
* `Dualizing.LocalDuality.forall_exists_comp_eq_iff_range_le_range_homologyMap_dualizingDerivedHom`
  — that factorization condition, read on the finite modules `H^j(RHom(−, ω))` as a containment
  of images.
* `Dualizing.LocalDuality.ker_le_ker_localCohomologyModuleFunctor_iff_range_le_range` — the
  kernel containment on local cohomology is the image containment on Ext.

## References

* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0AAK](https://stacks.math.columbia.edu/tag/0AAK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing.LocalDuality

variable (B : Type u) [CommRing B]

/-! ### Transporting the factorization condition along an isomorphism of the target -/

/-- **The factorization condition only depends on the target up to isomorphism.** Replacing the
object the morphisms land in by an isomorphic one changes neither side of
"every `u` out of `X`, precomposed with `α`, factors through `γ`". -/
theorem forall_exists_comp_eq_iff_of_iso {C : Type*} [Category C] {X Y Z : C}
    (α : Z ⟶ X) (γ : Z ⟶ Y) {P P' : C} (e : P ≅ P') :
    (∀ u : X ⟶ P, ∃ v : Y ⟶ P, α ≫ u = γ ≫ v) ↔
      ∀ u : X ⟶ P', ∃ v : Y ⟶ P', α ≫ u = γ ≫ v := by
  have key : ∀ {P P' : C} (e : P ≅ P'), (∀ u : X ⟶ P, ∃ v : Y ⟶ P, α ≫ u = γ ≫ v) →
      ∀ u : X ⟶ P', ∃ v : Y ⟶ P', α ≫ u = γ ≫ v := fun e h u => by
    obtain ⟨v, hv⟩ := h (u ≫ e.inv)
    exact ⟨v ≫ e.hom, by simpa using hv =≫ e.hom⟩
  exact ⟨key e, key e.symm⟩

/-! ### The reformulation of both sides as one vanishing -/

section

variable [IsNoetherianRing B] [IsLocalRing B]

attribute [local instance] Stacks.LocalCohomology.derivedPowerTorsionProperty_isTriangulated
  Stacks.LocalCohomology.derivedPowerTorsionProperty_isClosedUnderIsomorphisms

omit [IsNoetherianRing B] [IsLocalRing B] in
/-- **The kernel of `H^i_Z(f)` is the image of `H^i_Z(β)`**, where `β` is the connecting morphism
of the inverse-rotated triangle of the short exact sequence `0 → N → P → Q → 0`. -/
theorem range_localCohomology_invRotate_mor₁_eq_ker (I : Ideal B) (hI : I.FG)
    {S : ShortComplex (ModuleCat.{u} B)} (hS : S.ShortExact) (i : ℤ) :
    LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor B I hI).map
          hS.singleTriangle.invRotate.mor₁)).hom =
      LinearMap.ker ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor B I hI).map
          hS.singleTriangle.invRotate.mor₂)).hom := by
  let := Stacks.LocalCohomology.localCohomologyFunctorCommShift.{u, u} B I hI
  let := Stacks.LocalCohomology.localCohomologyFunctor_isTriangulated.{u, u} B I hI
  have hT := (Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor B
    I hI).map_distinguished _ (inv_rot_of_distTriang _ hS.singleTriangle_distinguished)
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    (DerivedCategory.HomologySequence.exact₂ _ hT i)

end

/-! ### The transport -/

section

variable [IsNoetherianRing B] [IsLocalRing B]

/-- **Local duality for a kernel containment.** Let `(B, 𝔪)` be a Noetherian local ring with a
normalized dualizing complex `ω`, let `0 → N → P → Q → 0` be a short exact sequence of finite
`B`-modules and let `a : N ⟶ N'` be any map into a finite module. Then the containment

`ker H^i_{V(𝔪)}(N → P) ⊆ ker H^i_{V(𝔪)}(a)`

holds exactly when for every morphism `u : N'[0] ⟶ ω⟦-i⟧` of `D(B)` the composite `a[0] ≫ u`
factors through `(N → P)[0]`. -/
theorem ker_le_ker_localCohomologyModuleFunctor_iff_forall_exists_comp_eq
    (ω : DerivedCategory (ModuleCat.{u} B)) (hω : IsNormalizedDualizingComplex.{u, u} ω) (i : ℤ)
    {S : ShortComplex (ModuleCat.{u} B)} (hS : S.ShortExact) [Module.Finite B S.X₃]
    {N : ModuleCat.{u} B} [Module.Finite B N] (a : S.X₁ ⟶ N) :
    (LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor B i).map S.f).hom ≤
        LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor B i).map a).hom) ↔
      ∀ u : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N ⟶
          (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (-i)).obj ω,
        ∃ v : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj S.X₂ ⟶
            (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (-i)).obj ω,
          (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a ≫ u =
            (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map S.f ≫ v := by
  classical
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal B))
  obtain ⟨E, ιE, hmono, hhull⟩ := Module.exists_isInjectiveHull B
    ((ModuleCat.uliftFunctor.{u} B).obj
      (ModuleCat.of B (IsLocalRing.ResidueField B)))
  let : Mono ιE := hmono
  obtain ⟨⟨b, hb⟩, -⟩ := hω.1.bounded
  have : ω.IsGE b := hb
  have hbshift : ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B))
      (-i)).obj ω).IsGE (b + i) :=
    (DerivedCategory.TStructure.t).isGE_shift _ b (-i) (b + i) (by ring)
  have hT' := inv_rot_of_distTriang _ hS.singleTriangle_distinguished
  have hle : (hS.singleTriangle.invRotate.obj₁).IsLE 1 := by
    change (((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj S.X₃)⟦(-1 : ℤ)⟧).IsLE 1
    have : ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj S.X₃).IsLE 0 := inferInstance
    exact (DerivedCategory.TStructure.t).isLE_shift _ 0 (-1) 1 (by ring)
  have hfin₁ : ∀ l : ℤ, Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) l).obj
        hS.singleTriangle.invRotate.obj₁) :=
    finite_homology_shift _ (fun l => finite_homology_single _ l) (-1)
  have step₁ : (LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor B i).map
        S.f).hom ≤
        LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor B i).map a).hom) ↔
      (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor B
          (IsLocalRing.maximalIdeal B) (IsNoetherian.noetherian _)).map
          (hS.singleTriangle.invRotate.mor₁ ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a)) = 0 := by
    rw [show LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor B i).map
            S.f).hom =
          LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
            ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor B
              (IsLocalRing.maximalIdeal B) (IsNoetherian.noetherian _)).map
              hS.singleTriangle.invRotate.mor₁)).hom from
        (range_localCohomology_invRotate_mor₁_eq_ker B (IsLocalRing.maximalIdeal B)
          (IsNoetherian.noetherian _) hS i).symm]
    erw [Functor.map_comp, Functor.map_comp]
    refine ⟨fun h => ModuleCat.hom_ext (LinearMap.ext fun x => h ⟨x, rfl⟩), ?_⟩
    rintro h _ ⟨x, rfl⟩
    exact ConcreteCategory.congr_hom h x
  rw [step₁]
  have step₂ : ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
        ((Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor B
          (IsLocalRing.maximalIdeal B) (IsNoetherian.noetherian _)).map
          (hS.singleTriangle.invRotate.mor₁ ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a)) = 0) ↔
      ∀ u : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N ⟶
          (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (-i)).obj ω,
        (hS.singleTriangle.invRotate.mor₁ ≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a) ≫ u = 0 :=
    ⟨fun hz u => comp_eq_zero_of_homologyMap_localCohomology_eq_zero_of_bounded B f hf ω hω
        ιE hhull i _ 1 (b + i) hle hbshift hfin₁
        (finite_homology_shift _ hω.1.finiteCohomology (-i)) hz u,
      homologyMap_localCohomology_eq_zero_of_forall_comp_eq_zero_of_bounded B f hf ω hω
        ιE hhull i _ 0 (b + i) inferInstance hbshift
        (fun l => finite_homology_single _ l)
        (finite_homology_shift _ hω.1.finiteCohomology (-i))⟩
  rw [step₂]
  refine forall_congr' fun u => ?_
  rw [show (hS.singleTriangle.invRotate.mor₁ ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a) ≫ u =
      hS.singleTriangle.invRotate.mor₁ ≫
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a ≫ u) from
    Category.assoc _ _ _]
  refine ⟨Triangle.yoneda_exact₂ _ hT' _, ?_⟩
  rintro ⟨v, hv⟩
  refine (congrArg (hS.singleTriangle.invRotate.mor₁ ≫ ·) hv).trans ?_
  refine (Category.assoc hS.singleTriangle.invRotate.mor₁
    hS.singleTriangle.invRotate.mor₂ v).symm.trans ?_
  exact (comp_distTriang_mor_zero₁₂ _ hT' =≫ v).trans Limits.zero_comp

end

/-! ### The factorization condition as a containment of images of Ext -/

/-- **The factorization condition, read on the modules `H^j(RHom(−, ω))`.** For a complex `ω`
bounded below and maps `a : N ⟶ N'`, `f : N ⟶ P` of modules, every morphism `u : N'[0] ⟶ ω⟦j⟧`
has `a[0] ≫ u` factoring through `f[0]` exactly when the image of the map induced by `a` on
`H^j(RHom(−, ω))` is contained in the image of the map induced by `f`. -/
theorem forall_exists_comp_eq_iff_range_le_range_homologyMap_dualizingDerivedHom
    (ω : DerivedCategory (ModuleCat.{u} B)) (j : ℤ)
    {N N' P : ModuleCat.{u} B} (a : N ⟶ N') (f : N ⟶ P) :
    (∀ u : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N' ⟶
        (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) j).obj ω,
      ∃ v : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj P ⟶
          (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) j).obj ω,
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a ≫ u =
          (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map f ≫ v) ↔
      LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map
          ((dualizingDerivedHomFunctor.{u, u} B ω).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a).op)).hom ≤
        LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map
          ((dualizingDerivedHomFunctor.{u, u} B ω).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map f).op)).hom := by
  constructor
  · rintro h _ ⟨z, rfl⟩
    obtain ⟨u, rfl⟩ := (extIntoOmegaAtLinearEquiv.{u, u} B ω j N').surjective z
    obtain ⟨v, hv⟩ := h u
    refine ⟨extIntoOmegaAtLinearEquiv.{u, u} B ω j P v, ?_⟩
    rw [← extIntoOmegaAtLinearEquiv_naturality.{u, u} B ω j f v,
      ← extIntoOmegaAtLinearEquiv_naturality.{u, u} B ω j a u, hv]
  · intro h u
    obtain ⟨z, hz⟩ := h (LinearMap.mem_range_self _
      (extIntoOmegaAtLinearEquiv.{u, u} B ω j N' u))
    obtain ⟨v, rfl⟩ := (extIntoOmegaAtLinearEquiv.{u, u} B ω j P).surjective z
    refine ⟨v, (extIntoOmegaAtLinearEquiv.{u, u} B ω j N).injective ?_⟩
    rw [extIntoOmegaAtLinearEquiv_naturality.{u, u} B ω j a u,
      extIntoOmegaAtLinearEquiv_naturality.{u, u} B ω j f v, hz]

/-! ### The two composed -/

/-- **The stable-image transport of local duality.** Let `(B, 𝔪)` be a Noetherian local ring, let
`ω'` be a normalized dualizing complex, let `0 → N → P → Q → 0` be a short exact sequence with `Q`
finite, let `a : N ⟶ N'` be a map into a finite module and let `ω` be a complex with
`ω⟦j⟧ ≅ ω'⟦-i⟧`. Then

`ker H^i_{V(𝔪)}(N → P) ⊆ ker H^i_{V(𝔪)}(a)`  ⟺  `im Ext^j(a) ⊆ im Ext^j(N → P)`,

where `Ext^j(−)` means the map induced on `H^j(RHom_B(−, ω))`. -/
theorem ker_le_ker_localCohomologyModuleFunctor_iff_range_le_range
    [IsNoetherianRing B] [IsLocalRing B]
    (ω' : DerivedCategory (ModuleCat.{u} B)) (hω' : IsNormalizedDualizingComplex.{u, u} ω')
    (i : ℤ) (ω : DerivedCategory (ModuleCat.{u} B)) (j : ℤ)
    (e : (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) j).obj ω ≅
      (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (-i)).obj ω')
    {S : ShortComplex (ModuleCat.{u} B)} (hS : S.ShortExact) [Module.Finite B S.X₃]
    {N : ModuleCat.{u} B} [Module.Finite B N] (a : S.X₁ ⟶ N) :
    (LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor B i).map S.f).hom ≤
        LinearMap.ker ((Stacks.LocalCohomology.localCohomologyModuleFunctor B i).map a).hom) ↔
      LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map
          ((dualizingDerivedHomFunctor.{u, u} B ω).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a).op)).hom ≤
        LinearMap.range ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).map
          ((dualizingDerivedHomFunctor.{u, u} B ω).map
            ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map S.f).op)).hom :=
  (ker_le_ker_localCohomologyModuleFunctor_iff_forall_exists_comp_eq B ω' hω' i hS a).trans
    (((forall_exists_comp_eq_iff_of_iso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map a)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map S.f) e).symm).trans
      (forall_exists_comp_eq_iff_range_le_range_homologyMap_dualizingDerivedHom B ω j a S.f))

end Dualizing.LocalDuality

end
