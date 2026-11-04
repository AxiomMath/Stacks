module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SurjectiveEtaleFaithful
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ExtensionTorsor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllConnectedCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeEtaleSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantSerreClass
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingAdjunction
public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsAdequate.FinitelyPresentedExtTwo

/-!
# Duality for locally constant `ℤ/ℓ`-coefficients from duality for constant coefficients

Let `X` be a connected scheme, `ℓ` a prime, `N` a natural number and
`t : Ext^N(ℤ/ℓ_X, ℤ/ℓ_X) → ℤ/ℓ` a trace. For a finite étale `π : T → X` the adjunctions
`π^{-1} ⊣ π_* ⊣ π^{-1}` transfer `t` to a trace on `Ext^N(π^{-1}ℤ/ℓ, π^{-1}ℤ/ℓ)`, which we read on
`Ext^N(ℤ/ℓ_T, ℤ/ℓ_T)` through `π^{-1}ℤ/ℓ_X ≅ ℤ/ℓ_T`: this is `coverTrace π N t`.

**Dévissage.** Suppose `Ext^{N+1}(ℤ/ℓ_T, K) = 0` for every finite étale `T → X` and every `K`
on `T`, and that duality holds at `ℤ/ℓ_T` for `coverTrace π N t` whenever `T` is connected.
Then duality holds at every finite type locally constant sheaf `F` of `ℤ/ℓ`-modules on `X`.

Proof: by Tag 0A3R (with a connected cover,
`Stacks.EtaleCohomology.exists_connected_primeToEll_finiteEtale_relSeries_constantRankOneStep`)
there is a connected finite étale `π : T → X` with `π^{-1}F` a successive extension of copies of
`ℤ/ℓ_T`; by the five lemma (`CategoryTheory.Abelian.Ext.isDualityPerfect_X₂`) duality holds at
`π^{-1}F` for `coverTrace π N t`, hence at `π_* π^{-1}F` for `t`
(`CategoryTheory.Abelian.Ext.isDualityPerfect_obj_iff`). The trace `π_*π^{-1}F → F` is onto
(`π` is surjective, `Stacks.EtaleCohomology.epi_etaleModuleDirectImageInverseImageAdj_counit_app`)
with finite type locally constant kernel, and `Ext^{N+1}(ℤ/ℓ_X, -) = 0`, so the way-out argument
`CategoryTheory.Abelian.Ext.isDualityPerfect_of_resolution` concludes.

## Main results

* `Stacks.EtaleCohomology.coverTrace`: the transferred trace.
* `Stacks.EtaleCohomology.isDualityPerfect_of_relSeries_constantRankOneStep`: duality at a
  successive extension of copies of `ℤ/ℓ`.
* `Stacks.EtaleCohomology.isDualityPerfect_of_isFiniteTypeLocallyConstant`: the dévissage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **`ℤ/p` has the extension property for subgroups of `ℤ/p`-vector spaces.** -/
theorem exists_extend_zmod {p : ℕ} [Fact p.Prime] {E : Type*} [AddCommGroup E]
    [Module (ZMod p) E] (H : AddSubgroup E) (φ : H →+ ZMod p) :
    ∃ ψ : E →+ ZMod p, ∀ x : H, ψ x = φ x := by
  let Hs : Submodule (ZMod p) E :=
    { carrier := H
      add_mem' := H.add_mem
      zero_mem' := H.zero_mem
      smul_mem' := fun c x hx => by
        rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
        exact H.nsmul_mem hx _ }
  let φ' : Hs →ₗ[ZMod p] ZMod p := (φ.comp (AddMonoidHom.mk' (fun x : Hs =>
    (⟨x.1, x.2⟩ : H)) (fun _ _ => rfl))).toZModLinearMap p
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ'
  exact ⟨ψ.toAddMonoidHom, fun x => LinearMap.congr_fun hψ (⟨x.1, x.2⟩ : Hs)⟩

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Cover

variable {X T : Scheme.{u}} (π : T ⟶ X) [IsFinite π] [Etale π]

/-- `π^{-1} ℤ/ℓ_X ≅ ℤ/ℓ_T`. -/
def unitSheafInverseImageIso :
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := X) ℓ) ≅ unitSheaf (X := T) ℓ :=
  (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) π).app
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))

/-- For finite étale `π`, the inverse image `π^{-1}` on étale `ℤ/ℓ`-modules preserves finite
limits. -/
instance etaleModuleInverseImage_preservesFiniteLimits' :
    PreservesFiniteLimits (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π) :=
  etaleModuleInverseImage_preservesFiniteLimits _ _

/-- For finite étale `π`, the inverse image `π^{-1}` on étale `ℤ/ℓ`-modules preserves finite
colimits. -/
instance etaleModuleInverseImage_preservesFiniteColimits' :
    PreservesFiniteColimits (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π) :=
  etaleModuleInverseImage_preservesFiniteColimits _ _

/-- For finite étale `π`, the inverse image `π^{-1}` on étale `ℤ/ℓ`-modules is additive. -/
instance etaleModuleInverseImage_additive' :
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- For finite étale `π`, the direct image `π_*` on étale `ℤ/ℓ`-modules preserves finite limits. -/
instance etaleModuleDirectImage_preservesFiniteLimits_of_finiteEtale :
    PreservesFiniteLimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π) :=
  have := (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) π).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

/-- For finite étale `π`, the direct image `π_*` on étale `ℤ/ℓ`-modules preserves finite
colimits. -/
instance etaleModuleDirectImage_preservesFiniteColimits_of_finiteEtale :
    PreservesFiniteColimits (etaleModuleDirectImage.{u, 0} (ZMod ℓ) π) :=
  have :=
    (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).leftAdjoint_preservesColimits.{0, 0}
  inferInstance

variable (N : ℕ)

/-- **The trace on a finite étale cover.** A trace `t` on `Ext^N(ℤ/ℓ_X, ℤ/ℓ_X)` induces, through
`π^{-1} ⊣ π_* ⊣ π^{-1}` and `π^{-1}ℤ/ℓ_X ≅ ℤ/ℓ_T`, the trace
`z ↦ t (η ∘ π_* z ∘ tr)` on `Ext^N(ℤ/ℓ_T, ℤ/ℓ_T)`. -/
def coverTrace (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) N →+ ZMod ℓ) :
    Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) N →+ ZMod ℓ :=
  Ext.transportTrace (Ext.transferTrace (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) π)
    (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π) _ _ N t)
    (unitSheafInverseImageIso π) (unitSheafInverseImageIso π)

/-- **Duality at a direct image.** Duality holds at `π_* G` for `t` if and only if it holds at `G`
for `coverTrace π N t`. -/
theorem isDualityPerfect_directImage_iff (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) N →+ ZMod ℓ)
    (G : EtaleModules.{u, 0} (ZMod ℓ) T) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) N t
        ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj G) ↔
      Ext.IsDualityPerfect (unitSheaf (X := T) ℓ) (unitSheaf ℓ) N (coverTrace π N t) G :=
  (Ext.isDualityPerfect_obj_iff (etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) π)
    (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π) _ _ N t G).trans
    (Ext.isDualityPerfect_transport_iff _ _ _ G)

/-- **The transferred trace is injective** when `t` is, provided `π` is surjective,
`Ext^{N+1}(ℤ/ℓ_X, -) = 0`, and `Ext^N(ℤ/ℓ_T, ℤ/ℓ_T)` is finite with as many elements as
`Ext^N(ℤ/ℓ_X, ℤ/ℓ_X)`. -/
theorem injective_coverTrace [Surjective π]
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) N →+ ZMod ℓ)
    (ht : Function.Injective t)
    (hvan : ∀ K : EtaleModules.{u, 0} (ZMod ℓ) X,
      Subsingleton (Ext (unitSheaf (X := X) ℓ) K (N + 1)))
    [Finite (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) N)]
    (hcard : Nat.card (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) N) =
      Nat.card (Ext (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) N)) :
    Function.Injective (coverTrace π N t) := by
  have := epi_etaleModuleDirectImageInverseImageAdj_counit_app (ZMod ℓ) π (unitSheaf (X := X) ℓ)
  let adj₁ := etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) π
  let adj₂ := etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π
  have hτ : Function.Surjective (Ext.transferTrace adj₁ adj₂ (unitSheaf (X := X) ℓ)
      (unitSheaf ℓ) N (AddMonoidHom.id (Ext (unitSheaf (X := X) ℓ) (unitSheaf (X := X) ℓ) N))) :=
    Ext.surjective_transferTrace_id adj₁ adj₂ (unitSheaf (X := X) ℓ) (unitSheaf ℓ) N (hvan _)
  let e := unitSheafInverseImageIso (ℓ := ℓ) π
  let α : Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) N →
      Ext ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := X) ℓ))
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj (unitSheaf (X := X) ℓ)) N :=
    fun z => (Ext.mk₀ e.hom).comp (z.comp (Ext.mk₀ e.inv) (add_zero N)) (zero_add N)
  have hα : Function.Surjective α := by
    intro w
    refine ⟨(Ext.mk₀ e.inv).comp (w.comp (Ext.mk₀ e.hom) (add_zero N)) (zero_add N), ?_⟩
    simp only [α]
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      e.hom_inv_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  exact fun _ _ hzw => ((hτ.comp hα).bijective_of_nat_card_le hcard.le).1 (ht hzw)

end Cover

section Filtration

variable {T : Scheme.{u}} (N : ℕ) (t' : Ext (unitSheaf (X := T) ℓ) (unitSheaf ℓ) N →+ ZMod ℓ)

/-- **Duality at a successive extension of copies of `ℤ/ℓ`.** If `Ext^{N+1}(ℤ/ℓ_T, -) = 0` and
duality holds at `ℤ/ℓ_T`, it holds at every sheaf with a finite filtration whose successive
quotients are `ℤ/ℓ_T`. -/
theorem isDualityPerfect_of_relSeries_constantRankOneStep
    (hvan : ∀ K : EtaleModules.{u, 0} (ZMod ℓ) T,
      Subsingleton (Ext (unitSheaf (X := T) ℓ) K (N + 1)))
    (hconst : Ext.IsDualityPerfect (unitSheaf (X := T) ℓ) (unitSheaf ℓ) N t' (unitSheaf ℓ))
    (G : EtaleModules.{u, 0} (ZMod ℓ) T) (Xs : RelSeries (ConstantRankOneStep.{0} ℓ G))
    (hhead : IsZero (Subobject.underlying.obj Xs.head)) (hlast : IsIso Xs.last.arrow) :
    Ext.IsDualityPerfect (unitSheaf (X := T) ℓ) (unitSheaf ℓ) N t' G := by
  have : Subsingleton (Ext (unitSheaf (X := T) ℓ) (unitSheaf (X := T) ℓ) (N + 1)) := hvan _
  have key : ∀ i : Fin (Xs.length + 1), Ext.IsDualityPerfect (unitSheaf (X := T) ℓ)
      (unitSheaf ℓ) N t' (Subobject.underlying.obj (Xs i)) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      exact Ext.isDualityPerfect_of_retract (0 : _ ⟶ unitSheaf (X := T) ℓ) 0
        (hhead.eq_of_src _ _) hconst
    | succ i ih =>
      obtain ⟨hle, ⟨e⟩⟩ := Xs.step i
      let S := ShortComplex.mk (Subobject.ofLE _ _ hle) (cokernel.π (Subobject.ofLE _ _ hle))
        (cokernel.condition _)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_cokernel _ }
      have h₃ : Ext.IsDualityPerfect (unitSheaf (X := T) ℓ) (unitSheaf ℓ) N t' S.X₃ :=
        Ext.isDualityPerfect_of_retract e.hom e.inv e.hom_inv_id hconst
      have := hvan S.X₁
      have : Subsingleton (Ext S.X₃ (unitSheaf (X := T) ℓ) (N + 1)) :=
        AdequateFunctor.subsingleton_ext_of_iso_left e.symm (N + 1) inferInstance
      exact Ext.isDualityPerfect_X₂ hS ih h₃ inferInstance inferInstance
        (fun _ _ H φ => exists_extend_zmod H φ)
  exact Ext.isDualityPerfect_of_retract (inv Xs.last.arrow) Xs.last.arrow (by simp)
    (key (Fin.last _))

end Filtration

section Devissage

variable {X : Scheme.{u}} [ConnectedSpace X]

/-- A finite étale morphism from a connected (in particular nonempty) scheme to a connected
scheme is surjective. -/
theorem surjective_of_finiteEtale_of_connectedSpace {T : Scheme.{u}} [ConnectedSpace T]
    (π : T ⟶ X) [IsFinite π] [Etale π] : Surjective π := by
  constructor
  obtain ⟨y⟩ : Nonempty T := inferInstance
  exact Set.range_eq_univ.1 (IsClopen.eq_univ ⟨π.isClosedMap.isClosed_range,
    π.isOpenMap.isOpen_range⟩ ⟨π.base y, y, rfl⟩)

/-- Inverse image along a finite étale morphism of connected schemes preserves finite type
local constancy of sheaves of `ℤ/ℓ`-modules. -/
theorem isFiniteTypeLocallyConstant_etaleModuleInverseImage {T : Scheme.{u}} [ConnectedSpace T]
    (π : T ⟶ X) [IsFinite π] [Etale π] (G : EtaleModules.{u, 0} (ZMod ℓ) X)
    (hG : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology G) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) T.smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj G) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have hT : B.Contains T := B.contains_of_finiteEtale π ⟨inferInstance, inferInstance⟩ hX
  let XS : B.Scheme := ⟨X, hX⟩
  let XT : B.Scheme := ⟨T, hT⟩
  let fB : XT ⟶ XS := ObjectProperty.homMk π
  have : ConnectedSpace XS.1 := ‹ConnectedSpace X›
  have : ConnectedSpace XT.1 := ‹ConnectedSpace T›
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ _
    (((etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) π).leftAdjointUniq
      (etaleSiteSheafPullbackModuleAdjunction B fB (ZMod ℓ))).app G).symm
    (isFiniteTypeLocallyConstant_etaleSiteSheafPullbackModule B fB (ZMod ℓ) G hG)

/-- **Duality for finite type locally constant `ℤ/ℓ`-coefficients by dévissage.** Let `X` be a
connected scheme and `t` a trace on `Ext^N(ℤ/ℓ_X, ℤ/ℓ_X)`. If `Ext^{N+1}(ℤ/ℓ_T, -)` vanishes on
every finite étale `T → X`, and duality holds at `ℤ/ℓ_T` for the transferred trace
`coverTrace π N t` on every connected finite étale `π : T → X`, then duality holds for `t` at
every finite type locally constant sheaf of `ℤ/ℓ`-modules on `X`. -/
theorem isDualityPerfect_of_isFiniteTypeLocallyConstant (N : ℕ)
    (t : Ext (unitSheaf (X := X) ℓ) (unitSheaf ℓ) N →+ ZMod ℓ)
    (hvan : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π]
      (K : EtaleModules.{u, 0} (ZMod ℓ) T), Subsingleton (Ext (unitSheaf (X := T) ℓ) K (N + 1)))
    (hconst : ∀ (T : Scheme.{u}) (π : T ⟶ X) [IsFinite π] [Etale π] [ConnectedSpace T],
      Ext.IsDualityPerfect (unitSheaf (X := T) ℓ) (unitSheaf ℓ) N (coverTrace π N t)
        (unitSheaf ℓ))
    (F : EtaleModules.{u, 0} (ZMod ℓ) X)
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology F) :
    Ext.IsDualityPerfect (unitSheaf (X := X) ℓ) (unitSheaf ℓ) N t F := by
  have hp : ℓ.Prime := Fact.out
  refine Ext.isDualityPerfect_of_resolution (unitSheaf (X := X) ℓ) (unitSheaf ℓ) N t
    (fun G => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology G)
    ?_ (fun K _ => hvan X (𝟙 X) K) (fun M j H φ => exists_extend_zmod H φ) F hF
  intro G hG
  obtain ⟨T, π, d, hfin, het, hconn, -, -, Xs, hhead, hlast⟩ :=
    exists_connected_primeToEll_finiteEtale_relSeries_constantRankOneStep hp G hG
  have := hfin
  have := het
  have := hconn
  have := surjective_of_finiteEtale_of_connectedSpace π
  let ε := (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).counit.app G
  have : Epi ε := epi_etaleModuleDirectImageInverseImageAdj_counit_app (ZMod ℓ) π G
  have hG₂ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology
      ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj G)) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules.{u, 0, 0} π
      (ZMod ℓ) _ (isFiniteTypeLocallyConstant_etaleModuleInverseImage π G hG)
  refine ⟨ShortComplex.mk (kernel.ι ε) ε (kernel.condition ε),
    { exact := ShortComplex.exact_kernel ε }, rfl, ?_, ?_⟩
  · exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_kernel.{u, u + 1, 0, 0}
      X.smallEtaleTopology (ZMod ℓ) ε hG₂ hG
  · exact (isDualityPerfect_directImage_iff π N t _).2
      (isDualityPerfect_of_relSeries_constantRankOneStep N _ (hvan T π) (hconst T π) _ Xs hhead
        hlast)

end Devissage

end Stacks.EtaleCohomology

end
