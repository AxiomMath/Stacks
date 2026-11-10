module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveOpenDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportIntegralCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SurjectiveEtaleFaithful
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairingGysin
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ConnectingSurjective

/-!
# Poincaré duality on an open of a curve, pushed forward along a finite étale cover

Let `j : V → Y` be an open immersion, `π : T → V` finite étale, and
```
T  --jT--> T̄
|π          |π̄
V  --j-->  Y
```
a cartesian square with `jT` an open immersion and `π̄` integral (for a smooth curve `V` this is
the smooth projective compactification of the cover, `AlgebraicGeometry.CoverCompactification`).
Then `j_! π_* ≅ π̄_* jT_!`, and for every sheaf `G` on `T` the map

`Ext^q_T̄(jT_! G, jT_! E) → Ext^q_Y(π̄_* jT_! G, Λ_Y)`, `y ↦ π̄_* y ∘ Γ`,

is bijective, where `E = π^{-1} j^{-1} Λ_Y` and
`Γ : π̄_* jT_! E ≅ j_! π_* π^{-1} j^{-1} Λ_Y → j_! j^{-1} Λ_Y → Λ_Y` is the trace of `π` followed
by the counit of `j_! ⊣ j^{-1}`: both sides are `Ext^q_T(G, E)`, through `jT_! ⊣ jT^{-1}`, the
duality `π_* ⊣ π^{-1}` of the finite étale `π`, and `j_! ⊣ j^{-1}`.
By `CategoryTheory.Abelian.Ext.isDualityPerfect_obj_iff_gysinTrace` (with `c = 0`), duality on `Y`
at `j_! π_* G` is duality on `T̄` at `jT_! G`.

## Main definitions

* `Stacks.EtaleCohomology.coverTraceClass`: the class `Γ`.

## Main results

* `Stacks.EtaleCohomology.bijective_mapExactFunctor_comp_coverTraceClass`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable {ℓ : ℕ} [Fact ℓ.Prime]

section Transfer

variable {V T Tb Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j] (jT : T ⟶ Tb) [IsOpenImmersion jT]
  (π : T ⟶ V) [IsFinite π] [Etale π] (πb : Tb ⟶ Y) [IsIntegralHom πb]
  (sq : IsPullback π jT j πb)

/-- The coefficient `E = π^{-1} j^{-1} Λ_Y` on the cover. -/
abbrev coverCoefficient : EtaleModules.{u, 0} (ZMod ℓ) T :=
  (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).obj
    ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := Y) ℓ))

/-- **The trace class of the cover** `Γ : π̄_* jT_! E ≅ j_! π_* E → j_! j^{-1} Λ_Y → Λ_Y`. -/
def coverTraceClass :
    Ext ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) πb).obj
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj (coverCoefficient (ℓ := ℓ) j π)))
      (unitSheaf (X := Y) ℓ) 0 :=
  Ext.mk₀ ((inv (extensionByZeroDirectImageNatTrans (ZMod ℓ) j jT π πb sq)).app _ ≫
    (etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j).map
      ((etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).counit.app
        ((etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := Y) ℓ))) ≫
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j).counit.app (unitSheaf (X := Y) ℓ))

/-- **The duality of the cover**: `y ↦ π̄_* y ∘ Γ` is a bijection
`Ext^q_T̄(jT_! G, jT_! E) ≅ Ext^q_Y(π̄_* jT_! G, Λ_Y)`. -/
theorem bijective_mapExactFunctor_comp_coverTraceClass (G : EtaleModules.{u, 0} (ZMod ℓ) T)
    (q : ℕ) :
    Function.Bijective (fun y : Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj G)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT).obj (coverCoefficient (ℓ := ℓ) j π)) q =>
      (y.mapExactFunctor (etaleModuleDirectImage.{u, 0} (ZMod ℓ) πb)).comp
        (coverTraceClass (ℓ := ℓ) j jT π πb sq) (add_zero q)) := by
  let jTS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jT
  let jS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) j
  let πS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) π
  let πbS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) πb
  let ε := extensionByZeroDirectImageNatTrans (ZMod ℓ) j jT π πb sq
  let E := coverCoefficient (ℓ := ℓ) j π
  let B := (etaleModuleRestriction.{u, 0} (ZMod ℓ) j).obj (unitSheaf (X := Y) ℓ)
  let adjπ := etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π
  let adjj := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) j
  have hT := Stacks.ExtAdjunction.mapExtAddHom_bijective
    (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) jT) G E q
  rw [← Function.Bijective.of_comp_iff _ hT]
  have key : ∀ z : Ext G E q,
      ((z.mapExactFunctor jTS).mapExactFunctor πbS).comp
        (coverTraceClass (ℓ := ℓ) j jT π πb sq) (add_zero q) =
      (Ext.mk₀ ((inv ε).app G)).comp (Stacks.ExtAdjunction.extMap adjj (πS.obj G)
        (unitSheaf (X := Y) ℓ) q (Stacks.ExtAdjunction.extMap adjπ G B q z)) (zero_add q) := by
    intro z
    rw [coverTraceClass, Stacks.ExtAdjunction.extMap_apply, Stacks.ExtAdjunction.extMap_apply,
      Stacks.ExtFunctorial.mapExactFunctor_comp_functor jTS πbS G q z,
      ← Ext.mk₀_comp_mk₀, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
      ← Ext.comp_assoc_of_third_deg_zero]
    have hnat := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor (inv ε) G q z
    have h1 : (z.mapExactFunctor (jTS ⋙ πbS)).comp (Ext.mk₀ ((inv ε).app E)) (add_zero q) =
        (Ext.mk₀ ((inv ε).app G)).comp (z.mapExactFunctor (πS ⋙ jS)) (zero_add q) :=
      hnat.symm
    rw [h1, Ext.comp_assoc _ _ _ (zero_add q) (add_zero q) (by omega), Ext.mapExactFunctor_comp,
      Ext.mapExactFunctor_mk₀, Stacks.ExtFunctorial.mapExactFunctor_comp_functor πS jS G q z,
      Ext.comp_assoc_of_third_deg_zero]
  have hfun : (fun y : Ext (jTS.obj G) (jTS.obj E) q =>
        (y.mapExactFunctor πbS).comp (coverTraceClass (ℓ := ℓ) j jT π πb sq) (add_zero q)) ∘
        ⇑(jTS.mapExtAddHom G E q) =
      (fun w => (Ext.mk₀ ((inv ε).app G)).comp w (zero_add q)) ∘
        ⇑(Stacks.ExtAdjunction.extMap adjj (πS.obj G) (unitSheaf (X := Y) ℓ) q) ∘
        ⇑(Stacks.ExtAdjunction.extMap adjπ G B q) := by
    funext z
    exact key z
  rw [hfun]
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q).comp
    ((Stacks.ExtAdjunction.extMap_bijective adjj _ _ q).comp
      (Stacks.ExtAdjunction.extMap_bijective adjπ _ _ q))

end Transfer

section Helpers

/-- **Duality at a successive extension of copies of `ℤ/ℓ`, pushed by an exact functor.** -/
theorem isDualityPerfect_map_of_relSeries_constantRankOneStep {T Tb : Scheme.{u}}
    (Φ : EtaleModules.{u, 0} (ZMod ℓ) T ⥤ EtaleModules.{u, 0} (ZMod ℓ) Tb) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (O D : EtaleModules.{u, 0} (ZMod ℓ) Tb)
    (N : ℕ) (t : Ext O D N →+ ZMod ℓ)
    (hvan : ∀ K : EtaleModules.{u, 0} (ZMod ℓ) T, Subsingleton (Ext O (Φ.obj K) (N + 1)))
    (hconst : Ext.IsDualityPerfect O D N t (Φ.obj (unitSheaf (X := T) ℓ)))
    (hconst' : ∀ q, N < q → Subsingleton (Ext (Φ.obj (unitSheaf (X := T) ℓ)) D q))
    (G : EtaleModules.{u, 0} (ZMod ℓ) T) (Xs : RelSeries (ConstantRankOneStep.{0} ℓ G))
    (hhead : IsZero (Subobject.underlying.obj Xs.head)) (hlast : IsIso Xs.last.arrow) :
    Ext.IsDualityPerfect O D N t (Φ.obj G) ∧ ∀ q, N < q → Subsingleton (Ext (Φ.obj G) D q) := by
  have hA : ∀ (M : EtaleModules.{u, 0} (ZMod ℓ) Tb) (j : ℕ) (H : AddSubgroup (Ext M D j))
      (φ : H →+ ZMod ℓ), ∃ ψ : Ext M D j →+ ZMod ℓ, ∀ x : H, ψ x = φ x :=
    fun M j H φ => exists_extend_zmod H φ
  have key : ∀ i : Fin (Xs.length + 1), Ext.IsDualityPerfect O D N t
      (Φ.obj (Subobject.underlying.obj (Xs i))) ∧
      ∀ q, N < q → Subsingleton (Ext (Φ.obj (Subobject.underlying.obj (Xs i))) D q) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      have h0 : IsZero (Φ.obj (Subobject.underlying.obj Xs.head)) := Φ.map_isZero hhead
      refine ⟨Ext.isDualityPerfect_of_retract (0 : _ ⟶ Φ.obj (unitSheaf (X := T) ℓ)) 0
        (h0.eq_of_src _ _) hconst, fun q hq => ?_⟩
      have h0' : IsZero (Φ.obj (Subobject.underlying.obj (Xs 0))) := h0
      exact ⟨fun a b => by
        rw [← Ext.mk₀_id_comp a, ← Ext.mk₀_id_comp b, h0'.eq_of_src (𝟙 _) 0, Ext.mk₀_zero,
          Ext.zero_comp, Ext.zero_comp]⟩
    | succ i ih =>
      obtain ⟨hle, ⟨e⟩⟩ := Xs.step i
      let S := ShortComplex.mk (Subobject.ofLE _ _ hle) (cokernel.π (Subobject.ofLE _ _ hle))
        (cokernel.condition _)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
      have hS' := hS.map_of_exact Φ
      let e' : Φ.obj S.X₃ ≅ Φ.obj (unitSheaf (X := T) ℓ) := Φ.mapIso e
      have h₃ : Ext.IsDualityPerfect O D N t (S.map Φ).X₃ :=
        Ext.isDualityPerfect_of_retract e'.hom e'.inv e'.hom_inv_id hconst
      have h₃' : ∀ q, N < q → Subsingleton (Ext (S.map Φ).X₃ D q) := fun q hq =>
        have := hconst' q hq
        (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := D) e'.hom q).2.subsingleton
      have : Subsingleton (Ext O (S.map Φ).X₁ (N + 1)) := hvan S.X₁
      have := h₃' (N + 1) (by omega)
      exact ⟨Ext.isDualityPerfect_X₂ hS' ih.1 h₃ inferInstance inferInstance hA, fun q hq =>
        Ext.subsingleton_ext_left_X₂_of_shortExact hS' D (ih.2 q hq) (h₃' q hq)⟩
  obtain ⟨h1, h2⟩ := key (Fin.last _)
  let ι := Φ.map Xs.last.arrow
  have : IsIso ι := inferInstance
  refine ⟨Ext.isDualityPerfect_of_retract (inv ι) ι (by simp) h1, fun q hq => ?_⟩
  have : Subsingleton (Ext (Φ.obj (Subobject.underlying.obj Xs.last)) D q) := h2 q hq
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := D) (inv ι) q).2.subsingleton

end Helpers

section Cover

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [IsProper f]

include f in
/-- **Poincaré duality at the direct image of a unipotent sheaf along a finite étale cover of an
open of a curve.** Let `V` be a nonempty open of `Y` with finite complement of closed points,
`π : T → V` finite étale with `T` connected, and `G` a sheaf on `T` with a finite filtration whose
successive quotients are `Λ_T`. Given local purity, duality holds on `Y` at `j_! π_* G` for every
injective trace on `H²(Y)`, and `Ext^q(j_! π_* G, Λ_Y) = 0` for `q > 2`. -/
theorem isDualityPerfect_extensionByZero_directImage_of_relSeries (hℓ : IsUnit (ℓ : k))
    (hpurity : LocalPurity ℓ k) (t : Ext (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 →+ ZMod ℓ)
    (ht : Function.Injective t) (S : Finset Y) (hS : ∀ y ∈ S, IsClosed ({y} : Set Y))
    (V : Y.Opens) (hV : (V : Set Y) = (↑S : Set Y)ᶜ) [Nonempty V]
    {T : Scheme.{u}} (π : T ⟶ V) [IsFinite π] [Etale π] [ConnectedSpace T]
    (G : EtaleModules.{u, 0} (ZMod ℓ) T) (Xs : RelSeries (ConstantRankOneStep.{0} ℓ G))
    (hhead : IsZero (Subobject.underlying.obj Xs.head)) (hlast : IsIso Xs.last.arrow) :
    Ext.IsDualityPerfect (unitSheaf (X := Y) ℓ) (unitSheaf ℓ) 2 t
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj G)) ∧
      ∀ q, 2 < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι).obj
          ((etaleModuleDirectImage.{u, 0} (ZMod ℓ) π).obj G)) (unitSheaf (X := Y) ℓ) q) := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hdimY : topologicalKrullDim Y ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have : IsCurve k (V.ι ≫ f) := isCurve_opensι_comp k f V
  let C : CoverCompactification k f V.ι π :=
    (nonempty_coverCompactification k (V.ι ≫ f) f V.ι rfl π).some
  have hdimTb : topologicalKrullDim C.Vb ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := C.q)).le
  have sq : IsPullback π C.j V.ι C.fb := C.isPullback.flip
  let ΛY := unitSheaf (X := Y) ℓ
  let ΛTb := unitSheaf (X := C.Vb) ℓ
  let E := coverCoefficient (ℓ := ℓ) V.ι π
  let Γ := coverTraceClass (ℓ := ℓ) V.ι C.j π C.fb sq
  let adjb := etaleModuleInverseImageAdj.{u, 0} (ZMod ℓ) C.fb
  let jTS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) C.j
  let πbS := etaleModuleDirectImage.{u, 0} (ZMod ℓ) C.fb
  let adjT := etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) C.j
  let D' := (etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) C.j).obj ΛTb
  let cT := adjT.counit.app ΛTb
  -- the complement of `T` in `T̄`
  let Sb := C.finite_compl.toFinset
  have hSb : ∀ y ∈ Sb, IsClosed ({y} : Set C.Vb) := fun y hy =>
    C.isClosed_compl y ((Set.Finite.mem_toFinset C.finite_compl).1 hy)
  have hjT : Set.range C.j.base = (↑Sb : Set C.Vb)ᶜ := by
    rw [Set.Finite.coe_toFinset, compl_compl]
  have : Nonempty T := ConnectedSpace.toNonempty
  -- (A) duality on `Y` at `π̄_* jT_! G` is duality on `T̄` at `jT_! G`
  have hβ := bijective_mapExactFunctor_comp_coverTraceClass (ℓ := ℓ) V.ι C.j π C.fb sq
  have hgys := Ext.isDualityPerfect_obj_iff_gysinTrace adjb ΛY (jTS.obj E) ΛY
    (show 2 + 0 = 2 from rfl) Γ t (jTS.obj G) (fun q => hβ G q)
    (fun i hi => subsingleton_ext_unitSheaf_of_curve f hdimY _ i hi)
    (fun j hj => absurd hj (Nat.not_lt_zero j))
  -- the coefficients on `T̄`
  let eO : (etaleModuleInverseImage.{u, 0} (ZMod ℓ) C.fb).obj ΛY ≅ ΛTb :=
    (etaleModuleInverseImageConstantIso.{u, 0} (ZMod ℓ) C.fb).app
      (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  let eE₀ : E ≅ (etaleModuleRestriction.{u, 0} (ZMod ℓ) C.j).obj ΛTb :=
    (etaleModuleInverseImage.{u, 0} (ZMod ℓ) π).mapIso
        (unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) V.ι).symm ≪≫
      unitSheafInverseImageIso π ≪≫ unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) C.j
  let eE : jTS.obj E ≅ D' := jTS.mapIso eE₀
  -- `y ↦ y ∘ ε` on `Ext(jT_! G, -)` is bijective
  have hβ' : ∀ (M : EtaleModules.{u, 0} (ZMod ℓ) T) (q : ℕ),
      Function.Bijective (fun y : Ext (jTS.obj M) D' q => y.comp (Ext.mk₀ cT) (add_zero q)) := by
    intro M q
    have : IsIso ((etaleModuleRestriction.{u, 0} (ZMod ℓ) C.j).map cT) :=
      isIso_etaleModuleRestriction_map_counit_of_factors (ZMod ℓ) C.j C.j (𝟙 T)
        (Category.id_comp _) ΛTb
    have hE := Stacks.ExtAdjunction.extMap_bijective adjT M D' q
    rw [← Function.Bijective.of_comp_iff _ hE]
    have hfun : (fun y : Ext (jTS.obj M) D' q => y.comp (Ext.mk₀ cT) (add_zero q)) ∘
        ⇑(Stacks.ExtAdjunction.extMap adjT M D' q) =
        ⇑(Stacks.ExtAdjunction.extMap adjT M ΛTb q) ∘
          (fun e => e.comp (Ext.mk₀ ((etaleModuleRestriction.{u, 0} (ZMod ℓ) C.j).map cT))
            (add_zero q)) := by
      funext e
      exact (Stacks.ExtAdjunction.extMap_naturality_mk₀ adjT M cT q e).symm
    rw [hfun]
    exact (Stacks.ExtAdjunction.extMap_bijective adjT M ΛTb q).comp
      (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso _ q)
  -- excision on `T̄`, and the induced trace `t₀` on `H²(T̄)`
  have hexc := bijective_comp_counit_ext_two_of_curve C.q hℓ hpurity Sb hSb C.j hjT
  let eexc := AddEquiv.ofBijective ((Ext.mk₀ cT).postcomp ΛTb (add_zero 2)) hexc
  let tg := Ext.gysinTrace adjb ΛY (jTS.obj E) ΛY (show 2 + 0 = 2 from rfl) Γ t
  let t'' := Ext.transportTrace tg eO eE
  let t₀ : Ext ΛTb ΛTb 2 →+ ZMod ℓ := t''.comp eexc.symm.toAddMonoidHom
  have ht₀ : Ext.compTrace (show 2 + 0 = 2 from rfl) (Ext.mk₀ cT) t₀ = t'' := by
    ext z
    change t'' (eexc.symm (eexc z)) = t'' z
    rw [AddEquiv.symm_apply_apply]
  -- `t₀` is injective
  have ht₀inj : Function.Injective t₀ := by
    -- the transfer `H²_c(T) → H²(Y)` is onto
    have hY2 : Nat.card (Ext ΛY ΛY 2) = ℓ := natCard_ext_two_unitSheaf f hℓ
    have : Finite (Ext ΛY ΛY 2) := Nat.finite_of_card_ne_zero (by rw [hY2]; exact hp.ne_zero)
    have : Nontrivial (Ext ΛY ΛY 2) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hY2]; exact hp.one_lt)
    obtain ⟨z, hz⟩ := exists_ne (0 : Ext ΛY ΛY 2)
    have htz : t z ≠ 0 := fun h0 => hz (ht (h0.trans (map_zero t).symm))
    have : Surjective π := surjective_of_finiteEtale_of_connectedSpace π
    let B := (etaleModuleRestriction.{u, 0} (ZMod ℓ) V.ι).obj ΛY
    let jS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) V.ι
    let tr := (etaleModuleDirectImageInverseImageAdj.{u, 0} (ZMod ℓ) π).counit.app B
    have : Epi tr := epi_etaleModuleDirectImageInverseImageAdj_counit_app (ZMod ℓ) π B
    let g := jS.map tr
    have : Epi g := inferInstance
    let SS := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
    have hSS : SS.ShortExact := { exact := ShortComplex.exact_kernel g }
    have hsurj₂ := Ext.surjective_comp_mk₀_g_of_subsingleton hSS ΛY 2
      (subsingleton_ext_unitSheaf_of_curve f hdimY _ 3 (by omega))
    have hsurj₃ := (bijective_comp_counit_ext_two_of_curve f hℓ hpurity S hS V.ι
      (by rw [Scheme.Opens.range_ι]; exact hV)).2
    obtain ⟨x₃, hx₃⟩ := hsurj₃ z
    obtain ⟨x₂, hx₂⟩ := hsurj₂ x₃
    let εE := (extensionByZeroDirectImageNatTrans (ZMod ℓ) V.ι C.j π C.fb sq).app E
    let x₁ := x₂.comp (Ext.mk₀ εE) (add_zero 2)
    have hεE : εE ≫ (inv (extensionByZeroDirectImageNatTrans (ZMod ℓ) V.ι C.j π C.fb sq)).app E =
        𝟙 _ := by
      rw [← NatTrans.comp_app, IsIso.hom_inv_id, NatTrans.id_app]
    have hx₁ : x₁.comp Γ (add_zero 2) = z := by
      rw [← hx₃, ← hx₂]
      change (x₂.comp (Ext.mk₀ εE) (add_zero 2)).comp
          (Ext.mk₀ ((inv (extensionByZeroDirectImageNatTrans (ZMod ℓ) V.ι C.j π C.fb sq)).app _ ≫
            g ≫ (etaleModuleExtensionByZeroAdj.{u, 0} (ZMod ℓ) V.ι).counit.app ΛY)) (add_zero 2) =
        (x₂.comp (Ext.mk₀ g) (add_zero 2)).comp (Ext.mk₀ ((etaleModuleExtensionByZeroAdj.{u, 0}
          (ZMod ℓ) V.ι).counit.app ΛY)) (add_zero 2)
      rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, reassoc_of% hεE,
        Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
    -- so the Gysin trace does not vanish
    have htg : tg ((Stacks.ExtAdjunction.extMap adjb ΛY (jTS.obj E) 2 x₁).comp
        (Ext.mk₀ (𝟙 (jTS.obj E))) (add_zero 2)) ≠ 0 := by
      rw [Ext.gysinTrace_comp_extMap, Ext.mapExactFunctor_mk₀, πbS.map_id, Ext.mk₀_id_comp, hx₁]
      exact htz
    -- `t''` is injective, its domain having `ℓ` elements
    have hcard : Nat.card (Ext ΛTb D' 2) = ℓ :=
      (Nat.card_eq_of_bijective _ hexc).trans (natCard_ext_two_unitSheaf C.q hℓ)
    have ht'' : Function.Injective t'' := by
      refine injective_of_prime_card t'' hcard fun h0 => htg ?_
      have := DFunLike.congr_fun h0 (((Ext.mk₀ eO.inv).comp (Stacks.ExtAdjunction.extMap adjb ΛY
        (jTS.obj E) 2 x₁) (zero_add 2)).comp ((Ext.mk₀ (𝟙 (jTS.obj E))).comp (Ext.mk₀ eE.hom)
          (add_zero 0)) (add_zero 2))
      rw [AddMonoidHom.zero_apply, show t'' = Ext.transportTrace tg eO eE from rfl,
        Ext.transportTrace_comp] at this
      exact this
    exact ht''.comp eexc.symm.injective
  -- duality on `T̄` at `jT_! G` for `t₀`
  obtain ⟨hU₁, hU₂⟩ := isDualityPerfect_extensionByZeroOfRestriction_unitSheaf_of_isOpenImmersion
    C.q hℓ hpurity t₀ ht₀inj Sb hSb C.j hjT
  let eΛ : jTS.obj (unitSheaf (X := T) ℓ) ≅ D' :=
    jTS.mapIso (unitSheafIsoRestrictionOfIsOpenImmersion (ℓ := ℓ) C.j)
  obtain ⟨hG₁, hG₂⟩ := isDualityPerfect_map_of_relSeries_constantRankOneStep jTS ΛTb ΛTb 2 t₀
    (fun K => subsingleton_ext_unitSheaf_of_curve C.q hdimTb _ 3 (by omega))
    (Ext.isDualityPerfect_of_iso eΛ.symm hU₁)
    (fun q hq =>
      have := hU₂ q hq
      (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := ΛTb) eΛ.hom q).2.subsingleton)
    G Xs hhead hlast
  -- back to `Y`
  have hT : Ext.IsDualityPerfect ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) C.fb).obj ΛY)
      (jTS.obj E) 2 tg (jTS.obj G) := by
    refine (Ext.isDualityPerfect_transport_iff tg eO eE (jTS.obj G)).2 ?_
    rw [show Ext.transportTrace tg eO eE = t'' from rfl, ← ht₀]
    exact (Ext.isDualityPerfect_iff_compTrace (show 2 + 0 = 2 from rfl) (Ext.mk₀ cT) t₀
      (jTS.obj G) (hβ' G) (fun i hi => subsingleton_ext_unitSheaf_of_curve C.q hdimTb _ i hi)
      (fun j hj => absurd hj (Nat.not_lt_zero j))).1 hG₁
  let ε := asIso ((extensionByZeroDirectImageNatTrans (ZMod ℓ) V.ι C.j π C.fb sq).app G)
  refine ⟨Ext.isDualityPerfect_of_iso ε.symm (hgys.2 hT), fun q hq => ?_⟩
  have : Subsingleton (Ext (jTS.obj G) ((𝟭 _).obj ΛTb) q) := hG₂ q hq
  have : Subsingleton (Ext (jTS.obj G) D' q) := (hβ' G q).1.subsingleton
  have : Subsingleton (Ext (jTS.obj G) (jTS.obj E) q) :=
    (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (X := jTS.obj G) eE.hom q).1.subsingleton
  have : Subsingleton (Ext ((jTS ⋙ πbS).obj G) ΛY q) := (hβ G q).2.subsingleton
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso (Z := ΛY) ε.hom q).2.subsingleton

end Cover

end Stacks.EtaleCohomology

end
