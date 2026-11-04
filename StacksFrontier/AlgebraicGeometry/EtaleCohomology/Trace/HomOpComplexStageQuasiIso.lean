module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HomOpComplexStageCochains

/-!
# Precomposition with a quasi-isomorphism on sections of the internal Hom complex

Let `X` be a scheme, `W` an étale `X`-scheme, `Λ` a ring with a ring map `ℤ/n ⟶ Λ`, `f : L' ⟶ L`
a quasi-isomorphism of complexes of sheaves of `Λ`-modules on `X_étale` and `M` the complex of
abelian sheaves underlying a bounded below complex `K` of injective sheaves of `ℤ/n`-modules.
Under the identification of sections over `W` of `ℋom^•_ℤ(L, M)` with the Hom complex
`Hom^•(L|_W, K|_W)` (`Stacks.EtaleCohomology.stageCochain`), the differential is the Hom-complex
differential (`Stacks.EtaleCohomology.stageCochain_d`) and precomposition with `f` is
precomposition with `f|_W` (`Stacks.EtaleCohomology.stageCochain_precomp`). As `K|_W` is
K-injective, precomposition with the quasi-isomorphism `f|_W` is bijective on cohomology classes
(`CochainComplex.HomComplex.cohomologyClassMap_bijective`), which gives the two elementwise
statements `Stacks.EtaleCohomology.exists_homOpComplexPrecomp_stage_eq_add_d` (surjectivity) and
`Stacks.EtaleCohomology.exists_homOpComplex_stage_eq_d` (injectivity) on the cohomology of the
complexes of sections over `W`.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-! ### Compatibility with the differential and with precomposition -/

section Differential

open CochainComplex.HomComplex Stacks.AbelianInternalHom

attribute [local instance] moduleCat_hasLimitsOfSize

variable {X : Scheme.{u}} (W : X.Etale) {Λ : Type} [Ring Λ] {n : ℕ} (ψ : ZMod n →+* Λ)
  (L : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λ)) ℤ)
  (K : CochainComplex (EtaleModules.{u, 0} (ZMod n) X) ℤ)

/-- The component at `U` of a sum of morphisms of sheaves of modules, evaluated at a section `x`,
is the sum of the components evaluated at `x`. -/
lemma sheafHom_add_app_apply
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λᵐᵒᵖ)}
    (f g : F ⟶ G) (U : X.Etaleᵒᵖ) (x : F.obj.obj U) :
    ((f + g).hom.app U).hom x = (f.hom.app U).hom x + (g.hom.app U).hom x :=
  rfl

/-- The component at `U` of a composite of morphisms of sheaves of modules, evaluated at a section
`x`, is the iterated evaluation of the components. -/
lemma sheafHom_comp_app_apply
    {F G H : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λᵐᵒᵖ)}
    (f : F ⟶ G) (g : G ⟶ H) (U : X.Etaleᵒᵖ) (x : F.obj.obj U) :
    ((f ≫ g).hom.app U).hom x = (g.hom.app U).hom ((f.hom.app U).hom x) :=
  rfl

/-- The component at `U` of the multiple of a morphism of sheaves of modules by a unit `k` of `ℤ`,
evaluated at a section `x`, is `k` times the component evaluated at `x`. -/
lemma sheafHom_units_smul_app_apply
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λᵐᵒᵖ)}
    (k : ℤˣ) (f : F ⟶ G) (U : X.Etaleᵒᵖ) (x : F.obj.obj U) :
    ((k • f).hom.app U).hom x = (k : ℤ) • (f.hom.app U).hom x := by
  rw [Units.smul_def]
  exact map_zsmul (AddMonoidHom.mk' (fun g : F ⟶ G => (g.hom.app U).hom x) (fun _ _ => rfl))
    (k : ℤ) f

/-- The factor `ℋom_ℤ(L^p, M^q)` of the differential of a section of `ℋom^•_ℤ(L, M)` over `W`
is the corresponding component of the differential. -/
lemma homOpComplexStageπ_homOpComplexD (m : ℤ) (x : HomOpIndex (m + 1))
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W)) :
    homOpComplexStageπ W L K x
        (((homOpComplexD X.smallEtaleTopology L (zmodForgetComplex K) m).hom.app (op W)).hom s) =
      ((homOpComplexDComponent X.smallEtaleTopology L (zmodForgetComplex K) m x).hom.app
        (op W)).hom s := by
  rw [← homOpComplexD_π]
  exact (sheafHom_comp_app_apply _ _ _ _).symm

/-- The component of the differential on sections over `W`:
`(δ s)^{p,q} = s^{p,q-1} ≫ d_M + (-1)^{m+1} d_L ≫ s^{p+1,q}`. -/
lemma homOpComplexDComponent_app_apply (m : ℤ) (x : HomOpIndex (m + 1))
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W)) :
    ((homOpComplexDComponent X.smallEtaleTopology L (zmodForgetComplex K) m x).hom.app
        (op W)).hom s =
      ((homOpMap X.smallEtaleTopology (L.X x.1.1)
          ((zmodForgetComplex K).d (x.1.2 - 1) x.1.2)).hom.app (op W)).hom
          (homOpComplexStageπ W L K (⟨(x.1.1, x.1.2 - 1), by have := x.2; lia⟩ : HomOpIndex m) s) +
        ((m + 1).negOnePow : ℤ) • ((homOpMapLeft X.smallEtaleTopology (L.d x.1.1 (x.1.1 + 1))
          ((zmodForgetComplex K).X x.1.2)).hom.app (op W)).hom
          (homOpComplexStageπ W L K
            (⟨(x.1.1 + 1, x.1.2), by have := x.2; lia⟩ : HomOpIndex m) s) := by
  unfold homOpComplexDComponent
  rw [sheafHom_add_app_apply, sheafHom_units_smul_app_apply, sheafHom_comp_app_apply,
    sheafHom_comp_app_apply]

/-- The first summand of the differential, as a cochain component. -/
lemma stageSectionHomPQ_homOpMap_stageπ (m : ℤ) (x : HomOpIndex (m + 1))
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W)) :
    stageSectionHomPQ W ψ L K x.1.1 x.1.2 (((homOpMap X.smallEtaleTopology (L.X x.1.1)
        ((zmodForgetComplex K).d (x.1.2 - 1) x.1.2)).hom.app (op W)).hom
          (homOpComplexStageπ W L K (⟨(x.1.1, x.1.2 - 1), by have := x.2; lia⟩ : HomOpIndex m) s)) =
      stageSectionHomPQ W ψ L K (⟨(x.1.1, x.1.2 - 1), by have := x.2; lia⟩ : HomOpIndex m).1.1
          (⟨(x.1.1, x.1.2 - 1), by have := x.2; lia⟩ : HomOpIndex m).1.2
          (homOpComplexStageπ W L K (⟨(x.1.1, x.1.2 - 1), by have := x.2; lia⟩ : HomOpIndex m) s) ≫
        (stageZModComplex W K).d (x.1.2 - 1) x.1.2 :=
  stageSectionHomPQ_homOpMap W ψ L K x.1.1 _

/-- The second summand of the differential, as a cochain component. -/
lemma stageSectionHomPQ_homOpMapLeft_stageπ (m : ℤ) (x : HomOpIndex (m + 1))
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W)) :
    stageSectionHomPQ W ψ L K x.1.1 x.1.2
      (((homOpMapLeft X.smallEtaleTopology (L.d x.1.1 (x.1.1 + 1))
        ((zmodForgetComplex K).X x.1.2)).hom.app (op W)).hom
          (homOpComplexStageπ W L K (⟨(x.1.1 + 1, x.1.2), by have := x.2; lia⟩ : HomOpIndex m) s)) =
      (stageComplex W ψ L).d x.1.1 (x.1.1 + 1) ≫
        stageSectionHomPQ W ψ L K (⟨(x.1.1 + 1, x.1.2), by have := x.2; lia⟩ : HomOpIndex m).1.1
          (⟨(x.1.1 + 1, x.1.2), by have := x.2; lia⟩ : HomOpIndex m).1.2
          (homOpComplexStageπ W L K (⟨(x.1.1 + 1, x.1.2), by have := x.2; lia⟩ : HomOpIndex m) s) :=
  stageSectionHomPQ_homOpMapLeft_d W ψ L K x.1.2 _

/-- The components of `stageCochain` of a differential. -/
lemma stageCochain_d_v (m : ℤ)
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W))
    (p q : ℤ) (hpq : p + (m + 1) = q) :
    (stageCochain W ψ L K (m + 1)
        (((homOpComplexD X.smallEtaleTopology L (zmodForgetComplex K) m).hom.app (op W)).hom
          s)).v p q hpq =
      (stageCochain W ψ L K m s).v p (q - 1) (by lia) ≫ (stageZModComplex W K).d (q - 1) q +
        (m + 1).negOnePow • ((stageComplex W ψ L).d p (p + 1) ≫
          (stageCochain W ψ L K m s).v (p + 1) q (by lia)) := by
  rw [stageCochain_v, homOpComplexStageπ_homOpComplexD, homOpComplexDComponent_app_apply,
    map_add, map_zsmul, stageSectionHomPQ_homOpMap_stageπ, stageSectionHomPQ_homOpMapLeft_stageπ,
    stageCochain_v, stageCochain_v, Units.smul_def]

/-- **`stageCochain` commutes with the differentials**: the differential of `ℋom^•_ℤ(L, M)` is
the Hom-complex differential `δ`. -/
lemma stageCochain_d (m : ℤ)
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W)) :
    stageCochain W ψ L K (m + 1)
        (((homOpComplexD X.smallEtaleTopology L (zmodForgetComplex K) m).hom.app (op W)).hom s) =
      δ m (m + 1) (stageCochain W ψ L K m s) :=
  Cochain.ext _ _ fun p q hpq => (stageCochain_d_v W ψ L K m s p q hpq).trans
    (δ_v m (m + 1) rfl _ p q hpq (q - 1) (p + 1) rfl rfl).symm

/-- **`stageCochain` commutes with precomposition** by a morphism of complexes `f : L' ⟶ L`. -/
lemma stageCochain_precomp
    {L' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λ)) ℤ}
    (f : L' ⟶ L) (m : ℤ)
    (s : (homOpComplexX X.smallEtaleTopology L (zmodForgetComplex K) m).obj.obj (op W)) :
    stageCochain W ψ L' K m (((homOpComplexPrecompX (M := zmodForgetComplex K) f m).hom.app
        (op W)).hom s) =
      cochainMap (((stageRestrict W ψ).mapHomologicalComplex _).map f) (𝟙 _) m
        (stageCochain W ψ L K m s) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  rw [cochainMap_v, stageCochain_v, stageCochain_v, HomologicalComplex.id_f, Category.comp_id]
  have e : homOpComplexStageπ W L' K ⟨(p, q), hpq⟩
      (((homOpComplexPrecompX (M := zmodForgetComplex K) f m).hom.app (op W)).hom s) =
      ((homOpMapLeft X.smallEtaleTopology (f.f (⟨(p, q), hpq⟩ : HomOpIndex m).1.1)
        ((zmodForgetComplex K).X (⟨(p, q), hpq⟩ : HomOpIndex m).1.2)).hom.app (op W)).hom
        (homOpComplexStageπ W L K ⟨(p, q), hpq⟩ s) := by
    show ((homOpComplexPrecompX (M := zmodForgetComplex K) f m ≫
      homOpComplexπ X.smallEtaleTopology L' (zmodForgetComplex K) m ⟨(p, q), hpq⟩).hom.app
        (op W)).hom s = _
    rw [homOpComplexPrecompX_π]
    rfl
  rw [e]
  exact stageSectionHomPQ_homOpMapLeft_f W ψ L K f _ _ _

end Differential

/-! ### Precomposition with a quasi-isomorphism on sections over `W` -/

section StageQuasiIso

open CochainComplex.HomComplex Stacks.AbelianInternalHom

attribute [local instance] moduleCat_hasLimitsOfSize

variable {X : Scheme.{u}} (W : X.Etale) {Λ : Type} [Ring Λ] {n : ℕ} (ψ : ZMod n →+* Λ)

/-- Restriction of scalars followed by restriction to `W_étale` is exact. -/
instance preservesHomology_stageRestrict : (stageRestrict W ψ).PreservesHomology := by
  have h := (Functor.exact_tfae (stageRestrict W ψ)).out 4 3
  exact h.mp ⟨inferInstance, inferInstance⟩

/-- **`K|_W` is K-injective** for a bounded below complex `K` of injective sheaves of
`ℤ/n`-modules: it is again a bounded below complex of injectives. -/
theorem isKInjective_stageZModComplex (K : CochainComplex (EtaleModules.{u, 0} (ZMod n) X) ℤ)
    (a : ℤ) [K.IsStrictlyGE a] [∀ q, Injective (K.X q)] :
    (stageZModComplex W K).IsKInjective := by
  have : (stageZModComplex W K).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact Functor.map_isZero (etaleModuleRestriction.{u, 0} (ZMod n) W.hom)
      (K.isZero_of_isStrictlyGE a i hi)
  have : ∀ q, Injective ((stageZModComplex W K).X q) := fun q =>
    injective_etaleModuleRestriction.{u, 0} (ZMod n) W.hom (K.X q)
  exact CochainComplex.isKInjective_of_injective _ a

variable {L L' : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) u} Λ)) ℤ}
  (f : L' ⟶ L) [QuasiIso f]
  (K : CochainComplex (EtaleModules.{u, 0} (ZMod n) X) ℤ) (a : ℤ) [K.IsStrictlyGE a]
  [∀ q, Injective (K.X q)]

include a f ψ in
/-- **Surjectivity on cohomology over `W`**: a cocycle of `Γ(W, ℋom^•_ℤ(L', M))` is the image of
a cocycle of `Γ(W, ℋom^•_ℤ(L, M))` up to a coboundary, for `f : L' ⟶ L` a quasi-isomorphism and
`M` the complex underlying a bounded below complex `K` of injective `ℤ/n`-sheaves. -/
theorem exists_homOpComplexPrecomp_stage_eq_add_d (m : ℤ)
    (y : ((homOpComplex X.smallEtaleTopology L' (zmodForgetComplex K)).X (m + 1)).obj.obj
      (op W))
    (hy : (((homOpComplex X.smallEtaleTopology L' (zmodForgetComplex K)).d (m + 1)
      (m + 1 + 1)).hom.app (op W)).hom y = 0) :
    ∃ x : ((homOpComplex X.smallEtaleTopology L (zmodForgetComplex K)).X (m + 1)).obj.obj
        (op W),
      (((homOpComplex X.smallEtaleTopology L (zmodForgetComplex K)).d (m + 1)
        (m + 1 + 1)).hom.app (op W)).hom x = 0 ∧
      ∃ z : ((homOpComplex X.smallEtaleTopology L' (zmodForgetComplex K)).X m).obj.obj (op W),
        y = (((homOpComplexPrecomp (M := zmodForgetComplex K) f).f (m + 1)).hom.app
            (op W)).hom x +
          (((homOpComplex X.smallEtaleTopology L' (zmodForgetComplex K)).d m
            (m + 1)).hom.app (op W)).hom z := by
  have := isKInjective_stageZModComplex W K a
  have hy' : ((homOpComplexD X.smallEtaleTopology L' (zmodForgetComplex K) (m + 1)).hom.app
      (op W)).hom y = 0 := by
    rwa [homOpComplex_d] at hy
  have hc : δ (m + 1) (m + 1 + 1) (stageCochain W ψ L' K (m + 1) y) = 0 :=
    (stageCochain_d W ψ L' K (m + 1) y).symm.trans
      ((congrArg (stageCochain W ψ L' K (m + 1 + 1)) hy').trans (map_zero _))
  let z' : Cocycle (stageComplex W ψ L') (stageZModComplex W K) (m + 1) :=
    Cocycle.mk _ (m + 1 + 1) rfl hc
  let g := ((stageRestrict W ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  obtain ⟨c, hc'⟩ := (cohomologyClassMap_bijective g (𝟙 _) (m + 1)).2 (CohomologyClass.mk z')
  obtain ⟨z, rfl⟩ := c.mk_surjective
  have h1 : CohomologyClass.mk (z' - cocycleMap g (𝟙 _) (m + 1) z) = 0 := by
    rw [CohomologyClass.mk_sub, ← hc']
    exact sub_self _
  rw [CohomologyClass.mk_eq_zero_iff] at h1
  obtain ⟨β, hβ⟩ := (mem_coboundaries_iff _ m rfl).1 h1
  obtain ⟨x, hx⟩ := (bijective_stageCochain W ψ L K (m + 1)).2 z.1
  obtain ⟨w, hw⟩ := (bijective_stageCochain W ψ L' K m).2 β
  refine ⟨x, ?_, w, ?_⟩
  · rw [homOpComplex_d]
    apply (bijective_stageCochain W ψ L K (m + 1 + 1)).1
    exact (stageCochain_d W ψ L K (m + 1) x).trans ((congrArg (δ (m + 1) (m + 1 + 1)) hx).trans
      (((Cocycle.mem_iff (m + 1) (m + 1 + 1) rfl z.1).1 z.2).trans (map_zero _).symm))
  · rw [homOpComplex_d]
    apply (bijective_stageCochain W ψ L' K (m + 1)).1
    have hpx : stageCochain W ψ L' K (m + 1)
        (((homOpComplexPrecompX (M := zmodForgetComplex K) f (m + 1)).hom.app (op W)).hom x) =
          cochainMap g (𝟙 _) (m + 1) z.1 :=
      (stageCochain_precomp W ψ L K f (m + 1) x).trans (congrArg _ hx)
    have hdw : stageCochain W ψ L' K (m + 1)
        (((homOpComplexD X.smallEtaleTopology L' (zmodForgetComplex K) m).hom.app (op W)).hom w) =
          (z' : Cochain _ _ (m + 1)) - cochainMap g (𝟙 _) (m + 1) z.1 :=
      (stageCochain_d W ψ L' K m w).trans ((congrArg (δ m (m + 1)) hw).trans hβ)
    calc stageCochain W ψ L' K (m + 1) y
        = cochainMap g (𝟙 _) (m + 1) z.1 +
            ((z' : Cochain _ _ (m + 1)) - cochainMap g (𝟙 _) (m + 1) z.1) :=
          (add_sub_cancel _ _).symm
      _ = _ := (congrArg₂ (· + ·) hpx.symm hdw.symm).trans (map_add _ _ _).symm

include a f ψ in
/-- **Injectivity on cohomology over `W`**: a cocycle of `Γ(W, ℋom^•_ℤ(L, M))` whose image in
`Γ(W, ℋom^•_ℤ(L', M))` is a coboundary is a coboundary. -/
theorem exists_homOpComplex_stage_eq_d (m : ℤ)
    (x : ((homOpComplex X.smallEtaleTopology L (zmodForgetComplex K)).X (m + 1)).obj.obj (op W))
    (hx : (((homOpComplex X.smallEtaleTopology L (zmodForgetComplex K)).d (m + 1)
      (m + 1 + 1)).hom.app (op W)).hom x = 0)
    (z : ((homOpComplex X.smallEtaleTopology L' (zmodForgetComplex K)).X m).obj.obj (op W))
    (hz : (((homOpComplexPrecomp (M := zmodForgetComplex K) f).f (m + 1)).hom.app (op W)).hom x =
      (((homOpComplex X.smallEtaleTopology L' (zmodForgetComplex K)).d m (m + 1)).hom.app
        (op W)).hom z) :
    ∃ w : ((homOpComplex X.smallEtaleTopology L (zmodForgetComplex K)).X m).obj.obj (op W),
      x = (((homOpComplex X.smallEtaleTopology L (zmodForgetComplex K)).d m (m + 1)).hom.app
        (op W)).hom w := by
  have := isKInjective_stageZModComplex W K a
  have hx' : ((homOpComplexD X.smallEtaleTopology L (zmodForgetComplex K) (m + 1)).hom.app
      (op W)).hom x = 0 := by
    rwa [homOpComplex_d] at hx
  have hz' : ((homOpComplexPrecompX (M := zmodForgetComplex K) f (m + 1)).hom.app (op W)).hom x =
      ((homOpComplexD X.smallEtaleTopology L' (zmodForgetComplex K) m).hom.app (op W)).hom z := by
    rwa [homOpComplex_d] at hz
  have hc : δ (m + 1) (m + 1 + 1) (stageCochain W ψ L K (m + 1) x) = 0 :=
    (stageCochain_d W ψ L K (m + 1) x).symm.trans
      ((congrArg (stageCochain W ψ L K (m + 1 + 1)) hx').trans (map_zero _))
  let zc : Cocycle (stageComplex W ψ L) (stageZModComplex W K) (m + 1) :=
    Cocycle.mk _ (m + 1 + 1) rfl hc
  let g := ((stageRestrict W ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  have h1 : cohomologyClassMap g (𝟙 _) (m + 1) (CohomologyClass.mk zc) = 0 := by
    show CohomologyClass.mk (cocycleMap g (𝟙 _) (m + 1) zc) = 0
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m rfl]
    exact ⟨stageCochain W ψ L' K m z, ((stageCochain_d W ψ L' K m z).symm.trans
      (congrArg (stageCochain W ψ L' K (m + 1)) hz'.symm)).trans
        (stageCochain_precomp W ψ L K f (m + 1) x)⟩
  have h2 : CohomologyClass.mk zc = 0 :=
    (cohomologyClassMap_bijective g (𝟙 _) (m + 1)).1 (h1.trans (map_zero _).symm)
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m rfl] at h2
  obtain ⟨α, hα⟩ := h2
  obtain ⟨w, hw⟩ := (bijective_stageCochain W ψ L K m).2 α
  refine ⟨w, ?_⟩
  rw [homOpComplex_d]
  exact (bijective_stageCochain W ψ L K (m + 1)).1
    ((stageCochain_d W ψ L K m w).trans ((congrArg (δ m (m + 1)) hw).trans hα)).symm

end StageQuasiIso

end Stacks.EtaleCohomology
