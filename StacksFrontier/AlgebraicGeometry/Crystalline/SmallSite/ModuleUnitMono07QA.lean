module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechPullback07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CechResolutionOpen07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Comparison07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisModuleInverseImageValues

/-!
# The module unit of an iterated `α_p`-cover is injective on sections

This file proves that, for `f : X' ⟶ X` an iterated `α_p`-cover over the closed fibre of a
divided power base with `p` in the divided power ideal and `ℱ` a crystal in quasi-coherent
`𝒪_{X/S}`-modules, `u_{X/S, *}` of the module unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` is a monomorphism.
By `...SmallSite.mono_homologyMap_moduleComparison07Q9_iff` this is the vanishing of `ℋ^{-1}` of
the cone of the comparison map of [Stacks, Tag 07Q9], which the cokernel bound of
[Stacks, Tag 07QA] uses.

## Main results

* `mono_of_injective_app_of_isBasis` — a morphism of abelian sheaves on `X_Zar` injective on the
  sections over every member of a basis is a monomorphism.
* `injective_zariskiDirectImage_map_app_of_cechSystemHom` — for a morphism `μ : ℱ ⟶ f_{cris, *}𝒢`
  and a morphism of Čech systems over `f` into a pro-covering of an open `W`, injectivity of `μ`
  followed by the evaluation at every level of the system gives injectivity of `u_{X/S, *}μ` on
  the sections over `W`.
* `crisModuleUnit_app_comp_crisDirectImageEval` — the module unit followed by the evaluation of
  `f_{cris, *}` at `τ : f(A) ⟶ A'` is the unit of `i_!` followed by the restriction of `i_!ℱ`
  along `τ`.

## References

* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section Basis

variable (S : GlobalCrystallineSituation.{u})

/-- Elementwise form of an equality `f ≫ g = h` of morphisms of abelian groups. -/
private theorem apply_apply_eq_of_comp_eq {X Y Z : AddCommGrpCat.{u + 1}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : X ⟶ Z} (H : f ≫ g = h) (x : X) : g (f x) = h x := by
  simpa using ConcreteCategory.congr_hom H x

/-- **A morphism of abelian sheaves on `X_Zar` injective on the sections over the members of a
basis is a monomorphism.**  A section over an arbitrary open killed by the morphism restricts to
zero over every basic open inside it, so it vanishes by the sheaf axiom. -/
theorem mono_of_injective_app_of_isBasis {M N : Sheaf (opensTopology S) AddCommGrpCat.{u + 1}}
    (φ : M ⟶ N) {ℬ : Set S.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (h : ∀ W ∈ ℬ, Function.Injective (φ.hom.app (op W))) : Mono φ := by
  have hinj : ∀ V : S.X.Opens, Function.Injective (φ.hom.app (op V)) := by
    intro V
    rw [injective_iff_map_eq_zero]
    intro s hs
    have hcover : V ≤ ⨆ W : {W : S.X.Opens // W ∈ ℬ ∧ W ≤ V}, W.1 := by
      intro x hx
      obtain ⟨W, hWℬ, hxW, hWV⟩ := (Opens.isBasis_iff_nbhd.1 hℬ) hx
      exact Opens.mem_iSup.2 ⟨⟨W, hWℬ, hWV⟩, hxW⟩
    simpa using TopCat.Sheaf.eq_of_locally_eq' (F := M)
      (fun W : {W : S.X.Opens // W ∈ ℬ ∧ W ≤ V} => W.1) V (fun W => homOfLE W.2.2) hcover s 0
      (fun W => by
        rw [map_zero]
        apply h W.1 W.2.1
        rw [map_zero, apply_apply_eq_of_comp_eq (φ.hom.naturality (homOfLE W.2.2).op),
          ConcreteCategory.comp_apply, hs, map_zero])
  have : ∀ V : (S.X.Opens)ᵒᵖ, Mono (φ.hom.app V) := fun V =>
    (AddCommGrpCat.mono_iff_injective _).2 (hinj V.unop)
  have : Mono φ.hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ φ

end Basis

section Cech

variable {S S' : GlobalCrystallineSituation.{u}} {fS : S.S ⟶ S'.S} {fX : S.X ⟶ S'.X}
  {hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber}

/-- **Injectivity of `u_{X/S, *}μ` over an open, from a morphism of Čech systems.**  Let `T'` be a
pro-covering of the open `W` of `X` by objects of `Cris(X/S)`, `Φ : T ⟶ T'` a morphism of Čech
systems over `f` with level shift `k`, and `μ : ℱ ⟶ f_{cris, *}𝒢`.  Suppose that for every level
`l` there is a level `e` with `l ≤ e + k` such that every section of `ℱ` over `T'(0)_{e + k}`
killed by `μ` followed by the evaluation of `f_{cris, *}𝒢` at `Φ` restricts to zero on
`T'(0)_l`.  Then `u_{X/S, *}μ` is injective on the sections over `W`.

A section over `W` killed by `u_{X/S, *}μ` has, at each level `e + k`, an image killed by `μ`
and the evaluation, so its image at every level `l` vanishes; it vanishes because the sections
over `W` inject into `lim_e ℱ(T'(0)_e)` (`exact_openAugmentation`). -/
theorem injective_zariskiDirectImage_map_app_of_cechSystemHom {W : S'.X.Opens}
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (hT' : IsOpenProCovering S' W T')
    (Φ : CechSystemHom fS fX hf T T') {F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}}
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (μ : F ⟶ (crisDirectImage S S' fS fX hf).obj G)
    (h : ∀ l : ℕ, ∃ (e : ℕ) (hle : l ≤ e + Φ.k),
      ∀ y : F.obj.obj (op ((T'.obj (op ⦋0⦌)).obj (e + Φ.k))),
        (μ.hom.app (op ((T'.obj (op ⦋0⦌)).obj (e + Φ.k))) ≫
          crisDirectImageEval S S' fS fX hf (Φ.τ ⦋0⦌ e) G) y = 0 →
        F.obj.map ((T'.obj (op ⦋0⦌)).map (homOfLE hle)).op y = 0) :
    Function.Injective (((zariskiDirectImage S').map μ).hom.app (op W)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have he : ∀ l : ℕ, zariskiDirectImageEval S' (hT'.liesOver 0 l) F x = 0 := by
    intro l
    obtain ⟨e, hle, hy⟩ := h l
    have hc := ConcreteCategory.congr_hom (zariskiDirectImageEval_comp S'
      ((T'.obj (op ⦋0⦌)).map (homOfLE hle)) (hT'.liesOver 0 l)
      (hT'.liesOver 0 (e + Φ.k)) F) x
    simp only [ConcreteCategory.comp_apply] at hc
    rw [← hc]
    apply hy
    have hn := ConcreteCategory.congr_hom
      (zariskiDirectImageEval_naturality S' (hT'.liesOver 0 (e + Φ.k)) μ) x
    simp only [ConcreteCategory.comp_apply] at hn ⊢
    rw [← hn, hx, map_zero, map_zero]
  apply (AddCommGrpCat.mono_iff_injective _).1 (exact_openAugmentation hT' F).2
  rw [map_zero]
  refine Concrete.limit_ext _ _ _ fun e => ?_
  rw [map_zero, apply_apply_eq_of_comp_eq (openAugmentation_π hT' F e.unop), he e.unop]

/-- **The monomorphism criterion over a basis.**  If every member of a basis of opens of `X` admits
a pro-covering and a morphism of Čech systems over `f` as in
`injective_zariskiDirectImage_map_app_of_cechSystemHom`, then `u_{X/S, *}μ` is a monomorphism. -/
theorem mono_zariskiDirectImage_map_of_cechSystemHom
    {F : Sheaf (smallTopology S') AddCommGrpCat.{u + 1}}
    {G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}}
    (μ : F ⟶ (crisDirectImage S S' fS fX hf).obj G) {ℬ : Set S'.X.Opens} (hℬ : Opens.IsBasis ℬ)
    (h : ∀ W ∈ ℬ, ∃ (T : SimplicialObject (ℕ ⥤ CrystallineThickening S))
      (T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')) (_ : IsOpenProCovering S' W T')
      (Φ : CechSystemHom fS fX hf T T'), ∀ l : ℕ, ∃ (e : ℕ) (hle : l ≤ e + Φ.k),
        ∀ y : F.obj.obj (op ((T'.obj (op ⦋0⦌)).obj (e + Φ.k))),
          (μ.hom.app (op ((T'.obj (op ⦋0⦌)).obj (e + Φ.k))) ≫
            crisDirectImageEval S S' fS fX hf (Φ.τ ⦋0⦌ e) G) y = 0 →
          F.obj.map ((T'.obj (op ⦋0⦌)).map (homOfLE hle)).op y = 0) :
    Mono ((zariskiDirectImage S').map μ) :=
  mono_of_injective_app_of_isBasis S' _ hℬ fun W hW => by
    obtain ⟨T, T', hT', Φ, hΦ⟩ := h W hW
    exact injective_zariskiDirectImage_map_app_of_cechSystemHom hT' Φ μ hΦ

end Cech

section RanUnit

variable {C C' D H : Type*} [Category C] [Category C'] [Category D] [Category H]
  (L : C ⥤ D) (M : C' ⥤ C) [∀ P : C ⥤ H, L.HasRightKanExtension P]
  [∀ Q : C' ⥤ H, M.HasRightKanExtension Q]

/-- **Two right Kan extension units followed by the two counits.**  For `N : D ⥤ H`, a morphism
`uL : N ⟶ ran_L (L ⋙ N)` and a morphism `uM : L ⋙ N ⟶ ran_M (M ⋙ L ⋙ N)` satisfying the triangle
identities of the right Kan extension adjunctions against the counits, the composite

`N(d) ⟶ ran_L ran_M (M ⋙ L ⋙ N)(d) ⟶ ran_L ran_M (⋯)(L M c') ⟶ ran_M (⋯)(M c') ⟶ N(L M c')`

of `uL ≫ ran_L uM`, the restriction along `τ : d ⟶ L M c'` and the two counits is `N(τ)`. -/
theorem ran_unit_comp_counit_eq_map (N : D ⥤ H) (uL : N ⟶ L.ran.obj (L ⋙ N))
    (uM : L ⋙ N ⟶ M.ran.obj (M ⋙ L ⋙ N))
    (hL : ∀ c, uL.app (L.obj c) ≫ (L.ranCounit.app (L ⋙ N)).app c = 𝟙 _)
    (hM : ∀ c', uM.app (M.obj c') ≫ (M.ranCounit.app (M ⋙ L ⋙ N)).app c' = 𝟙 _)
    {d : D} {c' : C'} (τ : d ⟶ L.obj (M.obj c')) :
    (uL ≫ L.ran.map uM).app d ≫ (L.ran.obj (M.ran.obj (M ⋙ L ⋙ N))).map τ ≫
        (L.ranCounit.app (M.ran.obj (M ⋙ L ⋙ N))).app (M.obj c') ≫
          (M.ranCounit.app (M ⋙ L ⋙ N)).app c' = N.map τ := by
  have e1 := (L.ran.map uM).naturality τ
  have e2 := congr_app (L.ranCounit.naturality uM) (M.obj c')
  have e3 := uL.naturality τ
  simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.comp_map,
    Functor.whiskeringLeft_obj_map, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.id_map] at e2
  rw [NatTrans.comp_app, Category.assoc, ← reassoc_of% e1, reassoc_of% e2, ← reassoc_of% e3,
    reassoc_of% (hL (M.obj c')), hM c']
  exact Category.comp_id _

end RanUnit

section Algebra

open scoped TensorProduct

variable {R B : Type*} [CommRing R] [AddCommGroup B] [Module R B] {M : Type*} [AddCommGroup M]
  [Module R M]

/-- **A retraction modulo an ideal detects `J`-divisibility.**  If `r : B → R/J` is `R`-linear with
`r(b₀) = 1`, then `b₀ ⊗ m = 0` in `B ⊗_R M` forces `m ∈ J M`: applying `r ⊗ M` gives `1 ⊗ m = 0`
in `R/J ⊗_R M = M/JM`. -/
theorem mem_smul_top_of_tmul_eq_zero (J : Ideal R) (r : B →ₗ[R] R ⧸ J) {b₀ : B} (hr : r b₀ = 1)
    {m : M} (h : b₀ ⊗ₜ[R] m = 0) : m ∈ J • (⊤ : Submodule R M) := by
  have h1 : (Ideal.Quotient.mk J 1) ⊗ₜ[R] m = 0 := by
    have := congrArg (LinearMap.rTensor M r) h
    rwa [LinearMap.rTensor_tmul, hr, map_zero, ← map_one (Ideal.Quotient.mk J)] at this
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M J) h1
  rwa [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul, map_zero,
    Submodule.Quotient.mk_eq_zero] at h2

/-- An additive map, semilinear over a ring map killing the ideal `J`, kills `J M`. -/
theorem map_eq_zero_of_mem_smul_top {R' M' : Type*} [CommRing R'] [AddCommGroup M']
    [Module R' M'] (ρ : R →+* R') (ψ : M →+ M') (hψ : ∀ (a : R) (x : M), ψ (a • x) = ρ a • ψ x)
    (J : Ideal R) (hJ : ∀ a ∈ J, ρ a = 0) {m : M} (hm : m ∈ J • (⊤ : Submodule R M)) :
    ψ m = 0 := by
  refine Submodule.smul_induction_on hm (fun a ha x _ => ?_) (fun x y hx hy => ?_)
  · rw [hψ, hJ a ha, zero_smul]
  · rw [map_add, hx, hy, add_zero]

end Algebra

section UnitEval

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **The abelian unit of restriction along change of divided power base, evaluated.**  For an
abelian sheaf `N` on `CRIS(X/S')` and `τ : f(A) ⟶ A'` with `A` in `Cris(X'/S)` and `A'` in
`Cris(X/S')`, the unit `N ⟶ f_{CRIS, *}i_{X', *}i_{X'}^{-1}f_CRIS^{-1}N` at `A'` followed by the
evaluation at `τ` is the restriction of `N` along `τ`.  Both units are those of right Kan
extensions, and the evaluation is the counit; the triangle identities cancel them. -/
theorem changeBaseRestrictionUnit_app_comp_crisDirectImageEval
    (N : Sheaf (topology S') AddCommGrpCat.{u + 1}) {A : CrystallineThickening S}
    {A' : CrystallineThickening S'}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A) ⟶
      (CrystallineThickening.ι S').obj A') :
    (changeBaseRestrictionUnit S S' fS fX hf N).hom.app (op ((CrystallineThickening.ι S').obj A'))
        ≫ crisDirectImageEval S S' fS fX hf τ ((smallRestriction S).obj
          (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (topology S) (topology S')).obj N)) =
      N.obj.map τ.op := by
  set N' := ((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology S) (topology S')).obj N
  have hβ := Functor.sheafAdjunctionCocontinuous_unit_app_hom (G := CrystallineThickening.ι S)
    (A := AddCommGrpCat.{u + 1}) (J := smallTopology S) (K := topology S) N'
  have hu := Functor.sheafAdjunctionCocontinuous_unit_app_hom (G := changeBase S S' fS fX hf)
    (A := AddCommGrpCat.{u + 1}) (J := topology S) (K := topology S') N
  refine ran_unit_comp_counit_eq_map (changeBase S S' fS fX hf).op (CrystallineThickening.ι S).op
    N.obj _ _ (fun c => ?_) (fun c' => ?_) τ.op
  · rw [hu]
    exact Functor.ranCounit_app_app_ranAdjunction_unit_app_app _ _ _
  · exact (congrArg (· ≫ _) (congr_app hβ ((CrystallineThickening.ι S).op.obj c'))).trans
      (Functor.ranCounit_app_app_ranAdjunction_unit_app_app _ _ _)

/-- **The module unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` evaluated at `τ : f(A) ⟶ A'`** is the unit
`ℱ ⟶ i_{X}^{-1}i_{X, !}ℱ` of [Stacks, Tag 07IJ] at `A'` followed by the restriction of
`i_{X, !}ℱ` along `τ`; the target is `(f_cris^*ℱ)(A) = (i_{X, !}ℱ)(f(A))`. -/
theorem crisModuleUnit_app_comp_crisDirectImageEval (F : ModuleSheaf S')
    {A : CrystallineThickening S} {A' : CrystallineThickening S'}
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A) ⟶
      (CrystallineThickening.ι S').obj A') :
    (crisModuleUnit S S' fS fX hf F).hom.app (op A') ≫
        crisDirectImageEval S S' fS fX hf τ
          ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F)) =
      ((toAbelianSheaf S').map ((moduleLowerShriekAdjunction S').unit.app F)).hom.app (op A') ≫
        ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S')).obj
          ((moduleLowerShriek S').obj F)).obj.map τ.op :=
  (Category.assoc (((toAbelianSheaf S').map
    ((moduleLowerShriekAdjunction S').unit.app F)).hom.app (op A')) _ _).trans
      (congrArg _ (changeBaseRestrictionUnit_app_comp_crisDirectImageEval S S' fS fX hf
        ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S')).obj
          ((moduleLowerShriek S').obj F)) τ))

end UnitEval

section Pointwise

open scoped TensorProduct

variable {S S' : GlobalCrystallineSituation.{u}} (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (F : SheafOfModules.{u} (structureSheaf S'))

/-- **The restriction of `f_cris^*ℱ` along `τ` detects restriction to a smaller level.**  Let `ℱ`
be a locally quasi-coherent crystal on `Cris(X/S)`, `τ : f(A') ⟶ A` with `A`, `A'` affine, and
`g : B ⟶ A`.  Suppose `Γ(A', 𝒪)` has a `Γ(A, 𝒪)`-linear map `r` to `Γ(A, 𝒪)/J` sending `1` to
`1`, for an ideal `J` killed by the restriction to `B`.  Then a section of `ℱ` over `A` whose
restriction along `τ` vanishes restricts to zero on `B`.

`Γ(A', 𝒪) ⊗_{Γ(A, 𝒪)} ℱ(A) ⟶ (f_cris^*ℱ)(A')` is bijective
(`...SmallSite.bijective_crisInverseImageBaseChange`), so `1 ⊗ s = 0`; `r` turns this into
`s ∈ J ℱ(A)`, which `g` kills. -/
theorem restrict_eq_zero_of_crisInverseImageRestrict_eq_zero (hF : IsLocallyQuasiCoherent F)
    (hcrys : IsSheafCrystal F) {A B : CrystallineThickening S'} (g : B ⟶ A)
    {A' : CrystallineThickening S} [IsAffine A.obj.thickening.target.scheme]
    [IsAffine A'.obj.thickening.target.scheme]
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    (J : Ideal ((crisCommRing S').obj (op ((CrystallineThickening.ι S').obj A))))
    (hJ : ∀ a ∈ J, (crisCommRing S').map ((CrystallineThickening.ι S').map g).op a = 0)
    (r : Γ(((changeBase S S' fS fX hf).obj
      ((CrystallineThickening.ι S).obj A')).thickening.target.scheme, ⊤) →+
      (crisCommRing S').obj (op ((CrystallineThickening.ι S').obj A)) ⧸ J)
    (hr : ∀ a t, r (tauRing τ a * t) = Ideal.Quotient.mk J a * r t) (hr1 : r 1 = 1)
    (s : F.val.obj (op A)) (hs : crisInverseImageRestrict fS fX hf F τ s = 0) :
    F.val.map g.op s = 0 := by
  let r' : (ModuleCat.restrictScalars (tauRing τ).hom).obj (ModuleCat.of _
      Γ(((changeBase S S' fS fX hf).obj
        ((CrystallineThickening.ι S).obj A')).thickening.target.scheme, ⊤)) →ₗ[
        (crisCommRing S').obj (op ((CrystallineThickening.ι S').obj A))]
      (crisCommRing S').obj (op ((CrystallineThickening.ι S').obj A)) ⧸ J :=
    { toFun := fun t => r t
      map_add' := map_add r
      map_smul' := fun a t => hr a t }
  have h0 : Stacks.PullbackModel.tmul (tauRing τ).hom (1 : Γ(A'.obj.thickening.target.scheme, ⊤))
      (show sectionsOver F A from s) = 0 := by
    apply (bijective_crisInverseImageBaseChange fS fX hf F τ hF hcrys).1
    rw [map_zero, crisInverseImageBaseChange_tmul]
    exact (one_smul ((structureSheaf S).obj.obj (op A')) _).trans hs
  exact map_eq_zero_of_mem_smul_top (M := sectionsOver F A) (M' := sectionsOver F B)
    ((crisCommRing S').map ((CrystallineThickening.ι S').map g).op).hom
    (F.val.restrictₛₗ g.op).toAddMonoidHom (fun a x => (F.val.restrictₛₗ g.op).map_smulₛₗ a x) J
    hJ (mem_smul_top_of_tmul_eq_zero (M := sectionsOver F A) J r'
      (b₀ := (1 : Γ(A'.obj.thickening.target.scheme, ⊤))) (show r 1 = 1 from hr1) h0)

/-- **The module unit followed by an evaluation detects restriction to a smaller level.**  The
form of `restrict_eq_zero_of_crisInverseImageRestrict_eq_zero` that
`mono_zariskiDirectImage_map_of_cechSystemHom` consumes, for the module unit
`ℱ ⟶ f_{cris, *}f_cris^*ℱ` of the universe lift of `ℱ`, through
`crisModuleUnit_app_comp_crisDirectImageEval`. -/
theorem restrict_eq_zero_of_crisModuleUnit_eval_eq_zero (hF : IsLocallyQuasiCoherent F)
    (hcrys : IsSheafCrystal F) {A B : CrystallineThickening S'} (g : B ⟶ A)
    {A' : CrystallineThickening S} [IsAffine A.obj.thickening.target.scheme]
    [IsAffine A'.obj.thickening.target.scheme]
    (τ : (changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A') ⟶
      (CrystallineThickening.ι S').obj A)
    (J : Ideal ((crisCommRing S').obj (op ((CrystallineThickening.ι S').obj A))))
    (hJ : ∀ a ∈ J, (crisCommRing S').map ((CrystallineThickening.ι S').map g).op a = 0)
    (r : Γ(((changeBase S S' fS fX hf).obj
      ((CrystallineThickening.ι S).obj A')).thickening.target.scheme, ⊤) →+
      (crisCommRing S').obj (op ((CrystallineThickening.ι S').obj A)) ⧸ J)
    (hr : ∀ a t, r (tauRing τ a * t) = Ideal.Quotient.mk J a * r t) (hr1 : r 1 = 1)
    (y : ((toAbelianSheaf S').obj ((moduleULift S').obj F)).obj.obj (op A))
    (hy : ((crisModuleUnit S S' fS fX hf ((moduleULift S').obj F)).hom.app (op A) ≫
      crisDirectImageEval S S' fS fX hf τ
        ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj
          ((moduleULift S').obj F)))) y = 0) :
    ((toAbelianSheaf S').obj ((moduleULift S').obj F)).obj.map g.op y = 0 := by
  rw [crisModuleUnit_app_comp_crisDirectImageEval] at hy
  exact congrArg ULift.up (restrict_eq_zero_of_crisInverseImageRestrict_eq_zero fS fX hf F hF
    hcrys g τ J hJ r hr hr1 y.down hy)

end Pointwise

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
