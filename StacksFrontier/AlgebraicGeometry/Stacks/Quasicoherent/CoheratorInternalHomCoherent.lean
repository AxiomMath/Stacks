module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfKernelPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomPushforward

/-!
# Stacks 0GRD: `hom(ℱ, 𝒢)` is coherent on a locally Noetherian algebraic stack

Let `𝒳` be a locally Noetherian algebraic stack and `ℱ`, `𝒢` coherent `𝒪_𝒳`-modules. Stacks 0GRD
says that the internal hom `hom(ℱ, 𝒢) = Q(𝓗om_{𝒪_𝒳}(ℱ, 𝒢))` of Stacks 0GQN
(`AlgebraicGeometry.Stack.FlatFppf.coheratorInternalHom`) is coherent.

The source restricts to a smooth atlas and uses Stacks 0GQT and the case of algebraic spaces. The
proof here works on the flat-fppf site instead, in the way `Q(Ker φ)` is shown to be coherent in
`StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfKernelPresentation`:

* over an object `z` over an affine scheme, a section of `𝓗om(ℱ, 𝒢)` is an `𝒪(z)`-linear map
  `ℱ(z) ⟶ 𝒢(z)` (`AlgebraicGeometry.Stack.FlatFppf.sheafHomEvalLinear_bijective`), by the
  presentation of `ℱ|_z` by its sections;
* these sections base change along flat morphisms of affine objects when `ℱ(z)` is finitely
  presented (`AlgebraicGeometry.Stack.FlatFppf.bijective_fibredSectionsBaseChange_sheafHom`, the
  flat base change of `Hom_A(M, N)`), and they are finitely presented over a Noetherian ring;
* so over a flat object lying over a Noetherian affine scheme the restriction of `𝓗om(ℱ, 𝒢)` to
  the flat-fppf site is finitely presented, hence so is `Q(𝓗om(ℱ, 𝒢)) = g_!g^{-1}𝓗om(ℱ, 𝒢)` over
  the objects mapping to it, and those objects cover.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isCoherent_coheratorInternalHom`: the internal hom of two
  coherent modules on a locally Noetherian algebraic stack is coherent.

## References

* [Stacks Project, Tag 0GRD](https://stacks.math.columbia.edu/tag/0GRD)
* [Stacks Project, Tag 0GQN](https://stacks.math.columbia.edu/tag/0GQN)
* [Stacks Project, Tag 0GQT](https://stacks.math.columbia.edu/tag/0GQT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Module

/-- Flat base change of a module of homomorphisms, as a comparison of restriction maps. Let `A ⟶ B`
be flat, `M` finitely presented, and let `KZ ≃ Hom_A(M, N)` and `KW ≃ Hom_B(M_W, N_W)` be
compatible with restriction maps `M ⟶ M_W`, `N ⟶ N_W`, `KZ ⟶ KW` whose base changes along `A ⟶ B`
are bijective for `M` and `N`. Then the base change of `KZ ⟶ KW` is bijective. -/
theorem bijective_liftBaseChange_of_homEquiv {A B M N KZ Mw Nw KW : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Flat A B]
    [AddCommGroup M] [Module A M] [Module.FinitePresentation A M] [AddCommGroup N] [Module A N]
    [AddCommGroup KZ] [Module A KZ]
    [AddCommGroup Mw] [Module A Mw] [Module B Mw] [IsScalarTower A B Mw]
    [AddCommGroup Nw] [Module A Nw] [Module B Nw] [IsScalarTower A B Nw]
    [AddCommGroup KW] [Module A KW] [Module B KW] [IsScalarTower A B KW]
    (rM : M →ₗ[A] Mw) (rN : N →ₗ[A] Nw) (rK : KZ →ₗ[A] KW)
    (hM : Function.Bijective (rM.liftBaseChange B)) (hN : Function.Bijective (rN.liftBaseChange B))
    (Ez : KZ ≃ₗ[A] (M →ₗ[A] N)) (Ew : KW ≃ₗ[B] (Mw →ₗ[B] Nw))
    (hc : ∀ k m, Ew (rK k) (rM m) = rN (Ez k m)) :
    Function.Bijective (rK.liftBaseChange B) := by
  let cF := LinearEquiv.ofBijective _ hM
  let cG := LinearEquiv.ofBijective _ hN
  let e1 := (Module.FinitePresentation.isBaseChange_map A M N B).equiv
  let Φ := ((Ez.baseChange A B).trans e1).trans (cF.arrowCongr cG)
  have hk : ∀ k, Ew (rK k) = (cF.arrowCongr cG) ((Ez k : M →ₗ[A] N).baseChange B) := fun k ↦ by
    have h : (Ew (rK k)) ∘ₗ cF.toLinearMap =
        ((cF.arrowCongr cG) ((Ez k : M →ₗ[A] N).baseChange B)) ∘ₗ cF.toLinearMap := by
      refine TensorProduct.AlgebraTensorModule.ext fun b m ↦ ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
      show Ew (rK k) (rM.liftBaseChange B (b ⊗ₜ m)) = rN.liftBaseChange B (b ⊗ₜ Ez k m)
      rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul, hc]
    refine LinearMap.ext fun m' ↦ ?_
    obtain ⟨t, rfl⟩ := cF.surjective m'
    exact LinearMap.congr_fun h t
  have key : Ew.toLinearMap ∘ₗ rK.liftBaseChange B = Φ.toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun b k ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, LinearEquiv.coe_coe, map_smul, hk]
    show _ = (cF.arrowCongr cG) (e1 (b ⊗ₜ Ez k))
    rw [IsBaseChange.equiv_tmul, map_smul]
    rfl
  have hb : Function.Bijective (Ew.toLinearMap ∘ₗ rK.liftBaseChange B) := by
    rw [key]; exact Φ.bijective
  exact (Function.Bijective.of_comp_iff' Ew.bijective _).1 hb

/-- Over a Noetherian ring, the module of homomorphisms between finite modules is finite. -/
theorem finite_linearMap_of_isNoetherianRing {A M N : Type*} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] : Module.Finite A (M →ₗ[A] N) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let e : (M →ₗ[A] N) →ₗ[A] (Fin n → N) := LinearMap.pi fun i ↦ LinearMap.applyₗ (s i)
  have : IsNoetherian A (Fin n → N) := isNoetherian_of_isNoetherianRing_of_finite A _
  exact Module.Finite.of_injective e fun φ ψ h ↦
    LinearMap.ext_on_range hs fun i ↦ congrFun h i

end Module

namespace AlgebraicGeometry.RingedSite

/-- The restriction of a section of the internal Hom along `f : V ⟶ U`, evaluated at the terminal
object of the slice at `V`, on a restricted section. -/
theorem internalHomSheaf_map_app_terminal.{m, u₀, v₀, w₀} (X : RingedSite.{u₀, v₀, w₀})
    (A B : SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V : X.C}
    (f : V ⟶ U) (α : (X.internalHomSheaf A B).val.obj (op U)) (m : A.val.obj (op U)) :
    (((X.internalHomSheaf A B).val.map f.op).hom α :
      (restrFun X.O.obj V).obj A.val ⟶ (restrFun X.O.obj V).obj B.val).app
        (op (Over.mk (𝟙 V))) (A.val.map f.op m) =
      B.val.map f.op ((α : (restrFun X.O.obj U).obj A.val ⟶ (restrFun X.O.obj U).obj B.val).app
        (op (Over.mk (𝟙 U))) m) :=
  PresheafOfModules.internalHom_map_app_terminal X.O.obj A.val B.val f α m

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- The ringed fppf site of an algebraic stack is essentially small. -/
instance (priority := low) : EssentiallySmall.{u} (fppfRingedSite B S hS 𝒳).C :=
  essentiallySmall_obj_algebraicStack B S hS 𝒳

/-- An object of `𝒳`, read as an object of its ringed fppf site. -/
abbrev siteObj (z : 𝒳.val.val.obj) : (fppfRingedSite B S hS 𝒳).C := z

/-- The sections of the small internal Hom over `z`, read as morphisms of the restrictions to the
slice at `z`. -/
def sheafHomEquiv (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (z : 𝒳.val.val.obj) :
    (sheafHom B S hS 𝒳 F G).val.obj (op z) ≃+
      ((restrFun (fppfRingedSite B S hS 𝒳).O.obj (siteObj z)).obj F.val ⟶
        (restrFun (fppfRingedSite B S hS 𝒳).O.obj (siteObj z)).obj G.val) :=
  haveI := RingedSite.small_internalHomSheaf_obj (fppfRingedSite B S hS 𝒳) F G (op (siteObj z))
  Shrink.addEquiv.{u}
    (α := ((fppfRingedSite B S hS 𝒳).internalHomSheaf F G).val.obj (op (siteObj z)))

/-- The value at the terminal object of the slice of the morphism named by a section. -/
def sheafHomEval (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (z : 𝒳.val.val.obj) (k : (sheafHom B S hS 𝒳 F G).val.obj (op z)) (m : F.val.obj (op z)) :
    G.val.obj (op z) :=
  ((sheafHomEquiv F G z k).app (op (Over.mk (𝟙 (siteObj z))))) m

/-- Restricting a section of the structure sheaf to the terminal object of the slice at `z`
returns the same section. -/
theorem fRestr_id (z : (fppfRingedSite B S hS 𝒳).C)
    (r : (Oforget (fppfRingedSite B S hS 𝒳).O.obj).obj (op z)) :
    fRestr (fppfRingedSite B S hS 𝒳).O.obj z r (op (Over.mk (𝟙 z))) = r := by
  show ((Oforget (fppfRingedSite B S hS 𝒳).O.obj).map (𝟙 z).op).hom r = r
  rw [op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Evaluation of sections of `𝓗om(ℱ, 𝒢)` is linear in the section with respect to `𝒪(z)`. -/
theorem sheafHomEval_smul (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (z : 𝒳.val.val.obj) (r : fibredSectionRing B S hS 𝒳.val.val.p z)
    (k : (sheafHom B S hS 𝒳 F G).val.obj (op z)) (m : F.val.obj (op z)) :
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids (sheafHom B S hS 𝒳 F G) z
    sheafHomEval F G z (r • k) m = r • sheafHomEval F G z k m := by
  have := RingedSite.small_internalHomSheaf_obj (fppfRingedSite B S hS 𝒳) F G (op (siteObj z))
  have h := (Shrink.linearEquiv.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (fppfRingedSite B S hS 𝒳).O).obj.obj (op (siteObj z)))
    (((fppfRingedSite B S hS 𝒳).internalHomSheaf F G).val.obj (op (siteObj z)))).map_smul r k
  have h2 := congrArg (fun α : ((restrFun (fppfRingedSite B S hS 𝒳).O.obj (siteObj z)).obj F.val ⟶
      (restrFun (fppfRingedSite B S hS 𝒳).O.obj (siteObj z)).obj G.val) ↦
    (α.app (op (Over.mk (𝟙 (siteObj z))))) m) h
  refine h2.trans ?_
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
  show (show fibredSectionRing B S hS 𝒳.val.val.p z from
    fRestr (fppfRingedSite B S hS 𝒳).O.obj (siteObj z) r (op (Over.mk (𝟙 (siteObj z))))) •
    sheafHomEval F G z k m = _
  congr 1
  exact fRestr_id _ r

/-- Over an object over an affine scheme, a section of `𝓗om(ℱ, 𝒢)` is determined by its values on
the sections of `ℱ`, for `ℱ` cartesian between affine objects. -/
theorem sheafHomEval_injective
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F) {z : 𝒳.val.val.obj}
    (hz : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z))
    {k l : (sheafHom B S hS 𝒳 F G).val.obj (op z)}
    (h : ∀ m, sheafHomEval F G z k m = sheafHomEval F G z l m) : k = l := by
  apply (sheafHomEquiv F G z).injective
  have hkl : (⟨sheafHomEquiv F G z k⟩ : F.over z ⟶ G.over z) = ⟨sheafHomEquiv F G z l⟩ :=
    Stacks.SheafOfModules.FreeSheafification.hom_ext_of_terminal (Over.mk (𝟙 z))
      (Over.isTerminalMkId z) (F.over z) (fun i ↦ i)
      (hgen_over_of_isCartesianBetweenAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F hF hz)
      h
  exact congrArg _root_.SheafOfModules.Hom.val hkl

/-- Over an object over an affine scheme, every linear map `ℱ(z) ⟶ 𝒢(z)` is the family of values
of a section of `𝓗om(ℱ, 𝒢)`, for `ℱ` cartesian between affine objects. -/
theorem exists_sheafHomEval_eq
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F) {z : 𝒳.val.val.obj}
    (hz : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (ψ : letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
      letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
      F.val.obj (op z) →ₗ[fibredSectionRing B S hS 𝒳.val.val.p z] G.val.obj (op z)) :
    ∃ k : (sheafHom B S hS 𝒳 F G).val.obj (op z), ∀ m, sheafHomEval F G z k m = ψ m := by
  classical
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
  obtain ⟨α, hα⟩ := Stacks.SheafOfModules.FreeSheafification.exists_hom_of_terminal
    (Over.mk (𝟙 z)) (Over.isTerminalMkId z) (F.over z) (F.val.obj (op z))
    (Module.BaseChange.Relations (fibredSectionRing B S hS 𝒳.val.val.p z) (F.val.obj (op z)))
    (fun i ↦ i) (fun k ↦ k.1) (fun k ↦ k.2)
    (hgen_over_of_isCartesianBetweenAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F hF hz)
    (hrel_over_of_isCartesianBetweenAffines B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F hF hz)
    (G.over z) (fun i ↦ ψ i) (fun k ↦ by
      show (k.1.sum fun i r ↦ r • ψ i) = 0
      calc (k.1.sum fun i r ↦ r • ψ i) = ψ (k.1.sum fun i r ↦ r • i) := by
            rw [map_finsuppSum]; exact Finset.sum_congr rfl fun i _ ↦ (ψ.map_smul _ _).symm
        _ = 0 := by rw [k.2, map_zero])
  obtain ⟨k, hk⟩ := (sheafHomEquiv F G z).surjective α.val
  exact ⟨k, fun m ↦ (congrArg (fun β : (restrFun (fppfRingedSite B S hS 𝒳).O.obj
    (siteObj z)).obj F.val ⟶ (restrFun (fppfRingedSite B S hS 𝒳).O.obj (siteObj z)).obj G.val ↦
      β.app (op (Over.mk (𝟙 (siteObj z)))) m) hk).trans (hα m)⟩

/-- Evaluation commutes with restriction along a morphism `g : w ⟶ z`. -/
theorem sheafHomEval_map (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    {z w : 𝒳.val.val.obj} (g : w ⟶ z) (k : (sheafHom B S hS 𝒳 F G).val.obj (op z))
    (m : F.val.obj (op z)) :
    sheafHomEval F G w ((sheafHom B S hS 𝒳 F G).val.map g.op k) (F.val.map g.op m) =
      G.val.map g.op (sheafHomEval F G z k m) := by
  have h1 : sheafHomEquiv F G w ((sheafHom B S hS 𝒳 F G).val.map g.op k) =
      ((fppfRingedSite B S hS 𝒳).internalHomSheaf F G).val.map
        (show siteObj w ⟶ siteObj z from g).op (sheafHomEquiv F G z k) :=
    @Stacks.shrinkPresheaf_map_apply.{u, u + 1, u + 1, u} _ _
      ((fppfRingedSite B S hS 𝒳).internalHomSheaf F G).val.presheaf
      (RingedSite.small_internalHomSheaf_obj (fppfRingedSite B S hS 𝒳) F G) _ _
      (show siteObj w ⟶ siteObj z from g).op k
  have h3 := RingedSite.internalHomSheaf_map_app_terminal (fppfRingedSite B S hS 𝒳) F G
    (show siteObj w ⟶ siteObj z from g) (sheafHomEquiv F G z k) m
  rw [← h1] at h3
  exact h3

/-- Evaluation of sections of `𝓗om(ℱ, 𝒢)` is additive in the section. -/
theorem sheafHomEval_add_left
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) (z : 𝒳.val.val.obj)
    (k l : (sheafHom B S hS 𝒳 F G).val.obj (op z)) (m : F.val.obj (op z)) :
    sheafHomEval F G z (k + l) m = sheafHomEval F G z k m + sheafHomEval F G z l m := by
  unfold sheafHomEval
  rw [map_add]
  rfl

/-- Evaluation of a section of `𝓗om(ℱ, 𝒢)` is additive in the argument. -/
theorem sheafHomEval_add_right
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) (z : 𝒳.val.val.obj)
    (k : (sheafHom B S hS 𝒳 F G).val.obj (op z)) (m m' : F.val.obj (op z)) :
    sheafHomEval F G z k (m + m') = sheafHomEval F G z k m + sheafHomEval F G z k m' :=
  map_add _ _ _

/-- Evaluation of a section of `𝓗om(ℱ, 𝒢)` is `𝒪(z)`-linear in the argument. -/
theorem sheafHomEval_smul_right
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) (z : 𝒳.val.val.obj)
    (k : (sheafHom B S hS 𝒳 F G).val.obj (op z)) (r : fibredSectionRing B S hS 𝒳.val.val.p z)
    (m : F.val.obj (op z)) :
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
    sheafHomEval F G z k (r • m) = r • sheafHomEval F G z k m :=
  ((sheafHomEquiv F G z k).app (op (Over.mk (𝟙 (siteObj z))))).hom.map_smul r m

/-- Evaluation at the terminal object of the slice, as an `𝒪(z)`-linear map from the sections of
`𝓗om(ℱ, 𝒢)` over `z` to `Hom_{𝒪(z)}(ℱ(z), 𝒢(z))`. -/
def sheafHomEvalLinear (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (z : 𝒳.val.val.obj) :
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
    letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids (sheafHom B S hS 𝒳 F G) z
    (sheafHom B S hS 𝒳 F G).val.obj (op z) →ₗ[fibredSectionRing B S hS 𝒳.val.val.p z]
      (F.val.obj (op z) →ₗ[fibredSectionRing B S hS 𝒳.val.val.p z] G.val.obj (op z)) :=
  letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
  letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
  letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids (sheafHom B S hS 𝒳 F G) z
  { toFun := fun k ↦
      { toFun := sheafHomEval F G z k
        map_add' := sheafHomEval_add_right F G z k
        map_smul' := sheafHomEval_smul_right F G z k }
    map_add' := fun k l ↦ LinearMap.ext (sheafHomEval_add_left F G z k l)
    map_smul' := fun r k ↦ LinearMap.ext (sheafHomEval_smul F G z r k) }

/-- `sheafHomEvalLinear` applied to a section is `sheafHomEval` of that section. -/
theorem sheafHomEvalLinear_apply
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (z : 𝒳.val.val.obj) (k : (sheafHom B S hS 𝒳 F G).val.obj (op z)) (m : F.val.obj (op z)) :
    sheafHomEvalLinear F G z k m = sheafHomEval F G z k m := rfl

/-- Over an object over an affine scheme, for `ℱ` cartesian between affine objects, the sections
of `𝓗om(ℱ, 𝒢)` over `z` are identified with `Hom_{𝒪(z)}(ℱ(z), 𝒢(z))` by evaluation. -/
theorem sheafHomEvalLinear_bijective
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F) {z : 𝒳.val.val.obj}
    (hz : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z)) :
    Function.Bijective (sheafHomEvalLinear F G z) :=
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
  ⟨fun _ _ h ↦ sheafHomEval_injective F G hF hz fun m ↦ congrArg (fun φ ↦ φ m) h,
    fun ψ ↦ by
      obtain ⟨k, hk⟩ := exists_sheafHomEval_eq F G hF hz ψ
      exact ⟨k, LinearMap.ext hk⟩⟩

/-- The sections of `𝓗om(ℱ, 𝒢)` base change along flat morphisms of affine objects, for `ℱ`, `𝒢`
cartesian between affine objects and `ℱ(z)` finitely presented. -/
theorem bijective_fibredSectionsBaseChange_sheafHom
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F)
    (hG : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids G)
    {z w : 𝒳.val.val.obj} (g : w ⟶ z)
    (hz : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (hw : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj w))
    (hflat : letI := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) g
      Module.Flat (fibredSectionRing B S hS 𝒳.val.val.p z) (fibredSectionRing B S hS 𝒳.val.val.p w))
    (hfp : letI := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
      Module.FinitePresentation (fibredSectionRing B S hS 𝒳.val.val.p z) (F.val.obj (op z))) :
    Function.Bijective
      (fibredSectionsBaseChange 𝒳.val.isFiberedInGroupoids (sheafHom B S hS 𝒳 F G) g) := by
  classical
  let hp := 𝒳.val.isFiberedInGroupoids
  let K := sheafHom B S hS 𝒳 F G
  let A := fibredSectionRing B S hS 𝒳.val.val.p z
  let Bw := fibredSectionRing B S hS 𝒳.val.val.p w
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) g
  let := fibredSectionsModule hp F z
  let := fibredSectionsModule hp G z
  let := fibredSectionsModule hp K z
  let := fibredSectionsModule hp F w
  let := fibredSectionsModule hp G w
  let := fibredSectionsModule hp K w
  let := fibredSectionsModuleOver hp F g
  let := fibredSectionsModuleOver hp G g
  let := fibredSectionsModuleOver hp K g
  have : IsScalarTower A Bw (F.val.obj (op w)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A Bw (G.val.obj (op w)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower A Bw (K.val.obj (op w)) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat A Bw := hflat
  have : Module.FinitePresentation A (F.val.obj (op z)) := hfp
  exact Module.bijective_liftBaseChange_of_homEquiv (fibredSectionsRestrict hp F g)
    (fibredSectionsRestrict hp G g) (fibredSectionsRestrict hp K g) (hF g hz hw) (hG g hz hw)
    (LinearEquiv.ofBijective _ (sheafHomEvalLinear_bijective F G hF hz))
    (LinearEquiv.ofBijective _ (sheafHomEvalLinear_bijective F G hF hw))
    (fun k m ↦ sheafHomEval_map F G g k m)

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

/-- A module whose sections over affine objects base change along flat morphisms and are finitely
presented over Noetherian rings has finitely presented restrictions to the flat-fppf sites of flat
objects lying over Noetherian affine schemes. -/
theorem isFinitelyPresentedByGlobalSections_restrictedModuleRestrictionAlong_of_baseChange
    (K : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hbcK : ∀ {z w : 𝒳.val.val.obj} (g : w ⟶ z),
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z) →
      IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj w) →
      IsNoetherianRing (fibredSectionRing B S hS 𝒳.val.val.p z) →
      @Module.Flat (fibredSectionRing B S hS 𝒳.val.val.p z)
          (fibredSectionRing B S hS 𝒳.val.val.p w) _ _
          (fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) g).toModule →
      Function.Bijective (fibredSectionsBaseChange 𝒳.val.isFiberedInGroupoids K g))
    (hfpK : ∀ z : 𝒳.val.val.obj, IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z) →
      IsNoetherianRing (fibredSectionRing B S hS 𝒳.val.val.p z) →
      @Module.FinitePresentation (fibredSectionRing B S hS 𝒳.val.val.p z) (K.val.obj (op z)) _ _
        (fibredSectionsModule 𝒳.val.isFiberedInGroupoids K z))
    (y : FlatFppf B S hS 𝒳)
    (hyaff : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj))
    (hnoeth : IsNoetherianRing (fibredSectionRing B S hS 𝒳.val.val.p y.obj)) :
    ((restrictedModuleRestrictionAlong B S hS (ambientSliceMorphism B S hS y)
      (isFlat_ambientSliceMorphism B S hS y)).obj
        ((moduleInverseImageU B S hS 𝒳).obj K)).IsFinitelyPresentedByGlobalSections := by
  classical
  let p := 𝒳.val.val.p
  let hp := 𝒳.val.isFiberedInGroupoids
  let f := ambientSliceMorphism B S hS y
  let hf := isFlat_ambientSliceMorphism B S hS y
  let 𝒵 := schemeStack.{u, w} B S hS (p.obj y.obj)
  have : (primedSiteFunctor B S hS f hf).IsContinuous (topology B S hS 𝒵)
      (topology B S hS 𝒳) := siteFunctor_isContinuous B S hS f hf
  let Fn : FlatFppf B S hS 𝒵 ⥤ 𝒳.val.val.obj :=
    primedSiteFunctor B S hS f hf ⋙ (objectProperty B S hS 𝒳).ι
  have : Fn.IsContinuous (topology B S hS 𝒵) (associatedTopology B S hS p B.topology) :=
    Functor.isContinuous_comp _ _ _ (topology B S hS 𝒳) _
  let t : FlatFppf B S hS 𝒵 := ⟨Over.mk (𝟙 _), flatObject_schemeStack_id.{u, w} B S hS _⟩
  let ht : IsTerminal t := ObjectProperty.isTerminalFullSubcategory _ (Over.isTerminalMkId _) _
  have hpobj : ∀ V : FlatFppf B S hS 𝒵, p.obj (Fn.obj V) = V.obj.left := fun V ↦
    Functor.congr_obj f.hom.hom.w V.obj
  have hpmap : ∀ {V W : FlatFppf B S hS 𝒵} (h : V ⟶ W),
      p.map (Fn.map h) = eqToHom (hpobj V) ≫ h.hom.left ≫ eqToHom (hpobj W).symm :=
    fun h ↦ Functor.congr_hom f.hom.hom.w h.hom
  have haffV : ∀ V : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj V.obj)) →
      IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (Fn.obj V)) := fun V hV ↦ by
    show IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj V)))
    rw [hpobj V]; exact hV
  have hy₀aff : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (Fn.obj t)) := by
    show IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj t)))
    rw [hpobj t]; exact hyaff
  have hflat : ∀ V : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj V.obj)) →
      let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from V))
      Module.Flat (fibredSectionRing B S hS p (Fn.obj t))
        (fibredSectionRing B S hS p (Fn.obj V)) := by
    intro V hV
    have hm : Flat ((BigFppfOver.toScheme B S hS).map (p.map (Fn.map (ht.from V)))) :=
      flat_toScheme_map_of_eq B S hS (hpobj V) (hpobj t) _ _ (hpmap _)
        (flat_of_flatObject_schemeStack.{u, w} B S hS _ V.obj V.property)
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj V))) := haffV V hV
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj t))) := hy₀aff
    exact Scheme.Hom.flat_appTop _
  let A := fibredSectionRing B S hS p (Fn.obj t)
  have : IsNoetherianRing A := by
    show IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj (p.obj (Fn.obj t)), ⊤)
    rw [hpobj t]; exact hnoeth
  let := fibredSectionsModule hp K (Fn.obj t)
  have : Module.FinitePresentation A (K.val.obj (op (Fn.obj t))) := hfpK _ hy₀aff inferInstance
  obtain ⟨n, s₀, hs₀⟩ := Module.Finite.exists_fin (R := A) (M := K.val.obj (op (Fn.obj t)))
  let s : ULift.{u} (Fin n) → K.val.obj (op (Fn.obj t)) := fun i ↦ s₀ i.down
  have hs : Submodule.span A (Set.range s) = ⊤ := by
    rw [show Set.range s = Set.range s₀ from ULift.down_surjective.range_comp s₀]; exact hs₀
  have hsurj : Function.Surjective (Finsupp.linearCombination A s) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]; exact hs
  obtain ⟨k, ρ₀, hρ₀⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (Module.FinitePresentation.fg_ker _ hsurj)
  let ρ : ULift.{u} (Fin k) → ULift.{u} (Fin n) →₀ A := fun i ↦ ρ₀ i.down
  have hρspan : Submodule.span A (Set.range ρ) = LinearMap.ker (Finsupp.linearCombination A s) := by
    rw [show Set.range ρ = Set.range ρ₀ from ULift.down_surjective.range_comp ρ₀]; exact hρ₀
  have hρ : ∀ i, ((ρ i).sum fun j r ↦ r • s j) = 0 := fun i ↦ by
    have hmem : ρ i ∈ LinearMap.ker (Finsupp.linearCombination A s) :=
      hρspan ▸ Submodule.subset_span ⟨i, rfl⟩
    simpa [Finsupp.linearCombination_apply] using hmem
  have hbc : ∀ W : FlatFppf B S hS 𝒵,
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒵.val.val.p.obj W.obj)) →
      Function.Bijective (fibredSectionsBaseChange hp K (Fn.map (ht.from W))) := fun W hW ↦
    hbcK (Fn.map (ht.from W)) hy₀aff (haffV W hW) inferInstance (hflat W hW)
  have := hasSheafify_addCommGrpCat B S hS 𝒵
  have := wEqualsLocallyBijective_addCommGrpCat B S hS 𝒵
  let h : (Fn.sheafPushforwardContinuous RingCat.{u} (topology B S hS 𝒵)
      (associatedTopology B S hS p B.topology)).obj (ambientRingStructureSheaf B S hS 𝒳) =
      subsiteRingStructureSheaf B S hS 𝒵 := inverseImageRing_primedSiteFunctor B S hS f hf
  have main :=
    (Stacks.SheafOfModules.FreeSheafification.isPresentedByGlobalSections_pushforward_of_terminal
    Fn h K t ht (ULift.{u} (Fin n)) (ULift.{u} (Fin k)) s ρ hρ ?_ ?_).2 inferInstance inferInstance
  · refine Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_iso ?_ main
    exact ((_root_.SheafOfModules.pushforwardComp (F := primedSiteFunctor B S hS f hf)
      (G := (objectProperty B S hS 𝒳).ι)
      (eqToHom (inverseImageRing_primedSiteFunctor B S hS f hf).symm)
      (𝟙 (((objectProperty B S hS 𝒳).ι.sheafPushforwardContinuous RingCat.{u}
        (topology B S hS 𝒳) (associatedTopology B S hS p B.topology)).obj
          (ambientRingStructureSheaf B S hS 𝒳)))).app K ≪≫
      (_root_.SheafOfModules.pushforwardCongr
        (by rw [CategoryTheory.Functor.map_id]; exact Category.comp_id _)).app K).symm
  · intro V x
    obtain ⟨T, hT, haff⟩ := FlatFppf.isCoveringFamily_isAffine B S hS 𝒵 V
    refine ⟨T, hT, fun W g hg ↦ ?_⟩
    let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from W))
    let := fibredSectionsModule hp K (Fn.obj W)
    let := fibredSectionsModuleOver hp K (Fn.map (ht.from W))
    have : IsScalarTower A (fibredSectionRing B S hS p (Fn.obj W)) (K.val.obj (op (Fn.obj W))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.BaseChange.exists_finsupp_of_surjective_liftBaseChange_of_span
      (fibredSectionsRestrict hp K (Fn.map (ht.from W))) s hs (hbc W (haff hg)).2
      (K.val.map (Fn.map g).op x)
  · intro V c hc
    obtain ⟨T, hT, haff⟩ := FlatFppf.isCoveringFamily_isAffine B S hS 𝒵 V
    refine ⟨T, hT, fun W g hg ↦ ?_⟩
    let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := p) (Fn.map (ht.from W))
    let := fibredSectionsModule hp K (Fn.obj W)
    let := fibredSectionsModuleOver hp K (Fn.map (ht.from W))
    have : IsScalarTower A (fibredSectionRing B S hS p (Fn.obj W)) (K.val.obj (op (Fn.obj W))) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let c' : ULift.{u} (Fin n) →₀ fibredSectionRing B S hS p (Fn.obj W) :=
      c.mapRange (fibredSectionRestrict (Fn.map g)) (map_zero _)
    have hc' :
        (c'.sum fun i r ↦ r • fibredSectionsRestrict hp K (Fn.map (ht.from W)) (s i)) = 0 := by
      have h0 :=
        (Stacks.SheafOfModules.FreeSheafification.map_finsupp_sum_smul K.val (Fn.map g).op c
        (fun i ↦ (show K.val.obj (op (Fn.obj V)) from
          K.val.map (Fn.map (ht.from V)).op (s i)))).symm.trans
        ((congrArg (fun m ↦ K.val.map (Fn.map g).op m) hc).trans (map_zero _))
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
      refine congrArg (c' i • ·) ?_
      refine (K.val.congr_map_apply (congrArg (fun m ↦ (Fn.map m).op)
        (ht.hom_ext (ht.from W) (g ≫ ht.from V))) (s i)).trans ?_
      rw [Functor.map_comp, op_comp]
      exact K.val.map_comp_apply _ _ (s i)
    exact Module.BaseChange.exists_finsupp_relations_of_bijective_liftBaseChange_of_span
      (fibredSectionsRestrict hp K (Fn.map (ht.from W))) s hs ρ hρspan (hbc W (haff hg)) c' hc'


/-- Over an affine object with Noetherian ring of functions, the sections of `𝓗om(ℱ, 𝒢)` form a
finitely presented module, for `ℱ`, `𝒢` quasi-coherent of finite type. -/
theorem finitePresentation_sheafHom_sections
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F) (hFt : F.IsFiniteTypeOnSite)
    (hG : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids G) (hGt : G.IsFiniteTypeOnSite)
    (z : 𝒳.val.val.obj) (hz : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj z))
    (hn : IsNoetherianRing (fibredSectionRing B S hS 𝒳.val.val.p z)) :
    @Module.FinitePresentation (fibredSectionRing B S hS 𝒳.val.val.p z)
      ((sheafHom B S hS 𝒳 F G).val.obj (op z)) _ _
      (fibredSectionsModule 𝒳.val.isFiberedInGroupoids (sheafHom B S hS 𝒳 F G) z) := by
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids G z
  let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids (sheafHom B S hS 𝒳 F G) z
  have := moduleFinite_sections_of_isFiniteTypeOnSite_fibred 𝒳.val.isFiberedInGroupoids F hF hFt hz
  have := moduleFinite_sections_of_isFiniteTypeOnSite_fibred 𝒳.val.isFiberedInGroupoids G hG hGt hz
  have := Module.finite_linearMap_of_isNoetherianRing (A := fibredSectionRing B S hS 𝒳.val.val.p z)
    (M := F.val.obj (op z)) (N := G.val.obj (op z))
  have : Module.FinitePresentation (fibredSectionRing B S hS 𝒳.val.val.p z)
      (F.val.obj (op z) →ₗ[fibredSectionRing B S hS 𝒳.val.val.p z] G.val.obj (op z)) :=
    Module.finitePresentation_of_finite _ _
  exact Module.FinitePresentation.of_equiv
    (LinearEquiv.ofBijective _ (sheafHomEvalLinear_bijective F G hF hz)).symm

/-- Let `𝒳` be a locally Noetherian algebraic stack and `ℱ`, `𝒢` coherent `𝒪_𝒳`-modules. Then the
internal hom `hom(ℱ, 𝒢) = Q(𝓗om_{𝒪_𝒳}(ℱ, 𝒢))` is a coherent `𝒪_𝒳`-module. -/
@[stacks 0GRD]
theorem isCoherent_coheratorInternalHom
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)}
    (hF : IsCoherent B S hS 𝒳 F) (hG : IsCoherent B S hS 𝒳 G) :
    IsCoherent B S hS 𝒳 (coheratorInternalHom B S hS 𝒳 F G) := by
  have hFc := isCartesianBetweenAffines_of_isQuasicoherentOnSite _ F hF.1.1
  have hGc := isCartesianBetweenAffines_of_isQuasicoherentOnSite _ G hG.1.1
  refine (isCoherent_iff_isCoherentModule B S hS 𝒳 h𝒳 _).2 ⟨fun U ↦ ?_⟩
  refine ⟨Σ w : 𝒳.val.val.obj, {g : w ⟶ U // noetherianFlatSieve 𝒳 U g}, fun i ↦ i.1,
    fun i ↦ i.2.1, ?_, fun i ↦ ?_⟩
  · refine GrothendieckTopology.superset_covering _ ?_ (noetherianFlatSieve_mem 𝒳 h𝒳 U)
    intro Y h hh
    exact ⟨Y, 𝟙 Y, h, Presieve.ofArrows.mk (⟨Y, h, hh⟩ :
      Σ w : 𝒳.val.val.obj, {g : w ⟶ U // noetherianFlatSieve 𝒳 U g}), Category.id_comp h⟩
  · obtain ⟨w, g, y, hyaff, hnoeth, ⟨c⟩⟩ := i
    exact Stacks.SheafOfModules.FinitePresentationTransport.hasFiniteGlobalPresentation_overMap _ c
      (Stacks.SheafOfModules.hasFiniteGlobalPresentation_of_isFinitelyPresentedByGlobalSections
        (isFinitelyPresentedByGlobalSections_over_moduleLowerShriekU B S hS y _
          (isFinitelyPresentedByGlobalSections_restrictedModuleRestrictionAlong_of_baseChange
            (sheafHom B S hS 𝒳 F G)
            (fun {z _} g hz hw hn hflat ↦
              let := fibredSectionsModule 𝒳.val.isFiberedInGroupoids F z
              have := moduleFinite_sections_of_isFiniteTypeOnSite_fibred
                𝒳.val.isFiberedInGroupoids F hFc hF.1.2 hz
              bijective_fibredSectionsBaseChange_sheafHom F G hFc hGc g hz hw hflat
                (Module.finitePresentation_of_finite _ _))
            (fun z hz hn ↦ finitePresentation_sheafHom_sections F G hFc hF.1.2 hGc hG.1.2 z hz hn)
            y hyaff hnoeth)))

end AlgebraicGeometry.Stack.FlatFppf

end
