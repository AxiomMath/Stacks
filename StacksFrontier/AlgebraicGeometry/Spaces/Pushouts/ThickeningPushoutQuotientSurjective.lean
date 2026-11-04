module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutQuotientGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutGlueModule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.RingTheory.MilnorPatching.BaseChangeAlongSurjective

/-!
# A module maps onto the glued module of two of its quotients

In the situation of Stacks 08IW, let `M` be a quasi-coherent module on `P` (the base change of
`X` to `Y'`), and let `u : a^*M ⟶ A` and `v : b^*M ⟶ B'` be epimorphisms onto quasi-coherent
modules identified over `U` by an isomorphism `θ`. A morphism `λ : M ⟶ G` into the glued module
`G = a_*A ×_{(c ≫ a)_*c^*A} b_*B'` whose two components are the adjoints of `u` and `v` is an
epimorphism: on an affine chart diagram this is Stacks 08IG and 08KJ
(`MilnorPatching.IsRelativeSquare.exists_eq_of_surjective`).

## References

* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
* [Stacks Project, Tag 08IG](https://stacks.math.columbia.edu/tag/08IG)
* [Stacks Project, Tag 08KJ](https://stacks.math.columbia.edu/tag/08KJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

/-- **An epimorphism is the projection onto the quotient by its kernel**, for any choice of the
kernel and cokernel: in an abelian category, for an epimorphism `l : X ⟶ Y` there is an
isomorphism `X / ker l ≅ Y` under which the projection is `l`. -/
theorem CategoryTheory.Abelian.exists_cokernel_kernelSubobject_iso {C : Type*} [Category* C]
    [Abelian C] {X Y : C} (l : X ⟶ Y) [Epi l] [HasKernel l]
    [HasCokernel (kernelSubobject l).arrow] :
    ∃ e : cokernel (kernelSubobject l).arrow ≅ Y,
      cokernel.π (kernelSubobject l).arrow ≫ e.hom = l := by
  have hs : IsLimit (KernelFork.ofι (kernelSubobject l).arrow (kernelSubobject_arrow_comp l)) :=
    KernelFork.IsLimit.ofι _ _ (fun k hk => kernel.lift l k hk ≫ (kernelSubobjectIso l).inv)
      (fun k hk => by rw [Category.assoc, kernelSubobject_arrow', kernel.lift_ι])
      (fun k hk m hm => by
        rw [← cancel_mono (kernelSubobject l).arrow, hm, Category.assoc,
          kernelSubobject_arrow', kernel.lift_ι])
  have hc := Abelian.epiIsCokernelOfKernel _ hs
  exact ⟨(cokernelIsCokernel (kernelSubobject l).arrow).coconePointUniqueUpToIso hc,
    (cokernelIsCokernel (kernelSubobject l).arrow).comp_coconePointUniqueUpToIso_hom hc
      WalkingParallelPair.one⟩

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The transpose of `u : g^*M ⟶ N` read on a chart diagram** is `u` applied to the chart
section. -/
theorem modulePushforwardCounitApp_homEquiv {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    (M : Modules.{u, u} B S hS X'.1 X'.2) (N : Modules.{u, u} B S hS X.1 X.2)
    (u : (modulePullback B S hS g).obj M ⟶ N) (d : ChartDiagram B S hS X.1 X'.1 g.hom)
    (s : M.val.obj (op d.V)) :
    modulePushforwardCounitApp B S hS g N d
        (((modulePullbackAdjunction B S hS g).homEquiv M N u).val.app (op d.V) s) =
      u.val.app (op d.U) (modulePullbackChartSection B S hS g M d s) :=
  (modulePullbackHomFMap_app B S hS g M N u d s).trans
    (congrArg (u.val.app (op d.U))
      (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M d s))

namespace ThickeningPushoutSpaces

variable {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}
  {P V U' U : AlgebraicSpaces B S hS} {p : P ⟶ (schemeSpaceFunctor B S hS).obj Y'}
  {pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y} {pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z'}
  {pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z} {a : V ⟶ P} {b : U' ⟶ P} {c : U ⟶ V} {d : U ⟶ U'}

variable (E : ThickeningPushoutSpaces i f g h p pV pU' pU a b c d)
include E

section Lift

variable {A : Modules.{u, u} B S hS V.1 V.2} {B' : Modules.{u, u} B S hS U'.1 U'.2}
  {θ : (modulePullback B S hS d).obj B' ⟶ (modulePullback B S hS c).obj A}
  {φ : (modulePushforward B S hS a).obj A ⟶
    (modulePushforward B S hS (c ≫ a)).obj ((modulePullback B S hS c).obj A)}
  {ψ : (modulePushforward B S hS b).obj B' ⟶
    (modulePushforward B S hS (c ≫ a)).obj ((modulePullback B S hS c).obj A)}
  {M : Modules.{u, u} B S hS P.1 P.2} (lam : M ⟶ pullback φ ψ)
  {u : (modulePullback B S hS a).obj M ⟶ A} {v : (modulePullback B S hS b).obj M ⟶ B'}
  (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom)

/-- The first component of a map into the glued module, read on the chart `W_Y`. -/
theorem glueFst_lift (hfst : lam ≫ pullback.fst φ ψ =
      (modulePullbackAdjunction B S hS a).homEquiv M A u) (l : M.val.obj (op dT.U)) :
    E.glueFst dT φ ψ (lam.val.app (op dT.U) l) =
      u.val.app (op (E.WY dT)) (modulePullbackChartSection B S hS a M (E.dWY dT) l) :=
  (congrArg (modulePushforwardCounitApp B S hS a A (E.dWY dT))
    ((comp_val_app_op lam (pullback.fst φ ψ) dT.U l).symm.trans
      (congrArg (fun k : M ⟶ _ => k.val.app (op dT.U) l) hfst))).trans
    (modulePushforwardCounitApp_homEquiv a M A u (E.dWY dT) l)

/-- The second component of a map into the glued module, read on the chart `W_{Z'}`. -/
theorem glueSnd_lift (hsnd : lam ≫ pullback.snd φ ψ =
      (modulePullbackAdjunction B S hS b).homEquiv M B' v) (l : M.val.obj (op dT.U)) :
    E.glueSnd dT φ ψ (lam.val.app (op dT.U) l) =
      v.val.app (op (E.WZ' dT)) (modulePullbackChartSection B S hS b M (E.dWZ' dT) l) :=
  (congrArg (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT))
    ((comp_val_app_op lam (pullback.snd φ ψ) dT.U l).symm.trans
      (congrArg (fun k : M ⟶ _ => k.val.app (op dT.U) l) hsnd))).trans
    (modulePushforwardCounitApp_homEquiv b M B' v (E.dWZ' dT) l)

/-- **A module maps onto the glued module of two of its quotients, on an affine chart
diagram** (Stacks 08IG and 08KJ). -/
theorem surjective_lift_app
    (hU : IsAffine ((SmallEtale.toOver B S hS P.1 ⋙ BigFppfOver.toScheme B S hS).obj dT.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS ((schemeSpaceFunctor B S hS).obj Y').1 ⋙
      BigFppfOver.toScheme B S hS).obj dT.V))
    (hM : M.IsQuasicoherentOnSite) (hA : A.IsQuasicoherentOnSite)
    (hB : B'.IsQuasicoherentOnSite) (hθ : IsIso θ) (hu : Epi u) (hv : Epi v)
    (hfst : lam ≫ pullback.fst φ ψ = (modulePullbackAdjunction B S hS a).homEquiv M A u)
    (hsnd : lam ≫ pullback.snd φ ψ = (modulePullbackAdjunction B S hS b).homEquiv M B' v)
    (hφ : ∀ x, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ y, modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    Function.Surjective (lam.val.app (op dT.U)) := by
  intro m
  have hqa := isBaseChangeAlong_modulePullbackChartSectionₛₗ B S hS a M hM (E.dWY dT)
    (E.isAffine_WY dT hU) hU
  have hqb := isBaseChangeAlong_modulePullbackChartSectionₛₗ B S hS b M hM (E.dWZ' dT)
    (E.isAffine_WZ' dT hU) hU
  have hsa := surjective_val_app_of_epi_of_isQuasicoherentOnSite u hu
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS a M hM) hA (E.WY dT)
    (E.isAffine_WY dT hU)
  have hsb := surjective_val_app_of_epi_of_isQuasicoherentOnSite v hv
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS b M hM) hB (E.WZ' dT)
    (E.isAffine_WZ' dT hU)
  obtain ⟨l, hl₁, hl₂⟩ := (E.isRelativeSquare dT hU hV).exists_eq_of_surjective
    (E.isBaseChangeAlong_glueβ dT hU (θ := θ) hB hθ)
    ((E.glueFst dT φ ψ).comp (lam.val.app (op dT.U)).hom)
    ((E.glueSnd dT φ ψ).comp (lam.val.app (op dT.U)).hom)
    (hqa.surjective_liftAlong_of_comp (u.val.app (op (E.WY dT))).hom hsa
      fun l => (E.glueFst_lift lam dT hfst l).symm)
    (hqb.surjective_liftAlong_of_comp (v.val.app (op (E.WZ' dT))).hom hsb
      fun l => (E.glueSnd_lift lam dT hsnd l).symm)
    (E.glueFst dT φ ψ m) (E.glueSnd dT φ ψ m) (E.glue_comm dT hφ hψ m)
    (fun l => E.glue_comm dT hφ hψ (lam.val.app (op dT.U) l))
  exact ⟨l, E.glue_injective dT _ _ hl₁ hl₂⟩

omit dT in
/-- **A module maps onto the glued module of two of its quotients** (the surjectivity in the
proof of Stacks 08IW). -/
theorem epi_lift (hM : M.IsQuasicoherentOnSite) (hA : A.IsQuasicoherentOnSite)
    (hB : B'.IsQuasicoherentOnSite) (hθ : IsIso θ) (hu : Epi u) (hv : Epi v)
    (hfst : lam ≫ pullback.fst φ ψ = (modulePullbackAdjunction B S hS a).homEquiv M A u)
    (hsnd : lam ≫ pullback.snd φ ψ = (modulePullbackAdjunction B S hS b).homEquiv M B' v)
    (hφ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) x,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) y,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    Epi lam :=
  epi_of_surjective_affineChartDiagram p lam fun dT hU hV =>
    E.surjective_lift_app lam dT hU hV hM hA hB hθ hu hv hfst hsnd (hφ dT) (hψ dT)

omit E in
/-- A map into the glued module from two compatible maps into its pieces. -/
theorem exists_lift_glue (x : M ⟶ (modulePushforward B S hS a).obj A)
    (y : M ⟶ (modulePushforward B S hS b).obj B') (w : x ≫ φ = y ≫ ψ) :
    ∃ lam : M ⟶ pullback φ ψ, lam ≫ pullback.fst φ ψ = x ∧ lam ≫ pullback.snd φ ψ = y :=
  ⟨pullback.lift x y w, pullback.lift_fst x y w, pullback.lift_snd x y w⟩

omit E in
/-- The first restriction of a map into the glued module is the morphism it was built from. -/
theorem modulePullback_map_comp_glueCounitFst
    (hfst : lam ≫ pullback.fst φ ψ = (modulePullbackAdjunction B S hS a).homEquiv M A u) :
    (modulePullback B S hS a).map lam ≫ glueCounitFst φ ψ = u := by
  rw [glueCounitFst, ← Adjunction.homEquiv_naturality_left_symm, hfst, Equiv.symm_apply_apply]

omit E in
/-- The second restriction of a map into the glued module is the morphism it was built from. -/
theorem modulePullback_map_comp_glueCounitSnd
    (hsnd : lam ≫ pullback.snd φ ψ = (modulePullbackAdjunction B S hS b).homEquiv M B' v) :
    (modulePullback B S hS b).map lam ≫ glueCounitSnd φ ψ = v := by
  rw [glueCounitSnd, ← Adjunction.homEquiv_naturality_left_symm, hsnd, Equiv.symm_apply_apply]

/-- **The quotient of `M` glued from two of its quotients** (the construction in the proof of
Stacks 08IW): if `λ : M ⟶ G` into the glued module is an epimorphism with components the adjoints
of `u` and `v`, the kernel `K` of `λ` has quotient `M/K ≅ G` quasi-coherent and flat over `Y'`,
whose restrictions to `V` and to `U'` are identified with `A` and with `B'` compatibly with `u`
and `v`; the quotient is the glued module. -/
theorem exists_subobject_glue [Epi lam] (hA : A.IsQuasicoherentOnSite)
    (hB : B'.IsQuasicoherentOnSite) (hθ : IsIso θ)
    (hAf : IsFlatOver B S hS V.2 pV.hom A) (hBf : IsFlatOver B S hS U'.2 pU'.hom B')
    (hfst : lam ≫ pullback.fst φ ψ = (modulePullbackAdjunction B S hS a).homEquiv M A u)
    (hsnd : lam ≫ pullback.snd φ ψ = (modulePullbackAdjunction B S hS b).homEquiv M B' v)
    (hφ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) x,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (φ.val.app (op dT.U) x) =
      modulePullbackChartSection B S hS c A (E.dWZ dT)
        (modulePushforwardCounitApp B S hS a A (E.dWY dT) x))
    (hψ : ∀ (dT : ChartDiagram B S hS P.1 ((schemeSpaceFunctor B S hS).obj Y').1 p.hom) y,
      modulePushforwardCounitApp B S hS (c ≫ a) ((modulePullback B S hS c).obj A)
        (E.dWZW dT) (ψ.val.app (op dT.U) y) =
      θ.val.app (op (E.WZ dT)) (modulePullbackChartSection B S hS d B' (E.dWZZ' dT)
        (modulePushforwardCounitApp B S hS b B' (E.dWZ' dT) y))) :
    ∃ K : Subobject M, (cokernel K.arrow).IsQuasicoherentOnSite ∧
      IsFlatOver B S hS P.2 p.hom (cokernel K.arrow) ∧
      (∃ j : (modulePullback B S hS a).obj (cokernel K.arrow) ⟶ A, IsIso j ∧
        (modulePullback B S hS a).map (cokernel.π K.arrow) ≫ j = u) ∧
      (∃ j : (modulePullback B S hS b).obj (cokernel K.arrow) ⟶ B', IsIso j ∧
        (modulePullback B S hS b).map (cokernel.π K.arrow) ≫ j = v) ∧
      Nonempty (cokernel K.arrow ≅ pullback φ ψ) := by
  have := E.isIso_glueCounitFst θ hA hB hθ hφ hψ
  have := E.isIso_glueCounitSnd θ hA hB hθ hφ hψ
  obtain ⟨eK, hπ⟩ := Abelian.exists_cokernel_kernelSubobject_iso lam
  refine ⟨kernelSubobject lam, (E.isQuasicoherentOnSite_glue φ ψ hA hB).of_iso eK.symm,
    IsFlatOver.of_iso B S hS _ eK.symm (E.isFlatOver_glue θ hA hB hθ hAf hBf hφ hψ),
    ⟨(modulePullback B S hS a).map eK.hom ≫ glueCounitFst φ ψ, inferInstance, ?_⟩,
    ⟨(modulePullback B S hS b).map eK.hom ≫ glueCounitSnd φ ψ, inferInstance, ?_⟩, ⟨eK⟩⟩
  all_goals rw [← Functor.map_comp_assoc, hπ]
  exacts [modulePullback_map_comp_glueCounitFst lam hfst,
    modulePullback_map_comp_glueCounitSnd lam hsnd]

end Lift

end ThickeningPushoutSpaces

end AlgebraicGeometry.Space

end
