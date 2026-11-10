module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.LinearAlgebra.Contraction
public import StacksFrontier.Algebra.Module.Adequate.Defs

/-!
# The representability equivalence of Tag 06V7 at independent universes

A linearly adequate module-valued functor `L` on the commutative `A`-algebras is represented
by a finitely presented `A`-module: there is a finitely presented `M` together with
`B`-linear isomorphisms `L(B) ≃ Hom_A(M, B)`, natural in the `A`-algebra `B`. This is the
input that the splitting argument of Stacks 06V7 uses to produce the tautological element,
and it is proved here with the algebra carriers and the module values in universes
independent of the base ring: the algebras are objects of `CommAlgCat.{max u v} A` and the
values lie in `Type (max u v w)`, which is the universe discipline of
`AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A`.

`StacksFrontier.Algebra.Module.Adequate.Splitting` proves the same statement at the single
universe `u`; that proof is left untouched, and nothing here depends on it.

## Main results

* `AdequateFunctor.exists_linearRepresentation_large`: a linearly adequate functor is
  `Hom_A(M, -)` for a finitely presented `A`-module `M`, naturally in the algebra.
* `AdequateFunctor.tensorDual_bijective_large`: for `V` finite free over `A`, the canonical
  map `B ⊗[A] V → Hom_A(V^*, B)` is bijective.
* `AdequateFunctor.kernelTensorDual_bijective_large`: the kernel of a base-changed map of
  finite free modules is `Hom_A(-, B)` of the cokernel of the dual map.

## Implementation notes

The three inputs are kept as separate named pieces, each proved once at the generality it
actually has, so that no definitional unfolding is ever demanded at the concrete nested
arguments of the final statement.

`evaluatedKernelIsoLarge` is stated for an arbitrary presheaf of modules over an arbitrary
ring-valued diagram: evaluating a kernel of presheaves of modules is the kernel of the
evaluated map. The only inputs are that `PresheafOfModules.evaluation` preserves finite
limits and that `ModuleCat` kernels are the linear-map kernels, both of which hold with the
value universe unrelated to the universe of the scalars.

`tensorDualLarge` and `kernelTensorDualLarge` are pure linear algebra, with the base ring,
the two finite free modules and the algebra all in unrelated universes: `B ⊗[A] V` lives in
`max uB uV` rather than in either alone, and the dual `Module.Dual A V` lives in
`max u uV`, so these carriers are given independent universes rather than being assumed to
agree.

`exists_linearRepresentation_large` then combines them. The module it produces is
`Module.Dual A V ⧸ LinearMap.range f.dualMap` for `f` the presenting map of finite free
modules; `StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift` builds the
same module in the equivalent shape `(Fin n → A) ⧸ LinearMap.range (transposeLinearMap A d)`
together with its symmetric algebra and the universal property of that algebra, but it never
builds the inverse direction, which is what makes the displayed equivalence a representability
statement rather than a one-sided universal property.

## References

* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AdequateFunctor

universe u v w uB uC uV uW uR uM uC₀ vC₀

section EvaluatedKernel

variable {C₀ : Type uC₀} [Category.{vC₀} C₀] {R : C₀ᵒᵖ ⥤ RingCat.{uR}}

/-- Evaluating the kernel of a morphism of presheaves of modules at an object gives the
kernel of the evaluated morphism. The value universe `uM` is unrelated to the universe
`uR` of the scalars. -/
public noncomputable def evaluatedKernelIsoLarge {F G : PresheafOfModules.{uM} R}
    (q : F ⟶ G) (X : C₀ᵒᵖ) :
    (PresheafOfModules.evaluation R X).obj (kernel q) ≅
      ModuleCat.of (R.obj X) ((q.app X).hom.ker) :=
  (isLimitMapConeForkEquiv' (PresheafOfModules.evaluation R X) (kernel.condition q)
    (isLimitOfPreserves _ (kernelIsKernel q))).conePointUniqueUpToIso
      (ModuleCat.kernelIsLimit _)

/-- The isomorphism of `evaluatedKernelIsoLarge` is compatible with the two inclusions into
the evaluated source. -/
public lemma evaluatedKernelIsoLarge_hom_comp {F G : PresheafOfModules.{uM} R}
    (q : F ⟶ G) (X : C₀ᵒᵖ) :
    (evaluatedKernelIsoLarge q X).hom ≫
      ModuleCat.ofHom (LinearMap.ker (q.app X).hom).subtype =
        (PresheafOfModules.evaluation R X).map (kernel.ι q) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitMapConeForkEquiv' (PresheafOfModules.evaluation R X) (kernel.condition q)
      (isLimitOfPreserves _ (kernelIsKernel q))) (ModuleCat.kernelIsLimit _) .zero

end EvaluatedKernel

section TensorDual

/-- The canonical `B`-linear map `B ⊗[A] V → Hom_A(V^*, B)`. The base ring, the module and
the algebra live in unrelated universes. -/
public noncomputable def tensorDualLarge (A : Type u) (V : Type uV) (B : Type uB) [CommRing A]
    [AddCommGroup V] [Module A V] [CommRing B] [Algebra A B] :
    B ⊗[A] V →ₗ[B] (Module.Dual A V →ₗ[A] B) :=
  LinearMap.liftBaseChange B
    ((LinearMap.compRight A (Algebra.linearMap A B)).comp (Module.Dual.eval A V))

/-- The value of `tensorDualLarge` on a pure tensor. -/
public lemma tensorDualLarge_tmul (A : Type u) (V : Type uV) (B : Type uB) [CommRing A]
    [AddCommGroup V] [Module A V] [CommRing B] [Algebra A B]
    (b : B) (v : V) (l : Module.Dual A V) :
    tensorDualLarge A V B (b ⊗ₜ[A] v) l = b * algebraMap A B (l v) := rfl

/-- For `V` finite free over `A`, the canonical map `B ⊗[A] V → Hom_A(V^*, B)` is bijective. -/
public lemma tensorDualLarge_bijective (A : Type u) (V : Type uV) (B : Type uB) [CommRing A]
    [AddCommGroup V] [Module A V] [Module.Finite A V] [Module.Free A V]
    [CommRing B] [Algebra A B] : Function.Bijective (tensorDualLarge A V B) := by
  let e := ((TensorProduct.congr (LinearEquiv.refl A B) (Module.evalEquiv A V)).trans
    (TensorProduct.comm A B (Module.Dual A (Module.Dual A V)))).trans
      (dualTensorHomEquiv A (Module.Dual A V) B)
  have he : (tensorDualLarge A V B).restrictScalars A = e.toLinearMap := by
    apply LinearMap.ext
    intro t
    apply LinearMap.ext
    intro l
    induction t using TensorProduct.inductionOn with
    | tmul b v =>
      simp only [LinearMap.restrictScalars_apply, tensorDualLarge_tmul, e,
        LinearEquiv.trans_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, TensorProduct.comm_tmul, dualTensorHomEquiv,
        LinearEquiv.ofBijective_apply, dualTensorHom_apply,
        Module.evalEquiv_apply, Module.Dual.eval_apply, Algebra.smul_def]
      exact mul_comm _ _
    | add t t' ht ht' => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht ht'
  change Function.Bijective ((tensorDualLarge A V B).restrictScalars A)
  rw [he]
  exact e.bijective

/-- `tensorDualLarge` turns base change of a linear map into precomposition on duals. -/
public lemma tensorDualLarge_baseChange {A : Type u} {V : Type uV} {W : Type uW} {B : Type uB}
    [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [CommRing B] [Algebra A B] (f : V →ₗ[A] W) (t : B ⊗[A] V)
    (l : Module.Dual A W) :
    tensorDualLarge A W B (f.baseChange B t) l = tensorDualLarge A V B t (l.comp f) := by
  induction t using TensorProduct.inductionOn with
  | tmul b v => simp only [LinearMap.baseChange_tmul, tensorDualLarge_tmul, LinearMap.comp_apply]
  | add t t' ht ht' => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht ht'

/-- `tensorDualLarge` is natural in the algebra. -/
public lemma tensorDualLarge_naturality {A : Type u} {V : Type uV} {B : Type uB} {C : Type uC}
    [CommRing A] [AddCommGroup V] [Module A V] [CommRing B] [Algebra A B]
    [CommRing C] [Algebra A C] (f : B →ₐ[A] C) (t : B ⊗[A] V)
    (l : Module.Dual A V) :
    tensorDualLarge A V C (TensorProduct.map f.toLinearMap LinearMap.id t) l =
      f (tensorDualLarge A V B t l) := by
  induction t using TensorProduct.inductionOn with
  | tmul b v => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
      AlgHom.toLinearMap_apply, tensorDualLarge_tmul, map_mul, AlgHom.commutes]
  | add t t' ht ht' => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht ht'

/-- The map `tensorDualLarge` descends from the kernel of a base-changed linear map to the
`A`-linear maps out of the cokernel of the dual map. -/
public noncomputable def kernelTensorDualLarge {A : Type u} {V : Type uV} {W : Type uW}
    {B : Type uB} [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [CommRing B] [Algebra A B] (f : V →ₗ[A] W) :
    LinearMap.ker (f.baseChange B) →ₗ[B]
      ((Module.Dual A V ⧸ LinearMap.range f.dualMap) →ₗ[A] B) where
  toFun t := (LinearMap.range f.dualMap).liftQ (tensorDualLarge A V B t.val) (by
    rintro _ ⟨l, rfl⟩
    change tensorDualLarge A V B t.val (l.comp f) = 0
    rw [← tensorDualLarge_baseChange, t.property, map_zero, LinearMap.zero_apply])
  map_add' x y := by
    ext l
    simp [Submodule.liftQ_apply]
  map_smul' b x := by
    ext l
    simp [Submodule.liftQ_apply]

/-- `kernelTensorDualLarge` computes on a representative of the quotient. -/
public lemma kernelTensorDualLarge_mkQ {A : Type u} {V : Type uV} {W : Type uW} {B : Type uB}
    [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [CommRing B] [Algebra A B] (f : V →ₗ[A] W)
    (t : LinearMap.ker (f.baseChange B)) (l : Module.Dual A V) :
    kernelTensorDualLarge f t ((LinearMap.range f.dualMap).mkQ l) =
      tensorDualLarge A V B t.val l := rfl

/-- For `V` and `W` finite free, `kernelTensorDualLarge` is bijective: the kernel of the
base-changed map is represented by the cokernel of the dual map. -/
public lemma kernelTensorDualLarge_bijective {A : Type u} {V : Type uV} {W : Type uW}
    {B : Type uB} [CommRing A] [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    [Module.Finite A V] [Module.Free A V] [Module.Finite A W] [Module.Free A W]
    [CommRing B] [Algebra A B] (f : V →ₗ[A] W) :
    Function.Bijective (kernelTensorDualLarge (B := B) f) := by
  refine ⟨fun x y h => Subtype.ext <| (tensorDualLarge_bijective A V B).injective <|
    LinearMap.ext fun l => congrArg (· ((LinearMap.range f.dualMap).mkQ l)) h, fun h => ?_⟩
  obtain ⟨t, ht⟩ := (tensorDualLarge_bijective A V B).surjective
    (h.comp (LinearMap.range f.dualMap).mkQ)
  have hf : f.baseChange B t = 0 :=
    (tensorDualLarge_bijective A W B).injective <| LinearMap.ext fun l => by
      rw [tensorDualLarge_baseChange, ht, map_zero, LinearMap.zero_apply]
      exact (congrArg h ((Submodule.Quotient.mk_eq_zero _).mpr ⟨l, rfl⟩)).trans (map_zero h)
  exact ⟨⟨t, hf⟩, Submodule.linearMap_qext _ ht⟩

end TensorDual

section Representation

/-- The value of a module-valued functor at an `A`-algebra. -/
public abbrev algebraValueLarge {A : Type u} [CommRing A]
    (F : ModuleValuedFunctor.{uM, v} A) (B : Type (max u v)) [CommRing B] [Algebra A B] :=
  F.obj (Opposite.op (Opposite.op (CommAlgCat.of A B)))

/-- The transition map of a module-valued functor along a map of `A`-algebras. -/
public noncomputable abbrev algebraMapValueLarge {A : Type u} {B C : Type (max u v)}
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (F : ModuleValuedFunctor.{uM, v} A) (f : B →ₐ[A] C) :
    algebraValueLarge F B →ₛₗ[f.toRingHom] algebraValueLarge F C :=
  F.restrictₛₗ ((CommAlgCat.ofHom f).op.op)

/-- A morphism of module-valued functors commutes with the transition maps. -/
public lemma algebraMapValueLarge_naturality {A : Type u} {B C : Type (max u v)} [CommRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    {F G : ModuleValuedFunctor.{uM, v} A} (η : F ⟶ G) (f : B →ₐ[A] C)
    (x : algebraValueLarge F B) :
    (η.app (Opposite.op (Opposite.op (CommAlgCat.of A C)))).hom
        (algebraMapValueLarge F f x) =
      algebraMapValueLarge G f ((η.app (Opposite.op (Opposite.op (CommAlgCat.of A B)))).hom x) :=
  PresheafOfModules.naturality_apply η (CommAlgCat.ofHom f).op.op x

/-- `evaluatedKernelIsoLarge` for module-valued functors on the commutative `A`-algebras: the
value of the kernel at an algebra `B` is the kernel of the evaluated map, as a `B`-module. -/
public noncomputable def evaluatedKernelIso06V7_large {A : Type u} [CommRing A]
    {F G : ModuleValuedFunctor.{uM, v} A} (q : F ⟶ G)
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) :
    (PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X).obj (kernel q) ≅
      ModuleCat.of (X.unop.unop : Type (max u v)) ((q.app X).hom.ker) :=
  evaluatedKernelIsoLarge q X

/-- `evaluatedKernelIso06V7_large` is compatible with the two inclusions into the evaluated
source. -/
public lemma evaluatedKernelIso06V7_hom_comp_large {A : Type u} [CommRing A]
    {F G : ModuleValuedFunctor.{uM, v} A} (q : F ⟶ G)
    (X : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ) :
    (evaluatedKernelIso06V7_large q X).hom ≫
      ModuleCat.ofHom (LinearMap.ker (q.app X).hom).subtype =
        (PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X).map (kernel.ι q) :=
  evaluatedKernelIsoLarge_hom_comp q X

/-- **Stacks Tag 06V7**, the representability input: a linearly adequate module-valued functor
is `Hom_A(M, -)` for a finitely presented `A`-module `M`, naturally in the algebra.
Independent-universe form: the algebras are objects of `CommAlgCat.{max u v} A` and the values
lie in `Type (max u v w)`. -/
public lemma exists_linearRepresentation_large {A : Type u} [CommRing A]
    (L : ModuleValuedFunctor.{max u v w, v} A) (hL : IsLinearlyAdequate (𝟭 _) L) :
    ∃ (M : Type (max u v w)) (_ : AddCommGroup M) (_ : Module A M),
      Module.FinitePresentation A M ∧
      ∃ e : ∀ B : CommAlgCat.{max u v} A,
          algebraValueLarge L B ≃ₗ[B] (M →ₗ[A] B),
        ∀ (B C : CommAlgCat.{max u v} A) (f : B ⟶ C) (x : algebraValueLarge L B),
          e C (algebraMapValueLarge L f.hom x) = f.hom.toLinearMap.comp (e B x) := by
  obtain ⟨n, m, f, hf⟩ := (isLinearlyAdequate_iff_exists_module_map L).mp hL
  obtain ⟨e⟩ := (isKernelPresentation_iff L f).mp hf
  let V := finiteFreeModule.{max u v w} A n
  let W := finiteFreeModule.{max u v w} A m
  have hfree (k : ℕ) : Module.Free A (finiteFreeModule.{max u v w} A k) ∧
      Module.Finite A (finiteFreeModule.{max u v w} A k) :=
    ⟨Module.Free.of_equiv ULift.moduleEquiv.symm, Module.Finite.equiv ULift.moduleEquiv.symm⟩
  obtain ⟨_, _⟩ := hfree n
  obtain ⟨_, _⟩ := hfree m
  let Q := LinearMap.range f.hom.dualMap
  let M := Module.Dual A V ⧸ Q
  have hM : Module.FinitePresentation A M :=
    Module.finitePresentation_of_free_of_surjective Q.mkQ Q.mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := A) (M := Module.Dual A W)).map f.hom.dualMap)
  let q := (moduleExtensionFunctor.{max u v w, v} A).map f
  let η : L ⟶ moduleExtension.{max u v w, v} A V := e.hom ≫ kernel.ι q
  let eB (B : CommAlgCat.{max u v} A) :
      algebraValueLarge L B ≃ₗ[B] LinearMap.ker (f.hom.baseChange (B : Type (max u v))) :=
    CategoryTheory.Iso.toLinearEquiv
      ((PresheafOfModules.evaluation (algebraRingDiagram.{v} A)
        (Opposite.op (Opposite.op B))).mapIso e ≪≫ evaluatedKernelIso06V7_large q _)
  have heB (B : CommAlgCat.{max u v} A) (x : algebraValueLarge L B) :
      (eB B x).val = (η.app (Opposite.op (Opposite.op B))).hom x :=
    congrArg (fun g => g.hom ((e.hom.app (Opposite.op (Opposite.op B))).hom x))
      (evaluatedKernelIso06V7_hom_comp_large q (Opposite.op (Opposite.op B)))
  let r (B : CommAlgCat.{max u v} A) : algebraValueLarge L B ≃ₗ[B] (M →ₗ[A] B) :=
    (eB B).trans (LinearEquiv.ofBijective (kernelTensorDualLarge f.hom)
      (kernelTensorDualLarge_bijective f.hom))
  refine ⟨M, inferInstance, inferInstance, hM, r, fun B C g x => LinearMap.ext fun z => ?_⟩
  obtain ⟨l, rfl⟩ := Q.mkQ_surjective z
  change tensorDualLarge A V (C : Type (max u v))
      (eB C (algebraMapValueLarge L g.hom x)).val l =
    g.hom (tensorDualLarge A V (B : Type (max u v)) (eB B x).val l)
  rw [heB, heB, algebraMapValueLarge_naturality η g.hom x]
  exact tensorDualLarge_naturality g.hom _ l

end Representation

end AdequateFunctor
