module

public import StacksFrontier.Algebra.Module.Adequate.DomainValues
public import StacksFrontier.Algebra.Module.Adequate.Splitting06V7Large
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.DomainFullness

/-!
# The representability input of Tag 06V7 on a restricted domain of algebras

Let `A` be a ring and `Q` a property of commutative `A`-algebras. A linearly adequate
module-valued functor `L` defined only on the full subcategory of algebras satisfying `Q` is
represented by a finitely presented `A`-module: there is a finitely presented `M` together with
`B`-linear isomorphisms `L(B) ≃ Hom_A(M, B)`, natural in the algebra `B` of the domain. This is
the representability input that the splitting argument of [Stacks, Tag 06V7] consumes, ported
from the full domain of all commutative `A`-algebras to the restricted one.

`StacksFrontier.Algebra.Module.Adequate.SplittingRepresentabilityLarge` proves the same statement
on the full domain; that proof is left untouched, and the restricted-domain statement is not an
instance of it, because the functors the splitting argument applies it to are not restrictions
of functors on all algebras.

## Main results

* `AdequateFunctor.LaurentDomain.exists_linearRepresentation` — a linearly adequate functor on
  the restricted domain is `Hom_A(M, -)` for a finitely presented `A`-module `M`, naturally in
  the algebra of the domain.
* `AdequateFunctor.LaurentDomain.exists_linearRepresentation_smallCarrier` — the same with the
  representing module on a carrier in `Type (max u v)`, so that its symmetric algebra is an
  object of `CommAlgCat.{max u v} A`.

## Implementation notes

Everything that is pure linear algebra or holds over an arbitrary ring-valued diagram is reused
verbatim from the full-domain file rather than reproved: `evaluatedKernelIsoLarge` and
`evaluatedKernelIsoLarge_hom_comp` are stated for an arbitrary `R : C₀ᵒᵖ ⥤ RingCat` and are
instantiated here at `R := algebraRingDiagramOn Q.ι` with `C₀ := (Q.FullSubcategory)ᵒᵖ`, while
`tensorDualLarge`, `kernelTensorDualLarge` and `kernelTensorDualLarge_bijective` are statements
about a base ring, two finite free modules and an algebra in unrelated universes and are used as
they stand. The small-carrier transport reuses `homCongrLeftLarge` together with
`Module.FinitePresentation.equiv_quotient`, exactly as the full-domain version does.

One hypothesis is genuinely new. On the full domain, the presenting morphism of a linearly
adequate functor is known to be the base change of a map of finite free *modules* because
extension of scalars is fully faithful there, which is what
`AdequateFunctor.isLinearlyAdequate_iff_exists_module_map` records; no such statement is
available on a restricted domain, where a morphism of module extensions is only determined by
its value at the base ring. The port therefore takes a `AdequateFunctor.BaseAlgebraObject` for
the domain and reads the module map off with
`AdequateFunctor.moduleExtension_natTransOn_eq_map`, which is the idiom of
`AdequateFunctor.isAdequate_of_isLinearlyAdequate_on`. The value universe of a kernel
presentation is raised by construction, and that lift is undone with
`AdequateFunctor.presheafOfModulesUliftIso`, as in `AdequateFunctor.isKernelPresentation_iff`.

The evaluated-kernel comparison is wrapped once, for a *variable* morphism of module-valued
functors on the domain and a variable object, so that the kernel is never asked to unify the
general isomorphism at the concrete nested arguments of the final statement.

## References

* [Stacks Project, Tag 06V7](https://stacks.math.columbia.edu/tag/06V7)
* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AdequateFunctor.LaurentDomain

universe u v w uM

section EvaluatedKernel

variable {A : Type u} [CommRing A] {Q : ObjectProperty (CommAlgCat.{max u v} A)}

/-- `AdequateFunctor.evaluatedKernelIsoLarge` on a restricted domain of algebras: the value of
the kernel of a morphism of module-valued functors at an object of the domain is the kernel of
the evaluated morphism, as a module over the algebra carried by that object. -/
private noncomputable def evaluatedKernelIsoOn {F G : ModuleValuedFunctorOn.{uM} Q.ι}
    (q : F ⟶ G) (X : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ) :
    (PresheafOfModules.evaluation (algebraRingDiagramOn Q.ι) X).obj (kernel q) ≅
      ModuleCat.of (X.unop.unop.obj : Type (max u v)) ((q.app X).hom.ker) :=
  evaluatedKernelIsoLarge q X

/-- `evaluatedKernelIsoOn` is compatible with the two inclusions into the evaluated source. -/
private lemma evaluatedKernelIsoOn_hom_comp {F G : ModuleValuedFunctorOn.{uM} Q.ι}
    (q : F ⟶ G) (X : ((Q.FullSubcategory)ᵒᵖ)ᵒᵖ) :
    (evaluatedKernelIsoOn q X).hom ≫
      ModuleCat.ofHom (LinearMap.ker (q.app X).hom).subtype =
        (PresheafOfModules.evaluation (algebraRingDiagramOn Q.ι) X).map (kernel.ι q) :=
  evaluatedKernelIsoLarge_hom_comp q X

/-- The finite free module `finiteFreeModule A k` is free. -/
private instance free_finiteFreeModule {A : Type u} [CommRing A] (k : ℕ) :
    Module.Free A (finiteFreeModule.{w} A k) :=
  Module.Free.of_equiv (ULift.moduleEquiv.symm : (Fin k → A) ≃ₗ[A] finiteFreeModule.{w} A k)

/-- The finite free module `finiteFreeModule A k` is finite. -/
private instance finite_finiteFreeModule {A : Type u} [CommRing A] (k : ℕ) :
    Module.Finite A (finiteFreeModule.{w} A k) :=
  Module.Finite.equiv (ULift.moduleEquiv.symm : (Fin k → A) ≃ₗ[A] finiteFreeModule.{w} A k)

end EvaluatedKernel

section Representation

variable {A : Type u} [CommRing A] {Q : ObjectProperty (CommAlgCat.{max u v} A)}

/-- **Stacks Tag 06V7**, the representability input, on a restricted domain of algebras: a
linearly adequate module-valued functor on the full subcategory of algebras satisfying `Q` is
`Hom_A(M, -)` for a finitely presented `A`-module `M`, naturally in the algebra of the domain.

Unlike the full-domain statement this needs a base algebra object, which is what lets the
presenting morphism of finite free module extensions be read off as a map of modules. -/
public lemma exists_linearRepresentation (b : BaseAlgebraObject.{v} Q.ι)
    (L : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (hL : IsLinearlyAdequate.{max u v w, v} Q.ι L) :
    ∃ (M : Type (max u v w)) (_ : AddCommGroup M) (_ : Module A M),
      Module.FinitePresentation A M ∧
      ∃ e : ∀ X : Q.FullSubcategory,
          L.obj (Opposite.op (Opposite.op X)) ≃ₗ[(X.obj : Type (max u v))]
            ((M →ₗ[A] (X.obj : Type (max u v)))),
        ∀ (X Y : Q.FullSubcategory) (f : X ⟶ Y) (x : L.obj (Opposite.op (Opposite.op X))),
          e Y (L.map f.op.op x) = (Q.ι.map f).hom.toLinearMap.comp (e X x) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hL
  let g := moduleHomOfExtensionNatTransOn.{max u v w} b f
  let q := (moduleExtensionFunctorOn.{max u v w} Q.ι).map g
  let iso : L ≅ kernel q :=
    (presheafOfModulesUliftIso.{max u v, w} (algebraRingDiagramOn Q.ι) L).symm ≪≫ e ≪≫
      kernelIsoOfEq (moduleExtension_natTransOn_eq_map.{max u v w} b f)
  let V := finiteFreeModule.{max u v w} A n
  let W := finiteFreeModule.{max u v w} A m
  let K := LinearMap.range g.hom.dualMap
  let M := Module.Dual A V ⧸ K
  have hM : Module.FinitePresentation A M :=
    Module.finitePresentation_of_free_of_surjective K.mkQ K.mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      simpa only [Submodule.map_top] using
        (Module.Finite.fg_top (R := A) (M := Module.Dual A W)).map g.hom.dualMap)
  let η : L ⟶ (moduleExtensionFunctorOn.{max u v w} Q.ι).obj V := iso.hom ≫ kernel.ι q
  let eX (X : Q.FullSubcategory) :
      L.obj (Opposite.op (Opposite.op X)) ≃ₗ[(X.obj : Type (max u v))]
        LinearMap.ker (g.hom.baseChange (X.obj : Type (max u v))) :=
    CategoryTheory.Iso.toLinearEquiv
      ((PresheafOfModules.evaluation (algebraRingDiagramOn Q.ι)
        (Opposite.op (Opposite.op X))).mapIso iso ≪≫ evaluatedKernelIsoOn q _)
  have heX (X : Q.FullSubcategory) (x : L.obj (Opposite.op (Opposite.op X))) :
      (eX X x).val = (η.app (Opposite.op (Opposite.op X))).hom x :=
    congrArg (fun t => t.hom ((iso.hom.app (Opposite.op (Opposite.op X))).hom x))
      (evaluatedKernelIsoOn_hom_comp q (Opposite.op (Opposite.op X)))
  let r (X : Q.FullSubcategory) :
      L.obj (Opposite.op (Opposite.op X)) ≃ₗ[(X.obj : Type (max u v))]
        (M →ₗ[A] (X.obj : Type (max u v))) :=
    (eX X).trans (LinearEquiv.ofBijective (kernelTensorDualLarge g.hom)
      (kernelTensorDualLarge_bijective g.hom))
  refine ⟨M, inferInstance, inferInstance, hM, r, fun X Y φ x => LinearMap.ext fun z => ?_⟩
  obtain ⟨l, rfl⟩ := K.mkQ_surjective z
  show tensorDualLarge A V (Y.obj : Type (max u v))
      (eX Y (L.map φ.op.op x)).val l =
    (Q.ι.map φ).hom (tensorDualLarge A V (X.obj : Type (max u v)) (eX X x).val l)
  rw [heX Y (L.map φ.op.op x), heX X x,
    PresheafOfModules.naturality_apply η φ.op.op x]
  exact tensorDualLarge_naturality (Q.ι.map φ).hom _ l

/-- `AdequateFunctor.LaurentDomain.exists_linearRepresentation` with the representing module
placed on a carrier in `Type (max u v)`, so that its symmetric algebra is an object of
`CommAlgCat.{max u v} A`.

The module produced by the representability statement lies in `Type (max u v w)`, which is the
universe its construction as a quotient of a dual of `finiteFreeModule.{max u v w} A n`
dictates; being finitely presented it is also realised on a carrier in `Type (max u v)`, and the
comparison `L(B) ≃ₗ[B] Hom_A(M, B)` crosses that universe gap without loss. -/
public lemma exists_linearRepresentation_smallCarrier (b : BaseAlgebraObject.{v} Q.ι)
    (L : ModuleValuedFunctorOn.{max u v w} Q.ι)
    (hL : IsLinearlyAdequate.{max u v w, v} Q.ι L) :
    ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module A M),
      Module.FinitePresentation A M ∧
      ∃ e : ∀ X : Q.FullSubcategory,
          L.obj (Opposite.op (Opposite.op X)) ≃ₗ[(X.obj : Type (max u v))]
            ((M →ₗ[A] (X.obj : Type (max u v)))),
        ∀ (X Y : Q.FullSubcategory) (f : X ⟶ Y) (x : L.obj (Opposite.op (Opposite.op X))),
          e Y (L.map f.op.op x) = (Q.ι.map f).hom.toLinearMap.comp (e X x) := by
  obtain ⟨M, hMadd, hMmod, hMfp, e, he⟩ := exists_linearRepresentation.{u, v, w} b L hL
  let := hMadd
  let := hMmod
  let := hMfp
  have : Small.{max u v} A := small_lift.{u, max u v} A
  obtain ⟨N, hNadd, hNmod, K, eqv, -, -, -⟩ :
      ∃ (N : Type (max u v)) (_ : AddCommGroup N) (_ : Module A N) (K : Submodule A N)
        (_ : M ≃ₗ[A] N ⧸ K), Module.Free A N ∧ Module.Finite A N ∧ K.FG :=
    Module.FinitePresentation.equiv_quotient A M
  let := hNadd
  let := hNmod
  refine ⟨N ⧸ K, inferInstance, inferInstance, Module.FinitePresentation.of_equiv eqv,
    fun X => (e X).trans (homCongrLeftLarge eqv.symm (X.obj : Type (max u v))), ?_⟩
  intro X Y φ x
  show (e Y (L.map φ.op.op x)).comp eqv.symm.toLinearMap =
    (Q.ι.map φ).hom.toLinearMap.comp ((e X x).comp eqv.symm.toLinearMap)
  rw [he X Y φ x, LinearMap.comp_assoc]

end Representation

end AdequateFunctor.LaurentDomain

end
