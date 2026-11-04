module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Algebra.Module.Adequate.Tangent

/-!
# Tag 06ZA, corrected: the tangent functor of an injective functor is surjective at the end

**Stacks erratum.**  [Stacks, Tag 06ZA] asserts that for an
injective object `I` of the category of module-valued functors on `Alg_A`, every `A`-algebra
`B` and every short exact sequence `0 → N₁ → N → N₂ → 0` of `B`-modules, the sequence of
tangent modules `TI(B, N₁) → TI(B, N) → TI(B, N₂) → 0` is exact.  **That is false as the
source states it.**  Exactness at the middle term `TI(B, N)` fails.

The counterexample is formalized in
`StacksFrontier/Examples/Algebra/InjectiveTangentNotRightExact.lean`.  Take a field `k`, the
algebra `C = k[ε]/(ε²)` and the injective `C`-module `J = Hom_k(C, k)`, and let
`I(D) = ∏_{α : D →ₐ C} J` with `D` acting on the `α`-component through `α`.  Then `I` is
right adjoint to evaluation at `C`, hence injective, and for finite-dimensional `V` the
tangent module `TI(k, V)` is the set of functions `V^* → J` vanishing at `0`.  Apply this to
`0 → k → k² → k → 0`, the inclusion of the first coordinate followed by the projection to the
second: the two tangent maps are `g ↦ ((a, b) ↦ g a)` and `h ↦ (b ↦ h (0, b))`.  For
`0 ≠ j ∈ J` the function with `h (1, 0) = j` and `h = 0` elsewhere lies in the kernel of the
second map but not in the image of the first, since every element of that image takes equal
values at `(1, 0)` and `(1, 1)`.  So the tangent sequence is not exact in the middle.

What survives is exactness at `TI(B, N₂)`, that is, surjectivity of `TI(B, N) → TI(B, N₂)`,
and that is what this file proves.  The argument is the one part of the source's proof that
is unaffected, and it never forms the coequalizer that the counterexample denies: for
`R : Cᵒᵖ ⥤ RingCat` the free presheaf of modules on the Yoneda presheaf of an object
corepresents evaluation there, a monomorphism of the base category is carried by `yoneda` to
a morphism injective at every object, the free functor carries that to a monomorphism because
it is `Finsupp.mapDomain` at every object, and injectivity of `I` turns the restriction map
into a surjection.  Applied to the surjection of square-zero extensions `B[N] → B[N₂]` this
lifts any `t ∈ TI(B, N₂)` to some `s ∈ I(B[N])`, and `s` lies in `TI(B, N)` automatically
because the augmentation `B[N] → B` factors through `B[N₂]`.

The companion refutation of the *proof step* of Tag 06ZA — that the free module-valued
functor preserves the square-zero equalizer — is
`StacksFrontier/Algebra/Module/Adequate/TangentEqualizerCounterexample.lean`.

## Main results

* `AdequateFunctor.surjective_map_op_of_injective`: an injective presheaf of modules is
  surjective on restriction along a monomorphism of the base category.
* `AdequateFunctor.surjective_moduleValueMap_of_injective`: an injective module-valued
  functor is surjective on a surjection of algebras.
* `AdequateFunctor.surjective_tangentFunctorAt_map_of_injective`: the tangent functor of an
  injective module-valued functor is surjective on a surjection of modules.
* `AdequateFunctor.epi_tangentFunctorAt_map_of_injective`: **Tag 06ZA, corrected** —
  surjectivity of `TI(B, N) → TI(B, N₂)`.

## Implementation notes

The surjectivity statement is proved with the module universe of `I` equal to the universe of
the algebras, which is the universe in which the free presheaf of modules on a presheaf of
types lives.  The source has no universes; this is the one-universe reading of it.

## References

* [Stacks Project, Tag 06ZA](https://stacks.math.columbia.edu/tag/06ZA)
* [Stacks Project, Tag 06ZF](https://stacks.math.columbia.edu/tag/06ZF)
-/

@[expose] public section

namespace AdequateFunctor

open CategoryTheory

universe u v

section FreeYoneda

universe u₁ v₁

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{v₁}}

/-- The free presheaf of modules on a morphism of presheaves of types which is injective at
every object is a monomorphism: at every object the induced map is `Finsupp.mapDomain` along
an injection. -/
private lemma mono_free_map {F G : Cᵒᵖ ⥤ Type v₁} (φ : F ⟶ G)
    (hφ : ∀ X, Function.Injective (φ.app X)) :
    Mono ((PresheafOfModules.free (R := R)).map φ) :=
  PresheafOfModules.mono_of_injective fun {X} _ _ hab => Finsupp.mapDomain_injective (hφ X) hab

/-- **An injective presheaf of modules is surjective on restriction along a monomorphism.**
If `I` is an injective object of `PresheafOfModules R` and `w : Y ⟶ X` is a monomorphism of
the base category, then `I(X) → I(Y)` is surjective.

The free presheaf of modules on the Yoneda presheaf of `X` corepresents evaluation at `X`
(`PresheafOfModules.freeYonedaEquiv`), and `w` monic makes `yoneda.map w` injective at every
object, hence `(free R).map (yoneda.map w)` a monomorphism.  An element of `I(Y)` is a
morphism out of the free Yoneda object at `Y`; injectivity of `I` extends it along that
monomorphism, and the extension, evaluated at the generator `𝟙 X`, is the required preimage.

This is the step of the proof of [Stacks, Tag 06ZA] that survives the failure recorded in
`AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective`. -/
lemma surjective_map_op_of_injective (I : PresheafOfModules.{v₁} R) [Injective I]
    {X Y : C} (w : Y ⟶ X) [Mono w] :
    Function.Surjective (I.map w.op) := by
  intro z
  have hmono : Mono ((PresheafOfModules.free (R := R)).map (yoneda.map w)) :=
    mono_free_map _ fun _ _ _ hab => (cancel_mono w).mp hab
  set g : (PresheafOfModules.free (R := R)).obj (yoneda.obj Y) ⟶ I :=
    PresheafOfModules.freeYonedaEquiv.symm z with hg
  set h := Injective.factorThru g ((PresheafOfModules.free (R := R)).map (yoneda.map w))
  have mid : ((PresheafOfModules.free (R := R)).obj (yoneda.obj X)).map w.op
        (ModuleCat.freeMk (𝟙 X)) =
      ((PresheafOfModules.free (R := R)).map (yoneda.map w)).app (Opposite.op Y)
        (ModuleCat.freeMk (𝟙 Y)) := by
    refine (ModuleCat.freeDesc_apply _ (𝟙 X)).trans ?_
    refine Eq.trans ?_
      (ModuleCat.free_map_apply ((yoneda.map w).app (Opposite.op Y)) (𝟙 Y)).symm
    exact congrArg
      (fun a : Y ⟶ X =>
        (ModuleCat.freeMk a :
          ((PresheafOfModules.free (R := R)).obj (yoneda.obj X)).obj (Opposite.op Y)))
      (by simp : w ≫ 𝟙 X = 𝟙 Y ≫ w)
  refine ⟨h.app (Opposite.op X) (ModuleCat.freeMk (𝟙 X)), ?_⟩
  rw [← PresheafOfModules.naturality_apply h w.op (ModuleCat.freeMk (𝟙 X)), mid,
    show h.app (Opposite.op Y)
        (((PresheafOfModules.free (R := R)).map (yoneda.map w)).app (Opposite.op Y)
          (ModuleCat.freeMk (𝟙 Y))) = g.app (Opposite.op Y) (ModuleCat.freeMk (𝟙 Y)) from
      congrArg (fun k : _ ⟶ I => k.app (Opposite.op Y) (ModuleCat.freeMk (𝟙 Y)))
        (Injective.comp_factorThru g _), hg]
  exact PresheafOfModules.freeYonedaEquiv_symm_app I Y z

end FreeYoneda

section RightExactHalf

variable (A : Type u) [CommRing A]

/-- A surjective homomorphism of `A`-algebras is an epimorphism of `CommAlgCat A`. -/
private lemma epi_ofHom_of_surjective {B C : Type v} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (u : B →ₐ[A] C) (hu : Function.Surjective u) :
    Epi (CommAlgCat.ofHom u) := by
  constructor
  intro Z g₁ g₂ hg
  refine CommAlgCat.hom_ext (AlgHom.ext fun c => ?_)
  obtain ⟨b, rfl⟩ := hu c
  exact congrArg (fun k : CommAlgCat.of A B ⟶ Z => k.hom b) hg

/-- **An injective module-valued functor is surjective on a surjection of algebras.**
If `I` is an injective object of the category of module-valued functors on `Alg_A` and
`u : B → C` is a surjective homomorphism of `A`-algebras, then `I(B) → I(C)` is surjective.
A surjective algebra map is an epimorphism, so it is a monomorphism of the index category of
module-valued functors, and `AdequateFunctor.surjective_map_op_of_injective` applies. -/
lemma surjective_moduleValueMap_of_injective
    (I : PresheafOfModules.{v} (algebraStructurePresheaf.{v} A)) [Injective I]
    {B C : Type v} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (u : B →ₐ[A] C) (hu : Function.Surjective u) :
    Function.Surjective (moduleValueMap A I u) := by
  have : Epi (CommAlgCat.ofHom u) := epi_ofHom_of_surjective A u hu
  exact surjective_map_op_of_injective I (CommAlgCat.ofHom u).op

/-- **The tangent functor of an injective module-valued functor is surjective on surjections
of modules.**  For `I` injective, an `A`-algebra `B` and a surjection `g : M → N` of
`B`-modules, the induced map `TI(B,M) → TI(B,N)` is surjective.

The square-zero extension `B[M] → B[N]` induced by `g` is a surjection of `A`-algebras, so
`I(B[M]) → I(B[N])` is surjective by
`AdequateFunctor.surjective_moduleValueMap_of_injective`.  A lift of an element of the
tangent module `TI(B,N) ⊆ I(B[N])` automatically lies in `TI(B,M)`, because the augmentation
`B[M] → B` is the composite of `B[M] → B[N]` with the augmentation `B[N] → B`; this is where
the hypothesis that `g` is a map over the identity of `B` is used. -/
lemma surjective_tangentFunctorAt_map_of_injective
    (I : PresheafOfModules.{v} (algebraStructurePresheaf.{v} A)) [Injective I]
    (B : Type v) [CommRing B] [Algebra A B] {M N : ModuleCat.{v} B} (g : M ⟶ N)
    (hg : Function.Surjective g) :
    Function.Surjective ((tangentFunctorAt A I B).map g) := by
  show Function.Surjective
    ((tangentFunctor A I).map ((fixedAlgebraModuleFunctor A B).map g))
  set X := (fixedAlgebraModuleFunctor A B).obj M
  set Y := (fixedAlgebraModuleFunctor A B).obj N
  set q : X ⟶ Y := (fixedAlgebraModuleFunctor A B).map g
  have hsq : Function.Surjective (squareZeroMap A q) := by
    intro t
    obtain ⟨m, hm⟩ := hg (TrivSqZeroExt.snd t)
    exact ⟨(TrivSqZeroExt.fst t, m), TrivSqZeroExt.ext rfl hm⟩
  intro z
  obtain ⟨y, hy⟩ := surjective_moduleValueMap_of_injective A I (squareZeroMap A q) hsq
    (z : extensionValue A I Y)
  have hker : moduleValueMap A I (squareZeroAugmentation A X) y = 0 := by
    have hcomm : (squareZeroAugmentation A Y).comp (squareZeroMap A q) =
        squareZeroAugmentation A X := AlgHom.ext fun _ => rfl
    have hstep := moduleValueMap_comp A I (squareZeroMap A q) (squareZeroAugmentation A Y) y
    rw [hcomm, hy] at hstep
    have hz : moduleValueMap A I (squareZeroAugmentation A Y)
        (z : extensionValue A I Y) = 0 := z.2
    rw [hstep, hz]
  refine ⟨⟨y, hker⟩, Subtype.ext ?_⟩
  rwa [(tangentFunctor A I).map_coe q ⟨y, hker⟩]

/-- **Tag 06ZA, corrected.  Stacks erratum.**  Let `I` be an
injective object of the category of module-valued functors on `Alg_A`.  For every `A`-algebra
`B` and every short exact sequence `0 → N₁ → N → N₂ → 0` of `B`-modules, the map
`TI(B, N) → TI(B, N₂)` is an epimorphism.

The source asserts more: that the whole sequence `TI(B, N₁) → TI(B, N) → TI(B, N₂) → 0` is
exact, which in this library is the predicate `AdequateFunctor.HasRightExactTangentFunctor`
of Tag 06ZF.  **The other conjunct, exactness at `TI(B, N)`, is false**, and is refuted by
`AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective`: the counterexample
takes the field `k = ℚ`, the algebra `C = k[ε]/(ε²)`, the injective `C`-module
`J = Hom_k(C, k)` and the coinduced functor `I(D) = ∏_{α : D →ₐ C} J`, whose tangent module
`TI(k, V)` is the functions `V^* → J` vanishing at `0`; on `0 → k → k² → k → 0` the function
sending the first-coordinate functional to `0 ≠ j ∈ J` and everything else to `0` is killed
by `TI(k, k²) → TI(k, k)` and is not in the image of `TI(k, k) → TI(k, k²)`, every element of
which takes equal values at `(1, 0)` and `(1, 1)`.

Surjectivity at `TI(B, N₂)` — the statement proved here, and the whole of what the source's
assertion leaves standing — is unaffected: its proof does not use the coequalizer step that
the counterexample refutes. -/
@[stacks 06ZA "Stacks erratum: only the surjectivity at \
`TI(B, N₂)`.  Exactness at `TI(B, N)`, the other conjunct of the source's assertion that \
`TI(B,N₁) → TI(B,N) → TI(B,N₂) → 0` is exact, is false as stated, and is refuted by \
`AdequateFunctor.not_forall_hasRightExactTangentFunctor_of_injective`.  The module universe \
of `I` is taken to be the universe of the algebras."]
theorem epi_tangentFunctorAt_map_of_injective
    (I : PresheafOfModules.{v} (algebraStructurePresheaf.{v} A)) [Injective I]
    (B : Type v) [CommRing B] [Algebra A B] (S : ShortComplex (ModuleCat.{v} B))
    (hS : S.ShortExact) :
    Epi ((tangentFunctorAt A I B).map S.g) :=
  (AddCommGrpCat.epi_iff_surjective _).mpr
    (surjective_tangentFunctorAt_map_of_injective A I B S.g
      ((ModuleCat.epi_iff_surjective _).mp hS.epi_g))

end RightExactHalf

end AdequateFunctor
