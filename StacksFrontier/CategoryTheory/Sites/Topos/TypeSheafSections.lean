module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Subsheaf
import StacksCore.Tactic.EgaSgaAttribute

/-! # Sections of equalizers and of coproducts of sheaves of types

Two elementary descriptions of sections of sheaves of types on a site `(C, J)`.

## Main results

* `Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv`: for `f g : A ⟶ B` a pair of morphisms of
  sheaves of types, the sections of `CategoryTheory.Limits.equalizer f g` over an object `X` are
  the sections of `A` over `X` on which `f` and `g` agree. The underlying element of a section of
  the equalizer is obtained by applying `CategoryTheory.Limits.equalizer.ι`, and this
  identification is natural in `X`.

* `Stacks.Sheaves.TypeSheaf.exists_covering_of_epi_sigmaDesc`: if a family of morphisms of sheaves
  of types `ψ i : A i ⟶ B` induces an epimorphism `∐ A ⟶ B`, then every section of `B` is, locally
  on a covering sieve, in the image of a single `ψ i`.

The second statement is the concrete content of "an epimorphism out of a coproduct is a jointly
locally surjective family": the covering sieve produced is the sieve of all `g : V ⟶ X` along which
the restriction of the given section lies in the union of the ranges of the `ψ i`, and the fact
that it covers is `Stacks.Sheaves.TypeSheaf.sheafify_iSup_range_eq_top`.

## References

* [Stacks Project, Sheaves on sites](https://stacks.math.columbia.edu/tag/00VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w₂ t v u

namespace Stacks.Sheaves.TypeSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Equalizer

variable {A B : Sheaf J (Type w)} (f g : A ⟶ B) (X : Cᵒᵖ)

/-- The underlying element over `X` of a section of `CategoryTheory.Limits.equalizer f g`, namely
its image under `CategoryTheory.Limits.equalizer.ι f g`, is a section of `A` on which `f` and `g`
agree. -/
theorem equalizer_ι_app_condition (y : (equalizer f g).obj.obj X) :
    f.hom.app X ((equalizer.ι f g).hom.app X y) =
      g.hom.app X ((equalizer.ι f g).hom.app X y) := by
  simpa using congr_arg (fun m : equalizer f g ⟶ B => m.hom.app X y) (equalizer.condition f g)

/-- A section `y` of `A` over `X` on which `f` and `g` agree is the image under
`CategoryTheory.Limits.equalizer.ι f g` of a unique section of `CategoryTheory.Limits.equalizer
f g` over `X`.

This is the sheaf-theoretic form of the fact that the functor of sections over `X` preserves finite
limits, combined with the description of equalizers in `Type`. -/
theorem existsUnique_equalizer_ι_app_eq (y : A.obj.obj X)
    (hy : f.hom.app X y = g.hom.app X y) :
    ∃! z : (equalizer f g).obj.obj X, (equalizer.ι f g).hom.app X z = y :=
  Types.unique_of_type_equalizer _ _
    (isLimitOfHasEqualizerOfPreservesLimit
      (sheafToPresheaf J (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj X) f g) y hy

/-- The sections over `X` of the equalizer of two morphisms `f g : A ⟶ B` of sheaves of types are
the sections of `A` over `X` on which `f` and `g` agree. -/
def equalizerSectionsEquiv :
    (equalizer f g).obj.obj X ≃ { x : A.obj.obj X // f.hom.app X x = g.hom.app X x } :=
  Equiv.ofBijective (fun y => ⟨(equalizer.ι f g).hom.app X y, equalizer_ι_app_condition f g X y⟩)
    ⟨fun y₁ _ h => (existsUnique_equalizer_ι_app_eq f g X
        ((equalizer.ι f g).hom.app X y₁) (equalizer_ι_app_condition f g X y₁)).unique rfl
        (congr_arg Subtype.val h).symm,
      fun x => ((existsUnique_equalizer_ι_app_eq f g X x.1 x.2).exists.imp
        fun _ hz => Subtype.ext hz)⟩

/-- `Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv` is given by applying
`CategoryTheory.Limits.equalizer.ι f g`. -/
@[simp] theorem equalizerSectionsEquiv_apply_coe (y : (equalizer f g).obj.obj X) :
    ((equalizerSectionsEquiv f g X y : { x : A.obj.obj X // f.hom.app X x = g.hom.app X x }) :
      A.obj.obj X) = (equalizer.ι f g).hom.app X y :=
  rfl

/-- The section of the equalizer attached to a section `x` of `A` on which `f` and `g` agree does
restrict to `x` along `CategoryTheory.Limits.equalizer.ι f g`. -/
@[simp] theorem equalizerSectionsEquiv_symm_apply
    (x : { x : A.obj.obj X // f.hom.app X x = g.hom.app X x }) :
    (equalizer.ι f g).hom.app X ((equalizerSectionsEquiv f g X).symm x) = (x : A.obj.obj X) :=
  congr_arg Subtype.val ((equalizerSectionsEquiv f g X).apply_symm_apply x)

/-- `Stacks.Sheaves.TypeSheaf.equalizerSectionsEquiv` is natural in the object: the underlying
element of the restriction of a section of the equalizer is the restriction of its underlying
element. -/
theorem equalizerSectionsEquiv_naturality {Y : Cᵒᵖ} (h : X ⟶ Y)
    (y : (equalizer f g).obj.obj X) :
    ((equalizerSectionsEquiv f g Y ((equalizer f g).obj.map h y) :
        { x : A.obj.obj Y // f.hom.app Y x = g.hom.app Y x }) : A.obj.obj Y) =
      A.obj.map h (equalizerSectionsEquiv f g X y : A.obj.obj X) := by
  simp

end Equalizer

section Coproduct

variable [HasSheafify J (Type t)] {ι : Type w₂}
  (A : ι → Sheaf J (Type t)) {B : Sheaf J (Type t)} [HasCoproduct A]
  (ψ : ∀ i, A i ⟶ B) [Epi (Sigma.desc ψ)]

/-- If the morphism `∐ A ⟶ B` of sheaves of types induced by a family `ψ i : A i ⟶ B` is an
epimorphism, then the union of the ranges of the `ψ i`, as a subpresheaf of `B`, sheafifies to the
whole of `B`.

Indeed that sheafified union is a subsheaf of `B` through which every `ψ i`, hence also
`CategoryTheory.Limits.Sigma.desc ψ`, factors; so its inclusion into `B` is both a monomorphism and
an epimorphism, and the category of sheaves of types is balanced. -/
theorem sheafify_iSup_range_eq_top :
    (⨆ i, Subfunctor.range (ψ i).hom).sheafify J = ⊤ := by
  have hle : ∀ i, Subfunctor.range (ψ i).hom ≤
      (⨆ i, Subfunctor.range (ψ i).hom).sheafify J := fun i =>
    (le_iSup (fun i => Subfunctor.range (ψ i).hom) i).trans (Subfunctor.le_sheafify _ _)
  let B' : Sheaf J (Type t) :=
    ⟨((⨆ i, Subfunctor.range (ψ i).hom).sheafify J).toFunctor,
      (isSheaf_iff_isSheaf_of_type J _).2 (Subfunctor.sheafify_isSheaf _
        ((isSheaf_iff_isSheaf_of_type J B.obj).1 B.property))⟩
  let m : B' ⟶ B := ⟨Subfunctor.ι _⟩
  let ψ' : ∀ i, A i ⟶ B' := fun i => ⟨Subfunctor.lift (ψ i).hom (hle i)⟩
  have hfac : Sigma.desc ψ' ≫ m = Sigma.desc ψ := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact Sheaf.hom_ext (Subfunctor.lift_ι (ψ i).hom (hle i))
  have : Epi m := epi_of_epi_fac hfac
  have : Mono m := (sheafToPresheaf J (Type t)).mono_of_mono_map
    (by dsimp [m]; infer_instance)
  have : IsIso m := isIso_of_mono_of_epi m
  rw [Subfunctor.eq_top_iff_isIso]
  exact (sheafToPresheaf J (Type t)).map_isIso m

/-- Sections of a coproduct of sheaves of types are locally in one component: if the family
`ψ i : A i ⟶ B` of morphisms of sheaves of types induces an epimorphism `∐ A ⟶ B`, then every
section `b` of `B` over `X` admits a covering sieve `S` of `X` such that the restriction of `b`
along any `g : V ⟶ X` in `S` is in the image of a single `ψ i`. -/
@[sga "3 IV 4.4.3" "(i) ⇒ (iii)", sga "3 VIB 10.15" "partial"]
theorem exists_covering_of_epi_sigmaDesc (X : C) (b : B.obj.obj (op X)) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ ⦃V : C⦄ (g : V ⟶ X), S g →
      ∃ (i : ι) (a : (A i).obj.obj (op V)),
        (ψ i).hom.app (op V) a = B.obj.map g.op b := by
  refine ⟨(⨆ i, Subfunctor.range (ψ i).hom).sieveOfSection b, ?_, ?_⟩
  · change b ∈ ((⨆ i, Subfunctor.range (ψ i).hom).sheafify J).obj (op X)
    rw [sheafify_iSup_range_eq_top A ψ]
    trivial
  · intro V g hg
    simpa only [Subfunctor.sieveOfSection_apply, Subfunctor.iSup_obj,
      Set.mem_iUnion, Subfunctor.range_obj, Set.mem_range] using hg

end Coproduct

end Stacks.Sheaves.TypeSheaf

end
