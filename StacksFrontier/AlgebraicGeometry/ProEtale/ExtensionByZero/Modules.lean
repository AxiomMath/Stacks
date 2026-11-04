module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.Localization
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of module sheaves on the small pro-étale site

A weakly étale morphism of schemes induces restriction of sheaves of modules over a ring on
the small pro-étale sites. This restriction has a left adjoint, extension by zero.

## Main definitions

* `AlgebraicGeometry.ProEtale.Modules.proetaleRestriction` is restriction of module sheaves
  along the morphism.
* `AlgebraicGeometry.ProEtale.Modules.extensionByZero` is the extension-by-zero functor.
* `AlgebraicGeometry.ProEtale.Modules.sheafifiedExtensionByZero` is the same functor given by
  an explicit construction: sheafification of the left Kan extension.

## Main results

* `AlgebraicGeometry.ProEtale.Modules.exists_extensionByZero` asserts existence of a left
  adjoint to restriction.
* `AlgebraicGeometry.ProEtale.Modules.extensionByZero_adjunction` is the defining adjunction.
* `AlgebraicGeometry.ProEtale.Modules.sheafifiedExtensionByZeroAdjunction` is the defining
  adjunction of the explicitly constructed functor.
* `AlgebraicGeometry.ProEtale.Modules.extensionByZeroIsoSheafified` identifies the two.

## Implementation notes

Sheaves of modules over the constant ring are represented as sheaves valued in `ModuleCat Λ`.
Restriction is precomposition along the canonical functor
`AlgebraicGeometry.ProEtale.proetalePostcompose` between small pro-étale sites. The
extension-by-zero functor is chosen from the existence assertion, with its adjunction supplied
by the same witness; in particular clients can use the adjunction unit and counit without
unfolding the choice.

Sheafification needs the forgetful functor of `ModuleCat Λ` to preserve the colimits indexed by
the coverings of the site. The universe of the ring is independent of the universe of the module
sections here, so Mathlib's instance for filtered colimits — which identifies the two — does not
apply, and the required preservation is obtained from `Module.DirectLimit`, which is available
for a directed system of modules in any pair of universes.

The left adjoint is moreover available as concrete data: `sheafifiedExtensionByZero` is the
composite of the forgetful functor to presheaves, left Kan extension along the opposite of
postcomposition, and sheafification, and `sheafifiedExtensionByZeroAdjunction` is its
adjunction to restriction. Uniqueness of left adjoints then pins the chosen functor down to a
canonical isomorphism with this construction.

## References

* [Stacks Project, Tag 09AE](https://stacks.math.columbia.edu/tag/09AE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.ProEtale.Modules

/-- The forgetful functor of a category of modules preserves the colimit of a system indexed by
a nonempty directed preorder. The colimit is realized by `Module.DirectLimit`, whose universe
of sections is independent of the universe of the ring. -/
private theorem forget_preservesColimit_of_directedPreorder
    {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (R : Type v) [Ring R] (F : ι ⥤ ModuleCat.{max u w} R) :
    PreservesColimit F (forget (ModuleCat.{max u w} R)) := by
  classical
  let G : ι → Type (max u w) := fun i => F.obj i
  let f : ∀ i j, i ≤ j → G i →ₗ[R] G j := fun i j h => (F.map (homOfLE h)).hom
  let : DirectedSystem G (f · · ·) := {
    map_self := fun i x => by simp [f]
    map_map := fun k j i hij hjk x =>
      congrArg (fun g : F.obj i ⟶ F.obj k => g.hom x)
        (F.map_comp (homOfLE hij) (homOfLE hjk)).symm
  }
  let c : Cocone F := {
    pt := ModuleCat.of R (Module.DirectLimit (G := G) f)
    ι := {
      app i := ModuleCat.ofHom (Module.DirectLimit.of R ι G f i)
      naturality i j g := by
        ext x
        rw [Subsingleton.elim g (homOfLE (leOfHom g))]
        simp [f]
    }
  }
  have hc : IsColimit c := {
    desc := fun s => ModuleCat.ofHom <| Module.DirectLimit.lift R ι G f
      (fun i => (s.ι.app i).hom) (fun i j h x => by simp [f])
    fac s i := by
      ext x
      simp [c, Module.DirectLimit.lift_of]
    uniq s m h := by
      refine ModuleCat.hom_ext (Module.DirectLimit.hom_ext fun i => ?_)
      ext x
      simpa [c, Module.DirectLimit.lift_of] using
        congrArg (fun φ : F.obj i ⟶ s.pt => φ.hom x) (h i)
  }
  have ht : IsColimit ((forget (ModuleCat.{max u w} R)).mapCocone c) := by
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      obtain ⟨i, y, hy⟩ :=
        Module.DirectLimit.exists_of (R := R) (G := G) (f := f) x
      exact ⟨i, y, hy.symm⟩
    · intro i x y h
      obtain ⟨j, hij, hxy⟩ :=
        Module.DirectLimit.exists_eq_of_of_eq (R := R) (G := G) (f := f) h
      exact ⟨j, homOfLE hij, hxy⟩
  exact preservesColimit_of_preserves_colimit_cocone hc ht

/-- Restriction of module sheaves along a weakly étale morphism of schemes. -/
@[implicit_reducible]
def proetaleRestriction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (Λ : Type v) [Ring Λ] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ) := by
  letI := proetalePostcompose_isContinuous j
  exact (proetalePostcompose j).sheafPushforwardContinuous
    (ModuleCat.{max (u + 1) w} Λ) (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- Sheafification exists for `Λ`-module presheaves on the small pro-étale site. -/
private theorem hasSheafify_of_essentiallySmall (X : Scheme.{u}) (Λ : Type v) [Ring Λ] :
    HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) := by
  let eSite : Scheme.ProEt X ≌
      SmallModel.{max (u + 1) w, u, u + 1} (Scheme.ProEt X) :=
    equivSmallModel.{max (u + 1) w, u, u + 1} (Scheme.ProEt X)
  let Jsmall := eSite.inverse.inducedTopology (Scheme.ProEt.topology X)
  let : ∀ V : SmallModel.{max (u + 1) w, u, u + 1} (Scheme.ProEt X),
      PreservesColimitsOfShape (Jsmall.Cover V)ᵒᵖ
        (forget (ModuleCat.{max (u + 1) w} Λ)) := by
    intro V
    let : PreservesColimitsOfShape (OrderDual (Jsmall.Cover V))
        (forget (ModuleCat.{max (u + 1) w} Λ)) :=
      ⟨forget_preservesColimit_of_directedPreorder Λ _⟩
    exact preservesColimitsOfShape_of_equiv
      (orderDualEquivalence (Jsmall.Cover V))
      (forget (ModuleCat.{max (u + 1) w} Λ))
  let : HasSheafify Jsmall (ModuleCat.{max (u + 1) w} Λ) := inferInstance
  exact hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) w} _ _

/-- Restriction of pro-étale module sheaves has a left adjoint. -/
@[stacks 09AE "extension_by_zero_modules", sga "4 IV 11.3.1" "pro-étale, Λ-modules"]
theorem exists_extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (Λ : Type v) [Ring Λ] :
    Nonempty (Σ F : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ),
        F ⊣ proetaleRestriction j Λ) := by
  let : (proetalePostcompose j).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
    proetalePostcompose_isContinuous j
  let : HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) :=
    hasSheafify_of_essentiallySmall.{u, v, w} X Λ
  exact ⟨⟨_, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proetalePostcompose j) (ModuleCat.{max (u + 1) w} Λ)
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)⟩⟩

/-- Extension by zero of pro-étale sheaves of modules. -/
@[implicit_reducible]
def extensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (Λ : Type v) [Ring Λ] :
    Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) :=
  (Classical.choice (exists_extensionByZero j Λ)).1

/-- Extension by zero is left adjoint to restriction. -/
def extensionByZero_adjunction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (Λ : Type v) [Ring Λ] :
    extensionByZero j Λ ⊣ proetaleRestriction j Λ :=
  (Classical.choice (exists_extensionByZero j Λ)).2

/-- Presheaves of `Λ`-modules on the small pro-étale site admit sheafification. The site is
essentially small, and the forgetful functor of `ModuleCat Λ` preserves the colimits indexed
by the coverings of a small model of the site. -/
theorem hasSheafify_proetale (X : Scheme.{u}) (Λ : Type v) [Ring Λ] :
    HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) := by
  exact hasSheafify_of_essentiallySmall.{u, v, w} X Λ

/-- Extension by zero of pro-étale sheaves of `Λ`-modules, as an explicit functor: the
composite of the inclusion of sheaves into presheaves, left Kan extension along the opposite
of postcomposition by `j`, and sheafification. -/
@[implicit_reducible, stacks 09AE "(3), the functor j_! : Mod(U_proetale, Λ) -> \
Mod(X_proetale, Λ) called extension by zero, as explicit data: the sheafification of the \
left Kan extension along the opposite of postcomposition by j"]
def sheafifiedExtensionByZero {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (Λ : Type v) [Ring Λ] :
    Sheaf (Scheme.ProEt.topology U) (ModuleCat.{max (u + 1) w} Λ) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) := by
  haveI := proetalePostcompose_isContinuous j
  haveI := hasSheafify_proetale.{u, v, w} X Λ
  exact Functor.sheafPullbackConstruction.sheafPullback
    (proetalePostcompose j) (ModuleCat.{max (u + 1) w} Λ)
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The explicit extension-by-zero functor is left adjoint to restriction. -/
@[stacks 09AE "(3), the adjunction j_! ⊣ j^{-1} on sheaves of Λ-modules, witnessing that \
restriction along a weakly étale morphism has extension by zero as a left adjoint"]
def sheafifiedExtensionByZeroAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (Λ : Type v) [Ring Λ] :
    sheafifiedExtensionByZero.{u, v, w} j Λ ⊣ proetaleRestriction.{u, v, w} j Λ := by
  haveI := proetalePostcompose_isContinuous j
  haveI := hasSheafify_proetale.{u, v, w} X Λ
  exact Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proetalePostcompose j) (ModuleCat.{max (u + 1) w} Λ)
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)

/-- The chosen extension-by-zero functor is canonically isomorphic to the explicit
sheafified left Kan extension, by uniqueness of left adjoints. -/
def extensionByZeroIsoSheafified {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (Λ : Type v) [Ring Λ] :
    extensionByZero.{u, v, w} j Λ ≅ sheafifiedExtensionByZero.{u, v, w} j Λ :=
  (extensionByZero_adjunction.{u, v, w} j Λ).leftAdjointUniq
    (sheafifiedExtensionByZeroAdjunction.{u, v, w} j Λ)

end AlgebraicGeometry.ProEtale.Modules

end
