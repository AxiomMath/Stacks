module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Composite

/-!
# Vanishing of a pulled-back section, read as an inclusion of ideal sheaves

A global section `σ` of an invertible module `L` on a scheme `X` pulls back to zero along
`f : W ⟶ X` exactly when `f` factors through the zero scheme `Z(σ)` ([Stacks, Tag 02OR]), and a
morphism factors through the closed subscheme cut out by a quasi-coherent ideal sheaf exactly
when that ideal sheaf lies in the kernel of the morphism. Chaining the two turns the vanishing
of a pulled-back section into the inclusion `Z(σ) ≤ f.ker`, which is the form in which several
such conditions can be compared and combined.

This file collects that translation together with the three manipulations of a vanishing
condition that the proof of condition (4) of [Stacks, Tag 0F97] needs: transport along an
isomorphism of the ambient module, the composition law, and the passage between an inverse-image
ideal sheaf `J.comap h` and the kernel of a composite.

## Main definitions

* `Stacks.Divisors.pullbackCompIso`: the contraction `f^*g^*M ≅ (f ≫ g)^*M` of an iterated
  pullback, as an isomorphism; `Stacks.PullbackTensorIso.pullbackCompHom` is its forward
  direction, and nothing in the repository records that that morphism is invertible.

## Main results

* `Stacks.Divisors.factorsThrough_closedImmersion_iff`: a morphism factors through a closed
  immersion exactly when the immersion's kernel lies in the morphism's kernel. This is the
  universal property of a closed immersion, `AlgebraicGeometry.IsClosedImmersion.lift`, read as
  an equivalence.
* `Stacks.Divisors.le_ker_iff_factorsThrough`: the same for the closed subscheme of a
  quasi-coherent ideal sheaf.
* `Stacks.Divisors.comap_le_ker_iff`: **the inverse image `J.comap h` lies in the kernel of `f`
  exactly when `J` lies in the kernel of `f ≫ h`.**
* `Stacks.Divisors.pullbackGlobalSections_eq_zero_iff_le_ker`: **the pulled-back section
  vanishes exactly when the ideal of the zero scheme lies in the kernel.**
* `Stacks.Divisors.pullbackGlobalSections_iso_eq_zero_iff` and
  `Stacks.Divisors.pullbackGlobalSections_comp_eq_zero_iff`: the vanishing of a pulled-back
  section is unchanged by an isomorphism of the ambient module, and vanishing along a composite
  is vanishing of the twice-pulled-back section.

## Implementation notes

`StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization` proves three of these
statements as `private` lemmas, for its own use: the factorization criterion for an ideal sheaf,
the transport along an isomorphism, and the composition law. They are reproved here from the
public interface — the factorization clause of [Stacks, Tag 02OR],
`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι` and
`AlgebraicGeometry.Scheme.Hom.le_ker_comp` — rather than exported from there, so that nothing in
that file changes.

`Stacks.Divisors.comap_le_ker_iff` is the one statement here with geometric content, and it is
the cartesian square `(J.comap h).subscheme ≅ W ×_V J.subscheme` of
`AlgebraicGeometry.Scheme.IdealSheafData.comapIso`: factoring `f : W ⟶ T` through the inverse
image of `J` is giving a morphism to that fibre product over `f`, which is factoring `f ≫ h`
through `J`.

## References

* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

@[expose] public noncomputable section

namespace Stacks.Divisors

/-! ### Factorization and kernels -/

/-- **A morphism factors through a closed immersion exactly when the immersion's kernel is
contained in the morphism's kernel.** The factorization is
`AlgebraicGeometry.IsClosedImmersion.lift`. -/
theorem factorsThrough_closedImmersion_iff {A B W : Scheme.{u}} (j : A ⟶ B)
    [IsClosedImmersion j] (f : W ⟶ B) :
    (∃ g : W ⟶ A, g ≫ j = f) ↔ j.ker ≤ f.ker :=
  ⟨fun ⟨g, hg⟩ => hg ▸ Scheme.Hom.le_ker_comp g j,
    fun h => ⟨IsClosedImmersion.lift j f h, IsClosedImmersion.lift_fac j f h⟩⟩

/-- **A quasi-coherent ideal sheaf is contained in the kernel of a morphism exactly when that
morphism factors through the closed subscheme the ideal sheaf cuts out.** -/
theorem le_ker_iff_factorsThrough {X W : Scheme.{u}} (I : X.IdealSheafData) (f : W ⟶ X) :
    I ≤ f.ker ↔ ∃ g : W ⟶ I.subscheme, g ≫ I.subschemeι = f :=
  (iff_of_eq (congrArg (fun J : X.IdealSheafData => J ≤ f.ker)
      (Scheme.IdealSheafData.ker_subschemeι I).symm)).trans
    (factorsThrough_closedImmersion_iff I.subschemeι f).symm

/-- **The scheme-theoretic inverse image of an ideal sheaf lies in the kernel of a morphism
exactly when the ideal sheaf lies in the kernel of the composite.** Both sides say that the
composite factors through the closed subscheme, the left-hand side through the inverse image
inside the intermediate scheme. -/
theorem comap_le_ker_iff {W T V : Scheme.{u}} (J : V.IdealSheafData) (h : T ⟶ V) (f : W ⟶ T) :
    J.comap h ≤ f.ker ↔ J ≤ (f ≫ h).ker := by
  rw [le_ker_iff_factorsThrough, le_ker_iff_factorsThrough]
  refine ⟨fun ⟨u, hu⟩ => ⟨u ≫ (J.comapIso h).hom ≫ pullback.snd h J.subschemeι, ?_⟩,
    fun ⟨w, hw⟩ => ⟨pullback.lift f w hw.symm ≫ (J.comapIso h).inv, ?_⟩⟩
  · rw [Category.assoc, Category.assoc, ← pullback.condition,
      ← Category.assoc (J.comapIso h).hom, Scheme.IdealSheafData.comapIso_hom_fst,
      ← Category.assoc, hu]
  · rw [Category.assoc, Scheme.IdealSheafData.comapIso_inv_subschemeι, pullback.lift_fst]

/-! ### Vanishing of a pulled-back section -/

/-- An isomorphism of sheaves of modules detects vanishing of sections. -/
theorem hom_app_eq_zero_iff_of_isIso {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) [IsIso φ] (U : X.Opens) (σ : Γ(M, U)) :
    PresheafOfModules.Hom.app φ.val (op U) σ = 0 ↔ σ = 0 :=
  map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (φ.app U)).injective

/-- **The pullback of a global section of an invertible module along `f` vanishes exactly when
the defining ideal of its zero scheme lies in the kernel of `f`.** -/
theorem pullbackGlobalSections_eq_zero_iff_le_ker {X W : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) (f : W ⟶ X) :
    pullbackGlobalSections f L σ = 0 ↔ zeroScheme X L σ ≤ f.ker :=
  (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L σ f).trans
    (le_ker_iff_factorsThrough (zeroScheme X L σ) f).symm

/-- **The vanishing of a pulled-back section is unchanged by an isomorphism of the ambient
module.** -/
theorem pullbackGlobalSections_iso_eq_zero_iff {X W : Scheme.{u}} (f : W ⟶ X)
    {M N : X.Modules} (e : M ≅ N) (σ : Γ(M, ⊤)) :
    pullbackGlobalSections f N (PresheafOfModules.Hom.app e.hom.val (op ⊤) σ) = 0 ↔
      pullbackGlobalSections f M σ = 0 := by
  have : IsIso e.hom := e.isIso_hom
  refine (Eq.congr_left
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
      f e.hom σ)).trans ?_
  exact hom_app_eq_zero_iff_of_isIso ((Scheme.Modules.pullback f).map e.hom) ⊤ _

/-- **Vanishing of a section pulled back along a composite is vanishing of the twice-pulled-back
section.** -/
theorem pullbackGlobalSections_comp_eq_zero_iff {W X Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Z)
    (L : Z.Modules) (σ : Γ(L, ⊤)) :
    pullbackGlobalSections (f ≫ g) L σ = 0 ↔
      pullbackGlobalSections f ((Scheme.Modules.pullback g).obj L)
        (pullbackGlobalSections g L σ) = 0 := by
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp f g L σ]
  exact hom_app_eq_zero_iff_of_isIso ((Scheme.Modules.pullbackComp f g).hom.app L) ⊤ _

/-- A section killed by `g` is killed by any composite ending in `g`. -/
theorem pullbackGlobalSections_comp_eq_zero {W X Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Z)
    (L : Z.Modules) (σ : Γ(L, ⊤)) (h : pullbackGlobalSections g L σ = 0) :
    pullbackGlobalSections (f ≫ g) L σ = 0 :=
  (pullbackGlobalSections_comp_eq_zero_iff f g L σ).mpr (by rw [h]; exact map_zero _)

/-! ### The contraction of an iterated pullback as an isomorphism -/

/-- **The contraction `f^*g^*M ≅ (f ≫ g)^*M` of an iterated pullback**, at the spelling of
[Stacks, Tag 01CD] that `Stacks.PullbackTensorIso.pullbackCompHom` and the two fibre coordinates
of [Stacks, Tag 0F97] are written at. -/
def pullbackCompIso {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (N : C.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj N where
  hom := Stacks.PullbackTensorIso.pullbackCompHom f g N
  inv := (Stacks.DerivedPullback.Composition.modulePullbackComp f.toLRSHom.toShHom
    g.toLRSHom.toShHom).inv.app N
  hom_inv_id := (Stacks.DerivedPullback.Composition.modulePullbackComp f.toLRSHom.toShHom
    g.toLRSHom.toShHom).hom_inv_id_app N
  inv_hom_id := (Stacks.DerivedPullback.Composition.modulePullbackComp f.toLRSHom.toShHom
    g.toLRSHom.toShHom).inv_hom_id_app N

end Stacks.Divisors

end
