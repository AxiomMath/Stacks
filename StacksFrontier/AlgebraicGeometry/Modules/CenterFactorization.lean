module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Kaehler
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHomQcohSource
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackVanishingOpenImmersion
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishing

/-!
# Factoring multiplication by a global section through a morphism of modules

Let `X` be a scheme and `r` a global section of `𝒪_X`. Multiplication by `r` on all
`𝒪_X`-modules at once is `Stacks.RegularSequence.globalSmulCenter`, an element of the centre of
the category of `𝒪_X`-modules. This file records the two steps by which a factorisation of
multiplication by `r` through a morphism of modules is produced and moved:

* on a spectrum and out of a quasi-coherent module, a factorisation on **global sections** is
  already a factorisation of morphisms;
* a factorisation of morphisms is carried across an isomorphism by the **naturality** of the
  centre element, with no compatibility of any functor with the scalar action.

Both are stated for arbitrary modules. They are used in the pole bound of [Stacks, Tag 0G5G],
where the concrete modules are inverse images of exterior powers of sheaves of relative
differentials; elaborating either step against those terms exhausts the heartbeat budget,
whereas against variables each is immediate.

## Main results

* `Stacks.AlgebraicGeometry.Modules.center_app_eq_of_moduleSpecΓ`: **a global-sections
  factorisation by a scalar is a factorisation by the centre element.**
* `Stacks.AlgebraicGeometry.Modules.comp_center_app_of_comp`: **conjugating a factorisation by
  the centre element through an isomorphism.**
* `Stacks.AlgebraicGeometry.Modules.restrictFunctor_map_globalSmulCenter`: **restriction along an
  open immersion carries multiplication by a global section to multiplication by its pullback.**
* `Stacks.AlgebraicGeometry.Modules.cokernelπ_app_smul_eq_zero`: **a factorisation of
  multiplication by a global section through the inverse image of a morphism along an open
  immersion, read on the sections over the opens inside the image of that open immersion.**

## Implementation notes

The first statement runs on faithfulness of global sections out of a quasi-coherent sheaf of
modules on a spectrum
(`Stacks.AlgebraicGeometry.ModuleLimits.moduleSpec_hom_ext_of_isQuasicoherent_source`) together
with the agreement of the `A`-action and the `Γ(Spec A, ⊤)`-action on global sections
(`Stacks.AlgebraicGeometry.AffineDifferentialsIso.smul_Spec_top`). The scalar is therefore
spelled `(Scheme.ΓSpecIso A).inv.hom c` on the sheaf side and `c` on the ring side; the two
`•` are different instances, and the restriction map `Γ(Spec A, ⊤) ⟶ Γ(Spec A, ⊤)` appearing in
`Stacks.RegularSequence.globalSmulCenter_app_app` is the identity because `Opens.leTop ⊤` is.

The second statement is where the distinction between transporting a *property* and transporting
*data* is settled. Monomorphy of a morphism moves across an isomorphism by faithfulness of the
functor applied; a factorisation is data, so moving it would need fullness, and then a
compatibility of that functor with the scalar action. Neither is needed if the conjugation is
performed inside one module category: `Stacks.RegularSequence.globalSmulCenter` is an element of
`CategoryTheory.CatCenter`, so its naturality field already says that multiplication by `r`
commutes with every morphism of `𝒪_X`-modules, and the two conjugating isomorphisms are absorbed
by it.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RegularSequence (globalSmulCenter globalSmulCenter_app_app)

universe u

namespace Stacks.AlgebraicGeometry.Modules

/-- **A global-sections factorisation by a scalar is a factorisation by the centre element**, on
a spectrum and out of a quasi-coherent module.

Global sections is faithful out of such a module
(`Stacks.AlgebraicGeometry.ModuleLimits.moduleSpec_hom_ext_of_isQuasicoherent_source`), and the
scalar actions of `A` and of `Γ(Spec A, ⊤)` on the global sections agree
(`Stacks.AlgebraicGeometry.AffineDifferentialsIso.smul_Spec_top`), so a factorisation of
multiplication by `c : A` on global sections is a factorisation of multiplication by the
corresponding global section of the structure sheaf. -/
theorem center_app_eq_of_moduleSpecΓ {A : CommRingCat.{u}} {F G : (Spec A).Modules}
    [F.IsQuasicoherent] (Θ : F ⟶ G) (Φ : G ⟶ F) (c : ↥A)
    (h : ∀ s, (moduleSpecΓFunctor.map Φ).hom ((moduleSpecΓFunctor.map Θ).hom s) = c • s) :
    Θ ≫ Φ = (globalSmulCenter (Spec A) ((Scheme.ΓSpecIso A).inv.hom c)).app F := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.moduleSpec_hom_ext_of_isQuasicoherent_source
    (ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  have hlhs : (moduleSpecΓFunctor.map (Θ ≫ Φ)).hom s =
      (moduleSpecΓFunctor.map Φ).hom ((moduleSpecΓFunctor.map Θ).hom s) := rfl
  have hrhs := globalSmulCenter_app_app (Spec A) ((Scheme.ΓSpecIso A).inv.hom c) F ⊤ s
  have hres : ((Spec A).presheaf.map
        (TopologicalSpace.Opens.leTop (⊤ : (Spec A).Opens)).op).hom
      ((Scheme.ΓSpecIso A).inv.hom c) = (Scheme.ΓSpecIso A).inv.hom c := by
    rw [show (TopologicalSpace.Opens.leTop (⊤ : (Spec A).Opens)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  rw [hres] at hrhs
  refine hlhs.trans ((h s).trans (Eq.trans ?_ hrhs.symm))
  exact (congrArg (fun y : ↥A => y • s)
      (Iso.inv_hom_id_apply (Scheme.ΓSpecIso A) c).symm).trans
    (Stacks.AlgebraicGeometry.AffineDifferentialsIso.smul_Spec_top
      ((Scheme.ΓSpecIso A).inv.hom c) s)

/-- **Conjugating a factorisation by the centre element through an isomorphism.** If
`Θ ≫ (K ≫ ψ ≫ u)` is multiplication by `r` and `u` is invertible, then `(u ≫ Θ ≫ K) ≫ ψ` is
multiplication by `r` as well.

`Stacks.RegularSequence.globalSmulCenter` is an element of the centre of the category of
`𝒪_X`-modules, so it commutes with `u`; that is the whole proof, and in particular no
compatibility of a functor with the scalar action is used. -/
theorem comp_center_app_of_comp {X : Scheme.{u}} (r : Γ(X, ⊤)) {A B C D : X.Modules}
    (u : A ⟶ B) [IsIso u] (Θ : B ⟶ C) (K : C ⟶ D) (ψ : D ⟶ A)
    (h : Θ ≫ (K ≫ ψ ≫ u) = (globalSmulCenter X r).app B) :
    (u ≫ Θ ≫ K) ≫ ψ = (globalSmulCenter X r).app A := by
  refine (cancel_mono u).1 ?_
  calc ((u ≫ Θ ≫ K) ≫ ψ) ≫ u
      = u ≫ Θ ≫ (K ≫ ψ ≫ u) := by simp only [Category.assoc]
    _ = u ≫ (globalSmulCenter X r).app B := by rw [h]
    _ = (globalSmulCenter X r).app A ≫ u := (globalSmulCenter X r).naturality u

/-- **Restriction along an open immersion carries multiplication by a global section to
multiplication by its pullback.** For `j : Y ⟶ X` an open immersion and `c` a global section of
`𝒪_X`, the restriction along `j` of multiplication by `c` on an `𝒪_X`-module is multiplication by
`j^*c` on the restricted module.

Over an open `V ⊆ Y` the sections of the restriction are the sections over the image `j(V)`, and
its `Γ(Y, V)`-action is the `Γ(X, j(V))`-action read through `AlgebraicGeometry.Scheme.Hom.appIso`;
so the statement is the identity
`(j.appIso V).inv (j.appLE ⊤ V c) = c|_{j(V)}`, which is
`AlgebraicGeometry.Scheme.Hom.appLE_appIso_inv`. -/
theorem restrictFunctor_map_globalSmulCenter {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (c : Γ(X, ⊤)) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor j).map ((globalSmulCenter X c).app M) =
      (globalSmulCenter Y (j.appTop c)).app ((Scheme.Modules.restrictFunctor j).obj M) := by
  apply Scheme.Modules.hom_ext
  intro V
  ext x
  have hscalar : (j.appIso V).inv (Y.presheaf.map V.leTop.op (j.appTop c)) =
      X.presheaf.map (j ''ᵁ V).leTop.op c :=
    Scheme.Hom.appLE_appIso_inv_apply j (le_top : V ≤ j ⁻¹ᵁ (⊤ : X.Opens)) c
  exact (congrArg (fun z : Γ(X, j ''ᵁ V) => (M.smul z).hom x) hscalar).symm

/-- **A factorisation of multiplication by a global section through a morphism of modules, read
on the sections over the opens inside the image of an open immersion.** If multiplication by the
pullback of `c : Γ(X, ⊤)` along an open immersion `j : Y ⟶ X` factors through the inverse image
along `j` of `ψ : M ⟶ N`, then over every open `W ⊆ X` contained in the image of `j` the cokernel
of `ψ` kills `c · s` for every section `s` of `N` over `W`.

Three steps: the factorisation is carried from the inverse image to the restriction along `j` by
`Stacks.AlgebraicGeometry.Modules.comp_center_app_of_comp`, which absorbs the comparison of the
two functors in the naturality of the centre element; the scalar is identified by
`Stacks.AlgebraicGeometry.Modules.restrictFunctor_map_globalSmulCenter`, which turns the
factorisation into the vanishing of the restriction along `j` of multiplication by `c` followed by
the projection to the cokernel of `ψ`; and that vanishing is read on the sections over the opens
inside the image of `j` by
`AlgebraicGeometry.Scheme.Modules.app_eq_zero_of_le_opensRange`. -/
theorem cokernelπ_app_smul_eq_zero {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (c : Γ(X, ⊤)) {M N : X.Modules} (ψ : M ⟶ N)
    (Θ : (Scheme.Modules.pullback j).obj N ⟶ (Scheme.Modules.pullback j).obj M)
    (h : Θ ≫ (Scheme.Modules.pullback j).map ψ =
      (globalSmulCenter Y (j.appTop c)).app ((Scheme.Modules.pullback j).obj N))
    {W : X.Opens} (hW : W ≤ j.opensRange) (s : Γ(N, W)) :
    (cokernel.π ψ).app W (X.presheaf.map W.leTop.op c • s) = 0 := by
  have hΘr : ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N ≫ Θ ≫
        inv ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M)) ≫
      (Scheme.Modules.restrictFunctor j).map ψ =
      (globalSmulCenter Y (j.appTop c)).app ((Scheme.Modules.restrictFunctor j).obj N) := by
    refine comp_center_app_of_comp (j.appTop c)
      ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N) Θ
      (inv ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M))
      ((Scheme.Modules.restrictFunctor j).map ψ) ?_
    rwa [(Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality ψ, IsIso.inv_hom_id_assoc]
  have hzero : (Scheme.Modules.restrictFunctor j).map (ψ ≫ cokernel.π ψ) = 0 := by
    rw [cokernel.condition]
    apply Scheme.Modules.hom_ext
    intro V
    rfl
  have hz : (Scheme.Modules.restrictFunctor j).map
      ((globalSmulCenter X c).app N ≫ cokernel.π ψ) = 0 := by
    rw [Functor.map_comp, restrictFunctor_map_globalSmulCenter j c N, ← hΘr, Category.assoc,
      ← Functor.map_comp, hzero, comp_zero]
  exact Scheme.Modules.app_eq_zero_of_le_opensRange j _ hz hW s

end Stacks.AlgebraicGeometry.Modules

end
