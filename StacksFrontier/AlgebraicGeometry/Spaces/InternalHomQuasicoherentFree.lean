module

public import StacksFrontier.AlgebraicGeometry.Spaces.InternalHomFreeBaseCase
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts

/-!
# Quasi-coherence of the internal Hom out of a finite free `𝒪_F`-module

Clause (6) of Stacks 03M1 asserts that the internal Hom `𝓗om_{𝒪_F}(G, G')` of two quasi-coherent
`𝒪_F`-modules on an algebraic space `F` is quasi-coherent when `G` is of finite presentation. This
file proves that `𝓗om_{𝒪_F}(P, N)` is quasi-coherent when `P` is a finite coproduct of copies of
the structure sheaf and `N` is quasi-coherent, and deduces the case of a module with a global
presentation by finite free modules, granted Descent, Proposition 03DX(2).

## Main definitions

* `Stacks.SheafOfModules.isLimitFanOfBijectiveApp`: a family of morphisms of sheaves of modules
  which is bijective on the sections over every object of the site is a limiting fan.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_unit`: `𝓗om_{𝒪_F}(𝒪_F, N)`
  is quasi-coherent when `N` is.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_free`: the base case of
  Stacks 03M1(6) for quasi-coherence: if `P` is a finite coproduct of copies of the structure sheaf
  and `N` is quasi-coherent then `𝓗om_{𝒪_F}(P, N)` is quasi-coherent.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation`: clause
  (6) for a module with a *global* presentation by finite free modules, granted Descent,
  Proposition 03DX(2).

## Implementation notes

**No `@[stacks 03M1]` attribute is carried and no clause of Stacks 03M1 is proved here.** The
finite-presentation hypothesis of the source is Stacks 03DL(7), which is *local*: for every object
`U` of the site there is a covering `{U_i → U}` on whose members the first variable has a finite
global presentation. The hypotheses below are global presentations on the small étale site of `F`
itself, which is strictly stronger, so none of the statements is clause (6).

`Stacks.SheafOfModules.isLimitFanOfBijectiveApp` asks for bijectivity over *every* object of the
site, not only over the affine étale charts, and holds for an arbitrary index type in an arbitrary
universe; the finiteness of `Fin n` is what
`SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts` needs.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GMY](https://stacks.math.columbia.edu/tag/0GMY)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v r m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- **A family of morphisms of sheaves of modules which is bijective on the sections over every
object of the site is a limiting fan.**  For `π : ∀ i, H ⟶ G i` such that

`H(X) ⟶ ∏_{i} (G i)(X)`, `x ↦ (π i (x))_i`

is bijective for every object `X`, the fan `H ⟶ G i` is a product of the `G i`.

The limiting cone is the given one, so no limit in the category of sheaves of modules has to exist
and no sheafification hypothesis is needed. The index type is arbitrary and lives in its own
universe. -/
noncomputable def isLimitFanOfBijectiveApp {I : Type w}
    {G : I → _root_.SheafOfModules.{m} R} {H : _root_.SheafOfModules.{m} R}
    (π : ∀ i, H ⟶ G i)
    (hπ : ∀ X : Cᵒᵖ, Function.Bijective
      (fun x : H.val.obj X => fun i => (π i).val.app X x)) :
    IsLimit (Fan.mk H π) := by
  let e : ∀ X : Cᵒᵖ, (H.val.obj X ≃ₗ[R.obj.obj X] (∀ i, (G i).val.obj X)) :=
    fun X => LinearEquiv.ofBijective (LinearMap.pi fun i => ((π i).val.app X).hom) (hπ X)
  have he : ∀ (X : Cᵒᵖ) (z : ∀ i, (G i).val.obj X) (i : I),
      (π i).val.app X ((e X).symm z) = z i :=
    fun X z i => congrFun ((e X).apply_symm_apply z) i
  refine Fan.IsLimit.mk _ (fun s => ⟨PresheafOfModules.Hom.mk
    (fun X => ModuleCat.ofHom ((e X).symm.toLinearMap.comp
      (LinearMap.pi fun i => ((s.proj i).val.app X).hom))) ?_⟩) ?_ ?_
  · intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change (e Y).symm (fun i => (s.proj i).val.app Y (s.pt.val.map f y)) =
      H.val.map f ((e X).symm (fun i => (s.proj i).val.app X y))
    refine (e Y).injective (funext fun i => ?_)
    have hnat : (π i).val.app Y (H.val.map f ((e X).symm
        (fun i => (s.proj i).val.app X y))) =
        (s.proj i).val.app Y (s.pt.val.map f y) := by
      rw [PresheafOfModules.naturality_apply (π i).val f, he X]
      exact (PresheafOfModules.naturality_apply (s.proj i).val f y).symm
    exact (he Y _ i).trans hnat.symm
  · intro s j
    apply _root_.SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact he X _ j
  · intro s n hn
    apply _root_.SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change n.val.app X y = (e X).symm (fun i => (s.proj i).val.app X y)
    refine (e X).injective (funext fun i => ?_)
    have hleg : (π i).val.app X (n.val.app X y) = (s.proj i).val.app X y :=
      congrArg (fun k => (ConcreteCategory.hom
        (PresheafOfModules.Hom.app k X)) y) (congrArg _root_.SheafOfModules.Hom.val (hn i))
    exact hleg.trans (he X (fun i => (s.proj i).val.app X y) i).symm

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The internal Hom out of one copy of the structure sheaf of an algebraic space is
quasi-coherent as soon as the module itself is.** -/
theorem isQuasicoherentOnSite_smallEtaleInternalHom_unit
    (N : Modules.{u, max (u + 1) m} B S hS F hF) (hN : N.IsQuasicoherentOnSite) :
    (smallEtaleInternalHom B S hS F hF
      (smallEtaleUliftUnit.{u, m} B S hS F hF) N).IsQuasicoherentOnSite :=
  (_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).prop_of_iso
      (smallEtaleUnitCoevalIso N) hN

/-- **The base case of Stacks 03M1(6) for quasi-coherence.** Let `P` be a *finite* coproduct of
copies of the structure sheaf of an algebraic space `F` — in this module universe, of
`AlgebraicGeometry.Space.smallEtaleUliftUnit` — and let `N` be a quasi-coherent `𝒪_F`-module. Then
`𝓗om_{𝒪_F}(P, N)` is quasi-coherent. -/
theorem isQuasicoherentOnSite_smallEtaleInternalHom_free {n : ℕ}
    {P N : Modules.{u, max (u + 1) m} B S hS F hF}
    (ι : ∀ _ : Fin n, smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (hN : N.IsQuasicoherentOnSite) :
    (smallEtaleInternalHom B S hS F hF P N).IsQuasicoherentOnSite :=
  (_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))).prop_of_isLimit_fan
      (Stacks.SheafOfModules.isLimitFanOfBijectiveApp
        (G := fun _ : Fin n => smallEtaleInternalHom B S hS F hF
          (smallEtaleUliftUnit.{u, m} B S hS F hF) N)
        (fun i => smallEtaleInternalHomMapLeft B S hS F hF (ι i) N)
        (fun X => bijective_smallEtaleInternalHomMapLeft_pi_app ι hP N X.unop))
      (fun _ => isQuasicoherentOnSite_smallEtaleInternalHom_unit N hN)

/-- **Stacks 03M1(6) for a module with a global presentation by finite free modules, granted
Descent, Proposition 03DX(2).** Let `Q --a--> P --b--> M --> 0` be a presentation of `𝒪_F`-modules
with `P` and `Q` finite coproducts of copies of the structure sheaf, and let `N` be a
quasi-coherent `𝒪_F`-module. Then `𝓗om_{𝒪_F}(M, N)` is quasi-coherent.

`h03DX` is Descent, Proposition 03DX(2) for the small étale site of `F`: an `𝒪_F`-module is
quasi-coherent exactly when it is cartesian on affine charts.

This is **not** clause (6): the finite-presentation hypothesis of Stacks 03M1(6), Stacks 03DL(7),
asks for a presentation only étale-locally on `F`, and the one here is global. See the
implementation notes. -/
theorem isQuasicoherentOnSite_smallEtaleInternalHom_of_presentation {p q : ℕ}
    {M P Q N : Modules.{u, max (u + 1) m} B S hS F hF}
    (ιP : ∀ _ : Fin p, smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ P)
    (hιP : IsColimit (Cofan.mk P ιP))
    (ιQ : ∀ _ : Fin q, smallEtaleUliftUnit.{u, m} B S hS F hF ⟶ Q)
    (hιQ : IsColimit (Cofan.mk Q ιQ))
    {a : Q ⟶ P} {b : P ⟶ M} (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab))
    (hN : N.IsQuasicoherentOnSite)
    (h03DX : ∀ G : Modules.{u, max (u + 1) m} B S hS F hF,
      G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G) :
    (smallEtaleInternalHom B S hS F hF M N).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_smallEtaleInternalHom_of_isCartesian hab hb N h03DX
    (isQuasicoherentOnSite_smallEtaleInternalHom_free ιP hιP hN)
    (isQuasicoherentOnSite_smallEtaleInternalHom_free ιQ hιQ hN)

end AlgebraicGeometry.Space

end
