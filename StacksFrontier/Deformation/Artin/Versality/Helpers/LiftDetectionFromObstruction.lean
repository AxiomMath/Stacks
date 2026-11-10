module

public import StacksFrontier.Deformation.Artin.Versality.Helpers.OpennessFromLiftDetection

/-!
# Lift detection over products of kernels from obstruction groups

Let `x` be an object of a category fibred in groupoids over `Spec A`. Suppose given abelian
groups `O(M)`, functorial in the `A`-module `M`, obstruction elements `ob(t) ∈ O(Ker t)` for the
deformation situations `t` of `A`, vanishing exactly when `x` lifts across `t` and carried to each
other by the kernel maps of morphisms of deformation situations over the identity of `(x, A)`,
and suppose `O(∏ Mₙ) → ∏ O(Mₙ)` injective. Then `x` lifts across a deformation situation whose
kernel is the product of the kernels of deformation situations it lifts across. This is how
assumptions (4) and (5)(b) of Stacks 0CYF enter its proof
(`Deformation.Artin.ObstructionTheory.hasLift_of_injective`), with the naturality of obstruction
elements asked only over a fixed `(x, A)`, as in the footnote to assumption (4) of the source.

## Main results

* `Deformation.Artin.hasLiftOfCountableProductsOfFiniteType_of_obstruction`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe w' u v w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

/-- A family of module maps `N ⟶ Mₙ` identifying `N` with `∏ Mₙ` carries injectivity of
`O(∏ Mₙ) → ∏ O(Mₙ)` to injectivity of `O(N) → ∏ O(Mₙ)`. -/
theorem injective_map_of_bijective {A : Type u} [CommRing A]
    (O : ModuleCat.{u} A ⥤ AddCommGrpCat.{w'})
    {N : ModuleCat.{u} A} (M : ℕ → ModuleCat.{u} A) (g : ∀ n, N ⟶ M n)
    (hbij : Function.Bijective (fun z n => g n z))
    (hinj : Function.Injective (fun (z : O.obj (ModuleCat.of A (∀ n, (M n : Type u)))) n =>
      O.map (ModuleCat.ofHom (LinearMap.proj n) : ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n) z)) :
    Function.Injective fun (o : O.obj N) (n : ℕ) => O.map (g n) o := by
  let e : (N : Type u) ≃ₗ[A] (∀ n, (M n : Type u)) :=
    LinearEquiv.ofBijective (LinearMap.pi fun n => (g n).hom) hbij
  have hfac : ∀ n, g n = (LinearEquiv.toModuleIso e).hom ≫
      (ModuleCat.ofHom (LinearMap.proj n) : ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n) :=
    fun n => by ext z; rfl
  intro o o' h
  refine (ConcreteCategory.bijective_of_isIso (O.map (LinearEquiv.toModuleIso e).hom)).1
    (hinj (funext fun n => ?_))
  simpa only [hfac, Functor.map_comp, ConcreteCategory.comp_apply] using congrFun h n

/-- **Lift detection from obstruction groups at one object.** For an object `x` over `Spec A`,
abelian groups `O(M)` functorial in `M`, and obstruction elements `ob(t) ∈ O(Ker t)` vanishing
exactly when `x` lifts across `t`, natural along the kernel maps of morphisms of deformation
situations over the identity which are surjective on thickened rings, with
`O(∏ Mₙ) → ∏ O(Mₙ)` injective: `x` lifts across `t` as soon as it lifts across deformation
situations `sₙ` receiving morphisms from `t` over the identity whose kernel maps identify `Ker t`
with `∏ Ker sₙ`. -/
theorem hasLift_of_obstruction_of_bijective {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S}
    {hA : B.Contains (Spec (.of A))} (hU : MapsIntoAffineOpen S toS) (x : X)
    (hx : p.obj x = algebraOver A B S hS toS hA)
    (O : ModuleCat.{u} A ⥤ AddCommGrpCat.{w'})
    (ob : ∀ t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA),
      O.obj t.kernelObj)
    (hob : ∀ t, AffineObject.HasLift hp (AugmentedSiteRing.affineObject x hx hU) t ↔ ob t = 0)
    (hnat : ∀ (t s : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA))
      (m : DeformationSituation.Hom B S hS p (P := AugmentedSiteRing.affineObject x hx hU)
        (Q := AugmentedSiteRing.affineObject x hx hU) t s),
      m.base = AffineObject.Hom.id _ → Function.Surjective m.top.ringMap →
        ∀ fk : t.kernelObj ⟶ s.kernelObj,
        (∀ z, s.kernelVal (fk z) = m.top.ringMap (t.kernelVal z)) → O.map fk (ob t) = ob s)
    (hinj : ∀ M : ℕ → ModuleCat.{u} A, Function.Injective (fun (z : O.obj
        (ModuleCat.of A (∀ n, (M n : Type u)))) n =>
      O.map (ModuleCat.ofHom (LinearMap.proj n) : ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n) z))
    (t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA))
    (s : ℕ → DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA))
    (m : ∀ n, DeformationSituation.Hom B S hS p (P := AugmentedSiteRing.affineObject x hx hU)
      (Q := AugmentedSiteRing.affineObject x hx hU) t (s n))
    (hbase : ∀ n, (m n).base = AffineObject.Hom.id _)
    (hsurj : ∀ n, Function.Surjective (m n).top.ringMap)
    (fk : ∀ n, t.kernelObj ⟶ (s n).kernelObj)
    (hfk : ∀ n z, (s n).kernelVal (fk n z) = (m n).top.ringMap (t.kernelVal z))
    (hbij : Function.Bijective (fun z n => fk n z))
    (hlift : ∀ n, AffineObject.HasLift hp (AugmentedSiteRing.affineObject x hx hU) (s n)) :
    AffineObject.HasLift hp (AugmentedSiteRing.affineObject x hx hU) t := by
  rw [hob]
  have hinj' : Function.Injective fun (o : O.obj t.kernelObj) (n : ℕ) => O.map (fk n) o :=
    injective_map_of_bijective O (fun n => (s n).kernelObj) fk hbij (hinj _)
  refine hinj' (funext fun n => ?_)
  change O.map (fk n) (ob t) = O.map (fk n) 0
  rw [hnat t (s n) (m n) (hbase n) (hsurj n) (fk n) (hfk n), map_zero]
  exact (hob (s n)).1 (hlift n)

variable (B S hS p hp) in
/-- **Lift detection over products of kernels at bases of finite type, from obstruction groups.**
If every object `x` over the spectrum of a ring `A` with `Spec A → S` locally of finite type and
mapping into an affine open has obstruction groups as in
`Deformation.Artin.hasLift_of_obstruction_of_bijective`, then
`Deformation.Artin.HasLiftOfCountableProductsOfFiniteType` holds. -/
theorem hasLiftOfCountableProductsOfFiniteType_of_obstruction
    (H : ∀ (A : Type u) [CommRing A] (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
      (hU : MapsIntoAffineOpen S toS), LocallyOfFiniteType toS →
      ∀ (x : X) (hx : p.obj x = algebraOver A B S hS toS hA),
      ∃ (O : ModuleCat.{u} A ⥤ AddCommGrpCat.{w'})
        (ob : ∀ t : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA),
          O.obj t.kernelObj),
        (∀ t, AffineObject.HasLift hp (AugmentedSiteRing.affineObject x hx hU) t ↔ ob t = 0) ∧
        (∀ (t s : DeformationSituation B S hS (AugmentedSiteRing.siteAlgebra A toS hA))
          (m : DeformationSituation.Hom B S hS p (P := AugmentedSiteRing.affineObject x hx hU)
            (Q := AugmentedSiteRing.affineObject x hx hU) t s),
          m.base = AffineObject.Hom.id _ → Function.Surjective m.top.ringMap →
        ∀ fk : t.kernelObj ⟶ s.kernelObj,
            (∀ z, s.kernelVal (fk z) = m.top.ringMap (t.kernelVal z)) → O.map fk (ob t) = ob s) ∧
        (∀ M : ℕ → ModuleCat.{u} A, Function.Injective (fun (z : O.obj
            (ModuleCat.of A (∀ n, (M n : Type u)))) n =>
          O.map (ModuleCat.ofHom (LinearMap.proj n) :
            ModuleCat.of A (∀ n, (M n : Type u)) ⟶ M n) z))) :
    HasLiftOfCountableProductsOfFiniteType B S hS p hp := by
  intro A _ toS hA hU hlft x hx t s m hbase hsurj fk hfk hbij hlift
  obtain ⟨O, ob, hob, hnat, hinj⟩ := H A toS hA hU hlft x hx
  exact hasLift_of_obstruction_of_bijective hU x hx O ob hob hnat hinj t s m hbase hsurj fk hfk hbij
    hlift

end Deformation.Artin

end
