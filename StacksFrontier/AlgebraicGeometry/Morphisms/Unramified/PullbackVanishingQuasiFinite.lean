module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Numerical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of `i^* Ω_{X/Y}` makes `f` unramified, hence quasi-finite, along `i`

Let `i : Z ⟶ X` be an immersion — more generally a morphism surjective on stalks — and let
`f : X ⟶ Y` be locally of finite type. This file shows that if the pullback `i^* Ω_{X/Y}` of the
sheaf of relative differentials is a zero object then `f` is unramified, and therefore
quasi-finite, at every point of the image of `i`.

The chain has three links.

*From the sheaf to the stalk.* The stalk functor on `𝒪_Z`-modules is a left adjoint
(`Stacks.ModuleSkyscraper.isLeftAdjoint_modulesStalkFunctor`), hence preserves zero morphisms,
so the stalk of `i^* Ω_{X/Y}` at `z` vanishes; and that stalk is
`𝒪_{Z,z} ⊗_{𝒪_{X,i z}} Ω_{X/Y,i z}` by [Stacks, Tag 0098]
(`Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv`).

*Nakayama.* The stalk map `𝒪_{X,i z} ⟶ 𝒪_{Z,z}` of a morphism surjective on stalks is a
surjective local homomorphism of local rings, so it induces an isomorphism on residue fields;
tensoring down along it therefore exhibits `κ(i z) ⊗_{𝒪_{X,i z}} Ω_{X/Y,i z}` as a quotient of
the vanishing module above. Since `Ω_{X/Y,i z}` is a finite `𝒪_{X,i z}`-module
([Stacks, Tag 01V2], `Stacks.RelativeDifferentialStalkMap.finite_relativeDifferentialStalk`),
Mathlib's `IsLocalRing.subsingleton_tensorProduct` concludes `Ω_{X/Y,i z} = 0`.

*Unramified, then quasi-finite.* Vanishing of the differentials stalk is unramifiedness at the
point, which is the implication (3) ⟹ (1) of [Stacks, Tag 02GF], already available as
`AlgebraicGeometry.unramifiedAt_of_subsingleton_relativeDifferentialStalk`. Unramifiedness at a
point is quasi-finiteness there by [Stacks, Tag 02V5], available as
`AlgebraicGeometry.quasiFiniteAt_of_unramifiedAt`.

## Main results

* `Stacks.UnramifiedAlongImmersion.subsingleton_of_subsingleton_tensorProduct_of_surjective` —
  Nakayama along a surjective local homomorphism: if `A ⟶ B` is a surjective local
  homomorphism of local rings and `M` is a finite `A`-module with `B ⊗_A M = 0`, then `M = 0`.
* `Stacks.UnramifiedAlongImmersion.subsingleton_relativeDifferentialStalk_of_isZero_pullback` —
  `i^* Ω_{X/Y} = 0` forces `Ω_{X/Y,i z} = 0` for every `z`.
* `Stacks.UnramifiedAlongImmersion.unramifiedAt_of_isZero_pullback_relativeDifferentials` and
  `Stacks.UnramifiedAlongImmersion.quasiFiniteAt_of_isZero_pullback_relativeDifferentials` —
  **the conclusions**: `f` is unramified, and quasi-finite, at every point of the image of `i`.

## What is and is not proved

Everything here is proved outright; no hypothesis of any Stacks result is carried.

## Implementation notes

The first result is pure commutative algebra and belongs in that layer of the library rather
than here; it is stated in this file because nothing else needs it yet. Its `Module A B`
argument is an ordinary instance argument together with the compatibility `a • b = φ a * b`,
so that it applies to the module structure `ModuleCat.extendScalars` installs, which is
`Module.compHom` of the stalk map rather than `Algebra.toModule` of an algebra instance.

**No `@[stacks 02GF]` and no `@[stacks 02V5]` attribute is placed.** Tag 02GF is the
list of equivalent conditions, which the library already proves as
`AlgebraicGeometry.unramifiedAt_tfae`, and this file only *applies* one of its implications.
Tag 02V5 is carried where it is proved, in
`StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties`: its pointwise claim by
`AlgebraicGeometry.quasiFiniteAt_of_unramifiedAt` and its global consequence by
`AlgebraicGeometry.locallyOfFiniteType_of_unramified` together with
`AlgebraicGeometry.locallyQuasiFinite_of_unramified`. This file only applies the pointwise
claim.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 02V5](https://stacks.math.columbia.edu/tag/02V5)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01V2](https://stacks.math.columbia.edu/tag/01V2)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SmoothAtJacobian (relativeDifferentialStalk relativeDifferentialStalkModule)
open scoped TensorProduct

universe u

namespace Stacks.UnramifiedAlongImmersion

/-! ### Nakayama along a surjective local homomorphism -/

/-- **Nakayama along a surjective local homomorphism.** Let `φ : A →+* B` be a surjective local
homomorphism of local rings, and let `M` be a finite `A`-module. If `B ⊗_A M` has at most one
element then so does `M`.

Surjectivity of `φ` makes the induced map on residue fields surjective, and it is injective
because its source is a field; so it is a ring isomorphism, and composing the residue map of `B`
with its inverse gives a surjective `A`-linear map `B ⟶ κ(A)`. Tensoring that with `M` presents
`κ(A) ⊗_A M` as a quotient of `B ⊗_A M`, hence trivial, and Nakayama's lemma in the form
`IsLocalRing.subsingleton_tensorProduct` finishes.

The `A`-module structure on `B` is an instance argument constrained by `hsmul` rather than
derived from an `Algebra A B` instance, so that the result applies verbatim to the module
structure `ModuleCat.extendScalars` installs. -/
@[ega "0 1.7.5" "Nakayama step"]
public theorem subsingleton_of_subsingleton_tensorProduct_of_surjective
    {A B M : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module A B] (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ)
    (hsmul : ∀ (a : A) (b : B), a • b = φ a * b)
    (h : Subsingleton (B ⊗[A] M)) : Subsingleton M := by
  have hsurj : Function.Surjective (IsLocalRing.ResidueField.map φ) := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨IsLocalRing.residue A a, IsLocalRing.ResidueField.map_residue φ a⟩
  let e : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField B :=
    RingEquiv.ofBijective _ ⟨(IsLocalRing.ResidueField.map φ).injective, hsurj⟩
  let ψ : B →ₗ[A] IsLocalRing.ResidueField A :=
    { toFun := fun b => e.symm (IsLocalRing.residue B b)
      map_add' := fun x y => by simp
      map_smul' := fun a b => by
        have h1 : IsLocalRing.residue B (a • b) =
            e (IsLocalRing.residue A a) * IsLocalRing.residue B b := by
          rw [hsmul, map_mul]
          exact congrArg (fun t => t * IsLocalRing.residue B b)
            (IsLocalRing.ResidueField.map_residue φ a).symm
        show e.symm (IsLocalRing.residue B (a • b)) = a • e.symm (IsLocalRing.residue B b)
        rw [h1, map_mul, e.symm_apply_apply, Algebra.smul_def]
        rfl }
  have hψ : Function.Surjective ψ := fun y => by
    obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (e y)
    refine ⟨b, ?_⟩
    show e.symm (IsLocalRing.residue B b) = y
    rw [hb, e.symm_apply_apply]
  have hmap : Function.Surjective (TensorProduct.map ψ (LinearMap.id (R := A) (M := M))) :=
    TensorProduct.map_surjective hψ Function.surjective_id
  exact IsLocalRing.subsingleton_tensorProduct.mp hmap.subsingleton

/-! ### Vanishing of the pullback of the relative differentials -/

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) [SurjectiveOnStalks i] (f : X ⟶ Y)
  [LocallyOfFiniteType f]

/-- **`i^* Ω_{X/Y} = 0` forces `Ω_{X/Y,i z} = 0`.** The stalk functor on `𝒪_Z`-modules preserves
zero objects, so the stalk at `z` of the pullback vanishes; by [Stacks, Tag 0098] that stalk is
`𝒪_{Z,z} ⊗_{𝒪_{X,i z}} Ω_{X/Y,i z}`, and the stalk map `𝒪_{X,i z} ⟶ 𝒪_{Z,z}` is a surjective
local homomorphism, so Nakayama along it gives the conclusion. Finiteness of the differentials
stalk is [Stacks, Tag 01V2]. -/
public theorem subsingleton_relativeDifferentialStalk_of_isZero_pullback
    (hzero : IsZero ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials f)))
    (z : Z) : Subsingleton (relativeDifferentialStalk f (i.base z)) := by
  have h0 : Subsingleton (Stacks.ModuleSkyscraper.stalkObj
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials f)).val z) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (Functor.map_isZero (Stacks.ModuleSkyscraper.modulesStalkFunctor Z z) hzero)
  have h1 : Subsingleton ((ModuleCat.extendScalars (Scheme.Hom.stalkMap i z).hom).obj
      (Stacks.ModuleSkyscraper.stalkObj (Scheme.Hom.relativeDifferentials f).val
        (i.base z))) :=
    @Equiv.subsingleton _ _ (Stacks.ModuleSkyscraper.pullbackStalkLinearEquiv i z
      (Scheme.Hom.relativeDifferentials f)).toEquiv h0
  exact @subsingleton_of_subsingleton_tensorProduct_of_surjective _ _ _ _ _ _ _ _
    (relativeDifferentialStalkModule f (i.base z))
    (Stacks.RelativeDifferentialStalkMap.finite_relativeDifferentialStalk f (i.base z))
    (Module.compHom (Z.presheaf.stalk z) (Scheme.Hom.stalkMap i z).hom)
    (Scheme.Hom.stalkMap i z).hom _ (i.stalkMap_surjective z) (fun _ _ => rfl) h1

/-- **`i^* Ω_{X/Y} = 0` makes `f` unramified at every point of the image of `i`.** The previous
result gives the vanishing of the differentials stalk, and that is unramifiedness at the point
by the implication (3) ⟹ (1) of [Stacks, Tag 02GF]. -/
@[sga "3 XI 1.3" "(i)(c)⇒(a)"]
public theorem unramifiedAt_of_isZero_pullback_relativeDifferentials
    (hzero : IsZero ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials f)))
    (z : Z) : UnramifiedAt f (i.base z) :=
  unramifiedAt_of_subsingleton_relativeDifferentialStalk f
    (subsingleton_relativeDifferentialStalk_of_isZero_pullback i f hzero z)

/-- **`i^* Ω_{X/Y} = 0` makes `f` quasi-finite at every point of the image of `i`.** This is the
previous result followed by `AlgebraicGeometry.quasiFiniteAt_of_unramifiedAt`
([Stacks, Tag 02V5]). -/
public theorem quasiFiniteAt_of_isZero_pullback_relativeDifferentials
    (hzero : IsZero ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials f)))
    (z : Z) : f.QuasiFiniteAt (i.base z) :=
  (AlgebraicGeometry.quasiFiniteAt_of_unramifiedAt f
    (unramifiedAt_of_isZero_pullback_relativeDifferentials i f hzero z)).2

end Stacks.UnramifiedAlongImmersion

end
