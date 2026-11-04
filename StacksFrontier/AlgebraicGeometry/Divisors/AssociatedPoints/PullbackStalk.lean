module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# The stalks of a pullback of modules on a scheme, and its associated points

Let `f : X ⟶ Y` be a morphism of schemes and let `G` be an `𝒪_Y`-module. The stalk of the
pullback `f^* G` at a point `x` of `X` is the base change of the stalk of `G` along the map of
local rings `f^♯_x : 𝒪_{Y, f x} → 𝒪_{X, x}`:

  `(f^* G)_x = 𝒪_{X, x} ⊗_{𝒪_{Y, f x}} G_{f x}`.

This formula, for `AlgebraicGeometry.Scheme.Modules.pullback`, is an `𝒪_{X, x}`-linear
equivalence, and it determines the associated points of `f^* G`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackStalkEquiv` is the linear equivalence above.
* `Stacks.Divisors.baseChangeEquivOfBijective` and `Stacks.Divisors.baseChangeQuotEquiv`
  evaluate a base change `B ⊗_A M` along a bijective, resp. a surjective, ring map: it is `M`
  itself, resp. `M ⧸ (ker • M)`.
* `AlgebraicGeometry.Scheme.Modules.fiberRestrictionStalkQuotEquiv'` and
  `AlgebraicGeometry.Scheme.Modules.fiberRestrictionStalkQuotEquiv`: the stalk of the
  restriction of a module to a scheme-theoretic fibre, at an arbitrary presentation of the point
  and at the point itself.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackStalkEquiv_germ` characterises the equivalence: it
  carries the germ of the adjunction-unit image of a section `s` of `G` to the pure tensor
  `1 ⊗ germ s`. `pullbackStalkEquiv_symm_one_tmul` is the inverse form.
* `Stacks.Divisors.isAssociatedPoint_pullback_iff` is the resulting dictionary: `x` is
  associated to `f^* G` exactly when the maximal ideal of `𝒪_{X, x}` is an associated prime of
  the base-changed stalk.
* `Stacks.Divisors.associatedPoints_pullback_of_iso`: along an isomorphism of schemes the
  associated points of a pullback are the preimage of the associated points,
  `Ass(ψ^* G) = ψ⁻¹(Ass(G))`.
* `Stacks.Divisors.isAssociatedPoint_pullback_iff_quotient` specialises the dictionary to a
  morphism with surjective stalk maps, where the base change is a quotient by the kernel.
* `Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff` is the fibre dictionary: a point of
  the scheme-theoretic fibre of `f : X ⟶ S` over `f x` is associated to the restriction of an
  `𝒪_X`-module `F` to the fibre exactly when the maximal ideal of `𝒪_{X, x}` is an associated
  prime of `F_x ⧸ 𝔪_{S, f x} · F_x`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 02OJ](https://stacks.math.columbia.edu/tag/02OJ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Stacks 0098 for `Scheme.Modules.pullback`.** The stalk at `x` of the pullback `f^* G` of
an `𝒪_Y`-module `G` along a morphism of schemes `f : X ⟶ Y` is the base change of the stalk of
`G` at `f x` along the induced map of local rings, as `𝒪_{X, x}`-modules. -/
noncomputable def pullbackStalkEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    TopCat.Presheaf.stalk (C := Ab.{u}) ((pullback f).obj G).val.presheaf x
        ≃ₗ[X.presheaf.stalk x]
      TensorProduct (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base x)) :=
  (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    f.toLRSHom.toShHom G x).choose

/-- **The characterisation of `pullbackStalkEquiv`.** The germ at `x` of the image of a section
`s` of `G` over `V` under the unit of the pullback–pushforward adjunction goes to the pure
tensor `1 ⊗ germ s`. -/
theorem pullbackStalkEquiv_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) (x : X)
    (V : Y.Opens) (hx : f.base x ∈ V) (s : Γ(G, V)) :
    letI : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    pullbackStalkEquiv f G x
        (TopCat.Presheaf.germ (C := Ab.{u}) ((pullback f).obj G).val.presheaf (f ⁻¹ᵁ V) x hx
          (((pullbackPushforwardAdjunction f).unit.app G).val.app (op V) s)) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)]
        TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf V (f.base x) hx s :=
  (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    f.toLRSHom.toShHom G x).choose_spec V hx s

/-- The inverse form of `pullbackStalkEquiv_germ`: the pure tensor `1 ⊗ germ s` comes from the
germ of the adjunction-unit image of `s`. -/
theorem pullbackStalkEquiv_symm_one_tmul {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) (x : X)
    (V : Y.Opens) (hx : f.base x ∈ V) (s : Γ(G, V)) :
    letI : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    (pullbackStalkEquiv f G x).symm
        ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f.base x)]
          TopCat.Presheaf.germ (C := Ab.{u}) G.val.presheaf V (f.base x) hx s) =
      TopCat.Presheaf.germ (C := Ab.{u}) ((pullback f).obj G).val.presheaf (f ⁻¹ᵁ V) x hx
        (((pullbackPushforwardAdjunction f).unit.app G).val.app (op V) s) :=
  (LinearEquiv.symm_apply_eq _).2 (pullbackStalkEquiv_germ f G x V hx s).symm

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Divisors

/-! ### Transport of the associated-prime condition -/

/-- Being a strict associated prime is invariant under a linear equivalence. -/
theorem isAssociatedPrimeStacks_of_linearEquiv_iff {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (p : Ideal R) :
    IsAssociatedPrimeStacks R M p ↔ IsAssociatedPrimeStacks R N p := by
  have ann (m : M) : (⊥ : Submodule R N).colon (Submodule.span R {e m}) =
      (⊥ : Submodule R M).colon (Submodule.span R {m}) := by
    ext r
    simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← e.map_smul,
      e.map_eq_zero_iff]
  refine ⟨fun ⟨hp, m, hm⟩ => ⟨hp, e m, (ann m).trans hm⟩, fun ⟨hp, n, hn⟩ => ⟨hp, e.symm n, ?_⟩⟩
  rw [← ann, e.apply_symm_apply, hn]

/-- Along a surjective ring map `R → S`, association of an ideal of `S` to an `S`-module is
association of its contraction to the same module read over `R`. -/
theorem isAssociatedPrimeStacks_comap_surjective_iff {R S M : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (hs : Function.Surjective (algebraMap R S)) (q : Ideal S) :
    IsAssociatedPrimeStacks S M q ↔
      IsAssociatedPrimeStacks R M (q.comap (algebraMap R S)) := by
  have ann (m : M) : (⊥ : Submodule R M).colon (Submodule.span R {m}) =
      ((⊥ : Submodule S M).colon (Submodule.span S {m})).comap (algebraMap R S) := by
    ext r
    simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot, Ideal.mem_comap,
      algebraMap_smul]
  refine ⟨fun ⟨hp, m, hm⟩ => ⟨hp.comap _, m, (ann m).trans (congrArg (Ideal.comap _) hm)⟩, ?_⟩
  rintro ⟨hp, m, hm⟩
  refine ⟨?_, m, Ideal.comap_injective_of_surjective _ hs ((ann m).symm.trans hm)⟩
  have h := Ideal.map_isPrime_of_surjective (f := algebraMap R S) hs
    (show RingHom.ker (algebraMap R S) ≤ q.comap (algebraMap R S) from
      fun r hr => by simpa only [Ideal.mem_comap, RingHom.mem_ker.mp hr] using q.zero_mem)
  rwa [Ideal.map_comap_of_surjective _ hs] at h

/-! ### Base change along a bijective or surjective ring map -/

/-- Base change along a bijective ring map does nothing: if `algebraMap A B` is bijective then
`B ⊗[A] M` is `M`, `A`-linearly. -/
noncomputable def baseChangeEquivOfBijective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hbij : Function.Bijective (algebraMap A B))
    (M : Type*) [AddCommGroup M] [Module A M] :
    (B ⊗[A] M) ≃ₗ[A] M :=
  (TensorProduct.congr (AlgEquiv.ofBijective (Algebra.ofId A B) hbij).toLinearEquiv.symm
    (LinearEquiv.refl A M)).trans (TensorProduct.lid A M)

/-- Base change along a surjective ring map is a quotient: if `algebraMap A B` is surjective
then `B ⊗[A] M` is `M ⧸ (ker • M)`, `A`-linearly. -/
noncomputable def baseChangeQuotEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hsurj : Function.Surjective (algebraMap A B))
    (M : Type*) [AddCommGroup M] [Module A M] :
    (B ⊗[A] M) ≃ₗ[A] M ⧸ (RingHom.ker (algebraMap A B) • (⊤ : Submodule A M)) :=
  (TensorProduct.congr
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hsurj).toLinearEquiv.symm
      (LinearEquiv.refl A M)).trans
    (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (algebraMap A B)))

/-- Along a surjective local homomorphism `A → B`, the maximal ideal of `B` is associated to a
`B`-module `P` exactly when that of `A` is associated to any `A`-linear model of `P`. -/
private theorem isAssociatedPrimeStacks_maximalIdeal_iff_of_surjective {A B P N : Type*}
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    [AddCommGroup N] [Module A N] (hs : Function.Surjective (algebraMap A B)) (e : P ≃ₗ[A] N) :
    IsAssociatedPrimeStacks B P (IsLocalRing.maximalIdeal B) ↔
      IsAssociatedPrimeStacks A N (IsLocalRing.maximalIdeal A) := by
  have : IsLocalHom (algebraMap A B) := IsLocalHom.of_surjective _ hs
  rw [isAssociatedPrimeStacks_comap_surjective_iff hs, IsLocalRing.maximalIdeal_comap]
  exact isAssociatedPrimeStacks_of_linearEquiv_iff e _

/-- Along a bijective local homomorphism the maximal ideal is associated to a base change
exactly when it is associated to the original module. -/
theorem isAssociatedPrimeStacks_baseChange_bijective_iff {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hbij : Function.Bijective (algebraMap A B))
    (M : Type*) [AddCommGroup M] [Module A M] :
    IsAssociatedPrimeStacks B (B ⊗[A] M) (IsLocalRing.maximalIdeal B) ↔
      IsAssociatedPrimeStacks A M (IsLocalRing.maximalIdeal A) := by
  exact isAssociatedPrimeStacks_maximalIdeal_iff_of_surjective hbij.surjective
    (baseChangeEquivOfBijective hbij M)

/-- Along a surjective local homomorphism the maximal ideal of the target is associated to a
base change exactly when the maximal ideal of the source is associated to the quotient
`M ⧸ (ker • M)`. -/
theorem isAssociatedPrimeStacks_baseChange_surjective_iff {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hsurj : Function.Surjective (algebraMap A B))
    (M : Type*) [AddCommGroup M] [Module A M] :
    IsAssociatedPrimeStacks B (B ⊗[A] M) (IsLocalRing.maximalIdeal B) ↔
      IsAssociatedPrimeStacks A (M ⧸ (RingHom.ker (algebraMap A B) • (⊤ : Submodule A M)))
        (IsLocalRing.maximalIdeal A) := by
  exact isAssociatedPrimeStacks_maximalIdeal_iff_of_surjective hsurj
    (baseChangeQuotEquiv hsurj M)

/-! ### Associated points of a pullback -/

/-- **The associated-point dictionary for a pullback.** A point `x` of `X` is associated to the
pullback `f^* G` of an `𝒪_Y`-module along `f : X ⟶ Y` exactly when the maximal ideal of
`𝒪_{X, x}` is an associated prime of the base-changed stalk
`𝒪_{X, x} ⊗_{𝒪_{Y, f x}} G_{f x}`. -/
theorem isAssociatedPoint_pullback_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (G : Y.Modules) (x : X) :
    letI : Algebra (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    IsAssociatedPoint ((Scheme.Modules.pullback f).obj G) x ↔
      IsAssociatedPrimeStacks (X.presheaf.stalk x)
        (TensorProduct (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f.base x)))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
  isAssociatedPrimeStacks_of_linearEquiv_iff (Scheme.Modules.pullbackStalkEquiv f G x) _

/-- **The associated points of a pullback along an isomorphism.** For an isomorphism of schemes
`ψ : X ≅ Y` and an `𝒪_Y`-module `G`, the associated points of `ψ^* G` are the preimage of the
associated points of `G`: `Ass(ψ^* G) = ψ⁻¹(Ass(G))`. -/
theorem associatedPoints_pullback_of_iso {X Y : Scheme.{u}} (ψ : X ≅ Y) (G : Y.Modules) :
    associatedPoints ((Scheme.Modules.pullback ψ.hom).obj G) =
      ψ.hom ⁻¹' associatedPoints G := by
  ext x
  have hiso : IsIso (ψ.hom.stalkMap x) :=
    ((isIso_iff_isIso_stalkMap ψ.hom).mp inferInstance).2 x
  have hbij : Function.Bijective (ψ.hom.stalkMap x).hom :=
    ConcreteCategory.bijective_of_isIso _
  let : Algebra (Y.presheaf.stalk (ψ.hom.base x)) (X.presheaf.stalk x) :=
    (ψ.hom.stalkMap x).hom.toAlgebra
  rw [mem_associatedPoints_iff, Set.mem_preimage, mem_associatedPoints_iff,
    isAssociatedPoint_pullback_iff ψ.hom G x]
  exact isAssociatedPrimeStacks_baseChange_bijective_iff hbij _

/-- **The associated-point dictionary for a pullback with surjective stalk maps.** When the
stalk maps of `g : X' ⟶ X` are surjective — a preimmersion, for instance, and in particular the
inclusion of a scheme-theoretic fibre — the base change in
`isAssociatedPoint_pullback_iff` is a quotient: `x'` is associated to `g^* F` exactly when the
maximal ideal of `𝒪_{X, g x'}` is an associated prime of `F_{g x'} ⧸ (ker g^♯_{x'}) · F_{g x'}`. -/
theorem isAssociatedPoint_pullback_iff_quotient {X' X : Scheme.{u}} (g : X' ⟶ X)
    [SurjectiveOnStalks g] (F : X.Modules) (x' : X') :
    IsAssociatedPoint ((Scheme.Modules.pullback g).obj F) x' ↔
      IsAssociatedPrimeStacks (X.presheaf.stalk (g x'))
        ((TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (g x')) ⧸
          (RingHom.ker (g.stalkMap x').hom •
            (⊤ : Submodule (X.presheaf.stalk (g x'))
              (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (g x')))))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (g x'))) := by
  let : Algebra (X.presheaf.stalk (g x')) (X'.presheaf.stalk x') :=
    (g.stalkMap x').hom.toAlgebra
  rw [isAssociatedPoint_pullback_iff g F x']
  exact isAssociatedPrimeStacks_baseChange_surjective_iff (g.stalkMap_surjective x') _

/-! ### The fibre dictionary -/

/-- The kernel of the stalk map of a fibre inclusion is the ideal generated by the maximal ideal
of the base. -/
theorem ker_stalkMap_fiberι_asFiber {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    RingHom.ker ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom =
      Ideal.map (f.stalkMap (f.fiberι (f x) (f.asFiber x))).hom
        (IsLocalRing.maximalIdeal
          (S.presheaf.stalk (f (f.fiberι (f x) (f.asFiber x))))) := by
  obtain ⟨e, he⟩ := AlgebraicGeometry.quotientStalk_bridge f x
  ext b
  rw [RingHom.mem_ker, ← he b, ← map_zero e, e.injective.eq_iff,
    Ideal.Quotient.eq_zero_iff_mem]

/-- **The fibre dictionary, at an arbitrary presentation of the point.** The point `f.asFiber x`
of the scheme-theoretic fibre of `f : X ⟶ S` over `f x` is associated to the restriction of an
`𝒪_X`-module `F` to that fibre exactly when the maximal ideal of `𝒪_{X, z}` is an associated
prime of `F_z ⧸ 𝔪_{S, f z} · F_z`, for any point `z` of `X` presenting `f.asFiber x`. -/
theorem isAssociatedPoint_pullback_fiberι_iff' {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) {z : X} (hz : f.fiberι (f x) (f.asFiber x) = z) :
    IsAssociatedPoint ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x) ↔
      IsAssociatedPrimeStacks (X.presheaf.stalk z)
        ((TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z) ⧸
          (Ideal.map (f.stalkMap z).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f z))) •
            (⊤ : Submodule (X.presheaf.stalk z)
              (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z))))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk z)) := by
  subst hz
  rw [isAssociatedPoint_pullback_iff_quotient (f.fiberι (f x)) F (f.asFiber x),
    ker_stalkMap_fiberι_asFiber f x]

/-- **The fibre dictionary.** The point `f.asFiber x` of the scheme-theoretic fibre of
`f : X ⟶ S` over `f x` is associated to the restriction of an `𝒪_X`-module `F` to that fibre
exactly when the maximal ideal of `𝒪_{X, x}` is an associated prime of
`F_x ⧸ 𝔪_{S, f x} · F_x`. -/
theorem isAssociatedPoint_pullback_fiberι_iff {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) :
    IsAssociatedPoint ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x) ↔
      IsAssociatedPrimeStacks (X.presheaf.stalk x)
        ((TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ⧸
          (Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) •
            (⊤ : Submodule (X.presheaf.stalk x)
              (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x))))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
  isAssociatedPoint_pullback_fiberι_iff' f F x (f.fiberι_asFiber x)

end Stacks.Divisors

end

/-! ### The stalk of the restriction of a module to a scheme-theoretic fibre

Let `f : X ⟶ S` be a morphism of schemes, let `F` be an `𝒪_X`-module and let `x` be a point of
`X`. The stalk at the canonical point of the fibre `X_{f x}` of the restriction of `F` to that
fibre is the fibre of the stalk: `(F|_{X_{f x}})_{x} = F_x / 𝔪_{S, f x} F_x`. This is the stalk
formula of Tag 0098 for the fibre inclusion, whose stalk maps are surjective with kernel the
ideal generated by the maximal ideal of the base. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The stalk of a module restricted to a scheme-theoretic fibre, at an arbitrary presentation
of the point.** For `f : X ⟶ S` and an `𝒪_X`-module `F`, the stalk of the restriction of `F` to
the fibre of `f` over `f x` at the canonical point `f.asFiber x` is `F_z / 𝔪_{S, f z} F_z`, for
any point `z` of `X` presenting `f.asFiber x`. -/
noncomputable def fiberRestrictionStalkQuotEquiv' {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) {z : X} (hz : f.fiberι (f x) (f.asFiber x) = z) :
    letI : Algebra (X.presheaf.stalk z)
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
      (hz ▸ ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom).toAlgebra
    letI : Module (X.presheaf.stalk z) (TopCat.Presheaf.stalk (C := Ab.{u})
        ((pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)) :=
      Module.compHom _ (algebraMap (X.presheaf.stalk z)
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
    TopCat.Presheaf.stalk (C := Ab.{u})
        ((pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)
      ≃ₗ[X.presheaf.stalk z]
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z) ⧸
        (Ideal.map (f.stalkMap z).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f z))) •
          (⊤ : Submodule (X.presheaf.stalk z)
            (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z))) := by
  subst hz
  letI : Algebra (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
    ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom.toAlgebra
  letI : Module (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
  letI : IsScalarTower (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))
      ((f.fiber (f x)).presheaf.stalk (f.asFiber x))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)) :=
    IsScalarTower.of_compHom _ _ _
  refine ((pullbackStalkEquiv (f.fiberι (f x)) F (f.asFiber x)).restrictScalars
      (X.presheaf.stalk (f.fiberι (f x) (f.asFiber x)))).trans
    ((Stacks.Divisors.baseChangeQuotEquiv
      ((f.fiberι (f x)).stalkMap_surjective (f.asFiber x)) _).trans
      (Submodule.quotEquivOfEq _ _ ?_))
  exact congrArg (· • (⊤ : Submodule _ _)) (Stacks.Divisors.ker_stalkMap_fiberι_asFiber f x)

/-- **The stalk of a module restricted to a scheme-theoretic fibre.** For `f : X ⟶ S` and an
`𝒪_X`-module `F`, the stalk of the restriction of `F` to the fibre of `f` over `f x` at the
canonical point `f.asFiber x` is `F_x / 𝔪_{S, f x} F_x`. -/
noncomputable def fiberRestrictionStalkQuotEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) :
    letI : Algebra (X.presheaf.stalk x)
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) :=
      (f.fiberι_asFiber x ▸ ((f.fiberι (f x)).stalkMap (f.asFiber x)).hom).toAlgebra
    letI : Module (X.presheaf.stalk x) (TopCat.Presheaf.stalk (C := Ab.{u})
        ((pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)) :=
      Module.compHom _ (algebraMap (X.presheaf.stalk x)
        ((f.fiber (f x)).presheaf.stalk (f.asFiber x)))
    TopCat.Presheaf.stalk (C := Ab.{u})
        ((pullback (f.fiberι (f x))).obj F).val.presheaf (f.asFiber x)
      ≃ₗ[X.presheaf.stalk x]
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) ⧸
        (Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) •
          (⊤ : Submodule (X.presheaf.stalk x)
            (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x))) :=
  fiberRestrictionStalkQuotEquiv' f F x (f.fiberι_asFiber x)

end AlgebraicGeometry.Scheme.Modules

end
