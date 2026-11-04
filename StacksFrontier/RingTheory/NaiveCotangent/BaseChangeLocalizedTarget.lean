module

public import StacksFrontier.RingTheory.NaiveCotangent.DerivedBaseChange
public import StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget

/-!
# The naive cotangent complex for an arbitrary base change followed by a localization

Let `R → A` and `R → B` be ring maps -- with **no** flatness assumed of either -- and let `C` be
a localization of `B ⊗_R A`.  Then the canonical map of two-term complexes of `C`-modules

`NL_{A/R} ⊗_A C ⟶ NL_{C/B}`

is an isomorphism on `H₀` and a surjection on `H₁`.

This is the ring-level statement behind base change for the naive cotangent complex of a
*cartesian* square of schemes with no flatness hypothesis (Stacks 0FV5): if

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

is cartesian, then the local ring of `X'` at a point `x'` is a localization of
`𝒪_{Y',f'(x')} ⊗_{𝒪_{Y,y}} 𝒪_{X,g'(x')}`, which is the only hypothesis
`NaiveCotangent.isH₀IsoH₁Surj_nlExtensionBaseChangeMap_of_isLocalization_tensor` below needs.

It is the exact analogue of `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_base`
with flatness of `R → B` dropped and the conclusion correspondingly weakened in degree `1`: the
proof factors the comparison through `NL_{(B ⊗_R A)/B} ⊗_{B ⊗_R A} C` in exactly the same way,
and the one factor that is no longer a quasi-isomorphism -- the pushout comparison
`NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}`, which flat base change (Stacks 00S4) would make
one -- is supplied instead by arbitrary base change, Stacks 0FUZ.

## Main definitions

* `NaiveCotangent.IsH₀IsoH₁Surj`: a chain map of two-term complexes is an isomorphism on
  `H₀ = coker d` and a surjection on `H₁ = ker d`.  This is what Stacks 0FUZ delivers and all it
  delivers: injectivity on `H₁` is exactly the half that fails for a non-flat base change.

## Main results

* `NaiveCotangent.IsQuasiIso.isH₀IsoH₁Surj`, `NaiveCotangent.IsH₀IsoH₁Surj.comp`,
  `NaiveCotangent.IsH₀IsoH₁Surj.of_comp_right` and
  `NaiveCotangent.IsH₀IsoH₁Surj.baseChange`: the condition is weaker than quasi-isomorphy, is
  stable under composition, can be cancelled on the right against a quasi-isomorphism, and is
  preserved by a flat base change.  These are the four closure properties the factorisation of
  the comparison needs, and each is the corresponding property of
  `NaiveCotangent.IsQuasiIso` with the degree-`1` injectivity removed.
* `NaiveCotangent.IsH₀IsoH₁Surj.exists_of_d_eq_zero`,
  `NaiveCotangent.IsH₀IsoH₁Surj.exists_d_eq` and
  `NaiveCotangent.IsH₀IsoH₁Surj.exists_add_d_eq`: the condition read back elementwise, as the
  three surviving clauses of `NaiveCotangent.IsQuasiIso.eq_zero_of_d_eq_zero` and its
  companions.
* `NaiveCotangent.surjective_onH₁_of_exists`,
  `NaiveCotangent.injective_onH₀_of_exists_d_eq` and
  `NaiveCotangent.surjective_onH₀_of_exists_add_d_eq`: the three elementwise criteria, in which
  Stacks 0FUZ states its conclusion.
* `NaiveCotangent.isH₀IsoH₁Surj_nlExtensionBaseChangeMap_canHom`: **Stacks 0FUZ** in the
  `NaiveCotangent.nlExtensionBaseChangeMap` packaging: for arbitrary `R → B` the canonical map
  `NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}` is an isomorphism on `H₀` and a surjection on
  `H₁`.
* `NaiveCotangent.isH₀IsoH₁Surj_nlExtensionBaseChangeMap_of_isLocalization_tensor`: **the
  comparison `NL_{A/R} ⊗_A C ⟶ NL_{C/B}` is an isomorphism on `H₀` and a surjection on `H₁`**
  when `C` is a localization of `B ⊗_R A`.

## Implementation notes

`NaiveCotangent.flatBaseLocalizedHom` and
`NaiveCotangent.nlExtensionBaseChangeMap_flatBaseLocalizedHom_comp_cancel` are reused verbatim
from `StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget`: neither mentions flatness,
which enters that file only in the quasi-isomorphy of the pushout comparison, so the
factorisation of the comparison is shared between the flat and the general statement and is not
written twice.  `NaiveCotangent.FlatBaseChangeNL.canHom` is likewise flatness-free -- it is by
definition the `Algebra.Generators.defaultHom` between the two canonical presentations, which is
the morphism of extensions Stacks 0FUZ states its conclusion for.

`Algebra.TensorProduct.rightAlgebra`, the `A`-algebra structure on `B ⊗_R A`, is a local
instance here as it is in `StacksFrontier.RingTheory.NaiveCotangent.FlatBaseLocalizedTarget`; it is
what makes `B ⊗_R A` a target for base change of `NL_{A/R}`, and it is the structure Stacks 0FUZ
is stated against.

## References

* [Stacks Project, Tag 0FUZ](https://stacks.math.columbia.edu/tag/0FUZ), the naive cotangent
  complex and arbitrary base change.
* [Stacks Project, Tag 00S7](https://stacks.math.columbia.edu/tag/00S7), the naive cotangent
  complex and localization of the target.
* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5), base change for the
  naive cotangent complex of a morphism of schemes, which consumes this statement at every
  point of a cartesian square.
-/

@[expose] public section

namespace NaiveCotangent

open Algebra TensorProduct

noncomputable section

/-!
## Isomorphism on `H₀` and surjection on `H₁`
-/

section Predicate

variable {S : Type*} [CommRing S] {A B D : TwoTerm S}

/-- **A chain map of two-term complexes which is an isomorphism on `H₀` and a surjection on
`H₁`.**  This is the conclusion of arbitrary base change for the naive cotangent complex
(Stacks 0FUZ): the degree-`1` half is a surjection and not a bijection, injectivity on the
kernel being exactly what flatness of the base change would buy. -/
def IsH₀IsoH₁Surj (f : ChainMap A B) : Prop :=
  Function.Surjective f.onH₁ ∧ Function.Bijective f.onH₀

/-- A quasi-isomorphism is an isomorphism on `H₀` and a surjection on `H₁`. -/
theorem IsQuasiIso.isH₀IsoH₁Surj {f : ChainMap A B} (hf : IsQuasiIso f) : IsH₀IsoH₁Surj f :=
  ⟨hf.1.2, hf.2⟩

/-- The map induced on `H₁` by a composite is the composite of the induced maps. -/
private theorem onH₁_comp_coe {g : ChainMap B D} {f : ChainMap A B} :
    ⇑(g.comp f).onH₁ = g.onH₁ ∘ f.onH₁ :=
  congrArg DFunLike.coe (ChainMap.onH₁_comp g f)

/-- The map induced on `H₀` by a composite is the composite of the induced maps. -/
private theorem onH₀_comp_coe {g : ChainMap B D} {f : ChainMap A B} :
    ⇑(g.comp f).onH₀ = g.onH₀ ∘ f.onH₀ :=
  congrArg DFunLike.coe (ChainMap.onH₀_comp g f)

/-- The condition is stable under composition: a composite of surjections is a surjection and a
composite of bijections is a bijection. -/
theorem IsH₀IsoH₁Surj.comp {g : ChainMap B D} {f : ChainMap A B} (hg : IsH₀IsoH₁Surj g)
    (hf : IsH₀IsoH₁Surj f) : IsH₀IsoH₁Surj (g.comp f) := by
  rw [IsH₀IsoH₁Surj, onH₁_comp_coe, onH₀_comp_coe]
  exact ⟨hg.1.comp hf.1, hg.2.comp hf.2⟩

/-- **Cancelling a quasi-isomorphism on the right.**  If `f` is a quasi-isomorphism and `g ∘ f`
is an isomorphism on `H₀` and a surjection on `H₁`, then so is `g`.

This is `NaiveCotangent.IsQuasiIso.of_comp_right` with the degree-`1` conclusion weakened: a
surjection that factors through `f.onH₁` has a surjective left factor, and a bijection whose
right factor is a bijection has a bijective left factor. -/
theorem IsH₀IsoH₁Surj.of_comp_right {f : ChainMap A B} {g : ChainMap B D} (hf : IsQuasiIso f)
    (hgf : IsH₀IsoH₁Surj (g.comp f)) : IsH₀IsoH₁Surj g := by
  rw [IsH₀IsoH₁Surj, onH₁_comp_coe, onH₀_comp_coe] at hgf
  exact ⟨hgf.1.of_comp, (Function.Bijective.of_comp_iff g.onH₀ hf.2).mp hgf.2⟩

/-- **Surjectivity on the kernel of the differential**, read off the surjection on `H₁`.  This
is `NaiveCotangent.IsQuasiIso.exists_of_d_eq_zero` for the weaker condition. -/
theorem IsH₀IsoH₁Surj.exists_of_d_eq_zero {f : ChainMap A B} (hf : IsH₀IsoH₁Surj f) (m : B.X₁)
    (h1 : B.d m = 0) : ∃ n : A.X₁, A.d n = 0 ∧ f.f₁ n = m := by
  obtain ⟨n, hn⟩ := hf.1 ⟨m, h1⟩
  exact ⟨n.1, n.2, (LinearMap.coe_restrict_apply _ _).symm.trans (congrArg Subtype.val hn)⟩

/-- **Injectivity on the cokernel of the differential**, read off the isomorphism on `H₀`.  This
is `NaiveCotangent.IsQuasiIso.exists_d_eq` for the weaker condition. -/
theorem IsH₀IsoH₁Surj.exists_d_eq {f : ChainMap A B} (hf : IsH₀IsoH₁Surj f) (n : A.X₀)
    (h : ∃ m : B.X₁, B.d m = f.f₀ n) : ∃ z : A.X₁, A.d z = n := by
  have h0 : f.onH₀ (Submodule.Quotient.mk n) = 0 :=
    (Submodule.mapQ_apply _ _ _ n).trans ((Submodule.Quotient.mk_eq_zero _).mpr h)
  exact (Submodule.Quotient.mk_eq_zero _).mp (hf.2.1 (h0.trans (map_zero f.onH₀).symm))

/-- **Surjectivity on the cokernel of the differential**, read off the isomorphism on `H₀`.  This
is `NaiveCotangent.IsQuasiIso.exists_add_d_eq` for the weaker condition. -/
theorem IsH₀IsoH₁Surj.exists_add_d_eq {f : ChainMap A B} (hf : IsH₀IsoH₁Surj f) (n : B.X₀) :
    ∃ (m : A.X₀) (z : B.X₁), f.f₀ m + B.d z = n := by
  obtain ⟨t, ht⟩ := hf.2.2 (Submodule.Quotient.mk n)
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp ((Submodule.mapQ_apply _ _ _ m).symm.trans ht)
  exact ⟨m, -z, by rw [map_neg, hz]; abel⟩

end Predicate

/-!
## The three elementwise criteria
-/

section Elementwise

variable {S : Type*} [CommRing S] {A B : TwoTerm S}

/-- **Surjectivity on `H₁` from the elementwise statement.**  If every cycle of the target is the
image of a cycle of the source, the map induced on `H₁ = ker d` is surjective. -/
theorem surjective_onH₁_of_exists (f : ChainMap A B)
    (h : ∀ y : B.X₁, B.d y = 0 → ∃ x : A.X₁, A.d x = 0 ∧ f.f₁ x = y) :
    Function.Surjective f.onH₁ := by
  intro y
  have hy : (y : B.X₁) ∈ LinearMap.ker B.d := y.2
  obtain ⟨x, hx, hfx⟩ := h (y : B.X₁) (LinearMap.mem_ker.mp hy)
  exact ⟨⟨x, LinearMap.mem_ker.mpr hx⟩,
    Subtype.ext (by simpa only [onH₁_apply_coe] using hfx)⟩

/-- **Injectivity on `H₀` from the elementwise statement.**  If a degree-`0` element of the
source whose image bounds already bounds, the map induced on `H₀ = coker d` is injective. -/
theorem injective_onH₀_of_exists_d_eq (f : ChainMap A B)
    (h : ∀ x : A.X₀, (∃ m : B.X₁, B.d m = f.f₀ x) → ∃ z : A.X₁, A.d z = x) :
    Function.Injective f.onH₀ := by
  refine (injective_iff_map_eq_zero f.onH₀).mpr fun x hx => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [onH₀_mk] at hx
  obtain ⟨z, hz⟩ := h x (LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hx))
  exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range.mpr ⟨z, hz⟩)

/-- **Surjectivity on `H₀` from the elementwise statement.**  If every degree-`0` element of the
target is the image of one of the source up to a boundary, the map induced on `H₀ = coker d` is
surjective. -/
theorem surjective_onH₀_of_exists_add_d_eq (f : ChainMap A B)
    (h : ∀ y : B.X₀, ∃ (x : A.X₀) (z : B.X₁), f.f₀ x + B.d z = y) :
    Function.Surjective f.onH₀ := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, z, hxz⟩ := h y
  refine ⟨Submodule.Quotient.mk x, ?_⟩
  rw [onH₀_mk, Submodule.Quotient.eq]
  exact ⟨-z, by rw [map_neg, ← hxz]; abel⟩

end Elementwise

/-!
## Flat base change of the condition
-/

section BaseChange

variable {S : Type*} [CommRing S] {A B : TwoTerm S} (T : Type*) [CommRing T] [Algebra S T]

/-- **A flat base change preserves the condition.**  The degree-`0` half is the degree-`0` half
of `NaiveCotangent.IsQuasiIso.baseChange` verbatim and needs no flatness; the degree-`1` half
needs flatness only to know that the kernel of the base changed differential is the base change
of the kernel, after which surjectivity base changes because the tensor product is right
exact. -/
theorem IsH₀IsoH₁Surj.baseChange [Module.Flat S T] {f : ChainMap A B} (hf : IsH₀IsoH₁Surj f) :
    IsH₀IsoH₁Surj (f.baseChange T) := by
  refine ⟨surjective_onH₁_of_exists _ fun y hy => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := LinearMap.mem_range.mp
      ((ker_baseChange_eq_range_baseChange_subtype T B).le
        (show y ∈ LinearMap.ker (LinearMap.baseChange T B.d) from hy))
    obtain ⟨w, rfl⟩ := surjective_baseChange T hf.1 v
    refine ⟨LinearMap.baseChange T (H₁ A).subtype w, ?_, ?_⟩
    · exact (ker_baseChange_eq_range_baseChange_subtype T A).ge (LinearMap.mem_range.mpr ⟨w, rfl⟩)
    · exact (baseChange_f₁_baseChange_subtype T f w).trans hv
  · exact bijective_onH₀_of_surjective_square (T ⊗[S] H₀ A) (T ⊗[S] H₀ B) (f.baseChange T)
      (LinearMap.baseChange T (LinearMap.range A.d).mkQ)
      (LinearMap.baseChange T (LinearMap.range B.d).mkQ)
      (LinearMap.baseChange T f.onH₀)
      (surjective_baseChange T (Submodule.mkQ_surjective _))
      (ker_baseChange_mkQ T A) (ker_baseChange_mkQ T B)
      (baseChange_mkQ_comp_baseChange_f₀ T f) (bijective_baseChange T hf.2)

end BaseChange

/-!
## Homotopy invariance
-/

section Congr

variable {R S T R' : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing R'] [Algebra R S]
  [Algebra S T] [Algebra R R'] [Algebra R' T] [Algebra R T] [IsScalarTower R R' T]
  [IsScalarTower R S T]

/-- The condition does not depend on the morphism of extensions chosen: homotopic chain maps
induce the same maps on `H₁` and on `H₀`. -/
theorem isH₀IsoH₁Surj_nlExtensionBaseChangeMap_congr {P : Extension R S} {Q : Extension R' T}
    (h h' : P.Hom Q) (hq : IsH₀IsoH₁Surj (nlExtensionBaseChangeMap (T := T) h')) :
    IsH₀IsoH₁Surj (nlExtensionBaseChangeMap (T := T) h) := by
  refine ⟨?_, ?_⟩
  · rw [ChainMap.onH₁_eq_of_homotopic (homotopic_nlExtensionBaseChangeMap (T := T) h h')]
    exact hq.1
  · rw [ChainMap.onH₀_eq_of_homotopic (homotopic_nlExtensionBaseChangeMap (T := T) h h')]
    exact hq.2

end Congr

/-!
## Arbitrary base change and a localization of the target
-/

section BaseLocalizedTarget

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- **Stacks 0FUZ** in the packaging of `NaiveCotangent.nlExtensionBaseChangeMap`: for an
arbitrary ring map `R → B` the canonical map
`NL_{A/R} ⊗_A (B ⊗_R A) ⟶ NL_{(B ⊗_R A)/B}` is an isomorphism on `H₀` and a surjection on `H₁`.

The three elementwise conclusions of
`NaiveCotangent.naiveCotangentComplex_baseChange_homology` for the canonical presentations are
exactly the hypotheses of the three criteria above; the morphism of extensions it states them
for is the `Algebra.Generators.defaultHom` between the two canonical presentations, which is
`NaiveCotangent.FlatBaseChangeNL.canHom` by definition. -/
theorem isH₀IsoH₁Surj_nlExtensionBaseChangeMap_canHom :
    IsH₀IsoH₁Surj (nlExtensionBaseChangeMap (T := B ⊗[R] A)
      (FlatBaseChangeNL.canHom (R := R) (S := A) B)) := by
  have h := naiveCotangentComplex_baseChange_homology (R := R) (S := A) (T := B)
    (Algebra.Generators.self R A)
  refine ⟨surjective_onH₁_of_exists _ fun y hy => h.2.2.2.2.2.2.2 y hy,
    injective_onH₀_of_exists_d_eq _ fun x hx => ?_,
    surjective_onH₀_of_exists_add_d_eq _ fun y => ?_⟩
  · exact LinearMap.mem_range.mp
      ((h.2.2.2.2.2.2.1 x).mp (LinearMap.mem_range.mpr hx))
  · obtain ⟨x, hx⟩ := h.2.2.2.2.2.1 y
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hx
    refine ⟨x, z, ?_⟩
    have hz' : (nlOfExtension (Generators.self B (B ⊗[R] A)).toExtension).d z =
        y - (nlExtensionBaseChangeMap (T := B ⊗[R] A)
          (FlatBaseChangeNL.canHom (R := R) (S := A) B)).f₀ x := hz
    rw [hz']
    abel

variable {C : Type u} [CommRing C] [Algebra R C] [Algebra A C] [Algebra B C]
  [Algebra (B ⊗[R] A) C] [IsScalarTower R A C] [IsScalarTower R B C]
  [IsScalarTower A (B ⊗[R] A) C] [IsScalarTower B (B ⊗[R] A) C]

/-- **The naive cotangent complex for an arbitrary base change followed by a localization.**  Let
`R → A` and `R → B` be ring maps and let `C` be a localization of `B ⊗_R A` at a multiplicative
subset, compatibly with the maps out of `A` and `B`.  Then the canonical map of two-term
complexes of `C`-modules

`NL_{A/R} ⊗_A C ⟶ NL_{C/B}`

is an isomorphism on `H₀` and a surjection on `H₁`.  The statement holds for every morphism of
extensions `h` inducing it: any two are homotopic, so the maps induced on `H₁` and `H₀` agree.

This declaration carries **no** `@[stacks]` attribute: it is the ring-level input to base change
for the naive cotangent complex of a morphism of schemes (Stacks 0FV5), not that statement,
which also requires the identification of the stalks of a cartesian square. -/
theorem isH₀IsoH₁Surj_nlExtensionBaseChangeMap_of_isLocalization_tensor
    (M : Submonoid (B ⊗[R] A)) [IsLocalization M C]
    (h : ((Generators.self R A).toExtension).Hom ((Generators.self B C).toExtension)) :
    IsH₀IsoH₁Surj (nlExtensionBaseChangeMap (T := C) h) := by
  have : Module.Flat (B ⊗[R] A) C := IsLocalization.flat C M
  refine isH₀IsoH₁Surj_nlExtensionBaseChangeMap_congr h
    (flatBaseLocalizedHom (R := R) (A := A) (B := B) (C := C)) ?_
  refine IsH₀IsoH₁Surj.of_comp_right
    (isQuasiIso_cancelBaseChangeChainMap (D := B ⊗[R] A) (C := C)
      ((Generators.self R A).toExtension)) ?_
  rw [nlExtensionBaseChangeMap_flatBaseLocalizedHom_comp_cancel]
  exact ((isQuasiIso_nlExtensionBaseChangeMap_of_isLocalization M _).isH₀IsoH₁Surj).comp
    (isH₀IsoH₁Surj_nlExtensionBaseChangeMap_canHom.baseChange C)

end BaseLocalizedTarget

end

end NaiveCotangent

end
