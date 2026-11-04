module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# The pullback of a meromorphic section, in the generic-stalk model

Let `p : X ⟶ Y` be a morphism of schemes and let `L` be an `𝒪_Y`-module. For a point `x` of `X`
the stalk of the pullback at `x` is the base change of the stalk of `L` at `p(x)` along the
germ map `𝒪_{Y, p x} → 𝒪_{X, x}` ([Stacks, Tag 0098](https://stacks.math.columbia.edu/tag/0098)),
and the element `1 ⊗ m` of that base change is the **pullback of a stalk element**
`m ∈ L_{p x}`. This file constructs that map, `Stacks.Divisors.pullbackStalk`, and the three
facts about it that the order-of-vanishing calculus of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder` needs:

* it carries germs to germs, the germ of `m` over `V` going to the germ of the pullback of a
  section over `p⁻¹V`;
* it is semilinear over the germ map `𝒪_{Y, p x} → 𝒪_{X, x}`;
* it carries a stalk basis to a stalk basis, because the base change of a free rank-one module
  is free of rank one.

In the generic-stalk model a meromorphic section of `L` on an integral scheme is an element of
the stalk `L_{η_Y}` at the generic point (see the module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder`). A dominant morphism of integral schemes
takes `η_X` to `η_Y`, so `pullbackStalk` at `x = η_X`, transported along that equality, is the
**pullback of a meromorphic section** `Stacks.Divisors.genericStalkPullback`; it is semilinear
over the extension of function fields `AlgebraicGeometry.dominantFunctionFieldMap p`.

The result these are for is the last of them, `Stacks.Divisors.IsCoordinateAt.pullback`: if the
rational function `a` expresses the meromorphic section `s` in terms of a basis of `L_{p x}`,
then its image in `R(X)` expresses `p^*s` in terms of a basis of `(p^*L)_x`. That is the
coordinate identification the proof of
[Stacks, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST) performs when it compares
`div_{p^*L}(p^*s)` with `div_L(s)` fibre by fibre.

## Main definitions

* `Stacks.Divisors.pullbackStalkBaseChange` — the chosen base-change equivalence
  `(p^*L)_x ≃ 𝒪_{X, x} ⊗_{𝒪_{Y, p x}} L_{p x}` of Stacks 0098, at the `Scheme.Modules`
  spelling.
* `Stacks.Divisors.pullbackStalk` — `m ↦ 1 ⊗ m`, the map `L_{p x} → (p^*L)_x`.
* `Stacks.Divisors.pullbackStalkAt` — the same map with the image point named through an
  equality `p(x) = z`, so that the generic-point case needs no transport of its own.
* `Stacks.Divisors.genericStalkPullback` — the pullback `L_{η_Y} → (p^*L)_{η_X}` of a
  meromorphic section along a dominant morphism of integral schemes.

## Main results

* `Stacks.Divisors.bijective_smul_one_tmul` — base change of a free rank-one module is free of
  rank one, in the shape `Stacks.Divisors.IsStalkBasis` is stated in.
* `Stacks.Divisors.pullbackStalk_germ`, `Stacks.Divisors.pullbackStalk_smul` and
  `Stacks.Divisors.IsStalkBasis.pullbackStalk` — the three facts listed above.
* `Stacks.Divisors.IsTrivializedNear.pullback` — the pullback of a module trivialized near `p(x)`
  is trivialized near `x`.
* `Stacks.Divisors.genericStalkPullback_smul` — semilinearity over
  `AlgebraicGeometry.dominantFunctionFieldMap`.
* `Stacks.Divisors.toGenericStalk_pullbackStalk` — the pullback of stalk elements commutes with
  passage to the generic stalk.
* `Stacks.Divisors.IsCoordinateAt.pullback` — a coordinate of `s` at `p(x)` pulls back to a
  coordinate of `p^*s` at `x`.

## What this is not

No declaration here carries a Stacks attribute. Stacks 0098 is carried by
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`, which is what
`Stacks.Divisors.pullbackStalkBaseChange` chooses an equivalence from; the rest is the
bookkeeping that Tag 02ST's proof needs and is not itself a tagged statement.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 0CC1](https://stacks.math.columbia.edu/tag/0CC1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

universe u

namespace Stacks.Divisors

/-! ### Base change of a free rank-one module -/

/-- **Base change of a free rank-one module is free of rank one.** If multiplication by `m` is a
bijection `R → N` then multiplication by `1 ⊗ m` is a bijection `S → S ⊗_R N`: the first
bijection is an `R`-linear equivalence `R ≃ N`, so `S ⊗_R N ≃ S ⊗_R R ≃ S` as `S`-modules, and
that composite carries `s · (1 ⊗ m)` to `s`.

This is the form `Stacks.Divisors.IsStalkBasis` is stated in, and it is what makes the pullback
of a stalk basis a stalk basis. -/
theorem bijective_smul_one_tmul {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] {m : N} (hm : Function.Bijective fun r : R => r • m) :
    Function.Bijective fun s : S => s • ((1 : S) ⊗ₜ[R] m) := by
  let eR : R ≃ₗ[R] N := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R N m) hm
  let φ : S ⊗[R] N ≃ₗ[S] S :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) eR.symm).trans
      (TensorProduct.AlgebraTensorModule.rid R S S)
  convert φ.symm.bijective using 1
  funext s
  exact φ.eq_symm_apply.mpr
    (by simp [φ, TensorProduct.smul_tmul',
      (eR.symm_apply_eq.2 (one_smul R m).symm : eR.symm m = 1)])

/-! ### The stalk of a pullback as a base change -/

variable {X Y : Scheme.{u}}

/-- **Stacks 0098 at the `Scheme.Modules` spelling.** A chosen linear equivalence between the
stalk of `p^*L` at `x` and the base change of the stalk of `L` at `p(x)` along the germ map
`𝒪_{Y, p x} → 𝒪_{X, x}`, pinned down by `Stacks.Divisors.pullbackStalkBaseChange_germ`.

This is `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` for the underlying
morphism of ringed spaces; no transport is needed, the two spellings of the pullback agreeing by
`rfl`. The equivalence is unique, being determined on the germs of pullbacks of sections, which
span the stalk; uniqueness is not needed below and is not proved. -/
def pullbackStalkBaseChange (p : X ⟶ Y) (L : Y.Modules) (x : X) :
    letI : Algebra (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
      (p.stalkMap x).hom.toAlgebra
    ((Scheme.Modules.pullback p).obj L).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (X.presheaf.stalk x) ⊗[Y.presheaf.stalk (p.base x)] L.presheaf.stalk (p.base x) :=
  letI : Algebra (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
    (p.stalkMap x).hom.toAlgebra
  (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    p.toLRSHom.toShHom L x).choose

/-- **The characterization of `Stacks.Divisors.pullbackStalkBaseChange`:** the germ at `x` of the
pullback of a section `a` of `L` over `V` goes to `1 ⊗ (germ of a at p(x))`. -/
theorem pullbackStalkBaseChange_germ (p : X ⟶ Y) (L : Y.Modules) (x : X) (V : Y.Opens)
    (hx : p.base x ∈ V) (a : Γ(L, V)) :
    letI : Algebra (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
      (p.stalkMap x).hom.toAlgebra
    pullbackStalkBaseChange p L x
        (((Scheme.Modules.pullback p).obj L).presheaf.germ (p ⁻¹ᵁ V) x hx
          (pullbackUnitSections p L V a)) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (p.base x)]
        L.presheaf.germ V (p.base x) hx a :=
  (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    p.toLRSHom.toShHom L x).choose_spec V hx a

/-! ### The pullback of a stalk element -/

/-- **The pullback of an element of the stalk of `L` at `p(x)`**, an element of the stalk of
`p^*L` at `x`: the element `1 ⊗ m` of the base change, read through
`Stacks.Divisors.pullbackStalkBaseChange`. -/
def pullbackStalk (p : X ⟶ Y) (L : Y.Modules) (x : X) (m : L.presheaf.stalk (p.base x)) :
    ((Scheme.Modules.pullback p).obj L).presheaf.stalk x :=
  letI : Algebra (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
    (p.stalkMap x).hom.toAlgebra
  (pullbackStalkBaseChange p L x).symm
    ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (p.base x)] m)

/-- **The pullback of a stalk element carries germs to germs.** The germ at `p(x)` of a section
`a` of `L` over `V` pulls back to the germ at `x` of the pullback of `a`, a section of `p^*L`
over `p⁻¹V`. -/
theorem pullbackStalk_germ (p : X ⟶ Y) (L : Y.Modules) (x : X) (V : Y.Opens)
    (hx : p.base x ∈ V) (a : Γ(L, V)) :
    pullbackStalk p L x (L.presheaf.germ V (p.base x) hx a) =
      ((Scheme.Modules.pullback p).obj L).presheaf.germ (p ⁻¹ᵁ V) x hx
        (pullbackUnitSections p L V a) :=
  let : Algebra (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
    (p.stalkMap x).hom.toAlgebra
  (LinearEquiv.symm_apply_eq _).2 (pullbackStalkBaseChange_germ p L x V hx a).symm

/-- **The pullback of a stalk element is semilinear** over the germ map
`𝒪_{Y, p x} → 𝒪_{X, x}`: in the base change `1 ⊗ (r · m) = (r · 1) ⊗ m`, and `r · 1` is the
image of `r`. -/
theorem pullbackStalk_smul (p : X ⟶ Y) (L : Y.Modules) (x : X)
    (r : Y.presheaf.stalk (p.base x)) (m : L.presheaf.stalk (p.base x)) :
    pullbackStalk p L x (r • m) = (p.stalkMap x).hom r • pullbackStalk p L x m := by
  let : Algebra (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
    (p.stalkMap x).hom.toAlgebra
  have htmul : ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (p.base x)] (r • m)) =
      (p.stalkMap x).hom r •
        ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (p.base x)] m) := by
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
    congr 1
  show (pullbackStalkBaseChange p L x).symm _ = _
  rw [htmul, map_smul]
  rfl

/-- **The pullback of a stalk basis is a stalk basis.** Multiplication by `1 ⊗ m` is bijective by
`Stacks.Divisors.bijective_smul_one_tmul`, and the base-change equivalence is semilinear, so
multiplication by the pullback of `m` is bijective too. -/
theorem IsStalkBasis.pullbackStalk {p : X ⟶ Y} {L : Y.Modules} {x : X}
    {m : L.presheaf.stalk (p.base x)} (hm : IsStalkBasis L (p.base x) m) :
    IsStalkBasis ((Scheme.Modules.pullback p).obj L) x (Divisors.pullbackStalk p L x m) := by
  let : Algebra (Y.presheaf.stalk (p.base x)) (X.presheaf.stalk x) :=
    (p.stalkMap x).hom.toAlgebra
  show Function.Bijective fun s : X.presheaf.stalk x => s • Divisors.pullbackStalk p L x m
  convert (pullbackStalkBaseChange p L x).symm.bijective.comp (bijective_smul_one_tmul hm) using 1
  funext s
  exact ((pullbackStalkBaseChange p L x).symm.map_smul s _).symm

/-- **The pullback of a trivialized module is trivialized.** If a section `t` of `L` over `W` has
a stalk basis for its germ at every point of `W` then so does the pullback of `t`, a section of
`p^*L` over `p⁻¹W`: its germ at a point `x'` is the pullback of the germ of `t` at `p(x')`.

This discharges, with no invertibility hypothesis, the rank-one hypothesis that the
order-of-vanishing calculus asks of a pullback. -/
theorem IsTrivializedNear.pullback {p : X ⟶ Y} {L : Y.Modules} {x : X}
    (hL : IsTrivializedNear L (p.base x)) :
    IsTrivializedNear ((Scheme.Modules.pullback p).obj L) x := by
  obtain ⟨W, hW, t, ht⟩ := hL
  refine ⟨p ⁻¹ᵁ W, hW, pullbackUnitSections p L W t, fun x' hx' => ?_⟩
  rw [← pullbackStalk_germ p L x' W hx' t]
  exact (ht (p.base x') hx').pullbackStalk

/-! ### Naming the image point through an equality -/

section At

variable (p : X ⟶ Y) (L : Y.Modules) (x : X)

/-- `Stacks.Divisors.pullbackStalk` with the image point named through an equality
`p(x) = z`. The generic-point case is this at `x = η_X` and `z = η_Y`, and stating the
transport once here is what keeps the lemmas below free of it. -/
def pullbackStalkAt {z : Y} (h : p.base x = z) (m : L.presheaf.stalk z) :
    ((Scheme.Modules.pullback p).obj L).presheaf.stalk x :=
  (h ▸ pullbackStalk p L x) m

/-- `Stacks.Divisors.pullbackStalkAt` carries germs to germs. -/
theorem pullbackStalkAt_germ {z : Y} (h : p.base x = z) (V : Y.Opens) (hx : p.base x ∈ V)
    (a : Γ(L, V)) :
    pullbackStalkAt p L x h (L.presheaf.germ V z (h ▸ hx) a) =
      ((Scheme.Modules.pullback p).obj L).presheaf.germ (p ⁻¹ᵁ V) x hx
        (pullbackUnitSections p L V a) := by
  cases h
  exact pullbackStalk_germ p L x V hx a

/-- `Stacks.Divisors.pullbackStalkAt` is semilinear over the transported germ map. -/
theorem pullbackStalkAt_smul {z : Y} (h : p.base x = z) (r : Y.presheaf.stalk z)
    (m : L.presheaf.stalk z) :
    pullbackStalkAt p L x h (r • m) =
      (h ▸ p.stalkMap x).hom r • pullbackStalkAt p L x h m := by
  cases h
  exact pullbackStalk_smul p L x r m

/-- `Stacks.Divisors.pullbackStalkAt` carries a stalk basis to a stalk basis. -/
theorem IsStalkBasis.pullbackStalkAt {z : Y} (h : p.base x = z) {m : L.presheaf.stalk z}
    (hm : IsStalkBasis L z m) :
    IsStalkBasis ((Scheme.Modules.pullback p).obj L) x (Divisors.pullbackStalkAt p L x h m) := by
  cases h
  exact hm.pullbackStalk

end At

/-! ### The pullback of a meromorphic section -/

/-- **A dominant morphism of integral schemes takes the generic point to the generic point.**
This is clause (2) of Stacks 0CC1, `AlgebraicGeometry.tfae_isDominant_of_isIntegral`. -/
theorem base_genericPoint_of_isDominant (p : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [IsDominant p] : p.base (genericPoint X) = genericPoint Y :=
  ((tfae_isDominant_of_isIntegral p).out 1 2).mp (inferInstance : IsDominant p)

variable [IsIntegral X] [IsIntegral Y]

/-- **The pullback of a meromorphic section.** In the generic-stalk model a meromorphic section
of `L` is an element of the stalk `L_{η_Y}`; along a dominant morphism `p : X ⟶ Y` of integral
schemes the generic point of `X` lies over the generic point of `Y`, so
`Stacks.Divisors.pullbackStalk` at `η_X` gives an element of `(p^*L)_{η_X}`, a meromorphic
section of `p^*L`. -/
def genericStalkPullback (p : X ⟶ Y) [IsDominant p] (L : Y.Modules)
    (s : L.presheaf.stalk (genericPoint Y)) :
    ((Scheme.Modules.pullback p).obj L).presheaf.stalk (genericPoint X) :=
  pullbackStalkAt p L (genericPoint X) (base_genericPoint_of_isDominant p) s

/-- **The pullback of a meromorphic section carries germs to germs.** -/
theorem genericStalkPullback_germ (p : X ⟶ Y) [IsDominant p] (L : Y.Modules) (V : Y.Opens)
    (hx : p.base (genericPoint X) ∈ V) (a : Γ(L, V)) :
    genericStalkPullback p L
        (L.presheaf.germ V (genericPoint Y) (base_genericPoint_of_isDominant p ▸ hx) a) =
      ((Scheme.Modules.pullback p).obj L).presheaf.germ (p ⁻¹ᵁ V) (genericPoint X) hx
        (pullbackUnitSections p L V a) :=
  pullbackStalkAt_germ p L (genericPoint X) (base_genericPoint_of_isDominant p) V hx a

/-- **The pullback of a meromorphic section is semilinear over the extension of function
fields** `AlgebraicGeometry.dominantFunctionFieldMap p`, which is by definition the germ map at
the generic point transported along `p(η_X) = η_Y`. -/
theorem genericStalkPullback_smul (p : X ⟶ Y) [IsDominant p] (L : Y.Modules)
    (r : Y.functionField) (s : L.presheaf.stalk (genericPoint Y)) :
    genericStalkPullback p L (r • s) =
      dominantFunctionFieldMap p r • genericStalkPullback p L s :=
  pullbackStalkAt_smul p L (genericPoint X) (base_genericPoint_of_isDominant p) r s

/-- **The pullback of a meromorphic section carries a stalk basis to a stalk basis.** -/
theorem IsStalkBasis.genericStalkPullback {p : X ⟶ Y} [IsDominant p] {L : Y.Modules}
    {s : L.presheaf.stalk (genericPoint Y)} (hs : IsStalkBasis L (genericPoint Y) s) :
    IsStalkBasis ((Scheme.Modules.pullback p).obj L) (genericPoint X)
      (Divisors.genericStalkPullback p L s) :=
  hs.pullbackStalkAt p L (genericPoint X) (base_genericPoint_of_isDominant p)

/-- **Pulling back a stalk element commutes with passage to the generic stalk.** Both sides are
computed on a section representing the given germ, where each is the germ at `η_X` of the
pullback of that section. -/
theorem toGenericStalk_pullbackStalk (p : X ⟶ Y) [IsDominant p] (L : Y.Modules) (x : X)
    (m : L.presheaf.stalk (p.base x)) :
    toGenericStalk ((Scheme.Modules.pullback p).obj L) x (pullbackStalk p L x m) =
      genericStalkPullback p L (toGenericStalk L (p.base x) m) := by
  obtain ⟨V, hxV, a, ha⟩ := L.presheaf.exists_germ_eq m
  have hηpV : genericPoint X ∈ p ⁻¹ᵁ V := genericPoint_mem_of_mem (W := p ⁻¹ᵁ V) hxV
  rw [← ha, pullbackStalk_germ p L x V hxV a,
    toGenericStalk_germ (L := (Scheme.Modules.pullback p).obj L) hxV hηpV,
    toGenericStalk_germ (L := L) hxV (genericPoint_mem_of_mem hxV)]
  exact (genericStalkPullback_germ p L V hηpV a).symm

/-! ### Coordinates -/

/-- **A coordinate pulls back to a coordinate.** If the rational function `a` on `Y` expresses
the meromorphic section `s` of `L` in terms of a basis of the stalk `L_{p x}`, then the image of
`a` in `R(X)` expresses `p^*s` in terms of a basis of `(p^*L)_x`.

This is the coordinate identification used in the proof of
[Stacks, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST): with it, the order of vanishing
of `p^*s` along a prime divisor of `X` lying over `x` is the order of vanishing of the image of
`a`, by `Stacks.Divisors.orderOfVanishing_eq`. -/
theorem IsCoordinateAt.pullback {p : X ⟶ Y} [IsDominant p] {L : Y.Modules} {x : X}
    {s : L.presheaf.stalk (genericPoint Y)} {a : Y.functionField}
    (ha : IsCoordinateAt L (p.base x) s a) :
    IsCoordinateAt ((Scheme.Modules.pullback p).obj L) x (genericStalkPullback p L s)
      (dominantFunctionFieldMap p a) := by
  obtain ⟨m, hm, hsa⟩ := ha
  refine ⟨pullbackStalk p L x m, hm.pullbackStalk, ?_⟩
  rw [hsa, genericStalkPullback_smul, toGenericStalk_pullbackStalk]

end Stacks.Divisors

end
