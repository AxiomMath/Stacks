module

public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction

/-!
# Functoriality of the conormal module of a first-order thickening

Let `i : T ⟶ T'` be a first-order thickening with `T'` affine. The conormal module of `i` is the
kernel of `i.appTop : Γ(T', ⊤) ⟶ Γ(T, ⊤)`, a module over `Γ(T, ⊤)` by
`Stacks.Smooth.thickeningKerModule`: the ideal is square-zero, so the action of `Γ(T', ⊤)` on it
factors through the surjection `i.appTop`.

This file makes that module functorial. A *morphism of thickenings* from `i : T ⟶ T'` to
`j : S ⟶ S'` is a commutative square
```
T --i--→ T'
|        |
f        k
↓        ↓
S --j--→ S'
```
and the induced ring map `k.appTop : Γ(S', ⊤) ⟶ Γ(T', ⊤)` carries the conormal module of `j`
into the conormal module of `i`, because `i.appTop ∘ k.appTop = f.appTop ∘ j.appTop` kills
anything killed by `j.appTop`. The resulting map is linear not merely over `Γ(S', ⊤)` but over
`Γ(S, ⊤)`, acting on the target through `f.appTop`; that is
`Stacks.Thickenings.conormalMap`, the affine avatar of the map
`f^*𝒞_{S/S'} → 𝒞_{T/T'}` of [Stacks Project, Tag 01R4] in the case where the two immersions are
first-order thickenings.

## Main definitions

* `Stacks.Thickenings.conormalModuleAlong` is the `Γ(S, ⊤)`-module structure on the conormal
  module of `i : T ⟶ T'` obtained from `Stacks.Smooth.thickeningKerModule` by restricting scalars
  along `f.appTop` for a morphism `f : T ⟶ S`. It is the affine avatar of regarding
  `𝒞_{T/T'}` as the target of a map out of a pullback along `f`.
* `Stacks.Thickenings.conormalMap` is the induced `Γ(S, ⊤)`-linear map of conormal modules.

## Main results

* `Stacks.Thickenings.appTop_comm_of_comm` and `Stacks.Thickenings.mem_ker_appTop_of_comm`: a
  morphism of thickenings carries the conormal ideal into the conormal ideal.
* `Stacks.Thickenings.conormalMap_apply`: the characterizing property. On underlying sections the
  conormal map is `k.appTop`. This is the affine characterization of
  [Stacks Project, Tag 01R4] for thickenings: a section of the defining ideal of `j` is sent to
  its image under the ambient ring map. No quotient by a square of the ideal appears, because for
  a first-order thickening the defining ideal already equals its own conormal module.
* `Stacks.Thickenings.conormalMap_id_apply` and `Stacks.Thickenings.conormalMap_comp_apply`:
  functoriality.
* `Stacks.Thickenings.bijective_conormalMap`: the conormal map of an isomorphism of thickenings
  is bijective.

## Implementation notes

The module structures on the two conormal modules are not instances — they are produced by
`Stacks.Smooth.thickeningKerModule` from a proof that the thickening is first-order — so they are
introduced by `letI` in the statement of `Stacks.Thickenings.conormalMap`, as in
`Stacks.Smooth.conormalRestrict`. All the downstream lemmas are stated on *underlying sections*,
after the coercion `RingHom.ker i.appTop.hom → Γ(T', ⊤)`, rather than as equalities of linear
maps. That is deliberate: an equality of linear maps between modules whose scalar actions are
built by `Module.compHom` along different ring maps would require transporting along an equality
of module structures, whereas the underlying sections live in a fixed commutative ring and the
statements are exactly the affine characterization of Tag 01R4.

Affineness of the *ambient* schemes `T'` and `S'` is what makes `i.appTop` surjective with
square-zero kernel, hence what makes the kernel a module over `Γ(T, ⊤)` at all; affineness of
`T` and `S` then follows, since a closed subscheme of an affine scheme is affine. No affineness
hypothesis is needed for `Stacks.Thickenings.appTop_comm_of_comm` or
`Stacks.Thickenings.mem_ker_appTop_of_comm`, which are statements about the ring maps alone.

This is *not* the full statement of Tag 01R4, which is about arbitrary immersions and produces a
morphism of quasi-coherent sheaves `f^*𝒞_{S/S'} → 𝒞_{T/T'}` on all of `T`. It is the global
sections of that morphism over an affine ambient scheme, which is the only case the proof of
[Stacks Project, Tag 04F7] uses in the thickening situation and the only case reachable from the
conormal material currently in the library. Neither of the two declarations carries a `01R4`
attribute, for that reason.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Thickenings

variable {R R' S S' T T' : Scheme.{u}}

/-! ### Global sections of a commutative square -/

/-- Global sections turn composition of morphisms of schemes into composition of the induced ring
maps, in the opposite order. -/
theorem appTop_comp_apply (p : R ⟶ S) (q : S ⟶ T) (x : Γ(T, (⊤ : T.Opens))) :
    p.appTop.hom (q.appTop.hom x) = (p ≫ q).appTop.hom x :=
  rfl

/-- **A commutative square of schemes on global sections.** For `i ≫ k = f ≫ j`, going around the
square one way agrees with going around it the other way on global sections. -/
theorem appTop_comm_of_comm {i : T ⟶ T'} {j : S ⟶ S'} {f : T ⟶ S} {k : T' ⟶ S'}
    (comm : i ≫ k = f ≫ j) (x : Γ(S', (⊤ : S'.Opens))) :
    i.appTop.hom (k.appTop.hom x) = f.appTop.hom (j.appTop.hom x) := by
  rw [appTop_comp_apply, appTop_comp_apply, comm]

/-- **A morphism of thickenings carries the conormal ideal into the conormal ideal.** If
`i ≫ k = f ≫ j` then `k.appTop` maps the kernel of `j.appTop` into the kernel of `i.appTop`. -/
theorem mem_ker_appTop_of_comm {i : T ⟶ T'} {j : S ⟶ S'} {f : T ⟶ S} {k : T' ⟶ S'}
    (comm : i ≫ k = f ≫ j) {x : Γ(S', (⊤ : S'.Opens))} (hx : x ∈ RingHom.ker j.appTop.hom) :
    k.appTop.hom x ∈ RingHom.ker i.appTop.hom := by
  rw [RingHom.mem_ker, appTop_comm_of_comm comm, RingHom.mem_ker.mp hx, map_zero]

/-- The composite of two morphisms of thickenings is a morphism of thickenings. -/
theorem comm_comp {i : T ⟶ T'} {j : S ⟶ S'} {n : R ⟶ R'} {f : T ⟶ S} {k : T' ⟶ S'}
    {f' : S ⟶ R} {k' : S' ⟶ R'} (comm : i ≫ k = f ≫ j) (comm' : j ≫ k' = f' ≫ n) :
    i ≫ (k ≫ k') = (f ≫ f') ≫ n := by
  rw [← Category.assoc, comm, Category.assoc, comm', ← Category.assoc]

/-! ### The conormal module along a morphism of the closed subschemes -/

/-- The `Γ(S, ⊤)`-module structure on the conormal module of a first-order thickening
`i : T ⟶ T'` with `T'` affine, obtained from `Stacks.Smooth.thickeningKerModule` by restricting
scalars along `f.appTop` for a morphism `f : T ⟶ S`.

This is the affine avatar of regarding the conormal sheaf `𝒞_{T/T'}` as the target of a morphism
out of a pullback along `f`: a `Γ(S, ⊤)`-linear map into it is the same as a map out of the
pullback. -/
@[instance_reducible]
noncomputable def conormalModuleAlong [IsAffine T'] {i : T ⟶ T'}
    (hi : IsFirstOrderThickening i) (f : T ⟶ S) :
    Module Γ(S, (⊤ : S.Opens)) (RingHom.ker i.appTop.hom) :=
  Smooth.kerModuleOfRingHom (Smooth.surjective_appTop_of_isFirstOrderThickening hi)
    (Smooth.ker_appTop_sq_eq_bot hi) f.appTop.hom

/-- The action of `Γ(S, ⊤)` through `Stacks.Thickenings.conormalModuleAlong` is multiplication by
any section of `T'` whose image in `Γ(T, ⊤)` is the image of the scalar under `f.appTop`. -/
theorem conormalModuleAlong_smul [IsAffine T'] {i : T ⟶ T'} (hi : IsFirstOrderThickening i)
    (f : T ⟶ S) (c : Γ(S, (⊤ : S.Opens))) {x : Γ(T', (⊤ : T'.Opens))}
    (hx : i.appTop.hom x = f.appTop.hom c) (y : RingHom.ker i.appTop.hom) :
    letI := conormalModuleAlong hi f
    c • y = x • y :=
  Smooth.kerModuleOfRingHom_smul (Smooth.surjective_appTop_of_isFirstOrderThickening hi)
    (Smooth.ker_appTop_sq_eq_bot hi) f.appTop.hom c x hx y

/-! ### The induced map of conormal modules -/

/-- **The conormal module map of a morphism of first-order thickenings.** Let `i : T ⟶ T'` and
`j : S ⟶ S'` be first-order thickenings with `T'` and `S'` affine, and let `f : T ⟶ S`,
`k : T' ⟶ S'` form a commutative square `i ≫ k = f ≫ j`. Then `k.appTop` carries the conormal
module of `j` into the conormal module of `i`, `Γ(S, ⊤)`-linearly for the action on the target
through `f.appTop`.

This is the affine form, for thickenings, of the canonical map
`f^*𝒞_{S/S'} → 𝒞_{T/T'}` of [Stacks Project, Tag 01R4]. -/
noncomputable def conormalMap [IsAffine T'] [IsAffine S'] {i : T ⟶ T'} {j : S ⟶ S'}
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j) {f : T ⟶ S} {k : T' ⟶ S'}
    (comm : i ≫ k = f ≫ j) :
    letI := Smooth.thickeningKerModule hj
    letI := conormalModuleAlong hi f
    RingHom.ker j.appTop.hom →ₗ[Γ(S, (⊤ : S.Opens))] RingHom.ker i.appTop.hom :=
  letI := Smooth.thickeningKerModule hj
  letI := conormalModuleAlong hi f
  { toFun := fun x ↦
      ⟨k.appTop.hom (x : Γ(S', (⊤ : S'.Opens))), mem_ker_appTop_of_comm comm x.2⟩
    map_add' := fun x y ↦ Subtype.ext (by
      simp only [Submodule.coe_add]
      exact map_add _ _ _)
    map_smul' := fun c x ↦ Subtype.ext (by
      obtain ⟨r, hr⟩ := Smooth.surjective_appTop_of_isFirstOrderThickening hj c
      have hcx : ((c • x : RingHom.ker j.appTop.hom) : Γ(S', (⊤ : S'.Opens)))
          = r * (x : Γ(S', (⊤ : S'.Opens))) := by
        rw [← hr, Smooth.thickeningKerModule_smul hj, Submodule.coe_smul, smul_eq_mul]
      rw [RingHom.id_apply, conormalModuleAlong_smul hi f c
          (x := k.appTop.hom r) (by rw [appTop_comm_of_comm comm, hr]),
        Submodule.coe_smul, smul_eq_mul]
      change k.appTop.hom ((c • x : RingHom.ker j.appTop.hom) : Γ(S', (⊤ : S'.Opens))) = _
      rw [hcx, map_mul]) }

/-- **The affine characterization of the conormal map.** On underlying sections
`Stacks.Thickenings.conormalMap` is the ring map `k.appTop` of the ambient schemes.

This is the characterizing property of the map of [Stacks Project, Tag 01R4] in the thickening
case: the defining ideal of a first-order thickening equals its own conormal module, so no
quotient by the square of the ideal intervenes. -/
theorem conormalMap_apply [IsAffine T'] [IsAffine S'] {i : T ⟶ T'} {j : S ⟶ S'}
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j) {f : T ⟶ S} {k : T' ⟶ S'}
    (comm : i ≫ k = f ≫ j) (x : RingHom.ker j.appTop.hom) :
    ((conormalMap hi hj comm x : RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens)))
      = k.appTop.hom (x : Γ(S', (⊤ : S'.Opens))) :=
  rfl

/-- The conormal map of the identity morphism of thickenings is the identity. -/
theorem conormalMap_id_apply [IsAffine T'] {i : T ⟶ T'} (hi : IsFirstOrderThickening i)
    (x : RingHom.ker i.appTop.hom) :
    ((conormalMap hi hi (f := 𝟙 T) (k := 𝟙 T') (by simp) x : RingHom.ker i.appTop.hom) :
        Γ(T', (⊤ : T'.Opens))) = (x : Γ(T', (⊤ : T'.Opens))) :=
  rfl

/-- The conormal map of a composite of morphisms of thickenings is the composite of the conormal
maps, in the opposite order. -/
theorem conormalMap_comp_apply [IsAffine R'] [IsAffine S'] [IsAffine T'] {i : T ⟶ T'}
    {j : S ⟶ S'} {n : R ⟶ R'} (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j)
    (hn : IsFirstOrderThickening n) {f : T ⟶ S} {k : T' ⟶ S'} {f' : S ⟶ R} {k' : S' ⟶ R'}
    (comm : i ≫ k = f ≫ j) (comm' : j ≫ k' = f' ≫ n) (x : RingHom.ker n.appTop.hom) :
    ((conormalMap hi hn (comm_comp comm comm') x : RingHom.ker i.appTop.hom) :
        Γ(T', (⊤ : T'.Opens)))
      = ((conormalMap hi hj comm (conormalMap hj hn comm' x) : RingHom.ker i.appTop.hom) :
        Γ(T', (⊤ : T'.Opens))) :=
  rfl

/-- Going along a morphism of thickenings and back along one whose top components compose to the
identity is the identity. -/
private theorem conormalMap_conormalMap_apply [IsAffine T'] [IsAffine S'] {i : T ⟶ T'}
    {j : S ⟶ S'} (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j) {f : T ⟶ S}
    {k : T' ⟶ S'} {f' : S ⟶ T} {k' : S' ⟶ T'} (comm : i ≫ k = f ≫ j) (comm' : j ≫ k' = f' ≫ i)
    (hkk' : k' ≫ k = 𝟙 S') (x : RingHom.ker j.appTop.hom) :
    conormalMap hj hi comm' (conormalMap hi hj comm x) = x :=
  Subtype.ext (by
    rw [conormalMap_apply, conormalMap_apply, appTop_comp_apply, hkk']
    rfl)

/-- **The conormal map of an isomorphism of thickenings is bijective.** If `(f, k)` and `(f', k')`
are morphisms of thickenings in opposite directions whose ambient components are mutually
inverse, then the conormal map of `(f, k)` is bijective, with the conormal map of `(f', k')` as
its inverse. -/
theorem bijective_conormalMap [IsAffine T'] [IsAffine S'] {i : T ⟶ T'} {j : S ⟶ S'}
    (hi : IsFirstOrderThickening i) (hj : IsFirstOrderThickening j) {f : T ⟶ S} {k : T' ⟶ S'}
    {f' : S ⟶ T} {k' : S' ⟶ T'} (comm : i ≫ k = f ≫ j) (comm' : j ≫ k' = f' ≫ i)
    (hkk' : k' ≫ k = 𝟙 S') (hk'k : k ≫ k' = 𝟙 T') :
    Function.Bijective (conormalMap hi hj comm) := by
  exact ⟨Function.LeftInverse.injective (conormalMap_conormalMap_apply hi hj comm comm' hkk'),
    fun y ↦ ⟨_, conormalMap_conormalMap_apply hj hi comm' comm hk'k y⟩⟩

end Stacks.Thickenings

end
