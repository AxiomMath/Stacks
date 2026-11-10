module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleGaloisAction

/-!
# The Galois action on the Picard group of a base change

Let `S/R` be an extension of commutative rings and let `X` be a scheme over `Spec R`. An
`R`-algebra automorphism `σ` of `S` induces the automorphism `id_X × Spec(σ)` of the base change
`X_S = X ×_{Spec R} Spec S` — `AlgebraicGeometry.galoisActionOnBaseChange`, which is a right
action of the automorphism group because `Spec` is contravariant. Pullback of invertible modules
reverses composition once more, so pullback along these automorphisms is a *left* action of the
automorphism group on `Pic(X_S)`, by homomorphisms of abelian groups.

The classes fixed by that action are `Stacks.Picard.galoisFixedClasses`. Pullback along the
projection `X_S → X` lands in them: the projection is unchanged by the automorphisms, since
`id_X × Spec(σ)` is the identity in the `X`-coordinate, so the pullback of a class from `X` is
fixed. This is the easy inclusion of Stacks Tag 0CDT, which asserts for `R = k` a field,
`S = k'` a Galois extension, `X` quasi-compact, quasi-separated, with `H⁰(X, 𝒪_X) = k` and a
`k`-rational point, that pullback is a *bijection* of `Pic(X)` onto the fixed classes. The
remaining content of that tag — injectivity, and Galois descent for the surjectivity — is
proved elsewhere; see the implementation notes.

## Main definitions

* `Stacks.Picard.galoisTwist` — the automorphism `id_X × Spec(σ)` of the base change.
* `Stacks.Picard.galoisPicardAction` — the induced left action on the Picard group of the base
  change.
* `Stacks.Picard.galoisFixedClasses` — the Picard classes fixed by every Galois twist.

## Main results

* `Stacks.Picard.galoisTwist_one`, `Stacks.Picard.galoisTwist_mul` — the twists form a right
  action: `galoisTwist (σ * τ) = galoisTwist σ ≫ galoisTwist τ`.
* `Stacks.Picard.galoisTwist_comp_fst` — a twist does not move the projection to `X`.
* `Stacks.Picard.schemePullbackClass_mem_galoisFixedClasses` — pullback along the projection
  `X_S → X` takes values in the Galois-fixed classes.

## Implementation notes

The action is given as a `DistribMulAction`-valued definition rather than as an instance: the
carrier is `Stacks.Picard.ofScheme` of a base change, and a global instance keyed on the Picard
group of an arbitrary ringed site would be tried, and then fail to unify, on every Picard group
in the library. `Stacks.Picard.galoisPicardAction_smul` identifies its scalar multiplication
with pullback along the twist, and `Stacks.Picard.galoisFixedClasses` is phrased directly in
terms of pullback for the same reason.

What Tag 0CDT needs beyond this file: injectivity of `Pic(X) → Pic(X_{k'})` (Tag 0CC5), Galois
descent for quasi-coherent modules along a finite Galois extension (Tag 0CDR), the identity
`H⁰(X_{k'}, 𝒪) = k'` (Tag 02KH) used to normalise the descent cocycle at the rational point, and
— to reduce an infinite Galois extension to the finite ones — the identification of `Pic` of a
limit of schemes with the colimit of the `Pic`s (Tag 0B8W).

All four are available, and the tag is proved.  Tag 0CC5 is
`StacksFrontier/AlgebraicGeometry/PicardBaseChange/Injectivity.lean`, and the injectivity half of
Tag 0CDT is proved from it in
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/Injectivity.lean`; Tag 0CDR is
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/GaloisFieldExtension.lean`, as an
equivalence of categories of quasi-coherent modules for a finite extension, read on invertible
modules in `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/InvertibleDescent.lean`; Tag 0B8W
is in
`StacksFrontier/AlgebraicGeometry/ModuleLimits/`; and Tag 02KH is carried in degree `0` over an
affine base.  The surjectivity half is
`Stacks.Picard.surjOn_schemePullbackClass_galoisFixedClasses`: the reduction to a finite Galois
stage is `StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageFixed.lean` and the
descent at that stage, with the
cocycle normalised at the rational point, is
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/FiniteStageDescent.lean`.  The
whole identification is `Stacks.Picard.bijOn_schemePullbackClass_galoisFixedClasses` of
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/PicardGaloisInvariants.lean`.

## References

* [Stacks Project, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT)
* [Stacks Project, Tag 038J](https://stacks.math.columbia.edu/tag/038J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (X : Over (Spec (.of R)))

/-- The automorphism `id_X × Spec(σ)` of the base change `X_S`, attached to an `R`-algebra
automorphism `σ` of `S`. -/
abbrev galoisTwist (σ : S ≃ₐ[R] S) :
    SchemeOver.baseChange R S X ⟶ SchemeOver.baseChange R S X :=
  ((galoisActionOnBaseChange R S X).ρ (MulOpposite.op σ)).asHom

/-- The identity automorphism of `S` induces the identity of the base change. -/
@[simp]
theorem galoisTwist_one : galoisTwist R S X 1 = 𝟙 (SchemeOver.baseChange R S X) := by
  change ((galoisActionOnBaseChange R S X).ρ (MulOpposite.op (1 : S ≃ₐ[R] S))).asHom = _
  rw [show MulOpposite.op (1 : S ≃ₐ[R] S) = 1 from rfl, map_one, End.one_asHom]
  rfl

/-- The twists compose in the same order as the automorphisms: the twists are a right action of
the automorphism group, which is why pullback along them is a left action. -/
theorem galoisTwist_mul (σ τ : S ≃ₐ[R] S) :
    galoisTwist R S X (σ * τ) = galoisTwist R S X σ ≫ galoisTwist R S X τ := by
  change ((galoisActionOnBaseChange R S X).ρ (MulOpposite.op (σ * τ))).asHom = _
  rw [show MulOpposite.op (σ * τ) = MulOpposite.op τ * MulOpposite.op σ from rfl, map_mul,
    End.mul_asHom]

/-- A twist is the identity in the `X`-coordinate, so it does not move the projection `X_S → X`.
This is what makes a class pulled back from `X` Galois-fixed. -/
@[simp]
theorem galoisTwist_comp_fst (σ : S ≃ₐ[R] S) :
    galoisTwist R S X σ ≫
        pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  dsimp only [galoisTwist, galoisActionOnBaseChange, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [pullback.lift_fst, Category.comp_id]

/-- A twist acts on the `S`-coordinate by `Spec(σ)`. -/
@[simp]
theorem galoisTwist_comp_snd (σ : S ≃ₐ[R] S) :
    galoisTwist R S X σ ≫
        pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫
        specMapAlgAut R S σ := by
  dsimp only [galoisTwist, galoisActionOnBaseChange, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [pullback.lift_snd]
  rfl

/-- **The Galois action on the Picard group of a base change.** Pullback along the twists
`id_X × Spec(σ)` is a left action of the `R`-algebra automorphism group of `S` on `Pic(X_S)` by
homomorphisms of abelian groups. -/
@[instance_reducible]
def galoisPicardAction :
    DistribMulAction (S ≃ₐ[R] S) (ofScheme (SchemeOver.baseChange R S X)) where
  smul σ x := schemePullbackClass (galoisTwist R S X σ) x
  one_smul x := by
    change schemePullbackClass (galoisTwist R S X 1) x = x
    rw [galoisTwist_one]
    exact schemePullbackClass_id _ x
  mul_smul σ τ x := by
    change schemePullbackClass (galoisTwist R S X (σ * τ)) x =
      schemePullbackClass (galoisTwist R S X σ)
        (schemePullbackClass (galoisTwist R S X τ) x)
    rw [schemePullbackClass_comp, galoisTwist_mul]
  smul_zero σ := map_zero (schemePullbackClassHom (galoisTwist R S X σ))
  smul_add σ x y := map_add (schemePullbackClassHom (galoisTwist R S X σ)) x y

/-- The scalar multiplication of the Galois action is pullback along the corresponding twist. -/
theorem galoisPicardAction_smul (σ : S ≃ₐ[R] S)
    (x : ofScheme (SchemeOver.baseChange R S X)) :
    letI := galoisPicardAction R S X
    σ • x = schemePullbackClass (galoisTwist R S X σ) x := rfl

/-- The Galois-fixed Picard classes of the base change: those invariant under pullback along
every twist `id_X × Spec(σ)`. -/
def galoisFixedClasses : Set (ofScheme (SchemeOver.baseChange R S X)) :=
  {x | ∀ σ : S ≃ₐ[R] S, schemePullbackClass (galoisTwist R S X σ) x = x}

/-- A Picard class of the base change is Galois-fixed if and only if it is invariant under
pullback along every twist `id_X × Spec(σ)`. -/
@[simp]
theorem mem_galoisFixedClasses {x : ofScheme (SchemeOver.baseChange R S X)} :
    x ∈ galoisFixedClasses R S X ↔
      ∀ σ : S ≃ₐ[R] S, schemePullbackClass (galoisTwist R S X σ) x = x :=
  Iff.rfl

/-- **The easy inclusion of Stacks Tag 0CDT.** Pullback along the projection `X_S → X` takes
every Picard class of `X` to a Galois-fixed class of `X_S`, because a twist does not move the
projection. -/
theorem schemePullbackClass_mem_galoisFixedClasses (x : ofScheme X.left) :
    schemePullbackClass (pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))) x ∈ galoisFixedClasses R S X := by
  intro σ
  rw [schemePullbackClass_comp, galoisTwist_comp_fst]

/-- Pullback along the projection `X_S → X`, as a homomorphism into the Galois-fixed classes:
the map Stacks Tag 0CDT asserts to be bijective. -/
theorem mapsTo_schemePullbackClass_galoisFixedClasses :
    Set.MapsTo (schemePullbackClass (pullback.fst X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))))
      Set.univ (galoisFixedClasses R S X) :=
  fun x _ => schemePullbackClass_mem_galoisFixedClasses R S X x

end Stacks.Picard

end
