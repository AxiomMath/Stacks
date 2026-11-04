module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Additive

/-!
# `𝐆_a` and the Artin–Schreier map on the small étale site

The additive group of a scheme `X` is the sheaf of abelian groups on the small étale site of `X`
whose sections over an étale `X`-scheme `U` are the global functions `Γ(U, 𝒪_U)`. This file
constructs it, together with the Frobenius endomorphism `x ↦ x ^ p` and the Artin–Schreier map
`x ↦ x ^ p - x`, both available when the prime `p` vanishes on `X`.

The sheaf condition is representability: the global functions on `X`-schemes are the functor of
points of the additive group scheme over `X`
(`AlgebraicGeometry.additiveGroupBaseChangeRepresentableBy`), and the small étale site is
subcanonical over `Over X`
(`AlgebraicGeometry.Scheme.isSheaf_smallEtale_comp_of_isRepresentable`). No descent argument is
needed, and in particular no structure sheaf of the small étale site is used.

## Main definitions

* `Stacks.ArtinSchreier.globalFunctionsPresheaf`: the presheaf of rings `U ↦ Γ(U, 𝒪_U)`.
* `Stacks.ArtinSchreier.additiveSheaf`: `𝐆_a` on the small étale site of `X`.
* `Stacks.ArtinSchreier.frobeniusMap`: the Frobenius `𝐆_a ⟶ 𝐆_a`, `x ↦ x ^ p`.
* `Stacks.ArtinSchreier.artinSchreierMap`: the map `F - 1`, that is `x ↦ x ^ p - x`.

## Main results

* `Stacks.ArtinSchreier.isSheaf_additivePresheaf`: the sheaf condition for `𝐆_a`.
* `Stacks.ArtinSchreier.artinSchreierMap_app_ofSection`: the Artin–Schreier map really is
  `x ↦ x ^ p - x` on sections.

## Implementation notes

Frobenius is built first as the ring endomorphism `Stacks.ArtinSchreier.frobeniusRingHom` and
then as an endomorphism of the presheaf of rings of global functions, which is whiskered into the
coefficient category. Building it directly on the abelian-group-valued presheaf is possible but
loses the multiplicative structure of the sections, which is what makes naturality a single
application of `map_pow`.

The coefficient category is `AddCommGrpCat.{max (u + 1) v}`, the universe in which this library
computes étale cohomology of a scheme in `Scheme.{u}`; sections of the structure sheaf are in
`Type u`, so they are raised by `AddCommGrpCat.uliftFunctor`. The additive group of a ring is
turned into a multiplicative one by `AddGrpCat.toGrp` in the representability statement, a type
synonym on the underlying set, so the sheaf condition transports along
`CategoryTheory.Presieve.isSheaf_iff_of_nat_equiv` exactly as for `𝐆_m`.

Additivity of `x ↦ x ^ p` is the freshman's dream `(x + y) ^ p = x ^ p + y ^ p`, which holds in
every commutative ring in which the prime `p` vanishes; this is a hypothesis of the statement,
in the form `(p : Γ(X, ⊤)) = 0`, transported to each étale `X`-scheme along the restriction ring
homomorphism; the zero ring, where `CharP` reads `1` rather than `p`, is handled separately.

## References

* [Stacks Project, Tag 0A3J](https://stacks.math.columbia.edu/tag/0A3J): the Artin–Schreier
  sequence, whose middle and right terms are the sheaf built here.
* [Stacks Project, Tag 022V](https://stacks.math.columbia.edu/tag/022V): the additive group
  scheme, whose functor of points gives the sheaf condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.ArtinSchreier

/-- **The freshman's dream.** In a commutative ring in which a prime `p` vanishes, taking `p`-th
powers is additive. -/
theorem add_pow_eq_of_natCast_eq_zero {R : Type*} [CommRing R] {p : ℕ} (hp : p.Prime)
    (h : (p : R) = 0) (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · have : Fact p.Prime := ⟨hp⟩
    have : CharP R p := (CharP.charP_iff_prime_eq_zero hp).mpr h
    exact add_pow_char x y p

/-- **The Frobenius endomorphism of a commutative ring in which the prime `p` vanishes**:
`x ↦ x ^ p`. It is multiplicative by commutativity and additive by the freshman's dream. -/
def frobeniusRingHom (R : Type*) [CommRing R] {p : ℕ} (hp : p.Prime) (h : (p : R) = 0) :
    R →+* R where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow hp.ne_zero
  map_add' := add_pow_eq_of_natCast_eq_zero hp h

/-- If `p` vanishes on `X` then it vanishes on every étale `X`-scheme, being carried along the
restriction homomorphism of global functions. -/
theorem natCast_eq_zero_of_etale (X : Scheme.{u}) {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (U : X.Etale) : (p : Γ(U.left, ⊤)) = 0 :=
  (map_natCast (Scheme.Γ.map U.hom.op).hom p).symm.trans
    ((congrArg (Scheme.Γ.map U.hom.op).hom hX).trans (map_zero _))

/-- The presheaf of rings on the small étale site of `X` whose sections over an étale `X`-scheme
`U` are the global functions `Γ(U, 𝒪_U)`. -/
noncomputable def globalFunctionsPresheaf (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ

/-- The passage from a ring to its additive group, raised to the coefficient universe of étale
cohomology. -/
noncomputable def additiveCoefficients : CommRingCat.{u} ⥤ AddCommGrpCat.{max (u + 1) v} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙
    AddCommGrpCat.uliftFunctor.{max (u + 1) v, u}

/-- The presheaf of abelian groups on the small étale site of `X` whose sections over an étale
`X`-scheme `U` are the global functions `Γ(U, 𝒪_U)`. -/
noncomputable def additivePresheaf (X : Scheme.{u}) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
  globalFunctionsPresheaf X ⋙ additiveCoefficients.{u, v}

/-- Sections of `Stacks.ArtinSchreier.additivePresheaf` over `U` are the global functions on
`U`. -/
theorem additivePresheaf_obj (X : Scheme.{u}) (U : X.Etale) :
    ToType ((additivePresheaf.{u, v} X).obj (op U)) = ULift.{max (u + 1) v} Γ(U.left, ⊤) :=
  rfl

/-- The underlying presheaf of types of `Stacks.ArtinSchreier.additivePresheaf` is the functor of
points of the additive group scheme over `X`, restricted to the small étale site, hence a sheaf:
that functor is representable and the small étale site is subcanonical over `Over X`. -/
theorem isSheaf_forget_additivePresheaf (X : Scheme.{u}) :
    Presieve.IsSheaf X.smallEtaleTopology
      (additivePresheaf.{u, v} X ⋙ CategoryTheory.forget AddCommGrpCat) := by
  have hrep : Presieve.IsSheaf X.smallEtaleTopology
      ((Scheme.Etale.forget X).op ⋙ globalSectionsAdditive X ⋙ forget GrpCat) :=
    have : (globalSectionsAdditive X ⋙ forget GrpCat).IsRepresentable :=
      (additiveGroupBaseChangeRepresentableBy X).isRepresentable
    Scheme.isSheaf_smallEtale_comp_of_isRepresentable X _
  exact (Presieve.isSheaf_iff_of_nat_equiv
    (P₂ := additivePresheaf.{u, v} X ⋙ CategoryTheory.forget AddCommGrpCat)
    (fun {_} => Multiplicative.toAdd.trans Equiv.ulift.symm) (fun _ _ _ _ => rfl)).1 hrep

/-- **The presheaf of global functions is a sheaf of abelian groups on the small étale site.** -/
theorem isSheaf_additivePresheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf X.smallEtaleTopology (additivePresheaf.{u, v} X) :=
  Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _
    (isSheaf_forget_additivePresheaf.{u, v} X)

/-- **`𝐆_a` on the small étale site of a scheme**: the sheaf of abelian groups whose sections
over an étale `X`-scheme `U` are the global functions `Γ(U, 𝒪_U)`. -/
noncomputable def additiveSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  ⟨additivePresheaf.{u, v} X, isSheaf_additivePresheaf.{u, v} X⟩

/-- The underlying presheaf of `Stacks.ArtinSchreier.additiveSheaf` is
`Stacks.ArtinSchreier.additivePresheaf`. -/
@[simp]
theorem additiveSheaf_obj (X : Scheme.{u}) :
    (additiveSheaf.{u, v} X).obj = additivePresheaf.{u, v} X :=
  rfl

/-- The global function `x` on `U`, as a section of `𝐆_a` over `U`. -/
noncomputable def ofSection {X : Scheme.{u}} {U : X.Etale} (x : Γ(U.left, ⊤)) :
    ToType ((additiveSheaf.{u, v} X).obj.obj (op U)) :=
  ULift.up x

/-- Every section of `𝐆_a` over `U` is a global function on `U`. -/
theorem ofSection_surjective {X : Scheme.{u}} {U : X.Etale} :
    Function.Surjective (ofSection.{u, v} (X := X) (U := U)) :=
  fun a => ⟨a.down, rfl⟩

/-- Distinct global functions give distinct sections of `𝐆_a`. -/
theorem ofSection_injective {X : Scheme.{u}} {U : X.Etale} :
    Function.Injective (ofSection.{u, v} (X := X) (U := U)) :=
  fun _ _ h => congrArg ULift.down h

/-- The zero section of `𝐆_a` is the zero function. -/
@[simp]
theorem ofSection_zero {X : Scheme.{u}} {U : X.Etale} :
    ofSection.{u, v} (X := X) (U := U) 0 = 0 :=
  rfl

/-- Restricting the section of `𝐆_a` attached to a global function along a morphism of the small
étale site pulls that function back. -/
@[simp]
theorem map_ofSection {X : Scheme.{u}} {U V : X.Etale} (f : V ⟶ U) (x : Γ(U.left, ⊤)) :
    (additiveSheaf.{u, v} X).obj.map f.op (ofSection x) =
      ofSection (f.left.appTop.hom x) :=
  rfl

/-- The Frobenius endomorphism of the presheaf of rings of global functions on the small étale
site of a scheme on which the prime `p` vanishes. It is natural because ring homomorphisms
preserve `p`-th powers. -/
noncomputable def frobeniusGlobalFunctions (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : globalFunctionsPresheaf X ⟶ globalFunctionsPresheaf X where
  app U := CommRingCat.ofHom
    (frobeniusRingHom _ hp (natCast_eq_zero_of_etale X hX U.unop))
  naturality _ _ _ := by
    ext x
    exact (map_pow _ x p).symm

/-- **The Frobenius endomorphism of `𝐆_a`**, `x ↦ x ^ p`, on the small étale site of a scheme on
which the prime `p` vanishes. -/
noncomputable def frobeniusMap (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : additiveSheaf.{u, v} X ⟶ additiveSheaf.{u, v} X :=
  ⟨Functor.whiskerRight (frobeniusGlobalFunctions X hp hX) additiveCoefficients.{u, v}⟩

/-- **The Frobenius is `x ↦ x ^ p` on sections.** -/
@[simp]
theorem frobeniusMap_app_ofSection (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (frobeniusMap.{u, v} X hp hX).hom.app (op U) (ofSection x) = ofSection (x ^ p) :=
  rfl

/-- **The Artin–Schreier map `F - 1` on `𝐆_a`**, that is `x ↦ x ^ p - x`, on the small étale site
of a scheme on which the prime `p` vanishes. -/
noncomputable def artinSchreierMap (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : additiveSheaf.{u, v} X ⟶ additiveSheaf.{u, v} X :=
  frobeniusMap.{u, v} X hp hX - 𝟙 _

/-- **The Artin–Schreier map is `x ↦ x ^ p - x` on sections.** -/
@[simp]
theorem artinSchreierMap_app_ofSection (X : Scheme.{u}) {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etale) (x : Γ(U.left, ⊤)) :
    (artinSchreierMap.{u, v} X hp hX).hom.app (op U) (ofSection x) = ofSection (x ^ p - x) :=
  rfl

end Stacks.ArtinSchreier

end
