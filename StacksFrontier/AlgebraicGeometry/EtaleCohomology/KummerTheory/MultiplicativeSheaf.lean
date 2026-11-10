module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.SmallEtaleSubcanonical
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcQuasicoherentSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝐆_m` and `μ_n` as abelian sheaves on the small étale site

The multiplicative group of a scheme `X` is the sheaf of abelian groups on the small étale site
of `X` whose sections over an étale `X`-scheme `U` are the invertible global functions
`Γ(U, 𝒪_U)ˣ`, written additively.  This file constructs it, the `n`-th power map on it, and
`μ_n` as the kernel of that map, which is the definition used in the Kummer sequence.

The sheaf condition is representability: the invertible global functions on `X`-schemes are the
functor of points of the multiplicative group scheme over `X`
(`AlgebraicGeometry.multiplicativeGroupBaseChangeRepresentsGlobalUnits`), and the small étale
site is subcanonical over `Over X`
(`AlgebraicGeometry.Scheme.isSheaf_smallEtale_comp_of_isRepresentable`).  No descent argument is
needed, and in particular the structure sheaf of the small étale site is not used.

## Main definitions

* `Stacks.Kummer.multiplicativePresheaf`: the presheaf `U ↦ Γ(U, 𝒪_U)ˣ` of abelian groups.
* `Stacks.Kummer.multiplicativeSheaf`: `𝐆_m` on the small étale site of `X`.
* `Stacks.Kummer.powMap`: the `n`-th power map `𝐆_m ⟶ 𝐆_m`.
* `Stacks.Kummer.rootsOfUnitySheaf`: `μ_n`, the kernel of the `n`-th power map.

## Main results

* `Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget`: a presheaf of abelian groups whose
  underlying presheaf of types is a sheaf is a sheaf.
* `Stacks.Kummer.isSheaf_multiplicativePresheaf`: the sheaf condition for `𝐆_m`.
* `Stacks.Kummer.powMap_app_ofMul`: the `n`-th power map really is `x ↦ xⁿ` on sections.

## Implementation notes

The coefficient category is `AddCommGrpCat.{max (u + 1) v}`, the universe in which this library
computes étale cohomology of a scheme in `Scheme.{u}`; this is where
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology` and
`AlgebraicGeometry.Scheme.wEqualsLocallyBijective_smallEtaleTopology` live, hence where the
category of sheaves is abelian.  Sections of the structure sheaf are in `Type u`, so they are
raised by `AddCommGrpCat.uliftFunctor`; the multiplicative group of a ring is turned into an
additive one by `commGroupAddCommGroupEquivalence`.  Both are type synonyms on the underlying
sets, so the underlying presheaf of types is still the functor of points of the multiplicative
group scheme up to the evident bijection, and the sheaf condition transports along
`CategoryTheory.Presieve.isSheaf_iff_of_nat_equiv`.

`Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget` is the abelian-group analogue of
`Stacks.Sites.isSheaf_ringCat_of_isSheaf_forget`; Mathlib's
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` does not apply, because it requires the
coefficient category to be concrete over the universe `max u (u + 1)` of the site, which is not
the coefficient universe for every `v`.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence,
  where `μ_n` is defined as the kernel of the `n`-th power map on `𝐆_m`.
* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U): the multiplicative
  group scheme, whose functor of points gives the sheaf condition here.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v₁ u₁ u v

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C]

end Stacks.Sites

namespace Stacks.Kummer

/-- The presheaf of abelian groups on the small étale site of `X` whose sections over an étale
`X`-scheme `U` are the invertible global functions `Γ(U, 𝒪_U)ˣ`, written additively and raised
to the coefficient universe of étale cohomology. -/
noncomputable def multiplicativePresheaf (X : Scheme.{u}) :
    X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ ⋙
    forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor ⋙ AddCommGrpCat.uliftFunctor.{max (u + 1) v, u}

/-- Sections of `Stacks.Kummer.multiplicativePresheaf` over `U` are the invertible global
functions on `U`. -/
theorem multiplicativePresheaf_obj (X : Scheme.{u}) (U : X.Etale) :
    ToType ((multiplicativePresheaf.{u, v} X).obj (op U)) =
      ULift.{max (u + 1) v} (Additive (Γ(U.left, ⊤))ˣ) :=
  rfl

/-- The underlying presheaf of types of `Stacks.Kummer.multiplicativePresheaf` is the functor of
points of the multiplicative group scheme over `X`, restricted to the small étale site, hence a
sheaf: that functor is representable and the small étale site is subcanonical over `Over X`. -/
theorem isSheaf_forget_multiplicativePresheaf (X : Scheme.{u}) :
    Presieve.IsSheaf X.smallEtaleTopology
      (multiplicativePresheaf.{u, v} X ⋙ CategoryTheory.forget AddCommGrpCat) := by
  have hrep : Presieve.IsSheaf X.smallEtaleTopology
      ((Scheme.Etale.forget X).op ⋙ globalUnits X ⋙ forget GrpCat) :=
    have : (globalUnits X ⋙ forget GrpCat).IsRepresentable :=
      (multiplicativeGroupBaseChangeRepresentsGlobalUnits X).isRepresentable
    Scheme.isSheaf_smallEtale_comp_of_isRepresentable X _
  exact (Presieve.isSheaf_iff_of_nat_equiv
    (P₂ := multiplicativePresheaf.{u, v} X ⋙ CategoryTheory.forget AddCommGrpCat)
    (fun {_} => Additive.ofMul.trans Equiv.ulift.symm) (fun _ _ _ _ => rfl)).1 hrep

/-- **The presheaf of invertible global functions is a sheaf of abelian groups on the small
étale site.** -/
theorem isSheaf_multiplicativePresheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf X.smallEtaleTopology (multiplicativePresheaf.{u, v} X) :=
  Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _
    (isSheaf_forget_multiplicativePresheaf.{u, v} X)

/-- **`𝐆_m` on the small étale site of a scheme**: the sheaf of abelian groups whose sections
over an étale `X`-scheme `U` are the invertible global functions `Γ(U, 𝒪_U)ˣ`. -/
noncomputable def multiplicativeSheaf (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  ⟨multiplicativePresheaf.{u, v} X, isSheaf_multiplicativePresheaf.{u, v} X⟩

/-- The underlying presheaf of `𝐆_m` is `multiplicativePresheaf X`. -/
@[simp]
theorem multiplicativeSheaf_obj (X : Scheme.{u}) :
    (multiplicativeSheaf.{u, v} X).obj = multiplicativePresheaf.{u, v} X :=
  rfl

/-- The invertible global function `x` on `U`, as a section of `𝐆_m` over `U`. -/
noncomputable def ofUnit {X : Scheme.{u}} {U : X.Etale} (x : (Γ(U.left, ⊤))ˣ) :
    ToType ((multiplicativeSheaf.{u, v} X).obj.obj (op U)) :=
  ULift.up (Additive.ofMul x)

/-- Every section of `𝐆_m` over `U` is an invertible global function on `U`. -/
theorem ofUnit_surjective {X : Scheme.{u}} {U : X.Etale} :
    Function.Surjective (ofUnit.{u, v} (X := X) (U := U)) :=
  fun a => ⟨Additive.toMul a.down, rfl⟩

/-- Distinct invertible global functions give distinct sections of `𝐆_m`. -/
theorem ofUnit_injective {X : Scheme.{u}} {U : X.Etale} :
    Function.Injective (ofUnit.{u, v} (X := X) (U := U)) :=
  fun _ _ h => Additive.ofMul.injective (congrArg ULift.down h)

/-- The zero section of `𝐆_m` is the constant function `1`. -/
@[simp]
theorem ofUnit_one {X : Scheme.{u}} {U : X.Etale} :
    ofUnit.{u, v} (X := X) (U := U) 1 = 0 :=
  rfl

/-- Restricting the section of `𝐆_m` attached to an invertible global function along a morphism
of the small étale site pulls that function back. -/
@[simp]
theorem map_ofUnit {X : Scheme.{u}} {U V : X.Etale} (f : V ⟶ U) (x : (Γ(U.left, ⊤))ˣ) :
    (multiplicativeSheaf.{u, v} X).obj.map f.op (ofUnit x) =
      ofUnit (Units.map f.left.appTop.hom x) :=
  rfl

/-- The `n`-th power map `𝐆_m ⟶ 𝐆_m` on the small étale site.  In the additive notation of the
coefficient category it is multiplication by `n`. -/
noncomputable def powMap (X : Scheme.{u}) (n : ℕ) :
    multiplicativeSheaf.{u, v} X ⟶ multiplicativeSheaf.{u, v} X :=
  n • 𝟙 _

/-- **The `n`-th power map is `x ↦ xⁿ` on sections.** -/
@[simp]
theorem powMap_app_ofUnit (X : Scheme.{u}) (n : ℕ) (U : X.Etale) (x : (Γ(U.left, ⊤))ˣ) :
    (powMap.{u, v} X n).hom.app (op U) (ofUnit x) = ofUnit (x ^ n) := by
  change ULift.up (n • Additive.ofMul x) = ULift.up (Additive.ofMul (x ^ n))
  rw [ofMul_pow]

/-- **`μ_n` on the small étale site of a scheme**: the sheaf of `n`-th roots of unity, defined
as the kernel of the `n`-th power map on `𝐆_m`. -/
@[sga "4 IX 3.0",
  sga "4 XVIII 1.1.1" "i = 1",
  sga "4½ Arcata 2.2.4",
  sga "4½ Arcata 6.1" "partial",
  sga "5 VI 3.2"]
noncomputable def rootsOfUnitySheaf (X : Scheme.{u}) (n : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} :=
  kernel (powMap.{u, v} X n)

/-- The inclusion `μ_n ⟶ 𝐆_m`. -/
noncomputable def rootsOfUnityι (X : Scheme.{u}) (n : ℕ) :
    rootsOfUnitySheaf.{u, v} X n ⟶ multiplicativeSheaf.{u, v} X :=
  kernel.ι _

/-- The inclusion `μ_n ⟶ 𝐆_m` is a monomorphism. -/
instance mono_rootsOfUnityι (X : Scheme.{u}) (n : ℕ) : Mono (rootsOfUnityι.{u, v} X n) :=
  inferInstanceAs (Mono (kernel.ι _))

/-- The inclusion `μ_n ⟶ 𝐆_m` is annihilated by the `n`-th power map. -/
theorem rootsOfUnityι_comp_powMap (X : Scheme.{u}) (n : ℕ) :
    rootsOfUnityι.{u, v} X n ≫ powMap.{u, v} X n = 0 :=
  kernel.condition _

/-- **Sections of `μ_n` are `n`-th roots of unity**: an invertible global function that is the
image of a section of `μ_n` satisfies `xⁿ = 1`.  This is what identifies the kernel of the
`n`-th power map with the sheaf of `n`-th roots of unity. -/
theorem pow_eq_one_of_rootsOfUnitySheaf (X : Scheme.{u}) (n : ℕ) (U : X.Etale)
    (s : ToType ((rootsOfUnitySheaf.{u, v} X n).obj.obj (op U))) (x : (Γ(U.left, ⊤))ˣ)
    (hx : (rootsOfUnityι.{u, v} X n).hom.app (op U) s = ofUnit x) :
    x ^ n = 1 := by
  have h := congrArg (fun (φ : rootsOfUnitySheaf.{u, v} X n ⟶ multiplicativeSheaf.{u, v} X) =>
    φ.hom.app (op U) s) (rootsOfUnityι_comp_powMap.{u, v} X n)
  simp only at h
  rw [show ((rootsOfUnityι.{u, v} X n ≫ powMap.{u, v} X n).hom.app (op U)) s =
      (powMap.{u, v} X n).hom.app (op U)
        ((rootsOfUnityι.{u, v} X n).hom.app (op U) s) from rfl, hx,
    powMap_app_ofUnit] at h
  exact ofUnit_injective.{u, v} (h.trans ofUnit_one.symm)

end Stacks.Kummer

end
