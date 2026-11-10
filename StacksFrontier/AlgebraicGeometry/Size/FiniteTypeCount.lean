module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# How many affine schemes of finite type sit over an affine base

The size cutoff `κ` of a big fppf site bounds the *individual* objects of the site, and the
cardinal arithmetic of `StacksFrontier.AlgebraicGeometry.Size.Cutoff` says which constructions
stay below it. The tools that collapse a family of schemes to a single chart —
`AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le` and
`AlgebraicGeometry.FormalSpace.exists_chart_of_size_le` — want more: one cardinal `μ < κ`
bounding both the *number* of members of the family and the size of each member. This file
supplies the counting half of such a bound in the situation that occurs when one tests a
sheaf on the site against an affine object `T`: the members are affine schemes of finite
type over `T`, and there are at most `ℵ₀ * 2 ^ max ℵ₀ #Γ(T, ⊤)` of them up to isomorphism
over `T`.

The count is the one the Stacks Project makes in Lemma 000P's company: an affine `T`-scheme
of finite type is `Spec` of a quotient of a polynomial ring in finitely many variables over
`Γ(T, ⊤)`, so the isomorphism classes inject into pairs (a number of variables, an ideal of
that polynomial ring). Mathlib already names that index type,
`FGAlgCatSkeleton Γ(T, ⊤)`, and already knows every finite type algebra is a quotient of
such a polynomial ring (`Algebra.FiniteType.iff_quotient_mvPolynomial''`); what is new here
is the cardinality of that index type and the passage from algebras to schemes over `T`.

## Main results

* `Cardinal.mk_fgAlgCatSkeleton_le`: `#(FGAlgCatSkeleton R) ≤ ℵ₀ * 2 ^ max ℵ₀ #R`. An ideal
  of a ring is a subset of it, and a polynomial ring in finitely many variables over `R` has
  at most `max ℵ₀ #R` elements, so there are at most `2 ^ max ℵ₀ #R` ideals for each of the
  countably many numbers of variables.
* `AlgebraicGeometry.AffineFiniteTypeOver.exists_ofSkeleton`: every affine `T`-scheme of
  finite type, `T` affine, is isomorphic over `T` to the model attached to a member of
  `FGAlgCatSkeleton Γ(T, ⊤)`.
* `AlgebraicGeometry.mk_quotient_affineFiniteTypeOver_le`: **the counting lemma.** For `T`
  affine the isomorphism classes of affine `T`-schemes of finite type number at most
  `ℵ₀ * 2 ^ max ℵ₀ #Γ(T, ⊤)`.
* `AlgebraicGeometry.exists_index_affineFiniteTypeOver`: the same bound in the shape the
  chart tools consume — a `Type u` indexing a family of affine `T`-schemes of finite type
  hitting every isomorphism class, whose cardinality obeys the bound.
* `Cardinal.mk_fgAlgCatSkeleton_lt_of_isStrongPrelimit` and
  `AlgebraicGeometry.mk_fgAlgCatSkeleton_sections_lt_of_isStrongPrelimit`: the bound is
  below the cutoff. These are what a consumer uses, and they assume of the cutoff `κ` only
  `ℵ₀ < κ` and `Cardinal.IsStrongPrelimit κ` — the fields
  `AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` and
  `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`. In particular *no* regularity and
  no hypothesis on `κ.ord.cof` is used: closure under powersets alone gives `2 ^ μ < κ` for
  `μ < κ`, and that is the whole of the cardinal arithmetic here.

## Implementation notes

"Isomorphism class of affine `T`-scheme of finite type" is read as a class of the setoid
`AlgebraicGeometry.AffineFiniteTypeOver.isoSetoid` on
`AlgebraicGeometry.AffineFiniteTypeOver T`, the affine schemes carrying a morphism to `T`
locally of finite type, two of them being equivalent when an isomorphism of the underlying
schemes commutes with the structure morphisms. That type lives in `Type (u + 1)`, so the
bound on its quotient is stated with a `Cardinal.lift`. The
unlifted statement is `AlgebraicGeometry.exists_index_affineFiniteTypeOver`, which indexes
the classes by a type of `Type u`; it is the one the chart tools can use, since their index
types are of `Type u`.

The identification of an affine `T`-scheme with the spectrum of a quotient of a polynomial
ring runs through `AlgebraicGeometry.Scheme.isoSpec` and its naturality
`AlgebraicGeometry.Scheme.isoSpec_inv_naturality`; the structure morphism of the model is
`Spec` of the algebra map followed by `T.isoSpec.inv`, since `T` is only isomorphic to
`Spec Γ(T, ⊤)`, not equal to it.

## References

* [Stacks Project, Tag 000P](https://stacks.math.columbia.edu/tag/000P)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public section

open Cardinal CategoryTheory

universe u

namespace Cardinal

/-- The ideals of a polynomial ring in `n` variables over `R` number at most
`2 ^ max ℵ₀ #R`: an ideal is determined by its underlying subset, and the polynomial ring
has at most `max ℵ₀ #R` elements, being a finitely generated `R`-algebra. -/
lemma mk_ideal_mvPolynomial_fin_le (R : Type u) [CommRing R] (n : ℕ) :
    #(Ideal (MvPolynomial (Fin n) R)) ≤ 2 ^ max ℵ₀ #R :=
  calc #(Ideal (MvPolynomial (Fin n) R))
      ≤ #(Set (MvPolynomial (Fin n) R)) :=
        mk_le_of_injective (f := fun I => (I : Set (MvPolynomial (Fin n) R)))
          fun _ _ h => SetLike.coe_injective h
    _ = 2 ^ #(MvPolynomial (Fin n) R) := mk_set
    _ ≤ 2 ^ max ℵ₀ #R := power_le_power_left two_ne_zero
        (mk_le_of_algebra_finiteType R (MvPolynomial (Fin n) R))

/-- **The small skeleton of the finitely generated `R`-algebras has at most
`ℵ₀ * 2 ^ max ℵ₀ #R` members.**

A member of `FGAlgCatSkeleton R` is a number of variables together with an ideal of the
polynomial ring in that many variables over `R`. There are `ℵ₀` choices of the first and, by
`Cardinal.mk_ideal_mvPolynomial_fin_le`, at most `2 ^ max ℵ₀ #R` of the second. -/
lemma mk_fgAlgCatSkeleton_le (R : Type u) [CommRing R] :
    #(FGAlgCatSkeleton R) ≤ ℵ₀ * 2 ^ max ℵ₀ #R := by
  have hinj : Function.Injective
      (fun P : FGAlgCatSkeleton R => (⟨P.n, P.I⟩ : Σ n : ℕ, Ideal (MvPolynomial (Fin n) R))) := by
    rintro ⟨n, I⟩ ⟨m, J⟩ h
    obtain ⟨rfl, rfl⟩ := Sigma.mk.injEq .. ▸ h
    rfl
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_sigma]
  refine (sum_le_sum _ (fun _ => 2 ^ max ℵ₀ #R)
    fun n => mk_ideal_mvPolynomial_fin_le R n).trans ?_
  simp [sum_const]

/-- The bound of `Cardinal.mk_fgAlgCatSkeleton_le` lies below a cutoff cardinal.

The hypotheses on `κ` are exactly `ℵ₀ < κ` and closure under powersets; nothing about the
cofinality of `κ`, and in particular no regularity, is used. Indeed
`max ℵ₀ #R ≤ max ℵ₀ μ < κ`, so `2 ^ max ℵ₀ μ < κ` by closure under powersets, and the
bound is at most the product of that infinite cardinal with itself, which is itself. -/
lemma mk_fgAlgCatSkeleton_lt_of_isStrongPrelimit {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hstrong : κ.IsStrongPrelimit) {μ : Cardinal.{u}} (hμ : μ < κ)
    (R : Type u) [CommRing R] (hR : #R ≤ μ) :
    #(FGAlgCatSkeleton R) < κ := by
  have hpow : ℵ₀ ≤ 2 ^ max ℵ₀ μ :=
    ((cantor ℵ₀).trans_le (power_le_power_left two_ne_zero (le_max_left _ _))).le
  calc #(FGAlgCatSkeleton R)
      ≤ ℵ₀ * 2 ^ max ℵ₀ #R := mk_fgAlgCatSkeleton_le R
    _ ≤ 2 ^ max ℵ₀ μ * 2 ^ max ℵ₀ μ :=
        mul_le_mul' hpow (power_le_power_left two_ne_zero (max_le_max le_rfl hR))
    _ = 2 ^ max ℵ₀ μ := mul_eq_self hpow
    _ < κ := hstrong (max_lt hκ hμ)

end Cardinal

namespace AlgebraicGeometry

/-- An **affine `T`-scheme of finite type**: an affine scheme together with a morphism to
`T` that is locally of finite type. -/
structure AffineFiniteTypeOver (T : Scheme.{u}) : Type (u + 1) where
  /-- The underlying scheme. -/
  obj : Scheme.{u}
  /-- The structure morphism to `T`. -/
  hom : obj ⟶ T
  /-- The underlying scheme is affine. -/
  isAffine : IsAffine obj
  /-- The structure morphism is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType hom

namespace AffineFiniteTypeOver

attribute [instance] isAffine locallyOfFiniteType

/-- Two affine `T`-schemes of finite type are equivalent when they are isomorphic over `T`:
there is an isomorphism of the underlying schemes commuting with the structure
morphisms. -/
def isoSetoid (T : Scheme.{u}) : Setoid (AffineFiniteTypeOver T) where
  r V W := ∃ e : V.obj ≅ W.obj, e.hom ≫ W.hom = V.hom
  iseqv :=
    { refl _ := ⟨Iso.refl _, by simp⟩
      symm := fun ⟨e, he⟩ => ⟨e.symm, by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]⟩
      trans := fun ⟨e, he⟩ ⟨e', he'⟩ =>
        ⟨e.trans e', by rw [Iso.trans_hom, Category.assoc, he', he]⟩ }

variable (T : Scheme.{u}) [IsAffine T]

/-- The affine `T`-scheme of finite type attached to a finitely generated
`Γ(T, ⊤)`-algebra `A`: the spectrum of `A`, with structure morphism `Spec` of the algebra
map followed by the identification of `Spec Γ(T, ⊤)` with `T`. -/
noncomputable def ofAlgebra (A : Type u) [CommRing A] [Algebra Γ(T, ⊤) A]
    [Algebra.FiniteType Γ(T, ⊤) A] : AffineFiniteTypeOver T where
  obj := Spec (CommRingCat.of A)
  hom := Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) A)) ≫ T.isoSpec.inv
  isAffine := inferInstance
  locallyOfFiniteType :=
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) A))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
    inferInstance

/-- The affine `T`-scheme of finite type attached to a member of Mathlib's small skeleton of
the finitely generated `Γ(T, ⊤)`-algebras: the spectrum of the quotient of the polynomial
ring in `P.n` variables by the ideal `P.I`. -/
noncomputable def ofSkeleton (P : FGAlgCatSkeleton Γ(T, ⊤)) : AffineFiniteTypeOver T :=
  ofAlgebra T (MvPolynomial (Fin P.n) Γ(T, ⊤) ⧸ P.I)

/-- **An affine `T`-scheme of finite type is the model of any of its algebras of global
sections.** If the global sections of `V` are `Γ(T, ⊤)`-isomorphic to `A`, with the
`Γ(T, ⊤)`-algebra structure on `Γ(V.obj, ⊤)` read off the structure morphism of `V`, then
`V` is isomorphic over `T` to `AlgebraicGeometry.AffineFiniteTypeOver.ofAlgebra T A`.

The isomorphism of schemes is `Spec` of the isomorphism of rings followed by the
identification of `V.obj` with the spectrum of its global sections; that it commutes with
the structure morphisms is the naturality
`AlgebraicGeometry.Scheme.isoSpec_inv_naturality` together with the fact that an algebra
isomorphism commutes with the algebra maps. -/
theorem isoSetoid_ofAlgebra (V : AffineFiniteTypeOver T) (A : Type u) [CommRing A]
    [Algebra Γ(T, ⊤) A] [Algebra.FiniteType Γ(T, ⊤) A]
    [Algebra Γ(T, ⊤) Γ(V.obj, ⊤)]
    (halg : algebraMap Γ(T, ⊤) Γ(V.obj, ⊤) = V.hom.appTop.hom)
    (e : A ≃ₐ[Γ(T, ⊤)] Γ(V.obj, ⊤)) :
    isoSetoid T (ofAlgebra T A) V := by
  set ε : CommRingCat.of A ≅ CommRingCat.of Γ(V.obj, ⊤) := e.toRingEquiv.toCommRingCatIso
    with hε
  have hcomp : V.hom.appTop ≫ ε.inv = CommRingCat.ofHom (algebraMap Γ(T, ⊤) A) := by
    ext x
    rw [hε]
    change e.symm (V.hom.appTop.hom x) = algebraMap Γ(T, ⊤) A x
    rw [← halg]
    exact e.symm.commutes x
  refine ⟨(Scheme.Spec.mapIso ε.op).symm ≪≫ V.obj.isoSpec.symm, ?_⟩
  change Spec.map ε.inv ≫ V.obj.isoSpec.inv ≫ V.hom
      = Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) A)) ≫ T.isoSpec.inv
  rw [← Scheme.isoSpec_inv_naturality, ← Spec.map_comp_assoc, hcomp]

/-- **Every affine `T`-scheme of finite type over an affine base is one of the models.**

Its ring of global sections is a finitely generated `Γ(T, ⊤)`-algebra, hence is
`Γ(T, ⊤)`-isomorphic to a quotient of a polynomial ring in finitely many variables
(`Algebra.FiniteType.iff_quotient_mvPolynomial''`), and
`AlgebraicGeometry.AffineFiniteTypeOver.isoSetoid_ofAlgebra` turns that algebra
isomorphism into an isomorphism over `T`. -/
theorem exists_ofSkeleton (V : AffineFiniteTypeOver T) :
    ∃ P : FGAlgCatSkeleton Γ(T, ⊤), isoSetoid T (ofSkeleton T P) V := by
  let : Algebra Γ(T, ⊤) Γ(V.obj, ⊤) := V.hom.appTop.hom.toAlgebra
  have hFT : Algebra.FiniteType Γ(T, ⊤) Γ(V.obj, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := V.hom)).mp
      V.locallyOfFiniteType
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  exact ⟨⟨n, RingHom.ker φ⟩, isoSetoid_ofAlgebra T V _ rfl
    (Ideal.quotientKerAlgEquivOfSurjective hφ)⟩

end AffineFiniteTypeOver

/-- **The counting lemma, in the shape the chart tools consume.** For `T` an affine scheme
there is a family of affine `T`-schemes of finite type, indexed by a type of `Type u` of
cardinality at most `ℵ₀ * 2 ^ max ℵ₀ #Γ(T, ⊤)`, meeting every isomorphism class of affine
`T`-schemes of finite type.

The index type is Mathlib's small skeleton `FGAlgCatSkeleton Γ(T, ⊤)` of the finitely
generated `Γ(T, ⊤)`-algebras, counted by `Cardinal.mk_fgAlgCatSkeleton_le`. -/
theorem exists_index_affineFiniteTypeOver (T : Scheme.{u}) [IsAffine T] :
    ∃ (I : Type u) (V : I → AffineFiniteTypeOver T),
      #I ≤ ℵ₀ * 2 ^ max ℵ₀ #Γ(T, ⊤) ∧
      ∀ W : AffineFiniteTypeOver T, ∃ i, ∃ e : (V i).obj ≅ W.obj, e.hom ≫ W.hom = (V i).hom :=
  ⟨FGAlgCatSkeleton Γ(T, ⊤), AffineFiniteTypeOver.ofSkeleton T,
    Cardinal.mk_fgAlgCatSkeleton_le _, fun W => AffineFiniteTypeOver.exists_ofSkeleton T W⟩

/-- **The counting lemma.** For `T` an affine scheme, the affine `T`-schemes of finite type
number at most `ℵ₀ * 2 ^ max ℵ₀ #Γ(T, ⊤)` up to isomorphism over `T`.

The classes are covered by the models attached to the members of Mathlib's small skeleton
`FGAlgCatSkeleton Γ(T, ⊤)` of the finitely generated `Γ(T, ⊤)`-algebras
(`AlgebraicGeometry.AffineFiniteTypeOver.exists_ofSkeleton`), and that type is counted by
`Cardinal.mk_fgAlgCatSkeleton_le`. The `Cardinal.lift` is bookkeeping: the affine
`T`-schemes of finite type form a type of `Type (u + 1)`, while the bound is a cardinal of
`Type u`. -/
theorem mk_quotient_affineFiniteTypeOver_le (T : Scheme.{u}) [IsAffine T] :
    #(Quotient (AffineFiniteTypeOver.isoSetoid T)) ≤
      Cardinal.lift.{u + 1} (ℵ₀ * 2 ^ max ℵ₀ #Γ(T, ⊤)) := by
  have hsurj : Function.Surjective
      fun P : ULift.{u + 1} (FGAlgCatSkeleton Γ(T, ⊤)) =>
        Quotient.mk (AffineFiniteTypeOver.isoSetoid T)
          (AffineFiniteTypeOver.ofSkeleton T P.down) := by
    intro q
    induction q using Quotient.ind with
    | _ V =>
      obtain ⟨P, hP⟩ := AffineFiniteTypeOver.exists_ofSkeleton T V
      exact ⟨⟨P⟩, Quotient.sound hP⟩
  calc #(Quotient (AffineFiniteTypeOver.isoSetoid T))
      ≤ #(ULift.{u + 1} (FGAlgCatSkeleton Γ(T, ⊤))) := Cardinal.mk_le_of_surjective hsurj
    _ = Cardinal.lift.{u + 1} #(FGAlgCatSkeleton Γ(T, ⊤)) := Cardinal.mk_uLift _
    _ ≤ Cardinal.lift.{u + 1} (ℵ₀ * 2 ^ max ℵ₀ #Γ(T, ⊤)) :=
        Cardinal.lift_le.mpr (Cardinal.mk_fgAlgCatSkeleton_le _)

/-- **The count of affine `T`-schemes of finite type lies below the cutoff.** If the affine
scheme `T` is an object of the category of schemes cut off at `κ`, so is every affine
`T`-scheme of finite type, and there are fewer than `κ` of them up to isomorphism over `T`.

This is the form a chart tool consumes: it provides the cardinal `μ < κ` bounding the index
type of the family of `AlgebraicGeometry.exists_index_affineFiniteTypeOver`.

The hypotheses on `κ` are `ℵ₀ < κ` and `Cardinal.IsStrongPrelimit κ`, i.e. the fields
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` and
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit` of a big fppf site. No regularity of
`κ` and no hypothesis on `κ.ord.cof` is used. -/
theorem mk_fgAlgCatSkeleton_sections_lt_of_isStrongPrelimit {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hstrong : κ.IsStrongPrelimit) (T : Scheme.{u}) [IsAffine T] (hT : T.size < κ) :
    #(FGAlgCatSkeleton Γ(T, ⊤)) < κ :=
  Cardinal.mk_fgAlgCatSkeleton_lt_of_isStrongPrelimit hκ hstrong hT _
    (T.mk_sections_le_size ⟨⊤, isAffineOpen_top T⟩)

end AlgebraicGeometry

end
