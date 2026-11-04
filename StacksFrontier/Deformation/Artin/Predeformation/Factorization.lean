module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Artinian.Ring
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Predeformation

/-!
# The category `𝒞_Λ` as the category of factorizations of a field-valued point

Let `S` be a locally Noetherian scheme and let `x : Spec k ⟶ S` be a field-valued point of
finite type. The category `𝒞_Λ` of Artinian local `Λ`-algebras with residue field `k` is
built from a chosen affine open `Spec Λ ⊂ S` through which `x` factors, so a priori it depends
on that choice. This file shows that it does not: `𝒞_Λ` is equivalent to the opposite of the
category of factorizations `Spec k ⟶ Spec A ⟶ S` of `x` by the spectrum of an Artinian local
ring whose residue field is identified with `k`, and that category refers only to `x`.

The objects of the factorization category are the `Deformation.Artin.ArtinianLocalFactorization`
already attached to `x`; a morphism is a morphism of the middle terms over `S` commuting with
the two arrows out of `Spec k`. Sending an object `A` of `𝒞_Λ` to the factorization
`Spec k ⟶ Spec A ⟶ Spec Λ ⟶ S` is fully faithful because `Spec` is fully faithful on affines
and `Spec Λ ⟶ S` is a monomorphism, and essentially surjective because the spectrum of an
Artinian local ring is a one-point space: its image in `S` is the image of the closed point of
`Spec k`, hence lies in the chosen affine open, so `Spec A ⟶ S` factors through `Spec Λ` and
that factorization is the `Λ`-algebra structure sought.

## Main definitions

* `Deformation.Artin.ArtinianLocalFactorization.Hom` — a morphism of factorizations, and the
  category structure it defines.
* `Deformation.Artin.ArtinianLocalFactorization.ofAlg` — the factorization attached to an
  object of `𝒞_Λ`, and `Deformation.Artin.ArtinianLocalFactorization.homOfAlg` its action on
  morphisms.
* `Deformation.Artin.factorizationComparison` — the resulting functor from `𝒞_Λ` to the
  opposite of the category of factorizations.

## Main results

* `Deformation.Artin.factorizationEquivalence`: `𝒞_Λ` is equivalent to the opposite of the
  category of factorizations of `x`.
* `Deformation.Artin.artinianLocalAlgCatEquiv`: consequently `𝒞_Λ` is independent, up to
  canonical equivalence, of the choice of the affine open `Spec Λ ⊂ S`.

## Implementation notes

The source picks the affine open so that the ring map `Λ ⟶ k` is finite, which is what makes
`𝒞_Λ` fit the classical setting of formal deformation theory. Finiteness plays no part in the
comparison proved here, so it is not assumed: the hypotheses are that `Spec Λ ⟶ S` is an open
immersion and that `x` factors through it by way of the given algebra structure on `k`.

The direction of the arrows is the source's. A morphism `A ⟶ A'` of `𝒞_Λ` is an algebra map,
so it induces `Spec A' ⟶ Spec A`; the factorization category therefore computes the *opposite*
of `𝒞_Λ`. Locality of the ring map is not an extra condition to check when going back: a ring
map between objects of `𝒞_Λ` commuting with the maps to `k` carries nonunits to nonunits, as
`Deformation.Artin.isLocalHom_of_comp_residueMap` records.

## References

* [Stacks Project, Tag 07T2](https://stacks.math.columbia.edu/tag/07T2)
* [Stacks Project, Tag 07T3](https://stacks.math.columbia.edu/tag/07T3)
* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
-/

@[expose] public section

namespace Deformation.Artin

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

noncomputable section

/-! ### The category of factorizations of a field-valued point -/

namespace ArtinianLocalFactorization

variable {S : Scheme.{u}} {k : Type u} [Field k] {x : Spec (CommRingCat.of k) ⟶ S}
  [IsLocallyNoetherian S] [LocallyOfFiniteType x] [QuasiCompact x]

/-- The ring map `A ⟶ k` attached to a factorization: the residue map of `A` followed by
the chosen identification of its residue field with `k`. -/
public def residueHom (a : ArtinianLocalFactorization S k x) : a.carrier →+* k :=
  a.residueEquiv.toRingHom.comp (residue a.carrier)

/-- The first arrow `Spec k ⟶ Spec A` of a factorization. -/
public def point (a : ArtinianLocalFactorization S k x) :
    Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of a.carrier) :=
  Spec.map (CommRingCat.ofHom a.residueHom)

/-- The two arrows of a factorization compose to the point being factored. -/
public theorem point_comp_toBase (a : ArtinianLocalFactorization S k x) :
    a.point ≫ a.toBase = x := a.fac

/-- A morphism of factorizations is a morphism of the middle terms over `S` compatible
with the two arrows out of `Spec k`. -/
@[ext]
public structure Hom (a b : ArtinianLocalFactorization S k x) where
  /-- The morphism of the middle terms. -/
  base : Spec (CommRingCat.of a.carrier) ⟶ Spec (CommRingCat.of b.carrier)
  /-- It is a morphism over `S`. -/
  over_base : base ≫ b.toBase = a.toBase
  /-- It is compatible with the arrows out of `Spec k`. -/
  over_point : a.point ≫ base = b.point

/-- Factorizations of a field-valued point form a category: composition is composition of
the morphisms of the middle terms. -/
public instance : Category (ArtinianLocalFactorization S k x) where
  Hom := Hom
  id a := ⟨𝟙 _, by simp, by simp⟩
  comp f g := ⟨f.base ≫ g.base, by rw [Category.assoc, g.over_base, f.over_base],
    by rw [← Category.assoc, f.over_point, g.over_point]⟩

/-- The middle-term morphism of an identity is an identity. -/
@[simp]
public theorem id_base (a : ArtinianLocalFactorization S k x) :
    Hom.base (𝟙 a) = 𝟙 _ := rfl

/-- The middle-term morphism of a composite is the composite of the middle-term
morphisms. -/
@[simp]
public theorem comp_base {a b c : ArtinianLocalFactorization S k x} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).base = f.base ≫ g.base := rfl

end ArtinianLocalFactorization

/-! ### The comparison functor from `𝒞_Λ` -/

section

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {S : Scheme.{u}} {x : Spec (CommRingCat.of k) ⟶ S}
  [IsLocallyNoetherian S] [LocallyOfFiniteType x] [QuasiCompact x]
variable (iΛ : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion iΛ]
variable (hiΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ = x)

/-- The map to `k` attached to an object of `𝒞_Λ` restricts to the structure map of `k`
on `Λ`. -/
public theorem residueMap_comp_algebraMap_artinianLocalAlg (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (residueMap A).comp (algebraMap Λ A) = algebraMap Λ k := by
  ext l
  exact A.residueEquiv.commutes l

include hiΛ in
/-- The factorization `Spec k ⟶ Spec A ⟶ Spec Λ ⟶ S` attached to an object of `𝒞_Λ`. -/
public def ArtinianLocalFactorization.ofAlg (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    ArtinianLocalFactorization S k x where
  carrier := A
  residueEquiv := A.residueEquiv.toRingEquiv
  toBase := Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ
  fac := by
    rw [← hiΛ]
    change Spec.map (CommRingCat.ofHom (residueMap A)) ≫ _ ≫ _ = _
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      residueMap_comp_algebraMap_artinianLocalAlg]

omit [IsOpenImmersion iΛ] in
/-- The map to `k` of the attached factorization is the one attached to the object
of `𝒞_Λ`. -/
@[simp]
public theorem ArtinianLocalFactorization.ofAlg_residueHom
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (ArtinianLocalFactorization.ofAlg (x := x) iΛ hiΛ A).residueHom = residueMap A := rfl

omit [IsOpenImmersion iΛ] in
/-- The first arrow of the attached factorization. -/
@[simp]
public theorem ArtinianLocalFactorization.ofAlg_point
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (ArtinianLocalFactorization.ofAlg (x := x) iΛ hiΛ A).point =
      Spec.map (CommRingCat.ofHom (residueMap A)) := rfl

omit [IsOpenImmersion iΛ] in
/-- The second arrow of the attached factorization. -/
@[simp]
public theorem ArtinianLocalFactorization.ofAlg_toBase
    (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    (ArtinianLocalFactorization.ofAlg (x := x) iΛ hiΛ A).toBase =
      Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ := rfl

omit [IsLocallyNoetherian S] in
/-- The spectrum of a morphism of `𝒞_Λ` is a morphism over `S`. -/
public theorem spec_algebraMap_comm {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) :
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ := by
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  ext l
  exact f.hom.commutes l

/-- The spectrum of a morphism of `𝒞_Λ` is compatible with the arrows out of `Spec k`. -/
public theorem spec_residueMap_comm {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) :
    Spec.map (CommRingCat.ofHom (residueMap B)) ≫
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom (residueMap A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact residueMap_comp f

/-- The spectrum of an identity of `𝒞_Λ` is an identity. -/
public theorem spec_id_hom (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Spec.map (CommRingCat.ofHom (𝟙 A : A ⟶ A).hom.toRingHom) =
      𝟙 (Spec (CommRingCat.of A.carrier)) := by
  rw [ArtinianLocalAlgCat.id_hom]
  simp

/-- The spectrum of a composite of `𝒞_Λ` is the composite in the reversed order. -/
public theorem spec_comp_hom {A B C : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    Spec.map (CommRingCat.ofHom (f ≫ g).hom.toRingHom) =
      Spec.map (CommRingCat.ofHom g.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom f.hom.toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ArtinianLocalAlgCat.comp_hom]
  rfl

include hiΛ in
/-- A morphism of `𝒞_Λ`, read as a morphism of the attached factorizations in the
reversed direction. -/
public def ArtinianLocalFactorization.homOfAlg
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) :
    ArtinianLocalFactorization.ofAlg (x := x) iΛ hiΛ B ⟶
      ArtinianLocalFactorization.ofAlg (x := x) iΛ hiΛ A where
  base := Spec.map (CommRingCat.ofHom f.hom.toRingHom)
  over_base := spec_algebraMap_comm iΛ f
  over_point := spec_residueMap_comm f

/-- The middle-term morphism attached to a morphism of `𝒞_Λ` is its spectrum. -/
@[simp]
public theorem ArtinianLocalFactorization.homOfAlg_base
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) :
    (ArtinianLocalFactorization.homOfAlg (x := x) iΛ hiΛ f).base =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := rfl

/-- The construction takes identities to identities. -/
public theorem ArtinianLocalFactorization.homOfAlg_id (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    ArtinianLocalFactorization.homOfAlg (x := x) iΛ hiΛ (𝟙 A) = 𝟙 _ :=
  ArtinianLocalFactorization.Hom.ext (spec_id_hom A)

/-- The construction reverses composition. -/
public theorem ArtinianLocalFactorization.homOfAlg_comp
    {A B C : ArtinianLocalAlgCat.{u, u, u} Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    ArtinianLocalFactorization.homOfAlg (x := x) iΛ hiΛ (f ≫ g) =
      ArtinianLocalFactorization.homOfAlg iΛ hiΛ g ≫
        ArtinianLocalFactorization.homOfAlg iΛ hiΛ f :=
  ArtinianLocalFactorization.Hom.ext (spec_comp_hom f g)

include hiΛ in
/-- The comparison functor from `𝒞_Λ` to the opposite of the category of factorizations. -/
public def factorizationComparison :
    ArtinianLocalAlgCat.{u, u, u} Λ k ⥤ (ArtinianLocalFactorization S k x)ᵒᵖ where
  obj A := Opposite.op (ArtinianLocalFactorization.ofAlg iΛ hiΛ A)
  map f := (ArtinianLocalFactorization.homOfAlg iΛ hiΛ f).op
  map_id A := by rw [ArtinianLocalFactorization.homOfAlg_id]; rfl
  map_comp f g := by rw [ArtinianLocalFactorization.homOfAlg_comp]; rfl

/-- The comparison functor is faithful: a morphism of `𝒞_Λ` is determined by the
morphism of affine schemes it induces. -/
public instance : (factorizationComparison (x := x) iΛ hiΛ).Faithful where
  map_injective {A B} {f g} h := by
    have h1 : ArtinianLocalFactorization.homOfAlg (x := x) iΛ hiΛ f =
        ArtinianLocalFactorization.homOfAlg iΛ hiΛ g := Quiver.Hom.op_inj h
    have h2 : Spec.map (CommRingCat.ofHom f.hom.toRingHom) =
        Spec.map (CommRingCat.ofHom g.hom.toRingHom) :=
      congrArg ArtinianLocalFactorization.Hom.base h1
    have h3 : f.hom.toRingHom = g.hom.toRingHom := by
      simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    exact ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a => DFunLike.congr_fun h3 a)

/-- A ring map between objects of `𝒞_Λ` compatible with the maps to `k` is local: an element
of the maximal ideal has residue zero, so its image has residue zero and is a nonunit. -/
public theorem isLocalHom_of_comp_residueMap {A B : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (ψ : A.carrier →+* B.carrier) (h : (residueMap B).comp ψ = residueMap A) :
    IsLocalHom ψ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hcon
  have h0 : residue A.carrier a = 0 :=
    (residue_eq_zero_iff a).mpr ((mem_maximalIdeal a).mpr hcon)
  have hB : residueMap B (ψ a) = 0 := by
    rw [← RingHom.comp_apply, h]
    simp [residueMap, h0]
  have h0B : residue B.carrier (ψ a) = 0 :=
    B.residueEquiv.injective (by simpa [residueMap] using hB)
  exact (mem_maximalIdeal _).mp ((residue_eq_zero_iff _).mp h0B) ha

/-- The comparison functor is full: a morphism of the middle terms over `S` compatible with
the arrows out of `Spec k` is the spectrum of a morphism of `𝒞_Λ`. -/
public instance : (factorizationComparison (x := x) iΛ hiΛ).Full where
  map_surjective {A B} y := by
    haveI : Mono iΛ := IsOpenImmersion.mono iΛ
    set g := y.unop
    let ψ : CommRingCat.of A.carrier ⟶ CommRingCat.of B.carrier :=
      (Spec.fullyFaithful.preimage g.base).unop
    have hψ : Spec.map ψ = g.base := Spec.map_preimage_unop g.base
    have hb : Spec.map ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ =
        Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫ iΛ := by
      rw [hψ]
      exact g.over_base
    rw [← Category.assoc, ← Spec.map_comp] at hb
    have halg : ψ.hom.comp (algebraMap Λ A) = algebraMap Λ B := by
      simpa using congrArg CommRingCat.Hom.hom
        (Spec.map_injective ((cancel_mono iΛ).mp hb))
    have hp : Spec.map (CommRingCat.ofHom (residueMap B)) ≫ Spec.map ψ =
        Spec.map (CommRingCat.ofHom (residueMap A)) := by
      rw [hψ]
      exact g.over_point
    rw [← Spec.map_comp] at hp
    have hres : (residueMap B).comp ψ.hom = residueMap A := by
      simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective hp)
    refine ⟨⟨⟨ψ.hom, DFunLike.congr_fun halg⟩,
      isLocalHom_of_comp_residueMap ψ.hom hres, DFunLike.congr_fun hres⟩, ?_⟩
    apply Quiver.Hom.unop_inj
    refine ArtinianLocalFactorization.Hom.ext ?_
    change Spec.map (CommRingCat.ofHom ψ.hom) = g.base
    rw [CommRingCat.ofHom_hom]
    exact hψ

include hiΛ in
omit [IsOpenImmersion iΛ] in
/-- The middle term of a factorization maps into the chosen affine open: the spectrum of an
Artinian local ring is a one-point space, so that image is the image of the closed point of
`Spec k`, which lies in the open by hypothesis. -/
public theorem range_toBase_subset (a : ArtinianLocalFactorization S k x) :
    Set.range a.toBase.base ⊆ Set.range iΛ.base := by
  rintro p ⟨q, rfl⟩
  have : Subsingleton (Spec (CommRingCat.of a.carrier)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum a.carrier))
  obtain ⟨o⟩ : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have hq : a.point.base o = q := Subsingleton.elim _ _
  refine ⟨(Spec.map (CommRingCat.ofHom (algebraMap Λ k))).base o, ?_⟩
  calc iΛ.base ((Spec.map (CommRingCat.ofHom (algebraMap Λ k))).base o)
      = (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ).base o :=
        (Scheme.Hom.comp_apply _ _ _).symm
    _ = (a.point ≫ a.toBase).base o := by rw [a.point_comp_toBase, hiΛ]
    _ = a.toBase.base (a.point.base o) := Scheme.Hom.comp_apply _ _ _
    _ = a.toBase.base q := by rw [hq]

/-- The comparison functor is essentially surjective: the middle term of a factorization
carries the `Λ`-algebra structure given by the factorization of `Spec A ⟶ S` through the
chosen affine open, and that makes it an object of `𝒞_Λ` with the given factorization. -/
public instance : (factorizationComparison (x := x) iΛ hiΛ).EssSurj where
  mem_essImage Y := by
    haveI : Mono iΛ := IsOpenImmersion.mono iΛ
    set a := Y.unop
    let l : Spec (CommRingCat.of a.carrier) ⟶ Spec (CommRingCat.of Λ) :=
      IsOpenImmersion.lift iΛ a.toBase (range_toBase_subset iΛ hiΛ a)
    have hl : l ≫ iΛ = a.toBase := IsOpenImmersion.lift_fac _ _ _
    let φ : CommRingCat.of Λ ⟶ CommRingCat.of a.carrier :=
      (Spec.fullyFaithful.preimage l).unop
    have hφ : Spec.map φ = l := Spec.map_preimage_unop l
    letI : Algebra Λ a.carrier := φ.hom.toAlgebra
    have hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ a.carrier)) ≫ iΛ = a.toBase := by
      change Spec.map (CommRingCat.ofHom φ.hom) ≫ iΛ = a.toBase
      rw [CommRingCat.ofHom_hom, hφ, hl]
    have hcomm : a.residueHom.comp (algebraMap Λ a.carrier) = algebraMap Λ k := by
      have h1 : Spec.map (CommRingCat.ofHom a.residueHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ a.carrier)) ≫ iΛ =
          Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
        rw [hbase]
        exact a.point_comp_toBase.trans hiΛ.symm
      rw [← Category.assoc, ← Spec.map_comp] at h1
      simpa using congrArg CommRingCat.Hom.hom
        (Spec.map_injective ((cancel_mono iΛ).mp h1))
    let A₀ : ArtinianLocalAlgCat.{u, u, u} Λ k :=
      { carrier := a.carrier
        algebra := φ.hom.toAlgebra
        residueEquiv :=
          { a.residueEquiv with commutes' := DFunLike.congr_fun hcomm } }
    have htoBase : (ArtinianLocalFactorization.ofAlg (x := x) iΛ hiΛ A₀).toBase = a.toBase :=
      hbase
    have hpoint : (ArtinianLocalFactorization.ofAlg (x := x) iΛ hiΛ A₀).point = a.point := rfl
    have e : a ≅ ArtinianLocalFactorization.ofAlg (x := x) iΛ hiΛ A₀ :=
      { hom := { base := 𝟙 _
                 over_base := (Category.id_comp _).trans htoBase
                 over_point := (Category.comp_id _).trans hpoint.symm }
        inv := { base := 𝟙 _
                 over_base := (Category.id_comp _).trans htoBase.symm
                 over_point := (Category.comp_id _).trans hpoint }
        hom_inv_id := ArtinianLocalFactorization.Hom.ext (Category.id_comp _)
        inv_hom_id := ArtinianLocalFactorization.Hom.ext (Category.id_comp _) }
    exact ⟨A₀, ⟨e.op⟩⟩

/-- Being full, faithful and essentially surjective, the comparison functor is an
equivalence. -/
public instance : (factorizationComparison (x := x) iΛ hiΛ).IsEquivalence := { }

include hiΛ in
/-- **The category `𝒞_Λ` is equivalent to the opposite of the category of factorizations
`Spec k ⟶ Spec A ⟶ S` of the given point by the spectrum of an Artinian local ring with
residue field identified with `k`.** -/
@[stacks 07T2 "the category 𝒞_Λ is equivalent to the opposite of the category of \
factorizations Spec k ⟶ Spec A ⟶ S of the point, with A Artinian local and its residue \
field identified with k"]
public def factorizationEquivalence :
    ArtinianLocalAlgCat.{u, u, u} Λ k ≌ (ArtinianLocalFactorization S k x)ᵒᵖ :=
  (factorizationComparison iΛ hiΛ).asEquivalence

end

/-! ### Independence of the chosen affine open -/

section

variable {Λ Λ' k : Type u} [CommRing Λ] [CommRing Λ'] [Field k] [Algebra Λ k] [Algebra Λ' k]
variable {S : Scheme.{u}} {x : Spec (CommRingCat.of k) ⟶ S}
  [IsLocallyNoetherian S] [LocallyOfFiniteType x] [QuasiCompact x]
variable (iΛ : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion iΛ]
  (hiΛ : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ = x)
variable (iΛ' : Spec (CommRingCat.of Λ') ⟶ S) [IsOpenImmersion iΛ']
  (hiΛ' : Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ' = x)

include hiΛ hiΛ' in
/-- **The category `𝒞_Λ` does not depend, up to canonical equivalence, on the choice of the
affine open `Spec Λ ⊂ S` through which the point factors.** Both are equivalent to the
opposite of the category of factorizations of the point, which refers only to the point. -/
@[stacks 07T2 "the category 𝒞_Λ is independent, up to canonical equivalence, of the choice \
of the affine open Spec Λ ⊂ S the point factors through"]
public def artinianLocalAlgCatEquiv :
    ArtinianLocalAlgCat.{u, u, u} Λ k ≌ ArtinianLocalAlgCat.{u, u, u} Λ' k :=
  (factorizationEquivalence (x := x) iΛ hiΛ).trans
    (factorizationEquivalence (x := x) iΛ' hiΛ').symm

end

end

end Deformation.Artin
