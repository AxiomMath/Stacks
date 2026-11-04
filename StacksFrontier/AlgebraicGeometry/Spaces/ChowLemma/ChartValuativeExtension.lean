module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ValuativeCriteria

/-!
# Enlarging the valuation ring of a valuative square until a given chart carries a lift

Starting from a valuative square `q` for a morphism `f : X ⟶ Y` and from any flat surjective
morphism `c : yoneda.obj W ⟶ Y` out of an object of the site, there is a dominating extension of
`q` — a field extension of `q.K` and a valuation ring of it dominating `q.R` — together with a
morphism from the spectrum of the enlarged valuation ring to `W` lying over the bottom edge of
the enlarged square.

## Main definitions

* `AlgebraicGeometry.Space.dominatingExtensionOfRingHom`: the dominating extension of a valuative
  square attached to a local homomorphism of valuation rings compatible with a homomorphism of
  fraction fields.

## Main results

* `AlgebraicGeometry.Space.exists_dominatingExtension_lift_of_isFlat_of_isSurjective`: the
  bottom edge of a valuative square lifts through any flat surjective chart after a dominating
  extension of the valuation ring.

## References

* [Stacks Project, Tag 03IX](https://stacks.math.columbia.edu/tag/03IX)
* [Stacks Project, Tag 089F](https://stacks.math.columbia.edu/tag/089F)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- An injection of rings keeps the spectrum of the source inside the chosen big site. -/
theorem spec_mem_of_injective
    (B : AlgebraicGeometry.BigFppfSite.{u}) {R T : Type u} [CommRing R] [CommRing T]
    (hT : B.Contains (Spec (.of T))) (i : R → T) (hi : Function.Injective i) :
    B.Contains (Spec (.of R)) := by
  show (Spec (.of R)).size < B.cutoff
  change (Spec (.of T)).size < B.cutoff at hT
  rw [Scheme.size_Spec] at hT ⊢
  exact lt_of_le_of_lt (max_le_max_left _ (Cardinal.mk_le_of_injective hi)) hT

/-- A surjection of rings keeps the spectrum of the target inside the chosen big site. -/
theorem spec_mem_of_surjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) {R T : Type u} [CommRing R] [CommRing T]
    (hR : B.Contains (Spec (.of R))) (i : R → T) (hi : Function.Surjective i) :
    B.Contains (Spec (.of T)) := by
  classical
  exact spec_mem_of_injective B hR (Function.surjInv hi) (Function.injective_surjInv hi)

/-- The spectrum of a fraction field stays inside the chosen big site. -/
theorem spec_fractionRing_mem
    (B : AlgebraicGeometry.BigFppfSite.{u}) {R K : Type u}
    [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
    (hR : B.Contains (Spec (.of R))) : B.Contains (Spec (.of K)) := by
  show (Spec (.of K)).size < B.cutoff
  change (Spec (.of R)).size < B.cutoff at hR
  simpa only [Scheme.size_Spec, IsFractionRing.cardinalMk R K] using hR

/-- The left column of a valuative square, as a morphism of objects of the site. -/
noncomputable abbrev specializationArrow
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} (q : ValuativeSquare f) :=
  (Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)))) :
    siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) ⟶
    siteObject B S hS q.ring_mem q.base)

/-- The dominating extension attached to a local homomorphism from the valuation ring of a
valuative square to another valuation ring, compatibly with a homomorphism of the fraction
fields. -/
noncomputable def dominatingExtensionOfRingHom
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} (q : ValuativeSquare f)
    {A L : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    [Field L] [Algebra A L] [IsFractionRing A L]
    (hA : B.Contains (Spec (.of A))) (hL : B.Contains (Spec (.of L)))
    (i : q.R →+* A) (j : q.K →+* L) (hi : IsLocalHom i)
    (hij : (algebraMap A L).comp i = j.comp (algebraMap q.R q.K)) :
    q.DominatingExtension := by
  let base := Spec.map (CommRingCat.ofHom i) ≫ q.base
  let a : siteObject B S hS hA base ⟶
      siteObject B S hS q.ring_mem q.base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom i)))
  have hb : Spec.map (CommRingCat.ofHom j) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ base := by
    dsimp [base]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun k => Spec.map (CommRingCat.ofHom k) ≫ q.base) hij.symm
  let b : siteObject B S hS hL
      (Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ base) ⟶
      siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base) :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom j)))
      (B.inclusion.map_injective hb)
  let c : siteObject B S hS hL
      (Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ base) ⟶
      siteObject B S hS hA base :=
    Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap A L))))
  have hc : b ≫ specializationArrow q = c ≫ a := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change Spec.map (CommRingCat.ofHom j) ≫
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) =
      Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ Spec.map (CommRingCat.ofHom i)
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun k => Spec.map (CommRingCat.ofHom k)) hij.symm
  exact {
    square := {
      R := A, K := L, ring_mem := hA, field_mem := hL, base := base
      generic := yoneda.map b ≫ q.generic
      special := yoneda.map a ≫ q.special
      comm := by
        calc
          (yoneda.map b ≫ q.generic) ≫ f =
              yoneda.map b ≫ (yoneda.map (specializationArrow q) ≫ q.special) := by
                rw [Category.assoc, q.comm]
          _ = yoneda.map c ≫ (yoneda.map a ≫ q.special) := by
            simpa only [Functor.map_comp, Category.assoc] using
              congrArg (fun k => yoneda.map k ≫ q.special) hc
    }
    ringMap := i, fieldMap := j, isLocalHom := hi, fraction_comm := hij
    base_comm := rfl
    genericOver := b, genericOver_left := rfl
    specialOver := a, specialOver_left := rfl
    generic_comm := rfl, special_comm := rfl }

/-- **The bottom edge of a valuative square lifts through any flat surjective chart after a
dominating extension of the valuation ring.**

Let `q` be a valuative square for a morphism `f : X ⟶ Y` of presheaves on the big fppf site of
`S`, with `Y` an algebraic space, and let `c : yoneda.obj W ⟶ Y` be flat and surjective — for
instance a surjective étale chart. Then there are a dominating extension `e` of `q` and a
morphism `l` from the presheaf represented by the spectrum of the enlarged valuation ring to the
presheaf represented by `W` with `l ≫ c = e.square.special`. -/
theorem exists_dominatingExtension_lift_of_isFlat_of_isSurjective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    (q : ValuativeSquare f) (W : AlgebraicGeometry.BigFppfOver B S hS)
    (c : yoneda.obj W ⟶ Y) (hc : IsFlat B S hS c) (hcs : IsSurjective B S hS c) :
    ∃ (e : q.DominatingExtension)
      (l : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ yoneda.obj W),
      l ≫ c = e.square.special := by
  let G := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let T := siteObject B S hS q.ring_mem q.base
  let k := IsLocalRing.ResidueField q.R
  have hk : B.Contains (Spec (.of k)) :=
    spec_mem_of_surjective B q.ring_mem (IsLocalRing.residue q.R)
      IsLocalRing.residue_surjective
  let p : FieldValuedPoint B S hS (yoneda.obj T) := {
    carrier := k, contained := hk
    toBase := Spec.map (CommRingCat.ofHom (IsLocalRing.residue q.R)) ≫ q.base
    value := Over.homMk (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue q.R)))) }
  obtain ⟨A, hAring, hAdomain, hAval, i, hi, V, eV, j, l, hj, hl⟩ :=
    AlgebraicGeometry.Space.exists_valuationRing_extension_lift_of_isFlat q.R
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS W) hY
      c hc T (Iso.refl _) q.special p
      (by exact IsLocalRing.comap_closedPoint (IsLocalRing.residue q.R))
      (hcs _)
  have hA : B.Contains (Spec (.of A)) := by
    show (Spec (.of A)).size < B.cutoff
    rw [← Scheme.size_congr eV]
    exact V.left.2
  let L := FractionRing A
  have hL : B.Contains (Spec (.of L)) := spec_fractionRing_mem B hA
  let kmap : q.K →+* L := IsFractionRing.lift (A := q.R) (K := q.K)
    (g := (algebraMap A L).comp i) ((IsFractionRing.injective A L).comp hi.1)
  have hkmap : (algebraMap A L).comp i = kmap.comp (algebraMap q.R q.K) := by
    ext x
    exact (IsFractionRing.lift_algebraMap (K := q.K)
      (g := (algebraMap A L).comp i) ((IsFractionRing.injective A L).comp hi.1) x).symm
  let e := dominatingExtensionOfRingHom q hA hL i kmap hi.2 hkmap
  have hinv : eV.inv ≫ G.map j = Spec.map (CommRingCat.ofHom i) := by
    rw [(Category.comp_id _).symm.trans hj]
    simp
  have hb : eV.inv ≫ B.inclusion.map V.hom = e.square.base := by
    show eV.inv ≫ B.inclusion.map V.hom = Spec.map (CommRingCat.ofHom i) ≫ q.base
    rw [← hinv, Category.assoc]
    exact congrArg (eV.inv ≫ ·) (congrArg B.inclusion.map j.w).symm
  let v : siteObject B S hS e.square.ring_mem e.square.base ⟶ V :=
    Over.homMk (ObjectProperty.homMk eV.inv)
      (B.inclusion.map_injective hb)
  have hv : v ≫ j = e.specialOver := by
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    exact hinv
  refine ⟨e, yoneda.map v ≫ l, ?_⟩
  rw [Category.assoc, hl, ← Category.assoc, ← yoneda.map_comp, hv]
  exact e.special_comm.symm

end AlgebraicGeometry.Space

end
