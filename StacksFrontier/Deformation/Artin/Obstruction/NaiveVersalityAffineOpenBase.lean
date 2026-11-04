module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityStalkBase

/-!
# Changing the deformation base from an affine open to the local ring of `S`

`Deformation.Artin.IsVersalAt` is, by `Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint`,
the lifting property `Deformation.Artin.LiftsAtResiduePoint` quantified over the surjections of
`𝒞_{𝒪_{S,s}}`: the deformation base is the local ring of `S` at the image of the point.
`Deformation.Artin.liftsAtResiduePoint_changeBase` turns that property into the same property
over the ring `Λ` of an affine open, which is the form the direction `(1) ⇒ (2)` of
[Stacks, Tag 07YM] consumes.

This file is the **opposite** transfer, which the direction `(2) ⇒ (1)` needs: the lifting
property over `Λ` implies the lifting property over `𝒪_{S,s}`, hence versality at the point.
Where the transfer of `Deformation.Artin.liftsAtResiduePoint_changeBase` asks nothing of
`Spec Λ ⟶ S` — an Artinian local `Λ`-algebra is canonically an `𝒪_{S,s}`-algebra because its
spectrum is a point — this one does: an Artinian local `𝒪_{S,s}`-algebra is a `Λ`-algebra only
by restriction of scalars along a ring map `Λ ⟶ 𝒪_{S,s}`, and such a map exists exactly because
`Spec Λ ⟶ S` is an open immersion. The germ at a point of the affine open is that map, and the
uniqueness of the factorization makes it the only one.

## Main results

* `Deformation.Artin.exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion` — **the ring map**
  `Λ ⟶ 𝒪_{S,s}`: for an open immersion `iΛ : Spec Λ ⟶ S` and a point `t` of `Spec Λ`, the germ
  of `Λ` at `t`, read through the stalk isomorphism of the open immersion, is a ring map to the
  local ring of `S` at `iΛ t` whose spectrum composed with `iΛ` is
  `AlgebraicGeometry.Scheme.fromSpecStalk`.
* `Deformation.Artin.ringHom_comp_fromSpecStalk_unique` — it is the only such map, `iΛ` being a
  monomorphism and `Spec` faithful on affines.
* `Deformation.Artin.restrictBaseObj` and `Deformation.Artin.restrictBaseHom` — an object,
  respectively a morphism, of `𝒞_{𝒪_{S,s}}` read in `𝒞_Λ` by restriction of scalars, with
  `Deformation.Artin.specMap_restrictBaseObj` the identification of the two presentations of
  the base over `S`.
* `Deformation.Artin.algebraMap_eq_comp_of_specMap_eq` — the compatibility that restriction of
  scalars asks of the fixed residue field is automatic: two ring maps `Λ ⟶ κ` whose spectra
  induce the same morphism `Spec κ ⟶ S` agree.
* `Deformation.Artin.liftsAtResiduePoint_changeBase_affineOpen` — **the transfer**: the lifting
  property over an affine open implies the lifting property over the local ring.
* `Deformation.Artin.liftsAtResiduePoint_iff_affineOpenBase` — the two transfers composed into
  an equivalence, and `Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_affineOpen` the
  same read at `Deformation.Artin.IsVersalAt`: versality at `u₀` is the lifting property with
  the ring of an affine open through which the structure morphism factors as deformation base.

## Implementation notes

The `Λ`-algebra structure of a restricted object is `RingHom.toAlgebra` of the composite
`Λ ⟶ 𝒪_{S,s} ⟶ C`. That is the mirror of `Deformation.Artin.stalkAlgebra`, and it is sound for
the same reason: the structure is attached to a *new* object of `𝒞_Λ`, so it replaces nothing,
and the carrier, the ring, the Artinian and local structures and the underlying equivalence of
residue fields are reused unchanged. Everything being literally reused is what makes
`Deformation.Artin.residueMap_restrictBaseObj` hold by `rfl` and what makes
`Deformation.Artin.schemeMap` at the two presentations of one base the same morphism: the two
identifications are proofs of equalities between the same pair of objects, so proof irrelevance
identifies the `eqToHom`s they contribute.

Nothing is asked of the point `t` of `Spec Λ` beyond that `iΛ` carry it to `s`. In the
application `s` is the image of the finite type point `u₀` under `U.hom`, and `t` is the point
of the affine open underlying it; the hypothesis is then the statement that the structure
morphism of `U` factors through the affine open at `u₀`.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 06GC](https://stacks.math.columbia.edu/tag/06GC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

/-! ### The germ of an affine open at a point of its image -/

section Germ

variable {Λ : Type u} [CommRing Λ] {S : Scheme.{u}} (iΛ : Spec (CommRingCat.of Λ) ⟶ S)

/-- **The ring map `Λ ⟶ 𝒪_{S,s}` of an affine open.** For an open immersion
`iΛ : Spec Λ ⟶ S` and a point `t` of `Spec Λ`, the germ map of `Λ` at `t` followed by the
inverse of the stalk isomorphism of `iΛ` is a ring map `Λ ⟶ 𝒪_{S, iΛ t}` whose spectrum,
composed with `iΛ`, is the canonical morphism out of the spectrum of the local ring.

This is the ingredient restriction of scalars needs and the one
`Deformation.Artin.liftsAtResiduePoint_changeBase` does *not*: that transfer produces an
`𝒪_{S,s}`-algebra structure on an Artinian local `Λ`-algebra at the level of schemes, where no
ring map `Λ ⟶ 𝒪_{S,s}` is involved, while the opposite transfer restricts scalars and therefore
needs one. Being an open immersion is exactly what supplies it: the stalk map of `iΛ` at `t` is
an isomorphism. -/
public theorem exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion
    [IsOpenImmersion iΛ] (t : Spec (CommRingCat.of Λ)) (s : S) (hts : iΛ t = s) :
    ∃ g : Λ →+* S.presheaf.stalk s,
      Spec.map (CommRingCat.ofHom g) ≫ iΛ = S.fromSpecStalk s := by
  subst hts
  have H : Set.range (S.fromSpecStalk (iΛ t)) ⊆ Set.range iΛ := by
    rw [Scheme.range_fromSpecStalk]
    exact fun y hy => hy.mem_open (IsOpenImmersion.isOpen_range iΛ) ⟨t, rfl⟩
  refine ⟨ringHom_of_schemeMap (A := Λ) (C := (S.presheaf.stalk (iΛ t) : Type u))
    (IsOpenImmersion.lift iΛ (S.fromSpecStalk (iΛ t)) H), ?_⟩
  rw [specMap_ringHom_of_schemeMap]
  exact IsOpenImmersion.lift_fac iΛ (S.fromSpecStalk (iΛ t)) H

/-- The ring map of `Deformation.Artin.exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion` is
the only one with its property: `iΛ` is a monomorphism, so the composite determines the
spectrum, and `Spec` is faithful on affine schemes. -/
public theorem ringHom_comp_fromSpecStalk_unique [Mono iΛ] (s : S)
    (g g' : Λ →+* S.presheaf.stalk s)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ iΛ = S.fromSpecStalk s)
    (hg' : Spec.map (CommRingCat.ofHom g') ≫ iΛ = S.fromSpecStalk s) : g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono iΛ).mp (hg.trans hg'.symm)))

end Germ

/-! ### Restriction of scalars along the germ map -/

section RestrictBase

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} {s : S} [algStalk : Algebra (S.presheaf.stalk s) k]
  (g : Λ →+* S.presheaf.stalk s)
  (hk : (algebraMap (S.presheaf.stalk s) k).comp g = algebraMap Λ k)

/-- **The `Λ`-algebra structure of an object of `𝒞_{𝒪_{S,s}}` by restriction of scalars**
along the germ map `g`. This is the mirror of `Deformation.Artin.stalkAlgebra`, and it replaces
nothing: it is attached to a new object of `𝒞_Λ`. -/
@[instance_reducible]
public def restrictBaseAlgebra (C : ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) k) :
    Algebra Λ (C : Type u) :=
  ((algebraMap (S.presheaf.stalk s) (C : Type u)).comp g).toAlgebra

omit [Algebra Λ k] in
/-- The structure map of `Deformation.Artin.restrictBaseAlgebra` is the structure map of its
input precomposed with `g`. -/
public theorem algebraMap_restrictBaseAlgebra
    (C : ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) k) :
    letI := restrictBaseAlgebra g C
    algebraMap Λ (C : Type u) = (algebraMap (S.presheaf.stalk s) (C : Type u)).comp g := rfl

omit [Algebra Λ k] in
/-- **The two presentations of the base agree.** If the spectrum of `g` composed with
`Spec Λ ⟶ S` is the canonical morphism out of `Spec 𝒪_{S,s}`, then the structure morphism of
`Spec C` read over `Λ` is the one read over the local ring. -/
public theorem specMap_restrictBaseAlgebra {iΛ : Spec (CommRingCat.of Λ) ⟶ S}
    (hg : Spec.map (CommRingCat.ofHom g) ≫ iΛ = S.fromSpecStalk s)
    (C : ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) k) :
    letI := restrictBaseAlgebra g C
    Spec.map (CommRingCat.ofHom (algebraMap Λ (C : Type u))) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (C : Type u))) ≫
        S.fromSpecStalk s := by
  let := restrictBaseAlgebra g C
  have h : CommRingCat.ofHom (algebraMap Λ (C : Type u)) =
      CommRingCat.ofHom g ≫
        CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (C : Type u)) := rfl
  rw [h, Spec.map_comp, Category.assoc, hg]

/-- **An object of `𝒞_{𝒪_{S,s}}` as an object of `𝒞_Λ`.** The carrier, the ring, the Artinian
and local structures and the underlying equivalence of residue fields are reused unchanged;
the algebra structure is restriction of scalars along `g`, whose compatibility with the residue
identification is the hypothesis `hk` on the fixed residue field. -/
public def restrictBaseObj (C : ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) k) :
    ArtinianLocalAlgCat.{u, u, u} Λ k where
  carrier := C
  algebra := restrictBaseAlgebra g C
  residueEquiv :=
    letI := restrictBaseAlgebra g C
    { C.residueEquiv with
      commutes' := fun l => by
        rw [show algebraMap Λ k l = (algebraMap (S.presheaf.stalk s) k) (g l) from
          (RingHom.congr_fun hk l).symm]
        exact C.residueEquiv.commutes (g l) }

/-- The carrier of `Deformation.Artin.restrictBaseObj` is that of its input. -/
public theorem restrictBaseObj_carrier
    (C : ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) k) :
    (restrictBaseObj g hk C : Type u) = (C : Type u) := rfl

/-- The map to the fixed residue field is unchanged by
`Deformation.Artin.restrictBaseObj`. -/
public theorem residueMap_restrictBaseObj
    (C : ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) k) :
    residueMap (restrictBaseObj g hk C) = residueMap C := rfl

variable (A B : ArtinianLocalAlgCat.{u, u, u} (S.presheaf.stalk s) k) (f : B ⟶ A)

/-- **A morphism of `𝒞_{𝒪_{S,s}}` as a morphism of `𝒞_Λ`**, with the same underlying ring
map: an `𝒪_{S,s}`-algebra homomorphism is `Λ`-linear for the restricted structures. -/
public def restrictBaseHom : restrictBaseObj g hk B ⟶ restrictBaseObj g hk A where
  hom :=
    { toRingHom := f.hom.toRingHom
      commutes' := fun l => f.hom.commutes (g l) }
  isLocal := f.isLocal
  residue_comm := f.residue_comm

/-- The ring map underlying `Deformation.Artin.restrictBaseHom` is the one underlying its
input. -/
public theorem restrictBaseHom_hom_toRingHom :
    (restrictBaseHom g hk A B f).hom.toRingHom = f.hom.toRingHom := rfl

end RestrictBase

/-! ### The compatibility on the residue field is automatic -/

section Compatibility

/-- **Two ring maps into the fixed residue field with the same spectrum agree.** If
`Spec Λ ⟶ S` is a monomorphism and the structure map of `κ` over `Λ`, read through it, induces
the same morphism `Spec κ ⟶ S` as the structure map of `κ` over `𝒪_{S,s}` read through the
canonical morphism, then the first is the second precomposed with `g`.

This is the hypothesis `Deformation.Artin.restrictBaseObj` asks of the fixed residue field, and
it is not an extra assumption: it is the compatibility of the chosen residue point with the
local ring of `S`, which the lifting property already carries. -/
public theorem algebraMap_eq_comp_of_specMap_eq {Λ k : Type u} [CommRing Λ] [Field k]
    [Algebra Λ k] {S : Scheme.{u}} {s : S} [Algebra (S.presheaf.stalk s) k]
    (iΛ : Spec (CommRingCat.of Λ) ⟶ S) [Mono iΛ] (g : Λ →+* S.presheaf.stalk s)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ iΛ = S.fromSpecStalk s)
    (hcompat : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s) :
    (algebraMap (S.presheaf.stalk s) k).comp g = algebraMap Λ k := by
  have h : Spec.map (CommRingCat.ofHom ((algebraMap (S.presheaf.stalk s) k).comp g)) ≫ iΛ =
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ := by
    rw [hcompat,
      show CommRingCat.ofHom ((algebraMap (S.presheaf.stalk s) k).comp g) =
        CommRingCat.ofHom g ≫ CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k) from rfl,
      Spec.map_comp, Category.assoc, hg]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono iΛ).mp h))

end Compatibility

/-! ### The transfer of the lifting property -/

section ChangeBase

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} (iΛ : Spec (CommRingCat.of Λ) ⟶ S) (s : S)
  [algStalk : Algebra (S.presheaf.stalk s) k]
  {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
  (U : Over S) (x : X) (hx : q.obj x = U) (κ : Spec (CommRingCat.of k) ⟶ U.left)

/-- **The change of deformation base, from an affine open to the local ring.** If the lifting
property defining versality holds with the ring `Λ` of an affine open as deformation base, it
holds with the local ring of `S` at the chosen point.

Every Artinian local `𝒪_{S,s}`-algebra of a lifting problem is a `Λ`-algebra by restriction of
scalars along the germ map `g` (`Deformation.Artin.restrictBaseObj`), the surjection between
two of them is a morphism of `𝒞_Λ` with the same underlying ring map
(`Deformation.Artin.restrictBaseHom`), and the two presentations of each base over `S` agree
(`Deformation.Artin.specMap_restrictBaseObj`).

Unlike `Deformation.Artin.liftsAtResiduePoint_changeBase`, which runs the other way, this
transfer needs `Spec Λ ⟶ S` to admit the germ map — which is what
`Deformation.Artin.exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion` supplies for an open
immersion. -/
public theorem liftsAtResiduePoint_changeBase_affineOpen
    (g : Λ →+* S.presheaf.stalk s)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ iΛ = S.fromSpecStalk s)
    (hk : (algebraMap (S.presheaf.stalk s) k).comp g = algebraMap Λ k)
    (hbase : LiftsAtResiduePoint (Λ := Λ) (k := k) iΛ q U x hx κ) :
    LiftsAtResiduePoint (Λ := S.presheaf.stalk s) (k := k) (alg := algStalk)
      (S.fromSpecStalk s) q U x hx κ := by
  intro A B f hf y z hy hz i hi a ha
  have hy' : q.obj y = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap Λ (restrictBaseObj g hk A : Type u))) ≫ iΛ) := by
    rw [hy]
    exact congrArg Over.mk (specMap_restrictBaseAlgebra g hg A).symm
  have hz' : q.obj z = Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap Λ (restrictBaseObj g hk B : Type u))) ≫ iΛ) := by
    rw [hz]
    exact congrArg Over.mk (specMap_restrictBaseAlgebra g hg B).symm
  exact hbase (restrictBaseObj g hk A) (restrictBaseObj g hk B)
    (restrictBaseHom g hk A B f) hf y z hy' hz' i hi a ha

/-- **The lifting property over an affine open and over the local ring agree.**
`Deformation.Artin.liftsAtResiduePoint_changeBase` is one implication and
`Deformation.Artin.liftsAtResiduePoint_changeBase_affineOpen` the other.

The two hypotheses are the ones each direction needs and nothing more: locality of the
structure map of `κ` over the local ring for the forward implication, and the germ map for the
converse. The compatibility of the residue point with the local ring, `hκ`, is shared. -/
public theorem liftsAtResiduePoint_iff_affineOpenBase
    (hloc : IsLocalHom (algebraMap (S.presheaf.stalk s) k))
    (hκ : κ ≫ U.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) k)) ≫ S.fromSpecStalk s)
    (g : Λ →+* S.presheaf.stalk s)
    (hg : Spec.map (CommRingCat.ofHom g) ≫ iΛ = S.fromSpecStalk s)
    (hk : (algebraMap (S.presheaf.stalk s) k).comp g = algebraMap Λ k) :
    LiftsAtResiduePoint (Λ := S.presheaf.stalk s) (k := k) (alg := algStalk)
        (S.fromSpecStalk s) q U x hx κ ↔
      LiftsAtResiduePoint (Λ := Λ) (k := k) iΛ q U x hx κ :=
  ⟨liftsAtResiduePoint_changeBase iΛ s hloc q U x hx κ hκ,
    liftsAtResiduePoint_changeBase_affineOpen iΛ s q U x hx κ g hg hk⟩

end ChangeBase

/-! ### Versality at a point, read over an affine open -/

section VersalAffineOpen

variable {Λ : Type u} [CommRing Λ] {S : Scheme.{u}} (iΛ : Spec (CommRingCat.of Λ) ⟶ S)
  (U : Over S) {X : Type v} [Category.{w} X] (q : X ⥤ Over S)
  (u₀ : U.left) (x : X) (hx : q.obj x = U)
  [Algebra Λ (U.left.residueField u₀)]

include hx in
/-- **Versality at a point is the lifting property over an affine open.** Let
`iΛ : Spec Λ ⟶ S` be an open immersion carrying a point `t` to the image of `u₀`, and suppose
the structure map of the residue field at `u₀` over `Λ`, read through `iΛ`, is the canonical
residue-field point of `U` followed by the structure morphism. Then `x` is versal at `u₀`
exactly when the lifting property holds with `Λ` as deformation base.

`Deformation.Artin.IsVersalAt` is literally the lifting property with the local ring of `S` at
the image of `u₀` as base (`Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint`), and
`Deformation.Artin.liftsAtResiduePoint_iff_affineOpenBase` moves the base in both directions:
the germ map comes from `Deformation.Artin.exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion`
and the compatibility it needs on the residue field from
`Deformation.Artin.algebraMap_eq_comp_of_specMap_eq`.

This is what lets the whole of [Stacks, Tag 07YM] be argued over the ring `Λ` of the affine
open the family maps into: conditions (i) and (ii) and the morphism `ξ` are stated there, and
the objects of `𝒞_{𝒪_{S,s}}` never have to be met. -/
public theorem isVersalAt_iff_liftsAtResiduePoint_affineOpen [IsOpenImmersion iΛ]
    (t : Spec (CommRingCat.of Λ)) (ht : iΛ t = basePoint U u₀)
    (hcompat : Spec.map (CommRingCat.ofHom
        (algebraMap Λ (U.left.residueField u₀))) ≫ iΛ =
      U.left.fromSpecResidueField u₀ ≫ U.hom) :
    IsVersalAt U q u₀ x hx ↔
      LiftsAtResiduePoint (Λ := Λ) (k := U.left.residueField u₀) iΛ q U x hx
        (U.left.fromSpecResidueField u₀) := by
  let algStalk := residueFieldAlgebra U u₀
  have hloc : IsLocalHom
      (algebraMap (S.presheaf.stalk (basePoint U u₀)) (U.left.residueField u₀)) :=
    show IsLocalHom (Scheme.stalkClosedPointTo (residueFieldBasePoint U u₀)).hom from
      inferInstance
  have hκ : U.left.fromSpecResidueField u₀ ≫ U.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk (basePoint U u₀))
        (U.left.residueField u₀))) ≫ S.fromSpecStalk (basePoint U u₀) :=
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (residueFieldBasePoint U u₀)).symm
  obtain ⟨g₀, hg₀⟩ :=
    exists_ringHom_comp_fromSpecStalk_of_isOpenImmersion iΛ t (basePoint U u₀) ht
  have hk := algebraMap_eq_comp_of_specMap_eq (k := U.left.residueField u₀) iΛ g₀ hg₀
    (hcompat.trans hκ)
  exact (isVersalAt_iff_liftsAtResiduePoint U q u₀ x hx).trans
    (liftsAtResiduePoint_iff_affineOpenBase (k := (U.left.residueField u₀ : Type u))
      iΛ (basePoint U u₀) q U x hx
      (U.left.fromSpecResidueField u₀) hloc hκ g₀ hg₀ hk)

end VersalAffineOpen

end Deformation.Artin
