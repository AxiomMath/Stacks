module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityPrimeBase
public import StacksFrontier.Deformation.BaseCategory.AugmentedPowQuotient

/-!
# The section the lifting property produces

This is the geometric step of the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] in degree `-1`.
Given the square-zero extension `A' → A` of [Stacks, Tag 07YL] and a lift `x'` of the family `x`
to `Spec A'`, the argument restricts both to the Artinian quotients — `x|_{A ⧸ 𝔭 ^ n}` and
`x'|_{A' ⧸ (𝔭') ^ n}` — joins them by the arrow over `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` that the
commuting square of rings supplies, and tests versality against that arrow. What comes back is an
arrow `x'|_{A' ⧸ (𝔭') ^ n} ⟶ x` whose underlying ring map `σ : A → A' ⧸ (𝔭') ^ n` *lifts the
quotient map* `A → A ⧸ 𝔭 ^ n` — which is exactly the hypothesis of
`Deformation.ArtinianLocalAlgCat.not_isEssentialSurjection_of_lift_powQuotient`.

Both crossings between the fibred category and rings are already available:
`Deformation.Artin.restrictAlong` and `Deformation.Artin.schemeMap_restrictAlongArrow_mk` go one
way, `Deformation.Artin.ringHom_of_schemeMap` and `Deformation.Artin.algHom_of_schemeMap_over`
the other. What this file adds is the conversion of the *equation* `i ≫ b = a` that versality
returns into the pointwise ring identity `f ∘ σ = mk`, and the assembly.

## Main results

* `Deformation.Artin.specMap_quotientMk_comp` — the quotient map of a `Λ`-algebra is compatible
  with the structure morphisms to `S`, which is the only hypothesis
  `Deformation.Artin.restrictAlong` takes.
* `Deformation.Artin.comp_ringHom_of_schemeMap_of_comp_eq` — **the conversion**: if `i ≫ b = a`
  and the underlying morphisms of schemes of `i` and `a` are the spectra of `f` and `g`, then
  `f ∘ σ = g` for the ring map `σ` underlying `b`. Both ends being affine, this is the
  faithfulness of `Scheme.Spec` applied to `Deformation.Artin.schemeMap_comp`.
* `Deformation.Artin.exists_algHom_powQuotient_of_liftsAtResiduePoint` — **the section**: the
  lifting property at the residue point, applied to the arrow of the square, produces a
  `Λ`-algebra map `σ : A →ₐ[Λ] A' ⧸ (𝔭') ^ n` lifting the quotient map `A → A ⧸ 𝔭 ^ n`.

## Implementation notes

The two restrictions are introduced through an existential statement rather than by name: what
the rest of the argument uses of `x|_{A ⧸ 𝔭 ^ n}` is only that it lies over `Spec (A ⧸ 𝔭 ^ n)`
and carries an arrow to `x` over the quotient map, and quantifying over that keeps the
`Deformation.Artin.restrictAlong` term — which mentions the chosen pullbacks of `p` — out of
every subsequent goal. Cartesianness of the second restriction's structure arrow is not needed
either: `p` is fibred in groupoids, so `Deformation.Artin.exists_unique_schemeMap_eq_of_square`
factors through *any* arrow to the lift.

The commuting triangle `i ≫ r = a ≫ ℓ` is used only to produce `i`, and is discarded: the
lifting property asks of `i` nothing beyond that it lie over the spectrum of the small extension,
and the arrow it returns satisfies `i ≫ b = a`, from which the ring identity follows.

The `Λ`-linearity of `σ` is where the monomorphism hypothesis on `Spec Λ ⟶ S` is used, and it is
the only place: what the arrow `b` carries is a morphism of schemes over `S`, and
`Deformation.Artin.algHom_of_schemeMap_over` turns "over `S`" into "over `Spec Λ`" by cancelling
it. That cancellation cannot be avoided — the difference of the two maps `Λ → A' ⧸ (𝔭') ^ n`
obtained from `σ` and from the algebra structure lands in the kernel of a small extension, on
which it is an arbitrary derivation, so the identity `f ∘ σ = mk` does not by itself force
`σ` to be `Λ`-linear.

## References

* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

open Deformation.ArtinianLocalAlgCat

universe u v w

/-! ### The quotient map as a morphism over the base -/

/-- An algebra map is compatible with the structure morphisms to `S` through `Spec Λ ⟶ S`. -/
private theorem specMap_algHom_comp_algebraMap_comp {Λ R R' : Type u} [CommRing Λ] [CommRing R]
    [CommRing R'] [Algebra Λ R] [Algebra Λ R'] (f : R →ₐ[Λ] R') {S : Scheme.{u}}
    (baseMap : Spec (CommRingCat.of Λ) ⟶ S) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ baseMap =
      Spec.map (CommRingCat.ofHom (algebraMap Λ R')) ≫ baseMap := by
  rw [← Category.assoc, ← Spec.map_comp]
  exact congrArg (· ≫ baseMap) (congrArg Spec.map (by ext l; exact f.commutes l))

/-- The quotient map of a `Λ`-algebra whose spectrum maps to `S` through the affine open
`Spec Λ ⟶ S` is compatible with the structure morphisms: `Spec (R ⧸ I) ⟶ Spec R ⟶ S` is the
structure morphism of `Spec (R ⧸ I)`.

This is the only hypothesis `Deformation.Artin.restrictAlong` takes, and it is what presents the
restriction of a family to an Artinian quotient as an object over `S` in the shape
`Deformation.Artin.LiftsAtResiduePoint` consumes. -/
public theorem specMap_quotientMk_comp {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R]
    (I : Ideal R) {S : Scheme.{u}} (baseMap : Spec (CommRingCat.of Λ) ⟶ S)
    (toR : Spec (CommRingCat.of R) ⟶ S)
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ R)) ≫ baseMap = toR) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ toR =
      Spec.map (CommRingCat.ofHom (algebraMap Λ (R ⧸ I))) ≫ baseMap := by
  rw [← hbase]
  exact specMap_algHom_comp_algebraMap_comp (Ideal.Quotient.mkₐ Λ I) baseMap

/-! ### From an equation of arrows to an identity of ring maps -/

/-- **An equation of arrows of the fibred category, read as an identity of ring maps.** Let
`i : y ⟶ z`, `b : z ⟶ x` and `a : y ⟶ x` be arrows with `i ≫ b = a`, between objects presented
over `S` by spectra of rings, and suppose the morphisms of schemes underlying `i` and `a` are the
spectra of ring maps `f` and `g`. Then `f` composed with the ring map underlying `b` is `g`.

Both ends being affine, `Deformation.Artin.schemeMap_comp` turns the equation into an equation of
morphisms of affine schemes, and the faithfulness of `Scheme.Spec` turns that into the identity
of ring maps. This is what converts the conclusion `i ≫ b = a` of
`Deformation.Artin.LiftsAtResiduePoint` into the hypothesis
`∀ a, f (σ a) = Ideal.Quotient.mk (𝔭 ^ n) a` of
`Deformation.ArtinianLocalAlgCat.not_isEssentialSurjection_of_lift_powQuotient`. -/
@[stacks 07YM "i ≫ b = a read as an identity of ring maps"]
public theorem comp_ringHom_of_schemeMap_of_comp_eq
    {A C C' : Type u} [CommRing A] [CommRing C] [CommRing C']
    {S : Scheme.{u}} {toS : Spec (CommRingCat.of A) ⟶ S}
    {toSC : Spec (CommRingCat.of C) ⟶ S} {toSC' : Spec (CommRingCat.of C') ⟶ S}
    {Y : Type v} [Category.{w} Y] (q : Y ⥤ Over S) {y z x : Y}
    (hy : q.obj y = Over.mk toSC) (hz : q.obj z = Over.mk toSC')
    (hx : q.obj x = Over.mk toS)
    {i : y ⟶ z} {b : z ⟶ x} {a : y ⟶ x} (hab : i ≫ b = a)
    {f : C' →+* C} (hi : schemeMap q hy hz i = Spec.map (CommRingCat.ofHom f))
    {g : A →+* C} (ha : schemeMap q hy hx a = Spec.map (CommRingCat.ofHom g)) :
    f.comp (ringHom_of_schemeMap (schemeMap q hz hx b)) = g := by
  have key : Spec.map (CommRingCat.ofHom
        (f.comp (ringHom_of_schemeMap (schemeMap q hz hx b)))) =
      Spec.map (CommRingCat.ofHom g) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, specMap_ringHom_of_schemeMap, ← hi,
      ← schemeMap_comp q hy hz hx i b, hab, ha]
  simpa using congrArg CommRingCat.Hom.hom (Spec.map_injective key)

/-! ### The section produced by the lifting property -/

section SquareLift

variable {Λ A A' κ : Type u} [CommRing Λ] [CommRing A] [CommRing A'] [Field κ]
  [Algebra Λ A] [Algebra Λ A'] [Algebra Λ κ] [IsNoetherianRing A] [IsNoetherianRing A']
  {X : Type v} [Category.{w} X]

/-- **The section of [Stacks, Tag 07YM].** Let `A' → A` be a map of augmented Noetherian
`Λ`-algebras over a field `κ`, with `φ` surjective, let `x` be a family over `Spec A` and `x'` a
lift of it to `Spec A'`, presented over `S` through the affine open `Spec Λ ⟶ S`. If the lifting
property defining versality holds at the residue point of `A` determined by its augmentation,
then the quotient map `A → A ⧸ 𝔭 ^ n` lifts through the small extension
`A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` to a `Λ`-algebra map `σ : A →ₐ[Λ] A' ⧸ (𝔭') ^ n`.

The two restrictions are the chosen pullbacks `Deformation.Artin.restrictAlong`, the arrow
between them is `Deformation.Artin.exists_unique_schemeMap_eq_of_square` applied to the commuting
square of rings `A' → A → A ⧸ 𝔭 ^ n` and `A' → A' ⧸ (𝔭') ^ n → A ⧸ 𝔭 ^ n`, the residue condition
that versality asks of the arrow to `x` is the compatibility of the induced augmentation with the
quotient map, and the ring map is read off the resulting arrow by
`Deformation.Artin.algHom_of_schemeMap_over`, whose output is the identity
`Deformation.Artin.comp_ringHom_of_schemeMap_of_comp_eq` converts. -/
@[stacks 07YM "versality lifts A through A'/(𝔭') ^ n"]
public theorem exists_algHom_powQuotient_of_liftsAtResiduePoint
    (ε : A →ₐ[Λ] κ) (hε : Function.Surjective ε)
    (ε' : A' →ₐ[Λ] κ) (hε' : Function.Surjective ε')
    (φ : A' →ₐ[Λ] A) (hφ : ε.comp φ = ε') (hsurjφ : Function.Surjective φ)
    (n : ℕ) [NeZero n]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (toS : Spec (CommRingCat.of A) ⟶ S) (hA : B.Contains (Spec (CommRingCat.of A)))
    (hA' : B.Contains (Spec (CommRingCat.of A')))
    (baseMap : Spec (CommRingCat.of Λ) ⟶ S) [Mono baseMap]
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
    (hC : B.Contains (Spec (CommRingCat.of (A ⧸ RingHom.ker ε.toRingHom ^ n))))
    (hC' : B.Contains (Spec (CommRingCat.of (A' ⧸ RingHom.ker ε'.toRingHom ^ n))))
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x x' : X)
    (hx : p.obj x = algebraOver A B S hS toS hA)
    (hxS : (p ⋙ Over.post B.inclusion).obj x = Over.mk toS)
    (hx' : p.obj x' = algebraOver A' B S hS
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap) hA')
    (hx'S : (p ⋙ Over.post B.inclusion).obj x' =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap))
    (lift : x ⟶ x')
    (hlift : schemeMap (p ⋙ Over.post B.inclusion) hxS hx'S lift =
      Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hlifts : LiftsAtResiduePoint (Λ := Λ) (k := κ) baseMap (p ⋙ Over.post B.inclusion)
      (Over.mk toS) x hxS (Spec.map (CommRingCat.ofHom ε.toRingHom))) :
    ∃ σ : A →ₐ[Λ] (powQuotientObj ε' hε' n : Type u),
      ∀ t : A, (powQuotientMap hφ hε' hε n).hom (σ t) =
        Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n) t := by
  let : p.IsFibered := hp.isFibered
  -- the restriction of `x` to `Spec (A ⧸ 𝔭 ^ n)`, with its arrow to `x` over the quotient map
  obtain ⟨y, hy, a, ha⟩ : ∃ (y : X) (hy : (p ⋙ Over.post B.inclusion).obj y = Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap Λ (A ⧸ RingHom.ker ε.toRingHom ^ n))) ≫ baseMap))
      (a : y ⟶ x), schemeMap (p ⋙ Over.post B.inclusion) hy hxS a =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n))) :=
    ⟨_, _, _, schemeMap_restrictAlongArrow_mk _ B S hS toS _ hA hC
      (specMap_quotientMk_comp _ baseMap toS hbase) p x hx hxS⟩
  -- the restriction of the lift `x'` to `Spec (A' ⧸ (𝔭') ^ n)`
  obtain ⟨z, hz, r, hr⟩ : ∃ (z : X) (hz : (p ⋙ Over.post B.inclusion).obj z = Over.mk
        (Spec.map (CommRingCat.ofHom
          (algebraMap Λ (A' ⧸ RingHom.ker ε'.toRingHom ^ n))) ≫ baseMap))
      (r : z ⟶ x'), schemeMap (p ⋙ Over.post B.inclusion) hz hx'S r =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker ε'.toRingHom ^ n))) :=
    ⟨_, _, _, schemeMap_restrictAlongArrow_mk _ B S hS _ _ hA' hC'
      (specMap_quotientMk_comp _ baseMap _ rfl) p x' hx' hx'S⟩
  -- the arrow of the square, over the spectrum of the small extension
  have hmkq : CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker ε'.toRingHom ^ n)) ≫
      CommRingCat.ofHom (powQuotientMapAlgHom hφ n).toRingHom =
      CommRingCat.ofHom φ.toRingHom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n)) := by
    ext t
    exact powQuotientMapAlgHom_mk hφ n t
  have hfS : Spec.map (CommRingCat.ofHom (powQuotientMapAlgHom hφ n).toRingHom) ≫
      (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ (A' ⧸ RingHom.ker ε'.toRingHom ^ n))) ≫ baseMap)).hom =
      (Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap Λ (A ⧸ RingHom.ker ε.toRingHom ^ n))) ≫ baseMap)).hom := by
    exact specMap_algHom_comp_algebraMap_comp (powQuotientMapAlgHom hφ n) baseMap
  have hsquare : Spec.map (CommRingCat.ofHom (powQuotientMapAlgHom hφ n).toRingHom) ≫
      schemeMap (p ⋙ Over.post B.inclusion) hz hx'S r =
      schemeMap (p ⋙ Over.post B.inclusion) hy hx'S (a ≫ lift) := by
    rw [schemeMap_comp (p ⋙ Over.post B.inclusion) hy hxS hx'S a lift, ha, hlift, hr,
      ← Spec.map_comp, ← Spec.map_comp, hmkq]
  obtain ⟨i, ⟨hi, -⟩, -⟩ := exists_unique_schemeMap_eq_of_square B S hS p hp hy hz hx'S r
    (a ≫ lift) (Spec.map (CommRingCat.ofHom (powQuotientMapAlgHom hφ n).toRingHom)) hfS hsquare
  -- versality supplies the arrow `b`: the arrow `a` restricts to the chosen residue point
  have hmkaug : CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker ε.toRingHom ^ n)) ≫
      CommRingCat.ofHom (powQuotientAug ε n).toRingHom = CommRingCat.ofHom ε.toRingHom := by
    ext t
    rfl
  obtain ⟨b, hb⟩ : ∃ b : z ⟶ x, i ≫ b = a := by
    refine hlifts (powQuotientObj ε hε n) (powQuotientObj ε' hε' n)
      (powQuotientMap hφ hε' hε n) (powQuotientMapAlgHom_surjective hφ n hsurjφ)
      y z hy hz i hi a ?_
    show Spec.map (CommRingCat.ofHom (powQuotientAug ε n).toRingHom) ≫
      schemeMap (p ⋙ Over.post B.inclusion) hy hxS a = Spec.map (CommRingCat.ofHom ε.toRingHom)
    rw [ha, ← Spec.map_comp, hmkaug]
  have hover : schemeMap (p ⋙ Over.post B.inclusion) hz hxS b ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Λ (A' ⧸ RingHom.ker ε'.toRingHom ^ n))) ≫ baseMap := by
    rw [hbase]
    exact schemeMap_over (p ⋙ Over.post B.inclusion) hz hxS b
  exact ⟨algHom_of_schemeMap_over baseMap _ hover,
    RingHom.congr_fun (comp_ringHom_of_schemeMap_of_comp_eq _ hy hz hxS hb hi ha)⟩

end SquareLift

end Deformation.Artin
