module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpoints
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftTorsor
public import StacksFrontier.Deformation.RimSchlessingerCategory.AutomorphismLifting
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpointsSupplied

/-!
# The class of a lift of a morphism of schemes to a pair of deformations

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`, let `P` be a deformation of `X` and
`Q` a deformation of `Y` over one object `A` of `𝒞_Λ`, and let `ℓ : P.scheme ⟶ Q.scheme` be a
lift of `f` over `baseSpec A` in the sense of `Deformation.Examples.globalLiftsOverBase`. Such
a lift *is* a deformation of `f`: the pair `(P.scheme, Q.scheme)` with the arrow `ℓ` between
them is a flat family of morphisms of schemes over `A`, and the two special-fibre immersions of
`P` and of `Q` exhibit `f : X ⟶ Y` as its fibre over the closed point. This file builds that
object of `Def_{X ⟶ Y}`, reads its class in the tangent module, and identifies the lifts among
the first-order deformations of `f`.

This is the `cls` map and the hypothesis `hc` of
`Deformation.exact_triple_of_simplyTransitiveVAdd`, the torsor form of the three interior spots
of the six-term exact sequence of [Stacks Project, Tag 0E3V].

## Main definitions

* `Deformation.Examples.liftSchemeMorphismFamily`: the flat family of morphisms of schemes over
  `Q.base` attached to a lift.
* `Deformation.Examples.liftSpecialFiberHom`: its arrow down to the special-fibre family, built
  from the two special-fibre immersions.
* `Deformation.Examples.liftDeformationObject`: the resulting object of
  `Deformation.Examples.schemeMorphismDeformationCategory`, and
  `Deformation.Examples.liftDeformationFiberObject` the same thing read in the fibre over a base
  object.
* `Deformation.Examples.liftClass`: **the `cls` map of [Stacks Project, Tag 0E3V]**, the class of
  a lift in the tangent module of `Def_{X ⟶ Y}`.

## Main results

* `Deformation.Examples.isPullback_of_globalLift`: the square formed by `f`, the lift and the two
  special-fibre immersions is cartesian. This is the `source_pullback` condition of
  `Deformation.Examples.SchemeMorphismFamily.Hom`, and the only nonformal input to
  `Deformation.Examples.liftSpecialFiberHom`.
* `Deformation.Examples.isIsomorphic_sourceFiber_liftDeformationFiberObject` and
  `Deformation.Examples.isIsomorphic_targetFiber_liftDeformationFiberObject`: the two endpoints
  of the deformation of `f` attached to a lift are the given deformations `P` and `Q`, up to
  isomorphism in their fibres.
* `Deformation.Examples.liftClass_mem_ker`: the class of a lift dies in `T(Def_X × Def_Y)`.
* `Deformation.Examples.isIsomorphic_liftDeformationFiberObject_of_familyHom`: an arrow of flat
  families with the three compatibilities exhibits a first-order deformation of `f` as the one
  attached to a lift.
* `Deformation.Examples.exists_globalLift_of_isIsomorphic_endpoints`: a first-order deformation
  of `f` both of whose endpoints are isomorphic, in their fibres, to the given deformations `P`
  and `Q` comes from a lift `P.scheme ⟶ Q.scheme`.
* `Deformation.Examples.exists_liftClass_iff`: **the `hc` input of
  `Deformation.exact_triple_of_simplyTransitiveVAdd`.** A first-order deformation of `f` is
  killed by the arrow to `T(Def_X × Def_Y)` exactly when it is the class of a lift. This is the
  source's "if some first order deformation `(f_ε : X_ε → Y_ε)` maps to zero in
  `T(Def_X × Def_Y)`, then we can choose isomorphisms `X' → X_ε` and `Y' → Y_ε` and we conclude
  we are in the image of the south-west arrow".
* `Deformation.Examples.liftClass_eq_liftClass_iff` and
  `Deformation.Examples.liftClass_eq_zero_iff`: **the `hcls` input.** Two lifts have the same
  class exactly when a pair of isomorphisms of the two total spaces over the base, compatible
  with the special fibres, carries one to the other — the source's "`(f_ε : X' → Y')` is
  isomorphic to the trivial deformation `(f' : X' → Y')` exactly when `f_ε = β⁻¹ ∘ f' ∘ α`".

## Implementation notes

**The two bases.** `Deformation.Examples.globalLiftsOverBase` takes a morphism
`e : Q.base ⟶ P.base` of `𝒞_Λ` rather than asking the two deformations to have equal bases,
because the structure morphism of `P` would otherwise have to be transported along an equality
of schemes. The family a lift gives rise to lives over `Q.base`, and its source structure
morphism is the composite `P.toBase ≫ baseSpecMap e`; for that composite to be **flat**, as a
flat family requires, `e` must be invertible. So `e` is carried here with an `IsIso` instance.
The case the six-term sequence needs is `P.base = Q.base` and `e = 𝟙`, which is invertible; for
two deformations whose bases are equal only up to a proof `h`, take `e = eqToHom h`.

**Which square is cartesian.** The `source_pullback` field of
`Deformation.Examples.SchemeMorphismFamily.Hom` is a cartesian square of *schemes* not
mentioning the base: it asks that `X` be the fibre product of `Y` and `P.scheme` over
`Q.scheme`. The two conditions defining a lift only give that the square commutes, so this is
proved rather than read off: `Deformation.Examples.isPullback_of_globalLift` cancels
`Q.specialCartesian` off the rectangle obtained by pasting `P.specialCartesian` with the
square identifying the two closed points of `baseSpec P.base` and `baseSpec Q.base`, which is
cartesian because `baseSpecMap e` is invertible.

**The two endpoints.** The source-forgetful functor does *not* send the deformation of `f`
attached to a lift to `P` on the nose: it sends it to `P` with its base replaced by `Q.base` and
its structure morphism composed with `baseSpecMap e`. The comparison arrow is the identity on
`P.scheme` over `e`, and it is cartesian because `baseSpecMap e` is invertible; that is
`Deformation.Examples.isIsomorphic_sourceFiber_liftDeformationFiberObject`. On the target side
the forgetful functor does hit `Q` on the nose, but the fibre objects still differ by the
proofs they carry, so the comparison is recorded in the same shape.

**Triviality is a hypothesis, not a construction.** `Deformation.Examples.exists_liftClass_iff`
asks that the classes of `P` and of `Q` in the tangent modules of `Def_X` and `Def_Y` vanish —
that is what makes `P` and `Q` the *trivial* first-order deformations of the source's proof. It
is supplied in the assembled sequence by `Deformation.tangentClassAt_pushforward_eq_zero`, and
is kept as a hypothesis here so that no choice of pushforward enters this file.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

section LiftClass

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-! ### The deformation of `f` attached to a lift -/

/-- **The square of a lift is cartesian.** For a lift `ℓ : P.scheme ⟶ Q.scheme` of `f` over
`baseSpec Q.base` the square
```
X  --f-->  Y
|          |
v          v
P.scheme --ℓ--> Q.scheme
```
whose vertical arrows are the two special-fibre immersions is a pullback square. Pasting
`P.specialCartesian` with the square comparing the closed points of `baseSpec P.base` and
`baseSpec Q.base` — cartesian because `baseSpecMap e` is invertible — exhibits the rectangle
obtained by following `Q.toBase` as cartesian, and `Q.specialCartesian` cancels off its right
half. -/
theorem isPullback_of_globalLift (hf : f ≫ pY = pX)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e] (ℓ : globalLiftsOverBase f P Q e) :
    IsPullback f P.specialMap Q.specialMap ℓ.1 := by
  have hPc : IsPullback pX P.specialMap (residueSpecMap P.base) P.toBase :=
    P.specialCartesian.flip
  have hQc : IsPullback pY Q.specialMap (residueSpecMap Q.base) Q.toBase :=
    Q.specialCartesian.flip
  have hsq : IsPullback (𝟙 (Spec (CommRingCat.of k))) (residueSpecMap P.base)
      (residueSpecMap Q.base) (baseSpecMap e) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, residueSpecMap_naturality]⟩
  have h : IsPullback pX P.specialMap (residueSpecMap Q.base) (P.toBase ≫ baseSpecMap e) := by
    have h0 := hPc.paste_horiz hsq
    rwa [Category.comp_id] at h0
  have hb : ℓ.1 ≫ Q.toBase = P.toBase ≫ baseSpecMap e := ℓ.2.1
  have hs : f ≫ Q.specialMap = P.specialMap ≫ ℓ.1 := ℓ.2.2.symm
  refine IsPullback.of_right ?_ hs hQc
  rw [hf, hb]
  exact h

/-- **The flat family of morphisms of schemes attached to a lift.** The two total spaces with
the lift between them, over the base of `Q`: the condition that the lift is a morphism over
`baseSpec Q.base` is the `over_base` field, the target is flat because `Q` is, and the source is
flat because `P` is and `baseSpecMap e` is invertible. -/
def liftSchemeMorphismFamily
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e] (ℓ : globalLiftsOverBase f P Q e) :
    SchemeMorphismFamily.{u, u} Λ k where
  base := Q.base
  source := P.scheme
  target := Q.scheme
  morphism := ℓ.1
  sourceToBase := deformationAmbientToBase P e
  targetToBase := Q.toBase
  over_base := ℓ.2.1
  source_flat := by
    have := P.flat
    infer_instance
  target_flat := Q.flat

/-- **The arrow from the family of a lift to the special-fibre family.** Its two scheme
components are the special-fibre immersions of `P` and of `Q`, its component on bases is the
unique morphism to the terminal object `residueFieldBase Λ k`, the cartesian square on the
target is `Q.specialCartesian` and the cartesian square on the source is
`Deformation.Examples.isPullback_of_globalLift`. -/
def liftSpecialFiberHom
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e] (ℓ : globalLiftsOverBase f P Q e) :
    liftSchemeMorphismFamily f pX pY ℓ ⟶ schemeMorphismFamilySpecialFiber f pX pY hf where
  base := (isTerminal_residueFieldBase (Λ := Λ) (k := k)).from Q.base
  source := P.specialMap
  target := Q.specialMap
  source_pullback := isPullback_of_globalLift f pX pY hf ℓ
  target_pullback := by
    change IsPullback Q.specialMap pY Q.toBase
      (baseSpecMap ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).from Q.base))
    rw [baseSpecMap_eq_residueSpecMap]
    exact Q.specialCartesian

/-- **A lift of `f` is a deformation of `f`.** The object of
`Deformation.Examples.schemeMorphismDeformationCategory` determined by a lift: the family
`Deformation.Examples.liftSchemeMorphismFamily` with its arrow
`Deformation.Examples.liftSpecialFiberHom` down to the special fibre. -/
def liftDeformationObject
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e] (ℓ : globalLiftsOverBase f P Q e) :
    schemeMorphismDeformationCategory f pX pY hf :=
  Over.mk (liftSpecialFiberHom f pX pY hf ℓ)

/-- The base of the deformation `Deformation.Examples.liftDeformationObject` determined by a
lift is the base `Q.base` of the deformation of the target. -/
@[simp]
theorem liftDeformationObject_left_base
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e] (ℓ : globalLiftsOverBase f P Q e) :
    (liftDeformationObject f pX pY hf ℓ).left.base = Q.base := rfl

/-- **A lift of `f`, read in the fibre of `Def_{X ⟶ Y}` over a base object.** The object
`Deformation.Examples.liftDeformationObject` together with the identification of its base with
the given object `A` of `𝒞_Λ`. -/
def liftDeformationFiberObject
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e] {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hQ : Q.base = A) (ℓ : globalLiftsOverBase f P Q e) :
    (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber A :=
  ⟨liftDeformationObject f pX pY hf ℓ, hQ⟩

/-! ### The class of a lift -/

/-- **The `cls` map of [Stacks Project, Tag 0E3V].** The class in the tangent module of
`Def_{X ⟶ Y}` of the first-order deformation of `f` determined by a lift of `f` to a pair of
first-order deformations of its endpoints. -/
def liftClass
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e]
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (ℓ : globalLiftsOverBase f P Q e) :
    ↥(tangentModuleAt.{u, u, u}
      (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM M) :=
  tangentClassAt.{u, u, u}
    (BasedCategory.ofFunctor (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM M
    (liftDeformationFiberObject f pX pY hf hQ ℓ)

/-! ### The two endpoints of the deformation attached to a lift -/

/-- A morphism in a groupoid exhibits its source and target as isomorphic. -/
private theorem isIsomorphic_of_isGroupoid {C : Type*} [Category C] (hg : IsGroupoid C)
    {a b : C} (ψ : a ⟶ b) : IsIsomorphic a b :=
  have := hg.all_isIso ψ
  ⟨asIso ψ⟩

/-- The components `map` on total spaces of an isomorphism in a fibre of the projection of the
deformation category of a scheme are mutually inverse. -/
private theorem map_inv_comp_map_hom {T : Over (Spec (CommRingCat.of k))}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {a b : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) T).Fiber A} (σ : a ≅ b) :
    σ.inv.1.map ≫ σ.hom.1.map = 𝟙 a.1.scheme :=
  congrArg SchemeDeformationCategory.Hom.map (congrArg Subtype.val σ.hom_inv_id)

/-- A morphism in a fibre of the projection of the deformation category of a scheme lies over
the identity of the base object. -/
private theorem base_eq_of_fiber_hom {T : Over (Spec (CommRingCat.of k))}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {a b : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) T).Fiber A} (φ : a ⟶ b) :
    φ.1.base = eqToHom a.2 ≫ 𝟙 A ≫ eqToHom b.2.symm :=
  have := φ.2
  IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) T) (𝟙 A) φ.1

/-- **The source endpoint of the deformation of `f` attached to a lift is `P`.** The
source-forgetful functor sends the deformation of `f` built from a lift to `P` with its base
replaced by that of `Q` and its structure morphism composed with `baseSpecMap e`; the identity
of `P.scheme` over `e` is an arrow back to `P`, cartesian because `baseSpecMap e` is invertible,
and every arrow in a fibre of a category cofibered in groupoids is invertible. -/
theorem isIsomorphic_sourceFiber_liftDeformationFiberObject
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (hP : P.base = A) (hQ : Q.base = A)
    (ℓ : globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm))) :
    IsIsomorphic
      ((fiberFunctor (schemeMorphismSourceBased f pX pY hf) A).obj
        (liftDeformationFiberObject f pX pY hf hQ ℓ))
      (⟨P, hP⟩ : (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))).p.Fiber A) := by
  have hcart : IsPullback (𝟙 P.scheme) P.toBase
      (P.toBase ≫ baseSpecMap (eqToHom (hQ.trans hP.symm)))
      (baseSpecMap (eqToHom (hQ.trans hP.symm))) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp]⟩
  let φ : SchemeDeformationCategory.Hom
      ((schemeMorphismSourceForgetful f pX pY hf).obj (liftDeformationObject f pX pY hf ℓ)) P :=
    { base := eqToHom (hQ.trans hP.symm)
      map := 𝟙 P.scheme
      cartesian := hcart
      special_compat := Category.comp_id _ }
  have hlift : (schemeDeformationCategoryProjection (Λ := Λ) (k := k)
      (Over.mk pX)).IsHomLift (𝟙 A) φ := by
    refine IsHomLift.of_fac'
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)) (𝟙 A) φ hQ hP ?_
    change eqToHom (hQ.trans hP.symm) = eqToHom hQ ≫ 𝟙 A ≫ eqToHom hP.symm
    simp
  let ψ : (fiberFunctor (schemeMorphismSourceBased f pX pY hf) A).obj
      (liftDeformationFiberObject f pX pY hf hQ ℓ) ⟶
      (⟨P, hP⟩ : (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))).p.Fiber A) :=
    ⟨φ, hlift⟩
  exact isIsomorphic_of_isGroupoid (fiber_isGroupoid _ hX.predeformation.cofibered A) ψ

/-- **The target endpoint of the deformation of `f` attached to a lift is `Q`.** Unlike on the
source side the target-forgetful functor hits `Q` on the nose: the family of a lift is built
over the base of `Q` with `Q.toBase` as its target structure morphism. -/
theorem isIsomorphic_targetFiber_liftDeformationFiberObject
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e] {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (hQ : Q.base = A)
    (ℓ : globalLiftsOverBase f P Q e) :
    IsIsomorphic
      ((fiberFunctor (schemeMorphismTargetBased f pX pY hf) A).obj
        (liftDeformationFiberObject f pX pY hf hQ ℓ))
      (⟨Q, hQ⟩ : (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))).p.Fiber A) :=
  ⟨Iso.refl _⟩

/-- **The class of a lift dies in `T(Def_X × Def_Y)`.** The two endpoints of the deformation of
`f` attached to a lift are `P` and `Q` up to isomorphism in their fibres, so if the classes of
`P` and of `Q` vanish — that is, if `P` and `Q` are the *trivial* first-order deformations of
`X` and of `Y` — then so does the image of the class of the lift. This is the easy half of
`Deformation.Examples.exists_liftClass_iff`. -/
theorem liftClass_mem_ker
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (hP : P.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hP0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M ⟨P, hP⟩ = 0)
    (hQ0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M ⟨Q, hQ⟩ = 0)
    (ℓ : globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm))) :
    schemeMorphismTangentPair f pX pY hf hM hX hY M
      (liftClass f pX pY hf hM M hQ ℓ) = 0 := by
  refine Prod.ext ?_ ?_
  · exact (tangentMapAt_tangentClassAt.{u, u, u} hM hX (schemeMorphismSourceBased f pX pY hf) M
      (liftDeformationFiberObject f pX pY hf hQ ℓ)).trans
      (((tangentClassAt_eq_iff.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M _ _).mpr
          (isIsomorphic_sourceFiber_liftDeformationFiberObject f pX pY hf hX hP hQ ℓ)).trans hP0)
  · exact (tangentMapAt_tangentClassAt.{u, u, u} hM hY (schemeMorphismTargetBased f pX pY hf) M
      (liftDeformationFiberObject f pX pY hf hQ ℓ)).trans
      (((tangentClassAt_eq_iff.{u, u, u} (BasedCategory.ofFunctor
            (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M _ _).mpr
          (isIsomorphic_targetFiber_liftDeformationFiberObject f pX pY hf hQ ℓ)).trans hQ0)

/-! ### Recognising the deformations of `f` that come from lifts -/

/-- A morphism of schemes equal to an identity is invertible. Stated with the equation as an
argument so that it applies to a morphism whose source and target are spelled through a chain
of definitions. -/
private theorem isIso_of_eq_id {S : Scheme.{u}} (g : S ⟶ S) (h : g = 𝟙 S) : IsIso g := by
  rw [h]; infer_instance

/-- A square of schemes whose top and bottom arrows are isomorphisms is cartesian. This is
`CategoryTheory.IsPullback.of_horiz_isIso` with the two invertibility hypotheses taken as
arguments rather than as instances. -/
private theorem isPullback_of_isIso_horiz {S T U V : Scheme.{u}} (fst : S ⟶ T) (snd : S ⟶ U)
    (fm : T ⟶ V) (g : U ⟶ V) (hfst : IsIso fst) (hg : IsIso g) (w : fst ≫ fm = snd ≫ g) :
    IsPullback fst snd fm g :=
  have := hfst
  have := hg
  IsPullback.of_horiz_isIso ⟨w⟩

/-- The first projection of a cartesian square whose bottom arrow is invertible is invertible.
This is `CategoryTheory.IsPullback.isIso_fst_of_isIso` with the invertibility hypothesis taken
as an argument rather than as an instance. -/
private theorem isIso_fst_of_isPullback {S T U V : Scheme.{u}} {fst : S ⟶ T} {snd : S ⟶ U}
    {fm : T ⟶ V} {g : U ⟶ V} (hg : IsIso g) (h : IsPullback fst snd fm g) : IsIso fst :=
  have := hg
  h.isIso_fst_of_isIso

/-- A square of schemes whose two vertical arrows are isomorphisms is cartesian. This is
`CategoryTheory.IsPullback.of_vert_isIso` with the two invertibility hypotheses taken as
arguments rather than as instances, so that it applies to morphisms whose source and target are
spelled through a chain of definitions. -/
private theorem isPullback_of_isIso_vert {S T U V : Scheme.{u}} (m : S ⟶ T) (es : S ⟶ U)
    (et : T ⟶ V) (hes : IsIso es) (het : IsIso et) (b : U ⟶ V) (w : m ≫ et = es ≫ b) :
    IsPullback m es et b :=
  have := hes
  have := het
  IsPullback.of_vert_isIso ⟨w⟩


/-- **An arrow of families exhibits a deformation of `f` as the one attached to a lift.** The
data is an arrow of flat families from `Deformation.Examples.liftSchemeMorphismFamily` to the
given deformation of `f`, assembled from its three components: the cartesian squares are the
hypotheses `hsp` and `htp`, compatibility with the special fibres is `hss` and `hts`, and `heb`
says that the component on bases lifts the identity of `A`. Every arrow in a fibre of a category
cofibered in groupoids is invertible, so such an arrow is enough. -/
theorem isIsomorphic_liftDeformationFiberObject_of_familyHom
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e] {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (hQ : Q.base = A)
    (ℓ : globalLiftsOverBase f P Q e)
    (mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber A)
    (hA : mε.1.left.base = A) (eb : Q.base ⟶ mε.1.left.base)
    (es : mε.1.left.source ⟶ P.scheme) (et : mε.1.left.target ⟶ Q.scheme)
    (hsp : IsPullback mε.1.left.morphism es et ℓ.1)
    (htp : IsPullback et mε.1.left.targetToBase Q.toBase (baseSpecMap eb))
    (hss : mε.1.hom.source ≫ es = P.specialMap)
    (hts : mε.1.hom.target ≫ et = Q.specialMap)
    (heb : eb = eqToHom hQ ≫ 𝟙 A ≫ eqToHom hA.symm) :
    IsIsomorphic (liftDeformationFiberObject f pX pY hf hQ ℓ) mε := by
  let ψ : liftSchemeMorphismFamily f pX pY ℓ ⟶ mε.1.left :=
    { base := eb
      source := es
      target := et
      source_pullback := hsp
      target_pullback := htp }
  have hover : ψ ≫ mε.1.hom = liftSpecialFiberHom f pX pY hf ℓ :=
    SchemeMorphismFamily.Hom.ext (isTerminal_residueFieldBase.hom_ext _ _) hss hts
  let Φ : liftDeformationObject f pX pY hf ℓ ⟶ mε.1 := Over.homMk ψ hover
  have hliftΦ : (schemeMorphismDeformationCategoryProjection f pX pY hf).IsHomLift (𝟙 A) Φ :=
    IsHomLift.of_fac' (schemeMorphismDeformationCategoryProjection f pX pY hf) (𝟙 A) Φ hQ hA heb
  let Ψ : liftDeformationFiberObject f pX pY hf hQ ℓ ⟶ mε := ⟨Φ, hliftΦ⟩
  exact isIsomorphic_of_isGroupoid (fiber_isGroupoid _ hM.predeformation.cofibered A) Ψ

/-- **A deformation of `f` with trivial endpoints is a lift.** This is the geometric step of the
source's "we can choose isomorphisms `X' → X_ε` and `Y' → Y_ε` and we conclude we are in the
image of the south-west arrow": given a first-order deformation `mε` of `f` and isomorphisms, in
the two fibres, of its endpoints with `P` and with `Q`, transporting the arrow of `mε` along them
gives a lift `P.scheme ⟶ Q.scheme` of `f`, and `mε` is the deformation of `f` that lift
determines.

The two conditions defining a lift come out of the two isomorphisms: the condition over the base
from their cartesian squares together with the fact that their components on bases lift the
identity, the condition on the special fibre from their compatibilities with the special-fibre
immersions. -/
theorem exists_globalLift_of_isIsomorphic_endpoints
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (hP : P.base = A) (hQ : Q.base = A)
    (mε : (schemeMorphismDeformationCategoryProjection f pX pY hf).Fiber A)
    (hsrc : IsIsomorphic ((fiberFunctor (schemeMorphismSourceBased f pX pY hf) A).obj mε)
      (⟨P, hP⟩ : (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))).p.Fiber A))
    (htgt : IsIsomorphic ((fiberFunctor (schemeMorphismTargetBased f pX pY hf) A).obj mε)
      (⟨Q, hQ⟩ : (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))).p.Fiber A)) :
    ∃ ℓ : globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm)),
      IsIsomorphic (liftDeformationFiberObject f pX pY hf hQ ℓ) mε := by
  obtain ⟨σ⟩ := hsrc
  obtain ⟨τ⟩ := htgt
  have hA : mε.1.left.base = A := mε.2
  have hsb := base_eq_of_fiber_hom σ.hom
  have htb := base_eq_of_fiber_hom τ.inv
  have hbb : τ.inv.1.base ≫ σ.hom.1.base = eqToHom (hQ.trans hP.symm) := by
    rw [hsb, htb]
    simp only [Category.id_comp, eqToHom_trans]
    apply eqToHom_trans
  have e1 : σ.inv.1.map ≫ σ.hom.1.map = 𝟙 mε.1.left.source := map_inv_comp_map_hom σ
  have hisoσ : IsIso (σ.inv.1.map : mε.1.left.source ⟶ P.scheme) :=
    ⟨⟨σ.hom.1.map, e1, map_inv_comp_map_hom σ.symm⟩⟩
  have hisoτ : IsIso (τ.inv.1.map : mε.1.left.target ⟶ Q.scheme) :=
    ⟨⟨τ.hom.1.map, map_inv_comp_map_hom τ, map_inv_comp_map_hom τ.symm⟩⟩
  have hsc : σ.hom.1.map ≫ mε.1.left.sourceToBase = P.toBase ≫ baseSpecMap σ.hom.1.base :=
    σ.hom.1.cartesian.w
  have htc : τ.inv.1.map ≫ Q.toBase =
      mε.1.left.targetToBase ≫ baseSpecMap τ.inv.1.base := τ.inv.1.cartesian.w
  have hcomp : baseSpecMap σ.hom.1.base ≫ baseSpecMap τ.inv.1.base =
      baseSpecMap (eqToHom (hQ.trans hP.symm)) :=
    (baseSpecMap_comp τ.inv.1.base σ.hom.1.base).symm.trans (congrArg baseSpecMap hbb)
  have hcond₁ : (σ.hom.1.map ≫ mε.1.left.morphism ≫ τ.inv.1.map) ≫ Q.toBase =
      P.toBase ≫ baseSpecMap (eqToHom (hQ.trans hP.symm)) := by
    erw [Category.assoc, Category.assoc, htc, reassoc_of% mε.1.left.over_base,
      ← Category.assoc, hsc, Category.assoc, hcomp]
  have hs2 : P.specialMap ≫ σ.hom.1.map = mε.1.hom.source := σ.hom.1.special_compat
  have ht2 : mε.1.hom.target ≫ τ.inv.1.map = Q.specialMap := τ.inv.1.special_compat
  have hcond₂ : P.specialMap ≫ σ.hom.1.map ≫ mε.1.left.morphism ≫ τ.inv.1.map =
      f ≫ Q.specialMap := by
    erw [reassoc_of% hs2, ← reassoc_of% mε.1.hom.source_pullback.w, ht2]
    rfl
  have hwsq : mε.1.left.morphism ≫ τ.inv.1.map =
      σ.inv.1.map ≫ σ.hom.1.map ≫ mε.1.left.morphism ≫ τ.inv.1.map := by
    rw [reassoc_of% e1]
    exact (Category.id_comp _).symm
  refine ⟨⟨σ.hom.1.map ≫ mε.1.left.morphism ≫ τ.inv.1.map, hcond₁, hcond₂⟩, ?_⟩
  exact isIsomorphic_liftDeformationFiberObject_of_familyHom f pX pY hf hM hQ _ mε hA
    τ.inv.1.base σ.inv.1.map τ.inv.1.map
    (isPullback_of_isIso_vert _ _ _ hisoσ hisoτ _ hwsq) τ.inv.1.cartesian
    σ.inv.1.special_compat ht2 htb

/-- **The `hc` input of `Deformation.exact_triple_of_simplyTransitiveVAdd` for
[Stacks Project, Tag 0E3V].** Let `P` and `Q` be *trivial* first-order deformations of `X` and of
`Y` — that is, first-order deformations whose classes in the tangent modules of `Def_X` and
`Def_Y` vanish. Then an element of `T Def_{X ⟶ Y}` is killed by the arrow to
`T(Def_X × Def_Y)` exactly when it is the class of a lift `P.scheme ⟶ Q.scheme` of `f`.

One direction is `Deformation.Examples.liftClass_mem_ker`. For the other, the element is the
class of some first-order deformation of `f` (`Deformation.tangentClassAt_surjective`); its two
endpoint classes agree with those of `P` and of `Q`, hence (`Deformation.tangentClassAt_eq_iff`)
its endpoints are isomorphic to `P` and to `Q` in their fibres, and
`Deformation.Examples.exists_globalLift_of_isIsomorphic_endpoints` turns those two isomorphisms
into a lift with the given class. -/
theorem exists_liftClass_iff
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (hX : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)))
    (hY : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (hP : P.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (hP0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M ⟨P, hP⟩ = 0)
    (hQ0 : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M ⟨Q, hQ⟩ = 0)
    (t : ↥(tangentModuleAt.{u, u, u} (BasedCategory.ofFunctor
      (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM M)) :
    schemeMorphismTangentPair f pX pY hf hM hX hY M t = 0 ↔
      ∃ ℓ : globalLiftsOverBase f P Q (eqToHom (hQ.trans hP.symm)),
        liftClass f pX pY hf hM M hQ ℓ = t := by
  refine ⟨fun hzero => ?_, ?_⟩
  · obtain ⟨mε, hmε⟩ := tangentClassAt_surjective.{u, u, u} (BasedCategory.ofFunctor
      (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM M t
    subst hmε
    have h₁ : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M
          ((fiberFunctor (schemeMorphismSourceBased f pX pY hf)
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) =
        tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))) hX M ⟨P, hP⟩ :=
      ((tangentMapAt_tangentClassAt.{u, u, u} hM hX
        (schemeMorphismSourceBased f pX pY hf) M mε).symm.trans
          (congrArg Prod.fst hzero)).trans hP0.symm
    have h₂ : tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M
          ((fiberFunctor (schemeMorphismTargetBased f pX pY hf)
            ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)).obj mε) =
        tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
          (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))) hY M ⟨Q, hQ⟩ :=
      ((tangentMapAt_tangentClassAt.{u, u, u} hM hY
        (schemeMorphismTargetBased f pX pY hf) M mε).symm.trans
          (congrArg Prod.snd hzero)).trans hQ0.symm
    obtain ⟨ℓ, hℓ⟩ := exists_globalLift_of_isIsomorphic_endpoints f pX pY hf hM hP hQ mε
      ((tangentClassAt_eq_iff.{u, u, u} _ hX M _ _).mp h₁)
      ((tangentClassAt_eq_iff.{u, u, u} _ hY M _ _).mp h₂)
    exact ⟨ℓ, (tangentClassAt_eq_iff.{u, u, u} _ hM M _ _).mpr hℓ⟩
  · rintro ⟨ℓ, rfl⟩
    exact liftClass_mem_ker f pX pY hf hM hX hY M hP hQ hP0 hQ0 ℓ

/-! ### Which lifts have the same class -/

/-- **The `hcls` input of `Deformation.exact_triple_of_simplyTransitiveVAdd` for
[Stacks Project, Tag 0E3V].** Two lifts of `f` to the same pair of deformations determine the
same first-order deformation of `f` exactly when a pair `(α, β)` of automorphisms of the two
total spaces, each over the base and each restricting to the identity on the special fibre,
carries one to the other: `ℓ' ≫ β = α ≫ ℓ`, the source's "`f_ε = β⁻¹ ∘ f' ∘ α`".

An isomorphism of the two deformations of `f` in the fibre *is* such a pair: its component on
bases lifts the identity of the base object, hence is the identity, which makes the cartesian
square on the targets say that `β` is over the base; compatibility with the arrow down to the
special fibre says that `α` and `β` restrict to the identity there; and the cartesian square on
the sources is exactly the relation between the two lifts. Conversely such a pair assembles into
an arrow of flat families over the identity of the base, cartesian because `α` and `β` are
invertible, and every arrow in a fibre of a category cofibered in groupoids is invertible.

That `α` is over the base is not listed: it follows, since `β` is and `baseSpecMap e` is a
monomorphism. -/
theorem liftClass_eq_liftClass_iff
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e]
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (ℓ ℓ' : globalLiftsOverBase f P Q e) :
    liftClass f pX pY hf hM M hQ ℓ = liftClass f pX pY hf hM M hQ ℓ' ↔
      ∃ (α : P.scheme ⟶ P.scheme) (β : Q.scheme ⟶ Q.scheme), IsIso α ∧ IsIso β ∧
        β ≫ Q.toBase = Q.toBase ∧ P.specialMap ≫ α = P.specialMap ∧
        Q.specialMap ≫ β = Q.specialMap ∧ ℓ'.1 ≫ β = α ≫ ℓ.1 := by
  have hcl : eqToHom hQ ≫ 𝟙 ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) ≫
      eqToHom hQ.symm = 𝟙 Q.base := by simp
  constructor
  · intro hclass
    obtain ⟨φ⟩ := (tangentClassAt_eq_iff.{u, u, u} (BasedCategory.ofFunctor
      (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM M _ _).mp hclass
    have := φ.hom.2
    have hbase1 : φ.hom.1.left.base = 𝟙 Q.base :=
      (IsHomLift.fac' (BasedCategory.ofFunctor
        (schemeMorphismDeformationCategoryProjection f pX pY hf)).p (𝟙 _) φ.hom.1).trans hcl
    have hbsm : baseSpecMap φ.hom.1.left.base = 𝟙 (baseSpec Q.base) :=
      (congrArg baseSpecMap hbase1).trans (baseSpecMap_id Q.base)
    have hisobsm : IsIso (baseSpecMap φ.hom.1.left.base) := isIso_of_eq_id _ hbsm
    have hβb : φ.hom.1.left.target ≫ Q.toBase = Q.toBase :=
      φ.hom.1.left.target_pullback.w.trans
        ((congrArg (fun z => Q.toBase ≫ z) hbsm).trans (Category.comp_id _))
    have hisoβ : IsIso φ.hom.1.left.target :=
      isIso_fst_of_isPullback hisobsm φ.hom.1.left.target_pullback
    have hisoα : IsIso φ.hom.1.left.source :=
      isIso_fst_of_isPullback hisoβ φ.hom.1.left.source_pullback.flip
    have hαs : P.specialMap ≫ φ.hom.1.left.source = P.specialMap :=
      congrArg SchemeMorphismFamily.Hom.source (Over.w φ.hom.1)
    have hβs : Q.specialMap ≫ φ.hom.1.left.target = Q.specialMap :=
      congrArg SchemeMorphismFamily.Hom.target (Over.w φ.hom.1)
    exact ⟨φ.hom.1.left.source, φ.hom.1.left.target, hisoα, hisoβ, hβb, hαs, hβs,
      φ.hom.1.left.source_pullback.w⟩
  · rintro ⟨α, β, hα, hβ, hβb, hαs, hβs, hαβ⟩
    have hbsmid : IsIso (baseSpecMap (𝟙 Q.base)) := isIso_of_eq_id _ (baseSpecMap_id Q.base)
    have hwtp : β ≫ Q.toBase = Q.toBase ≫ baseSpecMap (𝟙 Q.base) := by
      rw [baseSpecMap_id, Category.comp_id, hβb]
    exact (tangentClassAt_eq_iff.{u, u, u} (BasedCategory.ofFunctor
      (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM M _ _).mpr
      (isIsomorphic_liftDeformationFiberObject_of_familyHom f pX pY hf hM hQ ℓ
        (liftDeformationFiberObject f pX pY hf hQ ℓ') hQ (𝟙 Q.base) α β
        (isPullback_of_isIso_vert _ _ _ hα hβ _ hαβ)
        (isPullback_of_isIso_horiz _ _ _ _ hβ hbsmid hwtp) hαs hβs hcl.symm)

/-- **The class of a lift vanishes exactly when a pair of infinitesimal automorphisms carries
the trivial lift to it.** `Deformation.Examples.liftClass_eq_liftClass_iff` read against a lift
`ℓ₀` whose class is the zero of the tangent module — the *trivial* deformation
`(f' : X' → Y')` of the source's proof. -/
theorem liftClass_eq_zero_iff
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf))
    (M : FGModuleCat.{u} k)
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX)}
    {Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    {e : Q.base ⟶ P.base} [IsIso e]
    (hQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (ℓ₀ ℓ : globalLiftsOverBase f P Q e)
    (h0 : liftClass f pX pY hf hM M hQ ℓ₀ = 0) :
    liftClass f pX pY hf hM M hQ ℓ = 0 ↔
      ∃ (α : P.scheme ⟶ P.scheme) (β : Q.scheme ⟶ Q.scheme), IsIso α ∧ IsIso β ∧
        β ≫ Q.toBase = Q.toBase ∧ P.specialMap ≫ α = P.specialMap ∧
        Q.specialMap ≫ β = Q.specialMap ∧ ℓ₀.1 ≫ β = α ≫ ℓ.1 := by
  rw [← h0]
  exact liftClass_eq_liftClass_iff f pX pY hf hM M hQ ℓ ℓ₀

end LiftClass

end Deformation.Examples

end
