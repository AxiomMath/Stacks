module

public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Examples.Geometric.SpecialFibreFirstOrder
public import StacksFrontier.Deformation.RingedSpaceThickening.FirstOrderIdealMapIso

/-!
# A first-order deformation of a scheme is a solution of the deformation problem of Stacks 08U7

Let `X` be a scheme over a field `k` and let `A` be an object of `𝒞_Λ` whose maximal ideal has
square zero — for instance the dual numbers `k[ε]`, or more generally `k[V]` for a
finite-dimensional `k`-vector space `V`. Write `S = Spec k ⊂ S' = Spec A` for the closed point,
a first order thickening with ideal `𝒥`, and `f : X ⟶ S` for the structure morphism.

A deformation `X'` of `X` over `A` in the sense of [Stacks Project, Tag 0DY7] — a scheme flat over
`Spec A` with a cartesian square identifying its special fibre with `X` — is then a solution of
the deformation problem of [Stacks Project, Tag 08U7] for the thickening `S ⊂ S'`, the module
`𝒢 = f^* 𝒥` and the prescribed map `c` the identity. This is the first step of the proof of
[Stacks Project, Tag 0D14]: there `X` is viewed as a closed subscheme of `X'`, and by
[Stacks Project, Tag 063Y] (here flat base change for the conormal sheaf,
[Stacks Project, Tag 0473]) the ideal sheaf of `X` in `X'` is `f^* 𝒞_{S/S'}`, so that the
diagram of [Stacks Project, Tag 08U7] is filled in.

## Main definitions

* `Deformation.Examples.SchemeDeformationCategory.toSolution`: the solution of the deformation
  problem of Stacks 08U7 attached to a deformation over a base with square-zero maximal ideal.
* `Deformation.Examples.fiberSolution`: the same for a point of the fibre over `A`.
* `Deformation.Examples.fiberHomOfShHom`: a morphism of the fibre from an invertible morphism of
  total spaces, read as ringed spaces, under `X` and over `Spec A`.

## Main results

* `Deformation.Examples.residueSpecMap_isFirstOrderThickening`: the closed point of `Spec A` is a
  first order thickening of ringed spaces when the maximal ideal of `A` has square zero.
* `Deformation.Examples.SchemeDeformationCategory.isIso_conormalSheafMap`: the conormal map of the
  special-fibre square of a deformation is invertible (flat base change).
* `Deformation.Examples.isomorphic_fiberSolution_of_hom` and
  `Deformation.Examples.isIsomorphic_of_isomorphic_fiberSolution`: two points of the fibre are
  isomorphic exactly when their solutions are.

## References

* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction AlgebraicGeometry.RingedSpaceThickening

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The base thickening -/

/-- The ideal sheaf of the closed point of `Spec A` has square zero when the maximal ideal of `A`
does: the closed point is its own base change. -/
theorem residueSpecMap_ker_sq_eq_bot (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) : (residueSpecMap A).ker ^ 2 = ⊥ :=
  ker_sq_eq_bot_of_isPullback (𝟙 _) (IsPullback.id_vert (residueSpecMap A)) hA

/-- **The closed point `Spec k ⊂ Spec A` is a first order thickening of ringed spaces** when the
maximal ideal of `A` has square zero. -/
theorem residueSpecMap_isFirstOrderThickening (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    IsFirstOrderThickening (residueSpecMap A).toLRSHom.toShHom :=
  have := residueSpecMap_isClosedImmersion A
  Stacks.Thickenings.isFirstOrderThickening_toShHom _ (residueSpecMap_ker_sq_eq_bot A hA)

namespace SchemeDeformationCategory

variable {X : Over (Spec (CommRingCat.of k))} (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)

/-- The special-fibre immersion of a deformation over a base with square-zero maximal ideal is a
first order thickening of ringed spaces. -/
theorem specialMap_isFirstOrderThickening
    (hA : IsLocalRing.maximalIdeal (P.base : Type u) ^ 2 = ⊥) :
    IsFirstOrderThickening P.specialMap.toLRSHom.toShHom :=
  have := deformationSpecialMap_isClosedImmersion P
  Stacks.Thickenings.isFirstOrderThickening_toShHom _
    (ker_sq_eq_bot_of_isPullback P.toBase P.specialCartesian hA)

/-- The special-fibre square of a deformation, as a commutative square of ringed spaces. -/
theorem toShHom_comm :
    P.specialMap.toLRSHom.toShHom ≫ P.toBase.toLRSHom.toShHom =
      X.hom.toLRSHom.toShHom ≫ (residueSpecMap P.base).toLRSHom.toShHom :=
  Stacks.Immersion.toShHom_square P.specialCartesian.w

/-- **The conormal map of the special-fibre square of a deformation is invertible**:
`f^* 𝒞_{Spec k/Spec A} ⟶ 𝒞_{X/X'}` is an isomorphism, by flat base change for conormal sheaves
([Stacks Project, Tag 0473]), the structure morphism of a deformation being flat and its
special-fibre square cartesian. This is condition (2) of [Stacks Project, Tag 063Y]. -/
theorem isIso_conormalSheafMap :
    IsIso (Stacks.ClosedImmersion.conormalSheafMap P.toShHom_comm) := by
  have := residueSpecMap_isClosedImmersion P.base
  have := deformationSpecialMap_isClosedImmersion P
  have : Flat P.toBase := P.flat
  have h := Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat P.specialMap
    (residueSpecMap P.base) X.hom P.toBase P.specialCartesian
  rw [Stacks.Immersion.immersionConormalSheafMap] at h
  have h' : IsIso (Stacks.ClosedImmersion.conormalSheafMap P.toShHom_comm ≫
      (Stacks.Immersion.conormalSheafSelfIso P.specialMap).hom) :=
    IsIso.of_isIso_comp_left ((modulePullback X.hom.toLRSHom.toShHom).map
      (Stacks.Immersion.conormalSheafSelfIso (residueSpecMap P.base)).inv) _
  exact IsIso.of_isIso_comp_right _ (Stacks.Immersion.conormalSheafSelfIso P.specialMap).hom

/-- The morphism of first order thickenings underlying a deformation over a base with square-zero
maximal ideal: the special-fibre square. -/
abbrev thickeningSquare (hA : IsLocalRing.maximalIdeal (P.base : Type u) ^ 2 = ⊥) :
    MorphismOfThickenings.{u} :=
  RingedSpaceThickening.thickeningSquare (residueSpecMap_isFirstOrderThickening P.base hA)
    P.specialMap.toLRSHom.toShHom P.toBase.toLRSHom.toShHom
    (P.specialMap_isFirstOrderThickening hA) P.toShHom_comm

/-- **The ideal of the special fibre of a deformation is the pulled-back ideal of the closed
point**: the first-order ideal map `f^* 𝒥 ⟶ ℐ` of [Stacks Project, Tag 08KZ] is invertible. -/
theorem isIso_firstOrderIdealMap (hA : IsLocalRing.maximalIdeal (P.base : Type u) ^ 2 = ⊥) :
    IsIso ((P.thickeningSquare hA).firstOrderIdealMap (P.specialMap_isFirstOrderThickening hA)
      (residueSpecMap_isFirstOrderThickening P.base hA)).1 :=
  have := P.isIso_conormalSheafMap
  MorphismOfThickenings.isIso_firstOrderIdealMap_of_isIso (P.thickeningSquare hA) _ _

/-- The module `f^* 𝒥` on `X` of the deformation problem of a deformation over `A`: the pullback
along the structure morphism of `X` of the ideal of the closed point of `Spec A`. -/
abbrev pulledIdeal (A : ArtinianLocalAlgCat.{u, u, u} Λ k) (X : Over (Spec (CommRingCat.of k))) :
    SheafOfModules.{u} (structureSheafRing X.left.toLocallyRingedSpace.toRingedSpace) :=
  (modulePullback X.hom.toLRSHom.toShHom).obj
    ((modulePullback (residueSpecMap A).toLRSHom.toShHom).obj
      (AlgebraicGeometry.SheafOfModules.idealSheaf (residueSpecMap A).toLRSHom.toShHom))

/-- **A deformation of `X` over a base with square-zero maximal ideal is a solution of the
deformation problem of Stacks 08U7**, for the thickening `Spec k ⊂ Spec A`, the module `f^* 𝒥` and
the identity as prescribed map. The deformed space is the total space of the deformation, the
thickening is its special-fibre immersion, the morphism over `Spec A` is its structure morphism,
and the ideal of the special fibre is identified with `f^* 𝒥` by the first-order ideal map, which
is invertible by flatness (`isIso_firstOrderIdealMap`). -/
def toSolution (hA : IsLocalRing.maximalIdeal (P.base : Type u) ^ 2 = ⊥) :
    DeformationSolution (residueSpecMap P.base).toLRSHom.toShHom
      (residueSpecMap_isFirstOrderThickening P.base hA) X.hom.toLRSHom.toShHom
      (pulledIdeal P.base X) (𝟙 _) :=
  haveI := P.isIso_firstOrderIdealMap hA
  DeformationSolution.ofIsIso _ P.specialMap.toLRSHom.toShHom P.toBase.toLRSHom.toShHom
    (P.specialMap_isFirstOrderThickening hA) P.toShHom_comm

/-! ### Rebasing a deformation along an equality of base objects -/

/-- A deformation whose base object equals `A`, read as a deformation with base object `A` on the
nose: the structure morphism is composed with the transport `Spec P.base = Spec A`. -/
def rebase {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : P.base = A) :
    SchemeDeformationCategory (Λ := Λ) (k := k) X where
  base := A
  scheme := P.scheme
  toBase := P.toBase ≫ eqToHom (congrArg baseSpec h)
  flat := by
    have := P.flat
    exact inferInstance
  specialMap := P.specialMap
  specialCartesian := by
    obtain ⟨B, Y, q, hq, i, hi⟩ := P
    dsimp only at h ⊢
    subst h
    simpa using hi

/-- The base object of `P.rebase h` is `A`. -/
@[simp] theorem rebase_base {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : P.base = A) :
    (P.rebase h).base = A := rfl

/-- The total space of `P.rebase h` is that of `P`. -/
@[simp] theorem rebase_scheme {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : P.base = A) :
    (P.rebase h).scheme = P.scheme := rfl

/-- The closed immersion of `X` into `P.rebase h` is that of `P`. -/
@[simp] theorem rebase_specialMap {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : P.base = A) :
    (P.rebase h).specialMap = P.specialMap := rfl

/-- The structure morphism of `P.rebase h` is that of `P` followed by the transport
`Spec P.base = Spec A`. -/
theorem rebase_toBase {A : ArtinianLocalAlgCat.{u, u, u} Λ k} (h : P.base = A) :
    (P.rebase h).toBase = P.toBase ≫ eqToHom (congrArg baseSpec h) := rfl

end SchemeDeformationCategory

/-- The map of spectra induced by a transport along an equality of objects of `𝒞_Λ` is the
transport along the induced equality of spectra. -/
theorem baseSpecMap_eqToHom {A B : ArtinianLocalAlgCat.{u, u, u} Λ k} (e : A = B) :
    baseSpecMap (eqToHom e) = eqToHom (congrArg baseSpec e.symm) := by
  subst e
  simp

/-! ### The fibre over a base with square-zero maximal ideal -/

section Fibre

variable {X : Over (Spec (CommRingCat.of k))} {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
  (hA : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥)

/-- The solution of the deformation problem of Stacks 08U7 attached to a point of the fibre of the
deformation category of `X` over `A`. -/
def fiberSolution (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A) :
    DeformationSolution (residueSpecMap A).toLRSHom.toShHom
      (residueSpecMap_isFirstOrderThickening A hA) X.hom.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal A X) (𝟙 _) :=
  (x.1.rebase x.2).toSolution hA

/-- The total space of `fiberSolution hA x` is the ringed space underlying `x.1.scheme`. -/
theorem fiberSolution_X' (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A) :
    (fiberSolution hA x).X' = x.1.scheme.toLocallyRingedSpace.toRingedSpace := rfl

/-- The closed immersion of `fiberSolution hA x` is the one underlying `x.1.specialMap`. -/
theorem fiberSolution_i (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A) :
    (fiberSolution hA x).i = x.1.specialMap.toLRSHom.toShHom := rfl

/-- The structure morphism of `fiberSolution hA x` is the one underlying `x.1.toBase` followed by
the transport `Spec x.1.base = Spec A`. -/
theorem fiberSolution_f' (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A) :
    (fiberSolution hA x).f' =
      (x.1.toBase ≫ eqToHom (congrArg baseSpec x.2)).toLRSHom.toShHom := rfl

/-- A morphism of the fibre lies over the transport between the two base objects. -/
theorem fiber_hom_base {x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A}
    (φ : x ⟶ y) : φ.1.base = eqToHom (x.2.trans y.2.symm) := by
  have : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift (𝟙 A) φ.1 := φ.2
  have h := IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
    (𝟙 A) φ.1
  change φ.1.base = _ at h
  rw [h]
  simp

/-- The map of total spaces of a morphism of the fibre commutes with the rebased structure
morphisms. -/
theorem fiber_hom_map_comp_toBase
    {x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A} (φ : x ⟶ y) :
    φ.1.map ≫ x.1.toBase ≫ eqToHom (congrArg baseSpec x.2) =
      y.1.toBase ≫ eqToHom (congrArg baseSpec y.2) := by
  rw [← Category.assoc, φ.1.cartesian.w, fiber_hom_base, baseSpecMap_eqToHom, Category.assoc,
    eqToHom_trans]

/-- **A morphism of the fibre gives an isomorphism of the attached solutions.** -/
theorem isomorphic_fiberSolution_of_hom
    {x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A} (φ : x ⟶ y) :
    Isomorphic (fiberSolution hA y) (fiberSolution hA x) :=
  isomorphic_of_comm φ.1.map.toLRSHom.toShHom
    (Stacks.Immersion.toShHom_square
      ((φ.1.special_compat).trans (Category.comp_id _).symm) |>.trans (Category.comp_id _))
    (congrArg (fun p : y.1.scheme ⟶ baseSpec A => p.toLRSHom.toShHom)
      (fiber_hom_map_comp_toBase φ))

/-- The morphism of schemes underlying an invertible morphism of the underlying ringed spaces. -/
def schemeHomOfIsIso {Y Z : Scheme.{u}}
    (h : Y.toLocallyRingedSpace.toRingedSpace ⟶ Z.toLocallyRingedSpace.toRingedSpace) [IsIso h] :
    Y ⟶ Z :=
  Scheme.Hom.mk (LocallyRingedSpace.homOfSheafedSpaceHomOfIsIso h)

/-- The morphism of ringed spaces underlying `schemeHomOfIsIso h` is `h`. -/
theorem schemeHomOfIsIso_toShHom {Y Z : Scheme.{u}}
    (h : Y.toLocallyRingedSpace.toRingedSpace ⟶ Z.toLocallyRingedSpace.toRingedSpace) [IsIso h] :
    (schemeHomOfIsIso h).toLRSHom.toShHom = h := rfl

/-- Two morphisms of schemes with the same underlying morphism of ringed spaces are equal. -/
theorem scheme_hom_ext_toShHom {Y Z : Scheme.{u}} {a b : Y ⟶ Z}
    (h : a.toLRSHom.toShHom = b.toLRSHom.toShHom) : a = b :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (congrArg InducedCategory.Hom.hom h))

/-- A morphism of the fibre built from an invertible morphism of the total spaces, read as ringed
spaces, under `X` and over `Spec A`. -/
def fiberHomOfShHom {x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A}
    (h : y.1.scheme.toLocallyRingedSpace.toRingedSpace ⟶
      x.1.scheme.toLocallyRingedSpace.toRingedSpace) [IsIso h]
    (th : y.1.specialMap.toLRSHom.toShHom ≫ h = x.1.specialMap.toLRSHom.toShHom)
    (bh : h ≫ (x.1.toBase ≫ eqToHom (congrArg baseSpec x.2)).toLRSHom.toShHom =
      (y.1.toBase ≫ eqToHom (congrArg baseSpec y.2)).toLRSHom.toShHom) : x ⟶ y :=
  haveI : IsIso (schemeHomOfIsIso h) :=
    ⟨schemeHomOfIsIso (inv h), scheme_hom_ext_toShHom (IsIso.hom_inv_id h),
      scheme_hom_ext_toShHom (IsIso.inv_hom_id h)⟩
  have hb : schemeHomOfIsIso h ≫ x.1.toBase =
      y.1.toBase ≫ baseSpecMap (eqToHom (x.2.trans y.2.symm)) := by
    have e : schemeHomOfIsIso h ≫ x.1.toBase ≫ eqToHom (congrArg baseSpec x.2) =
        y.1.toBase ≫ eqToHom (congrArg baseSpec y.2) := scheme_hom_ext_toShHom bh
    rw [baseSpecMap_eqToHom, ← cancel_mono (eqToHom (congrArg baseSpec x.2))]
    simpa using e
  ⟨{ base := eqToHom (x.2.trans y.2.symm)
     map := schemeHomOfIsIso h
     cartesian := by
       rw [baseSpecMap_eqToHom] at hb ⊢
       exact IsPullback.of_horiz_isIso ⟨hb⟩
     special_compat := scheme_hom_ext_toShHom th },
   IsHomLift.of_fac' _ _ _ x.2 y.2 (by
     change eqToHom (x.2.trans y.2.symm) = _
     simp)⟩

/-- **Isomorphic solutions come from isomorphic points of the fibre.** -/
theorem isIsomorphic_of_isomorphic_fiberSolution
    {x y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber A}
    (e : Isomorphic (fiberSolution hA y) (fiberSolution hA x)) : IsIsomorphic x y := by
  obtain ⟨e, he⟩ := e
  let g : y.1.scheme.toLocallyRingedSpace.toRingedSpace ⟶
      x.1.scheme.toLocallyRingedSpace.toRingedSpace := e.hom
  have : IsIso g := he
  have th : y.1.specialMap.toLRSHom.toShHom ≫ g = x.1.specialMap.toLRSHom.toShHom :=
    e.thickening_comm
  have bh : g ≫ (x.1.toBase ≫ eqToHom (congrArg baseSpec x.2)).toLRSHom.toShHom =
      (y.1.toBase ≫ eqToHom (congrArg baseSpec y.2)).toLRSHom.toShHom := e.base_comm
  have th' : x.1.specialMap.toLRSHom.toShHom ≫ inv g = y.1.specialMap.toLRSHom.toShHom := by
    simp [← th]
  have bh' : inv g ≫ (y.1.toBase ≫ eqToHom (congrArg baseSpec y.2)).toLRSHom.toShHom =
      (x.1.toBase ≫ eqToHom (congrArg baseSpec x.2)).toLRSHom.toShHom := by
    simp [← bh]
  refine ⟨⟨fiberHomOfShHom g th bh, fiberHomOfShHom (inv g) th' bh', ?_, ?_⟩⟩ <;>
    refine Functor.Fiber.hom_ext (SchemeDeformationCategory.Hom.ext ?_ (scheme_hom_ext_toShHom ?_))
  · show eqToHom (x.2.trans y.2.symm) ≫ eqToHom (y.2.trans x.2.symm) = 𝟙 _
    simp
  · exact IsIso.inv_hom_id g
  · show eqToHom (y.2.trans x.2.symm) ≫ eqToHom (x.2.trans y.2.symm) = 𝟙 _
    simp
  · exact IsIso.hom_inv_id g

end Fibre

end Deformation.Examples
