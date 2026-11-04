module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistedSections
public import StacksFrontier.AlgebraicGeometry.ModuleTwistIso.GlobalLeft
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistHom
import all StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModule

/-!
# A twist of a twist is semilinear for the graded scalar action

Let `S` be a graded ring, `X = Proj S`, `ℱ` a sheaf of `𝒪_X`-modules and `d` a natural number
whose ratio locus is all of `X`. `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafIterateIso`
is then the isomorphism

`(ℱ(m))(dn) ≅ ℱ(dn + m)`

of [Stacks, Tag 03GJ]: Equation 03GJ with the twist in the right slot of the tensor product
instead of the left one. Its global sections form a bijection
`Γ(X, (ℱ(m))(dn)) ≃+ Γ(X, ℱ(dn + m))` which is semilinear for the graded scalar action of
[Stacks, Tag 03GK] for the scalars whose degree is a multiple of `d`: a homogeneous
`a ∈ S_{ed}` acts on both sides, and the two actions agree once the degrees are identified.

The restriction to scalars of degree divisible by `d` is necessary. A scalar of degree `i`
carries `(ℱ(m))(dn)` to `(ℱ(m))(i + dn)`, and `i + dn` need not be a multiple of `d`, so there
is no iterate isomorphism out of the target at all and the square cannot even be written down.
At `i = ed` the target degree is `d(e + n)`, the iterate isomorphism exists there, and the square
commutes. That is the only case the degree-`d` residue argument of [Stacks, Tag 0B5R] uses: the
scalars it moves sections by are exactly the elements of `S_{ed}`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafIterateSections`: the global sections of the
  iterate isomorphism over `⊤`, as an isomorphism of additive groups
  `Γ(X, (ℱ(m))(dn)) ≃+ Γ(X, ℱ(dn + m))`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso`
  `.twistSheafIterateSections_homogeneousScalarTwistedSections`: the semilinearity. For
  `a ∈ S_{ed}` the iterate bijection carries the graded action of `a` on `Γ(X, (ℱ(m))(dn))` to
  the graded action of `a` on `Γ(X, ℱ(dn + m))`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafScalarMap_comp_twistSheafIterateIso`: the
  same statement one level up, as a commuting square of morphisms of sheaves of modules.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafIterateMap`: the iterate morphism
  `(ℱ(m))(p) ⟶ ℱ(p + m)` for an arbitrary integer `p`, with no hypothesis on the ratio locus —
  the braiding followed by Equation 03GJ. The iterate isomorphism is this morphism at `p = dn`.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafScalarMap_comp_twistSheafIterateMap`: the
  square for `twistSheafIterateMap`, where it is a statement about arbitrary degrees.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafScalarMap_comp_tensorProductBraiding`: the
  naturality of the braiding in the twisted slot, and
  `Stacks.AlgebraicGeometry.ModuleTwistIso`
  `.twistScalarSheafMap_comp_twistSheafMultiplicationMap`: the compatibility of Equation 03GJ
  with multiplication by a homogeneous scalar. These are the two halves the square factors into.
* `Stacks.AlgebraicGeometry.ModuleTwistIso.twistIterateScalarDegree` and
  `Stacks.AlgebraicGeometry.ModuleTwistIso.twistIterateScalarDegree_add`: the degree bookkeeping
  `ed + dn = d(e + n)` and `ed + (dn + m) = d(e + n) + m` the statements transport along.

The square is proved at the level of morphisms of sheaves and only then read on global sections:
a section of `(ℱ(m))(dn)` over `⊤` is a section of a sheafified tensor product and is not a sum
of pure tensors, so neither side can be computed on it directly. What is left after both halves
are reduced to pure tensors is a product of three local sections of twisting sheaves
reassociated, which is `mul_assoc` in the localized fibre at each point.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 03GJ](https://stacks.math.columbia.edu/tag/03GJ)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules
  degreeSection multiplyTwistSections multiplyTwistSections_apply
  pureTensorSection pureTensorSection_hom_ext tensorSheafMap_pureTensorSection
  tensorProductBraiding_pureTensorSection twistSheafMultiplicationMap
  twistSheafMultiplicationMap_pureTensorSection projStructureRing projStructureRingIsSheaf)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap twistSheafScalarMap
  twistedSectionsComponent homogeneousScalarTwistedSections
  cast_homogeneousScalarTwistedSections)
open Stacks.SheafOfModules.Invertible (tensorProductBraiding)
open Stacks.Algebraization (tensorSheafMapPair)
open Stacks.Veronese (bijective_sheafIsoSections multiplyTwistSections_degreeSection
  tensorSheaf_hom_ext_right_toTensorSheafSection)

namespace Stacks.AlgebraicGeometry.ModuleTwistIso

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf ModuleCat.restrictScalars
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The pointwise value of multiplication by a homogeneous scalar on a twisting sheaf: at a point
of `U` the image of a section `c` of `𝒪(n)` under the morphism `𝒪(n) ⟶ 𝒪(k)` induced by a
homogeneous `a` of degree `i` is the product of `c` with the section of `𝒪(i)` that `a` names.

The target degree `k` is arbitrary: a section of a twisting sheaf is a dependent function into
the localized fibres, whose type does not mention the degree, so the value does not depend on
which degree the morphism is stated at. -/
private theorem twistScalarSheafMap_apply_val (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k)
    (a : 𝒮 i) (U : Opens (ProjectiveSpectrum.top 𝒮))
    (c : (twistingSheaf 𝒮 n).val.obj (op U)) (x : U) :
    ((twistScalarSheafMap 𝒮 i n k hk a).val.app (op U) c).1 x =
      ((twistingSheaf 𝒮 (i : ℤ)).val.map (homOfLE le_top).op (degreeSection 𝒮 i a)).1 x *
        c.1 x := by
  cases hk
  exact (congrArg (fun z => z.1 x)
      (multiplyTwistSections_degreeSection 𝒮 i n a U c)).symm.trans
    (multiplyTwistSections_apply 𝒮 (i : ℤ) n U _ c x)

/-- Multiplication by a homogeneous scalar may be performed before or after multiplying two
local sections of twisting sheaves together. Both sides are, at every point, the product of
three fractions, and the identity is the associativity of that product. -/
private theorem multiplyTwistSections_twistScalarSheafMap (i : ℕ) (p m q : ℤ)
    (hq : (i : ℤ) + p = q) (hqm : (i : ℤ) + (p + m) = q + m) (a : 𝒮 i)
    (U : Opens (ProjectiveSpectrum.top 𝒮)) (t : (twistingSheaf 𝒮 p).val.obj (op U))
    (w : (twistingSheaf 𝒮 m).val.obj (op U)) :
    multiplyTwistSections 𝒮 q m U ((twistScalarSheafMap 𝒮 i p q hq a).val.app (op U) t) w =
      (twistScalarSheafMap 𝒮 i (p + m) (q + m) hqm a).val.app (op U)
        (multiplyTwistSections 𝒮 p m U t w) := by
  refine AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSectionsOn_ext 𝒮 fun x => ?_
  refine Eq.trans (multiplyTwistSections_apply 𝒮 q m U
    ((twistScalarSheafMap 𝒮 i p q hq a).val.app (op U) t) w x) ?_
  refine Eq.trans (congrArg (fun z => z * w.1 x)
    (twistScalarSheafMap_apply_val 𝒮 i p q hq a U t x)) ?_
  refine Eq.trans (mul_assoc _ (t.1 x) (w.1 x)) ?_
  refine Eq.trans (congrArg (fun z =>
      ((twistingSheaf 𝒮 (i : ℤ)).val.map (homOfLE le_top).op (degreeSection 𝒮 i a)).1 x * z)
    (multiplyTwistSections_apply 𝒮 p m U t w x).symm) ?_
  exact (twistScalarSheafMap_apply_val 𝒮 i (p + m) (q + m) hqm a U
    (multiplyTwistSections 𝒮 p m U t w) x).symm

variable (F : SheafOfModules.{u}
  ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
    (forget₂ CommRingCat.{u} RingCat.{u})).obj (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-! ### The two halves of the square -/

/-- The braiding is natural in the twisted slot: multiplying `ℱ(p)` by a homogeneous scalar
of degree `i` and then crossing the two factors is crossing them first and multiplying the
twisting sheaf at the end. -/
public theorem twistSheafScalarMap_comp_tensorProductBraiding (i : ℕ) (p q : ℤ)
    (hq : (i : ℤ) + p = q) (a : 𝒮 i) :
    twistSheafScalarMap 𝒮 F i p q hq a ≫
        (tensorProductBraiding (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮) F
          (twistingSheaf 𝒮 q)).hom =
      (tensorProductBraiding (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮) F
          (twistingSheaf 𝒮 p)).hom ≫
        tensorSheafMapPair (AlgebraicGeometry.Proj 𝒮)
          (twistScalarSheafMap 𝒮 i p q hq a) (𝟙 F) := by
  refine pureTensorSection_hom_ext 𝒮 F (twistingSheaf 𝒮 p) _ ?_
  intro U x y
  have h1 := tensorSheafMap_pureTensorSection 𝒮 F (twistingSheaf 𝒮 p) F (twistingSheaf 𝒮 q)
    (𝟙 F) (twistScalarSheafMap 𝒮 i p q hq a) U x y
  have h2 := tensorProductBraiding_pureTensorSection 𝒮 F (twistingSheaf 𝒮 q) U x
    ((twistScalarSheafMap 𝒮 i p q hq a).val.app (op U) y)
  have h3 := tensorProductBraiding_pureTensorSection 𝒮 F (twistingSheaf 𝒮 p) U x y
  have h4 := tensorSheafMap_pureTensorSection 𝒮 (twistingSheaf 𝒮 p) F (twistingSheaf 𝒮 q) F
    (twistScalarSheafMap 𝒮 i p q hq a) (𝟙 F) U y x
  exact ((congrArg (fun z => (tensorProductBraiding (projStructureRing 𝒮)
        (projStructureRingIsSheaf 𝒮) F (twistingSheaf 𝒮 q)).hom.val.app (op U) z) h1).trans
      h2).trans
    (((congrArg (fun z => (tensorSheafMapPair (AlgebraicGeometry.Proj 𝒮)
        (twistScalarSheafMap 𝒮 i p q hq a) (𝟙 F)).val.app (op U) z) h3).trans h4).symm)

/-- Equation 03GJ is compatible with multiplication by a homogeneous scalar: multiplying the
left factor of `𝒪(p) ⊗ ℱ(m)` by a homogeneous `a` of degree `i` and then multiplying out is
multiplying out first and then multiplying `ℱ(p + m)` by `a`.

Both sides are checked on a nested pure tensor, where the content is the associativity of the
product of three local sections of twisting sheaves. -/
public theorem twistScalarSheafMap_comp_twistSheafMultiplicationMap (i : ℕ) (p m q : ℤ)
    (hq : (i : ℤ) + p = q) (hqm : (i : ℤ) + (p + m) = q + m) (a : 𝒮 i) :
    tensorSheafMapPair (AlgebraicGeometry.Proj 𝒮)
          (twistScalarSheafMap 𝒮 i p q hq a) (𝟙 (twistSheafOfModules 𝒮 F m)) ≫
        twistSheafMultiplicationMap 𝒮 F q m =
      twistSheafMultiplicationMap 𝒮 F p m ≫
        twistSheafScalarMap 𝒮 F i (p + m) (q + m) hqm a := by
  refine tensorSheaf_hom_ext_right_toTensorSheafSection (AlgebraicGeometry.Proj 𝒮).toRingedSpace
    (B := F) (C := twistingSheaf 𝒮 m) _ _ ?_
  rintro ⟨U⟩ t b w
  have hfinal := multiplyTwistSections_twistScalarSheafMap 𝒮 i p m q hq hqm a U t w
  have h1 := tensorSheafMap_pureTensorSection 𝒮 (twistingSheaf 𝒮 p)
    (twistSheafOfModules 𝒮 F m) (twistingSheaf 𝒮 q) (twistSheafOfModules 𝒮 F m)
    (twistScalarSheafMap 𝒮 i p q hq a) (𝟙 (twistSheafOfModules 𝒮 F m)) U t
    (pureTensorSection 𝒮 F (twistingSheaf 𝒮 m) U b w)
  have h2 := twistSheafMultiplicationMap_pureTensorSection 𝒮 F q m U
    ((twistScalarSheafMap 𝒮 i p q hq a).val.app (op U) t) b w
  have h3 := twistSheafMultiplicationMap_pureTensorSection 𝒮 F p m U t b w
  have h4 := tensorSheafMap_pureTensorSection 𝒮 F (twistingSheaf 𝒮 (p + m)) F
    (twistingSheaf 𝒮 (q + m)) (𝟙 F) (twistScalarSheafMap 𝒮 i (p + m) (q + m) hqm a) U b
    (multiplyTwistSections 𝒮 p m U t w)
  exact ((congrArg (fun z => (twistSheafMultiplicationMap 𝒮 F q m).val.app (op U) z) h1).trans
      h2).trans
    ((congrArg (pureTensorSection 𝒮 F (twistingSheaf 𝒮 (q + m)) U b) hfinal).trans
      (((congrArg (fun z => (twistSheafScalarMap 𝒮 F i (p + m) (q + m) hqm a).val.app (op U) z)
        h3).trans h4).symm))

/-! ### The iterate morphism and its semilinearity -/

/-- The iterate morphism `(ℱ(m))(p) ⟶ ℱ(p + m)`: cross the two factors of `ℱ(m) ⊗ 𝒪(p)` and
apply Equation 03GJ. No hypothesis on `p` is needed to write it down, and it is an isomorphism
exactly when Equation 03GJ is. -/
public def twistSheafIterateMap (p m : ℤ) :
    twistSheafOfModules 𝒮 (twistSheafOfModules 𝒮 F m) p ⟶ twistSheafOfModules 𝒮 F (p + m) :=
  (tensorProductBraiding (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮)
      (twistSheafOfModules 𝒮 F m) (twistingSheaf 𝒮 p)).hom ≫
    twistSheafMultiplicationMap 𝒮 F p m

/-- The iterate morphism, unfolded into the braiding followed by Equation 03GJ. -/
public theorem twistSheafIterateMap_eq (p m : ℤ) :
    twistSheafIterateMap 𝒮 F p m =
      (tensorProductBraiding (projStructureRing 𝒮) (projStructureRingIsSheaf 𝒮)
          (twistSheafOfModules 𝒮 F m) (twistingSheaf 𝒮 p)).hom ≫
        twistSheafMultiplicationMap 𝒮 F p m :=
  rfl

/-- The iterate morphism intertwines the graded scalar actions: multiplying `(ℱ(m))(p)` by a
homogeneous `a` of degree `i` and then comparing with `ℱ(q + m)` is comparing with `ℱ(p + m)`
first and multiplying by `a` there.

No divisibility hypothesis appears: the degrees `p` and `q` are arbitrary integers subject only
to `i + p = q`. -/
public theorem twistSheafScalarMap_comp_twistSheafIterateMap (i : ℕ) (p m q : ℤ)
    (hq : (i : ℤ) + p = q) (hqm : (i : ℤ) + (p + m) = q + m) (a : 𝒮 i) :
    twistSheafScalarMap 𝒮 (twistSheafOfModules 𝒮 F m) i p q hq a ≫
        twistSheafIterateMap 𝒮 F q m =
      twistSheafIterateMap 𝒮 F p m ≫ twistSheafScalarMap 𝒮 F i (p + m) (q + m) hqm a := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ twistSheafMultiplicationMap 𝒮 F q m)
    (twistSheafScalarMap_comp_tensorProductBraiding 𝒮 (twistSheafOfModules 𝒮 F m) i p q hq a)).trans
    ((Category.assoc _ _ _).trans ?_)
  refine (congrArg (_ ≫ ·)
    (twistScalarSheafMap_comp_twistSheafMultiplicationMap 𝒮 F i p m q hq hqm a)).trans ?_
  exact (Category.assoc _ _ _).symm

/-! ### The degree bookkeeping -/

/-- The degree bookkeeping of the iterate semilinearity: a scalar of degree `ed` acting on
the `dn`-th twist lands in degree `ed + dn`, which the iterate isomorphism at `e + n` reads as
`d(e + n)`. -/
public theorem twistIterateScalarDegree (d e : ℕ) (n : ℤ) :
    ((e * d : ℕ) : ℤ) + (d : ℤ) * n = (d : ℤ) * ((e : ℤ) + n) := by
  push_cast
  ring

/-- The same bookkeeping after the inner twist by `m` has been multiplied out. -/
public theorem twistIterateScalarDegree_add (d e : ℕ) (n m : ℤ) :
    ((e * d : ℕ) : ℤ) + ((d : ℤ) * n + m) = (d : ℤ) * ((e : ℤ) + n) + m := by
  push_cast
  ring

/-- The twist-of-a-twist isomorphism intertwines multiplication by a homogeneous scalar whose
degree is a multiple of `d`, as a commuting square of morphisms of sheaves of modules:

`(ℱ(m))(dn) ⟶ (ℱ(m))(d(e + n)) ⟶ ℱ(d(e + n) + m)` equals
`(ℱ(m))(dn) ⟶ ℱ(dn + m) ⟶ ℱ(d(e + n) + m)`,

the first map of each row being multiplication by `a ∈ S_{ed}`. -/
public theorem twistSheafScalarMap_comp_twistSheafIterateIso {d : ℕ}
    (hd : ProjShared.ratioLocus 𝒮 d = ⊤) (n m : ℤ) (e : ℕ) (a : 𝒮 (e * d)) :
    twistSheafScalarMap 𝒮 (twistSheafOfModules 𝒮 F m) (e * d) ((d : ℤ) * n)
          ((d : ℤ) * ((e : ℤ) + n)) (twistIterateScalarDegree d e n) a ≫
        (twistSheafIterateIso 𝒮 hd F ((e : ℤ) + n) m).hom =
      (twistSheafIterateIso 𝒮 hd F n m).hom ≫
        twistSheafScalarMap 𝒮 F (e * d) ((d : ℤ) * n + m) ((d : ℤ) * ((e : ℤ) + n) + m)
          (twistIterateScalarDegree_add d e n m) a :=
  twistSheafScalarMap_comp_twistSheafIterateMap 𝒮 F (e * d) ((d : ℤ) * n) m
    ((d : ℤ) * ((e : ℤ) + n)) (twistIterateScalarDegree d e n)
    (twistIterateScalarDegree_add d e n m) a

/-! ### On global sections -/

/-- A twist of a twist on global sections, `Γ(X, (ℱ(m))(dn)) ≃+ Γ(X, ℱ(dn + m))`: the sections
over `⊤` of `Stacks.AlgebraicGeometry.ModuleTwistIso.twistSheafIterateIso`. It is bijective
because an isomorphism of sheaves of modules is bijective on the sections over any
open, and additive because it is a component of a morphism of sheaves of modules. -/
public def twistSheafIterateSections {d : ℕ} (hd : ProjShared.ratioLocus 𝒮 d = ⊤) (n m : ℤ) :
    twistedSectionsComponent 𝒮 (twistSheafOfModules 𝒮 F m) ((d : ℤ) * n) ≃+
      twistedSectionsComponent 𝒮 F ((d : ℤ) * n + m) :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk'
      (fun s => ((twistSheafIterateIso 𝒮 hd F n m).hom.val.app (op ⊤)).hom s)
      (map_add ((twistSheafIterateIso 𝒮 hd F n m).hom.val.app (op ⊤)).hom))
    (bijective_sheafIsoSections (twistSheafIterateIso 𝒮 hd F n m) (op ⊤))

/-- The twist-of-a-twist bijection on global sections is applied by applying the sections over
`⊤` of the iterate isomorphism. -/
@[simp]
public theorem twistSheafIterateSections_apply {d : ℕ} (hd : ProjShared.ratioLocus 𝒮 d = ⊤)
    (n m : ℤ) (s : twistedSectionsComponent 𝒮 (twistSheafOfModules 𝒮 F m) ((d : ℤ) * n)) :
    twistSheafIterateSections 𝒮 F hd n m s =
      ((twistSheafIterateIso 𝒮 hd F n m).hom.val.app (op ⊤)).hom s :=
  rfl

/-- The twist-of-a-twist bijection on global sections is semilinear for the graded scalar action
of [Stacks, Tag 03GK], for the scalars of degree a multiple of `d`.

Let `a ∈ S_{ed}` and let `s` be a global section of `(ℱ(m))(dn)`. Acting by `a` carries `s` into
`Γ(X, (ℱ(m))(d(e + n)))`, where the iterate bijection at `e + n` is defined; the result is the
section of `Γ(X, ℱ(d(e + n) + m))` obtained by first comparing `s` with `ℱ(dn + m)` and then
acting by `a` there, once the degrees `ed + (dn + m)` and `d(e + n) + m` are identified.

So the iterate isomorphism is an isomorphism of graded modules from `⨁_n Γ(X, (ℱ(m))(dn))` onto
`⨁_n Γ(X, ℱ(dn + m))` over the subring generated by the homogeneous elements of degree divisible
by `d`. -/
public theorem twistSheafIterateSections_homogeneousScalarTwistedSections {d : ℕ}
    (hd : ProjShared.ratioLocus 𝒮 d = ⊤) (n m : ℤ) (e : ℕ) (a : 𝒮 (e * d))
    (s : twistedSectionsComponent 𝒮 (twistSheafOfModules 𝒮 F m) ((d : ℤ) * n)) :
    twistSheafIterateSections 𝒮 F hd ((e : ℤ) + n) m
        (cast (congrArg (twistedSectionsComponent 𝒮 (twistSheafOfModules 𝒮 F m))
            (twistIterateScalarDegree d e n))
          (homogeneousScalarTwistedSections 𝒮 (twistSheafOfModules 𝒮 F m) (e * d)
            ((d : ℤ) * n) a s)) =
      cast (congrArg (twistedSectionsComponent 𝒮 F) (twistIterateScalarDegree_add d e n m))
        (homogeneousScalarTwistedSections 𝒮 F (e * d) ((d : ℤ) * n + m) a
          (twistSheafIterateSections 𝒮 F hd n m s)) := by
  rw [cast_homogeneousScalarTwistedSections 𝒮 (twistSheafOfModules 𝒮 F m) (e * d) ((d : ℤ) * n)
      ((d : ℤ) * ((e : ℤ) + n)) (twistIterateScalarDegree d e n) a s,
    cast_homogeneousScalarTwistedSections 𝒮 F (e * d) ((d : ℤ) * n + m)
      ((d : ℤ) * ((e : ℤ) + n) + m) (twistIterateScalarDegree_add d e n m) a
      (twistSheafIterateSections 𝒮 F hd n m s)]
  exact congrArg
    (fun φ : twistSheafOfModules 𝒮 (twistSheafOfModules 𝒮 F m) ((d : ℤ) * n) ⟶
        twistSheafOfModules 𝒮 F ((d : ℤ) * ((e : ℤ) + n) + m) => (φ.val.app (op ⊤)).hom s)
    (twistSheafScalarMap_comp_twistSheafIterateIso 𝒮 F hd n m e a)

end Stacks.AlgebraicGeometry.ModuleTwistIso

end
