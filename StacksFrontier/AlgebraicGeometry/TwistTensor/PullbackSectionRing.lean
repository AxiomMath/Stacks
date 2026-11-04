module

public import Mathlib.Algebra.DirectSum.Ring
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonBraided
public import StacksFrontier.AlgebraicGeometry.TwistTensor.PullbackMultiplication

/-!
# The graded section ring of the pulled-back twists of `Proj S`

Let `S` be a graded ring, `f : X ⟶ Proj S` a morphism of ringed spaces and `d` a natural number.
The pulled-back twists `f^*𝒪(nd)`, for `n ≥ 0`, carry the multiplication maps

`f^*𝒪(nd) ⊗ f^*𝒪(md) ⟶ f^*𝒪((n + m)d)`

of `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMul` — the inverse of the comparison of
Stacks Tag 01CD followed by the pullback of the canonical multiplication map of Stacks Tag 01MO.
This file proves those maps associative, commutative and unital at module level, and deduces that
for every open `V ⊆ X` the sections

`⨁_{n ≥ 0} Γ(V, f^*𝒪(nd))`

form a graded commutative ring, the product of two sections being the image of their pure tensor
under the multiplication map and the unit the image of the section `1` under
`Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistUnit`.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistTensor.veroneseTwist` — the degree `n` piece `f^*𝒪(nd)`, and
  `veroneseTwistEq` the transport along an equality of Veronese degrees.
* `Stacks.AlgebraicGeometry.TwistTensor.veroneseMulHom` and `veroneseOneHom` — the multiplication
  and the unit of that family, as morphisms of sheaves of modules out of `⊗` and out of `𝟙_`.
* `Stacks.AlgebraicGeometry.TwistTensor.veroneseSections`, `veroneseSectionMul`,
  `veroneseSectionOne` and `veroneseSectionCast` — the sections of the degree `n` piece over an
  open `V`, their product, the unit section, and the transport of a section along an equality of
  degrees.
* `Stacks.AlgebraicGeometry.TwistTensor.veroneseSectionGradedRing` — the graded commutative ring
  structure on `n ↦ Γ(V, f^*𝒪(nd))`.
* `Stacks.AlgebraicGeometry.TwistTensor.veroneseSectionRing` and `veroneseSectionRingGrading` —
  the ring `⨁_n Γ(V, f^*𝒪(nd))` and its homogeneous components.

## Main results

* `Stacks.AlgebraicGeometry.TwistTensor.pullbackTwistMulRS_comm` and `pullbackTwistMul_comm` —
  commutativity of the pulled-back twist multiplication, in arbitrary integer degrees: it is the
  symmetry constraint of Stacks Tag 01CA followed by the multiplication the other way round.
* `Stacks.AlgebraicGeometry.TwistTensor.veroneseMulHom_assoc`, `veroneseOneHom_mulHom`,
  `veroneseMulHom_oneHom` and `veroneseMulHom_comm` — the four laws at the Veronese indexing, with
  the transports along `n + m + k = n + (m + k)`, `m = 0 + m`, `n = n + 0` and `n + m = m + n`.
* `Stacks.AlgebraicGeometry.TwistTensor.veroneseSectionMul_assoc`, `veroneseSectionOne_mul`,
  `veroneseSectionMul_one` and `veroneseSectionMul_comm` — the same four laws on sections, and
  `veroneseSectionMul_add`, `veroneseSectionAdd_mul`, `veroneseSectionMul_zero`,
  `veroneseSectionZero_mul` — biadditivity.
* `Stacks.AlgebraicGeometry.TwistTensor.veroneseSectionMul_pullbackUnit` and
  `veroneseSectionOne_pullbackUnit` — the product and the unit on pullback-unit images: the
  product of the pullback-unit images of two local sections of `𝒪(nd)` and `𝒪(md)` is the
  pullback-unit image of their product `Stacks.AlgebraicGeometry.TwistTensor.mulSection`, and the
  unit section is the pullback-unit image of the unit of the twists.

## Implementation notes

The sections of a pullback are not exhausted by the pullback-unit images, so an identity between
two operations on *arbitrary* sections of `f^*𝒪(nd)` cannot be checked on those images. Each of the
four laws is therefore an equality of morphisms of sheaves of modules, proved from the
corresponding law of `pullbackTwistMul`, and only then evaluated on a pure tensor of sections with
the section formulas `Stacks.PullbackTensorCoherence.whiskerRight_tmul`, `whiskerLeft_tmul`,
`associator_hom_tmul`, `leftUnitor_hom_tmul`, `rightUnitor_hom_tmul` and `braiding_tmul`.

The twists are typed over `projStructureRing` while the comparison of Stacks Tag 01CD is typed over
`Stacks.RingedSpace.structureRingSheaf`; the two are equal by `rfl` but a term mixing them is
type-correct only at default transparency, so `rw` and the simplifier refuse such a goal. Every
crossing below therefore happens inside a proof given by `:=` or `exact`.

`F.map (eqToHom h)` is not `eqToHom (congrArg F.obj h)` on the nose: the step between them is
`CategoryTheory.eqToHom_map`, a theorem and not a definitional unfolding.

The graded-monoid laws are stated twice: with `veroneseSectionCast`, the transport written as
`eqToHom` applied to a section, which is the form the module-level laws produce; and with `cast`
along `congrArg veroneseSections`, the form `GradedMonoid` asks for. `veroneseSectionCast_eq_cast`
identifies the two.

`veroneseSectionGradedRing` is a `def`, not an instance, so that it does not interfere with
instance search on every section group of a sheaf of modules.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO) — the twists of the
  structure sheaf on `Proj S` and the canonical maps between them.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules, with its associator, unitors and symmetry constraint.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) — the graded ring of
  sections attached to an invertible sheaf.
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5) — the degree `d` open.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction PresheafOfModules
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.PullbackTensorCoherence
open Stacks.RingedSpace
open scoped DirectSum

namespace Stacks.AlgebraicGeometry.TwistTensor

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance_reducible] ProjectiveSpectrum.top

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
  Stacks.PullbackTensorCoherence.braidedCategory

variable {X : RingedSpace.{u, u}} (f : X ⟶ (AlgebraicGeometry.Proj 𝒮).toRingedSpace) (d : ℕ)

/-! ### Commutativity of the pulled-back multiplication -/

/-- Commutativity of the canonical twist multiplication on `Proj S`, at the ringed-space spelling
of the structure sheaf of rings. -/
theorem twistMulRS_comm (a b : ℤ) :
    twistMulRS 𝒮 a b = (β_ (twistRS 𝒮 a) (twistRS 𝒮 b)).hom ≫ twistMulRS 𝒮 b a ≫
      eqToHom (congrArg (twistRS 𝒮) (add_comm b a)) :=
  twistMul_comm 𝒮 a b

/-- The pulled-back multiplication unfolded: the inverse of the comparison of Stacks Tag 01CD
followed by the pullback of the canonical multiplication map. -/
private theorem pullbackTwistMulRS_eq_inv_comp (a b : ℤ) :
    pullbackTwistMulRS 𝒮 f a b =
      inv (pullbackTensorComparison f (twistRS 𝒮 a) (twistRS 𝒮 b)) ≫
        (pullbackFunctor f).map (twistMulRS 𝒮 a b) := rfl

/-- The comparison of Stacks Tag 01CD commutes with the symmetry constraint, with both comparisons
inverted and the pullback of the symmetry constraint on the left. -/
private theorem inv_comp_map_braiding (a b : ℤ) :
    inv (pullbackTensorComparison f (twistRS 𝒮 a) (twistRS 𝒮 b)) ≫
        (pullbackFunctor f).map (β_ (twistRS 𝒮 a) (twistRS 𝒮 b)).hom =
      (β_ (pullbackTwistRS 𝒮 f a) (pullbackTwistRS 𝒮 f b)).hom ≫
        inv (pullbackTensorComparison f (twistRS 𝒮 b) (twistRS 𝒮 a)) := by
  rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq]
  exact pullbackTensorComparison_braiding f (twistRS 𝒮 a) (twistRS 𝒮 b)

/-- Commutativity of the pulled-back twist multiplication: multiplying `f^*𝒪(a) ⊗ f^*𝒪(b)` down
to `f^*𝒪(a + b)` is the symmetry constraint of Stacks Tag 01CA followed by multiplying the other
way round, followed by the pullback of the transport along `b + a = a + b`. -/
theorem pullbackTwistMulRS_comm (a b : ℤ) :
    pullbackTwistMulRS 𝒮 f a b =
      (β_ (pullbackTwistRS 𝒮 f a) (pullbackTwistRS 𝒮 f b)).hom ≫
        pullbackTwistMulRS 𝒮 f b a ≫
          (pullbackFunctor f).map (eqToHom (congrArg (twistRS 𝒮) (add_comm b a))) := by
  rw [pullbackTwistMulRS_eq_inv_comp 𝒮 f a b, twistMulRS_comm 𝒮 a b,
    (pullbackFunctor f).map_comp, (pullbackFunctor f).map_comp, ← Category.assoc,
    inv_comp_map_braiding 𝒮 f a b, pullbackTwistMulRS_eq_inv_comp 𝒮 f b a,
    Category.assoc, Category.assoc]

/-- Commutativity of the pulled-back twist multiplication, with the twists at their own spelling
and the transport read on the pullback rather than pulled back. -/
theorem pullbackTwistMul_comm (a b : ℤ) :
    pullbackTwistMul 𝒮 f a b =
      (β_ (pullbackTwist 𝒮 f a) (pullbackTwist 𝒮 f b)).hom ≫ pullbackTwistMul 𝒮 f b a ≫
        eqToHom (congrArg (pullbackTwist 𝒮 f) (add_comm b a)) :=
  (pullbackTwistMulRS_comm 𝒮 f a b).trans
    (congrArg
      (fun φ => (β_ (pullbackTwistRS 𝒮 f a) (pullbackTwistRS 𝒮 f b)).hom ≫
        pullbackTwistMulRS 𝒮 f b a ≫ φ)
      (eqToHom_map (pullbackFunctor f) (congrArg (twistRS 𝒮) (add_comm b a))))

/-! ### The Veronese family of pulled-back twists -/

/-- The degree `n` piece of the `d`-th Veronese family: the pullback along `f` of the twist
`𝒪(nd)`. -/
abbrev veroneseTwist (n : ℕ) : SheafOfModules.{u} (structureRingSheaf X) :=
  pullbackTwist 𝒮 f ((n * d : ℕ) : ℤ)

/-- The transport of the Veronese family along an equality of Veronese degrees. -/
abbrev veroneseTwistEq {n m : ℕ} (h : n = m) :
    veroneseTwist 𝒮 f d n ⟶ veroneseTwist 𝒮 f d m :=
  eqToHom (congrArg (veroneseTwist 𝒮 f d) h)

/-- The multiplication of the Veronese family,
`f^*𝒪(nd) ⊗ f^*𝒪(md) ⟶ f^*𝒪((n + m)d)`: the pulled-back twist multiplication followed by the
transport along `nd + md = (n + m)d`. -/
def veroneseMulHom (n m : ℕ) :
    veroneseTwist 𝒮 f d n ⊗ veroneseTwist 𝒮 f d m ⟶ veroneseTwist 𝒮 f d (n + m) :=
  pullbackTwistMul 𝒮 f ((n * d : ℕ) : ℤ) ((m * d : ℕ) : ℤ) ≫
    eqToHom (congrArg (pullbackTwist 𝒮 f)
      (show ((n * d : ℕ) : ℤ) + ((m * d : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
        push_cast; ring))

/-- The unit of the Veronese family, `𝒪_X ⟶ f^*𝒪(0)`: the unit of the pulled-back twist
multiplication followed by the transport along `0 = 0 · d`. -/
def veroneseOneHom :
    𝟙_ (SheafOfModules.{u} (structureRingSheaf X)) ⟶ veroneseTwist 𝒮 f d 0 :=
  pullbackTwistUnit 𝒮 f ≫
    eqToHom (congrArg (pullbackTwistRS 𝒮 f)
      (show (0 : ℤ) = ((0 * d : ℕ) : ℤ) from by push_cast; ring))

/-- Associativity of the multiplication of the Veronese family, as an equality of morphisms out
of `(f^*𝒪(nd) ⊗ f^*𝒪(md)) ⊗ f^*𝒪(kd)`, up to the transport along `n + (m + k) = n + m + k`. -/
theorem veroneseMulHom_assoc (n m k : ℕ) :
    veroneseMulHom 𝒮 f d n m ▷ veroneseTwist 𝒮 f d k ≫ veroneseMulHom 𝒮 f d (n + m) k =
      (α_ (veroneseTwist 𝒮 f d n) (veroneseTwist 𝒮 f d m) (veroneseTwist 𝒮 f d k)).hom ≫
        veroneseTwist 𝒮 f d n ◁ veroneseMulHom 𝒮 f d m k ≫
          (veroneseMulHom 𝒮 f d n (m + k) ≫
            veroneseTwistEq 𝒮 f d (add_assoc n m k).symm) := by
  rw [veroneseMulHom, veroneseMulHom, veroneseMulHom, veroneseMulHom, Category.assoc,
    eqToHom_trans]
  exact pullbackTwistMul_assoc_transport 𝒮 f
    (show ((n * d : ℕ) : ℤ) + ((m * d : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
      push_cast; ring)
    (show ((m * d : ℕ) : ℤ) + ((k * d : ℕ) : ℤ) = (((m + k) * d : ℕ) : ℤ) from by
      push_cast; ring)
    (show (((n + m) * d : ℕ) : ℤ) + ((k * d : ℕ) : ℤ) = (((n + m + k) * d : ℕ) : ℤ) from by
      push_cast; ring)
    (show ((n * d : ℕ) : ℤ) + (((m + k) * d : ℕ) : ℤ) = (((n + m + k) * d : ℕ) : ℤ) from by
      push_cast; ring)

/-- The left unit law of the multiplication of the Veronese family: the unit whiskered into
`f^*𝒪(md)` and multiplied is the left unitor of Stacks Tag 01CA followed by the transport along
`m = 0 + m`. -/
theorem veroneseOneHom_mulHom (m : ℕ) :
    veroneseOneHom 𝒮 f d ▷ veroneseTwist 𝒮 f d m ≫ veroneseMulHom 𝒮 f d 0 m =
      (λ_ (veroneseTwist 𝒮 f d m)).hom ≫ veroneseTwistEq 𝒮 f d (zero_add m).symm :=
  pullbackTwistMul_one_left_transport 𝒮 f
    (show (0 : ℤ) = ((0 * d : ℕ) : ℤ) from by push_cast; ring)
    (show ((0 * d : ℕ) : ℤ) + ((m * d : ℕ) : ℤ) = (((0 + m) * d : ℕ) : ℤ) from by push_cast; ring)
    (show ((m * d : ℕ) : ℤ) = (((0 + m) * d : ℕ) : ℤ) from by push_cast; ring)

/-- The right unit law of the multiplication of the Veronese family: the unit whiskered into
`f^*𝒪(nd)` on the left and multiplied is the right unitor of Stacks Tag 01CA followed by the
transport along `n = n + 0`. -/
theorem veroneseMulHom_oneHom (n : ℕ) :
    veroneseTwist 𝒮 f d n ◁ veroneseOneHom 𝒮 f d ≫ veroneseMulHom 𝒮 f d n 0 =
      (ρ_ (veroneseTwist 𝒮 f d n)).hom ≫ veroneseTwistEq 𝒮 f d (add_zero n).symm :=
  pullbackTwistMul_one_right_transport 𝒮 f
    (show (0 : ℤ) = ((0 * d : ℕ) : ℤ) from by push_cast; ring)
    (show ((n * d : ℕ) : ℤ) + ((0 * d : ℕ) : ℤ) = (((n + 0) * d : ℕ) : ℤ) from by push_cast; ring)
    (show ((n * d : ℕ) : ℤ) = (((n + 0) * d : ℕ) : ℤ) from by push_cast; ring)

/-- Commutativity of the multiplication of the Veronese family: it is the symmetry constraint
of Stacks Tag 01CA followed by the multiplication the other way round and the transport along
`m + n = n + m`. -/
theorem veroneseMulHom_comm (n m : ℕ) :
    veroneseMulHom 𝒮 f d n m =
      (β_ (veroneseTwist 𝒮 f d n) (veroneseTwist 𝒮 f d m)).hom ≫
        veroneseMulHom 𝒮 f d m n ≫ veroneseTwistEq 𝒮 f d (add_comm m n) := by
  rw [veroneseMulHom, veroneseMulHom, pullbackTwistMul_comm 𝒮 f ((n * d : ℕ) : ℤ)
    ((m * d : ℕ) : ℤ)]
  simp only [Category.assoc, eqToHom_trans]

/-! ### Sections of the Veronese family -/

variable (V : (Opens X.carrier)ᵒᵖ)

/-- The sections of the degree `n` piece of the Veronese family over `V`: `Γ(V, f^*𝒪(nd))`. -/
abbrev veroneseSections (n : ℕ) : Type u := (veroneseTwist 𝒮 f d n).val.obj V

/-- The product of two sections of the degree `n` and degree `m` pieces: the image of their
pure tensor under the multiplication of the Veronese family. -/
def veroneseSectionMul (n m : ℕ) (s : veroneseSections 𝒮 f d V n)
    (t : veroneseSections 𝒮 f d V m) : veroneseSections 𝒮 f d V (n + m) :=
  (veroneseMulHom 𝒮 f d n m).val.app V
    (tmul X (veroneseTwist 𝒮 f d n) (veroneseTwist 𝒮 f d m) V s t)

/-- The unit section, in degree zero: the image of the section `1` of `𝒪_X` under the unit of
the Veronese family. -/
def veroneseSectionOne : veroneseSections 𝒮 f d V 0 :=
  (veroneseOneHom 𝒮 f d).val.app V (oneSec X V)

/-- The transport of a section along an equality of Veronese degrees. -/
def veroneseSectionCast {n m : ℕ} (h : n = m) (s : veroneseSections 𝒮 f d V n) :
    veroneseSections 𝒮 f d V m :=
  (veroneseTwistEq 𝒮 f d h).val.app V s

/-- A transport along an equality of a degree with itself is the identity. -/
theorem veroneseSectionCast_self {n : ℕ} (s : veroneseSections 𝒮 f d V n) :
    veroneseSectionCast 𝒮 f d V (rfl : n = n) s = s := rfl

/-- Two successive transports are the transport along the composite equality. -/
theorem veroneseSectionCast_trans {n m k : ℕ} (h : n = m) (h' : m = k)
    (s : veroneseSections 𝒮 f d V n) :
    veroneseSectionCast 𝒮 f d V h' (veroneseSectionCast 𝒮 f d V h s) =
      veroneseSectionCast 𝒮 f d V (h.trans h') s := by
  subst h; rfl

/-- The transport of a section agrees with the transport of its type along the same equality. -/
theorem veroneseSectionCast_eq_cast {n m : ℕ} (h : n = m) (s : veroneseSections 𝒮 f d V n) :
    veroneseSectionCast 𝒮 f d V h s =
      cast (congrArg (veroneseSections 𝒮 f d V) h) s := by
  subst h; rfl

/-! ### Biadditivity -/

/-- A pure tensor of local sections is additive in its first factor. -/
private theorem tmul_add_left {A B : SheafOfModules.{u} (structureRingSheaf X)}
    (a a' : A.val.obj V) (b : B.val.obj V) :
    tmul X A B V (a + a') b = tmul X A B V a b + tmul X A B V a' b := by
  rw [tmul, tmul, tmul, TensorProduct.add_tmul]
  exact map_add _ _ _

/-- A pure tensor of local sections is additive in its second factor. -/
private theorem tmul_add_right {A B : SheafOfModules.{u} (structureRingSheaf X)}
    (a : A.val.obj V) (b b' : B.val.obj V) :
    tmul X A B V a (b + b') = tmul X A B V a b + tmul X A B V a b' := by
  rw [tmul, tmul, tmul, TensorProduct.tmul_add]
  exact map_add _ _ _

/-- A pure tensor with zero first factor vanishes. -/
private theorem tmul_zero_left {A B : SheafOfModules.{u} (structureRingSheaf X)}
    (b : B.val.obj V) : tmul X A B V 0 b = 0 := by
  rw [tmul, TensorProduct.zero_tmul]
  exact map_zero _

/-- A pure tensor with zero second factor vanishes. -/
private theorem tmul_zero_right {A B : SheafOfModules.{u} (structureRingSheaf X)}
    (a : A.val.obj V) : tmul X A B V a (0 : B.val.obj V) = 0 := by
  rw [tmul, TensorProduct.tmul_zero]
  exact map_zero _

/-- The product of sections vanishes when its second factor does. -/
theorem veroneseSectionMul_zero (n m : ℕ) (s : veroneseSections 𝒮 f d V n) :
    veroneseSectionMul 𝒮 f d V n m s 0 = 0 := by
  rw [veroneseSectionMul, tmul_zero_right]
  exact map_zero _

/-- The product of sections vanishes when its first factor does. -/
theorem veroneseSectionZero_mul (n m : ℕ) (t : veroneseSections 𝒮 f d V m) :
    veroneseSectionMul 𝒮 f d V n m 0 t = 0 := by
  rw [veroneseSectionMul, tmul_zero_left]
  exact map_zero _

/-- The product of sections is additive in its second factor. -/
theorem veroneseSectionMul_add (n m : ℕ) (s : veroneseSections 𝒮 f d V n)
    (t t' : veroneseSections 𝒮 f d V m) :
    veroneseSectionMul 𝒮 f d V n m s (t + t') =
      veroneseSectionMul 𝒮 f d V n m s t + veroneseSectionMul 𝒮 f d V n m s t' := by
  rw [veroneseSectionMul, veroneseSectionMul, veroneseSectionMul, tmul_add_right]
  exact map_add _ _ _

/-- The product of sections is additive in its first factor. -/
theorem veroneseSectionAdd_mul (n m : ℕ) (s s' : veroneseSections 𝒮 f d V n)
    (t : veroneseSections 𝒮 f d V m) :
    veroneseSectionMul 𝒮 f d V n m (s + s') t =
      veroneseSectionMul 𝒮 f d V n m s t + veroneseSectionMul 𝒮 f d V n m s' t := by
  rw [veroneseSectionMul, veroneseSectionMul, veroneseSectionMul, tmul_add_left]
  exact map_add _ _ _

/-! ### The graded-monoid laws on sections -/

/-- An equality of morphisms out of a tensor product, evaluated on a pure tensor of sections. -/
private theorem val_app_tmul_congr {A B C : SheafOfModules.{u} (structureRingSheaf X)}
    {φ ψ : A ⊗ B ⟶ C} (h : φ = ψ) (a : A.val.obj V) (b : B.val.obj V) :
    φ.val.app V (tmul X A B V a b) = ψ.val.app V (tmul X A B V a b) := by
  rw [h]

/-- The unit section is a left unit for the product of sections, modulo the transport along
`m = 0 + m`. -/
theorem veroneseSectionOne_mul (m : ℕ) (s : veroneseSections 𝒮 f d V m) :
    veroneseSectionMul 𝒮 f d V 0 m (veroneseSectionOne 𝒮 f d V) s =
      veroneseSectionCast 𝒮 f d V (zero_add m).symm s := by
  have h := val_app_tmul_congr V (veroneseOneHom_mulHom 𝒮 f d m) (oneSec X V) s
  refine Eq.trans ?_ (Eq.trans h ?_)
  · exact (congrArg ((veroneseMulHom 𝒮 f d 0 m).val.app V)
      (whiskerRight_tmul (veroneseOneHom 𝒮 f d) V (oneSec X V) s)).symm
  · refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _) ?_
    exact congrArg ((veroneseTwistEq 𝒮 f d (zero_add m).symm).val.app V)
      ((leftUnitor_hom_tmul V (oneSec X V) s).trans (one_smul _ _))

/-- The unit section is a right unit for the product of sections, modulo the transport along
`n = n + 0`. -/
theorem veroneseSectionMul_one (n : ℕ) (s : veroneseSections 𝒮 f d V n) :
    veroneseSectionMul 𝒮 f d V n 0 s (veroneseSectionOne 𝒮 f d V) =
      veroneseSectionCast 𝒮 f d V (add_zero n).symm s := by
  have h := val_app_tmul_congr V (veroneseMulHom_oneHom 𝒮 f d n) s (oneSec X V)
  refine Eq.trans ?_ (Eq.trans h ?_)
  · exact (congrArg ((veroneseMulHom 𝒮 f d n 0).val.app V)
      (whiskerLeft_tmul (veroneseOneHom 𝒮 f d) V s (oneSec X V))).symm
  · refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _) ?_
    exact congrArg ((veroneseTwistEq 𝒮 f d (add_zero n).symm).val.app V)
      ((rightUnitor_hom_tmul V s (oneSec X V)).trans (one_smul _ _))

/-- The product of sections is commutative, modulo the transport along `m + n = n + m`. -/
theorem veroneseSectionMul_comm (n m : ℕ) (s : veroneseSections 𝒮 f d V n)
    (t : veroneseSections 𝒮 f d V m) :
    veroneseSectionMul 𝒮 f d V n m s t =
      veroneseSectionCast 𝒮 f d V (add_comm m n) (veroneseSectionMul 𝒮 f d V m n t s) := by
  have h := val_app_tmul_congr V (veroneseMulHom_comm 𝒮 f d n m) s t
  refine h.trans ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _) ?_
  exact congrArg
    (fun z => (veroneseTwistEq 𝒮 f d (add_comm m n)).val.app V
      ((veroneseMulHom 𝒮 f d m n).val.app V z))
    (braiding_tmul X (veroneseTwist 𝒮 f d n) (veroneseTwist 𝒮 f d m) V s t)

/-- The product of sections is associative, modulo the transport along
`i + j + k = i + (j + k)`. -/
theorem veroneseSectionMul_assoc (i j k : ℕ) (a : veroneseSections 𝒮 f d V i)
    (b : veroneseSections 𝒮 f d V j) (c : veroneseSections 𝒮 f d V k) :
    veroneseSectionMul 𝒮 f d V (i + j) k (veroneseSectionMul 𝒮 f d V i j a b) c =
      veroneseSectionCast 𝒮 f d V (add_assoc i j k).symm
        (veroneseSectionMul 𝒮 f d V i (j + k) a (veroneseSectionMul 𝒮 f d V j k b c)) := by
  have h := val_app_tmul_congr V (veroneseMulHom_assoc 𝒮 f d i j k)
    (tmul X (veroneseTwist 𝒮 f d i) (veroneseTwist 𝒮 f d j) V a b) c
  refine Eq.trans ?_ (Eq.trans h ?_)
  · refine Eq.trans ?_ (SheafOfModules.comp_val_app_apply _ _ _ _).symm
    exact (congrArg ((veroneseMulHom 𝒮 f d (i + j) k).val.app V)
      (whiskerRight_tmul (veroneseMulHom 𝒮 f d i j) V _ c)).symm
  · refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _) ?_
    refine Eq.trans (congrArg
      ((veroneseTwist 𝒮 f d i ◁ veroneseMulHom 𝒮 f d j k ≫
        veroneseMulHom 𝒮 f d i (j + k) ≫
          veroneseTwistEq 𝒮 f d (add_assoc i j k).symm).val.app V)
      (associator_hom_tmul V a b c)) ?_
    refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _) ?_
    refine Eq.trans (congrArg ((veroneseMulHom 𝒮 f d i (j + k) ≫
        veroneseTwistEq 𝒮 f d (add_assoc i j k).symm).val.app V)
      (whiskerLeft_tmul (veroneseMulHom 𝒮 f d j k) V a _)) ?_
    exact SheafOfModules.comp_val_app_apply _ _ _ _

/-! ### The graded commutative ring of sections -/

/-- A law proved with `veroneseSectionCast` gives the same law with `cast` of the section type. -/
private theorem cast_eq_of_eq_veroneseSectionCast {n m : ℕ} (h : n = m)
    (x : veroneseSections 𝒮 f d V n) (y : veroneseSections 𝒮 f d V m)
    (hxy : x = veroneseSectionCast 𝒮 f d V h.symm y) :
    cast (congrArg (veroneseSections 𝒮 f d V) h) x = y := by
  rw [← veroneseSectionCast_eq_cast 𝒮 f d V h, hxy, veroneseSectionCast_trans,
    veroneseSectionCast_self]

/-- The left unit law, with the transport written as a `cast` of the section type. -/
theorem veroneseSectionCast_one_mul (j : ℕ) (s : veroneseSections 𝒮 f d V j) :
    cast (congrArg (veroneseSections 𝒮 f d V) (zero_add j))
        (veroneseSectionMul 𝒮 f d V 0 j (veroneseSectionOne 𝒮 f d V) s) = s :=
  cast_eq_of_eq_veroneseSectionCast 𝒮 f d V (zero_add j) _ _
    (veroneseSectionOne_mul 𝒮 f d V j s)

/-- The right unit law, with the transport written as a `cast` of the section type. -/
theorem veroneseSectionCast_mul_one (j : ℕ) (s : veroneseSections 𝒮 f d V j) :
    cast (congrArg (veroneseSections 𝒮 f d V) (add_zero j))
        (veroneseSectionMul 𝒮 f d V j 0 s (veroneseSectionOne 𝒮 f d V)) = s :=
  cast_eq_of_eq_veroneseSectionCast 𝒮 f d V (add_zero j) _ _
    (veroneseSectionMul_one 𝒮 f d V j s)

/-- Associativity, with the transport written as a `cast` of the section type. -/
theorem veroneseSectionCast_mul_assoc (i j k : ℕ) (a : veroneseSections 𝒮 f d V i)
    (b : veroneseSections 𝒮 f d V j) (c : veroneseSections 𝒮 f d V k) :
    cast (congrArg (veroneseSections 𝒮 f d V) (add_assoc i j k))
        (veroneseSectionMul 𝒮 f d V (i + j) k (veroneseSectionMul 𝒮 f d V i j a b) c) =
      veroneseSectionMul 𝒮 f d V i (j + k) a (veroneseSectionMul 𝒮 f d V j k b c) :=
  cast_eq_of_eq_veroneseSectionCast 𝒮 f d V (add_assoc i j k) _ _
    (veroneseSectionMul_assoc 𝒮 f d V i j k a b c)

/-- Commutativity, with the transport written as a `cast` of the section type. -/
theorem veroneseSectionCast_mul_comm (i j : ℕ) (a : veroneseSections 𝒮 f d V i)
    (b : veroneseSections 𝒮 f d V j) :
    cast (congrArg (veroneseSections 𝒮 f d V) (add_comm i j))
        (veroneseSectionMul 𝒮 f d V i j a b) =
      veroneseSectionMul 𝒮 f d V j i b a :=
  cast_eq_of_eq_veroneseSectionCast 𝒮 f d V (add_comm i j) _ _
    (veroneseSectionMul_comm 𝒮 f d V i j a b)

/-- The sections of the Veronese family over `V` form a graded commutative ring, with degree
`n` piece `Γ(V, f^*𝒪(nd))`, product the image of a pure tensor under the multiplication of the
family, and unit the image of the section `1` of `𝒪_X` under its unit. -/
@[instance_reducible] def veroneseSectionGradedRing :
    DirectSum.GCommRing (veroneseSections 𝒮 f d V) := by
  letI : GradedMonoid.GMul (veroneseSections 𝒮 f d V) :=
    ⟨fun {n m} => veroneseSectionMul 𝒮 f d V n m⟩
  letI : GradedMonoid.GOne (veroneseSections 𝒮 f d V) := ⟨veroneseSectionOne 𝒮 f d V⟩
  refine
    { mul := fun {n m} => veroneseSectionMul 𝒮 f d V n m
      one := veroneseSectionOne 𝒮 f d V
      mul_zero := fun {n m} s => veroneseSectionMul_zero 𝒮 f d V n m s
      zero_mul := fun {n m} t => veroneseSectionZero_mul 𝒮 f d V n m t
      mul_add := fun {n m} s t t' => veroneseSectionMul_add 𝒮 f d V n m s t t'
      add_mul := fun {n m} s s' t => veroneseSectionAdd_mul 𝒮 f d V n m s s' t
      one_mul := ?_
      mul_one := ?_
      mul_assoc := ?_
      mul_comm := ?_
      natCast := fun k => k • veroneseSectionOne 𝒮 f d V
      natCast_zero := zero_nsmul (veroneseSectionOne 𝒮 f d V)
      natCast_succ := fun k => succ_nsmul (veroneseSectionOne 𝒮 f d V) k
      intCast := fun z => z • veroneseSectionOne 𝒮 f d V
      intCast_ofNat := fun k => natCast_zsmul (veroneseSectionOne 𝒮 f d V) k
      intCast_negSucc_ofNat := fun k => negSucc_zsmul (veroneseSectionOne 𝒮 f d V) k }
  · rintro ⟨j, s⟩
    exact Sigma.ext (zero_add j)
      (heq_of_cast_eq (congrArg (veroneseSections 𝒮 f d V) (zero_add j))
        (veroneseSectionCast_one_mul 𝒮 f d V j s))
  · rintro ⟨j, s⟩
    exact Sigma.ext (add_zero j)
      (heq_of_cast_eq (congrArg (veroneseSections 𝒮 f d V) (add_zero j))
        (veroneseSectionCast_mul_one 𝒮 f d V j s))
  · rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
    exact Sigma.ext (add_assoc i j k)
      (heq_of_cast_eq (congrArg (veroneseSections 𝒮 f d V) (add_assoc i j k))
        (veroneseSectionCast_mul_assoc 𝒮 f d V i j k a b c))
  · rintro ⟨i, a⟩ ⟨j, b⟩
    exact Sigma.ext (add_comm i j)
      (heq_of_cast_eq (congrArg (veroneseSections 𝒮 f d V) (add_comm i j))
        (veroneseSectionCast_mul_comm 𝒮 f d V i j a b))

/-- `⨁_{n ≥ 0} Γ(V, f^*𝒪(nd))`, the `d`-th Veronese section ring of the pulled-back twists. -/
abbrev veroneseSectionRing : Type u := ⨁ n : ℕ, veroneseSections 𝒮 f d V n

/-- The degree `n` homogeneous component of the Veronese section ring: the image of the `n`-th
summand. -/
def veroneseSectionRingGrading (n : ℕ) : AddSubgroup (veroneseSectionRing 𝒮 f d V) :=
  (DirectSum.of (veroneseSections 𝒮 f d V) n).range

/-- The homogeneous components of the Veronese section ring are closed under the product and
contain the unit. -/
theorem veroneseSectionRingGrading_gradedMonoid :
    letI := veroneseSectionGradedRing 𝒮 f d V
    SetLike.GradedMonoid (veroneseSectionRingGrading 𝒮 f d V) :=
  let := veroneseSectionGradedRing 𝒮 f d V
  { one_mem := ⟨_, (DirectSum.one_def _).symm⟩
    mul_mem := by
      rintro n m s t ⟨s, rfl⟩ ⟨t, rfl⟩
      exact ⟨_, (DirectSum.of_mul_of (A := veroneseSections 𝒮 f d V) s t).symm⟩ }

/-! ### Values on pullback-unit images -/

/-- The transport of a pullback-unit image along an equality of twist degrees is the pullback-unit
image of the transport. -/
private theorem eqToHom_pullbackTwist_pullbackUnit {a b : ℤ} (h : a = b)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) (s : (twist 𝒮 a).val.obj U) :
    (eqToHom (congrArg (pullbackTwist 𝒮 f) h)).val.app ((opensMap f).op.obj U)
        (pullbackUnit f (twist 𝒮 a) U s) =
      pullbackUnit f (twist 𝒮 b) U ((eqToHom (congrArg (twist 𝒮) h)).val.app U s) := by
  subst h
  rfl

/-- The product of two pullback-unit images is the pullback-unit image of the product
`Stacks.AlgebraicGeometry.TwistTensor.mulSection` of the two local sections on `Proj S`,
transported along `nd + md = (n + m)d`. -/
theorem veroneseSectionMul_pullbackUnit (n m : ℕ)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s : (twist 𝒮 ((n * d : ℕ) : ℤ)).val.obj U)
    (t : (twist 𝒮 ((m * d : ℕ) : ℤ)).val.obj U) :
    veroneseSectionMul 𝒮 f d ((opensMap f).op.obj U) n m
        (pullbackUnit f (twist 𝒮 ((n * d : ℕ) : ℤ)) U s)
        (pullbackUnit f (twist 𝒮 ((m * d : ℕ) : ℤ)) U t) =
      pullbackUnit f (twist 𝒮 (((n + m) * d : ℕ) : ℤ)) U
        ((eqToHom (congrArg (twist 𝒮)
              (show ((n * d : ℕ) : ℤ) + ((m * d : ℕ) : ℤ) = (((n + m) * d : ℕ) : ℤ) from by
                push_cast; ring))).val.app U
          (mulSection 𝒮 ((n * d : ℕ) : ℤ) ((m * d : ℕ) : ℤ) U s t)) := by
  rw [veroneseSectionMul, veroneseMulHom, SheafOfModules.comp_val_app_apply,
    pullbackTwistMul_tmul]
  exact eqToHom_pullbackTwist_pullbackUnit 𝒮 f (by push_cast; ring) U _

/-- The unit section is the pullback-unit image of the unit of the twists of `Proj S`, transported
along `0 = 0 · d`. -/
theorem veroneseSectionOne_pullbackUnit (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) :
    veroneseSectionOne 𝒮 f d ((opensMap f).op.obj U) =
      pullbackUnit f (twist 𝒮 ((0 * d : ℕ) : ℤ)) U
        ((eqToHom (congrArg (twist 𝒮)
              (show (0 : ℤ) = ((0 * d : ℕ) : ℤ) from by push_cast; ring))).val.app U
          ((twistUnit 𝒮).val.app U
            (oneSec (AlgebraicGeometry.Proj 𝒮).toRingedSpace U))) := by
  have h1 : (inv (pullbackUnitComparison f)).val.app ((opensMap f).op.obj U)
        (oneSec X ((opensMap f).op.obj U)) =
      pullbackUnit f (𝟙_ (SheafOfModules.{u}
        (structureRingSheaf (AlgebraicGeometry.Proj 𝒮).toRingedSpace))) U
        (oneSec (AlgebraicGeometry.Proj 𝒮).toRingedSpace U) :=
    (congrArg ((inv (pullbackUnitComparison f)).val.app ((opensMap f).op.obj U))
        (pullbackUnitComparison_oneSec f U).symm).trans
      (inv_val_app_apply (pullbackUnitComparison f) ((opensMap f).op.obj U) _)
  rw [veroneseSectionOne, veroneseOneHom, pullbackTwistUnit, SheafOfModules.comp_val_app_apply,
    SheafOfModules.comp_val_app_apply, h1]
  refine Eq.trans (congrArg _ (pullbackUnit_naturality f (twistUnitRS 𝒮) U _)) ?_
  exact eqToHom_pullbackTwist_pullbackUnit 𝒮 f (by push_cast; ring) U _

end Stacks.AlgebraicGeometry.TwistTensor

end
