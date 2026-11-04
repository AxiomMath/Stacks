module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.JacobsonInverse
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.StalkModule
public import StacksFrontier.AlgebraicGeometry.Variety.NoetherianDimensionOne.TrivializedInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Topology.Sheaves.Glueing.AlgebraicStructure

/-!
# Globally generated invertible modules with a prescribed nonvanishing locus

On an integral separated scheme, a nonempty affine open whose complement is finite and whose
local rings along that complement are Noetherian of dimension one is the nonvanishing locus of a
global section of a globally generated invertible module. This is
[Stacks, Tag 09NB](https://stacks.math.columbia.edu/tag/09NB).

The construction uses only two patches. The second patch `V` is produced by Tag 09N5: the
coordinate ring of `U` and the local rings at the omitted points all sit inside the function
field of `X`, the omitted points have dimension one, and so some nonzero `f ∈ Γ(X, U)` has
`f⁻¹` in the maximal ideal of every one of those local rings. Gluing the sections `f⁻¹` over
neighbourhoods of the omitted points gives `g ∈ Γ(X, V)` with `U ⊔ V = ⊤` and `f·g = 1` on
`U ⊓ V`. Then the structure sheaf is glued to itself over `U ⊓ V` along multiplication by the
unit `f·g`, producing an invertible module `L` with two tautological trivializations, and the
pair `(1, g)` is a global section of `L` whose nonvanishing locus is exactly `U` — it is a unit
at every point of `U`, and at a point outside `U` the germ of `g` lies in the maximal ideal.
Global generation comes from the two sections `(1, g)` and `(f, 1)`, which trivialize `L` on
`U` and on `V` respectively.

## Main results

* `AlgebraicGeometry.exists_isInvertible_generatingSections_nonvanishingOpen_eq`: the globally
  generated invertible module and its section.

## Implementation notes

Global generation is `Mathlib`'s `SheafOfModules.GeneratingSections`, and the nonvanishing open
is the canonical open of Tag 01CY, which takes invertibility as an instance; the invertibility
witness is therefore bound explicitly in the statement. Finiteness of the complement is
expressed directly as finiteness of its underlying set of points.

Invertibility is read off from the two tautological trivializations through
`Stacks.SheafOfModules.Trivialized.isInvertible_of_coversTop_trivialization`, which is the
unconditional direction of Tag 0B8M in trivialization form.

Tag 01CY states the nonvanishing locus with the stalk module structure of Tag 01CB, while the
stalk computations below use Mathlib's stalk module structure on a presheaf of modules; the two
agree (`Stacks.SheafOfModules.stalkModule_eq`), and `Stacks.SheafOfModules.mem_smul_top_congr`
transports membership in `𝔪 • ⊤` across the equality.

Tag 09N5 is stated on main for semilocal rings, which the Stacks source also has here: the rings
in question are the local rings of `X` at the omitted points, and a local ring has a singleton
maximal spectrum, so the hypothesis is discharged rather than assumed.

## References

* [Stacks Project, Tag 09NB](https://stacks.math.columbia.edu/tag/09NB)
* [Stacks Project, Tag 09N5](https://stacks.math.columbia.edu/tag/09N5)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry TopCat

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.NoetherianDimensionOne

/-- The two-element index set of the patch cover. -/
inductive TwoPatch : Type u
  | first
  | second

/-- The two-patch cover. -/
def twoOpenCover {X : Scheme.{u}} (U V : X.Opens) :
    TwoPatch → X.Opens
  | .first => U
  | .second => V

/-- The sections of a sheaf of rings over the opens contained in `W`, as a local presheaf of
sets. -/
def twoOpenLocalPresheaf {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace)
    (W : X.Opens) : TopCat.Sheaf.LocalPresheaf X.toPresheafedSpace W :=
  TopCat.Presheaf.toLocalPresheaf (O.obj ⋙ CategoryTheory.forget RingCat) W

/-- The local presheaf of sections of a sheaf of rings is a sheaf. -/
lemma twoOpenLocalPresheaf_isSheaf {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (W : X.Opens) :
    (twoOpenLocalPresheaf O W).IsSheaf :=
  TopCat.Presheaf.isSheaf_toLocalPresheaf
    ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (CategoryTheory.forget RingCat) O.obj).mp O.property) W

/-- Restriction of sections of a sheaf of rings along an inclusion of opens, as a ring
homomorphism. -/
def twoOpenRestriction {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace)
    {W Z : X.Opens} (h : Z ≤ W) :
    (O.obj.obj (op W) : Type u) →+* (O.obj.obj (op Z) : Type u) :=
  (O.obj.map (homOfLE h).op).hom

/-- Restriction along a composite inclusion of opens is the composite of the restrictions. -/
lemma twoOpenRestriction_comp {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace)
    {V W Z : X.Opens} (hVW : W ≤ V) (hZW : Z ≤ W) :
    twoOpenRestriction O (hZW.trans hVW) =
      (twoOpenRestriction O hZW).comp (twoOpenRestriction O hVW) := by
  ext x
  show (O.obj.map (homOfLE (hZW.trans hVW)).op).hom x = _
  have hc : (homOfLE hVW).op ≫ (homOfLE hZW).op =
      (homOfLE (hZW.trans hVW)).op := Subsingleton.elim _ _
  rw [← hc, Functor.map_comp]
  rfl

/-- Restricting twice is restricting along the composite inclusion. -/
private lemma twoOpenRestriction_restriction {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace)
    {V W Z : X.Opens} (hVW : W ≤ V) (hZW : Z ≤ W) (x : (O.obj.obj (op V) : Type u)) :
    twoOpenRestriction O hZW (twoOpenRestriction O hVW x) =
      twoOpenRestriction O (hZW.trans hVW) x :=
  (RingHom.congr_fun (twoOpenRestriction_comp O hVW hZW) x).symm

/-- The additive groups of sections of a sheaf of rings over the opens contained in `W`, as a
local presheaf of abelian groups. -/
def twoOpenAddLocalPresheaf {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace)
    (W : X.Opens) : TopCat.Sheaf.AddLocalPresheaf X.toPresheafedSpace W where
  obj Z h := AddCommGrpCat.of (O.obj.obj (op Z) : Type u)
  map h := AddCommGrpCat.ofHom (twoOpenRestriction O h).toAddMonoidHom
  map_id := by
    intro V hV
    apply AddCommGrpCat.hom_ext
    ext x
    simp [twoOpenRestriction]
  map_map h₁ h₂ := by
    apply AddCommGrpCat.hom_ext
    ext x
    change twoOpenRestriction O h₂ (twoOpenRestriction O h₁ x) = _
    rw [twoOpenRestriction_comp O h₁ h₂]
    rfl

/-- The local presheaf of additive groups of sections of a sheaf of rings is a sheaf. -/
lemma twoOpenAddLocalPresheaf_isSheaf {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (W : X.Opens) :
    (twoOpenAddLocalPresheaf O W).toLocalPresheaf.IsSheaf := twoOpenLocalPresheaf_isSheaf O W

/-- The transition isomorphism of the two-patch descent datum: multiplication by the unit `a`,
or its inverse, on the overlap, and the identity on each patch. -/
def twoOpenAddTransEquiv {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (i j : TwoPatch) {W : X.Opens} (hi : W ≤ twoOpenCover U V i)
    (hj : W ≤ twoOpenCover U V j) :
    (O.obj.obj (op W) : Type u) ≃+ (O.obj.obj (op W) : Type u) := by
  cases i with
  | first =>
    cases j with
    | first => exact AddEquiv.refl _
    | second =>
      change W ≤ U at hi
      change W ≤ V at hj
      let r : (O.obj.obj (op (U ⊓ V)) : Type u) →*
          (O.obj.obj (op W) : Type u) :=
        (twoOpenRestriction O (le_inf hi hj)).toMonoidHom
      exact AddAut.mulLeft (Units.map r a)⁻¹
  | second =>
    cases j with
    | first =>
      change W ≤ V at hi
      change W ≤ U at hj
      let r : (O.obj.obj (op (U ⊓ V)) : Type u) →*
          (O.obj.obj (op W) : Type u) :=
        (twoOpenRestriction O (le_inf hj hi)).toMonoidHom
      exact AddAut.mulLeft (Units.map r a)
    | second => exact AddEquiv.refl _

/-- The set descent datum for two copies of the structure sheaf, compared by multiplication
by a unit on the overlap. -/
def twoOpenGlueData {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ) :
    TopCat.Sheaf.GlueData X.toPresheafedSpace (twoOpenCover U V) where
  sheaf i := twoOpenLocalPresheaf O (twoOpenCover U V i)
  isSheaf i := twoOpenLocalPresheaf_isSheaf O (twoOpenCover U V i)
  trans i j {W} hi hj := by
    cases i with
    | first =>
      cases j with
      | first => exact Equiv.refl _
      | second =>
        change W ≤ U at hi
        change W ≤ V at hj
        dsimp [twoOpenLocalPresheaf, TopCat.Presheaf.toLocalPresheaf]
        let r : (O.obj.obj (op (U ⊓ V)) : Type u) →*
            (O.obj.obj (op W) : Type u) :=
          (twoOpenRestriction O (le_inf hi hj)).toMonoidHom
        exact (Units.map r a)⁻¹.mulLeft
    | second =>
      cases j with
      | first =>
        change W ≤ V at hi
        change W ≤ U at hj
        dsimp [twoOpenLocalPresheaf, TopCat.Presheaf.toLocalPresheaf]
        let r : (O.obj.obj (op (U ⊓ V)) : Type u) →*
            (O.obj.obj (op W) : Type u) :=
          (twoOpenRestriction O (le_inf hj hi)).toMonoidHom
        exact (Units.map r a).mulLeft
      | second => exact Equiv.refl _
  trans_map := by
    intro i j W Z hi hj hZW x
    cases i with
    | first =>
      cases j with
      | first => rfl
      | second =>
        change W ≤ U at hi
        change W ≤ V at hj
        change (O.obj.obj (op W) : Type u) at x
        change ((Units.map
            (twoOpenRestriction O (le_inf (hZW.trans hi) (hZW.trans hj))).toMonoidHom a)⁻¹ : _) *
            twoOpenRestriction O hZW x =
          twoOpenRestriction O hZW
            (((Units.map
              (twoOpenRestriction O (le_inf hi hj)).toMonoidHom a)⁻¹ : _) * x)
        rw [show twoOpenRestriction O (le_inf (hZW.trans hi) (hZW.trans hj)) =
            (twoOpenRestriction O hZW).comp (twoOpenRestriction O (le_inf hi hj)) by
              rw [twoOpenRestriction_comp]]
        simp [map_mul]
    | second =>
      cases j with
      | first =>
        change W ≤ V at hi
        change W ≤ U at hj
        change (O.obj.obj (op W) : Type u) at x
        change (Units.map
            (twoOpenRestriction O (le_inf (hZW.trans hj) (hZW.trans hi))).toMonoidHom a : _) *
            twoOpenRestriction O hZW x =
          twoOpenRestriction O hZW
            ((Units.map
              (twoOpenRestriction O (le_inf hj hi)).toMonoidHom a : _) * x)
        rw [show twoOpenRestriction O (le_inf (hZW.trans hj) (hZW.trans hi)) =
            (twoOpenRestriction O hZW).comp (twoOpenRestriction O (le_inf hj hi)) by
              rw [twoOpenRestriction_comp]]
        simp [map_mul]
      | second => rfl
  trans_trans := by
    intro i j k W hi hj hk x
    change (O.obj.obj (op W) : Type u) at x
    cases i with
    | first =>
      change W ≤ U at hi
      cases j with
      | first =>
        change W ≤ U at hj
        cases k with
        | first => rfl
        | second =>
          change W ≤ V at hk
          rfl
      | second =>
        change W ≤ V at hj
        cases k with
        | first =>
          change W ≤ U at hk
          change ↑(Units.map
              (twoOpenRestriction O (le_inf hk hj)).toMonoidHom a) *
            (↑((Units.map
              (twoOpenRestriction O (le_inf hi hj)).toMonoidHom a)⁻¹) * x) = x
          have hc : twoOpenRestriction O (le_inf hk hj) =
              twoOpenRestriction O (le_inf hi hj) := by
            congr 1
          let f := twoOpenRestriction O (le_inf hi hj)
          have hcM : (twoOpenRestriction O (le_inf hk hj)).toMonoidHom =
              f.toMonoidHom := congrArg RingHom.toMonoidHom hc
          rw [hcM]
          calc
            f (↑a) * (f (↑a⁻¹) * x) = (f (↑a) * f (↑a⁻¹)) * x := by rw [← mul_assoc]
            _ = f (↑a * ↑a⁻¹) * x := by rw [← map_mul]
            _ = x := by simp
        | second =>
          change W ≤ V at hk
          rfl
    | second =>
      change W ≤ V at hi
      cases j with
      | first =>
        change W ≤ U at hj
        cases k with
        | first =>
          change W ≤ U at hk
          rfl
        | second =>
          change W ≤ V at hk
          change ↑((Units.map
              (twoOpenRestriction O (le_inf hj hi)).toMonoidHom a)⁻¹) *
            (↑(Units.map
              (twoOpenRestriction O (le_inf hj hk)).toMonoidHom a) * x) = x
          have hc : twoOpenRestriction O (le_inf hj hi) =
              twoOpenRestriction O (le_inf hj hk) := by
            congr 1
          let f := twoOpenRestriction O (le_inf hj hi)
          have hcM : (twoOpenRestriction O (le_inf hj hk)).toMonoidHom =
              f.toMonoidHom := congrArg RingHom.toMonoidHom hc.symm
          rw [hcM]
          calc
            f (↑a⁻¹) * (f (↑a) * x) = (f (↑a⁻¹) * f (↑a)) * x := by rw [← mul_assoc]
            _ = f (↑a⁻¹ * ↑a) * x := by rw [← map_mul]
            _ = x := by simp
      | second =>
        change W ≤ V at hj
        cases k with
        | first =>
          change W ≤ U at hk
          rfl
        | second => rfl

/-- The transition isomorphism of the additive descent datum acts as the transition map of the
underlying descent datum of sets. -/
lemma twoOpenAddTransEquiv_apply {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (i j : TwoPatch) {W : X.Opens} (hi : W ≤ twoOpenCover U V i)
    (hj : W ≤ twoOpenCover U V j) (x : (O.obj.obj (op W) : Type u)) :
    ((twoOpenAddTransEquiv O U V a i j hi hj) x : (O.obj.obj (op W) : Type u)) =
      ((twoOpenGlueData O U V a).trans i j hi hj x : (O.obj.obj (op W) : Type u)) := by
  cases i <;> cases j <;> rfl

/-- The additive descent datum for two copies of the structure sheaf, compared by multiplication
by a unit on the overlap. -/
def twoOpenAddGlueData {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ) :
    TopCat.Sheaf.AddGlueData X.toPresheafedSpace (twoOpenCover U V) where
  sheaf i := twoOpenAddLocalPresheaf O (twoOpenCover U V i)
  isSheaf i := twoOpenAddLocalPresheaf_isSheaf O (twoOpenCover U V i)
  trans i j {W} hi hj :=
    AddEquiv.toAddCommGrpIso
      (X := AddCommGrpCat.of (O.obj.obj (op W) : Type u))
      (Y := AddCommGrpCat.of (O.obj.obj (op W) : Type u))
      (twoOpenAddTransEquiv O U V a i j hi hj)
  trans_map := by
    intro i j W Z hi hj hZW
    apply AddCommGrpCat.hom_ext
    ext x; change (O.obj.obj (op W) : Type u) at x
    change (twoOpenAddTransEquiv O U V a i j (hZW.trans hi) (hZW.trans hj))
        (twoOpenRestriction O hZW x) =
      twoOpenRestriction O hZW ((twoOpenAddTransEquiv O U V a i j hi hj) x)
    rw [twoOpenAddTransEquiv_apply, twoOpenAddTransEquiv_apply]
    exact (twoOpenGlueData O U V a).trans_map i j hi hj hZW x
  trans_trans := by
    intro i j k W hi hj hk
    apply AddCommGrpCat.hom_ext
    ext x
    change (O.obj.obj (op W) : Type u) at x
    change (twoOpenAddTransEquiv O U V a j k hj hk)
        ((twoOpenAddTransEquiv O U V a i j hi hj) x) =
      (twoOpenAddTransEquiv O U V a i k hi hk) x
    rw [twoOpenAddTransEquiv_apply, twoOpenAddTransEquiv_apply,
      twoOpenAddTransEquiv_apply]
    exact (twoOpenGlueData O U V a).trans_trans i j k hi hj hk x

/-- The transition isomorphism of the two-patch descent datum is the transition map of the
additive descent datum built from it. -/
lemma twoOpenAddTransEquiv_hom {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (i j : TwoPatch) {W : X.Opens} (hi : W ≤ twoOpenCover U V i)
    (hj : W ≤ twoOpenCover U V j) :
    twoOpenAddTransEquiv O U V a i j hi hj =
      ((twoOpenAddGlueData O U V a).trans i j hi hj).addCommGroupIsoToAddEquiv := by
  cases i <;> cases j <;> rfl

/-- Left multiplication by a unit of `S` commutes with multiplication by an element pulled
back along a ring homomorphism, when multiplication on `S` is commutative. -/
lemma twoOpenMulAddEquiv_smul {R S : Type u} [Ring R] [Ring S]
    (φ : R →+* S) (a : Sˣ) (r : R) (x : S)
    (hcomm : ∀ x y : S, x * y = y * x) :
    a * (φ r * x) = φ r * (a * x) := by rw [← mul_assoc, hcomm (↑a) (φ r), mul_assoc]

/-- The transition isomorphism is linear for multiplication by a section, when multiplication on
the sections over the overlap is commutative. -/
lemma twoOpenAddTransEquiv_smul {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (i j : TwoPatch) {W : X.Opens}
    (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j)
    (r x : (O.obj.obj (op W) : Type u)) :
    (hcomm : ∀ x y : (O.obj.obj (op W) : Type u), x * y = y * x) →
    twoOpenAddTransEquiv O U V a i j hi hj (r * x) =
      r * twoOpenAddTransEquiv O U V a i j hi hj x := by
  intro hcomm
  cases i <;> cases j <;> first | rfl | exact twoOpenMulAddEquiv_smul (RingHom.id _) _ r x hcomm

/-- Restriction of sections from `W` to its intersection with a patch, as a ring homomorphism. -/
def twoOpenScalarRestriction {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (i : TwoPatch) (W : X.Opens) :
    (O.obj.obj (op W) : Type u) →+* (O.obj.obj (op (W ⊓ twoOpenCover U V i)) : Type u) :=
  twoOpenRestriction O (inf_le_left : W ⊓ twoOpenCover U V i ≤ W)

/-- The sections over `W ⊓ Vᵢ` form a module over the sections over `W`, by restriction and
multiplication. -/
instance twoOpenAmbientModule {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (W : X.Opens) : Module (O.obj.obj (op W) : Type u)
      (∀ i : TwoPatch,
        (O.obj.obj (op (W ⊓ twoOpenCover U V i)) : Type u)) := by
  let R := (O.obj.obj (op W) : Type u)
  letI : ∀ i : TwoPatch, Module R
      (O.obj.obj (op (W ⊓ twoOpenCover U V i)) : Type u) :=
    fun i => Module.compHom _ (twoOpenScalarRestriction O U V i W)
  exact inferInstance

/-- The sections over `W` of the module glued from two copies of the structure sheaf: the tuples
of sections over the patches that agree under the transition isomorphisms. -/
def twoOpenModuleSectionsSubmodule {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x)
    (W : X.Opens) :
    Submodule (O.obj.obj (op W) : Type u)
      (∀ i : TwoPatch,
        (O.obj.obj (op (W ⊓ twoOpenCover U V i)) : Type u)) := by
  let R := (O.obj.obj (op W) : Type u)
  letI : ∀ i : TwoPatch, Module R
      (O.obj.obj (op (W ⊓ twoOpenCover U V i)) : Type u) :=
    fun i => Module.compHom _ (twoOpenScalarRestriction O U V i W)
  let D := twoOpenAddGlueData O U V a
  refine {
    carrier := (D.sectionsAddSubgroup W).carrier
    zero_mem' := (D.sectionsAddSubgroup W).zero_mem
    add_mem' := fun hs ht => (D.sectionsAddSubgroup W).add_mem hs ht
    smul_mem' := by
      intro r s hs
      change ∀ i j : TwoPatch, _ = _ at hs
      intro i j
      let Z := W ⊓ twoOpenCover U V i ⊓ (W ⊓ twoOpenCover U V j)
      let hi : Z ≤ W ⊓ twoOpenCover U V i := inf_le_left
      let hj : Z ≤ W ⊓ twoOpenCover U V j := inf_le_right
      let hci : Z ≤ twoOpenCover U V i := hi.trans inf_le_right
      let hcj : Z ≤ twoOpenCover U V j := hj.trans inf_le_right
      let hZi : Z ≤ W := hi.trans inf_le_left
      let hZj : Z ≤ W := hj.trans inf_le_left
      have hri : twoOpenRestriction O hZi r =
          twoOpenRestriction O hi (twoOpenScalarRestriction O U V i W r) := by
        have h := congrArg (fun f : (O.obj.obj (op W) : Type u) →+*
            (O.obj.obj (op Z) : Type u) => f r)
          (twoOpenRestriction_comp O
            (inf_le_left : W ⊓ twoOpenCover U V i ≤ W) hi)
        simpa [twoOpenScalarRestriction, Function.comp_def] using h
      have hrj : twoOpenRestriction O hZj r =
          twoOpenRestriction O hj (twoOpenScalarRestriction O U V j W r) := by
        have h := congrArg (fun f : (O.obj.obj (op W) : Type u) →+*
            (O.obj.obj (op Z) : Type u) => f r)
          (twoOpenRestriction_comp O
            (inf_le_left : W ⊓ twoOpenCover U V j ≤ W) hj)
        simpa [twoOpenScalarRestriction, Function.comp_def] using h
      change twoOpenAddTransEquiv O U V a i j hci hcj
          (twoOpenRestriction O hi
            (twoOpenScalarRestriction O U V i W r * s i)) =
        twoOpenRestriction O hj
          (twoOpenScalarRestriction O U V j W r * s j)
      rw [map_mul (twoOpenRestriction O hi) (twoOpenScalarRestriction O U V i W r) (s i)]
      rw [map_mul (twoOpenRestriction O hj) (twoOpenScalarRestriction O U V j W r) (s j)]
      rw [← hri, ← hrj]
      rw [twoOpenAddTransEquiv_smul O U V a i j hci hcj
        (twoOpenRestriction O hZi r) (twoOpenRestriction O hi (s i)) (hcomm Z)]
      have hcompat : twoOpenAddTransEquiv O U V a i j hci hcj
          (twoOpenRestriction O hi (s i)) = twoOpenRestriction O hj (s j) := by
        rw [twoOpenAddTransEquiv_hom]
        exact hs i j
      rw [hcompat]
  }

/-- The presheaf of modules glued from two copies of the structure sheaf along multiplication by
a unit on the overlap. -/
noncomputable def twoOpenModuleGluePresheaf {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x) :
    PresheafOfModules O.obj := by
  let D := twoOpenAddGlueData O U V a
  letI : ∀ W : (X.Opens)ᵒᵖ,
      Module (O.obj.obj W) (D.gluedAddPresheaf.obj W) := fun W => by
    change Module (O.obj.obj W : Type u)
      (twoOpenModuleSectionsSubmodule O U V a hcomm W.unop)
    infer_instance
  refine PresheafOfModules.ofPresheaf D.gluedAddPresheaf ?_
  intro W Z f r s
  change twoOpenModuleSectionsSubmodule O U V a hcomm W.unop at s
  let : Module (O.obj.obj Z : Type u) ↥(D.sectionsAddSubgroup Z.unop) := by
    change Module (O.obj.obj Z : Type u)
      (twoOpenModuleSectionsSubmodule O U V a hcomm Z.unop)
    infer_instance
  apply Subtype.ext
  funext i
  change ((D.sectionsMapHom f.unop.le).hom (r • s)).1 i =
    ((O.obj.map f).hom r • (D.sectionsMapHom f.unop.le).hom s).1 i
  change twoOpenRestriction O (inf_le_inf_right (twoOpenCover U V i) f.unop.le)
      (twoOpenScalarRestriction O U V i W.unop r * s.1 i) =
    twoOpenScalarRestriction O U V i Z.unop ((O.obj.map f).hom r) *
      twoOpenRestriction O (inf_le_inf_right (twoOpenCover U V i) f.unop.le) (s.1 i)
  rw [map_mul]
  congr 1
  change twoOpenRestriction O (inf_le_inf_right (twoOpenCover U V i) f.unop.le)
      (twoOpenRestriction O inf_le_left r) =
    twoOpenRestriction O inf_le_left (twoOpenRestriction O f.unop.le r)
  rw [← RingHom.comp_apply, ← twoOpenRestriction_comp,
    ← RingHom.comp_apply, ← twoOpenRestriction_comp]

/-- The sheaf of modules glued from two copies of the structure sheaf along multiplication by a
unit on the overlap. -/
noncomputable def twoOpenModuleGlueSheaf {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x) :
    SheafOfModules.{u} O where
  val := twoOpenModuleGluePresheaf O U V a hcomm
  isSheaf := (twoOpenAddGlueData O U V a).gluedAddPresheaf_isSheaf

private noncomputable def twoOpenModuleSectionsLinearEquiv {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x)
    (i : TwoPatch) {W : X.Opens} (hW : W ≤ twoOpenCover U V i) :
    (twoOpenModuleGlueSheaf O U V a hcomm).val.obj (op W) ≃ₗ[O.obj.obj (op W)]
      (O.obj.obj (op W)) := by
  let D := twoOpenAddGlueData O U V a
  refine { __ := D.toGlueData.sectionsEquiv i hW
           map_add' := ?_
           map_smul' := ?_ }
  · intro s t
    change twoOpenRestriction O (le_inf le_rfl hW) (s.1 i + t.1 i) = _
    exact map_add _ _ _
  · intro r s
    change twoOpenModuleSectionsSubmodule O U V a hcomm W at s
    change twoOpenRestriction O (le_inf le_rfl hW)
        (twoOpenScalarRestriction O U V i W r * s.1 i) =
      r * twoOpenRestriction O (le_inf le_rfl hW) (s.1 i)
    rw [map_mul]
    congr 1
    change twoOpenRestriction O (le_inf le_rfl hW)
        (twoOpenRestriction O inf_le_left r) = r
    rw [twoOpenRestriction_restriction]
    change (O.obj.map (𝟙 (op W))).hom r = r
    simp

/-- The tautological isomorphism of the glued module with the unit module over a patch. -/
private noncomputable def twoOpenModuleOverIso {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x)
    (i : TwoPatch) :
    (twoOpenModuleGlueSheaf O U V a hcomm).over (twoOpenCover U V i) ≅
      SheafOfModules.unit (O.over (twoOpenCover U V i)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W =>
      (twoOpenModuleSectionsLinearEquiv O U V a hcomm i W.unop.hom.le).toModuleIso) (by
      intro W W' f
      ext z
      exact (twoOpenAddGlueData O U V a).toGlueData.sectionsEquiv_map i
        W.unop.hom.le f.unop.left.le z))

/-- Multiplication on the sections of the structure sheaf of a scheme over an open set is
commutative. -/
lemma structureSheaf_mul_comm (X : Scheme.{u}) (W : X.Opens)
    (r s : X.ringCatSheaf.obj.obj (op W)) : r * s = s * r :=
  @mul_comm Γ(X, W) inferInstance r s

/-- The tautological trivialization of the glued module on a patch, in the form consumed by
`Stacks.SheafOfModules.Trivialized.isInvertible_of_coversTop_trivialization`. -/
private noncomputable def twoOpenModuleTrivialization (X : Scheme.{u}) (U V : X.Opens)
    (a : Γ(X, U ⊓ V)ˣ) (i : TwoPatch) :
    Stacks.SheafOfModules.Trivialized.Trivialization X.toRingedSpace.presheaf
      (structureSheaf X.toRingedSpace.sheaf).property
      (twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X))
      (twoOpenCover U V i) :=
  (SheafOfModules.forget _).mapIso
    (twoOpenModuleOverIso X.ringCatSheaf U V a (structureSheaf_mul_comm X) i)

private lemma twoOpenCover_coversTop (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    (Opens.grothendieckTopology X).CoversTop (twoOpenCover U V) := by
  apply (Opens.coversTop_iff _ (twoOpenCover U V)).mpr
  apply top_le_iff.mp
  rw [← hcover]
  exact sup_le (le_iSup (twoOpenCover U V) TwoPatch.first)
    (le_iSup (twoOpenCover U V) TwoPatch.second)

private lemma twoOpenModuleGlueSheaf_isInvertible (X : Scheme.{u}) (U V : X.Opens)
    (a : Γ(X, U ⊓ V)ˣ) (hcover : U ⊔ V = ⊤) :
    Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheaf X.toRingedSpace.sheaf).property
      (twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X)) :=
  Stacks.SheafOfModules.Trivialized.isInvertible_of_coversTop_trivialization
    (twoOpenCover_coversTop X U V hcover) (twoOpenModuleTrivialization X U V a)

private noncomputable def twoOpenModuleSection {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x)
    (t : ∀ i, (O.obj.obj (op (twoOpenCover U V i)) : Type u))
    (ht : ∀ (i j : TwoPatch) {W : X.Opens}
      (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j),
      twoOpenAddTransEquiv O U V a i j hi hj (twoOpenRestriction O hi (t i)) =
        twoOpenRestriction O hj (t j)) :
    (twoOpenModuleGlueSheaf O U V a hcomm).sections := by
  refine PresheafOfModules.sectionsMk
    (M := (twoOpenModuleGlueSheaf O U V a hcomm).val)
    (fun W => ⟨fun i => twoOpenRestriction O inf_le_right (t i), ?_⟩) ?_
  · intro i j
    change twoOpenAddTransEquiv O U V a i j _ _
        (twoOpenRestriction O inf_le_left (twoOpenRestriction O inf_le_right (t i))) =
      twoOpenRestriction O inf_le_right (twoOpenRestriction O inf_le_right (t j))
    rw [twoOpenRestriction_restriction, twoOpenRestriction_restriction]
    exact ht i j _ _
  · intro W Z f
    apply Subtype.ext
    funext i
    change twoOpenRestriction O (inf_le_inf_right (twoOpenCover U V i) f.unop.le)
        (twoOpenRestriction O inf_le_right (t i)) =
      twoOpenRestriction O inf_le_right (t i)
    rw [twoOpenRestriction_restriction]

private lemma twoOpenModuleSection_trivialization {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x)
    (t : ∀ i, (O.obj.obj (op (twoOpenCover U V i)) : Type u))
    (ht : ∀ (i j : TwoPatch) {W : X.Opens}
      (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j),
      twoOpenAddTransEquiv O U V a i j hi hj (twoOpenRestriction O hi (t i)) =
        twoOpenRestriction O hj (t j))
    (i : TwoPatch) {W : X.Opens} (hW : W ≤ twoOpenCover U V i) :
    twoOpenModuleSectionsLinearEquiv O U V a hcomm i hW
        ((twoOpenModuleSection O U V a hcomm t ht).eval (op W)) =
      twoOpenRestriction O hW (t i) := by
  show twoOpenRestriction O (le_inf le_rfl hW)
      (twoOpenRestriction O inf_le_right (t i)) = _
  rw [twoOpenRestriction_restriction]

/-- The pair of sections over the two patches with prescribed values. -/
def twoOpenValues {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (x : O.obj.obj (op U)) (y : O.obj.obj (op V)) :
    ∀ i, (O.obj.obj (op (twoOpenCover U V i)) : Type u)
  | .first => x
  | .second => y

private lemma twoOpenValues_compatible {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (x : O.obj.obj (op U)) (y : O.obj.obj (op V))
    (h : twoOpenRestriction O inf_le_left x =
      (a : O.obj.obj (op (U ⊓ V))) * twoOpenRestriction O inf_le_right y)
    (i j : TwoPatch) {W : X.Opens}
    (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j) :
    twoOpenAddTransEquiv O U V a i j hi hj
        (twoOpenRestriction O hi (twoOpenValues O U V x y i)) =
      twoOpenRestriction O hj (twoOpenValues O U V x y j) := by
  have hres {W : X.Opens} (hU : W ≤ U) (hV : W ≤ V) :
      twoOpenRestriction O hU x =
        twoOpenRestriction O (le_inf hU hV) (a : O.obj.obj (op (U ⊓ V))) *
          twoOpenRestriction O hV y := by
    have hh := congrArg (twoOpenRestriction O (le_inf hU hV)) h
    rwa [map_mul, twoOpenRestriction_restriction, twoOpenRestriction_restriction] at hh
  cases i <;> cases j
  · rfl
  · show (↑((Units.map (twoOpenRestriction O (le_inf hi hj)).toMonoidHom a)⁻¹)) *
        twoOpenRestriction O hi x = twoOpenRestriction O hj y
    rw [show twoOpenRestriction O hi x =
        twoOpenRestriction O (le_inf hi hj) (a : O.obj.obj (op (U ⊓ V))) *
          twoOpenRestriction O hj y from hres hi hj]
    show (↑((Units.map (twoOpenRestriction O (le_inf hi hj)).toMonoidHom a)⁻¹)) *
        (↑(Units.map (twoOpenRestriction O (le_inf hi hj)).toMonoidHom a) *
          twoOpenRestriction O hj y) = _
    rw [← mul_assoc, Units.inv_mul, one_mul]
  · exact (hres hj hi).symm
  · rfl

private lemma twoOpenModuleSection_unitHom_isIso {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x)
    (t : ∀ i, (O.obj.obj (op (twoOpenCover U V i)) : Type u))
    (ht : ∀ (i j : TwoPatch) {W : X.Opens}
      (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j),
      twoOpenAddTransEquiv O U V a i j hi hj (twoOpenRestriction O hi (t i)) =
        twoOpenRestriction O hj (t j))
    (i : TwoPatch) (hi : t i = 1) :
    IsIso (((twoOpenModuleGlueSheaf O U V a hcomm).unitHomEquiv.symm
      (twoOpenModuleSection O U V a hcomm t ht)).over (twoOpenCover U V i)) := by
  let M := twoOpenModuleGlueSheaf O U V a hcomm
  let s := twoOpenModuleSection O U V a hcomm t ht
  let e := twoOpenModuleOverIso O U V a hcomm i
  let f := (M.unitHomEquiv.symm s).over (twoOpenCover U V i)
  have h : f ≫ e.hom = 𝟙 (SheafOfModules.unit (O.over (twoOpenCover U V i))) := by
    apply SheafOfModules.hom_ext
    ext W : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change (O.obj.obj (op W.unop.left) : Type u) at r
    show twoOpenModuleSectionsLinearEquiv O U V a hcomm i W.unop.hom.le
        (r • s.eval (op W.unop.left)) = r
    rw [map_smul]
    have he := twoOpenModuleSection_trivialization O U V a hcomm t ht i W.unop.hom.le
    change twoOpenModuleSectionsLinearEquiv O U V a hcomm i W.unop.hom.le
        (s.eval (op W.unop.left)) = _ at he
    rw [he, hi, map_one]
    exact mul_one r
  have : IsIso (f ≫ e.hom) := h ▸ CategoryTheory.IsIso.id _
  exact IsIso.of_isIso_comp_right f e.hom

private lemma hom_ext_of_over_eq {X : Scheme.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {M N : SheafOfModules.{u} O} {ι : Type u} (W : ι → X.Opens)
    (hW : (Opens.grothendieckTopology X).CoversTop W)
    (f g : SheafOfModules.Hom M N) (h : ∀ i, f.over (W i) = g.over (W i)) : f = g := by
  apply (SheafOfModules.forget O ⋙ PresheafOfModules.toPresheaf O.obj).map_injective
  apply NatTrans.ext
  funext Z
  apply N.isSheaf.hom_ext (hW.cover Z.unop)
  rintro ⟨T, b, ⟨i, ⟨c⟩⟩⟩
  let F := (PresheafOfModules.toPresheaf O.obj).map f.val
  let G := (PresheafOfModules.toPresheaf O.obj).map g.val
  have hh : F.app (op T) = G.app (op T) := by
    have he := congrArg (fun q =>
      ((PresheafOfModules.toPresheaf (O.over (W i)).obj).map q.val).app
        (op (Over.mk c))) (h i)
    exact he
  show F.app Z ≫ N.val.presheaf.map b.op = G.app Z ≫ N.val.presheaf.map b.op
  exact (F.naturality b.op).symm.trans
    ((congrArg (fun k => M.val.presheaf.map b.op ≫ k) hh).trans (G.naturality b.op))

private lemma epi_of_epi_over {X : Scheme.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {M N : SheafOfModules.{u} O} {ι : Type u} (W : ι → X.Opens)
    (hW : (Opens.grothendieckTopology X).CoversTop W)
    (f : M ⟶ N) (hf : ∀ i, Epi (f.over (W i))) : Epi f := by
  constructor
  intro P g k h
  apply hom_ext_of_over_eq O W hW
  intro i
  let := hf i
  exact (cancel_epi (f.over (W i))).mp (congrArg (fun q => q.over (W i)) h)

private lemma nonempty_generatingSections_of_unitHom_epi_over {X : Scheme.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (M : SheafOfModules.{u} O) {ι : Type u} (W : ι → X.Opens)
    (hW : (Opens.grothendieckTopology X).CoversTop W) (s : ι → M.sections)
    (hs : ∀ i, Epi ((M.unitHomEquiv.symm (s i)).over (W i))) :
    Nonempty M.GeneratingSections := by
  let p := M.freeHomEquiv.symm s
  have hp : Epi p := by
    apply epi_of_epi_over O W hW
    intro i
    have hi : SheafOfModules.ιFree i ≫ p = M.unitHomEquiv.symm (s i) := by
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      exact congrArg M.unitHomEquiv.symm (congrFun (M.freeHomEquiv.apply_symm_apply s) i)
    have hcomp : (SheafOfModules.ιFree i).over (W i) ≫ p.over (W i) =
        (M.unitHomEquiv.symm (s i)).over (W i) := by
      show (SheafOfModules.overFunctor O (W i)).map (SheafOfModules.ιFree i) ≫
          (SheafOfModules.overFunctor O (W i)).map p = _
      rw [← Functor.map_comp, hi]
    have : Epi ((SheafOfModules.ιFree i).over (W i) ≫ p.over (W i)) := by
      rw [hcomp]
      exact hs i
    exact epi_of_epi (SheafOfModules.ιFree i |>.over (W i)) (p.over (W i))
  exact ⟨⟨ι, s, hp⟩⟩

private lemma twoOpenModuleGlueSheaf_generatingSections {X : Scheme.{u}}
    (O : TopCat.Sheaf RingCat.{u} X.toPresheafedSpace) (U V : X.Opens)
    (a : (O.obj.obj (op (U ⊓ V)) : Type u)ˣ)
    (hcomm : ∀ (W : X.Opens) (x y : (O.obj.obj (op W) : Type u)), x * y = y * x)
    (hcover : U ⊔ V = ⊤)
    (t : TwoPatch.{u} → ∀ i, (O.obj.obj (op (twoOpenCover U V i)) : Type u))
    (ht : ∀ (k i j : TwoPatch) {W : X.Opens}
      (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j),
      twoOpenAddTransEquiv O U V a i j hi hj (twoOpenRestriction O hi (t k i)) =
        twoOpenRestriction O hj (t k j))
    (hdiag : ∀ i, t i i = 1) :
    Nonempty (twoOpenModuleGlueSheaf O U V a hcomm).GeneratingSections := by
  refine nonempty_generatingSections_of_unitHom_epi_over O _ (twoOpenCover U V)
    ?_ (fun i => twoOpenModuleSection O U V a hcomm (t i) (ht i)) ?_
  · exact twoOpenCover_coversTop X U V hcover
  · intro i
    have := twoOpenModuleSection_unitHom_isIso O U V a hcomm (t i) (ht i) i (hdiag i)
    infer_instance

private noncomputable def twoOpenStalkProjectionCocone (X : Scheme.{u}) (U V : X.Opens)
    (a : Γ(X, U ⊓ V)ˣ) (i : TwoPatch) (x : X)
    (hx : x ∈ twoOpenCover U V i) :
    CategoryTheory.Limits.Cocone ((OpenNhds.inclusion x).op ⋙
      (twoOpenModuleGlueSheaf X.ringCatSheaf U V a
        (structureSheaf_mul_comm X)).val.presheaf) := by
  refine {
    pt := AddCommGrpCat.of (X.presheaf.stalk x)
    ι := {
      app W := AddCommGrpCat.ofHom {
        toFun s := X.presheaf.germ (W.unop.1 ⊓ twoOpenCover U V i) x ⟨W.unop.2, hx⟩ (s.1 i)
        map_zero' := by
          change X.presheaf.germ (W.unop.1 ⊓ twoOpenCover U V i) x _ 0 = 0
          exact map_zero _
        map_add' _ _ := map_add _ _ _ }
      naturality W Z f := by
        apply AddCommGrpCat.hom_ext
        ext s
        change X.presheaf.germ (Z.unop.1 ⊓ twoOpenCover U V i) x _
            (X.presheaf.map
              (homOfLE (inf_le_inf_right (twoOpenCover U V i) f.unop.le)).op (s.1 i)) = _
        exact X.presheaf.germ_res_apply _ _ _ _ } }

private noncomputable def twoOpenStalkProjection (X : Scheme.{u}) (U V : X.Opens)
    (a : Γ(X, U ⊓ V)ˣ) (i : TwoPatch) (x : X)
    (hx : x ∈ twoOpenCover U V i) :
    TopCat.Presheaf.stalk (C := Ab.{u})
      (twoOpenModuleGlueSheaf X.ringCatSheaf U V a
        (structureSheaf_mul_comm X)).val.presheaf x →+
      X.presheaf.stalk x :=
  (CategoryTheory.Limits.colimit.desc _ (twoOpenStalkProjectionCocone X U V a i x hx)).hom

private lemma twoOpenStalkProjection_germ (X : Scheme.{u}) (U V : X.Opens)
    (a : Γ(X, U ⊓ V)ˣ) (i : TwoPatch) (x : X)
    (hx : x ∈ twoOpenCover U V i) (W : X.Opens) (hxW : x ∈ W)
    (s : (twoOpenModuleGlueSheaf X.ringCatSheaf U V a
      (structureSheaf_mul_comm X)).val.obj (op W)) :
    twoOpenStalkProjection X U V a i x hx
        (TopCat.Presheaf.germ (twoOpenModuleGlueSheaf X.ringCatSheaf U V a
          (structureSheaf_mul_comm X)).val.presheaf W x hxW s) =
      X.presheaf.germ (W ⊓ twoOpenCover U V i) x ⟨hxW, hx⟩ (s.1 i) :=
  congrArg (fun q :
      (twoOpenModuleGlueSheaf X.ringCatSheaf U V a
        (structureSheaf_mul_comm X)).val.presheaf.obj (op W) ⟶
        AddCommGrpCat.of (X.presheaf.stalk x) => q.hom s)
    (CategoryTheory.Limits.colimit.ι_desc (twoOpenStalkProjectionCocone X U V a i x hx)
      (op (⟨W, hxW⟩ : OpenNhds x)))

private noncomputable def twoOpenStalkProjectionLinearMap (X : Scheme.{u}) (U V : X.Opens)
    (a : Γ(X, U ⊓ V)ˣ) (i : TwoPatch) (x : X)
    (hx : x ∈ twoOpenCover U V i) :
    TopCat.Presheaf.stalk (C := Ab.{u})
        (twoOpenModuleGlueSheaf X.ringCatSheaf U V a
          (structureSheaf_mul_comm X)).val.presheaf x →ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x := by
  refine { __ := twoOpenStalkProjection X U V a i x hx
           map_smul' := ?_ }
  intro r m
  change twoOpenStalkProjection X U V a i x hx (r • m) =
    r * twoOpenStalkProjection X U V a i x hx m
  obtain ⟨W, hxW, r, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨Z, hZW, hxZ, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq
    (twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X)).val.presheaf m hxW
  rw [← X.presheaf.germ_res_apply (homOfLE hZW) x hxZ r]
  refine (congrArg (twoOpenStalkProjection X U V a i x hx) (PresheafOfModules.germ_smul
    (R := X.presheaf) (twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X)).val
      x Z hxZ ((X.presheaf.map (homOfLE hZW).op) r) s)).symm.trans
    ((twoOpenStalkProjection_germ X U V a i x hx Z hxZ _).trans ?_)
  change X.presheaf.germ (Z ⊓ twoOpenCover U V i) x _
      (X.presheaf.map (homOfLE (show Z ⊓ twoOpenCover U V i ≤ Z from inf_le_left)).op
        (X.presheaf.map (homOfLE hZW).op r) *
          (show Γ(X, Z ⊓ twoOpenCover U V i) from s.1 i)) = _
  rw [twoOpenStalkProjection_germ X U V a i x hx Z hxZ s]
  rw [map_mul]
  rw [← X.presheaf.germ_res_apply
    (homOfLE (show Z ⊓ twoOpenCover U V i ≤ Z from inf_le_left)) x
    (show x ∈ Z ⊓ twoOpenCover U V i from ⟨hxZ, hx⟩) _]

private lemma twoOpenStalkProjection_section (X : Scheme.{u}) (U V : X.Opens)
    (a : Γ(X, U ⊓ V)ˣ)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (twoOpenCover U V i)) : Type u))
    (ht : ∀ (i j : TwoPatch) {W : X.Opens}
      (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j),
      twoOpenAddTransEquiv X.ringCatSheaf U V a i j hi hj
        (twoOpenRestriction X.ringCatSheaf hi (t i)) =
          twoOpenRestriction X.ringCatSheaf hj (t j))
    (i : TwoPatch) (x : X) (hx : x ∈ twoOpenCover U V i) :
    twoOpenStalkProjectionLinearMap X U V a i x hx
      (TopCat.Presheaf.Γgerm (twoOpenModuleGlueSheaf X.ringCatSheaf U V a
          (structureSheaf_mul_comm X)).val.presheaf x
        ((twoOpenModuleSection X.ringCatSheaf U V a
          (structureSheaf_mul_comm X) t ht).eval (op ⊤))) =
      X.presheaf.germ (twoOpenCover U V i) x hx (t i) := by
  show twoOpenStalkProjection X U V a i x hx
      (TopCat.Presheaf.germ (C := Ab.{u}) (twoOpenModuleGlueSheaf X.ringCatSheaf U V a
          (structureSheaf_mul_comm X)).val.presheaf ⊤ x (Opens.mem_top x)
        ((twoOpenModuleSection X.ringCatSheaf U V a
          (structureSheaf_mul_comm X) t ht).eval (op ⊤))) =
    X.presheaf.germ (twoOpenCover U V i) x hx (t i)
  refine (twoOpenStalkProjection_germ X U V a i x hx ⊤ (Opens.mem_top x) _).trans ?_
  exact X.presheaf.germ_res_apply (homOfLE inf_le_right) x _ _

private lemma twoOpenModuleSection_mem_nonvanishing_of_isUnit (X : Scheme.{u}) (U V : X.Opens)
    (a : Γ(X, U ⊓ V)ˣ)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (twoOpenCover U V i)) : Type u))
    (ht : ∀ (i j : TwoPatch) {W : X.Opens}
      (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j),
      twoOpenAddTransEquiv X.ringCatSheaf U V a i j hi hj
        (twoOpenRestriction X.ringCatSheaf hi (t i)) =
          twoOpenRestriction X.ringCatSheaf hj (t j))
    (i : TwoPatch) (x : X) (hx : x ∈ twoOpenCover U V i)
    (hu : IsUnit (X.presheaf.germ (twoOpenCover U V i) x hx (t i))) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      (twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X))
      (twoOpenModuleSection X.ringCatSheaf U V a (structureSheaf_mul_comm X) t ht) := by
  let M := twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X)
  let p := twoOpenStalkProjectionLinearMap X U V a i x hx
  have hinst := Stacks.SheafOfModules.stalkModule_eq (X := X.toRingedSpace) M.val x
  intro h
  have h' : TopCat.Presheaf.Γgerm (C := Ab.{u}) M.val.presheaf x
      ((twoOpenModuleSection X.ringCatSheaf U V a
        (structureSheaf_mul_comm X) t ht).eval (op ⊤)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x)) :=
    (Stacks.SheafOfModules.mem_smul_top_congr hinst _ _).mp h
  apply (IsLocalRing.notMem_maximalIdeal.mpr hu)
  rw [← twoOpenStalkProjection_section X U V a t ht i x hx]
  show p _ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)
  refine Submodule.smul_induction_on h' ?_ ?_
  · intro r hr m hm
    rw [map_smul]; exact Ideal.mul_mem_right _ _ hr
  · intro r s hr hs
    rw [map_add]; exact add_mem hr hs

/-- The germ at `x` of a global section of a sheaf of modules agrees with the germ of its
restriction to any open set containing `x`. -/
lemma section_germ_eq (X : Scheme.{u}) (M : X.Modules)
    (s : M.sections) (W : X.Opens) (x : X) (hx : x ∈ W) :
    TopCat.Presheaf.Γgerm M.val.presheaf x (s.eval (op ⊤)) =
      TopCat.Presheaf.germ M.val.presheaf W x hx (s.eval (op W)) := by
  rw [← TopCat.Presheaf.Γgerm_res_apply M.val.presheaf (i := homOfLE le_top) x hx]
  exact congrArg (TopCat.Presheaf.germ M.val.presheaf W x hx) (s.property (homOfLE le_top).op)

private lemma twoOpenModuleSection_notMem_nonvanishing_of_mem_maximalIdeal
    (X : Scheme.{u}) (U V : X.Opens) (a : Γ(X, U ⊓ V)ˣ)
    (t : ∀ i, (X.ringCatSheaf.obj.obj (op (twoOpenCover U V i)) : Type u))
    (ht : ∀ (i j : TwoPatch) {W : X.Opens}
      (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j),
      twoOpenAddTransEquiv X.ringCatSheaf U V a i j hi hj
        (twoOpenRestriction X.ringCatSheaf hi (t i)) =
          twoOpenRestriction X.ringCatSheaf hj (t j))
    (i : TwoPatch) (x : X) (hx : x ∈ twoOpenCover U V i)
    (hm : X.presheaf.germ (twoOpenCover U V i) x hx (t i) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    x ∉ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      (twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X))
      (twoOpenModuleSection X.ringCatSheaf U V a (structureSheaf_mul_comm X) t ht) := by
  let M := twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X)
  let s := twoOpenModuleSection X.ringCatSheaf U V a (structureSheaf_mul_comm X) t ht
  let W := twoOpenCover U V i
  let e := twoOpenModuleSectionsLinearEquiv X.ringCatSheaf U V a
    (structureSheaf_mul_comm X) i (le_refl W)
  have hinst := Stacks.SheafOfModules.stalkModule_eq (X := X.toRingedSpace) M.val x
  have hs : s.eval (op W) = t i • e.symm 1 := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply]
    have he := twoOpenModuleSection_trivialization X.ringCatSheaf U V a
      (structureSheaf_mul_comm X) t ht i (le_refl W)
    change e (s.eval (op W)) = (X.ringCatSheaf.obj.map (𝟙 (op W))).hom (t i) at he
    rw [CategoryTheory.Functor.map_id] at he
    simpa only [RingCat.id_apply, smul_eq_mul, mul_one] using he
  intro hn
  apply hn
  refine (Stacks.SheafOfModules.mem_smul_top_congr hinst _ _).mpr ?_
  rw [show (Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm X.toRingedSpace M.val x ⊤
    (Opens.mem_top x)
        (s.eval (op ⊤)) : TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x) =
      TopCat.Presheaf.Γgerm M.val.presheaf x (s.eval (op ⊤)) from rfl,
    section_germ_eq X M s W x hx, hs]
  exact (congrArg (· ∈ _) (PresheafOfModules.germ_smul (R := X.presheaf) M.val x W hx _ _)).mpr
    (Submodule.smul_mem_smul hm Submodule.mem_top)

private lemma exists_invertible_of_inverse_sections (X : Scheme.{u}) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (f : Γ(X, U)) (g : Γ(X, V))
    (hfg : X.presheaf.map (homOfLE inf_le_left).op f *
      X.presheaf.map (homOfLE inf_le_right).op g = 1)
    (hg : ∀ (x : X) (hx : x ∈ V), x ∉ U →
      X.presheaf.germ V x hx g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    ∃ (L : X.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
          L)
      (s : L.sections),
      Nonempty L.GeneratingSections ∧
        U = (letI := hL
             Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s) := by
  let a : Γ(X, U ⊓ V)ˣ := ⟨X.presheaf.map (homOfLE inf_le_left).op f,
    X.presheaf.map (homOfLE inf_le_right).op g, hfg, (mul_comm _ _).trans hfg⟩
  let M := twoOpenModuleGlueSheaf X.ringCatSheaf U V a (structureSheaf_mul_comm X)
  let t : TwoPatch.{u} → ∀ i,
      (X.ringCatSheaf.obj.obj (op (twoOpenCover U V i)) : Type u)
    | .first => twoOpenValues X.ringCatSheaf U V 1 g
    | .second => twoOpenValues X.ringCatSheaf U V f 1
  have ht (k i j : TwoPatch) {W : X.Opens}
      (hi : W ≤ twoOpenCover U V i) (hj : W ≤ twoOpenCover U V j) :
      twoOpenAddTransEquiv X.ringCatSheaf U V a i j hi hj
        (twoOpenRestriction X.ringCatSheaf hi (t k i)) =
          twoOpenRestriction X.ringCatSheaf hj (t k j) := by
    cases k
    · apply twoOpenValues_compatible
      show (X.presheaf.map _).hom 1 = _
      rw [map_one]
      exact hfg.symm
    · apply twoOpenValues_compatible
      show _ = _ * (X.presheaf.map _).hom 1
      rw [map_one, mul_one]
      rfl
  let s := twoOpenModuleSection X.ringCatSheaf U V a (structureSheaf_mul_comm X)
    (t .first) (ht .first)
  let hM := twoOpenModuleGlueSheaf_isInvertible X U V a hcover
  refine ⟨M, hM, s, ?_, ?_⟩
  · exact twoOpenModuleGlueSheaf_generatingSections X.ringCatSheaf U V a
      (structureSheaf_mul_comm X) hcover t ht (by intro i; cases i <;> rfl)
  · ext x
    show x ∈ U ↔ x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) M s
    constructor
    · intro hx
      apply twoOpenModuleSection_mem_nonvanishing_of_isUnit X U V a
        (t .first) (ht .first) .first x hx
      show IsUnit ((X.presheaf.germ U x hx).hom 1)
      rw [map_one]
      exact isUnit_one
    · intro hx
      by_contra hxu
      have hxv : x ∈ V := by
        have h : x ∈ U ⊔ V := by rw [hcover]; trivial
        exact h.resolve_left hxu
      exact twoOpenModuleSection_notMem_nonvanishing_of_mem_maximalIdeal
        X U V a (t .first) (ht .first) .second x hxv (hg x hxv hxu) hx

/-- A nonzero ideal of a subring of the fraction field of `B` has nonzero preimage in `B`,
along any ring map `B → T` agreeing with the inclusion of `B` into the fraction field. -/
lemma comap_ne_bot_of_fractionRing {B K : Type u} [CommRing B] [Field K]
    [IsDomain B] [Algebra B K] [IsFractionRing B K]
    (T : Subring K) (β : B →+* T) (hβ : ∀ b, (β b : K) = algebraMap B K b)
    (p : Ideal T) (hp : p ≠ ⊥) : p.comap β ≠ ⊥ := by
  obtain ⟨t, htp, ht⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective B (t : K)
  have hd0 : algebraMap B K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hb0 : b ≠ 0 := by
    intro hb
    rw [hb, map_zero, zero_div] at hbd
    exact ht (Subtype.ext hbd.symm)
  have heq : β b = t * β d := by
    apply Subtype.ext
    show (β b : K) = (t : K) * (β d : K)
    rw [hβ, hβ]
    exact (div_eq_iff hd0).mp hbd
  intro hbot
  apply hb0
  have hb : b ∈ p.comap β := by
    show β b ∈ p
    rw [heq]
    exact p.mul_mem_right _ htp
  simpa [hbot] using hb

/-- A subring of the function field of an integral separated scheme that receives both the
sections over a nonempty affine open `U` and the stalk at a one-dimensional point outside `U`
is a field. -/
lemma isField_subring_of_contains_sections_and_stalk
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (x : X) (hx : x ∉ U) (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (T : Subring X.functionField)
    (α : Γ(X, U) →+* T) (β : X.presheaf.stalk x →+* T)
    (hα : ∀ a, (α a : X.functionField) = X.germToFunctionField U a)
    (hβ : ∀ b, (β b : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField b) :
    IsField T := by
  have hmor : Spec.map (CommRingCat.ofHom α) ≫ hU.fromSpec =
      Spec.map (CommRingCat.ofHom β) ≫ X.fromSpecStalk x := by
    let j := Spec.map (CommRingCat.ofHom T.subtype)
    have : IsDominant j := by
      constructor
      apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical T.subtype).mpr
      intro t ht
      have ht0 : t = 0 := Subtype.ext ht
      simpa only [ht0] using (Ideal.zero_mem (nilradical T))
    apply ext_of_isDominant j
    dsimp [j]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
    have ha : CommRingCat.ofHom α ≫ CommRingCat.ofHom T.subtype =
        X.germToFunctionField U := by
      ext a
      exact hα a
    have hb : CommRingCat.ofHom β ≫ CommRingCat.ofHom T.subtype =
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
      ext b
      exact hβ b
    rw [ha, hb, X.SpecMap_stalkSpecializes_fromSpecStalk]
    exact hU.fromSpecStalk_eq_fromSpecStalk _
  by_contra hfield
  obtain ⟨p, hp, hpmax⟩ := Ring.exists_maximal_of_not_isField hfield
  let := hpmax
  let : Ring.KrullDimLE 1 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr (by simp [hdim])
  have hpB : (p.comap β).IsMaximal :=
    (Ideal.comap_isPrime β p).isMaximal_of_ne_bot (comap_ne_bot_of_fractionRing T β hβ p hp)
  have hpoint : (Spec.map (CommRingCat.ofHom β)) (⟨p, hpmax.isPrime⟩ : PrimeSpectrum T) =
      IsLocalRing.closedPoint (X.presheaf.stalk x) :=
    PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hpB)
  have heq : hU.fromSpec
        ((Spec.map (CommRingCat.ofHom α)) (⟨p, hpmax.isPrime⟩ : PrimeSpectrum T)) =
      X.fromSpecStalk x
        ((Spec.map (CommRingCat.ofHom β)) (⟨p, hpmax.isPrime⟩ : PrimeSpectrum T)) :=
    congrArg (fun f : Spec (.of T) ⟶ X => f (⟨p, hpmax.isPrime⟩ : PrimeSpectrum T)) hmor
  rw [hpoint] at heq
  have heq := heq.trans (Scheme.fromSpecStalk_closedPoint (X := X) (x := x))
  apply hx
  rw [← heq]
  exact hU.range_fromSpec.subset ⟨_, rfl⟩

/-- A subring of the fraction field of `B` that receives `B` and happens to be a field is the
whole fraction field. -/
lemma subring_subtype_surjective_of_isField {B K : Type u} [CommRing B] [Field K]
    [IsDomain B] [Algebra B K] [IsFractionRing B K]
    (T : Subring K) (β : B →+* T) (hβ : ∀ b, (β b : K) = algebraMap B K b)
    (hT : IsField T) : Function.Surjective T.subtype := by
  let := hT.toField
  intro z
  obtain ⟨b, d, hd, hbd⟩ := IsFractionRing.div_surjective B z
  refine ⟨β b / β d, ?_⟩
  rw [map_div₀]
  show (β b : K) / (β d : K) = z
  rw [hβ, hβ]
  exact hbd

/-- The map to the function field induced by the inclusions of the sections over a nonempty
affine open `U` and of the stalk at a one-dimensional point outside `U` is surjective on their
tensor product. -/
lemma tensorProduct_stalk_surjective (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (x : X) (hx : x ∉ U) (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (A B : Subring X.functionField)
    (eA : Γ(X, U) ≃+* A) (eB : X.presheaf.stalk x ≃+* B)
    (heA : ∀ a, (eA a : X.functionField) = X.germToFunctionField U a)
    (heB : ∀ b, (eB b : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField b) :
    Function.Surjective (Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
      B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)) := by
  let ψ := Algebra.TensorProduct.lift (B := B) A.subtype.toIntAlgHom
    B.subtype.toIntAlgHom (fun _ _ ↦ Commute.all _ _)
  let T := ψ.toRingHom.range
  let α : Γ(X, U) →+* T := ψ.toRingHom.rangeRestrict.comp
    (Algebra.TensorProduct.includeLeftRingHom.comp eA.toRingHom)
  let β : X.presheaf.stalk x →+* T := ψ.toRingHom.rangeRestrict.comp
    (Algebra.TensorProduct.includeRight.toRingHom.comp eB.toRingHom)
  have hα (a : Γ(X, U)) : (α a : X.functionField) = X.germToFunctionField U a := by
    show ψ (eA a ⊗ₜ[ℤ] (1 : B)) = _
    simpa [ψ] using heA a
  have hβ (b : X.presheaf.stalk x) : (β b : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField b := by
    show ψ ((1 : A) ⊗ₜ[ℤ] eB b) = _
    simpa [ψ] using heB b
  have hT := isField_subring_of_contains_sections_and_stalk X U hU x hx hdim T α β hα hβ
  intro z; obtain ⟨t, ht⟩ := subring_subtype_surjective_of_isField T β hβ hT z
  obtain ⟨q, hq⟩ := t.property
  exact ⟨q, hq.trans ht⟩

/-- An integral separated scheme carries a nonzero section over a nonempty affine open `U` whose
inverse in the function field has, at each of finitely many one-dimensional points outside `U`,
a germ in the maximal ideal. -/
lemma exists_ne_zero_inverse_germs (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    {ι : Type u} [Finite ι] (x : ι → X) (hx : ∀ i, x i ∉ U)
    (hn : ∀ i, IsNoetherianRing (X.presheaf.stalk (x i)))
    (hd : ∀ i, ringKrullDim (X.presheaf.stalk (x i)) = 1) :
    ∃ f : Γ(X, U), f ≠ 0 ∧ ∀ i, ∃ g : X.presheaf.stalk (x i),
      algebraMap (X.presheaf.stalk (x i)) X.functionField g =
        (X.germToFunctionField U f)⁻¹ ∧
      g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (x i)) := by
  let A := (X.germToFunctionField U).hom.range
  let B (i : ι) := (algebraMap (X.presheaf.stalk (x i)) X.functionField).range
  let eA : Γ(X, U) ≃+* A := RingEquiv.ofBijective (X.germToFunctionField U).hom.rangeRestrict
    ⟨fun _ _ h => X.germToFunctionField_injective U (congrArg Subtype.val h),
      fun a => by obtain ⟨b, hb⟩ := a.property; exact ⟨b, Subtype.ext hb⟩⟩
  let eB (i : ι) : X.presheaf.stalk (x i) ≃+* B i :=
    RingEquiv.ofBijective (algebraMap (X.presheaf.stalk (x i)) X.functionField).rangeRestrict
      ⟨fun _ _ h => IsFractionRing.injective _ _ (congrArg Subtype.val h),
        fun b => by obtain ⟨c, hc⟩ := b.property; exact ⟨c, Subtype.ext hc⟩⟩
  have heA (a : Γ(X, U)) : (eA a : X.functionField) = X.germToFunctionField U a := rfl
  have heB (i : ι) (b : X.presheaf.stalk (x i)) :
      (eB i b : X.functionField) =
        algebraMap (X.presheaf.stalk (x i)) X.functionField b := rfl
  have heA' (a : A) : X.germToFunctionField U (eA.symm a) = (a : X.functionField) := by
    rw [← heA, eA.apply_symm_apply]
  have heB' (i : ι) (b : B i) :
      algebraMap (X.presheaf.stalk (x i)) X.functionField ((eB i).symm b) =
        (b : X.functionField) := by
    rw [← heB, (eB i).apply_symm_apply]
  let : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : IsFractionRing A X.functionField := IsFractionRing.of_ringEquiv_left eA.symm
    (fun a => (heA' a).symm)
  let : ∀ i, IsFractionRing (B i) X.functionField := fun i =>
    IsFractionRing.of_ringEquiv_left (eB i).symm (fun b => (heB' i b).symm)
  let : ∀ i, IsNoetherianRing (X.presheaf.stalk (x i)) := hn
  let : ∀ i, IsNoetherianRing (B i) := fun i => isNoetherianRing_of_ringEquiv _ (eB i)
  let : ∀ i, IsLocalRing (B i) := fun i =>
    IsLocalRing.of_surjective' (eB i).toRingHom (eB i).surjective
  let : ∀ i, Finite (MaximalSpectrum (B i)) := fun i => by
    have hsub : Subsingleton (MaximalSpectrum (B i)) :=
      ⟨fun p q => MaximalSpectrum.ext
        ((IsLocalRing.eq_maximalIdeal p.isMaximal).trans
          (IsLocalRing.eq_maximalIdeal q.isMaximal).symm)⟩
    exact Finite.of_subsingleton
  obtain ⟨f, hf, hg⟩ :=
    Ring.exists_ne_zero_inverse_mem_jacobson_of_tensorProduct_surjective A B
      (fun i => (ringKrullDim_eq_of_ringEquiv (eB i)).symm.trans (hd i))
      (fun i => tensorProduct_stalk_surjective X U hU (x i) (hx i) (hd i) A (B i)
        eA (eB i) heA (heB i))
  refine ⟨eA.symm f, fun h => hf (eA.symm.injective (h.trans (map_zero eA.symm).symm)), ?_⟩
  intro i
  obtain ⟨g, heq, hgm⟩ := hg i
  refine ⟨(eB i).symm g, ?_, ?_⟩
  · rwa [heB', heA']
  · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hgm
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    intro hu
    apply (IsLocalRing.notMem_maximalIdeal.mpr (hu.map (eB i)))
    simpa only [(eB i).apply_symm_apply] using hgm

/-- The generic point of an integral scheme lies in every nonempty open set. -/
lemma genericPoint_mem_of_nonempty (X : Scheme.{u}) [IsIntegral X]
    (W : X.Opens) [Nonempty W] : genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using ‹Nonempty W›)

/-- If the complement of a nonempty affine open `U` of an integral separated scheme is a finite
set of one-dimensional points, then `U` has a complementary open `V` carrying sections inverse
to one another on `U ⊓ V`, the one on `V` vanishing at every point of `V` outside `U`. -/
lemma exists_inverse_sections (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    {ι : Type u} [Finite ι] [Nonempty ι] (x : ι → X) (hx : ∀ i, x i ∉ U)
    (hboundary : ∀ y : X, y ∉ U → ∃ i, x i = y)
    (hn : ∀ i, IsNoetherianRing (X.presheaf.stalk (x i)))
    (hd : ∀ i, ringKrullDim (X.presheaf.stalk (x i)) = 1) :
    ∃ (V : X.Opens) (f : Γ(X, U)) (g : Γ(X, V)), U ⊔ V = ⊤ ∧
      X.presheaf.map (homOfLE inf_le_left).op f *
        X.presheaf.map (homOfLE inf_le_right).op g = 1 ∧
      ∀ (y : X) (hy : y ∈ V), y ∉ U →
        X.presheaf.germ V y hy g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  classical
  obtain ⟨f, hf, hfg⟩ := exists_ne_zero_inverse_germs X U hU x hx hn hd
  choose g hg hm using hfg
  choose V hxV s hs using fun i => X.presheaf.exists_germ_eq (g i)
  let : ∀ i, Nonempty (V i) := fun i => ⟨⟨x i, hxV i⟩⟩
  have hsK (i : ι) : X.germToFunctionField (V i) (s i) = (X.germToFunctionField U f)⁻¹ := by
    rw [← X.algebraMap_germ_eq_germToFunctionField (hxV i), hs i]
    exact hg i
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro i j
    have hη : genericPoint X ∈ V i ⊓ V j :=
      ⟨genericPoint_mem_of_nonempty X (V i), genericPoint_mem_of_nonempty X (V j)⟩
    apply germ_injective_of_isIntegral X (genericPoint X) hη
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact (hsK i).trans (hsK j).symm
  obtain ⟨t, ht, _⟩ := X.sheaf.existsUnique_gluing V s hcompat
  have ht' (i : ι) : X.presheaf.map (homOfLE (le_iSup V i)).op t = s i := ht i
  have hcover : U ⊔ iSup V = ⊤ := by
    apply top_le_iff.mp
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inl hyU
    · obtain ⟨i, rfl⟩ := hboundary y hyU
      exact Or.inr (Opens.mem_iSup.mpr ⟨i, hxV i⟩)
  let i₀ : ι := Classical.choice inferInstance
  have hηV : genericPoint X ∈ iSup V :=
    Opens.mem_iSup.mpr ⟨i₀, genericPoint_mem_of_nonempty X (V i₀)⟩
  have htK : X.presheaf.germ (iSup V) (genericPoint X) hηV t =
      (X.germToFunctionField U f)⁻¹ := by
    have hh := X.presheaf.germ_res_apply (homOfLE (le_iSup V i₀)) (genericPoint X)
      (genericPoint_mem_of_nonempty X (V i₀)) t
    rw [ht' i₀] at hh
    exact hh.symm.trans (hsK i₀)
  refine ⟨iSup V, f, t, hcover, ?_, ?_⟩
  · have hη : genericPoint X ∈ U ⊓ iSup V :=
      ⟨genericPoint_mem_of_nonempty X U, hηV⟩
    apply germ_injective_of_isIntegral X (genericPoint X) hη
    rw [map_mul, map_one, X.presheaf.germ_res_apply (homOfLE inf_le_left) (genericPoint X) hη f,
      X.presheaf.germ_res_apply (homOfLE inf_le_right) (genericPoint X) hη t]
    show X.germToFunctionField U f * X.presheaf.germ (iSup V) (genericPoint X) hηV t = 1
    rw [htK, mul_inv_cancel₀]
    exact fun h => hf (X.germToFunctionField_injective U (h.trans (map_zero _).symm))
  · intro y hy hyU
    obtain ⟨i, rfl⟩ := hboundary y hyU
    have hh := X.presheaf.germ_res_apply (homOfLE (le_iSup V i)) (x i) (hxV i) t
    rw [ht' i, hs i] at hh
    exact hh ▸ hm i

end AlgebraicGeometry.NoetherianDimensionOne

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 09NB.** On an integral separated scheme, a nonempty affine open with
finite complement along which the local rings are Noetherian of dimension one is the
nonvanishing open of a global section of a globally generated invertible module. -/
@[stacks 09NB]
theorem exists_isInvertible_generatingSections_nonvanishingOpen_eq
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) (hU_nonempty : U ≠ ⊥)
    (hfinite : ((U : Set X)ᶜ).Finite)
    (hnoetherian : ∀ x : X, x ∉ U → IsNoetherianRing (X.presheaf.stalk x))
    (hdim : ∀ x : X, x ∉ U → ringKrullDim (X.presheaf.stalk x) = 1) :
    ∃ (L : X.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property
          L)
      (s : L.sections),
      Nonempty L.GeneratingSections ∧
        U = (letI := hL
             Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) L s) := by
  classical
  open NoetherianDimensionOne in
  by_cases htop : U = ⊤
  · subst U
    exact exists_invertible_of_inverse_sections X ⊤ ⊤ (by simp) 1 1
      (by simp) (fun _ _ h => (h trivial).elim)
  let : Nonempty U := Opens.nonempty_coeSort.mpr ((Opens.ne_bot_iff_nonempty U).mp hU_nonempty)
  let ι := (U : Set X)ᶜ
  let : Finite ι := hfinite.to_subtype
  have : Nonempty ι := by
    by_contra h
    exact htop (top_le_iff.mp fun x _ => by_contra fun hxU => h ⟨⟨x, hxU⟩⟩)
  obtain ⟨V, f, g, hcover, hfg, hg⟩ := exists_inverse_sections X U hU
    (fun i : ι => i.1) (fun i => i.2)
    (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
    (fun i => hnoetherian i.1 i.2) (fun i => hdim i.1 i.2)
  exact exists_invertible_of_inverse_sections X U V hcover f g hfg hg

end AlgebraicGeometry

end
