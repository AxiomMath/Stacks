module

public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebraTangentSpace
public import StacksFrontier.Deformation.Examples.Linear.SquareZeroBaseFst
public import StacksFrontier.RingTheory.GradedAlgebra.RecordBaseChange
public import StacksFrontier.RingTheory.GradedAlgebra.RecordInjective
public import StacksFrontier.Deformation.LiftsOfObjects.Action.Difference

/-!
# The tangent space of the deformations of a graded algebra is finite-dimensional

Let `P` be a graded `k`-algebra, finite-dimensional in each degree, with a weighted graded
presentation `k[X_1, …, X_n]/(F_1, …, F_r)`. Step (vii) of the proof of Stacks 0DVZ attaches to
every lift of `P` over a square-zero base `k[V]` an element of `W ⊗[k] V`, where
`W = Coker(gradedJacobian)`; the algebra of that construction is
`StacksFrontier/RingTheory/GradedAlgebra/SquareZeroRecord.lean` and the files around it. This file
performs the categorical half: it attaches the element to an *object of the deformation
category* and descends it to isomorphism classes, which is the map `t` the finiteness criterion
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` asks for.

The passage is not formal. An object of the fibre of the deformation category over `k[V]` is a
graded algebra over a base which is only *equal* to `k[V]`, and the type in which its record
lives cannot be written down before that equality is substituted: `Algebra k ↑(X.base)` is not
synthesizable for a general object of `𝒞_Λ`, and indeed no object of `𝒞_Λ` other than a
square-zero extension carries a `k`-algebra structure at all. So the record of a fibre object is
introduced as a *relation* whose algebra data is existentially quantified
(`Deformation.Examples.ProjectiveGradedAlgebra.IsFiberRecord`), not as a function of the object.

## Main definitions

* `Deformation.Examples.ProjectiveGradedAlgebra.IsFiberRecord`: `ω` is the record of a fibre
  object of the deformation category over `k[V]`.
* `Deformation.Examples.ProjectiveGradedAlgebra.tangentRecord`: the map `t` of the proof of
  Stacks 0DVZ, on isomorphism classes.

## Main results

* `…ProjectiveGradedAlgebra.exists_isFiberRecord`: every object of the fibre has a record.
* `…ProjectiveGradedAlgebra.isFiberRecord_eq_of_nonempty_iso`: isomorphic objects of the fibre
  have the same record.
* `…ProjectiveGradedAlgebra.exists_classRecord`: the record descends to isomorphism classes.
* `…ProjectiveGradedAlgebra.isFiberRecord_tangentRecord`: every representative of a class
  records `tangentRecord` of that class.
* `…ProjectiveGradedAlgebra.classOf_eq_of_algEquiv`: two lifts related by an algebra equivalence
  over `P` have the same class.
* `…ProjectiveGradedAlgebra.injective_tangentRecord`: the record determines the class.
* `…ProjectiveGradedAlgebra.isFiberRecord_eq_lTensor_of_isHomLift`: the record is natural in the
  test module.
* `…ProjectiveGradedAlgebra.finiteDimensional_tangentSpace`: **the tangent-space half of
  Stacks 0DVZ**, which those three assemble into through
  `finiteDimensional_tangentSpace_of_gradedJacobian_natural_injection`.

## Implementation notes

`Module kᵐᵒᵖ V` and `IsCentralScalar k V` are installed as `local instance`s, as
`StacksFrontier/Deformation/TangentSpace/Functor.lean` and the two sibling files of Stacks 0DVQ and
0DVZ already do: they are what makes `TrivSqZeroExt k V` a commutative ring, and the square-zero
extension functor is built in their presence.

`IsFiberRecord` spells out the characterisation of the record rather than referring to a chosen
witness, because that characterisation is verbatim the hypothesis `hw` of
`GradedAlgebra.squareZeroRecord_eq_of_algEquiv`,
`GradedAlgebra.squareZeroRecord_eq_lTensor_of_ringHom` and
`GradedAlgebra.exists_algEquiv_of_squareZeroRecord_eq`, which are the three theorems the map `t`
has to be fed to.

Only the last declaration is tagged: everything before it is step (vii) of 0DVZ's *proof*, and
Stacks does not tag the steps of a proof.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public noncomputable section

open CategoryTheory Deformation Deformation.Examples MvPolynomial TensorProduct

namespace Deformation.Examples.ProjectiveGradedAlgebra

universe u w m

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type (max w m)) [CommRing P] [Algebra k P]
  (grading : ℕ → Submodule k P) [GradedAlgebra grading]
  [∀ d, Module.Finite k (grading d)]

attribute [local instance] squareZeroBaseModuleMulOpposite
  squareZeroBaseIsCentralScalar

/-- The square-zero base object `k[V]`. -/
noncomputable abbrev szBase (V : FGModuleCat.{w} k) : ArtinianLocalAlgCat.{u, w, w} Λ k :=
  (artinianSquareZeroExtensionFunctor Λ k).obj V

/-- The base functor of the deformation category of a graded algebra. -/
noncomputable abbrev baseFunctor : Over (specialFiber (Λ := Λ) P grading) ⥤
    ArtinianLocalAlgCat.{u, w, w} Λ k :=
  objectsOverFunctor
    (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
    (specialFiber (Λ := Λ) P grading)

section Lift

variable (V : FGModuleCat.{w} k) (C : Type (max w m)) [CommRing C]
  [alg : Algebra (TrivSqZeroExt k (V : Type w)) C]
  (gr : ℕ → Submodule (TrivSqZeroExt k (V : Type w)) C) [gd : GradedAlgebra gr]
  [fin : ∀ i, Module.Finite (TrivSqZeroExt k (V : Type w)) (gr i)]
  [prj : ∀ i, Module.Projective (TrivSqZeroExt k (V : Type w)) (gr i)]

/-- A graded algebra over the square-zero base `k[V]`, as an object of the ambient category. -/
noncomputable abbrev liftObj : ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k :=
  @ProjectiveGradedAlgebra.mk Λ k _ _ _ (szBase (Λ := Λ) V) C _ alg gr gd fin prj

/-- The same object with every piece of data an explicit argument, for use in statements. -/
noncomputable abbrev liftOf (V' : FGModuleCat.{w} k) (C' : Type (max w m)) (cr : CommRing C')
    (al : Algebra (TrivSqZeroExt k (V' : Type w)) C')
    (gr' : ℕ → Submodule (TrivSqZeroExt k (V' : Type w)) C') (gd' : GradedAlgebra gr')
    (fi : ∀ i, Module.Finite (TrivSqZeroExt k (V' : Type w)) (gr' i))
    (pj : ∀ i, Module.Projective (TrivSqZeroExt k (V' : Type w)) (gr' i)) :
    ProjectiveGradedAlgebra.{u, w, w, max w m} Λ k :=
  @ProjectiveGradedAlgebra.mk Λ k _ _ _ (szBase (Λ := Λ) V') C' cr al gr' gd' fi pj

variable (H : liftObj (Λ := Λ) V C gr ⟶ specialFiber (Λ := Λ) P grading)

/-- The reduction of a lift over `k[V]`, with its underlying type made explicit. -/
noncomputable abbrev liftRed : C →+* P := H.map

/-- The kernel of the base morphism of a lift over `k[V]` is the kernel of the augmentation
`TrivSqZeroExt.fstHom`. -/
theorem ker_base_eq_ker_fstHom : RingHom.ker H.base.hom =
    (RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w)) :
      Ideal (TrivSqZeroExt k (V : Type w))) :=
  Ideal.ext fun a => Iff.intro
    (fun ha => (squareZeroBase_hom_eq_fst V H.base a).symm.trans ha)
    (fun ha => (squareZeroBase_hom_eq_fst V H.base a).trans ha)

/-- The reduction of a lift over `k[V]` is semilinear along `TrivSqZeroExt.fst`. -/
theorem liftRed_smul (a : TrivSqZeroExt k (V : Type w)) (y : C) :
    liftRed P grading V C gr H (a • y) =
      TrivSqZeroExt.fst a • liftRed P grading V C gr H y :=
  (H.map_smul a y).trans (congrArg (· • H.map y) (squareZeroBase_hom_eq_fst V H.base a))

/-- The kernel of the reduction of a lift over `k[V]` is the square-zero ideal times the
whole algebra. -/
theorem liftRed_eq_zero_iff (y : C) : liftRed P grading V C gr H y = 0 ↔
    y ∈ RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w)) •
      (⊤ : Submodule (TrivSqZeroExt k (V : Type w)) C) :=
  ker_base_eq_ker_fstHom P grading V C gr H ▸
    ProjectiveGradedAlgebra.hom_map_eq_zero_iff grading H y

/-- **The comparison map of a lift over `k[V]`.** The square-zero ideal of `k[V]` tensored with
`P` maps to the lift, injectively, by `b ⊗ₜ π y ↦ b • y`. -/
theorem exists_liftTheta :
    ∃ θ : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w))) ⊗[k] P →+ C,
      (∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w)))) (y : C),
          θ (b ⊗ₜ liftRed P grading V C gr H y) = (b : TrivSqZeroExt k (V : Type w)) • y) ∧
        Function.Injective θ := by
  let : ∀ i, Module.Flat (TrivSqZeroExt k (V : Type w)) (gr i) := fun _ =>
    Module.Flat.of_projective
  let : Module.Flat (TrivSqZeroExt k (V : Type w)) C := Module.Flat.of_decomposition gr
  obtain ⟨θ, hθ, hθinj, -⟩ := Ideal.exists_addMonoidHom_tmul_smul
    (TrivSqZeroExt.fstHom k k (V : Type w))
    (liftRed P grading V C gr H).toAddMonoidHom
    (RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w)))
    TrivSqZeroExt.ker_fstHom_mul_self_eq_bot
    TrivSqZeroExt.sub_algebraMap_fst_mem_ker_fstHom
    (liftRed_smul P grading V C gr H)
    (ProjectiveGradedAlgebra.surjective_hom_map grading H)
    (liftRed_eq_zero_iff P grading V C gr H)
  exact ⟨θ, hθ, hθinj⟩

end Lift

section Record

variable {n r : ℕ} {xg : Fin n → P} {dg : Fin n → ℕ} {eg : Fin r → ℕ}
  (hx : ∀ i, xg i ∈ grading (dg i)) (F : Fin r → MvPolynomial (Fin n) k)
  (hF : ∀ j, IsWeightedHomogeneous dg (F j) (eg j)) (hF0 : ∀ j, aeval xg (F j) = 0)

/-- Each graded piece of a lift over `k[V]` is flat, being projective. -/
theorem liftFlat_grading (V : FGModuleCat.{w} k) (C : Type (max w m)) [CommRing C]
    [Algebra (TrivSqZeroExt k (V : Type w)) C]
    (gr : ℕ → Submodule (TrivSqZeroExt k (V : Type w)) C)
    [∀ i, Module.Projective (TrivSqZeroExt k (V : Type w)) (gr i)] (i : ℕ) :
    Module.Flat (TrivSqZeroExt k (V : Type w)) (gr i) := Module.Flat.of_projective

/-- A lift over `k[V]` is flat over its base, being graded by projective pieces. -/
theorem liftFlat (V : FGModuleCat.{w} k) (C : Type (max w m)) [CommRing C]
    [Algebra (TrivSqZeroExt k (V : Type w)) C]
    (gr : ℕ → Submodule (TrivSqZeroExt k (V : Type w)) C) [GradedAlgebra gr]
    [∀ i, Module.Projective (TrivSqZeroExt k (V : Type w)) (gr i)] :
    Module.Flat (TrivSqZeroExt k (V : Type w)) C :=
  let : ∀ i, Module.Flat (TrivSqZeroExt k (V : Type w)) (gr i) := liftFlat_grading V C gr
  Module.Flat.of_decomposition gr

/-- **The record relation of a fibre object of the deformation category over `k[V]`.** An
element `ω` of `W ⊗[k] V` is *the* record of `z` when `z` has a presentation as a graded algebra
`C` over `k[V]` with a reduction to `P` for which `ω` is the element of `W ⊗[k] V` that
`GradedAlgebra.exists_squareZeroRecord` attaches to the lift: the class of the vector
`(g_1, …, g_m)` of obstructions of the lifted relations, read against the comparison map `θ`.

Every object of the fibre has a record (`exists_isFiberRecord`), and the relation is well
defined on isomorphism classes, natural in `V` and injective at `V = k`.

The presentation is quantified existentially rather than extracted by a `cases`/`subst`: the
type in which the record of a fibre object lives cannot be written down before the object's base
equality has been substituted, because `Algebra k ↑(z.1.left.base)` is not synthesizable for a
fibre object, so the relation has to be stated with the algebra data as a bound variable. The
characterisation is spelled out rather than referring to a chosen witness so that it is exactly
the hypothesis `hw` of the three theorems of
`StacksFrontier/RingTheory/GradedAlgebra/RecordBaseChange.lean` and
`StacksFrontier/RingTheory/GradedAlgebra/RecordInjective.lean`. -/
def IsFiberRecord (V : FGModuleCat.{w} k)
    (z : Functor.Fiber (baseFunctor (Λ := Λ) P grading) (szBase (Λ := Λ) V))
    (ω : (((j : Fin r) → ↥(grading (eg j))) ⧸
      LinearMap.range (GradedAlgebra.gradedJacobian grading hx F hF)) ⊗[k] (V : Type w)) :
    Prop :=
  ∃ (C : Type (max w m)) (cr : CommRing C) (al : Algebra (TrivSqZeroExt k (V : Type w)) C)
    (gr : ℕ → Submodule (TrivSqZeroExt k (V : Type w)) C) (gd : GradedAlgebra gr)
    (fi : ∀ i, Module.Finite (TrivSqZeroExt k (V : Type w)) (gr i))
    (pj : ∀ i, Module.Projective (TrivSqZeroExt k (V : Type w)) (gr i))
    (H : liftOf (Λ := Λ) V C cr al gr gd fi pj ⟶ specialFiber (Λ := Λ) P grading)
    (θ : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w))) ⊗[k] P →+ C),
    z = ⟨Over.mk H, rfl⟩ ∧
      (∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w)))) (y : C),
        θ (b ⊗ₜ (H.map y : P)) = (b : TrivSqZeroExt k (V : Type w)) • y) ∧
      Function.Injective θ ∧
      ∀ q : Fin n → C, (∀ i, q i ∈ gr (dg i)) → (∀ i, (H.map (q i) : P) = xg i) →
        ∀ g : (j : Fin r) →
            ↥(RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w))) ⊗[k] ↥(grading (eg j)),
          (∀ j, θ (LinearMap.lTensor _ (grading (eg j)).subtype (g j)) =
            -aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k (V : Type w))) (F j))) →
          GradedAlgebra.gradedJacobianCokernelRecord grading hx F hF
            (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := (V : Type w))).toLinearMap g = ω

include hF0 in
/-- **Every object of the fibre over `k[V]` has a record.** Substituting the base equality
presents the object as a graded algebra over `k[V]` with a surjective reduction to `P` whose
kernel is the square-zero ideal times the whole algebra, which is every hypothesis
`GradedAlgebra.exists_squareZeroRecord` makes. -/
theorem exists_isFiberRecord (V : FGModuleCat.{w} k)
    (z : Functor.Fiber (baseFunctor (Λ := Λ) P grading) (szBase (Λ := Λ) V)) :
    ∃ ω, IsFiberRecord P grading hx F hF V z ω := by
  obtain ⟨Y, hY⟩ := z
  cases Y with
  | mk left right hom =>
    cases right with
    | mk as =>
      cases as
      cases left with
      | @mk base carrier cr al gr' gd' fi pj =>
        change base = szBase (Λ := Λ) V at hY
        subst hY
        let : CommRing carrier := cr
        let : Algebra (TrivSqZeroExt k (V : Type w)) carrier := al
        let grT : ℕ → Submodule (TrivSqZeroExt k (V : Type w)) carrier := gr'
        let : GradedAlgebra grT := gd'
        let : ∀ i, Module.Finite (TrivSqZeroExt k (V : Type w)) (grT i) := fi
        let : ∀ i, Module.Projective (TrivSqZeroExt k (V : Type w)) (grT i) := pj
        let : ∀ i, Module.Flat (TrivSqZeroExt k (V : Type w)) (grT i) :=
          liftFlat_grading V carrier grT
        let : Module.Flat (TrivSqZeroExt k (V : Type w)) carrier := liftFlat V carrier grT
        obtain ⟨θ, hθ, hθinj⟩ := exists_liftTheta P grading V carrier grT hom
        obtain ⟨ω, hω⟩ := GradedAlgebra.exists_squareZeroRecord grading grT
          (liftRed P grading V carrier grT hom) hom.map_mem
          (liftRed_smul P grading V carrier grT hom)
          (ProjectiveGradedAlgebra.surjective_hom_map grading hom)
          (liftRed_eq_zero_iff P grading V carrier grT hom) θ hθ hθinj hx F hF hF0
        exact ⟨ω, carrier, cr, al, grT, gd', fi, pj, hom, θ, rfl, hθ, hθinj, hω⟩

include hF0 in
/-- **The record is well defined on isomorphism classes.** An isomorphism in the fibre over
`k[V]` has base morphism the identity, because its lift of the identity forces it so; the
underlying ring map is then an isomorphism of graded `k[V]`-algebras compatible with the
reductions to `P`, and `GradedAlgebra.squareZeroRecord_eq_of_algEquiv` applies.

This is what lets the record descend through `Deformation.isomorphismClasses`. -/
theorem isFiberRecord_eq_of_nonempty_iso (V : FGModuleCat.{w} k)
    {x y : Functor.Fiber (baseFunctor (Λ := Λ) P grading) (szBase (Λ := Λ) V)}
    (hxy : Nonempty (x ≅ y)) {ω ω' : (((j : Fin r) → ↥(grading (eg j))) ⧸
      LinearMap.range (GradedAlgebra.gradedJacobian grading hx F hF)) ⊗[k] (V : Type w)}
    (hω : IsFiberRecord P grading hx F hF V x ω)
    (hω' : IsFiberRecord P grading hx F hF V y ω') : ω' = ω := by
  obtain ⟨i⟩ := hxy
  obtain ⟨C, cr, al, gr, gd, fi, pj, H, θ, hz, hθ, hθinj, hw⟩ := hω
  obtain ⟨C', cr', al', gr', gd', fi', pj', H', θ', hz', hθ', hθ'inj, hw'⟩ := hω'
  subst hz hz'
  let : ∀ j, Module.Flat (TrivSqZeroExt k (V : Type w)) (gr j) := liftFlat_grading V C gr
  let : ∀ j, Module.Flat (TrivSqZeroExt k (V : Type w)) (gr' j) := liftFlat_grading V C' gr'
  let : Module.Flat (TrivSqZeroExt k (V : Type w)) C := liftFlat V C gr
  let : Module.Flat (TrivSqZeroExt k (V : Type w)) C' := liftFlat V C' gr'
  -- the two underlying morphisms of graded algebras
  let φ : liftOf (Λ := Λ) V C cr al gr gd fi pj ⟶ liftOf (Λ := Λ) V C' cr' al' gr' gd' fi' pj' :=
    i.hom.val.left
  let ψ : liftOf (Λ := Λ) V C' cr' al' gr' gd' fi' pj' ⟶ liftOf (Λ := Λ) V C cr al gr gd fi pj :=
    i.inv.val.left
  have hφψ : ∀ c : C, ψ.map (φ.map c) = c := fun c =>
    congrArg (fun u => u.left.map c) (congrArg Subtype.val i.hom_inv_id)
  have hψφ : ∀ c : C', φ.map (ψ.map c) = c := fun c =>
    congrArg (fun u => u.left.map c) (congrArg Subtype.val i.inv_hom_id)
  have hbase : φ.base = 𝟙 _ := by
    have := i.hom.2
    have h2 := IsHomLift.fac' (baseFunctor (Λ := Λ) P grading)
      (𝟙 (szBase (Λ := Λ) V)) i.hom.val
    simp only [Category.id_comp, eqToHom_refl] at h2
    exact h2
  have hsmul : ∀ (a : TrivSqZeroExt k (V : Type w)) (c : C),
      φ.map (a • c) = a • (φ.map c : C') := fun a c =>
    (φ.map_smul a c).trans (by rw [hbase]; rfl)
  let Φ : C ≃ₐ[TrivSqZeroExt k (V : Type w)] C' :=
    { toFun := φ.map
      invFun := ψ.map
      left_inv := hφψ
      right_inv := hψφ
      map_mul' := φ.map.map_mul
      map_add' := φ.map.map_add
      commutes' := fun a => by
        have h := hsmul a 1
        rwa [map_one φ.map, Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at h }
  have hΦπ : ∀ c : C, (H'.map (Φ c) : P) = (H.map c : P) := fun c =>
    congrArg (fun u => u.map c) (Over.w i.hom.val)
  exact GradedAlgebra.squareZeroRecord_eq_of_algEquiv grading gr gr'
    (liftRed P grading V C gr H) (liftRed P grading V C' gr' H') H.map_mem
    (liftRed_smul P grading V C gr H)
    (ProjectiveGradedAlgebra.surjective_hom_map grading H)
    (liftRed_eq_zero_iff P grading V C gr H) H'.map_mem
    (liftRed_smul P grading V C' gr' H')
    (ProjectiveGradedAlgebra.surjective_hom_map grading H')
    (liftRed_eq_zero_iff P grading V C' gr' H') θ hθ θ' hθ' Φ hΦπ φ.map_mem hx F hF hF0 hw hw'

section Class

/-- The deformation category of a graded algebra is cofibered in groupoids, which is what makes
its functor of fibrewise isomorphism classes available. -/
theorem cofibered_deformationBasedCategory :
    IsCofiberedInGroupoids (deformationBasedCategory (Λ := Λ) P grading).p :=
  (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation.cofibered

variable (V : FGModuleCat.{w} k)

include hF0 in
/-- **The record descends to isomorphism classes.** Any two objects of the fibre over `k[V]`
with the same class in `Deformation.isomorphismClasses` are isomorphic in the fibre, so the
record of one is a record of the other. -/
theorem exists_classRecord
    (z : (tangentSetFunctor (Λ := Λ) P grading).obj V) :
    ∃ ω, ∀ y : Functor.Fiber (deformationBasedCategory (Λ := Λ) P grading).p
        (szBase (Λ := Λ) V),
      classOf (deformationBasedCategory (Λ := Λ) P grading)
          (cofibered_deformationBasedCategory P grading) y = z →
        IsFiberRecord P grading hx F hF V y ω := by
  obtain ⟨x, hxz⟩ := classOf_surjective (deformationBasedCategory (Λ := Λ) P grading)
    (cofibered_deformationBasedCategory P grading) (szBase (Λ := Λ) V) z
  obtain ⟨ω, hω⟩ := exists_isFiberRecord P grading hx F hF hF0 V x
  refine ⟨ω, fun y hy => ?_⟩
  obtain ⟨ω', hω'⟩ := exists_isFiberRecord P grading hx F hF hF0 V y
  have hiso : Nonempty (x ≅ y) :=
    Quotient.exact
      ((classOf_eq (deformationBasedCategory (Λ := Λ) P grading)
          (cofibered_deformationBasedCategory P grading) x).symm.trans
        ((congrArg (cast (isomorphismClasses_obj (deformationBasedCategory (Λ := Λ) P grading)
              (cofibered_deformationBasedCategory P grading) (szBase (Λ := Λ) V)))
            (hxz.trans hy.symm)).trans
          (classOf_eq (deformationBasedCategory (Λ := Λ) P grading)
            (cofibered_deformationBasedCategory P grading) y)))
  exact (isFiberRecord_eq_of_nonempty_iso P grading hx F hF hF0 V hiso hω hω') ▸ hω'

include hF0 in
/-- **The map `t` of the proof of Stacks 0DVZ.** It sends the isomorphism class of a lift of
`P` over `k[V]` to the record of that lift in `W ⊗[k] V`, which `exists_classRecord` shows to be
independent of the representative. -/
noncomputable def tangentRecord (z : (tangentSetFunctor (Λ := Λ) P grading).obj V) :
    (((j : Fin r) → ↥(grading (eg j))) ⧸
      LinearMap.range (GradedAlgebra.gradedJacobian grading hx F hF)) ⊗[k] (V : Type w) :=
  (exists_classRecord P grading hx F hF hF0 V z).choose

include hF0 in
/-- Every representative of a class records `tangentRecord` of that class. -/
theorem isFiberRecord_tangentRecord
    (z : (tangentSetFunctor (Λ := Λ) P grading).obj V)
    (y : Functor.Fiber (deformationBasedCategory (Λ := Λ) P grading).p (szBase (Λ := Λ) V))
    (hy : classOf (deformationBasedCategory (Λ := Λ) P grading)
      (cofibered_deformationBasedCategory P grading) y = z) :
    IsFiberRecord P grading hx F hF V y (tangentRecord P grading hx F hF hF0 V z) :=
  (exists_classRecord P grading hx F hF hF0 V z).choose_spec y hy

end Class

end Record

section Iso

variable (V : FGModuleCat.{w} k) (C : Type (max w m)) [CommRing C]
  [Algebra (TrivSqZeroExt k (V : Type w)) C]
  (gr : ℕ → Submodule (TrivSqZeroExt k (V : Type w)) C) [GradedAlgebra gr]
  [∀ i, Module.Finite (TrivSqZeroExt k (V : Type w)) (gr i)]
  [∀ i, Module.Projective (TrivSqZeroExt k (V : Type w)) (gr i)]
  (C' : Type (max w m)) [CommRing C']
  [Algebra (TrivSqZeroExt k (V : Type w)) C']
  (gr' : ℕ → Submodule (TrivSqZeroExt k (V : Type w)) C') [GradedAlgebra gr']
  [∀ i, Module.Finite (TrivSqZeroExt k (V : Type w)) (gr' i)]
  [∀ i, Module.Projective (TrivSqZeroExt k (V : Type w)) (gr' i)]

/-- **An algebra equivalence over `k[V]` respecting the gradings is a morphism of the ambient
category.** The base morphism is the identity, so the base-change condition is
`IsBaseChange.ofEquiv`. -/
noncomputable def homOfAlgEquiv (Φ : C ≃ₐ[TrivSqZeroExt k (V : Type w)] C')
    (hΦmem : ∀ (e' : ℕ) (c : C), c ∈ gr e' → Φ c ∈ gr' e') :
    liftObj (Λ := Λ) V C gr ⟶ liftObj (Λ := Λ) V C' gr' where
  base := 𝟙 _
  map := (Φ : C →+* C')
  map_smul := by
    have key : ∀ (b : TrivSqZeroExt k (V : Type w)) (y : C), Φ (b • y) = b • Φ y :=
      fun b y => map_smul Φ b y
    exact key
  map_mem := hΦmem
  isBaseChange := IsBaseChange.ofEquiv
    { toFun := Φ
      invFun := Φ.symm
      left_inv := Φ.left_inv
      right_inv := Φ.right_inv
      map_add' := Φ.map_add
      map_smul' := fun a c => map_smul Φ a c }

variable (H : liftObj (Λ := Λ) V C gr ⟶ specialFiber (Λ := Λ) P grading)
  (H' : liftObj (Λ := Λ) V C' gr' ⟶ specialFiber (Λ := Λ) P grading)

/-- **An algebra equivalence over `k[V]` compatible with the reductions to `P` is a morphism of
the deformation category.** The base morphisms of the two reductions agree, both being the
scalar part, so the triangle over the special fibre commutes. -/
noncomputable def overHomOfAlgEquiv (Φ : C ≃ₐ[TrivSqZeroExt k (V : Type w)] C')
    (hΦmem : ∀ (e' : ℕ) (c : C), c ∈ gr e' → Φ c ∈ gr' e')
    (hΦπ : ∀ c : C, (H'.map (Φ c) : P) = (H.map c : P)) :
    (Over.mk H : Over (specialFiber (Λ := Λ) P grading)) ⟶ Over.mk H' :=
  Over.homMk (homOfAlgEquiv V C gr C' gr' Φ hΦmem)
    (by
      refine ProjectiveGradedAlgebra.Hom.ext ?_ (RingHom.ext hΦπ)
      change 𝟙 _ ≫ H'.base = H.base
      rw [Category.id_comp]
      exact ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a =>
        (squareZeroBase_hom_eq_fst V H'.base a).trans
          (squareZeroBase_hom_eq_fst V H.base a).symm))

/-- The morphism of the deformation category underlying an algebra equivalence lies over the
identity of `k[V]`, because its base morphism is the identity by construction. -/
theorem isHomLift_overHomOfAlgEquiv (Φ : C ≃ₐ[TrivSqZeroExt k (V : Type w)] C')
    (hΦmem : ∀ (e' : ℕ) (c : C), c ∈ gr e' → Φ c ∈ gr' e')
    (hΦπ : ∀ c : C, (H'.map (Φ c) : P) = (H.map c : P)) :
    (deformationBasedCategory (Λ := Λ) P grading).p.IsHomLift (𝟙 (szBase (Λ := Λ) V))
      (overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ) := by
  refine IsHomLift.of_fac' (deformationBasedCategory (Λ := Λ) P grading).p
    (𝟙 (szBase (Λ := Λ) V)) _ rfl rfl ?_
  simp only [overHomOfAlgEquiv, homOfAlgEquiv, Category.id_comp]
  rfl

/-- **An algebra equivalence over `k[V]` compatible with the reductions is an isomorphism of the
deformation category.** It lies over the identity, hence is strongly cocartesian over an
isomorphism, hence is itself an isomorphism. -/
noncomputable def overIsoOfAlgEquiv (Φ : C ≃ₐ[TrivSqZeroExt k (V : Type w)] C')
    (hΦmem : ∀ (e' : ℕ) (c : C), c ∈ gr e' → Φ c ∈ gr' e')
    (hΦπ : ∀ c : C, (H'.map (Φ c) : P) = (H.map c : P)) :
    (Over.mk H : Over (specialFiber (Λ := Λ) P grading)) ≅ Over.mk H' :=
  letI := isHomLift_overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids
    (cofibered_deformationBasedCategory P grading) (𝟙 (szBase (Λ := Λ) V))
    (overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ)
    (isHomLift_overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ)
  letI : IsIso (overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ) :=
    Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (p := (deformationBasedCategory (Λ := Λ) P grading).p)
      (f := 𝟙 (szBase (Λ := Λ) V)) _
  asIso (overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ)

/-- The forward direction of `overIsoOfAlgEquiv` is `overHomOfAlgEquiv`. -/
@[simp] theorem overIsoOfAlgEquiv_hom (Φ : C ≃ₐ[TrivSqZeroExt k (V : Type w)] C')
    (hΦmem : ∀ (e' : ℕ) (c : C), c ∈ gr e' → Φ c ∈ gr' e')
    (hΦπ : ∀ c : C, (H'.map (Φ c) : P) = (H.map c : P)) :
    (overIsoOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ).hom =
      overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ := rfl

/-- **Two lifts over `k[V]` related by an algebra equivalence over `P` have the same class.**
The equivalence is an isomorphism of the deformation category over the identity of `k[V]`, so it
induces an isomorphism of the fibre, which is what equality of classes means. -/
theorem classOf_eq_of_algEquiv (Φ : C ≃ₐ[TrivSqZeroExt k (V : Type w)] C')
    (hΦmem : ∀ (e' : ℕ) (c : C), c ∈ gr e' → Φ c ∈ gr' e')
    (hΦπ : ∀ c : C, (H'.map (Φ c) : P) = (H.map c : P)) :
    classOf (deformationBasedCategory (Λ := Λ) P grading)
        (cofibered_deformationBasedCategory P grading) ⟨Over.mk H, rfl⟩ =
      classOf (deformationBasedCategory (Λ := Λ) P grading)
        (cofibered_deformationBasedCategory P grading) ⟨Over.mk H', rfl⟩ := by
  have hL := isHomLift_overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ
  have hLinv : (deformationBasedCategory (Λ := Λ) P grading).p.IsHomLift
      (𝟙 (szBase (Λ := Λ) V))
      (overIsoOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ).inv := by
    have : (deformationBasedCategory (Λ := Λ) P grading).p.IsHomLift
        (Iso.refl (szBase (Λ := Λ) V)).hom
        (overIsoOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ).hom := hL
    exact IsHomLift.inv_lift_inv (p := (deformationBasedCategory (Λ := Λ) P grading).p)
      (Iso.refl (szBase (Λ := Λ) V))
      (overIsoOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ)
  refine classOf_eq_of_isIsomorphic _ _ _ _ ⟨?_⟩
  exact
    { hom := ⟨overHomOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ, hL⟩
      inv := ⟨(overIsoOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ).inv, hLinv⟩
      hom_inv_id := Functor.Fiber.hom_ext
        (overIsoOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ).hom_inv_id
      inv_hom_id := Functor.Fiber.hom_ext
        (overIsoOfAlgEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ).inv_hom_id }

end Iso

section Injective

variable {n r : ℕ} {xg : Fin n → P} {dg : Fin n → ℕ} {eg : Fin r → ℕ}
  (hx : ∀ i, xg i ∈ grading (dg i)) (F : Fin r → MvPolynomial (Fin n) k)
  (hF : ∀ j, IsWeightedHomogeneous dg (F j) (eg j)) (hF0 : ∀ j, aeval xg (F j) = 0)

include hF0 in
/-- **The map `t` is injective, over every square-zero base.** Two lifts of `P` over `k[V]`
with the same record are isomorphic as graded algebras over `P`
(`GradedAlgebra.exists_algEquiv_of_squareZeroRecord_eq`), and such an isomorphism is an
isomorphism of the fibre, so the two classes agree.

At the rank-one module this is the hypothesis `hinj` of
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection`. It is also the place
where the presentation of `P` is used *as a presentation*: that the kernel of the evaluation map
is generated by the `F j` is exactly what makes the recorded vector determine the lift. -/
theorem injective_tangentRecord (V : FGModuleCat.{w} k)
    (hxsurj : Function.Surjective (aeval xg : MvPolynomial (Fin n) k →ₐ[k] P))
    (hxker : ∀ G : MvPolynomial (Fin n) k, aeval xg G = 0 → G ∈ Ideal.span (Set.range F)) :
    Function.Injective
      (tangentRecord (Λ := Λ) P grading hx F hF hF0 V) := by
  intro z z' hzz'
  obtain ⟨x, hxz⟩ := classOf_surjective (deformationBasedCategory (Λ := Λ) P grading)
    (cofibered_deformationBasedCategory P grading) (szBase (Λ := Λ) V) z
  obtain ⟨y, hyz⟩ := classOf_surjective (deformationBasedCategory (Λ := Λ) P grading)
    (cofibered_deformationBasedCategory P grading) (szBase (Λ := Λ) V) z'
  have hX := isFiberRecord_tangentRecord (Λ := Λ) P grading hx F hF hF0
    V z x hxz
  have hY := isFiberRecord_tangentRecord (Λ := Λ) P grading hx F hF hF0
    V z' y hyz
  rw [hzz'] at hX
  obtain ⟨C, cr, al, gr, gd, fi, pj, H, θ, hz1, hθ, hθinj, hw⟩ := hX
  obtain ⟨C', cr', al', gr', gd', fi', pj', H', θ', hz2, hθ', hθ'inj, hw'⟩ := hY
  subst hz1 hz2
  let := liftFlat_grading V C gr
  let := liftFlat_grading V C' gr'
  let := liftFlat V C gr
  let := liftFlat V C' gr'
  obtain ⟨Φ, hΦπ, hΦmem⟩ := GradedAlgebra.exists_algEquiv_of_squareZeroRecord_eq grading gr gr'
    (liftRed P grading V C gr H)
    (liftRed P grading V C' gr' H') H.map_mem
    (liftRed_smul P grading V C gr H)
    (ProjectiveGradedAlgebra.surjective_hom_map grading H)
    (liftRed_eq_zero_iff P grading V C gr H) H'.map_mem
    (liftRed_smul P grading V C' gr' H')
    (ProjectiveGradedAlgebra.surjective_hom_map grading H')
    (liftRed_eq_zero_iff P grading V C' gr' H') θ hθ hθinj θ' hθ' hθ'inj
    hx hxsurj F hF hF0 hxker hw hw'
  rw [← hxz, ← hyz]
  exact classOf_eq_of_algEquiv P grading V C gr C' gr' H H' Φ hΦmem hΦπ

end Injective

section Nat

variable {V V' : FGModuleCat.{w} k}

/-- **The square-zero ideal is functorial in the test module.** The map `k[V] → k[V']` induced by
`f : V → V'` carries the kernel of the augmentation of `k[V]` into that of `k[V']`, and the
identification of those kernels with `V` and `V'` turns it back into `f`. -/
noncomputable def kerMap (f : V ⟶ V') :
    ↥(RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w))) →ₗ[k]
      ↥(RingHom.ker (TrivSqZeroExt.fstHom k k (V' : Type w))) where
  toFun b := ⟨TrivSqZeroExt.map f.hom.hom (b : TrivSqZeroExt k (V : Type w)),
    (TrivSqZeroExt.mem_ker_fstHom_iff _).mpr
      ((TrivSqZeroExt.fst_map _ _).trans ((TrivSqZeroExt.mem_ker_fstHom_iff _).mp b.2))⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' c b := Subtype.ext (by
    change TrivSqZeroExt.map f.hom.hom (c • (b : TrivSqZeroExt k (V : Type w))) =
      c • TrivSqZeroExt.map f.hom.hom (b : TrivSqZeroExt k (V : Type w))
    exact map_smul _ c _)

/-- `kerMap f` restricts to `f` under the identifications of the square-zero ideals with the
test modules. -/
theorem kerFstHomEquiv_comp_kerMap (f : V ⟶ V') :
    (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := (V' : Type w))).toLinearMap ∘ₗ kerMap f =
      f.hom.hom ∘ₗ (TrivSqZeroExt.kerFstHomEquiv (R := k) (M := (V : Type w))).toLinearMap :=
  LinearMap.ext fun _ => TrivSqZeroExt.snd_map _ _

variable {n r : ℕ} {xg : Fin n → P} {dg : Fin n → ℕ} {eg : Fin r → ℕ}
  (hx : ∀ i, xg i ∈ grading (dg i)) (F : Fin r → MvPolynomial (Fin n) k)
  (hF : ∀ j, IsWeightedHomogeneous dg (F j) (eg j)) (hF0 : ∀ j, aeval xg (F j) = 0)

include hF0 in
/-- **The record is natural in the test module, for a morphism of the fibres.** If `a` is a
morphism of the deformation category from a lift over `k[V]` to a lift over `k[V']` lying over
`k[f]`, then the record of the target is the image of the record of the source under `W ⊗ f`.

Nothing of the cokernel is used: `GradedAlgebra.squareZeroRecord_eq_lTensor_of_ringHom` pushes
the record along `kerMap f` on the left factor and changes the identification on the right. -/
theorem isFiberRecord_eq_lTensor_of_isHomLift (f : V ⟶ V')
    (x : Functor.Fiber (deformationBasedCategory (Λ := Λ) P grading).p (szBase (Λ := Λ) V))
    (y : Functor.Fiber (deformationBasedCategory (Λ := Λ) P grading).p (szBase (Λ := Λ) V'))
    (a : x.val ⟶ y.val)
    (ha : (deformationBasedCategory (Λ := Λ) P grading).p.IsHomLift
      ((artinianSquareZeroExtensionFunctor Λ k).map f) a)
    {ω : (((j : Fin r) → ↥(grading (eg j))) ⧸
      LinearMap.range (GradedAlgebra.gradedJacobian grading hx F hF)) ⊗[k] (V : Type w)}
    {ω' : (((j : Fin r) → ↥(grading (eg j))) ⧸
      LinearMap.range (GradedAlgebra.gradedJacobian grading hx F hF)) ⊗[k] (V' : Type w)}
    (hω : IsFiberRecord P grading hx F hF V x ω)
    (hω' : IsFiberRecord P grading hx F hF V' y ω') :
    ω' = LinearMap.lTensor _ f.hom.hom ω := by
  obtain ⟨C, cr, al, gr, gd, fi, pj, H, θ, hz, hθ, hθinj, hw⟩ := hω
  obtain ⟨C', cr', al', gr', gd', fi', pj', H', θ', hz', hθ', hθ'inj, hw'⟩ := hω'
  subst hz hz'
  let := liftFlat_grading V C gr
  let := liftFlat_grading V' C' gr'
  let := liftFlat V C gr
  let := liftFlat V' C' gr'
  -- the ring maps of `a`, with their underlying types made explicit
  let ρ : C →+* C' := a.left.map
  let σ : TrivSqZeroExt k (V : Type w) →+* TrivSqZeroExt k (V' : Type w) :=
    a.left.base.hom.toRingHom
  -- the base morphism of `a` is `k[f]`
  have hbase : a.left.base = (artinianSquareZeroExtensionFunctor Λ k).map f :=
    IsHomLift.fac' (deformationBasedCategory (Λ := Λ) P grading).p
      ((artinianSquareZeroExtensionFunctor Λ k).map f) a
  have hbasehom : ∀ b : TrivSqZeroExt k (V : Type w),
      σ b = TrivSqZeroExt.map f.hom.hom b := fun b =>
    (congrArg (fun g => g.hom b) hbase).trans (squareZeroExtensionArtinian_map_hom f b)
  have hmapsmul : ∀ (b : TrivSqZeroExt k (V : Type w)) (c : C), ρ (b • c) = σ b • ρ c :=
    a.left.map_smul
  -- the comparison maps intertwine
  have hρsmul : ∀ (b : ↥(RingHom.ker (TrivSqZeroExt.fstHom k k (V : Type w)))) (c : C),
      ((kerMap f b : TrivSqZeroExt k (V' : Type w))) • ρ c =
        ρ ((b : TrivSqZeroExt k (V : Type w)) • c) := fun b c =>
    ((hmapsmul b c).trans (congrArg (· • ρ c) (hbasehom b))).symm
  have hρπ : ∀ c : C, (H'.map (ρ c) : P) = (H.map c : P) := fun c =>
    congrArg (fun u => u.map c) (Over.w a)
  have hconst : ∀ b : TrivSqZeroExt k (V : Type w),
      ρ (algebraMap (TrivSqZeroExt k (V : Type w)) C b) =
        algebraMap (TrivSqZeroExt k (V' : Type w)) C'
          (TrivSqZeroExt.map f.hom.hom b) := fun b => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hmapsmul b 1,
      hbasehom b, map_one ρ]
  have hρaeval : ∀ (q : Fin n → C) (j : Fin r),
      ρ (aeval q (MvPolynomial.map (algebraMap k (TrivSqZeroExt k (V : Type w))) (F j))) =
        aeval (fun i => ρ (q i))
          (MvPolynomial.map (algebraMap k (TrivSqZeroExt k (V' : Type w))) (F j)) := by
    intro q j
    have hmaps : MvPolynomial.map (TrivSqZeroExt.map f.hom.hom : TrivSqZeroExt k (V : Type w) →+*
          TrivSqZeroExt k (V' : Type w))
        (MvPolynomial.map (algebraMap k (TrivSqZeroExt k (V : Type w))) (F j)) =
        MvPolynomial.map (algebraMap k (TrivSqZeroExt k (V' : Type w))) (F j) := by
      have hcomp : ((TrivSqZeroExt.map f.hom.hom :
            TrivSqZeroExt k (V : Type w) →+* TrivSqZeroExt k (V' : Type w)).comp
          (algebraMap k (TrivSqZeroExt k (V : Type w)))) =
          algebraMap k (TrivSqZeroExt k (V' : Type w)) :=
        RingHom.ext fun c => (TrivSqZeroExt.map f.hom.hom).commutes c
      rw [MvPolynomial.map_map, hcomp]
    rw [← hmaps]
    exact MvPolynomial.ringHom_aeval_eq_aeval_map
      (TrivSqZeroExt.map f.hom.hom : TrivSqZeroExt k (V : Type w) →+*
        TrivSqZeroExt k (V' : Type w)) ρ hconst (fun _ => rfl) _
  exact GradedAlgebra.squareZeroRecord_eq_lTensor_of_ringHom grading gr gr'
    (liftRed P grading V C gr H) (liftRed P grading V' C' gr' H') H.map_mem
    (liftRed_smul P grading V C gr H)
    (ProjectiveGradedAlgebra.surjective_hom_map grading H)
    (liftRed_eq_zero_iff P grading V C gr H) H'.map_mem
    (liftRed_smul P grading V' C' gr' H')
    (ProjectiveGradedAlgebra.surjective_hom_map grading H')
    (liftRed_eq_zero_iff P grading V' C' gr' H') θ hθ θ' hθ' ρ (kerMap f) hρπ hρsmul
    a.left.map_mem f.hom.hom (kerFstHomEquiv_comp_kerMap f) hx F hF hF0 hρaeval hw hw'

omit [∀ d, Module.Finite k (grading d)] in
/-- **The functor `G` of Stacks 0DVZ acts by tensoring with the test module.** This identifies
the right-hand side of the naturality statement with the one the finiteness criterion wants. -/
theorem gradedJacobianCokernelFunctor_map_apply (f : V ⟶ V')
    (ω : (((j : Fin r) → ↥(grading (eg j))) ⧸
      LinearMap.range (GradedAlgebra.gradedJacobian grading hx F hF)) ⊗[k] (V : Type w)) :
    ((GradedAlgebra.gradedJacobianCokernelFunctor grading hx F hF).map f) ω =
      LinearMap.lTensor _ f.hom.hom ω := rfl

end Nat

section Final

variable [Algebra.FiniteType k P]

/-- **The tangent-space half of Stacks 0DVZ.** The tangent space of the deformation category of
a graded `k`-algebra which is finite-dimensional in each degree and of finite type over `k` is
finite-dimensional.

The proof is Stacks' own: choose a weighted graded presentation of `P`
(`GradedAlgebra.exists_weightedGradedPresentation`), attach to a lift of `P` over `k[V]` the
class in `W ⊗[k] V` of the vector of obstructions of the lifted relations, where `W` is the
cokernel of the graded Jacobian of the presentation
(`Deformation.Examples.ProjectiveGradedAlgebra.tangentRecord`), and feed that map, its
naturality and its injectivity to
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` through
`finiteDimensional_tangentSpace_of_gradedJacobian_natural_injection`. `W` is
finite-dimensional because each graded piece of `P` is. -/
@[stacks 0DVZ "graded_tangent_finite"]
theorem finiteDimensional_tangentSpace :
    letI p := objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)
    letI 𝓕 := BasedCategory.ofFunctor p
    letI hD := isDeformationCategory_deformationCategory (Λ := Λ) P grading
    letI hS2 := Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory 𝓕 hD
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) := ⟨hS2⟩
    letI T := artinianTangentSpace Λ k (isomorphismClasses 𝓕 hD.predeformation.cofibered)
    letI : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
    letI : Module k T := associatedTangentSpaceModuleUnlifted 𝓕
    FiniteDimensional k T := by
  obtain ⟨n, dg, xg, hx, hxsurj, -, r, eg, F, hF, hker⟩ :=
    GradedAlgebra.exists_weightedGradedPresentation grading
  have hF0 : ∀ j, aeval xg (F j) = 0 := fun j =>
    show F j ∈ RingHom.ker (aeval xg : MvPolynomial (Fin n) k →ₐ[k] P) by
      rw [hker]
      exact Ideal.subset_span (Set.mem_range_self j)
  have hxker : ∀ G : MvPolynomial (Fin n) k, aeval xg G = 0 →
      G ∈ Ideal.span (Set.range F) := fun G hG => by
    rw [← hker]
    exact hG
  exact finiteDimensional_tangentSpace_of_gradedJacobian_natural_injection P grading hx F hF
    (fun V z => tangentRecord (Λ := Λ) P grading hx F hF hF0 V z)
    (fun {V V'} f z => by
      obtain ⟨x, hxz⟩ := classOf_surjective (deformationBasedCategory (Λ := Λ) P grading)
        (cofibered_deformationBasedCategory P grading) (szBase (Λ := Λ) V) z
      obtain ⟨y', a, ha⟩ := exists_pushforward (cofibered_deformationBasedCategory P grading)
        ((artinianSquareZeroExtensionFunctor Λ k).map f) x.val x.property
      have hy : (deformationBasedCategory (Λ := Λ) P grading).p.obj y' =
          szBase (Λ := Λ) V' := by
        have := ha
        exact IsHomLift.codomain_eq (deformationBasedCategory (Λ := Λ) P grading).p
          ((artinianSquareZeroExtensionFunctor Λ k).map f) a
      have hmap : (isomorphismClasses (deformationBasedCategory (Λ := Λ) P grading)
          (cofibered_deformationBasedCategory P grading)).map
            ((artinianSquareZeroExtensionFunctor Λ k).map f)
            (classOf (deformationBasedCategory (Λ := Λ) P grading)
              (cofibered_deformationBasedCategory P grading) x) =
          classOf (deformationBasedCategory (Λ := Λ) P grading)
            (cofibered_deformationBasedCategory P grading) ⟨y', hy⟩ := by
        have := ha
        exact map_classOf (deformationBasedCategory (Λ := Λ) P grading)
          (cofibered_deformationBasedCategory P grading) _ x ⟨y', hy⟩ a
      exact (isFiberRecord_eq_lTensor_of_isHomLift P grading hx F hF hF0 f x ⟨y', hy⟩ a ha
        (isFiberRecord_tangentRecord (Λ := Λ) P grading hx F hF hF0 V z x hxz)
        (isFiberRecord_tangentRecord (Λ := Λ) P grading hx F hF hF0 V'
          ((tangentSetFunctor (Λ := Λ) P grading).map f z) ⟨y', hy⟩
          (by rw [← hxz, ← hmap]; rfl))).trans
        (gradedJacobianCokernelFunctor_map_apply P grading hx F hF f _).symm)
    (injective_tangentRecord P grading hx F hF hF0 (FGModuleCat.of k k) hxsurj hxker)

end Final

end Deformation.Examples.ProjectiveGradedAlgebra

end
