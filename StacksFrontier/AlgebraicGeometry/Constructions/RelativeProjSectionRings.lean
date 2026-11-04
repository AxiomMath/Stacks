module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits

/-!
# The relative `Proj` situation and its graded rings of local sections

Relative `Proj` is glued from the `Proj` of graded rings of local sections. Its input datum is a
scheme `S` together with a quasi-coherent, commutative, nonnegatively graded sheaf of algebras
`𝒜 = ⨁_{n ≥ 0} 𝒜ₙ` over `𝒪_S`. This file fixes that datum and constructs, for every open
`U ⊆ S`, the graded ring

`⨁_{n ≥ 0} 𝒜ₙ(U)`

of homogeneous local sections, together with the canonical map from `𝒪_S(U)` and the
restriction maps along inclusions of opens.

## Main definitions

* `Stacks.RelativeProj.Situation`: a scheme with a quasi-coherent, commutative, nonnegatively
  graded algebra over its structure sheaf.
* `Stacks.RelativeProj.Situation.sectionPieces` and
  `Stacks.RelativeProj.Situation.sectionRing`: the homogeneous local sections over an open and
  their direct sum.
* `Stacks.RelativeProj.Situation.SectionRingStructure`: the graded-ring structure on the
  section rings, the map from the structure sheaf and the restriction maps, with the equations
  characterizing them.
* `Stacks.RelativeProj.Situation.sectionRingStructure`,
  `Stacks.RelativeProj.Situation.sectionRingBaseMap`,
  `Stacks.RelativeProj.Situation.sectionRingRestrict` and
  `Stacks.RelativeProj.Situation.sectionRingGrading`: the chosen such structure and its pieces.

## Main results

* `Stacks.RelativeProj.Situation.sectionRingStructure_exists`: such a structure exists. The
  homogeneous multiplication, the structure-sheaf map and the restriction maps are determined by
  their values on homogeneous sections, and restriction is functorial.

## Implementation notes

The graded algebra is `SheafOfModules.GradedAlgebra` over `S.ringCatSheaf`, the sheaf of rings
of the ringed site of open subsets of `S`. Following the Stacks Project's convention for graded
rings, the algebra is commutative and its negative homogeneous pieces vanish; quasi-coherence is
quasi-coherence of every homogeneous piece. Mathlib's `SheafOfModules.IsQuasicoherent` is stated
for module sheaves in the universe of the base sheaf of rings, so that is the universe the
homogeneous pieces live in.

The section ring is the direct sum of the nonnegative homogeneous section groups, i.e. finitely
supported families, not a product. Its graded-ring structure, structure-sheaf map and
restriction maps are not exposed as bare data but chosen from a single existence statement whose
conclusion lists the equations they satisfy; those equations are what make the choice canonical.

This `Situation` is the global datum of Tag 01NN. It is not `Stacks.RelativeProj.Data` of
`StacksFrontier/AlgebraicGeometry/Blowup/RelativeProjGluing.lean`, which is the *local* gluing
datum — a family of honest graded rings indexed by the affine opens of the base.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum

universe u

namespace Stacks.RelativeProj

/-- **Stacks Project, Tag 01NN.** A scheme equipped with a graded algebra over its structure
sheaf, each of whose homogeneous pieces is quasi-coherent. The algebra is commutative and
concentrated in nonnegative degrees. -/
@[stacks 01NN "the situation datum, on the SheafOfModules.GradedAlgebra substrate",
  ega "II 8.3.1" "partial"]
public structure Situation where
  /-- The base scheme. -/
  base : Scheme.{u}
  /-- The graded algebra over the structure sheaf of the base scheme. -/
  algebra : SheafOfModules.GradedAlgebra base.ringCatSheaf
  /-- Homogeneous multiplication is commutative. -/
  mul_comm (i j : ℤ) (U : (Opens base)ᵒᵖ)
      (a : (algebra.piece i).val.obj U) (b : (algebra.piece j).val.obj U) :
    HEq ((algebra.mul i j).app U a b) ((algebra.mul j i).app U b a)
  /-- Negative homogeneous pieces vanish. -/
  negative_isZero (n : ℤ) (hn : n < 0) : IsZero (algebra.piece n)
  /-- Every homogeneous piece of the graded algebra is quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (algebra.piece n).IsQuasicoherent

namespace Situation

attribute [instance] isQuasicoherent

/-- The homogeneous sections of degree `n` of a relative `Proj` algebra over an open. -/
public abbrev sectionPieces (s : Situation.{u}) (U : s.base.Opens) (n : ℕ) : Type u :=
  (s.algebra.piece (n : ℤ)).val.obj (op U)

/-- The underlying additive group of the graded ring of local sections. -/
public abbrev sectionRing (s : Situation.{u}) (U : s.base.Opens) : Type u :=
  (⨁ n : ℕ, s.sectionPieces U n)

/-- The direct sum of the homogeneous section groups, decomposed by its summands. -/
@[instance_reducible]
public noncomputable def sectionRingDecomposition (s : Situation.{u}) (U : s.base.Opens) :
    DirectSum.Decomposition (fun n : ℕ => (DirectSum.of (s.sectionPieces U) n).range) := by
  let d : s.sectionRing U →+ ⨁ n : ℕ, (DirectSum.of (s.sectionPieces U) n).range :=
    DirectSum.toAddMonoid fun n =>
      (DirectSum.of (fun n => (DirectSum.of (s.sectionPieces U) n).range) n).comp
        (DirectSum.of (s.sectionPieces U) n).rangeRestrict
  refine DirectSum.Decomposition.ofAddHom _ d ?_ ?_
  · apply DirectSum.addHom_ext
    intro n x
    simp [d]
  · apply DirectSum.addHom_ext
    intro n ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := hx
    simp [d]
    rfl

/-- The canonical operations on the graded section rings. The equations fix multiplication, the
structure-sheaf map and restriction on every homogeneous section. -/
public structure SectionRingStructure (s : Situation.{u}) where
  /-- The graded-ring structure on the homogeneous section groups. -/
  gradedRing (U : s.base.Opens) : DirectSum.GCommRing (s.sectionPieces U)
  /-- The product of homogeneous sections is their product in the graded algebra. -/
  mul_homogeneous (U : s.base.Opens) (n m : ℕ)
      (a : s.sectionPieces U n) (b : s.sectionPieces U m) :
    letI := gradedRing U
    HEq (GradedMonoid.GMul.mul a b) ((s.algebra.mul (n : ℤ) (m : ℤ)).app (op U) a b)
  /-- The unit is the unit of the graded algebra. -/
  one_homogeneous (U : s.base.Opens) :
    letI := gradedRing U
    (GradedMonoid.GOne.one : s.sectionPieces U 0) = s.algebra.one.eval (op U)
  /-- The canonical map from the sections of the structure sheaf. -/
  baseMap (U : s.base.Opens) :
    letI := gradedRing U
    s.base.ringCatSheaf.obj.obj (op U) →+* s.sectionRing U
  /-- That map multiplies the unit section by the given function. -/
  baseMap_apply (U : s.base.Opens) (r : s.base.ringCatSheaf.obj.obj (op U)) :
    letI := gradedRing U
    baseMap U r = DirectSum.of (s.sectionPieces U) 0 (r • s.algebra.one.eval (op U))
  /-- Restriction of graded sections along an inclusion of opens. -/
  restrict (U V : s.base.Opens) (h : U ≤ V) :
    letI := gradedRing U
    letI := gradedRing V
    s.sectionRing V →+* s.sectionRing U
  /-- On a homogeneous section, restriction is the restriction in that homogeneous piece. -/
  restrict_of (U V : s.base.Opens) (h : U ≤ V) (n : ℕ) (a : s.sectionPieces V n) :
    letI := gradedRing U
    letI := gradedRing V
    restrict U V h (DirectSum.of (s.sectionPieces V) n a) =
      DirectSum.of (s.sectionPieces U) n
        ((s.algebra.piece (n : ℤ)).val.map (homOfLE h).op a)
  /-- Restriction along the identity is the identity. -/
  restrict_id (U : s.base.Opens) :
    letI := gradedRing U
    restrict U U le_rfl = RingHom.id _
  /-- Restriction is functorial. -/
  restrict_comp (U V W : s.base.Opens) (hUV : U ≤ V) (hVW : V ≤ W) :
    letI := gradedRing U
    letI := gradedRing V
    letI := gradedRing W
    restrict U W (le_trans hUV hVW) = (restrict U V hUV).comp (restrict V W hVW)
  /-- Restriction is compatible with the map from the structure sheaf. -/
  restrict_baseMap (U V : s.base.Opens) (h : U ≤ V)
      (r : s.base.ringCatSheaf.obj.obj (op V)) :
    letI := gradedRing U
    letI := gradedRing V
    restrict U V h (baseMap V r) =
      baseMap U (s.base.ringCatSheaf.obj.map (homOfLE h).op r)

/-- The product of two homogeneous local sections, as a section of the sum degree. -/
private def sectionMul (s : Situation.{u}) (U : s.base.Opens) {n m : ℕ}
    (a : s.sectionPieces U n) (b : s.sectionPieces U m) : s.sectionPieces U (n + m) :=
  cast (by simp [sectionPieces]) ((s.algebra.mul (n : ℤ) (m : ℤ)).app (op U) a b)

/-- The graded-ring structure on the homogeneous local sections over one open. -/
@[instance_reducible] private noncomputable def sectionGCommRing (s : Situation.{u})
    (U : s.base.Opens) : DirectSum.GCommRing (s.sectionPieces U) := by
  letI : GradedMonoid.GOne (s.sectionPieces U) := ⟨s.algebra.one.eval (op U)⟩
  letI : GradedMonoid.GMul (s.sectionPieces U) := ⟨sectionMul s U⟩
  exact {
    mul := sectionMul s U
    mul_zero := by intro n m a; simp [sectionPieces, sectionMul]
    zero_mul := by intro n m b; simp [sectionPieces, sectionMul]
    mul_add := by intro n m a b c; simp [sectionPieces, sectionMul]
    add_mul := by intro n m a b c; simp [sectionPieces, sectionMul]
    one := s.algebra.one.eval (op U)
    one_mul := by
      rintro ⟨n, a⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      apply Sigma.ext (zero_add n)
      simpa [sectionPieces, sectionMul, GradedMonoid.mk, GradedMonoid.GMul.toMul]
        using s.algebra.one_mul (n : ℤ) (op U) a
    mul_one := by
      rintro ⟨n, a⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      apply Sigma.ext (add_zero n)
      simpa [sectionPieces, sectionMul, GradedMonoid.mk, GradedMonoid.GMul.toMul]
        using s.algebra.mul_one (n : ℤ) (op U) a
    mul_assoc := by
      rintro ⟨n, a⟩ ⟨m, b⟩ ⟨k, c⟩
      change GradedMonoid.mk ((n + m) + k)
          (GradedMonoid.GMul.mul (GradedMonoid.GMul.mul a b) c) =
        GradedMonoid.mk (n + (m + k))
          (GradedMonoid.GMul.mul a (GradedMonoid.GMul.mul b c))
      apply Sigma.ext (add_assoc n m k)
      change HEq (sectionMul s U (sectionMul s U a b) c)
        (sectionMul s U a (sectionMul s U b c))
      simpa [sectionPieces, sectionMul]
        using s.algebra.mul_assoc (n : ℤ) (m : ℤ) (k : ℤ) (op U) a b c
    natCast := fun n => n • s.algebra.one.eval (op U)
    natCast_zero := by simp
    natCast_succ := by intro n; simp [AddMonoid.nsmul_succ]
    intCast := fun n => n • s.algebra.one.eval (op U)
    intCast_ofNat := by simp
    intCast_negSucc_ofNat := by simp
    mul_comm := by
      rintro ⟨n, a⟩ ⟨m, b⟩
      change GradedMonoid.mk _ _ = GradedMonoid.mk _ _
      apply Sigma.ext (add_comm n m)
      simpa [sectionPieces, sectionMul, GradedMonoid.mk, GradedMonoid.GMul.toMul]
        using s.mul_comm (n : ℤ) (m : ℤ) (op U) a b }

/-- Restriction of graded local sections, as an additive homomorphism. -/
private noncomputable def sectionRestrictAddHom (s : Situation.{u}) (U V : s.base.Opens)
    (h : U ≤ V) : s.sectionRing V →+ s.sectionRing U :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (s.sectionPieces U) n).comp
      { toFun := fun a => (s.algebra.piece (n : ℤ)).val.map (homOfLE h).op a
        map_zero' := map_zero _
        map_add' := fun a b => map_add _ a b }

section

attribute [local instance] sectionGCommRing

/-- The structure-sheaf map into the graded local sections, through the unit in degree zero. -/
private noncomputable def sectionBaseRingHom (s : Situation.{u}) (U : s.base.Opens) :
    s.base.ringCatSheaf.obj.obj (op U) →+* s.sectionRing U := by
  let e : s.sectionPieces U 0 := s.algebra.one.eval (op U)
  have hone (t : s.base.ringCatSheaf.obj.obj (op U)) :
      (s.algebra.mul 0 0).app (op U) e (t • e) = t • e := by
    simpa [e] using eq_of_heq (s.algebra.one_mul 0 (op U) (t • e))
  have hscalar (r t : s.base.ringCatSheaf.obj.obj (op U)) :
      sectionMul s U (r • e) (t • e) = (r * t) • e := by
    change (s.algebra.mul 0 0).app (op U) (r • e) (t • e) = _
    rw [(s.algebra.mul 0 0).map_smul_left, hone, smul_smul]
  exact
    { toFun := fun r => DirectSum.of (s.sectionPieces U) 0 (r • e)
      map_zero' := by simp
      map_add' := by intro r t; simp [add_smul]
      map_one' := by
        change DirectSum.of (s.sectionPieces U) 0 (1 • e) =
          DirectSum.of (s.sectionPieces U) 0 e
        simp
      map_mul' := by
        intro r t
        rw [DirectSum.of_mul_of]
        change DirectSum.of (s.sectionPieces U) 0 ((r * t) • e) =
          DirectSum.of (s.sectionPieces U) 0 (sectionMul s U (r • e) (t • e))
        congr 1
        exact (hscalar r t).symm }

/-- Restriction of graded local sections along an inclusion of opens, as a ring map. -/
private noncomputable def sectionRestrictRingHom (s : Situation.{u}) (U V : s.base.Opens)
    (h : U ≤ V) : s.sectionRing V →+* s.sectionRing U := by
  let : DirectSum.GSemiring (s.sectionPieces U) := (sectionGCommRing s U).toGRing.toGSemiring
  let : DirectSum.GSemiring (s.sectionPieces V) := (sectionGCommRing s V).toGRing.toGSemiring
  let f := sectionRestrictAddHom s U V h
  exact
    { toFun := f
      map_zero' := f.map_zero
      map_add' := f.map_add
      map_one' := by
        simp only [DirectSum.one_def, f, sectionRestrictAddHom, DirectSum.toAddMonoid_of,
          AddMonoidHom.comp_apply, AddMonoidHom.coe_mk]
        exact congrArg (DirectSum.of (s.sectionPieces U) 0)
          (s.algebra.one.property (homOfLE h).op)
      map_mul' := by
        rw [f.map_mul_iff]
        refine DirectSum.addHom_ext' (fun n => AddMonoidHom.ext (fun a => ?_))
        refine DirectSum.addHom_ext' (fun m => AddMonoidHom.ext (fun b => ?_))
        change f (DirectSum.of (s.sectionPieces V) n a *
            DirectSum.of (s.sectionPieces V) m b) =
          f (DirectSum.of (s.sectionPieces V) n a) *
            f (DirectSum.of (s.sectionPieces V) m b)
        simp only [f, sectionRestrictAddHom, DirectSum.toAddMonoid_of,
          AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, DirectSum.of_mul_of]
        apply congrArg (DirectSum.of (s.sectionPieces U) (n + m))
        change (s.algebra.piece ((n + m : ℕ) : ℤ)).val.map (homOfLE h).op
            (sectionMul s V a b) =
          sectionMul s U
            ((s.algebra.piece (n : ℤ)).val.map (homOfLE h).op a)
            ((s.algebra.piece (m : ℤ)).val.map (homOfLE h).op b)
        simpa [sectionPieces, sectionMul] using
          ((s.algebra.mul (n : ℤ) (m : ℤ)).naturality (homOfLE h).op a b) }

/-- Restriction of graded local sections is compatible with the structure-sheaf maps. -/
private lemma sectionRestrictRingHom_sectionBaseRingHom (s : Situation.{u})
    (U V : s.base.Opens) (h : U ≤ V) (r : s.base.ringCatSheaf.obj.obj (op V)) :
    sectionRestrictRingHom s U V h (sectionBaseRingHom s V r) =
      sectionBaseRingHom s U (s.base.ringCatSheaf.obj.map (homOfLE h).op r) := by
  change sectionRestrictAddHom s U V h
      (DirectSum.of (s.sectionPieces V) 0 (r • s.algebra.one.eval (op V))) =
    DirectSum.of (s.sectionPieces U) 0
      ((s.base.ringCatSheaf.obj.map (homOfLE h).op r) • s.algebra.one.eval (op U))
  simp only [sectionRestrictAddHom, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply,
    AddMonoidHom.coe_mk]
  apply congrArg (DirectSum.of (s.sectionPieces U) 0)
  change (s.algebra.piece (0 : ℤ)).val.map (homOfLE h).op
      (r • s.algebra.one.eval (op V)) =
    (s.base.ringCatSheaf.obj.map (homOfLE h).op r) • s.algebra.one.eval (op U)
  have hone : (s.algebra.piece (0 : ℤ)).val.map (homOfLE h).op
      (s.algebra.one.eval (op V)) = s.algebra.one.eval (op U) :=
    s.algebra.one.property (homOfLE h).op
  have hsmul := (s.algebra.piece 0).val.map_smul (homOfLE h).op r
    (s.algebra.one.eval (op V))
  rw [hone] at hsmul
  convert hsmul using 1
  rfl

/-- **The canonical nonnegatively graded rings of local sections** of a quasi-coherent graded
algebra, with their structure-sheaf maps and restriction maps. -/
@[stacks 01NN "graded rings of local sections"]
public theorem sectionRingStructure_exists (s : Situation.{u}) :
    Nonempty (s.SectionRingStructure) := by
  classical
  refine ⟨{
    gradedRing := sectionGCommRing s
    mul_homogeneous := fun _ _ _ _ _ => HEq.rfl
    one_homogeneous := fun _ => rfl
    baseMap := sectionBaseRingHom s
    baseMap_apply := fun _ _ => rfl
    restrict := sectionRestrictRingHom s
    restrict_of := by
      intro U V h n a
      change sectionRestrictAddHom s U V h (DirectSum.of (s.sectionPieces V) n a) =
        DirectSum.of (s.sectionPieces U) n
          ((s.algebra.piece (n : ℤ)).val.map (homOfLE h).op a)
      simp only [sectionRestrictAddHom, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply,
        AddMonoidHom.coe_mk]
      rfl
    restrict_id := by
      intro U
      let : DirectSum.GSemiring (s.sectionPieces U) := (sectionGCommRing s U).toGRing.toGSemiring
      apply DirectSum.ringHom_ext
      intro n a
      change sectionRestrictAddHom s U U le_rfl (DirectSum.of (s.sectionPieces U) n a) =
        DirectSum.of (s.sectionPieces U) n a
      simp [sectionRestrictAddHom]
    restrict_comp := by
      intro U V W hUV hVW
      let : DirectSum.GSemiring (s.sectionPieces U) := (sectionGCommRing s U).toGRing.toGSemiring
      let : DirectSum.GSemiring (s.sectionPieces V) := (sectionGCommRing s V).toGRing.toGSemiring
      let : DirectSum.GSemiring (s.sectionPieces W) := (sectionGCommRing s W).toGRing.toGSemiring
      apply DirectSum.ringHom_ext
      intro n a
      change sectionRestrictAddHom s U W _ (DirectSum.of (s.sectionPieces W) n a) =
        sectionRestrictAddHom s U V hUV
          (sectionRestrictAddHom s V W hVW (DirectSum.of (s.sectionPieces W) n a))
      simp only [sectionRestrictAddHom, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply,
        AddMonoidHom.coe_mk]
      apply congrArg (DirectSum.of (s.sectionPieces U) n)
      change (s.algebra.piece (n : ℤ)).val.map (homOfLE (le_trans hUV hVW)).op a =
        (s.algebra.piece (n : ℤ)).val.map (homOfLE hUV).op
          ((s.algebra.piece (n : ℤ)).val.map (homOfLE hVW).op a)
      rw [show (homOfLE (le_trans hUV hVW)).op = (homOfLE hVW).op ≫ (homOfLE hUV).op from
        Subsingleton.elim _ _, PresheafOfModules.map_comp_apply]
    restrict_baseMap := sectionRestrictRingHom_sectionBaseRingHom s }⟩

end

/-- The section-ring operations selected by their homogeneous formulas. -/
public noncomputable def sectionRingStructure (s : Situation.{u}) : s.SectionRingStructure :=
  Classical.choice (sectionRingStructure_exists s)

/-- The graded commutative ring structure on the homogeneous sections over `U`, taken from
`sectionRingStructure`. -/
public noncomputable instance sectionRingGradedRing (s : Situation.{u}) (U : s.base.Opens) :
    DirectSum.GCommRing (s.sectionPieces U) :=
  (sectionRingStructure s).gradedRing U

/-- The canonical map from the structure-sheaf sections to the graded section ring. -/
public noncomputable def sectionRingBaseMap (s : Situation.{u}) (U : s.base.Opens) :
    s.base.ringCatSheaf.obj.obj (op U) →+* s.sectionRing U :=
  (sectionRingStructure s).baseMap U

/-- Restriction of graded sections along an inclusion of opens. -/
public noncomputable def sectionRingRestrict (s : Situation.{u}) (U V : s.base.Opens)
    (h : U ≤ V) : s.sectionRing V →+* s.sectionRing U :=
  (sectionRingStructure s).restrict U V h

/-- The degree-`n` homogeneous component of a section ring. -/
public noncomputable def sectionRingGrading (s : Situation.{u}) (U : s.base.Opens) (n : ℕ) :
    AddSubgroup (s.sectionRing U) :=
  (DirectSum.of (s.sectionPieces U) n).range

/-- The section ring is internally graded by its homogeneous summands. -/
public noncomputable instance sectionRingGradingGradedRing (s : Situation.{u})
    (U : s.base.Opens) : GradedRing (s.sectionRingGrading U) where
  toDecomposition := sectionRingDecomposition s U
  one_mem := ⟨_, (DirectSum.one_def _).symm⟩
  mul_mem := by
    rintro n m a b ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨_, (DirectSum.of_mul_of (A := s.sectionPieces U) a b).symm⟩

end Situation

end Stacks.RelativeProj

end
