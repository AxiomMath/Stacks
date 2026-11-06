module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula

/-!
# Local dimension is preserved by a dominant quasi-finite morphism

Let `f : X ⟶ S` be a dominant morphism of integral schemes which is locally of finite type, with
`S` locally Noetherian and universally catenary. The dimension formula (Stacks 02JU) reads

`dim 𝒪_{X,x} + trdeg_{κ(f x)} κ(x) = dim 𝒪_{S,f x} + trdeg_{R(S)} R(X)`.

Both correction terms vanish as soon as `f` is quasi-finite: quasi-finiteness at a point makes
the residue field extension there a *finite* field extension, hence algebraic, hence of
transcendence degree zero, and applying that at the generic point — where the residue field
extension *is* the extension of function fields, up to the canonical identification of the stalk
at a generic point with its own residue field — kills the second term as well. So the two local
rings have the same Krull dimension.

## Main results

* `AlgebraicGeometry.Scheme.Hom.finite_residueField_of_quasiFiniteAt` — at a point where a
  morphism is quasi-finite, the residue field of the source is a finite extension of the residue
  field of the image.
* `AlgebraicGeometry.isAlgebraic_functionField_of_finite_residueField_genericPoint` — if the
  residue field extension at the generic point is finite, then the induced extension of function
  fields is algebraic.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_trdeg_zero` — the dimension formula with both
  transcendence degrees assumed zero.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite` — the consumer: a dominant
  locally quasi-finite morphism locally of finite type between integral schemes over a
  universally catenary base preserves the Krull dimension of every local ring.

## Implementation notes

The algebra structures in these statements are the canonical ones induced by
`Scheme.Hom.residueFieldMap` and by `AlgebraicGeometry.dominantFunctionFieldMap`, supplied by a
`letI` inside the statement so that hypothesis and conclusion speak about the same instance.

`stalkRingEquivResidueField` identifies a local ring that happens to be a field with its own
residue field. On an integral scheme the stalk at the generic point is the function field, which
is a field, so this is the bridge between `trdeg_{R(S)} R(X)` and the residue-field
transcendence degree at the generic point. Transporting the stalk along the identification of
`f (genericPoint X)` with `genericPoint S` is what makes `residueFieldMap` at the generic point
agree with `dominantFunctionFieldMap`; the naturality square
`Scheme.residue_residueFieldMap` is what supplies that agreement.

Quasi-finiteness enters only through `Module.Finite.of_quasiFinite`: the stalk map at `x` is
quasi-finite, the residue field of the source is a quotient of the source stalk, hence
quasi-finite over the base stalk, hence over the base residue field by
`Algebra.QuasiFinite.of_restrictScalars`, and a quasi-finite algebra over a field is finite.

## References

* [Stacks Project, Tag 01TG](https://stacks.math.columbia.edu/tag/01TG)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A local ring which is a field is its own residue field: the residue map is then injective,
because its kernel is the maximal ideal, which is zero. -/
private noncomputable def stalkRingEquivResidueField (X : Scheme.{u}) (x : X)
    (hfield : IsField (X.presheaf.stalk x)) :
    X.presheaf.stalk x ≃+* X.residueField x := by
  letI : Field (X.presheaf.stalk x) := hfield.toField
  have hker : RingHom.ker (X.residue x).hom = ⊥ := by
    change RingHom.ker
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) = ⊥
    rw [Ideal.mk_ker, IsLocalRing.maximalIdeal_eq_bot]
  exact RingEquiv.ofBijective (X.residue x).hom
    ⟨(RingHom.injective_iff_ker_eq_bot _).mpr hker, X.residue_surjective x⟩

/-- `stalkRingEquivResidueField` is the residue map. -/
private theorem stalkRingEquivResidueField_toRingHom (X : Scheme.{u}) (x : X)
    (hfield : IsField (X.presheaf.stalk x)) :
    (stalkRingEquivResidueField X x hfield).toRingHom = (X.residue x).hom := rfl

/-- On an integral scheme the function field is the residue field of the generic point. -/
private noncomputable def genericStalkRingEquivResidueField (X : Scheme.{u}) [IsIntegral X] :
    X.functionField ≃+* X.residueField (genericPoint X) :=
  stalkRingEquivResidueField X (genericPoint X) (Field.toIsField _)

/-- The ring homomorphism underlying the ring equivalence of an isomorphism in `CommRingCat` is
the underlying map of its forward morphism. Mathlib's `commRingCatIsoToRingEquiv_toRingHom` says
this in the `RingHomClass` coercion spelling; the `RingEquiv.toRingHom` spelling is the one the
`RingEquiv.toRingHom_trans` normal form produces, and `simp` will not cross between them. -/
private theorem commRingCatIso_toRingEquiv_toRingHom {R T : CommRingCat.{u}} (e : R ≅ T) :
    e.commRingCatIsoToRingEquiv.toRingHom = e.hom.hom := rfl

/-- The residue field map at the generic point of the source agrees with
`dominantFunctionFieldMap` under the identifications of the two function fields with the residue
fields of the generic points. -/
private theorem residueFieldMap_genericPoint_comp_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [IsIntegral X] [IsIntegral S] [IsDominant f] :
    letI hgen : f (genericPoint X) = genericPoint S :=
      ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
    letI hfieldS : IsField (S.presheaf.stalk (f (genericPoint X))) := by
      rw [hgen]
      exact Field.toIsField _
    letI eS : S.functionField ≃+* S.residueField (f (genericPoint X)) :=
      (S.presheaf.stalkCongr (Inseparable.of_eq hgen.symm)).commRingCatIsoToRingEquiv.trans
        (stalkRingEquivResidueField S (f (genericPoint X)) hfieldS)
    (f.residueFieldMap (genericPoint X)).hom.comp eS.toRingHom =
      (genericStalkRingEquivResidueField X).toRingHom.comp (dominantFunctionFieldMap f) := by
  dsimp only
  have hnatural := congrArg CommRingCat.Hom.hom
    (Scheme.residue_residueFieldMap f (genericPoint X))
  change (f.residueFieldMap (genericPoint X)).hom.comp
      (S.residue (f (genericPoint X))).hom =
    (X.residue (genericPoint X)).hom.comp
      (f.stalkMap (genericPoint X)).hom at hnatural
  have hgen : f (genericPoint X) = genericPoint S :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
  have hcast : (dominantFunctionFieldMap f) =
      ((S.presheaf.stalkCongr (Inseparable.of_eq hgen.symm)).hom ≫
        f.stalkMap (genericPoint X)).hom := by
    show (hgen ▸ f.stalkMap (genericPoint X)).hom = _
    rw [congrArg CommRingCat.Hom.hom (stalkMap_cast_target f (genericPoint X) hgen)]
  rw [hcast]
  simpa only [RingEquiv.toRingHom_trans, RingEquiv.toRingHom_trans', Scheme.functionField,
    genericStalkRingEquivResidueField, stalkRingEquivResidueField_toRingHom,
    commRingCatIso_toRingEquiv_toRingHom, TopCat.Presheaf.stalkCongr_hom,
    ← CommRingCat.hom_comp, Category.assoc, RingHom.comp_assoc, RingHom.comp_apply] using
      congrArg (fun g => g.comp
        (S.presheaf.stalkCongr (Inseparable.of_eq hgen.symm)).hom.hom) hnatural

/-- At a point where a morphism of schemes is quasi-finite, the residue field of the source is a
finite extension of the residue field of the image: the stalk map is quasi-finite, the residue
field of the source is a quotient of the source stalk, and a quasi-finite algebra over a field is
finite. -/
@[stacks 01TG "the hypothesis is the stalk half `Scheme.Hom.QuasiFiniteAt` of
`AlgebraicGeometry.quasiFiniteAt`, so the finite-type half is not used"]
theorem Scheme.Hom.finite_residueField_of_quasiFiniteAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : f.QuasiFiniteAt x) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (S.residueField (f x)) (X.residueField x) := by
  let R := S.presheaf.stalk (f x)
  let T := X.presheaf.stalk x
  let φ := (f.stalkMap x).hom
  let : Algebra R T := φ.toAlgebra
  have : Algebra.QuasiFinite R T := h
  let K := S.residueField (f x)
  let L := X.residueField x
  let : Algebra T L := (X.residue x).hom.toAlgebra
  let : Algebra R L := ((X.residue x).hom.comp φ).toAlgebra
  let : IsScalarTower R T L := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.QuasiFinite R L :=
    Algebra.QuasiFinite.of_surjective_algHom
      (Ideal.Quotient.mkₐ R (IsLocalRing.maximalIdeal T)) Ideal.Quotient.mk_surjective
  let : Algebra K L := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra R K := (S.residue (f x)).hom.toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    show (f.residueFieldMap x).hom ((S.residue (f x)).hom a) =
      (X.residue x).hom (φ a)
    simpa [CommRingCat.hom_comp, φ] using
      congrArg (fun g : CommRingCat.Hom R L => g.hom a) (Scheme.residue_residueFieldMap (f := f) x))
  have : Algebra.QuasiFinite K L := Algebra.QuasiFinite.of_restrictScalars R K L
  exact Module.Finite.of_quasiFinite

/-- If the residue field extension at the generic point is finite, the induced extension of
function fields is algebraic. -/
theorem isAlgebraic_functionField_of_finite_residueField_genericPoint {X S : Scheme.{u}}
    (f : X ⟶ S) [IsIntegral X] [IsIntegral S] [IsDominant f]
    (hfd : letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra;
      Module.Finite (S.residueField (f (genericPoint X))) (X.residueField (genericPoint X))) :
    letI : Algebra S.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
    Algebra.IsAlgebraic S.functionField X.functionField := by
  let K := S.residueField (f (genericPoint X))
  let L := X.residueField (genericPoint X)
  let : Algebra K L := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  have : Module.Finite K L := hfd
  have hgen : f (genericPoint X) = genericPoint S :=
    ((tfae_isDominant_of_isIntegral f).out 1 2).mp (inferInstance : IsDominant f)
  have hfieldS : IsField (S.presheaf.stalk (f (genericPoint X))) := by
    rw [hgen]
    exact Field.toIsField _
  let eS : S.functionField ≃+* K :=
    (S.presheaf.stalkCongr (Inseparable.of_eq hgen.symm)).commRingCatIsoToRingEquiv.trans
      (stalkRingEquivResidueField S (f (genericPoint X)) hfieldS)
  let : Algebra S.functionField X.functionField := (dominantFunctionFieldMap f).toAlgebra
  exact (Algebra.isAlgebraic_ringHom_iff_of_comp_eq eS (genericStalkRingEquivResidueField X)
    (residueFieldMap_genericPoint_comp_eq f)).mp (Algebra.IsAlgebraic.of_finite K L)

/-- **Stacks 02JU.** When both transcendence degrees in the dimension formula vanish, the local
rings at a point and at its image have the same Krull dimension. -/
theorem ringKrullDim_stalk_eq_of_trdeg_zero {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] [IsIntegral X] [IsIntegral S] [IsDominant f]
    (hS : Scheme.IsUniversallyCatenary S)
    (hres : ∀ x : X, letI := (f.residueFieldMap x).hom.toAlgebra;
      Algebra.trdeg (S.residueField (f x)) (X.residueField x) = 0)
    (hfun : letI := (dominantFunctionFieldMap f).toAlgebra;
      Algebra.trdeg S.functionField X.functionField = 0)
    (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (S.presheaf.stalk (f x)) := by
  let := (dominantFunctionFieldMap f).toAlgebra
  let := (f.residueFieldMap x).hom.toAlgebra
  simpa [hres x, hfun] using localDimension_add_trdeg_eq f hS x

/-- A dominant locally quasi-finite morphism locally of finite type between integral schemes over
a locally Noetherian universally catenary base preserves the Krull dimension of every local ring:
quasi-finiteness makes every residue field extension finite, hence of transcendence degree zero,
and the same at the generic point kills the function-field term of the dimension formula. -/
@[ega "IV 13.2.5" "(iv), special case",
  ega "IV 13.3.4" "special case",
  ega "IV 5.6.5" "special case"]
theorem ringKrullDim_stalk_eq_of_locallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian S]
    [IsIntegral X] [IsIntegral S] [IsDominant f]
    (hS : Scheme.IsUniversallyCatenary S) (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (S.presheaf.stalk (f x)) := by
  refine ringKrullDim_stalk_eq_of_trdeg_zero f hS (fun y => ?_) ?_ x
  · let := (f.residueFieldMap y).hom.toAlgebra
    have := f.finite_residueField_of_quasiFiniteAt y (f.quasiFiniteAt y)
    exact trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)
  · let := (dominantFunctionFieldMap f).toAlgebra
    exact trdeg_eq_zero_iff.mpr (isAlgebraic_functionField_of_finite_residueField_genericPoint f
      (f.finite_residueField_of_quasiFiniteAt _ (f.quasiFiniteAt _)))

end AlgebraicGeometry

end
