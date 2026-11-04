module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Cohomology of the fibres of a proper family

For a proper morphism `f : Y ⟶ T`, a quasi-coherent `𝒪_Y`-module `L` and a point `t` of `T`, the
*fibre cohomology* of `L` at `t` is the cohomology of the pullback of `L` to the fibre
`Y_t = Y ×_T Spec κ(t)`, as a `κ(t)`-vector space.

The point of this file is that it can be computed on any field-valued point lying over `t`: if
`x : Spec K ⟶ T` factors as `Spec K ⟶ Spec κ(t) ⟶ T` and `Z` is *any* fibre product of `f` and
`x`, then `dim_K Hⁿ(Z, L_Z) = dim_{κ(t)} Hⁿ(Y_t, L_t)` ([Stacks, Tag 02KH] for the field extension
`κ(t) ⟶ K`). So the fibre cohomology dimensions are a function on the underlying set of `T`
which is compatible with every base change.

## Main definitions

* `Stacks.FibreCohomology.fibreAt`, `fibreAtProj`, `fibreAtMap`: the canonical fibre.
* `Stacks.FibreCohomology.fibreCohomology`: `Hⁿ(Y_t, L_t)` over `κ(t)`.

## Main results

* `Stacks.FibreCohomology.finrank_eq_of_isPullback`: computation on any field point over `t`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.FibreCohomology

/-- An isomorphism of modules induces an isomorphism of their cohomology over a field. -/
def cohomologyOverFieldMapIso (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {F G : X.Modules} (e : F ≅ G) (n : ℕ) :
    cohomologyOverField k f F n ≅ cohomologyOverField k f G n :=
  (ModuleCat.restrictScalars _).mapIso
    (((_root_.SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).mapIso e)

variable {Y T : Scheme.{u}} (f : Y ⟶ T) (L : Y.Modules) (t : T)

/-- The fibre `Y_t = Y ×_T Spec κ(t)` of `f` over a point. -/
abbrev fibreAt : Scheme.{u} := pullback f (T.fromSpecResidueField t)

/-- The projection of the fibre onto `Y`. -/
abbrev fibreAtMap : fibreAt f t ⟶ Y := pullback.fst _ _

/-- The structure morphism of the fibre. -/
abbrev fibreAtProj : fibreAt f t ⟶ Spec (T.residueField t) := pullback.snd _ _

/-- **The fibre cohomology** `Hⁿ(Y_t, L_t)`, a `κ(t)`-vector space. -/
abbrev fibreCohomology (n : ℕ) : ModuleCat.{u} (T.residueField t) :=
  cohomologyOverField (T.residueField t) (fibreAtProj f t)
    ((Scheme.Modules.pullback (fibreAtMap f t)).obj L) n

/-- The fibre of `f` over `t` is a pullback square. -/
private theorem isPullback_fibreAt :
    IsPullback (fibreAtMap f t) (fibreAtProj f t) f (T.fromSpecResidueField t) :=
  IsPullback.of_hasPullback _ _

variable [IsProper f] [L.IsQuasicoherent]

/-- **Fibre cohomology can be computed on any field point over `t`.** Let `φ : κ(t) ⟶ K` be a
field extension and `Z` a fibre product of `f` with `Spec K ⟶ Spec κ(t) ⟶ T`; let `M` be
isomorphic to the pullback of `L` to `Z`. Then `dim_K Hⁿ(Z, M) = dim_{κ(t)} Hⁿ(Y_t, L_t)`. -/
theorem finrank_eq_of_isPullback {K : Type u} [Field K] (φ : T.residueField t ⟶ CommRingCat.of K)
    {Z : Scheme.{u}} (gZ : Z ⟶ Y) (fZ : Z ⟶ Spec (.of K))
    (hZ : IsPullback gZ fZ f (Spec.map φ ≫ T.fromSpecResidueField t)) (M : Z.Modules)
    (eM : M ≅ (Scheme.Modules.pullback gZ).obj L) (n : ℕ) :
    Module.finrank K (cohomologyOverField K fZ M n) =
      Module.finrank (T.residueField t) (fibreCohomology f L t n) := by
  let : Algebra (T.residueField t) K := φ.hom.toAlgebra
  have hfib := isPullback_fibreAt f t
  let gZ' : Z ⟶ fibreAt f t := hfib.lift gZ (fZ ≫ Spec.map φ) (by
    rw [hZ.w, Category.assoc])
  have hgZ' : gZ' ≫ fibreAtMap f t = gZ := hfib.lift_fst _ _ _
  have hsq : IsPullback gZ' fZ (fibreAtProj f t) (Spec.map φ) :=
    IsPullback.of_right (h₁₂ := fibreAtMap f t) (v₁₃ := f)
      (h₂₂ := T.fromSpecResidueField t) (by rwa [hgZ']) (hfib.lift_snd _ _ _) hfib
  have hsq' : IsPullback gZ' fZ (fibreAtProj f t)
      (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) K))) := hsq
  have hproper : IsProper (fibreAtProj f t) :=
    MorphismProperty.of_isPullback hfib inferInstance
  have h := finrank_cohomologyOverField_baseChange_field (T.residueField t) K gZ' fZ
    (fibreAtProj f t) hsq' ((Scheme.Modules.pullback (fibreAtMap f t)).obj L) n
  rw [← h]
  refine LinearEquiv.finrank_eq (cohomologyOverFieldMapIso K fZ ?_ n).toLinearEquiv
  exact eM ≪≫ (Scheme.Modules.pullbackCongr hgZ'.symm).app L ≪≫
    ((Scheme.Modules.pullbackComp gZ' (fibreAtMap f t)).app L).symm

/-- **Fibre cohomology is compatible with base change.** For a cartesian square
`Y' = Y ×_T S` and `L'` isomorphic to the pullback of `L`, the fibre cohomology of `L'` at a point
`x` of `S` has the same dimension as the fibre cohomology of `L` at the image of `x`. -/
theorem finrank_fibreCohomology_eq_of_isPullback {Y' S : Scheme.{u}} (q : Y' ⟶ Y) (f' : Y' ⟶ S)
    (h : S ⟶ T) (hq : IsPullback q f' f h) (L' : Y'.Modules)
    (eL : L' ≅ (Scheme.Modules.pullback q).obj L) (x : S) (n : ℕ) :
    Module.finrank (S.residueField x) (fibreCohomology f' L' x n) =
      Module.finrank (T.residueField (h x)) (fibreCohomology f L (h x) n) := by
  have hbig := (isPullback_fibreAt f' x).paste_horiz hq
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at hbig
  exact finrank_eq_of_isPullback f L (h x) (h.residueFieldMap x) _ _ hbig _
    ((Scheme.Modules.pullback (fibreAtMap f' x)).mapIso eL ≪≫
      (Scheme.Modules.pullbackComp (fibreAtMap f' x) q).app L) n

end Stacks.FibreCohomology
