module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.UniformizerDifferential
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.Locality
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
public import StacksFrontier.FieldTheory.FrobeniusDegree

/-!
# The degree of the relative Frobenius at the generic point

Let `X` be an integral scheme of finite type over a field `k` of characteristic `p`, smooth over
`k`, and let `d` be its dimension. The residue degree of the relative Frobenius
`F_{X/k} : X ⟶ X^{(p)}` at the generic point divides `p ^ d`.

The residue field `κ` of `X` at the generic point is the function field, and the image of the
residue-field map of `F_{X/k}` there contains the image of `k` and every `p`-th power of `κ`,
because the relative Frobenius composed with the two projections of the Frobenius twist is the
structure morphism and the absolute Frobenius of `X` respectively. The image therefore contains
the compositum `kκᵖ`, over which `κ` has degree `p ^ d`: the extension `κ / k` is formally
smooth because `X` is smooth, and its transcendence degree is the dimension of `X`.

## Main results

* `AlgebraicGeometry.absoluteFrobenius_residueFieldMap_apply` — the residue-field map of the
  absolute Frobenius raises to the `p`-th power.
* `AlgebraicGeometry.residueDegree_eq_finrank_fieldRange` — the residue degree of a morphism is
  the degree of the residue field over the image of its residue-field map.
* `AlgebraicGeometry.compositumFrobenius_le_fieldRange_residueFieldMap_relativeFrobenius` — the
  compositum of the base field with the `p`-th powers lies in the image of the residue-field map
  of the relative Frobenius.
* `AlgebraicGeometry.residueDegree_relativeFrobenius_genericPoint_dvd` — the resulting
  divisibility.

## Implementation notes

Only the inclusion of the compositum in the image of the residue-field map is proved, not the
equality, since divisibility of the degree is what consumers use and the reverse inclusion needs
the description of the residue field of a fibre product. The `k`-algebra structure on the
residue field is the one in which Stacks 0A21 states the equality of the dimension with the
transcendence degree, namely the evaluation of global sections at the point.

## References

* [Stacks Project, Tag 0CCF](https://stacks.math.columbia.edu/tag/0CCF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The residue fields of a scheme over a field of characteristic `p` have characteristic `p`. -/
theorem charP_residueField_of_over {k : Type u} [Field k] (p : ℕ) [CharP k p]
    {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (x : X) :
    CharP (X.residueField x) p := by
  let ι : k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.evaluation ⊤ x trivial).hom
  exact (ι.charP_iff_charP p).mp inferInstance

/-- The residue-field map of the absolute Frobenius is the `p`-th power map. -/
theorem absoluteFrobenius_residueFieldMap_apply (X : Scheme.{u}) (p : ℕ)
    [Fact p.Prime] (hX : IsInCharacteristic X p) (x : X) (a : X.residueField x) :
    (absoluteFrobenius X p hX).residueFieldMap x a = a ^ p := by
  obtain ⟨s, rfl⟩ := X.residue_surjective x a
  rw [← map_pow]
  have h := congrArg (fun g => g s)
    (Scheme.residue_residueFieldMap (absoluteFrobenius X p hX) x)
  change (absoluteFrobenius X p hX).residueFieldMap x (X.residue x s) =
    X.residue x ((absoluteFrobenius X p hX).stalkMap x s) at h
  rw [h]
  congr 1
  obtain ⟨U, hxU, g, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg := Scheme.Hom.germ_stalkMap_apply (absoluteFrobenius X p hX) U x hxU g
  rw [absoluteFrobenius_app_apply] at hg
  exact hg.trans (map_pow (X.presheaf.germ U x hxU).hom g p)

/-- The image of the residue-field map of a composition is contained in the image of the
residue-field map of its first factor. -/
theorem fieldRange_residueFieldMap_le_of_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (e : f ≫ g = h) (x : X) :
    (h.residueFieldMap x).hom.fieldRange ≤ (f.residueFieldMap x).hom.fieldRange := by
  subst h
  rw [Scheme.residueFieldMap_comp]
  rintro _ ⟨a, rfl⟩
  exact ⟨g.residueFieldMap (f x) a, rfl⟩

/-- The residue degree of a morphism is the degree of the residue field at the point over the
image of its residue-field map. -/
theorem residueDegree_eq_finrank_fieldRange {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.residueDegree x =
      Module.finrank (f.residueFieldMap x).hom.fieldRange (X.residueField x) := by
  let ι := (f.residueFieldMap x).hom
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) := ι.toAlgebra
  dsimp only [Scheme.Hom.residueDegree]
  exact Algebra.finrank_eq_of_equiv_equiv ι.rangeRestrictFieldEquiv
    (RingEquiv.refl (X.residueField x)) rfl

/-- The degree of a field over a larger subfield divides its degree over a smaller one. -/
theorem finrank_dvd_finrank_of_subfield_le {L : Type*} [Field L] {C M : Subfield L} (h : C ≤ M) :
    Module.finrank M L ∣ Module.finrank C L := by
  let ιCM : C →+* M :=
    { toFun := fun a => ⟨a.1, h a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra C M := ιCM.toAlgebra
  let _ : IsScalarTower C M L := IsScalarTower.of_algebraMap_eq' rfl
  exact Dvd.intro_left _ (Module.finrank_mul_finrank C M L)

/-- The compositum of the base field with the `p`-th powers of the residue field lies in the
image of the residue-field map of the relative Frobenius: the structure morphism factors the
relative Frobenius through the second projection, and the absolute Frobenius factors it through
the first.

The inclusion is in fact an equality, `fieldRange_residueFieldMap_relativeFrobenius` in
`StacksFrontier.AlgebraicGeometry.Variety.Frobenius.GenericDegreeEquality`, whose proof supplies
the reverse inclusion and takes this one as its other half. -/
theorem compositumFrobenius_le_fieldRange_residueFieldMap_relativeFrobenius
    {k : Type u} [Field k] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime]
    (hS : IsInCharacteristic (Spec (.of k)) p) (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation x).hom.toAlgebra
    compositumFrobenius k (X.residueField x) p ≤
      ((relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left.residueFieldMap
        x).hom.fieldRange := by
  let _ : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let S := Spec (.of k)
  let hX := isInCharacteristic_of_hom pX p hS
  let F := (relativeFrobenius S p hS (Over.mk pX)).left
  have hbase : (pX.residueFieldMap x).hom.fieldRange ≤ (F.residueFieldMap x).hom.fieldRange :=
    fieldRange_residueFieldMap_le_of_comp F
      (pullback.snd pX (absoluteFrobenius S p hS)) pX
      (relativeFrobenius_snd S p hS (Over.mk pX)) x
  have hfrob : ((absoluteFrobenius X p hX).residueFieldMap x).hom.fieldRange ≤
      (F.residueFieldMap x).hom.fieldRange :=
    fieldRange_residueFieldMap_le_of_comp F
      (pullback.fst pX (absoluteFrobenius S p hS)) (absoluteFrobenius X p hX)
      (relativeFrobenius_fst S p hS (Over.mk pX)) x
  apply Subfield.closure_le.mpr
  rintro a (⟨b, rfl⟩ | ⟨b, rfl⟩)
  · refine hbase ⟨((Scheme.ΓSpecIso (.of k)).inv ≫ S.Γevaluation (pX x)).hom b, ?_⟩
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ S.Γevaluation (pX x) ≫
        pX.residueFieldMap x).hom b =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation x).hom b
    rw [Scheme.Γevaluation_naturality]
  · exact hfrob ⟨b, absoluteFrobenius_residueFieldMap_apply X p hX x b⟩

/-- **The degree of the relative Frobenius of a smooth variety.** For an integral scheme of
finite type and smooth over a field of characteristic `p`, with dimension `d`, the residue
degree of the relative Frobenius at the generic point divides `p ^ d`. -/
theorem residueDegree_relativeFrobenius_genericPoint_dvd
    {k : Type u} [Field k] {X : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    (p : ℕ) [Fact p.Prime] [CharP k p] [IsIntegral X] [LocallyOfFiniteType pX] [Smooth pX]
    (hS : IsInCharacteristic (Spec (.of k)) p) (d : ℕ) (hd : topologicalKrullDim X = d) :
    (relativeFrobenius (Spec (.of k)) p hS (Over.mk pX)).left.residueDegree (genericPoint X) ∣
      p ^ d := by
  classical
  let η := genericPoint X
  let _ : Algebra k (X.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η).hom.toAlgebra
  have _ : CharP (X.residueField η) p := charP_residueField_of_over p pX η
  -- the algebra structure on the generic stalk, and its smoothness properties
  let _ : Algebra k (X.presheaf.stalk η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.presheaf.germ ⊤ η trivial).hom.toAlgebra
  obtain ⟨_, _⟩ := smoothAt_field_stalk_properties pX η
    ((InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp pX η).mpr
      ⟨⊤, trivial, MorphismProperty.comp_mem (W := @Smooth) _ _ inferInstance inferInstance⟩)
  let e : X.functionField ≃ₐ[k] X.residueField η :=
    AlgEquiv.ofRingEquiv (f := genericResidueEquiv X) (fun _ => rfl)
  have _ : Algebra.EssFiniteType k (X.residueField η) :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  have _ : Algebra.FormallySmooth k (X.residueField η) := Algebra.FormallySmooth.of_equiv e
  -- the transcendence degree of the residue field is the dimension
  have htr : Cardinal.toNat (Algebra.trdeg k (X.residueField η)) = d := by
    have hdim := topologicalKrullDim_eq_trdeg_residueField k X pX η (genericPoint_spec X)
    rw [hd] at hdim
    have hdim' : (d : ℕ∞) = Cardinal.toENat (Algebra.trdeg k (X.residueField η)) := mod_cast hdim
    simpa only [ENat.toNat_natCast, Cardinal.toNat_toENat] using (congrArg ENat.toNat hdim').symm
  have hcomp : Module.finrank (compositumFrobenius k (X.residueField η) p) (X.residueField η) =
      p ^ d := by
    rw [finrank_compositumFrobenius_eq_pow_trdeg p, htr]
  rw [residueDegree_eq_finrank_fieldRange, ← hcomp]
  exact finrank_dvd_finrank_of_subfield_le
    (compositumFrobenius_le_fieldRange_residueFieldMap_relativeFrobenius pX p hS η)

end AlgebraicGeometry

end
