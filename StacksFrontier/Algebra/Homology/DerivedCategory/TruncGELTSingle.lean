module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# A one-step truncation is its cohomology object placed in a single degree

For the canonical t-structure on the derived category of an abelian category `C`, the
truncation `τ^{≥q} τ^{<q+1}` of an object has its cohomology concentrated in degree `q`, and
is therefore isomorphic to `H^q` of that object regarded as a complex sitting in degree `q`.
This file proves that identification **as a natural isomorphism of functors**
```
τ^{≥q} τ^{<q+1} ≅ H^q(-)[-q]
```
on `DerivedCategory C` and on `DerivedCategory.Plus C`.

The statement is what turns the second page of the spectral sequence of a canonical truncation
tower into a double derived functor: for an additive functor `G`, the term
`H^{p+q}(RG(τ^{≥q} τ^{<q+1} M))` becomes `H^{p+q}(RG((single q).obj (H^q M)))`, which is the
`p`-th right derived functor of `G` applied to `H^q M`.

## Main definitions

* `DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor`: the natural isomorphism
  `τ^{≥q} τ^{<q+1} ≅ H^q ⋙ single q` on `DerivedCategory C`.
* `DerivedCategory.Plus.truncGELTIsoHomologyFunctorCompSingleFunctor`: the same on
  `DerivedCategory.Plus C`, for the induced t-structure.
* `DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIsoOfEq`: for a shift-commuting
  functor `Φ` and `p + q = r`, the identification
  `single q ⋙ Φ ⋙ H^r ≅ single 0 ⋙ Φ ⋙ H^p`, which turns the right-hand side of the previous
  item into a `p`-th right derived functor.
  `DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso` is the case `r = p + q`,
  which is how it is most often applied; the degree `r` is kept separate because the case
  `p = 0`, `r = q` is the one that identifies `single q ⋙ Φ ⋙ H^q` with `R ⁰` of the
  underlying functor, and there `0 + q = q` is not a definitional equality.

## Main results

* `DerivedCategory.isIso_homologyMap_truncLTι_app` and
  `DerivedCategory.isIso_homologyMap_truncGEπ_app`: the canonical maps to and from a truncation
  are isomorphisms on cohomology in the degrees the truncation retains, together with their
  natural-isomorphism forms `truncLTCompHomologyFunctorIso`, `truncGECompHomologyFunctorIso`
  and `truncGELTCompHomologyFunctorIso`.
* The same four statements in the `DerivedCategory.Plus` namespace.

## Implementation notes

Two inputs are not in Mathlib and are supplied here.

* No lemma in Mathlib relates a truncation functor of a t-structure to a homology functor.  The
  comparison is therefore read off the truncation triangle `τ^{<c} X ⟶ X ⟶ τ^{≥c} X` through
  the long exact cohomology sequence: the four `epi`/`mono` criteria
  `DerivedCategory.HomologySequence.{epi,mono}_homologyMap_mor{₁,₂}_iff` turn invertibility of
  the induced map into the vanishing of a cohomology object of the other vertex, which is the
  defining property of the truncation.  For `DerivedCategory.Plus` the same four criteria are
  not available, so the generic homological-functor versions
  `CategoryTheory.Functor.homologySequence_{epi,mono}_shift_map_mor{₁,₂}_iff` are used
  directly; they apply because `DerivedCategory.Plus.homologyFunctor C 0` is a homological
  functor with a shift sequence whose `i`-th term is `DerivedCategory.Plus.homologyFunctor C i`.
* Passing from "every value of the functor is isomorphic to a single complex" to a natural
  isomorphism does not go through a choice of such an isomorphism at each object: the single
  functor is fully faithful, so `CategoryTheory.Functor.essImage.liftFunctor` lifts the
  truncation functor through it and `essImage.liftFunctorCompIso` provides the factorisation.
  The lifted functor is then identified with `H^q` by applying `H^q` to that factorisation and
  using `DerivedCategory.singleFunctorCompHomologyFunctorIso`.  This avoids the heart of the
  t-structure, which has no instances outside Mathlib's own
  `Mathlib/CategoryTheory/Triangulated/TStructure/Heart.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' v v' u u'

namespace DerivedCategory

/-- If the third vertex of a distinguished triangle has vanishing homology in degrees `i - 1`
and `i`, then the first map is an isomorphism in degree `i`. -/
private theorem isIso_shift_map_mor₁_of_isZero {D : Type u'} {A : Type u} [Category.{v'} D]
    [Category.{v} A] [Abelian A] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] (F : D ⥤ A) [F.IsHomological]
    [F.ShiftSequence ℤ] (T : Triangle D) (hT : T ∈ distTriang D) (i : ℤ)
    (h₁ : IsZero ((F.shift (i - 1)).obj T.obj₃)) (h₂ : IsZero ((F.shift i).obj T.obj₃)) :
    IsIso ((F.shift i).map T.mor₁) := by
  have : Epi ((F.shift i).map T.mor₁) := by
    rw [F.homologySequence_epi_shift_map_mor₁_iff T hT i]
    exact h₂.eq_of_tgt _ _
  have : Mono ((F.shift i).map T.mor₁) := by
    rw [F.homologySequence_mono_shift_map_mor₁_iff T hT (i - 1) i (by omega)]
    exact h₁.eq_of_src _ _
  exact isIso_of_mono_of_epi _

/-- If the first vertex of a distinguished triangle has vanishing homology in degrees `i` and
`i + 1`, then the second map is an isomorphism in degree `i`. -/
private theorem isIso_shift_map_mor₂_of_isZero {D : Type u'} {A : Type u} [Category.{v'} D]
    [Category.{v} A] [Abelian A] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] (F : D ⥤ A) [F.IsHomological]
    [F.ShiftSequence ℤ] (T : Triangle D) (hT : T ∈ distTriang D) (i : ℤ)
    (h₁ : IsZero ((F.shift i).obj T.obj₁)) (h₂ : IsZero ((F.shift (i + 1)).obj T.obj₁)) :
    IsIso ((F.shift i).map T.mor₂) := by
  have : Epi ((F.shift i).map T.mor₂) := by
    rw [F.homologySequence_epi_shift_map_mor₂_iff T hT i (i + 1) rfl]
    exact h₂.eq_of_tgt _ _
  have : Mono ((F.shift i).map T.mor₂) := by
    rw [F.homologySequence_mono_shift_map_mor₂_iff T hT i]
    exact h₁.eq_of_src _ _
  exact isIso_of_mono_of_epi _

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **Below the truncation degree, `τ^{<c} X ⟶ X` is an isomorphism on cohomology.**  The
truncation triangle `τ^{<c} X ⟶ X ⟶ τ^{≥c} X` has third vertex with vanishing cohomology in
degrees `< c`, so the long exact sequence makes the first map epi in degree `i` and mono in
degree `i` for every `i < c`. -/
lemma isIso_homologyMap_truncLTι_app (c i : ℤ) (hi : i < c) (X : DerivedCategory C) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLTι c).app X)) := by
  exact isIso_shift_map_mor₁_of_isZero (homologyFunctor C 0) _
    (TStructure.t.triangleLTGE_distinguished c X) i (isZero_of_isGE _ c (i - 1) (by omega))
    (isZero_of_isGE _ c i hi)

/-- **At and above the truncation degree, `X ⟶ τ^{≥c} X` is an isomorphism on cohomology.**
The truncation triangle `τ^{<c} X ⟶ X ⟶ τ^{≥c} X` has first vertex with vanishing cohomology
in degrees `> c - 1`, so the long exact sequence makes the second map epi and mono in degree
`i` for every `c ≤ i`. -/
lemma isIso_homologyMap_truncGEπ_app (c i : ℤ) (hi : c ≤ i) (X : DerivedCategory C) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ c).app X)) := by
  exact isIso_shift_map_mor₂_of_isZero (homologyFunctor C 0) _
    (TStructure.t.triangleLTGE_distinguished c X) i
    (isZero_of_isLE _ (c - 1) i (by omega)) (isZero_of_isLE _ (c - 1) (i + 1) (by omega))

/-- **Truncating from above does not change cohomology below the truncation degree**, as a
natural isomorphism `τ^{<c} ⋙ H^i ≅ H^i` for `i < c`. -/
def truncLTCompHomologyFunctorIso (c i : ℤ) (hi : i < c) :
    TStructure.t.truncLT c ⋙ homologyFunctor C i ≅ homologyFunctor C i :=
  haveI : ∀ X : DerivedCategory C, IsIso ((Functor.whiskerRight (TStructure.t.truncLTι c)
      (homologyFunctor C i)).app X) := isIso_homologyMap_truncLTι_app c i hi
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight (TStructure.t.truncLTι c) (homologyFunctor C i))
  asIso (Functor.whiskerRight (TStructure.t.truncLTι c) (homologyFunctor C i)) ≪≫
    (homologyFunctor C i).leftUnitor

/-- **Truncating from below does not change cohomology at or above the truncation degree**, as a
natural isomorphism `H^i ≅ τ^{≥c} ⋙ H^i` for `c ≤ i`. -/
def truncGECompHomologyFunctorIso (c i : ℤ) (hi : c ≤ i) :
    homologyFunctor C i ≅ TStructure.t.truncGE c ⋙ homologyFunctor C i :=
  haveI : ∀ X : DerivedCategory C, IsIso ((Functor.whiskerRight (TStructure.t.truncGEπ c)
      (homologyFunctor C i)).app X) := isIso_homologyMap_truncGEπ_app c i hi
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight (TStructure.t.truncGEπ c) (homologyFunctor C i))
  (homologyFunctor C i).leftUnitor.symm ≪≫
    asIso (Functor.whiskerRight (TStructure.t.truncGEπ c) (homologyFunctor C i))

/-- **A one-step truncation has the cohomology of the object in the retained degree**, as a
natural isomorphism `τ^{≥q} τ^{<q+1} ⋙ H^q ≅ H^q`. -/
def truncGELTCompHomologyFunctorIso (q : ℤ) :
    TStructure.t.truncGELT q (q + 1) ⋙ homologyFunctor C q ≅ homologyFunctor C q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (truncGECompHomologyFunctorIso q q le_rfl).symm ≪≫
      truncLTCompHomologyFunctorIso (q + 1) q (by omega)

/-- **A one-step truncation is its cohomology object placed in a single degree**: the natural
isomorphism `τ^{≥q} τ^{<q+1} ≅ H^q ⋙ single q` of functors on `DerivedCategory C`.

Every value of `τ^{≥q} τ^{<q+1}` is `≥ q` and `≤ q`, hence isomorphic to a single complex in
degree `q`; since `single q` is fully faithful this lifts the truncation functor through it,
and applying `H^q` to the resulting factorisation identifies the lift with `H^q`. -/
def truncGELTIsoHomologyFunctorCompSingleFunctor (q : ℤ) :
    TStructure.t.truncGELT q (q + 1) ≅ homologyFunctor C q ⋙ singleFunctor C q := by
  have hG : ∀ X : DerivedCategory C,
      (singleFunctor C q).essImage ((TStructure.t.truncGELT q (q + 1)).obj X) := by
    intro X
    have : ((TStructure.t.truncGELT q (q + 1)).obj X).IsLE q := by
      have h : TStructure.t.IsLE ((TStructure.t.truncGELT q (q + 1)).obj X) (q + 1 - 1) :=
        inferInstance
      simpa using h
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.truncGELT q (q + 1)).obj X) q
    exact ⟨Y, ⟨e.symm⟩⟩
  let L := Functor.essImage.liftFunctor (TStructure.t.truncGELT q (q + 1)) (singleFunctor C q) hG
  let e₁ : L ⋙ singleFunctor C q ≅ TStructure.t.truncGELT q (q + 1) :=
    Functor.essImage.liftFunctorCompIso _ _ hG
  let e₂ : L ≅ homologyFunctor C q :=
    L.rightUnitor.symm ≪≫
      Functor.isoWhiskerLeft L (singleFunctorCompHomologyFunctorIso C q).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight e₁ (homologyFunctor C q) ≪≫
            truncGELTCompHomologyFunctorIso q
  exact e₁.symm ≪≫ Functor.isoWhiskerRight e₂ (singleFunctor C q)

namespace Plus

/-- **The single functor into the bounded below derived category is faithful**, because
composing it with the fully faithful inclusion `D⁺(C) ⥤ D(C)` is the single functor into
`D(C)`. -/
instance (q : ℤ) : (singleFunctor C q).Faithful :=
  haveI : (singleFunctor C q ⋙ Plus.ι).Faithful :=
    inferInstanceAs (DerivedCategory.singleFunctor C q).Faithful
  Functor.Faithful.of_comp _ Plus.ι

/-- **The single functor into the bounded below derived category is full**, because composing it
with the fully faithful inclusion `D⁺(C) ⥤ D(C)` is the single functor into `D(C)`. -/
instance (q : ℤ) : (singleFunctor C q).Full :=
  haveI : (singleFunctor C q ⋙ Plus.ι).Full :=
    inferInstanceAs (DerivedCategory.singleFunctor C q).Full
  Functor.Full.of_comp_faithful _ Plus.ι

/-- **The cohomology of a single complex in the same degree is the object itself**, on the
bounded below derived category.  This is
`DerivedCategory.singleFunctorCompHomologyFunctorIso` read through the inclusion. -/
def singleFunctorCompHomologyFunctorIso (q : ℤ) :
    singleFunctor C q ⋙ homologyFunctor C q ≅ 𝟭 C :=
  DerivedCategory.singleFunctorCompHomologyFunctorIso C q

/-- **Below the truncation degree, `τ^{<c} X ⟶ X` is an isomorphism on cohomology**, on the
bounded below derived category with its induced t-structure. -/
lemma isIso_homologyMap_truncLTι_app (c i : ℤ) (hi : i < c) (X : Plus C) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncLTι c).app X)) := by
  exact isIso_shift_map_mor₁_of_isZero (homologyFunctor C 0) _
    (TStructure.t.triangleLTGE_distinguished c X) i
    (isZero_homology_of_isGE _ c (i - 1) (by omega)) (isZero_homology_of_isGE _ c i hi)

/-- **At and above the truncation degree, `X ⟶ τ^{≥c} X` is an isomorphism on cohomology**, on
the bounded below derived category with its induced t-structure. -/
lemma isIso_homologyMap_truncGEπ_app (c i : ℤ) (hi : c ≤ i) (X : Plus C) :
    IsIso ((homologyFunctor C i).map ((TStructure.t.truncGEπ c).app X)) := by
  exact isIso_shift_map_mor₂_of_isZero (homologyFunctor C 0) _
    (TStructure.t.triangleLTGE_distinguished c X) i
    (isZero_homology_of_isLE _ (c - 1) i (by omega))
    (isZero_homology_of_isLE _ (c - 1) (i + 1) (by omega))

/-- **Truncating from above does not change cohomology below the truncation degree**, on the
bounded below derived category. -/
def truncLTCompHomologyFunctorIso (c i : ℤ) (hi : i < c) :
    TStructure.t.truncLT c ⋙ homologyFunctor C i ≅ homologyFunctor C i :=
  haveI : ∀ X : Plus C, IsIso ((Functor.whiskerRight (TStructure.t.truncLTι c)
      (homologyFunctor C i)).app X) := isIso_homologyMap_truncLTι_app c i hi
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight (TStructure.t.truncLTι c) (homologyFunctor C i))
  asIso (Functor.whiskerRight (TStructure.t.truncLTι c) (homologyFunctor C i)) ≪≫
    (homologyFunctor C i).leftUnitor

/-- **Truncating from below does not change cohomology at or above the truncation degree**, on
the bounded below derived category. -/
def truncGECompHomologyFunctorIso (c i : ℤ) (hi : c ≤ i) :
    homologyFunctor C i ≅ TStructure.t.truncGE c ⋙ homologyFunctor C i :=
  haveI : ∀ X : Plus C, IsIso ((Functor.whiskerRight (TStructure.t.truncGEπ c)
      (homologyFunctor C i)).app X) := isIso_homologyMap_truncGEπ_app c i hi
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight (TStructure.t.truncGEπ c) (homologyFunctor C i))
  (homologyFunctor C i).leftUnitor.symm ≪≫
    asIso (Functor.whiskerRight (TStructure.t.truncGEπ c) (homologyFunctor C i))

/-- **A one-step truncation has the cohomology of the object in the retained degree**, on the
bounded below derived category. -/
def truncGELTCompHomologyFunctorIso (q : ℤ) :
    TStructure.t.truncGELT q (q + 1) ⋙ homologyFunctor C q ≅ homologyFunctor C q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (truncGECompHomologyFunctorIso q q le_rfl).symm ≪≫
      truncLTCompHomologyFunctorIso (q + 1) q (by omega)

/-- **A one-step truncation is its cohomology object placed in a single degree**, on the bounded
below derived category: the natural isomorphism `τ^{≥q} τ^{<q+1} ≅ H^q ⋙ single q` of functors
on `DerivedCategory.Plus C`.

This is the identification that rewrites `H^{p+q}(RG(τ^{≥q} τ^{<q+1} M))`, the second page of
the spectral sequence of the canonical truncation tower, as `H^{p+q}(RG((single q).obj H^q M))`.
The essential-image condition is checked through the inclusion `D⁺(C) ⥤ D(C)`, where
`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE` applies. -/
def truncGELTIsoHomologyFunctorCompSingleFunctor (q : ℤ) :
    TStructure.t.truncGELT q (q + 1) ≅ homologyFunctor C q ⋙ singleFunctor C q := by
  have hG : ∀ X : Plus C,
      (singleFunctor C q).essImage ((TStructure.t.truncGELT q (q + 1)).obj X) := by
    intro X
    have : ((TStructure.t.truncGELT q (q + 1)).obj X).IsLE q := by
      have h : TStructure.t.IsLE ((TStructure.t.truncGELT q (q + 1)).obj X) (q + 1 - 1) :=
        inferInstance
      simpa using h
    obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
      (Plus.ι.obj ((TStructure.t.truncGELT q (q + 1)).obj X)) q
    exact ⟨Y, ⟨Plus.ι.preimageIso e.symm⟩⟩
  let L := Functor.essImage.liftFunctor (TStructure.t.truncGELT q (q + 1)) (singleFunctor C q) hG
  let e₁ : L ⋙ singleFunctor C q ≅ TStructure.t.truncGELT q (q + 1) :=
    Functor.essImage.liftFunctorCompIso _ _ hG
  let e₂ : L ≅ homologyFunctor C q :=
    L.rightUnitor.symm ≪≫
      Functor.isoWhiskerLeft L (singleFunctorCompHomologyFunctorIso q).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight e₁ (homologyFunctor C q) ≪≫
            truncGELTCompHomologyFunctorIso q
  exact e₁.symm ≪≫ Functor.isoWhiskerRight e₂ (singleFunctor C q)

section Shift

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]

/-- **Moving the degree of a single complex across a shift-commuting functor.**  For a functor
`Φ : D⁺(A) ⥤ D⁺(B)` commuting with the shift,
```
single q ⋙ Φ ⋙ H^{p+q} ≅ single 0 ⋙ Φ ⋙ H^p,
```
because `single q` is `single 0` shifted by `-q`, the shift passes through `Φ`, and the shift
sequence of `H^0` turns `H^{p+q}` of a complex shifted by `-q` into `H^p`.

Together with `truncGELTIsoHomologyFunctorCompSingleFunctor` this is what rewrites
`H^{p+q}(Φ(τ^{≥q} τ^{<q+1} K))` as `H^p(Φ((single 0).obj (H^q K)))`, that is, as the `p`-th
right derived functor of the underlying functor applied to `H^q K` when `Φ` is a right derived
functor. -/
def singleFunctorCompHomologyFunctorShiftIsoOfEq (Φ : Plus A ⥤ Plus B) [Φ.CommShift ℤ]
    (p q r : ℤ) (hr : p + q = r) :
    singleFunctor A q ⋙ Φ ⋙ homologyFunctor B r ≅
      singleFunctor A 0 ⋙ Φ ⋙ homologyFunctor B p :=
  Functor.isoWhiskerRight ((singleFunctors A).shiftIso (-q) q 0 (by omega)).symm
      (Φ ⋙ homologyFunctor B r) ≪≫
    Functor.isoWhiskerLeft (singleFunctor A 0)
      (Functor.isoWhiskerRight (Φ.commShiftIso (-q)) (homologyFunctor B r)) ≪≫
      Functor.isoWhiskerLeft (singleFunctor A 0) (Functor.isoWhiskerLeft Φ
        ((homologyFunctor B 0).shiftIso (-q) r p (by omega)))

/-- `singleFunctorCompHomologyFunctorShiftIsoOfEq` in the degree `r = p + q` in which it is most
often applied. -/
def singleFunctorCompHomologyFunctorShiftIso (Φ : Plus A ⥤ Plus B) [Φ.CommShift ℤ] (p q : ℤ) :
    singleFunctor A q ⋙ Φ ⋙ homologyFunctor B (p + q) ≅
      singleFunctor A 0 ⋙ Φ ⋙ homologyFunctor B p :=
  singleFunctorCompHomologyFunctorShiftIsoOfEq Φ p q (p + q) rfl

end Shift

end Plus

end DerivedCategory

end
