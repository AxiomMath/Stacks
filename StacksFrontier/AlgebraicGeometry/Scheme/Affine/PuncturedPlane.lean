module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# The punctured affine plane and its standard affine cover

Over a field `k`, the *punctured affine plane* is the complement of the origin in the affine
plane `Spec k[x, y]`, regarded as an open subscheme through its canonical open immersion.

It is covered by the two standard opens on which the coordinates `x` and `y` are respectively
invertible. Both of these are affine, with coordinate rings `k[x, y, 1/x]` and `k[x, y, 1/y]`,
and their intersection is the standard open where `xy` is invertible, with coordinate ring
`k[x, y, 1/(xy)]`. This is the cover exhibiting the punctured plane as a scheme, and the starting
point for showing that it is not an affine one.

## Main definitions

* `AlgebraicGeometry.affinePlaneRing`, `AlgebraicGeometry.affinePlane`: the coordinate ring
  `k[x, y]` and the affine plane `Spec k[x, y]`.
* `AlgebraicGeometry.affinePlaneOrigin`: the origin of the affine plane.
* `AlgebraicGeometry.PuncturedAffinePlane`: a field together with its affine plane punctured at
  the origin, and `AlgebraicGeometry.PuncturedAffinePlane.openImmersion` the canonical inclusion.
* `AlgebraicGeometry.puncturedAffinePlaneOf`: the punctured affine plane over a field, with the
  union of the two coordinate standard opens as its open subscheme.
* `AlgebraicGeometry.PuncturedAffinePlane.xOpen`,
  `AlgebraicGeometry.PuncturedAffinePlane.yOpen`,
  `AlgebraicGeometry.PuncturedAffinePlane.xyOpen`: the three standard opens of the punctured
  plane.

## Main results

* `AlgebraicGeometry.PuncturedAffinePlane.xOpen_sup_yOpen`: the two coordinate opens cover.
* `AlgebraicGeometry.PuncturedAffinePlane.isAffineOpen_xOpen` and
  `AlgebraicGeometry.PuncturedAffinePlane.isAffineOpen_yOpen`: the members of the cover are
  affine.
* `AlgebraicGeometry.PuncturedAffinePlane.xOpen_inf_yOpen`: their intersection is `xyOpen`.
* `AlgebraicGeometry.coe_basicOpen_X_sup`: the union of the two coordinate standard opens of
  `Spec k[x, y]` is the complement of the origin, and
  `AlgebraicGeometry.PuncturedAffinePlane.basicOpen_X_le_U` is the containment of one of them.
* The three `toScheme_iso_specAway_*` results identify these open subschemes with the spectra of
  the corresponding localized polynomial rings.
* `AlgebraicGeometry.PuncturedAffinePlane.compactSpace`,
  `AlgebraicGeometry.PuncturedAffinePlane.isQuasiAffine`,
  `AlgebraicGeometry.PuncturedAffinePlane.nonempty` and
  `AlgebraicGeometry.PuncturedAffinePlane.isIntegral`: the punctured affine plane is a nonempty
  quasi-compact integral scheme, and it is quasi-affine.

## Implementation notes

The polynomial ring `k[x, y]` is `MvPolynomial (Fin 2) k`, and the origin is the inverse image
of the closed point of `Spec k` under evaluation of both variables at zero. The scheme and its
inclusion morphism are determined by the field and the open subset, so they are exposed as named
definitions rather than stored as redundant fields of the structure. The standard opens of the
punctured plane are the inverse images of the standard opens of `Spec k[x, y]`, and the notation
`k[x, y, 1/f]` is represented by `Localization.Away f`.

The open subset of the situation is an open of the scheme `Spec k[x, y]`, whereas the elementary
facts about the coordinates are statements about the prime spectrum of `k[x, y]`. The two
descriptions agree definitionally but not syntactically, so the coordinate facts are proved for
a bare field, in terms of the prime spectrum alone, and the single lemma identifying the union of
the two coordinate opens with the punctured plane crosses between the two descriptions. That
crossing is done with `Eq.trans` and `congrArg` rather than `rw`, which would need the two types
to agree syntactically.

## References

* [Stacks Project, Tag 01IL](https://stacks.math.columbia.edu/tag/01IL)
* [Stacks Project, Section 26.6 (Tag 01HX)](https://stacks.math.columbia.edu/tag/01HX)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- The coordinate ring of the affine plane over `k`. -/
abbrev affinePlaneRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k

/-- The affine plane over `k`. -/
abbrev affinePlane (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of (affinePlaneRing k))

/-- The origin of the affine plane, defined by evaluation of both coordinates at zero. -/
noncomputable def affinePlaneOrigin (k : Type u) [Field k] :
    PrimeSpectrum (affinePlaneRing k) :=
  PrimeSpectrum.comap (MvPolynomial.eval 0) (⊤ : PrimeSpectrum k)

section Coordinates

variable (k : Type u) [Field k]

private lemma affinePlaneOrigin_asIdeal :
    (affinePlaneOrigin k).asIdeal =
      Ideal.comap (MvPolynomial.eval (0 : Fin 2 → k)) (IsLocalRing.maximalIdeal k) := rfl

/-- Both coordinates vanish at the origin of the affine plane. -/
lemma X_mem_affinePlaneOrigin (i : Fin 2) :
    (MvPolynomial.X i : affinePlaneRing k) ∈ (affinePlaneOrigin k).asIdeal := by
  rw [affinePlaneOrigin_asIdeal, Ideal.mem_comap]
  simp

private lemma isMaximal_affinePlaneOrigin : (affinePlaneOrigin k).asIdeal.IsMaximal := by
  rw [affinePlaneOrigin_asIdeal]
  exact Ideal.comap_isMaximal_of_surjective _ fun x => ⟨MvPolynomial.C x, by simp⟩

private lemma eval_eq_zero_of_mem_affinePlaneOrigin {f : affinePlaneRing k}
    (hf : f ∈ (affinePlaneOrigin k).asIdeal) :
    MvPolynomial.eval (0 : Fin 2 → k) f = 0 := by
  have h : MvPolynomial.eval (0 : Fin 2 → k) f ∈ IsLocalRing.maximalIdeal k := hf
  simpa [IsLocalRing.maximalIdeal_eq_bot] using h

private lemma affinePlaneOrigin_le_of_forall_X_mem
    {p : PrimeSpectrum (affinePlaneRing k)}
    (h : ∀ i : Fin 2, (MvPolynomial.X i : affinePlaneRing k) ∈ p.asIdeal) :
    (affinePlaneOrigin k).asIdeal ≤ p.asIdeal := by
  intro f hf
  apply (Ideal.span_le.2 ?_)
    (show f ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2))) from
      MvPolynomial.mem_ideal_span_X_image.2 ?_)
  · rintro _ ⟨i, -, rfl⟩
    exact h i
  · intro m hm
    have hf0 := eval_eq_zero_of_mem_affinePlaneOrigin k hf
    rw [MvPolynomial.eval_zero] at hf0
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact MvPolynomial.mem_support_iff.mp hm hf0
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ i, hi⟩

/-- Away from the origin, at least one of the two coordinates is invertible: the union of the two
coordinate standard opens is the complement of the origin. -/
lemma coe_basicOpen_X_sup :
    ((PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 2) : affinePlaneRing k) ⊔
        PrimeSpectrum.basicOpen (MvPolynomial.X (1 : Fin 2) : affinePlaneRing k) :
      TopologicalSpace.Opens (PrimeSpectrum (affinePlaneRing k))) :
        Set (PrimeSpectrum (affinePlaneRing k))) = {affinePlaneOrigin k}ᶜ := by
  ext p
  simp only [TopologicalSpace.Opens.coe_sup, Set.mem_union, SetLike.mem_coe,
    PrimeSpectrum.mem_basicOpen, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) rfl
    · exact h (X_mem_affinePlaneOrigin k 0)
    · exact h (X_mem_affinePlaneOrigin k 1)
  · intro hp
    by_contra hcon
    push Not at hcon
    exact hp (PrimeSpectrum.ext
      ((isMaximal_affinePlaneOrigin k).eq_of_le p.2.ne_top
        (affinePlaneOrigin_le_of_forall_X_mem k (Fin.forall_fin_two.2 hcon))).symm)

end Coordinates

/-- A field together with its affine plane punctured at the origin. -/
structure PuncturedAffinePlane where
  /-- The ground field. -/
  k : Type u
  /-- The field structure on the ground field. -/
  [field : Field k]
  /-- The open subspace of the affine plane. -/
  U : (affinePlane k).Opens
  /-- Its underlying set is precisely the complement of the origin. -/
  carrier_U : (U : Set (affinePlane k)) = {affinePlaneOrigin k}ᶜ

attribute [instance] PuncturedAffinePlane.field

namespace PuncturedAffinePlane

/-- The coordinate ring `k[x, y]` belonging to the situation. -/
abbrev R (S : PuncturedAffinePlane) := affinePlaneRing S.k

/-- The affine plane `Spec(k[x, y])` belonging to the situation. -/
abbrev X (S : PuncturedAffinePlane) : Scheme.{u} := affinePlane S.k

/-- The punctured affine plane as a scheme. -/
abbrev puncturedScheme (S : PuncturedAffinePlane) : Scheme.{u} := S.U

/-- The canonical open immersion from the punctured affine plane into the affine plane. -/
noncomputable def openImmersion (S : PuncturedAffinePlane) :
    S.puncturedScheme ⟶ S.X :=
  S.U.ι

variable (S : PuncturedAffinePlane.{u})

/-- The inclusion of the punctured affine plane into the affine plane is an open immersion. -/
local instance : IsOpenImmersion S.openImmersion := by
  dsimp [PuncturedAffinePlane.openImmersion]
  infer_instance

/-- The open subscheme of the situation is the union of the two coordinate standard opens, as
opens of `Spec k[x, y]`. -/
lemma basicOpen_X_sup_eq_U :
    ((PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 2) : S.R) : S.X.Opens) ⊔
      PrimeSpectrum.basicOpen (MvPolynomial.X (1 : Fin 2) : S.R)) = S.U :=
  TopologicalSpace.Opens.ext ((coe_basicOpen_X_sup S.k).trans S.carrier_U.symm)

/-- A coordinate standard open is contained in the punctured plane, as opens of `Spec k[x, y]`. -/
lemma basicOpen_X_le_U (i : Fin 2) :
    (PrimeSpectrum.basicOpen (MvPolynomial.X i : S.R) : S.X.Opens) ≤ S.U := by
  refine le_of_le_of_eq ?_ (basicOpen_X_sup_eq_U S)
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- The first-coordinate standard open in the punctured affine plane. -/
def xOpen : S.puncturedScheme.Opens :=
  S.openImmersion ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 2) : S.R)

/-- The second-coordinate standard open in the punctured affine plane. -/
def yOpen : S.puncturedScheme.Opens :=
  S.openImmersion ⁻¹ᵁ PrimeSpectrum.basicOpen (MvPolynomial.X (1 : Fin 2) : S.R)

/-- The standard open where the product of the two coordinates is invertible. -/
def xyOpen : S.puncturedScheme.Opens :=
  S.openImmersion ⁻¹ᵁ PrimeSpectrum.basicOpen
    (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) : S.R)

/-- The two coordinate standard opens cover the punctured affine plane. -/
@[stacks 01IL "affine_open_cover"]
theorem xOpen_sup_yOpen : xOpen S ⊔ yOpen S = ⊤ :=
  S.openImmersion.preimage_sup.symm.trans
    ((congrArg (fun V : S.X.Opens => S.openImmersion ⁻¹ᵁ V) (basicOpen_X_sup_eq_U S)).trans
      S.U.ι_preimage_self)

/-- The preimage of a basic open contained in the punctured plane is affine. -/
private theorem isAffineOpen_preimage_basicOpen (f : S.R)
    (h : (PrimeSpectrum.basicOpen f : S.X.Opens) ≤ S.U) :
    IsAffineOpen (S.openImmersion ⁻¹ᵁ (PrimeSpectrum.basicOpen f : S.X.Opens)) :=
  (IsAffineOpen.Spec_basicOpen _).preimage_of_isOpenImmersion _
    (h.trans_eq S.U.opensRange_ι.symm)

/-- The preimage of a basic open contained in the punctured plane is the spectrum of the
localization at `f`. -/
private theorem nonempty_iso_specAway_preimage_basicOpen (f : S.R)
    (h : (PrimeSpectrum.basicOpen f : S.X.Opens) ≤ S.U) :
    Nonempty ((S.openImmersion ⁻¹ᵁ (PrimeSpectrum.basicOpen f : S.X.Opens)).toScheme ≅
      Spec (.of (Localization.Away f))) :=
  ⟨Scheme.Opens.isoOfLE h ≪≫ basicOpenIsoSpecAway _⟩

/-- The first-coordinate member of the standard cover is affine. -/
@[stacks 01IL "affine_open_cover"]
theorem isAffineOpen_xOpen : IsAffineOpen (xOpen S) :=
  isAffineOpen_preimage_basicOpen S _ (basicOpen_X_le_U S 0)

/-- The second-coordinate member of the standard cover is affine. -/
@[stacks 01IL "affine_open_cover"]
theorem isAffineOpen_yOpen : IsAffineOpen (yOpen S) :=
  isAffineOpen_preimage_basicOpen S _ (basicOpen_X_le_U S 1)

/-- The intersection of the two members of the cover is the product standard open. -/
@[stacks 01IL "affine_open_cover"]
theorem xOpen_inf_yOpen : xOpen S ⊓ yOpen S = xyOpen S := by
  exact S.openImmersion.preimage_inf.symm.trans
    (congrArg _ (PrimeSpectrum.basicOpen_mul _ _).symm)

/-- The first-coordinate standard open has coordinate ring `k[x,y,1/x]`. -/
@[stacks 01IL "affine_open_cover"]
theorem toScheme_iso_specAway_x :
    Nonempty ((xOpen S).toScheme ≅
      Spec (.of (Localization.Away (MvPolynomial.X (0 : Fin 2) : S.R)))) :=
  nonempty_iso_specAway_preimage_basicOpen S _ (basicOpen_X_le_U S 0)

/-- The second-coordinate standard open has coordinate ring `k[x,y,1/y]`. -/
@[stacks 01IL "affine_open_cover"]
theorem toScheme_iso_specAway_y :
    Nonempty ((yOpen S).toScheme ≅
      Spec (.of (Localization.Away (MvPolynomial.X (1 : Fin 2) : S.R)))) :=
  nonempty_iso_specAway_preimage_basicOpen S _ (basicOpen_X_le_U S 1)

/-- The intersection standard open has coordinate ring `k[x,y,1/(xy)]`. -/
@[stacks 01IL "affine_open_cover"]
theorem toScheme_iso_specAway_xy :
    Nonempty ((xyOpen S).toScheme ≅ Spec (.of (Localization.Away
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) : S.R)))) :=
  nonempty_iso_specAway_preimage_basicOpen S _ ((PrimeSpectrum.basicOpen_mul _ _).le.trans
    (inf_le_left.trans (basicOpen_X_le_U S 0)))

/-- The punctured affine plane is quasi-compact: it is covered by its two affine standard
opens. -/
@[ega "III 2.2.5" "(ii)"]
instance compactSpace : CompactSpace S.puncturedScheme := by
  constructor
  have h : (Set.univ : Set S.puncturedScheme) =
      (xOpen S : Set S.puncturedScheme) ∪ (yOpen S : Set S.puncturedScheme) := by
    rw [← TopologicalSpace.Opens.coe_sup, xOpen_sup_yOpen, TopologicalSpace.Opens.coe_top]
  rw [h]
  exact (isAffineOpen_xOpen S).isCompact.union (isAffineOpen_yOpen S).isCompact

/-- The punctured affine plane is quasi-affine: it is a quasi-compact open subscheme of an
affine scheme. -/
instance isQuasiAffine : S.puncturedScheme.IsQuasiAffine :=
  Scheme.IsQuasiAffine.of_isImmersion (f := S.openImmersion)

/-- The punctured affine plane is nonempty: it contains the generic point of `Spec k[x, y]`. -/
instance nonempty : Nonempty S.puncturedScheme := by
  refine ⟨⟨(⊥ : PrimeSpectrum S.R), ?_⟩⟩
  change (⊥ : PrimeSpectrum S.R) ∈ (S.U : Set S.X)
  rw [S.carrier_U]
  intro hbot
  have h := X_mem_affinePlaneOrigin S.k 0
  rw [← hbot, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot] at h
  exact MvPolynomial.X_ne_zero (0 : Fin 2) h

/-- The punctured affine plane is integral: it is a nonempty open subscheme of the spectrum of
a polynomial ring over a field. -/
instance isIntegral : IsIntegral S.puncturedScheme :=
  isIntegral_of_isOpenImmersion S.openImmersion

end PuncturedAffinePlane

/-- The punctured affine plane over a field, as a situation: the open subscheme is the union of
the two coordinate standard opens of `Spec k[x, y]`. -/
def puncturedAffinePlaneOf (k : Type u) [Field k] : PuncturedAffinePlane.{u} where
  k := k
  U := (PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 2) : affinePlaneRing k) :
      (affinePlane k).Opens) ⊔
    PrimeSpectrum.basicOpen (MvPolynomial.X (1 : Fin 2) : affinePlaneRing k)
  carrier_U := coe_basicOpen_X_sup k

/-- The field of `puncturedAffinePlaneOf k` is `k`. -/
@[simp]
lemma puncturedAffinePlaneOf_k (k : Type u) [Field k] : (puncturedAffinePlaneOf k).k = k := rfl

/-- The open subscheme of `puncturedAffinePlaneOf k` is the union of the two coordinate standard
opens of `Spec k[x, y]`. -/
@[simp]
lemma puncturedAffinePlaneOf_U (k : Type u) [Field k] :
    (puncturedAffinePlaneOf k).U =
      (PrimeSpectrum.basicOpen (MvPolynomial.X (0 : Fin 2) : affinePlaneRing k) :
          (affinePlane k).Opens) ⊔
        PrimeSpectrum.basicOpen (MvPolynomial.X (1 : Fin 2) : affinePlaneRing k) := rfl

end AlgebraicGeometry

end
