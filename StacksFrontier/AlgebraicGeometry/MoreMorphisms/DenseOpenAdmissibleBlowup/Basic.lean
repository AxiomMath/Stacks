module

public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.TwistAmple
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AmpleFamilyCartier.AmpleFamily
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic

/-!
# A dense open with an admissible blowup carrying an ample family

Let `X` be a quasi-compact and quasi-separated scheme with finitely many irreducible components.
Covering `X` by finitely many affine opens `W 0, …, W (m-1)` each containing all the generic
points of the irreducible components, the quasi-compact open `U = W 0 ⊓ ⋯ ⊓ W (m-1)` is dense,
and the blowup of `X` in a product `I = A 0 ⋯ A (m-1)` of finite type ideals cutting out the
complements of the `W i` is a `U`-admissible blowup on which each `A i` pulls back to an
effective Cartier divisor whose complement is the inverse image of `W i`.

## Main results

* `Stacks.DenseOpenAdmissibleBlowup.isEffectiveCartierDivisor_comap_blowUpToBase_of_eq_mul`: on
  the blowup of `X` in a product, the inverse image of either factor is an effective Cartier
  divisor.
* `Stacks.DenseOpenAdmissibleBlowup.exists_admissibleBlowup_effectiveCartierCover`: the
  construction above, with all of its data.
* `Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_isAdmissibleBlowup`: the quasi-compact
  dense open and the `U`-admissible blowup of [Stacks, Tag 0GTT], without the ample family.
* `Stacks.DenseOpenAdmissibleBlowup.exists_isRelativelyAmple_twist`: [Stacks, Tag 02NS] part (2)
  re-spelled for the ampleness predicate used below.
* `Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_isAdmissibleBlowup_isAmpleFamily`:
  the argument of [Stacks, Tag 0GTT] for any transition datum of the chart twists.

## Implementation notes

**The ample family.** The source's proof concludes with [Stacks, Tag 0GTS] — finitely many
effective Cartier divisors with empty common intersection and an invertible module ample on the
complement of each give an ample family — applied to the divisors constructed here and to
`𝒪_{X'}(1)`, which is ample relative to the blowup morphism by [Stacks, Tag 02NS]. Tag 0GTS is
`Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_isAmpleOnComplement_cover`, and Tag 02NS
part (2) is `AlgebraicGeometry.isRelativelyAmple_twist_reesSituation`; both are used here.
`exists_isRelativelyAmple_twist` below is only the re-spelling that feeds the latter to the
ampleness-on-a-complement predicate. It is stated for an arbitrary
`Stacks.RelativeProj.Situation.TwistTransition 1` — the comparison data of [Stacks, Tag 01NO]
clauses (3) and (4) for the chart twists — so the theorem of this file takes one such datum per
centre as `h01NO`, which `Stacks.RelativeProj.Situation.twistTransition` supplies in
`Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_admissibleBlowup_isAmpleFamily`.

**The effective Cartier divisors.** The divisor at the index `i` is the inverse image on the
blowup of the factor `A i` of the centre. Tag 080A (`AlgebraicGeometry.blowUpMulIso`) factors the
blowup in `A i * J i` over `X` through the blowup in `A i`, on which the inverse image of `A i` is
the exceptional divisor (Tag 02OS); its further inverse image is defined by Tag 0809, and
transporting along the comparison isomorphism over `X` uses Tag 02OO for a flat — here
invertible — morphism. The factorization `I = A i * J i` is consumed by `subst` rather than by
`rw`, since rewriting the centre changes the type of the ideal sheaf on the blowup.

**Two constructions of the blowup.** `Stacks.Blowup.IsAdmissibleBlowup` is phrased with
`Stacks.Blowup.blowUp` while the Cartier machinery above is developed for
`AlgebraicGeometry.blowUp`; the two are compared by `Stacks.Blowup.isAdmissibleBlowup_iff`, which
is the form of the predicate used here.

**The spelling of ampleness on a complement.** `Stacks.AmpleFamilyCartier.IsAmpleOnComplement`
asks for ampleness of `(Scheme.Modules.restrictFunctor ι).obj L`, whereas
`Stacks.RelativeAmple.IsRelativelyAmple` delivers it for
`(Scheme.Modules.pullback ι).obj L`; the two are compared by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, across which ampleness moves by
`AlgebraicGeometry.Scheme.Modules.isAmple_of_iso` and invertibility by
`Stacks.SheafOfModules.Invertible.isInvertible_of_iso`.

## References

* [Stacks Project, Tag 0GTT](https://stacks.math.columbia.edu/tag/0GTT)
* [Stacks Project, Tag 0GTS](https://stacks.math.columbia.edu/tag/0GTS)
* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 01ZX](https://stacks.math.columbia.edu/tag/01ZX)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.DenseOpenAdmissibleBlowup

variable {X : Scheme.{u}}

/-- A point of a finite infimum of opens is a point of each member. -/
private theorem mem_inf_finset {α : Type*} {T : Type*} [TopologicalSpace T]
    (s : Finset α) (V : α → Opens T) (x : T) :
    x ∈ s.inf V ↔ ∀ i ∈ s, x ∈ V i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih => simp [Finset.inf_insert, ih]

/-- A finite infimum of quasi-compact opens of a quasi-compact quasi-separated space is
quasi-compact; the empty infimum is the whole space. -/
private theorem isCompact_inf_finset {α : Type*} {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [QuasiSeparatedSpace T] (s : Finset α) (V : α → Opens T)
    (hV : ∀ i, IsCompact ((V i : Opens T) : Set T)) :
    IsCompact ((s.inf V : Opens T) : Set T) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCompact_univ (X := T)
  | @insert i s his ih =>
      rw [Finset.inf_insert]
      exact QuasiSeparatedSpace.inter_isCompact _ _ (V i).2 (hV i) (s.inf V).2 ih

/-- Ampleness on a complement, recognized through any open identified with that complement. -/
private theorem isAmpleOnComplement_of_support_compl_eq {Y : Scheme.{u}} {D : Y.IdealSheafData}
    {V : Y.Opens} (hV : D.support.compl = V) {L : Y.Modules}
    (hinv : AlgebraicGeometry.SheafOfModules.IsInvertible V.toScheme.toRingedSpace.presheaf
      (structureSheafRing V.toScheme.toRingedSpace).property
      ((Scheme.Modules.restrictFunctor V.ι).obj L))
    (hamp : @AlgebraicGeometry.Scheme.Modules.IsAmple V.toScheme
      ((Scheme.Modules.restrictFunctor V.ι).obj L) hinv) :
    Stacks.AmpleFamilyCartier.IsAmpleOnComplement D L := by
  subst hV
  exact ⟨hinv, hamp⟩

/-- **The inverse image of a factor of the centre is an effective Cartier divisor on the
blowup.** If the centre `I` factors as `A * B`, then blowing up `A` and then the inverse image of
`B` gives the blowup of `A * B` over `X` (Tag 080A); on the first blowup the inverse image of `A`
is the exceptional divisor (Tag 02OS), its further inverse image is an effective Cartier divisor
(Tag 0809), and the comparison isomorphism over `X` is flat (Tag 02OO). -/
theorem isEffectiveCartierDivisor_comap_blowUpToBase_of_eq_mul {I A B : X.IdealSheafData}
    (h : I = A * B) :
    Stacks.Divisors.IsEffectiveCartierDivisor (A.comap (blowUpToBase I)) := by
  subst h
  have hseq : Stacks.Divisors.IsEffectiveCartierDivisor
      (A.comap (blowUpToBase (B.comap (blowUpToBase A)) ≫ blowUpToBase A)) := by
    rw [Scheme.IdealSheafData.comap_comp]
    exact AlgebraicGeometry.isPullbackDefined_blowUpToBase (B.comap (blowUpToBase A))
      (exceptionalIdeal A) (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal A)
  have e : Over.mk (blowUpToBase (B.comap (blowUpToBase A)) ≫ blowUpToBase A) ≅
      Over.mk (blowUpToBase (A * B)) := AlgebraicGeometry.blowUpMulIso A B
  have : IsIso e.inv.left := by
    change IsIso ((Over.forget X).map e.inv)
    infer_instance
  have hpull := Stacks.Divisors.isPullbackDefined_of_flat e.inv.left _ hseq
  have hmap : e.inv.left ≫ (blowUpToBase (B.comap (blowUpToBase A)) ≫ blowUpToBase A) =
      blowUpToBase (A * B) := Over.w e.inv
  change Stacks.Divisors.IsEffectiveCartierDivisor
    ((A.comap (blowUpToBase (B.comap (blowUpToBase A)) ≫ blowUpToBase A)).comap e.inv.left)
    at hpull
  rwa [← Scheme.IdealSheafData.comap_comp, hmap] at hpull

/-- **The relatively ample invertible module on a blowup, from [Stacks, Tag 02NS] part (2).** For
a centre of finite type, the degree-one twist `𝒪_{X'}(1)` glued along a transition datum `t` is
invertible and ample relative to the blowup morphism.

This repackages `AlgebraicGeometry.isRelativelyAmple_twist_reesSituation` with the invertibility
of the twist (`AlgebraicGeometry.isInvertibleModule_twist_reesSituation`) as an explicit
witness, the form consumed by the ampleness-on-a-complement predicate. -/
theorem exists_isRelativelyAmple_twist (I : X.IdealSheafData) (hI : I.IsFiniteType)
    (t : (reesSituation I).TwistTransition 1) :
    ∃ (L : (blowUp I).Modules) (hL : AlgebraicGeometry.SheafOfModules.IsInvertible
        (blowUp I).presheaf (blowUp I).ringCatSheaf.2 L),
      @Stacks.RelativeAmple.IsRelativelyAmple _ _ (blowUpToBase I) L hL := by
  have hinv : Stacks.Ample.IsInvertibleModule (blowUp I)
      (Stacks.RelativeProj.Situation.twist t) :=
    AlgebraicGeometry.isInvertibleModule_twist_reesSituation I t
  exact ⟨_, hinv, (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple
    (blowUpToBase I) _).mp (AlgebraicGeometry.isRelativelyAmple_twist_reesSituation I hI t)⟩

/-- **The construction behind [Stacks, Tag 0GTT], at prescribed generic points.** Let `X` be
a quasi-compact quasi-separated scheme and let `η 0, …, η (n-1)` be the generic points of
finitely many distinct irreducible components `Z 0, …, Z (n-1)` of `X`. Then `X` carries a finite
family of affine opens `W i` covering it, a quasi-compact open `U` contained in each of them and
containing every `η j`, and finite type ideals `A i` cutting out the complements of the `W i`,
such that the blowup of `X` in `I = ∏ A i` is a `U`-admissible blowup on which each `A i` pulls
back to an effective Cartier divisor whose complement is the inverse image of `W i`.

No finiteness of the set of irreducible components of `X` is needed: the affine opens through a
point and the prescribed generic points come from Tag 01ZX for the finitely many components
`Z i`. -/
theorem exists_admissibleBlowup_effectiveCartierCover_of_genericPoints (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] {n : ℕ} (Z : Fin n → Set X)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hinj : Function.Injective Z) (η : Fin n → X)
    (hη : ∀ i, IsGenericPoint (η i) (Z i)) :
    ∃ (U : X.Opens) (I : X.IdealSheafData) (m : ℕ) (W : Fin m → X.Opens)
      (A : Fin m → X.IdealSheafData),
      IsCompact (U : Set X) ∧ (∀ i, η i ∈ U) ∧ I.IsFiniteType ∧
        Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
        (∀ i, IsAffineOpen (W i)) ∧
        (∀ x : X, ∃ i, x ∈ W i) ∧
        (∀ i, Stacks.Divisors.IsEffectiveCartierDivisor ((A i).comap (blowUpToBase I))) ∧
        (∀ i, ((A i).comap (blowUpToBase I)).support.compl = blowUpToBase I ⁻¹ᵁ W i) := by
  classical
  -- An affine open through any prescribed point and all the generic points, by Tag 01ZX.
  have htarget (x : X) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ ∀ i, η i ∈ V :=
    AlgebraicGeometry.exists_affineOpen_mem_of_genericPoints_irreducibleComponents
      X Z hZ hinj η hη x
  choose V hVaff hxV hVη using htarget
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).2)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  let m := s.card
  let eS : Fin m ≃ s := s.equivFin.symm
  let W : Fin m → X.Opens := fun i => V (eS i).1
  have hWaff : ∀ i, IsAffineOpen (W i) := fun i => hVaff (eS i).1
  have hWcompact : ∀ i, IsCompact (W i : Set X) := fun i => (hWaff i).isCompact
  have hWcover : ∀ x : X, ∃ i, x ∈ W i := by
    intro x
    obtain ⟨i, his, hi⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨eS.symm ⟨i, his⟩, by simpa [W] using hi⟩
  -- The quasi-compact open through the prescribed generic points.
  let U : X.Opens := Finset.univ.inf W
  have hUle : ∀ i, U ≤ W i := fun i => Finset.inf_le (Finset.mem_univ i)
  have hUcompact : IsCompact (U : Set X) := isCompact_inf_finset Finset.univ W hWcompact
  have hηU : ∀ i, η i ∈ U := fun i =>
    (mem_inf_finset Finset.univ W (η i)).2 fun j _ => hVη (eS j).1 i
  -- The finite type ideals cutting out the complements of the `W i`, by Tag 01PH.
  have hAex (i : Fin m) : ∃ K : X.IdealSheafData, K.IsFiniteType ∧
      (K.support : Set X) = (W i : Set X)ᶜ :=
    AlgebraicGeometry.exists_isFiniteType_idealSheafData_support_eq_compl (W i) (hWcompact i)
  choose A hAft hAsupport using hAex
  let I : X.IdealSheafData := ∏ i, A i
  have hIft : I.IsFiniteType := Stacks.Blowup.isFiniteType_prod Finset.univ A hAft
  have hIavoid : Disjoint (U : Set X) (I.support : Set X) :=
    Stacks.Blowup.disjoint_support_prod U Finset.univ A fun i _ =>
      Set.disjoint_left.mpr fun x hxU hxi => ((hAsupport i).le hxi) (hUle i hxU)
  -- The complement of the inverse image of `A i` is the inverse image of `W i`.
  have hcompl (i : Fin m) :
      ((A i).comap (blowUpToBase I)).support.compl = blowUpToBase I ⁻¹ᵁ W i := by
    refine Opens.ext (Set.ext fun x => ?_)
    have h1 : x ∈ ((((A i).comap (blowUpToBase I)).support.compl : (blowUp I).Opens) :
          Set (blowUp I)) ↔ (blowUpToBase I).base x ∉ ((A i).support : Set X) := by
      rw [Scheme.IdealSheafData.support_comap]; exact Iff.rfl
    have h2 : x ∈ ((blowUpToBase I ⁻¹ᵁ W i : (blowUp I).Opens) : Set (blowUp I)) ↔
        (blowUpToBase I).base x ∈ (W i : Set X) := Iff.rfl
    rw [h1, h2, show ((A i).support : Set X) = (W i : Set X)ᶜ from hAsupport i,
      Set.mem_compl_iff, not_not]
  refine ⟨U, I, m, W, A, hUcompact, hηU, hIft, ?_, hWaff, hWcover, fun i => ?_, hcompl⟩
  · exact (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase I)).mpr
      ⟨I, (AlgebraicGeometry.finitePresentation_subschemeι_iff_isFiniteType I).mpr hIft, hIavoid,
        Iso.refl _, Category.id_comp _⟩
  · exact isEffectiveCartierDivisor_comap_blowUpToBase_of_eq_mul
      (B := ∏ j ∈ Finset.univ.erase i, A j)
      (Finset.mul_prod_erase Finset.univ A (Finset.mem_univ i)).symm

/-- An open of a scheme with finitely many irreducible components that contains the generic point
of each of them is dense. -/
theorem dense_of_forall_genericPoint_mem [Finite (irreducibleComponents X)] (U : X.Opens)
    (hU : ∀ c : irreducibleComponents X, c.2.1.genericPoint ∈ (U : Set X)) :
    Dense (U : Set X) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  have hxall : x ∈ ⋃₀ irreducibleComponents X := by
    rw [sUnion_irreducibleComponents]
    simp
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hxall
  let c : irreducibleComponents X := ⟨C, hC⟩
  have hxC' : x ∈ (c : Set X) := hxC
  have hgen : closure ({c.2.1.genericPoint} : Set X) = (c : Set X) :=
    (c.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ c.2)).def
  refine closure_mono (fun y hy => ?_) (hgen ▸ hxC' : x ∈ closure _)
  simpa [Set.mem_singleton_iff.mp hy] using hU c

/-- Enumerating the irreducible components of a scheme with finitely many of them gives distinct
components with generic points such that every open containing all these points is dense. -/
private theorem exists_genericPoints_forall_mem_dense (X : Scheme.{u})
    [Finite (irreducibleComponents X)] :
    ∃ (n : ℕ) (Z : Fin n → Set X) (_ : ∀ i, Z i ∈ irreducibleComponents X)
      (_ : Function.Injective Z) (η : Fin n → X), (∀ i, IsGenericPoint (η i) (Z i)) ∧
        ∀ U : X.Opens, (∀ i, η i ∈ U) → Dense (U : Set X) := by
  have : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let e : Fin (Fintype.card (irreducibleComponents X)) ≃ irreducibleComponents X :=
    (Fintype.equivFin _).symm
  refine ⟨_, fun i => (e i : Set X), fun i => (e i).2,
    fun i j hij => e.injective (Subtype.ext hij), fun i => (e i).2.1.genericPoint,
    fun i => (e i).2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ (e i).2), fun U hU => ?_⟩
  exact dense_of_forall_genericPoint_mem U fun c => by simpa using hU (e.symm c)

/-- **The construction behind [Stacks, Tag 0GTT].** A quasi-compact quasi-separated scheme with
finitely many irreducible components carries a finite family of affine opens `W i` covering it,
all containing every generic point, a quasi-compact dense open `U` contained in each of them, and
finite type ideals `A i` cutting out the complements of the `W i`, such that the blowup of `X` in
`I = ∏ A i` is a `U`-admissible blowup on which each `A i` pulls back to an effective Cartier
divisor whose complement is the inverse image of `W i`. -/
theorem exists_admissibleBlowup_effectiveCartierCover (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [Finite (irreducibleComponents X)] :
    ∃ (U : X.Opens) (I : X.IdealSheafData) (m : ℕ) (W : Fin m → X.Opens)
      (A : Fin m → X.IdealSheafData),
      IsCompact (U : Set X) ∧ Dense (U : Set X) ∧ I.IsFiniteType ∧
        Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
        (∀ i, IsAffineOpen (W i)) ∧
        (∀ x : X, ∃ i, x ∈ W i) ∧
        (∀ i, Stacks.Divisors.IsEffectiveCartierDivisor ((A i).comap (blowUpToBase I))) ∧
        (∀ i, ((A i).comap (blowUpToBase I)).support.compl = blowUpToBase I ⁻¹ᵁ W i) := by
  obtain ⟨n, Z, hZ, hinj, η, hη, hdense⟩ := exists_genericPoints_forall_mem_dense X
  obtain ⟨U, I, m, W, A, hUc, hηU, hrest⟩ :=
    exists_admissibleBlowup_effectiveCartierCover_of_genericPoints X Z hZ hinj η hη
  exact ⟨U, I, m, W, A, hUc, hdense U hηU, hrest⟩

/-- **The first two conjuncts of [Stacks, Tag 0GTT].** A quasi-compact quasi-separated scheme
with finitely many irreducible components has a quasi-compact dense open `U` and a
`U`-admissible blowup `X' ⟶ X`. The ample family on `X'` is not asserted here; see
`Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_isAdmissibleBlowup_isAmpleFamily`. -/
theorem exists_isCompact_dense_isAdmissibleBlowup (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [Finite (irreducibleComponents X)] :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ Dense (U : Set X) ∧
      ∃ (X' : Scheme.{u}) (f : X' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup U f := by
  obtain ⟨U, I, m, W, A, hUc, hUd, -, hadm, -, -, -, -⟩ :=
    exists_admissibleBlowup_effectiveCartierCover X
  exact ⟨U, hUc, hUd, blowUp I, blowUpToBase I, hadm⟩

/-- **The argument of [Stacks, Tag 0GTT] at prescribed generic points, for any choice of
chart-twist transition data.** Let `X` be a quasi-compact quasi-separated scheme and let
`η 0, …, η (n-1)` be the generic points of finitely many distinct irreducible components of `X`.
There are a quasi-compact open `U` containing every `η i` and a finite type ideal `I` disjoint
from `U` such that the blowup `blowUp I ⟶ X` is a `U`-admissible blowup and `blowUp I` has an
ample family of invertible modules, as soon as the Rees relative `Proj` of every centre is given
a transition datum `h01NO` for its degree-one twist.

The ample family is [Stacks, Tag 0GTS]
(`Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_isAmpleOnComplement_cover`) applied to the
effective Cartier divisors of `exists_admissibleBlowup_effectiveCartierCover_of_genericPoints` and
to the twist `𝒪_{X'}(1)`, ample relative to the blowup by [Stacks, Tag 02NS] part (2). -/
theorem exists_isCompact_isAdmissibleBlowup_isAmpleFamily_of_genericPoints (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] {n : ℕ} (Z : Fin n → Set X)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hinj : Function.Injective Z) (η : Fin n → X)
    (hη : ∀ i, IsGenericPoint (η i) (Z i))
    (h01NO : ∀ K : X.IdealSheafData, (reesSituation K).TwistTransition 1) :
    ∃ (U : X.Opens) (I : X.IdealSheafData), IsCompact (U : Set X) ∧ (∀ i, η i ∈ U) ∧
      I.IsFiniteType ∧ Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
        ∃ (J : Type u) (N : J → (blowUp I).Modules), (blowUp I).IsAmpleFamily N := by
  classical
  obtain ⟨U, I, m, W, A, hUc, hηU, hIft, hadm, hWaff, hWcover, hDeff, hcompl⟩ :=
    exists_admissibleBlowup_effectiveCartierCover_of_genericPoints X Z hZ hinj η hη
  obtain ⟨L, hLinv, hLrel⟩ := exists_isRelativelyAmple_twist I hIft (h01NO I)
  have := hLinv
  refine ⟨U, I, hUc, hηU, hIft, hadm, ?_⟩
  refine Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_isAmpleOnComplement_cover
    (fun i => (A i).comap (blowUpToBase I)) (fun _ => L) hDeff
    (fun _ => (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      _ _ L).mpr hLinv) ?_ ?_
  · intro x
    obtain ⟨i, hi⟩ := hWcover ((blowUpToBase I).base x)
    exact ⟨i, by rwa [hcompl i]⟩
  · intro i
    have i1 : AlgebraicGeometry.SheafOfModules.IsInvertible
        (blowUpToBase I ⁻¹ᵁ W i).toScheme.toRingedSpace.presheaf
        (structureSheafRing (blowUpToBase I ⁻¹ᵁ W i).toScheme.toRingedSpace).property
        ((Scheme.Modules.pullback (blowUpToBase I ⁻¹ᵁ W i).ι).obj L) :=
      Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
        (blowUpToBase I ⁻¹ᵁ W i).ι.toLRSHom.toShHom L
    have hAmp : AlgebraicGeometry.Scheme.Modules.IsAmple
        (blowUpToBase I ⁻¹ᵁ W i).toScheme
        ((Scheme.Modules.pullback (blowUpToBase I ⁻¹ᵁ W i).ι).obj L) :=
      (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mp
        (hLrel.isAmple_preimage _ _ (W i) (hWaff i))
    let eres := (Scheme.Modules.restrictFunctorIsoPullback (blowUpToBase I ⁻¹ᵁ W i).ι).app L
    have i2 : AlgebraicGeometry.SheafOfModules.IsInvertible
        (blowUpToBase I ⁻¹ᵁ W i).toScheme.toRingedSpace.presheaf
        (structureSheafRing (blowUpToBase I ⁻¹ᵁ W i).toScheme.toRingedSpace).property
        ((Scheme.Modules.restrictFunctor (blowUpToBase I ⁻¹ᵁ W i).ι).obj L) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ eres.symm
    exact isAmpleOnComplement_of_support_compl_eq (hcompl i) i2
      (AlgebraicGeometry.Scheme.Modules.isAmple_of_iso eres.symm hAmp)

/-- **The argument of [Stacks, Tag 0GTT], for any choice of chart-twist transition data.** A
quasi-compact quasi-separated scheme `X` with finitely many irreducible components has a
quasi-compact dense open `U` and a `U`-admissible blowup `X' ⟶ X` such that `X'` has an ample
family of invertible modules, as soon as the Rees relative `Proj` of every centre is given a
transition datum `h01NO` for its degree-one twist.

The ample family is [Stacks, Tag 0GTS]
(`Stacks.AmpleFamilyCartier.exists_isAmpleFamily_of_isAmpleOnComplement_cover`) applied to the
effective Cartier divisors of `exists_admissibleBlowup_effectiveCartierCover` and to the twist
`𝒪_{X'}(1)`, ample relative to the blowup by [Stacks, Tag 02NS] part (2). The transition datum
is supplied by `Stacks.RelativeProj.Situation.twistTransition`, which removes `h01NO` in
`Stacks.DenseOpenAdmissibleBlowup.exists_isCompact_dense_admissibleBlowup_isAmpleFamily`. -/
theorem exists_isCompact_dense_isAdmissibleBlowup_isAmpleFamily (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [Finite (irreducibleComponents X)]
    (h01NO : ∀ K : X.IdealSheafData, (reesSituation K).TwistTransition 1) :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ Dense (U : Set X) ∧
      ∃ (X' : Scheme.{u}) (f : X' ⟶ X), Stacks.Blowup.IsAdmissibleBlowup U f ∧
        ∃ (J : Type u) (N : J → X'.Modules), X'.IsAmpleFamily N := by
  obtain ⟨n, Z, hZ, hinj, η, hη, hdense⟩ := exists_genericPoints_forall_mem_dense X
  obtain ⟨U, I, hUc, hηU, -, hadm, hfam⟩ :=
    exists_isCompact_isAdmissibleBlowup_isAmpleFamily_of_genericPoints X Z hZ hinj η hη h01NO
  exact ⟨U, hUc, hdense U hηU, blowUp I, blowUpToBase I, hadm, hfam⟩

end Stacks.DenseOpenAdmissibleBlowup

end
