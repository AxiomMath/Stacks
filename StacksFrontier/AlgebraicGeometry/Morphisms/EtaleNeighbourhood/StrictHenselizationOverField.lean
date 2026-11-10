module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import StacksCore.FieldTheory.MvRatFunc.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.RingTheory.Henselian.StrictHenselizationColimit
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.OfHenselization
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField
public import StacksFrontier.RingTheory.MvPolynomial.PrimeStandardForm
public import StacksFrontier.RingTheory.NoetherNormalization.Basic
public import StacksFrontier.RingTheory.QuasiFinite.AffineSpaceDimension
public import StacksFrontier.RingTheory.QuasiFinite.BaseChange
public import StacksFrontier.RingTheory.QuasiFinite.Basic
public import StacksFrontier.RingTheory.QuasiFinite.Dimension
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples

/-!
# Strict henselizations of finite-type schemes over a field

At a point `x` of a scheme `X` of finite type over a field `K`, the strict henselization of
the local ring receives a map from a separable closure of a rational function field in
`trdeg_K κ(x)` variables. The induced residue-field extension is purely inseparable, and the
strict henselization is a filtered colimit of finite-type algebras whose Krull dimensions are
bounded by the local dimension of `X` at `x` minus that transcendence degree.

## Main definitions

* `AlgebraicGeometry.IsFilteredColimitOfFiniteTypeAlgebrasWithDimensionAddLE` records a
  filtered-colimit presentation by finite-type algebras whose Krull dimensions, after adding
  `a`, are at most `d`.

## Main results

* `AlgebraicGeometry.exists_strictHenselization_map_of_finiteType` constructs the map into a
  strict henselization and gives its residue-field and filtered-colimit properties.

## Implementation notes

The number of variables is represented by a type `ι` whose cardinality is the transcendence
degree, so that `MvRatFunc ι K` is the source's `K(t₁, …, t_a)`. Since subtraction is not
available on `WithBot ℕ∞`, the bound `dim B ≤ d - a` is expressed equivalently as
`dim B + a ≤ d`; this is what the filtered-colimit predicate records, and it is stated for an
arbitrary pair of algebras rather than only for the geometric situation at hand. A strict
henselization is represented by an algebra satisfying `IsLocalRing.IsHenselization` with
respect to a separable closure of the residue field. The displayed map is a `K`-algebra map;
the two scalar-tower hypotheses identify its restriction to `K` with the structural map
through the local ring of `X` at `x`.

## References

* [Stacks Project, Tag 0F0U](https://stacks.math.columbia.edu/tag/0F0U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A local algebra over a field whose residue field is a field extension of it receives a
map from a rational function field on a transcendence basis of the residue extension, over
which the residue field is algebraic. -/
private theorem exists_mvRatFunc_map_to_localRing
    (K A : Type u) [Field K] [CommRing A] [IsLocalRing A]
    [Algebra K A] [Algebra K (IsLocalRing.ResidueField A)]
    [FaithfulSMul K (IsLocalRing.ResidueField A)]
    (hbase : algebraMap K (IsLocalRing.ResidueField A) =
      (IsLocalRing.residue A).comp (algebraMap K A)) :
    ∃ (ι : Type u) (ψ : MvRatFunc ι K →ₐ[K] A)
      (χ : MvRatFunc ι K →ₐ[K] IsLocalRing.ResidueField A),
      Cardinal.mk ι = Algebra.trdeg K (IsLocalRing.ResidueField A) ∧
        (IsLocalRing.residue A).comp ψ.toRingHom = χ.toRingHom ∧
        letI : Algebra (MvRatFunc ι K) (IsLocalRing.ResidueField A) := χ.toRingHom.toAlgebra
        Algebra.IsAlgebraic (MvRatFunc ι K) (IsLocalRing.ResidueField A) := by
  classical
  let F := IsLocalRing.ResidueField A
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' K F
  let liftx : ι → A := fun i => Classical.choose (IsLocalRing.residue_surjective (x i))
  have hliftx : ∀ i, IsLocalRing.residue A (liftx i) = x i := fun i =>
    Classical.choose_spec (IsLocalRing.residue_surjective (x i))
  let ralg : A →ₐ[K] F :=
    { toRingHom := IsLocalRing.residue A
      commutes' := fun k => by
        have hh := congrFun (congrArg DFunLike.coe hbase) k
        change algebraMap K F k = IsLocalRing.residue A (algebraMap K A k) at hh
        exact hh.symm }
  let φp : MvPolynomial ι K →ₐ[K] A := MvPolynomial.aeval liftx
  let ψp : MvPolynomial ι K →ₐ[K] F := MvPolynomial.aeval x
  have hcomp : ralg.comp φp = ψp := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ralg, φp, ψp, hliftx]
  have hψinj : Function.Injective ψp :=
    (algebraicIndependent_iff_injective_aeval.mp hx.1)
  have hval (p : MvPolynomial ι K) : ralg (φp p) = ψp p := by
    have hh := congrArg (fun g : MvPolynomial ι K →ₐ[K] F => g p) hcomp
    simpa only [AlgHom.comp_apply] using hh
  have hunit (y : nonZeroDivisors (MvPolynomial ι K)) : IsUnit (φp y.1) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (φp y.1)).mp
    have hy : y.1 ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
    have hne : ψp y.1 ≠ 0 := by
      intro hzero
      apply hy
      apply hψinj
      simpa using hzero
    change ralg (φp y.1) ≠ 0
    rw [hval y.1]
    exact hne
  let f : MvRatFunc ι K →+* A := IsLocalization.lift hunit
  have hconst : f.comp (algebraMap K (MvRatFunc ι K)) = algebraMap K A := by
    ext k
    change f (algebraMap K (MvRatFunc ι K) k) = _
    rw [show algebraMap K (MvRatFunc ι K) k =
      algebraMap (MvPolynomial ι K) (MvRatFunc ι K) (MvPolynomial.C k) by rfl]
    rw [IsLocalization.lift_eq hunit]
    simp [φp]
  let ψ : MvRatFunc ι K →ₐ[K] A :=
    { toRingHom := f
      commutes' := fun k => DFunLike.congr_fun hconst k }
  let H := IntermediateField.adjoin K (Set.range x)
  let e : MvRatFunc ι K ≃ₐ[K] H := hx.1.aevalEquivField
  let : Algebra H F := (IntermediateField.val H).toRingHom.toAlgebra
  let : Algebra (MvRatFunc ι K) H := e.toRingHom.toAlgebra
  let : Algebra (MvRatFunc ι K) F :=
    ((IntermediateField.val H).toRingHom.comp e.toRingHom).toAlgebra
  let χ : MvRatFunc ι K →ₐ[K] F :=
    { toRingHom := (IntermediateField.val H).toRingHom.comp e.toRingHom
      commutes' := fun k => by simp }
  have hres : (IsLocalRing.residue A).comp ψ.toRingHom = χ.toRingHom := by
    have hrestrict :
        ((IsLocalRing.residue A).comp ψ.toRingHom).comp
            (algebraMap (MvPolynomial ι K) (MvRatFunc ι K)) =
          χ.toRingHom.comp (algebraMap (MvPolynomial ι K) (MvRatFunc ι K)) := by
      apply RingHom.ext
      intro p
      change IsLocalRing.residue A (f (algebraMap (MvPolynomial ι K) (MvRatFunc ι K) p)) =
        χ (algebraMap (MvPolynomial ι K) (MvRatFunc ι K) p)
      rw [IsLocalization.lift_eq hunit]
      change ralg (φp p) = _
      rw [hval]
      change (MvPolynomial.aeval x) p =
        (IntermediateField.val H) (e (algebraMap (MvPolynomial ι K)
          (MvRatFunc ι K) p))
      exact (hx.1.aevalEquivField_algebraMap_apply_coe p).symm
    exact IsLocalization.ringHom_ext
      (M := nonZeroDivisors (MvPolynomial ι K)) hrestrict
  have hscalar : IsScalarTower (MvRatFunc ι K) H F := .of_algebraMap_eq fun _ => rfl
  let := hscalar
  let : Algebra.IsAlgebraic (MvRatFunc ι K) H :=
    (Algebra.isIntegral_of_surjective e.surjective).isAlgebraic
  let : Algebra.IsAlgebraic H F := hx.isAlgebraic_field
  have hAlgF : Algebra.IsAlgebraic (MvRatFunc ι K) F :=
    @Algebra.IsAlgebraic.trans (MvRatFunc ι K) H F _ _ _ _ _ _ hscalar _ _ _
  exact ⟨ι, ψ, χ, hx.cardinalMk_eq_trdeg, hres, hAlgF⟩

/-- A separable closure of a field maps into a separable closure of an algebraic extension
of it, and the latter is purely inseparable over the image. -/
private theorem sepClosure_over_algebraic_extension_is_purelyInseparable
    (F κ E L : Type*) [Field F] [Field κ] [Field E] [Field L]
    [Algebra F κ] [Algebra F E] [Algebra κ L] [Algebra F L]
    [IsScalarTower F κ L] [IsSepClosure F E] [IsSepClosure κ L]
    (hFK : Algebra.IsAlgebraic F κ) :
    ∃ g : E →ₐ[F] L,
      letI : Algebra E L := g.toRingHom.toAlgebra
      IsPurelyInseparable E L := by
  classical
  let : Algebra.IsAlgebraic F κ := hFK
  let : Algebra.IsSeparable κ L := IsSepClosure.isSeparable
  let : Algebra.IsAlgebraic κ L := Algebra.IsSeparable.isAlgebraic κ L
  let : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.trans F κ L
  let : IsSepClosed L := IsSepClosure.sep_closed κ (K := L)
  let g : E →ₐ[F] L := IsSepClosed.lift (K := F) (L := E) (M := L)
  let : Algebra E L := g.toRingHom.toAlgebra
  let : IsScalarTower F E L :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  let : IsSepClosed E := IsSepClosure.sep_closed F (K := E)
  let : Algebra.IsAlgebraic E L := Algebra.IsAlgebraic.tower_top (K := F) E
  exact ⟨g, Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed⟩

/-- An algebra is a filtered colimit of finite-type algebras whose Krull dimensions, after
adding `a`, are bounded by `d`. This is the subtraction-free form of the bound
`ringKrullDim B ≤ d - a`. -/
def IsFilteredColimitOfFiniteTypeAlgebrasWithDimensionAddLE
    (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (a d : WithBot ℕ∞) : Prop :=
  ∃ (I : Type (u + 1)) (_ : SmallCategory I) (_ : IsFiltered I)
    (F : I ⥤ CommAlgCat.{u} k) (c : Cocone F),
    Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ CommAlgCat.of k A) ∧
      ∀ i, Algebra.FiniteType k (F.obj i) ∧
        ringKrullDim (F.obj i) + a ≤ d

/-- Monotonicity of `Cardinal.toENat`, stated in `WithBot ℕ∞`. -/
private theorem coe_toENat_le_coe_toENat {a b : Cardinal} (h : a ≤ b) :
    (Cardinal.toENat a : WithBot ℕ∞) ≤ Cardinal.toENat b :=
  WithBot.coe_le_coe.mpr (Cardinal.toENat.monotone' h)

/-- The Krull dimension of a finite-type algebra over a field is at most the transcendence
degree of the algebra over the field. -/
private theorem ringKrullDim_le_toENat_trdeg (K B : Type u) [Field K] [CommRing B]
    [Nontrivial B] [Algebra K B] [Algebra.FiniteType K B] :
    ringKrullDim B ≤ (Cardinal.toENat (Algebra.trdeg K B) : WithBot ℕ∞) := by
  obtain ⟨n, f, hn, hi, hf⟩ := noether_normalization_global (k := K) (T := B)
  have h := lift_trdeg_le_of_injective f hi
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fin, Cardinal.lift_natCast,
    Cardinal.lift_id] at h
  rw [← hn]
  simpa using coe_toENat_le_coe_toENat h

/-- For a finite-type domain over a field the transcendence degree is at most the Krull
dimension, so the two agree. -/
private theorem toENat_trdeg_le_ringKrullDim (K B : Type u) [Field K] [CommRing B]
    [Nontrivial B] [Algebra K B] [Algebra.FiniteType K B] :
    (Cardinal.toENat (Algebra.trdeg K B) : WithBot ℕ∞) ≤ ringKrullDim B := by
  classical
  obtain ⟨n, f, hn, hi, hf⟩ := noether_normalization_global (k := K) (T := B)
  suffices h : Algebra.trdeg K B ≤ n by
    rw [← hn]
    simpa using coe_toENat_le_coe_toENat h
  rw [Algebra.trdeg]
  apply ciSup_le'
  intro s
  let P := MvPolynomial s.1 K
  let φ : P →ₐ[K] B := MvPolynomial.aeval (Subtype.val : s.1 → B)
  have hφ : Function.Injective φ := algebraicIndependent_iff_injective_aeval.mp s.2
  obtain ⟨q, -, hq, hqφ⟩ := Ideal.exists_ideal_comap_le_prime
    (f := φ.toRingHom) (⊥ : Ideal P) (⊥ : Ideal B)
      (fun z hz => hφ (by simpa using (hz : φ z = 0)))
  let ψ : P →ₐ[K] B ⧸ q := (Ideal.Quotient.mkₐ K q).comp φ
  have hψ : Function.Injective ψ := (injective_iff_map_eq_zero _).2 fun z hz =>
    hqφ (Ideal.Quotient.eq_zero_iff_mem (a := φ z) (I := q) |>.mp hz)
  have hle := lift_trdeg_le_of_injective ψ hψ
  simp only [P, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at hle
  have hfrac := trdeg_le_of_injective (IsScalarTower.toAlgHom K (B ⧸ q)
    (FractionRing (B ⧸ q))) (IsFractionRing.injective (B ⧸ q) (FractionRing (B ⧸ q)))
  have hb : (Cardinal.toENat (Cardinal.mk s.1) : WithBot ℕ∞) ≤ n := by
    calc
      _ ≤ (Cardinal.toENat (Algebra.trdeg K (FractionRing (B ⧸ q))) : WithBot ℕ∞) :=
        coe_toENat_le_coe_toENat (hle.trans hfrac)
      _ = ringKrullDim (B ⧸ q) :=
        (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, u, u, 0}
          K (B ⧸ q) (FractionRing (B ⧸ q))).1.symm
      _ ≤ ringKrullDim B := ringKrullDim_quotient_le q
      _ = n := hn.symm
  exact (Cardinal.toENat_le_natCast).mp (by exact_mod_cast hb)

/-- An algebra which is the directed union of its finite-type subalgebras of bounded
dimension is a filtered colimit of finite-type algebras with that dimension bound. -/
private theorem isFilteredColimit_of_subalgebra_dim_le
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    (a d : WithBot ℕ∞)
    (h : ∀ S : Subalgebra k A, S.FG → ringKrullDim S + a ≤ d) :
    IsFilteredColimitOfFiniteTypeAlgebrasWithDimensionAddLE k A a d := by
  let e := commAlgCatEquivUnder (.of k)
  let P : ObjectProperty (Under (CommRingCat.of k)) := fun B =>
    B.hom.hom.FiniteType ∧ ringKrullDim B.right + a ≤ d
  have hind : P.ind.{u} (e.functor.obj (CommAlgCat.of k A)) := by
    apply (CommRingCat.ind_under_iff_exists_factorization _ (E := P) (fun B hB => ?_)).2
    · intro B hB f
      let : Algebra k B := B.hom.hom.toAlgebra
      let φ : B →ₐ[k] A :=
        { toRingHom := f.right.hom
          commutes' := fun z => ConcreteCategory.congr_hom (Under.w f) z }
      let : Algebra.FinitePresentation k B := hB
      let : Algebra.FiniteType k B := inferInstance
      have hft : Algebra.FiniteType k φ.range :=
        Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
      have hfg : φ.range.FG := (Subalgebra.fg_iff_finiteType _).mpr hft
      let C := e.functor.obj (CommAlgCat.of k φ.range)
      let g : B ⟶ C := φ.rangeRestrict.toUnder
      let h' : C ⟶ e.functor.obj (CommAlgCat.of k A) := φ.range.val.toUnder
      refine ⟨C, g, h', ?_, ?_, h φ.range hfg⟩
      · ext z
        rfl
      · change (algebraMap k φ.range).FiniteType
        exact RingHom.finiteType_algebraMap.mpr hft
    · exact RingHom.FinitePresentation.of_finiteType.mp hB.1
  obtain ⟨J, _, _, pres, hp⟩ := hind
  let pres' := (pres.map e.inverse).ofIso (e.unitIso.app (CommAlgCat.of k A)).symm
  let Q : ObjectProperty (CommAlgCat.{u} k) := fun B =>
    Algebra.FiniteType k B ∧ ringKrullDim B + a ≤ d
  have hind' : Q.ind.{u + 1} (CommAlgCat.of k A) :=
    ObjectProperty.of_essentiallySmall_index pres' (fun j => ⟨(hp j).1, (hp j).2⟩)
  obtain ⟨I, _, _, pres'', hpres''⟩ := hind'
  exact ⟨I, inferInstance, inferInstance, pres''.diag, pres''.cocone,
    ⟨pres''.isColimit⟩, ⟨Iso.refl _⟩, hpres''⟩

/-- An algebra whose transcendence degree over the base is bounded is a filtered colimit of
finite-type algebras obeying the corresponding dimension bound. -/
private theorem isFilteredColimit_of_trdeg_le
    (K E A : Type u) [Field K] [Field E] [CommRing A] [Nontrivial A]
    [Algebra K E] [Algebra E A] [Algebra K A] [IsScalarTower K E A]
    (a d : WithBot ℕ∞)
    (ha : a ≤ (Cardinal.toENat (Algebra.trdeg K E) : WithBot ℕ∞))
    (hd : (Cardinal.toENat (Algebra.trdeg K A) : WithBot ℕ∞) ≤ d) :
    IsFilteredColimitOfFiniteTypeAlgebrasWithDimensionAddLE E A a d := by
  apply isFilteredColimit_of_subalgebra_dim_le
  intro S hS
  let : Algebra.FiniteType E S := (Subalgebra.fg_iff_finiteType S).mp hS
  calc
    ringKrullDim S + a ≤
        (Cardinal.toENat (Algebra.trdeg E S) : WithBot ℕ∞) +
        (Cardinal.toENat (Algebra.trdeg K E) : WithBot ℕ∞) :=
      add_le_add (ringKrullDim_le_toENat_trdeg E S) ha
    _ ≤ (Cardinal.toENat (Algebra.trdeg E A) : WithBot ℕ∞) +
        (Cardinal.toENat (Algebra.trdeg K E) : WithBot ℕ∞) := by
      gcongr
      exact coe_toENat_le_coe_toENat (trdeg_le_of_injective S.val Subtype.val_injective)
    _ = (Cardinal.toENat (Algebra.trdeg K E + Algebra.trdeg E A) : WithBot ℕ∞) := by
      rw [map_add, WithBot.coe_add, add_comm]
    _ ≤ (Cardinal.toENat (Algebra.trdeg K A) : WithBot ℕ∞) :=
      coe_toENat_le_coe_toENat (trdeg_add_le (R := K) (S := E) (A := A))
    _ ≤ d := hd

/-- A finite set of elements of the apex of a colimit cocone over a filtered category comes
from a single object of the diagram. -/
private theorem exists_rep_finite {R : Type u} [CommRing R]
    {J : Type u} [Category J] [IsFiltered J] {F : J ⥤ CommAlgCat.{u} R}
    (c : Cocone F) (hc : IsColimit c) {ι : Type*} [Finite ι] (x : ι → (c.pt : Type u)) :
    ∃ j : J, ∃ y : ι → (F.obj j : Type u), ∀ i, (c.ι.app j).hom (y i) = x i := by
  classical
  let := Fintype.ofFinite ι
  have : Nonempty J := IsFiltered.nonempty
  choose j y hy using fun i => CommAlgCat.exists_app_eq hc (x i)
  obtain ⟨k, hk⟩ := (CommAlgCat.directed_range c).finset_le (Finset.univ.image j)
  exact ⟨k, fun i => (hk (j i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    ⟨y i, hy i⟩).choose, fun i => (hk (j i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    ⟨y i, hy i⟩).choose_spec⟩

/-- An ind-étale algebra over a local ring has transcendence degree over the base field
bounded by that of the base. -/
private theorem toENat_trdeg_le_of_ind_etale
    (K B A : Type u) [Field K] [CommRing B] [Nontrivial B] [CommRing A] [Nontrivial A]
    [Algebra K B] [Algebra B A] [Algebra K A] [IsScalarTower K B A]
    [Algebra.FiniteType K B]
    (hind : (CommAlgCat.etale.{u} B).ind.{u} (CommAlgCat.of B A)) :
    (Cardinal.toENat (Algebra.trdeg K A) : WithBot ℕ∞) ≤ ringKrullDim B := by
  classical
  obtain ⟨n, φ, hn, -, -⟩ := noether_normalization_global (k := K) (T := B)
  rw [← hn]
  apply WithBot.coe_le_coe.mpr
  apply Cardinal.toENat_le_natCast.mpr
  rw [Algebra.trdeg]
  apply ciSup_le'
  intro t
  refine algebraicIndependent_bounded_of_finset_algebraicIndependent_bounded ?_ t.1 t.2
  intro s hs
  obtain ⟨J, _, _, pres, hp⟩ := hind
  obtain ⟨j, y, hy⟩ := exists_rep_finite pres.cocone pres.isColimit (Subtype.val : s → A)
  let D := pres.diag.obj j
  let g : D →ₐ[B] A := (pres.ι.app j).hom
  let : Nontrivial D := g.toRingHom.domain_nontrivial
  let : Algebra K D := ((algebraMap B D).comp (algebraMap K B)).toAlgebra
  let : IsScalarTower K B D := .of_algebraMap_eq' rfl
  let : Algebra.Etale B D := hp j
  let : Algebra.FiniteType K D :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K B) inferInstance
  have hD : ringKrullDim D ≤ ringKrullDim B :=
    (ringKrullDim_le_iff_height_le _).2 fun {q} _ =>
      (WithBot.coe_le_coe.2
        (Ideal.height_le_height_of_liesOver_of_quasiFiniteAt (q.under B) q)).trans
      Ideal.height_le_ringKrullDim_of_isPrime
  let f : D →ₐ[K] A := g.restrictScalars K
  have hyind : AlgebraicIndependent K y := AlgebraicIndependent.of_comp f (by
    rwa [show ⇑f ∘ y = Subtype.val from funext hy])
  have hbound : (Cardinal.toENat (Cardinal.mk s) : WithBot ℕ∞) ≤ n :=
    (coe_toENat_le_coe_toENat hyind.cardinalMk_le_trdeg).trans
      ((toENat_trdeg_le_ringKrullDim K D).trans (hD.trans_eq hn.symm))
  simpa using hbound

/-- The transcendence degree of a strict henselization of the local ring of a finite-type
scheme over a field is at most the local dimension of the scheme at the point. -/
private theorem toENat_trdeg_henselization_le_topologicalKrullDimAt
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (x : X)
    (R : Type u) [CommRing R] [Nontrivial R]
    [Algebra (X.presheaf.stalk x) R]
    (hind : (CommAlgCat.etale.{u} (X.presheaf.stalk x)).ind.{u}
      (CommAlgCat.of (X.presheaf.stalk x) R)) :
    letI := (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
    letI : Algebra K R := ((algebraMap (X.presheaf.stalk x) R).comp
      (algebraMap K (X.presheaf.stalk x))).toAlgebra
    (Cardinal.toENat (Algebra.trdeg K R) : WithBot ℕ∞) ≤ topologicalKrullDimAt X x := by
  let A := X.presheaf.stalk x
  let : Algebra K A := (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
  let : Algebra K R := ((algebraMap A R).comp (algebraMap K A)).toAlgebra
  let : IsScalarTower K A R := .of_algebraMap_eq' rfl
  unfold topologicalKrullDimAt
  apply le_iInf
  intro U
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open U.2.1 U.2.2
  let B := Γ(X, V)
  let : Algebra B A := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let : Nontrivial B := (algebraMap B A).domain_nontrivial
  let : Algebra K B := (((Scheme.ΓSpecIso (.of K)).inv ≫
    f.appLE ⊤ V (by simp)).hom).toAlgebra
  have : Algebra.FiniteType K B := by
    change (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ V (by simp)).hom).FiniteType
    exact RingHom.FiniteType.comp
      (f.finiteType_appLE (isAffineOpen_top _) hV _)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have : IsScalarTower K B A := by
    apply IsScalarTower.of_algebraMap_eq'
    change (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom) =
      (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appLE ⊤ V (by simp) ≫
      X.presheaf.germ V x hxV).hom)
    apply congrArg CommRingCat.Hom.hom
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  let : Algebra B R := ((algebraMap A R).comp (algebraMap B A)).toAlgebra
  let : IsScalarTower B A R := .of_algebraMap_eq' rfl
  let : IsScalarTower K B R := .of_algebraMap_eq fun k => by
    change algebraMap A R (algebraMap K A k) =
      algebraMap A R (algebraMap B A (algebraMap K B k))
    rw [IsScalarTower.algebraMap_apply K B A]
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let : q.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  let : IsLocalization.AtPrime A q := hV.isLocalization_stalk ⟨x, hxV⟩
  have hindB := CommAlgCat.ind_etale_comp (CommAlgCat.ind_etale_atPrime B A q) hind
  refine (toENat_trdeg_le_of_ind_etale K B R hindB).trans ?_
  have hdim : ringKrullDim B = topologicalKrullDim V := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hV.isoSpec)).isHomeomorph).symm
  rw [hdim]
  exact Topology.IsInducing.topologicalKrullDim_le
    (Topology.IsEmbedding.inclusion hVU).isInducing

/-- A local ring admits a henselization relative to any separably closed extension of its
residue field. -/
@[sga "4 VIII 4.4"]
private theorem exists_henselization_over_localRing
    (A L : Type u) [CommRing A] [IsLocalRing A] [Field L]
    [Algebra (ResidueField A) L] [IsSepClosure (ResidueField A) L] :
    ∃ Rsh : Type u, ∃ (_ : CommRing Rsh) (_ : IsLocalRing Rsh) (_ : Algebra A Rsh),
      IsLocalRing.IsHenselization A L Rsh := by
  let : Algebra A A := Algebra.id A
  have hind : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A A) :=
    (CommAlgCat.etale A).le_ind _ (inferInstanceAs (Algebra.Etale A A))
  have hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap A A)) :=
    fun z => ⟨z, by simp⟩
  obtain ⟨Rsh, hCR, hLR, hAR, _, _, _, hHens, _, hInd, _, he⟩ :=
    IsLocalRing.exists_strictHenselization A A hind hres L
  let : CommRing Rsh := hCR
  let : IsLocalRing Rsh := hLR
  let : Algebra A Rsh := hAR
  exact ⟨Rsh, hCR, hLR, hAR, IsLocalRing.IsHenselization.of_ind_etale hHens hInd he⟩

/-- A field is its own residue field. -/
private noncomputable def residueFieldEquivOfField (F : Type u) [Field F] :
    F ≃+* IsLocalRing.ResidueField F :=
  RingEquiv.ofBijective (IsLocalRing.residue F)
    ⟨(IsLocalRing.residue F).injective, IsLocalRing.residue_surjective⟩

/-- A separable algebraic extension of fields is ind-étale. -/
private theorem sepClosure_is_ind_etale (F E : Type u) [Field F] [Field E]
    [Algebra F E] [IsSepClosure F E] :
    (CommAlgCat.etale.{u} F).ind.{u} (CommAlgCat.of F E) := by
  classical
  let hF : IsHenselization F (IsLocalRing.ResidueField F) F := by
    apply IsLocalRing.IsHenselization.of_ind_etale inferInstance
      ((CommAlgCat.etale F).le_ind _ (inferInstanceAs (Algebra.Etale F F)))
    exact ⟨RingEquiv.refl _, fun _ => rfl⟩
  let eκ : IsLocalRing.ResidueField F ≃+* F := (residueFieldEquivOfField F).symm
  let : Algebra (IsLocalRing.ResidueField F) E :=
    ((algebraMap F E).comp eκ.toRingHom).toAlgebra
  have hsepκ : IsSepClosure (IsLocalRing.ResidueField F) E := by
    refine ⟨IsSepClosure.sep_closed F (K := E), ?_⟩
    exact Algebra.IsSeparable.of_equiv_equiv
      (A₁ := F) (B₁ := E) (A₂ := IsLocalRing.ResidueField F) (B₂ := E)
      eκ.symm (RingEquiv.refl E) (by
      ext x
      simp [eκ, RingHom.algebraMap_toAlgebra])
  let := hF
  obtain ⟨_, _, _, U, _, _, hAlgFU₁, hAlgFU₂, _, A, _, ι, _, _, _, _, hιcompat, hιinj,
      hcover, hhens, hsepU, hURh, hUR⟩ :=
    IsLocalRing.IsHenselization.exists_strictHenselization_iUnion_finiteEtale.{u, u}
      F F E
  let : Algebra F U := hAlgFU₂
  have hfieldStage (L : IsLocalRing.FiniteIntermediateField
      (IsLocalRing.ResidueField F) E) : Nonempty (IsField (A L)) := by
    let : IsArtinianRing (A L) := IsArtinianRing.of_finite F (A L)
    let : IsReduced (A L) := Algebra.FormallyUnramified.isReduced_of_field F (A L)
    exact ⟨IsArtinianRing.isField_of_isReduced_of_isLocalRing (A L)⟩
  have hmax : IsLocalRing.maximalIdeal U = ⊥ := by
    apply le_antisymm
    · intro z hz
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
      obtain ⟨L, a, ha⟩ := hcover z
      rcases eq_or_ne a 0 with ha0 | ha0
      · rw [← ha, ha0, map_zero]
        exact Ideal.zero_mem _
      · have hf := (hfieldStage L).some
        obtain ⟨b, hb⟩ := hf.mul_inv_cancel ha0
        have hua : IsUnit a := by
          refine ⟨⟨a, b, hb, ?_⟩, rfl⟩
          exact (hf.mul_comm b a).trans hb
        have huz : IsUnit z := by
          rw [← ha]
          exact RingHom.isUnit_map (AlgHom.toRingHom (ι L)) hua
        exact (hz huz).elim
    · exact bot_le
  let : Algebra F U := hAlgFU₁
  obtain ⟨ε, hε⟩ := hUR.exists_residueFieldEquiv
    (R := F) (L := E) (Rh := U)
  have hrUinj : Function.Injective (IsLocalRing.residue U) := by
    intro x y hxy
    have hmem : x - y ∈ IsLocalRing.maximalIdeal U := by
      apply (IsLocalRing.residue_eq_zero_iff _).mp
      rw [map_sub, hxy, sub_self]
    rw [hmax] at hmem
    exact sub_eq_zero.mp hmem
  let rU : U ≃+* IsLocalRing.ResidueField U :=
    RingEquiv.ofBijective (IsLocalRing.residue U)
      ⟨hrUinj, IsLocalRing.residue_surjective⟩
  let eEU : E ≃+* U := ε.trans rU.symm
  have hbase (x : F) : algebraMap (IsLocalRing.ResidueField F) E
      (IsLocalRing.residue F x) = algebraMap F E x := by
    change algebraMap F E (eκ (IsLocalRing.residue F x)) = _
    have hh : eκ.symm x = IsLocalRing.residue F x := rfl
    rw [← hh, eκ.apply_symm_apply]
  let eAlg : E ≃ₐ[F] U := AlgEquiv.ofRingEquiv (f := eEU) (by
    intro x
    apply rU.injective
    change rU (rU.symm (ε (algebraMap F E x))) =
      rU (algebraMap F U x)
    rw [RingEquiv.apply_symm_apply, ← hbase x]
    change ε (algebraMap (IsLocalRing.ResidueField F) E (IsLocalRing.residue F x)) =
      IsLocalRing.residue U (algebraMap F U x)
    exact hε x)
  have hUind := (CommAlgCat.etale F).ind.prop_of_iso
    (CommAlgCat.isoMk (ULift.algEquiv : ULift.{u} U ≃ₐ[F] U)) hUR.ind_etale
  exact (CommAlgCat.etale F).ind.prop_of_iso (CommAlgCat.isoMk eAlg.symm) hUind

/-- **Stacks Project, Tag 0F0U.** At a point `x` of a finite-type `K`-scheme, a strict
henselization of the local ring admits a map from a separable closure of a rational function
field in `trdeg K κ(x)` variables. The induced residue-field extension is purely inseparable,
and the strict henselization is a filtered colimit of finite-type algebras of dimension at most
`dimₓ(X) - trdeg K κ(x)`. -/
@[stacks 0F0U]
theorem exists_strictHenselization_map_of_finiteType
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] [QuasiCompact f] (x : X) :
    letI := (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
    letI := (((Scheme.ΓSpecIso (.of K)).inv ≫
      (Spec (.of K)).presheaf.germ ⊤ (f x) trivial ≫
      (Spec (.of K)).residue (f x) ≫ f.residueFieldMap x).hom).toAlgebra
    ∃ (ι E Rsh L : Type u)
      (_ : Field E) (_ : Algebra K E) (_ : Algebra (MvRatFunc ι K) E)
      (_ : IsScalarTower K (MvRatFunc ι K) E)
      (_ : IsSepClosure (MvRatFunc ι K) E)
      (_ : CommRing Rsh) (_ : IsLocalRing Rsh)
      (_ : Algebra K Rsh) (_ : Algebra (X.presheaf.stalk x) Rsh)
      (_ : IsScalarTower K (X.presheaf.stalk x) Rsh)
      (_ : Field L) (_ : Algebra (ResidueField (X.presheaf.stalk x)) L)
      (_ : IsSepClosure (ResidueField (X.presheaf.stalk x)) L),
      Cardinal.mk ι = Algebra.trdeg K (X.residueField x) ∧
      IsLocalRing.IsHenselization (X.presheaf.stalk x) L Rsh ∧
      ∃ e : E →ₐ[K] Rsh,
        letI := ((residue Rsh).comp e.toRingHom).toAlgebra
        IsPurelyInseparable E (ResidueField Rsh) ∧
          letI := e.toAlgebra
          IsFilteredColimitOfFiniteTypeAlgebrasWithDimensionAddLE E Rsh
            (Cardinal.toENat (Cardinal.mk ι)) (topologicalKrullDimAt X x) := by
  classical
  let A := X.presheaf.stalk x
  let : Algebra K A := (((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
  let : Algebra K (ResidueField A) := (((Scheme.ΓSpecIso (.of K)).inv ≫
    (Spec (.of K)).presheaf.germ ⊤ (f x) trivial ≫
    (Spec (.of K)).residue (f x) ≫ f.residueFieldMap x).hom).toAlgebra
  have hbase : algebraMap K (ResidueField A) =
      (IsLocalRing.residue A).comp (algebraMap K A) := by
    have hcat :
        (Scheme.ΓSpecIso (.of K)).inv ≫
            (Spec (.of K)).presheaf.germ ⊤ (f x) trivial ≫
            (Spec (.of K)).residue (f x) ≫ f.residueFieldMap x =
          (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
            X.presheaf.germ ⊤ x (by simp) ≫ X.residue x := by
      calc
        _ = (Scheme.ΓSpecIso (.of K)).inv ≫
            (Spec (.of K)).Γevaluation (f x) ≫ f.residueFieldMap x := by
              simp [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
        _ = (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ X.Γevaluation x := by
              rw [Scheme.Γevaluation_naturality]
        _ = _ := by simp [Scheme.Γevaluation, Scheme.evaluation]
    change CommRingCat.Hom.hom
        ((Scheme.ΓSpecIso (.of K)).inv ≫
          (Spec (.of K)).presheaf.germ ⊤ (f x) trivial ≫
          (Spec (.of K)).residue (f x) ≫ f.residueFieldMap x) =
      CommRingCat.Hom.hom
        ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
          X.presheaf.germ ⊤ x (by simp) ≫ X.residue x)
    exact congrArg CommRingCat.Hom.hom hcat
  obtain ⟨ι, φ, χ, hcard, hres, hAlgF⟩ :=
    exists_mvRatFunc_map_to_localRing K A hbase
  let F := MvRatFunc ι K
  let E := SeparableClosure F
  let L := SeparableClosure (ResidueField A)
  let : Field E := inferInstance
  let : Algebra F E := inferInstance
  let : IsSepClosure F E := inferInstance
  let : Field L := inferInstance
  let : Algebra (ResidueField A) L := inferInstance
  let : IsSepClosure (ResidueField A) L := inferInstance
  let : Algebra F (ResidueField A) := χ.toRingHom.toAlgebra
  let : Algebra F L :=
    ((algebraMap (ResidueField A) L).comp χ.toRingHom).toAlgebra
  let : IsScalarTower F (ResidueField A) L := .of_algebraMap_eq' rfl
  have hAlgebraic : Algebra.IsAlgebraic F (ResidueField A) := hAlgF
  obtain ⟨g, hg⟩ :=
    sepClosure_over_algebraic_extension_is_purelyInseparable F (ResidueField A) E L hAlgebraic
  obtain ⟨Rsh, hCR, hLR, hAR, hsh⟩ := exists_henselization_over_localRing A L
  let : Algebra F A := φ.toRingHom.toAlgebra
  let : Algebra F Rsh := ((algebraMap A Rsh).comp φ.toRingHom).toAlgebra
  let : IsScalarTower F A Rsh := .of_algebraMap_eq' rfl
  obtain ⟨εL, hεL⟩ := hsh.exists_residueFieldEquiv (R := A) (L := L) (Rh := Rsh)
  let eEκ := residueFieldEquivOfField E
  let φres : IsLocalRing.ResidueField E →+* IsLocalRing.ResidueField Rsh :=
    εL.toRingHom.comp (g.toRingHom.comp eEκ.symm.toRingHom)
  have hφres : φres.comp ((IsLocalRing.residue E).comp (algebraMap F E)) =
      (IsLocalRing.residue Rsh).comp (algebraMap F Rsh) := by
    apply RingHom.ext
    intro z
    change εL (g (eEκ.symm (IsLocalRing.residue E (algebraMap F E z)))) =
      IsLocalRing.residue Rsh (algebraMap F Rsh z)
    have hz : eEκ.symm (IsLocalRing.residue E (algebraMap F E z)) =
        algebraMap F E z := by
      change eEκ.symm (eEκ (algebraMap F E z)) = _
      exact eEκ.symm_apply_apply _
    rw [hz, g.commutes]
    change εL (algebraMap (ResidueField A) L (χ z)) =
      IsLocalRing.residue Rsh (algebraMap A Rsh (φ z))
    have hresz := DFunLike.congr_fun hres z
    change IsLocalRing.residue A (φ z) = χ z at hresz
    rw [← hresz]
    exact hεL (φ z)
  let : Algebra K Rsh := ((algebraMap A Rsh).comp (algebraMap K A)).toAlgebra
  let : IsScalarTower K A Rsh := .of_algebraMap_eq' rfl
  let : HenselianLocalRing Rsh := hsh.henselian
  have hindE := (CommAlgCat.etale F).ind.prop_of_iso
    (CommAlgCat.isoMk (ULift.algEquiv.symm : E ≃ₐ[F] ULift.{u} E))
    (sepClosure_is_ind_etale F E)
  obtain ⟨eF, ⟨heLocal, heRes⟩, _⟩ :=
    _root_.StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
      hindE φres hφres
  have hresMap : (IsLocalRing.residue Rsh).comp eF.toRingHom =
      εL.toRingHom.comp g.toRingHom := by
    calc
      (IsLocalRing.residue Rsh).comp eF.toRingHom = φres.comp (IsLocalRing.residue E) := heRes
      _ = εL.toRingHom.comp g.toRingHom := by
        apply RingHom.ext
        intro y
        change εL (g (eEκ.symm (eEκ y))) = εL (g y)
        rw [eEκ.symm_apply_apply]
  let : Algebra E (IsLocalRing.ResidueField Rsh) :=
    ((IsLocalRing.residue Rsh).comp eF.toRingHom).toAlgebra
  have hpure : IsPurelyInseparable E (IsLocalRing.ResidueField Rsh) :=
    (RingHom.isPurelyInseparable_algebraMap_iff).mp (by
      change ((IsLocalRing.residue Rsh).comp eF.toRingHom).IsPurelyInseparable
      rw [hresMap]
      apply RingHom.IsPurelyInseparable.comp
      · let : Algebra E L := g.toRingHom.toAlgebra
        exact (RingHom.isPurelyInseparable_algebraMap_iff).2 hg
      · exact RingHom.isPurelyInseparable_of_surjective εL.toRingHom εL.surjective)
  let : IsScalarTower K F E := .of_algebraMap_eq' rfl
  have hKFA : algebraMap K A = (algebraMap F A).comp (algebraMap K F) := by
    ext k
    change algebraMap K A k = φ (algebraMap K F k)
    exact (φ.commutes k).symm
  let : IsScalarTower K F A := .of_algebraMap_eq' hKFA
  have hKFR : algebraMap K Rsh = (algebraMap F Rsh).comp (algebraMap K F) := by
    ext k
    calc
      algebraMap K Rsh k = algebraMap A Rsh (algebraMap K A k) :=
        (IsScalarTower.algebraMap_apply K A Rsh k).symm
      _ = algebraMap A Rsh (algebraMap F A (algebraMap K F k)) := by
        rw [hKFA]
        simp only [RingHom.comp_apply]
      _ = algebraMap F Rsh (algebraMap K F k) := by
        simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  let : IsScalarTower K F Rsh := .of_algebraMap_eq' hKFR
  let e : E →ₐ[K] Rsh := eF.restrictScalars K
  refine ⟨ι, E, Rsh, L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hCR, hLR, inferInstance, hAR, inferInstance, inferInstance, inferInstance,
    inferInstance, hcard, hsh, e, hpure, ?_⟩
  let : Algebra E Rsh := e.toAlgebra
  let : IsScalarTower K E Rsh := .of_algebraMap_eq fun k => (e.commutes k).symm
  apply isFilteredColimit_of_trdeg_le K E Rsh
  · have hPF := trdeg_le_of_injective
      (IsScalarTower.toAlgHom K (MvPolynomial ι K) F)
      (IsFractionRing.injective (MvPolynomial ι K) F)
    have hFE := trdeg_le_of_injective (IsScalarTower.toAlgHom K F E)
      (algebraMap F E).injective
    simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at hPF
    exact coe_toENat_le_coe_toENat (hPF.trans hFE)
  · let := hsh
    exact toENat_trdeg_henselization_le_topologicalKrullDimAt K f x Rsh
      (IsLocalRing.IsHenselization.ind_etale_of_universe_le (R := A) (L := L) (Rh := Rsh))

end AlgebraicGeometry

end
