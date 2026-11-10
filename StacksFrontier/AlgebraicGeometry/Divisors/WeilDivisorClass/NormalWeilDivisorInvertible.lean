module

public import StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassSurjective
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.PrincipalIdealOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint

/-!
# `𝒪_X(D)` on a normal scheme: invertible away from codimension two

Let `X` be an integral locally Noetherian normal scheme and `D` a Weil divisor on `X`.  The
ideal sheaf `AlgebraicGeometry.positiveWeilIdeal D` of the positive part of `D` — the locally
finite product `∏_Z 𝓘_Z^{D_Z}` over the prime divisors in the support of `D` — is an effective
Cartier divisor as soon as its local rings are factorial, by
`AlgebraicGeometry.positiveWeilIdeal_isEffectiveCartierDivisor`.  Over a merely normal scheme
that fails: the one step of that argument which uses factoriality is
`AlgebraicGeometry.PrimeDivisor.isEffectiveCartierDivisor_idealSheaf`, which says a prime divisor
is itself an effective Cartier divisor, i.e. that the height one primes of the local rings are
principal.  That is exactly the condition distinguishing factorial from normal in
[Stacks, Tag 0BE9].

What survives over a normal scheme is that the ideal sheaf is principal in *codimension one*.
At the generic point of `X` the ideal sheaf is the unit ideal, and at the generic point of a
prime divisor `Z` it is the `D_Z`-th power of the maximal ideal of `𝒪_{X,ξ_Z}`, by
`AlgebraicGeometry.positiveWeilIdeal_stalk_genericPoint`; normality makes that local ring a
discrete valuation ring, hence a principal ideal ring.  So every point outside
`AlgebraicGeometry.weilDivisorInvertibleOpen D`, the locus where the ideal sheaf is principal, has
coheight at least two, and on that locus the inverse image of the ideal sheaf is an effective
Cartier divisor whose `𝒪_X(D)` has the expected orders of vanishing.

Since `Cl(U) = Cl(X)` for such an open subscheme, every Weil divisor class on `X` is the class of
an invertible module on an open subscheme whose complement has codimension at least two: the
positive part of `D` and the positive part of `-D` give two effective Cartier divisors on a
common such open subscheme, and the difference of their Picard classes is represented by an
invertible module there.

## Main definitions

* `AlgebraicGeometry.weilDivisorInvertibleOpen` — the open subscheme on which `𝒪_X(D)` is
  invertible.

## Main results

* `AlgebraicGeometry.positiveWeilIdeal_stalk_genericPoint_eq_top` — `𝒪_X(D)` is the unit ideal at
  the generic point.
* `AlgebraicGeometry.two_le_codimension_compl_weilDivisorInvertibleOpen` — the complement of the
  invertibility locus has codimension at least two.
* `AlgebraicGeometry.isEffectiveCartierDivisor_comap_positiveWeilIdeal` — the ideal sheaf becomes
  an effective Cartier divisor there.
* `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_comap_positiveWeilIdeal` — its Weil
  divisor class is the restriction of the positive part of `D`.
* `AlgebraicGeometry.exists_weilClassOfCodimTwoInvertible_eq` — **every Weil divisor class is the
  class of an invertible module on an open subscheme whose complement has codimension at least
  two.**

## References

* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
* [Stacks Project, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8)
-/

@[expose] public noncomputable section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### The generic point lies outside every prime divisor -/

/-- **The generic point of an integral scheme lies outside every prime divisor.**  Otherwise the
generic point of the prime divisor would specialize to it, forcing that generic point to be the
top element of the specialization order and hence to have coheight zero, while the generic point
of a prime divisor has coheight one. -/
theorem PrimeDivisor.genericPoint_notMem_support [IsIntegral X] (Z : PrimeDivisor X) :
    _root_.genericPoint X ∉ Z.support := by
  intro hmem
  have hspec : Z.genericPoint ⤳ _root_.genericPoint X :=
    specializes_iff_mem_closure.mpr (Z.support_eq_closure ▸ hmem)
  have hcoh := Z.coheight_genericPoint
  rw [(hspec.antisymm (genericPoint_specializes Z.genericPoint)).eq,
    coheight_eq_zero.2 (isMax_genericPoint X)] at hcoh
  exact zero_ne_one hcoh

variable [IsLocallyNoetherian X]

omit [IsLocallyNoetherian X] in
/-- **The ideal sheaf of the positive part of a Weil divisor is the unit ideal at the generic
point** of an integral scheme: every prime divisor misses that point, so every factor of the
product is the unit ideal there. -/
theorem positiveWeilIdeal_stalk_genericPoint_eq_top [IsIntegral X] (D : WeilDivisor X) :
    IdealSheafData.stalk (positiveWeilIdeal D) (genericPoint X) = ⊤ := by
  classical
  obtain ⟨W, hW, hηW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint X) trivial
  rw [IdealSheafData.stalk_eq_map_germ _ (genericPoint X) ⟨W, hW⟩ hηW, positiveWeilIdeal_ideal,
    show Ideal.map (X.presheaf.germ (⟨W, hW⟩ : X.affineOpens).1 (genericPoint X) hηW).hom
        (∏ Z ∈ (finite_primeDivisors_meeting_affine D ⟨W, hW⟩).toFinset,
          Z.idealSheaf.ideal ⟨W, hW⟩ ^ (D.val Z).toNat) =
        ∏ Z ∈ (finite_primeDivisors_meeting_affine D ⟨W, hW⟩).toFinset,
          (Z.idealSheaf.ideal ⟨W, hW⟩ ^ (D.val Z).toNat).map
            (X.presheaf.germ (⟨W, hW⟩ : X.affineOpens).1 (genericPoint X) hηW).hom from
      map_prod (Ideal.mapHom _) _ _]
  refine (Finset.prod_eq_one fun Z _ => ?_).trans Ideal.one_eq_top
  rw [Ideal.map_pow,
    ← IdealSheafData.stalk_eq_map_germ Z.idealSheaf (genericPoint X) ⟨W, hW⟩ hηW,
    IdealSheafData.stalk_eq_top_of_notMem_support Z.idealSheaf Z.genericPoint_notMem_support,
    Ideal.top_pow]
  exact Ideal.one_eq_top.symm

/-! ### The invertibility locus of `𝒪_X(D)` -/

variable [IsIntegral X] [IsNormal X]

/-- **The open subscheme on which `𝒪_X(D)` is invertible**: the locus where the ideal sheaf of
the positive part of `D` is principal. -/
def weilDivisorInvertibleOpen (D : WeilDivisor X) : X.Opens :=
  IdealSheafData.principalOpen (positiveWeilIdeal D)

/-- **The ideal sheaf of the positive part of a Weil divisor is principal at the generic point of
a prime divisor** of a normal scheme: it is a power of the maximal ideal, and that local ring is a
discrete valuation ring, hence a principal ideal ring. -/
theorem positiveWeilIdeal_stalk_genericPoint_isPrincipal (D : WeilDivisor X)
    (Z : PrimeDivisor X) :
    (IdealSheafData.stalk (positiveWeilIdeal D) Z.genericPoint).IsPrincipal := by
  let : IsDiscreteValuationRing (X.presheaf.stalk Z.genericPoint) :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
      Z.coheight_genericPoint
  let : IsPrincipalIdealRing (X.presheaf.stalk Z.genericPoint) :=
    IsDiscreteValuationRing.toIsPrincipalIdealRing
  rw [positiveWeilIdeal_stalk_genericPoint D Z]
  exact IsPrincipalIdealRing.principal _

/-- **The complement of the invertibility locus of `𝒪_X(D)` has codimension at least two.**  The
generic point of `X` is in the locus because the ideal sheaf is the unit ideal there, and the
generic point of a prime divisor is in it because the ideal sheaf is a power of the maximal ideal
of a discrete valuation ring there; so every point outside has coheight at least two. -/
theorem two_le_codimension_compl_weilDivisorInvertibleOpen (D : WeilDivisor X) (x : X)
    (hx : x ∉ weilDivisorInvertibleOpen D) :
    (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  rw [← coheight_eq_codimension_closureSingleton]
  by_contra hlt
  refine hx (IdealSheafData.mem_principalOpen_of_stalk_isPrincipal _ ?_)
  rcases Order.le_one_iff.mp (ENat.lt_two_iff.mp (lt_of_not_ge hlt)) with
    hzero | hone
  · have hle : x ≤ genericPoint X :=
      Scheme.le_iff_specializes.mpr (genericPoint_specializes x)
    have htop : genericPoint X = x :=
      ((Scheme.le_iff_specializes.mp hle).antisymm
        (Scheme.le_iff_specializes.mp (coheight_eq_zero.mp hzero hle))).eq
    refine htop ▸ ?_
    rw [positiveWeilIdeal_stalk_genericPoint_eq_top D]
    exact ⟨1, by simp⟩
  · exact PrimeDivisor.genericPoint_ofCoheightOne x hone ▸
      positiveWeilIdeal_stalk_genericPoint_isPrincipal D (PrimeDivisor.ofCoheightOne x hone)

/-! ### `𝒪_X(D)` is an effective Cartier divisor on the invertibility locus -/

omit [IsNormal X] in
/-- **The ideal sheaf of the positive part of `D` becomes an effective Cartier divisor on any open
subscheme of the invertibility locus**: there it is principal in every local ring, with a nonzero
generator. -/
theorem isEffectiveCartierDivisor_comap_positiveWeilIdeal (D : WeilDivisor X) (U : X.Opens)
    [IsIntegral U.toScheme] (hU : U ≤ weilDivisorInvertibleOpen D) :
    Stacks.Divisors.IsEffectiveCartierDivisor ((positiveWeilIdeal D).comap U.ι) :=
  IdealSheafData.isEffectiveCartierDivisor_comap_of_le_principalOpen _
    (positiveWeilIdeal_stalk_genericPoint_eq_top D) U hU

section CodimensionTwoComplement

variable (U : X.Opens)
  (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))

include hU

omit [IsLocallyNoetherian X] [IsIntegral X] [IsNormal X] in
/-- **The order of `𝒪_X(D)` along a prime divisor of the open subscheme.**  The ideal sheaf
induces, in the local ring at the generic point of a prime divisor `W` of `U`, the `D_Z`-th power
of the maximal ideal, where `Z` is the prime divisor of `X` that `W` comes from. -/
theorem stalk_comap_positiveWeilIdeal_genericPoint (D : WeilDivisor X)
    (W : PrimeDivisor U.toScheme) :
    IdealSheafData.stalk ((positiveWeilIdeal D).comap U.ι) W.genericPoint =
      IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk W.genericPoint) ^
        (D.val ((primeDivisorRestrictEquiv U hU).symm W)).toNat := by
  refine IdealSheafData.stalk_comap_opensι_eq_maximalIdeal_pow _ U W.genericPoint _ ?_
  rw [← genericPoint_primeDivisorRestrictEquiv_symm U hU W]
  exact positiveWeilIdeal_stalk_genericPoint D _

/-- **The Weil divisor class of `𝒪_X(D)` on the invertibility locus** is the class of the
restriction of the positive part of `D`: at the generic point of every prime divisor the ideal
sheaf is a power of the maximal ideal of a discrete valuation ring, and a generator of the `n`-th
power of that maximal ideal has order of vanishing `n`. -/
theorem weilDivisorClassOfInvertibleSheaf_comap_positiveWeilIdeal (D : WeilDivisor X)
    (hUle : U ≤ weilDivisorInvertibleOpen D) :
    letI : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
    letI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
    letI : Stacks.Divisors.IsEffectiveCartierDivisor ((positiveWeilIdeal D).comap U.ι) :=
      isEffectiveCartierDivisor_comap_positiveWeilIdeal D U hUle
    weilDivisorClassOfInvertibleSheaf U.toScheme
        (Stacks.Divisors.modulesInvertibleSheaf ((positiveWeilIdeal D).comap U.ι)) =
      (weilDivisorRestrictEquiv U hU (positiveWeilDivisor D) :
        weilDivisorClassGroup U.toScheme) := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsNormal U.toScheme := isNormal_of_isOpenImmersion U.ι
  have : Stacks.Divisors.IsEffectiveCartierDivisor ((positiveWeilIdeal D).comap U.ι) :=
    isEffectiveCartierDivisor_comap_positiveWeilIdeal D U hUle
  refine weilDivisorClassOfInvertibleSheaf_eq_of_forall_ord _ _ fun W c hc => ?_
  have : IsDiscreteValuationRing (U.toScheme.presheaf.stalk W.genericPoint) :=
    Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
      W.coheight_genericPoint
  rw [weilDivisorRestrictEquiv_apply_val, positiveWeilDivisor_apply]
  exact (ord_algebraMap_eq_of_span_eq_maximalIdeal_pow W.genericPoint W.coheight_genericPoint c _
    (hc.symm.trans (stalk_comap_positiveWeilIdeal_genericPoint U hU D W))).symm

end CodimensionTwoComplement

/-! ### Every Weil divisor class comes from an invertible module in codimension two -/

attribute [local instance] schemePicardGroupAddCommGroup

/-- **Every Weil divisor class is the class of an invertible module on an open subscheme whose
complement has codimension at least two.**  This is what
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_surjective_iff` asks for.

Write the class as that of a Weil divisor `D = D⁺ - (-D)⁺`.  On the intersection `U` of the
invertibility loci of `𝒪_X(D⁺)` and `𝒪_X((-D)⁺)` — whose complement has codimension at least
two — both ideal sheaves become effective Cartier divisors, so both `𝒪_U` of them are
invertible, with Weil divisor classes the restrictions of `D⁺` and of `(-D)⁺`.  The difference of
their Picard classes is represented by an invertible module on `U`, and the first Chern class of
`U` is a homomorphism, so that module has Weil divisor class the restriction of `D`. -/
theorem exists_weilClassOfCodimTwoInvertible_eq (c : weilDivisorClassGroup X) :
    ∃ (V : X.Opens)
      (hV : ∀ x : X, x ∉ V → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
      (L : V.toScheme.Modules) (hL : SheafOfModules.IsInvertible V.toScheme.sheaf.obj
        V.toScheme.ringCatSheaf.property L), weilClassOfCodimTwoInvertible V hV L hL = c := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
  set U : X.Opens := weilDivisorInvertibleOpen D ⊓ weilDivisorInvertibleOpen (-D) with hUdef
  have hU : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x) :=
    two_le_codimension_compl_inf _ _ (two_le_codimension_compl_weilDivisorInvertibleOpen D)
      (two_le_codimension_compl_weilDivisorInvertibleOpen (-D))
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsDominant U.ι := isDominant_opensι (U := U)
  have h1 : Stacks.Divisors.IsEffectiveCartierDivisor ((positiveWeilIdeal D).comap U.ι) :=
    isEffectiveCartierDivisor_comap_positiveWeilIdeal D U inf_le_left
  have h2 : Stacks.Divisors.IsEffectiveCartierDivisor ((positiveWeilIdeal (-D)).comap U.ι) :=
    isEffectiveCartierDivisor_comap_positiveWeilIdeal (-D) U inf_le_right
  set L1 : U.toScheme.Modules :=
    Stacks.Divisors.modulesInvertibleSheaf ((positiveWeilIdeal D).comap U.ι) with hL1def
  set L2 : U.toScheme.Modules :=
    Stacks.Divisors.modulesInvertibleSheaf ((positiveWeilIdeal (-D)).comap U.ι) with hL2def
  have hi1 : Stacks.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property L1 :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf _
  have hi2 : Stacks.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property L2 :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf _
  set p : Stacks.SheafOfModules.PicardGroup U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property :=
    Stacks.SheafOfModules.picardClass U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property L1 hi1 -
      Stacks.SheafOfModules.picardClass U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
        L2 hi2 with hpdef
  have hiP : SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (picardRepresentative U.toScheme p).obj :=
    (picardRepresentative U.toScheme p).property.toAlgebraicGeometry
  refine ⟨U, hU, (picardRepresentative U.toScheme p).obj, hiP, ?_⟩
  have hclass : weilDivisorClassOfInvertibleSheaf U.toScheme
      (picardRepresentative U.toScheme p).obj =
      weilDivisorClassRestrictEquiv U hU ((D : WeilDivisor X) : weilDivisorClassGroup X) := by
    have hp : picardToWeilDivisorClassGroup U.toScheme p =
        weilDivisorClassOfInvertibleSheaf U.toScheme L1 -
          weilDivisorClassOfInvertibleSheaf U.toScheme L2 := by
      rw [hpdef, map_sub]
      have := hi1
      have := hi2
      exact congrArg₂ (· - ·) (weilDivisorClassOfPicardClass_picardClass U.toScheme L1)
        (weilDivisorClassOfPicardClass_picardClass U.toScheme L2)
    rw [show weilDivisorClassOfInvertibleSheaf U.toScheme
          (picardRepresentative U.toScheme p).obj =
        picardToWeilDivisorClassGroup U.toScheme p from rfl, hp,
      weilDivisorClassOfInvertibleSheaf_comap_positiveWeilIdeal U hU D inf_le_left,
      weilDivisorClassOfInvertibleSheaf_comap_positiveWeilIdeal U hU (-D) inf_le_right,
      weilDivisorClassRestrictEquiv_mk]
    rw [← QuotientAddGroup.mk_sub, ← map_sub, positiveWeilDivisor_sub_neg]
  change (weilDivisorClassRestrictEquiv U hU).symm _ = _
  rw [hclass, AddEquiv.symm_apply_apply]

end AlgebraicGeometry

end
