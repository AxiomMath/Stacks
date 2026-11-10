module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentReducedFibre
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne.FreeOverLocalBase
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStageLocalCase
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.FreenessCriterion
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FreeSpreadOut
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.NagataValuativeCriterion.Basic

/-!
# The essential-image half of Stacks Tag 0EXH over a normal base

Let `p` be a prime and `f : X ⟶ Y` a flat, proper, surjective morphism of schemes in
characteristic `p`, with `Y` normal and Noetherian and `f_*𝒪_X = 𝒪_Y`. Let `ℰ` be a finite locally
free `𝒪_X`-module satisfying the fibre condition of Stacks Tag 0EXH (some Frobenius power
pullback of `ℰ` is free on every reduced fibre `X_{y,red}`). Then some `F^{n,*}ℰ` is the pullback
of a finite locally free `𝒪_Y`-module.

This is the last paragraph of the proof of Stacks Tag 0EXH. After a Frobenius power pullback `ℰ`
is free over the local schemes `X ×_Y Spec 𝒪_{Y,η}` at the generic points `η` (the fibre condition
on the Noetherian fibre, `Scheme.Vect.IsFreeOnReducedFibresAfterFrobenius.exists_free`), hence
over the local schemes at all points of a dense open (freeness spreads out,
`Stacks.AlgebraicGeometry.ModuleLimits.exists_mem_pullback_iso_free_of_fromSpecStalk`). Outside
it lie only finitely many points of codimension one, at each of which `𝒪_{Y,z}` is a discrete
valuation ring; there Stacks Tag 0EXF, applied after a further Frobenius power pullback which makes
`ℰ` free on the generic fibre and on the thickening `X_{n_z}` of the special fibre, gives freeness
over `X ×_Y Spec 𝒪_{Y,z}`. Freeness in codimension at most one makes the counit `f^*f_*ℰ ⟶ ℰ` an
isomorphism, by the argument of Stacks Tag 0EXG.

## Main results

* `AlgebraicGeometry.Scheme.Vect.descendsAfterFrobenius_of_isNormal`.

## References

* [Stacks Project, Tag 0EXH](https://stacks.math.columbia.edu/tag/0EXH)
* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
* [Stacks Project, Tag 0EXG](https://stacks.math.columbia.edu/tag/0EXG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Points of a Noetherian scheme -/

/-- **A closed subset of a Noetherian scheme has only finitely many points with no proper
generization inside it**: they are the generic points of its irreducible components. -/
theorem Scheme.finite_setOf_forall_specializes_eq {Y : Scheme.{u}} [IsNoetherian Y] (T : Set Y)
    (hT : IsClosed T) : {z | z ∈ T ∧ ∀ t ∈ T, t ⤳ z → t = z}.Finite := by
  obtain ⟨𝒮, h𝒮fin, h𝒮closed, h𝒮irred, h𝒮union⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  have : Finite 𝒮 := h𝒮fin.to_subtype
  refine (Set.finite_range fun t : 𝒮 ↦ (h𝒮irred t.1 t.2).genericPoint).subset ?_
  rintro z ⟨hzT, hz⟩
  obtain ⟨t, ht𝒮, hzt⟩ : z ∈ ⋃₀ 𝒮 := h𝒮union ▸ hzT
  have hgen : closure ({(h𝒮irred t ht𝒮).genericPoint} : Set Y) = t :=
    ((h𝒮irred t ht𝒮).genericPoint_closure_eq).trans (h𝒮closed t ht𝒮).closure_eq
  have hspec : (h𝒮irred t ht𝒮).genericPoint ⤳ z :=
    specializes_iff_mem_closure.mpr (by rwa [hgen])
  have hmemT : (h𝒮irred t ht𝒮).genericPoint ∈ T := by
    rw [h𝒮union]
    exact ⟨t, ht𝒮, hgen.subset (subset_closure (Set.mem_singleton _))⟩
  exact ⟨⟨t, ht𝒮⟩, hz _ hmemT hspec⟩

/-- In a scheme, a strict generization of a point whose local ring has dimension one has a local
ring of dimension zero. -/
theorem Scheme.ringKrullDim_stalk_eq_zero_of_specializes {Y : Scheme.{u}} {t z : Y}
    (hz : ringKrullDim (Y.presheaf.stalk z) = 1) (htz : t ⤳ z) (hne : t ≠ z) :
    ringKrullDim (Y.presheaf.stalk t) = 0 := by
  rw [ringKrullDim_stalk_eq_coheight] at hz ⊢
  have hlt : z < t := lt_of_le_not_ge htz (fun h ↦ hne (htz.antisymm h).eq)
  have h1 : Order.coheight z = 1 := by exact_mod_cast hz
  have h2 := Order.coheight_add_one_le hlt
  rw [h1] at h2
  have h3 : Order.coheight t = 0 := by
    by_contra h0
    have h1' : (1 : ℕ∞) ≤ Order.coheight t := Order.one_le_iff_ne_zero.mpr h0
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left h1' 1).trans h2
    norm_num at this
  rw [h3]
  rfl

/-- **The points of codimension zero of a Noetherian scheme are finite in number.** -/
theorem Scheme.finite_setOf_ringKrullDim_stalk_eq_zero (Y : Scheme.{u}) [IsNoetherian Y] :
    {z : Y | ringKrullDim (Y.presheaf.stalk z) = 0}.Finite := by
  refine (Scheme.finite_setOf_forall_specializes_eq Set.univ isClosed_univ).subset
    fun z hz ↦ ⟨trivial, fun t _ htz ↦ ?_⟩
  have hz' : Order.coheight z = 0 := by
    rw [Set.mem_ofPred_eq, ringKrullDim_stalk_eq_coheight] at hz
    exact_mod_cast hz
  exact (htz.antisymm (Order.coheight_eq_zero.mp hz' htz)).eq

/-- **Outside an open set containing all the points of codimension zero, a Noetherian scheme has
only finitely many points of codimension one.** -/
theorem Scheme.finite_setOf_ringKrullDim_stalk_eq_one_of_notMem {Y : Scheme.{u}} [IsNoetherian Y]
    (O : Set Y) (hO : IsOpen O) (h0 : ∀ y, ringKrullDim (Y.presheaf.stalk y) = 0 → y ∈ O) :
    {z : Y | z ∉ O ∧ ringKrullDim (Y.presheaf.stalk z) = 1}.Finite := by
  refine (Scheme.finite_setOf_forall_specializes_eq Oᶜ hO.isClosed_compl).subset ?_
  rintro z ⟨hzO, hz⟩
  refine ⟨hzO, fun t htO htz ↦ ?_⟩
  by_contra hne
  exact htO (h0 t (Scheme.ringKrullDim_stalk_eq_zero_of_specializes hz htz hne))

/-- The spectrum of a local ring of dimension zero has a single point. -/
theorem subsingleton_spec_of_ringKrullDim_eq_zero (R : CommRingCat.{u}) [IsLocalRing R]
    (h : ringKrullDim R = 0) : Subsingleton (Spec R) := by
  have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr h.le
  exact Ring.KrullDimLE.subsingleton_primeSpectrum R

/-- The quotient of a local ring by a power of its maximal ideal has a single prime ideal. -/
theorem subsingleton_primeSpectrum_quotient_maximalIdeal_pow (A : Type u) [CommRing A]
    [IsLocalRing A] (n : ℕ) :
    Subsingleton (PrimeSpectrum (A ⧸ IsLocalRing.maximalIdeal A ^ n)) := by
  have key : ∀ P : PrimeSpectrum (A ⧸ IsLocalRing.maximalIdeal A ^ n),
      P.asIdeal.comap (Ideal.Quotient.mk _) = IsLocalRing.maximalIdeal A := by
    intro P
    have hP : (P.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n))).IsPrime :=
      Ideal.comap_isPrime _ _
    have hle : IsLocalRing.maximalIdeal A ^ n ≤
        P.asIdeal.comap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)) := by
      intro a ha
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le hP.ne_top (hP.le_of_pow_le hle)).symm
  exact ⟨fun P Q ↦ PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _
    Ideal.Quotient.mk_surjective ((key P).trans (key Q).symm))⟩

/-! ### Freeness over the local schemes -/

/-- A sheaf of modules `ℰ` on `X` is **free of finite rank over the local scheme at `s`** (for a
morphism `f : X ⟶ Y` and `s ∈ Y`) if its pullback to `X ×_Y Spec 𝒪_{Y,s}` is isomorphic to
`𝒪^{⊕r}` for some `r`. -/
def IsFreeOverLocalScheme {X Y : Scheme.{u}} (f : X ⟶ Y) (E : X.Modules) (s : Y) : Prop :=
  ∃ r : ℕ, Nonempty ((Scheme.Modules.pullback (pullback.fst f (Y.fromSpecStalk s))).obj E ≅
    SheafOfModules.free (ULift.{u} (Fin r)))

variable {p : ℕ} [Fact p.Prime]

/-- **Freeness after a pullback survives further Frobenius power pullbacks.** -/
theorem nonempty_iso_free_frobeniusPullbackIter_add {T X : Scheme.{u}} (a : T ⟶ X)
    (hT : IsInCharacteristic T p) (hX : IsInCharacteristic X p) (E : X.Vect) (N m r : ℕ)
    (e : (Scheme.Modules.pullback a).obj ((frobeniusPullbackIter X p hX N).obj E).obj ≅
      SheafOfModules.free (ULift.{u} (Fin r))) :
    Nonempty ((Scheme.Modules.pullback a).obj ((frobeniusPullbackIter X p hX (N + m)).obj E).obj ≅
      SheafOfModules.free (ULift.{u} (Fin r))) := by
  let e' : (Scheme.Vect.pullback a).obj ((frobeniusPullbackIter X p hX N).obj E) ≅
      Scheme.Vect.freeRank T r := ObjectProperty.isoMk _ e
  exact ⟨(ObjectProperty.ι _).mapIso
    ((Scheme.Vect.pullback a).mapIso (Scheme.Vect.frobeniusPullbackIterAddIso X hX m N E).symm ≪≫
      frobeniusPullbackIterPullbackIso a p hT hX m _ ≪≫
        (frobeniusPullbackIter T p hT m).mapIso e' ≪≫ frobeniusPullbackIterObjFreeIso p T hT m r)⟩

/-- Freeness of a Frobenius power pullback of `a^*ℰ` gives freeness of `a^*` of a further
Frobenius power pullback of `ℰ`. -/
private theorem nonempty_iso_free_pullback_frobeniusPullbackIter_add {T X : Scheme.{u}} (a : T ⟶ X)
    (hT : IsInCharacteristic T p) (hX : IsInCharacteristic X p) (E : X.Vect) (N m r : ℕ)
    (e : ((frobeniusPullbackIter T p hT N).obj ((Scheme.Vect.pullback a).obj E)).obj ≅
      SheafOfModules.free (ULift.{u} (Fin r))) :
    Nonempty ((Scheme.Modules.pullback a).obj ((frobeniusPullbackIter X p hX (N + m)).obj E).obj ≅
      SheafOfModules.free (ULift.{u} (Fin r))) :=
  nonempty_iso_free_frobeniusPullbackIter_add a hT hX E N m r
    ((ObjectProperty.ι _).mapIso (frobeniusPullbackIterPullbackIso a p hT hX N E) ≪≫ e)

/-- **Freeness over a local scheme survives further Frobenius power pullbacks.** -/
theorem IsFreeOverLocalScheme.frobeniusPullbackIter_mono {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hX : IsInCharacteristic X p) {E : X.Vect} {N N' : ℕ} (hNN' : N ≤ N') {s : Y}
    (h : IsFreeOverLocalScheme f ((frobeniusPullbackIter X p hX N).obj E).obj s) :
    IsFreeOverLocalScheme f ((frobeniusPullbackIter X p hX N').obj E).obj s := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hNN'
  obtain ⟨r, ⟨e⟩⟩ := h
  exact ⟨r, nonempty_iso_free_frobeniusPullbackIter_add _
    (isInCharacteristic_of_hom (pullback.fst f (Y.fromSpecStalk s)) p hX) hX E N m r e⟩

/-- **Freeness over the local schemes is an open condition**, for a quasi-compact quasi-separated
morphism and a finite locally free module. -/
theorem isOpen_setOf_isFreeOverLocalScheme {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (E : X.Vect) : IsOpen {s : Y | IsFreeOverLocalScheme f E.obj s} := by
  have : E.obj.IsFinitePresentation :=
    @Stacks.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree _ _ _ _ _ _ E.obj E.property
  refine isOpen_iff_forall_mem_open.mpr fun s ⟨r, ⟨e⟩⟩ ↦ ?_
  obtain ⟨W, hsW, ⟨eW⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_mem_pullback_iso_free_of_fromSpecStalk f E.obj
      s r e
  refine ⟨W, fun s' hs' ↦ ⟨r, ⟨?_⟩⟩, W.isOpen, hsW⟩
  let σ : pullback f (Y.fromSpecStalk s') ⟶ pullback f W.ι :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ W.fromSpecStalkOfMem s' hs')
      (by rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, pullback.condition])
  have hσ : σ ≫ pullback.fst f W.ι = pullback.fst f (Y.fromSpecStalk s') :=
    pullback.lift_fst _ _ _
  exact (Scheme.Modules.pullbackCongr hσ.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp σ _).app _).symm ≪≫
      (Scheme.Modules.pullback σ).mapIso eW ≪≫ Scheme.Modules.pullbackFreeIso σ _

end AlgebraicGeometry

namespace AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime]

open Scheme.Vect in
/-- **At a point of codimension zero, the fibre condition of Stacks Tag 0EXH gives freeness over
the local scheme after a Frobenius power pullback.** The local scheme is a single point, and its
base change is Noetherian. -/
theorem exists_isFreeOverLocalScheme_of_ringKrullDim_eq_zero {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian Y]
    (hX : IsInCharacteristic X p) {E : X.Vect} (hE : IsFreeOnReducedFibresAfterFrobenius f p hX E)
    (y : Y) (hy : ringKrullDim (Y.presheaf.stalk y) = 0) :
    ∃ N, IsFreeOverLocalScheme f ((frobeniusPullbackIter X p hX N).obj E).obj y := by
  let g := Y.fromSpecStalk y
  let a := pullback.fst f g
  have hT : IsInCharacteristic (pullback f g) p := isInCharacteristic_of_hom a p hX
  have hET := hE.pullback (f' := pullback.snd f g) pullback.condition hX hT
  have : Subsingleton (Spec (Y.presheaf.stalk y)) :=
    subsingleton_spec_of_ringKrullDim_eq_zero _ hy
  have : IsNoetherian (pullback f g) := isNoetherian_of_locallyOfFiniteType (pullback.snd f g)
  obtain ⟨N, r, ⟨e⟩⟩ := hET.exists_free (IsLocalRing.closedPoint _)
  exact ⟨N, r, nonempty_iso_free_pullback_frobeniusPullbackIter_add a hT hX E N 0 r e⟩

open Scheme.Vect Stacks.AlgebraicGeometry.FreenessOverDVR
  Stacks.AlgebraicGeometry.NagataValuativeCriterion in
/-- **At a point of codimension one of a normal base, the fibre condition of Stacks Tag 0EXH gives
freeness over the local scheme after a Frobenius power pullback.** The local ring is a discrete
valuation ring `A`; after a Frobenius power pullback `ℰ` is free on the generic fibre and on the
thickening `X_n` of the special fibre of `X ×_Y Spec A ⟶ Spec A`, both one-point-based and
Noetherian, where `n` is the integer of Stacks Tag 0EXF; and then Tag 0EXF gives freeness. -/
theorem exists_isFreeOverLocalScheme_of_ringKrullDim_eq_one {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsInCharacteristic X p) {E : X.Vect} (hE : IsFreeOnReducedFibresAfterFrobenius f p hX E)
    (z : Y) (hz : ringKrullDim (Y.presheaf.stalk z) = 1) :
    ∃ N, IsFreeOverLocalScheme f ((frobeniusPullbackIter X p hX N).obj E).obj z := by
  have : IsDiscreteValuationRing (Y.presheaf.stalk z) :=
    isDiscreteValuationRing_stalk_of_ringKrullDim_eq_one Y hz
  let A : Type u := Y.presheaf.stalk z
  let g := Y.fromSpecStalk z
  let a := pullback.fst f g
  let fz : pullback f g ⟶ Spec (.of A) := pullback.snd f g
  have hXz : IsInCharacteristic (pullback f g) p := isInCharacteristic_of_hom a p hX
  let Ez := (Scheme.Vect.pullback a).obj E
  have hEz : IsFreeOnReducedFibresAfterFrobenius fz p hXz Ez :=
    hE.pullback (f' := fz) pullback.condition hX hXz
  have : IsProper fz := inferInstanceAs (IsProper (pullback.snd f g))
  obtain ⟨n, hn, h0EXF⟩ := exists_thickening_exponent_free A fz
  -- the generic fibre
  let gen := genericPoint (Spec (.of A))
  let Gι := fz.fiberι gen
  have hG : IsInCharacteristic (fz.fiber gen) p := isInCharacteristic_of_hom Gι p hXz
  have hEG := hEz.pullback (Scheme.Hom.fiber_fac fz gen) hXz hG
  have : IsNoetherian (fz.fiber gen) :=
    isNoetherian_of_locallyOfFiniteType (fz.fiberToSpecResidueField gen)
  have : Subsingleton (Spec ((Spec (.of A)).residueField gen)) :=
    Ring.KrullDimLE.subsingleton_primeSpectrum _
  obtain ⟨N₁, r₁, ⟨e₁⟩⟩ := hEG.exists_free (IsLocalRing.closedPoint _)
  -- the thickening
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ n)))
  let Tι := pullback.fst fz q
  have hTh : IsInCharacteristic (pullback fz q) p := isInCharacteristic_of_hom Tι p hXz
  have hET := hEz.pullback (f' := pullback.snd fz q) pullback.condition hXz hTh
  have : IsNoetherian (pullback fz q) := isNoetherian_of_locallyOfFiniteType (pullback.snd fz q)
  have : Subsingleton (Spec (.of (A ⧸ IsLocalRing.maximalIdeal A ^ n))) :=
    subsingleton_primeSpectrum_quotient_maximalIdeal_pow A n
  have : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ n) := Ideal.Quotient.nontrivial_iff.mpr <|
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.pow_le_self (Nat.pos_iff_ne_zero.mp hn))
  obtain ⟨N₂, r₂, ⟨e₂⟩⟩ := hET.exists_free (Classical.arbitrary _)
  -- both after the Frobenius power `N₁ + N₂`
  have hgen : IsFreeOfFiniteRank (genericFibreRestrict A fz
      ((frobeniusPullbackIter _ p hXz (N₁ + N₂)).obj Ez).obj) :=
    ⟨r₁, nonempty_iso_free_pullback_frobeniusPullbackIter_add Gι hG hXz Ez N₁ N₂ r₁ e₁⟩
  have hthick : IsFreeOfFiniteRank (thickeningRestrict A fz n
      ((frobeniusPullbackIter _ p hXz (N₁ + N₂)).obj Ez).obj) := by
    rw [add_comm]
    exact ⟨r₂, nonempty_iso_free_pullback_frobeniusPullbackIter_add Tι hTh hXz Ez N₂ N₁ r₂ e₂⟩
  obtain ⟨r, ⟨e⟩⟩ := h0EXF _ ((Stacks.Modules.isFiniteLocallyFree_iff_localGenerators _).mpr
    ((frobeniusPullbackIter _ p hXz (N₁ + N₂)).obj Ez).property) hgen hthick
  exact ⟨N₁ + N₂, r,
    nonempty_iso_free_pullback_frobeniusPullbackIter_add a hXz hX E (N₁ + N₂) 0 r e⟩

open Scheme.Vect VectorBundleCodimensionOne in
/-- **The essential-image half of Stacks Tag 0EXH over a normal base.** Let `f : X ⟶ Y` be flat,
proper and surjective with `Y` normal and Noetherian and `f_*𝒪_X = 𝒪_Y`, all in characteristic
`p`, and let `ℰ` be a finite locally free `𝒪_X`-module satisfying the fibre condition of Stacks
Tag 0EXH. Then some Frobenius power pullback `F^{n,*}ℰ` is isomorphic to the pullback of a finite
locally free `𝒪_Y`-module. -/
theorem descendsAfterFrobenius_of_isNormal {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsProper f]
    [Surjective f] [IsNoetherian Y] [IsNormal Y] (hO : IsIso f.c)
    (hX : IsInCharacteristic X p) (E : X.Vect)
    (hE : IsFreeOnReducedFibresAfterFrobenius f p hX E) : DescendsAfterFrobenius f p hX E := by
  classical
  -- a Frobenius power making `ℰ` free over the local schemes at the points of codimension zero
  let G₀ := (Scheme.finite_setOf_ringKrullDim_stalk_eq_zero Y).toFinset
  choose N₀f hN₀f using fun y : {y : Y // ringKrullDim (Y.presheaf.stalk y) = 0} ↦
    exists_isFreeOverLocalScheme_of_ringKrullDim_eq_zero f hX hE y.1 y.2
  let N₀ : ℕ := G₀.attach.sup fun y ↦ N₀f ⟨y.1, by
    simpa only [G₀, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using y.2⟩
  have hP₀ : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) = 0 →
      IsFreeOverLocalScheme f ((frobeniusPullbackIter X p hX N₀).obj E).obj y := by
    intro y hy
    have hyG : y ∈ G₀ := (Set.Finite.mem_toFinset _).mpr hy
    exact (hN₀f ⟨y, hy⟩).frobeniusPullbackIter_mono hX
      (Finset.le_sup (f := fun y : G₀ ↦ N₀f ⟨y.1, by
        simpa only [G₀, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using y.2⟩)
        (Finset.mem_attach G₀ ⟨y, hyG⟩))
  -- the open set where this holds, and the finitely many points of codimension one outside it
  let O := {s : Y | IsFreeOverLocalScheme f ((frobeniusPullbackIter X p hX N₀).obj E).obj s}
  have hO' : IsOpen O := isOpen_setOf_isFreeOverLocalScheme f _
  let Z₁ := (Scheme.finite_setOf_ringKrullDim_stalk_eq_one_of_notMem O hO' hP₀).toFinset
  choose N₁f hN₁f using fun z : {z : Y // ringKrullDim (Y.presheaf.stalk z) = 1} ↦
    exists_isFreeOverLocalScheme_of_ringKrullDim_eq_one f hX hE z.1 z.2
  let N : ℕ := N₀ + Z₁.attach.sup fun z ↦ N₁f ⟨z.1, ((Set.Finite.mem_toFinset _).mp z.2).2⟩
  have hP : ∀ s : Y, ringKrullDim (Y.presheaf.stalk s) ≤ 1 →
      IsFreeOverLocalScheme f ((frobeniusPullbackIter X p hX N).obj E).obj s := by
    intro s hs
    by_cases hsO : s ∈ O
    · exact IsFreeOverLocalScheme.frobeniusPullbackIter_mono hX (Nat.le_add_right N₀ _) hsO
    · have hs1 : ringKrullDim (Y.presheaf.stalk s) = 1 := by
        by_contra h1
        have hlt : ringKrullDim (Y.presheaf.stalk s) < ((0 : ℕ) : WithBot ℕ∞) + 1 := by
          simpa using lt_of_le_of_ne hs h1
        have h0 : ringKrullDim (Y.presheaf.stalk s) = 0 :=
          le_antisymm (by simpa using ENat.WithBot.lt_add_one_iff.mp hlt)
            ringKrullDim_nonneg_of_nontrivial
        exact hsO (hP₀ s h0)
      have hsZ : s ∈ Z₁ := (Set.Finite.mem_toFinset _).mpr ⟨hsO, hs1⟩
      refine (hN₁f ⟨s, hs1⟩).frobeniusPullbackIter_mono hX ?_
      refine le_trans ?_ (Nat.le_add_left _ N₀)
      exact Finset.le_sup (f := fun z : Z₁ ↦ N₁f ⟨z.1, ((Set.Finite.mem_toFinset _).mp z.2).2⟩)
        (Finset.mem_attach Z₁ ⟨s, hsZ⟩)
  -- the counit of `f^* ⊣ f_*` at `F^{N,*}ℰ` is an isomorphism, by the argument of Tag 0EXG
  let EN := ((frobeniusPullbackIter X p hX N).obj E).obj
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} EN :=
    ((frobeniusPullbackIter X p hX N).obj E).property
  have hO₂ : IsIso f.toLRSHom.toHom.c := hO
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : EN.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree EN
  let _ : EN.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X EN
  let M := (Scheme.Modules.pushforward f).obj EN
  let _ : M.IsCoherent := ProperCoherenceWitness.isCoherent_pushforward f EN
  have hMqc : M.IsQuasicoherent := AlgebraicGeometry.pushforward_isQuasicoherent f EN
  let _ : M.IsQuasicoherent := hMqc
  let _ : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj EN).IsCoherent :=
    isCoherent_pullback f M
  let _ : ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback f).obj EN).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ f.toLRSHom.toShHom M hMqc
  let _ : ((𝟭 X.Modules).obj EN).IsQuasicoherent := inferInstanceAs EN.IsQuasicoherent
  have hstalkFinite : ∀ s : Y, Module.Finite (Y.presheaf.stalk s)
      (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf s) := fun s => by
    have : M.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
    exact SheafOfModules.finite_stalk Y.sheaf M s
  have hcodim : ∀ x : X, ringKrullDim (Y.presheaf.stalk (f x)) ≤ 1 →
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app EN).val)) := by
    intro x hx
    obtain ⟨r, ⟨e⟩⟩ := hP (f x) hx
    let g := Y.fromSpecStalk (f x)
    let _ : IsLocallyNoetherian (pullback f g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f g)
    have hcoh : ((Scheme.Modules.pullback (pullback.fst f g)).obj EN).IsCoherent :=
      isCoherent_pullback (pullback.fst f g) EN
    exact VectorBundleCodimensionOne.isIso_stalk_counit_of_iso_free f hO₂ EN (f x) _ e
      hcoh.isFiniteType x specializes_rfl
  obtain ⟨M', hM', ⟨e'⟩⟩ := exists_isFiniteLocallyFree_pullback_iso_of_isIso_counit f EN
    (isIso_counit_of_isIso_stalk_of_codim_le_one f EN hstalkFinite hcodim)
  exact ⟨N, ⟨M', hM'⟩, ⟨ObjectProperty.isoMk _ e'.symm⟩⟩

end AlgebraicGeometry

end
