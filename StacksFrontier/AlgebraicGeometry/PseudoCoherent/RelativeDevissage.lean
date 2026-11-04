module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeSummand
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTriangulated
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.Homology.PseudoCoherent.Characterization
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeBoundedComplex
import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.BoundedVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Dévissage for relative pseudo-coherence

Let `f : X ⟶ S` be a morphism of schemes locally of finite type. This file develops the
elementary calculus of the predicate "`E` is `m`-pseudo-coherent relative to `S`" of Stacks 09UI:
it is monotone in `m`, it holds for every object concentrated in degrees `< m`, it is compatible
with shifts and biproducts, and — the main point — it propagates along the stupid filtration of a
bounded above complex, so that a triangulated functor into `D(𝒪_X)` carries such a complex to a
relatively `m`-pseudo-coherent object as soon as it does so on the complex's terms placed in
their degrees.

It also records that an absolutely `m`-pseudo-coherent object on a quasi-compact open is bounded
above there by a single bound, which is the boundedness input the dévissage needs.

## Main results

* `CategoryTheory.DerivedCategory.isLE_mapDerivedCategory`: an exact additive functor preserves
  boundedness above.
* `CategoryTheory.DerivedCategory.exists_distinguished_single_stupidTrunc`: the distinguished
  triangle of the top step of the stupid filtration of a bounded above complex.
* `CategoryTheory.DerivedCategory.property_map_of_boundedAbove`: the stupid-filtration dévissage
  for an arbitrary two-out-of-three property of derived objects.
* `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.mono` and
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_isLE`: monotonicity in `m`, and
  relative `m`-pseudo-coherence of an object of `D^{≤ m - 1}(𝒪_X)`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_shift_one_iff` and
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_shift_iff`: shifting by `n` raises by `n`
  the degree an object is relatively pseudo-coherent from.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_biprod`: a biproduct of two relatively
  `m`-pseudo-coherent objects is relatively `m`-pseudo-coherent.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_map_of_boundedAbove`,
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_map_finiteFree` and
  `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_map_of_modulePseudoCoherent`: the dévissage
  at the relative predicate, over a bounded above complex, over a finite free module, and over a
  pseudo-coherent module through its bounded above finite free resolution.
* `AlgebraicGeometry.exists_isZero_homology_restrict_of_isCompact` and
  `AlgebraicGeometry.exists_isLE_of_isPseudoCoherentFrom`: an `m`-pseudo-coherent object of
  `D(𝒪_Y)` has, on every quasi-compact open of `Y`, a single degree above which all its
  cohomology sheaves vanish there; on a quasi-compact `Y` it is bounded above.

## Implementation notes

**The shift.** Both directions of `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_shift_one_iff`
come from the contractible triangle `(E, 0, E⟦1⟧)` and Stacks 09UL: parts (1) and (3) of that
lemma applied to it, the middle term being zero and therefore relatively pseudo-coherent in every
degree. The general integer shift is an induction on the shift along `Int.induction_on`, the
comparison `E⟦n + 1⟧ ≅ (E⟦n⟧)⟦1⟧` being `CategoryTheory.shiftFunctorAdd'`.

**The dévissage is stated for a property, not for pseudo-coherence.** The only facts about
relative `m`-pseudo-coherence that the induction over the stupid filtration uses are closure
under isomorphism, the two-out-of-three rule of Stacks 09UL, and its validity below the degree
`m`. `CategoryTheory.DerivedCategory.property_map_of_boundedAbove` therefore takes those three as
hypotheses on an arbitrary `CategoryTheory.ObjectProperty`, and the relative and absolute
statements are two instantiations of it.

The boundedness hypothesis `hF` of that lemma is asked for only on complexes whose terms satisfy a
property `Q` of objects, rather than on every object of the derived category. That weaker form is
what a functor given by a derived tensor product satisfies: its right t-exactness is known only
on complexes whose terms are flat, and the stupid truncations of the complex the dévissage runs
over do keep that property, since `Q` is required to be closed under isomorphism and to contain
the zero objects.

**The relative predicate, not the absolute one.** For an object that is only *relatively*
pseudo-coherent on a chart, the absolute derived-tensor estimate
`Stacks.Cohomology.PseudoCoherentTensor.isPseudoCoherentFrom_derivedTensorProduct` cannot be used
in place of the relative dévissage. Transporting the relative condition into the ambient affine
space of the chart and tensoring there would need derived pushforward along the closed immersion
of the chart to commute with `⊗^𝐋`, and it does not: already for the closed immersion
`jZ : {0} ⟶ 𝔸¹` and `F = k` the unit `Lj_Z^*Rj_{Z*}F ⟶ F` is not invertible, the source being
`k ⊕ k[1]`. The dévissage above therefore runs with the relative predicate on the chart itself.

**Boundedness above is read off a strictly perfect approximation.** The local comparison
`α : P ⟶ 𝓕|_O` provided by absolute `m`-pseudo-coherence is an isomorphism on cohomology in
degrees `> m`, and `P` is a bounded complex, so the cohomology of `𝓕|_O` vanishes above the
larger of `m` and a bound for `P`. Those pointwise bounds are made uniform on a quasi-compact
open by `AlgebraicGeometry.exists_isZero_restrict_of_isCompact`.

The two spellings of restriction of modules to an open —
`AlgebraicGeometry.RingedSpace.restrictModules`, in which the sheaf-level predicate is stated, and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`, in which the uniform bound is stated — are
compared by an isomorphism of functors, as in
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.resLE`.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.6 (09UL)](https://stacks.math.columbia.edu/tag/09UL)
* [The Stacks Project, Lemma 36.61.9 (09UN)](https://stacks.math.columbia.edu/tag/09UN)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open StrictlyPerfect

universe w u

namespace CategoryTheory.DerivedCategory

/-! ### Boundedness above through an exact functor -/

/-- **An exact additive functor preserves boundedness above.** A representative of `K` with no
terms above `n` is carried to a complex with no terms above `n`, which represents the image
of `K`. -/
@[sga "6 I 2.13" "special case"]
public theorem isLE_mapDerivedCategory {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : DerivedCategory C) (n : ℤ)
    (hK : K.IsLE n) : (G.mapDerivedCategory.obj K).IsLE n := by
  have := hK
  obtain ⟨L, hL, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE n
  have := hL
  have : CochainComplex.IsStrictlyLE
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n :=
    (CochainComplex.isStrictlyLE_iff _ n).2 fun i hi =>
      Functor.map_isZero G (L.isZero_of_isStrictlyLE n i hi)
  refine (DerivedCategory.isLE_iff _ n).2 fun i hi => ?_
  exact (DerivedCategory.isZero_of_isLE
      (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) n i hi).of_iso
    ((DerivedCategory.homologyFunctor D i).mapIso
      (G.mapDerivedCategory.mapIso e ≪≫ G.mapDerivedCategoryFactors.app L))

/-! ### The top step of the stupid filtration -/

section

variable {C : Type*} [Category C] [Abelian C]

/-- **The top step of the stupid filtration of a bounded above complex.** For `L` a complex with
no terms above `b`, the degreewise split inclusion of its top term placed in degree `b` and the
projection to its stupid truncation in degrees `≤ b - 1` form a distinguished triangle of the
derived category. -/
public theorem exists_distinguished_single_stupidTrunc [HasDerivedCategory.{w} C]
    (L : CochainComplex C ℤ) (b : ℤ) [L.IsStrictlyLE b] :
    ∃ (f : (DerivedCategory.singleFunctor C b).obj (L.X b) ⟶ DerivedCategory.Q.obj L)
      (g : DerivedCategory.Q.obj L ⟶
        DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))))
      (h : DerivedCategory.Q.obj (L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))) ⟶
        ((DerivedCategory.singleFunctor C b).obj (L.X b))⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles := by
  obtain ⟨ι, hιb⟩ := _root_.DerivedCategory.exists_hom_from_single_isIso_f L b
  obtain ⟨π, hπ⟩ := _root_.DerivedCategory.exists_hom_to_stupidTrunc_isIso_f L b
  have hMb : IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntLE (b - 1))).X b) :=
    _root_.DerivedCategory.isZero_stupidTrunc_X_of_lt L (by omega)
  have hcomp : ι ≫ π = 0 := HomologicalComplex.hom_ext _ _ fun i => by
    by_cases hi : i = b
    · subst hi
      exact hMb.eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) b (L.X b) i hi).eq_of_src _ _
  have hSE : (ShortComplex.mk ι π hcomp).ShortExact := by
    refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
    by_cases hi : i = b
    · subst hi
      exact ShortComplex.shortExact_of_isIso_f_of_isZero_X₃ _ hιb hMb
    · exact ShortComplex.shortExact_of_isZero_X₁_of_isIso_g _
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) b (L.X b) i hi) (hπ i hi)
  exact ⟨_, _, _, Pretriangulated.mk_mem_distTriang_of_iso _
    (DerivedCategory.triangleOfSES_distinguished hSE)
    ((DerivedCategory.singleFunctorIsoCompQ C b).app (L.X b))⟩

/-! ### The dévissage -/

/-- **The stupid-filtration dévissage.** Let `P` be a property of objects of `D(D)` which is
closed under isomorphism, satisfies two-out-of-three in distinguished triangles and holds on
every object of `D^{≤ m - 1}(D)`, and let `F : D(C) ⥤ D(D)` be triangulated. Then `P` holds on
`F(K)` for every bounded above complex `K` of objects of `C` on whose terms, placed in their own
degrees, `P` holds after `F`.

The boundedness hypothesis `hF` on `F` is required only on complexes all of whose terms satisfy a
property `Q` which is closed under isomorphism and contains the zero objects, so that it is
inherited by the stupid truncations of `K` that the induction meets. -/
public theorem property_map_of_boundedAbove {D : Type*} [Category D] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (P : ObjectProperty (DerivedCategory D))
    (hiso : ∀ {K L}, P K → (K ≅ L) → P L)
    (hext : ∀ T : Triangle (DerivedCategory D), T ∈ distinguishedTriangles →
      P T.obj₁ → P T.obj₃ → P T.obj₂)
    (F : DerivedCategory C ⥤ DerivedCategory D)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] (a m : ℤ)
    (hvanish : ∀ L : DerivedCategory D, L.IsLE (m - 1) → P L)
    (Q : ObjectProperty C)
    (hQiso : ∀ {M N : C}, Q M → (M ≅ N) → Q N)
    (hQzero : ∀ M : C, IsZero M → Q M)
    (hF : ∀ (L : CochainComplex C ℤ) (n : ℤ), (∀ i : ℤ, Q (L.X i)) →
      L.IsStrictlyLE n → (F.obj (DerivedCategory.Q.obj L)).IsLE (n + a))
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hKQ : ∀ i : ℤ, Q (K.X i))
    (hterms : ∀ i : ℤ, P (F.obj ((DerivedCategory.singleFunctor C i).obj (K.X i)))) :
    P (F.obj (DerivedCategory.Q.obj K)) := by
  have hz (M : C) (i : ℤ) (hM : IsZero M) :
      P (F.obj ((DerivedCategory.singleFunctor C i).obj M)) := by
    refine hvanish _ ((DerivedCategory.isLE_iff _ _).2 fun j _ => ?_)
    exact (DerivedCategory.homologyFunctor _ j).map_isZero
      (F.map_isZero ((DerivedCategory.singleFunctor C i).map_isZero hM))
  have aux : ∀ (n : ℕ) (L : CochainComplex C ℤ),
      L.IsStrictlyLE (m - 1 - a + n) → (∀ i : ℤ, Q (L.X i)) →
      (∀ i : ℤ, P (F.obj ((DerivedCategory.singleFunctor C i).obj (L.X i)))) →
      P (F.obj (DerivedCategory.Q.obj L)) := by
    intro n
    induction n with
    | zero =>
        intro L hL hQL _
        have hL0 : L.IsStrictlyLE (m - 1 - a) := by simpa using hL
        refine hvanish _ ?_
        convert hF L (m - 1 - a) hQL hL0 using 1
        ring
    | succ n ih =>
        intro L hL hQL hterms
        set c : ℤ := m - 1 - a + (n + 1 : ℕ) with hc
        have : L.IsStrictlyLE c := hL
        set L' : CochainComplex C ℤ :=
          L.stupidTrunc (ComplexShape.embeddingUpIntLE (c - 1))
        obtain ⟨f₀, g₀, h₀, hT⟩ := exists_distinguished_single_stupidTrunc L c
        have hL' : L'.IsStrictlyLE (m - 1 - a + n) :=
          (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
            _root_.DerivedCategory.isZero_stupidTrunc_X_of_lt L (by rw [hc]; push_cast; omega)
        have hQL' : ∀ i : ℤ, Q (L'.X i) := by
          intro i
          by_cases hi : i ≤ c - 1
          · exact hQiso (hQL i)
              (L.stupidTruncXIso _
                (_root_.DerivedCategory.embeddingUpIntLE_f_toNat (c - 1) i hi)).symm
          · exact hQzero _ (_root_.DerivedCategory.isZero_stupidTrunc_X_of_lt L (by omega))
        have hterms' : ∀ i : ℤ,
            P (F.obj ((DerivedCategory.singleFunctor C i).obj (L'.X i))) := by
          intro i
          by_cases hi : i ≤ c - 1
          · exact hiso (hterms i)
              (F.mapIso ((DerivedCategory.singleFunctor C i).mapIso
                (L.stupidTruncXIso _
                  (_root_.DerivedCategory.embeddingUpIntLE_f_toNat (c - 1) i hi)).symm))
          · exact hz (L'.X i) i (_root_.DerivedCategory.isZero_stupidTrunc_X_of_lt L (by omega))
        exact hext (F.mapTriangle.obj (Triangle.mk f₀ g₀ h₀)) (F.map_distinguished _ hT)
          (hterms c) (ih L' hL' hQL' hterms')
  exact aux (b - (m - 1 - a)).toNat K
    ((CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => K.isZero_of_isStrictlyLE b i (by omega))
    hKQ hterms

end

end CategoryTheory.DerivedCategory

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Elementary stability of relative pseudo-coherence -/

/-- **Relative `m`-pseudo-coherence is monotone in `m`.** The witnessing covers and closed
immersions are unchanged; only the sheaf-level condition at each of them is weakened, by
`AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom.mono`. -/
public theorem IsPseudoCoherentFrom.mono [LocallyOfFiniteType f] {E : DerivedCategory X.Modules}
    {m m' : ℤ} (h : IsPseudoCoherentFrom f E m) (hmm : m ≤ m') :
    IsPseudoCoherentFrom f E m' := by
  obtain ⟨ι, V, hV, hU⟩ := h
  refine ⟨ι, V, hV, fun i => ?_⟩
  obtain ⟨κ, U, hUc, hUl⟩ := hU i
  refine ⟨κ, U, hUc, fun j => ?_⟩
  obtain ⟨hle, n, g, hg, hcomm, hpc⟩ := hUl j
  obtain ⟨K, eK, c, hc, hpc'⟩ := hpc
  exact ⟨hle, n, g, hg, hcomm, ⟨K, eK, c, hc, hpc'.mono hmm⟩⟩

/-- **An object of `D^{≤ m - 1}(𝒪_X)` is `m`-pseudo-coherent relative to `S`.** Restriction to an
affine open and pushforward along a closed immersion into affine space are exact, so they preserve
the cohomological bound, and the sheaf-level condition then holds by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isLE`. -/
public theorem isPseudoCoherentFrom_of_isLE [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ) [E.IsLE (m - 1)] :
    IsPseudoCoherentFrom f E m := by
  refine isPseudoCoherentFrom_of_forall_affinePair f E m fun U V hUV => ?_
  obtain ⟨n, i, hi, hio⟩ := exists_isClosedImmersion_affineSpace_resLE f V U hUV
  have := hi
  refine ⟨n, i, hi, hio, (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).2 ?_⟩
  have h1 : ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E).IsLE (m - 1) :=
    DerivedCategory.isLE_mapDerivedCategory _ E (m - 1) ‹_›
  have h2 := DerivedCategory.isLE_mapDerivedCategory (Scheme.Modules.pushforward i)
    ((Scheme.Modules.restrictFunctor U.1.ι).mapDerivedCategory.obj E) (m - 1) h1
  exact @RingedSpace.isPseudoCoherentFrom_of_isLE
    (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).toRingedSpace _ _ m h2

/-- **Shifting once raises by one the degree an object is relatively pseudo-coherent from.** Both
directions are Stacks 09UL at the contractible triangle `(E, 0, E⟦1⟧)`, whose middle term is
relatively pseudo-coherent in every degree. -/
public theorem isPseudoCoherentFrom_shift_one_iff [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ) :
    IsPseudoCoherentFrom f (E⟦(1 : ℤ)⟧) m ↔ IsPseudoCoherentFrom f E (m + 1) :=
  ⟨fun h => isPseudoCoherentFrom_obj₁_of_distinguished f m _
      (contractible_distinguished₂ E)
      (isPseudoCoherentFrom_of_isZero f (isZero_zero _) (m + 1)) h,
    fun h => isPseudoCoherentFrom_obj₃_of_distinguished f m _
      (contractible_distinguished₂ E) h
      (isPseudoCoherentFrom_of_isZero f (isZero_zero _) m)⟩

/-- **Shifting by `n` raises by `n` the degree an object is relatively pseudo-coherent from.** -/
public theorem isPseudoCoherentFrom_shift_iff [LocallyOfFiniteType f] (n : ℤ) :
    ∀ (E : DerivedCategory X.Modules) (m : ℤ),
      IsPseudoCoherentFrom f (E⟦n⟧) m ↔ IsPseudoCoherentFrom f E (m + n) := by
  induction n using Int.induction_on with
  | zero =>
      intro E m
      have e : E⟦(0 : ℤ)⟧ ≅ E := (shiftFunctorZero (DerivedCategory X.Modules) ℤ).app E
      rw [add_zero]
      exact ⟨fun h => h.of_iso f e, fun h => h.of_iso f e.symm⟩
  | succ k ih =>
      intro E m
      have e : E⟦((k : ℤ) + 1)⟧ ≅ (E⟦(k : ℤ)⟧)⟦(1 : ℤ)⟧ :=
        (shiftFunctorAdd' (DerivedCategory X.Modules) (k : ℤ) 1 ((k : ℤ) + 1) rfl).app E
      have hA : IsPseudoCoherentFrom f (E⟦((k : ℤ) + 1)⟧) m ↔
          IsPseudoCoherentFrom f ((E⟦(k : ℤ)⟧)⟦(1 : ℤ)⟧) m :=
        ⟨fun h => h.of_iso f e, fun h => h.of_iso f e.symm⟩
      exact hA.trans ((isPseudoCoherentFrom_shift_one_iff f (E⟦(k : ℤ)⟧) m).trans
        ((ih E (m + 1)).trans (by rw [show m + 1 + (k : ℤ) = m + ((k : ℤ) + 1) by ring])))
  | pred k ih =>
      intro E m
      have e : (E⟦(-(k : ℤ) - 1)⟧)⟦(1 : ℤ)⟧ ≅ E⟦(-(k : ℤ))⟧ :=
        ((shiftFunctorAdd' (DerivedCategory X.Modules) (-(k : ℤ) - 1) 1 (-(k : ℤ))
          (by ring)).app E).symm
      have hA : IsPseudoCoherentFrom f ((E⟦(-(k : ℤ) - 1)⟧)⟦(1 : ℤ)⟧) (m - 1) ↔
          IsPseudoCoherentFrom f (E⟦(-(k : ℤ) - 1)⟧) m := by
        refine (isPseudoCoherentFrom_shift_one_iff f (E⟦(-(k : ℤ) - 1)⟧) (m - 1)).trans ?_
        rw [show m - 1 + 1 = m by ring]
      have hB : IsPseudoCoherentFrom f ((E⟦(-(k : ℤ) - 1)⟧)⟦(1 : ℤ)⟧) (m - 1) ↔
          IsPseudoCoherentFrom f (E⟦(-(k : ℤ))⟧) (m - 1) :=
        ⟨fun h => h.of_iso f e, fun h => h.of_iso f e.symm⟩
      exact hA.symm.trans (hB.trans ((ih E (m - 1)).trans
        (by rw [show m - 1 + -(k : ℤ) = m + (-(k : ℤ) - 1) by ring])))

/-- A biproduct of two objects `m`-pseudo-coherent relative to `S` is `m`-pseudo-coherent relative
to `S`: it is the middle term of the split distinguished triangle on the two summands, so
Stacks 09UL part (2) applies. The converse is Stacks 09UN. -/
public theorem isPseudoCoherentFrom_biprod [LocallyOfFiniteType f]
    (E K : DerivedCategory X.Modules) (m : ℤ) (hE : IsPseudoCoherentFrom f E m)
    (hK : IsPseudoCoherentFrom f K m) : IsPseudoCoherentFrom f (E ⊞ K) m :=
  isPseudoCoherentFrom_obj₂_of_distinguished f m _
    (binaryBiproductTriangle_distinguished E K) hE hK

/-! ### The dévissage at the relative predicate -/

/-- **The stupid-filtration dévissage for relative pseudo-coherence.** Let
`F : D(C) ⥤ D(𝒪_X)` be triangulated and let `K` be a bounded above complex of objects of `C`
whose terms satisfy a property `Q` closed under isomorphism and containing the zero objects. If
`F` raises the cohomological bound of a complex with `Q`-terms by at most `a`, and if `F` carries
each term of `K`, placed in its own degree, to an object `m`-pseudo-coherent relative to `S`, then
`F(K)` is `m`-pseudo-coherent relative to `S`. -/
public theorem isPseudoCoherentFrom_map_of_boundedAbove {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] [LocallyOfFiniteType f]
    (F : DerivedCategory C ⥤ DerivedCategory X.Modules)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] (a m : ℤ)
    (Q : ObjectProperty C)
    (hQiso : ∀ {M N : C}, Q M → (M ≅ N) → Q N)
    (hQzero : ∀ M : C, IsZero M → Q M)
    (hF : ∀ (L : CochainComplex C ℤ) (n : ℤ), (∀ i : ℤ, Q (L.X i)) →
      L.IsStrictlyLE n → (F.obj (DerivedCategory.Q.obj L)).IsLE (n + a))
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hKQ : ∀ i : ℤ, Q (K.X i))
    (hterms : ∀ i : ℤ,
      IsPseudoCoherentFrom f (F.obj ((DerivedCategory.singleFunctor C i).obj (K.X i))) m) :
    IsPseudoCoherentFrom f (F.obj (DerivedCategory.Q.obj K)) m :=
  DerivedCategory.property_map_of_boundedAbove
    (fun E => IsPseudoCoherentFrom f E m)
    (fun h e => h.of_iso f e)
    (isPseudoCoherentFrom_obj₂_of_distinguished f m)
    F a m (fun L hL => by have := hL; exact isPseudoCoherentFrom_of_isLE f L m)
    Q hQiso hQzero hF K b hKQ hterms

/-- **The dévissage over a finite free module.** An additive functor from `R`-modules to
`D(𝒪_X)` which carries `R` to an object `m`-pseudo-coherent relative to `S` carries every finite
free `R`-module there, by induction on a basis through
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_biprod`. -/
public theorem isPseudoCoherentFrom_map_finiteFree {R : Type u} [Ring R] [LocallyOfFiniteType f]
    (F : ModuleCat.{u} R ⥤ DerivedCategory X.Modules) [F.Additive] (m : ℤ)
    (hF : IsPseudoCoherentFrom f (F.obj (ModuleCat.of R (ULift.{u} R))) m)
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Free R M] :
    IsPseudoCoherentFrom f (F.obj M) m := by
  classical
  let motive (N : Type u) [AddCommGroup N] [Module R N] : Prop :=
    IsPseudoCoherentFrom f (F.obj (ModuleCat.of R N)) m
  have he : ∀ {N N' : Type u} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'],
      (N ≃ₗ[R] N') → motive N → motive N' := by
    intro N N' _ _ _ _ e h
    exact h.of_iso f (F.mapIso e.toModuleIso)
  have hzero : motive PUnit :=
    isPseudoCoherentFrom_of_isZero f
      (F.map_isZero (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit))) m
  have hprod : ∀ {N N' : Type u} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'],
      motive N → motive N' → motive (N × N') := by
    intro N N' _ _ _ _ hN hN'
    have : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
    have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
    exact (isPseudoCoherentFrom_biprod f _ _ m hN hN').of_iso f
      ((F.mapBiprod (ModuleCat.of R N) (ModuleCat.of R N')).symm ≪≫
        F.mapIso (ModuleCat.biprodIsoProd (ModuleCat.of R N) (ModuleCat.of R N')))
  have hpi : motive (Module.Free.ChooseBasisIndex R M → ULift.{u} R) :=
    Module.pi_induction' R motive motive he he hzero hprod
      (fun _ : Module.Free.ChooseBasisIndex R M => ULift.{u} R) fun _ => hF
  exact he ((Module.Free.chooseBasis R M).equivFun.trans
    (LinearEquiv.piCongrRight fun _ => (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm)).symm hpi

/-- **The dévissage over a pseudo-coherent module.** A module pseudo-coherent in every degree has
a bounded above finite free resolution, and the dévissage over it reduces the claim to the single
free module `R` placed in degree zero. The terms of the resolution placed in their own degrees are
reached from degree zero by a shift, which is where
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_shift_iff` and monotonicity in `m` are used. -/
public theorem isPseudoCoherentFrom_map_of_modulePseudoCoherent {R : Type u} [Ring R]
    [LocallyOfFiniteType f]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory X.Modules)
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] (a m : ℤ)
    (Q : ObjectProperty (ModuleCat.{u} R))
    (hQiso : ∀ {M N : ModuleCat.{u} R}, Q M → (M ≅ N) → Q N)
    (hQzero : ∀ M : ModuleCat.{u} R, IsZero M → Q M)
    (hQff : ∀ N : ModuleCat.{u} R, Module.Finite R N → Module.Free R N → Q N)
    (hF : ∀ (L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ), (∀ i : ℤ, Q (L.X i)) →
      L.IsStrictlyLE n → (F.obj (DerivedCategory.Q.obj L)).IsLE (n + a))
    (hunit : IsPseudoCoherentFrom f
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (ULift.{u} R)))) m)
    (M : ModuleCat.{u} R)
    (hM : ∀ k : ℤ, StacksDraft.PseudoCoherence.IsModulePseudoCoherentFrom (R := R) M k) :
    IsPseudoCoherentFrom f
      (F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) m := by
  set T := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M with hT
  have hMT : StacksDraft.PseudoCoherence.IsPseudoCoherent T :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
      T 0).1.mpr hM
  obtain ⟨E, α, hE, hE0, hα⟩ :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
      T 0).2.2 hMT fun i hi => DerivedCategory.isZero_of_isLE T 0 i hi
  have hFE : IsPseudoCoherentFrom f (F.obj (DerivedCategory.Q.obj E)) m := by
    refine isPseudoCoherentFrom_map_of_boundedAbove f F a m Q hQiso hQzero hF E 0
      (fun i => hQff (E.X i) (hE i).1 (hE i).2) fun i => ?_
    by_cases hi : i ≤ 0
    · have := (hE i).1
      have := (hE i).2
      have hsingle := isPseudoCoherentFrom_map_finiteFree f
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙ F) m hunit (E.X i)
      have hshift : IsPseudoCoherentFrom f
          ((F.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (E.X i)))⟦-i⟧)
          (m + i) :=
        (isPseudoCoherentFrom_shift_iff f (-i) _ (m + i)).2
          (by rwa [show m + i + -i = m by ring])
      exact (hshift.mono f (show m + i ≤ m by omega)).of_iso f
        ((F.commShiftIso (-i)).symm.app _ ≪≫
          F.mapIso (((DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso
            (-i) i 0 (by omega)).app (E.X i)))
    · exact isPseudoCoherentFrom_of_isZero f
        (F.map_isZero ((DerivedCategory.singleFunctor _ i).map_isZero
          (E.isZero_of_isStrictlyLE 0 i (by omega)))) m
  exact hFE.of_iso f (F.mapIso (asIso α))

end Scheme.Hom

/-! ### Global boundedness above on a quasi-compact open -/

/-- The two spellings of restriction of sheaves of modules to an open subscheme agree. -/
private def restrictFunctorIsoRestrictModules (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Modules.restrictFunctor U.ι ≅ RingedSpace.restrictModules X.toRingedSpace U := by
  simp only [Scheme.Modules.restrictFunctor, Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact Iso.refl _

/-- Restriction to an open subspace is exact, hence commutes with the cohomology of a complex. -/
private def restrictComplexHomologyIso (X : Scheme.{u}) (U : X.Opens)
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ) (j : ℤ) :
    (RingedSpace.restrictComplex E U).homology j ≅
      (RingedSpace.restrictModules X.toRingedSpace U).obj (E.homology j) :=
  have := RingedSpace.restrictModules_preservesFiniteLimits X.toRingedSpace U
  have := RingedSpace.restrictModules_preservesFiniteColimits X.toRingedSpace U
  (E.sc j).mapHomologyIso (RingedSpace.restrictModules X.toRingedSpace U)

/-- Vanishing of the cohomology of a restricted complex, read in the other spelling of
restriction. -/
private lemma isZero_restrict_homology_of_isZero_restrictComplex (Y : Scheme.{u})
    (O : Y.Opens) (K : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) ℤ)
    (i : ℤ) (hz : IsZero ((RingedSpace.restrictComplex K O).homology i)) :
    IsZero ((Scheme.Modules.restrictFunctor O.ι).obj (K.homology i)) :=
  (hz.of_iso (restrictComplexHomologyIso Y O K i).symm).of_iso
    ((restrictFunctorIsoRestrictModules Y O).app (K.homology i))

/-- The same, transported along a representative of an object of the derived category. -/
private lemma isZero_restrict_homology_of_isZero_restrictComplex_of_iso (Y : Scheme.{u})
    (O : Y.Opens) (K : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace) ℤ)
    (E : DerivedCategory Y.Modules) (eK : DerivedCategory.Q.obj K ≅ E) (i : ℤ)
    (hz : IsZero ((RingedSpace.restrictComplex K O).homology i)) :
    IsZero ((Scheme.Modules.restrictFunctor O.ι).obj
      ((DerivedCategory.homologyFunctor Y.Modules i).obj E)) := by
  refine (isZero_restrict_homology_of_isZero_restrictComplex Y O K i hz).of_iso ?_
  exact (Scheme.Modules.restrictFunctor O.ι).mapIso
    (((DerivedCategory.homologyFunctor Y.Modules i).mapIso eK).symm ≪≫
      (DerivedCategory.homologyFunctorFactors Y.Modules i).app K)

/-- **An `m`-pseudo-coherent object is bounded above on every quasi-compact open, with a single
bound.** Near every point the strictly perfect approximation of a representative is a bounded
complex and the comparison is an isomorphism on cohomology above `m`, which bounds the cohomology
of the object there; `AlgebraicGeometry.exists_isZero_restrict_of_isCompact` makes those bounds
uniform on a quasi-compact open. -/
@[sga "6 III 1.2.1" "special case"]
public theorem exists_isZero_homology_restrict_of_isCompact {Y : Scheme.{u}}
    (E : DerivedCategory Y.Modules) (m : ℤ)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) E m)
    (U : Y.Opens) (hU : IsCompact (U : Set Y)) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
        ((DerivedCategory.homologyFunctor Y.Modules i).obj E)) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  refine exists_isZero_restrict_of_isCompact
    (fun i => (DerivedCategory.homologyFunctor Y.Modules i).obj E) U hU fun x _ => ?_
  obtain ⟨O, hxO, P, hP, α, hα, -⟩ := hK x
  obtain ⟨c, hc⟩ := hP.bounded.bddAbove
  have hPzero : ∀ i : ℤ, c < i → IsZero (P.X i) := by
    intro i hi
    by_contra h
    exact absurd (hc (show i ∈ {j : ℤ | ¬ IsZero (P.X j)} from h)) (by omega)
  have hPLE : P.IsStrictlyLE c := (CochainComplex.isStrictlyLE_iff P c).2 hPzero
  refine ⟨(O : Y.Opens), hxO, max c m, fun i hi => ?_⟩
  have hiso : IsIso (HomologicalComplex.homologyMap α i) := hα i (by omega)
  have hz : IsZero ((RingedSpace.restrictComplex K O).homology i) :=
    (ShortComplex.isZero_homology_of_isZero_X₂ (P.sc i)
      (P.isZero_of_isStrictlyLE c i (by omega))).of_iso
      (asIso (HomologicalComplex.homologyMap α i)).symm
  exact isZero_restrict_homology_of_isZero_restrictComplex_of_iso Y (O : Y.Opens) K E eK i hz

/-- **An `m`-pseudo-coherent object on a quasi-compact scheme is bounded above.** The uniform
bound on the whole space is the one of
`AlgebraicGeometry.exists_isZero_homology_restrict_of_isCompact` at the open `⊤`, and a sheaf of
modules whose restriction to `⊤` vanishes has vanishing stalks, hence vanishes. -/
public theorem exists_isLE_of_isPseudoCoherentFrom {Y : Scheme.{u}} [CompactSpace Y]
    (E : DerivedCategory Y.Modules) (m : ℤ)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := Y.toRingedSpace) E m) :
    ∃ b : ℤ, E.IsLE b := by
  obtain ⟨b, hb⟩ := exists_isZero_homology_restrict_of_isCompact E m hE ⊤
    (by simpa using isCompact_univ (X := Y))
  refine ⟨b, (DerivedCategory.isLE_iff E b).2 fun i hi => ?_⟩
  refine isZero_of_forall_isZero_stalk _ fun x => ?_
  exact (Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk ⊤ _).1 (hb i hi) x trivial

end AlgebraicGeometry

end
