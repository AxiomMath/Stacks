module

public import StacksFrontier.AlgebraicGeometry.Thickenings
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Infinitesimal neighbourhoods of an immersion

Let `i : Z ⟶ X` be an immersion of schemes. It factors as a closed immersion
`AlgebraicGeometry.Scheme.Hom.liftCoborder` of `Z` into the open subscheme
`AlgebraicGeometry.Scheme.Hom.coborderRange` of `X`, and the `n`th-order infinitesimal
neighbourhood of `Z` in `X` is the closed subscheme of that open subscheme cut out by the
`(n+1)`st power of the defining ideal sheaf of the factorization.

## Main definitions

* `Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood` is the `n`th-order infinitesimal
  neighbourhood.
* `Stacks.Thickenings.firstOrderInfinitesimalNeighbourhood` is the case `n = 1`.
* `Stacks.Thickenings.nthOrderι`, `Stacks.Thickenings.nthOrderInclusion` and
  `Stacks.Thickenings.nthOrderToBase` are the closed immersion of the neighbourhood into the
  ambient open subscheme, the inclusion of `Z` into the neighbourhood, and the neighbourhood's
  structure morphism to `X`.

## Main results

* `Stacks.Thickenings.nthOrderInclusion_toBase`: the two structure morphisms compose to `i`.
* `Stacks.Thickenings.nthOrderInclusion_isNthOrderThickening`: the inclusion is an `n`th-order
  thickening.
* `Stacks.Thickenings.existsUnique_nthOrderLift` and
  `Stacks.Thickenings.existsUnique_firstOrderLift`: the universal property of the `n`th-order
  and first-order infinitesimal neighbourhoods, [Stacks Project, Tag 04EZ].

## Implementation notes

The open subscheme of `X` in which `Z` is closed is not unique, and the construction of
[Stacks Project, Tag 04EY] depends on a choice of one. The choice made here is the canonical
largest one, `AlgebraicGeometry.Scheme.Hom.coborderRange`, which is `X ∖ (closure Z ∖ Z)`; the
universal property `Stacks.Thickenings.existsUnique_nthOrderLift` shows a posteriori that the
result does not depend on the choice.

The universal property is proved for all `n` at once and the first-order case is deduced from
it at `n = 1`, rather than the other way round: the Stacks proof of part (1) applies verbatim
to part (2). Its one substantial ingredient is
`Stacks.Thickenings.ker_pow_le_ker_of_comm_square`, the scheme-theoretic form of
[Stacks Project, Tag 01HP]: if `j ≫ f = a ≫ l` with `l` and `j` closed immersions and
`j.ker ^ n = ⊥`, then `l.ker ^ n ≤ f.ker`, so that `f` factors through the subscheme cut out by
`l.ker ^ n`. It is proved by reducing to affine charts of a pullback along an affine open cover,
where the statement becomes the vanishing of an `n`th power in a quotient ring.

## References

* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 04EZ](https://stacks.math.columbia.edu/tag/04EZ)
* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-! ### The construction -/

/-- **Stacks Project, Tag 04EY, part (2).** The `n`th-order infinitesimal neighbourhood of `Z`
in `X` for an immersion `i : Z ⟶ X`: the closed subscheme of the canonical open neighbourhood
`AlgebraicGeometry.Scheme.Hom.coborderRange` of the image of `i` cut out by the `(n+1)`st power
of the defining ideal sheaf of `AlgebraicGeometry.Scheme.Hom.liftCoborder`. -/
@[implicit_reducible,
  stacks 04EY "part (2): nth-order infinitesimal neighbourhood",
  ega "IV 16.1.2" "special case",
  ega "IV 19.4.6", sga "2 XI 3.18" "more general"]
def nthOrderInfinitesimalNeighbourhood (n : ℕ) : Scheme.{u} :=
  (i.liftCoborder.ker ^ (n + 1)).subscheme

/-- **Stacks Project, Tag 04EY, part (1).** The first-order infinitesimal neighbourhood of `Z`
in `X`, cut out by the square of the defining ideal sheaf of the immersion. -/
@[stacks 04EY "part (1): first-order infinitesimal neighbourhood",
  ega "IV 16.1.2" "Y^{(1)}, immersions"]
abbrev firstOrderInfinitesimalNeighbourhood : Scheme.{u} :=
  nthOrderInfinitesimalNeighbourhood i 1

/-- The closed immersion of the `n`th-order infinitesimal neighbourhood of `Z` in `X` into the
canonical open neighbourhood `AlgebraicGeometry.Scheme.Hom.coborderRange` of the image of `i`.

This is `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`, named so that the interface of the
neighbourhood does not force a consumer to spell out the ideal sheaf it is cut out by. It is an
abbreviation rather than a definition because the ideal-sheaf lemmas of Mathlib are stated for
`subschemeι` and must continue to apply to it. -/
@[ega "IV 19.4.6"]
abbrev nthOrderι (n : ℕ) :
    nthOrderInfinitesimalNeighbourhood i n ⟶ i.coborderRange.toScheme :=
  (i.liftCoborder.ker ^ (n + 1)).subschemeι

/-- The `n`th-order infinitesimal neighbourhood of `Z` in `X` is cut out by the `(n+1)`st power
of the defining ideal sheaf of the closed-immersion factorization of `i`. -/
theorem nthOrderι_ker (n : ℕ) : (nthOrderι i n).ker = i.liftCoborder.ker ^ (n + 1) :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- The inclusion of `Z` into its `n`th-order infinitesimal neighbourhood. -/
@[stacks 04EY "part (2): inclusion into the nth-order neighbourhood",
  ega "IV 16.1.2" "Y^{(n)} inclusion"]
def nthOrderInclusion (n : ℕ) : Z ⟶ nthOrderInfinitesimalNeighbourhood i n :=
  IsClosedImmersion.lift (nthOrderι i n) i.liftCoborder
    (by
      rw [nthOrderι_ker]
      exact Scheme.IdealSheafData.le_def.mpr fun U ↦ Ideal.pow_le_self (by simp))

/-- The structure morphism from the `n`th-order infinitesimal neighbourhood of `Z` in `X`
to `X`. -/
@[stacks 04EY "part (2): map from the nth-order neighbourhood to the base"]
def nthOrderToBase (n : ℕ) : nthOrderInfinitesimalNeighbourhood i n ⟶ X :=
  nthOrderι i n ≫ i.coborderRange.ι

/-- The structure morphism of the `n`th-order infinitesimal neighbourhood is the composite of its
closed immersion into the canonical open neighbourhood of the image of `i` with the open
immersion of that neighbourhood into `X`. -/
@[simp]
theorem nthOrderToBase_eq (n : ℕ) :
    nthOrderToBase i n = nthOrderι i n ≫ i.coborderRange.ι := rfl

/-- The inclusion of `Z` into its `n`th-order infinitesimal neighbourhood, followed by the
closed immersion of that neighbourhood into the canonical open neighbourhood of the image, is
the closed-immersion factorization of `i`. -/
@[reassoc (attr := simp)]
theorem nthOrderInclusion_nthOrderι (n : ℕ) :
    nthOrderInclusion i n ≫ nthOrderι i n = i.liftCoborder :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inclusion of `Z` into its `n`th-order infinitesimal neighbourhood, followed by the
structure morphism to `X`, is the original immersion. -/
@[stacks 04EY "part (2): factorization over the base"]
theorem nthOrderInclusion_toBase (n : ℕ) :
    nthOrderInclusion i n ≫ nthOrderToBase i n = i := by
  rw [nthOrderToBase_eq, nthOrderInclusion_nthOrderι_assoc, i.liftCoborder_ι]

/-- The inclusion of `Z` into its `n`th-order infinitesimal neighbourhood is a closed immersion:
its composite with the closed immersion of the neighbourhood into the ambient open subscheme is
the closed immersion `AlgebraicGeometry.Scheme.Hom.liftCoborder`. -/
instance isClosedImmersion_nthOrderInclusion (n : ℕ) :
    IsClosedImmersion (nthOrderInclusion i n) := by
  have : IsClosedImmersion (nthOrderInclusion i n ≫ nthOrderι i n) := by
    rw [nthOrderInclusion_nthOrderι]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (nthOrderι i n)

/-- The structure morphism of an infinitesimal neighbourhood is an immersion: a closed immersion
into the canonical open neighbourhood of the image of `i`, followed by an open immersion. -/
instance isImmersion_nthOrderToBase (n : ℕ) : IsImmersion (nthOrderToBase i n) := by
  rw [nthOrderToBase_eq]
  infer_instance

/-- If a surjective ring map `φ` has the `n`th power of the contraction of `J` as its kernel,
then `J ^ n = ⊥`. This is the affine-chart form of the vanishing of the defining ideal sheaf of
an infinitesimal neighbourhood. -/
private lemma ideal_pow_eq_bot_of_surjective_comap
    {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (J : Ideal S) (n : ℕ)
    (hφ : Function.Surjective φ)
    (hpow : J.comap φ ^ n = RingHom.ker φ) :
    J ^ n = ⊥ := by
  rw [← Ideal.map_comap_of_surjective φ hφ J, ← Ideal.map_pow, hpow,
    RingHom.ker_eq_comap_bot, Ideal.map_comap_of_surjective φ hφ]

/-- **Stacks Project, Tag 04EY, part (2).** The inclusion of `Z` into its `n`th-order
infinitesimal neighbourhood is an `n`th-order thickening: it is a closed immersion whose
defining ideal sheaf has vanishing `(n+1)`st power.

Affine-locally on the open neighbourhood `AlgebraicGeometry.Scheme.Hom.coborderRange`, the
`(n+1)`st power of the ideal sheaf of `i.liftCoborder` is the kernel of the surjection onto the
sections of the neighbourhood, so the `(n+1)`st power of its image vanishes. -/
@[stacks 04EY "part (2): nth-order thickening"]
theorem nthOrderInclusion_isNthOrderThickening (n : ℕ) :
    IsNthOrderThickening n (nthOrderInclusion i n) := by
  let B := i.coborderRange.toScheme
  let K : B.IdealSheafData := i.liftCoborder.ker
  let p : nthOrderInfinitesimalNeighbourhood i n ⟶ B := (K ^ (n + 1)).subschemeι
  refine ⟨inferInstance, ?_⟩
  have hker : (nthOrderInclusion i n).ker.map p = K := by
    rw [← Scheme.Hom.ker_comp]
    exact congrArg Scheme.Hom.ker (nthOrderInclusion_nthOrderι i n)
  have hpow : K ^ (n + 1) = p.ker := (Scheme.IdealSheafData.ker_subschemeι _).symm
  let U : B.affineOpens → (nthOrderInfinitesimalNeighbourhood i n).affineOpens :=
    fun V ↦ ⟨p ⁻¹ᵁ V.1, V.2.preimage p⟩
  have hcover : ⨆ V, (U V).1 = ⊤ := by
    simpa [U] using congrArg (fun V : B.Opens => p ⁻¹ᵁ V) (iSup_affineOpens_eq_top B)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover fun V ↦ ?_
  show ((nthOrderInclusion i n).ker ^ (n + 1)).ideal (U V) = ⊥
  let W := U V
  let φ := (p.app V).hom
  have hKloc : K.ideal V = ((nthOrderInclusion i n).ker.ideal W).comap φ := by
    rw [← hker]
    exact Scheme.IdealSheafData.ideal_map (I := (nthOrderInclusion i n).ker)
      p V (V.2.preimage p)
  have hpV : p.ker.ideal V = RingHom.ker φ := by
    simp [φ, Scheme.Hom.ker_apply]
  have hpowV : (K.ideal V) ^ (n + 1) = RingHom.ker φ := by
    have h := congrArg (fun J : B.IdealSheafData => J.ideal V) hpow
    simpa [Scheme.IdealSheafData.ideal_pow, hpV] using h
  have hnil := ideal_pow_eq_bot_of_surjective_comap φ
    ((nthOrderInclusion i n).ker.ideal W) (n + 1)
    ((K ^ (n + 1)).subschemeι_app_surjective V) (hKloc ▸ hpowV)
  simpa [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] using hnil

/-- **Stacks Project, Tag 04EY, part (1).** The inclusion of `Z` into its first-order
infinitesimal neighbourhood is a first-order thickening. -/
@[stacks 04EY "part (1): first-order thickening"]
theorem nthOrderInclusion_isFirstOrderThickening :
    IsFirstOrderThickening (nthOrderInclusion i 1) := by
  simpa [IsFirstOrderThickening, IsNthOrderThickening] using
    nthOrderInclusion_isNthOrderThickening i 1

/-- The inclusion of `Z` into its `n`th-order infinitesimal neighbourhood is a thickening: `Z`
and the neighbourhood have the same underlying topological space. -/
theorem nthOrderInclusion_isThickening (n : ℕ) : IsThickening (nthOrderInclusion i n) :=
  (nthOrderInclusion_isNthOrderThickening i n).isThickening

/-! ### The universal property -/

/-- Two equal morphisms of schemes have equal restricted section maps. -/
private lemma appLE_eq_of_eq {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g)
    {U : B.Opens} {V : A.Opens} (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst g
  congr 1

/-- The scheme-theoretic form of [Stacks Project, Tag 01HP]. Let `l : Z ⟶ X` and `j : T ⟶ T'` be
closed immersions and let `j ≫ f = a ≫ l` be a commutative square. If the `n`th power of the
defining ideal sheaf of `j` vanishes, then the `n`th power of the defining ideal sheaf of `l` is
contained in that of `f`, so `f` factors through the closed subscheme of `X` cut out by
`l.ker ^ n`.

The containment is checked on affine opens `V` of `X`: a section in `(l.ker ^ n).ideal V` is
shown to vanish in `Γ(T', f ⁻¹ᵁ V)` by passing to an affine open cover of `f ⁻¹ᵁ V` and, on each
chart, to the pullback of the chart along `j`, where the square identifies the section's image
with one lying in the `n`th power of a nilpotent ideal. -/
theorem ker_pow_le_ker_of_comm_square {Z X T T' : Scheme.{u}}
    (l : Z ⟶ X) [IsClosedImmersion l] (j : T ⟶ T') [IsClosedImmersion j]
    (a : T ⟶ Z) (f : T' ⟶ X) (n : ℕ)
    (h : j ≫ f = a ≫ l) (hj : j.ker ^ n = ⊥) :
    l.ker ^ n ≤ f.ker := by
  apply (Scheme.IdealSheafData.le_ofIdeals_iff).2
  intro V
  show (l.ker ^ n).ideal V ≤ RingHom.ker (f.app V).hom
  intro x hx
  let P := f ⁻¹ᵁ V.1
  let q := f.resLE V.1 P le_rfl
  let 𝒰 := P.toScheme.affineCover
  have hqzero : q.appTop.hom (V.1.topIso.inv.hom x) = 0 := by
    refine AlgebraicGeometry.Scheme.zero_of_zero_cover _ 𝒰 fun k ↦ ?_
    let c := 𝒰.f k
    let g := c ≫ q
    let w := c ≫ P.ι
    let Q := Limits.pullback w j
    let p := Limits.pullback.fst w j
    let r := Limits.pullback.snd w j
    let F := p ≫ w ≫ f
    let G := r ≫ a ≫ l
    have : IsClosedImmersion p := by infer_instance
    have : IsOpenImmersion w := by infer_instance
    have hFtop : F ⁻¹ᵁ V.1 = ⊤ := by
      simp [F, w, P]
    have hFG : F = G := by
      have hpb : p ≫ w = r ≫ j := Limits.pullback.condition
      calc
        F = (p ≫ w) ≫ f := rfl
        _ = (r ≫ j) ≫ f := congrArg (fun k => k ≫ f) hpb
        _ = G := by dsimp [G]; rw [Category.assoc, h]
    have hFle : (⊤ : Q.Opens) ≤ F ⁻¹ᵁ V.1 := by rw [hFtop]
    have hGle : (⊤ : Q.Opens) ≤ G ⁻¹ᵁ V.1 := hFG ▸ hFle
    have hFGapp : F.appLE V.1 ⊤ hFle = G.appLE V.1 ⊤ hGle :=
      appLE_eq_of_eq hFG hFle hGle
    let Ctop : (𝒰.X k).affineOpens := ⟨⊤, isAffineOpen_top (𝒰.X k)⟩
    let W : T'.affineOpens :=
      ⟨w ''ᵁ (Ctop : (𝒰.X k).Opens), Ctop.2.image_of_isOpenImmersion w⟩
    let J : Ideal Γ(T', W.1) := j.ker.ideal W
    have hJpow : J ^ n = ⊥ := by
      have h := congrArg (fun K : T'.IdealSheafData => K.ideal W) hj
      change (j.ker ^ n).ideal W = (⊥ : T'.IdealSheafData).ideal W at h
      change (j.ker.ideal W) ^ n = ⊥ at h
      simpa only [J] using h
    have hkerp : p.ker.ideal Ctop = J.comap (w.appIso Ctop).inv.hom := by
      show (Limits.pullback.fst w j).ker.ideal Ctop = _
      rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
        Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    have hkerpow : p.ker.ideal Ctop ^ n = ⊥ := by
      rw [hkerp]
      refine le_antisymm ((Ideal.le_comap_pow (w.appIso Ctop).inv.hom n).trans ?_) bot_le
      rw [hJpow, Ideal.comap_bot_of_injective _
        (ConcreteCategory.bijective_of_isIso (w.appIso Ctop).inv).1]
    have hkerApp : RingHom.ker p.appTop.hom = p.ker.ideal Ctop := by
      have hka := Scheme.Hom.ker_apply p Ctop
      change p.ker.ideal Ctop = RingHom.ker p.appTop.hom at hka
      exact hka.symm
    let φ : Γ(X, V.1) →+* Γ(𝒰.X k, ⊤) :=
      g.appTop.hom.comp (V.1.ι.appLE V.1 ⊤ (by simp)).hom
    have hι : V.1.ι.appLE V.1 ⊤ (by simp) = V.1.topIso.inv := by
      symm
      simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appLE]
      congr 1
    have hmap : Ideal.map φ (l.ker.ideal V) ≤ RingHom.ker p.appTop.hom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro y hy
      show φ y ∈ RingHom.ker p.appTop.hom
      rw [RingHom.mem_ker]
      have hcompzero : (F.appLE V.1 ⊤ hFle).hom y = 0 := by
        have hlzero : (l.app V).hom y = 0 := by
          apply RingHom.mem_ker.mp
          rw [← Scheme.Hom.ker_apply l V]
          exact hy
        have hGzero : (G.appLE V.1 ⊤ hGle).hom y = 0 := by
          simp [G, hlzero]
        rw [hFGapp]
        exact hGzero
      have hFfac : F = p ≫ g ≫ V.1.ι := by
        dsimp [F, g, w, q]
        simp [Scheme.Hom.resLE_comp_ι, Category.assoc]
      have hFle' : (⊤ : Q.Opens) ≤ (p ≫ g ≫ V.1.ι) ⁻¹ᵁ V.1 := hFfac ▸ hFle
      have hFmap' : F.appLE V.1 ⊤ hFle =
          V.1.ι.appLE V.1 ⊤ (by simp) ≫ g.appTop ≫ p.appTop := by
        have houter := Scheme.Hom.appLE_comp_appLE (f := p ≫ g) (g := V.1.ι)
          V.1 ⊤ ⊤ (by simp) (by simp)
        have hinner := Scheme.Hom.appLE_comp_appLE (f := p) (g := g)
          ⊤ ⊤ ⊤ (by simp) (by simp)
        have happ : ∀ {A B : Scheme.{u}} (k : A ⟶ B), k.appLE ⊤ ⊤ (by simp) = k.appTop :=
          fun k ↦ by simpa [Scheme.Hom.appTop] using Scheme.Hom.appLE_eq_app (f := k) (U := ⊤)
        calc
          F.appLE V.1 ⊤ hFle = (p ≫ g ≫ V.1.ι).appLE V.1 ⊤ hFle' :=
            appLE_eq_of_eq hFfac hFle hFle'
          _ = V.1.ι.appLE V.1 ⊤ (by simp) ≫ (p ≫ g).appLE ⊤ ⊤ (by simp) := by
            simpa only [Category.assoc] using houter.symm
          _ = V.1.ι.appLE V.1 ⊤ (by simp) ≫ g.appTop ≫ p.appTop := by
            rw [← hinner, happ, happ]
      have hFmap : (F.appLE V.1 ⊤ hFle).hom y = p.appTop.hom (φ y) := by
        have h := congrArg (fun k : Γ(X, V.1) ⟶ Γ(Q, ⊤) => k.hom y) hFmap'
        simpa [φ, Scheme.Hom.appLE, CommRingCat.hom_comp,
          CommRingCat.comp_apply, RingHom.comp_apply] using h
      rw [hFmap] at hcompzero
      simpa using hcompzero
    have hx' : x ∈ (l.ker.ideal V) ^ n := by
      simpa [Scheme.IdealSheafData.ideal_pow] using hx
    have hφx : φ x ∈ (RingHom.ker p.appTop.hom) ^ n := by
      have hm := Ideal.mem_map_of_mem φ hx'
      rw [Ideal.map_pow] at hm
      exact (Ideal.pow_right_mono hmap n) (by simpa [φ] using hm)
    have hφzero : φ x = 0 := by
      rw [hkerApp, hkerpow] at hφx
      simpa using hφx
    show g.appTop.hom (V.1.topIso.inv.hom x) = 0
    rw [← hι]
    simpa [φ] using hφzero
  have hfLE : (f.appLE V.1 P le_rfl).hom x = 0 := by
    have hqval : q.appTop.hom (V.1.topIso.inv.hom x) =
        P.topIso.inv.hom ((f.appLE V.1 P le_rfl).hom x) := by
      show ((f.resLE V.1 P le_rfl).appTop).hom (V.1.topIso.inv.hom x) = _
      simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply]
      rw [Iso.inv_hom_id_apply]
    rw [hqval] at hqzero
    exact (ConcreteCategory.bijective_of_isIso P.topIso.inv).1 (by simpa using hqzero)
  simpa [P, Scheme.Hom.appLE_eq_app] using hfLE

/-- **Stacks Project, Tag 04EZ, part (2).** The universal property of the `n`th-order
infinitesimal neighbourhood: given an `n`th-order thickening `j : T ⟶ T'`, a morphism
`a : T ⟶ Z` and a morphism `b : T' ⟶ X` making the square commute, there is a unique morphism
`T' ⟶ Z_n` extending `a` and lying over `b`.

Since `j` is surjective on points, `b` lands in the open subscheme
`AlgebraicGeometry.Scheme.Hom.coborderRange` and so factors as `f ≫ i.coborderRange.ι`. The
square then reads `j ≫ f = a ≫ i.liftCoborder`, so
`Stacks.Thickenings.ker_pow_le_ker_of_comm_square` gives `i.liftCoborder.ker ^ (n + 1) ≤ f.ker`
and `f` factors through the closed subscheme cut out by `i.liftCoborder.ker ^ (n + 1)`, which is
`Z_n`. Uniqueness is monomorphicity of the two immersions.

The source's hypothesis `1 ≤ n` is retained for faithfulness but is not needed: the argument is
uniform in `n`, and at `n = 0` both sides degenerate to `Z` itself. -/
@[stacks 04EZ "part (2): nth-order universal property"]
theorem existsUnique_nthOrderLift {T T' : Scheme.{u}}
    (n : ℕ) (_hn : 1 ≤ n) (j : T ⟶ T') (hj : IsNthOrderThickening n j)
    (a : T ⟶ Z) (b : T' ⟶ X) (h : j ≫ b = a ≫ i) :
    ∃! a' : T' ⟶ nthOrderInfinitesimalNeighbourhood i n,
      (j ≫ a' = a ≫ nthOrderInclusion i n) ∧ (a' ≫ nthOrderToBase i n = b) := by
  let U := i.coborderRange
  let l := i.liftCoborder
  let I : U.toScheme.IdealSheafData := l.ker ^ (n + 1)
  have hj' : IsThickening j := hj.isThickening
  have hrange : Set.range b.base ⊆ Set.range U.ι.base := by
    rintro y ⟨y', rfl⟩
    obtain ⟨x, hx⟩ := hj'.2 y'
    refine ⟨l.base (a.base x), ?_⟩
    have hpoint := congrArg (fun q : T ⟶ X => q.base x) h
    show (l ≫ U.ι).base (a.base x) = b.base y'
    rw [← hx]
    simpa [l, U, i.liftCoborder_ι] using hpoint.symm
  let f : T' ⟶ U.toScheme := IsOpenImmersion.lift U.ι b hrange
  have hf : f ≫ U.ι = b := IsOpenImmersion.lift_fac U.ι b hrange
  have hbase : j ≫ f = a ≫ l := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc, hf, h, Category.assoc, i.liftCoborder_ι]
  let _ : IsClosedImmersion j := hj'.1
  have hpow : l.ker ^ (n + 1) ≤ f.ker :=
    ker_pow_le_ker_of_comm_square l j a f (n + 1) hbase hj.2
  have hI : I.subschemeι.ker ≤ f.ker := by simpa only [I.ker_subschemeι] using hpow
  let g : T' ⟶ nthOrderInfinitesimalNeighbourhood i n := IsClosedImmersion.lift I.subschemeι f hI
  have hgι : g ≫ I.subschemeι = f := IsClosedImmersion.lift_fac I.subschemeι f hI
  have hNι : nthOrderInclusion i n ≫ I.subschemeι = l := nthOrderInclusion_nthOrderι i n
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · apply (cancel_mono I.subschemeι).1
    rw [Category.assoc, Category.assoc, hgι, hNι, hbase]
  · calc
      g ≫ nthOrderToBase i n = (g ≫ I.subschemeι) ≫ U.ι := by
        rw [Category.assoc]
        rfl
      _ = b := by rw [hgι, hf]
  · intro g' hg'
    have hg'ι : g' ≫ I.subschemeι = f := by
      apply (cancel_mono U.ι).1
      rw [Category.assoc, hf, ← hg'.2, nthOrderToBase_eq]
    exact (cancel_mono I.subschemeι).1 (hg'ι.trans hgι.symm)

/-- **Stacks Project, Tag 04EZ, part (1).** The universal property of the first-order
infinitesimal neighbourhood, the case `n = 1` of
`Stacks.Thickenings.existsUnique_nthOrderLift`. -/
@[stacks 04EZ "part (1): first-order universal property"]
theorem existsUnique_firstOrderLift {T T' : Scheme.{u}}
    (j : T ⟶ T') (hj : IsFirstOrderThickening j)
    (a : T ⟶ Z) (b : T' ⟶ X) (h : j ≫ b = a ≫ i) :
    ∃! a' : T' ⟶ firstOrderInfinitesimalNeighbourhood i,
      (j ≫ a' = a ≫ nthOrderInclusion i 1) ∧ (a' ≫ nthOrderToBase i 1 = b) :=
  existsUnique_nthOrderLift i 1 le_rfl j ⟨hj.1, by simpa using hj.2⟩ a b h

end Stacks.Thickenings

end
