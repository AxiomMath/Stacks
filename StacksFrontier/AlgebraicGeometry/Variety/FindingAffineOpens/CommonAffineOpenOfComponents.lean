module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromSurjectiveUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.AvoidingPrimes

/-!
# A finite set of points contained in affine opens of the components

Let `X` be a scheme with finitely many irreducible components and let `T ⊆ X` be a finite set
of points. If, component by component, `T` meets each irreducible component inside an affine
open of the corresponding reduced induced closed subscheme, then `T` lies in a single affine
open subscheme of `X`.

The components are glued in one at a time. Given an affine open `U` of the reduced induced
subscheme on `Z₁ ∪ … ∪ Z_{r-1}` containing the part of `T` there, and an affine open `V` of the
one on `Z_r` containing `T ∩ Z_r`, the closed subset of `U` lying on `Z_r` but outside `V` misses
`T`, so simultaneous avoidance of the finitely many primes of `T` shrinks `U` to a standard open
disjoint from it; the symmetric step shrinks `V`. Both shrinkings are arranged by one function on
`V` and a function on `U` restricting to it, which makes `U ∩ V` closed in each of `U` and `V`, so
that `U ∪ V` is covered by two affine closed subschemes and is therefore affine. The induction
ends with an affine open of the reduced induced subscheme on all of `X`, whose inclusion is a
surjective closed immersion, and a surjective universally closed morphism from an affine scheme
has affine target.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_containing_of_components`: the common affine open.

## Implementation notes

An irreducible component is presented as a closed subset whose carrier lies in
`irreducibleComponents`, and its reduced induced closed subscheme as the closed subscheme of the
vanishing ideal sheaf of that closed set. Containment of points in an affine open of such a
subscheme is expressed through the range of the composite of the open and closed immersions
into `X`.

## References

* [Stacks Project, Tag 09NM](https://stacks.math.columbia.edu/tag/09NM)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- A scheme set theoretically covered by finitely many affine closed subschemes is affine: the
induced morphism from their coproduct is finite, hence universally closed, and it is surjective
with affine source. -/
private theorem isAffine_of_surjective_sigmaDesc_of_isClosedImmersion
    {ι : Type v} [Finite ι] {W : Scheme.{u}} {Z : ι → Scheme.{u}}
    (q : ∀ i, Z i ⟶ W) [∀ i, IsAffine (Z i)] [∀ i, IsClosedImmersion (q i)]
    [Surjective (Sigma.desc q)] : IsAffine W :=
  have : IsFinite (Sigma.desc q) := AlgebraicGeometry.isFinite_sigmaDesc
  Stacks.AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed (Sigma.desc q)

private lemma mem_basicOpen_iff_not_mem_primeIdeal {S : Scheme.{u}}
    (hTop : IsAffineOpen (⊤ : S.Opens))
    (x : S) (f : Γ(S, ⊤)) :
    x ∈ S.basicOpen f ↔
      f ∉ (hTop.primeIdealOf ⟨x, trivial⟩).asIdeal := by
  have key : hTop.primeIdealOf ⟨x, trivial⟩ ∈ hTop.fromSpec ⁻¹ᵁ S.basicOpen f ↔
      x ∈ S.basicOpen f :=
    iff_of_eq (congrArg (· ∈ S.basicOpen f) (hTop.fromSpec_primeIdealOf ⟨x, trivial⟩))
  rw [← key, hTop.fromSpec_preimage_basicOpen]
  exact Iff.rfl

private lemma mem_zeroLocus_iff_ideal_le_prime {S : Scheme.{u}}
    (hTop : IsAffineOpen (⊤ : S.Opens))
    (I : Ideal Γ(S, ⊤)) (x : S) :
    x ∈ S.zeroLocus (U := ⊤) I ↔
      I ≤ (hTop.primeIdealOf ⟨x, trivial⟩).asIdeal := by
  rw [Scheme.mem_zeroLocus_iff (X := S) (U := ⊤) (↑I)]
  exact ⟨fun hx f hf => not_not.mp fun hn =>
      hx f hf ((mem_basicOpen_iff_not_mem_primeIdeal hTop x f).2 hn),
    fun hle f hf hx => (mem_basicOpen_iff_not_mem_primeIdeal hTop x f).1 hx (hle hf)⟩

/-- Finitely many points of an affine scheme outside the zero locus of an ideal `I` lie in the
standard open of some lift of any class modulo `I`. -/
private lemma exists_lift_subset_basicOpen_of_finite {S : Scheme.{u}} [IsAffine S]
    (I : Ideal Γ(S, ⊤)) (T : Set S) (hT : T.Finite)
    (hTI : ∀ x ∈ T, x ∉ S.zeroLocus (U := ⊤) I) (c : Γ(S, ⊤) ⧸ I) :
    ∃ f : Γ(S, ⊤), Ideal.Quotient.mk I f = c ∧ T ⊆ S.basicOpen f := by
  have hTop : IsAffineOpen (⊤ : S.Opens) := isAffineOpen_top S
  let : Fintype T := hT.fintype
  let e := Fintype.equivFin T
  obtain ⟨f, hf, hq⟩ := Ideal.exists_lift_avoiding_primes I
    (fun i => (hTop.primeIdealOf ⟨(e.symm i).1, trivial⟩).asIdeal) (fun _ => inferInstance)
    (fun i hle => hTI _ (e.symm i).2 ((mem_zeroLocus_iff_ideal_le_prime hTop I _).2 hle)) c
  exact ⟨f, hq, fun x hx =>
    (mem_basicOpen_iff_not_mem_primeIdeal hTop x f).2 (by simpa using hf (e ⟨x, hx⟩))⟩

private lemma exists_basicOpen_containing_finite_subset
    {S : Scheme.{u}} (hS : IsAffine S) (T : Set S) (hT : T.Finite)
    (O : S.Opens) (hTO : T ⊆ O) :
    ∃ f : Γ(S, ⊤), T ⊆ S.basicOpen f ∧ S.basicOpen f ≤ O := by
  obtain ⟨I, hI⟩ := (S.eq_zeroLocus_of_isClosed_of_isAffine (O : Set S)ᶜ).mp O.2.isClosed_compl
  obtain ⟨f, hq, hf⟩ := exists_lift_subset_basicOpen_of_finite I T hT (fun x hx h => by
    rw [← hI] at h
    exact h (hTO hx)) 0
  refine ⟨f, hf, fun x hx => not_not.mp fun hxO => ?_⟩
  exact (Scheme.mem_zeroLocus_iff (X := S) (U := ⊤) (↑I) x).mp (by rwa [← hI]) f
    (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hq)) hx

private lemma exists_section_extending_finite_nonvanishing
    {C U : Scheme.{u}} (j : C ⟶ U) [IsClosedImmersion j] (hU : IsAffine U)
    (T : Set U) (hT : T.Finite) (s : Γ(C, ⊤))
    (hOn : ∀ x ∈ T, ∀ y : C, j y = x → y ∈ C.basicOpen s) :
    ∃ g : Γ(U, ⊤), j.appTop g = s ∧ T ⊆ U.basicOpen g := by
  classical
  have : IsAffine C := isAffine_of_isAffineHom j
  obtain ⟨g₀, hg₀⟩ := j.app_surjective ⊤ (isAffineOpen_top U) s
  let I : Ideal Γ(U, ⊤) := RingHom.ker j.appTop.hom
  have hRange : Set.range j = U.zeroLocus (U := ⊤) I := by
    calc
      Set.range j = closure (Set.range j) :=
        j.isClosedEmbedding.isClosed_range.closure_eq.symm
      _ = j.ker.support := (Scheme.Hom.support_ker j).symm
      _ = U.zeroLocus (U := ⊤) I := by
        rw [Scheme.ker_of_isAffine j]
        rfl
  obtain ⟨g, hgquot, hgAvoid⟩ := exists_lift_subset_basicOpen_of_finite I
    {x | x ∈ T ∧ x ∉ Set.range j} (hT.subset fun _ hx => hx.1)
    (fun x hx h => hx.2 (by rwa [hRange]))
    (Ideal.Quotient.mk I g₀)
  have hmap : j.appTop g = s := by
    refine (sub_eq_zero.mp ?_ : j.appTop g = j.appTop g₀).trans hg₀
    rw [← RingHom.map_sub]
    exact RingHom.mem_ker.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem g g₀).mp hgquot)
  refine ⟨g, hmap, fun x hxT => ?_⟩
  by_cases hxj : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hxj
    change y ∈ j ⁻¹ᵁ U.basicOpen g
    rw [j.preimage_basicOpen_top, hmap]
    exact hOn (j y) hxT y rfl
  · exact hgAvoid ⟨hxT, hxj⟩

private lemma isClosed_range_diff_open {A A' Y : Type*} [TopologicalSpace A]
    [TopologicalSpace A']
    [TopologicalSpace Y] (f : A → Y) (hf : Topology.IsClosedEmbedding f)
    (u : A' → A) (hu : Topology.IsOpenEmbedding u) :
    IsClosed (Set.range f \ Set.range (f ∘ u)) := by
  rw [Set.range_comp, ← Set.image_compl_eq_range_sdiff_image hf.injective]
  exact hf.isClosedMap _ hu.isOpen_range.isClosed_compl

/-- The lift of `g` through an open immersion `f` agrees with `g` after applying `f`. -/
private lemma apply_lift_eq {X Y U : Scheme.{u}} (f : U ⟶ Y) [IsOpenImmersion f] (g : X ⟶ Y)
    (h : Set.range g ⊆ Set.range f) (z : X) : f (IsOpenImmersion.lift f g h z) = g z :=
  congrArg (fun k : X ⟶ Y => k z) (IsOpenImmersion.lift_fac f g h)

/-- The lift of a preimmersion into an open subscheme is a closed immersion once its range is
closed. -/
private lemma isClosedImmersion_lift_of_isClosed_range {A W : Scheme.{u}} (O : W.Opens)
    (a : A ⟶ W) [IsPreimmersion a] (h : Set.range a ⊆ Set.range O.ι)
    (hc : IsClosed (Set.range (IsOpenImmersion.lift O.ι a h))) :
    IsClosedImmersion (IsOpenImmersion.lift O.ι a h) := by
  have : IsPreimmersion (IsOpenImmersion.lift O.ι a h ≫ O.ι) := by
    rw [IsOpenImmersion.lift_fac]
    infer_instance
  have : IsPreimmersion (IsOpenImmersion.lift O.ι a h) := IsPreimmersion.of_comp _ O.ι
  exact IsClosedImmersion.of_isPreimmersion _ hc

private lemma range_lift_eq_preimage {A B O W : Type*}
    (a : A → O) (i : O → W) (f : A → W) (g : B → W) (S : Set W)
    (hi : Function.Injective i) (hfac : i ∘ a = f)
    (hO : Set.range i = Set.range f ∪ Set.range g)
    (hfs : Set.range f ⊆ S) (hcompat : Set.range g ∩ S ⊆ Set.range f) :
    Set.range a = i ⁻¹' S := by
  rw [← Set.preimage_image_eq (Set.range a) hi, ← Set.range_comp, hfac]
  refine Set.Subset.antisymm (fun _ hx => hfs hx) fun x hx => ?_
  have hxO : i x ∈ Set.range f ∪ Set.range g := by
    rw [← hO]
    exact ⟨x, rfl⟩
  exact hxO.elim id fun hx' => hcompat ⟨hx', hx⟩

/-- A scheme covered set theoretically by the images of finitely many closed immersions from
affine schemes is affine. -/
private theorem isAffine_of_isClosedImmersion_of_forall_exists
    {ι : Type v} [Finite ι] {W : Scheme.{u}} {Z : ι → Scheme.{u}}
    (q : ∀ i, Z i ⟶ W) [∀ i, IsAffine (Z i)] [∀ i, IsClosedImmersion (q i)]
    (hq : ∀ x, ∃ i y, q i y = x) : IsAffine W := by
  have : Surjective (Sigma.desc q) := ⟨fun x => by
    obtain ⟨i, y, rfl⟩ := hq x
    exact ⟨Sigma.ι Z i y, congrArg (fun k : Z i ⟶ W => k y) (Sigma.ι_comp_desc q i)⟩⟩
  exact isAffine_of_surjective_sigmaDesc_of_isClosedImmersion q

/-- A finite set of points of an affine scheme whose images avoid a closed set lies in a standard
open whose image avoids it. -/
private lemma exists_basicOpen_forall_not_mem {A W : Scheme.{u}} [IsAffine A] (a : A ⟶ W)
    {T K : Set W} (hT : (a ⁻¹' T).Finite) (hK : IsClosed K)
    (hTK : ∀ x, a x ∈ T → a x ∉ K) :
    ∃ s : Γ(A, ⊤), a ⁻¹' T ⊆ A.basicOpen s ∧ ∀ x ∈ A.basicOpen s, a x ∉ K := by
  obtain ⟨s, hsT, hsK⟩ := exists_basicOpen_containing_finite_subset inferInstance (a ⁻¹' T) hT
    ⟨(a ⁻¹' K)ᶜ, (hK.preimage a.continuous).isOpen_compl⟩ hTK
  exact ⟨s, hsT, fun x hx => hsK hx⟩

/-- If a commuting square surjects onto the pairs of points with equal images, and subsets `E`
and `H` of the two sources have the same preimage in it, then the part of the image of `E` over
the second map lies in the image of `H`. -/
private lemma image_inter_range_subset_of_preimage_eq {A B P W : Type*} (a : A → W)
    (b : B → W) (pA : P → A) (pB : P → B) (hp : ∀ z, a (pA z) = b (pB z))
    (hab : ∀ x y, a x = b y → ∃ z, pA z = x ∧ pB z = y) {E : Set A} {H : Set B}
    (hEH : pA ⁻¹' E = pB ⁻¹' H) : a '' E ∩ Set.range b ⊆ b '' H := by
  rintro _ ⟨⟨x, hx, rfl⟩, y, hy⟩
  obtain ⟨z, rfl, rfl⟩ := hab x y hy.symm
  have hz : z ∈ pB ⁻¹' H := by rwa [← hEH]
  exact ⟨pB z, hz, (hp z).symm⟩

/-- Given a standard open of an open `V` of the source of a closed immersion `g`, a standard
open of an affine scheme `A` over the same target can be chosen so that the two standard opens
have the same points over each other. -/
private lemma exists_basicOpen_range_compat {A B W : Scheme.{u}} [IsAffine A] (a : A ⟶ W)
    (g : B ⟶ W) [IsClosedImmersion g] (V : B.Opens)
    (hag : Set.range a ∩ Set.range g ⊆ Set.range (V.ι ≫ g)) (s : Γ(V.toScheme, ⊤))
    {T : Set W} (hT : (a ⁻¹' T).Finite) (hTs : (V.ι ≫ g) ⁻¹' T ⊆ V.toScheme.basicOpen s) :
    ∃ r : Γ(A, ⊤), a ⁻¹' T ⊆ A.basicOpen r ∧
      Set.range ((A.basicOpen r).ι ≫ a) ∩ Set.range g ⊆
        Set.range ((V.toScheme.basicOpen s).ι ≫ V.ι ≫ g) ∧
      Set.range ((V.toScheme.basicOpen s).ι ≫ V.ι ≫ g) ∩ Set.range a ⊆
        Set.range ((A.basicOpen r).ι ≫ a) := by
  let P : Scheme := pullback a g
  let pA : P ⟶ A := pullback.fst a g
  let pB : P ⟶ B := pullback.snd a g
  have hpair (z : P) : a (pA z) = g (pB z) :=
    congrArg (fun k : P ⟶ W => k z) (pullback.condition (f := a) (g := g))
  have : IsClosedImmersion pA := inferInstance
  let e : P ⟶ V.toScheme := IsOpenImmersion.lift V.ι pB (by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hag ⟨⟨pA z, hpair z⟩, ⟨pB z, rfl⟩⟩
    exact ⟨w, g.isClosedEmbedding.injective hw⟩)
  have he (z : P) : V.ι (e z) = pB z := apply_lift_eq V.ι pB _ z
  have hp (z : P) : a (pA z) = (V.ι ≫ g) (e z) :=
    (hpair z).trans (congrArg (⇑g) (he z)).symm
  have hab (x : A) (y : V.toScheme) (h : a x = (V.ι ≫ g) y) : ∃ z, pA z = x ∧ e z = y := by
    obtain ⟨z, hzA, hzB⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := a) (g := g) x (V.ι y) h
    exact ⟨z, hzA, V.ι.isOpenEmbedding.injective ((he z).trans hzB)⟩
  have : IsAffine P := isAffine_of_isAffineHom pA
  have hsP (x : A) (hx : x ∈ a ⁻¹' T) (y : P) (hy : pA y = x) :
      y ∈ P.basicOpen (e.appTop s) := by
    have hpre : y ∈ e ⁻¹ᵁ V.toScheme.basicOpen s := hTs (show (V.ι ≫ g) (e y) ∈ T by
      rw [← hp, hy]
      exact hx)
    rwa [e.preimage_basicOpen_top] at hpre
  obtain ⟨r, hrEq, hrT⟩ :=
    exists_section_extending_finite_nonvanishing pA inferInstance _ hT (e.appTop s) hsP
  have hEH' : pA ⁻¹ᵁ A.basicOpen r = e ⁻¹ᵁ V.toScheme.basicOpen s := by
    rw [pA.preimage_basicOpen_top, e.preimage_basicOpen_top, hrEq]
  have hEH : pA ⁻¹' (A.basicOpen r : Set A) =
      e ⁻¹' (V.toScheme.basicOpen s : Set V.toScheme) := congrArg SetLike.coe hEH'
  refine ⟨r, hrT, ?_, ?_⟩
  · rintro _ ⟨⟨x, rfl⟩, hxg⟩
    have hx : ((A.basicOpen r).ι ≫ a) x ∈
        a '' (A.basicOpen r : Set A) ∩ Set.range (V.ι ≫ g) :=
      ⟨⟨x.1, x.2, rfl⟩, hag ⟨⟨x.1, rfl⟩, hxg⟩⟩
    obtain ⟨y, hy, hyx⟩ :=
      image_inter_range_subset_of_preimage_eq a (V.ι ≫ g) pA e hp hab hEH hx
    exact ⟨⟨y, hy⟩, hyx⟩
  · rintro _ ⟨⟨x, rfl⟩, hxa⟩
    have hx : ((V.toScheme.basicOpen s).ι ≫ V.ι ≫ g) x ∈
        (V.ι ≫ g) '' (V.toScheme.basicOpen s : Set V.toScheme) ∩ Set.range a :=
      ⟨⟨x.1, x.2, rfl⟩, hxa⟩
    obtain ⟨y, hy, hyx⟩ := image_inter_range_subset_of_preimage_eq (V.ι ≫ g) a e pA
      (fun z => (hp z).symm) (fun x y h => (hab y x h.symm).imp fun _ h => h.symm) hEH.symm hx
    exact ⟨⟨y, hy⟩, hyx⟩

/-- The lift of `a` into an open `O` covered by the images of `a` and `b` is a closed immersion
when the image of `a` is cut out by a closed set that the image of `b` meets only inside it. -/
private lemma isClosedImmersion_lift_of_range_eq {A B W : Scheme.{u}} (O : W.Opens)
    (a : A ⟶ W) (b : B ⟶ W) [IsPreimmersion a] {S : Set W} (hS : IsClosed S)
    (hO : Set.range O.ι = Set.range a ∪ Set.range b) (haS : Set.range a ⊆ S)
    (hbS : Set.range b ∩ S ⊆ Set.range a) (h : Set.range a ⊆ Set.range O.ι) :
    IsClosedImmersion (IsOpenImmersion.lift O.ι a h) := by
  have hr := range_lift_eq_preimage (IsOpenImmersion.lift O.ι a h) O.ι a b S
    O.ι.isOpenEmbedding.injective (funext (apply_lift_eq O.ι a h)) hO haS hbS
  refine isClosedImmersion_lift_of_isClosed_range O a h ?_
  rw [hr]
  exact hS.preimage O.ι.continuous

/-- Two affine schemes immersed into `W`, with images open in two closed sets covering `W` and
agreeing over each other, have an affine open union of images. -/
private lemma exists_isAffineOpen_eq_range_union {A B W : Scheme.{u}} (a : A ⟶ W)
    (b : B ⟶ W) [IsAffine A] [IsAffine B] [IsPreimmersion a] [IsPreimmersion b]
    {Sa Sb : Set W} (hSa : IsClosed Sa) (hSb : IsClosed Sb) (hcover : Sa ∪ Sb = Set.univ)
    (haS : Set.range a ⊆ Sa) (hbS : Set.range b ⊆ Sb)
    (ha : IsClosed (Sa \ Set.range a)) (hb : IsClosed (Sb \ Set.range b))
    (hab : Set.range a ∩ Sb ⊆ Set.range b) (hba : Set.range b ∩ Sa ⊆ Set.range a) :
    ∃ O : W.Opens, IsAffineOpen O ∧ (O : Set W) = Set.range a ∪ Set.range b := by
  have hOcomp : (Set.range a ∪ Set.range b)ᶜ = (Sa \ Set.range a) ∪ (Sb \ Set.range b) := by
    ext y
    constructor
    · intro hy
      rcases (hcover ▸ Set.mem_univ y : y ∈ Sa ∪ Sb) with hya | hyb
      exacts [Or.inl ⟨hya, fun h => hy (Or.inl h)⟩, Or.inr ⟨hyb, fun h => hy (Or.inr h)⟩]
    · rintro (⟨hya, hna⟩ | ⟨hyb, hnb⟩) (h | h)
      exacts [hna h, hna (hba ⟨h, hya⟩), hnb (hab ⟨h, hyb⟩), hnb h]
  let O : W.Opens := ⟨Set.range a ∪ Set.range b, by
    rw [← compl_compl (Set.range a ∪ Set.range b), hOcomp]
    exact (ha.union hb).isOpen_compl⟩
  have hO : Set.range O.ι = Set.range a ∪ Set.range b := Scheme.Opens.range_ι O
  have hA : Set.range a ⊆ Set.range O.ι := hO ▸ Set.subset_union_left
  have hB : Set.range b ⊆ Set.range O.ι := hO ▸ Set.subset_union_right
  have := isClosedImmersion_lift_of_range_eq O a b hSa hO haS hba hA
  have := isClosedImmersion_lift_of_range_eq O b a hSb (hO.trans (Set.union_comm _ _)) hbS hab hB
  let Z : Bool → Scheme := fun i => if i then B else A
  let q : ∀ i, Z i ⟶ O.toScheme
    | false => IsOpenImmersion.lift O.ι a hA
    | true => IsOpenImmersion.lift O.ι b hB
  have : ∀ i, IsAffine (Z i) := by rintro (_ | _) <;> dsimp [Z] <;> infer_instance
  have : ∀ i, IsClosedImmersion (q i) := by rintro (_ | _) <;> dsimp [q] <;> assumption
  refine ⟨O, isAffine_of_isClosedImmersion_of_forall_exists q fun x => ?_, rfl⟩
  obtain ⟨z, hz⟩ | ⟨z, hz⟩ : O.ι x ∈ Set.range a ∪ Set.range b := x.2
  · exact ⟨false, z, O.ι.isOpenEmbedding.injective
      ((apply_lift_eq O.ι a hA z).trans hz)⟩
  · exact ⟨true, z, O.ι.isOpenEmbedding.injective
      ((apply_lift_eq O.ι b hB z).trans hz)⟩

private lemma exists_affineOpen_of_two_closed_cover
    {A B W : Scheme.{u}} (f : A ⟶ W) (g : B ⟶ W)
    [IsClosedImmersion f] [IsClosedImmersion g]
    (hcover : Set.range f ∪ Set.range g = Set.univ)
    {T : Set W} (hT : T.Finite)
    (U : A.Opens) (hU : IsAffineOpen U)
    (hTU : T ∩ Set.range f ⊆ Set.range (U.ι ≫ f))
    (V : B.Opens) (hV : IsAffineOpen V)
    (hTV : T ∩ Set.range g ⊆ Set.range (V.ι ≫ g)) :
    ∃ O : W.Opens, IsAffineOpen O ∧ T ⊆ O := by
  let a₀ : U.toScheme ⟶ W := U.ι ≫ f
  let b₀ : V.toScheme ⟶ W := V.ι ≫ g
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  obtain ⟨fs, hFA, hFgood⟩ := exists_basicOpen_forall_not_mem a₀
    (hT.preimage a₀.injective.injOn) (K := Set.range g \ Set.range b₀)
    (isClosed_range_diff_open g g.isClosedEmbedding V.ι V.ι.isOpenEmbedding)
    fun x hx hxK => hxK.2 (hTV ⟨hx, hxK.1⟩)
  let F : U.toScheme.Opens := U.toScheme.basicOpen fs
  let a₁ : F.toScheme ⟶ W := F.ι ≫ a₀
  have hcompat₁ : Set.range a₁ ∩ Set.range g ⊆ Set.range b₀ := by
    rintro _ ⟨⟨x, rfl⟩, hxg⟩
    exact not_not.mp fun hxb => hFgood x.1 x.2 ⟨hxg, hxb⟩
  have : IsAffine F.toScheme := (isAffineOpen_top U.toScheme).basicOpen fs
  obtain ⟨hs, hH, hHgood⟩ := exists_basicOpen_forall_not_mem b₀
    (hT.preimage b₀.injective.injOn) (K := Set.range f \ Set.range a₁)
    (isClosed_range_diff_open f f.isClosedEmbedding (F.ι ≫ U.ι) (F.ι ≫ U.ι).isOpenEmbedding)
    fun x hx hxK => by
      obtain ⟨y, hy⟩ := hTU ⟨hx, hxK.1⟩
      exact hxK.2 ⟨⟨y, hFA (by rwa [Set.mem_preimage, hy])⟩, hy⟩
  obtain ⟨r, hrT, hcompat₂, hcompat₃⟩ := exists_basicOpen_range_compat a₁ g V hcompat₁ hs
    (hT.preimage a₁.injective.injOn) hH
  let E : F.toScheme.Opens := F.toScheme.basicOpen r
  let H : V.toScheme.Opens := V.toScheme.basicOpen hs
  let a₂ : E.toScheme ⟶ W := E.ι ≫ a₁
  let b₁ : H.toScheme ⟶ W := H.ι ≫ V.ι ≫ g
  have hba : Set.range b₁ ∩ Set.range f ⊆ Set.range a₂ := by
    rintro _ ⟨⟨x, rfl⟩, hxf⟩
    exact hcompat₃ ⟨⟨x, rfl⟩, not_not.mp fun h => hHgood x.1 x.2 ⟨hxf, h⟩⟩
  have : IsAffine E.toScheme := (isAffineOpen_top F.toScheme).basicOpen r
  have : IsAffine H.toScheme := (isAffineOpen_top V.toScheme).basicOpen hs
  have : IsPreimmersion a₂ := inferInstanceAs (IsPreimmersion (E.ι ≫ F.ι ≫ U.ι ≫ f))
  have : IsPreimmersion b₁ := inferInstanceAs (IsPreimmersion (H.ι ≫ V.ι ≫ g))
  obtain ⟨O, hO, hOeq⟩ := exists_isAffineOpen_eq_range_union a₂ b₁
    f.isClosedEmbedding.isClosed_range g.isClosedEmbedding.isClosed_range hcover
    (fun _ ⟨z, hz⟩ => ⟨U.ι (F.ι (E.ι z)), hz⟩) (fun _ ⟨z, hz⟩ => ⟨V.ι (H.ι z), hz⟩)
    (isClosed_range_diff_open f f.isClosedEmbedding (E.ι ≫ F.ι ≫ U.ι)
      (E.ι ≫ F.ι ≫ U.ι).isOpenEmbedding)
    (isClosed_range_diff_open g g.isClosedEmbedding (H.ι ≫ V.ι) (H.ι ≫ V.ι).isOpenEmbedding)
    hcompat₂ hba
  refine ⟨O, hO, fun x hx => ?_⟩
  rw [hOeq]
  rcases (hcover ▸ Set.mem_univ x : x ∈ Set.range f ∪ Set.range g) with hxf | hxg
  · obtain ⟨y, hy⟩ := hTU ⟨hx, hxf⟩
    have hyF : y ∈ F := hFA (by rwa [Set.mem_preimage, hy])
    have hyE : (⟨y, hyF⟩ : F.toScheme) ∈ E := hrT (show a₀ y ∈ T by rwa [hy])
    exact Or.inl ⟨⟨⟨y, hyF⟩, hyE⟩, hy⟩
  · obtain ⟨y, hy⟩ := hTV ⟨hx, hxg⟩
    exact Or.inr ⟨⟨y, hH (by rwa [Set.mem_preimage, hy])⟩, hy⟩

/-- The reduced induced closed subscheme on `Z` has image `Z`. -/
private lemma range_subschemeι_vanishingIdeal {X : Scheme.{u}} (Z : Closeds X) :
    Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = Z := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- The inclusion of closed subschemes `V(J) ⟶ V(I)` has image the preimage of `V(J)`. -/
private lemma range_inclusion_eq_preimage {X : Scheme.{u}} {I J : X.IdealSheafData}
    (h : I ≤ J) :
    Set.range (Scheme.IdealSheafData.inclusion h) =
      I.subschemeι ⁻¹' Set.range J.subschemeι := by
  rw [← Scheme.IdealSheafData.inclusion_subschemeι h]
  change _ = I.subschemeι ⁻¹' Set.range (I.subschemeι ∘ Scheme.IdealSheafData.inclusion h)
  rw [Set.range_comp, Set.preimage_image_eq _ I.subschemeι.injective]

/-- The inductive step: affine opens of the reduced induced subschemes on `Z₁` and `Z₂`
containing the relevant points of `T` give one on `Z₂ ⊔ Z₁`. -/
private lemma exists_isAffineOpen_subscheme_of_eq_sup {X : Scheme.{u}} {T : Set X}
    (hT : T.Finite) (Z Z₁ Z₂ : Closeds X) (hZ : Z = Z₂ ⊔ Z₁)
    (U : (Scheme.IdealSheafData.vanishingIdeal Z₁).subscheme.Opens) (hU : IsAffineOpen U)
    (hUT : {y | (Scheme.IdealSheafData.vanishingIdeal Z₁).subschemeι y ∈ T} ⊆ U)
    (V : (Scheme.IdealSheafData.vanishingIdeal Z₂).subscheme.Opens) (hV : IsAffineOpen V)
    (hVT : T ∩ (Z₂ : Set X) ⊆
      Set.range (V.ι ≫ (Scheme.IdealSheafData.vanishingIdeal Z₂).subschemeι)) :
    ∃ O : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens, IsAffineOpen O ∧
      {y | (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι y ∈ T} ⊆ O := by
  subst hZ
  have h₁ := Scheme.IdealSheafData.vanishingIdeal_antimono (le_sup_right : Z₁ ≤ Z₂ ⊔ Z₁)
  have h₂ := Scheme.IdealSheafData.vanishingIdeal_antimono (le_sup_left : Z₂ ≤ Z₂ ⊔ Z₁)
  let qN := (Scheme.IdealSheafData.vanishingIdeal (Z₂ ⊔ Z₁)).subschemeι
  let f := Scheme.IdealSheafData.inclusion h₁
  let g := Scheme.IdealSheafData.inclusion h₂
  have hcover : Set.range f ∪ Set.range g = Set.univ := by
    rw [range_inclusion_eq_preimage, range_inclusion_eq_preimage, ← Set.preimage_union,
      range_subschemeι_vanishingIdeal, range_subschemeι_vanishingIdeal, ← Closeds.coe_sup,
      sup_comm Z₁ Z₂, ← range_subschemeι_vanishingIdeal (Z₂ ⊔ Z₁), Set.preimage_range]
  have hTU : qN ⁻¹' T ∩ Set.range f ⊆ Set.range (U.ι ≫ f) := by
    rintro _ ⟨hyT, z, rfl⟩
    have hpoint : qN (f z) = (Scheme.IdealSheafData.vanishingIdeal Z₁).subschemeι z :=
      congrArg (fun k : (Scheme.IdealSheafData.vanishingIdeal Z₁).subscheme ⟶ X => k z)
        (Scheme.IdealSheafData.inclusion_subschemeι h₁)
    have hzt : (Scheme.IdealSheafData.vanishingIdeal Z₁).subschemeι z ∈ T := hpoint ▸ hyT
    exact ⟨⟨z, hUT hzt⟩, rfl⟩
  have hTV : qN ⁻¹' T ∩ Set.range g ⊆ Set.range (V.ι ≫ g) := by
    rintro _ ⟨hyT, z, rfl⟩
    have hpoint : qN (g z) = (Scheme.IdealSheafData.vanishingIdeal Z₂).subschemeι z :=
      congrArg (fun k : (Scheme.IdealSheafData.vanishingIdeal Z₂).subscheme ⟶ X => k z)
        (Scheme.IdealSheafData.inclusion_subschemeι h₂)
    have hzt : (Scheme.IdealSheafData.vanishingIdeal Z₂).subschemeι z ∈ T := hpoint ▸ hyT
    obtain ⟨v, hv⟩ := hVT ⟨hzt, (range_subschemeι_vanishingIdeal Z₂).subset ⟨z, rfl⟩⟩
    have hvz : V.ι v = z :=
      (Scheme.IdealSheafData.vanishingIdeal Z₂).subschemeι.injective (by simpa using hv)
    exact ⟨v, congrArg (⇑g) hvz⟩
  exact exists_affineOpen_of_two_closed_cover f g hcover (hT.preimage qN.injective.injOn)
    U hU hTU V hV hTV

/-- The image of an affine open under a surjective closed immersion is an affine open. -/
private lemma exists_isAffineOpen_image_of_surjective {X Y : Scheme.{u}} (q : Y ⟶ X)
    [IsClosedImmersion q] (hq : Function.Surjective q) (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ O : X.Opens, IsAffineOpen O ∧ (O : Set X) = q '' U := by
  have hhomeo : IsHomeomorph q :=
    q.isClosedEmbedding.toHomeomorphOfSurjective hq |>.isHomeomorph
  let O : X.Opens := ⟨q '' U, hhomeo.isOpenMap _ U.2⟩
  refine ⟨O, ?_, rfl⟩
  have : IsAffine U.toScheme := hU
  have hsub : Set.range (U.ι ≫ q) ⊆ Set.range O.ι := by
    rintro _ ⟨z, rfl⟩
    exact ⟨⟨q (U.ι z), U.ι z, z.2, rfl⟩, rfl⟩
  let r : U.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι (U.ι ≫ q) hsub
  have hrange : Set.range r = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨z, hz, hzy⟩ : y.1 ∈ q '' U := y.2
    exact ⟨⟨z, hz⟩, O.ι.isOpenEmbedding.injective
      ((apply_lift_eq O.ι (U.ι ≫ q) hsub ⟨z, hz⟩).trans hzy)⟩
  have : IsClosedImmersion r :=
    isClosedImmersion_lift_of_isClosed_range O _ hsub (hrange ▸ isClosed_univ)
  have : Surjective r := ⟨Set.range_eq_univ.mp hrange⟩
  exact Stacks.AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed r

/-- **[Stacks, Tag 09NM].** Let `X` be a scheme with finitely many irreducible components and
`T ⊆ X` a finite set of points. If for every irreducible component `Z` the set `T ∩ Z` is
contained in an affine open of the reduced induced closed subscheme on `Z`, then `T` is
contained in an affine open subscheme of `X`. -/
@[stacks 09NM]
public theorem exists_isAffineOpen_containing_of_components
    (X : Scheme.{u}) {T : Set X} (hT : T.Finite)
    (hcomponents : (irreducibleComponents X).Finite)
    (hlocal : ∀ Z : Closeds X, (Z : Set X) ∈ irreducibleComponents X →
      ∃ U : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme.Opens,
        IsAffineOpen U ∧
          T ∩ (Z : Set X) ⊆
            Set.range (U.ι ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ T ⊆ U := by
  classical
  let C := irreducibleComponents X
  let : Fintype C := hcomponents.fintype
  let cset : C → Closeds X := fun c =>
    ⟨(c : Set X), isClosed_of_mem_irreducibleComponents _ c.2⟩
  let support (F : Finset C) : Closeds X := F.sup cset
  let ideal (F : Finset C) : X.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (support F)
  let Y (F : Finset C) : Scheme := (ideal F).subscheme
  let q (F : Finset C) : Y F ⟶ X := (ideal F).subschemeι
  let points (F : Finset C) : Set (Y F) := {y | q F y ∈ T}
  have hInd : ∀ F : Finset C,
      ∃ U : (Y F).Opens, IsAffineOpen U ∧ points F ⊆ U := by
    intro F
    induction F using Finset.induction with
    | empty =>
        have : IsAffine (Y ∅) := by
          simpa [Y, ideal, support] using
            (inferInstance : IsAffine ((⊤ : X.IdealSheafData).subscheme))
        exact ⟨⊤, isAffineOpen_top (Y ∅), Set.subset_univ _⟩
    | @insert c F hc ih =>
        obtain ⟨U, hU, hUF⟩ := ih
        obtain ⟨V, hV, hVC⟩ := hlocal (cset c) (by simp [cset])
        exact exists_isAffineOpen_subscheme_of_eq_sup hT (support (insert c F)) (support F)
          (cset c) (by simp [support]) U hU hUF V hV hVC
  obtain ⟨U, hU, hUT⟩ := hInd Finset.univ
  have hfull : support Finset.univ = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    have hx' : x ∈ ⋃₀ C := by
      rw [sUnion_irreducibleComponents]
      exact Set.mem_univ x
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hx'
    exact Finset.le_sup (f := cset) (Finset.mem_univ ⟨Z, hZ⟩) hxZ
  have hsurj : Function.Surjective (q Finset.univ) := by
    intro x
    change x ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal (support Finset.univ)).subschemeι
    rw [range_subschemeι_vanishingIdeal, hfull]
    exact Set.mem_univ x
  obtain ⟨O, hO, hOU⟩ := exists_isAffineOpen_image_of_surjective (q Finset.univ) hsurj U hU
  refine ⟨O, hO, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [hOU]
  exact ⟨y, hUT hx, rfl⟩

end AlgebraicGeometry

end
