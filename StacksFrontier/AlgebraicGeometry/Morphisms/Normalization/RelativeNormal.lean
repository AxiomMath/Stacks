module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksFrontier.AlgebraicGeometry.Limits.SigmaIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative normalization in a normal scheme

Let `f : X ⟶ Y` be quasi-compact and quasi-separated, let `X` be normal and assume that every
quasi-compact open of `X` has finitely many irreducible components. Then the normalization
`f.normalization` of `Y` in `X` is a disjoint union of integral normal schemes, and the dominant
morphism `f.toNormalization` induces a bijection on irreducible components.

## Main results

* `AlgebraicGeometry.isNormal_normalization`: the normalization of `Y` in `X` is normal.
* `AlgebraicGeometry.finite_irreducibleComponents_normalization`: its quasi-compact opens have
  finitely many irreducible components.
* `AlgebraicGeometry.exists_iso_sigma_normalization`: it is a disjoint union of integral normal
  schemes.
* `AlgebraicGeometry.bijOn_irreducibleComponents_toNormalization`: taking the closure of the
  image under `f.toNormalization` is a bijection from the irreducible components of `X` to those
  of the normalization.

## Implementation notes

Over an affine open `U` of `Y` the normalization is the spectrum of the integral closure `A'` of
`A = Γ(Y, U)` in `B = Γ(X, f⁻¹U)`. The preimage `f⁻¹U` is quasi-compact and normal, so it is a
coproduct of finitely many normal integral schemes, whence `B` is a finite product of normal
domains. The integral closure in a finite product is the product of the integral closures, and
the integral closure in a normal domain is a normal domain, so `A'` is a finite product of normal
domains and the normalization over `U` is a coproduct of finitely many normal integral schemes.
This yields a cover of the normalization by irreducible opens indexed by the same finite set that
indexes the decomposition of `f⁻¹U`.

The bijection on irreducible components is then purely topological. A scheme covered by pairwise
disjoint nonempty irreducible opens has those opens' closures as its irreducible components, so
the bijection is built from the local comparison of two such covers across the dominant map
`f.toNormalization`: the image of each member of the cover downstairs is contained in a unique
member upstairs, dominance makes this assignment surjective, and the index set is finite, so it is
a bijection whose members have the same closures.

## References

* [Stacks Project, Tag 035L](https://stacks.math.columbia.edu/tag/035L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### Integral elements of a product of finitely many algebras -/

section IntegralClosurePi

variable {A : Type*} [CommRing A] {ι : Type*} {B : ι → Type*} [∀ i, CommRing (B i)]
  [∀ i, Algebra A (B i)]

/-- Polynomial evaluation in a product of algebras is computed componentwise. -/
private theorem aeval_pi_apply (x : ∀ i, B i) (p : Polynomial A) (j : ι) :
    Polynomial.aeval x p j = Polynomial.aeval (x j) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial]

/-- An element of a product of finitely many algebras is integral as soon as each of its
components is: the product of monic polynomials annihilating the components annihilates it. -/
private theorem isIntegral_pi [Finite ι] {x : ∀ i, B i} (hx : ∀ i, IsIntegral A (x i)) :
    IsIntegral A x := by
  classical
  cases nonempty_fintype ι
  choose p hp hp0 using hx
  refine ⟨∏ i, p i, Polynomial.monic_prod_of_monic _ _ fun i _ ↦ hp i, ?_⟩
  rw [← Polynomial.aeval_def]
  funext j
  simp only [Pi.zero_apply, aeval_pi_apply, map_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  rw [Polynomial.aeval_def]
  exact hp0 j

/-- The integral closure of `A` in a product of finitely many `A`-algebras is the product of the
integral closures. -/
@[ega "II 6.3.6" "special case"]
private def integralClosurePiAlgEquiv [Finite ι] :
    integralClosure A (∀ i, B i) ≃ₐ[A] ∀ i, integralClosure A (B i) := by
  refine AlgEquiv.ofBijective
    (AlgHom.pi fun i ↦ ((Pi.evalAlgHom A B i).comp
      (integralClosure A (∀ i, B i)).val).codRestrict _ fun x ↦ ?_) ⟨?_, ?_⟩
  · exact (mem_integralClosure_iff _ _).2
      (((mem_integralClosure_iff _ _).1 x.2).map (Pi.evalAlgHom A B i))
  · intro x y h
    exact Subtype.ext (funext fun i ↦
      congrArg (fun z : ∀ i, integralClosure A (B i) ↦ (z i : B i)) h)
  · intro y
    refine ⟨⟨fun i ↦ (y i : B i),
      isIntegral_pi fun i ↦ (mem_integralClosure_iff _ _).1 (y i).2⟩, ?_⟩
    exact funext fun i ↦ Subtype.ext rfl

end IntegralClosurePi

/-! ### Covers by pairwise disjoint irreducible opens -/

section IrredCover

variable {T : Type*} [TopologicalSpace T]

/-- A family of pairwise disjoint nonempty irreducible open sets whose union is `W`. -/
private structure IrredCover {ι : Type*} (R : ι → Set T) (W : Set T) : Prop where
  /-- Each member is open. -/
  isOpen : ∀ i, IsOpen (R i)
  /-- Each member is irreducible, in particular nonempty. -/
  isIrreducible : ∀ i, IsIrreducible (R i)
  /-- Distinct members are disjoint. -/
  disjoint : Pairwise (Function.onFun Disjoint R)
  /-- The members cover `W`. -/
  iUnion_eq : ⋃ i, R i = W

/-- A nonempty preconnected subset of a set covered by pairwise disjoint open sets is contained
in a single member of the cover. -/
private theorem exists_subset_of_isPreconnected {ι : Type*} {R : ι → Set T} {W : Set T}
    (hopen : ∀ i, IsOpen (R i)) (hdisj : Pairwise (Function.onFun Disjoint R))
    (hcover : W ⊆ ⋃ i, R i) {S : Set T} (hS : IsPreconnected S) (hSW : S ⊆ W)
    (hSne : S.Nonempty) : ∃ i, S ⊆ R i := by
  obtain ⟨s, hs⟩ := hSne
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcover (hSW hs))
  have hdv : Disjoint (R i) (⋃ j ∈ {j | j ≠ i}, R j) := by
    refine Set.disjoint_left.2 fun x hxi hx ↦ ?_
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 hx
    exact Set.disjoint_left.1 (hdisj hj) hxj hxi
  have hsub : S ⊆ R i ∪ ⋃ j ∈ {j | j ≠ i}, R j := by
    intro x hxS
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 (hcover (hSW hxS))
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hxj)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨j, hji, hxj⟩)
  exact ⟨i, IsPreconnected.subset_left_of_subset_union (hopen i)
    (isOpen_biUnion fun j _ ↦ hopen j) hdv hsub ⟨s, hs, hi⟩ hS⟩

/-- An irreducible component meeting a nonempty irreducible open set is the closure of that
open set. -/
private theorem eq_closure_of_mem_irreducibleComponents {Z R : Set T}
    (hZ : Z ∈ irreducibleComponents T) (hRo : IsOpen R) (hRi : IsIrreducible R)
    (h : (Z ∩ R).Nonempty) : Z = closure R := by
  obtain ⟨C, hC, hRC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible R hRi
  obtain ⟨r, hr⟩ := hRi.1
  obtain rfl : Z = C :=
    AlgebraicGeometry.component_eq_of_open_irreducible_nhd Z C hZ hC R hRo hRi h ⟨r, hRC hr, hr⟩
  refine Set.Subset.antisymm
    ((subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 hRo h).trans
      (closure_mono Set.inter_subset_right)) ?_
  exact (isClosed_of_mem_irreducibleComponents Z hZ).closure_subset_iff.2 hRC

/-- The closure of a nonempty irreducible open set is an irreducible component. -/
private theorem closure_mem_irreducibleComponents {R : Set T} (hRo : IsOpen R)
    (hRi : IsIrreducible R) : closure R ∈ irreducibleComponents T := by
  obtain ⟨C, hC, hRC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible R hRi
  obtain ⟨r, hr⟩ := hRi.1
  rwa [← eq_closure_of_mem_irreducibleComponents hC hRo hRi ⟨r, hRC hr, hr⟩]

/-- A point of `W` lying in an irreducible component `Z` lies in a member `R i` of a cover of `W`,
and then `Z` is the closure of `R i`. -/
private theorem IrredCover.exists_eq_closure {ι : Type*} {R : ι → Set T} {W : Set T}
    (hR : IrredCover R W) {Z : Set T} (hZ : Z ∈ irreducibleComponents T) {x : T} (hxZ : x ∈ Z)
    (hxW : x ∈ W) : ∃ i, x ∈ R i ∧ Z = closure (R i) := by
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 (hR.iUnion_eq.ge hxW)
  exact ⟨i, hxi, eq_closure_of_mem_irreducibleComponents hZ (hR.isOpen i) (hR.isIrreducible i)
    ⟨x, hxZ, hxi⟩⟩

/-- Distinct members of a family of pairwise disjoint nonempty irreducible open sets have
distinct closures. -/
private theorem injective_closure_of_disjoint {ι : Type*} {R : ι → Set T}
    (hopen : ∀ i, IsOpen (R i)) (hirr : ∀ i, IsIrreducible (R i))
    (hdisj : Pairwise (Function.onFun Disjoint R)) :
    Function.Injective fun i ↦ closure (R i) := by
  intro i j (h : closure (R i) = closure (R j))
  by_contra hij
  obtain ⟨ri, hri⟩ := (hirr i).1
  obtain ⟨rj, hrj⟩ := (hirr j).1
  obtain ⟨x, hx⟩ := (hirr i).closure.2 (R i) (R j) (hopen i) (hopen j)
    ⟨ri, subset_closure hri, hri⟩ ⟨rj, h ▸ subset_closure hrj, hrj⟩
  exact Set.disjoint_left.1 (hdisj hij) hx.2.1 hx.2.2

/-- Comparing two covers by pairwise disjoint irreducible opens across a dominant map: after
reindexing, the closure of the image of each member downstairs is the closure of the
corresponding member upstairs. -/
private theorem exists_perm_closure_image_eq {T₁ T₂ : Type*} [TopologicalSpace T₁]
    [TopologicalSpace T₂] {g : T₁ → T₂} (hg : Continuous g) {ι : Type*} [Finite ι]
    {R : ι → Set T₁} {S : ι → Set T₂} {W : Set T₁} {W' : Set T₂}
    (hR : IrredCover R W) (hS : IrredCover S W')
    (hgW : Set.MapsTo g W W') (hdense : W' ⊆ closure (g '' W)) :
    ∃ σ : Equiv.Perm ι, ∀ i, closure (g '' R i) = closure (S (σ i)) := by
  classical
  have hRW : ∀ i, R i ⊆ W := fun i ↦ hR.iUnion_eq.le.trans' (Set.subset_iUnion R i)
  have key : ∀ i, ∃ j, g '' R i ⊆ S j := fun i ↦
    exists_subset_of_isPreconnected hS.isOpen hS.disjoint hS.iUnion_eq.ge
      (((hR.isIrreducible i).2.image g hg.continuousOn).isPreconnected)
      (Set.image_subset_iff.2 fun x hx ↦ hgW (hRW i hx)) ((hR.isIrreducible i).1.image g)
  choose σ₀ hσ₀ using key
  have hsurj : Function.Surjective σ₀ := by
    intro j
    obtain ⟨r, hr⟩ := (hS.isIrreducible j).1
    obtain ⟨z, hzS, hzg⟩ :=
      mem_closure_iff.1 (hdense (hS.iUnion_eq.le (Set.mem_iUnion.2 ⟨j, hr⟩)))
        (S j) (hS.isOpen j) hr
    obtain ⟨x, hxW, rfl⟩ := hzg
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 (hR.iUnion_eq.ge hxW)
    refine ⟨i, ?_⟩
    by_contra hne
    exact Set.disjoint_left.1 (hS.disjoint hne) (hσ₀ i ⟨x, hxi, rfl⟩) hzS
  have hinj : Function.Injective σ₀ := Finite.injective_iff_surjective.2 hsurj
  refine ⟨Equiv.ofBijective σ₀ ⟨hinj, hsurj⟩, fun i ↦ ?_⟩
  refine Set.Subset.antisymm (closure_mono (hσ₀ i)) (closure_minimal ?_ isClosed_closure)
  intro x hx
  have hmem : x ∈ closure (g '' W) := hdense (hS.iUnion_eq.le (Set.mem_iUnion.2 ⟨σ₀ i, hx⟩))
  rw [← hR.iUnion_eq, Set.image_iUnion, closure_iUnion_of_finite] at hmem
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hmem
  obtain rfl : k = i := by
    by_contra hne
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 (closure_mono (hσ₀ k) hk)
      (S (σ₀ i)) (hS.isOpen _) hx
    exact Set.disjoint_left.1 (hS.disjoint fun h ↦ hne (hinj h).symm) hy1 hy2
  exact hk

/-- Taking the closure before pushing a set forward along a continuous map does not change the
closure of the image. -/
private theorem closure_image_closure_eq {T₁ T₂ : Type*} [TopologicalSpace T₁]
    [TopologicalSpace T₂] {g : T₁ → T₂} (hg : Continuous g) (A : Set T₁) :
    closure (g '' closure A) = closure (g '' A) :=
  Set.Subset.antisymm
    (closure_minimal (image_closure_subset_closure_image hg) isClosed_closure)
    (closure_mono (Set.image_mono subset_closure))

/-- A preirreducible subset of a space traces out a preirreducible subset of any open
subspace. -/
private theorem isPreirreducible_preimage_val {W A : Set T} (hWo : IsOpen W)
    (hA : IsPreirreducible A) : IsPreirreducible ((Subtype.val : W → T) ⁻¹' A) := by
  rintro u v hu hv ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.1 hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.1 hv
  obtain ⟨c, hc⟩ := hA (u' ∩ W) (v' ∩ W) (hu'.inter hWo) (hv'.inter hWo)
    ⟨a.1, ha.1, ha.2, a.2⟩ ⟨b.1, hb.1, hb.2, b.2⟩
  exact ⟨⟨c, hc.2.1.2⟩, hc.1, hc.2.1.1, hc.2.2.1⟩

/-- A space in which every point has an irreducible open neighbourhood has finitely many
irreducible components on every quasi-compact open subset. -/
private theorem finite_irreducibleComponents_of_locally_irreducible
    (hloc : ∀ z : T, ∃ N : Set T, IsOpen N ∧ z ∈ N ∧ IsIrreducible N) {W : Set T}
    (hWo : IsOpen W) (hW : IsCompact W) : (irreducibleComponents W).Finite := by
  classical
  choose N hNo hzN hNi using hloc
  have : CompactSpace W := isCompact_iff_compactSpace.1 hW
  obtain ⟨s, hs⟩ := (isCompact_univ (X := W)).elim_finite_subcover
    (fun x : W ↦ (Subtype.val : W → T) ⁻¹' N x.1)
    (fun x ↦ (hNo x.1).preimage continuous_subtype_val)
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hzN x.1⟩)
  refine finite_irreducibleComponents_of_isPreirreducible_cover (s := (s : Set W))
    s.finite_toSet (fun x ↦ (hNo x.1).preimage continuous_subtype_val)
    (fun x ↦ isPreirreducible_preimage_val hWo (hNi x.1).2) fun x ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact ⟨y, hy, hxy⟩

end IrredCover

/-! ### Decomposing an open subscheme as a coproduct -/

namespace AlgebraicGeometry

/-- The images of the summands of a decomposition of an open subscheme as a coproduct of
irreducible schemes cover that open by pairwise disjoint irreducible opens. -/
private theorem exists_irredCover_of_iso_sigma {X : Scheme.{u}} (V : X.Opens) {ι : Type u}
    (Z : ι → Scheme.{u}) (hZ : ∀ i, IrreducibleSpace (Z i)) (e : V.toScheme ≅ ∐ Z) :
    ∃ R : ι → Set X, IrredCover R (V : Set X) := by
  let φ : (∐ Z : Scheme.{u}) ⟶ X := e.inv ≫ V.ι
  have hbase : ∀ i, IsIrreducible (Set.range (Sigma.ι Z i).base) := by
    intro i
    have := hZ i
    simpa using (IrreducibleSpace.isIrreducible_univ (Z i)).image _
      (Sigma.ι Z i).continuous.continuousOn
  refine ⟨fun i ↦ φ.base '' Set.range (Sigma.ι Z i).base, fun i ↦ ?_, fun i ↦ ?_, ?_, ?_⟩
  · exact φ.isOpenEmbedding.isOpenMap _ (Sigma.ι Z i).isOpenEmbedding.isOpen_range
  · exact (hbase i).image _ φ.continuous.continuousOn
  · intro i j hij
    refine Set.disjoint_image_of_injective φ.isOpenEmbedding.injective ?_
    exact Opens.coe_disjoint.2 (disjoint_opensRange_sigmaι Z i j hij)
  · have huniv : ⋃ i, Set.range (Sigma.ι Z i).base = (Set.univ : Set (∐ Z : Scheme.{u})) := by
      refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk Z).surjective x
      exact Set.mem_iUnion.2 ⟨i, z, (sigmaMk_mk Z i z).symm⟩
    rw [← Set.image_iUnion, huniv, Set.image_univ, ← V.range_ι]
    have hsurj : Function.Surjective e.inv.base := e.inv.homeomorph.surjective
    ext x
    simp only [Set.mem_range]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.inv.base z, (Scheme.Hom.comp_apply _ _ _).symm⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := hsurj w
      exact ⟨z, by rw [Scheme.Hom.comp_apply, hz]⟩

/-- A coproduct of nonempty schemes whose underlying space is quasi-compact has a finite index
type. -/
private theorem finite_of_compactSpace_sigma {ι : Type u} (Z : ι → Scheme.{u})
    [CompactSpace (∐ Z : Scheme.{u})] (hZ : ∀ i, Nonempty (Z i)) : Finite ι := by
  have : CompactSpace (Σ i, Z i) := (sigmaMk Z).symm.compactSpace
  obtain ⟨s, t, hs, -, heq⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (Σ i, Z i))).sigma_exists_finite_sigma_eq Set.univ
  refine Set.finite_univ_iff.mp (hs.subset fun i _ ↦ ?_)
  obtain ⟨z⟩ := hZ i
  exact (show (⟨i, z⟩ : Σ i, Z i) ∈ s.sigma t from heq.symm ▸ Set.mem_univ _).1

/-- The ring of global sections of a coproduct of finitely many schemes is the product of the
rings of global sections of the summands. -/
private theorem nonempty_ringEquiv_pi_of_iso_sigma {W : Scheme.{u}} {ι : Type u} [Finite ι]
    (Z : ι → Scheme.{u}) (e : W ≅ ∐ Z) : Nonempty (Γ(W, ⊤) ≃+* ∀ i, Γ(Z i, ⊤)) := by
  classical
  let hΓ : IsColimit (Cofan.mk (Scheme.Γ.rightOp.obj (∐ Z))
      (fun i ↦ Scheme.Γ.rightOp.map (Sigma.ι Z i))) :=
    isColimitCofanMkObjOfIsColimit Scheme.Γ.rightOp Z (Sigma.ι Z) (coproductIsCoproduct Z)
  let cPi : Cofan (fun i ↦ Scheme.Γ.rightOp.obj (Z i)) :=
    Cofan.mk (Opposite.op (CommRingCat.of (∀ i, Γ(Z i, ⊤))))
      (fun i ↦ show Scheme.Γ.rightOp.obj (Z i) ⟶
          Opposite.op (CommRingCat.of (∀ i, Γ(Z i, ⊤))) from
        (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦ Γ(Z i, ⊤)) i)).op)
  let hPi : IsColimit cPi := by
    refine Cofan.IsColimit.mk cPi (fun t ↦
      (CommRingCat.ofHom (RingHom.pi fun i ↦ (t.inj i).unop.hom)).op) ?_ ?_
    · intro t i
      apply Quiver.Hom.unop_inj
      ext x
      rfl
    · intro t m hm
      apply Quiver.Hom.unop_inj
      ext x
      funext i
      exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (congrArg Quiver.Hom.unop (hm i))) x
  exact ⟨((Scheme.Γ.mapIso e.op).symm ≪≫
    ((hΓ.coconePointUniqueUpToIso hPi).unop).symm).commRingCatIsoToRingEquiv⟩

/-- If a ring is, as an `A`-algebra, isomorphic to a product of finitely many normal domains,
then the integral closure of `A` in it is isomorphic to a product of finitely many normal
domains. -/
private theorem exists_ringEquiv_pi_integralClosure {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {ι : Type u} [Finite ι] (C : ι → Type u) [∀ i, CommRing (C i)]
    (hC : ∀ i, IsNormalDomain (C i)) (e : B ≃+* ∀ i, C i) :
    ∃ (D : ι → Type u) (_ : ∀ i, CommRing (D i)) (_ : ∀ i, IsNormalDomain (D i)),
      Nonempty (integralClosure A B ≃+* ∀ i, D i) := by
  let : ∀ i, Algebra A (C i) := fun i ↦
    ((Pi.evalRingHom C i).comp (e.toRingHom.comp (algebraMap A B))).toAlgebra
  exact ⟨fun i ↦ ↥(integralClosure A (C i)), fun i ↦ inferInstance,
    fun i ↦ integralClosure_isNormalDomain (hC i),
    ⟨((AlgEquiv.ofRingEquiv (f := e) fun _ ↦ funext fun _ ↦ rfl).mapIntegralClosure.trans
      integralClosurePiAlgEquiv).toRingEquiv⟩⟩

/-- Normality transports backwards along an isomorphism of schemes. -/
private theorem isNormal_of_iso_aux {W W' : Scheme.{u}} (e : W ≅ W') (h : IsNormal W') :
    IsNormal W :=
  isNormal_of_openCover
    (Scheme.coverOfIsIso.{u, u} (P := @IsOpenImmersion) e.inv) fun _ ↦ h

/-! ### The local structure of the relative normalization -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- Over an affine open `U` of `Y`, the preimage of `U` in `X` and the preimage of `U` in the
normalization of `Y` in `X` are both covered by pairwise disjoint irreducible opens indexed by
one finite set, and the latter preimage is normal. -/
private theorem exists_irredCover_pair [IsNormal X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : Y.affineOpens) :
    ∃ (ι : Type u) (_ : Finite ι) (R : ι → Set X) (S : ι → Set f.normalization),
      IrredCover R ((f ⁻¹ᵁ U.1 : X.Opens) : Set X) ∧
        IrredCover S ((f.fromNormalization ⁻¹ᵁ U.1 : f.normalization.Opens) :
          Set f.normalization) ∧
        IsNormal (f.fromNormalization ⁻¹ᵁ U.1).toScheme := by
  classical
  let : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  have hVc : IsCompact ((f ⁻¹ᵁ U.1 : X.Opens) : Set X) := f.isCompact_preimage U.2.isCompact
  have : Finite (irreducibleComponents (f ⁻¹ᵁ U.1).toScheme) := (hX _ hVc).to_subtype
  have hVfin : ∀ O : (f ⁻¹ᵁ U.1).toScheme.Opens,
      IsCompact ((O : (f ⁻¹ᵁ U.1).toScheme.Opens) : Set (f ⁻¹ᵁ U.1).toScheme) →
      (irreducibleComponents ((O : (f ⁻¹ᵁ U.1).toScheme.Opens) :
        Set (f ⁻¹ᵁ U.1).toScheme)).Finite := fun O _ ↦
    @Set.toFinite _ _ (finite_irreducibleComponents_opens (X := (f ⁻¹ᵁ U.1).toScheme) O)
  obtain ⟨ι, Z, hZn, hZi, ⟨eV⟩⟩ := (isNormal_iff_exists_iso_coproduct hVfin).mp inferInstance
  have hZirr : ∀ i, IrreducibleSpace (Z i) := fun i ↦ have := hZi i; inferInstance
  have : CompactSpace (f ⁻¹ᵁ U.1).toScheme := isCompact_iff_compactSpace.1 hVc
  have : CompactSpace (∐ Z : Scheme.{u}) := eV.hom.homeomorph.compactSpace
  have hιfin : Finite ι := finite_of_compactSpace_sigma Z fun i ↦ (hZirr i).toNonempty
  obtain ⟨R, hR⟩ := exists_irredCover_of_iso_sigma (f ⁻¹ᵁ U.1) Z hZirr eV
  obtain ⟨eB0⟩ := nonempty_ringEquiv_pi_of_iso_sigma Z eV
  have hCnormal : ∀ i, IsNormalDomain (Γ(Z i, ⊤) : Type u) := by
    intro i
    have := hZi i
    have := hZn i
    have : Nonempty (⊤ : (Z i).Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    have : IsDomain Γ(Z i, ⊤) := IsIntegral.component_integral ⊤
    exact ⟨inferInstance, normal_globalSections (Z i)⟩
  obtain ⟨D, hDring, hDnormal, ⟨eD⟩⟩ :=
    exists_ringEquiv_pi_integralClosure (A := Γ(Y, U.1)) (B := Γ(X, f ⁻¹ᵁ U.1))
      (fun i ↦ (Γ(Z i, ⊤) : Type u)) hCnormal
      ((((f ⁻¹ᵁ U.1).topIso).symm.commRingCatIsoToRingEquiv).trans eB0)
  let := hDring
  have hDdom : ∀ i, IsDomain (D i) := fun i ↦ (hDnormal i).isDomain
  have hDic : ∀ i, IsIntegrallyClosed (D i) := fun i ↦ (hDnormal i).isIntegrallyClosed
  let eU' : (f.fromNormalization ⁻¹ᵁ U.1).toScheme ≅ (∐ fun i ↦ Spec (CommRingCat.of (D i))) :=
    relativeNormalizationPreimageIso f U.1 U.2 ≪≫
      (Scheme.Spec.mapIso eD.toCommRingCatIso.op).symm ≪≫
      (asIso (sigmaSpec fun i ↦ CommRingCat.of (D i))).symm
  have hSpecIrr : ∀ i, IrreducibleSpace (Spec (CommRingCat.of (D i))) := by
    intro i
    have : AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of (D i))) := inferInstance
    infer_instance
  obtain ⟨S, hS⟩ := exists_irredCover_of_iso_sigma (f.fromNormalization ⁻¹ᵁ U.1) _ hSpecIrr eU'
  exact ⟨ι, hιfin, R, S, hR, hS, isNormal_of_iso_aux eU' (isNormal_sigma _ fun i ↦
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed (D i)))⟩

/-! ### Normality of the relative normalization -/

/-- The normalization of `Y` in `X` is normal when `X` is normal and its quasi-compact opens have
finitely many irreducible components. -/
theorem isNormal_normalization [IsNormal X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    IsNormal f.normalization := by
  have h : IsNormal f.normalization ↔
      ∃ (I : Type u) (W : I → f.normalization.Opens),
        IsOpenCover W ∧ ∀ i, IsNormal (W i).toScheme :=
    (isNormal_tfae _).out 1 4
  refine h.mpr ⟨Y.affineOpens, fun U ↦ f.fromNormalization ⁻¹ᵁ U.1, IsOpenCover.mk ?_, fun U ↦ ?_⟩
  · refine top_unique fun z _ ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f.fromNormalization z)) isOpen_univ
    exact Opens.mem_iSup.2 ⟨⟨V, hV⟩, hzV⟩
  · obtain ⟨ι, -, R, S, -, -, hn⟩ := exists_irredCover_pair f hX U
    exact hn

/-! ### Comparing the local covers across the morphism to the normalization -/

/-- A point of `X` lies over `V` exactly when its image in the normalization does. -/
private theorem toNormalization_mem_preimage_iff (V : Y.Opens) (x : X) :
    f.toNormalization.base x ∈ f.fromNormalization ⁻¹ᵁ V ↔ x ∈ f ⁻¹ᵁ V := by
  change f.fromNormalization (f.toNormalization x) ∈ V ↔ f.base x ∈ V
  rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization]

/-- Over an affine open `U` of `Y`, the two covers by pairwise disjoint irreducible opens can be
indexed so that the closure of the image of each member in `X` is the closure of the
corresponding member in the normalization. -/
private theorem exists_irredCover_pair_closure [IsNormal X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (U : Y.affineOpens) :
    ∃ (ι : Type u) (_ : Finite ι) (R : ι → Set X) (S : ι → Set f.normalization),
      IrredCover R ((f ⁻¹ᵁ U.1 : X.Opens) : Set X) ∧
        IrredCover S ((f.fromNormalization ⁻¹ᵁ U.1 : f.normalization.Opens) :
          Set f.normalization) ∧
        ∀ i, closure (f.toNormalization.base '' R i) = closure (S i) := by
  obtain ⟨ι, hι, R, S, hR, hS, -⟩ := exists_irredCover_pair f hX U
  have hmaps : Set.MapsTo f.toNormalization.base ((f ⁻¹ᵁ U.1 : X.Opens) : Set X)
      ((f.fromNormalization ⁻¹ᵁ U.1 : f.normalization.Opens) : Set f.normalization) := by
    exact fun x hx ↦ (toNormalization_mem_preimage_iff f U.1 x).2 hx
  have hdense : ((f.fromNormalization ⁻¹ᵁ U.1 : f.normalization.Opens) : Set f.normalization) ⊆
      closure (f.toNormalization.base '' ((f ⁻¹ᵁ U.1 : X.Opens) : Set X)) := by
    intro z hz
    refine mem_closure_iff.2 fun o ho hzo ↦ ?_
    obtain ⟨w, ⟨hwo, hwU⟩, x, rfl⟩ := f.toNormalization.denseRange.inter_open_nonempty
      (o ∩ ((f.fromNormalization ⁻¹ᵁ U.1 : f.normalization.Opens) : Set f.normalization))
      (ho.inter (f.fromNormalization ⁻¹ᵁ U.1).2) ⟨z, hzo, hz⟩
    refine ⟨f.toNormalization.base x, hwo, x, ?_, rfl⟩
    exact (toNormalization_mem_preimage_iff f U.1 x).1 hwU
  obtain ⟨σ, hσ⟩ := exists_perm_closure_image_eq f.toNormalization.continuous hR hS hmaps hdense
  exact ⟨ι, hι, R, fun i ↦ S (σ i), hR,
    ⟨fun i ↦ hS.isOpen _, fun i ↦ hS.isIrreducible _,
      fun i j hij ↦ hS.disjoint (σ.injective.ne hij),
      (σ.surjective.iUnion_comp S).trans hS.iUnion_eq⟩, hσ⟩

/-- The two matched covers by pairwise disjoint irreducible opens, over an affine open
neighbourhood of a given point of `Y`. -/
private theorem exists_irredCover_pair_at [IsNormal X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) (y : Y) :
    ∃ (V : Y.Opens) (_ : y ∈ V) (ι : Type u) (_ : Finite ι) (R : ι → Set X)
        (S : ι → Set f.normalization),
      IrredCover R ((f ⁻¹ᵁ V : X.Opens) : Set X) ∧
        IrredCover S ((f.fromNormalization ⁻¹ᵁ V : f.normalization.Opens) :
          Set f.normalization) ∧
        ∀ i, closure (f.toNormalization.base '' R i) = closure (S i) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact ⟨V, hyV, exists_irredCover_pair_closure f hX ⟨V, hV⟩⟩

/-- Every point of the normalization has an irreducible open neighbourhood. -/
private theorem exists_irreducible_nhds_normalization [IsNormal X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (z : f.normalization) :
    ∃ N : Set f.normalization, IsOpen N ∧ z ∈ N ∧ IsIrreducible N := by
  obtain ⟨V, hV, ι, -, R, S, -, hS, -⟩ :=
    exists_irredCover_pair_at f hX (f.fromNormalization z)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hS.iUnion_eq.ge hV)
  exact ⟨S i, hS.isOpen i, hi, hS.isIrreducible i⟩

/-- Every quasi-compact open of the normalization has finitely many irreducible components. -/
theorem finite_irreducibleComponents_normalization [IsNormal X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (W : f.normalization.Opens) (hW : IsCompact (W : Set f.normalization)) :
    (irreducibleComponents W).Finite :=
  finite_irreducibleComponents_of_locally_irreducible
    (exists_irreducible_nhds_normalization f hX) W.2 hW

/-- **Stacks Project, Tag 035L.** The normalization of `Y` in a normal scheme `X` whose
quasi-compact opens have finitely many irreducible components is a disjoint union of integral
normal schemes. -/
@[stacks 035L "disjoint union of integral normal schemes"]
theorem exists_iso_sigma_normalization [IsNormal X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    ∃ (ι : Type u) (Z : ι → Scheme.{u}) (_ : ∀ i, IsNormal (Z i))
        (_ : ∀ i, AlgebraicGeometry.IsIntegral (Z i)), Nonempty (f.normalization ≅ ∐ Z) :=
  (isNormal_iff_exists_iso_coproduct (finite_irreducibleComponents_normalization f hX)).mp
    (isNormal_normalization f hX)

/-! ### The bijection on irreducible components -/

/-- **Stacks Project, Tag 035L.** The dominant morphism from `X` to the normalization of `Y` in
`X` carries irreducible components to irreducible components bijectively. -/
@[stacks 035L "bijection on irreducible components"]
theorem bijOn_irreducibleComponents_toNormalization [IsNormal X]
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    Set.BijOn (fun C ↦ closure (f.toNormalization.base '' C))
      (irreducibleComponents X) (irreducibleComponents f.normalization) := by
  have hmaps : ∀ C ∈ irreducibleComponents X,
      closure (f.toNormalization.base '' C) ∈ irreducibleComponents f.normalization := by
    intro C hC
    obtain ⟨x, hxC⟩ := hC.1.1
    obtain ⟨V, hV, ι, -, R, S, hR, hS, hcl⟩ := exists_irredCover_pair_at f hX (f.base x)
    obtain ⟨i, -, hCeq⟩ := hR.exists_eq_closure hC hxC (show x ∈ _ from hV)
    rw [hCeq, closure_image_closure_eq f.toNormalization.continuous, hcl i]
    exact closure_mem_irreducibleComponents (hS.isOpen i) (hS.isIrreducible i)
  refine ⟨hmaps, ?_, ?_⟩
  · intro C hC C' hC' heq
    have heq' : closure (f.toNormalization.base '' C) = closure (f.toNormalization.base '' C') :=
      heq
    obtain ⟨z, hzD⟩ := (hmaps C hC).1.1
    obtain ⟨V, hV, ι, -, R, S, hR, hS, hcl⟩ :=
      exists_irredCover_pair_at f hX (f.fromNormalization.base z)
    obtain ⟨j, -, hDeq⟩ := hS.exists_eq_closure (hmaps C hC) hzD (show z ∈ _ from hV)
    have step : ∀ E ∈ irreducibleComponents X,
        closure (f.toNormalization.base '' E) = closure (S j) → E = closure (R j) := by
      intro E hE hEeq
      obtain ⟨s₀, hs₀⟩ := (hS.isIrreducible j).1
      obtain ⟨-, hwS, x, hxE, rfl⟩ :=
        mem_closure_iff.1 (hEeq ▸ subset_closure hs₀ : s₀ ∈ closure _) (S j) (hS.isOpen j) hs₀
      obtain ⟨i, -, hEeq'⟩ := hR.exists_eq_closure hE hxE
        ((toNormalization_mem_preimage_iff f V x).1 (hS.iUnion_eq.le (Set.mem_iUnion.2 ⟨j, hwS⟩)))
      have hij : i = j := by
        refine injective_closure_of_disjoint hS.isOpen hS.isIrreducible hS.disjoint ?_
        change closure (S i) = closure (S j)
        rw [← hcl i, ← closure_image_closure_eq f.toNormalization.continuous (R i), ← hEeq',
          hEeq]
      rw [hEeq', hij]
    rw [step C hC hDeq, step C' hC' (heq'.symm.trans hDeq)]
  · intro D hD
    obtain ⟨z, hzD⟩ := hD.1.1
    obtain ⟨V, hV, ι, -, R, S, hR, hS, hcl⟩ :=
      exists_irredCover_pair_at f hX (f.fromNormalization.base z)
    obtain ⟨i, -, hDeq⟩ := hS.exists_eq_closure hD hzD (show z ∈ _ from hV)
    refine ⟨closure (R i),
      closure_mem_irreducibleComponents (hR.isOpen i) (hR.isIrreducible i), ?_⟩
    change closure (f.toNormalization.base '' closure (R i)) = D
    rw [closure_image_closure_eq f.toNormalization.continuous, hcl i]
    exact hDeq.symm

end AlgebraicGeometry
