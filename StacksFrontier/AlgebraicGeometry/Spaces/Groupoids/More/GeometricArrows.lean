module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.RingTheory.Localization.FractionRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.RestrictionArrows
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Geometric representatives of points of a groupoid over a field

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces whose object space `U` is the
algebraic space represented by the spectrum of a field `k`. A point of the arrow space `R`
is an equivalence class of field-valued points, and such a representative gives two
embeddings `a, b : k →+* E` of `k` into its field of definition `E`, one through the source
and one through the target. In a large enough algebraically closed extension `k'` of `E`
the two embeddings become conjugate by an automorphism `τ` of `k'`, because two
algebraically closed extensions of `k` of the same large cardinality are `k`-isomorphic.
That automorphism is exactly the datum turning the representative into an arrow of the
restriction of the groupoid along `Spec k' ⟶ Spec k` whose source lift is the identity and
whose target lift is `τ`; both are then isomorphisms.

## Main results

* `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_max_lt`: an algebraically closed
  algebra whose cardinality exceeds both that of its base and `ℵ₀` has the cardinality of
  any of its transcendence bases.
* `IsAlgClosed.nonempty_algEquiv_of_cardinal_eq_of_max_lt`: two algebraically closed
  extensions of a base of equal cardinality, large compared with the base and `ℵ₀`, are
  isomorphic over the base.
* `IsAlgClosed.exists_conjugate_ringHom`: two embeddings of a field `k` into a field `E`
  become conjugate in an algebraically closed extension of `E` whose cardinality is
  bounded by `2 ^ c`, for any infinite `c` bounding `#k` and `#E`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.exists_isIso_source_target_over_isAlgClosed`:
  every point of the arrow space of a groupoid in algebraic spaces on the spectrum of a
  field acquires, after an algebraically closed field extension, a representative in the
  restricted groupoid whose source and target are automorphisms.

## Implementation notes

The cardinality bound `2 ^ c` in `IsAlgClosed.exists_conjugate_ringHom` is what makes the
geometric statement possible at all: the spectrum of the extending field has to remain an
object of the big fppf site, and the site's cutoff is a strong prelimit cardinal, so it
suffices to produce the extension inside `2 ^ c` for some `c` below the cutoff. The bound
is read off the construction, an algebraic closure of the fraction field of a polynomial
ring in `2 ^ c` variables.

A section of the algebraic space represented by a scheme of the site over a test object is
literally a morphism of the site, so the source and target of a field-valued point of the
arrow space are morphisms of spectra of fields and hence come from ring maps. The arrow of
the restriction is then assembled from the triple (source lift, arrow, target lift) by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv`, which also reads
the three structure morphisms back off the triple.

The hypothesis is an *equality* of the object space with the algebraic space of the field
spectrum, not an isomorphism, because that is how the situation of Stacks 06DY arises: the
object space is prescribed. The comparison `eqToHom` of that equality is transported across
the source and target by naturality.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 04LR](https://stacks.math.columbia.edu/tag/04LR)
* [Stacks Project, Tag 06E2](https://stacks.math.columbia.edu/tag/06E2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace IsAlgClosed

open Cardinal

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] [IsAlgClosed K]
variable {ι : Type u} (v : ι → K)

/-- An algebraically closed `R`-algebra whose cardinality exceeds both `#R` and `ℵ₀` has the
cardinality of any of its transcendence bases over `R`.

This complements `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'`, which
bounds `#R` by `ℵ₀` instead of bounding both by `#K`. -/
theorem cardinal_eq_cardinal_transcendence_basis_of_max_lt
    (hv : IsTranscendenceBasis R v) (hK : max #R ℵ₀ < #K) : #K = #ι := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R K)
  refine le_antisymm ?_ (Cardinal.mk_le_of_injective hv.1.injective)
  have hb := cardinal_le_max_transcendence_basis' v hv
  have hR : #R < #K := (le_max_left _ _).trans_lt hK
  have hn : ℵ₀ < #K := (le_max_right _ _).trans_lt hK
  rcases le_max_iff.mp hb with hb | hb
  · exact (le_max_iff.mp hb).resolve_left (not_le_of_gt hR)
  · exact absurd hb (not_le_of_gt hn)

/-- Two algebraically closed extensions of `R` of the same cardinality, large compared with
both `#R` and `ℵ₀`, are isomorphic as `R`-algebras: they are algebraic closures of purely
transcendental extensions of `R` on equipotent transcendence bases. -/
theorem nonempty_algEquiv_of_cardinal_eq_of_max_lt {R K L : Type u}
    [CommRing R] [Field K] [Field L] [Algebra R K] [Algebra R L]
    [FaithfulSMul R K] [FaithfulSMul R L] [IsAlgClosed K] [IsAlgClosed L]
    (hK : max #R ℵ₀ < #K) (hKL : #K = #L) : Nonempty (K ≃ₐ[R] L) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hc : #s = #t :=
    (cardinal_eq_cardinal_transcendence_basis_of_max_lt _ hs hK).symm.trans
      (hKL.trans (cardinal_eq_cardinal_transcendence_basis_of_max_lt _ ht (hKL ▸ hK)))
  let e : s ≃ t := Classical.choice (Cardinal.eq.mp hc)
  let f : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  let _ := isAlgClosure_of_transcendence_basis _ hs
  let _ := isAlgClosure_of_transcendence_basis _ ht
  let g := IsAlgClosure.equivOfEquiv K L f.toRingEquiv
  refine ⟨{ g with commutes' := fun x => ?_ }⟩
  show IsAlgClosure.equivOfEquiv K L f.toRingEquiv (algebraMap R K x) = algebraMap R L x
  simpa only [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply] using
    IsAlgClosure.equivOfEquiv_algebraMap K L f.toRingEquiv
      (algebraMap R (Algebra.adjoin R (Set.range ((↑) : s → K))) x)

/-- Every field admits an algebraically closed extension of cardinality larger than a
prescribed infinite cardinal `c` bounding it, but no larger than `2 ^ c`: adjoin `2 ^ c`
indeterminates, pass to the fraction field and take an algebraic closure. -/
private lemma exists_isAlgClosed_ringHom_lt_mk_le_two_pow (E : Type u) [Field E]
    (c : Cardinal.{u}) (hE : #E ≤ c) (hc : ℵ₀ ≤ c) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (_ : E →+* K),
      c < #K ∧ #K ≤ 2 ^ c := by
  let ι : Type u := ((2 : Cardinal.{u}) ^ c).out
  let P := MvPolynomial ι E
  let F := FractionRing P
  let K := AlgebraicClosure F
  let j : E →+* K := (algebraMap F K).comp ((algebraMap P F).comp MvPolynomial.C)
  have hci : c < #ι := by simpa [ι] using Cardinal.cantor c
  refine ⟨K, inferInstance, inferInstance, j, ?_, ?_⟩
  · have hinj : Function.Injective
        (fun x : ι => algebraMap F K (algebraMap P F (MvPolynomial.X x))) :=
      (algebraMap F K).injective.comp
        ((IsFractionRing.injective P F).comp MvPolynomial.X_injective)
    exact hci.trans_le (Cardinal.mk_le_of_injective hinj)
  · have hℵ : ℵ₀ ≤ #ι := hc.trans hci.le
    let _ : Algebra F K := AlgebraicClosure.instAlgebra F
    have hP : #P ≤ max (max #E #ι) ℵ₀ := MvPolynomial.cardinalMk_le_max
    calc #K ≤ max #F ℵ₀ := Algebra.IsAlgebraic.cardinalMk_le_max F K
      _ ≤ #ι := max_le ((Cardinal.mk_fractionRing P).trans_le
          (hP.trans (max_le (max_le (hE.trans hci.le) le_rfl) hℵ))) hℵ
      _ = 2 ^ c := Cardinal.mk_out _

/-- **Stacks 04LR.** Two embeddings `a, b` of a field `k` into a field `E` become conjugate
in an algebraically closed extension `K` of `E`: there are `j : E →+* K` and an automorphism
`τ` of `K` with `τ ∘ j ∘ a = j ∘ b`. The extension can be taken of cardinality at most
`2 ^ c` for any infinite cardinal `c` bounding both `#k` and `#E`. -/
theorem exists_conjugate_ringHom {k E : Type u} [Field k] [Field E] (a b : k →+* E)
    (c : Cardinal.{u}) (hk : #k ≤ c) (hE : #E ≤ c) (hc : ℵ₀ ≤ c) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (j : E →+* K) (τ : K ≃+* K),
      τ.toRingHom.comp (j.comp a) = j.comp b ∧ #K ≤ 2 ^ c := by
  obtain ⟨K, instK, instClosed, j, hbig, hle⟩ :=
    exists_isAlgClosed_ringHom_lt_mk_le_two_pow E c hE hc
  let L := ULift.{0} K
  let e : L ≃+* K := ULift.ringEquiv
  let _ : IsAlgClosed L := IsAlgClosed.of_ringEquiv K L e.symm
  let _ : Algebra k K := (j.comp a).toAlgebra
  let _ : Algebra k L := (e.symm.toRingHom.comp (j.comp b)).toAlgebra
  obtain ⟨f⟩ := nonempty_algEquiv_of_cardinal_eq_of_max_lt (R := k) (L := L)
    ((max_le hk hc).trans_lt hbig)
    (Cardinal.mk_congr e.toEquiv.symm)
  refine ⟨K, instK, instClosed, j, f.toRingEquiv.trans e, ?_, hle⟩
  ext x
  exact (congrArg e (f.commutes x)).trans (e.apply_symm_apply _)

end IsAlgClosed

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open Cardinal

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The comparison isomorphism of an equality of algebraic spaces is undone by the
comparison isomorphism of the symmetric equality. -/
private lemma eqToHom_symm_hom_app {F G : AlgebraicSpaces C S hS} (e : F = G)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : F.obj.obj T) :
    (eqToHom e.symm).hom.app T ((eqToHom e).hom.app T x) = x := by
  cases e
  rfl

/-- Transporting a structure morphism of a groupoid in algebraic spaces across an equality
of its object space with the algebraic space of a scheme `T` of the site turns a section of
the arrow space into a morphism to `T`, naturally: restricting the section along `l` and
then transporting is composing the transported section with `l`. -/
private lemma eqToHom_hom_app_map_op {T : BigFppfOver C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (objects_eq : G.objects = schemeSpace T) (f : G.arrows ⟶ G.objects)
    {P Q : BigFppfOver C S hS} (l : Q ⟶ P) (x : G.arrows.obj.obj (Opposite.op P)) :
    (eqToHom objects_eq).hom.app (Opposite.op Q)
        (f.hom.app (Opposite.op Q) (G.arrows.obj.map l.op x)) =
      l ≫ ((eqToHom objects_eq).hom.app (Opposite.op P)
        (f.hom.app (Opposite.op P) x) : P ⟶ T) := by
  have h₁ := congrArg (fun u => u x) (f.hom.naturality l.op)
  have h₂ := congrArg (fun u => u (f.hom.app (Opposite.op P) x))
    ((eqToHom objects_eq).hom.naturality l.op)
  exact (congrArg ((eqToHom objects_eq).hom.app (Opposite.op Q)) h₁).trans h₂

/-- The spectrum of a field of cardinality at most `2 ^ c`, for a cardinal `c` below the
cutoff of a big fppf site, is an object of that site: the cutoff is a strong prelimit. -/
private lemma contains_spec_of_mk_le_two_pow (C : BigFppfSite.{u}) {k : Type u} [Field k]
    {c : Cardinal.{u}} (hc : c < C.cutoff) (hk : #k ≤ 2 ^ c) :
    C.Contains (Spec (CommRingCat.of k)) := by
  show (Spec (CommRingCat.of k)).size < C.cutoff
  rw [Scheme.size_Spec]
  exact max_lt C.aleph0_lt_cutoff (hk.trans_lt (C.cutoff_isStrongPrelimit hc))

/-- The cardinality of a field whose spectrum is an object of a big fppf site is below the
site's cutoff. -/
private lemma mk_lt_cutoff_of_contains_spec (C : BigFppfSite.{u}) {k : Type u} [Field k]
    (hk : C.Contains (Spec (CommRingCat.of k))) : #k < C.cutoff := by
  have h : (Spec (CommRingCat.of k)).size < C.cutoff := hk
  rw [Scheme.size_Spec] at h
  exact (le_max_right _ _).trans_lt h

/-- Two embeddings `a, b` of a field `k` into a field `E`, both of whose spectra are objects of
a big fppf site, become conjugate in an algebraically closed extension of `E` whose spectrum
is again an object of the site. -/
private lemma exists_conjugate_ringHom_of_contains_spec (C : BigFppfSite.{u}) {k E : Type u}
    [Field k] [Field E] (hk : C.Contains (Spec (CommRingCat.of k)))
    (hE : C.Contains (Spec (CommRingCat.of E))) (a b : k →+* E) :
    ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (j : E →+* K) (τ : K ≃+* K),
      τ.toRingHom.comp (j.comp a) = j.comp b ∧ C.Contains (Spec (CommRingCat.of K)) := by
  obtain ⟨K, instK, instClosed, j, τ, hτ, hcard⟩ :=
    IsAlgClosed.exists_conjugate_ringHom a b (max (max #k #E) ℵ₀)
      ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _)
  exact ⟨K, instK, instClosed, j, τ, hτ, contains_spec_of_mk_le_two_pow C
    (max_lt (max_lt (mk_lt_cutoff_of_contains_spec C hk) (mk_lt_cutoff_of_contains_spec C hE))
      C.aleph0_lt_cutoff) hcard⟩

/-- A morphism of a big fppf site between spectra of fields is the spectrum of a ring map. -/
private lemma exists_ringHom_spec_map_eq {k E : Type u} [Field k] [Field E]
    {hk : C.Contains (Spec (CommRingCat.of k))} {hE : C.Contains (Spec (CommRingCat.of E))}
    (m : C.obj hE ⟶ C.obj hk) :
    ∃ a : k →+* E, Scheme.Spec.map (CommRingCat.ofHom a).op = C.inclusion.map m :=
  ⟨(Scheme.Spec.preimage (C.inclusion.map m)).unop.hom, Scheme.Spec.map_preimage _⟩

/-- In a big fppf site, composing the spectrum of `j` with a morphism which is the spectrum of
`a` gives the spectrum of `j ∘ a`. -/
private lemma spec_map_comp_eq {k E K : Type u} [Field k] [Field E] [Field K]
    {hk : C.Contains (Spec (CommRingCat.of k))} {hE : C.Contains (Spec (CommRingCat.of E))}
    {hK : C.Contains (Spec (CommRingCat.of K))} (a : k →+* E) (j : E →+* K)
    (m : C.obj hE ⟶ C.obj hk) (hm : Scheme.Spec.map (CommRingCat.ofHom a).op = C.inclusion.map m) :
    (⟨Scheme.Spec.map (CommRingCat.ofHom j).op⟩ : C.obj hK ⟶ C.obj hE) ≫ m =
      ⟨Scheme.Spec.map (CommRingCat.ofHom (j.comp a)).op⟩ := by
  apply C.inclusion.map_injective
  show Scheme.Spec.map (CommRingCat.ofHom j).op ≫ C.inclusion.map m =
    Scheme.Spec.map (CommRingCat.ofHom (j.comp a)).op
  rw [← hm, ← Scheme.Spec.map_comp]
  rfl

/-- The spectrum of a ring automorphism of a field `k`, as an endomorphism of an object of the
big fppf site over `S` with underlying scheme `Spec k`, is an isomorphism. -/
private lemma isIso_overHomMk_spec_ringEquiv {k : Type u} [Field k]
    {hk : C.Contains (Spec (CommRingCat.of k))} (τ : k ≃+* k) {X : C.obj hk ⟶ C.obj hS}
    (w : (⟨Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op⟩ : C.obj hk ⟶ C.obj hk) ≫ X = X) :
    IsIso (Over.homMk (U := Over.mk X) (V := Over.mk X)
      ⟨Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op⟩ w) := by
  let z0 : C.obj hk ⟶ C.obj hk := ⟨Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op⟩
  have : IsIso (C.inclusion.map z0) := by
    show IsIso (Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op)
    have : IsIso (CommRingCat.ofHom τ.toRingHom) := τ.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsIso z0 :=
    (Functor.FullyFaithful.ofFullyFaithful C.inclusion).isIso_of_isIso_map z0
  have : IsIso ((Over.forget (C.obj hS)).map
      (Over.homMk (U := Over.mk X) (V := Over.mk X) z0 w)) := by
    rw [Over.forget_map]
    show IsIso z0
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget (C.obj hS))

/-- An arrow of `G` together with lifts along `g` of its source and target is the image of an
arrow of the restriction of `G` along `g` with those lifts as its source and target. -/
private lemma exists_restrictionArrows_of_lifts (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) {T : (BigFppfOver C S hS)ᵒᵖ}
    (s : U'.obj.obj T) (x : G.arrows.obj.obj T) (t : U'.obj.obj T)
    (ht : g.hom.app T t = G.target.hom.app T x) (hs : G.source.hom.app T x = g.hom.app T s) :
    ∃ r : (restrictionArrows G g).obj.obj T,
      (restrictionSource G g).hom.app T r = s ∧ (restrictionTarget G g).hom.app T r = t ∧
        (restrictionArrowsToArrows G g).hom.app T r = x := by
  refine ⟨(restrictionArrowDataEquiv G g T).symm ⟨s, x, t, ht, hs⟩, ?_, ?_, ?_⟩ <;>
    simp [← restrictionArrowDataEquiv_source, ← restrictionArrowDataEquiv_target,
      ← restrictionArrowDataEquiv_arrow]

/-- Let `x` be an arrow of `G` over `P` and `l : T' ⟶ P`. If the source and target of `x`,
transported to morphisms `P ⟶ T` and composed with `l`, are `d` and `z ≫ d`, then the pullback
of `x` along `l` is the image of an arrow of the restriction of `G` along `d` with source lift
`𝟙 T'` and target lift `z`. -/
private lemma exists_restrictionArrows_of_comp_eq {T T' P : BigFppfOver C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) (objects_eq : G.objects = schemeSpace T)
    (d : T' ⟶ T) (l : T' ⟶ P) (z : T' ⟶ T') (x : G.arrows.obj.obj (Opposite.op P))
    (hs : l ≫ ((eqToHom objects_eq).hom.app (Opposite.op P)
      (G.source.hom.app (Opposite.op P) x) : P ⟶ T) = d)
    (ht : l ≫ ((eqToHom objects_eq).hom.app (Opposite.op P)
      (G.target.hom.app (Opposite.op P) x) : P ⟶ T) = z ≫ d) :
    ∃ r : (restrictionArrows G (schemeSpaceMap d ≫ eqToHom objects_eq.symm)).obj.obj
        (Opposite.op T'),
      (restrictionSource G (schemeSpaceMap d ≫ eqToHom objects_eq.symm)).hom.app
          (Opposite.op T') r = 𝟙 T' ∧
        (restrictionTarget G (schemeSpaceMap d ≫ eqToHom objects_eq.symm)).hom.app
          (Opposite.op T') r = z ∧
        (restrictionArrowsToArrows G (schemeSpaceMap d ≫ eqToHom objects_eq.symm)).hom.app
          (Opposite.op T') r = G.arrows.obj.map l.op x := by
  have hgApp : ∀ w : T' ⟶ T',
      (schemeSpaceMap d ≫ eqToHom objects_eq.symm).hom.app (Opposite.op T') w =
        (eqToHom objects_eq.symm).hom.app (Opposite.op T') (w ≫ d) := fun _ => rfl
  exact exists_restrictionArrows_of_lifts G (schemeSpaceMap d ≫ eqToHom objects_eq.symm)
    (T := Opposite.op T') (𝟙 T') (G.arrows.obj.map l.op x) z
    (by rw [hgApp, ← ht, ← eqToHom_hom_app_map_op G objects_eq G.target l x,
      eqToHom_symm_hom_app])
    (by rw [hgApp, Category.id_comp, ← hs, ← eqToHom_hom_app_map_op G objects_eq G.source l x,
      eqToHom_symm_hom_app])

/-- **Stacks 06E2.** Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B` whose
object space `U` is the algebraic space represented by the spectrum of a field `k`. Every
point `r` of the arrow space `R` has, after an algebraically closed field extension `k'/k`,
a representative `r'` in the arrow space of the restriction `(U', R', s', t', c')` of the
groupoid along `Spec k' ⟶ Spec k`: it maps to `r` in the points of `R`, and both its source
`s' ∘ r'` and its target `t' ∘ r'` are automorphisms of `Spec k'`. -/
@[stacks 06E2]
theorem exists_isIso_source_target_over_isAlgClosed {k : Type u} [Field k]
    (C : BigFppfSite.{u}) {S : Scheme.{u}} (hS : C.Contains S)
    (structureMap : Spec (CommRingCat.of k) ⟶ S)
    (hk : C.Contains (Spec (CommRingCat.of k))) (B : AlgebraicSpaces C S hS)
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (objects_eq : G.objects = schemeSpace
      (Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)))
    (r : Space.points C S hS G.arrows.obj) :
    ∃ (k' : Type u) (field' : Field k') (_ : IsAlgClosed k')
      (i : k →+* k') (hk' : C.Contains (Spec (CommRingCat.of k'))),
      let T : BigFppfOver C S hS :=
        Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)
      let T' : BigFppfOver C S hS :=
        Over.mk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap⟩ :
          C.obj hk' ⟶ C.obj hS)
      let g : schemeSpace T' ⟶ G.objects :=
        schemeSpaceMap
          (Over.homMk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op⟩ :
            C.obj hk' ⟶ C.obj hk) rfl : T' ⟶ T) ≫
          eqToHom objects_eq.symm
      ∃ r' : (restrictionArrows G g).obj.obj (Opposite.op T'),
        let p : Space.FieldValuedPoint C S hS G.arrows.obj :=
          { carrier := k'
            field := field'
            contained := hk'
            toBase := Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap
            value := (restrictionArrowsToArrows G g).hom.app (Opposite.op T') r' }
        let sourceEnd : T' ⟶ T' := (restrictionSource G g).hom.app (Opposite.op T') r'
        let targetEnd : T' ⟶ T' := (restrictionTarget G g).hom.app (Opposite.op T') r'
        p.class C S hS G.arrows.obj = r ∧ IsIso sourceEnd ∧ IsIso targetEnd := by
  classical
  obtain ⟨p, rfl⟩ := Quot.exists_rep r
  let T : BigFppfOver C S hS := Over.mk (⟨structureMap⟩ : C.obj hk ⟶ C.obj hS)
  let P : BigFppfOver C S hS := p.siteObject C S hS G.arrows.obj
  let sourceMap : P ⟶ T := (eqToHom objects_eq).hom.app (Opposite.op P)
    (G.source.hom.app (Opposite.op P) p.value)
  let targetMap : P ⟶ T := (eqToHom objects_eq).hom.app (Opposite.op P)
    (G.target.hom.app (Opposite.op P) p.value)
  obtain ⟨a, ha⟩ := exists_ringHom_spec_map_eq (hE := p.contained) sourceMap.left
  obtain ⟨b, hb⟩ := exists_ringHom_spec_map_eq (hE := p.contained) targetMap.left
  obtain ⟨k', field', alg', j, τ, hτ, hk'⟩ :=
    exists_conjugate_ringHom_of_contains_spec C hk p.contained a b
  let i : k →+* k' := j.comp a
  let T' : BigFppfOver C S hS :=
    Over.mk (⟨Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap⟩ :
      C.obj hk' ⟶ C.obj hS)
  let d0 : C.obj hk' ⟶ C.obj hk := ⟨Scheme.Spec.map (CommRingCat.ofHom i).op⟩
  let d : T' ⟶ T := Over.homMk d0 rfl
  let l0 : C.obj hk' ⟶ C.obj p.contained := ⟨Scheme.Spec.map (CommRingCat.ofHom j).op⟩
  let z0 : C.obj hk' ⟶ C.obj hk' :=
    ⟨Scheme.Spec.map (CommRingCat.ofHom τ.toRingHom).op⟩
  have hSourceComp : l0 ≫ sourceMap.left = d0 :=
    spec_map_comp_eq (hE := p.contained) a j sourceMap.left ha
  have hTargetComp : l0 ≫ targetMap.left = z0 ≫ d0 :=
    (spec_map_comp_eq (hE := p.contained) b j targetMap.left hb).trans
      ((congrArg (fun w : k →+* k' =>
        (⟨Scheme.Spec.map (CommRingCat.ofHom w).op⟩ : C.obj hk' ⟶ C.obj hk)) hτ.symm).trans
        (spec_map_comp_eq i τ.toRingHom d0 rfl).symm)
  have hlw : l0 ≫ P.hom = T'.hom := by
    rw [← Over.w sourceMap, ← Category.assoc, hSourceComp]
    rfl
  have hzOver : z0 ≫ T'.hom = T'.hom := by
    show z0 ≫ d0 ≫ T.hom = T'.hom
    rw [← Category.assoc, ← hTargetComp, Category.assoc, Over.w targetMap, hlw]
  let l : T' ⟶ P := Over.homMk l0 hlw
  let z : T' ⟶ T' := Over.homMk z0 hzOver
  have : IsIso z := isIso_overHomMk_spec_ringEquiv τ hzOver
  obtain ⟨r', hSourceEnd, hTargetEnd, hArrowValue⟩ :=
    exists_restrictionArrows_of_comp_eq G objects_eq d l z p.value
      (Over.OverMorphism.ext hSourceComp) (Over.OverMorphism.ext hTargetComp)
  refine ⟨k', field', alg', i, hk', r', ?_, ?_, ?_⟩
  · exact Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension C S hS G.arrows.obj
      ⟨_, Space.FieldValuedPoint.dominates_refl C S hS G.arrows.obj _, ⟨l, hArrowValue.symm⟩⟩
  · rw [hSourceEnd]
    infer_instance
  · rw [hTargetEnd]
    infer_instance

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
