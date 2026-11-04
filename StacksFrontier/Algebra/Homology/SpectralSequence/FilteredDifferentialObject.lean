module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Subobject.FactorThru
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Subobject.Butterfly

/-!
# The spectral sequence of a filtered differential object

Filtered differential objects of an abelian category, the induced filtration on their
cohomology, weak convergence and abutment of the associated spectral sequence, and the
identification of the associated graded of the cohomology with a subquotient of the limit term.

## Main definitions

* `FilteredDifferentialObject`: an object with a decreasing filtration and a differential
  `d` with `d ≫ d = 0` respecting the filtration.
* `FilteredDifferentialObject.inducedFiltration`: the filtration
  `F^p H(K, d) = Im(H(F^p K, d) ⟶ H(K, d))` on the cohomology.
* `FilteredDifferentialObject.WeaklyConvergesTo`, `FilteredDifferentialObject.AbutsTo`: weak
  convergence and abutment of the associated spectral sequence.

## Main results

* `CategoryTheory.gr_homology_isSubquotient_stablePage`: in each degree `p`, the associated
  graded `gr^p H(K, d)` of the cohomology is a subquotient of the limit term `E_∞^p`.
-/

@[expose] public section

section

open CategoryTheory

variable (C : Type*) [Category C] [Abelian C]

/-- A *filtered object* `(X, F)` of an abelian category `C` consists of an
object `X : C` together with a decreasing filtration `F : ℤ → Subobject X`,
i.e. `F (p+1) ≤ F p` for every `p` (equivalently, `F` is antitone). -/
structure FilteredObjectForDifferential where
  /-- The underlying object. -/
  X : C
  /-- The filtration, a family of subobjects of `X` indexed by `ℤ`. -/
  F : ℤ → Subobject X
  /-- The filtration is decreasing. -/
  antitone' : Antitone F

variable {C}

/-- A morphism of underlying objects `d : A.X ⟶ A.X` *respects* the filtration
`A.F` if for every `p`, the composite `(A.F p).arrow ≫ d` factors through `A.F p`. -/
def FilteredObjectForDifferential.respects (A : FilteredObjectForDifferential C) (d : A.X ⟶ A.X) :
    Prop :=
  ∀ p : ℤ, (A.F p).Factors ((A.F p).arrow ≫ d)

variable (C)

/-- A *filtered differential object* `(K, F, d)` of an abelian category `A` is a filtered object
`(K, F)` of `A` endowed with an endomorphism `d : (K, F) → (K, F)` whose square is zero:
`d ∘ d = 0`. -/
@[stacks_fixed 012B]
structure FilteredDifferentialObject extends FilteredObjectForDifferential C where
  /-- The differential endomorphism on the underlying object. -/
  d : X ⟶ X
  /-- `d` respects the filtration. -/
  d_respects : toFilteredObjectForDifferential.respects d
  /-- The differential squares to zero. -/
  d_squared : d ≫ d = 0

namespace FilteredDifferentialObject

variable {C}

/-- The differential of a filtered differential object squares to zero. -/
theorem d_comp_d (K : FilteredDifferentialObject C) : K.d ≫ K.d = 0 :=
  K.d_squared

/-- The differential maps each step `F p` of the filtration into itself. -/
theorem d_respects_filtration (K : FilteredDifferentialObject C) (p : ℤ) :
    (K.F p).Factors ((K.F p).arrow ≫ K.d) :=
  K.d_respects p

/-- The filtration of a filtered differential object is decreasing. -/
theorem filtration_antitone (K : FilteredDifferentialObject C) : Antitone K.F :=
  K.antitone'

end FilteredDifferentialObject

end

section

/-!
## Induced filtration on the cohomology of a filtered differential object

For a filtered differential object `(K, F, d)` the *induced filtration* on the cohomology
`H(K, d)` is `F^p H(K, d) = Im(H(F^p K, d) → H(K, d))`, where `H(K, d)` is the homology of the
short complex `K --d--> K --d--> K` and `F^p K` carries the restriction of `d`.
-/

open CategoryTheory CategoryTheory.Limits

namespace FilteredDifferentialObject

variable {C : Type*} [Category C] [Abelian C] (X : FilteredDifferentialObject C)

/-- The restriction `d_p : F^p K ⟶ F^p K` of the differential. -/
noncomputable def dp (p : ℤ) : (X.F p : C) ⟶ (X.F p : C) :=
  (X.F p).factorThru ((X.F p).arrow ≫ X.d) (X.d_respects p)

/-- The restriction `d_p` commutes with the inclusion `F p K ↪ K`. -/
@[reassoc (attr := simp)]
lemma dp_comm (p : ℤ) : X.dp p ≫ (X.F p).arrow = (X.F p).arrow ≫ X.d :=
  Subobject.factorThru_arrow _ _ _

/-- The short complex `K --d--> K --d--> K` modelling `(K, d)`. Its homology is `H(K, d)`. -/
noncomputable abbrev shortComplex : ShortComplex C :=
  ShortComplex.mk X.d X.d X.d_squared

/-- The restricted differential `d_p` also squares to zero. -/
lemma dp_sq (p : ℤ) : X.dp p ≫ X.dp p = 0 := by
  rw [← cancel_mono (X.F p).arrow, zero_comp, Category.assoc, X.dp_comm,
    X.dp_comm_assoc, X.d_squared, comp_zero]

/-- The short complex `F p K --d_p--> F p K --d_p--> F p K` modelling `(F p K, d)`. -/
noncomputable abbrev shortComplexF (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (X.dp p) (X.dp p) (X.dp_sq p)

/-- The morphism of short complexes induced by `F p K ↪ K`. -/
@[simps]
noncomputable def shortComplexFHom (p : ℤ) : X.shortComplexF p ⟶ X.shortComplex where
  τ₁ := (X.F p).arrow
  τ₂ := (X.F p).arrow
  τ₃ := (X.F p).arrow
  comm₁₂ := (X.dp_comm p).symm
  comm₂₃ := (X.dp_comm p).symm

/-- The cohomology `H(K, d)`. -/
noncomputable abbrev homology : C := X.shortComplex.homology

/-- The cohomology `H(F^p K, d)`. -/
noncomputable abbrev homologyF (p : ℤ) : C := (X.shortComplexF p).homology

/-- The map `H(F^p K, d) ⟶ H(K, d)` induced by the inclusion `F p K ↪ K`. -/
noncomputable def homologyFMap (p : ℤ) : X.homologyF p ⟶ X.homology :=
  ShortComplex.homologyMap (X.shortComplexFHom p)

/-- The `p`-th step of the induced filtration on `H(K, d)` is
`F^p H(K, d) := Im (H(F^p K, d) ⟶ H(K, d))`. -/
@[stacks 012E]
noncomputable def inducedFiltration (p : ℤ) : Subobject X.homology :=
  imageSubobject (X.homologyFMap p)

/-- The inclusion `F^q K ⊆ F^p K`, `p ≤ q`, as a morphism of short complexes. -/
@[simps]
noncomputable def shortComplexFMap {p q : ℤ} (h : p ≤ q) :
    X.shortComplexF q ⟶ X.shortComplexF p where
  τ₁ := Subobject.ofLE _ _ (X.filtration_antitone h)
  τ₂ := Subobject.ofLE _ _ (X.filtration_antitone h)
  τ₃ := Subobject.ofLE _ _ (X.filtration_antitone h)
  comm₁₂ := by simp [← cancel_mono (X.F p).arrow]
  comm₂₃ := by simp [← cancel_mono (X.F p).arrow]

/-- The induced filtration on cohomology is decreasing. -/
theorem inducedFiltration_antitone : Antitone X.inducedFiltration := fun p q h ↦ by
  have e : X.homologyFMap q =
      ShortComplex.homologyMap (X.shortComplexFMap h) ≫ X.homologyFMap p := by
    rw [homologyFMap, homologyFMap, ← ShortComplex.homologyMap_comp]
    congr 1
    ext <;> simp
  simp only [inducedFiltration, e]
  exact imageSubobject_comp_le _ _

end FilteredDifferentialObject

end

section

/-!
## Weak convergence and abutment of spectral sequences

For a filtered differential object `(K, F, d)` in an abelian category, the associated spectral
sequence *weakly converges* to `H(K)` when the comparison `gr^p H(K) → E_∞^p` is an isomorphism for
every `p`, and *abuts* to `H(K)` when moreover the induced filtration on the cohomology is
separated and exhaustive.
-/

open CategoryTheory CategoryTheory.Limits

namespace FilteredDifferentialObject

variable {A : Type*} [Category A] [Abelian A]

/-- The inclusion `F^{p+1} H ⊆ F^p H` of the induced filtration. -/
noncomputable def inducedFiltrationInclusionSucc (X : FilteredDifferentialObject A) (p : ℤ) :
    (X.inducedFiltration (p + 1) : A) ⟶ (X.inducedFiltration p : A) :=
  Subobject.ofLE _ _ (X.inducedFiltration_antitone (by lia))

/-- The associated graded piece `gr^p H(K, d)` of the induced filtration. -/
noncomputable def grH (X : FilteredDifferentialObject A) (p : ℤ) : A :=
  cokernel (X.inducedFiltrationInclusionSucc p)

/-- The associated spectral sequence data. -/
structure AssociatedSpectralSequence (X : FilteredDifferentialObject A) where
  /-- The `E_∞` page. -/
  Einf : ℤ → A
  /-- The comparison morphism `gr^p H(X) ⟶ E_∞^p`. -/
  comparison : ∀ p : ℤ, X.grH p ⟶ Einf p

/-- The spectral sequence *weakly converges to `H(X)`* when the comparison
`gr^p H(X) ⟶ E_∞^p` is an isomorphism for every `p`. -/
@[stacks 012I "weakly_converges"]
def WeaklyConvergesTo (X : FilteredDifferentialObject A) (ss : AssociatedSpectralSequence X) :
    Prop :=
  ∀ p : ℤ, IsIso (ss.comparison p)

/-- The spectral sequence *abuts to `H(X)`* when it weakly converges and the induced filtration on
`H(X)` is separated and exhaustive: the only subobject contained in every `F^p H(X)` is `⊥`, and
the only one containing every `F^p H(X)` is `⊤`. -/
@[stacks 012I "abuts"]
def AbutsTo (X : FilteredDifferentialObject A) (ss : AssociatedSpectralSequence X) : Prop :=
  WeaklyConvergesTo X ss ∧
    (∀ Y : Subobject X.homology, (∀ p : ℤ, Y ≤ X.inducedFiltration p) → Y = ⊥) ∧
    (∀ Y : Subobject X.homology, (∀ p : ℤ, X.inducedFiltration p ≤ Y) → Y = ⊤)

/-- Abutment is a strengthening of weak convergence. -/
theorem abutsTo_weaklyConvergesTo (X : FilteredDifferentialObject A)
    (ss : AssociatedSpectralSequence X) (h : AbutsTo X ss) : WeaklyConvergesTo X ss :=
  h.1

end FilteredDifferentialObject

end


section

/-!
## The associated graded of the cohomology of a filtered differential object

Let `𝒜` be an abelian category and let `(K, F, d)` be a filtered differential object of `𝒜`: an
object `K`, a decreasing filtration `F : ℤ → Subobject K`, and a differential `d : K ⟶ K` with
`d ≫ d = 0` which preserves the filtration. Inside `gr^p K = F^p K / F^{p+1} K` the spectral
sequence associated to `(K, F, d)` has

* cycles `Z_r^p = (F^p K ⊓ d⁻¹(F^{p+r} K) ⊔ F^{p+1} K) / F^{p+1} K`,
* boundaries `B_r^p = (F^p K ⊓ d(F^{p-r+1} K) ⊔ F^{p+1} K) / F^{p+1} K`,
* pages `E_r^p = Z_r^p / B_r^p`.

If the stable objects `Z_∞^p = ⋂_r Z_r^p` and `B_∞^p = ⋃_r B_r^p` exist, the limit term is
`E_∞^p = Z_∞^p / B_∞^p`, and the associated graded of the cohomology, for the induced filtration
`F^p H(K, d) = Im(H(F^p K, d) ⟶ H(K, d))`, is a subquotient of it: the two subobjects

`D = Im(d) ⊓ F^p K ⊔ F^{p+1} K  ≤  N = Ker(d) ⊓ F^p K ⊔ F^{p+1} K`

lie between `B_∞^p` and `Z_∞^p`, and the quotient `N / D` is `gr^p H(K, d)`, compatibly with the
two quotient maps out of `Ker(d) ⊓ F^p K`. Thus `gr^p H(K, d)` is the subquotient `(N/B_∞^p) /
(D/B_∞^p)` of `E_∞^p`, and it is `E_∞^p` itself exactly when the two inclusions are equalities,
which is the criterion for weak convergence.

## References

* [Stacks, Tag 012F](https://stacks.math.columbia.edu/tag/012F)
-/

universe v u

namespace CategoryTheory

open Limits Preadditive

section

variable {C : Type u} [Category.{v} C] [Abelian C]

section ShortComplex

/-- The cycles of a short complex, as a subobject of `S.X₂`, are the kernel of `S.g`. -/
private lemma mk_iCycles (S : ShortComplex C) [S.HasHomology] :
    Subobject.mk S.iCycles = kernelSubobject S.g :=
  Subobject.mk_eq_mk_of_comm _ _ S.cyclesIsoKernel (by simp)

variable {S : ShortComplex C} [S.HasHomology]

/-- The arrow of the pullback of `G` along `S.iCycles` lies in `G` when viewed in `S.X₂`. -/
private lemma factors_pullback_arrow_comp_iCycles {S : ShortComplex C} [S.HasHomology]
    (G : Subobject S.X₂) : G.Factors (((Subobject.pullback S.iCycles).obj G).arrow ≫ S.iCycles) :=
  (pullback_factors_iff _ _ _).1 (Subobject.factors_self _)

/-- Let `c` be a cycle of `S` lying in `G`, and suppose that in `S.X₂` it lies in
`Im(S.f) ⊓ G ⊔ G'`. Then the class of `c` in homology lies in the image of the cycles lying in
`G'`. -/
private lemma factors_imageSubobject_homologyπ_of_factors_sup {G G' : Subobject S.X₂} {T : C}
    (c : T ⟶ S.cycles) (hcG : G.Factors (c ≫ S.iCycles))
    (hc : (imageSubobject S.f ⊓ G ⊔ G').Factors (c ≫ S.iCycles)) :
    (imageSubobject (((Subobject.pullback S.iCycles).obj G').arrow ≫ S.homologyπ)).Factors
      (c ≫ S.homologyπ) := by
  have hmod : (imageSubobject S.f ⊔ kernelSubobject S.g ⊓ G').Factors (c ≫ S.iCycles) := by
    refine Subobject.factors_of_le _ ?_ ((Subobject.inf_factors _).2 ⟨(Subobject.inf_factors _).2
      ⟨kernelSubobject_factors _ _ (by rw [Category.assoc, S.iCycles_g, comp_zero]), hcG⟩, hc⟩)
    calc (kernelSubobject S.g ⊓ G) ⊓ (imageSubobject S.f ⊓ G ⊔ G')
        ≤ (imageSubobject S.f ⊔ G') ⊓ kernelSubobject S.g :=
          le_inf (inf_le_right.trans (sup_le_sup_right inf_le_left _))
            (inf_le_left.trans inf_le_left)
      _ ≤ imageSubobject S.f ⊔ G' ⊓ kernelSubobject S.g :=
          sup_inf_le_assoc_of_le _ (_root_.image_le_kernel _ _ S.zero)
      _ ≤ imageSubobject S.f ⊔ kernelSubobject S.g ⊓ G' :=
          sup_le_sup_left (le_inf inf_le_right inf_le_left) _
  obtain ⟨T', z, hz, β, γ, fac⟩ := Subobject.exists_refinement_of_factors_sup _ hmod
  have hγ0 : (kernelSubobject S.g ⊓ G').arrow ≫ S.g = 0 :=
    Subobject.arrow_comp_eq_zero_of_le_kernelSubobject inf_le_left
  set L := S.liftCycles (imageSubobject S.f).arrow (imageSubobject_arrow_comp_eq_zero S.zero)
  set M := S.liftCycles ((kernelSubobject S.g ⊓ G').arrow) hγ0
  have hboundary : L ≫ S.homologyπ = 0 := by
    rw [← cancel_epi (factorThruImageSubobject S.f), comp_zero, ← Category.assoc,
      show factorThruImageSubobject S.f ≫ L = S.toCycles from by
        rw [← cancel_mono S.iCycles, Category.assoc, S.liftCycles_i, imageSubobject_arrow_comp,
          S.toCycles_i],
      S.toCycles_comp_homologyπ]
  have hclass : z ≫ c ≫ S.homologyπ = γ ≫ M ≫ S.homologyπ := by
    rw [← Category.assoc, show z ≫ c = β ≫ L + γ ≫ M from by
      rw [← cancel_mono S.iCycles, add_comp, Category.assoc, Category.assoc, Category.assoc,
        S.liftCycles_i, S.liftCycles_i]
      exact fac, add_comp, Category.assoc, Category.assoc, hboundary, comp_zero, zero_add]
  have hfac : ((Subobject.pullback S.iCycles).obj G').Factors M := by
    rw [pullback_factors_iff, S.liftCycles_i]
    exact Subobject.factors_of_le _ inf_le_right (Subobject.factors_self _)
  rw [Subobject.imageSubobject_factors_iff]
  refine ⟨T', z, hz, γ ≫ ((Subobject.pullback S.iCycles).obj G').factorThru M hfac, ?_⟩
  rwa [Category.assoc, ← Category.assoc _ ((Subobject.pullback S.iCycles).obj G').arrow,
    Subobject.factorThru_arrow]

/-- Let `c` be a cycle of `S` lying in `G`, and suppose that the class of `c` in homology lies in
the image of the cycles lying in `G' ≤ G`. Then in `S.X₂` the cycle `c` lies in
`Im(S.f) ⊓ G ⊔ G'`. -/
private lemma factors_sup_of_factors_imageSubobject_homologyπ {G G' : Subobject S.X₂}
    (hG : G' ≤ G) {T : C} (c : T ⟶ S.cycles) (hcG : G.Factors (c ≫ S.iCycles))
    (hc : (imageSubobject (((Subobject.pullback S.iCycles).obj G').arrow ≫ S.homologyπ)).Factors
      (c ≫ S.homologyπ)) :
    (imageSubobject S.f ⊓ G ⊔ G').Factors (c ≫ S.iCycles) := by
  set P := (Subobject.pullback S.iCycles).obj G'
  obtain ⟨T', z, hz, x, fac⟩ := (Subobject.imageSubobject_factors_iff _ _).1 hc
  have hzero : (z ≫ c - x ≫ P.arrow) ≫ S.homologyπ = 0 := by
    rw [sub_comp, Category.assoc, Category.assoc, fac, sub_self]
  obtain ⟨T'', z', hz', ρ, fac'⟩ :=
    (Limits.CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
      S.homologyIsCokernel _).1 hzero
  have hG' := factors_pullback_arrow_comp_iCycles G'
  have hsplit : (z' ≫ z) ≫ c ≫ S.iCycles
      = (z' ≫ (z ≫ c - x ≫ P.arrow)) ≫ S.iCycles + (z' ≫ x) ≫ (P.arrow ≫ S.iCycles) := by
    simp only [comp_sub, sub_comp, Category.assoc, sub_add_cancel]
  have him : (imageSubobject S.f).Factors ((z' ≫ (z ≫ c - x ≫ P.arrow)) ≫ S.iCycles) := by
    rw [fac', Category.assoc, S.toCycles_i]
    exact imageSubobject_factors_comp_self _ ρ
  have hg : G.Factors ((z' ≫ (z ≫ c - x ≫ P.arrow)) ≫ S.iCycles) := by
    rw [eq_sub_of_add_eq hsplit.symm]
    exact Subobject.factors_sub _ _ (Subobject.factors_of_factors_right _ hcG)
      (Subobject.factors_of_factors_right _ (Subobject.factors_of_le _ hG hG'))
  refine Subobject.factors_of_epi_comp z _ (Subobject.factors_of_epi_comp z' _ ?_)
  rw [← Category.assoc, hsplit]
  exact Subobject.factors_add _ _
    (Subobject.sup_factors_of_factors_left ((Subobject.inf_factors _).2 ⟨him, hg⟩))
    (Subobject.sup_factors_of_factors_right (Subobject.factors_of_factors_right _ hG'))

end ShortComplex

end

/-- Let `(K, F, d)` be a filtered differential object of an abelian category, let
`p : ℤ`, and suppose the stable cycles `Z_∞^p` and boundaries `B_∞^p` in degree `p` exist, i.e.
that `Zinf` is the greatest lower bound of the numerators of the `Z_r^p` and `Binf` the least upper
bound of the numerators of the `B_r^p`. Then the numerators `D = Im(d) ⊓ F^p K ⊔ F^{p+1} K` and
`N = Ker(d) ⊓ F^p K ⊔ F^{p+1} K` satisfy `Binf ≤ D ≤ N ≤ Zinf`, and `N / D` is `gr^p H(K, d)`,
the graded piece of the cohomology for the induced filtration, by the isomorphism compatible with
the two quotient maps out of `Ker(d) ⊓ F^p K`. In particular the limit term `E_∞^p = Zinf / Binf`
is defined and has `gr^p H(K, d)` as a subquotient. -/
@[stacks 012F]
public theorem gr_homology_isSubquotient_stablePage {C : Type u} [Category.{v} C] [Abelian C]
    {K : C} {d : K ⟶ K} (hd : d ≫ d = 0) {F : ℤ → Subobject K} {p : ℤ} (hFp : F (p + 1) ≤ F p)
    {Zinf Binf : Subobject K}
    (hZinf : IsGLB (Set.range fun r : ℕ =>
      F p ⊓ (Subobject.pullback d).obj (F (p + (r : ℤ))) ⊔ F (p + 1)) Zinf)
    (hBinf : IsLUB (Set.range fun r : ℕ =>
      F p ⊓ imageSubobject ((F (p - (r : ℤ))).arrow ≫ d) ⊔ F (p + 1)) Binf)
    {D N : Subobject K} (hD : D = imageSubobject d ⊓ F p ⊔ F (p + 1))
    (hN : N = kernelSubobject d ⊓ F p ⊔ F (p + 1))
    (j : (D : C) ⟶ (N : C)) (hj : j ≫ N.arrow = D.arrow)
    {V W : Subobject (ShortComplex.mk d d hd).cycles}
    (hV : V = (Subobject.pullback (ShortComplex.mk d d hd).iCycles).obj (F p))
    (hW : W = (Subobject.pullback (ShortComplex.mk d d hd).iCycles).obj (F (p + 1)))
    {FH FH' : Subobject (ShortComplex.mk d d hd).homology}
    (hFH : FH = imageSubobject (V.arrow ≫ (ShortComplex.mk d d hd).homologyπ))
    (hFH' : FH' = imageSubobject (W.arrow ≫ (ShortComplex.mk d d hd).homologyπ))
    (ι : (FH' : C) ⟶ (FH : C)) (hι : ι ≫ FH.arrow = FH'.arrow)
    (a : (V : C) ⟶ (N : C)) (ha : a ≫ N.arrow = V.arrow ≫ (ShortComplex.mk d d hd).iCycles)
    (b : (V : C) ⟶ (FH : C))
    (hb : b ≫ FH.arrow = V.arrow ≫ (ShortComplex.mk d d hd).homologyπ) :
    Binf ≤ D ∧ D ≤ N ∧ N ≤ Zinf ∧
      ∃ e : cokernel j ≅ cokernel ι, a ≫ cokernel.π j ≫ e.hom = b ≫ cokernel.π ι := by
  refine ⟨hBinf.2 ?_, ?_, hZinf.2 ?_, ?_⟩
  · rintro X ⟨r, rfl⟩
    rw [hD]
    exact sup_le_sup_right
      (le_inf (inf_le_right.trans (imageSubobject_comp_le _ d)) inf_le_left) _
  · rw [hD, hN]
    exact sup_le_sup_right (inf_le_inf_right _ (_root_.image_le_kernel d d hd)) _
  · rintro X ⟨r, rfl⟩
    rw [hN]
    refine sup_le_sup_right (le_inf inf_le_right (Subobject.le_of_factors ?_)) _
    rw [pullback_factors_iff, Subobject.arrow_comp_eq_zero_of_le_kernelSubobject
      (inf_le_left : kernelSubobject d ⊓ F p ≤ _)]
    exact Subobject.factors_zero
  · have hVp : ∀ {T : C} (g : T ⟶ (V : C)),
        (F p).Factors ((g ≫ V.arrow) ≫ (ShortComplex.mk d d hd).iCycles) := by
      intro T g
      rw [Category.assoc]
      exact Subobject.factors_of_factors_right _
        (by rw [hV]; exact factors_pullback_arrow_comp_iCycles (S := ShortComplex.mk d d hd) _)
    have hVN : Subobject.mk (V.arrow ≫ (ShortComplex.mk d d hd).iCycles)
        = kernelSubobject d ⊓ F p := by
      rw [hV, Subobject.mk_pullback_arrow_comp, mk_iCycles]
    have : Mono (a ≫ N.arrow) := by rw [ha]; infer_instance
    have hNsup : N ≤ Subobject.mk (a ≫ N.arrow) ⊔ F (p + 1) := by
      simp only [ha]
      rw [hVN, hN]
    have hepia : Epi (a ≫ cokernel.π j) :=
      Subobject.epi_comp_cokernel_π j hj a hNsup (by rw [hD]; exact le_sup_right)
    have : Epi b := Subobject.epi_of_comp_arrow_eq hFH b hb
    refine Subobject.exists_iso_cokernel_of_factors_iff j hj ι hι a b ?_
    intro T g
    rw [ha, hb, hD, hFH', hW]
    simp only [← Category.assoc]
    exact ⟨factors_imageSubobject_homologyπ_of_factors_sup (S := ShortComplex.mk d d hd) _ (hVp g),
      factors_sup_of_factors_imageSubobject_homologyπ (S := ShortComplex.mk d d hd) hFp _ (hVp g)⟩

end CategoryTheory

end
