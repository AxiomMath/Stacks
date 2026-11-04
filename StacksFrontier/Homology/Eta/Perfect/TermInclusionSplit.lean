module

public import StacksFrontier.Homology.Eta.Perfect.LocallyFree

/-!
# The graph inclusion of a décalage term, for a complex isomorphic to a matrix complex

Let `A` be a commutative ring, `f ∈ A` a nonzerodivisor and `K^•` a complex of `A`-modules. The
degree-`n` term of the décalage `η_f K^•` sits inside `f^n K^n × f^{n+1} K^{n+1}` by the graph
inclusion `x ↦ (x, d x)`. If `K^•` is isomorphic to a bounded complex `C^•` of finite free modules
whose determinantal ideal `I_n(C^•, f)` is principal, then the term is finite projective of rank
`rank Cⁿ` and the graph inclusion has a linear retraction.

## Main definitions

* `EtaComplex.termInclusion`: the graph inclusion `x ↦ (x, d x)`.

## Main results

* `EtaComplex.finite_projective_rankAtStalk_term_of_iso`: the term is finite projective of the
  expected rank.
* `EtaComplex.exists_retraction_termInclusion_of_iso`: the graph inclusion has a retraction.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace EtaComplex

universe u

variable {A : Type u} [CommRing A]

/-- **The graph inclusion of a décalage term**: `x ↦ (x, d x)`, from the degree-`n` term of
`η_f K^•` into `f^n K^n × f^{n+1} K^{n+1}`. -/
def termInclusion (f : A) (K : Complex.{u, u} A) (n : ℤ) :
    term f K n →ₗ[A] EtaPow.fpowSub f (K.X n) n × EtaPow.fpowSub f (K.X (n + 1)) (n + 1) :=
  LinearMap.prod
    (LinearMap.codRestrict _ (term f K n).subtype (fun x => x.2.1))
    (LinearMap.codRestrict _ ((EtaPow.fLoc f (K.d n (n + 1)).hom).comp (term f K n).subtype)
      (fun x => x.2.2))

/-- The localization of a map, restricted to the power submodules. -/
def fpowSubMap (f : A) {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (g : M →ₗ[A] N) (n : ℤ) :
    EtaPow.fpowSub f M n →ₗ[A] EtaPow.fpowSub f N n :=
  ((EtaPow.fLoc f g).domRestrict _).codRestrict _ (fun x => localizedMap_mem_power f g n x.2)

/-- The term inclusion is natural: it intertwines the map of décalage terms induced by
`e : K ⟶ L` with the product of the induced maps on power submodules. -/
theorem termInclusion_naturality (f : A) {K L : Complex.{u, u} A} (e : K ⟶ L) (n : ℤ)
    (x : term f K n) :
    termInclusion f L n (etaMapLinear f e n x) =
      ((fpowSubMap f (e.f n).hom n).prodMap (fpowSubMap f (e.f (n + 1)).hom (n + 1)))
        (termInclusion f K n x) := by
  have comm' : (L.d n (n + 1)).hom ∘ₗ (e.f n).hom = (e.f (n + 1)).hom ∘ₗ (K.d n (n + 1)).hom := by
    ext y
    simpa only [ModuleCat.hom_comp] using ConcreteCategory.congr_hom (e.comm n (n + 1)) y
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · rfl
  · change EtaPow.fLoc f (L.d n (n + 1)).hom (EtaPow.fLoc f (e.f n).hom (x : EtaPow.Loc f _)) =
      EtaPow.fLoc f (e.f (n + 1)).hom (EtaPow.fLoc f (K.d n (n + 1)).hom x)
    rw [localizedMap_comp_apply, comm', ← localizedMap_comp_apply]

/-- The differential of a matrix complex is multiplication by its matrix. -/
private theorem hom_d_toCochainComplex (C : BoundedComplex A) (n : ℤ) :
    (C.toCochainComplex.d n (n + 1)).hom = (C.d n).mulVecLin :=
  congrArg ModuleCat.Hom.hom (BoundedComplex.toCochainComplex_d C n)

/-- The term of a matrix complex is the décalage term of its differential matrix. -/
theorem term_toCochainComplex_eq (f : A) (C : BoundedComplex A) (n : ℤ) :
    term f C.toCochainComplex n = EtaPow.fetaTerm f ((C.d n).mulVecLin) n :=
  congrArg (fun dd => EtaPow.fetaTerm f dd n) (hom_d_toCochainComplex C n)

variable (f : A) (K : Complex.{u, u} A) (C : BoundedComplex A) (e : K ≅ C.toCochainComplex)
  (hf : IsRegular f) (n : ℤ) (hI : (idealI C f n).IsPrincipal)

/-- The degree-`n` décalage terms of isomorphic complexes are linearly equivalent. -/
def termEquivOfIso : term f K n ≃ₗ[A] term f C.toCochainComplex n where
  __ := etaMapLinear f e.hom n
  invFun := etaMapLinear f e.inv n
  left_inv x := by
    have h := congrArg (fun φ => (φ.f n).hom x) (etaMap_comp f e.hom e.inv)
    simp only [e.hom_inv_id, etaMap_id] at h
    exact h.symm
  right_inv x := by
    have h := congrArg (fun φ => (φ.f n).hom x) (etaMap_comp f e.inv e.hom)
    simp only [e.inv_hom_id, etaMap_id] at h
    exact h.symm

include hf hI e in
/-- **The décalage term is finite projective of rank `rank Cⁿ`**, for a complex isomorphic to a
matrix complex `C` with principal determinantal ideal `I_n(C, f)`, `f` a nonzerodivisor. -/
theorem finite_projective_rankAtStalk_term_of_iso :
    ∃ (_ : Module.Finite A (term f K n)) (_ : Module.Projective A (term f K n)),
      Module.rankAtStalk (R := A) (term f K n) = fun _ => C.rank n := by
  obtain ⟨⟨hfin, hproj, hrank⟩, -⟩ :=
    EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal C f hf n hI
  let e' : term f K n ≃ₗ[A] EtaPow.fetaTerm f ((C.d n).mulVecLin) n :=
    (termEquivOfIso f K C e n).trans (LinearEquiv.ofEq _ _ (term_toCochainComplex_eq f C n))
  exact ⟨Module.Finite.equiv e'.symm, Module.Projective.of_equiv e'.symm,
    (Module.rankAtStalk_eq_of_equiv e').trans hrank⟩

include hf hI in
/-- **The graph inclusion of a term of a matrix complex has a retraction**, when the
determinantal ideal `I_n(C, f)` is principal and `f` is a nonzerodivisor. -/
theorem exists_retraction_termInclusion :
    ∃ ρ : EtaPow.fpowSub f (C.toCochainComplex.X n) n ×
        EtaPow.fpowSub f (C.toCochainComplex.X (n + 1)) (n + 1) →ₗ[A] term f C.toCochainComplex n,
      ρ ∘ₗ termInclusion f C.toCochainComplex n = LinearMap.id := by
  obtain ⟨-, ρ, hρ⟩ :=
    EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal C f hf n hI
  let eq : term f C.toCochainComplex n ≃ₗ[A] EtaPow.fetaTerm f ((C.d n).mulVecLin) n :=
    LinearEquiv.ofEq _ _ (term_toCochainComplex_eq f C n)
  refine ⟨eq.symm.toLinearMap ∘ₗ ρ, ?_⟩
  ext x : 1
  have h1 := LinearMap.congr_fun hρ (eq x)
  apply eq.injective
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  refine Eq.trans (congrArg ρ ?_) h1
  refine Prod.ext (Subtype.ext rfl) (Subtype.ext ?_)
  exact congrArg (fun dd => EtaPow.fLoc f dd
    ((x : term f C.toCochainComplex n) : EtaPow.Loc f (C.toCochainComplex.X n)))
    (hom_d_toCochainComplex C n)

include hf hI e in
/-- **The graph inclusion of a décalage term has a retraction**, for a complex isomorphic to a
matrix complex with principal determinantal ideal. -/
theorem exists_retraction_termInclusion_of_iso :
    ∃ ρ : EtaPow.fpowSub f (K.X n) n × EtaPow.fpowSub f (K.X (n + 1)) (n + 1) →ₗ[A] term f K n,
      ρ ∘ₗ termInclusion f K n = LinearMap.id := by
  obtain ⟨ρ, hρ⟩ := exists_retraction_termInclusion f C hf n hI
  refine ⟨(termEquivOfIso f K C e n).symm.toLinearMap ∘ₗ ρ ∘ₗ
    ((fpowSubMap f (e.hom.f n).hom n).prodMap (fpowSubMap f (e.hom.f (n + 1)).hom (n + 1))), ?_⟩
  ext x : 1
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [← termInclusion_naturality f e.hom n x]
  have h1 := LinearMap.congr_fun hρ (etaMapLinear f e.hom n x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
  rw [h1]
  exact (termEquivOfIso f K C e n).symm_apply_apply x

end EtaComplex

end
