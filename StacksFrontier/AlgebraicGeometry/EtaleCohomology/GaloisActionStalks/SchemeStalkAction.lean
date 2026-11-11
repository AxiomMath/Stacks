module

public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.GeometricPointAction

/-!
# The Galois action on stalks at a geometric point of a scheme

Let `S` be a scheme, `s̄` a geometric point of `S` lying over `s`, with algebraically closed
field `Ω = κ(s̄)`, and let `κ(s) ⊂ κ(s)^sep ⊂ Ω` be the separable closure of `κ(s)` in `Ω`.
An automorphism `σ ∈ Aut(Ω/κ(s))` is an automorphism `Spec σ` of the geometric point, and so
acts on the étale stalk `F_{s̄}` of every sheaf of sets `F`: the germ of `(U, ū, t)` goes to the
germ of `(U, ū ∘ Spec σ, t)` (Stacks 59.56.0.1). This is a left action, functorial in `F`.

Since `U → S` is étale, the residue field extension `κ(u)/κ(s)` at the image `u` of `ū` is finite
separable, so `ū^♯ : κ(u) → Ω` lands in `κ(s)^sep`. Consequently:

1. an automorphism of `Ω` over `κ(s)^sep` acts trivially on `F_{s̄}`;
2. every element of `Gal_{κ(s)} = Gal(κ(s)^sep/κ(s))` extends to `Ω` (the restriction map
   `Aut(Ω/κ(s)) → Gal_{κ(s)}` is surjective), and the action of `Aut(Ω/κ(s))` is the pullback of
   a unique action of `Gal_{κ(s)}`;
3. an element of `Gal_{κ(s)}` fixing the image `K` of `ū^♯` fixes the germ of `(U, ū, t)`.

Altogether `F_{s̄}` is a `Gal_{κ(s)}`-set with open stabilizers, i.e. a continuous
`Gal_{κ(s)}`-set, and the stalk functor becomes a functor from sheaves on `S_étale` to
continuous `Gal_{κ(s)}`-sets.

## Main definitions

* `AlgebraicGeometry.GeometricPoint.autHom`: `Spec σ` as an endomorphism of the geometric point.
* `AlgebraicGeometry.etaleStalkAut`: the action of `σ ∈ Aut(κ(s̄)/κ(s))` on the stalk.
* `AlgebraicGeometry.etaleStalkAutMulAction`: the resulting left action.
* `AlgebraicGeometry.GeometricPoint.galLift`: a chosen extension of `σ ∈ Gal_{κ(s)}` to `Ω`.
* `AlgebraicGeometry.etaleStalkGalSmul`, `AlgebraicGeometry.etaleStalkGalMulAction`: the action
  of the absolute Galois group on the stalk.
* `AlgebraicGeometry.etaleStalkGalContinuousGSet`: the stalk as a continuous `Gal_{κ(s)}`-set.
* `AlgebraicGeometry.etaleStalkGalSetFunctor`: the stalk functor to continuous `Gal_{κ(s)}`-sets.

## Main results

* `AlgebraicGeometry.etaleStalkAut_germ`: the rule 59.56.0.1 on germs.
* `AlgebraicGeometry.etaleStalkAut_one`, `AlgebraicGeometry.etaleStalkAut_mul`,
  `AlgebraicGeometry.etaleStalkAut_naturality`: a left action, functorial in the sheaf.
* `AlgebraicGeometry.GeometricPoint.residueFieldHom_mem_separableClosure`: `ū^♯` lands in
  `κ(s)^sep`.
* `AlgebraicGeometry.etaleStalkAut_eq_id_of_forall_eq`: statement (1).
* `AlgebraicGeometry.exists_algEquiv_extend_separableClosure`: the restriction to `κ(s)^sep` is
  surjective.
* `AlgebraicGeometry.etaleStalkAut_eq_etaleStalkGalSmul`: statement (2), with
  `AlgebraicGeometry.etaleStalkGalSmul_one`, `AlgebraicGeometry.etaleStalkGalSmul_mul` and
  `AlgebraicGeometry.etaleStalkGalSmul_germ`.
* `AlgebraicGeometry.etaleStalkGalSmul_germ_eq_of_forall`: statement (3).
* `AlgebraicGeometry.continuousSMul_etaleStalkGal`: the action is continuous.
* `AlgebraicGeometry.etaleStalkGalSmul_eq_etaleStalkSmul`: over the spectrum of a field this is
  `AlgebraicGeometry.etaleStalkSmul`.

## References

* [Stacks Project, Tag 03QW](https://stacks.math.columbia.edu/tag/03QW)
* [Stacks Project, Tag 04JK](https://stacks.math.columbia.edu/tag/04JK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

section FieldTheory

/-- **Galois automorphisms of the separable closure extend to an algebraically closed field.**
If `Ω` is algebraically closed over `k`, every automorphism of the separable closure of `k` in
`Ω` over `k` is the restriction of an automorphism of `Ω` over `k`. -/
theorem exists_algEquiv_extend_separableClosure {k Ω : Type u} [Field k] [Field Ω]
    [IsAlgClosed Ω] [Algebra k Ω] (σ : Gal(separableClosure k Ω/k)) :
    ∃ τ : Gal(Ω/k), ∀ a : separableClosure k Ω, τ (a : Ω) = (σ a : Ω) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (separableClosure k Ω) Ω
  let P := Algebra.adjoin (separableClosure k Ω) (Set.range ((↑) : s → Ω))
  have : IsAlgClosure P Ω := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let e : P ≃+* P := hs.1.aevalEquiv.symm.toRingEquiv.trans
    ((MvPolynomial.mapEquiv s σ.toRingEquiv).trans hs.1.aevalEquiv.toRingEquiv)
  have he : ∀ a : separableClosure k Ω,
      e (algebraMap (separableClosure k Ω) P a) = algebraMap (separableClosure k Ω) P (σ a) := by
    intro a
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply,
      MvPolynomial.map_C]
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  let φ : Ω ≃+* Ω := IsAlgClosure.equivOfEquiv Ω Ω e
  have hφ : ∀ a : separableClosure k Ω, φ (a : Ω) = (σ a : Ω) := by
    intro a
    have h1 : (a : Ω) = algebraMap P Ω (algebraMap (separableClosure k Ω) P a) := rfl
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he]
    rfl
  refine ⟨AlgEquiv.ofRingEquiv (f := φ) fun c => ?_, hφ⟩
  have h := hφ (algebraMap k (separableClosure k Ω) c)
  rw [AlgEquiv.commutes] at h
  exact h

end FieldTheory

namespace GeometricPoint

variable {S X : Scheme.{u}}

/-- The geometric point of `X` given by a lift `p : Spec κ(s̄) ⟶ X` of a geometric point `s̄`. -/
abbrev ofLift (sbar : GeometricPoint S) (p : sbar.source ⟶ X) : GeometricPoint X where
  residueField := sbar.residueField
  hom := p

/-- Precomposing a geometric point with `Spec τ` only depends on `τ` through its composite with
the residue field embedding. -/
theorem specMap_comp_hom_eq (t : GeometricPoint X) (τ : t.residueField →+* t.residueField) :
    Spec.map (CommRingCat.ofHom τ) ≫ t.hom =
      Spec.map (CommRingCat.ofHom (τ.comp (residueFieldHom t))) ≫
        X.fromSpecResidueField (t.hom default) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    specMap_residueFieldHom_comp_fromSpecResidueField]

/-- The residue field embedding of the image of a geometric point under a morphism is the
residue field embedding of the point composed with the residue field map of the morphism. -/
theorem residueFieldHom_map (t : GeometricPoint X) (f : X ⟶ S) :
    residueFieldHom (t.map f) =
      (residueFieldHom t).comp (f.residueFieldMap (t.hom default)).hom := by
  have h1 := specMap_residueFieldHom_comp_fromSpecResidueField (t.map f)
  have h2 : Spec.map (CommRingCat.ofHom
        ((residueFieldHom t).comp (f.residueFieldMap (t.hom default)).hom)) ≫
      S.fromSpecResidueField (f (t.hom default)) = t.hom ≫ f := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
      specMap_residueFieldHom_comp_fromSpecResidueField]
  have h3 := (cancel_mono (S.fromSpecResidueField (f (t.hom default)))).1 (h1.trans h2.symm)
  exact congrArg CommRingCat.Hom.hom (Spec.map_inj.1 h3)

/-- For a lift `p` of a geometric point `s̄` along `f : X ⟶ S`, the residue field embedding of
`p` composed with the residue field map of `f` is the residue field embedding of `s̄`. -/
theorem residueFieldHom_comp_residueFieldMap (sbar : GeometricPoint S) (f : X ⟶ S)
    (p : sbar.source ⟶ X) (hp : p ≫ f = sbar.hom) (h : f (p default) = sbar.hom default) :
    (residueFieldHom (sbar.ofLift p)).comp (f.residueFieldMap (p default)).hom =
      (residueFieldHom sbar).comp (S.residueFieldCongr h).hom.hom := by
  have key : (residueFieldHom (sbar.ofLift p)).comp (f.residueFieldMap (p default)).hom =
      residueFieldHom ((sbar.ofLift p).map f) := (residueFieldHom_map (sbar.ofLift p) f).symm
  have e1 : Spec.map (CommRingCat.ofHom
        ((residueFieldHom (sbar.ofLift p)).comp (f.residueFieldMap (p default)).hom)) ≫
      S.fromSpecResidueField (f (p default)) = p ≫ f := by
    rw [key]
    exact specMap_residueFieldHom_comp_fromSpecResidueField _
  have e2 : Spec.map (CommRingCat.ofHom
        ((residueFieldHom sbar).comp (S.residueFieldCongr h).hom.hom)) ≫
      S.fromSpecResidueField (f (p default)) = p ≫ f := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
      Scheme.residueFieldCongr_fromSpecResidueField,
      specMap_residueFieldHom_comp_fromSpecResidueField, hp]
  exact congrArg CommRingCat.Hom.hom
    (Spec.map_inj.1 ((cancel_mono (S.fromSpecResidueField (f (p default)))).1 (e1.trans e2.symm)))

/-- **A lift of a geometric point to an étale scheme sees only the separable closure.** If
`p : Spec κ(s̄) ⟶ X` lifts `s̄` along an étale morphism `X ⟶ S`, the residue field embedding
`κ(p) → κ(s̄)` lands in the separable closure of `κ(s)` in `κ(s̄)`, because `κ(p)/κ(s)` is
separable. -/
theorem residueFieldHom_mem_separableClosure (sbar : GeometricPoint S) (f : X ⟶ S) [Etale f]
    (p : sbar.source ⟶ X) (hp : p ≫ f = sbar.hom) (a : X.residueField (p default)) :
    residueFieldHom (sbar.ofLift p) a ∈ separableClosure sbar := by
  have h : f (p default) = sbar.hom default := by rw [← hp]; rfl
  have key := residueFieldHom_comp_residueFieldMap sbar f p hp h
  let : Algebra (S.residueField (f (p default))) (X.residueField (p default)) :=
    (f.residueFieldMap (p default)).hom.toAlgebra
  let : Algebra (S.residueField (f (p default))) (S.residueField (sbar.hom default)) :=
    (S.residueFieldCongr h).hom.hom.toAlgebra
  let : Algebra (S.residueField (f (p default))) sbar.residueField :=
    ((residueFieldHom sbar).comp (S.residueFieldCongr h).hom.hom).toAlgebra
  have : IsScalarTower (S.residueField (f (p default))) (S.residueField (sbar.hom default))
      sbar.residueField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : X.residueField (p default) →ₐ[S.residueField (f (p default))] sbar.residueField :=
    { toRingHom := residueFieldHom (sbar.ofLift p)
      commutes' := fun r => RingHom.congr_fun key r }
  exact algHom_mem_separableClosure (κ := S.residueField (sbar.hom default)) φ a

/-- The image of the residue field embedding of a lift of a geometric point to an étale scheme
lies in a finite subextension of the separable closure. -/
theorem exists_finiteDimensional_residueFieldHom (sbar : GeometricPoint S) (f : X ⟶ S)
    [Etale f] (p : sbar.source ⟶ X) (hp : p ≫ f = sbar.hom) :
    ∃ E : IntermediateField (S.residueField (sbar.hom default)) (separableClosure sbar),
      FiniteDimensional (S.residueField (sbar.hom default)) E ∧
        ∀ a : separableClosure sbar,
          (a : sbar.residueField) ∈ Set.range (residueFieldHom (sbar.ofLift p)) → a ∈ E := by
  have h : f (p default) = sbar.hom default := by rw [← hp]; rfl
  have key := residueFieldHom_comp_residueFieldMap sbar f p hp h
  have hinv : ∀ r, (S.residueFieldCongr h).hom.hom ((S.residueFieldCongr h).inv.hom r) = r :=
    fun r => by
      change ((S.residueFieldCongr h).inv ≫ (S.residueFieldCongr h).hom).hom r = r
      rw [Iso.inv_hom_id]
      rfl
  have hhom : ∀ r, (S.residueFieldCongr h).inv.hom ((S.residueFieldCongr h).hom.hom r) = r :=
    fun r => by
      change ((S.residueFieldCongr h).hom ≫ (S.residueFieldCongr h).inv).hom r = r
      rw [Iso.hom_inv_id]
      rfl
  have hfin : letI := (f.residueFieldMap (p default)).hom.toAlgebra
      Module.Finite (S.residueField (f (p default))) (X.residueField (p default)) :=
    finite_residueField_of_etale_fibers f (fun y => by
      change Etale (Limits.pullback.snd f (S.fromSpecResidueField y))
      infer_instance) (p default)
  let : Algebra (S.residueField (f (p default))) (X.residueField (p default)) :=
    (f.residueFieldMap (p default)).hom.toAlgebra
  let : Algebra (S.residueField (sbar.hom default)) (X.residueField (p default)) :=
    ((f.residueFieldMap (p default)).hom.comp (S.residueFieldCongr h).inv.hom).toAlgebra
  have : Module.Finite (S.residueField (sbar.hom default)) (X.residueField (p default)) :=
    Module.Finite.of_equiv_equiv (S.residueFieldCongr h).commRingCatIsoToRingEquiv
      (RingEquiv.refl _) (RingHom.ext fun r => by
        change (f.residueFieldMap (p default)).hom
          ((S.residueFieldCongr h).inv.hom ((S.residueFieldCongr h).hom.hom r)) =
            (f.residueFieldMap (p default)).hom r
        rw [hhom])
  let ψ : X.residueField (p default) →ₐ[S.residueField (sbar.hom default)]
      separableClosure sbar :=
    { toRingHom := (residueFieldHom (sbar.ofLift p)).codRestrict (separableClosure sbar)
        (fun x => residueFieldHom_mem_separableClosure sbar f p hp x)
      commutes' := fun r => Subtype.ext (by
        change residueFieldHom (sbar.ofLift p)
          ((f.residueFieldMap (p default)).hom ((S.residueFieldCongr h).inv.hom r)) =
            residueFieldHom sbar r
        have := RingHom.congr_fun key ((S.residueFieldCongr h).inv.hom r)
        simp only [RingHom.coe_comp, Function.comp_apply, hinv] at this
        exact this) }
  refine ⟨ψ.fieldRange, ψ.toLinearMap.finiteDimensional_range, ?_⟩
  rintro a ⟨x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

/-- Two endomorphisms of `κ(s̄)` agreeing on the separable closure of `κ(s)` have the same
composite with any lift of `s̄` to an étale scheme. -/
theorem specMap_comp_eq_of_forall_eq (sbar : GeometricPoint S) (f : X ⟶ S) [Etale f]
    (p : sbar.source ⟶ X) (hp : p ≫ f = sbar.hom)
    (τ τ' : sbar.residueField →+* sbar.residueField)
    (h : ∀ a : separableClosure sbar, τ a = τ' a) :
    Spec.map (CommRingCat.ofHom τ) ≫ p = Spec.map (CommRingCat.ofHom τ') ≫ p := by
  have hc : τ.comp (residueFieldHom (sbar.ofLift p)) = τ'.comp (residueFieldHom (sbar.ofLift p)) :=
    RingHom.ext fun x => h ⟨_, residueFieldHom_mem_separableClosure sbar f p hp x⟩
  refine (specMap_comp_hom_eq (sbar.ofLift p) τ).trans ?_
  refine Eq.trans ?_ (specMap_comp_hom_eq (sbar.ofLift p) τ').symm
  rw [hc]

/-- An automorphism `σ` of `κ(s̄)` over `κ(s)`, as the endomorphism `Spec σ` of the geometric
point `s̄`. -/
def autHom (sbar : GeometricPoint S)
    (σ : Gal(sbar.residueField/S.residueField (sbar.hom default))) :
    GeometricPoint.Hom sbar sbar :=
  ⟨Spec.map (CommRingCat.ofHom σ.toRingHom), sbar.specMap_algEquiv_comp_hom σ⟩

/-- A chosen extension to `κ(s̄)` of an element of the absolute Galois group `Gal_{κ(s)}`. -/
def galLift (sbar : GeometricPoint S) (σ : absoluteGaloisGroup sbar) :
    Gal(sbar.residueField/S.residueField (sbar.hom default)) :=
  (exists_algEquiv_extend_separableClosure σ).choose

/-- The chosen extension restricts to the given Galois automorphism. -/
theorem galLift_apply (sbar : GeometricPoint S) (σ : absoluteGaloisGroup sbar)
    (a : separableClosure sbar) : sbar.galLift σ (a : sbar.residueField) = (σ a : _) :=
  (exists_algEquiv_extend_separableClosure σ).choose_spec a

end GeometricPoint

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (sbar : GeometricPoint S)

/-- The pointed étale neighbourhood `(U, ū ∘ Spec σ)` obtained from `(U, ū)` and an automorphism
`σ` of `κ(s̄)` over `κ(s)`. -/
def autNeighborhood (σ : Gal(sbar.residueField/S.residueField (sbar.hom default)))
    (U : (geometricPointFiber B S hS sbar).Elements) : (geometricPointFiber B S hS sbar).Elements :=
  Functor.elementsMk _ U.1 ⟨Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ U.2.1, by
    rw [Category.assoc, U.2.2]
    exact sbar.specMap_algEquiv_comp_hom σ⟩

/-- The neighbourhood `(U, ū ∘ Spec σ)` lies over the same étale scheme as `(U, ū)`. -/
@[simp]
theorem autNeighborhood_fst (σ : Gal(sbar.residueField/S.residueField (sbar.hom default)))
    (U : (geometricPointFiber B S hS sbar).Elements) : (autNeighborhood B S hS sbar σ U).1 = U.1 :=
  rfl

/-- The lift of `(U, ū ∘ Spec σ)` is `ū ∘ Spec σ`. -/
theorem autNeighborhood_snd_coe (σ : Gal(sbar.residueField/S.residueField (sbar.hom default)))
    (U : (geometricPointFiber B S hS sbar).Elements) :
    (autNeighborhood B S hS sbar σ U).2.1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ U.2.1 :=
  rfl

/-- Two maps out of an étale stalk agree if they agree on germs. -/
theorem etaleStalk_hom_ext {F : smallEtaleTopos.{u, max u v} B S hS} {Y : Type (max u v)}
    {f g : (etaleStalkFunctor.{u, v} B S hS sbar).obj F ⟶ Y}
    (h : ∀ (U : (geometricPointFiber B S hS sbar).Elements)
      (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)),
      ConcreteCategory.hom f (etaleStalkGerm.{u, v} B S hS sbar F U t) =
        ConcreteCategory.hom g (etaleStalkGerm.{u, v} B S hS sbar F U t)) : f = g := by
  ext x
  obtain ⟨V, t, rfl⟩ := Types.jointly_surjective'
    (F := (Functor.Elements.π (geometricPointFiber B S hS sbar)).op ⋙
      (sheafToPresheaf _ _).obj F) x
  exact h V.unop t

variable (F : smallEtaleTopos.{u, max u v} B S hS)

/-- Germs over the same étale scheme at equal lifts agree. -/
theorem etaleStalkGerm_congr (U : SmallEtale B S hS)
    (p p' : (geometricPointFiber B S hS sbar).obj U) (h : p.1 = p'.1)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U)) :
    etaleStalkGerm.{u, v} B S hS sbar F (Functor.elementsMk _ U p) t =
      etaleStalkGerm.{u, v} B S hS sbar F (Functor.elementsMk _ U p') t := by
  obtain rfl : p = p' := Subtype.ext h
  rfl

/-- **The action of `Aut(κ(s̄)/κ(s))` on the étale stalk at `s̄`** (Stacks 03QW). An automorphism
`σ` acts by the canonical map of stalks along the endomorphism `Spec σ` of `s̄`. -/
def etaleStalkAut (σ : Gal(sbar.residueField/S.residueField (sbar.hom default))) :
    (etaleStalkFunctor.{u, v} B S hS sbar).obj F ⟶ (etaleStalkFunctor.{u, v} B S hS sbar).obj F :=
  (geometricPointStalkMap B S hS (sbar.autHom σ) (Type (max u v))).app ((sheafToPresheaf _ _).obj F)

/-- **The rule 59.56.0.1.** The germ of `(U, ū, t)` goes to the germ of `(U, ū ∘ Spec σ, t)`. -/
theorem etaleStalkAut_germ (σ : Gal(sbar.residueField/S.residueField (sbar.hom default)))
    (U : (geometricPointFiber B S hS sbar).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    ConcreteCategory.hom (etaleStalkAut.{u, v} B S hS sbar F σ)
        (etaleStalkGerm.{u, v} B S hS sbar F U t) =
      etaleStalkGerm.{u, v} B S hS sbar F (autNeighborhood B S hS sbar σ U) t :=
  ConcreteCategory.congr_hom (colimit.ι_pre ((Functor.Elements.π
    (geometricPointFiber B S hS sbar)).op ⋙ (sheafToPresheaf _ _).obj F)
    (neighborhoodFunctor B S hS (sbar.autHom σ)).op (op U)) t

/-- The identity acts trivially on the stalk. -/
theorem etaleStalkAut_one : etaleStalkAut.{u, v} B S hS sbar F 1 = 𝟙 _ := by
  refine etaleStalk_hom_ext B S hS sbar (fun U t => ?_)
  rw [etaleStalkAut_germ]
  refine etaleStalkGerm_congr.{u, v} B S hS sbar F U.1 (autNeighborhood B S hS sbar 1 U).2 U.2
    ?_ t
  change Spec.map (CommRingCat.ofHom (RingHom.id sbar.residueField)) ≫ U.2.1 = U.2.1
  rw [show CommRingCat.ofHom (RingHom.id sbar.residueField) = 𝟙 (CommRingCat.of _) from rfl,
    Spec.map_id, Category.id_comp]

/-- **The action of `Aut(κ(s̄)/κ(s))` on the stalk is a left action**: `σ₁ · (σ₂ · ξ) =
(σ₁ σ₂) · ξ`. -/
theorem etaleStalkAut_mul (σ τ : Gal(sbar.residueField/S.residueField (sbar.hom default))) :
    etaleStalkAut.{u, v} B S hS sbar F (σ * τ) =
      etaleStalkAut.{u, v} B S hS sbar F τ ≫ etaleStalkAut.{u, v} B S hS sbar F σ := by
  refine etaleStalk_hom_ext B S hS sbar (fun U t => ?_)
  rw [ConcreteCategory.comp_apply, etaleStalkAut_germ, etaleStalkAut_germ]
  refine Eq.trans ?_
    (etaleStalkAut_germ.{u, v} B S hS sbar F σ (autNeighborhood B S hS sbar τ U) t).symm
  refine etaleStalkGerm_congr.{u, v} B S hS sbar F U.1 (autNeighborhood B S hS sbar (σ * τ) U).2
    (autNeighborhood B S hS sbar σ (autNeighborhood B S hS sbar τ U)).2 ?_ t
  change Spec.map (CommRingCat.ofHom (σ.toRingHom.comp τ.toRingHom)) ≫ U.2.1 =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ U.2.1
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- **The action of `Aut(κ(s̄)/κ(s))` on the stalk is functorial in the sheaf.** -/
theorem etaleStalkAut_naturality {F F' : smallEtaleTopos.{u, max u v} B S hS} (φ : F ⟶ F')
    (σ : Gal(sbar.residueField/S.residueField (sbar.hom default))) :
    etaleStalkAut.{u, v} B S hS sbar F σ ≫ (etaleStalkFunctor.{u, v} B S hS sbar).map φ =
      (etaleStalkFunctor.{u, v} B S hS sbar).map φ ≫ etaleStalkAut.{u, v} B S hS sbar F' σ :=
  ((geometricPointStalkMap B S hS (sbar.autHom σ) (Type (max u v))).naturality
    ((sheafToPresheaf _ _).map φ)).symm

/-- The group `Aut(κ(s̄)/κ(s))` acts on the left on the étale stalk at `s̄`. -/
@[instance_reducible]
def etaleStalkAutMulAction :
    MulAction (Gal(sbar.residueField/S.residueField (sbar.hom default)))
      ((etaleStalkFunctor.{u, v} B S hS sbar).obj F) where
  smul σ x := ConcreteCategory.hom (etaleStalkAut.{u, v} B S hS sbar F σ) x
  one_smul x := ConcreteCategory.congr_hom (etaleStalkAut_one.{u, v} B S hS sbar F) x
  mul_smul σ τ x := ConcreteCategory.congr_hom (etaleStalkAut_mul.{u, v} B S hS sbar F σ τ) x

/-- Automorphisms of `κ(s̄)` over `κ(s)` that agree on the separable closure `κ(s)^sep` act in
the same way on the stalk. -/
theorem etaleStalkAut_eq_of_forall_eq
    (σ τ : Gal(sbar.residueField/S.residueField (sbar.hom default)))
    (h : ∀ a : GeometricPoint.separableClosure sbar, σ (a : sbar.residueField) = τ a) :
    etaleStalkAut.{u, v} B S hS sbar F σ = etaleStalkAut.{u, v} B S hS sbar F τ := by
  refine etaleStalk_hom_ext B S hS sbar (fun U t => ?_)
  rw [etaleStalkAut_germ, etaleStalkAut_germ]
  refine etaleStalkGerm_congr.{u, v} B S hS sbar F U.1 (autNeighborhood B S hS sbar σ U).2
    (autNeighborhood B S hS sbar τ U).2 ?_ t
  exact sbar.specMap_comp_eq_of_forall_eq (B.inclusion.map U.1.obj.hom) U.2.1 U.2.2 _ _ h

/-- **Statement (1) of Section 03QW.** An automorphism of `κ(s̄)` over the separable closure
`κ(s)^sep` acts trivially on the stalk. -/
theorem etaleStalkAut_eq_id_of_forall_eq
    (σ : Gal(sbar.residueField/S.residueField (sbar.hom default)))
    (h : ∀ a : GeometricPoint.separableClosure sbar, σ (a : sbar.residueField) = a) :
    etaleStalkAut.{u, v} B S hS sbar F σ = 𝟙 _ :=
  (etaleStalkAut_eq_of_forall_eq.{u, v} B S hS sbar F σ 1 h).trans
    (etaleStalkAut_one.{u, v} B S hS sbar F)

/-- **The action of the absolute Galois group `Gal_{κ(s)}` on the étale stalk at `s̄`**: an
element acts as any of its extensions to `κ(s̄)`. -/
def etaleStalkGalSmul (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    (etaleStalkFunctor.{u, v} B S hS sbar).obj F ⟶ (etaleStalkFunctor.{u, v} B S hS sbar).obj F :=
  etaleStalkAut.{u, v} B S hS sbar F (sbar.galLift σ)

/-- **Statement (2) of Section 03QW.** The action of `Aut(κ(s̄)/κ(s))` on the stalk is
determined by the action of `Gal_{κ(s)}`: an automorphism restricting to `σ` on `κ(s)^sep` acts
as `σ`. Every `σ` arises this way (`AlgebraicGeometry.exists_algEquiv_extend_separableClosure`),
so the action of `Gal_{κ(s)}` is in turn determined by that of `Aut(κ(s̄)/κ(s))`. -/
theorem etaleStalkAut_eq_etaleStalkGalSmul
    (τ : Gal(sbar.residueField/S.residueField (sbar.hom default)))
    (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (h : ∀ a : GeometricPoint.separableClosure sbar, τ (a : sbar.residueField) = (σ a : _)) :
    etaleStalkAut.{u, v} B S hS sbar F τ = etaleStalkGalSmul.{u, v} B S hS sbar F σ :=
  etaleStalkAut_eq_of_forall_eq.{u, v} B S hS sbar F _ _ fun a =>
    (h a).trans (sbar.galLift_apply σ a).symm

/-- The action of `Gal_{κ(s)}` on germs: `σ` sends the germ of `(U, ū, t)` to the germ of
`(U, ū ∘ Spec τ, t)` for any extension `τ` of `σ` to `κ(s̄)`. -/
theorem etaleStalkGalSmul_germ (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (τ : Gal(sbar.residueField/S.residueField (sbar.hom default)))
    (h : ∀ a : GeometricPoint.separableClosure sbar, τ (a : sbar.residueField) = (σ a : _))
    (U : (geometricPointFiber B S hS sbar).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1)) :
    ConcreteCategory.hom (etaleStalkGalSmul.{u, v} B S hS sbar F σ)
        (etaleStalkGerm.{u, v} B S hS sbar F U t) =
      etaleStalkGerm.{u, v} B S hS sbar F (autNeighborhood B S hS sbar τ U) t := by
  rw [← etaleStalkAut_eq_etaleStalkGalSmul.{u, v} B S hS sbar F τ σ h, etaleStalkAut_germ]

/-- The identity of `Gal_{κ(s)}` acts trivially on the stalk. -/
theorem etaleStalkGalSmul_one : etaleStalkGalSmul.{u, v} B S hS sbar F 1 = 𝟙 _ :=
  (etaleStalkAut_eq_etaleStalkGalSmul.{u, v} B S hS sbar F 1 1 fun _ => rfl).symm.trans
    (etaleStalkAut_one.{u, v} B S hS sbar F)

/-- The action of `Gal_{κ(s)}` on the stalk is a left action. -/
theorem etaleStalkGalSmul_mul (σ τ : GeometricPoint.absoluteGaloisGroup sbar) :
    etaleStalkGalSmul.{u, v} B S hS sbar F (σ * τ) =
      etaleStalkGalSmul.{u, v} B S hS sbar F τ ≫ etaleStalkGalSmul.{u, v} B S hS sbar F σ := by
  refine (etaleStalkAut_eq_etaleStalkGalSmul.{u, v} B S hS sbar F
    (sbar.galLift σ * sbar.galLift τ) (σ * τ) fun a => ?_).symm.trans
    (etaleStalkAut_mul.{u, v} B S hS sbar F _ _)
  rw [AlgEquiv.mul_apply, sbar.galLift_apply τ a, sbar.galLift_apply σ (τ a)]
  rfl

/-- The action of `Gal_{κ(s)}` on the stalk is functorial in the sheaf. -/
theorem etaleStalkGalSmul_naturality {F F' : smallEtaleTopos.{u, max u v} B S hS} (φ : F ⟶ F')
    (σ : GeometricPoint.absoluteGaloisGroup sbar) :
    etaleStalkGalSmul.{u, v} B S hS sbar F σ ≫ (etaleStalkFunctor.{u, v} B S hS sbar).map φ =
      (etaleStalkFunctor.{u, v} B S hS sbar).map φ ≫ etaleStalkGalSmul.{u, v} B S hS sbar F' σ :=
  etaleStalkAut_naturality.{u, v} B S hS sbar φ _

/-- **Statement (3) of Section 03QW.** Let `ξ` be the germ of `(U, ū, t)` and `K ⊂ κ(s)^sep` the
image of `ū^♯ : κ(u) → κ(s̄)`. Every element of `Gal(κ(s)^sep/K)`, that is every element of
`Gal_{κ(s)}` fixing `K` pointwise, fixes `ξ`. -/
theorem etaleStalkGalSmul_germ_eq_of_forall (σ : GeometricPoint.absoluteGaloisGroup sbar)
    (U : (geometricPointFiber B S hS sbar).Elements)
    (t : ((sheafToPresheaf _ _).obj F).obj (op U.1))
    (h : ∀ a : GeometricPoint.separableClosure sbar,
      (a : sbar.residueField) ∈ Set.range (GeometricPoint.residueFieldHom (sbar.ofLift U.2.1)) →
        σ a = a) :
    ConcreteCategory.hom (etaleStalkGalSmul.{u, v} B S hS sbar F σ)
        (etaleStalkGerm.{u, v} B S hS sbar F U t) =
      etaleStalkGerm.{u, v} B S hS sbar F U t := by
  rw [etaleStalkGalSmul_germ.{u, v} B S hS sbar F σ (sbar.galLift σ)
    (sbar.galLift_apply σ) U t]
  refine etaleStalkGerm_congr.{u, v} B S hS sbar F U.1
    (autNeighborhood B S hS sbar (sbar.galLift σ) U).2 U.2 ?_ t
  have hι : (sbar.galLift σ).toRingHom.comp (GeometricPoint.residueFieldHom (sbar.ofLift U.2.1)) =
      GeometricPoint.residueFieldHom (sbar.ofLift U.2.1) := by
    refine RingHom.ext fun x => ?_
    have hx := GeometricPoint.residueFieldHom_mem_separableClosure sbar
      (B.inclusion.map U.1.obj.hom) U.2.1 U.2.2 x
    have := sbar.galLift_apply σ ⟨_, hx⟩
    rw [h ⟨_, hx⟩ ⟨x, rfl⟩] at this
    exact this
  change Spec.map (CommRingCat.ofHom (sbar.galLift σ).toRingHom) ≫ U.2.1 = U.2.1
  refine ((sbar.ofLift U.2.1).specMap_comp_hom_eq _).trans ?_
  rw [hι]
  exact (sbar.ofLift U.2.1).specMap_residueFieldHom_comp_fromSpecResidueField

/-- The absolute Galois group `Gal_{κ(s)}` acts on the étale stalk at `s̄`. -/
@[instance_reducible]
def etaleStalkGalMulAction : MulAction (GeometricPoint.absoluteGaloisGroup sbar)
    ((etaleStalkFunctor.{u, v} B S hS sbar).obj F) where
  smul σ x := ConcreteCategory.hom (etaleStalkGalSmul.{u, v} B S hS sbar F σ) x
  one_smul x := ConcreteCategory.congr_hom (etaleStalkGalSmul_one.{u, v} B S hS sbar F) x
  mul_smul σ τ x :=
    ConcreteCategory.congr_hom (etaleStalkGalSmul_mul.{u, v} B S hS sbar F σ τ) x

attribute [local instance] etaleStalkGalMulAction

/-- **The action of `Gal_{κ(s)}` on the étale stalk is continuous**: the stabilizer of the germ
of `(U, ū, t)` contains the open subgroup fixing the finite extension `K` of `κ(s)` cut out by
`ū`. -/
theorem continuousSMul_etaleStalkGal :
    letI : TopologicalSpace ((etaleStalkFunctor.{u, v} B S hS sbar).obj F) := ⊥
    ContinuousSMul (GeometricPoint.absoluteGaloisGroup sbar)
      ((etaleStalkFunctor.{u, v} B S hS sbar).obj F) := by
  let : TopologicalSpace ((etaleStalkFunctor.{u, v} B S hS sbar).obj F) := ⊥
  let : DiscreteTopology ((etaleStalkFunctor.{u, v} B S hS sbar).obj F) := ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  obtain ⟨V, t, rfl⟩ := Types.jointly_surjective'
    (F := (Functor.Elements.π (geometricPointFiber B S hS sbar)).op ⋙
      (sheafToPresheaf _ _).obj F) x
  obtain ⟨E, hE, hsub⟩ := GeometricPoint.exists_finiteDimensional_residueFieldHom sbar
    (B.inclusion.map V.unop.1.obj.hom) V.unop.2.1 V.unop.2.2
  have hle : E.fixingSubgroup ≤ MulAction.stabilizer (GeometricPoint.absoluteGaloisGroup sbar)
      (etaleStalkGerm.{u, v} B S hS sbar F V.unop t) := by
    intro σ hσ
    rw [MulAction.mem_stabilizer_iff]
    exact etaleStalkGalSmul_germ_eq_of_forall.{u, v} B S hS sbar F σ V.unop t
      fun a ha => (IntermediateField.mem_fixingSubgroup_iff E σ).1 hσ a (hsub a ha)
  exact Subgroup.isOpen_mono hle E.fixingSubgroup_isOpen

/-- **The étale stalk at `s̄` as a continuous `Gal_{κ(s)}`-set.** -/
def etaleStalkGalContinuousGSet :
    AlgebraicGeometry.ContinuousGSet.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar) := by
  letI : HasForget₂ (Type max u v) TopCat.{max u v} :=
    { forget₂ := TopCat.discrete, forget_comp := rfl }
  letI : TopologicalSpace ((etaleStalkFunctor.{u, v} B S hS sbar).obj F) := ⊥
  letI : DiscreteTopology ((etaleStalkFunctor.{u, v} B S hS sbar).obj F) := ⟨rfl⟩
  exact ⟨⟨Action.ofMulAction (GeometricPoint.absoluteGaloisGroup sbar)
    ((etaleStalkFunctor.{u, v} B S hS sbar).obj F),
    continuousSMul_etaleStalkGal.{u, v} B S hS sbar F⟩, ⟨rfl⟩⟩

/-- **The stalk functor at `s̄` with its Galois action**, from the small étale topos of `S` to
continuous `Gal_{κ(s)}`-sets. -/
def etaleStalkGalSetFunctor :
    smallEtaleTopos.{u, max u v} B S hS ⥤
      AlgebraicGeometry.ContinuousGSet.{u, max u v} (GeometricPoint.absoluteGaloisGroup sbar) where
  obj F := etaleStalkGalContinuousGSet.{u, v} B S hS sbar F
  map {F F'} φ := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := (etaleStalkFunctor.{u, v} B S hS sbar).map φ
      comm := fun σ ↦ etaleStalkGalSmul_naturality.{u, v} B S hS sbar φ σ })
  map_id F := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact (etaleStalkFunctor.{u, v} B S hS sbar).map_id F
  map_comp {F F' F''} φ ψ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact (etaleStalkFunctor.{u, v} B S hS sbar).map_comp φ ψ

/-- Over the spectrum of a field, the action of `Gal_{κ(s)}` is the action
`AlgebraicGeometry.etaleStalkSmul` through the lifts of the geometric point. -/
theorem etaleStalkGalSmul_eq_etaleStalkSmul (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) (tbar : GeometricPoint (Spec (.of K)))
    (G : smallEtaleTopos.{u, max u v} B (Spec (.of K)) hK)
    (σ : GeometricPoint.absoluteGaloisGroup tbar) :
    etaleStalkGalSmul.{u, v} B (Spec (.of K)) hK tbar G σ = etaleStalkSmul.{u, v} B K hK tbar G σ :=
  (etaleStalkSmul_eq_geometricPointStalkMap.{u, v} B K hK tbar G σ (tbar.galLift σ)
    (fun a => (tbar.galLift_apply σ a).symm) (tbar.autHom (tbar.galLift σ)) rfl).symm

/-! ### Registration of Section 03QW -/

add_to_stacks 03QW "the action of Aut(κ(s̄)/κ(s)) on the étale stalk at a geometric point s̄"
  AlgebraicGeometry.etaleStalkAut
add_to_stacks 03QW "the rule 59.56.0.1 on germs" AlgebraicGeometry.etaleStalkAut_germ
add_to_stacks 03QW "the identity acts trivially" AlgebraicGeometry.etaleStalkAut_one
add_to_stacks 03QW "the action is a left action" AlgebraicGeometry.etaleStalkAut_mul
add_to_stacks 03QW "the action is functorial in the sheaf"
  AlgebraicGeometry.etaleStalkAut_naturality
add_to_stacks 03QW "the left action of Aut(κ(s̄)/κ(s)) on the stalk"
  AlgebraicGeometry.etaleStalkAutMulAction
add_to_stacks 03QW "Aut(κ(s̄)/κ(s)) → Gal_κ(s) is surjective"
  AlgebraicGeometry.exists_algEquiv_extend_separableClosure
add_to_stacks 03QW "(1): Aut(κ(s̄)/κ(s)^sep) acts trivially"
  AlgebraicGeometry.etaleStalkAut_eq_id_of_forall_eq
add_to_stacks 03QW "(2): the action of Gal_κ(s) on the stalk" AlgebraicGeometry.etaleStalkGalSmul
add_to_stacks 03QW "(2): the Aut-action is the pullback of the Gal_κ(s)-action"
  AlgebraicGeometry.etaleStalkAut_eq_etaleStalkGalSmul
add_to_stacks 03QW "(2): the Gal_κ(s)-action on germs" AlgebraicGeometry.etaleStalkGalSmul_germ
add_to_stacks 03QW "(2): the stalk as a Gal_κ(s)-set" AlgebraicGeometry.etaleStalkGalMulAction
add_to_stacks 03QW "(3): Gal(κ(s)^sep/K) fixes the germ of (U, ū, t)"
  AlgebraicGeometry.etaleStalkGalSmul_germ_eq_of_forall
add_to_stacks 03QW "the Gal_κ(s)-action is continuous"
  AlgebraicGeometry.continuousSMul_etaleStalkGal
add_to_stacks 03QW "the stalk as a Gal_κ(s)-set (04JJ)"
  AlgebraicGeometry.etaleStalkGalContinuousGSet
add_to_stacks 03QW "the stalk functor Sh(S_étale) → Gal_κ(s)-Sets"
  AlgebraicGeometry.etaleStalkGalSetFunctor

end AlgebraicGeometry

end
