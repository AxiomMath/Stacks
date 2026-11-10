module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Generators
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Composition
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.KoszulBraiding
public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.HomComplex.TensorHom
public import StacksFrontier.Homology.KFlat.BaseChange
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.LeftDual
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorLargeUniverse
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.BoundedTheta
import StacksCore.Tactic.EgaSgaAttribute
import all StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.ProjectiveComparison
import all StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.RepresentativeDiagonal
import all StacksFrontier.Homology.HomComplex.Evaluation.TensorHom.BoundedTheta

/-!
# The derived tensor--Hom diagonal: the bounded-below case

Triangulatedness of the derived tensor and Hom functors in each variable, the chain-level
tensor--Hom adjunction, the computation of the derived diagonal for a K-flat tensor factor and a
bounded-above projective Hom source (`isIso_diagonal_of_projective_quasiIso_theta`), and the case
of [stacks 0ATK] in which `M` is pseudo-coherent, `L` is bounded below and `K` has Tor amplitude
in `[a, ∞]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Pretriangulated ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u v w w'

set_option maxRecDepth 4096

namespace Stacks.DerivedTensorHomDiagonal

open StacksDraft.DerivedHom

variable {R : Type u} [CommRing R]

open CochainComplex HomComplex HomologicalComplex TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- The tensor bifunctor agrees with the triangulated derived tensor construction. -/
private noncomputable def tensorFunctorIsoDerivedTensorProduct
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    (Functor.curry.obj (DerivedInternalHom.Model.tensor R)).flip.obj (DerivedCategory.Q.obj K) ≅
      CochainComplex.DerivedTensor.derivedTensorProduct (DerivedCategory.Q.obj K) := by
  let F :=
    (Functor.curry.obj (DerivedInternalHom.Model.tensor R)).flip.obj (DerivedCategory.Q.obj K)
  let G := CochainComplex.DerivedTensor.derivedTensorProduct (DerivedCategory.Q.obj K)
  let H := TrightCochain K ⋙ DerivedCategory.Q
  let α : DerivedCategory.Q ⋙ F ≅ H := NatIso.ofComponents
    (fun X ↦ (DerivedInternalHom.Model.adjunction R).tensorIso X K hK)
    (fun f ↦ by
      have h := (DerivedInternalHom.Model.adjunction R).tensorIso_naturality f (𝟙 K) hK hK
      rwa [DerivedCategory.Q.map_id] at h)
  let β := Classical.choice
    (CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution
    (DerivedCategory.Q.obj K) K K (𝟙 K) hK
    ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)).1
  let Q := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  let ε : Q ⋙ Tright K ≅ TrightCochain K ⋙ Q :=
    CategoryTheory.Quotient.lift.isLift (homotopic (ModuleCat R) (ComplexShape.up ℤ))
      (TrightCochain K ⋙ Q)
      (fun _ _ _ _ h ↦ CategoryTheory.Quotient.sound _ (TrightCochain_preservesHomotopyRel K h))
  let γ : DerivedCategory.Q ⋙ G ≅ H :=
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat R)).symm G ≪≫
      Functor.isoWhiskerLeft Q β ≪≫ Functor.isoWhiskerRight ε DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (TrightCochain K) (DerivedCategory.quotientCompQhIso (ModuleCat R))
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ F) (DerivedCategory.Q ⋙ G) F G (α ≪≫ γ.symm)

/-- Triangulatedness transfers along an isomorphism of endofunctors of the derived category. -/
private theorem exists_isTriangulated_of_iso {F G : DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R)} [F.CommShift ℤ] [F.IsTriangulated] (e : F ≅ G) :
    ∃ s : G.CommShift ℤ, letI := s; G.IsTriangulated := by
  let s := Functor.CommShift.ofIso e ℤ
  have : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  exact ⟨s, Functor.isTriangulated_of_iso e⟩

/-- The tensor bifunctor is triangulated in its first argument. -/
private theorem exists_tensorFunctor_isTriangulated
    (M : DerivedCategory (ModuleCat.{u} R)) :
    let F := (Functor.curry.obj (DerivedInternalHom.Model.tensor R)).flip.obj M
    ∃ s : F.CommShift ℤ, letI := s; F.IsTriangulated := by
  let T := (Functor.curry.obj (DerivedInternalHom.Model.tensor R)).flip
  obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution
    (DerivedCategory.Q.objPreimage M)
  have : QuasiIso f := hf
  let eP : DerivedCategory.Q.obj P ≅ M :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  let e : CochainComplex.DerivedTensor.derivedTensorProduct (DerivedCategory.Q.obj P) ≅ T.obj M :=
    (tensorFunctorIsoDerivedTensorProduct P hP).symm ≪≫ T.mapIso eP
  exact exists_isTriangulated_of_iso e

/-- The fixed tensor–Hom equivalence is an adjunction of the corresponding endofunctors. -/
@[sga "6 I 7.4" "special case"]
private noncomputable def tensorHomAdjunction
    (M : DerivedCategory (ModuleCat.{u} R)) :
    (Functor.curry.obj (DerivedInternalHom.Model.tensor R)).flip.obj M ⊣
      (Functor.curry.obj (DerivedInternalHom.Model.hom R)).obj (Opposite.op M) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦ ((DerivedInternalHom.Model.adjunction R).homEquiv X M Y).symm.toEquiv
      homEquiv_naturality_left_symm := fun f g ↦
        (DerivedInternalHom.Model.adjunction R).homEquiv_naturality_left f g
      homEquiv_naturality_right := fun f g ↦ by
        apply ((DerivedInternalHom.Model.adjunction R).homEquiv _ M _).injective
        change (DerivedInternalHom.Model.adjunction R).homEquiv _ M _
            (((DerivedInternalHom.Model.adjunction R).homEquiv _ M _).symm (f ≫ g)) =
          (DerivedInternalHom.Model.adjunction R).homEquiv _ M _
            (((DerivedInternalHom.Model.adjunction R).homEquiv _ M _).symm f ≫
              (DerivedInternalHom.Model.hom R).map (𝟙 (Opposite.op M), g))
        rw [(DerivedInternalHom.Model.adjunction R).homEquiv_naturality_right]
        simp only [AddEquiv.apply_symm_apply] }

/-- Derived Hom is triangulated in its target argument. -/
private theorem exists_homFunctor_isTriangulated
    (M : DerivedCategory (ModuleCat.{u} R)) :
    let F := (Functor.curry.obj (DerivedInternalHom.Model.hom R)).obj (Opposite.op M)
    ∃ s : F.CommShift ℤ, letI := s; F.IsTriangulated := by
  obtain ⟨s, hs⟩ := exists_tensorFunctor_isTriangulated M
  let := s
  have := hs
  let adj := tensorHomAdjunction M
  let t := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨t, adj.isTriangulated_rightAdjoint⟩

/-- The one-sided hypotheses yield simultaneous representatives on which the comparison
is already an isomorphism of complexes. -/
private theorem exists_bounded_tensorHom_isIso_representatives
    (K L M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) [L.IsGE b]
    (hK : ∀ (N : ModuleCat.{u} R) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))))) :
    ∃ (E F P : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ),
      E.IsStrictlyGE a ∧ E.KFlat ∧ (∀ i, Module.Flat R (E.X i)) ∧
      F.IsStrictlyGE b ∧ P.IsStrictlyLE d ∧
      (∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) ∧
      Nonempty (K ≅ DerivedCategory.Q.obj E) ∧
      Nonempty (L ≅ DerivedCategory.Q.obj F) ∧
      Nonempty (M ≅ DerivedCategory.Q.obj P) ∧ IsIso (Stacks.HomComplex.TensorHomComparison.theta E
        F P) := by
  obtain ⟨E, F, P, d, hEa, hEk, hEf, hFb, hPd, hP, eK, eL, eM⟩ :=
    exists_bounded_tensorHom_representatives K L M a b hM hK
  have := hEa
  have := hFb
  have := hPd
  have : ∀ i, Module.Finite R (P.X i) := fun i ↦ (hP i).1
  have : ∀ i, Module.Free R (P.X i) := fun i ↦ (hP i).2
  exact ⟨E, F, P, d, hEa, hEk, hEf, hFb, hPd, hP, eK, eL, eM,
    isIso_theta_of_boundedBelow E F P a b d⟩

/-- The tensor bifunctor is triangulated in its second argument, by tensor symmetry. -/
private theorem exists_tensorFunctorLeft_isTriangulated
    (M : DerivedCategory (ModuleCat.{u} R)) :
    let F := (Functor.curry.obj (DerivedInternalHom.Model.tensor R)).obj M
    ∃ s : F.CommShift ℤ, letI := s; F.IsTriangulated := by
  let D := DerivedInternalHom.Model.adjunction R
  obtain ⟨s, hs⟩ := exists_tensorFunctor_isTriangulated M
  let := s
  have := hs
  let e : (Functor.curry.obj D.tensor).flip.obj M ≅ (Functor.curry.obj D.tensor).obj M :=
    NatIso.ofComponents (fun X ↦ D.tensorSwap X M)
      (fun f ↦ D.tensorSwap_naturality f (𝟙 M))
  exact exists_isTriangulated_of_iso e

set_option backward.isDefEq.respectTransparency false in
private theorem postcomp_eq_homCxMap
    (P B I : CochainComplex (ModuleCat.{u} R) ℤ) (r : B ⟶ I) :
    Stacks.HomComplex.TensorHomMap.postcomp R P B I r =
      Stacks.HomComplex.TensorHomComparison.HomCxMap P P B I (𝟙 P) r := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro i j hij
  change (z.comp (Cochain.ofHom r) (add_zero n)).v i j hij =
    (Stacks.HomComplex.TensorHomComparison.HomCxMapDeg P P B I (𝟙 P) r n z).v i j hij
  rw [Stacks.HomComplex.TensorHomComparison.HomCxMapDeg_v]
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f,
    Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The projective-source comparison is the inverse of the localization map induced by
any K - injective resolution of the target. -/
private theorem homComparison_inv_naturality
    (P B I : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    [P.IsStrictlyLE d] [∀ i, Projective (P.X i)] [I.IsKInjective] (r : B ⟶ I) :
    ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso P B
      d).inv ≫
        (DerivedInternalHom.Model.hom R).map
          (𝟙 (Opposite.op (DerivedCategory.Q.obj P)), DerivedCategory.Q.map r) =
      DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.postcomp R P B I r) ≫
        ((DerivedInternalHom.Model.adjunction R).homIso P I).inv := by
  let c := Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)
  change (c.iso P B d).inv ≫ _ = _
  apply (cancel_epi (c.iso P B d).hom).mp
  apply (cancel_mono ((DerivedInternalHom.Model.adjunction R).homIso P I).hom).mp
  simp only [Iso.hom_inv_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [postcomp_eq_homCxMap]
  exact (c.resolution_comparison P B I d r).symm

private theorem postcomp_comp
    (P A B I : CochainComplex (ModuleCat.{u} R) ℤ) (f : A ⟶ B) (r : B ⟶ I) :
    Stacks.HomComplex.TensorHomMap.postcomp R P A B f ≫ Stacks.HomComplex.TensorHomMap.postcomp R P
      B I r =
      Stacks.HomComplex.TensorHomMap.postcomp R P A I (f ≫ r) := by
  simp only [postcomp_eq_homCxMap]
  simpa only [Category.id_comp] using
    (Stacks.HomComplex.TensorHomComparison.HomCxMap_comp P P P A B I (𝟙 P) (𝟙 P) f r).symm



section ChainAdjunction
set_option backward.isDefEq.respectTransparency false

/-- The Hom complex functor `M ↦ Hom(L, M)` on cochain complexes. -/
noncomputable def chainHomFunctor (L : CochainComplex (ModuleCat R) ℤ) :
    CochainComplex (ModuleCat R) ℤ ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := CochainComplex.HomComplexR R L M
  map f := Stacks.HomComplex.TensorHomMap.postcomp R L _ _ f
  map_id M := by
    ext n z
    change z.comp (Cochain.ofHom (𝟙 M)) (add_zero n) = z
    exact Cochain.comp_id z
  map_comp f g := by
    ext n z
    change z.comp (Cochain.ofHom (f ≫ g)) (add_zero n) =
      (z.comp (Cochain.ofHom f) (add_zero n)).comp (Cochain.ofHom g) (add_zero n)
    rw [Cochain.ofHom_comp]
    exact (Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ _).symm

/-- The morphism of complexes `A' ⟶ B'` obtained by applying the degree-zero component of a
chain map `Hom(A, B) ⟶ Hom(A', B')` to a morphism `A ⟶ B`. -/
noncomputable def chainHomMap
    {A B A' B' : CochainComplex (ModuleCat R) ℤ}
    (f : CochainComplex.HomComplexR R A B ⟶ CochainComplex.HomComplexR R A' B')
    (g : A ⟶ B) : A' ⟶ B' :=
  Cocycle.homOf (Cocycle.mk ((f.f 0).hom (Cochain.ofHom g)) 1 rfl (by
    have h := congrArg (fun k => k.hom (Cochain.ofHom g)) (f.comm 0 1)
    change δ 0 1 ((f.f 0).hom (Cochain.ofHom g)) = 0
    change δ 0 1 ((f.f 0).hom (Cochain.ofHom g)) =
      (f.f 1).hom (δ 0 1 (Cochain.ofHom g)) at h
    simpa only [δ_ofHom, map_zero] using h))

/-- The cochain of `chainHomMap f g` is the image of the cochain of `g` under `f` in degree
zero. -/
lemma ofHom_chainHomMap
    {A B A' B' : CochainComplex (ModuleCat R) ℤ}
    (f : CochainComplex.HomComplexR R A B ⟶ CochainComplex.HomComplexR R A' B')
    (g : A ⟶ B) :
    Cochain.ofHom (chainHomMap f g) = (f.f 0).hom (Cochain.ofHom g) := by
  simp only [chainHomMap, Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe]

/-- The bijection `(A ⟶ B) ≃ (A' ⟶ B')` induced by an isomorphism of Hom complexes
`Hom(A, B) ≅ Hom(A', B')`. -/
noncomputable def chainHomEquiv
    {A B A' B' : CochainComplex (ModuleCat R) ℤ}
    (e : CochainComplex.HomComplexR R A B ≅ CochainComplex.HomComplexR R A' B') :
    (A ⟶ B) ≃ (A' ⟶ B') where
  toFun := chainHomMap e.hom
  invFun := chainHomMap e.inv
  left_inv g := by
    apply Cochain.ofHom_injective
    rw [ofHom_chainHomMap, ofHom_chainHomMap]
    exact congrArg (fun f => (f.f 0).hom (Cochain.ofHom g)) e.hom_inv_id
  right_inv g := by
    apply Cochain.ofHom_injective
    rw [ofHom_chainHomMap, ofHom_chainHomMap]
    exact congrArg (fun f => (f.f 0).hom (Cochain.ofHom g)) e.inv_hom_id

/-- The tensor--Hom bijection `(K ⟶ Hom(L, M)) ≃ (K ⊗ L ⟶ M)` for cochain complexes. -/
noncomputable abbrev chainTensorHomEquiv
    (K L M : CochainComplex (ModuleCat R) ℤ) :
    (K ⟶ CochainComplex.HomComplexR R L M) ≃ (K ⊗ L ⟶ M) :=
  chainHomEquiv (Stacks.HomComplex.Currying.curryIso K L M)

/-- The cochain of `chainTensorHomEquiv K L M g` is the image of the cochain of `g` under the
currying isomorphism in degree zero. -/
lemma ofHom_chainTensorHomEquiv
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (g : K ⟶ CochainComplex.HomComplexR R L M) :
    Cochain.ofHom (chainTensorHomEquiv K L M g) =
      ((Stacks.HomComplex.Currying.curryIso K L M).hom.f 0).hom (Cochain.ofHom g) :=
  ofHom_chainHomMap _ _

/-- The morphism `chainTensorHomEquiv K L M φ` sends the image of `x ⊗ y` to `φ(x)(y)`. -/
lemma chainTensorHomEquiv_apply
    (K L M : CochainComplex (ModuleCat R) ℤ)
    (φ : K ⟶ HomComplexR R L M) (r s t : ℤ) (hrs : r + s = t)
    (x : K.X r) (y : L.X s) :
    ((chainTensorHomEquiv K L M φ).f t).hom
      ((ιTensorObj K L r s t hrs).hom (x ⊗ₜ[R] y)) =
        (((φ.f r).hom x).v s t (by omega)).hom y := by
  have h := CochainComplex.LeftDual.curryIso_hom_apply_degree K L M 0 r s t t r
    hrs (add_zero t) (add_zero r) (Cochain.ofHom φ) x y
  rw [← ofHom_chainTensorHomEquiv] at h
  simp only [Cochain.ofHom_v] at h
  convert h using 1

private lemma chainTensorHomEquiv_naturality_left
    {K K' L M : CochainComplex (ModuleCat R) ℤ} (f : K' ⟶ K)
    (g : K ⟶ CochainComplex.HomComplexR R L M) :
    chainTensorHomEquiv K' L M (f ≫ g) = f ▷ L ≫ chainTensorHomEquiv K L M g := by
  apply Cochain.ofHom_injective
  rw [ofHom_chainTensorHomEquiv, ← Stacks.HomComplex.MonoidalClosed.precomp_ofHom f g,
    ← Stacks.HomComplex.MonoidalClosed.precomp_ofHom (f ▷ L) (chainTensorHomEquiv K L M g),
    ofHom_chainTensorHomEquiv]
  exact congrArg (fun k => (k.f 0).hom (Cochain.ofHom g))
    (Stacks.HomComplex.Currying.curryIso_naturality_left f)

private lemma chainTensorHomEquiv_naturality_right
    {K L M M' : CochainComplex (ModuleCat R) ℤ}
    (g : K ⟶ CochainComplex.HomComplexR R L M) (f : M ⟶ M') :
    chainTensorHomEquiv K L M' (g ≫ Stacks.HomComplex.TensorHomMap.postcomp R L M M' f) =
      chainTensorHomEquiv K L M g ≫ f := by
  apply Cochain.ofHom_injective
  rw [ofHom_chainTensorHomEquiv, ← Stacks.HomComplex.MonoidalClosed.postcomp_ofHom g,
    ← Stacks.HomComplex.MonoidalClosed.postcomp_ofHom (chainTensorHomEquiv K L M g) f,
    ofHom_chainTensorHomEquiv]
  exact congrArg (fun k => (k.f 0).hom (Cochain.ofHom g))
    (Stacks.HomComplex.Currying.curryIso_naturality_right f)

private noncomputable def chainTensorHomAdjunction
    (M : CochainComplex (ModuleCat R) ℤ) : tensorRight M ⊣ chainHomFunctor M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K L => (chainTensorHomEquiv K M L).symm
      homEquiv_naturality_left_symm := chainTensorHomEquiv_naturality_left
      homEquiv_naturality_right := by
        intro K L L' f g
        change (chainTensorHomEquiv K M L').symm (f ≫ g) =
          (chainTensorHomEquiv K M L).symm f ≫ Stacks.HomComplex.TensorHomMap.postcomp R M L L' g
        apply (chainTensorHomEquiv K M L').injective
        rw [Equiv.apply_symm_apply, chainTensorHomEquiv_naturality_right,
          Equiv.apply_symm_apply] }


private theorem transpose_theta (K L M : CochainComplex (ModuleCat R) ℤ) :
    chainTensorHomEquiv (K ⊗ HomComplexR R M L) M (K ⊗ L)
      (Stacks.HomComplex.TensorHomComparison.theta K L M) =
      (α_ K (HomComplexR R M L) M).hom ≫
        K ◁ chainTensorHomEquiv (HomComplexR R M L) M L (𝟙 _) := by
  ext n : 1
  apply GradedObject.Monoidal.tensorObj₃'_ext
  intro p q r h
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq _ _ _ p q r n h (p + q) rfl]
  change (ιTensorObj K (HomComplexR R M L) p q (p + q) rfl ▷ M.X r) ≫
      ιTensorObj (K ⊗ HomComplexR R M L) M (p + q) r n h ≫ _ =
    (ιTensorObj K (HomComplexR R M L) p q (p + q) rfl ▷ M.X r) ≫
      ιTensorObj (K ⊗ HomComplexR R M L) M (p + q) r n h ≫
        ((α_ K (HomComplexR R M L) M).hom.f n ≫
          (K ◁ chainTensorHomEquiv (HomComplexR R M L) M L (𝟙 _)).f n)
  rw [reassoc_of% (CochainComplex.LeftDual.ι_associator_hom K (HomComplexR R M L) M
    p q r (p + q) (q + r) n rfl rfl h)]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro z m
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa [TensorProduct.add_tmul] using congrArg₂ (· + ·) hx hy
  | tmul x φ =>
    change Cochain M L q at φ
    change (chainTensorHomEquiv (K ⊗ HomComplexR R M L) M (K ⊗ L)
      (Stacks.HomComplex.TensorHomComparison.theta K L M)).f n
      ((ιTensorObj (K ⊗ HomComplexR R M L) M (p + q) r n h)
        ((ιTensorObj K (HomComplexR R M L) p q (p + q) rfl (x ⊗ₜ[R] φ)) ⊗ₜ[R] m)) = _
    rw [chainTensorHomEquiv_apply]
    change ((Stacks.HomComplex.TensorHomComparison.thetaDeg K L M (p + q))
      ((ιTensorObj K (HomComplexR R M L) p q (p + q) rfl).hom (x ⊗ₜ[R] φ))).v r n (by omega) m = _
    rw [Stacks.HomComplex.TensorHomComparison.theta_apply]
    change (ιTensorObj K L p (n - p) n (by omega)) (x ⊗ₜ[R] φ.v r (n - p) (by omega) m) =
      (K ◁ chainTensorHomEquiv (HomComplexR R M L) M L (𝟙 _)).f n
        ((ιTensorObj K (HomComplexR R M L ⊗ M) p (q + r) n (by omega))
          (x ⊗ₜ[R] (ιTensorObj (HomComplexR R M L) M q r (q + r) rfl (φ ⊗ₜ[R] m))))
    rw [← id_tensorHom, StacksDraft.DerivedHom.DerivedInternalHom.Model.tensorHom_apply,
      chainTensorHomEquiv_apply]
    have hn : n - p = q + r := by omega
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
    change (ιTensorObj K L p (n - p) n (by omega)).hom
      (x ⊗ₜ[R] (φ.v r (n - p) (by omega)).hom m) =
        (ιTensorObj K L p (q + r) n (by omega)).hom
          (x ⊗ₜ[R] (φ.v r (q + r) (by omega)).hom m)
    have he (s t : ℤ) (hs : p + s = n) (ht : p + t = n)
        (hsr : r + q = s) (htr : r + q = t) (hst : s = t) :
        (ιTensorObj K L p s n hs).hom (x ⊗ₜ[R] (φ.v r s hsr).hom m) =
          (ιTensorObj K L p t n ht).hom (x ⊗ₜ[R] (φ.v r t htr).hom m) := by
      cases hst
      rfl
    exact he (n - p) (q + r) (by omega) (by omega) (by omega) (by omega) hn


end ChainAdjunction


/-! ### The three cases -/

/-- A K-flat left tensor factor and a bounded-above projective Hom source allow the
canonical diagonal to be computed on complexes.

**The bridge from chains to the derived diagonal, and what the K-flatness is for.** The Hom
source being a bounded-above complex of projectives makes the ordinary Hom complex compute
derived internal Hom; the tensor factor being K-flat makes the ordinary tensor product compute
the derived tensor product at the two places the diagonal of [stacks 0BYN] uses it — against the
Hom complex on the left-hand side, and against the Hom target on the right. K-flatness is used
for nothing else, but it cannot simply be dropped: a bounded tensor factor with finitely
presented terms, say, makes `Stacks.HomComplex.TensorHomComparison.theta` a degreewise
isomorphism without making either chain-level tensor product the derived one, and the derived
diagonal is then genuinely not invertible — witness the tensor factor `k` over `k[x]/(x²)` in
the documentation of `isIso_derivedTensorHomDiagonal_of_relativeKFlat`. -/
public theorem isIso_diagonal_of_projective_quasiIso_theta
    (K L M : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ) (hK : K.KFlat)
    [M.IsStrictlyLE d] [∀ i, Projective (M.X i)]
    [QuasiIso (Stacks.HomComplex.TensorHomComparison.theta K L M)] :
    IsIso (DerivedInternalHom.Model.diagonal
      (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M)) := by
  rw [DerivedInternalHom.Model.diagonal_projective_comparison K L M d hK]
  have : IsIso (𝟙 (DerivedCategory.Q.obj K),
      ((Stacks.DerivedTensorHomDiagonal.ProjectiveComparison.projectiveHomComparison (R := R)).iso M
        L d).hom) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  have : IsIso (𝟙 (Opposite.op (DerivedCategory.Q.obj M)),
      ((DerivedInternalHom.Model.adjunction R).tensorSwap (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L) ≪≫
        (DerivedInternalHom.Model.adjunction R).tensorIso L K hK ≪≫
        DerivedCategory.Q.mapIso (StacksDraft.DerivedHom.Model.complexSwap R L K)).inv) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  infer_instance

/-- Under the one-sided boundedness hypotheses the canonical diagonal is invertible. -/
private theorem isIso_diagonal_of_boundedBelow
    (K L M : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ)
    (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M) [L.IsGE b]
    (hK : ∀ (N : ModuleCat.{u} R) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.obj K).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))))) :
    IsIso (DerivedInternalHom.Model.diagonal K L M) := by
  obtain ⟨E, F, P, d, hEa, hEk, hEf, hFb, hPd, hP, ⟨eK⟩, ⟨eL⟩, ⟨eM⟩, hθ⟩ :=
    exists_bounded_tensorHom_isIso_representatives K L M a b hM hK
  let := hPd
  let := hθ
  let : ∀ i, Module.Free R (P.X i) := fun i ↦ (hP i).2
  have : ∀ i, Projective (P.X i) := fun i ↦ ModuleCat.projective_of_categoryTheory_projective _
  have := isIso_diagonal_of_projective_quasiIso_theta E F P d hEk
  exact isIso_diagonal_of_iso eK eL eM

end Stacks.DerivedTensorHomDiagonal

end
